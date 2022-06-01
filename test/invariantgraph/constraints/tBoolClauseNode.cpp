#include "../nodeTestBase.hpp"
#include "core/propagationEngine.hpp"
#include "invariantgraph/constraints/boolClauseNode.hpp"

static bool isViolating(const std::vector<Int>& asValues,
                        const std::vector<Int>& bsValues) {
  for (const Int aVal : asValues) {
    if (aVal != 0) {
      return true;
    }
  }
  for (const Int bVal : bsValues) {
    if (bVal == 0) {
      return true;
    }
  }
  return false;
}

template <ConstraintType Type>
class AbstractBoolClauseNodeTest : public NodeTestBase {
 public:
  BOOL_VARIABLE(a);
  BOOL_VARIABLE(b);
  BOOL_VARIABLE(c);
  BOOL_VARIABLE(d);
  BOOL_VARIABLE(r);

  std::unique_ptr<fznparser::Constraint> constraint;
  std::unique_ptr<fznparser::FZNModel> model;
  std::unique_ptr<invariantgraph::BoolClauseNode> node;

  void SetUp() override {
    if constexpr (Type == ConstraintType::REIFIED) {
      fznparser::Constraint cnstr{
          "bool_clause_reif",
          {fznparser::Constraint::ArrayArgument{a.name, b.name},
           fznparser::Constraint::ArrayArgument{c.name, d.name},
           fznparser::Constraint::Argument{"r"}},
          {}};

      constraint = std::make_unique<fznparser::Constraint>(std::move(cnstr));

      fznparser::FZNModel mdl{
          {}, {a, b, c, d, r}, {*constraint}, fznparser::Satisfy{}};

      model = std::make_unique<fznparser::FZNModel>(std::move(mdl));
    } else {
      if constexpr (Type == ConstraintType::NORMAL) {
        fznparser::Constraint cnstr{
            "bool_clause",
            {fznparser::Constraint::ArrayArgument{a.name, b.name},
             fznparser::Constraint::ArrayArgument{c.name, d.name}},
            {}};

        constraint = std::make_unique<fznparser::Constraint>(std::move(cnstr));
      } else if constexpr (Type == ConstraintType::CONSTANT_FALSE) {
        fznparser::Constraint cnstr{
            "bool_clause_reif",
            {fznparser::Constraint::ArrayArgument{a.name, b.name},
             fznparser::Constraint::ArrayArgument{c.name, d.name}, false},
            {}};

        constraint = std::make_unique<fznparser::Constraint>(std::move(cnstr));
      } else {
        fznparser::Constraint cnstr{
            "bool_clause_reif",
            {fznparser::Constraint::ArrayArgument{a.name, b.name},
             fznparser::Constraint::ArrayArgument{c.name, d.name}, true},
            {}};

        constraint = std::make_unique<fznparser::Constraint>(std::move(cnstr));
      }

      fznparser::FZNModel mdl{
          {}, {a, b, c, d}, {*constraint}, fznparser::Satisfy{}};

      model = std::make_unique<fznparser::FZNModel>(std::move(mdl));
    }

    setModel(model.get());
    node = makeNode<invariantgraph::BoolClauseNode>(*constraint);
  }

  void construction() {
    EXPECT_EQ(node->as().size(), 2);
    EXPECT_EQ(*node->as().at(0)->variable(),
              invariantgraph::VariableNode::FZNVariable(a));
    EXPECT_EQ(*node->as().at(1)->variable(),
              invariantgraph::VariableNode::FZNVariable(b));

    EXPECT_EQ(node->bs().size(), 2);
    EXPECT_EQ(*node->bs().at(0)->variable(),
              invariantgraph::VariableNode::FZNVariable(c));
    EXPECT_EQ(*node->bs().at(1)->variable(),
              invariantgraph::VariableNode::FZNVariable(d));

    EXPECT_EQ(node->staticInputs().size(),
              node->as().size() + node->bs().size());

    std::vector<invariantgraph::VariableNode*> expectedVars(node->as());
    for (auto* const var : node->bs()) {
      expectedVars.emplace_back(var);
    }
    EXPECT_EQ(expectedVars, node->staticInputs());

    expectMarkedAsInput(node.get(), node->as());
    expectMarkedAsInput(node.get(), node->bs());
    if constexpr (Type != ConstraintType::REIFIED) {
      EXPECT_FALSE(node->isReified());
      EXPECT_EQ(node->reifiedViolation(), nullptr);
    } else {
      EXPECT_TRUE(node->isReified());
      EXPECT_NE(node->reifiedViolation(), nullptr);
      EXPECT_EQ(node->reifiedViolation()->variable(),
                invariantgraph::VariableNode::FZNVariable(r));
    }
  }

  void application() {
    PropagationEngine engine;
    engine.open();
    registerVariables(engine, {a.name, b.name, c.name, d.name});
    for (auto* const definedVariable : node->definedVariables()) {
      EXPECT_EQ(definedVariable->varId(), NULL_ID);
    }
    EXPECT_EQ(node->violationVarId(), NULL_ID);
    node->createDefinedVariables(engine);
    for (auto* const definedVariable : node->definedVariables()) {
      EXPECT_NE(definedVariable->varId(), NULL_ID);
    }
    EXPECT_NE(node->violationVarId(), NULL_ID);
    node->registerWithEngine(engine);
    engine.close();

    // a, b, c and d
    EXPECT_EQ(engine.searchVariables().size(), 4);

    // a, b, c, d, sum
    EXPECT_EQ(engine.numVariables(), 5);

    // linear
    EXPECT_EQ(engine.numInvariants(), 1);
  }

  void propagation() {
    PropagationEngine engine;
    engine.open();
    registerVariables(engine, {a.name, b.name, c.name, d.name});
    node->createDefinedVariables(engine);
    node->registerWithEngine(engine);

    EXPECT_EQ(node->as().size(), 2);
    std::vector<VarId> asInputs;
    for (auto* const inputVariable : node->as()) {
      EXPECT_NE(inputVariable->varId(), NULL_ID);
      asInputs.emplace_back(inputVariable->varId());
      engine.updateBounds(inputVariable->varId(), 0, 5, true);
    }
    EXPECT_EQ(node->bs().size(), 2);
    std::vector<VarId> bsInputs;
    for (auto* const inputVariable : node->bs()) {
      EXPECT_NE(inputVariable->varId(), NULL_ID);
      bsInputs.emplace_back(inputVariable->varId());
      engine.updateBounds(inputVariable->varId(), 0, 5, true);
    }

    EXPECT_NE(node->violationVarId(), NULL_ID);
    const VarId violationId = node->violationVarId();

    std::vector<Int> asValues(asInputs.size());
    std::vector<Int> bsValues(bsInputs.size());
    engine.close();

    for (asValues.at(0) = engine.lowerBound(asInputs.at(0));
         asValues.at(0) <= engine.upperBound(asInputs.at(0));
         ++asValues.at(0)) {
      for (asValues.at(1) = engine.lowerBound(asInputs.at(1));
           asValues.at(1) <= engine.upperBound(asInputs.at(1));
           ++asValues.at(1)) {
        for (bsValues.at(0) = engine.lowerBound(bsInputs.at(0));
             bsValues.at(0) <= engine.upperBound(bsInputs.at(0));
             ++bsValues.at(0)) {
          for (bsValues.at(1) = engine.lowerBound(bsInputs.at(1));
               bsValues.at(1) <= engine.upperBound(bsInputs.at(1));
               ++bsValues.at(1)) {
            engine.beginMove();
            for (size_t i = 0; i < asInputs.size(); ++i) {
              engine.setValue(asInputs.at(i), asValues.at(i));
            }
            for (size_t i = 0; i < bsInputs.size(); ++i) {
              engine.setValue(bsInputs.at(i), bsValues.at(i));
            }
            engine.endMove();

            engine.beginProbe();
            engine.query(violationId);
            engine.endProbe();
            if constexpr (Type != ConstraintType::CONSTANT_FALSE) {
              EXPECT_EQ(engine.currentValue(violationId) > 0,
                        isViolating(asValues, bsValues));
            } else {
              EXPECT_NE(engine.currentValue(violationId) > 0,
                        isViolating(asValues, bsValues));
            }
          }
        }
      }
    }
  }
};

class BoolClauseNodeTest
    : public AbstractBoolClauseNodeTest<ConstraintType::NORMAL> {};

TEST_F(BoolClauseNodeTest, Construction) { construction(); }

TEST_F(BoolClauseNodeTest, Application) { application(); }

TEST_F(BoolClauseNodeTest, Propagation) { propagation(); }

class BoolClauseReifNodeTest
    : public AbstractBoolClauseNodeTest<ConstraintType::REIFIED> {};

TEST_F(BoolClauseReifNodeTest, Construction) { construction(); }

TEST_F(BoolClauseReifNodeTest, Application) { application(); }

TEST_F(BoolClauseReifNodeTest, Propagation) { propagation(); }

class BoolClauseFalseNodeTest
    : public AbstractBoolClauseNodeTest<ConstraintType::CONSTANT_FALSE> {};

TEST_F(BoolClauseFalseNodeTest, Construction) { construction(); }

TEST_F(BoolClauseFalseNodeTest, Application) { application(); }

TEST_F(BoolClauseFalseNodeTest, Propagation) { propagation(); }

class BoolClauseTrueNodeTest
    : public AbstractBoolClauseNodeTest<ConstraintType::CONSTANT_TRUE> {};

TEST_F(BoolClauseTrueNodeTest, Construction) { construction(); }

TEST_F(BoolClauseTrueNodeTest, Application) { application(); }

TEST_F(BoolClauseTrueNodeTest, Propagation) { propagation(); }