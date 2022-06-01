#include <gmock/gmock.h>

#include "../nodeTestBase.hpp"
#include "core/propagationEngine.hpp"
#include "invariantgraph/constraints/arrayBoolAndNode.hpp"

static bool isViolating(const std::vector<Int>& values) {
  for (const Int val : values) {
    if (val > 0) {
      return true;
    }
  }
  return false;
}

template <ConstraintType Type>
class AbstractArrayBoolAndNodeTest : public NodeTestBase {
 public:
  BOOL_VARIABLE(a);
  BOOL_VARIABLE(b);
  BOOL_VARIABLE(r);

  std::unique_ptr<fznparser::Constraint> constraint;
  std::unique_ptr<fznparser::FZNModel> model;
  std::unique_ptr<invariantgraph::ArrayBoolAndNode> node;

  void SetUp() override {
    if constexpr (Type == ConstraintType::REIFIED) {
      fznparser::Constraint cnstr{
          "array_bool_and",
          {fznparser::Constraint::ArrayArgument{"a", "b"},
           fznparser::Constraint::Argument{"r"}},
          {}};

      constraint = std::make_unique<fznparser::Constraint>(std::move(cnstr));

      fznparser::FZNModel mdl{
          {}, {a, b, r}, {*constraint}, fznparser::Satisfy{}};

      model = std::make_unique<fznparser::FZNModel>(std::move(mdl));
    } else {
      if constexpr (Type == ConstraintType::NORMAL) {
        fznparser::Constraint cnstr{
            "array_bool_and",
            {fznparser::Constraint::ArrayArgument{"a", "b"}, true},
            {}};

        constraint = std::make_unique<fznparser::Constraint>(std::move(cnstr));
      } else if constexpr (Type == ConstraintType::CONSTANT_FALSE) {
        fznparser::Constraint cnstr{
            "array_bool_and",
            {fznparser::Constraint::ArrayArgument{"a", "b"}, false},
            {}};

        constraint = std::make_unique<fznparser::Constraint>(std::move(cnstr));
      } else {
        fznparser::Constraint cnstr{
            "array_bool_and",
            {fznparser::Constraint::ArrayArgument{"a", "b"}, true},
            {}};

        constraint = std::make_unique<fznparser::Constraint>(std::move(cnstr));
      }

      fznparser::FZNModel mdl{{}, {a, b}, {*constraint}, fznparser::Satisfy{}};

      model = std::make_unique<fznparser::FZNModel>(std::move(mdl));
    }
    setModel(model.get());
    node = makeNode<invariantgraph::ArrayBoolAndNode>(*constraint);
  }

  void construction() {
    EXPECT_EQ(node->staticInputs().size(), 2);
    EXPECT_EQ(node->dynamicInputs().size(), 0);
    std::vector<invariantgraph::VariableNode*> expectedVars;
    for (size_t i = 0; i < 2; ++i) {
      expectedVars.emplace_back(_variables.at(i).get());
    }
    EXPECT_EQ(node->staticInputs(), expectedVars);
    EXPECT_THAT(expectedVars, testing::ContainerEq(node->staticInputs()));
    expectMarkedAsInput(node.get(), node->staticInputs());
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
    registerVariables(engine, {a.name, b.name});
    for (auto* const definedVariable : node->definedVariables()) {
      EXPECT_EQ(definedVariable->varId(), NULL_ID);
    }
    node->createDefinedVariables(engine);
    for (auto* const definedVariable : node->definedVariables()) {
      EXPECT_NE(definedVariable->varId(), NULL_ID);
    }
    node->registerWithEngine(engine);
    engine.close();

    // a and b
    EXPECT_EQ(engine.searchVariables().size(), 2);

    // a, b and r
    EXPECT_EQ(engine.numVariables(), 3);

    // sum
    EXPECT_EQ(engine.numInvariants(), 1);
  }

  void propagation() {
    PropagationEngine engine;
    engine.open();
    registerVariables(engine, {a.name, b.name});
    node->createDefinedVariables(engine);
    node->registerWithEngine(engine);

    std::vector<VarId> inputs;
    EXPECT_EQ(node->staticInputs().size(), 2);
    for (auto* const inputVariable : node->staticInputs()) {
      EXPECT_NE(inputVariable->varId(), NULL_ID);
      inputs.emplace_back(inputVariable->varId());
      engine.updateBounds(inputVariable->varId(), 0, 10, true);
    }

    EXPECT_NE(node->violationVarId(), NULL_ID);
    const VarId violationId = node->violationVarId();

    std::vector<Int> values(inputs.size());
    engine.close();

    for (values.at(0) = engine.lowerBound(inputs.at(0));
         values.at(0) <= engine.upperBound(inputs.at(0)); ++values.at(0)) {
      for (values.at(1) = engine.lowerBound(inputs.at(1));
           values.at(1) <= engine.upperBound(inputs.at(1)); ++values.at(1)) {
        engine.beginMove();
        for (size_t i = 0; i < inputs.size(); ++i) {
          engine.setValue(inputs.at(i), values.at(i));
        }
        engine.endMove();

        engine.beginProbe();
        engine.query(violationId);
        engine.endProbe();

        if constexpr (Type != ConstraintType::CONSTANT_FALSE) {
          EXPECT_EQ(engine.currentValue(violationId) > 0, isViolating(values));
        } else {
          EXPECT_NE(engine.currentValue(violationId) > 0, isViolating(values));
        }
      }
    }
  }
};

class ArrayBoolAndNodeTest
    : public AbstractArrayBoolAndNodeTest<ConstraintType::NORMAL> {};

TEST_F(ArrayBoolAndNodeTest, Construction) { construction(); }

TEST_F(ArrayBoolAndNodeTest, Application) { application(); }

TEST_F(ArrayBoolAndNodeTest, Propagation) { propagation(); }

class ArrayBoolAndReifNodeTest
    : public AbstractArrayBoolAndNodeTest<ConstraintType::REIFIED> {};

TEST_F(ArrayBoolAndReifNodeTest, Construction) { construction(); }

TEST_F(ArrayBoolAndReifNodeTest, Application) { application(); }

TEST_F(ArrayBoolAndReifNodeTest, Propagation) { propagation(); }

class ArrayBoolAndFalseNodeTest
    : public AbstractArrayBoolAndNodeTest<ConstraintType::CONSTANT_FALSE> {};

TEST_F(ArrayBoolAndFalseNodeTest, Construction) { construction(); }

TEST_F(ArrayBoolAndFalseNodeTest, Application) { application(); }

TEST_F(ArrayBoolAndFalseNodeTest, Propagation) { propagation(); }

class ArrayBoolAndTrueNodeTest
    : public AbstractArrayBoolAndNodeTest<ConstraintType::CONSTANT_TRUE> {};

TEST_F(ArrayBoolAndTrueNodeTest, Construction) { construction(); }

TEST_F(ArrayBoolAndTrueNodeTest, Application) { application(); }

TEST_F(ArrayBoolAndTrueNodeTest, Propagation) { propagation(); }