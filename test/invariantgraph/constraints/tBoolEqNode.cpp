#include "../nodeTestBase.hpp"
#include "core/propagationEngine.hpp"
#include "invariantgraph/violationInvariantNodes/boolEqNode.hpp"

static bool isViolating(const std::vector<Int>& values) {
  for (size_t i = 0; i < values.size(); i++) {
    for (size_t j = i + 1; j < values.size(); j++) {
      if ((values.at(i) == 0) != (values.at(j) == 0)) {
        return true;
      }
    }
  }
  return false;
}

template <ConstraintType Type>
class AbstractBoolEqNodeTest : public NodeTestBase<invariantgraph::BoolEqNode> {
 public:
  invariantgraph::VarNodeId a;
  invariantgraph::VarNodeId b;
  invariantgraph::VarNodeId r;

  void SetUp() override {
    NodeTestBase::SetUp();
    a = createBoolVar("a");
    b = createBoolVar("b");
    r = createBoolVar("r");

    if constexpr (Type == ConstraintType::REIFIED) {
      _model->addConstraint(std::move(fznparser::Constraint(
          "bool_eq_reif",
          std::vector<fznparser::Arg>{fznparser::BoolArg{boolVar(a)},
                                      fznparser::BoolArg{boolVar(b)},
                                      fznparser::BoolArg{boolVar(r)}})));
    } else {
      if constexpr (Type == ConstraintType::NORMAL) {
        _model->addConstraint(std::move(fznparser::Constraint(
            "bool_eq",
            std::vector<fznparser::Arg>{fznparser::BoolArg{boolVar(a)},
                                        fznparser::BoolArg{boolVar(b)}})));
      } else if constexpr (Type == ConstraintType::CONSTANT_FALSE) {
        _model->addConstraint(std::move(fznparser::Constraint(
            "bool_eq_reif",
            std::vector<fznparser::Arg>{fznparser::BoolArg{boolVar(a)},
                                        fznparser::BoolArg{boolVar(b)},
                                        fznparser::BoolArg{false}})));
      } else {
        _model->addConstraint(std::move(fznparser::Constraint(
            "bool_eq_reif",
            std::vector<fznparser::Arg>{fznparser::BoolArg{boolVar(a)},
                                        fznparser::BoolArg{boolVar(b)},
                                        fznparser::BoolArg{true}})));
      }
    }

    makeInvNode(_model->constraints().front());
  }

  void construction() {
    expectInputTo(invNode());
    expectOutputOf(invNode());

    EXPECT_EQ(invNode().a(), a);
    EXPECT_EQ(invNode().b(), b);
    if constexpr (Type != ConstraintType::REIFIED) {
      EXPECT_FALSE(invNode().isReified());
      EXPECT_EQ(invNode().reifiedViolationNodeId(),
                invariantgraph::NULL_NODE_ID);
    } else {
      EXPECT_TRUE(invNode().isReified());
      EXPECT_NE(invNode().reifiedViolationNodeId(),
                invariantgraph::NULL_NODE_ID);
      EXPECT_EQ(invNode().reifiedViolationNodeId(), r);
    }
  }

  void application() {
    PropagationEngine engine;
    engine.open();
    addInputVarsToEngine(engine);
    for (const auto& outputVarNodeId : invNode().outputVarNodeIds()) {
      EXPECT_EQ(varId(outputVarNodeId), NULL_ID);
    }
    EXPECT_EQ(invNode().violationVarId(*_invariantGraph), NULL_ID);
    invNode().registerOutputVariables(*_invariantGraph, engine);
    for (const auto& outputVarNodeId : invNode().outputVarNodeIds()) {
      EXPECT_NE(varId(outputVarNodeId), NULL_ID);
    }
    EXPECT_NE(invNode().violationVarId(*_invariantGraph), NULL_ID);
    invNode().registerNode(*_invariantGraph, engine);
    engine.close();

    // a and b
    EXPECT_EQ(engine.searchVariables().size(), 2);

    // a, b and the violation
    EXPECT_EQ(engine.numVariables(), 3);

    // equal
    EXPECT_EQ(engine.numInvariants(), 1);

    EXPECT_EQ(engine.lowerBound(invNode().violationVarId(*_invariantGraph)), 0);
    EXPECT_EQ(engine.upperBound(invNode().violationVarId(*_invariantGraph)), 1);
  }

  void propagation() {
    PropagationEngine engine;
    engine.open();
    addInputVarsToEngine(engine);
    invNode().registerOutputVariables(*_invariantGraph, engine);
    invNode().registerNode(*_invariantGraph, engine);

    std::vector<VarId> inputs;
    EXPECT_EQ(invNode().staticInputVarNodeIds().size(), 2);
    for (const auto& inputVarNodeId : invNode().staticInputVarNodeIds()) {
      EXPECT_NE(varId(inputVarNodeId), NULL_ID);
      inputs.emplace_back(varId(inputVarNodeId));
      engine.updateBounds(varId(inputVarNodeId), 0, 5, true);
    }

    EXPECT_NE(invNode().violationVarId(*_invariantGraph), NULL_ID);
    const VarId violationId = invNode().violationVarId(*_invariantGraph);
    EXPECT_EQ(inputs.size(), 2);

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

class BoolEqNodeTest : public AbstractBoolEqNodeTest<ConstraintType::NORMAL> {};

TEST_F(BoolEqNodeTest, Construction) { construction(); }

TEST_F(BoolEqNodeTest, Application) { application(); }

TEST_F(BoolEqNodeTest, Propagation) { propagation(); }

class BoolEqReifNodeTest
    : public AbstractBoolEqNodeTest<ConstraintType::REIFIED> {};

TEST_F(BoolEqReifNodeTest, Construction) { construction(); }

TEST_F(BoolEqReifNodeTest, Application) { application(); }

TEST_F(BoolEqReifNodeTest, Propagation) { propagation(); }

class BoolEqFalseNodeTest
    : public AbstractBoolEqNodeTest<ConstraintType::CONSTANT_FALSE> {};

TEST_F(BoolEqFalseNodeTest, Construction) { construction(); }

TEST_F(BoolEqFalseNodeTest, Application) { application(); }

TEST_F(BoolEqFalseNodeTest, Propagation) { propagation(); }

class BoolEqTrueNodeTest
    : public AbstractBoolEqNodeTest<ConstraintType::CONSTANT_TRUE> {};

TEST_F(BoolEqTrueNodeTest, Construction) { construction(); }

TEST_F(BoolEqTrueNodeTest, Application) { application(); }

TEST_F(BoolEqTrueNodeTest, Propagation) { propagation(); }