#include "../nodeTestBase.hpp"
#include "atlantis/invariantgraph/fzn/array_int_minimum.hpp"
#include "atlantis/invariantgraph/invariantNodes/arrayIntMinimumNode.hpp"
#include "atlantis/propagation/solver.hpp"

namespace atlantis::testing {

using namespace atlantis::invariantgraph;

class ArrayIntMinimumNodeTestFixture
    : public NodeTestBase<ArrayIntMinimumNode> {
 public:
  std::vector<VarNodeId> inputVarNodeIds;
  std::vector<std::string> inputIdentifiers;
  VarNodeId outputVarNodeId{NULL_NODE_ID};
  std::string outputIdentifier{"output"};

  Int computeOutput() {
    Int val = std::numeric_limits<Int>::max();
    for (const auto& identifier : inputIdentifiers) {
      val = std::min(val, varNode(identifier).upperBound());
    }
    return val;
  }

  Int computeOutput(propagation::Solver& solver) {
    Int val = std::numeric_limits<Int>::max();
    for (const auto& identifier : inputIdentifiers) {
      if (varNode(identifier).isFixed() ||
          varId(identifier) == propagation::NULL_ID) {
        val = std::min(val, varNode(identifier).upperBound());
      } else {
        val = std::min(val, solver.currentValue(varId(identifier)));
      }
    }
    return val;
  }

  void SetUp() override {
    NodeTestBase::SetUp();

    std::vector<std::pair<Int, Int>> bounds;

    if (shouldBeSubsumed()) {
      bounds = {{-2, 5}, {-5, 2}, {-5, -5}};

    } else if (shouldBeReplaced()) {
      bounds = {{-5, 2}, {2, 5}, {2, 2}};
    } else {
      bounds = {{-5, 0}, {-2, -2}, {0, 5}};
    }
    for (const auto& [lb, ub] : bounds) {
      inputIdentifiers.emplace_back("input_" +
                                    std::to_string(inputIdentifiers.size()));
      inputVarNodeIds.emplace_back(
          retrieveIntVarNode(lb, ub, inputIdentifiers.back()));
    }
    outputVarNodeId = retrieveIntVarNode(-5, 5, outputIdentifier);

    createInvariantNode(std::vector<VarNodeId>{inputVarNodeIds},
                        outputVarNodeId);
  }
};

TEST_P(ArrayIntMinimumNodeTestFixture, construction) {
  expectInputTo(invNode());
  expectOutputOf(invNode());

  EXPECT_EQ(invNode().staticInputVarNodeIds().size(), inputVarNodeIds.size());
  for (size_t i = 0; i < inputVarNodeIds.size(); ++i) {
    EXPECT_EQ(invNode().staticInputVarNodeIds().at(i), inputVarNodeIds.at(i));
  }

  EXPECT_EQ(invNode().outputVarNodeIds().size(), 1);
  EXPECT_EQ(invNode().outputVarNodeIds().front(), outputVarNodeId);
}

TEST_P(ArrayIntMinimumNodeTestFixture, application) {
  propagation::Solver solver;
  solver.open();
  addInputVarsToSolver(solver);
  for (const auto& outputVarNodeId : invNode().outputVarNodeIds()) {
    EXPECT_EQ(varId(outputVarNodeId), propagation::NULL_ID);
  }
  invNode().registerOutputVars(*_invariantGraph, solver);
  for (const auto& outputVarNodeId : invNode().outputVarNodeIds()) {
    EXPECT_NE(varId(outputVarNodeId), propagation::NULL_ID);
  }
  invNode().registerNode(*_invariantGraph, solver);
  solver.close();

  Int lb = std::numeric_limits<Int>::max();
  Int ub = std::numeric_limits<Int>::max();

  for (const auto& inputVarNodeId : invNode().staticInputVarNodeIds()) {
    lb = std::min(lb, solver.lowerBound(varId(inputVarNodeId)));
    ub = std::min(ub, solver.upperBound(varId(inputVarNodeId)));
  }

  EXPECT_EQ(solver.lowerBound(varId(outputVarNodeId)), lb);
  EXPECT_EQ(solver.upperBound(varId(outputVarNodeId)), ub);

  // x1, x2, and x3
  EXPECT_EQ(solver.searchVars().size(), 3);

  // x1, x2 and outputVarNodeId
  EXPECT_EQ(solver.numVars(), 4);

  // maxSparse
  EXPECT_EQ(solver.numInvariants(), 1);
}

TEST_P(ArrayIntMinimumNodeTestFixture, updateState) {
  Int minVal = std::numeric_limits<Int>::min();
  Int maxVal = std::numeric_limits<Int>::max();
  for (const auto& identifier : inputIdentifiers) {
    minVal =
        std::min(minVal, _invariantGraph->varNode(identifier).lowerBound());
    maxVal =
        std::max(maxVal, _invariantGraph->varNode(identifier).upperBound());
  }
  EXPECT_EQ(invNode().state(), InvariantNodeState::ACTIVE);
  invNode().updateState(*_invariantGraph);
  if (shouldBeSubsumed()) {
    EXPECT_EQ(invNode().state(), InvariantNodeState::SUBSUMED);
    // TODO: disabled for the MZN challange. This should be computed by Gecode.
    // EXPECT_TRUE(_invariantGraph->varNode(outputVarNodeId).isFixed());
    const Int expected = computeOutput();
    const Int actual = _invariantGraph->varNode(outputVarNodeId).upperBound();
    // TODO: disabled for the MZN challange. This should be computed by Gecode.
    // EXPECT_EQ(expected, actual);
  } else {
    EXPECT_EQ(invNode().state(), InvariantNodeState::ACTIVE);
  }
  EXPECT_LE(minVal, _invariantGraph->varNode(outputVarNodeId).lowerBound());
  EXPECT_GE(maxVal, _invariantGraph->varNode(outputVarNodeId).upperBound());
}

TEST_P(ArrayIntMinimumNodeTestFixture, replace) {
  EXPECT_EQ(invNode().state(), InvariantNodeState::ACTIVE);
  invNode().updateState(*_invariantGraph);
  if (shouldBeReplaced()) {
    EXPECT_TRUE(invNode().canBeReplaced(*_invariantGraph));
    EXPECT_TRUE(invNode().replace(*_invariantGraph));
    invNode().deactivate(*_invariantGraph);
    EXPECT_EQ(invNode().state(), InvariantNodeState::SUBSUMED);
  } else if (invNode().state() == InvariantNodeState::ACTIVE) {
    EXPECT_FALSE(invNode().canBeReplaced(*_invariantGraph));
    EXPECT_FALSE(invNode().replace(*_invariantGraph));
  }
}

TEST_P(ArrayIntMinimumNodeTestFixture, propagation) {
  Int ub = std::numeric_limits<Int>::max();
  for (const auto& identifier : inputIdentifiers) {
    ub = std::min(ub, varNode(identifier).upperBound());
  }

  propagation::Solver solver;
  _invariantGraph->apply(solver);
  _invariantGraph->close(solver);

  if (shouldBeSubsumed()) {
    const Int expected = computeOutput(solver);
    const Int actual = varNode(outputVarNodeId).lowerBound();
    EXPECT_EQ(expected, actual);
    return;
  }
  if (shouldBeReplaced()) {
    EXPECT_FALSE(varNode(outputIdentifier).isFixed());
    EXPECT_EQ(varId(outputIdentifier), propagation::NULL_ID);
    return;
  }

  std::vector<propagation::VarId> inputVarIds;
  for (const auto& identifier : inputIdentifiers) {
    if (varNode(identifier).lowerBound() < ub) {
      EXPECT_NE(varId(identifier), propagation::NULL_ID);
      inputVarIds.emplace_back(varId(identifier));
    }
  }

  VarNode& outputNode = varNode(outputIdentifier);

  if (outputNode.isFixed()) {
    const Int expected = outputNode.lowerBound();
    const Int actual = computeOutput(solver);
    EXPECT_EQ(expected, actual);
    return;
  }
  EXPECT_NE(varId(outputIdentifier), propagation::NULL_ID);

  const propagation::VarId outputId = varId(outputIdentifier);

  std::vector<Int> inputVals = makeInputVals(solver, inputVarIds);

  while (increaseNextVal(solver, inputVarIds, inputVals)) {
    solver.beginMove();
    setVarVals(solver, inputVarIds, inputVals);
    solver.endMove();

    solver.beginProbe();
    solver.query(outputId);
    solver.endProbe();

    expectVarVals(solver, inputVarIds, inputVals);

    const Int expected = computeOutput(solver);
    const Int actual = solver.currentValue(outputId);
    EXPECT_EQ(expected, actual);
  }
}

INSTANTIATE_TEST_CASE_P(
    ArrayIntMinimumNodeTest, ArrayIntMinimumNodeTestFixture,
    ::testing::Values(ParamData{}, ParamData{InvariantNodeAction::SUBSUME},
                      ParamData{InvariantNodeAction::REPLACE}));

}  // namespace atlantis::testing
