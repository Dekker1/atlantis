#include "../nodeTestBase.hpp"
#include "invariantgraph/implicitConstraints/circuitImplicitNode.hpp"
#include "propagation/solver.hpp"
#include "search/neighbourhoods/circuitNeighbourhood.hpp"

namespace atlantis::testing {

using namespace atlantis::invariantgraph;

class CircuitImplicitNodeTest : public NodeTestBase<CircuitImplicitNode> {
 public:
  VarNodeId a;
  VarNodeId b;
  VarNodeId c;
  VarNodeId d;

  void SetUp() override {
    NodeTestBase::SetUp();
    a = createIntVar(1, 4, "a");
    b = createIntVar(1, 4, "b");
    c = createIntVar(1, 4, "c");
    d = createIntVar(1, 4, "d");

    fznparser::IntVarArray inputs("");
    inputs.append(intVar(a));
    inputs.append(intVar(b));
    inputs.append(intVar(c));
    inputs.append(intVar(d));

    _model->addConstraint(fznparser::Constraint(
        "circuit_no_offset", std::vector<fznparser::Arg>{inputs}));

    makeImplicitNode(_model->constraints().front());
  }
};

TEST_F(CircuitImplicitNodeTest, construction) {
  std::vector<VarNodeId> expectedVars{a, b, c, d};

  EXPECT_EQ(invNode().outputVarNodeIds(), expectedVars);
}

TEST_F(CircuitImplicitNodeTest, application) {
  propagation::Solver solver;
  solver.open();
  for (const auto& outputVarNodeId : invNode().outputVarNodeIds()) {
    EXPECT_EQ(varId(outputVarNodeId), propagation::NULL_ID);
  }
  invNode().registerOutputVars(*_invariantGraph, solver);
  for (const auto& outputVarNodeId : invNode().outputVarNodeIds()) {
    EXPECT_NE(varId(outputVarNodeId), propagation::NULL_ID);
  }
  invNode().registerNode(*_invariantGraph, solver);
  solver.close();

  // a, b, c and d
  EXPECT_EQ(solver.searchVars().size(), 4);

  // a, b, c and d
  EXPECT_EQ(solver.numVars(), 4);

  EXPECT_EQ(solver.numInvariants(), 0);

  auto neighbourhood = invNode().neighbourhood();

  EXPECT_TRUE(dynamic_cast<search::neighbourhoods::CircuitNeighbourhood*>(
      neighbourhood.get()));
}

}  // namespace atlantis::testing