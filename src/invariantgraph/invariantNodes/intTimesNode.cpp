#include "invariantgraph/invariantNodes/intTimesNode.hpp"

#include "../parseHelper.hpp"

namespace atlantis::invariantgraph {

IntTimesNode::IntTimesNode(VarNodeId a, VarNodeId b, VarNodeId output)
    : InvariantNode({output}, {a, b}) {}

void IntTimesNode::registerOutputVars(InvariantGraph& invariantGraph,
                                      propagation::SolverBase& solver) {
  makeSolverVar(solver, invariantGraph.varNode(outputVarNodeIds().front()));
}

void IntTimesNode::registerNode(InvariantGraph& invariantGraph,
                                propagation::SolverBase& solver) {
  assert(invariantGraph.varId(outputVarNodeIds().front()) !=
         propagation::NULL_ID);
  solver.makeInvariant<propagation::Times>(
      solver, invariantGraph.varId(outputVarNodeIds().front()),
      invariantGraph.varId(a()), invariantGraph.varId(b()));
}

}  // namespace atlantis::invariantgraph