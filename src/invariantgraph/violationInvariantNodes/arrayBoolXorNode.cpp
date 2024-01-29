#include "invariantgraph/violationInvariantNodes/arrayBoolXorNode.hpp"

#include "../parseHelper.hpp"

namespace atlantis::invariantgraph {

ArrayBoolXorNode::ArrayBoolXorNode(std::vector<VarNodeId>&& as,
                                   VarNodeId output)
    : ViolationInvariantNode(std::move(as), output) {}

ArrayBoolXorNode::ArrayBoolXorNode(std::vector<VarNodeId>&& as, bool shouldHold)
    : ViolationInvariantNode(std::move(as), shouldHold) {}

void ArrayBoolXorNode::registerOutputVars(InvariantGraph& invariantGraph,
                                          propagation::SolverBase& solver) {
  if (violationVarId(invariantGraph) == propagation::NULL_ID) {
    _intermediate = solver.makeIntVar(0, 0, 0);
    if (shouldHold()) {
      setViolationVarId(invariantGraph,
                        solver.makeIntView<propagation::EqualConst>(
                            solver, _intermediate, 1));
    } else {
      assert(!isReified());
      setViolationVarId(invariantGraph,
                        solver.makeIntView<propagation::NotEqualConst>(
                            solver, _intermediate, 1));
    }
  }
}

void ArrayBoolXorNode::registerNode(InvariantGraph& invariantGraph,
                                    propagation::SolverBase& solver) {
  assert(violationVarId(invariantGraph) != propagation::NULL_ID);
  std::vector<propagation::VarId> inputs;
  std::transform(staticInputVarNodeIds().begin(), staticInputVarNodeIds().end(),
                 std::back_inserter(inputs),
                 [&](const auto& node) { return invariantGraph.varId(node); });

  solver.makeInvariant<propagation::BoolLinear>(solver, _intermediate, inputs);
}

}  // namespace atlantis::invariantgraph