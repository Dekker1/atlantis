#include "invariantgraph/implicitConstraintNode.hpp"

#include "invariantgraph/invariantGraph.hpp"

namespace invariantgraph {

ImplicitConstraintNode::ImplicitConstraintNode(
    std::vector<VarNodeId>&& outputVarNodeIds)
    : InvariantNode(std::move(outputVarNodeIds)) {}

void ImplicitConstraintNode::registerOutputVariables(
    InvariantGraph& invariantGraph, Engine& engine) {
  for (const auto& varNodeId : outputVarNodeIds()) {
    auto& varNode = invariantGraph.varNode(varNodeId);
    if (varNode.varId() == NULL_ID) {
      const auto& [lb, ub] = varNode.bounds();
      varNode.setVarId(engine.makeIntVar(lb, lb, ub));
    }
  }
}

std::shared_ptr<search::neighbourhoods::Neighbourhood>
ImplicitConstraintNode::neighbourhood() noexcept {
  return _neighbourhood;
}

void ImplicitConstraintNode::registerNode(InvariantGraph& invariantGraph,
                                          Engine& engine) {
  if (_neighbourhood != nullptr) {
    return;
  }
  std::vector<search::SearchVariable> varIds;
  varIds.reserve(outputVarNodeIds().size());

  for (const auto& id : outputVarNodeIds()) {
    auto& node = invariantGraph.varNode(id);
    assert(node.varId() != NULL_ID);
    varIds.emplace_back(node.varId(), node.domain());
  }

  _neighbourhood = createNeighbourhood(engine, std::move(varIds));
  assert(_neighbourhood);
}

}  // namespace invariantgraph