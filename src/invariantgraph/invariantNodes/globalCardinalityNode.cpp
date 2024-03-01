#include "atlantis/invariantgraph/invariantNodes/globalCardinalityNode.hpp"

#include <utility>

#include "../parseHelper.hpp"
#include "atlantis/propagation/invariants/exists.hpp"
#include "atlantis/propagation/invariants/globalCardinalityOpen.hpp"
#include "atlantis/propagation/invariants/linear.hpp"
#include "atlantis/propagation/views/equalConst.hpp"
#include "atlantis/propagation/views/notEqualConst.hpp"
#include "atlantis/propagation/violationInvariants/equal.hpp"
#include "atlantis/propagation/violationInvariants/notEqual.hpp"

namespace atlantis::invariantgraph {

GlobalCardinalityNode::GlobalCardinalityNode(std::vector<VarNodeId>&& inputs,
                                             std::vector<Int>&& cover,
                                             std::vector<VarNodeId>&& counts)
    : InvariantNode(std::move(counts), std::move(inputs)),
      _cover(std::move(cover)) {}

void GlobalCardinalityNode::registerOutputVars(
    InvariantGraph& invariantGraph, propagation::SolverBase& solver) {
  for (const VarNodeId& countOutput : outputVarNodeIds()) {
    if (invariantGraph.varId(countOutput) == propagation::NULL_ID) {
      makeSolverVar(solver, invariantGraph.varNode(countOutput));
    }
  }
}

void GlobalCardinalityNode::registerNode(InvariantGraph& invariantGraph,
                                         propagation::SolverBase& solver) {
  std::vector<propagation::VarId> inputVarIds;
  std::transform(staticInputVarNodeIds().begin(), staticInputVarNodeIds().end(),
                 std::back_inserter(inputVarIds),
                 [&](const auto& id) { return invariantGraph.varId(id); });

  std::vector<propagation::VarId> outputVarIds;
  std::transform(outputVarNodeIds().begin(), outputVarNodeIds().end(),
                 std::back_inserter(outputVarIds),
                 [&](const auto& id) { return invariantGraph.varId(id); });

  solver.makeInvariant<propagation::GlobalCardinalityOpen>(
      solver, std::move(outputVarIds), std::move(inputVarIds),
      std::vector<Int>(_cover));
}

}  // namespace atlantis::invariantgraph
