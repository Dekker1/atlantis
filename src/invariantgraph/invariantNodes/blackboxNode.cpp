
#include "atlantis/invariantgraph/invariantNodes/blackboxNode.hpp"

#include "atlantis/misc/blackboxFunction.hpp"
#include "atlantis/propagation/invariants/blackbox.hpp"

namespace atlantis::invariantgraph {

BlackBoxNode::BlackBoxNode(std::unique_ptr<blackbox::BlackBoxFn>&& blackBoxFn,
                           std::vector<VarNodeId>&& int_in,
                           std::vector<VarNodeId>&& int_out)
    : InvariantNode(std::move(int_out), std::move(int_in)),
      _blackBoxFn(std::move(blackBoxFn)) {}

void BlackBoxNode::init(InvariantGraph& graph, const InvariantNodeId& id) {
  InvariantNode::init(graph, id);
  assert(std::all_of(outputVarNodeIds().begin(), outputVarNodeIds().end(),
                     [&](const VarNodeId& vId) {
                       return graph.varNodeConst(vId).isIntVar();
                     }));
  assert(std::all_of(staticInputVarNodeIds().begin(),
                     staticInputVarNodeIds().end(), [&](const VarNodeId& vId) {
                       return graph.varNodeConst(vId).isIntVar();
                     }));
}

void BlackBoxNode::registerOutputVars(InvariantGraph& graph,
                                      propagation::SolverBase& solver) {
  for (size_t i = 0; i < outputVarNodeIds().size(); ++i) {
    assert(graph.varNodeConst(outputVarNodeIds().at(i)).varId() ==
           propagation::NULL_ID);
    makeSolverVar(solver, graph.varNode(outputVarNodeIds().at(i)));
  }
  assert(std::all_of(outputVarNodeIds().begin(), outputVarNodeIds().end(),
                     [&](const VarNodeId& vId) {
                       return graph.varNodeConst(vId).varId() !=
                              propagation::NULL_ID;
                     }));
}

void BlackBoxNode::registerNode(InvariantGraph& graph,
                                propagation::SolverBase& solver) {
  std::vector<propagation::VarId> inputVarIds;
  std::transform(staticInputVarNodeIds().begin(), staticInputVarNodeIds().end(),
                 std::back_inserter(inputVarIds),
                 [&](const auto& id) { return graph.varId(id); });

  std::vector<propagation::VarId> outputVarIds;
  std::transform(outputVarNodeIds().begin(), outputVarNodeIds().end(),
                 std::back_inserter(outputVarIds),
                 [&](const auto& id) { return graph.varId(id); });

  solver.makeInvariant<propagation::Blackbox>(solver, std::move(_blackBoxFn),
                                              std::move(outputVarIds),
                                              std::move(inputVarIds));
}

}  // namespace atlantis::invariantgraph
