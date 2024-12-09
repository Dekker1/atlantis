
#include "atlantis/invariantgraph/invariantNodes/blackboxNode.hpp"

#include "atlantis/misc/blackboxFunction.hpp"
#include "atlantis/propagation/invariants/blackbox.hpp"

namespace atlantis::invariantgraph {

BlackBoxNode::BlackBoxNode(IInvariantGraph& graph,
                           std::unique_ptr<blackbox::BlackBoxFn>&& blackBoxFn,
                           std::vector<VarNodeId>&& int_in,
                           std::vector<VarNodeId>&& int_out)
    : InvariantNode(graph, std::move(int_out), std::move(int_in)),
      _blackBoxFn(std::move(blackBoxFn)) {}

void BlackBoxNode::init(InvariantNodeId id) {
  InvariantNode::init(id);
  assert(std::all_of(outputVarNodeIds().begin(), outputVarNodeIds().end(),
                     [&](const VarNodeId& vId) {
                       return invariantGraphConst().varNodeConst(vId).isIntVar();
                     }));
  assert(std::all_of(staticInputVarNodeIds().begin(),
                     staticInputVarNodeIds().end(), [&](const VarNodeId& vId) {
                       return invariantGraphConst().varNodeConst(vId).isIntVar();
                     }));
}

void BlackBoxNode::registerOutputVars() {
  for (size_t i = 0; i < outputVarNodeIds().size(); ++i) {
    assert(invariantGraph().varNodeConst(outputVarNodeIds().at(i)).varId() ==
           propagation::NULL_ID);
    makeSolverVar(outputVarNodeIds().at(i));
  }
  assert(std::all_of(outputVarNodeIds().begin(), outputVarNodeIds().end(),
                     [&](const VarNodeId& vId) {
                       return invariantGraph().varNodeConst(vId).varId() !=
                              propagation::NULL_ID;
                     }));
}

void BlackBoxNode::registerNode() {
  std::vector<propagation::VarViewId> inputVarIds;
  std::transform(staticInputVarNodeIds().begin(), staticInputVarNodeIds().end(),
                 std::back_inserter(inputVarIds),
                 [&](const auto& varNodeId) { return invariantGraph().varId(varNodeId); });

  std::vector<propagation::VarViewId> outputVarIds;
  std::transform(outputVarNodeIds().begin(), outputVarNodeIds().end(),
                 std::back_inserter(outputVarIds),
                 [&](const auto& varNodeId) { return invariantGraph().varId(varNodeId); });

  solver().makeInvariant<propagation::Blackbox>(solver(), std::move(_blackBoxFn),
                                              std::move(outputVarIds),
                                              std::move(inputVarIds));
}

std::string BlackBoxNode::dotLangIdentifier() const { return "blackbox"; }

}  // namespace atlantis::invariantgraph
