#pragma once

#include <vector>

#include "atlantis/invariantgraph/invariantGraph.hpp"
#include "atlantis/invariantgraph/types.hpp"
#include "atlantis/invariantgraph/violationInvariantNode.hpp"
#include "atlantis/propagation/solverBase.hpp"

namespace atlantis::invariantgraph {

class BoolEqNode : public ViolationInvariantNode {
 public:
  explicit BoolEqNode(VarNodeId a, VarNodeId b, VarNodeId r);

  explicit BoolEqNode(VarNodeId a, VarNodeId b, bool shouldHold = true);

  void registerOutputVars(InvariantGraph&,
                          propagation::SolverBase& solver) override;

  void registerNode(InvariantGraph&, propagation::SolverBase& solver) override;

  [[nodiscard]] VarNodeId a() const noexcept {
    return staticInputVarNodeIds().front();
  }
  [[nodiscard]] VarNodeId b() const noexcept {
    return staticInputVarNodeIds().back();
  }
};

}  // namespace atlantis::invariantgraph
