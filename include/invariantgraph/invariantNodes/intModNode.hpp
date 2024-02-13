#pragma once

#include "invariantgraph/invariantGraph.hpp"
#include "invariantgraph/invariantNode.hpp"
#include "propagation/invariants/mod.hpp"

namespace atlantis::invariantgraph {

class IntModNode : public InvariantNode {
 public:
  IntModNode(VarNodeId numerator, VarNodeId denominator, VarNodeId remainder);

  ~IntModNode() override = default;

  void registerOutputVars(InvariantGraph&,
                          propagation::SolverBase& solver) override;

  void registerNode(InvariantGraph&, propagation::SolverBase& solver) override;

  [[nodiscard]] VarNodeId numerator() const noexcept {
    return staticInputVarNodeIds().front();
  }
  [[nodiscard]] VarNodeId denominator() const noexcept {
    return staticInputVarNodeIds().back();
  }
};

}  // namespace atlantis::invariantgraph