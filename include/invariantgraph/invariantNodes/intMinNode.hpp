#pragma once

#include <cmath>

#include "invariantgraph/invariantGraph.hpp"
#include "invariantgraph/invariantNode.hpp"
#include "propagation/invariants/binaryMin.hpp"

namespace atlantis::invariantgraph {

class IntMinNode : public InvariantNode {
 public:
  IntMinNode(VarNodeId a, VarNodeId b, VarNodeId output);

  ~IntMinNode() override = default;

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