#pragma once

#include <vector>

#include "atlantis/invariantgraph/invariantGraph.hpp"
#include "atlantis/invariantgraph/types.hpp"
#include "atlantis/invariantgraph/violationInvariantNode.hpp"
#include "atlantis/propagation/solverBase.hpp"
#include "atlantis/propagation/types.hpp"

namespace atlantis::invariantgraph {

class IntLinEqNode : public ViolationInvariantNode {
 private:
  std::vector<Int> _coeffs;
  Int _bound;
  propagation::VarId _intermediate{propagation::NULL_ID};

 public:
  IntLinEqNode(std::vector<Int>&& coeffs, std::vector<VarNodeId>&& vars,
               Int bound, bool shouldHold = true);

  IntLinEqNode(std::vector<Int>&& coeffs, std::vector<VarNodeId>&& vars,
               Int bound, VarNodeId reified);

  void init(InvariantGraph&, const InvariantNodeId&) override;

  void updateState(InvariantGraph&) override;

  void registerOutputVars(InvariantGraph&, propagation::SolverBase&) override;

  void registerNode(InvariantGraph&, propagation::SolverBase&) override;

  [[nodiscard]] const std::vector<Int>& coeffs() const;
};

}  // namespace atlantis::invariantgraph
