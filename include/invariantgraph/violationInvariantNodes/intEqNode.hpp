#pragma once

#include <fznparser/model.hpp>
#include <utility>

#include "propagation/violationInvariants/equal.hpp"
#include "propagation/violationInvariants/notEqual.hpp"
#include "invariantgraph/invariantGraph.hpp"
#include "invariantgraph/violationInvariantNode.hpp"

namespace atlantis::invariantgraph {

class IntEqNode : public ViolationInvariantNode {
 public:
  explicit IntEqNode(VarNodeId a, VarNodeId b, VarNodeId r);

  explicit IntEqNode(VarNodeId a, VarNodeId b, bool shouldHold = true);

  static std::vector<std::pair<std::string, size_t>> acceptedNameNumArgPairs() {
    return std::vector<std::pair<std::string, size_t>>{{"int_eq", 2},
                                                       {"int_eq_reif", 3}};
  }

  static std::unique_ptr<IntEqNode> fromModelConstraint(
      const fznparser::Constraint&, InvariantGraph&);

  void registerOutputVars(InvariantGraph&, propagation::SolverBase& solver) override;

  void registerNode(InvariantGraph&, propagation::SolverBase& solver) override;

  [[nodiscard]] VarNodeId a() const noexcept {
    return staticInputVarNodeIds().front();
  }
  [[nodiscard]] VarNodeId b() const noexcept {
    return staticInputVarNodeIds().back();
  }
};

}  // namespace invariantgraph