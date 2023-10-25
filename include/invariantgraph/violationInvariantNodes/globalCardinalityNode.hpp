#pragma once

#include <fznparser/model.hpp>
#include <utility>

#include "propagation/violationInvariants/equal.hpp"
#include "propagation/violationInvariants/notEqual.hpp"
#include "invariantgraph/invariantGraph.hpp"
#include "invariantgraph/violationInvariantNode.hpp"
#include "propagation/invariants/exists.hpp"
#include "propagation/invariants/globalCardinalityOpen.hpp"
#include "propagation/invariants/linear.hpp"
#include "propagation/views/equalConst.hpp"
#include "propagation/views/notEqualConst.hpp"

namespace atlantis::invariantgraph {
class GlobalCardinalityNode : public ViolationInvariantNode {
 private:
  const std::vector<VarNodeId> _inputs;
  const std::vector<Int> _cover;
  const std::vector<VarNodeId> _counts;
  std::vector<propagation::VarId> _intermediate{};
  std::vector<propagation::VarId> _violations{};

 public:
  explicit GlobalCardinalityNode(std::vector<VarNodeId>&& x,
                                 std::vector<Int>&& cover,
                                 std::vector<VarNodeId>&& counts, VarNodeId r);

  explicit GlobalCardinalityNode(std::vector<VarNodeId>&& x,
                                 std::vector<Int>&& cover,
                                 std::vector<VarNodeId>&& counts,
                                 bool shouldHold);

  static std::vector<std::pair<std::string, size_t>> acceptedNameNumArgPairs() {
    return std::vector<std::pair<std::string, size_t>>{
        {"fzn_global_cardinality", 3}, {"fzn_global_cardinality_reif", 4}};
  }

  static std::unique_ptr<GlobalCardinalityNode> fromModelConstraint(
      const fznparser::Constraint&, InvariantGraph&);

  void registerOutputVars(InvariantGraph&, propagation::SolverBase& solver) override;

  void registerNode(InvariantGraph&, propagation::SolverBase& solver) override;

  [[nodiscard]] inline const std::vector<VarNodeId>& inputs() const {
    return _inputs;
  }

  [[nodiscard]] inline const std::vector<VarNodeId>& counts() const {
    return _counts;
  }
};
}  // namespace invariantgraph