#pragma once

#include <fznparser/model.hpp>
#include <utility>

#include "invariantgraph/invariantGraph.hpp"
#include "invariantgraph/violationInvariantNode.hpp"
#include "propagation/violationInvariants/boolAllEqual.hpp"
#include "propagation/views/notEqualConst.hpp"

namespace atlantis::invariantgraph {
class BoolAllEqualNode : public ViolationInvariantNode {
 private:
  propagation::VarId _intermediate{propagation::NULL_ID};

 public:
  explicit BoolAllEqualNode(std::vector<VarNodeId>&& vars, VarNodeId r);

  explicit BoolAllEqualNode(std::vector<VarNodeId>&& vars,
                            bool shouldHold = true);

  static std::vector<std::pair<std::string, size_t>> acceptedNameNumArgPairs() {
    return std::vector<std::pair<std::string, size_t>>{
        {"fzn_all_equal_bool", 1}, {"fzn_all_equal_bool_reif", 2}};
  }

  static std::unique_ptr<BoolAllEqualNode> fromModelConstraint(
      const fznparser::Constraint&, InvariantGraph&);

  bool prune(InvariantGraph&) override;

  void registerOutputVars(InvariantGraph&,
                               propagation::SolverBase& solver) override;

  void registerNode(InvariantGraph&, propagation::SolverBase& solver) override;
};
}  // namespace atlantis::invariantgraph