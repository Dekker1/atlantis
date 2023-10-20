#pragma once

#include <fznparser/model.hpp>
#include <utility>

#include "constraints/equal.hpp"
#include "constraints/globalCardinalityConst.hpp"
#include "constraints/notEqual.hpp"
#include "invariantgraph/invariantGraph.hpp"
#include "invariantgraph/violationInvariantNode.hpp"
#include "invariants/exists.hpp"
#include "invariants/linear.hpp"
#include "views/notEqualConst.hpp"

namespace invariantgraph {
class GlobalCardinalityLowUpClosedNode : public ViolationInvariantNode {
 private:
  const std::vector<Int> _cover;
  const std::vector<Int> _low;
  const std::vector<Int> _up;
  VarId _intermediate{NULL_ID};

 public:
  explicit GlobalCardinalityLowUpClosedNode(std::vector<VarNodeId>&& x,
                                            std::vector<Int>&& cover,
                                            std::vector<Int>&& low,
                                            std::vector<Int>&& up, VarNodeId r);

  explicit GlobalCardinalityLowUpClosedNode(std::vector<VarNodeId>&& x,
                                            std::vector<Int>&& cover,
                                            std::vector<Int>&& low,
                                            std::vector<Int>&& up,
                                            bool shouldHold);

  static std::vector<std::pair<std::string, size_t>> acceptedNameNumArgPairs() {
    return std::vector<std::pair<std::string, size_t>>{
        {"fzn_global_cardinality_low_up_closed", 4},
        {"fzn_global_cardinality_low_up_closed_reif", 5}};
  }

  static std::unique_ptr<GlobalCardinalityLowUpClosedNode> fromModelConstraint(
      const fznparser::Constraint&, InvariantGraph&);

  void registerOutputVariables(InvariantGraph&, Engine& engine) override;

  void registerNode(InvariantGraph&, Engine& engine) override;
};
}  // namespace invariantgraph