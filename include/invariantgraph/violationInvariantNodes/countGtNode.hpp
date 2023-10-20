#pragma once

#include <fznparser/model.hpp>
#include <utility>

#include "constraints/lessEqual.hpp"
#include "constraints/lessThan.hpp"
#include "invariantgraph/invariantGraph.hpp"
#include "invariantgraph/violationInvariantNode.hpp"
#include "invariants/count.hpp"
#include "invariants/countConst.hpp"
#include "views/equalConst.hpp"
#include "views/greaterEqualConst.hpp"
#include "views/lessEqualConst.hpp"
#include "views/notEqualConst.hpp"

namespace invariantgraph {
class CountGtNode : public ViolationInvariantNode {
 private:
  const bool _yIsParameter;
  const Int _yParameter;
  const bool _cIsParameter;
  const Int _cParameter;
  VarId _intermediate{NULL_ID};

  explicit CountGtNode(std::vector<VarNodeId>&& x, VarNodeId y, Int yParameter,
                       VarNodeId c, Int cParameter, VarNodeId r);

  explicit CountGtNode(std::vector<VarNodeId>&& x, VarNodeId y, Int yParameter,
                       VarNodeId c, Int cParameter, bool shouldHold);

 public:
  explicit CountGtNode(std::vector<VarNodeId>&& x, VarNodeId y, VarNodeId c,
                       VarNodeId r);

  explicit CountGtNode(std::vector<VarNodeId>&& x, Int yParameter, VarNodeId c,
                       VarNodeId r);

  explicit CountGtNode(std::vector<VarNodeId>&& x, VarNodeId y, Int cParameter,
                       VarNodeId r);

  explicit CountGtNode(std::vector<VarNodeId>&& x, Int yParameter,
                       Int cParameter, VarNodeId r);

  explicit CountGtNode(std::vector<VarNodeId>&& x, VarNodeId y, VarNodeId c,
                       bool shouldHold);

  explicit CountGtNode(std::vector<VarNodeId>&& x, Int yParameter, VarNodeId c,
                       bool shouldHold);

  explicit CountGtNode(std::vector<VarNodeId>&& x, VarNodeId y, Int cParameter,
                       bool shouldHold);

  explicit CountGtNode(std::vector<VarNodeId>&& x, Int yParameter,
                       Int cParameter, bool shouldHold);

  static std::vector<std::pair<std::string, size_t>> acceptedNameNumArgPairs() {
    return std::vector<std::pair<std::string, size_t>>{
        {"fzn_count_gt", 3}, {"fzn_count_gt_reif", 4}};
  }

  static std::unique_ptr<CountGtNode> fromModelConstraint(
      const fznparser::Constraint&, InvariantGraph&);

  void registerOutputVariables(InvariantGraph&, Engine& engine) override;

  void registerNode(InvariantGraph&, Engine& engine) override;

  [[nodiscard]] VarNodeId yVarNode() const;

  [[nodiscard]] VarNodeId cVarNode() const;
};
}  // namespace invariantgraph