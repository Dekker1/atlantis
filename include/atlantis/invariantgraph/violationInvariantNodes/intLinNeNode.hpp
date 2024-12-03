#pragma once

#include "atlantis/invariantgraph/violationInvariantNode.hpp"

namespace atlantis::invariantgraph {

class IntLinNeNode : public ViolationInvariantNode {
 private:
  std::vector<Int> _coeffs;
  Int _bound;
  propagation::VarViewId _intermediate{propagation::NULL_ID};

 public:
  IntLinNeNode(IInvariantGraph& graph, std::vector<Int>&& coeffs,
               std::vector<VarNodeId>&& vars, Int bound,
               bool shouldHold = true);

  IntLinNeNode(IInvariantGraph& graph, std::vector<Int>&& coeffs,
               std::vector<VarNodeId>&& vars, Int bound, VarNodeId reified);

  void init(InvariantNodeId) override;

  void updateState() override;

  void registerOutputVars() override;

  void registerNode() override;

  [[nodiscard]] const std::vector<Int>& coeffs() const;

  virtual std::string dotLangIdentifier() const override;
};

}  // namespace atlantis::invariantgraph
