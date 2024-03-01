#pragma once

#include <vector>

#include "atlantis/invariantgraph/invariantGraph.hpp"
#include "atlantis/invariantgraph/invariantNode.hpp"
#include "atlantis/invariantgraph/types.hpp"
#include "atlantis/propagation/solverBase.hpp"
#include "atlantis/types.hpp"

namespace atlantis::invariantgraph {
class BoolLinearNode : public InvariantNode {
 private:
  std::vector<Int> _coeffs;

 public:
  BoolLinearNode(std::vector<Int>&& coeffs, std::vector<VarNodeId>&& vars,
                 VarNodeId output);

  ~BoolLinearNode() override = default;

  void registerOutputVars(InvariantGraph&,
                          propagation::SolverBase& solver) override;

  void registerNode(InvariantGraph&, propagation::SolverBase& solver) override;

  [[nodiscard]] const std::vector<Int>& coeffs() const { return _coeffs; }
};
}  // namespace atlantis::invariantgraph
