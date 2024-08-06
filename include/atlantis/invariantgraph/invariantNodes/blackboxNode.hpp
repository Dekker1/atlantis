#pragma once

#include <memory>
#include <vector>

#include "atlantis/invariantgraph/invariantGraph.hpp"
#include "atlantis/invariantgraph/invariantNode.hpp"
#include "atlantis/invariantgraph/types.hpp"
#include "atlantis/misc/blackboxFunction.hpp"
#include "atlantis/propagation/solverBase.hpp"

namespace atlantis::invariantgraph {

class BlackBoxNode : public InvariantNode {
 private:
  std::unique_ptr<blackbox::BlackBoxFn> _blackBoxFn;

 public:
  explicit BlackBoxNode(std::unique_ptr<blackbox::BlackBoxFn>&& blackBoxFn,
                        std::vector<VarNodeId>&& int_in,
                        std::vector<VarNodeId>&& int_out);

  void init(InvariantGraph&, const InvariantNodeId&) override;

  void registerOutputVars(InvariantGraph&, propagation::SolverBase&) override;

  void registerNode(InvariantGraph&, propagation::SolverBase&) override;
};

}  // namespace atlantis::invariantgraph
