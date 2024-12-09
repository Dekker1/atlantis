#pragma once

#include <memory>
#include <vector>

#include "atlantis/invariantgraph/invariantNode.hpp"
#include "atlantis/misc/blackboxFunction.hpp"

namespace atlantis::invariantgraph {

class BlackBoxNode : public InvariantNode {
 private:
  std::unique_ptr<blackbox::BlackBoxFn> _blackBoxFn;

 public:
  explicit BlackBoxNode(IInvariantGraph& graph,

                        std::unique_ptr<blackbox::BlackBoxFn>&& blackBoxFn,
                        std::vector<VarNodeId>&& int_in,
                        std::vector<VarNodeId>&& int_out);

  void init(InvariantNodeId) override;

  void registerOutputVars() override;

  void registerNode() override;

  virtual std::string dotLangIdentifier() const override;
};

}  // namespace atlantis::invariantgraph
