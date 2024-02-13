#pragma once

#include "invariantgraph/invariantGraph.hpp"
#include "invariantgraph/violationInvariantNode.hpp"
#include "propagation/invariants/forAll.hpp"
#include "propagation/views/elementConst.hpp"
#include "propagation/views/notEqualConst.hpp"

namespace atlantis::invariantgraph {

class ArrayBoolAndNode : public ViolationInvariantNode {
 private:
  propagation::VarId _intermediate{propagation::NULL_ID};

 public:
  ArrayBoolAndNode(std::vector<VarNodeId>&& as, VarNodeId output);

  ArrayBoolAndNode(std::vector<VarNodeId>&& as, bool shouldHold);

  void registerOutputVars(InvariantGraph&,
                          propagation::SolverBase& solver) override;

  void registerNode(InvariantGraph&, propagation::SolverBase& solver) override;
};

}  // namespace atlantis::invariantgraph