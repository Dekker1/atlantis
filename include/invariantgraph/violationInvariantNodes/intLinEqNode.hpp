#pragma once

#include <fznparser/model.hpp>

#include "propagation/violationInvariants/equal.hpp"
#include "invariantgraph/invariantGraph.hpp"
#include "invariantgraph/violationInvariantNode.hpp"
#include "propagation/invariants/linear.hpp"
#include "propagation/views/equalConst.hpp"
#include "propagation/views/notEqualConst.hpp"

namespace atlantis::invariantgraph {

class IntLinEqNode : public ViolationInvariantNode {
 private:
  std::vector<Int> _coeffs;
  Int _c;
  propagation::VarId _sumVarId{propagation::NULL_ID};

 public:
  static std::unique_ptr<IntLinEqNode> fromModelConstraint(
      const fznparser::Constraint&, InvariantGraph&);

  static std::vector<std::pair<std::string, size_t>> acceptedNameNumArgPairs() {
    return std::vector<std::pair<std::string, size_t>>{{"int_lin_eq", 3},
                                                       {"int_lin_eq_reif", 4}};
  }

  IntLinEqNode(std::vector<Int>&& coeffs, std::vector<VarNodeId>&& vars,
               Int c, VarNodeId r);

  IntLinEqNode(std::vector<Int>&& coeffs, std::vector<VarNodeId>&& vars,
               Int c, bool shouldHold);

  void registerOutputVars(InvariantGraph&, propagation::SolverBase& solver) override;

  void registerNode(InvariantGraph&, propagation::SolverBase&) override;

  [[nodiscard]] const std::vector<Int>& coeffs() const { return _coeffs; }

  [[nodiscard]] Int c() const { return _c; }
};

}  // namespace invariantgraph