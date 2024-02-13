#include "invariantgraph/fzn/bool_xor.hpp"

#include "../parseHelper.hpp"
#include "./fznHelper.hpp"
#include "invariantgraph/fzn/bool_eq.hpp"

namespace atlantis::invariantgraph::fzn {

bool bool_xor(FznInvariantGraph& invariantGraph, VarNodeId a, VarNodeId b) {
  invariantGraph.addInvariantNode(std::make_unique<BoolEqNode>(a, b, true));
  return true;
}

bool bool_xor(FznInvariantGraph& invariantGraph, const fznparser::BoolArg& a,
              const fznparser::BoolArg& b) {
  return bool_xor(invariantGraph, invariantGraph.createVarNodeFromFzn(a, false),
                  invariantGraph.createVarNodeFromFzn(b, false));
}

bool bool_xor(FznInvariantGraph& invariantGraph, VarNodeId a, VarNodeId b,
              VarNodeId reified) {
  const auto& reifiedVarNode = invariantGraph.varNode(reified);
  if (reifiedVarNode.isFixed()) {
    if (reifiedVarNode.lowerBound() == 0) {
      return bool_xor(invariantGraph, a, b);
    }
    // !(a xor b) == (x == b)
    return bool_eq(invariantGraph, a, b);
  }

  invariantGraph.addInvariantNode(std::make_unique<BoolEqNode>(a, b, reified));

  return true;
}

bool bool_xor(FznInvariantGraph& invariantGraph, const fznparser::BoolArg& a,
              const fznparser::BoolArg& b, const fznparser::BoolArg& reified) {
  if (reified.isFixed()) {
    if (reified.toParameter()) {
      return bool_xor(invariantGraph, a, b);
    }
    // !(a xor b) == (x == b)
    return bool_eq(invariantGraph, a, b);
  }

  invariantGraph.addInvariantNode(std::make_unique<BoolEqNode>(
      invariantGraph.createVarNodeFromFzn(a, false),
      invariantGraph.createVarNodeFromFzn(b, false),
      invariantGraph.createVarNodeFromFzn(reified.var(), true)));

  return true;
}

bool bool_xor(FznInvariantGraph& invariantGraph,
              const fznparser::Constraint& constraint) {
  if (constraint.identifier() != "bool_xor") {
    return false;
  }

  bool isReified = constraint.arguments().size() >= 3;
  verifyNumArguments(constraint, isReified ? 3 : 2);
  FZN_CONSTRAINT_TYPE_CHECK(constraint, 0, fznparser::BoolArg, true)
  FZN_CONSTRAINT_TYPE_CHECK(constraint, 1, fznparser::BoolArg, true)

  if (!isReified) {
    return bool_xor(invariantGraph,
                    std::get<fznparser::BoolArg>(constraint.arguments().at(0)),
                    std::get<fznparser::BoolArg>(constraint.arguments().at(1)));
  }
  FZN_CONSTRAINT_TYPE_CHECK(constraint, 2, fznparser::BoolArg, true)
  return bool_xor(invariantGraph,
                  std::get<fznparser::BoolArg>(constraint.arguments().at(0)),
                  std::get<fznparser::BoolArg>(constraint.arguments().at(1)),
                  std::get<fznparser::BoolArg>(constraint.arguments().at(2)));
}

}  // namespace atlantis::invariantgraph::fzn