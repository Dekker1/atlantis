

#include "atlantis/invariantgraph/fzn/int_times.hpp"

#include "../parseHelper.hpp"
#include "./fznHelper.hpp"
#include "atlantis/invariantgraph/invariantNodes/intTimesNode.hpp"

namespace atlantis::invariantgraph::fzn {

bool int_times(FznInvariantGraph& invariantGraph, const fznparser::IntArg& a,
               const fznparser::IntArg& b, const fznparser::IntArg& product) {
  invariantGraph.addInvariantNode(std::make_unique<IntTimesNode>(
      invariantGraph.retrieveVarNode(a), invariantGraph.retrieveVarNode(b),
      invariantGraph.retrieveVarNode(product)));
  return true;
}

bool int_times(FznInvariantGraph& invariantGraph,
               const fznparser::Constraint& constraint) {
  if (constraint.identifier() != "int_times") {
    return false;
  }
  verifyNumArguments(constraint, 3);
  FZN_CONSTRAINT_TYPE_CHECK(constraint, 0, fznparser::IntArg, true)
  FZN_CONSTRAINT_TYPE_CHECK(constraint, 1, fznparser::IntArg, true)
  FZN_CONSTRAINT_TYPE_CHECK(constraint, 3, fznparser::IntArg, true)

  return int_times(invariantGraph,
                   std::get<fznparser::IntArg>(constraint.arguments().at(0)),
                   std::get<fznparser::IntArg>(constraint.arguments().at(1)),
                   std::get<fznparser::IntArg>(constraint.arguments().at(2)));
}

}  // namespace atlantis::invariantgraph::fzn
