#include "atlantis/invariantgraph/fzn/int_lt.hpp"

#include "../parseHelper.hpp"
#include "./fznHelper.hpp"
#include "atlantis/invariantgraph/violationInvariantNodes/intLtNode.hpp"

namespace atlantis::invariantgraph::fzn {

bool int_lt(FznInvariantGraph& graph, const fznparser::IntArg& a,
            const fznparser::IntArg& b) {
  graph.addInvariantNode(std::make_shared<IntLtNode>(
      graph, graph.retrieveVarNode(a), graph.retrieveVarNode(b)));
  return true;
}

bool int_lt(FznInvariantGraph& graph, const fznparser::IntArg& a,
            const fznparser::IntArg& b, const fznparser::BoolArg& reified) {
  graph.addInvariantNode(std::make_shared<IntLtNode>(
      graph, graph.retrieveVarNode(a), graph.retrieveVarNode(b),
      graph.retrieveVarNode(reified)));
  return true;
}

bool int_lt(FznInvariantGraph& graph, const fznparser::Constraint& constraint) {
  if (constraint.identifier() != "int_lt" &&
      constraint.identifier() != "int_lt_reif") {
    return false;
  }
  const bool isReified = constraintIdentifierIsReified(constraint);
  verifyNumArguments(constraint, isReified ? 3 : 2);
  FZN_CONSTRAINT_TYPE_CHECK(constraint, 0, fznparser::IntArg, true)
  FZN_CONSTRAINT_TYPE_CHECK(constraint, 1, fznparser::IntArg, true)

  if (!isReified) {
    return int_lt(graph,
                  std::get<fznparser::IntArg>(constraint.arguments().at(0)),
                  std::get<fznparser::IntArg>(constraint.arguments().at(1)));
  }
  FZN_CONSTRAINT_TYPE_CHECK(constraint, 2, fznparser::BoolArg, true)
  return int_lt(graph,
                std::get<fznparser::IntArg>(constraint.arguments().at(0)),
                std::get<fznparser::IntArg>(constraint.arguments().at(1)),
                std::get<fznparser::BoolArg>(constraint.arguments().at(2)));
}

}  // namespace atlantis::invariantgraph::fzn
