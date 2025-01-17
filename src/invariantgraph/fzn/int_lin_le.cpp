#include "atlantis/invariantgraph/fzn/int_lin_le.hpp"

#include "../parseHelper.hpp"
#include "./fznHelper.hpp"
#include "atlantis/invariantgraph/violationInvariantNodes/intLinLeNode.hpp"

namespace atlantis::invariantgraph::fzn {

static void verifyInputs(
    const std::vector<Int>& coeffs,
    const std::shared_ptr<fznparser::IntVarArray>& inputs) {
  if (coeffs.size() != inputs->size()) {
    throw FznArgumentException(
        "int_lin_le constraint first and second array arguments must have the "
        "same length");
  }
}

bool int_lin_le(FznInvariantGraph& graph, std::vector<Int>&& coeffs,
                const std::shared_ptr<fznparser::IntVarArray>& inputs,
                Int bound) {
  verifyInputs(coeffs, inputs);
  if (coeffs.empty()) {
    if (bound >= 0) {
      return true;
    }
    throw FznArgumentException(
        "int_lin_le constraint: total of empty arrays is always greater than " +
        std::to_string(bound));
  }

  graph.addInvariantNode(std::make_shared<IntLinLeNode>(
      graph, std::move(coeffs), graph.retrieveVarNodes(inputs), bound));

  return true;
}

bool int_lin_le(FznInvariantGraph& graph, std::vector<Int>&& coeffs,
                const std::shared_ptr<fznparser::IntVarArray>& inputs,
                Int bound, const fznparser::BoolArg& reified) {
  verifyInputs(coeffs, inputs);

  graph.addInvariantNode(std::make_shared<IntLinLeNode>(
      graph, std::move(coeffs), graph.retrieveVarNodes(inputs), bound,
      graph.retrieveVarNode(reified)));

  return true;
}

bool int_lin_le(FznInvariantGraph& graph,
                const fznparser::Constraint& constraint) {
  if (constraint.identifier() != "int_lin_le" &&
      constraint.identifier() != "int_lin_le_reif") {
    return false;
  }
  const bool isReified = constraintIdentifierIsReified(constraint);
  verifyNumArguments(constraint, isReified ? 4 : 3);
  FZN_CONSTRAINT_ARRAY_TYPE_CHECK(constraint, 0, fznparser::IntVarArray, false)
  FZN_CONSTRAINT_ARRAY_TYPE_CHECK(constraint, 1, fznparser::IntVarArray, true)
  FZN_CONSTRAINT_TYPE_CHECK(constraint, 2, fznparser::IntArg, false)

  std::vector<Int> coeffs =
      getArgArray<fznparser::IntVarArray>(constraint.arguments().at(0))
          ->toParVector();

  if (!isReified) {
    return int_lin_le(
        graph, std::move(coeffs),
        getArgArray<fznparser::IntVarArray>(constraint.arguments().at(1)),
        std::get<fznparser::IntArg>(constraint.arguments().at(2))
            .toParameter());
  }
  FZN_CONSTRAINT_TYPE_CHECK(constraint, 3, fznparser::BoolArg, true)
  return int_lin_le(
      graph, std::move(coeffs),
      getArgArray<fznparser::IntVarArray>(constraint.arguments().at(1)),
      std::get<fznparser::IntArg>(constraint.arguments().at(2)).toParameter(),
      std::get<fznparser::BoolArg>(constraint.arguments().at(3)));
}

}  // namespace atlantis::invariantgraph::fzn
