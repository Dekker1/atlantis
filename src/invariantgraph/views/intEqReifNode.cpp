#include "invariantgraph/views/intEqReifNode.hpp"

#include "../parseHelper.hpp"
#include "invariantgraph/constraints/intEqNode.hpp"
#include "invariantgraph/views/reifiedConstraint.hpp"

std::unique_ptr<invariantgraph::IntEqReifNode>
invariantgraph::IntEqReifNode::fromModelConstraint(
    const std::shared_ptr<fznparser::Constraint> &constraint,
    const std::function<VariableNode *(std::shared_ptr<fznparser::Variable>)>
        &variableMap) {
  assert(constraint->name() == "int_eq_reif");
  assert(constraint->arguments().size() == 3);

  MAPPED_SEARCH_VARIABLE_ARG(a, constraint->arguments()[0], variableMap);
  MAPPED_SEARCH_VARIABLE_ARG(b, constraint->arguments()[1], variableMap);
  MAPPED_SEARCH_VARIABLE_ARG(r, constraint->arguments()[2], variableMap);

  return std::make_unique<invariantgraph::IntEqReifNode>(
      std::make_unique<invariantgraph::IntEqNode>(a, b), r);
}
