#include "invariantgraph/views/intLtReifNode.hpp"

#include "../parseHelper.hpp"
#include "invariantgraph/constraints/intEqNode.hpp"
#include "invariantgraph/views/reifiedConstraint.hpp"

std::unique_ptr<invariantgraph::IntLtReifNode>
invariantgraph::IntLtReifNode::fromModelConstraint(
    const fznparser::FZNModel&, const fznparser::Constraint& constraint,
    const std::function<VariableNode*(MappableValue&)>& variableMap) {
  assert(constraint.name == "int_lt_reif");
  assert(constraint.arguments.size() == 3);

  auto a = mappedVariable(constraint.arguments[0], variableMap);
  auto b = mappedVariable(constraint.arguments[1], variableMap);
  auto r = mappedVariable(constraint.arguments[2], variableMap);

  return std::make_unique<invariantgraph::IntLtReifNode>(
      std::make_unique<invariantgraph::IntEqNode>(a, b), r);
}
