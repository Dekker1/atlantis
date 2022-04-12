#include "invariantgraph/invariants/maxNode.hpp"

#include <algorithm>

#include "../parseHelper.hpp"
#include "invariants/maxSparse.hpp"

std::unique_ptr<invariantgraph::MaxNode>
invariantgraph::MaxNode::fromModelConstraint(
    const fznparser::FZNModel& model, const fznparser::Constraint& constraint,
    const std::function<VariableNode*(MappableValue&)>& variableMap) {
  assert(constraint.name == "array_int_maximum");
  assert(constraint.arguments.size() == 2);

  auto inputs =
      mappedVariableVector(model, constraint.arguments[1], variableMap);
  auto output = mappedVariable(constraint.arguments[0], variableMap);
  assert(definesVariable(constraint, *output->variable()));

  return std::make_unique<invariantgraph::MaxNode>(inputs, output);
}

void invariantgraph::MaxNode::registerWithEngine(
    Engine& engine, VariableDefiningNode::VariableMap& variableMap) {
  std::vector<VarId> variables;
  std::transform(_variables.begin(), _variables.end(),
                 std::back_inserter(variables),
                 [&](const auto& var) { return variableMap.at(var); });

  auto outputId =
      registerDefinedVariable(engine, variableMap, definedVariables()[0]);
  engine.makeInvariant<::MaxSparse>(variables, outputId);
}
