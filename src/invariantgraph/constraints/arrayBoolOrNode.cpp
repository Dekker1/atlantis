#include "invariantgraph/constraints/arrayBoolOrNode.hpp"

#include "../parseHelper.hpp"

std::unique_ptr<invariantgraph::ArrayBoolOrNode>
invariantgraph::ArrayBoolOrNode::fromModelConstraint(
    const fznparser::FZNModel& model, const fznparser::Constraint& constraint,
    const std::function<VariableNode*(MappableValue&)>& variableMap) {
  assert(hasCorrectSignature(acceptedNameNumArgPairs(), constraint));

  auto as = mappedVariableVector(model, constraint.arguments[0], variableMap);

  if (std::holds_alternative<bool>(constraint.arguments[1])) {
    auto shouldHold = std::get<bool>(constraint.arguments[1]);
    return std::make_unique<invariantgraph::ArrayBoolOrNode>(as, shouldHold);
  } else {
    auto r = mappedVariable(constraint.arguments[1], variableMap);
    return std::make_unique<invariantgraph::ArrayBoolOrNode>(as, r);
  }
  return std::make_unique<invariantgraph::ArrayBoolOrNode>(as, true);
}

void invariantgraph::ArrayBoolOrNode::createDefinedVariables(Engine& engine) {
  if (violationVarId() == NULL_ID) {
    if (shouldHold()) {
      registerViolation(engine);
    } else {
      assert(!isReified());
      _intermediate = engine.makeIntVar(0, 0, 0);
      setViolationVarId(engine.makeIntView<NotEqualConst>(_intermediate, 0));
    }
  }
}

void invariantgraph::ArrayBoolOrNode::registerWithEngine(Engine& engine) {
  assert(violationVarId() != NULL_ID);
  std::vector<VarId> inputs;
  std::transform(staticInputs().begin(), staticInputs().end(),
                 std::back_inserter(inputs),
                 [&](const auto& node) { return node->varId(); });

  engine.makeInvariant<Exists>(!shouldHold() ? _intermediate : violationVarId(),
                               inputs);
}
