#include "invariantgraph/constraints/globalCardinalityNode.hpp"

#include "../parseHelper.hpp"

std::unique_ptr<invariantgraph::GlobalCardinalityNode>
invariantgraph::GlobalCardinalityNode::fromModelConstraint(
    const fznparser::FZNModel& model, const fznparser::Constraint& constraint,
    const std::function<VariableNode*(MappableValue&)>& variableMap) {
  assert(hasCorrectSignature(acceptedNameNumArgPairs(), constraint));

  auto x = mappedVariableVector(model, constraint.arguments[0], variableMap);

  auto cover = integerVector(model, constraint.arguments[1]);

  auto counts =
      mappedVariableVector(model, constraint.arguments[2], variableMap);

  assert(cover.size() == counts.size());

  bool shouldHold = true;
  VariableNode* r = nullptr;

  if (constraint.arguments.size() >= 4) {
    if (std::holds_alternative<bool>(constraint.arguments[3])) {
      shouldHold = std::get<bool>(constraint.arguments[3]);
    } else {
      r = mappedVariable(constraint.arguments[3], variableMap);
    }
  }

  if (r != nullptr) {
    return std::make_unique<GlobalCardinalityNode>(x, cover, counts, r);
  }
  assert(r == nullptr);
  return std::make_unique<GlobalCardinalityNode>(x, cover, counts, shouldHold);
}

void invariantgraph::GlobalCardinalityNode::createDefinedVariables(
    Engine& engine) {
  if (!isReified() && shouldHold()) {
    for (auto* const countOutput : definedVariables()) {
      if (countOutput->varId() == NULL_ID) {
        countOutput->setVarId(engine.makeIntVar(0, 0, _inputs.size()));
      }
    }
  } else if (violationVarId() == NULL_ID) {
    registerViolation(engine);

    for (size_t i = 0; i < _counts.size(); ++i) {
      _intermediate.emplace_back(engine.makeIntVar(0, 0, _inputs.size()));
    }
    if (_counts.size() == 1) {
      _violations.emplace_back(violationVarId());
    } else {
      for (size_t i = 0; i < _counts.size(); ++i) {
        _violations.emplace_back(engine.makeIntVar(0, 0, _inputs.size()));
      }
    }
  }
}

void invariantgraph::GlobalCardinalityNode::registerWithEngine(Engine& engine) {
  std::vector<VarId> inputs;
  std::transform(_inputs.begin(), _inputs.end(), std::back_inserter(inputs),
                 [&](auto node) { return node->varId(); });

  if (!isReified() && shouldHold()) {
    std::vector<VarId> countOutputs;
    std::transform(_counts.begin(), _counts.end(),
                   std::back_inserter(countOutputs),
                   [&](auto node) { return node->varId(); });

    engine.makeInvariant<GlobalCardinalityOpen>(inputs, _cover, countOutputs);
  } else {
    assert(violationVarId() != NULL_ID);
    assert(_intermediate.size() == _counts.size());
    assert(_violations.size() == _counts.size());
    engine.makeInvariant<GlobalCardinalityOpen>(inputs, _cover, _intermediate);
    for (size_t i = 0; i < _counts.size(); ++i) {
      if (shouldHold()) {
        engine.makeConstraint<Equal>(_violations.at(i), _intermediate.at(i),
                                     _counts.at(i)->varId());
      } else {
        engine.makeConstraint<NotEqual>(_violations.at(i), _intermediate.at(i),
                                        _counts.at(i)->varId());
      }
    }
    if (_counts.size() > 1) {
      if (shouldHold()) {
        // To hold, each count must be equal to its corresponding intermediate:
        engine.makeInvariant<Linear>(_violations, violationVarId());
      } else {
        // To hold, only one count must not be equal to its corresponding
        // intermediate:
        engine.makeInvariant<Exists>(_violations, violationVarId());
      }
    }
  }
}
