#include "invariantgraph/constraints/countGtNode.hpp"

#include "../parseHelper.hpp"

std::unique_ptr<invariantgraph::CountGtNode>
invariantgraph::CountGtNode::fromModelConstraint(
    const fznparser::FZNModel& model, const fznparser::Constraint& constraint,
    const std::function<VariableNode*(MappableValue&)>& variableMap) {
  assert(hasCorrectSignature(acceptedNameNumArgPairs(), constraint));

  auto x = mappedVariableVector(model, constraint.arguments[0], variableMap);

  bool yIsParameter = std::holds_alternative<Int>(constraint.arguments[1]);
  VariableNode* yVarNode =
      yIsParameter ? nullptr
                   : mappedVariable(constraint.arguments[1], variableMap);
  const Int yParameter =
      yIsParameter ? std::get<Int>(constraint.arguments[1]) : -1;

  bool cIsParameter = std::holds_alternative<Int>(constraint.arguments[2]);
  VariableNode* cVarNode =
      cIsParameter ? nullptr
                   : mappedVariable(constraint.arguments[2], variableMap);
  const Int cParameter =
      cIsParameter ? std::get<Int>(constraint.arguments[2]) : -1;

  bool shouldHold = true;
  VariableNode* r = nullptr;

  if (constraint.arguments.size() >= 4) {
    if (std::holds_alternative<bool>(constraint.arguments[3])) {
      shouldHold = std::get<bool>(constraint.arguments[3]);
    } else {
      r = mappedVariable(constraint.arguments[3], variableMap);
    }
  }

  if (yIsParameter) {
    if (cIsParameter) {
      if (r != nullptr) {
        return std::make_unique<CountGtNode>(x, yParameter, cParameter, r);
      }
      return std::make_unique<CountGtNode>(x, yParameter, cParameter,
                                           shouldHold);
    }
    if (r != nullptr) {
      return std::make_unique<CountGtNode>(x, yParameter, cVarNode, r);
    }
    return std::make_unique<CountGtNode>(x, yParameter, cVarNode, shouldHold);
  }
  if (cIsParameter) {
    if (r != nullptr) {
      return std::make_unique<CountGtNode>(x, yVarNode, cParameter, r);
    }
    return std::make_unique<CountGtNode>(x, yVarNode, cParameter, shouldHold);
  }
  if (r != nullptr) {
    return std::make_unique<CountGtNode>(x, yVarNode, cVarNode, r);
  }
  return std::make_unique<CountGtNode>(x, yVarNode, cVarNode, shouldHold);
}

void invariantgraph::CountGtNode::createDefinedVariables(Engine& engine) {
  if (violationVarId() == NULL_ID) {
    _intermediate = engine.makeIntVar(0, 0, 0);
    if (!_cIsParameter) {
      registerViolation(engine);
    } else {
      if (shouldHold()) {
        setViolationVarId(engine.makeIntView<GreaterEqualConst>(
            _intermediate, _cParameter + 1));
      } else {
        assert(!isReified());
        setViolationVarId(
            engine.makeIntView<LessEqualConst>(_intermediate, _cParameter));
      }
    }
  }
}

void invariantgraph::CountGtNode::registerWithEngine(Engine& engine) {
  std::vector<VarId> engineInputs;
  assert(staticInputs().size() >= static_cast<size_t>(!_yIsParameter) +
                                      static_cast<size_t>(!_cIsParameter));
  const size_t vectorSize = staticInputs().size() -
                            static_cast<size_t>(!_yIsParameter) -
                            static_cast<size_t>(!_cIsParameter);

  engineInputs.resize(vectorSize);

  for (size_t i = 0; i < vectorSize; ++i) {
    engineInputs.at(i) = staticInputs().at(i)->varId();
  }

  assert(violationVarId() != NULL_ID);
  assert(_intermediate != NULL_ID);

  if (!_yIsParameter) {
    assert(yVarNode() != nullptr);
    assert(yVarNode()->varId() != NULL_ID);
    engine.makeInvariant<Count>(_intermediate, yVarNode()->varId(),
                                engineInputs);
  } else {
    assert(yVarNode() == nullptr);
    engine.makeInvariant<CountConst>(_intermediate, _yParameter, engineInputs);
  }
  if (!_cIsParameter) {
    assert(cVarNode() != nullptr);
    assert(cVarNode()->varId() != NULL_ID);
    if (shouldHold()) {
      // c > count(x, y) -> count(x, y) < c
      engine.makeInvariant<LessThan>(violationVarId(), _intermediate,
                                     cVarNode()->varId());
    } else {
      engine.makeInvariant<LessEqual>(violationVarId(), cVarNode()->varId(),
                                      _intermediate);
    }
  }
}
