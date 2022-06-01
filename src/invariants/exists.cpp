#include "invariants/exists.hpp"

Exists::Exists(std::vector<VarId> varArray, VarId y)
    : Invariant(NULL_ID),
      _varArray(std::move(varArray)),
      _y(y),
      _localPriority(_varArray.size()) {
  _modifiedVars.reserve(_varArray.size());
}

void Exists::registerVars(Engine& engine) {
  assert(!_id.equals(NULL_ID));
  for (size_t i = 0; i < _varArray.size(); ++i) {
    engine.registerInvariantInput(_id, _varArray[i], i);
  }
  registerDefinedVariable(engine, _y);
}

void Exists::updateBounds(Engine& engine, bool widenOnly) {
  Int lb = std::numeric_limits<Int>::max();
  Int ub = std::numeric_limits<Int>::max();
  for (const VarId input : _varArray) {
    lb = std::min(lb, engine.lowerBound(input));
    ub = std::min(ub, engine.upperBound(input));
  }
  engine.updateBounds(_y, std::max(Int(0), lb), ub, widenOnly);
}

void Exists::recompute(Timestamp ts, Engine& engine) {
  for (size_t i = 0; i < _varArray.size(); ++i) {
    _localPriority.updatePriority(
        ts, i, std::max(Int(0), engine.value(ts, _varArray[i])));
  }
  assert(_localPriority.minPriority(ts) >= 0);
  updateValue(ts, engine, _y, _localPriority.minPriority(ts));
}

void Exists::notifyInputChanged(Timestamp ts, Engine& engine, LocalId id) {
  _localPriority.updatePriority(
      ts, id, std::max(Int(0), engine.value(ts, _varArray[id])));
  assert(_localPriority.minPriority(ts) >= 0);
  updateValue(ts, engine, _y, _localPriority.minPriority(ts));
}

VarId Exists::nextInput(Timestamp ts, Engine&) {
  const auto index = static_cast<size_t>(_state.incValue(ts, 1));
  assert(0 <= _state.value(ts));
  if (index < _varArray.size()) {
    return _varArray[index];
  } else {
    return NULL_ID;  // Done
  }
}

void Exists::notifyCurrentInputChanged(Timestamp ts, Engine& engine) {
  notifyInputChanged(ts, engine, _state.value(ts));
}

void Exists::commit(Timestamp ts, Engine& engine) {
  Invariant::commit(ts, engine);
  _localPriority.commitIf(ts);
}