#include "invariants/intDiv.hpp"

#include "core/engine.hpp"

void IntDiv::init([[maybe_unused]] Timestamp ts, Engine& engine) {
  assert(!_id.equals(NULL_ID));

  registerDefinedVariable(engine, _y);
  engine.registerInvariantInput(_id, _a, 0);
  engine.registerInvariantInput(_id, _b, 0);
}

void IntDiv::recompute(Timestamp ts, Engine& engine) {
  // TODO: How to handle division by 0?
  updateValue(ts, engine, _y,
              engine.value(ts, _a) / engine.value(ts, _b));
}

VarId IntDiv::nextInput(Timestamp ts, Engine&) {
  _state.incValue(ts, 1);
  switch (_state.value(ts)) {
    case 0:
      return _a;
    case 1:
      return _b;
    default:
      return NULL_ID;
  }
}

void IntDiv::notifyCurrentInputChanged(Timestamp ts, Engine& engine) {
  recompute(ts, engine);
}

void IntDiv::notifyInputChanged(Timestamp ts, Engine& engine, LocalId) {
  recompute(ts, engine);
}

void IntDiv::commit(Timestamp ts, Engine& engine) {
  Invariant::commit(ts, engine);
}