#include "invariants/ifThenElse.hpp"

IfThenElse::IfThenElse(VarId b, VarId x, VarId y, VarId z)
    : Invariant(NULL_ID), _b(b), _xy({x, y}), _z(z) {
  _modifiedVars.reserve(1);
}

void IfThenElse::init([[maybe_unused]] Timestamp ts, Engine& engine) {
  assert(!_id.equals(NULL_ID));

  registerDefinedVariable(engine, _z);
  engine.registerInvariantDependsOnVar(_id, _b, 0);
  engine.registerInvariantDependsOnVar(_id, _xy[0], 0);
  engine.registerInvariantDependsOnVar(_id, _xy[1], 0);
}

void IfThenElse::recompute(Timestamp ts, Engine& engine) {
  auto b = engine.getValue(ts, _b);
  updateValue(ts, engine, _z, engine.getValue(ts, _xy[1 - (b == 0)]));
}

void IfThenElse::notifyIntChanged(Timestamp ts, Engine& engine, LocalId) {
  recompute(ts, engine);
}

VarId IfThenElse::getNextDependency(Timestamp ts, Engine& engine) {
  _state.incValue(ts, 1);
  auto state = _state.getValue(ts);
  if (state == 0) {
    return _b;
  } else if (state == 1) {
    auto b = engine.getValue(ts, _b);
    return _xy[1 - (b == 0)];
  } else {
    return NULL_ID;  // Done
  }
}

void IfThenElse::notifyCurrentDependencyChanged(Timestamp ts, Engine& engine) {
  recompute(ts, engine);
}

void IfThenElse::commit(Timestamp ts, Engine& engine) {
  Invariant::commit(ts, engine);
}