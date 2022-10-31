#include "invariants/boolXor.hpp"

#include "core/engine.hpp"

/**
 * invariant output = ((x == 0) != (y == 0))
 * output does not violate if exactly one of x or y violates.
 * @param violationId id for the violationCount
 * @param x first violation variable
 * @param y second violation variable
 * @param output result
 */
BoolXor::BoolXor(Engine& engine, VarId output, VarId x, VarId y)
    : Invariant(engine), _output(output), _x(x), _y(y) {
  _modifiedVars.reserve(1);
}

void BoolXor::registerVars() {
  assert(_id != NULL_ID);
  _engine.registerInvariantInput(_id, _x, LocalId(0));
  _engine.registerInvariantInput(_id, _y, LocalId(0));
  registerDefinedVariable(_output);
}

void BoolXor::updateBounds(bool widenOnly) {
  _engine.updateBounds(_output, 0, 1, widenOnly);
}

void BoolXor::recompute(Timestamp ts) {
  updateValue(ts, _output,
              static_cast<Int>((_engine.value(ts, _x) != 0) ==
                               (_engine.value(ts, _y) != 0)));
}

void BoolXor::notifyInputChanged(Timestamp ts, LocalId) { recompute(ts); }

VarId BoolXor::nextInput(Timestamp ts) {
  switch (_state.incValue(ts, 1)) {
    case 0:
      return _x;
    case 1:
      return _y;
    default:
      return NULL_ID;
  }
}

void BoolXor::notifyCurrentInputChanged(Timestamp ts) { recompute(ts); }

void BoolXor::commit(Timestamp ts) { Invariant::commit(ts); }
