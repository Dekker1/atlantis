#include "atlantis/propagation/violationInvariants/notEqual.hpp"

#include <array>

namespace atlantis::propagation {

/**
 * Constraint x != y
 * @param violationId id for the violationCount
 * @param x variable of lhs
 * @param y variable of rhs
 */
NotEqual::NotEqual(SolverBase& solver, VarId violationId, VarViewId x,
                   VarViewId y)
    : ViolationInvariant(solver, violationId), _x(x), _y(y) {}

NotEqual::NotEqual(SolverBase& solver, VarViewId violationId, VarViewId x,
                   VarViewId y)
    : NotEqual(solver, VarId(violationId), x, y) {
  assert(violationId.isVar());
}

void NotEqual::registerVars() {
  assert(_id != NULL_ID);
  _solver.registerInvariantInput(_id, _x, LocalId(0), false);
  _solver.registerInvariantInput(_id, _y, LocalId(0), false);
  registerDefinedVar(_violationId);
}

void NotEqual::updateBounds(bool widenOnly) {
  const Int xLb = _solver.lowerBound(_x);
  const Int xUb = _solver.upperBound(_x);
  const Int yLb = _solver.lowerBound(_y);
  const Int yUb = _solver.upperBound(_y);
  if (xUb < yLb || yUb < xLb) {
    _solver.updateBounds(_violationId, 0, 0, widenOnly);
    return;
  }

  for (const Int val : std::array<Int, 3>{xUb, yLb, yUb}) {
    if (xLb != val) {
      _solver.updateBounds(_violationId, 0, 1, widenOnly);
      return;
    }
  }
  _solver.updateBounds(_violationId, 1, 1, widenOnly);
}

void NotEqual::recompute(Timestamp ts) {
  updateValue(ts, _violationId, _solver.value(ts, _x) == _solver.value(ts, _y));
}

void NotEqual::notifyInputChanged(Timestamp ts, LocalId) { recompute(ts); }

VarViewId NotEqual::nextInput(Timestamp ts) {
  switch (_state.incValue(ts, 1)) {
    case 0:
      return _x;
    case 1:
      return _y;
    default:
      return NULL_ID;
  }
}

void NotEqual::notifyCurrentInputChanged(Timestamp ts) { recompute(ts); }
}  // namespace atlantis::propagation
