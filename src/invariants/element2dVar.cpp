#include "invariants/element2dVar.hpp"

#include "core/engine.hpp"

static inline Int numCols(const std::vector<std::vector<VarId>>& varMatrix) {
  assert(std::all_of(varMatrix.begin(), varMatrix.end(), [&](const auto& col) {
    return col.size() == varMatrix.front().size();
  }));
  return varMatrix.empty() ? 0 : varMatrix.front().size();
}

Element2dVar::Element2dVar(Engine& engine, VarId output, VarId index1,
                           VarId index2,
                           std::vector<std::vector<VarId>> varMatrix,
                           Int offset1, Int offset2)
    : Invariant(engine),
      _varMatrix(varMatrix),
      _indices{index1, index2},
      _dimensions{static_cast<Int>(_varMatrix.size()), numCols(_varMatrix)},
      _offsets{offset1, offset2},
      _output(output) {
  _modifiedVars.reserve(1);
}

void Element2dVar::registerVars() {
  assert(_id != NULL_ID);
  _engine.registerInvariantInput(_id, _indices[0], LocalId(0));
  _engine.registerInvariantInput(_id, _indices[1], LocalId(0));
  for (const auto& varRow : _varMatrix) {
    for (const VarId input : varRow) {
      _engine.registerInvariantInput(_id, input, LocalId(0), true);
    }
  }
  registerDefinedVariable(_output);
}

void Element2dVar::updateBounds(bool widenOnly) {
  Int lb = std::numeric_limits<Int>::max();
  Int ub = std::numeric_limits<Int>::min();

  std::array<Int, 2> iLb;
  std::array<Int, 2> iUb;
  for (size_t i = 0; i < 2; ++i) {
    iLb[i] = std::max<Int>(_offsets[i], _engine.lowerBound(_indices[i]));
    iUb[i] = std::min<Int>(_dimensions[i] - 1 + _offsets[i],
                           _engine.upperBound(_indices[i]));
    if (iLb > iUb) {
      iLb[i] = _offsets[i];
      iUb[i] = _dimensions[i] - 1 + _offsets[i];
    }
  }

  for (Int i1 = iLb[0]; i1 <= iUb[0]; ++i1) {
    assert(_offsets[0] <= i1);
    assert(i1 - _offsets[0] < _dimensions[0]);
    for (Int i2 = iLb[1]; i2 <= iUb[1]; ++i2) {
      assert(_offsets[1] <= i2);
      assert(i2 - _offsets[1] < _dimensions[1]);
      lb = std::min(
          lb, _engine.lowerBound(_varMatrix[safeIndex1(i1)][safeIndex2(i2)]));
      ub = std::max(
          ub, _engine.upperBound(_varMatrix[safeIndex1(i1)][safeIndex2(i2)]));
    }
  }
  _engine.updateBounds(_output, lb, ub, widenOnly);
}

void Element2dVar::recompute(Timestamp ts) {
  assert(safeIndex1(_engine.value(ts, _indices[0])) <
         static_cast<size_t>(_dimensions[0]));
  assert(safeIndex2(_engine.value(ts, _indices[1])) <
         static_cast<size_t>(_dimensions[1]));
  updateValue(ts, _output,
              _engine.value(
                  ts, _varMatrix[safeIndex1(_engine.value(ts, _indices[0]))]
                                [safeIndex2(_engine.value(ts, _indices[1]))]));
}

void Element2dVar::notifyInputChanged(Timestamp ts, LocalId) { recompute(ts); }

VarId Element2dVar::nextInput(Timestamp ts) {
  switch (_state.incValue(ts, 1)) {
    case 0:
      return _indices[0];
    case 1:
      return _indices[1];
    case 2: {
      assert(safeIndex1(_engine.value(ts, _indices[0])) <
             static_cast<size_t>(_dimensions[0]));
      assert(safeIndex2(_engine.value(ts, _indices[1])) <
             static_cast<size_t>(_dimensions[1]));
      return _varMatrix[safeIndex1(_engine.value(ts, _indices[0]))]
                       [safeIndex2(_engine.value(ts, _indices[1]))];
    }
    default:
      return NULL_ID;  // Done
  }
}

void Element2dVar::notifyCurrentInputChanged(Timestamp ts) { recompute(ts); }

void Element2dVar::commit(Timestamp ts) { Invariant::commit(ts); }