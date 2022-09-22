#include "constraints/globalCardinalityClosed.hpp"

#include "core/engine.hpp"
#include "variables/committableInt.hpp"

inline bool all_in_range(Int start, Int stop,
                         std::function<bool(Int)> predicate) {
  std::vector<Int> vec(stop - start);
  for (Int i = 0; i < stop - start; ++i) {
    vec.at(i) = start + i;
  }
  return std::all_of(vec.begin(), vec.end(), predicate);
}

/**
 * @param violationId id for the violationCount
 */
GlobalCardinalityClosed::GlobalCardinalityClosed(VarId violationId,
                                                 std::vector<VarId> outputs,
                                                 std::vector<VarId> inputs,
                                                 std::vector<Int> cover)
    : Constraint(violationId),
      _outputs(std::move(outputs)),
      _inputs(std::move(inputs)),
      _cover(std::move(cover)),
      _coverVarIndex(),
      _localValues(),
      _counts(),
      _offset(0) {
  _modifiedVars.reserve(_inputs.size());
  assert(_cover.size() == _outputs.size());
  assert(all_in_range(0, _cover.size(), [&](const size_t i) {
    return all_in_range(i + 1, _cover.size(), [&](const size_t j) {
      return _cover.at(i) != _cover.at(j) && _outputs.at(i) != _outputs.at(j);
    });
  }));
}

void GlobalCardinalityClosed::registerVars(Engine& engine) {
  assert(!_id.equals(NULL_ID));
  for (size_t i = 0; i < _inputs.size(); ++i) {
    engine.registerInvariantInput(_id, _inputs[i], LocalId(i));
  }
  registerDefinedVariable(engine, _violationId);
  for (const VarId output : _outputs) {
    registerDefinedVariable(engine, output);
  }
}

void GlobalCardinalityClosed::updateBounds(Engine& engine, bool widenOnly) {
  engine.updateBounds(_violationId, 0, _inputs.size(), widenOnly);
  for (const VarId output : _outputs) {
    engine.updateBounds(output, 0, _inputs.size(), widenOnly);
  }
}

void GlobalCardinalityClosed::close(Timestamp timestamp, Engine& engine) {
  const auto [lb, ub] = std::minmax_element(_cover.begin(), _cover.end());
  _offset = *lb;
  _coverVarIndex.resize(*ub - *lb + 1, -1);
  for (size_t i = 0; i < _cover.size(); ++i) {
    assert(0 <= _cover[i] - _offset);
    assert(_cover[i] - _offset < static_cast<Int>(_coverVarIndex.size()));
    _coverVarIndex[_cover[i] - _offset] = i;
  }
  _counts.resize(_outputs.size(), CommittableInt(timestamp, 0));
  _localValues.clear();
  for (const VarId input : _inputs) {
    _localValues.emplace_back(timestamp, engine.committedValue(input));
  }
}

void GlobalCardinalityClosed::recompute(Timestamp timestamp, Engine& engine) {
  for (CommittableInt& c : _counts) {
    c.setValue(timestamp, 0);
  }

  Int excess = 0;
  for (size_t i = 0; i < _inputs.size(); ++i) {
    excess += increaseCount(timestamp, engine.value(timestamp, _inputs[i]));
    _localValues[i].setValue(timestamp, engine.value(timestamp, _inputs[i]));
  }

  updateValue(timestamp, engine, _violationId, excess);
  for (size_t i = 0; i < _outputs.size(); ++i) {
    assert(0 <= _cover[i] - _offset &&
           _cover[i] - _offset < static_cast<Int>(_coverVarIndex.size()));
    updateValue(timestamp, engine, _outputs[i], _counts[i].value(timestamp));
  }
}

void GlobalCardinalityClosed::notifyInputChanged(Timestamp timestamp,
                                                 Engine& engine,
                                                 LocalId localId) {
  assert(localId < _localValues.size());
  const Int oldValue = _localValues[localId].value(timestamp);
  const Int newValue = engine.value(timestamp, _inputs[localId]);
  if (newValue == oldValue) {
    return;
  }
  const Int dec = decreaseCount(timestamp, oldValue);
  const Int inc = increaseCount(timestamp, newValue);
  _localValues[localId].setValue(timestamp, newValue);
  incValue(timestamp, engine, _violationId, inc - dec);
  updateOutput(timestamp, engine, oldValue);
  updateOutput(timestamp, engine, newValue);
}

VarId GlobalCardinalityClosed::nextInput(Timestamp timestamp, Engine&) {
  const auto index = static_cast<size_t>(_state.incValue(timestamp, 1));
  assert(0 <= _state.value(timestamp));
  if (index < _inputs.size()) {
    return _inputs[index];
  }
  return NULL_ID;
}

void GlobalCardinalityClosed::notifyCurrentInputChanged(Timestamp timestamp,
                                                        Engine& engine) {
  assert(static_cast<size_t>(_state.value(timestamp)) < _inputs.size());
  notifyInputChanged(timestamp, engine, _state.value(timestamp));
}

void GlobalCardinalityClosed::commit(Timestamp timestamp, Engine& engine) {
  Invariant::commit(timestamp, engine);

  for (auto& localValue : _localValues) {
    localValue.commitIf(timestamp);
  }

  for (CommittableInt& CommittableInt : _counts) {
    CommittableInt.commitIf(timestamp);
  }
}
