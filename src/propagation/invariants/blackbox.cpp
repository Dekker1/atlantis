#include "atlantis/propagation/invariants/blackbox.hpp"

#include <cassert>

#include "atlantis/propagation/variables/committableInt.hpp"

namespace atlantis::propagation {

inline std::vector<VarId> toVarIds(std::vector<VarViewId>&& ids) {
  std::vector<VarId> varIds;
  varIds.reserve(ids.size());
  for (const auto& id : ids) {
    assert(id.isVar());
    varIds.emplace_back(VarId(id));
  }
  return varIds;
}

Blackbox::Blackbox(SolverBase& solver,
                   std::unique_ptr<blackbox::BlackBoxFn>&& blackBoxFn,
                   std::vector<VarViewId>&& outputs, std::vector<VarViewId>&& inputs)
    : Invariant(solver),
      _blackBoxFn(std::move(blackBoxFn)),
      _outputs(toVarIds(std::move(outputs))),
      _inputs(toVarIds(std::move(inputs))) {}

void Blackbox::registerVars() {
  assert(_id != NULL_ID);
  for (size_t i = 0; i < _inputs.size(); ++i) {
    _solver.registerInvariantInput(_id, _inputs[i], LocalId(i), false);
  }
  for (const VarId& output : _outputs) {
    registerDefinedVar(output);
  }
}

void Blackbox::recompute(Timestamp timestamp) {
  // Initialize input
  std::vector<int> int_in(_inputs.size());
  for (size_t i = 0; i < _inputs.size(); ++i) {
    int_in[i] = _solver.value(timestamp, _inputs[i]);
  }
  std::vector<double> float_in;

  // Initialize output
  std::vector<int> int_out(_outputs.size(), 0);
  std::vector<double> float_out(0, 0.0);

  _blackBoxFn->run(int_in, float_in, int_out, float_out);

  for (size_t i = 0; i < _outputs.size(); ++i) {
    updateValue(timestamp, _outputs[i], int_out[i]);
  }
}

void Blackbox::notifyInputChanged(Timestamp timestamp, LocalId localId) {
  assert(localId < _inputs.size());
  const Int newValue = _solver.value(timestamp, _inputs[localId]);
  const Int committedValue = _solver.committedValue(_inputs[localId]);
  if (newValue == committedValue) {
    return;
  }
  recompute(timestamp);
}

VarViewId Blackbox::nextInput(Timestamp timestamp) {
  const auto index = static_cast<size_t>(_state.incValue(timestamp, 1));
  assert(0 <= _state.value(timestamp));
  if (index < _inputs.size()) {
    return _inputs[index];
  }
  return NULL_ID;
}

void Blackbox::notifyCurrentInputChanged(Timestamp timestamp) {
  assert(static_cast<size_t>(_state.value(timestamp)) < _inputs.size());
  notifyInputChanged(timestamp, _state.value(timestamp));
}

}  // namespace atlantis::propagation
