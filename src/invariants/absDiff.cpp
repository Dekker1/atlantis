#include "invariants/absDiff.hpp"

#include <vector>

// TODO: invariant should take its true id in the constructor.
extern Id NULL_ID;

AbsDiff::AbsDiff(VarId a, VarId b, VarId c)
    : Invariant(NULL_ID), m_a(a), m_b(b), m_c(c) {}

void AbsDiff::init([[maybe_unused]] Timestamp t, Engine& e) {
  assert(m_id != NULL_ID);

  e.registerDefinedVariable(m_c, m_id);
  e.registerInvariantDependsOnVar(m_id, m_a, 0, 0);
  e.registerInvariantDependsOnVar(m_id, m_b, 1, 0);
}

void AbsDiff::recompute(Timestamp t, Engine& e) {
  e.setValue(t, m_c, std::abs(e.getValue(t, m_a) - e.getValue(t, m_b)));
}

void AbsDiff::notifyIntChanged(Timestamp t, Engine& e, LocalId, Int oldValue,
                               Int newValue, Int) {
  assert(newValue != oldValue);
  e.setValue(t, m_c, std::abs(e.getValue(t, m_a) - e.getValue(t, m_b)));
}

VarId AbsDiff::getNextDependency(Timestamp t, Engine&) {
  m_state.incValue(t, 1);
  switch (m_state.getValue(t)) {
    case 0:
      return m_a;
    case 1:
      return m_b;
    default:
      return NULL_ID;
  }
}

void AbsDiff::notifyCurrentDependencyChanged(Timestamp t, Engine& e) {
  assert(m_state.getValue(t) == 0);
  e.setValue(t, m_c, std::abs(e.getValue(t, m_a) - e.getValue(t, m_b)));
}

void AbsDiff::commit(Timestamp t, Engine& e) { Invariant::commit(t, e); }