#include "invariants/linear.hpp"

#include <vector>

Linear::Linear(std::vector<Int>&& A, std::vector<std::shared_ptr<IntVar>>&& X,
               std::shared_ptr<IntVar> b)
    : Invariant(Engine::NULL_ID), m_A(std::move(A)), m_X(std::move(X)), m_b(b) {
#ifdef VERBOSE_TRACE
#include <iostream>
  std::cout << "constructing invariant"
            << "\n";
#endif
}

// Linear::Linear(Engine& e, std::vector<Int>&& A,
//                std::vector<std::shared_ptr<IntVar>>&& X,
//                std::shared_ptr<IntVar> b)
//     : Invariant(Engine::NULL_ID), m_A(std::move(A)), m_X(std::move(X)),
//     m_b(b) {
//   init(e);
// }

void Linear::init(const Timestamp& t, Engine& e) {
#ifdef VERBOSE_TRACE
#include <iostream>
  std::cout << "initialising invariant " << m_id << "\n";
#endif
  // precondition: this invariant must be registered with the engine before it
  // is initialised.
  assert(m_id != Engine::NULL_ID);

  e.registerDefinedVariable(m_id, m_b->m_id);
  for (size_t i = 0; i < m_X.size(); i++) {
    e.registerInvariantDependency(m_id, m_X[i]->m_id, LocalId(i), m_A[i]);
  }

  this->recompute(t, e);
  this->commit(t);
}

void Linear::recompute(const Timestamp& t, Engine& e) {
  Int sum = 0;
  for (size_t i = 0; i < m_X.size(); i++) {
    sum += m_A[i] * m_X[i]->getValue(t);
  }
#ifdef VERBOSE_TRACE
#include <iostream>
  std::cout << "Invariant " << m_id << " sum was recomputed to " << sum << "\n";
#endif
  m_b->setValue(t, sum);
  e.notifyMaybeChanged(t, m_b->m_id);
}

void Linear::notifyIntChanged(const Timestamp& t, Engine& e,
                              [[maybe_unused]] LocalId id, Int oldValue,
                              Int newValue, Int coef) {
  assert(newValue != oldValue);  // precondition
  m_b->incValue(t, (newValue - oldValue) * coef);
  e.notifyMaybeChanged(t, m_b->m_id);
#ifdef VERBOSE_TRACE
#include <iostream>
  std::cout << "Invariant " << m_id << " notifying output changed by  "
            << (newValue - oldValue) * coef << "\n";
#endif
}

void Linear::commit(const Timestamp& t) {
  this->validate(t);
  m_b->commitIf(t);
}