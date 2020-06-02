#pragma once

#include "core/engine.hpp"
#include "core/savedInt.hpp"
#include "core/types.hpp"
#include "core/var.hpp"

class IntVar : public Var {
 private:
  SavedInt m_value;

 public:
  IntVar() : IntVar(Engine::NULL_ID){};
  IntVar(Id t_id) : Var(id), m_value(0, 0), m_modified(false){};
  ~IntVar();

  [[gnu::always_inline]] inline Int getNewValue(const Timestamp& t) {
    return m_value.getValue(t);
  }
  [[gnu::always_inline]] inline Int getOldValue() {
    return m_value.getCommittedValue();
  }
  [[gnu::always_inline]] inline void setNewValue(const Timestamp& timestamp,
                                                 Int value) {
    m_value.setValue(timestamp, value);
  }
  [[gnu::always_inline]] inline void incValue(const Timestamp& timestamp,
                                              Int inc) {
    m_value.incValue(timestamp, inc);
  }
  [[gnu::always_inline]] inline void commit() { m_value.commit(); }
  [[gnu::always_inline]] inline void commitValue(Int value) {
    m_value.commitValue(value);
  }
  [[gnu::always_inline]] inline void commitIf(const Timestamp& timestamp) {
    m_value.commitIf(timestamp);
  }
};