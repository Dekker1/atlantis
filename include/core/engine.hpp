#pragma once

#include <assert.h>

#include <memory>
#include <vector>

#include "core/constraint.hpp"
#include "core/intVar.hpp"
#include "core/invariant.hpp"
#include "core/tracer.hpp"
#include "core/types.hpp"
#include "exceptions/exceptions.hpp"
#include "store/store.hpp"

class Engine {
 protected:
  static const size_t ESTIMATED_NUM_OBJECTS = 1;

  Timestamp m_currentTime;

  bool m_isOpen = true;

  struct InvariantDependencyData {
    InvariantId id;
    LocalId localId;
    Timestamp lastNotification;  // todo: unclear if this information is
                                 // relevant for all types of propagation. If
                                 // not then move it to a subclass...
  };
  // Map from VarID -> vector of InvariantID
  std::vector<std::vector<InvariantDependencyData>> m_dependentInvariantData;

  Store m_store;

 public:
  Engine(/* args */);

  virtual ~Engine() = default;

  virtual void open() = 0;
  virtual void close() = 0;

  //--------------------- Variable ---------------------
  void incValue(Timestamp, VarId, Int inc);
  inline void incValue(VarId v, Int val) { incValue(m_currentTime, v, val); }

  void updateValue(Timestamp, VarId, Int val);
  inline void updateValue(VarId v, Int val) {
    updateValue(m_currentTime, v, val);
  }

  virtual void notifyMaybeChanged(Timestamp t, VarId id) = 0;

  Int getValue(Timestamp, VarId);
  inline Int getNewValue(VarId v) { return getValue(m_currentTime, v); }

  Int getCommittedValue(VarId);

  Timestamp getTmpTimestamp(VarId);

  inline bool hasChanged(Timestamp t, VarId v) const {
    return m_store.getConstIntVar(v).hasChanged(t);
  }

  bool isPostponed(InvariantId);

  void postpone(InvariantId);
  void recompute(InvariantId);
  void recompute(Timestamp, InvariantId);

  void commit(VarId);  // todo: this feels dangerous, maybe commit should
                       // always have a timestamp?
  void commitIf(Timestamp, VarId);
  void commitValue(VarId, Int val);

  inline Int getLowerBound(VarId v) const {
    return m_store.getConstIntVar(v).getLowerBound();
  }

  inline Int getUpperBound(VarId v) const {
    return m_store.getConstIntVar(v).getUpperBound();
  }

  void commitInvariantIf(Timestamp, InvariantId);

  //--------------------- Registration ---------------------
  /**
   * Register an invariant in the engine and return its pointer.
   * This also sets the id of the invariant to the new id.
   * @param args the constructor arguments of the invariant
   * @return the created invariant.
   */
  template <class T, typename... Args>
  std::enable_if_t<std::is_base_of<Invariant, T>::value, std::shared_ptr<T>>
  makeInvariant(Args&&... args);

  /**
   * Register a constraint in the engine and return its pointer.
   * This also sets the id of the constraint to the new id.
   * @param args the constructor arguments of the constraint
   * @return the created constraint.
   */
  template <class T, typename... Args>
  std::enable_if_t<std::is_base_of<Constraint, T>::value, std::shared_ptr<T>>
  makeConstraint(Args&&... args);

  /**
   * Creates an IntVar and registers it to the engine.
   * @return the created IntVar
   */
  VarId makeIntVar(Int initValue, Int lowerBound, Int upperBound);

  /**
   * Register that Invariant to depends on variable from depends on dependency
   * @param dependent the invariant that the variable depends on
   * @param source the depending variable
   * @param localId the id of the depending variable in the invariant
   * @param data additional data
   */
  virtual void registerInvariantDependsOnVar(InvariantId dependent,
                                             VarId source, LocalId localId) = 0;

  /**
   * Register that 'from' defines variable 'to'. Throws exception if
   * already defined.
   * @param dependent the variable that is defined by the invariant
   * @param source the invariant defining the variable
   * @throw if the variable is already defined by an invariant.
   */
  virtual void registerDefinedVariable(VarId dependent, InvariantId source) = 0;

  virtual void registerVar(VarId) = 0;
  virtual void registerInvariant(InvariantId) = 0;

  const Store& getStore();
  Timestamp getCurrentTime();
};

template <class T, typename... Args>
std::enable_if_t<std::is_base_of<Invariant, T>::value, std::shared_ptr<T>>
Engine::makeInvariant(Args&&... args) {
  if (!m_isOpen) {
    throw ModelNotOpenException("Cannot make invariant when store is closed.");
  }
  auto invariantPtr = std::make_shared<T>(std::forward<Args>(args)...);

  auto newId = m_store.createInvariantFromPtr(invariantPtr);
  registerInvariant(newId);
  //  std::cout << "Created new invariant with id: " << newId << "\n";
  invariantPtr->init(m_currentTime, *this);
  return invariantPtr;
}

template <class T, typename... Args>
std::enable_if_t<std::is_base_of<Constraint, T>::value, std::shared_ptr<T>>
Engine::makeConstraint(Args&&... args) {
  if (!m_isOpen) {
    throw ModelNotOpenException("Cannot make invariant when store is closed.");
  }
  auto constraintPtr = std::make_shared<T>(std::forward<Args>(args)...);

  auto newId = m_store.createInvariantFromPtr(constraintPtr);
  registerInvariant(newId);
  //  std::cout << "Created new Constraint with id: " << newId << "\n";
  constraintPtr->init(m_currentTime, *this);
  return constraintPtr;
}

//--------------------- Inlined functions ---------------------

inline const Store& Engine::getStore() { return m_store; }
inline Timestamp Engine::getCurrentTime() { return m_currentTime; }

inline Int Engine::getValue(Timestamp t, VarId v) {
  return m_store.getIntVar(v).getValue(t);
}

inline Int Engine::getCommittedValue(VarId v) {
  return m_store.getIntVar(v).getCommittedValue();
}

inline Timestamp Engine::getTmpTimestamp(VarId v) {
  return m_store.getIntVar(v).getTmpTimestamp();
}

inline bool Engine::isPostponed(InvariantId id) {
  return m_store.getInvariant(id).isPostponed();
}

inline void Engine::postpone(InvariantId id) {
  return m_store.getInvariant(id).postpone();
}

inline void Engine::recompute(InvariantId id) {
  return m_store.getInvariant(id).recompute(m_currentTime, *this);
}

inline void Engine::recompute(Timestamp t, InvariantId id) {
  return m_store.getInvariant(id).recompute(t, *this);
}

inline void Engine::updateValue(Timestamp t, VarId v, Int val) {
  m_store.getIntVar(v).setValue(t, val);
  this->notifyMaybeChanged(t, v);
}

inline void Engine::incValue(Timestamp t, VarId v, Int inc) {
  m_store.getIntVar(v).incValue(t, inc);
  this->notifyMaybeChanged(t, v);
}

inline void Engine::commit(VarId v) { m_store.getIntVar(v).commit(); }

inline void Engine::commitIf(Timestamp t, VarId v) {
  m_store.getIntVar(v).commitIf(t);
}

inline void Engine::commitValue(VarId v, Int val) {
  m_store.getIntVar(v).commitValue(val);
}

inline void Engine::commitInvariantIf(Timestamp t, InvariantId id) {
  m_store.getInvariant(id).commit(t, *this);
}
