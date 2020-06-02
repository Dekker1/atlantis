#pragma once
#include "core/invariant.hpp"
#include "core/types.hpp"

class Engine {
 private:
 public:
  static const Id NULL_ID = 0;
  Engine(/* args */);
  ~Engine();

  //---------------------Notificaion
  void notifyMaybeChanged(Int id);

  //---------------------Registration
  /**
   * Register an invariant in the engine and return its new id.
   * TODO: this should also set the id of the invariant to the new id.
   */
  Id registerInvariant(Invariant& i);

  /**
   * Register that target depends on dependency
   */
  void registerDependency(Id target, Id dependency, Id localId, Int data);

  /**
   * Register that source defines variable definedVar. Throws exception if
   * already defined.
   */
  void registerDefinedVariable(Id source, Id definedVar);
};