#pragma once

#include <unordered_set>
#include <vector>

#include "core/types.hpp"
#include "exceptions/exceptions.hpp"
#include "utils/idMap.hpp"

// Forward declare PropagationEngine
class PropagationEngine;

class OutputToInputExplorer {
  PropagationEngine& _engine;

  std::vector<VarId> _variableStack;
  size_t _varStackIdx = 0;
  std::vector<InvariantId> _invariantStack;
  size_t _invariantStackIdx = 0;
  IdMap<VarIdBase, Timestamp> _varStableAt;  // last timestamp when a VarID was
                                             // stable (i.e., will not change)
  IdMap<InvariantId, Timestamp> _invariantStableAt;
  IdMap<InvariantId, bool> _invariantIsOnStack;

  IdMap<VarIdBase, std::unordered_set<VarIdBase>> _decisionVarAncestor;
  OutputToInputMarkingMode _outputToInputMarkingMode;

  template <OutputToInputMarkingMode MarkingMode>
  void preprocessVarStack(Timestamp);

  template <OutputToInputMarkingMode MarkingMode>
  bool isUpToDate([[maybe_unused]] VarIdBase);

  void pushVariableStack(VarId);
  void popVariableStack();
  VarId peekVariableStack();
  void pushInvariantStack(InvariantId);
  void popInvariantStack();
  InvariantId peekInvariantStack();
  void markStable(Timestamp, VarIdBase);
  bool isStable(Timestamp, VarIdBase);
  bool isStable(Timestamp, InvariantId);

  // We expand an invariant by pushing it and its first input variable onto
  // each stack.
  template <OutputToInputMarkingMode MarkingMode>
  void expandInvariant(InvariantId);
  void notifyCurrentInvariant();

  template <OutputToInputMarkingMode MarkingMode>
  bool pushNextInputVariable();
  template <OutputToInputMarkingMode MarkingMode>
  void propagate(Timestamp);

 public:
  OutputToInputExplorer() = delete;
  OutputToInputExplorer(PropagationEngine& engine, size_t expectedSize);

  void populateAncestors();
  void registerVar(VarId);
  void registerInvariant(InvariantId);
  /**
   * Register than we want to compute the value of v at timestamp ts
   */
  void registerForPropagation(Timestamp, VarId);

  void clearRegisteredVariables();

  void propagate(Timestamp);

  OutputToInputMarkingMode outputToInputMarkingMode() const;
  void setOutputToInputMarkingMode(OutputToInputMarkingMode);
};

inline void OutputToInputExplorer::registerForPropagation(Timestamp, VarId id) {
  pushVariableStack(id);
}

inline void OutputToInputExplorer::clearRegisteredVariables() {
  _varStackIdx = 0;
}

inline void OutputToInputExplorer::pushVariableStack(VarId id) {
  _variableStack[_varStackIdx++] = id;
}
inline void OutputToInputExplorer::popVariableStack() { --_varStackIdx; }
inline VarId OutputToInputExplorer::peekVariableStack() {
  return _variableStack[_varStackIdx - 1];
}

inline void OutputToInputExplorer::pushInvariantStack(InvariantId invariantId) {
  if (_invariantIsOnStack.get(invariantId)) {
    throw DynamicCycleException();
  }
  _invariantIsOnStack.set(invariantId, true);
  _invariantStack[_invariantStackIdx++] = invariantId;
}
inline void OutputToInputExplorer::popInvariantStack() {
  _invariantIsOnStack.set(_invariantStack[--_invariantStackIdx], false);
}

inline InvariantId OutputToInputExplorer::peekInvariantStack() {
  return _invariantStack[_invariantStackIdx - 1];
}

inline void OutputToInputExplorer::markStable(Timestamp ts, VarIdBase id) {
  _varStableAt[id] = ts;
}

inline bool OutputToInputExplorer::isStable(Timestamp ts, VarIdBase id) {
  return _varStableAt.at(id) == ts;
}

inline bool OutputToInputExplorer::isStable(Timestamp ts,
                                            InvariantId invariantId) {
  return _invariantStableAt.at(invariantId) == ts;
}

inline OutputToInputMarkingMode
OutputToInputExplorer::outputToInputMarkingMode() const {
  return _outputToInputMarkingMode;
}

inline void OutputToInputExplorer::setOutputToInputMarkingMode(
    OutputToInputMarkingMode markingMode) {
  _outputToInputMarkingMode = markingMode;
}
