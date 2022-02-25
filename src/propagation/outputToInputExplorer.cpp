
#include "propagation/outputToInputExplorer.hpp"

#include "core/propagationEngine.hpp"

OutputToInputExplorer::OutputToInputExplorer(PropagationEngine& e,
                                             size_t expectedSize)
    : _engine(e),
      _varStackIdx(0),
      _invariantStackIdx(0),
      _varComputedAt(expectedSize),
      _invariantComputedAt(expectedSize),
      _invariantIsOnStack(expectedSize),
      _decisionVarAncestor(expectedSize),
      _outputToInputMarkingMode(OutputToInputMarkingMode::NONE) {
  _variableStack.reserve(expectedSize);
  _invariantStack.reserve(expectedSize);
}

void OutputToInputExplorer::populateAncestors() {
  std::vector<bool> varVisited(_engine.getNumVariables() + 1);
  std::deque<IdBase> stack(_engine.getNumVariables() + 1);

  for (IdBase idx = 1; idx <= _engine.getNumVariables(); ++idx) {
    if (_decisionVarAncestor.size() < idx) {
      _decisionVarAncestor.register_idx(idx);
    }

    _decisionVarAncestor[idx].clear();
  }

  for (const VarIdBase decisionVar : _engine.getDecisionVariables()) {
    std::fill(varVisited.begin(), varVisited.end(), false);
    stack.clear();
    stack.push_back(decisionVar);
    varVisited[decisionVar] = true;

    while (stack.size() > 0) {
      const VarIdBase id = stack.back();
      stack.pop_back();
      _decisionVarAncestor[id].emplace(decisionVar);

      for (InvariantId invariantId :
           _engine.getListeningInvariants(IdBase(id))) {
        for (VarIdBase outputVar : _engine.getVariablesDefinedBy(invariantId)) {
          if (!varVisited[outputVar]) {
            varVisited[outputVar] = true;
            stack.push_back(outputVar);
          }
        }
      }
    }
  }
}

void OutputToInputExplorer::propagate(Timestamp ts) {
  if (_outputToInputMarkingMode == OutputToInputMarkingMode::NONE) {
    propagate<OutputToInputMarkingMode::NONE>(ts);
  } else if (_outputToInputMarkingMode ==
             OutputToInputMarkingMode::TOPOLOGICAL_SORT) {
    propagate<OutputToInputMarkingMode::TOPOLOGICAL_SORT>(ts);
  } else if (_outputToInputMarkingMode ==
             OutputToInputMarkingMode::MARK_SWEEP) {
    propagate<OutputToInputMarkingMode::MARK_SWEEP>(ts);
  }
}

template bool OutputToInputExplorer::isMarked<OutputToInputMarkingMode::NONE>(
    VarIdBase id);
template bool OutputToInputExplorer::isMarked<
    OutputToInputMarkingMode::MARK_SWEEP>(VarIdBase id);
template bool OutputToInputExplorer::isMarked<
    OutputToInputMarkingMode::TOPOLOGICAL_SORT>(VarIdBase id);
template <OutputToInputMarkingMode MarkingMode>
bool OutputToInputExplorer::isMarked(VarIdBase id) {
  if constexpr (MarkingMode == OutputToInputMarkingMode::MARK_SWEEP) {
    for (const size_t ancestor : _engine.getModifiedDecisionVariables()) {
      if (_decisionVarAncestor.at(id).find(ancestor) !=
          _decisionVarAncestor.at(id).end()) {
        return true;
      }
    }
    return false;
  } else if constexpr (MarkingMode ==
                       OutputToInputMarkingMode::TOPOLOGICAL_SORT) {
    return _engine.isOnPropagationPath(id);
  } else {
    // We should check this with constant expressions
    assert(false);

    // We have no marking: no variable is up-to-date, all variables are all
    // potentially out-of-date and must be recomputed.
    return true;
  }
}

template void OutputToInputExplorer::preprocessVarStack<
    OutputToInputMarkingMode::NONE>(Timestamp currentTimestamp);
template void OutputToInputExplorer::preprocessVarStack<
    OutputToInputMarkingMode::MARK_SWEEP>(Timestamp currentTimestamp);
template void OutputToInputExplorer::preprocessVarStack<
    OutputToInputMarkingMode::TOPOLOGICAL_SORT>(Timestamp currentTimestamp);
template <OutputToInputMarkingMode MarkingMode>
void OutputToInputExplorer::preprocessVarStack(Timestamp currentTimestamp) {
  size_t newStackSize = 0;
  for (size_t s = 0; s < _varStackIdx; ++s) {
    if constexpr (MarkingMode == OutputToInputMarkingMode::NONE) {
      _variableStack[newStackSize] = _variableStack[s];
      ++newStackSize;
    } else {
      if (isMarked<MarkingMode>(_variableStack[s])) {
        _variableStack[newStackSize] = _variableStack[s];
        ++newStackSize;
      } else {
        setComputed(currentTimestamp, _variableStack[s]);
      }
    }
  }
  _varStackIdx = newStackSize;
}

template void OutputToInputExplorer::expandInvariant<
    OutputToInputMarkingMode::NONE>(InvariantId);
template void OutputToInputExplorer::expandInvariant<
    OutputToInputMarkingMode::MARK_SWEEP>(InvariantId);
template void OutputToInputExplorer::expandInvariant<
    OutputToInputMarkingMode::TOPOLOGICAL_SORT>(InvariantId);
// We expand an invariant by pushing it and its first input variable onto each
// stack.
template <OutputToInputMarkingMode MarkingMode>
void OutputToInputExplorer::expandInvariant(InvariantId invariantId) {
  if (invariantId == NULL_ID) {
    return;
  }
  if (_invariantIsOnStack.get(invariantId)) {
    throw DynamicCycleException();
  }
  VarId nextVar = _engine.getNextInput(invariantId);
  if constexpr (MarkingMode != OutputToInputMarkingMode::NONE) {
    while (nextVar != NULL_ID && !isMarked<MarkingMode>(nextVar)) {
      nextVar = _engine.getNextInput(invariantId);
    }
  }
  if (nextVar.id == NULL_ID) {
    return;
  }
  pushVariableStack(nextVar);
  pushInvariantStack(invariantId);
}

void OutputToInputExplorer::notifyCurrentInvariant() {
  _engine.notifyCurrentInputChanged(peekInvariantStack());
}

template bool
OutputToInputExplorer::pushNextInputVariable<OutputToInputMarkingMode::NONE>();
template bool OutputToInputExplorer::pushNextInputVariable<
    OutputToInputMarkingMode::MARK_SWEEP>();
template bool OutputToInputExplorer::pushNextInputVariable<
    OutputToInputMarkingMode::TOPOLOGICAL_SORT>();

template <OutputToInputMarkingMode MarkingMode>
bool OutputToInputExplorer::pushNextInputVariable() {
  VarId nextVar = _engine.getNextInput(peekInvariantStack());
  if constexpr (MarkingMode != OutputToInputMarkingMode::NONE) {
    while (nextVar != NULL_ID && !isMarked<MarkingMode>(nextVar)) {
      nextVar = _engine.getNextInput(peekInvariantStack());
    }
  }
  if (nextVar.id == NULL_ID) {
    return true;  // done with invariant
  }
  pushVariableStack(nextVar);
  return false;  // not done with invariant
}

void OutputToInputExplorer::registerVar(VarId id) {
  _variableStack.emplace_back(NULL_ID);  // push back just to resize the stack!
  _varComputedAt.register_idx(id);
}

void OutputToInputExplorer::registerInvariant(InvariantId invariantId) {
  _invariantStack.emplace_back(NULL_ID);  // push back just to resize the stack!
  _invariantComputedAt.register_idx(invariantId);
  _invariantIsOnStack.register_idx(invariantId, false);
}

template void OutputToInputExplorer::propagate<OutputToInputMarkingMode::NONE>(
    Timestamp currentTimestamp);
template void OutputToInputExplorer::propagate<
    OutputToInputMarkingMode::MARK_SWEEP>(Timestamp currentTimestamp);
template void OutputToInputExplorer::propagate<
    OutputToInputMarkingMode::TOPOLOGICAL_SORT>(Timestamp currentTimestamp);

template <OutputToInputMarkingMode MarkingMode>
void OutputToInputExplorer::propagate(Timestamp currentTimestamp) {
  preprocessVarStack<MarkingMode>(currentTimestamp);
  // recursively expand variables to compute their value.
  while (_varStackIdx > 0) {
    VarId currentVarId = peekVariableStack();

    // If the variable is not computed, then expand it.
    if (!isComputed(currentTimestamp, currentVarId)) {
      // Variable will become computed as it is either not defined or we now
      // expand its invariant. Note that expandInvariant may sometimes not
      // push a new invariant nor a new variable on the stack, so we must mark
      // the variable as computed before we expand it as this otherwise
      // results in an infinite loop.
      setComputed(currentTimestamp, currentVarId);
      // The variable is marked and computed: expand its defining invariant.
      expandInvariant<MarkingMode>(_engine.getDefiningInvariant(currentVarId));
      continue;
    }
    // currentVarId is done: pop it from the stack.
    popVariableStack();
    if (_invariantStackIdx == 0) {
      // we are at an output variable that is already computed. Just continue!
      continue;
    }
    if (_engine.hasChanged(currentTimestamp, currentVarId)) {
      // If the variable is computed and has changed then just send a
      // notification to top invariant (i.e, the invariant the variable is an
      // input to)
      notifyCurrentInvariant();
    }
    // push the next input variable of the top invariant
    bool invariantDone = pushNextInputVariable<MarkingMode>();
    if (invariantDone) {
      // The top invariant has finished propagating, so all output vars of the
      // top invariant have been computed at the current timestamp.
      for (auto defVar : _engine.getVariablesDefinedBy(peekInvariantStack())) {
        setComputed(currentTimestamp, defVar);
      }
      popInvariantStack();
    }
  }
  clearRegisteredVariables();
}
