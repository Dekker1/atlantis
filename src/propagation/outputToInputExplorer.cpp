
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
      _searchVariableAncestors(expectedSize),
      _onPropagationPath(expectedSize),
      _outputToInputMarkingMode(OutputToInputMarkingMode::NONE) {
  _variableStack.reserve(expectedSize);
  _invariantStack.reserve(expectedSize);
}

void OutputToInputExplorer::outputToInputStaticMarking() {
  std::vector<bool> varVisited(_engine.numVariables() + 1);

  for (IdBase idx = 1; idx <= _engine.numVariables(); ++idx) {
    if (_searchVariableAncestors.size() < idx) {
      _searchVariableAncestors.register_idx(idx);
    }

    _searchVariableAncestors[idx].clear();
  }

  for (const VarIdBase searchVariable : _engine.searchVariables()) {
    std::fill(varVisited.begin(), varVisited.end(), false);
    std::vector<IdBase> stack;
    stack.reserve(_engine.numVariables());

    stack.emplace_back(searchVariable);
    varVisited[searchVariable] = true;

    while (!stack.empty()) {
      const VarIdBase id = stack.back();
      stack.pop_back();
      _searchVariableAncestors[id].emplace(searchVariable);

      for (InvariantId invariantId : _engine.listeningInvariants(IdBase(id))) {
        for (const VarIdBase outputVar :
             _engine.variablesDefinedBy(invariantId)) {
          if (!varVisited[outputVar]) {
            varVisited[outputVar] = true;
            stack.push_back(outputVar);
          }
        }
      }
    }
  }
}

void OutputToInputExplorer::inputToOutputExplorationMarking() {
  std::vector<IdBase> stack;
  stack.reserve(_engine.numVariables());

  _onPropagationPath.assign(_engine.numVariables(), false);

  for (const VarIdBase modifiedDecisionVar :
       _engine.modifiedSearchVariables()) {
    stack.emplace_back(modifiedDecisionVar);
    assert(!_onPropagationPath.get(modifiedDecisionVar));
    _onPropagationPath.set(modifiedDecisionVar, true);

    while (!stack.empty()) {
      const IdBase id = stack.back();
      stack.pop_back();
      for (InvariantId invariantId : _engine.listeningInvariants(id)) {
        for (const VarIdBase outputVar :
             _engine.variablesDefinedBy(invariantId)) {
          if (!_onPropagationPath.get(outputVar)) {
            _onPropagationPath.set(outputVar, true);
            stack.emplace_back(outputVar);
          }
        }
      }
    }
  }
}

template void OutputToInputExplorer::close<OutputToInputMarkingMode::NONE>();
template void OutputToInputExplorer::close<
    OutputToInputMarkingMode::OUTPUT_TO_INPUT_STATIC>();
template void OutputToInputExplorer::close<
    OutputToInputMarkingMode::INPUT_TO_OUTPUT_EXPLORATION>();
template <OutputToInputMarkingMode MarkingMode>
void OutputToInputExplorer::close() {
  if constexpr (MarkingMode !=
                OutputToInputMarkingMode::OUTPUT_TO_INPUT_STATIC) {
    _searchVariableAncestors.clear();
  }
  if constexpr (MarkingMode !=
                OutputToInputMarkingMode::INPUT_TO_OUTPUT_EXPLORATION) {
    _onPropagationPath.clear();
  }
  if constexpr (MarkingMode ==
                OutputToInputMarkingMode::OUTPUT_TO_INPUT_STATIC) {
    outputToInputStaticMarking();
  }
}

void OutputToInputExplorer::propagate(Timestamp ts) {
  if (_outputToInputMarkingMode == OutputToInputMarkingMode::NONE) {
    propagate<OutputToInputMarkingMode::NONE>(ts);
  } else if (_outputToInputMarkingMode ==
             OutputToInputMarkingMode::INPUT_TO_OUTPUT_EXPLORATION) {
    inputToOutputExplorationMarking();
    propagate<OutputToInputMarkingMode::INPUT_TO_OUTPUT_EXPLORATION>(ts);
  } else if (_outputToInputMarkingMode ==
             OutputToInputMarkingMode::OUTPUT_TO_INPUT_STATIC) {
    propagate<OutputToInputMarkingMode::OUTPUT_TO_INPUT_STATIC>(ts);
  }
}

template bool OutputToInputExplorer::isMarked<OutputToInputMarkingMode::NONE>(
    VarIdBase id);
template bool OutputToInputExplorer::isMarked<
    OutputToInputMarkingMode::OUTPUT_TO_INPUT_STATIC>(VarIdBase id);
template bool OutputToInputExplorer::isMarked<
    OutputToInputMarkingMode::INPUT_TO_OUTPUT_EXPLORATION>(VarIdBase id);
template <OutputToInputMarkingMode MarkingMode>
bool OutputToInputExplorer::isMarked(VarIdBase id) {
  if constexpr (MarkingMode ==
                OutputToInputMarkingMode::OUTPUT_TO_INPUT_STATIC) {
    for (const size_t ancestor : _engine.modifiedSearchVariables()) {
      if (_searchVariableAncestors.at(id).find(ancestor) !=
          _searchVariableAncestors.at(id).end()) {
        return true;
      }
    }
    return false;
  } else if constexpr (MarkingMode ==
                       OutputToInputMarkingMode::INPUT_TO_OUTPUT_EXPLORATION) {
    return _onPropagationPath.get(id);
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
    OutputToInputMarkingMode::OUTPUT_TO_INPUT_STATIC>(
    Timestamp currentTimestamp);
template void OutputToInputExplorer::preprocessVarStack<
    OutputToInputMarkingMode::INPUT_TO_OUTPUT_EXPLORATION>(
    Timestamp currentTimestamp);
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
    OutputToInputMarkingMode::OUTPUT_TO_INPUT_STATIC>(InvariantId);
template void OutputToInputExplorer::expandInvariant<
    OutputToInputMarkingMode::INPUT_TO_OUTPUT_EXPLORATION>(InvariantId);
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
  VarId nextVar = _engine.nextInput(invariantId);
  if constexpr (MarkingMode != OutputToInputMarkingMode::NONE) {
    while (nextVar != NULL_ID && !isMarked<MarkingMode>(nextVar)) {
      nextVar = _engine.nextInput(invariantId);
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
    OutputToInputMarkingMode::OUTPUT_TO_INPUT_STATIC>();
template bool OutputToInputExplorer::pushNextInputVariable<
    OutputToInputMarkingMode::INPUT_TO_OUTPUT_EXPLORATION>();

template <OutputToInputMarkingMode MarkingMode>
bool OutputToInputExplorer::pushNextInputVariable() {
  VarId nextVar = _engine.nextInput(peekInvariantStack());
  if constexpr (MarkingMode != OutputToInputMarkingMode::NONE) {
    while (nextVar != NULL_ID && !isMarked<MarkingMode>(nextVar)) {
      nextVar = _engine.nextInput(peekInvariantStack());
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
    OutputToInputMarkingMode::OUTPUT_TO_INPUT_STATIC>(
    Timestamp currentTimestamp);
template void OutputToInputExplorer::propagate<
    OutputToInputMarkingMode::INPUT_TO_OUTPUT_EXPLORATION>(
    Timestamp currentTimestamp);

template <OutputToInputMarkingMode MarkingMode>
void OutputToInputExplorer::propagate(Timestamp currentTimestamp) {
  preprocessVarStack<MarkingMode>(currentTimestamp);
  // recursively expand variables to compute their value.
  while (_varStackIdx > 0) {
    const VarId currentVarId = peekVariableStack();

    // If the variable is not computed, then expand it.
    if (!isComputed(currentTimestamp, currentVarId)) {
      // Variable will become computed as it is either not defined or we now
      // expand its invariant. Note that expandInvariant may sometimes not
      // push a new invariant nor a new variable on the stack, so we must mark
      // the variable as computed before we expand it as this otherwise
      // results in an infinite loop.
      setComputed(currentTimestamp, currentVarId);
      // The variable is marked and computed: expand its defining invariant.
      expandInvariant<MarkingMode>(_engine.definingInvariant(currentVarId));
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
    // returns false if there are no more variables to push
    if (pushNextInputVariable<MarkingMode>()) {
      // The top invariant has finished propagating, so all defined vars can
      // be marked as compte at the current time.
      for (const auto defVar :
           _engine.variablesDefinedBy(peekInvariantStack())) {
        setComputed(currentTimestamp, defVar);
      }
      popInvariantStack();
    }
  }
  clearRegisteredVariables();
}
