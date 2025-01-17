#include <benchmark/benchmark.h>

#include <cassert>
#include <functional>
#include <iostream>
#include <random>
#include <stack>
#include <utility>
#include <vector>

#include "../benchmark.hpp"
#include "atlantis/propagation/invariants/elementVar.hpp"
#include "atlantis/propagation/invariants/linear.hpp"
#include "atlantis/propagation/solver.hpp"

namespace atlantis::benchmark {

class ExtremeDynamic : public ::benchmark::Fixture {
 public:
  std::shared_ptr<propagation::Solver> solver;
  propagation::VarViewId staticInputVar{propagation::NULL_ID};
  std::vector<propagation::VarViewId> dynamicInputVars;
  std::vector<propagation::VarViewId> outputVars;
  propagation::VarViewId objective{propagation::NULL_ID};

  std::random_device rd;
  std::mt19937 gen;
  std::uniform_int_distribution<Int> staticVarValueDist;
  std::uniform_int_distribution<Int> dynamicVarValueDist;
  size_t numInvariants;
  int lb{0};
  int ub{0};

  void SetUp(const ::benchmark::State& state) override {
    solver = std::make_shared<propagation::Solver>();

    lb = 0;
    ub = 1000;

    numInvariants = state.range(0);

    solver->open();
    setSolverMode(*solver, static_cast<int>(state.range(1)));

    staticInputVar = solver->makeIntVar(0, 0, static_cast<Int>(numInvariants));
    for (size_t i = 0; i < numInvariants; ++i) {
      dynamicInputVars.emplace_back(solver->makeIntVar(lb, lb, ub));
      outputVars.emplace_back(solver->makeIntVar(lb, lb, ub));
    }

    for (size_t i = 0; i < numInvariants; ++i) {
      solver->makeInvariant<propagation::ElementVar>(
          *solver, outputVars.at(i), staticInputVar,
          std::vector<propagation::VarViewId>(dynamicInputVars), 0);
    }

    objective = solver->makeIntVar(lb * static_cast<Int>(numInvariants),
                                   lb * static_cast<Int>(numInvariants),
                                   ub * static_cast<Int>(numInvariants));
    solver->makeInvariant<propagation::ElementVar>(
        *solver, objective, staticInputVar,
        std::vector<propagation::VarViewId>(outputVars), 0);

    solver->close();
    gen = std::mt19937(rd());
    staticVarValueDist = std::uniform_int_distribution<Int>{
        0, static_cast<Int>(numInvariants) - 1};
    dynamicVarValueDist = std::uniform_int_distribution<Int>{lb, ub};
  }

  void TearDown(const ::benchmark::State&) override {
    dynamicInputVars.clear();
    outputVars.clear();
  }
};

// probe_single_non_index_var
// probe_single_index_var
// probe_single_move_index_input

BENCHMARK_DEFINE_F(ExtremeDynamic, probe_static_var)
(::benchmark::State& st) {
  size_t probes = 0;
  for ([[maybe_unused]] const auto& _ : st) {
    // Perform move
    solver->beginMove();
    solver->setValue(staticInputVar, staticVarValueDist(gen));
    solver->endMove();

    solver->beginProbe();
    solver->query(objective);
    solver->endProbe();

    ++probes;
  }
  st.counters["probes_per_second"] = ::benchmark::Counter(
      static_cast<double>(probes), ::benchmark::Counter::kIsRate);
}

BENCHMARK_DEFINE_F(ExtremeDynamic, probe_single_dynamic_var)
(::benchmark::State& st) {
  size_t probes = 0;
  for ([[maybe_unused]] const auto& _ : st) {
    solver->beginMove();
    solver->setValue(dynamicInputVars.at(staticVarValueDist(gen)),
                     dynamicVarValueDist(gen));
    solver->endMove();

    solver->beginProbe();
    solver->query(objective);
    solver->endProbe();

    ++probes;
  }
  st.counters["probes_per_second"] = ::benchmark::Counter(
      static_cast<double>(probes), ::benchmark::Counter::kIsRate);
}

//*

// BENCHMARK_REGISTER_F(ExtremeDynamic, probe_static_var)
//     ->Unit(::benchmark::kMillisecond)
//     ->Apply(defaultArguments);

BENCHMARK_REGISTER_F(ExtremeDynamic, probe_single_dynamic_var)
    ->Unit(::benchmark::kMillisecond)
    ->Apply(defaultArguments);

//*/
}  // namespace atlantis::benchmark
