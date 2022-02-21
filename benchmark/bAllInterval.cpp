#include <benchmark/benchmark.h>

#include <constraints/allDifferent.hpp>
#include <core/propagationEngine.hpp>
#include <invariants/absDiff.hpp>
#include <iostream>
#include <random>
#include <utility>
#include <vector>

#include "benchmark.hpp"

class AllInterval : public benchmark::Fixture {
 public:
  std::unique_ptr<PropagationEngine> engine;
  std::vector<VarId> inputVars;
  std::vector<VarId> violationVars;
  std::random_device rd;
  std::mt19937 gen;

  std::uniform_int_distribution<> distribution;
  int n;

  VarId violation = NULL_ID;

  void SetUp(const ::benchmark::State& state) {
    engine = std::make_unique<PropagationEngine>();
    n = state.range(1);

    // TODO: why is this printed multiple times per test?
    logDebug(n);
    engine->open();

    engine->setPropagationMode(intToPropagationMode(state.range(0)));
    engine->setOutputToInputMarkingMode(
        intToOutputToInputMarkingMode(state.range(0)));

    for (int i = 0; i < n; ++i) {
      inputVars.push_back(engine->makeIntVar(i, 0, n - 1));
    }

    for (int i = 1; i < n; ++i) {
      violationVars.push_back(engine->makeIntVar(i, 0, n - 1));
      engine->makeInvariant<AbsDiff>(inputVars.at(i - 1), inputVars.at(i),
                                     violationVars.back());
    }

    violation = engine->makeIntVar(0, 0, n);
    engine->makeConstraint<AllDifferent>(violation, violationVars);

    engine->close();

    gen = std::mt19937(rd());

    distribution = std::uniform_int_distribution<>{0, n - 1};
  }

  void TearDown(const ::benchmark::State&) {
    inputVars.clear();
    violationVars.clear();
  }
};

BENCHMARK_DEFINE_F(AllInterval, probing_single_swap)(benchmark::State& st) {
  Int probes = 0;
  for (auto _ : st) {
    int i = distribution(gen);
    int j = distribution(gen);
    Int oldI = engine->getCommittedValue(inputVars.at(i));
    Int oldJ = engine->getCommittedValue(inputVars.at(j));
    // Perform random swap
    engine->beginMove();
    engine->setValue(inputVars.at(i), oldJ);
    engine->setValue(inputVars.at(j), oldI);
    engine->endMove();

    engine->beginQuery();
    engine->query(violation);
    engine->endQuery();
    ++probes;
  }
  st.counters["probes_per_second"] =
      benchmark::Counter(probes, benchmark::Counter::kIsRate);
}

BENCHMARK_DEFINE_F(AllInterval, probing_all_swap)(benchmark::State& st) {
  Int probes = 0;
  for (auto _ : st) {
    for (size_t i = 0; i < static_cast<size_t>(n); ++i) {
      for (size_t j = i + 1; j < static_cast<size_t>(n); ++j) {
        Int oldI = engine->getCommittedValue(inputVars.at(i));
        Int oldJ = engine->getCommittedValue(inputVars.at(j));
        engine->beginMove();
        engine->setValue(inputVars.at(i), oldJ);
        engine->setValue(inputVars.at(j), oldI);
        engine->endMove();

        engine->beginQuery();
        engine->query(violation);
        engine->endQuery();

        ++probes;
      }
    }
  }
  st.counters["probes_per_second"] =
      benchmark::Counter(probes, benchmark::Counter::kIsRate);
}

BENCHMARK_DEFINE_F(AllInterval, commit_single_swap)(benchmark::State& st) {
  int commits = 0;
  for (auto _ : st) {
    int i = distribution(gen);
    int j = distribution(gen);

    Int oldI = engine->getCommittedValue(inputVars.at(i));
    Int oldJ = engine->getCommittedValue(inputVars.at(j));
    // Perform random swap
    engine->beginMove();
    engine->setValue(inputVars.at(i), oldJ);
    engine->setValue(inputVars.at(j), oldI);
    engine->endMove();

    engine->beginCommit();
    engine->query(violation);
    engine->endCommit();

    ++commits;
  }

  st.counters["seconds_per_commit"] = benchmark::Counter(
      commits, benchmark::Counter::kIsRate | benchmark::Counter::kInvert);
}

///*
static void arguments(benchmark::internal::Benchmark* benchmark) {
  for (int n = 10; n <= 30; n += 10) {
    for (int mode = 0; mode <= 3; ++mode) {
      benchmark->Args({mode, n});
    }
  }
}

static void commitArguments(benchmark::internal::Benchmark* benchmark) {
  for (int n = 10; n <= 30; n += 10) {
    benchmark->Args({0, n});
  }
}

BENCHMARK_REGISTER_F(AllInterval, probing_single_swap)->Apply(arguments);
BENCHMARK_REGISTER_F(AllInterval, probing_all_swap)
    ->Unit(benchmark::kMillisecond)
    ->Apply(arguments);
BENCHMARK_REGISTER_F(AllInterval, commit_single_swap)->Apply(commitArguments);
//*/