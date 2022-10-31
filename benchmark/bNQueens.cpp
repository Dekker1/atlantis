#include <benchmark/benchmark.h>

#include <iostream>
#include <random>
#include <utility>
#include <vector>

#include "benchmark.hpp"
#include "constraints/allDifferent.hpp"
#include "core/propagationEngine.hpp"
#include "invariants/linear.hpp"
#include "views/intOffsetView.hpp"

class Queens : public benchmark::Fixture {
 public:
  std::unique_ptr<PropagationEngine> engine;
  std::vector<VarId> queens;
  std::vector<VarId> q_offset_plus;
  std::vector<VarId> q_offset_minus;
  std::random_device rd;
  std::mt19937 gen;

  std::uniform_int_distribution<Int> distribution;
  Int n;

  VarId violation1 = NULL_ID;
  VarId violation2 = NULL_ID;
  VarId violation3 = NULL_ID;
  VarId totalViolation = NULL_ID;

  void SetUp(const ::benchmark::State& state) override {
    engine = std::make_unique<PropagationEngine>();
    n = state.range(0);
    if (n < 0) {
      throw std::runtime_error("n must be non-negative.");
    }

    engine->open();

    setEngineModes(*engine, state.range(1));

    for (Int i = 0; i < n; ++i) {
      const VarId q = engine->makeIntVar(i, 0, n - 1);
      queens.push_back(q);
      q_offset_minus.push_back(
          engine->makeIntView<IntOffsetView>(*engine, q, -i));
      q_offset_plus.push_back(
          engine->makeIntView<IntOffsetView>(*engine, q, i));
    }

    violation1 = engine->makeIntVar(0, 0, n);
    violation2 = engine->makeIntVar(0, 0, n);
    violation3 = engine->makeIntVar(0, 0, n);

    engine->makeConstraint<AllDifferent>(*engine, violation1, queens);
    engine->makeConstraint<AllDifferent>(*engine, violation2, q_offset_minus);
    engine->makeConstraint<AllDifferent>(*engine, violation3, q_offset_plus);

    totalViolation = engine->makeIntVar(0, 0, 3 * n);

    engine->makeInvariant<Linear>(
        *engine, totalViolation, std::vector<Int>{1, 1, 1},
        std::vector<VarId>{violation1, violation2, violation3});

    engine->close();

    gen = std::mt19937(rd());

    distribution = std::uniform_int_distribution<Int>{0, n - 1};
  }

  void TearDown(const ::benchmark::State&) override {
    queens.clear();
    q_offset_minus.clear();
    q_offset_plus.clear();
  }

  std::string instanceToString() {
    std::string str = "Queens: ";
    for (auto q : queens) {
      str += std::to_string(engine->committedValue(q)) + ", ";
    }
    return str;
  }
};

BENCHMARK_DEFINE_F(Queens, probe_single_swap)(benchmark::State& st) {
  for (auto _ : st) {
    const size_t i = distribution(gen);
    assert(i < queens.size());
    const size_t j = distribution(gen);
    assert(j < queens.size());
    const Int oldI = engine->committedValue(queens[i]);
    const Int oldJ = engine->committedValue(queens[j]);
    // Perform random swap
    engine->beginMove();
    engine->setValue(queens[i], oldJ);
    engine->setValue(queens[j], oldI);
    engine->endMove();

    engine->beginProbe();
    engine->query(totalViolation);
    engine->endProbe();
  }
}

BENCHMARK_DEFINE_F(Queens, probe_all_swap)(benchmark::State& st) {
  int probes = 0;
  for (auto _ : st) {
    for (size_t i = 0; i < static_cast<size_t>(n); ++i) {
      for (size_t j = i + 1; j < static_cast<size_t>(n); ++j) {
        const Int oldI = engine->committedValue(queens[i]);
        const Int oldJ = engine->committedValue(queens[j]);
        engine->beginMove();
        engine->setValue(queens[i], oldJ);
        engine->setValue(queens[j], oldI);
        engine->endMove();

        engine->beginProbe();
        engine->query(totalViolation);
        engine->endProbe();

        ++probes;
      }
    }
  }
  st.counters["probes_per_second"] =
      benchmark::Counter(probes, benchmark::Counter::kIsRate);
}

BENCHMARK_DEFINE_F(Queens, solve)(benchmark::State& st) {
  Int it = 0;
  Int probes = 0;

  std::vector<Int> tabu;
  tabu.assign(n, 0);
  const Int tenure = 10;
  bool done = false;

  for (auto _ : st) {
    while (it < 100000 && !done) {
      size_t bestI = 0;
      size_t bestJ = 0;
      Int bestViol = n;
      for (size_t i = 0; i < static_cast<size_t>(n); ++i) {
        for (size_t j = i + 1; j < static_cast<size_t>(n); ++j) {
          if (tabu[i] > it && tabu[j] > it) {
            continue;
          }
          const Int oldI = engine->committedValue(queens[i]);
          const Int oldJ = engine->committedValue(queens[j]);
          engine->beginMove();
          engine->setValue(queens[i], oldJ);
          engine->setValue(queens[j], oldI);
          engine->endMove();

          engine->beginProbe();
          engine->query(totalViolation);
          engine->endProbe();

          ++probes;

          Int newValue = engine->currentValue(totalViolation);
          if (newValue <= bestViol) {
            bestViol = newValue;
            bestI = i;
            bestJ = j;
          }
        }
      }

      const Int oldI = engine->committedValue(queens[bestI]);
      const Int oldJ = engine->committedValue(queens[bestJ]);
      engine->beginMove();
      engine->setValue(queens[bestI], oldJ);
      engine->setValue(queens[bestJ], oldI);
      engine->endMove();

      engine->beginCommit();
      engine->query(totalViolation);
      engine->endCommit();

      tabu[bestI] = it + tenure;
      tabu[bestJ] = it + tenure;
      if (bestViol == 0) {
        done = true;
      }
      ++it;
    }
  }

  st.counters["it"] = benchmark::Counter(it);

  st.counters["it_per_s"] = benchmark::Counter(it, benchmark::Counter::kIsRate);
  st.counters["probes_per_s"] =
      benchmark::Counter(probes, benchmark::Counter::kIsRate);
  st.counters["solved"] = benchmark::Counter(done);
  logDebug(instanceToString());
}

/*
static void arguments(benchmark::internal::Benchmark* benchmark) {
  for (int n = 16; n <= 1024; n *= 2) {
    for (int mode = 0; mode <= 3; ++mode) {
      benchmark->Args({n, mode});
    }
#ifndef NDEBUG
    return;
#endif
  }
}

BENCHMARK_REGISTER_F(Queens, probe_single_swap)
    ->Unit(benchmark::kMillisecond)
    ->Apply(arguments);

//*
/*
BENCHMARK_REGISTER_F(Queens, probe_all_swap)
    ->Unit(benchmark::kMillisecond)
    ->Apply(arguments);

/*
BENCHMARK_REGISTER_F(Queens, solve)->Apply(arguments);
//*/