#include <benchmark/benchmark.h>

#include <algorithm>
#include <cassert>
#include <cstdlib>
#include <ctime>
#include <iostream>
#include <random>
#include <stack>
#include <utility>
#include <vector>

#include "../benchmark.hpp"
#include "propagation/violationInvariants/allDifferent.hpp"
#include "propagation/invariants/absDiff.hpp"
#include "propagation/invariants/linear.hpp"
#include "propagation/solver.hpp"

namespace atlantis::benchmark {

class FoldableBinaryTree : public ::benchmark::Fixture {
 private:
  propagation::VarId randomVar() { return vars.at(std::rand() % vars.size()); }
  propagation::VarId createTree() {
    propagation::VarId output = solver->makeIntVar(0, lb, ub);
    vars.push_back(output);

    propagation::VarId prev = output;

    for (size_t level = 0; level < treeHeight; ++level) {
      propagation::VarId left = solver->makeIntVar(0, lb, ub);
      propagation::VarId right = solver->makeIntVar(0, lb, ub);
      vars.push_back(left);
      vars.push_back(right);

      solver->makeInvariant<propagation::Linear>(
          *solver, prev, std::vector<propagation::VarId>{left, right});
      if (level == treeHeight - 1) {
        decisionVars.push_back(left);
      }
      decisionVars.push_back(right);
      prev = left;
    }
    assert(decisionVars.size() == treeHeight + 1);
    return output;
  }

 public:
  std::unique_ptr<propagation::Solver> solver;
  std::vector<propagation::VarId> vars;
  std::vector<propagation::VarId> decisionVars;
  propagation::VarId queryVar;
  std::random_device rd;

  std::mt19937 genValue;

  std::uniform_int_distribution<Int> decisionVarValueDist;

  size_t treeHeight;
  Int lb;
  Int ub;

  void probe(::benchmark::State& st, size_t moveCount);
  void probeRnd(::benchmark::State& st, size_t moveCount);
  void commit(::benchmark::State& st, size_t moveCount);
  void commitRnd(::benchmark::State& st, size_t moveCount);

  void SetUp(const ::benchmark::State& state) {
    std::srand(std::time(0));

    solver = std::make_unique<propagation::Solver>();

    treeHeight = state.range(0);  // Tree height
    lb = -1000;
    ub = 1000;

    solver->open();
    setSolverMode(*solver, state.range(1));

    queryVar = createTree();

    solver->close();

    genValue = std::mt19937(rd());
    decisionVarValueDist = std::uniform_int_distribution<Int>(lb, ub);
  }

  void TearDown(const ::benchmark::State&) {
    decisionVars.clear();
    vars.clear();
  }
};

void FoldableBinaryTree::probe(::benchmark::State& st, size_t moveCount) {
  size_t probes = 0;
  moveCount = std::min(moveCount, decisionVars.size());
  for (auto _ : st) {
    st.PauseTiming();
    std::random_shuffle(decisionVars.begin(), decisionVars.end());
    st.ResumeTiming();

    solver->beginMove();
    for (size_t i = 0; i < moveCount; ++i) {
      solver->setValue(decisionVars.at(i), decisionVarValueDist(genValue));
    }
    solver->endMove();

    // Query queryVar var
    solver->beginProbe();
    solver->query(queryVar);
    solver->endProbe();
    ++probes;
  }

  st.counters["probes_per_second"] =
      ::benchmark::Counter(probes, ::benchmark::Counter::kIsRate);
}

void FoldableBinaryTree::probeRnd(::benchmark::State& st, size_t moveCount) {
  size_t probes = 0;
  moveCount = std::min(moveCount, decisionVars.size());
  for (auto _ : st) {
    st.PauseTiming();
    std::random_shuffle(decisionVars.begin(), decisionVars.end());
    st.ResumeTiming();

    solver->beginMove();
    for (size_t i = 0; i < moveCount; ++i) {
      if (i >= decisionVars.size()) {
        logWarning("i: " << i);
      }
      solver->setValue(decisionVars.at(i), decisionVarValueDist(genValue));
    }
    solver->endMove();

    // Random query variable
    solver->beginProbe();
    solver->query(randomVar());
    solver->endProbe();
    ++probes;
  }

  st.counters["probes_per_second"] =
      ::benchmark::Counter(probes, ::benchmark::Counter::kIsRate);
}

void FoldableBinaryTree::commit(::benchmark::State& st, size_t moveCount) {
  size_t commits = 0;
  moveCount = std::min(moveCount, decisionVars.size());
  for (auto _ : st) {
    st.PauseTiming();
    std::random_shuffle(decisionVars.begin(), decisionVars.end());

    solver->beginMove();
    for (size_t i = 0; i < moveCount; ++i) {
      solver->setValue(decisionVars.at(i), decisionVarValueDist(genValue));
    }
    solver->endMove();

    st.ResumeTiming();

    // Commit last queryVar var
    solver->beginCommit();
    solver->query(queryVar);
    solver->endCommit();
    ++commits;
  }

  st.counters["seconds_per_commit"] = ::benchmark::Counter(
      commits, ::benchmark::Counter::kIsRate | ::benchmark::Counter::kInvert);
}

void FoldableBinaryTree::commitRnd(::benchmark::State& st, size_t moveCount) {
  size_t commits = 0;
  moveCount = std::min(moveCount, decisionVars.size());
  for (auto _ : st) {
    st.PauseTiming();
    std::random_shuffle(decisionVars.begin(), decisionVars.end());

    solver->beginMove();
    for (size_t i = 0; i < moveCount; ++i) {
      solver->setValue(decisionVars.at(i), decisionVarValueDist(genValue));
    }
    solver->endMove();

    st.ResumeTiming();

    // Query random variable
    solver->beginCommit();
    solver->query(randomVar());
    solver->endCommit();
    ++commits;
  }

  st.counters["seconds_per_commit"] = ::benchmark::Counter(
      commits, ::benchmark::Counter::kIsRate | ::benchmark::Counter::kInvert);
}

BENCHMARK_DEFINE_F(FoldableBinaryTree, probe_single)
(::benchmark::State& st) { probe(std::ref(st), 1); }

BENCHMARK_DEFINE_F(FoldableBinaryTree, probe_single_query_rnd)
(::benchmark::State& st) { probeRnd(std::ref(st), 1); }

BENCHMARK_DEFINE_F(FoldableBinaryTree, probe_double)
(::benchmark::State& st) { probe(std::ref(st), 2); }

BENCHMARK_DEFINE_F(FoldableBinaryTree, probe_double_query_rnd)
(::benchmark::State& st) { probeRnd(std::ref(st), 2); }

BENCHMARK_DEFINE_F(FoldableBinaryTree, probe_all)
(::benchmark::State& st) { probe(std::ref(st), st.range(1) + 1); }

BENCHMARK_DEFINE_F(FoldableBinaryTree, probe_all_query_rnd)
(::benchmark::State& st) { probeRnd(std::ref(st), st.range(1) + 1); }

BENCHMARK_DEFINE_F(FoldableBinaryTree, commit_move_single)
(::benchmark::State& st) { commit(std::ref(st), 1); }

BENCHMARK_DEFINE_F(FoldableBinaryTree, commit_move_single_query_rnd)
(::benchmark::State& st) { commitRnd(std::ref(st), 1); }

BENCHMARK_DEFINE_F(FoldableBinaryTree, commit_move_two)
(::benchmark::State& st) { commit(std::ref(st), 2); }

BENCHMARK_DEFINE_F(FoldableBinaryTree, commit_move_two_query_rnd)
(::benchmark::State& st) { commitRnd(std::ref(st), 2); }

BENCHMARK_DEFINE_F(FoldableBinaryTree, commit_move_all)
(::benchmark::State& st) { commit(std::ref(st), decisionVars.size()); }

BENCHMARK_DEFINE_F(FoldableBinaryTree, commit_move_all_query_rnd)
(::benchmark::State& st) { commitRnd(std::ref(st), decisionVars.size()); }

/*

// -----------------------------------------
// Probing
// ------------------------------------------

static void arguments(::benchmark::internal::Benchmark* benchmark) {
  for (int treeHeight = 2; treeHeight <= 10; treeHeight += 2) {
    for (Int mode = 0; mode <= 3; ++mode) {
      benchmark->Args({treeHeight, mode});
    }
#ifndef NDEBUG
    return;
#endif
  }
}

BENCHMARK_REGISTER_F(FoldableBinaryTree, probe_single)
    ->Unit(::benchmark::kMillisecond)
    ->Apply(arguments);
BENCHMARK_REGISTER_F(FoldableBinaryTree, probe_single_query_rnd)
    ->Unit(::benchmark::kMillisecond)
    ->Apply(arguments);

/*
BENCHMARK_REGISTER_F(FoldableBinaryTree, probe_double)
    ->Unit(::benchmark::kMillisecond)
    ->Apply(arguments);
BENCHMARK_REGISTER_F(FoldableBinaryTree, probe_double_query_rnd)
    ->Unit(::benchmark::kMillisecond)
    ->Apply(arguments);
BENCHMARK_REGISTER_F(FoldableBinaryTree, probe_all)
    ->Unit(::benchmark::kMillisecond)
    ->Apply(arguments);
BENCHMARK_REGISTER_F(FoldableBinaryTree, probe_all_query_rnd)
    ->Unit(::benchmark::kMillisecond)
    ->Apply(arguments);

/*
// -----------------------------------------
// Commit
// ------------------------------------------

// BENCHMARK_REGISTER_F(FoldableBinaryTree, commit_move_single)
//    ->ArgsProduct({::benchmark::CreateRange(4, 4, 2),
//                   ::benchmark::CreateRange(0, 0, 0)});
BENCHMARK_REGISTER_F(FoldableBinaryTree, commit_move_single_query_rnd)
    ->DenseRange(4, 4, 2);
BENCHMARK_REGISTER_F(FoldableBinaryTree, commit_move_two)->DenseRange(4, 4, 2);
BENCHMARK_REGISTER_F(FoldableBinaryTree, commit_move_two_query_rnd)
    ->DenseRange(4, 4, 2);
BENCHMARK_REGISTER_F(FoldableBinaryTree, commit_move_all)->DenseRange(4, 4, 2);
BENCHMARK_REGISTER_F(FoldableBinaryTree, commit_move_all_query_rnd)
    ->DenseRange(4, 4, 2);

//*/
}  // namespace atlantis::benchmark