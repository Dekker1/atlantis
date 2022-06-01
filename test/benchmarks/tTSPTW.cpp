#include <gtest/gtest.h>

#include <algorithm>
#include <constraints/lessEqual.hpp>
#include <core/propagationEngine.hpp>
#include <invariants/elementVar.hpp>
#include <invariants/linear.hpp>
#include <random>
#include <vector>
#include <views/elementConst.hpp>

#include "../testHelper.hpp"
#include "core/types.hpp"

namespace {
class TSPTWTest : public ::testing::Test {
 public:
  std::unique_ptr<PropagationEngine> engine;
  std::vector<VarId> pred;
  std::vector<VarId> timeToPrev;
  std::vector<VarId> arrivalPrev;
  std::vector<VarId> arrivalTime;
  std::vector<std::vector<Int>> dist;
  VarId totalDist;

  std::random_device rd;

  Int n;
  const int MAX_TIME = 100000;

  std::vector<VarId> violation;
  VarId totalViolation;

  void SetUp() override {
    engine = std::make_unique<PropagationEngine>();
    n = 30;

    logInfo(n);
    engine->open();

    for (int i = 0; i < n; ++i) {
      dist.emplace_back(std::vector<Int>());
      for (int j = 0; j < n; ++j) {
        dist[i].push_back(1);
      }
    }

    for (int i = 1; i <= n; ++i) {
      const Int initVal = 1 + (i % n);
      pred.emplace_back(engine->makeIntVar(initVal, 1, n));
      timeToPrev.emplace_back(engine->makeIntVar(0, 0, MAX_TIME));
      arrivalTime.emplace_back(engine->makeIntVar(0, 0, MAX_TIME));
      arrivalPrev.emplace_back(engine->makeIntVar(0, 0, MAX_TIME));
      violation.emplace_back(engine->makeIntVar(0, 0, MAX_TIME));
    }

    // Ignore index 0
    for (int i = 1; i < n; ++i) {
      // timeToPrev[i] = dist[i][pred[i]]
      timeToPrev[i] = engine->makeIntView<ElementConst>(pred[i], dist[i]);
      // arrivalPrev[i] = arrivalTime[pred[i]]
    }

    // Ignore index 0
    for (int i = 1; i < n; ++i) {
      // arrivalPrev[i] = arrivalTime[pred[i]]
      engine->makeInvariant<ElementVar>(arrivalPrev[i], pred[i], arrivalTime);
      // arrivalTime[i] = arrivalPrev[i] + timeToPrev[i]
      engine->makeInvariant<Linear>(
          arrivalTime[i], std::vector<VarId>({arrivalPrev[i], timeToPrev[i]}));
    }

    // totalDist = sum(timeToPrev)
    totalDist = engine->makeIntVar(0, 0, MAX_TIME);
    engine->makeInvariant<Linear>(totalDist, timeToPrev);

    VarId leqConst = engine->makeIntVar(100, 100, 100);
    for (int i = 0; i < n; ++i) {
      engine->makeConstraint<LessEqual>(violation[i], arrivalTime[i], leqConst);
    }

    totalViolation = engine->makeIntVar(0, 0, MAX_TIME * n);
    engine->makeInvariant<Linear>(totalViolation, violation);

    engine->close();
    for (const VarId p : pred) {
      assert(engine->lowerBound(p) == 1);
      assert(engine->upperBound(p) == n);
      assert(1 <= engine->committedValue(p) && engine->committedValue(p) <= n);
    }
  }

  void TearDown() override {
    pred.clear();
    timeToPrev.clear();
    arrivalPrev.clear();
    arrivalTime.clear();
    dist.clear();
    violation.clear();
  }
};

/**
 *  Testing constructor
 */

TEST_F(TSPTWTest, Probing) {
  for (int i = 0; i < n; ++i) {
    for (int j = 0; j < n; ++j) {
      if (i == j || engine->committedValue(pred[i]) == j + 1) {
        continue;
      }
      engine->beginMove();
      engine->setValue(
          pred[i],
          engine->committedValue(pred.at(engine->committedValue(pred[i]) - 1)));
      engine->setValue(pred[j], engine->committedValue(pred[i]));
      engine->setValue(pred.at(engine->committedValue(pred[i]) - 1),
                       engine->committedValue(pred[j]));
      engine->endMove();

      engine->beginProbe();
      engine->query(totalDist);
      engine->query(totalViolation);
      engine->endProbe();
    }
  }
}

}  // namespace
