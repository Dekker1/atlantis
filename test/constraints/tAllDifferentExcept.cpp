#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <algorithm>
#include <random>
#include <vector>

#include "../testHelper.hpp"
#include "constraints/allDifferentExcept.hpp"
#include "core/propagationEngine.hpp"
#include "core/types.hpp"

using ::testing::AtLeast;
using ::testing::AtMost;
using ::testing::Return;

namespace {

class AllDifferentExceptTest : public InvariantTest {
 public:
  Int computeViolation(const Timestamp ts, const std::vector<VarId>& variables,
                       const std::unordered_set<Int>& ignoredSet) {
    std::vector<Int> values(variables.size(), 0);
    for (size_t i = 0; i < variables.size(); ++i) {
      values.at(i) = engine->value(ts, variables.at(i));
    }
    return computeViolation(values, ignoredSet);
  }

  Int computeViolation(const std::vector<Int>& values,
                       const std::unordered_set<Int>& ignoredSet) {
    std::vector<bool> checked(values.size(), false);
    Int expectedViolation = 0;
    for (size_t i = 0; i < values.size(); ++i) {
      if (checked[i] || ignoredSet.count(values[i]) > 0) {
        continue;
      }
      checked[i] = true;
      for (size_t j = i + 1; j < values.size(); ++j) {
        if (checked[j]) {
          continue;
        }
        if (values[i] == values[j]) {
          checked[j] = true;
          ++expectedViolation;
        }
      }
    }
    return expectedViolation;
  }
};

TEST_F(AllDifferentExceptTest, UpdateBounds) {
  std::vector<std::pair<Int, Int>> boundVec{
      {-250, -150}, {-100, 0}, {-50, 50}, {0, 100}, {150, 250}};
  engine->open();
  std::vector<VarId> inputs{engine->makeIntVar(0, 0, 0),
                            engine->makeIntVar(0, 0, 0),
                            engine->makeIntVar(0, 0, 0)};
  const VarId violationId = engine->makeIntVar(0, 0, 2);
  AllDifferentExcept& invariant = engine->makeConstraint<AllDifferentExcept>(
      violationId, std::vector<VarId>(inputs), std::vector<Int>{10, 20});

  for (const auto& [aLb, aUb] : boundVec) {
    EXPECT_TRUE(aLb <= aUb);
    engine->updateBounds(inputs.at(0), aLb, aUb);
    for (const auto& [bLb, bUb] : boundVec) {
      EXPECT_TRUE(bLb <= bUb);
      engine->updateBounds(inputs.at(2), bLb, bUb);
      for (const auto& [cLb, cUb] : boundVec) {
        EXPECT_TRUE(cLb <= cUb);
        engine->updateBounds(inputs.at(2), cLb, cUb);
        invariant.updateBounds(*engine);
        ASSERT_EQ(0, engine->lowerBound(violationId));
        ASSERT_EQ(inputs.size() - 1, engine->upperBound(violationId));
      }
    }
  }
}

TEST_F(AllDifferentExceptTest, Recompute) {
  std::vector<std::pair<Int, Int>> boundVec{
      {-10004, -10000}, {-1, 1}, {10000, 10002}};

  std::vector<std::vector<Int>> ignoredVec{
      {-10003, -10000}, {-2, -1, 2}, {10000}};

  for (size_t i = 0; i < boundVec.size(); ++i) {
    auto const [lb, ub] = boundVec[i];
    auto const ignored = ignoredVec[i];
    std::unordered_set<Int> ignoredSet;
    std::copy(ignored.begin(), ignored.end(),
              std::inserter(ignoredSet, ignoredSet.end()));
    EXPECT_TRUE(lb <= ub);

    engine->open();
    const VarId a = engine->makeIntVar(lb, lb, ub);
    const VarId b = engine->makeIntVar(lb, lb, ub);
    const VarId c = engine->makeIntVar(lb, lb, ub);
    const VarId violationId = engine->makeIntVar(0, 0, 2);
    AllDifferentExcept& invariant = engine->makeConstraint<AllDifferentExcept>(
        violationId, std::vector<VarId>{a, b, c}, std::vector<Int>(ignored));
    engine->close();

    const std::vector<VarId> inputs{a, b, c};

    for (Int aVal = lb; aVal <= ub; ++aVal) {
      for (Int bVal = lb; bVal <= ub; ++bVal) {
        for (Int cVal = lb; cVal <= ub; ++cVal) {
          engine->setValue(engine->currentTimestamp(), a, aVal);
          engine->setValue(engine->currentTimestamp(), b, bVal);
          engine->setValue(engine->currentTimestamp(), c, cVal);
          const Int expectedViolation =
              computeViolation(engine->currentTimestamp(), inputs, ignoredSet);
          invariant.recompute(engine->currentTimestamp(), *engine);
          EXPECT_EQ(expectedViolation,
                    engine->value(engine->currentTimestamp(), violationId));
        }
      }
    }
  }
}

TEST_F(AllDifferentExceptTest, NotifyInputChanged) {
  std::vector<std::pair<Int, Int>> boundVec{
      {-10002, -10000}, {-1, 1}, {10000, 10002}};

  std::vector<std::vector<Int>> ignoredVec{
      {-10003, -10000}, {-2, -1, 2}, {10000}};

  for (size_t i = 0; i < boundVec.size(); ++i) {
    auto const [lb, ub] = boundVec[i];
    auto const ignored = ignoredVec[i];
    std::unordered_set<Int> ignoredSet;
    std::copy(ignored.begin(), ignored.end(),
              std::inserter(ignoredSet, ignoredSet.end()));
    EXPECT_TRUE(lb <= ub);

    engine->open();
    std::vector<VarId> inputs{engine->makeIntVar(lb, lb, ub),
                              engine->makeIntVar(lb, lb, ub),
                              engine->makeIntVar(lb, lb, ub)};
    const VarId violationId = engine->makeIntVar(0, 0, 2);
    AllDifferentExcept& invariant = engine->makeConstraint<AllDifferentExcept>(
        violationId, std::vector<VarId>(inputs), std::vector<Int>(ignored));
    engine->close();

    for (Int val = lb; val <= ub; ++val) {
      for (size_t j = 0; j < inputs.size(); ++j) {
        engine->setValue(engine->currentTimestamp(), inputs[j], val);
        const Int expectedViolation =
            computeViolation(engine->currentTimestamp(), inputs, ignoredSet);

        invariant.notifyInputChanged(engine->currentTimestamp(), *engine,
                                     LocalId(j));
        EXPECT_EQ(expectedViolation,
                  engine->value(engine->currentTimestamp(), violationId));
      }
    }
  }
}

TEST_F(AllDifferentExceptTest, NextInput) {
  const size_t numInputs = 1000;
  const Int lb = 0;
  const Int ub = numInputs - 1;
  EXPECT_TRUE(lb <= ub);

  engine->open();
  std::vector<size_t> indices;
  std::vector<Int> committedValues;
  std::vector<VarId> inputs;
  for (size_t i = 0; i < numInputs; ++i) {
    inputs.emplace_back(engine->makeIntVar(i, lb, ub));
  }

  std::vector<Int> ignored;
  for (size_t i = 0; i < numInputs; i += 3) {
    ignored.emplace_back(i);
  }

  const VarId minVarId = *std::min_element(inputs.begin(), inputs.end());
  const VarId maxVarId = *std::max_element(inputs.begin(), inputs.end());

  std::shuffle(inputs.begin(), inputs.end(), rng);

  const VarId violationId = engine->makeIntVar(0, 0, 2);
  AllDifferentExcept& invariant = engine->makeConstraint<AllDifferentExcept>(
      violationId, std::vector<VarId>(inputs), ignored);
  engine->close();

  for (Timestamp ts = engine->currentTimestamp() + 1;
       ts < engine->currentTimestamp() + 4; ++ts) {
    std::vector<bool> notified(maxVarId + 1, false);
    for (size_t i = 0; i < numInputs; ++i) {
      const VarId varId = invariant.nextInput(ts, *engine);
      EXPECT_NE(varId, NULL_ID);
      EXPECT_TRUE(minVarId <= varId);
      EXPECT_TRUE(varId <= maxVarId);
      EXPECT_FALSE(notified.at(varId));
      notified[varId] = true;
    }
    EXPECT_EQ(invariant.nextInput(ts, *engine), NULL_ID);
    for (size_t varId = minVarId; varId <= maxVarId; ++varId) {
      EXPECT_TRUE(notified.at(varId));
    }
  }
}

TEST_F(AllDifferentExceptTest, NotifyCurrentInputChanged) {
  const Int lb = -10;
  const Int ub = 10;
  EXPECT_TRUE(lb <= ub);

  engine->open();
  const size_t numInputs = 100;
  std::uniform_int_distribution<Int> valueDist(lb, ub);
  std::vector<VarId> inputs;
  for (size_t i = 0; i < numInputs; ++i) {
    inputs.emplace_back(engine->makeIntVar(valueDist(gen), lb, ub));
  }
  std::vector<Int> ignored;
  for (size_t i = 0; i < numInputs; i += 3) {
    ignored.emplace_back(i);
  }
  std::unordered_set<Int> ignoredSet;
  std::copy(ignored.begin(), ignored.end(),
            std::inserter(ignoredSet, ignoredSet.end()));

  const VarId violationId = engine->makeIntVar(0, 0, numInputs - 1);
  AllDifferentExcept& invariant = engine->makeConstraint<AllDifferentExcept>(
      violationId, std::vector<VarId>(inputs), ignored);
  engine->close();

  for (Timestamp ts = engine->currentTimestamp() + 1;
       ts < engine->currentTimestamp() + 4; ++ts) {
    for (const VarId varId : inputs) {
      EXPECT_EQ(invariant.nextInput(ts, *engine), varId);
      const Int oldVal = engine->value(ts, varId);
      do {
        engine->setValue(ts, varId, valueDist(gen));
      } while (engine->value(ts, varId) == oldVal);
      invariant.notifyCurrentInputChanged(ts, *engine);
      EXPECT_EQ(engine->value(ts, violationId),
                computeViolation(ts, inputs, ignoredSet));
    }
  }
}

TEST_F(AllDifferentExceptTest, Commit) {
  const Int lb = -10;
  const Int ub = 10;
  EXPECT_TRUE(lb <= ub);

  engine->open();
  const size_t numInputs = 1000;
  std::uniform_int_distribution<Int> valueDist(lb, ub);
  std::uniform_int_distribution<size_t> varDist(size_t(0), numInputs);
  std::vector<size_t> indices;
  std::vector<Int> committedValues;
  std::vector<VarId> inputs;
  std::vector<Int> ignored;
  for (size_t i = 0; i < numInputs; ++i) {
    indices.emplace_back(i);
    committedValues.emplace_back(valueDist(gen));
    inputs.emplace_back(engine->makeIntVar(committedValues.back(), lb, ub));
    ignored.emplace_back(i);
  }
  std::unordered_set<Int> ignoredSet;
  std::copy(ignored.begin(), ignored.end(),
            std::inserter(ignoredSet, ignoredSet.end()));
  std::shuffle(indices.begin(), indices.end(), rng);

  const VarId violationId = engine->makeIntVar(0, 0, 2);
  AllDifferentExcept& invariant = engine->makeConstraint<AllDifferentExcept>(
      violationId, std::vector<VarId>(inputs), ignored);
  engine->close();

  EXPECT_EQ(engine->value(engine->currentTimestamp(), violationId),
            computeViolation(engine->currentTimestamp(), inputs, ignoredSet));

  for (const size_t i : indices) {
    Timestamp ts = engine->currentTimestamp() + Timestamp(i);
    for (size_t j = 0; j < numInputs; ++j) {
      // Check that we do not accidentally commit:
      ASSERT_EQ(engine->committedValue(inputs.at(j)), committedValues.at(j));
    }

    const Int oldVal = committedValues.at(i);
    do {
      engine->setValue(ts, inputs.at(i), valueDist(gen));
    } while (oldVal == engine->value(ts, inputs.at(i)));

    // notify changes
    invariant.notifyInputChanged(ts, *engine, LocalId(i));

    // incremental value
    const Int notifiedViolation = engine->value(ts, violationId);
    invariant.recompute(ts, *engine);

    ASSERT_EQ(notifiedViolation, engine->value(ts, violationId));

    engine->commitIf(ts, inputs.at(i));
    committedValues.at(i) = engine->value(ts, inputs.at(i));
    engine->commitIf(ts, violationId);

    invariant.commit(ts, *engine);
    invariant.recompute(ts + 1, *engine);
    ASSERT_EQ(notifiedViolation, engine->value(ts + 1, violationId));
  }
}

class MockAllDifferentExcept : public AllDifferentExcept {
 public:
  bool registered = false;
  void registerVars(Engine& engine) override {
    registered = true;
    AllDifferentExcept::registerVars(engine);
  }
  MockAllDifferentExcept(VarId violationId, std::vector<VarId> variables,
                         const std::vector<Int>& ignored)
      : AllDifferentExcept(violationId, variables, ignored) {
    ON_CALL(*this, recompute)
        .WillByDefault([this](Timestamp timestamp, Engine& engine) {
          return AllDifferentExcept::recompute(timestamp, engine);
        });
    ON_CALL(*this, nextInput)
        .WillByDefault([this](Timestamp t, Engine& engine) {
          return AllDifferentExcept::nextInput(t, engine);
        });
    ON_CALL(*this, notifyCurrentInputChanged)
        .WillByDefault([this](Timestamp t, Engine& engine) {
          AllDifferentExcept::notifyCurrentInputChanged(t, engine);
        });
    ON_CALL(*this, notifyInputChanged)
        .WillByDefault([this](Timestamp t, Engine& engine, LocalId id) {
          AllDifferentExcept::notifyInputChanged(t, engine, id);
        });
    ON_CALL(*this, commit).WillByDefault([this](Timestamp t, Engine& engine) {
      AllDifferentExcept::commit(t, engine);
    });
  }
  MOCK_METHOD(void, recompute, (Timestamp timestamp, Engine& engine),
              (override));
  MOCK_METHOD(VarId, nextInput, (Timestamp, Engine&), (override));
  MOCK_METHOD(void, notifyCurrentInputChanged, (Timestamp, Engine& engine),
              (override));
  MOCK_METHOD(void, notifyInputChanged,
              (Timestamp t, Engine& engine, LocalId id), (override));
  MOCK_METHOD(void, commit, (Timestamp timestamp, Engine& engine), (override));
};

TEST_F(AllDifferentExceptTest, EngineIntegration) {
  for (const auto& [propMode, markingMode] : propMarkModes) {
    if (!engine->isOpen()) {
      engine->open();
    }
    std::vector<VarId> args;
    const Int numArgs = 10;
    const Int lb = -100;
    const Int ub = 100;
    for (Int value = 0; value < numArgs; ++value) {
      args.emplace_back(engine->makeIntVar(0, lb, ub));
    }
    std::vector<Int> ignored(ub - lb, 0);
    for (size_t i = 0; i < ignored.size(); ++i) {
      ignored[i] = i - lb;
    }
    std::shuffle(ignored.begin(), ignored.end(), rng);
    const VarId viol = engine->makeIntVar(0, 0, numArgs);
    testNotifications<MockAllDifferentExcept>(
        &engine->makeInvariant<MockAllDifferentExcept>(viol, args, ignored),
        propMode, markingMode, numArgs + 1, args.front(), 1, viol);
  }
}

}  // namespace