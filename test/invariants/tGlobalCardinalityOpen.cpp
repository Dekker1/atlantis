#include <gmock/gmock.h>
#include <gtest/gtest.h>
#include <rapidcheck/gtest.h>

#include <algorithm>
#include <random>
#include <vector>

#include "../testHelper.hpp"
#include "core/propagationEngine.hpp"
#include "core/types.hpp"
#include "invariants/globalCardinalityOpen.hpp"

namespace {

class GlobalCardinalityOpenTest : public InvariantTest {
 public:
  std::vector<Int> computeOutputs(const Timestamp ts,
                                  const std::vector<VarId>& inputs,
                                  const std::vector<Int>& cover) {
    std::vector<Int> values(inputs.size(), 0);
    for (size_t i = 0; i < inputs.size(); ++i) {
      values.at(i) = engine->value(ts, inputs.at(i));
    }
    return computeOutputs(values, cover);
  }

  std::vector<Int> computeOutputs(const std::vector<Int>& values,
                                  const std::vector<Int>& cover) {
    std::unordered_map<Int, size_t> coverToIndex;
    for (size_t i = 0; i < cover.size(); ++i) {
      coverToIndex.emplace(cover.at(i), i);
    }

    std::vector<Int> counts(cover.size(), 0);
    for (const Int val : values) {
      if (coverToIndex.contains(val)) {
        ++counts.at(coverToIndex.at(val));
      }
    }
    return counts;
  }
};

TEST_F(GlobalCardinalityOpenTest, UpdateBounds) {
  const Int lb = 0;
  const Int ub = 2;
  engine->open();
  std::vector<VarId> inputs{engine->makeIntVar(0, 0, 2),
                            engine->makeIntVar(0, 0, 2),
                            engine->makeIntVar(0, 0, 2)};

  std::vector<VarId> outputs{engine->makeIntVar(0, 0, 2),
                             engine->makeIntVar(0, 0, 2)};

  GlobalCardinalityOpen& invariant =
      engine->makeInvariant<GlobalCardinalityOpen>(
          inputs, std::vector<Int>{0, 2}, std::vector<VarId>{outputs});
  engine->close();
  for (const VarId output : outputs) {
    EXPECT_EQ(engine->lowerBound(output), 0);
  }

  for (Int aVal = lb; aVal <= ub; ++aVal) {
    engine->setValue(engine->currentTimestamp(), inputs.at(0), aVal);
    for (Int bVal = lb; bVal <= ub; ++bVal) {
      engine->setValue(engine->currentTimestamp(), inputs.at(1), bVal);
      for (Int cVal = lb; cVal <= ub; ++cVal) {
        engine->setValue(engine->currentTimestamp(), inputs.at(2), cVal);
        invariant.compute(engine->currentTimestamp(), *engine);
        for (const VarId output : outputs) {
          EXPECT_GE(engine->value(engine->currentTimestamp(), output), 0);
          EXPECT_LE(engine->value(engine->currentTimestamp(), output),
                    inputs.size());
        }
      }
    }
  }
}

TEST_F(GlobalCardinalityOpenTest, Recompute) {
  std::vector<std::pair<Int, Int>> boundVec{
      {-10004, -10000}, {-2, 2}, {10000, 10002}};

  std::vector<std::vector<Int>> coverVec{{std::vector<Int>{-10003, -10002}},
                                         {std::vector<Int>{-2, 2}},
                                         {std::vector<Int>{10000, 10002}}};

  for (size_t i = 0; i < boundVec.size(); ++i) {
    auto const [lb, ub] = boundVec[i];
    auto const cover = coverVec[i];
    EXPECT_TRUE(lb <= ub);

    std::unordered_set<Int> coverSet;
    for (const Int c : cover) {
      coverSet.emplace(c);
    }

    engine->open();
    const VarId a = engine->makeIntVar(lb, lb, ub);
    const VarId b = engine->makeIntVar(lb, lb, ub);
    const VarId c = engine->makeIntVar(lb, lb, ub);
    std::vector<VarId> outputs;
    for (size_t j = 0; j < cover.size(); ++j) {
      outputs.emplace_back(engine->makeIntVar(0, 0, 0));
    }

    GlobalCardinalityOpen& invariant =
        engine->makeInvariant<GlobalCardinalityOpen>(
            std::vector<VarId>{a, b, c}, cover, outputs);
    engine->close();

    const std::vector<VarId> inputs{a, b, c};

    for (Int aVal = lb; aVal <= ub; ++aVal) {
      for (Int bVal = lb; bVal <= ub; ++bVal) {
        for (Int cVal = lb; cVal <= ub; ++cVal) {
          engine->setValue(engine->currentTimestamp(), a, aVal);
          engine->setValue(engine->currentTimestamp(), b, bVal);
          engine->setValue(engine->currentTimestamp(), c, cVal);
          const auto expectedCounts =
              computeOutputs(engine->currentTimestamp(), inputs, cover);
          EXPECT_EQ(expectedCounts.size(), cover.size());
          invariant.recompute(engine->currentTimestamp(), *engine);
          for (size_t j = 0; j < outputs.size(); ++j) {
            EXPECT_EQ(expectedCounts.at(j),
                      engine->value(engine->currentTimestamp(), outputs.at(j)));
          }
        }
      }
    }
  }
}

TEST_F(GlobalCardinalityOpenTest, NotifyInputChanged) {
  std::vector<std::pair<Int, Int>> boundVec{
      {-10002, -10000}, {-1, 1}, {10000, 10002}};

  std::vector<std::vector<Int>> coverVec{{std::vector<Int>{-10003, -10002}},
                                         {std::vector<Int>{-2, 2}},
                                         {std::vector<Int>{10000, 10002}}};

  for (size_t i = 0; i < boundVec.size(); ++i) {
    auto const [lb, ub] = boundVec[i];
    auto const cover = coverVec[i];
    EXPECT_TRUE(lb <= ub);

    engine->open();
    std::vector<VarId> inputs{engine->makeIntVar(lb, lb, ub),
                              engine->makeIntVar(lb, lb, ub),
                              engine->makeIntVar(lb, lb, ub)};

    std::vector<VarId> outputs;
    for (size_t j = 0; j < cover.size(); ++j) {
      outputs.emplace_back(engine->makeIntVar(0, 0, 0));
    }

    GlobalCardinalityOpen& invariant =
        engine->makeInvariant<GlobalCardinalityOpen>(inputs, cover, outputs);
    engine->close();

    for (Int val = lb; val <= ub; ++val) {
      for (size_t j = 0; j < inputs.size(); ++j) {
        engine->setValue(engine->currentTimestamp(), inputs[j], val);
        const auto expectedCounts =
            computeOutputs(engine->currentTimestamp(), inputs, cover);

        invariant.notifyInputChanged(engine->currentTimestamp(), *engine,
                                     LocalId(j));
        for (size_t k = 0; k < outputs.size(); ++k) {
          EXPECT_EQ(expectedCounts.at(k),
                    engine->value(engine->currentTimestamp(), outputs.at(k)));
        }
      }
    }
  }
}

TEST_F(GlobalCardinalityOpenTest, NextInput) {
  const size_t numInputs = 1000;
  const Int lb = 0;
  const Int ub = numInputs - 1;
  const size_t numOutputs = 10;
  EXPECT_TRUE(lb <= ub);

  engine->open();
  std::vector<size_t> indices;
  std::vector<Int> committedValues;
  std::vector<VarId> inputs;
  for (size_t i = 0; i < numInputs; ++i) {
    inputs.emplace_back(engine->makeIntVar(i, lb, ub));
  }
  std::vector<Int> cover;
  std::vector<VarId> outputs;
  for (size_t i = 0; i < numOutputs; ++i) {
    cover.emplace_back(i);
    outputs.emplace_back(engine->makeIntVar(0, 0, numInputs));
  }

  const VarId minVarId = *std::min_element(inputs.begin(), inputs.end());
  const VarId maxVarId = *std::max_element(inputs.begin(), inputs.end());

  std::shuffle(inputs.begin(), inputs.end(), rng);

  GlobalCardinalityOpen& invariant =
      engine->makeInvariant<GlobalCardinalityOpen>(inputs, cover, outputs);
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

TEST_F(GlobalCardinalityOpenTest, NotifyCurrentInputChanged) {
  const size_t numInputs = 100;
  const size_t numOutputs = 10;
  const Int lb = -10;
  const Int ub = 10;
  EXPECT_TRUE(lb <= ub);

  engine->open();
  std::uniform_int_distribution<Int> valueDist(lb, ub);
  std::vector<VarId> inputs;
  for (size_t i = 0; i < numInputs; ++i) {
    inputs.emplace_back(engine->makeIntVar(valueDist(gen), lb, ub));
  }
  std::vector<Int> cover;
  std::vector<VarId> outputs;
  for (size_t i = 0; i < numOutputs; ++i) {
    cover.emplace_back(i);
    outputs.emplace_back(engine->makeIntVar(0, 0, numInputs));
  }

  GlobalCardinalityOpen& invariant =
      engine->makeInvariant<GlobalCardinalityOpen>(inputs, cover, outputs);
  engine->close();

  for (Timestamp ts = engine->currentTimestamp() + 1;
       ts < engine->currentTimestamp() + 4; ++ts) {
    for (const VarId varId : inputs) {
      EXPECT_EQ(invariant.nextInput(ts, *engine), varId);
      const Int oldVal = engine->value(ts, varId);
      do {
        engine->setValue(ts, varId, valueDist(gen));
      } while (engine->value(ts, varId) == oldVal);
      const auto expectedCounts = computeOutputs(ts, inputs, cover);

      invariant.notifyCurrentInputChanged(ts, *engine);
      for (size_t i = 0; i < outputs.size(); ++i) {
        EXPECT_EQ(expectedCounts.at(i), engine->value(ts, outputs.at(i)));
      }
    }
  }
}

TEST_F(GlobalCardinalityOpenTest, Commit) {
  const Int lb = -10;
  const Int ub = 10;
  EXPECT_TRUE(lb <= ub);

  const size_t numInputs = 1000;
  const size_t numOutputs = 15;
  std::vector<Int> cover(ub - lb + 1);
  std::iota(cover.begin(), cover.end(), lb);
  std::shuffle(cover.begin(), cover.end(), std::default_random_engine{});
  cover.resize(numOutputs);

  std::uniform_int_distribution<Int> valueDist(lb, ub);
  std::vector<size_t> indices;
  std::vector<Int> committedValues;
  std::vector<VarId> inputs;

  engine->open();
  for (size_t i = 0; i < numInputs; ++i) {
    indices.emplace_back(i);
    committedValues.emplace_back(valueDist(gen));
    inputs.emplace_back(engine->makeIntVar(committedValues.back(), lb, ub));
  }

  std::vector<VarId> outputs;
  for (size_t i = 0; i < numOutputs; ++i) {
    outputs.emplace_back(engine->makeIntVar(0, 0, 0));
  }

  std::shuffle(indices.begin(), indices.end(), rng);

  GlobalCardinalityOpen& invariant =
      engine->makeInvariant<GlobalCardinalityOpen>(inputs, cover, outputs);
  engine->close();

  std::vector<Int> notifiedOutputValues(numOutputs, -1);

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
    for (size_t j = 0; j < outputs.size(); ++j) {
      notifiedOutputValues.at(j) = engine->value(ts, outputs.at(j));
    }
    invariant.recompute(ts, *engine);

    for (size_t j = 0; j < outputs.size(); ++j) {
      ASSERT_EQ(notifiedOutputValues.at(j), engine->value(ts, outputs.at(j)));
    }

    engine->commitIf(ts, inputs.at(i));
    committedValues.at(i) = engine->value(ts, inputs.at(i));
    for (const VarId o : outputs) {
      engine->commitIf(ts, o);
    }

    invariant.commit(ts, *engine);
    invariant.recompute(ts + 1, *engine);
    for (size_t j = 0; j < outputs.size(); ++j) {
      ASSERT_EQ(notifiedOutputValues.at(j),
                engine->value(ts + 1, outputs.at(j)));
    }
  }
}

RC_GTEST_FIXTURE_PROP(GlobalCardinalityOpenTest, RapidCheck,
                      (unsigned char nInputs, int valOffset,
                       unsigned char nOutputs)) {
  size_t numInputs = static_cast<size_t>(nInputs) + static_cast<size_t>(2);
  size_t numOutputs = static_cast<size_t>(nOutputs) + static_cast<size_t>(1);

  Int valLb = static_cast<Int>(valOffset - numInputs);
  Int valUb = static_cast<Int>(valOffset + numInputs);

  std::random_device rd;
  std::vector<Int> cover(
      std::max(numOutputs, static_cast<size_t>(valUb - valLb + 1)));
  std::iota(cover.begin(), cover.end(), valLb);
  std::shuffle(cover.begin(), cover.end(), std::default_random_engine{});
  cover.resize(numOutputs);

  auto valDistribution = std::uniform_int_distribution<Int>{valLb, valUb};
  auto valGen = std::mt19937(rd());

  std::vector<VarId> inputs;
  engine->open();

  for (size_t i = 0; i < numInputs; i++) {
    inputs.emplace_back(
        engine->makeIntVar(valDistribution(valGen), valLb, valUb));
  }

  std::vector<VarId> outputs;
  for (size_t i = 0; i < numOutputs; ++i) {
    outputs.emplace_back(engine->makeIntVar(0, 0, inputs.size()));
  }

  RC_ASSERT(outputs.size() == numOutputs);

  engine->makeInvariant<GlobalCardinalityOpen>(inputs, cover, outputs);

  engine->close();

  for (auto [propMode, markMode] : propMarkModes) {
    for (size_t iter = 0; iter < 3; ++iter) {
      engine->open();
      engine->setPropagationMode(propMode);
      engine->setOutputToInputMarkingMode(markMode);
      engine->close();

      engine->beginMove();
      for (const VarId x : inputs) {
        engine->setValue(x, valDistribution(valGen));
      }
      engine->endMove();

      engine->beginProbe();
      for (const VarId output : outputs) {
        engine->query(output);
      }
      engine->endProbe();

      auto actualCounts =
          computeOutputs(engine->currentTimestamp(), inputs, cover);

      for (size_t i = 0; i < outputs.size(); ++i) {
        RC_ASSERT(actualCounts.at(i) == engine->currentValue(outputs.at(i)));
      }
    }
  }
}

class MockGlobalCardinalityClosed : public GlobalCardinalityOpen {
 public:
  bool registered = false;
  void registerVars(Engine& engine) override {
    registered = true;
    GlobalCardinalityOpen::registerVars(engine);
  }
  MockGlobalCardinalityClosed(std::vector<VarId>&& inputs,
                              std::vector<Int>&& cover,
                              std::vector<VarId>&& outputs)
      : GlobalCardinalityOpen(std::vector<VarId>{inputs},
                              std::vector<Int>{cover},
                              std::vector<VarId>{outputs}) {
    ON_CALL(*this, recompute)
        .WillByDefault([this](Timestamp timestamp, Engine& engine) {
          return GlobalCardinalityOpen::recompute(timestamp, engine);
        });
    ON_CALL(*this, nextInput)
        .WillByDefault([this](Timestamp timestamp, Engine& engine) {
          return GlobalCardinalityOpen::nextInput(timestamp, engine);
        });
    ON_CALL(*this, notifyCurrentInputChanged)
        .WillByDefault([this](Timestamp timestamp, Engine& engine) {
          GlobalCardinalityOpen::notifyCurrentInputChanged(timestamp, engine);
        });
    ON_CALL(*this, notifyInputChanged)
        .WillByDefault([this](Timestamp timestamp, Engine& engine,
                              LocalId localId) {
          GlobalCardinalityOpen::notifyInputChanged(timestamp, engine, localId);
        });
    ON_CALL(*this, commit)
        .WillByDefault([this](Timestamp timestamp, Engine& engine) {
          GlobalCardinalityOpen::commit(timestamp, engine);
        });
  }
  MOCK_METHOD(void, recompute, (Timestamp timestamp, Engine& engine),
              (override));
  MOCK_METHOD(VarId, nextInput, (Timestamp, Engine&), (override));
  MOCK_METHOD(void, notifyCurrentInputChanged, (Timestamp, Engine& engine),
              (override));
  MOCK_METHOD(void, notifyInputChanged,
              (Timestamp timestamp, Engine& engine, LocalId localId),
              (override));
  MOCK_METHOD(void, commit, (Timestamp timestamp, Engine& engine), (override));
};
TEST_F(GlobalCardinalityOpenTest, EngineIntegration) {
  for (const auto& [propMode, markingMode] : propMarkModes) {
    if (!engine->isOpen()) {
      engine->open();
    }
    const Int numInputs = 10;

    std::vector<VarId> inputs;
    for (Int value = 0; value < numInputs; ++value) {
      inputs.push_back(engine->makeIntVar(0, -100, 100));
    }
    std::vector<Int> cover{1, 2, 3};
    std::vector<VarId> outputs;
    for (size_t i = 0; i < cover.size(); ++i) {
      outputs.push_back(engine->makeIntVar(0, 0, numInputs));
    }

    testNotifications<MockGlobalCardinalityClosed>(
        &engine->makeInvariant<MockGlobalCardinalityClosed>(
            std::vector<VarId>{inputs}, std::vector<Int>{cover},
            std::vector<VarId>{outputs}),
        propMode, markingMode, numInputs + 1, inputs.front(), 1,
        outputs.front());
  }
}

}  // namespace