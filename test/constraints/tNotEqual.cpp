#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <random>
#include <vector>

#include "constraints/notEqual.hpp"
#include "core/propagationEngine.hpp"
#include "core/types.hpp"

using ::testing::AtLeast;
using ::testing::Return;

namespace {

class MockNotEqual : public NotEqual {
 public:
  bool initialized = false;

  void init(Timestamp timestamp, Engine& engine) override {
    initialized = true;
    NotEqual::init(timestamp, engine);
  }

  MockNotEqual(VarId violationId, VarId a, VarId b)
      : NotEqual(violationId, a, b) {
    ON_CALL(*this, recompute)
        .WillByDefault([this](Timestamp timestamp, Engine& engine) {
          return NotEqual::recompute(timestamp, engine);
        });
    ON_CALL(*this, nextInput)
        .WillByDefault([this](Timestamp t, Engine& engine) {
          return NotEqual::nextInput(t, engine);
        });

    ON_CALL(*this, notifyCurrentInputChanged)
        .WillByDefault([this](Timestamp t, Engine& engine) {
          NotEqual::notifyCurrentInputChanged(t, engine);
        });

    ON_CALL(*this, notifyInputChanged)
        .WillByDefault([this](Timestamp t, Engine& engine, LocalId id) {
          NotEqual::notifyInputChanged(t, engine, id);
        });

    ON_CALL(*this, commit).WillByDefault([this](Timestamp t, Engine& engine) {
      NotEqual::commit(t, engine);
    });
  }

  MOCK_METHOD(void, recompute, (Timestamp timestamp, Engine& engine),
              (override));

  MOCK_METHOD(VarId, nextInput, (Timestamp, Engine&), (override));
  MOCK_METHOD(void, notifyCurrentInputChanged, (Timestamp, Engine& engine),
              (override));

  MOCK_METHOD(void, notifyInputChanged, (Timestamp t, Engine& engine, LocalId id),
              (override));
  MOCK_METHOD(void, commit, (Timestamp timestamp, Engine& engine), (override));

 private:
};

class NotEqualTest : public ::testing::Test {
 protected:
  std::unique_ptr<PropagationEngine> engine;
  VarId violationId = NULL_ID;
  VarId x = NULL_ID;
  VarId y = NULL_ID;
  NotEqual* notEqual;
  std::mt19937 gen;

  void SetUp() override {
    std::random_device rd;
    gen = std::mt19937(rd());
    engine = std::make_unique<PropagationEngine>();
    engine->open();
    x = engine->makeIntVar(2, -100, 100);
    y = engine->makeIntVar(2, -100, 100);
    violationId = engine->makeIntVar(0, 0, 1);

    notEqual = &engine->makeConstraint<NotEqual>(violationId, x, y);
    engine->close();
  }

  void testNotifications(PropagationMode propMode) {
    engine->open();

    VarId a = engine->makeIntVar(5, -100, 100);
    VarId b = engine->makeIntVar(0, -100, 100);

    VarId viol = engine->makeIntVar(0, 0, 1);

    auto invariant = &engine->makeInvariant<MockNotEqual>(viol, a, b);

    EXPECT_TRUE(invariant->initialized);

    EXPECT_CALL(*invariant, recompute(testing::_, testing::_))
        .Times(AtLeast(1));

    EXPECT_CALL(*invariant, commit(testing::_, testing::_)).Times(AtLeast(1));

    engine->setPropagationMode(propMode);

    engine->close();

    if (engine->propagationMode() ==
        PropagationMode::INPUT_TO_OUTPUT) {
      EXPECT_CALL(*invariant, nextInput(testing::_, testing::_)).Times(0);
      EXPECT_CALL(*invariant, notifyCurrentInputChanged(testing::_, testing::_))
          .Times(0);
      EXPECT_CALL(*invariant,
                  notifyInputChanged(testing::_, testing::_, testing::_))
          .Times(1);
    } else {
      EXPECT_CALL(*invariant, nextInput(testing::_, testing::_)).Times(3);
      EXPECT_CALL(*invariant, notifyCurrentInputChanged(testing::_, testing::_))
          .Times(1);

      EXPECT_CALL(*invariant,
                  notifyInputChanged(testing::_, testing::_, testing::_))
          .Times(0);
    }

    engine->beginMove();
    engine->setValue(a, 0);
    engine->endMove();

    engine->beginProbe();
    engine->query(viol);
    engine->endProbe();
  }
};

/**
 *  Testing constructor
 */

TEST_F(NotEqualTest, Init) {
  EXPECT_EQ(engine->committedValue(violationId), 1);
  EXPECT_EQ(engine->value(engine->tmpTimestamp(violationId), violationId),
            1);
}

TEST_F(NotEqualTest, Recompute) {
  EXPECT_EQ(engine->value(0, violationId), 1);
  EXPECT_EQ(engine->committedValue(violationId), 1);

  Timestamp newTimestamp = 1;
  engine->setValue(newTimestamp, x, 40);
  notEqual->recompute(newTimestamp, *engine);
  EXPECT_EQ(engine->committedValue(violationId), 1);
  EXPECT_EQ(engine->value(newTimestamp, violationId), 0);
}

TEST_F(NotEqualTest, NotifyChange) {
  EXPECT_EQ(engine->value(0, violationId),
            1);

  LocalId unused = -1;

  Timestamp time1 = 1;

  EXPECT_EQ(engine->value(time1, x), 2);
  engine->setValue(time1, x, 40);
  EXPECT_EQ(engine->committedValue(x), 2);
  EXPECT_EQ(engine->value(time1, x), 40);
  notEqual->notifyInputChanged(time1, *engine, unused);
  EXPECT_EQ(engine->value(time1, violationId),
            0);  // incremental value of violationId is 0;

  engine->setValue(time1, y, 0);
  notEqual->notifyInputChanged(time1, *engine, unused);
  auto tmpValue = engine->value(
      time1, violationId);  // incremental value of violationId is 40;

  // Incremental computation gives the same result as recomputation
  notEqual->recompute(time1, *engine);
  EXPECT_EQ(engine->value(time1, violationId), tmpValue);

  Timestamp time2 = time1 + 1;

  EXPECT_EQ(engine->value(time2, y), 2);
  engine->setValue(time2, y, 20);
  EXPECT_EQ(engine->committedValue(y), 2);
  EXPECT_EQ(engine->value(time2, y), 20);
  notEqual->notifyInputChanged(time2, *engine, unused);
  EXPECT_EQ(engine->value(time2, violationId),
            0);  // incremental value of violationId is 0;
}

TEST_F(NotEqualTest, IncrementalVsRecompute) {
  EXPECT_EQ(engine->value(0, violationId),
            1);  // initially the value of violationId is 0
  LocalId unused = -1;
  // todo: not clear if we actually want to deal with overflows...
  std::uniform_int_distribution<> distribution(-100000, 100000);

  Timestamp currentTimestamp = 1;
  for (size_t i = 0; i < 1000; ++i) {
    ++currentTimestamp;
    // Check that we do not accidentally commit
    ASSERT_EQ(engine->committedValue(x), 2);
    ASSERT_EQ(engine->committedValue(y), 2);
    ASSERT_EQ(engine->committedValue(violationId),
              1);  // violationId is committed by register.

    // Set all variables
    engine->setValue(currentTimestamp, x, distribution(gen));
    engine->setValue(currentTimestamp, y, distribution(gen));

    // notify changes
    if (engine->committedValue(x) != engine->value(currentTimestamp, x)) {
      notEqual->notifyInputChanged(currentTimestamp, *engine, unused);
    }
    if (engine->committedValue(y) != engine->value(currentTimestamp, y)) {
      notEqual->notifyInputChanged(currentTimestamp, *engine, unused);
    }

    // incremental value
    auto tmp = engine->value(currentTimestamp, violationId);
    notEqual->recompute(currentTimestamp, *engine);

    ASSERT_EQ(tmp, engine->value(currentTimestamp, violationId));
  }
}

TEST_F(NotEqualTest, Commit) {
  EXPECT_EQ(engine->committedValue(violationId), 1);

  LocalId unused = -1;

  Timestamp currentTimestamp = 1;

  engine->setValue(currentTimestamp, x, 1);
  engine->setValue(currentTimestamp, y,
                   2);  // This change is not notified and should
                        // not have an impact on the commit

  notEqual->notifyInputChanged(currentTimestamp, *engine, unused);

  // Committing an invariant does not commit its output!
  // // Commit at wrong timestamp should have no impact
  // equal->commit(currentTimestamp + 1, *engine);
  // EXPECT_EQ(engine->committedValue(violationId), 0);
  // equal->commit(currentTimestamp, *engine);
  // EXPECT_EQ(engine->committedValue(violationId), 38);
}

TEST_F(NotEqualTest, CreateNotEqual) {
  engine->open();

  VarId a = engine->makeIntVar(5, -100, 100);
  VarId b = engine->makeIntVar(0, -100, 100);

  VarId viol = engine->makeIntVar(0, 0, 1);

  auto invariant = &engine->makeInvariant<MockNotEqual>(viol, a, b);

  EXPECT_TRUE(invariant->initialized);

  EXPECT_CALL(*invariant, recompute(testing::_, testing::_)).Times(AtLeast(1));

  EXPECT_CALL(*invariant, commit(testing::_, testing::_)).Times(AtLeast(1));

  engine->close();

  EXPECT_EQ(engine->currentValue(viol), 0);
}

TEST_F(NotEqualTest, NotificationsInputToOutput) {
  testNotifications(PropagationMode::INPUT_TO_OUTPUT);
}

TEST_F(NotEqualTest, NotificationsOutputToInput) {
  testNotifications(PropagationMode::OUTPUT_TO_INPUT);
}

TEST_F(NotEqualTest, NotificationsMixed) {
  testNotifications(PropagationMode::OUTPUT_TO_INPUT);
}

}  // namespace