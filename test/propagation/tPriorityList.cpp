#include <gtest/gtest.h>

#include <limits>
#include <random>
#include <vector>

#include "atlantis/propagation/utils/priorityList.hpp"

namespace atlantis::testing {

using namespace atlantis::propagation;

class PriorityListTest : public ::testing::Test {
 protected:
  void SetUp() override {
    std::random_device rd;
    gen = std::mt19937(rd());
  }
  std::mt19937 gen;

  static void updateForward(Timestamp ts, PriorityList &priorityList) {
    updateForward(ts, priorityList, 0);
  }
  static void updateForward(Timestamp ts, PriorityList &priorityList,
                            Int offset) {
    for (size_t idx = 0; idx < priorityList.size(); ++idx) {
      priorityList.updatePriority(ts, idx, static_cast<Int>(idx) + 1 + offset);
    }
  }

  static void updateBackwards(Timestamp ts, PriorityList &priorityList) {
    updateBackwards(ts, priorityList, 0);
  }
  static void updateBackwards(Timestamp ts, PriorityList &priorityList,
                              Int offset) {
    for (size_t idx = 0; idx < priorityList.size(); ++idx) {
      priorityList.updatePriority(
          ts, idx, static_cast<Int>(priorityList.size() - idx) + offset);
    }
  }

  static void updateUniform(Timestamp ts, PriorityList &priorityList) {
    for (size_t idx = 0; idx < priorityList.size(); ++idx) {
      priorityList.updatePriority(ts, idx, Int(ts));
    }
  }
};

/**
 *  Testing constructor
 */

TEST_F(PriorityListTest, Constructor) {
  for (size_t size = 0; size < 100; ++size) {
    PriorityList priorityList(size);
    EXPECT_EQ(priorityList.size(), size);
  }
}

TEST_F(PriorityListTest, SimpleUpdatePriority) {
  size_t size = 100;
  Timestamp ts;
  PriorityList priorityList(size);

  for (ts = 1; ts < 10; ++ts) {
    updateForward(ts, priorityList);
    EXPECT_EQ(priorityList.minPriority(ts), 1);
    EXPECT_EQ(priorityList.maxPriority(ts), 100);
  }
  for (ts = 1; ts < 10; ++ts) {
    updateBackwards(ts, priorityList);
    EXPECT_EQ(priorityList.minPriority(ts), 1);
    EXPECT_EQ(priorityList.maxPriority(ts), 100);
  }
  for (ts = 1; ts < 10; ++ts) {
    updateUniform(ts, priorityList);
    EXPECT_EQ(priorityList.minPriority(ts), Int(ts));
    EXPECT_EQ(priorityList.maxPriority(ts), Int(ts));
  }

  for (ts = 1; ts < 10; ++ts) {
    updateForward(ts, priorityList);
    EXPECT_EQ(priorityList.minPriority(ts), 1);
    EXPECT_EQ(priorityList.maxPriority(ts), 100);

    updateBackwards(ts, priorityList);
    EXPECT_EQ(priorityList.minPriority(ts), 1);
    EXPECT_EQ(priorityList.maxPriority(ts), 100);

    updateUniform(ts, priorityList);
    EXPECT_EQ(priorityList.minPriority(ts), Int(ts));
    EXPECT_EQ(priorityList.maxPriority(ts), Int(ts));
  }
}

TEST_F(PriorityListTest, RandomUpdatePriority) {
  for (size_t n = 0; n < 1000; ++n) {
    size_t size = 100;
    Timestamp ts = 1;
    std::uniform_int_distribution<> distribution(
        std::numeric_limits<int>::min(), std::numeric_limits<int>::max());

    PriorityList priorityList(size);
    Int minPriority = std::numeric_limits<int>::max();
    Int maxPriority = std::numeric_limits<int>::min();
    for (size_t idx = 0; idx < 100; ++idx) {
      Int newValue = distribution(gen);
      minPriority = std::min(newValue, minPriority);
      maxPriority = std::max(newValue, maxPriority);
      priorityList.updatePriority(ts, idx, newValue);
    }

    EXPECT_EQ(priorityList.minPriority(ts), minPriority);
    EXPECT_EQ(priorityList.maxPriority(ts), maxPriority);
  }
}

TEST_F(PriorityListTest, CommitIf) {
  size_t size = 100;
  PriorityList priorityList(size);
  Timestamp ts = 1;

  updateForward(ts, priorityList, Int(ts));
  priorityList.commitIf(ts);
  EXPECT_EQ(priorityList.minPriority(ts), 1 + Int(ts));
  EXPECT_EQ(priorityList.maxPriority(ts), 100 + Int(ts));
  EXPECT_EQ(priorityList.minPriority(ts + 1), 1 + Int(ts));
  EXPECT_EQ(priorityList.maxPriority(ts + 1), 100 + Int(ts));

  for (ts = 2; ts < 10; ++ts) {
    updateForward(ts, priorityList, Int(ts));
    EXPECT_EQ(priorityList.minPriority(ts), 1 + Int(ts));
    EXPECT_EQ(priorityList.maxPriority(ts), 100 + Int(ts));
    priorityList.commitIf(ts);
    EXPECT_EQ(priorityList.minPriority(ts + 1), 1 + Int(ts));
    EXPECT_EQ(priorityList.maxPriority(ts + 1), 100 + Int(ts));
  }
}

}  // namespace atlantis::testing
