#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <deque>
#include <random>
#include <vector>

#include "atlantis/invariantgraph/fzn/array_bool_xor.hpp"

namespace atlantis::testing {

using ::testing::AtLeast;
using ::testing::AtMost;

using namespace atlantis::invariantgraph;
using namespace atlantis::invariantgraph::fzn;

class array_bool_xorTest : public ::testing::Test {
 public:
  std::vector<VarNodeId> inputVarNodeIds{};
  Int numInputs = 3;

  void SetUp() override {}
};

}  // namespace atlantis::testing
