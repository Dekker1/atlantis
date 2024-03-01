#pragma once

#include <fznparser/constraint.hpp>
#include <fznparser/variables.hpp>

#include "atlantis/invariantgraph/fznInvariantGraph.hpp"

namespace atlantis::invariantgraph::fzn {

bool array_int_maximum(FznInvariantGraph&, const fznparser::IntArg& output,
                       const fznparser::IntVarArray& inputs);

bool array_int_maximum(FznInvariantGraph&, const fznparser::Constraint&);

}  // namespace atlantis::invariantgraph::fzn
