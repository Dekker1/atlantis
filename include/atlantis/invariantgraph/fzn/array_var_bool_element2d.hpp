#pragma once

#include <fznparser/constraint.hpp>
#include <fznparser/variables.hpp>

#include "atlantis/invariantgraph/fznInvariantGraph.hpp"

namespace atlantis::invariantgraph::fzn {

bool array_var_bool_element2d(
    FznInvariantGraph&, const fznparser::IntArg& idx1,
    const fznparser::IntArg& idx2,
    const std::shared_ptr<fznparser::BoolVarArray>& inputs,
    const fznparser::BoolArg& output, Int numRows, Int offset1, Int offset2);

bool array_var_bool_element2d(FznInvariantGraph&, const fznparser::Constraint&);

}  // namespace atlantis::invariantgraph::fzn
