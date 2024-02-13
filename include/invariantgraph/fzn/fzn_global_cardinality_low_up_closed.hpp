#pragma once

#include <fznparser/constraint.hpp>
#include <fznparser/variables.hpp>

#include "invariantgraph/fzn/array_bool_and.hpp"
#include "invariantgraph/fzn/set_in.hpp"
#include "invariantgraph/fznInvariantGraph.hpp"
#include "invariantgraph/types.hpp"
#include "invariantgraph/violationInvariantNodes/globalCardinalityLowUpNode.hpp"

namespace atlantis::invariantgraph::fzn {

bool fzn_global_cardinality_low_up_closed(FznInvariantGraph&,
                                          const fznparser::IntVarArray& inputs,
                                          std::vector<Int>&& cover,
                                          std::vector<Int>&& low,
                                          std::vector<Int>&& up);

bool fzn_global_cardinality_low_up_closed(FznInvariantGraph&,
                                          const fznparser::IntVarArray& inputs,
                                          std::vector<Int>&& cover,
                                          std::vector<Int>&& low,
                                          std::vector<Int>&& up,
                                          const fznparser::BoolArg& reified);

bool fzn_global_cardinality_low_up_closed(FznInvariantGraph&,
                                          const fznparser::Constraint&);

}  // namespace atlantis::invariantgraph::fzn