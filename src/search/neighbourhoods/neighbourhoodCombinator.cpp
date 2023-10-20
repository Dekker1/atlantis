#include "search/neighbourhoods/neighbourhoodCombinator.hpp"

#include <typeinfo>

#include "utils/type.hpp"

namespace search::neighbourhoods {

NeighbourhoodCombinator::NeighbourhoodCombinator(
    std::vector<std::shared_ptr<Neighbourhood>>&& neighbourhoods)
    : _neighbourhoods(std::move(neighbourhoods)) {
  assert(!_neighbourhoods.empty());
  size_t num_vars = 0;
  for (const auto& neighbourhood : _neighbourhoods) {
    num_vars += neighbourhood->coveredVariables().size();
  }
  _variables.reserve(num_vars);

  std::vector<size_t> weights;
  weights.reserve(_neighbourhoods.size());
  for (const auto& neighbourhood : _neighbourhoods) {
    weights.push_back(neighbourhood->coveredVariables().size());

    for (const auto& searchVar : neighbourhood->coveredVariables()) {
      _variables.emplace_back(searchVar);
    }
  }

  _neighbourhoodDistribution =
      std::discrete_distribution<size_t>{weights.begin(), weights.end()};
}

void NeighbourhoodCombinator::initialise(RandomProvider& random,
                                         AssignmentModifier& modifications) {
  for (const auto& neighbourhood : _neighbourhoods) {
    neighbourhood->initialise(random, modifications);
  }
}

bool NeighbourhoodCombinator::randomMove(RandomProvider& random,
                                         Assignment& assignment,
                                         Annealer& annealer) {
  auto& neighbourhood = selectNeighbourhood(random);
  return neighbourhood.randomMove(random, assignment, annealer);
}

void NeighbourhoodCombinator::printNeighbourhood(logging::Logger& logger) {
  for (const auto& neighbourhood : _neighbourhoods) {
    logger.debug("Neighbourhood {} covers {} variables.",
                 demangle(typeid(*neighbourhood).name()),
                 neighbourhood->coveredVariables().size());
  }
}

Neighbourhood& NeighbourhoodCombinator::selectNeighbourhood(
    RandomProvider& random) {
  auto idx = random.fromDistribution<size_t>(_neighbourhoodDistribution);
  return *_neighbourhoods[idx];
}

}  // namespace search::neighbourhoods