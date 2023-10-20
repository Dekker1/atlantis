#pragma once

#include <cassert>
#include <vector>

#include "core/engine.hpp"
#include "invariantgraph/invariantNode.hpp"
#include "invariantgraph/varNode.hpp"
#include "search/neighbourhoods/neighbourhood.hpp"

namespace invariantgraph {

class InvariantGraph;  // Forward declaration

/**
 * Serves as a marker for the invariant graph to start the application to the
 * propagation engine.
 */
class ImplicitConstraintNode : public InvariantNode {
 private:
  std::shared_ptr<search::neighbourhoods::Neighbourhood> _neighbourhood{
      nullptr};

 public:
  explicit ImplicitConstraintNode(std::vector<VarNodeId>&& outputVarNodeIds);

  void registerOutputVariables(InvariantGraph&, Engine& engine) override;

  void registerNode(InvariantGraph&, Engine& engine) override;

  /**
   * Take the neighbourhood which is constructed in the registerNode
   * call out of this instance. Note, this transfers ownership (as indicated
   * by the usage of unique_ptr).
   *
   * Calling this method before calling registerNode will return a
   * nullptr. The same holds if this method is called multiple times. Only
   * the first call will return a neighbourhood instance.
   *
   * The reason this does not return a reference, is because we want to be
   * able to delete the entire invariant graph after it has been applied to
   * the propagation engine. If a reference was returned here, that would
   * leave the reference dangling.
   *
   * @return The neighbourhood corresponding to this implicit constraint.
   */
  [[nodiscard]] std::shared_ptr<search::neighbourhoods::Neighbourhood>
  neighbourhood() noexcept;

 protected:
  virtual std::shared_ptr<search::neighbourhoods::Neighbourhood>
  createNeighbourhood(Engine& engine,
                      std::vector<search::SearchVariable>&& variables) = 0;
};
}  // namespace invariantgraph