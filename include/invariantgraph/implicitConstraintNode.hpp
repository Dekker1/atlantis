#pragma once

#include <cassert>
#include <fznparser/ast.hpp>
#include <vector>

#include "core/engine.hpp"
#include "invariantgraph/variableDefiningNode.hpp"
#include "invariantgraph/variableNode.hpp"
#include "search/neighbourhoods/neighbourhood.hpp"

namespace invariantgraph {

/**
 * Serves as a marker for the invariant graph to start the application to the
 * propagation engine.
 */
class ImplicitConstraintNode : public VariableDefiningNode {
 private:
  search::neighbourhoods::Neighbourhood* _neighbourhood{nullptr};

 public:
  explicit ImplicitConstraintNode(std::vector<VariableNode*> definedVariables)
      : VariableDefiningNode(std::move(definedVariables)) {}

  ~ImplicitConstraintNode() override { delete _neighbourhood; }

  void createDefinedVariables(Engine& engine) override;

  void registerWithEngine(Engine& engine) override;

  /**
   * Take the neighbourhood which is constructed in the registerWithEngine
   * call out of this instance. Note, this transfers ownership (as indicated
   * by the usage of unique_ptr).
   *
   * Calling this method before calling registerWithEngine will return a
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
  [[nodiscard]] std::unique_ptr<search::neighbourhoods::Neighbourhood>
  takeNeighbourhood() noexcept {
    auto ptr =
        std::unique_ptr<search::neighbourhoods::Neighbourhood>(_neighbourhood);
    _neighbourhood = nullptr;
    return ptr;
  }

 protected:
  virtual search::neighbourhoods::Neighbourhood* createNeighbourhood(
      Engine& engine, std::vector<search::SearchVariable> variables) = 0;
};
}  // namespace invariantgraph