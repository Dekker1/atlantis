#pragma once

#include "search/annealer.hpp"
#include "search/move.hpp"

namespace search::neighbourhoods {

class Neighbourhood {
 public:
  virtual ~Neighbourhood() = default;

  /**
   * Initialise an assignment.
   *
   * @param random The source of randomness.
   * @param modifications The modifications to the assignment.
   */
  virtual void initialise(RandomProvider& random,
                          AssignmentModifier& modifications) = 0;

  /**
   * Make a random move on @p assignment. After a move is constructed, the
   * decision whether to apply it is taken by @p annealer.
   *
   * @param random The source of randomness.
   * @param assignment The assignment to move on.
   * @param annealer The annealer which decides whether to accept the move.
   * @return True if a move was committed, false otherwise.
   */
  virtual bool randomMove(RandomProvider& random, Assignment& assignment,
                          Annealer& annealer) = 0;

 protected:
  template <unsigned int N>
  bool maybeCommit(Move<N> move, Assignment& assignment, Annealer& annealer) {
    if (annealer.acceptMove(move)) {
      move.commit(assignment);
      return true;
    }

    return false;
  }
};

}  // namespace search::neighbourhoods