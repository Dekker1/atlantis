#include "variables/intVar.hpp"

#include <iostream>
#include <stdexcept>

IntVar::IntVar(Int lowerBound, Int upperBound)
    : IntVar(NULL_ID, lowerBound, upperBound) {}

IntVar::IntVar(VarId id, Int lowerBound, Int upperBound)
    : IntVar(id, 0, lowerBound, upperBound) {}

IntVar::IntVar(VarId id, Int initValue, Int lowerBound, Int upperBound)
    : IntVar(NULL_TIMESTAMP, id, initValue, lowerBound, upperBound) {}

IntVar::IntVar(Timestamp t, VarId id, Int initValue, Int lowerBound,
               Int upperBound)
    : Var(id),
      _value(t, initValue),  // todo: We need both a time-zero (when
                             // initialisation happens) but also a dummy time.
      _lowerBound(lowerBound),
      _upperBound(upperBound) {
  if (lowerBound > upperBound) {
    throw std::out_of_range(
        "Lower bound must be smaller than or equal to upper bound");
  }
}

void IntVar::updateDomain(Int lowerBound, Int upperBound) {
  if (lowerBound > upperBound) {
    throw std::out_of_range(
        "Lower bound must be smaller than or equal to upper bound");
  }
  _lowerBound = lowerBound;
  _upperBound = upperBound;
}

std::ostream& operator<<(std::ostream& out, IntVar const& var) {
  out << "IntVar(id: " << var._id.id;
  out << ",c: " << var._value.getCommittedValue();
  out << ",t: " << var._value.getValue(var._value.getTmpTimestamp());
  out << ",ts: " << var._value.getTmpTimestamp();
  out << ")";
  return out;
}