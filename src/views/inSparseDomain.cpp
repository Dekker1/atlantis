#include "views/inSparseDomain.hpp"

#include "core/engine.hpp"

InSparseDomain::InSparseDomain(VarId parentId,
                               const std::vector<DomainEntry>& domain)
    : IntView(parentId), _offset(domain.front().lowerBound) {
#ifndef NDEBUG
  assert(domain.size() > 0);
  for (const auto& domEntry : domain) {
    assert(domEntry.lowerBound <= domEntry.upperBound);
  }
  for (size_t i = 1; i < domain.size(); ++i) {
    assert(domain[i - 1].upperBound < domain[i].lowerBound);
  }
#endif
  _valueViolation.resize(domain.back().upperBound - _offset + 1, 0);
  for (size_t i = 1; i < domain.size(); ++i) {
    for (Int val = domain[i - 1].upperBound + 1; val < domain[i].lowerBound;
         ++val) {
      _valueViolation[val - _offset] =
          std::min(val - domain[i - 1].upperBound, domain[i].lowerBound - val);
    }
  }
}

Int InSparseDomain::value(Timestamp ts) {
  const Int val = _engine->value(ts, _parentId);
  if (val < _offset) {
    return _offset - val;
  }
  if (val >= _offset + static_cast<Int>(_valueViolation.size())) {
    return val - _offset - _valueViolation.size() + 1;
  }
  return _valueViolation[val - _offset];
}

Int InSparseDomain::committedValue() {
  const Int val = _engine->committedValue(_parentId);
  if (val < _offset) {
    return _offset - val;
  }
  if (val >= _offset + static_cast<Int>(_valueViolation.size())) {
    return val - _offset - _valueViolation.size() + 1;
  }
  return _valueViolation[val - _offset];
}

Int InSparseDomain::lowerBound() const {
  const Int parentLb = _engine->lowerBound(_parentId);
  const Int parentUb = _engine->upperBound(_parentId);
  const Int dLb = _offset;
  const Int dUb = _offset + _valueViolation.size() - 1;

  if (parentUb < _offset) {
    return dLb - parentUb;
  } else if (dUb < parentLb) {
    return parentLb - dUb;
  }
  const Int begin = std::max<Int>(0, parentLb - _offset);
  const Int end = std::min<Int>(static_cast<Int>(_valueViolation.size()),
                                parentUb - _offset + 1);

  return *std::min_element(_valueViolation.begin() + begin,
                           _valueViolation.begin() + end);
}

Int InSparseDomain::upperBound() const {
  const Int parentLb = _engine->lowerBound(_parentId);
  const Int parentUb = _engine->upperBound(_parentId);
  const Int dLb = _offset;
  const Int dUb = _offset + _valueViolation.size() - 1;

  if (parentUb < dLb) {
    return dLb - parentLb;
  } else if (dUb < parentLb) {
    return parentUb - dUb;
  }
  const Int begin = std::max<Int>(0, parentLb - _offset);
  const Int end = std::min<Int>(static_cast<Int>(_valueViolation.size()),
                                parentUb - _offset + 1);

  return *std::max_element(_valueViolation.begin() + begin,
                           _valueViolation.begin() + end);
}