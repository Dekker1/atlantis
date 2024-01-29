#include "utils/domains.hpp"

namespace atlantis {

static bool isInterval(const std::vector<Int>& sortedVals) {
  return sortedVals.size() > 0 &&
         sortedVals.front() + static_cast<Int>(sortedVals.size()) - 1 ==
             sortedVals.back();
}

IntervalDomain::IntervalDomain(Int lb, Int ub) : _lb(lb), _ub(ub) {}

Int IntervalDomain::lowerBound() const { return _lb; }

Int IntervalDomain::upperBound() const { return _ub; }

std::pair<Int, Int> IntervalDomain::bounds() const {
  return std::pair<Int, Int>{_lb, _ub};
}

size_t IntervalDomain::size() const noexcept { return _ub - _lb + 1; }

bool IntervalDomain::isFixed() const noexcept { return _lb == _ub; }

bool IntervalDomain::contains(Int value) const noexcept {
  return _lb <= value && value <= _ub;
}

std::vector<DomainEntry> IntervalDomain::relativeComplementIfIntersects(
    const Int lb, const Int ub) const {
  if (_lb <= lb && ub <= _ub) {
    return std::vector<DomainEntry>();
  }
  return std::vector<DomainEntry>{{std::max(_lb, lb), std::min(_ub, ub)}};
}

void IntervalDomain::setLowerBound(Int lb) {
  assert(lb <= _ub);
  _lb = lb;
}

void IntervalDomain::setUpperBound(Int ub) {
  assert(_lb <= ub);
  _ub = ub;
}

void IntervalDomain::intersectWith(Int lb, Int ub) {
  _lb = std::max(lb, _lb);
  _ub = std::min(ub, _ub);
  if (_lb > _ub) {
    throw std::runtime_error("Empty domain");
  }
}

void IntervalDomain::fix(Int value) {
  assert(_lb <= value && value <= _ub);
  _lb = value;
  _ub = value;
}

bool IntervalDomain::operator==(const IntervalDomain& other) const {
  return other._lb == _lb && other._ub == _ub;
}

bool IntervalDomain::operator!=(const IntervalDomain& other) const {
  return !(*this == other);
}

SetDomain::SetDomain(std::vector<Int> values) : _values(std::move(values)) {
  std::sort(_values.begin(), _values.end());
}

const std::vector<Int>& SetDomain::values() const { return _values; }

Int SetDomain::lowerBound() const { return _values.front(); }

Int SetDomain::upperBound() const { return _values.back(); }

std::pair<Int, Int> SetDomain::bounds() const {
  return std::pair<Int, Int>{_values.front(), _values.back()};
}

size_t SetDomain::size() const noexcept { return _values.size(); }
bool SetDomain::isFixed() const noexcept { return _values.size() == 1; }

bool SetDomain::contains(Int value) const noexcept {
  return std::binary_search(_values.begin(), _values.end(), value);
}

std::vector<DomainEntry> SetDomain::relativeComplementIfIntersects(
    const Int lb, const Int ub) const {
  if (lowerBound() <= lb && ub <= upperBound() &&
      static_cast<Int>(size()) == upperBound() - lowerBound() + 1) {
    return std::vector<DomainEntry>();
  }
  assert(size() > 0);

  std::vector<DomainEntry> ret;
  // domEntryLb: the lb of the current DomainEntry (ub + 1 is a dummy value)
  Int domEntryLb = ub + 1;
  for (size_t i = 0; i < _values.size(); ++i) {
    if (_values[i] < lb) {
      continue;
    } else if (_values[i] > ub) {
      // the remaining values of the domain are outside the range
      if (domEntryLb <= ub) {
        if (lb < domEntryLb || _values[i - 1] < ub) {
          // There exists a current domain entry: add it.
          ret.emplace_back(DomainEntry{domEntryLb, _values[i - 1]});
          domEntryLb = ub + 1;
        }
      }
      break;
    } else if (domEntryLb > ub) {
      // store lowerBound for the current DomainEntry:
      domEntryLb = _values[i];
    } else if (0 < i && lb <= _values[i - 1] &&
               _values[i] != _values[i - 1] + 1) {
      // There is a hole in the domain in the range lb..ub:
      assert(domEntryLb <= ub);
      ret.emplace_back(DomainEntry{domEntryLb, _values[i - 1]});
      domEntryLb = ub + 1;
    }
  }
  if (domEntryLb <= ub) {
    // There exists a current domain entry
    if (lb < domEntryLb || _values.back() < ub) {
      ret.emplace_back(DomainEntry{domEntryLb, std::min(ub, _values.back())});
    }
  }
  return ret;
}

void SetDomain::remove(Int value) {
  if (value < lowerBound() || upperBound() < value) {
    return;
  }
  auto it = std::find(_values.begin(), _values.end(), value);
  if (it != _values.end()) {
    _values.erase(it);
  }
}

void SetDomain::removeBelow(Int newMin) {
  if (newMin <= lowerBound()) {
    return;
  }
  size_t offset = 0;
  for (size_t i = 0; i < _values.size() && _values[i] < newMin; ++i) {
    ++offset;
  }
  _values.erase(_values.begin(), _values.begin() + offset);
}

void SetDomain::removeAbove(Int newMax) {
  if (upperBound() <= newMax) {
    return;
  }
  size_t offset = _values.size() - 1;
  for (Int i = _values.size() - 1; 0 <= i && newMax < _values[i]; --i) {
    --offset;
  }
  _values.erase(_values.begin() + offset, _values.end());
}

void SetDomain::remove(const std::vector<Int>& values) {
  std::vector<Int> cpy(values);
  std::sort(cpy.begin(), cpy.end());

  size_t i = 0;
  size_t j = 0;
  while (i < cpy.size() && j < _values.size()) {
    if (cpy[i] > _values[j]) {
      ++j;
    } else {
      if (cpy[i] == _values[j]) {
        _values.erase(_values.begin() + j);
      }
      ++i;
    }
  }
}

void SetDomain::intersectWith(const std::vector<Int>& otherVals) {
  std::vector<Int> cpy(otherVals);
  std::sort(cpy.begin(), cpy.end());
  std::vector<Int> newValues;
  newValues.reserve(std::min(_values.size(), otherVals.size()));

  size_t i = 0;
  size_t j = 0;
  while (j < otherVals.size()) {
    while (i < _values.size() && _values[i] < otherVals[j]) {
      ++i;
    }
    if (_values[i] == otherVals[j]) {
      newValues.emplace_back(_values[i]);
    }
    while (j < otherVals.size() && otherVals[j] < _values[i]) {
      ++j;
    }
  }
  _values = std::move(newValues);
}

void SetDomain::fix(Int value) {
  assert(lowerBound() <= value && value <= upperBound());
  _values = std::vector<Int>{value};
}

bool SetDomain::operator==(const SetDomain& other) const {
  return _values == other._values;
}

bool SetDomain::operator!=(const SetDomain& other) const {
  return !(*this == other);
}

SearchDomain::SearchDomain(std::vector<Int> values)
    : _domain(SetDomain{values}) {}

SearchDomain::SearchDomain(Int lb, Int ub) : _domain(IntervalDomain{lb, ub}) {}

const std::variant<IntervalDomain, SetDomain>& SearchDomain::innerDomain()
    const noexcept {
  return _domain;
}

const std::vector<Int>& SearchDomain::values() {
  if (std::holds_alternative<IntervalDomain>(_domain)) {
    std::vector<Int> values(upperBound() - lowerBound() + 1);
    std::iota(values.begin(), values.end(), lowerBound());
    _domain = SetDomain(values);
  }
  assert(std::holds_alternative<SetDomain>(_domain));
  return std::get<SetDomain>(_domain).values();
}

Int SearchDomain::lowerBound() const {
  return std::visit<Int>([&](const auto& dom) { return dom.lowerBound(); },
                         _domain);
}

Int SearchDomain::upperBound() const {
  return std::visit<Int>([&](const auto& dom) { return dom.upperBound(); },
                         _domain);
}

std::pair<Int, Int> SearchDomain::bounds() const {
  return std::visit<std::pair<Int, Int>>(
      [&](const auto& dom) { return dom.bounds(); }, _domain);
}

size_t SearchDomain::size() const noexcept {
  return std::visit<Int>([&](const auto& dom) { return dom.size(); }, _domain);
}

bool SearchDomain::isFixed() const noexcept {
  return std::visit<bool>([&](const auto& dom) { return dom.isFixed(); },
                          _domain);
}

bool SearchDomain::contains(Int value) const noexcept {
  return std::visit<bool>([&](const auto& dom) { return dom.contains(value); },
                          _domain);
}

std::vector<DomainEntry> SearchDomain::relativeComplementIfIntersects(
    const Int lb, const Int ub) const {
  return std::visit<std::vector<DomainEntry>>(
      [&](const auto& dom) {
        return dom.relativeComplementIfIntersects(lb, ub);
      },
      _domain);
}

void SearchDomain::remove(Int value) {
  // do nothing if the value is not in the domain:
  if (value < lowerBound() || upperBound() < value) {
    return;
  }
  if (std::holds_alternative<SetDomain>(_domain)) {
    // Remove the value from the set domain:
    std::get<SetDomain>(_domain).remove(value);
    return;
  }
  assert(std::holds_alternative<IntervalDomain>(_domain));
  if (value == lowerBound()) {
    // change lb
    std::get<IntervalDomain>(_domain).setLowerBound(value + 1);
    return;
  } else if (value == upperBound()) {
    // change ub
    std::get<IntervalDomain>(_domain).setUpperBound(value - 1);
    return;
  }
  std::vector<Int> newDomain(upperBound() - lowerBound());
  Int i = 0;
  for (Int val = lowerBound(); val <= upperBound(); ++val) {
    if (val != value) {
      newDomain.at(i) = val;
      ++i;
    }
  }
  _domain = SetDomain(newDomain);
}

void SearchDomain::removeBelow(Int value) {
  if (value <= lowerBound()) {
    return;
  }
  if (std::holds_alternative<SetDomain>(_domain)) {
    // Remove the value from the set domain:
    std::get<SetDomain>(_domain).removeBelow(value);
    return;
  }
  assert(std::holds_alternative<IntervalDomain>(_domain));
  std::get<IntervalDomain>(_domain).setLowerBound(value);
}

void SearchDomain::removeAbove(Int value) {
  if (value >= upperBound()) {
    return;
  }
  if (std::holds_alternative<SetDomain>(_domain)) {
    // Remove the value from the set domain:
    std::get<SetDomain>(_domain).removeAbove(value);
    return;
  }
  assert(std::holds_alternative<IntervalDomain>(_domain));
  std::get<IntervalDomain>(_domain).setUpperBound(value);
}

void SearchDomain::remove(const std::vector<Int>& values) {
  if (std::holds_alternative<SetDomain>(_domain)) {
    // Remove the value from the set domain:
    std::get<SetDomain>(_domain).remove(values);
    return;
  }
  assert(std::holds_alternative<IntervalDomain>(_domain));
  std::vector<Int> cpy(values);
  std::sort(cpy.begin(), cpy.end());
  for (const Int value : cpy) {
    remove(value);
  }
}

void SearchDomain::intersectWith(const std::vector<Int>& values) {
  if (std::holds_alternative<SetDomain>(_domain)) {
    // Remove the value from the set domain:
    std::get<SetDomain>(_domain).intersectWith(values);
    return;
  }
  assert(std::holds_alternative<IntervalDomain>(_domain));
  std::vector<Int> cpy(values);
  std::sort(cpy.begin(), cpy.end());
  if (isInterval(cpy)) {
    std::get<IntervalDomain>(_domain).intersectWith(cpy.front(), cpy.back());
    return;
  }
  Int begin = 0;
  Int end = cpy.size() - 1;
  while (begin < end && cpy[begin] < lowerBound()) {
    ++begin;
  }
  while (end >= 0 && upperBound() < cpy[end]) {
    --end;
  }
  if (begin > end) {
    _domain = SetDomain(std::vector<Int>());
    return;
  }
  std::vector<Int> newDomain;
  newDomain.reserve(end - begin + 1);
  std::copy(cpy.begin() + begin, cpy.begin() + end + 1,
            std::back_inserter(newDomain));
  _domain = SetDomain(newDomain);
}

void SearchDomain::fix(Int value) {
  if (std::holds_alternative<SetDomain>(_domain)) {
    // Remove the value from the set domain:
    std::get<SetDomain>(_domain).fix(value);
    return;
  }
  assert(std::holds_alternative<IntervalDomain>(_domain));
  std::get<IntervalDomain>(_domain).fix(value);
}

bool SearchDomain::operator==(const SearchDomain& other) const {
  if (std::holds_alternative<IntervalDomain>(_domain) &&
      std::holds_alternative<IntervalDomain>(other._domain)) {
    return std::get<IntervalDomain>(_domain) ==
           std::get<IntervalDomain>(other._domain);
  }
  if (std::holds_alternative<SetDomain>(_domain) &&
      std::holds_alternative<SetDomain>(other._domain)) {
    return std::get<SetDomain>(_domain) == std::get<SetDomain>(other._domain);
  }
  return false;
}

bool SearchDomain::operator!=(const SearchDomain& other) const {
  if (std::holds_alternative<IntervalDomain>(_domain) &&
      std::holds_alternative<IntervalDomain>(other._domain)) {
    return std::get<IntervalDomain>(_domain) !=
           std::get<IntervalDomain>(other._domain);
  }
  if (std::holds_alternative<SetDomain>(_domain) &&
      std::holds_alternative<SetDomain>(other._domain)) {
    return std::get<SetDomain>(_domain) != std::get<SetDomain>(other._domain);
  }
  return true;
}

}  // namespace atlantis