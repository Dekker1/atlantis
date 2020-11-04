#include "views/intMaxView.hpp"

// TODO: invariant should take its true id in the constructor.
extern Id NULL_ID;

Int IntMaxView::getValue(Timestamp t) {
  return std::max<Int>(m_max, m_engine->getValue(t, m_parentId));
}

Int IntMaxView::getCommittedValue() {
  return std::max<Int>(m_max, m_engine->getCommittedValue(m_parentId));
}

Timestamp IntMaxView::getTmpTimestamp() {
  return m_engine->getTmpTimestamp(m_parentId);
}

void IntMaxView::init(VarId id, Engine& e) {
  m_id = id;
  m_engine = &e;
}