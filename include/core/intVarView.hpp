#pragma once
#include <memory>

#include "core/intVar.hpp"
#include "core/savedInt.hpp"
#include "core/tracer.hpp"
#include "core/types.hpp"
#include "core/var.hpp"
#include "core/varView.hpp"

class Engine;  // Forward declaration

class IntVarView : public VarView {
 protected:
  // SavedInt m_savedInt;

  friend class Engine;
  Engine& m_engine;

 public:
  IntVarView(const VarId t_parentId) : VarView(t_parentId) {}

  virtual void init(Engine& e) = 0;

  virtual ~IntVarView() = default;

  virtual bool hasChanged(Timestamp t) = 0;
  virtual Int getValue(Timestamp t) = 0;
  virtual Int getCommittedValue() = 0;
  virtual Timestamp getTmpTimestamp() = 0;

};