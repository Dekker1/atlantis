#pragma once

#include <fznparser/annotation.hpp>
#include <memory>
#include <string>
#include <vector>

#ifdef _WIN32
#define NOMINMAX  // Ensure the words min/max remain available
#include <Windows.h>
#else
// NOLINTNEXTLINE(bugprone-reserved-identifier)
#define __stdcall
#endif

namespace atlantis::blackbox {

/// Abstract class implemented by different methods to run blackbox functions
class BlackBoxFn {
 public:
  static std::unique_ptr<BlackBoxFn> from_annotation(
      const fznparser::Annotation &);
  virtual ~BlackBoxFn() = default;
  virtual void run(const std::vector<int> &int_in,
                   const std::vector<double> &float_in,
                   std::vector<int> &int_out,
                   std::vector<double> &float_out) = 0;
};

/// Implementation of a black box function that dynamically loads a library and
/// run a contained function.
class BlackBoxDLL : public BlackBoxFn {
 public:
  BlackBoxDLL(const std::string &name);
  virtual ~BlackBoxDLL();
  void run(const std::vector<int> &int_in, const std::vector<double> &float_in,
           std::vector<int> &int_out, std::vector<double> &float_out) override {
    dll_fzn_blackbox(int_in.data(), int_in.size(), float_in.data(),
                     float_in.size(), int_out.data(), int_out.size(),
                     float_out.data(), float_out.size());
  }

 protected:
  void *library;
  void(__stdcall *dll_fzn_blackbox)(const int *, size_t, const double *, size_t,
                                    int *, size_t, double *, size_t);
};

/// Implementation of a black function that starts a seperate process to
/// repeatedly run a blackbox function, communication I/O over pipe.
class BlackBoxExec : public BlackBoxFn {
 public:
  BlackBoxExec(const std::string &program);
  virtual ~BlackBoxExec();
  void run(const std::vector<int> &int_in, const std::vector<double> &float_in,
           std::vector<int> &int_out, std::vector<double> &float_out) override;

 protected:
#ifdef _WIN32
  HANDLE pipe_send;
  HANDLE pipe_receive;
#else
  int pipe_send;
  FILE *file_receive;
#endif
};

}  // namespace atlantis::blackbox
