#include <chrono>
#include <cxxopts.hpp>
#include <filesystem>
#include <iostream>

#include "fznBackend.hpp"
#include "logging/logger.hpp"

/**
 * @brief Read a duration in milliseconds from an input stream. Used to allow
 * cxxopts to parse the duration for us.
 *
 * @param is The input stream to parse from.
 * @param duration The reference to the value that holds the duration.
 * @return std::istream& The modified input stream.
 */
std::istream& operator>>(std::istream& is, std::chrono::milliseconds& duration);
atlantis::logging::Level getLogLevel(cxxopts::ParseResult& result);

int main(int argc, char* argv[]) {
  try {
    cxxopts::Options options(
        argv[0], "Constraint-based local search backend for MiniZinc.");

    options.positional_help("[flatzinc file]").show_positional_help();

    // Clang Format will make these option definitions completely garbled, hence
    // the comments to turn it off for this region.
    // clang-format off
    options.add_options()
      (
        "a,intermediate-solutions",
        "Ignored, but present because used in the MiniZinc challenge."
      )
      (
        "t,time-limit",
        "Wall time limit in milliseconds.",
        cxxopts::value<std::chrono::milliseconds>()->default_value("30000") // 30 seconds
      )
      (
        "r,seed",
        "The seed to use for the random number generator. If this is negative, the current system time is chosen as the seed.",
        cxxopts::value<long>()->default_value("-1")
      )
      (
        "annealing-schedule",
        "A file path to the annealing schedule definition.",
        cxxopts::value<std::filesystem::path>()
      )
      (
        "log-level",
        "Configures the log level. 0 = ERROR, 1 = WARNING, 2 = INFO, 3 = DEBUG, 4 = TRACE. If not specified, the WARN level is used.",
        cxxopts::value<uint8_t>()
      )
      ("help", "Print help");

    options.add_options("Positional")
      (
        "modelFile",
        "Path to the flatzinc file which contains the model.",
        cxxopts::value<std::filesystem::path>()
      );
    // clang-format on

    options.parse_positional({"modelFile"});

    auto result = options.parse(argc, argv);

    if (result.count("help")) {
      std::cout << options.help({""}) << std::endl;
      return 0;
    }

    atlantis::logging::Logger logger(stderr, getLogLevel(result));

    auto& modelFilePath = result["modelFile"].as<std::filesystem::path>();

    auto givenSeed = result["seed"].as<long>();
    std::uint_fast32_t seed = givenSeed >= 0
                                  ? static_cast<std::uint_fast32_t>(givenSeed)
                                  : std::time(nullptr);

    std::optional<std::chrono::milliseconds> timeout = [&] {
      if (result.count("time-limit") == 1) {
        return std::optional<std::chrono::milliseconds>{
            result["time-limit"].as<std::chrono::milliseconds>()};
      } else {
        return std::optional<std::chrono::milliseconds>{};
      }
    }();

    std::optional<std::filesystem::path> annealingScheduleDefinition = [&] {
      if (result.count("annealing-schedule") == 1) {
        return std::optional<std::filesystem::path>{
            result["annealing-schedule"].as<std::filesystem::path>()};
      } else {
        return std::optional<std::filesystem::path>{};
      }
    }();

    atlantis::search::AnnealingScheduleFactory scheduleFactory(
        annealingScheduleDefinition);
    atlantis::FznBackend backend(modelFilePath, scheduleFactory, seed, timeout);
    auto statistics = backend.solve(logger);

    // Don't log to std::cout, since that would interfere with MiniZinc.
    statistics.display(std::cerr);
  } catch (const cxxopts::OptionException& e) {
    std::cerr << "Error: " << e.what() << std::endl;
  } catch (const std::invalid_argument& e) {
    std::cerr << "Error: " << e.what() << std::endl;
  }
}

atlantis::logging::Level getLogLevel(cxxopts::ParseResult& result) {
  if (result.count("log-level") != 1) {
    return atlantis::logging::Level::WARN;
  }

  switch (result["log-level"].as<uint8_t>()) {
    case 0:
      return atlantis::logging::Level::ERR;
    case 1:
      return atlantis::logging::Level::WARN;
    case 2:
      return atlantis::logging::Level::INFO;
    case 3:
      return atlantis::logging::Level::DEBUG;
    case 4:
      return atlantis::logging::Level::TRACE;
    default:
      throw cxxopts::OptionException("The log level should be 0, 1, 2 or 3.");
  }
}

std::istream& operator>>(std::istream& is,
                         std::chrono::milliseconds& duration) {
  long x;
  auto& is2 = is >> x;

  duration = std::chrono::milliseconds(x);

  return is2;
}