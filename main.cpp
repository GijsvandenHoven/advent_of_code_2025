#include <iostream>
#include <memory>
#include <map>
#include <set>

#include "day_defs.hpp"

enum class ExitCodes {
    OK = 0,
    NO_INPUT = -1,
    BAD_INPUT = -2,
};

int benchEverything();

int main(int argc, char** argv) {
    if (argc < 3) {
        std::cout << "Require input: [solve|bench|bench_all] [dayNumber] (bench_sample_size)\n";
        return static_cast<int>(ExitCodes::NO_INPUT);
    }

    Day::setRoot(argv[1]);
    std::string mode = argv[2];

    if (mode == "bench_all") {
        std::cout << "bench all call.\n";
        return benchEverything();
    }

    if (argc < 4) {
        std::cout << "Require day number (int)\n";
        return static_cast<int>(ExitCodes::NO_INPUT);
    }

    int day = std::stoi(argv[3]);

    std::cout << mode << " day " << day << "\n";

    // looking up a day that does not exist will cause std::bad_function_call to be thrown,
    // because operator[] creates a new default-initialized value if the key is not found.
    // looking up a day that is not implemented will cause std::logic_error to be thrown,
    // because you shouldn't do that.
    auto solver = DayMap::get(day);

    if (mode == "solve") {
        solver->solve();
    } else if (mode == "bench") {
        if (argc > 4) {
            solver->benchmark(std::stoi(argv[4]));
        } else {
            solver->benchmark();
        }
    } else {
        std::cout << "unknown mode '" << mode << "'\n";
        return static_cast<int>(ExitCodes::BAD_INPUT);
    }

    return static_cast<int>(ExitCodes::OK);
}

// Runs every day in sequence and gets performance stats for each. You cannot use this until all days are implemented.
int benchEverything() {
    std::vector<std::array<BenchmarkStats, 3>> stats(DayMap::NtoDay.size());
    int defaultSampleSize = 10000;

    static const std::map<int, int> sampleSizeOverrides {
        // {3, 1000}, // example: hardcoded adjusted sampling for if your solution would be too slow with the default.
    };
    auto getSampleSize = [defaultSampleSize](int day){
        auto iter =
            std::ranges::find_if(
                sampleSizeOverrides,
                [day](auto& pair){ return pair.first == day; }
        );

        if (iter != sampleSizeOverrides.end()) {
            return iter->second;
        }
        return defaultSampleSize;
    };

    int i = 1;
    for (auto& [day, ctor] : DayMap::NtoDay) {
        // run benchmark with the specified sample count and less reporting on prints, do not cout resulting stat objects.
        int sampleCount = getSampleSize(day);
        std::cout << "Day " << day << ". (" << sampleCount << "x)\n";
        ctor()->benchmark(stats[i-1], sampleCount, 0.10, false);
        i++;
    }

    i = 1;
    for (auto& statblock : stats) {
        auto& [parse, v1, v2] = statblock;
        std::cout << "Day " << i << " parse mean (median): " << parse.format(parse.mean()) << " (" << parse.format(parse.median()) << "). Sample Size: " << parse.n_samples() << "\n";
        std::cout << "Day " << i << " part 1 mean (median): " << v1.format(v1.mean()) << " (" << v1.format(v1.median()) << "). Sample Size: " << v1.n_samples() << "\n";
        std::cout << "Day " << i << " part 2 mean (median): " << v2.format(v2.mean()) << " (" << v2.format(v2.median()) << "). Sample Size: " << v2.n_samples() << "\n";
        i++;
    }

    return static_cast<int>(ExitCodes::OK);
}