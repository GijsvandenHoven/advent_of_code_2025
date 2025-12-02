#pragma once

#include <iostream>

#include "../util/Day.hpp"
#include "../util/macros.hpp"

#define DAY 2

NAMESPACE_DEF(DAY) {

struct Range
{
    int64_t left;
    int64_t right;

    Range(std::string&& s_left, std::string&& s_right) : left(std::stol(s_left)), right(std::stol(s_right))
    {}
};

inline std::ostream& operator<<(std::ostream& os, const Range& range)
{
    os << "(" << range.left << " - " << range.right << ")";
    return os;
}

CLASS_DEF(DAY) {
    public:
    DEFAULT_CTOR_DEF(DAY)

    void parse(std::ifstream &input) override {
        std::string line;
        std::getline(input, line);

        std::ostringstream read;
        std::string left;

        std::ranges::for_each(line, [&](const char c)
        {
            switch (c)
            {
            case '-':
                left = std::move(read).str();
                break;
            case ',':
                ranges.emplace_back(std::move(left), std::move(read).str());
                left = "";
                break;
            default:
                read << c;
                break;
            }
        });
        // EOF case
        ranges.emplace_back(std::move(left), std::move(read).str());
    }

    static int find_number_magnitude(int64_t val)
    {
        int magnitude = 0;
        int64_t i = 1;
        while (val / i)
        {
            i *= 10;
            magnitude += 1;
        }

        return magnitude;
    }

    static bool value_repeats_n_times(const int64_t val)
    {
        int magnitude = find_number_magnitude(val);

        for (int divider = 2; divider <= magnitude; ++divider)
        {
            if (magnitude % divider != 0) continue;

            auto separator = static_cast<int64_t>(std::pow(10,  (magnitude / divider)));
            int64_t working_with = val;

            // we are doing pair-wise comparisons from the groups in the number from left-to-right.
            // Ex 13121212 -> 13|12|12|12 -> 12|12 OK, 12|12 OK, 13|12 NOK.
            // For val = 13121212, divider = 4, magnitude = 8, # iterations = 3
            bool works = true;
            for (int i = 0; i < divider - 1; ++i)
            {
                int64_t right = working_with % separator;
                working_with /= separator;
                int64_t left = working_with % separator;

                if (right != left)
                {
                    works = false;
                    break;
                }
            }

            if (works)
            {
                return true;
            } // otherwise keep searching with a different divider amount.
        }

        return false;
    }

    static bool value_repeats_twice(int64_t val)
    {
        // find the magnitude of this number.
        int magnitude = find_number_magnitude(val);

        if (magnitude % 2 != 0) return false;

        int n_digits_of_half = magnitude / 2;
        auto div_mod = static_cast<int64_t>(std::pow(10,  n_digits_of_half));

        int64_t left = val / div_mod;
        int64_t right = val % div_mod;

        // Notice: For numbers like '1001', this split is not mathematically sound. You get '10' and '1' because of "01".
        // Recall the puzzle input: There are no digits with leading zeroes.
        // Therefore in a twice-repeating number, the first digit of the right-hand side when split shall also be not zero
        // Thus the problem of splitting with div & mod when leading zeroes are present on the mod is not a concern.

        return left == right;
    }

    static int64_t get_repeating_score_of_range(const Range& range, bool multi_repeat_allowed = false)
    {
        auto functor = multi_repeat_allowed ? value_repeats_n_times : value_repeats_twice;

        int64_t range_score = 0;
        for (int64_t i = range.left; i <= range.right; ++i)
        {
            if (functor(i))
            {
                range_score += i;
            }
        }

        return range_score;
    }

    void v1() const override {
        // multithreading this is so overkill, the no-hread solution with std::accumulate took like 170ms for part 2. But it's easy! and faster!

        int64_t sum_of_repeated_digits = 0;
#pragma omp parallel for default(none) shared(sum_of_repeated_digits) schedule(dynamic)
        for (size_t i = 0; i < ranges.size(); ++i)
        {
            int64_t result = get_repeating_score_of_range(ranges[i]);
#pragma omp critical
            {
                sum_of_repeated_digits += result;
            }
        }

        reportSolution(sum_of_repeated_digits);
    }

    void v2() const override {
        int64_t sum_of_repeated_digits = 0;
#pragma omp parallel for default(none) shared(sum_of_repeated_digits) schedule(dynamic)
        for (size_t i = 0; i < ranges.size(); ++i)
        {
            int64_t result = get_repeating_score_of_range(ranges[i], true);
#pragma omp critical
            {
                sum_of_repeated_digits += result;
            }
        }

        reportSolution(sum_of_repeated_digits);
    }

    void parseBenchReset() override {
        ranges.clear();
    }

    private:
    std::vector<Range> ranges;
};

} // namespace

#undef DAY