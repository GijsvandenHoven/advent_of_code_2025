#pragma once

#include <iostream>

#include "../util/Day.hpp"
#include "../util/macros.hpp"

#define DAY 3

NAMESPACE_DEF(DAY) {

struct Bank
{
    std::vector<int> numbers;

    explicit Bank(std::vector<int>&& n) : numbers(n) {}

    [[nodiscard]] int get_jolt_rating() const
    {
        // largest digit pair by concatenation can be derived by finding the largest number that is not the last one,
        // Then picking the leftmost of that.
        // Then scanning to the right of that, find the highest number again.
        // Wonder if this will be p2: generalize for N numbers
        int best_n_index = 0;
        int best_left_n_value = numbers.at(best_n_index);

        for (int i = 0; i < numbers.size() - 1; ++i)
        {
            if (numbers.at(i) > best_left_n_value)
            {
                best_left_n_value = numbers.at(i);
                best_n_index = i;
            }
        }

        int best_right_n_value = numbers.at(best_n_index + 1);
        for (int i = best_n_index + 1; i < numbers.size(); ++i)
        {
            best_right_n_value = std::max(numbers.at(i), best_right_n_value);
        }

        int jolts = 10 * best_left_n_value + best_right_n_value;

        return jolts;
    }

    [[nodiscard]] int64_t get_giga_jolt_rating(const int N) const
    {
        // greedy algo: select the highest digit in range [i, Size-N], with i = 0 at the start.
        // Set i to the found digit and repeat until N = 0.
        std::vector<int> digits;
        digits.reserve(N);

        int start_index = 0;
        for (int i = N-1; i >= 0; --i)
        {
            const int upper_bound = static_cast<int>(numbers.size() - i);
            int best_digit = numbers.at(start_index);
            int best_index = start_index;
            for (int j = start_index; j < upper_bound; ++j)
            {
                if (numbers.at(j) > best_digit)
                {
                    best_digit = numbers.at(j);
                    best_index = j;
                }
            }

            // std::cout << "(" << i << ") The best digit is " << best_digit << " which lives at index " << best_index << "\n";
            start_index = best_index + 1; // never indexes out of bounds by definition of upper_bound
            digits.emplace_back(best_digit);
        }

        return std::accumulate(digits.begin(), digits.end(), 0ll, [](int64_t a, int d)
        {
            return 10 * a + d;
        });
    }
};

inline std::ostream& operator<<(std::ostream& os, const Bank& bank)
{
    for (auto& n : bank.numbers) std::cout << n;
    return os;
}

CLASS_DEF(DAY) {
    public:
    DEFAULT_CTOR_DEF(DAY)

    void parse(std::ifstream &input) override {
        std::vector<int> number_line;
        auto inserter = std::back_inserter(number_line);
        auto new_line = [&]()
        {
            volt_banks.emplace_back(std::move(number_line));
            number_line.clear(); // redundant but feels wrong not to do it.
            inserter = std::back_inserter(number_line);
        };

        while (input.peek() != EOF)
        {
            auto character = input.get();
            if (character == '\n')
            {
                new_line();
            } else
            {
                *inserter = character - '0';
                ++inserter;
            }
        }
        new_line(); // commit the one held on to from EOF

        // std::ranges::for_each(volt_banks, [&](auto& b) { std::cout << b << "\n"; });
    }

    void v1() const override {
        const int result = std::accumulate(volt_banks.begin(), volt_banks.end(), 0, [&](int a, auto& bank)
        {
            return a + bank.get_jolt_rating();
        });

        reportSolution(result);
    }

    void v2() const override {
        constexpr int N = 12;
        const int64_t result = std::accumulate(volt_banks.begin(), volt_banks.end(), 0ll, [&](int64_t a, auto& bank)
        {
            return a + bank.get_giga_jolt_rating(N);
        });

        reportSolution(result);
    }

    void parseBenchReset() override {
        volt_banks.clear();
    }

    private:
    std::vector<Bank> volt_banks;
};

} // namespace

#undef DAY