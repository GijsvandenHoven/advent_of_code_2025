#pragma once

#include <iostream>

#include "../util/Day.hpp"
#include "../util/macros.hpp"

#define DAY 6

// CAREFUL! I notice my IDE does not like the trailing whitespaces in this puzzle. They matter for part 2.
// Save text in a basic text editor, you can open the input file in CLion but do not modify.

NAMESPACE_DEF(DAY) {

struct Problem
{
    std::vector<int> numbers;
    char operand = '?';

    int64_t solve() const
    {
        int64_t result;
        std::function<int64_t(int64_t, int64_t)> functor;
        switch (operand)
        {
            case '+': functor = std::plus<int64_t>(); result = 0; break;
            case '*': functor = std::multiplies<int64_t>(); result = 1; break;
            default: throw std::logic_error("Invalid operand");
        }

        return std::accumulate(numbers.begin(), numbers.end(), result, functor);
    }
};

inline std::ostream& operator<<(std::ostream& os, const Problem& problem)
{
    os << "Problem {\n\tNumbers: ";
    std::ranges::for_each(problem.numbers, [&os](int n) { os << n << ", "; });
    os << "\n\tOperand: " << problem.operand << "\n}";

    return os;
}

using Chephalopointers = std::vector<std::string::const_reverse_iterator>;

CLASS_DEF(DAY) {
    public:
    DEFAULT_CTOR_DEF(DAY)

    void parse(std::ifstream &input) override
    {
        std::string line;
        auto add_number_line_to_problems = [this](const std::string& s, bool first = false)
        {
            std::istringstream iss(s);
            int count = 0;
            while (iss.good())
            {
                int number;
                iss >> number;
                if (first)
                {
                    problems.emplace_back();
                }

                problems.at(count).numbers.emplace_back(number);
                ++count;
            }
        };
        // hardcode it for the amount of lines, whatever... I don't want to add complexity by checking for numbers vs operand char.
        {
            std::getline(input, line);
            add_number_line_to_problems(line, true);
            lines.emplace_back(std::move(line));
        }
        {
            std::getline(input, line);
            add_number_line_to_problems(line);
            lines.emplace_back(std::move(line));
        }
        {
            std::getline(input, line);
            add_number_line_to_problems(line);
            lines.emplace_back(std::move(line));
        }
        {
            std::getline(input, line);
            add_number_line_to_problems(line);
            lines.emplace_back(std::move(line));
        }

        {
            // and the operands.
            std::getline(input, line);
            std::istringstream iss(line);
            int count = 0;
            std::string operand;
            while (iss.good() && count < problems.size()) // second part due to trailing spaces in the while loop. This risk also exists for the number lines, but the puzzle input did not have it.
            {
                iss >> operand;
                problems.at(count).operand = operand.at(0);
                ++count;
            }

            lines.emplace_back(std::move(line));
        }

        // std::ranges::for_each(problems, [](const Problem& p) { std::cout << p << "\n"; });
    }

    void v1() const override {
        int64_t result = std::accumulate(problems.begin(), problems.end(), 0ll, [](int64_t a, const Problem& p)
        {
            return a + p.solve();
        });
        reportSolution(result);
    }

    static int read_number_column(const Chephalopointers& cv)
    {
        int n = 0;
        for (int i = 0; i < cv.size() - 1; ++i) // skip the last chephalopointer: it has the operand.
        {
            char c = *cv.at(i);
            if (c == ' ') continue; // this row does not contribute to this chephalonumber

            n = (n * 10) +  c - '0';
        }

        return n;
    }

    void v2() const override {
        int64_t total = 0;
        Chephalopointers c;
        auto increment_chephalopointers = [&c]()
        {
            std::ranges::for_each(c, [](auto& ci) { ++ci; });
        };

        for (const auto& line : lines)
        {
            c.emplace_back(line.rbegin());
        }

        while (lines.front().rend() > c.front())
        {
            std::vector<int> chephalonumbers;
            while ((*c.back()) == ' ') // input analysis: the operand is always on the leftmost column.
            {
                chephalonumbers.emplace_back(read_number_column(c));
                increment_chephalopointers();
            }
            // we hit the operand. This is the last column.
            chephalonumbers.emplace_back(read_number_column(c));
            Problem p { .numbers = std::move(chephalonumbers), .operand = *c.back() };

            total += p.solve();

            increment_chephalopointers(); // consume this row
            increment_chephalopointers(); // and the row of spaces. For the last row this may put the iterators past the end. This is fine because we used '>' rather than '!=' in the loop.
        }


        reportSolution(total);
    }

    void parseBenchReset() override {
        problems.clear();
        lines.clear();
    }

    private:
    std::vector<Problem> problems;
    // problem 2 specific: This is hell to deal with.
    std::vector<std::string> lines;
};

} // namespace

#undef DAY