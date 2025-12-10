#pragma once

#include <iostream>

#include "../util/Day.hpp"
#include "../util/macros.hpp"

#define DAY 10

NAMESPACE_DEF(DAY) {

struct Machine
{
    int goal;
    std::vector<int> togglers;
    std::vector<int> joltage_goal;

    void get_possible_states(int given_state, std::set<int>& out_states) const
    {
        out_states.clear();

        std::ranges::for_each(togglers, [&out_states, given_state](int state)
        {
            // std::cout << given_state << '^' << state << '=' << (given_state ^ state) << std::endl;
            out_states.insert(given_state ^ state);
        });
    }

    void get_possible_joltages(const std::vector<int>& given_joltage, std::vector<std::vector<int>>& new_joltage) const
    {
        new_joltage.clear();

        std::ranges::for_each(togglers, [this, &new_joltage, &given_joltage](int button)
        {

            auto copy_to_modify = given_joltage;

            for (int i = 0; i < copy_to_modify.size(); ++i)
            {
                int bit = button & (1 << i);
                copy_to_modify[i] += (bit != 0);
            }

            if (! is_unrecoverable_joltage(copy_to_modify))
            {
                new_joltage.emplace_back(std::move(copy_to_modify));
            }
        });
    }

    [[nodiscard]] bool is_unrecoverable_joltage(const std::vector<int>& joltage) const
    {
        if (joltage.size() != joltage_goal.size()) throw std::invalid_argument("Joltage vector sizes mismatch");

        for (int i = 0; i < joltage.size(); i++)
        {
            if (joltage.at(i) > joltage_goal.at(i)) return true;
        }

        return false;
    }
};

inline std::ostream& operator<<(std::ostream& os, const Machine& m)
{
    os << "g: " << m.goal << " b: ( ";
    std::ranges::for_each(m.togglers, [&os](int i) { os << i << " "; });
    os << ") j: ( ";
    std::ranges::for_each(m.joltage_goal, [&os](int i) { os << i << " "; });
    os << ")";
    return os;
}

CLASS_DEF(DAY) {
    public:
    DEFAULT_CTOR_DEF(DAY)

    void parse(std::ifstream &input) override {
        // this code is awful. I should not have used a linear parser, oh god.
        std::string line;
        while (std::getline(input, line))
        {
            std::istringstream iss(line);
            while (iss.get() != '[') {}

            int goal = 0;
            int shift = 0;
            int c;
            while ((c = iss.get()) != ']')
            {
                int v = (c == '#') ? 1 : 0;
                goal = goal | (v << shift);
                ++shift;
            }

            iss.get(); // consume space character after ']'

            std::vector<int> buttons;
            while (iss.get() != '{')
            {
                int button_value = 0;
                while ((c = iss.get()) != ')')
                {
                    // DANGER: Input shows that buttons are at most 9 i.e. single digit. This is assumed.
                    if (c == ',') continue;
                    button_value |= 1 << (c - '0');
                }

                buttons.emplace_back(button_value);
                iss.get(); // consume space character after ')'
            }

            std::vector<int> jolters;
            while (c != '}')
            {
                c = iss.get();
                int v = (c - '0');
                while ((c = iss.get()) != ',')
                {
                    if (c == '}') break;
                    v = 10 * v + (c - '0');
                }

                jolters.emplace_back(v);
            }

            machines.emplace_back(goal, buttons, jolters);
        }

        // std::ranges::for_each(machines, [](auto& m) { std::cout << m << "\n"; });
    }

    static int steps_to_get_joltage(const Machine& m)
    {
        using Steps_Jolts_t = std::pair<int, std::vector<int>>;
        std::vector<Steps_Jolts_t> known_states;
        std::queue<Steps_Jolts_t> work;
        work.emplace(0, std::vector<int>(m.joltage_goal.size()));

        int depth = 1;
        while (! work.empty())
        {
            auto [steps, jvec] = std::move(work.front());
            if (steps > depth)
            {
                std::cout << steps << "\n";
                depth = steps;
            }
            work.pop();
            std::vector<std::vector<int>> neo;
            m.get_possible_joltages(jvec, neo);

            for (auto& nj : neo)
            {
                if (nj == m.joltage_goal) return steps + 1;

                // check if this is a known state.
                bool known = false;
                for (const auto& [_, known_jolt] : known_states)
                {
                    if (nj == known_jolt)
                    {
                        known = true;
                        break;
                    }
                }
                if (! known)
                {
                    known_states.emplace_back(steps + 1, nj);
                    work.emplace(steps + 1, nj);
                }
            }
        }

        throw std::invalid_argument("Joltage goal unreachable");
    }

    static int steps_to_get_state(const Machine& m)
    {
        // because there are up to 10 lights, program state is up to 2^10 = 1024. ezpz.
        std::set program_state_to_steps = { 0 };

        using State_Steps_t = std::pair<int, int>;
        std::queue<State_Steps_t> work;
        work.emplace(0, 0);

        while (! work.empty())
        {
            auto [state, step] = work.front();
            work.pop();

            std::set<int> discovered;
            m.get_possible_states(state, discovered); // these states we can make with button presses.
            for (int new_state : discovered)
            {
                if (new_state == m.goal) return step + 1; // because of the queue, this is always the shortest way to reach it.

                if (! program_state_to_steps.contains(new_state))
                {
                    program_state_to_steps.emplace(new_state); // this is a newly discovered state!
                    work.emplace(new_state, step + 1);
                }
            }
        }

        throw std::invalid_argument("The state is unreachable from initially lights off.");
    }

    void v1() const override {

        int total = 0;
        for (const auto& m : machines)
        {
            int v = steps_to_get_state(m);
            std::cout << "solved " << m << " in " << v << " steps\n";
            total += v;
        }

        reportSolution(total);
    }

    void v2() const override {
        int total = 0;
        for (const auto& m : machines)
        {
            int v = steps_to_get_joltage(m);
            std::cout << "solved " << m << " in " << v << " steps\n";
            total += v;
        }

        reportSolution(total);
    }

    void parseBenchReset() override {
        machines.clear();
    }

    private:
    std::vector<Machine> machines;
};

} // namespace

#undef DAY