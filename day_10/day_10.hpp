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
        // Given: Each button is a matrix of booleans.
        // We need to solve for a * A + b * B + c * C + ... = Joltage, while minimizing sum(a,b,c,...)
        // One way to do this is to use Z3, but let's try to do without it for now.

        // Given: B x N matrix (boolean) configuration of the button. Example:
        // g: 4 b: ( 5 9 24 27 7 22 ) j: ( 63 35 32 49 36 )
        //
        // The outputs of the button are on the VERTICAL axis if it is the LEFT matrix.
        //
        // [ 1 1 0 1 1 0 ]    [ A ]   [ 63 ]
        // [ 0 0 0 1 1 1 ]    [ B ]   [ 35 ]
        // [ 1 0 0 0 1 1 ]  x [ C ] = [ 32 ]
        // [ 0 1 1 1 0 0 ]    [ D ]   [ 49 ]
        // [ 0 0 1 1 0 1 ]    [ E ]   [ 36 ]
        //                    [ F ]

        // Let's say we pushed button one (A, 5) 10 times, and nothing else.
        // [ 1 1 0 1 1 0 ]    [ 10]   [ 1 * 10 ]
        // [ 0 0 0 1 1 1 ]    [ 0 ]   [ 0 * 10 ]
        // [ 1 0 0 0 1 1 ]  x [ 0 ] = [ 1 * 10 ]
        // [ 0 1 1 1 0 0 ]    [ 0 ]   [ 0 * 10 ]
        // [ 0 0 1 1 0 1 ]    [ 0 ]   [ 0 * 10 ]
        //                    [ 0 ]

        // Let's say that also the E button was pushed once.
        // [ 1 1 0 1 1 0 ]    [ 10]   [ 1 * 10 + 1 * 1 ]   [ 11 ]
        // [ 0 0 0 1 1 1 ]    [ 0 ]   [ 0 * 10 + 1 * 1 ]   [  1 ]
        // [ 1 0 0 0 1 1 ]  x [ 0 ] = [ 1 * 10 + 1 * 1 ] = [ 11 ]
        // [ 0 1 1 1 0 0 ]    [ 0 ]   [ 0 * 10 + 0 * 1 ]   [  0 ]
        // [ 0 0 1 1 0 1 ]    [ 1 ]   [ 0 * 10 + 0 * 1 ]   [  0 ]
        //                    [ 0 ]

        // OK, but how does a computer solve such an equation system?
        // I M = A^-1 B
        // compute A^T(AAT^1) to get A^-1 (A is not square)
        // multiply on the right with B to get a 6x1 vector with the answer
        // But remember we are also optimising for minimal...


        return 0;
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