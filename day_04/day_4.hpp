#pragma once

#include <iostream>

#include "../util/Day.hpp"
#include "../util/macros.hpp"

#define DAY 4

NAMESPACE_DEF(DAY) {

CLASS_DEF(DAY) {
    public:
    DEFAULT_CTOR_DEF(DAY)

    void parse(std::ifstream &input) override
    {
        items.emplace_back(); // empty row at the top.

        std::string line;
        while (std::getline(input, line))
        {
            items.emplace_back();
            auto& row = items.back();
            row.emplace_back(false); // left empty
            for (char c : line)
            {
                bool is_item = c == '@';
                row.emplace_back(is_item);
            }
            row.emplace_back(false); // right empty.
        }

        items.emplace_back();

        const size_t width = items.at(1).size();
        items.front().resize(width);
        items.back().resize(width);

        // print(items);
    }

    static void print(const std::vector<std::vector<bool>>& grid)
    {
        for (auto& v : grid)
        {
            for (auto i : v)
            {
                std::cout << (i ? '@' : '.');
            }
            std::cout << "\n";
        }
    }

    static int get_neighbour_count(const std::vector<std::vector<bool>>& grid, const int y, const int x)
    {
        return
            grid.at(y-1).at(x-1) +
                grid.at(y-1).at(x) +
                    grid.at(y-1).at(x+1) +
                        grid.at(y).at(x-1) +
                            grid.at(y).at(x+1) +
                                grid.at(y+1).at(x-1) +
                                    grid.at(y+1).at(x) +
                                        grid.at(y+1).at(x+1);
    }

    static int try_remove_items(std::vector<std::vector<bool>>& grid)
    {
        std::vector<std::vector<bool>> new_grid = grid;
        constexpr int N = 4;
        int can_remove = 0;
        for (int i = 1; i < grid.size() - 1; ++i)
        {
            for (int j = 1; j < grid.at(i).size() - 1; ++j)
            {
                if (! grid.at(i).at(j)) continue;

                int count = get_neighbour_count(grid, i, j);
                if (count < N)
                {
                    ++can_remove;
                    new_grid.at(i).at(j) = false;
                }
            }
        }

        grid = std::move(new_grid); // overwrite

        return can_remove;
    }

    void v1() const override {
        auto copy = items;
        int removed = try_remove_items(copy);
        reportSolution(removed);
    }

    void v2() const override {
        // who needs memory. Instead of holding on to the delta and committing at the end, just write to a copy.
        auto copy = items;
        int total_removed = 0;
        int iteration_removed = 0;
        do
        {
            iteration_removed = try_remove_items(copy);
            total_removed += iteration_removed;
        } while (iteration_removed > 0);

        reportSolution(total_removed);
    }

    void parseBenchReset() override {
        // none
    }

    private:
    std::vector<std::vector<bool>> items;
};

} // namespace

#undef DAY