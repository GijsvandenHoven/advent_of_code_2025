#pragma once

#include <iostream>

#include "../util/Day.hpp"
#include "../util/macros.hpp"

#define DAY 5

NAMESPACE_DEF(DAY) {

struct Range
{
    int64_t left;
    int64_t right;

    explicit Range(const std::string& r) : left(0), right(0)
    {
        std::istringstream ss(r);
        ss >> left;
        ss.get(); // hyphen is not a minus
        ss >> right;
    }

    Range(int64_t l, int64_t r) : left(l), right(r) {}
};

CLASS_DEF(DAY) {
    public:
    DEFAULT_CTOR_DEF(DAY)

    void parse(std::ifstream &input) override {
        std::string line;
        while (std::getline(input, line) && !line.empty())
        {
            ranges.emplace_back(line);
        }

        while (std::getline(input, line))
        {
            ingredients.emplace_back(std::stoll(line));
        }
    }

    bool is_item_in_any_range(int64_t item) const
    {
        bool ok = false;
        std::ranges::for_each(ranges, [&](auto& r)
        {
            if (item >= r.left && item <= r.right)
            {
                ok = true;
            }
        });

        return ok;
    }

    void v1() const override {
        int64_t r = std::accumulate(ingredients.begin(), ingredients.end(), 0ll, [&](int64_t s, auto i)
        {
            return s + is_item_in_any_range(i);
        });
        reportSolution(r);
    }

    static void get_unique_range_sections(const Range& source, const Range& subtractor, std::vector<Range>& out)
    {
        // case: no overlap (add everything)
        if (subtractor.right < source.left || subtractor.left > source.right)
        {
            out.emplace_back(source);
            return;
        }

        // case: full overlap (add nothing)
        if (subtractor.right >= source.right && subtractor.left <= source.left)
        {
            return;
        }

        // case partial overlap 1: left side cover
        if (subtractor.left <= source.left && subtractor.right < source.right)
        {
            out.emplace_back(subtractor.right + 1, source.right);
            return;
        }

        // case partial overlap 2: right side cover
        if (subtractor.right >= source.right && subtractor.left > source.left)
        {
            out.emplace_back(source.left, subtractor.left - 1);
            return;
        }

        // case partial overlap 3: inside.
        if (subtractor.right < source.right && subtractor.left > source.left)
        {
            out.emplace_back(source.left, subtractor.left - 1);
            out.emplace_back(subtractor.right + 1, source.right);
            return;
        }

        throw std::invalid_argument("Range and subtractor did not match any case?");
    }

    void produce_unique_subranges(int start, const Range& subject, std::vector<Range>& out) const
    {
        // cut up the subject into unique parts by a linear pass over what is left of it.
        out.clear();
        out.emplace_back(subject); // invariant: no two items in this vector shall have overlap.

        for (int i = start; i < ranges.size(); ++i)
        {
            std::vector<Range> new_sub_ranges;
            auto& subtractor = ranges.at(i);

            for (auto& r : out)
            {
                // compare subtractor and range to produce new_sub_ranges. We do not need to worry about previous iteration overlapping due to the non-overlap invariant.
                get_unique_range_sections(r, subtractor, new_sub_ranges);
            }

            out = std::move(new_sub_ranges);
        }
    }

    void v2() const override {
        std::vector<Range> completed_sub_ranges;
        for (int i = 0; i < ranges.size(); ++i)
        {
            std::vector<Range> this_range_production;
            produce_unique_subranges(i+1, ranges.at(i), this_range_production);
            for (auto& r : this_range_production)
            {
                completed_sub_ranges.emplace_back(r);
            }
        }

        int64_t total = 0;
        for (auto& r : completed_sub_ranges)
        {
            total += (r.right - r.left) + 1ll;
        }

        reportSolution(total);
    }

    void parseBenchReset() override {
        ingredients.clear();
        ranges.clear();
    }

    private:
    std::vector<int64_t> ingredients;
    std::vector<Range> ranges;
};

} // namespace

#undef DAY