#pragma once

#include <iostream>

#include "../util/Day.hpp"
#include "../util/macros.hpp"

#define DAY 7

NAMESPACE_DEF(DAY) {

struct Point
{
    int x;
    int y;

    Point(int _x, int _y): x(_x), y(_y) {}
};

inline bool operator<(const Point& lhs, const Point& rhs)
{
    return lhs.y < rhs.y || (lhs.y == rhs.y && lhs.x < rhs.x);
}

inline std::ostream& operator<<(std::ostream& os, const Point& p)
{
    os << "(" << p.x << ", " << p.y << ")";
    return os;
}

CLASS_DEF(DAY) {
    public:
    DEFAULT_CTOR_DEF(DAY)

    void parse(std::ifstream &input) override {
        std::string line;
        int row = 0;
        while (std::getline(input, line))
        {
            for (int col = 0; col < line.size(); ++col)
            {
                switch (line.at(col))
                {
                    case 'S': start.x = col; start.y = row; break;
                    case '^': splitters.emplace(col, row); break;
                    default: break;
                }
            }
            ++row;
        }

        end_depth = row;
        //
        // std::cout << "start " << start << "\n";
        // std::cout << "\nsplitters:\n";
        // std::ranges::for_each(splitters, [&](auto& p) { std::cout << p << "\n"; });
    }

    int64_t count_timelines_created(const Point& beam, std::map<Point, int64_t>& splitter_count_cache) const
    {
        // base case: This beam is at the exit
        if (beam.y >= end_depth) return 1; // This is one timeline.

        // Seek downward until splitter or end_depth for this X.
        int current = beam.y + 1;
        while (! splitters.contains(Point{beam.x, current}))
        {
            ++ current;
            if (current >= end_depth) return 1; // no splitter was hit, this is one timeline.
        }

        // OK, some splitter was hit. What is the amount of timelines it produces?
        Point the_splitter = {beam.x, current};
        auto iter = splitter_count_cache.find(the_splitter);
        if (iter != splitter_count_cache.end())
        {
            return iter->second;
        }

        // It is not known! Let's figure it out then.
        Point L = { beam.x-1, current };
        Point R = { beam.x+1, current };
        int64_t left = count_timelines_created(L, splitter_count_cache);
        int64_t right = count_timelines_created(R, splitter_count_cache);

        int64_t timelines_from_this_splitter = left + right;
        splitter_count_cache.emplace(the_splitter, timelines_from_this_splitter);

        return timelines_from_this_splitter;
    }

    int count_splitters_used(const Point& beam, std::set<Point>& hit_splitters) const
    {
        // base case: This beam is at the exit
        if (beam.y >= end_depth) return 0; // no splitter was hit.

        // Seek downward until splitter or end_depth for this X.
        int current = beam.y + 1;
        while (! splitters.contains(Point{beam.x, current}))
        { // every step of the beam should be cached.
            ++ current;
            if (current >= end_depth) return 0; // no splitter was hit,
        }

        auto [_, novel] = hit_splitters.emplace(beam.x, current);

        int left = 0;
        int right = 0;
        if (novel)
        {
            Point L = { beam.x-1, current };
            Point R = { beam.x+1, current };
            left = count_splitters_used(L, hit_splitters);
            right = count_splitters_used(R, hit_splitters);
        }

        return novel + left + right;
    }

    void v1() const override {
        std::set<Point> cache;
        auto result = count_splitters_used(start, cache);
        reportSolution(result);
    }

    void v2() const override {
        std::map<Point, int64_t> cache;
        auto result = count_timelines_created(start, cache);
        reportSolution(result);
    }

    void parseBenchReset() override {
        splitters.clear();
    }

    private:
    std::set<Point> splitters;
    Point start{0,0};
    int end_depth = 0;
};

} // namespace

#undef DAY