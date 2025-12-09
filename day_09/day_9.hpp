#pragma once

#include <iostream>

#include "../util/Day.hpp"
#include "../util/macros.hpp"

#define DAY 9

NAMESPACE_DEF(DAY) {

struct Point
{
    int x;
    int y;

    Point(int _x, int _y) : x(_x), y(_y) {}
};

CLASS_DEF(DAY) {
    public:
    DEFAULT_CTOR_DEF(DAY)

    void parse(std::ifstream &input) override {
        std::string line;
        while (std::getline(input, line))
        {
            int x = 0;
            int y = 0;
            int* affecting = &x;
            for (auto c : line)
            {
                if (c == ',')
                {
                    affecting = &y;
                } else
                {
                    *affecting = (*affecting * 10) + (c - '0');
                }
            }
            points.emplace_back(x, y);
        }

        // std::ranges::for_each(points, [](auto& p) { std::cout << p.x << ", " << p.y << "\n"; });
    }

    static int64_t get_rectangle_area(const Point& p1, const Point& p2)
    {
        int64_t h_size = std::abs(p1.x - p2.x) + 1;
        int64_t v_size = std::abs(p1.y - p2.y) + 1;

        return h_size * v_size;
    }

    void v1() const override {
        int64_t best_size = 0;
        for (int i = 0; i < points.size(); ++i)
        {
            for (int j = i + 1; j < points.size(); ++j)
            {
                int64_t candidate = get_rectangle_area(points.at(i), points.at(j));
                best_size = std::max(best_size, candidate);
            }
        }
        reportSolution(best_size);
    }

    // Fun fact! This will false positive on shapes outside the hull too, as long as the rectangle is not intersected.
    // One way to have this is a shape where the rectangle's opposing corners are the points, and one of the rectangle's third corner is an inner corner of the hull.
    // Analysis on the input (Sinusoid Y delta) shows that this is not a problem for the puzzle. It is shaped like an approximated circle with fuzzy/jittery edges.
    // Therefore, I never bothered to add code to deal with this. It is possible to detect this case, though:
    // Just inspect the points of the other pair of opposing corners of the rectangle to both exist within the shape.
    //     One way to do this that I can think of (laborious) is sorting the vertical edges,
    //     then casting a horizontal ray from (lowest X in polygon - 1) to (point X) while using flow-fill logic: flip when edge encountered & special handling for corners.
    //     Creating a JIRA ticket for this and estimating it and implementing it is left as an exercise for the reader.
    bool rectangle_in_hull (const Point& p1, const Point& p2) const
    {
        const Point top_left = {std::min(p1.x, p2.x), std::min(p1.y, p2.y)};
        const Point top_right = {std::max(p1.x, p2.x), std::min(p1.y, p2.y)};
        const Point bot_left = {std::min(p1.x, p2.x), std::max(p1.y, p2.y)};
        const Point bot_right = {std::max(p1.x, p2.x), std::max(p1.y, p2.y)}; // technically not needed, only 3 points are sufficient information to infer the 4th.
        // std::cout << "Rectangle under test is: " << top_left.x << ", " << top_left.y << "; " << bot_right.x << ", " << bot_right.y << "\n";

        // If there exists a line piece in the points that intersects this rectangle, we know the rectangle is not in the hull.
        for (int i = 0; i < points.size(); ++i)
        {
            // Given: Adjacent pieces of the input form the line pieces.
            int j = static_cast<int>((i + 1) % points.size());
            const Point& contender_1 = points.at(i);
            const Point& contender_2 = points.at(j);

            bool horizontal = contender_1.x != contender_2.x; // We know adjacent points have a delta on Either X or Y, not both. There is a delta on X here if true.
            int line_start;
            int line_end;
            int line_other_axis_point;

            // abstraction from x or y, don't want to if(horizontal) { duplicated code; }
            int rectangle_axis_start;
            int rectangle_axis_end;
            int rectangle_other_axis_start;
            int rectangle_other_axis_end;
            if (horizontal)
            {
                line_start = std::min(contender_1.x, contender_2.x);
                line_end = std::max(contender_1.x, contender_2.x);
                rectangle_axis_start = top_left.x;
                rectangle_axis_end = top_right.x;

                rectangle_other_axis_start = top_left.y;
                rectangle_other_axis_end = bot_left.y;
                line_other_axis_point = contender_1.y;
            } else
            {
                line_start = std::min(contender_1.y, contender_2.y);
                line_end = std::max(contender_1.y, contender_2.y);
                rectangle_axis_start = top_left.y;
                rectangle_axis_end = bot_left.y;

                rectangle_other_axis_start = top_left.x;
                rectangle_other_axis_end = top_right.x;
                line_other_axis_point = contender_1.x;
            }

            // std::cout << "Line piece under test is: " << (horizontal ? 'x' : 'y') << " - " << line_start << " - " << line_end << std::endl;

            if (
                (line_start < rectangle_axis_end) &&
                (line_end > rectangle_axis_start))
            {
                // s...|.....|...e or s....|...e....|..  or ..|......s.|.....e or ..|..s..e..|.. are all covered by this.
                // We intersect the rectangle on the line's axis. But are we matched on the other axis?
                if (line_other_axis_point > rectangle_other_axis_start && line_other_axis_point < rectangle_other_axis_end)
                {
                    // std::cout << "\tThis is in the hull. (at " << (horizontal ? 'x' : 'y') << " = " << line_other_axis_point << ")\n";
                    return false;
                }
            }
        }

        return true;
    }

    void v2() const override {
        int64_t best_size = 0;
        for (int i = 0; i < points.size(); ++i)
        {
            for (int j = i + 1; j < points.size(); ++j)
            {
                if (! rectangle_in_hull(points.at(i), points.at(j))) continue;

                int64_t candidate = get_rectangle_area(points.at(i), points.at(j));
                best_size = std::max(best_size, candidate);
            }
        }

        reportSolution(best_size);
    }

    void parseBenchReset() override {
        points.clear();
    }

    private:
    std::vector<Point> points;
};

} // namespace

#undef DAY