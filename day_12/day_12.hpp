#pragma once

#include <iostream>
#include <utility>

#include "../util/Day.hpp"
#include "../util/macros.hpp"

#define DAY 12

NAMESPACE_DEF(DAY) {

struct Shape
{
    using Matrix = std::array<std::array<bool, 3>, 3>;

    Shape(const std::string& L1, const std::string& L2, const std::string& L3)
    {
        auto get = [](const std::string& L, int i) { return L.at(i) == '#'; };
        base[0][0] = get(L1, 0);
        base[0][1] = get(L1, 1);
        base[0][2] = get(L1, 2);
        base[1][0] = get(L2, 0);
        base[1][1] = get(L2, 1);
        base[1][2] = get(L2, 2);
        base[2][0] = get(L3, 0);
        base[2][1] = get(L3, 1);
        base[2][2] = get(L3, 2);
    }

    [[nodiscard]] int unit_surface() const
    {
        return base[0][0] + base[0][1] + base[0][2] + base[1][0] + base[1][1] + base[1][2] + base[2][0] + base[2][1] + base[2][2];
    }

    static void print_mat(const Matrix& m, std::ostream& os = std::cout)
    {
        for (auto& a : m) { for (auto& i : a) { os << i << " "; } os << std::endl; }
    }

    Matrix base{};
};

struct Puzzle
{
    int xlen;
    int ylen;
    std::vector<int> puzzle_pieces;

    Puzzle(int _xlen, int _ylen, std::vector<int>&& _puzzle_pieces, std::shared_ptr<std::vector<Shape>> shapes) : xlen(_xlen), ylen(_ylen), puzzle_pieces(std::move(_puzzle_pieces)), shapes(std::move(shapes))
    {
        // std::cout << "Puzzle with " << xlen << " x " << ylen << " puzzle pieces";
        // std::ranges::for_each(puzzle_pieces, [](auto& p) { std::cout << " " << p; });
        // std::cout << "\n";
    }

    [[nodiscard]] bool trivially_unsat() const
    {
        int piece_count = 0;
        int surface = xlen * ylen;
        int piece_surface = 0;
        for (int i = 0; i < puzzle_pieces.size(); ++i)
        {
            piece_count += puzzle_pieces[i];
            piece_surface += puzzle_pieces[i] * (shapes->at(i).unit_surface());
        }


        bool can_fit_at_all = (surface - piece_surface) >= 0;

        // it is a tight fit if less than 2 open squares per piece are allowed on average.
        // Because any of the shapes either has at most 2 gaps, OR they can be combined with themselves to make a 4x3 with <= 2 gaps.
        if (can_fit_at_all && (surface - piece_surface) <= 2 * piece_count) throw std::invalid_argument("Hard fit means we cannot use this function");
        // observation: there are no hard fits.

        return ! can_fit_at_all;
    }

    std::shared_ptr<std::vector<Shape>> shapes;
};

inline std::ostream& operator<<(std::ostream& os, const Shape& shape)
{
    os << "Shape w/ content:\n";
    Shape::print_mat(shape.base, os);
    return os;
}

CLASS_DEF(DAY) {
    public:
    DEFAULT_CTOR_DEF(DAY)

    void parse(std::ifstream &input) override {
        shapes = std::make_shared<std::vector<Shape>>();
        // hardcoding this parse for the shape section. It would be annoying to "if the next line is a \d{2}x\d{2} instead of \d:" check.
        // Thankfully the example and real puzzle both have these 6 shapes.
        std::string toss;
        std::string L1;
        std::string L2;
        std::string L3;
        std::getline(input, toss); // 0:
        std::getline(input, L1);
        std::getline(input, L2);
        std::getline(input, L3);
        shapes->emplace_back(L1, L2, L3);
        std::getline(input, toss); // \n
        std::getline(input, toss); // 1:
        std::getline(input, L1);
        std::getline(input, L2);
        std::getline(input, L3);
        shapes->emplace_back(L1, L2, L3);
        std::getline(input, toss); // \n
        std::getline(input, toss); // 2:
        std::getline(input, L1);
        std::getline(input, L2);
        std::getline(input, L3);
        shapes->emplace_back(L1, L2, L3);
        std::getline(input, toss); // \n
        std::getline(input, toss); // 3:
        std::getline(input, L1);
        std::getline(input, L2);
        std::getline(input, L3);
        shapes->emplace_back(L1, L2, L3);
        std::getline(input, toss); // \n
        std::getline(input, toss); // 4:
        std::getline(input, L1);
        std::getline(input, L2);
        std::getline(input, L3);
        shapes->emplace_back(L1, L2, L3);
        std::getline(input, toss); // \n
        std::getline(input, toss); // 5:
        std::getline(input, L1);
        std::getline(input, L2);
        std::getline(input, L3);
        shapes->emplace_back(L1, L2, L3);
        std::getline(input, toss); // \n

        // We do a little jerry-rigged unit-testing.
        // std::ranges::for_each(shapes, [&](auto& s) { std::cout << s << "\n"; });
        // auto r = shapes.back().get_variants();
        // for (auto& v : r)
        // {
        //     Shape::print_mat(v);
        //     std::cout << "\n";
        // }

        while (std::getline(input, toss))
        {
            std::istringstream iss(toss);
            auto make_int = [](char c, int& i) { i = i * 10 + (c - '0'); };
            int xlen = 0;
            int ylen = 0;

            make_int(static_cast<char>(iss.get()), xlen);
            make_int(static_cast<char>(iss.get()), xlen);
            iss.get(); // 'x' character
            make_int(static_cast<char>(iss.get()), ylen);
            make_int(static_cast<char>(iss.get()), ylen);
            iss.get(); // ':' character.

            std::vector<int> shape_counts;
            while (iss.good())
            {
                int v = 0;
                iss >> v;
                shape_counts.emplace_back(v);
            }

            if (shape_counts.size() != shapes->size()) throw std::logic_error("Not all puzzle pieces enumerated.");

            puzzles.emplace_back(xlen, ylen, std::move(shape_counts), shapes);
        }
    }

    void v1() const override {
        int sat = 0;
        for (auto& p : puzzles)
        {
            if (!p.trivially_unsat())
            {
                ++sat;
            }
        }

        // oh my god. That actually worked. So much time wasted with Z3 and pen-and-paper optimising the shapes.
        // It should have been obvious with shape #4. That bastard is impossible to work with...
        reportSolution(sat);
    }

    void v2() const override {
        reportSolution(0);
    }

    void parseBenchReset() override {
        puzzles.clear();
        shapes->clear();
    }

    private:
    std::vector<Puzzle> puzzles;
    std::shared_ptr<std::vector<Shape>> shapes;
};

} // namespace

#undef DAY