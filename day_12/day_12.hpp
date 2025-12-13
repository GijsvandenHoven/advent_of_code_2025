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

    [[nodiscard]] std::vector<Matrix> get_variants() const
    {
        std::vector<Matrix> variants;
        auto bitmask = [](const Matrix& m)
        {
            int mask = 0;
            for (int i = 0; i < 9; ++i)
            {
                int y = i / 3;
                int x = i % 3;

                mask |= static_cast<int>(m[y][x]) << i;
            }
            return mask;
        };
        std::set<int> uniques{};
        auto add_if_new = [&](const Matrix& m)
        {
            int v = bitmask(m);
            if (! uniques.contains(v))
            {
                uniques.insert(v);
                variants.emplace_back(m);
            }
        };

        // generate variants by reading things in different orders

        { // 1:1
            Matrix m{};
            for (int i = 0; i < 3; ++i)
            {
                for (int j = 0; j < 3; ++j)
                {
                    int mi = i;
                    int mj = j;
                    m[i][j] = base[mi][mj];
                }
            }
            add_if_new(m);
        }
        { // rotate once clockwise
            Matrix m{};
            for (int i = 0; i < 3; ++i)
            {
                for (int j = 0; j < 3; ++j)
                {
                    int mi = 2 - j;
                    int mj = i;
                    m[i][j] = base[mi][mj];
                }
            }
            add_if_new(m);
        }
        { // rotate 180 degrees
            Matrix m{};
            for (int i = 0; i < 3; ++i)
            {
                for (int j = 0; j < 3; ++j)
                {
                    int mi = 2 - i;
                    int mj = 2 - j;
                    m[i][j] = base[mi][mj];
                }
            }
            add_if_new(m);
        }
        { // rotate once counter-clockwise
            Matrix m{};
            for (int i = 0; i < 3; ++i)
            {
                for (int j = 0; j < 3; ++j)
                {
                    int mi = j;
                    int mj = 2 - i;
                    m[i][j] = base[mi][mj];
                }
            }
            add_if_new(m);
        }



        { // h-fip no rotation
            Matrix m{};
            for (int i = 0; i < 3; ++i)
            {
                for (int j = 0; j < 3; ++j)
                {
                    int mi = i;
                    int mj = 2 - j;
                    m[i][j] = base[mi][mj];
                }
            }
            add_if_new(m);
        }
        { // h-flip rotate once clockwise
            Matrix m{};
            for (int i = 0; i < 3; ++i)
            {
                for (int j = 0; j < 3; ++j)
                {
                    int mi = 2 - j;
                    int mj = 2 - i;
                    m[i][j] = base[mi][mj];
                }
            }
            add_if_new(m);
        }
        { // h-flip rotate 180 degrees
            Matrix m{};
            for (int i = 0; i < 3; ++i)
            {
                for (int j = 0; j < 3; ++j)
                {
                    int mi = 2 - i;
                    int mj = j;
                    m[i][j] = base[mi][mj];
                }
            }
            add_if_new(m);
        }
        { // h-flip rotate once counter-clockwise
            Matrix m{};
            for (int i = 0; i < 3; ++i)
            {
                for (int j = 0; j < 3; ++j)
                {
                    int mi = j;
                    int mj = i;
                    m[i][j] = base[mi][mj];
                }
            }
            add_if_new(m);
        }



        { // v-fip no rotation
            Matrix m{};
            for (int i = 0; i < 3; ++i)
            {
                for (int j = 0; j < 3; ++j)
                {
                    int mi = 2 - i;
                    int mj = j;
                    m[i][j] = base[mi][mj];
                }
            }
            add_if_new(m);
        }
        { // v-flip rotate once clockwise
            Matrix m{};
            for (int i = 0; i < 3; ++i)
            {
                for (int j = 0; j < 3; ++j)
                {
                    int mi = j;
                    int mj = i;
                    m[i][j] = base[mi][mj];
                }
            }
            add_if_new(m);
        }
        { // v-flip rotate 180 degrees
            Matrix m{};
            for (int i = 0; i < 3; ++i)
            {
                for (int j = 0; j < 3; ++j)
                {
                    int mi = i;
                    int mj = 2 - j;
                    m[i][j] = base[mi][mj];
                }
            }
            add_if_new(m);
        }
        { // v-flip rotate once counter-clockwise
            Matrix m{};
            for (int i = 0; i < 3; ++i)
            {
                for (int j = 0; j < 3; ++j)
                {
                    int mi = 2 - j;
                    int mj = 2 - i;
                    m[i][j] = base[mi][mj];
                }
            }
            add_if_new(m);
        }

        { // d-flip no rotation
            Matrix m{};
            for (int i = 0; i < 3; ++i)
            {
                for (int j = 0; j < 3; ++j)
                {
                    int mi = 2 - i;
                    int mj = 2 - j;
                    m[i][j] = base[mi][mj];
                }
            }
            add_if_new(m);
        }
        { // d-flip rotate once clockwise
            Matrix m{};
            for (int i = 0; i < 3; ++i)
            {
                for (int j = 0; j < 3; ++j)
                {
                    int mi = j;
                    int mj = 2 - i;
                    m[i][j] = base[mi][mj];
                }
            }
            add_if_new(m);
        }
        { // d-flip rotate 180 degrees
            Matrix m{};
            for (int i = 0; i < 3; ++i)
            {
                for (int j = 0; j < 3; ++j)
                {
                    int mi = i;
                    int mj = j;
                    m[i][j] = base[mi][mj];
                }
            }
            add_if_new(m);
        }
        { // rotate once counter-clockwise
            Matrix m{};
            for (int i = 0; i < 3; ++i)
            {
                for (int j = 0; j < 3; ++j)
                {
                    int mi = 2 - j;
                    int mj = i;
                    m[i][j] = base[mi][mj];
                }
            }
            add_if_new(m);
        }

        return variants;
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
        bool is_hard_fit = can_fit_at_all && (surface - piece_surface) <= 2 * piece_count; // it is a tight fit if less than 2 open squares per piece are allowed on average.

        // observation: there are no hard fits.
        // MAYBE we just return true for any one that is not trivially impossible.
        std::cout << can_fit_at_all << " - " << is_hard_fit << "\n";

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

    static void generate_occupancy_ite(const std::string& variable_name, const Shape::Matrix& offsets, std::ostringstream& out)
    {
        out << "(ite (or "; // the conditions to occupy this spot with this variant.
        for (int i = 0; i < 3; ++i) // this loop creates the Vx & Vy constraints for each unit belonging to the variant. We are occupying if any one is on the x,y coordinate.
        {
            for (int j = 0; j < 3; ++j)
            {
                bool occupies = offsets[i][j];
                if (occupies)
                {
                    out << "(and ";
                    out << "(= x (+ " << variable_name << "_x " << j << "))";
                    out << " ";
                    out << "(= y (+ " << variable_name << "_y " << i << "))";
                    out << ") ";
                }
            }
        }
        out << ") 1 0)"; // close 'OR' and 'ITE'
    }

    static std::string create_ite_chain(const std::string& variable_name, const Shape& origin)
    {
        std::ostringstream out;
        auto variants = origin.get_variants();
        for (int i = 0; i < variants.size(); ++i)
        { // each variant needs an occupancy function comparing its name_x and name_y w/ offset of the top left coordinate to the input 'x' and 'y' params.
            out << "(ite (= " << variable_name << "_v " << i << ")\n\t";
            // generate the ite occupancy counter for the variant.
            generate_occupancy_ite(variable_name, variants.at(i), out);
            out << "\n";
            // else... repeat this loop! closing parentheses are dealt with later.
        }
        out << " 0"; // close the last ite. There is not really an 'else' , the variant has been exhausted, and other asserts shall enforce its bound from 0 to size-1.
        for (int i = 0; i < variants.size(); ++i)
        {
            out << ")";
        }

        return out.str();
    }

    bool sat(const Puzzle& puzzle) const
    {
        std::ostringstream smt;
        std::vector<std::vector<std::string>> variable_names;
        auto for_all_variables = [this, &variable_names](const std::function<void(const std::string&, const Shape&)>& f)
            { for (int i = 0; i < variable_names.size(); ++i) { for (auto& instance : variable_names.at(i)) { f(instance, shapes->at(i)); } } };

        // declare variables. there is an _x, _y, _v (x, y, variant) for each shape.
        for (int i = 0; i < puzzle.puzzle_pieces.size(); ++i)
        {
            variable_names.emplace_back();
            for (int j = 0; j < puzzle.puzzle_pieces.at(i); ++j)
            {
                variable_names.back().emplace_back(std::string("S_") + std::to_string(i) + "_" + std::to_string(j) );
                smt << "(declare-const " << variable_names.back().back() << "_x Int)\n";
                smt << "(declare-const " << variable_names.back().back() << "_y Int)\n";
                smt << "(declare-const " << variable_names.back().back() << "_v Int)\n";
            }
        }

        smt << "\n\n";
        smt << "(define-fun occ ((x Int) (y Int)) Int\n";

        smt << "(+\n\n";

        for_all_variables([&](const std::string& variable_name, const Shape& s)
        {
            smt << create_ite_chain(variable_name, s);
            smt << "\n\n";
        });

        smt << "\n\n))\n\n";

        // write 'asserts' section.
        smt << "(assert (and\n";

        // all variants shall be in their bounds. No '0' on that ITE please :)
        for_all_variables([&](const std::string& variable_name, const Shape& s)
        {
            auto vars = s.get_variants(); // not efficient to re-compute it here. Don't care.
            smt << "\t(>= " << variable_name << "_v 0)\n";
            smt << "\t(<  " << variable_name << "_v " <<  vars.size() << ")\n";
        });
        smt << "\n";
        // all x and y shall be on the grid. Keep in mind these vars are 'top left', and each shape is 3x3.
        for_all_variables([&](const std::string& variable_name, const Shape& s)
        {
            smt << "\t(>= " << variable_name << "_x 0)\n";
            smt << "\t(<  " << variable_name << "_x " << (puzzle.xlen - 2) << ")\n";
            smt << "\t(>= " << variable_name << "_y 0)\n";
            smt << "\t(<  " << variable_name << "_y " << (puzzle.ylen - 2) << ")\n";
        });

        // all grid-points shall have at most '1' occupancy!
        for (int i = 0; i < puzzle.xlen; ++i)
        {
            for (int j = 0; j < puzzle.ylen; ++j)
            {
                smt << "\t(<= (occ " << i << " " << j << ") 1)\n";
            }
        }

        smt << "))";

        std::cout << smt.str() << "\n\n";
        std::cout << "(check-sat)\n(get-objectives)\n(get-model)\n";

        return false;
    }

    void v1() const override {
        // int r = std::accumulate(puzzles.begin(), puzzles.end(), 0, [this](int acc, auto& p)
        // {
        //     return acc + sat(p);
        // });
        // reportSolution(r);

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