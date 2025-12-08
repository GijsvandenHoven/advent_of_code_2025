#pragma once

#include <iostream>
#include <queue>

#include "../util/Day.hpp"
#include "../util/macros.hpp"

#define DAY 8

NAMESPACE_DEF(DAY) {

// not my finest work. Least I could have done is caching the N^2 distances of nodes.
// Oh well, too late now that i got the gold stars :) - Runtime exceeds 1 minute. Absolutely atrocious for c++.

struct Point
{
    int x;
    int y;
    int z;

    Point(int x, int y, int z) : x(x), y(y), z(z) {}

    [[nodiscard]] double distance(const Point& other) const
    {
        double xx = x - other.x;
        double yy = y - other.y;
        double zz = z - other.z; // this will overflow otherwise.

        return std::sqrt((xx * xx) + (yy * yy) + (zz * zz));
    }
};

inline std::ostream& operator<<(std::ostream& os, const Point& p)
{
    os << "(" << p.x << ", " << p.y << ", " << p.z << ")";
    return os;
}

struct Node
{
    Point p;
    std::vector<Node*> connections;

    explicit Node(const Point& p) : p(p) {}
};

using Graph = std::unique_ptr<std::vector<Node>>;

CLASS_DEF(DAY) {
    public:
    DEFAULT_CTOR_DEF(DAY)

    void parse(std::ifstream &input) override {
        std::string line;
        while (std::getline(input, line))
        {
            int i = 0;
            std::array<int, 3> values{};
            for (auto &c : line)
            {
                if (c == ',')
                {
                    ++i;
                } else
                {
                    int d = c - '0';
                    values.at(i) = values.at(i) * 10 + d;
                }
            }

            boxes.emplace_back(values.at(0), values.at(1), values.at(2));
        }

        // std::ranges::for_each(boxes.begin(), boxes.end(), [](auto &box)
        // {
        //     std::cout << box << "\n";
        // });
    }

    std::pair<int,int> shortest_pair(const std::set<std::pair<int,int>>& already_matched) const
    {
        std::pair<int, int> shortest_dist{-1, -1};
        double best = std::numeric_limits<double>::max();

        // filter seen ones with cache?
        for (int i = 0; i < boxes.size(); ++i)
        {
            for (int j = i + 1; j < boxes.size(); ++j)
            {
                auto& L = boxes.at(i);
                auto& R = boxes.at(j);

                auto dist = L.distance(R);
                if (dist < best && ! already_matched.contains({i, j}))
                {
                    best = dist;
                    shortest_dist.first = i;
                    shortest_dist.second = j;
                }
            }
        }

        if (shortest_dist.first == -1)
        {
            throw std::logic_error("Every box is matched. No pair was assigned.");
        }

        // std::cout << "shortest dist is now " << best << "\n";

        return shortest_dist;
    }

    Graph build_graph(const std::set<std::pair<int,int>>& edges) const
    {
        auto graph = std::make_unique<std::vector<Node>>();
        for (auto& p : boxes)
        {
            graph->emplace_back(p);
        }

        for (auto& [x, y] : edges)
        {
            auto& L = graph->at(x); // can use indices of Boxes on Graph because they are entered in the same linear sequence.
            auto& R = graph->at(y);

            L.connections.emplace_back(&R);
            R.connections.emplace_back(&L);
        }

        return std::move(graph);
    }

    static void enumerate_networks(const Graph& G, std::vector<int>& out) {
        std::set<const Node*> seen;
        for (auto& node : *G)
        {
            // do BFS if it is not seen
            if (! seen.contains(&node))
            {
                int size = get_size_of_network_by_BFS(node, seen);
                // std::cout << "Using node " << node.p << ", Found a network sized: " << size << "\n";
                out.emplace_back(size);
            }
        }

        std::sort(out.begin(), out.end(), std::greater());

        std::cout << "Produced a network with:\n";
        std::ranges::for_each(out, [](auto& i){ std::cout << i << ","; });
        std::cout << "\n";
    }

    static int get_size_of_network_by_BFS(const Node& node, std::set<const Node*>& overall_seen)
    {
        if (overall_seen.contains(&node)) throw std::logic_error("Calling BFS on already visited node.");

        std::set<const Node*> local_seen;
        std::queue<const Node*> work;
        work.emplace(&node);
        while (! work.empty())
        {
            auto* n = work.front();
            work.pop();
            auto [_, novel] = local_seen.emplace(n);

            if (!novel) continue; // removal of duplicates, e.g. in a network A<->B, A<->C, B<->C. A gets seen, adding B,C. B gets seen, adding C again...

            for (auto* c : n->connections)
            {
                if (! local_seen.contains(c))
                {
                    work.emplace(c);
                }
            }
        }

        std::ranges::for_each(local_seen, [&](auto* network_item) { overall_seen.emplace(network_item); });

        return static_cast<int>(local_seen.size());
    }

    void v1() const override {
        std::set<std::pair<int,int>> coupled_pairs;

        const int N = boxes.size() > 25 ? 1000 : 10; // automatically select between test set and puzzle input.
        for (int i = 0; i < N; ++i)
        {
            auto [L, R] = shortest_pair(coupled_pairs);
            coupled_pairs.insert({L, R});
        }

        std::vector<int> networks;
        const Graph G = build_graph(coupled_pairs);

        enumerate_networks(G, networks);

        reportSolution(networks.at(0) * networks.at(1) * networks.at(2));
    }

    bool does_this_give_full_connection(const int N) const
    {
        std::set<std::pair<int,int>> coupled_pairs;

        try
        {
            for (int i = 0; i < N; ++i)
            {
                auto [L, R] = shortest_pair(coupled_pairs);
                coupled_pairs.insert({L, R});
            }
        } catch (std::logic_error& e)
        {
            // We got an exception because we ran out of pairs to match in shortest_pair().
            // If this happens, then for sure we have enough exceptions.
            // Using exceptions for program flow is bad practice. Too bad!
            std::cout << "WARN: Full connection assumed by exception thrown.\n";
            return true;
        }

        std::vector<int> networks;
        const Graph G = build_graph(coupled_pairs);

        enumerate_networks(G, networks);

        return networks.size() == 1;
    }

    std::pair<int,int> connect_until_N(int N) const
    {
        std::set<std::pair<int,int>> coupled_pairs;
        auto iter = coupled_pairs.end();

        for (int i = 0; i < N; ++i)
        {
            auto [L, R] = shortest_pair(coupled_pairs);
            auto [latest_iter, _] = coupled_pairs.insert({L, R});
            iter = latest_iter;
        }

        if (iter == coupled_pairs.end()) throw std::logic_error("No connections were made?");

        return *iter;
    }

    std::pair<int,int> binary_search_for_full_connection(const int lower, const int upper) const
    {
        std::cout << "Bin search with: " << lower << " - " << upper << "\n";
        if (lower == upper)
        {
            return connect_until_N(lower);
        }

        int middle = (lower + upper) / 2;

        if (does_this_give_full_connection(middle))
        {
            return binary_search_for_full_connection(lower, middle);
        } else
        {
            return binary_search_for_full_connection(middle+1, upper);
        }
    }

    void v2() const override {
        int N = 10;
        int lower = 0;
        int upper = N;
        while (! does_this_give_full_connection(N))
        {
            lower = N;
            N *= 2;
            upper = N;
        }

        auto [i, j] = binary_search_for_full_connection(lower, upper);

        reportSolution(boxes.at(i).x * boxes.at(j).x);
    }

    void parseBenchReset() override {
        boxes.clear();
    }

    private:
    std::vector<Point> boxes;
};

} // namespace

#undef DAY