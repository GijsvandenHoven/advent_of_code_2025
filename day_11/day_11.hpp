#pragma once

#include <iostream>

#include "../util/Day.hpp"
#include "../util/macros.hpp"

#define DAY 11

NAMESPACE_DEF(DAY) {

struct Node
{
    std::string name;
    std::vector<Node*> next;
};

inline std::ostream& operator<<(std::ostream& os, const Node& node)
{
    os << node.name << ":";
    std::ranges::for_each(node.next, [&os](const Node* child){ os << " " << child->name; });

    return os;
}

CLASS_DEF(DAY) {
    public:
    DEFAULT_CTOR_DEF(DAY)

    void parse(std::ifstream &input) override {
        std::string line;
        std::map<std::string, std::string> node_to_unprocessed_child;

        cables["out"] = { .name = "out" };
        while (std::getline(input, line))
        {
            auto name = line.substr(0, 3);
            auto children = line.substr(5);

            cables[name] = { .name = name };
            node_to_unprocessed_child[name] = children;
        }

        for (const auto& [node, children] : node_to_unprocessed_child)
        {
            std::istringstream iss(children);
            std::string child;
            while (iss.good())
            {
                iss >> child;
                cables[node].next.emplace_back(& cables[child]);
            }
        }

        // for (auto& kvp : cables)
        // {
        //     std::cout << kvp.first << ": " << kvp.second << "\n";
        // }
    }

    static int64_t get_number_of_paths_to_out(const Node* from, std::map<const Node*, int64_t>& answers, const std::string& target)
    {
        if (auto iter = answers.find(from); iter != answers.end())
        {
            // std::cout << "Cache hit for " << from->name << " : " << iter->second << "\n";
            return iter->second;
        }

        int64_t total = 0;
        for (const auto* child : from->next)
        {
            if (child->name == target) // that is one way to do it. But maybe there are other longer paths to get the same result?
            {
                total += 1;
            } else
            {
                const int64_t n_answers = get_number_of_paths_to_out(child, answers, target);
                answers[child] = n_answers;
                total += n_answers;
            }
        }

        return total;
    }

    void v1() const override {
        const auto iter = cables.find("you");
        if (iter == cables.end()) throw std::runtime_error("'You' is not in the map??");

        std::map<const Node*, int64_t> cache;
        int64_t answer = get_number_of_paths_to_out(&iter->second, cache, "out");
        reportSolution(answer);
    }


    void v2() const override {
        // A -- 3 -- B -- 2 -- C -- 5 -- E
        // There are 3 ways to get to B, 3x2 ways to get to C, 3x2x5 ways to get to E...
        // Furthermore, verified by running code for `dac to fft` and `fft to dac`: There exists ZERO paths from dac to fft.
        // This makes sense because a loop in the connections would allow one to generate infinite distinct paths.
        //      For generality with other persons inputs (0.0001% anyone else ever reads this code let alone uses it), we will still compute the redundant stuff.
#define REDUNDANT_RUN false

        const auto get_from_map = [this](const std::string& s)
        {
            const auto iter = cables.find(s);
            if (iter == cables.end()) throw std::runtime_error(s + " node not in the map??");
            return &iter->second;
        };

        int64_t answer = 0;
        int64_t svr_to_fft = 0;
        int64_t svr_to_dac = 0;
        int64_t fft_to_dac = 0;
        int64_t dac_to_fft = 0;
        int64_t dac_to_out = 0;
        int64_t fft_to_out = 0;
        {
            std::map<const Node*, int64_t> cache;
            svr_to_fft = get_number_of_paths_to_out(get_from_map("svr"), cache, "fft");
        }
        {
            std::map<const Node*, int64_t> cache;
            fft_to_dac = get_number_of_paths_to_out(get_from_map("fft"), cache, "dac");
        }
        {
            std::map<const Node*, int64_t> cache;
            dac_to_out = get_number_of_paths_to_out(get_from_map("dac"), cache, "out");
        }
#if REDUNDANT_RUN
        {
            std::map<const Node*, int64_t> cache;
            svr_to_dac = get_number_of_paths_to_out(get_from_map("svr"), cache, "dac");
        }
        {
            std::map<const Node*, int64_t> cache;
            dac_to_fft = get_number_of_paths_to_out(get_from_map("dac"), cache, "fft");
        }
        {
            std::map<const Node*, int64_t> cache;
            fft_to_out = get_number_of_paths_to_out(get_from_map("fft"), cache, "out");
        }
#endif
        // std::cout << "svr_to_fft = " << svr_to_fft << std::endl;
        // std::cout << "fft_to_dac = " << fft_to_dac << std::endl;
        // std::cout << "dac_to_out = " << dac_to_out << std::endl;
        // std::cout << "svr_to_dac = " << svr_to_dac << std::endl;
        // std::cout << "dac_to_fft = " << dac_to_fft << std::endl;
        // std::cout << "fft_to_out = " << fft_to_out << std::endl;

        answer = (svr_to_fft * fft_to_dac * dac_to_out) + (svr_to_dac * dac_to_fft * fft_to_out);

        reportSolution(answer);
    }

    void parseBenchReset() override {
        cables.clear();
    }

    private:
    std::map<std::string, Node> cables;
};

} // namespace

#undef DAY