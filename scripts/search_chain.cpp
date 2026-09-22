// Exhaustive, node-bounded search of increasing addition VALUE chains.
// No star restriction, heuristic pruning, floating point, or external tables.
// Usage: search_chain TARGET MAX_STEPS NODE_BUDGET [PREFIX values...]
// A budget result includes all pending subtrees, each independently restartable
// with the same TARGET/MAX_STEPS and its prefix. See the dated research report.
#include <algorithm>
#include <cstdint>
#include <functional>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using Int = std::uint64_t;
using Chain = std::vector<Int>;

Int number(const char* raw) {
    std::string s(raw);
    if (s.empty() || s.find_first_not_of("0123456789") != std::string::npos)
        throw std::invalid_argument("expected unsigned decimal integer");
    return std::stoull(s);
}

void print_chain(const Chain& chain) {
    std::cout << '[';
    for (std::size_t i = 0; i < chain.size(); ++i)
        std::cout << (i ? "," : "") << chain[i];
    std::cout << ']';
}

struct Search {
    Int target, max_steps, budget, visited = 0;
    Chain witness;
    std::vector<Chain> pending;

    // Every next value is a sum of two earlier values. Deduplicate only equal
    // VALUES from this same prefix; histories with different values never merge.
    Chain children(const Chain& a, Int remaining) const {
        Chain next;
        for (std::size_t i = 0; i < a.size(); ++i)
            for (std::size_t j = 0; j <= i; ++j) {
                Int s = a[i] + a[j];
                if (a.back() < s && s <= target && (s << (remaining - 1)) >= target)
                    next.push_back(s);
            }
        std::sort(next.begin(), next.end(), std::greater<Int>());
        next.erase(std::unique(next.begin(), next.end()), next.end());
        return next;
    }

    // Return true only to stop after finding a witness. On budget exhaustion,
    // save the untouched subtree and unwind, collecting every unvisited sibling.
    bool visit(Chain& a) {
        if (visited == budget) {
            pending.push_back(a);
            return false;
        }
        ++visited;
        if (a.back() == target) {
            witness = a;
            return true;
        }
        Int remaining = max_steps - (a.size() - 1);
        if (!remaining || (a.back() << remaining) < target) return false;
        for (Int s : children(a, remaining)) {
            a.push_back(s);
            bool found = visit(a);
            a.pop_back();
            if (found) return true;
        }
        return false;
    }
};

int main(int argc, char** argv) {
    try {
        if (argc < 4) throw std::invalid_argument("TARGET MAX_STEPS NODE_BUDGET [PREFIX...]");
        Search search{number(argv[1]), number(argv[2]), number(argv[3]), 0, {}, {}};
        // With target <= 2^30 and at most 32 steps, every shift is <= 2^62.
        if (!search.target || search.target > (Int(1) << 30) || search.max_steps > 32)
            throw std::invalid_argument("require 1 <= target <= 2^30 and steps <= 32");
        Chain prefix;
        for (int i = 4; i < argc; ++i) prefix.push_back(number(argv[i]));
        if (prefix.empty()) prefix.push_back(1);
        if (prefix[0] != 1 || prefix.size() - 1 > search.max_steps)
            throw std::invalid_argument("invalid prefix start or length");
        for (std::size_t i = 0; i < prefix.size(); ++i) {
            if (!prefix[i] || prefix[i] > search.target)
                throw std::invalid_argument("prefix outside target range");
            if (!i) continue;
            bool sum = false;
            for (std::size_t j = 0; j < i; ++j)
                for (std::size_t k = 0; k <= j; ++k)
                    sum = sum || prefix[j] + prefix[k] == prefix[i];
            if (prefix[i] <= prefix[i-1] || !sum)
                throw std::invalid_argument("prefix is not an addition chain");
        }
        Chain a = prefix;
        search.visit(a);
        std::string status = !search.witness.empty() ? "witness" :
                             search.pending.empty() ? "exhausted" : "budget";
        std::cout << "{\"target\":" << search.target << ",\"max_steps\":" << search.max_steps
                  << ",\"node_budget\":" << search.budget << ",\"visited\":" << search.visited
                  << ",\"status\":\"" << status << "\",\"prefix\":";
        print_chain(prefix);
        std::cout << ",\"witness\":";
        print_chain(search.witness);
        std::cout << ",\"pending_prefixes\":[";
        for (std::size_t i = 0; i < search.pending.size(); ++i) {
            if (i) std::cout << ',';
            print_chain(search.pending[i]);
        }
        std::cout << "]}\n";
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 2;
    }
}
