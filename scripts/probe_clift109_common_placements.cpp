// Bounded (u,d1)=(2,3) probe. Keep one common box, both actual three-pair
// exception shapes and one singleton, but relax the two prescribed halves.
// Reuse the existing box generator and tested singleton-position algorithm.
#include <cstdlib>
#include <unistd.h>
#define main completed_box_search_main
#include "clift109_box_search.cpp"
#undef main
namespace placed {
#define main interval_placement_main
#include "clift109_placed_pairs.cpp"
#undef main
}

struct Domain {
  u128 all = 0;
  std::array<u128, 4> roles{};
};

static Domain domain(u128 support, int m, int d, const std::vector<int> &rest) {
  std::vector<u128> edges;
  std::vector<int> starts;
  for (u128 x = support; x; x &= x - 1) {
    int s = ctz(x);
    if (has(support, s + d)) {
      edges.push_back((ONE << s) | (ONE << (s + d)));
      starts.push_back(s);
    }
  }
  Domain out;
  for (size_t i = 0; i < edges.size(); ++i)
    for (size_t j = i + 1; j < edges.size(); ++j) {
      if (edges[i] & edges[j]) continue;
      for (size_t k = j + 1; k < edges.size(); ++k) {
        if ((edges[i] | edges[j]) & edges[k]) continue;
        u128 mask = placed::singleton_positions(
            support ^ (edges[i] | edges[j] | edges[k]), m);
        out.all |= mask;
        for (size_t r = 0; r < rest.size(); ++r)
          if (starts[j] - starts[i] == rest[r] ||
              starts[k] - starts[j] == rest[r] ||
              starts[k] - starts[i] == rest[r]) out.roles[r] |= mask;
      }
    }
  return out;
}

int main() {
  alarm(120);
  Enumerator en;
  en.go(0, 1, 1, 0);
  long long boxes = 0, first = 0, both = 0, shared = 0, roles = 0;
  for (size_t si = 0; si < en.sets.size(); ++si) {
    const auto &xs = en.sets[si];
    if (std::find(xs.begin(), xs.end(), 2) == xs.end() ||
        std::find(xs.begin(), xs.end(), 3) == xs.end()) continue;
    std::vector<int> rest;
    for (int x : xs) if (x != 2 && x != 3) rest.push_back(x);
    for (int t = 0; t + en.totals[si] < N; ++t) {
      u128 support = FULL & ~(en.sums[si] << t);
      if (odd_runs(support, 2) > 7 || odd_runs(support, 3) > 7) continue;
      ++boxes;
      auto a = domain(support, 2, 3, rest);
      if (!a.all) continue;
      ++first;
      auto b = domain(support, 3, 2, rest);
      if (!b.all) continue;
      ++both;
      if (a.all & b.all) ++shared;
      u128 compatible = 0;
      for (int i = 0; i < 4; ++i) for (int j = 0; j < 4; ++j)
        if (i != j) compatible |= a.roles[i] & b.roles[j];
      if (compatible) ++roles;
    }
  }
  std::printf("{\"common_odd_run_boxes\":%lld,\"source_placement\":%lld,"
              "\"both_placements\":%lld,\"shared_singleton\":%lld,"
              "\"distinct_v_d2_roles_and_shared_singleton\":%lld}\n",
              boxes, first, both, shared, roles);
  return 0;
}
