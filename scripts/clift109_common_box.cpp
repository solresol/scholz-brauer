// Count common dissociated boxes passing both necessary odd-run bounds.
// Reuse the completed search's box generator and odd-run implementation;
// do not repeat its interval-configuration or cap enumeration.
#include <map>
#include <utility>
#define main completed_box_search_main
#include "clift109_box_search.cpp"
#undef main

struct Counts {
  long long packing = 0, odd = 0, top = 0;
};

int main() {
  std::map<std::pair<int, int>, Counts> counts;
  int m, d, scanned;
  while ((scanned = std::scanf("%d %d", &m, &d)) == 2) {
    if (m <= 0 || d <= 0 || m >= N || d >= N || m == d ||
        !counts.emplace(std::make_pair(m, d), Counts{}).second) return 2;
  }
  if (scanned != EOF || counts.empty()) return 2;
  Enumerator en;
  en.go(0, 1, 1, 0);
  long long offsets = 0;
  for (size_t si = 0; si < en.sets.size(); ++si) {
    const auto &xs = en.sets[si];
    for (int t = 0; t + en.totals[si] < N; ++t) {
      ++offsets;
      const u128 remainder = FULL & ~(en.sums[si] << t);
      bool good[6];
      for (int i = 0; i < 6; ++i)
        good[i] = odd_runs(remainder, xs[i]) <= 7;
      for (int i = 0; i < 6; ++i) for (int j = 0; j < 6; ++j) {
        if (i == j) continue;
        auto it = counts.find({xs[i], xs[j]});
        if (it == counts.end()) continue;
        ++it->second.packing;
        if (!good[i] || !good[j]) continue;
        ++it->second.odd;
        if (t + en.totals[si] == N - 1) ++it->second.top;
      }
    }
  }
  std::printf("S %zu %lld\n", en.sets.size(), offsets);
  for (auto [p, c] : counts)
    std::printf("D %d %d %lld %lld %lld\n", p.first, p.second,
                c.packing, c.odd, c.top);
  return 0;
}
