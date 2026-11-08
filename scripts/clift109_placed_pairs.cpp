// Exact singleton domains for a line tiled by m-pairs, three d-pairs and
// one singleton. This is a necessary interval test, not graph feasibility.
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <unistd.h>

using Mask = unsigned __int128;
static constexpr Mask ONE = 1;

static int popcount(Mask x) {
  return __builtin_popcountll(static_cast<uint64_t>(x)) +
         __builtin_popcountll(static_cast<uint64_t>(x >> 64));
}

static int lowest(Mask x) {
  uint64_t lo = static_cast<uint64_t>(x);
  return lo ? __builtin_ctzll(lo)
            : 64 + __builtin_ctzll(static_cast<uint64_t>(x >> 64));
}

// Pair-peeling leaves the last element of every odd arithmetic run. A
// single deletion can make all runs even iff exactly one run is odd; its
// allowed positions have even index from the start of that run.
static Mask singleton_positions(Mask support, int m) {
  Mask remaining = support, odd_ends = 0;
  while (remaining) {
    Mask starts = remaining & ~(remaining << m);
    Mask singles = starts & ~(remaining >> m);
    Mask pairs = starts & ~singles;
    odd_ends |= singles;
    remaining &= ~(singles | pairs | (pairs << m));
  }
  if (popcount(odd_ends) != 1) return 0;
  int end = lowest(odd_ends), begin = end;
  while (begin >= m && ((support >> (begin - m)) & ONE)) begin -= m;
  Mask out = 0;
  for (int s = begin; s <= end; s += 2 * m) out |= ONE << s;
  return out;
}

int main(int argc, char **argv) {
  if (argc != 2) return 2;
  char *end = nullptr;
  long bound = std::strtol(argv[1], &end, 10);
  if (*end || bound < 7 || bound > 109 || bound % 2 != 1) return 2;
  int n = static_cast<int>(bound);
  alarm(60);
  const Mask full = (ONE << n) - 1;
  int m, d, scanned;
  while ((scanned = std::scanf("%d %d", &m, &d)) == 2) {
    if (m <= 0 || m >= n || d <= 0 || d >= n) return 2;
    Mask found = 0;
    long long triples = 0;
    std::array<std::array<int, 3>, 109> witnesses{};
    for (int x = 0; x < n - d; ++x) {
      Mask a = (ONE << x) | (ONE << (x + d));
      for (int y = x + 1; y < n - d; ++y) {
        Mask b = (ONE << y) | (ONE << (y + d));
        if (a & b) continue;
        for (int z = y + 1; z < n - d; ++z) {
          Mask c = (ONE << z) | (ONE << (z + d));
          if (c & (a | b)) continue;
          ++triples;
          Mask candidates = singleton_positions(full ^ (a | b | c), m);
          Mask fresh = candidates & ~found;
          while (fresh) {
            int s = lowest(fresh);
            witnesses[s] = {x, y, z};
            fresh &= fresh - 1;
          }
          found |= candidates;
        }
      }
    }
    std::printf("D %d %d %llu %llu %lld\n", m, d,
                static_cast<unsigned long long>(found),
                static_cast<unsigned long long>(found >> 64), triples);
    for (int s = 0; s < n; ++s) {
      if ((found >> s) & ONE)
        std::printf("W %d %d %d %d %d %d\n", m, d, s,
                    witnesses[s][0], witnesses[s][1], witnesses[s][2]);
    }
  }
  return scanned == EOF ? 0 : 2;
}
