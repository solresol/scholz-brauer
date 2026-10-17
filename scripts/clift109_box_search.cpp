// Complete enumeration of interval path-weight configurations of Clift's
// selected 109 graph, organised around the 64 source-sink paths through 8.
//
// Notation (see results/2026-10-18-clift109-box-exclusion.md): an interval
// labelling has the 109 path weights {0,...,108}. Its weights are
//   t + SS(u,v,w,d1,d2,d3)             paths through 8 (the box), and
//   A1 + R(u,v) + R5,  A2 + P(u) + R7,  A3 + R5            the other 45,
// where P(a)={0,a}, R(a,b)=P(a)+P(b), R7=R(d1,d2)|{p}, R5=R7|(q+P(d1)),
// and SS is the set of subset sums. The six differences are positive with
// distinct subset sums and t+sum<=108. Every step below is a necessary
// condition, so every configuration is emitted; each emitted configuration
// is checked against the full partition before output.
//
// C = [0,108] minus the box = P(d1)+Z  disjoint  E, where
// E = p + (A1+R(u,v) | A2+P(u) | {A3}) has 7 elements. Hence C minus E is
// halved uniquely by d1 (A = X/(2^d1+1), with A disjoint from A<<d1), and
// C has at most 7 odd runs in steps of d1. Symmetrically C = P(u)+Y | (A3+R5)
// gives at most 7 odd runs in steps of u. Then
// Z = A1+R(u,v)+{0,d2,q} | A2+P(u)+{0,d2} | A3+{0,d2,q}; A3 is an element of
// Z and q is fixed by the five elements outside the q-free part.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <vector>

typedef unsigned __int128 u128;
static const int N = 109;
static const u128 ONE = 1;
static const u128 FULL = (ONE << N) - 1;

static inline int popc(u128 x) {
  return __builtin_popcountll((uint64_t)x) + __builtin_popcountll((uint64_t)(x >> 64));
}
static inline int ctz(u128 x) {
  uint64_t lo = (uint64_t)x;
  return lo ? __builtin_ctzll(lo) : 64 + __builtin_ctzll((uint64_t)(x >> 64));
}
static inline bool has(u128 m, long i) { return i >= 0 && i < N && ((m >> i) & 1); }

// Number of odd-length runs of C in arithmetic progressions of step d.
static int odd_runs(u128 C, int d) {
  u128 X = C, odd = 0;
  while (X) {
    u128 starts = X & ~(X << d);
    u128 single = starts & ~(X >> d);
    odd |= single;
    u128 ps = starts & ~single;
    X &= ~(single | ps | (ps << d));
  }
  return popc(odd);
}

// The unique A with A disjoint from A<<d and A|(A<<d)=C, if it exists.
static bool half(u128 C, int d, u128 &A) {
  u128 m = (ONE << d) + 1;
  if (C % m) return false;
  A = C / m;
  return !(A & (A << d));
}

static bool add(u128 &m, long x) {
  if (x < 0 || x >= N || ((m >> x) & 1)) return false;
  m |= ONE << x;
  return true;
}

struct Cfg { int u, v, w, d1, d2, d3, t, p, q, A1, A2, A3; };

// Ground truth: all 109 weights are distinct and form exactly [0,108].
static bool verify(const Cfg &c) {
  u128 m = 0;
  const long six[6] = {c.u, c.v, c.w, c.d1, c.d2, c.d3};
  for (int mask = 0; mask < 64; mask++) {
    long s = c.t;
    for (int i = 0; i < 6; i++) if (mask >> i & 1) s += six[i];
    if (!add(m, s)) return false;
  }
  const long R7[5] = {0, c.d1, c.d2, (long)c.d1 + c.d2, c.p};
  const long R5[7] = {0, c.d1, c.d2, (long)c.d1 + c.d2, c.p, c.q, (long)c.q + c.d1};
  const long Ruv[4] = {0, c.u, c.v, (long)c.u + c.v};
  for (long x : Ruv) for (long y : R5) if (!add(m, c.A1 + x + y)) return false;
  for (long x : {0L, (long)c.u}) for (long y : R7) if (!add(m, c.A2 + x + y)) return false;
  for (long y : R5) if (!add(m, c.A3 + y)) return false;
  return m == FULL;
}

struct Enumerator {
  std::vector<std::array<int, 6>> sets;
  std::vector<u128> sums;
  std::vector<int> totals;
  int chosen[6];
  void go(int depth, int start, u128 sm, int total) {
    if (depth == 6) {
      std::array<int, 6> a;
      std::copy(chosen, chosen + 6, a.begin());
      sets.push_back(a); sums.push_back(sm); totals.push_back(total);
      return;
    }
    for (int x = start; x < N - total; x++) {
      int rem = 5 - depth;  // remaining elements are > x
      if (total + x + rem * x + rem * (rem + 1) / 2 > N - 1) break;
      if ((sm << x) & sm) continue;  // a repeated subset sum
      chosen[depth] = x;
      go(depth + 1, x + 1, sm | (sm << x), total + x);
    }
  }
};

int main(int argc, char **argv) {
  if (argc != 2) { fprintf(stderr, "usage: %s OUTPUT\n", argv[0]); return 2; }
  FILE *fo = fopen(argv[1], "wx");
  if (!fo) { perror("refusing to replace output"); return 2; }
  Enumerator en;
  en.go(0, 1, 1, 0);
  long long set_t = 0, survivors = 0, e_candidates = 0, rejected = 0, configs = 0;
  for (size_t si = 0; si < en.sets.size(); si++) {
    const auto &xs = en.sets[si];
    for (int t = 0; t + en.totals[si] <= N - 1; t++) {
      set_t++;
      const u128 C = FULL & ~(en.sums[si] << t);
      bool good[6]; int ng = 0;
      for (int i = 0; i < 6; i++) { good[i] = odd_runs(C, xs[i]) <= 7; ng += good[i]; }
      if (ng < 2) continue;
      survivors++;
      for (int i1 = 0; i1 < 6; i1++) if (good[i1]) {
        const int d1 = xs[i1];
        for (int iu = 0; iu < 6; iu++) if (good[iu] && iu != i1) {
          const int u = xs[iu];
          for (int iv = 0; iv < 6; iv++) if (iv != iu && iv != i1) {
            const int v = xs[iv];
            int rest[3], nr = 0;
            for (int k = 0; k < 6; k++) if (k != iu && k != iv && k != i1) rest[nr++] = xs[k];
            for (u128 Cr = C; Cr; Cr &= Cr - 1) {
              const int r = ctz(Cr);
              if (!has(C, r + u) || !has(C, r + v) || !has(C, (long)r + u + v)) continue;
              const u128 rect = (ONE << r) | (ONE << (r + u)) | (ONE << (r + v)) | (ONE << (r + u + v));
              const u128 C1 = C & ~rect;
              for (u128 Cs = C1; Cs; Cs &= Cs - 1) {
                const int s = ctz(Cs);
                if (!has(C1, s + u)) continue;
                const u128 C2 = C1 & ~((ONE << s) | (ONE << (s + u)));
                for (u128 Cz = C2; Cz; Cz &= Cz - 1) {
                  const int z = ctz(Cz);
                  u128 Z;
                  if (!half(C2 & ~(ONE << z), d1, Z)) continue;
                  e_candidates++;
                  for (int k2 = 0; k2 < 3; k2++) {
                    const int d2 = rest[k2];
                    int w = rest[(k2 + 1) % 3], d3 = rest[(k2 + 2) % 3];
                    if (w > d3) std::swap(w, d3);  // w and d3 occur only in the box
                    for (u128 Zi = Z; Zi; Zi &= Zi - 1) {
                      const int A3 = ctz(Zi);
                      const int p = z - A3, A1 = r - p, A2 = s - p;
                      const long nonq[14] = {
                          A1, (long)A1 + u, (long)A1 + v, (long)A1 + u + v,
                          (long)A1 + d2, (long)A1 + u + d2, (long)A1 + v + d2, (long)A1 + u + v + d2,
                          A2, (long)A2 + u, (long)A2 + d2, (long)A2 + u + d2, A3, (long)A3 + d2};
                      u128 nm = 0; bool ok = true;
                      for (long x : nonq) if (!add(nm, x)) { ok = false; break; }
                      if (!ok || (nm & ~Z)) continue;
                      const u128 qpart = Z & ~nm;
                      if (popc(qpart) != 5) continue;
                      const int q = ctz(qpart) - std::min(A1, A3);
                      const Cfg c{u, v, w, d1, d2, d3, t, p, q, A1, A2, A3};
                      if (verify(c)) {
                        configs++;
                        fprintf(fo, "%d %d %d %d %d %d %d %d %d %d %d %d\n",
                                u, v, w, d1, d2, d3, t, p, q, A1, A2, A3);
                      } else {
                        rejected++;
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
  if (fclose(fo)) { perror("write"); return 1; }
  printf("{\"dissociated_sets\": %zu, \"set_offsets\": %lld, \"prefilter_survivors\": %lld, "
         "\"e_candidates\": %lld, \"partition_rejections\": %lld, \"configurations\": %lld}\n",
         en.sets.size(), set_t, survivors, e_candidates, rejected, configs);
  return 0;
}
