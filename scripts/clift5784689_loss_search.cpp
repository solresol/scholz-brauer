// Complete search for budget-attaining labellings of the run-generalised Clift
// graph G(a,b,c), in loss coordinates.  (5,9,3) is chain 9 of Clift's optimal
// chains for 5784689; (1,0,0) is Clift's selected 109 graph.
//
// Graph (values in order): R0=1, Ri=2R(i-1) (i=1..a), "4"=2Ra, "5"="4"+1,
// "7"="5"+Ra, "8"=2*"4", "15"="8"+"7", F0="15"+"8", Fj=2F(j-1) (j=1..b),
// "28"=Fb+"5", G0="28"+Fb, Gj=2G(j-1) (j=1..c), "58"=Gc+"7", n="58"+Gc.
//
// A labelling of cost n-1 has path weights exactly 0..n-1, and a critical path
// P* (weight n-1) whose edges carry their tail caps while every vertex off P*
// has all out-shifts 0 (lean/ScholzBrauer/CliftLabelling.lean).  Every doubling
// vertex lies on P*.  Write loss = (n-1) - weight.  Every path is P* plus a set
// of non-overlapping detours, so every loss is a sum of positive detour losses
// and the losses are exactly 0..n-1.
//
// Configuration (loss coordinates).  The 22 doubling-type differences fall in
// classes U (a run differences), v, W (w and d3), F (b run differences and d2),
// G (c run differences and d1).  With SS(.) the subset sums, the n losses are
// the disjoint union of nine components:
//   box  t + SS(all)          eK  A1 + SS(U,v,F,G)     ep  A1+p + SS(U,v)
//   eq   A1+q + SS(U,v,G)     tK  A2 + SS(U,F,G)       tp  A2+p + SS(U)
//   zK   A3 + SS(F,G)         zp  A3+p                 zq  A3+q + SS(G)
// (box: paths through "8"; e: through 4->5; t: through 2->7; z: through 1->5.)
// Every atom (t, A1, A2, A3, p, q and the differences) is positive except the
// anchor: P* runs 4-8 (families A, B: t = 0) or 4-5-7-15 (family C: A1 = 0).
//
// Search.  Each component is down-closed (dropping a difference or the p, q
// offset gives another element), so the smallest loss x not yet generated is
// the minimal element of a new atom: a new base (t, A1, A2, A3) equal to x, p
// or q at x minus the smallest known base containing it, or a new difference at
// x minus the smallest base of an active component containing its class.
// Branching on this choice enumerates every configuration exactly once.
// Classes are lazy: known differences carry the block of the class partition
// induced by the active components; activating a component refines the blocks
// (branching), so classes are decided only when they first matter.
//
// Pruning (all necessary conditions):
//  * every generated loss lies in [0,n) and is new (exact cover);
//  * box maximum t + sum(all) <= n-1, future differences distinct and >= lb;
//  * halving: X = [0,n) minus the components without class F (resp. G) is
//    halved by every F (resp. G) difference d, so [0,n) has at most |E| odd
//    runs in steps of d, |E_G| = val("7"), |E_F| = val("7") + val("5")2^(c+1);
//    option halve=all applies the same test to U, V and W (for chains 1-8,
//    |E_U| = 97 and |E_V| = 1137);
//  * caps: for every critical-path family the prefix cap sums P_0=0 <= ... <=
//    P_S=n-1 must satisfy the detour inequalities (family_ok), with unknown
//    atoms replaced by valid lower bounds and lazy classes by bounds valid for
//    every resolution.  Feasibility is Bellman-Ford on difference constraints.
//
// Modes (append `var=XYZ` for the chord variants of chains 10-16, X,Y,Z in
// {0,1}): `a b c t|A1 OUT [split=D]` searches one anchor (emitting `J` job
// lines at depth D); `a b c resume OUT [split=D]` reads job lines on stdin and
// searches each (or splits it further at depth D), printing per-job JSON;
// `a b c lptest` evaluates the caps test on stdin lines (validation hook).
// Configurations surviving every test are written as `C` lines.  Test hooks
// (environment): LPDROP=mask drops constraint groups; LPSLACK=s relaxes P_S.
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

typedef long long ll;
typedef std::pair<ll, int> DV;  // difference value, class block (bit mask)
enum { CU = 1, CV = 2, CW = 4, CF = 8, CG = 16 };
enum { AT = 0, AA1 = 1, AA2 = 2, AA3 = 3, AP = 4, AQ = 5 };
struct CompDef { int atoms; int mask; };
static const CompDef COMPS[9] = {
    {1 << AT, 31},  {1 << AA1, 27}, {(1 << AA1) | (1 << AP), 3}, {(1 << AA1) | (1 << AQ), 19},
    {1 << AA2, 25}, {(1 << AA2) | (1 << AP), 1}, {1 << AA3, 24}, {(1 << AA3) | (1 << AP), 0},
    {(1 << AA3) | (1 << AQ), 16}};

static ll n;
static int NW;
static int ga, gb, gc;
static int gvX = 0, gvY = 0, gvZ = 0;  // chord variants (chains 9-16, 1-8)
static int gs = 1;  // doublings from "2" to "4" (1 for chains 9-16, 10 for chains 1-8)
static int capc[5];
static bool use_lp = true;
static ll nodes = 0, solutions = 0, lp_prunes = 0, bound_prunes = 0, cand_prunes = 0, collisions = 0, jobs_out = 0;
static int split_depth = -1;
static FILE *out;
static std::vector<char> cand[5];  // halving candidates per class (empty: no test)
static bool halve_all = false;      // option halve=all: test U, V and W too
static ll lp_slack = 0;  // test hook: total caps may reach n-1+slack
static int lp_drop = 0;  // test hook: drop constraint groups (1 A1, 2 A2, 4 A3, 8 p, 16 q, 32 t)

// ------------------------------------------------------------ state --------
static std::vector<uint64_t> cov;  // generated losses
struct Comp { std::vector<uint64_t> w; ll lo = 0, hi = -1; bool on = false; };
static Comp comp[9];
static ll atom[6];
static std::vector<DV> diffs;

static inline bool isset(ll i) { return (cov[i >> 6] >> (i & 63)) & 1; }

struct UndoRec { int c; ll e; size_t off; ll t0, t1; };
static std::vector<uint64_t> arena;
static std::vector<UndoRec> undo;

// Component c becomes c | (c + e): the new losses must be below n and new.
static bool double_comp(int c, ll e) {
  Comp &C = comp[c];
  if (C.hi + e >= n) return false;
  ll s0 = C.lo >> 6, s1 = C.hi >> 6;
  ll t0 = (C.lo + e) >> 6, t1 = (C.hi + e) >> 6;
  ll q = e >> 6; int r = (int)(e & 63);
  size_t off = arena.size();
  arena.resize(off + (t1 - t0 + 1));
  uint64_t *S = arena.data() + off;
  for (ll t = t0; t <= t1; t++) {
    ll i = t - q;
    uint64_t v = 0;
    if (i >= s0 && i <= s1) v = C.w[i] << r;
    if (r && i - 1 >= s0 && i - 1 <= s1) v |= C.w[i - 1] >> (64 - r);
    if (v & cov[t]) { arena.resize(off); collisions++; return false; }
    S[t - t0] = v;
  }
  for (ll t = t0; t <= t1; t++) { cov[t] |= S[t - t0]; C.w[t] |= S[t - t0]; }
  C.hi += e;
  undo.push_back({c, e, off, t0, t1});
  return true;
}
static void undo_one() {
  UndoRec u = undo.back(); undo.pop_back();
  Comp &C = comp[u.c];
  const uint64_t *S = arena.data() + u.off;
  for (ll t = u.t0; t <= u.t1; t++) { cov[t] &= ~S[t - u.t0]; C.w[t] &= ~S[t - u.t0]; }
  C.hi -= u.e;
  arena.resize(u.off);
}
static void undo_to(size_t m) { while (undo.size() > m) undo_one(); }

static bool known(int A) { return atom[A] >= 0; }
static bool ready(int c) {
  for (int A = 0; A < 6; A++) if ((COMPS[c].atoms >> A & 1) && !known(A)) return false;
  return true;
}
static ll base_of(int c) {
  ll b = 0;
  for (int A = 0; A < 6; A++) if (COMPS[c].atoms >> A & 1) b += atom[A];
  return b;
}
// Blocks: classes with equal membership in every ready component.
static int blocks_for(const bool rd[9], int out_blocks[5]) {
  int keys[5], nb = 0;
  for (int k = 0; k < 5; k++) {
    int cl = 1 << k, key = 0;
    for (int c = 0; c < 9; c++) if (rd[c]) key = key * 2 + ((COMPS[c].mask & cl) ? 1 : 0);
    int j = 0;
    while (j < nb && keys[j] != key) j++;
    if (j == nb) { keys[nb] = key; out_blocks[nb] = 0; nb++; }
    out_blocks[j] |= cl;
  }
  return nb;
}
static int capof(int mask) { int c = 0; for (int k = 0; k < 5; k++) if (mask >> k & 1) c += capc[k]; return c; }
static int total_diffs() { return capc[0] + capc[1] + capc[2] + capc[3] + capc[4]; }
static int count_block(int B) { int c = 0; for (auto &d : diffs) if (d.second == B) c++; return c; }
// Halving candidates: a difference of block B belongs to one class of B, so it
// must be a candidate of some class in B (a class without a table always is).
static bool cand_ok(ll e, int mask) {
  if (e <= 0 || e >= n) return false;
  for (int k = 0; k < 5; k++)
    if ((mask >> k & 1) && (cand[k].empty() || cand[k][e])) return true;
  return false;
}

// ------------------------------------------------------------ caps LP ------
// Families: X = 0 (A: P* 4-8-15-23), 1 (B: 4-8-23), 2 (C: 4-5-7-15-23);
// i2 = 0 (F_b-51 direct) or 1 (F_b-28-51); i1 = 0 (G_c-sink) or 1 (G_c-58-sink).
// Chord variants (chains 10-16) double a chord: vX ("16"=2"8", F0="16"+"7")
// leaves only X = 3 (4-8-16-23, d3 the pair difference at "8"); vY ("46"=2Fb,
// G0="46"+"5") only i2 = 2 (Fb-46-51, d2 at Fb, q rejoins at G0); vZ
// ("102"=2Gc, n="102"+"7") only i1 = 2 (Gc-102-n, d1 at Gc, p rejoins at n).
// The nine components are the same in every variant.
// Positions on P*: R0..R(a-1) = 0..a-1, Ra = a, "4" = a+1, then A: "8" a+2,
// "15" a+3, F0 a+4; B: "8" a+2, F0 a+3; C: "5" a+2, "7" a+3, "15" a+4, F0 a+5.
// A detour from position s rejoining at e with first shift in [0, c_s] has loss
// in [P_e - P_(s+1), P_e - P_s]; detours sharing a first edge differ by P's.
//   A/B: A1 in [P_r - P_(a+2), P_r - P_(a+1)], A2 in [P_r - P_(a+1), P_r - P_a],
//        A3 in [P_r - P_1, P_r], p = P_r58 - P_r, q = P_r28 - P_r (r = a+3);
//        w <= c_(a+1); A: c_(a+3) <= d3 <= c_(a+2) + c_(a+3); B: d3 <= c_(a+2).
//   C:   t in [P_(a+4) - P_(a+2), P_(a+4) - P_(a+1)], t + w <= P_(a+4) - P_(a+1),
//        A2 in [P_(a+3) - P_(a+1), P_(a+3) - P_a], A3 in [P_(a+2) - P_1, P_(a+2)],
//        p in [P_r58 - P_(a+4), P_r58 - P_(a+3)], q in [P_r28 - P_(a+3), P_r28 - P_(a+2)],
//        d3 = c_(a+4).
//   All: run differences at most their caps; v <= c_a; d2 <= c_Fb (i) or in
//        [c_28, c_Fb + c_28] (ii); d1 <= c_Gc (a) or in [c_58, c_Gc + c_58] (b).
// Interior run positions only carry sums; their per-position bounds are implied
// by the run-sum bounds, so only the positions in `keep` are LP variables.
struct Edge { int i, j; ll w; };
struct LP {
  Edge E[256]; int ne = 0; int S = 0;
  void le(int i, int j, ll w) { E[ne++] = {i, j, w}; }   // P_j - P_i <= w
  void ge(int i, int j, ll w) { E[ne++] = {j, i, -w}; }  // P_j - P_i >= w
  bool feasible() const {  // no negative cycle (Bellman-Ford, all-zero start)
    ll d[64];
    for (int k = 0; k <= S; k++) d[k] = 0;
    for (int it = 0; it <= S + 1; it++) {
      bool ch = false;
      for (int q = 0; q < ne; q++) { const Edge &e = E[q]; ll nv = d[e.i] + e.w; if (nv < d[e.j]) { d[e.j] = nv; ch = true; } }
      if (!ch) return true;
    }
    return false;
  }
};
struct AI { bool k; ll v; };  // known exact value, or lower bound v
struct ClassInfo {
  ll LBU, LBF, LBG, LBV, maxF, minF, maxG, minG, minU, minV, runF, runG, runU1, runV1;
  bool allF, allG, allU, allV;
};
struct CLP {
  int map[96]; int nn = 0; LP L;
  void le(int i, int j, ll w) { L.le(map[i], map[j], w); }
  void ge(int i, int j, ll w) { L.ge(map[i], map[j], w); }
};
static bool family_ok(int X, int i2, int i1, const AI at[6], AI wv, AI dv, const ClassInfo &ci) {
  int a = ga, b = gb, c = gc, p4 = ga + gs;  // "2" at a, "4" at p4
  int f0 = X == 0 ? p4 + 3 : X == 1 ? p4 + 2 : X == 2 ? p4 + 4 : p4 + 3;
  int Fb = f0 + b, g0 = i2 == 0 ? Fb + 1 : Fb + 2, r28 = i2 == 2 ? Fb + 2 : Fb + 1, Gc = g0 + c;
  int S = i1 == 0 ? Gc + 1 : Gc + 2, r58 = i1 == 1 ? Gc + 1 : S;
  CLP C;
  bool used[96] = {false};
  int keep[] = {0, 1, a, a + 1, p4, p4 + 1, p4 + 2, p4 + 3, p4 + 4, f0, Fb, Fb + 1, Fb + 2, g0, Gc, Gc + 1, Gc + 2, S};
  for (int p : keep) if (p <= S) used[p] = true;
  for (int p = 0; p <= S; p++) C.map[p] = used[p] ? C.nn++ : -1;
  C.L.S = C.nn - 1;
  int prev = -1;
  for (int p = 0; p <= S; p++) if (used[p]) { if (prev >= 0) C.ge(prev, p, 0); prev = p; }
  C.le(0, S, n - 1 + lp_slack); C.ge(0, S, n - 1);
  auto range = [&](int bit, const AI &v, int lo_i, int j, int hi_i) {
    // lo: P_j - P_lo_i <= v (only if exact); hi: P_j - P_hi_i >= v
    if (lp_drop & bit) return;
    if (v.k) C.le(lo_i, j, v.v);
    C.ge(hi_i, j, v.v);
  };
  if (X <= 1) {
    int r15 = p4 + 2;
    range(1, at[AA1], p4 + 1, r15, p4);
    range(2, at[AA2], a + 1, r15, a);
    range(4, at[AA3], 1, r15, 0);
    if (!(lp_drop & 8)) { if (at[AP].k) C.le(r15, r58, at[AP].v); C.ge(r15, r58, at[AP].v); }
    if (!(lp_drop & 16)) { if (at[AQ].k) C.le(r15, r28, at[AQ].v); C.ge(r15, r28, at[AQ].v); }
    C.ge(p4, p4 + 1, wv.v);
    if (X == 0) { C.ge(p4 + 1, p4 + 3, dv.v); if (dv.k) C.le(p4 + 2, p4 + 3, dv.v); }
    else C.ge(p4 + 1, p4 + 2, dv.v);
  } else if (X == 3) {  // 4-8-16-23: detours from "7" rejoin at F0
    int r = p4 + 3;
    range(1, at[AA1], p4 + 1, r, p4);
    range(2, at[AA2], a + 1, r, a);
    range(4, at[AA3], 1, r, 0);
    if (!(lp_drop & 8)) { if (at[AP].k) C.le(r, r58, at[AP].v); C.ge(r, r58, at[AP].v); }
    if (!(lp_drop & 16)) { if (at[AQ].k) C.le(r, r28, at[AQ].v); C.ge(r, r28, at[AQ].v); }
    C.ge(p4, p4 + 1, wv.v);
    C.ge(p4 + 1, p4 + 2, dv.v);
  } else {
    range(32, at[AT], p4 + 1, p4 + 3, p4);
    range(2, at[AA2], a + 1, p4 + 2, a);
    range(4, at[AA3], 1, p4 + 1, 0);
    range(8, at[AP], p4 + 3, r58, p4 + 2);
    range(16, at[AQ], p4 + 2, r28, p4 + 1);
    C.ge(p4, p4 + 3, at[AT].v + wv.v);
    C.ge(p4 + 3, p4 + 4, dv.v); if (dv.k) C.le(p4 + 3, p4 + 4, dv.v);
  }
  C.ge(0, a, ci.LBU);
  C.ge(1, a, ci.runU1);
  if (ci.allU) C.ge(0, 1, ci.minU);
  C.ge(a, p4, ci.LBV);          // V run (s differences) at positions a..p4-1
  C.ge(a + 1, p4, ci.runV1);     // all but the one at "2" (which also leaves by theta)
  if (ci.allV) C.ge(a, a + 1, ci.minV);
  C.ge(f0, i2 == 1 ? Fb + 2 : Fb + 1, ci.LBF);
  C.ge(f0, Fb, ci.runF);
  if (ci.allF) {
    if (i2 != 1) C.ge(Fb, Fb + 1, ci.minF); else { C.le(Fb + 1, Fb + 2, ci.maxF); C.ge(Fb, Fb + 2, ci.minF); }
  }
  C.ge(g0, i1 == 1 ? S : Gc + 1, ci.LBG);
  C.ge(g0, Gc, ci.runG);
  if (ci.allG) {
    if (i1 != 1) C.ge(Gc, Gc + 1, ci.minG); else { C.le(Gc + 1, S, ci.maxG); C.ge(Gc, S, ci.minG); }
  }
  return C.L.feasible();
}

// sum of the r smallest values among vals[0..nv) and `extra` copies of lb
static ll smallest_sum(ll *vals, int nv, int extra, ll lb, int r) {
  for (int i = 0; i < extra && nv < 96; i++) vals[nv++] = lb;
  std::sort(vals, vals + nv);
  ll s = 0;
  for (int i = 0; i < r && i < nv; i++) s += vals[i];
  return s;
}

// Caps test for the current atoms and the differences d1 ++ d2.  x is a lower
// bound for the minimal element of every unknown atom: an unknown base is >= x,
// an unknown difference >= x (its minimal element lies in a component of base
// 0, except W under anchor A1: >= x - t), p >= x - min known A, q likewise.
static bool caps_ok2(ll x, const DV *d1, size_t n1, const DV *d2, size_t n2) {
  bool anchorT = atom[AT] == 0;
  AI at[6];
  ll minA = -1, minA13 = -1;
  for (int A = 1; A <= 3; A++) if (known(A) && (minA < 0 || atom[A] < minA)) minA = atom[A];
  for (int A : {1, 3}) if (known(A) && (minA13 < 0 || atom[A] < minA13)) minA13 = atom[A];
  for (int A = 0; A < 4; A++) at[A] = known(A) ? AI{true, atom[A]} : AI{false, x};
  at[AP] = known(AP) ? AI{true, atom[AP]} : AI{false, minA >= 0 ? std::max(1LL, x - minA) : 1};
  at[AQ] = known(AQ) ? AI{true, atom[AQ]} : AI{false, minA13 >= 0 ? std::max(1LL, x - minA13) : 1};
  ll lbd = x, lbdW = anchorT ? x : (known(AT) ? std::max(1LL, x - atom[AT]) : 1);
  ll resSum[5] = {0}, resCnt[5] = {0}, unresCnt[5] = {0}, unresMin[5] = {-1, -1, -1, -1, -1};
  ll resVals[5][40]; int nres[5] = {0};
  ll cand[5][96]; int ncand[5] = {0};  // possible members: resolved and unresolved
  for (size_t t = 0; t < n1 + n2; t++) {
    const DV &d = t < n1 ? d1[t] : d2[t - n1];
    int B = d.second;
    if (__builtin_popcount(B) == 1) {
      int k = __builtin_ctz(B); resSum[k] += d.first; resCnt[k]++;
      resVals[k][nres[k]++] = d.first; cand[k][ncand[k]++] = d.first;
    } else {
      for (int k = 0; k < 5; k++) if (B >> k & 1) {
        unresCnt[k]++; if (unresMin[k] < 0 || d.first < unresMin[k]) unresMin[k] = d.first;
        cand[k][ncand[k]++] = d.first;
      }
    }
  }
  // slots of class k certainly filled by future differences
  auto must = [&](int k) { return (int)std::max(0LL, (ll)capc[k] - resCnt[k] - unresCnt[k]); };
  ClassInfo ci;
  ci.LBU = resSum[0] + must(0) * lbd;
  ci.LBF = resSum[3] + must(3) * lbd;
  ci.LBG = resSum[4] + must(4) * lbd;
  // run parts: b of the b+1 F-class differences (c of the c+1 G, a-1 of U off R0)
  // are at least the smallest values among every possible member (resolved,
  // unresolved candidates, and every unresolved slot at the future bound).
  ci.runF = smallest_sum(cand[3], ncand[3], (int)(capc[3] - resCnt[3]), lbd, gb);
  ci.runG = smallest_sum(cand[4], ncand[4], (int)(capc[4] - resCnt[4]), lbd, gc);
  ci.runU1 = smallest_sum(cand[0], ncand[0], (int)(capc[0] - resCnt[0]), lbd, ga - 1);
  // V class (s differences): resolved ones plus the smallest possible others.
  {
    ll un[96]; int nu = 0;
    for (size_t t = 0; t < n1 + n2; t++) {
      const DV &d = t < n1 ? d1[t] : d2[t - n1];
      if (__builtin_popcount(d.second) > 1 && (d.second & CV)) un[nu++] = d.first;
    }
    int rest = (int)(capc[1] - resCnt[1]);
    ci.LBV = resSum[1] + smallest_sum(un, nu, rest, lbd, rest);
    ci.runV1 = smallest_sum(cand[1], ncand[1], rest, lbd, gs - 1);
    ci.allV = resCnt[1] == capc[1];
    ci.minV = ci.allV ? *std::min_element(resVals[1], resVals[1] + nres[1]) : 0;
  }
  ci.allF = resCnt[3] == capc[3]; ci.allG = resCnt[4] == capc[4]; ci.allU = resCnt[0] == capc[0];
  ci.maxF = ci.minF = ci.maxG = ci.minG = ci.minU = 0;
  if (ci.allF) { ci.maxF = *std::max_element(resVals[3], resVals[3] + nres[3]); ci.minF = *std::min_element(resVals[3], resVals[3] + nres[3]); }
  if (ci.allG) { ci.maxG = *std::max_element(resVals[4], resVals[4] + nres[4]); ci.minG = *std::min_element(resVals[4], resVals[4] + nres[4]); }
  if (ci.allU) ci.minU = *std::min_element(resVals[0], resVals[0] + nres[0]);
  // roles of the two W differences (which is w, which d3)
  AI wo[2][2]; int nwo = 0;
  ll otherW = lbdW; if (unresMin[2] >= 0) otherW = std::min(otherW, unresMin[2]);
  if (resCnt[2] == 2) { ll p = resVals[2][0], q = resVals[2][1]; wo[0][0] = {true, p}; wo[0][1] = {true, q}; wo[1][0] = {true, q}; wo[1][1] = {true, p}; nwo = 2; }
  else if (resCnt[2] == 1) { ll p = resVals[2][0]; wo[0][0] = {true, p}; wo[0][1] = {false, otherW}; wo[1][0] = {false, otherW}; wo[1][1] = {true, p}; nwo = 2; }
  else { wo[0][0] = {false, otherW}; wo[0][1] = {false, otherW}; nwo = 1; }
  static int last = 0;  // start with the family that succeeded last (speed only)
  int fams[8], nf = 0;
  const int Xs0[3] = {0, 1, 2}, Xs1[1] = {3};
  const int *Xs = gvX ? Xs1 : Xs0; int nX = gvX ? 1 : 3;
  for (int xi = 0; xi < nX; xi++) {
    int X = Xs[xi];
    if (anchorT ? X == 2 : X != 2) continue;  // anchor t: families A, B (or A'); A1: C
    for (int i2 = (gvY ? 2 : 0); i2 < (gvY ? 3 : 2); i2++)
      for (int i1 = (gvZ ? 2 : 0); i1 < (gvZ ? 3 : 2); i1++) fams[nf++] = X * 9 + i2 * 3 + i1;
  }
  if (nf == 0) return false;  // no critical path with this anchor (anchor A1 under vX)
  for (int t = 0; t < nf; t++) {
    int f = fams[(t + last) % nf];
    for (int w = 0; w < nwo; w++)
      if (family_ok(f / 9, (f / 3) % 3, f % 3, at, wo[w][0], wo[w][1], ci)) { last = (t + last) % nf; return true; }
  }
  return false;
}
static bool caps_ok(ll x, const std::vector<DV> &ds) { return caps_ok2(x, ds.data(), ds.size(), nullptr, 0); }

// ------------------------------------------------------------ search -------
static ll first_zero(ll from) {
  ll i = from >> 6;
  if (i >= (ll)NW) return n;
  uint64_t z = ~cov[i] & (~0ULL << (from & 63));
  while (!z) { i++; if (i >= (ll)NW) return n; z = ~cov[i]; }
  ll x = i * 64 + __builtin_ctzll(z);
  return x < n ? x : n;
}

static void emit_state(FILE *f) {
  fprintf(f, "J %lld %lld %lld %lld %lld %lld %zu", atom[0], atom[1], atom[2], atom[3], atom[4], atom[5], diffs.size());
  for (auto &p : diffs) fprintf(f, " %lld:%d", p.first, p.second);
  fprintf(f, "\n");
}

static void record() {
  if ((int)diffs.size() != total_diffs()) { fprintf(stderr, "full cover with missing differences\n"); exit(4); }
  for (int A = 0; A < 6; A++) if (!known(A)) { fprintf(stderr, "full cover with missing atom\n"); exit(4); }
  solutions++;
  fprintf(out, "C %lld %lld %lld %lld %lld %lld", atom[0], atom[1], atom[2], atom[3], atom[4], atom[5]);
  std::vector<DV> d = diffs;
  std::sort(d.begin(), d.end());
  for (auto &p : d) fprintf(out, " %lld:%d", p.first, p.second);
  fprintf(out, "\n");
  fflush(out);
}

static int depth() { int d = (int)diffs.size(); for (int A = 0; A < 6; A++) d += known(A); return d; }
static void step(ll x0);

// Refine the blocks of the known differences (old) against the new partition,
// adding each difference to the newly ready components it belongs to.
static void refine(const int *blocks, int nb, const std::vector<int> &newc, size_t i,
                   const std::vector<DV> &old, ll x) {
  if (i == old.size()) { step(x); return; }
  ll e = old[i].first; int ob = old[i].second;
  for (int bi = 0; bi < nb; bi++) {
    int B = blocks[bi];
    if (!(B & ob)) continue;
    if (count_block(B) + 1 > capof(B)) continue;
    if (!cand_ok(e, B)) continue;
    diffs.push_back({e, B});
    if (use_lp && B != ob && !caps_ok2(x + 1, diffs.data(), diffs.size(), old.data() + i + 1, old.size() - i - 1)) {
      lp_prunes++; diffs.pop_back(); continue;
    }
    size_t m = undo.size();
    bool ok = true;
    for (int c : newc)
      if (COMPS[c].mask & B) { if (!double_comp(c, e)) { ok = false; break; } }
    if (ok) refine(blocks, nb, newc, i + 1, old, x);
    undo_to(m);
    diffs.pop_back();
  }
}

// A new atom was set: place the bases of newly ready components, then refine.
static void activate(ll x) {
  bool rd[9];
  std::vector<int> newc;
  for (int c = 0; c < 9; c++) { rd[c] = ready(c); if (rd[c] && !comp[c].on) newc.push_back(c); }
  int blocks[5]; int nb = blocks_for(rd, blocks);
  if (use_lp && !caps_ok(x + 1, diffs)) { lp_prunes++; return; }
  std::vector<int> placed;
  bool ok = true;
  for (int c : newc) {
    ll b = base_of(c);
    if (b < 0 || b >= n || isset(b)) { ok = false; break; }
    cov[b >> 6] |= 1ULL << (b & 63); comp[c].w[b >> 6] |= 1ULL << (b & 63);
    comp[c].lo = comp[c].hi = b; comp[c].on = true; placed.push_back(c);
  }
  if (ok) {
    std::vector<DV> old = diffs;
    diffs.clear();
    refine(blocks, nb, newc, 0, old, x);
    diffs = old;
  }
  for (int c : placed) {
    ll b = comp[c].lo;
    cov[b >> 6] &= ~(1ULL << (b & 63)); comp[c].w[b >> 6] &= ~(1ULL << (b & 63));
    comp[c].on = false; comp[c].hi = -1;
  }
}

static void step(ll x0) {
  nodes++;
  ll x = first_zero(x0);
  if (x >= n) { record(); return; }
  int r = total_diffs() - (int)diffs.size();
  if (known(AT)) {
    ll sum = atom[AT];
    for (auto &d : diffs) sum += d.first;
    ll lb = atom[AT] == 0 ? x : std::max(1LL, x - atom[AT]);
    if (sum + r * lb + (ll)r * (r - 1) / 2 > n - 1) { bound_prunes++; return; }
  }
  if (use_lp && !caps_ok(x, diffs)) { lp_prunes++; return; }
  if (split_depth >= 0 && depth() >= split_depth) { emit_state(out); jobs_out++; return; }
  // x is a new base
  for (int A = 0; A < 4; A++)
    if (!known(A)) { atom[A] = x; activate(x); atom[A] = -1; }
  // x is the first p (or q) element: x = smallest known base containing it + p
  {
    ll m = -1;
    for (int A = 1; A <= 3; A++) if (known(A) && (m < 0 || atom[A] < m)) m = atom[A];
    if (!known(AP) && m >= 0) { atom[AP] = x - m; activate(x); atom[AP] = -1; }
    m = -1;
    for (int A : {1, 3}) if (known(A) && (m < 0 || atom[A] < m)) m = atom[A];
    if (!known(AQ) && m >= 0) { atom[AQ] = x - m; activate(x); atom[AQ] = -1; }
  }
  // x is the minimal element of a new difference of some block
  bool rd[9];
  for (int c = 0; c < 9; c++) rd[c] = comp[c].on;
  int blocks[5]; int nb = blocks_for(rd, blocks);
  for (int bi = 0; bi < nb; bi++) {
    int B = blocks[bi];
    if (count_block(B) >= capof(B)) continue;
    ll mb = -1;
    for (int c = 0; c < 9; c++)
      if (comp[c].on && (COMPS[c].mask & B) == B) { ll b = base_of(c); if (mb < 0 || b < mb) mb = b; }
    if (mb < 0) continue;
    ll e = x - mb;
    if (!cand_ok(e, B)) { cand_prunes++; continue; }
    diffs.push_back({e, B});
    if (use_lp && !caps_ok(x + 1, diffs)) { lp_prunes++; diffs.pop_back(); continue; }
    size_t m = undo.size();
    bool ok = true;
    for (int c = 0; c < 9; c++)
      if (comp[c].on && (COMPS[c].mask & B) == B) { if (!double_comp(c, e)) { ok = false; break; } }
    if (ok) step(x);
    undo_to(m);
    diffs.pop_back();
  }
}

static ll chain_value(int a, int b, int c, ll &v7, ll &v5) {
  ll two = 1LL << a, four = two << gs, five = four + 1, seven = five + two, eight = 2 * four;
  ll s15 = eight + seven, s23 = s15 + eight, fb = s23 << b, s28 = fb + five, s51 = s28 + fb;
  ll g = s51 << c, s58 = g + seven;
  v7 = seven; v5 = five;
  return s58 + g;
}

static void clear_state() {
  std::fill(cov.begin(), cov.end(), 0);
  for (int c = 0; c < 9; c++) { std::fill(comp[c].w.begin(), comp[c].w.end(), 0); comp[c].on = false; comp[c].hi = -1; }
  for (int A = 0; A < 6; A++) atom[A] = -1;
  diffs.clear(); undo.clear(); arena.clear();
}

// Rebuild the search state from a job line (atoms and differences with blocks).
static bool load_state(const char *line) {
  const char *p = line;
  int consumed;
  while (*p == ' ') p++;
  if (*p == 'J') p++;
  for (int A = 0; A < 6; A++) { if (sscanf(p, "%lld%n", &atom[A], &consumed) != 1) return false; p += consumed; }
  size_t k; if (sscanf(p, "%zu%n", &k, &consumed) != 1) return false; p += consumed;
  diffs.clear();
  for (size_t i = 0; i < k; i++) {
    ll e; int m;
    if (sscanf(p, " %lld:%d%n", &e, &m, &consumed) != 2) return false;
    p += consumed; diffs.push_back({e, m});
  }
  for (int c = 0; c < 9; c++) {
    if (!ready(c)) continue;
    ll b = base_of(c);
    if (b < 0 || b >= n || isset(b)) return false;
    cov[b >> 6] |= 1ULL << (b & 63); comp[c].w[b >> 6] |= 1ULL << (b & 63);
    comp[c].lo = comp[c].hi = b; comp[c].on = true;
    for (auto &d : diffs) {
      if (!d.second) return false;
      if ((COMPS[c].mask & d.second) == d.second) { if (!double_comp(c, d.first)) return false; }
      else if (COMPS[c].mask & d.second) return false;  // block straddles a ready component
    }
  }
  undo.clear(); arena.clear();
  return true;
}

int main(int argc, char **argv) {
  if (argc < 5) {
    fprintf(stderr, "usage: %s a b c t|A1|resume OUTPUT [nolp] [split=D]\n       %s a b c lptest\n", argv[0], argv[0]);
    return 2;
  }
  ga = atoi(argv[1]); gb = atoi(argv[2]); gc = atoi(argv[3]);
  if (ga < 1 || gb < 0 || gc < 0 || ga > 20 || gb > 30 || gc > 30) { fprintf(stderr, "bad (a,b,c)\n"); return 2; }
  if (getenv("LPSLACK")) lp_slack = atoll(getenv("LPSLACK"));
  if (getenv("LPDROP")) lp_drop = atoi(getenv("LPDROP"));
  std::string mode = argv[4];
  for (int i = 5; i < argc; i++) {
    if (!strcmp(argv[i], "nolp")) use_lp = false;
    if (!strncmp(argv[i], "split=", 6)) split_depth = atoi(argv[i] + 6);
    if (!strncmp(argv[i], "s=", 2)) gs = atoi(argv[i] + 2);
    if (!strcmp(argv[i], "halve=all")) halve_all = true;
    if (!strncmp(argv[i], "var=", 4) && strlen(argv[i]) == 7) {
      gvX = argv[i][4] == '1'; gvY = argv[i][5] == '1'; gvZ = argv[i][6] == '1';
    }
  }
  ll v7, v5;
  n = chain_value(ga, gb, gc, v7, v5);
  NW = (int)((n + 63) / 64);
  if (gs < 1 || gs > 30) { fprintf(stderr, "bad s\n"); return 2; }
  capc[0] = ga; capc[1] = gs; capc[2] = 2; capc[3] = gb + 1; capc[4] = gc + 1;
  // E_k = the components without class k: |E_G| = val("7"),
  // |E_F| = val("7") + val("5")2^(c+1); with halve=all also E_U, E_V, E_W.
  ll E[5] = {0, 0, 0, 0, 0};
  for (int k = 0; k < 5; k++)
    for (int c = 0; c < 9; c++)
      if (!(COMPS[c].mask >> k & 1)) E[k] += 1LL << capof(COMPS[c].mask);
  if (E[4] != v7 || E[3] != v7 + v5 * (1LL << (gc + 1))) { fprintf(stderr, "halving sets\n"); return 4; }
  for (int k = 0; k < 5; k++) if (k >= 3 || halve_all) cand[k].assign(n + 1, 0);
  for (ll d = 1; d < n; d++) {
    ll k = n / d, rr = n % d, odd = (k % 2 == 0) ? rr : d - rr;
    for (int j = 0; j < 5; j++) if (!cand[j].empty()) cand[j][d] = odd <= E[j];
  }
  cov.assign(NW + 1, 0);
  for (int c = 0; c < 9; c++) comp[c].w.assign(NW + 1, 0);
  for (int A = 0; A < 6; A++) atom[A] = -1;
  if (mode == "lptest") {
    // stdin lines: n x t A1 A2 A3 p q (-1 unknown) k e1:m1 ... ek:mk ; prints caps test
    ll xx, nn;
    while (scanf("%lld %lld", &nn, &xx) == 2) {
      n = nn;
      for (int A = 0; A < 6; A++) if (scanf("%lld", &atom[A]) != 1) return 3;
      int k; if (scanf("%d", &k) != 1) return 3;
      diffs.clear();
      for (int i = 0; i < k; i++) { ll e; int m; if (scanf("%lld:%d", &e, &m) != 2) return 3; diffs.push_back({e, m}); }
      printf("%d\n", caps_ok(xx, diffs) ? 1 : 0);
    }
    return 0;
  }
  if (argc < 6) { fprintf(stderr, "missing OUTPUT\n"); return 2; }
  out = fopen(argv[5], "wx");
  if (!out) { perror("refusing to replace output"); return 2; }
  if (mode == "resume") {
    static char buf[1 << 16];
    ll jobno = 0;
    while (fgets(buf, sizeof buf, stdin)) {
      if (buf[0] != 'J') continue;
      ll n0 = nodes, s0 = solutions, j0 = jobs_out;
      clear_state();
      if (!load_state(buf)) { fprintf(stderr, "bad job\n"); return 3; }
      step(0);
      printf("{\"job\": %lld, \"nodes\": %lld, \"configurations\": %lld, \"jobs\": %lld}\n",
             jobno++, nodes - n0, solutions - s0, jobs_out - j0);
      fflush(stdout);
    }
    fflush(out);
  } else if (mode == "t" || mode == "A1") {
    atom[mode == "t" ? AT : AA1] = 0;
    activate(0);
  } else {
    fprintf(stderr, "unknown mode\n"); return 2;
  }
  fclose(out);
  printf("{\"a\": %d, \"b\": %d, \"c\": %d, \"variant\": \"%d%d%d\", \"s\": %d, \"halve_all\": %d, \"n\": %lld, \"mode\": \"%s\", \"lp\": %d, \"nodes\": %lld, "
         "\"configurations\": %lld, \"jobs\": %lld, \"bound_prunes\": %lld, \"lp_prunes\": %lld, "
         "\"candidate_prunes\": %lld, \"collisions\": %lld}\n",
         ga, gb, gc, gvX, gvY, gvZ, gs, (int)halve_all, n, mode.c_str(), use_lp, nodes, solutions, jobs_out, bound_prunes, lp_prunes,
         cand_prunes, collisions);
  return 0;
}
