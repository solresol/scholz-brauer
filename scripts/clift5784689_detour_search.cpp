// clift5784689_detour_search.cpp
//
// Independent exhaustive search for budget-attaining labellings of a source
// chain (cost n - 1 and B(n) = 2^n - 1), using the critical-path / detour
// ("loss") formulation.  C++17, standard library only.
//
//   c++ -O2 -std=c++17 -Wall -Wextra -Werror -o detour scripts/clift5784689_detour_search.cpp
//   ./detour --abc 1,0,0                       # run-generalised Clift graph (a,b,c)
//   ./detour --pairs 1+1,2+1                   # explicit parents (values), slot 0 first
//   ./detour --batch FILE --expand             # one --pairs spec per line, JSON lines out
//   ./detour --abc 5,9,3 --jobs 64 --job 7 --split-depth 6   # one independent job
//
// ---------------------------------------------------------------------------
// Model.  Vertices 0..K-1 with values 1 = v0 < ... < v_{K-1} = n; vertex h >= 1
// has parents par[h][0], par[h][1] and two in-edges, edge id 2h+slot.  A
// labelling gives every edge a shift; cap(u) = largest out-shift of u; cost =
// sum of caps.  Every vertex must be an ancestor of the sink (else rejected).
//
// Facts used (proved in the repository; re-proved here in one line each):
//  (F1) B(v) = sum over source-to-v paths of 2^(path weight); v paths.
//  (F2) B(n) = 2^n - 1 with cost <= n - 1  <=>  path weights = {0..n-1}
//       exactly and then cost = n - 1 (weights distinct by binary weight;
//       every weight <= cost).
//  (F3) The weight-(n-1) path P* has shift(e) = cap(tail e) on every edge and
//       every vertex off P* has cap 0.  (n-1 = w(P*) <= sum of caps of P*
//       tails <= cost = n-1.)  Conversely, given P*, caps C(x) >= 0 of the
//       P* vertices summing to n-1, shifts in [0, C(x)] on the other edges
//       leaving P* vertices, and shift 0 on edges leaving off-P* vertices, the
//       cost is exactly n-1, so the labelling is budget-attaining iff its path
//       weights are {0..n-1}.
//  (F4) A vertex with two parallel out-edges lies on P* (else two paths that
//       differ only in the parallel edge have equal weight).
//
// Canonical forms (symmetry).
//  (S1) Swapping the two parallel edges u->2u is a graph automorphism, and
//       their shifts always differ (equal shifts give equal-weight paths).  We
//       search only labellings with shift(slot 0) > shift(slot 1) for every
//       parallel pair.  For a pair on P* this means P* uses slot 0 (the P*
//       edge carries the cap, strictly above the other copy).  For a pair
//       whose head is off P* ("twins": both copies start detours through the
//       same off-P* vertex), the slot-0 detour along a route has smaller loss
//       than the slot-1 detour along the same route (losses differ by
//       shift(slot 1) - shift(slot 0) < 0).  Losses are valued in increasing
//       order (below), so a slot-1 detour may only be valued after its slot-0
//       twin.  --expand regenerates all 2^(#pairs) images.
//  (S2) Permutable runs.  A P* segment w -> 2w whose tail w has out-degree 2
//       (just the parallel pair) is "permutable".  In a maximal block of
//       consecutive permutable segments every source-sink path traverses all
//       of them or none (internal vertices have in-edges only from their
//       predecessor and out-edges only to their successor), and the tails'
//       caps bound no other edge, so permuting the (slot0, slot1) shift pairs
//       among them preserves every path weight and the cost.  Their single
//       detour losses are distinct, so we keep only labellings whose losses
//       increase along each run; --expand regenerates all permutations.
//
// Detours.  Fix P* = x_0 .. x_M (positions).  A detour leaves P* at x along a
// non-P* edge e, follows edges with off-P* tails (all shift 0 by F3) and stops
// at the first P* vertex y.  Every source-sink path is P* plus a set of
// detours with pairwise interior-disjoint intervals [x,y] (shared endpoints
// allowed), bijectively.  With C(x) = shift of the P* edge at x and Pre(x) =
// sum of C over earlier P* vertices, the path weight is (n-1) minus the sum of
// detour losses, loss(d) = Pre(y) - Pre(x) - shift(e), 0 <= shift(e) <= C(x).
// Every loss >= 1 (the one-detour path differs from P*), and the losses of all
// compatible detour sets must be exactly {0..n-1}.  Constraints, all
// difference constraints on Pre:  shift >= 0: Pre(y) - Pre(x) >= L;  shift <=
// C(x): Pre(y) - Pre(x+1) <= L;  detours with the same first edge share the
// shift: Pre(y1) - Pre(y2) = L1 - L2.  Two detours with the same first edge
// and the same y would have equal loss: P* is rejected at once.
//   * "single": the slot-1 copy of a parallel pair whose slot 0 is the P*
//     edge (interval of length one; its only constraint is L <= C(x)).
//   * "unit": a single, or a "chord unit": a detour that is alone in its
//     first-edge group, is not a twin, and is compatible with every single and
//     every other chord unit (chosen greedily).  Units are pairwise compatible.
//   * "Q-item": every other detour.
//
// MEX LEMMA (the branching rule).  Let V be the detours valued so far, Cov the
// losses of compatible subsets of V (all distinct, < n), m = min(N \ Cov).
// In any completion some undecided detour has loss exactly m, and no
// undecided detour has loss < m.  Proof: m < n because |Cov| < n while
// detours remain (each remaining d gives the path {d} not counted in Cov).
// m is the loss of some compatible set S; S is not inside V, so S contains an
// undecided d, and L(d) <= m because losses are positive.  If some undecided
// d' had L(d') < m, then L(d') is in Cov, = loss of some T inside V, and the
// paths {d'} and T collide.  So the undecided losses are >= m, the d in S has
// L(d) = m (and S = {d}).  Hence the search: at each node branch on which
// undecided detour gets loss m; add every new compatible-set loss m + loss(T)
// (T inside V compatible with d); fail on a repeat or a loss >= n.  Exactly
// one undecided detour gets m (two would collide), so each completion is
// reached along exactly one branch.
//
// LAZY BLOCKS.  A "block" is a set of units that every valued Q-item covers
// entirely or not at all (covers = is incompatible with).  Units of a block
// are pairwise compatible and have the same compatibility with every valued
// Q-item, so any bijection between members preserves compatibility with
// every valued detour: Cov depends only on the multiset of losses given to
// each block, not on which member has which loss.  Initially all units form
// one block.  "A unit of block B gets m" is one branch (not one per member).
// When a Q-item d is valued and cuts a block into In (covered by d) and Out,
// we branch on which of the block's valued losses go to In and Out (all
// splits within the capacities): the refinement, done only when a valued
// detour distinguishes members.  At a leaf every Q-item is valued, so blocks
// are the classes of units that no Q-item distinguishes; there the losses are
// assigned to members in every way (modulo S2) and the cap constraints are
// solved exactly.
// Coverage formula: a compatible subset of the valued detours is a compatible
// set Q of valued Q-items plus any set of valued units not covered by Q; so
// Cov = disjoint union over Q of loss(Q) + SubsetSums(values of the blocks not
// covered by Q).  New losses when an item is valued are the terms containing
// it.
//
// PRUNING (each rule is a necessary condition of every completion):
//  (P1) a new loss repeats an existing one / (P2) a new loss is >= n.
//  (P3) Bellman-Ford feasibility of the difference constraints on Pre():
//       Pre(M) - Pre(0) = n - 1, Pre nondecreasing; valued Q-items and their
//       same-first-edge equalities exactly; every undecided Q-item d has its
//       proven bounds lo_d <= L_d <= hi_d (initially lo = m by the MEX LEMMA),
//       so Pre(y) - Pre(x) >= lo_d and Pre(y) - Pre(x+1) <= hi_d, and if its
//       first edge is shared with a valued r, lo_d - L_r <= Pre(y_d) -
//       Pre(y_r) <= hi_d - L_r.  Units in blocks: for every resolution, every
//       unit's loss is at most Pre(y_u) - Pre(x_u) (= C(x) for a single), and
//       units are pairwise interior-disjoint, so for any range [a,b),
//       Pre(b) - Pre(a) >= sum over blocks B of the sum of the r_B smallest
//       eventual losses of B, r_B = number of B's members inside [a,b).  The
//       eventual losses of B are its valued ones and, for its unvalued
//       members, sorted proven lower bounds (any r_B members carry r_B
//       distinct eventual losses, whose sum is at least the sum of the r_B
//       smallest).  This holds for every assignment of losses to members.
//  (P4) Max weight: the loss of every compatible set is <= n - 1.  Using
//       valued losses and lower bounds for undecided items, the heaviest
//       compatible set among {valued Q-items, undecided Q-items that cut no
//       block, all units} must weigh <= n - 1.  (Members of a block are
//       interchangeable w.r.t. all these detours, so placing the block's
//       eventual bounds on its members in any order gives the same maximum,
//       and true losses are >= the bounds used.)
//  (P5) Symmetry S1 (twins) and S2 (runs, at leaves).
//  (P6) Look-ahead.  For an undecided item t let Cov_t be the losses of
//       valued compatible sets that are certainly compatible with t (for a
//       Q-item, blocks cut by it are left out).  In every completion the sets
//       {t} + T, T counted in Cov_t, are distinct paths different from the
//       valued ones, so the eventual loss L of t satisfies: L + c is not in
//       Cov and L + c < n for every c in Cov_t.  Together with the bounds
//       read from all-pairs shortest paths of the (necessary) P3 system,
//       L lies in Valid_t; its least (and for Q-items greatest) element bounds
//       L.  A block with u unvalued members needs u distinct values of Valid_B
//       (each member is compatible with exactly Cov_B), so its k-th smallest
//       unvalued loss is at least the k-th element of Valid_B.  Any subset of
//       Cov_t (--la-sample) and any partial scan (--la-scan, every skipped
//       candidate examined and invalid) still give valid bounds.
//  (P7) Children inherit the parent's proven bounds (a completion of a child
//       is a completion of the parent; remaining undecided losses exceed m),
//       and P3 is checked for a child before its coverage is computed.  During
//       a refinement each partial In/Out decision is checked against P3 with
//       a part's free slots bounded by the smallest of (undecided values of
//       its block) U (the block's unvalued bounds): the sorted unvalued losses
//       dominate the bound list elementwise, so this is a valid lower bound.
//  (P8) Packing.  Let Y be a set of k undecided units (units are pairwise
//       compatible) and A the losses of the valued compatible sets that are
//       compatible with every member of Y.  For distinct subsets T, T' of Y
//       the path-loss sets A + sum(T) and A + sum(T') are disjoint (distinct
//       compatible sets), so sum(T) - sum(T') is not in A - A.  With w the
//       least positive integer not in A - A, the 2^k subset sums of Y are
//       pairwise at least w apart, so sum(Y) >= (2^k - 1) w; and the set
//       (heaviest set counted in A) + Y is compatible, so
//       (2^k - 1) w + max(A) <= n - 1.  Checked for Y = all undecided units
//       and for Y = the undecided members of each block; w is computed
//       exactly up to a work cap and otherwise bounded from below by the
//       last verified value (still sound).
//  (P9) Halving parity.  For any detour d with loss L, the losses of the
//       paths compatible with d (with or without d) form X + {0, L} =
//       X disjoint-union (X + L), so every maximal run of this set in steps of
//       L has even length (first element of a run is in X, elements alternate
//       X, X+L, and the last must be in X+L).  This set is [0,n) minus Skip_d,
//       the losses of paths using a detour incompatible with d, and |Skip_d| =
//       s_d = n - 2 cntL(x_d) cntR(y_d) is structural (cntL/cntR count the
//       compatible detour sets left of x_d / right of y_d).  In [0,n) the
//       runs in steps of L are the residue classes; the number of odd ones is
//       oc(L) = (n mod L) if floor(n/L) is even, else L - (n mod L).  Removing
//       one element from a run changes the number of odd runs by exactly +-1,
//       so oc(L) <= s_d and oc(L) = s_d (mod 2).  For a block (anonymous) the
//       valued losses must be matchable to distinct members satisfying this
//       with the member's own s_u (bipartite matching), and every candidate
//       loss in P6 must satisfy it for some member.
// Leaves: losses fixed; all assignments of block losses to members (S2:
// increasing along runs) are tried; the exact system is solved by
// Bellman-Ford and every integer solution Pre() is enumerated (the feasible
// set of one variable, given the earlier ones, is an interval read from
// shortest paths), each giving explicit shifts that are re-verified by
// recomputing all n path weights.
//
// JOBS.  --split D:J:j (repeatable; --jobs J --job j --split-depth D is the
// one-level form).  At each split depth D (number of valued detours) the
// nodes this job reaches, over all critical paths in order, are numbered in
// DFS order and only those with number = j (mod J) are explored.  Jobs that
// agree on the earlier levels explore identical trees down to the next split
// depth, so numbering is consistent and, for fixed earlier choices, the J
// values of j partition the subtrees.  A node is counted (and its leaves
// reported) only by the job whose j is 0 at every deeper level, so summing
// per-job node counts over a complete job set gives the single-run count.
// ---------------------------------------------------------------------------

#include <algorithm>
#include <array>
#include <bitset>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <functional>
#include <map>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

using namespace std;
typedef long long ll;
typedef unsigned long long u64;

static inline int popc(u64 x) { return (int)bitset<64>(x).count(); }
static inline int ctz64(u64 x) { int i = 0; while (!((x >> i) & 1)) ++i; return i; }
static inline int msb64(u64 x) { int i = 63; while (!((x >> i) & 1)) --i; return i; }

static double nowSeconds() {
  using namespace std::chrono;
  return duration<double>(steady_clock::now().time_since_epoch()).count();
}

// ------------------------------------------------------------------ graph --
struct Graph {
  vector<ll> val;               // val[0] = 1, strictly increasing
  vector<array<int, 2>> par;    // par[h] for h >= 1
  vector<vector<int>> out;      // out-edge ids per vertex
  vector<string> name;
  int K() const { return (int)val.size(); }
  int tail(int e) const { return par[e >> 1][e & 1]; }
  static int head(int e) { return e >> 1; }
  bool isPar(int h) const { return h >= 1 && par[h][0] == par[h][1]; }
};

static Graph buildGraph(const vector<pair<ll, ll>>& pairs, vector<string> names) {
  Graph G;
  G.val.push_back(1);
  G.par.push_back({-1, -1});
  map<ll, int> idx;
  idx[1] = 0;
  for (auto& pq : pairs) {
    auto ip = idx.find(pq.first), iq = idx.find(pq.second);
    if (ip == idx.end() || iq == idx.end())
      throw runtime_error("parent value " + to_string(pq.first) + "+" + to_string(pq.second) +
                          " not earlier in the chain");
    if (pq.first > (ll)4e18 - pq.second) throw runtime_error("overflow");
    ll v = pq.first + pq.second;
    if (v <= G.val.back()) throw runtime_error("chain values must be strictly increasing");
    idx[v] = G.K();
    G.val.push_back(v);
    G.par.push_back({ip->second, iq->second});
  }
  if (G.K() < 2) throw runtime_error("chain must have n >= 2");
  if (G.val.back() > (ll)1 << 34) throw runtime_error("n too large for the coverage bitset");
  G.out.assign(G.K(), {});
  for (int h = 1; h < G.K(); ++h)
    for (int s = 0; s < 2; ++s) G.out[G.par[h][s]].push_back(2 * h + s);
  vector<char> live(G.K(), 0);
  live[G.K() - 1] = 1;
  for (int v = G.K() - 1; v >= 1; --v)
    if (live[v]) live[G.par[v][0]] = live[G.par[v][1]] = 1;
  for (int v = 0; v < G.K(); ++v)
    if (!live[v]) throw runtime_error("vertex " + to_string(G.val[v]) + " is not an ancestor of the sink");
  if ((int)names.size() != G.K()) {
    names.clear();
    for (ll v : G.val) names.push_back(to_string(v));
  }
  G.name = names;
  return G;
}

// The run-generalised Clift chain (a, b, c); parent order as in the spec.
static Graph buildABC(int a, int b, int c) {
  if (a < 1 || b < 0 || c < 0) throw runtime_error("need a >= 1, b >= 0, c >= 0");
  if (a + b + c > 28) throw runtime_error("(a,b,c) too large");
  vector<pair<ll, ll>> P;
  vector<string> N = {"R0"};
  ll R = 1;
  for (int i = 1; i <= a; ++i) { P.push_back({R, R}); R *= 2; N.push_back("R" + to_string(i)); }
  ll v4 = 2 * R;  P.push_back({R, R});     N.push_back("4");
  ll v5 = v4 + 1; P.push_back({v4, 1});    N.push_back("5");
  ll v7 = v5 + R; P.push_back({v5, R});    N.push_back("7");
  ll v8 = 2 * v4; P.push_back({v4, v4});   N.push_back("8");
  ll v15 = v8 + v7; P.push_back({v8, v7}); N.push_back("15");
  ll F = v15 + v8; P.push_back({v15, v8}); N.push_back("F0");
  for (int i = 1; i <= b; ++i) { P.push_back({F, F}); F *= 2; N.push_back("F" + to_string(i)); }
  ll v28 = F + v5; P.push_back({F, v5});   N.push_back("28");
  ll Gv = v28 + F; P.push_back({v28, F});  N.push_back("G0");
  for (int i = 1; i <= c; ++i) { P.push_back({Gv, Gv}); Gv *= 2; N.push_back("G" + to_string(i)); }
  ll v58 = Gv + v7; P.push_back({Gv, v7}); N.push_back("58");
  P.push_back({v58, Gv});                  N.push_back("n");
  return buildGraph(P, N);
}

static vector<pair<ll, ll>> parsePairs(const string& s) {
  vector<pair<ll, ll>> P;
  string tok;
  stringstream ss(s);
  while (getline(ss, tok, ',')) {
    size_t b = tok.find_first_not_of(" \t\r\n"), e = tok.find_last_not_of(" \t\r\n");
    if (b == string::npos) continue;
    tok = tok.substr(b, e - b + 1);
    size_t plus = tok.find('+');
    if (plus == string::npos) throw runtime_error("bad pair '" + tok + "'");
    P.push_back({stoll(tok.substr(0, plus)), stoll(tok.substr(plus + 1))});
  }
  return P;
}

// All source-sink edge paths through every vertex with parallel out-edges
// (F4), using slot 0 of every parallel pair they traverse (S1).
static vector<vector<int>> enumPstars(const Graph& G) {
  int K = G.K();
  vector<char> forced(K, 0);
  for (int h = 1; h < K; ++h)
    if (G.isPar(h)) forced[G.par[h][0]] = 1;
  vector<vector<int>> res;
  vector<int> path;
  function<void(int)> dfs = [&](int v) {
    if (v == K - 1) { res.push_back(path); return; }
    for (int e : G.out[v]) {
      int h = Graph::head(e);
      if (G.isPar(h) && (e & 1)) continue;
      bool skip = false;
      for (int u = v + 1; u < h; ++u)
        if (forced[u]) { skip = true; break; }
      if (skip) continue;
      path.push_back(e);
      dfs(h);
      path.pop_back();
    }
  };
  dfs(0);
  return res;
}

// ---------------------------------------------------------------- options --
struct SplitLevel { int depth; ll jobs, job; };
struct Options {
  int jobs = 1, job = 0, splitDepth = 0;
  vector<SplitLevel> splits;  // sorted by depth; built from --split or --jobs/--job/--split-depth
  bool expand = false, describe = true;
  ll maxLabellings = 1000;
  int onlyPstar = -1;
  double progress = 0;
  bool verify = true;
  bool lookahead = true;
  bool chordUnits = true;
  ll laSample = 1024;
  ll laScan = 24;
  bool packing = true;
  bool parity = true;
  ll packCap = 1 << 16;     // max |A| for P8
  ll packWork = 1 << 22;    // word operations for computing w
  int traceDepth = -1;
  ll traceLimit = 20;
};

static string jstr(const string& s) {
  string o = "\"";
  for (char c : s) {
    if (c == '"' || c == '\\') { o += '\\'; o += c; }
    else if (c == '\n') o += "\\n";
    else o += c;
  }
  return o + "\"";
}

struct Stats {
  vector<ll> depthNodes;
  void bump(vector<ll>& v, int d) { if ((int)v.size() <= d) v.resize(d + 1, 0); v[d]++; }
  ll nodes = 0, leaves = 0, feasibleSystems = 0, prunedBF = 0, prunedMW = 0, prunedLA = 0, prunedBF2 = 0,
     childBF = 0, splitBF = 0, prunedPack = 0, prunedParity = 0, collisions = 0, deadFull = 0, refinements = 0, ownedSubtrees = 0, maxDepth = 0;
};

typedef vector<array<ll, 2>> Shifts;  // per vertex h (index h), shifts of slot 0 and 1

// Recompute all path weights (sorted vectors) and the cost; independent of
// the detour machinery.
static bool verifyLabelling(const Graph& G, const Shifts& sh, string& why) {
  int K = G.K();
  ll n = G.val.back();
  vector<vector<ll>> W(K);
  W[0] = {0};
  vector<ll> cap(K, 0);
  for (int h = 1; h < K; ++h) {
    for (int s = 0; s < 2; ++s) {
      if (sh[h][s] < 0) { why = "negative shift"; return false; }
      cap[G.par[h][s]] = max(cap[G.par[h][s]], sh[h][s]);
    }
    const vector<ll>& A = W[G.par[h][0]];
    const vector<ll>& B = W[G.par[h][1]];
    vector<ll> C;
    C.reserve(A.size() + B.size());
    size_t i = 0, j = 0;
    while (i < A.size() || j < B.size()) {
      if (j == B.size() || (i < A.size() && A[i] + sh[h][0] <= B[j] + sh[h][1])) C.push_back(A[i++] + sh[h][0]);
      else C.push_back(B[j++] + sh[h][1]);
    }
    W[h].swap(C);
  }
  const vector<ll>& T = W[K - 1];
  if ((ll)T.size() != n) { why = "path count"; return false; }
  for (ll i = 0; i < n; ++i)
    if (T[i] != i) { why = "path weights are not 0..n-1"; return false; }
  ll cost = 0;
  for (ll c : cap) cost += c;
  if (cost != n - 1) { why = "cost != n-1"; return false; }
  return true;
}

// ------------------------------------------------------------- searcher --
class Searcher {
 public:
  static constexpr ll INF = (ll)4e18;
  const Graph& G;
  const Options& opt;
  ll n;
  int K, M;
  vector<int> verts, pedges, pos;
  // all detours
  struct Det { int x, y, edge, group, twin; bool single; vector<int> path; };
  vector<Det> dets;
  vector<vector<int>> groups;  // detour indices per first edge
  bool rejected = false;
  string rejectReason;
  // units: singles first (by segment), then chord units
  int U = 0, S = 0;
  vector<int> unitDet, ux, uy, uRun, segSingleUnit;
  vector<ll> uS, qS;  // P9: s_d of each unit / Q-item
  vector<vector<int>> unitsEndingAt;
  vector<vector<int>> runs;  // unit indices of each permutable run (length >= 2)
  // Q-items
  int D = 0;
  vector<int> qDet, qx, qy, qtwin, qgroup;
  vector<u64> qcover, qcompat;
  vector<vector<int>> qGroups;  // Q-items per first edge (units are alone in theirs)
  vector<vector<int>> qEndAt;
  // search state
  struct Block { u64 mem; vector<ll> vals; };
  struct QI { ll loss; u64 blocked; u64 dmask; };
  vector<ll> qval;
  vector<Block> blocks;
  vector<QI> qs;
  vector<u64> bits;
  ll covCount = 0, mex = 0;
  vector<ll> undo;
  vector<vector<ll>> potStack;
  int unvaluedQ = 0;
  // results
  Stats st;
  vector<Shifts> canonical, expanded;
  set<Shifts> expandedSet;
  bool truncated = false;
  vector<ll>* subtreeCounter;  // one counter per split level (shared by all P*)
  double* lastProgress;
  ll* globalNodes;
  int pstarIndex;
  double t0 = 0;
  vector<ll> ssBuf, cvBuf;
  ll traced = 0;

  Searcher(const Graph& G_, const vector<int>& pe, const Options& o, vector<ll>* ctr, double* lp, ll* gn, int pi)
      : G(G_), opt(o), subtreeCounter(ctr), lastProgress(lp), globalNodes(gn), pstarIndex(pi) {
    n = G.val.back();
    K = G.K();
    pedges = pe;
    M = (int)pe.size();
    verts.assign(1, 0);
    for (int e : pe) verts.push_back(Graph::head(e));
    pos.assign(K, -1);
    for (int j = 0; j <= M; ++j) pos[verts[j]] = j;
    // enumerate detours
    map<int, int> groupOf;
    for (int j = 0; j < M; ++j) {
      int x = verts[j];
      for (int e : G.out[x]) {
        if (e == pe[j]) continue;
        vector<int> path = {e};
        function<void(int)> walk = [&](int v) {
          if (pos[v] >= 0) {
            if (pos[v] <= j) throw runtime_error("internal: detour goes backwards");
            Det d;
            d.x = j; d.y = pos[v]; d.edge = e; d.twin = -1; d.path = path;
            d.single = path.size() == 1 && pos[v] == j + 1;
            if (d.single && !(G.isPar(v) && (e & 1) && pe[j] == (e ^ 1)))
              throw runtime_error("internal: single is not a parallel copy");
            auto it = groupOf.find(e);
            if (it == groupOf.end()) { d.group = (int)groups.size(); groupOf[e] = d.group; groups.push_back({}); }
            else d.group = it->second;
            groups[d.group].push_back((int)dets.size());
            dets.push_back(d);
            return;
          }
          for (int f : G.out[v]) {
            path.push_back(f);
            walk(Graph::head(f));
            path.pop_back();
          }
        };
        walk(Graph::head(e));
      }
    }
    // same first edge, same re-entry vertex: equal losses, impossible.
    for (auto& g : groups)
      for (size_t i = 0; i < g.size(); ++i)
        for (size_t k = i + 1; k < g.size(); ++k)
          if (dets[g[i]].y == dets[g[k]].y && !rejected) {
            rejected = true;
            rejectReason = "two detours with first edge into " + G.name[Graph::head(dets[g[i]].edge)] +
                           " re-enter P* at the same vertex " + G.name[verts[dets[g[i]].y]];
          }
    // twins (S1): slot-1 first edge into an off-P* doubling vertex
    vector<char> isTwin(dets.size(), 0);
    for (size_t d = 0; d < dets.size(); ++d) {
      int e = dets[d].edge;
      if (dets[d].single || !G.isPar(Graph::head(e))) continue;
      isTwin[d] = 1;
      if (!(e & 1)) continue;
      for (size_t d2 = 0; d2 < dets.size(); ++d2)
        if (dets[d2].edge == (e ^ 1) && dets[d2].path.size() == dets[d].path.size() &&
            equal(dets[d].path.begin() + 1, dets[d].path.end(), dets[d2].path.begin() + 1))
          dets[d].twin = (int)d2;
      if (dets[d].twin < 0) throw runtime_error("internal: twin not found");
    }
    // number of compatible detour sets must equal the number of paths, n.
    {
      vector<ll> cnt(M + 1, 0);
      cnt[0] = 1;
      vector<vector<int>> endAll(M + 1);
      for (size_t d = 0; d < dets.size(); ++d) endAll[dets[d].y].push_back((int)d);
      for (int j = 1; j <= M; ++j) {
        cnt[j] = cnt[j - 1];
        for (int d : endAll[j]) cnt[j] += cnt[dets[d].x];
      }
      if (cnt[M] != n) throw runtime_error("internal: detour sets do not biject with paths");
    }
    // P9: s_d = n - 2 cntL(x_d) cntR(y_d)
    vector<ll> sDet(dets.size(), 0);
    {
      vector<ll> cl(M + 1, 0), cr(M + 1, 0);
      vector<vector<int>> endAll(M + 1), startAll(M + 1);
      for (size_t d = 0; d < dets.size(); ++d) { endAll[dets[d].y].push_back((int)d); startAll[dets[d].x].push_back((int)d); }
      cl[0] = 1;
      for (int j = 1; j <= M; ++j) {
        cl[j] = cl[j - 1];
        for (int d : endAll[j]) cl[j] += cl[dets[d].x];
      }
      cr[M] = 1;
      for (int j = M - 1; j >= 0; --j) {
        cr[j] = cr[j + 1];
        for (int d : startAll[j]) cr[j] += cr[dets[d].y];
      }
      for (size_t d = 0; d < dets.size(); ++d) {
        sDet[d] = n - 2 * cl[dets[d].x] * cr[dets[d].y];
        if (sDet[d] < 0) throw runtime_error("internal: negative skip count");
      }
    }
    // units
    segSingleUnit.assign(M, -1);
    for (int j = 0; j < M; ++j)
      for (size_t d = 0; d < dets.size(); ++d)
        if (dets[d].single && dets[d].x == j) { segSingleUnit[j] = U; unitDet.push_back((int)d); ++U; }
    S = U;
    vector<char> isUnit(dets.size(), 0);
    for (int u = 0; u < U; ++u) isUnit[unitDet[u]] = 1;
    auto overlap = [&](int x1, int y1, int x2, int y2) { return !(y1 <= x2 || y2 <= x1); };
    if (opt.chordUnits)
      for (size_t d = 0; d < dets.size(); ++d) {
        const Det& dd = dets[d];
        if (dd.single || isTwin[d] || groups[dd.group].size() != 1) continue;
        bool ok = true;
        for (int u = 0; u < U && ok; ++u) {
          const Det& du = dets[unitDet[u]];
          if (overlap(dd.x, dd.y, du.x, du.y)) ok = false;
        }
        if (ok) { unitDet.push_back((int)d); isUnit[d] = 1; ++U; }
      }
    if (U > 64) throw runtime_error("more than 64 units");
    ux.resize(U); uy.resize(U); uS.resize(U);
    for (int u = 0; u < U; ++u) uS[u] = sDet[unitDet[u]];
    unitsEndingAt.assign(M + 1, {});
    for (int u = 0; u < U; ++u) {
      ux[u] = dets[unitDet[u]].x;
      uy[u] = dets[unitDet[u]].y;
      unitsEndingAt[uy[u]].push_back(u);
    }
    // Q-items
    map<int, int> qIndex;
    for (size_t d = 0; d < dets.size(); ++d)
      if (!isUnit[d]) { qIndex[(int)d] = D++; qDet.push_back((int)d); }
    if (D > 64) throw runtime_error("more than 64 Q-items");
    qx.resize(D); qy.resize(D); qtwin.assign(D, -1); qgroup.resize(D); qS.resize(D);
    for (int q = 0; q < D; ++q) qS[q] = sDet[qDet[q]];
    qcover.assign(D, 0); qcompat.assign(D, 0);
    qEndAt.assign(M + 1, {});
    map<int, int> qgroupIndex;
    for (int q = 0; q < D; ++q) {
      const Det& dd = dets[qDet[q]];
      qx[q] = dd.x; qy[q] = dd.y;
      if (dd.twin >= 0) qtwin[q] = qIndex.at(dd.twin);
      auto it = qgroupIndex.find(dd.group);
      if (it == qgroupIndex.end()) { qgroup[q] = (int)qGroups.size(); qgroupIndex[dd.group] = qgroup[q]; qGroups.push_back({}); }
      else qgroup[q] = it->second;
      qGroups[qgroup[q]].push_back(q);
      qEndAt[qy[q]].push_back(q);
      for (int u = 0; u < U; ++u)
        if (overlap(qx[q], qy[q], ux[u], uy[u])) qcover[q] |= 1ULL << u;
    }
    for (int q = 0; q < D; ++q)
      for (int q2 = 0; q2 < D; ++q2)
        if (!overlap(qx[q], qy[q], qx[q2], qy[q2])) qcompat[q] |= 1ULL << q2;
    for (auto& g : qGroups)  // units are alone in their first-edge group
      for (int q : g)
        if (groups[dets[qDet[q]].group].size() != g.size()) throw runtime_error("internal: unit shares a first edge");
    // permutable runs (S2), singles only
    uRun.assign(U, -1);
    {
      auto permut = [&](int s) { return segSingleUnit[s] >= 0 && G.out[verts[s]].size() == 2; };
      int j = 0;
      while (j < M) {
        if (!permut(j)) { ++j; continue; }
        int k = j;
        while (k + 1 < M && permut(k + 1)) ++k;
        if (k > j) {
          vector<int> r;
          for (int s = j; s <= k; ++s) { r.push_back(segSingleUnit[s]); uRun[segSingleUnit[s]] = (int)runs.size(); }
          runs.push_back(r);
          for (int q = 0; q < D; ++q) {  // no Q-item distinguishes run members
            int c = 0;
            for (int u : r) c += (int)((qcover[q] >> u) & 1);
            if (c != 0 && c != (int)r.size()) throw runtime_error("internal: a detour splits a permutable run");
          }
        }
        j = k + 1;
      }
    }
  }

  // ------------------------------------------------------ P9: parity --
  bool p9ok(ll L, ll sd) const {
    if (!opt.parity) return true;
    if (L <= 0) return false;
    ll q = n / L, r = n % L;
    ll oc = (q % 2 == 0) ? r : L - r;
    return oc <= sd && ((sd - oc) % 2 == 0);
  }
  bool p9any(ll L, u64 mem) const {
    if (!opt.parity) return true;
    for (int u = 0; u < U; ++u)
      if (((mem >> u) & 1) && p9ok(L, uS[u])) return true;
    return false;
  }
  // P9 for an anonymous block: the valued losses can be given to distinct
  // members each satisfying P9 with its own s_u (Kuhn's matching).
  bool p9match(u64 mem, const vector<ll>& vals) const {
    if (!opt.parity) return true;
    vector<int> owner(U, -1);
    for (size_t i = 0; i < vals.size(); ++i) {
      vector<char> seen(U, 0);
      function<bool(int)> aug = [&](int vi) -> bool {
        for (int u = 0; u < U; ++u) {
          if (!((mem >> u) & 1) || seen[u] || !p9ok(vals[vi], uS[u])) continue;
          seen[u] = 1;
          if (owner[u] < 0 || aug(owner[u])) { owner[u] = vi; return true; }
        }
        return false;
      };
      if (!aug((int)i)) return false;
    }
    return true;
  }

  // ---------------------------------------------------------- coverage --
  inline bool test(ll x) const { return (bits[x >> 6] >> (x & 63)) & 1ULL; }
  inline void setb(ll x) { bits[x >> 6] |= 1ULL << (x & 63); }
  inline void clr(ll x) { bits[x >> 6] &= ~(1ULL << (x & 63)); }
  void rollback(size_t mark) {
    while (undo.size() > mark) { clr(undo.back()); undo.pop_back(); --covCount; }
  }
  // Insert base + s for every subset sum s of U (the new path losses of one
  // family).  False on a repeat or a value >= n (P1/P2); the bits set so far
  // stay logged and the caller rolls back.
  bool addSums(ll base, const vector<ll>& Uv) {
    ll tot = base;
    for (ll v : Uv) tot += v;
    if (tot >= n) return false;
    if (test(base)) return false;
    setb(base); undo.push_back(base); ++covCount;
    ssBuf.assign(1, 0);
    for (ll v : Uv) {
      size_t k = ssBuf.size();
      for (size_t i = 0; i < k; ++i) {
        ll s = ssBuf[i] + v;
        ll x = base + s;
        if (test(x)) return false;
        setb(x); undo.push_back(x); ++covCount;
        ssBuf.push_back(s);
      }
    }
    return true;
  }
  void advanceMex() { while (mex < n && test(mex)) ++mex; }

  // ------------------------------------------------------------ bounds --
  // Per-node loss bounds of the undecided items (valid in every completion).
  struct Bounds {
    vector<ll> lo, hi;        // per Q-item (used when unvalued)
    vector<vector<ll>> fill;  // per block: sorted lower bounds of its unvalued losses
    vector<ll> fillHi;        // per block: upper bound of each unvalued loss
    vector<ll> packLB;        // per block: lower bound of the sum of its unvalued losses (P8)
  };
  Bounds uniformBounds(ll m) const {
    Bounds b;
    b.lo.assign(D, m);
    b.hi.assign(D, INF);
    b.fill.resize(blocks.size());
    b.fillHi.assign(blocks.size(), INF);
    for (size_t bi = 0; bi < blocks.size(); ++bi) b.fill[bi].assign(popc(blocks[bi].mem) - blocks[bi].vals.size(), m);
    return b;
  }
  bool boundsConsistent(const Bounds& bd) const {
    for (int q = 0; q < D; ++q)
      if (qval[q] < 0 && bd.lo[q] > bd.hi[q]) return false;
    for (size_t bi = 0; bi < blocks.size(); ++bi)
      if (!bd.fill[bi].empty() && bd.fill[bi].back() > bd.fillHi[bi]) return false;
    return true;
  }
  // Bounds for a child after the loss m is taken: all remaining undecided
  // losses exceed m (P7).
  Bounds childBase(const Bounds& bd, ll m) const {
    Bounds cb = bd;
    cb.packLB.clear();  // P8 sums refer to this node's blocks and values only
    for (int q = 0; q < D; ++q) cb.lo[q] = max(cb.lo[q], m + 1);
    for (auto& f : cb.fill)
      for (auto& x : f) x = max(x, m + 1);
    return cb;
  }

  // -------------------------------------------------------- run search --
  void resetState() {
    bits.assign((size_t)(n >> 6) + 2, 0);
    qval.assign(D, -1);
    unvaluedQ = D;
    blocks.clear();
    if (U > 0) blocks.push_back({U == 64 ? ~0ULL : ((1ULL << U) - 1), {}});
    qs.assign(1, {0, 0, 0});
    covCount = 0;
    undo.clear();
    setb(0); covCount = 1;  // P* itself, loss 0
    mex = 1;
    potStack.assign(D + U + 2, vector<ll>(M + 1, 0));
  }

  void run() {
    if (rejected) return;
    t0 = nowSeconds();
    resetState();
    node(0, ownAt(0), nullptr);
  }

  bool ownAt(int depth) const {
    for (auto& sl : opt.splits)
      if (sl.depth > depth && sl.job != 0) return false;
    return true;
  }

  bool allBlocksFull() const {
    for (auto& b : blocks)
      if ((int)b.vals.size() < popc(b.mem)) return false;
    return true;
  }

  void progressTick() {
    ++*globalNodes;
    if (opt.progress > 0 && (*globalNodes & 0xFF) == 0) {
      double t = nowSeconds();
      if (t - *lastProgress > opt.progress) {
        *lastProgress = t;
        fprintf(stderr, "[progress] P*%d nodes=%lld subtrees=%lld cov=%lld mex=%lld t=%.0fs\n", pstarIndex,
                (long long)st.nodes, (long long)(subtreeCounter->empty() ? 0 : subtreeCounter->back()),
                (long long)covCount, (long long)mex, t - t0);
      }
    }
  }

  string itemName(int x, int y) const { return G.name[verts[x]] + ">" + G.name[verts[y]]; }

  void trace(ll m, const Bounds& bd) {
    fprintf(stderr, "[trace] mex=%lld cov=%lld |", (long long)m, (long long)covCount);
    for (int q = 0; q < D; ++q) {
      if (qval[q] >= 0) fprintf(stderr, " %s=%lld", itemName(qx[q], qy[q]).c_str(), (long long)qval[q]);
      else fprintf(stderr, " %s:[%lld,%lld]", itemName(qx[q], qy[q]).c_str(), (long long)bd.lo[q],
                   (long long)(bd.hi[q] >= INF ? -1 : bd.hi[q]));
    }
    fprintf(stderr, " | blocks:");
    for (size_t bi = 0; bi < blocks.size(); ++bi) {
      fprintf(stderr, " {");
      for (int u = 0; u < U; ++u)
        if ((blocks[bi].mem >> u) & 1) fprintf(stderr, "%s ", (u < S ? G.name[verts[ux[u]]] : itemName(ux[u], uy[u])).c_str());
      fprintf(stderr, ":");
      for (ll v : blocks[bi].vals) fprintf(stderr, " %lld", (long long)v);
      fprintf(stderr, " / fill");
      for (ll v : bd.fill[bi]) fprintf(stderr, " %lld", (long long)v);
      fprintf(stderr, "}");
    }
    fprintf(stderr, "\n");
  }

  // `inh`: bounds proven at the parent, aligned with this node's blocks (P7).
  void node(int depth, bool own, const Bounds* inh) {
    // JOBS: at each split depth, explore only the subtrees whose DFS index
    // (counted over the subtrees this job explores) is = job (mod jobs).  A
    // node is counted by the job whose index is 0 at every deeper level.
    for (size_t l = 0; l < opt.splits.size(); ++l) {
      if (depth != opt.splits[l].depth) continue;
      ll idx = (*subtreeCounter)[l]++;
      if (idx % opt.splits[l].jobs != opt.splits[l].job) return;
      if (l + 1 == opt.splits.size()) st.ownedSubtrees++;
    }
    own = ownAt(depth);
    if (own) { st.nodes++; st.maxDepth = max(st.maxDepth, (ll)depth); st.bump(st.depthNodes, depth); }
    progressTick();
    if (unvaluedQ == 0 && allBlocksFull()) {
      if (own) leaf();
      return;
    }
    ll m = mex;
    if (m >= n) { if (own) st.deadFull++; return; }  // MEX LEMMA: m < n while detours remain
    potStack[depth + 1] = potStack[depth];
    vector<ll>& pot = potStack[depth + 1];
    Bounds bd = uniformBounds(m);
    if (inh) {
      for (int q = 0; q < D; ++q)
        if (qval[q] < 0) { bd.lo[q] = max(bd.lo[q], inh->lo[q]); bd.hi[q] = min(bd.hi[q], inh->hi[q]); }
      for (size_t bi = 0; bi < blocks.size(); ++bi) {
        for (size_t k = 0; k < bd.fill[bi].size(); ++k) bd.fill[bi][k] = max(bd.fill[bi][k], inh->fill[bi][k]);
        bd.fillHi[bi] = min(bd.fillHi[bi], inh->fillHi[bi]);
      }
    }
    if (!boundsConsistent(bd)) { if (own) st.prunedBF++; return; }
    if (!bfCheck(bd, pot)) { if (own) st.prunedBF++; return; }
    if (!maxWeightCheck(bd)) { if (own) st.prunedMW++; return; }
    if (opt.packing) {
      if (!packingCheck(bd.packLB)) { if (own) st.prunedPack++; return; }
      if (!bfCheck(bd, pot)) { if (own) st.prunedBF++; return; }
    }
    if (opt.lookahead) {
      if (!lookahead(bd) || !boundsConsistent(bd)) { if (own) st.prunedLA++; return; }
      if (!bfCheck(bd, pot)) { if (own) st.prunedBF2++; return; }
      if (!maxWeightCheck(bd)) { if (own) st.prunedMW++; return; }
    }
    if (depth == opt.traceDepth && traced < opt.traceLimit) { ++traced; trace(m, bd); }
    // Branch.  An item can take the loss m only if m lies within its proven
    // bounds (MEX LEMMA: L = m exactly for the chosen item).
    for (size_t bi = 0; bi < blocks.size(); ++bi)
      if ((int)blocks[bi].vals.size() < popc(blocks[bi].mem) && bd.fill[bi][0] <= m && m <= bd.fillHi[bi])
        branchUnit((int)bi, m, depth, own, bd);
    for (int q = 0; q < D; ++q)
      if (qval[q] < 0 && bd.lo[q] <= m && m <= bd.hi[q]) branchQ(q, m, depth, own, bd);
  }

  // A unit of block bi gets loss m.  New paths: m + loss(Q) + subset sums
  // of blocks uncovered by Q, for every valued Q not covering block bi.
  void branchUnit(int bi, ll m, int depth, bool own, const Bounds& bd) {
    {
      vector<ll> vv = blocks[bi].vals;
      vv.push_back(m);
      if (!p9match(blocks[bi].mem, vv)) { if (own) st.prunedParity++; return; }
    }
    Bounds cb = childBase(bd, m);
    // the member taking m had the smallest unvalued loss of the block, so the
    // k-th smallest remaining one is the (k+1)-th smallest before
    cb.fill[bi].assign(bd.fill[bi].begin() + 1, bd.fill[bi].end());
    for (auto& x : cb.fill[bi]) x = max(x, m + 1);
    blocks[bi].vals.push_back(m);
    vector<ll> pot = potStack[depth + 1];
    bool feas = bfCheck(cb, pot);
    blocks[bi].vals.pop_back();
    if (!feas) { if (own) st.childBF++; return; }
    size_t mark = undo.size();
    vector<ll> Uv;
    bool ok = true;
    for (size_t qi = 0; qi < qs.size() && ok; ++qi) {
      const QI& q = qs[qi];
      if (q.blocked & blocks[bi].mem) continue;
      Uv.clear();
      for (auto& b : blocks)
        if (!(b.mem & q.blocked)) Uv.insert(Uv.end(), b.vals.begin(), b.vals.end());
      ok = addSums(m + q.loss, Uv);
    }
    if (ok) {
      ll oldMex = mex;
      blocks[bi].vals.push_back(m);
      advanceMex();
      node(depth + 1, own, &cb);
      blocks[bi].vals.pop_back();
      mex = oldMex;
    } else if (own) st.collisions++;
    rollback(mark);
  }

  struct DistCtx {
    int q; ll m; int depth; bool own;
    Bounds cb;  // child bounds, aligned with the coarse blocks
    vector<QI> qc;
    vector<vector<ll>> fixedU;
    vector<u64> splitMask;
    vector<int> splitBlock, splitIndex;
    vector<int> inCap, outCap;
    vector<vector<ll>> inVals, outVals;
    vector<pair<ll, int>> merged;  // values of the cut blocks, decreasing
    vector<ll> pot;
  };

  // Q-item q gets loss m.
  void branchQ(int q, ll m, int depth, bool own, const Bounds& bd) {
    if (qtwin[q] >= 0 && qval[qtwin[q]] < 0) return;  // S1: slot-0 twin has the smaller loss
    if (!p9ok(m, qS[q])) { if (own) st.prunedParity++; return; }
    DistCtx c;
    c.q = q; c.m = m; c.depth = depth; c.own = own;
    c.cb = childBase(bd, m);
    c.pot = potStack[depth + 1];
    qval[q] = m;
    --unvaluedQ;
    // P3 with the coarse blocks holds for every refinement (P7)
    if (!bfCheck(c.cb, c.pot)) {
      if (own) st.childBF++;
      qval[q] = -1;
      ++unvaluedQ;
      return;
    }
    c.splitIndex.assign(blocks.size(), -1);
    for (size_t bi = 0; bi < blocks.size(); ++bi) {
      u64 in = blocks[bi].mem & qcover[q];
      if (in && in != blocks[bi].mem) {
        c.splitIndex[bi] = (int)c.splitBlock.size();
        c.splitBlock.push_back((int)bi);
        c.inCap.push_back(popc(in));
        c.outCap.push_back(popc(blocks[bi].mem & ~qcover[q]));
        for (ll v : blocks[bi].vals) c.merged.push_back({v, c.splitIndex[bi]});
      }
    }
    sort(c.merged.begin(), c.merged.end());
    reverse(c.merged.begin(), c.merged.end());
    c.inVals.assign(c.splitBlock.size(), {});
    c.outVals.assign(c.splitBlock.size(), {});
    for (auto& qq : qs) {
      if (qq.dmask & ~qcompat[q]) continue;
      c.qc.push_back(qq);
      vector<ll> Uv;
      u64 sm = 0;
      u64 blk = qq.blocked | qcover[q];
      for (size_t bi = 0; bi < blocks.size(); ++bi) {
        if (c.splitIndex[bi] >= 0) {
          if (!(blocks[bi].mem & qq.blocked)) sm |= 1ULL << c.splitIndex[bi];
        } else if (!(blocks[bi].mem & blk)) {
          Uv.insert(Uv.end(), blocks[bi].vals.begin(), blocks[bi].vals.end());
        }
      }
      c.fixedU.push_back(Uv);
      c.splitMask.push_back(sm);
    }
    size_t mark = undo.size();
    bool ok = true;
    for (size_t t = 0; t < c.qc.size() && ok; ++t) ok = addSums(m + c.qc[t].loss, c.fixedU[t]);
    if (ok) distribute(c, 0);
    else if (own) st.collisions++;
    rollback(mark);
    qval[q] = -1;
    ++unvaluedQ;
  }

  // Lower-bound lists for the parts of the cut blocks after k decisions (P7).
  void partBounds(const DistCtx& c, size_t k, int si, bool inPart, vector<ll>& ev) const {
    int bi = c.splitBlock[si];
    const vector<ll>& dec = inPart ? c.inVals[si] : c.outVals[si];
    int cap = inPart ? c.inCap[si] : c.outCap[si];
    vector<ll> pool = c.cb.fill[bi];
    for (size_t t = k; t < c.merged.size(); ++t)
      if (c.merged[t].second == si) pool.push_back(c.merged[t].first);
    sort(pool.begin(), pool.end());
    ev = dec;
    for (int t = 0; t < cap - (int)dec.size() && t < (int)pool.size(); ++t) ev.push_back(pool[t]);
    sort(ev.begin(), ev.end());
  }

  bool partialBF(DistCtx& c, size_t k) {
    vector<BBlock> bb;
    for (size_t bi = 0; bi < blocks.size(); ++bi) {
      int si = c.splitIndex[bi];
      if (si < 0) {
        BBlock x{blocks[bi].mem, blocks[bi].vals};
        x.ev.insert(x.ev.end(), c.cb.fill[bi].begin(), c.cb.fill[bi].end());
        bb.push_back(x);
      } else {
        BBlock in{blocks[bi].mem & qcover[c.q], {}}, out{blocks[bi].mem & ~qcover[c.q], {}};
        partBounds(c, k, si, true, in.ev);
        partBounds(c, k, si, false, out.ev);
        bb.push_back(in);
        bb.push_back(out);
      }
    }
    return bfCore(bb, c.cb, c.pot);
  }

  // Refinement: decide In/Out for each valued loss of the cut blocks, largest
  // first.  Out losses create new paths with q (monotone: a repeat found for a
  // partial Out set persists for every extension); each partial decision is
  // also checked against P3 (P7).
  void distribute(DistCtx& c, size_t k) {
    if (k > 0 && !partialBF(c, k)) { if (c.own) st.splitBF++; return; }
    if (k == c.merged.size()) { applyQ(c); return; }
    ll v = c.merged[k].first;
    int si = c.merged[k].second;
    if ((int)c.inVals[si].size() < c.inCap[si]) {
      c.inVals[si].push_back(v);
      distribute(c, k + 1);
      c.inVals[si].pop_back();
    }
    if ((int)c.outVals[si].size() < c.outCap[si]) {
      size_t mark = undo.size();
      bool ok = true;
      vector<ll> Uv;
      for (size_t t = 0; t < c.qc.size() && ok; ++t) {
        if (!((c.splitMask[t] >> si) & 1)) continue;
        Uv = c.fixedU[t];
        for (size_t s2 = 0; s2 < c.splitBlock.size(); ++s2)
          if ((c.splitMask[t] >> s2) & 1) Uv.insert(Uv.end(), c.outVals[s2].begin(), c.outVals[s2].end());
        ok = addSums(c.m + c.qc[t].loss + v, Uv);
      }
      if (ok) {
        c.outVals[si].push_back(v);
        distribute(c, k + 1);
        c.outVals[si].pop_back();
      } else if (c.own) st.collisions++;
      rollback(mark);
    }
  }

  void applyQ(DistCtx& c) {
    for (size_t si = 0; si < c.splitBlock.size(); ++si) {
      u64 mem = blocks[c.splitBlock[si]].mem;
      if (!p9match(mem & qcover[c.q], c.inVals[si]) || !p9match(mem & ~qcover[c.q], c.outVals[si])) {
        if (c.own) st.prunedParity++;
        return;
      }
    }
    if (c.own && !c.splitBlock.empty()) st.refinements++;
    vector<Block> saved = blocks;
    vector<Block> nb;
    Bounds cb2 = c.cb;
    cb2.fill.clear();
    cb2.fillHi.clear();
    for (size_t bi = 0; bi < saved.size(); ++bi) {
      int si = c.splitIndex[bi];
      if (si < 0) {
        nb.push_back(saved[bi]);
        cb2.fill.push_back(c.cb.fill[bi]);
        cb2.fillHi.push_back(c.cb.fillHi[bi]);
        continue;
      }
      // values were decided largest first: sort each part ascending
      Block in{saved[bi].mem & qcover[c.q], c.inVals[si]}, out{saved[bi].mem & ~qcover[c.q], c.outVals[si]};
      sort(in.vals.begin(), in.vals.end());
      sort(out.vals.begin(), out.vals.end());
      for (Block* part : {&in, &out}) {
        size_t u = popc(part->mem) - part->vals.size();
        // a part's unvalued losses are some of the block's: k-th smallest >= fill[k]
        cb2.fill.push_back(vector<ll>(c.cb.fill[bi].begin(), c.cb.fill[bi].begin() + u));
        cb2.fillHi.push_back(c.cb.fillHi[bi]);
        nb.push_back(*part);
      }
    }
    blocks = nb;
    size_t qsz = qs.size();
    for (auto& qq : c.qc) qs.push_back({qq.loss + c.m, qq.blocked | qcover[c.q], qq.dmask | (1ULL << c.q)});
    ll oldMex = mex;
    advanceMex();
    node(c.depth + 1, c.own, &cb2);
    mex = oldMex;
    qs.resize(qsz);
    blocks = saved;
  }

  // ------------------------------------------------- P6: look-ahead --
  // Appends base + SubsetSums(U), smallest values first, stopping once `out`
  // holds `cap` elements (truncation is sound, see P6).
  void gatherSums(ll base, vector<ll> Uv, vector<ll>& out, size_t cap) {
    if (out.size() >= cap) return;
    sort(Uv.begin(), Uv.end());
    size_t st0 = out.size();
    out.push_back(base);
    for (ll v : Uv) {
      size_t k = out.size();
      for (size_t i = st0; i < k; ++i) {
        if (out.size() >= cap) return;
        out.push_back(out[i] + v);
      }
    }
  }
  size_t laCap() const { return opt.laSample > 0 ? (size_t)opt.laSample : (size_t)-1; }
  // 64 "free" flags for positions p..p+63 (bit i: p+i uncovered and < n).
  u64 freeWord(ll p) const {
    if (p >= n) return 0;
    size_t w = (size_t)(p >> 6);
    int sh = (int)(p & 63);
    u64 x = ~bits[w] >> sh;
    if (sh) x |= ~bits[w + 1] << (64 - sh);
    ll rem = n - p;
    if (rem < 64) x &= (1ULL << rem) - 1;
    return x;
  }
  // Validity flags for candidates L in [a, a + 64*nw): L valid iff every
  // L + c (c in cv, which contains 0) is uncovered and < n.
  void validWindow(const vector<ll>& cv, ll a, int nw, vector<u64>& v) const {
    v.assign(nw, ~0ULL);
    for (ll c : cv) {
      u64 any = 0;
      for (int w = 0; w < nw; ++w) { v[w] &= freeWord(a + c + 64LL * w); any |= v[w]; }
      if (!any) return;
    }
  }
  static constexpr int WIN = 16;  // largest window, in words
  // P9 test against a list of skip counts (true if some s in the list fits).
  bool p9list(ll L, const vector<ll>& sl) const {
    if (!opt.parity) return true;
    for (ll sd : sl)
      if (p9ok(L, sd)) return true;
    return false;
  }
  bool validAt(const vector<ll>& cv, ll L) const {
    for (ll c : cv)
      if (L + c >= n || test(L + c)) return false;
    return true;
  }
  // Candidate intervals for P9 for one quotient q: for L > s the condition
  // oc(L) <= s holds exactly on, with q = floor(n/L): q even:
  // ceil((n-s)/q) <= L <= floor(n/q); q odd: floor(n/(q+1)) < L <=
  // floor((n+s)/(q+1)).  Union over sl, clipped to [from, to], increasing;
  // parity is still checked per candidate.
  void p9AtQ(const vector<ll>& sl, ll q, ll from, ll to, vector<pair<ll, ll>>& cur) const {
    cur.clear();
    ll Lmin = n / (q + 1) + 1, Lmax = n / q;  // L with floor(n/L) = q
    for (ll sd : sl) {
      ll a, b;
      if (q % 2 == 0) { a = max(Lmin, (n - sd + q - 1) / q); b = Lmax; }
      else { a = Lmin; b = min(Lmax, (n + sd) / (q + 1)); }
      a = max(a, from); b = min(b, to);
      if (a <= b) cur.push_back({a, b});
    }
    sort(cur.begin(), cur.end());
    size_t k = 0;
    for (size_t i = 0; i < cur.size(); ++i) {
      if (k && cur[i].first <= cur[k - 1].second + 1) cur[k - 1].second = max(cur[k - 1].second, cur[i].second);
      else cur[k++] = cur[i];
    }
    cur.resize(k);
  }
  // Up to `want` smallest valid values in [lo, hi] (ascending): L valid iff
  // P9 holds for some s in sl and every L + c (c in cv, cv contains 0) is
  // uncovered and < n.  Below max(sl) candidates are scanned in windows of
  // 1, 2, 4, ... WIN words (bit-parallel); above it only the P9 intervals
  // are tried.  At most --la-scan windows (dense part) and 64 * WIN * --la-scan
  // candidates (sparse part) are examined; if the budget runs out, `res` is
  // padded with the first unexamined candidate (a lower bound: every smaller
  // candidate was examined and invalid).  `exhausted`: the whole range was
  // examined (only then may a shortfall prune).
  void firstValid(const vector<ll>& cv, ll lo, ll hi, size_t want, vector<ll>& res, bool& exhausted,
                  const vector<ll>& sl) const {
    res.clear();
    exhausted = true;
    ll maxc = 0;
    for (ll c : cv) maxc = max(maxc, c);
    hi = min(hi, n - 1 - maxc);
    lo = max(lo, 1LL);
    ll smax = 0;
    for (ll sd : sl) smax = max(smax, sd);
    if (!opt.parity) smax = n;
    vector<u64> v;
    ll budget = opt.laScan;
    ll a = lo;
    int nw = 1;
    ll denseHi = min(hi, smax);
    while (a <= denseHi && res.size() < want) {
      if (budget-- == 0) { exhausted = false; break; }
      validWindow(cv, a, nw, v);
      for (int w = 0; w < nw && res.size() < want; ++w) {
        u64 x = v[w];
        while (x && res.size() < want) {
          ll L = a + 64LL * w + ctz64(x);
          x &= x - 1;
          if (L > denseHi) break;
          if (p9list(L, sl)) res.push_back(L);
        }
      }
      a += 64LL * nw;
      nw = min(WIN, 2 * nw);
    }
    if (!exhausted) {
      while (res.size() < want) res.push_back(a);
      return;
    }
    if (res.size() >= want || hi <= smax) return;
    ll from = max(lo, smax + 1);
    ll cbudget = 64LL * WIN * opt.laScan;
    vector<pair<ll, ll>> cur;
    for (ll q = n / from; q >= max(1LL, n / hi) && res.size() < want; --q) {
      if (cbudget-- == 0) {  // each quotient costs one unit of budget too
        exhausted = false;
        while (res.size() < want) res.push_back(max(from, n / (q + 1) + 1));
        return;
      }
      p9AtQ(sl, q, from, hi, cur);
      for (auto& x : cur)
        for (ll L = x.first; L <= x.second && res.size() < want; ++L) {
          if (cbudget-- == 0) {
            exhausted = false;
            while (res.size() < want) res.push_back(L);
            return;
          }
          if (p9list(L, sl) && validAt(cv, L)) res.push_back(L);
        }
    }
  }
  // Greatest valid value in [lo, hi], or -1 if none; budget-limited (then
  // returns an upper bound: the highest unexamined candidate).
  ll lastValid(const vector<ll>& cv, ll lo, ll hi, const vector<ll>& sl) const {
    ll maxc = 0;
    for (ll c : cv) maxc = max(maxc, c);
    hi = min(hi, n - 1 - maxc);
    lo = max(lo, 1LL);
    if (lo > hi) return -1;
    ll smax = 0;
    for (ll sd : sl) smax = max(smax, sd);
    if (!opt.parity) smax = n;
    ll cbudget = 64LL * WIN * opt.laScan;
    if (hi > smax) {
      ll from = max(lo, smax + 1);
      vector<pair<ll, ll>> cur;
      for (ll q = max(1LL, n / hi); q <= n / from; ++q) {
        if (cbudget-- == 0) return min(hi, n / q);  // upper bound: nothing above was valid
        p9AtQ(sl, q, from, hi, cur);
        for (size_t k = cur.size(); k-- > 0;)
          for (ll L = cur[k].second; L >= cur[k].first; --L) {
            if (cbudget-- == 0) return L;
            if (p9list(L, sl) && validAt(cv, L)) return L;
          }
      }
    }
    vector<u64> v;
    ll budget = opt.laScan;
    ll top = min(hi, smax);  // window covers [top - 64*nw + 1, top]
    int nw = 1;
    while (top >= lo) {
      if (budget-- == 0) return top;
      ll a = max(0LL, top - 64LL * nw + 1);
      validWindow(cv, a, nw, v);
      for (int w = nw - 1; w >= 0; --w) {
        u64 x = v[w];
        while (x) {
          int bit = msb64(x);
          ll L = a + 64LL * w + bit;
          x &= ~(1ULL << bit);
          if (L > top) continue;
          if (L < lo) return -1;
          if (!p9list(L, sl)) continue;
          return L;
        }
      }
      top = a - 1;
      nw = min(WIN, 2 * nw);
    }
    return -1;
  }

  bool lookahead(Bounds& bd) {
    int V = M + 1;
    vector<ll> dm((size_t)V * V, INF);
    auto at = [&](int a, int b) -> ll& { return dm[(size_t)a * V + b]; };
    for (int i = 0; i < V; ++i) at(i, i) = 0;
    for (auto& e : E) at((int)e[0], (int)e[1]) = min(at((int)e[0], (int)e[1]), e[2]);
    for (int k = 0; k < V; ++k)
      for (int i = 0; i < V; ++i) {
        ll ik = at(i, k);
        if (ik == INF) continue;
        for (int j = 0; j < V; ++j) {
          ll kj = at(k, j);
          if (kj == INF) continue;
          if (ik + kj < at(i, j)) at(i, j) = ik + kj;
        }
      }
    vector<ll> res;
    for (int q = 0; q < D; ++q) {
      if (qval[q] >= 0) continue;
      ll lo = bd.lo[q], hi = bd.hi[q];
      // L = Pre(y) - Pre(x) - shift, 0 <= shift <= C(x) = Pre(x+1) - Pre(x)
      if (at(qy[q], qx[q] + 1) < INF) lo = max(lo, -at(qy[q], qx[q] + 1));
      if (at(qx[q], qy[q]) < INF) hi = min(hi, at(qx[q], qy[q]));
      int r = -1;
      for (int q2 : qGroups[qgroup[q]])
        if (qval[q2] >= 0) { r = q2; break; }
      if (r >= 0) {  // L_q = L_r + Pre(y_q) - Pre(y_r)
        if (at(qy[q], qy[r]) < INF) lo = max(lo, qval[r] - at(qy[q], qy[r]));
        if (at(qy[r], qy[q]) < INF) hi = min(hi, qval[r] + at(qy[r], qy[q]));
      }
      if (lo > hi) return false;
      cvBuf.clear();
      ll fullMax = 0;
      for (auto& qq : qs) {
        if (qq.dmask & ~qcompat[q]) continue;
        u64 blk = qq.blocked | qcover[q];
        vector<ll> Uv;
        for (auto& b : blocks) {
          u64 in = b.mem & qcover[q];
          if (in && in != b.mem) continue;  // cut by q: placement unknown, left out
          if (!(b.mem & blk)) Uv.insert(Uv.end(), b.vals.begin(), b.vals.end());
        }
        ll sum = qq.loss;
        for (ll v : Uv) sum += v;
        fullMax = max(fullMax, sum);
        gatherSums(qq.loss, Uv, cvBuf, laCap());
      }
      hi = min(hi, n - 1 - fullMax);  // the largest such set with q has loss < n
      bool exhausted;
      ll sq = qS[q];
      vector<ll> slq = {sq};
      firstValid(cvBuf, lo, hi, 1, res, exhausted, slq);
      if (res.empty()) return false;
      bd.lo[q] = res[0];
      ll last = lastValid(cvBuf, res[0], hi, slq);
      if (last < 0) return false;
      bd.hi[q] = last;
    }
    for (size_t bi = 0; bi < blocks.size(); ++bi) {
      size_t u = popc(blocks[bi].mem) - blocks[bi].vals.size();
      if (!u) continue;
      ll hi = 0;
      for (int k = 0; k < U; ++k)
        if ((blocks[bi].mem >> k) & 1) hi = max(hi, at(ux[k], uy[k]));  // L <= Pre(y) - Pre(x)
      cvBuf.clear();
      ll fullMax = 0;
      for (auto& qq : qs) {
        if (qq.blocked & blocks[bi].mem) continue;
        vector<ll> Uv;
        for (auto& b : blocks)
          if (!(b.mem & qq.blocked)) Uv.insert(Uv.end(), b.vals.begin(), b.vals.end());
        ll sum = qq.loss;
        for (ll v : Uv) sum += v;
        fullMax = max(fullMax, sum);
        gatherSums(qq.loss, Uv, cvBuf, laCap());
      }
      hi = min(hi, n - 1 - fullMax);
      bd.fillHi[bi] = min(bd.fillHi[bi], hi);
      bool exhausted;
      u64 bm = blocks[bi].mem;
      vector<ll> slb;
      for (int k = 0; k < U; ++k)
        if ((bm >> k) & 1) slb.push_back(uS[k]);
      sort(slb.begin(), slb.end());
      slb.erase(unique(slb.begin(), slb.end()), slb.end());
      firstValid(cvBuf, bd.fill[bi][0], hi, u, res, exhausted, slb);
      if (res.size() < u) return false;
      for (size_t k = 0; k < u; ++k) bd.fill[bi][k] = max(bd.fill[bi][k], res[k]);
      sort(bd.fill[bi].begin(), bd.fill[bi].end());
    }
    return true;
  }

  // ------------------------------------------------------------ P3: BF --
  vector<array<ll, 3>> E;  // (a, b, w): Pre[b] - Pre[a] <= w
  void addC(int a, int b, ll w) { E.push_back({(ll)a, (ll)b, w}); }

  static bool bellmanFord(const vector<array<ll, 3>>& Ed, int V, vector<ll>& dist) {
    // Any finite start: with no negative cycle the relaxation reaches a fixed
    // point within V passes; a change in pass V+1 proves a negative cycle.
    for (int pass = 0; pass <= V + 1; ++pass) {
      bool ch = false;
      for (auto& e : Ed) {
        ll nd = dist[e[0]] + e[2];
        if (nd < dist[e[1]]) { dist[e[1]] = nd; ch = true; }
      }
      if (!ch) {
        ll z = dist[0];
        for (auto& x : dist) x -= z;
        return true;
      }
    }
    return false;
  }

  void baseConstraints() {
    E.clear();
    addC(0, M, n - 1);
    addC(M, 0, -(n - 1));
    for (int j = 0; j < M; ++j) addC(j + 1, j, 0);
  }

  void qConstraints(const Bounds* bd) {
    for (int q = 0; q < D; ++q) {
      if (qval[q] >= 0) {
        addC(qy[q], qx[q], -qval[q]);      // shift >= 0
        addC(qx[q] + 1, qy[q], qval[q]);   // shift <= C(x)
      } else if (bd) {
        addC(qy[q], qx[q], -bd->lo[q]);    // L >= lo and shift >= 0
        if (bd->hi[q] < INF) addC(qx[q] + 1, qy[q], bd->hi[q]);  // shift <= C(x) and L <= hi
      }
    }
    for (auto& g : qGroups) {
      int r = -1;
      for (int q : g)
        if (qval[q] >= 0) { r = q; break; }
      if (r < 0) continue;
      for (int q : g) {
        if (q == r) continue;
        if (qval[q] >= 0) {
          addC(qy[r], qy[q], qval[q] - qval[r]);
          addC(qy[q], qy[r], qval[r] - qval[q]);
        } else if (bd) {
          // Pre(y_q) - Pre(y_r) = L_q - L_r, with lo <= L_q <= hi
          addC(qy[q], qy[r], qval[r] - bd->lo[q]);
          if (bd->hi[q] < INF) addC(qy[r], qy[q], bd->hi[q] - qval[r]);
        }
      }
    }
  }

  // Block view for P3: members and the sorted eventual lower bounds.
  struct BBlock { u64 mem; vector<ll> ev; ll spanLB = 0; };

  bool bfCheck(const Bounds& bd, vector<ll>& pot) {
    vector<BBlock> bb;
    for (size_t bi = 0; bi < blocks.size(); ++bi) {
      BBlock x{blocks[bi].mem, blocks[bi].vals};
      x.ev.insert(x.ev.end(), bd.fill[bi].begin(), bd.fill[bi].end());
      sort(x.ev.begin(), x.ev.end());
      // P8: the members of a block are interior-disjoint and lie inside its
      // span, so Pre(span end) - Pre(span start) >= sum of all its losses
      if (bi < bd.packLB.size() && bd.packLB[bi] > 0) {
        ll fillSum = 0;
        for (ll v : bd.fill[bi]) fillSum += v;
        x.spanLB = max(bd.packLB[bi], fillSum);
        for (ll v : blocks[bi].vals) x.spanLB += v;
      }
      bb.push_back(x);
    }
    return bfCore(bb, bd, pot);
  }

  bool bfCore(const vector<BBlock>& bb, const Bounds& bd, vector<ll>& pot) {
    baseConstraints();
    qConstraints(&bd);
    // block range bounds (P3): the members inside [a,b) are interior-disjoint
    // and carry distinct eventual losses, at least the smallest entries of ev
    vector<int> blockOf(U, -1);
    for (size_t bi = 0; bi < bb.size(); ++bi)
      for (int u = 0; u < U; ++u)
        if ((bb[bi].mem >> u) & 1) blockOf[u] = (int)bi;
    vector<int> cnt(bb.size());
    vector<char> isStart(M + 1, 0);
    for (int u = 0; u < U; ++u) isStart[ux[u]] = 1;
    for (int a = 0; a < M; ++a) {
      if (!isStart[a]) continue;
      fill(cnt.begin(), cnt.end(), 0);
      ll bound = 0;
      for (int b = a + 1; b <= M; ++b) {
        bool added = false;
        for (int u : unitsEndingAt[b]) {
          if (ux[u] < a) continue;
          int k = blockOf[u];
          bound += bb[k].ev[cnt[k]++];
          added = true;
        }
        if (added) addC(b, a, -bound);
      }
    }
    for (auto& x : bb) {
      if (x.spanLB <= 0) continue;
      int sa = M, sb = 0;
      for (int u = 0; u < U; ++u)
        if ((x.mem >> u) & 1) { sa = min(sa, ux[u]); sb = max(sb, uy[u]); }
      addC(sb, sa, -x.spanLB);
    }
    vector<ll> dist = pot;
    if (!bellmanFord(E, M + 1, dist)) return false;
    pot = dist;
    return true;
  }

  // ------------------------------------------------------- P8: packing --
  // Check (2^k - 1) w + max(A) <= n - 1 for the undecided units `ymask`
  // (members of blocks; the k = popcount).  A = losses of valued compatible
  // sets compatible with all of them.  Returns false only on a violation.
  vector<u64> abits;
  // Returns false on a violation; otherwise sets sumLB to a proven lower
  // bound (2^k - 1) w' on sum(Y) (w' <= w), or 0 when skipped.
  bool packOne(u64 ymask, int k, ll& sumLB) {
    sumLB = 0;
    if (k < 1) return true;
    // A = union over valued Q-sets not covering any unit of Y of
    //     loss(Q) + SubsetSums(values of blocks not covered by Q)
    ll total = 0, maxA = 0;
    vector<pair<ll, vector<ll>>> parts;
    for (auto& q : qs) {
      if (q.blocked & ymask) continue;
      vector<ll> Uv;
      for (auto& b : blocks)
        if (!(b.mem & q.blocked)) Uv.insert(Uv.end(), b.vals.begin(), b.vals.end());
      if (Uv.size() > 40) return true;
      total += 1LL << Uv.size();
      if (total > opt.packCap) return true;  // too large: skip (sound)
      ll sum = q.loss;
      for (ll v : Uv) sum += v;
      maxA = max(maxA, sum);
      parts.push_back({q.loss, Uv});
    }
    ll room = n - 1 - maxA;
    if (room < 0) return false;
    if (k >= 62) return false;  // 2^k - 1 > n - 1 >= room with w >= 1
    ll mult = (1LL << k) - 1;
    // (2^k - 1) w <= room needs w <= limit
    ll limit = room / mult;
    if (limit < 1) return false;  // w >= 1 always
    size_t W = (size_t)(maxA >> 6) + 2;
    abits.assign(W, 0);
    for (auto& pr : parts) {
      ssBuf.assign(1, 0);
      for (ll v : pr.second) {
        size_t sz = ssBuf.size();
        for (size_t i = 0; i < sz; ++i) ssBuf.push_back(ssBuf[i] + v);
      }
      for (ll x : ssBuf) { ll y = pr.first + x; abits[y >> 6] |= 1ULL << (y & 63); }
    }
    // w = least d >= 1 such that A and A + d are disjoint (every d < w is a
    // difference of two elements of A).  We search d = 1..limit.
    ll work = 0;
    for (ll d = 1; d <= limit; ++d) {
      size_t sw = (size_t)(d >> 6);
      int sb = (int)(d & 63);
      bool hit = false;
      for (size_t i = 0; i + sw < W && !hit; ++i) {
        u64 sh = abits[i + sw] >> sb;
        if (sb && i + sw + 1 < W) sh |= abits[i + sw + 1] << (64 - sb);
        if (abits[i] & sh) hit = true;
      }
      work += (ll)W;
      if (!hit) { sumLB = mult * d; return true; }  // w = d exactly
      if (work > opt.packWork) { sumLB = mult * d; return true; }  // 1..d verified: w >= d + 1 > d
    }
    return false;  // every d <= limit is a difference: w > limit, violation
  }
  // Fills packLB per block (lower bound on the sum of its unvalued losses).
  bool packingCheck(vector<ll>& packLB) {
    packLB.assign(blocks.size(), 0);
    // per block: Y = its unvalued members (blocks are uniform w.r.t. valued
    // Q-items, so "compatible with all of Y" = "not covering the block")
    u64 mask = 0;
    int kall = 0;
    for (size_t bi = 0; bi < blocks.size(); ++bi) {
      const Block& b = blocks[bi];
      int u = popc(b.mem) - (int)b.vals.size();
      if (u <= 0) continue;
      if (!packOne(b.mem, u, packLB[bi])) return false;
      mask |= b.mem;
      kall += u;
    }
    // Y = all undecided units
    ll dummy;
    return packOne(mask, kall, dummy);
  }

  // ------------------------------------------------------- P4: weights --
  bool maxWeightCheck(const Bounds& bd) {
    vector<ll> w(U, 0);
    for (size_t bi = 0; bi < blocks.size(); ++bi) {
      const Block& b = blocks[bi];
      size_t t = 0;
      for (int u = 0; u < U; ++u)
        if ((b.mem >> u) & 1) { w[u] = t < b.vals.size() ? b.vals[t] : bd.fill[bi][t - b.vals.size()]; ++t; }
    }
    vector<ll> best(M + 1, 0);
    for (int j = 1; j <= M; ++j) {
      best[j] = best[j - 1];
      for (int u : unitsEndingAt[j]) best[j] = max(best[j], best[ux[u]] + w[u]);
      for (int q : qEndAt[j]) {
        ll wq;
        if (qval[q] >= 0) wq = qval[q];
        else {
          bool cuts = false;
          for (auto& b : blocks) {
            u64 in = b.mem & qcover[q];
            if (in && in != b.mem) { cuts = true; break; }
          }
          if (cuts) continue;
          wq = bd.lo[q];
        }
        best[j] = max(best[j], best[qx[q]] + wq);
      }
    }
    return best[M] <= n - 1;
  }

  // -------------------------------------------------------------- leaf --
  vector<ll> uval;
  void leaf() {
    st.leaves++;
    if (covCount != n) throw runtime_error("internal: leaf without full coverage");
    uval.assign(U, -1);
    vector<int> blockOf(U, -1);
    for (size_t bi = 0; bi < blocks.size(); ++bi)
      for (int u = 0; u < U; ++u)
        if ((blocks[bi].mem >> u) & 1) blockOf[u] = (int)bi;
    vector<vector<char>> used(blocks.size());
    for (size_t bi = 0; bi < blocks.size(); ++bi) used[bi].assign(blocks[bi].vals.size(), 0);
    function<void(int)> rec = [&](int u) {
      if (truncated) return;
      if (u == U) { solveExact(); return; }
      int bi = blockOf[u];
      for (size_t t = 0; t < blocks[bi].vals.size(); ++t) {
        if (used[bi][t]) continue;
        ll v = blocks[bi].vals[t];
        if (uRun[u] >= 0 && u > 0 && uRun[u - 1] == uRun[u] && v <= uval[u - 1]) continue;  // S2
        used[bi][t] = 1;
        uval[u] = v;
        rec(u + 1);
        used[bi][t] = 0;
      }
    };
    rec(0);
  }

  void exactConstraints() {
    baseConstraints();
    qConstraints(nullptr);
    for (int u = 0; u < U; ++u) {
      addC(uy[u], ux[u], -uval[u]);                       // shift >= 0
      if (uy[u] > ux[u] + 1) addC(ux[u] + 1, uy[u], uval[u]);  // shift <= C(x)
    }
  }

  void solveExact() {
    exactConstraints();
    vector<ll> dist(M + 1, 0);
    if (!bellmanFord(E, M + 1, dist)) return;
    st.feasibleSystems++;
    vector<ll> pre(M + 1, 0);
    vector<array<ll, 3>> base = E;
    enumPre(1, base, pre);
  }

  static bool sssp(const vector<array<ll, 3>>& Ed, int V, int src, bool reverse, vector<ll>& dist) {
    dist.assign(V, INF);
    dist[src] = 0;
    for (int pass = 0; pass <= V; ++pass) {
      bool ch = false;
      for (auto& e : Ed) {
        int a = (int)(reverse ? e[1] : e[0]), b = (int)(reverse ? e[0] : e[1]);
        if (dist[a] == INF) continue;
        ll nd = dist[a] + e[2];
        if (nd < dist[b]) { dist[b] = nd; ch = true; }
      }
      if (!ch) return true;
    }
    return false;
  }

  void enumPre(int i, vector<array<ll, 3>>& Ed, vector<ll>& pre) {
    if (truncated) return;
    if (i == M) {
      pre[M] = n - 1;
      emit(pre);
      return;
    }
    vector<ll> fw, bw;
    if (!sssp(Ed, M + 1, 0, false, fw) || !sssp(Ed, M + 1, 0, true, bw))
      throw runtime_error("internal: infeasible during enumeration");
    ll hi = fw[i], lo = -bw[i];  // Pre[i]-Pre[0] <= fw[i];  Pre[0]-Pre[i] <= bw[i]
    for (ll v = lo; v <= hi && !truncated; ++v) {
      Ed.push_back({0, (ll)i, v});
      Ed.push_back({(ll)i, 0, -v});
      pre[i] = v;
      enumPre(i + 1, Ed, pre);
      Ed.pop_back();
      Ed.pop_back();
    }
  }

  void emit(const vector<ll>& pre) {
    Shifts sh(K, {0, 0});
    for (int j = 0; j < M; ++j) { int e = pedges[j]; sh[e >> 1][e & 1] = pre[j + 1] - pre[j]; }
    vector<ll> detLoss(dets.size(), -1);
    for (int u = 0; u < U; ++u) detLoss[unitDet[u]] = uval[u];
    for (int q = 0; q < D; ++q) detLoss[qDet[q]] = qval[q];
    for (size_t d = 0; d < dets.size(); ++d) {
      const Det& dd = dets[d];
      ll v = pre[dd.y] - pre[dd.x] - detLoss[d];
      int e = dd.edge;
      if (groups[dd.group][0] == (int)d) sh[e >> 1][e & 1] = v;
      else if (sh[e >> 1][e & 1] != v) throw runtime_error("internal: inconsistent shared first edge");
    }
    if (opt.verify) {
      string why;
      if (!verifyLabelling(G, sh, why)) throw runtime_error("internal: emitted labelling fails: " + why);
    }
    if ((ll)canonical.size() >= opt.maxLabellings) { truncated = true; return; }
    canonical.push_back(sh);
    if (opt.expand) expandOrbit(sh);
  }

  // All images under S1 (parallel swaps) and S2 (run permutations).
  void expandOrbit(const Shifts& sh) {
    vector<Shifts> cur = {sh};
    for (auto& r : runs) {
      vector<Shifts> nxt;
      vector<int> perm(r.size());
      for (auto& L : cur) {
        for (size_t i = 0; i < r.size(); ++i) perm[i] = (int)i;
        do {
          Shifts L2 = L;
          for (size_t i = 0; i < r.size(); ++i) L2[verts[ux[r[i]] + 1]] = L[verts[ux[r[perm[i]]] + 1]];
          nxt.push_back(L2);
        } while (next_permutation(perm.begin(), perm.end()));
      }
      cur.swap(nxt);
    }
    for (int h = 1; h < K; ++h) {
      if (!G.isPar(h)) continue;
      size_t sz = cur.size();
      for (size_t i = 0; i < sz; ++i) {
        Shifts L2 = cur[i];
        swap(L2[h][0], L2[h][1]);
        cur.push_back(L2);
      }
    }
    for (auto& L : cur) {
      string why;
      if (opt.verify && !verifyLabelling(G, L, why)) throw runtime_error("internal: expanded image fails: " + why);
      if (!expandedSet.insert(L).second) throw runtime_error("internal: orbit image repeated");
      expanded.push_back(L);
    }
  }

  // ---------------------------------------------------------- describe --
  string routeJson(const Det& d) const {
    ostringstream o;
    o << "[" << jstr(G.name[G.tail(d.path[0])]);
    for (int e : d.path) o << ", " << jstr(G.name[Graph::head(e)]);
    o << "]";
    return o.str();
  }
  string describeJson() const {
    ostringstream o;
    o << "\"pstar_vertices\": [";
    for (int j = 0; j <= M; ++j) o << (j ? ", " : "") << jstr(G.name[verts[j]]);
    o << "], \"num_singles\": " << S << ", \"num_chord_units\": " << U - S << ", \"num_q_items\": " << D;
    o << ", \"singles_at\": [";
    for (int u = 0; u < S; ++u) o << (u ? ", " : "") << jstr(G.name[verts[ux[u]]]);
    o << "], \"chord_units\": [";
    for (int u = S; u < U; ++u) o << (u > S ? ", " : "") << routeJson(dets[unitDet[u]]);
    o << "], \"runs\": [";
    for (size_t r = 0; r < runs.size(); ++r) {
      o << (r ? ", " : "") << "[";
      for (size_t i = 0; i < runs[r].size(); ++i) o << (i ? ", " : "") << jstr(G.name[verts[ux[runs[r][i]]]]);
      o << "]";
    }
    o << "], \"q_items\": [";
    for (int q = 0; q < D; ++q) {
      const Det& d = dets[qDet[q]];
      o << (q ? ", " : "") << "{\"route\": " << routeJson(d) << ", \"first_edge_slot\": " << (d.edge & 1)
        << ", \"twin_of\": " << qtwin[q] << ", \"group\": " << qgroup[q] << "}";
    }
    o << "]";
    return o.str();
  }
};

static string shiftsJson(const Graph& G, const Shifts& sh) {
  ostringstream o;
  o << "[";
  for (int h = 1; h < G.K(); ++h) o << (h > 1 ? ", " : "") << "[" << sh[h][0] << ", " << sh[h][1] << "]";
  o << "]";
  return o.str();
}

static string runGraph(const Graph& G, const Options& opt) {
  double t0 = nowSeconds();
  ostringstream o;
  ll n = G.val.back();
  o << "{\"n\": " << n << ", \"values\": [";
  for (int i = 0; i < G.K(); ++i) o << (i ? ", " : "") << G.val[i];
  o << "], \"parents\": [";
  for (int h = 1; h < G.K(); ++h) o << (h > 1 ? ", " : "") << "[" << G.val[G.par[h][0]] << ", " << G.val[G.par[h][1]] << "]";
  o << "], \"names\": [";
  for (int i = 0; i < G.K(); ++i) o << (i ? ", " : "") << jstr(G.name[i]);
  o << "], \"jobs\": " << opt.jobs << ", \"job\": " << opt.job << ", \"split_depth\": " << opt.splitDepth
    << ", \"splits\": [";
  for (size_t l = 0; l < opt.splits.size(); ++l)
    o << (l ? ", " : "") << "[" << opt.splits[l].depth << ", " << opt.splits[l].jobs << ", " << opt.splits[l].job << "]";
  o << "]"
    << ", \"options\": {\"lookahead\": " << (opt.lookahead ? "true" : "false")
    << ", \"chord_units\": " << (opt.chordUnits ? "true" : "false") << ", \"la_sample\": " << opt.laSample
    << ", \"la_scan\": " << opt.laScan << "}";
  vector<vector<int>> ps = enumPstars(G);
  o << ", \"num_pstars\": " << ps.size() << ", \"pstars\": [";
  vector<ll> subtreeCounter(opt.splits.size(), 0);
  ll totalNodes = 0, totalLab = 0, totalExp = 0, gnodes = 0;
  double lastProgress = nowSeconds();
  bool anyTrunc = false;
  bool first = true;
  for (size_t i = 0; i < ps.size(); ++i) {
    if (opt.onlyPstar >= 0 && (int)i != opt.onlyPstar) continue;
    double t1 = nowSeconds();
    Searcher s(G, ps[i], opt, &subtreeCounter, &lastProgress, &gnodes, (int)i);
    s.run();
    double t2 = nowSeconds();
    if (!first) o << ", ";
    first = false;
    o << "{\"index\": " << i << ", ";
    if (opt.describe) o << s.describeJson() << ", ";
    if (s.rejected) o << "\"rejected\": " << jstr(s.rejectReason) << ", ";
    const Stats& t = s.st;
    o << "\"nodes\": " << t.nodes << ", \"leaves\": " << t.leaves << ", \"feasible_systems\": " << t.feasibleSystems
      << ", \"pruned_bf\": " << t.prunedBF << ", \"pruned_maxweight\": " << t.prunedMW
      << ", \"pruned_lookahead\": " << t.prunedLA << ", \"pruned_bf_after_lookahead\": " << t.prunedBF2
      << ", \"child_pruned_bf\": " << t.childBF << ", \"split_pruned_bf\": " << t.splitBF
      << ", \"pruned_packing\": " << t.prunedPack << ", \"pruned_parity\": " << t.prunedParity
      << ", \"collisions\": " << t.collisions << ", \"dead_full\": " << t.deadFull
      << ", \"refinements\": " << t.refinements << ", \"owned_subtrees\": " << t.ownedSubtrees
      << ", \"max_depth\": " << t.maxDepth << ", \"seconds\": " << (t2 - t1);
    o << ", \"depth_nodes\": [";
    for (size_t k = 0; k < t.depthNodes.size(); ++k) o << (k ? ", " : "") << t.depthNodes[k];
    o << "]";
    o << ", \"result\": " << jstr(s.canonical.empty() ? "no labelling" : "labellings found");
    o << ", \"truncated\": " << (s.truncated ? "true" : "false");
    o << ", \"labellings\": [";
    for (size_t k = 0; k < s.canonical.size(); ++k) o << (k ? ", " : "") << shiftsJson(G, s.canonical[k]);
    o << "]";
    if (opt.expand) {
      o << ", \"expanded\": [";
      for (size_t k = 0; k < s.expanded.size(); ++k) o << (k ? ", " : "") << shiftsJson(G, s.expanded[k]);
      o << "]";
    }
    o << "}";
    totalNodes += t.nodes;
    totalLab += (ll)s.canonical.size();
    totalExp += (ll)s.expanded.size();
    anyTrunc = anyTrunc || s.truncated;
  }
  o << "], \"total_nodes\": " << totalNodes << ", \"total_subtrees_at_split\": "
    << (subtreeCounter.empty() ? 0 : subtreeCounter.back()) << ", \"subtrees_per_level\": [";
  for (size_t l = 0; l < subtreeCounter.size(); ++l) o << (l ? ", " : "") << subtreeCounter[l];
  o << "]"
    << ", \"total_canonical_labellings\": " << totalLab;
  if (opt.expand) o << ", \"total_expanded_labellings\": " << totalExp;
  o << ", \"truncated\": " << (anyTrunc ? "true" : "false");
  o << ", \"result\": " << jstr(totalLab ? "labellings found" : "no labelling");
  o << ", \"seconds\": " << (nowSeconds() - t0) << "}";
  return o.str();
}

static void usage() {
  fprintf(stderr,
          "usage: detour (--abc A,B,C | --pairs P1+Q1,P2+Q2,... | --batch FILE)\n"
          "              [--jobs J --job j --split-depth D | --split D:J:j ...] [--pstar I] [--expand]\n"
          "              [--max-labellings N] [--no-describe] [--no-verify] [--progress SECONDS]\n"
          "              [--no-lookahead] [--no-chord-units] [--no-packing] [--no-parity] [--pack-cap K]\n"
          "              [--la-sample K (0 = all)] [--la-scan K]\n"
          "              [--trace-depth D --trace-limit N]\n");
}

int main(int argc, char** argv) {
  Options opt;
  string abc, pairs, batch;
  for (int i = 1; i < argc; ++i) {
    string a = argv[i];
    auto need = [&]() -> string {
      if (i + 1 >= argc) { usage(); exit(2); }
      return argv[++i];
    };
    if (a == "--abc") abc = need();
    else if (a == "--pairs") pairs = need();
    else if (a == "--batch") batch = need();
    else if (a == "--jobs") opt.jobs = stoi(need());
    else if (a == "--job") opt.job = stoi(need());
    else if (a == "--split-depth") opt.splitDepth = stoi(need());
    else if (a == "--split") {
      string v = need();
      SplitLevel sl;
      long long d, J, j;
      if (sscanf(v.c_str(), "%lld:%lld:%lld", &d, &J, &j) != 3 || J < 1 || j < 0 || j >= J || d < 0) { usage(); return 2; }
      sl.depth = (int)d; sl.jobs = J; sl.job = j;
      opt.splits.push_back(sl);
    }
    else if (a == "--pstar") opt.onlyPstar = stoi(need());
    else if (a == "--expand") opt.expand = true;
    else if (a == "--max-labellings") opt.maxLabellings = stoll(need());
    else if (a == "--no-describe") opt.describe = false;
    else if (a == "--no-verify") opt.verify = false;
    else if (a == "--progress") opt.progress = stod(need());
    else if (a == "--no-lookahead") opt.lookahead = false;
    else if (a == "--no-chord-units") opt.chordUnits = false;
    else if (a == "--no-packing") opt.packing = false;
    else if (a == "--no-parity") opt.parity = false;
    else if (a == "--pack-cap") opt.packCap = stoll(need());
    else if (a == "--la-sample") opt.laSample = stoll(need());
    else if (a == "--la-scan") opt.laScan = stoll(need());
    else if (a == "--trace-depth") opt.traceDepth = stoi(need());
    else if (a == "--trace-limit") opt.traceLimit = stoll(need());
    else { usage(); return 2; }
  }
  if (opt.jobs < 1 || opt.job < 0 || opt.job >= opt.jobs) { usage(); return 2; }
  if (opt.jobs > 1) {
    if (!opt.splits.empty()) { usage(); return 2; }
    opt.splits.push_back({opt.splitDepth, opt.jobs, opt.job});
  }
  sort(opt.splits.begin(), opt.splits.end(), [](const SplitLevel& x, const SplitLevel& y) { return x.depth < y.depth; });
  for (size_t l = 1; l < opt.splits.size(); ++l)
    if (opt.splits[l].depth == opt.splits[l - 1].depth) { usage(); return 2; }
  try {
    if (!batch.empty()) {
      ifstream in(batch);
      if (!in) throw runtime_error("cannot open batch file");
      string line;
      while (getline(in, line)) {
        if (line.find('+') == string::npos) continue;
        try {
          Graph G = buildGraph(parsePairs(line), {});
          printf("%s\n", runGraph(G, opt).c_str());
        } catch (const exception& ex) {
          printf("{\"spec\": %s, \"error\": %s}\n", jstr(line).c_str(), jstr(ex.what()).c_str());
        }
        fflush(stdout);
      }
      return 0;
    }
    Graph G;
    if (!abc.empty()) {
      int a, b, c;
      if (sscanf(abc.c_str(), "%d,%d,%d", &a, &b, &c) != 3) throw runtime_error("bad --abc");
      G = buildABC(a, b, c);
    } else if (!pairs.empty()) {
      G = buildGraph(parsePairs(pairs), {});
    } else {
      usage();
      return 2;
    }
    printf("%s\n", runGraph(G, opt).c_str());
  } catch (const exception& ex) {
    printf("{\"error\": %s}\n", jstr(ex.what()).c_str());
    return 1;
  }
  return 0;
}
