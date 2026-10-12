// planecert.h (s443): SAT-leaf certificates for the lifting test `PL.ltP pts k` (s443/S4/PlaneLift.lean).
// For a complete assignment asg (a decomposition (a_e, b_e, c_e) of T mod E), the certificate lists rank facts
// (X, r, F, G): every matrix T(X) + sum_{e in l} b_e c_e^T has a 3x3 block [f_i^T M g_j] of rank >= r.  The facts must
// cover every k-subset S of the nonzero points of E: some fact has #{p in S : X(p) = 1} < r.
// The block code of M: bit 3i+j = f_i^T M g_j.  T(X) rows follow S7L.txrow: bit z of row y is set iff y%3 == z/3 and
// X bit 3*(z%3) + y/3.  The Lean check (factOK): the set reachable from blkT under XOR with every term block blkN(e)
// avoids LOW(r-1) (codes of rank <= r-1).
// Search per functional X (one lift of each nonzero xi in E*): the largest r <= 3 with
//   (1) a V-free block: F of dim r, G of dim r in (span{c_e : F b_e != 0})^perp with F T(X) G^T of rank r;
//   (2) (r = 3, if (1) fails) a transversal block: F of dim 3 whose affine space A + span{x_e c_e^T} (A = F T(X), x_e = F b_e)
//       has small dimension and only rank-3 elements, and G (dim 3) meeting none of their kernels.
#pragma once
#include <bits/stdc++.h>
namespace g7p {
static int PQ[3] = {0, 0, 0};
static int K = 3;
static std::vector<int> PTS;     // the nonzero points of E (comb(x), x = 1..2^m-1)
static long long nfail = 0, nfacts = 0, nsat = 0, nvfree = 0, ntrans = 0;
struct Fact { int X = 0, r = 0, F[3] = {0, 0, 0}, G[3] = {0, 0, 0}; };
static inline int dot(int a, int b) { return __builtin_parity(a & b); }
static inline int txrow(int X, int y) {
  int row = 0;
  for (int z = 0; z < 9; z++) if ((y % 3) == (z / 3) && ((X >> (3 * (z % 3) + y / 3)) & 1)) row |= 1 << z;
  return row;
}
static inline int outerC(int x, int y) { int c = 0; for (int k = 0; k < 9; k++) if (((x >> (k / 3)) & 1) && ((y >> (k % 3)) & 1)) c |= 1 << k; return c; }
static inline int vcB(const int* F, int b) { int v = 0; for (int i = 0; i < 3; i++) if (dot(F[i], b)) v |= 1 << i; return v; }
static inline int rowFT(int f, int X) { int r = 0; for (int y = 0; y < 9; y++) if ((f >> y) & 1) r ^= txrow(X, y); return r; }  // f^T T(X)
static int blkT(const int* F, const int* G, int X) {
  int c = 0;
  for (int i = 0; i < 3; i++) { int a = rowFT(F[i], X); for (int j = 0; j < 3; j++) if (dot(a, G[j])) c |= 1 << (3 * i + j); }
  return c;
}
static int rank3(int code) {
  int bas[3] = {0, 0, 0}, rk = 0;
  for (int i = 0; i < 3; i++) { int v = (code >> (3 * i)) & 7; while (v) { int h = 31 - __builtin_clz(v); if (!bas[h]) { bas[h] = v; rk++; break; } v ^= bas[h]; } }
  return rk;
}
static int rankRows(const std::vector<int>& rows) {
  int bas[32] = {0}, rk = 0;
  for (int v0 : rows) { int v = v0; while (v) { int h = 31 - __builtin_clz(v); if (!bas[h]) { bas[h] = v; rk++; break; } v ^= bas[h]; } }
  return rk;
}
// the Lean check, exactly: closure of {blkT} under XOR with blkN(e) (skipping zero blocks) avoids codes of rank <= r-1
static bool factOK(const std::vector<std::array<int, 3>>& asg, const Fact& f) {
  if (f.r < 1 || f.r > 3) return false;
  std::bitset<512> S; S[blkT(f.F, f.G, f.X)] = 1;
  for (auto& e : asg) {
    int v = outerC(vcB(f.F, e[1]), vcB(f.G, e[2]));
    if (!v) continue;
    std::bitset<512> T2;
    for (int w = 0; w < 512; w++) if (S[w]) T2[w ^ v] = 1;
    S |= T2;
  }
  for (int w = 0; w < 512; w++) if (S[w] && rank3(w) <= f.r - 1) return false;
  return true;
}
// r-dim subspaces of F2^9 by reduced echelon bases (highest-bit pivots)
static const std::vector<std::array<int, 3>>& subspaces(int r) {
  static std::vector<std::array<int, 3>> S[4]; static bool done[4] = {false, false, false, false};
  if (done[r]) return S[r];
  std::vector<int> piv(r);
  std::function<void(int, int)> choose = [&](int i, int start) {
    if (i == r) {
      std::vector<int> fb[3]; int pm = 0; for (int a = 0; a < r; a++) pm |= 1 << piv[a];
      for (int a = 0; a < r; a++) for (int b = 0; b < piv[a]; b++) if (!((pm >> b) & 1)) fb[a].push_back(b);
      int tot = 0; for (int a = 0; a < r; a++) tot += fb[a].size();
      for (long long m = 0; m < (1LL << tot); m++) {
        std::array<int, 3> v = {0, 0, 0}; int k = 0;
        for (int a = 0; a < r; a++) { v[a] = 1 << piv[a]; for (int b : fb[a]) { if ((m >> k) & 1) v[a] |= 1 << b; k++; } }
        S[r].push_back(v);
      }
      return;
    }
    for (int p = start; p < 9; p++) { piv[i] = p; choose(i + 1, p + 1); }
  };
  choose(0, 0); done[r] = true; return S[r];
}
// (1) V-free block of rank r for X
static bool vfree(const std::vector<std::array<int, 3>>& asg, int X, int r, Fact& out) {
  for (auto& F : subspaces(r)) {
    int bas[9] = {0}, rk = 0;
    for (auto& e : asg) {
      bool nz = false; for (int a = 0; a < r; a++) if (dot(F[a], e[1])) nz = true;
      if (!nz) continue;
      int x = e[2]; while (x) { int h = 31 - __builtin_clz(x); if (!bas[h]) { bas[h] = x; rk++; break; } x ^= bas[h]; }
      if (9 - rk < r) break;
    }
    if (9 - rk < r) continue;
    std::vector<int> wl; for (int h = 0; h < 9; h++) if (bas[h]) wl.push_back(bas[h]);
    // a basis of the perp space
    std::vector<int> pbl; int pb[9] = {0}, prk = 0;
    for (int g = 1; g < 512 && prk < 9 - rk; g++) {
      bool ok = true; for (int w : wl) if (dot(g, w)) { ok = false; break; }
      if (!ok) continue;
      int x = g; while (x) { int h = 31 - __builtin_clz(x); if (!pb[h]) { pb[h] = x; prk++; pbl.push_back(g); break; } x ^= pb[h]; }
    }
    int A[3]; for (int a = 0; a < r; a++) A[a] = rowFT(F[a], X);
    // choose r perp vectors g with [A_a . g] of rank r (greedy over subsets of the perp basis)
    int d = pbl.size(); if (d > 9) d = 9;
    std::vector<int> cols(d); for (int j = 0; j < d; j++) { int c = 0; for (int a = 0; a < r; a++) if (dot(A[a], pbl[j])) c |= 1 << a; cols[j] = c; }
    if (rankRows(cols) < r) continue;
    // greedy independent columns
    std::vector<int> pick; int cb[3] = {0, 0, 0};
    for (int j = 0; j < d && (int)pick.size() < r; j++) { int x = cols[j]; while (x) { int h = 31 - __builtin_clz(x); if (!cb[h]) { cb[h] = x; pick.push_back(j); break; } x ^= cb[h]; } }
    Fact f; f.X = X; f.r = r;
    for (int a = 0; a < 3; a++) f.F[a] = a < r ? F[a] : 0;
    for (int j = 0; j < 3; j++) f.G[j] = j < r ? pbl[pick[j]] : 0;
    if (factOK(asg, f)) { out = f; return true; }
  }
  return false;
}
// (2) transversal block of rank 3 for X
static bool transversal(const std::vector<std::array<int, 3>>& asg, int X, Fact& out, int maxd = 3) {
  static std::mt19937_64 rng(12345);
  for (auto& F : subspaces(3)) {
    int A[3]; for (int a = 0; a < 3; a++) A[a] = rowFT(F[a], X);
    // generators x_e c_e^T as 27-bit (row a: bits 9a..9a+8)
    std::vector<int> gens; int gb[27] = {0}; int gd = 0; bool big = false;
    for (auto& e : asg) {
      int x = vcB(F.data(), e[1]); if (!x) continue;
      int m = 0; for (int a = 0; a < 3; a++) if ((x >> a) & 1) m |= e[2] << (9 * a);
      int v = m; while (v) { int h = 31 - __builtin_clz(v); if (!gb[h]) { gb[h] = v; gd++; gens.push_back(m); break; } v ^= gb[h]; }
      if (gd > maxd) { big = true; break; }
    }
    if (big) continue;
    int a0 = A[0] | (A[1] << 9) | (A[2] << 18);
    std::vector<int> elems; bool ok = true;
    for (int s = 0; s < (1 << gd) && ok; s++) {
      int m = a0; for (int j = 0; j < gd; j++) if ((s >> j) & 1) m ^= gens[j];
      std::vector<int> rows = {m & 511, (m >> 9) & 511, (m >> 18) & 511};
      if (rankRows(rows) < 3) ok = false; else elems.push_back(m);
    }
    if (!ok) continue;
    for (int tries = 0; tries < 20000; tries++) {
      Fact f; f.X = X; f.r = 3; for (int a = 0; a < 3; a++) f.F[a] = F[a];
      for (int j = 0; j < 3; j++) f.G[j] = 1 + (int)(rng() % 511);
      if (rankRows({f.G[0], f.G[1], f.G[2]}) < 3) continue;
      bool all = true;
      for (int m : elems) { int code = 0; for (int a = 0; a < 3; a++) for (int j = 0; j < 3; j++) if (dot((m >> (9 * a)) & 511, f.G[j])) code |= 1 << (3 * a + j);
        if (rank3(code) < 3) { all = false; break; } }
      if (all && factOK(asg, f)) { out = f; return true; }
    }
  }
  return false;
}
static int cntX(int X, const std::vector<int>& S) { int c = 0; for (int p : S) if (dot(p, X)) c++; return c; }
// the facts for one decomposition (empty if no cover).  Phase 1: per xi the best V-free fact of rank <= 2; phase 2 (only
// if some k-subset is uncovered): rank-3 facts (V-free, then transversal) on the xi that would cover an uncovered subset.
static std::vector<Fact> facts(const std::vector<std::array<int, 3>>& asg) {
  int m = 0; while ((1 << m) - 1 < (int)PTS.size()) m++;
  std::vector<int> Xs;
  for (int xi = 1; xi < (1 << m); xi++) {
    int X = -1; for (int c = 1; c < 512 && X < 0; c++) { bool f = true; for (int j = 0; j < m; j++) if (dot(c, PQ[j]) != ((xi >> j) & 1)) f = false; if (f) X = c; }
    Xs.push_back(X);
  }
  std::vector<std::vector<int>> subs;
  int n = PTS.size();
  std::function<void(int, std::vector<int>&)> rec = [&](int i, std::vector<int>& cur) {
    if ((int)cur.size() == K) { subs.push_back(cur); return; }
    if (i == n) return;
    cur.push_back(PTS[i]); rec(i + 1, cur); cur.pop_back(); rec(i + 1, cur);
  };
  std::vector<int> cur; rec(0, cur);
  std::vector<Fact> best(Xs.size()); std::vector<char> have(Xs.size(), 0);
  for (size_t i = 0; i < Xs.size(); i++) {
    Fact f;
    if (vfree(asg, Xs[i], 2, f)) { best[i] = f; have[i] = 1; nvfree++; }
    else if (vfree(asg, Xs[i], 1, f)) { best[i] = f; have[i] = 1; nvfree++; }
  }
  auto coveredBy = [&](const Fact& f, const std::vector<int>& S) { return cntX(f.X, S) < f.r; };
  auto uncovered = [&]() { std::vector<int> u; for (size_t s = 0; s < subs.size(); s++) { bool c = false; for (size_t i = 0; i < Xs.size() && !c; i++) if (have[i] && coveredBy(best[i], subs[s])) c = true; if (!c) u.push_back(s); } return u; };
  auto un = uncovered();
  if (!un.empty()) {
    // rank-3 candidates: xi with cnt <= 2 on some uncovered subset, most-covering first
    std::vector<std::pair<int, int>> cand;
    for (size_t i = 0; i < Xs.size(); i++) { int c = 0; for (int s : un) if (cntX(Xs[i], subs[s]) <= 2) c++; if (c) cand.push_back({-c, (int)i}); }
    std::sort(cand.begin(), cand.end());
    for (auto& ci : cand) {
      int i = ci.second;
      bool need = false; for (int s : uncovered()) if (cntX(Xs[i], subs[s]) <= 2) need = true;
      if (!need) continue;
      Fact f;
      if (vfree(asg, Xs[i], 3, f)) { best[i] = f; have[i] = 1; nvfree++; }
      else if (transversal(asg, Xs[i], f)) { best[i] = f; have[i] = 1; ntrans++; }
      if (uncovered().empty()) break;
    }
    if (!uncovered().empty()) return {};
  }
  // greedy minimal cover among the found facts
  std::vector<char> covered(subs.size(), 0); std::vector<Fact> out; std::vector<char> used(Xs.size(), 0);
  while (true) {
    int bi = -1, bc = 0;
    for (size_t i = 0; i < Xs.size(); i++) if (have[i] && !used[i]) {
      int c = 0; for (size_t s = 0; s < subs.size(); s++) if (!covered[s] && coveredBy(best[i], subs[s])) c++;
      if (c > bc) { bc = c; bi = i; } }
    if (bi < 0) break;
    used[bi] = 1; out.push_back(best[bi]);
    for (size_t s = 0; s < subs.size(); s++) if (coveredBy(best[bi], subs[s])) covered[s] = 1;
  }
  for (size_t s = 0; s < subs.size(); s++) if (!covered[s]) return {};
  return out;
}

// ------------------------------------------------------------------ witness facts (PL.ltW, s443/S4/PlaneW.lean)
struct WFact { int X = 0, r = 0, side = 0, B[3] = {0, 0, 0}, Q[8] = {0, 0, 0, 0, 0, 0, 0, 0}; };
static inline int colTG(int X, int g) { int c = 0; for (int y = 0; y < 9; y++) if (dot(txrow(X, y), g)) c |= 1 << y; return c; }   // T(X) g
// a witness for v outside span(gens): some z with z.gens = 0 and z.v = 1 (or -1)
static int witness(int v, const std::vector<int>& gens) {
  int bas[9] = {0};
  for (int x0 : gens) { int x = x0; while (x) { int h = 31 - __builtin_clz(x); if (!bas[h]) { bas[h] = x; break; } x ^= bas[h]; } }
  { int x = v; while (x) { int h = 31 - __builtin_clz(x); if (!bas[h]) break; x ^= bas[h]; } if (!x) return -1; }
  for (int z = 1; z < 512; z++) { if (!dot(z, v)) continue; bool ok = true; for (int g : gens) if (dot(z, g)) { ok = false; break; } if (ok) return z; }
  return -1;
}
// the Lean check, exactly
static bool wfactOK(const std::vector<std::array<int, 3>>& asg, const WFact& f) {
  if (f.r < 1 || f.r > 3) return false;
  for (int l = 1; l < (1 << f.r); l++) {
    int c = 0; for (int i = 0; i < 3; i++) if ((l >> i) & 1) c ^= f.B[i];
    int w = f.side == 0 ? c : f.Q[l], z = f.side == 0 ? f.Q[l] : c;
    for (auto& e : asg) if (dot(w, e[1]) && dot(z, e[2])) return false;
    if (!dot(rowFT(w, f.X), z)) return false;
  }
  return true;
}
// best witness fact for X: per side, the good vectors with witnesses, then the largest r <= 3 subspace inside
static bool bestW(const std::vector<std::array<int, 3>>& asg, int X, int rmax, WFact& out) {
  out.r = 0;
  for (int side = 0; side < 2; side++) {
    int wit[512]; bool good[512];
    for (int v = 1; v < 512; v++) {
      std::vector<int> g; for (auto& e : asg) { if (side == 0 ? dot(v, e[1]) : dot(v, e[2])) g.push_back(side == 0 ? e[2] : e[1]); }
      int vec = side == 0 ? rowFT(v, X) : colTG(X, v);
      wit[v] = witness(vec, g); good[v] = wit[v] > 0;
    }
    good[0] = false;
    // search subspaces greedily-exhaustively up to rmax
    std::vector<int> base; int bestr = 0; std::vector<int> bestb;
    std::function<bool(int)> ext = [&](int start) -> bool {
      if ((int)base.size() > bestr) { bestr = base.size(); bestb = base; }
      if (bestr >= rmax) return true;
      for (int w = start; w < 512; w++) {
        if (!good[w]) continue; bool ok = true; int n = 1 << base.size();
        for (int sm = 1; sm < n && ok; sm++) { int v = w; for (size_t i = 0; i < base.size(); i++) if ((sm >> i) & 1) v ^= base[i]; if (!good[v]) ok = false; }
        if (!ok) continue;
        base.push_back(w); bool done = ext(w + 1); base.pop_back(); if (done) return true;
      }
      return false;
    };
    ext(1);
    if (bestr > out.r) {
      WFact f; f.X = X; f.r = bestr; f.side = side;
      for (int i = 0; i < bestr; i++) f.B[i] = bestb[i];
      for (int l = 1; l < (1 << bestr); l++) { int c = 0; for (int i = 0; i < bestr; i++) if ((l >> i) & 1) c ^= bestb[i]; f.Q[l] = wit[c]; }
      if (wfactOK(asg, f)) out = f;
    }
    if (out.r >= rmax) break;
  }
  return out.r > 0;
}
// ------------------------------------------------------------------ lift3 entries (PL.ltW3): a guessed term at pc
// For an uncovered k-subset S and a point pc in S: every lift has a term u v^T at pc (u, v != 0).  At a functional X with
// X(pc) = 1 and fewer than r other points of S, T(X) + sum_l N_e + u v^T is a sum of fewer than r rank-1 matrices.  So it
// suffices that for every u some fact of rank r on the coset T(X) + u v^T + V holds for every v (u-free: every pair's w
// is orthogonal to u), or (survivors) for every v some fact holds at (u, v).
struct SFact { WFact f; };
struct L3Entry { std::vector<int> S; int c = 0; std::vector<WFact> ufacts; std::vector<std::pair<int, std::vector<WFact>>> surv; };
static long long nl3 = 0, nl3fail = 0, nl3surv = 0, nl3vf = 0, nl3uf = 0;
// a fact is valid at shift (u, v): every pair kills the terms and w^T (T(X) + u v^T) z = 1
static bool sfactOK(const std::vector<std::array<int, 3>>& asg, const WFact& f, int u, int v) {
  if (f.r < 1 || f.r > 3) return false;
  for (int l = 1; l < (1 << f.r); l++) {
    int c = 0; for (int i = 0; i < 3; i++) if ((l >> i) & 1) c ^= f.B[i];
    int w = f.side == 0 ? c : f.Q[l], z = f.side == 0 ? f.Q[l] : c;
    for (auto& e : asg) if (dot(w, e[1]) && dot(z, e[2])) return false;
    if ((dot(rowFT(w, f.X), z) ^ (dot(w, u) & dot(z, v))) != 1) return false;
  }
  return true;
}
static bool ufree(const WFact& f, int u) {
  for (int l = 1; l < (1 << f.r); l++) {
    int c = 0; for (int i = 0; i < 3; i++) if ((l >> i) & 1) c ^= f.B[i];
    int w = f.side == 0 ? c : f.Q[l];
    if (dot(w, u)) return false;
  }
  return true;
}
// rank-2 facts at shift (u, v) for X, rows and columns: good vectors with witnesses, then 2-dim subspaces (all of them
// up to maxk, for covering)
static void shiftedFacts(const std::vector<std::array<int, 3>>& asg, int X, int u, int v, int maxk, std::vector<WFact>& out) {
  for (int side = 0; side < 2; side++) {
    int wit[512]; bool good[512]; good[0] = false;
    for (int a = 1; a < 512; a++) {
      std::vector<int> g; for (auto& e : asg) { if (side == 0 ? dot(a, e[1]) : dot(a, e[2])) g.push_back(side == 0 ? e[2] : e[1]); }
      int vec = side == 0 ? (rowFT(a, X) ^ (dot(a, u) ? v : 0)) : (colTG(X, a) ^ (dot(a, v) ? u : 0));
      wit[a] = witness(vec, g); good[a] = wit[a] > 0;
    }
    int cnt = 0;
    for (int a = 1; a < 512 && cnt < maxk; a++) if (good[a]) for (int b = a + 1; b < 512 && cnt < maxk; b++) if (good[b] && good[a ^ b]) {
      WFact f; f.X = X; f.r = 2; f.side = side; f.B[0] = a; f.B[1] = b; f.Q[1] = wit[a]; f.Q[2] = wit[b]; f.Q[3] = wit[a ^ b];
      out.push_back(f); cnt++;
    }
  }
}
static bool lift3(const std::vector<std::array<int, 3>>& asg, const std::vector<int>& S, const std::vector<int>& Xs, L3Entry& E) {
  for (int c = 0; c < (int)S.size(); c++) {
    int pc = S[c];
    std::vector<int> cand;
    for (int X : Xs) { if (!dot(X, pc)) continue; int k = 0; for (int j = 0; j < (int)S.size(); j++) if (j != c && dot(X, S[j])) k++; if (k < 2) cand.push_back(X); }
    if (cand.empty()) continue;
    // u-free facts: unshifted rank-2 facts; greedy cover of u in [1, 512)
    std::vector<WFact> pool;
    for (int X : cand) shiftedFacts(asg, X, 0, 0, 4000, pool);
    std::vector<char> covered(512, 0); covered[0] = 1; std::vector<WFact> uf;
    while (true) {
      int bi = -1, bc = 0;
      for (size_t i = 0; i < pool.size(); i++) { int k = 0; for (int u = 1; u < 512; u++) if (!covered[u] && ufree(pool[i], u)) k++; if (k > bc) { bc = k; bi = i; } }
      if (bi < 0) break;
      uf.push_back(pool[bi]); for (int u = 1; u < 512; u++) if (ufree(pool[bi], u)) covered[u] = 1;
    }
    std::vector<std::pair<int, std::vector<WFact>>> surv; bool ok = true;
    for (int u = 1; u < 512 && ok; u++) if (!covered[u]) {
      std::vector<WFact> vf; std::vector<char> vc(512, 0); vc[0] = 1;
      for (int v = 1; v < 512 && ok; v++) if (!vc[v]) {
        std::vector<WFact> pv; for (int X : cand) shiftedFacts(asg, X, u, v, 200, pv);
        if (pv.empty()) { ok = false; break; }
        int bi = -1, bc = -1;
        for (size_t i = 0; i < pv.size(); i++) { int k = 0; for (int v2 = 1; v2 < 512; v2++) if (!vc[v2] && sfactOK(asg, pv[i], u, v2)) k++; if (k > bc) { bc = k; bi = i; } }
        vf.push_back(pv[bi]); for (int v2 = 1; v2 < 512; v2++) if (sfactOK(asg, pv[bi], u, v2)) vc[v2] = 1;
        if (!vc[v]) { ok = false; break; }
      }
      if (ok) surv.push_back({u, vf});
    }
    if (!ok) continue;
    E.S = S; E.c = c; E.ufacts = uf; E.surv = surv;
    nl3++; nl3uf += uf.size(); nl3surv += surv.size(); for (auto& sv : surv) nl3vf += sv.second.size();
    return true;
  }
  nl3fail++;
  return false;
}
static std::vector<L3Entry> LAST_L3;
static long long nwfail = 0;
static std::vector<WFact> wfacts(const std::vector<std::array<int, 3>>& asg) {
  int m = 0; while ((1 << m) - 1 < (int)PTS.size()) m++;
  std::vector<int> Xs;
  for (int xi = 1; xi < (1 << m); xi++) {
    int X = -1; for (int c = 1; c < 512 && X < 0; c++) { bool f = true; for (int j = 0; j < m; j++) if (dot(c, PQ[j]) != ((xi >> j) & 1)) f = false; if (f) X = c; }
    Xs.push_back(X);
  }
  std::vector<std::vector<int>> subs; int n = PTS.size();
  std::function<void(int, std::vector<int>&)> rec = [&](int i, std::vector<int>& cur) {
    if ((int)cur.size() == K) { subs.push_back(cur); return; }
    if (i == n) return;
    cur.push_back(PTS[i]); rec(i + 1, cur); cur.pop_back(); rec(i + 1, cur);
  };
  std::vector<int> cur; rec(0, cur);
  std::vector<WFact> best(Xs.size()); std::vector<char> have(Xs.size(), 0);
  for (size_t i = 0; i < Xs.size(); i++) { WFact f; if (bestW(asg, Xs[i], 3, f)) { best[i] = f; have[i] = 1; } }
  auto cov = [&](const WFact& f, const std::vector<int>& S) { return cntX(f.X, S) < f.r; };
  std::vector<char> covered(subs.size(), 0); std::vector<WFact> out; std::vector<char> used(Xs.size(), 0);
  while (true) {
    int bi = -1, bc = 0;
    for (size_t i = 0; i < Xs.size(); i++) if (have[i] && !used[i]) {
      int c = 0; for (size_t s = 0; s < subs.size(); s++) if (!covered[s] && cov(best[i], subs[s])) c++;
      if (c > bc) { bc = c; bi = i; } }
    if (bi < 0) break;
    used[bi] = 1; out.push_back(best[bi]);
    for (size_t s = 0; s < subs.size(); s++) if (cov(best[bi], subs[s])) covered[s] = 1;
  }
  LAST_L3.clear();
  for (size_t s = 0; s < subs.size(); s++) if (!covered[s]) {
    L3Entry E;
    if (!lift3(asg, subs[s], Xs, E)) return {};
    LAST_L3.push_back(E);
  }
  return out;
}
}  // namespace g7p
