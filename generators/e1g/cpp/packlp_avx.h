// packlp_avx.h (lenum, native/xtier/lenum): packlp.h's PackLP with the same pivot sequence and the same floating-point
// operations, laid out for AVX-512.   max sum_j x_j  s.t.  sum_{j in S_i} x_j <= b_i (i < m, b_i >= 0),  0 <= x_j <= u_j.
// Differences from packlp.h, none of which changes a computed value (checked bit for bit on 462,739 node LPs of L479 and line
// 490: ok flag, iteration count, z, primal, duals; also with -ffp-contract=off):
//  - solveF(n, m, fill, b, u): the caller fills the 1.0 entries of each zeroed tableau row (solve() keeps the old interface);
//  - tableau rows padded to a multiple of 8 doubles (padding columns stay +0 and are never read for a real column);
//  - the entering column is copied once per iteration (col[i] = a[i][s]); every use reads the same value as before;
//  - Dantzig pricing as a vector max over the eligible columns, then the first column attaining it (the scalar loop's strict
//    '>' keeps the first index of the maximum); Bland's rule uses the original scalar loop;
//  - ratio test: the limits of 8 rows at a time with the same operands and divisions and the same 'lim < 0 -> 0' clamp, then
//    the original sequential selection (same tolerances, same B-index tie-break, rows in order) over the rows that can be
//    selected at all (lim_i <= PM_i + D(PM_i), see the comment there; the others leave the state unchanged);
//  - eliminations keep the expression 'ai[j] -= f * ar[j]' with a compile-time row length; the cur, z, enteringVal and d
//    updates keep packlp.h's expressions, so GCC contracts them exactly as in packlp.h under any -ffp-contract setting.
#pragma once
#include <vector>
#include <cmath>
#include <cstring>
#include <cstdlib>
#include <cstdint>
#include <immintrin.h>
struct PackLP {
  int n = 0, m = 0, nn = 0;
  double* a = nullptr; size_t acap = 0;   // m x nn
  std::vector<double> cur, d, ubv, col, lim, ubB;
  std::vector<int> B, Nv;
  std::vector<char> atU;                  // size nn (padding 0)
  std::vector<uint8_t> em;               // eligibility masks of the ratio test, 8 rows per byte
  double z = 0;
  int iters = 0;
  static constexpr double INF = 1e300, EPS = 1e-9, PIV = 1e-9;
  PackLP() {}
  PackLP(const PackLP&) = delete; PackLP& operator=(const PackLP&) = delete;
  ~PackLP() { free(a); }
  void ensure(size_t sz) { if (sz > acap) { free(a); acap = sz * 2 + 64; a = (double*)aligned_alloc(64, ((acap * sizeof(double) + 63) / 64) * 64); } }
  // the elimination keeps packlp.h's expression 'ai[j] -= f * ar[j]' (so GCC contracts it exactly as in the baseline, whatever
  // -ffp-contract says); rows are 8*NV doubles with a compile-time length
  template <int NV> inline void elim(int r, int s, double inv, const double* __restrict ar) {
    alignas(64) double av[8 * NV]; for (int k = 0; k < 8 * NV; k++) av[k] = ar[k];
    for (int i = 0; i < m; i++) {
      if (i == r) continue; double* __restrict ai = (double*)__builtin_assume_aligned(a + (size_t)i * (8 * NV), 64); double f = col[i]; if (f == 0) continue;
      for (int k = 0; k < 8 * NV; k++) ai[k] -= f * av[k];
      ai[s] = -f * inv;
    }
  }
  bool solve(int n_, const std::vector<std::vector<int>>& rows, const std::vector<double>& b, const double* u, int maxIt = 0) {
    return solveF(n_, (int)rows.size(), [&](int i, double* ar) { for (int j : rows[i]) ar[j] = 1.0; }, b.data(), u, maxIt); }
  // fill(i, row) sets the 1.0 entries of row i (columns < n) in a zeroed tableau row
  template <class F> bool solveF(int n_, int m_, F fill, const double* b, const double* u, int maxIt = 0) {
    n = n_; m = m_; iters = 0; z = 0; nn = (n + 7) & ~7; if (nn == 0) nn = 8;
    ensure((size_t)m * nn + 8); memset(a, 0, sizeof(double) * (size_t)m * nn);
    cur.resize(m + 8); d.assign(nn, 0.0); for (int j = 0; j < n; j++) d[j] = 1.0;
    ubv.assign(n + m, INF); B.resize(m); Nv.resize(n); atU.assign(nn, 0);
    col.resize(m + 8); lim.resize(m + 8); ubB.assign(m + 8, INF); em.resize(m / 8 + 2);
    for (int j = 0; j < n; j++) { Nv[j] = j; ubv[j] = u[j]; }
    for (int i = 0; i < m; i++) { B[i] = n + i; cur[i] = b[i]; if (b[i] < -EPS) return false; fill(i, a + (size_t)i * nn); }
    if (maxIt <= 0) maxIt = 50 * (n + m) + 100;
    int degen = 0;
    const __m512d SGN = _mm512_set1_pd(-0.0), ZERO = _mm512_setzero_pd();
    while (true) {
      if (++iters > maxIt) return false;
      bool bland = degen > 50;
      // pricing: entering column s and direction dir
      int s = -1; int dir = 0;
      if (bland) {
        for (int j = 0; j < n; j++) {
          double dj = d[j]; int dj_dir = 0;
          if (!atU[j] && dj > EPS) dj_dir = 1; else if (atU[j] && dj < -EPS) dj_dir = -1;
          if (!dj_dir) continue;
          if (s < 0 || Nv[j] < Nv[s]) { s = j; dir = dj_dir; }
        }
      } else {
        __m512d mx = _mm512_set1_pd(-1.0);
        for (int j = 0; j < nn; j += 8) {
          __m512d dv = _mm512_loadu_pd(&d[j]);
          __mmask8 au = (__mmask8)_mm_test_epi8_mask(_mm_loadl_epi64((const __m128i*)&atU[j]), _mm_loadl_epi64((const __m128i*)&atU[j]));
          __mmask8 e = (__mmask8)((~au & _mm512_cmp_pd_mask(dv, _mm512_set1_pd(EPS), _CMP_GT_OQ)) | (au & _mm512_cmp_pd_mask(dv, _mm512_set1_pd(-EPS), _CMP_LT_OQ)));
          mx = _mm512_mask_max_pd(mx, e, mx, _mm512_andnot_pd(SGN, dv));
        }
        double M = _mm512_reduce_max_pd(mx);
        if (M > 0) {
          const __m512d MV = _mm512_set1_pd(M);
          for (int j = 0; j < nn; j += 8) {
            __m512d dv = _mm512_loadu_pd(&d[j]);
            __mmask8 au = (__mmask8)_mm_test_epi8_mask(_mm_loadl_epi64((const __m128i*)&atU[j]), _mm_loadl_epi64((const __m128i*)&atU[j]));
            __mmask8 e = (__mmask8)((~au & _mm512_cmp_pd_mask(dv, _mm512_set1_pd(EPS), _CMP_GT_OQ)) | (au & _mm512_cmp_pd_mask(dv, _mm512_set1_pd(-EPS), _CMP_LT_OQ)));
            __mmask8 h = (__mmask8)(e & _mm512_cmp_pd_mask(_mm512_andnot_pd(SGN, dv), MV, _CMP_EQ_OQ));
            if (h) { s = j + __builtin_ctz((unsigned)h); dir = atU[s] ? -1 : 1; break; }
          }
        }
      }
      if (s < 0) break;   // optimal
      // ratio test: x_N[s] moves by dir*t, x_B[i] moves by c_i*t with c_i = -a[i][s]*dir
      { const double* as = a + s; for (int i = 0; i < m; i++) col[i] = as[(size_t)i * nn]; }
      double tmax = ubv[Nv[s]] < INF ? ubv[Nv[s]] : INF; int r = -1; bool toUpper = false;
      {
        const __m512d DV = _mm512_set1_pd((double)dir), MPIV = _mm512_set1_pd(-PIV), PPIV = _mm512_set1_pd(PIV), VINF = _mm512_set1_pd(INF);
        const __m512d BIG = _mm512_set1_pd(1e308), E12 = _mm512_set1_pd(1e-12), U50 = _mm512_set1_pd(0x1p-50), TWO = _mm512_set1_pd(2.0), MM2 = _mm512_set1_pd((double)(m + 2));
        const __m512i I1 = _mm512_setr_epi64(0, 0, 1, 2, 3, 4, 5, 6), I2 = _mm512_setr_epi64(0, 0, 0, 1, 2, 3, 4, 5), I4 = _mm512_setr_epi64(0, 0, 0, 0, 0, 1, 2, 3);
        double pm = tmax;
        for (int i = 0; i < m; i += 8) {
          __mmask8 lm = (m - i >= 8) ? (__mmask8)0xFF : (__mmask8)((1u << (m - i)) - 1);
          __m512d cv = _mm512_mul_pd(_mm512_xor_pd(_mm512_maskz_loadu_pd(lm, &col[i]), SGN), DV);     // c = -a[i][s]*dir
          __m512d cu = _mm512_maskz_loadu_pd(lm, &cur[i]), ub = _mm512_maskz_loadu_pd(lm, &ubB[i]);
          __mmask8 e1 = _mm512_mask_cmp_pd_mask(lm, cv, MPIV, _CMP_LT_OQ);
          __mmask8 e2 = (__mmask8)(_mm512_mask_cmp_pd_mask(lm, cv, PPIV, _CMP_GT_OQ) & _mm512_cmp_pd_mask(ub, VINF, _CMP_LT_OQ) & ~e1);
          // e1 rows: cur/(-c); e2 rows: (ub-cur)/c -- one division per lane, the same operands as the scalar code
          __m512d num = _mm512_mask_blend_pd(e2, cu, _mm512_sub_pd(ub, cu)), den = _mm512_mask_blend_pd(e2, _mm512_xor_pd(cv, SGN), cv);
          __mmask8 e = (__mmask8)(e1 | e2);
          __m512d L = _mm512_maskz_div_pd(e, num, den);
          L = _mm512_mask_blend_pd(_mm512_cmp_pd_mask(L, ZERO, _CMP_LT_OQ), L, ZERO);                 // if (lim < 0) lim = 0
          _mm512_mask_storeu_pd(&lim[i], lm, L);
          // candidates of the sequential selection below: a row i can be selected only if lim_i <= PM_i + D(PM_i), where PM_i is
          // the minimum of the initial tmax and the earlier eligible limits.  (After an eligible row j, tmax <= lim_j + eps(tmax):
          // a row that is not selected has lim_j >= fl(tmax-1e-12); tmax rises only by a tie-rule selection, by at most
          // eps(tmax) = 1e-12 + 2^-52 (|tmax|+1); selection needs lim_i <= fl(tmax+1e-12).  So D = (m+2)(1e-12 + 2^-50 (|PM|+2))
          // is a valid margin.)  Rows that cannot be selected leave the state unchanged, so skipping them is exact.
          const __mmask8 v = (__mmask8)(e & _mm512_cmp_pd_mask(L, L, _CMP_ORD_Q));
          __m512d x = _mm512_mask_blend_pd(v, BIG, L), inc = x;
          inc = _mm512_min_pd(inc, _mm512_mask_permutexvar_pd(BIG, 0xFE, I1, inc));
          inc = _mm512_min_pd(inc, _mm512_mask_permutexvar_pd(BIG, 0xFC, I2, inc));
          inc = _mm512_min_pd(inc, _mm512_mask_permutexvar_pd(BIG, 0xF0, I4, inc));
          __m512d exc = _mm512_min_pd(_mm512_mask_permutexvar_pd(BIG, 0xFE, I1, inc), _mm512_set1_pd(pm));
          __m512d D = _mm512_mul_pd(MM2, _mm512_add_pd(E12, _mm512_mul_pd(U50, _mm512_add_pd(_mm512_andnot_pd(SGN, exc), TWO))));
          em[i >> 3] = (uint8_t)(v & _mm512_cmp_pd_mask(L, _mm512_add_pd(exc, D), _CMP_LE_OQ));
          pm = std::min(pm, _mm512_reduce_min_pd(x));
        }
        for (int g = 0; 8 * g < m; g++) {
          unsigned e = em[g];
          while (e) {
            int i = 8 * g + __builtin_ctz(e); e &= e - 1;
            double li = lim[i];
            bool up = (li < tmax - 1e-12) || (li <= tmax + 1e-12 && r >= 0 && B[i] < B[r]);
            if (up) { tmax = li; r = i; }
          }
        }
        if (r >= 0) { double c = -col[r] * dir; toUpper = (c > 0); }
      }
      if (tmax >= INF) return false;   // cannot happen for this LP family
      degen = (tmax <= 1e-12) ? degen + 1 : 0;
      for (int i = 0; i < m; i++) cur[i] += -col[i] * dir * tmax;
      z += d[s] * dir * tmax;
      double enteringVal = (atU[s] ? ubv[Nv[s]] : 0.0) + dir * tmax;
      if (r < 0) { atU[s] = !atU[s]; continue; }   // bound flip
      // pivot: B[r] leaves at a bound, Nv[s] enters with value enteringVal
      double* ar = a + (size_t)r * nn; double p = ar[s]; if (std::fabs(p) < PIV) return false;
      double leaveAtUpper = toUpper;
      double inv = 1.0 / p;
      for (int j = 0; j < n; j++) ar[j] *= inv;
      ar[s] = inv;
      switch (nn >> 3) {
        case 1: elim<1>(r, s, inv, ar); break; case 2: elim<2>(r, s, inv, ar); break; case 3: elim<3>(r, s, inv, ar); break;
        case 4: elim<4>(r, s, inv, ar); break; case 5: elim<5>(r, s, inv, ar); break; case 6: elim<6>(r, s, inv, ar); break;
        case 7: elim<7>(r, s, inv, ar); break; case 8: elim<8>(r, s, inv, ar); break;
        default:
          for (int i = 0; i < m; i++) {
            if (i == r) continue; double* ai = a + (size_t)i * nn; double f = col[i]; if (f == 0) continue;
            for (int k = 0; k < nn; k++) ai[k] -= f * ar[k];
            ai[s] = -f * inv;
          }
      }
      double ds = d[s];
      for (int j = 0; j < n; j++) d[j] -= ds * ar[j];
      d[s] = -ds * inv;
      int leaving = B[r]; B[r] = Nv[s]; Nv[s] = leaving; atU[s] = leaveAtUpper ? 1 : 0; cur[r] = enteringVal; ubB[r] = ubv[B[r]];
    }
    return true;
  }
  // primal value of structural j, row dual y_i (>= 0), after a successful solve
  void primal(std::vector<double>& x) const {
    x.assign(n, 0.0);
    for (int j = 0; j < n; j++) if (Nv[j] < n && atU[j]) x[Nv[j]] = ubv[Nv[j]];
    for (int i = 0; i < m; i++) if (B[i] < n) x[B[i]] = cur[i];
  }
  void duals(std::vector<double>& y) const {
    y.assign(m, 0.0);
    for (int j = 0; j < n; j++) if (Nv[j] >= n) { double v = -d[j]; y[Nv[j] - n] = v > 0 ? v : 0; }
  }
};
