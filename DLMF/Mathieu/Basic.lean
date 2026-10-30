/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Mathieu.Basic.EquationAndSolutions
public import DLMF.Mathieu.Basic.Spectral
public import DLMF.Mathieu.Basic.Functions
public import DLMF.Mathieu.Basic.ContinuedFractions

/-!
# Mathieu's equation and the Mathieu functions of integer order (DLMF §28.2)

This umbrella exports the definitions of the Mathieu area (DLMF Chapter 28).
The initial-value and normalization API is in `DLMF.Mathieu.FundamentalSolutions`;
existence and enumeration of characteristic values are in
`DLMF.Mathieu.SpectralExistence`. The definitions include

* `IsMathieuSolution a q w`: `w` is an entire solution of Mathieu's equation 28.2.1
  `w'' + (a - 2q cos 2z) w = 0` (genuine differentiability, complex `z`, `a`, `q`);
* the basic solutions `mathieuWI a q`, `mathieuWII a q` (`w_I(z; a, q)`, `w_II(z; a, q)`,
  28.2.5), defined by choice from the existence theorem `exists_isMathieuSolution`
  (proved: entire solutions of linear ODEs with entire coefficients, majorant series);
  uniqueness is proved (`IsMathieuSolution.eq_of_initial`) from analytic uniqueness;
* Floquet notions (§28.2(iii)–(iv)): `IsMathieuCharExp a q ν` (`cos πν = w_I(π; a, q)`,
  28.2.16), `IsFloquetSolution a q ν w` (28.2.14) and the monodromy matrix
  `mathieuMonodromy a q` (28.2.15);
* the eigenvalues `mathieuA n q = a_n(q)` and `mathieuB n q = b_n(q)` for real `q`
  (Table 28.2.1, 28.2.21–28.2.22), the `⌊n/2⌋`-th smallest real root of the boundary condition
  of Table 28.2.1 (`nthLeast`); the theorems `mathieuSpecA_exists`, `mathieuSpecB_exists`
  (proved by Sturm–Liouville arguments, `DLMFMathlib/Analysis/ODE/P2sSturmSpectrum.lean`)
  assert that these roots exist;
* the eigenfunctions `mathieuCe n z q = ce_n(z, q)` and `mathieuSe n z q = se_n(z, q)`
  (Table 28.2.2), normalized by 28.2.30, with the sign `ce_n(0, q) > 0`, `se_n'(0, q) > 0`;
* the second solutions `mathieuFe n z q = fe_n(z, q)`, `mathieuGe n z q = ge_n(z, q)` with the
  factors `C_n(q)`, `S_n(q)` and periodic parts `f_n`, `g_n` (DLMF 28.5.1–28.5.5);
* the Fourier coefficients `mathieuFourierA n m q = A^n_m(q)` and
  `mathieuFourierB n m q = B^n_m(q)` of `ce_n`, `se_n` (DLMF 28.4.1–28.4.4).

## Design notes

* The eigenvalues are defined for real `q` only (DLMF §28.2(v); the analytic continuation to
  complex `q` of §28.7 is stated as theorems). For real `q` the four boundary-value problems
  of Table 28.2.1 are regular Sturm–Liouville problems with simple real eigenvalues, so the
  `k`-th smallest root is DLMF's `a_{2k}`, `a_{2k+1}`, `b_{2k+1}`, `b_{2k+2}`.
* DLMF fixes the sign of `ce_n`, `se_n` "by continuity" in `q` from `q = 0`. For real `q`,
  `ce_n(0, q) ≠ 0` and `se_n'(0, q) ≠ 0` (an even, resp. odd, nontrivial solution cannot have
  both initial data zero), so the continuity convention is equivalent to `ce_n(0, q) > 0` and
  `se_n'(0, q) > 0`, which is the definition used here (`ce_n = c · w_I(·; a_n(q), q)` with
  `c > 0`).
* Similarly `fe_n'(0, q) > 0` and `ge_n(0, q) > 0`: DLMF fixes the signs of `C_n(q)`, `S_n(q)`
  by `C_n f_n → sin nz`, `S_n g_n → cos nz` as `q → 0`. For `n = 0` the normalization 28.5.5
  cannot hold at `q = 0` (there `f_0 = 0`); `fe_0(z, 0) = z` (28.5.7) is used at `q = 0`.
* For real `q` the Mathieu functions are real on the real axis; the normalizing integrals are
  written with `‖·‖²`, which agrees with DLMF's squares there.
* `b_0` is not defined by DLMF; `mathieuB 0 q = 0` and `mathieuSe 0 z q` are junk values.
-/
