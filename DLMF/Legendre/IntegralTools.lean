/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Legendre.IntegralTools.Orthogonality
public import DLMF.Legendre.IntegralTools.FractionalAndLaplace

/-!
# Tools for Legendre integrals

Helper results (prefix `legInt_`) for `DLMF.Legendre.Integrals` and
`DLMF.Legendre.IntegralRepresentations`:

* the `m`-times differentiated Legendre equation for `P_n^{(m)}` and the moment recursion
  `∫ (1-x²)^{m+1} (P_l^{(m+1)})(P_n^{(m+1)}) = (n-m)(n+m+1) ∫ (1-x²)^m P_l^{(m)} P_n^{(m)}`,
  which yields the orthogonality of Ferrers functions of integer degree and order (DLMF 14.17.6);
* Green's identity in the order and the moment recursion behind the weight `1/(1-x²)`
  orthogonality (DLMF 14.17.8);
* the contiguous relation `𝐅(a,b;c) = c 𝐅(a,b;c+1) + a b z 𝐅(a+1,b+1;c+2)` on the cut plane and
  the resulting primitive `d/dw [w^{k+1} 𝐅(a,b;k+2;w)] = w^k 𝐅(a,b;k+1;w)`, which identifies
  iterated integrals of `P_ν` from the endpoint `1` with Ferrers and associated Legendre functions
  of negative integer order (DLMF 14.6.6, 14.6.7);
* analyticity of `z ↦ ∫_0^1 w(s) F(zs) ds` on the cut plane and the resulting cut-plane form of
  the fractional integral DLMF 15.6.8 with `d = 1`, used for DLMF 14.12.5;
* elementary facts on complex powers of positive reals and on the principal slit plane;
* the primitives `g_k = (z²-1)^{k/2} Q^{-k}_ν` with `g_{k+1}' = g_k` and `g_{k+1} → 0` at infinity,
  giving the iterated tail integrals of DLMF 14.6.8 on `(1,∞)` and on the principal sheet;
* integration-by-parts recurrences in the order for the Laplace-type moments
  `∫_0^π w^ν cos(mθ)` and `∫_0^π w^p sin^{2q}θ`, `w = x + √(x²-1) cos θ` (DLMF 14.12.7, 14.12.8);
* Heine's integral `∫_0^∞ dt/(x+√(x²-1) cosh t)^{n+1}` (DLMF 14.12.14) via an explicit primitive
  and a degree recurrence;
* recurrences in degree and order for `∫_0^u (x-√(x²-1) cosh t)^n cosh(mt)`, `u = arcoth x`
  (DLMF 14.12.9), and for `∫_{-1}^1 (1-t²)^n (x-t)^{-p}` (DLMF 14.12.11).
-/
