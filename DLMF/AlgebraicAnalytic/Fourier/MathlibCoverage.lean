/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# DLMF §1.8 results already in Mathlib

Checked pointers to Mathlib declarations for DLMF §1.8 (Fourier series). Mathlib's Fourier
series live on `AddCircle T`; for a function on an interval `[a, b]` Mathlib uses
`fourierCoeffOn hab f n = (b - a)⁻¹ ∫_a^b e^{-2πinx/(b-a)} f(x) dx`, which for `[a, b] = [-π, π]`
is DLMF's `c_n` (1.8.4; `DLMF.AlgebraicAnalytic.fourierExpCoeff_eq_fourierCoeffOn`). Mathlib's
Fourier transform is `𝓕 f(ξ) = ∫ e^{-2πixξ} f(x) dx`, not the normalization 1.14.1 of DLMF.
-/

/- §1.8(i). -/
dlmf_upstream 1.8.E3 has_pointwise_sum_fourier_series_of_summable
  "different notation: continuous f on AddCircle T, summable coefficients"
dlmf_upstream 1.8.E4 fourierCoeffOn
  "exact (different notation): fourierCoeffOn on [-π, π] is c_n"
dlmf_upstream 1.8.E6 hasSum_sq_fourierCoeffOn
  "exact (different notation): Parseval for f ∈ L²(a, b)"
dlmf_upstream 1.8.E6 tsum_sq_fourierCoeff
  "different notation: Parseval on L²(AddCircle T)"
dlmf_upstream 1.8.i hasSum_fourier_series_L2
  "related: the Fourier series of f ∈ L²(AddCircle T) converges to f in L²"
dlmf_upstream 1.8.E7 fourierCoeffOn_of_hasDerivAt
  "partial: one integration by parts for c_n"
dlmf_upstream 1.8.E10 Real.tendsto_integral_exp_smul_cocompact
  "stronger: f integrable on ℝ, kernel e^{-2πixξ}, |ξ| → ∞"
dlmf_upstream 1.8.E10 tendsto_integral_exp_inner_smul_cocompact
  "stronger: on a finite-dimensional inner product space"

/- §1.8(iv). -/
dlmf_upstream 1.8.E14 Real.tsum_eq_tsum_fourier_of_rpow_decay
  "different hypotheses: f, 𝓕 f = O(|x|^{-b}), b > 1"
dlmf_upstream 1.8.E14 Real.tsum_eq_tsum_fourier
  "different hypotheses: summable periodizations of f and 𝓕 f"
dlmf_upstream 1.8.E16 Complex.tsum_exp_neg_quadratic
  "different notation: Gaussian with linear term, ℜa > 0"
