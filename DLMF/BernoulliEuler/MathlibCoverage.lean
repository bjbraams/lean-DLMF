/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import DLMF.Core.UpstreamElementary
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.NumberTheory.ZetaValues

/-!
# DLMF Chapter 24, §§24.1–24.10: results already in Mathlib

Checked pointers from DLMF items to Mathlib declarations, in addition to the Chapter 24 pointers
already in `DLMF.Core.UpstreamElementary` (24.2.E2–E5, 24.4.E1, E3, E7, E18, E25, E27, E34,
24.8.E1–E3, 24.13.E1–E2), which are not repeated. Mathlib's `bernoulli` uses `B₁ = -1/2` (DLMF's
convention), `bernoulli'` uses `B'₁ = +1/2`; `Polynomial.bernoulli` lives in `ℚ[X]` and
`bernoulliFun` is its real evaluation.
-/

/- §24.2(iii): Mathlib's periodized Bernoulli function on the unit additive circle. -/
dlmf_upstream 24.2.iii periodizedBernoulli
  "different convention: B̃ₙ as a function on ℝ/ℤ (`UnitAddCircle`), defined from [0, 1); \
  bridge `DLMF.BernoulliEuler.periodicBernoulliB_eq_periodizedBernoulli`"

/- §24.2(iv), Table 24.2.1–24.2.2: individual exact values in Mathlib. -/
dlmf_upstream 24.2.T1 bernoulli_two "partial: B₂ = 1/6"
dlmf_upstream 24.2.T1 bernoulli'_four "partial: B'₄ = B₄ = -1/30"
dlmf_upstream 24.2.T2 Polynomial.bernoulli_one "partial: B₁(x) = x - 1/2 in ℚ[X]"

/- §24.4(ii): reflection in `-x`. -/
dlmf_upstream 24.4.E5 Polynomial.bernoulli_comp_neg_X
  "exact: as the polynomial identity Bₙ(-X) = (-1)ⁿ (Bₙ(X) + n X^{n-1}) in ℚ[X]"

/- §24.4(vi): special values. -/
dlmf_upstream 24.4.E27 bernoulliFun_eval_half_eq_zero "special case: B₂ₖ₊₁(1/2) = 0, real"
dlmf_upstream 24.4.E31 Polynomial.bernoulli_three_eval_one_quarter "special case: B₃(1/4) = 3/64"

/- §24.5(i): `∑_{k<n} (n choose k) Bₖ = 0` for `n ≥ 2`. -/
dlmf_upstream 24.5.E3 sum_bernoulli
  "stronger: ∑_{k<n} (n choose k) Bₖ = if n = 1 then 1 else 0, all n"

/- §24.10(i): von Staudt–Clausen. -/
dlmf_upstream 24.10.E1 Bernoulli.vonStaudt_clausen
  "exact: B₂ₖ + ∑_{p prime, p-1 ∣ 2k} 1/p ∈ ℤ for all k ≥ 0 (the sum runs over p < 2k + 2, \
  which contains every such prime)"
dlmf_upstream 24.10.E1 Bernoulli.dvd_den_bernoulli
  "partial: p ∣ den B₂ₖ when p - 1 ∣ 2k, k > 0 (one half of the denominator statement)"
dlmf_upstream 24.10.E1 Bernoulli.not_sq_dvd_den_bernoulli
  "partial: p² ∤ den B₂ₖ when p - 1 ∣ 2k, k > 0"
