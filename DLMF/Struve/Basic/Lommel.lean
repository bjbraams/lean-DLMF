/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Basic.SecondKind
public import DLMF.Hypergeometric.Basic.Pochhammer

/-!
# Lommel functions (DLMF §11.9)

## Main definitions

* `lommelA`: the product of the first `k` factors `(μ+2j+1)² - ν²` (DLMF 11.9.4).
* `LommelRegular`: the nonexceptional parameters of the small Lommel function.
* `lommelS`: the Lommel series `s_{μ,ν}(z)` (DLMF 11.9.3), on the principal power branch.
* `lommelCapitalRegular`: the capital Lommel function `S_{μ,ν}(z)` (DLMF 11.9.5) at regular
  parameters.

## Main results

* `lommelA_pochhammer`: DLMF 11.9.4.
* `lommelS_neg_order`, `lommelCapitalRegular_neg_order`: evenness in `ν` (DLMF 11.9.6).
* `LommelRegular.add_two`, `lommelA_add_two`: the shift `μ ↦ μ + 2`.

## Implementation notes

The series, the differential equation and the continuation `lommelCapital` of the capital
Lommel function to exceptional parameters are in `DLMF.Struve.Lommel`.
-/

@[expose] public noncomputable section

open Complex DLMF.Hypergeometric
open scoped Real

namespace DLMF.Struve

open DLMF.Bessel

/-- The finite product of the first `k` factors `(μ+2j+1)²-ν²` in the Lommel series denominator. -/
@[dlmf 11.9.E4]
def lommelA (μ ν : ℂ) (k : ℕ) : ℂ :=
  ∏ j ∈ Finset.range k, ((μ+2*j+1)^2-ν^2)

/-- Nonexceptional parameters of the small Lommel function. -/
def LommelRegular (μ ν : ℂ) : Prop :=
  ∀ n : ℕ, μ-ν ≠ -(2*n+1) ∧ μ+ν ≠ -(2*n+1)

/-- The totalized Lommel series `z^(μ+1) Σ (-1)^k z^(2k)/A(μ,ν,k+1)` on the principal power
branch. -/
@[dlmf 11.9.E3]
def lommelS (μ ν z : ℂ) : ℂ :=
  z^(μ+1) * ∑' k : ℕ, (-1)^k*z^(2*k)/lommelA μ ν (k+1)

/-- The regular-parameter capital Lommel solution obtained by adding the prescribed Gamma-weighted
J and Y connection terms to the Lommel series. -/
@[dlmf 11.9.E5]
def lommelCapitalRegular (μ ν z : ℂ) : ℂ :=
  lommelS μ ν z + 2^(μ-1)*Gamma ((μ+ν+1)/2)*Gamma ((μ-ν+1)/2)*
    (sin ((μ-ν)*π/2)*besselJ ν z-cos ((μ-ν)*π/2)*besselY ν z)

/-- The regular capital Lommel function is even in the order `ν`, for every parameter. -/
theorem lommelCapitalRegular_neg_order (μ ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    lommelCapitalRegular μ (-ν) z = lommelCapitalRegular μ ν z := by
  have hA : ∀ k, lommelA μ (-ν) k = lommelA μ ν k := fun k => by simp [lommelA]
  have hS : lommelS μ (-ν) z = lommelS μ ν z := by simp only [lommelS, hA]
  unfold lommelCapitalRegular
  rw [hS, besselJ_neg_eq ν hz, besselY_neg ν hz]
  have e1 : (μ+-ν+1)/2 = (μ-ν+1)/2 := by ring
  have e2 : (μ- -ν+1)/2 = (μ+ν+1)/2 := by ring
  have e3 : (μ- -ν)*π/2 = (μ-ν)*π/2 + ν*π := by ring
  rw [e1, e2, e3, sin_add, cos_add]
  linear_combination (2^(μ-1)*Gamma ((μ-ν+1)/2)*Gamma ((μ+ν+1)/2)*
    (sin ((μ-ν)*π/2)*besselJ ν z-cos ((μ-ν)*π/2)*besselY ν z))*sin_sq_add_cos_sq (ν*π)

/-- Identity under the stated parameter and domain assumptions: `lommelA μ ν k = 4^k*pochhammer
((μ-ν+1)/2) k*pochhammer ((μ+ν+1)/2) k`. -/
@[dlmf 11.9.E4]
theorem lommelA_pochhammer (μ ν : ℂ) (k : ℕ) :
    lommelA μ ν k = 4^k*pochhammer ((μ-ν+1)/2) k*pochhammer ((μ+ν+1)/2) k := by
  induction k with
  | zero => simp [lommelA, pochhammer_zero]
  | succ k ih =>
    have h : lommelA μ ν (k+1) = lommelA μ ν k*((μ+2*k+1)^2-ν^2) := by
      simp [lommelA, Finset.prod_range_succ]
    rw [h, ih, pochhammer_succ, pochhammer_succ, pow_succ]
    push_cast
    ring

/-- Identity under the stated parameter and domain assumptions: `lommelS μ (-ν) z = lommelS μ ν
z`. -/
@[dlmf 11.9.E6]
theorem lommelS_neg_order {μ ν : ℂ} {z : ℂ} :
    lommelS μ (-ν) z = lommelS μ ν z := by
  have h (k : ℕ) : lommelA μ (-ν) k=lommelA μ ν k := by simp [lommelA]
  simp only [lommelS, h]

/-- Shifting the degree by two preserves the regular Lommel parameter domain. -/
theorem LommelRegular.add_two {μ ν : ℂ} (h : LommelRegular μ ν) :
    LommelRegular (μ + 2) ν := by
  intro n
  constructor
  · intro hn
    exact (h (n + 1)).1 (by push_cast at *; linear_combination hn)
  · intro hn
    exact (h (n + 1)).2 (by push_cast at *; linear_combination hn)

/-- Removing the first Lommel product factor shifts the degree by two. -/
theorem lommelA_add_two (μ ν : ℂ) (k : ℕ) :
    lommelA μ ν (k + 1) = ((μ + 1)^2 - ν^2) * lommelA (μ + 2) ν k := by
  induction k with
  | zero => simp [lommelA]
  | succ k ih =>
    rw [show lommelA μ ν (k + 1 + 1) =
      lommelA μ ν (k + 1) * ((μ + 2 * (k + 1) + 1)^2 - ν^2) by
        simp [lommelA, Finset.prod_range_succ]]
    rw [ih]
    simp only [lommelA, Finset.prod_range_succ]
    ring

end DLMF.Struve
