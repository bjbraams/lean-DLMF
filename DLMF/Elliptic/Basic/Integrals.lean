/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Real Legendre elliptic integrals and their elementary integrands
-/

@[expose] public noncomputable section

open Real Set Filter
open scoped Topology

namespace DLMF.Elliptic

/-- For `m < 1` the base `1 - m sin²θ` is positive. -/
theorem one_sub_mul_sin_sq_pos {m : ℝ} (hm : m < 1) (θ : ℝ) : 0 < 1 - m * sin θ ^ 2 := by
  rcases le_or_gt m 0 with h | h <;> nlinarith [sin_sq_le_one θ, sq_nonneg (sin θ)]

/-- Upper bound for the base `1 - m sin²θ`. -/
theorem one_sub_mul_sin_sq_le {m : ℝ} (θ : ℝ) : 1 - m * sin θ ^ 2 ≤ 1 + |m| := by
  nlinarith [sin_sq_le_one θ, sq_nonneg (sin θ), abs_nonneg m, neg_abs_le m, le_abs_self m]

/-- For `m < 1`, `θ ↦ (1 - m sin²θ)^p` is continuous. -/
theorem continuous_one_sub_mul_sin_sq_rpow {m : ℝ} (hm : m < 1) (p : ℝ) :
    Continuous fun θ : ℝ => (1 - m * sin θ ^ 2) ^ p :=
  (by fun_prop : Continuous fun θ : ℝ => 1 - m * sin θ ^ 2).rpow_const
    fun θ => Or.inl (one_sub_mul_sin_sq_pos hm θ).ne'

/-- The complete elliptic integral of the first kind in Legendre's form, with parameter
`m = k²`: `K(m) = ∫₀^{π/2} (1 - m sin²θ)^{-1/2} dθ` (DLMF 19.2.8). -/
@[dlmf 19.2.E8]
def Real.compEllIntKm (m : ℝ) : ℝ := ∫ θ in (0 : ℝ)..(π / 2), (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ)

/-- The complete elliptic integral of the second kind, with parameter `m = k²`:
`E(m) = ∫₀^{π/2} (1 - m sin²θ)^{1/2} dθ` (DLMF 19.2.8). -/
@[dlmf 19.2.E8]
def Real.compEllIntEm (m : ℝ) : ℝ := ∫ θ in (0 : ℝ)..(π / 2), (1 - m * sin θ ^ 2) ^ (1 / 2 : ℝ)

/-- Legendre's incomplete integral of the first kind `F(φ|m) = ∫₀^φ (1 - m sin²θ)^{-1/2} dθ`
(DLMF 19.2.4, Temme (12.15)). -/
@[dlmf 19.2.E4]
def Real.incEllIntFm (φ m : ℝ) : ℝ := ∫ θ in (0 : ℝ)..φ, (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ)

/-- Legendre's incomplete integral of the second kind `E(φ|m) = ∫₀^φ (1 - m sin²θ)^{1/2} dθ`
(DLMF 19.2.5, Temme (12.16)). -/
@[dlmf 19.2.E5]
def Real.incEllIntEm (φ m : ℝ) : ℝ := ∫ θ in (0 : ℝ)..φ, (1 - m * sin θ ^ 2) ^ (1 / 2 : ℝ)

/-- The integrand `(1 - n sin²θ)⁻¹ (1 - m sin²θ)^{-1/2}` of the third kind. -/
def piIntegrand (n m θ : ℝ) : ℝ := (1 - n * sin θ ^ 2)⁻¹ * (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ)

/-- Legendre's incomplete integral of the third kind in the parameter `m = k²`, with DLMF's
argument order (amplitude, characteristic `n = α²`, parameter):
`Π(φ, n, m) = ∫₀^φ (1 - n sin²θ)⁻¹ (1 - m sin²θ)^{-1/2} dθ` (DLMF 19.2.7, Temme (12.17)),
used here for `n < 1`, `m < 1` where no principal value is needed. -/
@[dlmf 19.2.E7]
def Real.incEllIntPim (φ n m : ℝ) : ℝ := ∫ θ in (0 : ℝ)..φ, piIntegrand n m θ

/-- The complete integral of the third kind `Π(n, m) = Π(π/2, n, m)` (DLMF 19.2.7). -/
def Real.compEllIntPim (n m : ℝ) : ℝ := Real.incEllIntPim (π / 2) n m

/-- A smooth antiderivative of `(cos²φ + c² sin²φ)⁻¹`, equal to `arctan(c tan φ)/c` on
`(-π/2, π/2)`. -/
def piZeroPrimitive (c φ : ℝ) : ℝ :=
  (φ - arctan ((1 - c) * sin φ * cos φ / (cos φ ^ 2 + c * sin φ ^ 2))) / c

end DLMF.Elliptic
