/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Dirichlet integrals and simplex volumes (AAR §1.8)

AAR Theorem 1.8.1 is the simplex integral of `∏ x_i^{a_i-1}`. The inner integral in two
variables is recorded below. AAR Corollary 1.8.3 (volume of an `ℓ^p` ball) is
`MeasureTheory.volume_sum_rpow_le` in Mathlib; the volume of the unit `ℓ^1` ball
`{∑ |x_i| ≤ 1}` is `2^n / n!`.
-/

@[expose] public section

open Set Real MeasureTheory intervalIntegral

open scoped ENNReal Nat

noncomputable section

namespace Real

/-- Inner integral of Dirichlet's formula in two variables: `∫_0^t y^{b-1} dy = t^b / b`. -/
theorem integral_rpow_zero_of_pos {b t : ℝ} (hb : 0 < b) (_ht : 0 ≤ t) :
    ∫ y in (0 : ℝ)..t, y ^ (b - 1) = t ^ b / b := by
  have h : -1 < b - 1 := by linarith
  rw [integral_rpow (Or.inl h), sub_add_cancel, zero_rpow hb.ne', sub_zero]

end Real

namespace MeasureTheory

/-- AAR Corollary 1.8.3 for equal exponents `p_i = p`: volume of the `ℓ^p` ball of radius `r`.
This is Mathlib's `volume_sum_rpow_le`. -/
theorem volume_lp_ball_eq_gamma (ι : Type*) [Fintype ι] [Nonempty ι] {p r : ℝ}
    (hp : 1 ≤ p) :
    volume {x : ι → ℝ | (∑ i, |x i| ^ p) ^ (1 / p) ≤ r} =
      (.ofReal r) ^ Fintype.card ι *
        .ofReal ((2 * Real.Gamma (1 / p + 1)) ^ Fintype.card ι /
          Real.Gamma (Fintype.card ι / p + 1)) :=
  volume_sum_rpow_le (ι := ι) hp r

/-- The `ℓ^1` unit ball in `ι → ℝ` has volume `2^{#ι} / (#ι)!`. -/
theorem volume_l1_unitBall (ι : Type*) [Fintype ι] [Nonempty ι] :
    volume {x : ι → ℝ | ∑ i, |x i| ≤ 1} =
      .ofReal ((2 : ℝ) ^ Fintype.card ι / (Fintype.card ι).factorial) := by
  have h := volume_lp_ball_eq_gamma (ι := ι) (p := 1) (r := 1) le_rfl
  have hG : Real.Gamma (1 / (1 : ℝ) + 1) = 1 := by
    simp [Real.Gamma_add_one, Real.Gamma_one]
  have hGn : Real.Gamma ((Fintype.card ι : ℝ) / 1 + 1) =
      (Fintype.card ι).factorial := by
    simp [div_one, Real.Gamma_nat_eq_factorial]
  have hset : {x : ι → ℝ | (∑ i, |x i| ^ (1 : ℝ)) ^ (1 / (1 : ℝ)) ≤ 1} =
      {x : ι → ℝ | ∑ i, |x i| ≤ 1} := by
    ext x
    simp [Real.rpow_one]
  rw [← hset, h, hG, hGn]
  simp [ENNReal.ofReal_one, one_pow]

end MeasureTheory
