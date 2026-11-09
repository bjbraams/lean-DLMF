/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Mellin.Transforms

/-!
# Exact oscillatory Mellin continuations

Finite oscillatory power sums give exact model transforms after subtraction. The
quadratic phase checks both the Jacobian and the rescaled exponent in DLMF 2.5.18.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Finset Asymptotics Complex
open scoped Topology

namespace DLMF.AsymptoticApproximations

/-- A single oscillatory power has the same model continuation at every positive
truncation length, with all later coefficients zero. -/
theorem oscillatoryMellinContinuationAtTop_single (κ p : ℝ) (β : ℕ → ℂ)
    (d z : ℂ) {N : ℕ} (hN : 0 < N) :
    oscillatoryMellinContinuationAtTop
      (fun t => (exp (I * κ * (t ^ p : ℝ)) * (t : ℂ) ^ (-β 0)) • d)
      κ p (fun k => if k = 0 then d else 0) β N z =
        (d * (p : ℂ)⁻¹) * oscillatoryMellinTail κ ((z - β 0) / p) := by
  simp [oscillatoryMellinContinuationAtTop, smul_ite, Finset.sum_ite_eq', hN,
    mellinTruncHigh, mellinTruncLow, mellin, mul_comm, mul_left_comm, mul_assoc]

/-- The linear pure phase continues to the entire oscillatory tail model. -/
theorem oscillatoryMellinContinuationAtTop_exp (κ : ℝ) (z : ℂ) {N : ℕ} (hN : 0 < N) :
    oscillatoryMellinContinuationAtTop (fun t : ℝ => exp (I * κ * t)) κ 1
      (fun k => if k = 0 then 1 else 0) (fun k => k) N z = oscillatoryMellinTail κ z := by
  simpa using oscillatoryMellinContinuationAtTop_single κ 1 (fun k => (k : ℂ)) 1 z hN

/-- A quadratic phase and the power `t^(-3)` give the factor one half and the model
argument `(z-3)/2`. -/
theorem oscillatoryMellinContinuationAtTop_quadratic (κ : ℝ) (z : ℂ)
    {N : ℕ} (hN : 0 < N) :
    oscillatoryMellinContinuationAtTop
      (fun t : ℝ => exp (I * κ * (t ^ (2 : ℝ) : ℝ)) * (t : ℂ) ^ (-(3 : ℂ))) κ 2
      (fun k => if k = 0 then 1 else 0) (fun k => (k : ℂ) + 3) N z =
        (1 / 2 : ℂ) * oscillatoryMellinTail κ ((z - 3) / 2) := by
  simpa using oscillatoryMellinContinuationAtTop_single κ 2 (fun k => (k : ℂ) + 3) 1 z hN

/-- After two subtractions the two-term linear-phase example is the sum of its models. -/
theorem oscillatoryMellinContinuationAtTop_two_terms (κ : ℝ) (z : ℂ) :
    oscillatoryMellinContinuationAtTop
      (fun t : ℝ => exp (I * κ * t) * ((t : ℂ)⁻¹ + (t : ℂ)⁻¹ ^ 2)) κ 1
      (fun k => if k < 2 then 1 else 0) (fun k => (k : ℂ) + 1) 2 z =
        oscillatoryMellinTail κ (z - 1) + oscillatoryMellinTail κ (z - 2) := by
  have he (t : ℝ) : exp (I * κ * t) * ((t : ℂ)⁻¹ + (t : ℂ)⁻¹ ^ 2) -
      ∑ k ∈ range 2, (exp (I * κ * (t ^ (1 : ℝ) : ℝ)) *
        (t : ℂ) ^ (-((k : ℂ) + 1))) • (if k < 2 then (1 : ℂ) else 0) = 0 := by
    norm_num [Finset.sum_range_succ, cpow_neg, cpow_natCast, inv_pow]
    ring
  simp only [oscillatoryMellinContinuationAtTop, he]
  norm_num [mellinTruncHigh, mellinTruncLow, mellin, Finset.sum_range_succ]

/-- At one subtraction the remaining second power is absolutely Mellin integrable
for `Re z < 2`, and gives the second entire model. -/
theorem oscillatoryMellinContinuationAtTop_two_terms_one {κ : ℝ} (hκ : κ ≠ 0)
    {z : ℂ} (hz : z.re < 2) :
    oscillatoryMellinContinuationAtTop
      (fun t : ℝ => exp (I * κ * t) * ((t : ℂ)⁻¹ + (t : ℂ)⁻¹ ^ 2)) κ 1
      (fun k => if k < 2 then 1 else 0) (fun k => (k : ℂ) + 1) 1 z =
        oscillatoryMellinTail κ (z - 1) + oscillatoryMellinTail κ (z - 2) := by
  have he : (fun t : ℝ => exp (I * κ * t) * ((t : ℂ)⁻¹ + (t : ℂ)⁻¹ ^ 2) -
      ∑ k ∈ range 1, (exp (I * κ * (t ^ (1 : ℝ) : ℝ)) *
        (t : ℂ) ^ (-((k : ℂ) + 1))) • (if k < 2 then (1 : ℂ) else 0)) =
      (fun t : ℝ => exp (I * κ * t) * (t : ℂ) ^ (-(2 : ℂ))) := by
    funext t
    norm_num [cpow_neg, cpow_natCast, inv_pow]
    ring
  rw [oscillatoryMellinContinuationAtTop, he]
  have hm := Complex.hasMellin_indicator_exp_I_mul_rpow_cpow (κ := κ) (by norm_num : (0 : ℝ) < 1)
    (β := (2 : ℂ)) (z := z) (by simpa using hz)
  rw [mellinTruncHigh_eq_indicator]
  have hw : (z - 2).re < 0 := by
    change z.re - 2 < 0
    linarith
  have hm' : mellin ((Ioi (1 : ℝ)).indicator
      (fun t : ℝ => exp (I * κ * t) * (t : ℂ) ^ (-(2 : ℂ)))) z =
        oscillatoryMellinTail κ (z - 2) := by
    have hi : mellin ((Ioi (1 : ℝ)).indicator
        (fun t : ℝ => exp (I * κ * t) * (t : ℂ) ^ (-(2 : ℂ)))) z =
          oscillatoryMellinTailIntegral κ (z - 2) := by simpa using hm.2
    exact hi.trans (Complex.oscillatoryMellinTail_eq_integral hκ hw).symm
  rw [hm']
  norm_num
  ring

end DLMF.AsymptoticApproximations
