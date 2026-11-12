/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Basic.InceParity

/-!
# Mixed double orthogonality of paraboloidal wave functions

The mixed cosine-sine double orthogonality of DLMF 28.31.24 follows from parity and period
`2π`. The inner angular integral vanishes by reflection, so this result holds for arbitrary
indices, every real parameter, and any complex origin of the vertical line.

## Main results

* `integral_paraboloidalHc_mul_paraboloidalHs`: the angular integral vanishes.
* `paraboloidalHc_Hs_double_orthogonal'`: mixed double orthogonality.
-/

public noncomputable section

open Complex Set

namespace DLMF.Mathieu

/-- The product of cosine and sine paraboloidal waves integrates to zero against
`A - cos(2v)` over a full period. -/
lemma integral_paraboloidalHc_mul_paraboloidalHs (p₁ m₁ p₂ m₂ : ℕ) (ξ : ℝ) (A : ℂ) :
    (∫ v : ℝ in (0 : ℝ)..2 * Real.pi, paraboloidalHc p₁ m₁ v ξ *
      paraboloidalHs p₂ m₂ v ξ * (A - Complex.cos (2 * v))) = 0 := by
  let f : ℝ → ℂ := fun v => paraboloidalHc p₁ m₁ v ξ *
    paraboloidalHs p₂ m₂ v ξ * (A - Complex.cos (2 * v))
  have hreflect (v : ℝ) : f (2 * Real.pi - v) = -f v := by
    dsimp only [f]
    have hc : paraboloidalHc p₁ m₁ ((2 * Real.pi - v : ℝ) : ℂ) ξ =
        paraboloidalHc p₁ m₁ v ξ := by
      rw [ofReal_sub, ofReal_mul, ofReal_ofNat]
      have harg : (2 : ℂ) * Real.pi - (v : ℂ) = -(v : ℂ) + 2 * Real.pi := by ring
      rw [harg]
      have hp := periodic_paraboloidalHc p₁ m₁ ξ (-v)
      dsimp only at hp
      rw [hp, paraboloidalHc_neg]
    have hs : paraboloidalHs p₂ m₂ ((2 * Real.pi - v : ℝ) : ℂ) ξ =
        -paraboloidalHs p₂ m₂ v ξ := by
      rw [ofReal_sub, ofReal_mul, ofReal_ofNat]
      have harg : (2 : ℂ) * Real.pi - (v : ℂ) = -(v : ℂ) + 2 * Real.pi := by ring
      rw [harg]
      have hp := periodic_paraboloidalHs p₂ m₂ ξ (-v)
      dsimp only at hp
      rw [hp, paraboloidalHs_neg]
    rw [hc, hs, ofReal_sub, ofReal_mul, ofReal_ofNat]
    have he : Complex.cos (2 * ((2 : ℂ) * Real.pi - v)) = Complex.cos (2 * v) := by
      have harg : (2 : ℂ) * (2 * Real.pi - v) = -(2 * v) + 2 * (2 * Real.pi) := by ring
      have hcos : Complex.cos (-(2 * v : ℂ) + 2 * (2 * Real.pi)) =
          Complex.cos (-(2 * v)) := by
        simpa using Complex.cos_add_nat_mul_two_pi (-(2 * v : ℂ)) 2
      rw [harg, hcos, Complex.cos_neg]
    rw [he]
    ring
  have h := intervalIntegral.integral_comp_sub_left
    (a := (0 : ℝ)) (b := 2 * Real.pi) f (2 * Real.pi)
  simp only [sub_self, sub_zero] at h
  have hr : (∫ v : ℝ in (0 : ℝ)..2 * Real.pi, f (2 * Real.pi - v)) =
      -(∫ v : ℝ in (0 : ℝ)..2 * Real.pi, f v) := by
    simp_rw [hreflect]
    exact intervalIntegral.integral_neg
  rw [hr] at h
  dsimp only [f] at h ⊢
  linear_combination (-1 / 2 : ℂ) * h

/-- Double orthogonality of the cosine and sine paraboloidal wave functions, stronger than
DLMF, which assumes nonzero `ξ`, admissible indices, and a particular vertical-line origin. -/
@[dlmf 28.31.E24 "stronger than DLMF: arbitrary indices, ξ and complex vertical-line origin"]
theorem paraboloidalHc_Hs_double_orthogonal' (p₁ m₁ p₂ m₂ : ℕ) (ξ : ℝ) (u₀ : ℂ) :
    (∫ t in Ioi (0 : ℝ), ∫ v in (0 : ℝ)..2 * Real.pi,
      paraboloidalHc p₁ m₁ (u₀ + I * t) ξ * paraboloidalHc p₁ m₁ v ξ *
        paraboloidalHs p₂ m₂ (u₀ + I * t) ξ * paraboloidalHs p₂ m₂ v ξ *
        (Complex.cos (2 * (u₀ + I * t)) - Complex.cos (2 * v))) = 0 := by
  have hi (t : ℝ) : (∫ v in (0 : ℝ)..2 * Real.pi,
      paraboloidalHc p₁ m₁ (u₀ + I * t) ξ * paraboloidalHc p₁ m₁ v ξ *
        paraboloidalHs p₂ m₂ (u₀ + I * t) ξ * paraboloidalHs p₂ m₂ v ξ *
        (Complex.cos (2 * (u₀ + I * t)) - Complex.cos (2 * v))) = 0 := by
    have he (v : ℝ) : paraboloidalHc p₁ m₁ (u₀ + I * t) ξ * paraboloidalHc p₁ m₁ v ξ *
        paraboloidalHs p₂ m₂ (u₀ + I * t) ξ * paraboloidalHs p₂ m₂ v ξ *
        (Complex.cos (2 * (u₀ + I * t)) - Complex.cos (2 * v)) =
      (paraboloidalHc p₁ m₁ (u₀ + I * t) ξ * paraboloidalHs p₂ m₂ (u₀ + I * t) ξ) *
        (paraboloidalHc p₁ m₁ v ξ * paraboloidalHs p₂ m₂ v ξ *
        (Complex.cos (2 * (u₀ + I * t)) - Complex.cos (2 * v))) := by ring
    simp_rw [he]
    rw [intervalIntegral.integral_const_mul, integral_paraboloidalHc_mul_paraboloidalHs, mul_zero]
  simp_rw [hi]
  simp only [MeasureTheory.integral_zero]

end DLMF.Mathieu
