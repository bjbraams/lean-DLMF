/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Real powers in a ramified phase coordinate

The positive coordinate `h = u g^(1/μ)` converts ordinary powers of `h` to the
fractional-power scale of `u^μ g`. The corresponding density weights cancel even
when the complex density denominator is totalized at zero.
-/

@[expose] public noncomputable section

/-- Powers of a positive ramified coordinate agree with the corresponding phase powers. -/
theorem Real.rpow_ramified_phase (u g mu lam : ℝ) (n : ℕ) (hu : 0 < u) (hg : 0 < g)
    (hmu : mu ≠ 0) :
    (u * g ^ mu⁻¹) ^ ((n : ℝ) + lam - mu) =
      (u ^ mu * g) ^ (((n : ℝ) + lam - mu) / mu) := by
  rw [Real.mul_rpow hu.le (Real.rpow_nonneg hg.le _),
    Real.mul_rpow (Real.rpow_nonneg hu.le _) hg.le,
    ← Real.rpow_mul hg.le, ← Real.rpow_mul hu.le]
  congr 1
  · congr 1
    field_simp
  · congr 1
    field_simp

/-- The scalar factor arising from normalization of a ramified density cancels. -/
theorem Real.rpow_ramified_density_weights (u g mu lam : ℝ) (hu : 0 < u) (hg : 0 < g)
    (hmu : mu ≠ 0) :
    (u * g ^ mu⁻¹) ^ (lam - mu) * u ^ (1 - lam) * g ^ (1 - lam / mu) = u ^ (1 - mu) := by
  rw [Real.mul_rpow hu.le (Real.rpow_nonneg hg.le _), ← Real.rpow_mul hg.le]
  calc
    u ^ (lam - mu) * g ^ (mu⁻¹ * (lam - mu)) * u ^ (1 - lam) * g ^ (1 - lam / mu) =
        (u ^ (lam - mu) * u ^ (1 - lam)) *
          (g ^ (mu⁻¹ * (lam - mu)) * g ^ (1 - lam / mu)) := by ring
    _ = u ^ ((lam - mu) + (1 - lam)) *
        g ^ ((mu⁻¹ * (lam - mu)) + (1 - lam / mu)) := by
      rw [← Real.rpow_add hu, ← Real.rpow_add hg]
    _ = u ^ (1 - mu) := by
      have he : mu⁻¹ * (lam - mu) + (1 - lam / mu) = 0 := by field_simp; ring
      rw [he, Real.rpow_zero, mul_one]
      congr 1
      ring

/-- Normalized complex density weights cancel under the positive ramified coordinate. -/
theorem Complex.smul_ramified_density (u g mu lam : ℝ) (q d : ℂ) (hu : 0 < u) (hg : 0 < g)
    (hmu : mu ≠ 0) :
    (u * g ^ mu⁻¹) ^ (lam - mu) •
      ((u ^ (1 - lam) • q) / (u ^ (1 - mu) • d) *
        ((g ^ (1 - lam / mu) : ℝ) : ℂ)) = q / d := by
  have hB : ((u ^ (1 - mu) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hu _).ne'
  simp only [Complex.real_smul]
  rw [mul_div_mul_comm]
  calc
    (((u * g ^ mu⁻¹) ^ (lam - mu) : ℝ) : ℂ) *
        (((u ^ (1 - lam) : ℝ) : ℂ) / ((u ^ (1 - mu) : ℝ) : ℂ) * (q / d) *
          ((g ^ (1 - lam / mu) : ℝ) : ℂ)) =
      ((((u * g ^ mu⁻¹) ^ (lam - mu) : ℝ) : ℂ) * ((u ^ (1 - lam) : ℝ) : ℂ) *
          ((g ^ (1 - lam / mu) : ℝ) : ℂ) / ((u ^ (1 - mu) : ℝ) : ℂ)) * (q / d) := by
      simp only [div_eq_mul_inv]
      ring
    _ = q / d := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul,
        Real.rpow_ramified_density_weights u g mu lam hu hg hmu, div_self hB, one_mul]
