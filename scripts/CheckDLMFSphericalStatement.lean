/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import DLMF.EllipticIntegrals.SymmetricIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic
/-!
# A product-binder counterexample for DLMF 19.23.9

The missing denominator parentheses in the uncorrected transcription put the angular integral
inside the product. At `a = 0` and all `b` and `z` equal to one, the left side is one and the
literal right side is 4096. The independent angular-moment calculation uses no admitted
sphere representation. The corrected production theorem is audited below.
-/

public noncomputable section
open Complex Set MeasureTheory
open scoped Real
namespace DLMFStatementCorrections
/-- The first-octant angular moment at unit exponents is `1 / 8`. -/
lemma sphereAngularMoment_eq_one_eighth :
    (∫ φ in (0 : ℝ)..(π / 2), ∫ θ in (0 : ℝ)..(π / 2),
      ((∏ j : Fin 3, DLMF.EllipticIntegrals.directionCosines θ φ j : ℝ) : ℂ) *
        (Real.sin θ : ℂ)) = 1 / 8 := by
  have hθ : (∫ θ in (0 : ℝ)..(π / 2), Real.sin θ ^ 3 * Real.cos θ) = 1 / 4 := by
    have h := integral_sin_pow_mul_cos_pow_odd (a := (0 : ℝ)) (b := π / 2) 3 0
    norm_num only [zero_mul, zero_add, pow_one, pow_zero, mul_one,
      Real.sin_zero, Real.sin_pi_div_two] at h
    rw [integral_pow] at h
    norm_num at h
    exact h
  have hθC : (∫ θ in (0 : ℝ)..(π / 2),
      (Real.sin θ : ℂ) ^ 3 * (Real.cos θ : ℂ)) = (1 / 4 : ℂ) := by
    simp_rw [← ofReal_pow, ← ofReal_mul]
    rw [intervalIntegral.integral_ofReal, hθ]
    norm_num
  have hin (φ : ℝ) : (∫ θ in (0 : ℝ)..(π / 2),
      ((∏ j : Fin 3, DLMF.EllipticIntegrals.directionCosines θ φ j : ℝ) : ℂ) *
        (Real.sin θ : ℂ)) =
        (Real.sin φ * Real.cos φ : ℝ) * (1 / 4 : ℂ) := by
    rw [← hθC, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [DLMF.EllipticIntegrals.directionCosines, Fin.prod_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, ofReal_mul]
    ring_nf
  simp_rw [hin]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
    integral_sin_mul_cos₁]
  norm_num
/-- The product-bound interpretation of the transcribed denominator fails at unit data. -/
lemma sphere_three_product_binder_counterexample :
    let J : ℂ := ∫ φ in (0 : ℝ)..(π / 2), ∫ θ in (0 : ℝ)..(π / 2),
      ((∏ j : Fin 3, DLMF.EllipticIntegrals.directionCosines θ φ j : ℝ) : ℂ) *
        (Real.sin θ : ℂ)
    ¬ (DLMF.EllipticIntegrals.symmetricEllipticR 0 (fun _ : Fin 3 => 1) (fun _ => 1) =
      4 * Gamma (∑ _j : Fin 3, (1 : ℂ)) / ∏ _j : Fin 3, Gamma (1 : ℂ) * J) := by
  intro J
  have hΓ : Gamma (3 : ℂ) = 2 := by norm_num
  have hG : Gamma (∑ _j : Fin 3, (1 : ℂ)) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by norm_num [Fin.sum_univ_three])
  have hc := DLMF.EllipticIntegrals.symmetricEllipticR_const (ι := Fin 3) 0
    (fun _ => 1) one_mem_slitPlane hG
  simp only [neg_zero, cpow_zero] at hc
  dsimp only [J]
  rw [hc, sphereAngularMoment_eq_one_eighth]
  norm_num [Fin.sum_univ_three, Fin.prod_univ_three, hΓ]
#print axioms sphereAngularMoment_eq_one_eighth
#print axioms sphere_three_product_binder_counterexample
end DLMFStatementCorrections

#print axioms DLMF.EllipticIntegrals.symmetricEllipticR_three_eq_integral_sphere
