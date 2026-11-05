/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.WatsonSector
public import DLMFMathlib.Analysis.SpecialFunctions.ImproperIntegralsExtra
public import DLMFMathlib.Analysis.SpecialFunctions.Pow.RightHalfPlane

/-!
# Laplace transforms of complex powers times a sine or cosine

The Laplace transforms of `t^(s-1) sin(xt)` and `t^(s-1) cos(xt)` are expressed using
principal complex powers when the damping parameter is in the right half-plane. These
transforms also admit the arctangent forms used by the zeta integrals.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped Real

namespace Complex

/-- Absolute convergence and evaluation of the sine-modulated Gamma integral. -/
theorem integral_cpow_mul_cexp_neg_mul_mul_sin_Ioi {a s : ℂ}
    (ha : 0 < a.re) (hs : 0 < s.re) (x : ℝ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * exp (-(a * t)) *
      sin ((x : ℂ) * t)) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * exp (-(a * t)) *
        sin ((x : ℂ) * t)) =
          Gamma s * sin (s * arctan (x / a)) / (a ^ 2 + (x : ℂ) ^ 2) ^ (s / 2) := by
  have hp : 0 < (a + x * I).re := by simpa using ha
  have hm : 0 < (a - x * I).re := by simpa using ha
  let F : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 1) * exp (-(a * t)) * sin ((x : ℂ) * t)
  let P : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 1) * exp (-((a + x * I) * t))
  let Q : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 1) * exp (-((a - x * I) * t))
  have hP : IntegrableOn P (Ioi 0) := integrableOn_cpow_mul_exp_neg_mul hs hp
  have hQ : IntegrableOn Q (Ioi 0) := integrableOn_cpow_mul_exp_neg_mul hs hm
  have hF (t : ℝ) : F t = (Q t - P t) / (2 * I) := by
    have hep : exp (-(a * t)) * exp (-((x : ℂ) * t) * I) =
        exp (-((a + x * I) * t)) := by
      rw [← exp_add]
      congr 1
      ring
    have heq : exp (-(a * t)) * exp (((x : ℂ) * t) * I) =
        exp (-((a - x * I) * t)) := by
      rw [← exp_add]
      congr 1
      ring
    dsimp [F, P, Q]
    rw [sin]
    calc
      _ = ((t : ℂ) ^ (s - 1) * (exp (-(a * t)) * exp (-((x : ℂ) * t) * I)) -
          (t : ℂ) ^ (s - 1) * (exp (-(a * t)) * exp (((x : ℂ) * t) * I))) * I / 2 := by ring
      _ = _ := by
        rw [hep, heq]
        field_simp
        simp only [I_sq]
        ring
  have hFi : IntegrableOn F (Ioi 0) :=
    IntegrableOn.congr_fun ((hQ.sub hP).div_const (2 * I)) (fun t _ => (hF t).symm)
      measurableSet_Ioi
  refine ⟨hFi, ?_⟩
  change (∫ t in Ioi (0 : ℝ), F t) = _
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hF t), integral_div,
    integral_sub hQ hP]
  rw [show (∫ t in Ioi (0 : ℝ), Q t) = Gamma s * (a - x * I) ^ (-s) from
      integral_cpow_mul_cexp_neg_mul_Ioi hs hm,
    show (∫ t in Ioi (0 : ℝ), P t) = Gamma s * (a + x * I) ^ (-s) from
      integral_cpow_mul_cexp_neg_mul_Ioi hs hp]
  rw [← mul_sub, mul_div_assoc, ← sin_mul_arctan_div_cpow ha]
  ring

/-- Absolute convergence and evaluation of the cosine-modulated Gamma integral. -/
theorem integral_cpow_mul_cexp_neg_mul_mul_cos_Ioi {a s : ℂ}
    (ha : 0 < a.re) (hs : 0 < s.re) (x : ℝ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * exp (-(a * t)) *
      cos ((x : ℂ) * t)) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * exp (-(a * t)) *
        cos ((x : ℂ) * t)) =
          Gamma s * cos (s * arctan (x / a)) / (a ^ 2 + (x : ℂ) ^ 2) ^ (s / 2) := by
  have hp : 0 < (a + x * I).re := by simpa using ha
  have hm : 0 < (a - x * I).re := by simpa using ha
  let F : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 1) * exp (-(a * t)) * cos ((x : ℂ) * t)
  let P : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 1) * exp (-((a + x * I) * t))
  let Q : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 1) * exp (-((a - x * I) * t))
  have hP : IntegrableOn P (Ioi 0) := integrableOn_cpow_mul_exp_neg_mul hs hp
  have hQ : IntegrableOn Q (Ioi 0) := integrableOn_cpow_mul_exp_neg_mul hs hm
  have hF (t : ℝ) : F t = (Q t + P t) / 2 := by
    have hep : exp (-(a * t)) * exp (-((x : ℂ) * t) * I) =
        exp (-((a + x * I) * t)) := by
      rw [← exp_add]
      congr 1
      ring
    have heq : exp (-(a * t)) * exp (((x : ℂ) * t) * I) =
        exp (-((a - x * I) * t)) := by
      rw [← exp_add]
      congr 1
      ring
    dsimp [F, P, Q]
    rw [cos]
    rw [← hep, ← heq]
    ring

  have hFi : IntegrableOn F (Ioi 0) :=
    IntegrableOn.congr_fun ((hQ.add hP).div_const 2) (fun t _ => (hF t).symm)
      measurableSet_Ioi
  refine ⟨hFi, ?_⟩
  change (∫ t in Ioi (0 : ℝ), F t) = _
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hF t), integral_div,
    integral_add hQ hP]
  rw [show (∫ t in Ioi (0 : ℝ), Q t) = Gamma s * (a - x * I) ^ (-s) from
      integral_cpow_mul_cexp_neg_mul_Ioi hs hm,
    show (∫ t in Ioi (0 : ℝ), P t) = Gamma s * (a + x * I) ^ (-s) from
      integral_cpow_mul_cexp_neg_mul_Ioi hs hp]
  rw [← mul_add, mul_div_assoc, ← cos_mul_arctan_div_cpow ha]
  ring

end Complex
