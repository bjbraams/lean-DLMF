/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Scorer.ExpansionsAndZeros
public import DLMF.Gamma.Integrals.ExponentialMellin
public import DLMFMathlib.Analysis.MellinCubicLaplace
public import DLMFMathlib.Analysis.MellinParseval

/-!
# Mellin–Barnes representation of the Scorer function Hi

Rotating the cubic Laplace integral by `-arg(-z)/4` makes both Laplace factors decay.
Mellin Parseval then gives DLMF 9.12.24 throughout `|arg(-z)| < 2π/3`, including absolute
integrability on every vertical line `-1 < Re s < 0` and convergence of both improper tails.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory
open scoped Real Topology
open DLMF.Core

namespace DLMF.Airy
namespace ScorerMellin
/-- A quarter-angle rotation places the cubic damping and Laplace argument in right half-planes. -/
theorem rotation_parameters {w : ℂ} (hw0 : w ≠ 0) (hw : |arg w| < 2 * π / 3) :
    let θ : ℝ := -arg w / 4
    let q : ℂ := w * exp (θ * I)
    let a : ℂ := exp ((3 * θ : ℝ) * I) / 3
    |θ| < π / 6 ∧ 0 < q.re ∧ 0 < a.re ∧
      log q = log w + θ * I ∧ log a = (3 * θ : ℝ) * I - log 3 := by
  dsimp only
  have hlog3 : (log (3 : ℂ)).im = 0 := by rw [log_im]; norm_num
  set θ : ℝ := -arg w / 4 with hθdef
  have hθ : |θ| < π / 6 := by rw [hθdef, abs_div, abs_neg]; norm_num; linarith
  have hs : |arg w + θ| < π / 2 := by
    rw [hθdef, show arg w + -arg w / 4 = 3 / 4 * arg w by ring,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4)]
    linarith
  have hcosq : 0 < Real.cos (arg w + θ) :=
    Real.cos_pos_of_mem_Ioo (abs_lt.mp hs)
  have hcosa : 0 < Real.cos (3 * θ) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [abs_lt.mp hθ]
  have heq : w * exp (θ * I) = exp (log w + θ * I) := by
    rw [exp_add, exp_log hw0]
  have hq : 0 < (w * exp (θ * I)).re := by
    rw [heq, exp_re]
    simp only [add_im, log_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re,
      mul_zero, add_zero]
    simpa only [add_zero] using mul_pos (Real.exp_pos (log w + θ * I).re) hcosq
  have ha : 0 < (exp ((3 * θ : ℝ) * I) / 3).re := by
    rw [div_ofNat_re, exp_ofReal_mul_I_re]
    exact div_pos hcosa (by norm_num)
  refine ⟨hθ, hq, ha, ?_, ?_⟩
  · rw [heq, log_exp]
    · simp only [add_im, log_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re,
        mul_zero, add_zero]; linarith [abs_lt.mp hs, Real.pi_pos]
    · simp only [add_im, log_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re,
        mul_zero, add_zero]; linarith [abs_lt.mp hs, Real.pi_pos]
  · rw [show exp ((3 * θ : ℝ) * I) / 3 = exp ((3 * θ : ℝ) * I - log 3) by
      rw [exp_sub, exp_log (by norm_num : (3 : ℂ) ≠ 0)], log_exp]
    · simp only [sub_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
        add_zero, hlog3, sub_zero]; linarith [abs_lt.mp hθ, Real.pi_pos]
    · simp only [sub_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
        add_zero, hlog3, sub_zero]; linarith [abs_lt.mp hθ, Real.pi_pos]

/-- The rotated cubic Mellin moment has a phase independent of the chosen integration ray. -/
theorem phase_factor {w : ℂ} (hw0 : w ≠ 0) {θ : ℝ}
    (hq : log (w * exp (θ * I)) = log w + θ * I)
    (ha : log (exp ((3 * θ : ℝ) * I) / 3) = (3 * θ : ℝ) * I - log 3) (s : ℂ) :
    exp (θ * I) * (w * exp (θ * I)) ^ s *
      (exp ((3 * θ : ℝ) * I) / 3) ^ (-((s + 1) / 3)) / 3 =
        (3 : ℂ) ^ (-2 / 3 : ℂ) * exp (s * (log 3 / 3 + log w)) := by
  rw [cpow_def_of_ne_zero (mul_ne_zero hw0 (exp_ne_zero _)),
    cpow_def_of_ne_zero (div_ne_zero (exp_ne_zero _) (by norm_num)),
    cpow_def_of_ne_zero (by norm_num : (3 : ℂ) ≠ 0), hq, ha]
  rw [div_eq_mul_inv, show (3 : ℂ)⁻¹ = exp (-log 3) by
    rw [exp_neg, exp_log (by norm_num : (3 : ℂ) ≠ 0)]]
  simp only [← exp_add]
  congr 1
  push_cast
  ring

/-- The Scorer function `Hi` as a Laplace integral on a ray with `|θ| < π/6`. -/
theorem scorerHi_eq_rotated {z : ℂ} {θ : ℝ} (hθ : |θ| < π / 6) :
    π * scorerHi z = exp (θ * I) * ∫ t : ℝ in Ioi 0,
      exp (-((-z * exp (θ * I)) * t)) *
        exp (-((exp ((3 * θ : ℝ) * I) / 3) * (t : ℂ) ^ 3)) := by
  rw [ScorerExpansions.scorerHi_eq, ScorerExpansions.laplace_rotate 0 hθ]
  simp only [smul_eq_mul, pow_zero, one_mul]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  congr 2
  have he : exp (θ * I) ^ 3 = exp ((3 * θ : ℝ) * I) := by
    rw [← exp_nat_mul]; congr 1; push_cast; ring
  rw [mul_pow, he]
  ring

end ScorerMellin

open ScorerMellin Complex.CubicLaplace

/-- Mellin–Barnes integral for `Hi` on a vertical line `Re s = σ ∈ (-1, 0)`, for
`|arg(-z)| < 2π/3`; boundary values are ordinary improper integrals (DLMF 9.12.24). -/
@[dlmf 9.12.E24]
theorem scorerHi_mellinBarnes {z : ℂ} (hz0 : z ≠ 0) (hz : |arg (-z)| < 2 * π / 3) {σ : ℝ}
    (hσ0 : -1 < σ) (hσ1 : σ < 0) :
    HasIntegralWholeLine (fun y : ℝ => Gamma (1 / 3 + ((σ : ℂ) + y * I) / 3) *
      Gamma (-((σ : ℂ) + y * I)) *
        exp (((σ : ℂ) + y * I) * (log (3 : ℂ) / 3 + log (-z))))
      (2 * π ^ 2 * (3 : ℂ) ^ (2 / 3 : ℂ) * scorerHi z) := by
  set θ : ℝ := -arg (-z) / 4 with hθdef
  set q : ℂ := -z * exp (θ * I) with hqdef
  set a : ℂ := exp ((3 * θ : ℝ) * I) / 3 with hadef
  set p : ℝ := σ + 1 with hpdef
  have hp0 : 0 < p := by dsimp [p]; linarith
  have hp1 : p < 1 := by dsimp [p]; linarith
  have hw0 : -z ≠ 0 := neg_ne_zero.mpr hz0
  obtain ⟨hθ, hq, ha, hlogq, hloga⟩ := rotation_parameters hw0 hz
  change |θ| < π / 6 at hθ
  change 0 < q.re at hq
  change 0 < a.re at ha
  change log q = log (-z) + θ * I at hlogq
  change log a = (3 * θ : ℝ) * I - log 3 at hloga
  let B : ℝ → ℂ := fun y => Gamma (1 / 3 + ((σ : ℂ) + y * I) / 3) *
    Gamma (-((σ : ℂ) + y * I)) *
      exp (((σ : ℂ) + y * I) * (log (3 : ℂ) / 3 + log (-z)))
  let M : ℝ → ℂ := fun y =>
    (Gamma (1 - ((p : ℂ) + y * I)) * q ^ (-(1 - ((p : ℂ) + y * I)))) *
      (Gamma (((p : ℂ) + y * I) / 3) * a ^ (-(((p : ℂ) + y * I) / 3)) / 3)
  have hMf (y : ℝ) : mellin (fun t : ℝ => exp (-(q * t)))
      (1 - ((p : ℂ) + y * I)) =
        Gamma (1 - ((p : ℂ) + y * I)) * q ^ (-(1 - ((p : ℂ) + y * I))) :=
    mellin_exp_neg_mul (by simpa using sub_pos.mpr hp1) hq
  have hMg (y : ℝ) : mellin (fun t : ℝ => exp (-(a * (t : ℂ) ^ 3)))
      ((p : ℂ) + y * I) =
        Gamma (((p : ℂ) + y * I) / 3) * a ^ (-(((p : ℂ) + y * I) / 3)) / 3 :=
    mellin_exp_neg_mul_cube (by simpa using hp0) ha
  have hfM : Integrable (fun y : ℝ => mellin (fun t : ℝ => exp (-(q * t)))
      (1 - ((p : ℂ) + y * I))) := by
    have hg := DLMF.Gamma.integrable_Gamma_mul_cpow_neg (c := 1 - p) (by linarith) hq
    convert hg.comp_neg using 1
    funext y
    rw [hMf]
    congr 2 <;> push_cast <;> ring
  have hpoint (y : ℝ) : exp (θ * I) * M y = (3 : ℂ) ^ (-2 / 3 : ℂ) * B y := by
    set s : ℂ := (σ : ℂ) + y * I with hsdef
    have hline : (p : ℂ) + y * I = s + 1 := by dsimp [p, s]; push_cast; ring
    change exp (θ * I) *
      ((Gamma (1 - ((p : ℂ) + y * I)) * q ^ (-(1 - ((p : ℂ) + y * I)))) *
        (Gamma (((p : ℂ) + y * I) / 3) * a ^ (-(((p : ℂ) + y * I) / 3)) / 3)) =
      (3 : ℂ) ^ (-2 / 3 : ℂ) * (Gamma (1 / 3 + s / 3) * Gamma (-s) *
        exp (s * (log 3 / 3 + log (-z))))
    rw [hline, show (1 : ℂ) - (s + 1) = -s by ring, neg_neg]
    have hphase : exp (θ * I) * q ^ s * a ^ (-((s + 1) / 3)) / 3 =
        (3 : ℂ) ^ (-2 / 3 : ℂ) * exp (s * (log 3 / 3 + log (-z))) :=
      phase_factor hw0 hlogq hloga s
    calc _ = Gamma ((s + 1) / 3) * Gamma (-s) *
        (exp (θ * I) * q ^ s * a ^ (-((s + 1) / 3)) / 3) := by ring
      _ = _ := by rw [hphase, show (s + 1) / 3 = 1 / 3 + s / 3 by ring]; ring
  have hM : Integrable M := by
    have hm : AEStronglyMeasurable (fun y : ℝ =>
        mellin (fun t : ℝ => exp (-(a * (t : ℂ) ^ 3))) ((p : ℂ) + y * I)) := by
      simp_rw [hMg]
      exact Measurable.aestronglyMeasurable (by fun_prop)
    have hprod := hfM.bdd_mul hm
      (Eventually.of_forall fun y => norm_mellin_exp_neg_mul_cube_le p y a)
    convert hprod using 1
    funext y
    rw [hMf, hMg]
    ring
  have hcancel : (3 : ℂ) ^ (2 / 3 : ℂ) * (3 : ℂ) ^ (-2 / 3 : ℂ) = 1 := by
    rw [← cpow_add _ _ (by norm_num), show (2 / 3 : ℂ) + -2 / 3 = 0 by ring, cpow_zero]
  have hBscaled : Integrable (fun y => (3 : ℂ) ^ (-2 / 3 : ℂ) * B y) :=
    (hM.const_mul (exp (θ * I))).congr (Eventually.of_forall hpoint)
  have hB : Integrable B := by
    have h := hBscaled.const_mul ((3 : ℂ) ^ (2 / 3 : ℂ))
    simpa only [← mul_assoc, hcancel, one_mul] using h
  have hI : exp (θ * I) * ∫ y : ℝ, M y =
      (3 : ℂ) ^ (-2 / 3 : ℂ) * ∫ y : ℝ, B y := by
    rw [← integral_const_mul, integral_congr_ae (Eventually.of_forall hpoint),
      integral_const_mul]
  have hf : MellinConvergent (fun t : ℝ => exp (-(q * t))) (1 - (p : ℂ)) :=
    mellinConvergent_exp_neg_mul (by simp only [sub_re, one_re, ofReal_re]; linarith) hq
  have hg : MellinConvergent (fun t : ℝ => exp (-(a * (t : ℂ) ^ 3))) (p : ℂ) :=
    mellinConvergent_exp_neg_mul_cube (by simpa using hp0) ha
  have hL := integral_mul_eq_mellin_parseval hf hg (Or.inr hfM)
  simp_rw [hMf, hMg] at hL
  have hrot := scorerHi_eq_rotated (z := z) hθ
  change π * scorerHi z = exp (θ * I) * ∫ t : ℝ in Ioi 0,
    exp (-(q * t)) * exp (-(a * (t : ℂ) ^ 3)) at hrot
  have hmain : π * scorerHi z = (1 / (2 * π) : ℂ) *
      (3 : ℂ) ^ (-2 / 3 : ℂ) * ∫ y : ℝ, B y := by
    rw [hrot, hL]
    calc _ = (1 / (2 * π) : ℂ) * (exp (θ * I) * ∫ y : ℝ, M y) := by dsimp only [M]; ring
      _ = _ := by rw [hI]; ring
  have hπ0 : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpref : (2 * π * (3 : ℂ) ^ (2 / 3 : ℂ)) *
      ((1 / (2 * π) : ℂ) * (3 : ℂ) ^ (-2 / 3 : ℂ)) = 1 := by
    calc _ = (3 : ℂ) ^ (2 / 3 : ℂ) * (3 : ℂ) ^ (-2 / 3 : ℂ) := by field_simp
      _ = 1 := hcancel
  have hval : ∫ y : ℝ, B y = 2 * π ^ 2 * (3 : ℂ) ^ (2 / 3 : ℂ) * scorerHi z := by
    calc _ = (2 * π * (3 : ℂ) ^ (2 / 3 : ℂ)) *
        ((1 / (2 * π) : ℂ) * (3 : ℂ) ^ (-2 / 3 : ℂ) * ∫ y : ℝ, B y) := by
          rw [← mul_assoc, hpref, one_mul]
      _ = (2 * π * (3 : ℂ) ^ (2 / 3 : ℂ)) * (π * scorerHi z) := by rw [hmain]
      _ = _ := by ring
  refine ⟨∫ y : ℝ in Iic 0, B y, ∫ y : ℝ in Ioi 0, B y,
    intervalIntegral_tendsto_integral_Iic 0 hB.integrableOn tendsto_id,
    intervalIntegral_tendsto_integral_Ioi 0 hB.integrableOn tendsto_id, ?_⟩
  rw [← hval]
  simpa using integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hB


end DLMF.Airy
