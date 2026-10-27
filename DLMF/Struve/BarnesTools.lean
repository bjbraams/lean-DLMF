/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.ComplexBinet
public import DLMF.Gamma.ShiftedLineBounds
public import Mathlib.MeasureTheory.Integral.Asymptotics

/-!
# Estimates for the Mellin–Barnes integrand of the Struve function

Tools for the Barnes integral of `H_ν` (DLMF 11.5.8), whose integrand on `s = t + iy` is
`π/sin(πs) · w^s / (Γ(3/2+s) Γ(3/2+ν+s))`:

* `struveBar_recip_Gamma_isBigO`: on a shifted vertical line,
  `1/|Γ(a + i(y+m))| = O(y^{1/2-a} e^{πy/2})` as `y → +∞` (Stirling, DLMF 5.11.9, from
  `DLMF.Gamma.tendsto_norm_Gamma_vertical_div`);
* `struveBar_pi_div_sin_le`, `struveBar_pi_div_sin_isBigO`: `π/|sin(π(t+iy))| ≤ 4π e^{-πy}`
  for `y ≥ 1`;
* `struveBar_isBigO`: the product `π/|sin| · 1/|Γ(a+iy)| · 1/|Γ(b+i(y+m))|` is `O(y^{1-a-b})`;
* `struveBar_integrableOn_rpow_div_Gamma`: `w^t/(Γ(α+t)Γ(β+t))` is integrable on `(c, ∞)`;
* `struveBar_integrable_of_isBigO`: continuous functions with `O(|y|^p)` tails, `p < -1`, are
  integrable on `ℝ`.
-/

@[expose] public section

noncomputable section

open Complex Filter Set MeasureTheory Asymptotics
open scoped Real Topology

namespace DLMF.Struve

/-- `(y + m)^q ≤ 2^|q| y^q` once `y ≥ 2|m|`, `y > 0`. -/
theorem struveBar_rpow_shift_le {y m q : ℝ} (hy : 0 < y) (hym : 2 * |m| ≤ y) :
    (y + m) ^ q ≤ (2 : ℝ) ^ |q| * y ^ q := by
  have h1 : y / 2 ≤ y + m := by linarith [neg_abs_le m]
  have h2 : y + m ≤ 2 * y := by linarith [le_abs_self m, abs_nonneg m]
  have hy2 : 0 < y / 2 := by linarith
  rcases le_total 0 q with hq | hq
  · calc (y + m) ^ q ≤ (2 * y) ^ q := Real.rpow_le_rpow (by linarith) h2 hq
      _ = (2 : ℝ) ^ |q| * y ^ q := by
        rw [Real.mul_rpow (by norm_num) hy.le, abs_of_nonneg hq]
  · calc (y + m) ^ q ≤ (y / 2) ^ q := Real.rpow_le_rpow_of_nonpos hy2 h1 hq
      _ = (2 : ℝ) ^ |q| * y ^ q := by
        rw [Real.div_rpow hy.le (by norm_num), abs_of_nonpos hq, Real.rpow_neg (by norm_num),
          div_eq_mul_inv, mul_comm]

/-- Stirling on a shifted vertical line: `1/|Γ(a + i(y+m))| = O(y^{1/2-a} e^{πy/2})`. -/
theorem struveBar_recip_Gamma_isBigO (a m : ℝ) :
    (fun y : ℝ => (‖Gamma ((a : ℂ) + ((y : ℂ) + m) * I)‖)⁻¹) =O[atTop]
      (fun y : ℝ => y ^ (1 / 2 - a) * Real.exp (π * y / 2)) := by
  have hE := (Asymptotics.isEquivalent_of_tendsto_one
    (DLMF.Gamma.tendsto_norm_Gamma_vertical_div a)).comp_tendsto
    (tendsto_atTop_add_const_right atTop m tendsto_id)
  have hE' := hE.inv.isBigO
  refine (hE'.congr_left fun y => ?_).trans ?_
  · simp only [Function.comp_apply, Pi.inv_apply, id]
    congr 3; push_cast; ring
  refine Asymptotics.IsBigO.of_bound ((Real.sqrt (2 * π))⁻¹ * Real.exp (π * m / 2) *
    (2 : ℝ) ^ |1 / 2 - a|) ?_
  filter_upwards [eventually_ge_atTop (2 * |m| + 1)] with y hy
  have hy0 : 0 < y := by linarith [abs_nonneg m]
  have hym : 0 < y + m := by linarith [neg_abs_le m]
  simp only [Function.comp_apply, Pi.inv_apply, id, abs_of_pos hym, norm_inv, norm_mul,
    Real.norm_eq_abs]
  rw [abs_of_pos (Real.sqrt_pos.mpr (by positivity)), abs_of_pos (Real.rpow_pos_of_pos hym _),
    abs_of_pos (Real.exp_pos _), abs_of_pos (Real.rpow_pos_of_pos hy0 _), abs_of_pos (Real.exp_pos _)]
  rw [mul_inv, mul_inv, ← Real.rpow_neg hym.le, ← Real.exp_neg,
    show -(a - 1 / 2) = 1 / 2 - a by ring,
    show -(-π * (y + m) / 2) = π * m / 2 + π * y / 2 by ring, Real.exp_add]
  have hs := struveBar_rpow_shift_le (q := 1 / 2 - a) hy0 (by linarith)
  have hp : 0 ≤ (√(2 * π))⁻¹ * rexp (π * m / 2) := by positivity
  calc (√(2 * π))⁻¹ * (y + m) ^ (1 / 2 - a) * (rexp (π * m / 2) * rexp (π * y / 2))
      = ((√(2 * π))⁻¹ * rexp (π * m / 2)) * (y + m) ^ (1 / 2 - a) * rexp (π * y / 2) := by ring
    _ ≤ ((√(2 * π))⁻¹ * rexp (π * m / 2)) * ((2 : ℝ) ^ |1 / 2 - a| * y ^ (1 / 2 - a)) *
        rexp (π * y / 2) := by gcongr
    _ = _ := by ring


/-- `π/|sin(π(t+iy))| ≤ 4π e^{-πy}` for `y ≥ 1`. -/
theorem struveBar_pi_div_sin_le (t : ℝ) {y : ℝ} (hy : 1 ≤ y) :
    π / ‖sin (π * ((t : ℂ) + y * I))‖ ≤ 4 * π * Real.exp (-(π * y)) := by
  have hpy : π ≤ π * y := by nlinarith [Real.pi_pos]
  have hs := Complex.barnesRes_abs_sinh_le_norm_sin (π * t) (π * y)
  rw [show (π : ℂ) * ((t : ℂ) + y * I) = ((π * t : ℝ) : ℂ) + ((π * y : ℝ) : ℂ) * I by
    push_cast; ring]
  have he : 2 ≤ Real.exp (π * y) := by
    have := Real.add_one_le_exp (π * y); linarith [Real.two_le_pi]
  have hsh : Real.exp (π * y) / 4 ≤ |Real.sinh (π * y)| := by
    rw [Real.sinh_eq]
    have h1 : Real.exp (-(π * y)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [Real.pi_pos])
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hpos : 0 < Real.exp (π * y) / 4 := by positivity
  calc π / ‖sin (((π * t : ℝ) : ℂ) + ((π * y : ℝ) : ℂ) * I)‖ ≤ π / (Real.exp (π * y) / 4) :=
        div_le_div_of_nonneg_left Real.pi_pos.le hpos (hsh.trans hs)
    _ = 4 * π * Real.exp (-(π * y)) := by
        rw [Real.exp_neg]; field_simp

/-- `π/|sin(π(t+iy))| = O(e^{-πy})` as `y → +∞`. -/
theorem struveBar_pi_div_sin_isBigO (t : ℝ) :
    (fun y : ℝ => π / ‖sin (π * ((t : ℂ) + y * I))‖) =O[atTop]
      (fun y : ℝ => Real.exp (-(π * y))) := by
  refine Asymptotics.IsBigO.of_bound (4 * π) ?_
  filter_upwards [eventually_ge_atTop 1] with y hy
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (div_nonneg Real.pi_pos.le (norm_nonneg _))]
  exact struveBar_pi_div_sin_le t hy

/-- **Decay of the Barnes integrand of `H_ν` on horizontal lines** (Stirling, DLMF 5.11.9):
`π/|sin(π(t+iy))| · 1/|Γ(a+iy)| · 1/|Γ(b+i(y+m))| = O(y^{1-a-b})` as `y → +∞`. -/
theorem struveBar_isBigO (t a b m : ℝ) :
    (fun y : ℝ => π / ‖sin (π * ((t : ℂ) + y * I))‖ * (‖Gamma ((a : ℂ) + y * I)‖)⁻¹ *
      (‖Gamma ((b : ℂ) + ((y : ℂ) + m) * I)‖)⁻¹) =O[atTop] (fun y : ℝ => y ^ (1 - a - b)) := by
  have h1 := struveBar_pi_div_sin_isBigO t
  have h2 := struveBar_recip_Gamma_isBigO a 0
  have h3 := struveBar_recip_Gamma_isBigO b m
  simp only [ofReal_zero, add_zero] at h2
  refine ((h1.mul h2).mul h3).trans (Filter.EventuallyEq.isBigO ?_)
  filter_upwards [eventually_gt_atTop 0] with y hy
  rw [show (1 - a - b) = (1 / 2 - a) + (1 / 2 - b) by ring, Real.rpow_add hy]
  have : Real.exp (-(π * y)) * Real.exp (π * y / 2) * Real.exp (π * y / 2) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf; simp
  linear_combination (y ^ (1 / 2 - a) * y ^ (1 / 2 - b)) * this

/-- `t ↦ w^t / (Γ(α+t) Γ(β+t))` is continuous on `[c, ∞)` when `α + c, β + c > 0`. -/
theorem struveBar_continuousOn_rpow_div_Gamma {α β w c : ℝ} (hα : 0 < α + c) (hβ : 0 < β + c)
    (hw : 0 < w) :
    ContinuousOn (fun t : ℝ => w ^ t / (Real.Gamma (α + t) * Real.Gamma (β + t))) (Ici c) := by
  intro t ht
  have ht' : c ≤ t := ht
  have hG : ∀ x : ℝ, 0 < x → ContinuousAt Real.Gamma x := fun x hx =>
    (Real.differentiableAt_Gamma fun m => by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      intro h; linarith).continuousAt
  refine ContinuousAt.continuousWithinAt ?_
  refine ContinuousAt.div (Real.continuousAt_const_rpow hw.ne') ?_ ?_
  · exact ((hG (α + t) (by linarith)).comp (continuousAt_const.add continuousAt_id)).mul
      ((hG (β + t) (by linarith)).comp (continuousAt_const.add continuousAt_id))
  · exact mul_ne_zero (Real.Gamma_pos_of_pos (by linarith)).ne'
      (Real.Gamma_pos_of_pos (by linarith)).ne'

/-- `t ↦ w^t / (Γ(α+t) Γ(β+t))` is integrable on `(c, ∞)` when `α + c, β + c > 0`
(factorial decay, `DLMF.Gamma.shiftB_Gamma_ge`). -/
theorem struveBar_integrableOn_rpow_div_Gamma {α β w c : ℝ} (hα : 0 < α + c) (hβ : 0 < β + c)
    (hw : 0 < w) :
    IntegrableOn (fun t : ℝ => w ^ t / (Real.Gamma (α + t) * Real.Gamma (β + t))) (Ioi c) := by
  set f := fun t : ℝ => w ^ t / (Real.Gamma (α + t) * Real.Gamma (β + t)) with hf
  have hcont := struveBar_continuousOn_rpow_div_Gamma hα hβ hw
  set T : ℝ := max (max c 0) (max (1 - α) (1 - β)) with hT
  have hcT : c ≤ T := le_trans (le_max_left _ _) (le_max_left _ _)
  have h1 : IntegrableOn f (Icc c T) :=
    (hcont.mono Icc_subset_Ici_self).integrableOn_compact isCompact_Icc
  set A : ℝ := Real.exp 1 * (w + 1) with hA
  have hA0 : 0 < A := by positivity
  have hwA : w / A ≤ Real.exp (-1) := by
    rw [div_le_iff₀ hA0, hA, ← mul_assoc, ← Real.exp_add]; simp
  set C : ℝ := Real.exp (A + 1 + 2) * A ^ (1 - α) with hC
  have h2 : IntegrableOn f (Ioi T) := by
    refine ((exp_neg_integrableOn_Ioi T one_pos).const_mul C).mono'
      ((hcont.mono fun t ht => le_trans hcT (le_of_lt ht)).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht' : T < t := ht
    have ht0 : 0 ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht'.le
    have hT2 : max (1 - α) (1 - β) ≤ T := le_max_right _ _
    have hta : 1 ≤ α + t := by linarith [le_max_left (1 - α) (1 - β)]
    have htb : 1 ≤ β + t := by linarith [le_max_right (1 - α) (1 - β)]
    have hg1 := DLMF.Gamma.shiftB_Gamma_ge hta hA0
    have hg2 := DLMF.Gamma.shiftB_Gamma_ge htb one_pos
    rw [Real.one_rpow, one_mul, show (1 : ℝ) + 1 = 2 by norm_num] at hg2
    have hp1 : 0 < A ^ (α + t - 1) * Real.exp (-(A + 1)) := by positivity
    have hp2 : 0 < Real.exp (-2) := Real.exp_pos _
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.rpow_nonneg hw.le _)
      (mul_nonneg (Real.Gamma_pos_of_pos (by linarith)).le (Real.Gamma_pos_of_pos (by linarith)).le))]
    calc w ^ t / (Real.Gamma (α + t) * Real.Gamma (β + t))
        ≤ w ^ t / ((A ^ (α + t - 1) * Real.exp (-(A + 1))) * Real.exp (-2)) :=
          div_le_div_of_nonneg_left (Real.rpow_nonneg hw.le _) (by positivity)
            (mul_le_mul hg1 hg2 hp2.le (Real.Gamma_pos_of_pos (by linarith)).le)
      _ = C * (w / A) ^ t := by
          rw [hC, Real.div_rpow hw.le hA0.le, show α + t - 1 = t - (1 - α) by ring,
            Real.rpow_sub hA0, show A + 1 + 2 = (A + 1) + 2 by ring, Real.exp_add,
            Real.exp_neg, Real.exp_neg]
          have : 0 < A ^ t := Real.rpow_pos_of_pos hA0 _
          have : 0 < A ^ (1 - α) := Real.rpow_pos_of_pos hA0 _
          field_simp
      _ ≤ C * Real.exp (-1 * t) := by
          gcongr
          calc (w / A) ^ t ≤ Real.exp (-1) ^ t := Real.rpow_le_rpow (by positivity) hwA ht0
            _ = Real.exp (-1 * t) := by rw [← Real.exp_mul]
  refine (integrableOn_union.mpr ⟨h1, h2⟩).mono_set fun t ht => ?_
  by_cases htT : t ≤ T
  · exact Or.inl ⟨le_of_lt ht, htT⟩
  · exact Or.inr (lt_of_not_ge htT)

/-- `y^p = O((1 + |y|)^p)` as `y → +∞`, for `p ≤ 0`. -/
theorem struveBar_rpow_isBigO_one_add {p : ℝ} (hp : p ≤ 0) :
    (fun y : ℝ => y ^ p) =O[atTop] (fun y : ℝ => (1 + ‖y‖) ^ p) := by
  refine Asymptotics.IsBigO.of_bound ((2 : ℝ) ^ (-p)) ?_
  filter_upwards [eventually_ge_atTop 1] with y hy
  have hy0 : 0 < y := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hy0,
    abs_of_pos (Real.rpow_pos_of_pos hy0 _), abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)]
  have h := Real.rpow_le_rpow_of_nonpos (by linarith : (0 : ℝ) < 1 + y)
    (by linarith : 1 + y ≤ 2 * y) hp
  rw [Real.mul_rpow (by norm_num) hy0.le] at h
  have h2 : (2 : ℝ) ^ (-p) * (2 : ℝ) ^ p = 1 := by
    rw [← Real.rpow_add (by norm_num)]; simp
  have h3 : 0 ≤ (2 : ℝ) ^ (-p) := by positivity
  calc y ^ p = (2 : ℝ) ^ (-p) * ((2 : ℝ) ^ p * y ^ p) := by
        rw [← mul_assoc, h2, one_mul]
    _ ≤ (2 : ℝ) ^ (-p) * (1 + y) ^ p := mul_le_mul_of_nonneg_left h h3

/-- A continuous function on `ℝ` with `O(|y|^p)` tails at both ends, `p < -1`, is integrable. -/
theorem struveBar_integrable_of_isBigO {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : Continuous f) {p : ℝ} (hp : p < -1)
    (h1 : f =O[atTop] (fun y : ℝ => y ^ p)) (h2 : (fun y => f (-y)) =O[atTop] (fun y : ℝ => y ^ p)) :
    Integrable f := by
  have hg : Integrable (fun y : ℝ => (1 + ‖y‖) ^ p) := by
    have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := -p) (by simp; linarith)
    simpa using this
  have hO := struveBar_rpow_isBigO_one_add (by linarith : p ≤ 0)
  have hbot : f =O[atBot] (fun y : ℝ => (1 + ‖y‖) ^ p) := by
    have := (h2.trans hO).comp_tendsto tendsto_neg_atBot_atTop
    simpa [Function.comp_def] using this
  exact hf.locallyIntegrable.integrable_of_isBigO_atBot_atTop hbot (hg.integrableAtFilter _)
    (h1.trans hO) (hg.integrableAtFilter _)

end DLMF.Struve
