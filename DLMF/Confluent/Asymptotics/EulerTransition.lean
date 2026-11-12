/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Asymptotics.EulerTransitionSaddle
public import DLMF.Gamma.Asymptotics.GammaRatioNormalization

/-!
# The diagonal transition expansion of Kummer's function

Euler's integral and its reflected quadratic saddle give the first two terms for
`M(a,b,b)` when `Re a > 0`. A Gamma-ratio estimate restores its normalization.
The diagonal contiguous relation then extends the same remainder estimate to every
complex first parameter, proving DLMF 13.8.6.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics
open DLMF.Hypergeometric
open scoped Real Topology

namespace DLMF.Confluent.KummerTransition

/-- The first two terms of the diagonal Kummer M expansion. -/
def eulerApproximation (a : ℂ) (b : ℝ) : ℂ :=
  leadingCoefficient a*(b:ℂ)^(a/2)-firstCorrection a*(b:ℂ)^((a-1)/2)

/-- The two-term Kummer approximation has its leading power bound. -/
lemma isBigO_eulerApproximation (a : ℂ) :
    eulerApproximation a =O[atTop] (fun b : ℝ => (b:ℂ)^(a/2)) := by
  have hc := Asymptotics.isBigO_ofReal_cpow_of_re_le
    (u := (a-1)/2) (v := a/2) (by simp;linarith)
  exact ((isBigO_refl (fun b : ℝ => (b:ℂ)^(a/2)) atTop).const_mul_left
    (leadingCoefficient a)).sub (hc.const_mul_left (firstCorrection a))

/-- The Kummer contiguous relation extends the two-term diagonal expansion
down by one in the first parameter. -/
lemma isBigO_kummerM_sub_one {a : ℂ}
    (h0 : (fun b : ℝ => kummerM a b b-eulerApproximation a b) =O[atTop]
      (fun b : ℝ => (b:ℂ)^(a/2-1)))
    (h1 : (fun b : ℝ => kummerM (a+1) b b-eulerApproximation (a+1) b) =O[atTop]
      (fun b : ℝ => (b:ℂ)^((a+1)/2-1))) :
    (fun b : ℝ => kummerM (a-1) b b-eulerApproximation (a-1) b) =O[atTop]
      (fun b : ℝ => (b:ℂ)^((a-1)/2-1)) := by
  have hinv :
      (fun b : ℝ => ((b:ℂ)-a)⁻¹) =O[atTop] (fun b : ℝ => (b:ℂ)^(-1:ℂ)) := by
    apply IsBigO.of_bound 2
    filter_upwards [eventually_gt_atTop (2*‖a‖+1)] with b hb
    have hb0 : 0 < b := by linarith [norm_nonneg a]
    have hnorm : b ≤ ‖(b:ℂ)-a‖+‖a‖ := by
      calc b = ‖(b:ℂ)‖ := by rw [norm_real,Real.norm_eq_abs,abs_of_pos hb0]
        _ = ‖((b:ℂ)-a)+a‖ := by congr 1;ring
        _ ≤ _ := norm_add_le _ _
    have hnormpos : 0 < ‖(b:ℂ)-a‖ := by linarith
    rw [norm_inv,norm_cpow_eq_rpow_re_of_pos hb0]
    norm_num only [neg_re,one_re,Real.rpow_neg_one]
    calc ‖(b:ℂ)-a‖⁻¹ = 1/‖(b:ℂ)-a‖ := by simp
      _ ≤ 2/b := (div_le_div_iff₀ hnormpos hb0).mpr (by linarith)
      _ = _ := by rw [div_eq_mul_inv]
  have hpow : (fun b : ℝ => (b:ℂ)^(a/2-1)) =O[atTop]
      (fun b : ℝ => (b:ℂ)^((a-1)/2)) :=
    Asymptotics.isBigO_ofReal_cpow_of_re_le (by simp;linarith)
  have he0 := (h0.trans hpow).const_mul_left (2*a)
  have he1 : (fun b : ℝ => a*(kummerM (a+1) b b-eulerApproximation (a+1) b)) =O[atTop]
      (fun b : ℝ => (b:ℂ)^((a-1)/2)) := by
    convert h1.const_mul_left a using 2
    congr 1
    ring
  have hc := (isBigO_refl (fun b : ℝ => (b:ℂ)^((a-1)/2)) atTop).const_mul_left
    (2*a*firstCorrection a)
  have hm := (isBigO_eulerApproximation (a-1)).const_mul_left a
  have he := (((he1.sub he0).add hc).add hm).mul hinv
  refine he.congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop (‖a‖+1)] with b hb
    have hb0 : 0 < b := by linarith [norm_nonneg a]
    have hbc : (b:ℂ) ≠ 0 := ofReal_ne_zero.mpr hb0.ne'
    have hba : (b:ℂ)-a ≠ 0 := by
      intro hh
      have hh' : (b:ℂ)=a := sub_eq_zero.mp hh
      have hn := congrArg norm hh'
      simp only [norm_real,Real.norm_of_nonneg hb0.le] at hn
      linarith
    apply (mul_inv_eq_iff_eq_mul₀ hba).mpr
    have hU := kummerM_contiguous_a (a := a) (b := (b:ℂ)) (z := (b:ℂ))
      (not_neg_nat_of_re_pos (by simpa using hb0))
    have hp (v : ℂ) : (b:ℂ)*(b:ℂ)^v=(b:ℂ)^(1+v) := by
      rw [cpow_add _ _ hbc,cpow_one]
    have hp0 := hp ((a-1)/2)
    have hp1 := hp ((a-1-1)/2)
    rw [show 1+(a-1)/2=(a+1)/2 by ring] at hp0
    rw [show 1+(a-1-1)/2=a/2 by ring] at hp1
    dsimp only [eulerApproximation]
    rw [leadingCoefficient_sub_one,firstCorrection_sub_one]
    simp only [show a+1-1=a by ring,mul_sub]
    linear_combination -hU+a*leadingCoefficient (a+1)*hp0-
      (2*a*leadingCoefficient a+a*firstCorrection (a+1))*hp1
  · filter_upwards [eventually_gt_atTop 0] with b hb
    rw [←cpow_add _ _ (ofReal_ne_zero.mpr hb.ne')]
    congr 1

/-- The reflected coefficient form equals the normalization in DLMF 13.8.6. -/
lemma reflected_approximation_eq {b : ℝ} (hb : 0 < b) (a : ℂ) :
    leadingCoefficient a*(b:ℂ)^(a/2)-firstCorrection a*(b:ℂ)^((a-1)/2) =
      (Real.sqrt π:ℂ)*(b/2:ℂ)^(a/2)*
        (1/Gamma ((a+1)/2)+(a+1)*(8/b:ℂ)^(1/2:ℂ)/(3*Gamma (a/2))) := by
  have hb0 : (b:ℂ) ≠ 0 := ofReal_ne_zero.mpr hb.ne'
  have hp : (b/2:ℂ)^(a/2) = (2:ℂ)^(-(a/2))*(b:ℂ)^(a/2) := by
    have hh := div_cpow_ofReal_nonneg (a := b) hb.le (by norm_num : (0:ℝ) ≤ 2) (a/2)
    simp only [ofReal_ofNat] at hh
    rw [hh, div_eq_mul_inv, ← cpow_neg]
    ring
  have hconst : (8:ℂ)^(1/2:ℂ)=(2:ℂ)^(3/2:ℂ) := by
    have h8 : log (8:ℂ)=(Real.log 8:ℂ) := by
      simpa only [ofReal_ofNat] using (ofReal_log (by norm_num : (0:ℝ) ≤ 8)).symm
    have h2 : log (2:ℂ)=(Real.log 2:ℂ) := by
      simpa only [ofReal_ofNat] using (ofReal_log (by norm_num : (0:ℝ) ≤ 2)).symm
    rw [cpow_def_of_ne_zero (by norm_num : (8:ℂ) ≠ 0),
      cpow_def_of_ne_zero (by norm_num : (2:ℂ) ≠ 0),
      h8,h2]
    congr 1
    have hlog : Real.log 8=3*Real.log 2 := by
      rw [show (8:ℝ)=(2:ℝ)^3 by norm_num,Real.log_pow]
      norm_num
    rw [hlog]
    push_cast
    ring
  have hq : (8/b:ℂ)^(1/2:ℂ)=(2:ℂ)^(3/2:ℂ)*(b:ℂ)^(-1/2:ℂ) := by
    have hh := div_cpow_ofReal_nonneg (a := (8:ℝ)) (by norm_num) hb.le (1/2:ℂ)
    simp only [ofReal_ofNat] at hh
    rw [hh,hconst,div_eq_mul_inv,←cpow_neg]
    congr 2
    ring
  have hr2 : (2:ℂ)^((3-a)/2)=(2:ℂ)^(-(a/2))*(2:ℂ)^(3/2:ℂ) := by
    rw [←cpow_add _ _ (by norm_num)]
    congr 1
    ring
  have hrb : (b:ℂ)^((a-1)/2)=(b:ℂ)^(a/2)*(b:ℂ)^(-1/2:ℂ) := by
    rw [←cpow_add _ _ hb0]
    congr 1
    ring
  rw [hp,hq]
  dsimp only [leadingCoefficient,firstCorrection]
  rw [hr2,hrb]
  simp only [neg_div]
  ring

/-- Gamma-ratio normalization gives the Kummer transition expansion for `Re a > 0`. -/
lemma isBigO_kummerM_of_re_pos {a : ℂ} (ha : 0 < a.re) :
    (fun b : ℝ => kummerM a b b-eulerApproximation a b) =O[atTop]
      (fun b : ℝ => (b:ℂ)^(a/2-1)) := by
  let J : ℝ → ℂ := fun b => 1/Gamma a*(∫ t in Ioo (0:ℝ) 1,
      (Real.exp (-b*eulerPhase t):ℂ)*(t:ℂ)^(a-1)*((1-t:ℝ):ℂ)^(-a-1))
  have hJ := isBigO_euler_integral_of_re_pos ha
  have h := DLMF.Gamma.GammaRatioNormalization.isBigO_mul_sub_two_term
    a (leadingCoefficient a) (firstCorrection a) J hJ
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop a.re] with b hb
  have hba : 0 < ((b:ℂ)-a).re := by simp;linarith
  dsimp only [J,eulerApproximation]
  congr 1
  rw [kummerM_eq_euler_integral ha hba,intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]
  rw [setIntegral_congr_fun measurableSet_Ioo (fun t ht => euler_kernel_eq a b ht.2)]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- The diagonal Kummer M expansion holds for every complex first parameter. -/
lemma isBigO_kummerM_all (a : ℂ) :
    (fun b : ℝ => kummerM a b b-eulerApproximation a b) =O[atTop]
      (fun b : ℝ => (b:ℂ)^(a/2-1)) := by
  suffices h : ∀ m : ℕ, ∀ a : ℂ, 0 < (a+m).re →
      (fun b : ℝ => kummerM a b b-eulerApproximation a b) =O[atTop]
        (fun b : ℝ => (b:ℂ)^(a/2-1)) by
    obtain ⟨m,hm⟩ := exists_nat_gt (-a.re)
    exact h m a (by simp;linarith)
  intro m
  induction m with
  | zero => intro a ha;exact isBigO_kummerM_of_re_pos (by simpa using ha)
  | succ m ih =>
    intro a ha
    have h := isBigO_kummerM_sub_one
      (ih (a+1) (by simp at ha ⊢;linarith))
      (ih (a+1+1) (by simp at ha ⊢;linarith))
    simpa using h

end DLMF.Confluent.KummerTransition

namespace DLMF.Confluent

/-- Identity under the stated parameter and domain assumptions: `Asymptotics.IsBigO atTop (fun b :
ℝ => kummerM a b b - (Real.sqrt π : ℂ) * (b / 2 : ℂ) ^ (a / 2) * (1 / Gamma ((a + 1) / 2) + (a
+ 1) * (8 / b : ℂ) ^ (1 / 2 : ℂ) / (3 * Gamma (a / 2)))) (fun b : ℝ => (b : ℂ) ^ (a / 2 -
1))`. -/
@[dlmf 13.8.E6]
theorem kummerM_transition (a : ℂ) :
    Asymptotics.IsBigO atTop
      (fun b : ℝ => kummerM a b b -
        (Real.sqrt π : ℂ) * (b / 2 : ℂ) ^ (a / 2) *
          (1 / Gamma ((a + 1) / 2) + (a + 1) * (8 / b : ℂ) ^ (1 / 2 : ℂ) / (3 * Gamma (a / 2))))
      (fun b : ℝ => (b : ℂ) ^ (a / 2 - 1)) := by
  refine (KummerTransition.isBigO_kummerM_all a).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with b hb
  dsimp only [KummerTransition.eulerApproximation]
  rw [KummerTransition.reflected_approximation_eq hb]

end DLMF.Confluent
