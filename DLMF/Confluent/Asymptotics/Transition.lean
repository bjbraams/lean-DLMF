/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Asymptotics.TransitionSaddle
public import DLMF.Confluent.Asymptotics.LargeArgument

/-!
# The diagonal transition expansion of Tricomi's function

The quadratic-saddle expansion proves DLMF 13.8.7 first for `Re a > 0`. At `z=b`, the
Tricomi contiguous relation reads `U(a-1,b,b)=2a U(a,b,b)+a(b-a-1) U(a+1,b,b)`.
It extends the same two-term remainder estimate to every complex first parameter.
Gamma duplication gives the stated DLMF normalization.
-/

@[expose] public noncomputable section

open Complex Filter Asymptotics
open scoped Real Topology

namespace DLMF.Confluent.KummerTransition

/-- The leading coefficient of the diagonal Tricomi expansion, with totalized Gamma. -/
def leadingCoefficient (a : ℂ) : ℂ := (Real.sqrt π:ℂ)*(2:ℂ)^(-a/2)/Gamma ((a+1)/2)
/-- The first correction coefficient of the diagonal Tricomi expansion. -/
def firstCorrection (a : ℂ) : ℂ := -(Real.sqrt π:ℂ)*(2:ℂ)^((3-a)/2)*(a+1)/(3*Gamma (a/2))
/-- The first two terms of the diagonal Tricomi expansion at a real second parameter. -/
def approximation (a : ℂ) (b : ℝ) : ℂ :=
  leadingCoefficient a*(b:ℂ)^(-a/2)+firstCorrection a*(b:ℂ)^(-(a+1)/2)

/-- The leading coefficient satisfies the contiguous downward recurrence. -/
lemma leadingCoefficient_sub_one (a : ℂ) :
    leadingCoefficient (a-1)=a*leadingCoefficient (a+1) := by
  have hG := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a/2)
  have hp : (2:ℂ)^(-(a-1)/2) = 2*(2:ℂ)^(-(a+1)/2) := by
    rw [show -(a-1)/2=1+(-(a+1)/2) by ring,cpow_add _ _ (by norm_num),cpow_one]
  dsimp only [leadingCoefficient]
  rw [show (a-1+1)/2=a/2 by ring,show (a+1+1)/2=a/2+1 by ring,hp]
  linear_combination (Real.sqrt π:ℂ)*2*(2:ℂ)^(-(a+1)/2)*hG

/-- The first correction coefficient satisfies the contiguous downward recurrence. -/
lemma firstCorrection_sub_one (a : ℂ) :
    firstCorrection (a-1)=2*a*leadingCoefficient a+a*firstCorrection (a+1) := by
  have hG := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one ((a-1)/2)
  have hp : (2:ℂ)^((3-(a-1))/2) = 2^2*(2:ℂ)^(-a/2) := by
    rw [show (3-(a-1))/2=2+(-a/2) by ring,cpow_add _ _ (by norm_num),cpow_ofNat]
  have hq : (2:ℂ)^((3-(a+1))/2) = 2*(2:ℂ)^(-a/2) := by
    rw [show (3-(a+1))/2=1+(-a/2) by ring,cpow_add _ _ (by norm_num),cpow_one]
  dsimp only [firstCorrection,leadingCoefficient]
  rw [hp,hq,show a-1+1=a by ring,show (a+1)/2=(a-1)/2+1 by ring]
  linear_combination -(Real.sqrt π:ℂ)*(4/3)*(2:ℂ)^(-a/2)*a*hG

/-- Gamma duplication identifies the leading saddle moment for `Re a > 0`. -/
lemma integralCoefficient_leading {a : ℂ} (ha : 0 < a.re) :
    1/Gamma a * (Gamma (a/2)*(1/2:ℂ)^(-(a/2))/2) = leadingCoefficient a := by
  have hdup := Gamma_mul_Gamma_add_half (a/2)
  rw [show a/2+1/2=(a+1)/2 by ring,show 2*(a/2)=a by ring] at hdup
  have hG : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha
  have hG1 : Gamma ((a+1)/2) ≠ 0 := Gamma_ne_zero_of_re_pos
    (by simp only [sub_re,neg_re,div_ofNat_re,add_re,one_re,natCast_re];linarith)
  rw [Complex.one_div_two_cpow_neg]
  dsimp only [leadingCoefficient]
  field_simp
  have hp : (2:ℂ)^(1-a)*(2:ℂ)^(a/2) = 2*(2:ℂ)^(-a/2) := by
    rw [←cpow_add _ _ (by norm_num),show 1-a+a/2=1+(-a/2) by ring,
      cpow_add _ _ (by norm_num),cpow_one]
  simp only [neg_div] at hp ⊢
  linear_combination (2:ℂ)^(a/2)*hdup+Gamma a*(Real.sqrt π:ℂ)*hp

/-- Gamma duplication identifies the first saddle correction for `Re a > 0`. -/
lemma integralCoefficient_correction {a : ℂ} (ha : 0 < a.re) :
    1/Gamma a * (Gamma ((a+1)/2)*(1/2:ℂ)^(-((a+1)/2))/2)*(-2*(a+1)/3) =
      firstCorrection a := by
  have hdup := Gamma_mul_Gamma_add_half (a/2)
  rw [show a/2+1/2=(a+1)/2 by ring,show 2*(a/2)=a by ring] at hdup
  have hG : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha
  have hG1 : Gamma (a/2) ≠ 0 := Gamma_ne_zero_of_re_pos
    (by simp only [sub_re,neg_re,div_ofNat_re,add_re,one_re,natCast_re];linarith)
  rw [Complex.one_div_two_cpow_neg]
  dsimp only [firstCorrection]
  field_simp
  have hp : (2:ℂ)^(1-a)*(2:ℂ)^((a+1)/2) = (2:ℂ)^((3-a)/2) := by
    rw [←cpow_add _ _ (by norm_num)]
    congr 1
    ring
  linear_combination -(a+1)*(2:ℂ)^((a+1)/2)*hdup-
    (a+1)*Gamma a*(Real.sqrt π:ℂ)*hp

/-- The two-term Tricomi expansion holds on the half-plane `Re a > 0`. -/
lemma isBigO_sub_approximation_of_re_pos {a : ℂ} (ha : 0 < a.re) :
    (fun b : ℝ => kummerU a b b-approximation a b) =O[atTop]
      (fun b : ℝ => (b:ℂ)^(-a/2-1)) := by
  have h := isBigO_integral_of_re_pos ha
  apply h.congr'
  · apply Eventually.of_forall
    intro b
    dsimp only [approximation]
    linear_combination -(b:ℂ)^(-a/2)*integralCoefficient_leading ha-
      (b:ℂ)^(-(a+1)/2)*integralCoefficient_correction ha
  · exact Eventually.of_forall fun b => by congr 1;ring

/-- The two-term Tricomi expansion gives its leading power bound. -/
lemma isBigO_kummerU_of_expansion {a : ℂ}
    (h : (fun b : ℝ => kummerU a b b-approximation a b) =O[atTop]
      (fun b : ℝ => (b:ℂ)^(-a/2-1))) :
    (fun b : ℝ => kummerU a b b) =O[atTop] (fun b : ℝ => (b:ℂ)^(-a/2)) := by
  have h0 : (fun b : ℝ => (b:ℂ)^(-a/2-1)) =O[atTop]
      (fun b : ℝ => (b:ℂ)^(-a/2)) := Asymptotics.isBigO_ofReal_cpow_of_re_le
        (by simp only [sub_re,neg_re,div_ofNat_re,add_re,one_re,natCast_re];linarith)
  have h1 : (fun b : ℝ => (b:ℂ)^(-(a+1)/2)) =O[atTop]
      (fun b : ℝ => (b:ℂ)^(-a/2)) := Asymptotics.isBigO_ofReal_cpow_of_re_le
        (by simp only [sub_re,neg_re,div_ofNat_re,add_re,one_re,natCast_re];linarith)
  have hm := ((isBigO_refl (fun b : ℝ => (b:ℂ)^(-a/2)) atTop).const_mul_left
    (leadingCoefficient a)).add (h1.const_mul_left (firstCorrection a))
  simpa only [approximation,sub_add_cancel] using (h.trans h0).add hm

/-- The Tricomi contiguous relation extends the two-term expansion down by one. -/
lemma isBigO_sub_approximation_sub_one {a : ℂ}
    (h0 : (fun b : ℝ => kummerU a b b-approximation a b) =O[atTop]
      (fun b : ℝ => (b:ℂ)^(-a/2-1)))
    (h1 : (fun b : ℝ => kummerU (a+1) b b-approximation (a+1) b) =O[atTop]
      (fun b : ℝ => (b:ℂ)^(-(a+1)/2-1))) :
    (fun b : ℝ => kummerU (a-1) b b-approximation (a-1) b) =O[atTop]
      (fun b : ℝ => (b:ℂ)^(-(a-1)/2-1)) := by
  have hpow : (fun b : ℝ => (b:ℂ)^(-a/2-1)) =O[atTop]
      (fun b : ℝ => (b:ℂ)^(-(a-1)/2-1)) := Asymptotics.isBigO_ofReal_cpow_of_re_le
        (by simp only [sub_re,neg_re,div_ofNat_re,add_re,one_re,natCast_re];linarith)
  have he0 := (h0.trans hpow).const_mul_left (2*a)
  have he1 := ((isBigO_refl (fun b : ℝ => (b:ℂ)) atTop).mul h1).const_mul_left a
  have he1' : (fun b : ℝ => a*((b:ℂ)*(kummerU (a+1) b b-approximation (a+1) b)))
      =O[atTop] (fun b : ℝ => (b:ℂ)^(-(a-1)/2-1)) := by
    refine he1.congr' EventuallyEq.rfl ?_
    filter_upwards [eventually_gt_atTop 0] with b hb
    nth_rw 1 [show (b:ℂ)=(b:ℂ)^(1:ℂ) by simp]
    rw [←cpow_add _ _ (ofReal_ne_zero.mpr hb.ne')]
    congr 1
    ring
  have hu := (isBigO_kummerU_of_expansion h1).const_mul_left (a*(a+1))
  have hu' : (fun b : ℝ => a*(a+1)*kummerU (a+1) b b) =O[atTop]
      (fun b : ℝ => (b:ℂ)^(-(a-1)/2-1)) := by
    convert hu using 2
    congr 1
    ring
  have hc : (fun b : ℝ => 2*a*firstCorrection a*(b:ℂ)^(-(a+1)/2)) =O[atTop]
      (fun b : ℝ => (b:ℂ)^(-(a-1)/2-1)) := by
    convert (isBigO_refl (fun b : ℝ => (b:ℂ)^(-(a+1)/2)) atTop).const_mul_left
      (2*a*firstCorrection a) using 2
    congr 1
    ring
  refine (((he0.add he1').sub hu').add hc).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with b hb
  have hb0 : (b:ℂ) ≠ 0 := ofReal_ne_zero.mpr hb.ne'
  have hU := kummerU_contiguous_a a (b:ℂ) b hb0
  have hp (v : ℂ) : (b:ℂ)*(b:ℂ)^v=(b:ℂ)^(1+v) := by
    rw [cpow_add _ _ hb0,cpow_one]
  have hp0 := hp (-(a+1)/2)
  have hp1 := hp (-(a+1+1)/2)
  rw [show 1+(-(a+1)/2)=-(a-1)/2 by ring] at hp0
  rw [show 1+(-(a+1+1)/2)=-a/2 by ring] at hp1
  dsimp only [approximation]
  rw [leadingCoefficient_sub_one,firstCorrection_sub_one]
  simp only [show a-1+1=a by ring,mul_add,mul_sub]
  linear_combination -hU-a*leadingCoefficient (a+1)*hp0-a*firstCorrection (a+1)*hp1

/-- The diagonal Tricomi expansion holds for every complex first parameter. -/
lemma isBigO_sub_approximation (a : ℂ) :
    (fun b : ℝ => kummerU a b b-approximation a b) =O[atTop]
      (fun b : ℝ => (b:ℂ)^(-a/2-1)) := by
  suffices h : ∀ m : ℕ, ∀ a : ℂ, 0 < (a+m).re →
      (fun b : ℝ => kummerU a b b-approximation a b) =O[atTop]
        (fun b : ℝ => (b:ℂ)^(-a/2-1)) by
    obtain ⟨m,hm⟩ := exists_nat_gt (-a.re)
    exact h m a (by simp only [sub_re,neg_re,div_ofNat_re,add_re,one_re,natCast_re] <;> linarith)
  intro m
  induction m with
  | zero => intro a ha;exact isBigO_sub_approximation_of_re_pos (by simpa using ha)
  | succ m ih =>
    intro a ha
    have h := isBigO_sub_approximation_sub_one
      (ih (a+1) (by simp at ha ⊢;linarith))
      (ih (a+1+1) (by simp at ha ⊢;linarith))
    simpa using h

/-- The coefficient form of the expansion equals the normalization in DLMF 13.8.7. -/
lemma approximation_eq {b : ℝ} (hb : 0 < b) (a : ℂ) :
    approximation a b =
      (Real.sqrt π:ℂ)*(2*b:ℂ)^(-(a/2))*
        (1/Gamma ((a+1)/2)-(a+1)*(8/b:ℂ)^(1/2:ℂ)/(3*Gamma (a/2))) := by
  have hb0 : (b:ℂ) ≠ 0 := ofReal_ne_zero.mpr hb.ne'
  have hp : (2*b:ℂ)^(-(a/2)) = (2:ℂ)^(-(a/2))*(b:ℂ)^(-(a/2)) := by
    simpa only [ofReal_mul,ofReal_ofNat] using
      mul_cpow_ofReal_nonneg (a := (2:ℝ)) (by norm_num) hb.le (-(a/2))
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
  have hrb : (b:ℂ)^(-(a+1)/2)=(b:ℂ)^(-(a/2))*(b:ℂ)^(-1/2:ℂ) := by
    rw [←cpow_add _ _ hb0]
    congr 1
    ring
  rw [hp,hq]
  dsimp only [approximation,leadingCoefficient,firstCorrection]
  rw [hr2,hrb]
  simp only [neg_div]
  ring

end DLMF.Confluent.KummerTransition

namespace DLMF.Confluent

/-- Identity under the stated parameter and domain assumptions: `Asymptotics.IsBigO atTop (fun b :
ℝ => kummerU a b b - (Real.sqrt π : ℂ) * (2 * b : ℂ) ^ (-(a / 2)) * (1 / Gamma ((a + 1) / 2) -
(a + 1) * (8 / b : ℂ) ^ (1 / 2 : ℂ) / (3 * Gamma (a / 2)))) (fun b : ℝ => (b : ℂ) ^ (-(a / 2)
- 1))`. -/
@[dlmf 13.8.E7]
theorem kummerU_transition (a : ℂ) :
    Asymptotics.IsBigO atTop
      (fun b : ℝ => kummerU a b b -
        (Real.sqrt π : ℂ) * (2 * b : ℂ) ^ (-(a / 2)) *
          (1 / Gamma ((a + 1) / 2) - (a + 1) * (8 / b : ℂ) ^ (1 / 2 : ℂ) / (3 * Gamma (a / 2))))
      (fun b : ℝ => (b : ℂ) ^ (-(a / 2) - 1)) := by
  refine (KummerTransition.isBigO_sub_approximation a).congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with b hb
    rw [KummerTransition.approximation_eq hb]
  · exact Eventually.of_forall fun b => by congr 1;ring

end DLMF.Confluent
