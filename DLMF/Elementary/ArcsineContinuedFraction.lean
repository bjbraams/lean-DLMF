/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import DLMF.Elementary.Basic.InverseTrigonometric
public import DLMF.Hypergeometric.ContinuedFractions
import DLMF.Hypergeometric.Elementary.AlgebraicValues
import DLMFMathlib.Analysis.ContinuedFraction.JacobiValueRegion
public import DLMFMathlib.Analysis.Complex.RealSegmentComplement
public import DLMF.Elementary.Basic.InverseHyperbolic
public import DLMF.IncompleteGamma.FractionTools
public import TauCeti.Analysis.Normed.Group.LocallyBounded
import TauCeti.Analysis.Complex.Conformal.Vitali
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
# Continued fractions for the inverse sine

The arcsine continued fraction has paired numerators `-2,-2,-12,-12,…` and odd
Jacobi denominators. Positive rational rescaling makes its Jacobi matrix diagonally
dominant, giving pole-free finite convergents and uniform bounds outside `[-1,1]`.

* `ArcsineContinuedFraction.convergent_bound`: the full exterior-segment value bound.
-/

public noncomputable section
open Complex Set Filter GenContFract
open scoped Topology Nat
namespace DLMF.Elementary.ArcsineContinuedFraction

/-- The even index `2⌈k/2⌉` in each pair of equal arcsine partial numerators. -/
def pairedIndex (k : ℕ) : ℕ := 2 * ((k + 1) / 2)
/-- The paired index as a natural quotient. -/
lemma pairedIndex_def (k : ℕ) : pairedIndex k = 2 * ((k + 1) / 2) := by rfl
/-- Every noninitial pair index is at least two. -/
lemma pairedIndex_succ_two_le (k : ℕ) : 2 ≤ pairedIndex (k + 1) := by
  rw [pairedIndex_def]
  omega
/-- Consecutive paired indices add to `2k + 2`. -/
lemma pairedIndex_add_succ (k : ℕ) : pairedIndex k + pairedIndex (k + 1) = 2 * k + 2 := by
  simp only [pairedIndex_def]
  omega

/-- Positive rational scaling weights making the arcsine Jacobi matrix diagonally dominant. -/
def weight : ℕ → ℝ
  | 0 => 1
  | k + 1 => weight k * (pairedIndex (k + 1) - 1) / pairedIndex (k + 1)
/-- The initial scaling weight is one. -/
lemma weight_zero : weight 0 = 1 := by rfl
/-- Each scaling weight is obtained by its successive rational factor. -/
lemma weight_succ (k : ℕ) : weight (k + 1) =
    weight k * (pairedIndex (k + 1) - 1) / pairedIndex (k + 1) := by rfl
/-- Every scaling weight is positive. -/
lemma weight_pos (k : ℕ) : 0 < weight k := by
  induction k with
  | zero => rw [weight_zero];norm_num
  | succ k ih =>
    rw [weight_succ]
    have h : (1 : ℝ) < pairedIndex (k + 1) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) (pairedIndex_succ_two_le k))
    exact div_pos (mul_pos ih (sub_pos.mpr h)) (by linarith)
/-- The scaling recurrence with its denominator cleared. -/
lemma weight_succ_mul_index (k : ℕ) :
    weight (k + 1) * pairedIndex (k + 1) = weight k * (pairedIndex (k + 1) - 1) := by
  rw [weight_succ]
  have hn : (pairedIndex (k + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (by have h := pairedIndex_succ_two_le k;omega : pairedIndex (k + 1) ≠ 0)
  exact div_mul_cancel₀ _ hn

/-- The Jacobi numerators for the Cauchy form of the arcsine fraction. -/
def numerator (k : ℕ) : ℂ := if k = 0 then 1 else
  -((pairedIndex k - 1) * (pairedIndex k) : ℕ)
/-- The Jacobi denominators `(2k + 1)z`. -/
def denominator (z : ℂ) (k : ℕ) : ℂ := (2 * k + 1) * z
/-- The finite arcsine Jacobi convergent. -/
def convergent (n : ℕ) (z : ℂ) : ℂ := (ofFun 0 numerator (denominator z)).convs n

/-- The defining paired numerator formula. -/
lemma numerator_def (k : ℕ) : numerator k = if k = 0 then 1 else
    -(((pairedIndex k - 1) * pairedIndex k : ℕ) : ℂ) := by rfl

/-- The defining odd denominator formula. -/
lemma denominator_def (z : ℂ) (k : ℕ) : denominator z k = (2 * k + 1) * z := by rfl

/-- The defining finite generalized continued fraction. -/
lemma convergent_def (n : ℕ) (z : ℂ) :
    convergent n z = (ofFun 0 numerator (denominator z)).convs n := by rfl

/-- Rational rescaling turns every noninitial numerator into a negative square. -/
lemma scaled_numerator (k : ℕ) (hk : 1 ≤ k) :
    ((weight (k - 1) : ℂ) * weight k) * numerator k = -((weight k : ℂ) * pairedIndex k) ^ 2 := by
  have hk0 : k ≠ 0 := by omega
  have hidx : 2 ≤ pairedIndex k := by
    simpa only [Nat.sub_add_cancel hk] using pairedIndex_succ_two_le (k - 1)
  have hr := congrArg (fun r : ℝ => (r : ℂ)) (weight_succ_mul_index (k - 1))
  simp only [Nat.sub_add_cancel hk,ofReal_mul,ofReal_sub,ofReal_natCast,ofReal_one] at hr
  simp only [numerator,hk0,↓reduceIte]
  push_cast [Nat.cast_sub (by omega : 1 ≤ pairedIndex k)]
  linear_combination ((weight k : ℂ) * (pairedIndex k : ℂ)) * hr

/-- The finite arcsine convergents are pole-free and bounded off the real unit segment. -/
lemma convergent_bound {z : ℂ} (hz : z ∈ realSegmentComplement (-1) 1) (n : ℕ) :
    (ofFun 0 numerator (denominator z)).dens n ≠ 0 ∧
      ‖convergent n z‖ ≤ 1 / max (|z.re| - 1) |z.im| := by
  let A : ℕ → ℂ := fun k =>
    (if k = 0 then (weight 0 : ℂ) else (weight (k - 1) : ℂ) * weight k) * numerator k
  let B : ℕ → ℂ := fun k => (weight k : ℂ) * denominator z k
  let c : ℕ → ℝ := fun k => weight k * pairedIndex k
  let d : ℕ → ℝ := fun k => weight k * (2 * k + 1)
  have hdom (k : ℕ) : c k + c (k + 1) ≤ d k := by
    dsimp only [c,d]
    rw [weight_succ_mul_index]
    have hid := congrArg (fun r : ℕ => (r : ℝ)) (pairedIndex_add_succ k)
    push_cast at hid
    have he := congrArg (fun r : ℝ => weight k * r) hid
    linarith [he]
  have ha (k : ℕ) (hk : 1 ≤ k) : A k = -(c k : ℂ) ^ 2 := by
    simp only [A,show k ≠ 0 by omega,↓reduceIte,c,ofReal_mul,ofReal_natCast]
    exact scaled_numerator k hk
  have hb (k : ℕ) : B k = (d k : ℂ) * z := by
    dsimp [B,d,denominator]
    push_cast
    ring
  have hh := ofFun_jacobi_bound (a := A) (b := B)
    (max_abs_re_sub_one_abs_im_pos hz) (fun k => mul_nonneg (weight_pos k).le (Nat.cast_nonneg _))
    (fun k => mul_pos (weight_pos k) (by positivity)) hdom ha hb n
  have he := ofFun_convs_equiv (h := (0 : ℂ)) (a := numerator) (b := denominator z)
    (fun k => (weight k : ℂ)) (fun k => ofReal_ne_zero.mpr (weight_pos k).ne') n
  have hd := (ofFun_continuants_equiv (h := (0 : ℂ)) (a := numerator) (b := denominator z)
    (fun k => (weight k : ℂ)) n).1
  refine ⟨fun h0 => hh.1 (by rw [hd,h0,mul_zero]), ?_⟩
  rw [he] at hh
  simpa [A,d,weight_zero,numerator,convergent] using hh.2

open DLMF.Hypergeometric

/-- The specialized Gauss partial numerators are negative at positive arguments. -/
lemma gaussPartialNumerator_neg {t : ℝ} (ht : 0 < t) (k : ℕ) :
    GaussContinuedFraction.partialNumReal 1 0 (1 / 2) t k < 0 := by
  unfold GaussContinuedFraction.partialNumReal
  have hm : (0 : ℝ) ≤ ((k + 1) / 2 : ℕ) := Nat.cast_nonneg _
  split_ifs with h
  · nlinarith [mul_pos (mul_pos (by nlinarith [hm] : 0 < 1 + (((k + 1) / 2 : ℕ) : ℝ))
      (by nlinarith [hm] : 0 < 1 / 2 - 0 + (((k + 1) / 2 : ℕ) : ℝ))) ht]
  · have hNat : 1 ≤ (k + 1) / 2 := by omega
    have hm1 : (1 : ℝ) ≤ ((k + 1) / 2 : ℕ) := by exact_mod_cast hNat
    nlinarith [mul_pos (mul_pos (by linarith : 0 < 0 + (((k + 1) / 2 : ℕ) : ℝ))
      (by linarith : 0 < 1 / 2 - 1 + (((k + 1) / 2 : ℕ) : ℝ))) ht]

/-- Shifting the Gauss tail by two shifts its three parameters by `(1,1,2)`. -/
lemma gaussBackwardSolution_shift (t : ℝ) (j : ℕ) :
    GaussContinuedFraction.backwardSolutionReal 1 0 (1 / 2) t (j + 2) =
      GaussContinuedFraction.backwardSolutionReal 2 1 (5 / 2) t j := by
  dsimp only [GaussContinuedFraction.backwardSolutionReal]
  rw [show (j + 2) / 2 = j / 2 + 1 by omega,show (j + 2 + 1) / 2 = (j + 1) / 2 + 1 by omega]
  push_cast
  congr 1 <;> ring

/-- The Gauss tail numerators have the same two-step parameter shift. -/
lemma gaussPartialNumerator_shift (t : ℝ) (j : ℕ) :
    GaussContinuedFraction.partialNumReal 1 0 (1 / 2) t (j + 2) =
      GaussContinuedFraction.partialNumReal 2 1 (5 / 2) t j := by
  dsimp only [GaussContinuedFraction.partialNumReal]
  rw [show (j + 2 + 1)%2 = (j + 1)%2 by omega,show (j + 2 + 1) / 2 = (j + 1) / 2 + 1 by omega]
  split_ifs <;> push_cast <;> ring

/-- The specialized Gauss numerators are one-quarter of the paired arcsine numerators. -/
lemma gaussPartialNumerator_eq_paired (t : ℝ) (k : ℕ) :
    GaussContinuedFraction.partialNumReal 1 0 (1 / 2) t k =
      -(((2 * ((k + 2) / 2) - 1) * (2 * ((k + 2) / 2)) : ℕ) : ℝ) * t / 4 := by
  rcases Nat.even_or_odd' k with ⟨m,rfl|rfl⟩
  · simp only [GaussContinuedFraction.partialNumReal,
      show (2 * m + 1)%2 = 1 by omega,show (2 * m + 1) / 2 = m by omega,↓reduceIte,
      show (2 * m + 2) / 2 = m + 1 by omega,show 2 * (m + 1) - 1 = 2 * m + 1 by omega]
    push_cast
    ring
  · simp only [GaussContinuedFraction.partialNumReal,
      show (2 * m + 1 + 1)%2 = 0 by omega,show (2 * m + 1 + 1) / 2 = m + 1 by omega,
      show (2 * m + 1 + 2) / 2 = m + 1 by omega,show 2 * (m + 1) - 1 = 2 * m + 1 by omega]
    norm_num only [zero_ne_one,↓reduceIte]
    push_cast
    ring

/-- The reciprocal Gauss fraction has leading numerator one. -/
def gaussNumerator (t : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1 else GaussContinuedFraction.partialNumReal 1 0 (1 / 2) t (k - 1)
/-- The reciprocal Gauss denominators start at one-half. -/
def gaussDenominator (k : ℕ) : ℝ := 1 / 2 + k

/-- The leading-one numerator formula for the reciprocal Gauss fraction. -/
lemma gaussNumerator_def (t : ℝ) (k : ℕ) : gaussNumerator t k =
    if k = 0 then 1 else GaussContinuedFraction.partialNumReal 1 0 (1 / 2) t (k - 1) := by rfl

/-- The shifted-half denominator formula for the reciprocal Gauss fraction. -/
lemma gaussDenominator_def (k : ℕ) : gaussDenominator k = 1 / 2 + k := by rfl

/-- The specialized reciprocal Gauss fraction converges on a positive real interval. -/
lemma tendsto_gauss_inverse {t : ℝ} (ht : 0 < t) (ht2 : t < 1 / 2) :
    Tendsto (ofFun 0 (gaussNumerator t) gaussDenominator).convs atTop
      (𝓝 (GaussContinuedFraction.backwardSolutionReal 1 0 (1 / 2) t 1 /
        GaussContinuedFraction.backwardSolutionReal 1 0 (1 / 2) t 0)) := by
  let w := GaussContinuedFraction.backwardSolutionReal 1 0 (1 / 2) t
  have ht1 : t < 1 := by linarith
  have hta : |t| < 1 := by rwa [abs_of_pos ht]
  have hrec (k : ℕ) : w k =
      gaussDenominator k * w (k + 1) + gaussNumerator t (k + 1) * w (k + 2) := by
    simpa only [w,gaussDenominator,gaussNumerator,Nat.add_one_ne_zero,↓reduceIte,
      Nat.add_sub_cancel] using GaussContinuedFraction.backwardSolutionReal_rec 1 0 (1 / 2) hta k
  have hpos (j : ℕ) : 0 < w j := by
    dsimp only [w,GaussContinuedFraction.backwardSolutionReal]
    exact GaussContinuedFraction.realSum_pos
      (by positivity) (by positivity) (by positivity) ht.le ht1
  have hne (j : ℕ) : gaussNumerator t j ≠ 0 := by
    by_cases hj : j = 0
    · simp [gaussNumerator,hj]
    · simp only [gaussNumerator,hj,↓reduceIte]
      exact (gaussPartialNumerator_neg ht _).ne
  have hrat (k : ℕ) (hk : 2 ≤ k) :
      2 * (-gaussNumerator t (k + 1)) * w (k + 2) ≤ gaussDenominator k * w (k + 1) := by
    have h := GaussContinuedFraction.partialNumReal_mul_le (a := 2) (b := 1) (c := 5 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) ht1 ht ht2 (k - 2)
    rw [← gaussPartialNumerator_shift,← gaussBackwardSolution_shift,
      ← gaussBackwardSolution_shift] at h
    have hki : k - 2 + 2 = k := by omega
    have hk1 : k - 2 + 1 + 2 = k + 1 := by omega
    simp only [gaussNumerator,Nat.add_one_ne_zero,↓reduceIte,Nat.add_sub_cancel,
      gaussDenominator,w]
    rw [hki,hk1] at h
    rw [show (5 / 2 : ℝ) + ((k - 2 : ℕ) : ℝ) = 1 / 2 + (k : ℝ) by
      push_cast [Nat.cast_sub hk];ring] at h
    exact h
  have hh := tendsto_ofFun_convs_of_ratio_real (h := (0 : ℝ)) hrec (hpos 0).ne' hne (N := 2)
    (fun j _ => (hpos j).ne') (fun k _ => by
      have hn : gaussNumerator t (k + 1) < 0 := by
        simpa only [gaussNumerator,Nat.add_one_ne_zero,↓reduceIte,Nat.add_sub_cancel] using
          gaussPartialNumerator_neg ht k
      exact mul_neg_of_pos_of_neg (hpos k) (mul_neg_of_neg_of_pos hn (hpos (k + 2))))
    (fun k hk => by
      have hn : gaussNumerator t (k + 1) < 0 := by
        simpa only [gaussNumerator,Nat.add_one_ne_zero,↓reduceIte,Nat.add_sub_cancel] using
          gaussPartialNumerator_neg ht k
      rw [abs_of_neg (mul_neg_of_neg_of_pos hn (hpos (k + 2))),abs_of_pos (hpos k)]
      have h := hrat k hk
      have hr := hrec k
      nlinarith)
  simpa only [gaussNumerator,↓reduceIte,zero_add,one_mul] using hh

/-- Inversion maps the exterior unit-segment domain into the arcsine two-ray slit. -/
lemma inv_mem_arcsinCutPlane {z : ℂ} (hz : z ∈ realSegmentComplement (-1) 1) :
    z⁻¹ ∈ arcsinCutPlane := by
  have hz0 : z ≠ 0 := by intro h;subst z;norm_num [realSegmentComplement] at hz
  by_cases him : z.im = 0
  · have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [him]
    have hreal : 1 < |z.re| := by
      rcases hz with h | h | h
      · exact False.elim (h him)
      · linarith [neg_le_abs z.re]
      · exact h.trans_le (le_abs_self z.re)
    right
    rw [he,← ofReal_inv,ofReal_re,abs_inv]
    exact (inv_lt_one₀ (by linarith : 0 < |z.re|)).mpr hreal
  · left
    rw [inv_im]
    exact div_ne_zero (neg_ne_zero.mpr him) (normSq_pos.mpr hz0).ne'

/-- The Cauchy form `arcsin(1/z)/sqrt(1-1/z²)` on the exterior unit-segment domain. -/
def value (z : ℂ) : ℂ := arcsinPrincipal z⁻¹ / Complex.sqrt (1 - (z⁻¹) ^ 2)

/-- The defining principal arcsine quotient. -/
lemma value_def (z : ℂ) : value z = arcsinPrincipal z⁻¹ / Complex.sqrt (1 - (z⁻¹) ^ 2) := by rfl

/-- The arcsine Cauchy target is holomorphic off the real unit segment. -/
lemma differentiableOn_value : DifferentiableOn ℂ value (realSegmentComplement (-1) 1) := by
  intro z hz
  have hz0 : z ≠ 0 := by intro h;subst z;norm_num [realSegmentComplement] at hz
  have hdom := inv_mem_arcsinCutPlane hz
  have hq := Trigonometric.one_sub_sq_slit hdom
  have hroot : Complex.sqrt (1 - (z⁻¹) ^ 2) ≠ 0 := by
    intro h
    have hs := Trigonometric.complexSqrt_sq (1 - (z⁻¹) ^ 2)
    rw [h,zero_pow two_ne_zero] at hs
    exact slitPlane_ne_zero hq hs.symm
  have hi : DifferentiableAt ℂ (fun z : ℂ => z⁻¹) z := differentiableAt_id.inv hz0
  have ha := (analytic_arcsin_principal _ hdom).differentiableAt.comp z hi
  have hs := (Trigonometric.hasDerivAt_complexSqrt hq).differentiableAt.comp z
    ((differentiableAt_const (1 : ℂ)).sub (hi.pow 2))
  exact (ha.div hs hroot).differentiableWithinAt

/-- The principal arcsine equals its Gauss hypergeometric series in the unit disk. -/
lemma arcsinPrincipal_eq_gauss {z : ℂ} (hz : ‖z‖ < 1) :
    arcsinPrincipal z = z * ₂F₁ (1 / 2 : ℂ) (1 / 2) (3 / 2) (z ^ 2) := by
  have h := log_add_sqrt (z := I * z) (by simpa only [norm_mul,norm_I,one_mul] using hz)
  rw [mul_pow,I_sq,neg_one_mul,neg_neg] at h
  have harg : 1 + -(z ^ 2) = 1 - z ^ 2 := by ring
  rw [harg] at h
  have hsqrt : Complex.sqrt (1 - z ^ 2) = (1 - z ^ 2) ^ (1 / 2 : ℂ) := by
    rw [Complex.sqrt]
    norm_num
  rw [arcsinPrincipal,hsqrt,add_comm _ (I * z),← h]
  linear_combination -(z * ₂F₁ (1 / 2 : ℂ) (1 / 2) (3 / 2) (z ^ 2)) * I_sq

/-- Euler transformation identifies the Gauss quotient with the normalized arcsine. -/
lemma mul_gauss_eq_arcsin_div_sqrt {z : ℂ} (hz : ‖z‖ < 1) :
    z * ₂F₁ (1 : ℂ) 1 (3 / 2) (z ^ 2) = arcsinPrincipal z / Complex.sqrt (1 - z ^ 2) := by
  have hzc : ‖z ^ 2‖ < 1 := by rw [norm_pow];nlinarith [norm_nonneg z]
  have hc : ∀ k : ℕ, (3 / 2 : ℂ) ≠ -(k : ℂ) := by
    intro k h
    have he := congrArg Complex.re h
    norm_num at he
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  rw [euler_transformation_of_ne_neg_nat hc hzc,
    show (3 / 2 : ℂ) - 1 - 1 = -(1 / 2 : ℂ) by ring,
    show (3 / 2 : ℂ) - 1 = 1 / 2 by ring,arcsinPrincipal_eq_gauss hz,Complex.sqrt,
    cpow_neg]
  norm_num only [one_div]
  ring

/-- The real Gauss numerator is the scaled paired Jacobi numerator. -/
lemma ofReal_gaussNumerator (t : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    (gaussNumerator t k : ℂ) = numerator k * (t : ℂ) / 4 := by
  have hk0 : k ≠ 0 := by omega
  rw [gaussNumerator_def,ite_eq_right hk0,gaussPartialNumerator_eq_paired]
  rw [numerator_def,ite_eq_right hk0,pairedIndex_def]
  have he : k - 1 + 2 = k + 1 := by omega
  rw [he]
  push_cast
  ring

/-- Constant equivalence rescales the arcsine fraction to the reciprocal Gauss fraction. -/
lemma convergent_eq_gauss {x : ℝ} (hx : x ≠ 0) (n : ℕ) :
    convergent n (x : ℂ) = ((2 * (x : ℂ))⁻¹) *
      (((ofFun 0 (gaussNumerator (x⁻¹ ^ 2)) gaussDenominator).convs n : ℝ) : ℂ) := by
  have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx
  let r : ℂ := (2 * (x : ℂ))⁻¹
  have hr : r ≠ 0 := by dsimp [r]; exact inv_ne_zero (mul_ne_zero (by norm_num) hxC)
  have he := ofFun_convs_equiv (h := (0 : ℂ)) (a := numerator) (b := denominator x)
    (fun _ => r) (fun _ => hr) n
  have ha : (fun k => (if k = 0 then r else r * r) * numerator k) =
      (fun k => if k = 0 then r * (gaussNumerator (x⁻¹ ^ 2) 0 : ℂ)
        else (gaussNumerator (x⁻¹ ^ 2) k : ℂ)) := by
    funext k
    by_cases hk : k = 0
    · subst k;simp [numerator_def,gaussNumerator_def]
    · rw [ite_eq_right hk,ite_eq_right hk,ofReal_gaussNumerator _ k (by omega)]
      dsimp [r]
      push_cast
      field_simp
      ring
  have hb : (fun k => r * denominator x k) = fun k => (gaussDenominator k : ℂ) := by
    funext k
    rw [denominator_def,gaussDenominator_def]
    dsimp [r]
    push_cast
    field_simp
    ring
  rw [ha,hb] at he
  rw [ofFun_convs_mul_first_num (a := fun k => (gaussNumerator (x⁻¹ ^ 2) k : ℂ))] at he
  rw [convergent_def,← he]
  congr 1
  exact (ofFun_convs_map (h := (0 : ℝ)) (a := gaussNumerator (x⁻¹ ^ 2))
    (b := gaussDenominator) ofRealHom n)

/-- The reciprocal Gauss minimal solution is a Gauss hypergeometric function. -/
lemma gaussBackward_ratio (t : ℝ) :
    ((GaussContinuedFraction.backwardSolutionReal 1 0 (1 / 2) t 1 /
      GaussContinuedFraction.backwardSolutionReal 1 0 (1 / 2) t 0 : ℝ) : ℂ) =
      2 * ₂F₁ (1 : ℂ) 1 (3 / 2) (t : ℂ) := by
  simp only [ofReal_div,GaussContinuedFraction.backwardSolutionReal]
  norm_num only [Nat.reduceDiv,CharP.cast_eq_zero,Nat.cast_zero,Nat.cast_one,add_zero,zero_add,
    Nat.reduceAdd]
  rw [← GaussContinuedFraction.ofReal,← GaussContinuedFraction.ofReal]
  norm_num only [ofReal_one,ofReal_zero,ofReal_div,ofReal_ofNat,ofReal_add]
  have hhalf : ∀ k : ℕ, (1 / 2 : ℂ) ≠ -(k : ℂ) := by
    intro k h
    have he := congrArg Complex.re h
    norm_num at he
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  rw [regularizedGaussHypergeometricFun_eq_div_Gamma Complex.three_div_two_ne_neg_natCast,
    regularizedGaussHypergeometricFun_eq_div_Gamma hhalf,
    ordinaryHypergeometric_symm 1 0,ordinaryHypergeometric_zero_left]
  have hG : Gamma (3 / 2 : ℂ) = (1 / 2 : ℂ) * Gamma (1 / 2) := by
    convert Gamma_add_one (1 / 2 : ℂ) (by norm_num) using 1; congr 1; norm_num
  rw [hG]
  have hg : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero hhalf
  field_simp

/-- On the positive exterior real axis the arcsine fraction converges to its principal value. -/
lemma tendsto_convergent_ofReal {x : ℝ} (hx : 2 < x) :
    Tendsto (fun n => convergent n (x : ℂ)) atTop (𝓝 (value (x : ℂ))) := by
  have hx0 : x ≠ 0 := by linarith
  have ht : 0 < x⁻¹ ^ 2 := by positivity
  have htx : x⁻¹ < 1 / 2 :=
    (inv_lt_comm₀ (by linarith : 0 < x) (by norm_num)).mpr (by simpa using hx)
  have ht2 : x⁻¹ ^ 2 < 1 / 2 := by nlinarith [inv_pos.mpr (by linarith : 0 < x)]
  have h := (continuous_ofReal.tendsto _).comp (tendsto_gauss_inverse ht ht2)
  rw [gaussBackward_ratio] at h
  have hh := h.const_mul ((2 * (x : ℂ))⁻¹)
  have hval : (2 * (x : ℂ))⁻¹ * (2 * ₂F₁ (1 : ℂ) 1 (3 / 2) ((x⁻¹ ^ 2 : ℝ) : ℂ)) =
      value (x : ℂ) := by
    rw [value_def,← mul_gauss_eq_arcsin_div_sqrt]
    · push_cast
      field_simp
    · rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith : 0 < x)]
      linarith
  rw [hval] at hh
  convert hh using 1
  funext n
  exact convergent_eq_gauss hx0 n

/-- Every finite arcsine convergent is holomorphic off the real unit segment. -/
theorem differentiableOn_convergent (n : ℕ) :
    DifferentiableOn ℂ (convergent n) (realSegmentComplement (-1) 1) := by
  have he : convergent n = fun z => (ofFun 0 numerator (denominator z)).convs n :=
    funext (convergent_def n)
  rw [he]
  apply ofFun_convs_differentiableOn (differentiableOn_const (0 : ℂ))
    (fun k => differentiableOn_const (numerator k)) (fun k => ?_) n
    (fun z hz => (convergent_bound hz n).1)
  simp only [denominator_def]
  exact (differentiableOn_const (2 * (k : ℂ) + 1)).mul differentiableOn_id

/-- The arcsine convergents are locally bounded throughout the exterior segment domain. -/
theorem isLocallyBoundedOn_convergent :
    TauCeti.IsLocallyBoundedOn convergent (realSegmentComplement (-1) 1) := by
  have hβ : ContinuousOn (fun z : ℂ => 1 / max (|z.re| - 1) |z.im|)
      (realSegmentComplement (-1) 1) :=
    continuousOn_const.div
      (((continuous_re.abs.sub continuous_const).max continuous_im.abs).continuousOn)
      (fun z hz => (max_abs_re_sub_one_abs_im_pos hz).ne')
  refine TauCeti.isLocallyBoundedOn_def.mpr fun K hKΩ hK => ?_
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hβ.mono hKΩ)
  exact ⟨C, fun n z hz => (convergent_bound (hKΩ hz) n).2.trans
    ((Real.le_norm_self _).trans (hC z hz))⟩

/-- The Jacobi fraction converges to the arcsine Cauchy transform off `[-1,1]`. -/
theorem tendsto_convergent {z : ℂ} (hz : z ∈ realSegmentComplement (-1) 1) :
    Tendsto (fun n => convergent n z) atTop (𝓝 (value z)) := by
  let Ω := realSegmentComplement (-1) 1
  have hΩ : IsOpen Ω := isOpen_realSegmentComplement _ _
  have hpre : IsPreconnected Ω := isPreconnected_realSegmentComplement _ _
  let A : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Ioi 2
  have hAΩ : A ⊆ Ω := by
    rintro _ ⟨t, ht, rfl⟩
    have ht' : 2 < t := ht
    exact Or.inr (Or.inr (by simp only [ofReal_re]; linarith))
  have htend : Tendsto (fun n : ℕ => (((3 : ℝ) + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop
      (𝓝[≠] (3 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_add (3 : ℝ)
      simp only [add_zero] at h
      simpa [Function.comp_def] using (continuous_ofReal.tendsto 3).comp h
    · simp only [mem_compl_iff, mem_singleton_iff]
      have hn : (3 : ℝ) + 1 / ((n : ℝ) + 1) ≠ 3 := by
        have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      exact_mod_cast hn
  have hmem : ∀ n : ℕ, (((3 : ℝ) + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) ∈ A := by
    intro n
    refine ⟨(3 : ℝ) + 1 / ((n : ℝ) + 1), ?_, rfl⟩
    exact lt_add_of_lt_of_nonneg (by norm_num : (2 : ℝ) < 3) (by positivity)
  have hacc : AccPt (3 : ℂ) (𝓟 A) :=
    accPt_iff_frequently_nhdsNE.mpr (htend.frequently (Frequently.of_forall hmem))
  have htwo : (3 : ℂ) ∈ Ω := Or.inr (Or.inr (by norm_num))
  obtain ⟨g, hg, hgA, hconv⟩ := TauCeti.vitali_of_tendsto hΩ hpre
    differentiableOn_convergent isLocallyBoundedOn_convergent hAΩ htwo hacc
    (g := value) (by
      rintro _ ⟨t, ht, rfl⟩
      exact tendsto_convergent_ofReal ht)
  have hEq : EqOn g value Ω :=
    (hg.analyticOnNhd hΩ).eqOn_of_preconnected_of_frequently_eq
      (differentiableOn_value.analyticOnNhd hΩ) hpre htwo
      (htend.frequently (Frequently.of_forall fun n => hgA (hmem n)))
  rw [← hEq hz]
  exact hconv.tendsto_at hz


/-- Substitution gives the principal arcsine fraction on its two-ray slit. -/
lemma tendsto_arcsin {z : ℂ} (hz0 : z ≠ 0) (hz : z ∈ arcsinCutPlane) :
    Tendsto (ofFun 0
      (fun k => if k = 0 then z else
        -(((2 * ((k + 1) / 2) - 1) * (2 * ((k + 1) / 2)) : ℕ) : ℂ) * z ^ 2)
      (fun k => (2 * k + 1 : ℂ))).convs atTop
      (𝓝 (arcsinPrincipal z / Complex.sqrt (1 - z ^ 2))) := by
  have h := tendsto_convergent (inv_mem_realSegmentComplement hz0 hz)
  have heq (n : ℕ) :
      (ofFun 0 (fun k => if k = 0 then z else
        -(((2 * ((k + 1) / 2) - 1) * (2 * ((k + 1) / 2)) : ℕ) : ℂ) * z ^ 2)
        (fun k => (2 * k + 1 : ℂ))).convs n = convergent n z⁻¹ := by
    have he := ofFun_convs_equiv (h := (0 : ℂ)) (a := numerator) (b := denominator z⁻¹)
      (fun _ => z) (fun _ => hz0) n
    convert he using 2
    · congr 1
      · funext k
        by_cases hk : k = 0
        · subst k;simp [numerator_def]
        · simp only [hk,↓reduceIte,numerator_def,pairedIndex_def]
          ring
      · funext k
        rw [denominator_def]
        field_simp
    · exact convergent_def n z⁻¹
  simpa only [← heq,value_def,inv_inv] using h

/-- The principal arcsine has its paired-numerator continued fraction. -/
lemma hasContinuedFraction_arcsin {z : ℂ} (hz : z ∈ arcsinCutPlane) :
    DLMF.Core.HasContinuedFraction
      (fun k => if k = 0 then z else
        -(((2 * ((k + 1) / 2) - 1) * (2 * ((k + 1) / 2)) : ℕ) : ℂ) * z ^ 2)
      (fun k => (2 * k + 1 : ℂ)) (arcsinPrincipal z / Complex.sqrt (1 - z ^ 2)) := by
  by_cases hz0 : z = 0
  · subst z
    unfold DLMF.Core.HasContinuedFraction
    have he (n : ℕ) : DLMF.Core.continuedFractionTail
        (fun k => if k = 0 then (0 : ℂ) else
          -(((2 * ((k + 1) / 2) - 1) * (2 * ((k + 1) / 2)) : ℕ) : ℂ) * 0 ^ 2)
        (fun k => (2 * k + 1 : ℂ)) 0 n = 0 := by
      cases n with
      | zero => simp [DLMF.Core.continuedFractionTail,
          DLMF.Core.continuedFractionContinuants]
      | succ n =>
        rw [DLMF.Confluent.IncompleteGammaFractions.continuedFractionTail_freeze
          (by norm_num) (by omega)]
        norm_num
    -- The core convergence predicate evaluates these finite tails from index zero.
    change Tendsto (fun n => _) atTop _
    simp_rw [he]
    simp [arcsinPrincipal_zero]
  · rw [DLMF.Confluent.IncompleteGammaFractions.hasContinuedFraction_iff]
    · exact tendsto_arcsin hz0 hz
    · intro k hk
      simp only [show k ≠ 0 by omega,↓reduceIte,mul_ne_zero_iff,neg_ne_zero]
      refine ⟨?_,pow_ne_zero _ hz0⟩
      have hidx : 2 ≤ 2 * ((k + 1) / 2) := by omega
      exact_mod_cast (mul_ne_zero (by omega : 2 * ((k + 1) / 2) - 1 ≠ 0)
        (by omega : 2 * ((k + 1) / 2) ≠ 0))

/-- Scaling the initial numerator scales the principal arcsine quotient. -/
lemma hasContinuedFraction_scaled_arcsin (c : ℂ) {z : ℂ} (hz : z ∈ arcsinCutPlane) :
    DLMF.Core.HasContinuedFraction
      (fun k => if k = 0 then c * z else
        -(((2 * ((k + 1) / 2) - 1) * (2 * ((k + 1) / 2)) : ℕ) : ℂ) * z ^ 2)
      (fun k => (2 * k + 1 : ℂ)) (c * (arcsinPrincipal z / Complex.sqrt (1 - z ^ 2))) := by
  by_cases hz0 : z = 0
  · subst z
    simpa [arcsinPrincipal_zero] using hasContinuedFraction_arcsin hz
  · rw [DLMF.Confluent.IncompleteGammaFractions.hasContinuedFraction_iff]
    · have h := (tendsto_arcsin hz0 hz).const_mul c
      have he (n : ℕ) := ofFun_convs_mul_first_num
        (a := fun k => if k = 0 then z else
          -(((2 * ((k + 1) / 2) - 1) * (2 * ((k + 1) / 2)) : ℕ) : ℂ) * z ^ 2)
        (b := fun k => (2 * k + 1 : ℂ)) c n
      simp only [↓reduceIte] at he
      have heq : (fun k : ℕ => if k = 0 then c * z
          else if k = 0 then z else
            -(((2 * ((k + 1) / 2) - 1) * (2 * ((k + 1) / 2)) : ℕ) : ℂ) * z ^ 2) =
          (fun k : ℕ => if k = 0 then c * z else
            -(((2 * ((k + 1) / 2) - 1) * (2 * ((k + 1) / 2)) : ℕ) : ℂ) * z ^ 2) := by
        funext k
        by_cases hk : k = 0 <;> simp [hk]
      simp only [heq] at he
      simpa only [← he] using h
    · intro k hk
      simp only [show k ≠ 0 by omega,↓reduceIte,mul_ne_zero_iff,neg_ne_zero]
      refine ⟨?_,pow_ne_zero _ hz0⟩
      have hidx : 2 ≤ 2 * ((k + 1) / 2) := by omega
      exact_mod_cast (mul_ne_zero (by omega : 2 * ((k + 1) / 2) - 1 ≠ 0)
        (by omega : 2 * ((k + 1) / 2) ≠ 0))

/-- Rotation gives the principal inverse hyperbolic sine continued fraction. -/
lemma hasContinuedFraction_arcsinh {z : ℂ} (hz : z ∈ arcsinhDomain) :
    DLMF.Core.HasContinuedFraction
      (fun k => if k = 0 then z else
        ((2 * ((k + 1) / 2) - 1 : ℕ) : ℂ) * ((2 * ((k + 1) / 2) : ℕ) : ℂ) * z ^ 2)
      (fun k => (2 * k + 1 : ℂ)) (arcsinh z / Complex.sqrt (1 + z ^ 2)) := by
  have hdom : -I * z ∈ arcsinCutPlane := by
    simpa [arcsinhDomain,arcsinCutPlane,Complex.mul_re,Complex.mul_im] using hz
  have h := hasContinuedFraction_scaled_arcsin I hdom
  have hval : I * (arcsinPrincipal (-I * z) / Complex.sqrt (1 - (-I * z) ^ 2)) =
      arcsinh z / Complex.sqrt (1 + z ^ 2) := by
    rw [Hyperbolic.arcsinh_rotation,mul_div_assoc]
    have he : 1 - (-I * z) ^ 2 = 1 + z ^ 2 := by simp [mul_pow]
    rw [he]
  have hnum : (fun k : ℕ => if k = 0 then I * (-I * z) else
        -(((2 * ((k + 1) / 2) - 1) * (2 * ((k + 1) / 2)) : ℕ) : ℂ) * (-I * z) ^ 2) =
      (fun k => if k = 0 then z else
        ((2 * ((k + 1) / 2) - 1 : ℕ) : ℂ) * ((2 * ((k + 1) / 2) : ℕ) : ℂ) * z ^ 2) := by
    funext k
    by_cases hk : k = 0 <;> simp [hk,mul_pow,← mul_assoc]
  simpa only [hnum,hval] using h

end DLMF.Elementary.ArcsineContinuedFraction
