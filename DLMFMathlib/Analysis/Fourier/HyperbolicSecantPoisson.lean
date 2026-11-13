/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import DLMFMathlib.Analysis.Fourier.HyperbolicSecant
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import TauCeti.Analysis.SpecificLimits.Normed

/-!
# Poisson summation for the hyperbolic secant

The bilateral Laplace integral of the hyperbolic secant gives its Fourier transform at
every positive scale. Quadratic decay at both ends verifies the hypotheses of Mathlib's
Poisson summation theorem, giving the periodization at spacing `2π`.

## Main results

* `Real.inv_cosh_mul_isBigO_abs_rpow`: quadratic decay on the real line.
* `Real.summable_nat_pow_div_cosh_mul`: polynomially weighted sampling is summable.
* `Complex.fourier_inv_cosh_mul`: the Fourier transform with Mathlib's `2π` normalization.
* `Complex.tsum_inv_cosh_add_two_pi_mul`: the periodization formula.
* `Real.tsum_inv_cosh_add_two_pi_mul`: its real cosine form.
* `Real.hasSum_cosh_div_exp_sub_one_periodization`: a Lambert expansion of the tails.
* `Real.inv_cosh_add_lambert_eq_cos_sum`: the resulting local cosine identity.

The Lambert expansion uses TauCeti's `Summable.hasSum_lambert`.
-/

public noncomputable section

open Complex MeasureTheory Filter Set Asymptotics
open scoped Real Topology FourierTransform

namespace Real

/-- The hyperbolic secant has quadratic decay at both ends of the real line. -/
lemma inv_cosh_mul_isBigO_abs_rpow {r : ℝ} (hr : r ≠ 0) :
    (fun x : ℝ => (cosh (r * x))⁻¹) =O[cocompact ℝ] fun x : ℝ => |x| ^ (-2 : ℝ) := by
  refine isBigO_iff.mpr ⟨4 / r ^ 2, ?_⟩
  filter_upwards [tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop (1 : ℝ))]
    with x hx
  have hx' : 1 ≤ |x| := by simpa only [Real.norm_eq_abs] using hx
  have hx0 : x ≠ 0 := by intro h; norm_num [h] at hx'
  have hcosh : (r * x) ^ 2 / 4 ≤ cosh (r * x) := by
    have h := quadratic_le_exp_of_nonneg (abs_nonneg (r * x))
    have he : exp |r * x| ≤ 2 * cosh (r * x) := by
      rw [← cosh_abs (r * x), cosh_eq]
      linarith [exp_pos (-|r * x|)]
    rw [sq_abs] at h
    nlinarith [abs_nonneg (r * x)]
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (cosh_pos _)),
    Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg (abs_nonneg _) _), rpow_neg (abs_nonneg _),
    Real.rpow_two, sq_abs]
  have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx0
  have hc : 0 < cosh (r * x) := cosh_pos _
  calc
    (cosh (r * x))⁻¹ = 1 / cosh (r * x) := by ring_nf
    _ ≤ 4 / (r ^ 2 * x ^ 2) := (div_le_div_iff₀ hc (mul_pos hr2 hx2)).mpr (by nlinarith)
    _ = _ := by ring_nf

/-- Powers times a sampled hyperbolic secant form an absolutely convergent series. -/
lemma summable_nat_pow_div_cosh_mul {r : ℝ} (hr : 0 < r) (k : ℕ) :
    Summable (fun n : ℕ => (n : ℝ) ^ k / cosh (r * n)) := by
  refine ((summable_pow_mul_exp_neg_nat_mul k hr).mul_left 2).of_nonneg_of_le
    (fun n => by positivity) fun n => ?_
  have hden : 1 / cosh (r * n) ≤ 2 * exp (-(r * n)) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), div_mul_eq_mul_div,
      div_le_iff₀ (cosh_pos _), cosh_eq]
    linarith [exp_pos (-(r * n))]
  calc _ = (n : ℝ) ^ k * (1 / cosh (r * n)) := by ring_nf
    _ ≤ (n : ℝ) ^ k * (2 * exp (-(r * n))) :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    _ = _ := by ring_nf

end Real

namespace Complex

/-- Fourier transform of a positively scaled real hyperbolic secant, in Mathlib's
`exp(-2πi xξ)` normalization. -/
lemma fourier_inv_cosh_mul {r : ℝ} (hr : 0 < r) (ξ : ℝ) :
    𝓕 (fun x : ℝ => ((Real.cosh (r * x) : ℝ) : ℂ)⁻¹) ξ =
      ((Real.pi / r : ℝ) : ℂ) / (Real.cosh (Real.pi ^ 2 * ξ / r) : ℝ) := by
  let c : ℂ := ((-2 * Real.pi * ξ : ℝ) : ℂ) * I
  have hc : |c.re| < r := by simpa [c] using hr
  have hv := (integral_exp_div_cosh_mul hr hc).2
  have hcos : cos (Real.pi * c / ((2 * r : ℝ) : ℂ)) =
      (Real.cosh (Real.pi ^ 2 * ξ / r) : ℝ) := by
    rw [show (Real.pi : ℂ) * c / ((2 * r : ℝ) : ℂ) =
        ((-(Real.pi ^ 2 * ξ / r) : ℝ) : ℂ) * I by
      dsimp only [c]; push_cast; field_simp [ofReal_ne_zero.mpr hr.ne'],
      Complex.cos_mul_I, ← ofReal_cosh, Real.cosh_neg]
  rw [hcos] at hv
  rw [Real.fourier_eq']
  calc
    _ = (∫ x : ℝ, exp (c * x) / (Real.cosh (r * x) : ℝ)) := by
      apply integral_congr_ae (Eventually.of_forall fun x => ?_)
      rw [smul_eq_mul]
      have he : ((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * I = c * x := by
        dsimp only [c]
        simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
        push_cast
        ring_nf
      rw [he]
      ring_nf
    _ = _ := by rw [hv]; push_cast; ring_nf

/-- Poisson summation for the hyperbolic secant at period `2π`. -/
lemma tsum_inv_cosh_add_two_pi_mul (x : ℝ) :
    (∑' n : ℤ, ((Real.cosh (x + 2 * Real.pi * n) : ℝ) : ℂ)⁻¹) =
      (1 / 2 : ℂ) * ∑' n : ℤ,
        ((Real.cosh (Real.pi * n / 2) : ℝ) : ℂ)⁻¹ * exp ((n : ℂ) * x * I) := by
  let f : ℝ → ℂ := fun t => ((Real.cosh (2 * Real.pi * t) : ℝ) : ℂ)⁻¹
  have hFT (ξ : ℝ) : 𝓕 f ξ =
      (1 / 2 : ℂ) * ((Real.cosh (Real.pi * ξ / 2) : ℝ) : ℂ)⁻¹ := by
    rw [fourier_inv_cosh_mul (by positivity)]
    rw [show Real.pi ^ 2 * ξ / (2 * Real.pi) = Real.pi * ξ / 2 by
      field_simp]
    push_cast
    field_simp
  have hf : f =O[cocompact ℝ] fun t : ℝ => |t| ^ (-2 : ℝ) := by
    have h := Complex.isBigO_ofReal_left.mpr (Real.inv_cosh_mul_isBigO_abs_rpow
      (r := 2 * Real.pi) (by positivity))
    simpa only [ofReal_inv] using h
  have hF : (𝓕 f) =O[cocompact ℝ] fun t : ℝ => |t| ^ (-2 : ℝ) := by
    have h := (Complex.isBigO_ofReal_left.mpr (Real.inv_cosh_mul_isBigO_abs_rpow
      (r := Real.pi / 2) (by positivity))).const_mul_left (1 / 2 : ℂ)
    simp only [ofReal_inv] at h
    exact h.congr_left fun t => by
      rw [hFT, show Real.pi / 2 * t = Real.pi * t / 2 by ring_nf]
  have hcont : Continuous f :=
    (by fun_prop : Continuous fun t : ℝ => ((Real.cosh (2 * Real.pi * t) : ℝ) : ℂ)).inv₀
      (fun t => ofReal_ne_zero.mpr (Real.cosh_pos _).ne')
  have h := Real.tsum_eq_tsum_fourier_of_rpow_decay
    (f := f) hcont (b := 2) (by norm_num) hf hF (x / (2 * Real.pi))
  simp only [hFT, fourier_coe_apply, ofReal_one, div_one, mul_assoc] at h
  rw [tsum_mul_left] at h
  convert h using 1
  · apply tsum_congr
    intro n
    dsimp only [f]
    rw [show x + 2 * Real.pi * n = 2 * Real.pi * (x / (2 * Real.pi) + n) by
      field_simp]
  · apply congrArg (fun v : ℂ => (1 / 2 : ℂ) * v)
    apply tsum_congr
    intro n
    have he : (n : ℂ) * x * I =
        2 * ((Real.pi : ℂ) * (I * ((n : ℂ) * ((x / (2 * Real.pi) : ℝ) : ℂ)))) := by
      push_cast
      field_simp
    rw [he]

end Complex

namespace Real

/-- The real cosine form of the hyperbolic-secant periodization. -/
lemma tsum_inv_cosh_add_two_pi_mul (x : ℝ) :
    (∑' n : ℤ, (cosh (x + 2 * π * n))⁻¹) =
      1 / 2 + ∑' n : ℕ, cos (((n : ℝ) + 1) * x) / cosh (π * (n + 1) / 2) := by
  let F : ℤ → ℂ := fun n => ((cosh (π * n / 2))⁻¹ : ℝ) *
    Complex.exp ((n : ℂ) * x * I)
  have hW : Summable (fun n : ℤ => (cosh (π * n / 2))⁻¹) := by
    have h := summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
      ((inv_cosh_mul_isBigO_abs_rpow (r := π / 2) (by positivity)).comp_tendsto
        Int.tendsto_coe_cofinite)
    simpa only [Function.comp_def, div_mul_eq_mul_div] using h
  have hF : Summable F := hW.of_norm_bounded fun n => by
    dsimp only [F]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_exp]
    simp only [mul_re, mul_im, intCast_re, intCast_im, ofReal_re, ofReal_im, I_re,
      I_im, mul_zero, zero_mul, sub_zero, mul_one, add_zero, Real.exp_zero, mul_one]
    rw [abs_of_nonneg (by positivity)]
  have hpt (n : ℤ) : (F n).re = cos ((n : ℝ) * x) / cosh (π * n / 2) := by
    have he : (n : ℂ) * x * I = (((n : ℝ) * x : ℝ) : ℂ) * I := by push_cast; rfl
    dsimp only [F]
    rw [he, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    ring
  have hC : Summable (fun n : ℤ => cos ((n : ℝ) * x) / cosh (π * n / 2)) := by
    exact (Complex.reCLM.summable hF).congr fun n => hpt n
  have h := Complex.tsum_inv_cosh_add_two_pi_mul x
  simp_rw [← Complex.ofReal_inv] at h
  rw [← Complex.ofReal_tsum] at h
  have hr : (∑' n : ℤ, (cosh (x + 2 * π * n))⁻¹) =
      (1 / 2 : ℝ) * (∑' n, F n).re := by
    have hr := congrArg Complex.re h
    simpa only [Complex.mul_re, Complex.div_ofNat_re, Complex.one_re, Complex.div_ofNat_im,
      Complex.one_im, zero_div, zero_mul, sub_zero, Complex.ofReal_re] using hr
  rw [Complex.re_tsum hF] at hr
  simp_rw [hpt] at hr
  have heven : Function.Even (fun n : ℤ => cos ((n : ℝ) * x) / cosh (π * n / 2)) := by
    intro n
    push_cast
    rw [neg_mul, mul_neg, neg_div, cos_neg, cosh_neg]
  have hs := tsum_int_eq_zero_add_two_mul_tsum_pnat heven hC
  have hp : (∑' n : ℕ+, cos ((n : ℝ) * x) / cosh (π * n / 2)) =
      ∑' n : ℕ, cos (((n : ℝ) + 1) * x) / cosh (π * (n + 1) / 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      tsum_pnat_eq_tsum_succ (f := fun n : ℕ => cos ((n : ℝ) * x) / cosh (π * n / 2))
  rw [hs] at hr
  push_cast at hr
  rw [hp] at hr
  norm_num at hr
  linarith

end Real

namespace Real

set_option maxHeartbeats 800000 in
/-- A Lambert-series expansion of a one-sided hyperbolic-secant periodization. -/
lemma hasSum_exp_div_exp_sub_one_eq_cosh_sum {a x : ℝ} (ha : 0 < a) (hax : 0 < a + x) :
    HasSum (fun j : ℕ => (-1) ^ j * exp (-((2 * (j : ℝ) + 1) * x)) /
      (exp (a * (2 * j + 1)) - 1))
      (∑' n : ℕ, 1 / (2 * cosh (a * (n + 1) + x))) := by
  let C : ℕ → ℝ := fun k => if Even k then (-1) ^ (k / 2) else 0
  let f : ℝ → ℝ := fun z => z / (1 + z ^ 2)
  let q : ℝ := exp (-a)
  let w : ℝ := exp (-x)
  have hC (j : ℕ) : C (2 * j) = (-1) ^ j := by
    simp [C]
  have hinj : Function.Injective (fun j : ℕ => 2 * j) := by
    intro i j he
    dsimp only at he
    omega
  have hout (k : ℕ) (hk : k ∉ Set.range (fun j : ℕ => 2 * j)) : C k = 0 := by
    have hnot : ¬Even k := by
      rintro ⟨j, hj⟩
      exact hk ⟨j, by dsimp only; omega⟩
    simp only [C, ite_eq_right hnot]
  have hf (z : ℝ) (hz : ‖z‖ < 1) : HasSum (fun k : ℕ => C k * z ^ (k + 1)) (f z) := by
    have hzz : ‖-z ^ 2‖ < 1 := by rw [norm_neg, norm_pow]; nlinarith [norm_nonneg z]
    have hs := (hasSum_geometric_of_norm_lt_one hzz).mul_left z
    have hs' : HasSum (fun j : ℕ => (-1) ^ j * z ^ (2 * j + 1)) (f z) := by
      convert hs using 1
      · funext j
        conv_rhs => rw [neg_pow]
        rw [pow_succ, pow_mul]
        ring
      · dsimp only [f]
        rw [sub_neg_eq_add]
        ring
    refine (hinj.hasSum_iff fun k hk => by rw [hout k hk, zero_mul]).mp ?_
    simpa only [Function.comp_def, hC] using hs'
  have hq : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos (by positivity)]; dsimp [q]; simp [ha]
  have hqw : ‖q * w‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    dsimp only [q, w]
    rw [← exp_add, exp_lt_one_iff]
    linarith
  have hcoef : ∀ k : ℕ, ‖C k‖ ≤ 1 := by
    intro k
    dsimp only [C]
    split_ifs <;> simp
  have hc : Summable (fun k : ℕ => ‖C k‖ * ‖q * w‖ ^ k) := by
    refine (summable_geometric_of_lt_one (norm_nonneg _) hqw).of_nonneg_of_le
      (fun k => by positivity) fun k => ?_
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (hcoef k) (by positivity : 0 ≤ ‖q * w‖ ^ k)
  have hs := hc.hasSum_lambert hf hq hqw
  have hs' : HasSum (fun j : ℕ => C (2 * j) * q ^ (2 * j + 1) /
      (1 - q ^ (2 * j + 1)) * w ^ (2 * j + 1)) (∑' n : ℕ, f (q ^ (n + 1) * w)) :=
    (hinj.hasSum_iff fun k hk => by rw [hout k hk]; simp).mpr hs
  have hpow (u : ℝ) (n : ℕ) : exp (-u) ^ n = exp (-(u * n)) := by
    rw [← exp_nat_mul]
    congr 1
    ring
  have hrow (n : ℕ) : f (q ^ (n + 1) * w) = 1 / (2 * cosh (a * (n + 1) + x)) := by
    dsimp only [f, q, w]
    rw [hpow, ← exp_add]
    have he : -(a * ((n + 1 : ℕ) : ℝ)) + -x = -(a * (n + 1) + x) := by push_cast; ring
    rw [he, cosh_eq, exp_neg]
    field_simp
  simp_rw [hrow] at hs'
  refine hs'.congr_fun fun j => ?_
  rw [hC]
  dsimp only [q, w]
  rw [hpow, hpow]
  push_cast
  have hden : exp (a * (2 * (j : ℝ) + 1)) - 1 ≠ 0 := by
    apply ne_of_gt
    rw [sub_pos, one_lt_exp_iff]
    positivity
  have hratio : exp (-(a * (2 * (j : ℝ) + 1))) /
      (1 - exp (-(a * (2 * (j : ℝ) + 1)))) =
      1 / (exp (a * (2 * (j : ℝ) + 1)) - 1) := by
    rw [exp_neg]
    field_simp
  simp_rw [mul_div_assoc]
  rw [hratio,
    show -(x * (2 * (j : ℝ) + 1)) = -((2 * (j : ℝ) + 1) * x) by ring]
  ring

/-- A one-sided arithmetic sampling of the hyperbolic secant is summable. -/
lemma summable_inv_cosh_nat_mul_add {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Summable (fun n : ℕ => (cosh (a * (n + 1) + x))⁻¹) := by
  have hbound (y : ℝ) : (cosh y)⁻¹ ≤ 2 * exp (-y) := by
    rw [← one_div, exp_neg, ← div_eq_mul_inv]
    apply (div_le_div_iff₀ (cosh_pos _) (exp_pos _)).mpr
    rw [cosh_eq]
    linarith [exp_pos (-y)]
  have hs := (summable_exp_nat_mul_iff.mpr (by linarith : -a < 0)).mul_left
    (2 * exp (-(a + x)))
  refine hs.of_norm_bounded fun n => ?_
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (cosh_pos _))]
  calc _ ≤ 2 * exp (-(a * (n + 1) + x)) := hbound _
    _ = _ := by rw [mul_assoc, ← exp_add]; congr 2; ring

/-- Splitting the periodized hyperbolic secant into its central term and positive tails. -/
lemma tsum_inv_cosh_add_int_mul {a : ℝ} (ha : 0 < a) (x : ℝ) :
    (∑' n : ℤ, (cosh (x + a * n))⁻¹) = (cosh x)⁻¹ +
      (∑' n : ℕ, (cosh (a * (n + 1) + x))⁻¹) +
        ∑' n : ℕ, (cosh (a * (n + 1) - x))⁻¹ := by
  let F : ℤ → ℝ := fun n => (cosh (a * n + x))⁻¹
  have hNat : Summable (fun n : ℕ => F n) := by
    refine (summable_nat_add_iff 1).mp ?_
    refine (summable_inv_cosh_nat_mul_add ha x).congr fun n => ?_
    dsimp only [F]
    push_cast
    rw [add_comm]
  have hpoint (n : ℕ) : F (-(n + 1)) = (cosh (a * (n + 1) - x))⁻¹ := by
    dsimp only [F]
    push_cast
    rw [show a * (-((n : ℝ) + 1)) + x = -(a * (n + 1) - x) by ring, cosh_neg]
  have hNeg : Summable (fun n : ℕ => F (-(n + 1))) := by
    simp_rw [hpoint]
    simpa only [sub_eq_add_neg] using summable_inv_cosh_nat_mul_add ha (-x)
  have hs := tsum_of_nat_of_neg_add_one hNat hNeg
  rw [hNat.tsum_eq_zero_add] at hs
  simp_rw [hpoint] at hs
  dsimp only [F] at hs
  push_cast at hs
  have hs' : (∑' n : ℤ, (cosh (a * n + x))⁻¹) = (cosh x)⁻¹ +
      (∑' n : ℕ, (cosh (a * (n + 1) + x))⁻¹) +
        ∑' n : ℕ, (cosh (a * (n + 1) - x))⁻¹ := by
    simpa only [mul_zero, zero_add] using hs
  calc
    _ = ∑' n : ℤ, (cosh (a * n + x))⁻¹ := by
      apply tsum_congr
      intro n
      rw [add_comm]
    _ = _ := hs' 

/-- The noncentral part of a hyperbolic-secant periodization has a Lambert cosine-hyperbolic
expansion. -/
lemma hasSum_cosh_div_exp_sub_one_periodization {a x : ℝ} (ha : 0 < a) (hx : |x| < a) :
    HasSum (fun j : ℕ => 4 * (-1) ^ j * cosh ((2 * (j : ℝ) + 1) * x) /
      (exp (a * (2 * j + 1)) - 1))
      ((∑' n : ℤ, (cosh (x + a * n))⁻¹) - (cosh x)⁻¹) := by
  have hp := hasSum_exp_div_exp_sub_one_eq_cosh_sum ha
    (show 0 < a + x by linarith [neg_abs_le x])
  have hm := hasSum_exp_div_exp_sub_one_eq_cosh_sum ha
    (show 0 < a + -x by linarith [le_abs_self x])
  have h := (hp.add hm).mul_left 2
  have hhalf (y : ℝ) : (∑' n : ℕ, 1 / (2 * cosh (a * (n + 1) + y))) =
      (1 / 2) * ∑' n : ℕ, (cosh (a * (n + 1) + y))⁻¹ := by
    simp_rw [one_div, mul_inv]
    rw [tsum_mul_left]
  rw [hhalf x, hhalf (-x)] at h
  have hvalue : 2 * ((1 / 2) * (∑' n : ℕ, (cosh (a * (n + 1) + x))⁻¹) +
      (1 / 2) * ∑' n : ℕ, (cosh (a * (n + 1) - x))⁻¹) =
      (∑' n : ℤ, (cosh (x + a * n))⁻¹) - (cosh x)⁻¹ := by
    rw [tsum_inv_cosh_add_int_mul ha x]
    ring
  simp only [sub_eq_add_neg] at hvalue
  rw [hvalue] at h
  refine h.congr_fun fun j => ?_
  rw [cosh_eq]
  simp only [mul_neg, neg_neg]
  ring

/-- Combining the Poisson and Lambert expansions gives the local cosine identity for the
hyperbolic secant. -/
lemma inv_cosh_add_lambert_eq_cos_sum {z : ℝ} (hz : |z| < 1 / 4) :
    (cosh z)⁻¹ + 4 * (∑' j : ℕ, ((-1) ^ j /
      (exp (2 * π * (2 * j + 1)) - 1)) * cosh ((2 * j + 1) * z)) =
      1 / 2 + ∑' k : ℕ, (1 / cosh (π * (k + 1) / 2)) * cos (((k : ℝ) + 1) * z) := by
  have h := Real.hasSum_cosh_div_exp_sub_one_periodization
    (show 0 < 2 * π by positivity) (show |z| < 2 * π by linarith [pi_gt_three])
  have hp := Real.tsum_inv_cosh_add_two_pi_mul z
  have hs : (∑' j : ℕ, 4 * (-1) ^ j * cosh ((2 * j + 1) * z) /
      (exp (2 * π * (2 * j + 1)) - 1)) =
      4 * (∑' j : ℕ, ((-1) ^ j / (exp (2 * π * (2 * j + 1)) - 1)) *
        cosh ((2 * j + 1) * z)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    ring
  have hsum := h.tsum_eq
  rw [hs] at hsum
  rw [hp] at hsum
  have he : (∑' k : ℕ, cos (((k : ℝ) + 1) * z) / cosh (π * (k + 1) / 2)) =
      ∑' k : ℕ, (1 / cosh (π * (k + 1) / 2)) * cos (((k : ℝ) + 1) * z) := by
    apply tsum_congr
    intro k
    ring
  rw [he] at hsum
  linarith

end Real
