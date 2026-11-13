/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import DLMFMathlib.Analysis.MellinConvolution
import TauCeti.MeasureTheory.Integral.Exp.Decay
import TauCeti.Analysis.SpecialFunctions.Trigonometric.TanhSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.PSeries

/-!
# Mellin transform of a logarithmic kernel

Logarithmic substitution turns `log |(1+x)/(1-x)|` into an exponentially summable
series on the real line. Its bilateral Laplace transform reduces to the odd-pole
part of the cotangent expansion, supplied by TauCeti's `hasSum_cotTerm_two_mul`.

## Main results

* `Complex.integrable_exp_sub_mul_abs`: integrability of a tilted two-sided exponential.
* `Complex.integral_exp_sub_mul_abs`: its bilateral Laplace integral.
* `mellin_log_abs_one_add_div_one_sub`: the logarithmic Mellin transform.
-/

public noncomputable section

open Complex MeasureTheory Filter Set
open scoped Topology Nat

set_option maxHeartbeats 800000

namespace Complex
/-- A tilted two-sided exponential is bounded by its slowest exponential decay. -/
lemma norm_exp_sub_mul_abs_le {a : ℝ} (s : ℂ) (t : ℝ) :
    ‖exp (-s * t - (a * |t| : ℝ))‖ ≤ Real.exp (-((a - |s.re|) * |t|)) := by
  rw [Complex.norm_exp, Real.exp_le_exp]
  simp only [sub_re, mul_re, neg_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  have h := neg_abs_le (s.re * t)
  rw [abs_mul] at h
  nlinarith

/-- A two-sided exponential with a complex linear tilt is integrable in its convergence strip. -/
lemma integrable_exp_sub_mul_abs {a : ℝ} {s : ℂ} (hs : |s.re| < a) :
    Integrable (fun t : ℝ => exp (-s * t - (a * |t| : ℝ))) := by
  refine (TauCeti.integrable_exp_neg_mul_abs (sub_pos.mpr hs)).mono' (by fun_prop) ?_
  exact Eventually.of_forall fun t => norm_exp_sub_mul_abs_le s t

/-- The bilateral Laplace transform of a two-sided exponential. -/
lemma integral_exp_sub_mul_abs {a : ℝ} {s : ℂ} (hs : |s.re| < a) :
    (∫ t : ℝ, exp (-s * t - (a * |t| : ℝ))) = 1 / (a + s) + 1 / (a - s) := by
  have hint := integrable_exp_sub_mul_abs hs
  have hm : EqOn (fun t : ℝ => exp (-s * t - (a * |t| : ℝ)))
      (fun t : ℝ => exp (((a : ℂ) - s) * t)) (Iic 0) := by
    intro t ht
    dsimp only
    rw [abs_of_nonpos (show t ≤ 0 from ht)]
    congr 1
    push_cast
    ring
  have hp : EqOn (fun t : ℝ => exp (-s * t - (a * |t| : ℝ)))
      (fun t : ℝ => exp ((-(a : ℂ) - s) * t)) (Ioi 0) := by
    intro t ht
    dsimp only
    rw [abs_of_pos (show 0 < t from ht)]
    congr 1
    push_cast
    ring
  have hmre : 0 < ((a : ℂ) - s).re := by simpa using sub_pos.mpr ((le_abs_self s.re).trans_lt hs)
  have hpre : (-(a : ℂ) - s).re < 0 := by
    simp only [sub_re, neg_re, ofReal_re]
    linarith [neg_abs_le s.re]
  rw [← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn,
    setIntegral_congr_fun measurableSet_Iic hm, setIntegral_congr_fun measurableSet_Ioi hp,
    integral_exp_mul_complex_Iic hmre, integral_exp_mul_complex_Ioi hpre]
  norm_num only [ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
  rw [show -(a : ℂ) - s = -((a : ℂ) + s) by ring, neg_div_neg_eq]
  ring
end Complex

namespace MellinLogarithmicKernel

private lemma hasSum_exp_abs {t : ℝ} (ht : t ≠ 0) :
    HasSum (fun n : ℕ => (2 : ℝ) / (2 * n + 1) * Real.exp (-((2 * n + 1) * |t|)))
      (Real.log |(1 + Real.exp (-t)) / (1 - Real.exp (-t))|) := by
  have hr : |Real.exp (-|t|)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    linarith [abs_pos.mpr ht]
  have h := Real.hasSum_log_sub_log_of_abs_lt_one hr
  have harg : Real.log |(1 + Real.exp (-t)) / (1 - Real.exp (-t))| =
      Real.log (1 + Real.exp (-|t|)) - Real.log (1 - Real.exp (-|t|)) := by
    rw [← Real.log_div (by positivity) (by
      have hlt : Real.exp (-|t|) < 1 := (le_abs_self _).trans_lt hr
      linarith)]
    rcases lt_or_gt_of_ne ht with ht | ht
    · rw [abs_of_neg ht]
      have he : Real.exp (-t) = (Real.exp t)⁻¹ := Real.exp_neg t
      rw [he]
      have ht1 : Real.exp t < 1 := Real.exp_lt_one_iff.mpr ht
      have ha : (1 + (Real.exp t)⁻¹) / (1 - (Real.exp t)⁻¹) =
          -((1 + Real.exp t) / (1 - Real.exp t)) := by
        have hu : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
        generalize Real.exp t = u at ht1 hu ⊢
        have hu1 : u - 1 ≠ 0 := by linarith
        have h1u : -1 + u ≠ 0 := by linarith
        field_simp [hu, hu1, h1u]
        ring
      rw [ha, abs_neg, abs_of_pos (by positivity), neg_neg]
    · rw [abs_of_pos ht, abs_of_pos (by
        apply div_pos (by positivity)
        have he : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
        linarith)]
  rw [harg]
  refine h.congr_fun fun n => ?_
  simp only [mul_one_div]
  rw [← Real.exp_nat_mul]
  push_cast
  congr 2
  ring


private lemma integral_series {s : ℂ} (hs : |s.re| < 1) :
    HasSum (fun n : ℕ => (2 : ℂ) / (2 * n + 1) *
      (1 / ((2 * n + 1 : ℝ) + s) + 1 / ((2 * n + 1 : ℝ) - s)))
      (mellin (fun x => (Real.log |(1 + x) / (1 - x)| : ℂ)) s) := by
  let F : ℕ → ℝ → ℂ := fun n t => 2 / (2 * n + 1 : ℂ) *
    exp (-s * t - ((2 * n + 1 : ℝ) * |t| : ℝ))
  have hβ (n : ℕ) : |s.re| < 2 * (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hFi (n : ℕ) : Integrable (F n) :=
    (Complex.integrable_exp_sub_mul_abs (hβ n)).const_mul _
  have hM (n : ℕ) : Integrable (fun t : ℝ =>
      2 / (2 * (n : ℝ) + 1) * Real.exp (-(((2 * n + 1 : ℝ) - |s.re|) * |t|))) :=
    (TauCeti.integrable_exp_neg_mul_abs (sub_pos.mpr (hβ n))).const_mul _
  have hb (n : ℕ) (t : ℝ) : ‖F n t‖ ≤
      2 / (2 * (n : ℝ) + 1) * Real.exp (-(((2 * n + 1 : ℝ) - |s.re|) * |t|)) := by
    dsimp only [F]
    rw [norm_mul, norm_div]
    have hnorm : ‖(2 * n + 1 : ℂ)‖ = 2 * (n : ℝ) + 1 := by
      rw [show (2 * n + 1 : ℂ) = ((2 * (n : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [hnorm, norm_ofNat]
    exact mul_le_mul_of_nonneg_left (Complex.norm_exp_sub_mul_abs_le s t) (by positivity)
  have hnormint (n : ℕ) : (∫ t : ℝ, ‖F n t‖) ≤
      (4 / (1 - |s.re|)) / ((n : ℝ) + 1) ^ 2 := by
    calc
      _ ≤ ∫ t : ℝ, 2 / (2 * (n : ℝ) + 1) *
          Real.exp (-(((2 * n + 1 : ℝ) - |s.re|) * |t|)) :=
        integral_mono (hFi n).norm (hM n) (hb n)
      _ = (2 / (2 * (n : ℝ) + 1)) * (2 / ((2 * n + 1 : ℝ) - |s.re|)) := by
        rw [integral_const_mul, TauCeti.integral_exp_neg_mul_abs (sub_pos.mpr (hβ n))]
      _ ≤ _ := by
        have _hr : 0 < 1 - |s.re| := sub_pos.mpr hs
        have _hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        have _hB : 0 < 2 * (n : ℝ) + 1 := by positivity
        have _hD : 0 < (2 * (n : ℝ) + 1) - |s.re| := sub_pos.mpr (hβ n)
        have he : (1 - |s.re|) * ((n : ℝ) + 1) ^ 2 ≤
            (2 * (n : ℝ) + 1) * ((2 * (n : ℝ) + 1) - |s.re|) := by
          nlinarith [abs_nonneg s.re, sq_nonneg (n : ℝ)]
        calc
          _ = 4 / ((2 * (n : ℝ) + 1) * ((2 * (n : ℝ) + 1) - |s.re|)) := by
            rw [div_mul_div_comm]
            norm_num
          _ ≤ 4 / ((1 - |s.re|) * ((n : ℝ) + 1) ^ 2) :=
            div_le_div_of_nonneg_left (by norm_num) (by positivity) he
          _ = _ := by rw [div_div]
  have hsummable : Summable (fun n : ℕ => ∫ t : ℝ, ‖F n t‖) := by
    have hp := ((summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))).mul_left
        (4 / (1 - |s.re|))
    refine hp.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _) fun n => ?_
    have h := hnormint n
    simpa only [Nat.cast_add, Nat.cast_one, mul_one_div] using h
  have hsum := hasSum_integral_of_summable_integral_norm hFi hsummable
  have hpoint : ∀ᵐ t : ℝ, (∑' n, F n t) =
      exp (-s * t) * (Real.log |(1 + Real.exp (-t)) / (1 - Real.exp (-t))| : ℂ) := by
    have hae : ∀ᵐ t : ℝ, t ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [hae] with t ht
    have h := (Complex.hasSum_ofReal.mpr (hasSum_exp_abs ht)).mul_left (exp (-s * t))
    refine (h.congr_fun fun n => ?_).tsum_eq
    dsimp only [F]
    push_cast
    rw [Complex.exp_sub, Complex.exp_neg]
    ring
  rw [integral_congr_ae hpoint, ← mellin_eq_integral_exp_mul
    (fun x : ℝ => (Real.log |(1 + x) / (1 - x)| : ℂ)) s] at hsum
  refine hsum.congr_fun fun n => ?_
  dsimp only [F]
  rw [integral_const_mul, Complex.integral_exp_sub_mul_abs (hβ n)]


private lemma odd_partial_fraction {s : ℂ} (hs0 : -1 < s.re) (hs1 : s.re < 1) (hs : s ≠ 0) :
    HasSum (fun n : ℕ => (2 : ℂ) / (2 * n + 1) *
      (1 / ((2 * n + 1 : ℝ) + s) + 1 / ((2 * n + 1 : ℝ) - s)))
      (Real.pi * Complex.tan (s * Real.pi / 2) / s) := by
  have hz : s ∈ integerComplement := by
    rintro ⟨k, hk⟩
    have hsk : s = k := hk.symm
    have h0 : (-1 : ℝ) < k := by simpa [hsk] using hs0
    have h1 : (k : ℝ) < 1 := by simpa [hsk] using hs1
    have h0' : -1 < k := by exact_mod_cast h0
    have h1' : k < 1 := by exact_mod_cast h1
    have hk0 : k = 0 := by omega
    simp [hk0] at hk
    exact hs hk.symm
  have hsin := sin_pi_mul_ne_zero hz
  let u : ℂ := Real.pi * s / 2
  have hdouble : 2 * u = Real.pi * s := by dsimp [u]; ring
  have hsu : Complex.sin u ≠ 0 := by
    intro he
    rw [← hdouble, Complex.sin_two_mul, he] at hsin
    simp at hsin
  have hcu : Complex.cos u ≠ 0 := by
    intro he
    rw [← hdouble, Complex.sin_two_mul, he] at hsin
    simp at hsin
  have htrig : Complex.cot u - 2 * Complex.cot (2 * u) = Complex.tan u := by
    rw [Complex.cot_eq_cos_div_sin, Complex.cot_eq_cos_div_sin,
      Complex.tan_eq_sin_div_cos, Complex.sin_two_mul, Complex.cos_two_mul]
    field_simp
    have he := Complex.sin_sq_add_cos_sq u
    linear_combination -he
  have h := (TauCeti.hasSum_cotTerm_two_mul hz).mul_left ((-2 : ℂ) / s)
  have hv : (-2 : ℂ) / s * ((Real.pi : ℂ) * Complex.cot (Real.pi * s) -
      Real.pi / 2 * Complex.cot (Real.pi * (s / 2))) =
      Real.pi * Complex.tan (s * Real.pi / 2) / s := by
    rw [show (Real.pi : ℂ) * (s / 2) = u by dsimp [u]; ring,
      ← hdouble, show s * (Real.pi : ℂ) / 2 = u by dsimp [u]; ring, ← htrig]
    ring
  rw [hv] at h
  refine h.congr_fun fun n => ?_
  rw [cotTerm]
  push_cast
  have hβ : (2 * (n : ℂ) + 1) ≠ 0 := by
    exact_mod_cast (show 2 * n + 1 ≠ (0 : ℕ) by omega)
  have hplus : (2 * (n : ℂ) + 1) + s ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp at hr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hminus : (2 * (n : ℂ) + 1) - s ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp at hr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  generalize (2 * (n : ℂ) + 1) = B at hβ hplus hminus ⊢
  rw [show s - B = -(B - s) by ring, show s + B = B + s by ring]
  field_simp [hβ, hplus, hminus, hs]
  ring

end MellinLogarithmicKernel

/-- The Mellin transform of `log |(1+x)/(1-x)|` on the strip `-1 < re s < 1`. -/
lemma mellin_log_abs_one_add_div_one_sub {s : ℂ} (hs0 : -1 < s.re) (hs1 : s.re < 1)
    (hs : s ≠ 0) :
    mellin (fun x => (Real.log |(1 + x) / (1 - x)| : ℂ)) s =
      Real.pi * Complex.tan (s * Real.pi / 2) / s := by
  exact (MellinLogarithmicKernel.integral_series (abs_lt.mpr ⟨hs0, hs1⟩)).unique
    (MellinLogarithmicKernel.odd_partial_fraction hs0 hs1 hs)

