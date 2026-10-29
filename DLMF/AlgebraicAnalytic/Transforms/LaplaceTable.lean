/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Transforms.Laplace
public import DLMFMathlib.Analysis.Asymptotics.WatsonSector
public import DLMFMathlib.Analysis.SpecialFunctions.Gamma.Values
public import DLMFMathlib.Analysis.SpecialFunctions.ImproperIntegralsExtra
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import DLMFMathlib.Analysis.Integral.Frullani
public import TauCeti.Analysis.Complex.SlitPlane

/-!
# Elementary Laplace transforms (DLMF Table 1.14.4)

The polynomial, exponential, trigonometric and hyperbolic transform entries are evaluated
from complex exponential moments. The moments use the project’s complex Gamma integral
`integral_cpow_mul_cexp_neg_mul_Ioi` and Mathlib’s factorial values of `Complex.Gamma`.
The inverse-square-root entry uses `Complex.Gamma_one_half_eq_sqrt`.

Complex parameters and principal branches are retained. In rows 15–17 the convergence
conditions are corrected for complex parameters; see the module documentation of
`DLMF.AlgebraicAnalytic.Transforms.Tables` for the details. The logarithmic entries and
`sin(at)/t` follow from the complex exponential Frullani integral in
`DLMFMathlib.Analysis.Integral.Frullani`; branch-cut avoidance uses TauCeti
`div_mem_slitPlane_of_re_pos`.
-/

@[expose] public noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped Nat

namespace DLMF.AlgebraicAnalytic

/-- Integrability and evaluation of the complex exponential moment on the positive half-line. -/
private lemma exponential_moment {c : ℂ} (hc : 0 < c.re) (n : ℕ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ n * cexp (-(c * t))) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, (t : ℂ) ^ n * cexp (-(c * t))) = (n ! : ℂ) / c ^ (n + 1) := by
  have hn : 0 < ((n : ℂ) + 1).re := by simp; positivity
  have hi := Complex.integrableOn_cpow_mul_exp_neg_mul (b := (n : ℂ) + 1) hn hc
  have he := integral_cpow_mul_cexp_neg_mul_Ioi (s := (n : ℂ) + 1) hn hc
  simp only [add_sub_cancel_right, cpow_natCast] at hi he
  refine ⟨hi, ?_⟩
  rw [he, Complex.Gamma_nat_eq_factorial]
  rw [show -((n : ℂ) + 1) = -((n + 1 : ℕ) : ℂ) by push_cast; ring,
    cpow_neg, cpow_natCast, div_eq_mul_inv]

/-- Evaluate the Laplace transform of a polynomial times two exponentials. -/
private lemma laplace_exponential_combination (n : ℕ) {p q s : ℂ}
    (hp : 0 < (s - p).re) (hq : 0 < (s - q).re) (A B : ℂ) :
    laplaceTransform (fun t => (t : ℂ) ^ n * (A * cexp (p * t) + B * cexp (q * t))) s =
      A * (n ! : ℂ) / (s - p) ^ (n + 1) + B * (n ! : ℂ) / (s - q) ^ (n + 1) := by
  have he : (fun t : ℝ => cexp (-s * t) *
      ((t : ℂ) ^ n * (A * cexp (p * t) + B * cexp (q * t)))) =
      fun t : ℝ => A * ((t : ℂ) ^ n * cexp (-((s - p) * t))) +
        B * ((t : ℂ) ^ n * cexp (-((s - q) * t))) := by
    funext t
    rw [show -((s - p) * (t : ℂ)) = -s * t + p * t by ring,
      show -((s - q) * (t : ℂ)) = -s * t + q * t by ring,
      Complex.exp_add, Complex.exp_add]
    ring
  rw [laplaceTransform, he,
    integral_add ((exponential_moment hp n).1.const_mul A)
      ((exponential_moment hq n).1.const_mul B),
    integral_const_mul, integral_const_mul,
    (exponential_moment hp n).2, (exponential_moment hq n).2]
  ring

/-! ### Table 1.14.4: Laplace transforms `∫₀^∞ e^{-st} f(t) dt` -/

/-- DLMF Table 1.14.4, row 5: `e^{-at} ↦ 1/(s + a)`, `ℜ(s + a) > 0`. -/
@[dlmf 1.14.T4]
theorem laplaceTransform_exp_neg {a s : ℂ} (hs : 0 < (s + a).re) :
    laplaceTransform (fun t => cexp (-a * t)) s = 1 / (s + a) := by
  unfold laplaceTransform
  have h : (-(s + a)).re < 0 := by simp at hs ⊢; linarith
  have hne : s + a ≠ 0 := by
    intro h0; rw [h0] at hs; simp at hs
  calc (∫ t in Ioi (0 : ℝ), cexp (-s * t) * cexp (-a * t))
      = ∫ t in Ioi (0 : ℝ), cexp (-(s + a) * t) := by
        congr 1; funext t; rw [← Complex.exp_add]; congr 1; ring
    _ = 1 / (s + a) := by
        rw [integral_exp_mul_complex_Ioi h 0]
        simp only [ofReal_zero, mul_zero, Complex.exp_zero]
        field_simp

/-- DLMF Table 1.14.4, row 2: `1 ↦ 1/s`, `ℜs > 0`. -/
@[dlmf 1.14.T4]
theorem laplaceTransform_one {s : ℂ} (hs : 0 < s.re) :
    laplaceTransform (fun _ => 1) s = 1 / s := by
  have h := laplaceTransform_exp_neg (a := 0) (s := s) (by simpa using hs)
  simpa using h

/-- DLMF Table 1.14.4, row 3: `tⁿ/n! ↦ 1/s^{n+1}`, `ℜs > 0`. -/
@[dlmf 1.14.T4]
theorem laplaceTransform_pow_div_factorial (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    laplaceTransform (fun t => (t : ℂ) ^ n / n !) s = 1 / s ^ (n + 1) := by
  unfold laplaceTransform
  have he : (fun t : ℝ => cexp (-s * t) * ((t : ℂ) ^ n / n !)) =
      fun t : ℝ => ((t : ℂ) ^ n * cexp (-(s * t))) / n ! := by funext t; rw [neg_mul]; ring
  rw [he, integral_div, (exponential_moment hs n).2]
  have hn : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

/-- DLMF Table 1.14.4, row 4: `1/√(πt) ↦ 1/√s`, `ℜs > 0`, principal square root. -/
@[dlmf 1.14.T4]
theorem laplaceTransform_inv_sqrt {s : ℂ} (hs : 0 < s.re) :
    laplaceTransform (fun t => ((Real.sqrt (Real.pi * t))⁻¹ : ℂ)) s = s ^ (-(1 / 2 : ℂ)) := by
  have h := integral_cpow_mul_cexp_neg_mul_Ioi (s := (1 / 2 : ℂ)) (by norm_num) hs
  have he : laplaceTransform (fun t => ((Real.sqrt (Real.pi * t))⁻¹ : ℂ)) s =
      (Real.sqrt Real.pi : ℂ)⁻¹ *
        ∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((1 / 2 : ℂ) - 1) * cexp (-(s * t)) := by
    rw [← integral_const_mul]
    unfold laplaceTransform
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have hp : (t : ℂ) ^ ((1 / 2 : ℂ) - 1) = (Real.sqrt t : ℂ)⁻¹ := by
      rw [show (1 / 2 : ℂ) - 1 = -(1 / 2 : ℂ) by norm_num, cpow_neg]
      congr 1
      rw [Real.sqrt_eq_rpow, ofReal_cpow ht.le]
      norm_num
    dsimp only
    rw [hp, Real.sqrt_mul Real.pi_pos.le, ofReal_mul, mul_inv, neg_mul]
    ring
  rw [he, h, Complex.Gamma_one_half_eq_sqrt, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'

/-- DLMF Table 1.14.4, row 6: `tⁿ e^{-at}/n! ↦ 1/(s + a)^{n+1}`, `ℜ(s + a) > 0`. Proved from
row 3 and the translation rule 1.14.21. -/
@[dlmf 1.14.T4]
theorem laplaceTransform_pow_mul_exp_neg_div_factorial (n : ℕ) {a s : ℂ}
    (hs : 0 < (s + a).re) :
    laplaceTransform (fun t => (t : ℂ) ^ n * cexp (-a * t) / n !) s = 1 / (s + a) ^ (n + 1) := by
  have h := laplaceTransform_sub (fun t => (t : ℂ) ^ n / n !) s (-a)
  rw [sub_neg_eq_add, laplaceTransform_pow_div_factorial n (by simpa using hs)] at h
  rw [h]
  congr 1
  funext t
  ring

/-- DLMF Table 1.14.4, row 7: `(e^{-at} - e^{-bt})/(b - a) ↦ 1/((s + a)(s + b))`, `a ≠ b`,
`ℜs > -ℜa`, `ℜs > -ℜb`. Proved from row 5. -/
@[dlmf 1.14.T4]
theorem laplaceTransform_exp_neg_sub_exp_neg {a b s : ℂ} (hab : a ≠ b) (ha : -a.re < s.re)
    (hb : -b.re < s.re) :
    laplaceTransform (fun t => (cexp (-a * t) - cexp (-b * t)) / (b - a)) s =
      1 / ((s + a) * (s + b)) := by
  have ha' : 0 < (s + a).re := by simp; linarith
  have hb' : 0 < (s + b).re := by simp; linarith
  have hia : IntegrableOn (fun t : ℝ => cexp (-s * t) * cexp (-a * t)) (Ioi 0) := by
    have : IntegrableOn (fun t : ℝ => cexp (-(s + a) * t)) (Ioi 0) :=
      integrableOn_exp_mul_complex_Ioi (by simp at ha' ⊢; linarith) 0
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only; rw [← Complex.exp_add]; congr 1; ring
  have hib : IntegrableOn (fun t : ℝ => cexp (-s * t) * cexp (-b * t)) (Ioi 0) := by
    have : IntegrableOn (fun t : ℝ => cexp (-(s + b) * t)) (Ioi 0) :=
      integrableOn_exp_mul_complex_Ioi (by simp at hb' ⊢; linarith) 0
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only; rw [← Complex.exp_add]; congr 1; ring
  have ea := laplaceTransform_exp_neg ha'
  have eb := laplaceTransform_exp_neg hb'
  unfold laplaceTransform at *
  have : (fun t : ℝ => cexp (-s * t) * ((cexp (-a * t) - cexp (-b * t)) / (b - a))) =
      fun t : ℝ => (cexp (-s * t) * cexp (-a * t) - cexp (-s * t) * cexp (-b * t)) / (b - a) := by
    funext t; ring
  rw [this, integral_div, integral_sub hia hib, ea, eb]
  have h1 : s + a ≠ 0 := fun h => by rw [h] at ha'; simp at ha'
  have h2 : s + b ≠ 0 := fun h => by rw [h] at hb'; simp at hb'
  have h3 : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  field_simp
  ring

/-- DLMF Table 1.14.4, row 8: `sin(at) ↦ a/(s² + a²)`, `ℜs > |ℑa|`. -/
@[dlmf 1.14.T4]
theorem laplaceTransform_sin {a s : ℂ} (hs : |a.im| < s.re) :
    laplaceTransform (fun t => Complex.sin (a * t)) s = a / (s ^ 2 + a ^ 2) := by
  have hp : 0 < (s - (-(a * I))).re := by
    simp only [sub_re, neg_re, mul_I_re]
    linarith [le_abs_self a.im, neg_le_abs a.im]
  have hq : 0 < (s - (a * I)).re := by
    simp only [sub_re, mul_I_re]
    linarith [le_abs_self a.im, neg_le_abs a.im]
  have hp0 : s - (-(a * I)) ≠ 0 := fun h => by simp [h] at hp
  have hq0 : s - (a * I) ≠ 0 := fun h => by simp [h] at hq
  have hd : s ^ 2 + a ^ 2 ≠ 0 := by
    have he : (s - (-(a * I))) * (s - (a * I)) = s ^ 2 + a ^ 2 := by
      ring_nf
      simp [I_sq]
    rw [← he]; exact mul_ne_zero hp0 hq0
  calc laplaceTransform (fun t => Complex.sin (a * t)) s
      = laplaceTransform (fun t => (t : ℂ) ^ 0 *
          ((I / 2) * cexp ((-(a * I)) * t) + (-I / 2) * cexp ((a * I) * t))) s := by
        congr 1; funext t
        simp only [Complex.sin, pow_zero, one_mul]
        rw [show -(a * (t : ℂ)) * I = -(a * I) * t by ring,
          show (a * (t : ℂ)) * I = (a * I) * t by ring]
        ring
    _ = (I / 2) * (0 ! : ℂ) / (s - (-(a * I))) ^ (0 + 1) +
        (-I / 2) * (0 ! : ℂ) / (s - (a * I)) ^ (0 + 1) :=
      laplace_exponential_combination 0 hp hq _ _
    _ = a / (s ^ 2 + a ^ 2) := by
      simp only [Nat.factorial_zero, Nat.cast_one, mul_one,
        Nat.reduceAdd, sub_neg_eq_add, pow_one]
      have hu : s + a * I ≠ 0 := by simpa only [sub_neg_eq_add] using hp0
      have hv : s - a * I ≠ 0 := hq0
      have hrat (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0) (k : ℕ) :
          (I / 2) / u ^ k + (-I / 2) / v ^ k =
            I * (v ^ k - u ^ k) / (2 * (u * v) ^ k) := by
        rw [mul_pow]
        field_simp
        ring
      have hprod : (s + a * I) * (s - a * I) = s ^ 2 + a ^ 2 := by
        ring_nf; simp [I_sq]
      have hdiff : (s - a * I) ^ 1 - (s + a * I) ^ 1 = -2 * a * 1 * I := by ring
      rw [← pow_one (s + a * I), ← pow_one (s - a * I)]
      rw [hrat _ _ hu hv 1, hdiff, hprod]
      have hnum : I * (-2 * a * 1 * I) = 2 * a * 1 := by
        calc I * (-2 * a * 1 * I) = -2 * a * 1 * (I * I) := by ring
             _ = _ := by rw [I_mul_I]; ring
      rw [hnum]
      field_simp

/-- DLMF Table 1.14.4, row 9: `cos(at) ↦ s/(s² + a²)`, `ℜs > |ℑa|`. -/
@[dlmf 1.14.T4]
theorem laplaceTransform_cos {a s : ℂ} (hs : |a.im| < s.re) :
    laplaceTransform (fun t => Complex.cos (a * t)) s = s / (s ^ 2 + a ^ 2) := by
  have hp : 0 < (s - ((a * I))).re := by
    simp only [sub_re, mul_I_re]
    linarith [le_abs_self a.im, neg_le_abs a.im]
  have hq : 0 < (s - (-(a * I))).re := by
    simp only [sub_re, neg_re, mul_I_re]
    linarith [le_abs_self a.im, neg_le_abs a.im]
  have hp0 : s - ((a * I)) ≠ 0 := fun h => by simp [h] at hp
  have hq0 : s - (-(a * I)) ≠ 0 := fun h => by simp [h] at hq
  have hd : s ^ 2 + a ^ 2 ≠ 0 := by
    have he : (s - ((a * I))) * (s - (-(a * I))) = s ^ 2 + a ^ 2 := by
      ring_nf
      simp [I_sq]
    rw [← he]; exact mul_ne_zero hp0 hq0
  calc laplaceTransform (fun t => Complex.cos (a * t)) s
      = laplaceTransform (fun t => (t : ℂ) ^ 0 *
          (((1 / 2 : ℂ)) * cexp (((a * I)) * t) + ((1 / 2 : ℂ)) * cexp ((-(a * I)) * t))) s := by
        congr 1; funext t
        simp only [Complex.cos, pow_zero, one_mul]
        rw [show -(a * (t : ℂ)) * I = -(a * I) * t by ring,
          show (a * (t : ℂ)) * I = (a * I) * t by ring]
        ring
    _ = ((1 / 2 : ℂ)) * (0 ! : ℂ) / (s - ((a * I))) ^ (0 + 1) +
        ((1 / 2 : ℂ)) * (0 ! : ℂ) / (s - (-(a * I))) ^ (0 + 1) :=
      laplace_exponential_combination 0 hp hq _ _
    _ = s / (s ^ 2 + a ^ 2) := by
      norm_num only [Nat.factorial_zero, Nat.factorial_one, Nat.reduceAdd, pow_one]
      simp only [sub_neg_eq_add] at hp0 hq0 ⊢
      field_simp [hp0, hq0, hd]
      ring_nf
      norm_num [I_sq, pow_succ]

/-- DLMF Table 1.14.4, row 10: `sinh(at) ↦ a/(s² - a²)`, `ℜs > |ℜa|`. -/
@[dlmf 1.14.T4]
theorem laplaceTransform_sinh {a s : ℂ} (hs : |a.re| < s.re) :
    laplaceTransform (fun t => Complex.sinh (a * t)) s = a / (s ^ 2 - a ^ 2) := by
  have hp : 0 < (s - (a)).re := by
    simp only [sub_re]
    linarith [le_abs_self a.re, neg_le_abs a.re]
  have hq : 0 < (s - (-a)).re := by
    simp only [sub_re, neg_re]
    linarith [le_abs_self a.re, neg_le_abs a.re]
  have hp0 : s - (a) ≠ 0 := fun h => by simp [h] at hp
  have hq0 : s - (-a) ≠ 0 := fun h => by simp [h] at hq
  have hd : s ^ 2 - a ^ 2 ≠ 0 := by
    have he : (s - (a)) * (s - (-a)) = s ^ 2 - a ^ 2 := by
      ring_nf
    rw [← he]; exact mul_ne_zero hp0 hq0
  calc laplaceTransform (fun t => Complex.sinh (a * t)) s
      = laplaceTransform (fun t => (t : ℂ) ^ 0 *
          (((1 / 2 : ℂ)) * cexp ((a) * t) + ((-1 / 2 : ℂ)) * cexp ((-a) * t))) s := by
        congr 1; funext t
        simp only [Complex.sinh, pow_zero, one_mul]
        rw [neg_mul]
        ring
    _ = ((1 / 2 : ℂ)) * (0 ! : ℂ) / (s - (a)) ^ (0 + 1) +
        ((-1 / 2 : ℂ)) * (0 ! : ℂ) / (s - (-a)) ^ (0 + 1) :=
      laplace_exponential_combination 0 hp hq _ _
    _ = a / (s ^ 2 - a ^ 2) := by
      norm_num only [Nat.factorial_zero, Nat.factorial_one, Nat.reduceAdd, pow_one]
      simp only [sub_neg_eq_add] at hp0 hq0 ⊢
      field_simp [hp0, hq0, hd]
      ring_nf

/-- DLMF Table 1.14.4, row 11: `cosh(at) ↦ s/(s² - a²)`, `ℜs > |ℜa|`. -/
@[dlmf 1.14.T4]
theorem laplaceTransform_cosh {a s : ℂ} (hs : |a.re| < s.re) :
    laplaceTransform (fun t => Complex.cosh (a * t)) s = s / (s ^ 2 - a ^ 2) := by
  have hp : 0 < (s - (a)).re := by
    simp only [sub_re]
    linarith [le_abs_self a.re, neg_le_abs a.re]
  have hq : 0 < (s - (-a)).re := by
    simp only [sub_re, neg_re]
    linarith [le_abs_self a.re, neg_le_abs a.re]
  have hp0 : s - (a) ≠ 0 := fun h => by simp [h] at hp
  have hq0 : s - (-a) ≠ 0 := fun h => by simp [h] at hq
  have hd : s ^ 2 - a ^ 2 ≠ 0 := by
    have he : (s - (a)) * (s - (-a)) = s ^ 2 - a ^ 2 := by
      ring_nf
    rw [← he]; exact mul_ne_zero hp0 hq0
  calc laplaceTransform (fun t => Complex.cosh (a * t)) s
      = laplaceTransform (fun t => (t : ℂ) ^ 0 *
          (((1 / 2 : ℂ)) * cexp ((a) * t) + ((1 / 2 : ℂ)) * cexp ((-a) * t))) s := by
        congr 1; funext t
        simp only [Complex.cosh, pow_zero, one_mul]
        rw [neg_mul]
        ring
    _ = ((1 / 2 : ℂ)) * (0 ! : ℂ) / (s - (a)) ^ (0 + 1) +
        ((1 / 2 : ℂ)) * (0 ! : ℂ) / (s - (-a)) ^ (0 + 1) :=
      laplace_exponential_combination 0 hp hq _ _
    _ = s / (s ^ 2 - a ^ 2) := by
      norm_num only [Nat.factorial_zero, Nat.factorial_one, Nat.reduceAdd, pow_one]
      simp only [sub_neg_eq_add] at hp0 hq0 ⊢
      field_simp [hp0, hq0, hd]
      ring_nf

/-- DLMF Table 1.14.4, row 12: `t sin(at) ↦ 2as/(s² + a²)²`, `ℜs > |ℑa|`. -/
@[dlmf 1.14.T4]
theorem laplaceTransform_mul_sin {a s : ℂ} (hs : |a.im| < s.re) :
    laplaceTransform (fun t => t * Complex.sin (a * t)) s = 2 * a * s / (s ^ 2 + a ^ 2) ^ 2 := by
  have hp : 0 < (s - (-(a * I))).re := by
    simp only [sub_re, neg_re, mul_I_re]
    linarith [le_abs_self a.im, neg_le_abs a.im]
  have hq : 0 < (s - (a * I)).re := by
    simp only [sub_re, mul_I_re]
    linarith [le_abs_self a.im, neg_le_abs a.im]
  have hp0 : s - (-(a * I)) ≠ 0 := fun h => by simp [h] at hp
  have hq0 : s - (a * I) ≠ 0 := fun h => by simp [h] at hq
  have hd : s ^ 2 + a ^ 2 ≠ 0 := by
    have he : (s - (-(a * I))) * (s - (a * I)) = s ^ 2 + a ^ 2 := by
      ring_nf
      simp [I_sq]
    rw [← he]; exact mul_ne_zero hp0 hq0
  calc laplaceTransform (fun t => (t : ℂ) * Complex.sin (a * t)) s
      = laplaceTransform (fun t => (t : ℂ) ^ 1 *
          ((I / 2) * cexp ((-(a * I)) * t) + (-I / 2) * cexp ((a * I) * t))) s := by
        congr 1; funext t
        simp only [Complex.sin, pow_one]
        rw [show -(a * (t : ℂ)) * I = -(a * I) * t by ring,
          show (a * (t : ℂ)) * I = (a * I) * t by ring]
        ring
    _ = (I / 2) * (1 ! : ℂ) / (s - (-(a * I))) ^ (1 + 1) +
        (-I / 2) * (1 ! : ℂ) / (s - (a * I)) ^ (1 + 1) :=
      laplace_exponential_combination 1 hp hq _ _
    _ = 2 * a * s / (s ^ 2 + a ^ 2) ^ 2 := by
      simp only [Nat.factorial_one, Nat.cast_one, mul_one,
        Nat.reduceAdd, sub_neg_eq_add]
      have hu : s + a * I ≠ 0 := by simpa only [sub_neg_eq_add] using hp0
      have hv : s - a * I ≠ 0 := hq0
      have hrat (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0) (k : ℕ) :
          (I / 2) / u ^ k + (-I / 2) / v ^ k =
            I * (v ^ k - u ^ k) / (2 * (u * v) ^ k) := by
        rw [mul_pow]
        field_simp
        ring
      have hprod : (s + a * I) * (s - a * I) = s ^ 2 + a ^ 2 := by
        ring_nf; simp [I_sq]
      have hdiff : (s - a * I) ^ 2 - (s + a * I) ^ 2 = -4 * a * s * I := by ring
      rw [hrat _ _ hu hv 2, hdiff, hprod]
      have hnum : I * (-4 * a * s * I) = 4 * a * s := by
        calc I * (-4 * a * s * I) = -4 * a * s * (I * I) := by ring
             _ = _ := by rw [I_mul_I]; ring
      rw [hnum]
      field_simp
      ring

/-- DLMF Table 1.14.4, row 13: `t cos(at) ↦ (s² - a²)/(s² + a²)²`, `ℜs > |ℑa|`. -/
@[dlmf 1.14.T4]
theorem laplaceTransform_mul_cos {a s : ℂ} (hs : |a.im| < s.re) :
    laplaceTransform (fun t => t * Complex.cos (a * t)) s =
      (s ^ 2 - a ^ 2) / (s ^ 2 + a ^ 2) ^ 2 := by
  have hp : 0 < (s - ((a * I))).re := by
    simp only [sub_re, mul_I_re]
    linarith [le_abs_self a.im, neg_le_abs a.im]
  have hq : 0 < (s - (-(a * I))).re := by
    simp only [sub_re, neg_re, mul_I_re]
    linarith [le_abs_self a.im, neg_le_abs a.im]
  have hp0 : s - ((a * I)) ≠ 0 := fun h => by simp [h] at hp
  have hq0 : s - (-(a * I)) ≠ 0 := fun h => by simp [h] at hq
  have hd : s ^ 2 + a ^ 2 ≠ 0 := by
    have he : (s - ((a * I))) * (s - (-(a * I))) = s ^ 2 + a ^ 2 := by
      ring_nf
      simp [I_sq]
    rw [← he]; exact mul_ne_zero hp0 hq0
  calc laplaceTransform (fun t => (t : ℂ) * Complex.cos (a * t)) s
      = laplaceTransform (fun t => (t : ℂ) ^ 1 *
          (((1 / 2 : ℂ)) * cexp (((a * I)) * t) + ((1 / 2 : ℂ)) * cexp ((-(a * I)) * t))) s := by
        congr 1; funext t
        simp only [Complex.cos, pow_one]
        rw [show -(a * (t : ℂ)) * I = -(a * I) * t by ring,
          show (a * (t : ℂ)) * I = (a * I) * t by ring]
        ring
    _ = ((1 / 2 : ℂ)) * (1 ! : ℂ) / (s - ((a * I))) ^ (1 + 1) +
        ((1 / 2 : ℂ)) * (1 ! : ℂ) / (s - (-(a * I))) ^ (1 + 1) :=
      laplace_exponential_combination 1 hp hq _ _
    _ = (s ^ 2 - a ^ 2) / (s ^ 2 + a ^ 2) ^ 2 := by
      norm_num only [Nat.factorial_zero, Nat.factorial_one, Nat.reduceAdd, pow_one]
      simp only [sub_neg_eq_add] at hp0 hq0 ⊢
      field_simp [hp0, hq0, hd]
      ring_nf
      norm_num [I_sq, pow_succ]
      ring

/-- DLMF Table 1.14.4, row 14: `(e^{-bt} - e^{-at})/t ↦ ln((s + a)/(s + b))`, `ℜs > -ℜa`,
`ℜs > -ℜb`, principal logarithm. -/
@[dlmf 1.14.T4]
theorem laplaceTransform_exp_neg_sub_exp_neg_div {a b s : ℂ} (ha : -a.re < s.re)
    (hb : -b.re < s.re) :
    laplaceTransform (fun t => (cexp (-b * t) - cexp (-a * t)) / t) s =
      Complex.log ((s + a) / (s + b)) := by
  have hp : 0 < (s + a).re := by simp only [add_re]; linarith
  have hq : 0 < (s + b).re := by simp only [add_re]; linarith
  rw [← Complex.integral_exp_sub_exp_div hp hq]
  unfold laplaceTransform
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only
  rw [← mul_div_assoc, mul_sub, ← Complex.exp_add, ← Complex.exp_add]
  congr 2 <;> ring

/-- DLMF Table 1.14.4, row 15: `2(1 - cosh(at))/t ↦ ln(1 - a²/s²)`, under the **corrected**
condition `ℜs > |ℜa|` (DLMF prints `ℜ(s + a) > 0`, insufficient since the left side is even in
`a`). -/
@[dlmf 1.14.T4]
theorem laplaceTransform_one_sub_cosh_div {a s : ℂ} (hs : |a.re| < s.re) :
    laplaceTransform (fun t => 2 * (1 - Complex.cosh (a * t)) / t) s =
      Complex.log (1 - a ^ 2 / s ^ 2) := by
  have hsre : 0 < s.re := (abs_nonneg _).trans_lt hs
  have hs0 : s ≠ 0 := fun h => by simp [h] at hsre
  have hp : 0 < (s + a).re := by simp only [add_re]; linarith [neg_le_abs a.re]
  have hm : 0 < (s - a).re := by simp only [sub_re]; linarith [le_abs_self a.re]
  have hi₁ := Complex.integrableOn_exp_sub_exp_div hm hsre
  have hi₂ := Complex.integrableOn_exp_sub_exp_div hp hsre
  have heq : laplaceTransform (fun t => 2 * (1 - Complex.cosh (a * t)) / t) s =
      ∫ t in Ioi (0 : ℝ),
        (cexp (-s * t) - cexp (-(s - a) * t)) / t +
          (cexp (-s * t) - cexp (-(s + a) * t)) / t := by
    unfold laplaceTransform
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp only
    rw [Complex.cosh, show -(s - a) * (t : ℂ) = -s * t + a * t by ring,
      show -(s + a) * (t : ℂ) = -s * t + -(a * t) by ring,
      Complex.exp_add, Complex.exp_add]
    ring
  rw [heq, integral_add hi₁ hi₂, Complex.integral_exp_sub_exp_div hm hsre,
    Complex.integral_exp_sub_exp_div hp hsre]
  have hminus : (s - a) / s = 1 - a / s := by rw [sub_div, div_self hs0]
  have hplus : (s + a) / s = 1 + a / s := by rw [add_div, div_self hs0]
  -- TauCeti supplies branch-cut avoidance for ratios of right-half-plane points.
  rw [hminus, hplus, ← Complex.log_one_sub_sq
    (hminus ▸ TauCeti.div_mem_slitPlane_of_re_pos hsre hm)
    (hplus ▸ TauCeti.div_mem_slitPlane_of_re_pos hsre hp), div_pow]

/-- DLMF Table 1.14.4, row 16: `2(1 - cos(at))/t ↦ ln(1 + a²/s²)`, `ℜs > |ℑa|` (DLMF:
`ℜs > 0`, for real `a`). -/
@[dlmf 1.14.T4]
theorem laplaceTransform_one_sub_cos_div {a s : ℂ} (hs : |a.im| < s.re) :
    laplaceTransform (fun t => 2 * (1 - Complex.cos (a * t)) / t) s =
      Complex.log (1 + a ^ 2 / s ^ 2) := by
  have h := laplaceTransform_one_sub_cosh_div (a := a * I) (by simpa using hs)
  convert h using 1
  · congr 1
    ext t
    rw [show a * I * (t : ℂ) = (a * t) * I by ring, Complex.cosh_mul_I]
  · congr 1
    ring_nf
    rw [I_sq]
    ring

/-- DLMF Table 1.14.4, row 17: `sin(at)/t ↦ arctan(a/s)`, `ℜs > |ℑa|` (DLMF: `ℜs > 0`, for real
`a`), principal branch. -/
@[dlmf 1.14.T4]
theorem laplaceTransform_sin_div {a s : ℂ} (hs : |a.im| < s.re) :
    laplaceTransform (fun t => Complex.sin (a * t) / t) s = Complex.arctan (a / s) := by
  have hsre : 0 < s.re := (abs_nonneg _).trans_lt hs
  have hs0 : s ≠ 0 := fun h => by simp [h] at hsre
  have hp : 0 < (s + a * I).re := by
    simp only [add_re, mul_I_re]
    linarith [le_abs_self a.im]
  have hm : 0 < (s - a * I).re := by
    simp only [sub_re, mul_I_re]
    linarith [neg_le_abs a.im]
  have hratio : (1 + a / s * I) / (1 - a / s * I) = (s + a * I) / (s - a * I) := by
    field_simp
  rw [Complex.arctan, hratio, ← Complex.integral_exp_sub_exp_div hp hm,
    ← integral_const_mul]
  unfold laplaceTransform
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only
  rw [Complex.sin, show -(s - a * I) * (t : ℂ) = -s * t + (a * t) * I by ring,
    show -(s + a * I) * (t : ℂ) = -s * t + -(a * t) * I by ring,
    Complex.exp_add, Complex.exp_add]
  ring_nf

end DLMF.AlgebraicAnalytic
