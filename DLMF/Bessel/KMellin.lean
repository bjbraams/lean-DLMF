/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.Gamma
public import DLMF.Bessel.KIntegralRep

/-!
# The Mellin transform of `K_ν` (DLMF 10.43.19)

For `|Re ν| < Re μ`,

`∫₀^∞ t^{μ-1} K_ν(t) dt = 2^{μ-2} Γ((μ-ν)/2) Γ((μ+ν)/2)` (DLMF 10.43.19),

with absolute convergence. The proof inserts Schläfli's form
`K_ν(x) = ½ (x/2)^ν ∫₀^∞ e^{-t - x²/(4t)} t^{-ν-1} dt` (`besselK_ofReal_eq_integral_schlafli`),
interchanges the order of integration (Tonelli, with the real Gaussian moments of Mathlib
bounding the absolute integrand) and evaluates the inner Gaussian moment
`∫₀^∞ x^{s-1} e^{-b x²} dx = ½ b^{-s/2} Γ(s/2)` and the outer Euler integral.

The result is also given in the language of Mathlib's `mellin` (`besselK_mellinConvergent`,
`mellin_besselK`), so that `mellin_comp_rpow` and `mellin_comp_mul_left` apply to
functions such as `K_ν(c t^p)`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

namespace DLMF.Bessel

/-- The Gaussian moment `x^{s-1} e^{-b x²}` is integrable on `(0, ∞)` for `Re s > 0`, `b > 0`. -/
theorem kMel_integrableOn_gauss {s : ℂ} (hs : 0 < s.re) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * exp (-(b * (x : ℂ) ^ 2))) (Ioi 0) := by
  refine (integrableOn_rpow_mul_exp_neg_mul_rpow (s := s.re - 1) (p := 2) (by linarith)
    two_pos hb).mono' (by fun_prop) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
  have hx : 0 < x := hx
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx, norm_exp, Real.rpow_two]
  simp [← ofReal_pow]

/-- The absolute Gaussian moment: `∫₀^∞ x^{Re s-1} e^{-b x²} dx = ½ b^{-Re s/2} Γ(Re s/2)`. -/
theorem kMel_norm_integral_gauss {s : ℂ} (hs : 0 < s.re) {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ in Ioi 0, ‖(x : ℂ) ^ (s - 1)‖ * ‖exp (-(b * (x : ℂ) ^ 2))‖ =
      b ^ (-s.re / 2) * (1 / 2) * Real.Gamma (s.re / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (q := s.re - 1) (p := 2) two_pos
    (by linarith) hb
  rw [show s.re - 1 + 1 = s.re by ring] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx : 0 < x := hx
  rw [norm_cpow_eq_rpow_re_of_pos hx, norm_exp, Real.rpow_two]
  simp [← ofReal_pow]

/-- `(x²)^w = x^{2w}` for `x > 0`. -/
theorem kMel_ofReal_sq_cpow {x : ℝ} (hx : 0 < x) (w : ℂ) :
    ((x ^ 2 : ℝ) : ℂ) ^ w = (x : ℂ) ^ (2 * w) := by
  have hl : (Complex.log x).im = 0 := by rw [← ofReal_log hx.le]; rfl
  rw [ofReal_pow, ← cpow_natCast, ← cpow_mul]
  · push_cast; ring_nf
  · simp [hl]; exact Real.pi_pos
  · simp [hl]; exact Real.pi_pos.le

/-- The complex Gaussian moment: `∫₀^∞ x^{s-1} e^{-b x²} dx = ½ b^{-s/2} Γ(s/2)` for
`Re s > 0`, `b > 0`. -/
theorem kMel_integral_gauss {s : ℂ} (hs : 0 < s.re) {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ in Ioi 0, (x : ℂ) ^ (s - 1) * exp (-(b * (x : ℂ) ^ 2)) =
      (1 / (b : ℂ)) ^ (s / 2) * Gamma (s / 2) / 2 := by
  have hs2 : 0 < (s / 2).re := by simp; linarith
  have h := integral_comp_rpow_Ioi
    (fun y : ℝ => (1 / 2 : ℂ) * ((y : ℂ) ^ (s / 2 - 1) * exp (-(b * y)))) (p := 2) two_ne_zero
  rw [integral_const_mul, integral_cpow_mul_exp_neg_mul_Ioi hs2 hb] at h
  rw [show (1 / (b : ℂ)) ^ (s / 2) * Gamma (s / 2) / 2 = 1 / 2 * ((1 / (b:ℂ)) ^ (s / 2) * Gamma (s / 2)) by
    ring, ← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx : 0 < x := hx
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  rw [abs_two, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two,
    kMel_ofReal_sq_cpow hx, real_smul]
  push_cast
  rw [show 2 * (s / 2 - 1) = (s - 1) - 1 by ring, cpow_sub _ _ hx0, cpow_one]
  field_simp
  rw [← cpow_natCast, ← cpow_add _ _ hx0]
  push_cast; ring_nf

/-- The integrand of the double integral behind 10.43.19, in the variables `(t, x)`. -/
def kMel_kernel (μ ν : ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.1 : ℂ) ^ (-ν - 1) * exp (-(p.1 : ℂ)) *
    ((p.2 : ℂ) ^ (μ + ν - 1) * exp (-(((1 / (4 * p.1) : ℝ) : ℂ) * (p.2 : ℂ) ^ 2)))

/-- The kernel is measurable. -/
theorem kMel_measurable_kernel (μ ν : ℂ) : Measurable (kMel_kernel μ ν) := by
  unfold kMel_kernel; fun_prop

/-- The inner (Gaussian) integral of the kernel in `x`. -/
theorem kMel_inner {μ ν : ℂ} (h : 0 < (μ + ν).re) {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ in Ioi 0, kMel_kernel μ ν (t, x) =
      (4 : ℂ) ^ ((μ + ν) / 2) * Gamma ((μ + ν) / 2) / 2 *
        ((t : ℂ) ^ ((μ - ν) / 2 - 1) * exp (-(t : ℂ))) := by
  have hb : (0 : ℝ) < 1 / (4 * t) := by positivity
  simp only [kMel_kernel]
  rw [integral_const_mul, kMel_integral_gauss h hb]
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have e1 : (1 / ((1 / (4 * t) : ℝ) : ℂ)) = ((4 : ℝ) : ℂ) * (t : ℂ) := by push_cast; field_simp
  rw [e1, mul_cpow_ofReal_nonneg (by norm_num) ht.le]
  have e2 : (t : ℂ) ^ (-ν - 1) * (t : ℂ) ^ ((μ + ν) / 2) = (t : ℂ) ^ ((μ - ν) / 2 - 1) := by
    rw [← cpow_add _ _ ht0]; ring_nf
  linear_combination ((4 : ℂ) ^ ((μ + ν) / 2) * Gamma ((μ + ν) / 2) / 2 * exp (-(t : ℂ))) * e2

/-- The inner integral of the absolute kernel in `x`. -/
theorem kMel_norm_inner {μ ν : ℂ} (h : 0 < (μ + ν).re) {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ in Ioi 0, ‖kMel_kernel μ ν (t, x)‖ =
      (4 : ℝ) ^ ((μ + ν).re / 2) * (1 / 2) * Real.Gamma ((μ + ν).re / 2) *
        (Real.exp (-t) * t ^ ((μ.re - ν.re) / 2 - 1)) := by
  have hb : (0 : ℝ) < 1 / (4 * t) := by positivity
  simp only [kMel_kernel, norm_mul]
  rw [integral_const_mul, kMel_norm_integral_gauss h hb, norm_cpow_eq_rpow_re_of_pos ht, norm_exp]
  simp only [neg_re, ofReal_re, sub_re, one_re]
  rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), neg_div, neg_neg,
    Real.mul_rpow (by norm_num) ht.le]
  have e : t ^ (-ν.re - 1) * t ^ ((μ + ν).re / 2) = t ^ ((μ.re - ν.re) / 2 - 1) := by
    rw [← Real.rpow_add ht]; congr 1; simp only [add_re]; ring
  linear_combination ((4 : ℝ) ^ ((μ + ν).re / 2) * (1 / 2) * Real.Gamma ((μ + ν).re / 2) *
    Real.exp (-t)) * e

/-- The kernel is integrable on `(0, ∞)²` when `|Re ν| < Re μ`. -/
theorem kMel_integrable_kernel {μ ν : ℂ} (h : |ν.re| < μ.re) :
    Integrable (kMel_kernel μ ν) ((volume.restrict (Ioi (0 : ℝ))).prod
      (volume.restrict (Ioi (0 : ℝ)))) := by
  have h1 : 0 < (μ + ν).re := by simp only [add_re]; linarith [neg_abs_le ν.re]
  have h2 : 0 < (μ.re - ν.re) / 2 := by linarith [le_abs_self ν.re]
  refine (integrable_prod_iff (kMel_measurable_kernel μ ν).aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht : 0 < t := ht
    have hb : (0 : ℝ) < 1 / (4 * t) := by positivity
    simp only [kMel_kernel]
    exact (kMel_integrableOn_gauss (s := μ + ν) h1 hb).const_mul _
  · refine IntegrableOn.congr_fun (((Real.GammaIntegral_convergent h2).const_mul
      ((4 : ℝ) ^ ((μ + ν).re / 2) * (1 / 2) * Real.Gamma ((μ + ν).re / 2)))) (fun t ht => ?_)
      measurableSet_Ioi
    exact (kMel_norm_inner h1 ht).symm

/-- Schläfli's form of `x^{μ-1} K_ν(x)` as an integral of the kernel. -/
theorem kMel_schlafli {μ ν : ℂ} {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ (μ - 1) * besselK ν x =
      1 / 2 * (2 : ℂ) ^ (-ν) * ∫ t : ℝ in Ioi 0, kMel_kernel μ ν (t, x) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  rw [besselK_ofReal_eq_integral_schlafli hx ν]
  have e1 : ((x : ℂ) / 2) ^ ν = (x : ℂ) ^ ν * (2 : ℂ) ^ (-ν) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, div_cpow_ofReal_nonneg hx.le (by norm_num),
      cpow_neg, div_eq_mul_inv]
  have e2 : (∫ t : ℝ in Ioi 0, kMel_kernel μ ν (t, x)) = (x : ℂ) ^ (μ + ν - 1) *
      ∫ t : ℝ in Ioi 0, exp (-(t : ℂ) - (x : ℂ) ^ 2 / (4 * t)) * (t : ℂ) ^ (-ν - 1) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht : 0 < t := ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    have e : exp (-(t : ℂ) - (x : ℂ) ^ 2 / (4 * t)) =
        exp (-(t : ℂ)) * exp (-(((1 / (4 * t) : ℝ) : ℂ) * (x : ℂ) ^ 2)) := by
      rw [← exp_add]; congr 1; push_cast; field_simp; ring
    simp only [kMel_kernel]
    rw [e]; ring
  have e3 : (x : ℂ) ^ (μ - 1) * (x : ℂ) ^ ν = (x : ℂ) ^ (μ + ν - 1) := by
    rw [← cpow_add _ _ hx0]; ring_nf
  rw [e1, e2]
  linear_combination (1 / 2 * (2 : ℂ) ^ (-ν) *
    ∫ t : ℝ in Ioi 0, exp (-(t : ℂ) - (x : ℂ) ^ 2 / (4 * t)) * (t : ℂ) ^ (-ν - 1)) * e3

/-- `∫₀^∞ t^{a-1} e^{-t} dt = Γ(a)` for `Re a > 0`. -/
theorem kMel_gamma_integral {a : ℂ} (ha : 0 < a.re) :
    ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (a - 1) * exp (-(t : ℂ)) = Gamma a := by
  have := integral_cpow_mul_exp_neg_mul_Ioi ha one_pos
  simpa using this

/-- **Mellin transform of `K_ν`** (DLMF 10.43.19): for `|Re ν| < Re μ`,
`∫₀^∞ t^{μ-1} K_ν(t) dt = 2^{μ-2} Γ((μ-ν)/2) Γ((μ+ν)/2)`, the integral converging absolutely. -/
@[dlmf 10.43.E19]
theorem besselK_mellin {μ ν : ℂ} (h : |ν.re| < μ.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (μ - 1) * besselK ν t) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (μ - 1) * besselK ν t) =
        2 ^ (μ - 2) * Gamma ((μ - ν) / 2) * Gamma ((μ + ν) / 2) := by
  have h1 : 0 < (μ + ν).re := by simp only [add_re]; linarith [neg_abs_le ν.re]
  have h2 : 0 < ((μ - ν) / 2).re := by
    have : ((μ - ν) / 2).re = (μ.re - ν.re) / 2 := by simp [div_ofNat_re]
    rw [this]; linarith [le_abs_self ν.re]
  have hint := kMel_integrable_kernel h
  constructor
  · refine IntegrableOn.congr_fun ((hint.integral_prod_right).const_mul (1 / 2 * (2 : ℂ) ^ (-ν)))
      (fun x hx => (kMel_schlafli hx).symm) measurableSet_Ioi
  · rw [setIntegral_congr_fun measurableSet_Ioi fun x hx => kMel_schlafli (μ := μ) (ν := ν) hx,
      integral_const_mul]
    have hswap := integral_integral_swap (f := fun t x => kMel_kernel μ ν (t, x)) hint
    rw [← hswap, setIntegral_congr_fun measurableSet_Ioi fun t ht => kMel_inner h1 ht,
      integral_const_mul, kMel_gamma_integral h2]
    have e4 : (4 : ℂ) ^ ((μ + ν) / 2) = (2 : ℂ) ^ (μ + ν) := by
      have := kMel_ofReal_sq_cpow (x := 2) two_pos ((μ + ν) / 2)
      push_cast at this; norm_num at this; rw [this]; ring_nf
    have e5 : (2 : ℂ) ^ (-ν) * (2 : ℂ) ^ (μ + ν) = 4 * (2 : ℂ) ^ (μ - 2) := by
      rw [← cpow_add _ _ two_ne_zero, cpow_sub _ _ two_ne_zero]
      norm_num; ring
    rw [e4]
    linear_combination (Gamma ((μ + ν) / 2) * Gamma ((μ - ν) / 2) / 4) * e5

/-- Mellin convergence of `K_ν` on the real half-line for `|Re ν| < Re μ`. -/
theorem besselK_mellinConvergent {μ ν : ℂ} (h : |ν.re| < μ.re) :
    MellinConvergent (fun t : ℝ => besselK ν t) μ :=
  (besselK_mellin h).1

/-- DLMF 10.43.19 in the language of Mathlib's `mellin`. -/
theorem mellin_besselK {μ ν : ℂ} (h : |ν.re| < μ.re) :
    mellin (fun t : ℝ => besselK ν t) μ = 2 ^ (μ - 2) * Gamma ((μ - ν) / 2) * Gamma ((μ + ν) / 2) :=
  (besselK_mellin h).2

end DLMF.Bessel
