/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Elementary
public import DLMF.Bessel.KIntegralRep
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import DLMFMathlib.Analysis.ODE.LiouvilleGreenComparison

/-!
# Modified Bessel comparison kernels

The hyperbolic integral shows that `K_ν(x)` increases with nonnegative real order. Its
Wronskian identity with `I_ν` then gives `x I_ν(x) K_ν(x) ≤ 1`. The quotient `I_ν/K_ν`
increases along the positive axis. Together, these estimates bound the Green kernel for
`sqrt(x) K_ν(μx)` by `1/μ` after division by its recessive weight, uniformly for positive
`x < t`, `μ > 0` and nonnegative order. These bounds support the uniform modified-Bessel
approximations in DLMF §14.15.
-/

open Complex Filter Set MeasureTheory Asymptotics
open scoped Real Topology
@[expose] public noncomputable section
namespace DLMF.Bessel

/-- The real part of `K` on the positive axis has its real hyperbolic integral representation. -/
lemma re_besselK_eq_integral_cosh (ν : ℝ) {x : ℝ} (hx : 0 < x) :
    (besselK ν x).re = ∫ t : ℝ in Ioi 0,
      Real.exp (-(x * Real.cosh t)) * Real.cosh (ν * t) := by
  rw [besselK_eq_integral_cosh _ (by simpa using hx)]
  have he (t : ℝ) : exp (-((x : ℂ) * (Real.cosh t : ℂ))) * cosh ((ν : ℂ)*t) =
      ((Real.exp (-(x * Real.cosh t)) * Real.cosh (ν * t) : ℝ) : ℂ) := by
    push_cast
    rfl
  simp only [he, _root_.integral_complex_ofReal, ofReal_re]

/-- Absolute convergence of the real hyperbolic kernel defining `K`. -/
private lemma integrableOn_exp_neg_mul_cosh_mul_cosh (ν : ℝ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => Real.exp (-(x * Real.cosh t)) * Real.cosh (ν * t)) (Ioi 0) := by
  have h := (BesselKIntegral.integrable_exp_neg_mul_cosh_add (M := |ν|) hx).integrableOn
    (s := Ioi (0 : ℝ))
  refine h.mono' (by fun_prop : Continuous (fun t : ℝ =>
    Real.exp (-(x * Real.cosh t)) * Real.cosh (ν * t))).aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (Real.cosh_pos _)),
    Real.exp_add]
  gcongr
  calc Real.cosh (ν * t) ≤ Real.exp |ν * t| := BesselKIntegral.cosh_le_exp_abs _
    _ = Real.exp (|ν| * |t|) := by rw [abs_mul]

/-- On the positive axis, `K` is nondecreasing as its nonnegative real order increases. -/
lemma re_besselK_le_re_besselK_of_nonneg_of_le {ν μ : ℝ} (hν : 0 ≤ ν) (hνμ : ν ≤ μ)
    {x : ℝ} (hx : 0 < x) :
    (besselK ν x).re ≤ (besselK μ x).re := by
  rw [re_besselK_eq_integral_cosh ν hx, re_besselK_eq_integral_cosh μ hx]
  apply setIntegral_mono_on (integrableOn_exp_neg_mul_cosh_mul_cosh ν hx)
    (integrableOn_exp_neg_mul_cosh_mul_cosh μ hx) measurableSet_Ioi
  intro t ht
  gcongr
  apply Real.cosh_le_cosh.mpr
  rw [abs_of_nonneg (mul_nonneg hν ht.le),
    abs_of_nonneg (mul_nonneg (hν.trans hνμ) ht.le)]
  exact mul_le_mul_of_nonneg_right hνμ ht.le

/-- For nonnegative real order, `x I_ν(x) K_ν(x) ≤ 1` on the positive axis. -/
lemma mul_re_besselI_mul_re_besselK_le_one {ν x : ℝ} (hν : 0 ≤ ν) (hx : 0 < x) :
    x * (besselI ν x).re * (besselK ν x).re ≤ 1 := by
  obtain ⟨i, hi, hI⟩ := besselI_ofReal_pos (ν := ν) (by linarith) hx
  obtain ⟨i1, hi1, hI1⟩ := besselI_ofReal_pos (ν := ν + 1) (by linarith) hx
  obtain ⟨k, hk, hK⟩ := besselK_ofReal_pos ν hx
  obtain ⟨k1, hk1, hK1⟩ := besselK_ofReal_pos (ν + 1) hx
  have hmono := re_besselK_le_re_besselK_of_nonneg_of_le hν (by linarith : ν ≤ ν + 1) hx
  rw [hK, hK1, ofReal_re, ofReal_re] at hmono
  have hW := besselK_mul_besselI_succ_add (ν : ℂ) (z := x) (Or.inl (by simpa using hx))
  rw [show (ν : ℂ)+1=((ν + 1 : ℝ):ℂ) by push_cast; ring, hI, hI1, hK, hK1] at hW
  have hw := congrArg Complex.re hW
  simp only [add_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero] at hw
  have hw' : (k*i1+k1*i)*x=1 := by
    rw [hw]
    simp only [← ofReal_one, ← ofReal_div, ofReal_re]
    field_simp
  rw [hI, hK, ofReal_re, ofReal_re]
  have hmon := mul_le_mul_of_nonneg_right hmono (mul_nonneg hi.le hx.le)
  have hpos := mul_nonneg (mul_nonneg hk.le hi1.le) hx.le
  nlinarith

/-- The quotient `I_ν/K_ν` increases strictly on the positive axis for nonnegative order. -/
lemma strictMonoOn_re_besselI_div_re_besselK {ν : ℝ} (hν : 0 ≤ ν) :
    StrictMonoOn (fun x : ℝ => (besselI ν x).re / (besselK ν x).re) (Ioi 0) := by
  let i : ℝ → ℝ := fun x => (besselI ν x).re
  let k : ℝ → ℝ := fun x => (besselK ν x).re
  let di : ℝ → ℝ := fun x => (deriv (besselI (ν : ℂ)) x).re
  let dk : ℝ → ℝ := fun x => (deriv (besselK (ν : ℂ)) x).re
  have hi (x : ℝ) (hx : 0 < x) : HasDerivAt i (di x) x :=
    HasDerivAt.real_of_complex
      ((hasDerivAt_besselI (ν := (ν : ℂ))
        (Or.inl (by simpa using hx))).differentiableAt.hasDerivAt)
  have hk (x : ℝ) (hx : 0 < x) : HasDerivAt k (dk x) x :=
    HasDerivAt.real_of_complex
      ((hasDerivAt_besselK (ν : ℂ) (Or.inl (by simpa using hx))).differentiableAt.hasDerivAt)
  have hkpos (x : ℝ) (hx : 0 < x) : 0 < k x := by
    obtain ⟨r, hr, he⟩ := besselK_ofReal_pos ν hx
    simp only [k, he, ofReal_re]
    exact hr
  have hW (x : ℝ) (hx : 0 < x) : k x * di x - dk x * i x = 1/x := by
    have hw := wronskian_besselK_besselI (ν : ℂ) (z := x) (Or.inl (by simpa using hx))
    obtain ⟨r, hr, he⟩ := besselK_ofReal_pos ν hx
    obtain ⟨r1, hr1, he1⟩ := besselI_ofReal_pos (ν := ν) (by linarith) hx
    have hreal := congrArg Complex.re hw
    rw [he, he1] at hreal
    simpa only [i, k, di, dk, he, he1, sub_re, mul_re, ofReal_re, ofReal_im, mul_zero,
      sub_zero, zero_mul,←ofReal_one,←ofReal_div] using hreal
  have hd (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun x => i x / k x) ((1/x) / k x^2) x := by
    convert (hi x hx).div (hk x hx) (hkpos x hx).ne' using 1
    rw [← hW x hx]
    ring
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
  intro x hx
  rw [interior_Ioi] at hx
  rw [(hd x hx).deriv]
  exact div_pos (one_div_pos.mpr hx) (sq_pos_of_pos (hkpos x hx))

namespace ModifiedComparison

/-- The modified Bessel Green determinant is nonnegative when its arguments increase. -/
lemma green_nonneg {ν x t : ℝ} (hν : 0 ≤ ν) (hx : 0 < x) (hxt : x < t) :
    0 ≤ (besselK ν x).re * (besselI ν t).re - (besselI ν x).re * (besselK ν t).re := by
  obtain ⟨k, hk, hK⟩ := besselK_ofReal_pos ν hx
  obtain ⟨kt, hkt, hKt⟩ := besselK_ofReal_pos ν (hx.trans hxt)
  have h := strictMonoOn_re_besselI_div_re_besselK hν hx (hx.trans hxt) hxt
  dsimp only at h
  rw [hK, hKt, ofReal_re, ofReal_re, div_lt_div_iff₀ hk hkt] at h
  rw [hK, hKt, ofReal_re, ofReal_re]
  linarith

/-- The scaled modified Bessel Green kernel has a uniform bound with its recessive weight. -/
lemma norm_green_mul_le {ν μ x t : ℝ} (hν : 0 ≤ ν) (hμ : 0 < μ)
    (hx : 0 < x) (hxt : x < t) :
    ‖(Real.sqrt x : ℂ) * Real.sqrt t *
      (besselK ν (μ * x) * besselI ν (μ * t) - besselI ν (μ * x) * besselK ν (μ * t))‖ *
      (Real.sqrt t * (besselK ν (μ * t)).re) ≤
      Real.sqrt x * (besselK ν (μ * x)).re / μ := by
  have ht : 0 < t := hx.trans hxt
  obtain ⟨kx, hkx, hKx⟩ := besselK_ofReal_pos ν (mul_pos hμ hx)
  obtain ⟨kt, hkt, hKt⟩ := besselK_ofReal_pos ν (mul_pos hμ ht)
  obtain ⟨ix, hix, hIx⟩ := besselI_ofReal_pos (ν := ν) (by linarith) (mul_pos hμ hx)
  obtain ⟨it, hit, hIt⟩ := besselI_ofReal_pos (ν := ν) (by linarith) (mul_pos hμ ht)
  have hnonneg := green_nonneg hν (mul_pos hμ hx)
    (mul_lt_mul_of_pos_left hxt hμ)
  simp only [ofReal_mul] at hKx hKt hIx hIt hnonneg
  rw [hKx, hKt, hIx, hIt, ofReal_re, ofReal_re, ofReal_re, ofReal_re] at hnonneg
  have hprod := mul_re_besselI_mul_re_besselK_le_one hν (mul_pos hμ ht)
  simp only [ofReal_mul] at hprod
  rw [hIt, hKt, ofReal_re, ofReal_re] at hprod
  rw [hKx, hKt, hIx, hIt, ofReal_re, ofReal_re]
  have hc : (Real.sqrt x : ℂ) * (Real.sqrt t : ℂ) *
      ((kx : ℂ)*it-(ix : ℂ)*kt) = ((Real.sqrt x * Real.sqrt t * (kx*it-ix*kt) : ℝ):ℂ) := by
    push_cast
    rfl
  rw [hc, norm_real, Real.norm_of_nonneg (by positivity)]
  have hs : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  rw [le_div_iff₀ hμ]
  have hbound : (kx*it-ix*kt)*kt ≤ kx*(it*kt) := by
    nlinarith [mul_nonneg hix.le (sq_nonneg kt)]
  calc Real.sqrt x * Real.sqrt t * (kx*it-ix*kt) * (Real.sqrt t * kt) * μ
      = Real.sqrt x * ((kx*it-ix*kt)*kt) * (t*μ) := by
        calc _ = Real.sqrt x * ((kx*it-ix*kt)*kt) * (Real.sqrt t ^ 2 * μ) := by ring
          _ = _ := by rw [hs]
    _ ≤ Real.sqrt x * (kx*(it*kt)) * (t*μ) := by gcongr
    _ = Real.sqrt x * kx * (μ * t*it*kt) := by ring
    _ ≤ Real.sqrt x * kx * 1 := by gcongr
    _ = _ := by ring

/-- The square - root gauge converts the modified Bessel equation to its normal form. -/
private lemma hasDerivAt_sqrt_mul_comp_modifiedBessel {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G slitPlane) {ν μ : ℝ} (hμ : 0 < μ)
    (hode : ∀ z ∈ slitPlane, z ^ 2 * iteratedDeriv 2 G z + z * deriv G z -
      (z ^ 2 + (ν : ℂ) ^ 2) * G z = 0) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => (Real.sqrt x : ℂ) * G ((μ : ℂ) * x))
      ((2 * (Real.sqrt x : ℂ))⁻¹ * G ((μ : ℂ) * x) +
        (Real.sqrt x : ℂ) * μ * deriv G ((μ : ℂ) * x)) x ∧
    HasDerivAt (fun x : ℝ => (2 * (Real.sqrt x : ℂ))⁻¹ * G ((μ : ℂ) * x) +
        (Real.sqrt x : ℂ) * μ * deriv G ((μ : ℂ) * x))
      ((μ ^ 2 + (ν ^ 2 - 1 / 4) / x ^ 2 : ℝ) * ((Real.sqrt x : ℂ) * G ((μ : ℂ) * x))) x := by
  have hGa : AnalyticOnNhd ℂ G slitPlane := hG.analyticOnNhd isOpen_slitPlane
  have hz : (μ : ℂ) * x ∈ slitPlane := Or.inl (by simp; positivity)
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hs0 : (Real.sqrt x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hsq : (Real.sqrt x : ℂ) ^ 2 = x := by rw [← ofReal_pow, Real.sq_sqrt hx.le]
  have hS : HasDerivAt (fun x : ℝ => (Real.sqrt x : ℂ)) (2 * (Real.sqrt x : ℂ))⁻¹ x := by
    convert (Real.hasDerivAt_sqrt hx.ne').ofReal_comp using 1
    push_cast
    ring
  have hX : HasDerivAt (fun x : ℝ => (μ : ℂ) * x) μ x := by
    simpa using ((hasDerivAt_id (x : ℂ)).comp_ofReal.const_mul (μ : ℂ))
  have hGc := ((hGa _ hz).differentiableAt.hasDerivAt).comp x hX
  have hdGc := ((hGa.deriv _ hz).differentiableAt.hasDerivAt).comp x hX
  constructor
  · convert hS.mul hGc using 1
    · rfl
    · dsimp only [Function.comp_def]
      ring
  · have hinv := (hS.const_mul 2).inv (mul_ne_zero two_ne_zero hs0)
    have h := (hinv.mul hGc).add ((hS.mul_const (μ : ℂ)).mul hdGc)
    convert h using 1
    · rfl
    · have ho := hode _ hz
      rw [iteratedDeriv_succ, iteratedDeriv_one] at ho
      dsimp only [Function.comp_def, Pi.inv_apply]
      generalize G ((μ : ℂ) * x)=b0 at ho ⊢
      generalize deriv G ((μ : ℂ) * x)=b1 at ho ⊢
      generalize deriv (deriv G) ((μ : ℂ) * x)=b2 at ho ⊢
      push_cast at ho ⊢
      rw [← hsq] at ho ⊢
      field_simp
      linear_combination (-16 : ℂ) * ho

/-- The scaled recessive comparison function `sqrt(x) K_ν(μx)` on the positive axis. -/
def recessive (ν μ x : ℝ) : ℂ := (Real.sqrt x : ℂ) * besselK ν ((μ : ℂ) * x)
/-- The scaled dominant comparison function `sqrt(x) I_ν(μx)` on the positive axis. -/
def dominant (ν μ x : ℝ) : ℂ := (Real.sqrt x : ℂ) * besselI ν ((μ : ℂ) * x)
/-- The first derivative of the scaled recessive comparison function on the positive axis. -/
def recessiveDerivative (ν μ x : ℝ) : ℂ :=
  (2 * (Real.sqrt x : ℂ))⁻¹ * besselK ν ((μ : ℂ) * x) +
    (Real.sqrt x : ℂ) * μ * deriv (besselK ν) ((μ : ℂ) * x)
/-- The first derivative of the scaled dominant comparison function on the positive axis. -/
def dominantDerivative (ν μ x : ℝ) : ℂ :=
  (2 * (Real.sqrt x : ℂ))⁻¹ * besselI ν ((μ : ℂ) * x) +
    (Real.sqrt x : ℂ) * μ * deriv (besselI ν) ((μ : ℂ) * x)

/-- The scaled recessive function satisfies its defining differential equation. -/
lemma hasDerivAt_recessive {ν μ : ℝ} (hμ : 0 < μ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (recessive ν μ) (recessiveDerivative ν μ x) x ∧
    HasDerivAt (recessiveDerivative ν μ)
      ((μ ^ 2 + (ν ^ 2 - 1 / 4) / x ^ 2 : ℝ) * recessive ν μ x) x := by
  exact hasDerivAt_sqrt_mul_comp_modifiedBessel
    (fun z hz => (hasDerivAt_besselK (ν : ℂ) hz).differentiableAt.differentiableWithinAt)
    hμ (fun z hz => besselK_ode_all (ν : ℂ) hz) hx

/-- The scaled dominant function satisfies its defining differential equation. -/
lemma hasDerivAt_dominant {ν μ : ℝ} (hμ : 0 < μ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (dominant ν μ) (dominantDerivative ν μ x) x ∧
    HasDerivAt (dominantDerivative ν μ)
      ((μ ^ 2 + (ν ^ 2 - 1 / 4) / x ^ 2 : ℝ) * dominant ν μ x) x := by
  exact hasDerivAt_sqrt_mul_comp_modifiedBessel
    (fun z hz => (hasDerivAt_besselI (ν := (ν : ℂ)) hz).differentiableAt.differentiableWithinAt)
    hμ (fun z hz => besselI_ode hz) hx

/-- The scaled comparison solutions have constant Wronskian one. -/
lemma wronskian_recessive_dominant {ν μ : ℝ} (hμ : 0 < μ) {x : ℝ} (hx : 0 < x) :
    recessive ν μ x * dominantDerivative ν μ x -
      recessiveDerivative ν μ x * dominant ν μ x = 1 := by
  have hz : (μ : ℂ) * x ∈ slitPlane := Or.inl (by simp; positivity)
  have hw := wronskian_besselK_besselI (ν : ℂ) hz
  have hs : (Real.sqrt x : ℂ) ^ 2 = x := by rw [← ofReal_pow, Real.sq_sqrt hx.le]
  calc
    _ = (μ : ℂ) * (Real.sqrt x : ℂ) ^ 2 *
      (besselK ν ((μ : ℂ) * x) * deriv (besselI ν) ((μ : ℂ) * x) -
        deriv (besselK ν) ((μ : ℂ) * x) * besselI ν ((μ : ℂ) * x)) := by
      simp only [recessive, dominant, recessiveDerivative, dominantDerivative]
      ring
    _ = 1 := by
      rw [hw, hs]
      field_simp [ofReal_ne_zero.mpr hμ.ne', ofReal_ne_zero.mpr hx.ne']

/-- The norm of the recessive comparison function is its positive real value. -/
lemma norm_recessive {ν μ : ℝ} (hμ : 0 < μ) {x : ℝ} (hx : 0 < x) :
    ‖recessive ν μ x‖ = Real.sqrt x * (besselK ν ((μ : ℂ) * x)).re := by
  obtain ⟨k, hk, hK⟩ := besselK_ofReal_pos ν (mul_pos hμ hx)
  simp only [ofReal_mul] at hK
  simp only [recessive, hK, norm_mul, norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg x),
    norm_real, Real.norm_of_nonneg hk.le, ofReal_re]

/-- The norm of the dominant comparison function is its positive real value. -/
lemma norm_dominant {ν μ : ℝ} (hν : 0 ≤ ν) (hμ : 0 < μ) {x : ℝ} (hx : 0 < x) :
    ‖dominant ν μ x‖ = Real.sqrt x * (besselI ν ((μ : ℂ) * x)).re := by
  obtain ⟨i, hi, hI⟩ := besselI_ofReal_pos (ν := ν) (by linarith) (mul_pos hμ hx)
  simp only [ofReal_mul] at hI
  simp only [dominant, hI, norm_mul, norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg x),
    norm_real, Real.norm_of_nonneg hi.le, ofReal_re]

/-- The recessive comparison function has positive norm on the positive axis. -/
lemma norm_recessive_pos {ν μ : ℝ} (hμ : 0 < μ) {x : ℝ} (hx : 0 < x) :
    0 < ‖recessive ν μ x‖ := by
  obtain ⟨k, hk, hK⟩ := besselK_ofReal_pos ν (mul_pos hμ hx)
  simp only [ofReal_mul] at hK
  rw [norm_recessive hμ hx, hK, ofReal_re]
  exact mul_pos (Real.sqrt_pos.mpr hx) hk

/-- The dominant comparison function has positive norm on the positive axis. -/
lemma norm_dominant_pos {ν μ : ℝ} (hν : 0 ≤ ν) (hμ : 0 < μ) {x : ℝ} (hx : 0 < x) :
    0 < ‖dominant ν μ x‖ := by
  obtain ⟨i, hi, hI⟩ := besselI_ofReal_pos (ν := ν) (by linarith) (mul_pos hμ hx)
  simp only [ofReal_mul] at hI
  rw [norm_dominant hν hμ hx, hI, ofReal_re]
  exact mul_pos (Real.sqrt_pos.mpr hx) hi

/-- The Green determinant times its recessive weight is bounded by `1 / μ`. -/
lemma norm_green_mul_norm_recessive_le {ν μ x t : ℝ} (hν : 0 ≤ ν) (hμ : 0 < μ)
    (hx : 0 < x) (hxt : x < t) :
    ‖recessive ν μ x * dominant ν μ t - dominant ν μ x * recessive ν μ t‖ *
      ‖recessive ν μ t‖ ≤ ‖recessive ν μ x‖ / μ := by
  rw [norm_recessive hμ hx, norm_recessive hμ (hx.trans hxt)]
  have he : recessive ν μ x * dominant ν μ t - dominant ν μ x * recessive ν μ t =
      (Real.sqrt x : ℂ) * Real.sqrt t * (besselK ν ((μ : ℂ) * x) * besselI ν ((μ : ℂ) * t) -
        besselI ν ((μ : ℂ) * x) * besselK ν ((μ : ℂ) * t)) := by
    simp only [recessive, dominant]
    ring
  rw [he]
  exact norm_green_mul_le hν hμ hx hxt

/-- The product of the scaled comparison functions is bounded by `1 / μ`. -/
lemma norm_dominant_mul_norm_recessive_le {ν μ x : ℝ} (hν : 0 ≤ ν) (hμ : 0 < μ)
    (hx : 0 < x) : ‖dominant ν μ x‖ * ‖recessive ν μ x‖ ≤ 1 / μ := by
  rw [norm_dominant hν hμ hx, norm_recessive hμ hx, le_div_iff₀ hμ]
  have h := mul_re_besselI_mul_re_besselK_le_one hν (mul_pos hμ hx)
  simp only [ofReal_mul] at h
  calc
    _ = μ * x * (besselI ν ((μ : ℂ) * x)).re * (besselK ν ((μ : ℂ) * x)).re := by
        have hs : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
        calc
          _ = μ * Real.sqrt x ^ 2 * (besselI ν ((μ : ℂ) * x)).re *
              (besselK ν ((μ : ℂ) * x)).re := by ring
          _ = _ := by rw [hs]
    _ ≤ 1 := h

/-- The quotient of recessive and dominant norms decreases along the positive axis. -/
lemma norm_recessive_div_norm_dominant_le {ν μ x t : ℝ} (hν : 0 ≤ ν) (hμ : 0 < μ)
    (hx : 0 < x) (hxt : x < t) :
    ‖recessive ν μ t‖ / ‖dominant ν μ t‖ ≤ ‖recessive ν μ x‖ / ‖dominant ν μ x‖ := by
  have ht : 0 < t := hx.trans hxt
  obtain ⟨kx, hkx, hKx⟩ := besselK_ofReal_pos ν (mul_pos hμ hx)
  obtain ⟨kt, hkt, hKt⟩ := besselK_ofReal_pos ν (mul_pos hμ ht)
  obtain ⟨ix, hix, hIx⟩ := besselI_ofReal_pos (ν := ν) (by linarith) (mul_pos hμ hx)
  obtain ⟨it, hit, hIt⟩ := besselI_ofReal_pos (ν := ν) (by linarith) (mul_pos hμ ht)
  have h := green_nonneg hν (mul_pos hμ hx) (mul_lt_mul_of_pos_left hxt hμ)
  simp only [ofReal_mul] at hKx hKt hIx hIt h
  rw [hKx, hKt, hIx, hIt, ofReal_re, ofReal_re, ofReal_re, ofReal_re] at h
  rw [norm_recessive hμ ht, norm_recessive hμ hx, norm_dominant hν hμ ht,
    norm_dominant hν hμ hx, hKx, hKt, hIx, hIt, ofReal_re, ofReal_re, ofReal_re, ofReal_re,
    mul_div_mul_left _ _ (Real.sqrt_pos.mpr ht).ne',
    mul_div_mul_left _ _ (Real.sqrt_pos.mpr hx).ne', div_le_div_iff₀ hit hix]
  linarith

/-- A derivative envelope for the weighted modified - Bessel Green kernel. -/
def derivativeWeight (ν μ x : ℝ) : ℝ :=
  ‖recessiveDerivative ν μ x‖ +
    ‖dominantDerivative ν μ x‖ * (‖recessive ν μ x‖ / ‖dominant ν μ x‖)

/-- The derivative of the Green determinant has its weighted `1 / μ` bound. -/
lemma norm_green_deriv_mul_norm_recessive_le {ν μ x t : ℝ} (hν : 0 ≤ ν) (hμ : 0 < μ)
    (hx : 0 < x) (hxt : x < t) :
    ‖recessiveDerivative ν μ x * dominant ν μ t - dominantDerivative ν μ x * recessive ν μ t‖ *
      ‖recessive ν μ t‖ ≤ derivativeWeight ν μ x / μ := by
  have ht : 0 < t := hx.trans hxt
  have hDt := (norm_dominant_pos hν hμ ht).ne'
  calc
    _ ≤ (‖recessiveDerivative ν μ x‖ * ‖dominant ν μ t‖ +
        ‖dominantDerivative ν μ x‖ * ‖recessive ν μ t‖) * ‖recessive ν μ t‖ := by
        gcongr
        simpa only [norm_mul] using norm_sub_le (recessiveDerivative ν μ x * dominant ν μ t)
          (dominantDerivative ν μ x * recessive ν μ t)
    _ = ‖recessiveDerivative ν μ x‖ * (‖dominant ν μ t‖ * ‖recessive ν μ t‖) +
        ‖dominantDerivative ν μ x‖ * (‖recessive ν μ t‖ / ‖dominant ν μ t‖) *
          (‖dominant ν μ t‖ * ‖recessive ν μ t‖) := by field_simp
    _ ≤ ‖recessiveDerivative ν μ x‖ * (1 / μ) +
        ‖dominantDerivative ν μ x‖ * (‖recessive ν μ x‖ / ‖dominant ν μ x‖) * (1 / μ) := by
        have hp := norm_dominant_mul_norm_recessive_le hν hμ ht
        have hr := norm_recessive_div_norm_dominant_le hν hμ hx hxt
        refine add_le_add (mul_le_mul_of_nonneg_left hp (norm_nonneg _)) ?_
        calc
          _ ≤ ‖dominantDerivative ν μ x‖ * (‖recessive ν μ x‖ / ‖dominant ν μ x‖) *
              (‖dominant ν μ t‖ * ‖recessive ν μ t‖) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hr (norm_nonneg _)) (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by simp only [derivativeWeight]; ring

/-- The square of the recessive comparison norm has a uniform tail bound. -/
lemma norm_recessive_sq_le {ν μ x t : ℝ} (hν : 0 ≤ ν) (hμ : 0 < μ)
    (hx : 0 < x) (hxt : x < t) :
    ‖recessive ν μ t‖ ^ 2 ≤ (‖recessive ν μ x‖ / ‖dominant ν μ x‖) / μ := by
  have ht : 0 < t := hx.trans hxt
  have hDt := (norm_dominant_pos hν hμ ht).ne'
  have hp := norm_dominant_mul_norm_recessive_le hν hμ ht
  have hr := norm_recessive_div_norm_dominant_le hν hμ hx hxt
  calc
    _ = (‖recessive ν μ t‖ / ‖dominant ν μ t‖) *
        (‖dominant ν μ t‖ * ‖recessive ν μ t‖) := by field_simp
    _ ≤ (‖recessive ν μ x‖ / ‖dominant ν μ x‖) * (‖dominant ν μ t‖ * ‖recessive ν μ t‖) :=
          mul_le_mul_of_nonneg_right hr (by positivity)
    _ ≤ (‖recessive ν μ x‖ / ‖dominant ν μ x‖) * (1 / μ) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

/-- An integrable perturbation of the modified Bessel normal form has a recessive solution
with relative error bounded by `exp((∫ ‖ψ‖) / μ) - 1` and the corresponding derivative bound. -/
lemma exists_solution {ν μ : ℝ} (hν : 0 ≤ ν) (hμ : 0 < μ)
    {ψ : ℝ → ℂ} (hψc : ContinuousOn ψ (Ioi 0)) (hψi : IntegrableOn ψ (Ioi 0)) :
    ∃ η η' : ℝ → ℂ, ∀ x : ℝ, 0 < x →
      HasDerivAt (fun x => recessive ν μ x + η x) (recessiveDerivative ν μ x + η' x) x ∧
      HasDerivAt (fun x => recessiveDerivative ν μ x + η' x)
        ((((μ ^ 2 + (ν ^ 2 - 1 / 4) / x ^ 2 : ℝ):ℂ) + ψ x) * (recessive ν μ x + η x)) x ∧
      ‖η x‖ ≤ ‖recessive ν μ x‖ * (Real.exp ((∫ t in Ioi x, ‖ψ t‖) / μ) - 1) ∧
      ‖η' x‖ ≤ derivativeWeight ν μ x * (Real.exp ((∫ t in Ioi x, ‖ψ t‖) / μ) - 1) := by
  have hRc : ContinuousOn (recessive ν μ) (Ioi 0) := fun x hx =>
    (hasDerivAt_recessive hμ hx).1.continuousAt.continuousWithinAt
  have hDc : ContinuousOn (dominant ν μ) (Ioi 0) := fun x hx =>
    (hasDerivAt_dominant hμ hx).1.continuousAt.continuousWithinAt
  have hΦc : ContinuousOn (fun x => (‖recessive ν μ x‖ : ℂ)) (Ioi 0) :=
    continuous_ofReal.comp_continuousOn hRc.norm
  have hi1 (c : ℝ) (hc : 0 < c) :
      IntegrableOn (fun t => dominant ν μ t * (‖recessive ν μ t‖ : ℂ) * ψ t) (Ioi c) := by
    refine (IntegrableOn.mono_set (hψi.norm.const_mul (1 / μ)) (Ioi_subset_Ioi hc.le)).mono'
      ((((hDc.mul hΦc).mul hψc).mono (Ioi_subset_Ioi hc.le)).aestronglyMeasurable
        measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, norm_mul, norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (norm_dominant_mul_norm_recessive_le hν hμ (hc.trans ht)) (norm_nonneg _)
  have hi2 (c : ℝ) (hc : 0 < c) :
      IntegrableOn (fun t => recessive ν μ t * (‖recessive ν μ t‖ : ℂ) * ψ t) (Ioi c) := by
    refine (IntegrableOn.mono_set
      (hψi.norm.const_mul ((‖recessive ν μ c‖ / ‖dominant ν μ c‖) / μ))
        (Ioi_subset_Ioi hc.le)).mono'
      ((((hRc.mul hΦc).mul hψc).mono (Ioi_subset_Ioi hc.le)).aestronglyMeasurable
        measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, norm_mul, norm_real, Real.norm_of_nonneg (norm_nonneg _),←pow_two]
    exact mul_le_mul_of_nonneg_right (norm_recessive_sq_le hν hμ hc ht) (norm_nonneg _)
  have hK : ∀ x t : ℝ, 0 < x → x < t →
      ‖recessive ν μ x * dominant ν μ t - dominant ν μ x * recessive ν μ t‖ *
        ‖recessive ν μ t‖ * ‖ψ t‖ ≤ ‖(1 : ℂ)‖ * ‖recessive ν μ x‖ * (‖ψ t‖ / μ) := by
    intro x t hx hxt
    rw [norm_one, one_mul]
    calc _ ≤ (‖recessive ν μ x‖ / μ) * ‖ψ t‖ :=
        mul_le_mul_of_nonneg_right (norm_green_mul_norm_recessive_le hν hμ hx hxt) (norm_nonneg _)
      _ = _ := by ring
  have hK1 : ∀ x t : ℝ, 0 < x → x < t →
      ‖recessiveDerivative ν μ x * dominant ν μ t -
        dominantDerivative ν μ x * recessive ν μ t‖ * ‖recessive ν μ t‖ * ‖ψ t‖ ≤
          ‖(1 : ℂ)‖ * derivativeWeight ν μ x * (‖ψ t‖ / μ) := by
    intro x t hx hxt
    rw [norm_one, one_mul]
    calc _ ≤ (derivativeWeight ν μ x / μ) * ‖ψ t‖ :=
        mul_le_mul_of_nonneg_right
          (norm_green_deriv_mul_norm_recessive_le hν hμ hx hxt) (norm_nonneg _)
      _ = _ := by ring
  obtain ⟨η, η', h⟩ := LiouvilleGreen.exists_solution_of_comparison
    (a := 0) (𝒲 := (1 : ℂ)) (Q := fun x => ((μ ^ 2 + (ν ^ 2 - 1 / 4) / x ^ 2 : ℝ):ℂ))
    (y₁ := recessive ν μ) (y₁' := recessiveDerivative ν μ)
    (y₂ := dominant ν μ) (y₂' := dominantDerivative ν μ)
    (Φ := fun x => ‖recessive ν μ x‖) (Φ₁ := derivativeWeight ν μ)
    (ρ := fun x => ‖ψ x‖ / μ) one_ne_zero
    (fun x hx => (hasDerivAt_recessive hμ hx).1)
    (fun x hx => (hasDerivAt_recessive hμ hx).2)
    (fun x hx => (hasDerivAt_dominant hμ hx).1)
    (fun x hx => (hasDerivAt_dominant hμ hx).2)
    (fun x hx => wronskian_recessive_dominant hμ hx) hψc
    (fun x hx => norm_recessive_pos hμ hx) hRc.norm (fun _ _ => le_rfl)
    hi1 hi2 (hψc.norm.div_const μ)
    (fun c hc => IntegrableOn.mono_set (hψi.norm.div_const μ) (Ioi_subset_Ioi hc.le)) hK hK1
  refine ⟨η, η', fun x hx => ?_⟩
  simpa only [integral_div] using h x hx

end ModifiedComparison
end DLMF.Bessel
