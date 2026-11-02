/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.SpectralExistence
public import DLMF.Mathieu.Basic
public import DLMF.Mathieu.Noninteger.Basic
public import DLMF.Mathieu.Properties.BasicSolutions
public import DLMFMathlib.Analysis.ODE.SturmDeformation

/-!
# Continuation of real Floquet roots along a segment

For real `q` and `|c₀| < 1` this file follows a root `a` of the characteristic equation
`w_I(π; a, t q) = c₀` (DLMF 28.2.16 with `c₀ = cos πν`) continuously in `t`. This is the analytic
core of the normality of real parameters (DLMF §28.12(i)) used for `λ_ν(q)`.

For real `a`, `Q` the basic solutions are real on the real axis. Lagrange's identity for the
solutions with parameters `a` and `a'` gives the difference formula
`w_I(π; a', Q) - w_I(π; a, Q) = (a' - a) g(a, a', Q) / 2` with `g` continuous, so
`∂ₐ w_I(π; a, Q) = g(a, a, Q) / 2`. At a root with `|c₀| < 1` the Wronskian identity
`w_II(π) w_I'(π) = w_I(π)² - 1 < 0` makes `g(a, a, Q) = -w_II(π) ∫ w_I² + w_I'(π) ∫ w_II²`
definite, so all roots are simple. The roots are bounded below (there are none for
`a < -(2|Q| + 1)`) and unbounded above, so for each `t` they can be enumerated increasingly;
the zero-count deformation theorem (`ODE.sturmDef_eventually_ncard_eq`) shows that the `k`-th
root depends continuously on `t`, and the local one-zero theorem (`ODE.sturmDef_local`) gives
uniqueness of continuous root paths.

## Main results

* `exists_continuous_re_mathieuWI_pi_eq`: a continuous path of roots through a given root at
  `q = 0`.
* `eqOn_of_re_mathieuWI_pi_eq`: two continuous root paths on `[0, 1]` with the same initial
  value coincide.
* `isFloquetSolution_mathieuWII_pi_mul_add`: an explicit Floquet solution
  `w_II(π) w_I + (e^{πiν} - w_I(π)) w_II` when `cos πν = w_I(π)`.
* `im_eq_zero_of_isMeCoeffSeq`: for real `ν`, `q` the eigenvalue of an absolutely summable
  solution of 28.14.4 is real.
* `abs_cos_pi_mul_lt_one`: `|cos πν| < 1` for real `ν ∉ ℤ`.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Topology Real ComplexConjugate

namespace DLMF.Mathieu

/-- Real restriction of `w_I`. -/
private def r1 (a Q x : ℝ) : ℝ := (mathieuWI a Q x).re
/-- Real restriction of `w_II`. -/
private def r2 (a Q x : ℝ) : ℝ := (mathieuWII a Q x).re
/-- Real restriction of `w_I'`. -/
private def d1 (a Q x : ℝ) : ℝ := (deriv (mathieuWI a Q) x).re
/-- Real restriction of `w_II'`. -/
private def d2 (a Q x : ℝ) : ℝ := (deriv (mathieuWII a Q) x).re

private lemma famI (Q : ℝ) :
    (∀ (a x : ℝ), mathieuWI a Q x = ((mathieuWI a Q x).re : ℂ) ∧
      deriv (mathieuWI a Q) x = ((deriv (mathieuWI a Q) x).re : ℂ)) ∧
    (∀ (a x : ℝ), HasDerivAt (fun x : ℝ => (mathieuWI a Q x).re) (deriv (mathieuWI a Q) x).re x) ∧
    (∀ (a x : ℝ), HasDerivAt (fun x : ℝ => (deriv (mathieuWI a Q) x).re)
      ((2 * Q * Real.cos (2 * x) - a) * (mathieuWI a Q x).re) x) ∧
    ∀ (x : ℝ), (Differentiable ℂ fun a => mathieuWI a Q x) ∧
      Differentiable ℂ fun a => deriv (mathieuWI a Q) x :=
  real_family_of_isMathieuSolution Q (w := fun a => mathieuWI a Q)
    (fun a => isMathieuSolution_mathieuWI a Q) (α := 1) (β := 0)
    (fun a => by simp [(mathieuWI_spec a Q).2.1]) (fun a => by simp [(mathieuWI_spec a Q).2.2])

private lemma famII (Q : ℝ) :
    (∀ (a x : ℝ), mathieuWII a Q x = ((mathieuWII a Q x).re : ℂ) ∧
      deriv (mathieuWII a Q) x = ((deriv (mathieuWII a Q) x).re : ℂ)) ∧
    (∀ (a x : ℝ), HasDerivAt (fun x : ℝ => (mathieuWII a Q x).re)
      (deriv (mathieuWII a Q) x).re x) ∧
    (∀ (a x : ℝ), HasDerivAt (fun x : ℝ => (deriv (mathieuWII a Q) x).re)
      ((2 * Q * Real.cos (2 * x) - a) * (mathieuWII a Q x).re) x) ∧
    ∀ (x : ℝ), (Differentiable ℂ fun a => mathieuWII a Q x) ∧
      Differentiable ℂ fun a => deriv (mathieuWII a Q) x :=
  real_family_of_isMathieuSolution Q (w := fun a => mathieuWII a Q)
    (fun a => isMathieuSolution_mathieuWII a Q) (α := 0) (β := 1)
    (fun a => by simp [(mathieuWII_spec a Q).2.1]) (fun a => by simp [(mathieuWII_spec a Q).2.2])

private lemma r1_real (a Q x : ℝ) : mathieuWI a Q x = (r1 a Q x : ℂ) := ((famI Q).1 a x).1
private lemma r2_real (a Q x : ℝ) : mathieuWII a Q x = (r2 a Q x : ℂ) := ((famII Q).1 a x).1
private lemma d1_real (a Q x : ℝ) : deriv (mathieuWI a Q) x = (d1 a Q x : ℂ) :=
  ((famI Q).1 a x).2
private lemma d2_real (a Q x : ℝ) : deriv (mathieuWII a Q) x = (d2 a Q x : ℂ) :=
  ((famII Q).1 a x).2

private lemma hasDerivAt_r1 (a Q x : ℝ) : HasDerivAt (r1 a Q) (d1 a Q x) x := (famI Q).2.1 a x
private lemma hasDerivAt_r2 (a Q x : ℝ) : HasDerivAt (r2 a Q) (d2 a Q x) x := (famII Q).2.1 a x
private lemma hasDerivAt_d1 (a Q x : ℝ) :
    HasDerivAt (d1 a Q) ((2 * Q * Real.cos (2 * x) - a) * r1 a Q x) x := (famI Q).2.2.1 a x
private lemma hasDerivAt_d2 (a Q x : ℝ) :
    HasDerivAt (d2 a Q) ((2 * Q * Real.cos (2 * x) - a) * r2 a Q x) x := (famII Q).2.2.1 a x

private lemma r1_zero (a Q : ℝ) : r1 a Q 0 = 1 := by simp [r1, (mathieuWI_spec a Q).2.1]
private lemma d1_zero (a Q : ℝ) : d1 a Q 0 = 0 := by simp [d1, (mathieuWI_spec a Q).2.2]
private lemma r2_zero (a Q : ℝ) : r2 a Q 0 = 0 := by simp [r2, (mathieuWII_spec a Q).2.1]
private lemma d2_zero (a Q : ℝ) : d2 a Q 0 = 1 := by simp [d2, (mathieuWII_spec a Q).2.2]

private lemma wronskian_real (a Q x : ℝ) : r1 a Q x * d2 a Q x - d1 a Q x * r2 a Q x = 1 := by
  have h := mathieuWI_wronskian a Q x
  rw [r1_real, r2_real, d1_real, d2_real] at h
  exact_mod_cast h

private lemma d2_pi (a Q : ℝ) : d2 a Q π = r1 a Q π := by
  have h := mathieuWI_pi_eq_deriv_mathieuWII_pi a Q
  have e1 := r1_real a Q π
  have e2 := d2_real a Q π
  rw [e1, e2] at h
  exact_mod_cast h.symm

private lemma continuous_r1 : Continuous (fun p : ℝ × ℝ × ℝ => r1 p.1 p.2.1 p.2.2) := by
  have h := differentiable_mathieuWI_mathieuWII.1.continuous
  have hm : Continuous (fun p : ℝ × ℝ × ℝ => (((p.2.2 : ℝ) : ℂ), ((p.1 : ℝ) : ℂ),
      ((p.2.1 : ℝ) : ℂ))) := by fun_prop
  exact Complex.continuous_re.comp (h.comp hm)

private lemma continuous_r2 : Continuous (fun p : ℝ × ℝ × ℝ => r2 p.1 p.2.1 p.2.2) := by
  have h := differentiable_mathieuWI_mathieuWII.2.continuous
  have hm : Continuous (fun p : ℝ × ℝ × ℝ => (((p.2.2 : ℝ) : ℂ), ((p.1 : ℝ) : ℂ),
      ((p.2.1 : ℝ) : ℂ))) := by fun_prop
  exact Complex.continuous_re.comp (h.comp hm)

private lemma d1_pi_eq (a Q : ℝ) :
    d1 a Q π = ∫ x in (0 : ℝ)..π, (2 * Q * Real.cos (2 * x) - a) * r1 a Q x := by
  have hc : Continuous (fun x => (2 * Q * Real.cos (2 * x) - a) * r1 a Q x) := by
    have : Continuous (r1 a Q) := continuous_r1.comp (by fun_prop :
      Continuous (fun x : ℝ => (a, Q, x)))
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_d1 a Q x)
    (hc.intervalIntegrable _ _), d1_zero, sub_zero]

private lemma continuous_d1_pi : Continuous (fun p : ℝ × ℝ => d1 p.1 p.2 π) := by
  simp_rw [d1_pi_eq]
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have : Continuous (fun p : (ℝ × ℝ) × ℝ => r1 p.1.1 p.1.2 p.2) :=
    continuous_r1.comp (by fun_prop :
      Continuous (fun p : (ℝ × ℝ) × ℝ => (p.1.1, p.1.2, p.2)))
  exact (by fun_prop : Continuous (fun p : (ℝ × ℝ) × ℝ =>
    (2 * p.1.2 * Real.cos (2 * p.2) - p.1.1))).mul this


private lemma continuous_r1_of (a Q : ℝ) : Continuous (r1 a Q) :=
  continuous_r1.comp (by fun_prop : Continuous (fun x : ℝ => (a, Q, x)))
private lemma continuous_r2_of (a Q : ℝ) : Continuous (r2 a Q) :=
  continuous_r2.comp (by fun_prop : Continuous (fun x : ℝ => (a, Q, x)))

/-- Lagrange's identity on `[0, π]` for solutions with parameters `a` and `a'`. -/
private lemma integral_cross {a a' Q : ℝ} {y y' z z' : ℝ → ℝ}
    (hy : ∀ x, HasDerivAt y (y' x) x)
    (hy' : ∀ x, HasDerivAt y' ((2 * Q * Real.cos (2 * x) - a) * y x) x)
    (hz : ∀ x, HasDerivAt z (z' x) x)
    (hz' : ∀ x, HasDerivAt z' ((2 * Q * Real.cos (2 * x) - a') * z x) x) :
    (a' - a) * ∫ x in (0 : ℝ)..π, z x * y x =
      (z π * y' π - z' π * y π) - (z 0 * y' 0 - z' 0 * y 0) := by
  have hc : Continuous (fun x => (a' - a) * (z x * y x)) := by
    have := continuous_iff_continuousAt.2 fun x => (hz x).continuousAt
    have := continuous_iff_continuousAt.2 fun x => (hy x).continuousAt
    fun_prop
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => z x * y' x - z' x * y x)
    (fun x _ => ?_) (hc.intervalIntegrable _ _)
  convert ((hz x).mul (hy' x)).sub ((hz' x).mul (hy x)) using 1
  ring

/-- The coefficient in the difference formula for `w_I(π; a, Q)`. -/
private def gfun (a a' Q : ℝ) : ℝ :=
  -r2 a' Q π * (∫ x in (0 : ℝ)..π, r1 a' Q x * r1 a Q x) +
    r1 a' Q π * ((∫ x in (0 : ℝ)..π, r2 a' Q x * r1 a Q x) -
      ∫ x in (0 : ℝ)..π, r1 a' Q x * r2 a Q x) +
    d1 a' Q π * ∫ x in (0 : ℝ)..π, r2 a' Q x * r2 a Q x

/-- **Difference formula**: `w_I(π; a', Q) - w_I(π; a, Q) = (a' - a) g(a, a', Q) / 2`. -/
private lemma r1_pi_sub (a a' Q : ℝ) :
    r1 a' Q π - r1 a Q π = (a' - a) * gfun a a' Q / 2 := by
  have h11 := integral_cross (hasDerivAt_r1 a Q) (hasDerivAt_d1 a Q) (hasDerivAt_r1 a' Q)
    (hasDerivAt_d1 a' Q)
  have h12 := integral_cross (hasDerivAt_r2 a Q) (hasDerivAt_d2 a Q) (hasDerivAt_r1 a' Q)
    (hasDerivAt_d1 a' Q)
  have h21 := integral_cross (hasDerivAt_r1 a Q) (hasDerivAt_d1 a Q) (hasDerivAt_r2 a' Q)
    (hasDerivAt_d2 a' Q)
  have h22 := integral_cross (hasDerivAt_r2 a Q) (hasDerivAt_d2 a Q) (hasDerivAt_r2 a' Q)
    (hasDerivAt_d2 a' Q)
  simp only [r1_zero, d1_zero, r2_zero, d2_zero] at h11 h12 h21 h22
  have hW := wronskian_real a' Q π
  have hs := d2_pi a Q
  have hs' := d2_pi a' Q
  rw [hs] at h12 h22
  rw [hs'] at h21 h22 hW
  unfold gfun
  linear_combination (r2 a' Q π * h11 - r1 a' Q π * h21 + r1 a' Q π * h12
    - d1 a' Q π * h22) / 2 + r1 a Q π * hW


private lemma continuous_integral_prod {f g : ℝ → ℝ → ℝ → ℝ}
    (hf : Continuous (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2))
    (hg : Continuous (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)) :
    Continuous (fun p : ℝ × ℝ × ℝ => ∫ x in (0 : ℝ)..π, f p.2.1 p.2.2 x * g p.1 p.2.2 x) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have h1 : Continuous (fun p : (ℝ × ℝ × ℝ) × ℝ => f p.1.2.1 p.1.2.2 p.2) :=
    hf.comp (by fun_prop : Continuous (fun p : (ℝ × ℝ × ℝ) × ℝ => (p.1.2.1, p.1.2.2, p.2)))
  have h2 : Continuous (fun p : (ℝ × ℝ × ℝ) × ℝ => g p.1.1 p.1.2.2 p.2) :=
    hg.comp (by fun_prop : Continuous (fun p : (ℝ × ℝ × ℝ) × ℝ => (p.1.1, p.1.2.2, p.2)))
  exact h1.mul h2

private lemma continuous_gfun : Continuous (fun p : ℝ × ℝ × ℝ => gfun p.1 p.2.1 p.2.2) := by
  have e1 : Continuous (fun p : ℝ × ℝ × ℝ => r1 p.2.1 p.2.2 π) :=
    continuous_r1.comp (by fun_prop : Continuous (fun p : ℝ × ℝ × ℝ => (p.2.1, p.2.2, π)))
  have e2 : Continuous (fun p : ℝ × ℝ × ℝ => r2 p.2.1 p.2.2 π) :=
    continuous_r2.comp (by fun_prop : Continuous (fun p : ℝ × ℝ × ℝ => (p.2.1, p.2.2, π)))
  have e3 : Continuous (fun p : ℝ × ℝ × ℝ => d1 p.2.1 p.2.2 π) :=
    continuous_d1_pi.comp (by fun_prop : Continuous (fun p : ℝ × ℝ × ℝ => (p.2.1, p.2.2)))
  have i11 := continuous_integral_prod continuous_r1 continuous_r1
  have i12 := continuous_integral_prod continuous_r1 continuous_r2
  have i21 := continuous_integral_prod continuous_r2 continuous_r1
  have i22 := continuous_integral_prod continuous_r2 continuous_r2
  unfold gfun
  exact ((e2.neg.mul i11).add (e1.mul (i21.sub i12))).add (e3.mul i22)

/-- The derivative of `a ↦ w_I(π; a, Q)` is `g(a, a, Q) / 2`. -/
private lemma hasDerivAt_r1_pi (a Q : ℝ) :
    HasDerivAt (fun a => r1 a Q π) (gfun a a Q / 2) a := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hc : Tendsto (fun a' => gfun a a' Q / 2) (𝓝[≠] a) (𝓝 (gfun a a Q / 2)) := by
    have : Continuous (fun a' => gfun a a' Q / 2) :=
      (continuous_gfun.comp (by fun_prop : Continuous (fun a' : ℝ => (a, a', Q)))).div_const _
    exact this.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine hc.congr' (eventually_nhdsWithin_of_forall fun a' ha' => ?_)
  have hne : a' - a ≠ 0 := sub_ne_zero.mpr ha'
  rw [slope_def_field, r1_pi_sub]
  field_simp

/-- At a root of `w_I(π; a, Q) = c₀` with `|c₀| < 1`, the derivative `g(a, a, Q)` does not
vanish. -/
private lemma gfun_ne_zero {a Q c₀ : ℝ} (hc : |c₀| < 1) (h : r1 a Q π = c₀) :
    gfun a a Q ≠ 0 := by
  have hW := wronskian_real a Q π
  rw [d2_pi, h] at hW
  have hBC : r2 a Q π * d1 a Q π < 0 := by
    have : c₀ ^ 2 < 1 := by
      have := abs_lt.mp hc; nlinarith
    nlinarith
  have hI11 : 0 < ∫ x in (0 : ℝ)..π, r1 a Q x * r1 a Q x := by
    have hcont : Continuous (fun x => r1 a Q x * r1 a Q x) :=
      (continuous_r1_of a Q).mul (continuous_r1_of a Q)
    rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae'
      (MeasureTheory.ae_of_all _ fun x => mul_self_nonneg _) (hcont.intervalIntegrable _ _)]
    refine ⟨Real.pi_pos, ?_⟩
    have hopen : IsOpen (Function.support fun x => r1 a Q x * r1 a Q x) :=
      hcont.isOpen_support
    have h0 : (0 : ℝ) ∈ Function.support fun x => r1 a Q x * r1 a Q x := by
      simp [r1_zero]
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 h0
    have hsub : Ioo 0 (min ε π) ⊆ (Function.support fun x => r1 a Q x * r1 a Q x) ∩ Ioc 0 π := by
      intro x hx
      refine ⟨hball ?_, hx.1, hx.2.le.trans (min_le_right _ _)⟩
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx.1]
      exact hx.2.trans_le (min_le_left _ _)
    refine lt_of_lt_of_le ?_ (MeasureTheory.measure_mono hsub)
    simpa using ⟨hε, Real.pi_pos⟩
  have hI22 : 0 ≤ ∫ x in (0 : ℝ)..π, r2 a Q x * r2 a Q x :=
    intervalIntegral.integral_nonneg Real.pi_pos.le fun x _ => mul_self_nonneg _
  unfold gfun
  have hsym : (∫ x in (0 : ℝ)..π, r2 a Q x * r1 a Q x) =
      ∫ x in (0 : ℝ)..π, r1 a Q x * r2 a Q x := by
    simp_rw [mul_comm (r2 a Q _)]
  rw [hsym, sub_self, mul_zero, add_zero]
  rcases lt_or_gt_of_ne (show r2 a Q π ≠ 0 by rintro h0; rw [h0] at hBC; simp at hBC) with hB | hB
  · have hC : 0 < d1 a Q π := by nlinarith
    have := mul_pos (neg_pos.mpr hB) hI11
    have := mul_nonneg hC.le hI22
    linarith
  · have hC : d1 a Q π < 0 := by nlinarith
    have := mul_pos hB hI11
    have := mul_nonpos_of_nonpos_of_nonneg hC.le hI22
    linarith


/-- `((π / 2 : ℝ) : ℂ) = π / 2`. -/
private lemma ofReal_pi_div_two' : ((π / 2 : ℝ) : ℂ) = (π : ℂ) / 2 := by push_cast; ring

/-- DLMF 28.2.11 on the real axis. -/
private lemma r1_pi_add_one (a Q : ℝ) : r1 a Q π + 1 = 2 * r1 a Q (π / 2) * d2 a Q (π / 2) := by
  have h := mathieuWI_pi_add_one a Q
  rw [← ofReal_pi_div_two', r1_real, d2_real, r1_real] at h
  exact_mod_cast h

/-- DLMF 28.2.10 on the real axis. -/
private lemma r1_pi_sub_one (a Q : ℝ) : r1 a Q π - 1 = 2 * d1 a Q (π / 2) * r2 a Q (π / 2) := by
  have h := mathieuWI_pi_sub_one a Q
  rw [← ofReal_pi_div_two', r1_real, d1_real, r2_real] at h
  exact_mod_cast h

/-- For `a < -(2|Q| + 1)` the product `y y'` of a solution is monotone. -/
private lemma monotone_mul_deriv {a Q : ℝ} (ha : a < -(2 * |Q| + 1)) {y y' : ℝ → ℝ}
    (hy : ∀ x, HasDerivAt y (y' x) x)
    (hy' : ∀ x, HasDerivAt y' ((2 * Q * Real.cos (2 * x) - a) * y x) x) :
    Monotone (fun x => y x * y' x) := by
  have hd : ∀ x, HasDerivAt (fun x => y x * y' x)
      (y' x * y' x + y x * ((2 * Q * Real.cos (2 * x) - a) * y x)) x :=
    fun x => (hy x).mul (hy' x)
  refine monotone_of_deriv_nonneg (fun x => (hd x).differentiableAt) fun x => ?_
  rw [(hd x).deriv]
  have hc : -|Q| ≤ Q * Real.cos (2 * x) := by
    have h1 := Real.abs_cos_le_one (2 * x)
    have h2 : |Q * Real.cos (2 * x)| ≤ |Q| := by
      rw [abs_mul]; nlinarith [abs_nonneg Q, abs_nonneg (Real.cos (2 * x))]
    linarith [(abs_le.mp h2).1]
  have hpos : 0 ≤ 2 * Q * Real.cos (2 * x) - a := by nlinarith
  nlinarith [mul_self_nonneg (y' x), mul_nonneg hpos (mul_self_nonneg (y x))]

/-- **No roots far to the left**: for `a < -(2|Q| + 1)`, `w_I(π; a, Q) ≠ c₀` when `|c₀| < 1`. -/
private lemma r1_pi_ne_of_lt {a Q c₀ : ℝ} (hc : |c₀| < 1) (ha : a < -(2 * |Q| + 1)) :
    r1 a Q π ≠ c₀ := by
  intro h
  have m1 := monotone_mul_deriv ha (hasDerivAt_r1 a Q) (hasDerivAt_d1 a Q)
    (show (0 : ℝ) ≤ π / 2 by positivity)
  have m2 := monotone_mul_deriv ha (hasDerivAt_r2 a Q) (hasDerivAt_d2 a Q)
    (show (0 : ℝ) ≤ π / 2 by positivity)
  simp only [r1_zero, d1_zero, r2_zero, d2_zero, mul_zero, zero_mul] at m1 m2
  have e1 := r1_pi_add_one a Q
  have e2 := r1_pi_sub_one a Q
  rw [h] at e1 e2
  have hc2 : (c₀ + 1) * (c₀ - 1) < 0 := by
    have := abs_lt.mp hc; nlinarith
  rw [e1, e2] at hc2
  nlinarith [mul_nonneg m1 m2]

/-- The bound `|2 Q cos 2x| ≤ 2|Q| + 1`. -/
private lemma abs_pot_le (Q : ℝ) :
    ∀ x ∈ Icc (0 : ℝ) (π / 2), |2 * Q * Real.cos (2 * x)| ≤ 2 * |Q| + 1 := by
  intro x _
  rw [abs_mul, abs_mul, abs_two]
  have := Real.abs_cos_le_one (2 * x)
  nlinarith [abs_nonneg Q]

/-- A continuous function taking both signs beyond every bound has zeros beyond every bound. -/
private lemma exists_gt_zero_of_sign_changes {f : ℝ → ℝ} (hf : Continuous f)
    (hp : ∀ N, ∃ μ > N, 0 < f μ) (hn : ∀ N, ∃ μ > N, f μ < 0) (N : ℝ) :
    ∃ μ > N, f μ = 0 := by
  obtain ⟨μ₁, h₁, f₁⟩ := hp N
  obtain ⟨μ₂, h₂, f₂⟩ := hn N
  obtain ⟨c, hc, hfc⟩ := intermediate_value_uIcc (a := μ₁) (b := μ₂) hf.continuousOn
    (show (0 : ℝ) ∈ uIcc (f μ₁) (f μ₂) from ⟨by simp [f₂.le], by simp [f₁.le]⟩)
  refine ⟨c, lt_of_lt_of_le (lt_min h₁ h₂) hc.1, hfc⟩

private lemma continuous_r1_a (Q x : ℝ) : Continuous (fun a : ℝ => r1 a Q x) :=
  continuous_r1.comp (by fun_prop : Continuous (fun a : ℝ => (a, Q, x)))

private lemma continuous_d1_a (Q x : ℝ) : Continuous (fun a : ℝ => d1 a Q x) :=
  Complex.continuous_re.comp (((famI Q).2.2.2 x).2.continuous.comp Complex.continuous_ofReal)

/-- `w_I(π; a, Q) = 1` for arbitrarily large `a`. -/
private lemma exists_gt_r1_pi_eq_one (Q N : ℝ) : ∃ a > N, r1 a Q π = 1 := by
  have hs := ODE.sign_changes_deriv_initial_one_zero (Q := fun x => 2 * Q * Real.cos (2 * x))
    (Y := fun a x => r1 a Q x) (Y' := fun a x => d1 a Q x) (L := π / 2)
    (by positivity : (0 : ℝ) < 2 * |Q| + 1) (by positivity) (abs_pot_le Q)
    (fun a x => hasDerivAt_r1 a Q x) (fun a x => hasDerivAt_d1 a Q x) (fun a => r1_zero a Q)
    (fun a => d1_zero a Q)
  obtain ⟨a, ha, h0⟩ := exists_gt_zero_of_sign_changes (continuous_d1_a Q (π / 2)) hs.1 hs.2 N
  refine ⟨a, ha, ?_⟩
  have := r1_pi_sub_one a Q
  rw [h0] at this
  linarith

/-- `w_I(π; a, Q) = -1` for arbitrarily large `a`. -/
private lemma exists_gt_r1_pi_eq_neg_one (Q N : ℝ) : ∃ a > N, r1 a Q π = -1 := by
  have hs := ODE.sign_changes_val_initial_one_zero (Q := fun x => 2 * Q * Real.cos (2 * x))
    (Y := fun a x => r1 a Q x) (Y' := fun a x => d1 a Q x) (L := π / 2)
    (by positivity : (0 : ℝ) < 2 * |Q| + 1) (by positivity) (abs_pot_le Q)
    (fun a x => hasDerivAt_r1 a Q x) (fun a x => hasDerivAt_d1 a Q x) (fun a => r1_zero a Q)
    (fun a => d1_zero a Q)
  obtain ⟨a, ha, h0⟩ := exists_gt_zero_of_sign_changes (continuous_r1_a Q (π / 2)) hs.1 hs.2 N
  refine ⟨a, ha, ?_⟩
  have := r1_pi_add_one a Q
  rw [h0] at this
  linarith


/-! ### The family `t ↦ w_I(π; ·, t q) - c₀` -/

/-- The family whose zeros are the roots along the segment. -/
private def Yf (q c₀ t a : ℝ) : ℝ := r1 a (t * q) π - c₀
/-- Its derivative in `a`. -/
private def Yd (q t a : ℝ) : ℝ := gfun a a (t * q) / 2

private lemma continuousOn_Yf (q c₀ : ℝ) :
    ContinuousOn (Function.uncurry (Yf q c₀)) (univ ×ˢ univ) := by
  refine Continuous.continuousOn ?_
  have : Continuous (fun p : ℝ × ℝ => r1 p.2 (p.1 * q) π) :=
    continuous_r1.comp (by fun_prop : Continuous (fun p : ℝ × ℝ => (p.2, p.1 * q, π)))
  exact this.sub continuous_const

private lemma continuousOn_Yd (q : ℝ) :
    ContinuousOn (Function.uncurry (Yd q)) (univ ×ˢ univ) := by
  refine Continuous.continuousOn ?_
  exact (continuous_gfun.comp (by fun_prop :
    Continuous (fun p : ℝ × ℝ => (p.2, p.2, p.1 * q)))).div_const _

private lemma hasDerivAt_Yf (q c₀ : ℝ) :
    ∀ t ∈ (univ : Set ℝ), ∀ x ∈ (univ : Set ℝ), HasDerivAt (Yf q c₀ t) (Yd q t x) x :=
  fun t _ x _ => (hasDerivAt_r1_pi x (t * q)).sub_const c₀

private lemma Yd_ne_zero {q c₀ : ℝ} (hc : |c₀| < 1) :
    ∀ t ∈ (univ : Set ℝ), ∀ x ∈ (univ : Set ℝ), Yf q c₀ t x = 0 → Yd q t x ≠ 0 := by
  intro t _ x _ h
  exact div_ne_zero (gfun_ne_zero hc (sub_eq_zero.mp h)) two_ne_zero

private lemma Yf_ne_zero_of_lt {q c₀ t a : ℝ} (hc : |c₀| < 1) (ha : a < -(2 * |t * q| + 1)) :
    Yf q c₀ t a ≠ 0 :=
  sub_ne_zero.mpr (r1_pi_ne_of_lt hc ha)

/-- The roots along the segment can be enumerated in increasing order. -/
private lemma exists_nth_root (q c₀ t : ℝ) (hc : |c₀| < 1) (k : ℕ) :
    ∃ x ∈ {a | Yf q c₀ t a = 0}, ({a | Yf q c₀ t a = 0} ∩ Iio x).encard = k := by
  refine ODE.exists_zero_encard_inter_Iio_eq (G := fun μ => mathieuWI μ ((t * q : ℝ) : ℂ) π - c₀)
    (((famI (t * q)).2.2.2 π).1.sub_const _) (fun x => ?_)
    ⟨-(2 * |t * q| + 1), fun x hx => Yf_ne_zero_of_lt hc hx⟩ (fun N => ?_) (fun N => ?_) k
  · simp only [Yf]; rw [r1_real]; push_cast; ring
  · obtain ⟨a, ha, h⟩ := exists_gt_r1_pi_eq_one (t * q) N
    exact ⟨a, ha, by simp only [Yf, h]; linarith [(abs_lt.mp hc).2]⟩
  · obtain ⟨a, ha, h⟩ := exists_gt_r1_pi_eq_neg_one (t * q) N
    exact ⟨a, ha, by simp only [Yf, h]; linarith [(abs_lt.mp hc).1]⟩

/-- The `k`-th root along the segment. -/
private def branch (q c₀ : ℝ) (k : ℕ) (t : ℝ) : ℝ := nthLeast {a | Yf q c₀ t a = 0} k

private lemma branch_spec {q c₀ : ℝ} (hc : |c₀| < 1) (k : ℕ) (t : ℝ) :
    branch q c₀ k t ∈ {a | Yf q c₀ t a = 0} ∧
      ({a | Yf q c₀ t a = 0} ∩ Iio (branch q c₀ k t)).encard = k :=
  nthLeast_spec (exists_nth_root q c₀ t hc k)

/-- Uniform lower bound for the roots near `t₀`. -/
private lemma eventually_Yf_ne_zero (q c₀ t₀ : ℝ) (hc : |c₀| < 1) :
    ∀ᶠ t in 𝓝 t₀, ∀ a, a < -(2 * (|t₀ * q| + |q|) + 1) → Yf q c₀ t a ≠ 0 := by
  filter_upwards [Metric.ball_mem_nhds t₀ one_pos] with t ht a ha
  refine Yf_ne_zero_of_lt hc (lt_of_lt_of_le ha ?_)
  have h1 : |t - t₀| ≤ 1 := by rw [Metric.mem_ball, Real.dist_eq] at ht; exact ht.le
  have : |t * q| ≤ |t₀ * q| + |q| := by
    calc |t * q| = |t₀ * q + (t - t₀) * q| := by ring_nf
      _ ≤ |t₀ * q| + |(t - t₀) * q| := abs_add_le _ _
      _ ≤ |t₀ * q| + |q| := by
        rw [abs_mul (t - t₀)]; nlinarith [abs_nonneg q, abs_nonneg (t - t₀)]
  linarith

/-- **Continuity of the `k`-th root**. -/
private lemma continuous_branch {q c₀ : ℝ} (hc : |c₀| < 1) (k : ℕ) :
    Continuous (branch q c₀ k) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  obtain ⟨hz, hzk⟩ := branch_spec hc k t₀
  set z := branch q c₀ k t₀ with hzdef
  set A := -(2 * (|t₀ * q| + |q|) + 1) - 1 with hA
  have hlow := eventually_Yf_ne_zero q c₀ t₀ hc
  have hz1 : A + 1 ≤ z := by
    by_contra h
    exact hlow.self_of_nhds z (by linarith) hz
  obtain ⟨δ₀, hδ₀, hloc⟩ := ODE.sturmDef_local isOpen_univ isOpen_univ (continuousOn_Yf q c₀)
    (continuousOn_Yd q) (hasDerivAt_Yf q c₀) (mem_univ t₀) (mem_univ z) hz
    (Yd_ne_zero hc t₀ (mem_univ _) z (mem_univ _) hz)
  have hwin : ∀ x ∈ Ioo (z - δ₀) (z + δ₀), Yf q c₀ t₀ x = 0 → x = z := by
    obtain ⟨y, -, hy⟩ := (hloc δ₀ hδ₀ le_rfl).self_of_nhds
    intro x hx hx0
    rw [hy x ⟨hx, hx0⟩, hy z ⟨⟨by linarith, by linarith⟩, hz⟩]
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  set δ := min (min (δ₀ / 2) (1 / 2)) ε with hδ
  have hδp : 0 < δ := lt_min (lt_min (by linarith) (by norm_num)) hε
  have hδ₀' : δ < δ₀ := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) (by linarith)
  have hδ1 : δ ≤ 1 / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hδε : δ ≤ ε := min_le_right _ _
  have hA0 : Yf q c₀ t₀ A ≠ 0 := hlow.self_of_nhds A (by linarith)
  have hb0 : Yf q c₀ t₀ (z - δ) ≠ 0 := by
    intro h
    have := hwin (z - δ) ⟨by linarith, by linarith⟩ h
    linarith
  have hcount := ODE.sturmDef_eventually_ncard_eq isOpen_univ isOpen_univ (subset_univ _)
    (continuousOn_Yf q c₀) (continuousOn_Yd q) (hasDerivAt_Yf q c₀) (Yd_ne_zero hc)
    (mem_univ t₀) hA0 hb0
  have hset0 : {x | x ∈ Icc A (z - δ) ∧ Yf q c₀ t₀ x = 0} = {a | Yf q c₀ t₀ a = 0} ∩ Iio z := by
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_Icc, mem_Iio]
    constructor
    · rintro ⟨⟨-, hx⟩, hx0⟩; exact ⟨hx0, by linarith⟩
    · rintro ⟨hx0, hxz⟩
      refine ⟨⟨?_, ?_⟩, hx0⟩
      · by_contra h; exact hlow.self_of_nhds x (by linarith) hx0
      · by_contra h
        have := hwin x ⟨by linarith, by linarith⟩ hx0
        linarith
  have hk0 : ({x | x ∈ Icc A (z - δ) ∧ Yf q c₀ t₀ x = 0}).ncard = k := by
    rw [hset0]
    have := (Set.finite_of_encard_eq_coe hzk).cast_ncard_eq
    rw [hzk] at this
    exact_mod_cast this
  filter_upwards [hcount, hloc δ hδp hδ₀'.le, hlow] with t hct hut hlt
  obtain ⟨x, ⟨hxw, hx0⟩, hxu⟩ := hut
  have hfin : ({y | y ∈ Icc A (z - δ) ∧ Yf q c₀ t y = 0}).Finite :=
    ODE.sturmDef_finite (fun y _ => hasDerivAt_Yf q c₀ t (mem_univ _) y (mem_univ _))
      fun y _ => Yd_ne_zero hc t (mem_univ _) y (mem_univ _)
  have hsetx : {a | Yf q c₀ t a = 0} ∩ Iio x = {y | y ∈ Icc A (z - δ) ∧ Yf q c₀ t y = 0} := by
    ext y
    simp only [mem_ofPred_eq, mem_inter_iff, mem_Icc, mem_Iio]
    constructor
    · rintro ⟨hy0, hyx⟩
      refine ⟨⟨?_, ?_⟩, hy0⟩
      · by_contra h; exact hlt y (by linarith) hy0
      · by_contra h
        have := hxu y ⟨⟨by linarith, by linarith [hxw.2]⟩, hy0⟩
        linarith
    · rintro ⟨⟨-, hy⟩, hy0⟩; exact ⟨hy0, by linarith [hxw.1]⟩
  have hbx : branch q c₀ k t = x := by
    refine nthLeast_eq_of hx0 ?_
    rw [hsetx, ← hfin.cast_ncard_eq, hct, hk0]
  rw [hbx, Real.dist_eq, abs_lt]
  constructor <;> linarith [hxw.1, hxw.2]


/-- **Local uniqueness of continuous root paths**. -/
private lemma eqOn_of_Yf {q c₀ : ℝ} (hc : |c₀| < 1) {Λ₁ Λ₂ : ℝ → ℝ}
    (h₁ : ContinuousOn Λ₁ (Icc 0 1)) (h₂ : ContinuousOn Λ₂ (Icc 0 1)) (h0 : Λ₁ 0 = Λ₂ 0)
    (hr₁ : ∀ t ∈ Icc (0 : ℝ) 1, Yf q c₀ t (Λ₁ t) = 0)
    (hr₂ : ∀ t ∈ Icc (0 : ℝ) 1, Yf q c₀ t (Λ₂ t) = 0) :
    EqOn Λ₁ Λ₂ (Icc 0 1) := by
  have hcl : IsClosed ({t | Λ₁ t = Λ₂ t} ∩ Icc 0 1) := by
    have := (h₁.sub h₂).preimage_isClosed_of_isClosed isClosed_Icc (isClosed_singleton (x := 0))
    convert this using 1
    ext t; simp [sub_eq_zero, and_comm]
  intro t ht
  refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin hcl h0 (fun x hx => ?_) ht
  obtain ⟨hxe, hx01⟩ := hx
  have hxI : x ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self hx01
  set z := Λ₁ x
  obtain ⟨δ₀, hδ₀, hloc⟩ := ODE.sturmDef_local isOpen_univ isOpen_univ (continuousOn_Yf q c₀)
    (continuousOn_Yd q) (hasDerivAt_Yf q c₀) (mem_univ x) (mem_univ z) (hr₁ x hxI)
    (Yd_ne_zero hc x (mem_univ _) z (mem_univ _) (hr₁ x hxI))
  have hIcc : Icc (0 : ℝ) 1 ∈ 𝓝[>] x :=
    mem_of_superset (Ico_mem_nhdsGT hx01.2) fun y hy => ⟨hx01.1.trans hy.1, hy.2.le⟩
  have hle : 𝓝[>] x ≤ 𝓝[Icc 0 1] x := nhdsWithin_le_of_mem hIcc
  have hwin : Ioo (z - δ₀) (z + δ₀) ∈ 𝓝 z := Ioo_mem_nhds (by linarith) (by linarith)
  have e₁ : ∀ᶠ t in 𝓝[>] x, Λ₁ t ∈ Ioo (z - δ₀) (z + δ₀) := hle ((h₁ x hxI).tendsto hwin)
  have e₂ : ∀ᶠ t in 𝓝[>] x, Λ₂ t ∈ Ioo (z - δ₀) (z + δ₀) := by
    have hxe' : Λ₂ x = z := hxe.symm
    have := (h₂ x hxI).tendsto
    rw [hxe'] at this
    exact hle (this hwin)
  filter_upwards [e₁, e₂, hIcc, nhdsWithin_le_nhds (hloc δ₀ hδ₀ le_rfl)] with t ht₁ ht₂ ht hu
  obtain ⟨y, -, hy⟩ := hu
  exact (hy _ ⟨ht₁, hr₁ t ht⟩).trans (hy _ ⟨ht₂, hr₂ t ht⟩).symm

/-- **Continuation of a root of `w_I(π; a, q) = c₀` along the segment `[0, q]`**: for
`|c₀| < 1` and a root `a₀` at `q = 0`, there is a continuous `Λ` with `Λ 0 = a₀` and
`w_I(π; Λ t, t q) = c₀` for every real `t`. -/
theorem exists_continuous_re_mathieuWI_pi_eq {q c₀ a₀ : ℝ} (hc : |c₀| < 1)
    (h₀ : (mathieuWI a₀ 0 π).re = c₀) :
    ∃ Λ : ℝ → ℝ, Continuous Λ ∧ Λ 0 = a₀ ∧
      ∀ t : ℝ, (mathieuWI (Λ t) ((t * q : ℝ) : ℂ) π).re = c₀ := by
  have hroot : Yf q c₀ 0 a₀ = 0 := by simp [Yf, r1, h₀]
  have hfin : ({a | Yf q c₀ 0 a = 0} ∩ Iio a₀).Finite := by
    refine (ODE.sturmDef_finite (a := -(2 * |0 * q| + 1) - 1) (b := a₀)
      (fun y _ => hasDerivAt_Yf q c₀ 0 (mem_univ _) y (mem_univ _))
      fun y _ => Yd_ne_zero hc 0 (mem_univ _) y (mem_univ _)).subset ?_
    rintro y ⟨hy0, hya⟩
    refine ⟨⟨?_, (mem_Iio.mp hya).le⟩, hy0⟩
    by_contra h
    exact Yf_ne_zero_of_lt hc (by linarith) hy0
  set k := ({a | Yf q c₀ 0 a = 0} ∩ Iio a₀).ncard
  refine ⟨branch q c₀ k, continuous_branch hc k, ?_, fun t => ?_⟩
  · exact nthLeast_eq_of hroot hfin.cast_ncard_eq.symm
  · have := (branch_spec (q := q) hc k t).1
    simp only [mem_ofPred_eq, Yf, r1, sub_eq_zero] at this
    exact this

/-- **Uniqueness of the continuation**: two continuous paths of roots of
`w_I(π; a, t q) = c₀`, `|c₀| < 1`, on `[0, 1]` with the same initial value coincide. -/
theorem eqOn_of_re_mathieuWI_pi_eq {q c₀ : ℝ} (hc : |c₀| < 1) {Λ₁ Λ₂ : ℝ → ℝ}
    (h₁ : ContinuousOn Λ₁ (Icc 0 1)) (h₂ : ContinuousOn Λ₂ (Icc 0 1)) (h0 : Λ₁ 0 = Λ₂ 0)
    (hr₁ : ∀ t ∈ Icc (0 : ℝ) 1, (mathieuWI (Λ₁ t) ((t * q : ℝ) : ℂ) π).re = c₀)
    (hr₂ : ∀ t ∈ Icc (0 : ℝ) 1, (mathieuWI (Λ₂ t) ((t * q : ℝ) : ℂ) π).re = c₀) :
    EqOn Λ₁ Λ₂ (Icc 0 1) :=
  eqOn_of_Yf (q := q) hc h₁ h₂ h0 (fun t ht => by simp only [Yf, r1, hr₁ t ht, sub_self])
    (fun t ht => by simp only [Yf, r1, hr₂ t ht, sub_self])

/-! ### Floquet solutions and coefficient sequences for real parameters -/

/-- For real `ν ∉ ℤ`, `|cos πν| < 1`. -/
theorem abs_cos_pi_mul_lt_one {ν : ℝ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) : |Real.cos (π * ν)| < 1 := by
  have hs : Real.sin (π * ν) ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
    refine hν n ?_
    have : (n : ℝ) = ν := by
      have := Real.pi_pos
      field_simp at hn
      linarith
    exact_mod_cast this
  have h1 := Real.sin_sq_add_cos_sq (π * ν)
  have h2 : 0 < Real.sin (π * ν) ^ 2 := by positivity
  rw [abs_lt]
  constructor <;> nlinarith [sq_nonneg (Real.cos (π * ν))]

/-- **An explicit Floquet solution**: if `cos πν = w_I(π; a, q)` and `e^{πiν} ≠ e^{-πiν}`, then
`w_II(π) w_I(z) + (e^{πiν} - w_I(π)) w_II(z)` is a Floquet solution with respect to `ν`. -/
theorem isFloquetSolution_mathieuWII_pi_mul_add {a q ν : ℂ}
    (hμ : Complex.exp (π * I * ν) ≠ (Complex.exp (π * I * ν))⁻¹) (hc : IsMathieuCharExp a q ν) :
    IsFloquetSolution a q ν (fun z => mathieuWII a q π * mathieuWI a q z +
      (Complex.exp (π * I * ν) - mathieuWI a q π) * mathieuWII a q z) := by
  set μ := Complex.exp (π * I * ν) with hμdef
  set D := mathieuWI a q π
  set B := mathieuWII a q π
  have h1 := isMathieuSolution_mathieuWI a q
  have h2 := isMathieuSolution_mathieuWII a q
  have hμ0 : μ ≠ 0 := Complex.exp_ne_zero _
  have hcos : 2 * D * μ = μ ^ 2 + 1 := by
    have e : Complex.cos (π * ν) = (μ + μ⁻¹) / 2 := by
      rw [Complex.cos, show (π : ℂ) * ν * I = π * I * ν by ring,
        show -((π : ℂ) * ν) * I = -(π * I * ν) by ring, Complex.exp_neg]
    have := hc
    unfold IsMathieuCharExp at this
    rw [e] at this
    have hD : D = (μ + μ⁻¹) / 2 := this.symm
    rw [hD]
    field_simp
  have hW := (h1.const_mul B).add (h2.const_mul (μ - D))
  have hwr := mathieuWI_wronskian a q π
  have hsym := mathieuWI_pi_eq_deriv_mathieuWII_pi a q
  have hd0 : deriv (fun z => B * mathieuWI a q z + (μ - D) * mathieuWII a q z) 0 = μ - D := by
    rw [deriv_const_mul_add_const_mul (h1.differentiable 0) (h2.differentiable 0),
      deriv_mathieuWI_apply_zero, deriv_mathieuWII_apply_zero]
    ring
  refine ⟨hW, fun h0 => ?_, fun z => ?_⟩
  · have : μ - D = 0 := by
      rw [← hd0, h0]; simp
    have hμ2 : μ * μ = 1 := by
      have hD : D = μ := (sub_eq_zero.mp this).symm
      rw [hD] at hcos
      linear_combination hcos
    exact hμ (eq_inv_of_mul_eq_one_left hμ2)
  · have key := hW.comp_add_pi.eq_of_initial (hW.const_mul μ) (z₀ := 0)
      (by simp only [zero_add, mathieuWI_apply_zero, mathieuWII_apply_zero]; ring)
      (by
        have hsh := deriv_comp_add_const
          (f := fun z => B * mathieuWI a q z + (μ - D) * mathieuWII a q z) (a := (π : ℂ)) (x := 0)
        simp only [zero_add] at hsh
        rw [hsh, deriv_const_mul _ (hW.differentiable 0), hd0,
          deriv_const_mul_add_const_mul (h1.differentiable _) (h2.differentiable _), ← hsym]
        rw [← hsym] at hwr
        linear_combination -hwr + hcos)
    exact congrFun key z

/-- **Reality of the eigenvalue** for real `ν`, `q`: if the recurrence 28.14.4 has an absolutely
summable solution with `∑ c_m² = 1`, then `a` is real (the recurrence is symmetric). -/
theorem im_eq_zero_of_isMeCoeffSeq {ν q : ℝ} {a : ℂ} {c : ℤ → ℂ}
    (h : IsMeCoeffSeq ν q a c) : a.im = 0 := by
  obtain ⟨hrec, hs, hsq⟩ := h
  have hB : ∀ m, ‖c m‖ ≤ ∑' m, ‖c m‖ := fun m => hs.le_tsum m (fun j _ => norm_nonneg _)
  set B := ∑' m, ‖c m‖
  set T : ℤ → ℂ := fun m => (q : ℂ) * (c (m + 1) * conj (c m) - c m * conj (c (m + 1)))
  have hT : Summable T := by
    refine Summable.of_norm_bounded (g := fun m => 2 * |q| * B * ‖c m‖)
      (hs.mul_left _) fun m => ?_
    simp only [T, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have e1 : ‖c (m + 1) * conj (c m) - c m * conj (c (m + 1))‖ ≤ 2 * B * ‖c m‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
      nlinarith [hB (m + 1), norm_nonneg (c m), norm_nonneg (c (m + 1))]
    nlinarith [abs_nonneg q]
  have hT' : HasSum (fun m => T (m - 1)) (∑' m, T m) :=
    (Equiv.subRight (1 : ℤ)).hasSum_iff.mpr hT.hasSum
  have hdiff : HasSum (fun m => T m - T (m - 1)) 0 := by
    simpa using hT.hasSum.sub hT'
  have hpt : ∀ m, T m - T (m - 1) = (a - conj a) * ((‖c m‖ ^ 2 : ℝ) : ℂ) := by
    intro m
    have e := hrec m
    have ec := congrArg conj e
    simp only [map_sub, map_add, map_mul, Complex.conj_ofReal, map_pow, map_zero, map_ofNat,
      map_intCast] at ec
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    simp only [T, sub_add_cancel]
    linear_combination conj (c m) * e - c m * ec
  simp only [hpt] at hdiff
  have hsq' : HasSum (fun m => ((‖c m‖ ^ 2 : ℝ) : ℂ)) ((∑' m, ‖c m‖ ^ 2 : ℝ) : ℂ) := by
    have hs2 : Summable (fun m => ‖c m‖ ^ 2) :=
      Summable.of_nonneg_of_le (fun m => by positivity)
        (fun m => by rw [sq]; exact mul_le_mul_of_nonneg_right (hB m) (norm_nonneg _))
        (hs.mul_left B)
    exact_mod_cast hs2.hasSum
  have hpos : 0 < ∑' m, ‖c m‖ ^ 2 := by
    have hne : ∃ m, c m ≠ 0 := by
      by_contra hc
      push Not at hc
      have : HasSum (fun m => c m ^ 2) 0 := by simp [hc]
      exact one_ne_zero (this.unique hsq).symm
    obtain ⟨m, hm⟩ := hne
    have hs2 : Summable (fun m => ‖c m‖ ^ 2) :=
      Summable.of_nonneg_of_le (fun m => by positivity)
        (fun m => by rw [sq]; exact mul_le_mul_of_nonneg_right (hB m) (norm_nonneg _))
        (hs.mul_left B)
    exact hs2.tsum_pos (fun _ => by positivity) m (by positivity)
  have hzero := (hsq'.mul_left (a - conj a)).unique hdiff
  have hne : ((∑' m, ‖c m‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have : a - conj a = 0 := (mul_eq_zero.mp hzero).resolve_right hne
  have := congrArg Complex.im this
  simp [Complex.sub_im, Complex.conj_im] at this
  linarith

end DLMF.Mathieu
