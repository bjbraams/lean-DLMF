/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elementary.Hyperbolic.InverseIdentities
public import DLMF.Gamma.BetaFunction.Cosine
public import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
public import TauCeti.Analysis.SpecialFunctions.Hyperbolic
public import DLMF.Gamma.IntegralRepresentations.DigammaAndBinet
public import DLMF.Gamma.SeriesExpansions

/-!
# Continued fractions and integrals of hyperbolic functions

Convergent continued fractions, antiderivatives and definite integrals of hyperbolic and inverse
hyperbolic functions.

Source references and common attribution are retained in
`DLMF.Elementary.Hyperbolic`.
The hyperbolic tangent difference integral applies Mathlib’s Frullani theorem after
an exponential mean-value bound; continuity uses TauCeti’s `Real.continuous_tanh`.
The exponential over squared-cosh integral specializes the general cosh-power Beta
integral in `DLMF.Gamma.BetaFunction.Cosine` and Mathlib’s Gamma reflection formula.
The sine and hyperbolic-sine kernels use the proved digamma series, special values,
and real digamma integral in the Gamma area; the Laplace sine integral is the imaginary
part of Mathlib’s complex exponential integral.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory

open scoped Real Topology

namespace DLMF.Elementary

/-- Identity under the stated parameter and domain assumptions: `DLMF.HasContinuedFraction (fun n
=> if n=0 then z else z^2) (fun n => (2*n+1:ℂ)) (Complex.tanh z)`. -/
@[dlmf 4.39.E1]
theorem tanh_continued_fraction {z : ℂ} (hz : Complex.cosh z≠0) :
    DLMF.HasContinuedFraction (fun n => if n=0 then z else z^2) (fun n => (2*n+1:ℂ)) (Complex.tanh z) := by
  sorry

/-- Identity under the stated parameter and domain assumptions: `DLMF.HasContinuedFraction (fun n
=> if n=0 then z else ((2*((n+1)/2)-1:ℕ):ℂ)*(2*((n+1)/2):ℂ)*z^2) (fun n => (2*n+1:ℂ)) (arcsinh
z/Complex.sqrt (1+z^2))`. -/
@[dlmf 4.39.E2]
theorem arcsinh_continued_fraction {z : ℂ} (hz : z∈arcsinhDomain) :
    DLMF.HasContinuedFraction
      (fun n => if n=0 then z else ((2*((n+1)/2)-1:ℕ):ℂ)*(2*((n+1)/2):ℂ)*z^2)
      (fun n => (2*n+1:ℂ)) (arcsinh z/Complex.sqrt (1+z^2)) := by
  sorry

/-- Identity under the stated parameter and domain assumptions: `DLMF.HasContinuedFraction (fun n
=> if n=0 then z else -(n:ℂ)^2*z^2) (fun n => (2*n+1:ℂ)) (arctanh z)`. -/
@[dlmf 4.39.E3]
theorem arctanh_continued_fraction {z : ℂ} (hz : z∈arctanhDomain) :
    DLMF.HasContinuedFraction (fun n => if n=0 then z else -(n:ℂ)^2*z^2)
      (fun n => (2*n+1:ℂ)) (arctanh z) := by
  sorry

/-- At `x`, the function `(fun t : ℝ => Real.log (Real.cosh t))` has derivative `(Real.tanh x)`. -/
@[dlmf 4.40.E3]
theorem antiderivative_tanh (x : ℝ) : HasDerivAt (fun t : ℝ => Real.log (Real.cosh t)) (Real.tanh x) x := by
  simpa only [Real.tanh_eq_sinh_div_cosh] using (Real.hasDerivAt_cosh x).log (Real.cosh_pos x).ne'

/-- At `x`, the function `(fun t : ℝ => Real.log (Real.tanh (t/2)))` has derivative `(Real.sinh
x)⁻¹`. -/
@[dlmf 4.40.E4]
theorem antiderivative_csch {x : ℝ} (hx : 0<x) : HasDerivAt (fun t : ℝ => Real.log (Real.tanh (t/2))) (Real.sinh x)⁻¹ x := by
  have hs : 0 < Real.sinh (x/2) := Real.sinh_pos_iff.mpr (by linarith)
  have hc : 0 < Real.cosh (x/2) := Real.cosh_pos _
  have hf : (fun t : ℝ => Real.log (Real.tanh (t/2))) =
      fun t => Real.log (Real.sinh (t/2)/Real.cosh (t/2)) := by
    funext t; rw [Real.tanh_eq_sinh_div_cosh]
  rw [hf]
  have h1 := ((hasDerivAt_id x).div_const 2).sinh
  have h2 := ((hasDerivAt_id x).div_const 2).cosh
  have hd := (h1.div h2 hc.ne').log (div_pos hs hc).ne'
  convert hd using 1
  · rfl
  · dsimp only [id, Pi.div_apply]
    have h2x : Real.sinh x = 2*Real.sinh (x/2)*Real.cosh (x/2) := by
      rw [← Real.sinh_two_mul]; ring_nf
    rw [h2x]
    field_simp
    nlinarith [Real.cosh_sq (x/2)]

/-- At `x`, the function `(fun t : ℝ => 2*Real.arctan (Real.exp t)-π/2)` has derivative
`(Real.cosh x)⁻¹`. -/
@[dlmf 4.40.E5]
theorem antiderivative_sech (x : ℝ) : HasDerivAt (fun t : ℝ => 2*Real.arctan (Real.exp t)-π/2) (Real.cosh x)⁻¹ x := by
  have hd:=((Real.hasDerivAt_exp x).arctan.const_mul 2).sub_const (π/2)
  convert hd using 1
  rw [Real.cosh_eq,Real.exp_neg]
  field_simp <;> ring

/-- At `x`, the function `(fun t : ℝ => Real.log (Real.sinh t))` has derivative `(Real.cosh
x/Real.sinh x)`. -/
@[dlmf 4.40.E6]
theorem antiderivative_coth {x : ℝ} (hx : 0<x) : HasDerivAt (fun t : ℝ => Real.log (Real.sinh t)) (Real.cosh x/Real.sinh x) x := by
  exact (Real.hasDerivAt_sinh x).log (Real.sinh_pos_iff.mpr hx).ne'

/-- The imaginary part of the complex exponential Laplace integral evaluates a damped sine. -/
private lemma laplace_sin {a b : ℝ} (hb : 0<b) :
    IntegrableOn (fun x : ℝ => Real.exp (-b*x)*Real.sin (a*x)) (Ioi 0) ∧
      (∫ x : ℝ in Ioi 0, Real.exp (-b*x)*Real.sin (a*x)) = a/(b^2+a^2) := by
  let c : ℂ := -b+I*a
  have hc : c.re<0 := by dsimp [c]; simpa using neg_neg_of_pos hb
  have hi := integrableOn_exp_mul_complex_Ioi hc 0
  have he : (fun x : ℝ => (Complex.exp (c*x)).im) =
      fun x => Real.exp (-b*x)*Real.sin (a*x) := by
    ext x
    simp [c, Complex.exp_im]
  have him : IntegrableOn (fun x : ℝ => (Complex.exp (c*x)).im) (Ioi 0) := hi.im
  rw [he] at him
  refine ⟨him, ?_⟩
  rw [← he]
  simp only [← RCLike.im_to_complex]
  rw [integral_im hi, integral_exp_mul_complex_Ioi hc]
  simp [c, Complex.div_im, Complex.normSq_apply]
  ring
/-- Integral norms of the exponential-sine terms are bounded by a summable quadratic tail. -/
private lemma exp_sin_term_integral_norm_bound (a : ℝ) (n : ℕ) :
    (∫ x in Ioi (0:ℝ), ‖2*Real.exp (-(2*(n+1:ℝ))*x)*Real.sin (a*x)‖) ≤
      |a| /(2*(n+1:ℝ)^2) := by
  have hb : 0<2*(n+1:ℝ) := by positivity
  have hFn : IntegrableOn (fun x : ℝ => 2*Real.exp (-(2*(n+1:ℝ))*x)*Real.sin (a*x))
      (Ioi 0) := by
    simpa [IntegrableOn, mul_assoc] using (laplace_sin (a:=a) hb).1.const_mul 2
  have hI := (DLMF.Gamma.integrableOn_exp_mul_pow hb 1).const_mul (2 * |a| )
  have hlt : ∀ x ∈ Ioi (0:ℝ), ‖2*Real.exp (-(2*(n+1:ℝ))*x)*Real.sin (a*x)‖ ≤ 2 * |a|  * (Real.exp (-(2*(n+1:ℝ))*x)*x^1) := by
    intro x hx
    simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (by norm_num : (0:ℝ)≤2), pow_one]
    have hs := Real.abs_sin_le_abs (x := a*x)
    rw [abs_mul, abs_of_pos (show 0<x from hx)] at hs
    nlinarith [Real.exp_pos (-(2*(n+1:ℝ))*x)]
  have h := integral_mono_ae hFn.norm hI
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (hlt)))
  apply h.trans_eq
  rw [integral_const_mul, DLMF.Gamma.integral_exp_mul_pow hb 1]
  norm_num
  field_simp

/-- A bounded sine and `x ≤ sinh x` control the removable quotient by `|a| exp (-x)`. -/
private lemma integrable_exp_sin_div_sinh (a : ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (-x)*Real.sin (a*x)/Real.sinh x) (Ioi 0) := by
  apply Integrable.mono' ((integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0).const_mul |a|)
  · have hc : ContinuousOn (fun x : ℝ => Real.exp (-x)*Real.sin (a*x)/Real.sinh x) (Ioi 0) := by
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro x hx
      exact (Real.sinh_pos_iff.mpr hx).ne'
    exact hc.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hs := Real.abs_sin_le_abs (x := a*x)
    rw [abs_mul, abs_of_pos (show 0<x from hx)] at hs
    rw [norm_div, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Real.norm_eq_abs, abs_of_pos (Real.sinh_pos_iff.mpr hx)]
    apply (div_le_iff₀ (Real.sinh_pos_iff.mpr hx)).mpr
    have hxsh := Real.self_le_sinh_iff.mpr hx.le
    have he := Real.exp_pos (-x)
    simp only [neg_one_mul]
    calc Real.exp (-x)*|Real.sin (a*x)| ≤ Real.exp (-x)*(|a| *x) :=
          mul_le_mul_of_nonneg_left hs he.le
      _ = (|a| *Real.exp (-x))*x := by ring
      _ ≤ (|a| *Real.exp (-x))*Real.sinh x :=
          mul_le_mul_of_nonneg_left hxsh (mul_nonneg (abs_nonneg a) he.le)

/-- Integrability on the specified set: `IntegrableOn (fun x : ℝ => Real.exp (-x)*Real.sin
(a*x)/Real.sinh x) (Ioi 0) ∧ (∫ x : ℝ in Ioi 0, Real.exp (-x)*Real.sin (a*x)/Real.sinh
x)=π/2*(Real.cosh (π*a/2)/Real.sinh (π*a/2))-1/a`. -/
@[dlmf 4.40.E7]
theorem integral_exp_sin_div_sinh {a : ℝ} (ha : a≠0) : IntegrableOn (fun x : ℝ => Real.exp (-x)*Real.sin (a*x)/Real.sinh x) (Ioi 0) ∧ (∫ x : ℝ in Ioi 0, Real.exp (-x)*Real.sin (a*x)/Real.sinh x)=π/2*(Real.cosh (π*a/2)/Real.sinh (π*a/2))-1/a := by
  let F : ℕ → ℝ → ℝ := fun n x => 2*Real.exp (-(2*(n+1:ℝ))*x)*Real.sin (a*x)
  have hb (n : ℕ) : 0<2*(n+1:ℝ) := by positivity
  have hi (n : ℕ) : IntegrableOn (F n) (Ioi 0) := by
    simpa [IntegrableOn, F, mul_assoc] using (laplace_sin (a:=a) (hb n)).1.const_mul 2
  have hbound (n : ℕ) : (∫ x in Ioi (0:ℝ), ‖F n x‖) ≤
      |a| /(2*(n+1:ℝ)^2) := exp_sin_term_integral_norm_bound a n
  have hsum : Summable (fun n => ∫ x in Ioi (0:ℝ), ‖F n x‖) := by
    apply Summable.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg _) hbound
    have hp : Summable (fun n : ℕ => 1/(n:ℝ)^2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num : 1<2)
    have h := ((summable_nat_add_iff 1).mpr hp).mul_left (|a| /2)
    convert h using 1
    ext n
    push_cast
    field_simp
  have he : EqOn (fun x : ℝ => ∑' n, F n x)
      (fun x => Real.exp (-x)*Real.sin (a*x)/Real.sinh x) (Ioi 0) := by
    intro x hx
    have hx0 : 0<x := hx
    have hxexp : Real.exp (-2*x)<1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hf (n : ℕ) : F n x = (2*Real.exp (-2*x)*Real.sin (a*x))*Real.exp (-2*x)^n := by
      dsimp only [F]
      rw [show -(2*(n+1:ℝ))*x = -2*x+(n:ℝ)*(-2*x) by ring,
        Real.exp_add, Real.exp_nat_mul]
      ring
    simp_rw [hf]
    rw [tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_pos _).le hxexp]
    rw [Real.sinh_eq, show -2*x=-(x+x) by ring, Real.exp_neg, Real.exp_add, Real.exp_neg]
    field_simp
  have htsum := integral_tsum_of_summable_integral_norm hi hsum
  refine ⟨integrable_exp_sin_div_sinh a, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi he, ← htsum]
  have hv (n : ℕ) : (∫ x in Ioi (0:ℝ), F n x) = (a/2)/((n+1:ℝ)^2+(a/2)^2) := by
    have h := (laplace_sin (a:=a) (hb n)).2
    have hf : F n = fun x => 2 * (Real.exp (-(2*(n+1:ℝ))*x)*Real.sin (a*x)) := by
      ext x; dsimp only [F]; ring
    rw [hf, integral_const_mul, h]
    field_simp
  simp_rw [hv]
  rw [← DLMF.Gamma.digamma_one_add_mul_I_im_series (a/2),
    DLMF.Gamma.digamma_one_add_mul_I_im (a/2) (div_ne_zero ha (by norm_num))]
  rw [show 2*(a/2)=a by ring, show π*(a/2)=π*a/2 by ring]
  ring

/-- Integrability on the specified set: `IntegrableOn (fun x : ℝ => Real.sinh (a*x)/Real.sinh
(π*x)) (Ioi 0) ∧ (∫ x : ℝ in Ioi 0, Real.sinh (a*x)/Real.sinh (π*x))=Real.tan (a/2)/2`. -/
@[dlmf 4.40.E8]
theorem integral_sinh_div_sinh {a : ℝ} (ha : -π<a ∧ a<π) : IntegrableOn (fun x : ℝ => Real.sinh (a*x)/Real.sinh (π*x)) (Ioi 0) ∧ (∫ x : ℝ in Ioi 0, Real.sinh (a*x)/Real.sinh (π*x))=Real.tan (a/2)/2 := by
  let p := (π-a)/(2*π)
  have hp : 0<p := div_pos (by linarith) (by positivity)
  have hp1 : p<1 := (div_lt_one (by positivity : 0<2*π)).mpr (by linarith)
  let F := fun (s t : ℝ) => (Real.exp (-t)-Real.exp (-s*t))/(1-Real.exp (-t))
  let H := fun t : ℝ => F (1-p) t-F p t
  have hi : IntegrableOn H (Ioi 0) :=
    (DLMF.Gamma.integrableOn_digamma_add_euler (by linarith : 0<1-p)).sub
      (DLMF.Gamma.integrableOn_digamma_add_euler hp)
  have hv : (∫ t in Ioi (0:ℝ), H t) = π * Real.cot (π*p) := by
    rw [integral_sub (DLMF.Gamma.integrableOn_digamma_add_euler (by linarith : 0<1-p))
      (DLMF.Gamma.integrableOn_digamma_add_euler hp),
      ← DLMF.Gamma.digamma_add_euler_Ioi (by linarith : 0<1-p),
      ← DLMF.Gamma.digamma_add_euler_Ioi hp]
    have h := Real.digamma_one_sub hp hp1
    dsimp only [H, F] at *
    linarith
  have he : EqOn (fun x : ℝ => H ((2*π)*x))
      (fun x : ℝ => Real.sinh (a*x)/Real.sinh (π*x)) (Ioi 0) := by
    intro x hx
    have hx0 : 0<x := hx
    have hex : Real.exp (-(2*π*x)) ≠ 1 := ne_of_lt (Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos]))
    have hs : Real.sinh (π*x) ≠ 0 := (Real.sinh_pos_iff.mpr (by positivity)).ne'
    dsimp only [H, F, p]
    rw [show -(1-(π-a)/(2*π))*((2*π)*x) = -π*x-a*x by field_simp; ring,
      show -((π-a)/(2*π))*((2*π)*x) = -π*x+a*x by field_simp; ring]
    rw [Real.sinh_eq, Real.sinh_eq]
    rw [Real.exp_sub, Real.exp_add, show -(2*π*x)=-(π*x+π*x) by ring,
      Real.exp_neg, Real.exp_add, Real.exp_neg, Real.exp_neg]
    simp only [neg_mul, Real.exp_neg]
    field_simp
    ring
  have hi' : IntegrableOn (fun x : ℝ => H ((2*π)*x)) (Ioi 0) := by
    simpa using (integrableOn_Ioi_comp_mul_left_iff H 0 (by positivity : 0<2*π)).mpr
      (by simpa using hi)
  refine ⟨hi'.congr_fun he measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi he,
    integral_comp_mul_left_Ioi H 0 (by positivity : 0<2*π)]
  simp only [mul_zero, smul_eq_mul]
  rw [hv, Real.cot_eq_cos_div_sin, show π*p=π/2-a/2 by dsimp only [p]; field_simp,
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, Real.tan_eq_sin_div_cos]
  field_simp

/-- Integrability of the indicated kernel: `Integrable (fun x : ℝ => Real.exp (a*x)/(Real.cosh
(x/2))^2) ∧ (∫ x : ℝ, Real.exp (a*x)/(Real.cosh (x/2))^2)=(if a=0 then 4 else 4*π*a/Real.sin
(π*a))`. -/
@[dlmf 4.40.E9]
theorem integral_exp_div_cosh_sq {a : ℝ} (ha : -1<a ∧ a<1) : Integrable (fun x : ℝ => Real.exp (a*x)/(Real.cosh (x/2))^2) ∧ (∫ x : ℝ, Real.exp (a*x)/(Real.cosh (x/2))^2)=(if a=0 then 4 else 4*π*a/Real.sin (π*a)) := by
  have habs : |a| < 1 := abs_lt.mpr ha
  obtain ⟨hi,hv⟩ := DLMF.Gamma.integral_exp_div_cosh_rpow (a := 1) habs
  have he : (fun t : ℝ => Real.exp (2*a*t)/Real.cosh t^(2*(1:ℝ))) =
      fun t => Real.exp (2*a*t)/Real.cosh t^2 := by
    funext t
    norm_num
  rw [he] at hi hv
  have hcomp := (integrable_comp_mul_left_iff (g := fun t : ℝ => Real.exp (2*a*t)/Real.cosh t^2)
    (by norm_num : (1/2:ℝ) ≠ 0)).mpr hi
  have hform : (fun x : ℝ => Real.exp (a*x)/Real.cosh (x/2)^2) =
      fun x => Real.exp (2*a*((1/2)*x))/Real.cosh ((1/2)*x)^2 := by
    funext x
    rw [show 2*a*((1/2)*x) = a*x by ring, show (1/2:ℝ)*x = x/2 by ring]
  rw [hform]
  refine ⟨hcomp, ?_⟩
  rw [Measure.integral_comp_mul_left (fun t : ℝ => Real.exp (2*a*t)/Real.cosh t^2) (1/2), hv]
  norm_num
  by_cases ha0 : a=0
  · subst a
    norm_num [Real.Gamma_one]
  · rw [ite_eq_right ha0, show 1+a=a+1 by ring, Real.Gamma_add_one ha0,
      mul_assoc, Real.Gamma_mul_Gamma_one_sub a]
    ring

/-- The real derivative of hyperbolic tangent is the real restriction of its complex derivative. -/
private lemma hypR4_real_hasDerivAt_tanh (x : ℝ) :
    HasDerivAt Real.tanh ((Real.cosh x)⁻¹ ^ 2) x := by
  have hc : Complex.cosh (x : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_cosh]
    exact_mod_cast (Real.cosh_pos x).ne'
  simpa only [sech, ← Complex.ofReal_cosh, ← Complex.ofReal_inv,
    ← Complex.ofReal_pow, ← Complex.ofReal_tanh, Complex.ofReal_re] using
    (hasDerivAt_tanh hc).real_of_complex
/-- The derivative of hyperbolic tangent has an exponential upper bound on the real line. -/
private lemma hypR4_real_tanh_deriv_bound (x : ℝ) :
    ‖(Real.cosh x)⁻¹ ^ 2‖ ≤ 4 * Real.exp (-2 * x) := by
  have hc : 0 < Real.cosh x := Real.cosh_pos x
  have he : 0 < Real.exp x := Real.exp_pos x
  have hl : Real.exp x ≤ 2 * Real.cosh x := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-x)]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hi : (Real.cosh x)⁻¹ ≤ 2 * (Real.exp x)⁻¹ := by
    apply (inv_le_iff_one_le_mul₀ hc).mpr
    have hh : 1 ≤ (2 * Real.cosh x) / Real.exp x :=
      (le_div_iff₀ he).mpr (by simpa using hl)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh
  have hx : Real.exp (-2 * x) = ((Real.exp x)⁻¹)^2 := by
    rw [show -2 * x = -(x + x) by ring, Real.exp_neg, Real.exp_add, mul_inv, pow_two]
  rw [hx]
  nlinarith [inv_pos.mpr hc, inv_pos.mpr he]
/-- A mean-value bound for two scaled hyperbolic tangents cancels the Frullani kernel’s apparent singularity. -/
private lemma hypR4_real_tanh_difference_bound {a b t : ℝ} (ht : 0 ≤ t) :
    ‖Real.tanh (a*t) - Real.tanh (b*t)‖ ≤
      4 * Real.exp (-2 * min a b * t) * (|a-b| * t) := by
  have hd (x : ℝ) (_hx : x ∈ uIcc (b*t) (a*t)) :=
    (hypR4_real_hasDerivAt_tanh x).hasDerivWithinAt (s := uIcc (b*t) (a*t))
  have hb (x : ℝ) (hx : x ∈ uIcc (b*t) (a*t)) :
      ‖(Real.cosh x)⁻¹ ^ 2‖ ≤ 4 * Real.exp (-2 * min a b * t) := by
    apply (hypR4_real_tanh_deriv_bound x).trans
    have hmin : min a b * t ≤ x := by
      rw [uIcc, mem_Icc] at hx
      rw [min_mul_of_nonneg _ _ ht]
      simpa [min_comm] using hx.1
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
  have h := (convex_uIcc (b*t) (a*t)).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (left_mem_uIcc) (right_mem_uIcc)
  simpa only [Real.norm_eq_abs, ← sub_mul, abs_mul, abs_of_nonneg ht] using h
/-- Hyperbolic tangent tends to one at positive infinity. -/
private lemma hypR4_real_tanh_tendsto : Tendsto Real.tanh atTop (𝓝 1) := by
  have he : Tendsto (fun x : ℝ => Real.exp (-2*x)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      ((tendsto_const_mul_atBot_of_neg (by norm_num : (-2 : ℝ) < 0)).mpr tendsto_id)
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub he).div
    ((tendsto_const_nhds (x := (1 : ℝ))).add he) (by norm_num : (1:ℝ)+0 ≠ 0)
  convert h using 1
  · ext x
    dsimp only [Pi.div_apply]
    rw [Real.tanh_eq, show -2*x = -x + -x by ring, Real.exp_add, Real.exp_neg]
    have he0 := Real.exp_ne_zero x
    field_simp
  · norm_num

/-- Integrability on the specified set: `IntegrableOn (fun x : ℝ => (Real.tanh (a*x)-Real.tanh
(b*x))/x) (Ioi 0) ∧ (∫ x : ℝ in Ioi 0, (Real.tanh (a*x)-Real.tanh (b*x))/x)=Real.log (a/b)`. -/
@[dlmf 4.40.E10]
theorem integral_tanh_difference {a b : ℝ} (ha : 0<a) (hb : 0<b) : IntegrableOn (fun x : ℝ => (Real.tanh (a*x)-Real.tanh (b*x))/x) (Ioi 0) ∧ (∫ x : ℝ in Ioi 0, (Real.tanh (a*x)-Real.tanh (b*x))/x)=Real.log (a/b) := by
  -- TauCeti supplies continuity of the total real hyperbolic tangent.
  have hc := Real.continuous_tanh
  have hm : -2 * min a b < 0 := by nlinarith [lt_min ha hb]
  have hi : IntegrableOn (fun x : ℝ => (Real.tanh (a*x)-Real.tanh (b*x))/x) (Ioi 0) := by
    apply Integrable.mono' ((integrableOn_exp_mul_Ioi hm 0).const_mul (4 * |a-b|))
    · have hg : ContinuousOn (fun x : ℝ => (Real.tanh (a*x)-Real.tanh (b*x))/x) (Ioi 0) :=
        ((hc.comp (by fun_prop)).continuousOn.sub (hc.comp (by fun_prop)).continuousOn).div
          continuousOn_id (fun x hx => (ne_of_gt hx))
      exact hg.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : (0 : ℝ) < x := hx
      rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx0]
      apply (div_le_iff₀ hx0).mpr
      have h := hypR4_real_tanh_difference_bound (a := a) (b := b) hx0.le
      convert h using 1
      ring
  refine ⟨hi, ?_⟩
  have hl : Tendsto Real.tanh (𝓝[>] 0) (𝓝 0) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hi' : IntegrableOn (fun x : ℝ => x⁻¹ • (Real.tanh (a*x)-Real.tanh (b*x))) (Ioi 0) := by
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hi
  have h := Frullani.integral_Ioi_eq (hc.locallyIntegrable.locallyIntegrableOn _) ha hb hl
    hypR4_real_tanh_tendsto hi'
  rw [Real.log_div hb.ne' ha.ne'] at h
  rw [Real.log_div ha.ne' hb.ne']
  convert h using 1 <;> simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- At `x`, the function `(fun t : ℝ => t*Real.arsinh t-Real.sqrt (1+t^2))` has derivative
`(Real.arsinh x)`. -/
@[dlmf 4.40.E11]
theorem antiderivative_arcsinh (x : ℝ) : HasDerivAt (fun t : ℝ => t*Real.arsinh t-Real.sqrt (1+t^2)) (Real.arsinh x) x := by
  have hp:0<1+x^2 := by positivity
  have hd:=((hasDerivAt_id x).mul (Real.hasDerivAt_arsinh x)).sub
    ((((hasDerivAt_id x).pow 2).const_add 1).sqrt hp.ne')
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul]
    field_simp
    ring

/-- At `x`, the function `(fun t : ℝ => t*Real.arcosh t-Real.sqrt (t^2-1))` has derivative
`(Real.arcosh x)`. -/
@[dlmf 4.40.E12]
theorem antiderivative_arccosh {x : ℝ} (hx : 1<x) : HasDerivAt (fun t : ℝ => t*Real.arcosh t-Real.sqrt (t^2-1)) (Real.arcosh x) x := by
  have hp:0<x^2-1 := by nlinarith
  have hd:=((hasDerivAt_id x).mul (Real.hasDerivAt_arcosh hx)).sub
    ((((hasDerivAt_id x).pow 2).sub_const 1).sqrt hp.ne')
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul]
    field_simp
    ring

/-- At `x`, the function `(fun t : ℝ => t*Real.artanh t+Real.log (1-t^2)/2)` has derivative
`(Real.artanh x)`. -/
@[dlmf 4.40.E13]
theorem antiderivative_arctanh {x : ℝ} (hx : |x|<1) : HasDerivAt (fun t : ℝ => t*Real.artanh t+Real.log (1-t^2)/2) (Real.artanh x) x := by
  have hx' : x ∈ Ioo (-1:ℝ) 1 := ⟨(abs_lt.mp hx).1, (abs_lt.mp hx).2⟩
  have hp : 0 < 1-x^2 := by nlinarith [(abs_lt.mp hx).1, (abs_lt.mp hx).2]
  have hd := ((hasDerivAt_id x).mul (Real.hasDerivAt_artanh hx')).add
    ((((hasDerivAt_id x).pow 2).const_sub 1).log hp.ne' |>.div_const 2)
  convert hd using 1
  · rfl
  · dsimp only [id, Pi.pow_apply]
    field_simp
    ring

/-- At `x`, the function `(fun t : ℝ => t*Real.arsinh t⁻¹+Real.arsinh t)` has derivative
`(Real.arsinh x⁻¹)`. -/
@[dlmf 4.40.E14]
theorem antiderivative_arccsch {x : ℝ} (hx : 0<x) : HasDerivAt (fun t : ℝ => t*Real.arsinh t⁻¹+Real.arsinh t) (Real.arsinh x⁻¹) x := by
  have hx0 : x ≠ 0 := hx.ne'
  have hd := ((hasDerivAt_id x).mul ((hasDerivAt_inv hx.ne').arsinh)).add (Real.hasDerivAt_arsinh x)
  convert hd using 1
  · rfl
  · dsimp only [id]
    have hq : Real.sqrt (1+(x⁻¹)^2) = Real.sqrt (1+x^2)/x := by
      rw [show 1+(x⁻¹)^2 = (1+x^2)/x^2 by field_simp; ring, Real.sqrt_div (by positivity),
        Real.sqrt_sq hx.le]
    rw [hq, smul_eq_mul]
    have : 0 < Real.sqrt (1+x^2) := Real.sqrt_pos.mpr (by positivity)
    field_simp
    ring

/-- At `x`, the function `(fun t : ℝ => t*Real.arcosh t⁻¹+Real.arcsin t)` has derivative
`(Real.arcosh x⁻¹)`. -/
@[dlmf 4.40.E15]
theorem antiderivative_arcsech {x : ℝ} (hx : 0<x ∧ x<1) : HasDerivAt (fun t : ℝ => t*Real.arcosh t⁻¹+Real.arcsin t) (Real.arcosh x⁻¹) x := by
  obtain ⟨h0,h1⟩ := hx
  have hx0 : x ≠ 0 := h0.ne'
  have hi : x⁻¹ ∈ Ioi (1:ℝ) := by
    show 1 < x⁻¹
    exact one_lt_inv₀ h0 |>.mpr h1
  have hd := ((hasDerivAt_id x).mul ((Real.hasDerivAt_arcosh hi).comp x (hasDerivAt_inv h0.ne'))).add
    (Real.hasDerivAt_arcsin (by linarith) (by linarith : x ≠ 1))
  convert hd using 1
  · rfl
  · dsimp only [id, Function.comp]
    have hq : Real.sqrt ((x⁻¹)^2-1) = Real.sqrt (1-x^2)/x := by
      rw [show (x⁻¹)^2-1 = (1-x^2)/x^2 by field_simp, Real.sqrt_div (by nlinarith),
        Real.sqrt_sq h0.le]
    rw [hq]
    have : 0 < Real.sqrt (1-x^2) := Real.sqrt_pos.mpr (by nlinarith)
    field_simp
    ring

/-- At `x`, the function `(fun t : ℝ => t*Real.artanh t⁻¹+Real.log (t^2-1)/2)` has derivative
`(Real.artanh x⁻¹)`. -/
@[dlmf 4.40.E16]
theorem antiderivative_arccoth {x : ℝ} (hx : 1<x) : HasDerivAt (fun t : ℝ => t*Real.artanh t⁻¹+Real.log (t^2-1)/2) (Real.artanh x⁻¹) x := by
  have hi : x⁻¹ ∈ Ioo (-1:ℝ) 1 := ⟨by have := inv_pos.mpr (by linarith : (0:ℝ)<x); linarith,
    inv_lt_one_of_one_lt₀ hx⟩
  have hp : 0 < x^2-1 := by nlinarith
  have hd := ((hasDerivAt_id x).mul ((Real.hasDerivAt_artanh hi).comp x
    (hasDerivAt_inv (by linarith : x ≠ 0)))).add
    ((((hasDerivAt_id x).pow 2).sub_const 1).log hp.ne' |>.div_const 2)
  convert hd using 1
  · rfl
  · dsimp only [id, Function.comp, Pi.pow_apply]
    have hx0 : x ≠ 0 := by linarith
    have : 1-(x⁻¹)^2 = (x^2-1)/x^2 := by field_simp
    rw [this]
    field_simp
    ring

/-- Two functions that agree on an open neighbourhood have the same derivative there. -/
private lemma hypR4_deriv_eq {f g : ℂ → ℂ} {f' g' z : ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hz : z ∈ U) (hf : HasDerivAt f f' z) (hg : HasDerivAt g g' z) (h : ∀ w ∈ U, f w = g w) :
    f' = g' :=
  hf.unique (hg.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (hU.mem_nhds hz) h))

/-- Local logarithmic branches give complex primitives without imposing principal-log cuts. -/
theorem complex_antiderivatives_hyperbolic {U : Set ℂ} (hU : IsOpen U)
    {z : ℂ} (hz : z∈U) (hc : Complex.cosh z≠0) (hs : Complex.sinh z≠0)
    {Lcosh Lsinh Ltanh : ℂ → ℂ}
    (hLc : AnalyticOnNhd ℂ Lcosh U) (hLs : AnalyticOnNhd ℂ Lsinh U)
    (hLt : AnalyticOnNhd ℂ Ltanh U)
    (hEc : ∀ w∈U, Complex.exp (Lcosh w)=Complex.cosh w)
    (hEs : ∀ w∈U, Complex.exp (Lsinh w)=Complex.sinh w)
    (hEt : ∀ w∈U, Complex.exp (Ltanh w)=Complex.tanh (w/2)) :
    HasDerivAt Lcosh (Complex.tanh z) z ∧ HasDerivAt Lsinh (coth z) z ∧
      HasDerivAt Ltanh (csch z) z := by
  have dc := (hLc z hz).differentiableAt.hasDerivAt
  have ds := (hLs z hz).differentiableAt.hasDerivAt
  have dt := (hLt z hz).differentiableAt.hasDerivAt
  have ec := hypR4_deriv_eq hU hz dc.cexp (Complex.hasDerivAt_cosh z) hEc
  have es := hypR4_deriv_eq hU hz ds.cexp (Complex.hasDerivAt_sinh z) hEs
  have h2 : Complex.sinh z = 2*Complex.sinh (z/2)*Complex.cosh (z/2) := by
    rw [← Complex.sinh_two_mul]; ring_nf
  have hc2 : Complex.cosh (z/2) ≠ 0 := fun h => hs (by rw [h2, h]; ring)
  have hs2 : Complex.sinh (z/2) ≠ 0 := fun h => hs (by rw [h2, h]; ring)
  have dth : HasDerivAt (fun w => Complex.tanh (w/2)) (sech (z/2)^2*(1/2)) z := by
    have := (hasDerivAt_tanh hc2).comp z ((hasDerivAt_id z).div_const 2)
    simpa [Function.comp_def] using this
  have et := hypR4_deriv_eq hU hz dt.cexp dth hEt
  rw [hEc z hz] at ec
  rw [hEs z hz] at es
  rw [hEt z hz] at et
  refine ⟨?_, ?_, ?_⟩
  · convert dc using 1
    rw [Complex.tanh_eq_sinh_div_cosh, div_eq_iff hc]; linear_combination -ec
  · convert ds using 1
    rw [coth, div_eq_iff hs]; linear_combination -es
  · convert dt using 1
    have ht0 : Complex.tanh (z/2) ≠ 0 := by
      rw [Complex.tanh_eq_sinh_div_cosh]; exact div_ne_zero hs2 hc2
    have hd : deriv Ltanh z = sech (z/2)^2*(1/2)/Complex.tanh (z/2) := by
      rw [eq_div_iff ht0]; linear_combination et
    rw [hd, csch, h2, sech, Complex.tanh_eq_sinh_div_cosh]
    field_simp

/-- The principal complex arcsinh primitive on its complete open cut domain. -/
theorem complex_antiderivative_arcsinh {z : ℂ} (hz : z∈arcsinhDomain) :
    HasDerivAt (fun w => w*arcsinh w-Complex.sqrt (1+w^2)) (arcsinh z) z := by
  have hq : 1+z^2 ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    rcases hz with hr | hi
    · by_cases hy : z.im = 0
      · left; simp [pow_two, Complex.mul_re, hy]; nlinarith [sq_nonneg z.re]
      · right; simp [pow_two, Complex.mul_im]
        intro h; apply mul_ne_zero (mul_ne_zero two_ne_zero hr) hy; linear_combination h
    · left
      simp [pow_two, Complex.mul_re]
      nlinarith [abs_lt.mp hi, sq_nonneg z.re]
  have hr : Complex.sqrt (1+z^2) ≠ 0 := by
    intro h
    have hs := trig_sqrt_sq (1+z^2)
    rw [h, zero_pow two_ne_zero] at hs
    exact Complex.slitPlane_ne_zero hq hs.symm
  have hp : HasDerivAt (fun w : ℂ => 1+w^2) (2*z) z := by
    simpa using (hasDerivAt_pow 2 z).const_add 1
  have dS := (Complex.hasDerivAt_sqrt hq).comp z hp
  have hv : (1+z^2)^(-1/2:ℂ) = (Complex.sqrt (1+z^2))⁻¹ := by
    rw [Complex.sqrt, show (-1/2:ℂ) = -(2⁻¹) by norm_num, Complex.cpow_neg]
  have hd := ((hasDerivAt_id z).mul (hyper_hasDerivAt_arcsinh hz)).sub dS
  rw [hv] at hd
  convert hd using 1
  · funext w; simp [Function.comp_def]
  · simp only [id_eq]
    field_simp
    ring

/-- The principal complex arccosh primitive on its complete open cut domain. -/
theorem complex_antiderivative_arccosh {z : ℂ} (hz : z∈arccoshDomain) :
    HasDerivAt (fun w => w*arccosh w-Complex.sqrt (w-1)*Complex.sqrt (w+1)) (arccosh z) z := by
  obtain ⟨h1, h2⟩ := hypR4_acosh_slit hz
  have hs := hypR4_acosh_root_ne hz
  have hA : Complex.sqrt (z-1) ≠ 0 := fun h => hs (by rw [h, zero_mul])
  have hB : Complex.sqrt (z+1) ≠ 0 := fun h => hs (by rw [h, mul_zero])
  have dA : HasDerivAt (fun w => Complex.sqrt (w-1)) ((Complex.sqrt (z-1))⁻¹/2) z := by
    have := (Complex.hasDerivAt_sqrt h1).comp z ((hasDerivAt_id z).sub_const 1)
    simpa only [Complex.sqrt, show (-1/2:ℂ) = -(2⁻¹:ℂ) by norm_num, Complex.cpow_neg, mul_one,
      Function.comp_def, id] using this
  have dB : HasDerivAt (fun w => Complex.sqrt (w+1)) ((Complex.sqrt (z+1))⁻¹/2) z := by
    have := (Complex.hasDerivAt_sqrt h2).comp z ((hasDerivAt_id z).add_const 1)
    simpa only [Complex.sqrt, show (-1/2:ℂ) = -(2⁻¹:ℂ) by norm_num, Complex.cpow_neg, mul_one,
      Function.comp_def, id] using this
  have hd := ((hasDerivAt_id z).mul (hypR4_hasDerivAt_arccosh hz)).sub (dA.mul dB)
  convert hd using 1
  · rfl
  have eA := trig_sqrt_sq (z-1)
  have eB := trig_sqrt_sq (z+1)
  simp only [id_eq]
  generalize Complex.sqrt (z-1) = A at *
  generalize Complex.sqrt (z+1) = B at *
  field_simp
  linear_combination eA + eB

/-- The principal complex arctanh primitive on its complete open cut domain. -/
theorem complex_antiderivative_arctanh {z : ℂ} (hz : z∈arctanhDomain) :
    HasDerivAt (fun w => w*arctanh w+Complex.log (1-w^2)/2) (arctanh z) z := by
  have hq : 1-z^2 ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    rcases hz with hi | hr
    · by_cases hx : z.re = 0
      · left; simp [pow_two, Complex.mul_re, hx]; nlinarith [sq_nonneg z.im]
      · right; simp [pow_two, Complex.mul_im]
        intro h; apply mul_ne_zero (mul_ne_zero two_ne_zero hx) hi; linear_combination -h
    · left
      simp [pow_two, Complex.mul_re]
      nlinarith [abs_lt.mp hr, sq_nonneg z.im]
  have hq0 : 1-z^2 ≠ 0 := Complex.slitPlane_ne_zero hq
  have dL := ((Complex.hasDerivAt_log hq).comp z (((hasDerivAt_id z).pow 2).const_sub 1)).div_const 2
  have hd := ((hasDerivAt_id z).mul (hyper_hasDerivAt_arctanh hz)).add dL
  convert hd using 1
  · funext w; simp [Function.comp_def]
  · simp only [id_eq, Pi.pow_apply]
    field_simp
    ring

/-- The remaining inverse functions are real on their uncut real intervals. -/
theorem reciprocal_inverses_ofReal {x : ℝ} :
    (x≠0 → arccsch x=(Real.arsinh x⁻¹:ℂ)) ∧
    (0<x ∧ x≤1 → arcsech x=(Real.arcosh x⁻¹:ℂ)) ∧
    (1< |x| → arccoth x=(Real.artanh x⁻¹:ℂ)) := by
  refine ⟨fun _ => ?_, fun hx => ?_, fun hx => ?_⟩
  · rw [arccsch, ← Complex.ofReal_inv, arcsinh_ofReal]
  · have h1 : 1 ≤ x⁻¹ := one_le_inv₀ hx.1 |>.mpr hx.2
    rw [arcsech, ← Complex.ofReal_inv, arccosh_ofReal _ h1]
  · have hx0 : x ≠ 0 := by rintro rfl; simp at hx; linarith
    have h1 : |x⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hx
    rw [arccoth_eq_inv (by exact_mod_cast hx0), ← Complex.ofReal_inv, arctanh_ofReal _ h1]

/-- A nonvanishing holomorphic function on a disc about the origin, equal to `1` at the origin,
has a holomorphic logarithm vanishing at the origin. -/
private lemma hypR4_exists_log_ball {r : ℝ} {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (Metric.ball 0 r)) (hne : ∀ z ∈ Metric.ball (0:ℂ) r, g z ≠ 0)
    (h0 : g 0 = 1) (hr : 0 < r) : ∃ L, HyperbolicNormalizedLog (Metric.ball 0 r) g L := by
  have hB : IsOpen (Metric.ball (0:ℂ) r) := Metric.isOpen_ball
  have h0B : (0:ℂ) ∈ Metric.ball (0:ℂ) r := Metric.mem_ball_self hr
  have hd : DifferentiableOn ℂ (fun z => deriv g z / g z) (Metric.ball 0 r) :=
    (hg.deriv hB).div hg hne
  obtain ⟨P, hP0, hP⟩ := hd.isExactOn_ball.with_val_at 0 0
  have hPd : DifferentiableOn ℂ P (Metric.ball 0 r) :=
    fun z hz => (hP z hz).differentiableAt.differentiableWithinAt
  have hQd : ∀ z ∈ Metric.ball (0:ℂ) r,
      HasDerivAt (fun w => g w * Complex.exp (-P w)) 0 z := by
    intro z hz
    have hgz : HasDerivAt g (deriv g z) z :=
      (hg.differentiableAt (hB.mem_nhds hz)).hasDerivAt
    have := hgz.mul ((hP z hz).neg.cexp)
    convert this using 1
    field_simp [hne z hz]
    ring
  have hQc : Set.EqOn (fun w => g w * Complex.exp (-P w)) (fun _ => (1:ℂ)) (Metric.ball 0 r) := by
    refine hB.eqOn_of_deriv_eq (convex_ball (0:ℂ) r).isPreconnected
      (fun z hz => (hQd z hz).differentiableAt.differentiableWithinAt)
      (differentiableOn_const 1) (fun z hz => ?_) h0B (by simp [h0, hP0])
    simp only [(hQd z hz).deriv, deriv_const]
  refine ⟨P, hPd.analyticOnNhd hB, hP0, fun z hz => ?_⟩
  have h := hQc hz
  simp only at h
  have he : Complex.exp (-P z) * Complex.exp (P z) = 1 := by rw [← Complex.exp_add]; simp
  linear_combination -(Complex.exp (P z))*h + g z*he

/-- `sinh` has no zeros other than the origin in the open disc of radius `π`. -/
private lemma hypR4_sinh_ne_zero_ball {z : ℂ} (hz : ‖z‖ < π) (hz0 : z ≠ 0) :
    Complex.sinh z ≠ 0 := by
  intro h
  have hs : Complex.sin (z*I) = 0 := by rw [Complex.sin_mul_I, h, zero_mul]
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hs
  have hn : ‖z‖ = |(k:ℝ)| * π := by
    have := congrArg norm hk
    rw [norm_mul, Complex.norm_I, mul_one, norm_mul, Complex.norm_intCast, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le] at this
    exact this
  rcases eq_or_ne k 0 with rfl | hk0
  · simp at hk; exact hz0 hk
  · have : (1:ℝ) ≤ |(k:ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk0
    nlinarith [Real.pi_pos]

/-- `cosh` has no zeros in the open disc of radius `π/2`. -/
private lemma hypR4_cosh_ne_zero_ball {z : ℂ} (hz : ‖z‖ < π/2) : Complex.cosh z ≠ 0 := by
  intro h
  have hs : Complex.cos (z*I) = 0 := by rw [Complex.cos_mul_I, h]
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hs
  have hn : ‖z‖ = |2*(k:ℝ)+1| * π / 2 := by
    have := congrArg norm hk
    rw [norm_mul, Complex.norm_I, mul_one, norm_div, norm_mul,
      show (2*(k:ℂ)+1) = ((2*(k:ℝ)+1:ℝ):ℂ) by push_cast; ring, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le] at this
    simpa using this
  have : (1:ℝ) ≤ |2*(k:ℝ)+1| := by
    rcases le_or_gt 0 k with hk0 | hk0
    · rw [abs_of_nonneg (by positivity)]
      have : (0:ℝ) ≤ k := by exact_mod_cast hk0
      linarith
    · have : (k:ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hk0
      rw [abs_of_neg (by linarith)]; linarith
  nlinarith [Real.pi_pos]

/-- Existence of the three normalized analytic logarithms used in the prose series. -/
theorem exists_hyperbolic_logarithms :
    (∃ L, HyperbolicNormalizedLog (Metric.ball 0 π) sinhc L) ∧
    (∃ L, HyperbolicNormalizedLog (Metric.ball 0 (π/2)) Complex.cosh L) ∧
    (∃ L, HyperbolicNormalizedLog (Metric.ball 0 (π/2)) tanhc L) := by
  have hπ := Real.pi_pos
  refine ⟨?_, ?_, ?_⟩
  · have he : sinhc = dslope Complex.sinh 0 := by
      funext z
      by_cases hz : z = 0
      · subst hz; simp [sinhc, dslope_same, Complex.deriv_sinh]
      · rw [dslope_of_ne _ hz, slope_def_field]; simp [sinhc, hz]
    refine hypR4_exists_log_ball ?_ (fun z hz => ?_) (by simp [sinhc]) hπ
    · rw [he, differentiableOn_dslope (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hπ))]
      exact Complex.differentiable_sinh.differentiableOn
    · have hz' : ‖z‖ < π := by simpa using hz
      by_cases hz0 : z = 0
      · simp [sinhc, hz0]
      · simp only [sinhc, hz0, ↓reduceIte]
        exact div_ne_zero (hypR4_sinh_ne_zero_ball hz' hz0) hz0
  · exact hypR4_exists_log_ball Complex.differentiable_cosh.differentiableOn
      (fun z hz => hypR4_cosh_ne_zero_ball (by simpa using hz)) (by simp) (by positivity)
  · have hc : ∀ z ∈ Metric.ball (0:ℂ) (π/2), Complex.cosh z ≠ 0 :=
      fun z hz => hypR4_cosh_ne_zero_ball (by simpa using hz)
    have hT : DifferentiableOn ℂ Complex.tanh (Metric.ball 0 (π/2)) := by
      intro z hz
      have : Complex.tanh = fun w => Complex.sinh w / Complex.cosh w := by
        funext w; exact Complex.tanh_eq_sinh_div_cosh w
      rw [this]
      exact (Complex.differentiable_sinh.differentiableAt.div
        Complex.differentiable_cosh.differentiableAt (hc z hz)).differentiableWithinAt
    have hd0 : deriv Complex.tanh 0 = 1 := by
      have hh : HasDerivAt (fun w => Complex.sinh w / Complex.cosh w)
          ((Complex.cosh 0*Complex.cosh 0 - Complex.sinh 0*Complex.sinh 0)/(Complex.cosh 0)^2) 0 :=
        (Complex.hasDerivAt_sinh 0).div (Complex.hasDerivAt_cosh 0) (by simp)
      have : Complex.tanh = fun w => Complex.sinh w / Complex.cosh w := by
        funext w; exact Complex.tanh_eq_sinh_div_cosh w
      rw [this, hh.deriv]; simp
    have he : tanhc = dslope Complex.tanh 0 := by
      funext z
      by_cases hz : z = 0
      · subst hz; simp [tanhc, dslope_same, hd0]
      · rw [dslope_of_ne _ hz, slope_def_field]; simp [tanhc, hz]
    refine hypR4_exists_log_ball ?_ (fun z hz => ?_) (by simp [tanhc]) (by positivity)
    · rw [he, differentiableOn_dslope (Metric.isOpen_ball.mem_nhds
        (Metric.mem_ball_self (by positivity)))]
      exact hT
    · have hz' : ‖z‖ < π/2 := by simpa using hz
      by_cases hz0 : z = 0
      · simp [tanhc, hz0]
      · simp only [tanhc, hz0, ↓reduceIte]
        rw [Complex.tanh_eq_sinh_div_cosh]
        exact div_ne_zero (div_ne_zero (hypR4_sinh_ne_zero_ball (by linarith) hz0) (hc z hz)) hz0

/-- `√(1-z²)+iz` never lies on the closed negative real axis. -/
private lemma hypR4_sqrt_add_I_mul_slit (z : ℂ) :
    Complex.sqrt (1-z^2)+I*z ∈ Complex.slitPlane := by
  set q := Complex.sqrt (1-z^2) with hq
  have hq2 : q^2 = 1-z^2 := trig_sqrt_sq _
  have hqre : 0 ≤ q.re := by
    rw [hq, Complex.sqrt, Complex.cpow_inv_two_re]; exact Real.sqrt_nonneg _
  rw [Complex.mem_slitPlane_iff]
  by_contra hc
  push Not at hc
  obtain ⟨hre, him⟩ := hc
  set t := q+I*z with ht
  have hprod : t*(q-I*z) = 1 := by
    rw [ht]; linear_combination (by simp : (I:ℂ)^2 = -1) * (-z^2) + hq2
  have ht_real : t = (t.re:ℂ) := Complex.ext (by simp) (by simp [him])
  have ht0 : t ≠ 0 := by rintro h; rw [h, zero_mul] at hprod; exact zero_ne_one hprod
  have htre0 : t.re < 0 := lt_of_le_of_ne hre (fun h => ht0 (by rw [ht_real, h]; simp))
  have hsum : 2*q = t + t⁻¹ := by
    have : q - I*z = t⁻¹ := (eq_inv_of_mul_eq_one_right hprod)
    rw [← this, ht]; ring
  have : (2*q).re < 0 := by
    rw [hsum, ht_real, ← Complex.ofReal_inv, ← Complex.ofReal_add, Complex.ofReal_re]
    have : t.re⁻¹ < 0 := inv_lt_zero.mpr htre0
    linarith
  simp at this; linarith

/-- The complex extension of the reciprocal-inverse antiderivatives on compatible branches. -/
theorem complex_antiderivatives_reciprocal_inverse {z : ℂ}
    (hre : 0<z.re) (hs : z∈arccschDomain) (hc : z∈arcsechDomain)
    (ha : z.im≠0 ∨ |z.re|<1) :
    HasDerivAt (fun w => w*arccsch w+arcsinh w) (arccsch z) z ∧
    HasDerivAt (fun w => w*arcsech w-I*Complex.log (Complex.sqrt (1-w^2)+I*w))
      (arcsech z) z := by
  have hz0 : z ≠ 0 := hs.1
  have hzs : z ∈ arcsinhDomain := Or.inl hre.ne'
  constructor
  · have hd := ((hasDerivAt_id z).mul (hasDerivAt_arccsch_signed hs hre.ne')).add
      (hyper_hasDerivAt_arcsinh hzs)
    have hq : Complex.sqrt (1+z^2) ≠ 0 := by
      intro h
      have hsq := trig_sqrt_sq (1+z^2)
      rw [h, zero_pow two_ne_zero] at hsq
      have hzs' := hzs
      rcases hzs' with h1 | h1
      · have e : z^2 = -1 := by linear_combination -hsq
        have : z = I ∨ z = -I := by
          have : (z-I)*(z+I) = 0 := by
            linear_combination e - (by simp : (I:ℂ)^2 = -1)
          rcases mul_eq_zero.mp this with h | h
          · left; linear_combination h
          · right; linear_combination h
        rcases this with rfl | rfl <;> simp at h1
      · have e : z^2 = -1 := by linear_combination -hsq
        have : (z-I)*(z+I) = 0 := by
          linear_combination e - (by simp : (I:ℂ)^2 = -1)
        rcases mul_eq_zero.mp this with h | h
        · have : z = I := by linear_combination h
          subst this; simp at h1
        · have : z = -I := by linear_combination h
          subst this; simp at h1
    convert hd using 1
    · rfl
    simp only [hre, ↓reduceIte]
    simp only [id_eq]
    field_simp
    ring
  · have hsl := hypR4_asech_slit hc
    set q := Complex.sqrt (1-z^2) with hqdef
    have hq0 : q ≠ 0 := by
      intro h
      have hs2 := trig_sqrt_sq (1-z^2)
      rw [← hqdef, h, zero_pow two_ne_zero] at hs2
      exact Complex.slitPlane_ne_zero hsl hs2.symm
    have hp : HasDerivAt (fun w : ℂ => 1-w^2) (-(2*z)) z := by
      simpa using (hasDerivAt_pow 2 z).const_sub 1
    have dS := (Complex.hasDerivAt_sqrt hsl).comp z hp
    have hv : (1-z^2)^(-1/2:ℂ) = q⁻¹ := by
      rw [hqdef, Complex.sqrt, show (-1/2:ℂ) = -(2⁻¹) by norm_num, Complex.cpow_neg]
    rw [hv] at dS
    have hL := hypR4_sqrt_add_I_mul_slit z
    have hA : HasDerivAt (fun w : ℂ => Complex.sqrt (1-w^2)+I*w) (2⁻¹*q⁻¹*(-(2*z)) + I) z := by
      convert dS.add ((hasDerivAt_id z).const_mul I) using 1
      · funext w; simp [Function.comp_def]
      · ring
    have dL := (Complex.hasDerivAt_log hL).comp z hA
    have hd := ((hasDerivAt_id z).mul (hasDerivAt_arcsech hc)).sub (dL.const_mul I)
    have hne : q + I*z ≠ 0 := Complex.slitPlane_ne_zero hL
    have hI : (I:ℂ)^2 = -1 := by simp
    rw [← hqdef] at hd
    convert hd using 1
    · funext w; simp
    · simp only [id_eq]
      field_simp
      have hne' : q + z*I ≠ 0 := by rwa [mul_comm z I]
      rw [show I*(-z+q*I) = -(q+z*I) by linear_combination q*hI, neg_div, div_self hne']
      ring

/-- The complex inverse-cotangent primitive with a locally consistent logarithm. -/
theorem complex_antiderivative_arccoth {z : ℂ} (hz : z∈arccothDomain)
    (hlog : z^2-1∈slitPlane) :
    HasDerivAt (fun w => w*arccoth w+Complex.log (w^2-1)/2) (arccoth z) z := by
  have hq0 : z^2-1 ≠ 0 := Complex.slitPlane_ne_zero hlog
  have h1 : 1-z^2 ≠ 0 := fun h => hq0 (by linear_combination -h)
  have dL := ((Complex.hasDerivAt_log hlog).comp z (((hasDerivAt_id z).pow 2).sub_const 1)).div_const 2
  have hd := ((hasDerivAt_id z).mul (hasDerivAt_arccoth hz)).add dL
  convert hd using 1
  · funext w; simp [Function.comp_def]
  · simp only [id_eq, Pi.pow_apply]
    field_simp
    ring

/-- One-sided imaginary pole directions in the exact-value table, without an assigned infinite complex value. -/
@[dlmf 4.31.T1]
theorem hyperbolic_table_imaginary_pole_sides :
    Tendsto (fun y : ℝ => (Complex.tanh (I*y)).im) (𝓝[<] (π/2)) atTop ∧
    Tendsto (fun y : ℝ => (Complex.tanh (I*y)).im) (𝓝[>] (3*π/2)) atBot ∧
    Tendsto (fun y : ℝ => (sech (I*y)).re) (𝓝[<] (π/2)) atTop ∧
    Tendsto (fun y : ℝ => (sech (I*y)).re) (𝓝[>] (3*π/2)) atTop := by
  have ht : ∀ y : ℝ, (Complex.tanh (I*y)).im = Real.tan y := fun y => by
    rw [mul_comm, Complex.tanh_mul_I, Complex.mul_I_im, ← Complex.ofReal_tan, Complex.ofReal_re]
  have hs : ∀ y : ℝ, (sech (I*y)).re = (Real.cos y)⁻¹ := fun y => by
    rw [sech, mul_comm, Complex.cosh_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_inv,
      Complex.ofReal_re]
  have hcos1 : Tendsto Real.cos (𝓝[<] (π/2)) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have := Real.continuous_cos.continuousAt (x := π/2) |>.tendsto
      rw [Real.cos_pi_div_two] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT (by linarith [Real.pi_pos] : -(π/2) < π/2)] with y hy
      exact Real.cos_pos_of_mem_Ioo hy
  have hcos2 : Tendsto Real.cos (𝓝[>] (3*π/2)) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have := Real.continuous_cos.continuousAt (x := 3*π/2) |>.tendsto
      have e : Real.cos (3*π/2) = 0 := by
        rw [show 3*π/2 = π/2+π by ring, Real.cos_add_pi, Real.cos_pi_div_two, neg_zero]
      rw [e] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (by linarith [Real.pi_pos] : 3*π/2 < 5*π/2)] with y hy
      rw [← Real.cos_sub_two_pi]
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hshift : Tendsto (fun y : ℝ => y - 2*π) (𝓝[>] (3*π/2)) (𝓝[>] (-(π/2))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun y : ℝ => y - 2*π) (𝓝 (3*π/2)) (𝓝 (3*π/2 - 2*π)) :=
        tendsto_id.sub tendsto_const_nhds
      rw [show 3*π/2 - 2*π = -(π/2) by ring] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      show -(π/2) < y - 2*π
      have : 3*π/2 < y := hy
      linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ht]; exact Real.tendsto_tan_pi_div_two
  · simp only [ht]
    refine (Real.tendsto_tan_neg_pi_div_two.comp hshift).congr (fun y => ?_)
    simp only [Function.comp]
    rw [show y - 2*π = (y-π)-π by ring, Real.tan_periodic.sub_eq, Real.tan_periodic.sub_eq]
  · simp only [hs]; exact tendsto_inv_nhdsGT_zero.comp hcos1
  · simp only [hs]; exact tendsto_inv_nhdsGT_zero.comp hcos2

/-- A local continued Gudermannian, extending the sech antiderivative to the complex plane. -/
theorem complex_antiderivative_sech {z : ℂ} (hz : Complex.cosh z≠0) :
    ∃ U : Set ℂ, IsOpen U ∧ z∈U ∧ ∃ G : ℂ → ℂ,
      AnalyticOnNhd ℂ G U ∧
      (∀ w∈U, HasDerivAt G (sech w) w) ∧
      (∀ w∈U, Complex.tan (G w/2+π/4)=Complex.exp w) := by
  have hI : (I:ℂ)^2 = -1 := by simp
  have h2cosh : ∀ w : ℂ, 2*Complex.cosh w*Complex.exp w = Complex.exp w^2+1 := by
    intro w
    have h1 := Complex.cosh_add_sinh w
    have h2 := Complex.cosh_sub_sinh w
    have h3 : Complex.exp (-w)*Complex.exp w = 1 := by rw [← Complex.exp_add]; simp
    linear_combination (Complex.exp w)*h1 + (Complex.exp w)*h2 + h3
  have hfac : ∀ w : ℂ, Complex.exp w^2+1 = (1-I*Complex.exp w)*(1+I*Complex.exp w) := by
    intro w; linear_combination (Complex.exp w)^2*hI
  have hnz : ∀ w : ℂ, Complex.cosh w ≠ 0 → 1-I*Complex.exp w ≠ 0 ∧ 1+I*Complex.exp w ≠ 0 := by
    intro w hw
    have h := h2cosh w
    rw [hfac] at h
    have : (1-I*Complex.exp w)*(1+I*Complex.exp w) ≠ 0 := by
      rw [← h]; exact mul_ne_zero (mul_ne_zero two_ne_zero hw) (Complex.exp_ne_zero w)
    exact ⟨left_ne_zero_of_mul this, right_ne_zero_of_mul this⟩
  set f : ℂ → ℂ := fun w => (1+I*Complex.exp w)/(1-I*Complex.exp w) with hfdef
  obtain ⟨hz1, hz2⟩ := hnz z hz
  set c := f z with hc
  have hc0 : c ≠ 0 := div_ne_zero hz2 hz1
  set V : Set ℂ := {w | 1-I*Complex.exp w ≠ 0} with hV
  have hVo : IsOpen V := isOpen_ne_fun (by fun_prop) continuous_const
  have hfc : ContinuousOn (fun w => f w / c) V := by
    intro w hw
    exact (((by fun_prop : Continuous (fun w : ℂ => 1+I*Complex.exp w)).continuousAt.div
      (by fun_prop : Continuous (fun w : ℂ => 1-I*Complex.exp w)).continuousAt hw).div_const
      c).continuousWithinAt
  set U : Set ℂ := V ∩ (fun w => f w / c) ⁻¹' Complex.slitPlane with hU
  have hUo : IsOpen U := hfc.isOpen_inter_preimage hVo Complex.isOpen_slitPlane
  have hzU : z ∈ U := ⟨hz1, by
    show f z / c ∈ Complex.slitPlane
    rw [← hc, div_self hc0]; exact Complex.one_mem_slitPlane⟩
  set G : ℂ → ℂ := fun w => -I*(Complex.log (f w / c) + Complex.log c) - π/2 with hG
  have hderiv : ∀ w ∈ U, HasDerivAt G (sech w) w := by
    intro w hw
    obtain ⟨hw1, hw2⟩ := hw
    have hw2 : f w / c ∈ Complex.slitPlane := hw2
    have hw1' : 1-I*Complex.exp w ≠ 0 := hw1
    have hfw : f w / c ≠ 0 := Complex.slitPlane_ne_zero hw2
    have hfw0 : f w ≠ 0 := fun h => hfw (by rw [h, zero_div])
    have hw3 : 1+I*Complex.exp w ≠ 0 := fun h => hfw0 (by simp [hfdef, h])
    have hcw : Complex.cosh w ≠ 0 := by
      intro h
      have := h2cosh w
      rw [h, hfac, mul_zero, zero_mul] at this
      exact mul_ne_zero hw1' hw3 this.symm
    have hN : HasDerivAt (fun w : ℂ => 1+I*Complex.exp w) (I*Complex.exp w) w :=
      ((Complex.hasDerivAt_exp w).const_mul I).const_add 1
    have hD : HasDerivAt (fun w : ℂ => 1-I*Complex.exp w) (-(I*Complex.exp w)) w :=
      ((Complex.hasDerivAt_exp w).const_mul I).const_sub 1
    have hf := (hN.div hD hw1').div_const c
    have hl := ((hf.clog hw2).add_const (Complex.log c)).const_mul (-I) |>.sub_const (π/2:ℂ)
    convert hl using 1
    simp only [sech]
    have he := Complex.exp_ne_zero w
    have h2 := h2cosh w
    simp only [Pi.div_apply]
    field_simp
    linear_combination (-(Complex.exp w)^2 + 2*Complex.cosh w*Complex.exp w)*hI - h2
  refine ⟨U, hUo, hzU, G, ?_, hderiv, ?_⟩
  · exact DifferentiableOn.analyticOnNhd
      (fun w hw => (hderiv w hw).differentiableAt.differentiableWithinAt) hUo
  · intro w hw
    obtain ⟨hw1, hw2⟩ := hw
    have hw2 : f w / c ∈ Complex.slitPlane := hw2
    have hw1' : 1-I*Complex.exp w ≠ 0 := hw1
    have hfw : f w / c ≠ 0 := Complex.slitPlane_ne_zero hw2
    set L := Complex.log (f w / c) + Complex.log c with hL
    have hexpL : Complex.exp L = f w := by
      rw [hL, Complex.exp_add, Complex.exp_log hfw, Complex.exp_log hc0]; field_simp
    set θ := G w/2+π/4 with hθ
    have hθI : θ*I = L/2 := by
      rw [hθ, hG]; simp only; linear_combination (-L/2)*hI
    set E := Complex.exp (L/2) with hE
    have hE2 : E^2 = f w := by rw [hE, ← Complex.exp_nat_mul]; push_cast; rw [← hexpL]; ring_nf
    have h1 : Complex.cos θ + Complex.sin θ*I = E := by rw [Complex.cos_add_sin_I, hθI]
    have h2 : (Complex.cos θ - Complex.sin θ*I)*E = 1 := by
      rw [Complex.cos_sub_sin_I, hE, ← Complex.exp_add, show -θ*I + L/2 = 0 by
        linear_combination -hθI]
      simp
    have hff : f w*(1-I*Complex.exp w) = 1+I*Complex.exp w := div_mul_cancel₀ _ hw1'
    set u := Complex.exp w
    set s := Complex.sin θ
    set k := Complex.cos θ
    have e1 : 2*E*(s*I) = E^2-1 := by linear_combination E*h1 - h2
    have e2 : 2*E*k = E^2+1 := by linear_combination E*h1 + h2
    have key : 2*E*(s*I - I*u*k) = 0 := by
      linear_combination e1 - I*u*e2 + (1-I*u)*hE2 + hff
    have hE0 : E ≠ 0 := Complex.exp_ne_zero _
    have hsk : s = u*k := by
      have := (mul_eq_zero.mp key).resolve_left (mul_ne_zero two_ne_zero hE0)
      have : I*(s-u*k) = 0 := by linear_combination this
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left Complex.I_ne_zero)
    have hk : k ≠ 0 := by
      intro h0
      rw [h0, mul_zero, hE2] at e2
      have hf1 : f w = -1 := by linear_combination -e2
      rw [hf1] at hff
      have : (2:ℂ) = 0 := by linear_combination -hff
      norm_num at this
    rw [Complex.tan_eq_sin_div_cos]
    change s / k = u
    rw [hsk, mul_div_assoc, div_self hk, mul_one]

/-- Oddness of all inverse-tanh branches includes the two values on each cut. -/
@[dlmf 4.37.E12]
theorem arctanh_values_neg (z : ℂ) :
    (fun w : ℂ => -w) '' arctanhValues z=arctanhValues (-z) := by
  ext w
  constructor
  · rintro ⟨a, ⟨hc, ht⟩, rfl⟩
    exact ⟨by rwa [Complex.cosh_neg], by rw [Complex.tanh_neg, ht]⟩
  · rintro ⟨hc, ht⟩
    refine ⟨-w, ⟨by rwa [Complex.cosh_neg], by rw [Complex.tanh_neg, ht, neg_neg]⟩, neg_neg w⟩

/-- Oddness of all inverse-coth branches includes the two cut values at zero. -/
@[dlmf 4.37.E15]
theorem arccoth_values_neg (z : ℂ) :
    (fun w : ℂ => -w) '' arccothValues z=arccothValues (-z) := by
  have hneg : ∀ w, coth (-w) = -coth w := fun w => by
    simp [coth, Complex.cosh_neg, Complex.sinh_neg, div_neg]
  ext w
  constructor
  · rintro ⟨a, ⟨hs, ht⟩, rfl⟩
    exact ⟨by rwa [Complex.sinh_neg, neg_ne_zero], by rw [hneg, ht]⟩
  · rintro ⟨hs, ht⟩
    refine ⟨-w, ⟨by rwa [Complex.sinh_neg, neg_ne_zero], by rw [hneg, ht, neg_neg]⟩, neg_neg w⟩

/-- The rectangular-hyperbola equation delimiting the transformed inverse-tanh series. -/
@[dlmf 4.38.E8]
theorem arctanh_transformed_boundary (z : ℂ) :
    (z^2).re=1/2 ↔ z.re^2-z.im^2=1/2 := by
  simp only [pow_two, Complex.mul_re]

/-- The regular endpoint of the principal inverse cosh is included in its logarithmic formulas. -/
@[dlmf 4.37.E19, dlmf 4.37.E21]
theorem arccosh_one : arccosh 1=0 := by
  simp [arccosh]

/-- At zero inverse coth has the finite half-period family; reciprocal zero is not totalized inside the inverse. -/
@[dlmf 4.37.E6, dlmf 4.37.E9]
theorem arccoth_zero_values :
    arccothValues 0=Set.range (fun k : ℤ => ((k:ℂ)+1/2)*π*I) := by
  ext w
  simp only [Set.mem_range]
  constructor
  · rintro ⟨hs, ht⟩
    rw [coth, div_eq_zero_iff] at ht
    obtain ⟨k, hk⟩ := (cosh_zeros w).mp (ht.resolve_right hs)
    exact ⟨k, hk.symm⟩
  · rintro ⟨k, rfl⟩
    have hc : Complex.cosh (((k:ℂ)+1/2)*π*I) = 0 := (cosh_zeros _).mpr ⟨k, rfl⟩
    refine ⟨?_, by rw [coth, hc, zero_div]⟩
    intro hs
    have := Complex.cosh_sq_sub_sinh_sq (((k:ℂ)+1/2)*π*I)
    rw [hc, hs] at this; norm_num at this

/-- Continued inverse-sinh branches have the corresponding continued primitive. -/
theorem continued_antiderivative_arcsinh {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z∈U)
    {A : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A U)
    (hinv : ∀ w∈U, Complex.sinh (A w)=w) (hcrit : z≠I ∧ z≠ -I) :
    HasDerivAt (fun w => w*A w-Complex.cosh (A w)) (A z) z := by
  have hdA:=(hA z hz).differentiableAt.hasDerivAt
  have hd:=((hasDerivAt_id z).mul hdA).sub hdA.ccosh
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply]
    rw [hinv z hz]
    ring

/-- Continued inverse-cosh branches have the corresponding continued primitive. -/
theorem continued_antiderivative_arccosh {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z∈U)
    {A : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A U)
    (hinv : ∀ w∈U, Complex.cosh (A w)=w) (hcrit : z≠1 ∧ z≠ -1) :
    HasDerivAt (fun w => w*A w-Complex.sinh (A w)) (A z) z := by
  have hdA:=(hA z hz).differentiableAt.hasDerivAt
  have hd:=((hasDerivAt_id z).mul hdA).sub hdA.csinh
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply]
    rw [hinv z hz]
    ring

/-- Continued inverse-tanh and logarithm branches have the corresponding primitive. -/
theorem continued_antiderivative_arctanh {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z∈U)
    {A L : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A U) (hL : AnalyticOnNhd ℂ L U)
    (hinv : ∀ w∈U, Complex.tanh (A w)=w) (hpole : ∀ w∈U, Complex.cosh (A w)≠0)
    (hlog : ∀ w∈U, Complex.exp (L w)=Complex.cosh (A w)) :
    HasDerivAt (fun w => w*A w-L w) (A z) z := by
  have dA := (hA z hz).differentiableAt.hasDerivAt
  have dL := (hL z hz).differentiableAt.hasDerivAt
  have e := hypR4_deriv_eq hU hz dL.cexp dA.ccosh hlog
  rw [hlog z hz] at e
  have hc := hpole z hz
  have hlz : deriv L z = z*deriv A z := by
    calc deriv L z = Complex.sinh (A z)/Complex.cosh (A z)*deriv A z := by
          field_simp; linear_combination e
      _ = z*deriv A z := by rw [← Complex.tanh_eq_sinh_div_cosh, hinv z hz]
  have hd := ((hasDerivAt_id z).mul dA).sub dL
  convert hd using 1
  · rfl
  · dsimp only [id]
    rw [hlz]; ring

/-- Continued inverse-csch branches use a matching inverse-sinh square-root branch. -/
theorem continued_antiderivative_arccsch {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z∈U)
    {A B : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A U) (hB : AnalyticOnNhd ℂ B U)
    (hinv : ∀ w∈U, csch (A w)=w) (hpole : ∀ w∈U, Complex.sinh (A w)≠0)
    (hbinv : ∀ w∈U, Complex.sinh (B w)=w)
    (hbranch : ∀ w∈U, Complex.cosh (B w)=w*Complex.cosh (A w))
    (hcrit : z≠0 ∧ z≠I ∧ z≠ -I) :
    HasDerivAt (fun w => w*A w+B w) (A z) z := by
  have dA := (hA z hz).differentiableAt.hasDerivAt
  have dB := (hB z hz).differentiableAt.hasDerivAt
  have hs := hpole z hz
  have e1 := hypR4_deriv_eq hU hz ((hasDerivAt_csch hs).comp z dA) (hasDerivAt_id z) hinv
  have e2 := hypR4_deriv_eq hU hz dB.csinh (hasDerivAt_id z) hbinv
  rw [hbranch z hz] at e2
  have hcz := hinv z hz
  rw [csch] at hcz
  have hc0 : Complex.cosh (A z) ≠ 0 := by
    intro h; rw [h, mul_zero, zero_mul] at e2; exact zero_ne_one e2
  have hsz : Complex.sinh (A z) = z⁻¹ := by
    have := congrArg Inv.inv hcz; rwa [inv_inv] at this
  have hz0 : z ≠ 0 := hcrit.1
  have key : z*deriv A z + deriv B z = 0 := by
    rw [csch, coth, hsz, inv_inv, div_inv_eq_mul] at e1
    apply mul_left_cancel₀ (mul_ne_zero hz0 hc0)
    linear_combination -e1 + e2
  have hd := ((hasDerivAt_id z).mul dA).add dB
  convert hd using 1
  · rfl
  · dsimp only [id]
    linear_combination -key

/-- Continued inverse-sech branches use a matching inverse-sine square-root branch. -/
theorem continued_antiderivative_arcsech {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z∈U)
    {A B : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A U) (hB : AnalyticOnNhd ℂ B U)
    (hinv : ∀ w∈U, sech (A w)=w) (hpole : ∀ w∈U, Complex.cosh (A w)≠0)
    (hbinv : ∀ w∈U, Complex.sin (B w)=w)
    (hbranch : ∀ w∈U, Complex.cos (B w)=w*Complex.sinh (A w))
    (hcrit : z≠0 ∧ z≠1 ∧ z≠ -1) :
    HasDerivAt (fun w => w*A w+B w) (A z) z := by
  have dA := (hA z hz).differentiableAt.hasDerivAt
  have dB := (hB z hz).differentiableAt.hasDerivAt
  have hc := hpole z hz
  have e1 := hypR4_deriv_eq hU hz ((hasDerivAt_sech hc).comp z dA) (hasDerivAt_id z) hinv
  have e2 := hypR4_deriv_eq hU hz dB.csin (hasDerivAt_id z) hbinv
  rw [hbranch z hz] at e2
  have hcz := hinv z hz
  rw [sech] at hcz
  have hs0 : Complex.sinh (A z) ≠ 0 := by
    intro h; rw [h, mul_zero, zero_mul] at e2; exact zero_ne_one e2
  have hcz' : Complex.cosh (A z) = z⁻¹ := by
    have := congrArg Inv.inv hcz; rwa [inv_inv] at this
  have hz0 : z ≠ 0 := hcrit.1
  have key : z*deriv A z + deriv B z = 0 := by
    rw [sech, Complex.tanh_eq_sinh_div_cosh, hcz', inv_inv, div_inv_eq_mul] at e1
    apply mul_left_cancel₀ (mul_ne_zero hz0 hs0)
    linear_combination -e1 + e2
  have hd := ((hasDerivAt_id z).mul dA).add dB
  convert hd using 1
  · rfl
  · dsimp only [id]
    linear_combination -key

/-- Continued inverse-coth branches and a continued logarithm give the full complex primitive. -/
theorem continued_antiderivative_arccoth {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z∈U)
    {A L : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A U) (hL : AnalyticOnNhd ℂ L U)
    (hinv : ∀ w∈U, coth (A w)=w) (hpole : ∀ w∈U, Complex.sinh (A w)≠0)
    (hlog : ∀ w∈U, Complex.exp (2*L w)=w^2-1) :
    HasDerivAt (fun w => w*A w+L w) (A z) z := by
  have dA := (hA z hz).differentiableAt.hasDerivAt
  have dL := (hL z hz).differentiableAt.hasDerivAt
  have hs := hpole z hz
  have e1 := hypR4_deriv_eq hU hz ((hasDerivAt_coth hs).comp z dA) (hasDerivAt_id z) hinv
  have e2 := hypR4_deriv_eq hU hz (dL.const_mul 2).cexp ((hasDerivAt_id z).pow 2 |>.sub_const 1) hlog
  rw [hlog z hz] at e2
  have hcz := hinv z hz
  have hq : z^2-1 ≠ 0 := by rw [← hlog z hz]; exact Complex.exp_ne_zero _
  have hcs : csch (A z)^2 = z^2-1 := by
    have h : csch (A z)^2 = coth (A z)^2-1 := by
      rw [csch, coth]
      field_simp
      first | linear_combination Complex.cosh_sq_sub_sinh_sq (A z) |
        linear_combination -Complex.cosh_sq_sub_sinh_sq (A z)
    rw [h, hcz]
  have key : z*deriv A z + deriv L z = 0 := by
    rw [hcs] at e1
    apply mul_left_cancel₀ hq
    norm_num at e2
    linear_combination (-z)*e1 + e2/2
  have hd := ((hasDerivAt_id z).mul dA).add dL
  convert hd using 1
  · rfl
  · dsimp only [id]
    linear_combination -key

end DLMF.Elementary

end
