/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Basic
public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Schläfli's integral for `J_ν` (DLMF 10.9.6)

For complex `ν` and `ℜ z > 0`,
`J_ν(z) = π⁻¹ ∫₀^π cos(z sin θ - νθ) dθ - (sin νπ / π) ∫₀^∞ e^{-z sinh t - νt} dt`.

The integer case is Bessel's integral (`besselJ_int_eq_integral_cos`, DLMF 10.9.2).

## Method

With `c = z/2`, expand `e^{-c e^{-iθ}}` and `e^{c e^{-t}}` in powers of `c`. Termwise, Schläfli's
integral becomes `∑ₖ (-c)ᵏ/k! G(ν+k, c)`, where
`G(a, c) = (2π)⁻¹ ∫_{-π}^{π} e^{c e^{iθ} - iaθ} dθ - (sin πa/π) ∫₀^∞ e^{-c eᵗ - at} dt`
is Hankel's loop integral for `1/Γ` in the coordinate `u = e^w`. We show `G(a, c) = cᵃ/Γ(a+1)`
(`schlafli_gamma`):

* for `-1 < ℜ a < 0` and real `c > 0`, the circle part is `-2 sin πa ∫₀¹ u^{-a-1} e^{-cu} du`
  (termwise), the ray part is `∫₁^∞ u^{-a-1} e^{-cu} du` (substitution `u = eᵗ`), and Euler's
  integral and the reflection formula finish;
* both sides are entire in `a` and holomorphic in `c` on `ℜ c > 0`
  (`Complex.differentiableOn_integral_Ioi_of_locally_dominated`), so the identity theorem extends
  the formula.

The termwise sum is then the `₀F₁` series of `J_ν`.

## Main results

* `DLMF.Bessel.schlafli_gamma`: Hankel's formula for `1/Γ` in exponential coordinates.
* `DLMF.Bessel.besselJ_eq_schlafli`: Schläfli's integral (DLMF 10.9.6).
* `DLMF.Bessel.angular_sub_besselJ_eq_schlafli`: the difference form used for the Anger function.
* `DLMF.Bessel.integrableOn_schlafli`, `DLMF.Bessel.differentiable_schlafli_order`: integrability
  and holomorphy in the order of the radial integral.
* `DLMF.Bessel.tendsto_intervalIntegral_schlafliBoundary`: convergence of the radial integral as
  an improper integral for `ℜ μ > 0`, `ℜ w ≥ 0`, `w ≠ 0`, with continuity of its value.
-/

@[expose] public section

open Complex MeasureTheory Set Filter
open scoped Real Topology Nat Interval

noncomputable section

namespace DLMF.Bessel


/-- Gaussian-type bound for the ray integrand. -/
theorem norm_exp_schlafliRay_le {δ M : ℝ} (hδ : 0 < δ) {a c : ℂ} (hc : δ ≤ c.re) (ha : -M ≤ a.re)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (-(c * Real.exp t) - a * t)‖ ≤ Real.exp ((M + 1) ^ 2 / (2 * δ)) * Real.exp (-t) := by
  rw [norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hre : (-(c * (Real.exp t : ℂ)) - a * t).re = -(c.re * Real.exp t) - a.re * t := by
    simp [mul_re, Complex.exp_ofReal_re]
  rw [hre]
  have he := Real.quadratic_le_exp_of_nonneg ht
  have h1 : δ * (t ^ 2 / 2) ≤ c.re * Real.exp t := by
    have : t ^ 2 / 2 ≤ Real.exp t := by nlinarith
    nlinarith [Real.exp_pos t]
  have h2 : -(a.re * t) ≤ M * t := by nlinarith
  have h3 : (M + 1) * t - δ * (t ^ 2 / 2) ≤ (M + 1) ^ 2 / (2 * δ) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (δ * t - (M + 1))]
  nlinarith

/-- The dominating function is integrable on the half-line. -/
theorem integrableOn_schlafli_bound (K : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp K * Real.exp (-t)) (Ioi 0) := by
  have := (exp_neg_integrableOn_Ioi 0 one_pos).const_mul (Real.exp K)
  simp only [neg_mul, one_mul] at this; exact this

/-- The ray integrand `e^{-c eᵗ - a t}` is integrable on `(0, ∞)` for `ℜ c > 0`. -/
theorem integrableOn_schlafliRay {a c : ℂ} (hc : 0 < c.re) :
    IntegrableOn (fun t : ℝ => exp (-(c * Real.exp t) - a * t)) (Ioi 0) := by
  refine (integrableOn_schlafli_bound ((|a.re| + 1) ^ 2 / (2 * c.re))).mono' ?_ ?_
  · exact (by fun_prop : Continuous fun t : ℝ => exp (-(c * Real.exp t) - a * t))
      |>.aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    exact norm_exp_schlafliRay_le hc le_rfl (by linarith [neg_abs_le a.re]) (le_of_lt ht)


/-- The circle part `∫_{-π}^{π} e^{c e^{iθ} - iaθ} dθ` of the Hankel loop in exponential
coordinates `u = e^w`. -/
def schlafliCircle (a c : ℂ) : ℂ := ∫ θ in (-π)..π, exp (c * exp (θ * I) - a * θ * I)

/-- The ray part `∫₀^∞ e^{-c eᵗ - a t} dt` of the Hankel loop in exponential coordinates. -/
def schlafliRay (a c : ℂ) : ℂ := ∫ t in Ioi (0:ℝ), exp (-(c * Real.exp t) - a * t)

/-- `∫_{-π}^{π} e^{ibθ} dθ = 2 sin(πb)/b` for `b ≠ 0`. -/
theorem integral_exp_mul_I_symm {b : ℂ} (hb : b ≠ 0) :
    ∫ θ in (-π)..π, exp (b * θ * I) = 2 * sin (π * b) / b := by
  have hc : b * I ≠ 0 := mul_ne_zero hb I_ne_zero
  have := integral_exp_mul_complex (a := -π) (b := π) hc
  have hf : (fun θ : ℝ => exp (b * θ * I)) = fun θ : ℝ => exp ((b * I) * θ) := by
    funext θ; ring_nf
  rw [hf, this, Complex.sin]
  push_cast
  field_simp
  ring_nf
  rw [I_sq]; ring_nf

/-- Termwise expansion of the circle integral in powers of `c`. -/
theorem hasSum_schlafliCircle (a c : ℂ) :
    HasSum (fun n : ℕ => c ^ n / n ! * ∫ θ in (-π)..π, exp ((n - a) * θ * I))
      (schlafliCircle a c) := by
  have hpt (θ : ℝ) : HasSum (fun n : ℕ => c ^ n / n ! * exp ((n - a) * θ * I))
      (exp (c * exp (θ * I) - a * θ * I)) := by
    have h := (NormedSpace.expSeries_div_hasSum_exp (c * exp (θ * I))).mul_right
      (exp (-(a * θ * I)))
    simp only [← exp_eq_exp_ℂ] at h
    rw [sub_eq_add_neg, exp_add]
    convert h using 1
    funext n
    rw [mul_pow, ← exp_nat_mul, mul_div_right_comm, mul_assoc (c ^ n / _), ← exp_add]
    ring_nf
  have hint := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := -π) (b := π)
    (F := fun (n : ℕ) (θ : ℝ) => c ^ n / n ! * exp ((n - a) * θ * I))
    (f := fun θ : ℝ => exp (c * exp (θ * I) - a * θ * I))
    (fun n _ => ‖c‖ ^ n / n ! * Real.exp (π * |a.im|))
    (fun n => (by fun_prop : Continuous fun θ : ℝ => c ^ n / n ! * exp ((n - a) * θ * I))
      |>.aestronglyMeasurable)
    (fun n => Eventually.of_forall fun θ hθ => by
      rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast, norm_exp]
      gcongr
      have hre : ((n - a) * θ * I).re = θ * a.im := by simp; ring
      rw [hre]
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hθ
      have : |θ| ≤ π := abs_le.2 ⟨hθ.1.le, hθ.2⟩
      calc θ * a.im ≤ |θ * a.im| := le_abs_self _
        _ = |θ| * |a.im| := abs_mul _ _
        _ ≤ π * |a.im| := by gcongr)
    (Eventually.of_forall fun _ _ =>
      (Real.summable_pow_div_factorial ‖c‖).mul_right _)
    intervalIntegrable_const
    (Eventually.of_forall fun θ _ => hpt θ)
  simp only [intervalIntegral.integral_const_mul] at hint
  exact hint


/-- Termwise expansion of the lower incomplete Gamma integral `∫₀¹ u^{-a-1} e^{-cu} du`. -/
theorem hasSum_schlafli_lowerGamma {a : ℂ} (ha : a.re < 0) (c : ℂ) :
    HasSum (fun n : ℕ => (-c) ^ n / n ! * (1 / (n - a)))
      (∫ u in (0:ℝ)..1, (u : ℂ) ^ (-a - 1) * exp (-(c * u))) := by
  have hpt (u : ℝ) (hu : 0 < u) : HasSum (fun n : ℕ => (-c) ^ n / n ! * (u : ℂ) ^ ((n : ℂ) - a - 1))
      ((u : ℂ) ^ (-a - 1) * exp (-(c * u))) := by
    have h := (NormedSpace.expSeries_div_hasSum_exp (-(c * u))).mul_left ((u : ℂ) ^ (-a - 1))
    simp only [← exp_eq_exp_ℂ] at h
    convert h using 1
    funext n
    have hu0 : (u : ℂ) ≠ 0 := ofReal_ne_zero.2 hu.ne'
    rw [show (n : ℂ) - a - 1 = (n : ℂ) + (-a - 1) by ring, cpow_add _ _ hu0, cpow_natCast,
      neg_mul_eq_neg_mul, mul_pow]
    ring
  have hr : -1 < -a.re - 1 + 0 := by linarith
  have hint := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := 0) (b := 1)
    (F := fun (n : ℕ) (u : ℝ) => (-c) ^ n / n ! * (u : ℂ) ^ ((n : ℂ) - a - 1))
    (f := fun u : ℝ => (u : ℂ) ^ (-a - 1) * exp (-(c * u)))
    (fun n u => ‖c‖ ^ n / n ! * u ^ (-a.re - 1))
    (fun n => ((intervalIntegral.intervalIntegrable_cpow' (by simp; linarith [Nat.cast_nonneg (α := ℝ) n])).const_mul
      ((-c) ^ n / n !)).aestronglyMeasurable)
    (fun n => Eventually.of_forall fun u hu => by
      rw [Set.uIoc_of_le zero_le_one] at hu
      rw [norm_mul, norm_div, norm_pow, norm_neg, Complex.norm_natCast,
        norm_cpow_eq_rpow_re_of_pos hu.1]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hu.1 hu.2 (by simp))
        (by positivity))
    (Eventually.of_forall fun _ _ =>
      (Real.summable_pow_div_factorial ‖c‖).mul_right _)
    (by
      simp_rw [tsum_mul_right]
      exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _)
    (by
      rw [ae_iff]
      refine measure_mono_null (t := {0}) ?_ (by simp)
      intro u hu
      simp only [Set.mem_ofPred_eq, not_imp] at hu
      by_contra h0
      rw [Set.uIoc_of_le zero_le_one] at hu
      exact hu.2 (hpt u hu.1.1))
  have hterm (n : ℕ) : ∫ u in (0:ℝ)..1, (-c) ^ n / n ! * (u : ℂ) ^ ((n : ℂ) - a - 1) =
      (-c) ^ n / n ! * (1 / (n - a)) := by
    have hna : (n : ℂ) - a ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith [Nat.cast_nonneg (α := ℝ) n]
    rw [intervalIntegral.integral_const_mul, integral_cpow (Or.inl (by simp; linarith [Nat.cast_nonneg (α := ℝ) n]))]
    rw [show (n : ℂ) - a - 1 + 1 = n - a by ring]
    simp [zero_cpow hna]
  simp only [hterm] at hint
  exact hint


/-- `sin(π(n - a)) = -(-1)ⁿ sin(πa)`. -/
theorem sin_pi_mul_nat_sub (n : ℕ) (a : ℂ) : sin (π * (n - a)) = -((-1) ^ n * sin (π * a)) := by
  have hc : cos ((n : ℂ) * π) = (-1) ^ n := by
    rw [← ofReal_natCast, ← ofReal_mul, ← ofReal_cos, Real.cos_nat_mul_pi]; push_cast; rfl
  rw [mul_sub, sin_sub, mul_comm (π : ℂ) n, sin_nat_mul_pi, hc]
  ring

/-- For `ℜ a < 0` the circle integral is a multiple of the lower incomplete Gamma integral. -/
theorem schlafliCircle_eq_lower {a : ℂ} (ha : a.re < 0) (c : ℂ) :
    schlafliCircle a c =
      -2 * sin (π * a) * ∫ u in (0:ℝ)..1, (u : ℂ) ^ (-a - 1) * exp (-(c * u)) := by
  refine (hasSum_schlafliCircle a c).unique ?_
  convert (hasSum_schlafli_lowerGamma ha c).mul_left (-2 * sin (π * a)) using 1
  funext n
  have hna : (n : ℂ) - a ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith [Nat.cast_nonneg (α := ℝ) n]
  rw [integral_exp_mul_I_symm hna, sin_pi_mul_nat_sub, neg_pow]
  field_simp
  ring

/-- The substitution `u = eᵗ` turns the ray integral into an upper incomplete Gamma integral. -/
theorem schlafliRay_eq_upper (a c : ℂ) :
    schlafliRay a c = ∫ u in Ioi (1:ℝ), (u : ℂ) ^ (-a - 1) * exp (-(c * u)) := by
  have h := integral_comp_exp_Ioi (fun u : ℝ => (u : ℂ) ^ (-a - 1) * exp (-(c * u))) 0
  rw [Real.exp_zero] at h
  rw [← h, schlafliRay]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [Complex.real_smul]
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.2 (Real.exp_pos t).ne'), ← ofReal_log (Real.exp_pos t).le,
    Real.log_exp, ofReal_exp, ← exp_add, ← exp_add]
  ring_nf

/-- `sin(πa) ≠ 0` in the strip `-1 < ℜ a < 0`. -/
theorem sin_pi_mul_ne_zero_of_strip {a : ℂ} (ha0 : a.re < 0) (ha1 : -1 < a.re) :
    sin (π * a) ≠ 0 := by
  rw [Ne, Complex.sin_eq_zero_iff]
  rintro ⟨k, hk⟩
  have h := congrArg Complex.re hk
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, intCast_re, intCast_im] at h
  have hk' : a.re = k := by
    have := Real.pi_pos; field_simp at h; linarith
  rw [hk'] at ha0 ha1
  have h1 : k < 0 := by exact_mod_cast ha0
  have h2 : -1 < k := by exact_mod_cast ha1
  omega

/-- The Hankel-type formula for `1/Γ(a+1)` in the strip `-1 < ℜ a < 0` and for real `c > 0`. -/
theorem schlafli_gamma_strip {a : ℂ} (ha0 : a.re < 0) (ha1 : -1 < a.re) {c : ℝ} (hc : 0 < c) :
    1 / (2 * π) * schlafliCircle a c - sin (π * a) / π * schlafliRay a c =
      (c : ℂ) ^ a * (Gamma (a + 1))⁻¹ := by
  set g : ℝ → ℂ := fun u => (u : ℂ) ^ (-a - 1) * exp (-((c : ℂ) * u)) with hg
  have hlow : IntegrableOn g (Ioc 0 1) := by
    have h1 : IntervalIntegrable g volume 0 1 := by
      refine (intervalIntegral.intervalIntegrable_cpow' (by simp; linarith)).mul_continuousOn ?_
      exact (by fun_prop : Continuous fun u : ℝ => exp (-((c : ℂ) * u))).continuousOn
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 h1
  have hup : IntegrableOn g (Ioi 1) := by
    refine (exp_neg_integrableOn_Ioi 1 hc).mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun u hu => ?_) measurableSet_Ioi
      have hu0 : (0:ℝ) < u := lt_trans one_pos hu
      refine ContinuousAt.continuousWithinAt ?_
      refine ContinuousAt.mul ?_ (by fun_prop)
      exact (continuous_ofReal.continuousAt).cpow continuousAt_const (ofReal_mem_slitPlane.2 hu0)
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
      have hu0 : (0:ℝ) < u := lt_trans one_pos hu
      rw [hg]; simp only
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hu0, norm_exp]
      have : ((-((c : ℂ) * u))).re = -c * u := by simp
      rw [this]
      have hp : u ^ ((-a - 1).re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt hu)
        (by simp; linarith)
      calc u ^ ((-a - 1).re) * Real.exp (-c * u) ≤ 1 * Real.exp (-c * u) := by gcongr
        _ = _ := one_mul _
  have hsplit : (∫ u in (0:ℝ)..1, g u) + ∫ u in Ioi (1:ℝ), g u = ∫ u in Ioi (0:ℝ), g u := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← setIntegral_union (Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi hlow hup, Ioc_union_Ioi_eq_Ioi zero_le_one]
  have hgam := integral_cpow_mul_exp_neg_mul_Ioi (a := -a) (r := c) (by simp; linarith) hc
  rw [schlafliCircle_eq_lower ha0, schlafliRay_eq_upper]
  change 1 / (2 * π) * (-2 * sin (π * a) * ∫ u in (0:ℝ)..1, g u) -
    sin (π * a) / π * ∫ u in Ioi (1:ℝ), g u = _
  have hcomb : 1 / (2 * π) * (-2 * sin (π * a) * ∫ u in (0:ℝ)..1, g u) -
      sin (π * a) / π * ∫ u in Ioi (1:ℝ), g u =
      -(sin (π * a) / π) * ((∫ u in (0:ℝ)..1, g u) + ∫ u in Ioi (1:ℝ), g u) := by
    have : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    field_simp; ring
  rw [hcomb, hsplit, hgam]
  have hc' : (c : ℂ).arg ≠ π := by rw [arg_ofReal_of_nonneg hc.le]; exact Real.pi_ne_zero.symm
  rw [one_div, inv_cpow _ _ hc', cpow_neg, inv_inv]
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (-a)
  rw [show (1 : ℂ) - -a = a + 1 by ring, mul_neg, Complex.sin_neg] at hrefl
  have hs := sin_pi_mul_ne_zero_of_strip ha0 ha1
  have hG : Gamma (a + 1) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [eq_div_iff (neg_ne_zero.2 hs)] at hrefl
  field_simp
  linear_combination (c : ℂ) ^ a * hrefl


/-- A uniform bound for the circle integrand on `[-π, π]`. -/
theorem norm_exp_schlafliCircle_le (a c : ℂ) {θ : ℝ} (hθ : |θ| ≤ π) :
    ‖exp (c * exp (θ * I) - a * θ * I)‖ ≤ Real.exp (‖c‖ + ‖a‖ * π) := by
  rw [norm_exp]
  apply Real.exp_le_exp.mpr
  refine (re_le_norm _).trans ((norm_sub_le _ _).trans ?_)
  rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_mul, norm_mul, norm_I, mul_one,
    norm_real, Real.norm_eq_abs]
  gcongr

/-- Points of `Ι (-π) π` satisfy `|θ| ≤ π`. -/
theorem abs_le_pi_of_mem_uIoc {θ : ℝ} (hθ : θ ∈ Ι (-π) π) : |θ| ≤ π := by
  rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hθ
  exact abs_le.2 ⟨hθ.1.le, hθ.2⟩

/-- The circle integral is entire in the order. -/
theorem differentiable_schlafliCircle_left (c : ℂ) :
    Differentiable ℂ fun a => schlafliCircle a c := by
  have h := Complex.differentiableOn_intervalIntegral_of_locally_dominated (U := univ)
    (Φ := fun a (θ : ℝ) => exp (c * exp (θ * I) - a * θ * I)) isOpen_univ (ν := volume) (-π) π
    (fun a _ => (by fun_prop : Continuous fun θ : ℝ => exp (c * exp (θ * I) - a * θ * I))
      |>.aestronglyMeasurable)
    (Eventually.of_forall fun θ => (by fun_prop : Differentiable ℂ fun a : ℂ =>
      exp (c * exp (θ * I) - a * θ * I)).differentiableOn)
    (fun a0 _ => ⟨Metric.ball a0 1, Metric.ball_mem_nhds _ one_pos,
      fun _ => Real.exp (‖c‖ + (‖a0‖ + 1) * π), intervalIntegrable_const.def', by
        refine (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun θ hθ y hy => ?_)
        refine (norm_exp_schlafliCircle_le y c (abs_le_pi_of_mem_uIoc hθ)).trans ?_
        dsimp only
        gcongr
        have := norm_le_norm_add_norm_sub' y a0
        rw [Metric.mem_ball, dist_eq_norm] at hy
        linarith⟩)
  exact fun a => (h a (mem_univ a)).differentiableAt (isOpen_univ.mem_nhds (mem_univ a))

/-- The circle integral is entire in `c`. -/
theorem differentiable_schlafliCircle_right (a : ℂ) :
    Differentiable ℂ fun c => schlafliCircle a c := by
  have h := Complex.differentiableOn_intervalIntegral_of_locally_dominated (U := univ)
    (Φ := fun c (θ : ℝ) => exp (c * exp (θ * I) - a * θ * I)) isOpen_univ (ν := volume) (-π) π
    (fun c _ => (by fun_prop : Continuous fun θ : ℝ => exp (c * exp (θ * I) - a * θ * I))
      |>.aestronglyMeasurable)
    (Eventually.of_forall fun θ => (by fun_prop : Differentiable ℂ fun c : ℂ =>
      exp (c * exp (θ * I) - a * θ * I)).differentiableOn)
    (fun c0 _ => ⟨Metric.ball c0 1, Metric.ball_mem_nhds _ one_pos,
      fun _ => Real.exp ((‖c0‖ + 1) + ‖a‖ * π), intervalIntegrable_const.def', by
        refine (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun θ hθ y hy => ?_)
        refine (norm_exp_schlafliCircle_le a y (abs_le_pi_of_mem_uIoc hθ)).trans ?_
        dsimp only
        gcongr
        have := norm_le_norm_add_norm_sub' y c0
        rw [Metric.mem_ball, dist_eq_norm] at hy
        linarith⟩)
  exact fun c => (h c (mem_univ c)).differentiableAt (isOpen_univ.mem_nhds (mem_univ c))

/-- The ray integral is entire in the order for `ℜ c > 0`. -/
theorem differentiable_schlafliRay_left {c : ℂ} (hc : 0 < c.re) :
    Differentiable ℂ fun a => schlafliRay a c := by
  have h := Complex.differentiableOn_integral_Ioi_of_locally_dominated (U := univ)
    (Φ := fun a (t : ℝ) => exp (-(c * Real.exp t) - a * t)) isOpen_univ 0
    (fun a _ => (by fun_prop : Continuous fun t : ℝ => exp (-(c * Real.exp t) - a * t))
      |>.aestronglyMeasurable)
    (Eventually.of_forall fun t => (by fun_prop : Differentiable ℂ fun a : ℂ =>
      exp (-(c * Real.exp t) - a * t)).differentiableOn)
    (fun a0 _ => ⟨Metric.ball a0 1, Metric.ball_mem_nhds _ one_pos, _,
      integrableOn_schlafli_bound ((‖a0‖ + 1 + 1) ^ 2 / (2 * c.re)), by
        refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht y hy => ?_)
        refine norm_exp_schlafliRay_le hc le_rfl ?_ (le_of_lt ht)
        have := norm_le_norm_add_norm_sub' y a0
        rw [Metric.mem_ball, dist_eq_norm] at hy
        have := neg_abs_le y.re
        have := abs_re_le_norm y
        linarith⟩)
  exact fun a => (h a (mem_univ a)).differentiableAt (isOpen_univ.mem_nhds (mem_univ a))

/-- The ray integral is holomorphic in `c` on the right half-plane. -/
theorem differentiableOn_schlafliRay_right (a : ℂ) :
    DifferentiableOn ℂ (fun c => schlafliRay a c) {c | 0 < c.re} := by
  have hU : IsOpen {c : ℂ | 0 < c.re} := isOpen_lt continuous_const continuous_re
  exact Complex.differentiableOn_integral_Ioi_of_locally_dominated (U := {c | 0 < c.re})
    (Φ := fun c (t : ℝ) => exp (-(c * Real.exp t) - a * t)) hU 0
    (fun c _ => (by fun_prop : Continuous fun t : ℝ => exp (-(c * Real.exp t) - a * t))
      |>.aestronglyMeasurable)
    (Eventually.of_forall fun t => (by fun_prop : Differentiable ℂ fun c : ℂ =>
      exp (-(c * Real.exp t) - a * t)).differentiableOn)
    (fun c0 hc0 => ⟨Metric.ball c0 (c0.re / 2), Metric.ball_mem_nhds _ (by simp at hc0; linarith),
      _, integrableOn_schlafli_bound ((|a.re| + 1) ^ 2 / (2 * (c0.re / 2))), by
        refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht y hy => ?_)
        simp only [mem_ofPred_eq] at hc0
        refine norm_exp_schlafliRay_le (by linarith) ?_ (by linarith [neg_abs_le a.re]) (le_of_lt ht)
        rw [Metric.mem_ball, dist_eq_norm] at hy
        have := abs_re_le_norm (y - c0)
        rw [sub_re] at this
        have := neg_abs_le (y.re - c0.re)
        linarith⟩)


/-- The Hankel-type formula for `1/Γ(a+1)` for all `a` and real `c > 0`. -/
theorem schlafli_gamma_ofReal (a : ℂ) {r : ℝ} (hr : 0 < r) :
    1 / (2 * π) * schlafliCircle a r - sin (π * a) / π * schlafliRay a r =
      (r : ℂ) ^ a * (Gamma (a + 1))⁻¹ := by
  have hrc : (0 : ℝ) < (r : ℂ).re := by simpa using hr
  have hf : AnalyticOnNhd ℂ (fun a => 1 / (2 * π) * schlafliCircle a r -
      sin (π * a) / π * schlafliRay a r) univ := by
    refine analyticOnNhd_univ_iff_differentiable.2 ?_
    exact ((differentiable_schlafliCircle_left _).const_mul _).sub
      (((by fun_prop : Differentiable ℂ fun a : ℂ => sin (π * a) / π)).mul
        (differentiable_schlafliRay_left hrc))
  have hg : AnalyticOnNhd ℂ (fun a => (r : ℂ) ^ a * (Gamma (a + 1))⁻¹) univ := by
    refine analyticOnNhd_univ_iff_differentiable.2 fun a => ?_
    refine DifferentiableAt.mul ?_
      ((differentiable_one_div_Gamma.comp (differentiable_id.add_const (1:ℂ))) a)
    exact (differentiableAt_id).const_cpow (Or.inl (ofReal_ne_zero.2 hr.ne'))
  have hS : IsOpen {a : ℂ | a.re < 0 ∧ -1 < a.re} :=
    (isOpen_lt continuous_re continuous_const).inter (isOpen_lt continuous_const continuous_re)
  refine hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_univ (mem_univ (-1/2 : ℂ)) ?_
    (mem_univ a)
  filter_upwards [hS.mem_nhds (by norm_num : (-1/2 : ℂ) ∈ {a : ℂ | a.re < 0 ∧ -1 < a.re})]
    with b hb
  exact schlafli_gamma_strip hb.1 hb.2 hr

/-- Hankel's loop integral for `1/Γ` in exponential coordinates: for `ℜ c > 0` and all complex
`a`, `(2π)⁻¹ ∫_{-π}^{π} e^{c e^{iθ} - iaθ} dθ - (sin πa / π) ∫₀^∞ e^{-c eᵗ - at} dt = cᵃ / Γ(a+1)`.
This is DLMF 5.9.2 after the substitution `t = c e^w` on the Hankel loop. -/
theorem schlafli_gamma (a : ℂ) {c : ℂ} (hc : 0 < c.re) :
    1 / (2 * π) * schlafliCircle a c - sin (π * a) / π * schlafliRay a c =
      c ^ a * (Gamma (a + 1))⁻¹ := by
  set U := {c : ℂ | 0 < c.re}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  have hf : AnalyticOnNhd ℂ (fun c => 1 / (2 * π) * schlafliCircle a c -
      sin (π * a) / π * schlafliRay a c) U := by
    refine DifferentiableOn.analyticOnNhd ?_ hU
    exact ((differentiable_schlafliCircle_right a).const_mul _).differentiableOn.sub
      ((differentiableOn_schlafliRay_right a).const_mul _)
  have hg : AnalyticOnNhd ℂ (fun c => c ^ a * (Gamma (a + 1))⁻¹) U := by
    refine DifferentiableOn.analyticOnNhd (fun c hc => ?_) hU
    exact ((differentiableAt_id.cpow (differentiableAt_const a) (Or.inl hc)).mul_const
      _).differentiableWithinAt
  have hconv : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have h1 : (1 : ℂ) ∈ U := by simp [U]
  refine hf.eqOn_of_preconnected_of_frequently_eq hg hconv h1 ?_ hc
  have hu : Tendsto (fun n : ℕ => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (1 : ℝ)
      rw [add_zero] at this
      have h2 := (continuous_ofReal.tendsto _).comp this
      simpa [Function.comp_def] using h2
    · simp only [mem_compl_iff, mem_singleton_iff]
      intro h
      have h' : (1 + 1 / ((n:ℝ) + 1) : ℝ) = 1 := by exact_mod_cast h
      have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
      linarith
  refine hu.frequently (Frequently.of_forall fun n => ?_)
  exact schlafli_gamma_ofReal a (by positivity)


/-- A bound for the circle integrand depending only on `ℑ a`. -/
theorem norm_exp_schlafliCircle_le' (a c : ℂ) {θ : ℝ} (hθ : |θ| ≤ π) :
    ‖exp (c * exp (θ * I) - a * θ * I)‖ ≤ Real.exp (‖c‖ + |a.im| * π) := by
  rw [norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : (c * exp (θ * I) - a * θ * I).re = (c * exp (θ * I)).re + θ * a.im := by
    simp [mul_re]; ring
  rw [hre]
  have h1 : (c * exp (θ * I)).re ≤ ‖c‖ := by
    refine (re_le_norm _).trans ?_
    rw [norm_mul, norm_exp_ofReal_mul_I, mul_one]
  have h2 : θ * a.im ≤ |a.im| * π := by
    calc θ * a.im ≤ |θ * a.im| := le_abs_self _
      _ = |θ| * |a.im| := abs_mul _ _
      _ ≤ π * |a.im| := by gcongr
      _ = _ := mul_comm _ _
  linarith

/-- The angular part of Schläfli's integral, expanded in circle integrals. -/
theorem hasSum_schlafli_angular (ν z : ℂ) :
    HasSum (fun k : ℕ => (-(z / 2)) ^ k / k ! * schlafliCircle (ν + k) (z / 2))
      (∫ θ in (-π)..π, exp (I * (z * Real.sin θ - ν * θ))) := by
  set c := z / 2 with hc
  have hpt (θ : ℝ) : HasSum (fun k : ℕ => (-c) ^ k / k ! * exp (c * exp (θ * I) - (ν + k) * θ * I))
      (exp (I * (z * Real.sin θ - ν * θ))) := by
    have h := (NormedSpace.expSeries_div_hasSum_exp (-c * exp (-(θ * I)))).mul_left
      (exp (c * exp (θ * I) - ν * θ * I))
    simp only [← exp_eq_exp_ℂ] at h
    convert h using 1
    · funext k
      rw [mul_pow, ← exp_nat_mul, mul_div_right_comm, mul_comm (exp (c * exp (θ * I) - ν * θ * I)),
        mul_assoc ((-c) ^ k / _), ← exp_add]
      ring_nf
    · rw [← exp_add, ofReal_sin, Complex.sin, hc]
      congr 1
      ring_nf
      rw [I_sq]
      ring_nf
  have hint := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := -π) (b := π)
    (F := fun (k : ℕ) (θ : ℝ) => (-c) ^ k / k ! * exp (c * exp (θ * I) - (ν + k) * θ * I))
    (f := fun θ : ℝ => exp (I * (z * Real.sin θ - ν * θ)))
    (fun k _ => ‖c‖ ^ k / k ! * Real.exp (‖c‖ + |ν.im| * π))
    (fun k => (by fun_prop : Continuous fun θ : ℝ =>
      (-c) ^ k / k ! * exp (c * exp (θ * I) - (ν + k) * θ * I)).aestronglyMeasurable)
    (fun k => Eventually.of_forall fun θ hθ => by
      rw [norm_mul, norm_div, norm_pow, norm_neg, Complex.norm_natCast]
      gcongr
      have := norm_exp_schlafliCircle_le' (ν + k) c (abs_le_pi_of_mem_uIoc hθ)
      simpa using this)
    (Eventually.of_forall fun _ _ =>
      (Real.summable_pow_div_factorial ‖c‖).mul_right _)
    intervalIntegrable_const
    (Eventually.of_forall fun θ _ => hpt θ)
  simp only [intervalIntegral.integral_const_mul] at hint
  exact hint

/-- The radial part of Schläfli's integral, expanded in ray integrals. -/
theorem hasSum_schlafli_radial (ν : ℂ) {z : ℂ} (hz : 0 < z.re) :
    HasSum (fun k : ℕ => (z / 2) ^ k / k ! * schlafliRay (ν + k) (z / 2))
      (∫ t in Ioi (0:ℝ), exp (-(z * Real.sinh t) - ν * t)) := by
  set c := z / 2 with hc
  have hcre : 0 < c.re := by simp [hc]; linarith
  have hpt (t : ℝ) : HasSum (fun k : ℕ => c ^ k / k ! * exp (-(c * Real.exp t) - (ν + k) * t))
      (exp (-(z * Real.sinh t) - ν * t)) := by
    have h := (NormedSpace.expSeries_div_hasSum_exp (c * exp (-(t:ℂ)))).mul_left
      (exp (-(c * Real.exp t) - ν * t))
    simp only [← exp_eq_exp_ℂ] at h
    convert h using 1
    · funext k
      rw [mul_pow, ← exp_nat_mul, mul_div_right_comm, mul_comm (exp (-(c * Real.exp t) - ν * t)),
        mul_assoc (c ^ k / _), ← exp_add]
      ring_nf
    · rw [← exp_add, ofReal_sinh, Complex.sinh, hc, ofReal_exp]
      congr 1
      ring_nf
  set K := (|ν.re| + 1) ^ 2 / (2 * c.re)
  have hint := MeasureTheory.hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Ioi (0:ℝ)))
    (F := fun (k : ℕ) (t : ℝ) => c ^ k / k ! * exp (-(c * Real.exp t) - (ν + k) * t))
    (f := fun t : ℝ => exp (-(z * Real.sinh t) - ν * t))
    (fun k t => ‖c‖ ^ k / k ! * (Real.exp K * Real.exp (-t)))
    (fun k => (by fun_prop : Continuous fun t : ℝ =>
      c ^ k / k ! * exp (-(c * Real.exp t) - (ν + k) * t)).aestronglyMeasurable)
    (fun k => (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => by
      rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
      gcongr
      have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
      have hν := neg_abs_le ν.re
      refine norm_exp_schlafliRay_le hcre le_rfl ?_ (le_of_lt ht)
      simp only [add_re, natCast_re]
      linarith))
    (Eventually.of_forall fun _ =>
      (Real.summable_pow_div_factorial ‖c‖).mul_right _)
    (by
      simp_rw [tsum_mul_right]
      exact (integrableOn_schlafli_bound K).const_mul _)
    (Eventually.of_forall fun t => hpt t)
  simp only [integral_const_mul] at hint
  exact hint


/-- Folding the symmetric angular integral. -/
theorem integral_cos_eq_symm_exp (ν z : ℂ) :
    1 / π * ∫ θ in (0:ℝ)..π, cos (z * Real.sin θ - ν * θ) =
      1 / (2 * π) * ∫ θ in (-π)..π, exp (I * (z * Real.sin θ - ν * θ)) := by
  set h : ℝ → ℂ := fun θ => exp (I * (z * Real.sin θ - ν * θ)) with hh
  have hc : Continuous h := by fun_prop
  have hneg : ∫ θ in (-π)..0, h θ = ∫ θ in (0:ℝ)..π, exp (-(I * (z * Real.sin θ - ν * θ))) := by
    rw [← neg_zero, ← intervalIntegral.integral_comp_neg, neg_zero]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [hh, Real.sin_neg]
    push_cast
    ring_nf
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (-π) 0) (hc.intervalIntegrable (μ := volume) 0 π)
  have hc' : Continuous fun θ : ℝ => exp (-(I * (z * Real.sin θ - ν * θ))) := by fun_prop
  rw [← hsplit, hneg, add_comm, ← intervalIntegral.integral_add
    (hc.intervalIntegrable (μ := volume) 0 π) (hc'.intervalIntegrable (μ := volume) 0 π)]
  have hcos : (fun θ : ℝ => h θ + exp (-(I * (z * Real.sin θ - ν * θ)))) =
      fun θ : ℝ => 2 * cos (z * Real.sin θ - ν * θ) := by
    funext θ
    simp only [hh, Complex.cos]
    ring_nf
  rw [hcos, intervalIntegral.integral_const_mul]
  have : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp

/-- **Schläfli's integral** for `J_ν` (DLMF 10.9.6), for complex order and `ℜ z > 0`. -/
@[dlmf 10.9.E6]
theorem besselJ_eq_schlafli (ν : ℂ) {z : ℂ} (hz : 0 < z.re) :
    besselJ ν z = (1 / π * ∫ θ in (0:ℝ)..π, cos (z * Real.sin θ - ν * θ)) -
      sin (ν * π) / π * ∫ t in Ioi (0:ℝ), exp (-(z * Real.sinh t) - ν * t) := by
  set c := z / 2 with hc
  have hcre : 0 < c.re := by simp [hc]; linarith
  have hc0 : c ≠ 0 := fun h => by simp [h] at hcre
  have hA := (hasSum_schlafli_angular ν z).mul_left (1 / (2 * π) : ℂ)
  have hR := (hasSum_schlafli_radial ν hz).mul_left (sin (ν * π) / π : ℂ)
  rw [integral_cos_eq_symm_exp]
  refine HasSum.unique ?_ (hA.sub hR)
  have hF := ((hasFPowerSeriesOnBall_regularized0F1 (ν + 1)).hasSum_mul_pow
    (z := -(c ^ 2)) (by simp)).mul_left (c ^ ν)
  rw [besselJ_eq_regularized, show z ^ 2 / 4 = c ^ 2 by rw [hc]; ring, show z / 2 = c from rfl]
  convert hF using 1
  funext k
  have hG := schlafli_gamma (ν + k) hcre
  have hsin : sin (ν * π) * c ^ k = (-c) ^ k * sin (π * (ν + k)) := by
    have hs : sin (π * (ν + k)) = (-1) ^ k * sin (ν * π) := by
      have hc' : cos ((k : ℂ) * π) = (-1) ^ k := by
        rw [← ofReal_natCast, ← ofReal_mul, ← ofReal_cos, Real.cos_nat_mul_pi]; push_cast; rfl
      rw [mul_add, sin_add, mul_comm (π : ℂ) k, sin_nat_mul_pi, hc']
      ring_nf
    rw [hs, neg_pow]
    ring_nf
    rw [mul_comm k 2, pow_mul]
    norm_num
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hkey : 1 / (2 * π) * ((-c) ^ k / k ! * schlafliCircle (ν + k) c) -
      sin (ν * π) / π * (c ^ k / k ! * schlafliRay (ν + k) c) =
      (-c) ^ k / k ! * (1 / (2 * π) * schlafliCircle (ν + k) c -
        sin (π * (ν + k)) / π * schlafliRay (ν + k) c) := by
    rw [show sin (ν * π) / π * (c ^ k / k ! * schlafliRay (ν + k) c) =
      (sin (ν * π) * c ^ k) / π / k ! * schlafliRay (ν + k) c by ring, hsin]
    ring
  rw [hkey, hG, regularizedHGFunCoeff_empty, cpow_add _ _ hc0, cpow_natCast,
    show ν + k + 1 = ν + 1 + k by ring, neg_pow c, neg_pow (c ^ 2)]
  ring_nf


/-- `e^{-z sinh t - νt} = e^{-(z/2)eᵗ - νt} e^{(z/2)e^{-t}}`. -/
theorem exp_schlafli_split (ν z : ℂ) (t : ℝ) :
    exp (-(z * Real.sinh t) - ν * t) =
      exp (-(z / 2 * Real.exp t) - ν * t) * exp (z / 2 * Real.exp (-t)) := by
  rw [← exp_add, ofReal_sinh, Complex.sinh, ofReal_exp, ofReal_exp, ofReal_neg]
  congr 1
  ring

/-- A dominating bound for the radial integrand of Schläfli's integral. -/
theorem norm_exp_schlafli_le {δ M : ℝ} (hδ : 0 < δ) {ν z : ℂ} (hz : δ ≤ (z / 2).re)
    (hν : -M ≤ ν.re) {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (-(z * Real.sinh t) - ν * t)‖ ≤
      Real.exp ‖z / 2‖ * (Real.exp ((M + 1) ^ 2 / (2 * δ)) * Real.exp (-t)) := by
  rw [exp_schlafli_split, norm_mul, mul_comm]
  gcongr
  · rw [norm_exp]
    refine Real.exp_le_exp.mpr ((re_le_norm _).trans ?_)
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    calc ‖z / 2‖ * Real.exp (-t) ≤ ‖z / 2‖ * 1 := by gcongr
      _ = _ := mul_one _
  · exact norm_exp_schlafliRay_le hδ hz hν ht

/-- The radial integrand of Schläfli's integral is integrable for `ℜ z > 0`. -/
theorem integrableOn_schlafli (ν : ℂ) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => exp (-(z * Real.sinh t) - ν * t)) (Ioi 0) := by
  have hc : 0 < (z / 2).re := by simp; linarith
  refine ((integrableOn_schlafli_bound ((|ν.re| + 1) ^ 2 / (2 * (z / 2).re))).const_mul
    (Real.exp ‖z / 2‖)).mono' ?_ ?_
  · exact (by fun_prop : Continuous fun t : ℝ => exp (-(z * Real.sinh t) - ν * t))
      |>.aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    exact norm_exp_schlafli_le hc le_rfl (neg_abs_le ν.re) (le_of_lt ht)

/-- The radial integral of Schläfli's integral is entire in the order. -/
theorem differentiable_schlafli_order {z : ℂ} (hz : 0 < z.re) :
    Differentiable ℂ fun ν => ∫ t in Ioi (0:ℝ), exp (-(z * Real.sinh t) - ν * t) := by
  have hc : 0 < (z / 2).re := by simp; linarith
  have h := Complex.differentiableOn_integral_Ioi_of_locally_dominated (U := univ)
    (Φ := fun ν (t : ℝ) => exp (-(z * Real.sinh t) - ν * t)) isOpen_univ 0
    (fun ν _ => (by fun_prop : Continuous fun t : ℝ => exp (-(z * Real.sinh t) - ν * t))
      |>.aestronglyMeasurable)
    (Eventually.of_forall fun t => (by fun_prop : Differentiable ℂ fun ν : ℂ =>
      exp (-(z * Real.sinh t) - ν * t)).differentiableOn)
    (fun ν0 _ => ⟨Metric.ball ν0 1, Metric.ball_mem_nhds _ one_pos, _,
      (integrableOn_schlafli_bound ((‖ν0‖ + 1 + 1) ^ 2 / (2 * (z / 2).re))).const_mul
        (Real.exp ‖z / 2‖), by
        refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht y hy => ?_)
        refine norm_exp_schlafli_le hc le_rfl ?_ (le_of_lt ht)
        have := norm_le_norm_add_norm_sub' y ν0
        rw [Metric.mem_ball, dist_eq_norm] at hy
        have := neg_abs_le y.re
        have := abs_re_le_norm y
        linarith⟩)
  exact fun a => (h a (mem_univ a)).differentiableAt (isOpen_univ.mem_nhds (mem_univ a))

/-- The improper Riemann form of the radial integral in Schläfli's integral. -/
theorem tendsto_intervalIntegral_schlafli (ν : ℂ) {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun R : ℝ => ∫ t in (0:ℝ)..R, exp (-(z * Real.sinh t) - ν * t)) atTop
      (𝓝 (∫ t in Ioi (0:ℝ), exp (-(z * Real.sinh t) - ν * t))) :=
  intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_schlafli ν hz) tendsto_id

/-- Schläfli's integral in difference form: the angular (Anger-type) integral minus `J_ν(z)`
is `sin(νπ)/π` times the radial integral (DLMF 10.9.6). -/
@[dlmf 10.9.E6]
theorem angular_sub_besselJ_eq_schlafli (ν : ℂ) {z : ℂ} (hz : 0 < z.re) :
    (1 / π * ∫ θ in (0:ℝ)..π, cos (z * Real.sin θ - ν * θ)) - besselJ ν z =
      sin (ν * π) / π * ∫ t in Ioi (0:ℝ), exp (-(z * Real.sinh t) - ν * t) := by
  rw [besselJ_eq_schlafli ν hz]
  ring


/-! ### The radial integral on the closed right half-plane

For `ℜ μ > 0` one integration by parts, with `cosh t e^{-w sinh t} = -w⁻¹ d/dt e^{-w sinh t}`,
gives an absolutely convergent form `schlafliBoundary μ w` of `∫₀^∞ e^{-w sinh t - μt} dt`
valid for `ℜ w ≥ 0`, `w ≠ 0`, and continuous there. It is used for the boundary case of the
associated Anger–Weber function. -/

/-- The kernel produced by one integration by parts in the radial Schläfli integral. -/
def schlafliKernel (μ w : ℂ) (t : ℝ) : ℂ :=
  exp (-(w * Real.sinh t) - μ * t) * (-(μ * Real.cosh t + Real.sinh t) / (Real.cosh t : ℂ) ^ 2)

/-- The value of the radial Schläfli integral on the closed right half-plane, after one
integration by parts. -/
def schlafliBoundary (μ w : ℂ) : ℂ := (1 + ∫ t in Ioi (0:ℝ), schlafliKernel μ w t) / w

/-- `cosh t ≠ 0` as a complex number. -/
theorem cosh_ofReal_ne_zero (t : ℝ) : (Real.cosh t : ℂ) ≠ 0 :=
  ofReal_ne_zero.2 (Real.cosh_pos t).ne'

/-- The integration-by-parts kernel is continuous in `t`. -/
theorem continuous_schlafliKernel (μ w : ℂ) : Continuous (schlafliKernel μ w) := by
  unfold schlafliKernel
  refine (by fun_prop : Continuous fun t : ℝ => exp (-(w * Real.sinh t) - μ * t)).mul ?_
  exact Continuous.div (by fun_prop) (by fun_prop) fun t => pow_ne_zero 2 (cosh_ofReal_ne_zero t)

/-- The derivative of `e^{-w sinh t - μt} / cosh t`. -/
theorem hasDerivAt_schlafli_ibp (μ w : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => exp (-(w * Real.sinh s) - μ * s) / (Real.cosh s : ℂ))
      (-w * exp (-(w * Real.sinh t) - μ * t) + schlafliKernel μ w t) t := by
  have h1 : HasDerivAt (fun s : ℝ => (Real.sinh s : ℂ)) (Real.cosh t : ℂ) t :=
    (Real.hasDerivAt_sinh t).ofReal_comp
  have h2 : HasDerivAt (fun s : ℝ => (Real.cosh s : ℂ)) (Real.sinh t : ℂ) t :=
    (Real.hasDerivAt_cosh t).ofReal_comp
  have h3 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
  have hE := ((h1.const_mul w).neg.sub (h3.const_mul μ)).cexp
  have h := hE.div h2 (cosh_ofReal_ne_zero t)
  convert h using 1
  simp only [Pi.sub_apply, Pi.neg_apply]
  rw [schlafliKernel]
  have hc := cosh_ofReal_ne_zero t
  field_simp
  ring

/-- For `ℜ w ≥ 0` and `t ≥ 0`, `|e^{-w sinh t - μt}| ≤ e^{-ℜμ t}`. -/
theorem norm_exp_schlafli_le_of_re_nonneg {μ w : ℂ} (hw : 0 ≤ w.re) {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (-(w * Real.sinh t) - μ * t)‖ ≤ Real.exp (-μ.re * t) := by
  rw [norm_exp]
  apply Real.exp_le_exp.mpr
  have : (-(w * (Real.sinh t : ℂ)) - μ * t).re = -(w.re * Real.sinh t) - μ.re * t := by
    simp [mul_re, Complex.sinh_ofReal_re]
  rw [this]
  have := Real.sinh_nonneg_iff.2 ht
  nlinarith

/-- A bound for the integration-by-parts kernel. -/
theorem norm_schlafliKernel_le {μ w : ℂ} (hw : 0 ≤ w.re) {t : ℝ} (ht : 0 ≤ t) :
    ‖schlafliKernel μ w t‖ ≤ (‖μ‖ + 1) * Real.exp (-μ.re * t) := by
  rw [schlafliKernel, norm_mul, mul_comm]
  gcongr
  swap
  · exact norm_exp_schlafli_le_of_re_nonneg hw ht
  · have hc := Real.cosh_pos t
    have hc1 := Real.one_le_cosh t
    have hs : |Real.sinh t| ≤ Real.cosh t := by
      rw [abs_le]; constructor <;> nlinarith [Real.cosh_sq t]
    rw [norm_div, norm_neg, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hc]
    rw [div_le_iff₀ (by positivity)]
    calc ‖μ * (Real.cosh t : ℂ) + Real.sinh t‖ ≤ ‖μ‖ * Real.cosh t + Real.cosh t := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos hc]
          gcongr
      _ = (‖μ‖ + 1) * Real.cosh t := by ring
      _ ≤ (‖μ‖ + 1) * Real.cosh t ^ 2 := by gcongr; nlinarith

/-- The integration-by-parts kernel is integrable for `ℜ μ > 0`, `ℜ w ≥ 0`. -/
theorem integrableOn_schlafliKernel {μ w : ℂ} (hμ : 0 < μ.re) (hw : 0 ≤ w.re) :
    IntegrableOn (schlafliKernel μ w) (Ioi 0) := by
  refine ((exp_neg_integrableOn_Ioi 0 hμ).const_mul (‖μ‖ + 1)).mono' ?_ ?_
  · exact (continuous_schlafliKernel μ w)
      |>.aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    exact norm_schlafliKernel_le hw (le_of_lt ht)

/-- Integration by parts in the radial Schläfli integral. -/
theorem intervalIntegral_schlafli_ibp (μ : ℂ) {w : ℂ} (hw : w ≠ 0) (R : ℝ) :
    ∫ t in (0:ℝ)..R, exp (-(w * Real.sinh t) - μ * t) =
      (1 - exp (-(w * Real.sinh R) - μ * R) / (Real.cosh R : ℂ) +
        ∫ t in (0:ℝ)..R, schlafliKernel μ w t) / w := by
  have hcE : Continuous fun t : ℝ => exp (-(w * Real.sinh t) - μ * t) := by fun_prop
  have hcK : Continuous (schlafliKernel μ w) := continuous_schlafliKernel μ w
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := R) (fun t _ => hasDerivAt_schlafli_ibp μ w t)
    (((hcE.const_mul (-w)).add hcK).intervalIntegrable _ _)
  rw [intervalIntegral.integral_add ((hcE.const_mul (-w)).intervalIntegrable _ _)
    (hcK.intervalIntegrable _ _), intervalIntegral.integral_const_mul] at hftc
  simp only [Real.sinh_zero, Real.cosh_zero, ofReal_zero, ofReal_one, mul_zero, neg_zero,
    sub_zero, exp_zero, div_one] at hftc
  field_simp
  linear_combination -hftc

/-- The radial Schläfli integral converges on the closed right half-plane minus the origin. -/
theorem tendsto_intervalIntegral_schlafliBoundary {μ w : ℂ} (hμ : 0 < μ.re) (hw : 0 ≤ w.re)
    (hw0 : w ≠ 0) :
    Tendsto (fun R : ℝ => ∫ t in (0:ℝ)..R, exp (-(w * Real.sinh t) - μ * t)) atTop
      (𝓝 (schlafliBoundary μ w)) := by
  simp_rw [intervalIntegral_schlafli_ibp μ hw0]
  rw [schlafliBoundary]
  refine Tendsto.div_const ?_ w
  have hK := intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_schlafliKernel hμ hw) tendsto_id
  have hP : Tendsto (fun R : ℝ => exp (-(w * Real.sinh R) - μ * R) / (Real.cosh R : ℂ)) atTop
      (𝓝 0) := by
    have hb : Tendsto (fun R : ℝ => Real.exp (-μ.re * R)) atTop (𝓝 0) := by
      have := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.2 hμ))
      simpa [Function.comp_def] using this
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop 0] with R hR
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos R)]
    rw [div_le_iff₀ (Real.cosh_pos R)]
    calc _ ≤ Real.exp (-μ.re * R) := norm_exp_schlafli_le_of_re_nonneg hw hR
      _ ≤ Real.exp (-μ.re * R) * Real.cosh R := le_mul_of_one_le_right (Real.exp_pos _).le
          (Real.one_le_cosh R)
  simpa using (tendsto_const_nhds.sub hP).add hK

/-- On the open right half-plane the boundary form agrees with the Lebesgue integral. -/
theorem integral_schlafli_eq_schlafliBoundary {μ w : ℂ} (hμ : 0 < μ.re) (hw : 0 < w.re) :
    ∫ t in Ioi (0:ℝ), exp (-(w * Real.sinh t) - μ * t) = schlafliBoundary μ w :=
  tendsto_nhds_unique (tendsto_intervalIntegral_schlafli μ hw)
    (tendsto_intervalIntegral_schlafliBoundary hμ hw.le (fun h => by simp [h] at hw))

/-- Continuity of the boundary form in `w` within the closed right half-plane. -/
theorem continuousWithinAt_schlafliBoundary_right {μ w : ℂ} (hμ : 0 < μ.re) (hw0 : w ≠ 0) :
    ContinuousWithinAt (fun v => schlafliBoundary μ v) {v | 0 ≤ v.re} w := by
  unfold schlafliBoundary
  refine ContinuousWithinAt.div (continuousWithinAt_const.add ?_) continuousWithinAt_id hw0
  refine continuousWithinAt_of_dominated (bound := fun t => (‖μ‖ + 1) * Real.exp (-μ.re * t))
    (Eventually.of_forall fun v => (continuous_schlafliKernel μ v).aestronglyMeasurable) ?_
    ((exp_neg_integrableOn_Ioi 0 hμ).const_mul (‖μ‖ + 1)) ?_
  · filter_upwards [self_mem_nhdsWithin] with v hv
    exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht =>
      norm_schlafliKernel_le hv (le_of_lt ht))
  · exact Eventually.of_forall fun t => (by unfold schlafliKernel; fun_prop :
      Continuous fun v => schlafliKernel μ v t).continuousWithinAt

/-- Continuity of the boundary form in the order. -/
theorem continuousAt_schlafliBoundary_order {μ w : ℂ} (hμ : 0 < μ.re) (hw : 0 ≤ w.re) :
    ContinuousAt (fun ν => schlafliBoundary ν w) μ := by
  unfold schlafliBoundary
  refine ContinuousAt.div_const (continuousAt_const.add ?_) w
  have hU : {ν : ℂ | μ.re / 2 < ν.re ∧ ‖ν‖ < ‖μ‖ + 1} ∈ 𝓝 μ := by
    refine IsOpen.mem_nhds ?_ ⟨by linarith, by linarith⟩
    exact (isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)
  refine continuousAt_of_dominated (bound := fun t => (‖μ‖ + 1 + 1) * Real.exp (-(μ.re / 2) * t))
    (Eventually.of_forall fun ν => (continuous_schlafliKernel ν w).aestronglyMeasurable) ?_
    ((exp_neg_integrableOn_Ioi 0 (by linarith)).const_mul (‖μ‖ + 1 + 1)) ?_
  · filter_upwards [hU] with ν hν
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    refine (norm_schlafliKernel_le hw (le_of_lt ht)).trans ?_
    have ht0 : (0:ℝ) ≤ t := le_of_lt ht
    gcongr
    all_goals linarith [hν.1, hν.2]
  · exact Eventually.of_forall fun t => (by unfold schlafliKernel; fun_prop :
      Continuous fun ν => schlafliKernel ν w t).continuousAt

end DLMF.Bessel
