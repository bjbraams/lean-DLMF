/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.CoalescingSaddles.DifferentialEquations.Cuspoid

/-!
# Differential identities for the hyperbolic umbilic

Moment integrals, parameter derivatives and polynomial-weight estimates for the hyperbolic
umbilic.

Source references and common attribution are retained in
`DLMF.CoalescingSaddles.DifferentialEquations`.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set Filter Function

open scoped Real Topology

namespace DLMF.CoalescingSaddles

/-! ### Helpers: the hyperbolic umbilic integrand

On the product of the cubic V-contours, `s = σ d(σ)`, `t = τ d(τ)`, the cubic part of
`Φ^{(H)}` has imaginary part `|σ|³ + |τ|³`, so all moments `∫∫ s^a t^b exp(iΦ^{(H)})` converge
absolutely, uniformly for bounded parameters. -/

/-- An elementary cubic absorption bound: `(C/2 + 1/2) a² + C a ≤ a³ + c³ + c` with `c = (3C +
1)/2`, for `a, C ≥ 0`. -/
theorem s36b_cubic_le {a C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) :
    (C / 2 + 1 / 2) * a ^ 2 + C * a ≤ a ^ 3 + ((3 * C + 1) / 2) ^ 3 + (3 * C + 1) / 2 := by
  set B := (3 * C + 1) / 2 with hB
  have hB0 : 0 ≤ B := by positivity
  have h1 : C * a ≤ C + C * a ^ 2 := by nlinarith [sq_nonneg (a - 1 / 2)]
  have h2 : B * a ^ 2 ≤ a ^ 3 + B ^ 3 := by
    rcases le_total B a with h | h
    · nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg a), pow_nonneg hB0 3]
    · have h3 : a ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ ha h 2
      nlinarith [mul_le_mul_of_nonneg_left h3 hB0, pow_nonneg ha 3]
  nlinarith

/-- Lower bound for `Im Φ^{(H)}` on the product of V-contours: `|σ|³ + |τ|³ - |z||σ||τ| - |y||τ| -
|x||σ|`. -/
lemma s36b_im_hyperbolic_ge (σ τ x y z : ℝ) :
    |σ| ^ 3 + |τ| ^ 3 - |z| * |σ| * |τ| - |y| * |τ| - |x| * |σ| ≤
      (hyperbolicUmbilicPotential (cuspoidContour 1 σ) (cuspoidContour 1 τ) x y z).im := by
  have hs : cuspoidContour 1 σ ^ 3 = I * ((|σ| ^ 3 : ℝ) : ℂ) := cuspoidContour_pow 1 σ
  have ht : cuspoidContour 1 τ ^ 3 = I * ((|τ| ^ 3 : ℝ) : ℂ) := cuspoidContour_pow 1 τ
  unfold hyperbolicUmbilicPotential
  rw [hs, ht]
  simp only [add_im, I_mul_im, ofReal_re]
  have e1 := abs_im_le_norm ((z : ℂ) * cuspoidContour 1 σ * cuspoidContour 1 τ)
  have e2 := abs_im_le_norm ((y : ℂ) * cuspoidContour 1 τ)
  have e3 := abs_im_le_norm ((x : ℂ) * cuspoidContour 1 σ)
  simp only [norm_mul, norm_real, Real.norm_eq_abs, norm_cuspoidContour] at e1 e2 e3
  linarith [neg_abs_le ((z : ℂ) * cuspoidContour 1 σ * cuspoidContour 1 τ).im,
    neg_abs_le ((y : ℂ) * cuspoidContour 1 τ).im, neg_abs_le ((x : ℂ) * cuspoidContour 1 σ).im]

/-- Gaussian bound for the hyperbolic umbilic moment integrands, uniform for
`|x|, |y|, |z| ≤ C`. -/
lemma s36b_norm_hyperbolic_integrand_le (σ τ x y z : ℝ) (a b : ℕ) {C : ℝ} (hC0 : 0 ≤ C)
    (hx : |x| ≤ C) (hy : |y| ≤ C) (hz : |z| ≤ C) :
    ‖cuspoidContourDir 1 σ * cuspoidContourDir 1 τ *
        (cuspoidContour 1 σ ^ a * cuspoidContour 1 τ ^ b) *
        exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 σ) (cuspoidContour 1 τ) x y z)‖ ≤
      Real.exp (2 * (((3 * C + 1) / 2) ^ 3 + (3 * C + 1) / 2)) *
        ((|σ| ^ a * Real.exp (-(1 / 2) * σ ^ 2)) * (|τ| ^ b * Real.exp (-(1 / 2) * τ ^ 2))) := by
  set B := (3 * C + 1) / 2 with hB
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_cuspoidContourDir,
    norm_cuspoidContourDir, norm_cuspoidContour, norm_cuspoidContour, norm_exp]
  have hre : (I * hyperbolicUmbilicPotential (cuspoidContour 1 σ) (cuspoidContour 1 τ)
      x y z).re = -(hyperbolicUmbilicPotential (cuspoidContour 1 σ) (cuspoidContour 1 τ)
      x y z).im := by simp [mul_re]
  rw [hre]
  have him := s36b_im_hyperbolic_ge σ τ x y z
  have hσ := s36b_cubic_le (abs_nonneg σ) hC0
  have hτ := s36b_cubic_le (abs_nonneg τ) hC0
  rw [← hB] at hσ hτ
  have hst : 2 * (|σ| * |τ|) ≤ |σ| ^ 2 + |τ| ^ 2 := by nlinarith [sq_nonneg (|σ| - |τ|)]
  have h1 : |z| * |σ| * |τ| ≤ C * (|σ| ^ 2 + |τ| ^ 2) / 2 := by
    have := mul_le_mul_of_nonneg_right hz (mul_nonneg (abs_nonneg σ) (abs_nonneg τ))
    nlinarith
  have h2 : |y| * |τ| ≤ C * |τ| := mul_le_mul_of_nonneg_right hy (abs_nonneg τ)
  have h3 : |x| * |σ| ≤ C * |σ| := mul_le_mul_of_nonneg_right hx (abs_nonneg σ)
  have hσ2 : |σ| ^ 2 = σ ^ 2 := sq_abs σ
  have hτ2 : |τ| ^ 2 = τ ^ 2 := sq_abs τ
  have key : -(hyperbolicUmbilicPotential (cuspoidContour 1 σ) (cuspoidContour 1 τ) x y z).im ≤
      2 * (B ^ 3 + B) + (-(1 / 2) * σ ^ 2 + -(1 / 2) * τ ^ 2) := by
    rw [← hσ2, ← hτ2]; linarith
  have hexp := Real.exp_le_exp.mpr key
  rw [Real.exp_add, Real.exp_add] at hexp
  have hp : 0 ≤ |σ| ^ a * |τ| ^ b := by positivity
  calc 1 * 1 * (|σ| ^ a * |τ| ^ b) *
        Real.exp (-(hyperbolicUmbilicPotential (cuspoidContour 1 σ) (cuspoidContour 1 τ)
          x y z).im)
      ≤ |σ| ^ a * |τ| ^ b * (Real.exp (2 * (B ^ 3 + B)) *
          (Real.exp (-(1 / 2) * σ ^ 2) * Real.exp (-(1 / 2) * τ ^ 2))) := by
        rw [one_mul, one_mul]; exact mul_le_mul_of_nonneg_left hexp hp
    _ = _ := by ring

/-- The weight `d(σ) d(τ) t(σ)^a t(τ)^b` of the hyperbolic umbilic moments is measurable. -/
lemma s36b_measurable_hyperbolic_weight (a b : ℕ) :
    Measurable fun p : ℝ × ℝ => cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
      (cuspoidContour 1 p.1 ^ a * cuspoidContour 1 p.2 ^ b) :=
  (((measurable_cuspoidContourDir 1).comp measurable_fst).mul
    ((measurable_cuspoidContourDir 1).comp measurable_snd)).mul
    ((((measurable_cuspoidContour 1).comp measurable_fst).pow_const a).mul
      (((measurable_cuspoidContour 1).comp measurable_snd).pow_const b))

/-- The hyperbolic umbilic phase on the product of V-contours is measurable. -/
lemma s36b_measurable_hyperbolic_phase (x y z : ℝ) :
    Measurable fun p : ℝ × ℝ =>
      hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2) x y z := by
  have hc1 : Measurable fun p : ℝ × ℝ => cuspoidContour 1 p.1 :=
    (measurable_cuspoidContour 1).comp measurable_fst
  have hc2 : Measurable fun p : ℝ × ℝ => cuspoidContour 1 p.2 :=
    (measurable_cuspoidContour 1).comp measurable_snd
  unfold hyperbolicUmbilicPotential
  fun_prop

/-- The hyperbolic umbilic moment integrand is measurable. -/
lemma s36b_measurable_hyperbolic_integrand (x y z : ℝ) (a b : ℕ) :
    Measurable fun p : ℝ × ℝ => cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
      (cuspoidContour 1 p.1 ^ a * cuspoidContour 1 p.2 ^ b) *
      exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2) x y z) :=
  (s36b_measurable_hyperbolic_weight a b).mul
    (measurable_exp.comp ((s36b_measurable_hyperbolic_phase x y z).const_mul I))

/-- `|p₁|^a e^{-p₁²/2} |p₂|^b e^{-p₂²/2}` is integrable on `ℝ²`. -/
theorem s36b_integrable_gauss_prod (a b : ℕ) :
    Integrable fun p : ℝ × ℝ => (|p.1| ^ a * Real.exp (-(1 / 2) * p.1 ^ 2)) *
      (|p.2| ^ b * Real.exp (-(1 / 2) * p.2 ^ 2)) :=
  (s36b_integrable_pow_mul_gauss a).mul_prod (s36b_integrable_pow_mul_gauss b)

/-- The hyperbolic umbilic moment integrand is integrable on `ℝ²`. -/
lemma s36b_integrable_hyperbolic_integrand (x y z : ℝ) (a b : ℕ) :
    Integrable fun p : ℝ × ℝ => cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
      (cuspoidContour 1 p.1 ^ a * cuspoidContour 1 p.2 ^ b) *
      exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2) x y z) :=
  Integrable.mono' ((s36b_integrable_gauss_prod a b).const_mul _)
    (s36b_measurable_hyperbolic_integrand x y z a b).aestronglyMeasurable
    (ae_of_all _ fun p => s36b_norm_hyperbolic_integrand_le p.1 p.2 x y z a b
      (C := |x| + |y| + |z|) (by positivity)
      (by linarith [abs_nonneg y, abs_nonneg z]) (by linarith [abs_nonneg x, abs_nonneg z])
      (by linarith [abs_nonneg x, abs_nonneg y]))

/-- `Ψ^{(H)}` is the moment of order `(0, 0)`. -/
theorem hyperbolicUmbilicIntegral_eq_moment (x y z : ℝ) :
    hyperbolicUmbilicIntegral x y z = hyperbolicUmbilicMoment x y z 0 0 := by
  simp [hyperbolicUmbilicIntegral, hyperbolicUmbilicMoment]

/-- Differentiation under the integral sign in a parameter entering the phase linearly. -/
lemma s36b_hasDerivAt_param_integral {W A B : ℝ × ℝ → ℂ} {bound : ℝ × ℝ → ℝ} (w₀ : ℝ)
    (hW : Measurable W) (hA : Measurable A) (hB : Measurable B)
    (hint : Integrable fun p => W p * exp (I * (A p + (w₀ : ℂ) * B p)))
    (hbound : Integrable bound)
    (hle : ∀ p, ∀ w ∈ Metric.ball w₀ 1,
      ‖W p * (I * B p) * exp (I * (A p + (w : ℂ) * B p))‖ ≤ bound p) :
    HasDerivAt (fun w : ℝ => ∫ p, W p * exp (I * (A p + (w : ℂ) * B p)))
      (∫ p, W p * (I * B p) * exp (I * (A p + (w₀ : ℂ) * B p))) w₀ := by
  have hE : ∀ w : ℝ, Measurable fun p => exp (I * (A p + (w : ℂ) * B p)) := fun w =>
    measurable_exp.comp (measurable_const.mul (hA.add (measurable_const.mul hB)))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds w₀ one_pos)
    (Eventually.of_forall fun w => (hW.mul (hE w)).aestronglyMeasurable) hint
    ((hW.mul (measurable_const.mul hB)).mul (hE w₀)).aestronglyMeasurable
    (ae_of_all _ fun p w hw => hle p w hw) hbound (ae_of_all _ fun p w _ => ?_)).2
  have h1 : HasDerivAt (fun w : ℝ => I * (A p + (w : ℂ) * B p)) (I * B p) w := by
    simpa using ((((hasDerivAt_id w).ofReal_comp).mul_const (B p)).const_add (A p)).const_mul I
  convert h1.cexp.const_mul (W p) using 1
  ring

/-- `Φ^{(H)}` is affine in `x` with coefficient `s`. -/
lemma s36b_hyperbolic_potential_x (s t : ℂ) (x y z : ℝ) :
    hyperbolicUmbilicPotential s t x y z = hyperbolicUmbilicPotential s t 0 y z + (x : ℂ) * s := by
  unfold hyperbolicUmbilicPotential; push_cast; ring

/-- `Φ^{(H)}` is affine in `y` with coefficient `t`. -/
lemma s36b_hyperbolic_potential_y (s t : ℂ) (x y z : ℝ) :
    hyperbolicUmbilicPotential s t x y z = hyperbolicUmbilicPotential s t x 0 z + (y : ℂ) * t := by
  unfold hyperbolicUmbilicPotential; push_cast; ring

/-- `Φ^{(H)}` is affine in `z` with coefficient `st`. -/
lemma s36b_hyperbolic_potential_z (s t : ℂ) (x y z : ℝ) :
    hyperbolicUmbilicPotential s t x y z =
      hyperbolicUmbilicPotential s t x y 0 + (z : ℂ) * (s * t) := by
  unfold hyperbolicUmbilicPotential; push_cast; ring

/-- `∂/∂x ∫∫ s^a t^b e^{iΦ^{(H)}} = i ∫∫ s^{a+1} t^b e^{iΦ^{(H)}}`. -/
theorem hasDerivAt_hyperbolicUmbilicMoment_x (x y z : ℝ) (a b : ℕ) :
    HasDerivAt (fun w => hyperbolicUmbilicMoment w y z a b)
      (I * hyperbolicUmbilicMoment x y z (a + 1) b) x := by
  set C := |x| + 1 + |y| + |z|
  have hfun : (fun w => hyperbolicUmbilicMoment w y z a b) = fun w : ℝ => ∫ p : ℝ × ℝ,
      (cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
        (cuspoidContour 1 p.1 ^ a * cuspoidContour 1 p.2 ^ b)) *
      exp (I * (hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2) 0 y z +
        (w : ℂ) * cuspoidContour 1 p.1)) := by
    funext w; unfold hyperbolicUmbilicMoment
    simp_rw [← s36b_hyperbolic_potential_x]
  have hval : I * hyperbolicUmbilicMoment x y z (a + 1) b = ∫ p : ℝ × ℝ,
      (cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
        (cuspoidContour 1 p.1 ^ a * cuspoidContour 1 p.2 ^ b)) * (I * cuspoidContour 1 p.1) *
      exp (I * (hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2) 0 y z +
        (x : ℂ) * cuspoidContour 1 p.1)) := by
    unfold hyperbolicUmbilicMoment
    rw [← integral_const_mul]
    congr 1; funext p
    rw [← s36b_hyperbolic_potential_x, pow_succ]; ring
  rw [hfun, hval]
  refine s36b_hasDerivAt_param_integral x (s36b_measurable_hyperbolic_weight a b)
    (s36b_measurable_hyperbolic_phase 0 y z) ((measurable_cuspoidContour 1).comp measurable_fst)
    ?_ ((s36b_integrable_gauss_prod (a + 1) b).const_mul
      (Real.exp (2 * (((3 * C + 1) / 2) ^ 3 + (3 * C + 1) / 2)))) fun p w hw => ?_
  · simp_rw [← s36b_hyperbolic_potential_x]
    exact s36b_integrable_hyperbolic_integrand x y z a b
  · rw [← s36b_hyperbolic_potential_x]
    have hw' : |w| ≤ C := by
      have := abs_sub_abs_le_abs_sub w x
      have := (Metric.mem_ball.mp hw); rw [Real.dist_eq] at this
      linarith [abs_nonneg y, abs_nonneg z]
    have h := s36b_norm_hyperbolic_integrand_le p.1 p.2 w y z (a + 1) b (C := C) (by positivity)
      hw' (by linarith [abs_nonneg x, abs_nonneg z]) (by linarith [abs_nonneg x, abs_nonneg y])
    calc _ = ‖cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
          (cuspoidContour 1 p.1 ^ (a + 1) * cuspoidContour 1 p.2 ^ b) *
          exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2)
            w y z)‖ := by
          rw [show cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
              (cuspoidContour 1 p.1 ^ a * cuspoidContour 1 p.2 ^ b) * (I * cuspoidContour 1 p.1) *
              exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2)
                w y z) = I * (cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
              (cuspoidContour 1 p.1 ^ (a + 1) * cuspoidContour 1 p.2 ^ b) *
              exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2)
                w y z)) by rw [pow_succ]; ring, norm_mul, norm_I, one_mul]
      _ ≤ _ := h

/-- `∂/∂y ∫∫ s^a t^b e^{iΦ^{(H)}} = i ∫∫ s^a t^{b+1} e^{iΦ^{(H)}}`. -/
theorem hasDerivAt_hyperbolicUmbilicMoment_y (x y z : ℝ) (a b : ℕ) :
    HasDerivAt (fun w => hyperbolicUmbilicMoment x w z a b)
      (I * hyperbolicUmbilicMoment x y z a (b + 1)) y := by
  set C := |x| + |y| + 1 + |z|
  have hfun : (fun w => hyperbolicUmbilicMoment x w z a b) = fun w : ℝ => ∫ p : ℝ × ℝ,
      (cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
        (cuspoidContour 1 p.1 ^ a * cuspoidContour 1 p.2 ^ b)) *
      exp (I * (hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2) x 0 z +
        (w : ℂ) * cuspoidContour 1 p.2)) := by
    funext w; unfold hyperbolicUmbilicMoment
    simp_rw [← s36b_hyperbolic_potential_y]
  have hval : I * hyperbolicUmbilicMoment x y z a (b + 1) = ∫ p : ℝ × ℝ,
      (cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
        (cuspoidContour 1 p.1 ^ a * cuspoidContour 1 p.2 ^ b)) * (I * cuspoidContour 1 p.2) *
      exp (I * (hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2) x 0 z +
        (y : ℂ) * cuspoidContour 1 p.2)) := by
    unfold hyperbolicUmbilicMoment
    rw [← integral_const_mul]
    congr 1; funext p
    rw [← s36b_hyperbolic_potential_y, pow_succ]; ring
  rw [hfun, hval]
  refine s36b_hasDerivAt_param_integral y (s36b_measurable_hyperbolic_weight a b)
    (s36b_measurable_hyperbolic_phase x 0 z) ((measurable_cuspoidContour 1).comp measurable_snd)
    ?_ ((s36b_integrable_gauss_prod a (b + 1)).const_mul
      (Real.exp (2 * (((3 * C + 1) / 2) ^ 3 + (3 * C + 1) / 2)))) fun p w hw => ?_
  · simp_rw [← s36b_hyperbolic_potential_y]
    exact s36b_integrable_hyperbolic_integrand x y z a b
  · rw [← s36b_hyperbolic_potential_y]
    have hw' : |w| ≤ C := by
      have := abs_sub_abs_le_abs_sub w y
      have := (Metric.mem_ball.mp hw); rw [Real.dist_eq] at this
      linarith [abs_nonneg x, abs_nonneg z]
    have h := s36b_norm_hyperbolic_integrand_le p.1 p.2 x w z a (b + 1) (C := C) (by positivity)
      (by linarith [abs_nonneg y, abs_nonneg z]) hw' (by linarith [abs_nonneg x, abs_nonneg y])
    calc _ = ‖cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
          (cuspoidContour 1 p.1 ^ a * cuspoidContour 1 p.2 ^ (b + 1)) *
          exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2)
            x w z)‖ := by
          rw [show cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
              (cuspoidContour 1 p.1 ^ a * cuspoidContour 1 p.2 ^ b) * (I * cuspoidContour 1 p.2) *
              exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2)
                x w z) = I * (cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
              (cuspoidContour 1 p.1 ^ a * cuspoidContour 1 p.2 ^ (b + 1)) *
              exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2)
                x w z)) by rw [pow_succ]; ring, norm_mul, norm_I, one_mul]
      _ ≤ _ := h

/-- `∂/∂z ∫∫ s^a t^b e^{iΦ^{(H)}} = i ∫∫ s^{a+1} t^{b+1} e^{iΦ^{(H)}}`. -/
theorem hasDerivAt_hyperbolicUmbilicMoment_z (x y z : ℝ) (a b : ℕ) :
    HasDerivAt (fun w => hyperbolicUmbilicMoment x y w a b)
      (I * hyperbolicUmbilicMoment x y z (a + 1) (b + 1)) z := by
  set C := |x| + |y| + |z| + 1
  have hfun : (fun w => hyperbolicUmbilicMoment x y w a b) = fun w : ℝ => ∫ p : ℝ × ℝ,
      (cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
        (cuspoidContour 1 p.1 ^ a * cuspoidContour 1 p.2 ^ b)) *
      exp (I * (hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2) x y 0 +
        (w : ℂ) * (cuspoidContour 1 p.1 * cuspoidContour 1 p.2))) := by
    funext w; unfold hyperbolicUmbilicMoment
    simp_rw [← s36b_hyperbolic_potential_z]
  have hval : I * hyperbolicUmbilicMoment x y z (a + 1) (b + 1) = ∫ p : ℝ × ℝ,
      (cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
        (cuspoidContour 1 p.1 ^ a * cuspoidContour 1 p.2 ^ b)) *
        (I * (cuspoidContour 1 p.1 * cuspoidContour 1 p.2)) *
      exp (I * (hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2) x y 0 +
        (z : ℂ) * (cuspoidContour 1 p.1 * cuspoidContour 1 p.2))) := by
    unfold hyperbolicUmbilicMoment
    rw [← integral_const_mul]
    congr 1; funext p
    rw [← s36b_hyperbolic_potential_z, pow_succ, pow_succ]; ring
  rw [hfun, hval]
  refine s36b_hasDerivAt_param_integral z (s36b_measurable_hyperbolic_weight a b)
    (s36b_measurable_hyperbolic_phase x y 0)
    (((measurable_cuspoidContour 1).comp measurable_fst).mul
      ((measurable_cuspoidContour 1).comp measurable_snd))
    ?_ ((s36b_integrable_gauss_prod (a + 1) (b + 1)).const_mul
      (Real.exp (2 * (((3 * C + 1) / 2) ^ 3 + (3 * C + 1) / 2)))) fun p w hw => ?_
  · simp_rw [← s36b_hyperbolic_potential_z]
    exact s36b_integrable_hyperbolic_integrand x y z a b
  · rw [← s36b_hyperbolic_potential_z]
    have hw' : |w| ≤ C := by
      have := abs_sub_abs_le_abs_sub w z
      have := (Metric.mem_ball.mp hw); rw [Real.dist_eq] at this
      linarith [abs_nonneg x, abs_nonneg y]
    have h := s36b_norm_hyperbolic_integrand_le p.1 p.2 x y w (a + 1) (b + 1) (C := C)
      (by positivity) (by linarith [abs_nonneg y, abs_nonneg z])
      (by linarith [abs_nonneg x, abs_nonneg z]) hw'
    calc _ = ‖cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
          (cuspoidContour 1 p.1 ^ (a + 1) * cuspoidContour 1 p.2 ^ (b + 1)) *
          exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2)
            x y w)‖ := by
          rw [show cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
              (cuspoidContour 1 p.1 ^ a * cuspoidContour 1 p.2 ^ b) *
              (I * (cuspoidContour 1 p.1 * cuspoidContour 1 p.2)) *
              exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2)
                x y w) = I * (cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
              (cuspoidContour 1 p.1 ^ (a + 1) * cuspoidContour 1 p.2 ^ (b + 1)) *
              exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2)
                x y w)) by rw [pow_succ, pow_succ]; ring, norm_mul, norm_I, one_mul]
      _ ≤ _ := h

/-- Integrability in `σ` of the hyperbolic umbilic moment integrand for fixed `τ`. -/
lemma s36b_integrable_hyperbolic_s (x y z τ : ℝ) (a : ℕ) :
    Integrable fun σ : ℝ => cuspoidContourDir 1 σ * cuspoidContour 1 σ ^ a *
      exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 σ) (cuspoidContour 1 τ) x y z) := by
  set C := |x| + |y| + |z|
  have hm : Measurable fun σ : ℝ =>
      hyperbolicUmbilicPotential (cuspoidContour 1 σ) (cuspoidContour 1 τ) x y z := by
    have hc : Measurable (cuspoidContour 1) := measurable_cuspoidContour 1
    unfold hyperbolicUmbilicPotential
    fun_prop
  refine Integrable.mono' (((s36b_integrable_pow_mul_gauss a).mul_const
      (|τ| ^ 0 * Real.exp (-(1 / 2) * τ ^ 2))).const_mul
      (Real.exp (2 * (((3 * C + 1) / 2) ^ 3 + (3 * C + 1) / 2))))
    ((((measurable_cuspoidContourDir 1).mul ((measurable_cuspoidContour 1).pow_const a)).mul
      (measurable_exp.comp (hm.const_mul I))).aestronglyMeasurable)
    (ae_of_all _ fun σ => ?_)
  have h := s36b_norm_hyperbolic_integrand_le σ τ x y z a 0 (C := C) (by positivity)
    (by linarith [abs_nonneg y, abs_nonneg z]) (by linarith [abs_nonneg x, abs_nonneg z])
    (by linarith [abs_nonneg x, abs_nonneg y])
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_cuspoidContourDir, norm_cuspoidContourDir]
    at h
  rw [norm_mul, norm_mul, norm_cuspoidContourDir]
  simp only [pow_zero, norm_one, mul_one, one_mul] at h ⊢
  linarith

/-- Integrability in `τ` of the hyperbolic umbilic moment integrand for fixed `σ`. -/
lemma s36b_integrable_hyperbolic_t (x y z σ : ℝ) (b : ℕ) :
    Integrable fun τ : ℝ => cuspoidContourDir 1 τ * cuspoidContour 1 τ ^ b *
      exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 σ) (cuspoidContour 1 τ) x y z) := by
  set C := |x| + |y| + |z|
  have hm : Measurable fun τ : ℝ =>
      hyperbolicUmbilicPotential (cuspoidContour 1 σ) (cuspoidContour 1 τ) x y z := by
    have hc : Measurable (cuspoidContour 1) := measurable_cuspoidContour 1
    unfold hyperbolicUmbilicPotential
    fun_prop
  refine Integrable.mono' (((s36b_integrable_pow_mul_gauss b).const_mul
      (|σ| ^ 0 * Real.exp (-(1 / 2) * σ ^ 2))).const_mul
      (Real.exp (2 * (((3 * C + 1) / 2) ^ 3 + (3 * C + 1) / 2))))
    ((((measurable_cuspoidContourDir 1).mul ((measurable_cuspoidContour 1).pow_const b)).mul
      (measurable_exp.comp (hm.const_mul I))).aestronglyMeasurable)
    (ae_of_all _ fun τ => ?_)
  have h := s36b_norm_hyperbolic_integrand_le σ τ x y z 0 b (C := C) (by positivity)
    (by linarith [abs_nonneg y, abs_nonneg z]) (by linarith [abs_nonneg x, abs_nonneg z])
    (by linarith [abs_nonneg x, abs_nonneg y])
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_cuspoidContourDir, norm_cuspoidContourDir]
    at h
  rw [norm_mul, norm_mul, norm_cuspoidContourDir]
  simp only [pow_zero, norm_one, mul_one, one_mul] at h ⊢
  linarith

/-- `‖exp(iΦ^{(H)})‖ ≤ A e^{-σ²/2} e^{-τ²/2}` on the contour. -/
lemma s36b_norm_hyperbolic_exp_le (x y z σ τ : ℝ) :
    ‖exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 σ) (cuspoidContour 1 τ) x y z)‖ ≤
      Real.exp (2 * (((3 * (|x| + |y| + |z|) + 1) / 2) ^ 3 + (3 * (|x| + |y| + |z|) + 1) / 2)) *
        (Real.exp (-(1 / 2) * σ ^ 2) * Real.exp (-(1 / 2) * τ ^ 2)) := by
  have h := s36b_norm_hyperbolic_integrand_le σ τ x y z 0 0 (C := |x| + |y| + |z|)
    (by positivity) (by linarith [abs_nonneg y, abs_nonneg z])
    (by linarith [abs_nonneg x, abs_nonneg z]) (by linarith [abs_nonneg x, abs_nonneg y])
  rw [norm_mul, norm_mul, norm_mul, norm_cuspoidContourDir, norm_cuspoidContourDir] at h
  simpa using h

/-- Integration by parts in `s`: `∫ (3s² + zt + x) e^{iΦ^{(H)}} ds = 0` for fixed `t = t(τ)`. -/
lemma s36b_hyperbolic_ibp_s (x y z τ : ℝ) :
    ∫ σ : ℝ, cuspoidContourDir 1 σ *
      (3 * cuspoidContour 1 σ ^ 2 + (z : ℂ) * cuspoidContour 1 τ + x) *
      exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 σ) (cuspoidContour 1 τ) x y z) =
      0 := by
  set t := cuspoidContour 1 τ with ht
  have hP : ∀ u, HasDerivAt (fun u => hyperbolicUmbilicPotential u t x y z)
      (3 * u ^ 2 + (z : ℂ) * t + x) u := by
    intro u
    unfold hyperbolicUmbilicPotential
    have := ((((((hasDerivAt_pow 3 u).add_const (t ^ 3)).add
      (((hasDerivAt_id u).const_mul (z : ℂ)).mul_const t)).add_const ((y : ℂ) * t)).add
        ((hasDerivAt_id u).const_mul (x : ℂ))))
    convert this using 1
    · funext v; simp
    · simp
  have hlim : ∀ {l : Filter ℝ}, Tendsto (fun r : ℝ => -(1 / 2) * r ^ 2) l atBot →
      Tendsto (fun σ : ℝ => exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 σ) t x y z))
        l (𝓝 0) := by
    intro l hl
    refine squeeze_zero_norm (fun σ => s36b_norm_hyperbolic_exp_le x y z σ τ) ?_
    have := ((Real.tendsto_exp_atBot.comp hl).mul_const (Real.exp (-(1 / 2) * τ ^ 2))).const_mul
      (Real.exp (2 * (((3 * (|x| + |y| + |z|) + 1) / 2) ^ 3 + (3 * (|x| + |y| + |z|) + 1) / 2)))
    simpa using this
  refine s36b_contour_ibp 1 (P := fun u => hyperbolicUmbilicPotential u t x y z) hP ?_
    (hlim s36b_tendsto_neg_half_sq_atTop) (hlim s36b_tendsto_neg_half_sq_atBot)
  refine (((s36b_integrable_hyperbolic_s x y z τ 2).const_mul 3).add
    ((s36b_integrable_hyperbolic_s x y z τ 0).const_mul ((z : ℂ) * t + x))).congr
    (ae_of_all _ fun σ => ?_)
  simp only [← ht, Pi.add_apply, pow_zero, mul_one]
  ring

/-- Integration by parts in `t`: `∫ (3t² + zs + y) e^{iΦ^{(H)}} dt = 0` for fixed `s = s(σ)`. -/
lemma s36b_hyperbolic_ibp_t (x y z σ : ℝ) :
    ∫ τ : ℝ, cuspoidContourDir 1 τ *
      (3 * cuspoidContour 1 τ ^ 2 + (z : ℂ) * cuspoidContour 1 σ + y) *
      exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 σ) (cuspoidContour 1 τ) x y z) =
      0 := by
  set s := cuspoidContour 1 σ with hs
  have hP : ∀ u, HasDerivAt (fun u => hyperbolicUmbilicPotential s u x y z)
      (3 * u ^ 2 + (z : ℂ) * s + y) u := by
    intro u
    unfold hyperbolicUmbilicPotential
    have := (((((hasDerivAt_pow 3 u).const_add (s ^ 3)).add
      ((hasDerivAt_id u).const_mul ((z : ℂ) * s))).add
        ((hasDerivAt_id u).const_mul (y : ℂ))).add_const ((x : ℂ) * s))
    convert this using 1
    · funext v; simp
    · simp
  have hlim : ∀ {l : Filter ℝ}, Tendsto (fun r : ℝ => -(1 / 2) * r ^ 2) l atBot →
      Tendsto (fun τ : ℝ => exp (I * hyperbolicUmbilicPotential s (cuspoidContour 1 τ) x y z))
        l (𝓝 0) := by
    intro l hl
    refine squeeze_zero_norm (fun τ => s36b_norm_hyperbolic_exp_le x y z σ τ) ?_
    have := ((Real.tendsto_exp_atBot.comp hl).const_mul (Real.exp (-(1 / 2) * σ ^ 2))).const_mul
      (Real.exp (2 * (((3 * (|x| + |y| + |z|) + 1) / 2) ^ 3 + (3 * (|x| + |y| + |z|) + 1) / 2)))
    simpa using this
  refine s36b_contour_ibp 1 (P := fun u => hyperbolicUmbilicPotential s u x y z) hP ?_
    (hlim s36b_tendsto_neg_half_sq_atTop) (hlim s36b_tendsto_neg_half_sq_atBot)
  refine (((s36b_integrable_hyperbolic_t x y z σ 2).const_mul 3).add
    ((s36b_integrable_hyperbolic_t x y z σ 0).const_mul ((z : ℂ) * s + y))).congr
    (ae_of_all _ fun τ => ?_)
  simp only [← hs, Pi.add_apply, pow_zero, mul_one]
  ring

/-- The moment relation behind 36.10.15: `3M_{2,0} + zM_{0,1} + xM_{0,0} = 0`. -/
lemma s36b_hyperbolic_moment_rel_s (x y z : ℝ) :
    3 * hyperbolicUmbilicMoment x y z 2 0 + (z : ℂ) * hyperbolicUmbilicMoment x y z 0 1 +
      (x : ℂ) * hyperbolicUmbilicMoment x y z 0 0 = 0 := by
  have h1 := s36b_integrable_hyperbolic_integrand x y z 2 0
  have h2 := s36b_integrable_hyperbolic_integrand x y z 0 1
  have h3 := s36b_integrable_hyperbolic_integrand x y z 0 0
  have hsum : 3 * hyperbolicUmbilicMoment x y z 2 0 +
      (z : ℂ) * hyperbolicUmbilicMoment x y z 0 1 +
      (x : ℂ) * hyperbolicUmbilicMoment x y z 0 0 = ∫ p : ℝ × ℝ,
        (3 * (cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
          (cuspoidContour 1 p.1 ^ 2 * cuspoidContour 1 p.2 ^ 0) *
          exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2)
            x y z)) +
        (z : ℂ) * (cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
          (cuspoidContour 1 p.1 ^ 0 * cuspoidContour 1 p.2 ^ 1) *
          exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2)
            x y z))) +
        (x : ℂ) * (cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
          (cuspoidContour 1 p.1 ^ 0 * cuspoidContour 1 p.2 ^ 0) *
          exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2)
            x y z)) := by
    unfold hyperbolicUmbilicMoment
    rw [integral_add _ (h3.const_mul _), integral_add (h1.const_mul _) (h2.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul]
    exact (h1.const_mul _).add (h2.const_mul _)
  have hF := ((h1.const_mul (3 : ℂ)).add (h2.const_mul (z : ℂ))).add (h3.const_mul (x : ℂ))
  rw [hsum]
  rw [Measure.volume_eq_prod] at hF ⊢
  rw [integral_prod_symm]
  swap
  · exact hF
  refine integral_eq_zero_of_ae (ae_of_all _ fun τ => ?_)
  simp only [Pi.zero_apply]
  rw [← mul_zero (cuspoidContourDir 1 τ), ← s36b_hyperbolic_ibp_s x y z τ, ← integral_const_mul]
  congr 1; funext σ
  ring

/-- The moment relation behind 36.10.16: `3M_{0,2} + zM_{1,0} + yM_{0,0} = 0`. -/
lemma s36b_hyperbolic_moment_rel_t (x y z : ℝ) :
    3 * hyperbolicUmbilicMoment x y z 0 2 + (z : ℂ) * hyperbolicUmbilicMoment x y z 1 0 +
      (y : ℂ) * hyperbolicUmbilicMoment x y z 0 0 = 0 := by
  have h1 := s36b_integrable_hyperbolic_integrand x y z 0 2
  have h2 := s36b_integrable_hyperbolic_integrand x y z 1 0
  have h3 := s36b_integrable_hyperbolic_integrand x y z 0 0
  have hsum : 3 * hyperbolicUmbilicMoment x y z 0 2 +
      (z : ℂ) * hyperbolicUmbilicMoment x y z 1 0 +
      (y : ℂ) * hyperbolicUmbilicMoment x y z 0 0 = ∫ p : ℝ × ℝ,
        (3 * (cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
          (cuspoidContour 1 p.1 ^ 0 * cuspoidContour 1 p.2 ^ 2) *
          exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2)
            x y z)) +
        (z : ℂ) * (cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
          (cuspoidContour 1 p.1 ^ 1 * cuspoidContour 1 p.2 ^ 0) *
          exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2)
            x y z))) +
        (y : ℂ) * (cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
          (cuspoidContour 1 p.1 ^ 0 * cuspoidContour 1 p.2 ^ 0) *
          exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2)
            x y z)) := by
    unfold hyperbolicUmbilicMoment
    rw [integral_add _ (h3.const_mul _), integral_add (h1.const_mul _) (h2.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul]
    exact (h1.const_mul _).add (h2.const_mul _)
  have hF := ((h1.const_mul (3 : ℂ)).add (h2.const_mul (z : ℂ))).add (h3.const_mul (y : ℂ))
  rw [hsum]
  rw [Measure.volume_eq_prod] at hF ⊢
  rw [integral_prod]
  swap
  · exact hF
  refine integral_eq_zero_of_ae (ae_of_all _ fun σ => ?_)
  simp only [Pi.zero_apply]
  rw [← mul_zero (cuspoidContourDir 1 σ), ← s36b_hyperbolic_ibp_t x y z σ, ← integral_const_mul]
  congr 1; funext τ
  ring

/-- Differentiation in `x` raises the `s`-power of the hyperbolic umbilic moment: `∂_x M_{a,b} = i
M_{a+1,b}`. -/
lemma s36b_deriv_hyperbolicUmbilicMoment_x (y z : ℝ) (a b : ℕ) :
    deriv (fun w => hyperbolicUmbilicMoment w y z a b) =
      fun w => I * hyperbolicUmbilicMoment w y z (a + 1) b :=
  funext fun w => (hasDerivAt_hyperbolicUmbilicMoment_x w y z a b).deriv

/-- Differentiation in `y` raises the `t`-power of the hyperbolic umbilic moment: `∂_y M_{a,b} = i
M_{a,b+1}`. -/
lemma s36b_deriv_hyperbolicUmbilicMoment_y (x z : ℝ) (a b : ℕ) :
    deriv (fun w => hyperbolicUmbilicMoment x w z a b) =
      fun w => I * hyperbolicUmbilicMoment x w z a (b + 1) :=
  funext fun w => (hasDerivAt_hyperbolicUmbilicMoment_y x w z a b).deriv

end DLMF.CoalescingSaddles
end
