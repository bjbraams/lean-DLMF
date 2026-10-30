/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Summability.Basic

/-!
# Summability of integrals and of Fourier integrals (DLMF §1.15(iv)–(v))

The Abel and Cesàro summability of integrals over `(-∞, ∞)` (`HasAbelIntegral`,
`HasCesaroIntegral`, 1.15.29–1.15.32), and the Poisson and Fejér kernels of Fourier integrals
(1.15.33–1.15.46) with DLMF's Fourier transform 1.14.1.

Proved: the normalization 1.15.34 of the half-plane Poisson kernel (from Mathlib's
`integral_univ_inv_one_add_sq`), the Abel summability of an absolutely integrable function to its
integral (dominated convergence), and the formulas 1.15.40 and `Re Φ = h` of §1.15(v) by
computing real and imaginary parts under the integral. The other statements are admitted.

**Correction (§1.15(v), after 1.15.40).** DLMF says that `lim_{y→0+} ℑΦ(x + iy)` "is the Hilbert
transform of `f(x)` (§1.14(v))". With DLMF's own normalization 1.14.41 (denominator `t - x`) the
limit is `-ℋ(f)(x)`: by 1.15.40 and 1.14.42 the kernels are `(x - t)/((x - t)² + y²)` and
`(t - x)/((t - x)² + y²)`. Numerically, for `f(t) = 1/(1 + t²)` and `x = 0.6`,
`ℑΦ(x + 0.001i) = 0.4405` while `ℋf(x) = -x/(1 + x²) = -0.4412` (1.14.43). The corrected form is
acquired (`tendsto_im_poissonCauchyIntegral`).
-/

@[expose] public noncomputable section

open MeasureTheory Complex Set Filter Topology

namespace DLMF.AlgebraicAnalytic

/-! ### Summability of integrals (§1.15(iv)) -/

/-- DLMF §1.15(iv): if `∫_{-∞}^{∞} f(t) dt` converges absolutely and equals `L`, then the integral
is Abel summable to `L`. Proved by dominated convergence. -/
@[dlmf 1.15.iv]
theorem hasAbelIntegral_of_integrable {f : ℝ → ℂ} (hf : Integrable f) :
    HasAbelIntegral f (∫ t, f t) := by
  have hmeas : ∀ ε : ℝ, AEStronglyMeasurable (fun t => (Real.exp (-ε * |t|) : ℂ) * f t) :=
    fun ε => (by fun_prop : Continuous fun t : ℝ => (Real.exp (-ε * |t|) : ℂ))
      |>.aestronglyMeasurable.mul hf.aestronglyMeasurable
  have hbound : ∀ ε : ℝ, 0 ≤ ε → ∀ t, ‖(Real.exp (-ε * |t|) : ℂ) * f t‖ ≤ ‖f t‖ := by
    intro ε hε t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have : Real.exp (-ε * |t|) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg t])
    exact mul_le_of_le_one_left (norm_nonneg _) this
  refine ⟨fun ε hε => hf.norm.mono' (hmeas ε)
    (Eventually.of_forall (hbound ε hε.le)), ?_⟩
  have h := tendsto_integral_filter_of_dominated_convergence (l := 𝓝[>] (0 : ℝ))
    (F := fun ε t => (Real.exp (-ε * |t|) : ℂ) * f t) (f := f) (fun t => ‖f t‖)
    (Eventually.of_forall hmeas)
    (eventually_nhdsWithin_of_forall fun ε hε => Eventually.of_forall (hbound ε (le_of_lt hε)))
    hf.norm ?_
  · exact h
  · refine Eventually.of_forall fun t => ?_
    have hc : Tendsto (fun ε : ℝ => (Real.exp (-ε * |t|) : ℂ) * f t) (𝓝 0)
        (𝓝 ((Real.exp (-0 * |t|) : ℂ) * f t)) :=
      ((by fun_prop : Continuous fun ε : ℝ => (Real.exp (-ε * |t|) : ℂ) * f t).tendsto 0)
    simp only [neg_zero, zero_mul, Real.exp_zero, ofReal_one, one_mul] at hc
    exact hc.mono_left nhdsWithin_le_nhds

/-- DLMF §1.15(iv): if `∫_{-∞}^{∞} f(t) dt` converges absolutely and equals `L`, then the integral
is (C,1) summable to `L`. -/
@[dlmf 1.15.iv]
theorem hasCesaroIntegral_of_integrable {f : ℝ → ℂ} (hf : Integrable f) :
    HasCesaroIntegral f (∫ t, f t) := by
  sorry

/-- DLMF §1.15(iv), improper case: if `f` is locally integrable and the improper integral
`lim_{a→-∞, b→∞} ∫_a^b f` equals `L`, then `∫ f = L (C,1)`. -/
@[dlmf 1.15.iv]
theorem hasCesaroIntegral_of_tendsto {f : ℝ → ℂ} (hf : LocallyIntegrable f) {L : ℂ}
    (h : Tendsto (fun p : ℝ × ℝ => ∫ t in p.1..p.2, f t) (atBot ×ˢ atTop) (𝓝 L)) :
    HasCesaroIntegral f L := by
  sorry

/-- DLMF §1.15(iv), improper case: if `f` is locally integrable, the improper integral
`lim_{a→-∞, b→∞} ∫_a^b f` equals `L`, and `e^{-ε|t|} f(t)` is absolutely integrable for each
`ε > 0`, then `∫ f = L (A)`. -/
@[dlmf 1.15.iv]
theorem hasAbelIntegral_of_tendsto {f : ℝ → ℂ} (hf : LocallyIntegrable f) {L : ℂ}
    (h : Tendsto (fun p : ℝ × ℝ => ∫ t in p.1..p.2, f t) (atBot ×ˢ atTop) (𝓝 L))
    (hint : ∀ ε : ℝ, 0 < ε → Integrable fun t => (Real.exp (-ε * |t|) : ℂ) * f t) :
    HasAbelIntegral f L := by
  sorry

/-! ### Poisson kernel of the half-plane (§1.15(v)) -/

/-- DLMF 1.15.34: `(1/2π) ∫ P(x, y) dx = 1` for `y > 0`. Proved from Mathlib's
`integral_univ_inv_one_add_sq`. -/
@[dlmf 1.15.E34]
theorem integral_halfPlanePoissonKernel {y : ℝ} (hy : 0 < y) :
    1 / (2 * Real.pi) * ∫ x, halfPlanePoissonKernel x y = 1 := by
  have h1 : (fun x => halfPlanePoissonKernel x y) =
      fun x => (2 / y) * (1 + (x / y) ^ 2)⁻¹ := by
    funext x
    unfold halfPlanePoissonKernel
    have : y ≠ 0 := hy.ne'
    field_simp
    ring
  rw [h1, integral_const_mul, Measure.integral_comp_div (fun u => (1 + u ^ 2)⁻¹) y,
    integral_univ_inv_one_add_sq, abs_of_pos hy, smul_eq_mul]
  have : y ≠ 0 := hy.ne'
  field_simp

/-- DLMF 1.15.35: `∫_{|x| ≥ δ} P(x, y) dx → 0` as `y → 0+`, for `δ > 0`. -/
@[dlmf 1.15.E35]
theorem tendsto_integral_halfPlanePoissonKernel_tail {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun y => ∫ x in {x : ℝ | δ ≤ |x|}, halfPlanePoissonKernel x y) (𝓝[>] 0) (𝓝 0) := by
  sorry

/-- DLMF 1.15.37: for `f` absolutely integrable and `y > 0`, the Abel mean 1.15.36 of the
Fourier integral is the Poisson integral `h(x, y) = (1/2π) ∫ f(t) P(x - t, y) dt`. -/
@[dlmf 1.15.E37]
theorem fourierAbelMean_eq_poisson {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) {y : ℝ}
    (hy : 0 < y) :
    fourierAbelMean f x y =
      ((2 * Real.pi : ℝ)⁻¹ : ℂ) * ∫ t, f t * (halfPlanePoissonKernel (x - t) y : ℂ) := by
  sorry

/-- DLMF 1.15.38: for `f` absolutely integrable, `∫ |h(x, y) - f(x)| dx → 0` as `y → 0+`. -/
@[dlmf 1.15.E38]
theorem tendsto_integral_norm_fourierAbelMean_sub {f : ℝ → ℂ} (hf : Integrable f) :
    Tendsto (fun y => ∫ x, ‖fourierAbelMean f x y - f x‖) (𝓝[>] 0) (𝓝 0) := by
  sorry

/-- The integrand of 1.15.39 is integrable for integrable `f` and `y > 0`. -/
private lemma g1e_integrable_cauchy {f : ℝ → ℝ} (hf : Integrable f) (x y : ℝ) (hy : 0 < y) :
    Integrable fun t : ℝ => (f t : ℂ) / ((x - t : ℝ) + I * y) := by
  have hne : ∀ t : ℝ, ((x - t : ℝ) : ℂ) + I * y ≠ 0 := by
    intro t h
    have := congrArg Complex.im h
    simp at this
    exact hy.ne' this
  have hb : ∀ t : ℝ, ‖(f t : ℂ) / ((x - t : ℝ) + I * y)‖ ≤ y⁻¹ * ‖f t‖ := by
    intro t
    rw [norm_div, Complex.norm_real, div_eq_inv_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [inv_le_inv₀ (norm_pos_iff.mpr (hne t)) hy]
    have : |(((x - t : ℝ) : ℂ) + I * y).im| ≤ ‖((x - t : ℝ) : ℂ) + I * y‖ := abs_im_le_norm _
    simpa [abs_of_pos hy] using this
  refine (hf.norm.const_mul y⁻¹).mono' ?_ (Eventually.of_forall hb)
  simp_rw [div_eq_mul_inv]
  refine (Complex.continuous_ofReal.comp_aestronglyMeasurable hf.aestronglyMeasurable).mul ?_
  have hc : Continuous fun t : ℝ => ((x - t : ℝ) : ℂ) + I * y := by fun_prop
  exact (hc.inv₀ hne).aestronglyMeasurable

/-- Pointwise splitting of the integrand of 1.15.39 into real and imaginary parts. -/
private lemma g1e_cauchy_split (F u y : ℝ) (hy : 0 < y) :
    I / Real.pi * ((F : ℂ) / ((u : ℂ) + I * y)) =
      ((F * y / (Real.pi * (u ^ 2 + y ^ 2)) : ℝ) : ℂ) +
        I * ((F * u / (Real.pi * (u ^ 2 + y ^ 2)) : ℝ) : ℂ) := by
  have hD : 0 < u ^ 2 + y ^ 2 := by positivity
  have hpi := Real.pi_pos
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.div_re, Complex.div_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply, Complex.add_im,
      Complex.mul_im]
    field_simp
    ring
  · simp only [Complex.add_re, Complex.mul_re, Complex.div_re, Complex.div_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply, Complex.add_im,
      Complex.mul_im]
    field_simp
    ring

/-- The integral in 1.15.39 at `x + iy`, rewritten with a real-coordinate integrand. -/
private lemma g1e_poissonCauchy_eq {f : ℝ → ℝ} (x y : ℝ) :
    poissonCauchyIntegral (fun t => (f t : ℂ)) (x + y * I) =
      ∫ t : ℝ, I / Real.pi * ((f t : ℂ) / ((x - t : ℝ) + I * y)) := by
  unfold poissonCauchyIntegral
  rw [integral_const_mul]
  simp

/-- DLMF §1.15(v), after 1.15.39: for real absolutely integrable `f` and `y > 0`, the real part
of `Φ(x + iy)` is the Poisson integral `h(x, y) = (1/2π) ∫ f(t) P(x - t, y) dt`. -/
@[dlmf 1.15.v]
theorem re_poissonCauchyIntegral {f : ℝ → ℝ} (hf : Integrable f) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    (poissonCauchyIntegral (fun t => (f t : ℂ)) (x + y * I)).re =
      (2 * Real.pi)⁻¹ * ∫ t, f t * halfPlanePoissonKernel (x - t) y := by
  have hI := (g1e_integrable_cauchy hf x y hy).const_mul (I / Real.pi)
  rw [g1e_poissonCauchy_eq, ← RCLike.re_to_complex, ← integral_re hI, ← integral_const_mul]
  congr 1
  funext t
  rw [RCLike.re_to_complex, g1e_cauchy_split _ _ _ hy]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im]
  unfold halfPlanePoissonKernel
  have hD : 0 < (x - t) ^ 2 + y ^ 2 := by positivity
  have hpi := Real.pi_pos
  field_simp
  ring

/-- DLMF 1.15.40: for real absolutely integrable `f` and `y > 0`,
`ℑΦ(x + iy) = (1/π) ∫ f(t) (x - t)/((x - t)² + y²) dt`, the conjugate Poisson integral. -/
@[dlmf 1.15.E40]
theorem im_poissonCauchyIntegral {f : ℝ → ℝ} (hf : Integrable f) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    (poissonCauchyIntegral (fun t => (f t : ℂ)) (x + y * I)).im =
      Real.pi⁻¹ * ∫ t, f t * ((x - t) / ((x - t) ^ 2 + y ^ 2)) := by
  have hI := (g1e_integrable_cauchy hf x y hy).const_mul (I / Real.pi)
  rw [g1e_poissonCauchy_eq, ← RCLike.im_to_complex, ← integral_im hI, ← integral_const_mul]
  congr 1
  funext t
  rw [RCLike.im_to_complex, g1e_cauchy_split _ _ _ hy]
  simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_im]
  have hD : 0 < (x - t) ^ 2 + y ^ 2 := by positivity
  have hpi := Real.pi_pos
  field_simp
  ring

/-- DLMF §1.15(v), after 1.15.39: for real absolutely integrable `f`, `Φ` (1.15.39) is analytic in
the upper half-plane. -/
@[dlmf 1.15.v]
theorem differentiableOn_poissonCauchyIntegral {f : ℝ → ℝ} (hf : Integrable f) :
    DifferentiableOn ℂ (poissonCauchyIntegral fun t => (f t : ℂ)) {z : ℂ | 0 < z.im} := by
  sorry

/-- DLMF §1.15(v), after 1.15.40, **corrected sign**: for real absolutely integrable `f`, for
almost every `x`, `ℑΦ(x + iy) → -ℋ(f)(x)` as `y → 0+`, with DLMF's Hilbert transform 1.14.41.
DLMF says the limit "is the Hilbert transform"; the sign is opposite (module docstring). -/
@[dlmf 1.15.v]
theorem tendsto_im_poissonCauchyIntegral {f : ℝ → ℝ} (hf : Integrable f) :
    ∀ᵐ x : ℝ, Tendsto (fun y : ℝ => (poissonCauchyIntegral (fun t => (f t : ℂ)) (x + y * I)).im)
      (𝓝[>] 0) (𝓝 (-(hilbertTransform (fun t => (f t : ℂ)) x).re)) := by
  sorry

/-! ### Fejér kernel of Fourier integrals (§1.15(v)) -/

/-- DLMF 1.15.42: `∫ K_R(s) ds = 1` for `R > 0`. -/
@[dlmf 1.15.E42]
theorem integral_fejerKernelLine {R : ℝ} (hR : 0 < R) : ∫ s, fejerKernelLine R s = 1 := by
  sorry

/-- DLMF 1.15.43: `∫_{|s| ≥ δ} K_R(s) ds → 0` as `R → ∞`, for `δ > 0`. -/
@[dlmf 1.15.E43]
theorem tendsto_integral_fejerKernelLine_tail {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun R => ∫ s in {s : ℝ | δ ≤ |s|}, fejerKernelLine R s) atTop (𝓝 0) := by
  sorry

/-- DLMF 1.15.45: for `f` absolutely integrable and `R > 0`, the Cesàro mean 1.15.44 of the
Fourier integral is `σ_R(θ) = ∫ f(t) K_R(θ - t) dt`. -/
@[dlmf 1.15.E45]
theorem fourierCesaroMeanIntegral_eq {f : ℝ → ℂ} (hf : Integrable f) {R : ℝ} (hR : 0 < R)
    (θ : ℝ) :
    fourierCesaroMeanIntegral f R θ = ∫ t, f t * (fejerKernelLine R (θ - t) : ℂ) := by
  sorry

/-- DLMF 1.15.46: for `f` absolutely integrable, `∫ |σ_R(θ) - f(θ)| dθ → 0` as `R → ∞`. -/
@[dlmf 1.15.E46]
theorem tendsto_integral_norm_fourierCesaroMeanIntegral_sub {f : ℝ → ℂ} (hf : Integrable f) :
    Tendsto (fun R => ∫ θ, ‖fourierCesaroMeanIntegral f R θ - f θ‖) atTop (𝓝 0) := by
  sorry

end DLMF.AlgebraicAnalytic
