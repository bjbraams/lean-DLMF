/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.CoalescingSaddles.Defs
public import DLMF.CoalescingSaddles.CanonicalIntegrals

/-!
# Leading-order asymptotics of the canonical integrals: DLMF §36.11

* 36.11.1–36.11.2: the stationary-phase approximation of `Ψ_K(x)` far from the origin, away
  from the bifurcation set. DLMF does not say along which path `x → ∞`; we state it along the
  scaling rays of §36.6, `x(k) = (x₁k^{γ₁}, …, x_Kk^{γ_K})` (`cuspoidScaledCoords`) with
  `k → ∞`, for `x ∉` bifurcation set: on this ray `Ψ_K(x(k)) = k^{1/(K+2)} ∫ exp(ikΦ_K(τ; x)) dτ`,
  and 36.11.2 is the stationary-phase theorem for the large parameter `k`. Each term of the sum is
  of exact order `k^{1/(K+2) - 1/2}`, so DLMF's factors `1 + o(1)` amount to an `o` of that order.
* 36.11.3–36.11.8: asymptotics along symmetry lines, stated with `Asymptotics.IsLittleO`.

**Corrections (36.11.7, 36.11.8).** DLMF states both formulas for `z → ±∞`. They hold for
`z → +∞` only. By 36.2.24, `Ψ^{(U)}(0, 0, -z) = conj Ψ^{(U)}(0, 0, z)`, and conjugating the printed
formulas gives, for `z → -∞`,
`Ψ^{(E)}(0, 0, z) = (π/z)(i - √3 exp(4iz³/27) + o(1))` and
`Ψ^{(H)}(0, 0, z) = (2π/z)(-1 - (i/√3) exp(iz³/27) + o(1))`,
that is `(π/|z|)(i sign z + √3 e^{4iz³/27})` and `(2π/|z|)(1 - i sign z e^{iz³/27}/√3)`. Direct
quadrature confirms this: `Ψ^{(E)}(0, 0, -6) = 0.75621 - 1.01820i` against the printed
`-0.75656 - 0.02351i` and the corrected `0.75656 - 1.02369i`; `Ψ^{(H)}(0, 0, -12) =
0.80126 + 0.11760i` against the printed `-0.24548 + 0.11846i` and the corrected
`0.80172 + 0.11846i`. The `z → -∞` statements below are the corrected forms, derived from the
`z → +∞` statements and 36.2.24.

**36.11.6.** DLMF's `z → +∞` remainder `o(1)` is weaker than the size `|z|^{-1/3}` of the leading
term; we state the stronger `o(|z|^{-1/3})` (stronger than DLMF), which numerical quadrature
supports (relative error `3·10⁻⁵` at `z = 20` and `9·10⁻⁷` at `z = 60`).

Other numerical checks: 36.11.2 for `K = 1, 2, 3` at points with one to three real critical
points, 36.11.3–36.11.5 and 36.11.6 (`z → -∞`) at moderate arguments; relative errors decrease as
the argument grows.

**Proofs.** 36.11.3 for `y → +∞` (`cuspoidIntegral_two_zero_atTop`) is proved by the scaling
`t = u/√y` and dominated convergence to a complex Gaussian integral. 36.11.6 for `z → +∞`
(`cuspoidIntegral_three_z_atTop`) is proved by splitting `Ψ₃(0, 0, z) = 2 Re ∫_0^∞`, the
scaling `r = u/z^{1/3}`, dominated convergence to `∫_0^∞ e^{iπ/10} exp(i(ue^{iπ/10})³) du`, and
rotation of that ray to the angle `π/6` (the `θ`-derivative of the ray integral vanishes), where
it equals `e^{iπ/6} Γ(4/3)`.
-/

@[expose] public noncomputable section

open Complex Filter Asymptotics
open scoped Real Topology ComplexConjugate

namespace DLMF.CoalescingSaddles

/-! ### The stationary-phase approximation (36.11.1–36.11.2) -/

/-- Leading-order asymptotics of the cuspoid canonical integral (DLMF 36.11.2): along the scaling
ray `x(k) = cuspoidScaledCoords K ξ k` through a point `ξ` outside the bifurcation set,
`Ψ_K(x(k)) = √(2π) ∑ⱼ exp(i(Φ_K(tⱼ; x(k)) + ¼π(-1)^{j+K+1})) |Φ_K''(tⱼ; x(k))|^{-1/2}
  + o(k^{1/(K+2) - 1/2})` as `k → ∞`, the sum (`cuspoidStationaryPhaseSum`) running over the real
critical points ordered as in 36.11.1. -/
@[dlmf 36.11.E2]
theorem cuspoidIntegral_sub_stationaryPhaseSum_isLittleO (K : ℕ) (ξ : Fin K → ℝ)
    (hξ : ξ ∉ cuspoidBifurcationSet K) :
    (fun k : ℝ => cuspoidIntegral K (cuspoidScaledCoords K ξ k) -
        cuspoidStationaryPhaseSum K (cuspoidScaledCoords K ξ k)) =o[atTop]
      (fun k : ℝ => k ^ (1 / ((K : ℝ) + 2) - 1 / 2)) := by
  sorry

/-! ### Helpers for 36.11.3 (`y → +∞`): scaling and dominated convergence

With `t = u/√y` the Pearcey integral on the line `x = 0` is `y^{-1/2}` times
`∫ e^{iπ/8} exp(-u⁴/y² + i e^{iπ/4} u²) du`; the integrand is dominated by `exp(-u²/√2)`, and
the limit is a complex Gaussian integral. -/

section q2t

open MeasureTheory Set

/-- The Pearcey integrand on the symmetry line after the scaling `t = u/√y`. -/
def q2t_pearceyScaled (y u : ℝ) : ℂ :=
  exp (((π / 8 : ℝ) : ℂ) * I) *
    exp (-((u ^ 4 / y ^ 2 : ℝ) : ℂ) + I * exp (((π / 4 : ℝ) : ℂ) * I) * (u : ℂ) ^ 2)

lemma q2t_cuspoidAngle_two : cuspoidAngle 2 = π / 8 := by
  unfold cuspoidAngle; norm_num

lemma q2t_pearcey_integrand (y r : ℝ) :
    cuspoidContourDir 2 r * exp (I * cuspoidPotential 2 (cuspoidContour 2 r) ![0, y]) =
      exp (((π / 8 : ℝ) : ℂ) * I) * exp (-((r ^ 4 : ℝ) : ℂ) +
        I * exp (((π / 4 : ℝ) : ℂ) * I) * ((y * r ^ 2 : ℝ) : ℂ)) := by
  have hd : cuspoidContourDir 2 r = exp (((π / 8 : ℝ) : ℂ) * I) := by
    rw [s36a_dir_of_even (by decide), q2t_cuspoidAngle_two]
  rw [hd, cuspoidPotential_two]
  congr 2
  have h4 := cuspoidContour_pow 2 r
  have h2 : cuspoidContour 2 r ^ 2 = (r : ℂ) ^ 2 * exp (((π / 4 : ℝ) : ℂ) * I) := by
    rw [cuspoidContour, hd, mul_pow, ← exp_nat_mul]; push_cast; ring_nf
  rw [show (2 + 2 : ℕ) = 4 from rfl] at h4
  rw [h4, h2, show |r| ^ 4 = r ^ 4 from by rw [show 4 = 2 * 2 from rfl, pow_mul, sq_abs,
    ← pow_mul]]
  push_cast
  linear_combination ((r : ℂ) ^ 4) * I_sq

lemma q2t_pearcey_scale {y : ℝ} (hy : 0 < y) :
    cuspoidIntegral 2 ![0, y] =
      ((1 / Real.sqrt y : ℝ) : ℂ) * ∫ u : ℝ, q2t_pearceyScaled y u := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hss : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
  set g : ℝ → ℂ := fun r => exp (((π / 8 : ℝ) : ℂ) * I) * exp (-((r ^ 4 : ℝ) : ℂ) +
    I * exp (((π / 4 : ℝ) : ℂ) * I) * ((y * r ^ 2 : ℝ) : ℂ)) with hg
  have h1 : cuspoidIntegral 2 ![0, y] = ∫ r, g r := by
    unfold cuspoidIntegral; simp only [q2t_pearcey_integrand, hg]
  have h2 : (fun u : ℝ => q2t_pearceyScaled y u) = fun u => g (u / Real.sqrt y) := by
    funext u
    have h4 : Real.sqrt y ^ 4 = y ^ 2 := by
      calc Real.sqrt y ^ 4 = (Real.sqrt y ^ 2) ^ 2 := by ring
        _ = y ^ 2 := by rw [hss]
    have e1 : (u / Real.sqrt y) ^ 4 = u ^ 4 / y ^ 2 := by rw [div_pow, h4]
    have e2 : y * (u / Real.sqrt y) ^ 2 = u ^ 2 := by
      rw [div_pow, hss]; field_simp
    simp only [q2t_pearceyScaled, hg, e1, e2]
    push_cast; ring_nf
  rw [h1, h2, Measure.integral_comp_div, abs_of_pos hs, Complex.real_smul, ← mul_assoc,
    ← ofReal_mul, one_div_mul_cancel hs.ne', ofReal_one, one_mul]

lemma q2t_norm_pearceyScaled_le (y u : ℝ) :
    ‖q2t_pearceyScaled y u‖ ≤ Real.exp (-(Real.sqrt 2 / 2) * u ^ 2) := by
  rw [q2t_pearceyScaled, norm_mul, norm_exp_ofReal_mul_I, one_mul, norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have hre : (I * exp (((π / 4 : ℝ) : ℂ) * I)).re = -(Real.sqrt 2 / 2) := by
    rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
    simp
  have : (-((u ^ 4 / y ^ 2 : ℝ) : ℂ) + I * exp (((π / 4 : ℝ) : ℂ) * I) * (u : ℂ) ^ 2).re =
      -(u ^ 4 / y ^ 2) + -(Real.sqrt 2 / 2) * u ^ 2 := by
    rw [add_re, neg_re, ofReal_re, show (u : ℂ) ^ 2 = ((u ^ 2 : ℝ) : ℂ) by push_cast; ring,
      re_mul_ofReal, hre]
  rw [this]
  have : 0 ≤ u ^ 4 / y ^ 2 := by positivity
  linarith

lemma q2t_tendsto_pearceyScaled :
    Tendsto (fun y : ℝ => ∫ u : ℝ, q2t_pearceyScaled y u) atTop
      (𝓝 (∫ u : ℝ, exp (((π / 8 : ℝ) : ℂ) * I) *
        exp (I * exp (((π / 4 : ℝ) : ℂ) * I) * (u : ℂ) ^ 2))) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u => Real.exp (-(Real.sqrt 2 / 2) * u ^ 2)) (Eventually.of_forall fun y => ?_)
    (Eventually.of_forall fun y => ae_of_all _ fun u => q2t_norm_pearceyScaled_le y u)
    (integrable_exp_neg_mul_sq (by positivity)) (ae_of_all _ fun u => ?_)
  · unfold q2t_pearceyScaled; fun_prop
  · have h0 : Tendsto (fun y : ℝ => u ^ 4 / y ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
    have h1 : Tendsto (fun y : ℝ => q2t_pearceyScaled y u) atTop
        (𝓝 (exp (((π / 8 : ℝ) : ℂ) * I) * exp (-((0 : ℝ) : ℂ) +
          I * exp (((π / 4 : ℝ) : ℂ) * I) * (u : ℂ) ^ 2))) := by
      unfold q2t_pearceyScaled
      exact tendsto_const_nhds.mul (((continuous_ofReal.tendsto 0).comp h0).neg.add
        tendsto_const_nhds).cexp
    simpa using h1

/-- The Fresnel-type limit: `∫ e^{iπ/8} exp(i e^{iπ/4} u²) du = √π e^{iπ/4}`. -/
lemma q2t_pearcey_limit :
    ∫ u : ℝ, exp (((π / 8 : ℝ) : ℂ) * I) * exp (I * exp (((π / 4 : ℝ) : ℂ) * I) * (u : ℂ) ^ 2) =
      (Real.sqrt π : ℂ) * exp (I * π / 4) := by
  set b : ℂ := exp (-(((π / 4 : ℝ) : ℂ) * I)) with hb
  have hbI : I * exp (((π / 4 : ℝ) : ℂ) * I) = -b := by
    rw [hb, show -(((π / 4 : ℝ) : ℂ) * I) = ((-(π / 4) : ℝ) : ℂ) * I by push_cast; ring,
      exp_mul_I, exp_mul_I, ← ofReal_cos, ← ofReal_sin, ← ofReal_cos, ← ofReal_sin, Real.cos_neg,
      Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]
    push_cast
    linear_combination ((Real.sqrt 2 : ℂ) / 2) * I_sq
  have hre : 0 < b.re := by
    rw [hb, show -(((π / 4 : ℝ) : ℂ) * I) = ((-(π / 4) : ℝ) : ℂ) * I by push_cast; ring,
      exp_ofReal_mul_I_re, Real.cos_neg, Real.cos_pi_div_four]
    positivity
  simp only [hbI]
  rw [integral_const_mul, integral_gaussian_complex hre]
  have hπb : (π : ℂ) / b = exp (((Real.log π : ℝ) : ℂ) + ((π / 4 : ℝ) : ℂ) * I) := by
    rw [exp_add, ← ofReal_exp, Real.exp_log Real.pi_pos, hb, div_eq_mul_inv, ← exp_neg, neg_neg]
  have hpos : (π : ℂ) / b ≠ 0 := by rw [hπb]; exact exp_ne_zero _
  rw [cpow_def_of_ne_zero hpos, hπb, log_exp (by simp; linarith [Real.pi_pos])
    (by simp; linarith [Real.pi_pos])]
  have hsq : (Real.sqrt π : ℂ) = exp (((Real.log π : ℝ) : ℂ) * (1 / 2)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos Real.pi_pos, ofReal_exp]; push_cast; ring_nf
  rw [hsq, ← exp_add, ← exp_add]
  congr 1; push_cast; ring

/-- The cubic ray integrand `e^{iθ} exp(i (r e^{iθ})³)`. -/
def q2t_cubicRay (θ r : ℝ) : ℂ :=
  exp ((θ : ℂ) * I) * exp (I * ((r : ℂ) * exp ((θ : ℂ) * I)) ^ 3)

/-- Its `θ`-derivative `i e^{iθ} exp(i (r e^{iθ})³) (1 + 3i (r e^{iθ})³)`. -/
def q2t_cubicRayDeriv (θ r : ℝ) : ℂ :=
  I * exp ((θ : ℂ) * I) * exp (I * ((r : ℂ) * exp ((θ : ℂ) * I)) ^ 3) *
    (1 + 3 * I * ((r : ℂ) * exp ((θ : ℂ) * I)) ^ 3)

lemma q2t_hasDerivAt_cubicRay (θ r : ℝ) :
    HasDerivAt (fun θ => q2t_cubicRay θ r) (q2t_cubicRayDeriv θ r) θ := by
  have hE : HasDerivAt (fun θ : ℝ => exp ((θ : ℂ) * I)) (exp ((θ : ℂ) * I) * I) θ := by
    have := ((hasDerivAt_id (θ : ℂ)).mul_const I).cexp.comp_ofReal
    simpa using this
  have h2 := ((((hE.const_mul (r : ℂ)).pow 3).const_mul I).cexp)
  have h := hE.mul h2
  unfold q2t_cubicRay q2t_cubicRayDeriv
  convert h using 1
  simp only [Pi.pow_apply]; push_cast; ring

lemma q2t_cubicRay_re (θ r : ℝ) :
    (I * ((r : ℂ) * exp ((θ : ℂ) * I)) ^ 3).re = -(r ^ 3 * Real.sin (3 * θ)) := by
  have : ((r : ℂ) * exp ((θ : ℂ) * I)) ^ 3 = ((r ^ 3 : ℝ) : ℂ) * exp (((3 * θ : ℝ) : ℂ) * I) := by
    rw [mul_pow, ← exp_nat_mul]; push_cast; ring_nf
  rw [this, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  simp only [mul_re, mul_im, add_re, add_im, I_re, I_im, ofReal_re, ofReal_im]
  ring

lemma q2t_sin_three_ge {θ : ℝ} (h1 : π / 12 ≤ θ) (h2 : θ ≤ π / 4) :
    Real.sqrt 2 / 2 ≤ Real.sin (3 * θ) := by
  rw [← Real.cos_pi_div_four, ← Real.cos_sub_pi_div_two, ← Real.cos_abs (3 * θ - π / 2)]
  apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos])
  rw [abs_le]; constructor <;> linarith

lemma q2t_norm_exp_cubic_le {θ r : ℝ} (h1 : π / 12 ≤ θ) (h2 : θ ≤ π / 4) (hr : 0 ≤ r) :
    ‖exp (I * ((r : ℂ) * exp ((θ : ℂ) * I)) ^ 3)‖ ≤ Real.exp (-(Real.sqrt 2 / 2) * r ^ 3) := by
  rw [norm_exp, q2t_cubicRay_re]
  refine Real.exp_le_exp.mpr ?_
  have := q2t_sin_three_ge h1 h2
  have := pow_nonneg hr 3
  nlinarith

lemma q2t_norm_cube (θ r : ℝ) (hr : 0 ≤ r) : ‖((r : ℂ) * exp ((θ : ℂ) * I)) ^ 3‖ = r ^ 3 := by
  rw [norm_pow, norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr]

lemma q2t_norm_cubicRayDeriv_le {θ r : ℝ} (h1 : π / 12 ≤ θ) (h2 : θ ≤ π / 4) (hr : 0 ≤ r) :
    ‖q2t_cubicRayDeriv θ r‖ ≤ (1 + 3 * r ^ 3) * Real.exp (-(Real.sqrt 2 / 2) * r ^ 3) := by
  unfold q2t_cubicRayDeriv
  rw [norm_mul, norm_mul, norm_mul, norm_I, norm_exp_ofReal_mul_I, one_mul, one_mul, mul_comm]
  refine mul_le_mul ?_ (q2t_norm_exp_cubic_le h1 h2 hr) (norm_nonneg _) (by positivity)
  refine (norm_add_le _ _).trans ?_
  rw [norm_one, norm_mul, norm_mul, norm_I, q2t_norm_cube θ r hr]; simp

lemma q2t_integrableOn_cubic_bound :
    IntegrableOn (fun r : ℝ => (1 + 3 * r ^ 3) * Real.exp (-(Real.sqrt 2 / 2) * r ^ 3))
      (Ioi 0) := by
  have h0 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 0) (p := 3) (b := Real.sqrt 2 / 2)
    (by norm_num) (by norm_num) (by positivity)
  have h3 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 3) (p := 3) (b := Real.sqrt 2 / 2)
    (by norm_num) (by norm_num) (by positivity)
  refine (h0.add (h3.const_mul 3)).congr_fun (fun r hr => ?_) measurableSet_Ioi
  have hr' : (0 : ℝ) ≤ r := le_of_lt hr
  simp only [Pi.add_apply, Real.rpow_zero, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  push_cast; ring

/-- `∫_0^∞ ∂_θ(e^{iθ} exp(i(re^{iθ})³)) dr = 0`: the integrand is `i ∂_r(r e^{iθ} exp(i(re^{iθ})³))`
and the boundary terms vanish. -/
lemma q2t_integral_cubicRayDeriv {θ : ℝ} (h1 : π / 12 ≤ θ) (h2 : θ ≤ π / 4) :
    ∫ r in Ioi (0 : ℝ), q2t_cubicRayDeriv θ r = 0 := by
  set E : ℂ := exp ((θ : ℂ) * I)
  set k : ℝ → ℂ := fun r => (r : ℂ) * E * exp (I * ((r : ℂ) * E) ^ 3) with hk
  have hd : ∀ r : ℝ, HasDerivAt k ((-I) * q2t_cubicRayDeriv θ r) r := by
    intro r
    have h := (((hasDerivAt_id (r : ℂ)).mul_const E).mul
      ((((hasDerivAt_id (r : ℂ)).mul_const E).pow 3).const_mul I).cexp).comp_ofReal
    convert h using 1
    · funext y; simp [hk]
    unfold q2t_cubicRayDeriv
    simp only [id]
    push_cast
    linear_combination (-(E * exp (I * ((r : ℂ) * E) ^ 3)) *
      (1 + 3 * I * ((r : ℂ) * E) ^ 3)) * I_sq
  have hint : IntegrableOn (fun r => (-I) * q2t_cubicRayDeriv θ r) (Ioi 0) := by
    refine (q2t_integrableOn_cubic_bound.mono' ?_ ?_).const_mul (-I)
    · exact (by unfold q2t_cubicRayDeriv; fun_prop : Continuous fun r => q2t_cubicRayDeriv θ r)
        |>.aestronglyMeasurable
    · exact ae_restrict_of_forall_mem measurableSet_Ioi fun r hr =>
        q2t_norm_cubicRayDeriv_le h1 h2 (le_of_lt hr)
  have htend : Tendsto k atTop (𝓝 0) := by
    set c := Real.sqrt 2 / 2
    have hc : 0 < c := by positivity
    have h0 : Tendsto (fun r : ℝ => c⁻¹ * ((c * r) ^ 1 * Real.exp (-(c * r)))) atTop (𝓝 0) := by
      simpa using ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
        (tendsto_id.const_mul_atTop hc)).const_mul c⁻¹
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [eventually_ge_atTop 1] with r hr
    rw [hk]; simp only
    rw [norm_mul, norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
    have hb := q2t_norm_exp_cubic_le h1 h2 (by linarith : (0 : ℝ) ≤ r)
    have hr3 : r ≤ r ^ 3 := by
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ r)
        (by linarith : (0 : ℝ) ≤ r - 1)) (by linarith : (0 : ℝ) ≤ r + 1)]
    have : Real.exp (-(c * r ^ 3)) ≤ Real.exp (-(c * r)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    calc r * ‖exp (I * ((r : ℂ) * E) ^ 3)‖ ≤ r * Real.exp (-(c * r)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          refine hb.trans ?_; rw [neg_mul]; exact this
      _ = _ := by field_simp
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (a := 0) (m := 0)
    (hd 0).continuousAt.continuousWithinAt (fun r _ => hd r) hint htend
  rw [integral_const_mul] at h
  have hk0 : k 0 = 0 := by simp [hk]
  rw [hk0, sub_zero] at h
  have := congrArg (fun w => I * w) h
  simp only [← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul, mul_zero] at this
  exact this

lemma q2t_norm_cubicRay_le {θ r : ℝ} (h1 : π / 12 ≤ θ) (h2 : θ ≤ π / 4) (hr : 0 ≤ r) :
    ‖q2t_cubicRay θ r‖ ≤ (1 + 3 * r ^ 3) * Real.exp (-(Real.sqrt 2 / 2) * r ^ 3) := by
  unfold q2t_cubicRay
  rw [norm_mul, norm_exp_ofReal_mul_I, one_mul]
  refine (q2t_norm_exp_cubic_le h1 h2 hr).trans ?_
  have := pow_nonneg hr 3
  exact le_mul_of_one_le_left (by positivity) (by linarith)

/-- The cubic ray integral `G(θ) = ∫_0^∞ e^{iθ} exp(i(re^{iθ})³) dr`. -/
def q2t_cubicG (θ : ℝ) : ℂ := ∫ r in Ioi (0 : ℝ), q2t_cubicRay θ r

lemma q2t_hasDerivAt_cubicG {θ₀ : ℝ} (h1 : π / 10 ≤ θ₀) (h2 : θ₀ ≤ π / 6) :
    HasDerivAt q2t_cubicG 0 θ₀ := by
  have hpi := Real.pi_pos
  have hball : ∀ θ ∈ Metric.ball θ₀ (π / 60), π / 12 ≤ θ ∧ θ ≤ π / 4 := by
    intro θ hθ
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hθ
    constructor <;> linarith [hθ.1, hθ.2]
  have hcont : ∀ θ, Continuous fun r => q2t_cubicRay θ r := fun θ => by
    unfold q2t_cubicRay; fun_prop
  have hcont' : ∀ θ, Continuous fun r => q2t_cubicRayDeriv θ r := fun θ => by
    unfold q2t_cubicRayDeriv; fun_prop
  have h0 := hball θ₀ (Metric.mem_ball_self (by positivity))
  have hint : Integrable (fun r => q2t_cubicRay θ₀ r) (volume.restrict (Ioi 0)) :=
    q2t_integrableOn_cubic_bound.mono' (hcont θ₀).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr =>
        q2t_norm_cubicRay_le h0.1 h0.2 (le_of_lt hr))
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun θ r => q2t_cubicRay θ r) (F' := fun θ r => q2t_cubicRayDeriv θ r) (x₀ := θ₀)
    (bound := fun r => (1 + 3 * r ^ 3) * Real.exp (-(Real.sqrt 2 / 2) * r ^ 3))
    (s := Metric.ball θ₀ (π / 60)) (Metric.ball_mem_nhds _ (by positivity))
    (Eventually.of_forall fun θ => (hcont θ).aestronglyMeasurable) hint
    (hcont' θ₀).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr θ hθ =>
      q2t_norm_cubicRayDeriv_le (hball θ hθ).1 (hball θ hθ).2 (le_of_lt hr))
    q2t_integrableOn_cubic_bound
    (ae_of_all _ fun r θ _ => q2t_hasDerivAt_cubicRay θ r)
  have h2' := h.2
  rw [q2t_integral_cubicRayDeriv h0.1 h0.2] at h2'
  exact h2'

lemma q2t_cubicG_eq {θ : ℝ} (h1 : π / 10 ≤ θ) (h2 : θ ≤ π / 6) :
    q2t_cubicG θ = q2t_cubicG (π / 10) := by
  have hle : π / 10 ≤ π / 6 := by linarith [Real.pi_pos]
  refine constant_of_has_deriv_right_zero (f := q2t_cubicG) (a := π / 10) (b := π / 6)
    (fun x hx => (q2t_hasDerivAt_cubicG hx.1 hx.2).continuousAt.continuousWithinAt)
    (fun x hx => (q2t_hasDerivAt_cubicG hx.1 hx.2.le).hasDerivWithinAt) θ ⟨h1, h2⟩

lemma q2t_cubicG_pi_div_six :
    q2t_cubicG (π / 6) = exp (((π / 6 : ℝ) : ℂ) * I) * (Real.Gamma (1 / 3 + 1) : ℂ) := by
  have hE : exp (((π / 6 : ℝ) : ℂ) * I) ^ 3 = I := by
    rw [← exp_nat_mul, show ((3 : ℕ) : ℂ) * (((π / 6 : ℝ) : ℂ) * I) = ((π / 2 : ℝ) : ℂ) * I by
      push_cast; ring, exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    simp
  have hpt : ∀ r : ℝ, q2t_cubicRay (π / 6) r =
      exp (((π / 6 : ℝ) : ℂ) * I) * ((Real.exp (-r ^ 3) : ℝ) : ℂ) := by
    intro r
    unfold q2t_cubicRay
    rw [mul_pow, hE, ofReal_exp]
    congr 2
    push_cast
    linear_combination (r : ℂ) ^ 3 * I_sq
  unfold q2t_cubicG
  simp_rw [hpt]
  rw [integral_const_mul, integral_complex_ofReal, s36a_integral_exp_neg_pow 3 (by norm_num)]
  push_cast; ring_nf

lemma q2t_cuspoidAngle_three : cuspoidAngle 3 = π / 10 := by
  unfold cuspoidAngle; norm_num

lemma q2t_swallow_pot (z : ℝ) (t : ℂ) :
    cuspoidPotential 3 t ![0, 0, z] = t ^ 5 + (z : ℂ) * t ^ 3 := by
  simp [cuspoidPotential, Fin.sum_univ_three]

/-- The swallowtail integrand on the `z`-axis. -/
def q2t_swF (z r : ℝ) : ℂ :=
  cuspoidContourDir 3 r * exp (I * cuspoidPotential 3 (cuspoidContour 3 r) ![0, 0, z])

lemma q2t_swF_nonneg (z : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    q2t_swF z r = exp (((π / 10 : ℝ) : ℂ) * I) * exp (I * (((r : ℂ) *
      exp (((π / 10 : ℝ) : ℂ) * I)) ^ 5 + (z : ℂ) *
        ((r : ℂ) * exp (((π / 10 : ℝ) : ℂ) * I)) ^ 3)) := by
  unfold q2t_swF cuspoidContour
  rw [s36a_dir_of_nonneg 3 hr, q2t_cuspoidAngle_three, q2t_swallow_pot]

lemma q2t_swF_neg (z : ℝ) {s : ℝ} (hs : 0 < s) :
    q2t_swF z (-s) = (starRingEnd ℂ) (q2t_swF z s) := by
  have hn : ¬ Even 3 := by decide
  unfold q2t_swF cuspoidContour
  rw [s36a_dir_of_odd_neg hn (by linarith : -s < 0), s36a_dir_of_nonneg 3 hs.le,
    q2t_cuspoidAngle_three, q2t_swallow_pot, q2t_swallow_pot, map_mul, ← exp_conj, ← exp_conj]
  congr 2
  · simp only [map_mul, conj_I, conj_ofReal]; ring
  · simp only [map_mul, map_add, map_pow, conj_I, conj_ofReal, ← exp_conj]
    push_cast
    ring_nf

lemma q2t_swallow_split (z : ℝ) :
    cuspoidIntegral 3 ![0, 0, z] =
      (((2 * (∫ r in Ioi (0 : ℝ), q2t_swF z r).re : ℝ)) : ℂ) := by
  have hint : Integrable (q2t_swF z) := integrable_cuspoidIntegral_integrand 3 ![0, 0, z]
  have h := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hint
  rw [compl_Ioi] at h
  have hc : ∫ r in Iic (0 : ℝ), q2t_swF z r =
      (starRingEnd ℂ) (∫ r in Ioi (0 : ℝ), q2t_swF z r) := by
    rw [← integral_conj, show Iic (0 : ℝ) = Iic (-0) by simp,
      ← integral_comp_neg_Ioi (0 : ℝ) (q2t_swF z)]
    exact setIntegral_congr_fun measurableSet_Ioi fun r (hr : r ∈ Ioi 0) =>
      q2t_swF_neg z (mem_Ioi.mp hr)
  have : cuspoidIntegral 3 ![0, 0, z] = ∫ r, q2t_swF z r := rfl
  rw [this, ← h, hc, add_conj]

/-- The swallowtail integrand after the scaling `r = u/s`, `z = s³`. -/
def q2t_swScaled (s u : ℝ) : ℂ :=
  exp (((π / 10 : ℝ) : ℂ) * I) *
    exp (-((u ^ 5 / s ^ 5 : ℝ) : ℂ) + I * ((u : ℂ) * exp (((π / 10 : ℝ) : ℂ) * I)) ^ 3)

lemma q2t_exp_pi_div_ten_pow_five : exp (((π / 10 : ℝ) : ℂ) * I) ^ 5 = I := by
  rw [← exp_nat_mul, show ((5 : ℕ) : ℂ) * (((π / 10 : ℝ) : ℂ) * I) = ((π / 2 : ℝ) : ℂ) * I by
    push_cast; ring, exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  simp

lemma q2t_swF_scale {s u : ℝ} (hs : 0 < s) (hu : 0 ≤ u) :
    q2t_swF (s ^ 3) (s⁻¹ * u) = q2t_swScaled s u := by
  rw [q2t_swF_nonneg _ (by positivity)]
  unfold q2t_swScaled
  set E : ℂ := exp (((π / 10 : ℝ) : ℂ) * I)
  have hs' : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have h5 : (((s⁻¹ * u : ℝ) : ℂ) * E) ^ 5 = ((u ^ 5 / s ^ 5 : ℝ) : ℂ) * I := by
    rw [mul_pow, q2t_exp_pi_div_ten_pow_five]; push_cast; field_simp
  have h3 : (((s ^ 3 : ℝ) : ℝ) : ℂ) * (((s⁻¹ * u : ℝ) : ℂ) * E) ^ 3 = ((u : ℂ) * E) ^ 3 := by
    push_cast; rw [mul_pow, mul_pow, mul_pow]; field_simp
  congr 2
  rw [mul_add, h5, h3]
  linear_combination ((u ^ 5 / s ^ 5 : ℝ) : ℂ) * I_sq

lemma q2t_norm_swScaled_le {s u : ℝ} (hs : 0 < s) (hu : 0 ≤ u) :
    ‖q2t_swScaled s u‖ ≤ (1 + 3 * u ^ 3) * Real.exp (-(Real.sqrt 2 / 2) * u ^ 3) := by
  have hpi := Real.pi_pos
  have h1 : π / 12 ≤ π / 10 := by linarith
  have h2 : π / 10 ≤ π / 4 := by linarith
  unfold q2t_swScaled
  rw [norm_mul, norm_exp_ofReal_mul_I, one_mul, norm_exp, add_re, neg_re, ofReal_re,
    q2t_cubicRay_re]
  have hsin := q2t_sin_three_ge h1 h2
  have hu3 := pow_nonneg hu 3
  have h5 : 0 ≤ u ^ 5 / s ^ 5 := by positivity
  calc Real.exp (-(u ^ 5 / s ^ 5) + -(u ^ 3 * Real.sin (3 * (π / 10))))
      ≤ Real.exp (-(Real.sqrt 2 / 2) * u ^ 3) := Real.exp_le_exp.mpr (by nlinarith)
    _ ≤ _ := le_mul_of_one_le_left (by positivity) (by linarith)

lemma q2t_tendsto_swScaled :
    Tendsto (fun s : ℝ => ∫ u in Ioi (0 : ℝ), q2t_swScaled s u) atTop
      (𝓝 (q2t_cubicG (π / 10))) := by
  unfold q2t_cubicG
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u => (1 + 3 * u ^ 3) * Real.exp (-(Real.sqrt 2 / 2) * u ^ 3))
    (Eventually.of_forall fun s => ?_) ?_ q2t_integrableOn_cubic_bound
    (ae_of_all _ fun u => ?_)
  · exact (by unfold q2t_swScaled; fun_prop : Continuous fun u => q2t_swScaled s u)
      |>.aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop 0] with s hs
    exact ae_restrict_of_forall_mem measurableSet_Ioi fun u hu =>
      q2t_norm_swScaled_le hs (le_of_lt hu)
  · have h0 : Tendsto (fun s : ℝ => u ^ 5 / s ^ 5) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
    have h1 := (tendsto_const_nhds (x := exp (((π / 10 : ℝ) : ℂ) * I))).mul
      (((continuous_ofReal.tendsto 0).comp h0).neg.add
        (tendsto_const_nhds (x := I * ((u : ℂ) * exp (((π / 10 : ℝ) : ℂ) * I)) ^ 3))).cexp
    simpa [q2t_swScaled, q2t_cubicRay, Function.comp_def] using h1

lemma q2t_re_cubicG : (q2t_cubicG (π / 10)).re = Real.Gamma (1 / 3) / (2 * Real.sqrt 3) := by
  have hpi := Real.pi_pos
  rw [← q2t_cubicG_eq (θ := π / 6) (by linarith) le_rfl, q2t_cubicG_pi_div_six,
    show (1 / 3 : ℝ) + 1 = 1 / 3 + 1 from rfl, Real.Gamma_add_one (by norm_num),
    exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_six]
  simp only [mul_re, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im, mul_im]
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : Real.sqrt 3 ≠ 0 := by positivity
  field_simp
  ring_nf
  rw [h3]; ring

end q2t

/-! ### Asymptotics along symmetry lines -/

/-- The Pearcey integral on the symmetry line `x = 0`, `y → +∞` (DLMF 36.11.3):
`Ψ₂(0, y) = √(π/y)(exp(iπ/4) + o(1))`. -/
@[dlmf 36.11.E3]
theorem cuspoidIntegral_two_zero_atTop :
    (fun y : ℝ => cuspoidIntegral 2 ![0, y] -
        (Real.sqrt (π / y) : ℂ) * exp (I * π / 4)) =o[atTop]
      (fun y : ℝ => Real.sqrt (π / y)) := by
  set L : ℂ := ∫ u : ℝ, exp (((π / 8 : ℝ) : ℂ) * I) *
    exp (I * exp (((π / 4 : ℝ) : ℂ) * I) * (u : ℂ) ^ 2) with hL
  have hT : Tendsto (fun y : ℝ => (∫ u : ℝ, q2t_pearceyScaled y u) - L) atTop (𝓝 0) := by
    have := q2t_tendsto_pearceyScaled.sub_const L
    rwa [← hL, sub_self] at this
  have h1 := (isLittleO_one_iff ℝ).mpr hT
  have hpi : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have h2 : (fun y : ℝ => ((1 / Real.sqrt y : ℝ) : ℂ)) =O[atTop]
      (fun y : ℝ => Real.sqrt (π / y)) := by
    refine IsBigO.of_bound (1 / Real.sqrt π) ?_
    filter_upwards [eventually_gt_atTop 0] with y hy
    rw [norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity), Real.sqrt_div' π hy.le]
    field_simp; rfl
  refine ((h1.mul_isBigO h2).congr' ?_ (Eventually.of_forall fun y => one_mul _))
  filter_upwards [eventually_gt_atTop 0] with y hy
  have hLv : L = (Real.sqrt π : ℂ) * exp (I * π / 4) := q2t_pearcey_limit
  rw [q2t_pearcey_scale hy, hLv, Real.sqrt_div' π hy.le]
  push_cast; ring

/-- The Pearcey integral on the symmetry line `x = 0`, `y → -∞` (DLMF 36.11.3):
`Ψ₂(0, y) = √(π/|y|) exp(-iπ/4)(1 + i√2 exp(-iy²/4) + o(1))`. -/
@[dlmf 36.11.E3]
theorem cuspoidIntegral_two_zero_atBot :
    (fun y : ℝ => cuspoidIntegral 2 ![0, y] -
        (Real.sqrt (π / |y|) : ℂ) * exp (-(I * π / 4)) *
          (1 + I * Real.sqrt 2 * exp (-(I * y ^ 2 / 4)))) =o[atBot]
      (fun y : ℝ => Real.sqrt (π / |y|)) := by
  sorry

/-- The swallowtail integral on the `x`-axis, `x → +∞` (DLMF 36.11.4):
`Ψ₃(x, 0, 0) = (√(2π)/(5|x|³)^{1/8}) exp(-2√2(x/5)^{5/4})(cos(2√2(x/5)^{5/4} - π/8) + o(1))`. -/
@[dlmf 36.11.E4]
theorem cuspoidIntegral_three_x_atTop :
    (fun x : ℝ => cuspoidIntegral 3 ![x, 0, 0] -
        ((Real.sqrt (2 * π) / (5 * |x| ^ 3) ^ (1 / 8 : ℝ) *
          Real.exp (-(2 * Real.sqrt 2 * (x / 5) ^ (5 / 4 : ℝ))) *
          Real.cos (2 * Real.sqrt 2 * (x / 5) ^ (5 / 4 : ℝ) - π / 8) : ℝ) : ℂ)) =o[atTop]
      (fun x : ℝ => Real.sqrt (2 * π) / (5 * |x| ^ 3) ^ (1 / 8 : ℝ) *
          Real.exp (-(2 * Real.sqrt 2 * (x / 5) ^ (5 / 4 : ℝ)))) := by
  sorry

/-- The swallowtail integral on the `x`-axis, `x → -∞` (DLMF 36.11.4):
`Ψ₃(x, 0, 0) = (√(2π)/(5|x|³)^{1/8})(cos(4(|x|/5)^{5/4} - π/4) + o(1))`. -/
@[dlmf 36.11.E4]
theorem cuspoidIntegral_three_x_atBot :
    (fun x : ℝ => cuspoidIntegral 3 ![x, 0, 0] -
        ((Real.sqrt (2 * π) / (5 * |x| ^ 3) ^ (1 / 8 : ℝ) *
          Real.cos (4 * (|x| / 5) ^ (5 / 4 : ℝ) - π / 4) : ℝ) : ℂ)) =o[atBot]
      (fun x : ℝ => Real.sqrt (2 * π) / (5 * |x| ^ 3) ^ (1 / 8 : ℝ)) := by
  sorry

/-- The symmetry `Ψ₃(0, y, 0) = conj Ψ₃(0, -y, 0)` of 36.11.5, a case of 36.2.23. -/
@[dlmf 36.11.E5]
theorem cuspoidIntegral_three_y_conj (y : ℝ) :
    cuspoidIntegral 3 ![0, y, 0] = conj (cuspoidIntegral 3 ![0, -y, 0]) := by
  rw [← cuspoidIntegral_odd_conj (by decide)]
  congr 1
  funext m
  fin_cases m <;> simp

/-- The swallowtail integral on the `y`-axis, `y → +∞` (DLMF 36.11.5):
`Ψ₃(0, y, 0) = exp(iπ/4)√(π/y)(1 - (i/√3) exp(3i(2y/5)^{5/3}/2) + o(1))`; for `y → -∞` use
`cuspoidIntegral_three_y_conj`. -/
@[dlmf 36.11.E5]
theorem cuspoidIntegral_three_y_atTop :
    (fun y : ℝ => cuspoidIntegral 3 ![0, y, 0] -
        exp (I * π / 4) * (Real.sqrt (π / y) : ℂ) *
          (1 - I / Real.sqrt 3 * exp (3 / 2 * I * ((2 * y / 5) ^ (5 / 3 : ℝ) : ℝ)))) =o[atTop]
      (fun y : ℝ => Real.sqrt (π / y)) := by
  sorry

/-- The swallowtail integral on the `z`-axis, `z → +∞` (DLMF 36.11.6):
`Ψ₃(0, 0, z) = Γ(1/3)/(|z|^{1/3}√3) + o(|z|^{-1/3})`. Stronger than DLMF, which gives the
remainder as `o(1)`. -/
@[dlmf 36.11.E6]
theorem cuspoidIntegral_three_z_atTop :
    (fun z : ℝ => cuspoidIntegral 3 ![0, 0, z] -
        ((Real.Gamma (1 / 3) / (|z| ^ (1 / 3 : ℝ) * Real.sqrt 3) : ℝ) : ℂ)) =o[atTop]
      (fun z : ℝ => |z| ^ (-(1 / 3 : ℝ))) := by
  rw [isLittleO_iff]
  intro c hc
  have hT := q2t_tendsto_swScaled.comp (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3))
  have hev := (Metric.tendsto_nhds.mp hT) (c / 2) (by positivity)
  filter_upwards [hev, eventually_gt_atTop 0] with z hz hz0
  simp only [Function.comp_apply, dist_eq_norm] at hz
  set s := z ^ (1 / 3 : ℝ) with hsdef
  have hs : 0 < s := Real.rpow_pos_of_pos hz0 _
  have hs3 : s ^ 3 = z := by
    rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul hz0.le]; norm_num
  set H := ∫ u in Set.Ioi (0 : ℝ), q2t_swScaled s u
  set G := q2t_cubicG (π / 10)
  have hI : ∫ r in Set.Ioi (0 : ℝ), q2t_swF z r = ((s⁻¹ : ℝ) : ℂ) * H := by
    have h := MeasureTheory.integral_comp_mul_left_Ioi' (q2t_swF z) 0 (inv_pos.mpr hs)
    rw [mul_zero] at h
    rw [← h, Complex.real_smul]
    congr 1
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) => ?_
    rw [← hs3]; exact q2t_swF_scale hs hu.le
  have habs : |z| = z := abs_of_pos hz0
  rw [q2t_swallow_split, hI, habs, ← hsdef, Real.rpow_neg hz0.le, ← hsdef, ← ofReal_sub,
    norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
  have hre : (((s⁻¹ : ℝ) : ℂ) * H).re = s⁻¹ * H.re := by
    rw [re_ofReal_mul]
  have hL : Real.Gamma (1 / 3) / (s * Real.sqrt 3) = 2 * (s⁻¹ * G.re) := by
    rw [q2t_re_cubicG]; field_simp
  rw [hre, hL, ← mul_sub, ← mul_sub, abs_mul, abs_two, abs_mul, abs_of_pos (inv_pos.mpr hs)]
  have hHG : |H.re - G.re| ≤ ‖H - G‖ := by
    rw [← sub_re]; exact abs_re_le_norm _
  have hz' : ‖H - G‖ < c / 2 := hz
  have hsi : 0 < s⁻¹ := inv_pos.mpr hs
  nlinarith

/-- The swallowtail integral on the `z`-axis, `z → -∞` (DLMF 36.11.6):
`Ψ₃(0, 0, z) = Γ(1/3)/(|z|^{1/3}√3) + (2√π 5^{1/4}/(3|z|)^{3/4})(cos((2/3)(3|z|/5)^{5/2} - π/4)
  + o(1))`. -/
@[dlmf 36.11.E6]
theorem cuspoidIntegral_three_z_atBot :
    (fun z : ℝ => cuspoidIntegral 3 ![0, 0, z] -
        ((Real.Gamma (1 / 3) / (|z| ^ (1 / 3 : ℝ) * Real.sqrt 3) +
          2 * Real.sqrt π * (5 : ℝ) ^ (1 / 4 : ℝ) / (3 * |z|) ^ (3 / 4 : ℝ) *
            Real.cos (2 / 3 * (3 * |z| / 5) ^ (5 / 2 : ℝ) - π / 4) : ℝ) : ℂ)) =o[atBot]
      (fun z : ℝ => 2 * Real.sqrt π * (5 : ℝ) ^ (1 / 4 : ℝ) / (3 * |z|) ^ (3 / 4 : ℝ)) := by
  sorry

/-- The elliptic umbilic integral on the `z`-axis, `z → +∞` (DLMF 36.11.7):
`Ψ^{(E)}(0, 0, z) = (π/z)(i + √3 exp(4iz³/27) + o(1))`. -/
@[dlmf 36.11.E7]
theorem ellipticUmbilicIntegral_z_atTop :
    (fun z : ℝ => ellipticUmbilicIntegral 0 0 z -
        π / z * (I + Real.sqrt 3 * exp (4 / 27 * I * z ^ 3))) =o[atTop]
      (fun z : ℝ => 1 / z) := by
  sorry

/-- The elliptic umbilic integral on the `z`-axis, `z → -∞`: corrected form of DLMF 36.11.7,
`Ψ^{(E)}(0, 0, z) = (π/z)(i - √3 exp(4iz³/27) + o(1))` (DLMF prints `+√3` for `z → ±∞`; see the
module docstring). Derived from the `z → +∞` case and the symmetry 36.2.24. -/
@[dlmf 36.11.E7]
theorem ellipticUmbilicIntegral_z_atBot :
    (fun z : ℝ => ellipticUmbilicIntegral 0 0 z -
        π / z * (I - Real.sqrt 3 * exp (4 / 27 * I * z ^ 3))) =o[atBot]
      (fun z : ℝ => 1 / z) := by
  have h := ellipticUmbilicIntegral_z_atTop.comp_tendsto tendsto_neg_atBot_atTop
  refine (h.norm_left.congr_left fun z => ?_).of_norm_left.trans_isBigO ?_
  · simp only [Function.comp_apply]
    rw [ellipticUmbilicIntegral_conj 0 0 z, ← norm_conj]
    congr 1
    simp only [map_sub, map_mul, map_add, map_div₀, conj_ofReal, conj_I, ← exp_conj, map_ofNat,
      map_pow]
    push_cast
    ring_nf
  · refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_)
    simp [Function.comp_apply, norm_neg]

/-- The hyperbolic umbilic integral on the `z`-axis, `z → +∞` (DLMF 36.11.8):
`Ψ^{(H)}(0, 0, z) = (2π/z)(1 - (i/√3) exp(iz³/27) + o(1))`. -/
@[dlmf 36.11.E8]
theorem hyperbolicUmbilicIntegral_z_atTop :
    (fun z : ℝ => hyperbolicUmbilicIntegral 0 0 z -
        2 * π / z * (1 - I / Real.sqrt 3 * exp (I * z ^ 3 / 27))) =o[atTop]
      (fun z : ℝ => 1 / z) := by
  sorry

/-- The hyperbolic umbilic integral on the `z`-axis, `z → -∞`: corrected form of DLMF 36.11.8,
`Ψ^{(H)}(0, 0, z) = (2π/z)(-1 - (i/√3) exp(iz³/27) + o(1))` (DLMF prints `1 - …` for `z → ±∞`; see
the module docstring). Derived from the `z → +∞` case and the symmetry 36.2.24. -/
@[dlmf 36.11.E8]
theorem hyperbolicUmbilicIntegral_z_atBot :
    (fun z : ℝ => hyperbolicUmbilicIntegral 0 0 z -
        2 * π / z * (-1 - I / Real.sqrt 3 * exp (I * z ^ 3 / 27))) =o[atBot]
      (fun z : ℝ => 1 / z) := by
  have h := hyperbolicUmbilicIntegral_z_atTop.comp_tendsto tendsto_neg_atBot_atTop
  refine (h.norm_left.congr_left fun z => ?_).of_norm_left.trans_isBigO ?_
  · simp only [Function.comp_apply]
    rw [hyperbolicUmbilicIntegral_conj 0 0 z, ← norm_conj]
    congr 1
    simp only [map_sub, map_mul, map_div₀, map_one, conj_ofReal, conj_I,
      ← exp_conj, map_ofNat, map_pow]
    push_cast
    ring_nf
  · refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_)
    simp [Function.comp_apply, norm_neg]

end DLMF.CoalescingSaddles
