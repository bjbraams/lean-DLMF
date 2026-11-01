/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.CoalescingSaddles.Basic.AuxiliaryData
public import DLMF.CoalescingSaddles.CanonicalIntegrals

/-!
# Leading-order asymptotics of the canonical integrals

This file proves the leading-order asymptotics of the canonical integrals of DLMF §36.11: the
stationary-phase approximation of the cuspoid integrals `Ψ_K(x)` far from the origin (DLMF
36.11.1–36.11.2) and the asymptotics along symmetry lines (DLMF 36.11.3–36.11.8), stated with
`Asymptotics.IsLittleO`.

## Main results

* `cuspoidIntegral_sub_stationaryPhaseSum_isLittleO`: the stationary-phase approximation along
  scaling rays away from the bifurcation set (DLMF 36.11.2).
* `cuspoidIntegral_two_zero_atTop`, `cuspoidIntegral_two_zero_atBot`: the Pearcey integral on
  the symmetry line `x = 0` (DLMF 36.11.3).
* `cuspoidIntegral_three_x_atTop`, `cuspoidIntegral_three_x_atBot`: the swallowtail integral on
  the `x`-axis (DLMF 36.11.4).
* `cuspoidIntegral_three_y_conj`, `cuspoidIntegral_three_y_atTop`: the swallowtail integral on
  the `y`-axis (DLMF 36.11.5).
* `cuspoidIntegral_three_z_atTop`, `cuspoidIntegral_three_z_atBot`: the swallowtail integral on
  the `z`-axis (DLMF 36.11.6).
* `ellipticUmbilicIntegral_z_atTop`, `ellipticUmbilicIntegral_z_atBot`: the elliptic umbilic
  integral on the `z`-axis (DLMF 36.11.7, corrected for `z → -∞`).
* `hyperbolicUmbilicIntegral_z_atTop`, `hyperbolicUmbilicIntegral_z_atBot`: the hyperbolic
  umbilic integral on the `z`-axis (DLMF 36.11.8, corrected for `z → -∞`).

## Implementation notes

DLMF does not say along which path `x → ∞` in 36.11.2; we state it along the scaling rays of
§36.6, `x(k) = (x₁k^{γ₁}, …, x_Kk^{γ_K})` (`cuspoidScaledCoords`) with `k → ∞`, for `x` off
the bifurcation set. On this ray `Ψ_K(x(k)) = k^{1/(K+2)} ∫ exp(ikΦ_K(τ; x)) dτ`, and 36.11.2 is
the stationary-phase theorem for the large parameter `k`. Each term of the sum is of exact order
`k^{1/(K+2) - 1/2}`, so DLMF's factors `1 + o(1)` amount to an `o` of that order.

**Corrections (36.11.7, 36.11.8).** DLMF states both formulas for `z → ±∞`. They hold for
`z → +∞` only. By 36.2.24, `Ψ^{(U)}(0, 0, -z) = conj Ψ^{(U)}(0, 0, z)`, and conjugating the printed
formulas gives, for `z → -∞`,
`Ψ^{(E)}(0, 0, z) = (π/z)(i - √3 exp(4iz³/27) + o(1))` and
`Ψ^{(H)}(0, 0, z) = (2π/z)(-1 - (i/√3) exp(iz³/27) + o(1))`,
that is `(π/|z|)(i sign z + √3 e^{4iz³/27})` and `(2π/|z|)(1 - i sign z e^{iz³/27}/√3)`. Direct
quadrature confirms this: `Ψ^{(E)}(0, 0, -6) = 0.75621 - 1.01820i` against the printed
`-0.75656 - 0.02351i` and the corrected `0.75656 - 1.02369i`; `Ψ^{(H)}(0, 0, -12) =
0.80126 + 0.11760i` against the printed `-0.24548 + 0.11846i` and the corrected
`0.80172 + 0.11846i`. The `z → -∞` statements are the corrected forms, derived from the
`z → +∞` statements and 36.2.24.

**36.11.6.** DLMF's `z → +∞` remainder `o(1)` is weaker than the size `|z|^{-1/3}` of the leading
term; we state the stronger `o(|z|^{-1/3})` (stronger than DLMF), which numerical quadrature
supports (relative error `3·10⁻⁵` at `z = 20` and `9·10⁻⁷` at `z = 60`).

36.11.3 for `y → +∞` (`cuspoidIntegral_two_zero_atTop`) is proved by the scaling `t = u/√y` and
dominated convergence to a complex Gaussian integral. 36.11.6 for `z → +∞`
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

section CanonicalIntegrals
open MeasureTheory Set

/-- The Pearcey integrand on the symmetry line after the scaling `t = u/√y`. -/
def pearceySymmetryLineScaled (y u : ℝ) : ℂ :=
  exp (((π / 8 : ℝ) : ℂ) * I) *
    exp (-((u ^ 4 / y ^ 2 : ℝ) : ℂ) + I * exp (((π / 4 : ℝ) : ℂ) * I) * (u : ℂ) ^ 2)

/-- The Pearcey contour angle is `π/8`. -/
private lemma cuspoidAngle_two : cuspoidAngle 2 = π / 8 := by
  unfold cuspoidAngle; norm_num

/-- On the symmetry line `x = 0` the Pearcey contour integrand is `e^{iπ/8} exp(-r⁴ + i e^{iπ/4} y
r²)`. -/
private lemma cuspoidIntegrand_two_symmetryLine (y r : ℝ) :
    cuspoidContourDir 2 r * exp (I * cuspoidPotential 2 (cuspoidContour 2 r) ![0, y]) =
      exp (((π / 8 : ℝ) : ℂ) * I) * exp (-((r ^ 4 : ℝ) : ℂ) +
        I * exp (((π / 4 : ℝ) : ℂ) * I) * ((y * r ^ 2 : ℝ) : ℂ)) := by
  have hd : cuspoidContourDir 2 r = exp (((π / 8 : ℝ) : ℂ) * I) := by
    rw [cuspoidContourDir_of_even (by decide), cuspoidAngle_two]
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

/-- For `y > 0`, the substitution `t = u/√y` gives `Ψ₂(0, y) = y^{-1/2} ∫ pearceySymmetryLineScaled y u du`.
-/
private lemma cuspoidIntegral_two_symmetryLine_eq_scaled {y : ℝ} (hy : 0 < y) :
    cuspoidIntegral 2 ![0, y] =
      ((1 / Real.sqrt y : ℝ) : ℂ) * ∫ u : ℝ, pearceySymmetryLineScaled y u := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hss : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
  set g : ℝ → ℂ := fun r => exp (((π / 8 : ℝ) : ℂ) * I) * exp (-((r ^ 4 : ℝ) : ℂ) +
    I * exp (((π / 4 : ℝ) : ℂ) * I) * ((y * r ^ 2 : ℝ) : ℂ)) with hg
  have h1 : cuspoidIntegral 2 ![0, y] = ∫ r, g r := by
    unfold cuspoidIntegral; simp only [cuspoidIntegrand_two_symmetryLine, hg]
  have h2 : (fun u : ℝ => pearceySymmetryLineScaled y u) = fun u => g (u / Real.sqrt y) := by
    funext u
    have h4 : Real.sqrt y ^ 4 = y ^ 2 := by
      calc Real.sqrt y ^ 4 = (Real.sqrt y ^ 2) ^ 2 := by ring
        _ = y ^ 2 := by rw [hss]
    have e1 : (u / Real.sqrt y) ^ 4 = u ^ 4 / y ^ 2 := by rw [div_pow, h4]
    have e2 : y * (u / Real.sqrt y) ^ 2 = u ^ 2 := by
      rw [div_pow, hss]; field_simp
    simp only [pearceySymmetryLineScaled, hg, e1, e2]
    push_cast; ring_nf
  rw [h1, h2, Measure.integral_comp_div, abs_of_pos hs, Complex.real_smul, ← mul_assoc,
    ← ofReal_mul, one_div_mul_cancel hs.ne', ofReal_one, one_mul]

/-- The scaled Pearcey integrand is bounded by the Gaussian `exp(-(√2/2) u²)`. -/
private lemma norm_pearceySymmetryLineScaled_le (y u : ℝ) :
    ‖pearceySymmetryLineScaled y u‖ ≤ Real.exp (-(Real.sqrt 2 / 2) * u ^ 2) := by
  rw [pearceySymmetryLineScaled, norm_mul, norm_exp_ofReal_mul_I, one_mul, norm_exp]
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

/-- As `y → ∞` the scaled Pearcey integral tends to the Gaussian integral `∫ e^{iπ/8} exp(i e^{iπ/4}
u²) du` (dominated convergence). -/
private lemma tendsto_integral_pearceySymmetryLineScaled :
    Tendsto (fun y : ℝ => ∫ u : ℝ, pearceySymmetryLineScaled y u) atTop
      (𝓝 (∫ u : ℝ, exp (((π / 8 : ℝ) : ℂ) * I) *
        exp (I * exp (((π / 4 : ℝ) : ℂ) * I) * (u : ℂ) ^ 2))) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u => Real.exp (-(Real.sqrt 2 / 2) * u ^ 2)) (Eventually.of_forall fun y => ?_)
    (Eventually.of_forall fun y => ae_of_all _ fun u => norm_pearceySymmetryLineScaled_le y u)
    (integrable_exp_neg_mul_sq (by positivity)) (ae_of_all _ fun u => ?_)
  · unfold pearceySymmetryLineScaled; fun_prop
  · have h0 : Tendsto (fun y : ℝ => u ^ 4 / y ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
    have h1 : Tendsto (fun y : ℝ => pearceySymmetryLineScaled y u) atTop
        (𝓝 (exp (((π / 8 : ℝ) : ℂ) * I) * exp (-((0 : ℝ) : ℂ) +
          I * exp (((π / 4 : ℝ) : ℂ) * I) * (u : ℂ) ^ 2))) := by
      unfold pearceySymmetryLineScaled
      exact tendsto_const_nhds.mul (((continuous_ofReal.tendsto 0).comp h0).neg.add
        tendsto_const_nhds).cexp
    simpa using h1

/-- The Fresnel-type limit: `∫ e^{iπ/8} exp(i e^{iπ/4} u²) du = √π e^{iπ/4}`. -/
private lemma integral_pearceyGaussianLimit :
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
def cubicRayIntegrand (θ r : ℝ) : ℂ :=
  exp ((θ : ℂ) * I) * exp (I * ((r : ℂ) * exp ((θ : ℂ) * I)) ^ 3)

/-- Its `θ`-derivative `i e^{iθ} exp(i (r e^{iθ})³) (1 + 3i (r e^{iθ})³)`. -/
def cubicRayIntegrandDeriv (θ r : ℝ) : ℂ :=
  I * exp ((θ : ℂ) * I) * exp (I * ((r : ℂ) * exp ((θ : ℂ) * I)) ^ 3) *
    (1 + 3 * I * ((r : ℂ) * exp ((θ : ℂ) * I)) ^ 3)

/-- The cubic ray integrand has `θ`-derivative `cubicRayIntegrandDeriv θ r`. -/
private lemma hasDerivAt_cubicRayIntegrand (θ r : ℝ) :
    HasDerivAt (fun θ => cubicRayIntegrand θ r) (cubicRayIntegrandDeriv θ r) θ := by
  have hE : HasDerivAt (fun θ : ℝ => exp ((θ : ℂ) * I)) (exp ((θ : ℂ) * I) * I) θ := by
    have := ((hasDerivAt_id (θ : ℂ)).mul_const I).cexp.comp_ofReal
    simpa using this
  have h2 := ((((hE.const_mul (r : ℂ)).pow 3).const_mul I).cexp)
  have h := hE.mul h2
  unfold cubicRayIntegrand cubicRayIntegrandDeriv
  convert h using 1
  simp only [Pi.pow_apply]; push_cast; ring

/-- `Re (i (r e^{iθ})³) = -r³ sin 3θ`. -/
private lemma re_I_mul_ofReal_mul_exp_cube (θ r : ℝ) :
    (I * ((r : ℂ) * exp ((θ : ℂ) * I)) ^ 3).re = -(r ^ 3 * Real.sin (3 * θ)) := by
  have : ((r : ℂ) * exp ((θ : ℂ) * I)) ^ 3 = ((r ^ 3 : ℝ) : ℂ) * exp (((3 * θ : ℝ) : ℂ) * I) := by
    rw [mul_pow, ← exp_nat_mul]; push_cast; ring_nf
  rw [this, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  simp only [mul_re, mul_im, add_re, add_im, I_re, I_im, ofReal_re, ofReal_im]
  ring

/-- For `π/12 ≤ θ ≤ π/4`, `sin 3θ ≥ √2/2`. -/
private lemma sqrt_two_div_two_le_sin_three_mul {θ : ℝ} (h1 : π / 12 ≤ θ) (h2 : θ ≤ π / 4) :
    Real.sqrt 2 / 2 ≤ Real.sin (3 * θ) := by
  rw [← Real.cos_pi_div_four, ← Real.cos_sub_pi_div_two, ← Real.cos_abs (3 * θ - π / 2)]
  apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos])
  rw [abs_le]; constructor <;> linarith

/-- For `π/12 ≤ θ ≤ π/4` and `r ≥ 0`, `‖exp(i (r e^{iθ})³)‖ ≤ exp(-(√2/2) r³)`. -/
private lemma norm_exp_I_mul_cube_le {θ r : ℝ} (h1 : π / 12 ≤ θ) (h2 : θ ≤ π / 4) (hr : 0 ≤ r) :
    ‖exp (I * ((r : ℂ) * exp ((θ : ℂ) * I)) ^ 3)‖ ≤ Real.exp (-(Real.sqrt 2 / 2) * r ^ 3) := by
  rw [norm_exp, re_I_mul_ofReal_mul_exp_cube]
  refine Real.exp_le_exp.mpr ?_
  have := sqrt_two_div_two_le_sin_three_mul h1 h2
  have := pow_nonneg hr 3
  nlinarith

/-- `‖(r e^{iθ})³‖ = r³` for `r ≥ 0`. -/
private lemma norm_ofReal_mul_exp_cube (θ r : ℝ) (hr : 0 ≤ r) : ‖((r : ℂ) * exp ((θ : ℂ) * I)) ^ 3‖ = r ^ 3 := by
  rw [norm_pow, norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr]

/-- Uniform bound `(1 + 3r³) exp(-(√2/2) r³)` on the `θ`-derivative of the cubic ray integrand for
`π/12 ≤ θ ≤ π/4`. -/
private lemma norm_cubicRayIntegrandDeriv_le {θ r : ℝ} (h1 : π / 12 ≤ θ) (h2 : θ ≤ π / 4) (hr : 0 ≤ r) :
    ‖cubicRayIntegrandDeriv θ r‖ ≤ (1 + 3 * r ^ 3) * Real.exp (-(Real.sqrt 2 / 2) * r ^ 3) := by
  unfold cubicRayIntegrandDeriv
  rw [norm_mul, norm_mul, norm_mul, norm_I, norm_exp_ofReal_mul_I, one_mul, one_mul, mul_comm]
  refine mul_le_mul ?_ (norm_exp_I_mul_cube_le h1 h2 hr) (norm_nonneg _) (by positivity)
  refine (norm_add_le _ _).trans ?_
  rw [norm_one, norm_mul, norm_mul, norm_I, norm_ofReal_mul_exp_cube θ r hr]; simp

/-- The dominating function `(1 + 3r³) exp(-(√2/2) r³)` is integrable on `(0, ∞)`. -/
private lemma integrableOn_cubic_dominating :
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
private lemma integral_cubicRayIntegrandDeriv_eq_zero {θ : ℝ} (h1 : π / 12 ≤ θ) (h2 : θ ≤ π / 4) :
    ∫ r in Ioi (0 : ℝ), cubicRayIntegrandDeriv θ r = 0 := by
  set E : ℂ := exp ((θ : ℂ) * I)
  set k : ℝ → ℂ := fun r => (r : ℂ) * E * exp (I * ((r : ℂ) * E) ^ 3) with hk
  have hd : ∀ r : ℝ, HasDerivAt k ((-I) * cubicRayIntegrandDeriv θ r) r := by
    intro r
    have h := (((hasDerivAt_id (r : ℂ)).mul_const E).mul
      ((((hasDerivAt_id (r : ℂ)).mul_const E).pow 3).const_mul I).cexp).comp_ofReal
    convert h using 1
    · funext y; simp [hk]
    unfold cubicRayIntegrandDeriv
    simp only [id]
    push_cast
    linear_combination (-(E * exp (I * ((r : ℂ) * E) ^ 3)) *
      (1 + 3 * I * ((r : ℂ) * E) ^ 3)) * I_sq
  have hint : IntegrableOn (fun r => (-I) * cubicRayIntegrandDeriv θ r) (Ioi 0) := by
    refine (integrableOn_cubic_dominating.mono' ?_ ?_).const_mul (-I)
    · exact (by unfold cubicRayIntegrandDeriv; fun_prop : Continuous fun r => cubicRayIntegrandDeriv θ r)
        |>.aestronglyMeasurable
    · exact ae_restrict_of_forall_mem measurableSet_Ioi fun r hr =>
        norm_cubicRayIntegrandDeriv_le h1 h2 (le_of_lt hr)
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
    have hb := norm_exp_I_mul_cube_le h1 h2 (by linarith : (0 : ℝ) ≤ r)
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

/-- Uniform bound `(1 + 3r³) exp(-(√2/2) r³)` on the cubic ray integrand for `π/12 ≤ θ ≤ π/4`. -/
private lemma norm_cubicRayIntegrand_le {θ r : ℝ} (h1 : π / 12 ≤ θ) (h2 : θ ≤ π / 4) (hr : 0 ≤ r) :
    ‖cubicRayIntegrand θ r‖ ≤ (1 + 3 * r ^ 3) * Real.exp (-(Real.sqrt 2 / 2) * r ^ 3) := by
  unfold cubicRayIntegrand
  rw [norm_mul, norm_exp_ofReal_mul_I, one_mul]
  refine (norm_exp_I_mul_cube_le h1 h2 hr).trans ?_
  have := pow_nonneg hr 3
  exact le_mul_of_one_le_left (by positivity) (by linarith)

/-- The cubic ray integral `G(θ) = ∫_0^∞ e^{iθ} exp(i(re^{iθ})³) dr`. -/
def cubicRayIntegral (θ : ℝ) : ℂ := ∫ r in Ioi (0 : ℝ), cubicRayIntegrand θ r

/-- The cubic ray integral `G(θ)` has derivative `0` for `π/10 ≤ θ ≤ π/6` (Cauchy's theorem in
differential form). -/
private lemma hasDerivAt_cubicRayIntegral_zero {θ₀ : ℝ} (h1 : π / 10 ≤ θ₀) (h2 : θ₀ ≤ π / 6) :
    HasDerivAt cubicRayIntegral 0 θ₀ := by
  have hpi := Real.pi_pos
  have hball : ∀ θ ∈ Metric.ball θ₀ (π / 60), π / 12 ≤ θ ∧ θ ≤ π / 4 := by
    intro θ hθ
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hθ
    constructor <;> linarith [hθ.1, hθ.2]
  have hcont : ∀ θ, Continuous fun r => cubicRayIntegrand θ r := fun θ => by
    unfold cubicRayIntegrand; fun_prop
  have hcont' : ∀ θ, Continuous fun r => cubicRayIntegrandDeriv θ r := fun θ => by
    unfold cubicRayIntegrandDeriv; fun_prop
  have h0 := hball θ₀ (Metric.mem_ball_self (by positivity))
  have hint : Integrable (fun r => cubicRayIntegrand θ₀ r) (volume.restrict (Ioi 0)) :=
    integrableOn_cubic_dominating.mono' (hcont θ₀).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr =>
        norm_cubicRayIntegrand_le h0.1 h0.2 (le_of_lt hr))
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun θ r => cubicRayIntegrand θ r) (F' := fun θ r => cubicRayIntegrandDeriv θ r) (x₀ := θ₀)
    (bound := fun r => (1 + 3 * r ^ 3) * Real.exp (-(Real.sqrt 2 / 2) * r ^ 3))
    (s := Metric.ball θ₀ (π / 60)) (Metric.ball_mem_nhds _ (by positivity))
    (Eventually.of_forall fun θ => (hcont θ).aestronglyMeasurable) hint
    (hcont' θ₀).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr θ hθ =>
      norm_cubicRayIntegrandDeriv_le (hball θ hθ).1 (hball θ hθ).2 (le_of_lt hr))
    integrableOn_cubic_dominating
    (ae_of_all _ fun r θ _ => hasDerivAt_cubicRayIntegrand θ r)
  have h2' := h.2
  rw [integral_cubicRayIntegrandDeriv_eq_zero h0.1 h0.2] at h2'
  exact h2'

/-- The cubic ray integral `G(θ)` is constant on `[π/10, π/6]`. -/
private lemma cubicRayIntegral_eq_pi_div_ten {θ : ℝ} (h1 : π / 10 ≤ θ) (h2 : θ ≤ π / 6) :
    cubicRayIntegral θ = cubicRayIntegral (π / 10) := by
  have hle : π / 10 ≤ π / 6 := by linarith [Real.pi_pos]
  refine constant_of_has_deriv_right_zero (f := cubicRayIntegral) (a := π / 10) (b := π / 6)
    (fun x hx => (hasDerivAt_cubicRayIntegral_zero hx.1 hx.2).continuousAt.continuousWithinAt)
    (fun x hx => (hasDerivAt_cubicRayIntegral_zero hx.1 hx.2.le).hasDerivWithinAt) θ ⟨h1, h2⟩

/-- On the ray `θ = π/6`, `G(π/6) = e^{iπ/6} Γ(4/3)`. -/
private lemma cubicRayIntegral_pi_div_six :
    cubicRayIntegral (π / 6) = exp (((π / 6 : ℝ) : ℂ) * I) * (Real.Gamma (1 / 3 + 1) : ℂ) := by
  have hE : exp (((π / 6 : ℝ) : ℂ) * I) ^ 3 = I := by
    rw [← exp_nat_mul, show ((3 : ℕ) : ℂ) * (((π / 6 : ℝ) : ℂ) * I) = ((π / 2 : ℝ) : ℂ) * I by
      push_cast; ring, exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    simp
  have hpt : ∀ r : ℝ, cubicRayIntegrand (π / 6) r =
      exp (((π / 6 : ℝ) : ℂ) * I) * ((Real.exp (-r ^ 3) : ℝ) : ℂ) := by
    intro r
    unfold cubicRayIntegrand
    rw [mul_pow, hE, ofReal_exp]
    congr 2
    push_cast
    linear_combination (r : ℂ) ^ 3 * I_sq
  unfold cubicRayIntegral
  simp_rw [hpt]
  rw [integral_const_mul, integral_complex_ofReal, integral_Ioi_exp_neg_pow 3 (by norm_num)]
  push_cast; ring_nf

/-- The swallowtail contour angle is `π/10`. -/
private lemma cuspoidAngle_three : cuspoidAngle 3 = π / 10 := by
  unfold cuspoidAngle; norm_num

/-- The swallowtail potential on the `z`-axis is `t⁵ + z t³`. -/
private lemma cuspoidPotential_three_zAxis (z : ℝ) (t : ℂ) :
    cuspoidPotential 3 t ![0, 0, z] = t ^ 5 + (z : ℂ) * t ^ 3 := by
  simp [cuspoidPotential, Fin.sum_univ_three]

/-- The swallowtail integrand on the `z`-axis. -/
def swallowtailZAxisIntegrand (z r : ℝ) : ℂ :=
  cuspoidContourDir 3 r * exp (I * cuspoidPotential 3 (cuspoidContour 3 r) ![0, 0, z])

/-- For `r ≥ 0` the swallowtail integrand on the `z`-axis is `e^{iπ/10} exp(i((r e^{iπ/10})⁵ + z (r
e^{iπ/10})³))`. -/
private lemma swallowtailZAxisIntegrand_of_nonneg (z : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    swallowtailZAxisIntegrand z r = exp (((π / 10 : ℝ) : ℂ) * I) * exp (I * (((r : ℂ) *
      exp (((π / 10 : ℝ) : ℂ) * I)) ^ 5 + (z : ℂ) *
        ((r : ℂ) * exp (((π / 10 : ℝ) : ℂ) * I)) ^ 3)) := by
  unfold swallowtailZAxisIntegrand cuspoidContour
  rw [cuspoidContourDir_of_nonneg 3 hr, cuspoidAngle_three, cuspoidPotential_three_zAxis]

/-- On the negative half line the swallowtail integrand is the complex conjugate of its mirror
value. -/
private lemma swallowtailZAxisIntegrand_neg (z : ℝ) {s : ℝ} (hs : 0 < s) :
    swallowtailZAxisIntegrand z (-s) = (starRingEnd ℂ) (swallowtailZAxisIntegrand z s) := by
  have hn : ¬ Even 3 := by decide
  unfold swallowtailZAxisIntegrand cuspoidContour
  rw [cuspoidContourDir_of_odd_of_neg hn (by linarith : -s < 0), cuspoidContourDir_of_nonneg 3 hs.le,
    cuspoidAngle_three, cuspoidPotential_three_zAxis, cuspoidPotential_three_zAxis, map_mul, ← exp_conj, ← exp_conj]
  congr 2
  · simp only [map_mul, conj_I, conj_ofReal]; ring
  · simp only [map_mul, map_add, map_pow, conj_I, conj_ofReal, ← exp_conj]
    push_cast
    ring_nf

/-- On the `z`-axis, `Ψ₃(0, 0, z) = 2 Re ∫_0^∞ swallowtailZAxisIntegrand z r dr`. -/
private lemma cuspoidIntegral_three_zAxis_eq_two_re (z : ℝ) :
    cuspoidIntegral 3 ![0, 0, z] =
      (((2 * (∫ r in Ioi (0 : ℝ), swallowtailZAxisIntegrand z r).re : ℝ)) : ℂ) := by
  have hint : Integrable (swallowtailZAxisIntegrand z) := integrable_cuspoidIntegral_integrand 3 ![0, 0, z]
  have h := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hint
  rw [compl_Ioi] at h
  have hc : ∫ r in Iic (0 : ℝ), swallowtailZAxisIntegrand z r =
      (starRingEnd ℂ) (∫ r in Ioi (0 : ℝ), swallowtailZAxisIntegrand z r) := by
    rw [← integral_conj, show Iic (0 : ℝ) = Iic (-0) by simp,
      ← integral_comp_neg_Ioi (0 : ℝ) (swallowtailZAxisIntegrand z)]
    exact setIntegral_congr_fun measurableSet_Ioi fun r (hr : r ∈ Ioi 0) =>
      swallowtailZAxisIntegrand_neg z (mem_Ioi.mp hr)
  have : cuspoidIntegral 3 ![0, 0, z] = ∫ r, swallowtailZAxisIntegrand z r := rfl
  rw [this, ← h, hc, add_conj]

/-- The swallowtail integrand after the scaling `r = u/s`, `z = s³`. -/
def swallowtailZAxisScaled (s u : ℝ) : ℂ :=
  exp (((π / 10 : ℝ) : ℂ) * I) *
    exp (-((u ^ 5 / s ^ 5 : ℝ) : ℂ) + I * ((u : ℂ) * exp (((π / 10 : ℝ) : ℂ) * I)) ^ 3)

/-- `(e^{iπ/10})⁵ = i`. -/
private lemma exp_pi_div_ten_mul_I_pow_five : exp (((π / 10 : ℝ) : ℂ) * I) ^ 5 = I := by
  rw [← exp_nat_mul, show ((5 : ℕ) : ℂ) * (((π / 10 : ℝ) : ℂ) * I) = ((π / 2 : ℝ) : ℂ) * I by
    push_cast; ring, exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  simp

/-- Under `r = u/s` and `z = s³` the swallowtail integrand becomes the scaled integrand
`swallowtailZAxisScaled s u`. -/
private lemma swallowtailZAxisIntegrand_scale {s u : ℝ} (hs : 0 < s) (hu : 0 ≤ u) :
    swallowtailZAxisIntegrand (s ^ 3) (s⁻¹ * u) = swallowtailZAxisScaled s u := by
  rw [swallowtailZAxisIntegrand_of_nonneg _ (by positivity)]
  unfold swallowtailZAxisScaled
  set E : ℂ := exp (((π / 10 : ℝ) : ℂ) * I)
  have hs' : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have h5 : (((s⁻¹ * u : ℝ) : ℂ) * E) ^ 5 = ((u ^ 5 / s ^ 5 : ℝ) : ℂ) * I := by
    rw [mul_pow, exp_pi_div_ten_mul_I_pow_five]; push_cast; field_simp
  have h3 : (((s ^ 3 : ℝ) : ℝ) : ℂ) * (((s⁻¹ * u : ℝ) : ℂ) * E) ^ 3 = ((u : ℂ) * E) ^ 3 := by
    push_cast; rw [mul_pow, mul_pow, mul_pow]; field_simp
  congr 2
  rw [mul_add, h5, h3]
  linear_combination ((u ^ 5 / s ^ 5 : ℝ) : ℂ) * I_sq

/-- The scaled swallowtail integrand is bounded by `(1 + 3u³) exp(-(√2/2) u³)` for `u ≥ 0`. -/
private lemma norm_swallowtailZAxisScaled_le {s u : ℝ} (hs : 0 < s) (hu : 0 ≤ u) :
    ‖swallowtailZAxisScaled s u‖ ≤ (1 + 3 * u ^ 3) * Real.exp (-(Real.sqrt 2 / 2) * u ^ 3) := by
  have hpi := Real.pi_pos
  have h1 : π / 12 ≤ π / 10 := by linarith
  have h2 : π / 10 ≤ π / 4 := by linarith
  unfold swallowtailZAxisScaled
  rw [norm_mul, norm_exp_ofReal_mul_I, one_mul, norm_exp, add_re, neg_re, ofReal_re,
    re_I_mul_ofReal_mul_exp_cube]
  have hsin := sqrt_two_div_two_le_sin_three_mul h1 h2
  have hu3 := pow_nonneg hu 3
  have h5 : 0 ≤ u ^ 5 / s ^ 5 := by positivity
  calc Real.exp (-(u ^ 5 / s ^ 5) + -(u ^ 3 * Real.sin (3 * (π / 10))))
      ≤ Real.exp (-(Real.sqrt 2 / 2) * u ^ 3) := Real.exp_le_exp.mpr (by nlinarith)
    _ ≤ _ := le_mul_of_one_le_left (by positivity) (by linarith)

/-- As `s → ∞` the scaled swallowtail integral tends to the cubic ray integral `G(π/10)`. -/
private lemma tendsto_integral_swallowtailZAxisScaled :
    Tendsto (fun s : ℝ => ∫ u in Ioi (0 : ℝ), swallowtailZAxisScaled s u) atTop
      (𝓝 (cubicRayIntegral (π / 10))) := by
  unfold cubicRayIntegral
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u => (1 + 3 * u ^ 3) * Real.exp (-(Real.sqrt 2 / 2) * u ^ 3))
    (Eventually.of_forall fun s => ?_) ?_ integrableOn_cubic_dominating
    (ae_of_all _ fun u => ?_)
  · exact (by unfold swallowtailZAxisScaled; fun_prop : Continuous fun u => swallowtailZAxisScaled s u)
      |>.aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop 0] with s hs
    exact ae_restrict_of_forall_mem measurableSet_Ioi fun u hu =>
      norm_swallowtailZAxisScaled_le hs (le_of_lt hu)
  · have h0 : Tendsto (fun s : ℝ => u ^ 5 / s ^ 5) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
    have h1 := (tendsto_const_nhds (x := exp (((π / 10 : ℝ) : ℂ) * I))).mul
      (((continuous_ofReal.tendsto 0).comp h0).neg.add
        (tendsto_const_nhds (x := I * ((u : ℂ) * exp (((π / 10 : ℝ) : ℂ) * I)) ^ 3))).cexp
    simpa [swallowtailZAxisScaled, cubicRayIntegrand, Function.comp_def] using h1

/-- `Re G(π/10) = Γ(1/3)/(2√3)`. -/
private lemma re_cubicRayIntegral_pi_div_ten : (cubicRayIntegral (π / 10)).re = Real.Gamma (1 / 3) / (2 * Real.sqrt 3) := by
  have hpi := Real.pi_pos
  rw [← cubicRayIntegral_eq_pi_div_ten (θ := π / 6) (by linarith) le_rfl, cubicRayIntegral_pi_div_six,
    show (1 / 3 : ℝ) + 1 = 1 / 3 + 1 from rfl, Real.Gamma_add_one (by norm_num),
    exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_six]
  simp only [mul_re, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im, mul_im]
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : Real.sqrt 3 ≠ 0 := by positivity
  field_simp
  ring_nf
  rw [h3]; ring

end CanonicalIntegrals
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
  have hT : Tendsto (fun y : ℝ => (∫ u : ℝ, pearceySymmetryLineScaled y u) - L) atTop (𝓝 0) := by
    have := tendsto_integral_pearceySymmetryLineScaled.sub_const L
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
  have hLv : L = (Real.sqrt π : ℂ) * exp (I * π / 4) := integral_pearceyGaussianLimit
  rw [cuspoidIntegral_two_symmetryLine_eq_scaled hy, hLv, Real.sqrt_div' π hy.le]
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
  have hT := tendsto_integral_swallowtailZAxisScaled.comp (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3))
  have hev := (Metric.tendsto_nhds.mp hT) (c / 2) (by positivity)
  filter_upwards [hev, eventually_gt_atTop 0] with z hz hz0
  simp only [Function.comp_apply, dist_eq_norm] at hz
  set s := z ^ (1 / 3 : ℝ) with hsdef
  have hs : 0 < s := Real.rpow_pos_of_pos hz0 _
  have hs3 : s ^ 3 = z := by
    rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul hz0.le]; norm_num
  set H := ∫ u in Set.Ioi (0 : ℝ), swallowtailZAxisScaled s u
  set G := cubicRayIntegral (π / 10)
  have hI : ∫ r in Set.Ioi (0 : ℝ), swallowtailZAxisIntegrand z r = ((s⁻¹ : ℝ) : ℂ) * H := by
    have h := MeasureTheory.integral_comp_mul_left_Ioi' (swallowtailZAxisIntegrand z) 0 (inv_pos.mpr hs)
    rw [mul_zero] at h
    rw [← h, Complex.real_smul]
    congr 1
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) => ?_
    rw [← hs3]; exact swallowtailZAxisIntegrand_scale hs hu.le
  have habs : |z| = z := abs_of_pos hz0
  rw [cuspoidIntegral_three_zAxis_eq_two_re, hI, habs, ← hsdef, Real.rpow_neg hz0.le, ← hsdef, ← ofReal_sub,
    norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
  have hre : (((s⁻¹ : ℝ) : ℂ) * H).re = s⁻¹ * H.re := by
    rw [re_ofReal_mul]
  have hL : Real.Gamma (1 / 3) / (s * Real.sqrt 3) = 2 * (s⁻¹ * G.re) := by
    rw [re_cubicRayIntegral_pi_div_ten]; field_simp
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
