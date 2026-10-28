/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecialFunctions.Bessel

/-!
# Bessel functions of the first and second kinds (AAR §§4.5–4.6)

The series

$$
J_ν(z)=\Bigl(\frac{z}{2}\Bigr)^ν\sum_{k=0}^∞\frac{(-1)^k}{k!\,Γ(ν+k+1)}\Bigl(\frac{z}{2}\Bigr)^{2k}
$$

is Mathlib's regularized `₀F₁(;ν+1;-z²/4)` multiplied by `(z/2)^ν`; it is Mathlib's
`Complex.besselJ`, used here directly, with `besselJ_eq_regularized` giving the series form. The
second-kind function `Y_ν` is the usual linear combination of `J_ν` and `J_{-ν}`.
-/

@[expose] public section

open Complex
open scoped Real Nat Topology
open DLMF.Confluent

noncomputable section

namespace DLMF.Bessel

/-- Mathlib's Bessel function of the first kind `Complex.besselJ` as the regularized series
`J_ν(z) = (z/2)^ν ₀F̃₁(;ν+1;-z²/4)`, the normal form used in this project. -/
@[dlmf 10.2.E2]
theorem besselJ_eq_regularized (ν z : ℂ) :
    besselJ ν z = (z / 2) ^ ν * regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-(z ^ 2 / 4)) := by
  rw [besselJ, Multiset.empty_eq_zero, div_pow]
  norm_num

/-- Bessel function of the second kind (Weber's `Y_ν`), with integer orders
defined by their limits in the order parameter (AAR §4.6). -/
@[dlmf 10.2.E3]
def besselY (ν z : ℂ) : ℂ := by
  classical
  exact if ∃ k : ℤ, ν = k then
    Filter.limUnder (𝓝[≠] ν) (fun μ =>
      (besselJ μ z * cos (μ * π) - besselJ (-μ) z) / sin (μ * π))
  else (besselJ ν z * cos (ν * π) - besselJ (-ν) z) / sin (ν * π)

/-- Identity under the stated parameter and domain assumptions: `regularizedHGFunCoeff (∅ :
Multiset ℂ) {c} n = 1 / (n ! * Gamma (c + n))`. -/
theorem regularizedHGFunCoeff_empty (c : ℂ) (n : ℕ) :
    regularizedHGFunCoeff (∅ : Multiset ℂ) {c} n = 1 / (n ! * Gamma (c + n)) := by
  simp [regularizedHGFunCoeff]

/-- The regularized `₀F₁` series is entire, including nonpositive integer parameters. -/
theorem hasFPowerSeriesOnBall_regularized0F1 (c : ℂ) :
    HasFPowerSeriesOnBall (regularizedHGFun (∅ : Multiset ℂ) {c})
      (FormalMultilinearSeries.ofScalars ℂ (regularizedHGFunCoeff ∅ {c})) 0 ⊤ := by
  have hr : (regularizedHGFunSeries ∅ {c}).radius = ⊤ :=
    radius_regularizedHGFunSeries_eq_top (by simp)
  change HasFPowerSeriesOnBall (regularizedHGFunSeries ∅ {c}).sum
    (regularizedHGFunSeries ∅ {c}) 0 ⊤
  simpa only [hr] using (regularizedHGFunSeries ∅ {c}).hasFPowerSeriesOnBall
    (by rw [hr]; simp)

/-- The function `(regularizedHGFun (∅ : Multiset ℂ) {c})` is analytic over `ℂ` at `z`. -/
theorem analyticAt_regularized0F1 (c z : ℂ) :
    AnalyticAt ℂ (regularizedHGFun (∅ : Multiset ℂ) {c}) z :=
  (hasFPowerSeriesOnBall_regularized0F1 c).analyticAt_of_mem (by simp)

/-- The reciprocal Gamma recurrence avoids restrictions on the parameter. -/
theorem regularized0F1_coeff_recurrence (c : ℂ) (n : ℕ) :
    (n + 1 : ℂ) * (c + n) * regularizedHGFunCoeff ∅ {c} (n + 1) =
      regularizedHGFunCoeff ∅ {c} n := by
  simp only [regularizedHGFunCoeff_empty, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, one_div, mul_inv_rev]
  rw [show c + (n + 1) = (c + n) + 1 by ring,
    one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (c + n)]
  field [Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)]

/-- The differential equation for regularized `₀F₁`. -/
theorem regularized0F1_ode (c w : ℂ) :
    w * deriv (deriv (regularizedHGFun (∅ : Multiset ℂ) {c})) w +
      c * deriv (regularizedHGFun ∅ {c}) w - regularizedHGFun ∅ {c} w = 0 := by
  have he := (hasFPowerSeriesOnBall_regularized0F1 c).ode_of_recurrence
    (A := 0) (B := 0) (C := 1) (D := c)
    (fun n => by simpa using regularized0F1_coeff_recurrence c n) (z := w) (by simp)
  simpa using he

/-- Differentiating regularized `₀F₁` raises its parameter by one. -/
theorem deriv_regularized0F1 (c w : ℂ) :
    deriv (regularizedHGFun (∅ : Multiset ℂ) {c}) w = regularizedHGFun ∅ {c + 1} w := by
  have hd := (hasFPowerSeriesOnBall_regularized0F1 c).deriv_ofScalars.hasSum_mul_pow
    (z := w) (by simp)
  have he (n : ℕ) : (n + 1 : ℂ) * regularizedHGFunCoeff ∅ {c} (n + 1) =
      regularizedHGFunCoeff ∅ {c + 1} n := by
    simp only [regularizedHGFunCoeff_empty, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one, one_div, mul_inv_rev]
    rw [show c + (n + 1) = c + 1 + n by ring]
    field [Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)]
  simp_rw [he] at hd
  exact hd.unique ((hasFPowerSeriesOnBall_regularized0F1 (c + 1)).hasSum_mul_pow (by simp))

/-- At `w`, the function `(regularizedHGFun (∅ : Multiset ℂ) {c})` has derivative
`(regularizedHGFun ∅ {c + 1} w)`. -/
theorem hasDerivAt_regularized0F1 (c w : ℂ) :
    HasDerivAt (regularizedHGFun (∅ : Multiset ℂ) {c}) (regularizedHGFun ∅ {c + 1} w) w := by
  rw [← deriv_regularized0F1]
  exact (analyticAt_regularized0F1 c w).differentiableAt.hasDerivAt

/-- A contiguous relation valid even at the exceptional integer parameters. -/
theorem regularized0F1_contiguous (c w : ℂ) :
    regularizedHGFun (∅ : Multiset ℂ) {c} w =
      c * regularizedHGFun ∅ {c + 1} w + w * regularizedHGFun ∅ {c + 1 + 1} w := by
  have hf := hasFPowerSeriesOnBall_regularized0F1 (c + 1)
  have hs := ((hf.hasSum_mul_pow (z := w) (by simp)).mul_left c).add
    (hf.hasSum_z_mul_deriv (z := w) (by simp))
  have he (n : ℕ) : regularizedHGFunCoeff ∅ {c} n =
      (c + n) * regularizedHGFunCoeff ∅ {c + 1} n := by
    simp only [regularizedHGFunCoeff_empty, one_div, mul_inv_rev]
    rw [one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (c + n),
      show c + n + 1 = c + 1 + n by ring]
    ring
  have ht : HasSum (fun n => regularizedHGFunCoeff ∅ {c} n * w ^ n)
      (c * regularizedHGFun ∅ {c + 1} w + w * deriv (regularizedHGFun ∅ {c + 1}) w) := by
    convert! hs using 1
    funext n
    rw [he]
    ring
  rw [deriv_regularized0F1] at ht
  exact ((hasFPowerSeriesOnBall_regularized0F1 c).hasSum_mul_pow (by simp)).unique ht

/-- Formula under the stated hypotheses: `z / 2 ∈ slitPlane`. -/
theorem div_two_mem_slitPlane {z : ℂ} (hz : z ∈ slitPlane) : z / 2 ∈ slitPlane := by
  simpa [mem_slitPlane_iff, div_re, div_im] using hz

/-- Derivative of the principal-power prefactor in the Bessel series. -/
theorem hasDerivAt_besselPrefactor (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun w : ℂ => (w / 2) ^ ν) ((z / 2) ^ ν * (ν / z)) z := by
  have hd := ((hasDerivAt_id z).div_const 2).cpow_const (c := ν) (div_two_mem_slitPlane hz)
  convert! hd using 1
  simp only [id_eq]
  rw [cpow_sub _ _ (div_ne_zero (slitPlane_ne_zero hz) (by norm_num)), cpow_one]
  field

/-- Analyticity of the common Bessel series with either sign of its quadratic argument. -/
theorem analyticAt_besselSeries (ν σ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    AnalyticAt ℂ (fun w : ℂ => (w / 2) ^ ν *
      regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (σ * w ^ 2 / 4)) z := by
  apply AnalyticAt.mul
  · exact (analyticAt_id.div_const (c := (2 : ℂ))).cpow analyticAt_const (div_two_mem_slitPlane hz)
  · exact (analyticAt_regularized0F1 (ν + 1) _).comp (by fun_prop)

/-- AAR (4.5.1)–(4.5.2), with a sign parameter to cover modified Bessel functions too. -/
theorem besselSeries_ode (ν σ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    let f := fun w : ℂ => (w / 2) ^ ν *
      regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (σ * w ^ 2 / 4)
    z ^ 2 * deriv (deriv f) z + z * deriv f z - (σ * z ^ 2 + ν ^ 2) * f z = 0 := by
  let F := regularizedHGFun (∅ : Multiset ℂ) {ν + 1}
  let u := fun w : ℂ => σ * w ^ 2 / 4
  let g := fun w : ℂ => (w / 2) ^ ν
  let q := fun w : ℂ => ν / w
  let r := fun w : ℂ => σ * w / 2
  let f := fun w : ℂ => g w * F (u w)
  have hu (w : ℂ) : HasDerivAt u (r w) w := by
    convert! (((hasDerivAt_id w).pow 2).const_mul σ).div_const 4 using 1
    simp [r]
    ring
  have hF (w : ℂ) : HasDerivAt F (deriv F w) w :=
    (analyticAt_regularized0F1 (ν + 1) w).differentiableAt.hasDerivAt
  have hF' (w : ℂ) : HasDerivAt (deriv F) (deriv (deriv F) w) w :=
    (analyticAt_regularized0F1 (ν + 1) w).deriv.differentiableAt.hasDerivAt
  have hg (w : ℂ) (hw : w ∈ slitPlane) : HasDerivAt g (g w * q w) w :=
    hasDerivAt_besselPrefactor ν hw
  have hfirst (w : ℂ) (hw : w ∈ slitPlane) :
      deriv f w = g w * (q w * F (u w) + r w * deriv F (u w)) := by
    change deriv (g * F ∘ u) w = _
    rw [((hg w hw).mul ((hF (u w)).comp w (hu w))).deriv]
    simp only [Function.comp_apply]
    ring
  have heq : deriv f =ᶠ[𝓝 z]
      (g * (q * F ∘ u + r * deriv F ∘ u)) :=
    Filter.eventually_of_mem (isOpen_slitPlane.mem_nhds hz) hfirst
  have hq : HasDerivAt q (-ν / z ^ 2) z := by
    convert! (hasDerivAt_const z ν).div (hasDerivAt_id z) (slitPlane_ne_zero hz) using 1
    simp
  have hr : HasDerivAt r (σ / 2) z := by
    simpa [r] using ((hasDerivAt_id z).const_mul σ).div_const 2
  have hsecond := (hg z hz).mul
    ((hq.mul ((hF (u z)).comp z (hu z))).add
      (hr.mul ((hF' (u z)).comp z (hu z))))
  change z ^ 2 * deriv (deriv f) z + z * deriv f z - (σ * z ^ 2 + ν ^ 2) * f z = 0
  rw [heq.deriv_eq, hsecond.deriv, hfirst z hz]
  have hode := regularized0F1_ode (ν + 1) (u z)
  change u z * deriv (deriv F) (u z) + (ν + 1) * deriv F (u z) - F (u z) = 0 at hode
  dsimp only [f, q, r, Pi.mul_apply, Pi.add_apply, Function.comp_apply]
  linear_combination (norm := (dsimp [u]; field_simp [slitPlane_ne_zero hz]; ring))
    (σ * z ^ 2 * g z) * hode

/-- `J_ν(0) = 0` for `ν ≠ 0`. -/
theorem besselJ_apply_zero {ν : ℂ} (hν : ν ≠ 0) : besselJ ν 0 = 0 := by
  simp [Complex.besselJ_zero, hν]

/-- `J_0(0) = 1`. -/
theorem besselJ_zero_zero : besselJ 0 0 = 1 := by
  simp [Complex.besselJ_zero]

/-- Bessel's equation `z² y'' + z y' + (z² - ν²) y = 0` (AAR §4.5). -/
@[dlmf 10.2.E1]
theorem besselJ_ode {ν z : ℂ} (hz : z ∈ slitPlane) :
    z ^ 2 * iteratedDeriv 2 (besselJ ν) z + z * deriv (besselJ ν) z +
      (z ^ 2 - ν ^ 2) * besselJ ν z = 0 := by
  have he := besselSeries_ode ν (-1) hz
  have hf : (fun w : ℂ => (w / 2) ^ ν * regularizedHGFun ∅ {ν + 1} (-1 * w ^ 2 / 4)) =
      besselJ ν := by funext w; simp only [besselJ_eq_regularized, neg_one_mul, neg_div]
  dsimp only at he
  rw [hf] at he
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  simp only [besselJ_eq_regularized, neg_one_mul, neg_div] at he ⊢
  linear_combination he

/-- AAR (4.6.2): the derivative of `J_ν` in terms of `J_{ν+1}`. -/
theorem hasDerivAt_besselJ {ν z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (besselJ ν) (ν / z * besselJ ν z - besselJ (ν + 1) z) z := by
  have hu : HasDerivAt (fun w : ℂ => -(w ^ 2 / 4)) (-z / 2) z := by
    convert! (((hasDerivAt_id z).pow 2).div_const 4).neg using 1
    simp
    ring
  have hd := (hasDerivAt_besselPrefactor ν hz).mul
    ((hasDerivAt_regularized0F1 (ν + 1) (-(z ^ 2 / 4))).comp z hu)
  have hJ : ∀ μ : ℂ, besselJ μ =
      fun w => (w / 2) ^ μ * regularizedHGFun (∅ : Multiset ℂ) {μ + 1} (-(w ^ 2 / 4)) :=
    fun μ => funext (besselJ_eq_regularized μ)
  rw [hJ ν, hJ (ν + 1)]
  convert! hd using 1
  simp only [Function.comp_apply]
  rw [cpow_add _ _ (div_ne_zero (slitPlane_ne_zero hz) (by norm_num)), cpow_one]
  ring

/-- Identity under the stated parameter and domain assumptions: `z ^ 2 * iteratedDeriv 2 (besselY
ν) z + z * deriv (besselY ν) z + (z ^ 2 - ν ^ 2) * besselY ν z = 0`. -/
@[dlmf 10.2.E1]
theorem besselY_ode {ν z : ℂ} (hz : z ∈ slitPlane) (hν : ∀ k : ℤ, ν ≠ k) :
    z ^ 2 * iteratedDeriv 2 (besselY ν) z + z * deriv (besselY ν) z +
      (z ^ 2 - ν ^ 2) * besselY ν z = 0 := by
  let a := cos (ν * π) / sin (ν * π)
  let b := -1 / sin (ν * π)
  have hf : besselY ν = (fun w => a * besselJ ν w + b * besselJ (-ν) w) := by
    funext w
    simp only [besselY, show ¬ ∃ k : ℤ, ν = k from not_exists.mpr hν, ↓reduceIte]
    dsimp [a, b]
    ring
  have hp := analyticAt_besselJ ν hz
  have hn := analyticAt_besselJ (-ν) hz
  rw [hf, iteratedDeriv_fun_add (contDiffAt_const.mul (hp.contDiffAt (n := 2)))
      (contDiffAt_const.mul (hn.contDiffAt (n := 2))),
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
    deriv_fun_add (hp.differentiableAt.const_mul a)
      (hn.differentiableAt.const_mul b),
    deriv_const_mul_field, deriv_const_mul_field]
  linear_combination a * besselJ_ode (ν := ν) hz + b * besselJ_ode (ν := -ν) hz

/-- Half-integer Gamma values needed for the elementary Bessel evaluations. -/
theorem Gamma_three_halves : Gamma (3 / 2 : ℂ) = Gamma (1 / 2) / 2 := by
  have h := Gamma_add_one (1 / 2 : ℂ) (by norm_num)
  have heq : (1 / 2 : ℂ) + 1 = 3 / 2 := by ring
  rw [heq] at h
  rw [h]
  ring

/-- Identity under the stated parameter and domain assumptions: `Gamma ((3 / 2 : ℂ) + n) = ((2 * n
+ 1).factorial : ℂ) / (4 ^ n * n.factorial * 2) * Gamma (1 / 2)`. -/
theorem Gamma_nat_add_three_halves (n : ℕ) :
    Gamma ((3 / 2 : ℂ) + n) =
      ((2 * n + 1).factorial : ℂ) / (4 ^ n * n.factorial * 2) * Gamma (1 / 2) := by
  have hfac : ((2 * n + 1).factorial : ℝ) =
      (2 * n + 1).doubleFactorial * (2 ^ n * n.factorial) := by
    have h := Nat.factorial_eq_mul_doubleFactorial (2 * n)
    rw [Nat.doubleFactorial_two_mul] at h
    exact_mod_cast h
  have hreal : Real.Gamma (n + 1 + 1 / 2) =
      (2 * n + 1).factorial / (4 ^ n * n.factorial * 2) * Real.Gamma (1 / 2) := by
    rw [Real.Gamma_nat_add_one_add_half, Real.Gamma_one_half_eq, hfac]
    have h4 : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    rw [h4, pow_succ]
    field_simp
  have e1 : ((3 / 2 : ℂ) + n) = ((n + 1 + 1 / 2 : ℝ) : ℂ) := by push_cast; ring
  have e2 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2, Complex.Gamma_ofReal, Complex.Gamma_ofReal, hreal]
  push_cast
  ring

/-- Identity under the stated parameter and domain assumptions: `Gamma ((1 / 2 : ℂ) + n) = ((2 *
n).factorial : ℂ) / (4 ^ n * n.factorial) * Gamma (1 / 2)`. -/
theorem Gamma_nat_add_half (n : ℕ) :
    Gamma ((1 / 2 : ℂ) + n) =
      ((2 * n).factorial : ℂ) / (4 ^ n * n.factorial) * Gamma (1 / 2) := by
  have hfac : ((2 * n).factorial : ℝ) = 2 ^ n * n.factorial * (2 * n - 1).doubleFactorial := by
    rcases n with _ | n
    · simp
    · have h := Nat.factorial_eq_mul_doubleFactorial (2 * (n + 1) - 1)
      rw [show 2 * (n + 1) - 1 + 1 = 2 * (n + 1) by omega, Nat.doubleFactorial_two_mul] at h
      exact_mod_cast h
  have hreal : Real.Gamma (n + 1 / 2) =
      (2 * n).factorial / (4 ^ n * n.factorial) * Real.Gamma (1 / 2) := by
    rw [Real.Gamma_nat_add_half, Real.Gamma_one_half_eq, hfac]
    have h4 : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    rw [h4]
    field_simp
  have e1 : ((1 / 2 : ℂ) + n) = ((n + 1 / 2 : ℝ) : ℂ) := by push_cast; ring
  have e2 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2, Complex.Gamma_ofReal, Complex.Gamma_ofReal, hreal]
  push_cast
  ring

/-- Identity under the stated parameter and domain assumptions: `log (2 : ℂ) = Real.log 2`. -/
theorem log_two : log (2 : ℂ) = Real.log 2 := by
  rw [← ofReal_ofNat 2, ofReal_log (by norm_num)]

/-- Identity under the stated parameter and domain assumptions: `log (π : ℂ) = Real.log π`. -/
theorem log_pi : log (π : ℂ) = Real.log π :=
  (ofReal_log Real.pi_pos.le).symm

/-- Nonvanishing under the stated hypotheses: `(π : ℂ).arg ≠ π`. -/
theorem arg_pi_ne_pi : (π : ℂ).arg ≠ π := by
  rw [arg_ofReal_of_nonneg Real.pi_pos.le]
  exact ne_of_lt Real.pi_pos

/-- Identity under the stated parameter and domain assumptions: `log (z / 2) = log z - log 2`. -/
theorem log_div_ofNat_two {z : ℂ} (hz : z ∈ slitPlane) :
    log (z / 2) = log z - log 2 := by
  have hz0 := slitPlane_ne_zero hz
  have hinv : (2 : ℂ)⁻¹ = ↑((2 : ℝ)⁻¹) := by
    rw [← ofReal_ofNat 2, ← ofReal_inv]
  rw [div_eq_mul_inv, hinv, log_mul_ofReal (2⁻¹) (by norm_num) z hz0, Real.log_inv,
    ofReal_neg, log_two]
  ring

/-- Identity under the stated parameter and domain assumptions: `(z / 2) ^ (1 / 2 : ℂ) = z ^ (1 /
2 : ℂ) / (2 : ℂ) ^ (1 / 2 : ℂ)`. -/
theorem cpow_half_div_two {z : ℂ} (hz : z ∈ slitPlane) :
    (z / 2) ^ (1 / 2 : ℂ) = z ^ (1 / 2 : ℂ) / (2 : ℂ) ^ (1 / 2 : ℂ) := by
  have hz0 := slitPlane_ne_zero hz
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  rw [cpow_def_of_ne_zero (div_ne_zero hz0 h2), log_div_ofNat_two hz, sub_mul, exp_sub,
    ← cpow_def_of_ne_zero hz0, ← cpow_def_of_ne_zero h2]

/-- Identity under the stated parameter and domain assumptions: `(z / 2) ^ (-(1 / 2 : ℂ)) = (2 :
ℂ) ^ (1 / 2 : ℂ) / z ^ (1 / 2 : ℂ)`. -/
theorem cpow_half_recip_div_two {z : ℂ} (hz : z ∈ slitPlane) :
    (z / 2) ^ (-(1 / 2 : ℂ)) = (2 : ℂ) ^ (1 / 2 : ℂ) / z ^ (1 / 2 : ℂ) := by
  rw [cpow_neg, cpow_half_div_two hz, inv_div]

/-- Identity under the stated parameter and domain assumptions: `((2 : ℂ) / π) ^ (1 / 2 : ℂ) = (2
: ℂ) ^ (1 / 2 : ℂ) / (π : ℂ) ^ (1 / 2 : ℂ)`. -/
theorem cpow_half_div_pi :
    ((2 : ℂ) / π) ^ (1 / 2 : ℂ) =
      (2 : ℂ) ^ (1 / 2 : ℂ) / (π : ℂ) ^ (1 / 2 : ℂ) := by
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hlog : log ((2 : ℂ) / π) = log 2 - log π := by
    rw [div_eq_mul_inv, ← ofReal_ofNat 2, log_ofReal_mul (by norm_num) (inv_ne_zero hπ),
      log_inv _ arg_pi_ne_pi, ← log_two, log_pi]
    simp [ofReal_ofNat]
    abel
  rw [cpow_def_of_ne_zero (div_ne_zero h2 hπ), hlog, sub_mul, exp_sub,
    ← cpow_def_of_ne_zero h2, ← cpow_def_of_ne_zero hπ]

/-- Identity under the stated parameter and domain assumptions: `(2 / (π * z)) ^ (1 / 2 : ℂ) = ((2
: ℂ) / π) ^ (1 / 2 : ℂ) / z ^ (1 / 2 : ℂ)`. -/
theorem cpow_half_two_div_pi_z {z : ℂ} (hz : z ∈ slitPlane) :
    (2 / (π * z)) ^ (1 / 2 : ℂ) =
      ((2 : ℂ) / π) ^ (1 / 2 : ℂ) / z ^ (1 / 2 : ℂ) := by
  have hz0 := slitPlane_ne_zero hz
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpos : 0 < ((2 : ℝ) / π) := by positivity
  have hzinv : log (z⁻¹) = -log z := log_inv z (slitPlane_arg_ne_pi hz)
  have hform : (2 : ℂ) / (π * z) = ↑((2 : ℝ) / π) * z⁻¹ := by
    push_cast
    field [hπ, hz0]
  have hlog : log (2 / (π * z)) = log ((2 : ℂ) / π) - log z := by
    rw [hform, log_ofReal_mul hpos (inv_ne_zero hz0), hzinv, ofReal_log hpos.le,
      ofReal_div, ofReal_ofNat]
    ring
  rw [cpow_def_of_ne_zero (div_ne_zero h2 (mul_ne_zero hπ hz0)), hlog, sub_mul, exp_sub,
    ← cpow_def_of_ne_zero (div_ne_zero h2 hπ), ← cpow_def_of_ne_zero hz0]

/-- Identity under the stated parameter and domain assumptions: `w = w ^ (1 / 2 : ℂ) * w ^ (1 / 2
: ℂ)`. -/
theorem cpow_half_sq {w : ℂ} (hw : w ≠ 0) :
    w = w ^ (1 / 2 : ℂ) * w ^ (1 / 2 : ℂ) := by
  have hadd := cpow_add (x := w) (1 / 2 : ℂ) (1 / 2 : ℂ) hw
  have hsum : (1 / 2 : ℂ) + 1 / 2 = 1 := by ring
  rw [hsum, cpow_one] at hadd
  exact hadd

/-- The algebraic identity connecting the half-integer Bessel prefactors. -/
theorem bessel_half_prefactor {z : ℂ} (hz : z ∈ slitPlane) :
    (z / 2) ^ (1 / 2 : ℂ) * 2 / (z * Gamma (1 / 2 : ℂ)) =
      (2 / (π * z)) ^ (1 / 2 : ℂ) := by
  have hz0 := slitPlane_ne_zero hz
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2h : (2 : ℂ) ^ (1 / 2 : ℂ) ≠ 0 :=
    (cpow_ne_zero_iff.mpr (Or.inl h2) : (2 : ℂ) ^ (1 / 2 : ℂ) ≠ 0)
  have hzh : z ^ (1 / 2 : ℂ) ≠ 0 :=
    (cpow_ne_zero_iff.mpr (Or.inl hz0) : z ^ (1 / 2 : ℂ) ≠ 0)
  have hπh : (π : ℂ) ^ (1 / 2 : ℂ) ≠ 0 :=
    (cpow_ne_zero_iff.mpr (Or.inl hπ) : (π : ℂ) ^ (1 / 2 : ℂ) ≠ 0)
  have hzsq := cpow_half_sq hz0
  have h2sq := cpow_half_sq h2
  rw [Gamma_one_half_eq, cpow_half_div_two hz, cpow_half_two_div_pi_z hz, cpow_half_div_pi]
  have hform :
      z ^ (1 / 2 : ℂ) / (2 : ℂ) ^ (1 / 2 : ℂ) * 2 / (z * (π : ℂ) ^ (1 / 2 : ℂ)) =
        z ^ (1 / 2 : ℂ) / (2 : ℂ) ^ (1 / 2 : ℂ) *
          ((2 : ℂ) ^ (1 / 2 : ℂ) * (2 : ℂ) ^ (1 / 2 : ℂ)) /
        (z ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) * (π : ℂ) ^ (1 / 2 : ℂ)) := by
    rw [← hzsq, ← h2sq]
  have hsimp :
      z ^ (1 / 2 : ℂ) / (2 : ℂ) ^ (1 / 2 : ℂ) *
          ((2 : ℂ) ^ (1 / 2 : ℂ) * (2 : ℂ) ^ (1 / 2 : ℂ)) /
        (z ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) * (π : ℂ) ^ (1 / 2 : ℂ)) =
        (2 : ℂ) ^ (1 / 2 : ℂ) / (π : ℂ) ^ (1 / 2 : ℂ) / z ^ (1 / 2 : ℂ) := by
    field [h2h, hzh, hπh]
  rw [hform, hsimp]

/-- Identity under the stated parameter and domain assumptions: `regularizedHGFun (∅ : Multiset ℂ)
{3 / 2} (-(z ^ 2 / 4)) = 2 * sin z / (z * Gamma (1 / 2 : ℂ))`. -/
theorem regularized0F1_three_halves_eq_sinc {z : ℂ} (hz : z ≠ 0) :
    regularizedHGFun (∅ : Multiset ℂ) {3 / 2} (-(z ^ 2 / 4)) =
      2 * sin z / (z * Gamma (1 / 2 : ℂ)) := by
  have hg : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hs := (hasFPowerSeriesOnBall_regularized0F1 (3 / 2 : ℂ)).hasSum_mul_pow
    (z := -(z ^ 2 / 4)) (by simp)
  have hcoeff (n : ℕ) :
      regularizedHGFunCoeff (∅ : Multiset ℂ) {3 / 2} n * (-(z ^ 2 / 4)) ^ n =
        (2 / Gamma (1 / 2 : ℂ)) *
          ((-1) ^ n * z ^ (2 * n) / (2 * n + 1).factorial) := by
    have hn0 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have h2n : ((2 * n + 1).factorial : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (2 * n + 1).factorial_ne_zero
    have h4 : (4 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    have h2 : (2 : ℂ) ≠ 0 := by norm_num
    have hG : Gamma ((3 / 2 : ℂ) + n) ≠ 0 := by
      refine Gamma_ne_zero_of_re_pos ?_
      simp
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    rw [regularizedHGFunCoeff_empty, Gamma_nat_add_three_halves]
    have hpow : (-(z ^ 2 / 4)) ^ n = (-1) ^ n * z ^ (2 * n) / (4 : ℂ) ^ n := by
      rw [neg_pow, div_pow, pow_mul, mul_div_assoc]
    rw [hpow]
    field [hn0, h2n, h4, h2, hg, hG]
  simp_rw [hcoeff] at hs
  have hsin0 := (hasSum_sin z).div_const z
  have heq : (fun n : ℕ => ((-1) ^ n * z ^ (2 * n + 1) / (2 * n + 1).factorial) / z) =
      fun n => (-1) ^ n * z ^ (2 * n) / (2 * n + 1).factorial := by
    ext n
    field [hz]
  rw [heq] at hsin0
  have hval : (2 / Gamma (1 / 2 : ℂ)) * (sin z / z) =
      2 * sin z / (z * Gamma (1 / 2 : ℂ)) := by
    field [hz, hg]
  exact hs.unique (hval ▸ hsin0.mul_left (2 / Gamma (1 / 2 : ℂ)))

/-- Identity under the stated parameter and domain assumptions: `regularizedHGFun (∅ : Multiset ℂ)
{1 / 2} (-(z ^ 2 / 4)) = cos z / Gamma (1 / 2 : ℂ)`. -/
theorem regularized0F1_half_eq_cos {z : ℂ} :
    regularizedHGFun (∅ : Multiset ℂ) {1 / 2} (-(z ^ 2 / 4)) =
      cos z / Gamma (1 / 2 : ℂ) := by
  have hg : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hs := (hasFPowerSeriesOnBall_regularized0F1 (1 / 2 : ℂ)).hasSum_mul_pow
    (z := -(z ^ 2 / 4)) (by simp)
  have hcoeff (n : ℕ) :
      regularizedHGFunCoeff (∅ : Multiset ℂ) {1 / 2} n * (-(z ^ 2 / 4)) ^ n =
        (1 / Gamma (1 / 2 : ℂ)) * ((-1) ^ n * z ^ (2 * n) / (2 * n).factorial) := by
    have hn0 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have h2n : ((2 * n).factorial : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (2 * n).factorial_ne_zero
    have h4 : (4 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    have hG : Gamma ((1 / 2 : ℂ) + n) ≠ 0 := by
      refine Gamma_ne_zero_of_re_pos ?_
      simp
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    rw [regularizedHGFunCoeff_empty, Gamma_nat_add_half]
    have hpow : (-(z ^ 2 / 4)) ^ n = (-1) ^ n * z ^ (2 * n) / (4 : ℂ) ^ n := by
      rw [neg_pow, div_pow, pow_mul, mul_div_assoc]
    rw [hpow]
    field [hn0, h2n, h4, hg, hG]
  simp_rw [hcoeff] at hs
  have hval : (1 / Gamma (1 / 2 : ℂ)) * cos z = cos z / Gamma (1 / 2 : ℂ) := by
    field [hg]
  exact hs.unique (hval ▸ (hasSum_cos z).mul_left (1 / Gamma (1 / 2 : ℂ)))

/-- Elementary evaluation `J_{1/2}(z) = √(2/(πz)) sin z` (AAR §4.5). -/
@[dlmf 10.16.E1]
theorem besselJ_half (z : ℂ) (hz : z ∈ slitPlane) :
    besselJ (1 / 2) z = (2 / (π * z)) ^ (1 / 2 : ℂ) * sin z := by
  have hz0 := slitPlane_ne_zero hz
  have hg : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hpar : (1 / 2 : ℂ) + 1 = 3 / 2 := by ring
  simp only [besselJ_eq_regularized]
  rw [hpar, regularized0F1_three_halves_eq_sinc hz0, ← bessel_half_prefactor hz]
  field [hz0, hg]

/-- Elementary evaluation `J_{-1/2}(z) = √(2/(πz)) cos z`. -/
@[dlmf 10.16.E1]
theorem besselJ_neg_half (z : ℂ) (hz : z ∈ slitPlane) :
    besselJ (-(1 / 2)) z = (2 / (π * z)) ^ (1 / 2 : ℂ) * cos z := by
  have hz0 := slitPlane_ne_zero hz
  have hg : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2h : (2 : ℂ) ^ (1 / 2 : ℂ) ≠ 0 :=
    (cpow_ne_zero_iff.mpr (Or.inl h2) : (2 : ℂ) ^ (1 / 2 : ℂ) ≠ 0)
  have hzh : z ^ (1 / 2 : ℂ) ≠ 0 :=
    (cpow_ne_zero_iff.mpr (Or.inl hz0) : z ^ (1 / 2 : ℂ) ≠ 0)
  have hπh : (π : ℂ) ^ (1 / 2 : ℂ) ≠ 0 :=
    (cpow_ne_zero_iff.mpr (Or.inl hπ) : (π : ℂ) ^ (1 / 2 : ℂ) ≠ 0)
  have hpar : -(1 / 2 : ℂ) + 1 = 1 / 2 := by ring
  simp only [besselJ_eq_regularized]
  rw [hpar, regularized0F1_half_eq_cos, cpow_half_recip_div_two hz, Gamma_one_half_eq,
    cpow_half_two_div_pi_z hz, cpow_half_div_pi]
  field [hz0, hg, h2h, hzh, hπh]

/-- Kummer's second transformation (AAR (4.1.12), p. 191), in regularized `₀F₁` form. -/
theorem kummerM_eq_exp_mul_regularized0F1 {ν : ℂ}
    (hν : ∀ k : ℕ, ν + 1 ≠ -k) (h2ν : ∀ k : ℕ, 2 * ν + 1 ≠ -k) (z : ℂ) :
    kummerM (ν + 1 / 2) (2 * ν + 1) z =
      Gamma (ν + 1) * exp (z / 2) * regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (z ^ 2 / 16) := by
  let F := regularizedHGFun (∅ : Multiset ℂ) {ν + 1}
  let u := fun w : ℂ => w ^ 2 / 16
  let g := fun w : ℂ => Gamma (ν + 1) * exp (w / 2)
  let r := fun w : ℂ => w / 8
  let f := fun w : ℂ => g w * F (u w)
  have hu (w : ℂ) : HasDerivAt u (r w) w := by
    convert! ((hasDerivAt_id w).pow 2).div_const 16 using 1
    simp [r]
    ring
  have hg (w : ℂ) : HasDerivAt g (g w / 2) w := by
    convert! (((hasDerivAt_id w).div_const 2).cexp).const_mul (Gamma (ν + 1)) using 1
    dsimp [g]
    ring
  have hF (w : ℂ) : HasDerivAt F (deriv F w) w :=
    (analyticAt_regularized0F1 (ν + 1) w).differentiableAt.hasDerivAt
  have hF' (w : ℂ) : HasDerivAt (deriv F) (deriv (deriv F) w) w :=
    (analyticAt_regularized0F1 (ν + 1) w).deriv.differentiableAt.hasDerivAt
  have hfirst (w : ℂ) : deriv f w = g w * ((1 / 2) * F (u w) + r w * deriv F (u w)) := by
    change deriv (g * F ∘ u) w = _
    rw [((hg w).mul ((hF (u w)).comp w (hu w))).deriv]
    simp only [Function.comp_apply]
    ring
  have hdeq : deriv f = g * ((fun w => (1 / 2) * (F ∘ u) w) + r * deriv F ∘ u) := funext hfirst
  have hode (w : ℂ) : w * deriv (deriv f) w + (2 * ν + 1 - w) * deriv f w -
      (ν + 1 / 2) * f w = 0 := by
    have hr : HasDerivAt r (1 / 8) w := (hasDerivAt_id w).div_const 8
    have ht := (hg w).mul
      ((((hF (u w)).comp w (hu w)).const_mul (1 / 2)).add
        (hr.mul ((hF' (u w)).comp w (hu w))))
    rw [hdeq, ht.deriv]
    have he := regularized0F1_ode (ν + 1) (u w)
    change u w * deriv (deriv F) (u w) + (ν + 1) * deriv F (u w) - F (u w) = 0 at he
    dsimp only [f, r, Pi.mul_apply, Pi.add_apply, Function.comp_apply]
    linear_combination (norm := (dsimp [u]; ring)) (w * g w / 4) * he
  have hfa (w : ℂ) : AnalyticAt ℂ f w := by
    apply AnalyticAt.mul
    · dsimp [g]
      fun_prop
    · exact (analyticAt_regularized0F1 (ν + 1) _).comp (by dsimp [u]; fun_prop)
  have hs := hasFPowerSeriesOnBall_kummerM (a := ν + 1 / 2) h2ν
  have hma (w : ℂ) : AnalyticAt ℂ (kummerM (ν + 1 / 2) (2 * ν + 1)) w :=
    hs.analyticAt_of_mem (by simp)
  have hmode (w : ℂ) : w * deriv (deriv (kummerM (ν + 1 / 2) (2 * ν + 1))) w +
      (2 * ν + 1 - w) * deriv (kummerM (ν + 1 / 2) (2 * ν + 1)) w -
      (ν + 1 / 2) * kummerM (ν + 1 / 2) (2 * ν + 1) w = 0 := by
    have he := hs.ode_of_recurrence (A := 0) (B := 1) (C := ν + 1 / 2) (D := 2 * ν + 1)
      (fun n => by rw [kummerMCoeff_recurrence h2ν]; ring) (z := w) (by simp)
    simpa using he
  have hzero : f 0 = kummerM (ν + 1 / 2) (2 * ν + 1) 0 := by
    simp [f, g, F, u, DLMF.Confluent.regularizedHGFun_zero, regularizedHGFunCoeff, Gamma_ne_zero hν]
  exact (congrFun (confluent_ode_unique h2ν hfa hma hode hmode hzero) z).symm

/-- Relation of `J_ν` to Kummer's function (AAR §4.5). -/
@[dlmf 10.16.E5]
theorem besselJ_eq_kummerM {ν z : ℂ} (hν : ∀ k : ℕ, ν + 1 ≠ -k)
    (h2ν : ∀ k : ℕ, 2 * ν + 1 ≠ -k) :
    besselJ ν z =
      (z / 2) ^ ν * exp (-I * z) / Gamma (ν + 1) *
        kummerM (ν + 1 / 2) (2 * ν + 1) (2 * I * z) := by
  rw [kummerM_eq_exp_mul_regularized0F1 hν h2ν]
  have hu : (2 * I * z) ^ 2 / 16 = -(z ^ 2 / 4) := by rw [mul_pow, mul_pow, I_sq]; ring
  rw [hu, show (2 * I * z) / 2 = I * z by ring]
  simp only [neg_mul, exp_neg]
  simp only [besselJ_eq_regularized]
  field [Gamma_ne_zero hν, exp_ne_zero (I * z)]

end DLMF.Bessel
