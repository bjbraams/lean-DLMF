/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Basic
public import DLMF.Bessel.Basic.RegularizedSeries
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Bessel's equation and the modified Bessel equation

Bessel's differential equation for `J_ν` and `Y_ν` (DLMF 10.2.1), the derivative and the
basic recurrence of `J_ν` (DLMF 10.6.1), and the modified Bessel equation for `I_ν` and `K_ν`
(DLMF 10.25.1), all from the regularized series `₀F̃₁`.

## Main results

* `besselSeries_ode`: the common equation for `(z/2)^ν ₀F̃₁(;ν+1;σz²/4)`.
* `besselJ_ode`, `besselY_ode`: Bessel's equation (DLMF 10.2.1); `besselY_ode` for
  non-integer order.
* `hasDerivAt_besselJ`, `besselJ_add_sub`, `two_deriv_besselJ`: the derivative of `J_ν` and the
  recurrences DLMF 10.6.1.
* `besselJ_apply_zero`, `besselJ_zero_zero`, `besselI_apply_zero`, `besselI_zero_zero`: values
  at the origin.
* `besselI_eq_besselJ`: `I_ν(z) = i^{-ν} J_ν(iz)` (DLMF 10.27.6).
* `besselI_ode`, `besselK_ode`, `analyticAt_besselI`: the modified Bessel equation
  (DLMF 10.25.1); `besselK_ode` for non-integer order.

## Implementation notes

All functions use the principal branch of `(z/2)^ν`, so the statements hold on the slit plane.
Integer orders of `Y_ν` and `K_ν` are treated in `DLMF.Bessel.Basic.SecondKind`.
-/

@[expose] public section

open Complex
open scoped Real Nat Topology

noncomputable section

namespace DLMF.Bessel

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

/-- Recurrence `(2ν/z) J_ν(z) = J_{ν-1}(z) + J_{ν+1}(z)` (AAR (4.6.5), p. 202). -/
@[dlmf 10.6.E1]
theorem besselJ_add_sub {ν z : ℂ} (hz : z ≠ 0) :
    (2 * ν / z) * besselJ ν z = besselJ (ν - 1) z + besselJ (ν + 1) z := by
  have he := regularized0F1_contiguous ν (-(z ^ 2 / 4))
  simp only [besselJ_eq_regularized]
  rw [cpow_sub _ _ (div_ne_zero hz (by norm_num)),
    cpow_add _ _ (div_ne_zero hz (by norm_num)), cpow_one]
  rw [show ν - 1 + 1 = ν by ring]
  linear_combination (norm := (field_simp [hz]; ring)) (-2 * (z / 2) ^ ν / z) * he

/-- Derivative identity `2 J_ν'(z) = J_{ν-1}(z) - J_{ν+1}(z)` (AAR (4.6.6), p. 202). -/
@[dlmf 10.6.E1]
theorem two_deriv_besselJ {ν z : ℂ} (hz : z ∈ slitPlane) :
    2 * deriv (besselJ ν) z = besselJ (ν - 1) z - besselJ (ν + 1) z := by
  rw [(hasDerivAt_besselJ hz).deriv]
  linear_combination besselJ_add_sub (ν := ν) (slitPlane_ne_zero hz)

/-- Identity under the stated parameter and domain assumptions: `besselI ν 0 = 0`. -/
theorem besselI_apply_zero {ν : ℂ} (hν : ν ≠ 0) : besselI ν 0 = 0 := by
  unfold besselI
  rw [zero_div, zero_cpow hν, zero_mul]

/-- Identity under the stated parameter and domain assumptions: `besselI 0 0 = 1`. -/
theorem besselI_zero_zero : besselI 0 0 = 1 := by
  unfold besselI
  rw [zero_div, cpow_zero, one_mul]
  have harg : (0 ^ 2 / 4 : ℂ) = 0 := by ring
  rw [harg, Complex.regularizedHGFun_zero, regularizedHGFunCoeff_empty]
  simp [Gamma_one]

/-- `I_ν(z) = i^{-ν} J_ν(i z)` (principal branch). -/
@[dlmf 10.27.E6]
theorem besselI_eq_besselJ {ν z : ℂ} (hz : z ≠ 0) (harg : z.arg ≤ π / 2) :
    besselI ν z = I ^ (-ν) * besselJ ν (I * z) := by
  have hz2 : z / 2 ≠ 0 := div_ne_zero hz (by norm_num)
  have harg2 : (z / 2).arg = z.arg := by
    simpa only [div_eq_mul_inv, ← ofReal_ofNat, ← ofReal_inv] using
      arg_mul_real (r := (2 : ℝ)⁻¹) (by norm_num) z
  have hlog : log (I * (z / 2)) = log I + log (z / 2) := by
    apply log_mul I_ne_zero hz2
    rw [arg_I, harg2]
    exact ⟨by linarith [neg_pi_lt_arg z, Real.pi_pos], by linarith⟩
  have hpow : (I * (z / 2)) ^ ν = I ^ ν * (z / 2) ^ ν := by
    rw [cpow_def_of_ne_zero (mul_ne_zero I_ne_zero hz2), hlog, add_mul, exp_add,
      ← cpow_def_of_ne_zero I_ne_zero, ← cpow_def_of_ne_zero hz2]
  have hsq : -((I * z) ^ 2 / 4) = z ^ 2 / 4 := by
    rw [mul_pow, I_sq]
    ring
  unfold besselI
  simp only [besselJ_eq_regularized]
  rw [hsq, show I * z / 2 = I * (z / 2) by ring, hpow, cpow_neg]
  field [(cpow_ne_zero_iff.mpr (Or.inl I_ne_zero) : I ^ ν ≠ 0)]

/-- Modified Bessel equation `z² y'' + z y' - (z² + ν²) y = 0`. -/
@[dlmf 10.25.E1]
theorem besselI_ode {ν z : ℂ} (hz : z ∈ slitPlane) :
    z ^ 2 * iteratedDeriv 2 (besselI ν) z + z * deriv (besselI ν) z -
      (z ^ 2 + ν ^ 2) * besselI ν z = 0 := by
  have he := besselSeries_ode ν 1 hz
  have hf : (fun w : ℂ => (w / 2) ^ ν * regularizedHGFun ∅ {ν + 1} (1 * w ^ 2 / 4)) =
      besselI ν := by funext w; simp only [besselI, one_mul]
  dsimp only at he
  rw [hf] at he
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero, besselI, one_mul] using he

/-- `I_ν` is analytic on the principal slit plane, for every order. -/
theorem analyticAt_besselI (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    AnalyticAt ℂ (besselI ν) z := by
  have he := analyticAt_besselSeries ν 1 hz
  have hf : (fun w : ℂ => (w / 2) ^ ν * regularizedHGFun ∅ {ν + 1} (1 * w ^ 2 / 4)) =
      besselI ν := by funext w; simp only [besselI, one_mul]
  rwa [hf] at he

/-- Identity under the stated parameter and domain assumptions: `z ^ 2 * iteratedDeriv 2 (besselK
ν) z + z * deriv (besselK ν) z - (z ^ 2 + ν ^ 2) * besselK ν z = 0`. -/
@[dlmf 10.25.E1]
theorem besselK_ode {ν z : ℂ} (hz : z ∈ slitPlane) (hν : ∀ k : ℤ, ν ≠ k) :
    z ^ 2 * iteratedDeriv 2 (besselK ν) z + z * deriv (besselK ν) z -
      (z ^ 2 + ν ^ 2) * besselK ν z = 0 := by
  let a := -(π : ℂ) / (2 * sin (ν * π))
  let b := (π : ℂ) / (2 * sin (ν * π))
  have hf : besselK ν = (fun w => a * besselI ν w + b * besselI (-ν) w) := by
    funext w
    simp only [besselK, show ¬ ∃ k : ℤ, ν = k from not_exists.mpr hν, ↓reduceIte]
    dsimp [a, b]
    ring
  have hp := analyticAt_besselI ν hz
  have hn := analyticAt_besselI (-ν) hz
  rw [hf, iteratedDeriv_fun_add (contDiffAt_const.mul (hp.contDiffAt (n := 2)))
      (contDiffAt_const.mul (hn.contDiffAt (n := 2))),
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
    deriv_fun_add (hp.differentiableAt.const_mul a) (hn.differentiableAt.const_mul b),
    deriv_const_mul_field, deriv_const_mul_field]
  linear_combination a * besselI_ode (ν := ν) hz + b * besselI_ode (ν := -ν) hz

end DLMF.Bessel
