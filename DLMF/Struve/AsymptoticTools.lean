/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Struve.AngerWeber
public import DLMFMathlib.Analysis.Asymptotics.WatsonRotated
public import DLMFMathlib.Analysis.ODE.PowerSeriesUniqueness
public import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# Tools for the Struve and Anger–Weber asymptotics

The substitution `s = sinh t` turns the Schläfli-type integral (DLMF 11.10.4 via 11.10.1)
`A_ν(z) = π⁻¹ ∫₀^∞ e^{-νt - z sinh t} dt` into a Laplace transform

`A_ν(z) = π⁻¹ ∫₀^∞ e^{-zs} K_ν(s) ds`,  `K_ν(s) = (s + √(1+s²))^{-ν} (1+s²)^{-1/2}`

(`struveAs_angerA_eq_integral`). The kernel is holomorphic off the cuts `±i[1, ∞)`, grows at
most polynomially in closed sectors `|arg s| ≤ α < π/2`, and satisfies
`(1+s²) K'' + 3 s K' + (1-ν²) K = 0` (`struveAs_ode`), so its Taylor coefficients at `0` are
`dₙ/n!` with `d₀ = 1`, `d₁ = -ν`, `d_{n+2} = (ν² - (n+1)²) dₙ` (`struveAs_iteratedDeriv_kernel`).
Rotating the ray (`struveAs_angerA_eq_rot`, by analytic continuation in `z` at nonintegral
order and continuity in the order at integral order) and Watson's lemma give
`A_ν(z) ~ π⁻¹ ∑ dₙ z^{-n-1}` in every rotated sector (`struveAs_angerA_hasAsymptoticExpansion`),
the basis of DLMF 11.11.2–11.11.4.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics
open scoped Real Topology Nat Interval

namespace DLMF.Struve

/-- The domain `1 + s² ∈ ℂ \ (-∞, 0]`. -/
def struveAs_dom : Set ℂ := {s : ℂ | 1 + s ^ 2 ∈ slitPlane}

/-- The Laplace kernel `(s + √(1+s²))^{-ν} / √(1+s²)` of `A_ν`. -/
def struveAs_kernel (ν s : ℂ) : ℂ :=
  (s + (1 + s ^ 2) ^ (1 / 2 : ℂ)) ^ (-ν) * (1 + s ^ 2) ^ (-(1 / 2 : ℂ))

/-- The indicated domain is open: `IsOpen struveAs_dom`. -/
theorem struveAs_isOpen_dom : IsOpen struveAs_dom :=
  isOpen_slitPlane.preimage (by fun_prop)

/-- Estimate under the stated parameter and domain assumptions: `0 < (x ^ (1 / 2 : ℂ)).re`. -/
theorem struveAs_re_cpow_half_pos {x : ℂ} (hx : x ∈ slitPlane) : 0 < (x ^ (1 / 2 : ℂ)).re := by
  have hx0 := slitPlane_ne_zero hx
  rw [cpow_def_of_ne_zero hx0, exp_re]
  refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
  · have h1 := neg_pi_lt_arg x
    have : (log x * (1 / 2)).im = arg x / 2 := by simp [log_im, div_eq_mul_inv]
    rw [this]; linarith
  · have h2 : arg x < π := lt_of_le_of_ne (arg_le_pi x) (mem_slitPlane_iff_arg.mp hx).1
    have : (log x * (1 / 2)).im = arg x / 2 := by simp [log_im, div_eq_mul_inv]
    rw [this]; linarith [Real.pi_pos]

/-- Identity under the stated parameter and domain assumptions: `(x ^ (1 / 2 : ℂ)) ^ 2 = x`. -/
theorem struveAs_cpow_half_sq (x : ℂ) : (x ^ (1 / 2 : ℂ)) ^ 2 = x := by
  rw [one_div]; exact_mod_cast cpow_ofNat_inv_pow x 2

/-- Formula under the stated hypotheses: `s + (1 + s ^ 2) ^ (1 / 2 : ℂ) ∈ slitPlane`. -/
theorem struveAs_add_sqrt_mem {s : ℂ} (hs : s ∈ struveAs_dom) :
    s + (1 + s ^ 2) ^ (1 / 2 : ℂ) ∈ slitPlane := by
  set w := (1 + s ^ 2) ^ (1 / 2 : ℂ) with hw
  have hre := struveAs_re_cpow_half_pos hs
  rw [← hw] at hre
  have hw2 : w ^ 2 = 1 + s ^ 2 := struveAs_cpow_half_sq _
  rw [mem_slitPlane_iff]
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  set a := (s + w).re
  have hu : s + w = (a : ℂ) := Complex.ext (by simp [a]) (by simp [h2])
  have hws : w = a - s := by rw [← hu]; ring
  have key : (2 * a : ℂ) * w = a ^ 2 + 1 := by
    have : ((a : ℂ) - s) ^ 2 = 1 + s ^ 2 := by rw [← hws]; exact hw2
    rw [hws]; linear_combination this
  have key2 := congrArg Complex.re key
  simp only [mul_re, re_ofNat, im_ofNat, ofReal_re, ofReal_im, mul_zero, sub_zero,
    add_re, one_re] at key2
  rw [show ((a : ℂ) ^ 2).re = a ^ 2 by norm_cast, show ((2 : ℂ) * a).im = 0 by simp,
    zero_mul, sub_zero] at key2
  have : 2 * a * w.re ≤ 0 := by nlinarith
  nlinarith [sq_nonneg a]

/-- Nonvanishing under the stated hypotheses: `1 + s ^ 2 ≠ 0`. -/
theorem struveAs_one_add_sq_ne_zero {s : ℂ} (hs : s ∈ struveAs_dom) : 1 + s ^ 2 ≠ 0 :=
  slitPlane_ne_zero hs

/-- At `s`, the function `(fun s : ℂ => (1 + s ^ 2) ^ c)` has derivative `(c * (1 + s ^ 2) ^ (c -
1) * (2 * s))`. -/
theorem struveAs_hasDerivAt_cpow (c : ℂ) {s : ℂ} (hs : s ∈ struveAs_dom) :
    HasDerivAt (fun s : ℂ => (1 + s ^ 2) ^ c) (c * (1 + s ^ 2) ^ (c - 1) * (2 * s)) s := by
  have h : HasDerivAt (fun s : ℂ => 1 + s ^ 2) (2 * s) s := by
    simpa using ((hasDerivAt_pow 2 s).const_add 1)
  exact h.cpow_const hs

/-- The factor `q(s) = (1+s²)^{-1/2}`. -/
abbrev struveAs_q (s : ℂ) : ℂ := (1 + s ^ 2) ^ (-(1 / 2 : ℂ))
/-- The factor `h(s) = (s+√(1+s²))^{-ν}`. -/
abbrev struveAs_h (ν s : ℂ) : ℂ := (s + (1 + s ^ 2) ^ (1 / 2 : ℂ)) ^ (-ν)

/-- Identity under the stated parameter and domain assumptions: `(1 + s ^ 2) ^ (1 / 2 : ℂ) *
struveAs_q s = 1`. -/
theorem struveAs_sqrt_mul_q {s : ℂ} (hs : s ∈ struveAs_dom) :
    (1 + s ^ 2) ^ (1 / 2 : ℂ) * struveAs_q s = 1 := by
  rw [struveAs_q, ← cpow_add _ _ (struveAs_one_add_sq_ne_zero hs)]; simp

/-- Identity under the stated parameter and domain assumptions: `struveAs_q s * struveAs_q s * (1
+ s ^ 2) = 1`. -/
theorem struveAs_q_mul_q {s : ℂ} (hs : s ∈ struveAs_dom) :
    struveAs_q s * struveAs_q s * (1 + s ^ 2) = 1 := by
  have hu := struveAs_one_add_sq_ne_zero hs
  rw [struveAs_q, ← cpow_add _ _ hu, show -(1 / 2 : ℂ) + -(1 / 2) = -1 by norm_num, cpow_neg_one,
    inv_mul_cancel₀ hu]

/-- At `s`, the function `struveAs_q` has derivative `(-s * struveAs_q s * (1 + s ^ 2)⁻¹)`. -/
theorem struveAs_hasDerivAt_q {s : ℂ} (hs : s ∈ struveAs_dom) :
    HasDerivAt struveAs_q (-s * struveAs_q s * (1 + s ^ 2)⁻¹) s := by
  have hu := struveAs_one_add_sq_ne_zero hs
  convert struveAs_hasDerivAt_cpow (-(1 / 2 : ℂ)) hs using 1
  rw [cpow_sub _ _ hu, cpow_one, struveAs_q]
  field_simp

/-- At `s`, the function `(struveAs_h ν)` has derivative `(-ν * struveAs_h ν s * struveAs_q s)`. -/
theorem struveAs_hasDerivAt_h (ν : ℂ) {s : ℂ} (hs : s ∈ struveAs_dom) :
    HasDerivAt (struveAs_h ν) (-ν * struveAs_h ν s * struveAs_q s) s := by
  have hu := struveAs_one_add_sq_ne_zero hs
  have hv := struveAs_add_sqrt_mem hs
  have hv0 := slitPlane_ne_zero hv
  have hw : HasDerivAt (fun s : ℂ => s + (1 + s ^ 2) ^ (1 / 2 : ℂ)) (1 + s * struveAs_q s) s := by
    convert (hasDerivAt_id' s).add (struveAs_hasDerivAt_cpow (1 / 2 : ℂ) hs) using 1
    rw [show (1 / 2 : ℂ) - 1 = -(1 / 2) by norm_num, struveAs_q]; ring
  convert hw.cpow_const (c := -ν) hv using 1
  have hwq := struveAs_sqrt_mul_q hs
  have e : 1 + s * struveAs_q s = (s + (1 + s ^ 2) ^ (1 / 2 : ℂ)) * struveAs_q s := by
    linear_combination -hwq
  rw [cpow_sub _ _ hv0, cpow_one, struveAs_h, e]
  field_simp

/-- The first derivative of the kernel. -/
abbrev struveAs_G1 (ν s : ℂ) : ℂ :=
  -ν * struveAs_h ν s * struveAs_q s * struveAs_q s -
    s * struveAs_h ν s * struveAs_q s * (1 + s ^ 2)⁻¹

/-- Identity under the stated parameter and domain assumptions: `struveAs_kernel ν = fun s =>
struveAs_h ν s * struveAs_q s`. -/
theorem struveAs_kernel_eq (ν : ℂ) : struveAs_kernel ν = fun s => struveAs_h ν s * struveAs_q s :=
  rfl

/-- At `s`, the function `(struveAs_kernel ν)` has derivative `(struveAs_G1 ν s)`. -/
theorem struveAs_hasDerivAt_kernel (ν : ℂ) {s : ℂ} (hs : s ∈ struveAs_dom) :
    HasDerivAt (struveAs_kernel ν) (struveAs_G1 ν s) s := by
  rw [struveAs_kernel_eq]
  convert (struveAs_hasDerivAt_h ν hs).mul (struveAs_hasDerivAt_q hs) using 1
  ring

/-- The second derivative of the kernel. -/
abbrev struveAs_G2 (ν s : ℂ) : ℂ :=
  let h := struveAs_h ν s; let q := struveAs_q s; let i := (1 + s ^ 2)⁻¹
  ν ^ 2 * h * q ^ 3 + 3 * ν * s * h * q ^ 2 * i - h * q * i + 3 * s ^ 2 * h * q * i ^ 2

/-- At `s`, the function `(struveAs_G1 ν)` has derivative `(struveAs_G2 ν s)`. -/
theorem struveAs_hasDerivAt_G1 (ν : ℂ) {s : ℂ} (hs : s ∈ struveAs_dom) :
    HasDerivAt (struveAs_G1 ν) (struveAs_G2 ν s) s := by
  have hu := struveAs_one_add_sq_ne_zero hs
  have hh := struveAs_hasDerivAt_h ν hs
  have hq := struveAs_hasDerivAt_q hs
  have hi : HasDerivAt (fun s : ℂ => (1 + s ^ 2)⁻¹) (-(2 * s) / (1 + s ^ 2) ^ 2) s := by
    have h : HasDerivAt (fun s : ℂ => 1 + s ^ 2) (2 * s) s := by
      simpa using ((hasDerivAt_pow 2 s).const_add 1)
    exact h.inv hu
  have := (((hh.const_mul (-ν)).mul hq).mul hq).sub ((((hasDerivAt_id' s).mul hh).mul hq).mul hi)
  convert this using 1
  simp only [struveAs_G2, Pi.mul_apply]
  field_simp
  ring

/-- Identity under the stated parameter and domain assumptions: `(1 + s ^ 2) * struveAs_G2 ν s + 3
* s * struveAs_G1 ν s + (1 - ν ^ 2) * struveAs_kernel ν s = 0`. -/
theorem struveAs_ode (ν : ℂ) {s : ℂ} (hs : s ∈ struveAs_dom) :
    (1 + s ^ 2) * struveAs_G2 ν s + 3 * s * struveAs_G1 ν s + (1 - ν ^ 2) * struveAs_kernel ν s
      = 0 := by
  have hu := struveAs_one_add_sq_ne_zero hs
  have hq2 := struveAs_q_mul_q hs
  have hui : (1 + s ^ 2) * (1 + s ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hu
  simp only [struveAs_G2, struveAs_G1, struveAs_kernel_eq]
  linear_combination (ν ^ 2 * struveAs_h ν s * struveAs_q s) * hq2 +
    (3 * ν * s * struveAs_h ν s * struveAs_q s ^ 2 - struveAs_h ν s * struveAs_q s +
      3 * s ^ 2 * struveAs_h ν s * struveAs_q s * (1 + s ^ 2)⁻¹) * hui

/-- Taylor data `dₙ = n! cₙ` of the kernel: `d₀ = 1`, `d₁ = -ν`, `d_{n+2} = (ν² - (n+1)²) dₙ`. -/
def struveAs_coeffD (ν : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => -ν
  | n + 2 => (ν ^ 2 - ((n : ℂ) + 1) ^ 2) * struveAs_coeffD ν n

/-- Formula under the stated hypotheses: `(0 : ℂ) ∈ struveAs_dom`. -/
theorem struveAs_zero_mem : (0 : ℂ) ∈ struveAs_dom := by simp [struveAs_dom]

/-- Differentiability throughout the specified domain: `DifferentiableOn ℂ (struveAs_kernel ν)
struveAs_dom`. -/
theorem struveAs_differentiableOn_kernel (ν : ℂ) :
    DifferentiableOn ℂ (struveAs_kernel ν) struveAs_dom :=
  fun _ hs => (struveAs_hasDerivAt_kernel ν hs).differentiableAt.differentiableWithinAt

/-- The function `(struveAs_kernel ν)` is analytic over `ℂ` at `s`. -/
theorem struveAs_analyticAt_kernel (ν : ℂ) {s : ℂ} (hs : s ∈ struveAs_dom) :
    AnalyticAt ℂ (struveAs_kernel ν) s :=
  (struveAs_differentiableOn_kernel ν).analyticAt (struveAs_isOpen_dom.mem_nhds hs)

/-- Identity under the stated parameter and domain assumptions: `deriv (struveAs_kernel ν) =ᶠ[𝓝 s]
struveAs_G1 ν`. -/
theorem struveAs_deriv_kernel_eventually (ν : ℂ) {s : ℂ} (hs : s ∈ struveAs_dom) :
    deriv (struveAs_kernel ν) =ᶠ[𝓝 s] struveAs_G1 ν := by
  filter_upwards [struveAs_isOpen_dom.mem_nhds hs] with x hx
  exact (struveAs_hasDerivAt_kernel ν hx).deriv

/-- Identity under the stated parameter and domain assumptions: `deriv (deriv (struveAs_kernel ν))
s = struveAs_G2 ν s`. -/
theorem struveAs_deriv2_kernel (ν : ℂ) {s : ℂ} (hs : s ∈ struveAs_dom) :
    deriv (deriv (struveAs_kernel ν)) s = struveAs_G2 ν s := by
  rw [(struveAs_deriv_kernel_eventually ν hs).deriv_eq]
  exact (struveAs_hasDerivAt_G1 ν hs).deriv

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv (n + 2)
(struveAs_kernel ν) 0 = (ν ^ 2 - ((n : ℂ) + 1) ^ 2) * iteratedDeriv n (struveAs_kernel ν) 0`. -/
theorem struveAs_iteratedDeriv_add_two (ν : ℂ) (n : ℕ) :
    iteratedDeriv (n + 2) (struveAs_kernel ν) 0 =
      (ν ^ 2 - ((n : ℂ) + 1) ^ 2) * iteratedDeriv n (struveAs_kernel ν) 0 := by
  set f := struveAs_kernel ν with hfdef
  have hA : AnalyticAt ℂ f 0 := struveAs_analyticAt_kernel ν struveAs_zero_mem
  have hA1 : AnalyticAt ℂ (deriv f) 0 := hA.deriv
  have hA2 : AnalyticAt ℂ (deriv (deriv f)) 0 := hA1.deriv
  have hE : (fun s => deriv (deriv f) s + s ^ 2 * deriv (deriv f) s) =ᶠ[𝓝 0]
      (fun s => (-3 : ℂ) * (s ^ 1 * deriv f s) + (ν ^ 2 - 1) * (s ^ 0 * f s)) := by
    filter_upwards [struveAs_isOpen_dom.mem_nhds struveAs_zero_mem] with s hs
    have h := struveAs_ode ν hs
    rw [struveAs_deriv2_kernel ν hs, (struveAs_hasDerivAt_kernel ν hs).deriv]
    linear_combination h
  have h := hE.iteratedDeriv_eq n
  have hp : ∀ m : ℕ, ContDiffAt ℂ n (fun s : ℂ => s ^ m) 0 := fun m => by fun_prop
  rw [iteratedDeriv_fun_add hA2.contDiffAt ((hp 2).mul hA2.contDiffAt),
    iteratedDeriv_fun_add (contDiffAt_const.mul ((hp 1).mul hA1.contDiffAt))
      (contDiffAt_const.mul ((hp 0).mul hA.contDiffAt)),
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
    ODE.iteratedDeriv_pow_mul_zero hA2.contDiffAt, ODE.iteratedDeriv_pow_mul_zero hA1.contDiffAt,
    ODE.iteratedDeriv_pow_mul_zero hA.contDiffAt] at h
  have e2 : iteratedDeriv n (deriv (deriv f)) 0 = iteratedDeriv (n + 2) f 0 := by
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
  rw [e2] at h
  rcases n with _ | _ | k
  · simp at h ⊢; linear_combination h
  · simp at h ⊢; linear_combination h
  · have e3 : iteratedDeriv (k + 1 + 1 - 2) (deriv (deriv f)) 0 =
        iteratedDeriv (k + 1 + 1) f 0 := by
      rw [show k + 1 + 1 - 2 = k by omega, ← iteratedDeriv_succ', ← iteratedDeriv_succ']
    have e4 : iteratedDeriv (k + 1 + 1 - 1) (deriv f) 0 = iteratedDeriv (k + 1 + 1) f 0 := by
      rw [show k + 1 + 1 - 1 = k + 1 by omega, ← iteratedDeriv_succ']
    rw [e3, e4] at h
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero] at h
    push_cast at h ⊢
    linear_combination h

/-- Identity under the stated parameter and domain assumptions: `struveAs_kernel ν 0 = 1`. -/
theorem struveAs_kernel_zero (ν : ℂ) : struveAs_kernel ν 0 = 1 := by simp [struveAs_kernel]

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv n (struveAs_kernel
ν) 0 = struveAs_coeffD ν n`. -/
theorem struveAs_iteratedDeriv_kernel (ν : ℂ) (n : ℕ) :
    iteratedDeriv n (struveAs_kernel ν) 0 = struveAs_coeffD ν n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [struveAs_coeffD, struveAs_kernel_zero]
    | 1, _ =>
      rw [iteratedDeriv_one, (struveAs_hasDerivAt_kernel ν struveAs_zero_mem).deriv]
      simp [struveAs_coeffD, struveAs_G1, struveAs_h, struveAs_q]
    | k + 2, ih =>
      rw [struveAs_iteratedDeriv_add_two, ih k (by omega), struveAs_coeffD]

/-- Taylor expansion of the kernel at the origin. -/
theorem struveAs_kernel_sub_sum_isBigO (ν : ℂ) (N : ℕ) :
    (fun s => struveAs_kernel ν s - ∑ n ∈ Finset.range N, struveAs_coeffD ν n / n ! * s ^ n)
      =O[𝓝 0] fun s => ‖s‖ ^ N := by
  have h := ((struveAs_analyticAt_kernel ν struveAs_zero_mem).hasFPowerSeriesAt
    ).isBigO_sub_partialSum_pow N
  refine h.congr' (Eventually.of_forall fun s => ?_) EventuallyEq.rfl
  simp only [zero_add, FormalMultilinearSeries.partialSum,
    FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, struveAs_iteratedDeriv_kernel]

/-- `‖(s+√(1+s²))^{-ν} (1+s²)^{-1/2}‖ ≤ c^{-1/2} (1+2|s|)^{|re ν|} e^{π |im ν|}` when
`c ≤ |1+s²|`. -/
theorem struveAs_norm_kernel_le (ν : ℂ) {s : ℂ} (hs : s ∈ struveAs_dom) {c : ℝ} (hc : 0 < c)
    (hcs : c ≤ ‖1 + s ^ 2‖) :
    ‖struveAs_kernel ν s‖ ≤ c ^ (-(1 / 2 : ℝ)) * (1 + 2 * ‖s‖) ^ |ν.re| * Real.exp (π * |ν.im|) := by
  set w := (1 + s ^ 2) ^ (1 / 2 : ℂ) with hw
  have hw2 : w ^ 2 = 1 + s ^ 2 := struveAs_cpow_half_sq _
  have hv0 := slitPlane_ne_zero (struveAs_add_sqrt_mem hs)
  rw [← hw] at hv0
  have hwn : ‖w‖ ≤ 1 + ‖s‖ := by
    have h1 : ‖w‖ ^ 2 ≤ (1 + ‖s‖) ^ 2 := by
      rw [← norm_pow, hw2]
      calc ‖1 + s ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖s ^ 2‖ := norm_add_le _ _
        _ = 1 + ‖s‖ ^ 2 := by simp
        _ ≤ _ := by nlinarith [norm_nonneg s]
    nlinarith [norm_nonneg w, norm_nonneg s]
  have hprod : (s + w) * (w - s) = 1 := by linear_combination hw2
  have hvn1 : ‖s + w‖ ≤ 1 + 2 * ‖s‖ := (norm_add_le _ _).trans (by linarith)
  have hvn2 : (1 + 2 * ‖s‖)⁻¹ ≤ ‖s + w‖ := by
    have h1 : ‖s + w‖ * ‖w - s‖ = 1 := by rw [← norm_mul, hprod, norm_one]
    have h2 : ‖w - s‖ ≤ 1 + 2 * ‖s‖ := (norm_sub_le _ _).trans (by linarith)
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    calc (1 : ℝ) = ‖s + w‖ * ‖w - s‖ := h1.symm
      _ ≤ ‖s + w‖ * (1 + 2 * ‖s‖) := by gcongr
  have hvpos : 0 < ‖s + w‖ := norm_pos_iff.mpr hv0
  have hB : 1 ≤ 1 + 2 * ‖s‖ := by linarith [norm_nonneg s]
  have h1 : ‖(s + w) ^ (-ν)‖ ≤ (1 + 2 * ‖s‖) ^ |ν.re| * Real.exp (π * |ν.im|) := by
    refine (DLMF.Confluent.norm_cpow_le_exp _ _).trans ?_
    rw [neg_im, abs_neg, neg_re]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    rcases le_total 0 (-ν.re) with h | h
    · calc ‖s + w‖ ^ (-ν.re) ≤ (1 + 2 * ‖s‖) ^ (-ν.re) := Real.rpow_le_rpow hvpos.le hvn1 h
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hB (by linarith [neg_abs_le ν.re])
    · calc ‖s + w‖ ^ (-ν.re) ≤ ((1 + 2 * ‖s‖)⁻¹) ^ (-ν.re) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hvn2 h
        _ = (1 + 2 * ‖s‖) ^ ν.re := by
            rw [Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), neg_neg]
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hB (le_abs_self _)
  have h2 : ‖(1 + s ^ 2) ^ (-(1 / 2 : ℂ))‖ ≤ c ^ (-(1 / 2 : ℝ)) := by
    refine (DLMF.Confluent.norm_cpow_le_exp _ _).trans ?_
    have : (-(1 / 2 : ℂ)).re = -(1 / 2) := by norm_num
    rw [this, show (-(1 / 2 : ℂ)).im = 0 by simp, abs_zero, mul_zero, Real.exp_zero, mul_one]
    exact Real.rpow_le_rpow_of_nonpos hc hcs (by norm_num)
  rw [struveAs_kernel, norm_mul, ← hw]
  calc ‖(s + w) ^ (-ν)‖ * ‖(1 + s ^ 2) ^ (-(1 / 2 : ℂ))‖
      ≤ ((1 + 2 * ‖s‖) ^ |ν.re| * Real.exp (π * |ν.im|)) * c ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Points `r e^{iy}`, `|y| < π/2`, lie in the domain. -/
theorem struveAs_ray_mem {r y : ℝ} (hy : |y| < π / 2) : (r : ℂ) * exp (y * I) ∈ struveAs_dom := by
  change 1 + ((r : ℂ) * exp (y * I)) ^ 2 ∈ slitPlane
  rw [Complex.ofReal_mul_exp_ofReal_mul_I_sq, mem_slitPlane_iff, add_re, add_im, re_ofReal_mul,
    im_ofReal_mul, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im]
  simp only [one_re, one_im, zero_add]
  by_cases hs : Real.sin (2 * y) = 0
  · left
    have h0 : 2 * y = 0 := by
      rw [Real.sin_eq_zero_iff_of_lt_of_lt] at hs
      · exact hs
      · linarith [neg_abs_le y]
      · linarith [le_abs_self y]
    rw [h0, Real.cos_zero]; positivity
  · rcases eq_or_ne r 0 with h | h
    · left; simp [h]
    · right; exact mul_ne_zero (by positivity) hs

/-- Uniform bound for the kernel on the rays `r e^{iy}`, `|y| ≤ |α| < π/2`, uniformly for
`|re μ| ≤ a`, `|im μ| ≤ b`. -/
theorem struveAs_exists_ray_bound {α : ℝ} (hα : |α| < π / 2) (a b : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ μ : ℂ, |μ.re| ≤ a → |μ.im| ≤ b → ∀ r : ℝ, 0 ≤ r → ∀ y : ℝ, |y| ≤ |α| →
      ‖struveAs_kernel μ ((r : ℂ) * exp (y * I))‖ ≤ C * (1 + 2 * r) ^ a := by
  obtain ⟨c, hc, hcb⟩ := Complex.exists_pos_le_norm_one_add_ofReal_mul_exp
    (Φ := 2 * |α|) (by linarith)
  refine ⟨c ^ (-(1 / 2 : ℝ)) * Real.exp (π * b), by positivity, fun μ hμa hμb r hr y hy => ?_⟩
  have hmem := struveAs_ray_mem (r := r) (lt_of_le_of_lt hy hα)
  have hcs : c ≤ ‖1 + ((r : ℂ) * exp (y * I)) ^ 2‖ := by
    rw [Complex.ofReal_mul_exp_ofReal_mul_I_sq]
    exact hcb _ (by positivity) _ (by rw [abs_mul, abs_two]; linarith)
  refine (struveAs_norm_kernel_le μ hmem hc hcs).trans ?_
  rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hr, norm_exp_ofReal_mul_I, mul_one]
  have h1 : (1 + 2 * r) ^ |μ.re| ≤ (1 + 2 * r) ^ a :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hμa
  have h2 : Real.exp (π * |μ.im|) ≤ Real.exp (π * b) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hμb Real.pi_pos.le)
  calc c ^ (-(1 / 2 : ℝ)) * (1 + 2 * r) ^ |μ.re| * Real.exp (π * |μ.im|)
      ≤ c ^ (-(1 / 2 : ℝ)) * (1 + 2 * r) ^ a * Real.exp (π * b) := by gcongr
    _ = _ := by ring

/-- `(1 + 2r)^a ≤ 3^a r^a + 3^a` for `r ≥ 0`, `a ≥ 0`. -/
theorem struveAs_one_add_two_mul_rpow_le {a r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) :
    (1 + 2 * r) ^ a ≤ 3 ^ a * r ^ a + 3 ^ a := by
  rcases le_total r 1 with h | h
  · have : (1 + 2 * r) ^ a ≤ 3 ^ a := Real.rpow_le_rpow (by linarith) (by linarith) ha
    nlinarith [Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) a, Real.rpow_nonneg hr a]
  · have : (1 + 2 * r) ^ a ≤ (3 * r) ^ a := Real.rpow_le_rpow (by linarith) (by linarith) ha
    rw [Real.mul_rpow (by norm_num) hr] at this
    nlinarith [Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) a]

/-- On the real axis, `A(sinh t) cosh t = e^{-νt}`. -/
theorem struveAs_kernel_sinh (ν : ℂ) (t : ℝ) :
    struveAs_kernel ν (Real.sinh t) * Real.cosh t = exp (-ν * t) := by
  have hc := Real.cosh_pos t
  have h1 : (1 + (Real.sinh t : ℂ) ^ 2) = ((Real.cosh t ^ 2 : ℝ) : ℂ) := by
    rw [Real.cosh_sq t]; push_cast; ring
  have h2 : ((Real.cosh t ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = Real.cosh t := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq hc.le]
  have h3 : ((Real.cosh t ^ 2 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) = (Real.cosh t : ℂ)⁻¹ := by
    rw [cpow_neg, h2]
  have h4 : (Real.sinh t : ℂ) + Real.cosh t = exp t := by
    rw [← ofReal_add, Real.sinh_add_cosh, ofReal_exp]
  rw [struveAs_kernel, h1, h2, h3, h4, cpow_def_of_ne_zero (exp_ne_zero _),
    log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]
  have hc' : (Real.cosh t : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
  field_simp

/-- The substitution `s = sinh t` in the Laplace integral of `A_ν`. -/
theorem struveAs_integral_sinh (ν z : ℂ) :
    ∫ s in Ioi (0 : ℝ), exp (-(z * s)) * struveAs_kernel ν s =
      ∫ t in Ioi (0 : ℝ), exp (-ν * t - z * Real.sinh t) := by
  have himg : Real.sinh '' Ioi 0 = Ioi 0 := by
    simpa using OrderIso.image_Ioi Real.sinhOrderIso 0
  have h := integral_image_eq_integral_abs_deriv_smul (f := Real.sinh) (f' := Real.cosh)
    (measurableSet_Ioi (a := (0:ℝ))) (fun x _ => (Real.hasDerivAt_sinh x).hasDerivWithinAt)
    Real.sinh_injective.injOn (fun s : ℝ => exp (-(z * s)) * struveAs_kernel ν s)
  rw [himg] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [abs_of_pos (Real.cosh_pos t), real_smul, mul_left_comm, mul_comm (Real.cosh t : ℂ),
    struveAs_kernel_sinh, ← exp_add]
  ring_nf

/-- Exponential damping of a polynomially bounded continuous function is integrable. -/
theorem struveAs_integrableOn {G : ℝ → ℂ} {c C a : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hG : ContinuousOn G (Ioi 0)) (hb : ∀ r : ℝ, 0 < r → ‖G r‖ ≤ C * (1 + 2 * r) ^ a) :
    IntegrableOn (fun r : ℝ => Real.exp (-c * r) • G r) (Ioi 0) := by
  have hmaj := ((integrableOn_exp_neg_mul_mul_rpow_sub_one (s := a + 1) (by linarith) hc
    ).const_mul (C * 3 ^ a)).add ((exp_neg_integrableOn_Ioi 0 hc).const_mul (C * 3 ^ a))
  refine hmaj.mono' (((by fun_prop : Continuous fun t : ℝ => Real.exp (-c * t)
    ).continuousOn.smul hG).aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht : (0 : ℝ) < t := ht
  rw [norm_smul, Real.norm_eq_abs, Real.abs_exp, add_sub_cancel_right]
  calc Real.exp (-c * t) * ‖G t‖ ≤ Real.exp (-c * t) * (C * (3 ^ a * t ^ a + 3 ^ a)) :=
        mul_le_mul_of_nonneg_left ((hb t ht).trans (mul_le_mul_of_nonneg_left
          (struveAs_one_add_two_mul_rpow_le ha ht.le) hC)) (Real.exp_pos _).le
    _ = _ := by simp only [Pi.add_apply]; ring

/-- Continuity of the kernel along a ray. -/
theorem struveAs_continuous_ray (ν : ℂ) {θ : ℝ} (hθ : |θ| < π / 2) :
    Continuous fun r : ℝ => struveAs_kernel ν ((r : ℂ) * exp (θ * I)) :=
  continuous_iff_continuousAt.2 fun r =>
    ContinuousAt.comp (g := struveAs_kernel ν) (f := fun r : ℝ => (r : ℂ) * exp (θ * I)) (x := r)
      ((struveAs_differentiableOn_kernel ν).differentiableAt (struveAs_isOpen_dom.mem_nhds
        (struveAs_ray_mem hθ))).continuousAt
      (by fun_prop : Continuous fun r : ℝ => (r : ℂ) * exp (θ * I)).continuousAt

/-- Estimate under the stated parameter and domain assumptions: `∃ C, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → ∀ y
: ℝ, |y| ≤ |θ| → ‖struveAs_kernel ν ((r : ℂ) * exp (y * I))‖ ≤ C * (1 + 2 * r) ^ |ν.re|`. -/
theorem struveAs_ray_bound' (ν : ℂ) {θ : ℝ} (hθ : |θ| < π / 2) :
    ∃ C, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → ∀ y : ℝ, |y| ≤ |θ| →
      ‖struveAs_kernel ν ((r : ℂ) * exp (y * I))‖ ≤ C * (1 + 2 * r) ^ |ν.re| := by
  obtain ⟨C, hC, h⟩ := struveAs_exists_ray_bound hθ |ν.re| |ν.im|
  exact ⟨C, hC, fun r hr y hy => h ν le_rfl le_rfl r hr y hy⟩

/-- Integrability of the damped kernel along a ray. -/
theorem struveAs_integrableOn_ray (ν : ℂ) {θ c : ℝ} (hθ : |θ| < π / 2) (hc : 0 < c) :
    IntegrableOn (fun r : ℝ => Real.exp (-c * r) • struveAs_kernel ν ((r : ℂ) * exp (θ * I)))
      (Ioi 0) := by
  obtain ⟨C, hC, h⟩ := struveAs_ray_bound' ν hθ
  exact struveAs_integrableOn hc hC (abs_nonneg _) (struveAs_continuous_ray ν hθ).continuousOn
    fun r hr => h r hr.le θ le_rfl

/-- Integrability of the Laplace integrand on the real axis. -/
theorem struveAs_integrableOn_real (ν : ℂ) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun s : ℝ => exp (-(z * s)) * struveAs_kernel ν s) (Ioi 0) := by
  have h := struveAs_integrableOn_ray ν (θ := 0) (by simp [Real.pi_pos]) hz
  have h2 := integrableOn_cexp_neg_mul_smul_of_le h le_rfl
  simpa using h2

/-- `A_ν(z) = π⁻¹ ∫₀^∞ e^{-zs} (s+√(1+s²))^{-ν} (1+s²)^{-1/2} ds` for `re z > 0`. -/
theorem struveAs_angerA_eq_integral (ν : ℂ) {z : ℂ} (hz : 0 < z.re) :
    angerA ν z = 1 / π * ∫ s in Ioi (0 : ℝ), exp (-(z * s)) * struveAs_kernel ν s := by
  have himg : Real.sinh '' Ioi 0 = Ioi 0 := by
    simpa using OrderIso.image_Ioi Real.sinhOrderIso 0
  have hI := struveAs_integrableOn_real ν hz
  rw [← himg] at hI
  rw [integrableOn_image_iff_integrableOn_abs_deriv_smul (f := Real.sinh) (f' := Real.cosh)
    (measurableSet_Ioi (a := (0 : ℝ))) (fun x _ => (Real.hasDerivAt_sinh x).hasDerivWithinAt)
    Real.sinh_injective.injOn] at hI
  have hI' : IntegrableOn (fun t : ℝ => exp (-ν * t - z * Real.sinh t) / π) (Ioi 0) := by
    refine IntegrableOn.congr_fun (Integrable.div_const hI (π : ℂ)) (fun t _ => ?_)
      measurableSet_Ioi
    rw [abs_of_pos (Real.cosh_pos t), real_smul, mul_left_comm, mul_comm (Real.cosh t : ℂ),
      struveAs_kernel_sinh, ← exp_add]
    ring_nf
  have hlim := intervalIntegral_tendsto_integral_Ioi 0 hI' tendsto_id
  have hA := angerA_integral ν hz
  rw [DLMF.HasIntegralAtTop] at hA
  rw [tendsto_nhds_unique hA hlim, struveAs_integral_sinh, integral_div]
  ring

/-- The Laplace integral of the kernel along the ray `arg s = θ`. -/
def struveAs_rotInt (ν : ℂ) (θ : ℝ) (z : ℂ) : ℂ :=
  ∫ r in Ioi (0 : ℝ), exp (-(z * exp (θ * I) * r)) * struveAs_kernel ν (r * exp (θ * I))

/-- Rotation of the ray of integration. -/
theorem struveAs_integral_eq_rot (ν : ℂ) {θ : ℝ} (hθ : |θ| < π / 2) {z : ℂ} (hz : 0 < z.re)
    (hzθ : 0 < (z * exp (θ * I)).re) :
    ∫ s in Ioi (0 : ℝ), exp (-(z * s)) * struveAs_kernel ν s =
      exp (θ * I) * struveAs_rotInt ν θ z := by
  obtain ⟨C, hC, h⟩ := struveAs_ray_bound' ν hθ
  set a := |ν.re|
  have ha : 0 ≤ a := abs_nonneg _
  have h3 : (0 : ℝ) ≤ 3 ^ a := by positivity
  refine integral_cexp_neg_mul_mul_eq_rotate (σ := 1) (C := C * 3 ^ a) (k := a) one_pos
    (fun r _ y hy => (struveAs_differentiableOn_kernel ν).differentiableAt
      (struveAs_isOpen_dom.mem_nhds (struveAs_ray_mem
        (lt_of_le_of_lt (abs_le_abs_of_mem_uIcc_zero hy) hθ))))
    (fun r hr hr1 y hy => ?_) (fun r hr y hy => ?_)
    (fun y hy => Complex.re_mul_exp_pos_of_mem_uIcc hθ hz hzθ hy)
  · refine (h r hr.le y (abs_le_abs_of_mem_uIcc_zero hy)).trans ?_
    rw [sub_self, Real.rpow_zero, mul_one]
    gcongr
    linarith
  · refine (h r (by linarith) y (abs_le_abs_of_mem_uIcc_zero hy)).trans ?_
    rw [mul_assoc]
    gcongr
    rw [← Real.mul_rpow (by norm_num) (by linarith)]
    exact Real.rpow_le_rpow (by linarith) (by linarith) ha

/-- The rotated integral is holomorphic on the half-plane `re (z e^{iθ}) > 0`. -/
theorem struveAs_differentiableOn_rotInt (ν : ℂ) {θ : ℝ} (hθ : |θ| < π / 2) :
    DifferentiableOn ℂ (struveAs_rotInt ν θ) {z : ℂ | 0 < (z * exp (θ * I)).re} := by
  obtain ⟨C, hC, h⟩ := struveAs_ray_bound' ν hθ
  set a := |ν.re|
  have ha : 0 ≤ a := abs_nonneg _
  have hL := differentiableOn_integral_cexp_neg_mul_smul_of_le_rpow
    (G := fun r : ℝ => struveAs_kernel ν ((r : ℂ) * exp (θ * I))) (C := C * 3 ^ a)
    (D := C * 3 ^ a) (k := a) (by linarith) (struveAs_continuous_ray ν hθ).continuousOn
    (fun r hr => (h r hr.le θ le_rfl).trans (by
      have := struveAs_one_add_two_mul_rpow_le ha hr.le
      nlinarith))
  have hcomp := hL.comp (f := fun z : ℂ => z * exp (θ * I))
    (s := {z : ℂ | 0 < (z * exp (θ * I)).re})
    ((differentiable_id.mul_const _).differentiableOn) (fun z hz => hz)
  refine hcomp.congr fun z _ => ?_
  simp only [Function.comp_apply, struveAs_rotInt, smul_eq_mul]

/-- The rotated integral is continuous in the order. -/
theorem struveAs_continuousAt_rotInt_order {θ : ℝ} (hθ : |θ| < π / 2) {z : ℂ}
    (hz : 0 < (z * exp (θ * I)).re) (ν : ℂ) :
    ContinuousAt (fun μ => struveAs_rotInt μ θ z) ν := by
  set a := |ν.re| + 1
  set κ := (z * exp (θ * I)).re
  obtain ⟨C, hC, h⟩ := struveAs_exists_ray_bound hθ a (|ν.im| + 1)
  have ha : 0 ≤ a := by positivity
  set bound : ℝ → ℝ := fun r => ‖Real.exp (-κ * r) • ((C * (1 + 2 * r) ^ a : ℝ) : ℂ)‖
  have hbi : Integrable bound (volume.restrict (Ioi 0)) := by
    have := struveAs_integrableOn (G := fun r : ℝ => ((C * (1 + 2 * r) ^ a : ℝ) : ℂ)) hz hC ha
      (by fun_prop) (fun r hr => by
        rw [norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg hC (Real.rpow_nonneg (by linarith) _))])
    exact this.norm
  unfold struveAs_rotInt
  refine continuousAt_of_dominated (bound := bound) ?_ ?_ hbi ?_
  · refine Eventually.of_forall fun μ => ?_
    exact ((by fun_prop : Continuous fun r : ℝ => exp (-(z * exp (θ * I) * r))).mul
      (struveAs_continuous_ray μ hθ)).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds ν one_pos] with μ hμ
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
    have hr : (0 : ℝ) < r := hr
    rw [Metric.mem_ball, dist_eq_norm] at hμ
    have h1 : |μ.re| ≤ a := by
      have := abs_re_le_norm (μ - ν); rw [sub_re] at this
      have := abs_sub_abs_le_abs_sub μ.re ν.re
      simp only [a]; linarith
    have h2 : |μ.im| ≤ |ν.im| + 1 := by
      have := abs_im_le_norm (μ - ν); rw [sub_im] at this
      have := abs_sub_abs_le_abs_sub μ.im ν.im
      linarith
    rw [norm_mul, Complex.norm_exp]
    simp only [bound, norm_smul, norm_real, Real.norm_eq_abs, Real.abs_exp]
    rw [abs_of_nonneg (mul_nonneg hC (Real.rpow_nonneg (by linarith) _))]
    refine mul_le_mul (Real.exp_le_exp.mpr (le_of_eq ?_)) (h μ h1 h2 r hr.le θ le_rfl)
      (norm_nonneg _) (Real.exp_pos _).le
    rw [neg_re, show z * exp (θ * I) * r = (r : ℂ) * (z * exp (θ * I)) by ring, re_ofReal_mul]
    ring
  · refine Eventually.of_forall fun r => ?_
    have hv := slitPlane_ne_zero (struveAs_add_sqrt_mem (struveAs_ray_mem (r := r) hθ))
    refine continuousAt_const.mul ?_
    unfold struveAs_kernel
    refine ContinuousAt.mul ?_ continuousAt_const
    exact (continuous_neg.const_cpow (Or.inl hv)).continuousAt

/-- Estimate under the stated parameter and domain assumptions: `{z : ℂ | 0 < (z * exp (θ *
I)).re} ⊆ slitPlane`. -/
theorem struveAs_halfPlane_subset {θ : ℝ} (hθ : |θ| < π / 2) :
    {z : ℂ | 0 < (z * exp (θ * I)).re} ⊆ slitPlane := by
  intro w hw
  change 0 < (w * exp (θ * I)).re at hw
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [neg_abs_le θ], by linarith [le_abs_self θ]⟩
  by_contra h
  rw [mem_slitPlane_iff, not_or] at h
  push Not at h
  have hw' : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [h.2])
  rw [hw', re_ofReal_mul, exp_ofReal_mul_I_re] at hw
  nlinarith [h.1]

/-- The rotated representation of `A_ν`, at nonintegral order. -/
theorem struveAs_angerA_eq_rot_of_not_int {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) {θ : ℝ}
    (hθ : |θ| < π / 2) {z : ℂ} (hz : 0 < (z * exp (θ * I)).re) :
    angerA ν z = 1 / π * (exp (θ * I) * struveAs_rotInt ν θ z) := by
  set H : Set ℂ := {z : ℂ | 0 < (z * exp (θ * I)).re} with hH
  have hHo : IsOpen H := isOpen_lt continuous_const (by fun_prop)
  have hHc : Convex ℝ H := by
    intro z₁ hz₁ z₂ hz₂ s t hs ht hst
    change 0 < ((s • z₁ + t • z₂) * exp (θ * I)).re
    change 0 < (z₁ * exp (θ * I)).re at hz₁
    change 0 < (z₂ * exp (θ * I)).re at hz₂
    rw [add_mul, add_re, smul_mul_assoc, smul_mul_assoc, Complex.smul_re, Complex.smul_re,
      smul_eq_mul, smul_eq_mul]
    rcases eq_or_lt_of_le hs with h | h
    · subst h; simp at hst; subst hst; simpa using hz₂
    · nlinarith [mul_pos h hz₁, mul_nonneg ht hz₂.le]
  have hHs := struveAs_halfPlane_subset hθ
  have hs := sin_pi_mul_ne_zero_of_not_int hν
  have hU : AnalyticOnNhd ℂ (fun z => angerARegular ν z) H := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hHo
    unfold angerARegular
    exact ((((angerJ_entire ν) w).sub
      (DLMF.Bessel.hasDerivAt_besselJ (ν := ν) (hHs hw)).differentiableAt).div_const
      _).differentiableWithinAt
  have hV : AnalyticOnNhd ℂ (fun z => 1 / π * (exp (θ * I) * struveAs_rotInt ν θ z)) H :=
    (((struveAs_differentiableOn_rotInt ν hθ).const_mul _).const_mul _).analyticOnNhd hHo
  set zs : ℂ := exp ((-(θ / 2) : ℝ) * I) with hzs
  have hzs0 : 0 < zs.re := by
    rw [hzs, exp_ofReal_mul_I_re, Real.cos_neg]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le θ, Real.pi_pos],
      by linarith [le_abs_self θ, Real.pi_pos]⟩
  have hzsH : 0 < (zs * exp (θ * I)).re := by
    rw [hzs, ← exp_add, show ((-(θ / 2) : ℝ) : ℂ) * I + θ * I = ((θ / 2 : ℝ) : ℂ) * I by
      push_cast; ring, exp_ofReal_mul_I_re]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le θ, Real.pi_pos],
      by linarith [le_abs_self θ, Real.pi_pos]⟩
  have hev : (fun z => angerARegular ν z) =ᶠ[𝓝 zs]
      fun z => 1 / π * (exp (θ * I) * struveAs_rotInt ν θ z) := by
    have hopen : IsOpen {w : ℂ | 0 < w.re ∧ 0 < (w * exp (θ * I)).re} :=
      (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_const
        (by fun_prop : Continuous fun w : ℂ => (w * exp (θ * I)).re))
    filter_upwards [hopen.mem_nhds ⟨hzs0, hzsH⟩] with w hw
    rw [← angerA_regular hν (Or.inl hw.1), struveAs_angerA_eq_integral ν hw.1,
      struveAs_integral_eq_rot ν hθ hw.1 hw.2]
  rw [angerA_regular hν (hHs hz)]
  exact hU.eqOn_of_preconnected_of_eventuallyEq hV hHc.isPreconnected hzsH hev hz

/-- **Rotated Laplace representation of `A_ν`**: for `|θ| < π/2` and `re (z e^{iθ}) > 0`,
`A_ν(z) = π⁻¹ e^{iθ} ∫₀^∞ e^{-z e^{iθ} r} K_ν(r e^{iθ}) dr`. -/
theorem struveAs_angerA_eq_rot (ν : ℂ) {θ : ℝ} (hθ : |θ| < π / 2) {z : ℂ}
    (hz : 0 < (z * exp (θ * I)).re) :
    angerA ν z = 1 / π * (exp (θ * I) * struveAs_rotInt ν θ z) := by
  have hzs := struveAs_halfPlane_subset hθ hz
  refine DLMF.Confluent.eq_of_continuousAt_of_integerComplement (f := fun μ => angerA μ z)
    (g := fun μ => 1 / π * (exp (θ * I) * struveAs_rotInt μ θ z))
    (continuousAt_angerA_order ν hzs)
    (continuousAt_const.mul (continuousAt_const.mul
      (struveAs_continuousAt_rotInt_order hθ hz ν))) fun c hc => ?_
  exact struveAs_angerA_eq_rot_of_not_int (DLMF.Confluent.forall_of_mem_integerComplement hc) hθ hz

/-- Taylor remainder of the kernel along a ray, in the form required by Watson's lemma. -/
theorem struveAs_kernel_ray_isBigO (ν : ℂ) (θ : ℝ) (N : ℕ) :
    (fun r : ℝ => struveAs_kernel ν ((r : ℂ) * exp (θ * I)) -
        ∑ n ∈ Finset.range N, (((r : ℂ) * exp (θ * I)) ^ ((n : ℂ) + 1 - 1)) •
          (struveAs_coeffD ν n / n !))
      =O[𝓝[>] 0] fun r : ℝ => r ^ ((N : ℝ) + (1 : ℂ).re - 1) := by
  have ht : Tendsto (fun r : ℝ => (r : ℂ) * exp (θ * I)) (𝓝[>] 0) (𝓝 0) := by
    have : Continuous fun r : ℝ => (r : ℂ) * exp (θ * I) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  refine ((struveAs_kernel_sub_sum_isBigO ν N).comp_tendsto ht).congr' ?_ ?_
  · refine Eventually.of_forall fun r => ?_
    simp only [Function.comp_apply, add_sub_cancel_right, cpow_natCast, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun n _ => by ring
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have hr : (0 : ℝ) < r := hr
    simp only [Function.comp_apply, one_re, add_sub_cancel_right, Real.rpow_natCast]
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hr, norm_exp_ofReal_mul_I, mul_one]

/-- **Watson's lemma for `A_ν`** in a rotated sector: as `z → ∞` with
`δ |z| ≤ re (z e^{iθ})`, `|θ| < π/2`, `A_ν(z) ~ π⁻¹ ∑ dₙ z^{-n-1}`. -/
theorem struveAs_angerA_hasAsymptoticExpansion (ν : ℂ) {δ θ : ℝ} (hδ : 0 < δ)
    (hθ : |θ| < π / 2) :
    HasAsymptoticExpansion (DLMF.Confluent.rotSectorAtTop δ θ)
      (fun (n : ℕ) (z : ℂ) => z ^ (-((n : ℂ) + 1)))
      (fun n => struveAs_coeffD ν n / π) (angerA ν) := by
  have hW := hasAsymptoticExpansion_integral_cexp_smul_rotate_comap
    (F := struveAs_kernel ν) (a := fun n => struveAs_coeffD ν n / n !) (μ := 1) (c := 1)
    hθ (by simp) hδ (struveAs_integrableOn_ray ν hθ one_pos) (struveAs_kernel_ray_isBigO ν θ)
  have hW' := hW.const_smul (1 / π : ℂ)
  refine (hW'.congr' ?_).congr_coeff ?_
  · filter_upwards [DLMF.Confluent.eventually_rotSectorAtTop hδ hθ] with z hz
    rw [struveAs_angerA_eq_rot ν hθ hz.2.1, struveAs_rotInt]
    simp only [Pi.smul_apply, smul_eq_mul]
  · funext n
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Complex.Gamma_nat_eq_factorial]
    have : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    field_simp

end DLMF.Struve
