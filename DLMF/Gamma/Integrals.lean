/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.Polygamma
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import DLMF.Gamma.RecipGammaDeriv

/-!
# Mellin–Barnes and related integrals; sums (DLMF §§5.13, 5.16)

Vertical-line integrals are acquired with a real parameter `t` in place of the
source's `c±i∞` contour, on the indicated real-part strips. The inversion
contour 5.13.1 is restricted to positive real `z`. Parametrizing `s = σ + it`
converts the factor `1/(2πi) ds` into `1/(2π) dt`.
The alternating trigamma sum 5.16.1 has closed-form partial sums, and its limit
uses the odd part of `ζ(2)`.
-/

@[expose] public section

open Complex MeasureTheory Filter
open scoped Real Topology ComplexConjugate

noncomputable section

namespace DLMF.Gamma

@[dlmf 5.13.E1]
theorem mellin_barnes_beta {a b : ℂ} {x σ : ℝ}
    (hx : 0 < x) (hab : 0 < (a + b).re) (hσa : -a.re < σ) (hσb : σ < b.re) :
    (1 / (2 * π)) * ∫ t : ℝ,
        Complex.Gamma (σ + I * t + a) * Complex.Gamma (b - (σ + I * t)) *
          (x : ℂ) ^ (-(σ + I * t)) =
      Complex.Gamma (a + b) * (x : ℂ) ^ a / (1 + (x : ℂ)) ^ (a + b) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have h := Gamma_mul_one_add_cpow_neg (a := a + b) (σ := σ + a.re) (by linarith)
    (by simp only [add_re]; linarith) hx
  have htr := integral_add_right_eq_self (μ := volume) (fun y : ℝ =>
    Complex.Gamma (((σ + a.re : ℝ) : ℂ) + y * I) *
      Complex.Gamma (a + b - (((σ + a.re : ℝ) : ℂ) + y * I)) *
      (x : ℂ) ^ (-(((σ + a.re : ℝ) : ℂ) + y * I))) a.im
  rw [← htr] at h
  have hpt : ∀ t : ℝ, Complex.Gamma (((σ + a.re : ℝ) : ℂ) + ((t + a.im : ℝ) : ℂ) * I) *
      Complex.Gamma (a + b - (((σ + a.re : ℝ) : ℂ) + ((t + a.im : ℝ) : ℂ) * I)) *
      (x : ℂ) ^ (-(((σ + a.re : ℝ) : ℂ) + ((t + a.im : ℝ) : ℂ) * I)) =
      (x : ℂ) ^ (-a) * (Complex.Gamma (σ + I * t + a) * Complex.Gamma (b - (σ + I * t)) *
        (x : ℂ) ^ (-(σ + I * t))) := by
    intro t
    have e : ((σ + a.re : ℝ) : ℂ) + ((t + a.im : ℝ) : ℂ) * I = σ + I * t + a := by
      apply Complex.ext <;> simp
    rw [e, show a + b - (σ + I * t + a) = b - (σ + I * t) by ring,
      show -((σ : ℂ) + I * t + a) = -a + -(σ + I * t) by ring, cpow_add _ _ hx0]
    ring
  simp only [hpt] at h
  rw [integral_const_mul] at h
  have hxa : (x : ℂ) ^ a * (x : ℂ) ^ (-a) = 1 := by
    rw [← cpow_add _ _ hx0, add_neg_cancel, cpow_zero]
  have h1 : ((1 + x : ℝ) : ℂ) = 1 + (x : ℂ) := by push_cast; ring
  rw [h1, cpow_neg] at h
  generalize (∫ t : ℝ, Complex.Gamma (σ + I * t + a) * Complex.Gamma (b - (σ + I * t)) *
    (x : ℂ) ^ (-(σ + I * t))) = J at h ⊢
  linear_combination (-(x : ℂ) ^ a) * h - (1 / (2 * π) * J) * hxa

/-! ### The integral 5.13.2

With `s = 2t`, `mellin_barnes_beta` at `σ = 0`, `a = b = α` and `x = v⁻²` reads
`∫ Γ(α + is/2) Γ(α - is/2) v^{is} ds = 4π Γ(2α) (v + 1/v)^{-2α}` for `v > 0`. Both sides are
holomorphic for `re v > 0`, and 5.13.2 is the value at `v = e^{i(π/2 - b)}`. -/
/-- `Γ(α + is/2) Γ(α - is/2)`, the integrand of 5.13.2 in the variable `s = 2t`. -/
def normSqHalfB (α : ℝ) (s : ℝ) : ℂ :=
  Complex.Gamma (α + I * ((s : ℂ) / 2)) * Complex.Gamma (α - I * ((s : ℂ) / 2))

theorem continuous_normSqHalfB {α : ℝ} (hα : 0 < α) : Continuous (normSqHalfB α) := by
  refine continuous_iff_continuousAt.2 fun s => ?_
  have h1 : ContinuousAt Complex.Gamma ((α : ℂ) + I * ((s : ℂ) / 2)) :=
    continuousAt_Gamma_of_re_pos (by simpa using hα)
  have h2 : ContinuousAt Complex.Gamma ((α : ℂ) - I * ((s : ℂ) / 2)) :=
    continuousAt_Gamma_of_re_pos (by simpa using hα)
  exact (h1.comp (f := fun s : ℝ => (α : ℂ) + I * ((s : ℂ) / 2)) (by fun_prop)).mul
    (h2.comp (f := fun s : ℝ => (α : ℂ) - I * ((s : ℂ) / 2)) (by fun_prop))

theorem exists_norm_normSqHalfB_le {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, ∃ K : ℕ, ∀ s : ℝ,
      ‖normSqHalfB α s‖ ≤ C * (1 + |s|) ^ K * Real.exp (-(π * |s|) / 2) := by
  obtain ⟨C, K, hC⟩ := exists_norm_Gamma_le hα
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 0); simpa using this
  refine ⟨C * C, 2 * K, fun s => ?_⟩
  have h1 := hC (s / 2)
  have h2 := hC (-(s / 2))
  have e1 : (α : ℂ) + I * ((s : ℂ) / 2) = α + I * ((s / 2 : ℝ) : ℂ) := by push_cast; ring
  have e2 : (α : ℂ) - I * ((s : ℂ) / 2) = α + I * ((-(s / 2) : ℝ) : ℂ) := by push_cast; ring
  have hs2 : |s / 2| = |s| / 2 := by rw [abs_div, abs_two]
  rw [abs_neg] at h2
  rw [normSqHalfB, norm_mul, e1, e2]
  calc _ ≤ (C * (1 + |s / 2|) ^ K * Real.exp (-(π * |s / 2|) / 2)) *
        (C * (1 + |s / 2|) ^ K * Real.exp (-(π * |s / 2|) / 2)) :=
      mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = C * C * (1 + |s| / 2) ^ (2 * K) *
        Real.exp (-(π * (|s| / 2)) / 2 + -(π * (|s| / 2)) / 2) := by
      rw [hs2, Real.exp_add]; ring
    _ ≤ C * C * (1 + |s|) ^ (2 * K) * Real.exp (-(π * |s|) / 2) := by
      rw [show -(π * (|s| / 2)) / 2 + -(π * (|s| / 2)) / 2 = -(π * |s|) / 2 by ring]
      gcongr
      linarith [abs_nonneg s]

/-- The real-variable form of 5.13.2 before continuation: for `v > 0`,
`∫ B(s) v^{is} ds = 4π Γ(2α) (v + 1/v)^{-2α}`. -/
theorem integral_normSqHalfB_ofReal {α : ℝ} (hα : 0 < α) {v : ℝ} (hv : 0 < v) :
    ∫ s : ℝ, normSqHalfB α s * (v : ℂ) ^ (((0 : ℝ) : ℂ) + I * s) =
      4 * π * Complex.Gamma (2 * α) * ((v : ℂ) + (v : ℂ)⁻¹) ^ (-(2 * α : ℂ)) := by
  set x : ℝ := (v ^ 2)⁻¹ with hxdef
  have hx : 0 < x := by positivity
  have h := mellin_barnes_beta (a := (α : ℂ)) (b := (α : ℂ)) (σ := 0) hx
    (by simp; linarith) (by simpa using hα) (by simpa using hα)
  have hv0 : (v : ℂ) ≠ 0 := ofReal_ne_zero.2 hv.ne'
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
  -- substitute `s = 2t`
  have hsub := Measure.integral_comp_mul_left
    (fun s : ℝ => normSqHalfB α s * (v : ℂ) ^ (((0 : ℝ) : ℂ) + I * s)) 2
  have hpt : ∀ t : ℝ, normSqHalfB α (2 * t) * (v : ℂ) ^ (((0 : ℝ) : ℂ) + I * ((2 * t : ℝ) : ℂ)) =
      Complex.Gamma (((0 : ℝ) : ℂ) + I * t + α) * Complex.Gamma (α - (((0 : ℝ) : ℂ) + I * t)) *
        (x : ℂ) ^ (-(((0 : ℝ) : ℂ) + I * t)) := by
    intro t
    have e1 : (α : ℂ) + I * (((2 * t : ℝ) : ℂ) / 2) = ((0 : ℝ) : ℂ) + I * t + α := by
      push_cast; ring
    have e2 : (α : ℂ) - I * (((2 * t : ℝ) : ℂ) / 2) = α - (((0 : ℝ) : ℂ) + I * t) := by
      push_cast; ring
    have e3 : (v : ℂ) ^ (((0 : ℝ) : ℂ) + I * ((2 * t : ℝ) : ℂ)) =
        (x : ℂ) ^ (-(((0 : ℝ) : ℂ) + I * t)) := by
      rw [cpow_def_of_ne_zero hv0, cpow_def_of_ne_zero hx0, ← ofReal_log hv.le,
        ← ofReal_log hx.le, hxdef, Real.log_inv, Real.log_pow]
      congr 1
      push_cast; ring
    rw [normSqHalfB, e1, e2, e3]
  simp only [hpt] at hsub
  have hJ : ∫ s : ℝ, normSqHalfB α s * (v : ℂ) ^ (((0 : ℝ) : ℂ) + I * s) =
      2 * ∫ t : ℝ, Complex.Gamma (((0 : ℝ) : ℂ) + I * t + α) *
        Complex.Gamma (α - (((0 : ℝ) : ℂ) + I * t)) * (x : ℂ) ^ (-(((0 : ℝ) : ℂ) + I * t)) := by
    rw [hsub, Complex.real_smul, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
    push_cast; ring
  -- the real identity `x^α / (1+x)^{2α} = (v + 1/v)^{-2α}`
  have hreal : x ^ α / (1 + x) ^ (α + α) = (v + v⁻¹) ^ (-(2 * α)) := by
    have hvx : v + v⁻¹ = v * (1 + x) := by rw [hxdef]; field_simp
    have hxa : x ^ α = v ^ (-(2 * α)) := by
      rw [hxdef, Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hv.le,
        Real.rpow_neg hv.le]
      norm_num
    rw [hvx, Real.mul_rpow hv.le (by positivity), hxa,
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + x),
      show α + α = 2 * α by ring, div_eq_mul_inv]
  have hRHS : Complex.Gamma ((α : ℂ) + α) * (x : ℂ) ^ (α : ℂ) / (1 + (x : ℂ)) ^ ((α : ℂ) + α) =
      Complex.Gamma (2 * α) * ((v : ℂ) + (v : ℂ)⁻¹) ^ (-(2 * α : ℂ)) := by
    have e : (1 + (x : ℂ)) = ((1 + x : ℝ) : ℂ) := by push_cast; ring
    have e' : (v : ℂ) + (v : ℂ)⁻¹ = ((v + v⁻¹ : ℝ) : ℂ) := by push_cast; ring
    rw [e, e', show (α : ℂ) + α = ((α + α : ℝ) : ℂ) by push_cast; ring,
      show (-(2 * α : ℂ)) = ((-(2 * α) : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow hx.le, ← ofReal_cpow (by positivity), ← ofReal_cpow (by positivity),
      mul_div_assoc, ← ofReal_div, hreal, show ((α + α : ℝ) : ℂ) = 2 * α by push_cast; ring]
  rw [hJ]
  rw [hRHS] at h
  have hπ : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero)
  rw [one_div, inv_mul_eq_iff_eq_mul₀ hπ] at h
  rw [h]; ring


/-- The continuation of `integral_normSqHalfB_ofReal` to the right half-plane. -/
theorem integral_normSqHalfB {α : ℝ} (hα : 0 < α) {v : ℂ} (hv : 0 < v.re) :
    ∫ s : ℝ, normSqHalfB α s * v ^ (((0 : ℝ) : ℂ) + I * s) =
      4 * π * Complex.Gamma (2 * α) * (v + v⁻¹) ^ (-(2 * α : ℂ)) := by
  obtain ⟨C, K, hCK⟩ := exists_norm_normSqHalfB_le hα
  have hG := differentiableOn_integral_mul_cpow (continuous_normSqHalfB hα) hCK 0
  have hslit : ∀ w : ℂ, 0 < w.re → w + w⁻¹ ∈ slitPlane := by
    intro w hw
    refine mem_slitPlane_iff.2 (Or.inl ?_)
    rw [add_re, inv_re]
    have : 0 ≤ w.re / normSq w := div_nonneg hw.le (normSq_nonneg w)
    linarith
  have hR : DifferentiableOn ℂ (fun w : ℂ => 4 * π * Complex.Gamma (2 * α) *
      (w + w⁻¹) ^ (-(2 * α : ℂ))) {w | 0 < w.re} := by
    intro w hw
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw
    refine (DifferentiableAt.const_mul ?_ _).differentiableWithinAt
    exact (differentiableAt_id.add (differentiableAt_inv hw0)).cpow_const (hslit w hw)
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const continuous_re
  have hconv : Convex ℝ {w : ℂ | 0 < w.re} := convex_halfSpace_re_gt 0
  have h1 : (1 : ℂ) ∈ {w : ℂ | 0 < w.re} := by simp
  refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq (z₀ := 1)
    (hG.analyticOnNhd hU) (hR.analyticOnNhd hU) hconv.isPreconnected h1 ?_ hv
  have hev : ∀ᶠ x : ℝ in 𝓝[≠] 1, (∫ s : ℝ, normSqHalfB α s * (x : ℂ) ^ (((0 : ℝ) : ℂ) + I * s)) =
      4 * π * Complex.Gamma (2 * α) * ((x : ℂ) + (x : ℂ)⁻¹) ^ (-(2 * α : ℂ)) := by
    filter_upwards [nhdsWithin_le_nhds (lt_mem_nhds one_pos)] with x hx
    exact integral_normSqHalfB_ofReal hα hx
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] 1) (𝓝[≠] 1) :=
    Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun x hx => by
      simpa using hx
  exact ht.frequently hev.frequently

@[dlmf 5.13.E2]
theorem mellin_barnes_norm_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hbπ : b < π / 2) :
    (1 / (2 * π)) * ∫ t : ℝ,
        ‖Complex.Gamma (a + I * t)‖ ^ 2 * Real.exp ((2 * b - π) * t) =
      Real.Gamma (2 * a) / (2 * Real.sin b) ^ (2 * a) := by
  set ψ : ℝ := π / 2 - b with hψ
  set v : ℂ := exp (I * ψ) with hvdef
  have hsinb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb (by linarith [Real.pi_pos])
  have hvre : 0 < v.re := by
    rw [hvdef, show I * (ψ : ℂ) = (ψ : ℂ) * I by ring, exp_mul_I]
    simp only [add_re, ← ofReal_cos, ← ofReal_sin, ofReal_re, mul_re, I_re, I_im, ofReal_im]
    rw [hψ, Real.cos_pi_div_two_sub]; simpa using hsinb
  have hmain := integral_normSqHalfB ha hvre
  have hlog : log v = I * ψ := by
    rw [hvdef, log_exp] <;> simp [hψ] <;> linarith [Real.pi_pos]
  have hv0 : v ≠ 0 := exp_ne_zero _
  have hpow : ∀ s : ℝ, v ^ (((0 : ℝ) : ℂ) + I * s) = ((Real.exp (-(ψ * s)) : ℝ) : ℂ) := by
    intro s
    rw [cpow_def_of_ne_zero hv0, hlog, ofReal_exp]
    congr 1
    push_cast
    ring_nf
    rw [I_sq]; ring
  have hsum : v + v⁻¹ = ((2 * Real.sin b : ℝ) : ℂ) := by
    rw [hvdef, ← exp_neg, show I * (ψ : ℂ) = (ψ : ℂ) * I by ring,
      show -((ψ : ℂ) * I) = (-ψ : ℂ) * I by ring, exp_mul_I, exp_mul_I, cos_neg, sin_neg,
      ← ofReal_cos, hψ, Real.cos_pi_div_two_sub]
    push_cast; ring
  simp only [hpow, hsum] at hmain
  -- substitute `s = 2t`
  have hsub := Measure.integral_comp_mul_left
    (fun s : ℝ => normSqHalfB a s * ((Real.exp (-(ψ * s)) : ℝ) : ℂ)) 2
  have hpt : ∀ t : ℝ, normSqHalfB a (2 * t) * ((Real.exp (-(ψ * (2 * t))) : ℝ) : ℂ) =
      ((‖Complex.Gamma (a + I * t)‖ ^ 2 * Real.exp ((2 * b - π) * t) : ℝ) : ℂ) := by
    intro t
    have e1 : (a : ℂ) + I * (((2 * t : ℝ) : ℂ) / 2) = a + I * t := by push_cast; ring
    have e2 : (a : ℂ) - I * (((2 * t : ℝ) : ℂ) / 2) = conj ((a : ℂ) + I * t) := by
      simp only [map_add, map_mul, conj_ofReal, conj_I]; push_cast; ring
    rw [normSqHalfB, e1, e2, Complex.Gamma_conj, mul_conj, normSq_eq_norm_sq, hψ]
    push_cast
    congr 2
    ring
  simp only [hpt] at hsub
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), hmain, integral_complex_ofReal] at hsub
  have hreal : (∫ t : ℝ, ‖Complex.Gamma (a + I * t)‖ ^ 2 * Real.exp ((2 * b - π) * t)) =
      2 * π * Real.Gamma (2 * a) * (2 * Real.sin b) ^ (-(2 * a)) := by
    have e : ((2 * Real.sin b : ℝ) : ℂ) ^ (-(2 * a : ℂ)) =
        (((2 * Real.sin b) ^ (-(2 * a)) : ℝ) : ℂ) := by
      rw [ofReal_cpow (by positivity)]; push_cast; ring_nf
    rw [e, show (2 * (a : ℂ)) = ((2 * a : ℝ) : ℂ) by push_cast; ring,
      Complex.Gamma_ofReal] at hsub
    apply ofReal_injective
    rw [hsub, Complex.real_smul]
    push_cast; ring
  rw [hreal, Real.rpow_neg (by positivity)]
  field_simp

open Set in
/-- The vertical-line integrand `t ↦ Γ(a + it) Γ(c - it)` is integrable for `re a, re c > 0`. -/
theorem integrable_Gamma_add_mul_Gamma_sub {a c : ℂ} (ha : 0 < a.re) (hc : 0 < c.re) :
    Integrable (fun t : ℝ => Complex.Gamma (a + I * t) * Complex.Gamma (c - I * t)) := by
  have h := (integrable_Gamma_mul_Gamma_vertical (a := a + c) (σ := a.re) ha
    (by simp only [add_re]; linarith)).comp_add_right a.im
  refine h.congr (Eventually.of_forall fun t => ?_)
  have e : ((a.re : ℂ) + ((t + a.im : ℝ) : ℂ) * I) = a + I * t := by
    apply Complex.ext <;> simp; ring
  simp only [e]
  ring_nf

open Set in
/-- Inner integral in Barnes' first lemma: for `u > 0`,
`∫ Γ(a+it) Γ(c-it) u^{it} dt = 2π Γ(a+c) u^c (1+u)^{-(a+c)}`. -/
theorem integral_Gamma_mul_Gamma_mul_cpow {a c : ℂ} (ha : 0 < a.re) (hc : 0 < c.re) {u : ℝ}
    (hu : 0 < u) :
    ∫ t : ℝ, Complex.Gamma (a + I * t) * Complex.Gamma (c - I * t) * (u : ℂ) ^ (I * t) =
      2 * π * Complex.Gamma (a + c) * (u : ℂ) ^ c * ((1 + u : ℝ) : ℂ) ^ (-(a + c)) := by
  have hu' : (0 : ℝ) < u⁻¹ := inv_pos.mpr hu
  have h := Gamma_mul_one_add_cpow_neg (a := a + c) (σ := a.re) ha
    (by simp only [add_re]; linarith) hu'
  have huC : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have harg : (u : ℂ).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg hu.le]; exact Real.pi_ne_zero.symm
  -- rewrite the integrand of `h` as a translate
  have hshift : ∀ y : ℝ, Complex.Gamma (a.re + y * I) *
      Complex.Gamma (a + c - (a.re + y * I)) * ((u⁻¹ : ℝ) : ℂ) ^ (-((a.re : ℂ) + y * I)) =
      (u : ℂ) ^ a * (fun t : ℝ => Complex.Gamma (a + I * t) * Complex.Gamma (c - I * t) *
        (u : ℂ) ^ (I * t)) (y - a.im) := by
    intro y
    have e : (a.re : ℂ) + y * I = a + I * ((y - a.im : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [e, show a + c - (a + I * ((y - a.im : ℝ) : ℂ)) = c - I * ((y - a.im : ℝ) : ℂ) by ring,
      ofReal_inv, inv_cpow _ _ harg, cpow_neg, inv_inv, cpow_add _ _ huC]
    ring
  simp_rw [hshift] at h
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun t : ℝ => Complex.Gamma (a + I * t) * Complex.Gamma (c - I * t) * (u : ℂ) ^ (I * t))
    a.im] at h
  -- simplify `(1 + u⁻¹)^{-(a+c)} = (1+u)^{-(a+c)} u^{a+c}`
  have h1 : ((1 + u⁻¹ : ℝ) : ℂ) ^ (-(a + c)) =
      ((1 + u : ℝ) : ℂ) ^ (-(a + c)) * (u : ℂ) ^ (a + c) := by
    rw [show (1 + u⁻¹ : ℝ) = (1 + u) * u⁻¹ by field_simp; ring, ofReal_mul,
      mul_cpow_ofReal_nonneg (by linarith) (by positivity), ofReal_inv, inv_cpow _ _ harg,
      cpow_neg (u : ℂ), inv_inv]
  rw [h1] at h
  have hua : (u : ℂ) ^ a ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl huC)
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [cpow_add _ _ huC] at h
  generalize (∫ t : ℝ, Complex.Gamma (a + I * t) * Complex.Gamma (c - I * t) *
    (u : ℂ) ^ (I * t)) = J at h ⊢
  field_simp at h ⊢
  exact h.symm

open Set in
@[dlmf 5.13.E3]
theorem mellin_barnes_four {a b c d : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re) (hd : 0 < d.re) :
    (1 / (2 * π)) * ∫ t : ℝ,
        Complex.Gamma (a + I * t) * Complex.Gamma (b + I * t) *
          Complex.Gamma (c - I * t) * Complex.Gamma (d - I * t) =
      Complex.Gamma (a + c) * Complex.Gamma (a + d) * Complex.Gamma (b + c) *
        Complex.Gamma (b + d) / Complex.Gamma (a + b + c + d) := by
  set G : ℝ → ℂ := fun t => Complex.Gamma (a + I * t) * Complex.Gamma (c - I * t) with hG
  set K : ℝ → ℝ → ℂ := fun t u =>
    G t * ((u : ℂ) ^ (b + I * t - 1) * ((1 + u : ℝ) : ℂ) ^ (-(b + d))) with hK
  have hbd : Complex.Gamma (b + d) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp only [add_re]; linarith)
  -- Step 1: `Γ(b+it) Γ(d-it) = Γ(b+d) · ∫ u^{b+it-1} (1+u)^{-(b+d)} du`
  have hrow : ∀ t : ℝ, Complex.Gamma (a + I * t) * Complex.Gamma (b + I * t) *
      Complex.Gamma (c - I * t) * Complex.Gamma (d - I * t) =
      Complex.Gamma (b + d) * ∫ u in Ioi (0 : ℝ), K t u := by
    intro t
    have hm := mellin_one_add_cpow_neg (a := b + d) (s := b + I * t) (by simp [hb])
      (by simp only [add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im]; linarith)
    rw [mellin, show b + d - (b + I * t) = d - I * t by ring] at hm
    simp only [smul_eq_mul] at hm
    simp only [hK]
    rw [integral_const_mul, hm]
    simp only [hG]
    field_simp
  -- Step 2: integrability on the product, for Fubini
  have hGi : Integrable G := integrable_Gamma_add_mul_Gamma_sub ha hc
  have hHi : IntegrableOn (fun u : ℝ => u ^ (b.re - 1) * (1 + u) ^ (-(b + d).re)) (Ioi 0) :=
    integrableOn_rpow_mul_one_add_rpow hb (by simp only [add_re]; linarith)
  have hμ : (volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ))) =
      (volume.prod volume).restrict (univ ×ˢ Ioi (0 : ℝ)) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hKcont : ContinuousOn (Function.uncurry K) (univ ×ˢ Ioi (0 : ℝ)) := by
    rintro ⟨t, u⟩ ⟨-, hu⟩
    have hu0 : (0 : ℝ) < u := hu
    refine ContinuousAt.continuousWithinAt ?_
    simp only [hK, hG, Function.uncurry_def]
    refine ContinuousAt.mul (ContinuousAt.mul ?_ ?_) (ContinuousAt.mul ?_ ?_)
    · exact (continuousAt_Gamma_of_re_pos (by simp [ha])).comp (by fun_prop)
    · exact (continuousAt_Gamma_of_re_pos (by simp [hc])).comp (by fun_prop)
    · exact ContinuousAt.cpow (by fun_prop) (by fun_prop) (ofReal_mem_slitPlane.mpr hu0)
    · exact ContinuousAt.cpow (by fun_prop) (by fun_prop)
        (ofReal_mem_slitPlane.mpr (by linarith))
  have hKint : Integrable (Function.uncurry K) ((volume : Measure ℝ).prod
      (volume.restrict (Ioi (0 : ℝ)))) := by
    have hbound := hGi.norm.mul_prod hHi
    refine hbound.mono' ?_ ?_
    · rw [hμ]; exact hKcont.aestronglyMeasurable (MeasurableSet.univ.prod measurableSet_Ioi)
    · rw [hμ]
      refine (ae_restrict_iff' (MeasurableSet.univ.prod measurableSet_Ioi)).mpr
        (Eventually.of_forall fun ⟨t, u⟩ ⟨_, hu⟩ => ?_)
      have hu0 : (0 : ℝ) < u := hu
      simp only [Function.uncurry_apply_pair, hK, norm_mul]
      rw [norm_cpow_eq_rpow_re_of_pos hu0, norm_cpow_eq_rpow_re_of_pos (by linarith)]
      simp
  -- Step 3: swap and evaluate the inner integral
  have hswap := integral_integral_swap hKint
  have hinner : ∀ u ∈ Ioi (0 : ℝ), ∫ t : ℝ, K t u =
      2 * π * Complex.Gamma (a + c) *
        ((u : ℂ) ^ ((b + c) - 1) * ((1 + u : ℝ) : ℂ) ^ (-(a + b + c + d))) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    have huC : (u : ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
    have h1u : ((1 + u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0 : ℝ) < 1 + u).ne'
    have hsplit : ∀ t : ℝ, K t u = ((u : ℂ) ^ (b - 1) * ((1 + u : ℝ) : ℂ) ^ (-(b + d))) *
        (G t * (u : ℂ) ^ (I * t)) := by
      intro t
      simp only [hK]
      rw [show b + I * t - 1 = (b - 1) + I * t by ring, cpow_add _ _ huC]
      ring
    simp_rw [hsplit]
    rw [integral_const_mul]
    simp only [hG]
    rw [integral_Gamma_mul_Gamma_mul_cpow ha hc hu0]
    rw [show -(a + b + c + d) = -(b + d) + -(a + c) by ring, cpow_add _ _ h1u,
      show b + c - 1 = (b - 1) + c by ring, cpow_add _ _ huC]
    ring
  rw [show (∫ t : ℝ, Complex.Gamma (a + I * t) * Complex.Gamma (b + I * t) *
      Complex.Gamma (c - I * t) * Complex.Gamma (d - I * t)) =
      Complex.Gamma (b + d) * ∫ t : ℝ, ∫ u in Ioi (0 : ℝ), K t u by
    rw [← integral_const_mul]; exact integral_congr_ae (Eventually.of_forall hrow)]
  rw [hswap, setIntegral_congr_fun measurableSet_Ioi hinner, integral_const_mul]
  -- Step 4: the remaining Beta integral
  have hm := mellin_one_add_cpow_neg (a := a + b + c + d) (s := b + c)
    (by simp only [add_re]; linarith) (by simp only [add_re]; linarith)
  rw [mellin, show a + b + c + d - (b + c) = a + d by ring] at hm
  simp only [smul_eq_mul] at hm
  rw [hm]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

section Ramanujan

open Set FourierTransform
open scoped Interval

/-! ### Ramanujan's integral 5.13.4

For real parameters with `a + c > 1` and `b + d > 2`, the factor `1/(Γ(a+x)Γ(c-x))` is a
multiple of the Fourier transform of the kernel `1_{(-π/2,π/2]} cos^{a+c-2}φ e^{i(c-a)φ}`, by the
Cauchy-type integral `∫ cos^α x e^{iζx} dx` (5.12.5 continued to complex `ζ`). The
multiplication formula `∫ 𝓕h · G = ∫ h · 𝓕G` and Fourier inversion then reduce the integral to
one more Cauchy integral. The parameters are continued one at a time to complex values: the
integral is holomorphic in each parameter on `re(a+b+c+d) > 3`, by locally uniform tail bounds
from log-convexity of `Γ` and the reflection formula. -/

namespace RamanujanAux

/-- `|Γ(x+iy)| ≤ Γ(x)` for `x > 0`. -/
theorem norm_Gamma_le_Gamma_re {z : ℂ} (hz : 0 < z.re) : ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  have h := norm_Gamma_sq_eq hz z.im
  rw [show ((z.re : ℂ) + I * z.im) = z by rw [mul_comm]; exact re_add_im z] at h
  have hG := Real.Gamma_pos_of_pos hz
  have hP := one_le_gammaVertProd z.re z.im
  have h2 : ‖Complex.Gamma z‖ ^ 2 ≤ Real.Gamma z.re ^ 2 := by
    rw [h]; exact div_le_self (by positivity) hP
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hG.le two_ne_zero).1 h2

theorem gammaVertProd_le_of_abs_le {x y Y : ℝ} (hx : 0 < x) (hy : |y| ≤ Y) :
    gammaVertProd x y ≤ gammaVertProd x Y := by
  refine le_of_tendsto_of_tendsto' (tendsto_prod_gammaVertProd x y)
    (tendsto_prod_gammaVertProd x Y) fun n => ?_
  refine Finset.prod_le_prod₀ (fun k _ => by positivity) fun k _ => ?_
  have h1 : 0 < x + k := by positivity
  have : y ^ 2 ≤ Y ^ 2 := by
    rw [← sq_abs y]; exact pow_le_pow_left₀ (abs_nonneg y) hy 2
  gcongr

/-- A lower bound for `|Γ|` near the real axis: `Γ(x) ≤ √P(x₁,Y) |Γ(x+iy)|`. -/
theorem Gamma_re_le_mul_norm_Gamma {x₁ Y : ℝ} (hx₁ : 0 < x₁) {z : ℂ} (hz : x₁ ≤ z.re)
    (hy : |z.im| ≤ Y) :
    Real.Gamma z.re ≤ Real.sqrt (gammaVertProd x₁ Y) * ‖Complex.Gamma z‖ := by
  have hzr : 0 < z.re := hx₁.trans_le hz
  have h := norm_Gamma_sq_eq hzr z.im
  rw [show ((z.re : ℂ) + I * z.im) = z by rw [mul_comm]; exact re_add_im z] at h
  have hP1 := one_le_gammaVertProd z.re z.im
  have hP : gammaVertProd z.re z.im ≤ gammaVertProd x₁ Y :=
    (gammaVertProd_anti hx₁ hz z.im).trans (gammaVertProd_le_of_abs_le hx₁ hy)
  have hG := Real.Gamma_pos_of_pos hzr
  have h2 : Real.Gamma z.re ^ 2 ≤ (Real.sqrt (gammaVertProd x₁ Y) * ‖Complex.Gamma z‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by linarith), h]
    have hpos : 0 < gammaVertProd z.re z.im := by linarith
    rw [mul_div_assoc']
    rw [le_div_iff₀ hpos]
    have := sq_nonneg (Real.Gamma z.re)
    nlinarith
  exact (pow_le_pow_iff_left₀ hG.le (by positivity) two_ne_zero).1 h2

/-- `1/Γ(z) = Γ(1-z) sin(πz)/π` for `re z < 1`. -/
theorem recip_Gamma_eq_reflect {z : ℂ} (hz : z.re < 1) :
    (Complex.Gamma z)⁻¹ = Complex.Gamma (1 - z) * Complex.sin (π * z) / π := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  by_cases hs : Complex.sin (π * z) = 0
  · obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.1 hs
    have hzk : z = k := by
      rw [mul_comm] at hk; exact mul_right_cancel₀ hπ hk
    have hk0 : k ≤ 0 := by
      by_contra hk0
      have : (1 : ℝ) ≤ z.re := by rw [hzk]; simp; exact_mod_cast (Int.not_le.1 hk0)
      linarith
    obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat hk0
    rw [hs, mul_zero, zero_div, inv_eq_zero, hzk, hn]
    simpa using Complex.Gamma_neg_nat_eq_zero n
  · have h := Complex.Gamma_mul_Gamma_one_sub z
    have hG : Complex.Gamma z ≠ 0 := by
      intro h0; rw [h0, zero_mul] at h
      exact (div_ne_zero hπ hs) h.symm
    have h1 : Complex.Gamma z * (Complex.Gamma (1 - z) * Complex.sin (π * z) / π) = 1 := by
      rw [← mul_div_assoc, ← mul_assoc, h]; field_simp
    exact (eq_inv_of_mul_eq_one_right h1).symm

/-- `‖sin z‖ ≤ exp |im z|`. -/
theorem norm_sin_le_exp_abs_im (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin]
  have h1 : ‖Complex.exp (-z * I)‖ = Real.exp z.im := by rw [norm_exp]; simp
  have h2 : ‖Complex.exp (z * I)‖ = Real.exp (-z.im) := by rw [norm_exp]; simp
  calc ‖(Complex.exp (-z * I) - Complex.exp (z * I)) * I / 2‖
      ≤ (‖Complex.exp (-z * I)‖ + ‖Complex.exp (z * I)‖) / 2 := by
        rw [norm_div, norm_mul, norm_I, mul_one, Complex.norm_two]
        gcongr; exact norm_sub_le _ _
    _ ≤ Real.exp |z.im| := by
        rw [h1, h2]
        have := Real.exp_le_exp.2 (le_abs_self z.im)
        have := Real.exp_le_exp.2 (neg_le_abs z.im)
        linarith

/-- Two-sided comparison `c t^w Γ(t) ≤ Γ(t+w) ≤ C t^w Γ(t)` for large `t`. -/
def GammaShiftBound (w : ℝ) : Prop :=
  ∃ c C T : ℝ, 0 < c ∧ 0 < T ∧ ∀ t : ℝ, T ≤ t →
    c * t ^ w * Real.Gamma t ≤ Real.Gamma (t + w) ∧ Real.Gamma (t + w) ≤ C * t ^ w * Real.Gamma t

theorem gammaShiftBound_of_mem_Icc {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : GammaShiftBound s := by
  refine ⟨1 / 2, 1, 1, by norm_num, one_pos, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hG := Real.Gamma_pos_of_pos hx0
  rcases hs0.lt_or_eq with hs0 | rfl
  · rcases hs1.lt_or_eq with hs1 | rfl
    · have hup : Real.Gamma (x + s) ≤ x ^ s * Real.Gamma x := by
        have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := x) (t := x + 1)
          (a := 1 - s) (b := s) hx0 (by linarith) (by linarith) hs0 (by ring)
        rw [show (1 - s) * x + s * (x + 1) = x + s by ring, Real.Gamma_add_one hx0.ne',
          Real.mul_rpow hx0.le hG.le] at h
        calc Real.Gamma (x + s) ≤ Real.Gamma x ^ (1 - s) * (x ^ s * Real.Gamma x ^ s) := h
          _ = x ^ s * (Real.Gamma x ^ (1 - s) * Real.Gamma x ^ s) := by ring
          _ = x ^ s * Real.Gamma x := by
            rw [← Real.rpow_add hG, sub_add_cancel, Real.rpow_one]
      have hxs : 0 < x + s := by linarith
      have hGs := Real.Gamma_pos_of_pos hxs
      have hlow : x * Real.Gamma x ≤ (x + s) ^ (1 - s) * Real.Gamma (x + s) := by
        have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := x + s)
          (t := x + s + 1) (a := s) (b := 1 - s) hxs (by linarith) hs0 (by linarith) (by ring)
        rw [show s * (x + s) + (1 - s) * (x + s + 1) = x + 1 by ring,
          Real.Gamma_add_one hx0.ne', Real.Gamma_add_one hxs.ne',
          Real.mul_rpow hxs.le hGs.le] at h
        calc x * Real.Gamma x ≤ Real.Gamma (x + s) ^ s *
              ((x + s) ^ (1 - s) * Real.Gamma (x + s) ^ (1 - s)) := h
          _ = (x + s) ^ (1 - s) * (Real.Gamma (x + s) ^ s * Real.Gamma (x + s) ^ (1 - s)) := by
            ring
          _ = (x + s) ^ (1 - s) * Real.Gamma (x + s) := by
            rw [← Real.rpow_add hGs, add_sub_cancel, Real.rpow_one]
      refine ⟨?_, by linarith⟩
      -- `x^s (x+s)^{1-s} ≤ 2x`
      have h1 : (x + s) ^ (1 - s) ≤ (2 * x) ^ (1 - s) :=
        Real.rpow_le_rpow hxs.le (by linarith) (by linarith)
      have h2 : (2 * x) ^ (1 - s) ≤ 2 * x ^ (1 - s) := by
        rw [Real.mul_rpow (by norm_num) hx0.le]
        gcongr
        calc (2 : ℝ) ^ (1 - s) ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 2 := Real.rpow_one 2
      have h3 : x ^ s * x ^ (1 - s) = x := by
        rw [← Real.rpow_add hx0, add_sub_cancel, Real.rpow_one]
      have hxs' : 0 < x ^ s := by positivity
      have key : x ^ s * (x + s) ^ (1 - s) ≤ 2 * x := by
        calc x ^ s * (x + s) ^ (1 - s) ≤ x ^ s * (2 * x ^ (1 - s)) := by gcongr; linarith
          _ = 2 * (x ^ s * x ^ (1 - s)) := by ring
          _ = 2 * x := by rw [h3]
      have hpow : 0 < (x + s) ^ (1 - s) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hlow hxs'.le]
    · rw [Real.rpow_one, Real.Gamma_add_one hx0.ne']
      constructor <;> nlinarith
  · simp only [Real.rpow_zero, add_zero]
    constructor <;> nlinarith

theorem GammaShiftBound.add_one {w : ℝ} (h : GammaShiftBound w) : GammaShiftBound (w + 1) := by
  obtain ⟨c, C, T, hc, hT, hb⟩ := h
  refine ⟨c / 2, 2 * C, max T (2 * |w| + 1), by positivity, by positivity, fun t ht => ?_⟩
  have htT : T ≤ t := le_trans (le_max_left _ _) ht
  have htw : 2 * |w| + 1 ≤ t := le_trans (le_max_right _ _) ht
  have ht0 : 0 < t := by linarith [abs_nonneg w]
  have hw1 : t / 2 ≤ t + w := by linarith [neg_abs_le w]
  have hw2 : t + w ≤ 2 * t := by linarith [le_abs_self w]
  obtain ⟨h1, h2⟩ := hb t htT
  have hG := Real.Gamma_pos_of_pos ht0
  have hpos : 0 < t ^ w * Real.Gamma t := by positivity
  rw [← add_assoc, Real.Gamma_add_one (by linarith), Real.rpow_add_one ht0.ne']
  constructor
  · calc c / 2 * (t ^ w * t) * Real.Gamma t = (t / 2) * (c * t ^ w * Real.Gamma t) := by ring
      _ ≤ (t + w) * Real.Gamma (t + w) := by gcongr; linarith
  · calc (t + w) * Real.Gamma (t + w) ≤ (2 * t) * (C * t ^ w * Real.Gamma t) := by
          gcongr
          · nlinarith [Real.Gamma_pos_of_pos (show 0 < t + w by linarith)]
      _ = 2 * C * (t ^ w * t) * Real.Gamma t := by ring

theorem GammaShiftBound.sub_one {w : ℝ} (h : GammaShiftBound w) : GammaShiftBound (w - 1) := by
  obtain ⟨c, C, T, hc, hT, hb⟩ := h
  refine ⟨c / 2, 2 * C, max T (2 * |w| + 4), by positivity, by positivity, fun t ht => ?_⟩
  have htT : T ≤ t := le_trans (le_max_left _ _) ht
  have htw : 2 * |w| + 4 ≤ t := le_trans (le_max_right _ _) ht
  have ht0 : 0 < t := by linarith [abs_nonneg w]
  have hw1 : t / 2 ≤ t + w - 1 := by linarith [neg_abs_le w]
  have hw2 : t + w - 1 ≤ 2 * t := by linarith [le_abs_self w]
  have hpos1 : 0 < t + w - 1 := by linarith
  obtain ⟨h1, h2⟩ := hb t htT
  have hG := Real.Gamma_pos_of_pos ht0
  have hrec : Real.Gamma (t + w) = (t + w - 1) * Real.Gamma (t + (w - 1)) := by
    rw [show t + w = (t + (w - 1)) + 1 by ring, Real.Gamma_add_one (by linarith)]; ring_nf
  have hpw : t ^ (w - 1) * t = t ^ w := by
    rw [← Real.rpow_add_one ht0.ne', sub_add_cancel]
  have hG1 := Real.Gamma_pos_of_pos (show 0 < t + (w - 1) by linarith)
  rw [hrec] at h1 h2
  rw [← hpw] at h1 h2
  constructor
  · nlinarith [Real.rpow_pos_of_pos ht0 (w - 1)]
  · nlinarith [Real.rpow_pos_of_pos ht0 (w - 1)]

theorem gammaShiftBound (w : ℝ) : GammaShiftBound w := by
  have hb := gammaShiftBound_of_mem_Icc (Int.fract_nonneg w) (Int.fract_lt_one w).le
  have key : ∀ n : ℤ, GammaShiftBound (Int.fract w + n) := by
    intro n
    induction n using Int.induction_on with
    | zero => simpa using hb
    | succ k ih => simpa [add_assoc] using ih.add_one
    | pred k ih =>
      have := ih.sub_one
      simpa [sub_eq_add_neg, add_assoc] using this
  simpa [Int.fract_add_floor] using key ⌊w⌋

/-- The real Gamma ratio bound `Γ(t+α)/Γ(t+β) = O(t^{α-β})`. -/
theorem exists_Gamma_ratio_le (α β : ℝ) : ∃ K T : ℝ, 0 ≤ K ∧ 0 < T ∧ ∀ t : ℝ, T ≤ t →
    Real.Gamma (t + α) ≤ K * t ^ (α - β) * Real.Gamma (t + β) := by
  obtain ⟨_, C, T₁, _, hT₁, h1⟩ := gammaShiftBound α
  obtain ⟨c, _, T₂, hc, hT₂, h2⟩ := gammaShiftBound β
  refine ⟨max C 1 / c, max T₁ T₂, by positivity, by positivity, fun t ht => ?_⟩
  have ht1 : T₁ ≤ t := le_trans (le_max_left _ _) ht
  have ht2 : T₂ ≤ t := le_trans (le_max_right _ _) ht
  have ht0 : 0 < t := by linarith
  have hG := Real.Gamma_pos_of_pos ht0
  have e : t ^ (α - β) * t ^ β = t ^ α := by rw [← Real.rpow_add ht0, sub_add_cancel]
  have hM : 0 < max C 1 := lt_max_of_lt_right one_pos
  calc Real.Gamma (t + α) ≤ C * t ^ α * Real.Gamma t := (h1 t ht1).2
    _ ≤ max C 1 * t ^ α * Real.Gamma t := by gcongr; exact le_max_left _ _
    _ = max C 1 / c * t ^ (α - β) * (c * t ^ β * Real.Gamma t) := by
        rw [← e]; field_simp
    _ ≤ max C 1 / c * t ^ (α - β) * Real.Gamma (t + β) := by
        gcongr; exact (h2 t ht2).1


/-- **Integrals against `1/Γ(a+t)` are holomorphic in `a`**, given an integrable majorant on a
closed disc of radius `2r` about `a₀`. -/
theorem differentiableAt_integral_recip_Gamma_mul {G : ℝ → ℂ} (hG : Continuous G) {a₀ : ℂ}
    {r : ℝ} (hr : 0 < r) {M : ℝ → ℝ} (hM : Integrable M)
    (hb : ∀ a ∈ Metric.closedBall a₀ (2 * r), ∀ t : ℝ,
      ‖(Complex.Gamma (a + t))⁻¹ * G t‖ ≤ M t) :
    DifferentiableAt ℂ (fun a : ℂ => ∫ t : ℝ, (Complex.Gamma (a + t))⁻¹ * G t) a₀ := by
  set g : ℂ → ℂ := fun s => (Complex.Gamma s)⁻¹
  have hg : Differentiable ℂ g := differentiable_recip_Gamma
  set F : ℂ → ℝ → ℂ := fun a t => g (a + t) * G t with hF
  set F' : ℂ → ℝ → ℂ := fun a t => deriv g (a + t) * G t with hF'
  have hcont : ∀ a : ℂ, Continuous (F a) := fun a =>
    (hg.continuous.comp (by fun_prop : Continuous fun t : ℝ => a + (t : ℂ))).mul hG
  have hderiv : ∀ t : ℝ, ∀ a ∈ Metric.ball a₀ r, ‖F' a t‖ ≤ M t / r := by
    intro t a ha
    have hd : DiffContOnCl ℂ (fun w => g w * G t) (Metric.ball (a + t) r) :=
      (hg.mul_const (G t)).diffContOnCl
    have h := norm_deriv_le_of_forall_mem_sphere_norm_le hr hd (C := M t) (fun w hw => by
      have hw' : w - t ∈ Metric.closedBall a₀ (2 * r) := by
        rw [Metric.mem_sphere, dist_eq_norm] at hw
        rw [Metric.mem_ball, dist_eq_norm] at ha
        rw [Metric.mem_closedBall, dist_eq_norm]
        calc ‖w - t - a₀‖ = ‖(w - (a + t)) + (a - a₀)‖ := by ring_nf
          _ ≤ ‖w - (a + t)‖ + ‖a - a₀‖ := norm_add_le _ _
          _ ≤ 2 * r := by linarith
      have := hb (w - t) hw' t
      simpa [g] using this)
    have e : deriv (fun w => g w * G t) (a + t) = deriv g (a + t) * G t :=
      deriv_mul_const (hg (a + t)) (G t)
    rw [e] at h
    exact h
  have hball : Metric.ball a₀ r ⊆ Metric.closedBall a₀ (2 * r) :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F')
    (bound := fun t => M t / r) (Metric.ball_mem_nhds a₀ hr)
    (Eventually.of_forall fun a => (hcont a).aestronglyMeasurable)
    (hM.mono' (hcont a₀).aestronglyMeasurable (Eventually.of_forall fun t =>
      hb a₀ (Metric.mem_closedBall_self (by linarith)) t))
    (((measurable_deriv g).comp (by fun_prop : Continuous fun t : ℝ => a₀ + (t : ℂ)).measurable
      ).aestronglyMeasurable.mul hG.aestronglyMeasurable)
    (Eventually.of_forall fun t a ha => hderiv t a ha) (hM.div_const r)
    (Eventually.of_forall fun t a _ => by
      have h := ((hg (a + t)).hasDerivAt.comp a ((hasDerivAt_id a).add_const (t : ℂ))).mul_const
        (G t)
      simpa [F, F'] using h)
  exact key.2.differentiableAt


/-- A lower bound for `|Γ|` gives an upper bound for `1/|Γ|`. -/
theorem norm_recip_Gamma_le_of_re {Y : ℝ} {z : ℂ} (hz : 1 ≤ z.re) (hy : |z.im| ≤ Y) :
    ‖(Complex.Gamma z)⁻¹‖ ≤ Real.sqrt (gammaVertProd 1 Y) / Real.Gamma z.re := by
  have h := Gamma_re_le_mul_norm_Gamma one_pos hz hy
  have hG := Real.Gamma_pos_of_pos (show 0 < z.re by linarith)
  have hn : 0 < ‖Complex.Gamma z‖ := by
    by_contra h0
    have : ‖Complex.Gamma z‖ = 0 := le_antisymm (not_lt.1 h0) (norm_nonneg _)
    rw [this, mul_zero] at h; linarith
  rw [norm_inv, inv_eq_one_div, div_le_div_iff₀ hn hG]
  linarith

/-- The reflection bound `1/|Γ(z)| ≤ |Γ(1-z)| e^{π|im z|}/π` for `re z < 1`. -/
theorem norm_recip_Gamma_le_reflect {z : ℂ} (hz : z.re < 1) :
    ‖(Complex.Gamma z)⁻¹‖ ≤ ‖Complex.Gamma (1 - z)‖ * Real.exp (π * |z.im|) / π := by
  rw [recip_Gamma_eq_reflect hz, norm_div, norm_mul, norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  gcongr
  have := norm_sin_le_exp_abs_im (π * z)
  simpa [abs_mul, abs_of_pos Real.pi_pos] using this

/-- The complex Gamma ratio bound `|Γ(t+u)| ≤ K t^{re(u-v)} |Γ(t+v)|` for large `t`. -/
theorem exists_norm_Gamma_ratio_le (u v : ℂ) : ∃ K T : ℝ, 0 ≤ K ∧ 0 < T ∧ ∀ t : ℝ, T ≤ t →
    ‖Complex.Gamma (t + u)‖ ≤ K * t ^ (u - v).re * ‖Complex.Gamma (t + v)‖ := by
  obtain ⟨K, T, hK, hT, h⟩ := exists_Gamma_ratio_le u.re v.re
  refine ⟨K * Real.sqrt (gammaVertProd 1 |v.im|), max T (|u.re| + |v.re| + 1), by positivity,
    by positivity, fun t ht => ?_⟩
  have htT : T ≤ t := le_trans (le_max_left _ _) ht
  have ht1 : |u.re| + |v.re| + 1 ≤ t := le_trans (le_max_right _ _) ht
  have ht0 : 0 < t := by linarith [abs_nonneg u.re, abs_nonneg v.re]
  have hu : 0 < ((t : ℂ) + u).re := by simp; linarith [neg_abs_le u.re, abs_nonneg v.re]
  have hv : 1 ≤ ((t : ℂ) + v).re := by simp; linarith [neg_abs_le v.re, abs_nonneg u.re]
  have h1 := norm_Gamma_le_Gamma_re hu
  have h2 := Gamma_re_le_mul_norm_Gamma one_pos hv (Y := |v.im|) (by simp)
  have h3 := h t htT
  simp only [add_re, ofReal_re] at h1 h2
  rw [sub_re]
  calc ‖Complex.Gamma (t + u)‖ ≤ Real.Gamma (t + u.re) := h1
    _ ≤ K * t ^ (u.re - v.re) * Real.Gamma (t + v.re) := h3
    _ ≤ K * t ^ (u.re - v.re) * (Real.sqrt (gammaVertProd 1 |v.im|) *
          ‖Complex.Gamma (t + v)‖) := by gcongr
    _ = _ := by ring

theorem mul_recip_le_of_le_mul {x y k : ℝ} (hk : 0 ≤ k) (hy : 0 ≤ y) (h : x ≤ k * y) :
    x * y⁻¹ ≤ k := by
  rcases hy.lt_or_eq with hy | rfl
  · rw [← div_eq_mul_inv, div_le_iff₀ hy]; exact h
  · simpa using hk

/-- The integrand of Ramanujan's integral 5.13.4. -/
def ramanujanIntegrand (a b c d : ℂ) (t : ℝ) : ℂ :=
  1 / (Complex.Gamma (a + t) * Complex.Gamma (b + t) * Complex.Gamma (c - t) *
    Complex.Gamma (d - t))

theorem norm_ramanujanIntegrand (a b c d : ℂ) (t : ℝ) :
    ‖ramanujanIntegrand a b c d t‖ = ‖(Complex.Gamma (a + t))⁻¹‖ *
      ‖(Complex.Gamma (b + t))⁻¹‖ * ‖(Complex.Gamma (c - t))⁻¹‖ *
      ‖(Complex.Gamma (d - t))⁻¹‖ := by
  rw [ramanujanIntegrand, one_div, mul_inv, mul_inv, mul_inv, norm_mul, norm_mul, norm_mul]

theorem ramanujanIntegrand_neg (a b c d : ℂ) (u : ℝ) :
    ramanujanIntegrand a b c d (-u) = ramanujanIntegrand c d a b u := by
  simp only [ramanujanIntegrand, ofReal_neg, ← sub_eq_add_neg, sub_neg_eq_add]
  ring_nf

theorem ramanujanIntegrand_swap (a b c d : ℂ) (t : ℝ) :
    ramanujanIntegrand a b c d t = ramanujanIntegrand b a c d t := by
  simp only [ramanujanIntegrand]; ring_nf

theorem re_im_of_mem_closedBall {a a₀ : ℂ} {ρ : ℝ} (ha : a ∈ Metric.closedBall a₀ ρ) :
    a₀.re - ρ ≤ a.re ∧ a.re ≤ a₀.re + ρ ∧ |a.im| ≤ |a₀.im| + ρ := by
  rw [Metric.mem_closedBall, dist_eq_norm] at ha
  have h1 := abs_re_le_norm (a - a₀)
  have h2 := abs_im_le_norm (a - a₀)
  rw [sub_re, abs_le] at h1
  rw [sub_im] at h2
  refine ⟨by linarith [h1.1], by linarith [h1.2], ?_⟩
  have := abs_sub_abs_le_abs_sub a.im a₀.im
  linarith

/-- The right tail of Ramanujan's integrand, uniformly for `a` in a closed disc. -/
theorem right_tail (a₀ b c d : ℂ) (ρ : ℝ) : ∃ K T : ℝ, 0 ≤ K ∧ 0 < T ∧
    ∀ a ∈ Metric.closedBall a₀ ρ, ∀ t : ℝ, T ≤ t →
      ‖ramanujanIntegrand a b c d t‖ ≤ K * t ^ (2 - (a₀.re - ρ) - (b + c + d).re) := by
  set α := a₀.re - ρ with hα
  set Y := |a₀.im| + ρ
  obtain ⟨K1, T1, hK1, hT1, h1⟩ := exists_Gamma_ratio_le (1 - c.re) α
  obtain ⟨K2, T2, hK2, hT2, h2⟩ := exists_norm_Gamma_ratio_le (1 - d) b
  set P := Real.sqrt (gammaVertProd 1 Y)
  set Ec := Real.exp (π * |c.im|)
  set Ed := Real.exp (π * |d.im|)
  refine ⟨P * Ec * Ed / π ^ 2 * K1 * K2,
    max (max T1 T2) (max (|2 - α| + 1) (max (|c.re| + 1) (|d.re| + 1))), by positivity,
    by positivity, fun a ha t ht => ?_⟩
  obtain ⟨hre1, -, him⟩ := re_im_of_mem_closedBall ha
  have htT1 : T1 ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
  have htT2 : T2 ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
  have htα : |2 - α| + 1 ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have htc : |c.re| + 1 ≤ t := le_trans (le_trans (le_trans (le_max_left _ _)
    (le_max_right _ _)) (le_max_right _ _)) ht
  have htd : |d.re| + 1 ≤ t := le_trans (le_trans (le_trans (le_max_right _ _)
    (le_max_right _ _)) (le_max_right _ _)) ht
  have ht0 : 0 < t := by linarith [abs_nonneg c.re]
  have h2α : 2 ≤ t + α := by linarith [le_abs_self (2 - α)]
  have hGα := Real.Gamma_pos_of_pos (show 0 < t + α by linarith)
  -- the four factors
  have hA : ‖(Complex.Gamma (a + t))⁻¹‖ ≤ P / Real.Gamma (t + α) := by
    have h := norm_recip_Gamma_le_of_re (z := a + t) (Y := Y) (by simp; linarith)
      (by simpa using him)
    refine h.trans ?_
    have hmono : Real.Gamma (t + α) ≤ Real.Gamma (a + t : ℂ).re := by
      simp only [add_re, ofReal_re]
      exact Real.Gamma_strictMonoOn_Ici.monotoneOn (mem_Ici.2 h2α)
        (mem_Ici.2 (by linarith)) (by linarith)
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hGα hmono
  have hC : ‖(Complex.Gamma (c - t))⁻¹‖ ≤ Real.Gamma (t + (1 - c.re)) * Ec / π := by
    have h := norm_recip_Gamma_le_reflect (z := c - t) (by simp; linarith [le_abs_self c.re])
    refine h.trans ?_
    have hre : 0 < (1 - (c - t)).re := by simp; linarith [le_abs_self c.re]
    have h' := norm_Gamma_le_Gamma_re hre
    simp only [sub_re, one_re, ofReal_re, sub_im, ofReal_im, sub_zero] at h' ⊢
    rw [show 1 - (c.re - t) = t + (1 - c.re) by ring] at h'
    gcongr
  have hD : ‖(Complex.Gamma (d - t))⁻¹‖ ≤ ‖Complex.Gamma (t + (1 - d))‖ * Ed / π := by
    have h := norm_recip_Gamma_le_reflect (z := d - t) (by simp; linarith [le_abs_self d.re])
    rw [show (1 : ℂ) - (d - t) = t + (1 - d) by ring] at h
    simpa using h
  have hB : ‖(Complex.Gamma (b + t))⁻¹‖ = ‖Complex.Gamma (t + b)‖⁻¹ := by
    rw [norm_inv, add_comm]
  have hr1 := h1 t htT1
  have hr2 := h2 t htT2
  have hq1 : Real.Gamma (t + (1 - c.re)) * (Real.Gamma (t + α))⁻¹ ≤
      K1 * t ^ (1 - c.re - α) :=
    mul_recip_le_of_le_mul (by positivity) hGα.le hr1
  have hq2 : ‖Complex.Gamma (t + (1 - d))‖ * ‖Complex.Gamma (t + b)‖⁻¹ ≤
      K2 * t ^ (1 - d - b).re :=
    mul_recip_le_of_le_mul (by positivity) (norm_nonneg _) hr2
  have hexp : t ^ (1 - c.re - α) * t ^ (1 - d - b).re =
      t ^ (2 - (a₀.re - ρ) - (b + c + d).re) := by
    rw [← Real.rpow_add ht0]; congr 1; simp [hα]; ring
  rw [norm_ramanujanIntegrand, hB]
  have hGt : 0 ≤ Real.Gamma (t + (1 - c.re)) :=
    (Real.Gamma_pos_of_pos (by linarith [le_abs_self c.re])).le
  calc ‖(Complex.Gamma (a + t))⁻¹‖ * ‖Complex.Gamma (t + b)‖⁻¹ * ‖(Complex.Gamma (c - t))⁻¹‖ *
        ‖(Complex.Gamma (d - t))⁻¹‖
      ≤ (P / Real.Gamma (t + α)) * ‖Complex.Gamma (t + b)‖⁻¹ *
          (Real.Gamma (t + (1 - c.re)) * Ec / π) *
          (‖Complex.Gamma (t + (1 - d))‖ * Ed / π) := by gcongr
    _ = P * Ec * Ed / π ^ 2 *
          (Real.Gamma (t + (1 - c.re)) * (Real.Gamma (t + α))⁻¹) *
          (‖Complex.Gamma (t + (1 - d))‖ * ‖Complex.Gamma (t + b)‖⁻¹) := by
        field_simp
    _ ≤ P * Ec * Ed / π ^ 2 * (K1 * t ^ (1 - c.re - α)) * (K2 * t ^ (1 - d - b).re) := by
        gcongr
    _ = (P * Ec * Ed / π ^ 2 * K1 * K2) *
          t ^ (2 - (a₀.re - ρ) - (b + c + d).re) := by
        rw [← hexp]; ring

/-- The left tail of Ramanujan's integrand (in the reflected form), uniformly for `a` in a
closed disc. -/
theorem left_tail (a₀ b c d : ℂ) (ρ : ℝ) : ∃ K T : ℝ, 0 ≤ K ∧ 0 < T ∧
    ∀ a ∈ Metric.closedBall a₀ ρ, ∀ u : ℝ, T ≤ u →
      ‖ramanujanIntegrand c d a b u‖ ≤ K * u ^ (2 - (a₀.re - ρ) - (b + c + d).re) := by
  set α := a₀.re - ρ with hα
  set Y := |a₀.im| + ρ
  obtain ⟨K3, T3, hK3, hT3, h3⟩ := exists_Gamma_ratio_le (1 - α) c.re
  obtain ⟨K4, T4, hK4, hT4, h4⟩ := exists_norm_Gamma_ratio_le (1 - b) d
  set Pc := Real.sqrt (gammaVertProd 1 |c.im|)
  set Ea := Real.exp (π * Y)
  set Eb := Real.exp (π * |b.im|)
  refine ⟨Pc * Ea * Eb / π ^ 2 * K3 * K4,
    max (max T3 T4) (max (|a₀.re| + |ρ| + 2) (max (|b.re| + 1) (|c.re| + 1))), by positivity,
    by positivity, fun a ha u hu => ?_⟩
  obtain ⟨hre1, hre2, him⟩ := re_im_of_mem_closedBall ha
  have huT3 : T3 ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hu
  have huT4 : T4 ≤ u := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hu
  have hua : |a₀.re| + |ρ| + 2 ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hu
  have hub : |b.re| + 1 ≤ u := le_trans (le_trans (le_trans (le_max_left _ _)
    (le_max_right _ _)) (le_max_right _ _)) hu
  have huc : |c.re| + 1 ≤ u := le_trans (le_trans (le_trans (le_max_right _ _)
    (le_max_right _ _)) (le_max_right _ _)) hu
  have hu0 : 0 < u := by linarith [abs_nonneg c.re]
  have har : a.re + 1 ≤ u := by linarith [le_abs_self a₀.re, le_abs_self ρ]
  have hGc := Real.Gamma_pos_of_pos (show 0 < u + c.re by linarith [neg_abs_le c.re])
  have hA : ‖(Complex.Gamma (a - u))⁻¹‖ ≤ Real.Gamma (u + (1 - α)) * Ea / π := by
    have h := norm_recip_Gamma_le_reflect (z := a - u) (by simp; linarith)
    refine h.trans ?_
    have hre : 0 < (1 - (a - u)).re := by simp; linarith
    have h' := norm_Gamma_le_Gamma_re hre
    simp only [sub_re, one_re, ofReal_re, sub_im, ofReal_im, sub_zero] at h' ⊢
    have hmono : Real.Gamma (1 - (a.re - u)) ≤ Real.Gamma (u + (1 - α)) :=
      Real.Gamma_strictMonoOn_Ici.monotoneOn (mem_Ici.2 (by linarith))
        (mem_Ici.2 (by linarith)) (by linarith)
    have hE : Real.exp (π * |a.im|) ≤ Ea :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left him Real.pi_pos.le)
    have hm := h'.trans hmono
    have hG0 : 0 ≤ Real.Gamma (u + (1 - α)) := (norm_nonneg _).trans hm
    gcongr
  have hB : ‖(Complex.Gamma (b - u))⁻¹‖ ≤ ‖Complex.Gamma (u + (1 - b))‖ * Eb / π := by
    have h := norm_recip_Gamma_le_reflect (z := b - u) (by simp; linarith [le_abs_self b.re])
    rw [show (1 : ℂ) - (b - u) = u + (1 - b) by ring] at h
    simpa using h
  have hC : ‖(Complex.Gamma (c + u))⁻¹‖ ≤ Pc / Real.Gamma (u + c.re) := by
    have h := norm_recip_Gamma_le_of_re (z := c + u) (Y := |c.im|)
      (by simp; linarith [neg_abs_le c.re]) (by simp)
    simpa [add_comm] using h
  have hD : ‖(Complex.Gamma (d + u))⁻¹‖ = ‖Complex.Gamma (u + d)‖⁻¹ := by
    rw [norm_inv, add_comm]
  have hq3 : Real.Gamma (u + (1 - α)) * (Real.Gamma (u + c.re))⁻¹ ≤ K3 * u ^ (1 - α - c.re) :=
    mul_recip_le_of_le_mul (by positivity) hGc.le (h3 u huT3)
  have hq4 : ‖Complex.Gamma (u + (1 - b))‖ * ‖Complex.Gamma (u + d)‖⁻¹ ≤
      K4 * u ^ (1 - b - d).re :=
    mul_recip_le_of_le_mul (by positivity) (norm_nonneg _) (h4 u huT4)
  have hexp : u ^ (1 - α - c.re) * u ^ (1 - b - d).re =
      u ^ (2 - (a₀.re - ρ) - (b + c + d).re) := by
    rw [← Real.rpow_add hu0]; congr 1; simp [hα]; ring
  have hGa : 0 ≤ Real.Gamma (u + (1 - α)) :=
    (Real.Gamma_pos_of_pos (by linarith)).le
  rw [norm_ramanujanIntegrand, hD]
  calc ‖(Complex.Gamma (c + u))⁻¹‖ * ‖Complex.Gamma (u + d)‖⁻¹ * ‖(Complex.Gamma (a - u))⁻¹‖ *
        ‖(Complex.Gamma (b - u))⁻¹‖
      ≤ (Pc / Real.Gamma (u + c.re)) * ‖Complex.Gamma (u + d)‖⁻¹ *
          (Real.Gamma (u + (1 - α)) * Ea / π) *
          (‖Complex.Gamma (u + (1 - b))‖ * Eb / π) := by gcongr
    _ = Pc * Ea * Eb / π ^ 2 *
          (Real.Gamma (u + (1 - α)) * (Real.Gamma (u + c.re))⁻¹) *
          (‖Complex.Gamma (u + (1 - b))‖ * ‖Complex.Gamma (u + d)‖⁻¹) := by
        field_simp
    _ ≤ Pc * Ea * Eb / π ^ 2 * (K3 * u ^ (1 - α - c.re)) * (K4 * u ^ (1 - b - d).re) := by
        gcongr
    _ = Pc * Ea * Eb / π ^ 2 * K3 * K4 * u ^ (2 - (a₀.re - ρ) - (b + c + d).re) := by
        rw [← hexp]; ring

theorem continuous_ramanujanIntegrand_uncurry (b c d : ℂ) :
    Continuous fun p : ℂ × ℝ => ramanujanIntegrand p.1 b c d p.2 := by
  have hg : Continuous fun s : ℂ => (Complex.Gamma s)⁻¹ := differentiable_recip_Gamma.continuous
  have e : (fun p : ℂ × ℝ => ramanujanIntegrand p.1 b c d p.2) = fun p : ℂ × ℝ =>
      (Complex.Gamma (p.1 + p.2))⁻¹ * (Complex.Gamma (b + p.2))⁻¹ *
        (Complex.Gamma (c - p.2))⁻¹ * (Complex.Gamma (d - p.2))⁻¹ := by
    funext p; simp only [ramanujanIntegrand, one_div, mul_inv]
  rw [e]
  have h1 := hg.comp (by fun_prop : Continuous fun p : ℂ × ℝ => p.1 + (p.2 : ℂ))
  have h2 := hg.comp (by fun_prop : Continuous fun p : ℂ × ℝ => b + (p.2 : ℂ))
  have h3 := hg.comp (by fun_prop : Continuous fun p : ℂ × ℝ => c - (p.2 : ℂ))
  have h4 := hg.comp (by fun_prop : Continuous fun p : ℂ × ℝ => d - (p.2 : ℂ))
  exact ((h1.mul h2).mul h3).mul h4

theorem ramanujanIntegrand_eq_mul (a b c d : ℂ) (t : ℝ) :
    ramanujanIntegrand a b c d t = (Complex.Gamma (a + t))⁻¹ *
      (1 / (Complex.Gamma (b + t) * Complex.Gamma (c - t) * Complex.Gamma (d - t))) := by
  simp only [ramanujanIntegrand, one_div, mul_inv]; ring

/-- **Ramanujan's integral is holomorphic in `a`** on the half-plane `re(a+b+c+d) > 3`. -/
theorem differentiableOn_integral_ramanujanIntegrand (b c d : ℂ) :
    DifferentiableOn ℂ (fun a : ℂ => ∫ t : ℝ, ramanujanIntegrand a b c d t)
      {a | 3 < (a + b + c + d).re} := by
  intro a₀ ha₀
  change 3 < (a₀ + b + c + d).re at ha₀
  set r : ℝ := ((a₀ + b + c + d).re - 3) / 8 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  set ρ : ℝ := 2 * r with hρ
  obtain ⟨Kp, Tp, hKp, hTp, hp⟩ := right_tail a₀ b c d ρ
  obtain ⟨Km, Tm, hKm, hTm, hm⟩ := left_tail a₀ b c d ρ
  set e : ℝ := 2 - (a₀.re - ρ) - (b + c + d).re with he_def
  have he : e < -1 := by
    have : (a₀ + b + c + d).re = a₀.re + (b + c + d).re := by simp; ring
    rw [he_def, hρ]; linarith
  set T : ℝ := max Tp Tm with hT
  have hT0 : 0 < T := lt_max_of_lt_left hTp
  -- the compact middle part
  obtain ⟨K₀', hK₀'⟩ := (((isCompact_closedBall a₀ ρ).prod
    isCompact_Icc).exists_bound_of_continuousOn
    (continuous_ramanujanIntegrand_uncurry b c d).continuousOn :
    ∃ K, ∀ p ∈ Metric.closedBall a₀ ρ ×ˢ Icc (-T) T, ‖ramanujanIntegrand p.1 b c d p.2‖ ≤ K)
  set K₀ := max K₀' 0
  set φ : ℝ → ℝ := (Ici T).indicator fun t => t ^ e with hφ
  have hφi : Integrable φ := by
    rw [hφ, integrable_indicator_iff measurableSet_Ici]
    exact (integrableOn_Ici_iff_integrableOn_Ioi (by simp)).2 (integrableOn_Ioi_rpow_of_lt he hT0)
  have hφn : Integrable fun t => φ (-t) := hφi.comp_neg
  have hχ : Integrable ((Icc (-T) T).indicator fun _ : ℝ => K₀) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const (by simp) (by simp)
  set M : ℝ → ℝ := fun t => Kp * φ t + Km * φ (-t) + (Icc (-T) T).indicator (fun _ => K₀) t
  have hM : Integrable M := ((hφi.const_mul Kp).add (hφn.const_mul Km)).add hχ
  have hφ0 : ∀ t, 0 ≤ φ t := fun t => by
    rw [hφ]; by_cases ht : t ∈ Ici T
    · rw [indicator_of_mem ht]; exact Real.rpow_nonneg (hT0.le.trans ht) _
    · rw [indicator_of_notMem ht]
  have hχ0 : ∀ t, 0 ≤ (Icc (-T) T).indicator (fun _ : ℝ => K₀) t := fun t => by
    by_cases ht : t ∈ Icc (-T) T
    · rw [indicator_of_mem ht]; exact le_max_right _ _
    · rw [indicator_of_notMem ht]
  have hbound : ∀ a ∈ Metric.closedBall a₀ (2 * r), ∀ t : ℝ,
      ‖(Complex.Gamma (a + t))⁻¹ *
        (1 / (Complex.Gamma (b + t) * Complex.Gamma (c - t) * Complex.Gamma (d - t)))‖ ≤ M t := by
    intro a ha t
    rw [← ramanujanIntegrand_eq_mul]
    have h1 := hφ0 t
    have h2 := hφ0 (-t)
    have h3 := hχ0 t
    by_cases htp : T ≤ t
    · have hb := hp a ha t (le_trans (le_max_left _ _) htp)
      have : φ t = t ^ e := by rw [hφ, indicator_of_mem (mem_Ici.2 htp)]
      simp only [M]
      nlinarith
    by_cases htm : t ≤ -T
    · have hb := hm a ha (-t) (le_trans (le_max_right _ _) (by linarith))
      rw [← ramanujanIntegrand_neg, neg_neg] at hb
      have : φ (-t) = (-t) ^ e := by rw [hφ, indicator_of_mem (mem_Ici.2 (by linarith))]
      simp only [M]
      nlinarith
    · push Not at htp htm
      have hmem : t ∈ Icc (-T) T := ⟨htm.le, htp.le⟩
      have hb := hK₀' (a, t) ⟨ha, hmem⟩
      have : (Icc (-T) T).indicator (fun _ : ℝ => K₀) t = K₀ := indicator_of_mem hmem _
      simp only [M]
      have : K₀' ≤ K₀ := le_max_left _ _
      nlinarith [mul_nonneg hKp h1, mul_nonneg hKm h2]
  have hG : Continuous fun t : ℝ =>
      1 / (Complex.Gamma (b + t) * Complex.Gamma (c - t) * Complex.Gamma (d - t)) := by
    have hg : Continuous fun s : ℂ => (Complex.Gamma s)⁻¹ := differentiable_recip_Gamma.continuous
    have e : (fun t : ℝ => 1 / (Complex.Gamma (b + t) * Complex.Gamma (c - t) *
        Complex.Gamma (d - t))) = fun t : ℝ => (Complex.Gamma (b + t))⁻¹ *
          (Complex.Gamma (c - t))⁻¹ * (Complex.Gamma (d - t))⁻¹ := by
      funext t; simp only [one_div, mul_inv]
    rw [e]
    exact ((hg.comp (by fun_prop)).mul (hg.comp (by fun_prop))).mul (hg.comp (by fun_prop))
  have key := differentiableAt_integral_recip_Gamma_mul hG hr0 hM hbound
  have e2 : (fun a : ℂ => ∫ t : ℝ, ramanujanIntegrand a b c d t) = fun a : ℂ =>
      ∫ t : ℝ, (Complex.Gamma (a + t))⁻¹ *
        (1 / (Complex.Gamma (b + t) * Complex.Gamma (c - t) * Complex.Gamma (d - t))) := by
    funext a; congr 1; funext t; exact ramanujanIntegrand_eq_mul a b c d t
  rw [e2]
  exact key.differentiableWithinAt


/-- `cos^α` is a.e.-strongly measurable. -/
theorem measurable_cos_rpow (α : ℝ) : Measurable fun x : ℝ => ((Real.cos x ^ α : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp (Real.continuous_cos.measurable.pow_const α)

/-- The integral `∫_{-π/2}^{π/2} cos^α x · e^{iζx} dx` is entire in `ζ`. -/
theorem differentiable_integral_cos_rpow_mul_exp {α : ℝ} (hα : -1 < α) :
    Differentiable ℂ fun ζ : ℂ => ∫ x in (-(π / 2))..(π / 2),
      ((Real.cos x ^ α : ℝ) : ℂ) * Complex.exp (ζ * x * I) := by
  intro ζ₀
  set w : ℝ → ℂ := fun x => ((Real.cos x ^ α : ℝ) : ℂ)
  have hw : IntervalIntegrable (fun x => Real.cos x ^ α) volume (-(π / 2)) (π / 2) :=
    intervalIntegrable_cos_rpow' hα
  set F : ℂ → ℝ → ℂ := fun ζ x => w x * Complex.exp (ζ * x * I) with hF
  set F' : ℂ → ℝ → ℂ := fun ζ x => w x * ((x * I) * Complex.exp (ζ * x * I)) with hF'
  set C : ℝ := π / 2 * Real.exp ((‖ζ₀‖ + 1) * (π / 2))
  have hle : -(π / 2) ≤ π / 2 := by linarith [Real.pi_pos]
  have hexp : ∀ ζ ∈ Metric.ball ζ₀ 1, ∀ x ∈ Ι (-(π / 2)) (π / 2),
      ‖Complex.exp (ζ * x * I)‖ ≤ Real.exp ((‖ζ₀‖ + 1) * (π / 2)) := by
    intro ζ hζ x hx
    rw [uIoc_of_le hle] at hx
    rw [norm_exp]
    apply Real.exp_le_exp.2
    have hz : ‖ζ‖ ≤ ‖ζ₀‖ + 1 := by
      rw [Metric.mem_ball, dist_eq_norm] at hζ
      linarith [norm_le_norm_add_norm_sub' ζ ζ₀]
    have hxa : |x| ≤ π / 2 := abs_le.2 ⟨hx.1.le, hx.2⟩
    have : (ζ * x * I).re = -(ζ.im * x) := by simp
    rw [this]
    calc -(ζ.im * x) ≤ |ζ.im * x| := neg_le_abs _
      _ = |ζ.im| * |x| := abs_mul _ _
      _ ≤ (‖ζ₀‖ + 1) * (π / 2) :=
          mul_le_mul ((abs_im_le_norm ζ).trans hz) hxa (abs_nonneg _) (by positivity)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F)
    (F' := F') (bound := fun x => C * Real.cos x ^ α) (Metric.ball_mem_nhds ζ₀ one_pos)
    (Eventually.of_forall fun ζ => ((measurable_cos_rpow α).mul (by fun_prop :
      Measurable fun x : ℝ => Complex.exp (ζ * x * I))).aestronglyMeasurable)
    (by
      refine (intervalIntegrable_ofReal hw).mul_continuousOn ?_
      exact (by fun_prop : Continuous fun x : ℝ => Complex.exp (ζ₀ * x * I)).continuousOn)
    (((measurable_cos_rpow α).mul (by fun_prop : Measurable fun x : ℝ =>
      ((x : ℂ) * I) * Complex.exp (ζ₀ * x * I))).aestronglyMeasurable)
    (Eventually.of_forall fun x hx ζ hζ => by
      simp only [hF', norm_mul, norm_real, Real.norm_eq_abs, norm_I, mul_one]
      have h1 := hexp ζ hζ x hx
      rw [uIoc_of_le hle] at hx
      have hxa : |x| ≤ π / 2 := abs_le.2 ⟨hx.1.le, hx.2⟩
      have hc : 0 ≤ Real.cos x ^ α := Real.rpow_nonneg (Real.cos_nonneg_of_mem_Icc
        ⟨hx.1.le, hx.2⟩) _
      have hwx : ‖w x‖ = Real.cos x ^ α := by
        simp only [w, norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
      rw [hwx]
      calc Real.cos x ^ α * (|x| * ‖Complex.exp (ζ * x * I)‖)
          ≤ Real.cos x ^ α * (π / 2 * Real.exp ((‖ζ₀‖ + 1) * (π / 2))) := by gcongr
        _ = C * Real.cos x ^ α := by ring)
    (hw.const_mul C)
    (Eventually.of_forall fun x _ ζ _ => by
      have h := (((hasDerivAt_id ζ).mul_const ((x : ℂ) * I)).cexp).const_mul (w x)
      simpa [hF, hF', mul_assoc, mul_comm, mul_left_comm] using h)
  exact key.2.differentiableAt

/-- The Cauchy-type integral `∫_{-π/2}^{π/2} cos^α x e^{iζx} dx` for all complex `ζ`. -/
theorem integral_cos_rpow_mul_cexp {α : ℝ} (hα : -1 < α) (ζ : ℂ) :
    ∫ x in (-(π / 2))..(π / 2), ((Real.cos x ^ α : ℝ) : ℂ) * Complex.exp (ζ * x * I) =
      ((π * Real.Gamma (α + 1) / 2 ^ α : ℝ) : ℂ) *
        ((Complex.Gamma (1 + α / 2 + ζ / 2))⁻¹ * (Complex.Gamma (1 + α / 2 - ζ / 2))⁻¹) := by
  have hL := differentiable_integral_cos_rpow_mul_exp hα
  have hR : Differentiable ℂ fun ζ : ℂ => ((π * Real.Gamma (α + 1) / 2 ^ α : ℝ) : ℂ) *
      ((Complex.Gamma (1 + α / 2 + ζ / 2))⁻¹ * (Complex.Gamma (1 + α / 2 - ζ / 2))⁻¹) := by
    have hg := differentiable_recip_Gamma
    exact ((hg.comp (by fun_prop)).mul (hg.comp (by fun_prop))).const_mul _
  refine (AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq (z₀ := 0)
    (hL.differentiableOn.analyticOnNhd isOpen_univ)
    (hR.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (mem_univ 0) ?_
    (mem_univ ζ))
  have hev : ∀ᶠ b : ℝ in 𝓝[≠] 0,
      (∫ x in (-(π / 2))..(π / 2), ((Real.cos x ^ α : ℝ) : ℂ) * Complex.exp ((b : ℂ) * x * I)) =
      ((π * Real.Gamma (α + 1) / 2 ^ α : ℝ) : ℂ) *
        ((Complex.Gamma (1 + α / 2 + (b : ℂ) / 2))⁻¹ *
          (Complex.Gamma (1 + α / 2 - (b : ℂ) / 2))⁻¹) := by
    have hnhd : ∀ᶠ b : ℝ in 𝓝 0, |b| < α + 2 := by
      have : Metric.ball (0 : ℝ) (α + 2) ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 (by linarith)
      filter_upwards [this] with b hb
      simpa [Metric.mem_ball, Real.dist_eq] using hb
    filter_upwards [nhdsWithin_le_nhds hnhd] with b hb
    have h1 := integral_cos_rpow_mul_exp hα b
    have h2 := integral_cos_rpow_mul_cos (a := α + 1) (b := b) (by linarith) (by linarith)
    simp only [show α + 1 - 1 = α by ring] at h2
    have e1 : ∀ x : ℝ, Complex.exp ((b : ℂ) * x * I) = Complex.exp (↑(b * x) * I) := by
      intro x; push_cast; ring_nf
    simp_rw [e1, h1, h2]
    have g1 : 0 < Real.Gamma ((α + 1 + b + 1) / 2) := Real.Gamma_pos_of_pos (by
      linarith [neg_abs_le b])
    have g2 : 0 < Real.Gamma ((α + 1 - b + 1) / 2) := Real.Gamma_pos_of_pos (by
      linarith [le_abs_self b])
    have c1 : Complex.Gamma (1 + α / 2 + (b : ℂ) / 2) = Real.Gamma ((α + 1 + b + 1) / 2) := by
      rw [← Complex.Gamma_ofReal]; congr 1; push_cast; ring
    have c2 : Complex.Gamma (1 + α / 2 - (b : ℂ) / 2) = Real.Gamma ((α + 1 - b + 1) / 2) := by
      rw [← Complex.Gamma_ofReal]; congr 1; push_cast; ring
    rw [c1, c2, Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0)]
    push_cast
    field_simp
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) :=
    Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun x hx => by
      simpa using hx
  exact ht.frequently hev.frequently


/-- Integrability on `ℝ` from continuity and `O(|t|^e)` tails with `e < -1`. -/
theorem integrable_of_tails {f : ℝ → ℂ} (hf : Continuous f) {K T e : ℝ} (hT : 0 < T)
    (he : e < -1) (hp : ∀ t : ℝ, T ≤ t → ‖f t‖ ≤ K * t ^ e)
    (hm : ∀ t : ℝ, T ≤ t → ‖f (-t)‖ ≤ K * t ^ e) : Integrable f := by
  set φ : ℝ → ℝ := (Ici T).indicator fun t => K * t ^ e with hφ
  have hφi : Integrable φ := by
    rw [hφ, integrable_indicator_iff measurableSet_Ici]
    exact ((integrableOn_Ici_iff_integrableOn_Ioi (by simp)).2
      (integrableOn_Ioi_rpow_of_lt he hT)).const_mul K
  have h1 : IntegrableOn f (Ici T) := by
    refine Integrable.mono' (hφi.integrableOn) hf.aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ici).2 (Eventually.of_forall fun t ht => ?_)
    rw [hφ, indicator_of_mem ht]; exact hp t ht
  have h2 : IntegrableOn f (Iic (-T)) := by
    refine Integrable.mono' ((hφi.comp_neg).integrableOn) hf.aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' measurableSet_Iic).2 (Eventually.of_forall fun t ht => ?_)
    have ht' : -t ∈ Ici T := by simp at ht ⊢; linarith
    rw [hφ, indicator_of_mem ht']
    simpa using hm (-t) ht'
  have h3 : IntegrableOn f (Icc (-T) T) := hf.continuousOn.integrableOn_compact isCompact_Icc
  have hU : Iic (-T) ∪ Icc (-T) T ∪ Ici T = univ := by
    ext t; simp only [mem_union, mem_Iic, mem_Icc, mem_Ici, mem_univ, iff_true]
    by_cases h : t ≤ -T
    · exact Or.inl (Or.inl h)
    · by_cases h' : T ≤ t
      · exact Or.inr h'
      · exact Or.inl (Or.inr ⟨by linarith, by linarith⟩)
  rw [← integrableOn_univ, ← hU]
  exact (h2.union h3).union h1

/-- The two-factor product `1/(Γ(b+x)Γ(d-x))` is integrable when `re(b+d) > 2`. -/
theorem integrable_recip_Gamma_mul_recip_Gamma {b d : ℂ} (h : 2 < (b + d).re) :
    Integrable fun x : ℝ => (Complex.Gamma (b + x))⁻¹ * (Complex.Gamma (d - x))⁻¹ := by
  have hg : Continuous fun s : ℂ => (Complex.Gamma s)⁻¹ := differentiable_recip_Gamma.continuous
  obtain ⟨K1, T1, hK1, hT1, h1⟩ := exists_norm_Gamma_ratio_le (1 - d) b
  obtain ⟨K2, T2, hK2, hT2, h2⟩ := exists_norm_Gamma_ratio_le (1 - b) d
  set e : ℝ := 1 - (b + d).re
  have he : e < -1 := by simp only [e]; linarith
  set Eb := Real.exp (π * |b.im|)
  set Ed := Real.exp (π * |d.im|)
  refine integrable_of_tails ((hg.comp (by fun_prop)).mul (hg.comp (by fun_prop)))
    (K := K1 * Ed / π + K2 * Eb / π) (T := max (max T1 T2) (max (|b.re| + 1) (|d.re| + 1)))
    (by positivity) he ?_ ?_
  · intro t ht
    have htT : T1 ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
    have htd : |d.re| + 1 ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
    have ht0 : 0 < t := by linarith [abs_nonneg d.re]
    have hD := norm_recip_Gamma_le_reflect (z := d - t) (by simp; linarith [le_abs_self d.re])
    rw [show (1 : ℂ) - (d - t) = t + (1 - d) by ring] at hD
    simp only [sub_im, ofReal_im, sub_zero] at hD
    have hq := mul_recip_le_of_le_mul (by positivity) (norm_nonneg _) (h1 t htT)
    have hexp : (1 - d - b).re = e := by simp [e]; ring
    rw [hexp] at hq
    rw [norm_mul, norm_inv, add_comm b]
    calc ‖Complex.Gamma (t + b)‖⁻¹ * ‖(Complex.Gamma (d - t))⁻¹‖
        ≤ ‖Complex.Gamma (t + b)‖⁻¹ * (‖Complex.Gamma (t + (1 - d))‖ * Ed / π) := by gcongr
      _ = Ed / π * (‖Complex.Gamma (t + (1 - d))‖ * ‖Complex.Gamma (t + b)‖⁻¹) := by ring
      _ ≤ Ed / π * (K1 * t ^ e) := by gcongr
      _ ≤ (K1 * Ed / π + K2 * Eb / π) * t ^ e := by
          have : 0 ≤ K2 * Eb / π * t ^ e := by positivity
          have e1 : Ed / π * (K1 * t ^ e) = K1 * Ed / π * t ^ e := by ring
          rw [add_mul]; linarith
  · intro u hu
    have huT : T2 ≤ u := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hu
    have hub : |b.re| + 1 ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hu
    have hu0 : 0 < u := by linarith [abs_nonneg b.re]
    have hB := norm_recip_Gamma_le_reflect (z := b - u) (by simp; linarith [le_abs_self b.re])
    rw [show (1 : ℂ) - (b - u) = u + (1 - b) by ring] at hB
    simp only [sub_im, ofReal_im, sub_zero] at hB
    have hq := mul_recip_le_of_le_mul (by positivity) (norm_nonneg _) (h2 u huT)
    have hexp : (1 - b - d).re = e := by simp [e]; ring
    rw [hexp] at hq
    simp only [ofReal_neg, ← sub_eq_add_neg, sub_neg_eq_add]
    rw [norm_mul, norm_inv (Complex.Gamma (d + u)), add_comm d]
    calc ‖(Complex.Gamma (b - u))⁻¹‖ * ‖Complex.Gamma (u + d)‖⁻¹
        ≤ (‖Complex.Gamma (u + (1 - b))‖ * Eb / π) * ‖Complex.Gamma (u + d)‖⁻¹ := by gcongr
      _ = Eb / π * (‖Complex.Gamma (u + (1 - b))‖ * ‖Complex.Gamma (u + d)‖⁻¹) := by ring
      _ ≤ Eb / π * (K2 * u ^ e) := by gcongr
      _ ≤ (K1 * Ed / π + K2 * Eb / π) * u ^ e := by
          have : 0 ≤ K1 * Ed / π * u ^ e := by positivity
          have e1 : Eb / π * (K2 * u ^ e) = K2 * Eb / π * u ^ e := by ring
          rw [add_mul]; linarith


/-! ### Fourier transforms of the kernels `cos^p φ e^{iζφ}` on `(-π/2, π/2]` -/

/-- The kernel `1_{(-π/2,π/2]}(φ) cos^p φ e^{iζφ}`. -/
def kern (p ζ : ℝ) : ℝ → ℂ := (Ioc (-(π / 2)) (π / 2)).indicator fun φ =>
  ((Real.cos φ ^ p : ℝ) : ℂ) * Complex.exp ((ζ : ℂ) * φ * I)

theorem fourier_kern_eq (p ζ w : ℝ) :
    𝓕 (kern p ζ) w = ∫ x in (-(π / 2))..(π / 2),
      ((Real.cos x ^ p : ℝ) : ℂ) * Complex.exp (((ζ : ℂ) - 2 * π * w) * x * I) := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    ← integral_indicator measurableSet_Ioc]
  congr 1; funext v
  simp only [kern, smul_eq_mul]
  by_cases hv : v ∈ Ioc (-(π / 2)) (π / 2)
  · rw [indicator_of_mem hv, indicator_of_mem hv, mul_left_comm, ← Complex.exp_add]
    congr 2; push_cast; ring
  · rw [indicator_of_notMem hv, indicator_of_notMem hv, mul_zero]

theorem fourier_kern {p : ℝ} (hp : -1 < p) (ζ w : ℝ) :
    𝓕 (kern p ζ) w = ((π * Real.Gamma (p + 1) / 2 ^ p : ℝ) : ℂ) *
      ((Complex.Gamma (1 + p / 2 + ((ζ : ℂ) - 2 * π * w) / 2))⁻¹ *
        (Complex.Gamma (1 + p / 2 - ((ζ : ℂ) - 2 * π * w) / 2))⁻¹) := by
  rw [fourier_kern_eq]; exact integral_cos_rpow_mul_cexp hp _

theorem integrable_kern {p : ℝ} (hp : -1 < p) (ζ : ℝ) : Integrable (kern p ζ) := by
  rw [kern, integrable_indicator_iff measurableSet_Ioc]
  have hle : -(π / 2) ≤ π / 2 := by linarith [Real.pi_pos]
  have hii : IntervalIntegrable (fun x : ℝ => ((Real.cos x ^ p : ℝ) : ℂ) *
      Complex.exp ((ζ : ℂ) * x * I)) volume (-(π / 2)) (π / 2) :=
    (intervalIntegrable_ofReal (intervalIntegrable_cos_rpow' hp)).mul_continuousOn
      (by fun_prop : Continuous fun x : ℝ => Complex.exp ((ζ : ℂ) * x * I)).continuousOn
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).1 hii

theorem continuousAt_kern (p ζ : ℝ) {x : ℝ} (hx : x ∈ Ioo (-(π / 2)) (π / 2)) :
    ContinuousAt (kern p ζ) x := by
  have hcos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo hx
  have hc : ContinuousAt (fun φ : ℝ => ((Real.cos φ ^ p : ℝ) : ℂ) *
      Complex.exp ((ζ : ℂ) * φ * I)) x :=
    (Complex.continuous_ofReal.continuousAt.comp
      ((Real.continuousAt_rpow_const _ _ (Or.inl hcos.ne')).comp
        Real.continuous_cos.continuousAt)).mul
      (by fun_prop : Continuous fun φ : ℝ => Complex.exp ((ζ : ℂ) * φ * I)).continuousAt
  refine hc.congr ?_
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  simp [kern, indicator_of_mem (Ioo_subset_Ioc_self hy)]

theorem fourier_const_mul (C : ℂ) (F : ℝ → ℂ) (x : ℝ) :
    𝓕 (fun ξ => C * F ξ) x = C * 𝓕 F x := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_const_mul]
  congr 1; funext v; simp only [smul_eq_mul]; ring

theorem fourier_zero_eq_integral (F : ℝ → ℂ) : 𝓕 F 0 = ∫ v, F v := by
  rw [Real.fourier_real_eq_integral_exp_smul]; simp

theorem fourier_fourier_kern {p : ℝ} (hp : -1 < p) (ζ : ℝ) (h𝓕 : Integrable (𝓕 (kern p ζ)))
    {x : ℝ} (hx : -x ∈ Ioo (-(π / 2)) (π / 2)) :
    𝓕 (𝓕 (kern p ζ)) x = kern p ζ (-x) := by
  have h := (integrable_kern hp ζ).fourierInv_fourier_eq h𝓕 (continuousAt_kern p ζ hx)
  rw [Real.fourierInv_eq_fourier_neg, neg_neg] at h
  exact h


/-- **Ramanujan's integral for real parameters** with `a + c > 1` and `b + d > 2`, by the
multiplication formula `∫ 𝓕h · G = ∫ h · 𝓕G` and Fourier inversion. -/
theorem integral_ramanujanIntegrand_of_real {a b c d : ℝ} (hac : 1 < a + c) (hbd : 2 < b + d) :
    ∫ t : ℝ, ramanujanIntegrand a b c d t =
      Complex.Gamma (a + b + c + d - 3) /
        (Complex.Gamma (a + c - 1) * Complex.Gamma (a + d - 1) *
          Complex.Gamma (b + c - 1) * Complex.Gamma (b + d - 1)) := by
  set p₁ : ℝ := a + c - 2 with hp₁d
  set ζ₁ : ℝ := c - a with hζ₁d
  set p₂ : ℝ := b + d - 2 with hp₂d
  set ζ₂ : ℝ := d - b with hζ₂d
  have hp₁ : -1 < p₁ := by rw [hp₁d]; linarith
  have hp₂ : -1 < p₂ := by rw [hp₂d]; linarith
  have hP : -1 < p₁ + p₂ := by linarith
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  set C₁ : ℂ := ((π * Real.Gamma (p₁ + 1) / 2 ^ p₁ : ℝ) : ℂ) with hC₁
  set C₂ : ℂ := ((π * Real.Gamma (p₂ + 1) / 2 ^ p₂ : ℝ) : ℂ) with hC₂
  set CP : ℂ := ((π * Real.Gamma (p₁ + p₂ + 1) / 2 ^ (p₁ + p₂) : ℝ) : ℂ) with hCP
  have hC₂0 : C₂ ≠ 0 := by
    rw [hC₂]; exact ofReal_ne_zero.2 (by
      have := Real.Gamma_pos_of_pos (show 0 < p₂ + 1 by linarith)
      positivity)
  have hC₁0 : C₁ ≠ 0 := by
    rw [hC₁]; exact ofReal_ne_zero.2 (by
      have := Real.Gamma_pos_of_pos (show 0 < p₁ + 1 by linarith)
      positivity)
  -- the Fourier transforms of the two kernels
  have hF1 : ∀ w : ℝ, 𝓕 (kern p₁ ζ₁) w = C₁ *
      ((Complex.Gamma (c - π * w))⁻¹ * (Complex.Gamma (a + π * w))⁻¹) := by
    intro w; rw [fourier_kern hp₁]
    congr 4 <;> simp only [hp₁d, hζ₁d] <;> push_cast <;> ring
  have hF2 : ∀ w : ℝ, 𝓕 (kern p₂ ζ₂) w = C₂ *
      ((Complex.Gamma (d - π * w))⁻¹ * (Complex.Gamma (b + π * w))⁻¹) := by
    intro w; rw [fourier_kern hp₂]
    congr 4 <;> simp only [hp₂d, hζ₂d] <;> push_cast <;> ring
  set g : ℝ → ℂ := fun x => (Complex.Gamma (b + x))⁻¹ * (Complex.Gamma (d - x))⁻¹ with hgd
  have hg : Integrable g := integrable_recip_Gamma_mul_recip_Gamma (by simp; linarith)
  set G : ℝ → ℂ := fun ξ => g (π * ξ) with hGd
  have hG : Integrable G := hg.comp_mul_left' Real.pi_ne_zero
  have hFG : 𝓕 (kern p₂ ζ₂) = fun ξ => C₂ * G ξ := by
    funext ξ; rw [hF2]; simp only [hGd, hgd]; push_cast; ring
  have hF2i : Integrable (𝓕 (kern p₂ ζ₂)) := by rw [hFG]; exact hG.const_mul C₂
  have hGeq : G = fun ξ => C₂⁻¹ * 𝓕 (kern p₂ ζ₂) ξ := by
    funext ξ; rw [hFG]; field_simp
  -- the multiplication formula
  have hflip : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by
    ext; simp
  have hmult := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume)
    (ν := volume) (L := innerₗ ℝ) (e := Real.fourierChar) Real.continuous_fourierChar
    continuous_inner (integrable_kern hp₁ ζ₁) hG
  rw [hflip] at hmult
  change ∫ ξ, 𝓕 (kern p₁ ζ₁) ξ • G ξ = ∫ x, kern p₁ ζ₁ x • 𝓕 G x at hmult
  -- the left side
  have hL : ∫ ξ, 𝓕 (kern p₁ ζ₁) ξ • G ξ =
      C₁ * ((π : ℂ)⁻¹ * ∫ t : ℝ, ramanujanIntegrand a b c d t) := by
    have hpt : ∀ ξ : ℝ, 𝓕 (kern p₁ ζ₁) ξ • G ξ =
        C₁ * ramanujanIntegrand a b c d (π * ξ) := by
      intro ξ
      rw [hF1, smul_eq_mul, ramanujanIntegrand_eq_mul]
      simp only [hGd, hgd, one_div, mul_inv]
      push_cast; ring
    simp_rw [hpt]
    rw [integral_const_mul, Measure.integral_comp_mul_left, abs_inv,
      abs_of_pos Real.pi_pos, Complex.real_smul]
    push_cast; ring
  -- the right side
  have hR : ∫ x, kern p₁ ζ₁ x • 𝓕 G x = C₂⁻¹ * ∫ x, kern (p₁ + p₂) (ζ₁ - ζ₂) x := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_real (π / 2)] with x hx
    rw [hGeq, fourier_const_mul, smul_eq_mul]
    by_cases hxo : x ∈ Ioo (-(π / 2)) (π / 2)
    · have hxo' : -x ∈ Ioo (-(π / 2)) (π / 2) := ⟨by linarith [hxo.2], by linarith [hxo.1]⟩
      rw [fourier_fourier_kern hp₂ ζ₂ hF2i hxo']
      have hxc : x ∈ Ioc (-(π / 2)) (π / 2) := Ioo_subset_Ioc_self hxo
      have hxc' : -x ∈ Ioc (-(π / 2)) (π / 2) := Ioo_subset_Ioc_self hxo'
      simp only [kern, indicator_of_mem hxc, indicator_of_mem hxc', Real.cos_neg]
      have hcos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo hxo
      rw [Real.rpow_add hcos]
      push_cast
      have he : Complex.exp (((ζ₁ : ℂ) - ζ₂) * x * I) =
          Complex.exp ((ζ₁ : ℂ) * x * I) * Complex.exp ((ζ₂ : ℂ) * -(x : ℂ) * I) := by
        rw [← Complex.exp_add]; congr 1; ring
      rw [he]
      ring
    · have hxc : x ∉ Ioc (-(π / 2)) (π / 2) := by
        intro h; exact hxo ⟨h.1, lt_of_le_of_ne h.2 hx⟩
      simp only [kern, indicator_of_notMem hxc, zero_mul, mul_zero]
  -- the remaining kernel integral
  have hI : ∫ x, kern (p₁ + p₂) (ζ₁ - ζ₂) x =
      CP * ((Complex.Gamma (b + c - 1))⁻¹ * (Complex.Gamma (a + d - 1))⁻¹) := by
    rw [← fourier_zero_eq_integral, fourier_kern hP]
    congr 4 <;> simp only [hp₁d, hζ₁d, hp₂d, hζ₂d] <;> push_cast <;> ring
  rw [hL, hR, hI] at hmult
  -- solve for the integral
  have hJ : ∫ t : ℝ, ramanujanIntegrand a b c d t =
      π * C₁⁻¹ * C₂⁻¹ * CP * ((Complex.Gamma (b + c - 1))⁻¹ * (Complex.Gamma (a + d - 1))⁻¹) := by
    have := hmult
    field_simp at this ⊢
    linear_combination this
  rw [hJ]
  have g1 : Complex.Gamma (a + c - 1) = Real.Gamma (p₁ + 1) := by
    rw [← Complex.Gamma_ofReal]; congr 1; simp only [hp₁d]; push_cast; ring
  have g2 : Complex.Gamma (b + d - 1) = Real.Gamma (p₂ + 1) := by
    rw [← Complex.Gamma_ofReal]; congr 1; simp only [hp₂d]; push_cast; ring
  have g3 : Complex.Gamma (a + b + c + d - 3) = Real.Gamma (p₁ + p₂ + 1) := by
    rw [← Complex.Gamma_ofReal]; congr 1; simp only [hp₁d, hp₂d]; push_cast; ring
  have hG1 := Real.Gamma_pos_of_pos (show 0 < p₁ + 1 by linarith)
  have hG2 := Real.Gamma_pos_of_pos (show 0 < p₂ + 1 by linarith)
  have h2 : (2 : ℝ) ^ (p₁ + p₂) = 2 ^ p₁ * 2 ^ p₂ := Real.rpow_add (by norm_num) _ _
  rw [g1, g2, g3, hC₁, hC₂, hCP, h2]
  have h2p₁ : (0 : ℝ) < 2 ^ p₁ := by positivity
  have h2p₂ : (0 : ℝ) < 2 ^ p₂ := by positivity
  have c1 : (((2 : ℝ) ^ p₁ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 h2p₁.ne'
  have c2 : (((2 : ℝ) ^ p₂ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 h2p₂.ne'
  push_cast
  field_simp


/-! ### Continuation to complex parameters -/

/-- The right side of 5.13.4. -/
def ramanujanR (a b c d : ℂ) : ℂ :=
  Complex.Gamma (a + b + c + d - 3) /
    (Complex.Gamma (a + c - 1) * Complex.Gamma (a + d - 1) *
      Complex.Gamma (b + c - 1) * Complex.Gamma (b + d - 1))

theorem ramanujanR_swap (a b c d : ℂ) : ramanujanR a b c d = ramanujanR b a c d := by
  simp only [ramanujanR]; ring_nf

theorem ramanujanR_neg (a b c d : ℂ) : ramanujanR a b c d = ramanujanR c d a b := by
  simp only [ramanujanR]; ring_nf

theorem integral_ramanujanIntegrand_swap (a b c d : ℂ) :
    ∫ t : ℝ, ramanujanIntegrand a b c d t = ∫ t : ℝ, ramanujanIntegrand b a c d t := by
  simp_rw [ramanujanIntegrand_swap a b c d]

theorem integral_ramanujanIntegrand_neg (a b c d : ℂ) :
    ∫ t : ℝ, ramanujanIntegrand a b c d t = ∫ t : ℝ, ramanujanIntegrand c d a b t := by
  rw [← integral_neg_eq_self]; simp_rw [ramanujanIntegrand_neg]

theorem differentiableOn_ramanujanR (b c d : ℂ) :
    DifferentiableOn ℂ (fun a : ℂ => ramanujanR a b c d) {a | 3 < (a + b + c + d).re} := by
  intro a ha
  change 3 < (a + b + c + d).re at ha
  have hg := differentiable_recip_Gamma
  have hΓ : DifferentiableAt ℂ (fun a : ℂ => Complex.Gamma (a + b + c + d - 3)) a := by
    refine (Complex.differentiableAt_Gamma _ fun m hm => ?_).comp a (by fun_prop)
    have := congrArg re hm; simp at this
    have : (a + b + c + d).re = a.re + b.re + c.re + d.re := by simp
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have e : (fun a : ℂ => ramanujanR a b c d) = fun a : ℂ => Complex.Gamma (a + b + c + d - 3) *
      ((Complex.Gamma (a + c - 1))⁻¹ * (Complex.Gamma (a + d - 1))⁻¹ *
        (Complex.Gamma (b + c - 1))⁻¹ * (Complex.Gamma (b + d - 1))⁻¹) := by
    funext a; simp only [ramanujanR, div_eq_mul_inv, mul_inv]
  rw [e]
  refine (hΓ.mul ?_).differentiableWithinAt
  exact (((hg.comp (by fun_prop)).mul (hg.comp (by fun_prop))).mul
    (hg.comp (by fun_prop))).mul (hg.comp (by fun_prop)) |>.differentiableAt

/-- Identity theorem on a right half-plane, from agreement on a real half-line. -/
theorem eqOn_of_real_halfline {f g : ℂ → ℂ} {s : ℝ}
    (hf : DifferentiableOn ℂ f {a | s < a.re}) (hg : DifferentiableOn ℂ g {a | s < a.re})
    {x₀ : ℝ} (hx₀ : s ≤ x₀) (hfg : ∀ x : ℝ, x₀ < x → f x = g x) {a : ℂ} (ha : s < a.re) :
    f a = g a := by
  have hU : IsOpen {a : ℂ | s < a.re} := isOpen_lt continuous_const continuous_re
  have hconv : Convex ℝ {a : ℂ | s < a.re} := convex_halfSpace_re_gt s
  have h1 : ((x₀ + 1 : ℝ) : ℂ) ∈ {a : ℂ | s < a.re} := by simp; linarith
  refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq (z₀ := ((x₀ + 1 : ℝ) : ℂ))
    (hf.analyticOnNhd hU) (hg.analyticOnNhd hU) hconv.isPreconnected h1 ?_ ha
  have hev : ∀ᶠ x : ℝ in 𝓝[≠] (x₀ + 1), f x = g x := by
    filter_upwards [nhdsWithin_le_nhds (lt_mem_nhds (show x₀ < x₀ + 1 by linarith))] with x hx
    exact hfg x hx
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (x₀ + 1)) (𝓝[≠] ((x₀ + 1 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun x hx h =>
      hx (Complex.ofReal_injective h)
  exact ht.frequently hev.frequently

theorem halfplane_eq (k : ℂ) : {a : ℂ | 3 < (a + k).re} = {a : ℂ | 3 - k.re < a.re} := by
  ext a
  change 3 < (a + k).re ↔ 3 - k.re < a.re
  rw [add_re]; constructor <;> intro h <;> linarith

/-- One continuation step in the first parameter. -/
theorem ramanujan_step (b c d : ℂ) {x₀ : ℝ} (hx₀ : 3 - (b + c + d).re ≤ x₀)
    (h : ∀ x : ℝ, x₀ < x →
      ∫ t : ℝ, ramanujanIntegrand x b c d t = ramanujanR x b c d)
    {a : ℂ} (ha : 3 < (a + b + c + d).re) :
    ∫ t : ℝ, ramanujanIntegrand a b c d t = ramanujanR a b c d := by
  have e : ∀ a : ℂ, a + b + c + d = a + (b + c + d) := fun a => by ring
  have hset : {a : ℂ | 3 < (a + b + c + d).re} = {a : ℂ | 3 - (b + c + d).re < a.re} := by
    simp_rw [e]; exact halfplane_eq _
  have hf := differentiableOn_integral_ramanujanIntegrand b c d
  have hg := differentiableOn_ramanujanR b c d
  rw [hset] at hf hg
  refine eqOn_of_real_halfline hf hg hx₀ h ?_
  rw [e, add_re] at ha; linarith

end RamanujanAux

open RamanujanAux

@[dlmf 5.13.E4]
theorem mellin_barnes_recip_four {a b c d : ℂ}
    (h : 3 < (a + b + c + d).re) :
    ∫ t : ℝ, 1 /
        (Complex.Gamma (a + t) * Complex.Gamma (b + t) *
          Complex.Gamma (c - t) * Complex.Gamma (d - t)) =
      Complex.Gamma (a + b + c + d - 3) /
        (Complex.Gamma (a + c - 1) * Complex.Gamma (a + d - 1) *
          Complex.Gamma (b + c - 1) * Complex.Gamma (b + d - 1)) := by
  change ∫ t : ℝ, ramanujanIntegrand a b c d t = ramanujanR a b c d
  -- step 1: complex `a`, real `b, c, d` with `b + d > 2`
  have S1 : ∀ (a : ℂ) (b c d : ℝ), 2 < b + d → 3 < (a + b + c + d).re →
      ∫ t : ℝ, ramanujanIntegrand a b c d t = ramanujanR a b c d := by
    intro a b c d hbd ha
    refine ramanujan_step (b : ℂ) c d (x₀ := max (1 - c) (3 - (b + c + d))) ?_ (fun x hx => ?_) ha
    · simp
    · have hx1 : 1 - c < x := lt_of_le_of_lt (le_max_left _ _) hx
      exact integral_ramanujanIntegrand_of_real (by linarith) hbd
  -- step 2: complex `a, b`, real `c, d`
  have S2 : ∀ (a b : ℂ) (c d : ℝ), 3 < (a + b + c + d).re →
      ∫ t : ℝ, ramanujanIntegrand a b c d t = ramanujanR a b c d := by
    intro a b c d hab
    rw [integral_ramanujanIntegrand_swap, ramanujanR_swap]
    refine ramanujan_step a c d (x₀ := max (2 - d) (3 - (a + c + d).re)) ?_ (fun x hx => ?_)
      (by rw [show b + a + c + d = a + b + c + d by ring]; exact hab)
    · simp
    · rw [integral_ramanujanIntegrand_swap, ramanujanR_swap]
      have hx1 : 2 - d < x := lt_of_le_of_lt (le_max_left _ _) hx
      have hx2 : 3 - (a + c + d).re < x := lt_of_le_of_lt (le_max_right _ _) hx
      exact S1 a x c d (by linarith) (by simp at hx2 ⊢; linarith)
  -- step 3: complex `a, b, c`, real `d`
  have S3 : ∀ (a b c : ℂ) (d : ℝ), 3 < (a + b + c + d).re →
      ∫ t : ℝ, ramanujanIntegrand a b c d t = ramanujanR a b c d := by
    intro a b c d habc
    rw [integral_ramanujanIntegrand_neg, ramanujanR_neg]
    refine ramanujan_step (d : ℂ) a b (x₀ := 3 - (d + a + b).re) le_rfl (fun x hx => ?_)
      (by rw [show c + d + a + b = a + b + c + d by ring]; exact habc)
    rw [← integral_ramanujanIntegrand_neg, ← ramanujanR_neg]
    exact S2 a b x d (by simp at hx ⊢; linarith)
  -- step 4: all complex
  rw [integral_ramanujanIntegrand_neg, integral_ramanujanIntegrand_swap, ramanujanR_neg,
    ramanujanR_swap]
  refine ramanujan_step c a b (x₀ := 3 - (c + a + b).re) le_rfl (fun x hx => ?_)
    (by rw [show d + c + a + b = a + b + c + d by ring]; exact h)
  rw [← integral_ramanujanIntegrand_swap, ← ramanujanR_swap, ← integral_ramanujanIntegrand_neg,
    ← ramanujanR_neg]
  exact S3 a b c x (by simp at hx ⊢; linarith)

end Ramanujan

@[dlmf 5.13.E5]
theorem mellin_barnes_selberg {a : Fin 4 → ℂ} (ha : ∀ k, 0 < (a k).re) :
    (1 / (4 * π)) * ∫ t : ℝ,
        (∏ k : Fin 4, Complex.Gamma (a k + I * t) * Complex.Gamma (a k - I * t)) /
          (Complex.Gamma (2 * I * t) * Complex.Gamma (-2 * I * t)) =
      (∏ j : Fin 4, ∏ k : Fin 4, if j.val < k.val then Complex.Gamma (a j + a k) else 1) /
        Complex.Gamma (∑ k : Fin 4, a k) := by
  sorry

/-- `∑ 1/(2j+1)² = π²/8`. -/
theorem hasSum_one_div_odd_sq :
    HasSum (fun j : ℕ => (1 : ℝ) / (2 * j + 1) ^ 2) (π ^ 2 / 8) := by
  set f : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2 with hf
  have h : HasSum f (π ^ 2 / 6) := hasSum_zeta_two
  have he : HasSum (fun j : ℕ => f (2 * j)) (π ^ 2 / 24) := by
    have := h.div_const 4
    rw [show π ^ 2 / 6 / 4 = π ^ 2 / 24 by ring] at this
    refine this.congr_fun fun j => ?_
    simp only [hf]; push_cast
    rcases eq_or_ne j 0 with rfl | hj
    · simp
    · have : (j : ℝ) ≠ 0 := by exact_mod_cast hj
      field_simp; ring
  have hinj : Function.Injective fun j : ℕ => 2 * j + 1 := fun a b h => by
    simp only at h; omega
  have ho : HasSum (fun j : ℕ => f (2 * j + 1)) (∑' j : ℕ, f (2 * j + 1)) :=
    (h.summable.comp_injective hinj).hasSum
  have hval := h.unique (HasSum.even_add_odd (f := f) he ho)
  have ho' : ∑' j : ℕ, f (2 * j + 1) = π ^ 2 / 8 := by linarith
  rw [ho'] at ho
  refine ho.congr_fun fun j => ?_
  simp only [hf]; push_cast; ring

/-- Tail of the trigamma series. -/
theorem tendsto_trigamma_nat_add_one : Tendsto (fun k : ℕ => Real.trigamma (k + 1)) atTop (𝓝 0) := by
  have hs : Summable fun n : ℕ => ((n : ℝ) + 1)⁻¹ ^ 2 := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa [one_div] using this
  refine (tendsto_sum_nat_add fun n : ℕ => ((n : ℝ) + 1)⁻¹ ^ 2).congr fun k => ?_
  rw [Real.trigamma_eq_tsum (by positivity)]
  congr 1; funext n; push_cast; ring_nf


/-- Consecutive trigamma values differ by `1/(k+1)²`. -/
theorem trigamma_succ_sub (k : ℕ) :
    Real.trigamma ((k : ℝ) + 1) - Real.trigamma (((k + 1 : ℕ) : ℝ) + 1) =
      1 / ((k : ℝ) + 1) ^ 2 := by
  have h := trigamma_add_one (x := (k : ℝ) + 1) (by positivity)
  push_cast
  rw [h]; field_simp; ring

/-- Even partial sums of the alternating trigamma series. -/
theorem sum_alternating_trigamma_even (M : ℕ) :
    ∑ k ∈ Finset.range (2 * M), (-1 : ℝ) ^ (k + 1) * Real.trigamma (k + 1) =
      -∑ j ∈ Finset.range M, (1 : ℝ) / (2 * j + 1) ^ 2 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    have hd := trigamma_succ_sub (2 * M)
    have e1 : (-1 : ℝ) ^ (2 * M + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    have e2 : (-1 : ℝ) ^ (2 * M + 1 + 1) = 1 := by rw [pow_succ, e1]; norm_num
    rw [e1, e2]
    push_cast at hd ⊢
    linear_combination -hd

/-- Odd partial sums of the alternating trigamma series. -/
theorem sum_alternating_trigamma_odd (M : ℕ) :
    ∑ k ∈ Finset.range (2 * M + 1), (-1 : ℝ) ^ (k + 1) * Real.trigamma (k + 1) =
      -∑ j ∈ Finset.range M, (1 : ℝ) / (2 * j + 1) ^ 2 - Real.trigamma ((2 * M : ℕ) + 1) := by
  rw [Finset.sum_range_succ, sum_alternating_trigamma_even]
  have e1 : (-1 : ℝ) ^ (2 * M + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
  rw [e1]; push_cast; ring

/-- The alternating trigamma series. It converges only conditionally, so it is stated with
ordered partial sums; Lean's unordered `tsum` of the series would be `0`. -/
@[dlmf 5.16.E1]
theorem sum_alternating_trigamma :
    Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, (-1 : ℝ) ^ (k + 1) * Real.trigamma (k + 1))
      Filter.atTop (nhds (-π ^ 2 / 8)) := by
  set A : ℕ → ℝ := fun M => ∑ j ∈ Finset.range M, (1 : ℝ) / (2 * j + 1) ^ 2
  set E : ℕ → ℝ := fun N => if Even N then 0 else Real.trigamma (((N - 1 : ℕ) : ℝ) + 1)
  have hform : ∀ N, ∑ k ∈ Finset.range N, (-1 : ℝ) ^ (k + 1) * Real.trigamma (k + 1) =
      -A (N / 2) - E N := by
    intro N
    obtain ⟨M, rfl | rfl⟩ := Nat.even_or_odd' N
    · rw [sum_alternating_trigamma_even]
      simp [A, E, show 2 * M / 2 = M by omega]
    · rw [sum_alternating_trigamma_odd]
      simp [A, E, show (2 * M + 1) / 2 = M by omega, Nat.not_even_bit1]
  simp_rw [hform]
  have hA : Tendsto (fun N => A (N / 2)) atTop (𝓝 (π ^ 2 / 8)) :=
    hasSum_one_div_odd_sq.tendsto_sum_nat.comp (Nat.tendsto_div_const_atTop two_ne_zero)
  have hT : Tendsto (fun N : ℕ => Real.trigamma (((N - 1 : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_trigamma_nat_add_one.comp (tendsto_sub_atTop_nat 1)
  have hE : Tendsto E atTop (𝓝 0) := by
    refine squeeze_zero (fun N => ?_) (fun N => ?_) hT
    · simp only [E]; split_ifs
      · exact le_rfl
      · rw [Real.trigamma_eq_tsum (by positivity)]; positivity
    · simp only [E]; split_ifs
      · rw [Real.trigamma_eq_tsum (by positivity)]; positivity
      · exact le_rfl
  have := (hA.neg).sub hE
  simpa [neg_div] using this

section SumTrigamma

open Finset
open scoped ENNReal

/-- `ψ'(k+2) ≤ 1/(k+1)`, by comparison with a telescoping series. -/
theorem trigamma_add_two_le (k : ℕ) : Real.trigamma (k + 2) ≤ 1 / (k + 1) := by
  rw [Real.trigamma_eq_tsum (by positivity)]
  refine Real.tsum_le_of_sum_range_le (fun n => by positivity) fun N => ?_
  have h := Real.sum_recip_sub_recip_range ((k : ℝ) + 1) N
  have hle : ∀ n ∈ range N, ((k : ℝ) + 2 + n)⁻¹ ^ 2 ≤
      ((k : ℝ) + 1 + n)⁻¹ - ((k : ℝ) + 1 + n + 1)⁻¹ := by
    intro n _
    have h1 : (0 : ℝ) < k + 1 + n := by positivity
    rw [show (k : ℝ) + 1 + n + 1 = k + 2 + n by ring, inv_pow, inv_sub_inv h1.ne' (by positivity),
      show (k : ℝ) + 2 + n - (k + 1 + n) = 1 by ring]
    rw [one_div]
    exact inv_anti₀ (by positivity) (by nlinarith)
  refine (sum_le_sum hle).trans ?_
  rw [h, one_div]
  have : (0 : ℝ) ≤ ((k : ℝ) + 1 + N)⁻¹ := by positivity
  linarith

@[dlmf 5.16.E2]
theorem sum_trigamma_div :
    ∑' k : ℕ, (1 / (k + 1 : ℝ)) * Real.trigamma (k + 2) = (riemannZeta 3).re := by
  -- the summand and its ENNReal sum `L`
  set a : ℕ → ℝ := fun k => (1 / (k + 1 : ℝ)) * Real.trigamma (k + 2) with ha
  have ha0 : ∀ k, 0 ≤ a k := fun k => by
    simp only [ha]; rw [Real.trigamma_eq_tsum (by positivity)]; positivity
  have haS : Summable a := by
    refine Summable.of_nonneg_of_le ha0 (fun k => ?_)
      ((Real.summable_one_div_nat_add_rpow 1 2).mpr one_lt_two)
    simp only [ha]
    calc (1 / (k + 1 : ℝ)) * Real.trigamma (k + 2) ≤ (1 / (k + 1)) * (1 / (k + 1)) :=
          mul_le_mul_of_nonneg_left (trigamma_add_two_le k) (by positivity)
      _ = 1 / |(k : ℝ) + 1| ^ (2 : ℝ) := by
          rw [abs_of_pos (by positivity), Real.rpow_two]; field_simp
  set L : ℝ≥0∞ := ∑' k, ENNReal.ofReal (a k) with hL
  -- ζ(3) as a real series
  set z : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) ^ 3 with hz
  have hzS : Summable z := by
    refine ((Real.summable_one_div_nat_add_rpow 1 3).mpr (by norm_num)).congr fun j => ?_
    simp only [hz]; rw [abs_of_pos (by positivity)]; norm_cast
  have hzeta : (riemannZeta 3).re = ∑' j, z j := by
    rw [show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num,
      zeta_eq_tsum_one_div_nat_add_one_cpow (by norm_num)]
    simp only [cpow_natCast]
    rw [show (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ 3) = fun n => ((z n : ℝ) : ℂ) by
      funext n; simp [hz], ← ofReal_tsum, ofReal_re]
  -- the double series over `(p, q)` of `f p q = 1/((p+1)(q+1)(p+q+2))`
  set g : ℕ → ℕ → ℝ := fun p q => 1 / ((p + 1 : ℝ) * ((p : ℝ) + q + 2) ^ 2) with hg
  set f : ℕ → ℕ → ℝ := fun p q => 1 / ((p + 1 : ℝ) * (q + 1) * ((p : ℝ) + q + 2)) with hf
  have hfg : ∀ p q, ENNReal.ofReal (f p q) = ENNReal.ofReal (g p q) + ENNReal.ofReal (g q p) := by
    intro p q
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    simp only [hf, hg]
    field_simp
    ring
  -- symmetry: the double sum is `2 L`
  have hrow : ∀ p : ℕ, ∑' q, ENNReal.ofReal (g p q) = ENNReal.ofReal (a p) := by
    intro p
    have hS := Real.summable_trigamma (by positivity : (0 : ℝ) < p + 2)
    rw [show (fun q => ENNReal.ofReal (g p q)) = fun q : ℕ => ENNReal.ofReal (1 / (p + 1 : ℝ)) *
        ENNReal.ofReal (((p : ℝ) + 2 + q)⁻¹ ^ 2) by
      funext q; rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; simp only [hg]
      field_simp; ring_nf,
      ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hS,
      ← ENNReal.ofReal_mul (by positivity), ← Real.trigamma_eq_tsum (by positivity)]
  have hsym : ∑' p, ∑' q, ENNReal.ofReal (f p q) = 2 * L := by
    simp_rw [hfg, ENNReal.tsum_add]
    rw [ENNReal.tsum_comm (f := fun p q => ENNReal.ofReal (g q p))]
    simp_rw [hrow]
    rw [hL, two_mul]
  -- summing over `q` first gives harmonic numbers
  set c : ℕ → ℕ → ℝ≥0∞ := fun j p => ENNReal.ofReal (1 / ((j + 1 : ℝ) * (p + 1) ^ 2)) with hc
  have hcol : ∀ p : ℕ, ∑' q, ENNReal.ofReal (f p q) = ∑ j ∈ range (p + 1), c j p := by
    intro p
    have hx : (0 : ℝ) < p + 2 := by positivity
    have hT : ∑' n, Real.digammaSeriesTerm ((p : ℝ) + 2) n =
        ∑ j ∈ range (p + 1), 1 / (j + 1 : ℝ) := by
      have h1 := Real.digamma_eq_tsum hx
      have h2 := Real.digamma_nat_add_one (p + 1)
      rw [show ((p + 1 : ℕ) : ℝ) + 1 = (p : ℝ) + 2 by push_cast; ring, h1] at h2
      rw [show ∑ j ∈ range (p + 1), 1 / (j + 1 : ℝ) = (harmonic (p + 1) : ℝ) by
        simp [harmonic]]
      linarith
    have hD0 : ∀ n, 0 ≤ Real.digammaSeriesTerm ((p : ℝ) + 2) n := fun n => by
      simp only [Real.digammaSeriesTerm]
      rw [sub_nonneg]
      exact inv_anti₀ (by positivity) (by linarith)
    rw [show (fun q => ENNReal.ofReal (f p q)) = fun q => ENNReal.ofReal (1 / (p + 1 : ℝ) ^ 2) *
        ENNReal.ofReal (Real.digammaSeriesTerm ((p : ℝ) + 2) q) by
      funext q; rw [← ENNReal.ofReal_mul (by positivity)]; congr 1
      simp only [hf, Real.digammaSeriesTerm]
      field_simp; ring,
      ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg hD0
        (Real.summable_digammaSeriesTerm hx), hT, ← ENNReal.ofReal_mul (by positivity),
      mul_sum, ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
    refine sum_congr rfl fun j _ => ?_
    simp only [hc]; congr 1; field_simp
  -- the triangular interchange gives `ζ(3) + L`
  have hrow2 : ∀ j : ℕ, ∑' p, (if j ≤ p then c j p else 0) =
      ENNReal.ofReal (z j) + ENNReal.ofReal (a j) := by
    intro j
    rw [← Summable.sum_add_tsum_nat_add' (f := fun p => if j ≤ p then c j p else 0) (k := j)
      ENNReal.summable, sum_eq_zero fun i hi => by simp [show ¬ j ≤ i by simpa using hi],
      zero_add]
    simp only [le_add_iff_nonneg_left, zero_le, ite_true]
    rw [show (fun i => c j (i + j)) = fun i : ℕ => ENNReal.ofReal (1 / (j + 1 : ℝ)) *
        ENNReal.ofReal (((j : ℝ) + 1 + i)⁻¹ ^ 2) by
      funext i; simp only [hc]; rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; push_cast
      field_simp; ring,
      ENNReal.tsum_mul_left, tsum_eq_zero_add' ENNReal.summable]
    have hS := Real.summable_trigamma (by positivity : (0 : ℝ) < j + 2)
    rw [show (fun i : ℕ => ENNReal.ofReal (((j : ℝ) + 1 + ((i + 1 : ℕ) : ℝ))⁻¹ ^ 2)) =
        fun i : ℕ => ENNReal.ofReal (((j : ℝ) + 2 + i)⁻¹ ^ 2) by
      funext i; push_cast; ring_nf,
      ← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hS,
      ← Real.trigamma_eq_tsum (by positivity), ← ENNReal.ofReal_add (by positivity)
        (by rw [Real.trigamma_eq_tsum (by positivity)]; positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (ha0 j)]
    congr 1
    simp only [hz, ha]
    push_cast
    field_simp
    ring
  have htri : ∑' p, ∑' q, ENNReal.ofReal (f p q) = ENNReal.ofReal (∑' j, z j) + L := by
    have h1 : ∀ p, ∑ j ∈ range (p + 1), c j p = ∑' j, (if j ≤ p then c j p else 0) := by
      intro p
      rw [tsum_eq_sum (s := range (p + 1)) fun j hj => by
        simp only [mem_range, not_lt] at hj; simp [show ¬ j ≤ p by omega]]
      exact sum_congr rfl fun j hj => by
        simp only [mem_range] at hj; simp [show j ≤ p by omega]
    simp_rw [hcol, h1]
    rw [ENNReal.tsum_comm]
    simp_rw [hrow2]
    rw [ENNReal.tsum_add, ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hzS]
  -- conclude
  have hLfin : L = ENNReal.ofReal (∑' k, a k) := (ENNReal.ofReal_tsum_of_nonneg ha0 haS).symm
  have hLne : L ≠ ∞ := by rw [hLfin]; exact ENNReal.ofReal_ne_top
  have hEq : L = ENNReal.ofReal (∑' j, z j) := by
    have := hsym.symm.trans htri
    rw [two_mul] at this
    exact (ENNReal.add_left_inj hLne).mp this
  rw [hzeta]
  have hz0 : 0 ≤ ∑' j, z j := tsum_nonneg fun j => by positivity
  rw [hLfin] at hEq
  exact (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg ha0) hz0).mp hEq

end SumTrigamma

end DLMF.Gamma
