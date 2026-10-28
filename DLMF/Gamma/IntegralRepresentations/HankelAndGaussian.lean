/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.Digamma
public import DLMF.Gamma.Stirling
public import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import DLMFMathlib.Analysis.Asymptotics.WatsonSector

/-!
# Hankel and Gaussian Gamma representations

Laplace scaling, the reciprocal-Gamma Hankel loop and Gaussian forms of the Gamma integral.

Source references and common attribution are retained in
`DLMF.Gamma.IntegralRepresentations`.
-/

@[expose] public section

open Complex Filter MeasureTheory intervalIntegral

open scoped Real Topology

noncomputable section

namespace DLMF.Gamma

local macro "deriv_simp" : tactic => `(tactic| first
  | (simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply, Pi.div_apply, id_eq];
      field_simp; ring)
  | (simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply, Pi.div_apply, id_eq];
      field_simp; done)
  | (simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply, Pi.div_apply, id_eq];
      ring)
  | (field_simp; ring) | (field_simp; done) | ring | (simp; field_simp; ring) | (simp; done))

/-- The Laplace transform of a power: `∫₀^∞ u^(s-1) e^(-z u) du = Γ(s) z^(-s)` for
`Re s > 0` and `Re z > 0` (proved in `DLMFMathlib.Analysis.Asymptotics.WatsonSector`). -/
theorem integral_cpow_mul_exp_neg_mul_Ioi {s z : ℂ} (hs : 0 < s.re) (hz : 0 < z.re) :
    ∫ u : ℝ in Set.Ioi 0, (u : ℂ) ^ (s - 1) * Complex.exp (-(z * u)) =
      Complex.Gamma s * z ^ (-s) :=
  integral_cpow_mul_cexp_neg_mul_Ioi hs hz

/-- A Laplace-type integral for Gamma. The exponent `μ` must be real, as in DLMF: for
non-real `μ` the factor `exp (-z t ^ μ)` grows along a sequence `t → ∞` and the integral
diverges. -/
@[dlmf 5.9.E1]
theorem Gamma_laplace_power {μ ν z : ℂ} (hμ : 0 < μ.re) (hμi : μ.im = 0) (hν : 0 < ν.re)
    (hz : 0 < z.re) :
    (1 / μ) * Complex.Gamma (ν / μ) * z ^ (-(ν / μ)) =
      ∫ t : ℝ in Set.Ioi 0, Complex.exp (-z * (t : ℂ) ^ μ) * (t : ℂ) ^ (ν - 1) := by
  set m := μ.re with hm
  have hμm : μ = (m : ℂ) := Complex.ext (by simp [hm]) (by simp [hμi])
  have hm0 : (m : ℂ) ≠ 0 := ofReal_ne_zero.mpr hμ.ne'
  have hνμ : 0 < (ν / μ).re := by
    rw [hμm, div_ofReal_re]
    exact div_pos hν hμ
  rw [mul_assoc, ← integral_cpow_mul_exp_neg_mul_Ioi hνμ hz,
    ← integral_comp_rpow_Ioi_of_pos (p := m) hμ, ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  have hcpow (x : ℝ) (hx : 0 < x) (w : ℂ) :
      (x : ℂ) ^ w = Complex.exp (Real.log x * w) := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), ofReal_log hx.le]
  have hT : ((t ^ m : ℝ) : ℂ) = (t : ℂ) ^ μ := by rw [ofReal_cpow ht0.le, hμm]
  rw [hcpow (t ^ m) (Real.rpow_pos_of_pos ht0 m), Real.log_rpow ht0, hT,
    Real.rpow_def_of_pos ht0, hcpow t ht0 (ν - 1), Complex.real_smul, ofReal_mul, ofReal_exp, hμm]
  rw [show ∀ A B C : ℂ, 1 / (m : ℂ) * ((m : ℂ) * A * (B * C)) = (1 / (m : ℂ) * (m : ℂ)) *
      (A * B) * C from fun A B C => by ring, one_div_mul_cancel hm0, one_mul,
    ← Complex.exp_add, neg_mul, mul_comm (Complex.exp _) (Complex.exp _)]
  congr 2
  push_cast
  field_simp
  ring

/-- Binet's integrand. -/
@[dlmf 5.9.E2_5]
def binetPhi (t : ℝ) : ℝ :=
  1 - t * Real.cot t + Real.log (t / Real.sin t)

section BinetLoop

/-!
### Binet's loop integral for `1/Γ` (DLMF 5.9.2 on the steepest-descent path)

Hankel's loop integral `1/Γ(a) = (1/2πi) ∫ e^w w^{-a} dw` is taken along the path
`w = θ e^{iθ}/sin θ`, `-π < θ < π`, on which `e^{a w} w^{-a}` is real. By the symmetry
`θ ↦ -θ` only the upper half `0 < θ < π` is needed, and only imaginary parts. We never
deform contours: in the logarithmic coordinate `log w = log(θ/sin θ) + iθ`
(`binetPathLog`) the integrand `e^{c w} w^{b} d(log w)` (`binetPathTerm`) is explicit.
* Integration by parts gives `c P(b+1, c) + b P(b, c) = -e^c` (`binetPathInt_rec`).
* Differentiation in the scale `c` gives `∂_c P(b, c) = P(b+1, c)`. Together with the
  recursion, `c^b Im P(b, c)` does not depend on `c > 0` (`binetPathIm_scale`), which
  replaces the dilation `w ↦ c w` of the path.
* At `c = a`, `b = 1 - a` the imaginary part of the integrand is `e^{a} e^{-a φ(θ)}`
  (`im_binetPathTerm`).
* Hence `W(a) = Im P(1-a, 1)` satisfies `W(a) = a W(a+1)` and
  `W(a) = a^{1-a} e^a ∫₀^π e^{-aφ}`, so `W Γ` is `1`-periodic. Laplace's method
  (`tendsto_sqrt_mul_binetLaplace`, by dominated convergence after `θ = s/√x`) and
  Stirling's formula give `W Γ → π` along `a + n`, so `W Γ = π`.
-/

open Set

/-- `sin θ - θ cos θ ≥ 0` on `[0, π]`. -/
theorem binetPath_m_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ ≤ π) :
    0 ≤ Real.sin θ - θ * Real.cos θ := by
  rcases lt_or_ge θ (π / 2) with h | h
  · have ht := Real.le_tan h0 h
    have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, h⟩
    rw [Real.tan_eq_sin_div_cos, le_div_iff₀ hc] at ht
    linarith
  · have hc : Real.cos θ ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le h (by linarith)
    have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h0 hπ
    nlinarith

/-- `x ↦ sin x - x cos x` has derivative `θ sin θ` at `θ`. -/
theorem binetPath_hasDerivAt_m (θ : ℝ) :
    HasDerivAt (fun x : ℝ => Real.sin x - x * Real.cos x) (θ * Real.sin θ) θ := by
  have := (Real.hasDerivAt_sin θ).sub ((hasDerivAt_id' θ).mul (Real.hasDerivAt_cos θ))
  convert this using 1
  ring

/-- `sin θ - θ cos θ ≤ θ³/3` for `θ ≥ 0`. -/
theorem binetPath_m_le {θ : ℝ} (h0 : 0 ≤ θ) :
    Real.sin θ - θ * Real.cos θ ≤ θ ^ 3 / 3 := by
  have hmono : MonotoneOn (fun x : ℝ => x ^ 3 / 3 - (Real.sin x - x * Real.cos x)) (Ici 0) := by
    have hd : ∀ x, HasDerivAt (fun x : ℝ => x ^ 3 / 3 - (Real.sin x - x * Real.cos x))
        (x ^ 2 - x * Real.sin x) x := by
      intro x
      have := ((hasDerivAt_pow 3 x).div_const 3).sub (binetPath_hasDerivAt_m x)
      convert this using 1
      push_cast; ring
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [interior_Ici] at hx
    rw [(hd x).deriv]
    have := Real.sin_le (le_of_lt hx)
    have hx' : 0 < x := hx
    nlinarith
  have := hmono (self_mem_Ici) h0 h0
  simp at this
  linarith

/-- `1 - θ cot θ ≥ θ²/3`, in the form `sin θ - θ cos θ ≥ (θ²/3) sin θ`, on `[0, π]`. -/
theorem binetPath_k_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ ≤ π) :
    θ ^ 2 / 3 * Real.sin θ ≤ Real.sin θ - θ * Real.cos θ := by
  have hmono : MonotoneOn
      (fun x : ℝ => Real.sin x - x * Real.cos x - x ^ 2 / 3 * Real.sin x) (Icc 0 π) := by
    have hd : ∀ x, HasDerivAt
        (fun x : ℝ => Real.sin x - x * Real.cos x - x ^ 2 / 3 * Real.sin x)
        (x / 3 * (Real.sin x - x * Real.cos x)) x := by
      intro x
      have := (binetPath_hasDerivAt_m x).sub
        (((hasDerivAt_pow 2 x).div_const 3).mul (Real.hasDerivAt_sin x))
      convert this using 1
      push_cast; ring
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 π)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hd x).deriv]
    exact mul_nonneg (by linarith [hx.1]) (binetPath_m_nonneg hx.1.le hx.2.le)
  have := hmono ⟨le_rfl, Real.pi_pos.le⟩ ⟨h0, hπ⟩ h0
  simp at this
  linarith

/-- `θ / sin θ ≤ π² / (2 (π - θ))` on `(0, π)`. -/
theorem binetPath_div_sin_le {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    θ / Real.sin θ ≤ π ^ 2 / (2 * (π - θ)) := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have hsin : 2 / π * (θ * (π - θ) / π) ≤ Real.sin θ := by
    rcases le_or_gt θ (π / 2) with h | h
    · have := Real.mul_le_sin h0.le h
      have : θ * (π - θ) / π ≤ θ := by
        rw [div_le_iff₀ Real.pi_pos]; nlinarith
      calc 2 / π * (θ * (π - θ) / π) ≤ 2 / π * θ := by gcongr
        _ ≤ _ := ‹2 / π * θ ≤ Real.sin θ›
    · have h1 := Real.mul_le_sin (x := π - θ) (by linarith) (by linarith)
      rw [Real.sin_pi_sub] at h1
      have : θ * (π - θ) / π ≤ π - θ := by
        rw [div_le_iff₀ Real.pi_pos]; nlinarith
      calc 2 / π * (θ * (π - θ) / π) ≤ 2 / π * (π - θ) := by gcongr
        _ ≤ _ := h1
  rw [div_le_div_iff₀ hs (by nlinarith [Real.pi_pos])]
  have hp := Real.pi_pos
  have : 2 / π * (θ * (π - θ) / π) = 2 * θ * (π - θ) / π ^ 2 := by field_simp
  rw [this, div_le_iff₀ (by positivity)] at hsin
  nlinarith

/-- `θ cot θ ≤ 2 - (π/3)/(π - θ)` on `(0, π)`. -/
theorem binetPath_mul_cot_le {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    θ * Real.cot θ ≤ 2 - π / 3 / (π - θ) := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have ht : 0 < π - θ := by linarith
  have hp4 := Real.pi_le_four
  have hp0 := Real.pi_pos
  rw [Real.cot_eq_cos_div_sin]
  rcases le_or_gt θ (2 * π / 3) with h | h
  · have hm := binetPath_m_nonneg h0.le hπ.le
    have h1 : θ * (Real.cos θ / Real.sin θ) ≤ 1 := by
      rw [← mul_div_assoc, div_le_one hs]; linarith
    have h2 : π / 3 / (π - θ) ≤ 1 := by
      rw [div_le_one ht]; linarith
    linarith
  · set t := π - θ with htdef
    have hst : Real.sin θ = Real.sin t := by rw [htdef, Real.sin_pi_sub]
    have hct : Real.cos θ = -Real.cos t := by rw [htdef, Real.cos_pi_sub]; ring
    have hsint : Real.sin t ≤ t := Real.sin_le ht.le
    have hcost : 1 - t ^ 2 / 2 ≤ Real.cos t := Real.one_sub_sq_div_two_le_cos
    have htle : t < π / 3 := by linarith
    have hcot : Real.cos θ / Real.sin θ ≤ -1 / t + t / 2 := by
      rw [hst, hct]
      have hnum : -Real.cos t ≤ -1 + t ^ 2 / 2 := by linarith
      have hneg : -1 + t ^ 2 / 2 < 0 := by nlinarith
      have hst0 : 0 < Real.sin t := by rw [← hst]; exact hs
      calc -Real.cos t / Real.sin t ≤ (-1 + t ^ 2 / 2) / Real.sin t := by gcongr
        _ ≤ (-1 + t ^ 2 / 2) / t := by
          rw [div_le_div_iff₀ hst0 ht]; nlinarith
        _ = -1 / t + t / 2 := by field_simp
    have hcneg : Real.cos θ / Real.sin θ ≤ 0 := by
      have : Real.cos θ ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
      exact div_nonpos_of_nonpos_of_nonneg this hs.le
    have h1 : θ * (Real.cos θ / Real.sin θ) ≤ 2 * π / 3 * (Real.cos θ / Real.sin θ) :=
      mul_le_mul_of_nonpos_right h.le hcneg
    have h2 : 2 * π / 3 * (-1 / t + t / 2) = -(2 * (π / 3 / t)) + π / 3 * t := by
      field_simp
    have h3 : π / 3 * t ≤ 2 := by nlinarith
    have h4 : 0 ≤ π / 3 / t := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hcot (by positivity : (0:ℝ) ≤ 2 * π / 3)]

/-- Where `sin θ ≠ 0`, `φ(θ) = (sin θ - θ cos θ)/sin θ + log(θ/sin θ)` for the Binet phase `φ(θ) = 1
- θ cot θ + log(θ/sin θ)`. -/
theorem binetPhi_eq {θ : ℝ} (hs : Real.sin θ ≠ 0) :
    binetPhi θ = (Real.sin θ - θ * Real.cos θ) / Real.sin θ + Real.log (θ / Real.sin θ) := by
  rw [binetPhi, Real.cot_eq_cos_div_sin]
  field_simp

/-- `binetPhi θ ≥ θ²/3` on `(0, π)`. -/
theorem binetPhi_ge {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) : θ ^ 2 / 3 ≤ binetPhi θ := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  rw [binetPhi_eq hs.ne']
  have h1 : θ ^ 2 / 3 ≤ (Real.sin θ - θ * Real.cos θ) / Real.sin θ := by
    rw [le_div_iff₀ hs]; exact binetPath_k_nonneg h0.le hπ.le
  have h2 : 0 ≤ Real.log (θ / Real.sin θ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hs, one_mul]; exact Real.sin_le h0.le)
  linarith

/-- The quadratic behaviour of `binetPhi` at `0`: `|binetPhi θ - θ²/2| ≤ θ⁴/2` on `(0, 1]`. -/
theorem abs_binetPhi_sub_le {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ 1) :
    |binetPhi θ - θ ^ 2 / 2| ≤ θ ^ 4 / 2 := by
  have hab : |θ| ≤ 1 := by rw [abs_of_pos h0]; exact h1
  have hsb := Real.sin_bound hab
  have hcb := Real.cos_bound hab
  rw [abs_of_pos h0] at hsb hcb
  set s := Real.sin θ with hsdef
  set c := Real.cos θ with hcdef
  set e2 := s - (θ - θ ^ 3 / 6) with he2
  set e3 := c - (1 - θ ^ 2 / 2) with he3
  have he2b := abs_le.mp hsb
  have he3b := abs_le.mp hcb
  have hθ4 : θ ^ 4 ≤ θ ^ 2 := by nlinarith [pow_pos h0 2]
  have hθ5 : θ ^ 5 ≤ θ ^ 4 := by nlinarith [pow_pos h0 4]
  have hθ3 : θ ^ 3 ≤ θ := by nlinarith [pow_pos h0 2]
  have hs_lo : θ / 2 ≤ s := by nlinarith
  have hs_pos : 0 < s := by linarith
  have hs_le : s ≤ θ := Real.sin_le h0.le
  rw [binetPhi_eq hs_pos.ne']
  -- the `A` part
  have hA : |(s - θ * c) / s - θ ^ 2 / 3| ≤ 2 * θ ^ 4 / 5 := by
    have hnum : |s - θ * c - θ ^ 2 / 3 * s| ≤ θ ^ 5 / 5 := by
      have : s - θ * c - θ ^ 2 / 3 * s = e2 - θ * e3 + θ ^ 5 / 18 - θ ^ 2 / 3 * e2 := by
        rw [he2, he3]; ring
      rw [this, abs_le]
      constructor <;> nlinarith [pow_pos h0 2, pow_pos h0 5]
    have : (s - θ * c) / s - θ ^ 2 / 3 = (s - θ * c - θ ^ 2 / 3 * s) / s := by
      field_simp
    rw [this, abs_div, abs_of_pos hs_pos, div_le_iff₀ hs_pos]
    nlinarith [abs_nonneg (s - θ * c - θ ^ 2 / 3 * s), pow_pos h0 4]
  -- the `B` part
  set u := 1 - s / θ with hu
  have hsθ : s / θ = 1 - u := by rw [hu]; ring
  have hu_eq : u = θ ^ 2 / 6 - e2 / θ := by
    rw [hu, he2]; field_simp; ring
  have hu_b : |u - θ ^ 2 / 6| ≤ θ ^ 4 / 100 := by
    rw [hu_eq, show θ ^ 2 / 6 - e2 / θ - θ ^ 2 / 6 = -(e2 / θ) by ring, abs_neg, abs_div,
      abs_of_pos h0, div_le_iff₀ h0]
    nlinarith [hsb]
  have hu_lo : 0 ≤ u := by
    rw [hu, sub_nonneg, div_le_one h0]; exact hs_le
  have hu_hi : u ≤ θ ^ 2 / 5 := by
    have := (abs_le.mp hu_b).2; nlinarith
  have hu1 : u ≤ 1 / 5 := by nlinarith
  have h1u : 0 < 1 - u := by linarith
  have hB : |Real.log (θ / s) - θ ^ 2 / 6| ≤ θ ^ 4 / 10 := by
    have hlog : Real.log (θ / s) = -Real.log (1 - u) := by
      rw [← hsθ, ← Real.log_inv, inv_div]
    have hl1 : Real.log (1 - u) ≤ -u := by
      have := Real.log_le_sub_one_of_pos h1u; linarith
    have hl2 : -(u / (1 - u)) ≤ Real.log (1 - u) := by
      have := Real.one_sub_inv_le_log_of_pos h1u
      have e : 1 - (1 - u)⁻¹ = -(u / (1 - u)) := by field_simp; ring
      linarith
    have hq : u / (1 - u) ≤ u + 5 / 4 * u ^ 2 := by
      rw [div_le_iff₀ h1u]; nlinarith
    have hu2 : u ^ 2 ≤ θ ^ 4 / 25 := by
      have : u ^ 2 ≤ (θ ^ 2 / 5) ^ 2 := pow_le_pow_left₀ hu_lo hu_hi 2
      linarith [show (θ ^ 2 / 5) ^ 2 = θ ^ 4 / 25 by ring]
    rw [hlog, abs_le]
    have := abs_le.mp hu_b
    constructor <;> linarith
  have := abs_le.mp hA
  have := abs_le.mp hB
  rw [abs_le]
  constructor <;> linarith

/-- The path `w = θ e^{iθ}/sin θ` of Binet's loop integral, in the logarithmic coordinate
`log w = log (θ / sin θ) + iθ`, for `0 < θ < π`. -/
def binetPathLog (θ : ℝ) : ℂ := (Real.log (θ / Real.sin θ) : ℂ) + θ * I

/-- The derivative of `binetPathLog`. -/
def binetPathLogDeriv (θ : ℝ) : ℂ := ((1 / θ - Real.cot θ : ℝ) : ℂ) + I

/-- The integrand `e^{c w} w^{b} d(log w)` along the path. -/
def binetPathTerm (b c θ : ℝ) : ℂ :=
  exp (c * exp (binetPathLog θ) + b * binetPathLog θ) * binetPathLogDeriv θ

/-- `θ/sin θ ≥ 1` for `0 < θ < π`. -/
theorem binetPath_one_le_div_sin {θ : ℝ} (hθ : θ ∈ Ioo 0 π) : 1 ≤ θ / Real.sin θ := by
  rw [le_div_iff₀ (Real.sin_pos_of_mem_Ioo hθ), one_mul]; exact Real.sin_le hθ.1.le

/-- On `(0, π)`, the path coordinate `log(θ/sin θ) + iθ` has derivative `1/θ - cot θ + i`. -/
theorem hasDerivAt_binetPathLog {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    HasDerivAt binetPathLog (binetPathLogDeriv θ) θ := by
  have hs := Real.sin_pos_of_mem_Ioo hθ
  have hr : 0 < θ / Real.sin θ := div_pos hθ.1 hs
  have hd : HasDerivAt (fun x => x / Real.sin x)
      ((1 * Real.sin θ - θ * Real.cos θ) / Real.sin θ ^ 2) θ :=
    (hasDerivAt_id' θ).div (Real.hasDerivAt_sin θ) hs.ne'
  have hl := (hd.log hr.ne').ofReal_comp
  have hI : HasDerivAt (fun x : ℝ => (x : ℂ) * I) (1 * I) θ :=
    (hasDerivAt_id θ).ofReal_comp.mul_const I
  have hθ0 : θ ≠ 0 := hθ.1.ne'
  refine (hl.add hI).congr_deriv ?_
  simp only [binetPathLogDeriv, one_mul]
  congr 2
  rw [Real.cot_eq_cos_div_sin]
  field_simp

/-- `exp(log(θ/sin θ) + iθ) = θ cot θ + iθ` on `(0, π)`. -/
theorem exp_binetPathLog {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    exp (binetPathLog θ) = ((θ * Real.cot θ : ℝ) : ℂ) + θ * I := by
  have hs := Real.sin_pos_of_mem_Ioo hθ
  have hr : 0 < θ / Real.sin θ := div_pos hθ.1 hs
  rw [binetPathLog, Complex.exp_add, ← ofReal_exp, Real.exp_log hr,
    Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cot_eq_cos_div_sin]
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im] <;>
    field_simp <;> ring

/-- Real part of the exponent along the path: `Re(c w + b log w) = c θ cot θ + b log(θ/sin θ)`. -/
theorem re_binetPath_exponent (b c : ℝ) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    ((c : ℂ) * exp (binetPathLog θ) + b * binetPathLog θ).re =
      c * (θ * Real.cot θ) + b * Real.log (θ / Real.sin θ) := by
  rw [exp_binetPathLog hθ, binetPathLog]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

/-- `y^N e^{-a y} ≤ N!/a^N`. -/
theorem binetPath_pow_mul_exp_le {a y : ℝ} (ha : 0 < a) (hy : 0 ≤ y) (N : ℕ) :
    y ^ N * Real.exp (-(a * y)) ≤ N.factorial / a ^ N := by
  have h := Real.pow_div_factorial_le_exp (a * y) (by positivity) N
  rw [div_le_iff₀ (by positivity)] at h
  rw [le_div_iff₀ (by positivity), Real.exp_neg]
  have he := Real.exp_pos (a * y)
  rw [mul_pow] at h
  calc y ^ N * (Real.exp (a * y))⁻¹ * a ^ N = (a ^ N * y ^ N) * (Real.exp (a * y))⁻¹ := by ring
    _ ≤ (Real.exp (a * y) * N.factorial) * (Real.exp (a * y))⁻¹ := by gcongr
    _ = N.factorial := by field_simp

/-- The core estimate: `exp(c θ cot θ + b log(θ/sin θ)) ≤ e^{2c₂} e^{-a y} (C y)^n`, where
`y = 1/(π-θ)`, `C = π²/2`, `a = c₁π/3` and `n = ⌈|b|⌉`. -/
theorem binetPath_exp_le {b c c₁ c₂ θ : ℝ} (hc₁ : 0 < c₁) (hc : c₁ ≤ c) (hc₂ : c ≤ c₂)
    (hθ : θ ∈ Ioo 0 π) :
    Real.exp (c * (θ * Real.cot θ) + b * Real.log (θ / Real.sin θ)) ≤
      Real.exp (2 * c₂) * Real.exp (-(c₁ * π / 3 * (π - θ)⁻¹)) *
        (π ^ 2 / 2 * (π - θ)⁻¹) ^ ⌈|b|⌉₊ := by
  have ht : 0 < π - θ := by linarith [hθ.2]
  have hr1 := binetPath_one_le_div_sin hθ
  have hrC : θ / Real.sin θ ≤ π ^ 2 / 2 * (π - θ)⁻¹ := by
    have := binetPath_div_sin_le hθ.1 hθ.2
    rwa [show π ^ 2 / (2 * (π - θ)) = π ^ 2 / 2 * (π - θ)⁻¹ by field_simp] at this
  have hg0 : 0 ≤ Real.log (θ / Real.sin θ) := Real.log_nonneg hr1
  have hp := binetPath_mul_cot_le hθ.1 hθ.2
  have h1 : c * (θ * Real.cot θ) ≤ 2 * c₂ + -(c₁ * π / 3 * (π - θ)⁻¹) := by
    have hy : 0 ≤ π / 3 / (π - θ) := by positivity
    have : c * (θ * Real.cot θ) ≤ c * (2 - π / 3 / (π - θ)) :=
      mul_le_mul_of_nonneg_left hp (by linarith)
    have e : c₁ * π / 3 * (π - θ)⁻¹ = c₁ * (π / 3 / (π - θ)) := by field_simp
    rw [e]
    nlinarith
  have h2 : b * Real.log (θ / Real.sin θ) ≤ ⌈|b|⌉₊ * Real.log (π ^ 2 / 2 * (π - θ)⁻¹) := by
    have hb : b ≤ ⌈|b|⌉₊ := (le_abs_self b).trans (Nat.le_ceil _)
    have hlog : Real.log (θ / Real.sin θ) ≤ Real.log (π ^ 2 / 2 * (π - θ)⁻¹) :=
      Real.log_le_log (by linarith) hrC
    calc b * Real.log (θ / Real.sin θ) ≤ ⌈|b|⌉₊ * Real.log (θ / Real.sin θ) :=
          mul_le_mul_of_nonneg_right hb hg0
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
  have hCpos : 0 < π ^ 2 / 2 * (π - θ)⁻¹ := by positivity
  calc Real.exp (c * (θ * Real.cot θ) + b * Real.log (θ / Real.sin θ))
      ≤ Real.exp ((2 * c₂ + -(c₁ * π / 3 * (π - θ)⁻¹)) +
          ⌈|b|⌉₊ * Real.log (π ^ 2 / 2 * (π - θ)⁻¹)) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by
      rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_log hCpos]

/-- `|1/θ - cot θ + i| ≤ 3 (π²/2)/(π - θ)` on `(0, π)`. -/
theorem norm_binetPathLogDeriv_le {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    ‖binetPathLogDeriv θ‖ ≤ 3 * (π ^ 2 / 2 * (π - θ)⁻¹) := by
  have hs := Real.sin_pos_of_mem_Ioo hθ
  have ht : 0 < π - θ := by linarith [hθ.2]
  have hθ0 : θ ≠ 0 := hθ.1.ne'
  have hq : 1 / θ - Real.cot θ = (Real.sin θ - θ * Real.cos θ) / (θ * Real.sin θ) := by
    rw [Real.cot_eq_cos_div_sin]; field_simp
  have hq0 : 0 ≤ 1 / θ - Real.cot θ := by
    rw [hq]; exact div_nonneg (binetPath_m_nonneg hθ.1.le hθ.2.le) (by positivity [hθ.1])
  have hrC : θ / Real.sin θ ≤ π ^ 2 / 2 * (π - θ)⁻¹ := by
    have := binetPath_div_sin_le hθ.1 hθ.2
    rwa [show π ^ 2 / (2 * (π - θ)) = π ^ 2 / 2 * (π - θ)⁻¹ by field_simp] at this
  have hX1 : 1 ≤ π ^ 2 / 2 * (π - θ)⁻¹ := (binetPath_one_le_div_sin hθ).trans hrC
  have hq1 : 1 / θ - Real.cot θ ≤ 2 * (π ^ 2 / 2 * (π - θ)⁻¹) := by
    rw [hq]
    have hm := binetPath_m_le hθ.1.le
    have h0 := hθ.1
    calc (Real.sin θ - θ * Real.cos θ) / (θ * Real.sin θ) ≤ θ ^ 3 / 3 / (θ * Real.sin θ) := by
          gcongr
      _ = θ / 3 * (θ / Real.sin θ) := by field_simp
      _ ≤ 2 * (θ / Real.sin θ) := by
          gcongr
          linarith [hθ.2, Real.pi_le_four]
      _ ≤ _ := by gcongr
  calc ‖binetPathLogDeriv θ‖ ≤ ‖(((1 / θ - Real.cot θ : ℝ)) : ℂ)‖ + ‖I‖ := norm_add_le _ _
    _ = (1 / θ - Real.cot θ) + 1 := by rw [norm_real, Real.norm_of_nonneg hq0, norm_I]
    _ ≤ _ := by linarith

/-- The uniform bound on the integrand. -/
def binetPathBound (b c₁ c₂ : ℝ) : ℝ :=
  3 * Real.exp (2 * c₂) * (π ^ 2 / 2) ^ (⌈|b|⌉₊ + 1) * (⌈|b|⌉₊ + 1).factorial /
    (c₁ * π / 3) ^ (⌈|b|⌉₊ + 1)

/-- Uniform bound for the path integrand `e^(cw) w^b d(log w)` over `c ∈ [c₁, c₂]`, `c₁ > 0`. -/
theorem norm_binetPathTerm_le {b c c₁ c₂ θ : ℝ} (hc₁ : 0 < c₁) (hc : c₁ ≤ c) (hc₂ : c ≤ c₂)
    (hθ : θ ∈ Ioo 0 π) : ‖binetPathTerm b c θ‖ ≤ binetPathBound b c₁ c₂ := by
  have ht : 0 < π - θ := by linarith [hθ.2]
  set y := (π - θ)⁻¹ with hy
  have hy0 : 0 ≤ y := by positivity
  set n := ⌈|b|⌉₊
  rw [binetPathTerm, norm_mul, Complex.norm_exp, re_binetPath_exponent b c hθ]
  have h1 := binetPath_exp_le (b := b) hc₁ hc hc₂ hθ
  have h2 := norm_binetPathLogDeriv_le hθ
  have ha : 0 < c₁ * π / 3 := by positivity
  have h3 := binetPath_pow_mul_exp_le ha hy0 (n + 1)
  calc Real.exp (c * (θ * Real.cot θ) + b * Real.log (θ / Real.sin θ)) *
        ‖binetPathLogDeriv θ‖
      ≤ (Real.exp (2 * c₂) * Real.exp (-(c₁ * π / 3 * y)) * (π ^ 2 / 2 * y) ^ n) *
          (3 * (π ^ 2 / 2 * y)) := by gcongr
    _ = 3 * Real.exp (2 * c₂) * (π ^ 2 / 2) ^ (n + 1) *
          (y ^ (n + 1) * Real.exp (-(c₁ * π / 3 * y))) := by ring
    _ ≤ 3 * Real.exp (2 * c₂) * (π ^ 2 / 2) ^ (n + 1) *
          ((n + 1).factorial / (c₁ * π / 3) ^ (n + 1)) := by gcongr
    _ = binetPathBound b c₁ c₂ := by rw [binetPathBound]; ring

/-- The path coordinate `log(θ/sin θ) + iθ` is continuous on `(0, π)`. -/
theorem continuousOn_binetPathLog : ContinuousOn binetPathLog (Ioo 0 π) :=
  fun _ hθ => (hasDerivAt_binetPathLog hθ).continuousAt.continuousWithinAt

/-- Its derivative `1/θ - cot θ + i` is continuous on `(0, π)`. -/
theorem continuousOn_binetPathLogDeriv : ContinuousOn binetPathLogDeriv (Ioo 0 π) := by
  intro θ hθ
  have hs := Real.sin_pos_of_mem_Ioo hθ
  have h : ContinuousAt (fun x : ℝ => 1 / x - Real.cos x / Real.sin x) θ :=
    (continuousAt_const.div continuousAt_id hθ.1.ne').sub
      (Real.continuous_cos.continuousAt.div Real.continuous_sin.continuousAt hs.ne')
  have h' : ContinuousAt (fun x : ℝ => 1 / x - Real.cot x) θ := by
    simpa only [Real.cot_eq_cos_div_sin] using h
  exact ((continuous_ofReal.continuousAt.comp h').add continuousAt_const).continuousWithinAt

/-- The path integrand is continuous on `(0, π)`. -/
theorem continuousOn_binetPathTerm (b c : ℝ) : ContinuousOn (binetPathTerm b c) (Ioo 0 π) := by
  have hl := continuousOn_binetPathLog
  exact (((continuousOn_const.mul hl.cexp).add (continuousOn_const.mul hl)).cexp).mul
    continuousOn_binetPathLogDeriv

/-- For `c > 0` the path integrand is integrable on `(0, π)`. -/
theorem integrableOn_binetPathTerm (b : ℝ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (binetPathTerm b c) (Ioo 0 π) :=
  Integrable.of_bound ((continuousOn_binetPathTerm b c).aestronglyMeasurable measurableSet_Ioo)
    (binetPathBound b c c) ((ae_restrict_mem measurableSet_Ioo).mono fun _ hθ =>
      norm_binetPathTerm_le hc le_rfl le_rfl hθ)

/-- The antiderivative `e^{c w} w^{b}` along the path. -/
def binetPathF (b c θ : ℝ) : ℂ := exp (c * exp (binetPathLog θ) + b * binetPathLog θ)

/-- The path integrand with `b + 1` is `F(b, c) · w · d(log w)/dθ`, where `F = e^(cw) w^b`. -/
theorem binetPathTerm_add_one (b c θ : ℝ) :
    binetPathTerm (b + 1) c θ = binetPathF b c θ * exp (binetPathLog θ) * binetPathLogDeriv θ := by
  rw [binetPathTerm, binetPathF, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- `dF/dθ = c · term(b + 1) + b · term(b)` along the path, for `F = e^(cw) w^b`. -/
theorem hasDerivAt_binetPathF (b c : ℝ) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    HasDerivAt (binetPathF b c) (c * binetPathTerm (b + 1) c θ + b * binetPathTerm b c θ) θ := by
  have hl := hasDerivAt_binetPathLog hθ
  have h := (((hl.cexp).const_mul (c : ℂ)).add (hl.const_mul (b : ℂ))).cexp
  refine h.congr_deriv ?_
  rw [binetPathTerm_add_one, binetPathTerm, binetPathF]
  simp only [Pi.add_apply]
  ring

/-- The path coordinate tends to `0` as `θ → 0⁺`. -/
theorem tendsto_binetPathLog_zero : Tendsto binetPathLog (𝓝[>] 0) (𝓝 0) := by
  have hs : Tendsto Real.sinc (𝓝[>] 0) (𝓝 1) := by
    have := Real.continuous_sinc.tendsto 0
    rw [Real.sinc_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have hinv : Tendsto (fun θ => (Real.sinc θ)⁻¹) (𝓝[>] 0) (𝓝 1) := by
    simpa using hs.inv₀ one_ne_zero
  have hlog : Tendsto (fun θ => Real.log ((Real.sinc θ)⁻¹)) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuousAt_log one_ne_zero).tendsto.comp hinv
    rwa [Real.log_one] at this
  have heq : (fun θ => Real.log ((Real.sinc θ)⁻¹)) =ᶠ[𝓝[>] 0]
      fun θ => Real.log (θ / Real.sin θ) := by
    filter_upwards [self_mem_nhdsWithin] with θ (hθ : 0 < θ)
    rw [Real.sinc_of_ne_zero hθ.ne', inv_div]
  have h1 := (continuous_ofReal.tendsto 0).comp (hlog.congr' heq)
  have h2 : Tendsto (fun θ : ℝ => (θ : ℂ) * I) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds
      ((by fun_prop : Continuous fun θ : ℝ => (θ : ℂ) * I).tendsto' 0 0 (by simp))
  have h3 := h1.add h2
  simp only [ofReal_zero, add_zero, Function.comp_def] at h3
  exact h3

/-- `F(b, c) → e^c` as `θ → 0⁺`. -/
theorem tendsto_binetPathF_zero (b c : ℝ) :
    Tendsto (binetPathF b c) (𝓝[>] 0) (𝓝 (exp c)) := by
  have hG : Continuous fun z : ℂ => exp (c * exp z + b * z) := by fun_prop
  have := (hG.tendsto 0).comp tendsto_binetPathLog_zero
  simp only [Function.comp_def, Complex.exp_zero, mul_one, mul_zero, add_zero] at this
  exact this

/-- `F(b, c) → 0` as `θ → π⁻`, for `c > 0`. -/
theorem tendsto_binetPathF_pi (b : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (binetPathF b c) (𝓝[<] π) (𝓝 0) := by
  set n := ⌈|b|⌉₊
  have ha : 0 < c * π / 3 := by positivity
  set K := Real.exp (2 * c) * (π ^ 2 / 2) ^ n * ((n + 1).factorial / (c * π / 3) ^ (n + 1))
  refine squeeze_zero_norm' (a := fun θ => K * (π - θ)) ?_ ?_
  · filter_upwards [Ioo_mem_nhdsLT Real.pi_pos] with θ hθ
    have ht : 0 < π - θ := by linarith [hθ.2]
    set y := (π - θ)⁻¹ with hy
    have hy0 : 0 < y := by positivity
    rw [binetPathF, Complex.norm_exp, re_binetPath_exponent b c hθ]
    have h1 := binetPath_exp_le (b := b) hc le_rfl le_rfl hθ
    have h3 := binetPath_pow_mul_exp_le ha hy0.le (n + 1)
    have hyt : π - θ = y⁻¹ := by rw [hy, inv_inv]
    calc Real.exp (c * (θ * Real.cot θ) + b * Real.log (θ / Real.sin θ))
        ≤ Real.exp (2 * c) * Real.exp (-(c * π / 3 * y)) * (π ^ 2 / 2 * y) ^ n := h1
      _ = Real.exp (2 * c) * (π ^ 2 / 2) ^ n *
            (y ^ (n + 1) * Real.exp (-(c * π / 3 * y))) * y⁻¹ := by
          field_simp
          ring
      _ ≤ Real.exp (2 * c) * (π ^ 2 / 2) ^ n *
            ((n + 1).factorial / (c * π / 3) ^ (n + 1)) * y⁻¹ := by gcongr
      _ = K * (π - θ) := by rw [hyt]
  · have : Tendsto (fun θ => K * (π - θ)) (𝓝 π) (𝓝 (K * (π - π))) :=
      (continuous_const.mul (continuous_const.sub continuous_id)).tendsto π
    rw [sub_self, mul_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this

/-- The integral of the path integrand. -/
def binetPathInt (b c : ℝ) : ℂ := ∫ θ in Ioo 0 π, binetPathTerm b c θ

/-- Integration by parts along the path. -/
theorem binetPathInt_rec (b : ℝ) {c : ℝ} (hc : 0 < c) :
    c * binetPathInt (b + 1) c + b * binetPathInt b c = -exp c := by
  have hint : IntervalIntegrable
      (fun θ => (c : ℂ) * binetPathTerm (b + 1) c θ + b * binetPathTerm b c θ) volume 0 π := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le Real.pi_pos.le]
    exact ((integrableOn_binetPathTerm (b + 1) hc).const_mul _).add
      ((integrableOn_binetPathTerm b hc).const_mul _)
  have h := integral_eq_sub_of_hasDerivAt_of_tendsto Real.pi_pos
    (fun θ hθ => hasDerivAt_binetPathF b c hθ) hint (tendsto_binetPathF_zero b c)
    (tendsto_binetPathF_pi b hc)
  rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo,
    integral_add ((integrableOn_binetPathTerm (b + 1) hc).const_mul _)
      ((integrableOn_binetPathTerm b hc).const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, zero_sub] at h
  exact h

/-- The derivative in `c` of the path integrand with exponent `b` is the integrand with exponent `b
+ 1`. -/
theorem hasDerivAt_binetPathTerm_param (b c θ : ℝ) :
    HasDerivAt (fun c : ℝ => binetPathTerm b c θ) (binetPathTerm (b + 1) c θ) c := by
  have h1 : HasDerivAt (fun c : ℝ => (c : ℂ) * exp (binetPathLog θ) + b * binetPathLog θ)
      (exp (binetPathLog θ)) c := by
    simpa using ((hasDerivAt_id c).ofReal_comp.mul_const (exp (binetPathLog θ))).add_const
      ((b : ℂ) * binetPathLog θ)
  have h := h1.cexp.mul_const (binetPathLogDeriv θ)
  refine h.congr_deriv ?_
  rw [binetPathTerm_add_one, binetPathF]

/-- Differentiation in the scale `c`. -/
theorem hasDerivAt_binetPathInt (b : ℝ) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    HasDerivAt (binetPathInt b) (binetPathInt (b + 1) c₀) c₀ := by
  have hs : Ioo (c₀ / 2) (2 * c₀) ∈ 𝓝 c₀ := Ioo_mem_nhds (by linarith) (by linarith)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioo 0 π))
    (F := fun c θ => binetPathTerm b c θ) (F' := fun c θ => binetPathTerm (b + 1) c θ)
    (bound := fun _ => binetPathBound (b + 1) (c₀ / 2) (2 * c₀)) hs
    (Eventually.of_forall fun c =>
      (continuousOn_binetPathTerm b c).aestronglyMeasurable measurableSet_Ioo)
    (integrableOn_binetPathTerm b hc₀)
    ((continuousOn_binetPathTerm (b + 1) c₀).aestronglyMeasurable measurableSet_Ioo)
    ((ae_restrict_mem measurableSet_Ioo).mono fun θ hθ c hc =>
      norm_binetPathTerm_le (by linarith) hc.1.le hc.2.le hθ)
    (integrable_const _)
    (Eventually.of_forall fun θ c _ => hasDerivAt_binetPathTerm_param b c θ)
  exact h.2

/-- The imaginary part of the path integral. -/
def binetPathIm (b c : ℝ) : ℝ := (binetPathInt b c).im

/-- Recurrence for the imaginary parts of the path integrals: `c P(b + 1, c) + b P(b, c) = 0`. -/
theorem binetPathIm_rec (b : ℝ) {c : ℝ} (hc : 0 < c) :
    c * binetPathIm (b + 1) c + b * binetPathIm b c = 0 := by
  have h := congrArg Complex.im (binetPathInt_rec b hc)
  rw [Complex.add_im, im_ofReal_mul, im_ofReal_mul, Complex.neg_im, ← ofReal_exp,
    ofReal_im, neg_zero] at h
  exact h

/-- Independence of the scale: `c^b Im P(b, c)` does not depend on `c > 0`. -/
theorem binetPathIm_scale (b : ℝ) {c : ℝ} (hc : 0 < c) :
    c ^ b * binetPathIm b c = binetPathIm b 1 := by
  have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun c : ℝ => c ^ b * binetPathIm b c) 0 x := by
    intro x (hx : 0 < x)
    have h1 := Real.hasDerivAt_rpow_const (p := b) (Or.inl hx.ne')
    have h2 : HasDerivAt (fun c => binetPathIm b c) (binetPathIm (b + 1) x) x :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_binetPathInt b hx)
    refine (h1.mul h2).congr_deriv ?_
    have hr := binetPathIm_rec b hx
    rw [Real.rpow_sub_one hx.ne']
    field_simp
    linear_combination x ^ b * hr
  have := IsOpen.is_const_of_deriv_eq_zero isOpen_Ioi isPreconnected_Ioi
    (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hd x hx).deriv) hc (show (1 : ℝ) ∈ Ioi 0 from mem_Ioi.mpr one_pos)
  simpa using this

/-- `Im term(1 - a, a, θ) = e^a e^(-a φ(θ))` on `(0, π)`. -/
theorem im_binetPathTerm {a θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    (binetPathTerm (1 - a) a θ).im = Real.exp a * Real.exp (-a * binetPhi θ) := by
  have he := exp_binetPathLog hθ
  have hθ0 : θ ≠ 0 := hθ.1.ne'
  have hsplit : (a : ℂ) * exp (binetPathLog θ) + ((1 - a : ℝ) : ℂ) * binetPathLog θ =
      ((a * (θ * Real.cot θ - Real.log (θ / Real.sin θ)) : ℝ) : ℂ) + binetPathLog θ := by
    rw [he, binetPathLog]
    push_cast
    ring
  rw [binetPathTerm, hsplit, Complex.exp_add, ← ofReal_exp, he, mul_assoc, im_ofReal_mul,
    binetPathLogDeriv]
  have him : ((((θ * Real.cot θ : ℝ)) : ℂ) + θ * I) * ((((1 / θ - Real.cot θ : ℝ)) : ℂ) + I)
      = ((θ * Real.cot θ * (1 / θ - Real.cot θ) - θ : ℝ) : ℂ) + (1 : ℝ) * I := by
    apply Complex.ext <;>
      simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;>
      field_simp <;> ring
  rw [him]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  rw [← Real.exp_add, binetPhi]
  congr 1
  ring

/-- `Im P(1 - a, a) = e^a ∫₀^π e^(-a φ(θ)) dθ`. -/
theorem binetPathIm_eq (a : ℝ) {c : ℝ} (hc : 0 < c) (hca : c = a) :
    binetPathIm (1 - a) c = Real.exp a * ∫ θ in Ioo 0 π, Real.exp (-a * binetPhi θ) := by
  subst hca
  rw [binetPathIm, binetPathInt, ← RCLike.im_to_complex,
    ← integral_im (integrableOn_binetPathTerm (1 - c) hc), ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  simp only [RCLike.im_to_complex]
  exact im_binetPathTerm hθ

/-- The Binet phase `φ` is measurable. -/
theorem measurable_binetPhi : Measurable binetPhi := by
  have : binetPhi = fun t => 1 - t * (Real.cos t / Real.sin t) + Real.log (t / Real.sin t) := by
    funext t; rw [binetPhi, Real.cot_eq_cos_div_sin]
  rw [this]
  fun_prop

/-- The Binet phase `φ` is even. -/
theorem binetPhi_neg (θ : ℝ) : binetPhi (-θ) = binetPhi θ := by
  rw [binetPhi, binetPhi, Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.cos_neg,
    Real.sin_neg, neg_div_neg_eq]
  congr 2
  rw [div_neg]; ring

/-- The Laplace integral of `binetPhi` over `(0, π)`. -/
def binetLaplace (x : ℝ) : ℝ := ∫ θ in Ioo 0 π, Real.exp (-x * binetPhi θ)

/-- `x φ(s/√x) → s²/2` as `x → ∞`, for `s > 0`. -/
theorem tendsto_binetPhi_scaled {s : ℝ} (hs : 0 < s) :
    Tendsto (fun x : ℝ => x * binetPhi (s / √x)) atTop (𝓝 (s ^ 2 / 2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun x : ℝ => s ^ 4 / 2 / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_gt_atTop (s ^ 2)] with x hx
  have hx0 : 0 < x := lt_of_le_of_lt (by positivity) hx
  have hsx : 0 < √x := Real.sqrt_pos.mpr hx0
  set θ := s / √x with hθ
  have hθ0 : 0 < θ := div_pos hs hsx
  have hθ1 : θ ≤ 1 := by
    rw [hθ, div_le_one hsx]
    rw [show s = √(s ^ 2) by rw [Real.sqrt_sq hs.le]]
    exact Real.sqrt_le_sqrt hx.le
  have hb := abs_binetPhi_sub_le hθ0 hθ1
  have hsq : √x ^ 2 = x := Real.sq_sqrt hx0.le
  have h2 : x * θ ^ 2 = s ^ 2 := by rw [hθ, div_pow, hsq]; field_simp
  have h4 : x * θ ^ 4 = s ^ 4 / x := by
    rw [hθ, div_pow, show √x ^ 4 = (√x ^ 2) ^ 2 by ring, hsq]; field_simp
  rw [Real.norm_eq_abs]
  calc |x * binetPhi θ - s ^ 2 / 2| = x * |binetPhi θ - θ ^ 2 / 2| := by
        rw [← abs_of_pos hx0, ← abs_mul, abs_of_pos hx0]; congr 1; rw [← h2]; ring
    _ ≤ x * (θ ^ 4 / 2) := by gcongr
    _ = s ^ 4 / 2 / x := by rw [show x * (θ ^ 4 / 2) = x * θ ^ 4 / 2 by ring, h4]; ring

/-- `√x ∫₀^π e^(-x φ(θ)) dθ` as an integral over `(0, π√x)` after the substitution `θ = s/√x`. -/
theorem sqrt_mul_binetLaplace {x : ℝ} (hx : 0 < x) :
    √x * binetLaplace x = ∫ s in Ioi 0,
      (Ioo 0 (π * √x)).indicator (fun s => Real.exp (-x * binetPhi (s / √x))) s := by
  have hsx : 0 < √x := Real.sqrt_pos.mpr hx
  rw [setIntegral_indicator measurableSet_Ioo, inter_eq_right.mpr Ioo_subset_Ioi_self,
    binetLaplace, ← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le Real.pi_pos.le,
    ← intervalIntegral.integral_of_le (by positivity),
    intervalIntegral.integral_comp_div (fun θ => Real.exp (-x * binetPhi θ)) hsx.ne',
    zero_div, mul_div_assoc, div_self hsx.ne', mul_one, smul_eq_mul]

/-- `√x ∫₀^π e^(-x φ(θ)) dθ → √(2π)/2` as `x → ∞` (Laplace's method). -/
theorem tendsto_sqrt_mul_binetLaplace :
    Tendsto (fun x => √x * binetLaplace x) atTop (𝓝 (√(π / (1 / 2)) / 2)) := by
  rw [← integral_gaussian_Ioi]
  have hcongr : (fun x => ∫ s in Ioi 0,
      (Ioo 0 (π * √x)).indicator (fun s => Real.exp (-x * binetPhi (s / √x))) s) =ᶠ[atTop]
      fun x => √x * binetLaplace x := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [sqrt_mul_binetLaplace hx]
  refine Tendsto.congr' hcongr ?_
  refine tendsto_integral_filter_of_dominated_convergence (fun s => Real.exp (-(1 / 3) * s ^ 2))
    ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun x => ?_
    refine (Measurable.indicator ?_ measurableSet_Ioo).aestronglyMeasurable
    exact Real.measurable_exp.comp
      (measurable_const.mul (measurable_binetPhi.comp (measurable_id.div_const _)))
  · filter_upwards [eventually_gt_atTop 0] with x hx
    refine (ae_restrict_mem measurableSet_Ioi).mono fun s _ => ?_
    by_cases hmem : s ∈ Ioo 0 (π * √x)
    · rw [indicator_of_mem hmem, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have hsx : 0 < √x := Real.sqrt_pos.mpr hx
      have hθ0 : 0 < s / √x := div_pos hmem.1 hsx
      have hθπ : s / √x < π := by rw [div_lt_iff₀ hsx]; exact hmem.2
      have hge := binetPhi_ge hθ0 hθπ
      have hsq : x * (s / √x) ^ 2 = s ^ 2 := by
        rw [div_pow, Real.sq_sqrt hx.le]; field_simp
      apply Real.exp_le_exp.mpr
      nlinarith
    · rw [indicator_of_notMem hmem, norm_zero]; positivity
  · exact (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 3)).integrableOn
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun s (hs : 0 < s) => ?_
    have hev : ∀ᶠ x in atTop, (Ioo 0 (π * √x)).indicator
        (fun s => Real.exp (-x * binetPhi (s / √x))) s = Real.exp (-(x * binetPhi (s / √x))) := by
      filter_upwards [eventually_gt_atTop ((s / π) ^ 2)] with x hx
      have hx0 : 0 < x := lt_of_le_of_lt (by positivity) hx
      have hmem : s ∈ Ioo 0 (π * √x) := by
        refine ⟨hs, ?_⟩
        have h1 : s / π < √x := by
          rw [show s / π = √((s / π) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
          exact Real.sqrt_lt_sqrt (by positivity) hx
        rw [div_lt_iff₀ Real.pi_pos] at h1
        linarith
      rw [indicator_of_mem hmem, neg_mul]
    refine Tendsto.congr' (EventuallyEq.symm hev) ?_
    have := (Real.continuous_exp.tendsto _).comp (tendsto_binetPhi_scaled hs).neg
    rw [show -(1 / 2) * s ^ 2 = -(s ^ 2 / 2) by ring]
    exact this

/-- `∫_{-π}^{π} e^(-x φ(t)) dt = 2 ∫₀^π e^(-x φ(t)) dt` for `x ≥ 0`. -/
theorem integral_binetPhi_symm {x : ℝ} (hx : 0 ≤ x) :
    ∫ t in (-π)..π, Real.exp (-x * binetPhi t) = 2 * binetLaplace x := by
  have hmeas : Measurable fun t => Real.exp (-x * binetPhi t) :=
    Real.measurable_exp.comp (measurable_const.mul measurable_binetPhi)
  have hle : ∀ t, 0 ≤ binetPhi t → ‖Real.exp (-x * binetPhi t)‖ ≤ 1 := fun t ht => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    nlinarith
  have hpos : ∀ t ∈ Ioo 0 π, 0 ≤ binetPhi t := fun t ht =>
    le_trans (by positivity) (binetPhi_ge ht.1 ht.2)
  have h2 : IntervalIntegrable (fun t => Real.exp (-x * binetPhi t)) volume 0 π := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le Real.pi_pos.le]
    exact Integrable.of_bound hmeas.aestronglyMeasurable 1
      ((ae_restrict_mem measurableSet_Ioo).mono fun t ht => hle t (hpos t ht))
  have h1 : IntervalIntegrable (fun t => Real.exp (-x * binetPhi t)) volume (-π) 0 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [Real.pi_pos])]
    refine Integrable.of_bound hmeas.aestronglyMeasurable 1
      ((ae_restrict_mem measurableSet_Ioo).mono fun t ht => hle t ?_)
    rw [← binetPhi_neg]
    exact hpos (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hneg : ∫ t in (-π)..0, Real.exp (-x * binetPhi t) =
      ∫ t in (0 : ℝ)..π, Real.exp (-x * binetPhi t) := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := π)
      (fun t => Real.exp (-x * binetPhi t))
    simp only [binetPhi_neg, neg_zero] at this
    exact this.symm
  rw [← integral_add_adjacent_intervals h1 h2, hneg, two_mul, binetLaplace,
    intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo]

/-- The normalized path integral `W(a) = Im ∫ e^{w} w^{-a} dw`, which equals `π/Γ(a)`. -/
def binetW (a : ℝ) : ℝ := binetPathIm (1 - a) 1

/-- `W(a) = a^(1-a) e^a ∫₀^π e^(-a φ)` for `a > 0`. -/
theorem binetW_eq {a : ℝ} (ha : 0 < a) :
    binetW a = a ^ (1 - a) * (Real.exp a * binetLaplace a) := by
  rw [binetW, ← binetPathIm_scale (1 - a) ha, binetPathIm_eq a ha rfl, binetLaplace]

/-- `W(a) = a W(a + 1)`. -/
theorem binetW_rec (a : ℝ) : binetW a = a * binetW (a + 1) := by
  have h := binetPathIm_rec (-a) one_pos
  rw [binetW, binetW, show 1 - (a + 1) = -a by ring, show 1 - a = -a + 1 by ring]
  linarith

/-- `W(a + 1) Γ(a + 1) = W(a) Γ(a)` for `a > 0`. -/
theorem binetW_mul_Gamma_add_one {a : ℝ} (ha : 0 < a) :
    binetW (a + 1) * Real.Gamma (a + 1) = binetW a * Real.Gamma a := by
  rw [Real.Gamma_add_one ha.ne', binetW_rec a]
  ring

/-- `W(n + t) Γ(n + t) = W(t) Γ(t)` for `t > 0`. -/
theorem binetW_mul_Gamma_nat_add {t : ℝ} (ht : 0 < t) (n : ℕ) :
    binetW (n + t) * Real.Gamma (n + t) = binetW t * Real.Gamma t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, show (n : ℝ) + 1 + t = n + t + 1 by ring,
      binetW_mul_Gamma_add_one (by positivity), ih]

/-- `W(x) Γ(x) = (Γ(x)/stirlingGamma(x)) √(2π) (√x ∫₀^π e^(-x φ))` for `x > 0`. -/
theorem binetW_mul_Gamma_eq_stirling {x : ℝ} (hx : 0 < x) :
    binetW x * Real.Gamma x =
      Real.Gamma x / Real.stirlingGamma x * √(2 * π) * (√x * binetLaplace x) := by
  have hS : Real.stirlingGamma x = √(2 * π) / √x * (x ^ x / Real.exp x) := by
    rw [Real.stirlingGamma, Real.sqrt_div' _ hx.le, Real.div_rpow hx.le (Real.exp_pos 1).le,
      Real.exp_one_rpow]
  have hsx : 0 < √x := Real.sqrt_pos.mpr hx
  have hxx : 0 < x ^ x := Real.rpow_pos_of_pos hx x
  have h2π : 0 < √(2 * π) := Real.sqrt_pos.mpr (by positivity)
  rw [binetW_eq hx, hS, Real.rpow_sub hx, Real.rpow_one]
  field_simp
  rw [Real.sq_sqrt hx.le]
  ring

/-- `W(t) Γ(t) = π` for `0 < t ≤ 1`. -/
theorem binetW_mul_Gamma_of_le_one {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    binetW t * Real.Gamma t = π := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + t) atTop atTop :=
    tendsto_atTop_add_const_right _ t tendsto_natCast_atTop_atTop
  have hlim := ((Real.tendsto_Gamma_add_nat_div_stirlingGamma ht ht1).mul_const √(2 * π)).mul
    (tendsto_sqrt_mul_binetLaplace.comp hnat)
  have hval : 1 * √(2 * π) * (√(π / (1 / 2)) / 2) = π := by
    rw [show π / (1 / 2) = 2 * π by ring, one_mul, mul_div_assoc', Real.mul_self_sqrt
      (by positivity)]
    ring
  rw [hval] at hlim
  have hconst : (fun n : ℕ => binetW (n + t) * Real.Gamma (n + t)) =
      fun n : ℕ => Real.Gamma (n + t) / Real.stirlingGamma (n + t) * √(2 * π) *
        (√(n + t) * binetLaplace (n + t)) := by
    funext n
    exact binetW_mul_Gamma_eq_stirling (by positivity)
  have h := hlim
  rw [show (fun n : ℕ => Real.Gamma (n + t) / Real.stirlingGamma (n + t) * √(2 * π) *
      ((fun x => √x * binetLaplace x) ∘ fun n : ℕ => (n : ℝ) + t) n) =
      fun n : ℕ => binetW (n + t) * Real.Gamma (n + t) from by rw [hconst]; rfl] at h
  simp only [binetW_mul_Gamma_nat_add ht] at h
  exact tendsto_nhds_unique tendsto_const_nhds h

/-- `W(a) Γ(a) = π` for every `a > 0`. -/
theorem binetW_mul_Gamma {a : ℝ} (ha : 0 < a) : binetW a * Real.Gamma a = π := by
  have hc : 1 ≤ ⌈a⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr ha).ne'
  set m := ⌈a⌉₊ - 1
  have hm : (m : ℝ) = ⌈a⌉₊ - 1 := by rw [Nat.cast_sub hc, Nat.cast_one]
  have ht : 0 < a - m := by rw [hm]; linarith [Nat.ceil_lt_add_one ha.le]
  have ht1 : a - m ≤ 1 := by rw [hm]; linarith [Nat.le_ceil a]
  have := binetW_mul_Gamma_nat_add ht m
  rw [show (m : ℝ) + (a - m) = a by ring] at this
  rw [this, binetW_mul_Gamma_of_le_one ht ht1]

end BinetLoop

/-- DLMF 5.9.2 (second form): `1/Γ(x) = e^x x^(1-x)/(2π) ∫_{-π}^{π} e^(-x φ(t)) dt`, `φ(t) = 1 - t
cot t + ln(t/sin t)`, for `x > 0`. -/
@[dlmf 5.9.E2_5]
theorem recip_Gamma_binet {x : ℝ} (hx : 0 < x) :
    (Real.Gamma x)⁻¹ =
      Real.exp x * x ^ (1 - x) / (2 * π) *
        ∫ t : ℝ in (-π)..π, Real.exp (-x * binetPhi t) := by
  have hG : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have h := binetW_mul_Gamma hx
  rw [binetW_eq hx] at h
  rw [integral_binetPhi_symm hx.le]
  field_simp
  linarith

/-- Helper lemma for `Gamma_gaussian`: the complex-valued form of Mathlib's
`integral_comp_abs`. -/
theorem integral_comp_abs_complex {f : ℝ → ℂ} :
    ∫ x, f |x| = 2 * ∫ x in Set.Ioi (0 : ℝ), f x := by
  have eq : ∫ (x : ℝ) in Set.Ioi 0, f |x| = ∫ (x : ℝ) in Set.Ioi 0, f x := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun _ hx => ?_)
    rw [abs_eq_self.mpr (le_of_lt (by exact hx))]
  by_cases hf : IntegrableOn (fun x => f |x|) (Set.Ioi 0)
  · have int_Iic : IntegrableOn (fun x ↦ f |x|) (Set.Iic 0) := by
      rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
      let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
      rw [m.integrableOn_map_iff]
      simp_rw [Function.comp_def, abs_neg, Set.neg_preimage, Set.neg_Iic, neg_zero]
      exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf
    calc
      _ = (∫ x in Set.Iic 0, f |x|) + ∫ x in Set.Ioi 0, f |x| := by
        rw [← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi int_Iic hf,
          Set.Iic_union_Ioi, Measure.restrict_univ]
      _ = 2 * ∫ x in Set.Ioi 0, f x := by
        rw [two_mul, eq]
        congr! 1
        rw [← neg_zero, ← integral_comp_neg_Iic, neg_zero]
        refine setIntegral_congr_fun measurableSet_Iic (fun _ hx => ?_)
        rw [abs_eq_neg_self.mpr (by exact hx)]
  · have : ¬ Integrable (fun x => f |x|) := by
      contrapose hf
      exact hf.integrableOn
    rw [← eq, integral_undef hf, integral_undef this, mul_zero]

/-- DLMF 5.9.3: `c^(-z) Γ(z) = ∫_{-∞}^{∞} |t|^(2z-1) e^(-c t²) dt` for `Re c, Re z > 0`. -/
@[dlmf 5.9.E3]
theorem Gamma_gaussian {c z : ℂ} (hc : 0 < c.re) (hz : 0 < z.re) :
    c ^ (-z) * Complex.Gamma z =
      ∫ t : ℝ, ((|t| : ℝ) : ℂ) ^ (2 * z - 1) * Complex.exp (-c * (t : ℂ) ^ 2) := by
  have hsq (t : ℝ) : (t : ℂ) ^ 2 = ((|t| : ℝ) : ℂ) ^ 2 := by
    rw [← ofReal_pow, ← ofReal_pow, sq_abs]
  have hfun : (fun t : ℝ => ((|t| : ℝ) : ℂ) ^ (2 * z - 1) * Complex.exp (-c * (t : ℂ) ^ 2)) =
      fun t : ℝ => (fun y : ℝ => (y : ℂ) ^ (2 * z - 1) * Complex.exp (-c * (y : ℂ) ^ 2)) |t| := by
    funext t
    rw [hsq t]
  rw [hfun, integral_comp_abs_complex (f := fun y : ℝ =>
    (y : ℂ) ^ (2 * z - 1) * Complex.exp (-c * (y : ℂ) ^ 2))]
  have hl := Gamma_laplace_power (μ := 2) (ν := 2 * z) (z := c) (by norm_num) (by simp)
    (by simp; linarith) hc
  have h2z : 2 * z / 2 = z := by ring
  rw [h2z] at hl
  have hint : ∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (2 * z - 1) * Complex.exp (-c * (t : ℂ) ^ 2) =
      ∫ t : ℝ in Set.Ioi 0, Complex.exp (-c * (t : ℂ) ^ (2 : ℂ)) * (t : ℂ) ^ (2 * z - 1) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [cpow_ofNat, mul_comm]
  rw [hint, ← hl]
  ring

end DLMF.Gamma
end
end
