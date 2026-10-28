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
# Integral representations (DLMF §5.9)

Euler's integral 5.2.1 is Mathlib `Gamma_eq_integral`. Real-line Laplace,
Fourier, and Binet-type integrals are acquired below. The Hankel loop 5.9.2
and the Mellin–Barnes formulae 5.9.11, 5.9.17 are deferred; the Hankel loop on its
steepest-descent path, `recip_Gamma_binet`, is proved without contour deformation
(section `BinetLoop`).

The digamma integrals 5.9.12, 5.9.13 and 5.9.16 are proved from the digamma series by
termwise integration (`integral_tsum_of_summable_integral_norm`; the terms do not change
sign). Mathlib's Frullani integral gives `log x`. The constant in Binet's formula is
fixed by letting `x → ∞`, using `log x - 1/x ≤ ψ(x) ≤ log x`.
-/

@[expose] public section

open Complex Filter MeasureTheory intervalIntegral
open scoped Real Topology

noncomputable section

namespace DLMF.Gamma

/-- Closes an equation between two derivative expressions, as produced by the `HasDerivAt`
combinators (pointwise operations, `id`), by clearing denominators. -/
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

section Prym

/-! ### Prym's decomposition (Temme §3.2.1)

`Γ(z) = ∫₁^∞ t^{z-1} e^{-t} dt + ∑ₖ (-1)ᵏ/((z+k) k!)`. For `Re z > 0` this is Euler's integral
split at `t = 1`, with the exponential series integrated termwise on `(0, 1]`. Both terms
satisfy `F(z+1) = z F(z)` up to the same constant `e⁻¹` with opposite signs, so the sum obeys
the recursion of `Γ`, which carries the formula to all `z ∉ -ℕ`. -/

open Set

/-- Prym's series `∑ₖ (-1)ᵏ/((z+k) k!)`. -/
def prymSeries (z : ℂ) : ℂ := ∑' k : ℕ, (-1 : ℂ) ^ k / ((z + k) * k.factorial)

/-- The upper incomplete Euler integral `∫₁^∞ t^{z-1} e^{-t} dt`. -/
def prymIntegral (z : ℂ) : ℂ := ∫ t : ℝ in Ioi 1, (t : ℂ) ^ (z - 1) * Complex.exp (-(t : ℂ))

/-- Prym's series `∑ₖ (-1)^k/((z + k) k!)` converges. -/
theorem summable_prym (z : ℂ) :
    Summable fun k : ℕ => (-1 : ℂ) ^ k / ((z + k) * k.factorial) := by
  refine Summable.of_norm_bounded_eventually_nat (g := fun k => 1 ^ k / (k.factorial : ℝ))
    (Real.summable_pow_div_factorial 1) ?_
  filter_upwards [eventually_ge_atTop (⌈‖z‖⌉₊ + 1)] with k hk
  have hk' : ‖z‖ + 1 ≤ k := by
    have := Nat.le_ceil ‖z‖
    have : ((⌈‖z‖⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    push_cast at this
    linarith
  have h1 : 1 ≤ ‖z + k‖ := by
    have := norm_sub_norm_le (k : ℂ) (-z)
    rw [norm_neg, Complex.norm_natCast, sub_neg_eq_add, add_comm] at this
    linarith
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast,
    div_le_div_iff₀ (by positivity) hf]
  nlinarith

/-- `t^(z-1) e^(-t)` is integrable on `(1, ∞)`. -/
theorem integrableOn_prymIntegral (z : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 1) * Complex.exp (-(t : ℂ))) (Ioi 1) := by
  set s := max z.re 1 with hs
  have hs0 : 0 < s := lt_max_of_lt_right one_pos
  have hG := (Real.GammaIntegral_convergent hs0).mono_set (Ioi_subset_Ioi zero_le_one)
  refine hG.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    have ht' : (0 : ℝ) < t := zero_lt_one.trans ht
    exact ((continuousAt_ofReal_cpow_const t (z - 1) (Or.inr ht'.ne')).mul
      (by fun_prop : Continuous fun t : ℝ => Complex.exp (-(t : ℂ))).continuousAt)
      |>.continuousWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht' : (1 : ℝ) < t := ht
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht'
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_exp, neg_re, ofReal_re, sub_re,
      one_re, mul_comm]
    gcongr
    · exact ht'.le
    · simp [hs]

/-- `∫₁^∞ t^z e^{-t} dt = e⁻¹ + z ∫₁^∞ t^{z-1} e^{-t} dt`, by parts. -/
theorem prymIntegral_add_one (z : ℂ) :
    prymIntegral (z + 1) = Complex.exp (-1) + z * prymIntegral z := by
  have hu : ∀ t ∈ Ioi (1 : ℝ), HasDerivAt (fun t : ℝ => (t : ℂ) ^ z) (z * (t : ℂ) ^ (z - 1)) t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
    have := ((hasDerivAt_id (t : ℂ)).cpow_const (c := z) (by simpa using ht0)).comp_ofReal
    simpa using this
  have hv : ∀ t ∈ Ioi (1 : ℝ), HasDerivAt (fun t : ℝ => -Complex.exp (-(t : ℂ)))
      (Complex.exp (-(t : ℂ))) t := by
    intro t _
    have := ((hasDerivAt_id (t : ℂ)).neg.cexp.neg).comp_ofReal
    simpa using this
  have huv' : IntegrableOn (fun t : ℝ => (t : ℂ) ^ z * Complex.exp (-(t : ℂ))) (Ioi 1) := by
    simpa using integrableOn_prymIntegral (z + 1)
  have hu'v : IntegrableOn (fun t : ℝ => z * (t : ℂ) ^ (z - 1) * -Complex.exp (-(t : ℂ)))
      (Ioi 1) := by
    have := ((integrableOn_prymIntegral z).const_mul (-z))
    refine IntegrableOn.congr_fun this (fun t _ => by ring) measurableSet_Ioi
  have hzero : Tendsto (fun t : ℝ => (t : ℂ) ^ z * -Complex.exp (-(t : ℂ))) (𝓝[>] 1)
      (𝓝 (-Complex.exp (-1))) := by
    have hc : ContinuousAt (fun t : ℝ => (t : ℂ) ^ z * -Complex.exp (-(t : ℂ))) 1 :=
      (continuousAt_ofReal_cpow_const 1 z (Or.inr one_ne_zero)).mul
        (by fun_prop : Continuous fun t : ℝ => -Complex.exp (-(t : ℂ))).continuousAt
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hinfty : Tendsto (fun t : ℝ => (t : ℂ) ^ z * -Complex.exp (-(t : ℂ))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero z.re 1 one_pos).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
    simp
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v hzero hinfty
  simp only [prymIntegral, add_sub_cancel_right]
  rw [h, sub_neg_eq_add, zero_add, ← MeasureTheory.integral_const_mul, sub_eq_add_neg,
    ← MeasureTheory.integral_neg]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  ring

/-- `z S(z) = e⁻¹ + S(z+1)`. -/
theorem mul_prymSeries {z : ℂ} (hz : ∀ k : ℕ, z ≠ -k) :
    z * prymSeries z = Complex.exp (-1) + prymSeries (z + 1) := by
  have hzk : ∀ k : ℕ, z + k ≠ 0 := fun k h => hz k (eq_neg_of_add_eq_zero_left h)
  have hexp : HasSum (fun k : ℕ => (-1 : ℂ) ^ k / k.factorial) (Complex.exp (-1)) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp (-1 : ℂ)
  set g : ℕ → ℂ := fun k => (-1 : ℂ) ^ k * k / ((z + k) * k.factorial) with hg
  have hsplit : ∀ k : ℕ, z * ((-1 : ℂ) ^ k / ((z + k) * k.factorial)) =
      (-1 : ℂ) ^ k / k.factorial - g k := by
    intro k
    have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    simp only [hg]
    field_simp
    have := hzk k
    field_simp
    ring
  have hgs : Summable g := by
    have h1 := (summable_prym z).mul_left z
    simp_rw [hsplit] at h1
    have := hexp.summable.sub h1
    simpa using this
  have hg0 : ∀ j : ℕ, g (j + 1) = -((-1 : ℂ) ^ j / ((z + 1 + j) * j.factorial)) := by
    intro j
    have hf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
    have hzj : z + 1 + j ≠ 0 := by
      have := hzk (j + 1); push_cast at this; rwa [add_assoc, add_comm (1 : ℂ)]
    simp only [hg, Nat.factorial_succ]
    push_cast
    field_simp
    rw [show z + (j + 1) = z + 1 + j by ring]
    field_simp
    ring
  have hgsum : ∑' k, g k = -prymSeries (z + 1) := by
    rw [hgs.tsum_eq_zero_add, prymSeries, ← tsum_neg]
    simp only [hg, Nat.cast_zero, mul_zero, zero_div, zero_add]
    exact tsum_congr hg0
  rw [prymSeries, ← tsum_mul_left]
  simp_rw [hsplit]
  rw [(hexp.summable).tsum_sub hgs, hexp.tsum_eq, hgsum, sub_neg_eq_add]

/-- The `k`-th term `(-1)ᵏ t^{z+k-1}/k!` of `t^{z-1} e^{-t}`. -/
def prymTerm (z : ℂ) (k : ℕ) (t : ℝ) : ℂ := (-1 : ℂ) ^ k / k.factorial * (t : ℂ) ^ (z + k - 1)

/-- For `Re(z + k) > 0`, the `k`-th term `(-1)^k t^(z+k-1)/k!` is integrable on `(0, 1]`. -/
theorem integrableOn_prymTerm {z : ℂ} {k : ℕ} (hk : 0 < (z + k).re) :
    IntegrableOn (prymTerm z k) (Ioc 0 1) := by
  have hre : -1 < (z + k - 1).re := by simp at hk ⊢; linarith
  have := (intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := 1) hre).const_mul
    ((-1 : ℂ) ^ k / k.factorial)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
  exact this

/-- `∫₀¹ (-1)^k t^(z+k-1)/k! dt = (-1)^k/((z + k) k!)` for `Re(z + k) > 0`. -/
theorem integral_prymTerm {z : ℂ} {k : ℕ} (hk : 0 < (z + k).re) :
    ∫ t in Ioc (0 : ℝ) 1, prymTerm z k t = (-1 : ℂ) ^ k / ((z + k) * k.factorial) := by
  have hre : -1 < (z + k - 1).re := by simp at hk ⊢; linarith
  have hzk : z + k ≠ 0 := fun h => by rw [h, zero_re] at hk; exact lt_irrefl _ hk
  simp only [prymTerm]
  rw [MeasureTheory.integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
    integral_cpow (Or.inl hre), sub_add_cancel, ofReal_one, one_cpow, ofReal_zero,
    zero_cpow hzk, sub_zero]
  have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  field_simp

/-- `∫₀¹ |(-1)^k t^(z+k-1)/k!| dt = 1/(k! Re(z + k))` for `Re(z + k) > 0`. -/
theorem integral_norm_prymTerm {z : ℂ} {k : ℕ} (hk : 0 < (z + k).re) :
    ∫ t in Ioc (0 : ℝ) 1, ‖prymTerm z k t‖ = 1 / (k.factorial * (z + k).re) := by
  have hk' : 0 < z.re + k := by simpa using hk
  have hre : -1 < z.re + k - 1 := by linarith
  have heq : EqOn (fun t => ‖prymTerm z k t‖) (fun t => 1 / k.factorial * t ^ (z.re + k - 1))
      (Ioc 0 1) := by
    intro t ht
    simp only [prymTerm]
    rw [norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast,
      norm_cpow_eq_rpow_re_of_pos ht.1]
    simp
  rw [setIntegral_congr_fun measurableSet_Ioc heq, MeasureTheory.integral_const_mul,
    ← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl hre)]
  rw [sub_add_cancel, Real.one_rpow, Real.zero_rpow hk'.ne', sub_zero]
  simp only [add_re, natCast_re]
  field_simp

/-- `∫₀¹ ∑_{k ≥ m} (-1)ᵏ t^{z+k-1}/k! dt = ∑_{k ≥ m} (-1)ᵏ/((z+k) k!)` when `Re z + m > 0`. -/
theorem integral_tsum_prymTerm {z : ℂ} {m : ℕ} (hm : 0 < z.re + m) :
    ∫ t in Ioc (0 : ℝ) 1, ∑' j : ℕ, prymTerm z (j + m) t =
      ∑' j : ℕ, (-1 : ℂ) ^ (j + m) / ((z + (j + m : ℕ)) * (j + m).factorial) := by
  have hk : ∀ j : ℕ, 0 < (z + (j + m : ℕ)).re := fun j => by
    have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
    simp only [add_re, natCast_re, Nat.cast_add]
    linarith
  have hsum : Summable fun j : ℕ => ∫ t in Ioc (0 : ℝ) 1, ‖prymTerm z (j + m) t‖ := by
    simp_rw [integral_norm_prymTerm (hk _)]
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
      ((Real.summable_pow_div_factorial 1).mul_left (1 / (z.re + m)))
    · have := hk j; positivity
    · have hf : (0 : ℝ) < j.factorial := by exact_mod_cast j.factorial_pos
      have hf' : (j.factorial : ℝ) ≤ (j + m).factorial := by
        exact_mod_cast Nat.factorial_le (Nat.le_add_right j m)
      have hre : z.re + m ≤ (z + (j + m : ℕ)).re := by
        have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
        simp only [add_re, natCast_re, Nat.cast_add]
        linarith
      rw [one_pow, div_mul_div_comm, one_mul, one_div_le_one_div (by have := hk j; positivity)
        (by positivity)]
      nlinarith [mul_le_mul hf' hre hm.le (by positivity : (0 : ℝ) ≤ (j + m).factorial)]
  rw [← integral_tsum_of_summable_integral_norm (fun j => integrableOn_prymTerm (hk j)) hsum]
  exact tsum_congr fun j => integral_prymTerm (hk j)

/-- `t^{z-1} e^{-t} = ∑ₖ (-1)ᵏ t^{z+k-1}/k!` for `t > 0`. -/
theorem hasSum_prymTerm (z : ℂ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun k => prymTerm z k t) ((t : ℂ) ^ (z - 1) * Complex.exp (-(t : ℂ))) := by
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hexp : HasSum (fun k : ℕ => (-(t : ℂ)) ^ k / k.factorial) (Complex.exp (-(t : ℂ))) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  convert hexp.mul_left ((t : ℂ) ^ (z - 1)) using 1
  funext k
  simp only [prymTerm]
  rw [show z + k - 1 = (z - 1) + k by ring, cpow_add _ _ ht0, cpow_natCast, neg_pow]
  ring

/-- Prym's formula for `Re z > 0`. -/
theorem Gamma_eq_prym_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    Complex.Gamma z = prymIntegral z + prymSeries z := by
  rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral]
  have hint : IntegrableOn (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ) * (t : ℂ) ^ (z - 1)) (Ioi 0) :=
    Complex.GammaIntegral_convergent hz
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi zero_le_one)), add_comm]
  congr 1
  · refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    push_cast
    ring
  have h := integral_tsum_prymTerm (z := z) (m := 0) (by simpa using hz)
  simp only [add_zero] at h
  rw [prymSeries, ← h]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  rw [(hasSum_prymTerm z ht.1).tsum_eq]
  push_cast
  ring

/-- Prym's formula for all `z ∉ -ℕ`, via the recursion of `Γ`. -/
theorem Gamma_eq_prym {z : ℂ} (hz : ∀ k : ℕ, z ≠ -k) :
    Complex.Gamma z = prymIntegral z + prymSeries z := by
  obtain ⟨n, hn⟩ := exists_nat_gt (-z.re)
  induction n generalizing z with
  | zero => exact Gamma_eq_prym_of_re_pos (by simpa using hn)
  | succ n ih =>
    have hz1 : ∀ k : ℕ, z + 1 ≠ -k := fun k h =>
      hz (k + 1) (by push_cast; linear_combination h)
    have h1 := ih hz1 (by simp only [add_re, one_re]; push_cast at hn; linarith)
    have hz0 : z ≠ 0 := by simpa using hz 0
    have hP : prymIntegral (z + 1) + prymSeries (z + 1) =
        z * (prymIntegral z + prymSeries z) := by
      rw [prymIntegral_add_one, mul_add, mul_prymSeries hz]; ring
    have hG := Complex.Gamma_add_one z hz0
    rw [h1, hP] at hG
    exact (mul_left_cancel₀ hz0 hG).symm

/-- DLMF 5.9.4, Prym's decomposition: `Γ(z) = ∫₁^∞ t^(z-1) e^(-t) dt + ∑ₖ (-1)^k/((z + k) k!)` for
`z` not a nonpositive integer. -/
@[dlmf 5.9.E4]
theorem Gamma_incomplete_sum {z : ℂ} (hz : ∀ k : ℕ, z ≠ -k) :
    Complex.Gamma z =
      (∫ t : ℝ in Set.Ioi 1, (t : ℂ) ^ (z - 1) * Complex.exp (-(t : ℂ))) +
        ∑' k : ℕ, (-1 : ℂ) ^ k / ((z + k) * k.factorial) := by
  simpa only [prymIntegral, prymSeries] using Gamma_eq_prym hz

end Prym

open Set in
/-- The Cauchy–Saalschütz representation (Temme §3.2.2), from Prym's formula: on `(1, ∞)`
each power `t^{z+k-1}`, `k ≤ n`, integrates to `-1/(z+k)`, and on `(0, 1]` the tail of the
exponential series integrates to the remaining terms of Prym's series. -/
@[dlmf 5.9.E5]
theorem Gamma_truncated_exp {z : ℂ} {n : ℕ}
    (hlo : -((n + 1 : ℕ) : ℝ) < z.re) (hhi : z.re < -n) :
    Complex.Gamma z =
      ∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (z - 1) *
          (Complex.exp (-(t : ℂ)) -
            ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (t : ℂ) ^ k / k.factorial) := by
  push_cast at hlo
  have hz : ∀ k : ℕ, z ≠ -k := by
    intro k hk
    have h := congrArg Complex.re hk
    simp only [neg_re, natCast_re] at h
    rw [h] at hlo hhi
    have h1 : (n : ℝ) < k := by linarith
    have h2 : (k : ℝ) < n + 1 := by linarith
    have h1' : n < k := by exact_mod_cast h1
    have h2' : k < n + 1 := by exact_mod_cast h2
    omega
  -- the integrand
  set f : ℝ → ℂ := fun t => (t : ℂ) ^ (z - 1) * (Complex.exp (-(t : ℂ)) -
    ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (t : ℂ) ^ k / k.factorial) with hf
  have hfk : ∀ t : ℝ, 0 < t → f t = (t : ℂ) ^ (z - 1) * Complex.exp (-(t : ℂ)) -
      ∑ k ∈ Finset.range (n + 1), prymTerm z k t := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    simp only [hf, mul_sub, Finset.mul_sum, prymTerm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show z + k - 1 = (z - 1) + k by ring, cpow_add _ _ ht0, cpow_natCast]
    ring
  -- on `(0, 1]`: the tail of the series
  have htail : ∀ t ∈ Ioc (0 : ℝ) 1, f t = ∑' j : ℕ, prymTerm z (j + (n + 1)) t := by
    intro t ht
    rw [hfk t ht.1, ← (hasSum_prymTerm z ht.1).tsum_eq,
      ← (hasSum_prymTerm z ht.1).summable.sum_add_tsum_nat_add (n + 1)]
    ring
  have hm : 0 < z.re + (n + 1 : ℕ) := by push_cast; linarith
  -- on `(1, ∞)`: Euler's integral minus finitely many powers
  have hpow : ∀ k ∈ Finset.range (n + 1), IntegrableOn (prymTerm z k) (Ioi 1) ∧
      ∫ t in Ioi (1 : ℝ), prymTerm z k t = -((-1 : ℂ) ^ k / ((z + k) * k.factorial)) := by
    intro k hk
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hre : (z + k - 1).re < -1 := by simp; linarith
    have hzk : z + k ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have hf' : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    refine ⟨(integrableOn_Ioi_cpow_of_lt hre zero_lt_one).const_mul _, ?_⟩
    simp only [prymTerm]
    rw [MeasureTheory.integral_const_mul, integral_Ioi_cpow_of_lt hre zero_lt_one, sub_add_cancel,
      ofReal_one, one_cpow]
    field_simp
  have hint1 : IntegrableOn f (Ioi 1) := by
    have := (integrableOn_prymIntegral z).sub (integrable_finsetSum _ fun k hk => (hpow k hk).1)
    refine IntegrableOn.congr_fun this (fun t ht => ?_) measurableSet_Ioi
    rw [hfk t (zero_lt_one.trans ht)]
    simp
  have hint0 : IntegrableOn f (Ioc 0 1) := by
    -- `|e^{-t} - Pₙ(t)| ≤ C t^{n+1}` on `(0, 1]`
    set C : ℝ := ((n + 1 : ℕ).succ : ℝ) / ((n + 1).factorial * (n + 1 : ℕ))
    have hrpow : IntegrableOn (fun t : ℝ => C * t ^ (z.re + n)) (Ioc 0 1) := by
      have hre : -1 < z.re + n := by linarith
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hre).const_mul C
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
    refine hrpow.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioc
      exact ((continuousAt_ofReal_cpow_const t (z - 1) (Or.inr ht.1.ne')).mul
        (by fun_prop : Continuous fun t : ℝ => Complex.exp (-(t : ℂ)) -
          ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (t : ℂ) ^ k / k.factorial).continuousAt)
        |>.continuousWithinAt
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
      have ht0 : 0 < t := ht.1
      have hreal : Complex.exp (-(t : ℂ)) -
          ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (t : ℂ) ^ k / k.factorial =
          ((Real.exp (-t) - ∑ k ∈ Finset.range (n + 1), (-t) ^ k / k.factorial : ℝ) : ℂ) := by
        push_cast
        congr 1
        refine Finset.sum_congr rfl fun k _ => by ring
      have hb := Real.exp_bound (x := -t) (by rw [abs_neg, abs_of_pos ht0]; exact ht.2)
        (n := n + 1) (Nat.succ_pos n)
      rw [abs_neg, abs_of_pos ht0] at hb
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, hreal, Complex.norm_real, Real.norm_eq_abs]
      have hpow' : t ^ (n + 1) = t * t ^ (n : ℝ) := by
        rw [Real.rpow_natCast]; ring
      calc t ^ (z - 1).re * |Real.exp (-t) - ∑ k ∈ Finset.range (n + 1), (-t) ^ k / k.factorial|
          ≤ t ^ (z - 1).re * (t ^ (n + 1) * C) :=
            mul_le_mul_of_nonneg_left hb (by positivity)
        _ = C * t ^ (z.re + n) := by
            rw [hpow', sub_re, one_re, Real.rpow_add ht0, Real.rpow_sub_one ht0.ne']
            field_simp
  -- assemble
  have hΓ : Complex.Gamma z = prymIntegral z + prymSeries z := Gamma_eq_prym hz
  rw [hΓ, prymSeries, ← Ioc_union_Ioi_eq_Ioi zero_le_one,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hint0 hint1,
    setIntegral_congr_fun measurableSet_Ioc htail, integral_tsum_prymTerm hm]
  have h1 : ∫ t in Ioi (1 : ℝ), f t = prymIntegral z +
      ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k / ((z + k) * k.factorial) := by
    rw [setIntegral_congr_fun measurableSet_Ioi
        (fun t (ht : 1 < t) => hfk t (zero_lt_one.trans ht)),
      integral_sub (integrableOn_prymIntegral z)
        (integrable_finsetSum _ fun k hk => (hpow k hk).1),
      integral_finsetSum _ fun k hk => (hpow k hk).1, prymIntegral,
      Finset.sum_congr rfl fun k hk => (hpow k hk).2, Finset.sum_neg_distrib, sub_neg_eq_add]
  rw [h1, ← (summable_prym z).sum_add_tsum_nat_add (n + 1)]
  push_cast
  ring

section Oscillatory

/-! ### Oscillatory integrals (DLMF 5.9.6–9)

For `x < 1` and `t > 0` we write `t^{x-1} = Γ(1-x)⁻¹ ∫₀^∞ s^{-x} e^{-ts} ds` and exchange the
order of integration over `(0, R) × (0, ∞)`. The inner integrals `∫₀^R e^{-st} cos t dt` and
`∫₀^R e^{-st} sin t dt` are elementary, and dominated convergence as `R → ∞` leaves the Mellin
transform `∫₀^∞ s^{a-1}/(1+s²) ds = π/(2 sin(πa/2))`, itself the beta integral
`∫₀^∞ u^{b-1}/(1+u) du = Γ(b) Γ(1-b)`. -/

open Set

/-- `∫₀^∞ u^{b-1}/(1+u) du = Γ(b) Γ(1-b)` for `0 < b < 1`, via
`1/(1+u) = ∫₀^∞ e^{-(1+u)r} dr` and Fubini. -/
theorem integral_rpow_div_one_add {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    IntegrableOn (fun u : ℝ => u ^ (b - 1) / (1 + u)) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), u ^ (b - 1) / (1 + u) = Real.Gamma b * Real.Gamma (1 - b) := by
  set μ := volume.restrict (Ioi (0 : ℝ))
  set f : ℝ → ℝ → ℝ := fun u r => u ^ (b - 1) * Real.exp (-((1 + u) * r)) with hf
  have hnn : ∀ u r : ℝ, 0 < u → 0 ≤ f u r := fun u r hu => by simp only [hf]; positivity
  -- inner integral in `u`
  have hinner_u : ∀ r : ℝ, 0 < r → IntegrableOn (fun u => f u r) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), f u r = Real.exp (-r) * (r ^ (-b) * Real.Gamma b) := by
    intro r hr
    have hconv := (Real.GammaIntegral_convergent hb0)
    have heq : ∀ u : ℝ, f u r = Real.exp (-r) * (u ^ (b - 1) * Real.exp (-(r * u))) := by
      intro u; simp only [hf]; rw [mul_left_comm, ← Real.exp_add]; ring_nf
    have hint : IntegrableOn (fun u : ℝ => u ^ (b - 1) * Real.exp (-(r * u))) (Ioi 0) := by
      have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := b - 1) (b := r)
        (by linarith) one_pos hr
      refine IntegrableOn.congr_fun this (fun u _ => ?_) measurableSet_Ioi
      simp [Real.rpow_one]
    refine ⟨IntegrableOn.congr_fun (hint.const_mul (Real.exp (-r))) (fun u _ => (heq u).symm)
      measurableSet_Ioi, ?_⟩
    simp_rw [heq]
    rw [MeasureTheory.integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hb0 hr,
      Real.rpow_neg hr.le, one_div, Real.inv_rpow hr.le]
  -- inner integral in `r`
  have hinner_r : ∀ u : ℝ, 0 < u → ∫ r in Ioi (0 : ℝ), f u r = u ^ (b - 1) / (1 + u) := by
    intro u hu
    have hm : -(1 + u) < 0 := by linarith
    simp only [hf]
    rw [MeasureTheory.integral_const_mul]
    have := integral_exp_mul_Ioi hm 0
    simp only [mul_zero, Real.exp_zero] at this
    rw [show (fun r => Real.exp (-((1 + u) * r))) = fun r => Real.exp (-(1 + u) * r) by
      funext r; ring_nf, this]
    field_simp
  have hmeas : AEStronglyMeasurable (Function.uncurry f) (μ.prod μ) :=
    (by fun_prop : Measurable fun p : ℝ × ℝ =>
      p.1 ^ (b - 1) * Real.exp (-((1 + p.1) * p.2))).aestronglyMeasurable
  have hprod : Integrable (Function.uncurry f) (μ.prod μ) := by
    rw [integrable_prod_iff' hmeas]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact (hinner_u r hr).1
    · have hG := (Real.GammaIntegral_convergent (by linarith : 0 < 1 - b)).const_mul
        (Real.Gamma b)
      refine IntegrableOn.congr_fun hG (fun r hr => ?_) measurableSet_Ioi
      have hr' : (0 : ℝ) < r := hr
      simp only [Function.uncurry_apply_pair]
      rw [setIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) =>
        Real.norm_of_nonneg (hnn u r hu), (hinner_u r hr').2]
      rw [show (1 - b - 1) = -b by ring]
      ring
  have hswap := integral_integral_swap hprod
  have hL : ∫ u in Ioi (0 : ℝ), ∫ r in Ioi (0 : ℝ), f u r =
      ∫ u in Ioi (0 : ℝ), u ^ (b - 1) / (1 + u) :=
    setIntegral_congr_fun measurableSet_Ioi fun u hu => hinner_r u hu
  have hR : ∫ r in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), f u r = Real.Gamma b * Real.Gamma (1 - b) := by
    rw [setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => (hinner_u r hr).2,
      Real.Gamma_eq_integral (by linarith : 0 < 1 - b), ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    rw [show (1 - b - 1) = -b by ring]
    ring
  refine ⟨?_, by rw [← hL, hswap, hR]⟩
  have := hprod.integral_prod_left
  exact IntegrableOn.congr_fun this (fun u hu => hinner_r u hu) measurableSet_Ioi

/-- `∫₀^∞ s^{a-1}/(1+s²) ds = π/(2 sin(πa/2))` for `0 < a < 2`. -/
theorem integral_rpow_div_one_add_sq {a : ℝ} (ha0 : 0 < a) (ha2 : a < 2) :
    IntegrableOn (fun s : ℝ => s ^ (a - 1) / (1 + s ^ 2)) (Ioi 0) ∧
      ∫ s in Ioi (0 : ℝ), s ^ (a - 1) / (1 + s ^ 2) = π / (2 * Real.sin (π * a / 2)) := by
  obtain ⟨hint, hval⟩ := integral_rpow_div_one_add (b := a / 2) (by positivity) (by linarith)
  set g : ℝ → ℝ := fun u => u ^ (a / 2 - 1) / (1 + u) with hg
  have heq : EqOn (fun s : ℝ => (|(2 : ℝ)| * s ^ ((2 : ℝ) - 1)) • g (s ^ (2 : ℝ)))
      (fun s => 2 * (s ^ (a - 1) / (1 + s ^ 2))) (Ioi 0) := by
    intro s hs
    have hs' : (0 : ℝ) < s := hs
    simp only [hg, smul_eq_mul, Real.rpow_two, abs_two]
    rw [← Real.rpow_natCast s 2, ← Real.rpow_mul hs'.le]
    push_cast
    rw [show (2 : ℝ) * (a / 2 - 1) = a - 2 by ring, show (2 : ℝ) - 1 = 1 by norm_num,
      Real.rpow_one, show a - 1 = 1 + (a - 2) by ring, Real.rpow_add hs', Real.rpow_one]
    ring
  have hint' : IntegrableOn (fun s : ℝ => 2 * (s ^ (a - 1) / (1 + s ^ 2))) (Ioi 0) :=
    ((integrableOn_Ioi_comp_rpow_iff g two_ne_zero).mpr hint).congr_fun heq measurableSet_Ioi
  refine ⟨IntegrableOn.congr_fun (hint'.const_mul (1 / 2)) (fun s _ => by ring)
    measurableSet_Ioi, ?_⟩
  have h := integral_comp_rpow_Ioi g (two_ne_zero : (2 : ℝ) ≠ 0)
  rw [setIntegral_congr_fun measurableSet_Ioi heq, MeasureTheory.integral_const_mul, hg,
    hval, Real.Gamma_mul_Gamma_one_sub, show π * (a / 2) = π * a / 2 by ring] at h
  have hs : Real.sin (π * a / 2) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi (by positivity)
    (by nlinarith [Real.pi_pos])).ne'
  rw [eq_div_iff (mul_ne_zero two_ne_zero hs)]
  rw [eq_div_iff hs] at h
  linarith

/-- `t^{x-1} = Γ(1-x)⁻¹ ∫₀^∞ s^{-x} e^{-ts} ds` for `x < 1`, `t > 0`. -/
theorem rpow_eq_recip_Gamma_mul_integral {x t : ℝ} (hx : x < 1) (ht : 0 < t) :
    t ^ (x - 1) = (Real.Gamma (1 - x))⁻¹ *
      ∫ s in Ioi (0 : ℝ), s ^ (-x) * Real.exp (-(t * s)) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1 - x) (r := t) (by linarith) ht
  rw [show (1 - x - 1) = -x by ring] at h
  rw [h, one_div, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le, neg_sub]
  have := (Real.Gamma_pos_of_pos (by linarith : 0 < 1 - x)).ne'
  field_simp

/-- `s^(-x) e^(-ts)` is integrable on `(0, ∞)` for `x < 1`, `t > 0`. -/
theorem integrableOn_rpow_neg_mul_exp {x t : ℝ} (hx : x < 1) (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => s ^ (-x) * Real.exp (-(t * s))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -x) (b := t) (by linarith)
    one_pos ht
  refine IntegrableOn.congr_fun this (fun u _ => ?_) measurableSet_Ioi
  simp [Real.rpow_one]

/-- Fubini for `∫₀^R t^{x-1} g(t) dt`. -/
theorem integral_rpow_mul_eq {x R : ℝ} (hx : x < 1) (hR : 0 ≤ R) {g : ℝ → ℝ} (hg : Continuous g)
    (hint : IntegrableOn (fun t => |g t| * t ^ (x - 1)) (Ioc 0 R)) :
    ∫ t in (0 : ℝ)..R, t ^ (x - 1) * g t = (Real.Gamma (1 - x))⁻¹ *
      ∫ s in Ioi (0 : ℝ), s ^ (-x) * ∫ t in (0 : ℝ)..R, Real.exp (-(s * t)) * g t := by
  set μ := volume.restrict (Ioc (0 : ℝ) R)
  set ν := volume.restrict (Ioi (0 : ℝ))
  set F : ℝ → ℝ → ℝ := fun t s => s ^ (-x) * Real.exp (-(t * s)) * g t with hF
  have hG := Real.Gamma_pos_of_pos (by linarith : 0 < 1 - x)
  have hinner : ∀ t : ℝ, 0 < t → ∫ s in Ioi (0 : ℝ), s ^ (-x) * Real.exp (-(t * s)) =
      Real.Gamma (1 - x) * t ^ (x - 1) := by
    intro t ht
    rw [rpow_eq_recip_Gamma_mul_integral hx ht]
    field_simp
  have hmeas : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν) :=
    (by fun_prop : Measurable fun p : ℝ × ℝ =>
      p.2 ^ (-x) * Real.exp (-(p.1 * p.2)) * g p.1).aestronglyMeasurable
  have hprod : Integrable (Function.uncurry F) (μ.prod ν) := by
    rw [integrable_prod_iff hmeas]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact (integrableOn_rpow_neg_mul_exp hx ht.1).mul_const (g t)
    · refine IntegrableOn.congr_fun (hint.const_mul (Real.Gamma (1 - x))) (fun t ht => ?_)
        measurableSet_Ioc
      simp only [Function.uncurry_apply_pair, hF]
      rw [setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) => by
          rw [norm_mul, Real.norm_of_nonneg (by positivity), Real.norm_eq_abs],
        MeasureTheory.integral_mul_const, hinner t ht.1]
      ring
  have hswap := integral_integral_swap hprod
  rw [intervalIntegral.integral_of_le hR]
  have hL : ∫ t in Ioc (0 : ℝ) R, ∫ s in Ioi (0 : ℝ), F t s =
      Real.Gamma (1 - x) * ∫ t in Ioc (0 : ℝ) R, t ^ (x - 1) * g t := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    simp only [hF]
    rw [MeasureTheory.integral_mul_const, hinner t ht.1]
    ring
  have hR' : ∫ s in Ioi (0 : ℝ), ∫ t in Ioc (0 : ℝ) R, F t s =
      ∫ s in Ioi (0 : ℝ), s ^ (-x) * ∫ t in (0 : ℝ)..R, Real.exp (-(s * t)) * g t := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [intervalIntegral.integral_of_le hR, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    simp only [hF]
    ring_nf
  rw [hL, hR'] at hswap
  rw [← hswap]
  field_simp

/-- `∫₀^R e^{-st} cos t dt`. -/
theorem integral_exp_mul_cos {s R : ℝ} :
    ∫ t in (0 : ℝ)..R, Real.exp (-(s * t)) * Real.cos t =
      (s - Real.exp (-(s * R)) * (s * Real.cos R - Real.sin R)) / (s ^ 2 + 1) := by
  have hd : ∀ t ∈ uIcc 0 R, HasDerivAt
      (fun t => Real.exp (-(s * t)) * (Real.sin t - s * Real.cos t) / (s ^ 2 + 1))
      (Real.exp (-(s * t)) * Real.cos t) t := by
    intro t _
    have := ((((hasDerivAt_id t).const_mul s).neg.exp).mul
      ((Real.hasDerivAt_sin t).sub ((Real.hasDerivAt_cos t).const_mul s))).div_const (s ^ 2 + 1)
    have hs2 : s ^ 2 + 1 ≠ 0 := by positivity
    have hs2' : 1 + s ^ 2 ≠ 0 := by positivity
    exact this.congr_deriv (by deriv_simp)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun t => Real.exp (-(s * t)) * Real.cos t).intervalIntegrable _ _)]
  simp only [mul_zero, neg_zero, Real.exp_zero, Real.sin_zero, Real.cos_zero]
  ring

/-- `∫₀^R e^{-st} sin t dt`. -/
theorem integral_exp_mul_sin {s R : ℝ} :
    ∫ t in (0 : ℝ)..R, Real.exp (-(s * t)) * Real.sin t =
      (1 - Real.exp (-(s * R)) * (s * Real.sin R + Real.cos R)) / (s ^ 2 + 1) := by
  have hd : ∀ t ∈ uIcc 0 R, HasDerivAt
      (fun t => -(Real.exp (-(s * t)) * (Real.cos t + s * Real.sin t)) / (s ^ 2 + 1))
      (Real.exp (-(s * t)) * Real.sin t) t := by
    intro t _
    have := ((((hasDerivAt_id t).const_mul s).neg.exp).mul
      ((Real.hasDerivAt_cos t).add ((Real.hasDerivAt_sin t).const_mul s))).neg.div_const
      (s ^ 2 + 1)
    have hs2 : s ^ 2 + 1 ≠ 0 := by positivity
    have hs2' : 1 + s ^ 2 ≠ 0 := by positivity
    exact this.congr_deriv (by deriv_simp)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun t => Real.exp (-(s * t)) * Real.sin t).intervalIntegrable _ _)]
  simp only [mul_zero, neg_zero, Real.exp_zero, Real.sin_zero, Real.cos_zero]
  ring

/-- Dominated convergence for `∫₀^∞ s^{-x} K(s, R) ds` as `R → ∞`, where
`K(s, R) = (p(s) - e^{-sR} q(s, R))/(s² + 1)` with `|q(s, R)| ≤ s + 1`. -/
theorem tendsto_integral_rpow_neg_mul_kernel {x : ℝ} (hx : x < 1) {p : ℝ → ℝ}
    {q : ℝ → ℝ → ℝ} (hp : Continuous p) (hq : Continuous (Function.uncurry q))
    (hqb : ∀ s R, 0 < s → |q s R| ≤ s + 1)
    (hpint : IntegrableOn (fun s : ℝ => s ^ (-x) * (|p s| / (s ^ 2 + 1))) (Ioi 0)) :
    Tendsto (fun R : ℝ => ∫ s in Ioi (0 : ℝ),
        s ^ (-x) * ((p s - Real.exp (-(s * R)) * q s R) / (s ^ 2 + 1))) atTop
      (𝓝 (∫ s in Ioi (0 : ℝ), s ^ (-x) * (p s / (s ^ 2 + 1)))) := by
  have hb2 := (Real.GammaIntegral_convergent (by linarith : 0 < 2 - x))
  have hb1 := (Real.GammaIntegral_convergent (by linarith : 0 < 1 - x))
  have hbint : Integrable (fun s : ℝ => s ^ (-x) * (|p s| / (s ^ 2 + 1)) +
      (Real.exp (-s) * s ^ (2 - x - 1) + Real.exp (-s) * s ^ (1 - x - 1)))
      (volume.restrict (Ioi 0)) := hpint.add (hb2.add hb1)
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun s => s ^ (-x) * (|p s| / (s ^ 2 + 1)) +
      (Real.exp (-s) * s ^ (2 - x - 1) + Real.exp (-s) * s ^ (1 - x - 1))) ?_ ?_ hbint ?_
  · exact Eventually.of_forall fun R => (by fun_prop : Measurable fun s : ℝ =>
      s ^ (-x) * ((p s - Real.exp (-(s * R)) * q s R) / (s ^ 2 + 1))).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop 1] with R hR
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs' : (0 : ℝ) < s := hs
    have hsx : 0 < s ^ (-x) := Real.rpow_pos_of_pos hs' _
    have hd : (0 : ℝ) < s ^ 2 + 1 := by positivity
    have he : Real.exp (-(s * R)) ≤ Real.exp (-s) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hq' := hqb s R hs'
    have hpow2 : s ^ (2 - x - 1) = s ^ (-x) * s := by
      rw [show 2 - x - 1 = -x + 1 by ring, Real.rpow_add hs', Real.rpow_one]
    have hpow1 : s ^ (1 - x - 1) = s ^ (-x) := by ring_nf
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hsx, abs_div, abs_of_pos hd, hpow2, hpow1]
    have h1 : |p s - Real.exp (-(s * R)) * q s R| ≤ |p s| + Real.exp (-s) * (s + 1) := by
      calc |p s - Real.exp (-(s * R)) * q s R|
          ≤ |p s| + |Real.exp (-(s * R)) * q s R| := abs_sub _ _
        _ ≤ |p s| + Real.exp (-s) * (s + 1) := by
          rw [abs_mul, Real.abs_exp]
          gcongr
    have h2 : Real.exp (-s) * (s + 1) / (s ^ 2 + 1) ≤ Real.exp (-s) * (s + 1) :=
      div_le_self (by positivity) (by nlinarith)
    calc s ^ (-x) * (|p s - Real.exp (-(s * R)) * q s R| / (s ^ 2 + 1))
        ≤ s ^ (-x) * ((|p s| + Real.exp (-s) * (s + 1)) / (s ^ 2 + 1)) := by gcongr
      _ = s ^ (-x) * (|p s| / (s ^ 2 + 1)) + s ^ (-x) *
          (Real.exp (-s) * (s + 1) / (s ^ 2 + 1)) := by ring
      _ ≤ s ^ (-x) * (|p s| / (s ^ 2 + 1)) + s ^ (-x) * (Real.exp (-s) * (s + 1)) := by gcongr
      _ = _ := by ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs' : (0 : ℝ) < s := hs
    have hexp : Tendsto (fun R => Real.exp (-(s * R))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun R : ℝ => s * R) atTop atTop :=
        Tendsto.const_mul_atTop hs' tendsto_id
      have := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
      simpa [Function.comp_def] using this
    have hbdd : Tendsto (fun R => Real.exp (-(s * R)) * q s R) atTop (𝓝 0) := by
      refine hexp.zero_mul_isBoundedUnder_le ?_
      exact isBoundedUnder_of_eventually_le (a := s + 1)
        (Eventually.of_forall fun R => by simpa [Real.norm_eq_abs] using hqb s R hs')
    have := ((tendsto_const_nhds (x := p s)).sub hbdd).div_const (s ^ 2 + 1) |>.const_mul
      (s ^ (-x))
    simpa using this

/-- `∫₀^R t^{x-1} cos t dt → π/(2 Γ(1-x) sin(πx/2))` for `0 < x < 1`. -/
theorem tendsto_integral_rpow_mul_cos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R, t ^ (x - 1) * Real.cos t) atTop
      (𝓝 ((Real.Gamma (1 - x))⁻¹ * (π / (2 * Real.sin (π * (2 - x) / 2))))) := by
  obtain ⟨hM, hval⟩ := integral_rpow_div_one_add_sq (a := 2 - x) (by linarith) (by linarith)
  have hpint : IntegrableOn (fun s : ℝ => s ^ (-x) * (|s| / (s ^ 2 + 1))) (Ioi 0) := by
    refine IntegrableOn.congr_fun hM (fun s hs => ?_) measurableSet_Ioi
    have hs' : (0 : ℝ) < s := hs
    show s ^ (2 - x - 1) / (1 + s ^ 2) = s ^ (-x) * (|s| / (s ^ 2 + 1))
    rw [abs_of_pos hs', show 2 - x - 1 = -x + 1 by ring, Real.rpow_add hs', Real.rpow_one]
    ring
  have hlim := tendsto_integral_rpow_neg_mul_kernel hx1 (p := fun s => s)
    (q := fun s R => s * Real.cos R - Real.sin R) continuous_id (by fun_prop)
    (fun s R hs => by
      have := abs_sub (s * Real.cos R) (Real.sin R)
      rw [abs_mul, abs_of_pos hs] at this
      nlinarith [Real.abs_cos_le_one R, Real.abs_sin_le_one R]) hpint
  have hval' : ∫ s in Ioi (0 : ℝ), s ^ (-x) * (s / (s ^ 2 + 1)) =
      π / (2 * Real.sin (π * (2 - x) / 2)) := by
    rw [← hval]
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hs' : (0 : ℝ) < s := hs
    rw [show 2 - x - 1 = -x + 1 by ring, Real.rpow_add hs', Real.rpow_one]
    ring
  rw [hval'] at hlim
  refine (hlim.const_mul (Real.Gamma (1 - x))⁻¹).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with R hR
  have hint : IntegrableOn (fun t => |Real.cos t| * t ^ (x - 1)) (Ioc 0 R) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := R)
      (by linarith : -1 < x - 1))
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR] at this
    refine this.mono' ((by fun_prop : Measurable fun t =>
      |Real.cos t| * t ^ (x - 1)).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (Real.rpow_pos_of_pos ht.1 _)]
    exact mul_le_of_le_one_left (Real.rpow_pos_of_pos ht.1 _).le (Real.abs_cos_le_one t)
  rw [integral_rpow_mul_eq hx1 hR Real.continuous_cos hint]
  simp_rw [integral_exp_mul_cos]

/-- `∫₀^R t^{x-1} sin t dt → π/(2 Γ(1-x) cos(πx/2))` for `-1 < x < 1`. -/
theorem tendsto_integral_rpow_mul_sin {x : ℝ} (hx0 : -1 < x) (hx1 : x < 1) :
    Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R, t ^ (x - 1) * Real.sin t) atTop
      (𝓝 ((Real.Gamma (1 - x))⁻¹ * (π / (2 * Real.sin (π * (1 - x) / 2))))) := by
  obtain ⟨hM, hval⟩ := integral_rpow_div_one_add_sq (a := 1 - x) (by linarith) (by linarith)
  have hpint : IntegrableOn (fun s : ℝ => s ^ (-x) * (|(1 : ℝ)| / (s ^ 2 + 1))) (Ioi 0) := by
    refine IntegrableOn.congr_fun hM (fun s _ => ?_) measurableSet_Ioi
    show s ^ (1 - x - 1) / (1 + s ^ 2) = s ^ (-x) * (|(1 : ℝ)| / (s ^ 2 + 1))
    rw [abs_one, show 1 - x - 1 = -x by ring]
    ring
  have hlim := tendsto_integral_rpow_neg_mul_kernel hx1 (p := fun _ => 1)
    (q := fun s R => s * Real.sin R + Real.cos R) continuous_const (by fun_prop)
    (fun s R hs => by
      have := abs_add_le (s * Real.sin R) (Real.cos R)
      rw [abs_mul, abs_of_pos hs] at this
      nlinarith [Real.abs_cos_le_one R, Real.abs_sin_le_one R]) hpint
  have hval' : ∫ s in Ioi (0 : ℝ), s ^ (-x) * (1 / (s ^ 2 + 1)) =
      π / (2 * Real.sin (π * (1 - x) / 2)) := by
    rw [← hval]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [show 1 - x - 1 = -x by ring]
    ring
  rw [hval'] at hlim
  refine (hlim.const_mul (Real.Gamma (1 - x))⁻¹).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with R hR
  have hint : IntegrableOn (fun t => |Real.sin t| * t ^ (x - 1)) (Ioc 0 R) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := R) hx0)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR] at this
    refine this.mono' ((by fun_prop : Measurable fun t =>
      |Real.sin t| * t ^ (x - 1)).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
    have ht' : 0 < t := ht.1
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (Real.rpow_pos_of_pos ht' _)]
    have h1 : |Real.sin t| ≤ t := by simpa [abs_of_pos ht'] using Real.abs_sin_le_abs (x := t)
    calc |Real.sin t| * t ^ (x - 1) ≤ t * t ^ (x - 1) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_pos_of_pos ht' _).le
      _ = t ^ x := by
          rw [Real.rpow_sub_one ht'.ne']; field_simp
  rw [integral_rpow_mul_eq hx1 hR Real.continuous_sin hint]
  simp_rw [integral_exp_mul_sin]

/-- A cosine integral for Gamma. The integral converges only conditionally at infinity, so it is
stated as the limit of integrals over `(0, R)`; Lean's integral over `(0, ∞)` would be `0`. -/
@[dlmf 5.9.E6]
theorem Gamma_cos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto (fun R : ℝ => ∫ t : ℝ in (0 : ℝ)..R, t ^ (x - 1) * Real.cos t) atTop
      (𝓝 (Real.Gamma x * Real.cos (π * x / 2))) := by
  convert tendsto_integral_rpow_mul_cos hx0 hx1 using 2
  have hrefl := Real.Gamma_mul_Gamma_one_sub x
  have hs : 0 < Real.sin (π * x / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hc : 0 < Real.cos (π * x / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  have hG := Real.Gamma_pos_of_pos (by linarith : 0 < 1 - x)
  have h2 : Real.sin (π * (2 - x) / 2) = Real.sin (π * x / 2) := by
    rw [show π * (2 - x) / 2 = π - π * x / 2 by ring, Real.sin_pi_sub]
  have hdbl : Real.sin (π * x) = 2 * Real.sin (π * x / 2) * Real.cos (π * x / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  rw [h2]
  set S := Real.sin (π * x / 2)
  set C := Real.cos (π * x / 2)
  have hΓx : Real.Gamma x = π / (2 * S * C) / Real.Gamma (1 - x) := by
    rw [eq_div_iff hG.ne', hrefl, hdbl]
  rw [hΓx]
  field_simp

/-- A sine integral for Gamma, with the removable value `π/2` at `x = 0`.
The former literal product `Gamma x * sin (π*x/2)` was false at zero because
`Real.Gamma 0 = 0`. Reflection gives the regular expression used here.
The limit formulation includes the conditionally convergent cases at infinity;
Lean's Bochner integral over `(0, ∞)` would return `0` in those cases. -/
@[dlmf 5.9.E7]
theorem Gamma_sin {x : ℝ} (hx0 : -1 < x) (hx1 : x < 1) :
    Tendsto (fun R : ℝ => ∫ t : ℝ in (0 : ℝ)..R, t ^ (x - 1) * Real.sin t) atTop
      (𝓝 (π / (2 * Real.Gamma (1 - x) * Real.cos (π * x / 2)))) := by
  convert tendsto_integral_rpow_mul_sin hx0 hx1 using 2
  have h1 : Real.sin (π * (1 - x) / 2) = Real.cos (π * x / 2) := by
    rw [show π * (1 - x) / 2 = π / 2 - π * x / 2 by ring, Real.sin_pi_div_two_sub]
  rw [h1]
  field_simp

/-- `∫₀^R g(tⁿ) dt = n⁻¹ ∫₀^{Rⁿ} u^{1/n - 1} g(u) du`. -/
theorem integral_comp_pow {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 0 < R) (g : ℝ → ℝ) :
    ∫ t in (0 : ℝ)..R, g (t ^ n) =
      (n : ℝ)⁻¹ * ∫ u in (0 : ℝ)..R ^ n, u ^ ((1 : ℝ) / n - 1) * g u := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hf' : ∀ t ∈ Ioo (0 : ℝ) R, HasDerivWithinAt (fun t : ℝ => t ^ n)
      ((n : ℝ) * t ^ (n - 1)) (Ioo 0 R) t := fun t _ =>
    (hasDerivAt_pow n t).hasDerivWithinAt
  have hinj : InjOn (fun t : ℝ => t ^ n) (Ioo 0 R) := fun a ha b hb h =>
    (pow_left_inj₀ ha.1.le hb.1.le hn.ne').mp h
  have himg : (fun t : ℝ => t ^ n) '' Ioo 0 R = Ioo 0 (R ^ n) := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨pow_pos ht.1 n, pow_lt_pow_left₀ ht.2 ht.1.le hn.ne'⟩
    · rintro ⟨hu0, huR⟩
      refine ⟨u ^ ((1 : ℝ) / n), ⟨Real.rpow_pos_of_pos hu0 _, ?_⟩, ?_⟩
      · have := Real.rpow_lt_rpow hu0.le huR (by positivity : (0 : ℝ) < 1 / n)
        rwa [← Real.rpow_natCast, ← Real.rpow_mul hR.le, mul_one_div_cancel hn'.ne',
          Real.rpow_one] at this
      · simp only
        rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le, one_div_mul_cancel hn'.ne',
          Real.rpow_one]
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hf' hinj
    (fun u => u ^ ((1 : ℝ) / n - 1) * g u)
  rw [himg] at h
  rw [intervalIntegral.integral_of_le hR.le, intervalIntegral.integral_of_le (by positivity),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo, h,
    ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have ht0 : 0 < t := ht.1
  simp only [smul_eq_mul]
  rw [abs_of_pos (by positivity), ← Real.rpow_natCast t n, ← Real.rpow_mul ht0.le,
    show (n : ℝ) * (1 / n - 1) = 1 - n by field_simp]
  rw [Real.rpow_sub ht0, Real.rpow_one, Real.rpow_natCast]
  have hpow : t ^ n = t * t ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hpow]
  have : t ^ (n - 1) ≠ 0 := by positivity
  field_simp

/-- The generalized Fresnel integrals reduce to `Gamma_cos`, `Gamma_sin` by `u = tⁿ`. -/
theorem tendsto_integral_comp_pow {n : ℕ} (hn : 2 ≤ n) {g : ℝ → ℝ} {L : ℝ}
    (hg : Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R, t ^ ((1 : ℝ) / n - 1) * g t) atTop (𝓝 L)) :
    Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R, g (t ^ n)) atTop (𝓝 ((n : ℝ)⁻¹ * L)) := by
  have hn0 : 0 < n := by omega
  refine ((hg.comp (tendsto_pow_atTop hn0.ne')).const_mul (n : ℝ)⁻¹).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  rw [integral_comp_pow hn0 hR g]
  rfl

/-- The generalized Fresnel cosine integral. The integral converges only conditionally at infinity,
so it is stated as the limit of integrals over `(0, R)`; Lean's integral over `(0, ∞)` would be
`0`. -/
@[dlmf 5.9.E8]
theorem Gamma_cos_pow (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun R : ℝ => ∫ t : ℝ in (0 : ℝ)..R, Real.cos (t ^ n)) atTop
      (𝓝 (Real.Gamma (1 + 1 / n) * Real.cos (π / (2 * n)))) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < 1 / n := by positivity
  have hx1 : (1 : ℝ) / n < 1 := by rw [div_lt_one (by linarith)]; linarith
  convert tendsto_integral_comp_pow hn (Gamma_cos hx0 hx1) using 2
  rw [add_comm, Real.Gamma_add_one hx0.ne', show π * (1 / n) / 2 = π / (2 * n) by ring]
  field_simp

/-- The generalized Fresnel sine integral. The integral converges only conditionally at infinity, so
it is stated as the limit of integrals over `(0, R)`; Lean's integral over `(0, ∞)` would be
`0`. -/
@[dlmf 5.9.E9]
theorem Gamma_sin_pow (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun R : ℝ => ∫ t : ℝ in (0 : ℝ)..R, Real.sin (t ^ n)) atTop
      (𝓝 (Real.Gamma (1 + 1 / n) * Real.sin (π / (2 * n)))) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < 1 / n := by positivity
  have hx1 : (1 : ℝ) / n < 1 := by rw [div_lt_one (by linarith)]; linarith
  convert tendsto_integral_comp_pow hn (Gamma_sin (by linarith) hx1) using 2
  -- `π/(2 Γ(1-x) cos(πx/2)) = Γ(x) sin(πx/2)` by reflection
  have hrefl := Real.Gamma_mul_Gamma_one_sub (1 / n)
  have hs : 0 < Real.sin (π * (1 / n) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hc : 0 < Real.cos (π * (1 / n) / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  have hG := Real.Gamma_pos_of_pos (by linarith : 0 < 1 - 1 / (n : ℝ))
  have hG' := Real.Gamma_pos_of_pos hx0
  have hdbl : Real.sin (π * (1 / n)) = 2 * Real.sin (π * (1 / n) / 2) *
      Real.cos (π * (1 / n) / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  rw [add_comm, Real.Gamma_add_one hx0.ne', show π / (2 * n) = π * (1 / n) / 2 by ring]
  set S := Real.sin (π * (1 / n) / 2)
  set C := Real.cos (π * (1 / n) / 2)
  have hΓx : Real.Gamma (1 / n) = π / (2 * S * C) / Real.Gamma (1 - 1 / n) := by
    rw [eq_div_iff hG.ne', hrefl, hdbl]
  rw [hΓx]
  field_simp

end Oscillatory

section DigammaIntegrals

open Set

/-- `∫₀¹ (tⁿ - t^{n+x-1}) dt = 1/(n+1) - 1/(n+x)`. -/
theorem integral_pow_sub_rpow {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ∫ t in Ioo (0 : ℝ) 1, (t ^ n - t ^ ((n : ℝ) + x - 1)) = Real.digammaSeriesTerm x n := by
  have h1 : (-1 : ℝ) < (n : ℝ) + x - 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_sub (intervalIntegral.intervalIntegrable_pow _)
      (intervalIntegral.intervalIntegrable_rpow' h1), integral_pow,
    integral_rpow (Or.inl h1), Real.digammaSeriesTerm]
  rw [zero_pow (Nat.succ_ne_zero n), Real.one_rpow,
    Real.zero_rpow (by linarith : (n : ℝ) + x - 1 + 1 ≠ 0), one_pow,
    show (n : ℝ) + x - 1 + 1 = x + n by ring]
  have : (x + n : ℝ) ≠ 0 := by positivity
  field_simp
  ring


/-- `tⁿ - t^{n+x-1} = tⁿ (1 - t^{x-1})` for `t > 0`. -/
theorem pow_sub_rpow_eq {x t : ℝ} (ht : 0 < t) (n : ℕ) :
    t ^ n - t ^ ((n : ℝ) + x - 1) = t ^ n * (1 - t ^ (x - 1)) := by
  rw [show (n : ℝ) + x - 1 = n + (x - 1) by ring, Real.rpow_add ht, Real.rpow_natCast]; ring

/-- `ψ(x) + γ = ∫₀¹ (1 - t^{x-1})/(1 - t) dt`, from the digamma series. -/
theorem digamma_add_euler_Ioo {x : ℝ} (hx : 0 < x) :
    Real.digamma x + Real.eulerMascheroniConstant =
      ∫ t in Ioo (0 : ℝ) 1, (1 - t ^ (x - 1)) / (1 - t) := by
  set F : ℕ → ℝ → ℝ := fun n t => t ^ n - t ^ ((n : ℝ) + x - 1) with hF
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioo (0 : ℝ) 1)) := by
    intro n
    have h1 : (-1 : ℝ) < (n : ℝ) + x - 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have := ((intervalIntegral.intervalIntegrable_pow (μ := volume) (a := 0) (b := 1) n).sub
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) h1))
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
    exact this.mono_set Ioo_subset_Ioc_self
  -- the terms do not change sign on `(0, 1)`
  have hsign : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ n, ∀ t ∈ Ioo (0 : ℝ) 1, ‖F n t‖ = ε * F n t := by
    by_cases hx1 : 1 ≤ x
    · refine ⟨1, Or.inl rfl, fun n t ht => ?_⟩
      have h := Real.rpow_le_one ht.1.le ht.2.le (by linarith : (0 : ℝ) ≤ x - 1)
      simp only [hF, pow_sub_rpow_eq ht.1, one_mul]
      rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg ht.1.le _) (by linarith))]
    · refine ⟨-1, Or.inr rfl, fun n t ht => ?_⟩
      have h := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht.1 ht.2.le
        (by linarith : x - 1 ≤ 0)
      simp only [hF, pow_sub_rpow_eq ht.1]
      rw [Real.norm_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg ht.1.le _)
        (by linarith))]
      ring
  obtain ⟨ε, hε, hεF⟩ := hsign
  have hnorm : ∀ n, ∫ t in Ioo (0 : ℝ) 1, ‖F n t‖ = ε * Real.digammaSeriesTerm x n := by
    intro n
    rw [setIntegral_congr_fun measurableSet_Ioo (hεF n), MeasureTheory.integral_const_mul,
      integral_pow_sub_rpow hx]
  have hsum : Summable fun n => ∫ t in Ioo (0 : ℝ) 1, ‖F n t‖ := by
    simp_rw [hnorm]
    exact (Real.summable_digammaSeriesTerm hx).mul_left ε
  have key := integral_tsum_of_summable_integral_norm hint hsum
  simp_rw [hF, integral_pow_sub_rpow hx] at key
  rw [Real.digamma_eq_tsum hx, neg_add_cancel_comm, key]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  simp only [pow_sub_rpow_eq ht.1]
  rw [tsum_mul_right, tsum_geometric_of_lt_one ht.1.le ht.2]
  field_simp


/-- `∫₀^∞ (e^{-(n+1)t} - e^{-(n+x)t}) dt = 1/(n+1) - 1/(n+x)`. -/
theorem integral_exp_sub_exp {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ∫ t in Ioi (0 : ℝ), (Real.exp (-((n : ℝ) + 1) * t) - Real.exp (-((n : ℝ) + x) * t)) =
      Real.digammaSeriesTerm x n := by
  have h1 : -((n : ℝ) + 1) < 0 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h2 : -((n : ℝ) + x) < 0 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rw [integral_sub (integrableOn_exp_mul_Ioi h1 0) (integrableOn_exp_mul_Ioi h2 0),
    integral_exp_mul_Ioi h1, integral_exp_mul_Ioi h2, Real.digammaSeriesTerm]
  simp only [mul_zero, Real.exp_zero]
  have : (x + n : ℝ) ≠ 0 := by positivity
  have : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- Factorization of the exponential series term. -/
theorem exp_sub_exp_eq {x t : ℝ} (n : ℕ) :
    Real.exp (-((n : ℝ) + 1) * t) - Real.exp (-((n : ℝ) + x) * t) =
      Real.exp (-t) ^ n * (Real.exp (-t) - Real.exp (-x * t)) := by
  rw [← Real.exp_nat_mul, mul_sub, ← Real.exp_add, ← Real.exp_add]
  congr 2 <;> ring

/-- `ψ(x) + γ = ∫₀^∞ (e^{-t} - e^{-xt})/(1 - e^{-t}) dt`, from the digamma series. -/
theorem digamma_add_euler_Ioi {x : ℝ} (hx : 0 < x) :
    Real.digamma x + Real.eulerMascheroniConstant =
      ∫ t in Ioi (0 : ℝ), (Real.exp (-t) - Real.exp (-x * t)) / (1 - Real.exp (-t)) := by
  set F : ℕ → ℝ → ℝ := fun n t =>
    Real.exp (-((n : ℝ) + 1) * t) - Real.exp (-((n : ℝ) + x) * t) with hF
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioi (0 : ℝ))) := by
    intro n
    have h1 : -((n : ℝ) + 1) < 0 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h2 : -((n : ℝ) + x) < 0 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact (integrableOn_exp_mul_Ioi h1 0).sub (integrableOn_exp_mul_Ioi h2 0)
  have hsign : ∃ ε : ℝ, ∀ n, ∀ t ∈ Ioi (0 : ℝ), ‖F n t‖ = ε * F n t := by
    by_cases hx1 : 1 ≤ x
    · refine ⟨1, fun n t ht => ?_⟩
      have h : Real.exp (-x * t) ≤ Real.exp (-t) :=
        Real.exp_le_exp.mpr (by nlinarith [show (0 : ℝ) < t from ht])
      simp only [hF, exp_sub_exp_eq, one_mul]
      rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (Real.exp_pos _).le _) (by linarith))]
    · refine ⟨-1, fun n t ht => ?_⟩
      have h : Real.exp (-t) ≤ Real.exp (-x * t) :=
        Real.exp_le_exp.mpr (by nlinarith [show (0 : ℝ) < t from ht])
      simp only [hF, exp_sub_exp_eq]
      rw [Real.norm_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (Real.exp_pos _).le _)
        (by linarith))]
      ring
  obtain ⟨ε, hεF⟩ := hsign
  have hnorm : ∀ n, ∫ t in Ioi (0 : ℝ), ‖F n t‖ = ε * Real.digammaSeriesTerm x n := by
    intro n
    rw [setIntegral_congr_fun measurableSet_Ioi (hεF n), MeasureTheory.integral_const_mul,
      integral_exp_sub_exp hx]
  have hsum : Summable fun n => ∫ t in Ioi (0 : ℝ), ‖F n t‖ := by
    simp_rw [hnorm]
    exact (Real.summable_digammaSeriesTerm hx).mul_left ε
  have key := integral_tsum_of_summable_integral_norm hint hsum
  simp_rw [hF, integral_exp_sub_exp hx] at key
  rw [Real.digamma_eq_tsum hx, neg_add_cancel_comm, key]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [exp_sub_exp_eq]
  have he1 : Real.exp (-t) < 1 :=
    Real.exp_lt_one_iff.mpr (by simpa using (show (0 : ℝ) < t from ht))
  rw [tsum_mul_right, tsum_geometric_of_lt_one (Real.exp_pos _).le he1]
  field_simp


/-- The digamma function is monotone on `(0, ∞)`. -/
theorem digamma_le_digamma {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Real.digamma x ≤ Real.digamma y := by
  have hy : 0 < y := hx.trans_le hxy
  rw [Real.digamma_eq_tsum hx, Real.digamma_eq_tsum hy]
  refine add_le_add_right ((Real.summable_digammaSeriesTerm hx).tsum_le_tsum (fun n => ?_)
    (Real.summable_digammaSeriesTerm hy)) _
  simp only [Real.digammaSeriesTerm]
  have : 0 < x + n := by positivity
  gcongr

/-- `log x - 1/x ≤ ψ(x) ≤ log x`. -/
theorem digamma_le_log_and {x : ℝ} (hx : 0 < x) :
    Real.log x - 1 / x ≤ Real.digamma x ∧ Real.digamma x ≤ Real.log x := by
  -- mean value theorem for `log Γ` on `[x, x + 1]`
  have hcont : ContinuousOn (fun s => Real.log (Real.Gamma s)) (Icc x (x + 1)) := by
    intro s hs
    exact (Real.hasDerivAt_log_Gamma (hx.trans_le hs.1)).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hderiv⟩ := exists_hasDerivAt_eq_slope (fun s => Real.log (Real.Gamma s))
    Real.digamma (by linarith) hcont
    (fun s hs => Real.hasDerivAt_log_Gamma (hx.trans hs.1))
  have hslope : (Real.log (Real.Gamma (x + 1)) - Real.log (Real.Gamma x)) / (x + 1 - x) =
      Real.log x := by
    rw [Real.Gamma_add_one hx.ne', Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne']
    ring
  rw [hslope] at hderiv
  have h1 := digamma_le_digamma hx hc.1.le
  have h2 := digamma_le_digamma (hx.trans hc.1) hc.2.le
  rw [Real.digamma_add_one hx] at h2
  constructor
  · rw [one_div]; linarith
  · linarith


/-- `|e^{-t} - e^{-xt}| ≤ |x - 1| t e^{-min(1,x) t}` for `t ≥ 0`. -/
theorem abs_exp_neg_sub_exp_neg_le {x t : ℝ} (ht : 0 ≤ t) :
    |Real.exp (-t) - Real.exp (-x * t)| ≤ |x - 1| * t * Real.exp (-min 1 x * t) := by
  have key : ∀ a b : ℝ, a ≤ b → 0 ≤ Real.exp (-a * t) - Real.exp (-b * t) ∧
      Real.exp (-a * t) - Real.exp (-b * t) ≤ (b - a) * t * Real.exp (-a * t) := by
    intro a b hab
    have h1 : Real.exp (-b * t) = Real.exp (-a * t) * Real.exp (-((b - a) * t)) := by
      rw [← Real.exp_add]; ring_nf
    have h2 := Real.add_one_le_exp (-((b - a) * t))
    have h3 : Real.exp (-((b - a) * t)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    have he := Real.exp_pos (-a * t)
    rw [h1]
    constructor <;> nlinarith
  rcases le_total 1 x with h | h
  · obtain ⟨k0, k1⟩ := key 1 x h
    rw [min_eq_left h]
    simp only [neg_mul, one_mul] at k0 k1 ⊢
    rw [abs_of_nonneg k0, abs_of_nonneg (show (0 : ℝ) ≤ x - 1 by linarith)]
    exact k1
  · obtain ⟨k0, k1⟩ := key x 1 h
    rw [min_eq_right h]
    simp only [neg_mul, one_mul] at k0 k1 ⊢
    rw [abs_of_nonpos (show Real.exp (-t) - Real.exp (-(x * t)) ≤ 0 by linarith),
      abs_of_nonpos (show x - 1 ≤ 0 by linarith)]
    linarith

/-- Integrability of the Frullani integrand `(e^{-t} - e^{-xt})/t`. -/
theorem integrableOn_exp_neg_sub_exp_neg_div {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => t⁻¹ * (Real.exp (-t) - Real.exp (-x * t))) (Ioi 0) := by
  have hm : -min 1 x < 0 := by simp [hx]
  refine Integrable.mono' ((integrableOn_exp_mul_Ioi hm 0).const_mul |x - 1|) ?_ ?_
  · exact (ContinuousOn.mul (continuousOn_inv₀.mono fun t ht => (ne_of_gt ht))
      (by fun_prop)).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht' : (0 : ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos ht']
    have := abs_exp_neg_sub_exp_neg_le (x := x) ht'.le
    rw [inv_mul_le_iff₀ ht']
    nlinarith

/-- Frullani: `∫₀^∞ (e^{-t} - e^{-xt})/t dt = log x`. -/
theorem integral_exp_neg_sub_exp_neg_div {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), t⁻¹ * (Real.exp (-t) - Real.exp (-x * t)) = Real.log x := by
  have hc : Continuous fun t : ℝ => Real.exp (-t) := by fun_prop
  have hloc : LocallyIntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) :=
    hc.locallyIntegrable.locallyIntegrableOn _
  have hL : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝[>] 0) (𝓝 1) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hint : IntegrableOn (fun t : ℝ => t⁻¹ • (Real.exp (-(1 * t)) - Real.exp (-(x * t))))
      (Ioi 0) := by
    simpa [neg_mul, smul_eq_mul] using integrableOn_exp_neg_sub_exp_neg_div hx
  have h := Frullani.integral_Ioi_eq hloc one_pos hx hL Real.tendsto_exp_neg_atTop_nhds_zero hint
  simpa [neg_mul, smul_eq_mul] using h


/-- The Binet kernel `1/(1 - e^{-t}) - 1/t`. -/
def binetKernel (t : ℝ) : ℝ := 1 / (1 - Real.exp (-t)) - 1 / t

/-- `0 ≤ 1/(1 - e^{-t}) - 1/t ≤ 1` for `t > 0`. -/
theorem binetKernel_mem_Icc {t : ℝ} (ht : 0 < t) : binetKernel t ∈ Icc (0 : ℝ) 1 := by
  have he : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hpos : 0 < 1 - Real.exp (-t) := by linarith
  have h1 := Real.add_one_le_exp (-t)
  have h2 : t + 1 ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have h3 : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  have hep := Real.exp_pos (-t)
  unfold binetKernel
  constructor
  · rw [sub_nonneg, div_le_div_iff₀ ht hpos]; linarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hpos]
    have : 1 / t * (1 - Real.exp (-t)) = (1 - Real.exp (-t)) / t := by ring
    rw [add_mul, one_mul, this, ← sub_le_iff_le_add', le_div_iff₀ ht]
    nlinarith

/-- Integrability of `e^{-xt}` times the Binet kernel. -/
theorem integrableOn_exp_mul_binetKernel {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => Real.exp (-x * t) * binetKernel t) (Ioi 0) := by
  have hm : -x < 0 := by linarith
  refine Integrable.mono' (integrableOn_exp_mul_Ioi hm 0) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have h1 : 1 - Real.exp (-t) ≠ 0 := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -t < 0); linarith
    have h2 : t ≠ 0 := ht'.ne'
    unfold binetKernel
    exact (ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption)))
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    obtain ⟨h0, h1⟩ := binetKernel_mem_Icc ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg h0]
    nlinarith [Real.exp_pos (-x * t)]

/-- `J(x) = ∫₀^∞ e^{-xt} (1/(1 - e^{-t}) - 1/t) dt` lies in `[0, 1/x]`. -/
theorem integral_exp_mul_binetKernel_mem {x : ℝ} (hx : 0 < x) :
    0 ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * binetKernel t ∧
      ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * binetKernel t ≤ 1 / x := by
  have hm : -x < 0 := by linarith
  constructor
  · refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    exact mul_nonneg (Real.exp_pos _).le (binetKernel_mem_Icc ht).1
  · have hle : ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * binetKernel t ≤
        ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) := by
      refine setIntegral_mono_on (integrableOn_exp_mul_binetKernel hx)
        (integrableOn_exp_mul_Ioi hm 0) measurableSet_Ioi fun t ht => ?_
      have := (binetKernel_mem_Icc ht).2
      nlinarith [Real.exp_pos (-x * t)]
    rw [integral_exp_mul_Ioi hm] at hle
    simpa [neg_div, div_neg] using hle


/-- `ψ(x) + γ - log x = J(1) - J(x)`. -/
theorem digamma_add_euler_sub_log {x : ℝ} (hx : 0 < x) :
    Real.digamma x + Real.eulerMascheroniConstant - Real.log x =
      (∫ t in Ioi (0 : ℝ), Real.exp (-1 * t) * binetKernel t) -
        ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * binetKernel t := by
  rw [digamma_add_euler_Ioi hx, ← integral_exp_neg_sub_exp_neg_div hx,
    ← integral_sub (integrableOn_exp_mul_binetKernel one_pos) (integrableOn_exp_mul_binetKernel hx)]
  have heq : EqOn (fun t => (Real.exp (-t) - Real.exp (-x * t)) / (1 - Real.exp (-t)))
      (fun t => (Real.exp (-1 * t) * binetKernel t - Real.exp (-x * t) * binetKernel t) +
        t⁻¹ * (Real.exp (-t) - Real.exp (-x * t))) (Ioi 0) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have h1 : 1 - Real.exp (-t) ≠ 0 := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -t < 0); linarith
    simp only [binetKernel, neg_mul, one_mul]
    field_simp
    ring
  have hi1 : IntegrableOn (fun t => Real.exp (-1 * t) * binetKernel t -
      Real.exp (-x * t) * binetKernel t) (Ioi 0) :=
    (integrableOn_exp_mul_binetKernel one_pos).sub (integrableOn_exp_mul_binetKernel hx)
  rw [setIntegral_congr_fun measurableSet_Ioi heq,
    integral_add hi1 (integrableOn_exp_neg_sub_exp_neg_div hx)]
  ring

/-- Binet's formula for the digamma function, together with `J(1) = γ`. -/
theorem digamma_eq_log_sub {x : ℝ} (hx : 0 < x) :
    Real.digamma x = Real.log x - ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * binetKernel t := by
  set J : ℝ → ℝ := fun x => ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * binetKernel t with hJ
  -- `ψ(y) - log y + J(y)` is constant
  have hconst : ∀ y : ℝ, 0 < y →
      Real.digamma y - Real.log y + J y = J 1 - Real.eulerMascheroniConstant := by
    intro y hy
    have := digamma_add_euler_sub_log hy
    simp only [hJ]
    linarith
  have hlim : Tendsto (fun y : ℝ => Real.digamma y - Real.log y + J y) atTop (𝓝 0) := by
    have hinv : Tendsto (fun y : ℝ => 1 / y) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero
    have h1 : Tendsto (fun y : ℝ => Real.digamma y - Real.log y) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hinv.neg.trans (by simp))
        tendsto_const_nhds
        ?_ ?_
      · filter_upwards [eventually_gt_atTop 0] with y hy
        have := (digamma_le_log_and hy).1; linarith
      · filter_upwards [eventually_gt_atTop 0] with y hy
        have := (digamma_le_log_and hy).2; linarith
    have h2 : Tendsto J atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv ?_ ?_
      · filter_upwards [eventually_gt_atTop 0] with y hy
        exact (integral_exp_mul_binetKernel_mem hy).1
      · filter_upwards [eventually_gt_atTop 0] with y hy
        exact (integral_exp_mul_binetKernel_mem hy).2
    simpa using h1.add h2
  have hc : J 1 - Real.eulerMascheroniConstant = 0 := by
    refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hlim
    filter_upwards [eventually_gt_atTop 0] with y hy
    exact (hconst y hy).symm
  have := hconst x hx
  simp only [hJ] at this hc ⊢
  linarith

/-- `J(1) = ∫₀^∞ e^{-t} (1/(1 - e^{-t}) - 1/t) dt = γ`. -/
theorem integral_exp_mul_binetKernel_one :
    ∫ t in Ioi (0 : ℝ), Real.exp (-1 * t) * binetKernel t = Real.eulerMascheroniConstant := by
  have := digamma_eq_log_sub one_pos
  rw [Real.digamma_one, Real.log_one] at this
  linarith

/-- Integrability of `(e^{-t} - e^{-xt})/(1 - e^{-t})` on `(0, ∞)`. -/
theorem integrableOn_digamma_add_euler {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => (Real.exp (-t) - Real.exp (-x * t)) / (1 - Real.exp (-t))) (Ioi 0) := by
  have hi := ((integrableOn_exp_mul_binetKernel one_pos).sub
    (integrableOn_exp_mul_binetKernel hx)).add (integrableOn_exp_neg_sub_exp_neg_div hx)
  refine IntegrableOn.congr_fun hi (fun t ht => ?_) measurableSet_Ioi
  have ht' : (0 : ℝ) < t := ht
  have h1 : 1 - Real.exp (-t) ≠ 0 := by
    have := Real.exp_lt_one_iff.mpr (by linarith : -t < 0); linarith
  simp only [Pi.add_apply, Pi.sub_apply, binetKernel, neg_mul, one_mul]
  field_simp
  ring

end DigammaIntegrals

section Binet

/-! ### Binet's formulas for `log Γ`

We follow Temme, *Special Functions*, §3.4 and §3.6: Binet's formula (3.12) for `ψ` is
`digamma_eq_log_sub`; integrating it gives (3.20), and the constant of integration is fixed
by Stirling's formula along the integers (Temme uses the duplication formula instead). -/

open Set

/-- Binet's function `β(t) = 1/(eᵗ - 1) - 1/t + 1/2` (Temme (3.12)). -/
def binetBeta (t : ℝ) : ℝ := 1 / (Real.exp t - 1) - 1 / t + 1 / 2

/-- `e^t - 1 > 0` for `t > 0`. -/
theorem exp_sub_one_pos {t : ℝ} (ht : 0 < t) : 0 < Real.exp t - 1 := by
  have := Real.add_one_lt_exp ht.ne'; linarith

/-- `1/(1 - e^(-t)) - 1/t = β(t) + 1/2`, with `β(t) = 1/(e^t - 1) - 1/t + 1/2`. -/
theorem binetKernel_eq_binetBeta {t : ℝ} (ht : 0 < t) : binetKernel t = binetBeta t + 1 / 2 := by
  have h1 := (exp_sub_one_pos ht).ne'
  have h0 : Real.exp t ≠ 0 := Real.exp_ne_zero t
  have h2 : 1 - (Real.exp t)⁻¹ = (Real.exp t - 1) / Real.exp t := by field_simp
  unfold binetKernel binetBeta
  rw [Real.exp_neg, h2]
  field_simp
  ring

/-- `β(t) ≥ 0` for `t > 0`, i.e. `eᵗ (t - 2) + t + 2 ≥ 0`. -/
theorem binetBeta_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ binetBeta t := by
  set g : ℝ → ℝ := fun s => Real.exp s * (s - 2) + s + 2 with hg
  have hd : ∀ s, HasDerivAt g (Real.exp s * (s - 1) + 1) s := by
    intro s
    have := (((Real.hasDerivAt_exp s).mul ((hasDerivAt_id s).sub_const 2)).add
      (hasDerivAt_id s)).add_const 2
    exact this.congr_deriv (by deriv_simp)
  have hmono : MonotoneOn g (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun s _ => (hd s).continuousAt.continuousWithinAt)
      (fun s _ => (hd s).differentiableAt.differentiableWithinAt) fun s _ => ?_
    rw [(hd s).deriv]
    have h1 := Real.add_one_le_exp (-s)
    have h2 : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos s]
  have hgt : g 0 ≤ g t := hmono self_mem_Ici ht.le ht.le
  have hg0 : g 0 = 0 := by simp [hg]
  have hE := exp_sub_one_pos ht
  have heq : binetBeta t = g t / (2 * t * (Real.exp t - 1)) := by
    simp only [binetBeta, hg]
    field_simp
    ring
  rw [heq]
  exact div_nonneg (hg0 ▸ hgt) (by positivity)

/-- `β(t) ≤ t/12` for `t > 0`: the Padé bound `eᵗ (t² - 6t + 12) ≥ t² + 6t + 12`. -/
theorem binetBeta_le {t : ℝ} (ht : 0 < t) : binetBeta t ≤ t / 12 := by
  have hE := exp_sub_one_pos ht
  have hq : 0 < t ^ 2 - 6 * t + 12 := by nlinarith [sq_nonneg (t - 3)]
  have hP := Real.sum_le_exp_of_nonneg ht.le 6
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hP
  norm_num at hP
  have h5 : 0 ≤ t ^ 5 * (t ^ 2 - t + 2) := by
    have : 0 < t ^ 2 - t + 2 := by nlinarith [sq_nonneg (t - 1 / 2)]
    positivity
  have key : 0 ≤ Real.exp t * (t ^ 2 - 6 * t + 12) - (t ^ 2 + 6 * t + 12) := by
    nlinarith [mul_le_mul_of_nonneg_right hP hq.le]
  have heq : t / 12 - binetBeta t =
      (Real.exp t * (t ^ 2 - 6 * t + 12) - (t ^ 2 + 6 * t + 12)) / (12 * t * (Real.exp t - 1)) := by
    unfold binetBeta
    field_simp
    ring
  have : 0 ≤ t / 12 - binetBeta t := by rw [heq]; positivity
  linarith

/-- `β(t) ≤ 1/2` for `t > 0`. -/
theorem binetBeta_le_half {t : ℝ} (ht : 0 < t) : binetBeta t ≤ 1 / 2 := by
  have := (binetKernel_mem_Icc ht).2
  rw [binetKernel_eq_binetBeta ht] at this
  linarith

/-- `β(t) = 1/(e^t - 1) - 1/t + 1/2` is continuous on `(0, ∞)`. -/
theorem continuousOn_binetBeta : ContinuousOn binetBeta (Ioi 0) := by
  intro t ht
  have h1 := (exp_sub_one_pos ht).ne'
  have h2 : t ≠ 0 := (ne_of_gt ht)
  unfold binetBeta
  exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))

/-- Integrability of `e^{-xt} β(t)`. -/
theorem integrableOn_exp_mul_binetBeta {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => Real.exp (-x * t) * binetBeta t) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_exp_mul_Ioi (by linarith : -x < 0) 0).const_mul (1 / 2))
    ?_ ?_
  · exact ((by fun_prop : Continuous fun t => Real.exp (-x * t)).continuousOn.mul
      continuousOn_binetBeta).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (binetBeta_nonneg ht))]
    nlinarith [Real.exp_pos (-x * t), binetBeta_le_half ht]

/-- Integrability of `e^{-xt} β(t)/t`. -/
theorem integrableOn_exp_mul_binetBeta_div {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => Real.exp (-x * t) * binetBeta t / t) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_exp_mul_Ioi (by linarith : -x < 0) 0).const_mul (1 / 12))
    ?_ ?_
  · refine (((by fun_prop : Continuous fun t => Real.exp (-x * t)).continuousOn.mul
      continuousOn_binetBeta).div continuousOn_id fun t ht => ?_).aestronglyMeasurable
      measurableSet_Ioi
    exact (ne_of_gt ht)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht' : (0 : ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg (Real.exp_pos _).le
      (binetBeta_nonneg ht')) ht'.le), div_le_iff₀ ht']
    nlinarith [Real.exp_pos (-x * t), binetBeta_le ht']

/-- Binet's integral `Φ(x) = ∫₀^∞ e^{-xt} β(t)/t dt` (Temme (3.27)). -/
def binetIntegral (x : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * binetBeta t / t

/-- `0 ≤ Φ(x) ≤ 1/(12x)`. -/
theorem binetIntegral_mem {x : ℝ} (hx : 0 < x) :
    0 ≤ binetIntegral x ∧ binetIntegral x ≤ 1 / (12 * x) := by
  have hm : -x < 0 := by linarith
  constructor
  · refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le (binetBeta_nonneg ht)) (le_of_lt ht)
  · have hle : binetIntegral x ≤ ∫ t in Ioi (0 : ℝ), 1 / 12 * Real.exp (-x * t) := by
      refine setIntegral_mono_on (integrableOn_exp_mul_binetBeta_div hx)
        ((integrableOn_exp_mul_Ioi hm 0).const_mul _) measurableSet_Ioi fun t ht => ?_
      have ht' : (0 : ℝ) < t := ht
      rw [div_le_iff₀ ht']
      nlinarith [Real.exp_pos (-x * t), binetBeta_le ht']
    rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi hm] at hle
    convert hle using 1
    simp only [mul_zero, Real.exp_zero]
    field_simp

/-- `Φ'(x) = -∫₀^∞ e^{-xt} β(t) dt`. -/
theorem hasDerivAt_binetIntegral {x : ℝ} (hx : 0 < x) :
    HasDerivAt binetIntegral (∫ t in Ioi (0 : ℝ), -(Real.exp (-x * t) * binetBeta t)) x := by
  set δ := x / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hball : Metric.ball x δ ∈ 𝓝 x := Metric.ball_mem_nhds _ hδ0
  have hre : ∀ y ∈ Metric.ball x δ, δ < y := by
    intro y hy
    rw [Metric.mem_ball, Real.dist_eq] at hy
    have := (abs_lt.mp hy).1
    linarith
  have hmeas (y : ℝ) : AEStronglyMeasurable (fun t => Real.exp (-y * t) * binetBeta t / t)
      (volume.restrict (Ioi 0)) :=
    (((by fun_prop : Continuous fun t => Real.exp (-y * t)).continuousOn.mul
      continuousOn_binetBeta).div continuousOn_id fun t ht => (ne_of_gt ht)).aestronglyMeasurable
      measurableSet_Ioi
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun y t => Real.exp (-y * t) * binetBeta t / t)
    (F' := fun y t => -(Real.exp (-y * t) * binetBeta t))
    (bound := fun t => 1 / 2 * Real.exp (-δ * t))
    hball (Eventually.of_forall hmeas) (integrableOn_exp_mul_binetBeta_div hx)
    (integrableOn_exp_mul_binetBeta hx).neg.aestronglyMeasurable ?_
    ((integrableOn_exp_mul_Ioi (by linarith : -δ < 0) 0).const_mul _) ?_
  · exact h.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht y hy
    have ht' : (0 : ℝ) < t := ht
    have hexp : Real.exp (-y * t) ≤ Real.exp (-δ * t) :=
      Real.exp_le_exp.mpr (by nlinarith [hre y hy])
    rw [norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (binetBeta_nonneg ht'))]
    nlinarith [Real.exp_pos (-y * t), binetBeta_le_half ht', binetBeta_nonneg ht']
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht y _
    have ht' : (0 : ℝ) < t := ht
    have ht0 : t ≠ 0 := ht'.ne'
    have h := (((hasDerivAt_id y).neg.mul_const t).exp.mul_const (binetBeta t)).div_const t
    exact h.congr_deriv (by deriv_simp)

/-- `ψ(x) = log x - 1/(2x) - ∫₀^∞ e^{-xt} β(t) dt` (Temme (3.12)). -/
theorem digamma_eq_log_sub_binetBeta {x : ℝ} (hx : 0 < x) :
    Real.digamma x = Real.log x - 1 / (2 * x) -
      ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * binetBeta t := by
  have hm : -x < 0 := by linarith
  have hsplit : ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * binetKernel t =
      (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * binetBeta t) +
        ∫ t in Ioi (0 : ℝ), 1 / 2 * Real.exp (-x * t) := by
    rw [← integral_add (integrableOn_exp_mul_binetBeta hx)
      ((integrableOn_exp_mul_Ioi hm 0).const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [binetKernel_eq_binetBeta ht]
    ring
  rw [digamma_eq_log_sub hx, hsplit, MeasureTheory.integral_const_mul,
    integral_exp_mul_Ioi hm]
  simp only [mul_zero, Real.exp_zero]
  field_simp
  ring

/-- A function with zero derivative on `(0, ∞)` is constant there. -/
theorem eq_of_hasDerivAt_zero_Ioi {G : ℝ → ℝ} (hG : ∀ y, 0 < y → HasDerivAt G 0 y)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : G a = G b := by
  have key : ∀ a b : ℝ, 0 < a → a < b → G a = G b := by
    intro a b ha hab
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope G (fun _ => (0 : ℝ)) hab
      (fun y hy => (hG y (ha.trans_le hy.1)).continuousAt.continuousWithinAt)
      (fun y hy => hG y (ha.trans hy.1))
    have hne : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
    rw [eq_div_iff hne, zero_mul] at hslope
    linarith
  rcases lt_trichotomy a b with h | h | h
  · exact key a b ha h
  · rw [h]
  · exact (key b a hb h).symm

/-- DLMF 5.9.10 (exponential form): `ln Γ(x) = (x - 1/2) ln x - x + (1/2) ln 2π + ∫₀^∞ e^(-xt)
(1/(e^t - 1) - 1/t + 1/2) dt/t` for `x > 0`. -/
@[dlmf 5.9.E10_2]
theorem log_Gamma_binet_exp {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma x) =
      (x - 1 / 2) * Real.log x - x + (1 / 2) * Real.log (2 * π) +
        ∫ t : ℝ in Set.Ioi 0,
          Real.exp (-x * t) * (1 / (Real.exp t - 1) - 1 / t + 1 / 2) / t := by
  set M : ℝ → ℝ := fun y => (y - 1 / 2) * Real.log y - y + (1 / 2) * Real.log (2 * π) with hM
  set G : ℝ → ℝ := fun y => Real.log (Real.Gamma y) - M y - binetIntegral y with hG
  have hG' : ∀ y, 0 < y → HasDerivAt G 0 y := by
    intro y hy
    have h2 : HasDerivAt M (Real.log y - 1 / (2 * y)) y := by
      have := ((((hasDerivAt_id y).sub_const (1 / 2)).mul (Real.hasDerivAt_log hy.ne')).sub
        (hasDerivAt_id y)).add_const ((1 / 2) * Real.log (2 * π))
      exact this.congr_deriv (by deriv_simp)
    have := ((Real.hasDerivAt_log_Gamma hy).sub h2).sub (hasDerivAt_binetIntegral hy)
    exact this.congr_deriv (by
      rw [MeasureTheory.integral_neg, digamma_eq_log_sub_binetBeta hy]; ring)
  have hlimG : Tendsto (fun n : ℕ => G n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => Real.log (Real.Gamma n / Real.stirlingGamma n)) atTop
        (𝓝 0) := by
      simpa using Real.tendsto_Gamma_nat_div_stirlingGamma.log one_ne_zero
    have hinv : Tendsto (fun y : ℝ => 1 / (12 * y)) atTop (𝓝 0) := by
      refine (tendsto_inv_atTop_zero.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 12))).congr fun y => ?_
      simp [one_div]
    have h2 : Tendsto binetIntegral atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv ?_ ?_
      · filter_upwards [eventually_gt_atTop 0] with y hy
        exact (binetIntegral_mem hy).1
      · filter_upwards [eventually_gt_atTop 0] with y hy
        exact (binetIntegral_mem hy).2
    have h3 := h1.sub (h2.comp tendsto_natCast_atTop_atTop)
    rw [sub_zero] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [Function.comp_apply, hG, hM]
    rw [Real.log_div (Real.Gamma_pos_of_pos hn').ne' (Real.stirlingGamma_ne_zero hn'),
      Real.log_stirlingGamma hn']
    ring
  have hGx : G x = 0 := by
    refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hlimG
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact eq_of_hasDerivAt_zero_Ioi hG' hx (by exact_mod_cast hn)
  simp only [hG, hM, binetIntegral, binetBeta] at hGx
  linarith

/-- `β(t) > 0` for `t > 0`. -/
theorem binetBeta_pos {t : ℝ} (ht : 0 < t) : 0 < binetBeta t := by
  set g : ℝ → ℝ := fun s => Real.exp s * (s - 2) + s + 2 with hg
  have hd : ∀ s, HasDerivAt g (Real.exp s * (s - 1) + 1) s := by
    intro s
    have := (((Real.hasDerivAt_exp s).mul ((hasDerivAt_id s).sub_const 2)).add
      (hasDerivAt_id s)).add_const 2
    exact this.congr_deriv (by deriv_simp)
  have hmono : StrictMonoOn g (Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0)
      (fun s _ => (hd s).continuousAt.continuousWithinAt) fun s hs => ?_
    rw [interior_Ici] at hs
    rw [(hd s).deriv]
    have h1 := Real.add_one_lt_exp (by linarith [mem_Ioi.mp hs] : -s ≠ 0)
    have h2 : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos s]
  have hgt : g 0 < g t := hmono self_mem_Ici ht.le ht
  have hg0 : g 0 = 0 := by simp [hg]
  have hE := exp_sub_one_pos ht
  have heq : binetBeta t = g t / (2 * t * (Real.exp t - 1)) := by
    simp only [binetBeta, hg]
    field_simp
    ring
  rw [heq]
  exact div_pos (hg0 ▸ hgt) (by positivity)

/-- `β(t) < t/12` for `t > 0`. -/
theorem binetBeta_lt {t : ℝ} (ht : 0 < t) : binetBeta t < t / 12 := by
  have hE := exp_sub_one_pos ht
  have hq : 0 < t ^ 2 - 6 * t + 12 := by nlinarith [sq_nonneg (t - 3)]
  have hP := Real.sum_le_exp_of_nonneg ht.le 6
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hP
  norm_num at hP
  have h5 : 0 < t ^ 5 * (t ^ 2 - t + 2) := by
    have : 0 < t ^ 2 - t + 2 := by nlinarith [sq_nonneg (t - 1 / 2)]
    positivity
  have key : 0 < Real.exp t * (t ^ 2 - 6 * t + 12) - (t ^ 2 + 6 * t + 12) := by
    nlinarith [mul_le_mul_of_nonneg_right hP hq.le]
  have heq : t / 12 - binetBeta t =
      (Real.exp t * (t ^ 2 - 6 * t + 12) - (t ^ 2 + 6 * t + 12)) / (12 * t * (Real.exp t - 1)) := by
    unfold binetBeta
    field_simp
    ring
  have : 0 < t / 12 - binetBeta t := by rw [heq]; positivity
  linarith

/-- `0 < Φ(x) < 1/(12x)` (Temme §3.6.1). -/
theorem binetIntegral_pos_lt {x : ℝ} (hx : 0 < x) :
    0 < binetIntegral x ∧ binetIntegral x < 1 / (12 * x) := by
  have hm : -x < 0 := by linarith
  have hsupp : ∀ f : ℝ → ℝ, (∀ t ∈ Ioi (0 : ℝ), 0 < f t) → IntegrableOn f (Ioi 0) →
      0 < ∫ t in Ioi (0 : ℝ), f t := by
    intro f hf hfi
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => (hf t ht).le))
      hfi]
    have : Function.support f ∩ Ioi 0 = Ioi 0 :=
      inter_eq_right.mpr fun t ht => (hf t ht).ne'
    rw [this, Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  constructor
  · exact hsupp _ (fun t ht => div_pos (mul_pos (Real.exp_pos _) (binetBeta_pos ht)) ht)
      (integrableOn_exp_mul_binetBeta_div hx)
  · have hI : ∫ t in Ioi (0 : ℝ), 1 / 12 * Real.exp (-x * t) = 1 / (12 * x) := by
      rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi hm]
      simp only [mul_zero, Real.exp_zero]
      field_simp
    have hdiff := hsupp (fun t => 1 / 12 * Real.exp (-x * t) - Real.exp (-x * t) * binetBeta t / t)
      (fun t ht => by
        have ht' : (0 : ℝ) < t := ht
        have := binetBeta_lt ht'
        have he := Real.exp_pos (-x * t)
        rw [sub_pos, div_lt_iff₀ ht']
        nlinarith)
      (((integrableOn_exp_mul_Ioi hm 0).const_mul _).sub (integrableOn_exp_mul_binetBeta_div hx))
    rw [integral_sub ((integrableOn_exp_mul_Ioi hm 0).const_mul _)
      (integrableOn_exp_mul_binetBeta_div hx), hI] at hdiff
    unfold binetIntegral
    linarith

/-- `ln Γ(x) = (x - 1/2) ln x - x + (1/2) ln 2π + Φ(x)` with Binet's integral `Φ(x) = ∫₀^∞ e^(-xt)
β(t)/t dt`. -/
theorem log_Gamma_eq_add_binetIntegral {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma x) =
      (x - 1 / 2) * Real.log x - x + (1 / 2) * Real.log (2 * π) + binetIntegral x := by
  rw [log_Gamma_binet_exp hx, binetIntegral]
  rfl

/-! #### Partial fractions and Laplace transforms

The remaining Binet formulas rest on the partial fraction expansion of `coth`, which turns
`β(s)` into `∑ₘ 2s/(s² + aₘ²)` with `aₘ = 2π(m+1)` (Temme (3.26) with `N = 0`), and on the
symmetric Laplace identities obtained by one application of Fubini's theorem. -/

/-- `cosh(s/2)/sinh(s/2) = 2β(s) + 2/s`. -/
theorem cosh_div_sinh_half {s : ℝ} (hs : 0 < s) :
    Real.cosh (s / 2) / Real.sinh (s / 2) = 2 * binetBeta s + 2 / s := by
  have hs2 : Real.exp s = Real.exp (s / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hE1 : Real.exp (s / 2) ^ 2 - 1 ≠ 0 := by rw [← hs2]; exact (exp_sub_one_pos hs).ne'
  have hE0 : Real.exp (s / 2) ≠ 0 := Real.exp_ne_zero _
  have hsh : Real.exp (s / 2) - (Real.exp (s / 2))⁻¹ ≠ 0 := by
    intro h
    apply hE1
    field_simp at h
    linarith
  rw [Real.cosh_eq, Real.sinh_eq, Real.exp_neg]
  unfold binetBeta
  rw [hs2]
  field_simp
  ring

/-- The partial fraction expansion `β(s) = ∑ₘ 2s/(s² + (2π(m+1))²)`, from Mathlib's
`cot_series_rep'` at the imaginary point `x = i s/(2π)`. -/
theorem hasSum_binetBeta {s : ℝ} (hs : 0 < s) :
    HasSum (fun m : ℕ => 2 * s / (s ^ 2 + (2 * π * (m + 1)) ^ 2)) (binetBeta s) := by
  set f : ℕ → ℝ := fun m => 2 * s / (s ^ 2 + (2 * π * (m + 1)) ^ 2) with hf
  set c : ℂ := -(2 * π) * I with hc
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hc0 : c ≠ 0 := by simp [hc, Real.pi_ne_zero]
  have hσ : 0 < s / (2 * π) := by positivity
  set x : ℂ := ((s / (2 * π) : ℝ) : ℂ) * I with hxdef
  have hxim : x.im = s / (2 * π) := by rw [hxdef, mul_I_im, ofReal_re]
  have hx : x ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    have := congrArg Complex.im hn
    rw [hxim, intCast_im] at this
    linarith
  have hterm : ∀ n : ℕ, cotTerm x n = c * (f n : ℂ) := by
    intro n
    have hprod : (x + (n + 1)) * (x - (n + 1)) =
        -(((s / (2 * π)) ^ 2 + ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) := by
      simp only [hxdef]
      push_cast
      linear_combination ((s : ℂ) / (2 * π)) ^ 2 * I_sq
    have hD : (0 : ℝ) < (s / (2 * π)) ^ 2 + ((n : ℝ) + 1) ^ 2 := by positivity
    have hD' : (0 : ℝ) < s ^ 2 + (2 * π * ((n : ℝ) + 1)) ^ 2 := by positivity
    rw [cotTerm_identity hx n, hprod]
    simp only [hf, hc, hxdef]
    have h1 : (((s / (2 * π)) ^ 2 + ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
    have h2 : ((s ^ 2 + (2 * π * ((n : ℝ) + 1)) ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hD'.ne'
    push_cast at h1 h2 ⊢
    field_simp
  have hcot : (π : ℂ) * Complex.cot (π * x) - 1 / x = c * (binetBeta s : ℂ) := by
    have hpx : (π : ℂ) * x = ((s / 2 : ℝ) : ℂ) * I := by
      rw [hxdef, ← mul_assoc, ← ofReal_mul, show π * (s / (2 * π)) = s / 2 by
        field_simp]
    have hsinh : Real.sinh (s / 2) ≠ 0 := (Real.sinh_pos_iff.mpr (by linarith)).ne'
    have hC : Real.cosh (s / 2) = (2 * binetBeta s + 2 / s) * Real.sinh (s / 2) := by
      rw [← cosh_div_sinh_half hs]; field_simp
    rw [hpx, Complex.cot_eq_cos_div_sin, Complex.cos_mul_I, Complex.sin_mul_I, ← ofReal_cosh,
      ← ofReal_sinh, hC, ofReal_mul]
    have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
    have hsh : (Real.sinh (s / 2) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hsinh
    generalize ((Real.sinh (s / 2) : ℝ) : ℂ) = S at hsh ⊢
    have hσ0 : ((s / (2 * π) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hσ.ne'
    rw [mul_comm S I, mul_div_mul_right _ _ hsh, hxdef, ← div_div, Complex.div_I,
      Complex.div_I, hc]
    push_cast
    field_simp
    ring
  have hsumC : Summable fun n => c * (f n : ℂ) := (summable_cotTerm hx).congr hterm
  have hsumR : Summable f := by
    have := hsumC.mul_left c⁻¹
    simp only [← mul_assoc, inv_mul_cancel₀ hc0, one_mul] at this
    exact Complex.summable_ofReal.mp this
  have h := cot_series_rep' hx
  rw [hcot] at h
  have hterm' : ∀ n : ℕ, 1 / (x - (n + 1)) + 1 / (x + (n + 1)) = c * (f n : ℂ) := hterm
  simp_rw [hterm'] at h
  rw [tsum_mul_left, ← Complex.ofReal_tsum] at h
  have h' : binetBeta s = ∑' n, f n := by exact_mod_cast mul_left_cancel₀ hc0 h
  rw [h']
  exact hsumR.hasSum

/-- `β(s)/s = ∑ₘ 2/(s² + (2π(m+1))²)`. -/
theorem hasSum_binetBeta_div {s : ℝ} (hs : 0 < s) :
    HasSum (fun m : ℕ => 2 / (s ^ 2 + (2 * π * (m + 1)) ^ 2)) (binetBeta s / s) := by
  convert (hasSum_binetBeta hs).div_const s using 1
  funext m
  field_simp

/-- `1/(e^{2πt} - 1) = ∑ₘ e^{-2π(m+1)t}`. -/
theorem hasSum_recip_exp_two_pi_sub_one {t : ℝ} (ht : 0 < t) :
    HasSum (fun m : ℕ => Real.exp (-(2 * π * (m + 1)) * t))
      (1 / (Real.exp (2 * π * t) - 1)) := by
  set q := Real.exp (-(2 * π * t)) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hterm : ∀ m : ℕ, Real.exp (-(2 * π * (m + 1)) * t) = q * q ^ m := by
    intro m
    rw [hq, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hval : 1 / (Real.exp (2 * π * t) - 1) = q * (1 - q)⁻¹ := by
    have h1 : Real.exp (2 * π * t) * q = 1 := by rw [hq, ← Real.exp_add]; simp
    have h2 : Real.exp (2 * π * t) - 1 ≠ 0 := (exp_sub_one_pos (by positivity)).ne'
    have h3 : 1 - q ≠ 0 := by linarith
    field_simp
    linear_combination -h1
  simp_rw [hterm, hval]
  exact (hasSum_geometric_of_lt_one hq0 hq1).mul_left q

/-- The Laplace transforms of `cos` and `sin`. -/
theorem integral_exp_mul_cos_sin {x t : ℝ} (hx : 0 < x) :
    ∫ s in Ioi (0 : ℝ), Real.exp (-x * s) * Real.cos (t * s) = x / (x ^ 2 + t ^ 2) ∧
      ∫ s in Ioi (0 : ℝ), Real.exp (-x * s) * Real.sin (t * s) = t / (x ^ 2 + t ^ 2) := by
  set a : ℂ := -x + t * I with ha
  have hare : a.re < 0 := by simp [ha]; linarith
  have hint := integrableOn_exp_mul_complex_Ioi hare 0
  have h := integral_exp_mul_complex_Ioi hare 0
  simp only [ofReal_zero, mul_zero, Complex.exp_zero] at h
  have ha0 : a ≠ 0 := fun h0 => by rw [h0, zero_re] at hare; exact lt_irrefl _ hare
  have hd : ((x ^ 2 + t ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < x ^ 2 + t ^ 2 := by positivity
    exact_mod_cast this.ne'
  have hval : -1 / a = ((x / (x ^ 2 + t ^ 2) : ℝ) : ℂ) + ((t / (x ^ 2 + t ^ 2) : ℝ) : ℂ) * I := by
    have hd' : (x : ℂ) ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hd
    have e : ((x / (x ^ 2 + t ^ 2) : ℝ) : ℂ) + ((t / (x ^ 2 + t ^ 2) : ℝ) : ℂ) * I =
        ((x : ℂ) + t * I) / ((x : ℂ) ^ 2 + (t : ℂ) ^ 2) := by
      push_cast; field_simp
    rw [e, div_eq_div_iff ha0 hd', ha]
    linear_combination (-(t : ℂ) ^ 2) * I_sq
  rw [hval] at h
  have hre : ∀ s : ℝ, RCLike.re (Complex.exp (a * s)) =
      Real.exp (-x * s) * Real.cos (t * s) := by
    intro s
    rw [RCLike.re_to_complex, Complex.exp_re]
    simp [ha]
  have him : ∀ s : ℝ, RCLike.im (Complex.exp (a * s)) =
      Real.exp (-x * s) * Real.sin (t * s) := by
    intro s
    rw [RCLike.im_to_complex, Complex.exp_im]
    simp [ha]
  constructor
  · have := integral_re hint
    simp_rw [hre] at this
    rw [this, h, RCLike.re_to_complex, add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero]
  · have := integral_im hint
    simp_rw [him] at this
    rw [this, h, RCLike.im_to_complex, add_im, ofReal_im, mul_I_im, ofReal_re, zero_add]

/-- Integrability on `(0, ∞)²` of `e^{-xs} e^{-at} g(st)` with `|g| ≤ 1`. -/
theorem integrable_exp_mul_exp_prod {x a : ℝ} (hx : 0 < x) (ha : 0 < a) {g : ℝ → ℝ}
    (hg : Continuous g) (hg1 : ∀ y, |g y| ≤ 1) :
    Integrable (Function.uncurry fun s t : ℝ => Real.exp (-x * s) * Real.exp (-a * t) * g (s * t))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hprod := (integrableOn_exp_mul_Ioi (by linarith : -x < 0) 0).mul_prod
    (integrableOn_exp_mul_Ioi (by linarith : -a < 0) 0)
  refine hprod.mono' ?_ (Eventually.of_forall fun p => ?_)
  · exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
      Real.exp (-x * p.1) * Real.exp (-a * p.2) * g (p.1 * p.2)).aestronglyMeasurable
  · obtain ⟨u, v⟩ := p
    simp only [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_mul, Real.abs_exp]
    have := hg1 (u * v)
    have h1 := Real.exp_pos (-x * u)
    have h2 := Real.exp_pos (-a * v)
    nlinarith [mul_pos h1 h2, abs_nonneg (g (u * v))]

/-- `a ∫₀^∞ e^{-xs}/(s² + a²) ds = x ∫₀^∞ e^{-at}/(t² + x²) dt`. -/
theorem integral_exp_div_sq_add_sq_symm {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    a * ∫ s in Ioi (0 : ℝ), Real.exp (-x * s) / (s ^ 2 + a ^ 2) =
      x * ∫ t in Ioi (0 : ℝ), Real.exp (-a * t) / (t ^ 2 + x ^ 2) := by
  have hswap := integral_integral_swap
    (integrable_exp_mul_exp_prod hx ha Real.continuous_cos fun y => Real.abs_cos_le_one y)
  have hL : ∀ s ∈ Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ),
      Real.exp (-x * s) * Real.exp (-a * t) * Real.cos (s * t) =
        a * (Real.exp (-x * s) / (s ^ 2 + a ^ 2)) := by
    intro s _
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => show Real.exp (-x * s) *
      Real.exp (-a * t) * Real.cos (s * t) = Real.exp (-x * s) * (Real.exp (-a * t) *
        Real.cos (s * t)) by ring), MeasureTheory.integral_const_mul,
      (integral_exp_mul_cos_sin (t := s) ha).1]
    field_simp
    ring
  have hR : ∀ t ∈ Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ),
      Real.exp (-x * s) * Real.exp (-a * t) * Real.cos (s * t) =
        x * (Real.exp (-a * t) / (t ^ 2 + x ^ 2)) := by
    intro t _
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => show Real.exp (-x * s) *
      Real.exp (-a * t) * Real.cos (s * t) = Real.exp (-a * t) * (Real.exp (-x * s) *
        Real.cos (t * s)) by rw [mul_comm s t]; ring), MeasureTheory.integral_const_mul,
      (integral_exp_mul_cos_sin (t := t) hx).1]
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hL, setIntegral_congr_fun measurableSet_Ioi hR,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hswap
  exact hswap

/-- `∫₀^∞ e^{-xs} s/(s² + a²) ds = ∫₀^∞ e^{-at} t/(t² + x²) dt`. -/
theorem integral_exp_mul_div_sq_add_sq_symm {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    ∫ s in Ioi (0 : ℝ), Real.exp (-x * s) * (s / (s ^ 2 + a ^ 2)) =
      ∫ t in Ioi (0 : ℝ), Real.exp (-a * t) * (t / (t ^ 2 + x ^ 2)) := by
  have hswap := integral_integral_swap
    (integrable_exp_mul_exp_prod hx ha Real.continuous_sin fun y => Real.abs_sin_le_one y)
  have hL : ∀ s ∈ Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ),
      Real.exp (-x * s) * Real.exp (-a * t) * Real.sin (s * t) =
        Real.exp (-x * s) * (s / (s ^ 2 + a ^ 2)) := by
    intro s _
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => show Real.exp (-x * s) *
      Real.exp (-a * t) * Real.sin (s * t) = Real.exp (-x * s) * (Real.exp (-a * t) *
        Real.sin (s * t)) by ring), MeasureTheory.integral_const_mul,
      (integral_exp_mul_cos_sin (t := s) ha).2]
    ring_nf
  have hR : ∀ t ∈ Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ),
      Real.exp (-x * s) * Real.exp (-a * t) * Real.sin (s * t) =
        Real.exp (-a * t) * (t / (t ^ 2 + x ^ 2)) := by
    intro t _
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => show Real.exp (-x * s) *
      Real.exp (-a * t) * Real.sin (s * t) = Real.exp (-a * t) * (Real.exp (-x * s) *
        Real.sin (t * s)) by rw [mul_comm s t]; ring), MeasureTheory.integral_const_mul,
      (integral_exp_mul_cos_sin (t := t) hx).2]
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi hL, setIntegral_congr_fun measurableSet_Ioi hR]
    at hswap
  exact hswap

/-- `e^(-xs)/(s² + a²)` is integrable on `(0, ∞)` for `x, a > 0`. -/
theorem integrableOn_exp_div_sq_add_sq {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    IntegrableOn (fun s => Real.exp (-x * s) / (s ^ 2 + a ^ 2)) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_exp_mul_Ioi (by linarith : -x < 0) 0).const_mul
    (1 / a ^ 2)) ?_ (Eventually.of_forall fun s => ?_)
  · exact (Continuous.div (by fun_prop) (by fun_prop) fun s => by positivity).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_div, Real.abs_exp, abs_of_pos (by positivity : 0 < s ^ 2 + a ^ 2),
      div_le_iff₀ (by positivity)]
    have := Real.exp_pos (-x * s)
    field_simp
    nlinarith [sq_nonneg s]

/-- `∫₀^∞ e^{-xs}/(s² + a²) ds ≤ 1/(a² x)`. -/
theorem integral_exp_div_sq_add_sq_le {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    ∫ s in Ioi (0 : ℝ), Real.exp (-x * s) / (s ^ 2 + a ^ 2) ≤ 1 / (a ^ 2 * x) := by
  have hm : -x < 0 := by linarith
  have hle : ∫ s in Ioi (0 : ℝ), Real.exp (-x * s) / (s ^ 2 + a ^ 2) ≤
      ∫ s in Ioi (0 : ℝ), 1 / a ^ 2 * Real.exp (-x * s) := by
    refine setIntegral_mono_on (integrableOn_exp_div_sq_add_sq hx ha)
      ((integrableOn_exp_mul_Ioi hm 0).const_mul _) measurableSet_Ioi fun s _ => ?_
    rw [div_le_iff₀ (by positivity)]
    have := Real.exp_pos (-x * s)
    field_simp
    nlinarith [sq_nonneg s]
  rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi hm] at hle
  convert hle using 1
  simp only [mul_zero, Real.exp_zero]
  field_simp

/-- `∫₀^∞ e^(-xs)/(s² + a²) ds ≥ 0`. -/
theorem integral_exp_div_sq_add_sq_nonneg {x a : ℝ} :
    0 ≤ ∫ s in Ioi (0 : ℝ), Real.exp (-x * s) / (s ^ 2 + a ^ 2) :=
  setIntegral_nonneg measurableSet_Ioi fun s _ => by positivity

/-- `∑ₘ 1/(aₘ² x)` is summable. -/
theorem summable_recip_sq_two_pi {x : ℝ} :
    Summable fun m : ℕ => 1 / ((2 * π * (m + 1)) ^ 2 * x) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  convert h.mul_left (1 / (4 * π ^ 2 * x)) using 1
  funext m
  push_cast
  field_simp
  ring

/-- `Φ(x) = ∑ₘ 2 ∫₀^∞ e^{-xs}/(s² + aₘ²) ds`. -/
theorem hasSum_binetIntegral {x : ℝ} (hx : 0 < x) :
    HasSum (fun m : ℕ => 2 * ∫ s in Ioi (0 : ℝ),
      Real.exp (-x * s) / (s ^ 2 + (2 * π * (m + 1)) ^ 2)) (binetIntegral x) := by
  set F : ℕ → ℝ → ℝ := fun m s => 2 * (Real.exp (-x * s) / (s ^ 2 + (2 * π * (m + 1)) ^ 2))
    with hF
  have ha : ∀ m : ℕ, 0 < 2 * π * (m + 1) := fun m => by positivity
  have hint : ∀ m, Integrable (F m) (volume.restrict (Ioi (0 : ℝ))) :=
    fun m => (integrableOn_exp_div_sq_add_sq hx (ha m)).const_mul 2
  have hnorm : ∀ m, ∫ s in Ioi (0 : ℝ), ‖F m s‖ = ∫ s in Ioi (0 : ℝ), F m s := fun m =>
    setIntegral_congr_fun measurableSet_Ioi fun s _ => Real.norm_of_nonneg (by positivity)
  have hsum : Summable fun m => ∫ s in Ioi (0 : ℝ), ‖F m s‖ := by
    simp_rw [hnorm, hF, MeasureTheory.integral_const_mul]
    refine Summable.of_nonneg_of_le (fun m => by
      have := integral_exp_div_sq_add_sq_nonneg (x := x) (a := 2 * π * (m + 1)); positivity)
      (fun m => by
        have := integral_exp_div_sq_add_sq_le hx (ha m)
        exact mul_le_mul_of_nonneg_left this zero_le_two)
      (summable_recip_sq_two_pi.mul_left 2)
  have key := integral_tsum_of_summable_integral_norm hint hsum
  have hsum' : Summable fun m => ∫ s in Ioi (0 : ℝ), F m s := hsum.congr hnorm
  simp_rw [hF, MeasureTheory.integral_const_mul] at hsum' key
  rw [show binetIntegral x = ∑' m : ℕ, 2 * ∫ s in Ioi (0 : ℝ),
      Real.exp (-x * s) / (s ^ 2 + (2 * π * (m + 1)) ^ 2) from ?_]
  · exact hsum'.hasSum
  rw [key, binetIntegral]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs' : (0 : ℝ) < s := hs
  rw [mul_div_assoc, ← (hasSum_binetBeta_div hs').tsum_eq, ← tsum_mul_left]
  congr 1
  funext m
  ring

/-- `∫₀^∞ arctan(t/x) e^{-at} dt = (x/a) ∫₀^∞ e^{-at}/(t² + x²) dt`, by parts. -/
theorem integral_arctan_mul_exp {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), Real.arctan (t / x) * Real.exp (-a * t) =
      x / a * ∫ t in Ioi (0 : ℝ), Real.exp (-a * t) / (t ^ 2 + x ^ 2) := by
  have hu : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t => Real.arctan (t / x))
      (x / (t ^ 2 + x ^ 2)) t := by
    intro t _
    have := (Real.hasDerivAt_arctan (t / x)).comp t ((hasDerivAt_id t).div_const x)
    have hx' : x ≠ 0 := hx.ne'
    exact this.congr_deriv (by deriv_simp)
  have hv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t => -Real.exp (-a * t) / a)
      (Real.exp (-a * t)) t := by
    intro t _
    have := (((hasDerivAt_id t).const_mul (-a)).exp.neg).div_const a
    have ha' : a ≠ 0 := ha.ne'
    exact this.congr_deriv (by deriv_simp)
  have hm : -a < 0 := by linarith
  have hbound : ∀ t, |Real.arctan (t / x)| ≤ π / 2 := fun t =>
    abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
  have huv' : IntegrableOn (fun t => Real.arctan (t / x) * Real.exp (-a * t)) (Ioi 0) := by
    refine Integrable.mono' ((integrableOn_exp_mul_Ioi hm 0).const_mul (π / 2)) ?_
      (Eventually.of_forall fun t => ?_)
    · exact (by fun_prop : Continuous fun t => Real.arctan (t / x) * Real.exp (-a * t))
        |>.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
      exact mul_le_mul_of_nonneg_right (hbound t) (Real.exp_pos _).le
  have hu'v : IntegrableOn (fun t => x / (t ^ 2 + x ^ 2) * (-Real.exp (-a * t) / a)) (Ioi 0) := by
    have := ((integrableOn_exp_div_sq_add_sq ha hx).const_mul (-(x / a)))
    refine IntegrableOn.congr_fun this (fun t _ => ?_) measurableSet_Ioi
    field_simp
  have hzero : Tendsto (fun t => Real.arctan (t / x) * (-Real.exp (-a * t) / a)) (𝓝[>] 0)
      (𝓝 0) := by
    have : Continuous fun t => Real.arctan (t / x) * (-Real.exp (-a * t) / a) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hinfty : Tendsto (fun t => Real.arctan (t / x) * (-Real.exp (-a * t) / a)) atTop
      (𝓝 0) := by
    have hexp : Tendsto (fun t => -Real.exp (-a * t) / a) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hm)).neg.div_const a
      simpa [Function.comp_def] using this
    refine (hexp.zero_mul_isBoundedUnder_le ?_).congr fun t => mul_comm _ _
    exact isBoundedUnder_of_eventually_le (a := π / 2) (Eventually.of_forall fun t => by
      simpa [Real.norm_eq_abs] using hbound t)
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v hzero hinfty
  rw [h, sub_self, zero_sub, ← MeasureTheory.integral_neg, ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  ring

/-- `∫₀^∞ arctan(t/x) e^{-at} dt = ∫₀^∞ e^{-xs}/(s² + a²) ds`. -/
theorem integral_arctan_mul_exp_eq {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), Real.arctan (t / x) * Real.exp (-a * t) =
      ∫ s in Ioi (0 : ℝ), Real.exp (-x * s) / (s ^ 2 + a ^ 2) := by
  rw [integral_arctan_mul_exp hx ha, div_mul_eq_mul_div, ← integral_exp_div_sq_add_sq_symm hx ha]
  field_simp

/-- DLMF 5.9.10, Binet's second formula: `ln Γ(x) = (x - 1/2) ln x - x + (1/2) ln 2π + 2 ∫₀^∞
arctan(t/x)/(e^(2πt) - 1) dt` for `x > 0`. -/
@[dlmf 5.9.E10]
theorem log_Gamma_binet_arctan {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma x) =
      (x - 1 / 2) * Real.log x - x + (1 / 2) * Real.log (2 * π) +
        2 * ∫ t : ℝ in Set.Ioi 0,
          Real.arctan (t / x) / (Real.exp (2 * π * t) - 1) := by
  rw [log_Gamma_eq_add_binetIntegral hx]
  congr 1
  set F : ℕ → ℝ → ℝ := fun m t => Real.arctan (t / x) * Real.exp (-(2 * π * (m + 1)) * t)
    with hF
  have ha : ∀ m : ℕ, 0 < 2 * π * (m + 1) := fun m => by positivity
  have hval : ∀ m, ∫ t in Ioi (0 : ℝ), F m t =
      ∫ s in Ioi (0 : ℝ), Real.exp (-x * s) / (s ^ 2 + (2 * π * (m + 1)) ^ 2) := fun m =>
    integral_arctan_mul_exp_eq hx (ha m)
  have hFnn : ∀ m, ∀ t ∈ Ioi (0 : ℝ), 0 ≤ F m t := fun m t ht =>
    mul_nonneg (Real.arctan_nonneg.mpr (div_nonneg (le_of_lt ht) hx.le)) (Real.exp_pos _).le
  have hint : ∀ m, Integrable (F m) (volume.restrict (Ioi (0 : ℝ))) := by
    intro m
    refine Integrable.mono' ((integrableOn_exp_mul_Ioi (by linarith [ha m] :
      -(2 * π * (m + 1)) < 0) 0).const_mul (π / 2)) ?_ (Eventually.of_forall fun t => ?_)
    · exact (by fun_prop : Continuous (F m)).aestronglyMeasurable
    · simp only [hF, Real.norm_eq_abs, abs_mul, Real.abs_exp]
      have h1 := Real.neg_pi_div_two_lt_arctan (t / x)
      exact mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith, (Real.arctan_lt_pi_div_two _).le⟩)
        (Real.exp_pos _).le
  have hnorm : ∀ m, ∫ t in Ioi (0 : ℝ), ‖F m t‖ = ∫ t in Ioi (0 : ℝ), F m t := fun m =>
    setIntegral_congr_fun measurableSet_Ioi fun t ht => Real.norm_of_nonneg (hFnn m t ht)
  have hS := hasSum_binetIntegral hx
  have hsum : Summable fun m => ∫ t in Ioi (0 : ℝ), ‖F m t‖ := by
    simp_rw [hnorm, hval]
    exact (hS.summable.mul_left (1 / 2)).congr fun m => by ring
  have key := integral_tsum_of_summable_integral_norm hint hsum
  rw [← hS.tsum_eq, ← MeasureTheory.integral_const_mul]
  simp_rw [hval] at key
  rw [tsum_mul_left, key, ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [hF]
  rw [tsum_mul_left, (hasSum_recip_exp_two_pi_sub_one ht).tsum_eq]
  ring

/-- DLMF 5.9.10 (logarithmic form): `ln Γ(x) = (x - 1/2) ln x - x + (1/2) ln 2π - (x/π) ∫₀^∞ ln(1 -
e^(-2πt))/(t² + x²) dt` for `x > 0`. -/
@[dlmf 5.9.E10_1]
theorem log_Gamma_binet_log {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma x) =
      (x - 1 / 2) * Real.log x - x + (1 / 2) * Real.log (2 * π) -
        x / π * ∫ t : ℝ in Set.Ioi 0,
          Real.log (1 - Real.exp (-2 * π * t)) / (t ^ 2 + x ^ 2) := by
  rw [log_Gamma_eq_add_binetIntegral hx]
  suffices h : binetIntegral x = x / π * ∫ t : ℝ in Set.Ioi 0,
      -(Real.log (1 - Real.exp (-2 * π * t)) / (t ^ 2 + x ^ 2)) by
    rw [h, MeasureTheory.integral_neg]; ring
  set F : ℕ → ℝ → ℝ := fun m t =>
    Real.exp (-(2 * π * (m + 1)) * t) / (t ^ 2 + x ^ 2) / (m + 1) with hF
  have ha : ∀ m : ℕ, 0 < 2 * π * (m + 1) := fun m => by positivity
  have hval : ∀ m, x / π * ∫ t in Ioi (0 : ℝ), F m t =
      2 * ∫ s in Ioi (0 : ℝ), Real.exp (-x * s) / (s ^ 2 + (2 * π * (m + 1)) ^ 2) := by
    intro m
    have h := integral_exp_div_sq_add_sq_symm hx (ha m)
    simp only [hF]
    rw [MeasureTheory.integral_div]
    set I1 := ∫ s in Ioi (0 : ℝ), Real.exp (-x * s) / (s ^ 2 + (2 * π * (m + 1)) ^ 2)
    set I2 := ∫ t in Ioi (0 : ℝ), Real.exp (-(2 * π * (m + 1)) * t) / (t ^ 2 + x ^ 2)
    have hπ := Real.pi_pos
    have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
    calc x / π * (I2 / (m + 1)) = (x * I2) / (π * (m + 1)) := by field_simp
      _ = (2 * π * (m + 1) * I1) / (π * (m + 1)) := by rw [h]
      _ = 2 * I1 := by field_simp
  have hint : ∀ m, Integrable (F m) (volume.restrict (Ioi (0 : ℝ))) := fun m =>
    (integrableOn_exp_div_sq_add_sq (ha m) hx).div_const _
  have hnorm : ∀ m, ∫ t in Ioi (0 : ℝ), ‖F m t‖ = ∫ t in Ioi (0 : ℝ), F m t := fun m =>
    setIntegral_congr_fun measurableSet_Ioi fun t _ => Real.norm_of_nonneg (by positivity)
  have hS := hasSum_binetIntegral hx
  have hsum : Summable fun m => ∫ t in Ioi (0 : ℝ), ‖F m t‖ := by
    simp_rw [hnorm]
    have : (fun m => ∫ t in Ioi (0 : ℝ), F m t) = fun m : ℕ => π / x * (2 *
        ∫ s in Ioi (0 : ℝ), Real.exp (-x * s) / (s ^ 2 + (2 * π * (m + 1)) ^ 2)) := by
      funext m
      rw [← hval m]
      field_simp
    rw [this]
    exact hS.summable.mul_left _
  have key := integral_tsum_of_summable_integral_norm hint hsum
  rw [← hS.tsum_eq]
  simp_rw [← hval]
  rw [tsum_mul_left, key]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : (0 : ℝ) < t := ht
  have hq : |Real.exp (-2 * π * t)| < 1 := by
    rw [Real.abs_exp, Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  have hlog := (Real.hasSum_pow_div_log_of_abs_lt_one hq).div_const (t ^ 2 + x ^ 2)
  rw [← neg_div, ← hlog.tsum_eq]
  congr 1
  funext m
  simp only [hF]
  rw [← Real.exp_nat_mul]
  push_cast
  field_simp

end Binet

open Set in
/-- DLMF 5.9.12, Gauss: `ψ(x) = ∫₀^∞ (e^(-t)/t - e^(-xt)/(1 - e^(-t))) dt` for `x > 0`. -/
@[dlmf 5.9.E12]
theorem digamma_gauss {x : ℝ} (hx : 0 < x) :
    Real.digamma x =
      ∫ t : ℝ in Set.Ioi 0,
        Real.exp (-t) / t - Real.exp (-x * t) / (1 - Real.exp (-t)) := by
  have hJ1 := integral_exp_mul_binetKernel_one
  have hA := integrableOn_digamma_add_euler hx
  have heq : EqOn (fun t => Real.exp (-t) / t - Real.exp (-x * t) / (1 - Real.exp (-t)))
      (fun t => (Real.exp (-t) - Real.exp (-x * t)) / (1 - Real.exp (-t)) -
        Real.exp (-1 * t) * binetKernel t) (Ioi 0) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have h1 : 1 - Real.exp (-t) ≠ 0 := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -t < 0); linarith
    simp only [binetKernel, neg_mul, one_mul]
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi heq,
    integral_sub hA (integrableOn_exp_mul_binetKernel one_pos), ← digamma_add_euler_Ioi hx, hJ1]
  ring

open Set in
/-- DLMF 5.9.13: `ψ(x) = ln x + ∫₀^∞ (1/t - 1/(1 - e^(-t))) e^(-tx) dt` for `x > 0`. -/
@[dlmf 5.9.E13]
theorem digamma_binet {x : ℝ} (hx : 0 < x) :
    Real.digamma x =
      Real.log x +
        ∫ t : ℝ in Set.Ioi 0,
          (1 / t - 1 / (1 - Real.exp (-t))) * Real.exp (-t * x) := by
  rw [digamma_eq_log_sub hx, sub_eq_add_neg, ← MeasureTheory.integral_neg]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [binetKernel]
  ring_nf

section Frullani

/-! ### The Frullani-type integrals for `ψ` and `γ`

The substitution `u = eᵗ - 1` turns the integral `ψ(x) + γ = ∫₀^∞ (e^{-t} - e^{-xt})/(1 - e^{-t})`
into `∫₀^∞ ((1+u)⁻¹ - (1+u)^{-x})/u`. The constant `γ = ∫₀^∞ ((1+t)⁻¹ - e^{-t})/t` is found by
truncating at `ε`, where both `∫_ε^∞ dt/(t(1+t)) = log((1+ε)/ε)` and
`∫_ε^∞ dt/(eᵗ - 1) = -log(1 - e^{-ε})` are elementary. -/

open Set

/-- `0 ≤ ((1+t)⁻¹ - e^{-t})/t ≤ 2/(1+t²)` for `t > 0`. -/
theorem eulerIntegrand_mem {t : ℝ} (ht : 0 < t) :
    0 ≤ (1 / (1 + t) - Real.exp (-t)) / t ∧
      (1 / (1 + t) - Real.exp (-t)) / t ≤ 2 / (1 + t ^ 2) := by
  have he := Real.exp_pos (-t)
  have h1 : (1 + t) * Real.exp (-t) ≤ 1 := by
    have h := Real.add_one_le_exp t
    have h3 : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  have hN : 1 / (1 + t) - Real.exp (-t) = (1 - (1 + t) * Real.exp (-t)) / (1 + t) := by
    field_simp
  have hkey : 1 - t ≤ (1 + t) ^ 2 * Real.exp (-t) := by
    rcases le_or_gt t 1 with h | h
    · have := Real.add_one_le_exp (-t)
      nlinarith [sq_nonneg t]
    · nlinarith [mul_pos (pow_pos (by linarith : (0 : ℝ) < 1 + t) 2) he]
  rw [hN, div_div]
  constructor
  · exact div_nonneg (by linarith) (by positivity)
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    set N := 1 - (1 + t) * Real.exp (-t)
    have hN0 : 0 ≤ N := by linarith
    have hNk : (1 + t) * N ≤ 2 * t := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hNk (by positivity : (0 : ℝ) ≤ 1 + t),
      mul_nonneg hN0 ht.le]

/-- `(1/(1 + t) - e^(-t))/t` is continuous on `(0, ∞)`. -/
theorem continuousOn_eulerIntegrand :
    ContinuousOn (fun t : ℝ => (1 / (1 + t) - Real.exp (-t)) / t) (Ioi 0) := by
  intro t ht
  have ht' : (0 : ℝ) < t := ht
  have h1 : 1 + t ≠ 0 := by linarith
  have h2 : t ≠ 0 := ht'.ne'
  exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))

/-- `(1/(1 + t) - e^(-t))/t` is integrable on `(0, ∞)`. -/
theorem integrableOn_eulerIntegrand :
    IntegrableOn (fun t : ℝ => (1 / (1 + t) - Real.exp (-t)) / t) (Ioi 0) := by
  refine Integrable.mono' ((integrable_inv_one_add_sq.const_mul 2).integrableOn)
    (continuousOn_eulerIntegrand.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  obtain ⟨h0, h1⟩ := eulerIntegrand_mem ht
  rw [Real.norm_of_nonneg h0]
  simpa [div_eq_mul_inv] using h1

/-- `∫_ε^∞ dt/(t(1+t)) = log((1+ε)/ε)`. -/
theorem integral_Ioi_one_div_mul_one_add {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t => 1 / (t * (1 + t))) (Ioi ε) ∧
      ∫ t in Ioi ε, 1 / (t * (1 + t)) = Real.log ((1 + ε) / ε) := by
  set F : ℝ → ℝ := fun t => -Real.log (1 + t⁻¹) with hF
  have hd : ∀ t ∈ Ioi ε, HasDerivAt F (1 / (t * (1 + t))) t := by
    intro t ht
    have ht' : 0 < t := hε.trans ht
    have hpos : 0 < 1 + t⁻¹ := by positivity
    have := ((hasDerivAt_inv ht'.ne').const_add 1).log hpos.ne' |>.neg
    have h0 : t ≠ 0 := ht'.ne'
    have h1 : 1 + t ≠ 0 := by linarith
    exact this.congr_deriv (by deriv_simp)
  have hcont : ContinuousWithinAt F (Ici ε) ε := by
    have hpos : 0 < 1 + ε⁻¹ := by positivity
    exact (((continuousAt_inv₀ hε.ne').const_add 1).log hpos.ne').neg.continuousWithinAt
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h := ((tendsto_inv_atTop_zero (𝕜 := ℝ)).const_add 1)
    rw [add_zero] at h
    have := ((Real.continuousAt_log one_ne_zero).tendsto.comp h).neg
    simpa [hF, Function.comp_def] using this
  have hint := integrableOn_Ioi_deriv_of_nonneg hcont hd
    (fun t ht => by have : 0 < t := hε.trans ht; positivity) hlim
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hd hint hlim]
  simp only [hF, zero_sub, neg_neg]
  congr 1
  field_simp
  ring

/-- `∫_ε^∞ dt/(eᵗ - 1) = -log(1 - e^{-ε})`. -/
theorem integral_Ioi_one_div_exp_sub_one {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t => 1 / (Real.exp t - 1)) (Ioi ε) ∧
      ∫ t in Ioi ε, 1 / (Real.exp t - 1) = -Real.log (1 - Real.exp (-ε)) := by
  set F : ℝ → ℝ := fun t => Real.log (1 - Real.exp (-t)) with hF
  have hlt : ∀ t : ℝ, 0 < t → 0 < 1 - Real.exp (-t) := fun t ht => by
    have := Real.exp_lt_one_iff.mpr (by linarith : -t < 0); linarith
  have hd : ∀ t ∈ Ioi ε, HasDerivAt F (1 / (Real.exp t - 1)) t := by
    intro t ht
    have ht' : 0 < t := hε.trans ht
    have := (((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).const_sub 1).log
      (hlt t ht').ne'
    have h1 := (exp_sub_one_pos ht').ne'
    have h2 := (hlt t ht').ne'
    have h4 : Real.exp t ≠ 0 := Real.exp_ne_zero t
    rw [Real.exp_neg] at h2
    exact this.congr_deriv (by
      simp only [Function.comp_apply, Real.exp_neg]
      field_simp)
  have hcont : ContinuousWithinAt F (Ici ε) ε :=
    ((continuous_const.sub (Real.continuous_exp.comp continuous_neg)).continuousAt.log
      (hlt ε hε).ne').continuousWithinAt
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h : Tendsto (fun t => 1 - Real.exp (-t)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub Real.tendsto_exp_neg_atTop_nhds_zero
    simpa [hF, Function.comp_def] using (Real.continuousAt_log one_ne_zero).tendsto.comp h
  have hint := integrableOn_Ioi_deriv_of_nonneg hcont hd
    (fun t ht => by have := exp_sub_one_pos (hε.trans ht); positivity) hlim
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hd hint hlim]
  simp [hF]

/-- `log((1+ε)/ε) + log(1 - e^{-ε}) → 0` as `ε → 0⁺`. -/
theorem tendsto_log_add_log_one_sub_exp :
    Tendsto (fun ε : ℝ => Real.log ((1 + ε) / ε) + Real.log (1 - Real.exp (-ε)))
      (𝓝[>] 0) (𝓝 0) := by
  have hone : Tendsto (fun ε : ℝ => 1 + ε) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun ε : ℝ => 1 + ε) (𝓝 0) (𝓝 (1 + 0)) := tendsto_const_nhds.add tendsto_id
    rw [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hratio : Tendsto (fun ε : ℝ => (1 - Real.exp (-ε)) / ε) (𝓝[>] 0) (𝓝 1) := by
    have hlo : Tendsto (fun ε : ℝ => 1 / (1 + ε)) (𝓝[>] 0) (𝓝 1) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).div hone one_ne_zero
      rwa [div_one] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0 : ℝ) < ε := hε
      have h := Real.add_one_le_exp ε
      have h3 : Real.exp ε * Real.exp (-ε) = 1 := by rw [← Real.exp_add]; simp
      rw [div_le_div_iff₀ (by positivity) hε']
      nlinarith [Real.exp_pos (-ε)]
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0 : ℝ) < ε := hε
      rw [div_le_one hε']
      have := Real.add_one_le_exp (-ε)
      linarith
  have hprod := (Real.continuousAt_log (by norm_num : (1 : ℝ) * 1 ≠ 0)).tendsto.comp
    (hone.mul hratio)
  rw [mul_one, Real.log_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  have hlt : 0 < 1 - Real.exp (-ε) := by
    have := Real.exp_lt_one_iff.mpr (by linarith : -ε < 0); linarith
  simp only [Function.comp_apply]
  rw [← Real.log_mul (by positivity) hlt.ne']
  congr 1
  field_simp

/-- `γ = ∫₀^∞ ((1+t)⁻¹ - e^{-t})/t dt`. -/
theorem eulerMascheroni_eq_integral_recip_one_add :
    Real.eulerMascheroniConstant = ∫ t in Ioi (0 : ℝ), (1 / (1 + t) - Real.exp (-t)) / t := by
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hε
  have hεpos : ∀ n, 0 < ε n := fun n => by positivity
  have hmono : Monotone fun n => Ioi (ε n) := by
    intro m n hmn
    apply Ioi_subset_Ioi
    simp only [hε]
    gcongr
  have hU : (⋃ n, Ioi (ε n)) = Ioi 0 := by
    ext t
    simp only [mem_iUnion, mem_Ioi]
    constructor
    · rintro ⟨n, hn⟩; exact (hεpos n).trans hn
    · intro ht
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt ht
      exact ⟨n, by simpa [hε] using hn⟩
  set f : ℝ → ℝ := fun t => (1 / (1 + t) - Real.exp (-t)) / t with hf
  set g : ℝ → ℝ := fun t => Real.exp (-1 * t) * binetKernel t with hg
  have hA := tendsto_setIntegral_of_monotone (μ := volume) (f := f)
    (fun n => measurableSet_Ioi) hmono (by rw [hU]; exact integrableOn_eulerIntegrand)
  have hB := tendsto_setIntegral_of_monotone (μ := volume) (f := g)
    (fun n => measurableSet_Ioi) hmono (by rw [hU]; exact integrableOn_exp_mul_binetKernel one_pos)
  rw [hU] at hA hB
  have hdiff : ∀ n, (∫ t in Ioi (ε n), f t) - ∫ t in Ioi (ε n), g t =
      Real.log ((1 + ε n) / ε n) + Real.log (1 - Real.exp (-ε n)) := by
    intro n
    obtain ⟨hi1, hv1⟩ := integral_Ioi_one_div_mul_one_add (hεpos n)
    obtain ⟨hi2, hv2⟩ := integral_Ioi_one_div_exp_sub_one (hεpos n)
    have hfi : IntegrableOn f (Ioi (ε n)) :=
      integrableOn_eulerIntegrand.mono_set (Ioi_subset_Ioi (hεpos n).le)
    have hgi : IntegrableOn g (Ioi (ε n)) :=
      (integrableOn_exp_mul_binetKernel one_pos).mono_set (Ioi_subset_Ioi (hεpos n).le)
    rw [← integral_sub hfi hgi]
    have heq : EqOn (fun t => f t - g t) (fun t => 1 / (t * (1 + t)) - 1 / (Real.exp t - 1))
        (Ioi (ε n)) := by
      intro t ht
      have ht' : 0 < t := (hεpos n).trans ht
      have h1 := (exp_sub_one_pos ht').ne'
      have h2 : 1 - Real.exp (-t) ≠ 0 := by
        have := Real.exp_lt_one_iff.mpr (by linarith : -t < 0); linarith
      have h3 : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
      simp only [hf, hg, binetKernel, neg_mul, one_mul]
      rw [Real.exp_neg t] at h2 ⊢
      have h4 : 1 + t ≠ 0 := by linarith
      field_simp
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_sub hi1 hi2, hv1, hv2]
    ring
  have hε0 : Tendsto ε atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall hεpos⟩
  have hlim := (hA.sub hB)
  have hlim' := tendsto_log_add_log_one_sub_exp.comp hε0
  have hzero : (∫ t in Ioi (0 : ℝ), f t) - ∫ t in Ioi (0 : ℝ), g t = 0 :=
    tendsto_nhds_unique (hlim.congr fun n => hdiff n) hlim'
  rw [hg, integral_exp_mul_binetKernel_one] at hzero
  linarith

/-- The substitution `u = eᵗ - 1`:
`∫₀^∞ ((1+u)⁻¹ - (1+u)^{-x})/u du = ∫₀^∞ (e^{-t} - e^{-xt})/(1 - e^{-t}) dt`. -/
theorem integral_rpow_sub_rpow_div_eq {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u : ℝ => (1 / (1 + u) - (1 + u) ^ (-x)) / u) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), (1 / (1 + u) - (1 + u) ^ (-x)) / u =
        ∫ t in Ioi (0 : ℝ), (Real.exp (-t) - Real.exp (-x * t)) / (1 - Real.exp (-t)) := by
  set f : ℝ → ℝ := fun t => Real.exp t - 1 with hf
  set g : ℝ → ℝ := fun u => (1 / (1 + u) - (1 + u) ^ (-x)) / u with hg
  have hf' : ∀ t ∈ Ioi (0 : ℝ), HasDerivWithinAt f (Real.exp t) (Ioi 0) t := fun t _ =>
    ((Real.hasDerivAt_exp t).sub_const 1).hasDerivWithinAt
  have hinj : InjOn f (Ioi 0) := fun a _ b _ h => Real.exp_injective (by simpa [hf] using h)
  have himg : f '' Ioi 0 = Ioi 0 := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact exp_sub_one_pos ht
    · intro hu
      have hu' : (0 : ℝ) < u := hu
      refine ⟨Real.log (1 + u), Real.log_pos (by linarith), ?_⟩
      simp [hf, Real.exp_log (by linarith : (0 : ℝ) < 1 + u)]
  have hcomp : EqOn (fun t => |Real.exp t| • g (f t))
      (fun t => (Real.exp (-t) - Real.exp (-x * t)) / (1 - Real.exp (-t))) (Ioi 0) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have h1 := (exp_sub_one_pos ht').ne'
    have h2 : 1 - Real.exp (-t) ≠ 0 := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -t < 0); linarith
    have h3 : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
    have hpow : Real.exp t ^ (-x) = Real.exp (-x * t) := by
      rw [← Real.exp_mul]; ring_nf
    simp only [hg, hf, smul_eq_mul, Real.abs_exp, add_sub_cancel, hpow]
    rw [Real.exp_neg t] at h2 ⊢
    field_simp
  have hRint := integrableOn_digamma_add_euler hx
  constructor
  · have := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hf' hinj g).mpr
      (hRint.congr_fun hcomp.symm measurableSet_Ioi)
    rwa [himg] at this
  · have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hf' hinj g
    rw [himg] at h
    rw [h]
    exact setIntegral_congr_fun measurableSet_Ioi hcomp

/-- DLMF 5.9.14: `ψ(x) = ∫₀^∞ (e^(-t) - (1 + t)^(-x)) dt/t` for `x > 0`. -/
@[dlmf 5.9.E14]
theorem digamma_frullani {x : ℝ} (hx : 0 < x) :
    Real.digamma x =
      ∫ t : ℝ in Set.Ioi 0, (Real.exp (-t) - (1 + t) ^ (-x)) / t := by
  obtain ⟨hint, heq⟩ := integral_rpow_sub_rpow_div_eq hx
  have hψ : Real.digamma x = (Real.digamma x + Real.eulerMascheroniConstant) -
      Real.eulerMascheroniConstant := by ring
  rw [hψ, digamma_add_euler_Ioi hx, ← heq]
  conv_lhs => rw [eulerMascheroni_eq_integral_recip_one_add]
  rw [← integral_sub hint integrableOn_eulerIntegrand]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  ring

end Frullani

open Set in
/-- `t e^(-xt)` is integrable on `(0, ∞)` for `x > 0`. -/
theorem integrableOn_mul_exp_neg_mul {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => t * Real.exp (-x * t)) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := x) (by norm_num)
    one_pos hx
  refine IntegrableOn.congr_fun this (fun t _ => ?_) measurableSet_Ioi
  simp [Real.rpow_one]

open Set in
/-- `∫₀^∞ t e^(-xt) dt = 1/x²` for `x > 0`. -/
theorem integral_mul_exp_neg_mul {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), t * Real.exp (-x * t) = 1 / x ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := x) two_pos hx
  norm_num at h
  rw [one_div, ← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [neg_mul]

open Set in
/-- DLMF 5.9.15: `ψ(x) = ln x - 1/(2x) - 2 ∫₀^∞ t dt/((t² + x²)(e^(2πt) - 1))` for `x > 0`. -/
@[dlmf 5.9.E15]
theorem digamma_coth {x : ℝ} (hx : 0 < x) :
    Real.digamma x =
      Real.log x - 1 / (2 * x) -
        2 * ∫ t : ℝ in Set.Ioi 0,
          t / ((t ^ 2 + x ^ 2) * (Real.exp (2 * π * t) - 1)) := by
  rw [digamma_eq_log_sub_binetBeta hx]
  congr 1
  have ha : ∀ m : ℕ, 0 < 2 * π * (m + 1) := fun m => by positivity
  set F : ℕ → ℝ → ℝ := fun m t =>
    2 * (Real.exp (-x * t) * (t / (t ^ 2 + (2 * π * (m + 1)) ^ 2))) with hF
  set G : ℕ → ℝ → ℝ := fun m u =>
    2 * (Real.exp (-(2 * π * (m + 1)) * u) * (u / (u ^ 2 + x ^ 2))) with hG
  have hFG : ∀ m, ∫ t in Ioi (0 : ℝ), F m t = ∫ u in Ioi (0 : ℝ), G m u := by
    intro m
    simp only [hF, hG, MeasureTheory.integral_const_mul]
    rw [integral_exp_mul_div_sq_add_sq_symm hx (ha m)]
  -- `0 ≤ e^{-ct} t/(t² + d²) ≤ t e^{-ct}/d²`
  have hle : ∀ c d t : ℝ, 0 < d → 0 < t →
      Real.exp (-c * t) * (t / (t ^ 2 + d ^ 2)) ≤ 1 / d ^ 2 * (t * Real.exp (-c * t)) := by
    intro c d t hd ht
    have := Real.exp_pos (-c * t)
    rw [div_mul_eq_mul_div, one_mul, mul_div_assoc', div_le_div_iff₀ (by positivity)
      (by positivity)]
    nlinarith [mul_pos (mul_pos this ht) (pow_pos ht 2)]
  have hint_gen : ∀ c d : ℝ, 0 < c → 0 < d → IntegrableOn
      (fun t => 2 * (Real.exp (-c * t) * (t / (t ^ 2 + d ^ 2)))) (Ioi 0) := by
    intro c d hc hd
    refine Integrable.mono' (((integrableOn_mul_exp_neg_mul hc).const_mul (1 / d ^ 2)).const_mul 2)
      ?_ ?_
    · exact (Continuous.mul continuous_const (Continuous.mul (by fun_prop)
        (Continuous.div continuous_id (by fun_prop) fun t => by positivity))).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
      have ht' : (0 : ℝ) < t := ht
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hle c d t hd ht') zero_le_two
  have hintF : ∀ m, Integrable (F m) (volume.restrict (Ioi (0 : ℝ))) := fun m =>
    hint_gen x _ hx (ha m)
  have hintG : ∀ m, Integrable (G m) (volume.restrict (Ioi (0 : ℝ))) := fun m =>
    hint_gen _ x (ha m) hx
  have hnormF : ∀ m, ∫ t in Ioi (0 : ℝ), ‖F m t‖ = ∫ t in Ioi (0 : ℝ), F m t := fun m =>
    setIntegral_congr_fun measurableSet_Ioi fun t ht => Real.norm_of_nonneg (by
      have : (0 : ℝ) < t := ht; positivity)
  have hnormG : ∀ m, ∫ u in Ioi (0 : ℝ), ‖G m u‖ = ∫ u in Ioi (0 : ℝ), G m u := fun m =>
    setIntegral_congr_fun measurableSet_Ioi fun u hu => Real.norm_of_nonneg (by
      have : (0 : ℝ) < u := hu; positivity)
  have hboundG : ∀ m, ∫ u in Ioi (0 : ℝ), G m u ≤ 2 * (1 / ((2 * π * (m + 1)) ^ 2 * x ^ 2)) := by
    intro m
    have h := setIntegral_mono_on (hintG m)
      (((integrableOn_mul_exp_neg_mul (ha m)).const_mul (1 / x ^ 2)).const_mul 2)
      measurableSet_Ioi fun u hu => mul_le_mul_of_nonneg_left
        (hle _ x u hx (by exact hu)) zero_le_two
    simp only [MeasureTheory.integral_const_mul, integral_mul_exp_neg_mul (ha m)] at h
    refine h.trans (le_of_eq ?_)
    field_simp
  have hsumG : Summable fun m => ∫ u in Ioi (0 : ℝ), ‖G m u‖ := by
    simp_rw [hnormG]
    exact Summable.of_nonneg_of_le (fun m => setIntegral_nonneg measurableSet_Ioi fun u hu => by
      have : (0 : ℝ) < u := hu; positivity) hboundG
      ((summable_recip_sq_two_pi (x := x ^ 2)).mul_left 2)
  have hsumF : Summable fun m => ∫ t in Ioi (0 : ℝ), ‖F m t‖ :=
    hsumG.congr fun m => by rw [hnormG m, hnormF m, hFG m]
  have keyF := integral_tsum_of_summable_integral_norm hintF hsumF
  have keyG := integral_tsum_of_summable_integral_norm hintG hsumG
  have h1 : ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * binetBeta t =
      ∫ t in Ioi (0 : ℝ), ∑' m, F m t := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ) < t := ht
    rw [← ((hasSum_binetBeta ht').mul_left (Real.exp (-x * t))).tsum_eq]
    congr 1
    funext m
    simp only [hF]
    ring
  have h2 : 2 * ∫ t in Ioi (0 : ℝ), t / ((t ^ 2 + x ^ 2) * (Real.exp (2 * π * t) - 1)) =
      ∫ u in Ioi (0 : ℝ), ∑' m, G m u := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu' : (0 : ℝ) < u := hu
    have hs := (hasSum_recip_exp_two_pi_sub_one hu').mul_left (2 * (u / (u ^ 2 + x ^ 2)))
    have hG' : (fun m => G m u) = fun m : ℕ =>
        2 * (u / (u ^ 2 + x ^ 2)) * Real.exp (-(2 * π * (m + 1)) * u) := by
      funext m; simp only [hG]; ring
    rw [hG', hs.tsum_eq]
    have := (exp_sub_one_pos (by positivity : 0 < 2 * π * u)).ne'
    field_simp
  rw [h1, h2, ← keyF, ← keyG]
  simp_rw [hFG]

/-- DLMF 5.9.16: `ψ(x) + γ = ∫₀^∞ (e^(-t) - e^(-xt))/(1 - e^(-t)) dt = ∫₀¹ (1 - t^(x-1))/(1 - t) dt`
for `x > 0`. -/
@[dlmf 5.9.E16]
theorem digamma_add_euler {x : ℝ} (hx : 0 < x) :
    Real.digamma x + Real.eulerMascheroniConstant =
      ∫ t : ℝ in Set.Ioi 0,
        (Real.exp (-t) - Real.exp (-x * t)) / (1 - Real.exp (-t)) ∧
    Real.digamma x + Real.eulerMascheroniConstant =
      ∫ t : ℝ in (0 : ℝ)..1, (1 - t ^ (x - 1)) / (1 - t) := by
  refine ⟨digamma_add_euler_Ioi hx, ?_⟩
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  exact digamma_add_euler_Ioo hx

/-- DLMF 5.9.18: `γ = -∫₀^∞ e^(-t) ln t dt = ∫₀^∞ (1/(1 + t) - e^(-t)) dt/t`. -/
@[dlmf 5.9.E18]
theorem eulerMascheroni_integrals :
    Real.eulerMascheroniConstant =
      -∫ t : ℝ in Set.Ioi 0, Real.exp (-t) * Real.log t ∧
    Real.eulerMascheroniConstant =
      ∫ t : ℝ in Set.Ioi 0, (1 / (1 + t) - Real.exp (-t)) / t := by
  refine ⟨?_, eulerMascheroni_eq_integral_recip_one_add⟩
  rw [Real.eulerMascheroniConstant_eq_neg_integral_log]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun t _ => mul_comm _ _

section LogMoments

/-! ### Derivatives and integrals of `Γ` in the order (DLMF 5.9.19–20)

Both formulas differentiate Euler's integral under the integral sign. The integrands are
dominated using `|log t|^k ≤ (t^{kε} + t^{-kε})/εᵏ` and the convergence of Euler's integral. -/

open Set

/-- `|log t|^k ≤ (t^{kε} + t^{-kε})/εᵏ` for `t, ε > 0`. -/
theorem abs_log_pow_le {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) (k : ℕ) :
    |Real.log t| ^ k ≤ (t ^ (k * ε) + t ^ (-(k * ε))) / ε ^ k := by
  have hpow : ∀ a : ℝ, (t ^ a / ε) ^ k = t ^ (k * a) / ε ^ k := fun a => by
    rw [div_pow, ← Real.rpow_natCast (t ^ a), ← Real.rpow_mul ht.le, mul_comm]
  rcases le_or_gt 1 t with h1 | h1
  · have hl : 0 ≤ Real.log t := Real.log_nonneg h1
    rw [abs_of_nonneg hl]
    calc Real.log t ^ k ≤ (t ^ ε / ε) ^ k := pow_le_pow_left₀ hl (Real.log_le_rpow_div ht.le hε) k
      _ = t ^ (k * ε) / ε ^ k := hpow ε
      _ ≤ _ := by gcongr; exact le_add_of_nonneg_right (by positivity)
  · have hl : Real.log t < 0 := Real.log_neg ht h1
    have hle := Real.log_le_rpow_div (inv_pos.mpr ht).le hε
    rw [Real.log_inv, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le] at hle
    rw [abs_of_neg hl]
    calc (-Real.log t) ^ k ≤ (t ^ (-ε) / ε) ^ k := pow_le_pow_left₀ (by linarith) hle k
      _ = t ^ (-(k * ε)) / ε ^ k := by rw [hpow (-ε)]; ring_nf
      _ ≤ _ := by gcongr; exact le_add_of_nonneg_left (by positivity)

/-- `|log t|^k e^(-t) t^(s-1)` is continuous on `(0, ∞)`. -/
theorem continuousOn_abs_log_pow_mul_Gamma (k : ℕ) (s : ℝ) :
    ContinuousOn (fun t => |Real.log t| ^ k * Real.exp (-t) * t ^ (s - 1)) (Ioi 0) := by
  intro t ht
  have ht' : t ≠ 0 := (ne_of_gt ht)
  exact (((continuous_abs.continuousAt.comp (Real.continuousAt_log ht')).pow k).mul
    (Real.continuous_exp.comp continuous_neg).continuousAt).mul
    (Real.continuousAt_rpow_const t (s - 1) (Or.inl ht')) |>.continuousWithinAt

/-- `(log t)^k e^(-t) t^(s-1)` is continuous on `(0, ∞)`. -/
theorem continuousOn_log_pow_mul_Gamma (k : ℕ) (s : ℝ) :
    ContinuousOn (fun t => Real.log t ^ k * Real.exp (-t) * t ^ (s - 1)) (Ioi 0) := by
  intro t ht
  have ht' : t ≠ 0 := (ne_of_gt ht)
  exact (((Real.continuousAt_log ht').pow k).mul
    (Real.continuous_exp.comp continuous_neg).continuousAt).mul
    (Real.continuousAt_rpow_const t (s - 1) (Or.inl ht')) |>.continuousWithinAt

/-- Integrability of `|log t|ᵏ e^{-t} t^{s-1}` on `(0, ∞)` for `s > 0`. -/
theorem integrableOn_abs_log_pow_mul_Gamma {s : ℝ} (hs : 0 < s) (k : ℕ) :
    IntegrableOn (fun t => |Real.log t| ^ k * Real.exp (-t) * t ^ (s - 1)) (Ioi 0) := by
  set ε := s / (2 * (k + 1)) with hε
  have hε0 : 0 < ε := by positivity
  have hkε : k * ε < s := by
    have h : (k : ℝ) * ε = s * (k / (2 * (k + 1))) := by rw [hε]; ring
    have h' : (k : ℝ) / (2 * (k + 1)) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    rw [h]; nlinarith
  have hkε0 : 0 ≤ (k : ℝ) * ε := by positivity
  have h1 := Real.GammaIntegral_convergent (by linarith : 0 < s + k * ε)
  have h2 := Real.GammaIntegral_convergent (by linarith : 0 < s - k * ε)
  refine Integrable.mono' ((h1.add h2).div_const (ε ^ k))
    ((continuousOn_abs_log_pow_mul_Gamma k s).aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht' : (0 : ℝ) < t := ht
  rw [Real.norm_of_nonneg (by positivity)]
  have hb := abs_log_pow_le ht' hε0 k
  have he1 : t ^ (s + k * ε - 1) = t ^ (k * ε) * t ^ (s - 1) := by
    rw [← Real.rpow_add ht']; ring_nf
  have he2 : t ^ (s - k * ε - 1) = t ^ (-(k * ε)) * t ^ (s - 1) := by
    rw [← Real.rpow_add ht']; ring_nf
  simp only [Pi.add_apply, he1, he2]
  have hp : 0 ≤ Real.exp (-t) * t ^ (s - 1) := by positivity
  calc |Real.log t| ^ k * Real.exp (-t) * t ^ (s - 1)
      = |Real.log t| ^ k * (Real.exp (-t) * t ^ (s - 1)) := by ring
    _ ≤ (t ^ (k * ε) + t ^ (-(k * ε))) / ε ^ k * (Real.exp (-t) * t ^ (s - 1)) :=
        mul_le_mul_of_nonneg_right hb hp
    _ = _ := by ring

/-- `(log t)^k e^(-t) t^(s-1)` is integrable on `(0, ∞)` for `s > 0`. -/
theorem integrableOn_log_pow_mul_Gamma {s : ℝ} (hs : 0 < s) (k : ℕ) :
    IntegrableOn (fun t => Real.log t ^ k * Real.exp (-t) * t ^ (s - 1)) (Ioi 0) := by
  refine (integrableOn_abs_log_pow_mul_Gamma hs k).mono'
    ((continuousOn_log_pow_mul_Gamma k s).aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht' : (0 : ℝ) < t := ht
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Real.abs_exp,
    abs_of_pos (Real.rpow_pos_of_pos ht' _)]

/-- `t^{y-1} ≤ t^{a-1} + t^{b-1}` for `t > 0` and `a ≤ y ≤ b`. -/
theorem rpow_le_rpow_add_rpow {t a b y : ℝ} (ht : 0 < t) (hay : a ≤ y) (hyb : y ≤ b) :
    t ^ (y - 1) ≤ t ^ (a - 1) + t ^ (b - 1) := by
  rcases le_or_gt 1 t with h1 | h1
  · have := Real.rpow_le_rpow_of_exponent_le h1 (by linarith : y - 1 ≤ b - 1)
    have := Real.rpow_pos_of_pos ht (a - 1)
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge ht h1.le (by linarith : a - 1 ≤ y - 1)
    have := Real.rpow_pos_of_pos ht (b - 1)
    linarith

/-- `y ↦ t^(y-1)` has derivative `t^(y-1) log t` for `t > 0`. -/
theorem hasDerivAt_rpow_sub_one {t : ℝ} (ht : 0 < t) (y : ℝ) :
    HasDerivAt (fun y => t ^ (y - 1)) (t ^ (y - 1) * Real.log t) y := by
  have h := (Real.hasStrictDerivAt_const_rpow ht (y - 1)).hasDerivAt.comp y
    ((hasDerivAt_id y).sub_const 1)
  simp only [id_eq, mul_one, Function.comp_def] at h
  exact h

/-- `Iₙ(x) = ∫₀^∞ (log t)ⁿ e^{-t} t^{x-1} dt`. -/
def gammaLogMoment (n : ℕ) (x : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.log t ^ n * Real.exp (-t) * t ^ (x - 1)

/-- The log-moments `∫₀^∞ (log t)ⁿ e^(-t) t^(x-1) dt` satisfy `d/dx Mₙ(x) = M_{n+1}(x)` for `x > 0`.
-/
theorem hasDerivAt_gammaLogMoment (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (gammaLogMoment n) (gammaLogMoment (n + 1) x) x := by
  have hball : Metric.ball x (x / 2) ∈ 𝓝 x := Metric.ball_mem_nhds _ (by positivity)
  have hy : ∀ y ∈ Metric.ball x (x / 2), x / 2 ≤ y ∧ y ≤ 2 * x := by
    intro y hy
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy
    constructor <;> linarith [hy.1, hy.2]
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun y t => Real.log t ^ n * Real.exp (-t) * t ^ (y - 1))
    (F' := fun y t => Real.log t ^ (n + 1) * Real.exp (-t) * t ^ (y - 1))
    (bound := fun t => |Real.log t| ^ (n + 1) * Real.exp (-t) * t ^ (x / 2 - 1) +
      |Real.log t| ^ (n + 1) * Real.exp (-t) * t ^ (2 * x - 1))
    hball (Eventually.of_forall fun y =>
      (continuousOn_log_pow_mul_Gamma n y).aestronglyMeasurable measurableSet_Ioi)
    (integrableOn_log_pow_mul_Gamma hx n)
    (integrableOn_log_pow_mul_Gamma hx (n + 1)).aestronglyMeasurable ?_
    ((integrableOn_abs_log_pow_mul_Gamma (by positivity) _).add
      (integrableOn_abs_log_pow_mul_Gamma (by positivity) _)) ?_
  · exact h.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht y hy'
    have ht' : (0 : ℝ) < t := ht
    obtain ⟨hy1, hy2⟩ := hy y hy'
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Real.abs_exp,
      abs_of_pos (Real.rpow_pos_of_pos ht' _)]
    have hA : 0 ≤ |Real.log t| ^ (n + 1) * Real.exp (-t) := by positivity
    calc |Real.log t| ^ (n + 1) * Real.exp (-t) * t ^ (y - 1)
        ≤ |Real.log t| ^ (n + 1) * Real.exp (-t) * (t ^ (x / 2 - 1) + t ^ (2 * x - 1)) :=
          mul_le_mul_of_nonneg_left (rpow_le_rpow_add_rpow ht' hy1 hy2) hA
      _ = _ := by ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht y _
    have ht' : (0 : ℝ) < t := ht
    have := (hasDerivAt_rpow_sub_one ht' y).const_mul (Real.log t ^ n * Real.exp (-t))
    exact this.congr_deriv (by deriv_simp)

/-- DLMF 5.9.19: `Γ^(n)(x) = ∫₀^∞ (ln t)ⁿ e^(-t) t^(x-1) dt` for `x > 0`. -/
@[dlmf 5.9.E19]
theorem iteratedDeriv_Gamma {n : ℕ} {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n Real.Gamma x =
      ∫ t : ℝ in Set.Ioi 0, (Real.log t) ^ n * Real.exp (-t) * t ^ (x - 1) := by
  induction n generalizing x with
  | zero =>
    rw [iteratedDeriv_zero, Real.Gamma_eq_integral hx]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv n Real.Gamma =ᶠ[𝓝 x] gammaLogMoment n := by
      filter_upwards [Ioi_mem_nhds hx] with y hy using ih hy
    rw [heq.deriv_eq, (hasDerivAt_gammaLogMoment n hx).deriv]
    rfl

/-- `|(t^{a-1} - t^{b-1})/log t| ≤ |a - b| (t^{m-1} + t^{M-1})` with `m = min a b`,
`M = max a b`, by the mean value theorem in the exponent. -/
theorem abs_rpow_sub_rpow_div_log_le {t a b : ℝ} (ht : 0 < t) :
    |(t ^ (a - 1) - t ^ (b - 1)) / Real.log t| ≤
      |a - b| * (t ^ (min a b - 1) + t ^ (max a b - 1)) := by
  rcases eq_or_ne t 1 with rfl | ht1
  · simp
  have hlog : Real.log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one ht ht1
  have key : ∀ a b : ℝ, a < b → ∃ c ∈ Ioo a b,
      (t ^ (b - 1) - t ^ (a - 1)) / Real.log t = (b - a) * t ^ (c - 1) := by
    intro a b hab
    obtain ⟨c, hc, hd⟩ := exists_hasDerivAt_eq_slope (fun y => t ^ (y - 1))
      (fun y => t ^ (y - 1) * Real.log t) hab
      (fun y _ => (hasDerivAt_rpow_sub_one ht y).continuousAt.continuousWithinAt)
      (fun y _ => hasDerivAt_rpow_sub_one ht y)
    refine ⟨c, hc, ?_⟩
    have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
    rw [eq_div_iff hba] at hd
    field_simp
    linarith
  rcases lt_trichotomy a b with hab | rfl | hab
  · obtain ⟨c, hc, hv⟩ := key a b hab
    rw [show (t ^ (a - 1) - t ^ (b - 1)) / Real.log t =
      -((t ^ (b - 1) - t ^ (a - 1)) / Real.log t) by ring, hv, min_eq_left hab.le,
      max_eq_right hab.le, abs_neg, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht _),
      abs_sub_comm]
    exact mul_le_mul_of_nonneg_left (rpow_le_rpow_add_rpow ht hc.1.le hc.2.le) (abs_nonneg _)
  · simp
  · obtain ⟨c, hc, hv⟩ := key b a hab
    rw [hv, min_eq_right hab.le, max_eq_left hab.le, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos ht _), abs_sub_comm]
    exact mul_le_mul_of_nonneg_left (rpow_le_rpow_add_rpow ht hc.1.le hc.2.le) (abs_nonneg _)

/-- `(t^(a-1) - t^(b-1)) e^(-t)/log t` is continuous on `(0, ∞) \ {1}`. -/
theorem continuousOn_rpow_sub_rpow_div_log (a b : ℝ) :
    ContinuousOn (fun t => (t ^ (a - 1) - t ^ (b - 1)) / Real.log t * Real.exp (-t))
      (Ioi 0 \ {1}) := by
  intro t ht
  have ht0 : t ≠ 0 := (ne_of_gt ht.1)
  have hlog : Real.log t ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one ht.1 ht.2
  exact ((((Real.continuousAt_rpow_const t (a - 1) (Or.inl ht0)).sub
    (Real.continuousAt_rpow_const t (b - 1) (Or.inl ht0))).div (Real.continuousAt_log ht0)
    hlog).mul (Real.continuous_exp.comp continuous_neg).continuousAt).continuousWithinAt

/-- `(t^(a-1) - t^(b-1)) e^(-t)/log t` is integrable on `(0, ∞)` for `a, b > 0`. -/
theorem integrableOn_rpow_sub_rpow_div_log {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun t => (t ^ (a - 1) - t ^ (b - 1)) / Real.log t * Real.exp (-t)) (Ioi 0) := by
  have hm : 0 < min a b := lt_min ha hb
  have hM : 0 < max a b := lt_max_of_lt_left ha
  have hdom := ((Real.GammaIntegral_convergent hm).add
    (Real.GammaIntegral_convergent hM)).const_mul |a - b|
  have hdiff : Ioi (0 : ℝ) =ᵐ[volume] (Ioi 0 \ {1} : Set ℝ) :=
    (sdiff_null_ae_eq_self (measure_singleton 1)).symm
  rw [IntegrableOn, Measure.restrict_congr_set hdiff]
  refine Integrable.mono' (hdom.mono_measure (Measure.restrict_mono sdiff_subset le_rfl))
    ((continuousOn_rpow_sub_rpow_div_log a b).aestronglyMeasurable
      (measurableSet_Ioi.diff (measurableSet_singleton 1))) ?_
  refine (ae_restrict_iff' (measurableSet_Ioi.diff (measurableSet_singleton 1))).mpr
    (Eventually.of_forall fun t ht => ?_)
  have ht' : (0 : ℝ) < t := ht.1
  rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
  have := abs_rpow_sub_rpow_div_log_le (a := a) (b := b) ht'
  simp only [Pi.add_apply]
  calc |(t ^ (a - 1) - t ^ (b - 1)) / Real.log t| * Real.exp (-t)
      ≤ |a - b| * (t ^ (min a b - 1) + t ^ (max a b - 1)) * Real.exp (-t) :=
        mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
    _ = _ := by ring

/-- DLMF 5.9.20: `∫_c^x Γ(t) dt = ∫₀^∞ (t^(x-1) - t^(c-1)) e^(-t)/ln t dt` for `c, x > 0`. -/
@[dlmf 5.9.E20]
theorem integral_Gamma {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    ∫ t : ℝ in c..x, Real.Gamma t =
      ∫ t : ℝ in Set.Ioi 0,
        (t ^ (x - 1) - t ^ (c - 1)) / Real.log t * Real.exp (-t) := by
  set H : ℝ → ℝ := fun y =>
    ∫ t in Ioi (0 : ℝ), (t ^ (y - 1) - t ^ (c - 1)) / Real.log t * Real.exp (-t) with hH
  have hderiv : ∀ y, 0 < y → HasDerivAt H (Real.Gamma y) y := by
    intro y hy
    have hball : Metric.ball y (y / 2) ∈ 𝓝 y := Metric.ball_mem_nhds _ (by positivity)
    have hy' : ∀ z ∈ Metric.ball y (y / 2), y / 2 ≤ z ∧ z ≤ 2 * y := by
      intro z hz
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hz
      constructor <;> linarith [hz.1, hz.2]
    have hpos : ∀ z ∈ Metric.ball y (y / 2), 0 < z := fun z hz => by
      linarith [(hy' z hz).1]
    have hne1 : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), t ≠ 1 :=
      ae_restrict_of_ae (Measure.ae_ne volume 1)
    have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Ioi (0 : ℝ)))
      (F := fun z t => (t ^ (z - 1) - t ^ (c - 1)) / Real.log t * Real.exp (-t))
      (F' := fun z t => Real.exp (-t) * t ^ (z - 1))
      (bound := fun t => Real.exp (-t) * t ^ (y / 2 - 1) + Real.exp (-t) * t ^ (2 * y - 1))
      hball ?_ (integrableOn_rpow_sub_rpow_div_log hy hc)
      (Real.GammaIntegral_convergent hy).aestronglyMeasurable ?_
      ((Real.GammaIntegral_convergent (by positivity)).add
        (Real.GammaIntegral_convergent (by positivity))) ?_
    · rw [Real.Gamma_eq_integral hy]
      exact h.2
    · filter_upwards [hball] with z hz
      exact (integrableOn_rpow_sub_rpow_div_log (hpos z hz) hc).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
      have ht' : (0 : ℝ) < t := ht
      obtain ⟨hz1, hz2⟩ := hy' z hz
      rw [Real.norm_of_nonneg (by positivity)]
      have := rpow_le_rpow_add_rpow ht' hz1 hz2
      have he := Real.exp_pos (-t)
      nlinarith
    · filter_upwards [ae_restrict_mem measurableSet_Ioi, hne1] with t ht ht1 z _
      have ht' : (0 : ℝ) < t := ht
      have hlog : Real.log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one ht' ht1
      have := (((hasDerivAt_rpow_sub_one ht' z).sub_const (t ^ (c - 1))).div_const
        (Real.log t)).mul_const (Real.exp (-t))
      exact this.congr_deriv (by deriv_simp)
  have hpos : ∀ y ∈ uIcc c x, 0 < y := fun y hy => by
    rcases (mem_uIcc.mp hy) with h | h
    · exact hc.trans_le h.1
    · exact hx.trans_le h.1
  have hcont : ContinuousOn Real.Gamma (uIcc c x) := fun y hy =>
    (Real.differentiableAt_Gamma fun m =>
      (lt_of_le_of_lt (neg_nonpos.mpr m.cast_nonneg) (hpos y hy)).ne').continuousAt
      |>.continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y hy => hderiv y (hpos y hy))
    (hcont.intervalIntegrable)]
  have hHc : H c = 0 := by simp [hH]
  rw [hHc, sub_zero]

end LogMoments

end DLMF.Gamma
