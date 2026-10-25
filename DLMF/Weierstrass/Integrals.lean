/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.DifferentialEquations
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Integral representations and indefinite integrals (DLMF §§23.11, 23.14)

**Source corrections in §23.11.** DLMF 23.11.2–23.11.3 are stated with `τ = ω₃/ω₁` only, but
they are not homogeneous in the lattice: 23.11.2 holds exactly for the normalization
`2ω₁ = 1` (lattice generators `1, τ`) and fails for other `ω₁` (checked for
`ω₁ = 1, π, π/2, i, i/2`). With `2ω₁ = 1`, the integral in the printed 23.11.3 must be
multiplied by `4`: `ζ(z) = 1/z + 4∫₀^∞ (…) ds` (the printed form fails by about `0.08`
for `τ = 0.3 + 0.9i`, `z = 0.3 + 0.2i`; the corrected form agrees to `10⁻¹⁰`, and its
derivative is `-℘` by 23.11.2). The printed convergence condition `-1 < ℜ(z + τ) < 1` is also
insufficient: the `f₁` part of the integrands grows like `e^{(|ℜ(z ± τ)| - 1)s}`, so we
assume `|ℜz| + |ℜτ| < 1` (which gives `|ℜ(z ± τ)| < 1`) together with `|ℑz| < ℑτ`.

Indefinite integrals (§23.14) are stated as derivative identities for `z ∉ 𝕃`.
-/

@[expose] public section

open Complex PeriodPair MeasureTheory
open scoped Real

noncomputable section

namespace DLMF.Weierstrass

/-- `f₁(s, τ) = cosh²(τs/2)/(1 - 2e^{-s}cosh(τs) + e^{-2s})` (DLMF 23.11.1). -/
@[dlmf 23.11.E1]
def integralKernelOne (s τ : ℂ) : ℂ :=
  Complex.cosh (τ * s / 2) ^ 2 / (1 - 2 * cexp (-s) * Complex.cosh (τ * s) + cexp (-2 * s))

/-- `f₂(s, τ) = cos²(s/2)/(1 - 2e^{iτs}cos s + e^{2iτs})` (DLMF 23.11.1). -/
@[dlmf 23.11.E1]
def integralKernelTwo (s τ : ℂ) : ℂ :=
  Complex.cos (s / 2) ^ 2 / (1 - 2 * cexp (I * τ * s) * Complex.cos s + cexp (2 * I * τ * s))

namespace HalfPeriods

variable (H : HalfPeriods)

/-- DLMF 23.11.2 (normalization `2ω₁ = 1`, corrected domain): for `z ≠ 0` with
`|ℜz| + |ℜτ| < 1` and `|ℑz| < ℑτ`,
`℘(z) = 1/z² + 8∫₀^∞ s(e^{-s}sinh²(zs/2)f₁(s,τ) + e^{iτs}sin²(zs/2)f₂(s,τ)) ds`.
Corrected from the printed DLMF formula: the identity holds only for the normalization
`2ω₁ = 1`, and the printed condition `-1 < ℜ(z+τ) < 1` does not make the integral converge
(`τ = -0.6 + i`, `z = 0.6 + 0.1i`: integrand `4.4·10⁷` at `s = 80`); `|ℜz| + |ℜτ| < 1`,
`|ℑz| < ℑτ` is assumed instead. -/
@[dlmf 23.11.E2]
theorem weierstrassP_integral (hω : H.ω₁ = 1 / 2) {z : ℂ} (hz : z ≠ 0)
    (hre : |z.re| + |H.tau.re| < 1) (him : |z.im| < H.tau.im) :
    IntegrableOn (fun s : ℝ ↦ (s : ℂ) * (cexp (-s) * Complex.sinh (z * s / 2) ^ 2 *
        integralKernelOne s H.tau +
        cexp (I * H.tau * s) * Complex.sin (z * s / 2) ^ 2 * integralKernelTwo s H.tau))
      (Set.Ioi 0) ∧
    H.weierstrassP z = 1 / z ^ 2 + 8 * ∫ s in Set.Ioi (0 : ℝ), (s : ℂ) *
      (cexp (-s) * Complex.sinh (z * s / 2) ^ 2 * integralKernelOne s H.tau +
        cexp (I * H.tau * s) * Complex.sin (z * s / 2) ^ 2 * integralKernelTwo s H.tau) := by
  sorry

/-- DLMF 23.11.3, **corrected** (factor `4`, normalization `2ω₁ = 1`, corrected domain): for
`z ≠ 0` with `|ℜz| + |ℜτ| < 1` and `|ℑz| < ℑτ`,
`ζ(z) = 1/z + 4∫₀^∞ (e^{-s}(zs - sinh(zs))f₁(s,τ) - e^{iτs}(zs - sin(zs))f₂(s,τ)) ds`.
Corrected from the printed DLMF formula: the printed integral lacks the factor `4` (off by about
0.08 at `τ = 0.3 + 0.9i`, `z = 0.3 + 0.2i`), and normalization and domain are corrected as in
23.11.2. -/
@[dlmf 23.11.E3]
theorem weierstrassZeta_integral (hω : H.ω₁ = 1 / 2) {z : ℂ} (hz : z ≠ 0)
    (hre : |z.re| + |H.tau.re| < 1) (him : |z.im| < H.tau.im) :
    IntegrableOn (fun s : ℝ ↦ cexp (-s) * (z * s - Complex.sinh (z * s)) *
        integralKernelOne s H.tau -
        cexp (I * H.tau * s) * (z * s - Complex.sin (z * s)) * integralKernelTwo s H.tau)
      (Set.Ioi 0) ∧
    H.weierstrassZeta z = 1 / z + 4 * ∫ s in Set.Ioi (0 : ℝ),
      (cexp (-s) * (z * s - Complex.sinh (z * s)) * integralKernelOne s H.tau -
        cexp (I * H.tau * s) * (z * s - Complex.sin (z * s)) * integralKernelTwo s H.tau) := by
  sorry

end HalfPeriods

/-! ### Indefinite integrals (§23.14) -/

/-- DLMF 23.14.1: `∫℘(z) dz = -ζ(z)`, i.e. `(-ζ)' = ℘` off the lattice. -/
@[dlmf 23.14.E1]
theorem hasDerivAt_neg_weierstrassZeta (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt (fun w ↦ -weierstrassZeta L w) (℘[L] z) z := by
  have h := (hasDerivAt_weierstrassZeta L hz).neg
  rw [neg_neg] at h
  exact h

/-- `℘'` has derivative `6℘² - g₂/2` off the lattice. -/
theorem wp23_hasDerivAt_derivWeierstrassP (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt ℘'[L] (6 * ℘[L] z ^ 2 - L.g₂ / 2) z := by
  have hU : IsOpen (L.latticeᶜ : Set ℂ) := L.isClosed_lattice.isOpen_compl
  have hd := (L.analyticOnNhd_derivWeierstrassP z hz).differentiableAt
  rw [← deriv_derivWeierstrassP L hz]
  exact hd.hasDerivAt

/-- DLMF 23.14.2: `∫℘²(z) dz = ℘'(z)/6 + g₂z/12`, i.e. the derivative of the right side is
`℘²` off the lattice. -/
@[dlmf 23.14.E2]
theorem hasDerivAt_weierstrassP_sq_primitive (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt (fun w ↦ ℘'[L] w / 6 + L.g₂ * w / 12) (℘[L] z ^ 2) z := by
  have h1 := (wp23_hasDerivAt_derivWeierstrassP L hz).div_const 6
  have h2 := ((hasDerivAt_id z).const_mul L.g₂).div_const 12
  have h := h1.add h2
  have e : (fun w ↦ ℘'[L] w / 6 + L.g₂ * w / 12) =
      (fun x ↦ ℘'[L] x / 6) + fun x ↦ L.g₂ * id x / 12 := rfl
  rw [e]
  convert h using 1
  ring

/-- DLMF 23.14.3: `∫℘³(z) dz = ℘'''(z)/120 - (3/20)g₂ζ(z) + g₃z/10`, i.e. the derivative of
the right side is `℘³` off the lattice. -/
@[dlmf 23.14.E3]
theorem hasDerivAt_weierstrassP_cube_primitive (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt (fun w ↦ deriv (deriv ℘'[L]) w / 120 - 3 / 20 * L.g₂ * weierstrassZeta L w +
      L.g₃ * w / 10) (℘[L] z ^ 3) z := by
  have hU : IsOpen (L.latticeᶜ : Set ℂ) := L.isClosed_lattice.isOpen_compl
  -- `℘''' = 12℘℘'` near `z`.
  have hev : deriv (deriv ℘'[L]) =ᶠ[nhds z] fun w ↦ 12 * ℘[L] w * ℘'[L] w :=
    Filter.eventually_of_mem (hU.mem_nhds hz) fun w hw ↦ deriv_deriv_derivWeierstrassP L hw
  have hP : HasDerivAt ℘[L] (℘'[L] z) z := by
    have := (L.differentiableOn_weierstrassP z hz).differentiableAt (hU.mem_nhds hz)
    simpa using this.hasDerivAt
  have hP' := wp23_hasDerivAt_derivWeierstrassP L hz
  have h3 : HasDerivAt (deriv (deriv ℘'[L]))
      (12 * (℘'[L] z * ℘'[L] z + ℘[L] z * (6 * ℘[L] z ^ 2 - L.g₂ / 2))) z := by
    refine HasDerivAt.congr_of_eventuallyEq ?_ hev
    convert (hP.mul hP').const_mul 12 using 1
    · ext w; simp only [Pi.mul_apply]; ring
  have hsq := L.derivWeierstrassP_sq z hz
  have hZ := (hasDerivAt_weierstrassZeta L hz).const_mul (3 / 20 * L.g₂)
  have hA := h3.div_const 120
  have hB := ((hasDerivAt_id z).const_mul L.g₃).div_const 10
  have h := (hA.sub hZ).add hB
  have e : (fun w ↦ deriv (deriv ℘'[L]) w / 120 - 3 / 20 * L.g₂ * weierstrassZeta L w +
      L.g₃ * w / 10) = ((fun w ↦ deriv (deriv ℘'[L]) w / 120) -
        fun w ↦ 3 / 20 * L.g₂ * weierstrassZeta L w) + fun x ↦ L.g₃ * id x / 10 := rfl
  rw [e]
  convert h using 1
  linear_combination (-(1 : ℂ) / 10) * hsq

end DLMF.Weierstrass
