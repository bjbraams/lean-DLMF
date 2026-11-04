/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Basic.Properties
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Modulus and phase of the Airy functions (DLMF §9.8)

On the real line, `Ai(x) = M(x) sin θ(x)`, `Bi(x) = M(x) cos θ(x)`, and similarly
`Ai'(x) = N(x) sin φ(x)`, `Bi'(x) = N(x) cos φ(x)` (DLMF 9.8.1–9.8.8).

## Main definitions

* `DLMF.Airy.Real.airyAi`, `DLMF.Airy.Real.airyBi`, `DLMF.Airy.Real.airyAiDeriv`,
  `DLMF.Airy.Real.airyBiDeriv`: the real restrictions.
* `airyModulus`, `airyDerivModulus`: the moduli `M` and `N` (DLMF 9.8.3, 9.8.7).
* `airyPhase`, `airyDerivPhase`: the phases `θ` and `φ`, normalized by `θ(0) = π/6` and
  `φ(0) = -π/6`.

## Main results

* `airyAi_ofReal_eq` and siblings: the real restrictions recover the complex values.
* `wronskian_airyReal`: the real Wronskian.
* `airyModulus_pos`, `airyModulus_sq`, `hasDerivAt_airyModulus` and the `N` analogues.
* `hasDerivAt_airyPhase`, `hasDerivAt_airyDerivPhase`: `θ' = -1/(πM²)`, `φ' = x/(πN²)`.
* `airy_lagrange`: `N²M² = (AA' + BB')² + π⁻²`.

## Implementation notes

The phases are defined as integrals of their derivatives, so they are continuous on all of
`ℝ`. The representations `Bi + i Ai = M e^{iθ}`, the asymptotic expansions and the remaining
§9.8 results are in `DLMF.Airy.ModulusPhase.Representations`.
-/

@[expose] public noncomputable section

open Complex
open scoped Real

namespace DLMF.Airy

/-- Ai restricted to the real axis. -/
def Real.airyAi (x : ℝ) : ℝ := (Airy.airyAi x).re

/-- Bi restricted to the real axis. -/
def Real.airyBi (x : ℝ) : ℝ := (Airy.airyBi x).re

/-- Ai' restricted to the real axis. -/
def Real.airyAiDeriv (x : ℝ) : ℝ := (Airy.airyAiDeriv x).re

/-- Bi' restricted to the real axis. -/
def Real.airyBiDeriv (x : ℝ) : ℝ := (Airy.airyBiDeriv x).re

/-- Airy modulus M. -/
@[dlmf 9.8.E3]
def airyModulus (x : ℝ) : ℝ := Real.sqrt (DLMF.Airy.Real.airyAi x ^ 2 + DLMF.Airy.Real.airyBi x ^ 2)

/-- Derivative modulus N. -/
@[dlmf 9.8.E7]
def airyDerivModulus (x : ℝ) : ℝ :=
    Real.sqrt (DLMF.Airy.Real.airyAiDeriv x ^ 2 + DLMF.Airy.Real.airyBiDeriv x ^ 2)

/-- The unwrapped phase θ, normalized to θ(0)=π/6. -/
def airyPhase (x : ℝ) : ℝ := π / 6 - ∫ t in (0 : ℝ)..x, 1 / (π * airyModulus t ^ 2)

/-- The unwrapped derivative phase φ, normalized to φ(0)=-π/6. -/
def airyDerivPhase (x : ℝ) : ℝ := -π / 6 + ∫ t in (0 : ℝ)..x, t / (π * airyDerivModulus t ^ 2)

/-- `Ai(x)` as the cast of its real part. -/
theorem airyAi_ofReal_eq (x : ℝ) : airyAi x = (DLMF.Airy.Real.airyAi x : ℂ) :=
  Complex.ext (by simp [DLMF.Airy.Real.airyAi]) (by simp [airyAi_ofReal_im])

/-- `Bi(x)` as the cast of its real part. -/
theorem airyBi_ofReal_eq (x : ℝ) : airyBi x = (DLMF.Airy.Real.airyBi x : ℂ) :=
  Complex.ext (by simp [DLMF.Airy.Real.airyBi]) (by simp [airyBi_ofReal_im])

/-- `Ai'(x)` as the cast of its real part. -/
theorem airyAiDeriv_ofReal_eq (x : ℝ) : airyAiDeriv x = (DLMF.Airy.Real.airyAiDeriv x : ℂ) :=
  Complex.ext (by simp [DLMF.Airy.Real.airyAiDeriv]) (by simp [airyAiDeriv_ofReal_im])

/-- `Bi'(x)` as the cast of its real part. -/
theorem airyBiDeriv_ofReal_eq (x : ℝ) : airyBiDeriv x = (DLMF.Airy.Real.airyBiDeriv x : ℂ) :=
  Complex.ext (by simp [DLMF.Airy.Real.airyBiDeriv]) (by simp [airyBiDeriv_ofReal_im])

/-- The real derivative of `Ai` on the real axis. -/
theorem Real.hasDerivAt_airyAi (x : ℝ) : HasDerivAt DLMF.Airy.Real.airyAi
    (DLMF.Airy.Real.airyAiDeriv x) x :=
  (Airy.hasDerivAt_airyAi x).real_of_complex

/-- The real derivative of `Bi` on the real axis. -/
theorem Real.hasDerivAt_airyBi (x : ℝ) : HasDerivAt DLMF.Airy.Real.airyBi
    (DLMF.Airy.Real.airyBiDeriv x) x :=
  (Airy.hasDerivAt_airyBi x).real_of_complex

/-- Airy's equation for `Ai` on the real axis. -/
theorem Real.hasDerivAt_airyAiDeriv (x : ℝ) :
    HasDerivAt DLMF.Airy.Real.airyAiDeriv (x * DLMF.Airy.Real.airyAi x) x := by
  have h := (Airy.hasDerivAt_airyAiDeriv x).real_of_complex
  exact h.congr_deriv (by simp [DLMF.Airy.Real.airyAi])

/-- Airy's equation for `Bi` on the real axis. -/
theorem Real.hasDerivAt_airyBiDeriv (x : ℝ) :
    HasDerivAt DLMF.Airy.Real.airyBiDeriv (x * DLMF.Airy.Real.airyBi x) x := by
  have h := (Airy.hasDerivAt_airyBiDeriv x).real_of_complex
  exact h.congr_deriv (by simp [DLMF.Airy.Real.airyBi])

/-- The real Wronskian `Ai Bi' - Ai' Bi = 1/π`. -/
theorem wronskian_airyReal (x : ℝ) :
    DLMF.Airy.Real.airyAi x * DLMF.Airy.Real.airyBiDeriv x - DLMF.Airy.Real.airyAiDeriv x *
        DLMF.Airy.Real.airyBi x = 1 / π := by
  have h := wronskian_airyAi_airyBi x
  rw [airyAi_ofReal_eq, airyBi_ofReal_eq, airyAiDeriv_ofReal_eq, airyBiDeriv_ofReal_eq] at h
  exact_mod_cast h

/-- `Ai² + Bi² > 0` on the real axis. -/
theorem airyModulusSq_pos (x : ℝ) : 0 < DLMF.Airy.Real.airyAi x ^ 2 +
    DLMF.Airy.Real.airyBi x ^ 2 := by
  by_contra h
  have ha : DLMF.Airy.Real.airyAi x = 0 := by
      nlinarith [sq_nonneg (DLMF.Airy.Real.airyAi x), sq_nonneg (DLMF.Airy.Real.airyBi x)]
  have hb : DLMF.Airy.Real.airyBi x = 0 := by
      nlinarith [sq_nonneg (DLMF.Airy.Real.airyAi x), sq_nonneg (DLMF.Airy.Real.airyBi x)]
  have hw := wronskian_airyReal x
  rw [ha, hb] at hw
  have : (1 / π : ℝ) ≠ 0 := by have := Real.pi_pos; positivity
  exact this (by linarith)

/-- `Ai'² + Bi'² > 0` on the real axis. -/
theorem airyDerivModulusSq_pos (x : ℝ) : 0 < DLMF.Airy.Real.airyAiDeriv x ^ 2 +
    DLMF.Airy.Real.airyBiDeriv x ^ 2 := by
  by_contra h
  have ha : DLMF.Airy.Real.airyAiDeriv x = 0 := by
    nlinarith [sq_nonneg (DLMF.Airy.Real.airyAiDeriv x), sq_nonneg (DLMF.Airy.Real.airyBiDeriv x)]
  have hb : DLMF.Airy.Real.airyBiDeriv x = 0 := by
    nlinarith [sq_nonneg (DLMF.Airy.Real.airyAiDeriv x), sq_nonneg (DLMF.Airy.Real.airyBiDeriv x)]
  have hw := wronskian_airyReal x
  rw [ha, hb] at hw
  have : (1 / π : ℝ) ≠ 0 := by have := Real.pi_pos; positivity
  exact this (by linarith)

/-- `M² = Ai² + Bi²`. -/
theorem airyModulus_sq (x : ℝ) : airyModulus x ^ 2 = DLMF.Airy.Real.airyAi x ^ 2 +
    DLMF.Airy.Real.airyBi x ^ 2 :=
  Real.sq_sqrt (airyModulusSq_pos x).le

/-- `N² = Ai'² + Bi'²`. -/
theorem airyDerivModulus_sq (x : ℝ) :
    airyDerivModulus x ^ 2 = DLMF.Airy.Real.airyAiDeriv x ^ 2 + DLMF.Airy.Real.airyBiDeriv x ^ 2 :=
  Real.sq_sqrt (airyDerivModulusSq_pos x).le

/-- `M > 0`. -/
theorem airyModulus_pos (x : ℝ) : 0 < airyModulus x := Real.sqrt_pos.mpr (airyModulusSq_pos x)

/-- `N > 0`. -/
theorem airyDerivModulus_pos (x : ℝ) : 0 < airyDerivModulus x :=
  Real.sqrt_pos.mpr (airyDerivModulusSq_pos x)

/-- `M' = (Ai Ai' + Bi Bi')/M`. -/
theorem hasDerivAt_airyModulus (x : ℝ) :
    HasDerivAt airyModulus
      ((DLMF.Airy.Real.airyAi x * DLMF.Airy.Real.airyAiDeriv x + DLMF.Airy.Real.airyBi x *
          DLMF.Airy.Real.airyBiDeriv x) /
        airyModulus x) x := by
  have h := (((DLMF.Airy.Real.hasDerivAt_airyAi x).pow 2).add
      ((DLMF.Airy.Real.hasDerivAt_airyBi x).pow 2)).sqrt
    (airyModulusSq_pos x).ne'
  refine h.congr_deriv ?_
  simp only [airyModulus, Pi.add_apply, Pi.pow_apply]
  have := airyModulus_pos x
  simp only [airyModulus] at this
  field_simp
  push_cast
  ring

/-- `N' = x (Ai Ai' + Bi Bi')/N`. -/
theorem hasDerivAt_airyDerivModulus (x : ℝ) :
    HasDerivAt airyDerivModulus
      (x * (DLMF.Airy.Real.airyAi x * DLMF.Airy.Real.airyAiDeriv x + DLMF.Airy.Real.airyBi x *
          DLMF.Airy.Real.airyBiDeriv x) /
        airyDerivModulus x) x := by
  have h := (((DLMF.Airy.Real.hasDerivAt_airyAiDeriv x).pow 2).add
      ((DLMF.Airy.Real.hasDerivAt_airyBiDeriv x).pow 2)).sqrt
    (airyDerivModulusSq_pos x).ne'
  refine h.congr_deriv ?_
  simp only [airyDerivModulus, Pi.add_apply, Pi.pow_apply]
  have := airyDerivModulus_pos x
  simp only [airyDerivModulus] at this
  field_simp
  push_cast
  ring

/-- `M` is continuous. -/
theorem continuous_airyModulus : Continuous airyModulus :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_airyModulus x).continuousAt

/-- `N` is continuous. -/
theorem continuous_airyDerivModulus : Continuous airyDerivModulus :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_airyDerivModulus x).continuousAt

/-- `θ' = -1/(π M²)`. -/
theorem hasDerivAt_airyPhase (x : ℝ) : HasDerivAt airyPhase (-(1 / (π * airyModulus x ^ 2))) x := by
  have hc : Continuous fun t => 1 / (π * airyModulus t ^ 2) := by
    refine continuous_const.div (continuous_const.mul (continuous_airyModulus.pow 2)) fun t => ?_
    have := airyModulus_pos t; have := Real.pi_pos; positivity
  have h := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  exact h.const_sub _

/-- `φ' = x/(π N²)`. -/
theorem hasDerivAt_airyDerivPhase (x : ℝ) :
    HasDerivAt airyDerivPhase (x / (π * airyDerivModulus x ^ 2)) x := by
  have hc : Continuous fun t => t / (π * airyDerivModulus t ^ 2) := by
    refine continuous_id.div (continuous_const.mul (continuous_airyDerivModulus.pow 2)) fun t => ?_
    have := airyDerivModulus_pos t; have := Real.pi_pos; positivity
  have h := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  exact h.const_add _

/-- The derivative of `M` as a function. -/
theorem deriv_airyModulus : deriv airyModulus = fun x =>
    (DLMF.Airy.Real.airyAi x * DLMF.Airy.Real.airyAiDeriv x + DLMF.Airy.Real.airyBi x *
        DLMF.Airy.Real.airyBiDeriv x) / airyModulus x :=
  funext fun x => (hasDerivAt_airyModulus x).deriv

/-- The derivative of `N` as a function. -/
theorem deriv_airyDerivModulus : deriv airyDerivModulus = fun x =>
    x * (DLMF.Airy.Real.airyAi x * DLMF.Airy.Real.airyAiDeriv x + DLMF.Airy.Real.airyBi x *
        DLMF.Airy.Real.airyBiDeriv x) /
      airyDerivModulus x :=
  funext fun x => (hasDerivAt_airyDerivModulus x).deriv

/-- The derivative of `θ` as a function. -/
theorem deriv_airyPhase : deriv airyPhase = fun x => -(1 / (π * airyModulus x ^ 2)) :=
  funext fun x => (hasDerivAt_airyPhase x).deriv

/-- The derivative of `φ` as a function. -/
theorem deriv_airyDerivPhase : deriv airyDerivPhase = fun x => x / (π * airyDerivModulus x ^ 2) :=
  funext fun x => (hasDerivAt_airyDerivPhase x).deriv

/-- The Lagrange identity combined with the Wronskian: `N² M² = (AA' + BB')² + π⁻²`. -/
theorem airy_lagrange (x : ℝ) :
    (DLMF.Airy.Real.airyAiDeriv x ^ 2 + DLMF.Airy.Real.airyBiDeriv x ^ 2) *
        (DLMF.Airy.Real.airyAi x ^ 2 + DLMF.Airy.Real.airyBi x ^ 2) * π ^ 2
      = (DLMF.Airy.Real.airyAi x * DLMF.Airy.Real.airyAiDeriv x + DLMF.Airy.Real.airyBi x *
          DLMF.Airy.Real.airyBiDeriv x) ^ 2 * π ^ 2 + 1 := by
  have hW := wronskian_airyReal x
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hW' : (DLMF.Airy.Real.airyAi x * DLMF.Airy.Real.airyBiDeriv x -
      DLMF.Airy.Real.airyAiDeriv x * DLMF.Airy.Real.airyBi x) * π = 1 := by
    rw [hW]; field_simp
  linear_combination ((DLMF.Airy.Real.airyAi x * DLMF.Airy.Real.airyBiDeriv x -
      DLMF.Airy.Real.airyAiDeriv x * DLMF.Airy.Real.airyBi x) * π
    + 1) * hW'

/-- `S = AA' + BB'`, half the derivative of `M²`. -/
theorem hasDerivAt_airyCross (x : ℝ) :
    HasDerivAt (fun t => DLMF.Airy.Real.airyAi t * DLMF.Airy.Real.airyAiDeriv t +
        DLMF.Airy.Real.airyBi t * DLMF.Airy.Real.airyBiDeriv t)
      (DLMF.Airy.Real.airyAiDeriv x ^ 2 + DLMF.Airy.Real.airyBiDeriv x ^ 2 +
        x * (DLMF.Airy.Real.airyAi x ^ 2 + DLMF.Airy.Real.airyBi x ^ 2)) x := by
  have h := ((DLMF.Airy.Real.hasDerivAt_airyAi x).mul (DLMF.Airy.Real.hasDerivAt_airyAiDeriv x)).add
    ((DLMF.Airy.Real.hasDerivAt_airyBi x).mul (DLMF.Airy.Real.hasDerivAt_airyBiDeriv x))
  exact h.congr_deriv (by ring)

/-- `M²` as a function. -/
theorem airyModulus_sq_fun : (fun t => airyModulus t ^ 2) =
    fun t => DLMF.Airy.Real.airyAi t ^ 2 + DLMF.Airy.Real.airyBi t ^ 2 := funext airyModulus_sq

end DLMF.Airy
