/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Schlafli
public import DLMF.Bessel.SecondKind

/-!
# Schläfli's integral for `Y_ν` (DLMF 10.9.7)

For complex `ν` and `re z > 0`,
`Y_ν(z) = π⁻¹ ∫₀^π sin(z sin θ - νθ) dθ - π⁻¹ ∫₀^∞ (e^{νt} + e^{-νt} cos νπ) e^{-z sinh t} dt`.

At noninteger order this is `Y_ν = (J_ν cos νπ - J_{-ν}) / sin νπ` with Schläfli's integral for
`J_{±ν}` (`besselJ_eq_schlafli`, DLMF 10.9.6) and the reflection `θ ↦ π - θ` of the angular
integral; both sides are continuous in `ν`, which covers the integer orders.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set Filter
open scoped Real Topology

namespace DLMF.Bessel

/-- The reflection `θ ↦ π - θ` in the angular Schläfli integral. -/
theorem schlafli_integral_cos_add (z μ : ℂ) :
    ∫ θ in (0:ℝ)..π, cos (z * Real.sin θ + μ * θ) =
      cos (μ * π) * (∫ θ in (0:ℝ)..π, cos (z * Real.sin θ - μ * θ)) -
        sin (μ * π) * ∫ θ in (0:ℝ)..π, sin (z * Real.sin θ - μ * θ) := by
  have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := π)
    (fun θ : ℝ => cos (z * Real.sin θ + μ * θ)) π
  simp only [sub_zero, sub_self] at h
  rw [← h, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub]
  · refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [Real.sin_pi_sub]
    rw [show z * (Real.sin θ : ℂ) + μ * ((π - θ : ℝ) : ℂ) =
      (z * Real.sin θ - μ * θ) + μ * π by push_cast; ring, cos_add]
    ring
  · exact (by fun_prop : Continuous fun θ : ℝ => cos (μ * π) * cos (z * Real.sin θ - μ * θ))
      |>.intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun θ : ℝ => sin (μ * π) * sin (z * Real.sin θ - μ * θ))
      |>.intervalIntegrable _ _

/-- **Schläfli's integral for `Y_ν`** (DLMF 10.9.7), for complex order and `re z > 0`. -/
@[dlmf 10.9.E7]
theorem besselY_eq_schlafli (ν : ℂ) {z : ℂ} (hz : 0 < z.re) :
    besselY ν z = (1 / π * ∫ θ in (0:ℝ)..π, sin (z * Real.sin θ - ν * θ)) -
      1 / π * ∫ t in Ioi (0:ℝ), (exp (ν * t) + exp (-(ν * t)) * cos (ν * π)) *
        exp (-(z * Real.sinh t)) := by
  set R : ℂ → ℂ := fun μ => ∫ t in Ioi (0:ℝ), exp (-(z * Real.sinh t) - μ * t)
  set Sg : ℂ → ℂ := fun μ => ∫ θ in (0:ℝ)..π, sin (z * Real.sin θ - μ * θ)
  have hsplit : (∫ t in Ioi (0:ℝ), (exp (ν * t) + exp (-(ν * t)) * cos (ν * π)) *
      exp (-(z * Real.sinh t))) = R (-ν) + cos (ν * π) * R ν := by
    simp only [R]
    rw [← integral_const_mul, ← integral_add (integrableOn_schlafli (-ν) hz)
      ((integrableOn_schlafli ν hz).const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    have e1 : exp (ν * t) * exp (-(z * Real.sinh t)) = exp (-(z * Real.sinh t) - -ν * t) := by
      rw [← exp_add]; ring_nf
    have e2 : exp (-(ν * t)) * exp (-(z * Real.sinh t)) = exp (-(z * Real.sinh t) - ν * t) := by
      rw [← exp_add]; ring_nf
    linear_combination e1 + cos (ν * π) * e2
  rw [hsplit]
  have hzs : z ∈ slitPlane := Or.inl hz
  have hRc : Continuous R := (differentiable_schlafli_order hz).continuous
  have hSc : Continuous Sg :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) _ _
  refine DLMF.Confluent.eq_of_continuousAt_of_integerComplement (f := fun μ => besselY μ z)
    (g := fun μ => 1 / π * Sg μ - 1 / π * (R (-μ) + cos (μ * π) * R μ))
    (continuousAt_besselY_order id continuous_id ν hzs) ?_ (fun c hc => ?_)
  · exact ((continuous_const.mul hSc).sub (continuous_const.mul
      ((hRc.comp continuous_neg).add ((by fun_prop : Continuous fun μ : ℂ => cos (μ * π)).mul
        hRc)))).continuousAt
  · have hcz := DLMF.Confluent.forall_of_mem_integerComplement hc
    have hs := sin_mul_pi_ne_zero hcz
    have hJ := besselJ_eq_schlafli c hz
    have hJ' := besselJ_eq_schlafli (-c) hz
    have hA := schlafli_integral_cos_add z c
    simp only [neg_mul, sub_neg_eq_add] at hJ'
    rw [besselY_eq_of_not_int hcz, besselD, hJ, hJ', hA]
    simp only [R, Sg, neg_mul, sub_neg_eq_add, sin_neg]
    have hp : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    generalize sin (c * π) = s at hs ⊢
    field_simp
    ring

end DLMF.Bessel
