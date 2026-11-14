/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.ODE.ComplexBesselExpansion

/-!
# Infinity-selected simple-pole solutions on progressive Bessel branches

Olver, *Asymptotics and Special Functions*, Chapter 12, Theorem 9.1 and
§10, pp. 458–462, and Chapter 13, §§5–6, pp. 487–491,
synopsis O-13.03. The solution is selected by its actual K normalization
at a prescribed progressive infinity, rather than by a finite initial jet.
Every later error bound retains that prescribed initial tail.
-/

@[expose] public noncomputable section

open Set Filter Complex ODE
open scoped Topology

namespace DLMF.AsymptoticApproximations.ComplexBesselComparison

/-- A prescribed progressive infinity selects an exact K-recessive solution. Its
relative error and normalized derivative vanish there, and its adaptive-envelope bound
holds on every path retaining that initial tail. The source radius-ratio constant and
actual variation of `sqrt(zeta)*B0` are displayed.
Olver, Chapter 12, Theorem 9.1 and §10; Chapter 13, §§5–6, synopsis O-13.03. -/
theorem exists_complex_simplePole_K_recessive
    {D : Set ℂ} (hD : IsOpen D) (hstar : StarConvex ℝ 0 D) (hzero : 0 ∈ D)
    {ψ : ℂ → ℂ} {A B : ℕ → ℂ → ℂ} {ν : ℝ} (hν : 0 ≤ ν)
    {u : ℂ} (hu : u ≠ 0) (hseq : IsSimplePoleCoefficientSequence ψ ν A B D)
    {γ₀ : ℝ → ℂ} (hγ₀ : ContinuousOn γ₀ (Ioc 0 1))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) 1, TauCeti.IsPiecewiseC1On γ₀ t 1)
    (him : ∀ t ∈ Ioc (0 : ℝ) 1, exp (γ₀ t) ∈ D)
    (harg : ∀ t ∈ Ioc (0 : ℝ) 1, |(log u + γ₀ t / 2).im| ≤ Real.pi / 2)
    (hprogress : AntitoneOn (fun t => (u * exp (γ₀ t / 2)).re) (Ioc 0 1))
    (hinfty : Tendsto (fun t => (u * exp (γ₀ t / 2)).re) (𝓝[>] 0) atTop)
    {r : ℝ} (hr : 1 ≤ r)
    (hratio : ∀ s ∈ Ioc (0 : ℝ) 1, ∀ t ∈ Icc s 1,
      ‖exp (γ₀ t)‖ ≤ r * ‖exp (γ₀ s)‖)
    (hvar : BoundedVariationOn (fun t => exp (γ₀ t / 2) * B 0 (exp (γ₀ t))) (Ioc 0 1)) :
    ∃ S ε : ℂ → ℂ, AnalyticOnNhd ℂ S {w | exp w ∈ D} ∧
      AnalyticOnNhd ℂ ε {w | exp w ∈ D} ∧
      (∀ w : ℂ, exp w ∈ D →
        S w = comparison 1 ν u w + ε w ∧
        deriv (deriv S) w - deriv S w =
          (u ^ 2 * exp w / 4 + ((ν : ℂ) ^ 2 - 1) / 4 + exp w * ψ (exp w)) * S w) ∧
      Tendsto (fun t => ε (γ₀ t) / comparison 1 ν u (γ₀ t)) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun t => deriv ε (γ₀ t) / deriv (comparison 1 ν u) (γ₀ t))
        (𝓝[>] 0) (𝓝 0) ∧
      (∀ (γ : ℝ → ℂ) (ratio : ℝ), 1 ≤ ratio →
        ContinuousOn γ (Ioc 0 1) →
        (∀ t ∈ Ioo (0 : ℝ) 1, TauCeti.IsPiecewiseC1On γ t 1) →
        (∀ t ∈ Ioc (0 : ℝ) 1, exp (γ t) ∈ D) →
        (∀ᶠ t : ℝ in 𝓝[>] 0, γ t = γ₀ t) →
        (∀ t ∈ Ioc (0 : ℝ) 1, |(log u + γ t / 2).im| ≤ Real.pi / 2) →
        AntitoneOn (fun t => (u * exp (γ t / 2)).re) (Ioc 0 1) →
        (∀ s ∈ Ioc (0 : ℝ) 1, ∀ t ∈ Icc s 1, ‖exp (γ t)‖ ≤ ratio * ‖exp (γ s)‖) →
        BoundedVariationOn (fun t => exp (γ t / 2) * B 0 (exp (γ t))) (Ioc 0 1) →
        let V := (eVariationOn (fun t => exp (γ t / 2) * B 0 (exp (γ t))) (Ioc 0 1)).toReal
        let c := BesselComplexEnvelope.kernelConstant ν ratio
        ‖ε (γ 1)‖ ≤ envelope 1 ν u (γ 1) * c * Real.exp (c * V / ‖u‖) * V / ‖u‖) := by
  sorry

end DLMF.AsymptoticApproximations.ComplexBesselComparison
