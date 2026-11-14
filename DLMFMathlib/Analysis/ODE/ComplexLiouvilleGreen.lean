/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.BoundedVariation
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On

/-!
# Complex Liouville–Green solutions along progressive paths

Olver, *Asymptotics and Special Functions*, Chapter 6, Theorems 11.1–12.1,
pp. 222–224, and the parameter scaling in §5. Branches of the fourth root,
the phase primitive and the error-control primitive are explicit. Path regularity
uses TauCeti's piecewise `C¹` API; variation is Mathlib's `eVariationOn`.
-/

@[expose] public section

open Filter Set
open scoped Topology

noncomputable section

namespace Complex

/-- Analytic Liouville–Green branch data, Olver, Chapter 6, (2.01) and §11.
The amplitude is `f^(-1/4)`, the phase derivative is `sqrt f`, and the control
derivative is `f^(-1/4)(f^(-1/4))″-g/sqrt f`. -/
structure IsComplexLiouvilleGreenData
    (f g amplitude phase control : ℂ → ℂ) (D : Set ℂ) : Prop where
  /-- The leading equation coefficient is analytic. -/
  analytic_f : AnalyticOnNhd ℂ f D
  /-- The lower-order equation coefficient is analytic. -/
  analytic_g : AnalyticOnNhd ℂ g D
  /-- The chosen fourth-root amplitude is analytic. -/
  analytic_amplitude : AnalyticOnNhd ℂ amplitude D
  /-- The phase primitive is analytic. -/
  analytic_phase : AnalyticOnNhd ℂ phase D
  /-- The error-control primitive is analytic. -/
  analytic_control : AnalyticOnNhd ℂ control D
  /-- The amplitude is a branch of `f^(-1/4)`, excluding zeros of either factor. -/
  amplitude_fourth_mul : ∀ z ∈ D, amplitude z ^ 4 * f z = 1
  /-- The phase has the compatible square-root derivative. -/
  deriv_phase : ∀ z ∈ D, deriv phase z = (amplitude z ^ 2)⁻¹
  /-- The derivative of the error-control primitive. -/
  deriv_control : ∀ z ∈ D, deriv control z =
    amplitude z * deriv (deriv amplitude) z - g z * amplitude z ^ 2

/-- The analytic and normalization conditions defining the complex LG data,
Olver, Chapter 6, (2.01) and §11. -/
theorem isComplexLiouvilleGreenData_iff (f g amplitude phase control : ℂ → ℂ) (D : Set ℂ) :
    IsComplexLiouvilleGreenData f g amplitude phase control D ↔
      AnalyticOnNhd ℂ f D ∧ AnalyticOnNhd ℂ g D ∧ AnalyticOnNhd ℂ amplitude D ∧
      AnalyticOnNhd ℂ phase D ∧ AnalyticOnNhd ℂ control D ∧
      (∀ z ∈ D, amplitude z ^ 4 * f z = 1) ∧
      (∀ z ∈ D, deriv phase z = (amplitude z ^ 2)⁻¹) ∧
      ∀ z ∈ D, deriv control z =
        amplitude z * deriv (deriv amplitude) z - g z * amplitude z ^ 2 := by
  constructor
  · intro h
    exact ⟨h.analytic_f, h.analytic_g, h.analytic_amplitude, h.analytic_phase,
      h.analytic_control, h.amplitude_fourth_mul, h.deriv_phase, h.deriv_control⟩
  · rintro ⟨hf, hg, hA, hξ, hF, hroot, hphase, hcontrol⟩
    exact ⟨hf, hg, hA, hξ, hF, hroot, hphase, hcontrol⟩

/-- Olver, Chapter 6, §11: on a simply connected zero-free coefficient domain,
the branch amplitude and the two normalized primitives exist. -/
theorem exists_complexLiouvilleGreenData {D : Set ℂ} {f g : ℂ → ℂ} {b a₀ : ℂ}
    (hD : IsOpen D) (hsc : IsSimplyConnected D) (hb : b ∈ D)
    (hf : AnalyticOnNhd ℂ f D) (hg : AnalyticOnNhd ℂ g D)
    (hfne : ∀ z ∈ D, f z ≠ 0) (ha₀ : a₀ ^ 4 * f b = 1) :
    ∃ amplitude phase control : ℂ → ℂ,
      IsComplexLiouvilleGreenData f g amplitude phase control D ∧
      amplitude b = a₀ ∧ phase b = 0 ∧ control b = 0 := by
  sorry

/-- Olver, Chapter 6, Theorem 11.1, p. 222: the finite-reference complex LG
solution and its progressive-path error bound. Scaling by nonzero `u` gives the
equation `w″=(u²f+g)w`; both signs are included. -/
theorem exists_complexLiouvilleGreen_finite_reference
    {D : Set ℂ} {f g amplitude phase control : ℂ → ℂ} {b u : ℂ} {σ : ℝ}
    (hD : IsOpen D) (hsc : IsSimplyConnected D) (hb : b ∈ D) (hu : u ≠ 0)
    (hσ : σ = 1 ∨ σ = -1)
    (hd : IsComplexLiouvilleGreenData f g amplitude phase control D) :
    ∃ ε : ℂ → ℂ, AnalyticOnNhd ℂ ε D ∧ ε b = 0 ∧ deriv ε b = 0 ∧
      (∀ z ∈ D,
        let w := fun t => amplitude t * exp (σ * u * phase t) * (1 + ε t)
        deriv (deriv w) z = (u ^ 2 * f z + g z) * w z) ∧
      ∀ γ : ℝ → ℂ, TauCeti.IsPiecewiseC1On γ 0 1 → γ 0 = b →
        (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ D) →
        MonotoneOn (fun t => σ * (u * phase (γ t)).re) (Icc 0 1) →
        BoundedVariationOn (control ∘ γ) (Icc 0 1) →
        ‖ε (γ 1)‖ ≤ Real.exp ((eVariationOn (control ∘ γ) (Icc 0 1)).toReal / ‖u‖) - 1 ∧
        ‖amplitude (γ 1) ^ 2 * deriv ε (γ 1) / u‖ ≤
          Real.exp ((eVariationOn (control ∘ γ) (Icc 0 1)).toReal / ‖u‖) - 1 := by
  sorry

/-- Olver, Chapter 6, Theorem 11.1: an endpoint-reference solution normalized
along a prescribed initial arc. A finite boundary point or infinity is allowed.
All later progressive paths retain that initial tail in their variation bound. -/
theorem exists_complexLiouvilleGreen_endpoint_reference
    {D : Set ℂ} {f g amplitude phase control : ℂ → ℂ} {u : ℂ} {σ : ℝ}
    {γ₀ : ℝ → ℂ} (hD : IsOpen D) (hsc : IsSimplyConnected D) (hu : u ≠ 0)
    (hσ : σ = 1 ∨ σ = -1)
    (hd : IsComplexLiouvilleGreenData f g amplitude phase control D)
    (hγ₀ : ContinuousOn γ₀ (Ioc 0 1))
    (hregular : ∀ s : ℝ, 0 < s → s < 1 → TauCeti.IsPiecewiseC1On γ₀ s 1)
    (himage : ∀ t ∈ Ioc (0 : ℝ) 1, γ₀ t ∈ D)
    (hprogressive : MonotoneOn (fun t => σ * (u * phase (γ₀ t)).re) (Ioc 0 1))
    (hvariation : BoundedVariationOn (control ∘ γ₀) (Ioc 0 1))
    (hend : (∃ a : ℂ, a ∉ D ∧ Tendsto γ₀ (𝓝[>] 0) (𝓝 a)) ∨
      Tendsto (fun t => ‖γ₀ t‖) (𝓝[>] 0) atTop) :
    ∃ ε : ℂ → ℂ, AnalyticOnNhd ℂ ε D ∧
      (∀ z ∈ D,
        let w := fun t => amplitude t * exp (σ * u * phase t) * (1 + ε t)
        deriv (deriv w) z = (u ^ 2 * f z + g z) * w z) ∧
      Tendsto (ε ∘ γ₀) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun t => amplitude (γ₀ t) ^ 2 * deriv ε (γ₀ t) / u) (𝓝[>] 0) (𝓝 0) ∧
      ∀ s ∈ Ioc (0 : ℝ) 1, ∀ γ : ℝ → ℂ,
        TauCeti.IsPiecewiseC1On γ 0 1 → γ 0 = γ₀ s →
        (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ D) →
        MonotoneOn (fun t => σ * (u * phase (γ t)).re) (Icc 0 1) →
        BoundedVariationOn (control ∘ γ) (Icc 0 1) →
        let V := (eVariationOn (control ∘ γ₀) (Ioc 0 s)).toReal +
          (eVariationOn (control ∘ γ) (Icc 0 1)).toReal
        ‖ε (γ 1)‖ ≤ Real.exp (V / ‖u‖) - 1 ∧
          ‖amplitude (γ 1) ^ 2 * deriv ε (γ 1) / u‖ ≤ Real.exp (V / ‖u‖) - 1 := by
  sorry

/-- Olver, Chapter 6, Theorem 12.1, pp. 223–224: the two opposite endpoint
errors share the same connection multiplier, and their normalized derivatives tend
to zero at both ends of a progressive path of finite total error variation. -/
theorem exists_complexLiouvilleGreen_connection_multiplier
    {D : Set ℂ} {f g amplitude phase control : ℂ → ℂ} {u : ℂ} {γ : ℝ → ℂ}
    (hD : IsOpen D) (hsc : IsSimplyConnected D) (hu : u ≠ 0)
    (hd : IsComplexLiouvilleGreenData f g amplitude phase control D)
    (hγ : ContinuousOn γ (Ioo 0 1))
    (hregular : ∀ a b : ℝ, 0 < a → a < b → b < 1 → TauCeti.IsPiecewiseC1On γ a b)
    (himage : ∀ t ∈ Ioo (0 : ℝ) 1, γ t ∈ D)
    (hprogressive : MonotoneOn (fun t => (u * phase (γ t)).re) (Ioo 0 1))
    (hleft : Tendsto (fun t => (u * phase (γ t)).re) (𝓝[>] 0) atBot)
    (hright : Tendsto (fun t => (u * phase (γ t)).re) (𝓝[<] 1) atTop)
    (hvariation : BoundedVariationOn (control ∘ γ) (Ioo 0 1)) :
    ∃ εPlus εMinus : ℂ → ℂ, ∃ C : ℂ,
      AnalyticOnNhd ℂ εPlus D ∧ AnalyticOnNhd ℂ εMinus D ∧
      (∀ σ : ℝ, σ = 1 ∨ σ = -1 → ∀ z ∈ D,
        let ε := if σ = 1 then εPlus else εMinus
        let w := fun t => amplitude t * exp (σ * u * phase t) * (1 + ε t)
        deriv (deriv w) z = (u ^ 2 * f z + g z) * w z) ∧
      Tendsto (εPlus ∘ γ) (𝓝[>] 0) (𝓝 0) ∧ Tendsto (εMinus ∘ γ) (𝓝[<] 1) (𝓝 0) ∧
      Tendsto (εPlus ∘ γ) (𝓝[<] 1) (𝓝 C) ∧ Tendsto (εMinus ∘ γ) (𝓝[>] 0) (𝓝 C) ∧
      Tendsto (fun t => amplitude (γ t) ^ 2 * deriv εPlus (γ t) / u)
        (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun t => amplitude (γ t) ^ 2 * deriv εPlus (γ t) / u)
        (𝓝[<] 1) (𝓝 0) ∧
      Tendsto (fun t => amplitude (γ t) ^ 2 * deriv εMinus (γ t) / u)
        (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun t => amplitude (γ t) ^ 2 * deriv εMinus (γ t) / u)
        (𝓝[<] 1) (𝓝 0) ∧
      ‖C‖ ≤ (Real.exp ((eVariationOn (control ∘ γ) (Ioo 0 1)).toReal / ‖u‖) - 1) / 2 := by
  sorry

end Complex
