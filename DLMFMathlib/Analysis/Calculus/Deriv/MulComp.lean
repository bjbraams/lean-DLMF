/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Second derivative of a product with composed analytic factors

For `P`, `u`, `v` with first derivatives near `z` and second derivatives at `z`, and `F`, `G`
analytic at `u z`, `v z`, the first and second derivatives of `x ↦ P x * F (u x) * G (v x)` at
`z` are given by the product and chain rules.

## Main results

* `deriv_deriv_mul_comp_mul_comp`: the first and second derivatives of
  `x ↦ P x * F (u x) * G (v x)`.
-/

@[expose] public section

open Filter
open scoped Topology

/-- First and second derivatives of `x ↦ P x * F (u x) * G (v x)` for `F`, `G` analytic, in terms
of the first and second derivatives of `P`, `u` and `v`. -/
theorem deriv_deriv_mul_comp_mul_comp {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {P u v F G P1 u1 v1 : 𝕜 → 𝕜} {P2 u2 v2 z : 𝕜}
    (hP : ∀ᶠ x in 𝓝 z, HasDerivAt P (P1 x) x) (hP1 : HasDerivAt P1 P2 z)
    (hu : ∀ᶠ x in 𝓝 z, HasDerivAt u (u1 x) x) (hu1 : HasDerivAt u1 u2 z)
    (hv : ∀ᶠ x in 𝓝 z, HasDerivAt v (v1 x) x) (hv1 : HasDerivAt v1 v2 z)
    (hF : AnalyticAt 𝕜 F (u z)) (hG : AnalyticAt 𝕜 G (v z)) :
    deriv (fun x => P x * F (u x) * G (v x)) z =
        P1 z * F (u z) * G (v z) + P z * u1 z * deriv F (u z) * G (v z) +
          P z * F (u z) * v1 z * deriv G (v z) ∧
    deriv (deriv (fun x => P x * F (u x) * G (v x))) z =
        P2 * F (u z) * G (v z) + 2 * P1 z * u1 z * deriv F (u z) * G (v z) +
          2 * P1 z * F (u z) * v1 z * deriv G (v z) +
          P z * (u2 * deriv F (u z) + u1 z ^ 2 * deriv (deriv F) (u z)) * G (v z) +
          2 * P z * u1 z * v1 z * deriv F (u z) * deriv G (v z) +
          P z * F (u z) * (v2 * deriv G (v z) + v1 z ^ 2 * deriv (deriv G) (v z)) := by
  have hFe : ∀ᶠ x in 𝓝 z, AnalyticAt 𝕜 F (u x) :=
    hu.self_of_nhds.continuousAt.tendsto.eventually hF.eventually_analyticAt
  have hGe : ∀ᶠ x in 𝓝 z, AnalyticAt 𝕜 G (v x) :=
    hv.self_of_nhds.continuousAt.tendsto.eventually hG.eventually_analyticAt
  have hK : ∀ᶠ x in 𝓝 z, HasDerivAt (fun x => P x * F (u x) * G (v x))
      (P1 x * F (u x) * G (v x) + P x * u1 x * deriv F (u x) * G (v x) +
          P x * F (u x) * v1 x * deriv G (v x)) x := by
    filter_upwards [hP, hu, hv, hFe, hGe] with x hPx hux hvx hFx hGx
    exact ((hPx.mul (hFx.differentiableAt.hasDerivAt.comp x hux)).mul
      (hGx.differentiableAt.hasDerivAt.comp x hvx)).congr_deriv (by
        simp only [Pi.mul_apply, Function.comp_apply]
        ring)
  refine ⟨hK.self_of_nhds.deriv, ?_⟩
  have hev : deriv (fun x => P x * F (u x) * G (v x)) =ᶠ[𝓝 z] fun x =>
      P1 x * F (u x) * G (v x) + P x * u1 x * deriv F (u x) * G (v x) +
        P x * F (u x) * v1 x * deriv G (v x) := hK.mono fun x hx => hx.deriv
  rw [hev.deriv_eq]
  have h1 := hF.deriv.differentiableAt.hasDerivAt.comp z hu.self_of_nhds
  have h2 := hG.deriv.differentiableAt.hasDerivAt.comp z hv.self_of_nhds
  have h3 := hF.differentiableAt.hasDerivAt.comp z hu.self_of_nhds
  have h4 := hG.differentiableAt.hasDerivAt.comp z hv.self_of_nhds
  have hP0 := hP.self_of_nhds
  refine HasDerivAt.deriv ?_
  exact (HasDerivAt.add (HasDerivAt.add ((hP1.mul h3).mul h4) (((hP0.mul hu1).mul h1).mul h4))
    (((hP0.mul h3).mul hv1).mul h2)).congr_deriv (by
      simp only [Pi.mul_apply, Function.comp_apply]
      ring)
