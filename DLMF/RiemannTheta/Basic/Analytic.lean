/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.RiemannTheta.Basic.Characteristics
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import Mathlib.Tactic

/-!
# Entire Riemann theta functions in several variables

For a fixed Riemann matrix, the theta functions, including those with real
characteristics, are entire on the full finite-dimensional complex argument space.
The proof combines the existing continuity and coordinate analyticity with TauCeti's
Osgood lemma, `ContinuousOn.analyticOnNhd_of_differentiableAt_update`.

References: Mumford, *Tata Lectures on Theta I*, Chapter II, §1;
Igusa, *Theta Functions*, Chapter II, §4.
-/

public noncomputable section

open Complex Matrix Set
open scoped Real

namespace DLMF.RiemannTheta

variable {ι : Type*} [Fintype ι]

/-- A Riemann theta function is jointly entire in its vector argument, including
when the index type is empty. -/
theorem analyticOnNhd_riemannTheta {Ω : Matrix ι ι ℂ}
    (hΩ : Ω ∈ siegelUpperHalfSpace ι) :
    AnalyticOnNhd ℂ (fun z => riemannTheta z Ω) univ := by
  classical
  have hc : ContinuousOn (fun z => riemannTheta z Ω) univ :=
    continuousOn_riemannTheta.comp (f := fun z : ι → ℂ => (z, Ω))
      (continuous_id.prodMk continuous_const).continuousOn (fun _ _ => hΩ)
  exact hc.analyticOnNhd_of_differentiableAt_update isOpen_univ
    (fun z _ j => differentiableAt_riemannTheta_update z hΩ j)

/-- The theta series is complex differentiable as a function of all argument coordinates. -/
theorem differentiable_riemannTheta {Ω : Matrix ι ι ℂ}
    (hΩ : Ω ∈ siegelUpperHalfSpace ι) :
    Differentiable ℂ (fun z => riemannTheta z Ω) :=
  fun z => (analyticOnNhd_riemannTheta hΩ z (mem_univ z)).differentiableAt

/-- Theta functions with arbitrary real characteristics are jointly entire in the argument. -/
theorem analyticOnNhd_riemannThetaChar (α β : ι → ℝ) {Ω : Matrix ι ι ℂ}
    (hΩ : Ω ∈ siegelUpperHalfSpace ι) :
    AnalyticOnNhd ℂ (fun z => riemannThetaChar α β z Ω) univ := by
  have heq : (fun z => riemannThetaChar α β z Ω) = fun z =>
      exp (2 * π * I * ((1 / 2 : ℂ) * ((fun i => (α i : ℂ)) ⬝ᵥ
        (Ω *ᵥ fun i => (α i : ℂ))) +
          (fun i => (α i : ℂ)) ⬝ᵥ (z + fun i => (β i : ℂ)))) *
        riemannTheta (z + Ω *ᵥ (fun i => (α i : ℂ)) + fun i => (β i : ℂ)) Ω :=
    funext fun z => riemannThetaChar_eq α β z hΩ.1
  rw [heq]
  apply AnalyticOnNhd.mul
  · intro z _hz
    simp only [dotProduct, Pi.add_apply]
    apply AnalyticAt.cexp
    apply analyticAt_const.mul
    apply analyticAt_const.add
    apply Finset.analyticAt_fun_sum
    intro i _hi
    exact analyticAt_const.mul
      (((ContinuousLinearMap.proj (R := ℂ) i).analyticAt z).add analyticAt_const)
  · intro z _hz
    exact (analyticOnNhd_riemannTheta hΩ _ (mem_univ _)).comp
      (f := fun w : ι → ℂ => w + Ω *ᵥ (fun i => (α i : ℂ)) + fun i => (β i : ℂ))
      ((analyticAt_id.add analyticAt_const).add analyticAt_const)

/-- Theta functions with real characteristics are complex differentiable in all coordinates. -/
theorem differentiable_riemannThetaChar (α β : ι → ℝ) {Ω : Matrix ι ι ℂ}
    (hΩ : Ω ∈ siegelUpperHalfSpace ι) :
    Differentiable ℂ (fun z => riemannThetaChar α β z Ω) :=
  fun z => (analyticOnNhd_riemannThetaChar α β hΩ z (mem_univ z)).differentiableAt

end DLMF.RiemannTheta
