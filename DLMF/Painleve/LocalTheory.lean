/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Painleve.Basic
public import Mathlib.Analysis.ODE.ExistUnique

/-!
# Local real solutions of Painlevé II

Mathlib's Picard–Lindelöf and local Lipschitz theorems apply to the autonomous
system `(x,u,v)' = (1,v,2u³+xu-c)`. This gives actual local real solutions and
uniqueness of germs at every initial value, as used in Beals–Wong §15.3.
This file does not assert complex analytic or global meromorphic continuation.
-/

@[expose] public noncomputable section

open Set Filter Metric
open scoped Topology

namespace DLMF.Painleve

/-- The autonomous three-dimensional vector field for real Painlevé II. -/
def piiVectorField (c : ℝ) (y : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (1, y.2.2, 2 * y.2.1 ^ 3 + y.1 * y.2.1 - c)

/-- Painlevé II has a continuously differentiable polynomial vector field. -/
theorem contDiff_piiVectorField (c : ℝ) : ContDiff ℝ 1 (piiVectorField c) := by
  unfold piiVectorField
  fun_prop

/-- Every real initial pair determines a local real Painlevé II solution. -/
theorem exists_local_real_solution (c x₀ u₀ v₀ : ℝ) :
    ∃ ε > 0, ∃ u : ℝ → ℝ, IsPIIOn c u (Ioo (x₀ - ε) (x₀ + ε)) ∧
      u x₀ = u₀ ∧ deriv u x₀ = v₀ := by
  obtain ⟨γ, hγ₀, ε, hε, hγ⟩ :=
    (contDiff_piiVectorField c).contDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
      (x₀ := (x₀, u₀, v₀)) x₀
  have hx₀ : x₀ ∈ Ioo (x₀ - ε) (x₀ + ε) := ⟨by linarith, by linarith⟩
  have hfst (x : ℝ) (hx : x ∈ Ioo (x₀ - ε) (x₀ + ε)) :
      HasDerivAt (fun t => (γ t).1) 1 x := (hγ x hx).fst
  have htime : EqOn (fun x => (γ x).1) id (Ioo (x₀ - ε) (x₀ + ε)) := by
    apply isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo _ _).isPreconnected
      (fun x hx => (hfst x hx).differentiableAt.differentiableWithinAt) differentiableOn_id
      (fun x hx => by rw [(hfst x hx).deriv, deriv_id]) hx₀
    simpa using congrArg Prod.fst hγ₀
  have hu (x : ℝ) (hx : x ∈ Ioo (x₀ - ε) (x₀ + ε)) :
      HasDerivAt (fun t => (γ t).2.1) (γ x).2.2 x := (hγ x hx).snd.fst
  have hv (x : ℝ) (hx : x ∈ Ioo (x₀ - ε) (x₀ + ε)) :
      HasDerivAt (fun t => (γ t).2.2) (2 * (γ x).2.1 ^ 3 + x * (γ x).2.1 - c) x := by
    have hd : HasDerivAt (fun t => (γ t).2.2) ((piiVectorField c (γ x)).2.2) x :=
      (hγ x hx).snd.snd
    exact hd.congr_deriv (by dsimp only [piiVectorField]; rw [show (γ x).1 = x from htime hx])
  refine ⟨ε, hε, fun t => (γ t).2.1, isPIIOn_of_hasDerivAt isOpen_Ioo hu hv, ?_, ?_⟩
  · simpa using congrArg (fun y : ℝ × ℝ × ℝ => y.2.1) hγ₀
  · rw [(hu x₀ hx₀).deriv]
    simpa using congrArg (fun y : ℝ × ℝ × ℝ => y.2.2) hγ₀

/-- Solutions with the same initial value and derivative agree in a neighborhood,
the local uniqueness assertion for Painlevé II. -/
theorem IsPIIOn.eventuallyEq_real {c x₀ : ℝ} {u v : ℝ → ℝ} {s : Set ℝ}
    (hu : IsPIIOn c u s) (hv : IsPIIOn c v s) (hs : s ∈ 𝓝 x₀)
    (h₀ : u x₀ = v x₀) (h₁ : deriv u x₀ = deriv v x₀) : u =ᶠ[𝓝 x₀] v := by
  let U (x : ℝ) : ℝ × ℝ × ℝ := (x, u x, deriv u x)
  let V (x : ℝ) : ℝ × ℝ × ℝ := (x, v x, deriv v x)
  have hU (x : ℝ) (hx : x ∈ s) : HasDerivAt U (piiVectorField c (U x)) x :=
    (hasDerivAt_id x).prodMk ((hu.hasDerivAt hx).prodMk (hu.hasDerivAt_deriv x hx))
  have hV (x : ℝ) (hx : x ∈ s) : HasDerivAt V (piiVectorField c (V x)) x :=
    (hasDerivAt_id x).prodMk ((hv.hasDerivAt hx).prodMk (hv.hasDerivAt_deriv x hx))
  have hx₀ : x₀ ∈ s := mem_of_mem_nhds hs
  obtain ⟨K, t, ht, hK⟩ := (contDiff_piiVectorField c).contDiffAt.exists_lipschitzOnWith
    (x := U x₀)
  have hUV : U x₀ = V x₀ := by dsimp [U, V]; rw [h₀, h₁]
  have hUt : ∀ᶠ x in 𝓝 x₀, U x ∈ t := (hU x₀ hx₀).continuousAt.eventually ht
  have hVt : ∀ᶠ x in 𝓝 x₀, V x ∈ t :=
    (hV x₀ hx₀).continuousAt.eventually (by rwa [← hUV])
  have he := ODE_solution_unique_of_eventually (v := fun _ => piiVectorField c)
    (s := fun _ => t) (Eventually.of_forall fun _ => hK)
    (by filter_upwards [hs, hUt] with x hx hxt using ⟨hU x hx, hxt⟩)
    (by filter_upwards [hs, hVt] with x hx hxt using ⟨hV x hx, hxt⟩) hUV
  filter_upwards [he] with x hx using congrArg (fun y : ℝ × ℝ × ℝ => y.2.1) hx

end DLMF.Painleve
