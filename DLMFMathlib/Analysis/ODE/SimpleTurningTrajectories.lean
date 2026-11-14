/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.TurningPointCoordinates
public import DLMFMathlib.Analysis.ODE.ComplexLiouvilleGreen
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Principal trajectories from a simple analytic turning point

Olver, *Asymptotics and Special Functions*, Chapter 13, §11.1,
pp. 503–504, synopsis O-13.08. A principal trajectory is an actual regular
curve along which `f(z) dz²` is negative real. The local analytic Liouville
coordinate gives all three outgoing arcs, and maximal trajectories have no
crossings or regular interior endpoints.
-/

@[expose] public noncomputable section

open Set Complex Filter
open scoped Real Topology

namespace Complex.SimpleTurningPoint

/-- The three negative-cubic rays in the analytic Liouville coordinate. -/
def principalRay (j : Fin 3) : ℂ := exp (I * ((2 * (j : ℕ) + 1 : ℕ) : ℂ) * π / 3)

/-- The defining cyclic principal-ray directions. -/
theorem principalRay_def (j : Fin 3) :
    principalRay j = exp (I * ((2 * (j : ℕ) + 1 : ℕ) : ℂ) * π / 3) := rfl

/-- A regular real curve following the negative-real quadratic differential. -/
def IsPrincipalTrajectory (f : ℂ → ℂ) (D : Set ℂ) (γ : ℝ → ℂ) (J : Set ℝ) : Prop :=
  IsOpen J ∧ OrdConnected J ∧ ContDiffOn ℝ 1 γ J ∧
    ∀ t ∈ J, γ t ∈ D ∧ deriv γ t ≠ 0 ∧
      (f (γ t) * deriv γ t ^ 2).im = 0 ∧ (f (γ t) * deriv γ t ^ 2).re < 0

/-- The defining regularity and negative-real tangent conditions. -/
theorem isPrincipalTrajectory_iff (f : ℂ → ℂ) (D : Set ℂ) (γ : ℝ → ℂ) (J : Set ℝ) :
    IsPrincipalTrajectory f D γ J ↔ IsOpen J ∧ OrdConnected J ∧ ContDiffOn ℝ 1 γ J ∧
      ∀ t ∈ J, γ t ∈ D ∧ deriv γ t ≠ 0 ∧
        (f (γ t) * deriv γ t ^ 2).im = 0 ∧ (f (γ t) * deriv γ t ^ 2).re < 0 := Iff.rfl

/-- A connected principal-trajectory image, independent of parametrization. -/
def IsPrincipalTrajectoryImage (f : ℂ → ℂ) (D S : Set ℂ) : Prop :=
  ∃ (γ : ℝ → ℂ) (J : Set ℝ), IsPrincipalTrajectory f D γ J ∧ S = γ '' J

/-- The defining regular parametrization of a trajectory image. -/
theorem isPrincipalTrajectoryImage_iff (f : ℂ → ℂ) (D S : Set ℂ) :
    IsPrincipalTrajectoryImage f D S ↔
      ∃ (γ : ℝ → ℂ) (J : Set ℝ), IsPrincipalTrajectory f D γ J ∧ S = γ '' J := Iff.rfl

/-- A maximal connected principal trajectory in a punctured coefficient domain. -/
def IsMaximalPrincipalTrajectoryImage (f : ℂ → ℂ) (D S : Set ℂ) : Prop :=
  IsPrincipalTrajectoryImage f D S ∧
    ∀ T, IsPrincipalTrajectoryImage f D T → S ⊆ T → T = S

/-- The defining maximality property. -/
theorem isMaximalPrincipalTrajectoryImage_iff (f : ℂ → ℂ) (D S : Set ℂ) :
    IsMaximalPrincipalTrajectoryImage f D S ↔ IsPrincipalTrajectoryImage f D S ∧
      ∀ T, IsPrincipalTrajectoryImage f D T → S ⊆ T → T = S := Iff.rfl

/-- All three outgoing principal arcs in an actual analytic inverse coordinate. Their
initial directions differ by `2π/3`, and their quadratic-differential tangent values
are exactly `-t`, so no unspecified level curves are hidden in the conclusion.
Olver, Chapter 13, (11.05), synopsis O-13.08. -/
theorem exists_three_principal_arcs {f : ℂ → ℂ} {z₀ d : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hzero : f z₀ = 0) (hne : deriv f z₀ ≠ 0)
    (hd : d ^ 3 = deriv f z₀) :
    ∃ (r : ℝ) (ζ X : ℂ → ℂ), 0 < r ∧
      AnalyticOnNhd ℂ X (Metric.ball 0 r) ∧ X 0 = z₀ ∧
      InjOn X (Metric.ball 0 r) ∧ IsOpen (X '' Metric.ball 0 r) ∧
      AnalyticOnNhd ℂ ζ (X '' Metric.ball 0 r) ∧
      (∀ v ∈ Metric.ball (0 : ℂ) r, ζ (X v) = v ∧
        ζ (X v) * deriv ζ (X v) ^ 2 = f (X v)) ∧
      (∀ j : Fin 3,
        HasDerivAt (fun t : ℝ => X (t * principalRay j)) (principalRay j / d) 0 ∧
        (∀ t ∈ Ioo (0 : ℝ) r,
          f (X (t * principalRay j)) * deriv (fun s : ℝ => X (s * principalRay j)) t ^ 2 =
            -(t : ℂ))) ∧
      (∀ z ∈ X '' Metric.ball (0 : ℂ) r,
        ((ζ z ^ 3).im = 0 ∧ (ζ z ^ 3).re ≤ 0) ↔
          ∃ j : Fin 3, ∃ t ∈ Ico (0 : ℝ) r, z = X (t * principalRay j)) := by
  sorry

/-- Principal trajectories cannot cross themselves, and two maximal trajectories which
meet at an ordinary point coincide. Their only new interior accumulation endpoint is the
turning point. Olver, Chapter 13, §11.1, synopsis O-13.08. -/
theorem principal_trajectories_no_crossing {D : Set ℂ} (hD : IsOpen D)
    (hsc : IsSimplyConnected D) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f D)
    {z₀ : ℂ} (hz₀ : z₀ ∈ D) (hzero : f z₀ = 0) (hsimple : deriv f z₀ ≠ 0)
    (hne : ∀ z ∈ D, z ≠ z₀ → f z ≠ 0) :
    (∀ γ J, IsPrincipalTrajectory f (D \ {z₀}) γ J → InjOn γ J) ∧
      (∀ S T, IsMaximalPrincipalTrajectoryImage f (D \ {z₀}) S →
        IsMaximalPrincipalTrajectoryImage f (D \ {z₀}) T → (S ∩ T).Nonempty → S = T) ∧
      (∀ S, IsMaximalPrincipalTrajectoryImage f (D \ {z₀}) S →
        closure S ∩ D ⊆ S ∪ {z₀}) := by
  sorry

/-- The three outgoing maximal trajectories give actual simply connected cuts, the three
adjacent principal domains, and the normalized analytic branch amplitudes, phases and
control primitives. Other principal components away from the turning point may exist;
only the three incident domains are locally asserted to cover the cut complement.
Olver, Chapter 13, §11.1–11.2, pp. 503–505, synopsis O-13.08. -/
theorem exists_three_principal_branch_domains {D : Set ℂ} (hD : IsOpen D)
    (hsc : IsSimplyConnected D) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f D) (hg : AnalyticOnNhd ℂ g D)
    {z₀ : ℂ} (hz₀ : z₀ ∈ D) (hzero : f z₀ = 0) (hsimple : deriv f z₀ ≠ 0)
    (hne : ∀ z ∈ D, z ≠ z₀ → f z ≠ 0) :
    ∃ (C B P : Fin 3 → Set ℂ) (A Ξ F : Fin 3 → ℂ → ℂ) (κ : Fin 3 → ℂ),
      (∀ j, (C j).Nonempty ∧ IsMaximalPrincipalTrajectoryImage f (D \ {z₀}) (C j) ∧
        z₀ ∈ closure (C j) ∧ B j = D \ closure (C j) ∧ IsOpen (B j) ∧
        IsSimplyConnected (B j) ∧ IsOpen (P j) ∧ IsSimplyConnected (P j) ∧
        (P j).Nonempty ∧ z₀ ∈ closure (P j) ∧ κ j ≠ 0 ∧
        IsComplexLiouvilleGreenData f g (A j) (Ξ j) (F j) (B j) ∧
        Tendsto (Ξ j) (𝓝[B j] z₀) (𝓝 0)) ∧
      (∀ j k, j ≠ k → Disjoint (C j) (C k) ∧ Disjoint (P j) (P k)) ∧
      (∀ j k, P j ⊆ B k) ∧
      (∃ r : ℝ, 0 < r ∧ Metric.ball z₀ r ⊆ D ∧
        Metric.ball z₀ r \ (⋃ j, closure (C j)) ⊆ ⋃ j, P j) ∧
      (∀ j z, z ∈ P j → 0 < (Ξ j z).re ∧
        Ξ (j + 1) z = -Ξ j z ∧ Ξ (j + 2) z = -Ξ j z ∧
        κ (j + 1) * A (j + 1) z = exp (π * I / 6) * (κ j * A j z) ∧
        κ (j + 2) * A (j + 2) z = exp (-π * I / 6) * (κ j * A j z)) := by
  sorry

end Complex.SimpleTurningPoint
