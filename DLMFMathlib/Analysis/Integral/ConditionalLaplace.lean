/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Integral.LaplaceDomain
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Conditional convergence of Laplace integrals

Olver, *Asymptotics and Special Functions*, Chapter 4, Theorem 3.1, p. 112.
A continuous normalized primitive specifies the ordinary improper integral across
finitely many exceptional points. This distinguishes convergence from Bochner
integrability and retains separate abscissae of convergence and absolute convergence.
-/

@[expose] public section

open Filter Set Complex
open scoped Topology

noncomputable section

namespace MeasureTheory

/-- A normalized primitive of `exp(-zt)q(t)` on the positive half-line, with
ordinary removable limiting values at the finitely many exceptional points `S`.
Olver, Chapter 4, §3, p. 112. Its limit at infinity, when it exists, is the
ordinary improper Laplace integral, including conditional convergence. -/
def IsImproperLaplacePrimitive (q : ℝ → ℂ) (z : ℂ) (S : Finset ℝ) (P : ℝ → ℂ) : Prop :=
  ContinuousOn P (Ici 0) ∧ P 0 = 0 ∧
    ∀ t : ℝ, 0 < t → t ∉ S → HasDerivAt P (exp (-z * t) * q t) t

/-- The defining conditions for a normalized improper Laplace primitive,
Olver, Chapter 4, §3. -/
theorem isImproperLaplacePrimitive_iff (q : ℝ → ℂ) (z : ℂ) (S : Finset ℝ) (P : ℝ → ℂ) :
    IsImproperLaplacePrimitive q z S P ↔ ContinuousOn P (Ici 0) ∧ P 0 = 0 ∧
      ∀ t : ℝ, 0 < t → t ∉ S → HasDerivAt P (exp (-z * t) * q t) t := Iff.rfl

/-- Introduction of the normalized improper primitive, Olver, Chapter 4, §3. -/
theorem IsImproperLaplacePrimitive.mk {q : ℝ → ℂ} {z : ℂ} {S : Finset ℝ} {P : ℝ → ℂ}
    (hP : ContinuousOn P (Ici 0)) (hzero : P 0 = 0)
    (hderiv : ∀ t : ℝ, 0 < t → t ∉ S → HasDerivAt P (exp (-z * t) * q t) t) :
    IsImproperLaplacePrimitive q z S P := ⟨hP, hzero, hderiv⟩

/-- A normalized improper primitive is continuous at all limiting improper
points, Olver, Chapter 4, §3. -/
theorem IsImproperLaplacePrimitive.continuousOn {q : ℝ → ℂ} {z : ℂ}
    {S : Finset ℝ} {P : ℝ → ℂ} (hP : IsImproperLaplacePrimitive q z S P) :
    ContinuousOn P (Ici 0) := hP.1

/-- The normalized primitive has the damped amplitude as derivative away from
the exceptional points, Olver, Chapter 4, §3. -/
theorem IsImproperLaplacePrimitive.hasDerivAt {q : ℝ → ℂ} {z : ℂ}
    {S : Finset ℝ} {P : ℝ → ℂ} (hP : IsImproperLaplacePrimitive q z S P)
    {t : ℝ} (ht : 0 < t) (htS : t ∉ S) : HasDerivAt P (exp (-z * t) * q t) t :=
  hP.2.2 t ht htS

/-- Normalized primitives agree, so their convergent improper integrals are
independent of the primitive choice. Olver, Chapter 4, §3. -/
theorem IsImproperLaplacePrimitive.eqOn {q : ℝ → ℂ} {z : ℂ} {S : Finset ℝ}
    {P Q : ℝ → ℂ} (hP : IsImproperLaplacePrimitive q z S P)
    (hQ : IsImproperLaplacePrimitive q z S Q) : EqOn P Q (Ici 0) := by
  sorry

/-- Olver, Chapter 4, Theorem 3.1, p. 112: convergence at one complex damping
parameter implies ordinary convergence throughout the open half-plane to its right. -/
theorem exists_improperLaplace_of_re_lt {q : ℝ → ℂ} {z₀ z : ℂ} {S : Finset ℝ}
    {P₀ : ℝ → ℂ} {L₀ : ℂ} (hP₀ : IsImproperLaplacePrimitive q z₀ S P₀)
    (hL₀ : Tendsto P₀ atTop (𝓝 L₀)) (hz : z₀.re < z.re) :
    ∃ P : ℝ → ℂ, ∃ L : ℂ, IsImproperLaplacePrimitive q z S P ∧
      Tendsto P atTop (𝓝 L) := by
  sorry

/-- Olver, Chapter 4, §3: the extended-real abscissa of ordinary, potentially
conditional, Laplace convergence for a finite exceptional set. -/
def laplaceConvergenceAbscissa (q : ℝ → ℂ) (S : Finset ℝ) : EReal :=
  sInf ((fun x : ℝ => (x : EReal)) '' {x : ℝ | ∃ P : ℝ → ℂ, ∃ L : ℂ,
    IsImproperLaplacePrimitive q x S P ∧ Tendsto P atTop (𝓝 L)})

/-- The infimum formula for the conditional convergence abscissa,
Olver, Chapter 4, §3. -/
theorem laplaceConvergenceAbscissa_def (q : ℝ → ℂ) (S : Finset ℝ) :
    laplaceConvergenceAbscissa q S =
      sInf ((fun x : ℝ => (x : EReal)) '' {x : ℝ | ∃ P : ℝ → ℂ, ∃ L : ℂ,
        IsImproperLaplacePrimitive q x S P ∧ Tendsto P atTop (𝓝 L)}) := rfl

/-- Olver, Chapter 4, §3: ordinary convergence occurs strictly to the right of
its abscissa, including when that abscissa is negative infinity. -/
theorem exists_improperLaplace_of_abscissa_lt {q : ℝ → ℂ} {S : Finset ℝ} {z : ℂ}
    (hz : laplaceConvergenceAbscissa q S < (z.re : EReal)) :
    ∃ P : ℝ → ℂ, ∃ L : ℂ, IsImproperLaplacePrimitive q z S P ∧
      Tendsto P atTop (𝓝 L) := by
  sorry

/-- Olver, Chapter 4, §3: the abscissa of conditional convergence is no larger
than the absolute-convergence abscissa. Continuity is required only off the finite
exceptional set. -/
theorem laplaceConvergenceAbscissa_le_laplaceAbscissa {q : ℝ → ℂ} {S : Finset ℝ}
    (hq : ∀ t : ℝ, 0 < t → t ∉ S → ContinuousAt q t) :
    laplaceConvergenceAbscissa q S ≤ laplaceAbscissa q := by
  sorry

/-- A strict distinction between the two Laplace abscissae: for
`q(t)=exp(t) sin(exp(t))`, ordinary convergence begins at real damping `x>0`,
whereas absolute convergence requires `x>1`. This exemplifies Olver, Chapter 4,
§3's distinction between the two abscissae. -/
theorem improperLaplace_exp_mul_sin_exp_iff (x : ℝ) :
    (∃ P : ℝ → ℂ, ∃ L : ℂ,
      IsImproperLaplacePrimitive (fun t => (Real.exp t * Real.sin (Real.exp t) : ℝ))
        x ∅ P ∧ Tendsto P atTop (𝓝 L)) ↔ 0 < x := by
  sorry

/-- Absolute convergence in the example distinguishing the two abscissae,
Olver, Chapter 4, §3. -/
theorem integrableOn_exp_mul_sin_exp_iff (x : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-x * t) *
      (Real.exp t * Real.sin (Real.exp t))) (Ioi 0) ↔ 1 < x := by
  sorry

end MeasureTheory
