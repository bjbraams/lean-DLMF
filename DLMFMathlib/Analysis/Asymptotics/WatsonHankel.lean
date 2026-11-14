/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.WatsonConditional
public import Mathlib.Analysis.Analytic.Basic

/-!
# Watson's lemma for Hankel loops

Olver, *Asymptotics and Special Functions*, Chapter 4, Theorem 5.1, pp. 120–121.
The integrand is supplied on the logarithmic plane, so the upper and lower banks
of the negative cut remain correlated. A fixed-radius circular arc and the
ordinary improper integral of the cut jump define the Hankel transform.
-/

@[expose] public section

open Complex Filter Set MeasureTheory
open scoped Topology

noncomputable section

namespace Complex

/-- The normalized Hankel-loop Laplace transform of a logarithmic-plane
integrand `Q(w)=q(exp w)`, with circular radius `ρ`. The supplied `T` is the
ordinary Laplace transform of the shifted lower-bank-minus-upper-bank jump.
Olver, Chapter 4, §5.2 and Theorem 5.1. -/
def hankelLaplaceTransform (Q : ℂ → ℂ) (ρ : ℝ) (T : ℂ → ℂ) (z : ℂ) : ℂ :=
  (exp (-z * ρ) * T z + ∫ θ : ℝ in -Real.pi..Real.pi,
    exp (z * ρ * exp (θ * I)) * Q ((Real.log ρ : ℂ) + θ * I) *
      (I * ρ * exp (θ * I))) / (2 * Real.pi * I)

/-- The cut-jump and circular-arc formula for the Hankel Laplace transform,
Olver, Chapter 4, §5.2. -/
theorem hankelLaplaceTransform_def (Q : ℂ → ℂ) (ρ : ℝ) (T : ℂ → ℂ) (z : ℂ) :
    hankelLaplaceTransform Q ρ T z =
      (exp (-z * ρ) * T z + ∫ θ : ℝ in -Real.pi..Real.pi,
        exp (z * ρ * exp (θ * I)) * Q ((Real.log ρ : ℂ) + θ * I) *
          (I * ρ * exp (θ * I))) / (2 * Real.pi * I) := rfl

end Complex

namespace Asymptotics

/-- Olver, Chapter 4, Theorem 5.1, pp. 120–121: Watson's lemma on a Hankel
loop permits arbitrary complex `lam`; reciprocal-Gamma zeros cancel the corresponding
analytic powers. Both banks use the given logarithmic-plane integrand. -/
theorem watson_lemma_hankel {Q : ℂ → ℂ} {a : ℕ → ℂ} {lam : ℂ}
    {mu ρ c δ : ℝ} {S : Finset ℝ} {P : ℂ → ℝ → ℂ} {T : ℂ → ℂ}
    (hmu : 0 < mu) (hρ : 0 < ρ) (hδ : 0 < δ) (hδhalf : δ < Real.pi / 2)
    (hQanalytic : AnalyticOnNhd ℂ Q
      {w : ℂ | w.re ≤ Real.log ρ ∧ |w.im| ≤ Real.pi})
    (hT : ∀ z : ℂ, c < z.re →
      IsImproperLaplacePrimitive
        (fun t => Q ((Real.log (ρ + t) : ℂ) - Real.pi * I) -
          Q ((Real.log (ρ + t) : ℂ) + Real.pi * I)) z S (P z) ∧
        Tendsto (P z) atTop (𝓝 (T z)))
    (hQ : HasAsymptoticExpansion
      (Filter.comap (Prod.fst : ℝ × ℝ → ℝ) (𝓝[>] 0) ⊓
        𝓟 {p : ℝ × ℝ | |p.2| ≤ Real.pi})
      (fun (n : ℕ) (p : ℝ × ℝ) =>
        exp ((((n : ℂ) + lam) / mu - 1) * ((Real.log p.1 : ℂ) + p.2 * I)))
      a (fun p => Q ((Real.log p.1 : ℂ) + p.2 * I))) :
    HasAsymptoticExpansion
      (Filter.comap (fun z : ℂ => ‖z‖) atTop ⊓
        𝓟 {z : ℂ | |z.arg| ≤ Real.pi / 2 - δ})
      (fun (n : ℕ) (z : ℂ) => z ^ (-((n : ℂ) + lam) / mu))
      (fun n => a n / Gamma (1 - ((n : ℂ) + lam) / mu))
      (hankelLaplaceTransform Q ρ T) := by
  sorry

end Asymptotics
