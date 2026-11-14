/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Integral.ConditionalLaplace
public import DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Watson's lemma with conditionally convergent tails

Olver, *Asymptotics and Special Functions*, Chapter 3, Theorem 3.1, pp. 71–72,
and Chapter 4, Theorem 3.2, p. 113. Normalized primitives specify all ordinary
improper integrals, including finitely many improper interior points. Absolute
convergence of the original Laplace tail is not assumed.
-/

@[expose] public section

open Filter Set Complex MeasureTheory
open scoped Topology

noncomputable section

namespace Asymptotics

/-- Olver, Chapter 3, Theorem 3.1, and Chapter 4, Theorem 3.2: Watson's expansion
on the positive real axis with an ordinarily convergent, possibly conditional tail.
The parameter `lam` may be complex with positive real part. -/
theorem watson_lemma_conditional {q : ℝ → ℂ} {a : ℕ → ℂ} {lam : ℂ} {mu c : ℝ}
    {S : Finset ℝ} {P : ℂ → ℝ → ℂ} {F : ℂ → ℂ}
    (hlam : 0 < lam.re) (hmu : 0 < mu)
    (hF : ∀ z : ℂ, c < z.re → IsImproperLaplacePrimitive q z S (P z) ∧
      Tendsto (P z) atTop (𝓝 (F z)))
    (hq : HasAsymptoticExpansion (𝓝[>] 0)
      (fun (n : ℕ) (t : ℝ) => (t : ℂ) ^ (((n : ℂ) + lam) / mu - 1)) a q) :
    HasAsymptoticExpansion atTop
      (fun (n : ℕ) (x : ℝ) => (x : ℂ) ^ (-((n : ℂ) + lam) / mu))
      (fun n => Gamma (((n : ℂ) + lam) / mu) * a n) (fun x : ℝ => F x) := by
  sorry

/-- Olver, Chapter 4, Theorem 3.2, p. 113: the same conditionally convergent
Watson expansion is uniform on every closed proper subsector of the right half-plane. -/
theorem watson_lemma_sector_conditional {q : ℝ → ℂ} {a : ℕ → ℂ}
    {lam : ℂ} {mu c δ : ℝ} {S : Finset ℝ} {P : ℂ → ℝ → ℂ} {F : ℂ → ℂ}
    (hlam : 0 < lam.re) (hmu : 0 < mu) (hδ : 0 < δ) (hδhalf : δ < Real.pi / 2)
    (hF : ∀ z : ℂ, c < z.re → IsImproperLaplacePrimitive q z S (P z) ∧
      Tendsto (P z) atTop (𝓝 (F z)))
    (hq : HasAsymptoticExpansion (𝓝[>] 0)
      (fun (n : ℕ) (t : ℝ) => (t : ℂ) ^ (((n : ℂ) + lam) / mu - 1)) a q) :
    HasAsymptoticExpansion
      (Filter.comap (fun z : ℂ => ‖z‖) atTop ⊓
        𝓟 {z : ℂ | |z.arg| ≤ Real.pi / 2 - δ})
      (fun (n : ℕ) (z : ℂ) => z ^ (-((n : ℂ) + lam) / mu))
      (fun n => Gamma (((n : ℂ) + lam) / mu) * a n) F := by
  sorry

end Asymptotics
