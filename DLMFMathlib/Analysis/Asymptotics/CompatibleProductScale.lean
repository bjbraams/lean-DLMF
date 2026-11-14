/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion

/-!
# Products on compatible asymptotic scales

Olver, *Asymptotics and Special Functions*, Chapter 1, §10, pp. 24–26,
synopsis O-1.16. Multiplication is asserted only when the scale has the displayed
multiplicative compatibility; it is not an arbitrary-scale rule.
-/

@[expose] public section

open Filter Finset

namespace Asymptotics

/-- Cauchy multiplication on a multiplicatively compatible asymptotic scale.
Olver, Chapter 1, §10, synopsis O-1.16. -/
theorem HasAsymptoticExpansion.mul_of_compatible_scale {α K : Type*} [NormedField K]
    {l : Filter α} {φ : ℕ → α → K} {a b : ℕ → K} {f g : α → K}
    (hφ : IsAsymptoticScale l φ) (hzero : φ 0 =ᶠ[l] fun _ => 1)
    (hmul : ∀ i j, (fun x => φ i x * φ j x) =ᶠ[l] φ (i + j))
    (hf : HasAsymptoticExpansion l φ a f) (hg : HasAsymptoticExpansion l φ b g) :
    HasAsymptoticExpansion l φ
      (fun n => ∑ j ∈ range (n + 1), a j * b (n - j)) (fun x => f x * g x) := by
  sorry

end Asymptotics
