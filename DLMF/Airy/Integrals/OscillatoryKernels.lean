/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Integrals.PrimitivesAndLaplace
public import DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Iterated oscillatory Airy integrals

Olver, *Asymptotics and Special Functions*, Chapter 9, §8, pp. 342–344:
iterated tails of `Ai(-t)`, their endpoint values and the asymptotic expansion for
an Airy-kernel integral. The decay exponent is the source's equation (8.02).
All tail integrals are ordinary limits of interval integrals, not Bochner integrals
over the entire half-line.
-/

@[expose] public section

open Filter Set DLMF.Core
open scoped Topology Real ContDiff

noncomputable section

namespace DLMF.Airy

/-- Olver, Chapter 9, §8.1, p. 342: `A₀(v)=Ai(-v)` and
`A_{n+1}(v)=∫_v^∞ A_n(t) dt`, with an ordinary oscillatory improper integral.
Existence of each limit is asserted separately. -/
def oscillatoryTail : ℕ → ℝ → ℂ
  | 0 => fun v => airyAi (-(v : ℂ))
  | n + 1 => fun v => improperAtTop (oscillatoryTail n) v

/-- The initial oscillatory kernel, Olver, Chapter 9, §8.1. -/
@[simp] theorem oscillatoryTail_zero (v : ℝ) :
    oscillatoryTail 0 v = airyAi (-(v : ℂ)) := rfl

/-- The iterated-tail equation, Olver, Chapter 9, §8.1, p. 342. -/
theorem oscillatoryTail_add_one (n : ℕ) (v : ℝ) :
    oscillatoryTail (n + 1) v = improperAtTop (oscillatoryTail n) v := rfl

/-- Olver, Chapter 9, §8.1, pp. 342–343: each iterated oscillatory tail exists
as an ordinary improper integral. -/
theorem hasIntegralAtTop_oscillatoryTail (n : ℕ) (v : ℝ) :
    HasIntegralAtTop (oscillatoryTail n) v (oscillatoryTail (n + 1) v) := by
  sorry

/-- Olver, Chapter 9, (8.02), p. 343: the `n`th oscillatory Airy tail has order
`v^(-n/2-1/4)` for `n≥1`. -/
theorem isBigO_oscillatoryTail (n : ℕ) (hn : 1 ≤ n) :
    oscillatoryTail n =O[atTop] (fun v : ℝ => v ^ (-(n : ℝ) / 2 - 1 / 4)) := by
  sorry

/-- Olver, Chapter 9, §8.2, p. 344: the endpoint values of the iterated Airy
tails, expressed with the reciprocal Gamma factor. -/
theorem oscillatoryTail_zero_arg (n : ℕ) (hn : 1 ≤ n) :
    oscillatoryTail n 0 =
      (2 * Real.cos (((n : ℝ) - 1) * Real.pi / 3) /
        (3 : ℝ) ^ (((n : ℝ) + 2) / 3) : ℝ) *
          (Complex.Gamma (((n : ℂ) + 2) / 3))⁻¹ := by
  sorry

/-- Olver, Chapter 9, §8.1, p. 343: the Airy-kernel integral is an ordinary
convergent improper integral under the source's derivative-growth assumptions. -/
theorem hasIntegralAtTop_airyAi_neg_mul {f : ℝ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Ici 0))
    (hderiv : ∀ n : ℕ, 1 ≤ n → ∃ δ : ℝ, 0 < δ ∧
      (fun v => iteratedDeriv n f v) =O[atTop]
        (fun v : ℝ => v ^ ((2 * (n : ℝ) - 3 - δ) / 4)))
    {x : ℝ} (hx : 0 < x) :
    HasIntegralAtTop (fun v => airyAi (-((x * v : ℝ) : ℂ)) * f v) 0
      (improperAtTop (fun v => airyAi (-((x * v : ℝ) : ℂ)) * f v) 0) := by
  sorry

/-- Olver, Chapter 9, §8.1, p. 343: the full expansion of an oscillatory
Airy-kernel integral. The growth bound is `v^((2n-3-δₙ)/4)` for each derivative
of positive order, as in the source. -/
theorem airyAi_neg_kernel_expansion {f : ℝ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Ici 0))
    (hderiv : ∀ n : ℕ, 1 ≤ n → ∃ δ : ℝ, 0 < δ ∧
      (fun v => iteratedDeriv n f v) =O[atTop]
        (fun v : ℝ => v ^ ((2 * (n : ℝ) - 3 - δ) / 4))) :
    Asymptotics.HasAsymptoticExpansion atTop
      (fun (n : ℕ) (v : ℝ) => ((v : ℂ) ^ (n + 1))⁻¹)
      (fun n => oscillatoryTail (n + 1) 0 * iteratedDerivWithin n f (Ici 0) 0)
      (fun x => improperAtTop (fun v => airyAi (-((x * v : ℝ) : ℂ)) * f v) 0) := by
  sorry

end DLMF.Airy
