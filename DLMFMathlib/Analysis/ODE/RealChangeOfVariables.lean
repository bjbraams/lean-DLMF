/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.Basic

/-!
# Real Liouville changes of variable and coordinate sensitivity

Olver, *Asymptotics and Special Functions*, Chapter 6, Theorem 1.1,
pp. 190–191, and Lemma 8.1, p. 214, synopsis O-6.01/O-6.11.
The Schwarzian is displayed in derivatives, avoiding a second definition of
an already existing operator. Real coordinates require only `C³` regularity.
-/

@[expose] public noncomputable section

open Set

namespace Real

/-- The real `C³` Schwarzian chain rule, with its complete explicit derivative formula.
Olver, Chapter 6, Theorem 1.1, synopsis O-6.01. -/
theorem schwarzian_quotient_comp {f g : ℝ → ℝ} {t : ℝ}
    (hf : ContDiffAt ℝ 3 f (g t)) (hg : ContDiffAt ℝ 3 g t)
    (hfg : deriv f (g t) ≠ 0) (hgt : deriv g t ≠ 0) :
    iteratedDeriv 3 (f ∘ g) t / deriv (f ∘ g) t -
        3 / 2 * (iteratedDeriv 2 (f ∘ g) t / deriv (f ∘ g) t) ^ 2 =
      deriv g t ^ 2 * (iteratedDeriv 3 f (g t) / deriv f (g t) -
        3 / 2 * (iteratedDeriv 2 f (g t) / deriv f (g t)) ^ 2) +
      (iteratedDeriv 3 g t / deriv g t -
        3 / 2 * (iteratedDeriv 2 g t / deriv g t) ^ 2) := by
  sorry

/-- The inverse-coordinate Liouville identity for a merely `C³` real coordinate.
The positive amplitude `|x'|^(-1/2)` also handles orientation reversal; it differs
from a fixed square-root choice only by a constant phase.
Olver, Chapter 6, Theorem 1.1, pp. 190–191, synopsis O-6.01. -/
theorem iteratedDeriv_liouville_inverse {x : ℝ → ℝ} {w f : ℝ → ℂ} {t : ℝ}
    (hx : ContDiffAt ℝ 3 x t) (hdx : deriv x t ≠ 0)
    (hw : ContDiffAt ℝ 2 w (x t)) (hode : iteratedDeriv 2 w (x t) = f (x t) * w (x t)) :
    let W := fun s : ℝ => ((|deriv x s| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * w (x s)
    iteratedDeriv 2 W t =
      (f (x t) * ((deriv x t : ℝ) : ℂ) ^ 2 -
        ((iteratedDeriv 3 x t / deriv x t -
          3 / 2 * (iteratedDeriv 2 x t / deriv x t) ^ 2 : ℝ) : ℂ) / 2) * W t := by
  sorry

/-- A bounded logarithmic derivative controls the multiplicative sensitivity of a
positive coordinate, including the stronger exponential bounds and the source's
rational bounds. Endpoints use within-interval derivatives.
Olver, Chapter 6, Lemma 8.1, p. 214, synopsis O-6.11. -/
theorem exp_mul_le_of_abs_logDeriv_le {X X' : ℝ → ℝ} {a b K s t : ℝ}
    (hX : ContinuousOn X (Icc a b))
    (hX' : ∀ x ∈ Icc a b, HasDerivWithinAt X (X' x) (Icc a b) x)
    (hpos : ∀ x ∈ Icc a b, 0 < X x) (hK : 0 ≤ K)
    (hbound : ∀ x ∈ Icc a b, |X' x / X x| ≤ K)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    exp (-K * |s - t|) * X t ≤ X s ∧ X s ≤ exp (K * |s - t|) * X t ∧
      (K * |s - t| < 1 →
        (1 - K * |s - t|) * X t ≤ X s ∧ X s ≤ X t / (1 - K * |s - t|)) := by
  sorry

end Real
