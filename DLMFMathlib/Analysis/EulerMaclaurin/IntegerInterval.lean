/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.EulerMaclaurin
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Euler–Maclaurin on arbitrary integer intervals

Andrews, Askey and Roy, *Special Functions*, Theorem D.2.1, pp. 617–620
(synopsis AAR-D.2.1–D.3.2). Differentiability is required only on the closed
integration interval. Within derivatives give the appropriate one-sided values
at its endpoints, without assumptions on the function outside the interval.
-/

@[expose] public noncomputable section

open MeasureTheory Finset

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Euler–Maclaurin summation over the integer interval `(m,n]`, with the exact
periodic-Bernoulli remainder. Andrews–Askey–Roy, *Special Functions*,
Theorem D.2.1, pp. 617–620 (synopsis AAR-D.2.1–D.3.2). The convention is `B₁=-1/2`. -/
theorem sum_Ioc_eq_integral_add_bernoulli {m n : ℤ} (hmn : m < n)
    {s : ℕ} (hs : 1 ≤ s) {f : ℝ → E}
    (hf : ContDiffOn ℝ s f (Set.Icc (m : ℝ) (n : ℝ))) :
    let I := Set.Icc (m : ℝ) (n : ℝ)
    (∑ k ∈ Ioc m n, f k) = (∫ t : ℝ in (m : ℝ)..(n : ℝ), f t) +
      (∑ j ∈ Icc 1 s, ((-1 : ℝ) ^ j * (bernoulli j : ℝ) / j.factorial) •
        (iteratedDerivWithin (j - 1) f I n - iteratedDerivWithin (j - 1) f I m)) +
      ((-1 : ℝ) ^ (s + 1) / s.factorial) •
        ∫ t : ℝ in (m : ℝ)..(n : ℝ),
          periodicBernoulli s t • iteratedDerivWithin s f I t := by
  sorry

/-- The Euler–Maclaurin remainder is bounded by the periodic Bernoulli supremum times
the `L¹` norm of the highest derivative, divided by `s!`. Andrews–Askey–Roy,
*Special Functions*, Theorem D.2.1, pp. 617–620
(synopsis AAR-D.2.1–D.3.2). The periodic function is bounded, so its real supremum
is the ordinary finite supremum. -/
theorem norm_sum_Ioc_sub_integral_sub_bernoulli_le {m n : ℤ} (hmn : m < n)
    {s : ℕ} (hs : 1 ≤ s) {f : ℝ → E}
    (hf : ContDiffOn ℝ s f (Set.Icc (m : ℝ) (n : ℝ))) :
    let I := Set.Icc (m : ℝ) (n : ℝ)
    ‖(∑ k ∈ Ioc m n, f k) - (∫ t : ℝ in (m : ℝ)..(n : ℝ), f t) -
      ∑ j ∈ Icc 1 s, ((-1 : ℝ) ^ j * (bernoulli j : ℝ) / j.factorial) •
        (iteratedDerivWithin (j - 1) f I n - iteratedDerivWithin (j - 1) f I m)‖ ≤
      sSup (Set.range fun t : ℝ => |periodicBernoulli s t|) / s.factorial *
        ∫ t : ℝ in (m : ℝ)..(n : ℝ), ‖iteratedDerivWithin s f I t‖ := by
  sorry
