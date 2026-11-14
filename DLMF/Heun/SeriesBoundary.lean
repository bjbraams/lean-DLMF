/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Heun.LocalSolutions
public import DLMFMathlib.Analysis.SpecificLimits.SecondOrderRecurrence

/-!
# Boundary convergence and minimal Heun coefficient sequences

Kristensson, *Second Order Differential Equations*, Chapter 8, Theorem 8.1 and
(8.6)–(8.7), pp. 144–146. The normalized recurrence has characteristic roots
`1` and `1/A`. A minimal nonterminating coefficient sequence has radius `abs(A)`;
this larger radius is not attributed to an arbitrary local solution. Convergence
at the corresponding boundary retains the real-part hypothesis on its exponent.
-/

@[expose] public noncomputable section

open Complex Filter
open scoped Topology

namespace DLMF.Heun

/-- The first normalized Heun recurrence coefficient tends to `1+1/A`.
Kristensson, Chapter 8, (8.6), pp. 144–146. -/
theorem tendsto_heunRecurrenceQ_add_div_R {A : ℂ} (hA : A ≠ 0)
    (q α β c d : ℂ) :
    Tendsto (fun n : ℕ =>
      (heunRecurrenceQ A α β c d n + q) / heunRecurrenceR A c n)
      atTop (𝓝 (1 + A⁻¹)) := by
  sorry

/-- The second normalized Heun recurrence coefficient tends to `-1/A`.
Kristensson, Chapter 8, (8.6), pp. 144–146. -/
theorem tendsto_neg_heunRecurrenceP_div_R {A : ℂ} (hA : A ≠ 0) (α β c : ℂ) :
    Tendsto (fun n : ℕ => -heunRecurrenceP α β n / heunRecurrenceR A c n)
      atTop (𝓝 (-A⁻¹)) := by
  sorry

/-- The nonterminating canonical sequence has one of the two characteristic ratio
limits. The denominators are eventually nonzero; no headed continued-fraction
convergence is used as a substitute for minimality. Kristensson, Chapter 8,
(8.6)–(8.7), pp. 144–146. -/
theorem exists_heunLocalCoeff_ratio_limit {A q α β c d : ℂ} (hA : 1 < ‖A‖)
    (hc : ∀ n : ℕ, c ≠ -(n : ℂ))
    (hnonterminating : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ heunLocalCoeff A q α β c d n ≠ 0) :
    ∃ ρ : ℂ, (ρ = 1 ∨ ρ = A⁻¹) ∧
      (∀ᶠ n : ℕ in atTop, heunLocalCoeff A q α β c d n ≠ 0) ∧
      Tendsto (fun n : ℕ =>
        heunLocalCoeff A q α β c d (n + 1) / heunLocalCoeff A q α β c d n)
        atTop (𝓝 ρ) := by
  sorry

/-- The ordinary local Heun series is absolutely convergent on the unit circle
when the exponent at one has real part below one. Kristensson, Chapter 8,
Theorem 8.1, p. 145. Interior convergence is included. -/
theorem summable_heunLocalCoeff_of_norm_le_one {A q α β c d z : ℂ}
    (hA : 1 < ‖A‖) (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) (hd : d.re < 1)
    (hz : ‖z‖ ≤ 1) :
    Summable (fun n : ℕ => heunLocalCoeff A q α β c d n * z ^ n) := by
  sorry

/-- The exact radius of a minimal nonterminating Heun coefficient sequence is
`abs(A)`. Kristensson, Chapter 8, Theorem 8.1 and (8.6)–(8.7), pp. 144–146.
The ratio hypothesis is part of the assertion and is not inferred from arbitrary
continued-fraction convergence. -/
theorem radius_heunLocalCoeff_of_minimal {A q α β c d : ℂ}
    (hA : 1 < ‖A‖) (hc : ∀ n : ℕ, c ≠ -(n : ℂ))
    (hminimal : Tendsto (fun n : ℕ =>
      heunLocalCoeff A q α β c d (n + 1) / heunLocalCoeff A q α β c d n)
      atTop (𝓝 A⁻¹)) :
    (FormalMultilinearSeries.ofScalars ℂ (heunLocalCoeff A q α β c d)).radius =
      ENNReal.ofReal ‖A‖ := by
  sorry

/-- The minimal Heun series converges absolutely on its larger boundary circle
when the exponent at `A` has real part below one. Kristensson, Chapter 8,
Theorem 8.1, p. 145. The exponent is the canonical balanced `heunEpsilon`. -/
theorem summable_heunLocalCoeff_of_minimal_of_norm_le {A q α β c d z : ℂ}
    (hA : 1 < ‖A‖) (hc : ∀ n : ℕ, c ≠ -(n : ℂ))
    (hminimal : Tendsto (fun n : ℕ =>
      heunLocalCoeff A q α β c d (n + 1) / heunLocalCoeff A q α β c d n)
      atTop (𝓝 A⁻¹))
    (he : (heunEpsilon α β c d).re < 1) (hz : ‖z‖ ≤ ‖A‖) :
    Summable (fun n : ℕ => heunLocalCoeff A q α β c d n * z ^ n) := by
  sorry

end DLMF.Heun
