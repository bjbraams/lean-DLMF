/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ContinuedFraction.Convergence

/-!
# Monotonicity and bracketing for positive generalized continued fractions

Temme, *Special Functions* (1996), §13.5, pp. 347–348, synopsis TEM-13-12.
`ofFun h a b` uses zero-based partial numerators and denominators after the head `h`.
Positivity gives two one-sided limits, which are not asserted to be equal.
The continuant recurrence and determinant formula are reused from
`DLMFMathlib.Analysis.ContinuedFraction.Convergence`.
-/

@[expose] public noncomputable section
open Filter
open scoped Topology
namespace GenContFract

/-- Even convergents increase strictly, Temme §13.5, synopsis TEM-13-12. -/
theorem strictMono_ofFun_convs_even (h : ℝ) {a b : ℕ → ℝ}
    (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n) :
    StrictMono (fun n : ℕ => (ofFun h a b).convs (2 * n)) := by
  sorry

/-- Odd convergents decrease strictly, Temme §13.5, synopsis TEM-13-12. -/
theorem strictAnti_ofFun_convs_odd (h : ℝ) {a b : ℕ → ℝ}
    (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n) :
    StrictAnti (fun n : ℕ => (ofFun h a b).convs (2 * n + 1)) := by
  sorry

/-- Every even convergent precedes every odd convergent,
Temme §13.5, synopsis TEM-13-12. -/
theorem ofFun_convs_even_lt_odd (h : ℝ) {a b : ℕ → ℝ}
    (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n) (m n : ℕ) :
    (ofFun h a b).convs (2 * m) < (ofFun h a b).convs (2 * n + 1) := by
  sorry

/-- The even and odd subsequences have ordered limits, which need not coincide,
Temme §13.5, synopsis TEM-13-12. -/
theorem exists_tendsto_ofFun_convs_even_odd (h : ℝ) {a b : ℕ → ℝ}
    (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n) :
    ∃ L U : ℝ, L ≤ U ∧
      Tendsto (fun n : ℕ => (ofFun h a b).convs (2 * n)) atTop (𝓝 L) ∧
      Tendsto (fun n : ℕ => (ofFun h a b).convs (2 * n + 1)) atTop (𝓝 U) := by
  sorry

/-- A common limit is bracketed with error at most the neighboring convergent gap,
Temme §13.5, synopsis TEM-13-12. Convergence is an explicit hypothesis. -/
theorem abs_sub_ofFun_convs_le_gap (h : ℝ) {a b : ℕ → ℝ}
    (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n) {v : ℝ}
    (hv : Tendsto (ofFun h a b).convs atTop (𝓝 v)) (n : ℕ) :
    (ofFun h a b).convs (2 * n) ≤ v ∧ v ≤ (ofFun h a b).convs (2 * n + 1) ∧
      |v - (ofFun h a b).convs (2 * n)| ≤
        (ofFun h a b).convs (2 * n + 1) - (ofFun h a b).convs (2 * n) ∧
      |v - (ofFun h a b).convs (2 * n + 1)| ≤
        (ofFun h a b).convs (2 * n + 1) - (ofFun h a b).convs (2 * n) := by
  sorry

end GenContFract
