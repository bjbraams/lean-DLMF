/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.PositiveZeroSequence
public import DLMF.Bessel.Basic.SecondKind

/-!
# Consecutive-zero gaps and McMahon expansions

Temme, *Special Functions* (1996), Theorem 9.3, (9.57)–(9.59), and Exercise 9.5,
pp. 242–243, 250, synopses TEM-09-12/14. Enumerations are complete and increasing,
so their indexing cannot be shifted by omitting finitely many zeros.
-/

@[expose] public noncomputable section
open Complex Filter Asymptotics
open scoped Real Topology Nat
namespace DLMF.Bessel

/-- Sharp comparison of consecutive `J`-zero gaps with `π`, Temme Theorem 9.3,
(9.58)–(9.59), synopsis TEM-09-12. -/
theorem Real.besselJ_consecutive_zero_gap {ν a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hJa : besselJ ν a = 0) (hJb : besselJ ν b = 0)
    (hnext : ∀ x ∈ Set.Ioo a b, besselJ ν x ≠ 0) :
    (|ν| < 1 / 2 → b - a < Real.pi) ∧
      (|ν| = 1 / 2 → b - a = Real.pi) ∧
      (1 / 2 < |ν| → Real.pi < b - a) := by
  sorry

/-- McMahon's first two corrections for every complete increasing `J`-zero sequence,
Temme (9.57), synopsis TEM-09-14. Index zero denotes the first positive zero. -/
theorem Real.besselJ_positive_zeros_mcmahon {ν : ℝ} (hν : -1 < ν) (j : ℕ → ℝ)
    (hjpos : ∀ n, 0 < j n) (hjmono : StrictMono j)
    (hjrange : ∀ x : ℝ, 0 < x → (besselJ ν x = 0 ↔ ∃ n, j n = x))
    (hjlim : Tendsto j atTop atTop) :
    let μ := 4 * ν ^ 2
    let β : ℕ → ℝ := fun n => ((n : ℝ) + 1 + ν / 2 - 1 / 4) * Real.pi
    (fun n : ℕ => j n - β n + (μ - 1) / (8 * β n) +
      4 * (μ - 1) * (7 * μ - 31) / (3 * (8 * β n) ^ 3))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-5 : ℝ)) := by
  sorry

/-- The second-kind positive zeros also have a complete increasing enumeration,
Temme Exercise 9.5, p. 250, synopsis TEM-09-14. -/
theorem Real.exists_strictMono_besselY_positive_zeros (ν : ℝ) :
    ∃ y : ℕ → ℝ, (∀ n, 0 < y n) ∧ StrictMono y ∧ Tendsto y atTop atTop ∧
      ∀ x : ℝ, 0 < x → (besselY ν x = 0 ↔ ∃ n, y n = x) := by
  sorry

/-- McMahon's second-kind zero expansion, Temme Exercise 9.5,
p. 250, synopsis TEM-09-14. -/
theorem Real.besselY_positive_zeros_mcmahon {ν : ℝ} (hν : 0 ≤ ν) (y : ℕ → ℝ)
    (hypos : ∀ n, 0 < y n) (hymono : StrictMono y)
    (hyrange : ∀ x : ℝ, 0 < x → (besselY ν x = 0 ↔ ∃ n, y n = x))
    (hylim : Tendsto y atTop atTop) :
    let μ := 4 * ν ^ 2
    let β : ℕ → ℝ := fun n => ((n : ℝ) + 1 + ν / 2 - 3 / 4) * Real.pi
    (fun n : ℕ => y n - β n + (μ - 1) / (8 * β n) +
      4 * (μ - 1) * (7 * μ - 31) / (3 * (8 * β n) ^ 3))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-5 : ℝ)) := by
  sorry

end DLMF.Bessel
