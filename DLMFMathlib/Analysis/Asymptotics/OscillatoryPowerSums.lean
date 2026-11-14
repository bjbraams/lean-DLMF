/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.RingTheory.Binomial
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Fintype.BigOperators

/-!
# Complete asymptotic expansions of oscillatory power sums

Olver, *Asymptotics and Special Functions*, Chapter 8, §5,
pp. 295–299, synopsis O-8.07. The constant is a limit of explicitly
renormalized partial sums, including when the original series diverges.
-/

@[expose] public noncomputable section
open Filter Asymptotics
open scoped Topology
namespace Complex.OscillatoryPowerSum

/-- The triangular coefficient algorithm of Olver, Chapter 8, §5, pp. 295–299.
Its formal identity is `q(1+h)^alpha C(h/(1+h))-C(h)=1`. -/
def coefficient (α : ℝ) (q : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then (q - 1)⁻¹ else
    -q / (q - 1) * ∑ j : Fin n,
      coefficient α q j * (Ring.choose (α - j) (n - j) : ℝ)
termination_by n

/-- The zeroth coefficient is the reciprocal geometric-series increment. -/
theorem coefficient_zero (α : ℝ) (q : ℂ) : coefficient α q 0 = (q - 1)⁻¹ := by
  rw [coefficient, ite_eq_left rfl]

/-- The effective finite triangular recurrence for every later coefficient. -/
theorem coefficient_succ (α : ℝ) (q : ℂ) (n : ℕ) :
    coefficient α q (n + 1) = -q / (q - 1) * ∑ j : Fin (n + 1),
      coefficient α q j * (Ring.choose (α - j) (n + 1 - j) : ℝ) := by
  rw [coefficient, ite_eq_right (Nat.succ_ne_zero n)]

/-- The coefficient-by-coefficient formal functional equation. Olver §5. -/
theorem coefficient_functional_equation (α : ℝ) {q : ℂ} (hq : q ≠ 1) (n : ℕ) :
    q * (∑ j ∈ Finset.range (n + 1),
      coefficient α q j * (Ring.choose (α - j) (n - j) : ℝ)) - coefficient α q n =
        if n = 0 then 1 else 0 := by
  have hd : q - 1 ≠ 0 := sub_ne_zero.mpr hq
  rcases n with _ | n
  · norm_num [coefficient_zero, Ring.choose_zero_right]
    field_simp
  · rw [Finset.sum_range_succ]
    norm_num only [Nat.sub_self, Ring.choose_zero_right, ofReal_one, mul_one,
      Nat.succ_ne_zero]
    rw [coefficient_succ]
    have hs := Fin.sum_univ_eq_sum_range (fun j : ℕ =>
      coefficient α q j * (Ring.choose (α - j) (n + 1 - j) : ℝ)) (n + 1)
    rw [hs]
    field_simp
    norm_num; ring_nf; simp

/-- The finite oscillatory sum, ending before `n`, used by Olver §5. -/
def partialSum (α : ℝ) (q : ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.Ico 1 n, q ^ j * (j : ℂ) ^ (α : ℂ)

/-- The defining ordinary partial sum. -/
theorem partialSum_def (α : ℝ) (q : ℂ) (n : ℕ) :
    partialSum α q n = ∑ j ∈ Finset.Ico 1 n, q ^ j * (j : ℂ) ^ (α : ℂ) := rfl

/-- The oscillatory tail polynomial of length `N`. Olver, Chapter 8, §5. -/
def tail (α : ℝ) (q : ℂ) (N n : ℕ) : ℂ :=
  q ^ n * (n : ℂ) ^ (α : ℂ) *
    ∑ s ∈ Finset.range N, coefficient α q s / (n : ℂ) ^ s

/-- The defining finite tail approximation. -/
theorem tail_def (α : ℝ) (q : ℂ) (N n : ℕ) :
    tail α q N n = q ^ n * (n : ℂ) ^ (α : ℂ) *
      ∑ s ∈ Finset.range N, coefficient α q s / (n : ℂ) ^ s := rfl

/-- The constant is the limit after subtracting enough oscillatory terms.
Olver, Chapter 8, §5. It is not a totalized sum of a divergent series. -/
def constant (α : ℝ) (q : ℂ) : ℂ :=
  limUnder atTop (fun n : ℕ => partialSum α q n - tail α q (⌈max α 0⌉₊ + 2) n)

/-- The defining regularization limit for the oscillatory constant. -/
theorem constant_def (α : ℝ) (q : ℂ) : constant α q =
    limUnder atTop (fun n : ℕ => partialSum α q n - tail α q (⌈max α 0⌉₊ + 2) n) := rfl

/-- The chosen regularizing limit exists on the unit circle away from one.
Olver, Chapter 8, §5, pp. 295–299. -/
theorem tendsto_sub_tail (α : ℝ) {q : ℂ} (hnorm : ‖q‖ = 1) (hq : q ≠ 1) :
    Tendsto (fun n : ℕ => partialSum α q n - tail α q (⌈max α 0⌉₊ + 2) n)
      atTop (𝓝 (constant α q)) := by
  sorry

/-- Every finite truncation has its actual inverse-power error, with the same
constant for all orders. Olver, Chapter 8, §5, pp. 295–299. -/
theorem isBigO_sub_constant_sub_tail (α : ℝ) {q : ℂ}
    (hnorm : ‖q‖ = 1) (hq : q ≠ 1) (N : ℕ) :
    (fun n : ℕ => partialSum α q n - constant α q - tail α q N n) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (α - N)) := by
  sorry

/-- For negative powers the regularized constant equals the ordinary Dirichlet
limit, with the natural order retained. Olver, Chapter 8, §5, pp. 295–299. -/
theorem tendsto_partialSum {α : ℝ} (hα : α < 0) {q : ℂ}
    (hnorm : ‖q‖ = 1) (hq : q ≠ 1) :
    Tendsto (partialSum α q) atTop (𝓝 (constant α q)) := by
  sorry

end Complex.OscillatoryPowerSum
