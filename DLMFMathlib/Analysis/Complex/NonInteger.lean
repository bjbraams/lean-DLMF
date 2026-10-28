/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Module.Cardinality
public import Mathlib.Tactic.LinearCombination

/-!
# Complex numbers off the integers and off the poles of `Γ`

Bookkeeping for parameters that avoid the integers or the nonpositive integers, and the
density argument extending an identity of continuous functions from the non-integers to
all of `ℂ`.
-/

@[expose] public section

namespace Complex

/-- Two continuous functions on `ℂ` that agree off the integers agree everywhere. -/
theorem eq_of_continuous_of_eq_off_int {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ μ : ℂ, (∀ n : ℤ, μ ≠ n) → f μ = g μ) (μ : ℂ) : f μ = g μ := by
  have hd : Dense (Set.range (fun n : ℤ => (n : ℂ)))ᶜ :=
    (Set.countable_range _).dense_compl ℂ
  exact congrFun (hf.ext_on hd hg fun ν hν => h ν fun n hn => hν ⟨n, hn.symm⟩) μ

/-- A non-integer is not a nonpositive integer. -/
theorem ne_neg_natCast_of_ne_intCast {b : ℂ} (hb : ∀ k : ℤ, b ≠ k) : ∀ k : ℕ, b ≠ -k :=
  fun k h => hb (-(k : ℤ)) (by rw [h]; push_cast; ring)

/-- If `ν` is not an integer, neither is `ν + 1`. -/
theorem add_one_ne_intCast_of_ne_intCast {ν : ℂ} (hν : ∀ k : ℤ, ν ≠ k) :
    ∀ k : ℤ, ν + 1 ≠ k := fun k h =>
  hν (k - 1) (by push_cast; linear_combination h)

/-- If `l` is not a nonpositive integer, then `l + n ≠ 0` for every natural `n`. -/
theorem add_natCast_ne_zero_of_ne_neg_natCast {l : ℂ} (hl : ∀ n : ℕ, l ≠ -n) (n : ℕ) :
    l + n ≠ 0 := fun h => hl n (eq_neg_of_add_eq_zero_left h)

/-- If `Re a > 0`, then `a + n ≠ 0` for every natural `n`. -/
theorem add_natCast_ne_zero_of_re_pos {a : ℂ} (ha : 0 < a.re) (k : ℕ) : a + k ≠ 0 := by
  intro h
  have := congrArg re h
  simp at this
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- `1/2` is not a nonpositive integer. -/
theorem one_div_two_ne_neg_natCast : ∀ k : ℕ, (1 / 2 : ℂ) ≠ -(k : ℂ) := fun k h => by
  have := congrArg re h; simp at this; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]

end Complex
