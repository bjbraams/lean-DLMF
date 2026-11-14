/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A maximal-real-part indicial root has no positive integral resonance

Temme, *Special Functions* (1996), Theorem 4.3, (4.15)–(4.24), pp. 90–97,
synopsis TEM-04-05. Selecting the root with maximal real part permits the
single-root Frobenius construction even when the two roots differ by an integer.
-/

@[expose] public noncomputable section
namespace Complex

/-- Every monic second-order indicial quadratic has a root of maximal real part,
with no root at any positive integral translate. Temme Theorem 4.3,
synopsis TEM-04-05. A repeated root causes no exception. -/
theorem exists_indicial_root_maximal_re_nonresonant (p q : ℂ) :
    ∃ r : ℂ, r * (r - 1) + p * r + q = 0 ∧
      (∀ u : ℂ, u * (u - 1) + p * u + q = 0 → u.re ≤ r.re) ∧
      ∀ n : ℕ, 0 < n → (r + n) * (r + n - 1) + p * (r + n) + q ≠ 0 := by
  let d : ℂ := ((p - 1) ^ 2 - 4 * q) ^ (1 / 2 : ℂ)
  have hd : d ^ 2 = (p - 1) ^ 2 - 4 * q := by
    dsimp [d]
    rw [← cpow_mul_nat]
    norm_num
  have hdre : 0 ≤ d.re := by
    dsimp [d]
    rw [one_div, cpow_inv_two_re]
    exact Real.sqrt_nonneg _
  let r : ℂ := (1 - p + d) / 2
  have hr : r * (r - 1) + p * r + q = 0 := by
    dsimp [r]
    linear_combination hd / 4
  have hrel : 2 * r + p - 1 = d := by dsimp [r]; ring
  refine ⟨r, hr, ?_, ?_⟩
  · intro u hu
    have hfact : (u - r) * (u - r + d) = 0 := by
      linear_combination hu - hr - (u - r) * hrel
    rcases mul_eq_zero.mp hfact with h | h
    · rw [sub_eq_zero.mp h]
    · have hu' : u = r - d := by linear_combination h
      rw [hu', sub_re]
      linarith
  · intro n hn hz
    have hfact : (n : ℂ) * (n + d) = 0 := by
      linear_combination hz - hr - (n : ℂ) * hrel
    have hnd : (n : ℂ) + d = 0 :=
      (mul_eq_zero.mp hfact).resolve_left (Nat.cast_ne_zero.mpr (by omega))
    have hre := congrArg Complex.re hnd
    simp only [add_re, natCast_re, zero_re] at hre
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    linarith

end Complex
