/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.Binomial
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Analysis.Analytic.Binomial
public import DLMFMathlib.Combinatorics.S26aQuadraticSeries

/-!
# Catalan numbers (DLMF §26.5)

DLMF's Catalan number `C(n)` is Mathlib's `catalan n` (defined by the recurrence 26.5.3,
`catalan_succ`); no new definition is made. Mathlib proves `C(n) = C(2n, n)/(n+1)`
(`succ_mul_catalan_eq_centralBinom`), the formal generating-function identity
`PowerSeries.catalanSeries_sq_mul_X_add_one`, and counts Dyck words
(`DyckWord.card_dyckWord_semilength_eq_catalan`); a Dyck word of semilength `n` is a lattice
path from `(0, 0)` to `(n, n)` staying on or above `y = x` (up-step `(0, 1)`, down-step
`(1, 0)`), and the lattice-path count in DLMF's form is acquired here.

The forms `C(2n, n) - C(2n, n-1)` and `C(2n-1, n) - C(2n-1, n+1)` in 26.5.1 are stated for
`n ≥ 1` (for `n = 0` they need `C(0, -1) = 0`, resp. `C(-1, 0) - C(-1, 1)` with nonnegative
upper index, which DLMF's conventions do not cover).
-/

@[expose] public section

open Finset Filter Topology Asymptotics

noncomputable section

namespace DLMF.Combinatorics

/-- DLMF §26.5(i): `C(n)` is the number of lattice paths from `(0, 0)` to `(n, n)` that stay on
or above the line `y = x`. -/
@[dlmf 26.5.i]
theorem card_latticePaths_above_eq_catalan (n : ℕ) :
    #{l ∈ latticePaths unitSteps n n | StaysWeaklyAboveDiagonal l} = catalan n := by
  have h := q26a_ballot_eq (n + n) 0 n n rfl (by omega)
  simp only [q26a_ballot, Nat.cast_zero, q26a_staysAbove_zero_iff] at h
  rcases n with _ | n
  · simpa using h
  have hc := succ_mul_catalan_eq_centralBinom (n + 1)
  have hr := Nat.choose_succ_right_eq (n + 1 + (n + 1)) n
  rw [Nat.centralBinom_eq_two_mul_choose, two_mul] at hc
  rw [show n + 1 + (n + 1) - n = n + 2 by omega] at hr
  simp only [show 0 < n + 1 by omega, ite_true, Nat.add_sub_cancel, Nat.sub_zero] at h
  have : ((n + 2 : ℕ) : ℤ) *
        #{l ∈ latticePaths unitSteps (n + 1) (n + 1) | StaysWeaklyAboveDiagonal l}
      = (n + 2 : ℕ) * (catalan (n + 1) : ℤ) := by
    have hr' := congrArg (Nat.cast : ℕ → ℤ) hr
    have hc' := congrArg (Nat.cast : ℕ → ℤ) hc
    push_cast at hr' hc'
    rw [h]; push_cast; linear_combination hr' - hc'
  exact_mod_cast mul_left_cancel₀ (by positivity) this

/-- DLMF 26.5.1: `C(n) = C(2n, n)/(n+1) = C(2n+1, n)/(2n+1)` (all `n ≥ 0`). -/
@[dlmf 26.5.E1]
theorem catalan_eq_choose_div (n : ℕ) :
    (catalan n : ℚ) = ((2 * n).choose n : ℚ) / (n + 1) ∧
      (catalan n : ℚ) = ((2 * n + 1).choose n : ℚ) / (2 * n + 1) := by
  have h1 : ((n + 1 : ℕ) : ℚ) * catalan n = (2 * n).choose n := by
    exact_mod_cast (succ_mul_catalan_eq_centralBinom n).trans
      (Nat.centralBinom_eq_two_mul_choose n)
  have h2 : ((2 * n + 1 : ℕ) : ℚ) * (2 * n).choose n = (2 * n + 1).choose n * (n + 1 : ℕ) := by
    have := Nat.add_one_mul_choose_eq (2 * n) n
    rw [show n + 1 = 2 * n + 1 - n by omega, Nat.choose_symm (by omega)] at this
    rw [show 2 * n + 1 - n = n + 1 by omega] at this
    exact_mod_cast this
  push_cast at h1 h2
  have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
  have hn2 : 2 * (n : ℚ) + 1 ≠ 0 := by positivity
  constructor
  · rw [eq_div_iff hn1]; linarith
  · rw [eq_div_iff hn2]
    have : (catalan n : ℚ) * (2 * n + 1) * (n + 1) = (2 * n + 1).choose n * (n + 1) := by
      rw [← h2, ← h1]; ring
    exact mul_right_cancel₀ hn1 this

/-- DLMF 26.5.1 (third and fourth forms): `C(n) = C(2n, n) - C(2n, n-1)
= C(2n-1, n) - C(2n-1, n+1)`, `n ≥ 1`. -/
@[dlmf 26.5.E1]
theorem catalan_eq_choose_sub {n : ℕ} (hn : 1 ≤ n) :
    (catalan n : ℤ) = (2 * n).choose n - (2 * n).choose (n - 1) ∧
      (catalan n : ℤ) = (2 * n - 1).choose n - (2 * n - 1).choose (n + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel, show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
  -- `(k+2) C(k+1) = C(2k+2, k+1)` and `C(2k+2, k+1) (k+1) = C(2k+2, k) (k+2)`
  have h1 : ((k + 2 : ℕ) : ℤ) * catalan (k + 1) = (2 * (k + 1)).choose (k + 1) := by
    exact_mod_cast (succ_mul_catalan_eq_centralBinom (k + 1)).trans
      (Nat.centralBinom_eq_two_mul_choose (k + 1))
  have h2 := Nat.choose_succ_right_eq (2 * (k + 1)) k
  rw [show 2 * (k + 1) - k = k + 2 by omega] at h2
  have h2' : ((2 * (k + 1)).choose (k + 1) : ℤ) * (k + 1) = (2 * (k + 1)).choose k * (k + 2) := by
    exact_mod_cast h2
  push_cast at h1
  have first : (catalan (k + 1) : ℤ) = (2 * (k + 1)).choose (k + 1) - (2 * (k + 1)).choose k := by
    have hk : ((k : ℤ) + 2) ≠ 0 := by positivity
    apply mul_left_cancel₀ hk
    linear_combination h1 - h2'
  refine ⟨first, ?_⟩
  rw [first]
  have p1 : (2 * (k + 1)).choose (k + 1) = (2 * k + 1).choose k + (2 * k + 1).choose (k + 1) := by
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, Nat.choose_succ_succ']
  have p2 : (2 * (k + 1)).choose (k + 1 + 1) =
      (2 * k + 1).choose (k + 1) + (2 * k + 1).choose (k + 1 + 1) := by
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, Nat.choose_succ_succ']
  have s1 := Nat.choose_symm_half k
  have s2 : (2 * (k + 1)).choose (k + 1 + 1) = (2 * (k + 1)).choose k := by
    rw [← Nat.choose_symm (show k ≤ 2 * (k + 1) by omega)]; congr 1; omega
  rw [s2] at p2
  push_cast [p1, p2, s1]
  ring

/-- The generalized binomial coefficient over `ℝ` as a falling factorial over `n!`. -/
theorem q26a_ringChoose_eq (a : ℝ) (n : ℕ) :
    Ring.choose a n = (descPochhammer ℝ n).eval a / n.factorial := by
  rw [Ring.choose_eq_smul, ← Polynomial.aeval_eq_smeval, Polynomial.aeval_def,
    ← Polynomial.eval_map, descPochhammer_map,
    smul_eq_mul, div_eq_inv_mul]

/-- `C(n) = -(1/2) (-4)^{n+1} binom(1/2, n+1)`. -/
theorem q26a_catalan_eq_choose_half (n : ℕ) :
    (catalan n : ℝ) = -(1 / 2) * (-4) ^ (n + 1) * Ring.choose (1 / 2 : ℝ) (n + 1) := by
  induction n with
  | zero =>
    rw [q26a_ringChoose_eq]; simp; norm_num
  | succ n ih =>
    have hc := succ_mul_catalan_eq_centralBinom n
    have hc' := succ_mul_catalan_eq_centralBinom (n + 1)
    have hb := Nat.succ_mul_centralBinom_succ n
    have hrec : Ring.choose (1 / 2 : ℝ) (n + 1 + 1) =
        Ring.choose (1 / 2 : ℝ) (n + 1) * (1 / 2 - (n + 1)) / (n + 2) := by
      rw [q26a_ringChoose_eq, q26a_ringChoose_eq, descPochhammer_succ_eval, Nat.factorial_succ]
      push_cast
      have : ((n + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast (n + 1).factorial_ne_zero
      field_simp
      ring
    rw [hrec]
    have e1 : ((n + 2 : ℕ) : ℝ) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
      have h1 : ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * catalan (n + 1) =
          ((n + 1 : ℕ) : ℝ) * (2 * (2 * n + 1) * catalan n) := by
        have hA := congrArg (Nat.cast : ℕ → ℝ) hc'
        have hR := congrArg (Nat.cast : ℕ → ℝ) hb
        have hB := congrArg (Nat.cast : ℕ → ℝ) hc
        push_cast at hA hR hB ⊢
        linear_combination ((n : ℝ) + 1) * hA + hR - 2 * (2 * (n : ℝ) + 1) * hB
      have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have := h1
      rw [mul_comm ((n + 2 : ℕ) : ℝ), mul_assoc] at this
      exact mul_left_cancel₀ hn this
    have hn2 : ((n : ℝ) + 2) ≠ 0 := by positivity
    have : (catalan (n + 1) : ℝ) = 2 * (2 * n + 1) * catalan n / (n + 2) := by
      rw [eq_div_iff hn2]; push_cast at e1; linarith
    rw [this, ih]
    field_simp
    ring

/-- DLMF 26.5.2: `∑_{n=0}^∞ C(n) xⁿ = (1 - √(1-4x))/(2x)`, real `0 < |x| < 1/4` (DLMF:
`|x| < 1/4`; at `x = 0` the right side is the removable value `1`). -/
@[dlmf 26.5.E2]
theorem hasSum_catalan_mul_pow {x : ℝ} (hx0 : x ≠ 0) (hx : |x| < 1 / 4) :
    HasSum (fun n : ℕ => (catalan n : ℝ) * x ^ n) ((1 - Real.sqrt (1 - 4 * x)) / (2 * x)) := by
  have hb := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := (1 / 2 : ℝ))).hasSum
    (y := -4 * x) (by
      rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm, Real.norm_eq_abs, abs_mul]
      rw [ENNReal.ofReal_lt_one]; norm_num; linarith)
  simp only [binomialSeries_apply, List.ofFn_const, List.prod_replicate, smul_eq_mul,
    zero_add] at hb
  have h1 := (hasSum_nat_add_iff' 1).mpr hb
  simp only [range_one, sum_singleton, Ring.choose_zero_right, pow_zero, mul_one] at h1
  have h2 := h1.mul_left (-(1 / (2 * x)))
  rw [show (1 - Real.sqrt (1 - 4 * x)) / (2 * x) =
      -(1 / (2 * x)) * ((1 + -4 * x) ^ (1 / 2 : ℝ) - 1) by
    rw [← Real.sqrt_eq_rpow, show 1 + -4 * x = 1 - 4 * x by ring]; field_simp; ring]
  convert h2 using 1
  ext n
  rw [q26a_catalan_eq_choose_half, mul_pow]
  field_simp
  ring

/-- DLMF 26.5.3: `C(n+1) = ∑_{k=0}^{n} C(k) C(n-k)` (Mathlib `catalan_succ`, summed over
`Fin (n+1)`). -/
@[dlmf 26.5.E3]
theorem catalan_succ_eq_sum (n : ℕ) :
    catalan (n + 1) = ∑ k ∈ range (n + 1), catalan k * catalan (n - k) := by
  rw [catalan_succ, Fin.sum_univ_eq_sum_range (fun k => catalan k * catalan (n - k))]

/-- DLMF 26.5.4: `C(n+1) = 2(2n+1)/(n+2) · C(n)`. -/
@[dlmf 26.5.E4]
theorem catalan_succ_eq_mul (n : ℕ) :
    (catalan (n + 1) : ℚ) = 2 * (2 * n + 1) / (n + 2) * catalan n := by
  have h0 := succ_mul_catalan_eq_centralBinom n
  have h1 := succ_mul_catalan_eq_centralBinom (n + 1)
  have h2 := Nat.succ_mul_centralBinom_succ n
  have key : ((n + 1 : ℕ) : ℚ) * ((n + 2 : ℕ) : ℚ) * catalan (n + 1) =
      ((n + 1 : ℕ) : ℚ) * (2 * (2 * n + 1) * catalan n) := by
    have : (n + 1) * ((n + 2) * catalan (n + 1)) = (n + 1) * (2 * (2 * n + 1) * catalan n) := by
      rw [h1, h2, ← h0]; ring
    exact_mod_cast (by linarith [this] : (n + 1) * (n + 2) * catalan (n + 1) =
      (n + 1) * (2 * (2 * n + 1) * catalan n))
  have hn1 : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hn2 : (n : ℚ) + 2 ≠ 0 := by positivity
  rw [mul_assoc] at key
  have := mul_left_cancel₀ hn1 key
  push_cast at this
  rw [div_mul_eq_mul_div, eq_div_iff hn2]
  linarith

/-- DLMF 26.5.5: `C(n+1) = ∑_{k=0}^{⌊n/2⌋} C(n, 2k) 2^{n-2k} C(k)` (Touchard). -/
@[dlmf 26.5.E5]
theorem catalan_succ_eq_sum_touchard (n : ℕ) :
    catalan (n + 1) = ∑ k ∈ range (n / 2 + 1), n.choose (2 * k) * 2 ^ (n - 2 * k) * catalan k := by
  have h : (catalan (n + 1) : ℚ) =
      ∑ k ∈ range (n / 2 + 1), (n.choose (2 * k) : ℚ) * 2 ^ (n - 2 * k) * catalan k := by
    rw [s26a_catalan_succ_eq_sum,
      ← sum_subset (range_subset_range.mpr (by omega : n / 2 + 1 ≤ n + 1))]
    · exact sum_congr rfl fun k _ => by ring
    · intro k _ hk
      rw [Nat.choose_eq_zero_of_lt (by simp at hk; omega)]; simp
  exact_mod_cast h

/-- DLMF 26.5.6: `C(n) ~ 4ⁿ / √(πn³)` as `n → ∞`. -/
@[dlmf 26.5.E6]
theorem catalan_isEquivalent :
    (fun n : ℕ => (catalan n : ℝ)) ~[atTop] fun n => 4 ^ n / Real.sqrt (Real.pi * n ^ 3) := by
  have hc : ∀ n : ℕ, (catalan n : ℝ) = ((2 * n).choose n : ℝ) * (1 / (n + 1)) := by
    intro n
    have := congrArg (fun q : ℚ => (q : ℝ)) (catalan_eq_choose_div n).1
    push_cast at this
    rw [mul_one_div]; exact this
  have h1 : (fun n : ℕ => (1 / ((n : ℝ) + 1))) ~[atTop] fun n => 1 / (n : ℝ) := by
    apply isEquivalent_of_tendsto_one
    refine (tendsto_natCast_div_add_atTop (1 : ℝ)).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    simp only [Pi.div_apply]
    field_simp
  have := centralBinom_isEquivalent.mul h1
  refine (this.congr_left (Eventually.of_forall fun n => (hc n).symm)).congr_right ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Pi.mul_apply]
  rw [show Real.pi * (n : ℝ) ^ 3 = (Real.pi * n) * n ^ 2 by ring,
    Real.sqrt_mul (x := Real.pi * n) (by positivity) (n ^ 2), Real.sqrt_sq hn'.le]
  field_simp

/-- DLMF 26.5.7: `lim_{n→∞} C(n+1)/C(n) = 4`. -/
@[dlmf 26.5.E7]
theorem tendsto_catalan_succ_div :
    Tendsto (fun n : ℕ => (catalan (n + 1) : ℝ) / catalan n) atTop (𝓝 4) := by
  have hpos : ∀ n : ℕ, (catalan n : ℝ) ≠ 0 := fun n => by
    have h := succ_mul_catalan_eq_centralBinom n
    have : catalan n ≠ 0 := by
      intro h0; rw [h0, mul_zero] at h; exact (Nat.centralBinom_pos n).ne' h.symm
    exact_mod_cast this
  have h : ∀ n : ℕ, (catalan (n + 1) : ℝ) / catalan n = 4 - 6 / ((n + 2 : ℕ) : ℝ) := by
    intro n
    have := catalan_succ_eq_mul n
    have h' : (catalan (n + 1) : ℝ) = 2 * (2 * n + 1) / (n + 2) * catalan n := by
      have := congrArg (fun q : ℚ => (q : ℝ)) this
      push_cast at this; exact this
    rw [h', mul_div_assoc, div_self (hpos n), mul_one]
    have : (n : ℝ) + 2 ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  simp_rw [h]
  have := (tendsto_const_div_atTop_nhds_zero_nat (6 : ℝ)).comp (tendsto_add_atTop_nat 2)
  simpa using (tendsto_const_nhds (x := (4 : ℝ))).sub this

end DLMF.Combinatorics
