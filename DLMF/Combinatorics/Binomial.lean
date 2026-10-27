/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.Basic
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.RingTheory.Binomial
public import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Lattice paths: binomial coefficients (DLMF §26.3)

DLMF's binomial coefficient `C(m, n)` for nonnegative integers is Mathlib's `Nat.choose m n`
(with `C(m, n) = 0` for `n > m`, 26.3.2). Most of §26.3 is in Mathlib; the pointers are in
`DLMF/Combinatorics/MathlibCoverage.lean`. Here are the DLMF forms that Mathlib states
differently, the lattice-path counts of §26.3(i), and the asymptotic form 26.3.12 (derived from
Mathlib's Stirling formula `Stirling.tendsto_stirlingSeq_sqrt_pi`).

In 26.3.8 the term `k = 0` for `m = n` is `C(-1, 0) = 1`; the identity is stated with the
generalized binomial coefficient `Ring.choose` on `ℤ`, so that this boundary case is covered.
-/

@[expose] public section

open Finset Filter Topology Asymptotics

noncomputable section

namespace DLMF.Combinatorics

/-! ### Lattice paths (§26.3(i)) -/

/-- DLMF §26.3(i): `C(m+n, n)` is the number of lattice paths from `(0, 0)` to `(m, n)`. -/
@[dlmf 26.3.i]
theorem card_latticePaths_unitSteps (m n : ℕ) :
    #(latticePaths unitSteps m n) = (m + n).choose n := by
  have h0 : (0, 0) ∉ unitSteps := by decide
  induction m generalizing n with
  | zero =>
    induction n with
    | zero => simp [q26a_latticePaths_zero h0]
    | succ n ih =>
      have := q26a_card_filter_latticePaths h0 (m := 0) (n := n + 1) (by simp) (fun _ => True)
      simp only [filter_true] at this
      rw [this, show unitSteps.filter (fun s => s.1 ≤ 0 ∧ s.2 ≤ n + 1) = {(0, 1)} by
        ext ⟨a, b⟩; simp only [unitSteps, mem_filter, mem_insert, mem_singleton, Prod.mk.injEq]
        omega]
      simp [ih]
  | succ m ih =>
    induction n with
    | zero =>
      have := q26a_card_filter_latticePaths h0 (m := m + 1) (n := 0) (by simp) (fun _ => True)
      simp only [filter_true] at this
      rw [this, show unitSteps.filter (fun s => s.1 ≤ m + 1 ∧ s.2 ≤ 0) = {(1, 0)} by
        ext ⟨a, b⟩; simp only [unitSteps, mem_filter, mem_insert, mem_singleton, Prod.mk.injEq]
        omega]
      simp [ih]
    | succ n ihn =>
      have := q26a_card_filter_latticePaths h0 (m := m + 1) (n := n + 1) (by simp) (fun _ => True)
      simp only [filter_true] at this
      rw [this, show unitSteps.filter (fun s => s.1 ≤ m + 1 ∧ s.2 ≤ n + 1) = unitSteps by
        ext ⟨a, b⟩; simp only [unitSteps, mem_filter, mem_insert, mem_singleton, Prod.mk.injEq]
        omega]
      have hp : ∀ f : ℕ × ℕ → ℕ, ∑ s ∈ unitSteps, f s = f (1, 0) + f (0, 1) :=
        fun f => sum_pair (by decide)
      rw [hp]
      simp only [Nat.add_sub_cancel, Nat.sub_zero, ih, ihn]
      rw [show m + 1 + (n + 1) = (m + (n + 1)) + 1 by omega, Nat.choose_succ_succ',
        show m + 1 + n = m + (n + 1) by omega]
      ring

/-- DLMF §26.3(i): for `m ≤ n` the number of lattice paths from `(0, 0)` to `(m, n)` that stay
on or above the line `y = x` is `C(m+n, m) - C(m+n, m-1)` (with `C(m+n, -1) = 0` for
`m = 0`). -/
@[dlmf 26.3.i]
theorem card_latticePaths_unitSteps_above {m n : ℕ} (hmn : m ≤ n) :
    (#{l ∈ latticePaths unitSteps m n | StaysWeaklyAboveDiagonal l} : ℤ) =
      (m + n).choose m - if m = 0 then 0 else ((m + n).choose (m - 1) : ℤ) := by
  have h := q26a_ballot_eq (m + n) 0 m n rfl (by omega)
  simp only [q26a_ballot, Nat.cast_zero, q26a_staysAbove_zero_iff] at h
  rw [h, Nat.choose_symm_add]
  rcases m with _ | m <;> simp

/-! ### Generating functions (§26.3(ii)) -/

/-- DLMF 26.3.3: `∑_{n=0}^{m} C(m, n) xⁿ = (1+x)^m` (any commutative semiring). -/
@[dlmf 26.3.E3]
theorem sum_choose_mul_pow {R : Type*} [CommSemiring R] (m : ℕ) (x : R) :
    ∑ n ∈ range (m + 1), (m.choose n : R) * x ^ n = (1 + x) ^ m := by
  rw [add_comm (1 : R) x, add_pow]
  refine sum_congr rfl fun n _ => ?_
  rw [one_pow, mul_one, mul_comm]

/-- DLMF 26.3.4: `∑_{m=0}^∞ C(m+n, m) x^m = (1-x)^{-n-1}`, `|x| < 1` (real `x`). -/
@[dlmf 26.3.E4]
theorem hasSum_choose_mul_pow (n : ℕ) {x : ℝ} (hx : |x| < 1) :
    HasSum (fun m : ℕ => ((m + n).choose m : ℝ) * x ^ m) (1 / (1 - x) ^ (n + 1)) := by
  have := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) n (r := x) (by simpa using hx)
  convert this using 2 with m
  rw [Nat.choose_symm_add]

/-! ### Recurrence relations and identities (§26.3(iii)–(iv)) -/

/-- DLMF 26.3.6: `C(m, n) = (m/n) C(m-1, n-1) = ((m-n+1)/n) C(m, n-1)`, `m ≥ n ≥ 1`. -/
@[dlmf 26.3.E6]
theorem choose_eq_div_mul {m n : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    (m.choose n : ℚ) = m / n * (m - 1).choose (n - 1) ∧
      (m.choose n : ℚ) = (m - n + 1) / n * m.choose (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨l, rfl⟩ : ∃ l, m = l + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h1 := Nat.add_one_mul_choose_eq l k
  have h2 := Nat.choose_succ_right_eq (l + 1) k
  have hk : (k : ℚ) + 1 ≠ 0 := by positivity
  have h1' : ((l + 1).choose (k + 1) : ℚ) * ((k : ℚ) + 1) = ((l : ℚ) + 1) * (l.choose k : ℚ) := by
    exact_mod_cast h1.symm
  have h2' : ((l + 1).choose (k + 1) : ℚ) * ((k : ℚ) + 1) =
      ((l + 1).choose k : ℚ) * ((l : ℚ) + 1 - k) := by
    have := h2
    rw [← Nat.cast_inj (R := ℚ)] at this
    push_cast [Nat.cast_sub (show k ≤ l + 1 by omega)] at this
    linarith
  constructor
  · rw [div_mul_eq_mul_div]; push_cast; rw [eq_div_iff hk]; linarith
  · rw [div_mul_eq_mul_div]; push_cast; rw [eq_div_iff hk]; linarith

/-- `∑_{k=0}^{n} C(r+k, k) = C(r+n+1, n)`. -/
lemma c26a_sum_choose_add (r n : ℕ) :
    ∑ k ∈ range (n + 1), (r + k).choose k = (r + n + 1).choose n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, show r + (n + 1) + 1 = (r + n + 1) + 1 by omega,
      Nat.choose_succ_succ', show r + (n + 1) = r + n + 1 by omega]

/-- DLMF 26.3.8: `C(m, n) = ∑_{k=0}^{n} C(m-n-1+k, k)`, `m ≥ n ≥ 0`, with the generalized
binomial coefficient (for `m = n` the term `k = 0` is `C(-1, 0) = 1`). -/
@[dlmf 26.3.E8]
theorem choose_eq_sum_ringChoose {m n : ℕ} (hnm : n ≤ m) :
    (m.choose n : ℤ) = ∑ k ∈ range (n + 1), Ring.choose ((m : ℤ) - n - 1 + k) k := by
  rcases hnm.lt_or_eq with h | rfl
  · obtain ⟨r, rfl⟩ : ∃ r, m = n + r + 1 := ⟨m - n - 1, by omega⟩
    have : ∀ k : ℕ, ((n + r + 1 : ℕ) : ℤ) - n - 1 + k = ((r + k : ℕ) : ℤ) := by
      intro k; push_cast; ring
    simp_rw [this, Ring.choose_natCast]
    rw [← Nat.cast_sum, c26a_sum_choose_add, show r + n + 1 = n + r + 1 by omega]
  · rw [sum_range_succ', Nat.choose_self]
    have : ∀ k ∈ range n, Ring.choose ((n : ℤ) - n - 1 + ((k + 1 : ℕ) : ℤ)) (k + 1) = 0 := by
      intro k _
      rw [show (n : ℤ) - n - 1 + ((k + 1 : ℕ) : ℤ) = ((k : ℕ) : ℤ) by push_cast; ring,
        Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega)]
      simp
    rw [sum_eq_zero this]
    simp

/-- DLMF 26.3.10: `C(m, n) = ∑_{k=0}^{n} (-1)^{n-k} C(m+1, k)` (all `m, n ≥ 0`; DLMF states
`m ≥ n`). -/
@[dlmf 26.3.E10]
theorem choose_eq_alternating_sum (m n : ℕ) :
    (m.choose n : ℤ) = ∑ k ∈ range (n + 1), (-1) ^ (n - k) * ((m + 1).choose k : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, Nat.sub_self, pow_zero, one_mul]
    have : ∑ k ∈ range (n + 1), (-1 : ℤ) ^ (n + 1 - k) * ((m + 1).choose k : ℤ) =
        -∑ k ∈ range (n + 1), (-1) ^ (n - k) * ((m + 1).choose k : ℤ) := by
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun k hk => ?_
      rw [show n + 1 - k = n - k + 1 by have := mem_range.mp hk; omega, pow_succ]; ring
    rw [this, ← ih, Nat.choose_succ_succ']
    push_cast; ring

/-- DLMF 26.3.11: `C(2n, n) = 2ⁿ (2n-1)(2n-3)⋯3·1 / n!` (`(2n-1)‼`, with `(-1)‼ = 1`). -/
@[dlmf 26.3.E11]
theorem centralBinom_eq_doubleFactorial (n : ℕ) :
    ((2 * n).choose n : ℚ) = 2 ^ n * ((2 * n - 1).doubleFactorial : ℚ) / n.factorial := by
  have key : (2 * n).choose n * n.factorial = 2 ^ n * (2 * n - 1).doubleFactorial := by
    rcases n with _ | n
    · simp
    · have h1 := Nat.choose_mul_factorial_mul_factorial (show n + 1 ≤ 2 * (n + 1) by omega)
      rw [show 2 * (n + 1) - (n + 1) = n + 1 by omega] at h1
      have h2 := Nat.factorial_eq_mul_doubleFactorial (2 * n + 1)
      rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega, Nat.doubleFactorial_two_mul] at h2
      rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
      have hf : 0 < (n + 1).factorial := Nat.factorial_pos _
      apply Nat.eq_of_mul_eq_mul_right hf
      rw [h1, h2]; ring
  have hf : (n.factorial : ℚ) ≠ 0 := by positivity
  rw [eq_div_iff hf]
  exact_mod_cast key

/-! ### Limiting form (§26.3(v)) -/

/-- Central binomial coefficients via Stirling's sequence: for `n ≥ 1`,
`C(2n, n) √(πn) / 4ⁿ = stirlingSeq(2n) √π / stirlingSeq(n)²`. -/
lemma c26a_centralBinom_stirling {n : ℕ} (hn : 1 ≤ n) :
    ((2 * n).choose n : ℝ) * Real.sqrt (Real.pi * n) / 4 ^ n =
      Stirling.stirlingSeq (2 * n) * Real.sqrt Real.pi / Stirling.stirlingSeq n ^ 2 := by
  unfold Stirling.stirlingSeq
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Nat.cast_choose (K := ℝ) (show n ≤ 2 * n by omega), show 2 * n - n = n by omega]
  have e1 : Real.sqrt (2 * ((2 * n : ℕ) : ℝ)) = 2 * Real.sqrt n := by
    rw [show (2 : ℝ) * ((2 * n : ℕ) : ℝ) = 2 ^ 2 * n by push_cast; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have e2 : Real.sqrt (2 * (n : ℝ)) ^ 2 = 2 * n := Real.sq_sqrt (by positivity)
  have e3 : Real.sqrt (Real.pi * n) = Real.sqrt Real.pi * Real.sqrt n :=
    Real.sqrt_mul Real.pi_pos.le _
  have e4 : (((2 * n : ℕ) : ℝ) / Real.exp 1) ^ (2 * n) = 4 ^ n * ((n / Real.exp 1) ^ n) ^ 2 := by
    rw [show ((2 * n : ℕ) : ℝ) / Real.exp 1 = 2 * (n / Real.exp 1) by push_cast; ring, mul_pow,
      pow_mul (2 : ℝ) 2 n]
    ring
  have e5 : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn'.le
  rw [e1, e3, e4]
  set q := ((n : ℝ) / Real.exp 1) ^ n with hq
  set t := Real.sqrt (n : ℝ) with ht
  have h1 : t ≠ 0 := (Real.sqrt_pos.mpr hn').ne'
  have h2 : q ≠ 0 := by positivity
  have h3 : ((n.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  rw [div_pow, mul_pow, e2]
  field_simp
  rw [← e5]

/-- DLMF 26.3.12: `C(2n, n) ~ 4ⁿ / √(πn)` as `n → ∞`. -/
@[dlmf 26.3.E12]
theorem centralBinom_isEquivalent :
    (fun n : ℕ => ((2 * n).choose n : ℝ)) ~[atTop]
      fun n => 4 ^ n / Real.sqrt (Real.pi * n) := by
  apply isEquivalent_of_tendsto_one
  have h2n : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun n hn => by omega⟩
  have hπ : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hlim : Tendsto (fun n : ℕ => Stirling.stirlingSeq (2 * n) * Real.sqrt Real.pi /
      Stirling.stirlingSeq n ^ 2) atTop
      (𝓝 (Real.sqrt Real.pi * Real.sqrt Real.pi / Real.sqrt Real.pi ^ 2)) :=
    ((Stirling.tendsto_stirlingSeq_sqrt_pi.comp h2n).mul_const _).div
      (Stirling.tendsto_stirlingSeq_sqrt_pi.pow 2) (pow_ne_zero 2 hπ)
  rw [show Real.sqrt Real.pi * Real.sqrt Real.pi / Real.sqrt Real.pi ^ 2 = 1 by
    field_simp] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Pi.div_apply, ← c26a_centralBinom_stirling hn, div_div_eq_mul_div]

end DLMF.Combinatorics
