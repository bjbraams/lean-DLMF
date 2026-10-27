/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.Binomial
public import DLMFMathlib.Combinatorics.R26aFinpartition
public import DLMFMathlib.Combinatorics.Q26bSurjections

/-!
# Stirling numbers (DLMF §26.8)

DLMF's Stirling numbers of the first kind `s(n, k)` are **signed**: `(-1)^{n-k}` times the
number of permutations of `{1, …, n}` with exactly `k` cycles (DLMF 26.8(i)). Mathlib's
`Nat.stirlingFirst n k` is the unsigned (cycle-counting) number, so the DLMF function is
`signedStirlingFirst n k = (-1)^{n-k} * Nat.stirlingFirst n k : ℤ` (defined here). DLMF's
`S(n, k)` (second kind) is Mathlib's `Nat.stirlingSecond n k` itself; no new definition is
made for it. Both are defined for all `n, k : ℕ` and vanish for `k > n`.

The key bridge is `coeff_descPochhammer`: the falling factorial `x(x-1)⋯(x-n+1)` (Mathlib's
`descPochhammer`) has the coefficients `s(n, k)`. DLMF writes it as the rising factorial
`(x-n+1)_n` (`ascPochhammer` evaluated at `x - n + 1`). The inverse expansion 26.8.10 is
derived from Mathlib's `Nat.pow_eq_sum_stirlingSecond_mul_descFactorial` by polynomial
identity (agreement at every natural number). The lean-codes module
`Pochhammer.PochhammerTransform` has the same expansions in the rising-factorial basis.

**Source corrections (implicit conditions).**
* 26.8.10 (`∑_{k=1}^n S(n,k)(x-k+1)_k = xⁿ`) fails for `n = 0` (empty sum `0 ≠ 1`); it is
  acquired for `1 ≤ n`, with the `k = 0` form valid for all `n` alongside.
* 26.8.29 (`∑_{k=1}^n (-1)^{n-k} s(n,k) = n!`) fails for `n = 0`; acquired for `1 ≤ n`.
* 26.8.31 as printed ("when `f` is analytic for all `x` and the series converges") is false:
  for `f(x) = sin(πx)` at `x = 0`, `k = 1` every `Δⁿf(0) = 0`, so the series converges to
  `0`, but `f'(0) = π`. It is acquired for polynomial `f` (where the series is finite), and
  the counterexample is recorded (`not_forall_stirling_deriv_eq_fwdDiff_series`).
-/

@[expose] public section

open Finset Polynomial Filter Topology Asymptotics

noncomputable section

namespace DLMF.Combinatorics

/-! ### Definitions (§26.8(i)) -/

/-- DLMF §26.8(i): the (signed) Stirling number of the first kind
`s(n, k) = (-1)^{n-k} · #{permutations of {1,…,n} with exactly k cycles}`, written with
Mathlib's unsigned `Nat.stirlingFirst`. It is `0` for `k > n`. -/
@[dlmf 26.8.i]
def signedStirlingFirst (n k : ℕ) : ℤ := (-1) ^ (n - k) * (Nat.stirlingFirst n k : ℤ)

@[simp] theorem signedStirlingFirst_zero_zero : signedStirlingFirst 0 0 = 1 := by
  simp [signedStirlingFirst, Nat.stirlingFirst_zero]

@[simp] theorem signedStirlingFirst_zero_succ (k : ℕ) : signedStirlingFirst 0 (k + 1) = 0 := by
  simp [signedStirlingFirst, Nat.stirlingFirst_zero_succ]

@[simp] theorem signedStirlingFirst_succ_zero (n : ℕ) : signedStirlingFirst (n + 1) 0 = 0 := by
  simp [signedStirlingFirst, Nat.stirlingFirst_succ_zero]

theorem signedStirlingFirst_eq_zero_of_lt {n k : ℕ} (h : n < k) : signedStirlingFirst n k = 0 := by
  simp [signedStirlingFirst, Nat.stirlingFirst_eq_zero_of_lt h]

/-- The sign relation: `(-1)^{n-k} s(n, k)` is the unsigned Stirling number. -/
theorem neg_one_pow_mul_signedStirlingFirst (n k : ℕ) :
    (-1) ^ (n - k) * signedStirlingFirst n k = Nat.stirlingFirst n k := by
  rw [signedStirlingFirst, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp

/-- DLMF 26.8.18: `s(n, k) = s(n-1, k-1) - (n-1) s(n-1, k)`, written with `n + 1`, `k + 1`
(valid for all `n, k ≥ 0`). -/
@[dlmf 26.8.E18]
theorem signedStirlingFirst_succ_succ (n k : ℕ) :
    signedStirlingFirst (n + 1) (k + 1) =
      signedStirlingFirst n k - n * signedStirlingFirst n (k + 1) := by
  simp only [signedStirlingFirst, Nat.stirlingFirst_succ_succ, Nat.add_sub_add_right]
  push_cast
  rcases lt_or_ge k n with h | h
  · obtain ⟨d, rfl⟩ : ∃ d, n = k + 1 + d := ⟨n - (k + 1), by omega⟩
    have e1 : k + 1 + d - k = d + 1 := by omega
    have e2 : k + 1 + d - (k + 1) = d := by omega
    rw [e1, e2, pow_succ]; ring
  · rw [Nat.stirlingFirst_eq_zero_of_lt (by omega : n < k + 1), Nat.sub_eq_zero_of_le h]
    simp

/-- DLMF 26.8.18 at `k = 0`: `s(n+1, 0) = -n s(n, 0)` (both sides vanish). -/
@[dlmf 26.8.E18]
theorem signedStirlingFirst_succ_zero' (n : ℕ) :
    signedStirlingFirst (n + 1) 0 = -(n * signedStirlingFirst n 0) := by
  cases n <;> simp

/-! ### Basic values -/

/-- DLMF 26.8.1: `s(n, n) = 1`. -/
@[dlmf 26.8.E1]
theorem signedStirlingFirst_self (n : ℕ) : signedStirlingFirst n n = 1 := by
  simp [signedStirlingFirst, Nat.stirlingFirst_self]

/-- DLMF 26.8.2: `s(1, k) = δ_{1,k}`. -/
@[dlmf 26.8.E2]
theorem signedStirlingFirst_one (k : ℕ) : signedStirlingFirst 1 k = if k = 1 then 1 else 0 := by
  rcases k with _ | _ | k
  · simp
  · simp [signedStirlingFirst_self]
  · simp [signedStirlingFirst_eq_zero_of_lt (by omega : 1 < k + 2)]

/-- The elementary symmetric sum `e_j(1, 2, …, m) = ∑_{1 ≤ b₁ < ⋯ < b_j ≤ m} b₁⋯b_j`. -/
def c26a_esymmRange (m j : ℕ) : ℤ := ∑ B ∈ (Icc 1 m).powersetCard j, ∏ b ∈ B, (b : ℤ)

/-- The recurrence `e_{j+1}(1,…,m+1) = e_{j+1}(1,…,m) + (m+1) e_j(1,…,m)`. -/
lemma q26a_esymmRange_succ_succ (m j : ℕ) :
    c26a_esymmRange (m + 1) (j + 1) =
      c26a_esymmRange m (j + 1) + (m + 1) * c26a_esymmRange m j := by
  have hI : Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) := by
    ext x; simp only [mem_Icc, mem_insert]; omega
  have hx : m + 1 ∉ Icc 1 m := by simp
  unfold c26a_esymmRange
  rw [hI, powersetCard_succ_insert hx, sum_union, sum_image, mul_sum]
  · congr 1
    refine sum_congr rfl fun B hB => ?_
    have : m + 1 ∉ B := fun h => hx ((mem_powersetCard.mp hB).1 h)
    rw [prod_insert this]; push_cast; ring
  · intro B hB C hC h
    have hB' : m + 1 ∉ B := fun h => hx ((mem_powersetCard.mp hB).1 h)
    have hC' : m + 1 ∉ C := fun h => hx ((mem_powersetCard.mp hC).1 h)
    rw [← erase_insert hB', h, erase_insert hC']
  · rw [disjoint_left]
    intro B hB hB2
    obtain ⟨C, _, rfl⟩ := mem_image.mp hB2
    exact hx ((mem_powersetCard.mp hB).1 (mem_insert_self _ _))

/-- `e_0 = 1`. -/
lemma q26a_esymmRange_zero (m : ℕ) : c26a_esymmRange m 0 = 1 := by
  simp [c26a_esymmRange]

/-- `e_j(1,…,m) = 0` for `j > m`. -/
lemma q26a_esymmRange_eq_zero {m j : ℕ} (h : m < j) : c26a_esymmRange m j = 0 := by
  rw [c26a_esymmRange, powersetCard_eq_empty.mpr (by simp; omega), sum_empty]

/-- `c(m+1, i) = e_{m+1-i}(1, …, m)`. -/
lemma q26a_stirlingFirst_eq_esymm (m : ℕ) : ∀ i ≤ m + 1,
    (Nat.stirlingFirst (m + 1) i : ℤ) = c26a_esymmRange m (m + 1 - i) := by
  induction m with
  | zero =>
    intro i hi
    rcases i with _ | _ | i
    · simp [q26a_esymmRange_eq_zero]
    · simp [q26a_esymmRange_zero, Nat.stirlingFirst_self]
    · omega
  | succ m ih =>
    intro i hi
    rcases i with _ | i
    · simp [q26a_esymmRange_eq_zero]
    · rw [Nat.stirlingFirst_succ_succ]
      push_cast
      rcases Nat.lt_or_ge i (m + 1) with h | h
      · rw [ih (i + 1) (by omega), ih i (by omega),
          show m + 1 - i = m + 1 - (i + 1) + 1 by omega, q26a_esymmRange_succ_succ]
        push_cast; ring
      · obtain rfl : i = m + 1 := by omega
        simp [Nat.stirlingFirst_self, q26a_esymmRange_zero,
          Nat.stirlingFirst_eq_zero_of_lt (show m + 1 < m + 1 + 1 by omega)]

/-- DLMF 26.8.3: `(-1)^{n-k} s(n, k) = ∑_{1 ≤ b₁ < ⋯ < b_{n-k} ≤ n-1} b₁ b₂ ⋯ b_{n-k}`,
`n > k ≥ 1`. -/
@[dlmf 26.8.E3]
theorem neg_one_pow_mul_signedStirlingFirst_eq_esymm {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) :
    (-1) ^ (n - k) * signedStirlingFirst n k = c26a_esymmRange (n - 1) (n - k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [neg_one_pow_mul_signedStirlingFirst, q26a_stirlingFirst_eq_esymm m k (by omega)]
  rfl

/-- DLMF 26.8.4: `S(n, n) = 1` (Mathlib `Nat.stirlingSecond_self`). -/
@[dlmf 26.8.E4]
theorem stirlingSecond_self' (n : ℕ) : Nat.stirlingSecond n n = 1 := Nat.stirlingSecond_self n

/-- The complete homogeneous sum with weights `k, k-1, …, 1`. -/
def q26a_hRev (k d : ℕ) : ℤ :=
  ∑ c ∈ Finset.Nat.antidiagonalTuple k d, ∏ i : Fin k, ((k : ℤ) - i) ^ (c i)

/-- Splitting a sum over `antidiagonalTuple (k+1) d` by the first coordinate. -/
lemma q26a_sum_antidiagonalTuple_succ {M : Type*} [AddCommMonoid M] (k d : ℕ)
    (F : (Fin (k + 1) → ℕ) → M) :
    ∑ c ∈ Finset.Nat.antidiagonalTuple (k + 1) d, F c =
      ∑ p ∈ antidiagonal d, ∑ c ∈ Finset.Nat.antidiagonalTuple k p.2, F (Fin.cons p.1 c) := by
  rw [sum_sigma']
  refine sum_bij' (fun c _ => ⟨(c 0, d - c 0), Fin.tail c⟩) (fun q _ => Fin.cons q.1.1 q.2)
    ?_ ?_ ?_ ?_ ?_
  · intro c hc
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_succ] at hc
    simp only [mem_sigma, mem_antidiagonal, Finset.Nat.mem_antidiagonalTuple]
    refine ⟨by omega, ?_⟩
    simp only [Fin.tail]; omega
  · rintro ⟨⟨a, b⟩, c⟩ hq
    simp only [mem_sigma, mem_antidiagonal, Finset.Nat.mem_antidiagonalTuple] at hq
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]; omega
  · intro c _; simp
  · rintro ⟨⟨a, b⟩, c⟩ hq
    simp only [mem_sigma, mem_antidiagonal, Finset.Nat.mem_antidiagonalTuple] at hq
    simp only [Fin.cons_zero, Fin.tail_cons, Sigma.mk.injEq, Prod.mk.injEq, heq_eq_eq, and_true,
      true_and]
    omega
  · intro c _; simp

/-- First-coordinate expansion of `q26a_hRev`. -/
lemma q26a_hRev_succ (k d : ℕ) :
    q26a_hRev (k + 1) d = ∑ p ∈ antidiagonal d, ((k : ℤ) + 1) ^ p.1 * q26a_hRev k p.2 := by
  unfold q26a_hRev
  rw [q26a_sum_antidiagonalTuple_succ]
  refine sum_congr rfl fun p _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun c _ => ?_
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ]
  push_cast
  rw [sub_zero]
  congr 1
  exact prod_congr rfl fun i _ => by ring_nf

/-- The recurrence `h_{d+1}(k+1,…,1) = h_{d+1}(k,…,1) + (k+1) h_d(k+1,…,1)`. -/
lemma q26a_hRev_succ_succ (k d : ℕ) :
    q26a_hRev (k + 1) (d + 1) = q26a_hRev k (d + 1) + ((k : ℤ) + 1) * q26a_hRev (k + 1) d := by
  rw [q26a_hRev_succ, q26a_hRev_succ, Finset.Nat.sum_antidiagonal_succ, mul_sum]
  simp only [pow_zero, one_mul, pow_succ]
  congr 1
  refine sum_congr rfl fun p _ => by ring

/-- `q26a_hRev 0 d = δ_{d,0}`. -/
lemma q26a_hRev_zero_left (d : ℕ) : q26a_hRev 0 d = if d = 0 then 1 else 0 := by
  rcases d with _ | d <;> simp [q26a_hRev]

/-- `S(k+d, k) = h_d(k, k-1, …, 1)`. -/
lemma q26a_stirlingSecond_eq_hRev (k d : ℕ) :
    (Nat.stirlingSecond (k + d) k : ℤ) = q26a_hRev k d := by
  induction k generalizing d with
  | zero => rcases d with _ | d <;> simp [q26a_hRev_zero_left, Nat.stirlingSecond_succ_zero]
  | succ k ih =>
    induction d with
    | zero =>
      rw [q26a_hRev, Finset.Nat.antidiagonalTuple_zero_right]; simp [Nat.stirlingSecond_self]
    | succ d ihd =>
      rw [q26a_hRev_succ_succ, ← ih, ← ihd, show k + 1 + (d + 1) = (k + 1 + d) + 1 by ring,
        Nat.stirlingSecond_succ_succ, show k + 1 + d = k + (d + 1) by ring]
      push_cast; ring

/-- DLMF 26.8.5: `S(n, k) = ∑ 1^{c₁} 2^{c₂} ⋯ k^{c_k}` over `c₁ + ⋯ + c_k = n - k`
(the complete homogeneous symmetric polynomial `h_{n-k}(1, …, k)`), for `k ≤ n` (implicit in
DLMF: for `k > n` the left side is `0`). -/
@[dlmf 26.8.E5]
theorem stirlingSecond_eq_sum_antidiagonalTuple {n k : ℕ} (hkn : k ≤ n) :
    (Nat.stirlingSecond n k : ℤ) =
      ∑ c ∈ Finset.Nat.antidiagonalTuple k (n - k), ∏ i : Fin k, ((i : ℤ) + 1) ^ (c i) := by
  obtain ⟨d, rfl⟩ : ∃ d, n = k + d := ⟨n - k, by omega⟩
  rw [q26a_stirlingSecond_eq_hRev, Nat.add_sub_cancel_left, q26a_hRev]
  refine sum_nbij' (fun c => c ∘ Fin.rev) (fun c => c ∘ Fin.rev) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    simp only [Finset.Nat.mem_antidiagonalTuple] at hc ⊢
    rw [← hc]; exact Fintype.sum_equiv Fin.revPerm _ _ (fun i => rfl)
  · intro c hc
    simp only [Finset.Nat.mem_antidiagonalTuple] at hc ⊢
    rw [← hc]; exact Fintype.sum_equiv Fin.revPerm _ _ (fun i => rfl)
  · intro c _; ext i; simp
  · intro c _; ext i; simp
  · intro c _
    refine Fintype.prod_equiv Fin.revPerm _ _ (fun i => ?_)
    simp only [Function.comp_apply, Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
    congr 1
    have := i.isLt
    rw [Nat.cast_sub (by omega)]; push_cast; ring

/-- The `k`-th forward difference of `x ↦ xⁿ` at `0` is `k! S(n, k)`. -/
lemma q26a_fwdDiff_iter_pow (n k : ℕ) :
    (fwdDiff 1)^[k] (fun x : ℕ => ((x : ℚ) ^ n)) 0 = k.factorial * Nat.stirlingSecond n k := by
  have hf : (fun x : ℕ => ((x : ℚ) ^ n)) = ∑ i ∈ range (n + 1),
      ((Nat.stirlingSecond n i * i.factorial : ℕ) : ℚ) • (fun x : ℕ => (x.choose i : ℚ)) := by
    ext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Nat.cast_pow, Nat.pow_eq_sum_stirlingSecond_mul_descFactorial]
    push_cast
    refine sum_congr rfl fun i _ => ?_
    rw [Nat.descFactorial_eq_factorial_mul_choose]; push_cast; ring
  rw [hf, fwdDiff_iter_finsetSum]
  simp only [Finset.sum_apply, fwdDiff_iter_const_smul, Pi.smul_apply, fwdDiff_iter_choose_zero,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · push_cast; ring
  · rw [Nat.stirlingSecond_eq_zero_of_lt (by simp at h; omega)]; simp

/-- `∑_j (-1)^{k-j} C(k, j) jⁿ = k! S(n, k)`. -/
lemma q26a_sum_alt_choose_pow (n k : ℕ) :
    ∑ j ∈ range (k + 1), (-1 : ℚ) ^ (k - j) * (k.choose j : ℚ) * (j : ℚ) ^ n =
      k.factorial * Nat.stirlingSecond n k := by
  have h := q26a_fwdDiff_iter_pow n k
  rw [fwdDiff_iter_eq_sum_shift] at h
  simp only [zero_add, nsmul_eq_mul, mul_one, zsmul_eq_mul] at h
  push_cast at h
  exact h

/-- DLMF 26.8.6: `S(n, k) = (1/k!) ∑_{j=0}^{k} (-1)^{k-j} C(k, j) jⁿ` (all `n, k ≥ 0`, with
`0⁰ = 1`). -/
@[dlmf 26.8.E6]
theorem stirlingSecond_eq_sum (n k : ℕ) :
    (Nat.stirlingSecond n k : ℚ) =
      (1 / k.factorial) * ∑ j ∈ range (k + 1), (-1) ^ (k - j) * (k.choose j : ℚ) * (j : ℚ) ^ n := by
  rw [q26a_sum_alt_choose_pow]
  have : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  field_simp

/-! ### The falling factorial (§26.8(ii)) -/

/-- The coefficients of the falling factorial `x(x-1)⋯(x-n+1)` are the signed Stirling numbers
of the first kind. -/
theorem coeff_descPochhammer (n k : ℕ) :
    (descPochhammer ℤ n).coeff k = signedStirlingFirst n k := by
  induction n generalizing k with
  | zero =>
    rcases k with _ | k <;> simp [Polynomial.coeff_one]
  | succ n ih =>
    rw [descPochhammer_succ_right, mul_sub, coeff_sub, ← C_eq_natCast, coeff_mul_C]
    rcases k with _ | k
    · rw [coeff_mul_X_zero, ih]
      rcases n with _ | n <;> simp
    · rw [coeff_mul_X, ih, ih, signedStirlingFirst_succ_succ]; ring

/-- The falling factorial as a sum of monomials with the coefficients `s(n, k)`. -/
theorem descPochhammer_eq_sum (R : Type*) [CommRing R] (n : ℕ) :
    descPochhammer R n =
      ∑ k ∈ range (n + 1), C (signedStirlingFirst n k : R) * X ^ k := by
  rw [← descPochhammer_map (Int.castRingHom R)]
  conv_lhs => rw [(descPochhammer ℤ n).as_sum_range' (n + 1) (by simp)]
  simp [Polynomial.map_sum, coeff_descPochhammer, ← C_mul_X_pow_eq_monomial]

/-- DLMF 26.8.7: `∑_{k=0}^n s(n, k) x^k = (x-n+1)_n`, the rising factorial (Pochhammer
symbol) at `x - n + 1`, i.e. the falling factorial `x(x-1)⋯(x-n+1)`. Stated in any commutative
ring (DLMF: real `x`). -/
@[dlmf 26.8.E7]
theorem sum_signedStirlingFirst_mul_pow {R : Type*} [CommRing R] (n : ℕ) (x : R) :
    ∑ k ∈ range (n + 1), (signedStirlingFirst n k : R) * x ^ k =
      (ascPochhammer R n).eval (x - n + 1) := by
  rw [← descPochhammer_eval_eq_ascPochhammer, descPochhammer_eq_sum, eval_finsetSum]
  simp

/-- The integer polynomial identity `Xⁿ = ∑_k S(n, k) · X(X-1)⋯(X-k+1)`. -/
lemma c26a_X_pow_eq_sum_descPochhammer (n : ℕ) :
    (X : ℤ[X]) ^ n = ∑ k ∈ range (n + 1), C (Nat.stirlingSecond n k : ℤ) * descPochhammer ℤ k := by
  rw [← sub_eq_zero]
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply Set.Infinite.mono _ (Set.infinite_range_of_injective (Nat.cast_injective (R := ℤ)))
  rintro _ ⟨m, rfl⟩
  simp only [Set.mem_ofPred_eq, IsRoot, eval_sub, eval_pow, eval_X, eval_finsetSum, eval_mul,
    eval_C, descPochhammer_eval_eq_descFactorial, sub_eq_zero]
  exact_mod_cast Nat.pow_eq_sum_stirlingSecond_mul_descFactorial m n

/-- The polynomial identity `Xⁿ = ∑_k S(n, k) · X(X-1)⋯(X-k+1)` over any commutative ring. -/
theorem X_pow_eq_sum_stirlingSecond_mul_descPochhammer (R : Type*) [CommRing R] (n : ℕ) :
    (X : R[X]) ^ n =
      ∑ k ∈ range (n + 1), C (Nat.stirlingSecond n k : R) * descPochhammer R k := by
  have := congrArg (Polynomial.map (Int.castRingHom R)) (c26a_X_pow_eq_sum_descPochhammer n)
  simpa [Polynomial.map_sum, descPochhammer_map] using this

/-- DLMF 26.8.10, `k = 0` form: `∑_{k=0}^n S(n, k) (x-k+1)_k = xⁿ` for all `n ≥ 0`. -/
@[dlmf 26.8.E10]
theorem sum_range_stirlingSecond_mul_ascPochhammer {R : Type*} [CommRing R] (n : ℕ) (x : R) :
    ∑ k ∈ range (n + 1), (Nat.stirlingSecond n k : R) * (ascPochhammer R k).eval (x - k + 1) =
      x ^ n := by
  have := congrArg (Polynomial.eval x) (X_pow_eq_sum_stirlingSecond_mul_descPochhammer R n)
  simp only [eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C,
    descPochhammer_eval_eq_ascPochhammer] at this
  exact this.symm

/-- DLMF 26.8.10: `∑_{k=1}^n S(n, k) (x-k+1)_k = xⁿ`, for `n ≥ 1`. **Correction (implicit
condition):** for `n = 0` the printed sum is empty and the identity fails (`0 ≠ 1`); see
`sum_range_stirlingSecond_mul_ascPochhammer` for the form valid for all `n`. -/
@[dlmf 26.8.E10]
theorem sum_Icc_stirlingSecond_mul_ascPochhammer {R : Type*} [CommRing R] {n : ℕ} (hn : 1 ≤ n)
    (x : R) :
    ∑ k ∈ Icc 1 n, (Nat.stirlingSecond n k : R) * (ascPochhammer R k).eval (x - k + 1) = x ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [← sum_range_stirlingSecond_mul_ascPochhammer (m + 1) x, range_eq_Ico,
    sum_eq_sum_Ico_succ_bot (by omega),
    show Ico (0 + 1) (m + 1 + 1) = Icc 1 (m + 1) by ext; simp]
  simp [Nat.stirlingSecond_succ_zero]

/-! ### Generating functions (§26.8(ii)) -/

/-! #### Helpers for 26.8.8–9 (agent p26a) -/

/-- Coefficients of an everywhere absolutely convergent real power series are unique. -/
lemma s26a_coeff_unique {a b : ℕ → ℝ} (ha : ∀ r : NNReal, Summable fun k => |a k| * (r : ℝ) ^ k)
    (hb : ∀ r : NNReal, Summable fun k => |b k| * (r : ℝ) ^ k)
    (h : ∀ y : ℝ, ∑' k, a k * y ^ k = ∑' k, b k * y ^ k) : a = b := by
  have hrad : ∀ c : ℕ → ℝ, (∀ r : NNReal, Summable fun k => |c k| * (r : ℝ) ^ k) →
      (FormalMultilinearSeries.ofScalars ℝ c).radius = ⊤ := by
    intro c hc
    refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
    refine FormalMultilinearSeries.le_radius_of_summable_norm _ ?_
    simpa [FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs] using hc r
  have hser : ∀ c : ℕ → ℝ, (∀ r : NNReal, Summable fun k => |c k| * (r : ℝ) ^ k) →
      HasFPowerSeriesAt (fun y : ℝ => ∑' k, c k * y ^ k)
        (FormalMultilinearSeries.ofScalars ℝ c) 0 := by
    intro c hc
    have := (FormalMultilinearSeries.ofScalars ℝ c).hasFPowerSeriesOnBall
      (by rw [hrad c hc]; exact ENNReal.zero_lt_top)
    convert this.hasFPowerSeriesAt using 1
    ext y
    change _ = FormalMultilinearSeries.ofScalarsSum c y
    rw [FormalMultilinearSeries.ofScalars_sum_eq]
    simp [smul_eq_mul]
  have h1 := hser a ha
  have h2 := hser b hb
  rw [show (fun y : ℝ => ∑' k, a k * y ^ k) = fun y => ∑' k, b k * y ^ k from funext h] at h1
  exact FormalMultilinearSeries.ofScalars_series_injective ℝ ℝ (h1.eq_formalMultilinearSeries h2)

/-- `∑_k c(n, k) aᵏ = a(a+1)⋯(a+n-1)` (unsigned Stirling numbers of the first kind). -/
lemma s26a_sum_stirlingFirst_mul_pow (n : ℕ) (a : ℝ) :
    ∑ k ∈ range (n + 1), (Nat.stirlingFirst n k : ℝ) * a ^ k = (ascPochhammer ℝ n).eval a := by
  have h := descPochhammer_eq_sum ℝ n
  have h2 := congrArg (Polynomial.eval (-a)) h
  rw [eval_finsetSum] at h2
  have h3 := ascPochhammer_eval_neg_eq_descPochhammer (R := ℝ) (-a) n
  rw [neg_neg, h2] at h3
  rw [h3, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  simp only [mem_range] at hk
  simp only [eval_mul, eval_C, eval_pow, eval_X, signedStirlingFirst, Int.cast_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
  have hnk : (-1 : ℝ) ^ (n - k) = (-1) ^ n * (-1) ^ k := by
    have : (-1 : ℝ) ^ n = (-1) ^ (n - k) * (-1) ^ k := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    rw [this, mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
  rw [hnk, neg_pow a k]
  have hP : ((-1 : ℝ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have hQ : ((-1 : ℝ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  linear_combination (-((Nat.stirlingFirst n k : ℝ) * a ^ k)) * hP -
    (Nat.stirlingFirst n k : ℝ) * a ^ k * ((-1 : ℝ) ^ n) ^ 2 * hQ

/-- The generalized binomial coefficient over `ℝ` as a falling factorial over `n!`. -/
lemma s26a_ringChoose_eq (r : ℝ) (n : ℕ) :
    Ring.choose r n = (descPochhammer ℝ n).eval r / n.factorial := by
  rw [Ring.choose_eq_smul, ← Polynomial.aeval_eq_smeval, Polynomial.aeval_def,
    ← Polynomial.eval_map, descPochhammer_map, smul_eq_mul, div_eq_inv_mul]

/-- The binomial series `∑ binom(y, n) xⁿ = (1+x)^y`, real `|x| < 1`. -/
lemma s26a_hasSum_ringChoose_mul_pow {x : ℝ} (hx : |x| < 1) (y : ℝ) :
    HasSum (fun n : ℕ => Ring.choose y n * x ^ n) ((1 + x) ^ y) := by
  have hb := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := y)).hasSum (y := x) (by
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm, Real.norm_eq_abs]
    rwa [ENNReal.ofReal_lt_one])
  simp only [binomialSeries_apply, List.ofFn_const, List.prod_replicate, smul_eq_mul,
    zero_add] at hb
  exact hb

/-- `∑ binom(a+n-1, n) tⁿ = (1-t)^{-a}`, real `|t| < 1`. -/
lemma s26a_hasSum_ringChoose_add_mul_pow {t : ℝ} (ht : |t| < 1) (a : ℝ) :
    HasSum (fun n : ℕ => Ring.choose (a + n - 1) n * t ^ n) (1 / (1 - t) ^ a) := by
  have hb := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero a).hasSum (y := t) (by
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm, Real.norm_eq_abs]
    rwa [ENNReal.ofReal_lt_one])
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] at hb
  exact hb

/-- The rows of the bivariate series 26.8.9. -/
lemma s26a_hasSum_signedStirlingFirst_row (x y : ℝ) (n : ℕ) :
    HasSum (fun k : ℕ => (signedStirlingFirst n k : ℝ) * x ^ n / n.factorial * y ^ k)
      (Ring.choose y n * x ^ n) := by
  have h : HasSum (fun k : ℕ => (signedStirlingFirst n k : ℝ) * x ^ n / n.factorial * y ^ k)
      (∑ k ∈ range (n + 1), (signedStirlingFirst n k : ℝ) * x ^ n / n.factorial * y ^ k) :=
    hasSum_sum_of_ne_finset_zero fun k hk => by
      rw [signedStirlingFirst_eq_zero_of_lt (by simp at hk; omega)]; simp
  convert h using 1
  have h2 := congrArg (Polynomial.eval y) (descPochhammer_eq_sum ℝ n)
  rw [eval_finsetSum] at h2
  rw [s26a_ringChoose_eq, h2, sum_div, sum_mul]
  refine sum_congr rfl fun k _ => ?_
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  ring

/-- The absolute rows of the bivariate series 26.8.9. -/
lemma s26a_hasSum_signedStirlingFirst_row_abs (x y : ℝ) (n : ℕ) :
    HasSum (fun k : ℕ => |(signedStirlingFirst n k : ℝ) * x ^ n / n.factorial * y ^ k|)
      (Ring.choose (|y| + n - 1) n * |x| ^ n) := by
  have h : HasSum (fun k : ℕ => |(signedStirlingFirst n k : ℝ) * x ^ n / n.factorial * y ^ k|)
      (∑ k ∈ range (n + 1), |(signedStirlingFirst n k : ℝ) * x ^ n / n.factorial * y ^ k|) :=
    hasSum_sum_of_ne_finset_zero fun k hk => by
      rw [signedStirlingFirst_eq_zero_of_lt (by simp at hk; omega)]; simp
  convert h using 1
  rw [s26a_ringChoose_eq, descPochhammer_eval_eq_ascPochhammer,
    show |y| + n - 1 - n + 1 = |y| by ring, ← s26a_sum_stirlingFirst_mul_pow, sum_div, sum_mul]
  refine sum_congr rfl fun k _ => ?_
  simp only [signedStirlingFirst, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast, abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    Nat.abs_cast]
  ring

/-- The double series 26.8.9 converges absolutely. -/
lemma s26a_summable_abs_signedStirlingFirst_bivariate {x : ℝ} (hx : |x| < 1) (y : ℝ) :
    Summable (fun p : ℕ × ℕ => |(signedStirlingFirst p.1 p.2 : ℝ) * x ^ p.1 / p.1.factorial *
      y ^ p.2|) := by
  refine (summable_prod_of_nonneg fun _ => abs_nonneg _).mpr
    ⟨fun n => (s26a_hasSum_signedStirlingFirst_row_abs x y n).summable, ?_⟩
  simp_rw [fun n => (s26a_hasSum_signedStirlingFirst_row_abs x y n).tsum_eq]
  exact (s26a_hasSum_ringChoose_add_mul_pow (t := |x|) (by rwa [abs_abs]) |y|).summable

/-- The double series 26.8.9 is summable. -/
lemma s26a_summable_signedStirlingFirst_bivariate {x : ℝ} (hx : |x| < 1) (y : ℝ) :
    Summable (fun p : ℕ × ℕ => (signedStirlingFirst p.1 p.2 : ℝ) * x ^ p.1 / p.1.factorial *
      y ^ p.2) :=
  Summable.of_norm (by simpa only [Real.norm_eq_abs] using
    s26a_summable_abs_signedStirlingFirst_bivariate hx y)

/-- DLMF 26.8.9 (helper). -/
lemma s26a_hasSum_signedStirlingFirst_bivariate {x : ℝ} (hx : |x| < 1) (y : ℝ) :
    HasSum (fun p : ℕ × ℕ => (signedStirlingFirst p.1 p.2 : ℝ) * x ^ p.1 / p.1.factorial *
      y ^ p.2) ((1 + x) ^ y) := by
  have hs := s26a_summable_signedStirlingFirst_bivariate hx y
  have h1 := hs.hasSum.prod_fiberwise (s26a_hasSum_signedStirlingFirst_row x y)
  rw [← h1.unique (s26a_hasSum_ringChoose_mul_pow hx y)]
  exact hs.hasSum

/-- DLMF 26.8.8 (helper). -/
lemma s26a_hasSum_signedStirlingFirst_div_factorial (k : ℕ) {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => (signedStirlingFirst n k : ℝ) * x ^ n / n.factorial)
      (Real.log (1 + x) ^ k / k.factorial) := by
  set A : ℕ → ℝ := fun k => ∑' n : ℕ, (signedStirlingFirst n k : ℝ) * x ^ n / n.factorial
    with hAdef
  have hcol : ∀ k, Summable (fun n : ℕ => (signedStirlingFirst n k : ℝ) * x ^ n /
      n.factorial) := by
    intro k
    have h2 := ((Equiv.prodComm ℕ ℕ).summable_iff.mpr
      (s26a_summable_signedStirlingFirst_bivariate hx 1)).prod_factor k
    simpa using h2
  have hA : ∀ y : ℝ, HasSum (fun k => A k * y ^ k) ((1 + x) ^ y) := by
    intro y
    have hG' := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr
      (s26a_hasSum_signedStirlingFirst_bivariate hx y)
    refine hG'.prod_fiberwise fun k => ?_
    simpa [A] using (hcol k).hasSum.mul_right (y ^ k)
  set L := Real.log (1 + x)
  have h1x : 0 < 1 + x := by linarith [neg_abs_le x]
  have hB : ∀ y : ℝ, HasSum (fun k => L ^ k / k.factorial * y ^ k) ((1 + x) ^ y) := by
    intro y
    rw [Real.rpow_def_of_pos h1x]
    have := NormedSpace.expSeries_div_hasSum_exp (L * y)
    rw [← Real.exp_eq_exp_ℝ] at this
    convert this using 1; ext k; rw [mul_pow]; ring
  have ha : ∀ r : NNReal, Summable fun k => |A k| * (r : ℝ) ^ k := by
    intro r
    have hS := (Equiv.prodComm ℕ ℕ).summable_iff.mpr
      (s26a_summable_abs_signedStirlingFirst_bivariate hx (r : ℝ))
    have hS2 := ((summable_prod_of_nonneg fun _ => abs_nonneg _).mp hS).2
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun k => ?_) hS2
    show |A k| * (r : ℝ) ^ k ≤ ∑' n : ℕ, |(signedStirlingFirst n k : ℝ) * x ^ n /
      n.factorial * (r : ℝ) ^ k|
    have hr : (0 : ℝ) ≤ r := r.2
    have h1 : |A k| ≤ ∑' n : ℕ, |(signedStirlingFirst n k : ℝ) * x ^ n / n.factorial| := by
      have := norm_tsum_le_tsum_norm (f := fun n : ℕ => (signedStirlingFirst n k : ℝ) * x ^ n /
        n.factorial) (by simpa only [Real.norm_eq_abs] using (hcol k).abs)
      simpa only [Real.norm_eq_abs] using this
    have h2 : ∑' n : ℕ, |(signedStirlingFirst n k : ℝ) * x ^ n / n.factorial * (r : ℝ) ^ k| =
        (∑' n : ℕ, |(signedStirlingFirst n k : ℝ) * x ^ n / n.factorial|) * (r : ℝ) ^ k := by
      rw [← tsum_mul_right]
      refine tsum_congr fun n => ?_
      rw [abs_mul, abs_pow, abs_of_nonneg hr]
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hb : ∀ r : NNReal, Summable fun k => |L ^ k / k.factorial| * (r : ℝ) ^ k := by
    intro r
    have := Real.summable_pow_div_factorial (|L| * r)
    convert this using 1; ext k
    rw [abs_div, abs_pow, Nat.abs_cast, mul_pow]; ring
  have huniq := s26a_coeff_unique ha hb fun y => (hA y).tsum_eq.trans (hB y).tsum_eq.symm
  rw [show L ^ k / k.factorial = A k from (congrFun huniq k).symm]
  exact (hcol k).hasSum


/-- DLMF 26.8.8: `∑_{n=0}^∞ s(n, k) xⁿ/n! = (ln(1+x))^k / k!`, real `|x| < 1`. -/
@[dlmf 26.8.E8]
theorem hasSum_signedStirlingFirst_div_factorial (k : ℕ) {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => (signedStirlingFirst n k : ℝ) * x ^ n / n.factorial)
      (Real.log (1 + x) ^ k / k.factorial) :=
  s26a_hasSum_signedStirlingFirst_div_factorial k hx

/-- DLMF 26.8.9: `∑_{n,k=0}^∞ s(n, k) (xⁿ/n!) y^k = (1+x)^y`, real `|x| < 1`, real `y` (the
double series converges absolutely). -/
@[dlmf 26.8.E9]
theorem hasSum_signedStirlingFirst_bivariate {x : ℝ} (hx : |x| < 1) (y : ℝ) :
    HasSum (fun p : ℕ × ℕ => (signedStirlingFirst p.1 p.2 : ℝ) * x ^ p.1 / p.1.factorial * y ^ p.2)
      ((1 + x) ^ y) :=
  s26a_hasSum_signedStirlingFirst_bivariate hx y

/-- The series `∑ S(n, k) xⁿ` converges for `k|x| < 1` (from 26.8.6). -/
lemma q26a_summable_stirlingSecond_mul_pow (k : ℕ) {x : ℝ} (hx : k * |x| < 1) :
    Summable (fun n : ℕ => (Nat.stirlingSecond n k : ℝ) * x ^ n) := by
  have hc : ∀ n, (Nat.stirlingSecond n k : ℝ) * x ^ n = ∑ j ∈ range (k + 1),
      (1 / k.factorial : ℝ) * ((-1 : ℝ) ^ (k - j) * (k.choose j : ℝ)) * ((j : ℝ) * x) ^ n := by
    intro n
    have := congrArg (Rat.cast : ℚ → ℝ) (stirlingSecond_eq_sum n k)
    push_cast at this
    rw [this, mul_sum, sum_mul]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_pow]; ring
  simp_rw [hc]
  refine summable_sum fun j hj => (summable_geometric_of_abs_lt_one ?_).mul_left _
  have hj : (j : ℝ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [abs_mul, Nat.abs_cast]
  calc (j : ℝ) * |x| ≤ k * |x| := mul_le_mul_of_nonneg_right hj (abs_nonneg x)
    _ < 1 := hx

/-- DLMF 26.8.11: `∑_{n=0}^∞ S(n, k) xⁿ = x^k / ((1-x)(1-2x)⋯(1-kx))`, real `|x| < 1/k`
(written `k|x| < 1`, which for `k = 0` allows every `x`, where both sides are `1`). -/
@[dlmf 26.8.E11]
theorem hasSum_stirlingSecond_mul_pow (k : ℕ) {x : ℝ} (hx : k * |x| < 1) :
    HasSum (fun n : ℕ => (Nat.stirlingSecond n k : ℝ) * x ^ n)
      (x ^ k / ∏ j ∈ Icc 1 k, (1 - j * x)) := by
  induction k generalizing x with
  | zero =>
    convert hasSum_ite_eq 0 (1 : ℝ) using 1
    · ext n
      rcases n with _ | n <;> simp [Nat.stirlingSecond_succ_zero]
    · simp
  | succ k ih =>
    have hx' : (k : ℝ) * |x| < 1 := by
      have : (k : ℝ) * |x| ≤ (k + 1 : ℕ) * |x| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg x); push_cast; linarith
      linarith
    have hA := (q26a_summable_stirlingSecond_mul_pow (k + 1) hx).hasSum
    set A := ∑' n : ℕ, (Nat.stirlingSecond n (k + 1) : ℝ) * x ^ n
    have h1 := (hasSum_nat_add_iff' 1).mpr hA
    simp only [range_one, sum_singleton, Nat.stirlingSecond_zero_succ, Nat.cast_zero, zero_mul,
      sub_zero] at h1
    have h2 : HasSum (fun n : ℕ => (Nat.stirlingSecond (n + 1) (k + 1) : ℝ) * x ^ (n + 1))
        ((k + 1) * x * A + x * (x ^ k / ∏ j ∈ Icc 1 k, (1 - j * x))) := by
      have := (hA.mul_left ((k + 1) * x)).add ((ih hx').mul_left x)
      convert this using 1
      ext n
      rw [Nat.stirlingSecond_succ_succ]; push_cast; ring
    have hAeq := h1.unique h2
    have hpos : 0 < 1 - ((k + 1 : ℕ) : ℝ) * x := by
      have := le_abs_self x
      have : ((k + 1 : ℕ) : ℝ) * x ≤ ((k + 1 : ℕ) : ℝ) * |x| :=
        mul_le_mul_of_nonneg_left (le_abs_self x) (by positivity)
      linarith
    have hP : 0 < ∏ j ∈ Icc 1 k, (1 - (j : ℝ) * x) := by
      refine prod_pos fun j hj => ?_
      have hj : (j : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hj).2
      have : (j : ℝ) * x ≤ k * |x| := by
        calc (j : ℝ) * x ≤ j * |x| := mul_le_mul_of_nonneg_left (le_abs_self x) (by positivity)
          _ ≤ k * |x| := mul_le_mul_of_nonneg_right hj (abs_nonneg x)
      linarith
    rw [prod_Icc_succ_top (by omega), pow_succ]
    convert hA using 1
    rw [eq_comm, eq_div_iff (by positivity)]
    have h3 : A * (1 - ((k + 1 : ℕ) : ℝ) * x) = x * (x ^ k / ∏ j ∈ Icc 1 k, (1 - (j : ℝ) * x)) := by
      push_cast; linarith
    calc A * ((∏ j ∈ Icc 1 k, (1 - (j : ℝ) * x)) * (1 - ((k + 1 : ℕ) : ℝ) * x))
        = (A * (1 - ((k + 1 : ℕ) : ℝ) * x)) * ∏ j ∈ Icc 1 k, (1 - (j : ℝ) * x) := by ring
      _ = x ^ k * x := by rw [h3, mul_div_assoc', div_mul_cancel₀ _ hP.ne']; ring

/-- DLMF 26.8.12: `∑_{n=0}^∞ S(n, k) xⁿ/n! = (eˣ - 1)^k / k!`, all real `x`. -/
@[dlmf 26.8.E12]
theorem hasSum_stirlingSecond_div_factorial (k : ℕ) (x : ℝ) :
    HasSum (fun n : ℕ => (Nat.stirlingSecond n k : ℝ) * x ^ n / n.factorial)
      ((Real.exp x - 1) ^ k / k.factorial) := by
  have hc : ∀ n, (Nat.stirlingSecond n k : ℝ) = (1 / k.factorial) *
      ∑ j ∈ range (k + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * (j : ℝ) ^ n := by
    intro n
    have := congrArg (Rat.cast : ℚ → ℝ) (stirlingSecond_eq_sum n k)
    push_cast at this
    exact this
  have hs := hasSum_sum (s := range (k + 1)) fun j _ =>
    (NormedSpace.expSeries_div_hasSum_exp ((j : ℝ) * x)).mul_left
      ((1 / k.factorial : ℝ) * ((-1 : ℝ) ^ (k - j) * (k.choose j : ℝ)))
  have hv : ∑ j ∈ range (k + 1), (1 / k.factorial : ℝ) * ((-1 : ℝ) ^ (k - j) * (k.choose j : ℝ)) *
      NormedSpace.exp ((j : ℝ) * x) = (Real.exp x - 1) ^ k / k.factorial := by
    rw [sub_eq_add_neg, add_pow, sum_div]
    refine sum_congr rfl fun j _ => ?_
    rw [← Real.exp_eq_exp_ℝ, Real.exp_nat_mul]
    ring
  rw [hv] at hs
  convert hs using 1
  ext n
  rw [hc, mul_sum, sum_mul, sum_div]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_pow]; ring

/-- DLMF 26.8.13: `∑_{n,k=0}^∞ S(n, k) (xⁿ/n!) y^k = exp(y(eˣ - 1))`, all real `x, y` (the
double series converges absolutely). -/
@[dlmf 26.8.E13]
theorem hasSum_stirlingSecond_bivariate (x y : ℝ) :
    HasSum (fun p : ℕ × ℕ => (Nat.stirlingSecond p.1 p.2 : ℝ) * x ^ p.1 / p.1.factorial * y ^ p.2)
      (Real.exp (y * (Real.exp x - 1))) := by
  -- the fibers over the second index
  have hfib : ∀ (x y : ℝ) (k : ℕ), HasSum
      (fun n : ℕ => (Nat.stirlingSecond n k : ℝ) * x ^ n / n.factorial * y ^ k)
      ((y * (Real.exp x - 1)) ^ k / k.factorial) := by
    intro x y k
    have := (hasSum_stirlingSecond_div_factorial k x).mul_right (y ^ k)
    convert this using 1; rw [mul_pow]; ring
  set G : ℕ × ℕ → ℝ := fun q => (Nat.stirlingSecond q.2 q.1 : ℝ) * x ^ q.2 / q.2.factorial * y ^ q.1
  have hnorm : ∀ q,
      ‖G q‖ = (Nat.stirlingSecond q.2 q.1 : ℝ) * |x| ^ q.2 / q.2.factorial * |y| ^ q.1 := by
    intro q
    simp only [G, Real.norm_eq_abs, abs_mul, abs_div, abs_pow, Nat.abs_cast]
  have hsG : Summable G := by
    apply Summable.of_norm
    simp_rw [hnorm]
    rw [summable_prod_of_nonneg (fun q => by positivity)]
    refine ⟨fun k => (hfib |x| |y| k).summable, ?_⟩
    simp_rw [(hfib |x| |y| _).tsum_eq]
    exact (NormedSpace.expSeries_div_summable (|y| * (Real.exp |x| - 1) : ℝ))
  have hG := hsG.hasSum
  have h2 := hG.prod_fiberwise fun k => hfib x y k
  have h3 := NormedSpace.expSeries_div_hasSum_exp (y * (Real.exp x - 1))
  rw [← Real.exp_eq_exp_ℝ] at h3
  rw [h2.unique h3] at hG
  have := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hG
  convert this using 1
  ext p; simp [G]

/-! ### Special values (§26.8(iii)) -/

/-- DLMF 26.8.14 (first): `s(n, 0) = 0` for `n ≥ 1`. -/
@[dlmf 26.8.E14]
theorem signedStirlingFirst_zero_right {n : ℕ} (hn : 1 ≤ n) : signedStirlingFirst n 0 = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp

/-- DLMF 26.8.14 (second): `s(n, 1) = (-1)^{n-1} (n-1)!` for `n ≥ 1`. -/
@[dlmf 26.8.E14]
theorem signedStirlingFirst_one_right {n : ℕ} (hn : 1 ≤ n) :
    signedStirlingFirst n 1 = (-1) ^ (n - 1) * ((n - 1).factorial : ℤ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [signedStirlingFirst, Nat.stirlingFirst_one_right]

/-- The unsigned `c(n+1, 2) = n! H_n`. -/
lemma c26a_stirlingFirst_two (n : ℕ) :
    (Nat.stirlingFirst (n + 1) 2 : ℚ) = n.factorial * harmonic n := by
  induction n with
  | zero => simp [Nat.stirlingFirst_eq_zero_of_lt]
  | succ n ih =>
    rw [Nat.stirlingFirst_succ_succ, Nat.stirlingFirst_one_right]
    push_cast
    rw [ih, harmonic_succ, Nat.factorial_succ]
    push_cast
    field_simp

/-- DLMF 26.8.15: `s(n, 2) = (-1)ⁿ (n-1)! (1 + 1/2 + ⋯ + 1/(n-1))` for `n ≥ 1`
(`harmonic (n-1)` is the harmonic number `H_{n-1}`). -/
@[dlmf 26.8.E15]
theorem signedStirlingFirst_two_right {n : ℕ} (hn : 1 ≤ n) :
    (signedStirlingFirst n 2 : ℚ) = (-1) ^ n * (n - 1).factorial * harmonic (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases m with _ | m
  · simp [signedStirlingFirst, Nat.stirlingFirst_eq_zero_of_lt]
  · simp only [signedStirlingFirst, Nat.add_sub_cancel]
    push_cast
    rw [c26a_stirlingFirst_two, pow_succ, pow_succ]
    ring

/-- DLMF 26.8.16: `-s(n, n-1) = S(n, n-1) = C(n, 2)` for `n ≥ 1`. -/
@[dlmf 26.8.E16]
theorem neg_signedStirlingFirst_pred_self {n : ℕ} (hn : 1 ≤ n) :
    -signedStirlingFirst n (n - 1) = Nat.stirlingSecond n (n - 1) ∧
      (Nat.stirlingSecond n (n - 1) : ℤ) = n.choose 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel, signedStirlingFirst, Nat.stirlingFirst_succ_self_left,
    Nat.stirlingSecond_succ_self_left, show m + 1 - m = 1 by omega]
  simp

/-- DLMF 26.8.17 (first two): `S(n, 0) = 0` and `S(n, 1) = 1` for `n ≥ 1`. -/
@[dlmf 26.8.E17]
theorem stirlingSecond_zero_one_right {n : ℕ} (hn : 1 ≤ n) :
    Nat.stirlingSecond n 0 = 0 ∧ Nat.stirlingSecond n 1 = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact ⟨Nat.stirlingSecond_succ_zero m, Nat.stirlingSecond_one_right m⟩

/-- DLMF 26.8.17 (third): `S(n, 2) = 2^{n-1} - 1` for `n ≥ 1`. -/
@[dlmf 26.8.E17]
theorem stirlingSecond_two_right {n : ℕ} (hn : 1 ≤ n) :
    (Nat.stirlingSecond n 2 : ℤ) = 2 ^ (n - 1) - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  induction m with
  | zero => simp [Nat.stirlingSecond_eq_zero_of_lt]
  | succ m ih =>
    rw [Nat.stirlingSecond_succ_succ, Nat.stirlingSecond_one_right]
    push_cast
    rw [ih (by omega)]
    simp only [Nat.add_sub_cancel]
    ring

/-! ### Recurrence relations (§26.8(iv)) -/

/-- The falling factorial evaluated (`smeval`) in a commutative ring, as `∑_k s(n,k) rᵏ`. -/
lemma r26a_smeval_descPochhammer {R : Type*} [CommRing R] (n : ℕ) (r : R) :
    (descPochhammer ℤ n).smeval r = ∑ k ∈ range (n + 1), (signedStirlingFirst n k : R) * r ^ k := by
  rw [← aeval_eq_smeval, aeval_eq_sum_range' (n := n + 1) (by simp [descPochhammer_natDegree])]
  simp [coeff_descPochhammer, zsmul_eq_mul]

/-- The double coefficient `[Yᵐ][Xʰ]` of `c · Xᵃ Yᵇ` in `ℤ[X][Y]`. -/
lemma r26a_coeff_coeff (c : ℤ) (a b h m : ℕ) :
    (((c : ℤ[X][X]) * (C X) ^ a * X ^ b).coeff m).coeff h =
      if a = h ∧ b = m then c else 0 := by
  rw [← C_pow, show ((c : ℤ[X][X])) = C (c : ℤ[X]) by simp, ← C_mul, coeff_C_mul_X_pow]
  split_ifs with h1 h2 h2 <;> simp_all [coeff_intCast_mul, coeff_X_pow]
  · omega

/-- DLMF 26.8.19: `C(k, h) s(n, k) = ∑_{j=k-h}^{n-h} C(n, j) s(n-j, h) s(j, k-h)`,
`n ≥ k ≥ h`. -/
@[dlmf 26.8.E19]
theorem choose_mul_signedStirlingFirst {n k h : ℕ} (hkn : k ≤ n) (hhk : h ≤ k) :
    (k.choose h : ℤ) * signedStirlingFirst n k =
      ∑ j ∈ Icc (k - h) (n - h),
        (n.choose j : ℤ) * signedStirlingFirst (n - j) h * signedStirlingFirst j (k - h) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = h + m := ⟨k - h, by omega⟩
  have hV := Ring.descPochhammer_smeval_add (R := ℤ[X][X]) (r := C X) (s := X) n (Commute.all _ _)
  have hφ := congrArg (fun p : ℤ[X][X] => (p.coeff m).coeff h) hV
  simp only [r26a_smeval_descPochhammer, add_pow, mul_sum, sum_mul, finsetSum_coeff] at hφ
  have hL : ∀ x ∈ range (n + 1), ∑ i ∈ range (x + 1),
      (((signedStirlingFirst n x : ℤ[X][X]) *
        (C X ^ i * X ^ (x - i) * (x.choose i : ℤ[X][X]))).coeff
        m).coeff h = if x = h + m then (x.choose h : ℤ) * signedStirlingFirst n x else 0 := by
    intro x _
    have : ∀ i ∈ range (x + 1),
        (((signedStirlingFirst n x : ℤ[X][X]) * (C X ^ i * X ^ (x - i) *
          (x.choose i : ℤ[X][X]))).coeff m).coeff h =
        if i = h then (if x = h + m then (x.choose h : ℤ) * signedStirlingFirst n x else 0)
          else 0 := by
      intro i hi
      rw [show (signedStirlingFirst n x : ℤ[X][X]) * (C X ^ i * X ^ (x - i) *
          (x.choose i : ℤ[X][X])) = (((x.choose i : ℤ) * signedStirlingFirst n x : ℤ) : ℤ[X][X]) *
            C X ^ i * X ^ (x - i) by push_cast; ring, r26a_coeff_coeff]
      simp only [mem_range] at hi
      by_cases h1 : i = h
      · subst h1; by_cases h2 : x = i + m
        · simp [h2]
        · simp only [h2]; simp; omega
      · simp [h1]
    rw [sum_congr rfl this, sum_ite_eq']
    split_ifs with h1 h2 <;> simp_all
  have hR : ∀ x ∈ antidiagonal n, ∑ x_1 ∈ range (x.2 + 1), ∑ i ∈ range (x.1 + 1),
      (((n.choose x.1 : ℤ[X][X]) * ((signedStirlingFirst x.1 i : ℤ[X][X]) * C X ^ i *
        ((signedStirlingFirst x.2 x_1 : ℤ[X][X]) * X ^ x_1))).coeff m).coeff h =
      (n.choose x.2 : ℤ) * signedStirlingFirst x.1 h * signedStirlingFirst x.2 m := by
    intro x hx
    have : ∀ x_1 ∈ range (x.2 + 1), ∀ i ∈ range (x.1 + 1),
        (((n.choose x.1 : ℤ[X][X]) * ((signedStirlingFirst x.1 i : ℤ[X][X]) * C X ^ i *
          ((signedStirlingFirst x.2 x_1 : ℤ[X][X]) * X ^ x_1))).coeff m).coeff h =
        if x_1 = m then (if i = h then (n.choose x.2 : ℤ) * signedStirlingFirst x.1 h *
          signedStirlingFirst x.2 m else 0) else 0 := by
      intro x_1 _ i _
      rw [show (n.choose x.1 : ℤ[X][X]) * ((signedStirlingFirst x.1 i : ℤ[X][X]) * C X ^ i *
          ((signedStirlingFirst x.2 x_1 : ℤ[X][X]) * X ^ x_1)) =
          (((n.choose x.1 : ℤ) * signedStirlingFirst x.1 i * signedStirlingFirst x.2 x_1 : ℤ) :
            ℤ[X][X]) * C X ^ i * X ^ x_1 by push_cast; ring, r26a_coeff_coeff]
      rw [mem_antidiagonal] at hx
      rw [← Nat.choose_symm_of_eq_add hx.symm]
      by_cases h1 : x_1 = m <;> by_cases h2 : i = h <;> simp [h1, h2]
    rw [sum_congr rfl fun x_1 hx_1 => sum_congr rfl (this x_1 hx_1)]
    simp only [Finset.sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_range]
    split_ifs with h1 h2
    · rfl
    · rw [signedStirlingFirst_eq_zero_of_lt (by omega)]; simp
    · rw [signedStirlingFirst_eq_zero_of_lt (by omega : x.2 < m)]; simp
  rw [sum_congr rfl hL, sum_congr rfl hR, sum_ite_eq'] at hφ
  simp only [mem_range, show h + m < n + 1 by omega, ↓reduceIte] at hφ
  rw [hφ, Nat.add_sub_cancel_left,
    ← Nat.sum_antidiagonal_swap (f := fun x => (n.choose x.2 : ℤ) * signedStirlingFirst x.1 h *
      signedStirlingFirst x.2 m)]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => (n.choose i : ℤ) * signedStirlingFirst j h * signedStirlingFirst i m)]
  symm
  refine sum_subset (fun j hj => by simp at hj ⊢; omega) fun j hj hj' => ?_
  simp only [mem_Icc, not_and_or, not_le, mem_range] at hj hj'
  rcases hj' with hj' | hj'
  · rw [signedStirlingFirst_eq_zero_of_lt hj', mul_zero]
  · rw [signedStirlingFirst_eq_zero_of_lt (by omega : n - j < h), mul_zero, zero_mul]

/-- DLMF 26.8.20 (range form): `s(n+1, k+1) = n! ∑_{j=0}^{n} (-1)^{n-j} s(j, k) / j!`. -/
lemma c26a_signedStirlingFirst_succ_succ_eq_sum_range (n k : ℕ) :
    (signedStirlingFirst (n + 1) (k + 1) : ℚ) =
      n.factorial *
        ∑ j ∈ range (n + 1), (-1 : ℚ) ^ (n - j) / j.factorial * signedStirlingFirst j k := by
  induction n with
  | zero => rcases k with _ | k <;> simp [signedStirlingFirst_one]
  | succ n ih =>
    rw [signedStirlingFirst_succ_succ]
    push_cast
    rw [ih, sum_range_succ _ (n + 1), Nat.factorial_succ]
    have : ∑ j ∈ range (n + 1), (-1 : ℚ) ^ (n + 1 - j) / j.factorial * signedStirlingFirst j k =
        -∑ j ∈ range (n + 1), (-1 : ℚ) ^ (n - j) / j.factorial * signedStirlingFirst j k := by
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun j hj => ?_
      rw [show n + 1 - j = n - j + 1 by have := mem_range.mp hj; omega, pow_succ]
      ring
    rw [this]
    simp only [Nat.sub_self, pow_zero]
    push_cast
    field_simp
    ring

/-- DLMF 26.8.20: `s(n+1, k+1) = n! ∑_{j=k}^{n} (-1)^{n-j} s(j, k) / j!`. -/
@[dlmf 26.8.E20]
theorem signedStirlingFirst_succ_succ_eq_sum (n k : ℕ) :
    (signedStirlingFirst (n + 1) (k + 1) : ℚ) =
      n.factorial * ∑ j ∈ Icc k n, (-1 : ℚ) ^ (n - j) / j.factorial * signedStirlingFirst j k := by
  rw [c26a_signedStirlingFirst_succ_succ_eq_sum_range]
  congr 1
  symm
  apply sum_subset
  · intro j hj; simp only [mem_Icc] at hj; simp only [mem_range]; omega
  · intro j hj hj'
    simp only [mem_range] at hj; simp only [mem_Icc, not_and_or, not_le] at hj'
    rw [signedStirlingFirst_eq_zero_of_lt (by omega)]; simp

/-- DLMF 26.8.21: `s(n+k+1, k) = -∑_{j=0}^{k} (n+j) s(n+j, j)`. -/
@[dlmf 26.8.E21]
theorem signedStirlingFirst_add_succ (n k : ℕ) :
    signedStirlingFirst (n + k + 1) k =
      -∑ j ∈ range (k + 1), ((n + j : ℕ) : ℤ) * signedStirlingFirst (n + j) j := by
  induction k with
  | zero => rcases n with _ | n <;> simp
  | succ k ih =>
    rw [sum_range_succ, show n + (k + 1) + 1 = (n + k + 1) + 1 by omega,
      signedStirlingFirst_succ_succ, ih, show n + (k + 1) = n + k + 1 by omega]
    ring

/-- DLMF 26.8.22: `S(n, k) = k S(n-1, k) + S(n-1, k-1)` (Mathlib
`Nat.stirlingSecond_succ_succ`, written with `n + 1`, `k + 1`). -/
@[dlmf 26.8.E22]
theorem stirlingSecond_succ_succ' (n k : ℕ) :
    Nat.stirlingSecond (n + 1) (k + 1) = (k + 1) * Nat.stirlingSecond n (k + 1) +
      Nat.stirlingSecond n k := Nat.stirlingSecond_succ_succ n k

/-- Surjections `ι → Fin h ⊕ Fin m` with prescribed preimage `J` of the right summand. -/
lemma r26a_card_surj_sum_fiber {ι : Type*} [Fintype ι] [DecidableEq ι] (h m : ℕ)
    (J : Finset ι) :
    #{f : ι → Fin h ⊕ Fin m | Function.Surjective f ∧ ({x | (f x).isRight} : Finset ι) = J} =
      #{g : {x // x ∉ J} → Fin h | Function.Surjective g} *
        #{g : {x // x ∈ J} → Fin m | Function.Surjective g} := by
  rw [← card_product]
  symm
  refine card_bij (fun p _ => fun x => if hx : x ∈ J then Sum.inr (p.2 ⟨x, hx⟩)
    else Sum.inl (p.1 ⟨x, hx⟩)) ?_ ?_ ?_
  · rintro ⟨g1, g2⟩ hp
    simp only [mem_product, mem_filter, mem_univ, true_and] at hp ⊢
    refine ⟨?_, ?_⟩
    · rintro (a | b)
      · obtain ⟨⟨x, hx⟩, rfl⟩ := hp.1 a; exact ⟨x, by simp [hx]⟩
      · obtain ⟨⟨x, hx⟩, rfl⟩ := hp.2 b; exact ⟨x, by simp [hx]⟩
    · ext x; by_cases hx : x ∈ J <;> simp [hx]
  · rintro ⟨g1, g2⟩ _ ⟨g1', g2'⟩ _ he
    simp only [Prod.mk.injEq]
    refine ⟨funext fun ⟨x, hx⟩ => ?_, funext fun ⟨x, hx⟩ => ?_⟩
    · have := congrFun he x; simp only [hx, ↓reduceDIte, Sum.inl.injEq] at this; exact this
    · have := congrFun he x; simp only [hx, ↓reduceDIte, Sum.inr.injEq] at this; exact this
  · intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf
    obtain ⟨hs, rfl⟩ := hf
    have hl : ∀ x : {x // x ∉ ({x | (f x).isRight} : Finset ι)}, (f x).isLeft := by
      rintro ⟨x, hx⟩; simpa using hx
    have hr : ∀ x : {x // x ∈ ({x | (f x).isRight} : Finset ι)}, (f x).isRight := by
      rintro ⟨x, hx⟩; simpa using hx
    refine ⟨(fun x => (f x).getLeft (hl x), fun x => (f x).getRight (hr x)), ?_, ?_⟩
    · simp only [mem_product, mem_filter, mem_univ, true_and]
      refine ⟨fun a => ?_, fun b => ?_⟩
      · obtain ⟨x, hx⟩ := hs (Sum.inl a)
        exact ⟨⟨x, by simp [hx]⟩, by simp [hx]⟩
      · obtain ⟨x, hx⟩ := hs (Sum.inr b)
        exact ⟨⟨x, by simp [hx]⟩, by simp [hx]⟩
    · funext x
      by_cases hx : x ∈ ({x | (f x).isRight} : Finset ι)
      · simp only [hx, ↓reduceDIte]
        exact Sum.inr_getRight _ _
      · simp only [hx, ↓reduceDIte]
        exact Sum.inl_getLeft _ _

/-- The number of surjections depends only on the domain up to equivalence. -/
lemma r26a_card_surj_dom_congr {ι ι' β : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] [Fintype β] [DecidableEq β] (e : ι ≃ ι') :
    #{f : ι → β | Function.Surjective f} = #{f : ι' → β | Function.Surjective f} := by
  refine card_bij (fun f _ => f ∘ e.symm) ?_ ?_ ?_
  · intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf ⊢
    exact hf.comp e.symm.surjective
  · intro f _ g _ hfg
    funext x; simpa using congrFun hfg (e x)
  · intro g hg
    simp only [mem_filter, mem_univ, true_and] at hg
    exact ⟨g ∘ e, by simpa using hg.comp e.surjective, by funext x; simp⟩

/-- `#{surj Fin n → Fin (h+m)} = ∑_j C(n,j) #{surj Fin (n-j) → Fin h} #{surj Fin j → Fin m}`. -/
lemma r26a_card_surj_add (n h m : ℕ) :
    #{f : Fin n → Fin (h + m) | Function.Surjective f} =
      ∑ j ∈ range (n + 1), n.choose j * (#{f : Fin (n - j) → Fin h | Function.Surjective f} *
        #{f : Fin j → Fin m | Function.Surjective f}) := by
  rw [q26b_card_surjective_congr (finSumFinEquiv (m := h) (n := m)).symm,
    card_eq_sum_card_fiberwise
      (f := fun f : Fin n → Fin h ⊕ Fin m => ({x | (f x).isRight} : Finset (Fin n)))
      (t := (univ : Finset (Fin n)).powerset) (fun f _ => by simp)]
  have key : ∀ J ∈ (univ : Finset (Fin n)).powerset,
      #{f ∈ ({f : Fin n → Fin h ⊕ Fin m | Function.Surjective f} : Finset _) |
          ({x | (f x).isRight} : Finset (Fin n)) = J} =
        #{f : Fin (n - #J) → Fin h | Function.Surjective f} *
          #{f : Fin #J → Fin m | Function.Surjective f} := by
    intro J _
    rw [filter_filter, r26a_card_surj_sum_fiber]
    congr 1
    · apply r26a_card_surj_dom_congr
      exact Fintype.equivFinOfCardEq (by simp [Fintype.card_subtype_compl])
    · apply r26a_card_surj_dom_congr
      exact Fintype.equivFinOfCardEq (by simp)
  rw [sum_congr rfl key, sum_powerset_apply_card
    (fun j => #{f : Fin (n - j) → Fin h | Function.Surjective f} *
      #{f : Fin j → Fin m | Function.Surjective f})]
  simp [card_univ]

/-- DLMF 26.8.23: `C(k, h) S(n, k) = ∑_{j=k-h}^{n-h} C(n, j) S(n-j, h) S(j, k-h)`,
`n ≥ k ≥ h`. -/
@[dlmf 26.8.E23]
theorem choose_mul_stirlingSecond {n k h : ℕ} (hkn : k ≤ n) (hhk : h ≤ k) :
    k.choose h * Nat.stirlingSecond n k =
      ∑ j ∈ Icc (k - h) (n - h), n.choose j * Nat.stirlingSecond (n - j) h *
        Nat.stirlingSecond j (k - h) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = h + m := ⟨k - h, by omega⟩
  have hA := r26a_card_surj_add n h m
  simp only [q26b_card_surjective_fin] at hA
  have hsub : ∑ j ∈ Icc (h + m - h) (n - h), n.choose j * Nat.stirlingSecond (n - j) h *
        Nat.stirlingSecond j (h + m - h) = ∑ j ∈ range (n + 1), n.choose j *
          Nat.stirlingSecond (n - j) h * Nat.stirlingSecond j m := by
    rw [Nat.add_sub_cancel_left]
    refine sum_subset (fun j hj => by simp at hj ⊢; omega) fun j hj hj' => ?_
    simp only [mem_Icc, not_and_or, not_le] at hj'
    rcases hj' with hj' | hj'
    · rw [Nat.stirlingSecond_eq_zero_of_lt hj', mul_zero]
    · rw [Nat.stirlingSecond_eq_zero_of_lt (by simp at hj; omega : n - j < h), mul_zero,
        zero_mul]
  rw [hsub]
  have hpos : 0 < h.factorial * m.factorial := by positivity
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [mul_sum]
  have hk : (h + m).factorial = (h + m).choose h * (h.factorial * m.factorial) := by
    rw [← Nat.add_choose_mul_factorial_mul_factorial h m, Nat.choose_symm_add]; ring
  calc h.factorial * m.factorial * ((h + m).choose h * Nat.stirlingSecond n (h + m))
      = (h + m).factorial * Nat.stirlingSecond n (h + m) := by rw [hk]; ring
    _ = _ := hA
    _ = _ := sum_congr rfl fun j _ => by ring

/-- DLMF 26.8.24: `S(n, k) = ∑_{j=k}^{n} S(j-1, k-1) k^{n-j}`, for `k ≥ 1` (implicit in DLMF;
written with `k + 1`). -/
@[dlmf 26.8.E24]
theorem stirlingSecond_eq_sum_pow (n k : ℕ) :
    Nat.stirlingSecond n (k + 1) =
      ∑ j ∈ Icc (k + 1) n, Nat.stirlingSecond (j - 1) k * (k + 1) ^ (n - j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases lt_or_ge n k with h | h
    · rw [Nat.stirlingSecond_eq_zero_of_lt (by omega), Finset.Icc_eq_empty (by omega)]; rfl
    · rw [Finset.sum_Icc_succ_top (by omega), Nat.stirlingSecond_succ_succ, ih,
        Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one, mul_sum]
      congr 1
      refine sum_congr rfl fun j hj => ?_
      rw [show n + 1 - j = (n - j) + 1 by have := (mem_Icc.mp hj).2; omega, pow_succ]
      ring

/-- DLMF 26.8.25 (range form). -/
theorem c26a_stirlingSecond_succ_succ_eq_sum_range (n k : ℕ) :
    Nat.stirlingSecond (n + 1) (k + 1) =
      ∑ j ∈ range (n + 1), n.choose j * Nat.stirlingSecond j k := by
  induction n generalizing k with
  | zero => rcases k with _ | k <;> simp [Nat.stirlingSecond_eq_zero_of_lt, Nat.stirlingSecond_self]
  | succ n ih =>
    have hsplit : ∑ j ∈ range (n + 1 + 1), (n + 1).choose j * Nat.stirlingSecond j k =
        ∑ j ∈ range (n + 1), n.choose j * Nat.stirlingSecond (j + 1) k +
          Nat.stirlingSecond (n + 1) (k + 1) := by
      have h0 := sum_range_succ' (fun j => n.choose j * Nat.stirlingSecond j k) (n + 1)
      rw [sum_range_succ, Nat.choose_succ_self, zero_mul, add_zero] at h0
      rw [sum_range_succ', Nat.choose_zero_right, one_mul]
      simp_rw [Nat.choose_succ_succ', add_mul, sum_add_distrib]
      rw [add_assoc, ih k, h0, Nat.choose_zero_right, one_mul]
    rw [hsplit]
    rcases k with _ | k
    · simp [Nat.stirlingSecond_one_right]
    · have e : ∑ j ∈ range (n + 1), n.choose j * Nat.stirlingSecond (j + 1) (k + 1) =
          (k + 1) * ∑ j ∈ range (n + 1), n.choose j * Nat.stirlingSecond j (k + 1) +
            ∑ j ∈ range (n + 1), n.choose j * Nat.stirlingSecond j k := by
        rw [mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun j _ => ?_
        rw [Nat.stirlingSecond_succ_succ]; ring
      rw [e, ← ih, ← ih, Nat.stirlingSecond_succ_succ (n + 1) (k + 1)]
      ring

/-- DLMF 26.8.25: `S(n+1, k+1) = ∑_{j=k}^{n} C(n, j) S(j, k)`. -/
@[dlmf 26.8.E25]
theorem stirlingSecond_succ_succ_eq_sum (n k : ℕ) :
    Nat.stirlingSecond (n + 1) (k + 1) = ∑ j ∈ Icc k n, n.choose j * Nat.stirlingSecond j k := by
  rw [c26a_stirlingSecond_succ_succ_eq_sum_range]
  symm
  apply sum_subset
  · intro j hj; simp only [mem_Icc] at hj; simp only [mem_range]; omega
  · intro j hj hj'
    simp only [mem_range] at hj; simp only [mem_Icc, not_and_or, not_le] at hj'
    rw [Nat.stirlingSecond_eq_zero_of_lt (by omega)]; simp

/-- DLMF 26.8.26: `S(n+k+1, k) = ∑_{j=0}^{k} j S(n+j, j)`. -/
@[dlmf 26.8.E26]
theorem stirlingSecond_add_succ (n k : ℕ) :
    Nat.stirlingSecond (n + k + 1) k = ∑ j ∈ range (k + 1), j * Nat.stirlingSecond (n + j) j := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, show n + (k + 1) + 1 = (n + k + 1) + 1 by omega,
      Nat.stirlingSecond_succ_succ, ih, show n + (k + 1) = n + k + 1 by omega]
    ring

/-! ### Identities (§26.8(v)) -/

/-- Dropping a vanishing `k = 0` term: `∑_{k=0}^n f k = ∑_{k=1}^n f k` when `f 0 = 0`. -/
lemma c26a_sum_range_eq_sum_Icc {M : Type*} [AddCommMonoid M] (n : ℕ) {f : ℕ → M}
    (h : f 0 = 0) : ∑ k ∈ range (n + 1), f k = ∑ k ∈ Icc 1 n, f k := by
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega), h, zero_add]
  rfl

/-- `(-1)^{n-k} = (-1)^n (-1)^k` for `k ≤ n`. -/
lemma c26a_neg_one_pow_sub {R : Type*} [Monoid R] [HasDistribNeg R] {n k : ℕ} (hk : k ≤ n) :
    (-1 : R) ^ (n - k) = (-1) ^ n * (-1) ^ k := by
  have : (-1 : R) ^ n = (-1) ^ (n - k) * (-1) ^ k := by rw [← pow_add, Nat.sub_add_cancel hk]
  rw [this, mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp

/-- DLMF 26.8.27: `s(n, n-k) = ∑_{j=0}^{k} (-1)^j C(n-1+j, k+j) C(n+k, k-j) S(k+j, j)`,
`0 ≤ k ≤ n` (implicit in DLMF). -/
@[dlmf 26.8.E27]
theorem signedStirlingFirst_sub_eq_sum {n k : ℕ} (hk : k ≤ n) :
    signedStirlingFirst n (n - k) =
      ∑ j ∈ range (k + 1), (-1) ^ j * ((n - 1 + j).choose (k + j) : ℤ) *
        ((n + k).choose (k - j) : ℤ) * (Nat.stirlingSecond (k + j) j : ℤ) := by
  sorry

/-- DLMF 26.8.28: `∑_{k=1}^n s(n, k) = 0` for `n > 1`. -/
@[dlmf 26.8.E28]
theorem sum_signedStirlingFirst {n : ℕ} (hn : 1 < n) :
    ∑ k ∈ Icc 1 n, signedStirlingFirst n k = 0 := by
  have h := congrArg (Polynomial.eval (1 : ℤ)) (descPochhammer_eq_sum ℤ n)
  rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) by simp, descPochhammer_eval_coe_nat_of_lt hn] at h
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, Nat.cast_one, one_pow,
    mul_one, Int.cast_id] at h
  rw [← c26a_sum_range_eq_sum_Icc n (signedStirlingFirst_zero_right (by omega)), h]

/-- The falling factorial at `-1`: `(-1)(-2)⋯(-n) = (-1)ⁿ n!`. -/
lemma c26a_descPochhammer_eval_neg_one (n : ℕ) :
    (descPochhammer ℤ n).eval (-1) = (-1) ^ n * (n.factorial : ℤ) := by
  have h := ascPochhammer_eval_neg_eq_descPochhammer (R := ℤ) (-1) n
  rw [neg_neg, ascPochhammer_eval_one] at h
  rw [h, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp

/-- DLMF 26.8.29: `∑_{k=1}^n (-1)^{n-k} s(n, k) = n!`, for `n ≥ 1`. **Correction (implicit
condition):** for `n = 0` the printed sum is empty (`0 ≠ 0! = 1`). -/
@[dlmf 26.8.E29]
theorem sum_neg_one_pow_mul_signedStirlingFirst {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Icc 1 n, (-1) ^ (n - k) * signedStirlingFirst n k = n.factorial := by
  have h := congrArg (Polynomial.eval (-1 : ℤ)) (descPochhammer_eq_sum ℤ n)
  rw [c26a_descPochhammer_eval_neg_one] at h
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, Int.cast_id] at h
  rw [← c26a_sum_range_eq_sum_Icc n (by simp [signedStirlingFirst_zero_right hn])]
  have h2 : ∑ k ∈ range (n + 1), (-1) ^ (n - k) * signedStirlingFirst n k =
      (-1) ^ n * ∑ k ∈ range (n + 1), signedStirlingFirst n k * (-1) ^ k := by
    rw [mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hk : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [c26a_neg_one_pow_sub hk]; ring
  rw [h2, ← h, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp

/-- DLMF 26.8.30: `∑_{j=k}^{n} s(n+1, j+1) n^{j-k} = s(n, k)`. -/
@[dlmf 26.8.E30]
theorem sum_signedStirlingFirst_succ_mul_pow (n k : ℕ) :
    ∑ j ∈ Icc k n, signedStirlingFirst (n + 1) (j + 1) * (n : ℤ) ^ (j - k) =
      signedStirlingFirst n k := by
  rcases lt_or_ge n k with h | h
  · rw [Finset.Icc_eq_empty (by omega), sum_empty, signedStirlingFirst_eq_zero_of_lt h]
  · rw [show Icc k n = Ico k (n + 1) by ext x; simp only [mem_Icc, mem_Ico]; omega,
      sum_Ico_eq_sum_range]
    have := Finset.sum_range_sub' (fun i => signedStirlingFirst n (k + i) * (n : ℤ) ^ i)
      (n + 1 - k)
    simp only [add_zero, pow_zero, mul_one,
      signedStirlingFirst_eq_zero_of_lt (by omega : n < k + (n + 1 - k)), zero_mul,
      sub_zero] at this
    rw [← this]
    refine sum_congr rfl fun i _ => ?_
    rw [show k + i + 1 = (k + i) + 1 by omega, signedStirlingFirst_succ_succ,
      show k + i - k = i by omega, show k + (i + 1) = k + i + 1 by omega, pow_succ]
    ring

/-- DLMF 26.8.31 as printed is false: for an entire `f` the series
`∑_{n ≥ k} s(n,k) Δⁿ f(x) / n!` may converge without equalling `f^{(k)}(x)/k!`. The
counterexample is `f(z) = sin(πz)` at `x = 0`, `k = 1`: all `Δⁿ f(0)` vanish. -/
@[dlmf 26.8.E31]
theorem not_forall_stirling_deriv_eq_fwdDiff_series :
    ¬ ∀ (f : ℂ → ℂ), Differentiable ℂ f → ∀ (x : ℂ) (k : ℕ),
      Summable (fun n : ℕ => (signedStirlingFirst n k : ℂ) / n.factorial *
        (fwdDiff 1)^[n] f x) →
      (1 / k.factorial : ℂ) * iteratedDeriv k f x =
        ∑' n : ℕ, (signedStirlingFirst n k : ℂ) / n.factorial * (fwdDiff 1)^[n] f x := by
  intro H
  have hf : Differentiable ℂ (fun z : ℂ => Complex.sin (Real.pi * z)) :=
    Complex.differentiable_sin.comp (differentiable_id.const_mul _)
  have hΔ : ∀ n : ℕ, (fwdDiff (1 : ℂ))^[n] (fun z : ℂ => Complex.sin (Real.pi * z)) 0 = 0 := by
    intro n
    rw [fwdDiff_iter_eq_sum_shift]
    refine sum_eq_zero fun j _ => ?_
    have : Complex.sin (Real.pi * (0 + j • (1 : ℂ))) = 0 := by
      rw [zero_add, nsmul_eq_mul, mul_one, mul_comm]; exact Complex.sin_nat_mul_pi j
    rw [this, smul_zero]
  have := H _ hf 0 1 (by simp [hΔ])
  simp only [hΔ, mul_zero, tsum_zero, iteratedDeriv_one] at this
  have hd : deriv (fun z : ℂ => Complex.sin (Real.pi * z)) 0 = Real.pi := by
    have := ((Complex.hasDerivAt_sin (Real.pi * 0)).comp (0 : ℂ)
      ((hasDerivAt_id (0 : ℂ)).const_mul (Real.pi : ℂ)))
    simpa [Function.comp_def] using this.deriv
  rw [hd] at this
  simp [Real.pi_ne_zero] at this

/-- DLMF 26.8.31, **corrected** to polynomials `f` (where the series terminates):
`f^{(k)}(x)/k! = ∑_{n ≥ k} s(n, k) Δⁿ f(x) / n!`. The printed hypothesis (`f` entire and the
series convergent) is insufficient; see `not_forall_stirling_deriv_eq_fwdDiff_series`. -/
@[dlmf 26.8.E31]
theorem hasSum_signedStirlingFirst_fwdDiff (p : ℝ[X]) (k : ℕ) (x : ℝ) :
    HasSum (fun n : ℕ => (signedStirlingFirst n k : ℝ) / n.factorial *
        (fwdDiff 1)^[n] (fun y => p.eval y) x)
      ((1 / k.factorial : ℝ) * (derivative^[k] p).eval x) := by
  set N := p.natDegree
  set d : ℕ → ℝ := fun n => (fwdDiff 1)^[n] (fun y => p.eval y) x with hd
  have hd0 : ∀ n, N < n → d n = 0 := fun n hn => by
    simp only [hd]; rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hn]; rfl
  -- Newton's forward-difference formula as a polynomial identity
  have hQ : taylor x p = ∑ n ∈ range (N + 1), C (d n / n.factorial) * descPochhammer ℝ n := by
    rw [← sub_eq_zero]
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono _ (Set.infinite_range_of_injective (Nat.cast_injective (R := ℝ)))
    rintro _ ⟨t, rfl⟩
    simp only [Set.mem_ofPred_eq, IsRoot, eval_sub, eval_finsetSum, eval_mul, eval_C,
      descPochhammer_eval_eq_descFactorial, taylor_eval, sub_eq_zero]
    have h1 := shift_eq_sum_fwdDiff_iter (1 : ℝ) (fun y => p.eval y) t x
    simp only [nsmul_eq_mul, mul_one] at h1
    rw [add_comm, h1]
    have e1 : ∑ n ∈ range (t + 1), (t.choose n : ℝ) * d n =
        ∑ n ∈ range (N + t + 1), (t.choose n : ℝ) * d n := by
      apply sum_subset_zero_on_sdiff
      · intro n hn; simp only [mem_range] at hn ⊢; omega
      · intro n hn; simp only [Finset.mem_sdiff, mem_range, not_lt] at hn
        rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
      · intro _ _; rfl
    have e2 : ∑ n ∈ range (N + 1), d n / n.factorial * (t.descFactorial n : ℝ) =
        ∑ n ∈ range (N + t + 1), (t.choose n : ℝ) * d n := by
      apply sum_subset_zero_on_sdiff
      · intro n hn; simp only [mem_range] at hn ⊢; omega
      · intro n hn; simp only [Finset.mem_sdiff, mem_range, not_lt] at hn
        rw [hd0 n (by omega)]; simp
      · intro n _
        rw [Nat.descFactorial_eq_factorial_mul_choose]
        have : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
        push_cast; field_simp
    change ∑ n ∈ range (t + 1), (t.choose n : ℝ) * d n = _
    rw [e1, ← e2]
  have hcoeff := congrArg (fun q : ℝ[X] => q.coeff k) hQ
  simp only [taylor_coeff, finsetSum_coeff, coeff_C_mul] at hcoeff
  have hs : ∀ n, (descPochhammer ℝ n).coeff k = (signedStirlingFirst n k : ℝ) := by
    intro n
    rw [← descPochhammer_map (Int.castRingHom ℝ), coeff_map, coeff_descPochhammer]; rfl
  simp only [hs] at hcoeff
  have hk : (derivative^[k] p).eval x = k.factorial * (hasseDeriv k p).eval x := by
    rw [← factorial_smul_hasseDeriv]
    simp [nsmul_eq_mul]
  have hfin : ∀ n ∉ range (N + 1), (signedStirlingFirst n k : ℝ) / n.factorial * d n = 0 := by
    intro n hn; simp only [mem_range, not_lt] at hn; rw [hd0 n (by omega)]; simp
  have : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have e : (1 / k.factorial : ℝ) * (derivative^[k] p).eval x =
      ∑ n ∈ range (N + 1), (signedStirlingFirst n k : ℝ) / n.factorial * d n := by
    rw [hk, hcoeff, ← mul_assoc, one_div_mul_cancel this, one_mul]
    refine sum_congr rfl fun n _ => by ring
  rw [e]
  exact hasSum_sum_of_ne_finset_zero hfin

/-- DLMF 26.8.32: the forward difference `Δf(x) = f(x+1) - f(x)` is Mathlib's `fwdDiff 1`. -/
@[dlmf 26.8.E32]
theorem fwdDiff_one_apply {G : Type*} [AddCommGroup G] (f : ℝ → G) (x : ℝ) :
    fwdDiff 1 f x = f (x + 1) - f x := rfl

/-- DLMF 26.8.33: `S(n, n-k) = ∑_{j=0}^{k} (-1)^j C(n-1+j, k+j) C(n+k, k-j) s(k+j, j)`,
`0 ≤ k ≤ n` (implicit in DLMF). -/
@[dlmf 26.8.E33]
theorem stirlingSecond_sub_eq_sum {n k : ℕ} (hk : k ≤ n) :
    (Nat.stirlingSecond n (n - k) : ℤ) =
      ∑ j ∈ range (k + 1), (-1) ^ j * ((n - 1 + j).choose (k + j) : ℤ) *
        ((n + k).choose (k - j) : ℤ) * signedStirlingFirst (k + j) j := by
  sorry

/-- DLMF 26.8.34: `∑_{j=0}^n j^k x^j = ∑_{j=0}^k S(k, j) x^j (d/dx)^j ((1-x^{n+1})/(1-x))`,
as a polynomial identity: `(1-x^{n+1})/(1-x)` is the polynomial `1 + x + ⋯ + xⁿ` (its value
for `x ≠ 1`, and the removable value `n + 1` at `x = 1`). Any commutative ring. -/
@[dlmf 26.8.E34]
theorem sum_pow_mul_X_pow_eq (R : Type*) [CommRing R] (n k : ℕ) :
    ∑ j ∈ range (n + 1), C ((j : R) ^ k) * X ^ j =
      ∑ j ∈ range (k + 1), C (Nat.stirlingSecond k j : R) * X ^ j *
        derivative^[j] (∑ i ∈ range (n + 1), (X : R[X]) ^ i) := by
  have key : ∀ i j : ℕ, (X : R[X]) ^ j * derivative^[j] (X ^ i) =
      C ((i.descFactorial j : ℕ) : R) * X ^ i := by
    intro i j
    rw [iterate_derivative_X_pow_eq_C_mul]
    rcases le_or_gt j i with h | h
    · rw [mul_left_comm, ← pow_add, Nat.add_sub_cancel' h]
    · rw [(Nat.descFactorial_eq_zero_iff_lt).mpr h]; simp
  simp only [iterate_derivative_sum, mul_sum, mul_assoc, key]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [← Nat.cast_pow, Nat.pow_eq_sum_stirlingSecond_mul_descFactorial i k]
  simp only [Nat.cast_sum, Nat.cast_mul, map_sum, sum_mul, map_mul, mul_assoc]

/-- DLMF 26.8.35: `∑_{j=0}^n j^k = ∑_{j=0}^k j! S(k, j) C(n+1, j+1)` (with `0⁰ = 1`). -/
@[dlmf 26.8.E35]
theorem sum_range_pow_eq_sum_stirlingSecond (n k : ℕ) :
    ∑ j ∈ range (n + 1), j ^ k =
      ∑ j ∈ range (k + 1), j.factorial * Nat.stirlingSecond k j * (n + 1).choose (j + 1) := by
  simp_rw [Nat.pow_eq_sum_stirlingSecond_mul_descFactorial _ k]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  simp_rw [Nat.descFactorial_eq_factorial_mul_choose, ← mul_sum]
  rw [← Nat.sum_Icc_choose n i]
  have : ∑ m ∈ range (n + 1), m.choose i = ∑ m ∈ Icc i n, m.choose i := by
    symm; apply sum_subset
    · intro j hj; simp only [mem_Icc] at hj; simp only [mem_range]; omega
    · intro j hj hj'; simp only [mem_range] at hj; simp only [mem_Icc, not_and_or, not_le] at hj'
      exact Nat.choose_eq_zero_of_lt (by omega)
  rw [← this]; ring

/-- DLMF 26.8.36: `∑_{k=0}^n (-1)^{n-k} k! S(n, k) = 1`. -/
@[dlmf 26.8.E36]
theorem sum_neg_one_pow_mul_factorial_mul_stirlingSecond (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1) ^ (n - k) * (k.factorial : ℤ) * Nat.stirlingSecond n k = 1 := by
  have h := congrArg (Polynomial.eval (-1 : ℤ)) (c26a_X_pow_eq_sum_descPochhammer n)
  simp only [eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C,
    c26a_descPochhammer_eval_neg_one] at h
  have h2 : ∑ k ∈ range (n + 1), (-1) ^ (n - k) * (k.factorial : ℤ) * Nat.stirlingSecond n k =
      (-1) ^ n * ∑ k ∈ range (n + 1), (Nat.stirlingSecond n k : ℤ) * ((-1) ^ k * k.factorial) := by
    rw [mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hk : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [c26a_neg_one_pow_sub hk]; ring
  rw [h2, ← h, ← pow_add, ← two_mul, pow_mul]; simp

/-- DLMF 26.8.37: `Δ^k f(x) / k! = ∑_{n ≥ k} S(n, k) f^{(n)}(x) / n!` for an entire `f`
(the series then always converges). -/
@[dlmf 26.8.E37]
theorem hasSum_stirlingSecond_iteratedDeriv {f : ℂ → ℂ} (hf : Differentiable ℂ f) (k : ℕ)
    (x : ℂ) :
    HasSum (fun n : ℕ => (Nat.stirlingSecond n k : ℂ) / n.factorial * iteratedDeriv n f x)
      ((1 / k.factorial : ℂ) * (fwdDiff 1)^[k] f x) := by
  have hc : ∀ n, ∑ j ∈ range (k + 1), (-1 : ℂ) ^ (k - j) * (k.choose j : ℂ) * (j : ℂ) ^ n =
      k.factorial * Nat.stirlingSecond n k := by
    intro n
    have := congrArg (Rat.cast : ℚ → ℂ) (q26a_sum_alt_choose_pow n k)
    push_cast at this
    exact this
  have hs := hasSum_sum (s := range (k + 1)) fun j _ =>
    (Complex.hasSum_taylorSeries_of_entire hf x (x + j • (1 : ℂ))).const_smul
      ((-1 : ℤ) ^ (k - j) * k.choose j)
  rw [← fwdDiff_iter_eq_sum_shift] at hs
  have := hs.mul_left (1 / k.factorial : ℂ)
  convert this using 1
  ext n
  simp only [add_sub_cancel_left, nsmul_eq_mul, mul_one, smul_eq_mul, zsmul_eq_mul]
  push_cast
  have e : ∑ j ∈ range (k + 1), (-1 : ℂ) ^ (k - j) * (k.choose j : ℂ) *
      ((n.factorial : ℂ)⁻¹ * ((j : ℂ) ^ n * iteratedDeriv n f x)) =
      (∑ j ∈ range (k + 1), (-1 : ℂ) ^ (k - j) * (k.choose j : ℂ) * (j : ℂ) ^ n) *
        ((n.factorial : ℂ)⁻¹ * iteratedDeriv n f x) := by
    rw [sum_mul]; refine sum_congr rfl fun j _ => by ring
  rw [e, hc]
  have : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  field_simp

/-- DLMF 26.8.39 (first): `∑_{j=k}^{n} s(j, k) S(n, j) = δ_{n,k}`. -/
@[dlmf 26.8.E39]
theorem sum_signedStirlingFirst_mul_stirlingSecond (n k : ℕ) :
    ∑ j ∈ Icc k n, signedStirlingFirst j k * Nat.stirlingSecond n j = if n = k then 1 else 0 := by
  have h := congrArg (fun p : ℤ[X] => p.coeff k) (c26a_X_pow_eq_sum_descPochhammer n)
  simp only [coeff_X_pow, finsetSum_coeff, coeff_C_mul, coeff_descPochhammer] at h
  rw [show (if n = k then (1 : ℤ) else 0) = if k = n then 1 else 0 by simp [eq_comm], h]
  apply sum_subset_zero_on_sdiff
  · intro j hj; simp only [mem_Icc] at hj; simp only [mem_range]; omega
  · intro j hj
    simp only [Finset.mem_sdiff, mem_range, mem_Icc, not_and_or, not_le] at hj
    rcases hj.2 with h | h
    · rw [signedStirlingFirst_eq_zero_of_lt h]; simp
    · omega
  · intro j _; ring

/-- The matrices `(s(i, j))` and `(S(i, j))`, `0 ≤ i, j ≤ n`. -/
def c26a_matS1 (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun i j => signedStirlingFirst i j

/-- The matrix of Stirling numbers of the second kind, `0 ≤ i, j ≤ n`. -/
def c26a_matS2 (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun i j => Nat.stirlingSecond i j

lemma c26a_matS2_mul_matS1 (n : ℕ) : c26a_matS2 n * c26a_matS1 n = 1 := by
  ext a b
  have ha := a.isLt
  simp only [Matrix.mul_apply, c26a_matS1, c26a_matS2, Matrix.one_apply, Fin.ext_iff]
  rw [← sum_signedStirlingFirst_mul_stirlingSecond a b]
  rw [Finset.sum_fin_eq_sum_range]
  symm
  apply sum_subset_zero_on_sdiff
  · intro j hj; simp only [mem_Icc] at hj; simp only [mem_range]; omega
  · intro j hj
    simp only [Finset.mem_sdiff, mem_range, mem_Icc, not_and_or, not_le] at hj
    rcases hj.2 with h | h
    · simp [hj.1, signedStirlingFirst_eq_zero_of_lt h]
    · simp [hj.1, Nat.stirlingSecond_eq_zero_of_lt h]
  · intro j hj; simp only [mem_Icc] at hj; simp [show j < n + 1 by omega, mul_comm]

/-- DLMF 26.8.39 (second): `∑_{j=k}^{n} s(n, j) S(j, k) = δ_{n,k}`. -/
@[dlmf 26.8.E39]
theorem sum_signedStirlingFirst_mul_stirlingSecond' (n k : ℕ) :
    ∑ j ∈ Icc k n, signedStirlingFirst n j * Nat.stirlingSecond j k = if n = k then 1 else 0 := by
  rcases lt_or_ge n k with hnk | hkn
  · rw [Finset.Icc_eq_empty (by omega)]; simp [hnk.ne]
  have hm := congrFun (congrFun ((mul_eq_one_comm (a := c26a_matS2 n) (b := c26a_matS1 n)).mp
    (c26a_matS2_mul_matS1 n))
    ⟨n, by omega⟩) ⟨k, by omega⟩
  simp only [Matrix.mul_apply, c26a_matS1, c26a_matS2, Matrix.one_apply, Fin.ext_iff] at hm
  rw [← hm, Finset.sum_fin_eq_sum_range]
  apply sum_subset_zero_on_sdiff
  · intro j hj; simp only [mem_Icc] at hj; simp only [mem_range]; omega
  · intro j hj
    simp only [Finset.mem_sdiff, mem_range, mem_Icc, not_and_or, not_le] at hj
    rcases hj.2 with h | h
    · simp [hj.1, Nat.stirlingSecond_eq_zero_of_lt h]
    · simp [hj.1, signedStirlingFirst_eq_zero_of_lt h]
  · intro j hj; simp only [mem_Icc] at hj; simp [show j < n + 1 by omega]

/-- DLMF 26.8.38: with `A = (s(j, k))` and `B = (S(j, k))`, `1 ≤ j, k ≤ n` (indices shifted to
`Fin n`), `A⁻¹ = B` (over `ℚ`). -/
@[dlmf 26.8.E38]
theorem stirlingMatrix_inv (n : ℕ) :
    (Matrix.of fun i j : Fin n => (signedStirlingFirst ((i : ℕ) + 1) ((j : ℕ) + 1) : ℚ))⁻¹ =
      Matrix.of fun i j : Fin n => (Nat.stirlingSecond ((i : ℕ) + 1) ((j : ℕ) + 1) : ℚ) := by
  apply Matrix.inv_eq_right_inv
  ext a b
  have ha := a.isLt
  have hb := b.isLt
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, Fin.ext_iff]
  have h := sum_signedStirlingFirst_mul_stirlingSecond' ((a : ℕ) + 1) ((b : ℕ) + 1)
  rw [Fin.sum_univ_eq_sum_range (fun j => (signedStirlingFirst ((a : ℕ) + 1) (j + 1) : ℚ) *
    (Nat.stirlingSecond (j + 1) ((b : ℕ) + 1) : ℚ)) n]
  have e : ∑ j ∈ range n, (signedStirlingFirst ((a : ℕ) + 1) (j + 1) : ℚ) *
      (Nat.stirlingSecond (j + 1) ((b : ℕ) + 1) : ℚ) =
      ∑ j ∈ range (n + 1), (signedStirlingFirst ((a : ℕ) + 1) j : ℚ) *
        (Nat.stirlingSecond j ((b : ℕ) + 1) : ℚ) := by
    rw [sum_range_succ' _ n]; simp
  rw [e]
  have e2 : ∑ j ∈ range (n + 1), (signedStirlingFirst ((a : ℕ) + 1) j : ℚ) *
      (Nat.stirlingSecond j ((b : ℕ) + 1) : ℚ) =
      ((∑ j ∈ Icc ((b : ℕ) + 1) ((a : ℕ) + 1), signedStirlingFirst ((a : ℕ) + 1) j *
        Nat.stirlingSecond j ((b : ℕ) + 1) : ℤ) : ℚ) := by
    push_cast
    symm
    apply sum_subset_zero_on_sdiff
    · intro j hj; simp only [mem_Icc] at hj; simp only [mem_range]; omega
    · intro j hj
      simp only [Finset.mem_sdiff, mem_range, mem_Icc, not_and_or, not_le] at hj
      rcases hj.2 with h | h
      · simp [Nat.stirlingSecond_eq_zero_of_lt h]
      · simp [signedStirlingFirst_eq_zero_of_lt h]
    · intro j _; rfl
  rw [e2, h]
  split_ifs <;> simp_all

/-! ### Asymptotic approximations (§26.8(vii)) -/

/-- DLMF 26.8.40: `s(n+1, k+1) ~ (-1)^{n-k} (n!/k!) (γ + ln n)^k` as `n → ∞`, uniformly for
`k = o(ln n)`: stated for every sequence `k = k(n)` with `k(n) = o(ln n)`. -/
@[dlmf 26.8.E40]
theorem tendsto_signedStirlingFirst_div (k : ℕ → ℕ)
    (hk : (fun n => (k n : ℝ)) =o[atTop] fun n => Real.log n) :
    Tendsto (fun n : ℕ => (signedStirlingFirst (n + 1) (k n + 1) : ℝ) /
        ((-1) ^ (n - k n) * n.factorial / (k n).factorial *
          (Real.eulerMascheroniConstant + Real.log n) ^ (k n))) atTop (𝓝 1) := by
  sorry

/-- Faulhaber asymptotics: `∑_{j<K} j^p ~ K^{p+1}/(p+1)`. -/
lemma q26a_sum_range_pow_isEquivalent (p : ℕ) :
    (fun K : ℕ => ∑ j ∈ range K, (j : ℝ) ^ p) ~[atTop] fun K => (K : ℝ) ^ (p + 1) / (p + 1) := by
  apply isEquivalent_of_tendsto_one
  have hval : ∀ K : ℕ, 0 < K → (∑ j ∈ range K, (j : ℝ) ^ p) / ((K : ℝ) ^ (p + 1) / (p + 1)) =
      ∑ i ∈ range (p + 1), (bernoulli i : ℝ) * ((p + 1).choose i) * ((K : ℝ)⁻¹) ^ i := by
    intro K hK
    have h := congrArg (Rat.cast : ℚ → ℝ) (sum_range_pow K p)
    push_cast at h
    rw [h, div_div_eq_mul_div, sum_mul, sum_div]
    refine sum_congr rfl fun i hi => ?_
    have hi : i ≤ p + 1 := by have := mem_range.mp hi; omega
    have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
    rw [inv_pow, show (K : ℝ) ^ (p + 1) = (K : ℝ) ^ (p + 1 - i) * (K : ℝ) ^ i by
      rw [← pow_add, Nat.sub_add_cancel hi]]
    have : (K : ℝ) ^ i ≠ 0 := pow_ne_zero _ hK'
    have : (K : ℝ) ^ (p + 1 - i) ≠ 0 := pow_ne_zero _ hK'
    field_simp
  have hlim : Tendsto (fun K : ℕ => ∑ i ∈ range (p + 1), (bernoulli i : ℝ) * ((p + 1).choose i) *
      ((K : ℝ)⁻¹) ^ i) atTop (𝓝 (∑ i ∈ range (p + 1), (bernoulli i : ℝ) * ((p + 1).choose i) *
        (0 : ℝ) ^ i)) := by
    apply tendsto_finsetSum
    intro i _
    exact ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).pow i).const_mul _
  rw [sum_eq_single 0 (fun i _ hi => by simp [zero_pow hi]) (by simp)] at hlim
  simp only [bernoulli_zero, Rat.cast_one, Nat.choose_zero_right, Nat.cast_one, pow_zero,
    mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with K hK
  rw [Pi.div_apply, hval K hK]

/-- Summing asymptotic equivalents of a nonnegative divergent comparison sequence. -/
lemma q26a_sum_range_isEquivalent {u v : ℕ → ℝ} (h : u ~[atTop] v) (hv : 0 ≤ v)
    (hs : Tendsto (fun n => ∑ i ∈ range n, v i) atTop atTop) :
    (fun n => ∑ i ∈ range n, u i) ~[atTop] fun n => ∑ i ∈ range n, v i := by
  have := h.isLittleO.sum_range hv hs
  refine IsLittleO.isEquivalent ?_
  convert this using 1
  ext n; simp [sum_sub_distrib]

/-- Unsigned form of DLMF 26.8.41: `c(n+k, k) ~ k^{2n}/(2ⁿ n!)`. -/
lemma q26a_stirlingFirst_add_isEquivalent (n : ℕ) :
    (fun k : ℕ => (Nat.stirlingFirst (n + k) k : ℝ)) ~[atTop]
      fun k => (k : ℝ) ^ (2 * n) / (2 ^ n * n.factorial) := by
  induction n with
  | zero =>
    simp only [zero_add, Nat.stirlingFirst_self, Nat.cast_one, mul_zero, pow_zero,
      Nat.factorial_zero, mul_one, div_one]
    exact IsEquivalent.refl
  | succ n ih =>
    -- telescoping: `c(n+1+K, K) = ∑_{j<K} (n+j+1) c(n+j+1, j+1)`
    have htel : ∀ K, (Nat.stirlingFirst (n + 1 + K) K : ℝ) =
        ∑ j ∈ range K, ((n + j + 1 : ℕ) : ℝ) * Nat.stirlingFirst (n + (j + 1)) (j + 1) := by
      intro K
      induction K with
      | zero => simp [Nat.stirlingFirst_succ_zero]
      | succ K ihK =>
        rw [sum_range_succ, ← ihK, show n + 1 + (K + 1) = (n + K + 1) + 1 by ring,
          Nat.stirlingFirst_succ_succ, show n + K + 1 = n + 1 + K by ring,
          show n + (K + 1) = n + K + 1 by ring, show n + 1 + K = n + K + 1 by ring]
        push_cast; ring
    set c : ℝ := 1 / (2 ^ n * n.factorial) with hc
    have hcpos : 0 < c := by positivity
    have hu :
        (fun j : ℕ => ((n + j + 1 : ℕ) : ℝ) * Nat.stirlingFirst (n + (j + 1)) (j + 1)) ~[atTop]
        fun j : ℕ => c * (j : ℝ) ^ (2 * n + 1) := by
      have h1 : (fun j : ℕ => ((n + j + 1 : ℕ) : ℝ)) ~[atTop] fun j : ℕ => (j : ℝ) := by
        apply isEquivalent_of_tendsto_one
        have : Tendsto (fun j : ℕ => 1 + ((n + 1 : ℝ)) * (j : ℝ)⁻¹) atTop (𝓝 (1 + (n + 1) * 0)) :=
          tendsto_const_nhds.add
            ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul _)
        rw [mul_zero, add_zero] at this
        refine this.congr' ?_
        filter_upwards [eventually_gt_atTop 0] with j hj
        have : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
        simp only [Pi.div_apply]; push_cast; field_simp; ring
      have h2 : (fun j : ℕ => (Nat.stirlingFirst (n + (j + 1)) (j + 1) : ℝ)) ~[atTop]
          fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ (2 * n) / (2 ^ n * n.factorial) :=
        ih.comp_tendsto (tendsto_add_atTop_nat 1)
      have h3 : (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ (2 * n) / (2 ^ n * n.factorial)) ~[atTop]
          fun j : ℕ => c * (j : ℝ) ^ (2 * n) := by
        have h4 : (fun j : ℕ => ((j + 1 : ℕ) : ℝ)) ~[atTop] fun j : ℕ => (j : ℝ) := by
          have := h1
          apply isEquivalent_of_tendsto_one
          have : Tendsto (fun j : ℕ => 1 + (j : ℝ)⁻¹) atTop (𝓝 (1 + 0)) :=
            tendsto_const_nhds.add (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
          rw [add_zero] at this
          refine this.congr' ?_
          filter_upwards [eventually_gt_atTop 0] with j hj
          have : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
          simp only [Pi.div_apply]; push_cast; field_simp
        have := (h4.pow (2 * n)).mul (IsEquivalent.refl (u := fun _ : ℕ => c))
        convert this using 1
        · ext j; simp [hc, div_eq_mul_inv]
        · ext j; simp [mul_comm]
      have := h1.mul (h2.trans h3)
      convert this using 1
      ext j; simp only [Pi.mul_apply]; ring
    have hp : (fun K : ℕ => ∑ j ∈ range K, c * (j : ℝ) ^ (2 * n + 1)) ~[atTop]
        fun K : ℕ => c * ((K : ℝ) ^ (2 * n + 1 + 1) / (((2 * n + 1 : ℕ) : ℝ) + 1)) := by
      have := (IsEquivalent.refl (u := fun _ : ℕ => c)).mul
        (q26a_sum_range_pow_isEquivalent (2 * n + 1))
      convert this using 1
      ext K; simp [mul_sum]
    have hdiv : Tendsto
        (fun K : ℕ => c * ((K : ℝ) ^ (2 * n + 1 + 1) / (((2 * n + 1 : ℕ) : ℝ) + 1))) atTop
        atTop := by
      apply Tendsto.const_mul_atTop hcpos
      apply Tendsto.atTop_div_const (by positivity)
      exact (tendsto_pow_atTop (by omega)).comp tendsto_natCast_atTop_atTop
    have hsum := q26a_sum_range_isEquivalent hu (fun j => by positivity) (by
      exact hp.symm.tendsto_atTop hdiv)
    have hsum' : (fun K : ℕ => ∑ j ∈ range K, c * (j : ℝ) ^ (2 * n + 1)) ~[atTop]
        fun K : ℕ => c * ((K : ℝ) ^ (2 * n + 1 + 1) / (((2 * n + 1 : ℕ) : ℝ) + 1)) := hp
    have := hsum.trans hsum'
    convert this using 1
    · ext K; exact htel K
    · ext K; rw [hc, Nat.factorial_succ]; push_cast; field_simp; ring_nf

/-- DLMF 26.8.41: `s(n+k, k) ~ (-1)ⁿ k^{2n} / (2ⁿ n!)` as `k → ∞`, `n` fixed. -/
@[dlmf 26.8.E41]
theorem signedStirlingFirst_add_isEquivalent (n : ℕ) :
    (fun k : ℕ => (signedStirlingFirst (n + k) k : ℝ)) ~[atTop]
      fun k => (-1) ^ n / (2 ^ n * n.factorial) * (k : ℝ) ^ (2 * n) := by
  have h := (IsEquivalent.refl (u := fun _ : ℕ => (-1 : ℝ) ^ n)).mul
    (q26a_stirlingFirst_add_isEquivalent n)
  convert h using 1
  · ext k; simp [signedStirlingFirst]
  · ext k; simp only [Pi.mul_apply]; ring

/-- DLMF 26.8.42: `S(n, k) ~ kⁿ / k!` as `n → ∞`, `k` fixed. -/
@[dlmf 26.8.E42]
theorem stirlingSecond_isEquivalent (k : ℕ) :
    (fun n : ℕ => (Nat.stirlingSecond n k : ℝ)) ~[atTop]
      fun n => (k : ℝ) ^ n / k.factorial := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine IsEquivalent.congr_left IsEquivalent.refl ?_
    filter_upwards with n
    rcases n with _ | n <;> simp
  apply isEquivalent_of_tendsto_one
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hc : ∀ n, (Nat.stirlingSecond n k : ℝ) / ((k : ℝ) ^ n / k.factorial) =
      ∑ j ∈ range (k + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * ((j : ℝ) / k) ^ n := by
    intro n
    have := congrArg (Rat.cast : ℚ → ℝ) (q26a_sum_alt_choose_pow n k)
    push_cast at this
    simp_rw [div_pow, ← mul_div_assoc, ← sum_div, this]
    have : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    field_simp
  simp_rw [Pi.div_def, hc]
  have hlim : ∀ j ∈ range (k + 1), Tendsto (fun n : ℕ => (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) *
      ((j : ℝ) / k) ^ n) atTop (𝓝 (if j = k then 1 else 0)) := by
    intro j hj
    have hj : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
    split_ifs with hjk
    · subst hjk
      simp [div_self hkR.ne']
    · have hlt : (j : ℝ) / k < 1 := by
        rw [div_lt_one hkR]; exact_mod_cast lt_of_le_of_ne hj hjk
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hlt).const_mul
        ((-1 : ℝ) ^ (k - j) * (k.choose j : ℝ))
      simpa using this
  have := tendsto_finsetSum _ hlim
  rw [Finset.sum_ite_eq'] at this
  simpa using this

/-- DLMF 26.8.43: `S(n+k, k) ~ k^{2n} / (2ⁿ n!)` as `k → ∞`, uniformly for `n = o(k^{1/2})`:
stated for every sequence `n = n(k)` with `n(k) = o(√k)`. -/
@[dlmf 26.8.E43]
theorem tendsto_stirlingSecond_add_div (n : ℕ → ℕ)
    (hn : (fun k => (n k : ℝ)) =o[atTop] fun k => Real.sqrt k) :
    Tendsto (fun k : ℕ => (Nat.stirlingSecond (n k + k) k : ℝ) /
        ((k : ℝ) ^ (2 * n k) / (2 ^ (n k) * (n k).factorial))) atTop (𝓝 1) := by
  sorry

/-! ### Combinatorial interpretations (§26.8(i)) -/

section CycleCount

open Equiv Equiv.Perm

/-- A relation that is an equivalence and relates every point to its image contains `SameCycle`. -/
lemma q26a_sameCycle_le {α : Type*} {f : Perm α} {R : α → α → Prop} (hR : Equivalence R)
    (hf : ∀ x, R x (f x)) {x y : α} (h : SameCycle f x y) : R x y := by
  obtain ⟨i, rfl⟩ := h
  induction i using Int.induction_on with
  | zero => simpa using hR.refl x
  | succ i ih =>
    rw [add_comm, zpow_add, zpow_one, Perm.mul_apply]
    exact hR.trans ih (hf _)
  | pred i ih =>
    have h1 := hf ((f ^ (-(i : ℤ) - 1)) x)
    rw [← Perm.mul_apply, ← zpow_one_add, show (1 + (-(i:ℤ) - 1)) = -i by ring] at h1
    exact hR.trans ih (hR.symm h1)

/-- The cycle maxima of a permutation. -/
def q26a_cycleMax {α : Type*} [Fintype α] [LinearOrder α] (σ : Perm α) : Finset α :=
  {a | ∀ b, SameCycle σ a b → b ≤ a}

/-- Inserting `0` into a permutation of `Fin n` (via `decomposeFin`) does not change which
nonzero points lie in a common cycle. -/
lemma q26a_sameCycle_succ {n : ℕ} (p : Fin (n + 1)) (τ : Perm (Fin n)) (x y : Fin n) :
    SameCycle (decomposeFin.symm (p, τ)) x.succ y.succ ↔ SameCycle τ x y := by
  set σ := decomposeFin.symm (p, τ)
  constructor
  · intro h
    let g : Fin (n + 1) → Fin (n + 1) := fun a => if a = 0 then p else a
    let R : Fin (n + 1) → Fin (n + 1) → Prop := fun a b =>
      g a = g b ∨ ∃ x y, g a = Fin.succ x ∧ g b = Fin.succ y ∧ SameCycle τ x y
    have hR : Equivalence R := by
      refine ⟨fun a => Or.inl rfl, ?_, ?_⟩
      · rintro a b (h | ⟨x, y, hx, hy, h⟩)
        · exact Or.inl h.symm
        · exact Or.inr ⟨y, x, hy, hx, h.symm⟩
      · rintro a b c (h | ⟨x, y, hx, hy, h⟩) (h' | ⟨x', y', hx', hy', h'⟩)
        · exact Or.inl (h.trans h')
        · exact Or.inr ⟨x', y', h ▸ hx', hy', h'⟩
        · exact Or.inr ⟨x, y, hx, h' ▸ hy, h⟩
        · rw [hy, Fin.succ_inj] at hx'
          subst hx'
          exact Or.inr ⟨x, y', hx, hy', h.trans h'⟩
    have hstep : ∀ a, R a (σ a) := by
      intro a
      refine Fin.cases ?_ (fun x => ?_) a
      · left
        by_cases hp : p = 0 <;> simp [σ, g, hp]
      · simp only [σ, decomposeFin_symm_apply_succ]
        by_cases hx : (τ x).succ = p
        · right
          rw [← hx, swap_apply_right]
          exact ⟨x, τ x, by simp [g], by simp [g, hx], (SameCycle.refl _ _).apply_right⟩
        · right
          rw [swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) hx]
          exact ⟨x, τ x, by simp [g], by simp [g], (SameCycle.refl _ _).apply_right⟩
    rcases q26a_sameCycle_le hR hstep h with h | ⟨x', y', hx, hy, h⟩
    · simp only [g, Fin.succ_ne_zero, ite_false, Fin.succ_inj] at h
      subst h; exact SameCycle.refl _ _
    · simp only [g, Fin.succ_ne_zero, ite_false, Fin.succ_inj] at hx hy
      subst hx hy; exact h
  · intro h
    let R : Fin n → Fin n → Prop := fun a b => SameCycle σ a.succ b.succ
    have hR : Equivalence R :=
      ⟨fun a => SameCycle.refl _ _, fun h => h.symm, fun h h' => h.trans h'⟩
    refine q26a_sameCycle_le (R := R) hR (fun a => ?_) h
    simp only [R]
    by_cases hx : (τ a).succ = p
    · have h1 : σ a.succ = 0 := by simp [σ, ← hx]
      have h2 : σ (σ a.succ) = (τ a).succ := by rw [h1]; simp [σ, hx]
      rw [← h2]; exact (SameCycle.refl _ _).apply_right.apply_right
    · have h1 : σ a.succ = (τ a).succ := by
        simp only [σ, decomposeFin_symm_apply_succ]
        exact swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) hx
      rw [← h1]; exact (SameCycle.refl _ _).apply_right

/-- Inserting `0` adds a cycle exactly when `0` becomes a fixed point. -/
lemma q26a_card_cycleMax_decomposeFin {n : ℕ} (p : Fin (n + 1)) (τ : Perm (Fin n)) :
    #(q26a_cycleMax (decomposeFin.symm (p, τ))) = #(q26a_cycleMax τ) + if p = 0 then 1 else 0 := by
  simp only [q26a_cycleMax, card_filter, Fin.sum_univ_succ]
  rw [add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    apply propext
    constructor
    · intro h y hy
      exact Fin.succ_le_succ_iff.mp (h _ ((q26a_sameCycle_succ p τ x y).2 hy))
    · intro h b hb
      refine Fin.cases (fun _ => Fin.zero_le _) (fun y hy => ?_) b hb
      exact Fin.succ_le_succ_iff.mpr (h y ((q26a_sameCycle_succ p τ x y).1 hy))
  · by_cases hp : p = 0
    · subst hp
      simp only [ite_true]
      split_ifs with hc
      · rfl
      refine absurd (fun b hb => ?_) hc
      have : Function.IsFixedPt (decomposeFin.symm ((0 : Fin (n+1)), τ)) 0 := by
        simp [Function.IsFixedPt]
      exact (hb.eq_of_left this).symm.le
    · simp only [hp, ite_false]
      split_ifs with h
      swap; · rfl
      exfalso
      have hs : SameCycle (decomposeFin.symm (p, τ)) 0 p := by
        have := (SameCycle.refl (decomposeFin.symm (p, τ)) 0).apply_right
        simpa using this
      exact hp (le_antisymm (h p hs) (Fin.zero_le _))
/-- The number of cycles (fixed points included) equals the number of cycle maxima. -/
lemma q26a_card_parts_partition {α : Type*} [Fintype α] [LinearOrder α] (σ : Perm α) :
    Multiset.card σ.partition.parts = #(q26a_cycleMax σ) := by
  rw [parts_partition, Multiset.card_add, Multiset.card_replicate, cycleType_def,
    Multiset.card_map]
  rw [← card_filter_add_card_filter_not (s := q26a_cycleMax σ) (fun x => x ∈ σ.support)]
  congr 1
  · change #σ.cycleFactorsFinset = _
    symm
    apply Finset.card_bij (fun a _ => σ.cycleOf a)
    · intro a ha
      simp only [mem_filter] at ha
      exact cycleOf_mem_cycleFactorsFinset_iff.2 ha.2
    · intro a ha b hb hab
      simp only [mem_filter, q26a_cycleMax, mem_univ, true_and] at ha hb
      have : SameCycle σ a b := by
        have hb' : b ∈ (σ.cycleOf b).support :=
          (mem_support_cycleOf_iff.2 ⟨SameCycle.refl _ _, hb.2⟩)
        rw [← hab] at hb'
        exact (mem_support_cycleOf_iff.1 hb').1
      exact le_antisymm (hb.1 a this.symm) (ha.1 b this)
    · intro c hc
      have hne : c.support.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty_iff]
        exact (mem_cycleFactorsFinset_iff.1 hc).1.ne_one
      set m := c.support.max' hne
      have hm : m ∈ c.support := c.support.max'_mem hne
      have hcm := cycle_is_cycleOf hm hc
      have hms : m ∈ σ.support := mem_cycleFactorsFinset_support_le hc hm
      refine ⟨m, ?_, hcm.symm⟩
      simp only [mem_filter, q26a_cycleMax, mem_univ, true_and]
      refine ⟨fun b hb => ?_, hms⟩
      apply c.support.le_max'
      rw [hcm]
      exact mem_support_cycleOf_iff.2 ⟨hb, hms⟩
  · have : (q26a_cycleMax σ).filter (fun x => x ∉ σ.support) = univ \ σ.support := by
      ext a
      simp only [mem_filter, q26a_cycleMax, mem_univ, true_and, Finset.mem_sdiff]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨fun b hb => (hb.eq_of_left (notMem_support.1 h)).symm.le, h⟩
    rw [this, card_sdiff_of_subset (subset_univ _), card_univ]

/-- Permutations of `Fin n` with `k` cycle maxima are counted by `Nat.stirlingFirst n k`. -/
lemma q26a_card_cycleMax_eq (n k : ℕ) :
    #{σ : Perm (Fin n) | #(q26a_cycleMax σ) = k} = Nat.stirlingFirst n k := by
  induction n generalizing k with
  | zero =>
    rcases k with _ | k
    · simp only [Nat.stirlingFirst_zero]
      rw [Finset.card_eq_one]
      refine ⟨1, ?_⟩
      ext σ
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · intro _; exact Subsingleton.elim _ _
      · intro _; simp [q26a_cycleMax]
    · simp only [Nat.stirlingFirst_zero_succ, card_eq_zero, filter_eq_empty_iff]
      intro σ _
      simp [q26a_cycleMax]
  | succ n ih =>
    have key : ∀ m, #{σ : Perm (Fin (n + 1)) | #(q26a_cycleMax σ) = m} =
        #{τ : Perm (Fin n) | #(q26a_cycleMax τ) + 1 = m} +
          n * #{τ : Perm (Fin n) | #(q26a_cycleMax τ) = m} := by
      intro m
      simp only [card_filter]
      rw [← Equiv.sum_comp decomposeFin.symm, Fintype.sum_prod_type, Fin.sum_univ_succ]
      simp only [q26a_card_cycleMax_decomposeFin, Fin.succ_ne_zero, ite_true, ite_false, add_zero,
        sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    rcases k with _ | k
    · rw [Nat.stirlingFirst_succ_zero, key, ih]
      rcases n with _ | n <;> simp
    · rw [key, Nat.stirlingFirst_succ_succ, ← ih, ← ih]
      simp only [Nat.add_right_cancel_iff]
      ring

end CycleCount

/-- DLMF §26.8(i): `|s(n, k)|` (Mathlib's `Nat.stirlingFirst n k`) is the number of
permutations of `{1, …, n}` with exactly `k` cycles (fixed points counted as cycles, i.e. the
number of parts of the cycle-type partition `σ.partition`). -/
@[dlmf 26.8.i]
theorem card_perm_numCycles (n k : ℕ) :
    #{σ : Equiv.Perm (Fin n) | σ.partition.parts.card = k} = Nat.stirlingFirst n k := by
  simp only [q26a_card_parts_partition]
  exact q26a_card_cycleMax_eq n k

/-- DLMF §26.8(i): `s(n, k) = (-1)^{n-k}` times the number of permutations of `{1, …, n}`
with exactly `k` cycles. -/
@[dlmf 26.8.i]
theorem signedStirlingFirst_eq_card (n k : ℕ) :
    signedStirlingFirst n k =
      (-1) ^ (n - k) * (#{σ : Equiv.Perm (Fin n) | σ.partition.parts.card = k} : ℤ) := by
  rw [card_perm_numCycles, signedStirlingFirst]

/-- DLMF §26.8(i): `S(n, k)` is the number of partitions of `{1, …, n}` into exactly `k`
nonempty subsets. -/
@[dlmf 26.8.i]
theorem card_finpartition_eq_stirlingSecond (n k : ℕ) :
    #{P : Finpartition (univ : Finset (Fin n)) | P.parts.card = k} = Nat.stirlingSecond n k := by
  -- each finpartition with `k` parts comes from `k!` surjections `Fin n → Fin k`
  have h := r26a_card_surjective_filter (α := Fin n) k (fun _ => True)
  simp only [and_true] at h
  rw [q26b_card_surjective_fin] at h
  exact (Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos k) h).symm

end DLMF.Combinatorics
