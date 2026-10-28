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
# Stirling numbers and their generating series

Signed Stirling numbers, factorial expansions, basic values and generating functions.

Source references and common attribution are retained in
`DLMF.Combinatorics.Stirling`.
-/

@[expose] public section

open Finset Polynomial Filter Topology Asymptotics

noncomputable section

namespace DLMF.Combinatorics

/-- DLMF §26.8(i): the (signed) Stirling number of the first kind
`s(n, k) = (-1)^{n-k} · #{permutations of {1,…,n} with exactly k cycles}`, written with
Mathlib's unsigned `Nat.stirlingFirst`. It is `0` for `k > n`. -/
@[dlmf 26.8.i]
def signedStirlingFirst (n k : ℕ) : ℤ := (-1) ^ (n - k) * (Nat.stirlingFirst n k : ℤ)

/-- Identity under the stated parameter and domain assumptions: `signedStirlingFirst 0 0 = 1`. -/
@[simp] theorem signedStirlingFirst_zero_zero : signedStirlingFirst 0 0 = 1 := by
  simp [signedStirlingFirst, Nat.stirlingFirst_zero]

/-- Identity under the stated parameter and domain assumptions: `signedStirlingFirst 0 (k + 1) =
0`. -/
@[simp] theorem signedStirlingFirst_zero_succ (k : ℕ) : signedStirlingFirst 0 (k + 1) = 0 := by
  simp [signedStirlingFirst, Nat.stirlingFirst_zero_succ]

/-- Identity under the stated parameter and domain assumptions: `signedStirlingFirst (n + 1) 0 =
0`. -/
@[simp] theorem signedStirlingFirst_succ_zero (n : ℕ) : signedStirlingFirst (n + 1) 0 = 0 := by
  simp [signedStirlingFirst, Nat.stirlingFirst_succ_zero]

/-- Identity under the stated parameter and domain assumptions: `signedStirlingFirst n k = 0`. -/
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

end DLMF.Combinatorics
end
end
