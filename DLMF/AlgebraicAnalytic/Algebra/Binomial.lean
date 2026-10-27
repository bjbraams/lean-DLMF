/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.RingTheory.Binomial
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.PartialFractions
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order

/-!
# Binomial coefficients, finite series and partial fractions (DLMF §1.2(i)–(iii))

The binomial coefficient `C(n, k)` of nonnegative integers is Mathlib's `Nat.choose`, and for
complex `z` the coefficient `C(z, k)` of 1.2.6 is Mathlib's generalized binomial coefficient
`Ring.choose z k` (on `ℂ`, a binomial ring as a `ℚ≥0`-module). The binomial theorem 1.2.2, the
sums 1.2.3–1.2.4, Pascal's rule 1.2.7 and the geometric sum 1.2.11 are upstream; the pointers are
in `DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean`. Here are the DLMF forms that Mathlib
states differently or not at all: the even-index sum 1.2.5, the Pochhammer forms 1.2.6, the
complex sums 1.2.8–1.2.9, the arithmetic progression 1.2.10, the factor `a` in 1.2.11, and the
partial-fraction decompositions 1.2.12–1.2.16. The decompositions are stated for the values of
the rational functions at points `x` off the poles, over an arbitrary field (DLMF: constants,
real or complex); 1.2.14–1.2.15 need characteristic zero for the factorials.
-/

@[expose] public noncomputable section

open Finset Polynomial

namespace DLMF.AlgebraicAnalytic

/-! ### Binomial coefficients (§1.2(i)) -/

/-- DLMF 1.2.5: `C(n,0) + C(n,2) + C(n,4) + ⋯ + C(n,ℓ) = 2^{n-1}` for a positive integer `n`,
where `ℓ` is `n` or `n - 1` according as `n` is even or odd; the sum runs over the even
`k ≤ n`. -/
@[dlmf 1.2.E5]
theorem sum_choose_even {n : ℕ} (hn : n ≠ 0) :
    ∑ k ∈ (range (n + 1)).filter Even, n.choose k = 2 ^ (n - 1) := by
  have h1 := Nat.sum_range_choose n
  have h2 := Int.alternating_sum_range_choose_of_ne hn
  have key : (2 : ℤ) * ∑ k ∈ (range (n + 1)).filter Even, (n.choose k : ℤ) = 2 ^ n := by
    have : ∀ k ∈ range (n + 1), ((n.choose k : ℤ) + (-1) ^ k * n.choose k) =
        if Even k then 2 * (n.choose k : ℤ) else 0 := by
      intro k _
      rcases Nat.even_or_odd k with hk | hk
      · simp [hk.neg_one_pow, hk]; ring
      · simp [hk.neg_one_pow, Nat.not_even_iff_odd.mpr hk]
    rw [mul_sum, sum_filter, ← sum_congr rfl this, sum_add_distrib, h2, add_zero]
    exact_mod_cast h1
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [pow_succ] at key
  have : (∑ k ∈ (range (m + 1 + 1)).filter Even, (m.succ.choose k : ℤ)) = 2 ^ m := by
    linarith
  simp only [Nat.succ_sub_one]
  exact_mod_cast this

/-- DLMF 1.2.6: for complex `z` and a nonnegative integer `k`,
`C(z, k) = z(z-1)⋯(z-k+1)/k! = (-1)^k (-z)_k / k! = (-1)^k C(k - z - 1, k)`, with the falling
and rising factorials Mathlib's `descPochhammer` and `ascPochhammer`. -/
@[dlmf 1.2.E6]
theorem ringChoose_eq_descPochhammer (z : ℂ) (k : ℕ) :
    Ring.choose z k = (descPochhammer ℂ k).eval z / k.factorial ∧
    Ring.choose z k = (-1) ^ k * (ascPochhammer ℂ k).eval (-z) / k.factorial ∧
    Ring.choose z k = (-1) ^ k * Ring.choose ((k : ℂ) - z - 1) k := by
  have h1 : Ring.choose z k = (descPochhammer ℂ k).eval z / k.factorial := by
    rw [Ring.choose_eq_smul, smul_eq_mul, ← aeval_eq_smeval, aeval_def, eval₂_eq_eval_map,
      descPochhammer_map, div_eq_inv_mul]
  refine ⟨h1, ?_, ?_⟩
  · rw [h1, ascPochhammer_eval_neg_eq_descPochhammer, ← mul_assoc, ← mul_pow, neg_one_mul,
      neg_neg, one_pow, one_mul]
  · have := Ring.choose_neg (-z) k
    rw [neg_neg] at this
    rw [this, show -z + (k : ℂ) - 1 = k - z - 1 by ring, Units.smul_def, zsmul_eq_mul,
      Int.coe_negOnePow_natCast]
    push_cast
    ring

/-- DLMF 1.2.8: `∑_{k=0}^{m} C(z+k, k) = C(z+m+1, m)` for complex `z`. -/
@[dlmf 1.2.E8]
theorem sum_ringChoose_add (z : ℂ) (m : ℕ) :
    ∑ k ∈ range (m + 1), Ring.choose (z + k) k = Ring.choose (z + m + 1) m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    have := Ring.choose_succ_succ (z + (m : ℂ) + 1) m
    push_cast
    rw [show z + ((m : ℂ) + 1) + 1 = z + m + 1 + 1 by ring, this,
      show z + ((m : ℂ) + 1) = z + m + 1 by ring]

/-- DLMF 1.2.9: `C(z,0) - C(z,1) + ⋯ + (-1)^m C(z,m) = (-1)^m C(z-1, m)` for complex `z`. -/
@[dlmf 1.2.E9]
theorem alternating_sum_ringChoose (z : ℂ) (m : ℕ) :
    ∑ k ∈ range (m + 1), (-1) ^ k * Ring.choose z k = (-1) ^ m * Ring.choose (z - 1) m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    have := Ring.choose_succ_succ (z - 1) m
    rw [sub_add_cancel] at this
    rw [this, pow_succ]
    ring

/-! ### Finite series (§1.2(ii)) -/

/-- DLMF 1.2.10: the arithmetic progression
`a + (a+d) + ⋯ + (a+(n-1)d) = na + n(n-1)d/2 = n(a+ℓ)/2` with last term `ℓ = a + (n-1)d`,
in any field of characteristic zero. -/
@[dlmf 1.2.E10]
theorem sum_arithmetic_progression {K : Type*} [Field K] [CharZero K] (a d : K) (n : ℕ) :
    ∑ i ∈ range n, (a + i * d) = n * a + n * (n - 1) / 2 * d ∧
    ∑ i ∈ range n, (a + i * d) = n * (a + (a + (n - 1) * d)) / 2 := by
  have h : ∑ i ∈ range n, (a + i * d) = n * a + n * (n - 1) / 2 * d := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih]; push_cast; ring
  exact ⟨h, by rw [h]; ring⟩

/-- DLMF 1.2.11: the geometric progression `a + ax + ⋯ + ax^{n-1} = a(1 - x^n)/(1 - x)` for
`x ≠ 1`, in any field. -/
@[dlmf 1.2.E11]
theorem sum_geometric_progression {K : Type*} [Field K] (a : K) {x : K} (hx : x ≠ 1) (n : ℕ) :
    ∑ i ∈ range n, a * x ^ i = a * (1 - x ^ n) / (1 - x) := by
  rw [← mul_sum, geom_sum_eq hx, mul_div_assoc]
  congr 1
  rw [← neg_sub x 1, ← neg_sub (x ^ n) 1, neg_div_neg_eq]

/-! ### Partial fractions (§1.2(iii)) -/

/-- DLMF 1.2.12 and 1.2.13: for distinct constants `α₁, …, αₙ` and a polynomial `f` of degree
less than `n`,
`f(x)/((x-α₁)⋯(x-αₙ)) = ∑_j A_j/(x - α_j)` with `A_j = f(α_j)/∏_{k ≠ j}(α_j - α_k)`,
at every `x` different from all `α_j`. Derived from Mathlib's Lagrange interpolation
(`Lagrange.eq_interpolate`, `Lagrange.eval_interpolate_not_at_node`). -/
@[dlmf 1.2.E12, dlmf 1.2.E13]
theorem div_prod_sub_eq_sum {K : Type*} [Field K] {n : ℕ} {α : Fin n → K}
    (hα : Function.Injective α) {f : K[X]} (hf : f.degree < n) {x : K}
    (hx : ∀ j, x ≠ α j) :
    f.eval x / ∏ j, (x - α j) =
      ∑ j, (f.eval (α j) / ∏ k ∈ univ.erase j, (α j - α k)) / (x - α j) := by
  have hI := Lagrange.eq_interpolate (s := univ) (v := α) hα.injOn (by simpa using hf)
  have hx' : ∀ i ∈ (univ : Finset (Fin n)), x ≠ α i := fun i _ => hx i
  have hP : ∏ j, (x - α j) ≠ 0 := prod_ne_zero_iff.2 fun j _ => sub_ne_zero.2 (hx j)
  conv_lhs => arg 1; rw [hI]
  rw [Lagrange.eval_interpolate_not_at_node _ hx', Lagrange.eval_nodal, mul_div_cancel_left₀ _ hP]
  refine sum_congr rfl fun j _ => ?_
  rw [Lagrange.nodalWeight, prod_inv_distrib]
  field_simp

/-- DLMF 1.2.14 and 1.2.15: for a polynomial `f` of degree less than `n`,
`f(x)/(x-α)^n = ∑_{j=1}^{n} B_j/(x-α)^j` with `B_j = f^{(n-j)}(α)/(n-j)!`, at every `x ≠ α`, in
a field of characteristic zero. The sum is written over `j + 1`, `j < n`. -/
@[dlmf 1.2.E14, dlmf 1.2.E15]
theorem div_pow_sub_eq_sum {K : Type*} [Field K] [CharZero K] {n : ℕ} {f : K[X]}
    (hf : f.degree < n) (α : K) {x : K} (hx : x ≠ α) :
    f.eval x / (x - α) ^ n =
      ∑ j ∈ range n, ((derivative^[n - (j + 1)] f).eval α / (n - (j + 1)).factorial) /
        (x - α) ^ (j + 1) := by
  by_cases hf0 : f = 0
  · subst hf0; simp
  have hfn : f.natDegree < n := (natDegree_lt_iff_degree_lt hf0).2 hf
  have hxa : x - α ≠ 0 := sub_ne_zero.2 hx
  have hcoeff : ∀ i, (taylor α f).coeff i =
      (derivative^[i] f).eval α / (i.factorial : K) := by
    intro i
    rw [taylor_coeff, eq_div_iff (by exact_mod_cast i.factorial_ne_zero)]
    have h := congrFun (factorial_smul_hasseDeriv (R := K) i) f
    rw [LinearMap.smul_apply] at h
    rw [← h, eval_smul, nsmul_eq_mul, mul_comm]
  have key : f.eval x = ∑ i ∈ range n, (taylor α f).coeff i * (x - α) ^ i := by
    rw [← eval_eq_sum_range' (by rwa [natDegree_taylor]), taylor_eval, sub_add_cancel]
  rw [key, sum_div, ← sum_range_reflect]
  refine sum_congr rfl fun j hj => ?_
  have hj : j < n := mem_range.1 hj
  rw [hcoeff, show n - 1 - j = n - (j + 1) by omega]
  have hpow : (x - α) ^ n = (x - α) ^ (n - (j + 1)) * (x - α) ^ (j + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [hpow]
  field_simp

/-- DLMF 1.2.16: if `m₁, …, mₙ` are positive integers, the `α_j` are distinct and
`deg f < ∑ m_j`, then there are polynomials `f_j` with `deg f_j < m_j` such that
`f(x)/∏_j (x-α_j)^{m_j} = ∑_j f_j(x)/(x-α_j)^{m_j}` at every `x` different from all `α_j`.
(The positivity of the `m_j` is not needed.) Derived from Mathlib's
`Polynomial.eq_quo_mul_prod_add_sum_rem_mul_prod`. -/
@[dlmf 1.2.E16]
theorem exists_div_prod_pow_sub_eq_sum {K : Type*} [Field K] {n : ℕ} {α : Fin n → K}
    (hα : Function.Injective α) (m : Fin n → ℕ) {f : K[X]} (hf : f.degree < ∑ j, m j) :
    ∃ g : Fin n → K[X], (∀ j, (g j).degree < m j) ∧
      ∀ x : K, (∀ j, x ≠ α j) →
        f.eval x / ∏ j, (x - α j) ^ m j = ∑ j, (g j).eval x / (x - α j) ^ m j := by
  classical
  set g : Fin n → K[X] := fun j => (X - C (α j)) ^ m j with hg
  have hgm : ∀ i ∈ (univ : Finset (Fin n)), (g i).Monic := fun i _ => (monic_X_sub_C _).pow _
  have hcop : Set.Pairwise (univ : Finset (Fin n)) fun i j => IsCoprime (g i) (g j) :=
    fun i _ j _ hij => ((pairwise_coprime_X_sub_C hα) hij).pow
  obtain ⟨q, r, hr, hfe⟩ := eq_quo_mul_prod_add_sum_rem_mul_prod f hgm hcop
  have hgdeg : ∀ j, (g j).degree = m j := fun j => by simp [hg, degree_pow]
  have hPm : (∏ j, g j).Monic := monic_prod_of_monic _ _ hgm
  have hPdeg : (∏ j, g j).degree = ∑ j, m j := by
    rw [degree_prod]; simp [hgdeg]
  -- the remainder sum has degree less than the full denominator
  have hR : (∑ i, r i * ∏ k ∈ univ.erase i, g k).degree < (∏ j, g j).degree := by
    refine (degree_sum_le _ _).trans_lt ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_iff_ne_bot.2 (by
      rw [Ne, degree_eq_bot]; exact hPm.ne_zero))]
    intro i _
    have hne : (∏ k ∈ univ.erase i, g k) ≠ 0 :=
      (monic_prod_of_monic _ _ fun k hk => hgm k (mem_univ k)).ne_zero
    rw [← mul_prod_erase univ g (mem_univ i), degree_mul, degree_mul]
    have dnb : (∏ k ∈ univ.erase i, g k).degree ≠ ⊥ := by rwa [Ne, degree_eq_bot]
    by_cases hri : r i = 0
    · rw [hri, degree_zero, WithBot.bot_add]
      exact WithBot.bot_lt_iff_ne_bot.2 (by
        rw [← degree_mul, Ne, degree_eq_bot]
        exact mul_ne_zero (hgm i (mem_univ i)).ne_zero hne)
    · rw [WithBot.add_lt_add_iff_right dnb]
      exact hr i (mem_univ i)
  have hq : q = 0 := by
    by_contra hq0
    have h1 : (∏ j, g j).degree ≤ (q * ∏ j, g j).degree :=
      mul_comm q (∏ j, g j) ▸ degree_le_mul_left _ hq0
    have h2 : (q * ∏ j, g j) = f - ∑ i, r i * ∏ k ∈ univ.erase i, g k := by
      rw [hfe]; ring
    have h3 : (f - ∑ i, r i * ∏ k ∈ univ.erase i, g k).degree < (∏ j, g j).degree :=
      (degree_sub_le _ _).trans_lt (max_lt (hPdeg ▸ hf) hR)
    rw [← h2] at h3
    exact absurd h1 (not_le.2 h3)
  refine ⟨r, fun j => (hr j (mem_univ j)).trans_eq (hgdeg j), fun x hx => ?_⟩
  have hgx : ∀ j, (g j).eval x = (x - α j) ^ m j := fun j => by simp [hg]
  have hne : ∀ j, (x - α j) ^ m j ≠ 0 := fun j => pow_ne_zero _ (sub_ne_zero.2 (hx j))
  rw [hfe, hq, zero_mul, zero_add, eval_finsetSum, sum_div]
  refine sum_congr rfl fun i _ => ?_
  rw [eval_mul, eval_prod, ← mul_prod_erase univ (fun j => (x - α j) ^ m j) (mem_univ i)]
  simp only [hgx]
  have hE : ∏ k ∈ univ.erase i, (x - α k) ^ m k ≠ 0 :=
    prod_ne_zero_iff.2 fun k _ => hne k
  field_simp

end DLMF.AlgebraicAnalytic
