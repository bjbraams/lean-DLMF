/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.Permutations.CyclesAndExcedances
public import DLMFMathlib.Analysis.Analytic.OfScalarsUnique
public import DLMFMathlib.RingTheory.PowerSeriesEvaluation
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Eulerian numbers (DLMF §26.14)

Properties of the Eulerian numbers `⟨n k⟩` (`eulerianNumber`) and the distribution of the
inversion number and major index over `𝔖_n`.

## Main results

* `eulerianNumber_eq_card_excedance`, `eulerianNumber_eq_card_weakExcedance`: `⟨n k⟩` also
  counts permutations by (weak) excedances (DLMF §26.14(i)).
* `sum_pow_inversionNumber`: `∑_σ q^{inv σ} = ∑_σ q^{maj σ} = ∏_{j=1}^n (1 - q^j)/(1 - q)`
  (DLMF 26.14.3).
* `hasSum_eulerianNumber`: the exponential generating function (DLMF 26.14.4).
* `worpitzky`: Worpitzky's identity (DLMF 26.14.5).
* `eulerianNumber_eq_sum`, `eulerianNumber_eq_sum_stirlingSecond`: explicit sums
  (DLMF 26.14.6, 26.14.7).
* `eulerianNumber_recurrence`, `eulerianNumber_symm`, `sum_eulerianNumber`: the recurrence,
  symmetry and row sums (DLMF 26.14.8–26.14.10).
* `bernoulli_eq_sum_eulerianNumber`, `stirlingSecond_eq_sum_eulerianNumber`: relations to
  Bernoulli and Stirling numbers (DLMF 26.14.11, 26.14.12).
* `eulerianNumber_zero_left`, `eulerianNumber_zero_right`, `eulerianNumber_one_right`,
  `eulerianNumber_two_right`: special values (DLMF 26.14.13–26.14.16).
* `eulerianNumber_table`: a few entries of Table 26.14.1.

## References

* NIST DLMF §26.14.
-/

@[expose] public section

noncomputable section

open Finset Equiv

open Polynomial hiding bernoulli

namespace DLMF.Combinatorics

/-- `⟨0 k⟩ = δ_{0k}` (restated before its tagged form (26.14.13) below). -/
private lemma eulerianNumber_zero_left_eq_ite (k : ℕ) : eulerianNumber 0 k = if k =
    0 then 1 else 0 := by
  unfold eulerianNumber
  have h0 : ∀ σ : Perm (Fin 0), descentNumber σ = 0 := fun σ => by
    simp [descentNumber, wordDescentSet]
  split_ifs with hk
  · subst hk
    rw [Finset.filter_true_of_mem fun σ _ => h0 σ, card_univ]; simp
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro σ _ h
    exact hk (h ▸ h0 σ)

/-- The falling-factorial identity behind the Worpitzky induction. -/
private lemma mul_eval_descPochhammer_eq (n : ℕ) (x : ℂ) (k : ℕ) :
    (n + 1 : ℂ) * x * (descPochhammer ℂ n).eval (x + k) =
      (k + 1) * (descPochhammer ℂ (n + 1)).eval (x + k) +
        (n - k) * (descPochhammer ℂ (n + 1)).eval (x + k + 1) := by
  rw [descPochhammer_succ_eval, descPochhammer_succ_left, eval_mul, eval_X, eval_comp,
    eval_sub, eval_X, eval_one, add_sub_cancel_right]
  ring

/-- Worpitzky (26.14.5) multiplied by `n!`, summed to `n`, for all `n`. -/
private lemma sum_eulerianNumber_mul_eval_descPochhammer (n : ℕ) (x : ℂ) :
    ∑ k ∈ range (n + 1), (eulerianNumber n k : ℂ) * (descPochhammer ℂ n).eval (x + k) =
      n.factorial * x ^ n := by
  induction n with
  | zero => simp [eulerianNumber_zero_left_eq_ite]
  | succ n ih =>
    have hz : eulerianNumber n (n + 1) = 0 := by
      rcases n with _ | m
      · simp [eulerianNumber_zero_left_eq_ite]
      · exact eulerianNumber_succ_eq_zero_of_le (by omega) (by omega)
    have hsplit : ∀ k, (eulerianNumber (n + 1) k : ℂ) * (descPochhammer ℂ (n + 1)).eval (x + k) =
        ((k : ℂ) + 1) * (eulerianNumber n k : ℂ) * (descPochhammer ℂ (n + 1)).eval (x + k) +
        (if 1 ≤ k then ((n + 1 - k : ℕ) : ℂ) * (eulerianNumber n (k - 1) : ℂ) else 0) *
          (descPochhammer ℂ (n + 1)).eval (x + k) := by
      intro k; rw [eulerianNumber_succ_eq]; push_cast; split_ifs <;> ring
    rw [sum_congr rfl fun k _ => hsplit k, sum_add_distrib]
    rw [sum_range_succ' (fun k => ((if 1 ≤ k then ((n + 1 - k : ℕ) : ℂ) *
      (eulerianNumber n (k - 1) : ℂ) else 0) * (descPochhammer ℂ (n + 1)).eval (x + k)))]
    rw [sum_range_succ (fun k => ((k : ℂ) + 1) * (eulerianNumber n k : ℂ) *
      (descPochhammer ℂ (n + 1)).eval (x + k)), hz]
    have h10 : ¬ (1 ≤ 0) := by omega
    simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero, Nat.le_add_left, ite_true,
      Nat.add_sub_cancel, ite_eq_right h10, Nat.factorial_succ]
    rw [← sum_add_distrib, show (((n + 1) * n.factorial : ℕ) : ℂ) * x ^ (n + 1) =
      ((n + 1 : ℂ) * x) * (n.factorial * x ^ n) by push_cast; ring, ← ih, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have := mul_eval_descPochhammer_eq n x k
    rw [show n + 1 - (k + 1) = n - k by omega, Nat.cast_sub hk']
    push_cast
    simp only [add_assoc] at this ⊢
    linear_combination (-(eulerianNumber n k : ℂ)) * this

/-- Worpitzky at natural arguments: `mⁿ = ∑ₖ ⟨n k⟩ C(m+k, n)`. -/
private lemma pow_eq_sum_eulerianNumber_mul_choose (n m : ℕ) :
    m ^ n = ∑ k ∈ range (n + 1), eulerianNumber n k * (m + k).choose n := by
  have h := sum_eulerianNumber_mul_eval_descPochhammer n (m : ℂ)
  have e : ∀ k : ℕ, (descPochhammer ℂ n).eval ((m : ℂ) + k) =
      ((n.factorial * (m + k).choose n : ℕ) : ℂ) := by
    intro k
    rw [show (m : ℂ) + k = ((m + k : ℕ) : ℂ) by push_cast; ring,
      descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  simp_rw [e] at h
  have h' : ((n.factorial * ∑ k ∈ range (n + 1), eulerianNumber n k * (m + k).choose n : ℕ) : ℂ) =
      ((n.factorial * m ^ n : ℕ) : ℂ) := by
    push_cast at h ⊢
    rw [← h, mul_sum]
    exact sum_congr rfl fun k _ => by ring
  have := Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos n) (Nat.cast_injective h')
  exact this.symm

/-- Uniqueness of coefficients in the binomial basis `C(m, j)`. -/
private lemma eq_of_sum_choose_mul_eq (n : ℕ) (a b : ℕ → ℕ)
    (h : ∀ m : ℕ, ∑ j ∈ range (n + 1), m.choose j * a j = ∑ j ∈ range (n + 1), m.choose j * b j) :
    ∀ j ≤ n, a j = b j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have hm := h j
    have hs : ∀ c : ℕ → ℕ, ∑ i ∈ range (n + 1), j.choose i * c i =
        ∑ i ∈ range j, j.choose i * c i + c j := by
      intro c
      rw [← sum_range_add_sum_Ico _ (show j + 1 ≤ n + 1 by omega), sum_range_succ,
        Nat.choose_self, one_mul, sum_eq_zero (s := Ico (j + 1) (n + 1)) fun i hi => by
          rw [Nat.choose_eq_zero_of_lt (by simp at hi; omega), zero_mul], add_zero]
    rw [hs, hs, sum_congr rfl fun i hi => by rw [ih i (mem_range.mp hi) (by simp at hi; omega)]]
      at hm
    omega

/-- `j! S(n, j) = ∑ₖ ⟨n k⟩ C(k, n-j)` (Worpitzky and Vandermonde). -/
private lemma factorial_mul_stirlingSecond_eq_sum_eulerianNumber (n j : ℕ) (hj : j ≤ n) :
    j.factorial * Nat.stirlingSecond n j =
      ∑ k ∈ range (n + 1), eulerianNumber n k * k.choose (n - j) := by
  refine eq_of_sum_choose_mul_eq n (fun j => j.factorial * Nat.stirlingSecond n j)
    (fun j => ∑ k ∈ range (n + 1), eulerianNumber n k * k.choose (n - j)) (fun m => ?_) j hj
  have h1 := Nat.pow_eq_sum_stirlingSecond_mul_descFactorial m n
  simp only [Nat.descFactorial_eq_factorial_mul_choose] at h1
  calc ∑ j ∈ range (n + 1), m.choose j * (j.factorial * Nat.stirlingSecond n j) = m ^ n := by
        rw [h1]; exact sum_congr rfl fun j _ => by ring
    _ = ∑ k ∈ range (n + 1), eulerianNumber n k * (m + k).choose n :=
        pow_eq_sum_eulerianNumber_mul_choose n m
    _ = ∑ k ∈ range (n + 1), eulerianNumber n k *
          ∑ j ∈ range (n + 1), m.choose j * k.choose (n - j) := by
        refine sum_congr rfl fun k _ => ?_
        rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => m.choose i * k.choose j)]
    _ = _ := by
        simp_rw [mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring

/-- The orthogonality `∑_t (-1)^t C(k+t, k) C(l, k+t) = δ_{lk}` for `l ≤ k + N`. -/
private lemma sum_neg_one_pow_choose_mul_choose_eq_ite (k l N : ℕ) (hl : l ≤ k + N) :
    ∑ t ∈ range (N + 1), (-1 : ℤ) ^ t * (k + t).choose k * l.choose (k + t) =
      if l = k then 1 else 0 := by
  have e : ∀ t, ((k + t).choose k : ℤ) * l.choose (k + t) = l.choose k * (l - k).choose t := by
    intro t
    have := Nat.choose_mul (n := l) (k := k + t) (s := k) (by omega)
    rw [Nat.add_sub_cancel_left] at this
    exact_mod_cast (by rw [mul_comm]; exact this)
  simp_rw [mul_assoc, e]
  by_cases hlk : k ≤ l
  · obtain ⟨d, rfl⟩ : ∃ d, l = k + d := ⟨l - k, by omega⟩
    rw [Nat.add_sub_cancel_left]
    rw [← sum_range_add_sum_Ico _ (show d + 1 ≤ N + 1 by omega)]
    rw [sum_eq_zero (s := Ico (d + 1) (N + 1)) fun t ht => by
      rw [Nat.choose_eq_zero_of_lt (n := d) (by simp at ht; omega)]; simp, add_zero]
    have := Int.alternating_sum_range_choose (n := d)
    simp_rw [mul_left_comm _ ((k + d).choose k : ℤ)]
    rw [← mul_sum, this]
    by_cases hd : d = 0
    · subst hd; simp
    · rw [ite_eq_right hd, ite_eq_right (by omega)]; simp
  · rw [ite_eq_right (by omega)]
    refine sum_eq_zero fun t _ => ?_
    rw [Nat.choose_eq_zero_of_lt (by omega : l < k)]; simp

/-- The right side of (26.14.6). -/
def eulerianAlternatingSum (n k : ℕ) : ℤ :=
  ∑ j ∈ range (k + 1), (-1 : ℤ) ^ j * (n + 1).choose j * (k + 1 - j) ^ n

/-- The right side of (26.14.6) at `n = 0`. -/
private lemma eulerianAlternatingSum_zero (K : ℕ) : eulerianAlternatingSum 0 K = if K =
    0 then 1 else 0 := by
  unfold eulerianAlternatingSum
  split_ifs with hK
  · subst hK; simp
  · obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
    simp only [pow_zero, mul_one, zero_add]
    rw [← Finset.sum_range_add_sum_Ico _ (show 2 ≤ k + 1 + 1 by omega)]
    rw [Finset.sum_eq_zero (s := Ico 2 (k + 1 + 1)) fun j hj => by
      rw [Nat.choose_eq_zero_of_lt (by simp at hj; omega)]; simp]
    simp [sum_range_succ]

/-- The right side of (26.14.6) satisfies the Eulerian recurrence. -/
private lemma eulerianAlternatingSum_succ_succ (n k : ℕ) :
    eulerianAlternatingSum (n + 1) (k + 1) =
      (k + 2) * eulerianAlternatingSum n (k + 1) + ((n : ℤ) + 1 - (k + 1)) *
          eulerianAlternatingSum n k := by
  unfold eulerianAlternatingSum
  rw [sum_range_succ' _ (k + 1), sum_range_succ' _ (k + 1), mul_add, mul_sum, mul_sum]
  have h0 : (-1 : ℤ) ^ 0 * ((n + 1 + 1).choose 0 : ℕ) *
        (((k + 1 : ℕ) : ℤ) + 1 - ((0 : ℕ) : ℤ)) ^ (n + 1) =
      ((k : ℤ) + 2) * ((-1) ^ 0 * ((n + 1).choose 0 : ℕ) *
        (((k + 1 : ℕ) : ℤ) + 1 - ((0 : ℕ) : ℤ)) ^ n) := by
    simp only [Nat.choose_zero_right]; push_cast; ring
  rw [h0]
  conv_rhs => rw [add_right_comm, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  · 
    have hi' : i < k + 1 := mem_range.mp hi
    have h := Nat.choose_succ_right_eq (n + 1) i
    rw [Nat.choose_succ_succ]
    push_cast
    have h' : ((n + 1).choose (i + 1) : ℤ) * (i + 1) = ((n + 1).choose i) * ((n : ℤ) + 1 - i) := by
      rcases le_or_gt i (n + 1) with hin | hin
      · have := congrArg (Nat.cast : ℕ → ℤ) h
        push_cast [Nat.cast_sub hin] at this
        linear_combination this
      · rw [Nat.choose_eq_zero_of_lt hin, Nat.choose_eq_zero_of_lt (by omega)]; simp
    rw [show (k : ℤ) + 1 + 1 - (i + 1) = k + 1 - i by ring]
    rw [pow_succ]
    simp only [Nat.succ_eq_add_one] at *
    linear_combination ((-1 : ℤ) ^ i * ((k : ℤ) + 1 - i) ^ n) * h'

/-- §26.14(i): `⟨n k⟩` is also the number of permutations with exactly `k` excedances. -/
@[dlmf 26.14.i]
theorem eulerianNumber_eq_card_excedance (n k : ℕ) :
    eulerianNumber n k = #{σ : Perm (Fin n) | excedanceNumber σ = k} := by
  induction n generalizing k with
  | zero =>
    have h : ∀ σ : Perm (Fin 0), excedanceNumber σ = 0 := fun σ => by simp [excedanceNumber]
    simp only [h]
    unfold eulerianNumber
    have h' : ∀ σ : Perm (Fin 0), descentNumber σ = 0 := fun σ => by
      simp [descentNumber, wordDescentSet]
    simp only [h']
  | succ n ih =>
    rw [eulerianNumber_succ_eq, card_filter_excedanceNumber_succ, ih, ih]

/-- §26.14(i): for `n ≥ 1`, `⟨n k⟩` is also the number of permutations with exactly `k + 1`
weak excedances (for `n = 0` there are no weak excedances while `⟨0 0⟩ = 1`). -/
@[dlmf 26.14.i]
theorem eulerianNumber_eq_card_weakExcedance {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    eulerianNumber n k = #{σ : Perm (Fin n) | weakExcedanceNumber σ = k + 1} := by
  have hcomp : ∀ σ : Perm (Fin n), weakExcedanceNumber σ + excedanceNumber σ⁻¹ = n := by
    intro σ
    have h1 : excedanceNumber σ⁻¹ = #{j : Fin n | σ j < j} := by
      rw [excedanceNumber]
      refine card_bij (fun i _ => σ⁻¹ i) ?_ ?_ ?_
      · intro i hi; simp only [mem_filter, mem_univ, true_and] at hi ⊢; simpa using hi
      · intro a _ b _ h; exact σ⁻¹.injective h
      · intro j hj
        refine ⟨σ j, ?_, by simp⟩
        simp only [mem_filter, mem_univ, true_and] at hj ⊢; simpa using hj
    rw [h1, weakExcedanceNumber]
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun j => j ≤ σ j)
    simp only [not_le, card_univ, Fintype.card_fin] at this
    exact this
  have hle : ∀ σ : Perm (Fin n), excedanceNumber σ ≤ n := fun σ =>
    (card_le_univ _).trans (by simp)
  by_cases hk : k < n
  · rw [eulerianNumber_symm_of_lt hk, eulerianNumber_eq_card_excedance]
    refine card_bij (fun σ _ => σ⁻¹) ?_ ?_ ?_
    · intro σ hσ
      simp only [mem_filter, mem_univ, true_and] at hσ ⊢
      have := hcomp σ⁻¹
      rw [inv_inv] at this
      omega
    · intro a _ b _ h; exact inv_injective h
    · intro τ hτ
      refine ⟨τ⁻¹, ?_, inv_inv τ⟩
      simp only [mem_filter, mem_univ, true_and] at hτ ⊢
      have := hcomp τ
      have := hle τ⁻¹
      omega
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [eulerianNumber_succ_eq_zero_of_le (by omega) hn, eq_comm, card_eq_zero, filter_eq_empty_iff]
    intro σ _ h
    have := hcomp σ
    omega

/-- Table 26.14.1, a few entries: `⟨3 1⟩ = 4`, `⟨4 1⟩ = 11`, `⟨5 2⟩ = 66`. -/
@[dlmf 26.14.T1]
theorem eulerianNumber_table :
    eulerianNumber 3 1 = 4 ∧ eulerianNumber 4 1 = 11 ∧ eulerianNumber 5 2 = 66 := by
  decide +kernel

/-- (26.14.3): `∑_σ q^{inv σ} = ∑_σ q^{maj σ} = ∏_{j=1}^n (1 - q^j)/(1 - q)` for `q ≠ 1`. -/
@[dlmf 26.14.E3]
theorem sum_pow_inversionNumber {q : ℂ} (hq : q ≠ 1) (n : ℕ) :
    ∑ σ : Perm (Fin n), q ^ inversionNumber σ = ∏ j ∈ Icc 1 n, (1 - q ^ j) / (1 - q) ∧
      ∑ σ : Perm (Fin n), q ^ majorIndex σ = ∏ j ∈ Icc 1 n, (1 - q ^ j) / (1 - q) := by
  refine ⟨?_, ?_⟩
  ·   have hq' : 1 - q ≠ 0 := sub_ne_zero.mpr hq.symm
      induction n with
      | zero => simp [inversionNumber, wordInversions]
      | succ n ih =>
        rw [Finset.prod_Icc_succ_top (by omega), ← ih]
        rcases n with _ | n
        · simp [inversionNumber, wordInversions, div_self hq']
        rw [← (Perm.decomposeFin' (n := n)).symm.sum_comp, Fintype.sum_prod_type]
        simp only [Perm.decomposeFin'_symm, inversionNumber_decomposeFin'Symm, pow_add,
          ← Finset.mul_sum, ← Finset.sum_mul]
        congr 1
        rw [Fin.sum_univ_eq_sum_range (fun i => q ^ i), eq_div_iff hq', mul_comm, mul_neg_geom_sum]
        ring
  ·   have hq' : 1 - q ≠ 0 := sub_ne_zero.mpr hq.symm
      induction n with
      | zero => simp [majorIndex, wordMajorIndex, wordDescentSet]
      | succ n ih =>
        rw [Finset.prod_Icc_succ_top (by omega), ← ih]
        rcases n with _ | n
        · simp [majorIndex, wordMajorIndex, wordDescentSet, div_self hq']
        rw [← (insertMinEquiv (n := n)).sum_comp, Fintype.sum_prod_type_right]
        simp only [majorIndex_insertMinEquiv, pow_add, ← Finset.mul_sum]
        rw [Finset.sum_mul]
        refine sum_congr rfl fun σ _ => ?_
        congr 1
        rw [Fin.sum_univ_eq_sum_range
          (fun p => q ^ majorIndexIncrement (wordDescentSet fun i => (σ i : ℕ)) p),
          sum_pow_majorIndexIncrement q
              (by simpa using wordDescentSet_subset_range (fun i => (σ i : ℕ))),
          eq_div_iff hq', mul_comm, mul_neg_geom_sum]
        ring


/-- (26.14.5), Worpitzky's identity: `∑_{k=0}^{n-1} ⟨n k⟩ C(x + k, n) = xⁿ` for `n ≥ 1` and
every `x ∈ ℂ`, with `C(y, n) = y(y-1)⋯(y-n+1)/n!`. -/
@[dlmf 26.14.E5]
theorem worpitzky {n : ℕ} (hn : 1 ≤ n) (x : ℂ) :
    ∑ k ∈ range n, (eulerianNumber n k : ℂ) * ((descPochhammer ℂ n).eval (x + k) / n.factorial) =
      x ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := sum_eulerianNumber_mul_eval_descPochhammer (m + 1) x
  rw [sum_range_succ, eulerianNumber_succ_eq_zero_of_le (n := m + 1) (k := m) le_rfl hn] at h
  simp only [Nat.cast_zero, zero_mul, add_zero] at h
  have hf : ((m + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  simp_rw [mul_div_assoc']
  rw [← sum_div, h]
  field_simp

/-- (26.14.6) for every `n`, including `n = 0` (stronger than DLMF). -/
private lemma eulerianNumber_eq_eulerianAlternatingSum (n k : ℕ) : (eulerianNumber n k : ℤ) =
    eulerianAlternatingSum n k := by
  induction n generalizing k with
  | zero => rw [eulerianNumber_zero_left_eq_ite, eulerianAlternatingSum_zero]; split_ifs <;> simp
  | succ n ih =>
    rw [eulerianNumber_succ_eq]
    rcases k with _ | k
    · simp [ih, eulerianAlternatingSum]
    rw [eulerianAlternatingSum_succ_succ, ← ih, ← ih]
    simp only [show 1 ≤ k + 1 from by omega, ite_true, Nat.add_sub_cancel]
    by_cases hkn : k ≤ n
    · push_cast [Nat.cast_sub hkn]; ring
    · have hz : eulerianNumber n k = 0 := by
        rcases n with _ | m
        · rw [eulerianNumber_zero_left_eq_ite]; simp; omega
        · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
          exact eulerianNumber_succ_eq_zero_of_le (by omega) (by omega)
      have hz' : eulerianNumber n (k + 1) = 0 := by
        rcases n with _ | m
        · rw [eulerianNumber_zero_left_eq_ite]; simp
        · exact eulerianNumber_succ_eq_zero_of_le (by omega) (by omega)
      simp [hz, hz']

/-- (26.14.6): `⟨n k⟩ = ∑_{j=0}^k (-1)^j C(n+1, j) (k+1-j)ⁿ` for `n ≥ 1`. -/
@[dlmf 26.14.E6]
theorem eulerianNumber_eq_sum {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    (eulerianNumber n k : ℤ) =
      ∑ j ∈ range (k + 1), (-1 : ℤ) ^ j * (n + 1).choose j * (k + 1 - j) ^ n := by
  exact (fun _ => eulerianNumber_eq_eulerianAlternatingSum n k) hn

/-- (26.14.7): `⟨n k⟩ = ∑_{j=0}^{n-k} (-1)^{n-k-j} j! C(n-j, k) S(n, j)`, with
`S = Nat.stirlingSecond`. -/
@[dlmf 26.14.E7]
theorem eulerianNumber_eq_sum_stirlingSecond (n k : ℕ) :
    (eulerianNumber n k : ℤ) = ∑ j ∈ range (n - k + 1),
      (-1 : ℤ) ^ (n - k - j) * j.factorial * (n - j).choose k * Nat.stirlingSecond n j := by
  by_cases hkn : k ≤ n
  · rw [← sum_range_reflect]
    have step : ∀ t ∈ range (n - k + 1), (-1 : ℤ) ^ (n - k - (n - k + 1 - 1 - t)) *
        (n - k + 1 - 1 - t).factorial * (n - (n - k + 1 - 1 - t)).choose k *
          Nat.stirlingSecond n (n - k + 1 - 1 - t) =
        ∑ l ∈ range (n + 1), (eulerianNumber n l : ℤ) *
          ((-1 : ℤ) ^ t * (k + t).choose k * l.choose (k + t)) := by
      intro t ht
      have ht' := mem_range.mp ht
      have h := factorial_mul_stirlingSecond_eq_sum_eulerianNumber n (n - k + 1 - 1 - t) (by omega)
      rw [show n - (n - k + 1 - 1 - t) = k + t by omega] at h
      have h' : ((n - k + 1 - 1 - t).factorial : ℤ) * Nat.stirlingSecond n (n - k + 1 - 1 - t) =
          ∑ l ∈ range (n + 1), (eulerianNumber n l : ℤ) * l.choose (k + t) := by
        exact_mod_cast h
      rw [show n - k - (n - k + 1 - 1 - t) = t by omega,
        show n - (n - k + 1 - 1 - t) = k + t by omega]
      calc (-1 : ℤ) ^ t * ((n - k + 1 - 1 - t).factorial : ℤ) * ((k + t).choose k : ℤ) *
            (Nat.stirlingSecond n (n - k + 1 - 1 - t) : ℤ) =
          (-1 : ℤ) ^ t * ((k + t).choose k : ℤ) * (((n - k + 1 - 1 - t).factorial : ℤ) *
            Nat.stirlingSecond n (n - k + 1 - 1 - t)) := by ring
        _ = _ := by
          rw [h', mul_sum]
          exact sum_congr rfl fun l _ => by ring
    rw [sum_congr rfl step, sum_comm]
    simp_rw [← mul_sum]
    rw [sum_congr rfl fun l hl => by
      rw [sum_neg_one_pow_choose_mul_choose_eq_ite k l (n - k) (by have := mem_range.mp hl; omega)]]
    simp only [mul_ite, mul_one, mul_zero]
    rw [sum_ite_eq' (range (n + 1)) k, ite_eq_left (mem_range.mpr (by omega))]
  · have hz : eulerianNumber n k = 0 := by
      rcases n with _ | m
      · rw [eulerianNumber_zero_left_eq_ite, ite_eq_right (by omega)]
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        exact eulerianNumber_succ_eq_zero_of_le (by omega) (by omega)
    rw [hz, show n - k = 0 by omega]
    simp [Nat.choose_eq_zero_of_lt (by omega : n < k)]

/-- (26.14.8): `⟨n k⟩ = (k+1)⟨n-1, k⟩ + (n-k)⟨n-1, k-1⟩` for `n ≥ 2` and `k ≥ 1` (for `k = 0`
see (26.14.14)); the coefficient `n - k` is an integer. -/
@[dlmf 26.14.E8]
theorem eulerianNumber_recurrence {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    (eulerianNumber n k : ℤ) =
      (k + 1) * eulerianNumber (n - 1) k + ((n : ℤ) - k) * eulerianNumber (n - 1) (k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [eulerianNumber_succ_succ_nat]
  simp only [show m + 2 - 1 = m + 1 by omega, Nat.add_sub_cancel]
  by_cases hj : j ≤ m + 1
  · push_cast [hj]
    ring
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [eulerianNumber_succ_eq_zero_of_le (by omega) (by omega),
      eulerianNumber_succ_eq_zero_of_le (n := m + 1) (k := i) (by omega) (by omega)]
    simp

/-- (26.14.9): `⟨n k⟩ = ⟨n, n-1-k⟩` for `n ≥ 1` and `k ≤ n - 1` (for `k ≥ n` both sides are
`0` in DLMF's convention). -/
@[dlmf 26.14.E9]
theorem eulerianNumber_symm {n k : ℕ} (hk : k < n) :
    eulerianNumber n k = eulerianNumber n (n - 1 - k) :=
  eulerianNumber_symm_of_lt hk

/-- A permutation of `Fin n` has at most `n - 1` descents. -/
private lemma descentNumber_lt {n : ℕ} (hn : 1 ≤ n) (σ : Perm (Fin n)) : descentNumber σ < n := by
  unfold descentNumber
  have hsub : wordDescentSet (fun i => (σ i : ℕ)) ⊆ range (n - 1) := by
    intro j hj
    simp only [wordDescentSet, mem_filter, mem_range] at hj
    obtain ⟨_, h, _⟩ := hj
    simp only [mem_range]; omega
  have := card_le_card hsub
  simp only [card_range] at this
  omega

/-- (26.14.10): `∑_{k=0}^{n-1} ⟨n k⟩ = n!` for `n ≥ 1`. -/
@[dlmf 26.14.E10]
theorem sum_eulerianNumber {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ range n, eulerianNumber n k = n.factorial := by
  unfold eulerianNumber
  rw [← Finset.card_biUnion]
  · have : (range n).biUnion (fun k => ({σ : Perm (Fin n) | descentNumber σ = k} : Finset _)) =
        univ := by
      ext σ
      simp only [mem_biUnion, mem_range, mem_filter, mem_univ, true_and, iff_true]
      exact ⟨_, descentNumber_lt hn σ, rfl⟩
    rw [this, card_univ, Fintype.card_perm, Fintype.card_fin]
  · intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro σ h1 h2
    simp only [mem_filter] at h1 h2
    exact hij (h1.2.symm.trans h2.2)

/-- The alternating sum of Eulerian numbers in the form of (24.6.11). -/
private lemma alternating_sum_eulerianNumber_eq (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ range n, (-1 : ℚ) ^ k * eulerianNumber n k =
      ∑ K ∈ Icc 1 (n + 1), ∑ j ∈ range K,
        (-1 : ℚ) ^ (j + 1) * ((n + 1).choose K : ℚ) * (j : ℚ) ^ n := by
  have h6 : ∀ k, ((eulerianNumber n k : ℤ) : ℚ) = ∑ j ∈ range (k + 1),
      (-1 : ℚ) ^ j * (n + 1).choose j * ((k : ℚ) + 1 - j) ^ n := by
    intro k
    rw [eulerianNumber_eq_sum hn k]
    push_cast; rfl
  simp only [Int.cast_natCast] at h6
  simp_rw [h6, mul_sum]
  rw [sum_sigma', sum_sigma']
  have hterm : ∀ k j, j ≤ k → j ≤ n + 1 →
      (-1 : ℚ) ^ k * ((-1 : ℚ) ^ j * ((n + 1).choose j : ℚ) * ((k : ℚ) + 1 - j) ^ n) =
        (-1 : ℚ) ^ (k + 1 - j + 1) * ((n + 1).choose (n + 1 - j) : ℚ) *
          (((k + 1 - j : ℕ) : ℚ)) ^ n := by
    intro k j hjk hjn
    obtain ⟨d, rfl⟩ : ∃ d, k = j + d := ⟨k - j, by omega⟩
    rw [Nat.choose_symm hjn, show j + d + 1 - j = d + 1 by omega]
    push_cast
    rw [show (j : ℚ) + d + 1 - j = d + 1 by ring]
    have h2 : ((-1 : ℚ) ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [pow_add, pow_add, pow_add]
    linear_combination (-(1 : ℚ)) ^ d * ((n + 1).choose j : ℚ) * ((d : ℚ) + 1) ^ n * h2
  refine sum_bij_ne_zero (fun x _ _ => ⟨n + 1 - x.2, x.1 + 1 - x.2⟩) ?_ ?_ ?_ ?_
  · rintro ⟨k, j⟩ hx _
    simp only [mem_sigma, mem_range, mem_Icc] at hx ⊢
    omega
  · rintro ⟨k, j⟩ hx _ ⟨k', j'⟩ hx' _ h
    simp only [mem_sigma, mem_range] at hx hx'
    simp only [Sigma.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have : j = j' := by omega
    subst this
    have : k = k' := by have := eq_of_heq h2; omega
    subst this
    rfl
  · rintro ⟨K, j⟩ hy hne
    simp only [mem_sigma, mem_range, mem_Icc] at hy
    have hj : j ≠ 0 := by
      rintro rfl; apply hne; simp [zero_pow (by omega : n ≠ 0)]
    refine ⟨⟨j + n - K, n + 1 - K⟩, ?_, ?_, ?_⟩
    · simp only [mem_sigma, mem_range]; omega
    · intro h0
      apply hne
      rw [hterm _ _ (by dsimp only; omega) (by dsimp only; omega)] at h0
      rw [← h0]
      dsimp only
      rw [show n + 1 - (n + 1 - K) = K by omega, show j + n - K + 1 - (n + 1 - K) = j by omega]
    · simp only [Sigma.mk.injEq]
      refine ⟨by omega, ?_⟩
      rw [heq_eq_eq]; omega
  · rintro ⟨k, j⟩ hx _
    simp only [mem_sigma, mem_range] at hx
    exact hterm k j (by omega) (by omega)

/-- (26.14.11): `B_m = m/(2^m (2^m - 1)) ∑_{k=0}^{m-2} (-1)^k ⟨m-1, k⟩` for `m ≥ 2`
(`bernoulli`, the Bernoulli numbers with `B_1 = -1/2`). -/
@[dlmf 26.14.E11]
theorem bernoulli_eq_sum_eulerianNumber {m : ℕ} (hm : 2 ≤ m) :
    bernoulli m = (m : ℚ) / (2 ^ m * (2 ^ m - 1)) *
      ∑ k ∈ range (m - 1), (-1 : ℚ) ^ k * eulerianNumber (m - 1) k := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel, alternating_sum_eulerianNumber_eq n (by omega),
    DLMF.BernoulliEuler.bernoulli_eq_explicit₁₁ (by omega), Nat.add_sub_cancel]

/-- (26.14.12): `S(n, m) = (1/m!) ∑_{k=0}^{n-1} ⟨n k⟩ C(k, n-m)` for `n ≥ m`, `n ≥ 1`. -/
@[dlmf 26.14.E12]
theorem stirlingSecond_eq_sum_eulerianNumber {n m : ℕ} (hmn : m ≤ n) (hn : 1 ≤ n) :
    (Nat.stirlingSecond n m : ℚ) =
      1 / m.factorial * ∑ k ∈ range n, (eulerianNumber n k : ℚ) * k.choose (n - m) := by
  have h := factorial_mul_stirlingSecond_eq_sum_eulerianNumber n m hmn
  rw [sum_range_succ] at h
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [eulerianNumber_succ_eq_zero_of_le (n := n' + 1) (k := n') le_rfl hn, zero_mul, add_zero] at h
  have hq := congrArg (Nat.cast : ℕ → ℚ) h
  push_cast at hq
  rw [← hq]
  field_simp

/-- (26.14.13): `⟨0 k⟩ = δ_{0,k}`. -/
@[dlmf 26.14.E13]
theorem eulerianNumber_zero_left (k : ℕ) : eulerianNumber 0 k = if k = 0 then 1 else 0 := by
  unfold eulerianNumber
  have h0 : ∀ σ : Perm (Fin 0), descentNumber σ = 0 := fun σ => by
    simp [descentNumber, wordDescentSet]
  split_ifs with hk
  · subst hk
    rw [Finset.filter_true_of_mem fun σ _ => h0 σ, card_univ]; simp
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro σ _ h
    exact hk (h ▸ h0 σ)

/-- (26.14.14): `⟨n 0⟩ = 1`. -/
@[dlmf 26.14.E14]
theorem eulerianNumber_zero_right (n : ℕ) : eulerianNumber n 0 = 1 := by
  unfold eulerianNumber
  rw [Finset.card_eq_one]
  exact ⟨1, by ext σ; simp [descentNumber_eq_zero_iff]⟩

/-- (26.14.15): `⟨n 1⟩ = 2ⁿ - n - 1` for `n ≥ 1`. -/
@[dlmf 26.14.E15]
theorem eulerianNumber_one_right {n : ℕ} (hn : 1 ≤ n) :
    (eulerianNumber n 1 : ℤ) = 2 ^ n - n - 1 := by
  induction n, hn using Nat.le_induction with
  | base => rw [eulerianNumber_succ_eq_zero_of_le (n := 1) (k := 0) (by omega) le_rfl]; simp
  | succ m hm ih =>
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [eulerianNumber_succ_succ_nat, eulerianNumber_zero_right]
    push_cast
    rw [ih]
    push_cast
    ring

/-- (26.14.16): `⟨n 2⟩ = 3ⁿ - (n+1) 2ⁿ + C(n+1, 2)` for `n ≥ 1`. -/
@[dlmf 26.14.E16]
theorem eulerianNumber_two_right {n : ℕ} (hn : 1 ≤ n) :
    (eulerianNumber n 2 : ℤ) = 3 ^ n - (n + 1) * 2 ^ n + (n + 1).choose 2 := by
  induction n, hn using Nat.le_induction with
  | base => rw [eulerianNumber_succ_eq_zero_of_le (n := 1) (k := 1) (by omega) le_rfl]; simp
  | succ m hm ih =>
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [eulerianNumber_succ_succ_nat]
    push_cast
    rw [ih, eulerianNumber_one_right (by omega)]
    have h1 : ((n + 1 + 1 + 1).choose 2 : ℤ) = (n + 2) + (n + 1 + 1).choose 2 := by
      rw [Nat.choose_succ_succ]; push_cast; simp
    have h2 : ((n + 1 + 1).choose 2 : ℤ) * 2 = (n + 2) * (n + 1) := by
      have key : ∀ m : ℕ, (m + 1).choose 2 * 2 = (m + 1) * m := by
        intro m
        induction m with
        | zero => simp
        | succ m ih => rw [Nat.choose_succ_succ, add_mul, ih]; simp; ring
      exact_mod_cast key (n + 1)
    simp only [Nat.cast_add, Nat.cast_one] at h1 h2 ⊢
    rw [h1]
    linear_combination h2

/-! ### The exponential generating function (26.14.4)

Carlitz's identity `A_n(x) = (1 - x)^{n+1} ∑_j (j+1)ⁿ xʲ` (from 26.14.6) gives the generating
function for small `t` by expanding `1/(1 - x e^{(1-x)t})`; it extends to `|t| < 1` by the
identity theorem, since `e^{(x-1)t} ≠ x` there. -/

section GeneratingFunction

open Complex Filter Topology


/-- `‖e^z - 1‖ ≤ ‖z‖` for `Re z ≤ 0`. -/
private lemma norm_exp_sub_one_le_of_re_nonpos {z : ℂ} (hz : z.re ≤ 0) : ‖cexp z - 1‖ ≤ ‖z‖ := by
  have h := (convex_halfSpace_re_le 0).norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ) (f := cexp)
    (C := 1) (x := 0) (y := z) (fun w _ => differentiableAt_exp)
    (fun w hw => by
      rw [Complex.deriv_exp, norm_exp]
      exact Real.exp_le_one_iff.mpr hw) (by simp) hz
  simpa using h

/-- For `|x| < 1` and `|t| < 1`, `e^{(x-1)t} ≠ x`. -/
private lemma exp_mul_ne {x t : ℂ} (hx : ‖x‖ < 1) (ht : ‖t‖ < 1) : cexp ((x - 1) * t) ≠ x := by
  intro h
  rcases eq_or_ne x 0 with rfl | hx0
  · exact exp_ne_zero _ h
  have hre : ((x - 1) * t).re ≤ 0 := by
    have := congrArg norm h
    rw [norm_exp] at this
    have hl : Real.exp ((x - 1) * t).re < 1 := this ▸ hx
    by_contra hc
    push Not at hc
    linarith [Real.one_le_exp hc.le]
  have h1 := norm_exp_sub_one_le_of_re_nonpos hre
  rw [h, norm_mul] at h1
  have hx1 : 0 < ‖x - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (by rintro rfl; simp at hx))
  have : ‖x - 1‖ * ‖t‖ < ‖x - 1‖ := by nlinarith
  linarith


private lemma summable_succ_pow_mul_pow {x : ℂ} (hx : ‖x‖ < 1) (n : ℕ) :
    Summable (fun j : ℕ => ((j : ℂ) + 1) ^ n * x ^ j) := by
  have e : ∀ j : ℕ, ((j : ℂ) + 1) ^ n * x ^ j =
      ∑ m ∈ range (n + 1), (n.choose m : ℂ) * ((j : ℂ) ^ m * x ^ j) := by
    intro j
    rw [add_pow, sum_mul]
    refine sum_congr rfl fun m _ => ?_
    simp only [one_pow, mul_one]; ring
  simp_rw [e]
  exact summable_sum fun m _ => (summable_pow_mul_geometric_of_norm_lt_one m hx).mul_left _

private lemma eulerianNumber_eq_zero_of_lt {n k : ℕ} (hk : n < k) : eulerianNumber n k = 0 := by
  rcases n with _ | n
  · rw [eulerianNumber_zero_left]; simp; omega
  · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact eulerianNumber_succ_eq_zero_of_le (by omega) (by omega)

/-- Carlitz's identity `A_n(x) = (1 - x)^{n+1} ∑_j (j+1)ⁿ xʲ` for the Eulerian polynomial. -/
private lemma eulerianPoly_eq {x : ℂ} (hx : ‖x‖ < 1) (n : ℕ) :
    ∑ k ∈ range (n + 1), (eulerianNumber n k : ℂ) * x ^ k =
      (1 - x) ^ (n + 1) * ∑' j : ℕ, ((j : ℂ) + 1) ^ n * x ^ j := by
  have hx1 : (1 : ℂ) - x ≠ 0 := sub_ne_zero.mpr (by rintro rfl; simp at hx)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [eulerianNumber_zero_left, tsum_geometric_of_norm_lt_one hx, hx1]
  set Pa : PowerSeries ℤ := PowerSeries.mk fun i => (-1) ^ i * ((n + 1).choose i : ℤ)
  set Pb : PowerSeries ℤ := PowerSeries.mk fun j => ((j : ℤ) + 1) ^ n
  have hPa : PowerSeries.HasSumAt Pa x ((1 - x) ^ (n + 1)) := by
    rw [PowerSeries.hasSumAt_int_iff]
    have h : HasSum (fun i : ℕ => (((PowerSeries.coeff i Pa : ℤ) : ℂ)) * x ^ i)
        (∑ i ∈ range (n + 2), (((PowerSeries.coeff i Pa : ℤ) : ℂ)) * x ^ i) :=
      hasSum_sum_of_ne_finset_zero (fun i hi => by
        have : n + 1 < i := by simp at hi; omega
        simp [Pa, Nat.choose_eq_zero_of_lt this])
    convert h using 1
    rw [show (1 : ℂ) - x = -x + 1 by ring, add_pow]
    refine sum_congr rfl fun i _ => ?_
    simp only [Pa, PowerSeries.coeff_mk, one_pow, mul_one]
    rw [neg_pow]
    push_cast
    ring
  have hPb : PowerSeries.HasSumAt Pb x (∑' j : ℕ, ((j : ℂ) + 1) ^ n * x ^ j) := by
    rw [PowerSeries.hasSumAt_int_iff]
    convert (summable_succ_pow_mul_pow hx n).hasSum using 1
    funext j; simp [Pb]
  have hcoeff : ∀ k, PowerSeries.coeff k (Pa * Pb) = (eulerianNumber n k : ℤ) := by
    intro k
    rw [eulerianNumber_eq_sum hn, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine sum_congr rfl fun j hj => ?_
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
    simp only [Pa, Pb, PowerSeries.coeff_mk]
    push_cast [Nat.cast_sub hjk]
    ring
  have h1 := hPa.mul hPb
  have h2 : PowerSeries.HasSumAt (Pa * Pb) x
      (∑ k ∈ range (n + 1), (eulerianNumber n k : ℂ) * x ^ k) := by
    rw [PowerSeries.hasSumAt_int_iff]
    have h : HasSum (fun k : ℕ => (((PowerSeries.coeff k (Pa * Pb) : ℤ) : ℂ)) * x ^ k)
        (∑ k ∈ range (n + 1), (((PowerSeries.coeff k (Pa * Pb) : ℤ) : ℂ)) * x ^ k) :=
      hasSum_sum_of_ne_finset_zero (fun k hk => by
        have : n < k := by simpa using hk
        simp [hcoeff, eulerianNumber_eq_zero_of_lt this])
    convert h using 1
    refine sum_congr rfl fun k _ => ?_
    simp [hcoeff]
  exact h2.unique h1


/-- The Eulerian generating function for small `t`, by expanding `1/(1 - x e^{(1-x)t})`. -/
private lemma hasSum_eulerianPoly_of_small {x t : ℂ} (hx : ‖x‖ < 1)
    (hs : ‖x‖ * Real.exp ‖(1 - x) * t‖ < 1) :
    HasSum (fun n : ℕ => (∑ k ∈ range (n + 1), (eulerianNumber n k : ℂ) * x ^ k) * t ^ n /
      n.factorial) ((1 - x) / (cexp ((x - 1) * t) - x)) := by
  have hx1 : (1 : ℂ) - x ≠ 0 := sub_ne_zero.mpr (by rintro rfl; simp at hx)
  set s : ℂ := (1 - x) * t with hsdef
  set F : ℕ × ℕ → ℂ := fun p => (1 - x) * x ^ p.1 * (((p.1 : ℂ) + 1) * s) ^ p.2 / p.2.factorial
    with hF
  have hnorm : ∀ p : ℕ × ℕ, ‖F p‖ = ‖1 - x‖ * ‖x‖ ^ p.1 *
      (((p.1 : ℝ) + 1) * ‖s‖) ^ p.2 / p.2.factorial := by
    intro p
    simp only [hF, norm_div, norm_mul, norm_pow, Complex.norm_natCast]
    congr 3
    rw [show ((p.1 : ℂ) + 1) = ((p.1 + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    push_cast; ring
  have hrow : ∀ j : ℕ, HasSum (fun n => ‖F (j, n)‖)
      (‖1 - x‖ * ‖x‖ ^ j * Real.exp (((j : ℝ) + 1) * ‖s‖)) := by
    intro j
    simp only [hnorm]
    have := (Real.hasSum_pow_div_factorial (((j : ℝ) + 1) * ‖s‖)).mul_left (‖1 - x‖ * ‖x‖ ^ j)
    simpa [mul_div_assoc] using this
  have hgeo : Summable fun j : ℕ => ‖1 - x‖ * ‖x‖ ^ j * Real.exp (((j : ℝ) + 1) * ‖s‖) := by
    have e : ∀ j : ℕ, ‖1 - x‖ * ‖x‖ ^ j * Real.exp (((j : ℝ) + 1) * ‖s‖) =
        ‖1 - x‖ * Real.exp ‖s‖ * (‖x‖ * Real.exp ‖s‖) ^ j := by
      intro j
      rw [mul_pow, ← Real.exp_nat_mul, add_mul, one_mul, Real.exp_add]; ring
    simp_rw [e]
    exact (summable_geometric_of_lt_one (by positivity) hs).mul_left _
  have hsumF : Summable F := by
    refine Summable.of_norm ?_
    refine (summable_prod_of_nonneg (fun p => norm_nonneg _)).mpr ⟨fun j => (hrow j).summable, ?_⟩
    simpa [(hrow _).tsum_eq] using hgeo
  have hes : ‖x * cexp s‖ < 1 := by
    rw [norm_mul, norm_exp]
    calc ‖x‖ * Real.exp s.re ≤ ‖x‖ * Real.exp ‖s‖ := by
          gcongr; exact re_le_norm s
      _ < 1 := hs
  -- sum over `n` first
  have hfib1 : ∀ j : ℕ, HasSum (fun n => F (j, n)) ((1 - x) * cexp s * (x * cexp s) ^ j) := by
    intro j
    have := (hasSum_pow_div_factorial (((j : ℂ) + 1) * s)).mul_left ((1 - x) * x ^ j)
    convert this using 1
    · funext n; simp only [hF]; ring
    · rw [mul_pow, ← exp_nat_mul, show ((j : ℂ) + 1) * s = s + j * s by ring, exp_add]
      ring
  have hval : HasSum F ((1 - x) * cexp s / (1 - x * cexp s)) := by
    have h1 := hsumF.hasSum.prod_fiberwise hfib1
    have h2 := (hasSum_geometric_of_norm_lt_one hes).mul_left ((1 - x) * cexp s)
    have e : ∑' p, F p = (1 - x) * cexp s * (1 - x * cexp s)⁻¹ := h1.unique h2
    rw [div_eq_mul_inv, ← e]
    exact hsumF.hasSum
  -- sum over `j` first
  have hfib2 : ∀ n : ℕ, HasSum (fun j => F (j, n))
      ((∑ k ∈ range (n + 1), (eulerianNumber n k : ℂ) * x ^ k) * t ^ n / n.factorial) := by
    intro n
    have hS := (summable_succ_pow_mul_pow hx n).hasSum.mul_left ((1 - x) * s ^ n / n.factorial)
    convert hS using 1
    · funext j; simp only [hF, mul_pow]; ring
    · rw [eulerianPoly_eq hx n, hsdef, mul_pow]
      field_simp
      ring
  have hswap : HasSum (fun p : ℕ × ℕ => F p.swap) ((1 - x) * cexp s / (1 - x * cexp s)) :=
    (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hval
  have h3 := hswap.prod_fiberwise (fun n => hfib2 n)
  convert h3 using 1
  have hne : (1 : ℂ) - x * cexp s ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [← h] at hes; simp at hes
  have hne' : cexp ((x - 1) * t) - x ≠ 0 := by
    have : cexp ((x - 1) * t) = (cexp s)⁻¹ := by
      rw [← exp_neg]; congr 1; rw [hsdef]; ring
    rw [this]
    intro h
    apply hne
    have h' : (cexp s)⁻¹ = x := sub_eq_zero.mp h
    rw [← h', inv_mul_cancel₀ (exp_ne_zero s), sub_self]
  rw [div_eq_div_iff hne' hne]
  have : cexp ((x - 1) * t) * cexp s = 1 := by
    rw [← exp_add, hsdef, show (x - 1) * t + (1 - x) * t = 0 by ring, exp_zero]
  linear_combination (x - 1) * this


private lemma sum_range_succ_eulerianNumber (n : ℕ) :
    ∑ k ∈ range (n + 1), eulerianNumber n k = n.factorial := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [eulerianNumber_zero_left]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [sum_range_succ, sum_eulerianNumber hn,
      eulerianNumber_succ_eq_zero_of_le (n := m + 1) (k := m) le_rfl hn, add_zero]

private lemma norm_eulerianPoly_le {x : ℂ} (hx : ‖x‖ < 1) (n : ℕ) :
    ‖∑ k ∈ range (n + 1), (eulerianNumber n k : ℂ) * x ^ k‖ ≤ n.factorial := by
  calc ‖∑ k ∈ range (n + 1), (eulerianNumber n k : ℂ) * x ^ k‖
      ≤ ∑ k ∈ range (n + 1), ‖(eulerianNumber n k : ℂ) * x ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ range (n + 1), (eulerianNumber n k : ℝ) := by
        refine sum_le_sum fun k _ => ?_
        rw [norm_mul, norm_pow, Complex.norm_natCast]
        exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg _) hx.le)
    _ = n.factorial := by exact_mod_cast sum_range_succ_eulerianNumber n

private lemma norm_eulerianTerm_le {x t : ℂ} (hx : ‖x‖ < 1) (n : ℕ) :
    ‖(∑ k ∈ range (n + 1), (eulerianNumber n k : ℂ) * x ^ k) * t ^ n / n.factorial‖ ≤
      ‖t‖ ^ n := by
  rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast]
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_iff₀ hf]
  have := norm_eulerianPoly_le hx n
  nlinarith [pow_nonneg (norm_nonneg t) n]

/-- (26.14.4): `∑_{n,k} ⟨n k⟩ x^k tⁿ/n! = (1 - x)/(exp((x - 1)t) - x)` for `|x| < 1`, `|t| < 1`. -/
@[dlmf 26.14.E4]
theorem hasSum_eulerianNumber {x t : ℂ} (hx : ‖x‖ < 1) (ht : ‖t‖ < 1) :
    HasSum (fun nk : ℕ × ℕ => (eulerianNumber nk.1 nk.2 : ℂ) * x ^ nk.2 * t ^ nk.1 / nk.1.factorial)
      ((1 - x) / (Complex.exp ((x - 1) * t) - x)) := by
  set P : ℕ → ℂ := fun n => ∑ k ∈ range (n + 1), (eulerianNumber n k : ℂ) * x ^ k with hP
  set L : ℂ → ℂ := fun w => ∑' n : ℕ, P n * w ^ n / n.factorial with hL
  set R : ℂ → ℂ := fun w => (1 - x) / (cexp ((x - 1) * w) - x) with hR
  have hLsum : ∀ w : ℂ, ‖w‖ < 1 → HasSum (fun n : ℕ => P n * w ^ n / n.factorial) (L w) := by
    intro w hw
    refine (Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg w) hw)
      fun n => norm_eulerianTerm_le hx n).hasSum
  have hLdiff : DifferentiableOn ℂ L (Metric.ball 0 1) := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    set r : ℝ := (‖w‖ + 1) / 2 with hr
    have hr1 : r < 1 := by rw [hr]; linarith
    have hwr : ‖w‖ < r := by rw [hr]; linarith
    have hr0 : 0 ≤ r := by rw [hr]; positivity
    have hd : DifferentiableOn ℂ L (Metric.ball 0 r) := by
      refine differentiableOn_tsum_of_summable_norm (u := fun n : ℕ => r ^ n)
        (summable_geometric_of_lt_one hr0 hr1) (fun n => by fun_prop) Metric.isOpen_ball ?_
      intro n v hv
      rw [Metric.mem_ball, dist_zero_right] at hv
      refine (norm_eulerianTerm_le hx n).trans ?_
      exact pow_le_pow_left₀ (norm_nonneg v) hv.le n
    exact (hd.differentiableAt (Metric.isOpen_ball.mem_nhds (by simpa using hwr)))
      |>.differentiableWithinAt
  have hRdiff : DifferentiableOn ℂ R (Metric.ball 0 1) := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (differentiableAt_const _).div (by fun_prop) ?_
    exact sub_ne_zero.mpr (exp_mul_ne hx hw)
  have hnear : ∀ᶠ w in 𝓝 (0 : ℂ), L w = R w := by
    have hc : ContinuousAt (fun w : ℂ => ‖x‖ * Real.exp ‖(1 - x) * w‖) 0 := by fun_prop
    have h1 := hc.eventually_lt continuousAt_const (by simpa using hx)
    have h2 : ∀ᶠ w in 𝓝 (0 : ℂ), ‖w‖ < 1 :=
      (continuous_norm.tendsto 0).eventually (gt_mem_nhds (by simp))
    filter_upwards [h1, h2] with w hw1 hw2
    exact (hLsum w hw2).unique (hasSum_eulerianPoly_of_small hx hw1)
  have heq := hLdiff.analyticOnNhd Metric.isOpen_ball |>.eqOn_of_preconnected_of_eventuallyEq
    (hRdiff.analyticOnNhd Metric.isOpen_ball) (convex_ball 0 1).isPreconnected
    (Metric.mem_ball_self one_pos) hnear
  have hLR : L t = R t := heq (by simpa using ht)
  set G : ℕ × ℕ → ℂ := fun nk => (eulerianNumber nk.1 nk.2 : ℂ) * x ^ nk.2 * t ^ nk.1 /
    nk.1.factorial with hG
  have hfib : ∀ n : ℕ, HasSum (fun k => G (n, k)) (P n * t ^ n / n.factorial) := by
    intro n
    have h : HasSum (fun k : ℕ => G (n, k)) (∑ k ∈ range (n + 1), G (n, k)) :=
      hasSum_sum_of_ne_finset_zero (fun k hk => by
        have : n < k := by simpa using hk
        simp [hG, eulerianNumber_eq_zero_of_lt this])
    convert h using 1
    simp only [hP, hG, sum_mul, sum_div]
  have hnfib : ∀ n : ℕ, HasSum (fun k => ‖G (n, k)‖) (∑ k ∈ range (n + 1), ‖G (n, k)‖) :=
    fun n => hasSum_sum_of_ne_finset_zero (fun k hk => by
      have : n < k := by simpa using hk
      simp [hG, eulerianNumber_eq_zero_of_lt this])
  have hbound : ∀ n : ℕ, ∑ k ∈ range (n + 1), ‖G (n, k)‖ ≤ ‖t‖ ^ n := by
    intro n
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    calc ∑ k ∈ range (n + 1), ‖G (n, k)‖
        ≤ ∑ k ∈ range (n + 1), (eulerianNumber n k : ℝ) * ‖t‖ ^ n / n.factorial := by
          refine sum_le_sum fun k _ => ?_
          simp only [hG, norm_div, norm_mul, norm_pow, Complex.norm_natCast]
          gcongr
          exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg _) hx.le)
      _ = ‖t‖ ^ n := by
          rw [← sum_div, ← sum_mul]
          have : ∑ k ∈ range (n + 1), (eulerianNumber n k : ℝ) = n.factorial := by
            exact_mod_cast sum_range_succ_eulerianNumber n
          rw [this]; field_simp
  have hsumG : Summable G := by
    refine Summable.of_norm ((summable_prod_of_nonneg (fun p => norm_nonneg _)).mpr
      ⟨fun n => (hnfib n).summable, ?_⟩)
    refine Summable.of_nonneg_of_le (fun n => tsum_nonneg fun k => norm_nonneg _)
      (fun n => ?_) (summable_geometric_of_lt_one (norm_nonneg t) ht)
    rw [(hnfib n).tsum_eq]
    exact hbound n
  have h := hsumG.hasSum.prod_fiberwise hfib
  have e : ∑' p, G p = R t := by rw [← hLR]; exact h.unique (hLsum t ht)
  rw [show (1 - x) / (cexp ((x - 1) * t) - x) = R t from rfl, ← e]
  exact hsumG.hasSum

end GeneratingFunction

end DLMF.Combinatorics
end
end
