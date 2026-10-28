/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.Permutations.CyclesAndExcedances

/-!
# Eulerian numbers and permutation order statistics

Boundary values, recurrences and identities for Eulerian numbers and related permutation
statistics.

Source references and common attribution are retained in
`DLMF.Combinatorics.Permutations`.
-/

@[expose] public section

noncomputable section

open Finset Equiv

open Polynomial hiding bernoulli

namespace DLMF.Combinatorics

/-- `⟨0 k⟩ = δ_{0k}` (restated before its tagged form (26.14.13) below). -/
lemma r26b_eulerianNumber_zero_left (k : ℕ) : eulerianNumber 0 k = if k = 0 then 1 else 0 := by
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
lemma r26b_desc_key (n : ℕ) (x : ℂ) (k : ℕ) :
    (n + 1 : ℂ) * x * (descPochhammer ℂ n).eval (x + k) =
      (k + 1) * (descPochhammer ℂ (n + 1)).eval (x + k) +
        (n - k) * (descPochhammer ℂ (n + 1)).eval (x + k + 1) := by
  rw [descPochhammer_succ_eval, descPochhammer_succ_left, eval_mul, eval_X, eval_comp,
    eval_sub, eval_X, eval_one, add_sub_cancel_right]
  ring

/-- Worpitzky (26.14.5) multiplied by `n!`, summed to `n`, for all `n`. -/
lemma r26b_worpitzky_aux (n : ℕ) (x : ℂ) :
    ∑ k ∈ range (n + 1), (eulerianNumber n k : ℂ) * (descPochhammer ℂ n).eval (x + k) =
      n.factorial * x ^ n := by
  induction n with
  | zero => simp [r26b_eulerianNumber_zero_left]
  | succ n ih =>
    have hz : eulerianNumber n (n + 1) = 0 := by
      rcases n with _ | m
      · simp [r26b_eulerianNumber_zero_left]
      · exact r26b_eulerianNumber_eq_zero (by omega) (by omega)
    have hsplit : ∀ k, (eulerianNumber (n + 1) k : ℂ) * (descPochhammer ℂ (n + 1)).eval (x + k) =
        ((k : ℂ) + 1) * (eulerianNumber n k : ℂ) * (descPochhammer ℂ (n + 1)).eval (x + k) +
        (if 1 ≤ k then ((n + 1 - k : ℕ) : ℂ) * (eulerianNumber n (k - 1) : ℂ) else 0) *
          (descPochhammer ℂ (n + 1)).eval (x + k) := by
      intro k; rw [r26b_eulerian_rec]; push_cast; split_ifs <;> ring
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
    have := r26b_desc_key n x k
    rw [show n + 1 - (k + 1) = n - k by omega, Nat.cast_sub hk']
    push_cast
    simp only [add_assoc] at this ⊢
    linear_combination (-(eulerianNumber n k : ℂ)) * this

/-- Worpitzky at natural arguments: `mⁿ = ∑ₖ ⟨n k⟩ C(m+k, n)`. -/
lemma r26b_worpitzky_nat (n m : ℕ) :
    m ^ n = ∑ k ∈ range (n + 1), eulerianNumber n k * (m + k).choose n := by
  have h := r26b_worpitzky_aux n (m : ℂ)
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
lemma r26b_binom_basis_unique (n : ℕ) (a b : ℕ → ℕ)
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
lemma r26b_factorial_mul_stirlingSecond (n j : ℕ) (hj : j ≤ n) :
    j.factorial * Nat.stirlingSecond n j =
      ∑ k ∈ range (n + 1), eulerianNumber n k * k.choose (n - j) := by
  refine r26b_binom_basis_unique n (fun j => j.factorial * Nat.stirlingSecond n j)
    (fun j => ∑ k ∈ range (n + 1), eulerianNumber n k * k.choose (n - j)) (fun m => ?_) j hj
  have h1 := Nat.pow_eq_sum_stirlingSecond_mul_descFactorial m n
  simp only [Nat.descFactorial_eq_factorial_mul_choose] at h1
  calc ∑ j ∈ range (n + 1), m.choose j * (j.factorial * Nat.stirlingSecond n j) = m ^ n := by
        rw [h1]; exact sum_congr rfl fun j _ => by ring
    _ = ∑ k ∈ range (n + 1), eulerianNumber n k * (m + k).choose n := r26b_worpitzky_nat n m
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
lemma r26b_alt_choose_orth (k l N : ℕ) (hl : l ≤ k + N) :
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
def r26b_eulA (n k : ℕ) : ℤ :=
  ∑ j ∈ range (k + 1), (-1 : ℤ) ^ j * (n + 1).choose j * (k + 1 - j) ^ n

/-- The right side of (26.14.6) at `n = 0`. -/
lemma r26b_eulA_zero (K : ℕ) : r26b_eulA 0 K = if K = 0 then 1 else 0 := by
  unfold r26b_eulA
  split_ifs with hK
  · subst hK; simp
  · obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
    simp only [pow_zero, mul_one, zero_add]
    rw [← Finset.sum_range_add_sum_Ico _ (show 2 ≤ k + 1 + 1 by omega)]
    rw [Finset.sum_eq_zero (s := Ico 2 (k + 1 + 1)) fun j hj => by
      rw [Nat.choose_eq_zero_of_lt (by simp at hj; omega)]; simp]
    simp [sum_range_succ]

/-- The right side of (26.14.6) satisfies the Eulerian recurrence. -/
lemma r26b_eulA_succ (n k : ℕ) :
    r26b_eulA (n + 1) (k + 1) =
      (k + 2) * r26b_eulA n (k + 1) + ((n : ℤ) + 1 - (k + 1)) * r26b_eulA n k := by
  unfold r26b_eulA
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
    rw [r26b_eulerian_rec, r26b_excedance_succ, ih, ih]

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
  · rw [r26b_eulerianNumber_symm hk, eulerianNumber_eq_card_excedance]
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
    rw [r26b_eulerianNumber_eq_zero (by omega) hn, eq_comm, card_eq_zero, filter_eq_empty_iff]
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
        simp only [Perm.decomposeFin'_symm, r26b_inversionNumber_decomposeFin', pow_add,
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
        rw [← (r26b_insMin (n := n)).sum_comp, Fintype.sum_prod_type_right]
        simp only [r26b_majorIndex_insMin, pow_add, ← Finset.mul_sum]
        rw [Finset.sum_mul]
        refine sum_congr rfl fun σ _ => ?_
        congr 1
        rw [Fin.sum_univ_eq_sum_range
          (fun p => q ^ r26b_majInc (wordDescentSet fun i => (σ i : ℕ)) p),
          r26b_sum_pow_majInc q (by simpa using r26b_wordDescentSet_subset (fun i => (σ i : ℕ))),
          eq_div_iff hq', mul_comm, mul_neg_geom_sum]
        ring

/-- (26.14.4): `∑_{n,k} ⟨n k⟩ x^k tⁿ/n! = (1 - x)/(exp((x - 1)t) - x)` for `|x| < 1`, `|t| < 1`. -/
@[dlmf 26.14.E4]
theorem hasSum_eulerianNumber {x t : ℂ} (hx : ‖x‖ < 1) (ht : ‖t‖ < 1) :
    HasSum (fun nk : ℕ × ℕ => (eulerianNumber nk.1 nk.2 : ℂ) * x ^ nk.2 * t ^ nk.1 / nk.1.factorial)
      ((1 - x) / (Complex.exp ((x - 1) * t) - x)) := by
  sorry

/-- (26.14.5), Worpitzky's identity: `∑_{k=0}^{n-1} ⟨n k⟩ C(x + k, n) = xⁿ` for `n ≥ 1` and
every `x ∈ ℂ`, with `C(y, n) = y(y-1)⋯(y-n+1)/n!`. -/
@[dlmf 26.14.E5]
theorem worpitzky {n : ℕ} (hn : 1 ≤ n) (x : ℂ) :
    ∑ k ∈ range n, (eulerianNumber n k : ℂ) * ((descPochhammer ℂ n).eval (x + k) / n.factorial) =
      x ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := r26b_worpitzky_aux (m + 1) x
  rw [sum_range_succ, r26b_eulerianNumber_eq_zero (n := m + 1) (k := m) le_rfl hn] at h
  simp only [Nat.cast_zero, zero_mul, add_zero] at h
  have hf : ((m + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  simp_rw [mul_div_assoc']
  rw [← sum_div, h]
  field_simp

/-- (26.14.6) for every `n`, including `n = 0` (stronger than DLMF). -/
lemma r26b_eulerianNumber_eq_eulA (n k : ℕ) : (eulerianNumber n k : ℤ) = r26b_eulA n k := by
  induction n generalizing k with
  | zero => rw [r26b_eulerianNumber_zero_left, r26b_eulA_zero]; split_ifs <;> simp
  | succ n ih =>
    rw [r26b_eulerian_rec]
    rcases k with _ | k
    · simp [ih, r26b_eulA]
    rw [r26b_eulA_succ, ← ih, ← ih]
    simp only [show 1 ≤ k + 1 from by omega, ite_true, Nat.add_sub_cancel]
    by_cases hkn : k ≤ n
    · push_cast [Nat.cast_sub hkn]; ring
    · have hz : eulerianNumber n k = 0 := by
        rcases n with _ | m
        · rw [r26b_eulerianNumber_zero_left]; simp; omega
        · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
          exact r26b_eulerianNumber_eq_zero (by omega) (by omega)
      have hz' : eulerianNumber n (k + 1) = 0 := by
        rcases n with _ | m
        · rw [r26b_eulerianNumber_zero_left]; simp
        · exact r26b_eulerianNumber_eq_zero (by omega) (by omega)
      simp [hz, hz']

/-- (26.14.6): `⟨n k⟩ = ∑_{j=0}^k (-1)^j C(n+1, j) (k+1-j)ⁿ` for `n ≥ 1`. -/
@[dlmf 26.14.E6]
theorem eulerianNumber_eq_sum {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    (eulerianNumber n k : ℤ) =
      ∑ j ∈ range (k + 1), (-1 : ℤ) ^ j * (n + 1).choose j * (k + 1 - j) ^ n := by
  exact (fun _ => r26b_eulerianNumber_eq_eulA n k) hn

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
      have h := r26b_factorial_mul_stirlingSecond n (n - k + 1 - 1 - t) (by omega)
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
      rw [r26b_alt_choose_orth k l (n - k) (by have := mem_range.mp hl; omega)]]
    simp only [mul_ite, mul_one, mul_zero]
    rw [sum_ite_eq' (range (n + 1)) k, ite_eq_left (mem_range.mpr (by omega))]
  · have hz : eulerianNumber n k = 0 := by
      rcases n with _ | m
      · rw [r26b_eulerianNumber_zero_left, ite_eq_right (by omega)]
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        exact r26b_eulerianNumber_eq_zero (by omega) (by omega)
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
  rw [r26b_eulerian_succ]
  simp only [show m + 2 - 1 = m + 1 by omega, Nat.add_sub_cancel]
  by_cases hj : j ≤ m + 1
  · push_cast [hj]
    ring
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [r26b_eulerianNumber_eq_zero (by omega) (by omega),
      r26b_eulerianNumber_eq_zero (n := m + 1) (k := i) (by omega) (by omega)]
    simp

/-- (26.14.9): `⟨n k⟩ = ⟨n, n-1-k⟩` for `n ≥ 1` and `k ≤ n - 1` (for `k ≥ n` both sides are
`0` in DLMF's convention). -/
@[dlmf 26.14.E9]
theorem eulerianNumber_symm {n k : ℕ} (hk : k < n) :
    eulerianNumber n k = eulerianNumber n (n - 1 - k) :=
  r26b_eulerianNumber_symm hk

/-- A permutation of `Fin n` has at most `n - 1` descents. -/
lemma c26b_descentNumber_lt {n : ℕ} (hn : 1 ≤ n) (σ : Perm (Fin n)) : descentNumber σ < n := by
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
      exact ⟨_, c26b_descentNumber_lt hn σ, rfl⟩
    rw [this, card_univ, Fintype.card_perm, Fintype.card_fin]
  · intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro σ h1 h2
    simp only [mem_filter] at h1 h2
    exact hij (h1.2.symm.trans h2.2)

/-- The alternating sum of Eulerian numbers in the form of (24.6.11). -/
lemma r26b_alt_sum_eulerian (n : ℕ) (hn : 1 ≤ n) :
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
  rw [Nat.add_sub_cancel, r26b_alt_sum_eulerian n (by omega),
    DLMF.BernoulliEuler.bernoulli_eq_explicit₁₁ (by omega), Nat.add_sub_cancel]

/-- (26.14.12): `S(n, m) = (1/m!) ∑_{k=0}^{n-1} ⟨n k⟩ C(k, n-m)` for `n ≥ m`, `n ≥ 1`. -/
@[dlmf 26.14.E12]
theorem stirlingSecond_eq_sum_eulerianNumber {n m : ℕ} (hmn : m ≤ n) (hn : 1 ≤ n) :
    (Nat.stirlingSecond n m : ℚ) =
      1 / m.factorial * ∑ k ∈ range n, (eulerianNumber n k : ℚ) * k.choose (n - m) := by
  have h := r26b_factorial_mul_stirlingSecond n m hmn
  rw [sum_range_succ] at h
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [r26b_eulerianNumber_eq_zero (n := n' + 1) (k := n') le_rfl hn, zero_mul, add_zero] at h
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
  exact ⟨1, by ext σ; simp [q26b_descentNumber_eq_zero_iff]⟩

/-- (26.14.15): `⟨n 1⟩ = 2ⁿ - n - 1` for `n ≥ 1`. -/
@[dlmf 26.14.E15]
theorem eulerianNumber_one_right {n : ℕ} (hn : 1 ≤ n) :
    (eulerianNumber n 1 : ℤ) = 2 ^ n - n - 1 := by
  induction n, hn using Nat.le_induction with
  | base => rw [r26b_eulerianNumber_eq_zero (n := 1) (k := 0) (by omega) le_rfl]; simp
  | succ m hm ih =>
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [r26b_eulerian_succ, eulerianNumber_zero_right]
    push_cast
    rw [ih]
    push_cast
    ring

/-- (26.14.16): `⟨n 2⟩ = 3ⁿ - (n+1) 2ⁿ + C(n+1, 2)` for `n ≥ 1`. -/
@[dlmf 26.14.E16]
theorem eulerianNumber_two_right {n : ℕ} (hn : 1 ≤ n) :
    (eulerianNumber n 2 : ℤ) = 3 ^ n - (n + 1) * 2 ^ n + (n + 1).choose 2 := by
  induction n, hn using Nat.le_induction with
  | base => rw [r26b_eulerianNumber_eq_zero (n := 1) (k := 1) (by omega) le_rfl]; simp
  | succ m hm ih =>
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [r26b_eulerian_succ]
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

end DLMF.Combinatorics
end
end
