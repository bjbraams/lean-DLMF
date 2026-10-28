/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.Stirling.DefinitionsAndSeries

/-!
# Recurrences and identities for Stirling numbers

Recurrences, surjection counts and algebraic identities for the two kinds of Stirling numbers.

Source references and common attribution are retained in
`DLMF.Combinatorics.Stirling`.
-/

@[expose] public section

open Finset Polynomial Filter Topology Asymptotics

noncomputable section

namespace DLMF.Combinatorics

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

/-- Identity under the stated parameter and domain assumptions: `c26a_matS2 n * c26a_matS1 n = 1`. -/
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

end DLMF.Combinatorics
end
end
