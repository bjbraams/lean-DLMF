/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.Polynomial.RuleOfSigns
public import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Polynomial.Div

/-!
# The parity part of Descartes' rule of signs

The sign changes of a coefficient list relate the signs of its nonzero endpoint
coefficients. Multiplication by a positive linear root reverses that parity; a factor
`X` preserves it. A real polynomial without positive roots has matching leading and
constant signs, by the intermediate value theorem. Degree induction then identifies
the parity with the number of positive roots, counted with multiplicity.

This complements Mathlib's `Polynomial.roots_countP_pos_le_signVariations`. The proof
reuses its coefficient-list and `eraseLead` APIs, polynomial root factorization, and
real polynomial growth at infinity.

## Main results

* `Polynomial.neg_one_pow_signVariations_eq_neg_one_pow_countP_pos`: equality of parities.
* `Polynomial.even_signVariations_sub_countP_pos`: the difference is even.
-/

public section

namespace Polynomial

/-- The parity of coefficient sign changes relates the signs of the leading and constant
coefficients when the latter is nonzero. -/
lemma sign_coeff_zero_eq_neg_one_pow_signVariations_mul_sign_leadingCoeff
    {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {p : R[X]} (hp : p.coeff 0 ≠ 0) :
    SignType.sign (p.coeff 0) = (-1 : SignType) ^ p.signVariations *
      SignType.sign p.leadingCoeff := by
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  induction hdeg : p.natDegree using Nat.strong_induction_on generalizing p with
  | ind n ih =>
    by_cases hn : n = 0
    · have he : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero (hdeg.trans hn)
      rw [he]
      simp [signVariations, coeffList_C hp]
    · have hq0 : p.eraseLead.coeff 0 = p.coeff 0 :=
        eraseLead_coeff_of_ne 0 (by omega)
      have hq : p.eraseLead ≠ 0 := by intro h; rw [h] at hq0; simp_all
      have hl : p.eraseLead.natDegree < n := by
        rw [← hdeg]
        exact (eraseLead_natDegree_lt_or_eraseLead_eq_zero p).resolve_right hq
      have h := ih p.eraseLead.natDegree hl (p := p.eraseLead)
        (by rwa [hq0]) hq rfl
      rw [hq0] at h
      rw [signVariations_eq_eraseLead_add_ite hp0, pow_add]
      have hsign : SignType.sign p.leadingCoeff ≠ 0 := by simp [hp0]
      have hsignq : SignType.sign p.eraseLead.leadingCoeff ≠ 0 := by simp [hq]
      generalize hs : SignType.sign p.leadingCoeff = s at *
      generalize ht : SignType.sign p.eraseLead.leadingCoeff = t at *
      cases s <;> cases t <;> simp_all

/-- Multiplication by `X` appends a zero to the coefficient list of a nonzero polynomial. -/
lemma coeffList_X_mul {R : Type*} [Semiring R] [Nontrivial R] [NoZeroDivisors R]
    {p : R[X]} (hp : p ≠ 0) :
    (X * p).coeffList = p.coeffList ++ [0] := by
  rw [coeffList_of_ne_zero (mul_ne_zero X_ne_zero hp), coeffList_of_ne_zero hp,
    natDegree_X_mul hp]
  rw [List.range_succ_eq_map]
  simp [List.reverse_cons, List.map_append, List.map_map, coeff_X_mul]

/-- A factor `X` does not change the coefficient sign variations. -/
lemma signVariations_X_mul {R : Type*} [Semiring R] [Nontrivial R] [NoZeroDivisors R]
    [LinearOrder R] (p : R[X]) : (X * p).signVariations = p.signVariations := by
  by_cases hp : p = 0
  · simp [hp]
  · rw [signVariations, signVariations, coeffList_X_mul hp]
    simp [List.signVariations]

/-- A real polynomial with nonzero constant coefficient and no positive root has leading and
constant coefficients of the same sign. -/
lemma sign_coeff_zero_eq_sign_leadingCoeff_of_no_pos_root {p : ℝ[X]}
    (hp : p.coeff 0 ≠ 0) (hroot : ∀ x : ℝ, 0 < x → p.eval x ≠ 0) :
    SignType.sign (p.coeff 0) = SignType.sign p.leadingCoeff := by
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  wlog hl : 0 < p.leadingCoeff generalizing p
  · have hneg : 0 < (-p).leadingCoeff := by
      rw [leadingCoeff_neg]
      have h := leadingCoeff_ne_zero.mpr hp0
      exact neg_pos.mpr (lt_of_le_of_ne (not_lt.mp hl) h)
    have h := this (p := -p) (by simpa) (by simpa using hroot) (by simpa) hneg
    simpa only [coeff_neg, leadingCoeff_neg, Left.sign_neg, neg_inj] using h
  have hconst : 0 < p.coeff 0 := by
    by_contra h
    have hneg : p.coeff 0 < 0 := lt_of_le_of_ne (not_lt.mp h) hp
    by_cases hd : p.natDegree = 0
    · have he := eq_C_of_natDegree_eq_zero hd
      have := congrArg leadingCoeff he
      simp only [leadingCoeff_C] at this
      linarith
    · have ht := p.tendsto_atTop_of_leadingCoeff_nonneg
        (natDegree_pos_iff_degree_pos.mp (by omega)) hl.le
      obtain ⟨b, hb, hpB⟩ : ∃ b : ℝ, 0 < b ∧ 0 < p.eval b :=
        ((Filter.eventually_gt_atTop 0).and (ht.eventually_gt_atTop 0)).exists
      obtain ⟨r, hr, he⟩ := intermediate_value_Icc hb.le p.continuous.continuousOn
        (show (0 : ℝ) ∈ Set.Icc (p.eval 0) (p.eval b) by
          simpa only [← coeff_zero_eq_eval_zero] using ⟨hneg.le, hpB.le⟩)
      have hrpos : 0 < r := lt_of_le_of_ne hr.1 (by
        intro heq; subst r; exact hp (by simpa only [← coeff_zero_eq_eval_zero] using he))
      exact hroot r hrpos he
  simp [hconst, hl]

/-- A positive linear root reverses the parity of coefficient sign variations. -/
lemma neg_one_pow_signVariations_X_sub_C_mul {R : Type*} [Ring R] [LinearOrder R]
    [IsStrictOrderedRing R] {p : R[X]} (hp : p.coeff 0 ≠ 0)
    {a : R} (ha : 0 < a) :
    (-1 : SignType) ^ ((X - C a) * p).signVariations =
      -((-1 : SignType) ^ p.signVariations) := by
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  have hpc : ((X - C a) * p).coeff 0 ≠ 0 := by simp [ha.ne', hp]
  have h := sign_coeff_zero_eq_neg_one_pow_signVariations_mul_sign_leadingCoeff hpc
  have hq := sign_coeff_zero_eq_neg_one_pow_signVariations_mul_sign_leadingCoeff hp
  simp only [mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub,
    sign_mul, Left.sign_neg, sign_pos ha,
    leadingCoeff_monic_mul (monic_X_sub_C a)] at h
  rw [hq, neg_mul] at h
  apply mul_right_cancel₀ (by simp [hp0] : SignType.sign p.leadingCoeff ≠ 0)
  simpa only [one_mul, neg_mul] using h.symm

/-- For a nonzero real polynomial, the coefficient sign variations and the number of positive
roots, counted with multiplicity, have the same parity. -/
lemma neg_one_pow_signVariations_eq_neg_one_pow_countP_pos {p : ℝ[X]} (hp : p ≠ 0) :
    (-1 : SignType) ^ p.signVariations = (-1 : SignType) ^ p.roots.countP (0 < ·) := by
  induction hdeg : p.natDegree using Nat.strong_induction_on generalizing p with
  | ind n ih =>
    by_cases hc : p.coeff 0 = 0
    · obtain ⟨q, rfl⟩ := X_dvd_iff.mpr hc
      have hq : q ≠ 0 := right_ne_zero_of_mul hp
      have hsmall : q.natDegree < n := by
        rw [natDegree_mul X_ne_zero hq, natDegree_X] at hdeg
        omega
      rw [signVariations_X_mul, roots_mul hp, roots_X, Multiset.countP_add]
      simpa [Multiset.countP_eq_card_filter, Multiset.filter_singleton] using
        ih q.natDegree hsmall hq rfl
    · by_cases hroot : ∀ x : ℝ, 0 < x → p.eval x ≠ 0
      · have hsign := sign_coeff_zero_eq_sign_leadingCoeff_of_no_pos_root hc hroot
        have h := sign_coeff_zero_eq_neg_one_pow_signVariations_mul_sign_leadingCoeff hc
        rw [hsign] at h
        have hpow : (-1 : SignType) ^ p.signVariations = 1 := by
          apply mul_right_cancel₀ (by simp [hp] : SignType.sign p.leadingCoeff ≠ 0)
          simpa only [one_mul] using h.symm
        have hcount : p.roots.countP (0 < ·) = 0 := by
          rw [Multiset.countP_eq_zero]
          intro a ha
          exact fun hpos => hroot a hpos (isRoot_of_mem_roots ha)
        rw [hpow, hcount, pow_zero]
      · push Not at hroot
        obtain ⟨a, ha, hpa⟩ := hroot
        obtain ⟨q, rfl⟩ := dvd_iff_isRoot.mpr hpa
        have hq : q ≠ 0 := right_ne_zero_of_mul hp
        have hqc : q.coeff 0 ≠ 0 := by
          intro h; simp [h] at hc
        have hsmall : q.natDegree < n := by
          rw [natDegree_mul (X_sub_C_ne_zero a) hq, natDegree_X_sub_C] at hdeg
          omega
        rw [neg_one_pow_signVariations_X_sub_C_mul hqc ha,
          ih q.natDegree hsmall hq rfl, roots_mul hp, roots_X_sub_C, Multiset.countP_add]
        simp [Multiset.countP_eq_card_filter, Multiset.filter_singleton, ha, pow_add]

/-- The difference between coefficient sign variations and the number of positive roots is
even: the parity part of Descartes’ rule of signs. -/
lemma even_signVariations_sub_countP_pos {p : ℝ[X]} (hp : p ≠ 0) :
    Even (p.signVariations - p.roots.countP (0 < ·)) := by
  rw [Nat.even_sub p.roots_countP_pos_le_signVariations]
  have h := neg_one_pow_signVariations_eq_neg_one_pow_countP_pos hp
  simpa only [neg_one_pow_eq_one_iff_even (by decide : (-1 : SignType) ≠ 1)] using
    (Iff.of_eq (congrArg (· = (1 : SignType)) h))

end Polynomial
