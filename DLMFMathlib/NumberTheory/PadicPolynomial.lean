/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Algebra.Polynomial.Binomial
public import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Tactic

/-!
# p-adic bounds for polynomial functionals

A linear functional bounded by one on the binomial polynomial basis respects every
uniform p-adic bound on natural arguments. An averaging identity against integer values
supplies the bound on the binomial polynomials whenever its averaging length is prime to `p`.

* `LinearMap.padicNorm_apply_choose_X_comp_natCast`: integrality from averaging.
* `LinearMap.padicNorm_apply_le_of_choose_X`: preservation of a uniform bound.

The proof uses Mathlib's `Ring.choose` recurrence and the finite binomial polynomial basis,
together with the nonarchimedean p-adic norm inequality.
-/

public noncomputable section

open Finset Polynomial

namespace LinearMap

/-- A functional satisfying the integer averaging identity is bounded by one on all
nonnegative integer translates of binomial polynomials, if `p` does not divide the
averaging length. -/
lemma padicNorm_apply_choose_X_comp_natCast {p a : ℕ} [Fact p.Prime] (ha : ¬ p ∣ a)
    (L : ℚ[X] →ₗ[ℚ] ℚ)
    (hL : ∀ P : ℚ[X], (∑ j ∈ Finset.range a, L (P.comp (X + C (j : ℚ)))) =
      ∑ j ∈ Finset.range a, ∑ i ∈ Finset.range j, P.eval (i : ℚ)) :
    ∀ k j : ℕ, padicNorm p (L ((Ring.choose (X : ℚ[X]) k).comp (X + C (j : ℚ)))) ≤ 1 := by
  have hscale (k : ℕ) (hshift : ∀ j : ℕ,
      padicNorm p (L ((Ring.choose (X : ℚ[X]) k).comp (X + C (j : ℚ))) -
        L (Ring.choose (X : ℚ[X]) k)) ≤ 1) :
      padicNorm p (L (Ring.choose (X : ℚ[X]) k)) ≤ 1 := by
    have he := hL (Ring.choose (X : ℚ[X]) k)
    have hr : padicNorm p (∑ j ∈ Finset.range a, ∑ i ∈ Finset.range j,
        (Ring.choose (X : ℚ[X]) k).eval (i : ℚ)) ≤ 1 := by
      apply padicNorm.sum_le' _ (by norm_num)
      intro j _
      apply padicNorm.sum_le' _ (by norm_num)
      intro i _
      rw [Polynomial.eval_choose_X_natCast]
      exact padicNorm.of_nat _
    have hd : padicNorm p (∑ j ∈ Finset.range a,
        (L ((Ring.choose (X : ℚ[X]) k).comp (X + C (j : ℚ))) -
          L (Ring.choose (X : ℚ[X]) k))) ≤ 1 :=
      padicNorm.sum_le' (fun j _ => hshift j) (by norm_num)
    have heq : (a : ℚ) * L (Ring.choose (X : ℚ[X]) k) =
        (∑ j ∈ Finset.range a, ∑ i ∈ Finset.range j, (Ring.choose (X : ℚ[X]) k).eval (i : ℚ)) -
          (∑ j ∈ Finset.range a,
            (L ((Ring.choose (X : ℚ[X]) k).comp (X + C (j : ℚ))) -
              L (Ring.choose (X : ℚ[X]) k))) := by
      rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, he]
      ring
    have hb : padicNorm p ((a : ℚ) * L (Ring.choose (X : ℚ[X]) k)) ≤ 1 := by
      rw [heq, sub_eq_add_neg]
      exact padicNorm.nonarchimedean.trans (max_le hr (by simpa only [padicNorm.neg] using hd))
    rwa [padicNorm.mul, (padicNorm.nat_eq_one_iff a).mpr ha, one_mul] at hb
  intro k
  induction k with
  | zero =>
    have hbase : padicNorm p (L (Ring.choose (X : ℚ[X]) 0)) ≤ 1 := hscale 0 (by
      intro j
      simp only [Ring.choose_zero_right, Polynomial.one_comp, sub_self, padicNorm.zero]
      norm_num)
    intro j
    simpa only [Ring.choose_zero_right, Polynomial.one_comp] using hbase
  | succ k ih =>
    have hdiff (j : ℕ) : L ((Ring.choose (X : ℚ[X]) (k + 1)).comp (X + C (j : ℚ))) -
        L (Ring.choose (X : ℚ[X]) (k + 1)) =
          ∑ i ∈ Finset.range j, L ((Ring.choose (X : ℚ[X]) k).comp (X + C (i : ℚ))) := by
      induction j with
      | zero => simp
      | succ j hj =>
        rw [sum_range_succ, ← hj]
        have hc := congrArg (fun P : ℚ[X] => L (P.comp (X + C (j : ℚ))))
          (Polynomial.comp_choose_X_add_one_sub k)
        simp only [Polynomial.sub_comp, map_sub, Polynomial.comp_assoc,
          Polynomial.add_comp, Polynomial.X_comp, Polynomial.one_comp] at hc
        have he : (X + C (j : ℚ) + 1 : ℚ[X]) = X + C ((j + 1 : ℕ) : ℚ) := by
          push_cast
          simp only [map_add, map_one]
          ring
        rw [he] at hc
        linear_combination hc
    have hshift (j : ℕ) : padicNorm p
        (L ((Ring.choose (X : ℚ[X]) (k + 1)).comp (X + C (j : ℚ))) -
          L (Ring.choose (X : ℚ[X]) (k + 1))) ≤ 1 := by
      rw [hdiff]
      exact padicNorm.sum_le' (fun i _ => ih i) (by norm_num)
    have hb := hscale (k + 1) hshift
    intro j
    have he : L ((Ring.choose (X : ℚ[X]) (k + 1)).comp (X + C (j : ℚ))) =
        L (Ring.choose (X : ℚ[X]) (k + 1)) +
          (L ((Ring.choose (X : ℚ[X]) (k + 1)).comp (X + C (j : ℚ))) -
            L (Ring.choose (X : ℚ[X]) (k + 1))) := by ring
    rw [he]
    exact padicNorm.nonarchimedean.trans (max_le hb (hshift j))

/-- A linear functional bounded by one on binomial polynomials preserves every
uniform p-adic bound on the natural values of a polynomial. -/
lemma padicNorm_apply_le_of_choose_X {p : ℕ} [Fact p.Prime] (L : ℚ[X] →ₗ[ℚ] ℚ)
    (hL : ∀ k, padicNorm p (L (Ring.choose (X : ℚ[X]) k)) ≤ 1)
    {T : ℚ} (hT : 0 ≤ T) (P : ℚ[X]) (hP : ∀ j : ℕ, padicNorm p (P.eval (j : ℚ)) ≤ T) :
    padicNorm p (L P) ≤ T := by
  obtain ⟨N, c, hc⟩ := Polynomial.exists_sum_C_mul_choose_X P
  have hcoeff : ∀ j : ℕ, j < N → padicNorm p (c j) ≤ T := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      have he := congrArg (fun Q : ℚ[X] => Q.eval (j : ℚ)) hc
      simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_choose_X_natCast] at he
      rw [← sum_subset (range_subset_range.mpr (by omega : j + 1 ≤ N)) (fun k _ hk => by
        have hjk : j < k := by simp only [Finset.mem_range] at hk; omega
        rw [Nat.choose_eq_zero_of_lt hjk, Nat.cast_zero, mul_zero]), sum_range_succ,
          Nat.choose_self, Nat.cast_one, mul_one] at he
      have hs : padicNorm p (∑ k ∈ Finset.range j, c k * (j.choose k : ℚ)) ≤ T := by
        apply padicNorm.sum_le' _ hT
        intro k hk
        rw [padicNorm.mul]
        have hkj := Finset.mem_range.mp hk
        have hkbound := ih k hkj (by omega)
        have hchoose := padicNorm.of_nat (p := p) (j.choose k)
        calc
          _ ≤ padicNorm p (c k) * 1 :=
            mul_le_mul_of_nonneg_left hchoose (padicNorm.nonneg _)
          _ ≤ _ := by simpa only [mul_one] using hkbound
      have he' : c j = P.eval (j : ℚ) - ∑ k ∈ Finset.range j, c k * (j.choose k : ℚ) := by
        linarith [he]
      rw [he', sub_eq_add_neg]
      exact padicNorm.nonarchimedean.trans (max_le (hP j) (by simpa only [padicNorm.neg] using hs))
  rw [hc, map_sum]
  apply padicNorm.sum_le' _ hT
  intro k hk
  rw [← smul_eq_C_mul, map_smul, smul_eq_mul, padicNorm.mul]
  calc
    _ ≤ padicNorm p (c k) * 1 := mul_le_mul_of_nonneg_left (hL k) (padicNorm.nonneg _)
    _ ≤ _ := by simpa only [mul_one] using hcoeff k (Finset.mem_range.mp hk)

end LinearMap
