/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Integrals.FerrersDiagonal

/-!
# A triple product integral of Ferrers functions

The integral of `Q_l(cos θ) P_m(cos θ) P_n(cos θ) sin θ` on `[0,π]` vanishes when the degrees
satisfy strict triangle inequalities or have even sum (DLMF 14.17.17). The mixed pairwise
integral is skew in its degrees, and the Legendre recurrences preserve this pairing under
multiplication by polynomials of suitable degree. The polynomial difference of two mixed
products and orthogonality make the triple integral symmetric under the triangle condition.

## Main results

* `ferrers_triple_integral'`: the vanishing criterion for all natural degrees.
* `ferrers_triple_integral`: DLMF 14.17.17 for positive degrees.
-/

open Complex Filter Set MeasureTheory
open scoped Real Topology Nat
@[expose] public noncomputable section
namespace DLMF.Legendre.FerrersTriple
open DLMF.OrthogonalPolynomials

/-- A natural degree and zero order avoid the poles of the Ferrers second solution. -/
lemma legendreQRegular_nat (n : ℕ) : LegendreQRegular (n : ℂ) 0 := by
  intro j h
  have hh := congrArg Complex.re h
  simp at hh
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n), (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

/-- The Ferrers function Q of natural degree and zero order is integrable on `[-1, 1]`. -/
lemma intervalIntegrable_ferrersQ (n : ℕ) :
    IntervalIntegrable (fun x : ℝ => ferrersQ n 0 x) volume (-1) 1 := by
  have h := FerrersGreen.intervalIntegrable_PQ 0 (legendreQRegular_nat n)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)] at h ⊢
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioo
  have hz := ferrersP_nat_polynomial 0 hx
  norm_num only [Nat.cast_zero, legendrePolynomialP_zero] at hz
  simp only [hz, one_mul]

/-- The order - zero mixed Ferrers integral changes sign when the degrees are interchanged. -/
lemma integral_ferrersP_mul_ferrersQ_eq_neg_swap (l n : ℕ) :
    (∫ x : ℝ in -1..1, ferrersP l 0 x * ferrersQ n 0 x) =
      -(∫ x : ℝ in -1..1, ferrersP n 0 x * ferrersQ l 0 x) := by
  by_cases h : l = n
  · subst n
    have ho (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) : ferrersP l 0 (-x) * ferrersQ l 0 (-x) =
        -(ferrersP l 0 x * ferrersQ l 0 x) := by
      have hp := ferrersP_nat_reflection l 0 hx
      have hq := ferrersQ_nat_reflection_1 l 0 (x := x)
      simp only [Nat.cast_zero, one_mul, add_zero] at hp hq
      have hpow : ((-1 : ℂ) ^ l) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
      rw [hp, hq]
      linear_combination -(ferrersP l 0 x * ferrersQ l 0 x) * hpow
    have hi := intervalIntegral.integral_comp_neg
      (fun x : ℝ => ferrersP l 0 x * ferrersQ l 0 x) (a := (-1 : ℝ)) (b := 1)
    simp only [neg_neg] at hi
    have he : (∫ x : ℝ in -1..1, ferrersP l 0 (-x) * ferrersQ l 0 (-x)) =
        -(∫ x : ℝ in -1..1, ferrersP l 0 x * ferrersQ l 0 x) := by
      rw [← intervalIntegral.integral_neg]
      exact intervalIntegral.integral_congr_Ioo_of_le (by norm_num) ho
    rw [he] at hi
    exact hi.symm
  · have h1 := ferrersPQ_nat_integral l 0 n h (Nat.zero_le _)
    have h2 := ferrersPQ_nat_integral n 0 l (Ne.symm h) (Nat.zero_le _)
    simp only [Nat.cast_zero, Nat.add_zero, Nat.sub_zero] at h1 h2
    rw [h1, h2, Nat.add_comm n l]
    have hf1 : (l.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hf2 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hd : (l : ℂ) - n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
    have hd' : (n : ℂ) - l ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast Ne.symm h)
    have hs : (l : ℂ) + n + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (l + n)
    rw [show (n : ℂ) + l + 1 = (l : ℂ) + n + 1 by ring]
    field_simp [hf1, hf2, hd, hd', hs]
    ring

/-- The degree recurrence of the Ferrers second solution at natural degrees. -/
lemma ferrersQ_nat_recurrence (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ((n : ℂ) + 2) * ferrersQ (n + 2 : ℕ) 0 x - (2 * n + 3) * (x : ℂ) * ferrersQ (n + 1 : ℕ) 0 x +
      (n + 1) * ferrersQ n 0 x = 0 := by
  have h := ferrersQ_recurrence_3 n 0 (legendreQRegular_nat n) hx
  simpa only [sub_zero, add_zero, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using h

/-- The natural - degree Ferrers P factor can be replaced by its polynomial. -/
lemma integral_legendrePolynomialP_mul_ferrersQ (l n : ℕ) :
    (∫ x : ℝ in -1..1, legendrePolynomialP l x * ferrersQ n 0 x) =
      (∫ x : ℝ in -1..1, ferrersP l 0 x * ferrersQ n 0 x) := by
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro x hx
  dsimp only
  rw [ferrersP_nat_polynomial l hx]

/-- Polynomial moments against the Ferrers second solution are integrable. -/
lemma intervalIntegrable_ferrersQ_mul_pow_mul_legendrePolynomialP (l k n : ℕ) :
    IntervalIntegrable (fun x : ℝ => ferrersQ l 0 x * ((x : ℂ) ^ k * legendrePolynomialP n x))
      volume (-1) 1 :=
  (intervalIntegrable_ferrersQ l).mul_continuousOn ((continuous_ofReal.pow k).mul
    (continuous_legendrePolynomialP_ofReal n)).continuousOn

/-- The reflected polynomial moments against the Ferrers second solution are integrable. -/
lemma intervalIntegrable_legendrePolynomialP_mul_pow_mul_ferrersQ (l k n : ℕ) :
    IntervalIntegrable (fun x : ℝ => legendrePolynomialP l x * ((x : ℂ) ^ k * ferrersQ n 0 x))
      volume (-1) 1 := by
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    intervalIntegrable_ferrersQ_mul_pow_mul_legendrePolynomialP n k l

/-- Multiplication by a monomial of degree at most `n` preserves the skew mixed pairing. -/
lemma integral_moments_eq_neg_swap (l k n : ℕ) (hkn : k ≤ n) :
    (∫ x : ℝ in -1..1, ferrersQ l 0 x * ((x : ℂ) ^ k * legendrePolynomialP n x)) =
      -(∫ x : ℝ in -1..1, legendrePolynomialP l x * ((x : ℂ) ^ k * ferrersQ n 0 x)) := by
  induction k generalizing n with
  | zero =>
    simp only [pow_zero, one_mul]
    simp_rw [mul_comm (ferrersQ l 0 _) (legendrePolynomialP n _)]
    rw [integral_legendrePolynomialP_mul_ferrersQ, integral_legendrePolynomialP_mul_ferrersQ]
    exact integral_ferrersP_mul_ferrersQ_eq_neg_swap n l
  | succ k ih =>
    obtain ⟨n, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    have h3 : (2 * (n : ℂ) + 3) ≠ 0 := by norm_cast
    set A : ℂ := ((n : ℂ) + 2) / (2 * (n : ℂ) + 3)
    set B : ℂ := ((n : ℂ) + 1) / (2 * (n : ℂ) + 3)
    have hp (x : ℝ) : ferrersQ l 0 x * ((x : ℂ) ^ (k + 1) * legendrePolynomialP (n + 1) x) =
        A * (ferrersQ l 0 x * ((x : ℂ) ^ k * legendrePolynomialP (n + 2) x))+
        B * (ferrersQ l 0 x * ((x : ℂ) ^ k * legendrePolynomialP n x)) := by
      have hr := legendrePolynomialP_recurrence n (x : ℂ)
      have hx : (x : ℂ) * legendrePolynomialP (n + 1) x =
          (((n : ℂ) + 2) * legendrePolynomialP (n + 2) x+
            ((n : ℂ) + 1) * legendrePolynomialP n x) / (2 * (n : ℂ) + 3) := by
        rw [eq_div_iff h3]
        linear_combination -hr
      rw [pow_succ, mul_assoc ((x : ℂ) ^ k), hx]
      dsimp only [A, B]
      ring
    have hq (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) :
        legendrePolynomialP l x * ((x : ℂ) ^ (k + 1) * ferrersQ (n + 1 : ℕ) 0 x) =
        A * (legendrePolynomialP l x * ((x : ℂ) ^ k * ferrersQ (n + 2 : ℕ) 0 x))+
        B * (legendrePolynomialP l x * ((x : ℂ) ^ k * ferrersQ n 0 x)) := by
      have hr := ferrersQ_nat_recurrence n hx
      have hxq : (x : ℂ) * ferrersQ (n + 1 : ℕ) 0 x =
          (((n : ℂ) + 2) * ferrersQ (n + 2 : ℕ) 0 x+
            ((n : ℂ) + 1) * ferrersQ n 0 x) / (2 * (n : ℂ) + 3) := by
        rw [eq_div_iff h3]
        linear_combination -hr
      rw [pow_succ, mul_assoc ((x : ℂ) ^ k), hxq]
      dsimp only [A, B]
      ring
    simp_rw [hp]
    rw [intervalIntegral.integral_add ((intervalIntegrable_ferrersQ_mul_pow_mul_legendrePolynomialP
      l k _).const_mul _)
      ((intervalIntegrable_ferrersQ_mul_pow_mul_legendrePolynomialP l k _).const_mul _),
        intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, ih (n + 2) (by omega), ih n (by omega),
      intervalIntegral.integral_congr_Ioo_of_le (by norm_num) hq,
      intervalIntegral.integral_add ((intervalIntegrable_legendrePolynomialP_mul_pow_mul_ferrersQ l
        k _).const_mul _)
        ((intervalIntegrable_legendrePolynomialP_mul_pow_mul_ferrersQ l k _).const_mul _),
          intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    ring

open Polynomial

/-- The polynomial representing `Q_l P_(l + k) - P_l Q_(l + k)` on `(-1, 1)`. -/
def differencePolynomial (l : ℕ) : ℕ → Polynomial ℂ
  | 0 => 0
  | 1 => C (Gamma ((l : ℂ) + 1) / Gamma ((l : ℂ) + 2))
  | k + 2 => C (((l : ℂ) + k + 2)⁻¹)*
      (C (2 * ((l : ℂ) + k) + 3) * X * differencePolynomial l (k + 1)-
        C ((l : ℂ) + k + 1) * differencePolynomial l k)

/-- The mixed difference polynomial has degree at most the difference of its indices. -/
lemma natDegree_differencePolynomial_le (l k : ℕ) :
    (differencePolynomial l k).natDegree ≤ k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [differencePolynomial]
  | one => simp [differencePolynomial]
  | more k ih0 ih1 =>
    simp only [differencePolynomial]
    apply le_trans (natDegree_C_mul_le _ _)
    apply le_trans (natDegree_sub_le _ _)
    apply max_le
    · exact (natDegree_mul_le_of_le
        ((natDegree_C_mul_le _ _).trans natDegree_X_le) ih1).trans (by omega)
    · exact (natDegree_C_mul_le _ _).trans (ih0.trans (by omega))

/-- The difference of two mixed Ferrers products is the difference polynomial. -/
lemma eval_differencePolynomial (l k : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (differencePolynomial l k).eval (x : ℂ) = ferrersQ l 0 x * legendrePolynomialP (l + k) x-
      legendrePolynomialP l x * ferrersQ (l + k : ℕ) 0 x := by
  induction k using Nat.twoStepInduction with
  | zero => simp [differencePolynomial, mul_comm]
  | one =>
    have h := ferrers_wronskian_5 l 0 (legendreQRegular_nat l) hx
    have hp := ferrersP_nat_polynomial (l + 1) hx
    simp only [Nat.cast_add, Nat.cast_one] at hp
    simp only [sub_zero, add_zero] at h
    rw [hp, ferrersP_nat_polynomial l hx] at h
    simpa only [differencePolynomial, eval_C, mul_comm, Nat.cast_add, Nat.cast_one] using h.symm
  | more k ih0 ih1 =>
    have hp := legendrePolynomialP_recurrence (l + k) (x : ℂ)
    have hq := ferrersQ_nat_recurrence (l + k) hx
    have hd : (l : ℂ) + k + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (l + k + 1)
    simp only [differencePolynomial, eval_mul, eval_sub, eval_C, eval_X, ih0, ih1]
    simp only [Nat.add_assoc, Nat.cast_add] at hp hq ⊢
    field_simp [hd]
    linear_combination -(ferrersQ l 0 x) * hp + legendrePolynomialP l x * hq

/-- A Legendre polynomial is orthogonal to every monomial of smaller degree. -/
lemma integral_legendrePolynomialP_mul_pow_eq_zero (n k : ℕ) (hkn : k < n) :
    (∫ x : ℝ in -1..1, legendrePolynomialP n x * (x : ℂ) ^ k) = 0 := by
  induction k generalizing n with
  | zero =>
    have h := legendre_orthogonality n 0
    simpa only [legendrePolynomialP_zero, mul_one, ite_eq_right (Nat.ne_of_gt hkn), pow_zero] using
      h
  | succ k ih =>
    obtain ⟨n, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    have h3 : (2 * (n : ℂ) + 3) ≠ 0 := by norm_cast
    have he (x : ℝ) : legendrePolynomialP (n + 1) x * (x : ℂ) ^ (k + 1) =
        (((n : ℂ) + 2) / (2 * n + 3)) * (legendrePolynomialP (n + 2) x * (x : ℂ) ^ k)+
        (((n : ℂ) + 1) / (2 * n + 3)) * (legendrePolynomialP n x * (x : ℂ) ^ k) := by
      have hr := legendrePolynomialP_recurrence n (x : ℂ)
      have hx : (x : ℂ) * legendrePolynomialP (n + 1) x =
          (((n : ℂ) + 2) * legendrePolynomialP (n + 2) x+
            ((n : ℂ) + 1) * legendrePolynomialP n x) / (2 * (n : ℂ) + 3) := by
        rw [eq_div_iff h3]
        linear_combination -hr
      calc _ = (x : ℂ) ^ k * ((x : ℂ) * legendrePolynomialP (n + 1) x) := by ring
        _ = _ := by rw [hx]; ring
    have hint (j : ℕ) : IntervalIntegrable
        (fun x : ℝ => legendrePolynomialP j x * (x : ℂ) ^ k) volume (-1) 1 := by
      exact ((continuous_legendrePolynomialP_ofReal j).mul
        (continuous_ofReal.pow k)).intervalIntegrable _ _
    simp_rw [he]
    rw [intervalIntegral.integral_add ((hint (n + 2)).const_mul _)
      ((hint n).const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, ih (n + 2) (by omega), ih n (by omega)]
    ring

/-- A Legendre polynomial is orthogonal to every polynomial of smaller degree. -/
lemma integral_legendrePolynomialP_mul_polynomial_eq_zero (n : ℕ) (p : Polynomial ℂ) (hp :
  p.natDegree < n) :
    (∫ x : ℝ in -1..1, legendrePolynomialP n x * p.eval (x : ℂ)) = 0 := by
  have he (x : ℝ) : legendrePolynomialP n x * p.eval (x : ℂ) =
      ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * (legendrePolynomialP n x * (x : ℂ) ^ j) :=
        by
    rw [eval_eq_sum_range, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro j hj
    rw [intervalIntegral.integral_const_mul, integral_legendrePolynomialP_mul_pow_eq_zero n j (by
      have := Finset.mem_range.mp hj;omega), mul_zero]
  · intro j hj
    exact (((continuous_legendrePolynomialP_ofReal n).mul
      (continuous_ofReal.pow j)).const_mul _).intervalIntegrable _ _

/-- A polynomial of degree at most `n` preserves the skew mixed pairing. -/
lemma integral_polynomial_moments_eq_neg_swap (l n : ℕ) (p : Polynomial ℂ) (hp : p.natDegree ≤ n) :
    (∫ x : ℝ in -1..1, ferrersQ l 0 x * (p.eval (x : ℂ) * legendrePolynomialP n x)) =
      -(∫ x : ℝ in -1..1, legendrePolynomialP l x * (p.eval (x : ℂ) * ferrersQ n 0 x)) := by
  have hleft (x : ℝ) : ferrersQ l 0 x * (p.eval (x : ℂ) * legendrePolynomialP n x) =
      ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j*
        (ferrersQ l 0 x * ((x : ℂ) ^ j * legendrePolynomialP n x)) := by
    rw [eval_eq_sum_range, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hright (x : ℝ) : legendrePolynomialP l x * (p.eval (x : ℂ) * ferrersQ n 0 x) =
      ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j*
        (legendrePolynomialP l x * ((x : ℂ) ^ j * ferrersQ n 0 x)) := by
    rw [eval_eq_sum_range, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [hleft, hright]
  rw [intervalIntegral.integral_finsetSum (fun j _ =>
      (intervalIntegrable_ferrersQ_mul_pow_mul_legendrePolynomialP l j n).const_mul _),
    intervalIntegral.integral_finsetSum (fun j _ =>
      (intervalIntegrable_legendrePolynomialP_mul_pow_mul_ferrersQ l j n).const_mul _), ←
        Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_moments_eq_neg_swap l j n (by have := Finset.mem_range.mp hj;omega)]
  ring

/-- The canonical real Legendre polynomial has degree at most its index. -/
lemma natDegree_legendrePolyR_le (n : ℕ) : (legendrePolyR n).natDegree ≤ n := by
  have hm : (((shiftedLegendre n).map (Int.castRingHom ℝ))).natDegree ≤ n :=
    natDegree_map_le.trans (by simp)
  have ha : (C (1 / 2 : ℝ) * (1 - X) : Polynomial ℝ).natDegree ≤ 1 := by
    exact (natDegree_C_mul_le _ _).trans ((natDegree_sub_le _ _).trans (by simp))
  exact natDegree_comp_le.trans ((Nat.mul_le_mul hm ha).trans (by simp))

/-- The mixed integral of one Ferrers Q function and two Legendre polynomials on `[-1, 1]`. -/
def integral (l m n : ℕ) : ℂ :=
  ∫ x : ℝ in -1..1, ferrersQ l 0 x * (legendrePolynomialP m x * legendrePolynomialP n x)

/-- One Ferrers Q function times two Legendre polynomials is integrable on `[-1, 1]`. -/
lemma intervalIntegrable_triple (l m n : ℕ) : IntervalIntegrable
    (fun x : ℝ => ferrersQ l 0 x * (legendrePolynomialP m x * legendrePolynomialP n x))
      volume (-1) 1 :=
  (intervalIntegrable_ferrersQ l).mul_continuousOn ((continuous_legendrePolynomialP_ofReal m).mul
    (continuous_legendrePolynomialP_ofReal n)).continuousOn

/-- A smaller polynomial factor makes the mixed triple integral skew in the other degrees. -/
lemma integral_eq_neg_swap (l m n : ℕ) (hmn : m ≤ n) : integral l m n = -integral n m l := by
  have h := integral_polynomial_moments_eq_neg_swap l n ((legendrePolyR m).map ofRealHom)
    ((natDegree_map_le.trans (natDegree_legendrePolyR_le m)).trans hmn)
  simp_rw [← legendrePolynomialP_eq_eval] at h
  simpa only [integral, mul_comm, mul_left_comm, mul_assoc] using h

/-- Orthogonality makes the mixed triple integral symmetric under the stated degree bound. -/
lemma integral_eq_swap_of_le (l m n : ℕ) (hln : l ≤ n) (hbound : n - l < m) :
    integral l m n = integral n m l := by
  have hp := integral_legendrePolynomialP_mul_polynomial_eq_zero m (differencePolynomial l (n - l))
    ((natDegree_differencePolynomial_le l (n - l)).trans_lt hbound)
  have he : l + (n - l) = n := Nat.add_sub_of_le hln
  apply sub_eq_zero.mp
  change (∫ x : ℝ in -1..1, ferrersQ l 0 x * (legendrePolynomialP m x * legendrePolynomialP n x))-
    (∫ x : ℝ in -1..1, ferrersQ n 0 x * (legendrePolynomialP m x * legendrePolynomialP l x)) = 0
  rw [← intervalIntegral.integral_sub (intervalIntegrable_triple l m n)
    (intervalIntegrable_triple n m l)]
  calc _ = ∫ x : ℝ in -1..1, legendrePolynomialP m x*
      (differencePolynomial l (n - l)).eval (x : ℂ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro x hx
        dsimp only
        rw [eval_differencePolynomial l (n - l) hx, he]
        ring
    _ = 0 := hp

/-- The mixed triple integral is symmetric when the remaining degree exceeds the degree difference.
  -/
lemma integral_eq_swap (l m n : ℕ) (hl : l < m + n) (hn : n < m + l) :
    integral l m n = integral n m l := by
  rcases le_total l n with h | h
  · exact integral_eq_swap_of_le l m n h (by omega)
  · exact (integral_eq_swap_of_le n m l h (by omega)).symm

/-- The two polynomial factors in the mixed triple integral can be interchanged. -/
lemma integral_comm (l m n : ℕ) : integral l m n = integral l n m := by
  simp only [integral, mul_comm]

/-- Strict triangle inequalities force the mixed triple integral to vanish. -/
lemma integral_zero_triangle (l m n : ℕ) (hl : l < m + n) (hm : m < l + n) (hn : n < l + m) :
    integral l m n = 0 := by
  rcases le_total m n with h | h
  · have hs := integral_eq_swap l m n hl (by omega)
    have ha := integral_eq_neg_swap l m n h
    linear_combination (1 / 2 : ℂ) * hs + (1 / 2 : ℂ) * ha
  · have hs := integral_eq_swap l n m (by omega) (by omega)
    have ha := integral_eq_neg_swap l n m h
    rw [integral_comm l m n]
    linear_combination (1 / 2 : ℂ) * hs + (1 / 2 : ℂ) * ha

/-- Reflection multiplies the Legendre polynomial of degree `n` by `(-1) ^ n`. -/
lemma legendrePolynomialP_neg (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    legendrePolynomialP n (-x) = (-1 : ℂ) ^ n * legendrePolynomialP n x := by
  have h := ferrersP_nat_reflection n 0 hx
  have hnx : -x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith[hx.2], by linarith[hx.1]⟩
  simp only [Nat.cast_zero, Nat.add_zero] at h
  rw [ferrersP_nat_polynomial n hnx, ferrersP_nat_polynomial n hx] at h
  simpa only [ofReal_neg] using h

/-- Even total degree makes the mixed triple integrand odd. -/
lemma integral_zero_even (l m n : ℕ) (he : Even (l + m + n)) : integral l m n = 0 := by
  let f : ℝ → ℂ := fun x => ferrersQ l 0 x * (legendrePolynomialP m x * legendrePolynomialP n x)
  have ho (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) : f (-x) = -f x := by
    have hq := ferrersQ_nat_reflection_1 l 0 (x := x)
    simp only [Nat.cast_zero, Nat.add_zero, mul_zero] at hq
    dsimp only [f]
    rw [hq, show ((-x : ℝ) : ℂ)=-(x : ℂ) by simp, legendrePolynomialP_neg m hx,
      legendrePolynomialP_neg n hx]
    have hsign : (-1 : ℂ) ^ (l + 1) * (-1) ^ m * (-1) ^ n = -1 := by
      rw [← pow_add, ← pow_add, show l + 1 + m + n = (l + m + n) + 1 by omega, pow_succ,
        he.neg_one_pow]
      ring
    linear_combination (ferrersQ l 0 x * (legendrePolynomialP m x * legendrePolynomialP n x)) *
      hsign
  have hi := intervalIntegral.integral_comp_neg f (a := (-1 : ℝ)) (b := 1)
  simp only [neg_neg] at hi
  have hn : (∫ x : ℝ in -1..1, f (-x))=-(∫ x : ℝ in -1..1, f x) := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr_Ioo_of_le (by norm_num) ho
  rw [hn] at hi
  change -integral l m n = integral l m n at hi
  linear_combination -(1 / 2 : ℂ) * hi

/-- The substitution `x = cos θ` converts the angular triple integral to the interval integral. -/
lemma integral_cos_mul_sin (l m n : ℕ) :
    (∫ θ : ℝ in 0..π, ferrersQ l 0 (Real.cos θ) * ferrersP m 0 (Real.cos θ)*
      ferrersP n 0 (Real.cos θ) * Real.sin θ) = integral l m n := by
  let f : ℝ → ℂ := fun x => ferrersQ l 0 x * (legendrePolynomialP m x * legendrePolynomialP n x)
  have hinj : InjOn Real.cos (Ioo 0 π) := by
    intro a ha b hb he
    exact Real.injOn_cos ⟨ha.1.le, ha.2.le⟩ ⟨hb.1.le, hb.2.le⟩ he
  have him : Real.cos '' Ioo 0 π = Ioo (-1 : ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      have h1 := Real.cos_lt_cos_of_nonneg_of_le_pi ht.1.le le_rfl ht.2
      have h2 := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl ht.2.le ht.1
      simpa only [mem_Ioo, Real.cos_pi, Real.cos_zero] using And.intro h1 h2
    · intro hx
      refine ⟨Real.arccos x, ⟨Real.arccos_pos.mpr hx.2, Real.arccos_lt_pi.mpr hx.1⟩, ?_⟩
      exact Real.cos_arccos hx.1.le hx.2.le
  have hcov := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun t (_ : t ∈ Ioo (0 : ℝ) π) => (Real.hasDerivAt_cos t).hasDerivWithinAt) hinj f
  rw [him] at hcov
  rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo,
    integral, intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
  change (∫ θ : ℝ in Ioo 0 π, ferrersQ l 0 (Real.cos θ) * ferrersP m 0 (Real.cos θ)*
    ferrersP n 0 (Real.cos θ) * Real.sin θ)=∫ x in Ioo (-1) 1, f x
  rw [hcov]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have hc : Real.cos t ∈ Ioo (-1 : ℝ) 1 := by
    rw [← him]
    exact mem_image_of_mem _ ht
  dsimp only [f]
  rw [ferrersP_nat_polynomial m hc, ferrersP_nat_polynomial n hc, abs_neg,
    abs_of_pos (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2), Complex.real_smul]
  ring

end DLMF.Legendre.FerrersTriple

namespace DLMF.Legendre

/-- The Ferrers triple integral vanishes under the triangle or parity condition. This is
stronger than DLMF, which assumes positive integers for all three degrees. -/
@[dlmf 14.17.E17
  "stronger than DLMF: all natural degrees satisfying the triangle or parity condition"]
theorem ferrers_triple_integral' (l m n : ℕ)
    (htri : (|((m : ℤ) - n)| < l ∧ l < m + n) ∨ Even (l + m + n)) :
    (∫ θ : ℝ in 0..π, ferrersQ l 0 (Real.cos θ) * ferrersP m 0 (Real.cos θ)*
      ferrersP n 0 (Real.cos θ) * Real.sin θ) = 0 := by
  rw [FerrersTriple.integral_cos_mul_sin]
  rcases htri with ⟨habs, hlt⟩ | he
  · have h := abs_lt.mp habs
    exact FerrersTriple.integral_zero_triangle l m n hlt (by omega) (by omega)
  · exact FerrersTriple.integral_zero_even l m n he


/-- DLMF 14.17.17: for positive integers `l, m, n` such that either `|m-n| < l < m+n` or `l+m+n` is
even, `∫₀^π 𝖰_l(cos θ) 𝖯_m(cos θ) 𝖯_n(cos θ) sin θ dθ = 0`. -/
@[dlmf 14.17.E17]
theorem ferrers_triple_integral (l m n : ℕ) (hl : 0 < l) (hm : 0 < m) (hn : 0 < n)
    (htri : (|((m:ℤ)-n)| < l ∧ l < m+n) ∨ Even (l+m+n)) :
    (∫ θ : ℝ in 0..π, ferrersQ l 0 (Real.cos θ)*ferrersP m 0 (Real.cos θ)*ferrersP n 0
        (Real.cos θ)*Real.sin θ)=0 := by
  exact ferrers_triple_integral' l m n htri


end DLMF.Legendre
