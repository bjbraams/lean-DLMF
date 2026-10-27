/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Classical
public import DLMF.Gamma.Pochhammer
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.Real.Irrational

/-!
# Topics in orthogonal polynomials (AAR Chapter 7)

Connection coefficients, Turán's inequality, positive summability of ultraspherical series,
and Apéry's theorem on the irrationality of `ζ(3)`. None of these are in Mathlib.
The Jacobi connection proof uses finite Pochhammer inversion and the Mathlib
contributors’ finite-sum, binomial and polynomial APIs. Its regular head term
retains the case `α + β = -1`.
-/

@[expose] public section

open Complex Polynomial
open scoped Real Nat
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.OrthogonalPolynomials

/-- The pole-free head form of the finite very-well-poised cancellation. -/
theorem sum_choose_weighted_recip_poch_tail {a : ℂ} (ha : -1 < a.re) (N : ℕ) :
    1 / poch (a + 1) (N + 1) +
      ∑ k ∈ Finset.range (N + 1), (-1 : ℂ) ^ (k + 1) * ((N + 1).choose (k + 1) : ℂ) *
        (a + 2 * (k + 1)) / poch (a + (k + 1)) (N + 2) = 0 := by
  let g : ℕ → ℂ := fun k => (-1) ^ k * (N.choose k : ℂ) / poch (a + k + 1) (N + 1)
  have hterm (k : ℕ) : (-1 : ℂ) ^ (k + 1) * ((N + 1).choose (k + 1) : ℂ) * (a + 2 * (k + 1)) /
      poch (a + (k + 1)) (N + 2) = g (k + 1) - g k := by
    have h1 : poch (a + (k + 1)) (N + 2) =
        (a + (k + 1)) * poch (a + (k + 1) + 1) (N + 1) := poch_succ_left _ _
    have h2 : poch (a + k + 1) (N + 2) =
        poch (a + k + 1) (N + 1) * (a + k + 1 + (N + 1)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using poch_succ (a + k + 1) (N + 1)
    have hc : ((N + 1).choose (k + 1) : ℂ) * (k + 1) = (N + 1) * (N.choose k : ℂ) := by
      exact_mod_cast (Nat.add_one_mul_choose_eq N k).symm
    have hB : 1 / poch (a + (k + 1) + 1) (N + 1) =
        (a + (k + 1)) / poch (a + (k + 1)) (N + 2) := by
      rw [h1]
      have he : a + (k + 1) ≠ 0 := by intro he; have := congrArg re he; simp at this; linarith [Nat.cast_nonneg (α := ℝ) k]
      field_simp
    have hC : 1 / poch (a + (k + 1)) (N + 1) =
        (a + k + 1 + (N + 1)) / poch (a + (k + 1)) (N + 2) := by
      rw [show a + (k + 1) = a + k + 1 by ring, h2]
      have he : a + k + 1 + (N + 1) ≠ 0 := by
        intro he; have := congrArg re he; simp at this
        linarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) N]
      field_simp
    dsimp [g]
    simp only [Nat.cast_add, Nat.cast_one] at hc ⊢
    rw [show a + k + 1 = a + (k + 1) by ring]
    simp only [one_div] at hB hC
    simp only [div_eq_mul_inv]
    rw [hB, hC,
      Nat.choose_succ_succ, Nat.cast_add, pow_succ]
    rw [Nat.choose_succ_succ, Nat.cast_add] at hc
    have hA : poch (a + (k + 1 : ℕ)) (N + 2) ≠ 0 :=
      poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; linarith [Nat.cast_nonneg (α := ℝ) k])) _
    simp only [Nat.cast_add, Nat.cast_one] at hA
    field_simp
    linear_combination -hc
  simp_rw [hterm]
  -- Mathlib’s finite telescoping identity evaluates the regularized head-and-tail sum.
  rw [Finset.sum_range_sub]
  simp [g]



/-- The finite very-well-poised cancellation underlying polynomial basis inversion. -/
theorem sum_choose_weighted_recip_poch {a : ℂ} (ha : 0 < a.re) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 2), (-1 : ℂ) ^ k * ((N + 1).choose k : ℂ) * (a + 2 * k) /
      poch (a + k) (N + 2) = 0 := by
  have hh := sum_choose_weighted_recip_poch_tail (by linarith : -1 < a.re) N
  have ha0 : a ≠ 0 := by intro he; simp [he] at ha
  have hz : a / poch a (N + 2) = 1 / poch (a + 1) (N + 1) := by
    rw [poch_succ_left]
    field_simp
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one, pow_zero, Nat.choose_zero_right,
    Nat.cast_one, one_mul, mul_zero, add_zero] at hh ⊢
  rw [hz]
  linear_combination hh

/-- Regroup a finite triangular double sum by total degree. -/
theorem sum_triangle_by_total_degree (F : ℕ → ℕ → ℂ) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N - k + 1), F k j =
      ∑ r ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (r + 1), F k (r - k) := by
  induction N generalizing F with
  | zero => simp
  | succ N ih =>
    conv_lhs => rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_add_right, Nat.sub_zero]
    rw [ih (fun k j => F (k + 1) j)]
    conv_rhs => rw [Finset.sum_range_succ']
    have hh (r : ℕ) : (∑ k ∈ Finset.range (r + 1 + 1), F k (r + 1 - k)) =
        (∑ k ∈ Finset.range (r + 1), F (k + 1) (r - k)) + F 0 (r + 1) := by
      rw [Finset.sum_range_succ']
      simp only [Nat.add_sub_add_right, Nat.sub_zero]
    simp_rw [hh]
    rw [Finset.sum_add_distrib, Finset.sum_range_succ' (f := F 0)]
    simp only [Nat.zero_sub]
    have hz : (∑ k ∈ Finset.range 1, F k 0) = F 0 0 := by norm_num
    rw [hz]
    ring

/-- Include the degree-zero value of the finite cancellation. -/
theorem sum_choose_weighted_recip_poch_eq {a : ℂ} (ha : 0 < a.re) (r : ℕ) :
    ∑ k ∈ Finset.range (r + 1), (-1 : ℂ) ^ k * (r.choose k : ℂ) * (a + 2 * k) /
      poch (a + k) (r + 1) = if r = 0 then 1 else 0 := by
  cases r with
  | zero =>
    have ha0 : a ≠ 0 := by intro he; simp [he] at ha
    simp [poch_one, ha0]
  | succ r => simpa using sum_choose_weighted_recip_poch ha r

/-- Finite triangular Pochhammer inversion, including the exceptional zero base. -/
theorem sum_choose_recip_poch {a : ℂ} (ha : -1 < a.re) (r : ℕ) :
    ∑ k ∈ Finset.range (r + 1), (-1 : ℂ) ^ k * (r.choose k : ℂ) /
      (poch (a + k) k * poch (a + 2 * k + 1) (r - k)) = if r = 0 then 1 else 0 := by
  cases r with
  | zero => simp [poch_zero]
  | succ N =>
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one, pow_zero, Nat.choose_zero_right,
      one_mul, mul_zero, add_zero, poch_zero, Nat.sub_zero, ↓reduceIte]
    have ht (k : ℕ) (hk : k ∈ Finset.range (N + 1)) :
        (-1 : ℂ) ^ (k + 1) * ((N + 1).choose (k + 1) : ℂ) /
          (poch (a + (k + 1)) (k + 1) * poch (a + 2 * (k + 1) + 1) (N + 1 - (k + 1))) =
        (-1 : ℂ) ^ (k + 1) * ((N + 1).choose (k + 1) : ℂ) * (a + 2 * (k + 1)) /
          poch (a + (k + 1)) (N + 2) := by
      have hkN : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hd : poch (a + (k + 1)) (N + 2) =
          poch (a + (k + 1)) (k + 1) * (a + 2 * (k + 1)) *
            poch (a + 2 * (k + 1) + 1) (N - k) := by
        have hh := poch_add (a + (k + 1)) (k + 1) (N - k + 1)
        rw [show k + 1 + (N - k + 1) = N + 2 by omega,
          show a + (k + 1) + (k + 1 : ℕ) = a + 2 * (k + 1) by push_cast; ring,
          poch_succ_left (a + 2 * (k + 1)) (N - k)] at hh
        simpa only [mul_assoc] using hh
      have hz : a + 2 * (k + 1) ≠ 0 := by
        intro he; have hh := congrArg Complex.re he; simp at hh
        linarith [Nat.cast_nonneg (α := ℝ) k]
      rw [hd, show N + 1 - (k + 1) = N - k by omega]
      have hp1 : poch (a + (k + 1)) (k + 1) ≠ 0 :=
        poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; linarith [Nat.cast_nonneg (α := ℝ) k])) _
      have hp2 : poch (a + 2 * (k + 1) + 1) (N - k) ≠ 0 :=
        poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; linarith [Nat.cast_nonneg (α := ℝ) k])) _
      simp only [mul_comm] at hp1 hp2 hz ⊢
      field_simp [hp1, hp2, hz]
    rw [Finset.sum_congr rfl ht]
    simpa [add_comm] using sum_choose_weighted_recip_poch_tail ha N

/-- Inverse triangular Jacobi coefficients for powers of `(1-x)/2`. -/
noncomputable def jacobiInverseCoeff (α β : ℂ) (n k : ℕ) : ℂ :=
  (-1) ^ k * (n.factorial : ℂ) / (n - k).factorial * poch (α + k + 1) (n - k) /
    (poch (α + β + k + 1) k * poch (α + β + 2 * k + 2) (n - k))

/-- Regularity of the triangular Jacobi leading factors on the classical parameter range. -/
theorem jacobi_leading_poch_ne_zero {α β : ℂ} (hα : -1 < α.re) (hβ : -1 < β.re) (k : ℕ) :
    poch (α + β + k + 1) k ≠ 0 := by
  cases k with
  | zero => simp [poch_zero]
  | succ k =>
    apply poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos ?_)
    simp only [add_re, natCast_re, one_re, Nat.cast_add, Nat.cast_one]
    linarith [Nat.cast_nonneg (α := ℝ) k]

set_option maxHeartbeats 800000 in
/-- Multiplication of the two triangular coefficient matrices reduces to a finite inversion sum. -/
theorem jacobiInverseCoeff_mul_gaussCoeff {α β : ℂ} (hα : -1 < α.re) (hβ : -1 < β.re)
    (n j t : ℕ) (ht : j + t ≤ n) :
    jacobiInverseCoeff α β n (j + t) * (poch (α + 1) (j + t) / (j + t).factorial *
      gaussHGCoeff (-((j + t : ℕ) : ℂ)) ((j + t : ℕ) + α + β + 1) (α + 1) j) =
      (n.choose j : ℂ) * poch (α + j + 1) (n - j) *
        ((-1 : ℂ) ^ t * ((n - j).choose t : ℂ) /
          (poch (α + β + 2 * j + 1 + t) t *
            poch (α + β + 2 * j + 2 * t + 2) (n - j - t))) := by
  have hjn : j ≤ n := by omega
  have htn : t ≤ n - j := by omega
  have hαnp : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by simp; linarith)
  have hp (k : ℕ) : poch (α + 1) k ≠ 0 := poch_ne_zero_of_not_neg_nat hαnp k
  have hf (k : ℕ) : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hsplit : poch (α + β + (j + t : ℕ) + 1) (j + t) =
      poch (α + β + (j + t : ℕ) + 1) j * poch (α + β + 2 * j + 1 + t) t := by
    rw [poch_add]
    congr 2
    push_cast
    ring
  have htop : poch (α + β + (j + t : ℕ) + 1) j ≠ 0 := by
    have hh := jacobi_leading_poch_ne_zero hα hβ (j + t)
    rw [hsplit] at hh
    exact left_ne_zero_of_mul hh
  have htail : poch (α + β + 2 * j + 1 + t) t ≠ 0 := by
    have hh := jacobi_leading_poch_ne_zero hα hβ (j + t)
    rw [hsplit] at hh
    exact right_ne_zero_of_mul hh
  have hd : poch (α + β + 2 * (j + t : ℕ) + 2) (n - (j + t)) ≠ 0 := by
    apply poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos ?_)
    simp only [add_re, mul_re, natCast_re, natCast_im, re_ofNat, im_ofNat, mul_zero,
      sub_zero, add_zero]
    linarith [Nat.cast_nonneg (α := ℝ) (j + t)]
  have hnum : poch (α + 1) (j + t) * poch (α + (j + t : ℕ) + 1) (n - (j + t)) =
      poch (α + 1) j * poch (α + j + 1) (n - j) := by
    rw [show α + (j + t : ℕ) + 1 = α + 1 + (j + t : ℕ) by ring,
      ← poch_add, Nat.add_sub_of_le ht,
      show α + j + 1 = α + 1 + j by ring, ← poch_add, Nat.add_sub_of_le hjn]
  unfold jacobiInverseCoeff gaussHGCoeff
  rw [DLMF.Gamma.poch_neg_nat_eq, ite_eq_left (by omega : j ≤ j + t),
    show j + t - j = t by omega, hsplit,
    show ((j + t : ℕ) : ℂ) + α + β + 1 = α + β + (j + t : ℕ) + 1 by ring,
    show n - (j + t) = n - j - t by omega,
    show α + β + 2 * ((j + t : ℕ) : ℂ) + 2 = α + β + 2 * j + 2 * t + 2 by push_cast; ring,
    Nat.cast_choose ℂ hjn, Nat.cast_choose ℂ htn]
  have hd' : poch (α + β + 2 * j + 2 * t + 2) (n - j - t) ≠ 0 := by
    rw [show n - j - t = n - (j + t) by omega,
      show α + β + 2 * j + 2 * t + 2 = α + β + 2 * ((j + t : ℕ) : ℂ) + 2 by push_cast; ring]
    exact hd
  have hsgn : (-1 : ℂ) ^ (j + t) * (-1) ^ j = (-1) ^ t := by
    rw [pow_add]
    calc
      _ = ((-1 : ℂ) ^ j * (-1) ^ j) * (-1) ^ t := by ring
      _ = _ := by rw [← mul_pow]; norm_num
  field_simp [hp, hf, htop, htail, hd']
  have hnum' : poch (α + 1) (j + t) * poch (α + (j + t : ℕ) + 1) (n - j - t) =
      poch (α + 1) j * poch (α + j + 1) (n - j) := by
    simpa only [Nat.sub_sub] using hnum
  calc
    _ = ((-1 : ℂ) ^ (j + t) * (-1) ^ j) *
        (poch (α + 1) (j + t) * poch (α + (j + t : ℕ) + 1) (n - j - t)) := by ring
    _ = _ := by rw [hsgn, hnum']; ring


/-- Powers of the shifted coordinate in the Jacobi basis, including `α + β = -1`. -/
theorem jacobi_monomial_inverse {α β : ℂ} (hα : -1 < α.re) (hβ : -1 < β.re) (n : ℕ) (x : ℂ) :
    ((1 - x) / 2) ^ n = ∑ k ∈ Finset.range (n + 1), jacobiInverseCoeff α β n k * jacobiPolyP α β k x := by
  have hexpand : (∑ k ∈ Finset.range (n + 1), jacobiInverseCoeff α β n k * jacobiPolyP α β k x) =
      ∑ j ∈ Finset.range (n + 1), (∑ k ∈ Finset.Ico j (n + 1),
        jacobiInverseCoeff α β n k * (poch (α + 1) k / k.factorial *
          gaussHGCoeff (-(k : ℂ)) (k + α + β + 1) (α + 1) j)) * ((1 - x) / 2) ^ j := by
    simp_rw [jacobiPolyP, ordinaryHypergeometric_eq_sum_neg_nat, Finset.mul_sum]
    rw [Finset.sum_comm' (t' := Finset.range (n + 1)) (s' := fun j => Finset.Ico j (n + 1))
      (by intro k j; simp only [Finset.mem_range, Finset.mem_Ico]; omega)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hs (j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
      (∑ k ∈ Finset.Ico j (n + 1), jacobiInverseCoeff α β n k * (poch (α + 1) k / k.factorial *
          gaussHGCoeff (-(k : ℂ)) (k + α + β + 1) (α + 1) j)) = if j = n then 1 else 0 := by
    have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    rw [Finset.sum_Ico_eq_sum_range, show n + 1 - j = n - j + 1 by omega]
    have ha : -1 < (α + β + 2 * j + 1).re := by
      simp only [add_re, mul_re, re_ofNat, im_ofNat, natCast_re, natCast_im, mul_zero,
        sub_zero, add_zero, one_re]
      linarith [Nat.cast_nonneg (α := ℝ) j]
    have he : (∑ t ∈ Finset.range (n - j + 1), jacobiInverseCoeff α β n (j + t) *
        (poch (α + 1) (j + t) / (j + t).factorial *
          gaussHGCoeff (-((j + t : ℕ) : ℂ)) ((j + t : ℕ) + α + β + 1) (α + 1) j)) =
        (n.choose j : ℂ) * poch (α + j + 1) (n - j) *
          ∑ t ∈ Finset.range (n - j + 1), (-1 : ℂ) ^ t * ((n - j).choose t : ℂ) /
            (poch ((α + β + 2 * j + 1) + t) t *
              poch ((α + β + 2 * j + 1) + 2 * t + 1) (n - j - t)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      have htn : j + t ≤ n := by have := Finset.mem_range.mp ht; omega
      convert jacobiInverseCoeff_mul_gaussCoeff hα hβ n j t htn using 1 <;> congr 3 <;> ring
    rw [he, sum_choose_recip_poch ha]
    by_cases hj' : j = n
    · subst j
      simp [poch_zero]
    · have hr : n - j ≠ 0 := by omega
      simp [hj', hr]
  rw [hexpand]
  trans ∑ j ∈ Finset.range (n + 1), (if j = n then (1 : ℂ) else 0) * ((1 - x) / 2) ^ j
  · rw [Finset.sum_eq_single n]
    · simp
    · intro j hj hjn
      simp [hjn]
    · simp
  · symm
    apply Finset.sum_congr rfl
    intro j hj
    rw [hs j hj]


/-- A finite Jacobi coefficient multiplied by the inverse basis coefficient. -/
theorem jacobi_connection_coeff_term {α β γ δ : ℂ} (hα : -1 < α.re) (hβ : -1 < β.re)
    (hγ : -1 < γ.re) (n k j : ℕ) (hkj : k + j ≤ n) :
    (poch (γ + 1) n / n.factorial *
      gaussHGCoeff (-(n : ℂ)) (n + γ + δ + 1) (γ + 1) (k + j)) *
        jacobiInverseCoeff α β (k + j) k =
    (poch (n + γ + δ + 1) k * poch (k + γ + 1) (n - k) /
      ((n - k).factorial * poch (k + α + β + 1) k)) *
      (poch (-((n - k : ℕ) : ℂ)) j * poch (n + k + γ + δ + 1) j * poch (k + α + 1) j /
        (poch (k + γ + 1) j * poch (2 * k + α + β + 2) j * j.factorial)) := by
  have hkn : k ≤ n := by omega
  have hγnp : ∀ r : ℕ, γ + 1 ≠ -(r : ℂ) := not_neg_nat_of_re_pos (by simp; linarith)
  have hp (r : ℕ) : poch (γ + 1) r ≠ 0 := poch_ne_zero_of_not_neg_nat hγnp r
  have hpk (r : ℕ) : poch (γ + k + 1) r ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; linarith [Nat.cast_nonneg (α := ℝ) k])) r
  have hf (r : ℕ) : (r.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr r.factorial_ne_zero
  have hlead := jacobi_leading_poch_ne_zero hα hβ k
  have hshift : poch (α + β + 2 * k + 2) j ≠ 0 := by
    apply poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos ?_)
    simp only [add_re, mul_re, re_ofNat, im_ofNat, natCast_re, natCast_im, mul_zero, sub_zero]
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hγn : poch (γ + 1) n = poch (γ + 1) k * poch (γ + k + 1) (n - k) := by
    rw [show γ + k + 1 = γ + 1 + k by ring, ← poch_add, Nat.add_sub_of_le hkn]
  have hγkj : poch (γ + 1) (k + j) = poch (γ + 1) k * poch (γ + k + 1) j := by
    rw [poch_add]
    congr 2
    ring
  unfold gaussHGCoeff jacobiInverseCoeff
  rw [poch_add (-(n : ℂ)) k j, poch_add ((n : ℂ) + γ + δ + 1) k j,
    show -(n : ℂ) + k = -((n - k : ℕ) : ℂ) by rw [Nat.cast_sub hkn]; ring,
    DLMF.Gamma.poch_neg_nat_eq, ite_eq_left hkn, hγn, hγkj,
    Nat.add_sub_cancel_left,
    show (n : ℂ) + γ + δ + 1 + k = n + k + γ + δ + 1 by ring,
    show (k : ℂ) + γ + 1 = γ + k + 1 by ring,
    show (k : ℂ) + α + 1 = α + k + 1 by ring,
    show (k : ℂ) + α + β + 1 = α + β + k + 1 by ring,
    show 2 * (k : ℂ) + α + β + 2 = α + β + 2 * k + 2 by ring]
  have hsgn : ((-1 : ℂ) ^ k) ^ 2 = 1 := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
  field_simp [hp, hpk, hf, hlead, hshift]
  rw [hsgn, one_mul]


/-- Connection coefficients of Jacobi polynomials, AAR Lemma 7.1.1. -/
@[dlmf 18.18.iv]
theorem jacobiPolyP_connection {α β γ δ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (hδ : -1 < δ) (n : ℕ) (x : ℂ) :
    jacobiPolyP γ δ n x =
      ∑ k ∈ Finset.range (n + 1),
        (poch (n + (γ : ℂ) + δ + 1) k * poch (k + (γ : ℂ) + 1) (n - k) /
          ((n - k).factorial * poch (k + (α : ℂ) + β + 1) k)) *
        (∑ j ∈ Finset.range (n - k + 1),
          poch (-(n - k : ℕ) : ℂ) j * poch (n + k + (γ : ℂ) + δ + 1) j *
            poch (k + (α : ℂ) + 1) j /
            (poch (k + (γ : ℂ) + 1) j * poch (2 * k + (α : ℂ) + β + 2) j * j.factorial)) *
        jacobiPolyP α β k x := by
  have hα' : -1 < (α : ℂ).re := by simpa using hα
  have hβ' : -1 < (β : ℂ).re := by simpa using hβ
  have hγ' : -1 < (γ : ℂ).re := by simpa using hγ
  have he : jacobiPolyP γ δ n x = ∑ l ∈ Finset.range (n + 1),
      ∑ k ∈ Finset.range (l + 1),
        ((poch ((γ : ℂ) + 1) n / n.factorial *
          gaussHGCoeff (-(n : ℂ)) (n + (γ : ℂ) + δ + 1) (γ + 1) l) *
            jacobiInverseCoeff α β l k) * jacobiPolyP α β k x := by
    rw [jacobiPolyP, ordinaryHypergeometric_eq_sum_neg_nat, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    rw [jacobi_monomial_inverse hα' hβ', Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [he, Finset.sum_comm' (t' := Finset.range (n + 1)) (s' := fun k => Finset.Ico k (n + 1))
    (by intro l k; simp only [Finset.mem_range, Finset.mem_Ico]; omega)]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  rw [Finset.sum_Ico_eq_sum_range, show n + 1 - k = n - k + 1 by omega,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hkj : k + j ≤ n := by have := Finset.mem_range.mp hj; omega
  rw [jacobi_connection_coeff_term hα' hβ' hγ' n k j hkj]

/-- Coefficient recurrence for the Gegenbauer polynomials normalized at one. -/
private lemma ultrasphPoly_coeff_recurrence {lam : ℂ} (hlam : 0 < lam.re) (n k : ℕ) :
    (n + 1 + 2 * lam) * gaussHGCoeff (-(n + 2 : ℂ)) (n + 2 + 2 * lam)
        (lam + 1 / 2) (k + 1) -
      2 * (n + 1 + lam) * gaussHGCoeff (-(n + 1 : ℂ)) (n + 1 + 2 * lam)
        (lam + 1 / 2) (k + 1) +
      (n + 1) * gaussHGCoeff (-(n : ℂ)) (n + 2 * lam) (lam + 1 / 2) (k + 1) =
      -4 * (n + 1 + lam) * gaussHGCoeff (-(n + 1 : ℂ)) (n + 1 + 2 * lam)
        (lam + 1 / 2) k := by
  have hc : ∀ j : ℕ, lam + 1 / 2 ≠ -j := not_neg_nat_of_re_pos (by
    simp only [add_re, div_ofNat_re, one_re]; linarith)
  have hpk := poch_ne_zero_of_not_neg_nat hc k
  have hf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hk : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hck : lam + 1 / 2 + k ≠ 0 := by
    intro he
    apply hc k
    linear_combination he
  have hp : (n + 1 + 2 * lam) *
      (poch (-(n + 2 : ℂ)) (k + 1) * poch (n + 2 + 2 * lam) (k + 1)) =
      -(n + 2 : ℂ) * (n + 1 + 2 * lam + k) * (n + 2 + 2 * lam + k) *
        (poch (-(n + 1 : ℂ)) k * poch (n + 1 + 2 * lam) k) := by
    have h := poch_succ_left_mul (n + 1 + 2 * lam) (k + 1)
    rw [show (n : ℂ) + 1 + 2 * lam + 1 = n + 2 + 2 * lam by ring,
      poch_succ (n + 1 + 2 * lam) k] at h
    push_cast at h
    rw [poch_succ_left (-(n + 2 : ℂ)),
      show -(n + 2 : ℂ) + 1 = -(n + 1 : ℂ) by ring]
    linear_combination -(n + 2 : ℂ) * poch (-(n + 1 : ℂ)) k * h
  have hm : (n + 1 : ℂ) *
      (poch (-(n : ℂ)) (k + 1) * poch (n + 2 * lam) (k + 1)) =
      -(n + 2 * lam) * ((k : ℂ) - n - 1) * (k - n) *
        (poch (-(n + 1 : ℂ)) k * poch (n + 1 + 2 * lam) k) := by
    have h := poch_succ_left_mul (-(n + 1 : ℂ)) (k + 1)
    rw [show -(n + 1 : ℂ) + 1 = -(n : ℂ) by ring,
      poch_succ (-(n + 1 : ℂ)) k] at h
    push_cast at h
    rw [poch_succ_left (n + 2 * lam),
      show (n : ℂ) + 2 * lam + 1 = n + 1 + 2 * lam by ring]
    linear_combination -(n + 2 * lam) * poch (n + 1 + 2 * lam) k * h
  simp only [gaussHGCoeff, ← mul_div_assoc]
  rw [hp, hm, poch_succ (-(n + 1 : ℂ)), poch_succ (n + 1 + 2 * lam),
    poch_succ (lam + 1 / 2)]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  generalize hcdef : lam + 1 / 2 = c at hpk hck ⊢
  field_simp [hpk, hck, hf, hk]
  rw [← hcdef]
  ring

/-- Normalizing a Gegenbauer polynomial at one removes its Pochhammer prefactor. -/
theorem ultrasphPoly_div_at_one {lam : ℂ} (hlam : 0 < lam.re) (n : ℕ) (x : ℂ) :
    ultrasphPoly lam n x / ultrasphPoly lam n 1 =
      ₂F₁ (-(n : ℂ)) (n + 2 * lam) (lam + 1 / 2) ((1 - x) / 2) := by
  have hp : poch (2 * lam) n ≠ 0 := poch_ne_zero_of_not_neg_nat
    (not_neg_nat_of_re_pos (by simpa using mul_pos (by norm_num : (0 : ℝ) < 2) hlam)) n
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  simp only [ultrasphPoly, sub_self, zero_div, ordinaryHypergeometric_zero, mul_one]
  field_simp

/-- Three-term recurrence for the Gegenbauer polynomials normalized at one. -/
@[dlmf 18.9.T1]
theorem ultrasphPoly_normalized_recurrence {lam : ℂ} (hlam : 0 < lam.re) (n : ℕ) (x : ℂ) :
    (n + 1 + 2 * lam) * (ultrasphPoly lam (n + 2) x / ultrasphPoly lam (n + 2) 1) =
      2 * (n + 1 + lam) * x * (ultrasphPoly lam (n + 1) x / ultrasphPoly lam (n + 1) 1) -
        (n + 1) * (ultrasphPoly lam n x / ultrasphPoly lam n 1) := by
  let z := (1 - x) / 2
  let L (m k : ℕ) := gaussHGCoeff (-(m : ℂ)) (m + 2 * lam) (lam + 1 / 2) k
  let G (m : ℕ) := ultrasphPoly lam m x / ultrasphPoly lam m 1
  have hs (m : ℕ) : HasSum (fun k => L m k * z ^ k) (G m) := by
    dsimp only [G]
    rw [ultrasphPoly_div_at_one hlam, ordinaryHypergeometric_eq_sum_neg_nat]
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    have hmk : m < k := by simpa using hk
    simp [L, gaussHGCoeff, poch_neg_nat_eq_zero hmk]
  let d (k : ℕ) := (n + 1 + 2 * lam) * L (n + 2) k -
    2 * (n + 1 + lam) * L (n + 1) k + (n + 1) * L n k
  have hd0 : d 0 = 0 := by simp [d, L, gaussHGCoeff, poch_zero]; ring
  have hd (k : ℕ) : d (k + 1) = -4 * (n + 1 + lam) * L (n + 1) k := by
    dsimp [d, L]
    simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
      ultrasphPoly_coeff_recurrence hlam n k
  have hsum : HasSum (fun k => d k * z ^ k)
      ((n + 1 + 2 * lam) * G (n + 2) - 2 * (n + 1 + lam) * G (n + 1) +
        (n + 1) * G n) := by
    simpa only [d, sub_mul, add_mul, mul_assoc] using
      (((hs (n + 2)).mul_left (n + 1 + 2 * lam)).sub
        ((hs (n + 1)).mul_left (2 * (n + 1 + lam)))).add ((hs n).mul_left (n + 1 : ℂ))
  have hshift : HasSum (fun k => d (k + 1) * z ^ k) (-4 * (n + 1 + lam) * G (n + 1)) := by
    simpa only [hd, mul_assoc] using (hs (n + 1)).mul_left (-4 * (n + 1 + lam))
  have he := (hshift.mul_pow_shift hd0).unique hsum
  dsimp [z, G] at he
  linear_combination -he

/-- The normalized degree-one Gegenbauer polynomial is the identity function. -/
@[simp] theorem ultrasphPoly_normalized_one {lam : ℂ} (hlam : 0 < lam.re) (x : ℂ) :
    ultrasphPoly lam 1 x / ultrasphPoly lam 1 1 = x := by
  have hc : lam + 1 / 2 ≠ 0 := by
    intro he
    have hre := congrArg Complex.re he
    simp at hre
    linarith
  rw [ultrasphPoly_div_at_one hlam]
  have h := ordinaryHypergeometric_eq_sum_neg_nat 1 (1 + 2 * lam) (lam + 1 / 2) ((1 - x) / 2)
  norm_num only [Nat.cast_one] at h ⊢
  rw [h]
  norm_num [Finset.sum_range_succ, gaussHGCoeff, poch_succ, poch_zero]
  generalize hcdef : lam + 1 / 2 = c at hc ⊢
  field_simp
  rw [← hcdef]
  ring

/-- Turán's inequality for ultraspherical polynomials normalized at one
(AAR Exercise 6.23(b)). -/
@[dlmf 18.14.E11]
theorem turan_ultrasphPoly {lam : ℝ} (hlam : 0 < lam) {n : ℕ} (hn : n ≠ 0) {x : ℝ}
    (hx : |x| ≤ 1) :
    0 ≤ ((ultrasphPoly lam n x / ultrasphPoly lam n 1).re) ^ 2 -
      (ultrasphPoly lam (n - 1) x / ultrasphPoly lam (n - 1) 1).re *
        (ultrasphPoly lam (n + 1) x / ultrasphPoly lam (n + 1) 1).re := by
  let G (m : ℕ) := (ultrasphPoly lam m x / ultrasphPoly lam m 1).re
  have hl : 0 < (lam : ℂ).re := hlam
  have hG0 : G 0 = 1 := by simp [G]
  have hG1 : G 1 = x := by simp [G, ultrasphPoly_normalized_one hl]
  have hr (m : ℕ) : (m + 1 + 2 * lam) * G (m + 2) =
      2 * (m + 1 + lam) * x * G (m + 1) - (m + 1) * G m := by
    simpa [G, mul_re] using congrArg Complex.re (ultrasphPoly_normalized_recurrence hl m x)
  have hx2 : 0 ≤ 1 - x ^ 2 := by
    have := abs_le.mp hx
    nlinarith [sq_nonneg x]
  have hquad (u v : ℝ) : 0 ≤ u ^ 2 + v ^ 2 - 2 * x * u * v := by
    nlinarith [sq_nonneg (u - x * v), mul_nonneg hx2 (sq_nonneg v)]
  have hall : ∀ m : ℕ, 0 ≤ G (m + 1) ^ 2 - G m * G (m + 2) := by
    intro m
    induction m with
    | zero =>
      have hrec := hr 0
      norm_num [hG0, hG1] at hrec ⊢
      have hpos : 0 < 1 + 2 * lam := by linarith
      nlinarith
    | succ m ih =>
      have hrec := hr m
      have hrec' := hr (m + 1)
      simp only [Nat.cast_add, Nat.cast_one] at hrec'
      -- The difference of successive Turán determinants is a nonnegative quadratic form.
      have hstep : (m + 2 + 2 * lam) * (G (m + 2) ^ 2 - G (m + 1) * G (m + 3)) =
          (m + 1) * (G (m + 1) ^ 2 - G m * G (m + 2)) +
          (G (m + 2) ^ 2 + G (m + 1) ^ 2 - 2 * x * G (m + 2) * G (m + 1)) := by
        have hidx : m + 1 + 2 = m + 3 := by omega
        rw [hidx] at hrec'
        linear_combination -G (m + 1) * hrec' + G (m + 2) * hrec
      have hm : (0 : ℝ) ≤ m + 1 := by positivity
      have hpos : (0 : ℝ) < m + 2 + 2 * lam := by positivity
      have hnonneg := mul_nonneg hm ih
      have hq := hquad (G (m + 2)) (G (m + 1))
      have ht : 0 ≤ G (m + 2) ^ 2 - G (m + 1) * G (m + 3) := by
        apply nonneg_of_mul_nonneg_left (by rw [mul_comm, hstep]; linarith) hpos
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using ht
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simpa only [G, Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.add_assoc] using hall m

/-- Legendre polynomials are the normalized Gegenbauer family at `λ = 1/2`. -/
@[dlmf 18.7.E9]
theorem legendrePolyP_eq_normalized_ultrasphPoly (n : ℕ) (x : ℂ) :
    legendrePolyP n x = ultrasphPoly (1 / 2) n x / ultrasphPoly (1 / 2) n 1 := by
  rw [ultrasphPoly_div_at_one (by norm_num : 0 < (1 / 2 : ℂ).re)]
  norm_num [legendrePolyP, jacobiPolyP, Nat.cast_ne_zero.mpr n.factorial_ne_zero]

/-- The first Legendre polynomial. -/
@[simp, dlmf 18.5.E16]
theorem legendrePolyP_one (x : ℂ) : legendrePolyP 1 x = x := by
  rw [legendrePolyP_eq_normalized_ultrasphPoly,
    ultrasphPoly_normalized_one (by norm_num : 0 < (1 / 2 : ℂ).re)]

/-- The three-term recurrence for Legendre polynomials, including complex arguments. -/
@[dlmf 18.9.T1]
theorem legendrePolyP_recurrence (n : ℕ) (x : ℂ) :
    (n + 2 : ℂ) * legendrePolyP (n + 2) x =
      (2 * n + 3) * x * legendrePolyP (n + 1) x - (n + 1) * legendrePolyP n x := by
  simp_rw [legendrePolyP_eq_normalized_ultrasphPoly]
  have h := ultrasphPoly_normalized_recurrence (by norm_num : 0 < (1 / 2 : ℂ).re) n x
  convert h using 1 <;> ring

/-- Turán's inequality for Legendre polynomials (AAR Exercise 6.22):
`P_n(x)² - P_{n-1}(x) P_{n+1}(x) ≥ 0` on `[-1,1]`. -/
@[dlmf 18.14.E10]
theorem turan_legendre {n : ℕ} (hn : n ≠ 0) {x : ℝ} (hx : |x| ≤ 1) :
    0 ≤ (legendrePolyP n x).re ^ 2 -
      (legendrePolyP (n - 1) x).re * (legendrePolyP (n + 1) x).re := by
  simpa only [legendrePolyP_eq_normalized_ultrasphPoly, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat] using
    turan_ultrasphPoly (lam := 1 / 2) (by norm_num) hn hx

/-- Vietoris's inequality (AAR §7.3): the cosine polynomials with coefficients
`a_{2k} = a_{2k+1} = \binom{2k}{k} / 2^{2k}` are nonnegative. -/
theorem vietoris_inequality (n : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) (hθπ : θ ≤ π) :
    0 ≤ ∑ k ∈ Finset.range (n + 1),
      (Nat.choose (2 * (k / 2)) (k / 2) / (2 : ℝ) ^ (2 * (k / 2))) * Real.cos (k * θ) := by
  sorry

/-- Positivity of Cesàro sums of ultraspherical polynomials, AAR Corollary 7.6.4. -/
theorem ultrasphPoly_cesaro_nonneg {lam : ℝ} (hlam : 0 < lam) (n : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    0 ≤ (∑ k ∈ Finset.range (n + 1),
      poch (2 * (lam : ℂ)) (n - k) / (n - k).factorial * ultrasphPoly lam k x).re := by
  sorry

/-- Apéry's theorem: `ζ(3)` is irrational (AAR §7.7). -/
theorem irrational_riemannZeta_three : Irrational (riemannZeta 3).re := by
  sorry

end DLMF.OrthogonalPolynomials
