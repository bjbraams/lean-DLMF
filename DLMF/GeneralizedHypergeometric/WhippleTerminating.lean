/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Basic.ParametersAndSeries
public import DLMF.Hypergeometric.Basic.Pochhammer

/-!
# Whipple's terminating `₃F₂(1)` sum

This file proves the terminating form of Whipple's sum, DLMF 16.4.8,
`₃F₂(-n, a, 1 - a; d, 1 - d - 2n; 1) = (½(a+d))ₙ (½(d-a+1))ₙ / ((½d)ₙ (½(d+1))ₙ)`,
for lower parameters off the nonpositive integers.

## Main results

* `generalizedHypergeometricTruncated_whipple_sum`: Whipple's terminating sum, DLMF 16.4.8.

## Implementation notes

The series is not in the Sheppard orbit of a summable `₃F₂(1)`. The proof is by the
Wilf–Zeilberger method: the terms `c m k` of the series of length `m` satisfy
`(d+2m)(d+2m+1) c (m+1) k - (a+d+2m)(d-a+1+2m) c m k = W m (k+1) - W m k` with an explicit
certificate `W`, so the sums satisfy a first-order recurrence in `m`.
-/

@[expose] public noncomputable section

open Finset

namespace DLMF.Hypergeometric

/-- The Wilf–Zeilberger certificate for Whipple's terminating sum. -/
private def whippleWZ (a d : ℂ) (m k : ℕ) : ℂ :=
  -((k : ℂ) * (k + d - 1) * (k - d - 2 * m)) * pochhammer (-(m : ℂ)) (k - 1) * pochhammer a k *
    pochhammer (1 - a) k / (pochhammer (1 - d - 2 * m) k * pochhammer d k * k.factorial)

private lemma whipple_wz_step (a d : ℂ) (m k : ℕ) (hd : ∀ j : ℕ, d ≠ -j)
    (hL : ∀ j : ℕ, 1 - d - 2 * (m : ℂ) ≠ -j) (hM : ∀ j : ℕ, 1 - d - 2 * ((m : ℂ) + 1) ≠ -j) :
    (d + 2 * m) * (d + 2 * m + 1) *
        generalizedHypergeometricCoeff {-((m : ℂ) + 1), a, 1 - a} {d, 1 - d - 2 * ((m : ℂ) + 1)} k -
      (a + d + 2 * m) * (d - a + 1 + 2 * m) *
          generalizedHypergeometricCoeff {-(m : ℂ), a, 1 - a} {d, 1 - d - 2 * m} k =
    whippleWZ a d m (k + 1) - whippleWZ a d m k := by
  have hMeq : ∀ k : ℕ, pochhammer (1 - d - 2 * ((m : ℂ) + 1)) k =
      (-1 - d - 2 * m) * (-d - 2 * m) * pochhammer (1 - d - 2 * m) k /
        ((k - 1 - d - 2 * m) * (k - d - 2 * m)) := by
    intro k
    have h1 : (k : ℂ) - 1 - d - 2 * m ≠ 0 := by
      have := hM k; contrapose! this; linear_combination this
    have h2 : (k : ℂ) - d - 2 * m ≠ 0 := by
      have := hM (k + 1); contrapose! this; push_cast; linear_combination this
    rw [eq_div_iff (mul_ne_zero h1 h2)]
    set x : ℂ := 1 - d - 2 * ((m : ℂ) + 1) with hx
    have A : pochhammer x (k + 2) = pochhammer x k * (x + k) * (x + (k + 1)) := by
      rw [pochhammer_succ, pochhammer_succ]; push_cast; ring
    have B : pochhammer x (k + 2) = x * ((x + 1) * pochhammer (x + 1 + 1) k) := by
      rw [pochhammer_succ_left, pochhammer_succ_left]
    rw [show x + 1 + 1 = 1 - d - 2 * m by rw [hx]; ring] at B
    rw [hx] at A B ⊢
    linear_combination A.symm.trans B
  have hdk : ∀ k : ℕ, pochhammer d k ≠ 0 := pochhammer_ne_zero_of_not_neg_nat hd
  have hLk : ∀ k : ℕ, pochhammer (1 - d - 2 * (m : ℂ)) k ≠ 0 := pochhammer_ne_zero_of_not_neg_nat hL
  simp only [generalizedHypergeometricCoeff, pochhammerProduct, Multiset.insert_eq_cons,
      Multiset.map_cons, Multiset.map_singleton,
    Multiset.prod_cons, Multiset.prod_singleton, whippleWZ]
  rcases k with _ | j
  · have h0 : d ≠ 0 := by simpa using hd 0
    have h1 : 1 - d - 2 * (m : ℂ) ≠ 0 := by simpa using hL 0
    simp only [pochhammer_zero, pochhammer_one, Nat.factorial, CharP.cast_eq_zero,
        Nat.cast_one, zero_add,
      Nat.zero_sub]
    field_simp
    norm_num [pochhammer_zero]
    ring
  · have e1 : pochhammer (-((m : ℂ) + 1)) (j + 1) = -((m : ℂ) + 1) * pochhammer (-(m : ℂ)) j := by
      rw [pochhammer_succ_left]; congr 2; ring
    have e2 : pochhammer (-(m : ℂ)) (j + 1) = pochhammer (-(m : ℂ)) j * (-(m : ℂ) + j) :=
        pochhammer_succ _ _
    have s2 : ∀ x : ℂ, pochhammer x (j + 1 + 1) = pochhammer x (j + 1) * (x + (j + 1)) := by
      intro x; rw [pochhammer_succ]; push_cast; ring
    have hM1 := hMeq (j + 1)
    have hd1 : d + ((j : ℂ) + 1) ≠ 0 := by
      have := hd (j + 1); contrapose! this; push_cast; linear_combination this
    have hL1 : 1 - d - 2 * (m : ℂ) + ((j : ℂ) + 1) ≠ 0 := by
      have := hL (j + 1); contrapose! this; push_cast; linear_combination this
    have hA : ((j + 1 : ℕ) : ℂ) - 1 - d - 2 * m ≠ 0 := by
      have := hM (j + 1); contrapose! this; push_cast at this ⊢; linear_combination this
    have hB : ((j + 1 : ℕ) : ℂ) - d - 2 * m ≠ 0 := by
      have := hM (j + 2); contrapose! this; push_cast at this ⊢; linear_combination this
    have hdj := hdk (j + 1)
    have hLj := hLk (j + 1)
    rw [Nat.add_sub_cancel, Nat.add_sub_cancel, s2 a, s2 (1 - a), s2 (1 - d - 2 * (m : ℂ)),
      s2 d, e1, e2, hM1, Nat.factorial_succ (j + 1)]
    have hC : -1 - d - 2 * (m : ℂ) ≠ 0 := by
      have := hM 0; contrapose! this; push_cast; linear_combination this
    have hD : -d - 2 * (m : ℂ) ≠ 0 := by
      have := hM 1; contrapose! this; push_cast; linear_combination this
    push_cast at hA hB hd1 hL1 ⊢
    clear hMeq hM1 e1 e2 s2 hd hL hM hdk hLk
    have hf : ((j + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast (j + 1).factorial_ne_zero
    have h2 : (j : ℂ) + 1 + 1 ≠ 0 := by norm_cast
    generalize ((j + 1).factorial : ℂ) = F at hf ⊢
    generalize pochhammer a (j + 1) = PA
    generalize pochhammer (1 - a) (j + 1) = PB
    generalize pochhammer (-(m : ℂ)) j = PM
    generalize pochhammer d (j + 1) = PD at hdj ⊢
    generalize pochhammer (1 - d - 2 * (m : ℂ)) (j + 1) = PL at hLj ⊢
    generalize (m : ℂ) = M at *
    generalize (j : ℂ) = J at *
    have hA' : J - d - 2 * M ≠ 0 := by contrapose! hA; linear_combination hA
    have hB' : J + 1 - d - 2 * M ≠ 0 := hB
    clear hA
    rw [show J + 1 - 1 - d - 2 * M = J - d - 2 * M by ring]
    field_simp
    ring


/-- Regularity of `1 - d - 2m` for `m ≤ n` follows from regularity of `1 - d - 2n`. -/
private lemma whipple_regular_of_le {d : ℂ} {n m : ℕ} (hn : ∀ j : ℕ, 1 - d - 2 * (n : ℂ) ≠ -j)
    (hm : m ≤ n) (j : ℕ) : 1 - d - 2 * (m : ℂ) ≠ -j := by
  intro h
  apply hn (j + 2 * (n - m))
  push_cast [hm]
  linear_combination h

/-- The terms of index `m + 1` of the series of length `m` vanish. -/
private lemma whipple_coeff_top (a d : ℂ) (m : ℕ) :
    generalizedHypergeometricCoeff {-(m : ℂ), a, 1 - a} {d, 1 - d - 2 * m} (m + 1) = 0 := by
  simp [generalizedHypergeometricCoeff, pochhammerProduct,
      pochhammer_neg_nat_eq_zero (Nat.lt_succ_self m)]

/-- The first-order recurrence of Whipple's terminating sums. -/
private lemma whipple_sum_recurrence (a d : ℂ) (m : ℕ) (hd : ∀ j : ℕ, d ≠ -j)
    (hL : ∀ j : ℕ, 1 - d - 2 * (m : ℂ) ≠ -j) (hM : ∀ j : ℕ, 1 - d - 2 * ((m : ℂ) + 1) ≠ -j) :
    (d + 2 * m) * (d + 2 * m + 1) *
        ∑ k ∈ range (m + 2),
            generalizedHypergeometricCoeff {-((m : ℂ) + 1), a, 1 - a}
            {d, 1 - d - 2 * ((m : ℂ) + 1)} k =
      (a + d + 2 * m) * (d - a + 1 + 2 * m) *
        ∑ k ∈ range (m + 1),
            generalizedHypergeometricCoeff {-(m : ℂ), a, 1 - a} {d, 1 - d - 2 * m} k := by
  rw [show ∑ k ∈ range (m + 1),
      generalizedHypergeometricCoeff {-(m : ℂ), a, 1 - a} {d, 1 - d - 2 * m} k =
      ∑ k ∈ range (m + 2),
          generalizedHypergeometricCoeff {-(m : ℂ), a, 1 - a} {d, 1 - d - 2 * m} k by
    rw [sum_range_succ (n := m + 1), whipple_coeff_top, add_zero]]
  rw [← sub_eq_zero, mul_sum, mul_sum, ← sum_sub_distrib]
  simp_rw [whipple_wz_step a d m _ hd hL hM]
  rw [sum_range_sub]
  have h0 : whippleWZ a d m 0 = 0 := by simp [whippleWZ]
  have htop : whippleWZ a d m (m + 2) = 0 := by
    simp [whippleWZ, pochhammer_neg_nat_eq_zero (Nat.lt_succ_self m)]
  rw [h0, htop, sub_zero]

/-- Whipple's terminating sum, DLMF 16.4.8:
`₃F₂(-n, a, 1 - a; d, 1 - d - 2n; 1) = (½(a+d))ₙ (½(d-a+1))ₙ / ((½d)ₙ (½(d+1))ₙ)`,
for lower parameters `d` and `1 - d - 2n` off the nonpositive integers. -/
theorem generalizedHypergeometricTruncated_whipple_sum (n : ℕ) (a d : ℂ)
    (hb : LowerParametersRegular {d, 1 - d - 2 * n}) :
    generalizedHypergeometricTruncated n {(-n : ℂ), a, 1 - a} {d, 1 - d - 2 * n} 1 =
      pochhammer ((a + d) / 2) n * pochhammer ((d - a + 1) / 2) n /
        (pochhammer (d / 2) n * pochhammer ((d + 1) / 2) n) := by
  have hd : ∀ j : ℕ, d ≠ -j := hb d (by simp)
  have hn : ∀ j : ℕ, 1 - d - 2 * (n : ℂ) ≠ -j := hb _ (by simp)
  have hd2 : ∀ j : ℕ, d / 2 ≠ -j := by
    intro j h; apply hd (2 * j); push_cast; linear_combination 2 * h
  have hd3 : ∀ j : ℕ, (d + 1) / 2 ≠ -j := by
    intro j h; apply hd (2 * j + 1); push_cast; linear_combination 2 * h
  simp only [generalizedHypergeometricTruncated, one_pow, mul_one]
  suffices H : ∀ m ≤ n, ∑ k ∈ range (m + 1),
      generalizedHypergeometricCoeff {-(m : ℂ), a, 1 - a} {d, 1 - d - 2 * m} k =
      pochhammer ((a + d) / 2) m * pochhammer ((d - a + 1) / 2) m /
        (pochhammer (d / 2) m * pochhammer ((d + 1) / 2) m) from H n le_rfl
  intro m
  induction m with
  | zero => intro _; simp [generalizedHypergeometricCoeff, pochhammerProduct, pochhammer_zero]
  | succ m ih =>
    intro hm
    have hL := whipple_regular_of_le hn (Nat.le_of_succ_le hm)
    have hM : ∀ j : ℕ, 1 - d - 2 * ((m : ℂ) + 1) ≠ -j := by
      have := whipple_regular_of_le hn hm; push_cast at this; exact this
    have R := whipple_sum_recurrence a d m hd hL hM
    rw [ih (Nat.le_of_succ_le hm)] at R
    have h1 : d + 2 * (m : ℂ) ≠ 0 := by
      have := hd (2 * m); contrapose! this; push_cast; linear_combination this
    have h2 : d + 2 * (m : ℂ) + 1 ≠ 0 := by
      have := hd (2 * m + 1); contrapose! this; push_cast; linear_combination this
    have p1 := pochhammer_ne_zero_of_not_neg_nat hd2 m
    have p2 := pochhammer_ne_zero_of_not_neg_nat hd3 m
    push_cast
    rw [pochhammer_succ, pochhammer_succ, pochhammer_succ, pochhammer_succ]
    rw [show ∑ k ∈ range (m + 1 + 1),
        generalizedHypergeometricCoeff {-((m : ℂ) + 1), a, 1 - a} {d, 1 - d - 2 * ((m : ℂ) + 1)} k =
      (a + d + 2 * m) * (d - a + 1 + 2 * m) *
        (pochhammer ((a + d) / 2) m * pochhammer ((d - a + 1) / 2) m /
          (pochhammer (d / 2) m * pochhammer ((d + 1) / 2) m)) / ((d + 2 * m) * (d + 2 * m + 1)) by
      rw [eq_div_iff (mul_ne_zero h1 h2), ← R]; ring]
    have h3 : d / 2 + (m : ℂ) ≠ 0 := by
      contrapose! h1; linear_combination 2 * h1
    have h4 : (d + 1) / 2 + (m : ℂ) ≠ 0 := by
      contrapose! h2; linear_combination 2 * h2
    generalize pochhammer ((a + d) / 2) m = P1
    generalize pochhammer ((d - a + 1) / 2) m = P2
    generalize pochhammer (d / 2) m = Q1 at p1 ⊢
    generalize pochhammer ((d + 1) / 2) m = Q2 at p2 ⊢
    rw [div_eq_div_iff (mul_ne_zero h1 h2) (by simp [*])]
    field_simp
    ring

end DLMF.Hypergeometric
