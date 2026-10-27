/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Absolutely convergent evaluation of integer power series

`r27_absEval P x s` says that the integer power series `P` converges absolutely at `x : ℂ`
with sum `s`. Absolutely convergent evaluation is multiplicative (Cauchy product,
`r27_absEval_mul`), so formal identities in `ℤ⟦X⟧` transfer to identities of complex
numbers. A series with bounded coefficients converges absolutely in the unit disc
(`r27_absEval_of_bounded`).
-/

@[expose] public noncomputable section

open PowerSeries Finset

/-- The integer power series `P` converges absolutely at `x` with sum `s`. -/
def r27_absEval (P : PowerSeries ℤ) (x s : ℂ) : Prop :=
  Summable (fun n ↦ ‖((coeff n P : ℤ) : ℂ) * x ^ n‖) ∧
    HasSum (fun n ↦ ((coeff n P : ℤ) : ℂ) * x ^ n) s

/-- The sum of an absolutely convergent evaluation is unique. -/
theorem r27_absEval_unique {P : PowerSeries ℤ} {x s t : ℂ} (hs : r27_absEval P x s)
    (ht : r27_absEval P x t) : s = t :=
  hs.2.unique ht.2

/-- Evaluation of `1`. -/
theorem r27_absEval_one (x : ℂ) : r27_absEval 1 x 1 := by
  have h : (fun n ↦ ((coeff n (1 : PowerSeries ℤ) : ℤ) : ℂ) * x ^ n) =
      fun n ↦ if n = 0 then 1 else 0 := by
    funext n; rcases n with _ | n <;> simp
  refine ⟨?_, ?_⟩
  · rw [show (fun n ↦ ‖((coeff n (1 : PowerSeries ℤ) : ℤ) : ℂ) * x ^ n‖) = fun n ↦
      ‖(if n = 0 then (1 : ℂ) else 0)‖ from funext fun n ↦ by rw [congrFun h n]]
    exact summable_of_ne_finset_zero (s := {0}) (by intro n hn; simp_all)
  · rw [h]; exact hasSum_ite_eq 0 1

/-- Evaluation of `X`. -/
theorem r27_absEval_X (x : ℂ) : r27_absEval X x x := by
  have h : (fun n ↦ ((coeff n (X : PowerSeries ℤ) : ℤ) : ℂ) * x ^ n) =
      fun n ↦ if n = 1 then x else 0 := by
    funext n; by_cases hn : n = 1 <;> simp [coeff_X, hn]
  refine ⟨?_, ?_⟩
  · rw [show (fun n ↦ ‖((coeff n (X : PowerSeries ℤ) : ℤ) : ℂ) * x ^ n‖) = fun n ↦
      ‖(if n = 1 then x else 0)‖ from funext fun n ↦ by rw [congrFun h n]]
    exact summable_of_ne_finset_zero (s := {1}) (by intro n hn; simp_all)
  · rw [h]; exact hasSum_ite_eq 1 x

/-- Absolutely convergent evaluation is multiplicative (Cauchy product). -/
theorem r27_absEval_mul {P Q : PowerSeries ℤ} {x s t : ℂ} (hP : r27_absEval P x s)
    (hQ : r27_absEval Q x t) : r27_absEval (P * Q) x (s * t) := by
  set f : ℕ → ℂ := fun n ↦ ((coeff n P : ℤ) : ℂ) * x ^ n
  set g : ℕ → ℂ := fun n ↦ ((coeff n Q : ℤ) : ℂ) * x ^ n
  have hfg : (fun n ↦ ((coeff n (P * Q) : ℤ) : ℂ) * x ^ n) =
      fun n ↦ ∑ kl ∈ antidiagonal n, f kl.1 * g kl.2 := by
    funext n
    rw [coeff_mul, Int.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl ↦ ?_
    rw [mem_antidiagonal] at hkl
    simp only [f, g, Int.cast_mul, ← hkl, pow_add]
    ring
  refine ⟨?_, ?_⟩
  · rw [show (fun n ↦ ‖((coeff n (P * Q) : ℤ) : ℂ) * x ^ n‖) = fun n ↦
      ‖∑ kl ∈ antidiagonal n, f kl.1 * g kl.2‖ from funext fun n ↦ by rw [congrFun hfg n]]
    exact summable_norm_sum_mul_antidiagonal_of_summable_norm hP.1 hQ.1
  · rw [hfg]
    have hsum := summable_norm_sum_mul_antidiagonal_of_summable_norm hP.1 hQ.1
    have h := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hP.1 hQ.1
    rw [hP.2.tsum_eq, hQ.2.tsum_eq] at h
    rw [h]
    exact hsum.of_norm.hasSum

/-- Evaluation of a power. -/
theorem r27_absEval_pow {P : PowerSeries ℤ} {x s : ℂ} (hP : r27_absEval P x s) (k : ℕ) :
    r27_absEval (P ^ k) x (s ^ k) := by
  induction k with
  | zero => simpa using r27_absEval_one x
  | succ k ih => rw [pow_succ, pow_succ]; exact r27_absEval_mul ih hP

/-- Evaluation of a negation. -/
lemma r27_absEval_neg {P : PowerSeries ℤ} {x s : ℂ} (hP : r27_absEval P x s) :
    r27_absEval (-P) x (-s) := by
  refine ⟨?_, ?_⟩
  · simpa using hP.1
  · simpa [neg_mul] using hP.2.neg

/-- Evaluation of a sum. -/
lemma r27_absEval_add {P Q : PowerSeries ℤ} {x s t : ℂ} (hP : r27_absEval P x s)
    (hQ : r27_absEval Q x t) : r27_absEval (P + Q) x (s + t) := by
  refine ⟨?_, ?_⟩
  · refine (hP.1.add hQ.1).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ ?_
    simp only [map_add, Int.cast_add, add_mul]
    exact norm_add_le _ _
  · simpa [add_mul] using hP.2.add hQ.2

/-- Evaluation of a difference. -/
lemma r27_absEval_sub {P Q : PowerSeries ℤ} {x s t : ℂ} (hP : r27_absEval P x s)
    (hQ : r27_absEval Q x t) : r27_absEval (P - Q) x (s - t) := by
  simpa [sub_eq_add_neg] using r27_absEval_add hP (r27_absEval_neg hQ)

/-- A power series with bounded coefficients converges absolutely in the unit disc. -/
theorem r27_absEval_of_bounded {P : PowerSeries ℤ} {C : ℝ} (hC : ∀ n, |((coeff n P : ℤ) : ℝ)| ≤ C)
    {x : ℂ} (hx : ‖x‖ < 1) : r27_absEval P x (∑' n, ((coeff n P : ℤ) : ℂ) * x ^ n) := by
  have hs : Summable (fun n ↦ ‖((coeff n P : ℤ) : ℂ) * x ^ n‖) := by
    refine ((summable_geometric_of_lt_one (norm_nonneg x) hx).mul_left C).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) fun n ↦ ?_
    rw [norm_mul, norm_pow, Complex.norm_intCast]
    exact mul_le_mul_of_nonneg_right (hC n) (by positivity)
  exact ⟨hs, hs.of_norm.hasSum⟩

/-- Evaluation of `1 - X ^ k`. -/
lemma r27_absEval_one_sub_X_pow (x : ℂ) (k : ℕ) :
    r27_absEval (1 - X ^ k) x (1 - x ^ k) :=
  r27_absEval_sub (r27_absEval_one x) (r27_absEval_pow (r27_absEval_X x) k)

/-- The geometric series `∑_{j ≥ 0} X^{kj} = 1/(1 - X^k)`. -/
def r27_geomSeries (k : ℕ) : PowerSeries ℤ := PowerSeries.mk fun n ↦ if k ∣ n then 1 else 0

/-- `(∑_j X^{kj}) (1 - X^k) = 1` for `k ≥ 1`. -/
theorem r27_geomSeries_mul {k : ℕ} (hk : 0 < k) : r27_geomSeries k * (1 - X ^ k) = 1 := by
  ext n
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow', r27_geomSeries, coeff_mk, coeff_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [show ¬ k ≤ 0 by omega]
  · split_ifs with h1 h2 h3 <;> simp_all
    · exact absurd (Nat.le_of_dvd hn h1) (by omega)
    · rename_i h2 _
      rcases eq_or_lt_of_le h2 with rfl | h
      · exact absurd dvd_rfl h1
      · exact h

/-- `∑_j x^{kj} = 1/(1 - x^k)`, absolutely, for `‖x‖ < 1` and `k ≥ 1`. -/
theorem r27_absEval_geomSeries {k : ℕ} (hk : 0 < k) {x : ℂ} (hx : ‖x‖ < 1) :
    r27_absEval (r27_geomSeries k) x (1 - x ^ k)⁻¹ := by
  have hb := r27_absEval_of_bounded (P := r27_geomSeries k) (C := 1)
    (fun n ↦ by simp only [r27_geomSeries, coeff_mk]; split_ifs <;> simp) hx
  have h1 := r27_absEval_mul hb (r27_absEval_one_sub_X_pow x k)
  rw [r27_geomSeries_mul hk] at h1
  have h2 := r27_absEval_unique h1 (r27_absEval_one x)
  rwa [eq_inv_of_mul_eq_one_left h2] at hb

/-- Evaluation of a finite product. -/
theorem r27_absEval_prod {ι : Type*} (s : Finset ι) {P : ι → PowerSeries ℤ} {x : ℂ}
    {v : ι → ℂ} (h : ∀ i ∈ s, r27_absEval (P i) x (v i)) :
    r27_absEval (∏ i ∈ s, P i) x (∏ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using r27_absEval_one x
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact r27_absEval_mul (h a (mem_insert_self a s))
      (ih fun i hi ↦ h i (mem_insert_of_mem hi))
