/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Convergent evaluation of integer power series

`PowerSeries.HasSumAt P x s` states that the series of monomials of `P : ℤ⟦X⟧` has
sum `s : ℂ` at `x`. Mathlib's `HasSum` implies absolute convergence for complex series,
so no separate norm-summability assumption is stored. The evaluation respects sums,
products and finite products, and bounded coefficients give convergence in the unit disc.

`PowerSeries.geomSeriesOnMultiples k` is the formal geometric series on degrees divisible
by `k`; its product identity and convergent evaluation support the partition generating
functions of DLMF Chapter 27. Multiplicativity uses Mathlib's absolutely convergent
Cauchy-product theorem.
-/

@[expose] public noncomputable section

open PowerSeries Finset

/-- The integer power series `P` converges absolutely at `x` with sum `s`. -/
def PowerSeries.HasSumAt (P : PowerSeries ℤ) (x s : ℂ) : Prop :=
  HasSum (fun n ↦ ((coeff n P : ℤ) : ℂ) * x ^ n) s

/-- The sum of an absolutely convergent evaluation is unique. -/
theorem PowerSeries.HasSumAt.unique {P : PowerSeries ℤ} {x s t : ℂ}
    (hs : PowerSeries.HasSumAt P x s)
    (ht : PowerSeries.HasSumAt P x t) : s = t :=
  HasSum.unique hs ht

/-- Evaluation of `1`. -/
theorem PowerSeries.hasSumAt_one (x : ℂ) : PowerSeries.HasSumAt 1 x 1 := by
  have h : (fun n ↦ ((coeff n (1 : PowerSeries ℤ) : ℤ) : ℂ) * x ^ n) =
      fun n ↦ if n = 0 then 1 else 0 := by
    funext n; rcases n with _ | n <;> simp
  simpa only [PowerSeries.HasSumAt, h] using hasSum_ite_eq 0 (1 : ℂ)

/-- The monomial series of `X` has sum `x` at `x`. -/
theorem PowerSeries.hasSumAt_X (x : ℂ) : PowerSeries.HasSumAt X x x := by
  have h : (fun n ↦ ((coeff n (X : PowerSeries ℤ) : ℤ) : ℂ) * x ^ n) =
      fun n ↦ if n = 1 then x else 0 := by
    funext n; by_cases hn : n = 1 <;> simp [coeff_X, hn]
  simpa only [PowerSeries.HasSumAt, h] using hasSum_ite_eq 1 x

/-- Absolutely convergent evaluation is multiplicative (Cauchy product). -/
theorem PowerSeries.HasSumAt.mul {P Q : PowerSeries ℤ} {x s t : ℂ} (hP : PowerSeries.HasSumAt P x s)
    (hQ : PowerSeries.HasSumAt Q x t) : PowerSeries.HasSumAt (P * Q) x (s * t) := by
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
  change HasSum _ _
  rw [hfg]
  have hPnorm := (show HasSum _ _ from hP).summable.norm
  have hQnorm := (show HasSum _ _ from hQ).summable.norm
  have hsum := summable_norm_sum_mul_antidiagonal_of_summable_norm hPnorm hQnorm
  have h := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hPnorm hQnorm
  rw [(show HasSum _ _ from hP).tsum_eq, (show HasSum _ _ from hQ).tsum_eq] at h
  rw [h]
  exact hsum.of_norm.hasSum

/-- Evaluation of a power. -/
theorem PowerSeries.HasSumAt.pow {P : PowerSeries ℤ} {x s : ℂ}
    (hP : PowerSeries.HasSumAt P x s) (k : ℕ) :
    PowerSeries.HasSumAt (P ^ k) x (s ^ k) := by
  induction k with
  | zero => simpa using PowerSeries.hasSumAt_one x
  | succ k ih => rw [pow_succ, pow_succ]; exact PowerSeries.HasSumAt.mul ih hP

/-- Evaluation of a negation. -/
lemma PowerSeries.HasSumAt.neg {P : PowerSeries ℤ} {x s : ℂ}
    (hP : PowerSeries.HasSumAt P x s) : PowerSeries.HasSumAt (-P) x (-s) := by
  simpa [PowerSeries.HasSumAt, neg_mul] using HasSum.neg hP

/-- Evaluation preserves addition of power series. -/
lemma PowerSeries.HasSumAt.add {P Q : PowerSeries ℤ} {x s t : ℂ}
    (hP : PowerSeries.HasSumAt P x s) (hQ : PowerSeries.HasSumAt Q x t) :
    PowerSeries.HasSumAt (P + Q) x (s + t) := by
  simpa [PowerSeries.HasSumAt, add_mul] using HasSum.add hP hQ

/-- Evaluation of a difference. -/
lemma PowerSeries.HasSumAt.sub {P Q : PowerSeries ℤ} {x s t : ℂ} (hP : PowerSeries.HasSumAt P x s)
    (hQ : PowerSeries.HasSumAt Q x t) : PowerSeries.HasSumAt (P - Q) x (s - t) := by
  simpa [sub_eq_add_neg] using PowerSeries.HasSumAt.add hP (PowerSeries.HasSumAt.neg hQ)

/-- A power series with bounded coefficients converges absolutely in the unit disc. -/
theorem PowerSeries.hasSumAt_of_bounded {P : PowerSeries ℤ} {C : ℝ}
    (hC : ∀ n, |((coeff n P : ℤ) : ℝ)| ≤ C)
    {x : ℂ} (hx : ‖x‖ < 1) : PowerSeries.HasSumAt P x (∑' n, ((coeff n P : ℤ) : ℂ) * x ^ n) := by
  have hs : Summable (fun n ↦ ‖((coeff n P : ℤ) : ℂ) * x ^ n‖) := by
    refine ((summable_geometric_of_lt_one (norm_nonneg x) hx).mul_left C).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) fun n ↦ ?_
    rw [norm_mul, norm_pow, Complex.norm_intCast]
    exact mul_le_mul_of_nonneg_right (hC n) (by positivity)
  exact hs.of_norm.hasSum

/-- Evaluation of `1 - X ^ k`. -/
lemma PowerSeries.hasSumAt_one_sub_X_pow (x : ℂ) (k : ℕ) :
    PowerSeries.HasSumAt (1 - X ^ k) x (1 - x ^ k) :=
  PowerSeries.HasSumAt.sub (PowerSeries.hasSumAt_one x)
    (PowerSeries.HasSumAt.pow (PowerSeries.hasSumAt_X x) k)

/-- The integer power series with coefficient `1` in degrees divisible by `k` and `0`
elsewhere. For positive `k` it is the geometric series `∑_{j ≥ 0} X^{kj}`; for `k = 0`
it is the constant series `1`. -/
def PowerSeries.geomSeriesOnMultiples (k : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n ↦ if k ∣ n then 1 else 0

/-- `(∑_j X^{kj}) (1 - X^k) = 1` for `k ≥ 1`. -/
theorem PowerSeries.geomSeriesOnMultiples_mul_one_sub_X_pow {k : ℕ} (hk : 0 < k) :
    PowerSeries.geomSeriesOnMultiples k * (1 - X ^ k) = 1 := by
  ext n
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow', PowerSeries.geomSeriesOnMultiples,
    coeff_mk, coeff_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [show ¬ k ≤ 0 by omega]
  · split_ifs with h1 h2 h3 <;> simp_all
    · exact absurd (Nat.le_of_dvd hn h1) (by omega)
    · rename_i h2 _
      rcases eq_or_lt_of_le h2 with rfl | h
      · exact absurd dvd_rfl h1
      · exact h

/-- `∑_j x^{kj} = 1/(1 - x^k)`, absolutely, for `‖x‖ < 1` and `k ≥ 1`. -/
theorem PowerSeries.hasSumAt_geomSeriesOnMultiples {k : ℕ} (hk : 0 < k) {x : ℂ} (hx : ‖x‖ < 1) :
    PowerSeries.HasSumAt (PowerSeries.geomSeriesOnMultiples k) x (1 - x ^ k)⁻¹ := by
  have hb := PowerSeries.hasSumAt_of_bounded (P := PowerSeries.geomSeriesOnMultiples k) (C := 1)
    (fun n ↦ by simp only [PowerSeries.geomSeriesOnMultiples, coeff_mk]; split_ifs <;> simp) hx
  have h1 := PowerSeries.HasSumAt.mul hb (PowerSeries.hasSumAt_one_sub_X_pow x k)
  rw [PowerSeries.geomSeriesOnMultiples_mul_one_sub_X_pow hk] at h1
  have h2 := PowerSeries.HasSumAt.unique h1 (PowerSeries.hasSumAt_one x)
  rwa [eq_inv_of_mul_eq_one_left h2] at hb

/-- Evaluation of a finite product. -/
theorem PowerSeries.HasSumAt.prod {ι : Type*} (s : Finset ι) {P : ι → PowerSeries ℤ} {x : ℂ}
    {v : ι → ℂ} (h : ∀ i ∈ s, PowerSeries.HasSumAt (P i) x (v i)) :
    PowerSeries.HasSumAt (∏ i ∈ s, P i) x (∏ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PowerSeries.hasSumAt_one x
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact PowerSeries.HasSumAt.mul (h a (mem_insert_self a s))
      (ih fun i hi ↦ h i (mem_insert_of_mem hi))
