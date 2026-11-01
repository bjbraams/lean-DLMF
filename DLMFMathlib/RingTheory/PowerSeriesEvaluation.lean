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
# Convergent evaluation of formal power series

For a formal power series `P` over a commutative semiring `R` and an `R`-algebra `A` that is
a normed ring, `PowerSeries.HasSumAt P x s` states that the monomial series
`∑ₙ algebraMap R A (coeff n P) * x ^ n` has sum `s`. The integer geometric series on degrees
divisible by `k` supports the partition generating functions of DLMF Chapter 27.

## Main definitions

* `PowerSeries.HasSumAt`: convergent evaluation of a power series at a point.
* `PowerSeries.geomSeriesOnMultiples`: the integer formal geometric series on degrees
  divisible by `k`.

## Main results

* `PowerSeries.HasSumAt.unique`, `PowerSeries.HasSumAt.add`, `PowerSeries.HasSumAt.neg`,
  `PowerSeries.HasSumAt.sub`: uniqueness and additivity of evaluation.
* `PowerSeries.HasSumAt.mul`, `PowerSeries.HasSumAt.pow`, `PowerSeries.HasSumAt.prod`:
  multiplicativity of evaluation (Cauchy product).
* `PowerSeries.hasSumAt_of_bounded`: bounded coefficients give absolute convergence in the
  open unit ball.
* `PowerSeries.geomSeriesOnMultiples_mul_one_sub_X_pow`,
  `PowerSeries.hasSumAt_geomSeriesOnMultiples`: `∑_j x^{kj} = 1/(1 - x^k)` for `‖x‖ < 1`
  and `k ≥ 1`.

## Implementation notes

Only `HasSum` is stored. Evaluation respects sums and differences in general. It respects
products, powers and finite products when `A` is a complete commutative normed ring that is
finite-dimensional over `ℝ` (for example `ℂ`), because there `HasSum` implies absolute
convergence; multiplicativity uses Mathlib's absolutely convergent Cauchy-product theorem.
-/

@[expose] public noncomputable section

open Finset

namespace PowerSeries

variable {R A : Type*}

section Semiring

variable [CommSemiring R] [NormedRing A] [Algebra R A]

/-- The monomial series of `P` evaluated at `x` has sum `s`: `∑ₙ (coeff n P) xⁿ = s`, with the
coefficients mapped into `A` by `algebraMap R A`. -/
def HasSumAt (P : PowerSeries R) (x s : A) : Prop :=
  HasSum (fun n ↦ algebraMap R A (coeff n P) * x ^ n) s

/-- For integer power series the coefficients enter through the integer cast. -/
theorem hasSumAt_int_iff {P : PowerSeries ℤ} {x s : A} :
    HasSumAt P x s ↔ HasSum (fun n ↦ ((coeff n P : ℤ) : A) * x ^ n) s := by
  simp only [HasSumAt, algebraMap_int_eq, eq_intCast]

/-- The sum of a convergent evaluation is unique. -/
theorem HasSumAt.unique {P : PowerSeries R} {x s t : A}
    (hs : HasSumAt P x s) (ht : HasSumAt P x t) : s = t :=
  HasSum.unique hs ht

/-- Evaluation of `1`. -/
theorem hasSumAt_one (x : A) : HasSumAt (1 : PowerSeries R) x 1 := by
  have h : (fun n ↦ algebraMap R A (coeff n (1 : PowerSeries R)) * x ^ n) =
      fun n ↦ if n = 0 then 1 else 0 := by
    funext n; rcases n with _ | n <;> simp [coeff_one]
  simpa only [HasSumAt, h] using hasSum_ite_eq 0 (1 : A)

/-- The monomial series of `X` has sum `x` at `x`. -/
theorem hasSumAt_X (x : A) : HasSumAt (X : PowerSeries R) x x := by
  have h : (fun n ↦ algebraMap R A (coeff n (X : PowerSeries R)) * x ^ n) =
      fun n ↦ if n = 1 then x else 0 := by
    funext n; by_cases hn : n = 1 <;> simp [coeff_X, hn]
  simpa only [HasSumAt, h] using hasSum_ite_eq 1 x

/-- Evaluation preserves addition of power series. -/
lemma HasSumAt.add {P Q : PowerSeries R} {x s t : A}
    (hP : HasSumAt P x s) (hQ : HasSumAt Q x t) : HasSumAt (P + Q) x (s + t) := by
  simpa [HasSumAt, add_mul] using HasSum.add hP hQ

/-- A power series with bounded coefficients converges absolutely in the open unit ball. -/
theorem hasSumAt_of_bounded [CompleteSpace A] [NormOneClass A] {P : PowerSeries R} {C : ℝ}
    (hC : ∀ n, ‖algebraMap R A (coeff n P)‖ ≤ C) {x : A} (hx : ‖x‖ < 1) :
    HasSumAt P x (∑' n, algebraMap R A (coeff n P) * x ^ n) := by
  have hs : Summable (fun n ↦ ‖algebraMap R A (coeff n P) * x ^ n‖) := by
    refine ((summable_geometric_of_lt_one (norm_nonneg x) hx).mul_left C).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) fun n ↦ ?_
    calc ‖algebraMap R A (coeff n P) * x ^ n‖
        ≤ ‖algebraMap R A (coeff n P)‖ * ‖x‖ ^ n :=
          (norm_mul_le _ _).trans (by gcongr; exact norm_pow_le x n)
      _ ≤ C * ‖x‖ ^ n := by gcongr; exact hC n
  exact hs.of_norm.hasSum

end Semiring

section Ring

variable [CommRing R] [NormedRing A] [Algebra R A]

/-- Evaluation of a negation. -/
lemma HasSumAt.neg {P : PowerSeries R} {x s : A}
    (hP : HasSumAt P x s) : HasSumAt (-P) x (-s) := by
  simpa [HasSumAt, neg_mul] using HasSum.neg hP

/-- Evaluation of a difference. -/
lemma HasSumAt.sub {P Q : PowerSeries R} {x s t : A} (hP : HasSumAt P x s)
    (hQ : HasSumAt Q x t) : HasSumAt (P - Q) x (s - t) := by
  simpa [sub_eq_add_neg] using hP.add hQ.neg

end Ring

section Multiplicative

variable [CommSemiring R] [NormedCommRing A] [Algebra R A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [CompleteSpace A]

/-- Evaluation is multiplicative (Cauchy product); in a finite-dimensional real normed space
`HasSum` implies absolute convergence. -/
theorem HasSumAt.mul {P Q : PowerSeries R} {x s t : A} (hP : HasSumAt P x s)
    (hQ : HasSumAt Q x t) : HasSumAt (P * Q) x (s * t) := by
  set f : ℕ → A := fun n ↦ algebraMap R A (coeff n P) * x ^ n
  set g : ℕ → A := fun n ↦ algebraMap R A (coeff n Q) * x ^ n
  have hfg : (fun n ↦ algebraMap R A (coeff n (P * Q)) * x ^ n) =
      fun n ↦ ∑ kl ∈ antidiagonal n, f kl.1 * g kl.2 := by
    funext n
    rw [coeff_mul, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl ↦ ?_
    rw [mem_antidiagonal] at hkl
    simp only [f, g, map_mul, ← hkl, pow_add]
    ring
  change HasSum _ _
  rw [hfg]
  have hPnorm := summable_norm_iff.mpr (show HasSum _ _ from hP).summable
  have hQnorm := summable_norm_iff.mpr (show HasSum _ _ from hQ).summable
  have hsum := summable_norm_sum_mul_antidiagonal_of_summable_norm hPnorm hQnorm
  have h := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hPnorm hQnorm
  rw [(show HasSum _ _ from hP).tsum_eq, (show HasSum _ _ from hQ).tsum_eq] at h
  rw [h]
  exact hsum.of_norm.hasSum

/-- Evaluation of a power. -/
theorem HasSumAt.pow {P : PowerSeries R} {x s : A} (hP : HasSumAt P x s) (k : ℕ) :
    HasSumAt (P ^ k) x (s ^ k) := by
  induction k with
  | zero => simpa using hasSumAt_one (R := R) x
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul hP

/-- Evaluation of a finite product. -/
theorem HasSumAt.prod {ι : Type*} (s : Finset ι) {P : ι → PowerSeries R} {x : A}
    {v : ι → A} (h : ∀ i ∈ s, HasSumAt (P i) x (v i)) :
    HasSumAt (∏ i ∈ s, P i) x (∏ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasSumAt_one (R := R) x
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact (h a (mem_insert_self a s)).mul (ih fun i hi ↦ h i (mem_insert_of_mem hi))

end Multiplicative

/-- Evaluation of `1 - X ^ k`. -/
lemma hasSumAt_one_sub_X_pow [CommRing R] [NormedCommRing A] [Algebra R A] [NormedSpace ℝ A]
    [FiniteDimensional ℝ A] [CompleteSpace A] (x : A) (k : ℕ) :
    HasSumAt (1 - X ^ k : PowerSeries R) x (1 - x ^ k) :=
  (hasSumAt_one x).sub ((hasSumAt_X x).pow k)

/-- The integer power series with coefficient `1` in degrees divisible by `k` and `0`
elsewhere. For positive `k` it is the geometric series `∑_{j ≥ 0} X^{kj}`; for `k = 0`
it is the constant series `1`. -/
def geomSeriesOnMultiples (k : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n ↦ if k ∣ n then 1 else 0

/-- `(∑_j X^{kj}) (1 - X^k) = 1` for `k ≥ 1`. -/
theorem geomSeriesOnMultiples_mul_one_sub_X_pow {k : ℕ} (hk : 0 < k) :
    geomSeriesOnMultiples k * (1 - X ^ k) = 1 := by
  ext n
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow', geomSeriesOnMultiples,
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
theorem hasSumAt_geomSeriesOnMultiples {k : ℕ} (hk : 0 < k) {x : ℂ} (hx : ‖x‖ < 1) :
    HasSumAt (geomSeriesOnMultiples k) x (1 - x ^ k)⁻¹ := by
  have hb := hasSumAt_of_bounded (P := geomSeriesOnMultiples k) (C := 1)
    (fun n ↦ by simp only [geomSeriesOnMultiples, coeff_mk]; split_ifs <;> simp) hx
  have h1 := hb.mul (hasSumAt_one_sub_X_pow x k)
  rw [geomSeriesOnMultiples_mul_one_sub_X_pow hk] at h1
  have h2 := h1.unique (hasSumAt_one x)
  rwa [eq_inv_of_mul_eq_one_left h2] at hb

end PowerSeries
