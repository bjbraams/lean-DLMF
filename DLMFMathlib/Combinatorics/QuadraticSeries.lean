/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Combinatorics.Enumerative.Schroder
public import Mathlib.Tactic.LinearCombination

/-!
# Quadratic generating series built on the Catalan series

Over `ℚ`, with `C(X) = ∑ C(n) Xⁿ` the Catalan series (`C = 1 + X C²`), the series
`F_{a,e} = (1 - aX)⁻¹ C(X^e (1 - aX)⁻²)` (formal substitution, Mathlib `PowerSeries.subst`)
is the unique power series solution of `F = 1 + aXF + X^e F²` (`e ≥ 1`). Its coefficients
are `∑_k C(k) C(n, 2k) a^{n-2k}` for `e = 2` and `∑_k C(k) C(n+k, 2k) a^{n-k}` for `e = 1`.

## Main definitions

* `PowerSeries.catalanSeriesRat`: the Catalan generating series over `ℚ`.
* `PowerSeries.geometricSeries`: the geometric series `∑ aⁿ Xⁿ = 1/(1 - aX)`.
* `PowerSeries.quadraticSubstArg`: the substituted argument `X^e (1 - aX)^{-2}`.
* `PowerSeries.catalanQuadraticSeries`: the series `F_{a,e}`.

## Main results

* `PowerSeries.catalanQuadraticSeries_eq`, `PowerSeries.eq_of_quadratic_eq`: `F_{a,e}`
  satisfies `F = 1 + aXF + X^e F²` and is its unique solution.
* `PowerSeries.coeff_catalanQuadraticSeries_two`: the coefficients for `e = 2`.
* `catalan_succ_eq_sum_catalan_mul_choose_mul_two_pow`: Touchard's identity
  `C(n+1) = ∑_k C(k) C(n, 2k) 2^{n-2k}`.
* `Nat.largeSchroder_eq_sum_catalan_mul_choose`: the large Schröder numbers
  `r(n) = ∑_k C(k) C(n+k, 2k)`.
* `Nat.sum_range_choose_mul_choose_eq`: `∑_k C(n, k) C(k, m) = C(n, m) 2^{n-m}`.
* `Int.binomial_inversion`: binomial inversion.
-/

@[expose] public section

open Finset PowerSeries

noncomputable section

/-- The Catalan generating series `∑ C(n) Xⁿ` over `ℚ`. -/
noncomputable def PowerSeries.catalanSeriesRat : ℚ⟦X⟧ := mk fun n => (catalan n : ℚ)

/-- Identity under the stated parameter and domain assumptions: `PowerSeries.catalanSeriesRat = 1 + X *
PowerSeries.catalanSeriesRat ^ 2`. -/
private lemma PowerSeries.catalanSeriesRat_eq : PowerSeries.catalanSeriesRat = 1 + X * PowerSeries.catalanSeriesRat ^ 2 := by
  ext n
  rcases n with _ | n
  · simp [PowerSeries.catalanSeriesRat]
  · rw [map_add, coeff_succ_X_mul, pow_two, coeff_mul]
    simp [PowerSeries.catalanSeriesRat, catalan_succ']

/-- The geometric series `∑ aⁿ Xⁿ = 1/(1 - aX)`. -/
noncomputable def PowerSeries.geometricSeries (a : ℚ) : ℚ⟦X⟧ := rescale a (mk 1)

/-- Identity under the stated parameter and domain assumptions: `PowerSeries.geometricSeries a * (1 - C a * X) = 1`. -/
private lemma PowerSeries.geometricSeries_mul_one_sub_C_mul_X (a : ℚ) : PowerSeries.geometricSeries a * (1 - C a * X) = 1 := by
  have := congrArg (rescale a) (mk_one_mul_one_sub_eq_one (S := ℚ))
  rwa [map_mul, map_sub, map_one, rescale_X] at this

/-- Identity under the stated parameter and domain assumptions: `coeff n (PowerSeries.geometricSeries a ^ (d + 1)) =
a ^ n * (d + n).choose d`. -/
private lemma PowerSeries.coeff_geometricSeries_pow_succ (a : ℚ) (d n : ℕ) :
    coeff n (PowerSeries.geometricSeries a ^ (d + 1)) = a ^ n * (d + n).choose d := by
  rw [PowerSeries.geometricSeries, ← map_pow, mk_one_pow_eq_mk_choose_add, rescale_mk, coeff_mk]

/-- Identity under the stated parameter and domain assumptions: `constantCoeff (PowerSeries.geometricSeries a) = 1`. -/
private lemma PowerSeries.constantCoeff_geometricSeries (a : ℚ) : constantCoeff (PowerSeries.geometricSeries a) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.geometricSeries, rescale_mk, coeff_mk]; simp

/-- The substituted argument `q = X^e (1 - aX)^{-2}`. -/
noncomputable def PowerSeries.quadraticSubstArg (a : ℚ) (e : ℕ) : ℚ⟦X⟧ := X ^ e * PowerSeries.geometricSeries a ^ 2

/-- The stated relation follows from the given hypotheses: `HasSubst (PowerSeries.quadraticSubstArg a e)`. -/
private lemma PowerSeries.hasSubst_quadraticSubstArg (a : ℚ) {e : ℕ} (he : 1 ≤ e) : HasSubst (PowerSeries.quadraticSubstArg a e) :=
  HasSubst.of_constantCoeff_zero' (by
    simp [PowerSeries.quadraticSubstArg, zero_pow (by omega : e ≠ 0)])

/-- `F = (1 - aX)⁻¹ C(X^e (1 - aX)^{-2})`. -/
noncomputable def PowerSeries.catalanQuadraticSeries (a : ℚ) (e : ℕ) : ℚ⟦X⟧ :=
  PowerSeries.geometricSeries a * subst (PowerSeries.quadraticSubstArg a e) PowerSeries.catalanSeriesRat

/-- Identity under the stated parameter and domain assumptions: `PowerSeries.catalanQuadraticSeries a e = 1 + C a * X
* PowerSeries.catalanQuadraticSeries a e + X ^ e * PowerSeries.catalanQuadraticSeries a e ^ 2`. -/
theorem PowerSeries.catalanQuadraticSeries_eq (a : ℚ) {e : ℕ} (he : 1 ≤ e) :
    PowerSeries.catalanQuadraticSeries a e =
      1 + C a * X * PowerSeries.catalanQuadraticSeries a e + X ^ e * PowerSeries.catalanQuadraticSeries a e ^ 2 := by
  have hs := PowerSeries.hasSubst_quadraticSubstArg a he
  have hD : subst (PowerSeries.quadraticSubstArg a e) PowerSeries.catalanSeriesRat =
      1 + PowerSeries.quadraticSubstArg a e * subst (PowerSeries.quadraticSubstArg a e) PowerSeries.catalanSeriesRat ^ 2 := by
    conv_lhs => rw [PowerSeries.catalanSeriesRat_eq]
    rw [← coe_substAlgHom hs, map_add, map_one, map_mul, map_pow, substAlgHom_X]
  have hg := PowerSeries.geometricSeries_mul_one_sub_C_mul_X a
  simp only [PowerSeries.catalanQuadraticSeries, PowerSeries.quadraticSubstArg] at hD ⊢
  linear_combination (subst (X ^ e * PowerSeries.geometricSeries a ^ 2) PowerSeries.catalanSeriesRat) * hg + hD

/-- Uniqueness of the power series solution of `F = 1 + aXF + X^e F²`. -/
theorem PowerSeries.eq_of_quadratic_eq (a : ℚ) {e : ℕ} (he : 1 ≤ e) {F G : ℚ⟦X⟧}
    (hF : F = 1 + C a * X * F + X ^ e * F ^ 2) (hG : G = 1 + C a * X * G + X ^ e * G ^ 2) :
    F = G := by
  have h : (F - G) * (1 - C a * X - X ^ e * (F + G)) = 0 := by
    linear_combination hF - hG
  rcases mul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have := congrArg constantCoeff h
    simp [zero_pow (by omega : e ≠ 0)] at this

/-- Formula under the stated hypotheses: `coeff n (subst q f) = ∑ k ∈ range N, coeff k f * coeff n
(q ^ k)`. -/
private lemma PowerSeries.coeff_subst_eq_sum_range (q : ℚ⟦X⟧) (hq : constantCoeff q = 0) (f : ℚ⟦X⟧) {n N : ℕ}
    (hN : n < N) : coeff n (subst q f) = ∑ k ∈ range N, coeff k f * coeff n (q ^ k) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hq)]
  rw [finsum_eq_sum_of_support_subset _ (s := range N)]
  · simp [smul_eq_mul]
  · intro k hk
    simp only [Function.mem_support, ne_eq, coe_range, Set.mem_Iio] at hk ⊢
    by_contra hkn
    apply hk
    have : X ^ k ∣ q ^ k := pow_dvd_pow_of_dvd (X_dvd_iff.mpr hq) k
    rw [X_pow_dvd_iff] at this
    rw [this n (by omega), smul_zero]

/-- Coefficients of `g · f(q)` for a power series `g` and `q` without constant term. -/
private lemma PowerSeries.coeff_mul_subst_eq_sum_range (g q : ℚ⟦X⟧) (hq : constantCoeff q = 0) (f : ℚ⟦X⟧) (n : ℕ) :
    coeff n (g * subst q f) = ∑ k ∈ range (n + 1), coeff k f * coeff n (g * q ^ k) := by
  set P : ℚ⟦X⟧ := ∑ k ∈ range (n + 1), C (coeff k f) * q ^ k
  have hdvd : X ^ (n + 1) ∣ subst q f - P := by
    rw [X_pow_dvd_iff]
    intro m hm
    rw [map_sub, PowerSeries.coeff_subst_eq_sum_range q hq f hm, map_sum]
    simp [coeff_C_mul]
  obtain ⟨R, hR⟩ := hdvd
  rw [show subst q f = P + X ^ (n + 1) * R by rw [← hR]; ring, mul_add, map_add,
    mul_left_comm, coeff_X_pow_mul', ite_eq_right (by omega), add_zero, mul_sum, map_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, coeff_C_mul]

/-- Estimate under the stated parameter and domain assumptions: `coeff n (PowerSeries.catalanQuadraticSeries a e) = ∑
k ∈ range (n + 1), (catalan k : ℚ) * if e * k ≤ n then a ^ (n - e * k) * (2 * k + (n - e *
k)).choose (2 * k) else 0`. -/
private lemma PowerSeries.coeff_catalanQuadraticSeries (a : ℚ) {e : ℕ} (he : 1 ≤ e) (n : ℕ) :
    coeff n (PowerSeries.catalanQuadraticSeries a e) = ∑ k ∈ range (n + 1), (catalan k : ℚ) *
      if e * k ≤ n then a ^ (n - e * k) * (2 * k + (n - e * k)).choose (2 * k) else 0 := by
  rw [PowerSeries.catalanQuadraticSeries, PowerSeries.coeff_mul_subst_eq_sum_range _ _ (by
    simp [PowerSeries.quadraticSubstArg, zero_pow (by omega : e ≠ 0)])]
  refine sum_congr rfl fun k _ => ?_
  congr 1
  · simp [PowerSeries.catalanSeriesRat]
  · rw [PowerSeries.quadraticSubstArg, mul_pow, ← pow_mul, mul_left_comm,
      show PowerSeries.geometricSeries a * (PowerSeries.geometricSeries a ^ 2) ^ k = PowerSeries.geometricSeries a ^ (2 * k + 1) by ring,
      coeff_X_pow_mul', mul_comm e k]
    split_ifs
    · rw [PowerSeries.coeff_geometricSeries_pow_succ]
    · rfl

/-- The coefficients for `e = 2`: `∑_k C(k) C(n, 2k) a^{n-2k}`. -/
theorem PowerSeries.coeff_catalanQuadraticSeries_two (a : ℚ) (n : ℕ) :
    coeff n (PowerSeries.catalanQuadraticSeries a 2) =
      ∑ k ∈ range (n + 1), (catalan k : ℚ) * n.choose (2 * k) * a ^ (n - 2 * k) := by
  rw [PowerSeries.coeff_catalanQuadraticSeries a (by norm_num)]
  refine sum_congr rfl fun k _ => ?_
  split_ifs with h
  · rw [show 2 * k + (n - 2 * k) = n by omega]; ring
  · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

/-- The coefficients for `e = 1`: `∑_k C(k) C(n+k, 2k) a^{n-k}`. -/
private lemma PowerSeries.coeff_catalanQuadraticSeries_one (a : ℚ) (n : ℕ) :
    coeff n (PowerSeries.catalanQuadraticSeries a 1) =
      ∑ k ∈ range (n + 1), (catalan k : ℚ) * (n + k).choose (2 * k) * a ^ (n - k) := by
  rw [PowerSeries.coeff_catalanQuadraticSeries a le_rfl]
  refine sum_congr rfl fun k hk => ?_
  rw [ite_eq_left (by simp at hk; omega), one_mul, show 2 * k + (n - k) = n + k by
    simp at hk; omega]
  ring

/-- Touchard's identity over `ℚ`: `C(n+1) = ∑_k C(k) C(n, 2k) 2^{n-2k}`. -/
theorem catalan_succ_eq_sum_catalan_mul_choose_mul_two_pow (n : ℕ) :
    (catalan (n + 1) : ℚ) =
      ∑ k ∈ range (n + 1), (catalan k : ℚ) * n.choose (2 * k) * 2 ^ (n - 2 * k) := by
  set G : ℚ⟦X⟧ := mk fun n => (catalan (n + 1) : ℚ)
  have hC : PowerSeries.catalanSeriesRat = 1 + X * G := by
    ext m; rcases m with _ | m
    · simp [PowerSeries.catalanSeriesRat]
    · rw [map_add, coeff_succ_X_mul]; simp [PowerSeries.catalanSeriesRat, G]
  have hG : G = 1 + C 2 * X * G + X ^ 2 * G ^ 2 := by
    have h := PowerSeries.catalanSeriesRat_eq
    rw [hC] at h
    have : X * G = X * (1 + C 2 * X * G + X ^ 2 * G ^ 2) := by
      have h2 : (C 2 : ℚ⟦X⟧) = 2 := map_ofNat C 2
      rw [h2]; linear_combination h
    exact mul_left_cancel₀ X_ne_zero this
  have := PowerSeries.eq_of_quadratic_eq 2 (by norm_num) hG (PowerSeries.catalanQuadraticSeries_eq 2 (by norm_num))
  have h := congrArg (coeff n) this
  rwa [PowerSeries.coeff_catalanQuadraticSeries_two, coeff_mk] at h

/-- The large Schröder numbers: `r(n) = ∑_k C(k) C(n+k, 2k)`. -/
theorem Nat.largeSchroder_eq_sum_catalan_mul_choose (n : ℕ) :
    (Nat.largeSchroder n : ℚ) = ∑ k ∈ range (n + 1), (catalan k : ℚ) * (n + k).choose (2 * k) := by
  set R : ℚ⟦X⟧ := mk fun n => (Nat.largeSchroder n : ℚ)
  have hR : R = 1 + C 1 * X * R + X ^ 1 * R ^ 2 := by
    ext m
    rcases m with _ | m
    · simp [R]
    · rw [show (C 1 : ℚ⟦X⟧) = 1 from map_one C, one_mul, pow_one, map_add, map_add,
        coeff_succ_X_mul, coeff_succ_X_mul, coeff_one, pow_two, coeff_mul]
      simp only [R, coeff_mk, Nat.largeSchroder_succ, Nat.cast_add, Nat.cast_sum, Nat.cast_mul]
      simp [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
        (Nat.largeSchroder i : ℚ) * Nat.largeSchroder j), Nat.range_succ_eq_Iic]
  have := PowerSeries.eq_of_quadratic_eq 1 le_rfl hR (PowerSeries.catalanQuadraticSeries_eq 1 le_rfl)
  have h := congrArg (coeff n) this
  rw [PowerSeries.coeff_catalanQuadraticSeries_one, coeff_mk] at h
  simpa using h

/-- Splitting a sum over `range (m + d + 1)` at `m`, the lower part vanishing. -/
private lemma Finset.sum_range_add_succ_eq_of_eq_zero {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m d : ℕ)
    (h : ∀ k < m, f k = 0) :
    ∑ k ∈ range (m + d + 1), f k = ∑ j ∈ range (d + 1), f (m + j) := by
  rw [add_assoc, sum_range_add, sum_eq_zero fun k hk => h k (mem_range.mp hk), zero_add]

/-- `∑_k C(n, k) C(k, m) = C(n, m) 2^{n-m}`. -/
theorem Nat.sum_range_choose_mul_choose_eq (n m : ℕ) :
    ∑ k ∈ range (n + 1), n.choose k * k.choose m = n.choose m * 2 ^ (n - m) := by
  rcases lt_or_ge n m with h | h
  · rw [Nat.choose_eq_zero_of_lt h, zero_mul]
    exact sum_eq_zero fun k hk => by
      rw [Nat.choose_eq_zero_of_lt (n := k) (by simp at hk; omega), mul_zero]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Finset.sum_range_add_succ_eq_of_eq_zero _ m d fun k hk => by rw [Nat.choose_eq_zero_of_lt hk, mul_zero],
    Nat.add_sub_cancel_left, ← Nat.sum_range_choose, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [Nat.choose_mul (by omega), Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]

/-- `∑_k (-1)^{n-k} C(n, k) C(k, i) = [i = n]` for `i ≤ n`. -/
private lemma Int.sum_neg_one_pow_sub_mul_choose_mul_choose {n i : ℕ} (hi : i ≤ n) :
    ∑ k ∈ range (n + 1), (-1 : ℤ) ^ (n - k) * n.choose k * k.choose i =
      if i = n then 1 else 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [Finset.sum_range_add_succ_eq_of_eq_zero _ i d fun k hk => by
    rw [Nat.choose_eq_zero_of_lt hk, Nat.cast_zero, mul_zero]]
  have : ∀ j ∈ range (d + 1), (-1 : ℤ) ^ (i + d - (i + j)) * ((i + d).choose (i + j) : ℤ) *
      ((i + j).choose i : ℤ) = (i + d).choose i * ((-1) ^ (d - j) * d.choose j) := by
    intro j hj
    have := Nat.choose_mul (n := i + d) (k := i + j) (s := i) (by omega)
    rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left] at this
    rw [Nat.add_sub_add_left, mul_assoc, ← Nat.cast_mul, this]; push_cast; ring
  rw [sum_congr rfl this, ← mul_sum]
  have h2 : ∑ j ∈ range (d + 1), (-1 : ℤ) ^ (d - j) * d.choose j =
      ∑ j ∈ range (d + 1), (-1 : ℤ) ^ j * d.choose j := by
    rw [← sum_range_reflect]
    refine sum_congr rfl fun j hj => ?_
    rw [show d + 1 - 1 - j = d - j by omega, Nat.choose_symm (by simp at hj; omega),
      show d - (d - j) = j by simp at hj; omega]
  rw [h2, Int.alternating_sum_range_choose]
  rcases d with _ | d <;> simp

/-- Binomial inversion: if `b n = ∑_k C(n, k) a k` for all `n`, then
`a n = ∑_k (-1)^{n-k} C(n, k) b k`. -/
theorem Int.binomial_inversion (a b : ℕ → ℤ)
    (h : ∀ n, b n = ∑ k ∈ range (n + 1), (n.choose k : ℤ) * a k) (n : ℕ) :
    a n = ∑ k ∈ range (n + 1), (-1 : ℤ) ^ (n - k) * n.choose k * b k := by
  simp_rw [h, mul_sum]
  have : ∀ k ∈ range (n + 1), ∑ i ∈ range (k + 1),
      (-1 : ℤ) ^ (n - k) * n.choose k * ((k.choose i : ℤ) * a i) =
      ∑ i ∈ range (n + 1), (-1 : ℤ) ^ (n - k) * n.choose k * ((k.choose i : ℤ) * a i) := by
    intro k hk
    refine sum_subset (range_subset_range.mpr (by simp at hk; omega)) fun i _ hi => ?_
    rw [Nat.choose_eq_zero_of_lt (n := k) (by simp at hi; omega)]; simp
  rw [sum_congr rfl this, sum_comm]
  have e : ∀ i ∈ range (n + 1), ∑ k ∈ range (n + 1),
      (-1 : ℤ) ^ (n - k) * n.choose k * ((k.choose i : ℤ) * a i) =
      (if i = n then 1 else 0) * a i := by
    intro i hi
    rw [← Int.sum_neg_one_pow_sub_mul_choose_mul_choose (by simp at hi; omega), sum_mul]
    exact sum_congr rfl fun k _ => by ring
  rw [sum_congr rfl e]
  simp

end
