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
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic.LinearCombination

/-!
# Quadratic generating series built on the Catalan series

Over `ℚ`, with `C(X) = ∑ C(n) Xⁿ` the Catalan series (`C = 1 + X C²`), the series
`F_{a,e} = (1 - aX)⁻¹ C(X^e (1 - aX)⁻²)` (formal substitution, Mathlib `PowerSeries.subst`) is the
unique power series solution of `F = 1 + aXF + X^e F²` (`e ≥ 1`), and its coefficients are
`∑_k C(k) C(n, 2k) a^{n-2k}` for `e = 2` and `∑_k C(k) C(n+k, 2k) a^{n-k}` for `e = 1`.
Consequences: Touchard's identity `C(n+1) = ∑_k C(k) C(n, 2k) 2^{n-2k}` and the formula
`r(n) = ∑_k C(k) C(n+k, 2k)` for the large Schröder numbers. Also binomial inversion and
`∑_k C(n, k) C(k, m) = C(n, m) 2^{n-m}`.
-/

@[expose] public section

open Finset PowerSeries

noncomputable section

/-- The Catalan generating series `∑ C(n) Xⁿ` over `ℚ`. -/
noncomputable def s26a_catSeries : ℚ⟦X⟧ := mk fun n => (catalan n : ℚ)

theorem s26a_catSeries_eq : s26a_catSeries = 1 + X * s26a_catSeries ^ 2 := by
  ext n
  rcases n with _ | n
  · simp [s26a_catSeries]
  · rw [map_add, coeff_succ_X_mul, pow_two, coeff_mul]
    simp [s26a_catSeries, catalan_succ']

/-- The geometric series `∑ aⁿ Xⁿ = 1/(1 - aX)`. -/
noncomputable def s26a_geom (a : ℚ) : ℚ⟦X⟧ := rescale a (mk 1)

theorem s26a_geom_mul (a : ℚ) : s26a_geom a * (1 - C a * X) = 1 := by
  have := congrArg (rescale a) (mk_one_mul_one_sub_eq_one (S := ℚ))
  rwa [map_mul, map_sub, map_one, rescale_X] at this

theorem s26a_coeff_geom_pow (a : ℚ) (d n : ℕ) :
    coeff n (s26a_geom a ^ (d + 1)) = a ^ n * (d + n).choose d := by
  rw [s26a_geom, ← map_pow, mk_one_pow_eq_mk_choose_add, rescale_mk, coeff_mk]

theorem s26a_constantCoeff_geom (a : ℚ) : constantCoeff (s26a_geom a) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, s26a_geom, rescale_mk, coeff_mk]; simp

/-- The substituted argument `q = X^e (1 - aX)^{-2}`. -/
noncomputable def s26a_arg (a : ℚ) (e : ℕ) : ℚ⟦X⟧ := X ^ e * s26a_geom a ^ 2

theorem s26a_hasSubst_arg (a : ℚ) {e : ℕ} (he : 1 ≤ e) : HasSubst (s26a_arg a e) :=
  HasSubst.of_constantCoeff_zero' (by
    simp [s26a_arg, zero_pow (by omega : e ≠ 0)])

/-- `F = (1 - aX)⁻¹ C(X^e (1 - aX)^{-2})`. -/
noncomputable def s26a_quadSeries (a : ℚ) (e : ℕ) : ℚ⟦X⟧ :=
  s26a_geom a * subst (s26a_arg a e) s26a_catSeries

theorem s26a_quadSeries_eq (a : ℚ) {e : ℕ} (he : 1 ≤ e) :
    s26a_quadSeries a e =
      1 + C a * X * s26a_quadSeries a e + X ^ e * s26a_quadSeries a e ^ 2 := by
  have hs := s26a_hasSubst_arg a he
  have hD : subst (s26a_arg a e) s26a_catSeries =
      1 + s26a_arg a e * subst (s26a_arg a e) s26a_catSeries ^ 2 := by
    conv_lhs => rw [s26a_catSeries_eq]
    rw [← coe_substAlgHom hs, map_add, map_one, map_mul, map_pow, substAlgHom_X]
  have hg := s26a_geom_mul a
  simp only [s26a_quadSeries, s26a_arg] at hD ⊢
  linear_combination (subst (X ^ e * s26a_geom a ^ 2) s26a_catSeries) * hg + hD

/-- Uniqueness of the power series solution of `F = 1 + aXF + X^e F²`. -/
theorem s26a_quad_unique (a : ℚ) {e : ℕ} (he : 1 ≤ e) {F G : ℚ⟦X⟧}
    (hF : F = 1 + C a * X * F + X ^ e * F ^ 2) (hG : G = 1 + C a * X * G + X ^ e * G ^ 2) :
    F = G := by
  have h : (F - G) * (1 - C a * X - X ^ e * (F + G)) = 0 := by
    linear_combination hF - hG
  rcases mul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have := congrArg constantCoeff h
    simp [zero_pow (by omega : e ≠ 0)] at this

theorem s26a_coeff_subst (q : ℚ⟦X⟧) (hq : constantCoeff q = 0) (f : ℚ⟦X⟧) {n N : ℕ}
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
theorem s26a_coeff_mul_subst (g q : ℚ⟦X⟧) (hq : constantCoeff q = 0) (f : ℚ⟦X⟧) (n : ℕ) :
    coeff n (g * subst q f) = ∑ k ∈ range (n + 1), coeff k f * coeff n (g * q ^ k) := by
  set P : ℚ⟦X⟧ := ∑ k ∈ range (n + 1), C (coeff k f) * q ^ k
  have hdvd : X ^ (n + 1) ∣ subst q f - P := by
    rw [X_pow_dvd_iff]
    intro m hm
    rw [map_sub, s26a_coeff_subst q hq f hm, map_sum]
    simp [coeff_C_mul]
  obtain ⟨R, hR⟩ := hdvd
  rw [show subst q f = P + X ^ (n + 1) * R by rw [← hR]; ring, mul_add, map_add,
    mul_left_comm, coeff_X_pow_mul', ite_eq_right (by omega), add_zero, mul_sum, map_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, coeff_C_mul]

theorem s26a_coeff_quadSeries (a : ℚ) {e : ℕ} (he : 1 ≤ e) (n : ℕ) :
    coeff n (s26a_quadSeries a e) = ∑ k ∈ range (n + 1), (catalan k : ℚ) *
      if e * k ≤ n then a ^ (n - e * k) * (2 * k + (n - e * k)).choose (2 * k) else 0 := by
  rw [s26a_quadSeries, s26a_coeff_mul_subst _ _ (by
    simp [s26a_arg, zero_pow (by omega : e ≠ 0)])]
  refine sum_congr rfl fun k _ => ?_
  congr 1
  · simp [s26a_catSeries]
  · rw [s26a_arg, mul_pow, ← pow_mul, mul_left_comm,
      show s26a_geom a * (s26a_geom a ^ 2) ^ k = s26a_geom a ^ (2 * k + 1) by ring,
      coeff_X_pow_mul', mul_comm e k]
    split_ifs
    · rw [s26a_coeff_geom_pow]
    · rfl

/-- The coefficients for `e = 2`: `∑_k C(k) C(n, 2k) a^{n-2k}`. -/
theorem s26a_coeff_quadSeries_two (a : ℚ) (n : ℕ) :
    coeff n (s26a_quadSeries a 2) =
      ∑ k ∈ range (n + 1), (catalan k : ℚ) * n.choose (2 * k) * a ^ (n - 2 * k) := by
  rw [s26a_coeff_quadSeries a (by norm_num)]
  refine sum_congr rfl fun k _ => ?_
  split_ifs with h
  · rw [show 2 * k + (n - 2 * k) = n by omega]; ring
  · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

/-- The coefficients for `e = 1`: `∑_k C(k) C(n+k, 2k) a^{n-k}`. -/
theorem s26a_coeff_quadSeries_one (a : ℚ) (n : ℕ) :
    coeff n (s26a_quadSeries a 1) =
      ∑ k ∈ range (n + 1), (catalan k : ℚ) * (n + k).choose (2 * k) * a ^ (n - k) := by
  rw [s26a_coeff_quadSeries a le_rfl]
  refine sum_congr rfl fun k hk => ?_
  rw [ite_eq_left (by simp at hk; omega), one_mul, show 2 * k + (n - k) = n + k by
    simp at hk; omega]
  ring

/-- Touchard's identity over `ℚ`: `C(n+1) = ∑_k C(k) C(n, 2k) 2^{n-2k}`. -/
theorem s26a_catalan_succ_eq_sum (n : ℕ) :
    (catalan (n + 1) : ℚ) =
      ∑ k ∈ range (n + 1), (catalan k : ℚ) * n.choose (2 * k) * 2 ^ (n - 2 * k) := by
  set G : ℚ⟦X⟧ := mk fun n => (catalan (n + 1) : ℚ)
  have hC : s26a_catSeries = 1 + X * G := by
    ext m; rcases m with _ | m
    · simp [s26a_catSeries]
    · rw [map_add, coeff_succ_X_mul]; simp [s26a_catSeries, G]
  have hG : G = 1 + C 2 * X * G + X ^ 2 * G ^ 2 := by
    have h := s26a_catSeries_eq
    rw [hC] at h
    have : X * G = X * (1 + C 2 * X * G + X ^ 2 * G ^ 2) := by
      have h2 : (C 2 : ℚ⟦X⟧) = 2 := map_ofNat C 2
      rw [h2]; linear_combination h
    exact mul_left_cancel₀ X_ne_zero this
  have := s26a_quad_unique 2 (by norm_num) hG (s26a_quadSeries_eq 2 (by norm_num))
  have h := congrArg (coeff n) this
  rwa [s26a_coeff_quadSeries_two, coeff_mk] at h

/-- The large Schröder numbers: `r(n) = ∑_k C(k) C(n+k, 2k)`. -/
theorem s26a_largeSchroder_eq_sum (n : ℕ) :
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
  have := s26a_quad_unique 1 le_rfl hR (s26a_quadSeries_eq 1 le_rfl)
  have h := congrArg (coeff n) this
  rw [s26a_coeff_quadSeries_one, coeff_mk] at h
  simpa using h


/-- Splitting a sum over `range (m + d + 1)` at `m`, the lower part vanishing. -/
theorem s26a_sum_range_split {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m d : ℕ)
    (h : ∀ k < m, f k = 0) :
    ∑ k ∈ range (m + d + 1), f k = ∑ j ∈ range (d + 1), f (m + j) := by
  rw [add_assoc, sum_range_add, sum_eq_zero fun k hk => h k (mem_range.mp hk), zero_add]

/-- `∑_k C(n, k) C(k, m) = C(n, m) 2^{n-m}`. -/
theorem s26a_sum_choose_mul_choose (n m : ℕ) :
    ∑ k ∈ range (n + 1), n.choose k * k.choose m = n.choose m * 2 ^ (n - m) := by
  rcases lt_or_ge n m with h | h
  · rw [Nat.choose_eq_zero_of_lt h, zero_mul]
    exact sum_eq_zero fun k hk => by
      rw [Nat.choose_eq_zero_of_lt (n := k) (by simp at hk; omega), mul_zero]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [s26a_sum_range_split _ m d fun k hk => by rw [Nat.choose_eq_zero_of_lt hk, mul_zero],
    Nat.add_sub_cancel_left, ← Nat.sum_range_choose, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [Nat.choose_mul (by omega), Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]

/-- `∑_k (-1)^{n-k} C(n, k) C(k, i) = [i = n]` for `i ≤ n`. -/
theorem s26a_sum_neg_one_pow_choose_mul_choose {n i : ℕ} (hi : i ≤ n) :
    ∑ k ∈ range (n + 1), (-1 : ℤ) ^ (n - k) * n.choose k * k.choose i =
      if i = n then 1 else 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [s26a_sum_range_split _ i d fun k hk => by
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
theorem s26a_binomial_inversion (a b : ℕ → ℤ)
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
    rw [← s26a_sum_neg_one_pow_choose_mul_choose (by simp at hi; omega), sum_mul]
    exact sum_congr rfl fun k _ => by ring
  rw [sum_congr rfl e]
  simp

end
