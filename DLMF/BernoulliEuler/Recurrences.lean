/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.Properties

/-!
# Bernoulli and Euler numbers and polynomials: recurrence relations (DLMF §24.5)

The basic relations 24.5.1–24.5.5, further identities 24.5.6–24.5.8 and the inversion formulas
24.5.9–24.5.10, for complex `x` and rational numbers. The basic relations are proved; they hold
for all `n ≥ 0` where DLMF states `n ≥ 2` or `n ≥ 1` except 24.5.3 (`n ≥ 2`) and 24.5.4
(`n ≥ 1`), whose small cases fail.
-/

@[expose] public section

noncomputable section

open Polynomial (aeval X C)
open Finset
open scoped Nat Real Polynomial

namespace DLMF.BernoulliEuler

/-! ### §24.5(i) Basic relations -/

/-- **DLMF 24.5.1**: `∑_{k=0}^{n-1} (n choose k) Bₖ(x) = n x^{n-1}`. DLMF states `n ≥ 2`; this
holds for all `n` (stronger than DLMF). -/
@[dlmf 24.5.E1]
theorem sum_choose_mul_bernoulliPolyB (n : ℕ) (x : ℂ) :
    ∑ k ∈ range n, (n.choose k : ℂ) * bernoulliPolyB k x = n * x ^ (n - 1) := by
  have h := bernoulliPolyB_add n x 1
  rw [sum_range_succ] at h
  simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one, one_mul] at h
  rw [← bernoulliPolyB_add_one_sub n x, h]
  ring

/-- **DLMF 24.5.2**: `∑_{k=0}^{n} (n choose k) Eₖ(x) + Eₙ(x) = 2xⁿ`. DLMF states `n ≥ 1`; this
holds for all `n` (stronger than DLMF). -/
@[dlmf 24.5.E2]
theorem sum_choose_mul_eulerPolyE_add (n : ℕ) (x : ℂ) :
    ∑ k ∈ range (n + 1), (n.choose k : ℂ) * eulerPolyE k x + eulerPolyE n x = 2 * x ^ n := by
  have h := eulerPolyE_add n x 1
  simp only [one_pow, mul_one] at h
  rw [← h]
  exact eulerPolyE_add_one_add n x

/-- **DLMF 24.5.3**: `∑_{k=0}^{n-1} (n choose k) Bₖ = 0` for `n ≥ 2`. -/
@[dlmf 24.5.E3]
theorem sum_choose_mul_bernoulli_eq_zero {n : ℕ} (hn : 2 ≤ n) :
    ∑ k ∈ range n, (n.choose k : ℚ) * bernoulli k = 0 := by
  rw [sum_bernoulli, ite_eq_right_iff.mpr (fun h => by omega)]

/-- **DLMF 24.5.4**: `∑_{k=0}^{n} (2n choose 2k) E₂ₖ = 0` for `n ≥ 1`. -/
@[dlmf 24.5.E4]
theorem sum_choose_two_mul_mul_eulerNumber {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ range (n + 1), ((2 * n).choose (2 * k) : ℚ) * eulerNumber (2 * k) = 0 := by
  have hs := sum_choose_mul_eulerNumber (2 * n)
  rw [zero_pow (by omega), mul_zero] at hs
  have himg : ∑ k ∈ range (2 * n + 1), ((2 * n).choose k : ℚ) * (1 + (-1) ^ (2 * n - k)) *
      eulerNumber k = ∑ k ∈ (range (n + 1)).image (2 * ·), ((2 * n).choose k : ℚ) *
      (1 + (-1) ^ (2 * n - k)) * eulerNumber k := by
    symm
    refine sum_subset (fun k hk => ?_) (fun k hk hk' => ?_)
    · obtain ⟨j, hj, rfl⟩ := mem_image.mp hk
      have := mem_range.mp hj; exact mem_range.mpr (by omega)
    · have hodd : Odd k := by
        rcases Nat.even_or_odd k with ⟨j, hj⟩ | h
        · exact absurd (mem_image.mpr ⟨j, mem_range.mpr (by have := mem_range.mp hk; omega),
            by omega⟩) hk'
        · exact h
      simp [eulerNumber_eq_zero_of_odd hodd]
  rw [himg, sum_image (fun a _ b _ h => by simpa using h)] at hs
  have : ∀ k ∈ range (n + 1), ((2 * n).choose (2 * k) : ℚ) * (1 + (-1) ^ (2 * n - 2 * k)) *
      eulerNumber (2 * k) = 2 * (((2 * n).choose (2 * k) : ℚ) * eulerNumber (2 * k)) := by
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [show 2 * n - 2 * k = 2 * (n - k) by omega, pow_mul]; norm_num; ring
  rw [sum_congr rfl this, ← mul_sum] at hs
  linarith

/-- **DLMF 24.5.5**: `∑_{k=0}^{n} (n choose k) 2ᵏ Eₙ₋ₖ + Eₙ = 2`. -/
@[dlmf 24.5.E5]
theorem sum_choose_mul_two_pow_mul_eulerNumber (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k : ℚ) * 2 ^ k * eulerNumber (n - k) + eulerNumber n = 2 := by
  have h1 := eulerPolyE_eq_sum n (3 / 2)
  have h2 := eulerPolyE_add_one_add n (1 / 2)
  rw [show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num, h1, eulerPolyE_half] at h2
  rw [show (3 / 2 : ℂ) - 1 / 2 = 1 by norm_num] at h2
  simp only [one_pow, mul_one] at h2
  have h3 : ∑ k ∈ range (n + 1), (n.choose k : ℂ) * 2 ^ k * eulerNumber (n - k) =
      2 ^ n * ∑ k ∈ range (n + 1), (n.choose k : ℂ) * (eulerNumber k / 2 ^ k) := by
    rw [← sum_range_reflect, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [show n + 1 - 1 - k = n - k by omega, Nat.choose_symm hk',
      Nat.sub_sub_self hk', show (2 : ℂ) ^ n = 2 ^ (n - k) * 2 ^ k by
        rw [← pow_add, Nat.sub_add_cancel hk']]
    field_simp
  have h4 : (∑ k ∈ range (n + 1), (n.choose k : ℚ) * 2 ^ k * eulerNumber (n - k) +
      eulerNumber n : ℚ) = ((2 : ℚ) : ℂ) := by
    push_cast
    rw [h3]
    have h5 : (2 : ℂ) ^ n * (1 / 2) ^ n = 1 := by rw [← mul_pow]; norm_num
    field_simp at h2 ⊢
    linear_combination h2 + 2 * h5
  exact_mod_cast h4

/-! ### Helpers for §§24.5(ii)–(iii) -/

/-- Splitting off the first two terms of a sum over `range (n+1)`. -/
theorem q24a_sum_Icc_two {M : Type*} [AddCommMonoid M] (f : ℕ → M) {n : ℕ} (hn : 1 ≤ n) :
    f 0 + f 1 + ∑ k ∈ Icc 2 n, f k = ∑ k ∈ range (n + 1), f k := by
  induction n, hn using Nat.le_induction with
  | base => simp [sum_range_succ]
  | succ n hn ih => rw [sum_Icc_succ_top (by omega), ← add_assoc, ih, sum_range_succ (n := n + 1)]

/-- `∑_{k ≤ n} (n+2 choose k) Bₖ = -(n+2) Bₙ₊₁`. -/
theorem q24a_sum_choose_bernoulli_succ_succ (n : ℕ) :
    ∑ k ∈ range (n + 1), ((n + 2).choose k : ℚ) * bernoulli k = -(n + 2) * bernoulli (n + 1) := by
  have h := sum_bernoulli (n + 2)
  simp only [show n + 2 ≠ 1 by omega, ↓reduceIte] at h
  rw [sum_range_succ, Nat.choose_succ_self_right] at h
  push_cast at h
  linear_combination h

/-- The exponential generating function `∑ xₙ tⁿ/n!` as a formal power series. -/
noncomputable def q24a_egf (x : ℕ → ℂ) : PowerSeries ℂ := PowerSeries.mk fun n => x n / n !

/-- Coefficients of a product of exponential generating functions. -/
theorem q24a_coeff_egf_mul (x y : ℕ → ℂ) (n : ℕ) :
    PowerSeries.coeff n (q24a_egf x * q24a_egf y) =
      (∑ k ∈ range (n + 1), (n.choose k : ℂ) * x k * y (n - k)) / n ! := by
  rw [PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (q24a_egf x) * PowerSeries.coeff j (q24a_egf y)), sum_div]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  simp only [q24a_egf, PowerSeries.coeff_mk]
  have hc := Nat.choose_mul_factorial_mul_factorial hk'
  have hc' : (n.choose k : ℂ) * k ! * (n - k)! = n ! := by exact_mod_cast hc
  rw [← hc']
  have h1 : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : ((n - k)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : (n.choose k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hk').ne'
  field_simp

/-- Binomial convolution identities as products of exponential generating functions. -/
theorem q24a_egf_eq_mul_iff (x y z : ℕ → ℂ) :
    (∀ n, x n = ∑ k ∈ range (n + 1), (n.choose k : ℂ) * y k * z (n - k)) ↔
      q24a_egf x = q24a_egf y * q24a_egf z := by
  rw [PowerSeries.ext_iff]
  refine forall_congr' fun n => ?_
  rw [q24a_coeff_egf_mul]
  simp only [q24a_egf, PowerSeries.coeff_mk]
  have : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  constructor
  · intro h; rw [h]
  · intro h; exact (div_left_inj' this).mp h

/-- `(t/(eᵗ - 1)) · ((eᵗ - 1)/t) = 1` as formal power series. -/
theorem q24a_egf_bernoulli_mul :
    q24a_egf (fun n => (bernoulli n : ℂ)) * q24a_egf (fun n => 1 / ((n : ℂ) + 1)) = 1 := by
  have h := bernoulliPowerSeries_mul_exp_sub_one ℂ
  have hB : bernoulliPowerSeries ℂ = q24a_egf (fun n => (bernoulli n : ℂ)) := by
    ext n; simp [bernoulliPowerSeries, q24a_egf]
  have hE : PowerSeries.exp ℂ - 1 = PowerSeries.X * q24a_egf (fun n => 1 / ((n : ℂ) + 1)) := by
    ext n
    rcases n with _ | n
    · simp
    · rw [PowerSeries.coeff_succ_X_mul]
      simp [q24a_egf, PowerSeries.coeff_exp, Nat.factorial_succ]
      field_simp
  rw [hB, hE, mul_left_comm] at h
  have hX : (PowerSeries.X : PowerSeries ℂ) ≠ 0 := PowerSeries.X_ne_zero
  exact mul_left_cancel₀ hX (h.trans (mul_one _).symm)

/-- Sums over even indices `2k ≤ n`. -/
theorem q24a_sum_half_eq (g : ℕ → ℂ) (n : ℕ) :
    ∑ k ∈ range (n / 2 + 1), g (2 * k) = ∑ k ∈ range (n + 1), if Even k then g k else 0 := by
  rw [← sum_filter]
  have : (range (n + 1)).filter Even = (range (n / 2 + 1)).image (2 * ·) := by
    ext k
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hk, j, rfl⟩; exact ⟨j, by omega, by ring⟩
    · rintro ⟨j, hj, rfl⟩; exact ⟨by omega, even_two_mul j⟩
  rw [this, sum_image (fun a _ b _ h => by simpa using h)]

/-- `sech t · cosh t = 1` as formal power series. -/
theorem q24a_egf_euler_mul :
    q24a_egf (fun n => (eulerNumber n : ℂ)) * q24a_egf (fun n => if Even n then 1 else 0) = 1 := by
  ext n
  rw [q24a_coeff_egf_mul, PowerSeries.coeff_one]
  have h := sum_choose_mul_eulerNumber n
  have h' : ∑ k ∈ range (n + 1), (n.choose k : ℂ) * eulerNumber k *
      (if Even (n - k) then 1 else 0) = if n = 0 then 1 else 0 := by
    have hc : ∑ k ∈ range (n + 1), (n.choose k : ℂ) * (1 + (-1) ^ (n - k)) * eulerNumber k =
        2 * 0 ^ n := by exact_mod_cast h
    have : ∀ k ∈ range (n + 1), (n.choose k : ℂ) * eulerNumber k *
        (if Even (n - k) then 1 else 0) =
        ((n.choose k : ℂ) * (1 + (-1) ^ (n - k)) * eulerNumber k) / 2 := by
      intro k _
      rcases Nat.even_or_odd (n - k) with he | ho
      · simp only [he, ↓reduceIte, he.neg_one_pow]; ring
      · simp only [Nat.not_even_iff_odd.mpr ho, ↓reduceIte, ho.neg_one_pow]; ring
    rw [sum_congr rfl this, ← sum_div, hc]
    rcases n with _ | n <;> simp
  rw [h']
  rcases n with _ | n <;> simp

/-! ### §24.5(ii) Other identities -/

/-- **DLMF 24.5.6**: `∑_{k=2}^{n} (n choose k-2) Bₖ/k = 1/((n+1)(n+2)) - Bₙ₊₁`, `n ≥ 2`. -/
@[dlmf 24.5.E6]
theorem sum_choose_sub_two_mul_bernoulli_div {n : ℕ} (hn : 2 ≤ n) :
    ∑ k ∈ Icc 2 n, (n.choose (k - 2) : ℚ) * bernoulli k / k =
      1 / ((n + 1) * (n + 2)) - bernoulli (n + 1) := by
  have h1 := sum_bernoulli (n + 1)
  simp only [show n + 1 ≠ 1 by omega, ↓reduceIte] at h1
  have h2 := q24a_sum_choose_bernoulli_succ_succ n
  have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
  have hn2 : (n : ℚ) + 2 ≠ 0 := by positivity
  -- termwise: `(n choose k-2)/k = (n+2 choose k)(k-1)/((n+1)(n+2))` for `k ≥ 2`
  have hterm : ∀ k ∈ Icc 2 n, (n.choose (k - 2) : ℚ) * bernoulli k / k =
      (((k : ℚ) - 1) * (((n + 2).choose k : ℚ) * bernoulli k)) / ((n + 1) * (n + 2)) := by
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by have := (mem_Icc.mp hk).1; omega⟩
    rw [Nat.add_sub_cancel]
    have hA := Nat.add_one_mul_choose_eq n j
    have hB := Nat.add_one_mul_choose_eq (n + 1) (j + 1)
    have hA' : ((n : ℚ) + 1) * (n.choose j : ℚ) = ((n + 1).choose (j + 1) : ℚ) * (j + 1) := by
      exact_mod_cast hA
    have hB' : ((n : ℚ) + 2) * ((n + 1).choose (j + 1) : ℚ) =
        ((n + 2).choose (j + 2) : ℚ) * (j + 2) := by
      have := congrArg (Nat.cast : ℕ → ℚ) hB
      push_cast at this
      linear_combination this
    have hj : ((j + 2 : ℕ) : ℚ) ≠ 0 := by positivity
    push_cast at hj ⊢
    field_simp
    linear_combination (bernoulli (j + 2) * (n + 2)) * hA' +
      (bernoulli (j + 2) * (j + 1)) * hB'
  rw [sum_congr rfl hterm, ← sum_div]
  -- `T = ∑_{k=2}^{n} (k-1)(n+2 choose k)Bₖ = 1 - (n+1)(n+2)Bₙ₊₁`
  have hsplit := q24a_sum_Icc_two (fun k => ((k : ℚ) - 1) * (((n + 2).choose k : ℚ) * bernoulli k))
    (by omega : 1 ≤ n)
  simp only [Nat.cast_zero, zero_sub, Nat.choose_zero_right, bernoulli_zero, Nat.cast_one,
    sub_self, zero_mul] at hsplit
  have hdiff : ∀ k ∈ range (n + 1), ((k : ℚ) - 1) * (((n + 2).choose k : ℚ) * bernoulli k) =
      (n + 1) * (((n + 2).choose k : ℚ) * bernoulli k) -
        (n + 2) * (((n + 1).choose k : ℚ) * bernoulli k) := by
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have := congrArg (Nat.cast : ℕ → ℚ) (Nat.choose_mul_succ_eq (n + 1) k)
    push_cast [Nat.cast_sub (by omega : k ≤ n + 1 + 1)] at this
    linear_combination (bernoulli k) * this
  rw [sum_congr rfl hdiff, sum_sub_distrib, ← mul_sum, ← mul_sum, h1, h2] at hsplit
  have hT : ∑ k ∈ Icc 2 n, ((k : ℚ) - 1) * (((n + 2).choose k : ℚ) * bernoulli k) =
      1 - (n + 1) * (n + 2) * bernoulli (n + 1) := by linear_combination hsplit
  rw [hT]
  field_simp

/-- **DLMF 24.5.7**: `∑_{k=0}^{n} (n choose k) Bₖ/(n+2-k) = Bₙ₊₁/(n+1)`, `n ≥ 1`. -/
@[dlmf 24.5.E7]
theorem sum_choose_mul_bernoulli_div {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ range (n + 1), (n.choose k : ℚ) * bernoulli k / (n + 2 - k) =
      bernoulli (n + 1) / (n + 1) := by
  have h1 := sum_bernoulli (n + 1)
  simp only [show n + 1 ≠ 1 by omega, ↓reduceIte] at h1
  have h2 := q24a_sum_choose_bernoulli_succ_succ n
  have hterm : ∀ k ∈ range (n + 1), (n.choose k : ℚ) * bernoulli k / (n + 2 - k) =
      ((n + 2) * (((n + 1).choose k : ℚ) * bernoulli k) - ((n + 2).choose k : ℚ) * bernoulli k) /
        ((n + 1) * (n + 2)) := by
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hA := Nat.choose_mul_succ_eq n k
    have hB := Nat.choose_mul_succ_eq (n + 1) k
    have hA' : (n.choose k : ℚ) * (n + 1) = ((n + 1).choose k : ℚ) * (n + 1 - k) := by
      rw [show (n : ℚ) + 1 - k = ((n + 1 - k : ℕ) : ℚ) by push_cast [show k ≤ n + 1 by omega]; ring]
      exact_mod_cast hA
    have hB' : ((n + 1).choose k : ℚ) * (n + 2) = ((n + 2).choose k : ℚ) * (n + 2 - k) := by
      have := congrArg (Nat.cast : ℕ → ℚ) hB
      push_cast [Nat.cast_sub (by omega : k ≤ n + 1 + 1)] at this
      linear_combination this
    have hk2 : (n : ℚ) + 2 - k ≠ 0 := by
      have : (k : ℚ) ≤ n := by exact_mod_cast hk'
      linarith
    field_simp
    linear_combination (bernoulli k * (n + 2)) * hA' - bernoulli k * hB'
  rw [sum_congr rfl hterm, ← sum_div, sum_sub_distrib, ← mul_sum, h1, h2]
  field_simp
  ring

/-- **DLMF 24.5.8**: `∑_{k=0}^{n} 2²ᵏ B₂ₖ/((2k)!(2n+1-2k)!) = 1/(2n)!`, `n ≥ 1`. -/
@[dlmf 24.5.E8]
theorem sum_two_pow_mul_bernoulli_div_factorial {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ range (n + 1), (2 : ℚ) ^ (2 * k) * bernoulli (2 * k) / ((2 * k)! * (2 * n + 1 - 2 * k)!) =
      1 / (2 * n)! := by
  have h := q24a_sum_choose_bernoulli_two_pow n
  have hq : ∑ j ∈ range n, ((2 * n + 1).choose (2 * (j + 1)) : ℚ) * bernoulli (2 * (j + 1)) *
      2 ^ (2 * (j + 1)) = 2 * n := by exact_mod_cast h
  have hterm : ∀ k ∈ range (n + 1), (2 : ℚ) ^ (2 * k) * bernoulli (2 * k) /
      ((2 * k)! * (2 * n + 1 - 2 * k)!) =
      ((2 * n + 1).choose (2 * k) : ℚ) * bernoulli (2 * k) * 2 ^ (2 * k) / (2 * n + 1)! := by
    intro k hk
    have hk' : 2 * k ≤ 2 * n + 1 := by have := mem_range.mp hk; omega
    have hc := Nat.choose_mul_factorial_mul_factorial hk'
    have hc' : ((2 * n + 1).choose (2 * k) : ℚ) * (2 * k)! * (2 * n + 1 - 2 * k)! =
        (2 * n + 1)! := by exact_mod_cast hc
    rw [eq_div_iff (by positivity), ← hc']
    field_simp
  rw [sum_congr rfl hterm, ← sum_div, sum_range_succ', hq]
  simp only [mul_zero, Nat.choose_zero_right, Nat.cast_one, bernoulli_zero, pow_zero, mul_one]
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-! ### §24.5(iii) Inversion formulas -/

/-- **DLMF 24.5.9**: for sequences `aₙ`, `bₙ` (complex), `aₙ = ∑ₖ (n choose k) bₙ₋ₖ/(k+1)` for
all `n` if and only if `bₙ = ∑ₖ (n choose k) Bₖ aₙ₋ₖ` for all `n`. -/
@[dlmf 24.5.E9]
theorem bernoulli_inversion (a b : ℕ → ℂ) :
    (∀ n, a n = ∑ k ∈ range (n + 1), (n.choose k : ℂ) * b (n - k) / (k + 1)) ↔
      (∀ n, b n = ∑ k ∈ range (n + 1), (n.choose k : ℂ) * bernoulli k * a (n - k)) := by
  have e1 : (∀ n, a n = ∑ k ∈ range (n + 1), (n.choose k : ℂ) * b (n - k) / (k + 1)) ↔
      q24a_egf a = q24a_egf (fun n => 1 / ((n : ℂ) + 1)) * q24a_egf b := by
    have hsum : ∀ n, ∑ k ∈ range (n + 1), (n.choose k : ℂ) * b (n - k) / (k + 1) =
        ∑ k ∈ range (n + 1), (n.choose k : ℂ) * (1 / ((k : ℂ) + 1)) * b (n - k) :=
      fun n => sum_congr rfl fun k _ => by ring
    simp only [hsum]
    exact q24a_egf_eq_mul_iff _ _ _
  rw [e1, q24a_egf_eq_mul_iff]
  have hBE := q24a_egf_bernoulli_mul
  constructor
  · intro h; rw [h, ← mul_assoc, hBE, one_mul]
  · intro h; rw [h, ← mul_assoc, mul_comm (q24a_egf _) (q24a_egf (fun n => (bernoulli n : ℂ))),
      hBE, one_mul]

/-- **DLMF 24.5.10**: `aₙ = ∑_{k ≤ n/2} (n choose 2k) bₙ₋₂ₖ` for all `n` if and only if
`bₙ = ∑_{k ≤ n/2} (n choose 2k) E₂ₖ aₙ₋₂ₖ` for all `n`. -/
@[dlmf 24.5.E10]
theorem euler_inversion (a b : ℕ → ℂ) :
    (∀ n, a n = ∑ k ∈ range (n / 2 + 1), (n.choose (2 * k) : ℂ) * b (n - 2 * k)) ↔
      (∀ n, b n = ∑ k ∈ range (n / 2 + 1), (n.choose (2 * k) : ℂ) * eulerNumber (2 * k) *
        a (n - 2 * k)) := by
  have e1 : ∀ n, ∑ k ∈ range (n / 2 + 1), (n.choose (2 * k) : ℂ) * b (n - 2 * k) =
      ∑ k ∈ range (n + 1), (n.choose k : ℂ) * (if Even k then 1 else 0) * b (n - k) := by
    intro n
    rw [q24a_sum_half_eq (fun k => (n.choose k : ℂ) * b (n - k))]
    refine sum_congr rfl fun k _ => ?_
    split_ifs <;> ring
  have e2 : ∀ n, ∑ k ∈ range (n / 2 + 1), (n.choose (2 * k) : ℂ) * eulerNumber (2 * k) *
      a (n - 2 * k) = ∑ k ∈ range (n + 1), (n.choose k : ℂ) * eulerNumber k * a (n - k) := by
    intro n
    rw [q24a_sum_half_eq (fun k => (n.choose k : ℂ) * eulerNumber k * a (n - k))]
    refine sum_congr rfl fun k _ => ?_
    split_ifs with h
    · rfl
    · rw [eulerNumber_eq_zero_of_odd (Nat.not_even_iff_odd.mp h)]; simp
  simp only [e1, e2]
  rw [q24a_egf_eq_mul_iff, q24a_egf_eq_mul_iff]
  have hSC := q24a_egf_euler_mul
  constructor
  · intro h; rw [h, ← mul_assoc, hSC, one_mul]
  · intro h; rw [h, ← mul_assoc, mul_comm (q24a_egf _) (q24a_egf (fun n => (eulerNumber n : ℂ))),
      hSC, one_mul]

end DLMF.BernoulliEuler
