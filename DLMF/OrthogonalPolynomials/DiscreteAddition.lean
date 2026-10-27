/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Hahn

/-!
# Addition formulas for discrete classical polynomials

Beals–Wong §6.3–§6.5, in the normalizations of the existing Charlier, Meixner,
and Krawtchouk definitions. Formal generating series prove the identities for complex
polynomial arguments without analytic convergence restrictions. The binomial-series
product is the existing Chu–Vandermonde identity; no new summability assumptions enter.
-/

@[expose] public noncomputable section

open Complex
open scoped Nat
open DLMF.Hypergeometric

namespace DLMF.OrthogonalPolynomials

namespace DiscreteAddition

open PowerSeries

/-- Multiplication of exponential generating series in binomial-coefficient notation. -/
theorem coeff_mul_factorial (f g : PowerSeries ℂ) (n : ℕ) :
    coeff n (f * g) * n ! =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) *
        (coeff k f * k !) * (coeff (n - k) g * (n - k) !) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [Nat.cast_choose ℂ hk']
  field_simp [Nat.cast_ne_zero.mpr k.factorial_ne_zero,
    Nat.cast_ne_zero.mpr (n - k).factorial_ne_zero]

/-- Formal exponential generating series of the Charlier polynomials. -/
def charlierSeries (a x : ℂ) : PowerSeries ℂ :=
  rescale a⁻¹ (binomSeries (-x)) * PowerSeries.exp ℂ

/-- The Charlier coefficients, including the totalized value at `a = 0`. -/
theorem coeff_charlierSeries (a x : ℂ) (n : ℕ) :
    coeff n (charlierSeries a x) * n ! = charlier a n x := by
  rw [charlierSeries, coeff_mul_factorial]
  unfold charlier terminatingHG
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [coeff_rescale, coeff_binomSeries, coeff_exp]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    map_div₀, map_one, map_natCast]
  rw [poch_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose, neg_pow]
  push_cast
  have hs : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
    rw [← mul_pow]; norm_num
  have hf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hg : ((n - k) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (n - k).factorial_ne_zero
  field_simp [hf, hg]
  linear_combination -(n.choose k * poch (-x) k * a⁻¹ ^ k) * hs

/-- Translation of the Charlier generating series. -/
theorem charlierSeries_add (a x y : ℂ) :
    charlierSeries a (x + y) =
      rescale a⁻¹ (binomSeries (-y)) * charlierSeries a x := by
  simp only [charlierSeries, ← mul_assoc, ← map_mul, binomSeries_mul]
  congr 2
  congr 1
  ring

/-- The fixed-parameter Charlier convolution has the correction factor `exp(-X)`. -/
theorem charlierSeries_add_fixed (a x y : ℂ) :
    charlierSeries a (x + y) =
      PowerSeries.evalNegHom (PowerSeries.exp ℂ) *
        (charlierSeries a x * charlierSeries a y) := by
  unfold charlierSeries
  have hb : rescale a⁻¹ (binomSeries (-(x + y))) =
      rescale a⁻¹ (binomSeries (-x)) * rescale a⁻¹ (binomSeries (-y)) := by
    rw [← map_mul, binomSeries_mul, neg_add]
  rw [hb]
  linear_combination -(rescale a⁻¹ (binomSeries (-x)) *
    rescale a⁻¹ (binomSeries (-y)) * PowerSeries.exp ℂ) *
      (PowerSeries.exp_mul_exp_neg_eq_one (A := ℂ))

/-- Formal exponential generating series of `(β)_n M_n(x;β,c)`. -/
def meixnerSeries (β c x : ℂ) : PowerSeries ℂ :=
  rescale c⁻¹ (binomSeries (-x)) * binomSeries (x + β)

/-- Meixner coefficients with only the finite denominator restrictions needed at degree `n`. -/
theorem coeff_meixnerSeries {β c : ℂ} (n : ℕ)
    (hβ : ∀ k ≤ n, poch β k ≠ 0) (x : ℂ) :
    coeff n (meixnerSeries β c x) * n ! = poch β n * meixner β c n x := by
  rw [meixnerSeries, coeff_mul_factorial, poch_mul_meixner_eq_sum_of_ne_zero n hβ]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [coeff_rescale, coeff_binomSeries]
  have hf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hg : ((n - k) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (n - k).factorial_ne_zero
  field_simp

/-- Addition of both the argument and the Meixner parameter. -/
theorem meixnerSeries_add (β γ c x y : ℂ) :
    meixnerSeries (β + γ) c (x + y) = meixnerSeries β c x * meixnerSeries γ c y := by
  unfold meixnerSeries
  conv_rhs => rw [mul_mul_mul_comm, ← map_mul, binomSeries_mul, binomSeries_mul]
  rw [show -x + -y = -(x + y) by ring,
    show x + β + (y + γ) = x + y + (β + γ) by ring]

/-- The correction factor for addition at fixed Meixner parameter. -/
theorem meixnerSeries_add_fixed (β c x y : ℂ) :
    meixnerSeries β c (x + y) =
      binomSeries (-β) * (meixnerSeries β c x * meixnerSeries β c y) := by
  rw [← meixnerSeries_add]
  unfold meixnerSeries
  rw [mul_left_comm, binomSeries_mul]
  rw [show -β + (x + y + (β + β)) = x + y + β by ring]

/-- Formal generating series in Beals–Wong's Krawtchouk normalization. -/
def krawtchoukSeries (p : ℂ) (N : ℕ) (x : ℂ) : PowerSeries ℂ :=
  rescale p (meixnerSeries (-(N : ℂ)) (1 - p⁻¹)⁻¹ x)

/-- Krawtchouk coefficients up to degree `N`; the finite denominator factors are nonzero. -/
theorem coeff_krawtchoukSeries (p : ℂ) (N n : ℕ) (hn : n ≤ N) (x : ℂ) :
    coeff n (krawtchoukSeries p N x) * n ! =
      poch (-(N : ℂ)) n * p ^ n * krawtchouk p N n x := by
  have hb : ∀ k ≤ n, poch (-(N : ℂ)) k ≠ 0 := by
    intro k hk
    rw [poch_neg_coe_nat]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Nat.cast_ne_zero.mpr (Nat.descFactorial_pos.mpr (hk.trans hn)).ne')
  rw [krawtchoukSeries, coeff_rescale, mul_assoc, coeff_meixnerSeries n hb]
  simp only [meixner, krawtchouk, inv_inv, sub_sub_cancel]
  ring

/-- The Krawtchouk convolution correction is `(1-pX)^{-N}`. -/
theorem krawtchoukSeries_add (p : ℂ) (N : ℕ) (x y : ℂ) :
    krawtchoukSeries p N (x + y) =
      rescale p (binomSeries (N : ℂ)) *
        (krawtchoukSeries p N x * krawtchoukSeries p N y) := by
  simpa only [krawtchoukSeries, map_mul, neg_neg] using
    congrArg (rescale p) (meixnerSeries_add_fixed (-(N : ℂ)) (1 - p⁻¹)⁻¹ x y)

end DiscreteAddition

open DiscreteAddition PowerSeries

/-- Charlier translation formula, Beals–Wong (6.3.11), for arbitrary complex arguments. -/
theorem charlier_addition (a x y : ℂ) (n : ℕ) :
    charlier a n (x + y) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) *
        charlier a (n - k) x * poch (-y) k / a ^ k := by
  rw [← coeff_charlierSeries, charlierSeries_add, coeff_mul_factorial]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_charlierSeries, coeff_rescale, coeff_binomSeries]
  have hf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  simp only [div_eq_mul_inv, inv_pow]
  simp only [mul_assoc, inv_mul_cancel₀ hf, mul_one]
  ring

/-- Charlier convolution at fixed parameter, Beals–Wong (6.3.10). The nested ranges
encode the triples of nonnegative integers with sum `n`. -/
theorem charlier_addition_convolution (a x y : ℂ) (n : ℕ) :
    charlier a n (x + y) =
      ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n - j + 1),
        (n.choose j : ℂ) * ((n - j).choose k : ℂ) * (-1 : ℂ) ^ j *
          charlier a k x * charlier a (n - j - k) y := by
  rw [← coeff_charlierSeries, charlierSeries_add_fixed, coeff_mul_factorial]
  refine Finset.sum_congr rfl fun j _ => ?_
  have he : coeff j (PowerSeries.evalNegHom (PowerSeries.exp ℂ)) * j ! = (-1 : ℂ) ^ j := by
    simp only [PowerSeries.evalNegHom, coeff_rescale, coeff_exp,
      map_div₀, map_one, map_natCast]
    field_simp [Nat.cast_ne_zero.mpr j.factorial_ne_zero]
  rw [he, coeff_mul_factorial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_charlierSeries, coeff_charlierSeries]
  ring

/-- Meixner addition formula, Beals–Wong (6.5.11), in the project's standard normalization. -/
theorem meixner_addition {β : ℂ} (hβ : 0 < β.re) (c x y : ℂ) (n : ℕ) :
    poch β n * meixner β c n (x + y) =
      ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n - j + 1),
        (n.choose j : ℂ) * ((n - j).choose k : ℂ) * poch (-β) j *
          (poch β k * meixner β c k x) *
          (poch β (n - j - k) * meixner β c (n - j - k) y) := by
  have hb (m : ℕ) : ∀ k ≤ m, poch β k ≠ 0 :=
    fun k _ => poch_ne_zero_of_re_pos hβ k
  rw [← coeff_meixnerSeries n (hb n), meixnerSeries_add_fixed, coeff_mul_factorial]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_binomSeries, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr j.factorial_ne_zero),
    coeff_mul_factorial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_meixnerSeries k (hb k), coeff_meixnerSeries (n - j - k) (hb (n - j - k))]
  ring

/-- Krawtchouk convolution, Beals–Wong (6.4.12), after translating its normalization:
`k_n = (-N)_n p^n K_n/n!`. Multiplication by `n!` avoids quotients in the convolution. -/
theorem krawtchouk_addition (p x y : ℂ) {N n : ℕ} (hn : n ≤ N) :
    poch (-(N : ℂ)) n * p ^ n * krawtchouk p N n (x + y) =
      ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n - j + 1),
        (n.choose j : ℂ) * ((n - j).choose k : ℂ) * poch (N : ℂ) j * p ^ j *
          (poch (-(N : ℂ)) k * p ^ k * krawtchouk p N k x) *
          (poch (-(N : ℂ)) (n - j - k) * p ^ (n - j - k) *
            krawtchouk p N (n - j - k) y) := by
  rw [← coeff_krawtchoukSeries p N n hn, krawtchoukSeries_add, coeff_mul_factorial]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have he : coeff j (rescale p (binomSeries (N : ℂ))) * j ! = p ^ j * poch (N : ℂ) j := by
    rw [coeff_rescale, coeff_binomSeries]
    field_simp [Nat.cast_ne_zero.mpr j.factorial_ne_zero]
  rw [he, coeff_mul_factorial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n - j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [coeff_krawtchoukSeries p N k (by omega),
    coeff_krawtchoukSeries p N (n - j - k) (by omega)]
  ring

end DLMF.OrthogonalPolynomials
