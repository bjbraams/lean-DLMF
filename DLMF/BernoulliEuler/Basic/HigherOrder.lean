/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.Basic.GeneratingFunctions

/-!
# Higher-order Bernoulli and Euler polynomials

The Bernoulli and Euler polynomials of order `ℓ` and the Nörlund polynomials `B_n^{(x)}` of DLMF
§24.16(i), all defined by finite formulas, with the generating function of the Bernoulli
polynomials of order `ℓ` and their values at `0`.

## Main definitions

* `norlundPolynomial n : ℚ[X]`: the Nörlund polynomial `B_n^{(x)}` of DLMF 24.16.9 as a
  polynomial in the order `x`.
* `bernoulliNumberOrder`, `bernoulliOrder`: `B_n^{(ℓ)}` and the polynomial
  `B_n^{(ℓ)}(x) = ∑ₖ (n choose k) B_k^{(ℓ)} x^{n-k}` (DLMF 24.16.3, 24.16.1).
* `eulerNumberOrder`, `eulerOrder`: the same for the Euler polynomials (DLMF 24.16.3, 24.16.2).

## Main results

* `bernoulliNumberOrder_one`: `B_n^{(1)} = Bₙ`.
* `bernoulliNumberOrder_eq_factorial_mul_coeff`, `eulerNumberOrder_eq_factorial_mul_coeff`:
  the numbers of order `ℓ` as coefficients of `(t/(eᵗ-1))^ℓ` and `(2/(eᵗ+1))^ℓ`.
* `hasSum_bernoulliOrder`: the generating function DLMF 24.16.1.
* `bernoulliOrder_eval_zero`, `eulerOrder_eval_zero`: DLMF 24.16.3.

## Implementation notes

If `g(t) = t/(eᵗ - 1) - 1` (Mathlib's `bernoulliPowerSeries`, minus `1`), then
`(1 + g)^x = ∑ⱼ (x choose j) gʲ` and only `j ≤ n` contribute to the coefficient of `tⁿ`; so
`B_n^{(x)} = n! ∑_{j ≤ n} [tⁿ] gʲ · x(x-1)⋯(x-j+1)/j!` (`descPochhammer`). This is the
formal-power-series meaning of `(t/(eᵗ-1))^x`, the branch equal to `1` at `t = 0`. The
coefficient form of 24.16.1 comes from the factor `e^{xt}` contributing `x^{n-k}/(n-k)!`; the
Euler analogues use `2/(eᵗ + 1) = ∑ Eₙ(0) tⁿ/n!`. The generating function 24.16.1 is stated as
`HasSum` in `ℂ` for `t ≠ 0` and proved by summing the Cauchy products of the absolutely
convergent series of `t/(eᵗ-1)` and `e^{xt}`.

The generating function 24.16.2 needs the series of `2/(eᵗ+1)` on the full disc `|t| < π`, which
comes from the Elementary theorem layer; it and the rest of §24.16 are in
`DLMF.BernoulliEuler.Generalizations.HigherOrder`.
-/

@[expose] public noncomputable section

open Polynomial Finset Filter Topology

open scoped Nat Real

namespace DLMF.BernoulliEuler

/-- The coefficient of `tⁿ` in `(1 + g(t))^x`, as a polynomial in `x`, for a power series `g`
with zero constant term: `∑_{j ≤ n} [tⁿ] gʲ · x(x-1)⋯(x-j+1)/j!`. -/
def binomialSeriesCoeff (g : PowerSeries ℚ) (n : ℕ) : ℚ[X] :=
  ∑ j ∈ range (n + 1), C (PowerSeries.coeff n (g ^ j) / j !) * descPochhammer ℚ j

/-- DLMF 24.16.9: the Nörlund polynomial `B_n^{(x)}`, as a polynomial in the order `x`, defined
by `(t/(eᵗ-1))^x = ∑ₙ B_n^{(x)} tⁿ/n!` in the sense of formal power series. -/
@[dlmf 24.16.E9]
def norlundPolynomial (n : ℕ) : ℚ[X] :=
  (n ! : ℚ) • binomialSeriesCoeff (bernoulliPowerSeries ℚ - 1) n

/-- DLMF 24.16.3: the Bernoulli numbers of order `ℓ`, `B_n^{(ℓ)} = B_n^{(ℓ)}(0)`. -/
@[dlmf 24.16.E3]
def bernoulliNumberOrder (ℓ n : ℕ) : ℚ := (norlundPolynomial n).eval (ℓ : ℚ)

/-- DLMF 24.16.1: the Bernoulli polynomials of order `ℓ`,
`B_n^{(ℓ)}(x) = ∑ₖ (n choose k) B_k^{(ℓ)} x^{n-k}`. -/
@[dlmf 24.16.E1]
def bernoulliOrder (ℓ n : ℕ) : ℚ[X] :=
  ∑ k ∈ range (n + 1), C ((n.choose k : ℚ) * bernoulliNumberOrder ℓ k) * X ^ (n - k)

/-- Consistency check of the definition: `B_n^{(1)} = Bₙ`. -/
theorem bernoulliNumberOrder_one (n : ℕ) : bernoulliNumberOrder 1 n = _root_.bernoulli n := by
  rw [bernoulliNumberOrder, norlundPolynomial, binomialSeriesCoeff, eval_smul, eval_finsetSum,
    smul_eq_mul]
  rcases n with _ | n
  · simp [bernoulliPowerSeries]
  rw [sum_range_succ', sum_range_succ', Finset.sum_eq_zero]
  · simp [bernoulliPowerSeries]
    field_simp
  · intro j hj
    rw [eval_mul, eval_C, descPochhammer_eval_coe_nat_of_lt (by omega), mul_zero]

/-- The power series `2/(eᵗ + 1) = ∑ Eₙ(0) tⁿ/n!`. -/
def eulerPowerSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => (Polynomial.euler n).eval 0 / n !

/-- DLMF 24.16.3: the Euler numbers of order `ℓ`, `E_n^{(ℓ)} = E_n^{(ℓ)}(0)`, the coefficients of
`(2/(eᵗ+1))^ℓ`. -/
@[dlmf 24.16.E3]
def eulerNumberOrder (ℓ n : ℕ) : ℚ :=
  (n ! : ℚ) * (binomialSeriesCoeff (eulerPowerSeries - 1) n).eval (ℓ : ℚ)

/-- DLMF 24.16.2: the Euler polynomials of order `ℓ`,
`E_n^{(ℓ)}(x) = ∑ₖ (n choose k) E_k^{(ℓ)} x^{n-k}`. -/
@[dlmf 24.16.E2]
def eulerOrder (ℓ n : ℕ) : ℚ[X] :=
  ∑ k ∈ range (n + 1), C ((n.choose k : ℚ) * eulerNumberOrder ℓ k) * X ^ (n - k)

/-! ### Powers of power series (helpers for §24.16(i)) -/

/-- If `g` has zero constant term, `[tⁿ] gⁿ = ([t] g)ⁿ`. -/
lemma coeff_pow_self_of_constantCoeff_eq_zero (g : PowerSeries ℚ)
    (hg : PowerSeries.constantCoeff g = 0) (n : ℕ) :
    PowerSeries.coeff n (g ^ n) = (PowerSeries.coeff 1 g) ^ n := by
  obtain ⟨h, rfl⟩ := PowerSeries.X_dvd_iff.mpr hg
  rw [mul_pow, PowerSeries.coeff_X_pow_mul']
  simp only [le_refl, ite_true, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_pow]
  rw [show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- If `g` has zero constant term, `[tⁿ] gʲ = 0` for `j > n`. -/
private lemma coeff_pow_eq_zero_of_lt (g : PowerSeries ℚ) (hg : PowerSeries.constantCoeff g = 0)
    {n j : ℕ} (hj : n < j) : PowerSeries.coeff n (g ^ j) = 0 := by
  obtain ⟨h, rfl⟩ := PowerSeries.X_dvd_iff.mpr hg
  rw [mul_pow, PowerSeries.coeff_X_pow_mul']
  simp only [show ¬ j ≤ n by omega, ite_false]

/-- The coefficient polynomial `binomialSeriesCoeff` at a natural number `ℓ` is the coefficient of
the `ℓ`-th power. -/
private lemma binomialSeriesCoeff_eval_natCast (G : PowerSeries ℚ)
    (hG : PowerSeries.constantCoeff G = 1) (ℓ n : ℕ) :
    (binomialSeriesCoeff (G - 1) n).eval (ℓ : ℚ) = PowerSeries.coeff n (G ^ ℓ) := by
  set g := G - 1
  have hg : PowerSeries.constantCoeff g = 0 := by simp [g, hG]
  have hG' : G = g + 1 := by simp [g]
  rw [hG', add_pow]
  simp only [one_pow, mul_one, map_sum]
  have hR : ∀ j, PowerSeries.coeff n (g ^ j * (ℓ.choose j : PowerSeries ℚ)) =
      PowerSeries.coeff n (g ^ j) * ℓ.choose j := by
    intro j
    rw [← map_natCast (PowerSeries.C (R := ℚ)), PowerSeries.coeff_mul_C]
  simp only [hR]
  rw [binomialSeriesCoeff, eval_finsetSum]
  have hL : ∀ j, (C (PowerSeries.coeff n (g ^ j) / j !) * descPochhammer ℚ j).eval (ℓ : ℚ) =
      PowerSeries.coeff n (g ^ j) * ℓ.choose j := by
    intro j
    rw [eval_mul, eval_C, descPochhammer_eval_eq_descFactorial,
      Nat.descFactorial_eq_factorial_mul_choose]
    have : (j ! : ℚ) ≠ 0 := by positivity
    push_cast; field_simp
  simp only [hL]
  rw [sum_subset (range_subset_range.mpr (show n + 1 ≤ n + ℓ + 1 by omega)),
    sum_subset (range_subset_range.mpr (show ℓ + 1 ≤ n + ℓ + 1 by omega))]
  · intro j _ hj
    rw [Nat.choose_eq_zero_of_lt (by simp at hj; omega)]; simp
  · intro j _ hj
    rw [coeff_pow_eq_zero_of_lt g hg (by simp at hj; omega)]; simp

/-- Termwise product of the series of `F` and `G` at `t` is the series of `F * G`. -/
private lemma coeff_mul_mul_pow_eq_sum (F G : PowerSeries ℚ) (t : ℂ) (n : ℕ) :
    ((PowerSeries.coeff n (F * G) : ℚ) : ℂ) * t ^ n =
      ∑ k ∈ range (n + 1), ((PowerSeries.coeff k F : ℚ) * t ^ k) *
        ((PowerSeries.coeff (n - k) G : ℚ) * t ^ (n - k)) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  push_cast
  rw [sum_mul]
  refine sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [show t ^ n = t ^ k * t ^ (n - k) by rw [← pow_add, Nat.add_sub_cancel' hkn]]
  ring

/-- Absolute convergence of a power series with rational coefficients passes to powers. -/
lemma hasSum_coeff_pow_mul_pow (G : PowerSeries ℚ) {t v : ℂ}
    (hs : Summable fun n => ‖((PowerSeries.coeff n G : ℚ) : ℂ) * t ^ n‖)
    (h : HasSum (fun n => ((PowerSeries.coeff n G : ℚ) : ℂ) * t ^ n) v) (ℓ : ℕ) :
    Summable (fun n => ‖((PowerSeries.coeff n (G ^ ℓ) : ℚ) : ℂ) * t ^ n‖) ∧
      HasSum (fun n => ((PowerSeries.coeff n (G ^ ℓ) : ℚ) : ℂ) * t ^ n) (v ^ ℓ) := by
  induction ℓ with
  | zero =>
    have hf : (fun n => ((PowerSeries.coeff n (G ^ 0) : ℚ) : ℂ) * t ^ n) =
        fun n => if n = 0 then 1 else 0 := by
      funext n; rcases n with _ | n <;> simp [PowerSeries.coeff_one]
    refine ⟨(hasSum_ite_eq 0 (1 : ℝ)).summable.congr fun n => ?_, ?_⟩
    · rw [congrFun hf n]; split_ifs <;> simp
    · rw [hf]; simpa using hasSum_ite_eq 0 (1 : ℂ)
  | succ ℓ ih =>
    have hprod := hasSum_sum_range_mul_of_summable_norm ih.1 hs
    have hsum := summable_norm_sum_mul_range_of_summable_norm ih.1 hs
    rw [ih.2.tsum_eq, h.tsum_eq] at hprod
    simp only [pow_succ, coeff_mul_mul_pow_eq_sum]
    exact ⟨hsum, hprod⟩

/-- `B_n^{(ℓ)} = n! [tⁿ] (t/(eᵗ-1))^ℓ`. -/
lemma bernoulliNumberOrder_eq_factorial_mul_coeff (ℓ n : ℕ) :
    bernoulliNumberOrder ℓ n = n ! * PowerSeries.coeff n (bernoulliPowerSeries ℚ ^ ℓ) := by
  rw [bernoulliNumberOrder, norlundPolynomial, eval_smul, smul_eq_mul,
    binomialSeriesCoeff_eval_natCast _ (by simp [bernoulliPowerSeries])]

/-- `E_n^{(ℓ)} = n! [tⁿ] (2/(eᵗ+1))^ℓ`. -/
lemma eulerNumberOrder_eq_factorial_mul_coeff (ℓ n : ℕ) :
    eulerNumberOrder ℓ n = n ! * PowerSeries.coeff n (eulerPowerSeries ^ ℓ) := by
  rw [eulerNumberOrder, binomialSeriesCoeff_eval_natCast _ (by simp [eulerPowerSeries])]

/-- Evaluation of `∑ₖ (n choose k) cₖ X^{n-k}`. -/
lemma aeval_sum_C_choose_mul_X_pow (c : ℕ → ℚ) (n : ℕ) (x : ℂ) :
    aeval x (∑ k ∈ range (n + 1), C ((n.choose k : ℚ) * c k) * X ^ (n - k)) =
      ∑ k ∈ range (n + 1), (n.choose k : ℂ) * (c k : ℂ) * x ^ (n - k) := by
  simp [map_sum]

/-- DLMF 24.16.1: `(t/(eᵗ - 1))^ℓ e^{xt} = ∑ₙ B_n^{(ℓ)}(x) tⁿ/n!` for `0 < |t| < 2π`. -/
@[dlmf 24.16.E1]
theorem hasSum_bernoulliOrder (ℓ : ℕ) (x : ℂ) {t : ℂ} (ht : ‖t‖ < 2 * π) (ht0 : t ≠ 0) :
    HasSum (fun n : ℕ => aeval x (bernoulliOrder ℓ n) * t ^ n / n !)
      ((t / (Complex.exp t - 1)) ^ ℓ * Complex.exp (x * t)) := by
  have hcoef : ∀ n, ((PowerSeries.coeff n (bernoulliPowerSeries ℚ) : ℚ) : ℂ) =
      (_root_.bernoulli n : ℂ) / n ! := by
    intro n; simp [bernoulliPowerSeries]
  have hsum : ∀ z : ℂ, ‖z‖ < 2 * π →
      Summable (fun n => ((PowerSeries.coeff n (bernoulliPowerSeries ℚ) : ℚ) : ℂ) * z ^ n) := by
    intro z hz
    by_cases hz0 : z = 0
    · subst hz0
      exact (hasSum_single 0 (fun n hn => by simp [zero_pow hn])).summable
    · exact ((Complex.hasSum_bernoulli_mul_pow_div hz hz0).congr_fun
        fun n => by rw [hcoef]; ring).summable
  have h0 : HasSum (fun n => ((PowerSeries.coeff n (bernoulliPowerSeries ℚ) : ℚ) : ℂ) * t ^ n)
      (t / (Complex.exp t - 1)) :=
    (Complex.hasSum_bernoulli_mul_pow_div ht ht0).congr_fun fun n => by rw [hcoef]; ring
  obtain ⟨hs, h⟩ := hasSum_coeff_pow_mul_pow _ (summable_norm_mul_pow_of_summable hsum ht) h0 ℓ
  have hterm : ∀ n, (bernoulliNumberOrder ℓ n : ℂ) * t ^ n / n ! =
      ((PowerSeries.coeff n (bernoulliPowerSeries ℚ ^ ℓ) : ℚ) : ℂ) * t ^ n := by
    intro n
    rw [bernoulliNumberOrder_eq_factorial_mul_coeff]; push_cast
    have : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    field_simp
  have := hasSum_binomialConv_mul_exp (w := x) (hs.congr fun n => by rw [hterm])
    (h.congr_fun fun n => hterm n)
  refine this.congr_fun fun n => ?_
  rw [bernoulliOrder, aeval_sum_C_choose_mul_X_pow]

/-- DLMF 24.16.3: `B_n^{(ℓ)} = B_n^{(ℓ)}(0)`. -/
@[dlmf 24.16.E3]
theorem bernoulliOrder_eval_zero (ℓ n : ℕ) :
    (bernoulliOrder ℓ n).eval 0 = bernoulliNumberOrder ℓ n := by
  rw [bernoulliOrder, eval_finsetSum, sum_range_succ, Finset.sum_eq_zero]
  · simp
  · intro k hk
    have : n - k ≠ 0 := by have := mem_range.mp hk; omega
    simp [zero_pow this]

/-- DLMF 24.16.3: `E_n^{(ℓ)} = E_n^{(ℓ)}(0)`. -/
@[dlmf 24.16.E3]
theorem eulerOrder_eval_zero (ℓ n : ℕ) :
    (eulerOrder ℓ n).eval 0 = eulerNumberOrder ℓ n := by
  rw [eulerOrder, eval_finsetSum, sum_range_succ, Finset.sum_eq_zero]
  · simp
  · intro k hk
    have : n - k ≠ 0 := by have := mem_range.mp hk; omega
    simp [zero_pow this]

end DLMF.BernoulliEuler
