/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.Basic
public import DLMF.BernoulliEuler.GeneratingFunctions
public import DLMF.Combinatorics.Stirling
public import DLMFMathlib.NumberTheory.EulerNumbers
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Generalizations of Bernoulli and Euler polynomials (DLMF §24.16)

## Definitions (genuine, by finite formulas)

* `norlundPolynomial n : ℚ[X]`: the Nörlund polynomial `B_n^{(x)}` of 24.16.9 as a polynomial in
  the order `x`. If `g(t) = t/(eᵗ - 1) - 1` (Mathlib's `bernoulliPowerSeries`, minus `1`), then
  `(1 + g)^x = ∑ⱼ (x choose j) gʲ` and only `j ≤ n` contribute to the coefficient of `tⁿ`; so
  `B_n^{(x)} = n! ∑_{j ≤ n} [tⁿ] gʲ · x(x-1)⋯(x-j+1)/j!` (`descPochhammer`). This is the
  formal-power-series meaning of `(t/(eᵗ-1))^x`, the branch equal to `1` at `t = 0`.
* `bernoulliNumberOrder ℓ n = B_n^{(ℓ)}` (24.16.3) and `bernoulliOrder ℓ n : ℚ[X]`, the
  polynomial `B_n^{(ℓ)}(x) = ∑ₖ (n choose k) B_k^{(ℓ)} x^{n-k}` (the coefficient form of
  24.16.1, the factor `e^{xt}` contributing `x^{n-k}/(n-k)!`).
* `eulerNumberOrder ℓ n = E_n^{(ℓ)}` and `eulerOrder ℓ n` for 24.16.2, in the same way from
  `2/(eᵗ + 1) = ∑ Eₙ(0) tⁿ/n!`.
* `bernoulliSecondKind n = bₙ = ∫₀¹ (x choose n) dx` (24.16.5), written through the coefficients
  of `descPochhammer`: `bₙ = (1/n!) ∑ₖ [xᵏ] x(x-1)⋯(x-n+1) / (k+1)`.
* `degenerateBernoulli n : ℚ[X]`, the degenerate Bernoulli number `βₙ(λ)` (24.16.7) as a
  polynomial in `λ`: `((1 + λt)^{1/λ} - 1)/t = ∑ₖ (1-λ)(1-2λ)⋯(1-kλ) tᵏ/(k+1)!` has constant
  term `1`, and `βₙ(λ)/n!` is the `n`-th coefficient of its inverse (`PowerSeries.invOfUnit`).
* `bernoulliChar χ n = B_{n,χ}` (24.16.10) for a Dirichlet character `χ` modulo `f`, defined by
  the classical closed form `B_{n,χ} = f^{n-1} ∑_{a=1}^{f} χ(a) Bₙ(a/f)`; the generating function
  24.16.10 is a theorem. DLMF requires `χ` primitive (with `f` its conductor); the definition and
  the generating function make sense for every `χ` modulo `f ≥ 1`. `bernoulliCharPoly` is
  24.16.11.

## Generating functions and branches

DLMF's generating functions are stated as `HasSum` in `ℂ` for `t ≠ 0` (at `t = 0` the Lean
quotients are totalized). For the Nörlund polynomials of complex order (24.16.9) DLMF's power
`(t/(eᵗ-1))^x` is the branch analytic in `|t| < 2π` and equal to `1` at `0`; the principal power
`cpow` agrees with it only while `t/(eᵗ-1)` has not crossed the negative axis. Numerically the
principal argument stays below `π` for `|t| < 4.8`; we state 24.16.9 for complex `x` and
`0 < ‖t‖ < π`, and for real `x` and real `0 < |t| < 2π` (where `t/(eᵗ-1) > 0`). The degenerate
Bernoulli generating function 24.16.7 ("for sufficiently small `|t|`") is stated for `λ ≠ 0`
eventually in the punctured neighbourhood of `0`, with the principal power `(1 + λt)^{1/λ}`.

## Status

The generating functions 24.16.1, 24.16.2 and 24.16.10 are proved by summing the Cauchy
products of the absolutely convergent series of `t/(eᵗ-1)`, `2/(eᵗ+1)` and `e^{xt}`;
`natDegree_norlundPolynomial` is proved. The formal identity `t β' = β - tβ - β²` for
`β = t/(eᵗ-1)` gives the Nörlund recurrence
`a B_{n+1}^{(a+1)}(x) = (a-n-1) B_{n+1}^{(a)}(x) + (n+1)(x-a) B_n^{(a)}(x)`, hence
`B_n^{(n+1)}(x) = (x-1)⋯(x-n)`; with `∫₀¹ B_n^{(a+1)} = B_n^{(a)}` this proves 24.16.6, and with
the differential equation of `(ln(1+t)/t)^ℓ` it proves 24.16.4. 24.16.5 is proved by integrating
the binomial series `(1+t)^x = ∑ (x choose n) tⁿ` over `0 ≤ x ≤ 1`. 24.16.7 is proved for
`|t| < 1/(4(1+|λ|))` from the binomial series of `(1 + λt)^{1/λ}`, a geometric bound on the
coefficients of the formal inverse and the Cauchy product. The generating function 24.16.9 is
proved from a holomorphic logarithm `L` of `t/(eᵗ-1)` on `|t| < 2π` (a primitive of the
logarithmic derivative): the Taylor coefficients of `e^{xL}` are polynomials in `x` that agree
with `B_n^{(ℓ)}` at `x = ℓ ∈ ℕ`. The identity 24.16.8 is proved for real `0 < λ < 1/4` by writing
`(1+λt)^{1/λ} = eᵘ`, `u = ln(1+λt)/λ`, expanding `t/(eᵘ-1)` with 24.2.1, 24.16.5 and the
Stirling generating function 26.8.8 (`DLMF.Combinatorics.Stirling`), rearranging the absolutely
convergent double series and comparing coefficients with 24.16.7; agreement for infinitely many
`λ` gives the identity in `ℚ[λ]`. The file has no admissions.

## References

* NIST DLMF §24.16; Nörlund (1924), Milne-Thomson (1933), Carlitz (1979), Berndt (1975a).
-/

@[expose] public noncomputable section

open Polynomial Finset Filter Topology
open scoped Nat Real

namespace DLMF.BernoulliEuler

/-! ### §24.16(i) Higher-order analogs -/

/-- The coefficient of `tⁿ` in `(1 + g(t))^x`, as a polynomial in `x`, for a power series `g`
with zero constant term: `∑_{j ≤ n} [tⁿ] gʲ · x(x-1)⋯(x-j+1)/j!`. -/
def b24b_powCoeff (g : PowerSeries ℚ) (n : ℕ) : ℚ[X] :=
  ∑ j ∈ range (n + 1), C (PowerSeries.coeff n (g ^ j) / j !) * descPochhammer ℚ j

/-- DLMF 24.16.9: the Nörlund polynomial `B_n^{(x)}`, as a polynomial in the order `x`, defined
by `(t/(eᵗ-1))^x = ∑ₙ B_n^{(x)} tⁿ/n!` in the sense of formal power series. -/
@[dlmf 24.16.E9]
def norlundPolynomial (n : ℕ) : ℚ[X] :=
  (n ! : ℚ) • b24b_powCoeff (bernoulliPowerSeries ℚ - 1) n

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
  rw [bernoulliNumberOrder, norlundPolynomial, b24b_powCoeff, eval_smul, eval_finsetSum,
    smul_eq_mul]
  rcases n with _ | n
  · simp [bernoulliPowerSeries]
  rw [sum_range_succ', sum_range_succ', Finset.sum_eq_zero]
  · simp [bernoulliPowerSeries]
    field_simp
  · intro j hj
    rw [eval_mul, eval_C, descPochhammer_eval_coe_nat_of_lt (by omega), mul_zero]

/-- The power series `2/(eᵗ + 1) = ∑ Eₙ(0) tⁿ/n!`. -/
def b24b_eulerZeroSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => (Polynomial.euler n).eval 0 / n !

/-- DLMF 24.16.3: the Euler numbers of order `ℓ`, `E_n^{(ℓ)} = E_n^{(ℓ)}(0)`, the coefficients of
`(2/(eᵗ+1))^ℓ`. -/
@[dlmf 24.16.E3]
def eulerNumberOrder (ℓ n : ℕ) : ℚ :=
  (n ! : ℚ) * (b24b_powCoeff (b24b_eulerZeroSeries - 1) n).eval (ℓ : ℚ)

/-- DLMF 24.16.2: the Euler polynomials of order `ℓ`,
`E_n^{(ℓ)}(x) = ∑ₖ (n choose k) E_k^{(ℓ)} x^{n-k}`. -/
@[dlmf 24.16.E2]
def eulerOrder (ℓ n : ℕ) : ℚ[X] :=
  ∑ k ∈ range (n + 1), C ((n.choose k : ℚ) * eulerNumberOrder ℓ k) * X ^ (n - k)

/-! ### Powers of power series (helpers for §24.16(i)) -/

/-- If `g` has zero constant term, `[tⁿ] gⁿ = ([t] g)ⁿ`. -/
theorem q24b_coeff_pow_self (g : PowerSeries ℚ) (hg : PowerSeries.constantCoeff g = 0) (n : ℕ) :
    PowerSeries.coeff n (g ^ n) = (PowerSeries.coeff 1 g) ^ n := by
  obtain ⟨h, rfl⟩ := PowerSeries.X_dvd_iff.mpr hg
  rw [mul_pow, PowerSeries.coeff_X_pow_mul']
  simp only [le_refl, ite_true, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_pow]
  rw [show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- If `g` has zero constant term, `[tⁿ] gʲ = 0` for `j > n`. -/
theorem q24b_coeff_pow_of_lt (g : PowerSeries ℚ) (hg : PowerSeries.constantCoeff g = 0) {n j : ℕ}
    (hj : n < j) : PowerSeries.coeff n (g ^ j) = 0 := by
  obtain ⟨h, rfl⟩ := PowerSeries.X_dvd_iff.mpr hg
  rw [mul_pow, PowerSeries.coeff_X_pow_mul']
  simp only [show ¬ j ≤ n by omega, ite_false]

/-- The coefficient polynomial `b24b_powCoeff` at a natural number `ℓ` is the coefficient of
the `ℓ`-th power. -/
theorem q24b_powCoeff_eval_natCast (G : PowerSeries ℚ) (hG : PowerSeries.constantCoeff G = 1)
    (ℓ n : ℕ) : (b24b_powCoeff (G - 1) n).eval (ℓ : ℚ) = PowerSeries.coeff n (G ^ ℓ) := by
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
  rw [b24b_powCoeff, eval_finsetSum]
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
    rw [q24b_coeff_pow_of_lt g hg (by simp at hj; omega)]; simp

/-- Termwise product of the series of `F` and `G` at `t` is the series of `F * G`. -/
theorem q24b_coeff_mul_pow (F G : PowerSeries ℚ) (t : ℂ) (n : ℕ) :
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
theorem q24b_hasSum_pow (G : PowerSeries ℚ) {t v : ℂ}
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
    simp only [pow_succ, q24b_coeff_mul_pow]
    exact ⟨hsum, hprod⟩

/-- `B_n^{(ℓ)} = n! [tⁿ] (t/(eᵗ-1))^ℓ`. -/
theorem q24b_bernoulliNumberOrder_eq (ℓ n : ℕ) :
    bernoulliNumberOrder ℓ n = n ! * PowerSeries.coeff n (bernoulliPowerSeries ℚ ^ ℓ) := by
  rw [bernoulliNumberOrder, norlundPolynomial, eval_smul, smul_eq_mul,
    q24b_powCoeff_eval_natCast _ (by simp [bernoulliPowerSeries])]

/-- `E_n^{(ℓ)} = n! [tⁿ] (2/(eᵗ+1))^ℓ`. -/
theorem q24b_eulerNumberOrder_eq (ℓ n : ℕ) :
    eulerNumberOrder ℓ n = n ! * PowerSeries.coeff n (b24b_eulerZeroSeries ^ ℓ) := by
  rw [eulerNumberOrder, q24b_powCoeff_eval_natCast _ (by simp [b24b_eulerZeroSeries])]

/-- Evaluation of `∑ₖ (n choose k) cₖ X^{n-k}`. -/
theorem q24b_aeval_order (c : ℕ → ℚ) (n : ℕ) (x : ℂ) :
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
  obtain ⟨hs, h⟩ := q24b_hasSum_pow _ (b24a_summable_norm_of_summable hsum ht) h0 ℓ
  have hterm : ∀ n, (bernoulliNumberOrder ℓ n : ℂ) * t ^ n / n ! =
      ((PowerSeries.coeff n (bernoulliPowerSeries ℚ ^ ℓ) : ℚ) : ℂ) * t ^ n := by
    intro n
    rw [q24b_bernoulliNumberOrder_eq]; push_cast
    have : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    field_simp
  have := b24a_hasSum_mul_exp (w := x) (hs.congr fun n => by rw [hterm])
    (h.congr_fun fun n => hterm n)
  refine this.congr_fun fun n => ?_
  rw [bernoulliOrder, q24b_aeval_order]

/-- DLMF 24.16.2: `(2/(eᵗ + 1))^ℓ e^{xt} = ∑ₙ E_n^{(ℓ)}(x) tⁿ/n!` for `|t| < π`. -/
@[dlmf 24.16.E2]
theorem hasSum_eulerOrder (ℓ : ℕ) (x : ℂ) {t : ℂ} (ht : ‖t‖ < π) :
    HasSum (fun n : ℕ => aeval x (eulerOrder ℓ n) * t ^ n / n !)
      ((2 / (Complex.exp t + 1)) ^ ℓ * Complex.exp (x * t)) := by
  have hcoef : ∀ (n : ℕ) (z : ℂ), ((PowerSeries.coeff n b24b_eulerZeroSeries : ℚ) : ℂ) * z ^ n =
      eulerPolyE n 0 * z ^ n / n ! := by
    intro n z
    have h := eulerPolyE_ratCast n 0
    push_cast at h
    simp only [b24b_eulerZeroSeries, PowerSeries.coeff_mk, h]
    push_cast; ring
  have hsum : ∀ z : ℂ, ‖z‖ < π →
      Summable (fun n => ((PowerSeries.coeff n b24b_eulerZeroSeries : ℚ) : ℂ) * z ^ n) := by
    intro z hz
    exact ((hasSum_eulerPolyE_mul_pow_div 0 hz).congr_fun fun n => hcoef n z).summable
  have h0 : HasSum (fun n => ((PowerSeries.coeff n b24b_eulerZeroSeries : ℚ) : ℂ) * t ^ n)
      (2 / (Complex.exp t + 1)) := by
    have := (hasSum_eulerPolyE_mul_pow_div 0 ht).congr_fun fun n => hcoef n t
    simpa using this
  obtain ⟨hs, h⟩ := q24b_hasSum_pow _ (b24a_summable_norm_of_summable hsum ht) h0 ℓ
  have hterm : ∀ n, (eulerNumberOrder ℓ n : ℂ) * t ^ n / n ! =
      ((PowerSeries.coeff n (b24b_eulerZeroSeries ^ ℓ) : ℚ) : ℂ) * t ^ n := by
    intro n
    rw [q24b_eulerNumberOrder_eq]; push_cast
    have : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    field_simp
  have := b24a_hasSum_mul_exp (w := x) (hs.congr fun n => by rw [hterm])
    (h.congr_fun fun n => hterm n)
  refine this.congr_fun fun n => ?_
  rw [eulerOrder, q24b_aeval_order]

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

/-! ### Helpers for 24.16.4 and 24.16.6

The Nörlund recurrence and `B_n^{(n+1)}(x) = (x-1)⋯(x-n)`. -/

section R24bNorlund

local notation "T" => (PowerSeries.X : PowerSeries ℚ)
local notation "D" => @PowerSeries.derivative ℚ _
local notation "β" => bernoulliPowerSeries ℚ

/-- `T β' = β - T β - β²` for `β = t/(eᵗ-1)`. -/
theorem r24b_X_mul_derivative_bernoulliPowerSeries :
    T * D β = β - T * β - β ^ 2 := by
  set e := PowerSeries.exp ℚ
  have h := bernoulliPowerSeries_mul_exp_sub_one ℚ
  have hd := congrArg D h
  rw [Derivation.leibniz, map_sub, PowerSeries.derivative_exp, PowerSeries.derivative_one,
    PowerSeries.derivative_X, sub_zero, smul_eq_mul, smul_eq_mul] at hd
  have hne : e - 1 ≠ 0 := by
    intro h0
    have := congrArg (PowerSeries.coeff 1) h0
    simp [e, PowerSeries.coeff_exp] at this
  refine (mul_left_cancel₀ hne ?_)
  linear_combination T * hd + (β - 1) * h

/-- The series `e^{xt}`. -/
def r24b_expSeries (x : ℚ) : PowerSeries ℚ := PowerSeries.mk fun n => x ^ n / n !

/-- `d/dt e^{xt} = x e^{xt}`. -/
theorem r24b_derivative_expSeries (x : ℚ) :
    D (r24b_expSeries x) = PowerSeries.C x * r24b_expSeries x := by
  ext n
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul, r24b_expSeries,
    PowerSeries.coeff_mk, PowerSeries.coeff_mk, Nat.factorial_succ]
  push_cast
  have : (n ! : ℚ) ≠ 0 := by positivity
  field_simp
  ring

/-- `t (βᵃ)' = a βᵃ - a t βᵃ - a βᵃ⁺¹`. -/
theorem r24b_X_mul_derivative_pow (a : ℕ) :
    T * D (β ^ a) = (a : PowerSeries ℚ) * β ^ a - a * T * β ^ a - a * β ^ (a + 1) := by
  rcases a with _ | a
  · simp
  rw [PowerSeries.derivative_pow, Nat.add_sub_cancel]
  linear_combination ((a + 1 : ℕ) : PowerSeries ℚ) * β ^ a *
    r24b_X_mul_derivative_bernoulliPowerSeries

/-- `[tⁿ] βᵃ e^{xt} = B_n^{(a)}(x)/n!`. -/
theorem r24b_coeff_pow_mul_exp (a n : ℕ) (x : ℚ) :
    PowerSeries.coeff n (β ^ a * r24b_expSeries x) = (bernoulliOrder a n).eval x / n ! := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, bernoulliOrder,
    eval_finsetSum, sum_div]
  refine sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [r24b_expSeries, PowerSeries.coeff_mk, eval_mul, eval_C, eval_pow, eval_X,
    q24b_bernoulliNumberOrder_eq, Nat.cast_choose ℚ hkn]
  have h1 : (n ! : ℚ) ≠ 0 := by positivity
  have h2 : (k ! : ℚ) ≠ 0 := by positivity
  have h3 : ((n - k)! : ℚ) ≠ 0 := by positivity
  field_simp

/-- The Nörlund recurrence
`a B_{n+1}^{(a+1)}(x) = (a - n - 1) B_{n+1}^{(a)}(x) + (n+1)(x - a) B_n^{(a)}(x)`. -/
theorem r24b_bernoulliOrder_rec_eval (a n : ℕ) (x : ℚ) :
    (a : ℚ) * (bernoulliOrder (a + 1) (n + 1)).eval x =
      ((a : ℚ) - (n + 1)) * (bernoulliOrder a (n + 1)).eval x +
        (n + 1) * (x - a) * (bernoulliOrder a n).eval x := by
  set E := r24b_expSeries x
  have key : T * D (β ^ a * E) = (a : PowerSeries ℚ) * (β ^ a * E) - a * T * (β ^ a * E) -
      a * (β ^ (a + 1) * E) + PowerSeries.C x * T * (β ^ a * E) := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, r24b_derivative_expSeries]
    linear_combination E * r24b_X_mul_derivative_pow a
  have hc := congrArg (PowerSeries.coeff (n + 1)) key
  simp only [map_add, map_sub, mul_assoc, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_derivative, ← map_natCast (PowerSeries.C (R := ℚ)),
    ] at hc
  simp only [E, r24b_coeff_pow_mul_exp] at hc
  have h1 : ((n + 1)! : ℚ) ≠ 0 := by positivity
  have h2 : (n ! : ℚ) ≠ 0 := by positivity
  rw [Nat.factorial_succ] at hc h1
  push_cast at hc h1
  field_simp at hc
  linear_combination hc

/-- `B_n^{(n+1)}(x) = (x-1)(x-2)⋯(x-n)`. -/
theorem r24b_bernoulliOrder_succ_self (n : ℕ) :
    bernoulliOrder (n + 1) n = (descPochhammer ℚ n).comp (X - 1) := by
  induction n with
  | zero =>
    simp [bernoulliOrder, bernoulliNumberOrder_one]
  | succ n ih =>
    refine Polynomial.funext fun x => ?_
    have h := r24b_bernoulliOrder_rec_eval (n + 1) n x
    rw [ih] at h
    push_cast at h
    have hn : (n : ℚ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
    rw [eval_comp, descPochhammer_succ_eval, ← eval_comp, eval_sub, eval_X, eval_one]
    apply mul_left_cancel₀ hn
    linear_combination h

/-- The linear functional `p ↦ ∫₀¹ p`, `Xᵏ ↦ 1/(k+1)`. -/
def r24b_I : ℚ[X] →ₗ[ℚ] ℚ := lsum fun k => (1 / ((k : ℚ) + 1)) • LinearMap.id

/-- `I(c Xᵐ) = c/(m+1)`. -/
theorem r24b_I_C_mul_X_pow (c : ℚ) (m : ℕ) : r24b_I (C c * X ^ m) = c / (m + 1) := by
  rw [C_mul_X_pow_eq_monomial, r24b_I, lsum_apply, sum_monomial_index]
  · simp; ring
  · simp

/-- `I(p) = ∑ₖ pₖ/(k+1)`. -/
theorem r24b_I_eq_sum (p : ℚ[X]) {N : ℕ} (hN : p.natDegree < N) :
    r24b_I p = ∑ k ∈ range N, p.coeff k / (k + 1) := by
  rw [r24b_I, lsum_apply, sum_over_range' _ (fun _ => by simp) N hN]
  refine sum_congr rfl fun k _ => ?_
  simp; ring

/-- `∫₀¹ B_n^{(a+1)}(x) dx = B_n^{(a)}`. -/
theorem r24b_I_bernoulliOrder (a n : ℕ) :
    r24b_I (bernoulliOrder (a + 1) n) = bernoulliNumberOrder a n := by
  rw [bernoulliOrder, map_sum]
  simp only [r24b_I_C_mul_X_pow]
  have h := congrArg (PowerSeries.coeff (n + 1)) (congrArg (· * β ^ a)
    (bernoulliPowerSeries_mul_exp_sub_one ℚ))
  rw [show β * (PowerSeries.exp ℚ - 1) * β ^ a = β ^ (a + 1) * (PowerSeries.exp ℚ - 1) by ring,
    PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ] at h
  simp only [Nat.sub_self, map_sub, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.constantCoeff_exp, PowerSeries.constantCoeff_one, sub_self, mul_zero,
    add_zero] at h
  rw [q24b_bernoulliNumberOrder_eq, ← h, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [show n + 1 - k = (n - k) + 1 by omega, PowerSeries.coeff_exp, PowerSeries.coeff_one,
    q24b_bernoulliNumberOrder_eq, Nat.cast_choose ℚ hkn, Nat.factorial_succ]
  simp only [Nat.add_one_ne_zero, ite_false, sub_zero, Algebra.algebraMap_self, RingHom.id_apply]
  have h1 : (n ! : ℚ) ≠ 0 := by positivity
  have h2 : (k ! : ℚ) ≠ 0 := by positivity
  have h3 : ((n - k)! : ℚ) ≠ 0 := by positivity
  push_cast [hkn]
  field_simp

end R24bNorlund

/-! ### Helpers for 24.16.4: the series of `(ln(1+t)/t)^ℓ` -/

section R24bLog

local notation "T" => (PowerSeries.X : PowerSeries ℚ)
local notation "D" => @PowerSeries.derivative ℚ _

/-- The power series `ln(1+t)/t = ∑ₘ (-1)ᵐ tᵐ/(m+1)`. -/
def r24b_logSeries : PowerSeries ℚ := PowerSeries.mk fun m => (-1) ^ m / (m + 1)

/-- `(1 + t) (ln(1+t))' = 1`. -/
theorem r24b_one_add_X_mul_derivative_log : (1 + T) * D (T * r24b_logSeries) = 1 := by
  ext n
  rw [add_mul, one_mul, map_add]
  rcases n with _ | n
  · simp [r24b_logSeries]
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_derivative,
      PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul, r24b_logSeries,
      PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_one]
    simp only [Nat.add_one_ne_zero, ite_false]
    push_cast
    have h1 : (n : ℚ) + 1 + 1 ≠ 0 := by positivity
    have h2 : (n : ℚ) + 1 ≠ 0 := by positivity
    field_simp
    ring

/-- The differential equation of `(ln(1+t)/t)^{k+1}`. -/
theorem r24b_log_rec (k : ℕ) :
    (1 + T) * T * D (r24b_logSeries ^ (k + 1)) =
      ((k + 1 : ℕ) : PowerSeries ℚ) * r24b_logSeries ^ k -
        ((k + 1 : ℕ) : PowerSeries ℚ) * (1 + T) * r24b_logSeries ^ (k + 1) := by
  have h := r24b_one_add_X_mul_derivative_log
  rw [Derivation.leibniz, PowerSeries.derivative_X, smul_eq_mul, smul_eq_mul] at h
  rw [PowerSeries.derivative_pow, Nat.add_sub_cancel]
  linear_combination ((k + 1 : ℕ) : PowerSeries ℚ) * r24b_logSeries ^ k * h

/-- `n! [tⁿ] (ln(1+t)/t)^ℓ = ℓ B_n^{(ℓ+n)}/(ℓ+n)` for `ℓ ≥ 1`. -/
theorem r24b_coeff_logSeries_pow (n k : ℕ) :
    (n ! : ℚ) * PowerSeries.coeff n (r24b_logSeries ^ (k + 1)) =
      (k + 1) * bernoulliNumberOrder (k + 1 + n) n / (k + 1 + n) := by
  have hrec : ∀ k n : ℕ, ((n : ℚ) + k + 2) * PowerSeries.coeff (n + 1) (r24b_logSeries ^ (k + 1)) +
      ((n : ℚ) + k + 1) * PowerSeries.coeff n (r24b_logSeries ^ (k + 1)) =
      (k + 1) * PowerSeries.coeff (n + 1) (r24b_logSeries ^ k) := by
    intro k n
    have h := congrArg (PowerSeries.coeff (n + 1)) (r24b_log_rec k)
    rcases n with _ | n <;>
    simp only [add_mul, one_mul, mul_add, map_add, map_sub, mul_assoc,
      PowerSeries.coeff_succ_X_mul, ← map_natCast (PowerSeries.C (R := ℚ)),
      PowerSeries.coeff_C_mul, PowerSeries.coeff_derivative,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, PowerSeries.constantCoeff_X,
      zero_mul] at h ⊢ <;>
    push_cast at h ⊢ <;>
    linear_combination h
  have hc0 : ∀ a : ℕ, bernoulliNumberOrder a 0 = 1 := by
    intro a; rw [q24b_bernoulliNumberOrder_eq]; simp [bernoulliPowerSeries]
  have hcrec : ∀ a n : ℕ, (a : ℚ) * bernoulliNumberOrder (a + 1) (n + 1) =
      ((a : ℚ) - (n + 1)) * bernoulliNumberOrder a (n + 1) -
        a * (n + 1) * bernoulliNumberOrder a n := by
    intro a n
    have h := r24b_bernoulliOrder_rec_eval a n 0
    simp only [bernoulliOrder_eval_zero] at h
    linear_combination h
  induction n generalizing k with
  | zero =>
    simp only [Nat.factorial_zero, Nat.cast_one, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hc0, add_zero, mul_one]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, r24b_logSeries, PowerSeries.coeff_mk]
    simp only [pow_zero, Nat.cast_zero, zero_add, div_one, one_pow]
    have : (k : ℚ) + 1 ≠ 0 := by positivity
    rw [add_zero, div_self this]
  | succ n ih =>
    have S : ∀ j : ℕ, (((n + 1)! : ℕ) : ℚ) * PowerSeries.coeff (n + 1) (r24b_logSeries ^ j) =
        j * bernoulliNumberOrder (j + (n + 1)) (n + 1) / (j + (n + 1)) := by
      intro j
      induction j with
      | zero => simp [PowerSeries.coeff_one]
      | succ j ihj =>
        have h1 := hrec j n
        have h2 := ih j
        have h3 := hcrec (j + n + 1) n
        have e1 : j + 1 + (n + 1) = j + n + 1 + 1 := by omega
        have e2 : j + (n + 1) = j + n + 1 := by omega
        have e3 : j + 1 + n = j + n + 1 := by omega
        rw [e1]; rw [e2] at ihj; rw [e3] at h2
        have hf : (((n + 1)! : ℕ) : ℚ) = (n + 1) * n ! := by push_cast [Nat.factorial_succ]; ring
        rw [hf] at ihj ⊢
        have hA : (j : ℚ) + n + 2 ≠ 0 := by positivity
        have hB : (j : ℚ) + n + 1 ≠ 0 := by positivity
        have hn : (n ! : ℚ) ≠ 0 := by positivity
        push_cast at h1 h2 h3 ihj ⊢
        rw [eq_div_iff (by convert hA using 1; ring)]
        rw [eq_div_iff (by convert hB using 1; ring)] at ihj
        rw [eq_div_iff (by convert hB using 1; ring)] at h2
        apply mul_left_cancel₀ hB
        linear_combination (↑j + ↑n + 1) * (↑n + 1) * (↑n ! : ℚ) * h1
          - (↑n + 1) * (↑j + ↑n + 1) * h2 + (↑j + 1) * ihj - (↑j + 1) * h3
    have := S (k + 1)
    rw [show k + 1 + (n + 1) = k + 1 + (n + 1) from rfl] at this
    push_cast at this ⊢
    convert this using 2

end R24bLog

/-- DLMF 24.16.4: for `ℓ ≥ 1` and `0 < |t| < 1`,
`(ln(1+t)/t)^ℓ = ℓ ∑ₙ B_n^{(ℓ+n)}/(ℓ+n) · tⁿ/n!` (principal logarithm). -/
@[dlmf 24.16.E4]
theorem hasSum_log_div_pow {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {t : ℂ} (ht : ‖t‖ < 1) (ht0 : t ≠ 0) :
    HasSum (fun n : ℕ => (ℓ : ℂ) * (bernoulliNumberOrder (ℓ + n) n / (ℓ + n) : ℚ) * t ^ n / n !)
      ((Complex.log (1 + t) / t) ^ ℓ) := by
  have hcoef : ∀ m, ((PowerSeries.coeff m r24b_logSeries : ℚ) : ℂ) = (-1) ^ m / (m + 1) := by
    intro m; simp [r24b_logSeries]
  have h0 : HasSum (fun m => ((PowerSeries.coeff m r24b_logSeries : ℚ) : ℂ) * t ^ m)
      (Complex.log (1 + t) / t) := by
    have h := (hasSum_nat_add_iff' 1).mpr (Complex.hasSum_taylorSeries_log ht)
    simp only [range_one, sum_singleton, pow_zero, Nat.cast_zero, div_zero, sub_zero] at h
    refine (h.div_const t).congr_fun fun m => ?_
    rw [hcoef]
    have hm : (m : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero m
    push_cast
    field_simp
    ring
  have hs : Summable fun m => ‖((PowerSeries.coeff m r24b_logSeries : ℚ) : ℂ) * t ^ m‖ := by
    refine (summable_geometric_of_lt_one (norm_nonneg t) ht).of_nonneg_of_le
      (fun _ => norm_nonneg _) fun m => ?_
    rw [norm_mul, norm_pow, hcoef, norm_div, norm_pow, norm_neg, norm_one, one_pow]
    have : (1 : ℝ) ≤ ‖(m : ℂ) + 1‖ := by
      rw [show (m : ℂ) + 1 = ((m + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      exact_mod_cast Nat.succ_pos m
    calc 1 / ‖(m : ℂ) + 1‖ * ‖t‖ ^ m ≤ 1 * ‖t‖ ^ m := by
          gcongr; exact div_le_one_of_le₀ this (by positivity)
      _ = ‖t‖ ^ m := one_mul _
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  refine (q24b_hasSum_pow _ hs h0 (k + 1)).2.congr_fun fun n => ?_
  have h := r24b_coeff_logSeries_pow n k
  have hn : (n ! : ℚ) ≠ 0 := by positivity
  have hq : PowerSeries.coeff n (r24b_logSeries ^ (k + 1)) =
      (k + 1 : ℕ) * (bernoulliNumberOrder (k + 1 + n) n / (k + 1 + n : ℕ)) / n ! := by
    rw [eq_div_iff hn, mul_comm, h]; push_cast; ring
  rw [hq]
  push_cast
  ring

/-- DLMF 24.16.5: the Bernoulli numbers of the second kind,
`bₙ = ∫₀¹ (x choose n) dx = (1/n!) ∑ₖ [xᵏ](x(x-1)⋯(x-n+1))/(k+1)`. -/
@[dlmf 24.16.E5]
def bernoulliSecondKind (n : ℕ) : ℚ :=
  (∑ k ∈ range (n + 1), (descPochhammer ℚ n).coeff k / (k + 1)) / n !

/-! ### Helpers for 24.16.5: `bₙ = ∫₀¹ (x choose n) dx` and the binomial series -/

/-- `(x choose n) = x(x-1)⋯(x-n+1)/n!`. -/
theorem r24b_choose_eq (x : ℂ) (n : ℕ) :
    Ring.choose x n = aeval x (descPochhammer ℚ n) / n ! := by
  rw [Ring.choose_eq_smul, ← aeval_eq_smeval, smul_eq_mul, ← descPochhammer_map (algebraMap ℤ ℚ),
    aeval_map_algebraMap]
  ring

/-- `|x(x-1)⋯(x-n+1)| ≤ n!` for `0 ≤ x ≤ 1`. -/
theorem r24b_norm_descPochhammer_le (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    ‖aeval (x : ℂ) (descPochhammer ℚ n)‖ ≤ n ! := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [descPochhammer_succ_right, map_mul, norm_mul, Nat.factorial_succ, Nat.cast_mul,
      mul_comm _ (n ! : ℝ)]
    have h : ‖aeval (x : ℂ) (X - (n : ℚ[X]))‖ ≤ (n + 1 : ℕ) := by
      simp only [map_sub, aeval_X, map_natCast]
      rw [show (x : ℂ) - n = ((x - n : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_le]
      push_cast; constructor <;> linarith
    exact mul_le_mul ih h (norm_nonneg _) (by positivity)

/-- `∫₀¹ (x choose n) dx = bₙ`. -/
theorem r24b_integral_descPochhammer (n : ℕ) :
    ∫ x in (0 : ℝ)..1, aeval (x : ℂ) (descPochhammer ℚ n) / n ! = (bernoulliSecondKind n : ℂ) := by
  have hdeg : (descPochhammer ℚ n).natDegree < n + 1 := by
    rw [descPochhammer_natDegree]; omega
  have hx : ∀ x : ℝ, aeval (x : ℂ) (descPochhammer ℚ n) / n ! =
      ∑ k ∈ range (n + 1), (((descPochhammer ℚ n).coeff k / n ! : ℚ) : ℂ) * ((x ^ k : ℝ) : ℂ) := by
    intro x
    conv_lhs => rw [as_sum_range' _ _ hdeg]
    simp [map_sum, sum_div]
    refine sum_congr rfl fun k _ => ?_
    ring
  simp_rw [hx]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, integral_pow]
    rw [bernoulliSecondKind]
    push_cast
    rw [sum_div]
    refine sum_congr rfl fun k _ => ?_
    simp; ring
  · intro k _
    exact (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_pow k))).intervalIntegrable _ _

/-- DLMF 24.16.5: `t/ln(1+t) = ∑ₙ bₙ tⁿ` for `0 < |t| < 1` (principal logarithm). -/
@[dlmf 24.16.E5]
theorem hasSum_bernoulliSecondKind {t : ℂ} (ht : ‖t‖ < 1) (ht0 : t ≠ 0) :
    HasSum (fun n : ℕ => (bernoulliSecondKind n : ℂ) * t ^ n) (t / Complex.log (1 + t)) := by
  have h1t : 1 + t ≠ 0 := by
    intro h
    have : t = -1 := by linear_combination h
    rw [this, norm_neg, norm_one] at ht; exact lt_irrefl _ ht
  have hlog : Complex.log (1 + t) ≠ 0 := by
    intro h
    have := Complex.exp_log h1t
    rw [h, Complex.exp_zero] at this
    exact ht0 (by linear_combination -this)
  have hmem : t ∈ Metric.eball (0 : ℂ) 1 := by
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one]; exact ht
  have hser : ∀ x : ℝ, HasSum (fun n : ℕ => aeval (x : ℂ) (descPochhammer ℚ n) / n ! * t ^ n)
      ((1 + t) ^ (x : ℂ)) := by
    intro x
    have := (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := (x : ℂ))).hasSum hmem
    simp only [binomialSeries_apply, List.ofFn_const, List.prod_replicate, smul_eq_mul,
      zero_add] at this
    simpa [r24b_choose_eq] using this
  have hint : ∫ x in (0 : ℝ)..1, (1 + t) ^ (x : ℂ) = t / Complex.log (1 + t) := by
    simp_rw [Complex.cpow_def_of_ne_zero h1t]
    rw [integral_exp_mul_complex hlog]
    simp [Complex.exp_log h1t]
  rw [← hint]
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := MeasureTheory.volume)
    (a := 0) (b := 1)
    (F := fun (n : ℕ) (x : ℝ) => aeval (x : ℂ) (descPochhammer ℚ n) / n ! * t ^ n)
    (f := fun x : ℝ => (1 + t) ^ (x : ℂ)) (fun n _ => ‖t‖ ^ n) ?_ ?_ ?_ ?_ ?_
  · refine key.congr_fun fun n => ?_
    rw [intervalIntegral.integral_mul_const, r24b_integral_descPochhammer]
  · intro n
    refine (Continuous.aestronglyMeasurable ?_)
    refine Continuous.mul (Continuous.div_const ?_ _) continuous_const
    exact (Polynomial.continuous_aeval _).comp Complex.continuous_ofReal
  · intro n
    refine Eventually.of_forall fun x hx => ?_
    rw [Set.uIoc_of_le zero_le_one] at hx
    rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
    have := r24b_norm_descPochhammer_le x hx.1.le hx.2 n
    have hf : (0 : ℝ) < n ! := by positivity
    calc ‖aeval (x : ℂ) (descPochhammer ℚ n)‖ / n ! * ‖t‖ ^ n ≤ 1 * ‖t‖ ^ n := by
          gcongr; rwa [div_le_one hf]
      _ = _ := one_mul _
  · exact Eventually.of_forall fun x _ => summable_geometric_of_lt_one (norm_nonneg _) ht
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun x _ => hser x

/-- DLMF 24.16.6: `n! bₙ = -B_n^{(n-1)}/(n-1)` for `n ≥ 2`. -/
@[dlmf 24.16.E6]
theorem factorial_mul_bernoulliSecondKind {n : ℕ} (hn : 2 ≤ n) :
    (n ! : ℚ) * bernoulliSecondKind n = -bernoulliNumberOrder (n - 1) n / (n - 1 : ℕ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : (m : ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  rw [Nat.add_sub_cancel]
  have hb : (((m + 1)! : ℕ) : ℚ) * bernoulliSecondKind (m + 1) =
      r24b_I (descPochhammer ℚ (m + 1)) := by
    rw [bernoulliSecondKind,
      r24b_I_eq_sum (N := m + 1 + 1) _ (by rw [descPochhammer_natDegree]; omega)]
    have : (((m + 1)! : ℕ) : ℚ) ≠ 0 := by positivity
    field_simp
  have hD : descPochhammer ℚ (m + 1) = (descPochhammer ℚ (m + 1)).comp (X - 1) +
      ((m : ℚ[X]) + 1) * (descPochhammer ℚ m).comp (X - 1) := by
    rw [descPochhammer_succ_comp_X_sub_one, smul_eq_mul]; ring
  have h1 : r24b_I ((descPochhammer ℚ (m + 1)).comp (X - 1)) =
      bernoulliNumberOrder (m + 1) (m + 1) := by
    rw [← r24b_bernoulliOrder_succ_self, r24b_I_bernoulliOrder]
  have h2 : r24b_I ((descPochhammer ℚ m).comp (X - 1)) = bernoulliNumberOrder m m := by
    rw [← r24b_bernoulliOrder_succ_self, r24b_I_bernoulliOrder]
  have hrec := r24b_bernoulliOrder_rec_eval m m 0
  simp only [bernoulliOrder_eval_zero] at hrec
  have hI : r24b_I (((m : ℚ[X]) + 1) * (descPochhammer ℚ m).comp (X - 1)) =
      ((m : ℚ) + 1) * r24b_I ((descPochhammer ℚ m).comp (X - 1)) := by
    rw [show ((m : ℚ[X]) + 1) = C ((m : ℚ) + 1) by simp, ← smul_eq_C_mul, map_smul, smul_eq_mul]
  rw [hb, hD, map_add, hI, h1, h2, eq_div_iff hm]
  linear_combination hrec

/-- The power series `((1 + λt)^{1/λ} - 1)/t = ∑ₖ (1-λ)(1-2λ)⋯(1-kλ) tᵏ/(k+1)!`, with
coefficients in `ℚ[λ]`. -/
def b24b_degenerateSeries : PowerSeries ℚ[X] :=
  PowerSeries.mk fun k => C (1 / ((k + 1)! : ℚ)) * ∏ i ∈ range k, (1 - ((i + 1 : ℕ) : ℚ[X]) * X)

/-- DLMF 24.16.7: the degenerate Bernoulli numbers `βₙ(λ)` as polynomials in `λ`:
`βₙ(λ)/n!` is the `n`-th coefficient of the inverse of `((1 + λt)^{1/λ} - 1)/t`. -/
@[dlmf 24.16.E7]
def degenerateBernoulli (n : ℕ) : ℚ[X] :=
  (n ! : ℚ) • PowerSeries.coeff n (PowerSeries.invOfUnit b24b_degenerateSeries 1)

/-! ### Helpers for 24.16.7: the binomial series of `(1 + λt)^{1/λ}` and its inverse -/

/-- The degenerate series has constant term `1`. -/
theorem r24b_constantCoeff_degenerateSeries :
    PowerSeries.constantCoeff b24b_degenerateSeries = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, b24b_degenerateSeries, PowerSeries.coeff_mk]
  simp

/-- `aeval (1/λ) (x(x-1)⋯(x-k)) · λ^{k+1} = (1-λ)(1-2λ)⋯(1-kλ)`. -/
theorem r24b_descPochhammer_inv_mul_pow {lam : ℂ} (hlam : lam ≠ 0) (k : ℕ) :
    aeval (1 / lam) (descPochhammer ℚ (k + 1)) * lam ^ (k + 1) =
      ∏ i ∈ range k, (1 - ((i + 1 : ℕ) : ℂ) * lam) := by
  induction k with
  | zero => simp [descPochhammer_one]; field_simp
  | succ k ih =>
    rw [descPochhammer_succ_right, map_mul, prod_range_succ, ← ih]
    simp only [map_sub, aeval_X, map_natCast]
    rw [pow_succ]
    field_simp

/-- The coefficients of the degenerate series at `λ` are `(1/λ choose k+1) λ^{k+1}`. -/
theorem r24b_coeff_degenerate_aeval {lam : ℂ} (hlam : lam ≠ 0) (k : ℕ) :
    aeval lam (PowerSeries.coeff k b24b_degenerateSeries) =
      Ring.choose (1 / lam) (k + 1) * lam ^ (k + 1) := by
  rw [Ring.choose_eq_smul, ← aeval_eq_smeval,
    ← aeval_map_algebraMap ℚ (1 / lam) (descPochhammer ℤ (k + 1)), descPochhammer_map,
    smul_eq_mul, mul_assoc, r24b_descPochhammer_inv_mul_pow hlam, b24b_degenerateSeries,
    PowerSeries.coeff_mk, map_mul, aeval_C, map_prod]
  simp

/-- The coefficients of the degenerate series at `λ` are bounded by `(1 + |λ|)ᵏ`. -/
theorem r24b_norm_coeff_degenerate_le (lam : ℂ) (k : ℕ) :
    ‖aeval lam (PowerSeries.coeff k b24b_degenerateSeries)‖ ≤ (1 + ‖lam‖) ^ k := by
  rw [b24b_degenerateSeries, PowerSeries.coeff_mk, map_mul, aeval_C, map_prod, norm_mul,
    norm_prod]
  have hp : ∏ i ∈ range k, ‖aeval lam (1 - ((i + 1 : ℕ) : ℚ[X]) * X)‖ ≤ k ! * (1 + ‖lam‖) ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [prod_range_succ, Nat.factorial_succ, pow_succ]
      have hb : ‖aeval lam (1 - ((k + 1 : ℕ) : ℚ[X]) * X)‖ ≤ (k + 1 : ℕ) * (1 + ‖lam‖) := by
        simp only [map_sub, map_one, map_mul, map_natCast, aeval_X]
        refine (norm_sub_le _ _).trans ?_
        rw [norm_one, norm_mul, Complex.norm_natCast]
        push_cast
        nlinarith [norm_nonneg lam]
      calc (∏ i ∈ range k, ‖aeval lam (1 - ((i + 1 : ℕ) : ℚ[X]) * X)‖) *
            ‖aeval lam (1 - ((k + 1 : ℕ) : ℚ[X]) * X)‖
          ≤ (k ! * (1 + ‖lam‖) ^ k) * ((k + 1 : ℕ) * (1 + ‖lam‖)) :=
            mul_le_mul ih hb (norm_nonneg _) (by positivity)
        _ = _ := by push_cast; ring
  have hc : ‖(algebraMap ℚ ℂ) (1 / ((k + 1)! : ℚ))‖ = 1 / ((k + 1)! : ℝ) := by
    simp
  rw [hc]
  calc 1 / ((k + 1)! : ℝ) * ∏ i ∈ range k, ‖aeval lam (1 - ((i + 1 : ℕ) : ℚ[X]) * X)‖
      ≤ 1 / ((k + 1)! : ℝ) * (k ! * (1 + ‖lam‖) ^ k) := by gcongr
    _ ≤ (1 + ‖lam‖) ^ k := by
      rw [Nat.factorial_succ]; push_cast
      have hk : (0 : ℝ) < k ! := by positivity
      rw [show 1 / (((k : ℝ) + 1) * k !) * (k ! * (1 + ‖lam‖) ^ k) = (1 + ‖lam‖) ^ k / (k + 1) by
        field_simp]
      exact div_le_self (by positivity) (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])

/-- The coefficients `hₙ = βₙ(λ)/n!` of the inverse series are bounded by `(2(1 + |λ|))ⁿ`. -/
theorem r24b_norm_coeff_inv_le (lam : ℂ) (n : ℕ) :
    ‖aeval lam (PowerSeries.coeff n (PowerSeries.invOfUnit b24b_degenerateSeries 1))‖ ≤
      (2 * (1 + ‖lam‖)) ^ n := by
  set A := 1 + ‖lam‖
  have hA : 1 ≤ A := by simp [A]
  set h : ℕ → ℂ := fun n =>
    aeval lam (PowerSeries.coeff n (PowerSeries.invOfUnit b24b_degenerateSeries 1))
  set g : ℕ → ℂ := fun n => aeval lam (PowerSeries.coeff n b24b_degenerateSeries)
  have hg0 : g 0 = 1 := by
    simp only [g, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      r24b_constantCoeff_degenerateSeries, map_one]
  have hmul := PowerSeries.invOfUnit_mul b24b_degenerateSeries 1
    (by rw [r24b_constantCoeff_degenerateSeries]; rfl)
  have hrec : ∀ n, h (n + 1) = -∑ j ∈ range (n + 1), h j * g (n + 1 - j) := by
    intro n
    have hc := congrArg (fun F => aeval lam (PowerSeries.coeff (n + 1) F)) hmul
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ,
      map_add, map_sum, PowerSeries.coeff_one, Nat.sub_self] at hc
    simp only [Nat.add_one_ne_zero, ↓reduceIte, map_zero, map_mul] at hc
    change ∑ j ∈ range (n + 1), h j * g (n + 1 - j) + h (n + 1) * g 0 = 0 at hc
    rw [hg0, mul_one] at hc
    linear_combination hc
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simp only [pow_zero]
      change ‖h 0‖ ≤ 1
      have : h 0 = 1 := by
        simp [h, PowerSeries.coeff_zero_eq_constantCoeff_apply]
      rw [this, norm_one]
    change ‖h (n + 1)‖ ≤ _
    rw [hrec, norm_neg]
    calc ‖∑ j ∈ range (n + 1), h j * g (n + 1 - j)‖
        ≤ ∑ j ∈ range (n + 1), (2 * A) ^ j * A ^ (n + 1 - j) := by
          refine (norm_sum_le _ _).trans (sum_le_sum fun j hj => ?_)
          rw [norm_mul]
          exact mul_le_mul (ih j (by simp at hj; omega)) (r24b_norm_coeff_degenerate_le lam _)
            (norm_nonneg _) (by positivity)
      _ ≤ ∑ j ∈ range (n + 1), (2 * A) ^ (n + 1) / 2 ^ (n + 1 - j) := by
          refine sum_le_sum fun j hj => ?_
          have hjn : j ≤ n + 1 := by simp at hj; omega
          rw [le_div_iff₀ (by positivity)]
          obtain ⟨d, hd⟩ : ∃ d, n + 1 - j = d := ⟨_, rfl⟩
          have hnd : n + 1 = j + d := by omega
          rw [hd, hnd]
          apply le_of_eq
          ring
      _ ≤ (2 * A) ^ (n + 1) := by
          rw [← sum_range_reflect]
          simp only [div_eq_mul_inv]
          rw [← mul_sum]
          refine mul_le_of_le_one_right (by positivity) ?_
          have : ∀ j ∈ range (n + 1),
              ((2 : ℝ) ^ (n + 1 - (n + 1 - 1 - j)))⁻¹ = (1 / 2) ^ (j + 1) := by
            intro j hj
            have : n + 1 - (n + 1 - 1 - j) = j + 1 := by simp at hj; omega
            rw [this, one_div, inv_pow]
          rw [sum_congr rfl this]
          have := geom_sum_eq (show (1 / 2 : ℝ) ≠ 1 by norm_num) (n + 1)
          rw [show ∑ j ∈ range (n + 1), (1 / 2 : ℝ) ^ (j + 1) =
            (1 / 2) * ∑ j ∈ range (n + 1), (1 / 2 : ℝ) ^ j by
              rw [mul_sum]; simp [pow_succ, mul_comm],
            this]
          have hp : (0 : ℝ) < (1 / 2) ^ (n + 1) := by positivity
          rw [div_eq_mul_inv]
          norm_num
          linarith

/-- DLMF 24.16.7: for `λ ≠ 0` and all sufficiently small `t ≠ 0`,
`t/((1 + λt)^{1/λ} - 1) = ∑ₙ βₙ(λ) tⁿ/n!` (principal power). -/
@[dlmf 24.16.E7]
theorem hasSum_degenerateBernoulli {lam : ℂ} (hlam : lam ≠ 0) :
    ∀ᶠ t in 𝓝[≠] (0 : ℂ), HasSum (fun n : ℕ => aeval lam (degenerateBernoulli n) * t ^ n / n !)
      (t / ((1 + lam * t) ^ (1 / lam) - 1)) := by
  set A := 1 + ‖lam‖
  have hA : 1 ≤ A := by simp [A]
  have hball : Metric.ball (0 : ℂ) (1 / (4 * A)) ∈ 𝓝 (0 : ℂ) :=
    Metric.ball_mem_nhds _ (by positivity)
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hball] with t ht ht0
  rw [Metric.mem_ball, dist_zero_right] at ht
  have ht0' : t ≠ 0 := ht0
  set h : ℕ → ℂ := fun n =>
    aeval lam (PowerSeries.coeff n (PowerSeries.invOfUnit b24b_degenerateSeries 1))
  set g : ℕ → ℂ := fun n => aeval lam (PowerSeries.coeff n b24b_degenerateSeries)
  have hAt : A * ‖t‖ < 1 / 4 := by
    rw [lt_div_iff₀ (by positivity)] at ht
    nlinarith
  have hAt0 : 0 ≤ A * ‖t‖ := by positivity
  -- the series of `((1 + λt)^{1/λ} - 1)/t`
  have hlt : ‖lam * t‖ < 1 := by
    rw [norm_mul]
    calc ‖lam‖ * ‖t‖ ≤ A * ‖t‖ := by gcongr; simp [A]
      _ < 1 := by linarith
  have hmem : lam * t ∈ Metric.eball (0 : ℂ) 1 := by
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one]; exact hlt
  have hb := (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := 1 / lam)).hasSum hmem
  simp only [binomialSeries_apply, List.ofFn_const, List.prod_replicate, smul_eq_mul,
    zero_add] at hb
  have hG : HasSum (fun k => g k * t ^ k) (((1 + lam * t) ^ (1 / lam) - 1) / t) := by
    have h1 := ((hasSum_nat_add_iff' 1).mpr hb).div_const t
    simp only [range_one, sum_singleton, Ring.choose_zero_right, pow_zero, mul_one] at h1
    refine h1.congr_fun fun k => ?_
    simp only [g, r24b_coeff_degenerate_aeval hlam]
    field_simp
    ring
  have hGs : Summable fun k => ‖g k * t ^ k‖ := by
    refine (summable_geometric_of_lt_one hAt0 (by linarith)).of_nonneg_of_le
      (fun _ => norm_nonneg _) fun k => ?_
    rw [norm_mul, norm_pow, mul_pow]
    exact mul_le_mul_of_nonneg_right (r24b_norm_coeff_degenerate_le lam k) (by positivity)
  have hHs : Summable fun k => ‖h k * t ^ k‖ := by
    refine (summable_geometric_of_lt_one (by positivity : 0 ≤ 2 * A * ‖t‖)
      (by linarith)).of_nonneg_of_le (fun _ => norm_nonneg _) fun k => ?_
    rw [norm_mul, norm_pow, mul_pow]
    exact mul_le_mul_of_nonneg_right (r24b_norm_coeff_inv_le lam k) (by positivity)
  have hmul := PowerSeries.invOfUnit_mul b24b_degenerateSeries 1
    (by rw [r24b_constantCoeff_degenerateSeries]; rfl)
  have hprod := hasSum_sum_range_mul_of_summable_norm hHs hGs
  rw [hG.tsum_eq] at hprod
  have hone : HasSum (fun n : ℕ => ∑ k ∈ range (n + 1), h k * t ^ k * (g (n - k) * t ^ (n - k)))
      (1 : ℂ) := by
    have : (fun n : ℕ => ∑ k ∈ range (n + 1), h k * t ^ k * (g (n - k) * t ^ (n - k))) =
        fun n => if n = 0 then 1 else 0 := by
      funext n
      have hc := congrArg (fun F => aeval lam (PowerSeries.coeff n F)) hmul
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, map_sum,
        PowerSeries.coeff_one] at hc
      have hs : ∑ k ∈ range (n + 1), h k * t ^ k * (g (n - k) * t ^ (n - k)) =
          (∑ k ∈ range (n + 1), h k * g (n - k)) * t ^ n := by
        rw [sum_mul]
        refine sum_congr rfl fun k hk => ?_
        have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
        rw [show t ^ n = t ^ k * t ^ (n - k) by rw [← pow_add, Nat.add_sub_cancel' hkn]]
        ring
      rw [hs]
      have : ∑ k ∈ range (n + 1), h k * g (n - k) = if n = 0 then 1 else 0 := by
        simp only [h, g, ← map_mul]
        rw [hc]; split_ifs <;> simp
      rw [this]; split_ifs with hn <;> simp [hn]
    rw [this]; exact hasSum_ite_eq 0 1
  have hHG := hprod.unique hone
  set H := ∑' k, h k * t ^ k
  have hF : (1 + lam * t) ^ (1 / lam) - 1 ≠ 0 := by
    intro h0; rw [h0, zero_div, mul_zero] at hHG; exact zero_ne_one hHG
  have hH : H = t / ((1 + lam * t) ^ (1 / lam) - 1) := by
    field_simp at hHG ⊢
    linear_combination hHG
  rw [← hH]
  refine (hHs.of_norm.hasSum).congr_fun fun n => ?_
  simp only [h, degenerateBernoulli, map_smul, Rat.smul_def, Rat.cast_natCast]
  have : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

/-! ### Helpers for 24.16.8: composing `t/(eᵘ-1)` with `u = ln(1+λt)/λ`

For real `0 < λ < 1/4` and real `0 < |t| < 1`, `(1+λt)^{1/λ} = eᵘ` and
`t/(eᵘ-1) = t/u + ∑_{m ≥ 0} t B_{m+1} u^m/(m+1)!`; expanding `u^m = λ^{-m} m! ∑ⱼ s(j,m)(λt)ʲ/j!`
(26.8.8) gives an absolutely convergent double series whose `tⁿ` coefficients are compared with
24.16.7. Agreement for infinitely many `λ` gives the polynomial identity. -/

section S24bDegenerate

open DLMF.Combinatorics

/-- Coefficients of two real power series with the same sum on a punctured neighbourhood of `0`
are equal. -/
theorem s24b_coeff_unique {a b : ℕ → ℝ} {f : ℝ → ℝ}
    (ha : ∀ᶠ t in 𝓝[≠] (0 : ℝ), HasSum (fun n => a n * t ^ n) (f t))
    (hb : ∀ᶠ t in 𝓝[≠] (0 : ℝ), HasSum (fun n => b n * t ^ n) (f t)) : a = b := by
  have hser : ∀ c : ℕ → ℝ, (∀ᶠ t in 𝓝[≠] (0 : ℝ), HasSum (fun n => c n * t ^ n) (f t)) →
      HasFPowerSeriesAt (FormalMultilinearSeries.ofScalars ℝ c).sum
        (FormalMultilinearSeries.ofScalars ℝ c) 0 ∧
      ∀ᶠ t in 𝓝[≠] (0 : ℝ), (FormalMultilinearSeries.ofScalars ℝ c).sum t = f t := by
    intro c hc
    set P := FormalMultilinearSeries.ofScalars ℝ c
    have hsumP : ∀ t : ℝ, P.sum t = ∑' n, c n * t ^ n := fun t => by
      change FormalMultilinearSeries.ofScalarsSum _ t = _
      rw [FormalMultilinearSeries.ofScalars_sum_eq]; simp [smul_eq_mul]
    obtain ⟨t0, ht0, ht00⟩ := (hc.and self_mem_nhdsWithin).exists
    have hrad : ((‖t0‖₊ : NNReal) : ENNReal) ≤ P.radius := by
      refine P.le_radius_of_tendsto (l := 0) ?_
      have := ht0.summable.tendsto_atTop_zero.norm
      simpa [P, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow] using this
    have hpos : 0 < P.radius := lt_of_lt_of_le (by
      simpa [ENNReal.coe_pos, nnnorm_pos] using ht00) hrad
    refine ⟨(P.hasFPowerSeriesOnBall hpos).hasFPowerSeriesAt, ?_⟩
    filter_upwards [hc] with t ht
    rw [hsumP]; exact ht.tsum_eq
  obtain ⟨h1, e1⟩ := hser a ha
  obtain ⟨h2, e2⟩ := hser b hb
  have hfr : ∃ᶠ z in 𝓝[≠] (0 : ℝ),
      (FormalMultilinearSeries.ofScalars ℝ a).sum z =
        (FormalMultilinearSeries.ofScalars ℝ b).sum z := by
    refine Eventually.frequently ?_
    filter_upwards [e1, e2] with z hz1 hz2
    rw [hz1, hz2]
  have hev := (h1.analyticAt.frequently_eq_iff_eventually_eq h2.analyticAt).mp hfr
  exact FormalMultilinearSeries.ofScalars_series_injective ℝ ℝ
    (h1.eq_formalMultilinearSeries_of_eventually h2 hev)

/-- `u/(eᵘ - 1) = ∑ Bₙ uⁿ/n!` for real `0 < |u| < 2π`. -/
theorem s24b_hasSum_bernoulli_real {u : ℝ} (hu : |u| < 2 * π) (hu0 : u ≠ 0) :
    HasSum (fun n : ℕ => (bernoulli n : ℝ) * u ^ n / n !) (u / (Real.exp u - 1)) := by
  have h := Complex.hasSum_bernoulli_mul_pow_div (z := (u : ℂ))
    (by rwa [Complex.norm_real, Real.norm_eq_abs]) (by exact_mod_cast hu0)
  rw [← Complex.hasSum_ofReal]
  convert h using 1
  · ext n; push_cast; rfl
  · push_cast; rfl

/-- `∑ |Bₙ| vⁿ/n!` converges for `0 ≤ v < 2π`. -/
theorem s24b_summable_abs_bernoulli {v : ℝ} (hv0 : 0 ≤ v) (hv : v < 2 * π) :
    Summable (fun n : ℕ => |(bernoulli n : ℝ)| * v ^ n / n !) := by
  have hsum : ∀ z : ℂ, ‖z‖ < 2 * π →
      Summable (fun n => ((bernoulli n : ℂ) / n !) * z ^ n) := by
    intro z hz
    by_cases hz0 : z = 0
    · subst hz0
      exact (hasSum_single 0 (fun n hn => by simp [zero_pow hn])).summable
    · exact ((Complex.hasSum_bernoulli_mul_pow_div hz hz0).congr_fun
        fun n => by ring).summable
  have h := b24a_summable_norm_of_summable hsum (z := (v : ℂ))
    (by rwa [Complex.norm_real, Real.norm_of_nonneg hv0])
  refine h.congr fun n => ?_
  rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hv0,
    Complex.norm_natCast, Complex.norm_ratCast]
  ring

/-- `∑ⱼ |s(j, m)| xʲ/j! = (-ln(1-x))^m/m!` for `|x| < 1`. -/
theorem s24b_hasSum_stirlingFirst (m : ℕ) {x : ℝ} (hx : |x| < 1) :
    HasSum (fun j : ℕ => (Nat.stirlingFirst j m : ℝ) * x ^ j / j !)
      ((-Real.log (1 - x)) ^ m / m !) := by
  have h := hasSum_signedStirlingFirst_div_factorial m (x := -x) (by rwa [abs_neg])
  have h2 := h.mul_left ((-1) ^ m)
  rw [show 1 + -x = 1 - x by ring] at h2
  convert h2 using 1
  · ext j
    rcases lt_or_ge j m with hjm | hjm
    · simp [Nat.stirlingFirst_eq_zero_of_lt hjm, signedStirlingFirst_eq_zero_of_lt hjm]
    · simp only [signedStirlingFirst, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
        Int.cast_natCast, neg_pow x j]
      obtain ⟨d, rfl⟩ : ∃ d, j = m + d := ⟨j - m, by omega⟩
      rw [Nat.add_sub_cancel_left, pow_add]
      have : ((-1 : ℝ) ^ m) ^ 2 * ((-1) ^ d) ^ 2 = 1 := by
        rw [← pow_mul, ← pow_mul, mul_comm m 2, mul_comm d 2, pow_mul, pow_mul]; simp
      field_simp
      linear_combination (-(Nat.stirlingFirst (m + d) m : ℝ) * x ^ (m + d)) * this
  · rw [neg_pow]; ring

/-- `|ln(1+y)| ≤ |y|/(1-|y|)` for `|y| < 1`. -/
theorem s24b_abs_log_le {y : ℝ} (hy : |y| < 1) : |Real.log (1 + y)| ≤ |y| / (1 - |y|) := by
  have h1 : 0 < 1 + y := by linarith [neg_abs_le y]
  have h2 : 0 < 1 - |y| := by linarith
  have hup := Real.log_le_sub_one_of_pos h1
  have hlo := Real.one_sub_inv_le_log_of_pos h1
  rw [abs_le]
  constructor
  · refine le_trans ?_ hlo
    have e : 1 - (1 + y)⁻¹ = y / (1 + y) := by field_simp; ring
    rw [e]
    rcases le_or_gt 0 y with hy0 | hy0
    · have : 0 ≤ y / (1 + y) := div_nonneg hy0 h1.le
      have : 0 ≤ |y| / (1 - |y|) := div_nonneg (abs_nonneg _) h2.le
      linarith
    · rw [abs_of_neg hy0, show 1 - -y = 1 + y by ring, neg_div, neg_neg]
  · refine hup.trans ?_
    rw [le_div_iff₀ h2]
    nlinarith [le_abs_self y, abs_nonneg y]

/-- `0 ≤ -ln(1-x) ≤ x/(1-x)` for `0 ≤ x < 1`. -/
theorem s24b_neg_log_one_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    0 ≤ -Real.log (1 - x) ∧ -Real.log (1 - x) ≤ x / (1 - x) := by
  have h1 : 0 < 1 - x := by linarith
  refine ⟨neg_nonneg.mpr (Real.log_nonpos h1.le (by linarith)), ?_⟩
  have hlo := Real.one_sub_inv_le_log_of_pos h1
  rw [inv_eq_one_div, one_sub_div h1.ne'] at hlo
  rw [show x / (1 - x) = -((1 - x - 1) / (1 - x)) by ring]
  linarith

/-- The coefficients `e₀ = 0`, `e_{j+1} = (1/j!) ∑_{m ≤ j} (B_{m+1}/(m+1)) s(j, m) λ^{j-m}`. -/
noncomputable def s24b_e (l : ℝ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => (∑ m ∈ range (j + 1), (bernoulli (m + 1) : ℝ) / (m + 1) *
      (signedStirlingFirst j m : ℝ) * l ^ (j - m)) / j !

/-- For `0 < λ < 1/4` and `0 < |t| < 1`, with `u = ln(1+λt)/λ`,
`t/(eᵘ - 1) = ∑ₙ (bₙ λⁿ + eₙ) tⁿ`. -/
theorem s24b_hasSum_main {l : ℝ} (hl0 : 0 < l) (hl : l < 1 / 4) {t : ℝ} (ht : |t| < 1)
    (ht0 : t ≠ 0) :
    HasSum (fun n : ℕ => ((bernoulliSecondKind n : ℝ) * l ^ n + s24b_e l n) * t ^ n)
      (t / (Real.exp (Real.log (1 + l * t) / l) - 1)) := by
  have hl' : l ≠ 0 := hl0.ne'
  set y := l * t with hy
  have hyabs : |y| = l * |t| := by rw [hy, abs_mul, abs_of_pos hl0]
  have hy4 : |y| < 1 / 4 := by
    rw [hyabs]; nlinarith [abs_nonneg t]
  have hy1 : |y| < 1 := by linarith
  have hy0 : y ≠ 0 := mul_ne_zero hl0.ne' ht0
  have hyp : 0 < |y| := abs_pos.mpr hy0
  have h1y : 0 < 1 + y := by linarith [neg_abs_le y]
  set L := Real.log (1 + y) with hLdef
  have hL0 : L ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one h1y (by
    intro h; exact hy0 (by linarith))
  set u := L / l with hu
  have hu0 : u ≠ 0 := div_ne_zero hL0 hl0.ne'
  have hpi : (4 : ℝ) / 3 < 2 * π := by linarith [Real.pi_gt_three]
  have hd : (3 : ℝ) / 4 < 1 - |y| := by linarith
  have hut : |t| / (1 - |y|) < 4 / 3 := by
    rw [div_lt_iff₀ (by linarith)]; nlinarith [abs_nonneg t]
  have hu2 : |u| < 2 * π := by
    rw [hu, abs_div, abs_of_pos hl0, div_lt_iff₀ hl0]
    have := s24b_abs_log_le hy1
    have h3 : |y| / (1 - |y|) = l * (|t| / (1 - |y|)) := by rw [hyabs]; ring
    rw [h3] at this
    nlinarith
  set W := -Real.log (1 - |y|) with hW
  obtain ⟨hW0, hW1⟩ := s24b_neg_log_one_sub_le (abs_nonneg y) hy1
  have hWp : 0 < W := neg_pos.mpr (Real.log_neg (by linarith) (by linarith))
  set V := W / l with hV
  have hVp : 0 < V := div_pos hWp hl0
  have hV2 : V < 2 * π := by
    rw [hV, div_lt_iff₀ hl0]
    have h3 : |y| / (1 - |y|) = l * (|t| / (1 - |y|)) := by rw [hyabs]; ring
    rw [h3] at hW1
    nlinarith
  -- the double family
  set c : ℕ → ℝ := fun m => (bernoulli (m + 1) : ℝ) / (m + 1) with hc
  set F : ℕ × ℕ → ℝ := fun p => t * c p.1 / l ^ p.1 *
    ((signedStirlingFirst p.2 p.1 : ℝ) * y ^ p.2 / p.2 !) with hF
  have habsrow : ∀ m : ℕ, HasSum (fun j => |F (m, j)|) (|t| * |c m| / l ^ m * (W ^ m / m !)) := by
    intro m
    have h := (s24b_hasSum_stirlingFirst m (x := |y|) (by rwa [abs_abs])).mul_left
      (|t| * |c m| / l ^ m)
    refine h.congr_fun fun j => ?_
    simp only [hF, abs_mul, abs_div, abs_pow, abs_of_pos hl0, Nat.abs_cast]
    congr 2
    have e : ((Nat.stirlingFirst j m : ℕ) : ℝ) = |(signedStirlingFirst j m : ℝ)| := by
      rw [signedStirlingFirst]; push_cast
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
    rw [e]
  have hrowsum : Summable fun m : ℕ => |t| * |c m| / l ^ m * (W ^ m / m !) := by
    have h0 := s24b_summable_abs_bernoulli hVp.le hV2
    have h1 := ((summable_nat_add_iff 1).mpr h0).mul_left (|t| / V)
    refine h1.congr fun m => ?_
    simp only [hc, abs_div, Nat.factorial_succ]
    rw [show W = V * l by rw [hV]; field_simp]
    have : |((m : ℝ) + 1)| = m + 1 := abs_of_pos (by positivity)
    rw [this]
    push_cast
    field_simp
    ring
  have hFabs : Summable fun p : ℕ × ℕ => |F p| := by
    refine (summable_prod_of_nonneg fun _ => abs_nonneg _).mpr
      ⟨fun m => (habsrow m).summable, ?_⟩
    simp_rw [fun m => (habsrow m).tsum_eq]
    exact hrowsum
  have hFs : Summable F := Summable.of_norm (by simpa only [Real.norm_eq_abs] using hFabs)
  -- row sums
  have hrow : ∀ m : ℕ, HasSum (fun j => F (m, j)) (t * c m / l ^ m * (L ^ m / m !)) := by
    intro m
    have h := (hasSum_signedStirlingFirst_div_factorial m (x := y) hy1).mul_left
      (t * c m / l ^ m)
    exact h
  have hR := hFs.hasSum.prod_fiberwise hrow
  have hBer := (hasSum_nat_add_iff' 1).mpr (s24b_hasSum_bernoulli_real hu2 hu0)
  have hBer2 := hBer.mul_left (t / u)
  have hS : ∑' p, F p = t / u * (u / (Real.exp u - 1) - 1) := by
    refine hR.unique (hBer2.congr_fun fun m => ?_) |>.trans ?_
    · simp only [hc, hu, Nat.factorial_succ, div_pow]
      push_cast
      field_simp
      ring
    · simp
  -- column sums
  have hC := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hFs.hasSum
  have hcol : ∀ j : ℕ, HasSum (fun m => F (m, j)) (∑ m ∈ range (j + 1), F (m, j)) := by
    intro j
    exact hasSum_sum_of_ne_finset_zero fun m hm => by
      rw [hF]; dsimp only
      rw [signedStirlingFirst_eq_zero_of_lt (by simp at hm; omega)]; simp
  have hC2 := hC.prod_fiberwise fun j => hcol j
  have hGj : ∀ j : ℕ, ∑ m ∈ range (j + 1), F (m, j) = s24b_e l (j + 1) * t ^ (j + 1) := by
    intro j
    simp only [s24b_e, sum_div, sum_mul]
    refine sum_congr rfl fun m hm => ?_
    have hmj : m ≤ j := by simp at hm; omega
    simp only [hF, hc, hy]
    obtain ⟨d, rfl⟩ : ∃ d, j = m + d := ⟨j - m, by omega⟩
    rw [Nat.add_sub_cancel_left]
    field_simp
    ring
  simp_rw [hGj] at hC2
  have hE : HasSum (fun n => s24b_e l n * t ^ n) (∑' p, F p) := by
    refine (hasSum_nat_add_iff' 1).mp ?_
    simpa [s24b_e] using hC2
  -- second kind
  have hb2 := hasSum_bernoulliSecondKind (t := (y : ℂ))
    (by rwa [Complex.norm_real, Real.norm_eq_abs]) (by exact_mod_cast hy0)
  rw [show (1 : ℂ) + (y : ℂ) = ((1 + y : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_log h1y.le] at hb2
  have hb3 : HasSum (fun n : ℕ => (bernoulliSecondKind n : ℝ) * l ^ n * t ^ n) (t / u) := by
    rw [← Complex.hasSum_ofReal]
    convert hb2 using 1
    · ext n; simp only [hy, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ratCast,
        mul_pow]; ring
    · simp only [hu, hLdef, hy, Complex.ofReal_mul, Complex.ofReal_inv, div_eq_mul_inv,
        mul_inv, inv_inv]; ring
  have htot := hb3.add hE
  rw [hS] at htot
  convert htot using 1
  · ext n; ring
  · have e : t / u * (u / (Real.exp u - 1)) = t / (Real.exp u - 1) := by
      rw [div_mul_div_comm, mul_comm t u, mul_div_mul_left _ _ hu0]
    rw [mul_sub, e]; ring

/-- 24.16.7 restricted to real `0 < λ` and real `t`. -/
theorem s24b_hasSum_degenerate_real {l : ℝ} (hl0 : 0 < l) (hl : l < 1 / 4) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ), HasSum (fun n : ℕ => aeval l (degenerateBernoulli n) / n ! * t ^ n)
      (t / (Real.exp (Real.log (1 + l * t) / l) - 1)) := by
  have h := hasSum_degenerateBernoulli (lam := (l : ℂ)) (by exact_mod_cast hl0.ne')
  have hT : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := (Complex.continuous_ofReal.tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
      simpa using this
    · exact eventually_nhdsWithin_of_forall fun t ht => by simpa using ht
  have hball : Metric.ball (0 : ℝ) 1 ∈ 𝓝[≠] (0 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ one_pos)
  filter_upwards [hT.eventually h, hball] with t ht ht1
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at ht1
  have h1 : 0 < 1 + l * t := by
    have : |l * t| < 1 := by
      rw [abs_mul, abs_of_pos hl0]; nlinarith [abs_nonneg t]
    linarith [neg_abs_le (l * t)]
  rw [← Complex.hasSum_ofReal]
  convert ht using 1
  · ext n
    have := aeval_algebraMap_apply ℂ l (degenerateBernoulli n)
    simp only [Complex.coe_algebraMap] at this
    push_cast
    rw [this]; ring
  · rw [show (1 : ℂ) + (l : ℂ) * (t : ℂ) = ((1 + l * t : ℝ) : ℂ) by push_cast; ring,
      show (1 : ℂ) / (l : ℂ) = ((1 / l : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow h1.le, Real.rpow_def_of_pos h1]
    push_cast
    ring_nf

/-- The reindexing of the Bernoulli–Stirling sum in 24.16.8. -/
theorem s24b_sum_reindex {j : ℕ} (hj : 1 ≤ j) (l : ℝ) :
    ∑ k ∈ Icc 1 ((j + 1) / 2), ((j : ℝ) + 1) / (2 * k) * (bernoulli (2 * k) : ℝ) *
        ((-1) ^ (j + 1 - 2 * k) * (Nat.stirlingFirst j (2 * k - 1) : ℝ)) * l ^ (j + 1 - 2 * k) =
      ((j : ℝ) + 1) * ∑ m ∈ range (j + 1), (bernoulli (m + 1) : ℝ) / (m + 1) *
        (signedStirlingFirst j m : ℝ) * l ^ (j - m) := by
  set g : ℕ → ℝ := fun m => (bernoulli (m + 1) : ℝ) / (m + 1) *
    (signedStirlingFirst j m : ℝ) * l ^ (j - m) with hg
  have hinj : Set.InjOn (fun k : ℕ => 2 * k - 1) (Icc 1 ((j + 1) / 2) : Set ℕ) := by
    intro a ha b hb hab
    simp only [coe_Icc, Set.mem_Icc] at ha hb
    simp only at hab
    omega
  have hsub : (Icc 1 ((j + 1) / 2)).image (fun k : ℕ => 2 * k - 1) ⊆ range (j + 1) := by
    intro m hm
    simp only [mem_image, mem_Icc] at hm
    obtain ⟨k, hk, rfl⟩ := hm
    simp only [mem_range]; omega
  rw [← sum_subset hsub, sum_image hinj, mul_sum]
  · refine sum_congr rfl fun k hk => ?_
    simp only [mem_Icc] at hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have e1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    have e2 : j - (2 * k + 1) = j + 1 - 2 * (k + 1) := by omega
    simp only [e1, e2, signedStirlingFirst]
    push_cast
    ring_nf
  · intro m hm hnot
    simp only [mem_range] at hm
    simp only [mem_image, mem_Icc, not_exists, not_and] at hnot
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      simp [signedStirlingFirst, Nat.stirlingFirst_succ_zero]
    · have hodd : Odd (m + 1) := by
        rcases Nat.even_or_odd (m + 1) with ⟨r, hr⟩ | h
        · exact (hnot r (by omega) (by omega)).elim
        · exact h
      simp [bernoulli_eq_zero_of_odd hodd (by omega)]

/-- The coefficient identity behind 24.16.8, for real `0 < λ < 1/4`. -/
theorem s24b_aeval_degenerate {l : ℝ} (hl0 : 0 < l) (hl : l < 1 / 4) (n : ℕ) :
    aeval l (degenerateBernoulli n) / n ! =
      (bernoulliSecondKind n : ℝ) * l ^ n + s24b_e l n := by
  have hm : ∀ᶠ t in 𝓝[≠] (0 : ℝ), HasSum
      (fun n : ℕ => ((bernoulliSecondKind n : ℝ) * l ^ n + s24b_e l n) * t ^ n)
      (t / (Real.exp (Real.log (1 + l * t) / l) - 1)) := by
    have hball : Metric.ball (0 : ℝ) 1 ∈ 𝓝[≠] (0 : ℝ) :=
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ one_pos)
    filter_upwards [hball, self_mem_nhdsWithin] with t ht ht0
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
    exact s24b_hasSum_main hl0 hl ht ht0
  exact congrFun (s24b_coeff_unique (s24b_hasSum_degenerate_real hl0 hl) hm) n

end S24bDegenerate

/-- DLMF 24.16.8: for `n ≥ 2`,
`βₙ(λ) = n! bₙ λⁿ + ∑_{k=1}^{⌊n/2⌋} (n/(2k)) B₂ₖ s(n-1, 2k-1) λ^{n-2k}`, with the signed
Stirling number `s(n-1, 2k-1) = (-1)^{n-2k} |s(n-1, 2k-1)|` (Mathlib's unsigned
`Nat.stirlingFirst`). -/
@[dlmf 24.16.E8]
theorem degenerateBernoulli_eq {n : ℕ} (hn : 2 ≤ n) :
    degenerateBernoulli n =
      C ((n ! : ℚ) * bernoulliSecondKind n) * X ^ n +
        ∑ k ∈ Icc 1 (n / 2), C ((n : ℚ) / (2 * k) * _root_.bernoulli (2 * k) *
          ((-1) ^ (n - 2 * k) * (Nat.stirlingFirst (n - 1) (2 * k - 1) : ℚ))) *
            X ^ (n - 2 * k) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have hj : 1 ≤ j := by omega
  apply Polynomial.map_injective (algebraMap ℚ ℝ) (algebraMap ℚ ℝ).injective
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono ?_ (Set.Ioo_infinite (show (0 : ℝ) < 1 / 4 by norm_num))
  rintro l ⟨hl0, hl1⟩
  simp only [Set.mem_ofPred_eq, eval_map_algebraMap]
  have h := s24b_aeval_degenerate hl0 hl1 (j + 1)
  rw [div_eq_iff (by positivity)] at h
  rw [h, Nat.add_sub_cancel]
  simp only [map_add, map_sum, map_mul, aeval_C, map_pow, aeval_X, eq_ratCast]
  push_cast
  rw [s24b_sum_reindex hj l, s24b_e, Nat.factorial_succ]
  push_cast
  field_simp

/-! ### Helpers for 24.16.9: a holomorphic logarithm of `t/(eᵗ-1)` on `|t| < 2π`

`H(t) = t/(eᵗ-1)` (with `H(0) = 1`) is holomorphic and zero-free on `|t| < 2π`, so `H'/H` has a
primitive `L` with `L(0) = 0` (Morera on a disk) and `e^L = H`. `F_x = e^{xL}` is holomorphic on
the disk, so its Taylor series at `0` converges there; its `n`-th derivative at `0` is a
polynomial in `x` which at `x = ℓ ∈ ℕ` equals `B_n^{(ℓ)}` (24.16.1), hence equals `B_n^{(x)}`.
On `|t| < π`, `H(t) = e^{-t/2} (t/2)/sinh(t/2)` is a product of two numbers with positive real
part, so it lies in the slit plane and `L = log H` there; for real `t` the same holds as `H > 0`.
-/

section S24bNorlund

open Metric

/-- `t/(eᵗ - 1)`, with its limit `1` at `t = 0`. -/
noncomputable def s24b_H : ℂ → ℂ := Function.update (fun t => t / (Complex.exp t - 1)) 0 1

theorem s24b_exp_sub_one_ne {t : ℂ} (ht : ‖t‖ < 2 * π) (ht0 : t ≠ 0) :
    Complex.exp t - 1 ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (sub_eq_zero.mp h)
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn; exact ht0 hn
  rw [hn, norm_mul, norm_mul, norm_mul, Complex.norm_intCast, Complex.norm_I, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one] at ht
  have : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn0
  nlinarith [Real.pi_pos]

theorem s24b_H_of_ne {t : ℂ} (ht0 : t ≠ 0) : s24b_H t = t / (Complex.exp t - 1) :=
  Function.update_of_ne ht0 _ _

theorem s24b_H_zero : s24b_H 0 = 1 := Function.update_self _ _ _

theorem s24b_tendsto_H : Tendsto (fun t : ℂ => t / (Complex.exp t - 1)) (𝓝[≠] 0) (𝓝 1) := by
  have h := (Complex.hasDerivAt_exp 0).tendsto_slope_zero
  simp only [zero_add, Complex.exp_zero, smul_eq_mul] at h
  have h2 := h.inv₀ one_ne_zero
  simp only [inv_one] at h2
  refine h2.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
  simp [div_eq_mul_inv, mul_comm]

theorem s24b_differentiableOn_H : DifferentiableOn ℂ s24b_H (ball 0 (2 * π)) := by
  rw [← Complex.differentiableOn_compl_singleton_and_continuousAt_iff
    (ball_mem_nhds _ (by positivity))]
  refine ⟨fun t ht => ?_, ?_⟩
  · have ht0 : t ≠ 0 := ht.2
    have hb : ‖t‖ < 2 * π := by simpa using ht.1
    have hd : DifferentiableAt ℂ (fun t : ℂ => t / (Complex.exp t - 1)) t :=
      differentiableAt_id.div (Complex.differentiableAt_exp.sub_const 1)
        (s24b_exp_sub_one_ne hb ht0)
    refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [isOpen_ne.mem_nhds ht0] with z hz using s24b_H_of_ne hz
  · rw [s24b_H, continuousAt_update_same]; exact s24b_tendsto_H

theorem s24b_H_ne_zero {t : ℂ} (ht : ‖t‖ < 2 * π) : s24b_H t ≠ 0 := by
  by_cases ht0 : t = 0
  · rw [ht0, s24b_H_zero]; exact one_ne_zero
  · rw [s24b_H_of_ne ht0]; exact div_ne_zero ht0 (s24b_exp_sub_one_ne ht ht0)

/-- A product of two numbers in the open right half-plane lies in the slit plane. -/
theorem s24b_mul_mem_slitPlane {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    a * b ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  simp only [Complex.mul_re, Complex.mul_im] at h1 h2
  have h3 := mul_le_mul_of_nonneg_left h1 ha.le
  have h4 : a.im * (a.re * b.im + a.im * b.re) = 0 := by rw [h2, mul_zero]
  nlinarith [mul_pos (mul_pos ha ha) hb, mul_nonneg (sq_nonneg a.im) hb.le]


theorem s24b_six_pow_le (n : ℕ) : 6 ^ (n + 1) ≤ (2 * n + 3)! := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show 2 * (n + 1) + 3 = (2 * n + 3 + 1) + 1 by ring, Nat.factorial_succ,
      Nat.factorial_succ, pow_succ]
    calc 6 ^ (n + 1) * 6 ≤ (2 * n + 3)! * ((2 * n + 3 + 1 + 1) * (2 * n + 3 + 1)) :=
          Nat.mul_le_mul ih (by nlinarith)
      _ = _ := by ring

/-- `‖sinh w - w‖ < ‖w‖` for `0 < ‖w‖ < π/2`. -/
theorem s24b_norm_sinh_sub_lt {w : ℂ} (hw0 : w ≠ 0) (hw : ‖w‖ < π / 2) :
    ‖Complex.sinh w - w‖ < ‖w‖ := by
  set r := ‖w‖ with hr
  have hr0 : 0 < r := norm_pos_iff.mpr hw0
  set ρ := r ^ 2 / 6 with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 / 2 := by
    have := Real.pi_lt_d2
    rw [hρ]; nlinarith
  have hs := (hasSum_nat_add_iff' 1).mpr (Complex.hasSum_sinh w)
  simp only [Finset.range_one, Finset.sum_singleton, mul_zero, zero_add, pow_one,
    Nat.factorial_one, Nat.cast_one, div_one] at hs
  have hg := (hasSum_geometric_of_lt_one hρ0 (by linarith)).mul_left (r * ρ)
  have hb : ∀ n : ℕ, ‖w ^ (2 * (n + 1) + 1) / ((2 * (n + 1) + 1)! : ℂ)‖ ≤ r * ρ * ρ ^ n := by
    intro n
    rw [norm_div, norm_pow, Complex.norm_natCast, ← hr,
      show 2 * (n + 1) + 1 = 2 * n + 3 by ring]
    rw [div_le_iff₀ (by positivity)]
    have h6 : ((6 : ℝ) ^ (n + 1)) ≤ ((2 * n + 3)! : ℝ) := by exact_mod_cast s24b_six_pow_le n
    have : r * ρ * ρ ^ n = r ^ (2 * n + 3) / 6 ^ (n + 1) := by
      rw [hρ, div_pow, ← pow_mul]; field_simp; ring
    rw [this, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    exact mul_le_mul_of_nonneg_left h6 (by positivity)
  have hle := hs.norm_le_of_bounded hg hb
  calc ‖Complex.sinh w - w‖ ≤ r * ρ * (1 - ρ)⁻¹ := hle
    _ < r := by
      rw [mul_assoc]
      refine mul_lt_of_lt_one_right hr0 ?_
      rw [← div_eq_mul_inv, div_lt_one (by linarith)]; linarith

theorem s24b_H_mem_slitPlane {t : ℂ} (ht : ‖t‖ < π) : s24b_H t ∈ Complex.slitPlane := by
  by_cases ht0 : t = 0
  · rw [ht0, s24b_H_zero]; exact Complex.one_mem_slitPlane
  rw [s24b_H_of_ne ht0]
  set w := t / 2 with hw
  have hw0 : w ≠ 0 := div_ne_zero ht0 two_ne_zero
  have hwn : ‖w‖ < π / 2 := by
    rw [hw, norm_div, Complex.norm_ofNat]; linarith
  have hsh : Complex.exp t - 1 = 2 * Complex.exp w * Complex.sinh w := by
    have e1 : Complex.exp t = Complex.exp w * Complex.exp w := by
      rw [← Complex.exp_add, hw, add_halves]
    have e2 : Complex.exp w * Complex.exp (-w) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    rw [Complex.sinh, e1]; linear_combination e2
  have hne := s24b_exp_sub_one_ne (show ‖t‖ < 2 * π by linarith [Real.pi_pos]) ht0
  have hsinh : Complex.sinh w ≠ 0 := by
    intro h; rw [hsh, h, mul_zero] at hne; exact hne rfl
  have heq : t / (Complex.exp t - 1) = Complex.exp (-w) * (Complex.sinh w / w)⁻¹ := by
    rw [hsh, inv_div, Complex.exp_neg]
    have : Complex.exp w ≠ 0 := Complex.exp_ne_zero w
    rw [hw]; field_simp
  rw [heq]
  refine s24b_mul_mem_slitPlane ?_ ?_
  · rw [Complex.exp_re]
    refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩) <;>
    · have := Complex.abs_im_le_norm (-w)
      rw [norm_neg] at this
      rw [abs_le] at this; linarith [this.1, this.2]
  · set q := Complex.sinh w / w
    have hq : ‖q - 1‖ < 1 := by
      rw [show q - 1 = (Complex.sinh w - w) / w by rw [div_sub_one hw0], norm_div,
        div_lt_one (norm_pos_iff.mpr hw0)]
      exact s24b_norm_sinh_sub_lt hw0 hwn
    have hqre : 0 < q.re := by
      have := Complex.abs_re_le_norm (q - 1)
      rw [Complex.sub_re, Complex.one_re, abs_le] at this; linarith [this.1]
    rw [Complex.inv_re]
    exact div_pos hqre (Complex.normSq_pos.mpr fun h => by rw [h] at hqre; simp at hqre)


/-- The logarithmic derivative `H'/H`. -/
noncomputable def s24b_l (t : ℂ) : ℂ := deriv s24b_H t / s24b_H t

theorem s24b_differentiableOn_l : DifferentiableOn ℂ s24b_l (ball 0 (2 * π)) :=
  (s24b_differentiableOn_H.deriv isOpen_ball).div s24b_differentiableOn_H
    fun t ht => s24b_H_ne_zero (by simpa using ht)

theorem s24b_exists_L : ∃ L : ℂ → ℂ, L 0 = 0 ∧
    ∀ t ∈ ball (0 : ℂ) (2 * π), HasDerivAt L (s24b_l t) t :=
  s24b_differentiableOn_l.isExactOn_ball.with_val_at 0 0

/-- A holomorphic logarithm of `t/(eᵗ - 1)` on `|t| < 2π`, vanishing at `0`. -/
noncomputable def s24b_L : ℂ → ℂ := s24b_exists_L.choose

theorem s24b_L_zero : s24b_L 0 = 0 := s24b_exists_L.choose_spec.1

theorem s24b_hasDerivAt_L {t : ℂ} (ht : t ∈ ball (0 : ℂ) (2 * π)) :
    HasDerivAt s24b_L (s24b_l t) t :=
  s24b_exists_L.choose_spec.2 t ht

theorem s24b_exp_L {t : ℂ} (ht : t ∈ ball (0 : ℂ) (2 * π)) :
    Complex.exp (s24b_L t) = s24b_H t := by
  set g := fun z => s24b_H z * Complex.exp (-s24b_L z)
  have hd : ∀ z ∈ ball (0 : ℂ) (2 * π), HasDerivAt g 0 z := by
    intro z hz
    have hH := (s24b_differentiableOn_H.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have hE := ((s24b_hasDerivAt_L hz).neg).cexp
    convert hH.mul hE using 1
    have := s24b_H_ne_zero (by simpa using hz : ‖z‖ < 2 * π)
    simp only [s24b_l]; field_simp; ring
  have hc := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball _ _).isPreconnected
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd z hz).deriv) ht (mem_ball_self (by positivity))
  simp only [g, s24b_L_zero, Complex.exp_zero, s24b_H_zero,
    Complex.exp_neg, inv_one, mul_one] at hc
  exact ((mul_inv_eq_one₀ (Complex.exp_ne_zero _)).mp hc).symm

theorem s24b_differentiableOn_F (x : ℂ) :
    DifferentiableOn ℂ (fun z => Complex.exp (x * s24b_L z)) (ball 0 (2 * π)) :=
  fun _ hz => (((s24b_hasDerivAt_L hz).differentiableAt.const_mul x).cexp).differentiableWithinAt

theorem s24b_iteratedDeriv_F (n : ℕ) : ∃ c : ℕ → ℂ → ℂ,
    (∀ k, DifferentiableOn ℂ (c k) (ball 0 (2 * π))) ∧
    ∀ x : ℂ, ∀ t ∈ ball (0 : ℂ) (2 * π),
      iteratedDeriv n (fun z => Complex.exp (x * s24b_L z)) t =
        (∑ k ∈ range (n + 1), x ^ k * c k t) * Complex.exp (x * s24b_L t) := by
  induction n with
  | zero => exact ⟨fun _ _ => 1, fun _ => differentiableOn_const _, fun x t _ => by simp⟩
  | succ n ih =>
    obtain ⟨c, hc, hF⟩ := ih
    refine ⟨fun k t => (if k = n + 1 then 0 else deriv (c k) t) +
      (if k = 0 then 0 else s24b_l t * c (k - 1) t), fun k => ?_, fun x t ht => ?_⟩
    · refine DifferentiableOn.add ?_ ?_
      · split_ifs
        · exact differentiableOn_const _
        · exact (hc k).deriv isOpen_ball
      · split_ifs
        · exact differentiableOn_const _
        · exact s24b_differentiableOn_l.mul (hc (k - 1))
    · rw [iteratedDeriv_succ]
      have hev : iteratedDeriv n (fun z => Complex.exp (x * s24b_L z)) =ᶠ[𝓝 t]
          fun z => (∑ k ∈ range (n + 1), x ^ k * c k z) * Complex.exp (x * s24b_L z) := by
        filter_upwards [isOpen_ball.mem_nhds ht] with z hz using hF x z hz
      rw [hev.deriv_eq]
      have hS : HasDerivAt (fun z => ∑ k ∈ range (n + 1), x ^ k * c k z)
          (∑ k ∈ range (n + 1), x ^ k * deriv (c k) t) t := by
        refine HasDerivAt.fun_sum fun k _ => ?_
        exact ((hc k).differentiableAt (isOpen_ball.mem_nhds ht)).hasDerivAt.const_mul _
      have hE : HasDerivAt (fun z => Complex.exp (x * s24b_L z))
          (Complex.exp (x * s24b_L t) * (x * s24b_l t)) t :=
        ((s24b_hasDerivAt_L ht).const_mul x).cexp
      rw [(hS.fun_mul hE).deriv]
      have key : ∑ k ∈ range (n + 1 + 1), x ^ k * ((if k = n + 1 then 0 else deriv (c k) t) +
          (if k = 0 then 0 else s24b_l t * c (k - 1) t)) =
          ∑ k ∈ range (n + 1), x ^ k * deriv (c k) t +
            x * s24b_l t * ∑ k ∈ range (n + 1), x ^ k * c k t := by
        simp only [mul_add, sum_add_distrib]
        congr 1
        · rw [sum_range_succ, ite_eq_left (rfl : n + 1 = n + 1), mul_zero, add_zero]
          exact sum_congr rfl fun k hk => by rw [ite_eq_right_iff.mpr (by simp at hk; omega)]
        · rw [sum_range_succ', mul_sum]
          simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, ite_true, mul_zero,
            add_zero]
          exact sum_congr rfl fun k _ => by ring
      rw [key]; ring

theorem s24b_iteratedDeriv_F_natCast (ℓ n : ℕ) :
    iteratedDeriv n (fun z => Complex.exp ((ℓ : ℂ) * s24b_L z)) 0 =
      (((norlundPolynomial n).eval (ℓ : ℚ) : ℚ) : ℂ) := by
  have hev : (fun z => Complex.exp ((ℓ : ℂ) * s24b_L z)) =ᶠ[𝓝 0] fun z => s24b_H z ^ ℓ := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (show (0 : ℝ) < 2 * π by positivity))]
      with z hz
    rw [Complex.exp_nat_mul, s24b_exp_L hz]
  rw [hev.iteratedDeriv_eq]
  set c : ℕ → ℂ := fun n => aeval (0 : ℂ) (bernoulliOrder ℓ n) / (n ! : ℂ)
  have h0 : ∀ m, aeval (0 : ℂ) (bernoulliOrder ℓ m) = ((bernoulliNumberOrder ℓ m : ℚ) : ℂ) := by
    intro m
    rw [show (0 : ℂ) = algebraMap ℚ ℂ 0 by simp, aeval_algebraMap_apply_eq_algebraMap_eval,
      bernoulliOrder_eval_zero]
    rfl
  have hsum : ∀ y : ℂ, ‖y‖ < 2 * π → HasSum (fun n => c n * y ^ n) (s24b_H y ^ ℓ) := by
    intro y hy
    by_cases hy0 : y = 0
    · subst hy0
      rw [s24b_H_zero, one_pow]
      convert hasSum_single (f := fun n => c n * (0 : ℂ) ^ n) 0
        (fun n (hn : n ≠ 0) => by simp only [zero_pow hn, mul_zero]) using 1
      show (1 : ℂ) = aeval 0 (bernoulliOrder ℓ 0) / ((0 ! : ℕ) : ℂ) * 0 ^ 0
      rw [h0, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one,
        q24b_bernoulliNumberOrder_eq]
      simp [bernoulliPowerSeries]
    · have := hasSum_bernoulliOrder ℓ 0 hy hy0
      simp only [zero_mul, Complex.exp_zero, mul_one] at this
      rw [s24b_H_of_ne hy0]
      exact this.congr_fun fun n => by simp only [c]; ring
  set p := FormalMultilinearSeries.ofScalars ℂ c
  have hrad : (1 : ENNReal) ≤ p.radius := by
    have h1 := (hsum 1 (by simp; linarith [Real.pi_gt_three])).summable.tendsto_atTop_zero
    have := p.le_radius_of_tendsto (r := 1) (l := 0) ?_
    · simpa using this
    simp only [NNReal.coe_one, one_pow, mul_one, p, FormalMultilinearSeries.ofScalars_norm]
    simpa using h1.norm
  have hp : HasFPowerSeriesOnBall (fun z => s24b_H z ^ ℓ) p 0 1 :=
    { r_le := hrad
      r_pos := one_pos
      hasSum := fun {y} hy => by
        rw [zero_add]
        have hy' : ‖y‖ < 2 * π := by
          have : ‖y‖ < 1 := by
            simpa [← ofReal_norm] using hy
          linarith [Real.pi_gt_three]
        simp only [p, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
        exact hsum y hy' }
  rw [iteratedDeriv_eq_iteratedFDeriv, ← hp.factorial_smul 1 n,
    FormalMultilinearSeries.ofScalars_apply_eq]
  simp only [c, h0, one_pow, smul_eq_mul, mul_one, nsmul_eq_mul]
  have : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp
  rfl

theorem s24b_iteratedDeriv_F_eq (x : ℂ) (n : ℕ) :
    iteratedDeriv n (fun z => Complex.exp (x * s24b_L z)) 0 = aeval x (norlundPolynomial n) := by
  obtain ⟨c, -, hF⟩ := s24b_iteratedDeriv_F n
  have h0 : ∀ y : ℂ, iteratedDeriv n (fun z => Complex.exp (y * s24b_L z)) 0 =
      ∑ k ∈ range (n + 1), y ^ k * c k 0 := by
    intro y
    rw [hF y 0 (mem_ball_self (by positivity)), s24b_L_zero, mul_zero, Complex.exp_zero, mul_one]
  set P : ℂ[X] := ∑ k ∈ range (n + 1), C (c k 0) * X ^ k
  have hP : ∀ y, P.eval y = ∑ k ∈ range (n + 1), y ^ k * c k 0 := by
    intro y
    simp only [P, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    exact sum_congr rfl fun k _ => mul_comm _ _
  have hQ : P = (norlundPolynomial n).map (algebraMap ℚ ℂ) := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.infinite_of_injective_forall_mem (f := fun ℓ : ℕ => (ℓ : ℂ)) Nat.cast_injective
      fun ℓ => ?_
    simp only [Set.mem_ofPred_eq]
    rw [hP, ← h0, s24b_iteratedDeriv_F_natCast, eval_map_algebraMap,
      show (ℓ : ℂ) = algebraMap ℚ ℂ ℓ by simp, aeval_algebraMap_apply_eq_algebraMap_eval]
    rfl
  rw [h0, ← hP, hQ, eval_map_algebraMap]

theorem s24b_L_eq_log {t : ℂ} (ht : ‖t‖ < 2 * π)
    (hs : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → s24b_H (s * t) ∈ Complex.slitPlane) :
    s24b_L t = Complex.log (s24b_H t) := by
  set ψ : ℝ → ℂ := fun s => s24b_L (s * t) - Complex.log (s24b_H (s * t))
  have hball : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) * t ∈ ball (0 : ℂ) (2 * π) := by
    intro s hs
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    calc s * ‖t‖ ≤ 1 * ‖t‖ := by gcongr; exact hs.2
      _ < _ := by simpa
  have hd : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt ψ 0 s := by
    intro s hs'
    have hz := hball s hs'
    have hH := (s24b_differentiableOn_H.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have e : HasDerivAt (fun z : ℂ => s24b_L (z * t) - Complex.log (s24b_H (z * t))) 0
        (s : ℂ) := by
      have hm : HasDerivAt (fun z : ℂ => z * t) t (s : ℂ) := by
        simpa using (hasDerivAt_id (s : ℂ)).mul_const t
      have h1 := (s24b_hasDerivAt_L hz).comp (s : ℂ) hm
      have h2 := (hH.clog (hs s hs')).comp (s : ℂ) hm
      convert h1.sub h2 using 1 <;> first | rfl | simp only [s24b_l, sub_self]
    exact e.comp_ofReal
  have hc := constant_of_has_deriv_right_zero (f := ψ) (a := 0) (b := 1)
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hd s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt) 1
    (Set.right_mem_Icc.mpr zero_le_one)
  simp only [ψ, Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, s24b_L_zero,
    s24b_H_zero, Complex.log_one, sub_zero] at hc
  exact sub_eq_zero.mp hc

end S24bNorlund

/-- DLMF 24.16.9 (complex order): `(t/(eᵗ - 1))^x = ∑ₙ B_n^{(x)} tⁿ/n!`, principal power, for
complex `x` and `0 < |t| < π` (DLMF: `|t| < 2π` with the branch equal to `1` at `t = 0`; see
the module docstring). -/
@[dlmf 24.16.E9]
theorem hasSum_norlundPolynomial (x : ℂ) {t : ℂ} (ht : ‖t‖ < π) (ht0 : t ≠ 0) :
    HasSum (fun n : ℕ => aeval x (norlundPolynomial n) * t ^ n / n !)
      ((t / (Complex.exp t - 1)) ^ x) := by
  have hb : t ∈ Metric.ball (0 : ℂ) (2 * π) := by rw [mem_ball_zero_iff]; linarith [Real.pi_pos]
  have hT := Complex.hasSum_taylorSeries_on_ball (s24b_differentiableOn_F x) hb
  have hL := s24b_L_eq_log (t := t) (by linarith [Real.pi_pos]) fun s hs => by
    refine s24b_H_mem_slitPlane ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    calc s * ‖t‖ ≤ 1 * ‖t‖ := by gcongr; exact hs.2
      _ < _ := by simpa
  simp only [sub_zero, s24b_iteratedDeriv_F_eq, smul_eq_mul] at hT
  rw [hL] at hT
  rw [← s24b_H_of_ne ht0,
    Complex.cpow_def_of_ne_zero (s24b_H_ne_zero (by linarith [Real.pi_pos])),
    mul_comm (Complex.log _)]
  exact hT.congr_fun fun n => by ring

/-- DLMF 24.16.9 (real order and argument): `(t/(eᵗ - 1))^x = ∑ₙ B_n^{(x)} tⁿ/n!` for real `x`
and real `0 < |t| < 2π`. -/
@[dlmf 24.16.E9]
theorem hasSum_norlundPolynomial_real (x : ℝ) {t : ℝ} (ht : |t| < 2 * π) (ht0 : t ≠ 0) :
    HasSum (fun n : ℕ => aeval x (norlundPolynomial n) * t ^ n / n !)
      ((t / (Real.exp t - 1)) ^ x) := by
  have hpos : ∀ r : ℝ, r ≠ 0 → 0 < r / (Real.exp r - 1) := by
    intro r hr
    rcases lt_or_gt_of_ne hr with h | h
    · have := Real.exp_lt_exp.mpr h
      rw [Real.exp_zero] at this
      exact div_pos_of_neg_of_neg h (by linarith)
    · have := Real.exp_lt_exp.mpr h
      rw [Real.exp_zero] at this
      exact div_pos h (by linarith)
  have hHr : ∀ r : ℝ, r ≠ 0 → s24b_H (r : ℂ) = ((r / (Real.exp r - 1) : ℝ) : ℂ) := by
    intro r hr
    rw [s24b_H_of_ne (Complex.ofReal_ne_zero.mpr hr)]; push_cast; rfl
  have htn : ‖(t : ℂ)‖ < 2 * π := by rwa [Complex.norm_real, Real.norm_eq_abs]
  have hb : (t : ℂ) ∈ Metric.ball (0 : ℂ) (2 * π) := by rwa [mem_ball_zero_iff]
  have hT := Complex.hasSum_taylorSeries_on_ball (s24b_differentiableOn_F (x : ℂ)) hb
  have hL := s24b_L_eq_log htn fun s hs => by
    rw [← Complex.ofReal_mul]
    by_cases h0 : s * t = 0
    · rw [h0, Complex.ofReal_zero, s24b_H_zero]; exact Complex.one_mem_slitPlane
    · rw [hHr _ h0, Complex.ofReal_mem_slitPlane]; exact hpos _ h0
  have hR : Complex.exp ((x : ℂ) * s24b_L t) = (((t / (Real.exp t - 1)) ^ x : ℝ) : ℂ) := by
    rw [hL, hHr t ht0, ← Complex.ofReal_log (hpos t ht0).le, ← Complex.ofReal_mul,
      ← Complex.ofReal_exp, Real.rpow_def_of_pos (hpos t ht0), mul_comm]
  simp only [sub_zero, s24b_iteratedDeriv_F_eq, smul_eq_mul, hR] at hT
  rw [← Complex.hasSum_ofReal]
  refine hT.congr_fun fun n => ?_
  rw [show (x : ℂ) = algebraMap ℝ ℂ x from rfl, aeval_algebraMap_apply]
  simp only [Complex.coe_algebraMap]
  push_cast; ring

/-- DLMF §24.16(i): `B_n^{(x)}` is a polynomial in `x` of degree `n`. -/
@[dlmf 24.16.i]
theorem natDegree_norlundPolynomial (n : ℕ) : (norlundPolynomial n).natDegree = n := by
  set g := bernoulliPowerSeries ℚ - 1
  have hg : PowerSeries.constantCoeff g = 0 := by simp [g, bernoulliPowerSeries]
  have hg1 : PowerSeries.coeff 1 g = -1 / 2 := by simp [g, bernoulliPowerSeries]
  have hterm : ∀ j ∈ range (n + 1), (C (PowerSeries.coeff n (g ^ j) / j !) *
      descPochhammer ℚ j).natDegree ≤ n := fun j hj =>
    (natDegree_C_mul_le _ _).trans ((descPochhammer_natDegree ℚ j).le.trans
      (Nat.lt_succ_iff.mp (mem_range.mp hj)))
  have hcoeff : (norlundPolynomial n).coeff n = (-1 / 2) ^ n := by
    rw [norlundPolynomial, b24b_powCoeff, coeff_smul, finsetSum_coeff, sum_range_succ,
      Finset.sum_eq_zero, zero_add, coeff_C_mul, q24b_coeff_pow_self g hg, hg1]
    · have hm := (monic_descPochhammer ℚ n).leadingCoeff
      rw [leadingCoeff, descPochhammer_natDegree ℚ n] at hm
      rw [hm, smul_eq_mul]
      have : (n ! : ℚ) ≠ 0 := by positivity
      field_simp
    · intro j hj
      rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt, mul_zero]
      rw [descPochhammer_natDegree ℚ]; exact mem_range.mp hj
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ (by rw [hcoeff]; positivity)
  rw [norlundPolynomial, b24b_powCoeff]
  exact (natDegree_smul_le _ _).trans (natDegree_sum_le_of_forall_le _ _ hterm)

/-- DLMF §24.16(i): the notation is consistent with 24.16.3, `B_n^{(x)}` at `x = ℓ` being
`B_n^{(ℓ)}`. -/
@[dlmf 24.16.i]
theorem norlundPolynomial_eval_natCast (ℓ n : ℕ) :
    (norlundPolynomial n).eval (ℓ : ℚ) = bernoulliNumberOrder ℓ n := rfl

/-! ### §24.16(ii) Character analogs -/

/-- DLMF 24.16.10: the generalized Bernoulli numbers belonging to a Dirichlet character `χ`
modulo `f`, by the closed form `B_{n,χ} = f^{n-1} ∑_{a=1}^{f} χ(a) Bₙ(a/f)` (DLMF: `χ`
primitive with conductor `f`; the generating function is `hasSum_bernoulliChar`). -/
@[dlmf 24.16.E10]
def bernoulliChar {f : ℕ} (χ : DirichletCharacter ℂ f) (n : ℕ) : ℂ :=
  (f : ℂ) ^ ((n : ℤ) - 1) *
    ∑ a ∈ Icc 1 f, χ a * bernoulliPolyB n ((a : ℂ) / f)

/-- DLMF 24.16.11: `B_{n,χ}(x) = ∑ₖ (n choose k) B_{k,χ} x^{n-k}`. -/
@[dlmf 24.16.E11]
def bernoulliCharPoly {f : ℕ} (χ : DirichletCharacter ℂ f) (n : ℕ) (x : ℂ) : ℂ :=
  ∑ k ∈ range (n + 1), (n.choose k : ℂ) * bernoulliChar χ k * x ^ (n - k)

/-- DLMF 24.16.10: `∑_{a=1}^{f} χ(a) t e^{at}/(e^{ft} - 1) = ∑ₙ B_{n,χ} tⁿ/n!` for
`0 < |t| < 2π/f` (stated for every `χ` modulo `f ≥ 1`, which includes DLMF's primitive `χ`). -/
@[dlmf 24.16.E10]
theorem hasSum_bernoulliChar {f : ℕ} (hf : 1 ≤ f) (χ : DirichletCharacter ℂ f) {t : ℂ}
    (ht : ‖t‖ < 2 * π / f) (ht0 : t ≠ 0) :
    HasSum (fun n : ℕ => bernoulliChar χ n * t ^ n / n !)
      (∑ a ∈ Icc 1 f, χ a * t * Complex.exp (a * t) / (Complex.exp (f * t) - 1)) := by
  have hf0 : (f : ℂ) ≠ 0 := by exact_mod_cast (show f ≠ 0 by omega)
  have hfr : (0 : ℝ) < f := by exact_mod_cast (show 0 < f by omega)
  have hft : ‖(f : ℂ) * t‖ < 2 * π := by
    rw [norm_mul, Complex.norm_natCast, ← lt_div_iff₀' hfr]; exact ht
  have hft0 : (f : ℂ) * t ≠ 0 := mul_ne_zero hf0 ht0
  have key : ∀ a ∈ Icc 1 f, HasSum (fun n : ℕ => χ a * ((f : ℂ) ^ ((n : ℤ) - 1) *
      bernoulliPolyB n ((a : ℂ) / f)) * t ^ n / n !)
      (χ a * t * Complex.exp (a * t) / (Complex.exp (f * t) - 1)) := by
    intro a _
    have h := (hasSum_bernoulliPolyB_mul_pow_div ((a : ℂ) / f) hft hft0).mul_left (χ a / f)
    convert h using 1
    · funext n
      rw [zpow_sub₀ hf0, zpow_one, zpow_natCast, mul_pow]
      field_simp
    · rw [show (a : ℂ) / f * (f * t) = a * t by field_simp]
      field_simp
  convert hasSum_sum key using 1
  funext n
  rw [bernoulliChar, mul_sum, sum_mul, sum_div]
  refine sum_congr rfl fun a _ => ?_
  ring

/-- The character `χ₄` modulo `4` (`χ₄(1) = 1`, `χ₄(3) = -1`, `χ₄(2) = χ₄(4) = 0`) as a
complex Dirichlet character (Mathlib's `ZMod.χ₄` composed with `ℤ → ℂ`). -/
def b24b_chi4 : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

/-- DLMF 24.16.12: `Bₙ(x) = B_{n,χ₀}(x - 1)`, `χ₀` the trivial character (`f = 1`). -/
@[dlmf 24.16.E12]
theorem bernoulli_eq_bernoulliCharPoly_one (n : ℕ) (x : ℂ) :
    bernoulliPolyB n x = bernoulliCharPoly (1 : DirichletCharacter ℂ 1) n (x - 1) := by
  have h := bernoulliPolyB_add n 1 (x - 1)
  rw [add_sub_cancel] at h
  rw [h, bernoulliCharPoly]
  refine sum_congr rfl fun k _ => ?_
  congr 2
  simp [bernoulliChar, MulChar.one_apply (isUnit_of_subsingleton _)]

/-- DLMF 24.16.13: `Eₙ(x) = -(2^{1-n}/(n+1)) B_{n+1,χ₄}(2x - 1)`. -/
@[dlmf 24.16.E13]
theorem euler_eq_bernoulliCharPoly_chi4 (n : ℕ) (x : ℂ) :
    eulerPolyE n x =
      -((2 : ℂ) ^ (1 - (n : ℤ)) / (n + 1)) * bernoulliCharPoly b24b_chi4 (n + 1) (2 * x - 1) := by
  have hchi : ∀ k, bernoulliChar b24b_chi4 k =
      (4 : ℂ) ^ ((k : ℤ) - 1) * (bernoulliPolyB k (1 / 4) - bernoulliPolyB k (3 / 4)) := by
    intro k
    rw [bernoulliChar]
    simp [Finset.sum_Icc_succ_top, b24b_chi4, MulChar.ringHomComp_apply]
    ring_nf
    simp
  have hpoly : bernoulliCharPoly b24b_chi4 (n + 1) (2 * x - 1) =
      4 ^ n * (bernoulliPolyB (n + 1) (x / 2) - bernoulliPolyB (n + 1) (x / 2 + 1 / 2)) := by
    have h1 := bernoulliPolyB_add (n + 1) (1 / 4) ((2 * x - 1) / 4)
    have h3 := bernoulliPolyB_add (n + 1) (3 / 4) ((2 * x - 1) / 4)
    rw [show (1 / 4 : ℂ) + (2 * x - 1) / 4 = x / 2 by ring] at h1
    rw [show (3 / 4 : ℂ) + (2 * x - 1) / 4 = x / 2 + 1 / 2 by ring] at h3
    rw [h1, h3, bernoulliCharPoly, mul_sub, mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n + 1 := Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [hchi, div_pow]
    have h4 : (4 : ℂ) ^ n = (4 : ℂ) ^ ((k : ℤ) - 1) * 4 ^ (n + 1 - k) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
      congr 1; push_cast [hk']; ring
    rw [h4]
    have : (4 : ℂ) ^ (n + 1 - k) ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
  have he := congrArg (aeval x) (euler_eq_bernoulli n)
  simp only [map_mul, map_add, map_natCast, map_one, aeval_C, aeval_comp, aeval_X, map_sub,
    eq_ratCast] at he
  rw [hpoly]
  change ((n : ℂ) + 1) * eulerPolyE n x = _ at he
  have ha : ((1 / 2 : ℚ) : ℂ) * x + ((1 / 2 : ℚ) : ℂ) = x / 2 + 1 / 2 := by push_cast; ring
  have hb : ((1 / 2 : ℚ) : ℂ) * x = x / 2 := by push_cast; ring
  rw [ha, hb] at he
  change _ = ((2 ^ (n + 1) : ℚ) : ℂ) * (bernoulliPolyB (n + 1) (x / 2 + 1 / 2) -
    bernoulliPolyB (n + 1) (x / 2)) at he
  have hn : (n : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  have h2 : (2 : ℂ) ^ (1 - (n : ℤ)) * 4 ^ n = 2 ^ (n + 1) := by
    rw [show (4 : ℂ) ^ n = 2 ^ (2 * n) by rw [pow_mul]; norm_num, ← zpow_natCast (2 : ℂ) (2 * n),
      ← zpow_add₀ (by norm_num), ← zpow_natCast]
    congr 1; push_cast; ring
  have hE : eulerPolyE n x = (2 : ℂ) ^ (n + 1) * (bernoulliPolyB (n + 1) (x / 2 + 1 / 2) -
      bernoulliPolyB (n + 1) (x / 2)) / (n + 1) := by
    rw [eq_div_iff hn]; push_cast at he; linear_combination he
  rw [hE, ← h2]
  field_simp
  ring

end DLMF.BernoulliEuler
