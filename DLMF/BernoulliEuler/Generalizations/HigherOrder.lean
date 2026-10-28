/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.Basic
public import DLMF.BernoulliEuler.GeneratingFunctions
public import DLMF.Combinatorics.Stirling
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.Tactic.Monotonicity.Lemmas

/-!
# Higher-order Bernoulli and Euler analogs

Higher-order polynomial definitions, formal generating series and binomial constructions of
generalized Bernoulli numbers.

Source references and common attribution are retained in
`DLMF.BernoulliEuler.Generalizations`.
-/

@[expose] public noncomputable section

open Polynomial Finset Filter Topology

open scoped Nat Real

namespace DLMF.BernoulliEuler

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
lemma q24b_coeff_pow_self (g : PowerSeries ℚ) (hg : PowerSeries.constantCoeff g = 0) (n : ℕ) :
    PowerSeries.coeff n (g ^ n) = (PowerSeries.coeff 1 g) ^ n := by
  obtain ⟨h, rfl⟩ := PowerSeries.X_dvd_iff.mpr hg
  rw [mul_pow, PowerSeries.coeff_X_pow_mul']
  simp only [le_refl, ite_true, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_pow]
  rw [show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- If `g` has zero constant term, `[tⁿ] gʲ = 0` for `j > n`. -/
lemma q24b_coeff_pow_of_lt (g : PowerSeries ℚ) (hg : PowerSeries.constantCoeff g = 0) {n j : ℕ}
    (hj : n < j) : PowerSeries.coeff n (g ^ j) = 0 := by
  obtain ⟨h, rfl⟩ := PowerSeries.X_dvd_iff.mpr hg
  rw [mul_pow, PowerSeries.coeff_X_pow_mul']
  simp only [show ¬ j ≤ n by omega, ite_false]

/-- The coefficient polynomial `b24b_powCoeff` at a natural number `ℓ` is the coefficient of
the `ℓ`-th power. -/
lemma q24b_powCoeff_eval_natCast (G : PowerSeries ℚ) (hG : PowerSeries.constantCoeff G = 1)
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
lemma q24b_coeff_mul_pow (F G : PowerSeries ℚ) (t : ℂ) (n : ℕ) :
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
lemma q24b_hasSum_pow (G : PowerSeries ℚ) {t v : ℂ}
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
lemma q24b_bernoulliNumberOrder_eq (ℓ n : ℕ) :
    bernoulliNumberOrder ℓ n = n ! * PowerSeries.coeff n (bernoulliPowerSeries ℚ ^ ℓ) := by
  rw [bernoulliNumberOrder, norlundPolynomial, eval_smul, smul_eq_mul,
    q24b_powCoeff_eval_natCast _ (by simp [bernoulliPowerSeries])]

/-- `E_n^{(ℓ)} = n! [tⁿ] (2/(eᵗ+1))^ℓ`. -/
lemma q24b_eulerNumberOrder_eq (ℓ n : ℕ) :
    eulerNumberOrder ℓ n = n ! * PowerSeries.coeff n (b24b_eulerZeroSeries ^ ℓ) := by
  rw [eulerNumberOrder, q24b_powCoeff_eval_natCast _ (by simp [b24b_eulerZeroSeries])]

/-- Evaluation of `∑ₖ (n choose k) cₖ X^{n-k}`. -/
lemma q24b_aeval_order (c : ℕ → ℚ) (n : ℕ) (x : ℂ) :
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
lemma r24b_X_mul_derivative_bernoulliPowerSeries :
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
lemma r24b_derivative_expSeries (x : ℚ) :
    D (r24b_expSeries x) = PowerSeries.C x * r24b_expSeries x := by
  ext n
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul, r24b_expSeries,
    PowerSeries.coeff_mk, PowerSeries.coeff_mk, Nat.factorial_succ]
  push_cast
  have : (n ! : ℚ) ≠ 0 := by positivity
  field_simp
  ring

/-- `t (βᵃ)' = a βᵃ - a t βᵃ - a βᵃ⁺¹`. -/
lemma r24b_X_mul_derivative_pow (a : ℕ) :
    T * D (β ^ a) = (a : PowerSeries ℚ) * β ^ a - a * T * β ^ a - a * β ^ (a + 1) := by
  rcases a with _ | a
  · simp
  rw [PowerSeries.derivative_pow, Nat.add_sub_cancel]
  linear_combination ((a + 1 : ℕ) : PowerSeries ℚ) * β ^ a *
    r24b_X_mul_derivative_bernoulliPowerSeries

/-- `[tⁿ] βᵃ e^{xt} = B_n^{(a)}(x)/n!`. -/
lemma r24b_coeff_pow_mul_exp (a n : ℕ) (x : ℚ) :
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
lemma r24b_bernoulliOrder_rec_eval (a n : ℕ) (x : ℚ) :
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
lemma r24b_bernoulliOrder_succ_self (n : ℕ) :
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
lemma r24b_I_C_mul_X_pow (c : ℚ) (m : ℕ) : r24b_I (C c * X ^ m) = c / (m + 1) := by
  rw [C_mul_X_pow_eq_monomial, r24b_I, lsum_apply, sum_monomial_index]
  · simp; ring
  · simp

/-- `I(p) = ∑ₖ pₖ/(k+1)`. -/
lemma r24b_I_eq_sum (p : ℚ[X]) {N : ℕ} (hN : p.natDegree < N) :
    r24b_I p = ∑ k ∈ range N, p.coeff k / (k + 1) := by
  rw [r24b_I, lsum_apply, sum_over_range' _ (fun _ => by simp) N hN]
  refine sum_congr rfl fun k _ => ?_
  simp; ring

/-- `∫₀¹ B_n^{(a+1)}(x) dx = B_n^{(a)}`. -/
lemma r24b_I_bernoulliOrder (a n : ℕ) :
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
lemma r24b_one_add_X_mul_derivative_log : (1 + T) * D (T * r24b_logSeries) = 1 := by
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
lemma r24b_log_rec (k : ℕ) :
    (1 + T) * T * D (r24b_logSeries ^ (k + 1)) =
      ((k + 1 : ℕ) : PowerSeries ℚ) * r24b_logSeries ^ k -
        ((k + 1 : ℕ) : PowerSeries ℚ) * (1 + T) * r24b_logSeries ^ (k + 1) := by
  have h := r24b_one_add_X_mul_derivative_log
  rw [Derivation.leibniz, PowerSeries.derivative_X, smul_eq_mul, smul_eq_mul] at h
  rw [PowerSeries.derivative_pow, Nat.add_sub_cancel]
  linear_combination ((k + 1 : ℕ) : PowerSeries ℚ) * r24b_logSeries ^ k * h

/-- `n! [tⁿ] (ln(1+t)/t)^ℓ = ℓ B_n^{(ℓ+n)}/(ℓ+n)` for `ℓ ≥ 1`. -/
lemma r24b_coeff_logSeries_pow (n k : ℕ) :
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
lemma r24b_choose_eq (x : ℂ) (n : ℕ) :
    Ring.choose x n = aeval x (descPochhammer ℚ n) / n ! := by
  rw [Ring.choose_eq_smul, ← aeval_eq_smeval, smul_eq_mul, ← descPochhammer_map (algebraMap ℤ ℚ),
    aeval_map_algebraMap]
  ring

/-- `|x(x-1)⋯(x-n+1)| ≤ n!` for `0 ≤ x ≤ 1`. -/
lemma r24b_norm_descPochhammer_le (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
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
lemma r24b_integral_descPochhammer (n : ℕ) :
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
lemma r24b_constantCoeff_degenerateSeries :
    PowerSeries.constantCoeff b24b_degenerateSeries = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, b24b_degenerateSeries, PowerSeries.coeff_mk]
  simp

/-- `aeval (1/λ) (x(x-1)⋯(x-k)) · λ^{k+1} = (1-λ)(1-2λ)⋯(1-kλ)`. -/
lemma r24b_descPochhammer_inv_mul_pow {lam : ℂ} (hlam : lam ≠ 0) (k : ℕ) :
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
lemma r24b_coeff_degenerate_aeval {lam : ℂ} (hlam : lam ≠ 0) (k : ℕ) :
    aeval lam (PowerSeries.coeff k b24b_degenerateSeries) =
      Ring.choose (1 / lam) (k + 1) * lam ^ (k + 1) := by
  rw [Ring.choose_eq_smul, ← aeval_eq_smeval,
    ← aeval_map_algebraMap ℚ (1 / lam) (descPochhammer ℤ (k + 1)), descPochhammer_map,
    smul_eq_mul, mul_assoc, r24b_descPochhammer_inv_mul_pow hlam, b24b_degenerateSeries,
    PowerSeries.coeff_mk, map_mul, aeval_C, map_prod]
  simp

/-- The coefficients of the degenerate series at `λ` are bounded by `(1 + |λ|)ᵏ`. -/
lemma r24b_norm_coeff_degenerate_le (lam : ℂ) (k : ℕ) :
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
lemma r24b_norm_coeff_inv_le (lam : ℂ) (n : ℕ) :
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

end DLMF.BernoulliEuler
end
