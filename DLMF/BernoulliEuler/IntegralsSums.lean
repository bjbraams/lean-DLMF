/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.NumberTheory.EulerNumbers
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.NumberTheory.ZetaValues

/-!
# Integrals and sums of Bernoulli and Euler polynomials (DLMF §§24.13, 24.14)

DLMF's `Bₙ(t)`, `Eₙ(t)` on the real line are Mathlib's `bernoulliFun n` and the project's
`eulerFun n`; `Bₙ = _root_.bernoulli n` (Mathlib, `B₁ = -1/2`), `Eₙ = eulerNumber n`.

## §24.13 Integrals

* 24.13.1 is Mathlib's `antideriv_bernoulliFun` and 24.13.2 at `x = 0` is
  `integral_bernoulliFun_eq_zero` (pointers in `DLMF.Core.UpstreamElementary`); 24.13.2 for every
  real `x` is proved here (also for `n = 0`, stronger than DLMF).
* 24.13.3–24.13.5, 24.13.7–24.13.10 are proved from the antiderivatives, the shift relations and
  the Bernoulli–Euler relation `euler_eq_bernoulli`. 24.13.6 and 24.13.11 are proved by
  repeated integration by parts.

## §24.14 Sums

The polynomial identities 24.14.1, 24.14.3, 24.14.5 are stated for `x, y, h` in an arbitrary
commutative `ℚ`-algebra (via `Polynomial.aeval`), which covers DLMF's complex variables. In
24.14.1 and 24.14.6 the printed terms `n B_{n-1}` and `n E_{n-1}` vanish at `n = 0`; we write
`n • B_{n-1}` with natural subtraction, which agrees, and `(n - 1)` as an element of the
algebra. In 24.14.6 `2^{n-1}` is written `2ⁿ/2` (it is `1/2` at `n = 0`). The sums over
`j + k + ℓ = n` (24.14.8, 24.14.9) and over positive `j + k + ℓ + m = n` (24.14.10) run over
`Finset.Nat.antidiagonalTuple`. The Hankel determinants 24.14.11–24.14.12 are of size `n + 1`.

The sums 24.14.1–24.14.10 are proved with exponential generating functions in `PowerSeries`
(`q24b_egf`): products of generating functions are binomial convolutions. For 24.14.8–24.14.10
the generating functions `t/2 · coth(t/2)` and `sech t` satisfy polynomial relations with their
derivatives, obtained by `linear_combination` from the defining relation after clearing the
non-unit factor `eᵗ - 1` (or the unit `e²ᵗ + 1`). 24.14.9 holds for every `n` (stronger than
DLMF). The Hankel determinants 24.14.11–24.14.12 remain admitted.

## References

* NIST DLMF §§24.13, 24.14; Agoh and Dilcher (2011), Al-Salam and Carlitz (1959).
-/

@[expose] public noncomputable section

open Polynomial Finset intervalIntegral MeasureTheory
open scoped Nat

namespace DLMF.BernoulliEuler

/-! ### Helper lemmas -/

lemma b24b_bernoulliFun_eq_aeval (n : ℕ) (x : ℝ) :
    bernoulliFun n x = aeval x (Polynomial.bernoulli n) := by
  simp [bernoulliFun, eval_map_algebraMap]

lemma b24b_eulerFun_eq_aeval (n : ℕ) (x : ℝ) :
    eulerFun n x = aeval x (Polynomial.euler n) := by
  simp [eulerFun, eval_map_algebraMap]

lemma b24b_bernoulliFun_succ_add_one (n : ℕ) (x : ℝ) :
    bernoulliFun (n + 1) (x + 1) = bernoulliFun (n + 1) x + (n + 1) * x ^ n := by
  have h := congrArg (aeval x) (bernoulli_comp_one_add_X (n + 1))
  simp only [aeval_comp, map_add, map_one, aeval_X, map_nsmul, map_pow,
    Nat.add_sub_cancel] at h
  rw [b24b_bernoulliFun_eq_aeval, b24b_bernoulliFun_eq_aeval, add_comm x, h, nsmul_eq_mul]
  push_cast; ring

lemma b24b_integral_bernoulliFun (n : ℕ) (a b : ℝ) :
    ∫ t in a..b, bernoulliFun n t =
      (bernoulliFun (n + 1) b - bernoulliFun (n + 1) a) / (n + 1) := by
  rw [integral_eq_sub_of_hasDerivAt (fun x _ => antideriv_bernoulliFun n x)
    (intervalIntegrable_bernoulliFun n _ _), sub_div]

lemma b24b_antideriv_eulerFun (n : ℕ) (x : ℝ) :
    HasDerivAt (fun x => eulerFun (n + 1) x / (n + 1)) (eulerFun n x) x := by
  convert (hasDerivAt_eulerFun (n + 1) x).div_const ((n : ℝ) + 1) using 1
  have : (n : ℝ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  push_cast; field_simp

lemma b24b_integral_eulerFun (n : ℕ) (a b : ℝ) :
    ∫ t in a..b, eulerFun n t = (eulerFun (n + 1) b - eulerFun (n + 1) a) / (n + 1) := by
  rw [integral_eq_sub_of_hasDerivAt (fun x _ => b24b_antideriv_eulerFun n x)
    ((continuous_eulerFun n).intervalIntegrable _ _), sub_div]

/-- `(n+1) Eₙ(2x) = 2ⁿ⁺¹ (Bₙ₊₁(x + 1/2) - Bₙ₊₁(x))`, from `euler_eq_bernoulli`. -/
lemma b24b_eulerFun_two_mul (n : ℕ) (x : ℝ) :
    ((n : ℝ) + 1) * eulerFun n (2 * x) =
      2 ^ (n + 1) * (bernoulliFun (n + 1) (x + 1 / 2) - bernoulliFun (n + 1) x) := by
  have h := congrArg (aeval (2 * x)) (euler_eq_bernoulli n)
  simp only [map_mul, map_add, map_natCast, map_one, aeval_C, aeval_comp, aeval_X, map_sub,
    eq_ratCast] at h
  rw [b24b_eulerFun_eq_aeval, b24b_bernoulliFun_eq_aeval, b24b_bernoulliFun_eq_aeval]
  convert h using 3 <;> push_cast <;> ring_nf

/-- `Eₙ(0) = -2 (2ⁿ⁺¹ - 1) Bₙ₊₁/(n+1)` (DLMF 24.4.26), on `ℝ`. -/
lemma b24b_eulerFun_zero (n : ℕ) :
    eulerFun n 0 = -2 * (2 ^ (n + 1) - 1) * (_root_.bernoulli (n + 1) : ℝ) / (n + 1) := by
  have h := b24b_eulerFun_two_mul n 0
  rw [mul_zero, zero_add, bernoulliFun_eval_zero, show (1 / 2 : ℝ) = 2⁻¹ by norm_num,
    bernoulliFun_eval_half] at h
  have hn : (n : ℝ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  rw [eq_div_iff hn, mul_comm, h]
  field_simp
  ring

lemma b24b_eulerFun_one (n : ℕ) : eulerFun (n + 1) 1 = -eulerFun (n + 1) 0 := by
  have h := eulerFun_add_one_add (n + 1) 0
  rw [zero_add, zero_pow (Nat.succ_ne_zero n), mul_zero] at h
  linarith

lemma b24b_eulerFun_half (n : ℕ) : eulerFun n (1 / 2) = eulerNumber n / 2 ^ n := by
  have : (1 / 2 : ℝ) = algebraMap ℚ ℝ (1 / 2) := by simp
  rw [eulerFun, this, eval_map, eval₂_at_apply]
  simp only [eulerNumber, eq_ratCast]
  push_cast
  field_simp

/-- Integration by parts for `∫₀¹ Bₙ Bₘ₊₁`. -/
lemma q24b_integral_bernoulli_parts (n m : ℕ) :
    ∫ t in (0 : ℝ)..1, bernoulliFun n t * bernoulliFun (m + 1) t =
      (bernoulliFun (m + 1) 1 * bernoulliFun (n + 1) 1 -
        bernoulliFun (m + 1) 0 * bernoulliFun (n + 1) 0) / (n + 1) -
      (m + 1) / (n + 1) * ∫ t in (0 : ℝ)..1, bernoulliFun (n + 1) t * bernoulliFun m t := by
  have hn : (n : ℝ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  have h := integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1)
    (u := bernoulliFun (m + 1)) (u' := fun x => ((m + 1 : ℕ) : ℝ) * bernoulliFun m x)
    (v := fun x => bernoulliFun (n + 1) x / (n + 1)) (v' := bernoulliFun n)
    (fun x _ => by simpa using hasDerivAt_bernoulliFun (m + 1) x)
    (fun x _ => antideriv_bernoulliFun n x)
    ((continuous_const.mul (continuous_bernoulliFun _)).intervalIntegrable _ _)
    (intervalIntegrable_bernoulliFun _ _ _)
  simp_rw [mul_comm (bernoulliFun n _)] at *
  rw [h]
  have : ∫ x in (0 : ℝ)..1,
      ((m + 1 : ℕ) : ℝ) * bernoulliFun m x * (bernoulliFun (n + 1) x / (n + 1)) =
      (m + 1) / (n + 1) * ∫ t in (0 : ℝ)..1, bernoulliFun (n + 1) t * bernoulliFun m t := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext x; push_cast; field_simp
  rw [this]; field_simp

/-- `∫₀¹ Bₙ Bₘ₊₁ = (-1)ᵐ (m+1)! n!/(m+1+n)! B_{m+1+n}` for `n ≥ 1`. -/
lemma q24b_integral_bernoulli_mul_aux (m : ℕ) :
    ∀ n : ℕ, 1 ≤ n → ∫ t in (0 : ℝ)..1, bernoulliFun n t * bernoulliFun (m + 1) t =
      (-1) ^ m * ((m + 1)! * n ! / (m + 1 + n)! : ℝ) * (_root_.bernoulli (m + 1 + n) : ℝ) := by
  induction m with
  | zero =>
    intro n hn
    rw [q24b_integral_bernoulli_parts, intervalIntegral.integral_congr (g := fun t =>
      bernoulliFun (n + 1) t) (fun t _ => by simp [bernoulliFun]),
      integral_bernoulliFun_eq_zero (Nat.succ_ne_zero n), bernoulliFun_eval_one,
      bernoulliFun_endpoints_eq_of_ne_one (show n + 1 ≠ 1 by omega), bernoulliFun_eval_zero]
    have hn' : (n : ℝ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
    rw [show 0 + 1 + n = n + 1 by ring, Nat.factorial_succ n]
    simp only [bernoulliFun_eval_zero, ite_true]
    push_cast; field_simp; ring
  | succ m ih =>
    intro n hn
    rw [q24b_integral_bernoulli_parts, ih (n + 1) (by omega),
      bernoulliFun_endpoints_eq_of_ne_one (show m + 1 + 1 ≠ 1 by omega),
      bernoulliFun_endpoints_eq_of_ne_one (show n + 1 ≠ 1 by omega), sub_self, zero_div, zero_sub,
      show m + 1 + (n + 1) = m + 1 + 1 + n by ring]
    have hn' : (n : ℝ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
    rw [Nat.factorial_succ n, Nat.factorial_succ (m + 1)]
    push_cast; field_simp; ring

/-- Integration by parts for `∫₀¹ Eₙ Eₘ₊₁`. -/
lemma q24b_integral_euler_parts (n m : ℕ) :
    ∫ t in (0 : ℝ)..1, eulerFun n t * eulerFun (m + 1) t =
      -((m + 1) / (n + 1) * ∫ t in (0 : ℝ)..1, eulerFun (n + 1) t * eulerFun m t) := by
  have hn : (n : ℝ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  have h := integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1)
    (u := eulerFun (m + 1)) (u' := fun x => ((m + 1 : ℕ) : ℝ) * eulerFun m x)
    (v := fun x => eulerFun (n + 1) x / (n + 1)) (v' := eulerFun n)
    (fun x _ => by simpa using hasDerivAt_eulerFun (m + 1) x)
    (fun x _ => b24b_antideriv_eulerFun n x)
    ((continuous_const.mul (continuous_eulerFun _)).intervalIntegrable _ _)
    ((continuous_eulerFun _).intervalIntegrable _ _)
  simp_rw [mul_comm (eulerFun n _)] at *
  rw [h, b24b_eulerFun_one, b24b_eulerFun_one]
  have : ∫ x in (0 : ℝ)..1, ((m + 1 : ℕ) : ℝ) * eulerFun m x * (eulerFun (n + 1) x / (n + 1)) =
      (m + 1) / (n + 1) * ∫ t in (0 : ℝ)..1, eulerFun (n + 1) t * eulerFun m t := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext x; push_cast; field_simp
  rw [this]; ring

/-- `∫₀¹ Eₙ Eₘ = (-1)ᵐ m! n!/(m+n)! ∫₀¹ E_{m+n}`. -/
lemma q24b_integral_euler_mul_aux (m : ℕ) : ∀ n : ℕ,
    ∫ t in (0 : ℝ)..1, eulerFun n t * eulerFun m t =
      (-1) ^ m * (m ! * n ! / (m + n)! : ℝ) * ∫ t in (0 : ℝ)..1, eulerFun (m + n) t := by
  induction m with
  | zero =>
    intro n
    have : (n ! : ℝ) ≠ 0 := by positivity
    simp [eulerFun, div_self this]
  | succ m ih =>
    intro n
    rw [q24b_integral_euler_parts, ih (n + 1), show m + (n + 1) = m + 1 + n by ring]
    have hn' : (n : ℝ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
    rw [Nat.factorial_succ n, Nat.factorial_succ m]
    push_cast; field_simp; ring

/-- `Bₙ(t) = ∑ₖ (n choose k) Bₖ t^{n-k}` on `ℝ`. -/
lemma q24b_bernoulliFun_eq_sum (n : ℕ) (t : ℝ) :
    bernoulliFun n t =
      ∑ k ∈ range (n + 1), ((n.choose k : ℝ) * _root_.bernoulli k) * t ^ (n - k) := by
  simp only [bernoulliFun, Polynomial.bernoulli, Polynomial.map_sum, eval_finsetSum,
    Polynomial.map_monomial, eval_monomial]
  refine sum_congr rfl fun k _ => ?_
  simp only [map_mul, map_natCast, eq_ratCast]; ring

/-! ### §24.13(i) Bernoulli polynomials -/

/-- DLMF 24.13.2: `∫_x^{x+1} Bₙ(t) dt = xⁿ` for real `x` (DLMF: `n ≥ 1`; also true for `n = 0`,
stronger than DLMF). -/
@[dlmf 24.13.E2]
theorem integral_bernoulliFun_add_one (n : ℕ) (x : ℝ) :
    ∫ t in x..x + 1, bernoulliFun n t = x ^ n := by
  rw [b24b_integral_bernoulliFun, b24b_bernoulliFun_succ_add_one]
  have : (n : ℝ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  field_simp; ring

/-- DLMF 24.13.3: `∫_x^{x+1/2} Bₙ(t) dt = Eₙ(2x)/2ⁿ⁺¹`. -/
@[dlmf 24.13.E3]
theorem integral_bernoulliFun_add_half (n : ℕ) (x : ℝ) :
    ∫ t in x..x + 1 / 2, bernoulliFun n t = eulerFun n (2 * x) / 2 ^ (n + 1) := by
  rw [b24b_integral_bernoulliFun]
  have h := b24b_eulerFun_two_mul n x
  have hn : (n : ℝ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  rw [div_eq_div_iff hn (by positivity)]
  linear_combination -h

/-- DLMF 24.13.4: `∫_0^{1/2} Bₙ(t) dt = (1 - 2ⁿ⁺¹)/2ⁿ · Bₙ₊₁/(n+1)`. -/
@[dlmf 24.13.E4]
theorem integral_bernoulliFun_zero_half (n : ℕ) :
    ∫ t in (0 : ℝ)..1 / 2, bernoulliFun n t =
      (1 - 2 ^ (n + 1)) / 2 ^ n * ((_root_.bernoulli (n + 1) : ℝ) / (n + 1)) := by
  rw [b24b_integral_bernoulliFun, show (1 / 2 : ℝ) = 2⁻¹ by norm_num, bernoulliFun_eval_half,
    bernoulliFun_eval_zero]
  have hn : (n : ℝ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  field_simp
  ring

/-- DLMF 24.13.5: `∫_{1/4}^{3/4} Bₙ(t) dt = Eₙ/2²ⁿ⁺¹`. -/
@[dlmf 24.13.E5]
theorem integral_bernoulliFun_quarter (n : ℕ) :
    ∫ t in (1 / 4 : ℝ)..3 / 4, bernoulliFun n t = (eulerNumber n : ℝ) / 2 ^ (2 * n + 1) := by
  have h := integral_bernoulliFun_add_half n (1 / 4)
  rw [show (1 / 4 : ℝ) + 1 / 2 = 3 / 4 by norm_num, show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num,
    b24b_eulerFun_half] at h
  rw [h]
  field_simp
  ring

/-- DLMF 24.13.6: `∫_0^1 Bₙ(t) Bₘ(t) dt = (-1)ⁿ⁻¹ m! n!/(m+n)! · B_{m+n}` for `m, n ≥ 1`. -/
@[dlmf 24.13.E6]
theorem integral_bernoulliFun_mul_bernoulliFun {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∫ t in (0 : ℝ)..1, bernoulliFun n t * bernoulliFun m t =
      (-1) ^ (n - 1) * (m ! * n ! / (m + n)! : ℝ) * (_root_.bernoulli (m + n) : ℝ) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [q24b_integral_bernoulli_mul_aux j n hn]
  rcases Nat.even_or_odd (j + 1 + n) with he | ho
  · congr 2
    obtain ⟨k, hk⟩ := he
    rw [neg_one_pow_eq_pow_mod_two (R := ℝ), neg_one_pow_eq_pow_mod_two (R := ℝ) (n := n - 1),
      show j % 2 = (n - 1) % 2 by omega]
  · rw [bernoulli_eq_zero_of_odd ho (by omega)]; simp

/-! ### §24.13(ii) Euler polynomials -/

/-- DLMF 24.13.7: `∫ Eₙ(t) dt = Eₙ₊₁(t)/(n+1) + const`, as an antiderivative on `ℝ`. -/
@[dlmf 24.13.E7]
theorem hasDerivAt_eulerFun_succ_div (n : ℕ) (x : ℝ) :
    HasDerivAt (fun x => eulerFun (n + 1) x / (n + 1)) (eulerFun n x) x :=
  b24b_antideriv_eulerFun n x

/-- DLMF 24.13.8: `∫_0^1 Eₙ(t) dt = -2 Eₙ₊₁(0)/(n+1) = 4(2ⁿ⁺² - 1)/((n+1)(n+2)) · Bₙ₊₂`. -/
@[dlmf 24.13.E8]
theorem integral_eulerFun_zero_one (n : ℕ) :
    (∫ t in (0 : ℝ)..1, eulerFun n t) = -2 * eulerFun (n + 1) 0 / (n + 1) ∧
      (∫ t in (0 : ℝ)..1, eulerFun n t) =
        4 * (2 ^ (n + 2) - 1) / ((n + 1) * (n + 2)) * (_root_.bernoulli (n + 2) : ℝ) := by
  have h1 : (∫ t in (0 : ℝ)..1, eulerFun n t) = -2 * eulerFun (n + 1) 0 / (n + 1) := by
    rw [b24b_integral_eulerFun, b24b_eulerFun_one]; ring
  refine ⟨h1, ?_⟩
  rw [h1, b24b_eulerFun_zero]
  have hn : (n : ℝ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- DLMF 24.13.9: `∫_0^{1/2} E₂ₙ(t) dt = -E₂ₙ₊₁(0)/(2n+1) = 2(2²ⁿ⁺² - 1) B₂ₙ₊₂/((2n+1)(2n+2))`. -/
@[dlmf 24.13.E9]
theorem integral_eulerFun_even_zero_half (n : ℕ) :
    (∫ t in (0 : ℝ)..1 / 2, eulerFun (2 * n) t) = -eulerFun (2 * n + 1) 0 / (2 * n + 1) ∧
      (∫ t in (0 : ℝ)..1 / 2, eulerFun (2 * n) t) =
        2 * (2 ^ (2 * n + 2) - 1) * (_root_.bernoulli (2 * n + 2) : ℝ) /
          ((2 * n + 1) * (2 * n + 2)) := by
  have hodd : eulerFun (2 * n + 1) (1 / 2) = 0 := by
    rw [b24b_eulerFun_half, eulerNumber_eq_zero_of_odd (odd_two_mul_add_one n)]; simp
  have h1 : (∫ t in (0 : ℝ)..1 / 2, eulerFun (2 * n) t) =
      -eulerFun (2 * n + 1) 0 / (2 * n + 1) := by
    rw [b24b_integral_eulerFun, hodd]; push_cast; ring
  refine ⟨h1, ?_⟩
  rw [h1, b24b_eulerFun_zero]
  have hn : (2 * n : ℝ) + 1 ≠ 0 := by positivity
  have hn2 : (2 * n : ℝ) + 2 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- DLMF 24.13.10: `∫_0^{1/2} E₂ₙ₋₁(t) dt = E₂ₙ/(n 2²ⁿ⁺¹)` for `n ≥ 1`. -/
@[dlmf 24.13.E10]
theorem integral_eulerFun_odd_zero_half {n : ℕ} (hn : 1 ≤ n) :
    ∫ t in (0 : ℝ)..1 / 2, eulerFun (2 * n - 1) t =
      (eulerNumber (2 * n) : ℝ) / (n * 2 ^ (2 * n + 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, b24b_integral_eulerFun,
    show 2 * k + 1 + 1 = 2 * (k + 1) by ring, b24b_eulerFun_half, b24b_eulerFun_zero,
    show 2 * (k + 1) + 1 = 2 * (k + 1) + 1 by rfl,
    bernoulli_eq_zero_of_odd (odd_two_mul_add_one (k + 1)) (by omega)]
  have hk : (k : ℝ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero k
  push_cast
  field_simp
  ring

/-- DLMF 24.13.11: `∫_0^1 Eₙ(t) Eₘ(t) dt = (-1)ⁿ 4 (2^{m+n+2} - 1) m! n!/(m+n+2)! · B_{m+n+2}`
for `m, n ≥ 1`. -/
@[dlmf 24.13.E11]
theorem integral_eulerFun_mul_eulerFun {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∫ t in (0 : ℝ)..1, eulerFun n t * eulerFun m t =
      (-1) ^ n * 4 * ((2 ^ (m + n + 2) - 1) * m ! * n ! / (m + n + 2)! : ℝ) *
        (_root_.bernoulli (m + n + 2) : ℝ) := by
  rw [q24b_integral_euler_mul_aux, (integral_eulerFun_zero_one (m + n)).2]
  rcases Nat.even_or_odd (m + n) with he | ho
  · rw [neg_one_pow_eq_pow_mod_two (R := ℝ), neg_one_pow_eq_pow_mod_two (R := ℝ) (n := n),
      show m % 2 = n % 2 by obtain ⟨k, hk⟩ := he; omega]
    rw [show m + n + 2 = (m + n) + 1 + 1 by ring, Nat.factorial_succ (m + n + 1),
      Nat.factorial_succ (m + n)]
    push_cast; field_simp; ring
  · rw [bernoulli_eq_zero_of_odd
      (by rw [show m + n + 2 = (m + n) + 2 by ring]; exact ho.add_even even_two) (by omega)]
    simp

/-! ### Exponential generating functions (helpers for §24.14) -/

section EGF

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- Exponential generating function of `aₙ`: `∑ aₙ tⁿ/n!`. -/
def q24b_egf (a : ℕ → A) : PowerSeries A := PowerSeries.mk fun n => algebraMap ℚ A (n ! : ℚ)⁻¹ * a n

/-- Coefficients of `q24b_egf`. -/
lemma q24b_coeff_egf (a : ℕ → A) (n : ℕ) :
    PowerSeries.coeff n (q24b_egf a) = algebraMap ℚ A (n ! : ℚ)⁻¹ * a n := by
  simp [q24b_egf]

/-- The product of exponential generating functions is the binomial convolution. -/
lemma q24b_egf_mul (a b : ℕ → A) :
    q24b_egf a * q24b_egf b =
      q24b_egf fun n => ∑ k ∈ range (n + 1), (n.choose k : A) * a k * b (n - k) := by
  ext n
  rw [PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk, q24b_coeff_egf, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  simp only [q24b_coeff_egf]
  have h : (n.choose k : A) = algebraMap ℚ A (n.choose k : ℚ) := by simp
  rw [h, Nat.cast_choose ℚ hkn]
  have : (algebraMap ℚ A (n ! : ℚ)⁻¹) * algebraMap ℚ A ((n ! : ℚ) / (k ! * (n - k)!)) =
      algebraMap ℚ A (k ! : ℚ)⁻¹ * algebraMap ℚ A ((n - k)! : ℚ)⁻¹ := by
    rw [← map_mul, ← map_mul]; congr 1
    have h1 : (n ! : ℚ) ≠ 0 := by positivity
    have h2 : (k ! : ℚ) ≠ 0 := by positivity
    have h3 : ((n - k)! : ℚ) ≠ 0 := by positivity
    field_simp
  linear_combination (-(a k * b (n - k))) * this

/-- `exp` as an exponential generating function. -/
lemma q24b_exp_eq_egf : PowerSeries.exp A = q24b_egf fun _ => (1 : A) := by
  ext n; simp [q24b_egf, PowerSeries.coeff_exp]

/-- `e^{xt}` as an exponential generating function. -/
lemma q24b_rescale_exp_eq_egf (x : A) :
    PowerSeries.rescale x (PowerSeries.exp A) = q24b_egf fun n => x ^ n := by
  ext n; simp [q24b_egf, PowerSeries.coeff_exp, PowerSeries.coeff_rescale, mul_comm]

/-- Mathlib's Bernoulli generating function in `q24b_egf` form. -/
lemma q24b_egfB_gen (x : A) :
    q24b_egf (fun n => aeval x (Polynomial.bernoulli n)) * (PowerSeries.exp A - 1) =
      PowerSeries.X * PowerSeries.rescale x (PowerSeries.exp A) := by
  rw [← bernoulli_generating_function x]
  congr 1
  ext n
  simp [q24b_egf, Algebra.smul_def]

/-- The Euler generating function: `(∑ Eₙ(x) tⁿ/n!) (eᵗ + 1) = 2 e^{xt}`. -/
lemma q24b_egfE_gen (x : A) :
    q24b_egf (fun n => aeval x (Polynomial.euler n)) * (PowerSeries.exp A + 1) =
      2 * PowerSeries.rescale x (PowerSeries.exp A) := by
  have h1 : PowerSeries.exp A + 1 = q24b_egf fun n => if n = 0 then (2 : A) else 1 := by
    ext n; rcases n with _ | n <;> simp [q24b_egf, PowerSeries.coeff_exp, PowerSeries.coeff_one]
    norm_num
  have h2 : 2 * PowerSeries.rescale x (PowerSeries.exp A) = q24b_egf fun n => 2 * x ^ n := by
    rw [q24b_rescale_exp_eq_egf]; ext n
    rw [two_mul, map_add]; simp only [q24b_coeff_egf]; ring
  rw [h1, h2, q24b_egf_mul]
  congr 1; funext n
  have h := congrArg (aeval x) (sum_range_choose_smul_euler n)
  simp only [map_add, map_sum, map_mul, map_pow, aeval_X, map_smul, map_ofNat] at h
  rw [sum_range_succ, Nat.sub_self, ite_eq_left_iff.mpr (fun h => absurd rfl h), Nat.choose_self,
    Nat.cast_one, one_mul]
  rw [← h]
  congr 1
  · refine sum_congr rfl fun k hk => ?_
    have : n - k ≠ 0 := by have := mem_range.mp hk; omega
    simp only [this, ite_false, mul_one, Algebra.smul_def]; simp
  · ring

/-- `eᵗ - 1` can be cancelled (it is `t` times a unit). -/
lemma q24b_cancel_exp_sub_one {f g : PowerSeries A}
    (h : f * (PowerSeries.exp A - 1) = g * (PowerSeries.exp A - 1)) : f = g := by
  set u : PowerSeries A := PowerSeries.mk fun n => algebraMap ℚ A (1 / (n + 1)!)
  have hu : PowerSeries.exp A - 1 = PowerSeries.X * u := by
    ext n; rcases n with _ | n
    · simp
    · rw [PowerSeries.coeff_succ_X_mul]; simp [u, PowerSeries.coeff_exp, PowerSeries.coeff_one]
  have hunit : IsUnit u := by
    rw [PowerSeries.isUnit_iff_constantCoeff]; simp [u]
  rw [hu, ← mul_assoc, ← mul_assoc, mul_comm f, mul_comm g, mul_assoc, mul_assoc] at h
  exact hunit.mul_left_injective (PowerSeries.X_mul_cancel h)

/-- `eᵗ + 1` is a unit. -/
lemma q24b_isUnit_exp_add_one : IsUnit (PowerSeries.exp A + 1) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp only [map_add, PowerSeries.constantCoeff_exp, map_one]
  have : (1 + 1 : A) = algebraMap ℚ A 2 := by rw [map_ofNat]; norm_num
  rw [this]; exact (IsUnit.mk0 (2 : ℚ) two_ne_zero).map _

/-- `d/dt e^{at} = a e^{at}`. -/
lemma q24b_derivative_rescale_exp (a : A) :
    PowerSeries.derivative (R := A) (PowerSeries.rescale a (PowerSeries.exp A)) =
      PowerSeries.C a * PowerSeries.rescale a (PowerSeries.exp A) := by
  ext n
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale,
    PowerSeries.coeff_rescale, PowerSeries.coeff_exp, PowerSeries.coeff_exp, pow_succ]
  have key : (n + 1 : A) = algebraMap ℚ A (n + 1) := by
    rw [map_add, map_natCast, map_one]
  rw [key]
  have : algebraMap ℚ A (1 / (n + 1)!) * algebraMap ℚ A (n + 1) = algebraMap ℚ A (1 / n !) := by
    rw [← map_mul]; congr 1; rw [Nat.factorial_succ]; push_cast
    have : (n ! : ℚ) ≠ 0 := by positivity
    field_simp
  linear_combination (a ^ n * a) * this

/-- Exponential generating functions determine their sequences. -/
lemma q24b_egf_inj {a b : ℕ → A} (h : q24b_egf a = q24b_egf b) (n : ℕ) : a n = b n := by
  have h' := congrArg (PowerSeries.coeff n) h
  simp only [q24b_coeff_egf] at h'
  have hu : IsUnit (algebraMap ℚ A (n ! : ℚ)⁻¹) :=
    (IsUnit.mk0 _ (inv_ne_zero (by positivity))).map _
  exact hu.mul_left_cancel h'

/-- `(n+1)/(n+1)! = 1/n!` in `A`. -/
lemma q24b_fact_succ (n : ℕ) :
    algebraMap ℚ A ((n + 1)! : ℚ)⁻¹ * ((n : A) + 1) = algebraMap ℚ A (n ! : ℚ)⁻¹ := by
  have key : ((n : A) + 1) = algebraMap ℚ A (n + 1) := by
    rw [map_add, map_natCast, map_one]
  rw [key, ← map_mul]; congr 1; rw [Nat.factorial_succ]; push_cast
  have : (n ! : ℚ) ≠ 0 := by positivity
  field_simp

/-- Multiplication by `t` of an exponential generating function. -/
lemma q24b_X_mul_egf (a : ℕ → A) :
    PowerSeries.X * q24b_egf a = q24b_egf fun n => (n : A) * a (n - 1) := by
  ext n; rcases n with _ | n
  · simp [q24b_egf]
  · rw [PowerSeries.coeff_succ_X_mul, q24b_coeff_egf, q24b_coeff_egf, Nat.add_sub_cancel,
      ← q24b_fact_succ n]
    push_cast; ring

/-- The derivative of an exponential generating function shifts the sequence. -/
lemma q24b_derivative_egf (a : ℕ → A) :
    PowerSeries.derivative (R := A) (q24b_egf a) = q24b_egf fun n => a (n + 1) := by
  ext n
  rw [PowerSeries.coeff_derivative, q24b_coeff_egf, q24b_coeff_egf, ← q24b_fact_succ n]
  ring

/-- Rescaling an exponential generating function. -/
lemma q24b_rescale_egf (a : A) (b : ℕ → A) :
    PowerSeries.rescale a (q24b_egf b) = q24b_egf fun n => a ^ n * b n := by
  ext n; simp only [PowerSeries.coeff_rescale, q24b_coeff_egf]; ring

end EGF

/-! ### §24.14(i) Quadratic recurrence relations -/

section Quadratic

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- DLMF 24.14.1: `∑ₖ (n choose k) Bₖ(x) Bₙ₋ₖ(y) = n(x+y-1) Bₙ₋₁(x+y) - (n-1) Bₙ(x+y)`. -/
@[dlmf 24.14.E1]
theorem sum_choose_bernoulli_mul_bernoulli (n : ℕ) (x y : A) :
    ∑ k ∈ range (n + 1), (n.choose k : A) * aeval x (Polynomial.bernoulli k) *
        aeval y (Polynomial.bernoulli (n - k)) =
      n • ((x + y - 1) * aeval (x + y) (Polynomial.bernoulli (n - 1))) -
        ((n : A) - 1) * aeval (x + y) (Polynomial.bernoulli n) := by
  set s := x + y
  set E := PowerSeries.exp A
  set F := q24b_egf fun n => aeval s (Polynomial.bernoulli n)
  set es := PowerSeries.rescale s E
  have h1 : F * (E - 1) = PowerSeries.X * es := q24b_egfB_gen s
  have h2 := congrArg (PowerSeries.derivative (R := A)) h1
  simp only [Derivation.leibniz, smul_eq_mul, map_sub, E, PowerSeries.derivative_exp,
    PowerSeries.derivative_one, PowerSeries.derivative_X, es, q24b_derivative_rescale_exp,
    sub_zero] at h2
  set R := (PowerSeries.C s - 1) * PowerSeries.X * F -
    PowerSeries.X * PowerSeries.derivative (R := A) F + F
  have hR : R * (E - 1) * (E - 1) = PowerSeries.X ^ 2 * es := by
    linear_combination ((PowerSeries.C s - 1) * PowerSeries.X * (E - 1) + (E - 1) +
      PowerSeries.X * E) * h1 - PowerSeries.X * (E - 1) * h2
  have hL : q24b_egf (fun n => aeval x (Polynomial.bernoulli n)) *
      q24b_egf (fun n => aeval y (Polynomial.bernoulli n)) * (E - 1) * (E - 1) =
      PowerSeries.X ^ 2 * es := by
    have hx := q24b_egfB_gen x
    have hy := q24b_egfB_gen y
    have hxy := PowerSeries.exp_mul_exp_eq_exp_add x y
    linear_combination (q24b_egf (fun n => aeval y (Polynomial.bernoulli n)) * (E - 1)) * hx +
      (PowerSeries.X * PowerSeries.rescale x E) * hy + PowerSeries.X ^ 2 * hxy
  have hLR := q24b_cancel_exp_sub_one (q24b_cancel_exp_sub_one (hL.trans hR.symm))
  rw [q24b_egf_mul] at hLR
  have hR' : R = q24b_egf fun n => n • ((s - 1) * aeval s (Polynomial.bernoulli (n - 1))) -
      ((n : A) - 1) * aeval s (Polynomial.bernoulli n) := by
    simp only [R, F, q24b_derivative_egf, mul_assoc, q24b_X_mul_egf]
    ext n
    simp only [map_sub, map_add, PowerSeries.coeff_C_mul, sub_mul, one_mul, q24b_coeff_egf,
      nsmul_eq_mul]
    rcases n with _ | n
    · simp
    · simp only [Nat.add_sub_cancel]; push_cast; ring
  rw [hR'] at hLR
  exact q24b_egf_inj hLR n

/-- DLMF 24.14.2: `∑ₖ (n choose k) Bₖ Bₙ₋ₖ = (1 - n) Bₙ - n Bₙ₋₁`. -/
@[dlmf 24.14.E2]
theorem sum_choose_bernoulli_mul_bernoulli_number (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k : ℚ) * _root_.bernoulli k * _root_.bernoulli (n - k) =
      (1 - n) * _root_.bernoulli n - n * _root_.bernoulli (n - 1) := by
  have h := sum_choose_bernoulli_mul_bernoulli n (0 : ℚ) 0
  simp only [coe_aeval_eq_eval, Polynomial.bernoulli_eval_zero, add_zero, zero_sub,
    nsmul_eq_mul] at h
  rw [h]
  ring

/-- DLMF 24.14.3: `∑ₖ (n choose k) Eₖ(h) Eₙ₋ₖ(x) = 2 (Eₙ₊₁(x+h) - (x+h-1) Eₙ(x+h))`. -/
@[dlmf 24.14.E3]
theorem sum_choose_euler_mul_euler (n : ℕ) (x h : A) :
    ∑ k ∈ range (n + 1), (n.choose k : A) * aeval h (Polynomial.euler k) *
        aeval x (Polynomial.euler (n - k)) =
      2 * (aeval (x + h) (Polynomial.euler (n + 1)) -
        (x + h - 1) * aeval (x + h) (Polynomial.euler n)) := by
  set s := x + h
  set E := PowerSeries.exp A
  set F := q24b_egf fun n => aeval s (Polynomial.euler n)
  set es := PowerSeries.rescale s E
  have h1 : F * (E + 1) = 2 * es := q24b_egfE_gen s
  have h2 := congrArg (PowerSeries.derivative (R := A)) h1
  simp only [Derivation.leibniz, smul_eq_mul, map_add, E, PowerSeries.derivative_exp,
    PowerSeries.derivative_one, es, q24b_derivative_rescale_exp, add_zero] at h2
  have h2' : F * E + (E + 1) * PowerSeries.derivative (R := A) F =
      2 * (PowerSeries.C s * es) := by
    have : PowerSeries.derivative (R := A) (2 : PowerSeries A) = 0 := by
      rw [show (2 : PowerSeries A) = PowerSeries.C 2 from (map_ofNat PowerSeries.C 2).symm]
      exact PowerSeries.derivative_C
    rw [this, mul_zero, add_zero] at h2; exact h2
  set R := 2 * (PowerSeries.derivative (R := A) F - (PowerSeries.C s - 1) * F)
  have hR : R * (E + 1) * (E + 1) = 4 * es := by
    linear_combination 2 * (E + 1) * h2' + (-2 * E - 2 * (PowerSeries.C s - 1) * (E + 1)) * h1
  have hL : q24b_egf (fun n => aeval h (Polynomial.euler n)) *
      q24b_egf (fun n => aeval x (Polynomial.euler n)) * (E + 1) * (E + 1) = 4 * es := by
    have hh := q24b_egfE_gen h
    have hx := q24b_egfE_gen x
    have hxy := PowerSeries.exp_mul_exp_eq_exp_add h x
    rw [add_comm h x] at hxy
    linear_combination (q24b_egf (fun n => aeval x (Polynomial.euler n)) * (E + 1)) * hh +
      (2 * PowerSeries.rescale h E) * hx + 4 * hxy
  have hu := (q24b_isUnit_exp_add_one (A := A)).mul_left_injective
  have hLR := hu (hu (hL.trans hR.symm))
  rw [q24b_egf_mul] at hLR
  have hR' : R = q24b_egf fun n => 2 * (aeval s (Polynomial.euler (n + 1)) -
      (s - 1) * aeval s (Polynomial.euler n)) := by
    simp only [R, F, q24b_derivative_egf]
    ext n
    simp only [two_mul, map_add, map_sub, PowerSeries.coeff_C_mul, sub_mul, one_mul,
      q24b_coeff_egf]
    ring
  rw [hR'] at hLR
  exact q24b_egf_inj hLR n

/-- DLMF 24.14.4: `∑ₖ (n choose k) Eₖ Eₙ₋ₖ = -2ⁿ⁺¹ Eₙ₊₁(0)`. -/
@[dlmf 24.14.E4]
theorem sum_choose_eulerNumber_mul_eulerNumber (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k : ℚ) * eulerNumber k * eulerNumber (n - k) =
      -2 ^ (n + 1) * (Polynomial.euler (n + 1)).eval 0 := by
  have h := sum_choose_euler_mul_euler n (1 / 2 : ℚ) (1 / 2)
  have h1 := euler_eval_one_add_eval_zero (n + 1)
  simp only [coe_aeval_eq_eval, show (1 / 2 : ℚ) + 1 / 2 = 1 by norm_num, sub_self, zero_mul,
    sub_zero] at h
  rw [zero_pow (Nat.succ_ne_zero n), mul_zero] at h1
  have key : ∀ k ∈ range (n + 1), (n.choose k : ℚ) * eulerNumber k * eulerNumber (n - k) =
      2 ^ n * ((n.choose k : ℚ) * (euler k).eval (1 / 2) * (euler (n - k)).eval (1 / 2)) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have h2 : (2 : ℚ) ^ n = 2 ^ k * 2 ^ (n - k) := by rw [← pow_add, Nat.add_sub_cancel' hkn]
    rw [eulerNumber, eulerNumber, h2]; ring
  rw [sum_congr rfl key, ← mul_sum, h]
  linear_combination (2 : ℚ) ^ (n + 1) * h1

/-- DLMF 24.14.4 (second equality): `-2ⁿ⁺¹ Eₙ₊₁(0) = -2ⁿ⁺² (1 - 2ⁿ⁺²) Bₙ₊₂/(n+2)`. -/
@[dlmf 24.14.E4]
theorem neg_two_pow_mul_euler_eval_zero (n : ℕ) :
    -2 ^ (n + 1) * (Polynomial.euler (n + 1)).eval 0 =
      -2 ^ (n + 2) * (1 - 2 ^ (n + 2)) * _root_.bernoulli (n + 2) / (n + 2) := by
  have h := b24b_eulerFun_zero (n + 1)
  have h0 : eulerFun (n + 1) 0 = (((Polynomial.euler (n + 1)).eval 0 : ℚ) : ℝ) := by
    rw [eulerFun, show (0 : ℝ) = algebraMap ℚ ℝ 0 by simp, eval_map, eval₂_at_apply]; rfl
  rw [h0] at h
  have hq : (Polynomial.euler (n + 1)).eval 0 =
      -2 * (2 ^ (n + 1 + 1) - 1) * _root_.bernoulli (n + 1 + 1) / (((n + 1 : ℕ) : ℚ) + 1) := by
    exact_mod_cast h
  rw [hq]
  have : (n : ℚ) + 2 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- DLMF 24.14.5: `∑ₖ (n choose k) Eₖ(h) Bₙ₋ₖ(x) = 2ⁿ Bₙ((x+h)/2)`, with `(x+h)/2`
written `(2⁻¹ : ℚ) • (x + h)`. -/
@[dlmf 24.14.E5]
theorem sum_choose_euler_mul_bernoulli (n : ℕ) (x h : A) :
    ∑ k ∈ range (n + 1), (n.choose k : A) * aeval h (Polynomial.euler k) *
        aeval x (Polynomial.bernoulli (n - k)) =
      2 ^ n * aeval ((2⁻¹ : ℚ) • (x + h)) (Polynomial.bernoulli n) := by
  set s := x + h
  set G := q24b_egf fun n => aeval ((2⁻¹ : ℚ) • s) (Polynomial.bernoulli n)
  have hG := q24b_egfB_gen ((2⁻¹ : ℚ) • s)
  have hG2 := congrArg (PowerSeries.rescale (2 : A)) hG
  have hs2 : (2⁻¹ : ℚ) • s * 2 = s := by
    rw [Algebra.smul_def, mul_comm, ← mul_assoc]
    rw [show (2 : A) * algebraMap ℚ A 2⁻¹ = 1 by
      rw [show (2 : A) = algebraMap ℚ A 2 from (map_ofNat (algebraMap ℚ A) 2).symm, ← map_mul]
      norm_num, one_mul]
  have hE2 : PowerSeries.rescale (2 : A) (PowerSeries.exp A) = PowerSeries.exp A ^ 2 := by
    rw [PowerSeries.exp_pow_eq_rescale_exp]; norm_num
  simp only [map_mul, map_sub, map_one, PowerSeries.rescale_X, PowerSeries.rescale_rescale,
    hs2, hE2] at hG2
  have hL : q24b_egf (fun n => aeval h (Polynomial.euler n)) *
      q24b_egf (fun n => aeval x (Polynomial.bernoulli n)) * (PowerSeries.exp A - 1) *
        (PowerSeries.exp A + 1) =
      PowerSeries.C 2 * PowerSeries.X * PowerSeries.rescale s (PowerSeries.exp A) := by
    have hh := q24b_egfE_gen h
    have hx := q24b_egfB_gen x
    have hxy := PowerSeries.exp_mul_exp_eq_exp_add h x
    rw [add_comm h x] at hxy
    have h2 : (PowerSeries.C 2 : PowerSeries A) = 2 := map_ofNat _ 2
    rw [h2]
    linear_combination
      (q24b_egf (fun n => aeval x (Polynomial.bernoulli n)) * (PowerSeries.exp A - 1)) * hh +
      (2 * PowerSeries.rescale h (PowerSeries.exp A)) * hx + 2 * PowerSeries.X * hxy
  have hR : PowerSeries.rescale (2 : A) G * (PowerSeries.exp A - 1) * (PowerSeries.exp A + 1) =
      PowerSeries.C 2 * PowerSeries.X * PowerSeries.rescale s (PowerSeries.exp A) := by
    linear_combination hG2
  have hu := (q24b_isUnit_exp_add_one (A := A)).mul_left_injective
  have hLR := q24b_cancel_exp_sub_one (hu (hL.trans hR.symm))
  rw [q24b_egf_mul, q24b_rescale_egf] at hLR
  exact q24b_egf_inj hLR n

end Quadratic

/-- DLMF 24.14.6: `∑ₖ (n choose k) 2ᵏ Bₖ Eₙ₋ₖ = 2(1 - 2ⁿ⁻¹) Bₙ - n Eₙ₋₁` (with `2ⁿ⁻¹ = 2ⁿ/2`). -/
@[dlmf 24.14.E6]
theorem sum_choose_two_pow_bernoulli_mul_eulerNumber (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k : ℚ) * 2 ^ k * _root_.bernoulli k * eulerNumber (n - k) =
      2 * (1 - 2 ^ n / 2) * _root_.bernoulli n - n * eulerNumber (n - 1) := by
  set P := q24b_egf fun n => aeval (0 : ℚ) (Polynomial.bernoulli n)
  set Q := q24b_egf fun n => aeval (1 / 2 : ℚ) (Polynomial.euler n)
  have k1 : P * ((PowerSeries.exp ℚ) - 1) = PowerSeries.X := by
    rw [q24b_egfB_gen, PowerSeries.rescale_zero_apply, PowerSeries.constantCoeff_exp, map_one,
      mul_one]
  have hE2 : PowerSeries.rescale (2 : ℚ) (PowerSeries.exp ℚ) = (PowerSeries.exp ℚ) ^ 2 := by
    rw [PowerSeries.exp_pow_eq_rescale_exp]; norm_num
  have k2 : PowerSeries.rescale (2 : ℚ) P * ((PowerSeries.exp ℚ) ^ 2 - 1) =
      PowerSeries.C 2 * PowerSeries.X := by
    have := congrArg (PowerSeries.rescale (2 : ℚ)) k1
    simpa only [map_mul, map_sub, map_one, hE2, PowerSeries.rescale_X] using this
  have k3 : PowerSeries.rescale (2 : ℚ) Q * ((PowerSeries.exp ℚ) ^ 2 + 1) =
      2 * (PowerSeries.exp ℚ) := by
    have := congrArg (PowerSeries.rescale (2 : ℚ)) (q24b_egfE_gen (1 / 2 : ℚ))
    simp only [map_mul, map_add, map_one, hE2, PowerSeries.rescale_rescale, map_ofNat] at this
    rw [this]; norm_num
  have h2 : (PowerSeries.C 2 : PowerSeries ℚ) = 2 := map_ofNat _ 2
  rw [h2] at k2
  set L := PowerSeries.rescale (2 : ℚ) P * PowerSeries.rescale (2 : ℚ) Q
  set R := 2 * P - PowerSeries.rescale (2 : ℚ) P - PowerSeries.X * PowerSeries.rescale (2 : ℚ) Q
  have hL : L * ((PowerSeries.exp ℚ) - 1) * ((PowerSeries.exp ℚ) + 1) *
      ((PowerSeries.exp ℚ) ^ 2 + 1) = 4 * PowerSeries.X * (PowerSeries.exp ℚ) := by
    linear_combination (PowerSeries.rescale (2 : ℚ) Q * ((PowerSeries.exp ℚ) ^ 2 + 1)) * k2 +
      2 * PowerSeries.X * k3
  have hR : R * ((PowerSeries.exp ℚ) - 1) * ((PowerSeries.exp ℚ) + 1) *
      ((PowerSeries.exp ℚ) ^ 2 + 1) = 4 * PowerSeries.X * (PowerSeries.exp ℚ) := by
    linear_combination 2 * ((PowerSeries.exp ℚ) + 1) * ((PowerSeries.exp ℚ) ^ 2 + 1) * k1 -
      ((PowerSeries.exp ℚ) ^ 2 + 1) * k2 - PowerSeries.X * ((PowerSeries.exp ℚ) ^ 2 - 1) * k3
  have hu3 : IsUnit ((PowerSeries.exp ℚ) ^ 2 + 1) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]; simp
  have hLR := q24b_cancel_exp_sub_one (q24b_isUnit_exp_add_one.mul_left_injective
    (hu3.mul_left_injective (hL.trans hR.symm)))
  simp only [L, R, P, Q, q24b_rescale_egf, q24b_egf_mul, q24b_X_mul_egf] at hLR
  have hR' : (2 * q24b_egf fun n => aeval (0 : ℚ) (Polynomial.bernoulli n)) -
      (q24b_egf fun n => 2 ^ n * aeval (0 : ℚ) (Polynomial.bernoulli n)) -
      (q24b_egf fun n => (n : ℚ) * (2 ^ (n - 1) * aeval (1 / 2 : ℚ) (Polynomial.euler (n - 1)))) =
      q24b_egf fun n => 2 * (1 - 2 ^ n / 2) * _root_.bernoulli n - n * eulerNumber (n - 1) := by
    ext m
    simp only [two_mul, map_add, map_sub, q24b_coeff_egf, coe_aeval_eq_eval,
      Polynomial.bernoulli_eval_zero, eulerNumber]
    ring
  rw [hR'] at hLR
  have := q24b_egf_inj hLR n
  rw [← this]
  refine sum_congr rfl fun k hk => ?_
  simp only [coe_aeval_eq_eval, Polynomial.bernoulli_eval_zero, eulerNumber]
  ring

/-- DLMF 24.14.7: for `m, n ≥ 1` with `m + n` even,
`∑ⱼ ∑ₖ (m choose j)(n choose k) Bⱼ Bₖ/(m+n-j-k+1) = (-1)^{m-1} m! n!/(m+n)! · B_{m+n}`. -/
@[dlmf 24.14.E7]
theorem sum_choose_mul_bernoulli_mul_bernoulli_div {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (he : Even (m + n)) :
    ∑ j ∈ range (m + 1), ∑ k ∈ range (n + 1),
        (m.choose j : ℚ) * n.choose k * _root_.bernoulli j * _root_.bernoulli k /
          (m + n - j - k + 1) =
      (-1) ^ (m - 1) * (m ! * n ! / (m + n)! : ℚ) * _root_.bernoulli (m + n) := by
  have hI : ∫ t in (0 : ℝ)..1, bernoulliFun n t * bernoulliFun m t =
      ∑ j ∈ range (m + 1), ∑ k ∈ range (n + 1),
        ((m.choose j : ℚ) * n.choose k * _root_.bernoulli j * _root_.bernoulli k /
          (m + n - j - k + 1) : ℚ) := by
    simp_rw [mul_comm (bernoulliFun n _), q24b_bernoulliFun_eq_sum n, q24b_bernoulliFun_eq_sum m,
      sum_mul_sum]
    rw [intervalIntegral.integral_finsetSum (fun j _ => by
      exact (continuous_finsetSum _ fun k _ => by fun_prop).intervalIntegrable _ _)]
    push_cast
    refine sum_congr rfl fun j hj => ?_
    rw [intervalIntegral.integral_finsetSum (fun k _ => by
      exact (by fun_prop : Continuous _).intervalIntegrable _ _)]
    refine sum_congr rfl fun k hk => ?_
    have hjm : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have : ∀ t : ℝ, (m.choose j : ℝ) * _root_.bernoulli j * t ^ (m - j) *
        ((n.choose k : ℝ) * _root_.bernoulli k * t ^ (n - k)) =
        ((m.choose j : ℝ) * n.choose k * _root_.bernoulli j * _root_.bernoulli k) *
          t ^ ((m - j) + (n - k)) := by intro t; rw [pow_add]; ring
    simp_rw [this]
    rw [intervalIntegral.integral_const_mul, integral_pow]
    have hc : (((m - j) + (n - k) : ℕ) : ℝ) + 1 = m + n - j - k + 1 := by
      push_cast [hjm, hkn]; ring
    rw [hc]; simp; ring
  have hsign : (-1 : ℝ) ^ (n - 1) = (-1) ^ (m - 1) := by
    rw [neg_one_pow_eq_pow_mod_two (R := ℝ), neg_one_pow_eq_pow_mod_two (R := ℝ) (n := m - 1),
      show (n - 1) % 2 = (m - 1) % 2 by obtain ⟨k, hk⟩ := he; omega]
  rw [integral_bernoulliFun_mul_bernoulliFun hm hn, hsign] at hI
  apply Rat.cast_injective (α := ℝ)
  push_cast at hI ⊢
  linarith

/-! ### Helpers for §24.14(ii) -/

/-- Sums over `j + k + ℓ = n` as iterated sums. -/
lemma q24b_sum_antidiagonalTuple_three {M : Type*} [AddCommMonoid M] (n : ℕ)
    (F : ℕ → ℕ → ℕ → M) :
    ∑ v ∈ Finset.Nat.antidiagonalTuple 3 n, F (v 0) (v 1) (v 2) =
      ∑ a ∈ range (n + 1), ∑ c ∈ range (n - a + 1), F a c (n - a - c) := by
  rw [Finset.sum_sigma' (range (n + 1)) (fun a => range (n - a + 1))
    (fun a c => F a c (n - a - c))]
  refine Finset.sum_nbij' (fun v => ⟨v 0, v 1⟩) (fun p => ![p.1, p.2, n - p.1 - p.2])
    ?_ ?_ ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_sigma, Finset.mem_range]
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three] at hv
    constructor <;> omega
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    omega
  · intro v hv
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three] at hv
    funext i; fin_cases i <;> simp; omega
  · intro p _; simp
  · intro v hv
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three] at hv
    simp only
    congr 1; omega

/-- Summing a sequence vanishing at odd indices over its even indices. -/
private lemma sum_range_even_aux {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M)
    (hf : ∀ j, Odd j → f j = 0) :
    ∑ k ∈ range (n / 2 + 1), f (2 * k) = ∑ j ∈ range (n + 1), f j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ _ (n + 1), ← ih]
    rcases Nat.even_or_odd (n + 1) with he | ho
    · obtain ⟨m, hm⟩ := he
      rw [show (n + 1) / 2 = n / 2 + 1 by omega, sum_range_succ,
        show 2 * (n / 2 + 1) = n + 1 by omega]
    · rw [hf _ ho, add_zero, show (n + 1) / 2 = n / 2 by obtain ⟨m, hm⟩ := ho; omega]

/-- Differences of exponential generating functions. -/
lemma q24b_egf_sub {A : Type*} [CommRing A] [Algebra ℚ A] (a b : ℕ → A) :
    q24b_egf a - q24b_egf b = q24b_egf fun n => a n - b n := by
  ext n; simp only [map_sub, q24b_coeff_egf]; ring

/-- The triple binomial convolution of a sequence vanishing at odd indices, at an even index,
as a sum over `j + k + ℓ = n`. -/
lemma q24b_triple_conv_even (b : ℕ → ℚ) (hb : ∀ j, Odd j → b j = 0) (n : ℕ) :
    ∑ i ∈ range (2 * n + 1), ((2 * n).choose i : ℚ) * b i *
        ∑ j ∈ range (2 * n - i + 1), ((2 * n - i).choose j : ℚ) * b j * b (2 * n - i - j) =
      ∑ v ∈ Finset.Nat.antidiagonalTuple 3 n,
        ((2 * n)! / ((2 * v 0)! * (2 * v 1)! * (2 * v 2)!) : ℚ) *
          b (2 * v 0) * b (2 * v 1) * b (2 * v 2) := by
  rw [q24b_sum_antidiagonalTuple_three n (fun a c d => ((2 * n)! / ((2 * a)! * (2 * c)! *
    (2 * d)!) : ℚ) * b (2 * a) * b (2 * c) * b (2 * d))]
  rw [← sum_range_even_aux (2 * n) _ (fun j hj => by simp [hb j hj])]
  rw [show 2 * n / 2 = n by omega]
  refine sum_congr rfl fun a ha => ?_
  have han : a ≤ n := Nat.lt_succ_iff.mp (mem_range.mp ha)
  rw [← sum_range_even_aux (2 * n - 2 * a) _ (fun j hj => by simp [hb j hj])]
  rw [show (2 * n - 2 * a) / 2 = n - a by omega, mul_sum]
  refine sum_congr rfl fun c hc => ?_
  have hcn : c ≤ n - a := Nat.lt_succ_iff.mp (mem_range.mp hc)
  rw [show 2 * n - 2 * a - 2 * c = 2 * (n - a - c) by omega,
    Nat.cast_choose ℚ (show 2 * a ≤ 2 * n by omega),
    Nat.cast_choose ℚ (show 2 * c ≤ 2 * n - 2 * a by omega),
    show 2 * n - 2 * a - 2 * c = 2 * (n - a - c) by omega,
    show 2 * n - 2 * a = 2 * n - 2 * a by rfl]
  have h1 : ((2 * n - 2 * a)! : ℚ) ≠ 0 := by positivity
  have h2 : ((2 * a)! : ℚ) ≠ 0 := by positivity
  have h3 : ((2 * c)! : ℚ) ≠ 0 := by positivity
  have h4 : ((2 * (n - a - c))! : ℚ) ≠ 0 := by positivity
  field_simp

/-- The derivative of the constant power series `2`. -/
lemma q24b_derivative_two {A : Type*} [CommRing A] [Algebra ℚ A] :
    PowerSeries.derivative (R := A) (2 : PowerSeries A) = 0 := by
  rw [show (2 : PowerSeries A) = PowerSeries.C 2 from (map_ofNat PowerSeries.C 2).symm]
  exact PowerSeries.derivative_C

/-- Sums over `j + k + ℓ + m = n` as a sum over the first index and a triple sum. -/
lemma q24b_sum_antidiagonalTuple_four {M : Type*} [AddCommMonoid M] (n : ℕ)
    (F : ℕ → ℕ → ℕ → ℕ → M) :
    ∑ v ∈ Finset.Nat.antidiagonalTuple 4 n, F (v 0) (v 1) (v 2) (v 3) =
      ∑ a ∈ range (n + 1), ∑ w ∈ Finset.Nat.antidiagonalTuple 3 (n - a),
        F a (w 0) (w 1) (w 2) := by
  rw [Finset.sum_sigma' (range (n + 1)) (fun a => Finset.Nat.antidiagonalTuple 3 (n - a))
    (fun a w => F a (w 0) (w 1) (w 2))]
  refine Finset.sum_nbij' (fun v => ⟨v 0, ![v 1, v 2, v 3]⟩)
    (fun p => ![p.1, p.2 0, p.2 1, p.2 2]) ?_ ?_ ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.Nat.mem_antidiagonalTuple,
      Fin.sum_univ_three, Fin.sum_univ_four] at hv ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    constructor <;> omega
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.Nat.mem_antidiagonalTuple,
      Fin.sum_univ_three, Fin.sum_univ_four] at hp ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    omega
  · intro v _
    funext i; fin_cases i <;> rfl
  · intro p _
    refine Sigma.ext rfl (heq_of_eq ?_)
    funext i; fin_cases i <;> rfl
  · intro v _
    rfl

/-- The fourfold binomial convolution of a sequence vanishing at odd indices, at an even
index, as a sum over `j + k + ℓ + m = n`. -/
lemma q24b_quad_conv_even (b : ℕ → ℚ) (hb : ∀ j, Odd j → b j = 0) (n : ℕ) :
    ∑ i ∈ range (2 * n + 1), ((2 * n).choose i : ℚ) * b i *
        ∑ j ∈ range (2 * n - i + 1), ((2 * n - i).choose j : ℚ) * b j *
          ∑ k ∈ range (2 * n - i - j + 1), ((2 * n - i - j).choose k : ℚ) * b k *
            b (2 * n - i - j - k) =
      ∑ v ∈ Finset.Nat.antidiagonalTuple 4 n,
        ((2 * n)! / ((2 * v 0)! * (2 * v 1)! * (2 * v 2)! * (2 * v 3)!) : ℚ) *
          b (2 * v 0) * b (2 * v 1) * b (2 * v 2) * b (2 * v 3) := by
  rw [q24b_sum_antidiagonalTuple_four n (fun a c d e => ((2 * n)! / ((2 * a)! * (2 * c)! *
    (2 * d)! * (2 * e)!) : ℚ) * b (2 * a) * b (2 * c) * b (2 * d) * b (2 * e))]
  rw [← sum_range_even_aux (2 * n) _ (fun j hj => by simp [hb j hj])]
  rw [show 2 * n / 2 = n by omega]
  refine sum_congr rfl fun a ha => ?_
  have han : a ≤ n := Nat.lt_succ_iff.mp (mem_range.mp ha)
  rw [show 2 * n - 2 * a = 2 * (n - a) by omega, q24b_triple_conv_even b hb (n - a), mul_sum]
  refine sum_congr rfl fun w _ => ?_
  rw [Nat.cast_choose ℚ (show 2 * a ≤ 2 * n by omega),
    show 2 * n - 2 * a = 2 * (n - a) by omega]
  have h1 : ((2 * (n - a))! : ℚ) ≠ 0 := by positivity
  have h2 : ((2 * a)! : ℚ) ≠ 0 := by positivity
  have h3 : ((2 * w 0)! : ℚ) ≠ 0 := by positivity
  have h4 : ((2 * w 1)! : ℚ) ≠ 0 := by positivity
  have h5 : ((2 * w 2)! : ℚ) ≠ 0 := by positivity
  field_simp

/-! ### §24.14(ii) Higher-order recurrence relations -/

/-- DLMF 24.14.8: for `n ≥ 2`, summing over `j + k + ℓ = n`,
`∑ (2n)!/((2j)!(2k)!(2ℓ)!) B₂ⱼ B₂ₖ B₂ₗ = (n-1)(2n-1) B₂ₙ + n(n - 1/2) B₂ₙ₋₂`. -/
@[dlmf 24.14.E8]
theorem sum_antidiagonal_bernoulli_triple {n : ℕ} (hn : 2 ≤ n) :
    ∑ v ∈ Finset.Nat.antidiagonalTuple 3 n,
        ((2 * n)! / ((2 * v 0)! * (2 * v 1)! * (2 * v 2)!) : ℚ) *
          _root_.bernoulli (2 * v 0) * _root_.bernoulli (2 * v 1) * _root_.bernoulli (2 * v 2) =
      (n - 1) * (2 * n - 1) * _root_.bernoulli (2 * n) +
        n * (n - 1 / 2) * _root_.bernoulli (2 * n - 2) := by
  set b : ℕ → ℚ := fun m => if m = 1 then 0 else _root_.bernoulli m
  set f := q24b_egf b
  set E := PowerSeries.exp ℚ
  set X : PowerSeries ℚ := PowerSeries.X
  have hB : q24b_egf (fun m => (_root_.bernoulli m : ℚ)) * (E - 1) = X := by
    have := q24b_egfB_gen (0 : ℚ)
    simp only [Polynomial.aeval_def, Polynomial.eval₂_at_zero] at this
    simpa [Polynomial.coeff_zero_eq_eval_zero, Polynomial.bernoulli_eval_zero,
      PowerSeries.rescale_zero, E, X] using this
  have h2 : (2 : PowerSeries ℚ) = PowerSeries.C 2 := (map_ofNat PowerSeries.C 2).symm
  have hf : 2 * f = 2 * q24b_egf (fun m => (_root_.bernoulli m : ℚ)) + X := by
    ext m
    rw [map_add, h2, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, q24b_coeff_egf,
      q24b_coeff_egf]
    rcases m with _ | _ | m <;> norm_num [b, X, PowerSeries.coeff_X]
  have r0 : 2 * f * (E - 1) = X * (E + 1) := by
    rw [hf, add_mul, mul_assoc, hB]
    ring
  set D := PowerSeries.derivative (R := ℚ)
  have hDE : D E = E := PowerSeries.derivative_exp ℚ
  have hDX : D X = 1 := PowerSeries.derivative_X
  have hD2 : D 2 = 0 := q24b_derivative_two
  have r1 := congrArg D r0
  simp only [Derivation.leibniz, smul_eq_mul, map_add, map_sub, hDE, hDX, D.map_one_eq_zero,
    hD2, add_zero, mul_zero, sub_zero, mul_one] at r1
  have r2 := congrArg D r1
  simp only [Derivation.leibniz, smul_eq_mul, map_add, map_sub, hDE, hDX, D.map_one_eq_zero,
    hD2, add_zero, mul_zero, sub_zero, mul_one] at r2
  have key3 : (8 * f ^ 3 * (E - 1) * (E - 1)) * (E - 1) =
      ((8 * f - 8 * (X * D f) + 4 * (X * (X * D (D f))) + 2 * (X * (X * f))) * (E - 1) *
        (E - 1)) * (E - 1) := by
    linear_combination ((E - 1) * (-2 * E * X ^ 2 + E * X * (2 * f) - 4 * E * X + E * (2 * f) ^ 2
      - 4 * E + X * (2 * f) - (2 * f) ^ 2 + 4)) * r0 +
      (4 * X * (E - 1) * (E * X + E - 1)) * r1 - (2 * X ^ 2 * (E - 1) ^ 2) * r2
  have key := q24b_cancel_exp_sub_one (q24b_cancel_exp_sub_one (q24b_cancel_exp_sub_one key3))
  simp only [f, D, X, pow_three, q24b_egf_mul, q24b_derivative_egf, q24b_X_mul_egf] at key
  have hc := congrArg (PowerSeries.coeff (2 * n)) key
  simp only [show (8 : PowerSeries ℚ) = PowerSeries.C 8 from (map_ofNat PowerSeries.C 8).symm,
    show (4 : PowerSeries ℚ) = PowerSeries.C 4 from (map_ofNat PowerSeries.C 4).symm, h2,
    map_add, map_sub, PowerSeries.coeff_C_mul, q24b_coeff_egf, Algebra.algebraMap_self,
    RingHom.id_apply] at hc
  have hf : ((2 * n)! : ℚ) ≠ 0 := by positivity
  have hc' := congrArg (fun t => ((2 * n)! : ℚ) * t / 8) hc
  simp only [mul_add, mul_sub, add_div, sub_div] at hc'
  simp only [← mul_assoc, mul_comm _ ((2 * n)! : ℚ)⁻¹, inv_mul_cancel₀ hf, one_mul] at hc'
  rw [show 2 * n - 1 - 1 + 1 + 1 = 2 * n by omega, show 2 * n - 1 + 1 = 2 * n by omega,
    show 2 * n - 1 - 1 = 2 * n - 2 by omega] at hc'
  have hbodd : ∀ j, Odd j → b j = 0 := by
    intro j hj
    by_cases h1 : j = 1
    · simp [b, h1]
    · simp only [b, h1, ite_false]
      exact bernoulli_eq_zero_of_odd hj (by obtain ⟨k, hk⟩ := hj; omega)
  have hbe : ∀ k, b (2 * k) = _root_.bernoulli (2 * k) := fun k => by
    simp only [b, show 2 * k ≠ 1 by omega, ite_false]
  rw [q24b_triple_conv_even b hbodd n, show 2 * n - 2 = 2 * (n - 1) by omega] at hc'
  simp only [hbe] at hc'
  rw [show 2 * n - 2 = 2 * (n - 1) by omega]
  push_cast [show 1 ≤ 2 * n by omega] at hc'
  linear_combination hc'

/-- DLMF 24.14.9: for `n ≥ 2`, summing over `j + k + ℓ = n`,
`∑ (2n)!/((2j)!(2k)!(2ℓ)!) E₂ⱼ E₂ₖ E₂ₗ = (E₂ₙ - E₂ₙ₊₂)/2`. -/
@[dlmf 24.14.E9]
theorem sum_antidiagonal_eulerNumber_triple {n : ℕ} (hn : 2 ≤ n) :
    ∑ v ∈ Finset.Nat.antidiagonalTuple 3 n,
        ((2 * n)! / ((2 * v 0)! * (2 * v 1)! * (2 * v 2)!) : ℚ) *
          eulerNumber (2 * v 0) * eulerNumber (2 * v 1) * eulerNumber (2 * v 2) =
      (eulerNumber (2 * n) - eulerNumber (2 * n + 2)) / 2 := by
  have _ := hn
  set F := q24b_egf fun N => eulerNumber N
  have hE2 : PowerSeries.rescale (2 : ℚ) (PowerSeries.exp ℚ) = PowerSeries.exp ℚ ^ 2 := by
    rw [PowerSeries.exp_pow_eq_rescale_exp]; norm_num
  have r0 : F * (PowerSeries.exp ℚ ^ 2 + 1) = 2 * PowerSeries.exp ℚ := by
    have := congrArg (PowerSeries.rescale (2 : ℚ)) (q24b_egfE_gen (1 / 2 : ℚ))
    simp only [map_mul, map_add, map_one, hE2, PowerSeries.rescale_rescale, map_ofNat,
      q24b_rescale_egf] at this
    rw [show (1 / 2 : ℚ) * 2 = 1 by norm_num, PowerSeries.rescale_one] at this
    convert this using 2
    simp only [F]; congr 1
  set D := PowerSeries.derivative (R := ℚ)
  have hDE : D (PowerSeries.exp ℚ) = PowerSeries.exp ℚ := PowerSeries.derivative_exp ℚ
  have hDE2 : D (PowerSeries.exp ℚ ^ 2) = 2 * PowerSeries.exp ℚ ^ 2 := by
    rw [pow_two, Derivation.leibniz, hDE, smul_eq_mul]; ring
  have hD2 : D 2 = 0 := q24b_derivative_two
  have r1 := congrArg D r0
  simp only [Derivation.leibniz, smul_eq_mul, map_add, hDE, hDE2, D.map_one_eq_zero,
    hD2, add_zero, mul_zero] at r1
  have r2 := congrArg D r1
  simp only [Derivation.leibniz, smul_eq_mul, map_add, hDE, hDE2, D.map_one_eq_zero,
    hD2, add_zero, mul_zero] at r2
  set E := PowerSeries.exp ℚ
  set w := E ^ 2 + 1
  have key : 2 * F ^ 3 = F - D (D F) := by
    have hw : IsUnit w := by
      rw [PowerSeries.isUnit_iff_constantCoeff]; simp [w, E]
    apply (hw.pow 3).mul_left_injective
    simp only
    linear_combination (2 * ((F * w) ^ 2 + 2 * E * (F * w) + 4 * E ^ 2) - w ^ 2 +
      (8 * E ^ 4 - 4 * E ^ 2 * w)) * r0 + (-4 * E ^ 2 * w) * r1 + w ^ 2 * r2
  rw [pow_three, q24b_egf_mul, q24b_egf_mul, q24b_derivative_egf, q24b_derivative_egf,
    q24b_egf_sub] at key
  have hc := congrArg (PowerSeries.coeff (2 * n)) key
  rw [show (2 : PowerSeries ℚ) = PowerSeries.C 2 from (map_ofNat PowerSeries.C 2).symm,
    PowerSeries.coeff_C_mul, q24b_coeff_egf, q24b_coeff_egf] at hc
  have hf : ((2 * n)! : ℚ) ≠ 0 := by positivity
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hc
  rw [← q24b_triple_conv_even _ (fun j hj => eulerNumber_eq_zero_of_odd hj) n]
  have hc' := congrArg (fun t => ((2 * n)! : ℚ) * t / 2) hc
  simp only [← mul_assoc, mul_comm _ (2 : ℚ)] at hc'
  rw [mul_assoc 2, mul_inv_cancel₀ hf, mul_one] at hc'
  linear_combination hc'

/-- DLMF 24.14.10: for `n ≥ 4`, summing over positive `j + k + ℓ + m = n`,
`∑ (2n)!/((2j)!(2k)!(2ℓ)!(2m)!) B₂ⱼ B₂ₖ B₂ₗ B₂ₘ = -(2n+3 choose 3) B₂ₙ - (4/3) n²(2n-1) B₂ₙ₋₂`. -/
@[dlmf 24.14.E10]
theorem sum_antidiagonal_bernoulli_quadruple {n : ℕ} (hn : 4 ≤ n) :
    ∑ v ∈ (Finset.Nat.antidiagonalTuple 4 n).filter (fun v => ∀ i, 0 < v i),
        ((2 * n)! / ((2 * v 0)! * (2 * v 1)! * (2 * v 2)! * (2 * v 3)!) : ℚ) *
          _root_.bernoulli (2 * v 0) * _root_.bernoulli (2 * v 1) * _root_.bernoulli (2 * v 2) *
            _root_.bernoulli (2 * v 3) =
      -((2 * n + 3).choose 3 : ℚ) * _root_.bernoulli (2 * n) -
        4 / 3 * n ^ 2 * (2 * n - 1) * _root_.bernoulli (2 * n - 2) := by
  set b : ℕ → ℚ := fun m => if m = 1 then 0 else _root_.bernoulli m
  set c : ℕ → ℚ := fun m => if m ≤ 1 then 0 else _root_.bernoulli m
  set f := q24b_egf b
  set C := q24b_egf c
  set E := PowerSeries.exp ℚ
  set X : PowerSeries ℚ := PowerSeries.X
  have hB : q24b_egf (fun m => (_root_.bernoulli m : ℚ)) * (E - 1) = X := by
    have := q24b_egfB_gen (0 : ℚ)
    simpa [Polynomial.coeff_zero_eq_eval_zero, Polynomial.bernoulli_eval_zero,
      PowerSeries.rescale_zero, E, X] using this
  have h2 : (2 : PowerSeries ℚ) = PowerSeries.C 2 := (map_ofNat PowerSeries.C 2).symm
  have hf : 2 * f = 2 * q24b_egf (fun m => (_root_.bernoulli m : ℚ)) + X := by
    ext m
    rw [map_add, h2, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, q24b_coeff_egf,
      q24b_coeff_egf]
    rcases m with _ | _ | m <;> norm_num [b, X, PowerSeries.coeff_X]
  have hcf : 2 * C = 2 * f - 2 := by
    ext m
    rw [map_sub, h2, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, q24b_coeff_egf,
      q24b_coeff_egf, PowerSeries.coeff_C]
    rcases m with _ | _ | m <;> norm_num [b, c]
  have r0 : 2 * f * (E - 1) = X * (E + 1) := by
    rw [hf, add_mul, mul_assoc, hB]
    ring
  set D := PowerSeries.derivative (R := ℚ)
  have hDE : D E = E := PowerSeries.derivative_exp ℚ
  have hDX : D X = 1 := PowerSeries.derivative_X
  have hD2 : D 2 = 0 := q24b_derivative_two
  have r1 := congrArg D r0
  simp only [Derivation.leibniz, smul_eq_mul, map_add, map_sub, hDE, hDX, D.map_one_eq_zero,
    hD2, add_zero, mul_zero, sub_zero, mul_one] at r1
  have r2 := congrArg D r1
  simp only [Derivation.leibniz, smul_eq_mul, map_add, map_sub, hDE, hDX, D.map_one_eq_zero,
    hD2, add_zero, mul_zero, sub_zero, mul_one] at r2
  have r3 := congrArg D r2
  simp only [Derivation.leibniz, smul_eq_mul, map_add, map_sub, hDE, hDX, D.map_one_eq_zero,
    hD2, add_zero, mul_zero, sub_zero, mul_one] at r3
  have key4 : (48 * C ^ 4 * (E - 1) * (E - 1) * (E - 1)) * (E - 1) =
      ((-48 * f - 144 * (X * D f) - 72 * (X * (X * D (D f))) -
        8 * (X * (X * (X * D (D (D f))))) - 32 * (X * (X * f)) - 16 * (X * (X * (X * D f))) +
        48 + 72 * X ^ 2 + 3 * X ^ 4) * (E - 1) * (E - 1) * (E - 1)) * (E - 1) := by
    linear_combination
      ((E - 1) * (-9 * E ^ 2 * X ^ 3 + 3 * E ^ 2 * X ^ 2 * (2 * f) + 28 * E ^ 2 * X ^ 2 +
        3 * E ^ 2 * X * (2 * f) ^ 2 - 24 * E ^ 2 * X * (2 * f) + 3 * E ^ 2 * (2 * f) ^ 3 -
        24 * E ^ 2 * (2 * f) ^ 2 + 72 * E ^ 2 * (2 * f) - 72 * E ^ 2 + 6 * E * X ^ 2 * (2 * f) -
        44 * E * X ^ 2 + 72 * E * X - 6 * E * (2 * f) ^ 3 + 48 * E * (2 * f) ^ 2 -
        144 * E * (2 * f) + 144 * E - 3 * X ^ 3 + 3 * X ^ 2 * (2 * f) - 8 * X ^ 2 -
        3 * X * (2 * f) ^ 2 + 24 * X * (2 * f) - 72 * X + 3 * (2 * f) ^ 3 - 24 * (2 * f) ^ 2 +
        72 * (2 * f) - 72)) * r0 +
      (4 * X * (E - 1) * (5 * E ^ 2 * X ^ 2 - 18 * E ^ 2 * X + 18 * E ^ 2 - E * X ^ 2 +
        18 * E * X - 36 * E + 2 * X ^ 2 + 18)) * r1 +
      (-12 * X ^ 2 * (E - 1) ^ 2 * (E * X - 3 * E + 3)) * r2 +
      (4 * X ^ 3 * (E - 1) ^ 3) * r3 +
      (3 * ((2 * C) ^ 3 + (2 * C) ^ 2 * (2 * f - 2) + (2 * C) * (2 * f - 2) ^ 2 +
        (2 * f - 2) ^ 3) * (E - 1) ^ 4) * hcf
  have key := q24b_cancel_exp_sub_one (q24b_cancel_exp_sub_one (q24b_cancel_exp_sub_one
    (q24b_cancel_exp_sub_one key4)))
  rw [show C ^ 4 = C * (C * (C * C)) by ring] at key
  simp only [C, f, D, X, q24b_egf_mul, q24b_derivative_egf, q24b_X_mul_egf] at key
  have hc := congrArg (PowerSeries.coeff (2 * n)) key
  have hC : ∀ k : ℕ, [k.AtLeastTwo] →
      (OfNat.ofNat k : PowerSeries ℚ) = PowerSeries.C (OfNat.ofNat k : ℚ) :=
    fun k _ => (map_ofNat PowerSeries.C k).symm
  simp only [hC, neg_mul, map_add, map_sub, map_neg, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C, PowerSeries.coeff_X_pow, q24b_coeff_egf, Algebra.algebraMap_self,
    RingHom.id_apply, show 2 * n ≠ 0 by omega, show 2 * n ≠ 2 by omega,
    show 2 * n ≠ 4 by omega, ite_false, mul_zero, add_zero] at hc
  rw [show 2 * n - 1 - 1 - 1 + 1 + 1 + 1 = 2 * n by omega,
    show 2 * n - 1 - 1 - 1 + 1 = 2 * n - 2 by omega,
    show 2 * n - 1 - 1 + 1 + 1 = 2 * n by omega, show 2 * n - 1 + 1 = 2 * n by omega,
    show 2 * n - 1 - 1 = 2 * n - 2 by omega] at hc
  have hcodd : ∀ j, Odd j → c j = 0 := by
    intro j hj
    by_cases h1 : j ≤ 1
    · simp [c, h1]
    · simp only [c, h1, ite_false]
      exact bernoulli_eq_zero_of_odd hj (by omega)
  rw [q24b_quad_conv_even c hcodd n] at hc
  have hb2 : b (2 * n) = _root_.bernoulli (2 * n) := by
    simp only [b, show ¬ 2 * n = 1 by omega, ite_false]
  have hb2' : b (2 * n - 2) = _root_.bernoulli (2 * n - 2) := by
    simp only [b, show ¬ 2 * n - 2 = 1 by omega, ite_false]
  rw [hb2, hb2'] at hc
  have hfil : ∑ v ∈ (Finset.Nat.antidiagonalTuple 4 n).filter (fun v => ∀ i, 0 < v i),
        ((2 * n)! / ((2 * v 0)! * (2 * v 1)! * (2 * v 2)! * (2 * v 3)!) : ℚ) *
          _root_.bernoulli (2 * v 0) * _root_.bernoulli (2 * v 1) * _root_.bernoulli (2 * v 2) *
            _root_.bernoulli (2 * v 3) =
      ∑ v ∈ Finset.Nat.antidiagonalTuple 4 n,
        ((2 * n)! / ((2 * v 0)! * (2 * v 1)! * (2 * v 2)! * (2 * v 3)!) : ℚ) *
          c (2 * v 0) * c (2 * v 1) * c (2 * v 2) * c (2 * v 3) := by
    rw [Finset.sum_filter]
    refine sum_congr rfl fun v _ => ?_
    split_ifs with h
    · have hc' : ∀ i, c (2 * v i) = _root_.bernoulli (2 * v i) := fun i => by
        simp only [c, show ¬ 2 * v i ≤ 1 by have := h i; omega, ite_false]
      rw [hc', hc', hc', hc']
    · push Not at h
      obtain ⟨i, hi⟩ := h
      have hi0 : c (2 * v i) = 0 := by simp [show v i = 0 by omega, c]
      fin_cases i
      all_goals (simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hi0
                 simp [hi0])
  rw [hfil]
  have hch : ((2 * n + 3).choose 3 : ℚ) = (2 * n + 3) * (2 * n + 2) * (2 * n + 1) / 6 := by
    rw [Nat.cast_choose ℚ (by omega : 3 ≤ 2 * n + 3), show 2 * n + 3 - 3 = 2 * n by omega]
    simp [Nat.factorial_succ]
    field_simp
    ring
  have hf0 : ((2 * n)! : ℚ) ≠ 0 := by positivity
  have hc' := congrArg (fun t => ((2 * n)! : ℚ) * t / 48) hc
  simp only [mul_sub, mul_neg, sub_div, neg_div] at hc'
  simp only [← mul_assoc, mul_comm _ ((2 * n)! : ℚ)⁻¹, inv_mul_cancel₀ hf0, one_mul] at hc'
  push_cast [show 1 ≤ 2 * n by omega, show 2 ≤ 2 * n by omega] at hc'
  rw [hch]
  linear_combination hc'

/-- DLMF 24.14.11: the Hankel determinant `det[B_{r+s}]_{r,s=0}^{n}` equals
`(-1)^{n(n+1)/2} (∏_{k=1}^n k!)⁶ / ∏_{k=1}^{2n+1} k!`. -/
@[dlmf 24.14.E11]
theorem det_hankel_bernoulli (n : ℕ) :
    (Matrix.of fun r s : Fin (n + 1) => _root_.bernoulli (r + s : ℕ)).det =
      (-1) ^ (n * (n + 1) / 2) * (∏ k ∈ Finset.Icc 1 n, (k ! : ℚ)) ^ 6 /
        ∏ k ∈ Finset.Icc 1 (2 * n + 1), (k ! : ℚ) := by
  sorry

/-- DLMF 24.14.12: the Hankel determinant `det[E_{r+s}]_{r,s=0}^{n}` equals
`(-1)^{n(n+1)/2} (∏_{k=1}^n k!)²`. -/
@[dlmf 24.14.E12]
theorem det_hankel_eulerNumber (n : ℕ) :
    (Matrix.of fun r s : Fin (n + 1) => eulerNumber (r + s : ℕ)).det =
      (-1) ^ (n * (n + 1) / 2) * (∏ k ∈ Finset.Icc 1 n, (k ! : ℚ)) ^ 2 := by
  sorry

end DLMF.BernoulliEuler
