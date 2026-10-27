/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.Basic
public import DLMFMathlib.NumberTheory.EulerNumbers
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.Injectivity
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# Asymptotic approximations of Bernoulli and Euler numbers and polynomials (DLMF §24.11)

DLMF's `Bₙ`, `Bₙ(x)`, `Eₙ`, `Eₙ(x)` are Mathlib's `bernoulli` (with `B₁ = -1/2`),
`Polynomial.bernoulli`, and the project's `eulerNumber`, `Polynomial.euler`
(`DLMFMathlib.NumberTheory.EulerPolynomials`); at complex arguments they are
`bernoulliPolyB n x` and `eulerPolyE n x` (`DLMF.BernoulliEuler.Basic`).

* (24.11.1)–(24.11.4): the asymptotic equivalences of `(-1)ⁿ⁺¹ B₂ₙ` and `(-1)ⁿ E₂ₙ`, stated as
  `Asymptotics.IsEquivalent` along `n → ∞` in `ℝ`, all proved: (24.11.1) from
  `ζ(2n) = (-1)ⁿ⁺¹ (2π)²ⁿ B₂ₙ/(2 (2n)!)` and `ζ(x) → 1` as `x → ∞` (`LSeries.tendsto_atTop`),
  (24.11.3) in the same way from Dirichlet's `β(2n+1)`
  (`hasSum_sin_pi_div_two_div_pow_eulerNumber`), and (24.11.2), (24.11.4) from these and
  Stirling's formula.
* (24.11.5), (24.11.6): the normalized polynomials converge to `cos`/`sin` uniformly on compact
  subsets of `ℂ`; DLMF's single limit with a parity case split is stated as two limits, along the
  even and along the odd indices. All proved: with `cᵢ = (2π)ⁱ Bᵢ/i!`,
  `(2π)ⁿ Bₙ(x)/n! = ∑ᵢ cᵢ (2πx)ⁿ⁻ⁱ/(n-i)!`, and `ζ(2k) = 1 + O(4⁻ᵏ)` gives `cᵢ = dᵢ + O(2⁻ⁱ)`
  with `dᵢ` the coefficients that reproduce `±2 cos`/`±2 sin` exactly; the Euler limits follow
  from `Eₙ(x) = 2ⁿ⁺¹ (Bₙ₊₁(x/2 + 1/2) - Bₙ₊₁(x/2))/(n+1)`. DLMF's sign exponent
  `⌊n/2⌋ - 1` is an integer (it is `-1` for `n ∈ {0, 1}`), so it is taken in `ℤ` with `zpow`.

## References

* NIST DLMF §24.11; Leeming (1977), Dilcher (1987a).
-/

@[expose] public noncomputable section

open Filter Asymptotics Topology Polynomial
open scoped Nat Real

namespace DLMF.BernoulliEuler

/-- DLMF 24.11.1: `(-1)ⁿ⁺¹ B₂ₙ ∼ 2 (2n)!/(2π)²ⁿ` as `n → ∞`. -/
@[dlmf 24.11.E1]
theorem bernoulli_two_mul_isEquivalent :
    (fun n : ℕ => (-1 : ℝ) ^ (n + 1) * (bernoulli (2 * n) : ℝ)) ~[atTop]
      fun n => 2 * ((2 * n)! : ℝ) / (2 * π) ^ (2 * n) := by
  have hL : Tendsto (fun x : ℝ => LSeries 1 x) atTop (𝓝 1) := by
    have := LSeries.tendsto_atTop (f := 1)
      (by rw [LSeries.abscissaOfAbsConv_one]; exact EReal.coe_lt_top 1)
    simpa using this
  have h2 : Tendsto (fun n : ℕ => (2 * n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop two_pos
  have hc := (Complex.continuous_re.tendsto _).comp (hL.comp h2)
  apply isEquivalent_of_tendsto_one
  refine (hc.congr' ?_)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : n ≠ 0 := by omega
  simp only [Function.comp_apply, Pi.div_apply]
  rw [show (((2 * n : ℝ)) : ℂ) = 2 * (n : ℂ) by push_cast; ring,
    LSeries_one_eq_riemannZeta (by simp; linarith [(Nat.one_le_cast (α := ℝ)).mpr hn]),
    riemannZeta_two_mul_nat hn0]
  have hpi : 0 < π := Real.pi_pos
  have e2 : (2 : ℂ) ^ (2 * n - 1) = 2 ^ (2 * n) / 2 := by
    rw [eq_div_iff two_ne_zero, ← pow_succ, Nat.sub_add_cancel (by omega)]
  rw [e2]
  have : ((-1 : ℂ) ^ (n + 1) * (2 ^ (2 * n) / 2) * (π : ℂ) ^ (2 * n) * (bernoulli (2 * n) : ℂ)
      / ((2 * n)! : ℂ)) = (((-1 : ℝ) ^ (n + 1) * (2 ^ (2 * n) / 2) * π ^ (2 * n) *
        (bernoulli (2 * n) : ℝ) / ((2 * n)! : ℝ) : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.ofReal_re]
  have hf : ((2 * n)! : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- DLMF 24.11.2: `(-1)ⁿ⁺¹ B₂ₙ ∼ 4 √(πn) (n/(πe))²ⁿ` as `n → ∞`. -/
@[dlmf 24.11.E2]
theorem bernoulli_two_mul_isEquivalent_stirling :
    (fun n : ℕ => (-1 : ℝ) ^ (n + 1) * (bernoulli (2 * n) : ℝ)) ~[atTop]
      fun n => 4 * Real.sqrt (π * n) * (n / (π * Real.exp 1)) ^ (2 * n) := by
  refine bernoulli_two_mul_isEquivalent.trans ?_
  have h2 : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩
  have hs := (Stirling.factorial_isEquivalent_stirling.comp_tendsto h2)
  have := ((IsEquivalent.refl (u := fun _ : ℕ => (2 : ℝ))).mul hs).div
    (IsEquivalent.refl (u := fun n : ℕ => (2 * π) ^ (2 * n)))
  refine (this.congr_left (Eventually.of_forall fun n => ?_)).congr_right
    (Eventually.of_forall fun n => ?_)
  · simp only [Pi.div_apply, Pi.mul_apply, Function.comp_apply]
  simp only [Pi.div_apply, Pi.mul_apply, Function.comp_apply]
  have hpi : 0 < π := Real.pi_pos
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  rw [show (2 : ℝ) * ((2 * n : ℕ) : ℝ) * π = 2 ^ 2 * (π * n) by push_cast; ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  rw [div_eq_iff (by positivity), show ((2 * n : ℕ) : ℝ) / Real.exp 1 =
    (n : ℝ) / (π * Real.exp 1) * (2 * π) by push_cast; field_simp, mul_pow]
  ring

/-- DLMF 24.11.3: `(-1)ⁿ E₂ₙ ∼ 2²ⁿ⁺² (2n)!/π²ⁿ⁺¹` as `n → ∞`. -/
@[dlmf 24.11.E3]
theorem eulerNumber_two_mul_isEquivalent :
    (fun n : ℕ => (-1 : ℝ) ^ n * (eulerNumber (2 * n) : ℝ)) ~[atTop]
      fun n => (2 : ℝ) ^ (2 * n + 2) * ((2 * n)! : ℝ) / π ^ (2 * n + 1) := by
  set f : ℕ → ℂ := fun n => (Real.sin (π * n / 2) : ℂ) with hf
  have hL : Tendsto (fun x : ℝ => LSeries f x) atTop (𝓝 1) := by
    have := LSeries.tendsto_atTop (f := f)
      ((LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun n _ => by
        rw [hf, Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_sin_le_one _⟩).trans_lt
          (EReal.coe_lt_top 1))
    simpa [hf] using this
  have h2 : Tendsto (fun n : ℕ => ((2 * n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩)
  have hc := (Complex.continuous_re.tendsto _).comp (hL.comp h2)
  apply isEquivalent_of_tendsto_one
  refine (hc.congr' ?_)
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk0 : k ≠ 0 := by omega
  have hs := Polynomial.hasSum_sin_pi_div_two_div_pow_eulerNumber hk0
  have hL2 : LSeries f (((2 * k + 1 : ℕ) : ℝ) : ℂ) =
      (((-1) ^ k * (eulerNumber (2 * k) : ℝ) * π ^ (2 * k + 1) /
        (4 ^ (k + 1) * (2 * k)!) : ℝ) : ℂ) := by
    rw [LSeries]
    refine (HasSum.tsum_eq ?_)
    refine (Complex.hasSum_ofReal.mpr hs).congr_fun fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, hf]
      push_cast
      rw [show ((2 * (k : ℂ) + 1)) = ((2 * k + 1 : ℕ) : ℂ) by push_cast; ring, Complex.cpow_natCast]
      ring
  simp only [Function.comp_apply, Pi.div_apply]
  rw [hL2, Complex.ofReal_re]
  have hpi : 0 < π := Real.pi_pos
  rw [show (4 : ℝ) ^ (k + 1) = 2 ^ (2 * k + 2) by
    rw [show 2 * k + 2 = 2 * (k + 1) by ring, pow_mul]; norm_num]
  have hf' : ((2 * k)! : ℝ) ≠ 0 := by positivity
  field_simp

/-- DLMF 24.11.4: `(-1)ⁿ E₂ₙ ∼ 8 √(n/π) (4n/(πe))²ⁿ` as `n → ∞`. -/
@[dlmf 24.11.E4]
theorem eulerNumber_two_mul_isEquivalent_stirling :
    (fun n : ℕ => (-1 : ℝ) ^ n * (eulerNumber (2 * n) : ℝ)) ~[atTop]
      fun n => 8 * Real.sqrt (n / π) * (4 * n / (π * Real.exp 1)) ^ (2 * n) := by
  refine eulerNumber_two_mul_isEquivalent.trans ?_
  have h2 : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩
  have hs := (Stirling.factorial_isEquivalent_stirling.comp_tendsto h2)
  have := ((IsEquivalent.refl (u := fun n : ℕ => (2 : ℝ) ^ (2 * n + 2))).mul hs).div
    (IsEquivalent.refl (u := fun n : ℕ => π ^ (2 * n + 1)))
  refine (this.congr_left (Eventually.of_forall fun n => ?_)).congr_right
    (Eventually.of_forall fun n => ?_)
  · simp only [Pi.div_apply, Pi.mul_apply, Function.comp_apply]
  simp only [Pi.div_apply, Pi.mul_apply, Function.comp_apply]
  have hpi : 0 < π := Real.pi_pos
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hsq : Real.sqrt (2 * ((2 * n : ℕ) : ℝ) * π) = 2 * (Real.sqrt (n / π) * π) := by
    rw [show (2 : ℝ) * ((2 * n : ℕ) : ℝ) * π = 2 ^ 2 * (n / π) * π ^ 2 by push_cast; field_simp,
      Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num),
      Real.sqrt_sq hpi.le]
    ring
  rw [hsq, div_eq_iff (by positivity), show ((2 * n : ℕ) : ℝ) / Real.exp 1 =
    4 * (n : ℝ) / (π * Real.exp 1) * (π / 2) by push_cast; field_simp; ring, mul_pow,
    div_pow, pow_succ π (2 * n)]
  rw [show (2 : ℝ) ^ (2 * n + 2) = 2 ^ (2 * n) * 4 by rw [pow_add]; norm_num]
  have h12 : ((1 : ℝ) / 2) ^ (2 * n) * 2 ^ (2 * n) = 1 := by rw [← mul_pow]; norm_num
  field_simp
  linear_combination (π ^ (2 * n) * Real.sqrt (n / π) * 8) * h12

/-! ### Helpers for 24.11.5–24.11.6

With `cᵢ = (2π)ⁱ Bᵢ/i!`, `(2π)ⁿ Bₙ(x)/n! = ∑ᵢ cᵢ (2πx)ⁿ⁻ⁱ/(n-i)!`; by `ζ(2k) = 1 + O(4⁻ᵏ)`,
`|cᵢ - dᵢ| ≤ 32 · 2⁻ⁱ` where `dᵢ` are the coefficients that produce `cos`/`sin` exactly. -/

section R24bUniform

open Finset

/-- `cᵢ = (2π)ⁱ Bᵢ/i!`. -/
noncomputable def r24b_c (i : ℕ) : ℝ := (2 * π) ^ i * (_root_.bernoulli i : ℝ) / i !

/-- The limiting values of `cᵢ`: `2 (-1)^{i/2+1}` for even `i`, `0` for odd `i`. -/
def r24b_d (i : ℕ) : ℝ := if i % 2 = 0 then 2 * (-1) ^ (i / 2 + 1) else 0

/-- The Taylor coefficients of `cos` (`p = 0`) and `sin` (`p = 1`). -/
def r24b_a (p j : ℕ) : ℝ := if j % 2 = p then (-1) ^ (j / 2) else 0

/-- `|c₂ₖ - d₂ₖ| = 2 (ζ(2k) - 1) ≤ 32 · 4⁻ᵏ` for `k ≥ 1`. -/
lemma r24b_zeta_bound {k : ℕ} (hk : 1 ≤ k) :
    |r24b_c (2 * k) - r24b_d (2 * k)| ≤ 32 / 2 ^ (2 * k) := by
  have hZ := hasSum_zeta_nat (show k ≠ 0 by omega)
  set Z := (-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * k - 1) * π ^ (2 * k) *
    _root_.bernoulli (2 * k) / (2 * k)!
  have hc : r24b_c (2 * k) = 2 * (-1) ^ (k + 1) * Z := by
    have h2 : (2 : ℝ) ^ (2 * k) = 2 * 2 ^ (2 * k - 1) := by
      rw [← pow_succ']; congr 1; omega
    simp only [r24b_c, Z, mul_pow, h2]
    have : ((2 * k)! : ℝ) ≠ 0 := by positivity
    field_simp
    have h1 : ((-1 : ℝ) ^ (k + 1)) ^ 2 = 1 := by rw [← pow_mul, pow_mul']; norm_num
    rw [h1, mul_one]
  have hd : r24b_d (2 * k) = 2 * (-1) ^ (k + 1) := by
    simp [r24b_d]
  set g : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ (2 * k) - if n = 1 then 1 else 0
  have hg : HasSum g (Z - 1) := hZ.sub (hasSum_ite_eq 1 1)
  have hg0 : ∀ n, 0 ≤ g n := by
    intro n
    simp only [g]
    split_ifs with h
    · subst h; simp
    · simp only [sub_zero]; positivity
  have hgle : ∀ n, g n ≤ 4 / 4 ^ k * (1 / (n : ℝ) ^ 2) := by
    intro n
    simp only [g]
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · simp [zero_pow (show 2 * k ≠ 0 by omega)]
      · simp; positivity
    · have hn1 : ¬ n = 1 := by omega
      simp only [hn1, ↓reduceIte, sub_zero]
      have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have h4 : (4 : ℝ) ^ (k - 1) ≤ (n : ℝ) ^ (2 * k - 2) := by
        rw [show 2 * k - 2 = 2 * (k - 1) by omega, pow_mul]
        exact pow_le_pow_left₀ (by norm_num) (by nlinarith) _
      have hsplit : (n : ℝ) ^ (2 * k) = n ^ 2 * n ^ (2 * k - 2) := by
        rw [← pow_add]; congr 1; omega
      have h44 : (4 : ℝ) ^ k = 4 * 4 ^ (k - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [hsplit, h44]
      have : (0 : ℝ) < n := by linarith
      rw [div_le_iff₀ (by positivity)]
      field_simp
      exact h4
  have hup : Z - 1 ≤ 4 / 4 ^ k * (π ^ 2 / 6) := hasSum_le hgle hg (hasSum_zeta_two.mul_left _)
  have hlo : 0 ≤ Z - 1 := hasSum_le hg0 hasSum_zero hg
  rw [hc, hd, show 2 * (-1 : ℝ) ^ (k + 1) * Z - 2 * (-1) ^ (k + 1) = 2 * (-1) ^ (k + 1) * (Z - 1) by
    ring, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one,
    abs_two, abs_of_nonneg hlo]
  have hpi : π ^ 2 ≤ 16 := by nlinarith [Real.pi_le_four, Real.pi_pos]
  rw [pow_mul]; norm_num
  calc 2 * (Z - 1) ≤ 2 * (4 / 4 ^ k * (π ^ 2 / 6)) := by linarith
    _ ≤ 32 / 4 ^ k := by
      rw [show 2 * (4 / 4 ^ k * (π ^ 2 / 6)) = (8 * π ^ 2 / 6) / 4 ^ k by ring]
      gcongr; nlinarith

/-- `|cᵢ - dᵢ| ≤ 32 · 2⁻ⁱ` for all `i`. -/
lemma r24b_c_sub_d (i : ℕ) : |r24b_c i - r24b_d i| ≤ 32 / 2 ^ i := by
  rcases Nat.even_or_odd' i with ⟨k, rfl | rfl⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [r24b_c, r24b_d]; norm_num
    · exact r24b_zeta_bound hk
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [r24b_c, r24b_d]
      rw [abs_of_neg (by norm_num : (-1 / 2 : ℝ) < 0)]; linarith [Real.pi_le_four]
    · have hB : _root_.bernoulli (2 * k + 1) = 0 :=
        bernoulli_eq_zero_of_odd (odd_two_mul_add_one k) (by omega)
      have : (2 * k + 1) % 2 = 1 := by omega
      simp [r24b_c, r24b_d, hB, this]
      positivity

/-- For `n = 2m + p` (`p < 2`), `dᵢ = 2 (-1)^{m+1} a_p(n - i)`. -/
lemma r24b_d_eq {p : ℕ} (hp : p < 2) (m i : ℕ) (hi : i ≤ 2 * m + p) :
    r24b_d i = 2 * (-1) ^ (m + 1) * r24b_a p (2 * m + p - i) := by
  rcases Nat.even_or_odd' i with ⟨k, rfl | rfl⟩ <;> interval_cases p
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show k ≤ m by omega)
    have e : 2 * (k + j) + 0 - 2 * k = 2 * j := by omega
    have hj : ((-1 : ℝ) ^ j) * (-1) ^ j = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
    rw [e]; simp [r24b_d, r24b_a, pow_add]
    linear_combination (-2 * (-1 : ℝ) ^ k) * hj
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show k ≤ m by omega)
    have e : 2 * (k + j) + 1 - 2 * k = 2 * j + 1 := by omega
    rw [e]
    have h1 : (2 * j + 1) % 2 = 1 := by omega
    have h2 : (2 * j + 1) / 2 = j := by omega
    have hj : ((-1 : ℝ) ^ j) * (-1) ^ j = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
    simp [r24b_d, r24b_a, h1, h2, pow_add]
    linear_combination (-2 * (-1 : ℝ) ^ k) * hj
  · have h2 : (2 * k + 1) % 2 = 1 := by omega
    simp [r24b_d, r24b_a, h2]; omega
  · have h2 : (2 * k + 1) % 2 = 1 := by omega
    simp [r24b_d, r24b_a, h2]; omega

/-- `cos y = ∑ⱼ a₀(j) yʲ/j!`. -/
lemma r24b_hasSum_a_cos (y : ℂ) :
    HasSum (fun j => (r24b_a 0 j : ℂ) * y ^ j / j !) (Complex.cos y) := by
  rw [← (show Function.Injective (fun l : ℕ => 2 * l) from
    fun a b h => by simpa using h).hasSum_iff]
  · refine (Complex.hasSum_cos y).congr_fun fun l => ?_
    simp [r24b_a]
  · intro j hj
    have : j % 2 ≠ 0 := fun h => hj ⟨j / 2, by simp; omega⟩
    simp [r24b_a, this]

/-- `sin y = ∑ⱼ a₁(j) yʲ/j!`. -/
lemma r24b_hasSum_a_sin (y : ℂ) :
    HasSum (fun j => (r24b_a 1 j : ℂ) * y ^ j / j !) (Complex.sin y) := by
  rw [← (show Function.Injective (fun l : ℕ => 2 * l + 1) from
    fun a b h => by simpa using h).hasSum_iff]
  · refine (Complex.hasSum_sin y).congr_fun fun l => ?_
    have h1 : (2 * l + 1) % 2 = 1 := by omega
    have h2 : (2 * l + 1) / 2 = l := by omega
    simp [r24b_a, h1, h2]
  · intro j hj
    have : j % 2 ≠ 1 := fun h => hj ⟨j / 2, by simp; omega⟩
    simp [r24b_a, this]

/-- `(2π)ⁿ Bₙ(x)/n! = ∑ᵢ cᵢ (2πx)ⁿ⁻ⁱ/(n-i)!`. -/
lemma r24b_bernoulli_expand (n : ℕ) (x : ℂ) :
    (2 * π : ℂ) ^ n / n ! * bernoulliPolyB n x =
      ∑ i ∈ range (n + 1), (r24b_c i : ℂ) * (2 * π * x) ^ (n - i) / (n - i)! := by
  rw [bernoulliPolyB, Polynomial.bernoulli, map_sum, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rw [aeval_monomial, Nat.cast_choose ℚ hin, r24b_c]
  have h1 : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : (i ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : ((n - i)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hp : (2 * π : ℂ) ^ n = (2 * π) ^ i * (2 * π) ^ (n - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hin]
  simp only [map_mul, map_div₀, eq_ratCast, Rat.cast_natCast]
  push_cast
  rw [hp]
  field_simp
  ring

/-- The `cos`/`sin` coefficients are bounded by `1`. -/
lemma r24b_abs_a_le (p j : ℕ) : |r24b_a p j| ≤ 1 := by
  unfold r24b_a; split_ifs <;> simp

/-- The exponential series of a real number. -/
lemma r24b_hasSum_exp_real (R : ℝ) : HasSum (fun j => R ^ j / j !) (Real.exp R) := by
  rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp R

/-- The core estimate for 24.11.5: the normalized `Bₙ(x)`, `n = 2m + p`, differs from `cos`/`sin`
by at most `16 · 2⁻ⁿ e^{2R} + (e^R - ∑_{j ≤ n} Rʲ/j!)` when `‖2πx‖ ≤ R`. -/
lemma r24b_core {p : ℕ} (hp : p < 2) (m n : ℕ) (hn : n = 2 * m + p) (x : ℂ) {r : ℝ}
    (hx : ‖x‖ ≤ r) {G : ℂ}
    (hG : HasSum (fun j => (r24b_a p j : ℂ) * (2 * π * x) ^ j / j !) G) :
    ‖(-1 : ℂ) ^ ((m : ℤ) - 1) * (2 * π) ^ n / (2 * n !) * bernoulliPolyB n x - G‖ ≤
      16 / 2 ^ n * Real.exp (2 * (2 * π * r)) +
        (Real.exp (2 * π * r) - ∑ j ∈ range (n + 1), (2 * π * r) ^ j / j !) := by
  set y : ℂ := 2 * π * x
  set R : ℝ := 2 * π * r
  have hpi : 0 < π := Real.pi_pos
  have hyR : ‖y‖ ≤ R := by
    simp only [y, R, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpi]
    gcongr
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hyR
  set s : ℂ := (-1 : ℂ) ^ ((m : ℤ) - 1)
  have hs : s * (-1 : ℂ) ^ (m + 1) = 1 := by
    simp only [s]
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
    push_cast
    rw [show (m : ℤ) - 1 + (m + 1) = 2 * m by ring, zpow_mul]; norm_num
  have hsn : ‖s‖ = 1 := by simp [s]
  set P : ℂ := ∑ j ∈ range (n + 1), (r24b_a p j : ℂ) * y ^ j / (j ! : ℂ)
  have hW : ∑ i ∈ range (n + 1), (r24b_d i : ℂ) * y ^ (n - i) / (n - i)! =
      2 * (-1) ^ (m + 1) * P := by
    rw [mul_sum, ← sum_range_reflect]
    refine sum_congr rfl fun i hi => ?_
    have hin : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [show n + 1 - 1 - i = n - i by omega, show n - (n - i) = i by omega,
      r24b_d_eq hp m (n - i) (by omega),
      show 2 * m + p - (n - i) = i by omega]
    push_cast; ring
  have hsplit : s * (2 * π) ^ n / (2 * n !) * bernoulliPolyB n x - G =
      s / 2 * ∑ i ∈ range (n + 1), ((r24b_c i - r24b_d i : ℝ) : ℂ) * y ^ (n - i) / (n - i)! +
        (P - G) := by
    have hE := r24b_bernoulli_expand n x
    have hcd : ∑ i ∈ range (n + 1), ((r24b_c i - r24b_d i : ℝ) : ℂ) * y ^ (n - i) / (n - i)! =
        ∑ i ∈ range (n + 1), (r24b_c i : ℂ) * y ^ (n - i) / (n - i)! -
          ∑ i ∈ range (n + 1), (r24b_d i : ℂ) * y ^ (n - i) / (n - i)! := by
      rw [← sum_sub_distrib]; refine sum_congr rfl fun i _ => ?_; push_cast; ring
    rw [hcd, hW, ← hE]
    have : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
    linear_combination (2 * P * n !) * hs
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, norm_div, hsn, Complex.norm_ofNat]
    calc 1 / 2 * ‖∑ i ∈ range (n + 1), ((r24b_c i - r24b_d i : ℝ) : ℂ) * y ^ (n - i) / (n - i)!‖
        ≤ 1 / 2 * ∑ i ∈ range (n + 1), 32 / 2 ^ i * (R ^ (n - i) / (n - i)!) := by
          gcongr
          refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
          rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
            Complex.norm_natCast, mul_div_assoc]
          gcongr
          exact r24b_c_sub_d i
      _ = 16 / 2 ^ n * ∑ j ∈ range (n + 1), (2 * R) ^ j / j ! := by
          rw [← sum_range_reflect, mul_sum, mul_sum]
          refine sum_congr rfl fun i hi => ?_
          have hin : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
          rw [show n + 1 - 1 - i = n - i by omega, show n - (n - i) = i by omega, mul_pow]
          have h2 : (2 : ℝ) ^ n = 2 ^ (n - i) * 2 ^ i := by rw [← pow_add, Nat.sub_add_cancel hin]
          rw [h2]
          simp only [R, mul_pow]
          field_simp
          ring
      _ ≤ 16 / 2 ^ n * Real.exp (2 * R) := by
          gcongr
          exact Real.sum_le_exp_of_nonneg (by positivity) _
  · rw [norm_sub_rev]
    have hG' := (hasSum_nat_add_iff' (n + 1)).mpr hG
    have hR' := (hasSum_nat_add_iff' (n + 1)).mpr (r24b_hasSum_exp_real R)
    refine hG'.norm_le_of_bounded hR' fun j => ?_
    rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
    have := r24b_abs_a_le p (j + (n + 1))
    calc |r24b_a p (j + (n + 1))| * ‖y‖ ^ (j + (n + 1)) / ((j + (n + 1))! : ℝ)
        ≤ 1 * R ^ (j + (n + 1)) / ((j + (n + 1))! : ℝ) := by gcongr
      _ = _ := by rw [one_mul]

/-- The error bound of `r24b_core` for `‖x‖ ≤ r`. -/
noncomputable def r24b_err (p m : ℕ) (r : ℝ) : ℝ :=
  16 / 2 ^ (2 * m + p) * Real.exp (2 * (2 * π * r)) +
    (Real.exp (2 * π * r) - ∑ j ∈ range (2 * m + p + 1), (2 * π * r) ^ j / j !)

/-- The error bound tends to `0`. -/
lemma r24b_err_tendsto (p : ℕ) (r : ℝ) : Tendsto (fun m => r24b_err p m r) atTop (𝓝 0) := by
  have hn : Tendsto (fun m : ℕ => 2 * m + p) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩
  have h1 : Tendsto (fun m : ℕ => 16 / 2 ^ (2 * m + p) * Real.exp (2 * (2 * π * r))) atTop
      (𝓝 0) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).comp hn).const_mul 16 |>.mul_const (Real.exp (2 * (2 * π * r)))
    rw [mul_zero, zero_mul] at h
    refine h.congr fun m => ?_
    simp [div_eq_mul_inv]
  have h2 : Tendsto (fun m : ℕ => Real.exp (2 * π * r) -
      ∑ j ∈ range (2 * m + p + 1), (2 * π * r) ^ j / j !) atTop
      (𝓝 (Real.exp (2 * π * r) - Real.exp (2 * π * r))) :=
    tendsto_const_nhds.sub ((r24b_hasSum_exp_real _).tendsto_sum_nat.comp
      (tendsto_add_atTop_nat 1 |>.comp hn))
  simpa [r24b_err] using h1.add h2

/-- Uniform convergence from a uniform error bound tending to `0`. -/
lemma r24b_tendstoUniformlyOn_of_le {F : ℕ → ℂ → ℂ} {G : ℂ → ℂ} {K : Set ℂ} (e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0)) (h : ∀ m x, x ∈ K → ‖F m x - G x‖ ≤ e m) :
    TendstoUniformlyOn F G atTop K := by
  refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_
  filter_upwards [he.eventually (gt_mem_nhds hε)] with m hm x hx
  rw [dist_eq_norm, norm_sub_rev]
  exact (h m x hx).trans_lt hm

/-- The error bound for the even Bernoulli limit (24.11.5). -/
lemma r24b_bernoulli_even_bound (m : ℕ) (x : ℂ) {r : ℝ} (hx : ‖x‖ ≤ r) :
    ‖(-1 : ℂ) ^ ((m : ℤ) - 1) * (2 * π) ^ (2 * m) / (2 * (2 * m)!) * bernoulliPolyB (2 * m) x -
      Complex.cos (2 * π * x)‖ ≤ r24b_err 0 m r :=
  r24b_core (p := 0) (by norm_num) m (2 * m) (by ring) x hx (r24b_hasSum_a_cos _)

/-- The error bound for the odd Bernoulli limit (24.11.5). -/
lemma r24b_bernoulli_odd_bound (m : ℕ) (x : ℂ) {r : ℝ} (hx : ‖x‖ ≤ r) :
    ‖(-1 : ℂ) ^ ((m : ℤ) - 1) * (2 * π) ^ (2 * m + 1) / (2 * (2 * m + 1)!) *
        bernoulliPolyB (2 * m + 1) x - Complex.sin (2 * π * x)‖ ≤ r24b_err 1 m r :=
  r24b_core (p := 1) (by norm_num) m (2 * m + 1) rfl x hx (r24b_hasSum_a_sin _)

/-- `Eₙ(x) = 2^{n+1} (B_{n+1}(x/2 + 1/2) - B_{n+1}(x/2))/(n+1)` at complex `x`. -/
lemma r24b_eulerPolyE_eq (n : ℕ) (x : ℂ) :
    eulerPolyE n x = 2 ^ (n + 1) * (bernoulliPolyB (n + 1) (x / 2 + 1 / 2) -
      bernoulliPolyB (n + 1) (x / 2)) / (n + 1) := by
  have he := congrArg (aeval x) (euler_eq_bernoulli n)
  simp only [map_mul, map_add, map_natCast, map_one, aeval_C, aeval_comp, aeval_X, map_sub,
    eq_ratCast] at he
  change ((n : ℂ) + 1) * eulerPolyE n x = _ at he
  have ha : ((1 / 2 : ℚ) : ℂ) * x + ((1 / 2 : ℚ) : ℂ) = x / 2 + 1 / 2 := by push_cast; ring
  have hb : ((1 / 2 : ℚ) : ℂ) * x = x / 2 := by push_cast; ring
  rw [ha, hb] at he
  change _ = ((2 ^ (n + 1) : ℚ) : ℂ) * (bernoulliPolyB (n + 1) (x / 2 + 1 / 2) -
    bernoulliPolyB (n + 1) (x / 2)) at he
  have hn : (n : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  rw [eq_div_iff hn]; push_cast at he; linear_combination he

/-- `‖x/2‖, ‖x/2 + 1/2‖ ≤ r + 1` when `‖x‖ ≤ r`. -/
lemma r24b_norm_half_le {x : ℂ} {r : ℝ} (hx : ‖x‖ ≤ r) :
    ‖x / 2‖ ≤ r + 1 ∧ ‖x / 2 + 1 / 2‖ ≤ r + 1 := by
  have h0 : 0 ≤ r := (norm_nonneg _).trans hx
  have h1 : ‖x / 2‖ ≤ r / 2 := by rw [norm_div, Complex.norm_ofNat]; linarith
  refine ⟨by linarith, (norm_add_le _ _).trans ?_⟩
  have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by rw [norm_div, norm_one, Complex.norm_ofNat]
  linarith

end R24bUniform

/-- DLMF 24.11.5, even `n = 2m`: `(-1)^{m-1} (2π)^{2m}/(2 (2m)!) B₂ₘ(x) → cos(2πx)` uniformly
on every compact subset of `ℂ`. -/
@[dlmf 24.11.E5]
theorem tendstoUniformlyOn_bernoulli_even {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun (m : ℕ) (x : ℂ) => (-1 : ℂ) ^ ((m : ℤ) - 1) * (2 * π) ^ (2 * m) / (2 * (2 * m)!) *
        bernoulliPolyB (2 * m) x)
      (fun x => Complex.cos (2 * π * x)) atTop K := by
  obtain ⟨r, hr⟩ := hK.isBounded.exists_norm_le
  exact r24b_tendstoUniformlyOn_of_le _ (r24b_err_tendsto 0 r) fun m x hx =>
    r24b_bernoulli_even_bound m x (hr x hx)

/-- DLMF 24.11.5, odd `n = 2m + 1` (so `⌊n/2⌋ - 1 = m - 1`):
`(-1)^{m-1} (2π)^{2m+1}/(2 (2m+1)!) B₂ₘ₊₁(x) → sin(2πx)` uniformly on every compact subset
of `ℂ`. -/
@[dlmf 24.11.E5]
theorem tendstoUniformlyOn_bernoulli_odd {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun (m : ℕ) (x : ℂ) => (-1 : ℂ) ^ ((m : ℤ) - 1) * (2 * π) ^ (2 * m + 1) /
        (2 * (2 * m + 1)!) * bernoulliPolyB (2 * m + 1) x)
      (fun x => Complex.sin (2 * π * x)) atTop K := by
  obtain ⟨r, hr⟩ := hK.isBounded.exists_norm_le
  exact r24b_tendstoUniformlyOn_of_le _ (r24b_err_tendsto 1 r) fun m x hx =>
    r24b_bernoulli_odd_bound m x (hr x hx)

/-- DLMF 24.11.6, even `n = 2m` (so `⌊(n+1)/2⌋ = m`):
`(-1)^m π^{2m+1}/(4 (2m)!) E₂ₘ(x) → sin(πx)` uniformly on every compact subset of `ℂ`. -/
@[dlmf 24.11.E6]
theorem tendstoUniformlyOn_euler_even {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun (m : ℕ) (x : ℂ) => (-1 : ℂ) ^ m * (π : ℂ) ^ (2 * m + 1) / (4 * (2 * m)!) *
        eulerPolyE (2 * m) x)
      (fun x => Complex.sin (π * x)) atTop K := by
  obtain ⟨r, hr⟩ := hK.isBounded.exists_norm_le
  refine r24b_tendstoUniformlyOn_of_le _ (r24b_err_tendsto 1 (r + 1)) fun m x hx => ?_
  obtain ⟨h1, h2⟩ := r24b_norm_half_le (hr x hx)
  have b1 := r24b_bernoulli_odd_bound m _ h2
  have b2 := r24b_bernoulli_odd_bound m _ h1
  set O : ℂ → ℂ := fun z => (-1 : ℂ) ^ ((m : ℤ) - 1) * (2 * π) ^ (2 * m + 1) /
    (2 * (2 * m + 1)!) * bernoulliPolyB (2 * m + 1) z
  have hs : (-1 : ℂ) ^ ((m : ℤ) - 1) = -(-1) ^ m := by
    rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_one]; ring
  have hF : (-1 : ℂ) ^ m * (π : ℂ) ^ (2 * m + 1) / (4 * (2 * m)!) * eulerPolyE (2 * m) x -
      Complex.sin (π * x) =
        -(1 / 2) * ((O (x / 2 + 1 / 2) - Complex.sin (2 * π * (x / 2 + 1 / 2))) -
        (O (x / 2) - Complex.sin (2 * π * (x / 2)))) := by
    rw [r24b_eulerPolyE_eq, show 2 * π * (x / 2 + 1 / 2) = π * x + π by ring,
      show (2 : ℂ) * π * (x / 2) = π * x by ring, Complex.sin_add_pi]
    simp only [O, hs]
    have hf : (((2 * m + 1)! : ℕ) : ℂ) = (2 * m + 1) * (2 * m)! := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hf]
    have : ((2 * m)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h2m : (2 * (m : ℂ) + 1) ≠ 0 := by exact_mod_cast (show 2 * m + 1 ≠ 0 by omega)
    push_cast
    field_simp
    ring
  rw [hF, norm_mul, norm_neg, norm_div, norm_one, Complex.norm_ofNat]
  calc 1 / 2 * ‖(O (x / 2 + 1 / 2) - Complex.sin (2 * π * (x / 2 + 1 / 2))) -
        (O (x / 2) - Complex.sin (2 * π * (x / 2)))‖ ≤ 1 / 2 * (r24b_err 1 m (r + 1) +
          r24b_err 1 m (r + 1)) := by
        gcongr; exact (norm_sub_le _ _).trans (add_le_add b1 b2)
    _ = r24b_err 1 m (r + 1) := by ring

/-- DLMF 24.11.6, odd `n = 2m + 1` (so `⌊(n+1)/2⌋ = m + 1`):
`(-1)^{m+1} π^{2m+2}/(4 (2m+1)!) E₂ₘ₊₁(x) → cos(πx)` uniformly on every compact subset
of `ℂ`. -/
@[dlmf 24.11.E6]
theorem tendstoUniformlyOn_euler_odd {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun (m : ℕ) (x : ℂ) => (-1 : ℂ) ^ (m + 1) * (π : ℂ) ^ (2 * m + 2) / (4 * (2 * m + 1)!) *
        eulerPolyE (2 * m + 1) x)
      (fun x => Complex.cos (π * x)) atTop K := by
  obtain ⟨r, hr⟩ := hK.isBounded.exists_norm_le
  refine r24b_tendstoUniformlyOn_of_le _ ((r24b_err_tendsto 0 (r + 1)).comp
    (tendsto_add_atTop_nat 1)) fun m x hx => ?_
  obtain ⟨h1, h2⟩ := r24b_norm_half_le (hr x hx)
  have b1 := r24b_bernoulli_even_bound (m + 1) _ h2
  have b2 := r24b_bernoulli_even_bound (m + 1) _ h1
  set N : ℂ → ℂ := fun z => (-1 : ℂ) ^ (((m + 1 : ℕ) : ℤ) - 1) * (2 * π) ^ (2 * (m + 1)) /
    (2 * (2 * (m + 1))!) * bernoulliPolyB (2 * (m + 1)) z
  have hs : (-1 : ℂ) ^ (((m + 1 : ℕ) : ℤ) - 1) = (-1) ^ m := by
    rw [show ((m + 1 : ℕ) : ℤ) - 1 = m by push_cast; ring, zpow_natCast]
  have hF : (-1 : ℂ) ^ (m + 1) * (π : ℂ) ^ (2 * m + 2) / (4 * (2 * m + 1)!) *
      eulerPolyE (2 * m + 1) x - Complex.cos (π * x) =
      -(1 / 2) * ((N (x / 2 + 1 / 2) - Complex.cos (2 * π * (x / 2 + 1 / 2))) -
        (N (x / 2) - Complex.cos (2 * π * (x / 2)))) := by
    rw [r24b_eulerPolyE_eq, show 2 * π * (x / 2 + 1 / 2) = π * x + π by ring,
      show (2 : ℂ) * π * (x / 2) = π * x by ring, Complex.cos_add_pi]
    simp only [N, hs]
    have hf : (((2 * (m + 1))! : ℕ) : ℂ) = (2 * m + 2) * (2 * m + 1)! := by
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring, Nat.factorial_succ]; push_cast; ring
    rw [hf, show 2 * (m + 1) = 2 * m + 2 by ring, show 2 * m + 1 + 1 = 2 * m + 2 by ring]
    have : ((2 * m + 1)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h2m : (2 * (m : ℂ) + 2) ≠ 0 := by exact_mod_cast (show 2 * m + 2 ≠ 0 by omega)
    have h2m' : (2 * (m : ℂ) + 1 + 1) ≠ 0 := by exact_mod_cast (show 2 * m + 1 + 1 ≠ 0 by omega)
    push_cast
    field_simp
    ring
  rw [hF, norm_mul, norm_neg, norm_div, norm_one, Complex.norm_ofNat]
  calc 1 / 2 * ‖(N (x / 2 + 1 / 2) - Complex.cos (2 * π * (x / 2 + 1 / 2))) -
        (N (x / 2) - Complex.cos (2 * π * (x / 2)))‖ ≤ 1 / 2 * (r24b_err 0 (m + 1) (r + 1) +
          r24b_err 0 (m + 1) (r + 1)) := by
        gcongr; exact (norm_sub_le _ _).trans (add_le_add b1 b2)
    _ = r24b_err 0 (m + 1) (r + 1) := by ring

end DLMF.BernoulliEuler
