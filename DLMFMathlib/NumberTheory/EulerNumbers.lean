/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.NumberTheory.EulerPolynomials
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Euler numbers: Bernoulli relation, generating functions, `β(2k+1)` (Duverney §2.3.2)

* `euler_eq_bernoulli`: `(n+1) Eₙ(x) = 2ⁿ⁺¹ (Bₙ₊₁((x+1)/2) - Bₙ₊₁(x/2))`. Both sides satisfy
  `P(x+1) + P(x) = 2(n+1)xⁿ`, so they agree by `eq_of_comp_X_add_one_add_self_eq`.
* `eulerNumber_two_mul`: `E₂ₖ = -2^{4k+2} B₂ₖ₊₁(1/4)/(2k+1)`.
* `hasSum_sin_pi_div_two_div_pow_eulerNumber`: Dirichlet's
  `β(2k+1) = (-1)ᵏ E₂ₖ π^{2k+1}/(4^{k+1}(2k)!)` for `k ≥ 1`, from Mathlib's Fourier series of
  Bernoulli polynomials at `x = 1/4`.
* `abs_eulerNumber_le`: `|Eₙ| ≤ n! 2ⁿ`, by induction from the recurrence.
* `hasSum_eulerNumber_mul_pow_div`: `sech z = ∑ Eₙ zⁿ/n!` for `‖z‖ < 1/2`, by a Cauchy product with
  the series of `cosh`; `hasSum_eulerNumber_sec`: `sec z = ∑ (-1)ᵏ E₂ₖ z^{2k}/(2k)!`.
-/

@[expose] public section

noncomputable section

open Finset

namespace Polynomial

/-- **Euler polynomials through Bernoulli polynomials** (Duverney, Ex. 2.5):
`(n+1) Eₙ(x) = 2ⁿ⁺¹ (Bₙ₊₁((x+1)/2) - Bₙ₊₁(x/2))`. -/
theorem euler_eq_bernoulli (n : ℕ) :
    ((n : ℚ[X]) + 1) * euler n =
      C ((2 : ℚ) ^ (n + 1)) * ((bernoulli (n + 1)).comp (C (1 / 2) * X + C (1 / 2)) -
        (bernoulli (n + 1)).comp (C (1 / 2) * X)) := by
  apply eq_of_comp_X_add_one_add_self_eq
  set B := bernoulli (n + 1)
  set u : ℚ[X] := C (1 / 2) * X
  have hsh : B.comp (1 + u) = B.comp u + ((n + 1 : ℕ) : ℚ[X]) * u ^ n := by
    have h := congrArg (fun P : ℚ[X] => P.comp u) (bernoulli_comp_one_add_X (n + 1))
    simp only [add_comp, comp_assoc, one_comp, X_comp, nsmul_eq_mul, mul_comp, natCast_comp,
      pow_comp, Nat.add_sub_cancel] at h
    exact h
  have hu1 : u.comp (X + 1) = u + C (1 / 2 : ℚ) := by
    simp only [u, mul_comp, C_comp, X_comp]; rw [mul_add, mul_one]
  have e1 : (u + C (1 / 2 : ℚ)).comp (X + 1) = 1 + u := by
    rw [add_comp, hu1, C_comp]
    rw [show (1 : ℚ[X]) = C (1 / 2) + C (1 / 2) by rw [← C_add]; norm_num]; ring
  rw [mul_comp, add_comp, natCast_comp, one_comp, ← mul_add, euler_comp_X_add_one_add,
    mul_comp, C_comp, sub_comp, comp_assoc, comp_assoc, e1, hu1, hsh]
  simp only [u]
  rw [mul_pow, ← C_pow]
  have h2 : C ((2 : ℚ) ^ (n + 1)) * C ((1 / 2 : ℚ) ^ n) = 2 := by
    rw [← C_mul, show (2 : ℚ) ^ (n + 1) * (1 / 2) ^ n = 2 by
      rw [pow_succ, div_pow, one_pow]; field_simp]; rfl
  push_cast
  linear_combination (-((n : ℚ[X]) + 1) * X ^ n) * h2


/-- Even Euler numbers through Bernoulli polynomials:
`E₂ₖ = -2^{4k+2} B₂ₖ₊₁(1/4)/(2k+1)`. -/
theorem eulerNumber_two_mul (k : ℕ) :
    eulerNumber (2 * k) =
      -(2 ^ (4 * k + 2) / (2 * k + 1)) * (bernoulli (2 * k + 1)).eval (1 / 4) := by
  have h := congrArg (eval (1 / 2 : ℚ)) (euler_eq_bernoulli (2 * k))
  simp only [eval_mul, eval_add, eval_natCast, eval_one, eval_C, eval_sub, eval_comp, eval_X]
    at h
  have hr := bernoulli_eval_one_sub (2 * k + 1) (1 / 4)
  rw [show (1 : ℚ) - 1 / 4 = 1 / 2 * (1 / 2) + 1 / 2 by norm_num,
    (Odd.neg_one_pow (odd_two_mul_add_one k))] at hr
  rw [hr, show (1 / 2 : ℚ) * (1 / 2) = 1 / 4 by norm_num] at h
  rw [eulerNumber]
  have hk : ((2 * k : ℕ) : ℚ) + 1 ≠ 0 := by positivity
  field_simp
  push_cast at h hk ⊢
  linear_combination (2 : ℚ) ^ (2 * k) * h

/-- A crude bound `|Eₙ| ≤ n! 2ⁿ`, enough for convergence of `∑ Eₙ zⁿ/n!` on `‖z‖ < 1/2`. -/
theorem abs_eulerNumber_le (n : ℕ) : |eulerNumber n| ≤ n.factorial * 2 ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simp
    have hrec := sum_choose_mul_eulerNumber (n + 1)
    rw [sum_range_succ, Nat.choose_self, Nat.sub_self, pow_zero, zero_pow (Nat.succ_ne_zero n),
      mul_zero] at hrec
    have hlast : eulerNumber (n + 1) =
        -(∑ k ∈ range (n + 1), ((n + 1).choose k : ℚ) * (1 + (-1) ^ (n + 1 - k)) *
          eulerNumber k) / 2 := by
      push_cast at hrec; linarith
    rw [hlast, abs_div, abs_neg, abs_two]
    have hterm : ∀ k ∈ range (n + 1), |((n + 1).choose k : ℚ) * (1 + (-1) ^ (n + 1 - k)) *
        eulerNumber k| ≤ 2 * ((n + 1).factorial * 2 ^ k) := by
      intro k hk
      have hkn : k < n + 1 := mem_range.mp hk
      have h1 : |(1 + (-1 : ℚ) ^ (n + 1 - k))| ≤ 2 := by
        rcases neg_one_pow_eq_or ℚ (n + 1 - k) with h | h <;> rw [h] <;> norm_num
      have h2 : ((n + 1).choose k : ℚ) * k.factorial ≤ (n + 1).factorial := by
        have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_of_lt hkn)
        have hpos := Nat.factorial_pos (n + 1 - k)
        have : (n + 1).choose k * k.factorial ≤ (n + 1).factorial := by
          rw [← h]; exact Nat.le_mul_of_pos_right _ hpos
        exact_mod_cast this
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ ((n + 1).choose k : ℚ))]
      have h3 := ih k hkn
      calc ((n + 1).choose k : ℚ) * |1 + (-1) ^ (n + 1 - k)| * |eulerNumber k|
          ≤ ((n + 1).choose k : ℚ) * 2 * (k.factorial * 2 ^ k) := by gcongr
        _ = 2 * (((n + 1).choose k : ℚ) * k.factorial) * 2 ^ k := by ring
        _ ≤ 2 * ((n + 1).factorial : ℚ) * 2 ^ k := by gcongr
        _ = 2 * ((n + 1).factorial * 2 ^ k) := by ring
    have hsum := (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
    rw [← mul_sum, ← mul_sum] at hsum
    have hgeom : ∑ k ∈ range (n + 1), (2 : ℚ) ^ k ≤ 2 ^ (n + 1) := by
      rw [geom_sum_eq (by norm_num)]; norm_num
    calc |∑ k ∈ range (n + 1), ((n + 1).choose k : ℚ) * (1 + (-1) ^ (n + 1 - k)) *
          eulerNumber k| / 2 ≤ 2 * ((n + 1).factorial * ∑ k ∈ range (n + 1), (2 : ℚ) ^ k) / 2 := by
          gcongr
      _ ≤ (n + 1).factorial * 2 ^ (n + 1) := by
          have : (0 : ℚ) ≤ (n + 1).factorial := by positivity
          nlinarith

open scoped Nat Real in
/-- **Dirichlet beta at odd integers through Euler numbers** (Duverney (2.87)):
`β(2k+1) = ∑ₙ sin(πn/2)/n^{2k+1} = (-1)ᵏ E₂ₖ π^{2k+1}/(4^{k+1} (2k)!)` for `k ≥ 1`. -/
theorem hasSum_sin_pi_div_two_div_pow_eulerNumber {k : ℕ} (hk : k ≠ 0) :
    HasSum (fun n : ℕ => 1 / (n : ℝ) ^ (2 * k + 1) * Real.sin (π * n / 2))
      ((-1) ^ k * (eulerNumber (2 * k) : ℝ) * π ^ (2 * k + 1) / (4 ^ (k + 1) * (2 * k)!)) := by
  have h := hasSum_one_div_nat_pow_mul_sin hk (x := 1 / 4) ⟨by norm_num, by norm_num⟩
  have hev : (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * k + 1))).eval (1 / 4 : ℝ) =
      (((Polynomial.bernoulli (2 * k + 1)).eval (1 / 4 : ℚ) : ℚ) : ℝ) := by
    have : (1 / 4 : ℝ) = (algebraMap ℚ ℝ) (1 / 4 : ℚ) := by simp
    rw [this, Polynomial.eval_map, Polynomial.eval₂_at_apply]; rfl
  have he := eulerNumber_two_mul k
  have hk1 : ((2 * k : ℕ) : ℚ) + 1 ≠ 0 := by positivity
  have hB : (Polynomial.bernoulli (2 * k + 1)).eval (1 / 4 : ℚ) =
      -(2 * k + 1) * eulerNumber (2 * k) / 2 ^ (4 * k + 2) := by
    rw [he]; field_simp
  rw [hev, hB] at h
  convert h using 1
  · funext n; congr 2; ring
  · push_cast
    rw [Nat.factorial_succ, show (4 : ℝ) ^ (k + 1) = 2 ^ (2 * k + 2) by
      rw [show 2 * k + 2 = 2 * (k + 1) by ring, pow_mul]; norm_num]
    field_simp
    push_cast
    ring

open scoped Nat in
/-- **The secant–hyperbolic generating function** (DLMF 24.2.6, Duverney (2.55)): for
`‖z‖ < 1/2`, `sech z = ∑ₙ Eₙ zⁿ/n!`. (The true radius is `π/2`.) -/
@[dlmf 24.2.E6]
theorem hasSum_eulerNumber_mul_pow_div {z : ℂ} (hz : ‖z‖ < 1 / 2) :
    HasSum (fun n : ℕ => (eulerNumber n : ℂ) * z ^ n / n !) (Complex.cosh z)⁻¹ := by
  set f : ℕ → ℂ := fun n => (eulerNumber n : ℂ) * z ^ n / n ! with hf
  set g : ℕ → ℂ := fun n => (1 + (-1) ^ n) / 2 * z ^ n / n ! with hg
  have h2z : 2 * ‖z‖ < 1 := by linarith
  have hfn : Summable fun n => ‖f n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (summable_geometric_of_lt_one (by positivity) h2z)
    have hb := abs_eulerNumber_le n
    have hb' : ‖(eulerNumber n : ℂ)‖ ≤ n ! * 2 ^ n := by
      rw [Complex.norm_ratCast]; exact_mod_cast hb
    have hfac : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
    simp only [hf, norm_div, norm_mul, norm_pow, Complex.norm_natCast]
    rw [div_le_iff₀ hfac, mul_pow]
    calc ‖(eulerNumber n : ℂ)‖ * ‖z‖ ^ n ≤ n ! * 2 ^ n * ‖z‖ ^ n := by gcongr
      _ = 2 ^ n * ‖z‖ ^ n * n ! := by ring
  have hexp (w : ℂ) : HasSum (fun n : ℕ => w ^ n / n !) (Complex.exp w) := by
    simpa only [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp w
  have hgs : HasSum g (Complex.cosh z) := by
    have h := ((hexp z).add (hexp (-z))).div_const 2
    rw [show (Complex.exp z + Complex.exp (-z)) / 2 = Complex.cosh z by
      rw [← Complex.two_cosh]; ring] at h
    refine h.congr_fun fun n => ?_
    show (1 + (-1 : ℂ) ^ n) / 2 * z ^ n / n ! = (z ^ n / n ! + (-z) ^ n / n !) / 2
    rw [neg_pow]
    ring
  have hgn : Summable fun n => ‖g n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (Real.summable_pow_div_factorial ‖z‖)
    simp only [hg, norm_div, norm_mul, norm_pow, Complex.norm_natCast]
    have h1 : ‖(1 : ℂ) + (-1) ^ n‖ / ‖(2 : ℂ)‖ ≤ 1 := by
      rcases neg_one_pow_eq_or ℂ n with h | h <;> rw [h] <;> norm_num
    rw [div_le_div_iff_of_pos_right (by exact_mod_cast Nat.factorial_pos n)]
    calc ‖(1 : ℂ) + (-1) ^ n‖ / ‖(2 : ℂ)‖ * ‖z‖ ^ n ≤ 1 * ‖z‖ ^ n := by gcongr
      _ = ‖z‖ ^ n := one_mul _
  have hprod := hasSum_sum_range_mul_of_summable_norm hfn hgn
  rw [hgs.tsum_eq] at hprod
  have hcoef (n : ℕ) : ∑ k ∈ range (n + 1), f k * g (n - k) = z ^ n / n ! * 0 ^ n := by
    have hr := congrArg (fun q : ℚ => (q : ℂ)) (sum_choose_mul_eulerNumber n)
    push_cast at hr
    have hfac : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hterm : ∀ k ∈ range (n + 1), f k * g (n - k) =
        z ^ n / n ! / 2 * ((n.choose k : ℂ) * (1 + (-1) ^ (n - k)) * eulerNumber k) := by
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
      simp only [hf, hg]
      have hk1 : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
      have hk2 : ((n - k)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hch : (n.choose k : ℂ) = n ! / (k ! * (n - k)!) := by
        rw [Nat.choose_eq_factorial_div_factorial hkn, Nat.cast_div
          (Nat.factorial_mul_factorial_dvd_factorial hkn) (by push_cast; exact mul_ne_zero hk1 hk2)]
        push_cast; ring
      rw [hch, show z ^ n = z ^ k * z ^ (n - k) by rw [← pow_add, Nat.add_sub_cancel' hkn]]
      field_simp
    rw [sum_congr rfl hterm, ← mul_sum, hr]
    ring
  simp_rw [hcoef] at hprod
  have hone : HasSum (fun n : ℕ => z ^ n / n ! * 0 ^ n) 1 := by
    convert hasSum_single (f := fun n : ℕ => z ^ n / n ! * 0 ^ n) 0 (fun n hn => by simp [hn])
    simp
  have hSC := hprod.unique hone
  have hc : Complex.cosh z ≠ 0 := by
    intro h; rw [h, mul_zero] at hSC; exact zero_ne_one hSC
  rw [← eq_inv_of_mul_eq_one_left hSC]
  exact (Summable.of_norm hfn).hasSum

open scoped Nat in
/-- **The secant Taylor series** (Duverney (2.55)): for `‖z‖ < 1/2`,
`sec z = ∑ₖ (-1)ᵏ E₂ₖ z^{2k}/(2k)!`. -/
theorem hasSum_eulerNumber_sec {z : ℂ} (hz : ‖z‖ < 1 / 2) :
    HasSum (fun k : ℕ => (-1) ^ k * (eulerNumber (2 * k) : ℂ) * z ^ (2 * k) / (2 * k)!)
      (Complex.cos z)⁻¹ := by
  have h := hasSum_eulerNumber_mul_pow_div (z := z * Complex.I) (by
    rw [norm_mul, Complex.norm_I, mul_one]; exact hz)
  rw [Complex.cosh_mul_I] at h
  have hodd : ∀ n ∉ Set.range (fun k : ℕ => 2 * k),
      (eulerNumber n : ℂ) * (z * Complex.I) ^ n / n ! = 0 := by
    intro n hn
    have : Odd n := by
      rcases Nat.even_or_odd n with ⟨m, hm⟩ | h
      · exact absurd ⟨m, by simp only; omega⟩ hn
      · exact h
    simp [eulerNumber_eq_zero_of_odd this]
  have h2 := ((mul_right_injective₀ (two_ne_zero : (2 : ℕ) ≠ 0)).hasSum_iff hodd).mpr h
  refine h2.congr_fun fun k => ?_
  simp only [Function.comp]
  rw [mul_pow, pow_mul Complex.I, Complex.I_sq]
  ring

end Polynomial

end
