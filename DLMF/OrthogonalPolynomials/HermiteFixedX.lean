/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Integrals
public import DLMFMathlib.Analysis.ODE.Volterra

/-!
# Hermite polynomials of large degree at a fixed point

The Hermite function `u = e^{-x²/2} H_n` solves `u'' + (2n+1) u = x² u`. The Volterra
perturbation estimate `ODE.norm_sub_oscFree_le'` with `ω = √(2n+1)` and `g = x²` compares
`u` with the free oscillation having the same data at `0`, and the data at `0` are known
explicitly. This gives the leading term of the large-`n` expansion at fixed `x`
(Beals–Wong, §13.1; Szegő, (8.22.8)) with an explicit error bound:

* `abs_hermite_div_lambda_sub_cos_le`, `hermite_div_lambda_isBigO`: DLMF 18.15.27 with
  `M = 1`, `e^{-x²/2} H_n(x) / λ_n = cos (√(2n+1) x - nπ/2) + O(n^{-1/2})`, with the
  parity-dependent constant `λ_n` of DLMF 18.15.25;
* `abs_hermite_scaled_sub_cos_le`, `hermite_scaled_isBigO`: Szegő's form with the constant
  `Γ(n+1)/Γ(n/2+1)`.
-/

@[expose] public section

open Polynomial Filter Asymptotics Set Real

noncomputable section

namespace DLMF.OrthogonalPolynomials

namespace HermiteFixedX

/-- The Hermite function `e^{-x²/2} H_n(x)`. -/
def u (n : ℕ) (x : ℝ) : ℝ := exp (-x ^ 2 / 2) * (hermitePolyHR n).eval x

/-- The derivative of the Hermite function. -/
def u' (n : ℕ) (x : ℝ) : ℝ :=
  exp (-x ^ 2 / 2) * ((hermitePolyHR n).derivative.eval x - x * (hermitePolyHR n).eval x)

/-- The frequency `√(2n+1)`. -/
def freq (n : ℕ) : ℝ := √(2 * n + 1)

theorem freq_pos (n : ℕ) : 0 < freq n := Real.sqrt_pos.2 (by positivity)

theorem one_le_freq (n : ℕ) : 1 ≤ freq n := by
  rw [freq, Real.one_le_sqrt]
  have : (0 : ℝ) ≤ n := n.cast_nonneg
  linarith

theorem freq_sq (n : ℕ) : freq n ^ 2 = 2 * n + 1 := Real.sq_sqrt (by positivity)

theorem hermitePolyHR_ode (n : ℕ) (x : ℝ) :
    (hermitePolyHR n).derivative.derivative.eval x -
        2 * x * (hermitePolyHR n).derivative.eval x + 2 * n * (hermitePolyHR n).eval x = 0 := by
  have h := congrArg (fun p : ℤ[X] => (p.map (Int.castRingHom ℝ)).eval x)
    (hermitePolyH_differential_equation n)
  simpa [Polynomial.derivative_map, hermitePolyHR] using h

theorem hasDerivAt_exp_neg_sq_half (x : ℝ) :
    HasDerivAt (fun x => exp (-x ^ 2 / 2)) (exp (-x ^ 2 / 2) * -x) x := by
  have h := ((hasDerivAt_pow 2 x).neg.div_const 2).exp
  simp only [Pi.neg_apply] at h
  convert h using 1
  push_cast
  ring

theorem hasDerivAt_u (n : ℕ) (x : ℝ) : HasDerivAt (u n) (u' n x) x := by
  have h := (hasDerivAt_exp_neg_sq_half x).mul (Polynomial.hasDerivAt (hermitePolyHR n) x)
  refine h.congr_deriv ?_
  simp only [u']
  ring

theorem hasDerivAt_u' (n : ℕ) (x : ℝ) :
    HasDerivAt (u' n) ((x ^ 2 - freq n ^ 2) * u n x) x := by
  have h := (hasDerivAt_exp_neg_sq_half x).mul
    ((Polynomial.hasDerivAt (hermitePolyHR n).derivative x).sub
      ((hasDerivAt_id x).mul (Polynomial.hasDerivAt (hermitePolyHR n) x)))
  simp only [Pi.sub_apply, Pi.mul_apply, id] at h
  refine h.congr_deriv ?_
  simp only [u, freq_sq]
  linear_combination (exp (-x ^ 2 / 2)) * hermitePolyHR_ode n x

/-- The perturbation estimate for `x ≥ 0`. -/
theorem abs_u_sub_oscFree_le_of_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    |u n x - ODE.oscFree (freq n) 0 (u n 0) (u' n 0) x| ≤
      (|u n 0| + |u' n 0| / freq n) * (exp (x ^ 3 / 3 / freq n) - 1) := by
  have h := ODE.norm_sub_oscFree_le' (E := ℝ) (a := 0) (b := x) (ω := freq n)
    (freq_pos n).ne' (g := fun t => t ^ 2) (u := u n) (u' := u' n)
    (continuous_pow 2).continuousOn (fun t _ => hasDerivAt_u n t)
    (fun t _ => by simpa [smul_eq_mul] using hasDerivAt_u' n t) ⟨hx, le_rfl⟩
  have hint : ∫ t in (0 : ℝ)..x, |t ^ 2| = x ^ 3 / 3 := by
    simp only [fun t : ℝ => abs_of_nonneg (sq_nonneg t)]
    rw [integral_pow]
    norm_num
  simpa only [Real.norm_eq_abs, hint, abs_of_pos (freq_pos n)] using h

/-- The perturbation estimate on all of `ℝ`, using the parity of the equation for `x < 0`. -/
theorem abs_u_sub_oscFree_le (n : ℕ) (x : ℝ) :
    |u n x - ODE.oscFree (freq n) 0 (u n 0) (u' n 0) x| ≤
      (|u n 0| + |u' n 0| / freq n) * (exp (|x| ^ 3 / 3 / freq n) - 1) := by
  rcases le_or_gt 0 x with hx | hx
  · simpa [abs_of_nonneg hx] using abs_u_sub_oscFree_le_of_nonneg n hx
  · set v : ℝ → ℝ := fun t => u n (-t)
    set v' : ℝ → ℝ := fun t => -u' n (-t)
    have hv : ∀ t, HasDerivAt v (v' t) t := fun t => by
      have := (hasDerivAt_u n (-t)).comp t (hasDerivAt_neg t)
      refine this.congr_deriv ?_
      simp [v']
    have hv' : ∀ t, HasDerivAt v' ((t ^ 2 - freq n ^ 2) • v t) t := fun t => by
      have := ((hasDerivAt_u' n (-t)).comp t (hasDerivAt_neg t)).neg
      refine this.congr_deriv ?_
      simp [v, smul_eq_mul]
    have h := ODE.norm_sub_oscFree_le' (E := ℝ) (a := 0) (b := -x) (ω := freq n)
      (freq_pos n).ne' (g := fun t => t ^ 2) (u := v) (u' := v')
      (continuous_pow 2).continuousOn (fun t _ => hv t) (fun t _ => hv' t)
      ⟨by linarith, le_rfl⟩
    have hint : ∫ t in (0 : ℝ)..(-x), |t ^ 2| = (-x) ^ 3 / 3 := by
      simp only [fun t : ℝ => abs_of_nonneg (sq_nonneg t)]
      rw [integral_pow]
      norm_num
    have hosc : ODE.oscFree (freq n) 0 (v 0) (v' 0) (-x) =
        ODE.oscFree (freq n) 0 (u n 0) (u' n 0) x := by
      simp only [ODE.oscFree, v, v', neg_zero, sub_zero, mul_neg, Real.cos_neg, Real.sin_neg,
        smul_eq_mul]
      ring
    simp only [Real.norm_eq_abs, hint, abs_of_pos (freq_pos n), hosc] at h
    simpa [v, v', abs_of_neg hx, abs_neg] using h

/-! ### The data at `0` -/

theorem hermitePolyH_odd_at_zero (m : ℕ) : (hermitePolyH (2 * m + 1)).eval 0 = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring, hermitePolyH_succ,
      hermitePolyH_derivative]
    simp only [eval_sub, eval_mul, eval_ofNat, eval_X, eval_C, ih, mul_zero, zero_mul,
      sub_zero]

theorem hermitePolyHR_eval_zero (n : ℕ) :
    (hermitePolyHR n).eval 0 = ((hermitePolyH n).eval 0 : ℤ) :=
  eval_zero_map _ _

theorem hermitePolyHR_derivative_eval_zero (k : ℕ) :
    (hermitePolyHR (k + 1)).derivative.eval 0 = 2 * (k + 1) * (hermitePolyHR k).eval 0 := by
  rw [hermitePolyHR, Polynomial.derivative_map, hermitePolyH_derivative, Polynomial.map_mul,
    Polynomial.map_C, eval_mul, eval_C]
  simp [hermitePolyHR]

theorem hermitePolyHR_even_eval_zero (m : ℕ) :
    (hermitePolyHR (2 * m)).eval 0 =
      (-1) ^ m * ((2 * m).factorial / m.factorial : ℝ) := by
  rw [hermitePolyHR_eval_zero, hermitePolyH_even_at_zero, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, Int.cast_natCast,
    Nat.cast_div (Nat.factorial_dvd_factorial (by omega)) (by positivity)]

theorem u_zero (n : ℕ) : u n 0 = (hermitePolyHR n).eval 0 := by simp [u]

theorem u'_zero (n : ℕ) : u' n 0 = (hermitePolyHR n).derivative.eval 0 := by simp [u']

end HermiteFixedX

open HermiteFixedX in
/-- The constant `λ_n` of DLMF 18.15.25: `Γ(n+1)/Γ(n/2+1)` for even `n` and
`Γ(n+2)/(√(2n+1) Γ(n/2+3/2))` for odd `n`. -/
@[dlmf 18.15.E25]
def hermiteLambda (n : ℕ) : ℝ :=
  if Even n then Real.Gamma (n + 1) / Real.Gamma (n / 2 + 1)
  else Real.Gamma (n + 2) / (√(2 * n + 1) * Real.Gamma (n / 2 + 3 / 2))

namespace HermiteFixedX

theorem hermiteLambda_even (m : ℕ) :
    hermiteLambda (2 * m) = ((2 * m).factorial / m.factorial : ℝ) := by
  simp only [hermiteLambda, even_two_mul m, ↓reduceIte]
  rw [show (((2 * m : ℕ) : ℝ) / 2 + 1) = (m : ℝ) + 1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial]

theorem hermiteLambda_odd (m : ℕ) :
    hermiteLambda (2 * m + 1) =
      ((2 * m + 2).factorial / (m + 1).factorial : ℝ) / freq (2 * m + 1) := by
  have hne : ¬Even (2 * m + 1) := Nat.not_even_iff_odd.2 (odd_two_mul_add_one m)
  simp only [hermiteLambda, hne, ↓reduceIte]
  rw [show (((2 * m + 1 : ℕ) : ℝ) / 2 + 3 / 2) = ((m + 1 : ℕ) : ℝ) + 1 by push_cast; ring,
    show (((2 * m + 1 : ℕ) : ℝ) + 2) = ((2 * m + 2 : ℕ) : ℝ) + 1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial, freq]
  field_simp

/-- The data at `0` of the Hermite function in terms of `λ_n`. -/
theorem data_zero (n : ℕ) :
    u n 0 = hermiteLambda n * Real.cos (n * π / 2) ∧
      u' n 0 = freq n * (hermiteLambda n * Real.sin (n * π / 2)) ∧
      |u n 0| + |u' n 0| / freq n = hermiteLambda n ∧ 0 < hermiteLambda n := by
  have hω := freq_pos n
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hpos : 0 < ((2 * m).factorial / m.factorial : ℝ) := by positivity
    have harg : ((2 * m : ℕ) : ℝ) * π / 2 = (m : ℝ) * π := by push_cast; ring
    have hd : u' (2 * m) 0 = 0 := by
      rw [u'_zero]
      rcases m with _ | k
      · simp
      · rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, hermitePolyHR_derivative_eval_zero,
          hermitePolyHR_eval_zero, hermitePolyH_odd_at_zero]
        simp
    rw [hd, harg, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi, hermiteLambda_even, u_zero,
      hermitePolyHR_even_eval_zero]
    refine ⟨by ring, by ring, ?_, hpos⟩
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos hpos]
    simp
  · have hpos : 0 < ((2 * m + 2).factorial / (m + 1).factorial : ℝ) / freq (2 * m + 1) := by
      positivity
    have harg : ((2 * m + 1 : ℕ) : ℝ) * π / 2 = (m : ℝ) * π + π / 2 := by push_cast; ring
    have h0 : u (2 * m + 1) 0 = 0 := by
      rw [u_zero, hermitePolyHR_eval_zero, hermitePolyH_odd_at_zero]
      simp
    have hd : u' (2 * m + 1) 0 =
        2 * (2 * m + 1) * ((-1) ^ m * ((2 * m).factorial / m.factorial : ℝ)) := by
      rw [u'_zero, hermitePolyHR_derivative_eval_zero, hermitePolyHR_even_eval_zero]
      push_cast
      ring
    have hfac : 2 * (2 * m + 1) * ((2 * m).factorial / m.factorial : ℝ) =
        ((2 * m + 2).factorial / (m + 1).factorial : ℝ) := by
      rw [show 2 * m + 2 = (2 * m + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
        Nat.factorial_succ m]
      push_cast
      field_simp
      ring
    rw [h0, hd, harg, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two, Real.sin_nat_mul_pi,
      Real.cos_nat_mul_pi, hermiteLambda_odd]
    refine ⟨by ring, ?_, ?_, hpos⟩
    · rw [← hfac]
      field_simp [hω.ne']
    · rw [show 2 * (2 * (m : ℝ) + 1) * ((-1) ^ m * ((2 * m).factorial / m.factorial : ℝ)) =
          (-1) ^ m * (2 * (2 * m + 1) * ((2 * m).factorial / m.factorial : ℝ)) by ring, hfac,
        abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_zero, zero_add,
        abs_of_pos (by positivity)]

/-- The free oscillation with the data of the Hermite function is `λ_n cos (√(2n+1) x - nπ/2)`. -/
theorem oscFree_eq (n : ℕ) (x : ℝ) :
    ODE.oscFree (freq n) 0 (u n 0) (u' n 0) x =
      hermiteLambda n * Real.cos (freq n * x - n * π / 2) := by
  obtain ⟨h0, h1, -, -⟩ := data_zero n
  rw [ODE.oscFree, h0, h1, Real.cos_sub, sub_zero, smul_eq_mul, smul_eq_mul]
  field_simp [(freq_pos n).ne']

theorem exp_sub_one_le (y : ℝ) : Real.exp y - 1 ≤ y * Real.exp y := by
  have h := Real.add_one_le_exp (-y)
  have he : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add, neg_add_cancel, exp_zero]
  have hpos := Real.exp_pos y
  nlinarith

/-- The explicit error bound behind DLMF 18.15.27 with `M = 1`. -/
theorem abs_u_div_sub_cos_le (n : ℕ) (x : ℝ) :
    |u n x / hermiteLambda n - Real.cos (freq n * x - n * π / 2)| ≤
      |x| ^ 3 * Real.exp (|x| ^ 3 / 3) / (3 * freq n) := by
  obtain ⟨-, -, hM, hlam⟩ := data_zero n
  have hω := freq_pos n
  have h1 := one_le_freq n
  have hb := abs_u_sub_oscFree_le n x
  rw [hM, oscFree_eq] at hb
  have hy : 0 ≤ |x| ^ 3 / 3 / freq n := by positivity
  have hy' : |x| ^ 3 / 3 / freq n ≤ |x| ^ 3 / 3 := div_le_self (by positivity) h1
  have he := exp_sub_one_le (|x| ^ 3 / 3 / freq n)
  have he' : Real.exp (|x| ^ 3 / 3 / freq n) ≤ Real.exp (|x| ^ 3 / 3) := Real.exp_le_exp.2 hy'
  rw [show u n x / hermiteLambda n - Real.cos (freq n * x - n * π / 2) =
      (u n x - hermiteLambda n * Real.cos (freq n * x - n * π / 2)) / hermiteLambda n by
    field_simp, abs_div, abs_of_pos hlam, div_le_iff₀ hlam]
  calc _ ≤ hermiteLambda n * (Real.exp (|x| ^ 3 / 3 / freq n) - 1) := hb
    _ ≤ hermiteLambda n * (|x| ^ 3 / 3 / freq n * Real.exp (|x| ^ 3 / 3)) := by
        gcongr
        exact he.trans (mul_le_mul_of_nonneg_left he' hy)
    _ = _ := by field_simp

end HermiteFixedX

open HermiteFixedX

/-- **Hermite polynomials of large degree at a fixed point**, DLMF 18.15.27 with `M = 1`,
with an explicit error bound:
`|e^{-x²/2} H_n(x) / λ_n - cos (√(2n+1) x - nπ/2)| ≤ |x|³ e^{|x|³/3} / (3 √(2n+1))`. -/
@[dlmf 18.15.E27]
theorem abs_hermite_div_lambda_sub_cos_le (n : ℕ) (x : ℝ) :
    |Real.exp (-x ^ 2 / 2) * aeval x (hermitePolyH n) / hermiteLambda n -
        Real.cos (√(2 * n + 1) * x - n * π / 2)| ≤
      |x| ^ 3 * Real.exp (|x| ^ 3 / 3) / (3 * √(2 * n + 1)) := by
  have h := abs_u_div_sub_cos_le n x
  rwa [u, ← aeval_hermitePolyH_eq_eval] at h

/-- DLMF 18.15.27 with `M = 1`: `e^{-x²/2} H_n(x) = λ_n (cos (√(2n+1) x - nπ/2) + O(n^{-1/2}))`
as `n → ∞`, for fixed real `x`. -/
@[dlmf 18.15.E27]
theorem hermite_div_lambda_isBigO (x : ℝ) :
    (fun n : ℕ => Real.exp (-x ^ 2 / 2) * aeval x (hermitePolyH n) / hermiteLambda n -
        Real.cos (√(2 * n + 1) * x - n * π / 2)) =O[atTop]
      fun n : ℕ => (√(2 * n + 1))⁻¹ := by
  refine IsBigO.of_bound (|x| ^ 3 * Real.exp (|x| ^ 3 / 3) / 3) (Eventually.of_forall fun n => ?_)
  have hω : 0 < √(2 * (n : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_pos hω]
  calc _ ≤ |x| ^ 3 * Real.exp (|x| ^ 3 / 3) / (3 * √(2 * n + 1)) :=
        abs_hermite_div_lambda_sub_cos_le n x
    _ = _ := by field_simp

namespace HermiteFixedX

/-- Szegő's normalizing constant `Γ(n+1)/Γ(n/2+1)`. -/
def szegoConst (n : ℕ) : ℝ := Real.Gamma (n + 1) / Real.Gamma (n / 2 + 1)

theorem szegoConst_pos (n : ℕ) : 0 < szegoConst n :=
  div_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.Gamma_pos_of_pos (by positivity))

/-- `λ_n` and Szegő's constant agree up to a factor `1 + O(1/n)`. -/
theorem lambda_div_szegoConst (n : ℕ) :
    hermiteLambda n / szegoConst n ≤ 2 ∧
      |hermiteLambda n / szegoConst n - 1| ≤ 3 / (2 * n + 1) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have h : hermiteLambda (2 * m) = szegoConst (2 * m) := by
      simp only [hermiteLambda, even_two_mul m, ↓reduceIte, szegoConst]
    rw [h, div_self (szegoConst_pos _).ne']
    refine ⟨by norm_num, ?_⟩
    rw [sub_self, abs_zero]
    positivity
  · set Q := Real.Gamma (m + 1 / 2 + 1) / Real.Gamma (m + 1 / 2 + 1 / 2) with hQ
    have hω := freq_pos (2 * m + 1)
    have hω2 : freq (2 * m + 1) ^ 2 = 4 * m + 3 := by rw [freq_sq]; push_cast; ring
    have hratio : hermiteLambda (2 * m + 1) / szegoConst (2 * m + 1) =
        2 * Q / freq (2 * m + 1) := by
      have hne : ¬Even (2 * m + 1) := Nat.not_even_iff_odd.2 (odd_two_mul_add_one m)
      simp only [hermiteLambda, hne, ↓reduceIte, szegoConst, hQ]
      have hG1 : Real.Gamma ((2 * m + 1 : ℕ) + 2) =
          ((2 * m + 1 : ℕ) + 1) * Real.Gamma ((2 * m + 1 : ℕ) + 1) := by
        rw [show ((2 * m + 1 : ℕ) : ℝ) + 2 = ((2 * m + 1 : ℕ) + 1) + 1 by ring,
          Real.Gamma_add_one (by positivity)]
      have hG2 : Real.Gamma (((2 * m + 1 : ℕ) : ℝ) / 2 + 3 / 2) =
          ((m : ℝ) + 1) * Real.Gamma (m + 1 / 2 + 1 / 2) := by
        rw [show ((2 * m + 1 : ℕ) : ℝ) / 2 + 3 / 2 = ((m : ℝ) + 1 / 2 + 1 / 2) + 1 by
          push_cast; ring, Real.Gamma_add_one (by positivity)]
        ring
      have hG3 : ((2 * m + 1 : ℕ) : ℝ) / 2 + 1 = (m : ℝ) + 1 / 2 + 1 := by push_cast; ring
      rw [hG1, hG2, hG3, freq]
      have h1 : 0 < Real.Gamma (((2 * m + 1 : ℕ) : ℝ) + 1) := Real.Gamma_pos_of_pos (by positivity)
      have h2 : 0 < Real.Gamma ((m : ℝ) + 1 / 2 + 1 / 2) := Real.Gamma_pos_of_pos (by positivity)
      have h3 : 0 < Real.Gamma ((m : ℝ) + 1 / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
      have h4 : 0 < √(2 * ((2 * m + 1 : ℕ) : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
      field_simp
      push_cast
      ring
    obtain ⟨hlo, hhi⟩ := DLMF.Gamma.Gamma_ratio_bounds (x := (m : ℝ) + 1 / 2) (s := 1 / 2)
      (by positivity) (by norm_num) (by norm_num)
    rw [← hQ, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow] at hlo hhi
    have hQpos : 0 < Q := lt_of_le_of_lt (Real.sqrt_nonneg _) hlo
    have hQ2lo : (m : ℝ) + 1 / 2 < Q ^ 2 := (Real.sqrt_lt' hQpos).1 hlo
    have hQ2hi : Q ^ 2 < (m : ℝ) + 1 / 2 + 1 := (Real.lt_sqrt hQpos.le).1 hhi
    rw [hratio]
    set r := 2 * Q / freq (2 * m + 1) with hr
    have hrω : r * freq (2 * m + 1) = 2 * Q := by rw [hr]; field_simp
    have hr2 : r ^ 2 * (4 * m + 3) = 4 * Q ^ 2 := by
      rw [← hω2, ← mul_pow, hrω]; ring
    have hrpos : 0 < r := by positivity
    have hm : (0 : ℝ) ≤ m := m.cast_nonneg
    have hden : (0 : ℝ) < 4 * m + 3 := by positivity
    have hr4 : r ^ 2 < 4 := by
      have : r ^ 2 * (4 * m + 3) < 4 * (4 * m + 3) := by nlinarith
      exact lt_of_mul_lt_mul_right this hden.le
    refine ⟨by nlinarith, ?_⟩
    rw [show 2 * ((2 * m + 1 : ℕ) : ℝ) + 1 = 4 * m + 3 by push_cast; ring]
    have hup : (r - 1) * (4 * m + 3) ≤ 3 := by
      rcases le_or_gt r 1 with h | h
      · nlinarith
      · nlinarith [mul_nonneg (mul_nonneg hrpos.le (sub_nonneg.2 h.le)) hden.le]
    have hlo' : -3 ≤ (r - 1) * (4 * m + 3) := by
      rcases le_or_gt r 1 with h | h
      · nlinarith [mul_nonneg (mul_nonneg hrpos.le (sub_nonneg.2 h)) hden.le]
      · nlinarith
    rw [abs_le]
    constructor
    · rw [← neg_div, div_le_iff₀ hden]
      exact hlo'
    · rw [le_div_iff₀ hden]
      exact hup

end HermiteFixedX

/-- **Hermite polynomials of large degree at a fixed point** in Szegő's normalization
(Szegő, (8.22.8); Beals–Wong, §13.1), with an explicit error bound:
`|Γ(n/2+1)/Γ(n+1) e^{-x²/2} H_n(x) - cos (√(2n+1) x - nπ/2)| ≤
(3 + |x|³ e^{|x|³/3}) / √(2n+1)`. -/
theorem abs_hermite_scaled_sub_cos_le (n : ℕ) (x : ℝ) :
    |Real.exp (-x ^ 2 / 2) * aeval x (hermitePolyH n) * Real.Gamma (n / 2 + 1) /
          Real.Gamma (n + 1) - Real.cos (√(2 * n + 1) * x - n * π / 2)| ≤
      (3 + |x| ^ 3 * Real.exp (|x| ^ 3 / 3)) / √(2 * n + 1) := by
  obtain ⟨hρ2, hρ1⟩ := lambda_div_szegoConst n
  obtain ⟨-, -, -, hlam⟩ := data_zero n
  have hA := abs_hermite_div_lambda_sub_cos_le n x
  have hC := szegoConst_pos n
  have hω : 0 < √(2 * (n : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  have hω1 : 1 ≤ √(2 * (n : ℝ) + 1) := one_le_freq n
  set A := Real.exp (-x ^ 2 / 2) * aeval x (hermitePolyH n) / hermiteLambda n -
    Real.cos (√(2 * n + 1) * x - n * π / 2) with hAdef
  set c := Real.cos (√(2 * n + 1) * x - n * π / 2) with hc
  set ρ := hermiteLambda n / szegoConst n with hρ
  have hρpos : 0 < ρ := div_pos hlam hC
  have hexpr : Real.exp (-x ^ 2 / 2) * aeval x (hermitePolyH n) * Real.Gamma (n / 2 + 1) /
      Real.Gamma (n + 1) - c = A * ρ + c * (ρ - 1) := by
    rw [hAdef, hρ, szegoConst]
    have h1 : 0 < Real.Gamma ((n : ℝ) + 1) := Real.Gamma_pos_of_pos (by positivity)
    have h2 : 0 < Real.Gamma ((n : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
    field_simp
    ring
  rw [hexpr]
  have hc1 : |c| ≤ 1 := Real.abs_cos_le_one _
  have hK : 0 ≤ |x| ^ 3 * Real.exp (|x| ^ 3 / 3) := by positivity
  have hsq : 3 / (2 * (n : ℝ) + 1) ≤ 3 / √(2 * n + 1) := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * n + 1 by positivity)
    exact div_le_div_of_nonneg_left (by norm_num) hω (by nlinarith)
  calc |A * ρ + c * (ρ - 1)| ≤ |A| * ρ + 1 * |ρ - 1| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_pos hρpos]
        gcongr
    _ ≤ |x| ^ 3 * Real.exp (|x| ^ 3 / 3) / (3 * √(2 * n + 1)) * 2 +
          1 * (3 / √(2 * n + 1)) := by
        gcongr
        exact hρ1.trans hsq
    _ = (3 + 2 / 3 * (|x| ^ 3 * Real.exp (|x| ^ 3 / 3))) / √(2 * n + 1) := by
        field_simp
        ring
    _ ≤ (3 + |x| ^ 3 * Real.exp (|x| ^ 3 / 3)) / √(2 * n + 1) :=
        div_le_div_of_nonneg_right (by linarith) hω.le

/-- Szegő's form (8.22.8): `Γ(n/2+1)/Γ(n+1) e^{-x²/2} H_n(x) = cos (√(2n+1) x - nπ/2) +
O(n^{-1/2})` as `n → ∞`, for fixed real `x`. -/
theorem hermite_scaled_isBigO (x : ℝ) :
    (fun n : ℕ => Real.exp (-x ^ 2 / 2) * aeval x (hermitePolyH n) * Real.Gamma (n / 2 + 1) /
          Real.Gamma (n + 1) - Real.cos (√(2 * n + 1) * x - n * π / 2)) =O[atTop]
      fun n : ℕ => (√(2 * n + 1))⁻¹ := by
  refine IsBigO.of_bound (3 + |x| ^ 3 * Real.exp (|x| ^ 3 / 3))
    (Eventually.of_forall fun n => ?_)
  have hω : 0 < √(2 * (n : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_pos hω, ← div_eq_mul_inv]
  exact abs_hermite_scaled_sub_cos_le n x

end DLMF.OrthogonalPolynomials
