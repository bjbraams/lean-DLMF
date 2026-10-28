/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Elementary
public import DLMF.OrthogonalPolynomials.Mehler
public import DLMF.Confluent.ProductsAddition
public import DLMF.OrthogonalPolynomials.Explicit
public import DLMF.OrthogonalPolynomials.LegendreAddition
public import DLMF.OrthogonalPolynomials.GegenbauerSeries
public import DLMF.OrthogonalPolynomials.LaguerreSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import DLMFMathlib.Analysis.Complex.LagrangeBurmann
public import DLMF.Hypergeometric.AppellF4

/-!
# Classical polynomial generating functions

Scalar-series convolution, Jacobi Lagrange inversion and classical generating and multiplication
identities.

Source references and common attribution are retained in
`DLMF.OrthogonalPolynomials.Series`.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter

open scoped Real Nat Topology

open DLMF.Hypergeometric

open DLMF.Confluent

open DLMF.Bessel

noncomputable section

set_option autoImplicit false

namespace DLMF.OrthogonalPolynomials

/-- Cauchy product of scalar series, written as a coefficient convolution. -/
theorem hasSum_scalar_convolution {c d : ℕ → ℂ} {z u v : ℂ}
    (hc : HasSum (fun n => c n * z ^ n) u)
    (hd : HasSum (fun n => d n * z ^ n) v) :
    HasSum (fun n => (∑ k ∈ Finset.range (n + 1), c k * d (n - k)) * z ^ n) (u * v) := by
  exact hasSum_coefficient_convolution hc hd

/-- Insert zero odd coefficients into the exponential series. -/
theorem hasSum_exp_quadratic (q z : ℂ) :
    HasSum (fun n : ℕ => (if n % 2 = 0 then q ^ (n / 2) / (n / 2)! else 0) * z ^ n)
      (exp (q * z ^ 2)) := by
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := by intro i j h; dsimp at h; omega
  apply (hinj.hasSum_iff (fun n hn => ?_)).mp
  · convert NormedSpace.expSeries_div_hasSum_exp (q * z ^ 2) using 1
    · funext k
      simp only [Function.comp_apply, Nat.mul_mod_right, ↓reduceIte, Nat.mul_div_cancel_left,
        Nat.ofNat_pos, mul_pow, pow_mul]
      ring
    · simp only [Complex.exp_eq_exp_ℂ]
  · have hodd : n % 2 ≠ 0 := by
      intro he
      exact hn ⟨n / 2, by dsimp; omega⟩
    simp [hodd]

/-- Sum the even-indexed terms of a finite interval. -/
theorem sum_even_range (f : ℕ → ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), if k % 2 = 0 then f k else 0) =
      ∑ k ∈ Finset.range (n / 2 + 1), f (2 * k) := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun k _ => 2 * k)
  · intro k hk
    simp only [Finset.mem_range, Finset.mem_filter] at hk ⊢
    omega
  · intro i hi j hj he
    omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    refine ⟨k / 2, Finset.mem_range.mpr (by omega), by omega⟩
  · intro k hk
    rfl

/-- A quadratic exponential times the Hermite generating function. -/
theorem hasSum_exp_quadratic_mul_hermite (q lam x z : ℂ) :
    HasSum (fun n : ℕ => (∑ k ∈ Finset.range (n / 2 + 1),
      q ^ k / k ! * ((aeval x (hermitePolyH (n - 2 * k)) : ℂ) / (n - 2 * k)! *
        lam ^ (n - 2 * k))) * z ^ n)
      (exp (q * z ^ 2 + (2 * x * (lam * z) - (lam * z) ^ 2))) := by
  have hh : HasSum (fun n => ((aeval x (hermitePolyH n) : ℂ) / n ! * lam ^ n) * z ^ n)
      (exp (2 * x * (lam * z) - (lam * z) ^ 2)) := by
    convert hasSum_hermitePolyH_generating_function x (lam * z) using 1
    funext n; rw [mul_pow]; ring
  have h := hasSum_scalar_convolution (hasSum_exp_quadratic q z) hh
  rw [← exp_add] at h
  convert h using 1
  funext n
  congr 1
  simp_rw [ite_mul, zero_mul]
  rw [sum_even_range]
  simp

/-- The factorial ratio in the even-indexed Hermite formulas. -/
theorem poch_neg_nat_even_mul_factorial {n k : ℕ} (hk : 2 * k ≤ n) :
    poch (-(n : ℂ)) (2 * k) * ((n - 2 * k)! : ℂ) = n ! := by
  have h := poch_neg_nat_mul_factorial hk
  simpa [pow_mul] using h

section JacobiLagrange

open Metric Set

/-- Iterated derivatives of `(1 + a t)^s` on the slit-plane region. -/
theorem jacGen_iteratedDeriv_cpow (a s : ℂ) (k : ℕ) {t : ℂ} (ht : 1 + a * t ∈ slitPlane) :
    iteratedDeriv k (fun t => (1 + a * t) ^ s) t =
      a ^ k * ((-1) ^ k * poch (-s) k) * (1 + a * t) ^ (s - k) := by
  have hU : IsOpen {t : ℂ | 1 + a * t ∈ slitPlane} :=
    isOpen_slitPlane.preimage (by fun_prop)
  induction k generalizing t with
  | zero => simp [poch_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv k (fun t => (1 + a * t) ^ s) =ᶠ[𝓝 t]
        fun t => a ^ k * ((-1) ^ k * poch (-s) k) * (1 + a * t) ^ (s - k) :=
      Filter.eventually_of_mem (hU.mem_nhds ht) fun y hy => ih hy
    rw [hev.deriv_eq]
    have hd : HasDerivAt (fun t => 1 + a * t) a t := by
      simpa using ((hasDerivAt_id t).const_mul a).const_add 1
    have := ((hd.cpow_const (c := s - k) ht).const_mul (a ^ k * ((-1) ^ k * poch (-s) k))).deriv
    rw [this, poch_succ]
    push_cast
    rw [show s - (k : ℂ) - 1 = s - (k + 1) by ring]
    ring

/-- `(-1)^k (-s)_k = (s - k + 1)_k`. -/
theorem jacGen_neg_one_pow_mul_poch_neg (s : ℂ) (k : ℕ) :
    (-1 : ℂ) ^ k * poch (-s) k = poch (s - k + 1) k := by
  have h := poch_one_sub_sub (s - k + 1) k
  rw [show 1 - (s - k + 1) - (k : ℂ) = -s by ring] at h
  rw [h, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

/-- `(2/u)^α = 2^α / u^α` in the right half-plane. -/
theorem jacGen_two_div_cpow (α : ℂ) {u : ℂ} (hu : 0 < u.re) :
    (2 / u) ^ α = 2 ^ α / u ^ α := by
  have hu0 : u ≠ 0 := fun h => by simp [h] at hu
  have harg : u.arg ≠ π := by
    intro h
    have := Complex.arg_eq_pi_iff.mp h
    linarith [this.1]
  rw [div_eq_mul_inv, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
    cpow_def_of_ne_zero (mul_ne_zero (by norm_num) (inv_ne_zero hu0)),
    log_ofReal_mul (by norm_num) (inv_ne_zero hu0), log_inv _ harg,
    cpow_def_of_ne_zero (by norm_num), cpow_def_of_ne_zero hu0, ← ofReal_log (by norm_num)]
  rw [div_eq_mul_inv, ← exp_neg, ← exp_add]
  congr 1
  ring

/-- Analyticity of `(1 + a t)^s` at `0`. -/
theorem jacGen_analyticAt_cpow (a s : ℂ) : AnalyticAt ℂ (fun t => (1 + a * t) ^ s) 0 :=
  AnalyticAt.cpow (by fun_prop) analyticAt_const (by simp [one_mem_slitPlane])

/-- Taylor coefficients of `(1 + a t)^s (1 + b t)^u` at `0`. -/
theorem jacGen_coeff_cpow_mul_cpow (a b s u : ℂ) (n : ℕ) :
    iteratedDeriv n (fun t => (1 + a * t) ^ s * (1 + b * t) ^ u) 0 / n ! =
      ∑ i ∈ Finset.range (n + 1), (poch (s - i + 1) i / i !) *
        (poch (u - (n - i : ℕ) + 1) (n - i) / (n - i)!) * a ^ i * b ^ (n - i) := by
  rw [iteratedDeriv_fun_mul (jacGen_analyticAt_cpow a s).contDiffAt
    (jacGen_analyticAt_cpow b u).contDiffAt, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [jacGen_iteratedDeriv_cpow a s i (by simp [one_mem_slitPlane]),
    jacGen_iteratedDeriv_cpow b u (n - i) (by simp [one_mem_slitPlane]),
    jacGen_neg_one_pow_mul_poch_neg, jacGen_neg_one_pow_mul_poch_neg]
  simp only [mul_zero, add_zero, one_cpow, mul_one]
  rw [Nat.cast_choose ℂ hin]
  have h1 : (i ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr i.factorial_ne_zero
  have h2 : ((n - i)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (n - i).factorial_ne_zero
  have h3 : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  field_simp

/-- The Lagrange–Bürmann coefficient `[tⁿ] F φⁿ` for the Jacobi generating function
(`F = (1 + (x+1)t/2)^α (1 + (x-1)t/2)^β`, `φ = (1 + (x+1)t/2)(1 + (x-1)t/2)`) is
`P_n^{(α,β)}(x)`, by the binomial form 18.5.8. -/
theorem jacGen_coeff_eq_jacobiPolyP {α β : ℂ} (hα : -1 < α.re) (x : ℂ) (n : ℕ) :
    iteratedDeriv n (fun t => (1 + (x + 1) / 2 * t) ^ α * (1 + (x - 1) / 2 * t) ^ β *
      ((1 + (x + 1) / 2 * t) * (1 + (x - 1) / 2 * t)) ^ n) 0 / n ! = jacobiPolyP α β n x := by
  have hev : (fun t => (1 + (x + 1) / 2 * t) ^ α * (1 + (x - 1) / 2 * t) ^ β *
      ((1 + (x + 1) / 2 * t) * (1 + (x - 1) / 2 * t)) ^ n) =ᶠ[𝓝 0]
      fun t => (1 + (x + 1) / 2 * t) ^ (α + n) * (1 + (x - 1) / 2 * t) ^ (β + n) := by
    have hc : ContinuousAt (fun t : ℂ => (1 + (x + 1) / 2 * t, 1 + (x - 1) / 2 * t)) 0 := by
      fun_prop
    have hmem : {p : ℂ × ℂ | p.1 ≠ 0 ∧ p.2 ≠ 0} ∈ 𝓝 ((1 : ℂ), (1 : ℂ)) :=
      (isOpen_ne_fun continuous_fst continuous_const |>.inter
        (isOpen_ne_fun continuous_snd continuous_const)).mem_nhds (by simp)
    have := hc.preimage_mem_nhds (by simpa using hmem)
    filter_upwards [this] with t ht
    obtain ⟨h1, h2⟩ := ht
    rw [cpow_add _ _ h1, cpow_add _ _ h2, cpow_natCast, cpow_natCast, mul_pow]
    ring
  rw [← iteratedDerivWithin_univ, Filter.EventuallyEq.iteratedDerivWithin_eq
    (by simpa using hev) (hev.eq_of_nhds), iteratedDerivWithin_univ,
    jacGen_coeff_cpow_mul_cpow, jacobi_binomial_sum hα, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hb : β + n - ((n - i : ℕ) : ℂ) + 1 = β + i + 1 := by push_cast [hin]; ring
  rw [hb, show α + (n : ℂ) - i + 1 = α + n - i + 1 by ring, div_pow, div_pow]
  have h2n : (2 : ℂ) ^ n = 2 ^ i * 2 ^ (n - i) := by rw [← pow_add, Nat.add_sub_cancel' hin]
  rw [h2n]
  field_simp

/-- For `|x| ≤ 1` and `|z| < 1`, `1 - 2xz + z²` lies in the slit plane. -/
theorem jacGen_mem_slitPlane {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    1 - 2 * x * z + z ^ 2 ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_contra h
  push Not at h
  obtain ⟨hre, him⟩ := h
  have hz2 : z.re ^ 2 + z.im ^ 2 < 1 := by
    have := Complex.sq_norm z
    rw [Complex.normSq_apply] at this
    nlinarith [norm_nonneg z]
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [abs_nonneg x, sq_abs x]
  simp only [sub_re, add_re, one_re, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im,
    pow_two, mul_im, sub_im, add_im, one_im] at hre him
  have : z.im * (z.re - x) = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · rw [h] at hre hz2
    nlinarith [sq_nonneg (z.re - x)]
  · have : z.re = x := by linarith
    rw [this] at hre hz2
    nlinarith

/-- The right side of the Jacobi generating function 18.12.1. -/
noncomputable def jacGenRhs (α β : ℂ) (x : ℝ) (z : ℂ) : ℂ :=
  (2 : ℂ) ^ (α + β) / ((1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) *
    (1 + (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) - z) ^ α *
    (1 + (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) + z) ^ β)

/-- A point of the closed disc of radius `1/2` keeps `1 + c t` in the right half-plane. -/
theorem jacGen_re_pos {c t : ℂ} (hc : ‖c‖ ≤ 1) (ht : ‖t‖ ≤ 1 / 2) : 0 < (1 + c * t).re := by
  have h1 : ‖c * t‖ ≤ 1 / 2 := by
    rw [norm_mul]; nlinarith [norm_nonneg c, norm_nonneg t]
  have h2 := neg_abs_le (c * t).re
  have h3 := Complex.abs_re_le_norm (c * t)
  simp only [add_re, one_re]
  linarith

/-- On the circle `|t| = 1/2`, `|z (1 + a t)(1 + b t)| ≤ 1/4` when `|a|, |b| ≤ 1` and
`|z| ≤ 1/10`. -/
private lemma jacGen_norm_mul_le {a b z t : ℂ} (ha1 : ‖a‖ ≤ 1) (hb1 : ‖b‖ ≤ 1)
    (hzn : ‖z‖ ≤ 1 / 10) (htn : ‖t‖ = 1 / 2) : ‖z * ((1 + a * t) * (1 + b * t))‖ ≤ 1 / 4 := by
  have h1 : ‖1 + a * t‖ ≤ 3 / 2 := (norm_add_le _ _).trans (by
    rw [norm_one, norm_mul, htn]; nlinarith)
  have h2 : ‖1 + b * t‖ ≤ 3 / 2 := (norm_add_le _ _).trans (by
    rw [norm_one, norm_mul, htn]; nlinarith)
  rw [norm_mul, norm_mul]
  calc ‖z‖ * (‖1 + a * t‖ * ‖1 + b * t‖) ≤ (1 / 10) * ((3 / 2) * (3 / 2)) := by gcongr
    _ ≤ 1 / 4 := by norm_num

/-- The factor `c - z a b (t + w)` does not vanish on `|t| ≤ 1/2` when `|a|, |b| ≤ 1`,
`|z| ≤ 1/10`, `|c| ≥ 9/10` and `|w| ≤ 2/9`. -/
private lemma jacGen_sub_ne_zero {a b c z w t : ℂ} (ha1 : ‖a‖ ≤ 1) (hb1 : ‖b‖ ≤ 1)
    (hzn : ‖z‖ ≤ 1 / 10) (hcn : 9 / 10 ≤ ‖c‖) (hwn : ‖w‖ ≤ 2 / 9) (htn : ‖t‖ ≤ 1 / 2) :
    c - z * a * b * (t + w) ≠ 0 := by
  intro h
  have h1 : ‖z * a * b * (t + w)‖ ≤ 1 / 10 := by
    rw [norm_mul, norm_mul, norm_mul]
    have : ‖t + w‖ ≤ 1 := (norm_add_le _ _).trans (by linarith)
    calc ‖z‖ * ‖a‖ * ‖b‖ * ‖t + w‖ ≤ (1 / 10) * 1 * 1 * 1 := by gcongr
      _ = 1 / 10 := by norm_num
  rw [sub_eq_zero] at h
  rw [h] at hcn
  linarith

/-- The Jacobi generating function for small `|z|`, by the Lagrange–Bürmann formula. -/
theorem jacGen_hasSum_small {α β : ℂ} (hα : -1 < α.re) {x : ℝ} (hx : |x| ≤ 1) {z : ℂ}
    (hz : ‖z‖ < 1 / 10) :
    HasSum (fun n : ℕ => jacobiPolyP α β n x * z ^ n) (jacGenRhs α β x z) := by
  set a : ℂ := ((x : ℂ) + 1) / 2 with ha
  set b : ℂ := ((x : ℂ) - 1) / 2 with hb
  have hxn : ‖(x : ℂ)‖ ≤ 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  have hx' := abs_le.mp hx
  have ha1 : ‖a‖ ≤ 1 := by
    rw [ha, show ((x : ℂ) + 1) / 2 = (((x + 1) / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hb1 : ‖b‖ ≤ 1 := by
    rw [hb, show ((x : ℂ) - 1) / 2 = (((x - 1) / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  set u : ℂ := 1 - 2 * x * z + z ^ 2 with hu
  have huS : u ∈ slitPlane := jacGen_mem_slitPlane hx (by linarith)
  set R : ℂ := u ^ (1 / 2 : ℂ) with hR
  have hRre : 0 < R.re := DLMF.Hypergeometric.re_cpow_half_pos_of_mem_slitPlane huS
  have hR2 : R ^ 2 = u := DLMF.Hypergeometric.cpow_half_sq (slitPlane_ne_zero huS)
  have hzre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hxz : |(x * z.re)| ≤ 1 / 10 := by
    rw [abs_mul]; nlinarith [abs_nonneg x, abs_nonneg z.re]
  set c : ℂ := 1 - x * z with hc
  set D : ℂ := c + R with hD
  have hDre : 9 / 10 < D.re := by
    simp only [hD, hc, add_re, sub_re, one_re, mul_re, ofReal_re, ofReal_im, zero_mul,
      sub_zero]
    linarith [(abs_le.mp hxz).2]
  have hDn : 9 / 10 < ‖D‖ := hDre.trans_le (Complex.re_le_norm D)
  have hD0 : D ≠ 0 := fun h => by rw [h] at hDn; simp at hDn; linarith
  set w : ℂ := 2 * z / D with hw
  have hwn : ‖w‖ ≤ 2 / 9 := by
    rw [hw, norm_div, norm_mul, Complex.norm_ofNat, div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg z]
  have hroot : c * w - z * a * b * w ^ 2 - z = 0 := by
    rw [hw]; field_simp
    rw [hD, ha, hb, hc]
    linear_combination (-z) * hR2
  have hzn : ‖z‖ ≤ 1 / 10 := hz.le
  -- the hypotheses of the Lagrange–Bürmann formula
  have hball : ∀ t ∈ closedBall (0 : ℂ) (1 / 2), ‖t‖ ≤ 1 / 2 := fun t ht => by
    simpa using ht
  have hFd : DifferentiableOn ℂ (fun t => (1 + a * t) ^ α * (1 + b * t) ^ β)
      (closedBall 0 (1 / 2)) := by
    intro t ht
    have h1 : 1 + a * t ∈ slitPlane := Or.inl (jacGen_re_pos ha1 (hball t ht))
    have h2 : 1 + b * t ∈ slitPlane := Or.inl (jacGen_re_pos hb1 (hball t ht))
    exact ((DifferentiableAt.cpow (f := fun t => 1 + a * t) (by fun_prop)
      (differentiableAt_const _) h1).mul (DifferentiableAt.cpow (f := fun t => 1 + b * t)
      (by fun_prop) (differentiableAt_const _) h2)).differentiableWithinAt
  have hΦd : DifferentiableOn ℂ (fun t => (1 + a * t) * (1 + b * t)) (closedBall 0 (1 / 2)) :=
    by fun_prop
  have hgd : DifferentiableOn ℂ (fun t => c - z * a * b * (t + w)) (closedBall 0 (1 / 2)) :=
    by fun_prop
  have hcn : 9 / 10 ≤ ‖c‖ := by
    have h1 : ‖(x : ℂ) * z‖ ≤ 1 / 10 := by
      rw [norm_mul]; nlinarith [norm_nonneg z, norm_nonneg (x : ℂ)]
    have h2 := norm_sub_norm_le (1 : ℂ) ((x : ℂ) * z)
    rw [norm_one] at h2
    rw [hc]; linarith
  have hg0 : ∀ t ∈ closedBall (0 : ℂ) (1 / 2), c - z * a * b * (t + w) ≠ 0 :=
    fun t ht => jacGen_sub_ne_zero ha1 hb1 hzn hcn hwn (hball t ht)
  have hzΦ : ∀ t ∈ sphere (0 : ℂ) (1 / 2), ‖z * ((1 + a * t) * (1 + b * t))‖ ≤ 1 / 4 :=
    fun t ht => jacGen_norm_mul_le ha1 hb1 hzn (by simpa using ht)
  have hfac : ∀ t ∈ sphere (0 : ℂ) (1 / 2),
      t - z * ((1 + a * t) * (1 + b * t)) = (t - w) * (c - z * a * b * (t + w)) := by
    intro t _
    have hab : a + b = x := by rw [ha, hb]; ring
    linear_combination hroot
  have key := Complex.lagB_hasSum_iteratedDeriv (by norm_num : (0 : ℝ) < 1 / 2) hFd hΦd hgd hg0
    (by norm_num : (1 / 4 : ℝ) < 1 / 2) hzΦ (by linarith) hfac
  -- the coefficients
  have hcoef : ∀ n : ℕ, iteratedDeriv n (fun t => (1 + a * t) ^ α * (1 + b * t) ^ β *
      ((1 + a * t) * (1 + b * t)) ^ n) 0 / n ! = jacobiPolyP α β n x :=
    fun n => jacGen_coeff_eq_jacobiPolyP hα (x : ℂ) n
  simp only [hcoef] at key
  -- the value
  have hA : 0 < (1 + R - z).re := by
    simp only [sub_re, add_re, one_re]; linarith [(abs_le.mp hzre).2]
  have hB : 0 < (1 + R + z).re := by
    simp only [add_re, one_re]; linarith [(abs_le.mp hzre).1]
  have hA0 : 1 + R - z ≠ 0 := fun h => by rw [h] at hA; simp at hA
  have hB0 : 1 + R + z ≠ 0 := fun h => by rw [h] at hB; simp at hB
  have hR0 : R ≠ 0 := fun h => by rw [h] at hRre; simp at hRre
  have hgw : c - z * a * b * (w + w) = R := by
    rw [hw]; field_simp
    rw [hD, ha, hb, hc]
    linear_combination (-1 : ℂ) * hR2
  have h1 : 1 + a * w = 2 / (1 + R - z) := by
    rw [hw, eq_div_iff hA0]; field_simp
    rw [hD, ha, hc]
    linear_combination hR2
  have h2 : 1 + b * w = 2 / (1 + R + z) := by
    rw [hw, eq_div_iff hB0]; field_simp
    rw [hD, hb, hc]
    linear_combination hR2
  convert key using 1
  · funext n; ring
  · rw [hgw, h1, h2, jacGen_two_div_cpow α hA, jacGen_two_div_cpow β hB, jacGenRhs,
      cpow_add _ _ two_ne_zero, ← hu, ← hR]
    have hAα : (1 + R - z) ^ α ≠ 0 := fun h => hA0 ((cpow_eq_zero_iff _ _).mp h).1
    have hBβ : (1 + R + z) ^ β ≠ 0 := fun h => hB0 ((cpow_eq_zero_iff _ _).mp h).1
    field_simp

/-- The right side of 18.12.1 is holomorphic on the unit disc. -/
theorem jacGen_differentiableOn (α β : ℂ) {x : ℝ} (hx : |x| ≤ 1) :
    DifferentiableOn ℂ (jacGenRhs α β x) (ball 0 1) := by
  intro z hz
  have hz1 : ‖z‖ < 1 := by simpa using hz
  have huS := jacGen_mem_slitPlane hx hz1
  have hRre := DLMF.Hypergeometric.re_cpow_half_pos_of_mem_slitPlane huS
  have hzre := Complex.abs_re_le_norm z
  have hRd : DifferentiableAt ℂ (fun z : ℂ => (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ)) z :=
    DifferentiableAt.cpow (f := fun z : ℂ => 1 - 2 * x * z + z ^ 2) (by fun_prop)
      (differentiableAt_const _) huS
  set R := (1 - 2 * (x : ℂ) * z + z ^ 2) ^ (1 / 2 : ℂ) with hR
  have hA : 0 < (1 + R - z).re := by
    simp only [sub_re, add_re, one_re]; linarith [(abs_le.mp hzre).2]
  have hB : 0 < (1 + R + z).re := by
    simp only [add_re, one_re]; linarith [(abs_le.mp hzre).1]
  have hAd : DifferentiableAt ℂ (fun z : ℂ =>
      (1 + (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) - z) ^ α) z :=
    DifferentiableAt.cpow ((differentiableAt_const _).add hRd |>.sub differentiableAt_id)
      (differentiableAt_const _) (Or.inl hA)
  have hBd : DifferentiableAt ℂ (fun z : ℂ =>
      (1 + (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) + z) ^ β) z :=
    DifferentiableAt.cpow ((differentiableAt_const _).add hRd |>.add differentiableAt_id)
      (differentiableAt_const _) (Or.inl hB)
  have hA0 : 1 + R - z ≠ 0 := fun h => by rw [h] at hA; simp at hA
  have hB0 : 1 + R + z ≠ 0 := fun h => by rw [h] at hB; simp at hB
  have hR0 : R ≠ 0 := fun h => by rw [h] at hRre; simp at hRre
  have hAα : (1 + R - z) ^ α ≠ 0 := fun h => hA0 ((cpow_eq_zero_iff _ _).mp h).1
  have hBβ : (1 + R + z) ^ β ≠ 0 := fun h => hB0 ((cpow_eq_zero_iff _ _).mp h).1
  exact ((differentiableAt_const _).div ((hRd.mul hAd).mul hBd)
    (mul_ne_zero (mul_ne_zero hR0 hAα) hBβ)).differentiableWithinAt

end JacobiLagrange

/-- The series with terms `(fun n : ℕ => jacobiPolyP α β n x * z ^ n)` converges to `((2 : ℂ) ^ (α
+ β) / ((1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) * (1 + (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) -
z) ^ α * (1 + (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) + z) ^ β))`. -/
@[dlmf 18.12.E1]
theorem jacobi_generating_function {α β : ℂ} (hα : -1 < α.re) (hβ : -1 < β.re)
    {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => jacobiPolyP α β n x * z ^ n)
      ((2 : ℂ) ^ (α + β) / ((1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) *
        (1 + (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) - z) ^ α *
        (1 + (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) + z) ^ β)) := by
  have _hβ := hβ  -- 18.12.1 holds without a restriction on β
  exact Complex.lagB_hasSum_of_differentiableOn (c := fun n => jacobiPolyP α β n x)
    (by norm_num : (0 : ℝ) < 1 / 10) (jacGen_differentiableOn α β hx)
    (fun w hw => jacGen_hasSum_small hα hx (by simpa using hw)) (by simpa using hz)

/-- The series with terms `(fun n : ℕ => ultrasphPoly lam n x * z ^ n)` converges to `((1 - 2 * x
* z + z ^ 2) ^ (-lam))`. -/
@[dlmf 18.12.E4]
theorem ultrasphPoly_generating_function {lam : ℂ} (hlam : -1 / 2 < lam.re) {x : ℝ} (hx : |x| ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => ultrasphPoly lam n x * z ^ n) ((1 - 2 * x * z + z ^ 2) ^ (-lam)) := by
  have h := hasSum_coeff_gegenbauerSeries_mul_pow lam (Real.arccos x) hz
  rw [Real.cos_arccos (abs_le.mp hx).1 (abs_le.mp hx).2] at h
  refine h.congr_fun fun n => ?_
  rw [ofReal_eq_half_add_recip_of_abs_le_one hx,
    ultrasphPoly_eq_coeff_gegenbauerSeries hlam (Complex.exp_ne_zero _)]

/-- The series with terms `(fun n : ℕ => (n + 2 * lam) / (2 * lam) * ultrasphPoly lam n x * z ^
n)` converges to `((1 - x * z) / (1 - 2 * x * z + z ^ 2) ^ (lam + 1))`. -/
@[dlmf 18.12.E5]
theorem ultrasphPoly_weighted_generating_function {lam : ℂ} (hlam : -1 / 2 < lam.re)
    (hlam0 : lam ≠ 0)
    {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (n + 2 * lam) / (2 * lam) * ultrasphPoly lam n x * z ^ n)
      ((1 - x * z) / (1 - 2 * x * z + z ^ 2) ^ (lam + 1)) := by
  set w := exp (Real.arccos x * I)
  have hw : w ≠ 0 := Complex.exp_ne_zero _
  have hQ := hasSum_coeff_gegenbauerSeries_mul_pow (lam + 1) (Real.arccos x) hz
  rw [Real.cos_arccos (abs_le.mp hx).1 (abs_le.mp hx).2] at hQ
  have h := hasSum_coeff_one_sub_mul hQ ((w + w⁻¹) / 2)
  rw [← weightedGegenbauerSeries_eq hlam0 hw, ← ofReal_eq_half_add_recip_of_abs_le_one hx] at h
  rw [div_eq_mul_inv, ← Complex.cpow_neg]
  refine h.congr_fun fun n => ?_
  rw [coeff_weightedGegenbauerSeries hlam0, ofReal_eq_half_add_recip_of_abs_le_one hx,
    ultrasphPoly_eq_coeff_gegenbauerSeries hlam hw]

/-- Generating function of a sequence with constant-coefficient three-term recurrence. -/
theorem hasSum_of_three_term {a : ℕ → ℂ} {p q z : ℂ}
    (hrec : ∀ n, a (n + 2) = p * a (n + 1) + q * a n) (hs : Summable fun n => a n * z ^ n)
    (hD : 1 - p * z - q * z ^ 2 ≠ 0) :
    HasSum (fun n => a n * z ^ n) ((a 0 + (a 1 - p * a 0) * z) / (1 - p * z - q * z ^ 2)) := by
  set S := ∑' n, a n * z ^ n
  have h0 := hs.hasSum
  have h1 := (hasSum_nat_add_iff' 1).mpr h0
  have h2 := (hasSum_nat_add_iff' 2).mpr h0
  have h2' : HasSum (fun n => a (n + 2) * z ^ (n + 2))
      (p * z * (S - ∑ i ∈ Finset.range 1, a i * z ^ i) + q * z ^ 2 * S) := by
    have := (h1.mul_left (p * z)).add (h0.mul_left (q * z ^ 2))
    refine this.congr_fun fun n => ?_
    simp only [hrec]
    ring
  have heq := h2.unique h2'
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one,
    pow_one] at heq
  convert h0 using 1
  rw [div_eq_iff hD]
  linear_combination -heq

/-- `1 - 2xz + z²` does not vanish for `|x| ≤ 1` and `‖z‖ < 1`. -/
theorem one_sub_two_mul_add_sq_ne_zero {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    1 - 2 * x * z + z ^ 2 ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [sq] at hre him
  have hn : z.re ^ 2 + z.im ^ 2 < 1 := by
    have := Complex.sq_norm z
    rw [Complex.normSq_apply] at this
    nlinarith [norm_nonneg z]
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [abs_nonneg x, sq_abs x]
  rcases mul_eq_zero.mp (show z.im * (z.re - x) = 0 by linarith) with hb | ha
  · rw [hb] at hre hn
    nlinarith [sq_nonneg (z.re - x)]
  · have : z.re = x := by linarith
    rw [this] at hre hn
    nlinarith

/-- Chebyshev polynomials at a real point are real. -/
theorem chebyshevT_eval_ofReal (n : ℤ) (x : ℝ) :
    (Chebyshev.T ℂ n).eval (x : ℂ) = ((Chebyshev.T ℝ n).eval x : ℝ) := by
  rw [← Chebyshev.map_T (algebraMap ℝ ℂ), eval_map]
  exact eval₂_at_apply (algebraMap ℝ ℂ) x

/-- Chebyshev polynomials of the second kind at a real point are real. -/
theorem chebyshevU_eval_ofReal (n : ℤ) (x : ℝ) :
    (Chebyshev.U ℂ n).eval (x : ℂ) = ((Chebyshev.U ℝ n).eval x : ℝ) := by
  rw [← Chebyshev.map_U (algebraMap ℝ ℂ), eval_map]
  exact eval₂_at_apply (algebraMap ℝ ℂ) x

/-- `|Uₙ(x)| ≤ n + 1` on `[-1, 1]`. -/
theorem abs_eval_U_real_le {x : ℝ} (hx : |x| ≤ 1) (n : ℕ) :
    |(Chebyshev.U ℝ n).eval x| ≤ n + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := Chebyshev.U_eq_X_mul_U_add_T ℝ (n : ℤ)
    rw [show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring] at h
    rw [h, eval_add, eval_mul, eval_X]
    have hT := Chebyshev.abs_eval_T_real_le_one ((n + 1 : ℕ) : ℤ) hx
    calc |x * (Chebyshev.U ℝ n).eval x + (Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).eval x|
        ≤ |x| * |(Chebyshev.U ℝ n).eval x| + 1 := by
          rw [← abs_mul]; exact (abs_add_le _ _).trans (by linarith)
      _ ≤ 1 * (n + 1) + 1 := by gcongr
      _ = ((n + 1 : ℕ) : ℝ) + 1 := by push_cast; ring

/-- The series with terms `(fun n : ℕ => (Chebyshev.T ℂ n).eval (x : ℂ) * z ^ n)` converges to
`((1 - x * z) / (1 - 2 * x * z + z ^ 2))`. -/
@[dlmf 18.12.E8]
theorem chebyshevT_generating_function {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (Chebyshev.T ℂ n).eval (x : ℂ) * z ^ n) ((1 - x * z) / (1 - 2 * x * z + z ^ 2)) := by
  have hs : Summable fun n : ℕ => (Chebyshev.T ℂ n).eval (x : ℂ) * z ^ n := by
    refine Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg z) hz) fun n => ?_
    rw [norm_mul, norm_pow, chebyshevT_eval_ofReal, norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (by positivity) (Chebyshev.abs_eval_T_real_le_one _ hx)
  have h := hasSum_of_three_term (a := fun n : ℕ => (Chebyshev.T ℂ n).eval (x : ℂ))
    (p := 2 * x) (q := -1) (fun n => by
      have := Chebyshev.T_add_two ℂ (n : ℤ)
      rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by push_cast; ring,
        show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring, this]
      simp; ring) hs (by
        have := one_sub_two_mul_add_sq_ne_zero hx hz
        convert this using 1; ring)
  convert h using 2
  · simp; ring
  · ring

/-- `1 - z e^{iθ}` lies in the right half-plane for `‖z‖ < 1`. -/
theorem one_sub_mul_exp_re_pos {z : ℂ} (hz : ‖z‖ < 1) (θ : ℝ) :
    0 < (1 - z * exp (θ * I)).re := by
  have h : ‖z * exp (θ * I)‖ < 1 := by rw [norm_mul, norm_exp_ofReal_mul_I, mul_one]; exact hz
  have := Complex.re_le_norm (z * exp (θ * I))
  simp only [sub_re, one_re]
  linarith

/-- The series with terms `(fun n : ℕ => 2 * (Chebyshev.T ℂ (n + 1)).eval (x : ℂ) / (n + 1) * z ^
(n + 1))` converges to `(-log (1 - 2 * x * z + z ^ 2))`. -/
@[dlmf 18.12.E9]
theorem chebyshevT_log_generating_function {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => 2 * (Chebyshev.T ℂ (n + 1)).eval (x : ℂ) / (n + 1) * z ^ (n + 1))
      (-log (1 - 2 * x * z + z ^ 2)) := by
  set θ := Real.arccos x with hθ
  have hcos : Real.cos θ = x := Real.cos_arccos (abs_le.mp hx).1 (abs_le.mp hx).2
  set u := z * exp (θ * I) with hu
  set v := z * exp (-θ * I) with hv
  have hun : ‖u‖ < 1 := by rw [hu, norm_mul, norm_exp_ofReal_mul_I, mul_one]; exact hz
  have hvn : ‖v‖ < 1 := by
    rw [hv, norm_mul, show -(θ : ℂ) * I = ((-θ : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I, mul_one]; exact hz
  have h := (Complex.hasSum_taylorSeries_neg_log' hun).add (Complex.hasSum_taylorSeries_neg_log' hvn)
  have hprod : (1 - u) * (1 - v) = 1 - 2 * x * z + z ^ 2 := by
    rw [← hcos, ofReal_cos, Complex.cos, hu, hv]
    have : exp (θ * I) * exp (-θ * I) = 1 := by rw [← exp_add]; ring_nf; simp
    linear_combination z ^ 2 * this
  have hre1 : 0 < (1 - u).re := one_sub_mul_exp_re_pos hz θ
  have hre2 : 0 < (1 - v).re := by
    have := one_sub_mul_exp_re_pos hz (-θ); push_cast at this; exact this
  have harg1 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre1)
  have harg2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre2)
  have hne1 : 1 - u ≠ 0 := fun h => by rw [h] at hre1; simp at hre1
  have hne2 : 1 - v ≠ 0 := fun h => by rw [h] at hre2; simp at hre2
  have hlog : log ((1 - u) * (1 - v)) = log (1 - u) + log (1 - v) := by
    apply Complex.log_mul hne1 hne2
    constructor <;> linarith [abs_lt.mp harg1, abs_lt.mp harg2, Real.pi_pos]
  rw [← hprod, hlog, neg_add]
  refine h.congr_fun fun n => ?_
  have hT : (Chebyshev.T ℂ ((n + 1 : ℕ) : ℤ)).eval (x : ℂ) = cos ((n + 1 : ℕ) * (θ : ℂ)) := by
    rw [← hcos, ofReal_cos, Chebyshev.T_complex_cos]; push_cast; ring_nf
  push_cast at hT ⊢
  have e1 : exp (θ * I) ^ (n + 1) = exp (((n : ℂ) + 1) * θ * I) := by
    rw [← exp_nat_mul]; push_cast; ring_nf
  have e2 : exp (-θ * I) ^ (n + 1) = exp (-(((n : ℂ) + 1) * θ * I)) := by
    rw [← exp_nat_mul]; push_cast; ring_nf
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
  rw [hT, Complex.cos, hu, hv, mul_pow, mul_pow, e1, e2]
  field_simp

/-- The series with terms `(fun n : ℕ => (Chebyshev.U ℂ n).eval (x : ℂ) * z ^ n)` converges to
`((1 - 2 * x * z + z ^ 2)⁻¹)`. -/
@[dlmf 18.12.E10]
theorem chebyshevU_generating_function {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (Chebyshev.U ℂ n).eval (x : ℂ) * z ^ n) ((1 - 2 * x * z + z ^ 2)⁻¹) := by
  have hs : Summable fun n : ℕ => (Chebyshev.U ℂ n).eval (x : ℂ) * z ^ n := by
    refine Summable.of_norm_bounded (((summable_pow_mul_geometric_of_norm_lt_one 1
      (show ‖‖z‖‖ < 1 by simpa using hz)).add
      (summable_geometric_of_lt_one (norm_nonneg z) hz))) fun n => ?_
    rw [norm_mul, norm_pow, chebyshevU_eval_ofReal, norm_real, Real.norm_eq_abs, pow_one]
    have := abs_eval_U_real_le hx n
    nlinarith [pow_nonneg (norm_nonneg z) n]
  have h := hasSum_of_three_term (a := fun n : ℕ => (Chebyshev.U ℂ n).eval (x : ℂ))
    (p := 2 * x) (q := -1) (fun n => by
      have := Chebyshev.U_add_two ℂ (n : ℤ)
      rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by push_cast; ring,
        show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring, this]
      simp; ring) hs (by
        have := one_sub_two_mul_add_sq_ne_zero hx hz
        convert this using 1; ring)
  convert h using 2
  simp

/-- The series with terms `(fun n : ℕ => legendrePolyP n x * z ^ n)` converges to `((1 - 2 * x * z
+ z ^ 2) ^ (-1 / 2 : ℂ))`. -/
@[dlmf 18.12.E11]
theorem legendre_generating_function {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => legendrePolyP n x * z ^ n) ((1 - 2 * x * z + z ^ 2) ^ (-1 / 2 : ℂ)) := by
  simp_rw [legendre_eq_ultrasphPoly]
  rw [show (-1 / 2 : ℂ) = -(1 / 2) by ring]
  exact ultrasphPoly_generating_function (by norm_num) hx hz

/-- The series with terms `(fun n : ℕ => aeval x (hermite n) / (n.factorial : ℂ) * z ^ n)`
converges to `(exp (x * z - z ^ 2 / 2))`. -/
@[dlmf 18.12.E16]
theorem hermite_generating_function (x z : ℂ) :
    HasSum (fun n : ℕ => aeval x (hermite n) / (n.factorial : ℂ) * z ^ n)
      (exp (x * z - z ^ 2 / 2)) := by
  have hf : Differentiable ℂ (fun y : ℂ => exp (-(y ^ 2 / 2))) := by fun_prop
  have hne : exp (-(x ^ 2 / 2)) ≠ 0 := exp_ne_zero _
  have hderiv (n : ℕ) (y : ℂ) :
      iteratedDeriv n (fun t : ℂ => exp (-(t ^ 2 / 2))) y =
        (-1 : ℂ) ^ n * (aeval y (hermite n) : ℂ) * exp (-(y ^ 2 / 2)) := by
    rw [iteratedDeriv_eq_iterate, mul_assoc]
    induction n generalizing y with
    | zero => simp [hermite_zero]
    | succ n ih =>
      replace ih : deriv^[n] _ = _ := funext ih
      have hgaussian : deriv (fun t : ℂ => exp (-(t ^ 2 / 2))) y =
          -y * exp (-(y ^ 2 / 2)) := by
        rw [deriv_cexp (by fun_prop)]
        simp [pow_two]
        ring
      rw [Function.iterate_succ_apply', ih, deriv_const_mul_field, deriv_fun_mul,
        pow_succ, hgaussian, hermite_succ, map_sub, map_mul, aeval_X,
        Polynomial.deriv_aeval]
      · ring
      · apply Polynomial.differentiable_aeval
      · fun_prop
  have hs := Complex.hasSum_taylorSeries_of_entire (E := ℂ) hf x (x - z)
  have hterm : (fun n : ℕ =>
      (n ! : ℂ)⁻¹ • ((x - z) - x) ^ n •
        iteratedDeriv n (fun y : ℂ => exp (-(y ^ 2 / 2))) x) =
      fun n => (aeval x (hermite n) : ℂ) * z ^ n / n ! * exp (-(x ^ 2 / 2)) := by
    funext n
    simp only [sub_sub_cancel_left, smul_eq_mul]
    rw [hderiv, neg_pow]
    ring_nf
    rw [mul_comm n 2, pow_mul, neg_one_sq, one_pow]
    ring
  rw [hterm] at hs
  have hs' := hs.mul_right (exp (-(x ^ 2 / 2)))⁻¹
  have hsimp : (fun n : ℕ =>
      (aeval x (hermite n) : ℂ) * z ^ n / n ! * exp (-(x ^ 2 / 2)) *
        (exp (-(x ^ 2 / 2)))⁻¹) =
      fun n => (aeval x (hermite n) : ℂ) * z ^ n / n ! := by
    funext n
    field [hne]
  rw [hsimp] at hs'
  have hval : exp (-((x - z) ^ 2 / 2)) * (exp (-(x ^ 2 / 2)))⁻¹ =
      exp (x * z - z ^ 2 / 2) := by
    rw [← div_eq_mul_inv, div_eq_iff hne, ← exp_add]
    congr 1
    ring
  rw [hval] at hs'
  convert hs' using 1
  funext n
  ring

/-- The exponential generating function with an arbitrary starting degree. -/
theorem hasSum_hermitePolyH_shifted (m : ℕ) (x t : ℂ) :
    HasSum (fun n : ℕ => (aeval x (hermitePolyH (m + n)) : ℂ) * t ^ n / n !)
      ((aeval (x - t) (hermitePolyH m) : ℂ) * exp (2 * x * t - t ^ 2)) := by
  have hderiv (n : ℕ) (y : ℂ) :
      iteratedDeriv n (fun v : ℂ => (aeval v (hermitePolyH m) : ℂ) * exp (-(v ^ 2))) y =
        (-1 : ℂ) ^ n * (aeval y (hermitePolyH (m + n)) : ℂ) * exp (-(y ^ 2)) := by
    rw [iteratedDeriv_eq_iterate, mul_assoc]
    induction n generalizing y with
    | zero => simp
    | succ n ih =>
      replace ih := funext ih
      have hg : deriv (fun v : ℂ => exp (-(v ^ 2))) y = -(2 * y) * exp (-(y ^ 2)) := by
        rw [deriv_cexp (by fun_prop)]
        simp [pow_two]; ring
      rw [Function.iterate_succ_apply', ih, deriv_const_mul_field, deriv_fun_mul,
        pow_succ, hg, show m + (n + 1) = (m + n) + 1 by omega, hermitePolyH_succ,
        map_sub, map_mul, map_mul, map_ofNat, aeval_X, Polynomial.deriv_aeval]
      · ring
      · apply Polynomial.differentiable_aeval
      · fun_prop
  have hf : Differentiable ℂ (fun y : ℂ => (aeval y (hermitePolyH m) : ℂ) * exp (-(y ^ 2))) := by
    apply Differentiable.mul
    · apply Polynomial.differentiable_aeval
    · fun_prop
  have hne : exp (-(x ^ 2)) ≠ 0 := exp_ne_zero _
  have hs := Complex.hasSum_taylorSeries_of_entire (E := ℂ) hf x (x - t)
  have hterm : (fun n : ℕ =>
      (n ! : ℂ)⁻¹ • ((x - t) - x) ^ n •
        iteratedDeriv n (fun y : ℂ => (aeval y (hermitePolyH m) : ℂ) * exp (-(y ^ 2))) x) =
      fun n => (aeval x (hermitePolyH (m + n)) : ℂ) * t ^ n / n ! * exp (-(x ^ 2)) := by
    funext n
    simp only [sub_sub_cancel_left, smul_eq_mul]
    rw [hderiv, neg_pow]
    ring_nf
    rw [mul_comm n 2, pow_mul, neg_one_sq, one_pow]
    ring
  rw [hterm] at hs
  have hs' := hs.mul_right (exp (-(x ^ 2)))⁻¹
  have hsimp : (fun n : ℕ =>
      (aeval x (hermitePolyH (m + n)) : ℂ) * t ^ n / n ! * exp (-(x ^ 2)) *
        (exp (-(x ^ 2)))⁻¹) =
      fun n => (aeval x (hermitePolyH (m + n)) : ℂ) * t ^ n / n ! := by
    funext n
    field [hne]
  rw [hsimp] at hs'
  have hval : exp (-((x - t) ^ 2)) * (exp (-(x ^ 2)))⁻¹ =
      exp (2 * x * t - t ^ 2) := by
    rw [← div_eq_mul_inv, div_eq_iff hne, ← exp_add]
    congr 1
    ring
  simpa only [mul_assoc, hval] using hs'

/-- Translation of a Hermite polynomial by an arbitrary complex number. -/
theorem hermitePolyH_translation (m : ℕ) (x y : ℂ) :
    (aeval (x + y) (hermitePolyH m) : ℂ) =
      ∑ k ∈ Finset.range (m + 1), (m.choose k : ℂ) * (2 * y) ^ k *
        aeval x (hermitePolyH (m - k)) := by
  have hc := Complex.powerSeries_coefficients_unique
    (c := fun n => (aeval (x + y) (hermitePolyH n) : ℂ) / n !)
    (d := fun n => ∑ k ∈ Finset.range (n + 1),
      ((2 * y) ^ k / k !) * ((aeval x (hermitePolyH (n - k)) : ℂ) / (n - k)!))
    (f := fun z => exp (2 * (x + y) * z - z ^ 2))
    (fun z _ => (hasSum_hermitePolyH_generating_function _ z).congr_fun (by intro n; ring))
    (fun z _ => by
      have he : HasSum (fun k : ℕ => ((2 * y) ^ k / k !) * z ^ k) (exp (2 * y * z)) := by
        convert NormedSpace.expSeries_div_hasSum_exp (2 * y * z) using 1
        · funext k; rw [mul_pow]; ring
        · simp only [Complex.exp_eq_exp_ℂ]
      have hh : HasSum (fun k => ((aeval x (hermitePolyH k) : ℂ) / k !) * z ^ k)
          (exp (2 * x * z - z ^ 2)) :=
        (hasSum_hermitePolyH_generating_function x z).congr_fun (by intro k; ring)
      convert hasSum_scalar_convolution he hh using 1
      rw [← exp_add]; congr 1; ring)
  have h := congrArg (fun c : ℕ → ℂ => c m * m !) hc
  rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr m.factorial_ne_zero), Finset.sum_mul] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro k hk
  have he : (m.choose k : ℂ) * k ! * (m - k)! = m ! := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by simpa using Finset.mem_range.mp hk)
  rw [← he]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m - k))]

/-- The probabilists' Hermite polynomial as a finite monomial sum. -/
theorem hermite_finite_sum (n : ℕ) (x : ℂ) :
    (aeval x (hermite n) : ℂ) = ∑ k ∈ Finset.range (n / 2 + 1),
      (-1 : ℂ) ^ k * n.factorial /
        (2 ^ k * (k.factorial : ℂ) * (n - 2 * k).factorial) * x ^ (n - 2 * k) := by
  have hc := Complex.powerSeries_coefficients_unique
    (c := fun j => (aeval x (hermite j) : ℂ) / j !)
    (d := fun j => ∑ k ∈ Finset.range (j / 2 + 1),
      (-1 / 2 : ℂ) ^ k / k ! * (x ^ (j - 2 * k) / (j - 2 * k)!))
    (f := fun z => exp (x * z - z ^ 2 / 2))
    (fun z _ => hermite_generating_function x z)
    (fun z _ => by
      have he : HasSum (fun j : ℕ => (x ^ j / j !) * z ^ j) (exp (x * z)) := by
        convert NormedSpace.expSeries_div_hasSum_exp (x * z) using 1
        · funext j; rw [mul_pow]; ring
        · simp only [Complex.exp_eq_exp_ℂ]
      have h := hasSum_scalar_convolution (hasSum_exp_quadratic (-1 / 2) z) he
      rw [← exp_add, show (-1 / 2 : ℂ) * z ^ 2 + x * z = x * z - z ^ 2 / 2 by ring] at h
      convert h using 1
      funext j
      congr 1
      simp_rw [ite_mul, zero_mul]
      rw [sum_even_range]
      simp)
  have h := congrArg (fun c : ℕ → ℂ => c n * n !) hc
  rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr n.factorial_ne_zero), Finset.sum_mul] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro k _
  rw [div_pow]
  ring

/-- Formula under the stated hypotheses: `laguerreExtended (α + β + 1) n (x + y) = ∑ k ∈
Finset.range (n + 1), laguerreExtended α k x * laguerreExtended β (n - k) y`. -/
@[dlmf 18.18.E10, dlmf 18.18.E38]
theorem laguerrePolyL_addition (α β x y : ℂ) (n : ℕ) :
    laguerreExtended (α + β + 1) n (x + y) =
      ∑ k ∈ Finset.range (n + 1), laguerreExtended α k x * laguerreExtended β (n - k) y := by
  have hdiffL : ∀ β : ℂ, Differentiable ℂ fun α : ℂ => laguerreExtended (α + β + 1) n (x + y) :=
    fun β => (differentiable_laguerreExtended n (x + y)).comp
      ((differentiable_id.add_const _).add_const _)
  have hstep : ∀ β : ℂ, -1 < β.re → ∀ α : ℂ, laguerreExtended (α + β + 1) n (x + y) =
      ∑ k ∈ Finset.range (n + 1), laguerreExtended α k x * laguerreExtended β (n - k) y := by
    intro β hβ
    refine eq_of_differentiable_of_re_gt (hdiffL β) ?_
      fun α hα => laguerrePolyL_addition_of_re hα hβ x y n
    exact Differentiable.fun_sum fun k _ =>
      (differentiable_laguerreExtended k x).mul (differentiable_const _)
  refine eq_of_differentiable_of_re_gt (f := fun β => laguerreExtended (α + β + 1) n (x + y))
    (g := fun β => ∑ k ∈ Finset.range (n + 1), laguerreExtended α k x *
      laguerreExtended β (n - k) y) ?_ ?_ (fun β hβ => hstep β hβ α) β
  · exact (differentiable_laguerreExtended n (x + y)).comp
      ((differentiable_const _).add differentiable_id |>.add_const _)
  · exact Differentiable.fun_sum fun k _ =>
      (differentiable_const _).mul (differentiable_laguerreExtended (n - k) y)

/-- Formula under the stated hypotheses: `(aeval (a * x + b * y) (hermitePolyH n) : ℝ) = ∑ k ∈
Finset.range (n + 1), (n.choose k : ℝ) * a ^ k * b ^ (n - k) * aeval x (hermitePolyH k) *
aeval y (hermitePolyH (n - k))`. -/
@[dlmf 18.18.E11, dlmf 18.18.E39]
theorem hermitePolyH_addition (a b x y : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (n : ℕ) :
    (aeval (a * x + b * y) (hermitePolyH n) : ℝ) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * a ^ k * b ^ (n - k) *
        aeval x (hermitePolyH k) * aeval y (hermitePolyH (n - k)) := by
  have hab' : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 = 1 := by exact_mod_cast hab
  have hcoeff := Complex.powerSeries_coefficients_unique
    (c := fun n => (aeval ((a : ℂ) * x + b * y) (hermitePolyH n) : ℂ) / n !)
    (d := fun n => ∑ k ∈ Finset.range (n + 1),
      ((aeval (x : ℂ) (hermitePolyH k) : ℂ) / k ! * (a : ℂ) ^ k) *
      ((aeval (y : ℂ) (hermitePolyH (n - k)) : ℂ) / (n - k) ! * (b : ℂ) ^ (n - k)))
    (f := fun z => exp (2 * ((a : ℂ) * x + b * y) * z - z ^ 2))
    (fun z _ => (hasSum_hermitePolyH_generating_function _ z).congr_fun (by intro k; ring))
    (fun z _ => ?_)
  · have h := congrArg (fun c : ℕ → ℂ => c n * n !) hcoeff
    rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr n.factorial_ne_zero), Finset.sum_mul] at h
    have ht (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
        ((aeval (x : ℂ) (hermitePolyH k) : ℂ) / k ! * (a : ℂ) ^ k *
          ((aeval (y : ℂ) (hermitePolyH (n - k)) : ℂ) / (n - k) ! * (b : ℂ) ^ (n - k))) * n ! =
        (n.choose k : ℂ) * a ^ k * b ^ (n - k) *
          aeval (x : ℂ) (hermitePolyH k) * aeval (y : ℂ) (hermitePolyH (n - k)) := by
      have he : (n.choose k : ℂ) * k ! * (n - k) ! = n ! := by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by simpa using Finset.mem_range.mp hk)
      rw [← he]
      field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k),
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - k))]
    rw [Finset.sum_congr rfl ht] at h
    have castH (t : ℝ) (j : ℕ) :
        (aeval (t : ℂ) (hermitePolyH j) : ℂ) = ((aeval t (hermitePolyH j) : ℝ) : ℂ) :=
      aeval_algHom_apply (IsScalarTower.toAlgHom ℤ ℝ ℂ) t (hermitePolyH j)
    rw [show (a : ℂ) * x + b * y = ((a * x + b * y : ℝ) : ℂ) by push_cast; rfl] at h
    simp_rw [castH] at h
    exact_mod_cast h
  · have h1 : HasSum (fun k => ((aeval (x : ℂ) (hermitePolyH k) : ℂ) / k ! *
        (a : ℂ) ^ k) * z ^ k) (exp (2 * x * (a * z) - (a * z) ^ 2)) := by
      convert hasSum_hermitePolyH_generating_function (x : ℂ) (a * z) using 1
      funext k; rw [mul_pow]; ring
    have h2 : HasSum (fun k => ((aeval (y : ℂ) (hermitePolyH k) : ℂ) / k ! *
        (b : ℂ) ^ k) * z ^ k) (exp (2 * y * (b * z) - (b * z) ^ 2)) := by
      convert hasSum_hermitePolyH_generating_function (y : ℂ) (b * z) using 1
      funext k; rw [mul_pow]; ring
    convert hasSum_scalar_convolution h1 h2 using 1
    rw [← exp_add]
    congr 1
    linear_combination z ^ 2 * hab'

/-- Formula under the stated hypotheses: `laguerrePolyL α n (lam * x) / laguerrePolyL α n 0 = ∑ k
∈ Finset.range (n + 1), (n.choose k : ℂ) * lam ^ k * (1 - lam) ^ (n - k) * laguerrePolyL α k x
/ laguerrePolyL α k 0`. -/
@[dlmf 18.18.E12]
theorem laguerrePolyL_multiplication {α : ℂ} (hα : -1 < α.re) (lam x : ℂ) (n : ℕ) :
    laguerrePolyL α n (lam * x) / laguerrePolyL α n 0 = ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℂ) * lam ^ k * (1 - lam) ^ (n - k) * laguerrePolyL α k x
          / laguerrePolyL α k 0 := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by simp; linarith)
  have hpk : ∀ k, poch (α + 1) k ≠ 0 := poch_ne_zero_of_not_neg_nat hc
  have hL : ∀ m ≤ n, ∀ y, laguerrePolyL α m y / laguerrePolyL α m 0 =
      ∑ j ∈ Finset.range (n + 1), poch (-(m : ℂ)) j / (poch (α + 1) j * j !) * y ^ j := by
    intro m hm y
    have hp : poch (α + 1) m / m ! ≠ 0 :=
      div_ne_zero (hpk m) (Nat.cast_ne_zero.mpr m.factorial_ne_zero)
    unfold laguerrePolyL
    rw [kummerM_zero, mul_one, mul_div_cancel_left₀ _ hp, kummerM_eq_sum_neg_nat]
    refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun j _ hj => ?_
    rw [poch_neg_nat_eq_zero (by simpa using hj)]; simp
  rw [hL n le_rfl]
  simp_rw [mul_div_assoc _ (laguerrePolyL α _ x)]
  conv_rhs => rw [Finset.sum_congr rfl fun k hk => by
    rw [hL k (by simpa [Nat.lt_succ_iff] using hk) x]]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := by simp at hj; omega
  have hb := sum_choose_mul_poch_neg_nat_mul_pow hjn lam (1 - lam)
  rw [add_sub_cancel, one_pow, mul_one] at hb
  rw [Finset.sum_congr rfl (g := fun k => (n.choose k : ℂ) * poch (-(k : ℂ)) j * lam ^ k *
    (1 - lam) ^ (n - k) * (x ^ j / (poch (α + 1) j * j !))) (fun k _ => by ring),
    ← Finset.sum_mul, hb, mul_pow]
  ring

/-- Formula under the stated hypotheses: `aeval (lam * x) (hermitePolyH n) = ∑ k ∈ Finset.range (n
/ 2 + 1), poch (-(n : ℂ)) (2 * k) / k.factorial * lam ^ (n - 2 * k) * (lam ^ 2 - 1) ^ k *
aeval x (hermitePolyH (n - 2 * k))`. -/
@[dlmf 18.18.E13]
theorem hermitePolyH_multiplication (lam x : ℂ) (n : ℕ) :
    aeval (lam * x) (hermitePolyH n) = ∑ k ∈ Finset.range (n / 2 + 1),
      poch (-(n : ℂ)) (2 * k) / k.factorial * lam ^ (n - 2 * k) * (lam ^ 2 - 1) ^ k *
        aeval x (hermitePolyH (n - 2 * k)) := by
  have hc := Complex.powerSeries_coefficients_unique
    (c := fun j => (aeval (lam * x) (hermitePolyH j) : ℂ) / j !)
    (d := fun j => ∑ k ∈ Finset.range (j / 2 + 1),
      (lam ^ 2 - 1) ^ k / k ! *
        ((aeval x (hermitePolyH (j - 2 * k)) : ℂ) / (j - 2 * k)! * lam ^ (j - 2 * k)))
    (f := fun z => exp (2 * (lam * x) * z - z ^ 2))
    (fun z _ => (hasSum_hermitePolyH_generating_function _ z).congr_fun (by intro j; ring))
    (fun z _ => by
      convert hasSum_exp_quadratic_mul_hermite (lam ^ 2 - 1) lam x z using 1
      congr 1; ring)
  have h := congrArg (fun c : ℕ → ℂ => c n * n !) hc
  rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr n.factorial_ne_zero), Finset.sum_mul] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : 2 * k ≤ n := by have := Finset.mem_range.mp hk; omega
  rw [← poch_neg_nat_even_mul_factorial hk']
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - 2 * k))]

end DLMF.OrthogonalPolynomials
end
end
