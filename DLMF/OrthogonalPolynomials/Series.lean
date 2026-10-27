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
# Generating functions, connection formulas, and linearization

Statements from NIST DLMF Chapter 18, each tagged with its equation number by `@[dlmf]`.
Jacobi and Gegenbauer statements retain regularity hypotheses because the project's
hypergeometric definitions do not implement continuation in singular parameters.
The adjacent Jacobi generating function combines the local parameter-raising relation
with Mathlib’s shifted-series API and the proved Gegenbauer generating function.
The finite Gegenbauer proofs combine the local explicit sums and recurrence with
the Mathlib contributors’ finite-sum, factorial, binomial and polynomial APIs.

The Jacobi generating function 18.12.1 (`jacobi_generating_function`) follows from the
coefficient form of the Lagrange–Bürmann formula (`Complex.lagB_hasSum_iteratedDeriv`):
`P_n^{(α,β)}(x) = [tⁿ] F(t) φ(t)ⁿ` with `φ(t) = (1 + (x+1)t/2)(1 + (x-1)t/2)` and
`F(t) = (1 + (x+1)t/2)^α (1 + (x-1)t/2)^β` (by 18.5.8), the root of `t = z φ(t)` being
`w = 2z/(1 - xz + R)`, `R = (1 - 2xz + z²)^{1/2}`. This gives the identity for small `|z|`;
it extends to `|z| < 1` because the right side is holomorphic there
(`Complex.lagB_hasSum_of_differentiableOn`). The weighted form 18.12.3
(`jacobi_weighted_generating_function`) is proved for small `|z|` by summing an absolutely
convergent double series in two ways, and then on the star-shaped domain
`{|z| < 1, |2(x+1)z/(1+z)²| < 1}` by the identity theorem, the left side having radius of
convergence at least `1` by 18.12.1.

Brafman's generating function 18.12.2_5 (`jacobi_brafman_generating_function`) follows from
Bailey's product formula for Appell's `F₄` (`DLMF.Hypergeometric.appF4_bailey`): with
`U = (1 - R - z)/2`, `V = (1 - R + z)/2` one has `U(1 - V) = (x-1)z/2`, `V(1 - U) = (x+1)z/2`,
and the antidiagonal sums of `F₄((x-1)z/2, (x+1)z/2)` are the Jacobi terms by 18.5.8. The
bound `|U|², |V|² ≤ |z|` on the unit disc (`jacB_norm_sq_le`, from `Re(R conj(1 ∓ z)) > 0`
by a connectedness argument) makes the right side holomorphic there, so the hypotheses
`|U|, |V| < 1` of the statement are redundant.
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
  have hg0 : ∀ t ∈ closedBall (0 : ℂ) (1 / 2), c - z * a * b * (t + w) ≠ 0 := by
    intro t ht h
    have htn := hball t ht
    have h1 : ‖z * a * b * (t + w)‖ ≤ 1 / 10 := by
      rw [norm_mul, norm_mul, norm_mul]
      have : ‖t + w‖ ≤ 1 := (norm_add_le _ _).trans (by linarith)
      calc ‖z‖ * ‖a‖ * ‖b‖ * ‖t + w‖ ≤ (1 / 10) * 1 * 1 * 1 := by gcongr
        _ = 1 / 10 := by norm_num
    rw [sub_eq_zero] at h
    rw [h] at hcn
    linarith
  have hzΦ : ∀ t ∈ sphere (0 : ℂ) (1 / 2), ‖z * ((1 + a * t) * (1 + b * t))‖ ≤ 1 / 4 := by
    intro t ht
    have htn : ‖t‖ = 1 / 2 := by simpa using ht
    have h1 : ‖1 + a * t‖ ≤ 3 / 2 := (norm_add_le _ _).trans (by
      rw [norm_one, norm_mul, htn]; nlinarith)
    have h2 : ‖1 + b * t‖ ≤ 3 / 2 := (norm_add_le _ _).trans (by
      rw [norm_one, norm_mul, htn]; nlinarith)
    rw [norm_mul, norm_mul]
    calc ‖z‖ * (‖1 + a * t‖ * ‖1 + b * t‖) ≤ (1 / 10) * ((3 / 2) * (3 / 2)) := by gcongr
      _ ≤ 1 / 4 := by norm_num
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

@[dlmf 18.12.E4]
theorem ultrasphPoly_generating_function {lam : ℂ} (hlam : -1 / 2 < lam.re) {x : ℝ} (hx : |x| ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => ultrasphPoly lam n x * z ^ n) ((1 - 2 * x * z + z ^ 2) ^ (-lam)) := by
  have h := hasSum_coeff_gegenbauerSeries_mul_pow lam (Real.arccos x) hz
  rw [Real.cos_arccos (abs_le.mp hx).1 (abs_le.mp hx).2] at h
  refine h.congr_fun fun n => ?_
  rw [ofReal_eq_half_add_recip_of_abs_le_one hx,
    ultrasphPoly_eq_coeff_gegenbauerSeries hlam (Complex.exp_ne_zero _)]

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

@[dlmf 18.12.E11]
theorem legendre_generating_function {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => legendrePolyP n x * z ^ n) ((1 - 2 * x * z + z ^ 2) ^ (-1 / 2 : ℂ)) := by
  simp_rw [legendre_eq_ultrasphPoly]
  rw [show (-1 / 2 : ℂ) = -(1 / 2) by ring]
  exact ultrasphPoly_generating_function (by norm_num) hx hz

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
  have hc := scalarSeries_unique
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
  have hc := scalarSeries_unique
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

@[dlmf 18.18.E11, dlmf 18.18.E39]
theorem hermitePolyH_addition (a b x y : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (n : ℕ) :
    (aeval (a * x + b * y) (hermitePolyH n) : ℝ) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * a ^ k * b ^ (n - k) *
        aeval x (hermitePolyH k) * aeval y (hermitePolyH (n - k)) := by
  have hab' : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 = 1 := by exact_mod_cast hab
  have hcoeff := scalarSeries_unique
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

@[dlmf 18.18.E13]
theorem hermitePolyH_multiplication (lam x : ℂ) (n : ℕ) :
    aeval (lam * x) (hermitePolyH n) = ∑ k ∈ Finset.range (n / 2 + 1),
      poch (-(n : ℂ)) (2 * k) / k.factorial * lam ^ (n - 2 * k) * (lam ^ 2 - 1) ^ k *
        aeval x (hermitePolyH (n - 2 * k)) := by
  have hc := scalarSeries_unique
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

@[dlmf 18.18.E17]
theorem monomial_ultrasphPoly_expansion {lam : ℂ} (hlam : 0 < lam.re) (n : ℕ) (x : ℂ) :
    (2 * x) ^ n = n.factorial * ∑ k ∈ Finset.range (n / 2 + 1),
      (lam + n - 2 * k) / lam / (poch (lam + 1) (n - k) * k.factorial)
          * ultrasphPoly lam (n - 2 * k) x := by
  have hl : lam ≠ 0 := by intro he; simp [he] at hlam
  have hp (r : ℕ) : poch lam r ≠ 0 := poch_ne_zero_of_re_pos hlam r
  have hp1 (r : ℕ) : poch (lam + 1) r ≠ 0 := poch_ne_zero_of_re_pos (by simp; linarith) r
  have hf (r : ℕ) : (r.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr r.factorial_ne_zero
  let F : ℕ → ℕ → ℂ := fun k j =>
    (lam + n - 2 * k) / lam / (poch (lam + 1) (n - k) * k.factorial) *
      ((-1 : ℂ) ^ j * poch lam (n - 2 * k - j) /
        ((j.factorial : ℂ) * (n - 2 * k - 2 * j).factorial) * (2 * x) ^ (n - 2 * k - 2 * j))
  have hexpand : (∑ k ∈ Finset.range (n / 2 + 1),
      (lam + n - 2 * k) / lam / (poch (lam + 1) (n - k) * k.factorial) *
        ultrasphPoly lam (n - 2 * k) x) =
      ∑ k ∈ Finset.range (n / 2 + 1), ∑ j ∈ Finset.range (n / 2 - k + 1), F k j := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : 2 * k ≤ n := by have := Finset.mem_range.mp hk; omega
    rw [ultrasphPoly_finite_sum (by linarith : -1 / 2 < lam.re), Finset.mul_sum,
      show (n - 2 * k) / 2 = n / 2 - k by omega]
  have hterm {r k : ℕ} (hr : 2 * r ≤ n) (hk : k ≤ r) :
      F (r - k) k = (2 * x) ^ (n - 2 * r) / ((r.factorial : ℂ) * (n - 2 * r).factorial) *
        ((-1 : ℂ) ^ k * (r.choose k : ℂ) * ((lam + (n - 2 * r : ℕ)) + 2 * k) /
          poch ((lam + (n - 2 * r : ℕ)) + k) (r + 1)) := by
    have hidx1 : n - (r - k) = n - r + k := by omega
    have hidx2 : n - 2 * (r - k) - k = n - 2 * r + k := by omega
    have hidx3 : n - 2 * (r - k) - 2 * k = n - 2 * r := by omega
    have hcast : lam + n - 2 * ((r - k : ℕ) : ℂ) = lam + ((n - 2 * r : ℕ) : ℂ) + 2 * k := by
      rw [Nat.cast_sub hk, Nat.cast_sub hr, Nat.cast_mul, Nat.cast_ofNat]
      ring
    have hrel : poch (lam + 1) (n - r + k) =
        poch lam (n - 2 * r + k) * poch (lam + (n - 2 * r : ℕ) + k) (r + 1) / lam := by
      rw [eq_div_iff hl]
      have he := poch_add lam (n - 2 * r + k) (r + 1)
      rw [show n - 2 * r + k + (r + 1) = (n - r + k) + 1 by omega,
        poch_succ_left] at he
      push_cast at he
      simp only [← add_assoc] at he
      linear_combination he
    have hpa : poch (lam + (n - 2 * r : ℕ) + k) (r + 1) ≠ 0 :=
      poch_ne_zero_of_re_pos (by simp only [add_re, natCast_re]; positivity) _
    dsimp only [F]
    rw [hidx1, hidx2, hidx3, hcast, hrel, Nat.cast_choose ℂ hk]
    field_simp [hl, hp, hpa, hf]
  have hs (r : ℕ) (hr : r ∈ Finset.range (n / 2 + 1)) :
      (∑ k ∈ Finset.range (r + 1), F k (r - k)) =
        if r = 0 then (2 * x) ^ n / n.factorial else 0 := by
    have hrn : 2 * r ≤ n := by have := Finset.mem_range.mp hr; omega
    have ha : 0 < (lam + (n - 2 * r : ℕ)).re := by
      simp only [add_re, natCast_re]
      linarith [Nat.cast_nonneg (α := ℝ) (n - 2 * r)]
    conv_lhs => rw [← Finset.sum_range_reflect]
    have hh : (∑ k ∈ Finset.range (r + 1), F (r + 1 - 1 - k) (r - (r + 1 - 1 - k))) =
        (2 * x) ^ (n - 2 * r) / ((r.factorial : ℂ) * (n - 2 * r).factorial) *
          ∑ k ∈ Finset.range (r + 1), (-1 : ℂ) ^ k * (r.choose k : ℂ) *
            ((lam + (n - 2 * r : ℕ)) + 2 * k) / poch ((lam + (n - 2 * r : ℕ)) + k) (r + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hkr : k ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      rw [show r + 1 - 1 - k = r - k by omega, Nat.sub_sub_self hkr]
      exact hterm hrn hkr
    rw [hh, sum_choose_weighted_recip_poch_eq ha]
    split_ifs with he
    · subst r; simp
    · simp
  rw [hexpand, sum_triangle_by_total_degree, Finset.sum_congr rfl hs,
    Finset.sum_eq_single 0]
  · simp only [ite_true]
    field_simp [hf]
  · intro r hr hr0
    simp [hr0]
  · simp

@[dlmf 18.18.E16]
theorem ultrasphPoly_connection {lam μ : ℂ} (hlam : 0 < lam.re) (hμ : -1 / 2 < μ.re) (n : ℕ)
    (x : ℂ) :
    ultrasphPoly μ n x = ∑ k ∈ Finset.range (n / 2 + 1),
      (lam + n - 2 * k) / lam * poch μ (n - k) / poch (lam + 1) (n - k) *
      (poch (μ - lam) k / k.factorial) * ultrasphPoly lam (n - 2 * k) x := by
  have hl : lam ≠ 0 := by intro he; simp [he] at hlam
  have hp (r : ℕ) : poch (lam + 1) r ≠ 0 := poch_ne_zero_of_re_pos (by simp; linarith) r
  have hf (r : ℕ) : (r.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr r.factorial_ne_zero
  let G : ℕ → ℕ → ℂ := fun j k =>
    ((-1 : ℂ) ^ j * poch μ (n - j) / ((j.factorial : ℂ) * (n - 2 * j).factorial)) *
      ((n - 2 * j).factorial * ((lam + ((n - 2 * j : ℕ) : ℂ) - 2 * k) / lam /
        (poch (lam + 1) (n - 2 * j - k) * k.factorial)) * ultrasphPoly lam (n - 2 * j - 2 * k) x)
  have he : ultrasphPoly μ n x = ∑ j ∈ Finset.range (n / 2 + 1),
      ∑ k ∈ Finset.range (n / 2 - j + 1), G j k := by
    rw [ultrasphPoly_finite_sum hμ]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : 2 * j ≤ n := by have := Finset.mem_range.mp hj; omega
    rw [monomial_ultrasphPoly_expansion hlam, Finset.mul_sum, Finset.mul_sum,
      show (n - 2 * j) / 2 = n / 2 - j by omega]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [G]
    ring
  rw [he, sum_triangle_by_total_degree]
  apply Finset.sum_congr rfl
  intro r hr
  have hrn : 2 * r ≤ n := by have := Finset.mem_range.mp hr; omega
  let C : ℂ := (lam + n - 2 * r) / lam * poch μ (n - r) /
    poch (lam + 1) (n - r) / r.factorial * ultrasphPoly lam (n - 2 * r) x
  have ht (j : ℕ) (hj : j ∈ Finset.range (r + 1)) : G j (r - j) = C *
      ((r.choose j : ℂ) * poch (-lam - n + r) j * poch (μ + (n - r : ℕ)) (r - j)) := by
    have hjr : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hjn : j ≤ n - r := by omega
    have hden : poch (lam + 1) (n - r) = poch (lam + 1) (n - r - j) *
        ((-1 : ℂ) ^ j * poch (-lam - n + r) j) := by
      have hh := poch_add (lam + 1) (n - r - j) j
      rw [show n - r - j + j = n - r by omega] at hh
      have href := DLMF.Confluent.poch_sub_nat_self (lam + 1 + (n - r : ℕ)) j
      rw [show lam + 1 + (n - r : ℕ) - j = lam + 1 + (n - r - j : ℕ) by
        rw [Nat.cast_sub hjn]; ring,
        show 1 - (lam + 1 + (n - r : ℕ)) = -lam - n + r by rw [Nat.cast_sub (by omega : r ≤ n)]; ring] at href
      rw [href] at hh
      exact hh
    have hnum : poch μ (n - j) = poch μ (n - r) * poch (μ + (n - r : ℕ)) (r - j) := by
      rw [← poch_add]
      congr 1
      omega
    have hB : poch (-lam - n + r) j ≠ 0 := by
      have hh := hp (n - r)
      rw [hden] at hh
      exact right_ne_zero_of_mul (right_ne_zero_of_mul hh)
    dsimp [G, C]
    rw [show n - 2 * j - (r - j) = n - r - j by omega,
      show n - 2 * j - 2 * (r - j) = n - 2 * r by omega,
      show (lam + ((n - 2 * j : ℕ) : ℂ) - 2 * ((r - j : ℕ) : ℂ)) = lam + n - 2 * r by
        rw [Nat.cast_sub (by omega : 2 * j ≤ n), Nat.cast_sub hjr, Nat.cast_mul, Nat.cast_ofNat]; ring,
      hnum, hden, Nat.cast_choose ℂ hjr]
    have hsgn : ((-1 : ℂ) ^ j) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
    field_simp [hl, hp, hf, hB]
    rw [hsgn, one_mul]
  rw [Finset.sum_congr rfl ht, ← Finset.mul_sum]
  have hv := poch_add_eq_sum (-lam - n + r) (μ + (n - r : ℕ)) r
  rw [show -lam - n + r + (μ + (n - r : ℕ)) = μ - lam by
    rw [Nat.cast_sub (by omega : r ≤ n)]; ring] at hv
  rw [← hv]
  dsimp [C]
  ring

@[dlmf 18.18.E18]
theorem laguerrePolyL_connection (α β : ℂ) (n : ℕ) (x : ℂ) :
    laguerreExtended β n x = ∑ k ∈ Finset.range (n + 1),
      poch (β - α) (n - k) / (n - k).factorial * laguerreExtended α k x := by
  unfold laguerreExtended
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.range (n + 1)) (s' := fun j => Finset.Ico j (n + 1))
    (by intro k j; simp only [Finset.mem_range, Finset.mem_Ico]; omega)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := by simp at hj; omega
  rw [Finset.sum_Ico_eq_sum_range, show n + 1 - j = (n - j) + 1 by omega]
  have hv := poch_add_eq_sum (α + j + 1) (β - α) (n - j)
  rw [show α + j + 1 + (β - α) = β + j + 1 by ring] at hv
  rw [hv, Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmN : m ≤ n - j := by simp at hm; omega
  rw [show n - (j + m) = n - j - m by omega, show j + m - j = m by omega,
    Nat.cast_choose ℂ hmN]
  have h1 : ((n - j - m).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h4 : ((n - j).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

@[dlmf 18.18.E19]
theorem monomial_laguerrePolyL_expansion {α : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    x ^ n = poch (α + 1) n * ∑ k ∈ Finset.range (n + 1),
      poch (-(n : ℂ)) k / poch (α + 1) k * laguerrePolyL α k x := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by simp; linarith)
  have hpk : ∀ k, poch (α + 1) k ≠ 0 := poch_ne_zero_of_not_neg_nat hc
  simp_rw [laguerrePolyL_eq_sum hc, Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.range (n + 1)) (s' := fun j => Finset.Ico j (n + 1))
    (by intro k j; simp only [Finset.mem_range, Finset.mem_Ico]; omega)]
  have hterm : ∀ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.Ico j (n + 1),
      poch (α + 1) n * (poch (-(n : ℂ)) k / poch (α + 1) k *
        (poch (α + 1 + j) (k - j) / ((k - j).factorial * j.factorial : ℂ) * (-x) ^ j)) =
      poch (α + 1) n * (-x) ^ j * poch (-(n : ℂ)) j / (poch (α + 1) j * j.factorial) *
        0 ^ (n - j) := by
    intro j hj
    have hjn : j ≤ n := by simp at hj; omega
    rw [Finset.sum_Ico_eq_sum_range, show n + 1 - j = (n - j) + 1 by omega]
    have hs := sum_poch_neg_nat_div_factorial_mul_pow (n - j) 1
    rw [sub_self] at hs
    rw [← hs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [show j + m - j = m by omega, poch_add (α + 1) j m, poch_add (-(n : ℂ)) j m,
      show -(n : ℂ) + j = -((n - j : ℕ) : ℂ) by push_cast [Nat.cast_sub hjn]; ring]
    have h1 := hpk j
    have h2 : poch (α + 1 + j) m ≠ 0 := by
      have := hpk (j + m); rw [poch_add] at this; exact right_ne_zero_of_mul this
    have h3 : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h4 : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single n]
  · rw [Nat.sub_self, pow_zero, mul_one, poch_neg_coe_nat, Nat.descFactorial_self, neg_pow]
    have h4 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp [hpk n]
    rw [← pow_mul, mul_comm n 2, pow_mul, neg_one_sq, one_pow, mul_one]
  · intro j hj hjn
    have : 0 < n - j := by simp at hj; omega
    simp [zero_pow this.ne']
  · simp

@[dlmf 18.18.E20]
theorem monomial_hermitePolyH_expansion (n : ℕ) (x : ℂ) :
    (2 * x) ^ n = ∑ k ∈ Finset.range (n / 2 + 1),
      poch (-(n : ℂ)) (2 * k) / k.factorial * aeval x (hermitePolyH (n - 2 * k)) := by
  have hc := scalarSeries_unique
    (c := fun j => (2 * x) ^ j / j !)
    (d := fun j => ∑ k ∈ Finset.range (j / 2 + 1),
      (1 : ℂ) ^ k / k ! * ((aeval x (hermitePolyH (j - 2 * k)) : ℂ) / (j - 2 * k)! *
        (1 : ℂ) ^ (j - 2 * k)))
    (f := fun z => exp (2 * x * z))
    (fun z _ => by
      convert NormedSpace.expSeries_div_hasSum_exp (2 * x * z) using 1
      · funext j; rw [mul_pow]; ring
      · simp only [Complex.exp_eq_exp_ℂ])
    (fun z _ => by
      convert hasSum_exp_quadratic_mul_hermite 1 1 x z using 1
      congr 1; ring)
  have h := congrArg (fun c : ℕ → ℂ => c n * n !) hc
  rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr n.factorial_ne_zero), Finset.sum_mul] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : 2 * k ≤ n := by have := Finset.mem_range.mp hk; omega
  rw [← poch_neg_nat_even_mul_factorial hk']
  simp only [one_pow, mul_one, one_div]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - 2 * k))]

@[dlmf 18.18.E23]
theorem hermitePolyH_linearization (m n : ℕ) (x : ℂ) :
    (aeval x (hermitePolyH m) : ℂ) * aeval x (hermitePolyH n) =
      ∑ k ∈ Finset.range (min m n + 1), (m.choose k : ℂ) * n.choose k * 2 ^ k * k.factorial *
        aeval x (hermitePolyH (m + n - 2 * k)) := by
  have hc := scalarSeries_unique
    (c := fun j => (aeval x (hermitePolyH m) : ℂ) * aeval x (hermitePolyH j) / j !)
    (d := fun j => ∑ k ∈ Finset.range (m + 1),
      (m.choose k : ℂ) * 2 ^ k *
        (if k ≤ j then (aeval x (hermitePolyH (m - k + (j - k))) : ℂ) / (j - k)! else 0))
    (f := fun z => (aeval x (hermitePolyH m) : ℂ) * exp (2 * x * z - z ^ 2))
    (fun z _ => ((hasSum_hermitePolyH_generating_function x z).mul_left
      (aeval x (hermitePolyH m) : ℂ)).congr_fun (by intro j; ring))
    (fun z _ => by
      have hs (k : ℕ) := (hasSum_scalar_shift
        (c := fun j => (aeval x (hermitePolyH (m - k + j)) : ℂ) / j !) (z := z)
        ((hasSum_hermitePolyH_shifted (m - k) x z).congr_fun (by intro j; ring)) k).mul_left
          ((m.choose k : ℂ) * 2 ^ k)
      have h := hasSum_sum (s := Finset.range (m + 1)) (fun k _ => hs k)
      have hv : (∑ k ∈ Finset.range (m + 1), (m.choose k : ℂ) * 2 ^ k *
          (z ^ k * ((aeval (x - z) (hermitePolyH (m - k)) : ℂ) * exp (2 * x * z - z ^ 2)))) =
          (aeval x (hermitePolyH m) : ℂ) * exp (2 * x * z - z ^ 2) := by
        rw [show (∑ k ∈ Finset.range (m + 1), (m.choose k : ℂ) * 2 ^ k *
            (z ^ k * ((aeval (x - z) (hermitePolyH (m - k)) : ℂ) * exp (2 * x * z - z ^ 2)))) =
            (∑ k ∈ Finset.range (m + 1), (m.choose k : ℂ) * (2 * z) ^ k *
              aeval (x - z) (hermitePolyH (m - k))) * exp (2 * x * z - z ^ 2) by
          rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro k _; rw [mul_pow]; ring]
        rw [← hermitePolyH_translation, sub_add_cancel]
      rw [hv] at h
      simpa only [Finset.sum_mul, mul_assoc] using h)
  have h := congrArg (fun c : ℕ → ℂ => c n * n !) hc
  rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr n.factorial_ne_zero), Finset.sum_mul] at h
  rw [h]
  have hsub : Finset.range (min m n + 1) ⊆ Finset.range (m + 1) :=
    Finset.range_subset_range.mpr (by omega)
  rw [← Finset.sum_subset hsub (by
    intro k hk hkn
    have hnk : ¬ k ≤ n := by
      simp only [Finset.mem_range] at hk hkn; omega
    simp [hnk])]
  apply Finset.sum_congr rfl
  intro k hk
  have hkm : k ≤ m := by have := Finset.mem_range.mp hk; omega
  have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
  rw [if_pos hkn, show m - k + (n - k) = m + n - 2 * k by omega]
  have he : (n.choose k : ℂ) * k ! * (n - k)! = n ! := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  rw [← he]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - k))]

@[dlmf 18.18.E28]
theorem mehler_formula (x y : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (aeval (x : ℂ) (hermitePolyH n) : ℂ) * aeval (y : ℂ) (hermitePolyH n) /
      (2 ^ n * (n.factorial : ℂ)) * z ^ n)
      ((1 - z ^ 2) ^ (-1 / 2 : ℂ) * exp ((2 * x * y * z - (x ^ 2 + y ^ 2) * z ^ 2) / (1 - z ^ 2))) := by
  exact Mehler.hasSum_kernel (x : ℂ) (y : ℂ) hz


@[dlmf 18.18.E9]
theorem legendre_addition (n : ℕ) (θ ψ phi : ℝ) :
    legendrePolyP n (Real.cos θ * Real.cos ψ + Real.sin θ * Real.sin ψ * Real.cos phi) =
      legendrePolyP n (Real.cos θ) * legendrePolyP n (Real.cos ψ) +
      2 * ∑ k ∈ Finset.Icc 1 n, ((n - k).factorial : ℂ) * (n + k).factorial /
        (2 ^ (2 * k) * (n.factorial : ℂ) ^ 2) * (Real.sin θ : ℂ) ^ k *
        jacobiPolyP k k (n - k) (Real.cos θ) * (Real.sin ψ : ℂ) ^ k *
        jacobiPolyP k k (n - k) (Real.cos ψ) * Real.cos (k * phi) := by
  have hs0 := congrArg (fun x : ℝ => (x : ℂ)) (Real.sin_sq_add_cos_sq θ)
  have ht0 := congrArg (fun x : ℝ => (x : ℂ)) (Real.sin_sq_add_cos_sq ψ)
  push_cast at hs0 ht0 ⊢
  have hs : sin (θ : ℂ)^2 = 1-cos (θ : ℂ)^2 := by linear_combination hs0
  have ht : sin (ψ : ℂ)^2 = 1-cos (ψ : ℂ)^2 := by linear_combination ht0
  rw [LegendreAddition.legendre_eq_kernel n (cos θ) (cos ψ) (sin θ) (sin ψ) phi hs ht,
    LegendreAddition.kernel]
  rw [show Finset.Icc 1 n = Finset.Ico 1 (n+1) by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm 1]
  rw [LegendreAddition.coeff, LegendreAddition.weight_zero]
  simp only [pow_zero, one_mul, LegendreAddition.jet_zero]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k+1 ≤ n := by simp at hk; omega
  rw [LegendreAddition.coeff_eq_jacobi n (k+1) hk']
  push_cast
  ring

/-- The Gegenbauer product coefficient in the three nonnegative gap indices. -/
noncomputable def gegenbauerProductCoeff (lam : ℂ) (a b k : ℕ) : ℂ :=
  (lam + a + b) / (lam + a + b + k) * (a + b).factorial /
    (k.factorial * a.factorial * b.factorial) *
      (poch lam k * poch lam a * poch lam b * poch (2 * lam) (a + b + k) /
        (poch lam (a + b + k) * poch (2 * lam) (a + b)))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The interior coefficient recurrence follows from factorial and Pochhammer shifts. -/
theorem gegenbauerProductCoeff_recurrence {lam : ℂ} (hlam : 0 < lam.re) (a b k : ℕ) :
    (b + k + 2 : ℂ) * gegenbauerProductCoeff lam a (b + 1) (k + 1) =
      (b + k + 1 + lam) * (a + b + 1) / (lam + a + b) * gegenbauerProductCoeff lam a b (k + 1) +
      (b + k + 1 + lam) * (a + b + 2 * lam + 1) / (lam + a + b + 2) *
        gegenbauerProductCoeff lam (a + 1) (b + 1) k -
      (b + k + 2 * lam) * gegenbauerProductCoeff lam (a + 1) b k := by
  have hp (j : ℕ) : poch lam j ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos hlam) j
  have hp2 (j : ℕ) : poch (2 * lam) j ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; linarith)) j
  have hf (j : ℕ) : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  have hn (i j q : ℕ) : lam + i + j + q ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    simp at hh
    linarith [Nat.cast_nonneg (α := ℝ) i, Nat.cast_nonneg (α := ℝ) j,
      Nat.cast_nonneg (α := ℝ) q]
  have hd01 : a + (b + 1) = (a + b) + 1 := by omega
  have hd11 : (a + 1) + (b + 1) = (a + b) + 1 + 1 := by omega
  have hd10 : (a + 1) + b = (a + b) + 1 := by omega
  have hidx01' : (a + b + 1) + (k + 1) = (a + b + k) + 1 + 1 := by omega
  have hidx11' : (a + b + 1 + 1) + k = (a + b + k) + 1 + 1 := by omega
  have hidx10' : (a + b + 1) + k = (a + b + k) + 1 := by omega
  unfold gegenbauerProductCoeff
  simp only [hd01, hd11, hd10]
  simp only [hidx01', hidx11', hidx10', Nat.add_succ, poch_succ, Nat.factorial_succ]
  push_cast
  have h0 : lam + a + b ≠ 0 := by simpa using hn a b 0
  have h1 : lam + a + b + 1 ≠ 0 := by simpa using hn a b 1
  have h2 : lam + a + b + 2 ≠ 0 := by simpa using hn a b 2
  have hs0 : lam + a + b + k ≠ 0 := hn a b k
  have hs1 : lam + a + b + k + 1 ≠ 0 := by simpa [add_assoc] using hn a b (k + 1)
  have hs2 : lam + a + b + k + 2 ≠ 0 := by simpa [add_assoc] using hn a b (k + 2)
  have h20 : 2 * lam + a + b ≠ 0 := by
    intro he; have hh := congrArg Complex.re he; simp at hh
    linarith [Nat.cast_nonneg (α := ℝ) a, Nat.cast_nonneg (α := ℝ) b]
  have h21 : 2 * lam + a + b + 1 ≠ 0 := by
    intro he; have hh := congrArg Complex.re he; simp at hh
    linarith [Nat.cast_nonneg (α := ℝ) a, Nat.cast_nonneg (α := ℝ) b]
  simp only [add_comm, add_left_comm, add_assoc, one_add_one_eq_two] at h0 h1 h2 hs0 hs1 hs2 h20 h21 ⊢
  field_simp [hp, hp2, hf, h0, h1, h2, hs0, hs1, hs2, h20, h21]
  ring

/-- The coefficient of the trivial factor is one. -/
theorem gegenbauerProductCoeff_zero {lam : ℂ} (hlam : 0 < lam.re) (a : ℕ) :
    gegenbauerProductCoeff lam a 0 0 = 1 := by
  have hp (j : ℕ) : poch lam j ≠ 0 := poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos hlam) j
  have hp2 (j : ℕ) : poch (2 * lam) j ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; linarith)) j
  have hf (j : ℕ) : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  have hn : lam + a ≠ 0 := by
    intro he; have hh := congrArg Complex.re he; simp at hh
    linarith [Nat.cast_nonneg (α := ℝ) a]
  simp [gegenbauerProductCoeff, poch_zero, hp, hp2, hf, hn]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The upper endpoint of the coefficient recurrence. -/
theorem gegenbauerProductCoeff_top {lam : ℂ} (hlam : 0 < lam.re) (a b : ℕ) :
    (b + 1 : ℂ) * gegenbauerProductCoeff lam a (b + 1) 0 =
      (b + lam) * (a + b + 1) / (lam + a + b) * gegenbauerProductCoeff lam a b 0 := by
  have hp (j : ℕ) : poch lam j ≠ 0 := poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos hlam) j
  have hp2 (j : ℕ) : poch (2 * lam) j ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; linarith)) j
  have hf (j : ℕ) : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  have hn (q : ℕ) : lam + a + b + q ≠ 0 := by
    intro he; have hh := congrArg Complex.re he; simp at hh
    linarith [Nat.cast_nonneg (α := ℝ) a, Nat.cast_nonneg (α := ℝ) b, Nat.cast_nonneg (α := ℝ) q]
  have h0 : lam + a + b ≠ 0 := by simpa using hn 0
  have h1 : lam + a + b + 1 ≠ 0 := by simpa using hn 1
  unfold gegenbauerProductCoeff
  simp only [Nat.add_zero, Nat.cast_zero, add_zero, Nat.factorial_zero, Nat.cast_one,
    poch_zero, one_mul, mul_one, show a + (b + 1) = (a + b) + 1 by omega,
    poch_succ, Nat.factorial_succ]
  push_cast
  have h20 : 2 * lam + a + b ≠ 0 := by
    intro he; have hh := congrArg Complex.re he; simp at hh
    linarith [Nat.cast_nonneg (α := ℝ) a, Nat.cast_nonneg (α := ℝ) b]
  simp only [mul_comm, add_comm, add_left_comm, add_assoc] at hp2 h0 h1 h20 ⊢
  field_simp [hp, hp2, hf, h0, h1, h20]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The lower endpoint of the coefficient recurrence. -/
theorem gegenbauerProductCoeff_bottom {lam : ℂ} (hlam : 0 < lam.re) (a k : ℕ) :
    (k + 1 : ℂ) * gegenbauerProductCoeff lam a 0 (k + 1) =
      (k + lam) * (a + 2 * lam) / (lam + a + 1) * gegenbauerProductCoeff lam (a + 1) 0 k := by
  have hp (j : ℕ) : poch lam j ≠ 0 := poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos hlam) j
  have hp2 (j : ℕ) : poch (2 * lam) j ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; linarith)) j
  have hf (j : ℕ) : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  have hn (q : ℕ) : lam + a + q ≠ 0 := by
    intro he; have hh := congrArg Complex.re he; simp at hh
    linarith [Nat.cast_nonneg (α := ℝ) a, Nat.cast_nonneg (α := ℝ) q]
  have h0 : lam + a ≠ 0 := by simpa using hn 0
  have h1 : lam + a + 1 ≠ 0 := by simpa using hn 1
  have hs : lam + a + k + 1 ≠ 0 := by simpa [add_assoc] using hn (k + 1)
  have h2 : 2 * lam + a ≠ 0 := by
    intro he; have hh := congrArg Complex.re he; simp at hh
    linarith [Nat.cast_nonneg (α := ℝ) a]
  unfold gegenbauerProductCoeff
  simp only [Nat.add_zero, Nat.cast_zero, add_zero, Nat.factorial_zero, Nat.cast_one,
    poch_zero, one_mul, mul_one, show (a + 1) + k = a + k + 1 by omega,
    Nat.add_succ, poch_succ, Nat.factorial_succ]
  push_cast
  have hs0 : lam + a + k ≠ 0 := hn k
  simp only [mul_comm, add_comm, add_left_comm, add_assoc] at hp2 h0 h1 hs hs0 h2 ⊢
  field_simp [hp, hp2, hf, h0, h1, hs, hs0, h2]

/-- Multiplication by `2x` in the Gegenbauer basis, for positive degree. -/
theorem two_mul_x_ultrasphPoly {lam : ℂ} (hlam : 0 < lam.re) {d : ℕ} (hd : 0 < d) (x : ℂ) :
    2 * x * ultrasphPoly lam d x =
      (d + 1 : ℂ) / (lam + d) * ultrasphPoly lam (d + 1) x +
      (d + 2 * lam - 1) / (lam + d) * ultrasphPoly lam (d - 1) x := by
  have hn : lam + d ≠ 0 := by
    intro he; have hh := congrArg Complex.re he; simp at hh
    linarith [Nat.cast_nonneg (α := ℝ) d]
  have hh := ultrasphPoly_recurrence (by linarith : -1 / 2 < lam.re) (d - 1) x
  rw [show d - 1 + 2 = d + 1 by omega, show d - 1 + 1 = d by omega,
    Nat.cast_sub (by omega : 1 ≤ d)] at hh
  push_cast at hh
  field_simp [hn]
  linear_combination -hh

/-- The finite product expansion with the second degree bounded by the first. -/
noncomputable def gegenbauerLinearizationSum (lam : ℂ) (m n : ℕ) (x : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), gegenbauerProductCoeff lam (m - k) (n - k) k *
    ultrasphPoly lam (m + n - 2 * k) x

/-- The finite coefficient sum obeys the Gegenbauer recurrence in its second degree. -/
theorem gegenbauerLinearizationSum_recurrence {lam : ℂ} (hlam : 0 < lam.re)
    {m n : ℕ} (hnm : n + 2 ≤ m) (x : ℂ) :
    (n + 2 : ℂ) * gegenbauerLinearizationSum lam m (n + 2) x =
      2 * (n + lam + 1) * x * gegenbauerLinearizationSum lam m (n + 1) x -
        (n + 2 * lam) * gegenbauerLinearizationSum lam m n x := by
  let T : ℕ → ℂ := fun k => gegenbauerProductCoeff lam (m - k) (n + 2 - k) k *
    ultrasphPoly lam (m + (n + 2) - 2 * k) x
  let U : ℕ → ℂ := fun k => gegenbauerProductCoeff lam (m - k) (n + 1 - k) k *
    ultrasphPoly lam (m + (n + 1) - 2 * k) x
  let V : ℕ → ℂ := fun k => gegenbauerProductCoeff lam (m - k) (n - k) k *
    ultrasphPoly lam (m + n - 2 * k) x
  let A : ℕ → ℂ := fun k => (n + lam + 1) * ((m + (n + 1) - 2 * k : ℕ) + 1) /
    (lam + (m + (n + 1) - 2 * k : ℕ)) * gegenbauerProductCoeff lam (m - k) (n + 1 - k) k *
      ultrasphPoly lam ((m + (n + 1) - 2 * k) + 1) x
  let B : ℕ → ℂ := fun k => (n + lam + 1) * ((m + (n + 1) - 2 * k : ℕ) + 2 * lam - 1) /
    (lam + (m + (n + 1) - 2 * k : ℕ)) * gegenbauerProductCoeff lam (m - k) (n + 1 - k) k *
      ultrasphPoly lam ((m + (n + 1) - 2 * k) - 1) x
  have hU (k : ℕ) (hk : k ∈ Finset.range (n + 2)) :
      2 * (n + lam + 1) * x * U k = A k + B k := by
    have hd : 0 < m + (n + 1) - 2 * k := by have := Finset.mem_range.mp hk; omega
    dsimp [U, A, B]
    have he := congrArg (fun v : ℂ => (n + lam + 1) *
      gegenbauerProductCoeff lam (m - k) (n + 1 - k) k * v) (two_mul_x_ultrasphPoly hlam hd x)
    linear_combination he
  have hhead : (n + 2 : ℂ) * T 0 = A 0 := by
    dsimp [T, A]
    have he := congrArg (fun v : ℂ => v * ultrasphPoly lam (m + (n + 2)) x)
      (gegenbauerProductCoeff_top hlam m (n + 1))
    rw [show m + (n + 1) + 1 = m + (n + 2) by omega]
    push_cast at he ⊢
    linear_combination he
  have htail : (n + 2 : ℂ) * T (n + 2) = B (n + 1) := by
    have hm : m - (n + 2) + 1 = m - (n + 1) := by omega
    dsimp [T, B]
    rw [Nat.sub_self, Nat.sub_self]
    have he := congrArg (fun v : ℂ => v * ultrasphPoly lam (m - (n + 2)) x)
      (gegenbauerProductCoeff_bottom hlam (m - (n + 2)) (n + 1))
    rw [hm] at he
    rw [show m + (n + 2) - 2 * (n + 2) = m - (n + 2) by omega,
      show m + (n + 1) - 2 * (n + 1) = m - (n + 1) by omega,
      show m - (n + 1) - 1 = m - (n + 2) by omega]
    push_cast [Nat.cast_sub (show n + 1 ≤ m by omega), Nat.cast_sub hnm] at he ⊢
    linear_combination he
  have hinner (j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
      (n + 2 : ℂ) * T (j + 1) = A (j + 1) + B j - (n + 2 * lam) * V j := by
    have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hM : m - (j + 1) = m - j - 1 := by omega
    have hN : n + 2 - (j + 1) = (n - j) + 1 := by omega
    have hN0 : n + 1 - (j + 1) = n - j := by omega
    have hM1 : m - j - 1 + 1 = m - j := by omega
    have hN1 : n - j + 1 = n + 1 - j := by omega
    have hd0 : m + (n + 1) - 2 * (j + 1) = (m - j - 1) + (n - j) := by omega
    have hd1 : m + (n + 1) - 2 * j = (m - j - 1) + (n - j) + 2 := by omega
    have hd2 : m + (n + 2) - 2 * (j + 1) = (m - j - 1) + (n - j) + 1 := by omega
    have hd3 : m + n - 2 * j = (m - j - 1) + (n - j) + 1 := by omega
    dsimp [T, A, B, V]
    rw [hM, hN, hN0, hd0, hd1, hd2, hd3,
      show ((m - j - 1) + (n - j) + 2) - 1 = (m - j - 1) + (n - j) + 1 by omega]
    rw [hN1]
    have he := congrArg (fun v : ℂ => v * ultrasphPoly lam ((m - j - 1) + (n - j) + 1) x)
      (gegenbauerProductCoeff_recurrence hlam (m - j - 1) (n - j) j)
    rw [hM1, hN1] at he
    push_cast [Nat.cast_sub hjn] at he ⊢
    linear_combination he
  change (n + 2 : ℂ) * (∑ k ∈ Finset.range (n + 2 + 1), T k) =
    2 * (n + lam + 1) * x * (∑ k ∈ Finset.range (n + 1 + 1), U k) -
      (n + 2 * lam) * ∑ k ∈ Finset.range (n + 1), V k
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [Finset.sum_congr rfl hU]
  simp only [Finset.sum_add_distrib]
  conv_lhs => rw [Finset.sum_range_succ, Finset.sum_range_succ']
  conv_rhs => lhs; lhs; rw [Finset.sum_range_succ']
  conv_rhs => lhs; rhs; rw [Finset.sum_range_succ]
  rw [hhead, htail]
  have hi := Finset.sum_congr rfl hinner
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hi
  linear_combination hi

/-- Gegenbauer products are the finite coefficient sums when the second degree is smaller. -/
theorem ultrasphPoly_product_eq_sum_of_le {lam : ℂ} (hlam : 0 < lam.re) (m n : ℕ)
    (hnm : n ≤ m) (x : ℂ) :
    ultrasphPoly lam m x * ultrasphPoly lam n x = gegenbauerLinearizationSum lam m n x := by
  induction n using Nat.twoStepInduction with
  | zero => simp [gegenbauerLinearizationSum, gegenbauerProductCoeff_zero hlam]
  | one =>
    have hm : 0 < m := by omega
    have ht : gegenbauerProductCoeff lam m 1 0 = lam * (m + 1) / (lam + m) := by
      have he := gegenbauerProductCoeff_top hlam m 0
      rw [gegenbauerProductCoeff_zero hlam] at he
      norm_num at he
      linear_combination he
    have hb : gegenbauerProductCoeff lam (m - 1) 0 1 =
        lam * (m + 2 * lam - 1) / (lam + m) := by
      have he := gegenbauerProductCoeff_bottom hlam (m - 1) 0
      rw [gegenbauerProductCoeff_zero hlam] at he
      norm_num at he
      push_cast [Nat.cast_sub (show 1 ≤ m by omega)] at he
      convert he using 1 <;> ring
    have he := two_mul_x_ultrasphPoly hlam hm x
    rw [ultrasphPoly_one_eq (by linarith : -1 / 2 < lam.re)]
    unfold gegenbauerLinearizationSum
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero,
      Nat.sub_self, Nat.mul_zero, Nat.mul_one, Nat.cast_zero, Nat.cast_one]
    rw [ht, hb, show m + 1 - 2 = m - 1 by omega]
    linear_combination lam * he
  | more n ih0 ih1 =>
    have h0 := ih0 (by omega : n ≤ m)
    have h1 := ih1 (by omega : n + 1 ≤ m)
    have hS := gegenbauerLinearizationSum_recurrence hlam hnm x
    rw [← h0, ← h1] at hS
    have hC := ultrasphPoly_recurrence (by linarith : -1 / 2 < lam.re) n x
    have hn : (n + 2 : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    apply mul_left_cancel₀ hn
    linear_combination ultrasphPoly lam m x * hC - hS

/-- Symmetry of the coefficient in the two gap indices. -/
theorem gegenbauerProductCoeff_swap (lam : ℂ) (a b k : ℕ) :
    gegenbauerProductCoeff lam a b k = gegenbauerProductCoeff lam b a k := by
  unfold gegenbauerProductCoeff
  rw [Nat.add_comm b a]
  ring

/-- Match the gap-index coefficient to the DLMF normalization. -/
theorem gegenbauerProductCoeff_eq (lam : ℂ) {m n k : ℕ} (hkm : k ≤ m) (hkn : k ≤ n) :
    gegenbauerProductCoeff lam (m - k) (n - k) k =
      (m + n + lam - 2 * k) * (m + n - 2 * k).factorial /
        ((m + n + lam - k) * k.factorial * (m - k).factorial * (n - k).factorial) *
        (poch lam k * poch lam (m - k) * poch lam (n - k) * poch (2 * lam) (m + n - k) /
          (poch lam (m + n - k) * poch (2 * lam) (m + n - 2 * k))) := by
  unfold gegenbauerProductCoeff
  rw [show (m - k) + (n - k) = m + n - 2 * k by omega,
    show m + n - 2 * k + k = m + n - k by omega]
  push_cast [Nat.cast_sub hkm, Nat.cast_sub hkn]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring


@[dlmf 18.18.E22]
theorem ultrasphPoly_linearization {lam : ℝ} (hlam : 0 < lam) (m n : ℕ) (x : ℂ) :
    ultrasphPoly lam m x * ultrasphPoly lam n x = ∑ k ∈ Finset.range (min m n + 1),
      (m + n + (lam : ℂ) - 2 * k) * (m + n - 2 * k).factorial /
      ((m + n + lam - k) * k.factorial * (m - k).factorial * (n - k).factorial) *
      (poch lam k * poch lam (m - k) * poch lam (n - k) * poch (2 * lam) (m + n - k) /
       (poch lam (m + n - k) * poch (2 * lam) (m + n - 2 * k)))
           * ultrasphPoly lam (m + n - 2 * k) x := by
  have hl : 0 < (lam : ℂ).re := by simpa using hlam
  have he : ultrasphPoly lam m x * ultrasphPoly lam n x =
      ∑ k ∈ Finset.range (min m n + 1), gegenbauerProductCoeff lam (m - k) (n - k) k *
        ultrasphPoly lam (m + n - 2 * k) x := by
    rcases le_total n m with hnm | hmn
    · rw [min_eq_right hnm]
      exact ultrasphPoly_product_eq_sum_of_le hl m n hnm x
    · rw [min_eq_left hmn, mul_comm]
      have hh := ultrasphPoly_product_eq_sum_of_le hl n m hmn x
      simpa only [gegenbauerLinearizationSum, gegenbauerProductCoeff_swap (lam : ℂ), Nat.add_comm n m] using hh
  rw [he]
  apply Finset.sum_congr rfl
  intro k hk
  have hkm : k ≤ m := by have := Finset.mem_range.mp hk; omega
  have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
  rw [gegenbauerProductCoeff_eq (lam : ℂ) hkm hkn]


@[dlmf 18.18.E29]
theorem ultrasphPoly_convolution {lam μ : ℂ} (hlam : 0 < lam.re) (hμ : 0 < μ.re) (n : ℕ) (x : ℂ) :
    ∑ k ∈ Finset.range (n + 1),
        ultrasphPoly lam k x * ultrasphPoly μ (n - k) x = ultrasphPoly (lam + μ) n x := by
  obtain ⟨w, hw, rfl⟩ := exists_eq_half_add_recip x
  have h1 : -1 / 2 < lam.re := by linarith
  have h2 : -1 / 2 < μ.re := by linarith
  have h3 : -1 / 2 < (lam + μ).re := by rw [Complex.add_re]; linarith
  simp_rw [ultrasphPoly_eq_coeff_gegenbauerSeries h1 hw,
      ultrasphPoly_eq_coeff_gegenbauerSeries h2 hw,
    ultrasphPoly_eq_coeff_gegenbauerSeries h3 hw]
  exact sum_coeff_mul_coeff_gegenbauerSeries lam μ w n

@[dlmf 18.18.E30]
theorem ultrasphPoly_geometric_convolution {lam : ℂ} (hlam : 0 < lam.re) (n : ℕ) (x : ℂ) :
    ∑ k ∈ Finset.range (n + 1), (k + 2 * lam) / (2 * lam) * ultrasphPoly lam k x * x ^ (n - k) =
      ultrasphPoly (lam + 1) n x := by
  obtain ⟨w, hw, rfl⟩ := exists_eq_half_add_recip x
  have h1 : -1 / 2 < lam.re := by linarith
  have h2 : -1 / 2 < (lam + 1).re := by rw [Complex.add_re, Complex.one_re]; linarith
  have hlam0 : lam ≠ 0 := fun h => by rw [h, Complex.zero_re] at hlam; exact lt_irrefl _ hlam
  simp_rw [ultrasphPoly_eq_coeff_gegenbauerSeries h1 hw,
      ultrasphPoly_eq_coeff_gegenbauerSeries h2 hw]
  exact sum_weighted_coeff_gegenbauerSeries hlam0 hw n

/-- `U_{n+2} = 2 T_{n+2} + U_n`. -/
theorem chebyshevU_eq_two_T_add_U (n : ℕ) (x : ℂ) :
    (Chebyshev.U ℂ (n + 2)).eval x =
      2 * (Chebyshev.T ℂ (n + 2)).eval x + (Chebyshev.U ℂ n).eval x := by
  have hT := congrArg (fun p : ℂ[X] => p.eval x)
    (Chebyshev.T_eq_X_mul_U_sub_U (R := ℂ) n)
  have hU := congrArg (fun p : ℂ[X] => p.eval x)
    (Chebyshev.U_add_two (R := ℂ) n)
  simp only [eval_sub, eval_mul, eval_X, eval_ofNat] at hT hU
  linear_combination hU - 2 * hT

@[dlmf 18.18.E31]
theorem chebyshev_geometric_sum (n : ℕ) (x : ℂ) :
    ∑ k ∈ Finset.range (n + 1), (Chebyshev.T ℂ k).eval x * x ^ (n - k) =
      (Chebyshev.U ℂ n).eval x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one]
    have hsum : ∑ k ∈ Finset.range (n + 1), (Chebyshev.T ℂ k).eval x * x ^ (n + 1 - k) =
        x * ∑ k ∈ Finset.range (n + 1), (Chebyshev.T ℂ k).eval x * x ^ (n - k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
      ring
    rw [hsum, ih]
    have h := congrArg (Polynomial.eval x) (Chebyshev.U_eq_X_mul_U_add_T ℂ n)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] at h
    push_cast
    linear_combination -h

@[dlmf 18.18.E32]
theorem chebyshevT_even_sum (n : ℕ) (x : ℂ) :
    2 * ∑ k ∈ Finset.range (n + 1), (Chebyshev.T ℂ (2 * k)).eval x =
      1 + (Chebyshev.U ℂ (2 * n)).eval x := by
  induction n with
  | zero =>
    simp [Chebyshev.T_zero, Chebyshev.U_zero]
    norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hU := chebyshevU_eq_two_T_add_U (2 * n) x
    have hU' : (Chebyshev.U ℂ (2 * (n + 1))).eval x =
        2 * (Chebyshev.T ℂ (2 * (n + 1))).eval x + (Chebyshev.U ℂ (2 * n)).eval x := by
      convert hU <;> (push_cast; ring)
    simp only [Nat.cast_succ] at hU' ⊢
    rw [hU']
    ring

@[dlmf 18.18.E33]
theorem chebyshevT_odd_sum (n : ℕ) (x : ℂ) :
    2 * ∑ k ∈ Finset.range (n + 1), (Chebyshev.T ℂ (2 * k + 1)).eval x =
      (Chebyshev.U ℂ (2 * n + 1)).eval x := by
  induction n with
  | zero => simp [Chebyshev.T_one, Chebyshev.U_one]
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h := congrArg (Polynomial.eval x) (Chebyshev.two_mul_T_eq_U_sub_U ℂ (2 * n + 1))
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_ofNat] at h
    rw [show (2 : ℤ) * ((n + 1 : ℕ) : ℤ) + 1 = 2 * (n : ℤ) + 1 + 2 by push_cast; ring]
    linear_combination h

@[dlmf 18.18.E34]
theorem chebyshevU_even_sum (n : ℕ) (x : ℂ) :
    2 * (1 - x ^ 2) * ∑ k ∈ Finset.range (n + 1), (Chebyshev.U ℂ (2 * k)).eval x =
      1 - (Chebyshev.T ℂ (2 * n + 2)).eval x := by
  induction n with
  | zero =>
    simp [Chebyshev.T_two]
    ring
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h1 := congrArg (Polynomial.eval x)
      (Chebyshev.one_sub_X_sq_mul_U_eq_pol_in_T ℂ (2 * n + 2))
    have h2 := congrArg (Polynomial.eval x) (Chebyshev.T_add_two ℂ (2 * n + 2))
    simp only [Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat] at h1 h2
    rw [show (2 : ℤ) * ((n + 1 : ℕ) : ℤ) = 2 * (n : ℤ) + 2 by push_cast; ring]
    linear_combination 2 * h1 - h2

@[dlmf 18.18.E35]
theorem chebyshevU_odd_sum (n : ℕ) (x : ℂ) :
    2 * (1 - x ^ 2) * ∑ k ∈ Finset.range (n + 1), (Chebyshev.U ℂ (2 * k + 1)).eval x =
      x - (Chebyshev.T ℂ (2 * n + 3)).eval x := by
  induction n with
  | zero =>
    have h := congrArg (Polynomial.eval x) (Chebyshev.T_add_two ℂ 1)
    simp only [Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat] at h
    norm_num [Chebyshev.T_two, Chebyshev.T_one] at h
    simp [Chebyshev.U_one]
    rw [h]
    ring
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h1 := congrArg (Polynomial.eval x)
      (Chebyshev.one_sub_X_sq_mul_U_eq_pol_in_T ℂ (2 * n + 3))
    have h2 := congrArg (Polynomial.eval x) (Chebyshev.T_add_two ℂ (2 * n + 3))
    simp only [Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat] at h1 h2
    rw [show (2 : ℤ) * ((n + 1 : ℕ) : ℤ) + 1 = 2 * (n : ℤ) + 3 by push_cast; ring,
      show (2 : ℤ) * ((n + 1 : ℕ) : ℤ) + 3 = 2 * (n : ℤ) + 3 + 2 by push_cast; ring]
    linear_combination 2 * h1 - h2

@[dlmf 18.18.E36]
theorem legendre_convolution (n : ℕ) (x : ℂ) :
    ∑ k ∈ Finset.range (n + 1),
        legendrePolyP k x * legendrePolyP (n - k) x = (Chebyshev.U ℂ n).eval x := by
  simp_rw [legendre_eq_ultrasphPoly]
  rw [ultrasphPoly_convolution (by norm_num) (by norm_num), eval_U_eq_ultrasphPoly]
  norm_num

@[dlmf 18.18.E37]
theorem laguerrePolyL_sum (α : ℂ) (n : ℕ) (x : ℂ) :
    ∑ k ∈ Finset.range (n + 1), laguerreExtended α k x = laguerreExtended (α + 1) n x := by
  -- the polynomial identity in `α` is proved for `Re α > 0` and extended by analyticity
  have hana : ∀ m : ℕ, AnalyticOnNhd ℂ (fun a : ℂ => laguerreExtended a m x) Set.univ := by
    intro m a _
    unfold laguerreExtended
    refine Finset.analyticAt_fun_sum (Finset.range (m + 1)) fun k _ => ?_
    have h : AnalyticAt ℂ (fun a : ℂ => poch (a + k + 1) (m - k)) a :=
      (((Polynomial.differentiable (ascPochhammer ℂ (m - k))).comp
        ((differentiable_id.add_const _).add_const _))).analyticAt a
    exact (h.div_const).mul analyticAt_const
  have key : (fun a : ℂ => ∑ k ∈ Finset.range (n + 1), laguerreExtended a k x) =
      fun a => laguerreExtended (a + 1) n x := by
    refine DLMF.Hypergeometric.eq_of_eqOn_re_pos ?_ ?_ ?_
    · intro a _
      exact Finset.analyticAt_fun_sum (Finset.range (n + 1)) fun k _ => hana k a (Set.mem_univ a)
    · intro a _
      exact ((hana n) (a + 1) (Set.mem_univ _)).comp (f := fun a : ℂ => a + 1) (by fun_prop)
    intro a ha
    have h1 : ∀ k : ℕ, a + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
      simp only [Complex.add_re, Complex.one_re]
      linarith)
    have h2 : ∀ k : ℕ, a + 1 + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
      simp only [Complex.add_re, Complex.one_re]
      linarith)
    have ha' : -1 < a.re := by linarith
    simp only [laguerreExtended_eq h1, laguerreExtended_eq h2]
    induction n with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, laguerrePolyL_raise_parameter ha']
      ring
  exact congrFun key α

@[dlmf 18.18.E40]
theorem hermitePolyH_even_convolution (n : ℕ) (x y : ℂ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (aeval x (hermitePolyH (2 * k)) : ℂ) *
      aeval y (hermitePolyH (2 * n - 2 * k)) = (-1 : ℂ) ^ n * 2 ^ (2 * n) * n.factorial
          * laguerrePolyL 0 n (x ^ 2 + y ^ 2) := by
  have hc : ∀ k : ℕ, (-1 / 2 : ℂ) + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by norm_num)
  have hc0 : ∀ k : ℕ, (0 : ℂ) + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by norm_num)
  have hadd := laguerrePolyL_addition (-1 / 2) (-1 / 2) (x ^ 2) (y ^ 2) n
  rw [show (-1 / 2 : ℂ) + -1 / 2 + 1 = 0 by ring, laguerreExtended_eq hc0] at hadd
  rw [hadd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [show 2 * n - 2 * k = 2 * (n - k) by omega, hermitePolyH_even_eq_laguerrePolyL,
    hermitePolyH_even_eq_laguerrePolyL, laguerreExtended_eq hc, laguerreExtended_eq hc,
    Nat.cast_choose ℂ hkn]
  have h1 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : ((n - k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hpow1 : (-1 : ℂ) ^ n = (-1) ^ k * (-1) ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hkn]
  have hpow2 : (2 : ℂ) ^ (2 * n) = 2 ^ (2 * k) * 2 ^ (2 * (n - k)) := by
    rw [← pow_add]; congr 1; omega
  rw [hpow1, hpow2]
  field_simp



/-- The regularized `₀F₁` series converges absolutely everywhere. -/
theorem summable_norm_regularized0F1 (c w : ℂ) :
    Summable fun n : ℕ => ‖regularizedHGFunCoeff (∅ : Multiset ℂ) {c} n * w ^ n‖ := by
  have hr : (FormalMultilinearSeries.ofScalars ℂ (regularizedHGFunCoeff ∅ {c})).radius = ⊤ :=
    top_le_iff.mp (hasFPowerSeriesOnBall_regularized0F1 c).r_le
  have := (FormalMultilinearSeries.ofScalars ℂ (regularizedHGFunCoeff ∅ {c})).summable_norm_mul_pow
    (r := ‖w‖₊) (by rw [hr]; exact ENNReal.coe_lt_top)
  simpa [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow] using this


/-- `(a)ₖ / Γ(a + k) = 1 / Γ(a)` away from the poles of `Γ`. -/
theorem poch_div_Gamma_add_nat {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k) (k : ℕ) :
    poch a k / Complex.Gamma (a + k) = 1 / Complex.Gamma a := by
  have h := Complex.Gamma_add_nat_div_Gamma_eq (n := k) a ha
  have hG : Complex.Gamma a ≠ 0 := Complex.Gamma_ne_zero ha
  rw [poch, ← h]
  have hGk : Complex.Gamma (a + k) ≠ 0 := Complex.Gamma_ne_zero fun m hm =>
    ha (m + k) (by push_cast; linear_combination hm)
  field_simp


@[dlmf 18.12.E2]
theorem jacobi_regularized_generating_function {α β : ℂ} (hα : -1 < α.re)
    (hβ : -1 < β.re) (x z : ℂ) :
    HasSum (fun n : ℕ => jacobiPolyP α β n x / (Gamma (n + α + 1) * Gamma (n + β + 1)) * z ^ n)
      (regularizedHGFun (∅ : Multiset ℂ) {α + 1} ((x - 1) * z / 2) *
       regularizedHGFun (∅ : Multiset ℂ) {β + 1} ((x + 1) * z / 2)) := by
  set u := (x - 1) * z / 2
  set v := (x + 1) * z / 2
  have hu := summable_norm_regularized0F1 (α + 1) u
  have hv := summable_norm_regularized0F1 (β + 1) v
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hv hu
  have hsum := (summable_norm_sum_mul_antidiagonal_of_summable_norm hv hu).of_norm.hasSum
  rw [← hprod, ((hasFPowerSeriesOnBall_regularized0F1 (β + 1)).hasSum_mul_pow
      (by simp)).tsum_eq, ((hasFPowerSeriesOnBall_regularized0F1 (α + 1)).hasSum_mul_pow
      (by simp)).tsum_eq] at hsum
  rw [mul_comm]
  refine hsum.congr_fun fun n => ?_
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, jacobi_binomial_sum hα, Finset.mul_sum,
    Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hA : poch (α + n - k + 1) k / Gamma (n + α + 1) = 1 / Gamma (α + 1 + (n - k : ℕ)) := by
    have := poch_div_Gamma_add_nat (a := α + 1 + (n - k : ℕ)) (not_neg_nat_of_re_pos (by
      simp only [Complex.add_re, Complex.one_re, Complex.natCast_re]
      linarith [(Nat.cast_nonneg (α := ℝ) (n - k))])) k
    rw [← this]
    congr 1
    · congr 1; push_cast [Nat.cast_sub hkn]; ring
    · congr 1; push_cast [Nat.cast_sub hkn]; ring
  have hB : poch (β + k + 1) (n - k) / Gamma (n + β + 1) = 1 / Gamma (β + 1 + k) := by
    have := poch_div_Gamma_add_nat (a := β + 1 + k) (not_neg_nat_of_re_pos (by
      simp only [Complex.add_re, Complex.one_re, Complex.natCast_re]
      linarith [(Nat.cast_nonneg (α := ℝ) k)])) (n - k)
    rw [← this]
    congr 1
    · congr 1; ring
    · congr 1; push_cast [Nat.cast_sub hkn]; ring
  simp only [regularizedHGFunCoeff_empty]
  have hGA : Gamma (n + α + 1) ≠ 0 := Complex.Gamma_ne_zero (not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re, Complex.natCast_re]
    linarith [(Nat.cast_nonneg (α := ℝ) n)]))
  have hGB : Gamma (n + β + 1) ≠ 0 := Complex.Gamma_ne_zero (not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re, Complex.natCast_re]
    linarith [(Nat.cast_nonneg (α := ℝ) n)]))
  rw [div_eq_iff hGA] at hA
  rw [div_eq_iff hGB] at hB
  have hzn : z ^ n = z ^ k * z ^ (n - k) := by rw [← pow_add, Nat.add_sub_cancel' hkn]
  have h2n : (2 : ℂ) ^ n = 2 ^ k * 2 ^ (n - k) := by rw [← pow_add, Nat.add_sub_cancel' hkn]
  rw [hA, hB, hzn, h2n]
  simp only [u, v, div_pow, mul_pow]
  field_simp

section JacobiBrafman

open Metric Set
open scoped ComplexConjugate

/-- The square of `R conj(1 - w)`, `R² = 1 - 2xw + w²`, is never a nonpositive real for
`|w| < 1`, `|x| ≤ 1`. -/
theorem jacB_sq_not_nonpos {x : ℝ} (hx : |x| ≤ 1) {w : ℂ} (hw : ‖w‖ < 1) :
    ¬ (((1 - 2 * x * w + w ^ 2) * conj (1 - w) ^ 2).im = 0 ∧
      ((1 - 2 * x * w + w ^ 2) * conj (1 - w) ^ 2).re ≤ 0) := by
  rintro ⟨him, hre⟩
  have hw2 : w.re ^ 2 + w.im ^ 2 < 1 := by
    have := Complex.sq_norm w
    rw [Complex.normSq_apply] at this
    nlinarith [norm_nonneg w]
  have e1 : ((1 - 2 * x * w + w ^ 2) * conj (1 - w) ^ 2).im =
      2 * (1 - x) * w.im * (1 - w.re ^ 2 - w.im ^ 2) := by
    simp only [pow_two, mul_im, mul_re, sub_re, sub_im, add_re, add_im, one_re, one_im,
      conj_re, conj_im, ofReal_re, ofReal_im, re_ofNat, im_ofNat]
    ring
  have e2 : ((1 - 2 * x * w + w ^ 2) * conj (1 - w) ^ 2).re =
      ((1 - w.re) ^ 2 + w.im ^ 2) ^ 2 +
        2 * (1 - x) * (w.re * (1 + w.re ^ 2 + w.im ^ 2) - 2 * (w.re ^ 2 + w.im ^ 2)) := by
    simp only [pow_two, mul_im, mul_re, sub_re, sub_im, add_re, add_im, one_re, one_im,
      conj_re, conj_im, ofReal_re, ofReal_im, re_ofNat, im_ofNat]
    ring
  rw [e1] at him
  rw [e2] at hre
  have hp1 : w.re < 1 := by nlinarith [sq_nonneg w.im]
  have hpos : 0 < 1 - w.re ^ 2 - w.im ^ 2 := by linarith
  have hxq : (1 - x) * w.im = 0 := by
    have : 2 * ((1 - x) * w.im) * (1 - w.re ^ 2 - w.im ^ 2) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  rcases mul_eq_zero.mp hxq with h | h
  · have hx1 : x = 1 := by linarith
    subst hx1
    nlinarith [sq_nonneg w.im, sq_pos_of_pos (sub_pos.mpr hp1)]
  · rw [h] at hre
    have hxp : x * w.re ≤ |w.re| := by
      calc x * w.re ≤ |x * w.re| := le_abs_self _
        _ = |x| * |w.re| := abs_mul _ _
        _ ≤ 1 * |w.re| := mul_le_mul_of_nonneg_right hx (abs_nonneg _)
        _ = |w.re| := one_mul _
    have hpa : |w.re| < 1 := by
      rw [h] at hw2
      have h3 := sq_lt_sq.mp (show w.re ^ 2 < 1 ^ 2 by linarith)
      simpa using h3
    have hq : 0 < 1 - 2 * x * w.re + w.re ^ 2 := by
      nlinarith [sq_abs w.re, sq_nonneg (1 - |w.re|)]
    have hfac : ((1 - w.re) ^ 2 + 0 ^ 2) ^ 2 +
        2 * (1 - x) * (w.re * (1 + w.re ^ 2 + 0 ^ 2) - 2 * (w.re ^ 2 + 0 ^ 2)) =
        (1 - w.re) ^ 2 * (1 - 2 * x * w.re + w.re ^ 2) := by ring
    rw [hfac] at hre
    have := mul_pos (sq_pos_of_pos (sub_pos.mpr hp1)) hq
    linarith

/-- `Re(R conj(1 - z)) > 0` on the unit disc, `R = (1 - 2xz + z²)^{1/2}` (principal branch). -/
theorem jacB_re_pos {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    0 < ((1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) * conj (1 - z)).re := by
  set g : ℂ → ℝ := fun w => ((1 - 2 * x * w + w ^ 2) ^ (1 / 2 : ℂ) * conj (1 - w)).re with hg
  have hne : ∀ w ∈ ball (0 : ℂ) 1, g w ≠ 0 := by
    intro w hw h0
    have hw1 : ‖w‖ < 1 := by simpa using hw
    have hR2 : ((1 - 2 * x * w + w ^ 2) ^ (1 / 2 : ℂ)) ^ 2 = 1 - 2 * x * w + w ^ 2 :=
      cpow_half_sq (slitPlane_ne_zero (jacGen_mem_slitPlane hx hw1))
    set s := (1 - 2 * x * w + w ^ 2) ^ (1 / 2 : ℂ) * conj (1 - w) with hs
    have hs2 : s ^ 2 = (1 - 2 * x * w + w ^ 2) * conj (1 - w) ^ 2 := by
      rw [hs, mul_pow, hR2]
    have hsre : s.re = 0 := h0
    have him : (s ^ 2).im = 0 := by rw [pow_two, mul_im, hsre]; ring
    have hre : (s ^ 2).re ≤ 0 := by
      rw [pow_two, mul_re, hsre]; nlinarith [sq_nonneg s.im]
    rw [hs2] at him hre
    exact jacB_sq_not_nonpos hx hw1 ⟨him, hre⟩
  have hcont : ContinuousOn g (ball 0 1) := by
    intro w hw
    have hw1 : ‖w‖ < 1 := by simpa using hw
    have hRd : DifferentiableAt ℂ (fun w : ℂ => (1 - 2 * x * w + w ^ 2) ^ (1 / 2 : ℂ)) w :=
      DifferentiableAt.cpow (f := fun w : ℂ => 1 - 2 * x * w + w ^ 2) (by fun_prop)
        (differentiableAt_const _) (jacGen_mem_slitPlane hx hw1)
    have : ContinuousAt (fun w : ℂ => (1 - 2 * x * w + w ^ 2) ^ (1 / 2 : ℂ) * conj (1 - w)) w :=
      hRd.continuousAt.mul ((Complex.continuous_conj.comp (by fun_prop)).continuousAt)
    exact (Complex.continuous_re.continuousAt.comp this).continuousWithinAt
  have hpc := (convex_ball (0 : ℂ) 1).isPreconnected.image g hcont
  have h0 : g 0 = 1 := by simp [hg]
  by_contra hle
  push Not at hle
  have hz' : z ∈ ball (0 : ℂ) 1 := by simpa using hz
  have h00 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by simp
  have hsub := hpc.Icc_subset (mem_image_of_mem g hz') (mem_image_of_mem g h00)
  obtain ⟨w, hw, hw0⟩ := hsub ⟨hle, by rw [h0]; exact zero_le_one⟩
  exact hne w hw hw0

/-- `|(1 - R - z)/2|² ≤ |z|` on the unit disc (the two roots of `4U² - 4(1-z)U + 2(1-x)z`
have product `(x-1)z/2`, and the one with the minus sign is the smaller). -/
theorem jacB_norm_sq_le {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖(1 - (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) - z) / 2‖ ^ 2 ≤ ‖z‖ := by
  set R := (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) with hR
  have hR2 : R ^ 2 = 1 - 2 * x * z + z ^ 2 :=
    cpow_half_sq (slitPlane_ne_zero (jacGen_mem_slitPlane hx hz))
  have hre := jacB_re_pos hx hz
  rw [← hR] at hre
  set A := 1 - z with hA
  have hle : ‖A - R‖ ≤ ‖A + R‖ := by
    have h1 : ‖A - R‖ ^ 2 ≤ ‖A + R‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub, Complex.normSq_add]
      have : (A * conj R).re = (R * conj A).re := by
        rw [show A * conj R = conj (R * conj A) by simp [mul_comm], Complex.conj_re]
      linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1
  have hprod : (1 - R - z) / 2 * ((A + R) / 2) = (x - 1) / 2 * z := by
    rw [hA]; linear_combination (-1 / 4 : ℂ) * hR2
  have hx1 : ‖((x : ℂ) - 1) / 2‖ ≤ 1 := by
    rw [norm_div, show ((x : ℂ) - 1) = ((x - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs]
    norm_num
    have := abs_le.mp hx
    rw [div_le_one two_pos, abs_le]; constructor <;> linarith
  have hU : ‖(1 - R - z) / 2‖ ≤ ‖(A + R) / 2‖ := by
    rw [norm_div, norm_div, show 1 - R - z = A - R by rw [hA]; ring]
    gcongr
  calc ‖(1 - R - z) / 2‖ ^ 2 = ‖(1 - R - z) / 2‖ * ‖(1 - R - z) / 2‖ := pow_two _
    _ ≤ ‖(1 - R - z) / 2‖ * ‖(A + R) / 2‖ := mul_le_mul_of_nonneg_left hU (norm_nonneg _)
    _ = ‖((x : ℂ) - 1) / 2‖ * ‖z‖ := by rw [← norm_mul, hprod, norm_mul]
    _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hx1 (norm_nonneg _)
    _ = ‖z‖ := one_mul _

/-- The companion bound `|(1 - R + z)/2|² ≤ |z|`, by `(x, z) ↦ (-x, -z)`. -/
theorem jacB_norm_sq_le' {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖(1 - (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) + z) / 2‖ ^ 2 ≤ ‖z‖ := by
  have h := jacB_norm_sq_le (x := -x) (by rwa [abs_neg]) (z := -z) (by rwa [norm_neg])
  have e : (1 - 2 * ((-x : ℝ) : ℂ) * -z + (-z) ^ 2) = 1 - 2 * x * z + z ^ 2 := by
    push_cast; ring
  rw [e, norm_neg, sub_neg_eq_add] at h
  exact h

/-- The antidiagonal sums of Appell's `F₄` at `((x-1)/2, (x+1)/2)` are Jacobi polynomials
(by 18.5.8). -/
theorem jacB_coeff {α β : ℂ} (hα : -1 < α.re) (hβ : -1 < β.re) (γ x : ℂ) (N : ℕ) :
    ∑ p ∈ Finset.antidiagonal N, appF4Coeff γ (α + β + 1 - γ) (α + 1) (β + 1) p.1 p.2 *
        ((x - 1) / 2) ^ p.1 * ((x + 1) / 2) ^ p.2 =
      poch γ N * poch (α + β + 1 - γ) N / (poch (α + 1) N * poch (β + 1) N) *
        jacobiPolyP α β N x := by
  have hpa : ∀ j, poch (α + 1) j ≠ 0 := poch_ne_zero_of_not_neg_nat
    (not_neg_nat_of_re_pos (by simp only [add_re, one_re]; linarith))
  have hpb : ∀ j, poch (β + 1) j ≠ 0 := poch_ne_zero_of_not_neg_nat
    (not_neg_nat_of_re_pos (by simp only [add_re, one_re]; linarith))
  rw [jacobi_binomial_sum hα N x, ← mul_assoc, Finset.mul_sum,
    ← Finset.Nat.sum_antidiagonal_swap]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun n m =>
      appF4Coeff γ (α + β + 1 - γ) (α + 1) (β + 1) m n * ((x - 1) / 2) ^ m * ((x + 1) / 2) ^ n)]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  rw [Nat.add_sub_cancel_left]
  have e1 : α + ((k + m : ℕ) : ℂ) - k + 1 = α + 1 + m := by push_cast; ring
  rw [e1]
  unfold appF4Coeff
  rw [add_comm k m, poch_add (α + 1) m k,
    show poch (β + 1) (m + k) = poch (β + 1) k * poch (β + 1 + k) m by rw [add_comm m k, poch_add],
    show β + (k : ℂ) + 1 = β + 1 + k by ring, pow_add, div_pow, div_pow]
  have := hpa m; have := hpb k
  have := hpa k; have := hpb m
  have hpa' : poch (α + 1 + m) k ≠ 0 := fun h => hpa (m + k) (by rw [poch_add, h, mul_zero])
  have hpb' : poch (β + 1 + k) m ≠ 0 := fun h => hpb (k + m) (by rw [poch_add, h, mul_zero])
  field_simp

/-- Regrouping a summable double series along antidiagonals. -/
theorem jacB_hasSum_antidiagonal {A : ℕ × ℕ → ℂ} {S : ℂ} (h : HasSum A S) :
    HasSum (fun n => ∑ p ∈ Finset.antidiagonal n, A p) S := by
  have h' := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff (f := A)).mpr h
  refine h'.sigma fun n => ?_
  have := hasSum_fintype (fun p : Finset.antidiagonal n => A p)
  rwa [Finset.sum_coe_sort] at this

/-- Brafman's generating function for small `|z|`, from Bailey's product formula
`appF4_bailey`: with `U = (1 - R - z)/2`, `V = (1 - R + z)/2` one has `U(1 - V) = (x-1)z/2`
and `V(1 - U) = (x+1)z/2`. -/
theorem jacB_hasSum_small {α β : ℂ} (hα : -1 < α.re) (hβ : -1 < β.re) (γ : ℂ) {x : ℝ}
    (hx : |x| ≤ 1) : ∃ ε > 0, ∀ z ∈ ball (0 : ℂ) ε,
    HasSum (fun n : ℕ => poch γ n * poch (α + β + 1 - γ) n /
      (poch (α + 1) n * poch (β + 1) n) * jacobiPolyP α β n x * z ^ n)
      (₂F₁ γ (α + β + 1 - γ) (α + 1) ((1 - (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) - z) / 2) *
       ₂F₁ γ (α + β + 1 - γ) (β + 1) ((1 - (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) + z) / 2)) := by
  have hcc : (α + 1) + (β + 1) = γ + (α + β + 1 - γ) + 1 := by ring
  obtain ⟨δ, hδ, hB⟩ := appF4_bailey hcc (by simp only [add_re, one_re]; linarith)
    (by simp only [add_re, one_re]; linarith)
  refine ⟨min (δ ^ 2) 1, lt_min (by positivity) one_pos, fun z hz => ?_⟩
  have hz' : ‖z‖ < min (δ ^ 2) 1 := by simpa using hz
  have hz1 : ‖z‖ < 1 := lt_of_lt_of_le hz' (min_le_right _ _)
  have hzδ : ‖z‖ < δ ^ 2 := lt_of_lt_of_le hz' (min_le_left _ _)
  have hUs := jacB_norm_sq_le hx hz1
  have hVs := jacB_norm_sq_le' hx hz1
  set R := (1 - 2 * (x : ℂ) * z + z ^ 2) ^ (1 / 2 : ℂ) with hR
  have hR2 : R ^ 2 = 1 - 2 * x * z + z ^ 2 :=
    cpow_half_sq (slitPlane_ne_zero (jacGen_mem_slitPlane hx hz1))
  have hU : ‖(1 - R - z) / 2‖ < δ :=
    (pow_lt_pow_iff_left₀ (norm_nonneg _) hδ.le two_ne_zero).mp (by linarith)
  have hV : ‖(1 - R + z) / 2‖ < δ :=
    (pow_lt_pow_iff_left₀ (norm_nonneg _) hδ.le two_ne_zero).mp (by linarith)
  have h := hB _ _ hU hV
  have e1 : (1 - R - z) / 2 * (1 - (1 - R + z) / 2) = (x - 1) / 2 * z := by
    linear_combination (-1 / 4 : ℂ) * hR2
  have e2 : (1 - R + z) / 2 * (1 - (1 - R - z) / 2) = (x + 1) / 2 * z := by
    linear_combination (-1 / 4 : ℂ) * hR2
  rw [e1, e2] at h
  have h2 := jacB_hasSum_antidiagonal h
  refine h2.congr_fun fun N => ?_
  rw [← jacB_coeff hα hβ γ x N, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  rw [← hp, mul_pow, mul_pow, pow_add]
  ring

/-- The right side of Brafman's formula is holomorphic on the unit disc. -/
theorem jacB_differentiableOn (α β γ : ℂ) {x : ℝ} (hx : |x| ≤ 1) :
    DifferentiableOn ℂ (fun z : ℂ =>
      ₂F₁ γ (α + β + 1 - γ) (α + 1) ((1 - (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) - z) / 2) *
       ₂F₁ γ (α + β + 1 - γ) (β + 1) ((1 - (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) + z) / 2))
      (ball 0 1) := by
  intro w hw
  have hw1 : ‖w‖ < 1 := by simpa using hw
  have hRd : DifferentiableAt ℂ (fun w : ℂ => (1 - 2 * x * w + w ^ 2) ^ (1 / 2 : ℂ)) w :=
    DifferentiableAt.cpow (f := fun w : ℂ => 1 - 2 * x * w + w ^ 2) (by fun_prop)
      (differentiableAt_const _) (jacGen_mem_slitPlane hx hw1)
  have hU1 : ‖(1 - (1 - 2 * x * w + w ^ 2) ^ (1 / 2 : ℂ) - w) / 2‖ < 1 :=
    (pow_lt_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp
      (lt_of_le_of_lt (jacB_norm_sq_le hx hw1) hw1)
  have hV1 : ‖(1 - (1 - 2 * x * w + w ^ 2) ^ (1 / 2 : ℂ) + w) / 2‖ < 1 :=
    (pow_lt_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp
      (lt_of_le_of_lt (jacB_norm_sq_le' hx hw1) hw1)
  have hUd : DifferentiableAt ℂ
      (fun w : ℂ => (1 - (1 - 2 * x * w + w ^ 2) ^ (1 / 2 : ℂ) - w) / 2) w :=
    (((differentiableAt_const _).sub hRd).sub differentiableAt_id).div_const 2
  have hVd : DifferentiableAt ℂ
      (fun w : ℂ => (1 - (1 - 2 * x * w + w ^ 2) ^ (1 / 2 : ℂ) + w) / 2) w :=
    (((differentiableAt_const _).sub hRd).add differentiableAt_id).div_const 2
  exact (((analyticAt_ordinaryHypergeometric hU1).differentiableAt.comp w hUd).mul
    ((analyticAt_ordinaryHypergeometric hV1).differentiableAt.comp w hVd)).differentiableWithinAt

end JacobiBrafman

@[dlmf 18.12.E2_5]
theorem jacobi_brafman_generating_function {α β : ℂ} (hα : -1 < α.re)
    (hβ : -1 < β.re) (γ : ℂ) {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1)
    (hu : ‖(1 - (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) - z) / 2‖ < 1)
    (hv : ‖(1 - (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) + z) / 2‖ < 1) :
    HasSum (fun n : ℕ => poch γ n * poch (α + β + 1 - γ) n /
      (poch (α + 1) n * poch (β + 1) n) * jacobiPolyP α β n x * z ^ n)
      (₂F₁ γ (α + β + 1 - γ) (α + 1) ((1 - (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) - z) / 2) *
       ₂F₁ γ (α + β + 1 - γ) (β + 1) ((1 - (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) + z) / 2)) := by
  -- `hu` and `hv` are redundant: they follow from `|z| < 1` (`jacB_norm_sq_le`).
  have _hu := hu
  have _hv := hv
  obtain ⟨ε, hε, hsmall⟩ := jacB_hasSum_small hα hβ γ hx
  exact Complex.lagB_hasSum_of_differentiableOn (c := fun n => poch γ n *
      poch (α + β + 1 - γ) n / (poch (α + 1) n * poch (β + 1) n) * jacobiPolyP α β n x)
    hε (jacB_differentiableOn α β γ hx) hsmall (by simpa using hz)

section JacobiWeighted

open Metric Set

/-- `|(μ)_m| ≤ (1 + |μ|)^m m!`. -/
theorem jacW_norm_poch_le (μ : ℂ) (m : ℕ) : ‖poch μ m‖ ≤ (1 + ‖μ‖) ^ m * m ! := by
  exact appF4_norm_poch_le μ m

/-- `k! ≤ (1 + 1/(Re β + 1))^k |(β+1)_k|` for `Re β > -1`. -/
theorem jacW_factorial_le_norm_poch {β : ℂ} (hβ : -1 < β.re) (k : ℕ) :
    (k ! : ℝ) ≤ (1 + 1 / (β.re + 1)) ^ k * ‖poch (β + 1) k‖ := by
  have hσ : 0 < β.re + 1 := by linarith
  induction k with
  | zero => simp [poch_zero]
  | succ k ih =>
    rw [poch_succ, norm_mul, Nat.factorial_succ, pow_succ]
    have h1 : (β.re + 1 + k) ≤ ‖β + 1 + k‖ := by
      have := Complex.re_le_norm (β + 1 + k)
      simpa using this
    have h2 : ((k : ℝ) + 1) ≤ (1 + 1 / (β.re + 1)) * ‖β + 1 + k‖ := by
      have h3 : ((k : ℝ) + 1) ≤ (1 + 1 / (β.re + 1)) * (β.re + 1 + k) := by
        rw [add_mul, one_div, inv_mul_eq_div, add_div, div_self hσ.ne']
        have : 0 ≤ (k : ℝ) / (β.re + 1) := by positivity
        linarith
      exact h3.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
    push_cast
    calc ((k : ℝ) + 1) * k ! ≤ ((1 + 1 / (β.re + 1)) * ‖β + 1 + k‖) *
          ((1 + 1 / (β.re + 1)) ^ k * ‖poch (β + 1) k‖) :=
          mul_le_mul h2 ih (by positivity) (by positivity)
      _ = _ := by ring

/-- `(2k+m)! ≤ 2^{2k+m} 4^k k!² m!`. -/
theorem jacW_factorial_two_mul_add_le (k m : ℕ) :
    ((2 * k + m)! : ℝ) ≤ 2 ^ (2 * k + m) * 4 ^ k * (k ! * k ! * m !) := by
  have h1 : (2 * k + m)! = (2 * k + m).choose m * ((2 * k)! * m !) := by
    have := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left m (2 * k))
    rw [Nat.add_sub_cancel] at this
    rw [← this]; ring
  have h2 : (2 * k)! = (2 * k).choose k * (k ! * k !) := by
    have := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
    rw [show 2 * k - k = k by omega] at this
    rw [← this]; ring
  have hc1 : ((2 * k + m).choose m : ℝ) ≤ 2 ^ (2 * k + m) := by
    exact_mod_cast Nat.choose_le_two_pow _ _
  have hc2 : ((2 * k).choose k : ℝ) ≤ 4 ^ k := by
    have := Nat.choose_le_two_pow (2 * k) k
    rw [pow_mul] at this
    exact_mod_cast this
  rw [h1, h2]
  push_cast
  calc ((2 * k + m).choose m : ℝ) * (((2 * k).choose k : ℝ) * (k ! * k !) * m !)
      ≤ 2 ^ (2 * k + m) * (4 ^ k * (k ! * k !) * m !) := by gcongr
    _ = _ := by ring


/-- The double-series term behind 18.12.3:
`(λ)_{2k+m} (-1)^m y^k z^{k+m} / ((β+1)_k k! m!)`. -/
noncomputable def jacWTerm (l β y z : ℂ) (p : ℕ × ℕ) : ℂ :=
  poch l (2 * p.1 + p.2) * (-1) ^ p.2 * y ^ p.1 * z ^ (p.1 + p.2) /
    (poch (β + 1) p.1 * p.1 ! * p.2 !)

/-- A geometric bound for `jacWTerm`. -/
theorem jacWTerm_norm_le (l : ℂ) {β : ℂ} (hβ : -1 < β.re) {y : ℂ} (hy : ‖y‖ ≤ 1) (z : ℂ)
    (p : ℕ × ℕ) : ‖jacWTerm l β y z p‖ ≤
      (16 * (1 + ‖l‖) ^ 2 * (1 + 1 / (β.re + 1)) * ‖z‖) ^ p.1 * (2 * (1 + ‖l‖) * ‖z‖) ^ p.2 := by
  obtain ⟨k, m⟩ := p
  simp only
  have hσ : 0 < β.re + 1 := by linarith
  have hP := jacW_factorial_le_norm_poch hβ k
  have hPpos : 0 < ‖poch (β + 1) k‖ := by
    by_contra h
    push Not at h
    have h0 : ‖poch (β + 1) k‖ = 0 := le_antisymm h (norm_nonneg _)
    rw [h0, mul_zero] at hP
    exact absurd hP (not_le.mpr (by exact_mod_cast k.factorial_pos))
  have hL := jacW_norm_poch_le l (2 * k + m)
  have hF := jacW_factorial_two_mul_add_le k m
  have hk : (0 : ℝ) < k ! := by exact_mod_cast k.factorial_pos
  have hm : (0 : ℝ) < m ! := by exact_mod_cast m.factorial_pos
  unfold jacWTerm
  rw [norm_div, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow,
    norm_neg, norm_one, one_pow, mul_one, Complex.norm_natCast, Complex.norm_natCast,
    div_le_iff₀ (by positivity)]
  have hyk : ‖y‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) hy
  have hz := norm_nonneg z
  have hl := norm_nonneg l
  calc ‖poch l (2 * k + m)‖ * ‖y‖ ^ k * ‖z‖ ^ (k + m)
      ≤ ((1 + ‖l‖) ^ (2 * k + m) * (2 * k + m)!) * 1 * ‖z‖ ^ (k + m) := by gcongr
    _ ≤ ((1 + ‖l‖) ^ (2 * k + m) * (2 ^ (2 * k + m) * 4 ^ k * (k ! * k ! * m !))) * 1 *
          ‖z‖ ^ (k + m) := by gcongr
    _ ≤ ((1 + ‖l‖) ^ (2 * k + m) * (2 ^ (2 * k + m) * 4 ^ k *
          (((1 + 1 / (β.re + 1)) ^ k * ‖poch (β + 1) k‖) * k ! * m !))) * 1 *
          ‖z‖ ^ (k + m) := by gcongr
    _ = _ := by
      simp only [mul_pow, ← pow_mul, pow_add]
      rw [show (16 : ℝ) = 2 ^ 2 * 4 by norm_num, mul_pow, ← pow_mul]
      ring


/-- Duplication for rising factorials: `(2a)_{2m} = 4^m (a)_m (a + 1/2)_m`. -/
theorem jacW_poch_two_mul (a : ℂ) (m : ℕ) :
    poch (2 * a) (2 * m) = 4 ^ m * poch a m * poch (a + 1 / 2) m := by
  exact poch_two_mul_two_mul a m

/-- The `m`-sums of `jacWTerm` are binomial series. -/
theorem jacWTerm_hasSum_fiber (l β y : ℂ) {z : ℂ} (hz : ‖z‖ < 1) (k : ℕ) :
    HasSum (fun m => jacWTerm l β y z (k, m))
      (poch l (2 * k) / (poch (β + 1) k * k !) * (y * z) ^ k * (1 + z) ^ (-(l + 2 * k))) := by
  have hz' : ‖-z‖ < 1 := by rwa [norm_neg]
  have h := (hasSum_poch_div_factorial (β := l + 2 * k) hz').mul_left
    (poch l (2 * k) / (poch (β + 1) k * k !) * (y * z) ^ k)
  rw [sub_neg_eq_add] at h
  refine h.congr_fun fun m => ?_
  unfold jacWTerm
  simp only
  rw [poch_add, show l + ((2 * k : ℕ) : ℂ) = l + 2 * k by push_cast; ring]
  have h1 : (m ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  rw [neg_pow z, pow_add, mul_pow]
  by_cases hp : poch (β + 1) k = 0
  · simp [hp]
  have h2 : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  field_simp

/-- The `k`-sum of the fibre sums is `(1+z)^{-λ} ₂F₁(λ/2, λ/2 + 1/2; β+1; 4yz/(1+z)²)`. -/
theorem jacWTerm_hasSum_outer (l β y : ℂ) {z : ℂ} (hz : ‖z‖ < 1)
    (hv : ‖4 * y * z / (1 + z) ^ 2‖ < 1) :
    HasSum (fun k : ℕ => poch l (2 * k) / (poch (β + 1) k * k !) * (y * z) ^ k *
      (1 + z) ^ (-(l + 2 * k)))
      ((1 + z) ^ (-l) * ₂F₁ (l / 2) (l / 2 + 1 / 2) (β + 1) (4 * y * z / (1 + z) ^ 2)) := by
  have hz0 : 1 + z ≠ 0 := by
    intro h
    have : z = -1 := by linear_combination h
    rw [this] at hz; simp at hz
  have h := ((hasFPowerSeriesOnBall_ordinaryHypergeometric (l / 2) (l / 2 + 1 / 2)
    (β + 1)).hasSum_mul_pow (mem_eball_one_of_norm_lt_one hv)).mul_left ((1 + z) ^ (-l))
  refine h.congr_fun fun k => ?_
  have hpoch : poch l (2 * k) = 4 ^ k * poch (l / 2) k * poch (l / 2 + 1 / 2) k := by
    have := jacW_poch_two_mul (l / 2) k
    rwa [show 2 * (l / 2) = l by ring] at this
  have hcp : (1 + z) ^ (-(l + 2 * k)) = (1 + z) ^ (-l) * (((1 + z) ^ 2) ^ k)⁻¹ := by
    rw [neg_add, cpow_add _ _ hz0, cpow_neg (1 + z) (2 * k),
      show (2 : ℂ) * k = ((2 * k : ℕ) : ℂ) by push_cast; ring, cpow_natCast, pow_mul]
  rw [hcp, hpoch, gaussHGCoeff, div_pow, mul_pow, mul_pow, mul_pow]
  by_cases hp : poch (β + 1) k = 0
  · simp [hp]
  have h2 : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have h3 : ((1 + z) ^ 2) ^ k ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hz0)
  field_simp

/-- The Jacobi coefficient of 18.12.3 as an antidiagonal sum of `jacWTerm`. -/
theorem jacW_coeff_eq_sum_antidiagonal {α β : ℂ} (hα : -1 < α.re) (hβ : -1 < β.re) (x z : ℂ)
    (n : ℕ) :
    poch (α + β + 1) n / poch (β + 1) n * jacobiPolyP α β n x * z ^ n =
      ∑ p ∈ Finset.antidiagonal n, jacWTerm (α + β + 1) β ((x + 1) / 2) z p := by
  have hβ' : ∀ k : ℕ, β + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have hrefl := jacobi_reflection hα hβ n (-x)
  rw [neg_neg] at hrefl
  rw [hrefl, jacobi_finite_sum hβ n (-x),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => jacWTerm (α + β + 1) β
      ((x + 1) / 2) z (i, j)), Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  obtain ⟨m, rfl⟩ : ∃ m, n = k + m := ⟨n - k, by omega⟩
  rw [Nat.add_sub_cancel_left]
  unfold jacWTerm
  simp only
  rw [show 2 * k + m = (k + m) + k by ring, poch_add (α + β + 1) (k + m) k,
    poch_add (β + 1) k m]
  have hpk := poch_ne_zero_of_not_neg_nat hβ' k
  have hpm : poch (β + 1 + k) m ≠ 0 := by
    have : ∀ j : ℕ, β + 1 + k ≠ -(j : ℂ) := not_neg_nat_of_re_pos (by
      simp only [Complex.add_re, Complex.one_re, Complex.natCast_re]
      linarith [(Nat.cast_nonneg (α := ℝ) k)])
    exact poch_ne_zero_of_not_neg_nat this m
  have h1 : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have h2 : (m ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  rw [show ((k + m : ℕ) : ℂ) + β + α + 1 = α + β + 1 + ((k + m : ℕ) : ℂ) by ring,
    show β + k + 1 = β + 1 + k by ring, show (-x - 1) / 2 = -1 * ((x + 1) / 2) by ring,
    mul_pow]
  have hsq : (-1 : ℂ) ^ k * (-1) ^ k = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  calc _ = poch (α + β + 1) (k + m) * poch (α + β + 1 + ↑(k + m)) k * ((-1) ^ k * (-1) ^ k) *
        (-1) ^ m * ((x + 1) / 2) ^ k * z ^ (k + m) / (poch (β + 1) k * ↑k ! * ↑m !) := by
          field_simp
          rw [pow_add (-1 : ℂ) k m]
          ring
    _ = _ := by rw [hsq, mul_one]


/-- Regrouping a summable double series along antidiagonals. -/
theorem jacW_hasSum_antidiagonal {A : ℕ × ℕ → ℂ} {S : ℂ} (h : HasSum A S) :
    HasSum (fun n => ∑ p ∈ Finset.antidiagonal n, A p) S := by
  exact jacB_hasSum_antidiagonal h

/-- 18.12.3 for small `|z|`, by summing the double series in two ways. -/
theorem jacW_hasSum_small {α β : ℂ} (hα : -1 < α.re) (hβ : -1 < β.re) {x : ℝ} (hx : |x| ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 1 / (32 * ((1 + ‖α + β + 1‖) ^ 2 * (1 + 1 / (β.re + 1))))) :
    HasSum (fun n : ℕ => poch (α + β + 1) n / poch (β + 1) n * jacobiPolyP α β n x * z ^ n)
      ((1 + z) ^ (-α - β - 1) * ₂F₁ ((α + β + 1) / 2) ((α + β + 2) / 2)
        (β + 1) (2 * (x + 1 : ℂ) * z / (1 + z) ^ 2)) := by
  set l := α + β + 1 with hl
  set y : ℂ := ((x : ℂ) + 1) / 2 with hy
  have hσ : 0 < β.re + 1 := by linarith
  set K := (1 + ‖l‖) ^ 2 * (1 + 1 / (β.re + 1)) with hK
  have hl0 := norm_nonneg l
  have hK1 : 1 ≤ K := by
    have h1 : 1 ≤ (1 + ‖l‖) ^ 2 := one_le_pow₀ (by linarith)
    have h2 : 1 ≤ 1 + 1 / (β.re + 1) := by have : 0 < 1 / (β.re + 1) := by positivity
                                           linarith
    nlinarith
  have hz0 := norm_nonneg z
  have hKz : K * ‖z‖ < 1 / 32 := by
    rw [lt_div_iff₀ (by positivity)] at hz
    nlinarith
  have hz32 : ‖z‖ < 1 / 32 := by nlinarith
  have hz1 : ‖z‖ < 1 := by linarith
  have hy1 : ‖y‖ ≤ 1 := by
    rw [hy, show ((x : ℂ) + 1) / 2 = (((x + 1) / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [(abs_le.mp hx).1, (abs_le.mp hx).2]
  -- summability of the double series
  set P := 16 * (1 + ‖l‖) ^ 2 * (1 + 1 / (β.re + 1)) * ‖z‖ with hP
  set Q := 2 * (1 + ‖l‖) * ‖z‖ with hQ
  have hP0 : 0 ≤ P := by positivity
  have hQ0 : 0 ≤ Q := by positivity
  have hP1 : P < 1 := by
    have : P = 16 * (K * ‖z‖) := by rw [hP, hK]; ring
    rw [this]; linarith
  have hQ1 : Q < 1 := by
    have h1 : 2 * (1 + ‖l‖) ≤ 2 * K := by
      have : 1 + ‖l‖ ≤ (1 + ‖l‖) ^ 2 := by nlinarith
      have h3 : (1 + ‖l‖) ^ 2 ≤ K := by
        rw [hK]; have : 0 < 1 / (β.re + 1) := by positivity
        nlinarith
      linarith
    have : Q ≤ 2 * (K * ‖z‖) := by rw [hQ]; nlinarith
    linarith
  have hsum : Summable (jacWTerm l β y z) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hP0 hP1).mul_of_nonneg
      (summable_geometric_of_lt_one hQ0 hQ1) (fun _ => by positivity) (fun _ => by positivity))
      (fun p => ?_)
    exact jacWTerm_norm_le l hβ hy1 z p
  -- the argument of `₂F₁`
  have hz1' : 31 / 32 ≤ ‖1 + z‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-z)
    rw [norm_one, norm_neg, sub_neg_eq_add] at this
    linarith
  have hv : ‖4 * y * z / (1 + z) ^ 2‖ < 1 := by
    rw [norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_ofNat,
      div_lt_one (by positivity)]
    have : (31 / 32 : ℝ) ^ 2 ≤ ‖1 + z‖ ^ 2 := by gcongr
    nlinarith [norm_nonneg y]
  -- sum by fibres and by antidiagonals
  have hfib := hsum.hasSum.prod_fiberwise (fun k => jacWTerm_hasSum_fiber l β y hz1 k)
  have hval := (jacWTerm_hasSum_outer l β y hz1 hv).unique hfib
  have hanti := jacW_hasSum_antidiagonal hsum.hasSum
  rw [← hval] at hanti
  convert hanti using 1
  · funext n
    exact jacW_coeff_eq_sum_antidiagonal hα hβ (x : ℂ) z n
  · rw [show -α - β - 1 = -l by rw [hl]; ring, show (α + β + 1) / 2 = l / 2 by rw [hl],
      show (α + β + 2) / 2 = l / 2 + 1 / 2 by rw [hl]; ring,
      show 2 * ((x : ℂ) + 1) * z = 4 * y * z by rw [hy]; ring]


/-- The coefficients of 18.12.3 have radius of convergence at least `1`: for `0 ≤ r < 1`,
`|(α+β+1)_n/(β+1)_n P_n^{(α,β)}(x)| rⁿ → 0`, by 18.12.1 and the Gauss series. -/
theorem jacW_tendsto_coeff {α β : ℂ} (hα : -1 < α.re) (hβ : -1 < β.re) {x : ℝ} (hx : |x| ≤ 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Tendsto (fun n : ℕ => ‖poch (α + β + 1) n / poch (β + 1) n * jacobiPolyP α β n x‖ * r ^ n)
      atTop (𝓝 0) := by
  set s := Real.sqrt r with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg r
  have hs1 : s < 1 := by rw [hs, Real.sqrt_lt' one_pos]; simpa using hr
  have hss : s * s = r := Real.mul_self_sqrt hr0
  -- the Jacobi factor
  have hsn : ‖(s : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
  have hJ := (jacobi_generating_function hα hβ hx hsn).summable.norm.tendsto_atTop_zero
  -- the Pochhammer factor
  have hrad := (hasFPowerSeriesOnBall_ordinaryHypergeometric (α + β + 1) 1 (β + 1)).r_le
  have hsr : ((s.toNNReal : NNReal) : ENNReal) <
      (FormalMultilinearSeries.ofScalars ℂ (gaussHGCoeff (α + β + 1) 1 (β + 1))).radius :=
    lt_of_lt_of_le (by rw [ENNReal.coe_lt_one_iff, Real.toNNReal_lt_one]; exact hs1) hrad
  have hG := ((FormalMultilinearSeries.ofScalars ℂ
    (gaussHGCoeff (α + β + 1) 1 (β + 1))).summable_norm_mul_pow hsr).tendsto_atTop_zero
  have := hG.mul hJ
  rw [zero_mul] at this
  refine this.congr fun n => ?_
  rw [FormalMultilinearSeries.ofScalars_norm, gaussHGCoeff, poch_nat_one, norm_mul, norm_mul,
    norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0, Real.coe_toNNReal _ hs0,
    ← hss, mul_pow]
  have hf : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  rw [mul_div_mul_right _ _ hf]
  ring


/-- Star-convexity of the domain of 18.12.3: shrinking `z` towards `0` decreases
`|z / (1 + z)²|` (`|1 + bz|² - b|1 + z|² = (1 - b)(1 - b|z|²)`). -/
theorem jacW_norm_div_sq_le {z : ℂ} (hz : ‖z‖ < 1) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ‖(b : ℂ) * z / (1 + (b : ℂ) * z) ^ 2‖ ≤ ‖z / (1 + z) ^ 2‖ := by
  have hz2 : z.re ^ 2 + z.im ^ 2 < 1 := by
    have := Complex.sq_norm z
    rw [Complex.normSq_apply] at this
    nlinarith [norm_nonneg z]
  have hne : ∀ c : ℂ, ‖c‖ < 1 → 1 + c ≠ 0 := fun c hc h => by
    have : c = -1 := by linear_combination h
    rw [this] at hc; simp at hc
  have hbz : ‖(b : ℂ) * z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb0]
    nlinarith [norm_nonneg z]
  have h1 := hne z hz
  have h2 := hne _ hbz
  rw [norm_div, norm_div, norm_pow, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hb0, div_le_div_iff₀ (by positivity) (by positivity)]
  have key : b * ‖1 + z‖ ^ 2 ≤ ‖1 + (b : ℂ) * z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [add_re, one_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, add_im, one_im,
      mul_im, zero_add]
    nlinarith [mul_nonneg (sub_nonneg.2 hb1) (mul_nonneg hb0 (sub_nonneg.2 hz2.le))]
  have := mul_le_mul_of_nonneg_left key (norm_nonneg z)
  nlinarith [norm_nonneg z]

/-- The coefficient series of 18.12.3 has radius at least `1`. -/
theorem jacW_one_le_radius {α β : ℂ} (hα : -1 < α.re) (hβ : -1 < β.re) {x : ℝ} (hx : |x| ≤ 1) :
    1 ≤ (FormalMultilinearSeries.ofScalars ℂ
      (fun n : ℕ => poch (α + β + 1) n / poch (β + 1) n * jacobiPolyP α β n x)).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  have hr1 : (r : ℝ) < 1 := by exact_mod_cast hr
  refine FormalMultilinearSeries.le_radius_of_tendsto _ (l := 0) ?_
  refine (jacW_tendsto_coeff hα hβ hx r.2 hr1).congr fun n => ?_
  rw [FormalMultilinearSeries.ofScalars_norm]
  rfl

end JacobiWeighted

open Metric Set in
@[dlmf 18.12.E3]
theorem jacobi_weighted_generating_function {α β : ℂ} (hα : -1 < α.re)
    (hβ : -1 < β.re) {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1)
    (hu : ‖2 * (x + 1 : ℂ) * z / (1 + z) ^ 2‖ < 1) :
    HasSum (fun n : ℕ => poch (α + β + 1) n / poch (β + 1) n * jacobiPolyP α β n x * z ^ n)
      ((1 + z) ^ (-α - β - 1) * ₂F₁ ((α + β + 1) / 2) ((α + β + 2) / 2)
        (β + 1) (2 * (x + 1 : ℂ) * z / (1 + z) ^ 2)) := by
  set c : ℕ → ℂ := fun n => poch (α + β + 1) n / poch (β + 1) n * jacobiPolyP α β n x with hc
  set p := FormalMultilinearSeries.ofScalars ℂ c with hp
  have hrad : 1 ≤ p.radius := jacW_one_le_radius hα hβ hx
  have hF : HasFPowerSeriesOnBall p.sum p 0 1 :=
    (p.hasFPowerSeriesOnBall (lt_of_lt_of_le one_pos hrad)).mono one_pos hrad
  have hFsum : ∀ w : ℂ, ‖w‖ < 1 → HasSum (fun n => c n * w ^ n) (p.sum w) := by
    intro w hw
    have := hF.hasSum (mem_eball_one_of_norm_lt_one hw)
    simpa [hp, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using this
  -- the right side and its domain
  set v : ℂ → ℂ := fun w => 2 * (x + 1 : ℂ) * w / (1 + w) ^ 2 with hv
  set G : ℂ → ℂ := fun w => (1 + w) ^ (-α - β - 1) *
    ₂F₁ ((α + β + 1) / 2) ((α + β + 2) / 2) (β + 1) (v w) with hG
  have hne : ∀ w : ℂ, ‖w‖ < 1 → 1 + w ≠ 0 := fun w hw h => by
    have : w = -1 := by linear_combination h
    rw [this] at hw; simp at hw
  set D := ball (0 : ℂ) 1 ∩ v ⁻¹' ball 0 1 with hD
  have hD0 : (0 : ℂ) ∈ D := by simp [hD, hv]
  have hDs : StarConvex ℝ (0 : ℂ) D := by
    intro w hw a b ha hb hab
    obtain ⟨hw1, hw2⟩ := hw
    have hw1' : ‖w‖ < 1 := by simpa using hw1
    have hb1 : b ≤ 1 := by linarith
    simp only [smul_zero, zero_add, Complex.real_smul]
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb]
      nlinarith [norm_nonneg w]
    · have h2 : ‖v w‖ < 1 := by simpa using hw2
      rw [Set.mem_preimage, mem_ball_zero_iff]
      have hle := jacW_norm_div_sq_le hw1' hb hb1
      have e1 : v (b * w) = 2 * (x + 1 : ℂ) * ((b : ℂ) * w / (1 + (b : ℂ) * w) ^ 2) := by
        rw [hv]; ring
      have e2 : v w = 2 * (x + 1 : ℂ) * (w / (1 + w) ^ 2) := by rw [hv]; ring
      rw [e1, norm_mul]
      rw [e2, norm_mul] at h2
      calc _ ≤ ‖2 * ((x : ℂ) + 1)‖ * ‖w / (1 + w) ^ 2‖ :=
            mul_le_mul_of_nonneg_left hle (norm_nonneg _)
        _ < 1 := h2
  have hGa : AnalyticOnNhd ℂ G D := by
    intro w hw
    obtain ⟨hw1, hw2⟩ := hw
    have hw1' : ‖w‖ < 1 := by simpa using hw1
    have hw2' : ‖v w‖ < 1 := by simpa using hw2
    have hre : 0 < (1 + w).re := by
      have := Complex.abs_re_le_norm w
      simp only [add_re, one_re]; linarith [(abs_le.mp this).1]
    have hvA : AnalyticAt ℂ v w := by
      have := hne w hw1'
      exact AnalyticAt.div (f := fun w : ℂ => 2 * (x + 1 : ℂ) * w)
        (g := fun w : ℂ => (1 + w) ^ 2) (by fun_prop) (by fun_prop) (pow_ne_zero 2 this)
    have h1 : AnalyticAt ℂ (fun w : ℂ => (1 + w) ^ (-α - β - 1)) w :=
      AnalyticAt.cpow (by fun_prop) analyticAt_const (Or.inl hre)
    have h2 := (analyticAt_ordinaryHypergeometric (a := (α + β + 1) / 2) (b := (α + β + 2) / 2)
      (c := β + 1) hw2').comp hvA
    exact h1.mul h2
  have hFa : AnalyticOnNhd ℂ p.sum D := fun w hw =>
    hF.analyticAt_of_mem (mem_eball_one_of_norm_lt_one (by simpa using hw.1))
  -- agreement near `0`
  set δ := 1 / (32 * ((1 + ‖α + β + 1‖) ^ 2 * (1 + 1 / (β.re + 1)))) with hδ
  have hσ : 0 < β.re + 1 := by linarith
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hev : p.sum =ᶠ[𝓝 0] G := by
    filter_upwards [ball_mem_nhds (0 : ℂ) (lt_min hδ0 one_pos)] with w hw
    have hw' : ‖w‖ < min δ 1 := by simpa using hw
    exact (hFsum w (lt_of_lt_of_le hw' (min_le_right _ _))).unique
      (jacW_hasSum_small hα hβ hx (lt_of_lt_of_le hw' (min_le_left _ _)))
  have heq := hFa.eqOn_of_preconnected_of_eventuallyEq hGa
    (StarConvex.isPathConnected hDs hD0).isConnected.isPreconnected hD0 hev
  have hzD : z ∈ D := ⟨by simpa using hz, by simpa [hv] using hu⟩
  have := hFsum z hz
  rw [heq hzD] at this
  exact this

section AdjacentJacobiGenerating

set_option maxHeartbeats 1000000

/-- The adjacent Jacobi coefficients are consecutive Gegenbauer coefficients. -/
theorem jacobi_adjacent_coefficient {b : ℂ} (hb : -1 < b.re) (n : ℕ) (x : ℂ) :
    poch (2 * b + 2) (n + 1) / poch (b + 1) (n + 1) * jacobiPolyP (b + 1) b (n + 1) x =
      ultrasphPoly (b + 3 / 2) (n + 1) x + ultrasphPoly (b + 3 / 2) n x := by
  have ht : 0 < (b + 1).re := by simp; linarith
  have hp (k : ℕ) : poch (b + 2) k ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; linarith)) k
  have hb0 : b + 1 ≠ 0 := ne_zero_of_re_pos ht
  have hn0 : (n : ℂ) + b + 2 ≠ 0 := ne_zero_of_re_pos (by
    simp; linarith [Nat.cast_nonneg (α := ℝ) n])
  have hR := jacobi_raise_beta (α := b + 1) (β := b) (by simp; linarith) n x
  have hc (k : ℕ) : ultrasphPoly (b + 3 / 2) k x =
      poch (2 * b + 3) k / poch (b + 2) k * jacobiPolyP (b + 1) (b + 1) k x := by
    have hden : b + 3 / 2 + 1 / 2 = b + 2 := by ring
    have hnum : 2 * (b + 3 / 2) = 2 * b + 3 := by ring
    have hparam : b + 3 / 2 - 1 / 2 = b + 1 := by ring
    have h := ultrasphPoly_eq_jacobiPolyP (lam := b + 3 / 2) k x (by rw [hden]; exact hp k)
    simpa only [hden, hnum, hparam] using h
  rw [hc (n + 1), hc n]
  rw [show 2 * b + 2 = 2 * (b + 1) by ring,
    poch_succ_left (2 * (b + 1)) n, poch_succ_left (b + 1) n,
    show 2 * (b + 1) + 1 = 2 * b + 3 by ring,
    show b + 1 + 1 = b + 2 by ring,
    poch_succ (2 * b + 3) n, poch_succ (b + 2) n]
  have hn0' : b + 2 + (n : ℂ) ≠ 0 := by
    rw [show b + 2 + (n : ℂ) = (n : ℂ) + b + 2 by ring]
    exact hn0
  field_simp [hb0, hp n, hn0']
  linear_combination (poch (2 * b + 3) n) * hR

@[dlmf 18.12.E3_5]
theorem jacobi_adjacent_generating_function {β : ℂ} (hβ : -1 < β.re)
    {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => poch (2 * β + 2) n / poch (β + 1) n * jacobiPolyP (β + 1) β n x * z ^ n)
      ((1 + z) / (1 - 2 * x * z + z ^ 2) ^ (β + 3 / 2)) := by
  have h := ultrasphPoly_generating_function (lam := β + 3 / 2)
    (by simp; linarith) hx hz
  let f : ℕ → ℂ := fun n => if n = 0 then 0 else ultrasphPoly (β + 3 / 2) (n - 1) x * z ^ n
  have hs : HasSum f (z * (1 - 2 * x * z + z ^ 2) ^ (-(β + 3 / 2))) := by
    have hh := h.mul_left z
    have hshift : HasSum (fun n => f (n + 1)) (z * (1 - 2 * x * z + z ^ 2) ^ (-(β + 3 / 2))) := by
      simpa [f, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hh
    -- Mathlib's shifted-series identity includes the separate degree-zero term.
    have he := (hasSum_nat_add_iff 1).mp hshift
    simpa [f] using he
  have hh := h.add hs
  convert hh using 1
  · funext n
    cases n with
    | zero => simp [f, poch_zero]
    | succ n => simp only [f, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
                rw [jacobi_adjacent_coefficient hβ]
                ring
  · rw [cpow_neg]
    ring

end AdjacentJacobiGenerating

@[dlmf 18.12.E7]
theorem chebyshevT_poisson_generating_function {x : ℝ} (hx : |x| ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => 2 * (Chebyshev.T ℂ (n + 1)).eval (x : ℂ) * z ^ (n + 1))
      ((1 - z ^ 2) / (1 - 2 * x * z + z ^ 2) - 1) := by
  have hD := one_sub_two_mul_add_sq_ne_zero hx hz
  have h := ((hasSum_nat_add_iff' 1).mpr (chebyshevT_generating_function hx hz)).mul_left 2
  convert h using 1
  · funext n; push_cast; ring
  · simp only [Finset.sum_range_one, pow_zero, mul_one, Nat.cast_zero, Chebyshev.T_zero, eval_one]
    rw [div_sub_one hD, div_sub_one hD, ← mul_div_assoc]
    congr 1
    ring

/-- The exponential series in `ℂ`. -/
theorem hasSum_cexp (z : ℂ) : HasSum (fun n : ℕ => z ^ n / (n.factorial : ℂ)) (exp z) := by
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.expSeries_div_hasSum_exp z

/-- The exponential series converges absolutely. -/
theorem summable_norm_pow_div_factorial (z : ℂ) :
    Summable fun n : ℕ => ‖z ^ n / (n.factorial : ℂ)‖ := by
  simpa [norm_div, norm_pow] using Real.summable_pow_div_factorial ‖z‖

@[dlmf 18.12.E14]
theorem laguerrePolyL_bessel_generating_function {α : ℝ} (hα : -1 < α)
    {x z : ℝ} (hx : 0 < x) (hz : 0 < z) :
    HasSum (fun n : ℕ => laguerrePolyL α n x / poch (α + 1) n * (z : ℂ) ^ n)
      (Gamma (α + 1 : ℂ) * (x * z : ℂ) ^ (-α / 2 : ℂ) * exp z *
        besselJ α (2 * Real.sqrt (x * z))) := by
  have hc : ∀ k : ℕ, (α : ℂ) + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by simp; linarith)
  set w : ℂ := -((x : ℂ) * z)
  have hf := summable_norm_regularized0F1 (α + 1) w
  have hg := summable_norm_pow_div_factorial (z : ℂ)
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg
  have hsum := (summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg).of_norm.hasSum
  rw [← hprod, ((hasFPowerSeriesOnBall_regularized0F1 (α + 1)).hasSum_mul_pow
      (by simp)).tsum_eq, (hasSum_cexp _).tsum_eq] at hsum
  -- the Bessel prefactor
  have hxz : (0 : ℝ) < x * z := mul_pos hx hz
  have hbes : (x * z : ℂ) ^ (-α / 2 : ℂ) * besselJ α (2 * Real.sqrt (x * z)) =
      regularizedHGFun (∅ : Multiset ℂ) {(α : ℂ) + 1} w := by
    set t := x * z
    have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt hxz.le
    simp only [besselJ_eq_regularized]
    have harg : -((2 * (Real.sqrt t : ℂ)) ^ 2 / 4) = w := by
      simp only [w, t]
      rw [mul_pow, ← Complex.ofReal_pow, hsq]
      simp only [t]; push_cast; ring
    rw [harg, ← mul_assoc]
    convert one_mul _ using 2
    rw [show 2 * (Real.sqrt t : ℂ) / 2 = (Real.sqrt t : ℂ) by ring,
      show (x : ℂ) * z = (t : ℂ) by simp only [t]; push_cast; ring,
      show (-(α : ℂ) / 2) = ((-α / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hxz.le, ← Complex.ofReal_cpow (Real.sqrt_nonneg t),
      ← Complex.ofReal_mul, Real.sqrt_eq_rpow, ← Real.rpow_mul hxz.le, ← Real.rpow_add hxz,
      show -α / 2 + 1 / 2 * α = 0 by ring, Real.rpow_zero, Complex.ofReal_one]
  have hval : Gamma (α + 1 : ℂ) * (x * z : ℂ) ^ (-α / 2 : ℂ) * exp z *
      besselJ α (2 * Real.sqrt (x * z)) =
      Gamma (α + 1 : ℂ) * (regularizedHGFun (∅ : Multiset ℂ) {(α : ℂ) + 1} w * exp z) := by
    rw [← hbes]; ring
  rw [hval]
  refine (hsum.mul_left (Gamma (α + 1 : ℂ))).congr_fun fun n => ?_
  have hpos : 0 < ((α : ℂ) + 1).re := by simp; linarith
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← laguerreExtended_eq hc, laguerreExtended,
    Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hsplit : poch ((α : ℂ) + 1) n = poch ((α : ℂ) + 1) k * poch ((α : ℂ) + 1 + k) (n - k) := by
    rw [← poch_add, Nat.add_sub_cancel' hkn]
  have hG : Gamma ((α : ℂ) + 1 + k) = Gamma ((α : ℂ) + 1) * poch ((α : ℂ) + 1) k := by
    have := Complex.Gamma_add_nat_div_Gamma_eq (n := k) ((α : ℂ) + 1) hc
    rw [div_eq_iff (Complex.Gamma_ne_zero hc)] at this
    rw [this, poch]; ring
  have h1 : poch ((α : ℂ) + 1) k ≠ 0 := poch_ne_zero_of_re_pos hpos k
  have h2 : poch ((α : ℂ) + 1 + k) (n - k) ≠ 0 := poch_ne_zero_of_re_pos (by
    simp only [Complex.add_re, Complex.natCast_re] at hpos ⊢; positivity) (n - k)
  have h3 : Gamma ((α : ℂ) + 1) ≠ 0 := Complex.Gamma_ne_zero hc
  have hzn : (z : ℂ) ^ n = (z : ℂ) ^ k * (z : ℂ) ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hkn]
  rw [regularizedHGFunCoeff_empty, hG, hsplit, hzn, show (α : ℂ) + k + 1 = α + 1 + k by ring]
  have hw : w ^ k = (-1) ^ k * (x : ℂ) ^ k * (z : ℂ) ^ k := by
    simp only [w]; rw [neg_pow, mul_pow]; ring
  rw [hw, neg_pow (x : ℂ) k]
  field_simp

/-- The Laguerre generating function as a `HasSum`. -/
theorem hasSum_laguerrePolyL_generating_function {α x t : ℂ} (hα : ∀ k : ℕ, α + 1 ≠ -(k : ℂ))
    (ht : ‖t‖ < 1) :
    HasSum (fun n : ℕ => laguerrePolyL α n x * t ^ n)
        ((1 - t) ^ (-α - 1) * exp (-x * t / (1 - t))) := by
  have h := laguerrePolyL_generating_function (x := x) hα ht
  have h1t : (1 : ℂ) - t ≠ 0 := by
    intro h0
    have : t = 1 := by linear_combination -h0
    rw [this, norm_one] at ht; exact lt_irrefl _ ht
  have hne : (1 - t) ^ (-α - 1) * exp (-x * t / (1 - t)) ≠ 0 := by
    refine mul_ne_zero ?_ (exp_ne_zero _)
    rw [cpow_def_of_ne_zero h1t]; exact exp_ne_zero _
  have hs : Summable fun n : ℕ => laguerrePolyL α n x * t ^ n := by
    by_contra hns
    rw [tsum_eq_zero_of_not_summable hns] at h
    exact hne h
  rw [h]; exact hs.hasSum


/-- DLMF 18.12.17 prints the incorrect convergence condition `|z| < 1`
(checked 2026-09-16). The disk is `|z| < 1/2`: already at `x = 0`,
the even coefficients are `(-1)^k * (2*k)! / (k!)²`, with radius `1/2`. -/
@[dlmf 18.12.E17]
theorem hermitePolyH_half_factorial_generating_function (x : ℂ) {z : ℂ} (hz : ‖z‖ < 1 / 2) :
    HasSum (fun n : ℕ => aeval x (hermitePolyH n) / ((n / 2).factorial : ℂ) * z ^ n)
      ((1 + 2 * x * z + 4 * z ^ 2) / (1 + 4 * z ^ 2) ^ (3 / 2 : ℂ) *
        exp (4 * x ^ 2 * z ^ 2 / (1 + 4 * z ^ 2))) := by
  have ht : ‖-4 * z ^ 2‖ < 1 := by
    rw [norm_mul, norm_neg, norm_pow]
    have := norm_nonneg z
    norm_num; nlinarith
  have hw : (1 : ℂ) + 4 * z ^ 2 ≠ 0 := by
    intro h0
    have : -4 * z ^ 2 = 1 := by linear_combination -h0
    rw [this, norm_one] at ht; exact lt_irrefl _ ht
  have he := hasSum_laguerrePolyL_generating_function (α := -1 / 2) (x := x ^ 2)
    (not_neg_nat_of_re_pos (by norm_num)) ht
  have ho := (hasSum_laguerrePolyL_generating_function (α := 1 / 2) (x := x ^ 2)
    (not_neg_nat_of_re_pos (by norm_num)) ht).mul_left (2 * x * z)
  set E := exp (4 * x ^ 2 * z ^ 2 / (1 + 4 * z ^ 2))
  have hE : exp (-x ^ 2 * (-4 * z ^ 2) / (1 + 4 * z ^ 2)) = E := by
    congr 1; ring_nf
  rw [show (1 : ℂ) - -4 * z ^ 2 = 1 + 4 * z ^ 2 by ring, hE] at he ho
  set f : ℕ → ℂ := fun n => aeval x (hermitePolyH n) / ((n / 2).factorial : ℂ) * z ^ n with hf
  have hev : HasSum (fun m => f (2 * m))
      ((1 + 4 * z ^ 2) ^ (-(-1 / 2) - 1 : ℂ) * E) := by
    refine he.congr_fun fun m => ?_
    have hm : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    simp only [hf, show 2 * m / 2 = m by omega]
    rw [hermitePolyH_even_eq_laguerrePolyL, mul_pow, neg_pow (4 : ℂ),
      show z ^ (2 * m) = (z ^ 2) ^ m by rw [pow_mul],
      show (2 : ℂ) ^ (2 * m) = 4 ^ m by rw [pow_mul]; norm_num]
    field_simp
  have hod : HasSum (fun m => f (2 * m + 1))
      (2 * x * z * ((1 + 4 * z ^ 2) ^ (-(1 / 2) - 1 : ℂ) * E)) := by
    refine ho.congr_fun fun m => ?_
    have hm : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    simp only [hf, show (2 * m + 1) / 2 = m by omega]
    rw [hermitePolyH_odd_eq_laguerrePolyL, mul_pow, neg_pow (4 : ℂ),
      show z ^ (2 * m + 1) = z * (z ^ 2) ^ m by rw [pow_succ, pow_mul]; ring,
      show (2 : ℂ) ^ (2 * m + 1) = 2 * 4 ^ m by rw [pow_succ, pow_mul]; norm_num; ring]
    field_simp
  have hsum := hev.even_add_odd hod
  convert hsum using 1
  set w := (1 : ℂ) + 4 * z ^ 2
  have h1 : w ^ (-(-1 / 2) - 1 : ℂ) = w * (w ^ (3 / 2 : ℂ))⁻¹ := by
    rw [← cpow_neg, show (-(-1 / 2) - 1 : ℂ) = 1 + -(3 / 2) by norm_num, cpow_add _ _ hw, cpow_one]
  have h2 : w ^ (-(1 / 2) - 1 : ℂ) = (w ^ (3 / 2 : ℂ))⁻¹ := by
    rw [← cpow_neg]; norm_num
  rw [h1, h2]
  ring

end DLMF.OrthogonalPolynomials
