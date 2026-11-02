/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.Properties
public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import Mathlib.NumberTheory.ModularForms.Identities

/-!
# Bernoulli and Euler polynomials: series expansions

This file covers DLMF §24.8: the conditionally convergent boundary cases of the Fourier series
of the Bernoulli polynomials, the Fourier series of the Euler polynomials, and series
representations of the Bernoulli and Euler numbers.

## Main results

* `tendsto_sum_sin_div_eq_bernoulliFun_one`, `tendsto_sum_exp_div_eq_bernoulliFun_one`: DLMF
  24.8.2 with `n = 0` and 24.8.3 with `n = 1`, for `0 < x < 1`, as limits of natural
  (respectively symmetric) partial sums.
* `hasSum_sin_odd_eulerFun`, `hasSum_cos_odd_eulerFun`: the Fourier series of the Euler
  polynomials (DLMF 24.8.4, 24.8.5).
* `hasSum_bernoulli_four_mul_add_two`, `hasSum_bernoulli_two_mul_alt`,
  `bernoulli_two_mul_alpha_beta`: series for `B₂ₙ` (DLMF 24.8.6–24.8.8), from the modular
  transformation `E_k(-1/τ) = τ^k E_k(τ)` of Mathlib's level-one Eisenstein series and its
  `q`-expansion `EisensteinSeries.q_expansion_bernoulli`.
* `eulerNumber_two_mul_eq_series`: a series for `E₂ₙ` (DLMF 24.8.9).

## Implementation notes

The Fourier series 24.8.1, 24.8.2 (`n ≥ 1`) and 24.8.3 (`n ≥ 2`) are Mathlib's
`hasSum_one_div_nat_pow_mul_cos`, `hasSum_one_div_nat_pow_mul_sin` and
`hasSum_one_div_pow_mul_fourier_mul_bernoulliFun` (pointers in `DLMF.Core.UpstreamElementary`).
Series over `k ≥ 1` are written over `k + 1`, `k : ℕ`. In 24.8.8 and 24.8.9 two convergent
series are combined; their summability is part of the statement, so the `tsum`s are genuine
sums.
-/

@[expose] public section

noncomputable section

open Finset Filter Real
open scoped Nat Real Topology

namespace DLMF.BernoulliEuler

/-! ### Helpers -/

/-- Real form of DLMF 24.4.23: `Eₙ(x) = 2ⁿ⁺¹/(n+1) (Bₙ₊₁(x/2 + 1/2) - Bₙ₊₁(x/2))`. -/
private lemma eulerFun_eq_bernoulliFun_sub (n : ℕ) (x : ℝ) :
    eulerFun n x = 2 ^ (n + 1) / (n + 1) *
      (bernoulliFun (n + 1) (x / 2 + 1 / 2) - bernoulliFun (n + 1) (x / 2)) := by
  have h := eulerPolyE_eq_bernoulliPolyB_sub n x
  rw [eulerPolyE_ofReal, show (x : ℂ) / 2 + 1 / 2 = ((x / 2 + 1 / 2 : ℝ) : ℂ) by push_cast; ring,
    show (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) by push_cast; ring, bernoulliPolyB_ofReal,
    bernoulliPolyB_ofReal] at h
  have h' : ((eulerFun n x : ℝ) : ℂ) =
      ((2 ^ (n + 1) / (n + 1) * (bernoulliFun (n + 1) (x / 2 + 1 / 2) -
        bernoulliFun (n + 1) (x / 2)) : ℝ) : ℂ) := by push_cast; exact h
  exact_mod_cast h'

/-- Restricting a series vanishing at even indices to the odd indices. -/
private lemma hasSum_odd_of_even_eq_zero {f : ℕ → ℝ} {a : ℝ} (h : HasSum f a)
    (h0 : ∀ j, f (2 * j) = 0) :
    HasSum (fun k => f (2 * k + 1)) a := by
  have hinj : Function.Injective (fun m : ℕ => 2 * m + 1) := fun a b h => by simp at h; omega
  refine (hinj.hasSum_iff fun n hn => ?_).mpr h
  rcases Nat.even_or_odd n with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [← two_mul]; exact h0 j
  · exact absurd ⟨j, rfl⟩ hn

/-! ### §24.8(i) Fourier series -/

/-- The complex logarithmic series on the unit circle: for `w = e^{iθ}`, `0 < θ < 2π`, the partial
sums of `∑_{n≥1} wⁿ/n` converge to `-log(1 - w)` (Dirichlet's test and Abel's limit theorem). -/
private lemma tendsto_sum_exp_pow_div_neg_log {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 2 * π) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, Complex.exp (θ * Complex.I) ^ n / n) atTop
      (𝓝 (-Complex.log (1 - Complex.exp (θ * Complex.I)))) := by
  set w := Complex.exp (θ * Complex.I) with hw
  have hw1 : ‖w‖ = 1 := by rw [hw, Complex.norm_exp_ofReal_mul_I]
  have hwne : w ≠ 1 := by
    intro h
    rw [hw, Complex.exp_eq_one_iff] at h
    obtain ⟨k, hk⟩ := h
    have hk' : θ = 2 * π * k := by
      have := congrArg Complex.im hk
      simp at this; linarith
    rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
    · have : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.mpr hk0
      nlinarith [pi_pos]
    · subst hk0; simp at hk'; linarith
    · have : (1 : ℝ) ≤ k := by exact_mod_cast hk0
      nlinarith [pi_pos]
  have hsub : (1 - w) ∈ Complex.slitPlane := by
    left
    have : (1 - w).re = 1 - Real.cos θ := by simp [hw, Complex.exp_ofReal_mul_I_re]
    rw [this, sub_pos]
    refine lt_of_le_of_ne (cos_le_one θ) fun h => hwne ?_
    have hs : Real.sin θ = 0 := by nlinarith [sin_sq_add_cos_sq θ]
    rw [hw, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, h, hs]; simp
  -- convergence of the partial sums (Dirichlet's test)
  have hcauchy : CauchySeq fun N : ℕ => ∑ i ∈ range N, (1 / ((i : ℝ) + 1)) • w ^ (i + 1) := by
    refine Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded (b := 2 / ‖w - 1‖)
      (fun a b hab => ?_) ?_ fun N => ?_
    · have : (a : ℝ) ≤ b := by exact_mod_cast hab
      gcongr
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
    · have hne : w - 1 ≠ 0 := sub_ne_zero.mpr hwne
      have : ∑ i ∈ range N, w ^ (i + 1) = w * ((w ^ N - 1) / (w - 1)) := by
        rw [← geom_sum_eq hwne, mul_sum]; exact sum_congr rfl fun i _ => by ring
      rw [this, norm_mul, hw1, one_mul, norm_div]
      gcongr
      calc ‖w ^ N - 1‖ ≤ ‖w ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hw1]; norm_num
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hL' : Tendsto (fun N : ℕ => ∑ n ∈ range N, w ^ n / n) atTop (𝓝 L) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    refine hL.congr fun N => ?_
    rw [sum_range_succ']
    simp only [Nat.cast_zero, div_zero, add_zero, Complex.real_smul]
    exact sum_congr rfl fun i _ => by push_cast; field_simp
  -- Abel's theorem identifies the limit
  have habel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hL'
  have hlim : Tendsto (fun r : ℝ => -Complex.log (1 - (r : ℂ) * w)) (𝓝[<] 1)
      (𝓝 (-Complex.log (1 - w))) := by
    have hc : ContinuousAt (fun r : ℝ => -Complex.log (1 - (r : ℂ) * w)) 1 := by
      refine (ContinuousAt.neg ?_)
      refine ContinuousAt.comp (g := Complex.log) ?_ (by fun_prop)
      simpa using continuousAt_clog hsub
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  rw [tendsto_map'_iff] at habel
  have heq : (fun r : ℝ => ∑' n : ℕ, w ^ n / (n : ℂ) * ((r : ℂ)) ^ n) =ᶠ[𝓝[<] 1]
      fun r : ℝ => -Complex.log (1 - (r : ℂ) * w) := by
    have : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r := by
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr using hr.1
    filter_upwards [this, self_mem_nhdsWithin] with r hr hr1
    have hn : ‖(r : ℂ) * w‖ < 1 := by
      rw [norm_mul, hw1, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]; exact hr1
    rw [← (Complex.hasSum_taylorSeries_neg_log hn).tsum_eq]
    exact tsum_congr fun n => by rw [mul_pow]; ring
  have := tendsto_nhds_unique (habel.congr' heq) hlim
  rw [← this]; exact hL'


/-- `arg(1 - e^{iθ}) = (θ - π)/2` for `0 < θ < 2π`. -/
private lemma arg_one_sub_exp_mul_I {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 2 * π) :
    Complex.arg (1 - Complex.exp (θ * Complex.I)) = (θ - π) / 2 := by
  have hs : 0 < Real.sin (θ / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have he : 1 - Complex.exp (θ * Complex.I) = ((2 * Real.sin (θ / 2) : ℝ) : ℂ) *
      (((Real.cos ((θ - π) / 2) : ℝ) : ℂ) + ((Real.sin ((θ - π) / 2) : ℝ) : ℂ) * Complex.I) := by
    rw [show (θ - π) / 2 = θ / 2 - π / 2 by ring, Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have hc : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
      have := Real.cos_two_mul (θ / 2)
      rw [show 2 * (θ / 2) = θ by ring] at this
      nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]
    have hsn : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
      rw [← Real.sin_two_mul]; ring_nf
    rw [hc, hsn]
    apply Complex.ext <;>
      simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.one_re, Complex.one_im] <;> ring
  rw [he, Complex.arg_real_mul _ (by positivity), Complex.ofReal_cos, Complex.ofReal_sin,
    Complex.arg_cos_add_sin_mul_I]
  constructor <;> linarith [pi_pos]


/-- Symmetric sums over `0 < |k| ≤ N` as sums over `k = 1, …, N`. -/
private lemma sum_Icc_neg_ne_zero_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℤ → M) (N : ℕ) :
    ∑ k ∈ Icc (-(N : ℤ)) N with k ≠ 0, f k = ∑ k ∈ range N, (f (k + 1) + f (-(k + 1))) := by
  induction N with
  | zero => simp [Finset.filter_singleton]
  | succ N ih =>
    have hset : (Icc (-((N + 1 : ℕ) : ℤ)) (N + 1 : ℕ)).filter (· ≠ 0) =
        insert ((N : ℤ) + 1) (insert (-((N : ℤ) + 1)) ((Icc (-(N : ℤ)) N).filter (· ≠ 0))) := by
      ext k; simp only [mem_filter, mem_Icc, mem_insert]; push_cast; omega
    rw [hset, sum_insert (by simp only [mem_insert, mem_filter, mem_Icc]; omega),
      sum_insert (by simp only [mem_filter, mem_Icc]; omega), ih, sum_range_succ]
    abel

/-- **DLMF 24.8.2 with `n = 0`**: for `0 < x < 1`, `B₁(x) = -(2/(2π)) ∑_{k≥1} sin(2πkx)/k`, as the
limit of the partial sums (the series converges only conditionally). -/
@[dlmf 24.8.E2]
theorem tendsto_sum_sin_div_eq_bernoulliFun_one {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto (fun N : ℕ => -(2 / (2 * π)) * ∑ k ∈ range N, sin (2 * π * (k + 1) * x) / (k + 1))
      atTop (𝓝 (bernoulliFun 1 x)) := by
  have h := tendsto_sum_exp_pow_div_neg_log (θ := 2 * π * x) (by positivity) (by nlinarith [pi_pos])
  have him := (Complex.continuous_im.tendsto _).comp h
  rw [← tendsto_add_atTop_iff_nat 1] at him
  rw [Complex.neg_im, Complex.log_im, arg_one_sub_exp_mul_I (by positivity) (by nlinarith [pi_pos])]
    at him
  rw [bernoulliFun_one]
  have hval : -(2 / (2 * π)) * -((2 * π * x - π) / 2) = x - 1 / 2 := by
    field_simp
  rw [← hval]
  refine (him.const_mul _).congr fun N => ?_
  congr 1
  simp only [Function.comp, Complex.im_sum]
  rw [sum_range_succ']
  simp only [Nat.cast_zero, div_zero, Complex.zero_im, add_zero]
  refine sum_congr rfl fun k _ => ?_
  rw [← Complex.exp_nat_mul, show ((k + 1 : ℕ) : ℂ) * (↑(2 * π * x) * Complex.I) =
    ((2 * π * (k + 1) * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [show ((k + 1 : ℕ) : ℂ) = (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_im,
    Complex.exp_ofReal_mul_I_im]

/-- **DLMF 24.8.3 with `n = 1`**: for `0 < x < 1`,
`B₁(x) = -(1/(2πi)) ∑_{k ≠ 0} e^{2πikx}/k`, as the limit of the symmetric partial sums
`∑_{0 < |k| ≤ N}`. -/
@[dlmf 24.8.E3]
theorem tendsto_sum_exp_div_eq_bernoulliFun_one {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto (fun N : ℕ => -(1 / (2 * π * Complex.I)) *
        ∑ k ∈ Icc (-(N : ℤ)) N with k ≠ 0, Complex.exp (2 * π * Complex.I * k * x) / k)
      atTop (𝓝 (bernoulliFun 1 x : ℂ)) := by
  have h := (Complex.continuous_ofReal.tendsto _).comp
    (tendsto_sum_sin_div_eq_bernoulliFun_one hx0 hx1)
  refine h.congr fun N => ?_
  simp only [Function.comp]
  rw [sum_Icc_neg_ne_zero_eq_sum_range]
  push_cast
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hI : (2 * π * Complex.I) ≠ 0 := by simp [pi_ne_zero]
  set z : ℂ := 2 * π * ((k : ℂ) + 1) * x
  have e1 : Complex.exp (2 * π * Complex.I * ((k : ℂ) + 1) * x) = Complex.exp (z * Complex.I) := by
    congr 1; simp only [z]; ring
  have e2 : Complex.exp (2 * π * Complex.I * -((k : ℂ) + 1) * x) =
      Complex.exp (-z * Complex.I) := by
    congr 1; simp only [z]; ring
  have e3 : Complex.sin (2 * π * ((k : ℂ) + 1) * x) = Complex.sin z := rfl
  rw [e1, e2, e3, Complex.sin]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **DLMF 24.8.4**: for `n ≥ 1` and `0 ≤ x ≤ 1`,
`E₂ₙ(x) = (-1)ⁿ 4(2n)!/π^{2n+1} ∑_{k≥0} sin((2k+1)πx)/(2k+1)^{2n+1}`. -/
@[dlmf 24.8.E4]
theorem hasSum_sin_odd_eulerFun {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    HasSum (fun k : ℕ => (-1) ^ n * (4 * (2 * n)! / π ^ (2 * n + 1)) *
        (sin ((2 * k + 1) * π * x) / (2 * k + 1) ^ (2 * n + 1)))
      (eulerFun (2 * n) x) := by
  have hn0 : n ≠ 0 := by omega
  have hA := hasSum_one_div_nat_pow_mul_sin hn0 (x := x / 2 + 1 / 2) ⟨by linarith, by linarith⟩
  have hB := hasSum_one_div_nat_pow_mul_sin hn0 (x := x / 2) ⟨by linarith, by linarith⟩
  set c : ℝ := (-1 : ℝ) ^ (n + 1) * (2 * π) ^ (2 * n + 1) / 2 / (2 * n + 1)!
  have hc : c ≠ 0 := by
    have : (0 : ℝ) < (2 * π) ^ (2 * n + 1) / 2 / (2 * n + 1)! := by positivity
    simp only [c]
    rw [mul_div_assoc, mul_div_assoc]
    refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
    exact this.ne'
  have hD := (hA.sub hB).mul_left (2 ^ (2 * n + 1) / (2 * n + 1) / c)
  have hE : 2 ^ (2 * n + 1) / (2 * n + 1) / c * (c * Polynomial.eval (x / 2 + 1 / 2)
      (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * n + 1))) -
      c * Polynomial.eval (x / 2)
        (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * n + 1))))
      = eulerFun (2 * n) x := by
    change _ * (c * bernoulliFun _ _ - c * bernoulliFun _ _) = _
    rw [eulerFun_eq_bernoulliFun_sub]; push_cast; field_simp
  rw [hE] at hD
  refine (hasSum_odd_of_even_eq_zero hD fun j => ?_).congr_fun fun k => ?_
  · rw [show 2 * π * ((2 * j : ℕ) : ℝ) * (x / 2 + 1 / 2) = 2 * π * ((2 * j : ℕ) : ℝ) * (x / 2) +
      ((2 * j : ℕ) : ℝ) * π by ring, Real.sin_add_nat_mul_pi]
    simp [pow_mul]
  · rw [show 2 * π * ((2 * k + 1 : ℕ) : ℝ) * (x / 2 + 1 / 2) =
        2 * π * ((2 * k + 1 : ℕ) : ℝ) * (x / 2) + ((2 * k + 1 : ℕ) : ℝ) * π by ring,
      Real.sin_add_nat_mul_pi,
      show 2 * π * ((2 * k + 1 : ℕ) : ℝ) * (x / 2) = (2 * k + 1) * π * x by push_cast; ring]
    rw [(odd_two_mul_add_one k).neg_one_pow]
    simp only [c, Nat.factorial_succ (2 * n)]
    push_cast
    have : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    have h1 : ((-1 : ℝ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    rw [mul_pow]
    linear_combination (-4 * sin ((2 * k + 1) * π * x) * π ^ (2 * n + 1) * 2 ^ (2 * n + 1)) * h1

/-- **DLMF 24.8.5**: for `n ≥ 1` and `0 ≤ x ≤ 1`,
`E₂ₙ₋₁(x) = (-1)ⁿ 4(2n-1)!/π^{2n} ∑_{k≥0} cos((2k+1)πx)/(2k+1)^{2n}`. -/
@[dlmf 24.8.E5]
theorem hasSum_cos_odd_eulerFun {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    HasSum (fun k : ℕ => (-1) ^ n * (4 * (2 * n - 1)! / π ^ (2 * n)) *
        (cos ((2 * k + 1) * π * x) / (2 * k + 1) ^ (2 * n)))
      (eulerFun (2 * n - 1) x) := by
  have hn0 : n ≠ 0 := by omega
  have hA := hasSum_one_div_nat_pow_mul_cos hn0 (x := x / 2 + 1 / 2) ⟨by linarith, by linarith⟩
  have hB := hasSum_one_div_nat_pow_mul_cos hn0 (x := x / 2) ⟨by linarith, by linarith⟩
  set c : ℝ := (-1 : ℝ) ^ (n + 1) * (2 * π) ^ (2 * n) / 2 / (2 * n)!
  have hc : c ≠ 0 := by
    have : (0 : ℝ) < (2 * π) ^ (2 * n) / 2 / (2 * n)! := by positivity
    simp only [c]
    rw [mul_div_assoc, mul_div_assoc]
    refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
    exact this.ne'
  have hD := (hA.sub hB).mul_left (2 ^ (2 * n) / (2 * n) / c)
  have hE : 2 ^ (2 * n) / (2 * n) / c * (c * Polynomial.eval (x / 2 + 1 / 2)
      (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * n))) -
      c * Polynomial.eval (x / 2) (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * n))))
      = eulerFun (2 * n - 1) x := by
    change _ * (c * bernoulliFun _ _ - c * bernoulliFun _ _) = _
    rw [eulerFun_eq_bernoulliFun_sub, show 2 * n - 1 + 1 = 2 * n by omega]
    have : (2 * (n : ℝ)) ≠ 0 := by positivity
    rw [show ((2 * n - 1 : ℕ) : ℝ) + 1 = 2 * n by
      rw [Nat.cast_sub (by omega)]; push_cast; ring]
    field_simp
  rw [hE] at hD
  refine (hasSum_odd_of_even_eq_zero hD fun j => ?_).congr_fun fun k => ?_
  · rw [show 2 * π * ((2 * j : ℕ) : ℝ) * (x / 2 + 1 / 2) = 2 * π * ((2 * j : ℕ) : ℝ) * (x / 2) +
      ((2 * j : ℕ) : ℝ) * π by ring, Real.cos_add_nat_mul_pi]
    simp [pow_mul]
  · rw [show 2 * π * ((2 * k + 1 : ℕ) : ℝ) * (x / 2 + 1 / 2) =
        2 * π * ((2 * k + 1 : ℕ) : ℝ) * (x / 2) + ((2 * k + 1 : ℕ) : ℝ) * π by ring,
      Real.cos_add_nat_mul_pi,
      show 2 * π * ((2 * k + 1 : ℕ) : ℝ) * (x / 2) = (2 * k + 1) * π * x by push_cast; ring]
    rw [(odd_two_mul_add_one k).neg_one_pow]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega]
    simp only [c, show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Nat.factorial_succ (2 * m + 1)]
    push_cast
    have : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    have hm : (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    have h1 : ((-1 : ℝ) ^ (m + 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    rw [mul_pow]
    linear_combination (-4 * cos ((2 * k + 1) * π * x) * π ^ (2 * m + 1 + 1) * 2 ^ (2 * m + 1 + 1) -
      16 * m * cos ((2 * k + 1) * π * x) * π ^ (2 * m + 2) * 2 ^ (2 * m)) * h1

section Eisenstein

open Complex ModularForm EisensteinSeries ArithmeticFunction
open UpperHalfPlane hiding I
open scoped ArithmeticFunction.sigma MatrixGroups

/-- Termwise Lambert form: `k^p/(e^{2ak} - 1) = k^p r^k/(1 - r^k)` with `r = e^{-2a}`. -/
private lemma lambert_term_eq {a : ℝ} (ha : 0 < a) (p m : ℕ) :
    ((m : ℝ) + 1) ^ p / (Real.exp (2 * a * (m + 1)) - 1) =
      ((m + 1 : ℕ) : ℝ) ^ p * Real.exp (-(2 * a)) ^ (m + 1) /
        (1 - Real.exp (-(2 * a)) ^ (m + 1)) := by
  set u := Real.exp (-(2 * a)) ^ (m + 1)
  set v := Real.exp (2 * a * (m + 1))
  have he' : u * v = 1 := by
    simp only [u, v]
    rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf; simp
  have h1 : v - 1 ≠ 0 := by
    rw [sub_ne_zero]; simp only [v]; rw [Ne, Real.exp_eq_one_iff]; positivity
  have h2 : 1 - u ≠ 0 := by
    intro h; apply h1; linear_combination v * h + he'
  clear_value u v
  field_simp
  push_cast
  linear_combination (-((m:ℝ) + 1) ^ p) * he'

/-- `‖e^{-2a}‖ < 1` for `a > 0`. -/
private lemma norm_exp_neg_lt_one {a : ℝ} (ha : 0 < a) : ‖Real.exp (-(2 * a))‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_lt_one_iff.mpr (by linarith)

/-- Summability of the Lambert series `∑ k^p/(e^{2ak} - 1)`, `a > 0`. -/
private lemma summable_lambert {a : ℝ} (ha : 0 < a) (p : ℕ) :
    Summable fun m : ℕ => ((m : ℝ) + 1) ^ p / (Real.exp (2 * a * (m + 1)) - 1) := by
  have h := summable_norm_pow_mul_geometric_div_one_sub (𝕜 := ℝ) p (norm_exp_neg_lt_one ha)
  have h' : Summable fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ p * Real.exp (-(2 * a)) ^ (m + 1) /
      (1 - Real.exp (-(2 * a)) ^ (m + 1)) :=
    (summable_nat_add_iff 1).mpr h
  exact h'.congr fun m => (lambert_term_eq ha p m).symm

/-- The `q`-expansion of the level-one Eisenstein series `E_k` at `τ = ia/π` as a Lambert
series. -/
private lemma eisensteinE_I_mul {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) {a : ℝ} (ha : 0 < a) :
    ModularForm.E hk (UpperHalfPlane.mk (I * (a / π : ℝ)) (by simpa using div_pos ha Real.pi_pos)) =
      1 - (2 * k / bernoulli k) *
        ((∑' m : ℕ, ((m : ℝ) + 1) ^ (k - 1) / (Real.exp (2 * a * (m + 1)) - 1) : ℝ) : ℂ) := by
  rw [q_expansion_bernoulli hk hk2]
  congr 2
  set r : ℂ := cexp (2 * π * I * (I * ((a / π : ℝ) : ℂ)))
  have hr : r = (Real.exp (-(2 * a)) : ℂ) := by
    simp only [r, ofReal_exp]; congr 1; push_cast
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp; ring_nf; rw [I_sq]; ring
  have hr1 : ‖r‖ < 1 := by
    rw [hr, norm_real]; exact norm_exp_neg_lt_one ha
  simp only [zpow_natCast]
  rw [← tsum_pow_div_one_sub_eq_tsum_sigma hr1, tsum_pnat_eq_tsum_succ
    (f := fun n : ℕ => (n : ℂ) ^ (k - 1) * r ^ n / (1 - r ^ n)), ofReal_tsum]
  refine tsum_congr fun m => ?_
  rw [hr, lambert_term_eq ha]
  push_cast
  rfl

/-- The modular transformation `E_k(i/y) = (iy)^k E_k(iy)`. -/
private lemma eisensteinE_S_I_mul {k : ℕ} (hk : 3 ≤ k) {y : ℝ} (hy : 0 < y) :
    ModularForm.E hk (UpperHalfPlane.mk (I * (1 / y : ℝ)) (by simpa using hy)) =
      (I * y) ^ k * ModularForm.E hk (UpperHalfPlane.mk (I * y) (by simpa using hy)) := by
  have h := SlashInvariantForm.slash_action_eqn'' (ModularForm.E hk)
    (γ := Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S) (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
    (UpperHalfPlane.mk (I * y) (by simpa using hy))
  have hS : (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S) •
      (UpperHalfPlane.mk (I * y) (by simpa using hy)) =
      UpperHalfPlane.mk (I * (1 / y : ℝ)) (by simpa using hy) := by
    have := UpperHalfPlane.modular_S_smul (UpperHalfPlane.mk (I * y) (by simpa using hy))
    ext1
    rw [show (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S) • _ = ModularGroup.S • _ from rfl,
      this]
    have : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    field_simp
    push_cast
    rw [I_sq]; field_simp
  rw [hS] at h
  rw [h]
  congr 1
  rw [denom, Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe]
  simp [ModularGroup.S]

end Eisenstein

/-! ### §24.8(ii) Other series -/

/-- **DLMF 24.8.8**: for `α, β > 0` with `αβ = π²` and `n ≥ 2`,
`(B₂ₙ/(4n))(αⁿ - (-β)ⁿ) = αⁿ ∑_{k≥1} k^{2n-1}/(e^{2αk} - 1) - (-β)ⁿ ∑_{k≥1} k^{2n-1}/(e^{2βk} - 1)`.
-/
@[dlmf 24.8.E8]
theorem bernoulli_two_mul_alpha_beta {n : ℕ} (hn : 2 ≤ n) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hαβ : α * β = π ^ 2) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) ^ (2 * n - 1) / (exp (2 * α * (k + 1)) - 1)) ∧
      Summable (fun k : ℕ => ((k : ℝ) + 1) ^ (2 * n - 1) / (exp (2 * β * (k + 1)) - 1)) ∧
      (bernoulli (2 * n) : ℝ) / (4 * n) * (α ^ n - (-β) ^ n) =
        α ^ n * ∑' k : ℕ, ((k : ℝ) + 1) ^ (2 * n - 1) / (exp (2 * α * (k + 1)) - 1) -
          (-β) ^ n * ∑' k : ℕ, ((k : ℝ) + 1) ^ (2 * n - 1) / (exp (2 * β * (k + 1)) - 1) := by
  refine ⟨summable_lambert hα _, summable_lambert hβ _, ?_⟩
  have hk : 3 ≤ 2 * n := by omega
  have hk2 : Even (2 * n) := even_two_mul n
  have hy : 0 < α / π := div_pos hα Real.pi_pos
  have h1 := eisensteinE_I_mul hk hk2 hα
  have h2 := eisensteinE_I_mul hk hk2 hβ
  have h3 := eisensteinE_S_I_mul hk hy
  have hyβ : 1 / (α / π) = β / π := by
    field_simp; nlinarith [hαβ]
  simp only [hyβ] at h3
  rw [h1, h2, mul_pow, pow_mul, Complex.I_sq] at h3
  set Tα := ∑' k : ℕ, ((k : ℝ) + 1) ^ (2 * n - 1) / (Real.exp (2 * α * (k + 1)) - 1)
  set Tβ := ∑' k : ℕ, ((k : ℝ) + 1) ^ (2 * n - 1) / (Real.exp (2 * β * (k + 1)) - 1)
  clear_value Tα Tβ
  have hB : (bernoulli (2 * n) : ℝ) ≠ 0 := by
    have := (bernoulli_two_mul_add_one_eq_zero_and_sign
      (n := n) (by omega)).2
    intro h
    have h' : bernoulli (2 * n) = 0 := by exact_mod_cast h
    simp [h'] at this
  have key : (1 : ℝ) - 2 * (2 * n : ℕ) / bernoulli (2 * n) * Tβ =
      (-1) ^ n * (α / π) ^ (2 * n) * (1 - 2 * (2 * n : ℕ) / bernoulli (2 * n) * Tα) := by
    have := h3
    push_cast at this ⊢
    exact_mod_cast this
  have hyn : (α / π) ^ (2 * n) * β ^ n = α ^ n := by
    have hπ : π ^ (2 * n) = α ^ n * β ^ n := by rw [pow_mul, ← hαβ, mul_pow]
    rw [div_pow, hπ]
    have : β ^ n ≠ 0 := by positivity
    have : α ^ n ≠ 0 := by positivity
    field_simp; ring
  have key2 : (-β) ^ n * (1 - 2 * (2 * n : ℕ) / bernoulli (2 * n) * Tβ) =
      α ^ n * (1 - 2 * (2 * n : ℕ) / bernoulli (2 * n) * Tα) := by
    have h1' : ((-1 : ℝ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    rw [neg_pow, mul_assoc, key, ← hyn]
    linear_combination ((α / π) ^ (2 * n) * β ^ n *
      (1 - 2 * (2 * n : ℕ) / bernoulli (2 * n) * Tα)) * h1'
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  push_cast at key2
  field_simp at key2 ⊢
  linear_combination (-1 : ℝ) * key2

/-- **DLMF 24.8.6**: `B₄ₙ₊₂ = (8n+4) ∑_{k≥1} k^{4n+1}/(e^{2πk} - 1)`, `n ≥ 1`. -/
@[dlmf 24.8.E6]
theorem hasSum_bernoulli_four_mul_add_two {n : ℕ} (hn : 1 ≤ n) :
    HasSum (fun k : ℕ => (8 * n + 4) * (((k : ℝ) + 1) ^ (4 * n + 1) / (exp (2 * π * (k + 1)) - 1)))
      (bernoulli (4 * n + 2)) := by
  obtain ⟨hs, -, h⟩ := bernoulli_two_mul_alpha_beta (n := 2 * n + 1) (by omega) Real.pi_pos
    Real.pi_pos (by ring)
  rw [show 2 * (2 * n + 1) - 1 = 4 * n + 1 by omega, show 2 * (2 * n + 1) = 4 * n + 2 by omega,
    Odd.neg_pow (by exact odd_two_mul_add_one n)] at h
  rw [show 2 * (2 * n + 1) - 1 = 4 * n + 1 by omega] at hs
  have hp : π ^ (2 * n + 1) ≠ 0 := by positivity
  set T := ∑' k : ℕ, ((k : ℝ) + 1) ^ (4 * n + 1) / (Real.exp (2 * π * (k + 1)) - 1)
  have hT : (bernoulli (4 * n + 2) : ℝ) = (8 * n + 4) * T := by
    clear_value T
    have h4 : (4 * ((2 * n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    rw [div_mul_eq_mul_div, div_eq_iff h4] at h
    push_cast at h
    apply mul_left_cancel₀ hp
    linear_combination h / 2
  rw [hT]
  exact hs.hasSum.mul_left _

/-- **DLMF 24.8.7**: `B₂ₙ = (-1)ⁿ⁺¹ 4n/(2²ⁿ - 1) ∑_{k≥1} k^{2n-1}/(e^{πk} + (-1)^{k+n})`,
`n ≥ 2`. -/
@[dlmf 24.8.E7]
theorem hasSum_bernoulli_two_mul_alt {n : ℕ} (hn : 2 ≤ n) :
    HasSum (fun k : ℕ => (-1) ^ (n + 1) * (4 * n) / (2 ^ (2 * n) - 1) *
        (((k : ℝ) + 1) ^ (2 * n - 1) / (exp (π * (k + 1)) + (-1) ^ (k + 1 + n))))
      (bernoulli (2 * n)) := by
  set p := 2 * n - 1 with hp
  let g : ℝ → ℕ → ℝ := fun a k => ((k : ℝ) + 1) ^ p / (Real.exp (2 * a * (k + 1)) - 1)
  have hπ2 : 0 < π / 2 := by positivity
  have h2π : 0 < 2 * π := by positivity
  obtain ⟨sA, sC, hAC⟩ := bernoulli_two_mul_alpha_beta hn hπ2 h2π (by ring)
  obtain ⟨sT, -, hTT⟩ := bernoulli_two_mul_alpha_beta hn Real.pi_pos Real.pi_pos (by ring)
  rw [← hp] at sA sC sT hAC hTT
  set A := ∑' k : ℕ, ((k : ℝ) + 1) ^ p / (Real.exp (2 * (π / 2) * (k + 1)) - 1)
  set C := ∑' k : ℕ, ((k : ℝ) + 1) ^ p / (Real.exp (2 * (2 * π) * (k + 1)) - 1)
  set T := ∑' k : ℕ, ((k : ℝ) + 1) ^ p / (Real.exp (2 * π * (k + 1)) - 1)
  -- the odd-index subseries of the `T` series
  have hodd : HasSum (fun j : ℕ => g π (2 * j + 1)) (2 ^ p * C) := by
    have := sC.hasSum.mul_left (2 ^ p)
    refine this.congr_fun fun j => ?_
    simp only [g]
    push_cast
    rw [show (2 * (j : ℝ) + 1 + 1) = 2 * (j + 1) by ring, mul_pow]
    ring_nf
  have heven : HasSum (fun j : ℕ => g π (2 * j)) (T - 2 ^ p * C) := by
    have hs : Summable fun j : ℕ => g π (2 * j) :=
      sT.comp_injective (mul_right_injective₀ two_ne_zero)
    have := hs.hasSum.even_add_odd hodd
    have hT : T = ∑' j, g π (2 * j) + 2 ^ p * C := sT.hasSum.unique this
    rw [hT, add_sub_cancel_right]
    exact hs.hasSum
  let h : ℕ → ℝ := fun k => if Even (k + 1 + n) then g π k else 0
  have hh : HasSum h (if Even n then 2 ^ p * C else T - 2 ^ p * C) := by
    by_cases hn2 : Even n
    · rw [show (if Even n then 2 ^ p * C else T - 2 ^ p * C) = 2 ^ p * C by simp [hn2],
        ← zero_add (2 ^ p * C)]
      refine HasSum.even_add_odd ?_ ?_
      · convert hasSum_zero with j
        simp only [h]
        refine ite_eq_right ?_
        rw [Nat.not_even_iff_odd]
        exact (even_two_mul j).add_one.add_even hn2
      · convert hodd using 1
        funext j
        simp only [h]
        refine ite_eq_left ?_
        exact (by simpa [show 2 * j + 1 + 1 = 2 * (j + 1) by ring] using
          (even_two_mul (j + 1)).add hn2)
    · rw [show (if Even n then 2 ^ p * C else T - 2 ^ p * C) = T - 2 ^ p * C by simp [hn2],
        ← add_zero (T - 2 ^ p * C)]
      refine HasSum.even_add_odd ?_ ?_
      · convert heven using 1
        funext j
        simp only [h]
        refine ite_eq_left ?_
        exact (even_two_mul j).add_one.add_odd (Nat.not_even_iff_odd.mp hn2)
      · convert hasSum_zero with j
        simp only [h]
        refine ite_eq_right ?_
        rw [Nat.not_even_iff_odd]
        rw [show 2 * j + 1 + 1 + n = 2 * (j + 1) + n by ring]
        exact (even_two_mul (j + 1)).add_odd (Nat.not_even_iff_odd.mp hn2)
  have hterm : ∀ k : ℕ, ((k : ℝ) + 1) ^ (2 * n - 1) /
      (Real.exp (π * (k + 1)) + (-1) ^ (k + 1 + n)) = g (π / 2) k - 2 * h k := by
    intro k
    simp only [g, h]
    rw [← hp]
    set x := Real.exp (π * (k + 1)) with hx
    have hx1 : 1 < x := Real.one_lt_exp_iff.mpr (by positivity)
    have e1 : Real.exp (2 * (π / 2) * (k + 1)) = x := by rw [hx]; ring_nf
    have e2 : Real.exp (2 * π * (k + 1)) = x ^ 2 := by
      rw [hx, ← Real.exp_nat_mul]; push_cast; ring_nf
    rw [e1, e2]
    have h1 : x - 1 ≠ 0 := by linarith
    have h2 : x + 1 ≠ 0 := by linarith
    have h3 : x ^ 2 - 1 ≠ 0 := by nlinarith
    split_ifs with he
    · rw [he.neg_one_pow]
      field_simp
      ring
    · rw [(Nat.not_even_iff_odd.mp he).neg_one_pow]
      ring
  have hf : HasSum (fun k : ℕ => ((k : ℝ) + 1) ^ (2 * n - 1) /
      (Real.exp (π * (k + 1)) + (-1) ^ (k + 1 + n)))
      (A - 2 * (if Even n then 2 ^ p * C else T - 2 ^ p * C)) := by
    simp_rw [hterm]
    exact sA.hasSum.sub (hh.mul_left 2)
  have hf' := hf.mul_left ((-1 : ℝ) ^ (n + 1) * (4 * n) / (2 ^ (2 * n) - 1))
  convert hf' using 1
  clear_value A C T
  have h2p : (2 : ℝ) * 2 ^ p = 4 ^ n := by
    rw [← pow_succ', hp, show 2 * n - 1 + 1 = 2 * n by omega, pow_mul]; norm_num
  have h4 : (2 : ℝ) ^ (2 * n) = 4 ^ n := by rw [pow_mul]; norm_num
  have hw : (2 * π) ^ n = 4 ^ n * (π / 2) ^ n := by rw [← mul_pow]; ring_nf
  have hu : (π / 2) ^ n ≠ 0 := by positivity
  have hπn : π ^ n ≠ 0 := by positivity
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have h41 : (4 : ℝ) ^ n - 1 ≠ 0 := by
    have : (1 : ℝ) < 4 ^ n := one_lt_pow₀ (by norm_num) (by omega)
    linarith
  rw [h4]
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_pow, hw] at hAC
    simp only [he, ↓reduceIte]
    rw [(he.add_one).neg_one_pow, show (2 : ℝ) ^ p = 4 ^ n / 2 by linarith [h2p]]
    have : (bernoulli (2 * n) : ℝ) / (4 * n) * (1 - 4 ^ n) = A - 4 ^ n * C := by
      apply mul_left_cancel₀ hu; linear_combination hAC
    field_simp
    field_simp at this
    linear_combination (-1 : ℝ) * this
  · rw [ho.neg_pow, hw] at hAC
    rw [ho.neg_pow] at hTT
    have hne : ¬ Even n := Nat.not_even_iff_odd.mpr ho
    simp only [hne, ↓reduceIte]
    rw [(ho.add_one).neg_one_pow, show (2 : ℝ) ^ p = 4 ^ n / 2 by linarith [h2p]]
    have e1 : (bernoulli (2 * n) : ℝ) / (4 * n) * (1 + 4 ^ n) = A + 4 ^ n * C := by
      apply mul_left_cancel₀ hu; linear_combination hAC
    have e2 : (bernoulli (2 * n) : ℝ) / (4 * n) = T := by
      apply mul_left_cancel₀ hπn; linear_combination hTT / 2
    field_simp
    field_simp at e1 e2
    linear_combination e1 - 2 * e2

/-- **DLMF 24.8.9**: `E₂ₙ = (-1)ⁿ ∑_{k≥1} k^{2n}/cosh(πk/2) -
4 ∑_{k≥0} (-1)ᵏ (2k+1)^{2n}/(e^{2π(2k+1)} - 1)`, `n ≥ 1`. -/
@[dlmf 24.8.E9]
theorem eulerNumber_two_mul_eq_series {n : ℕ} (hn : 1 ≤ n) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) ^ (2 * n) / cosh (π * (k + 1) / 2)) ∧
      Summable (fun k : ℕ => (-1) ^ k * (2 * (k : ℝ) + 1) ^ (2 * n) /
        (exp (2 * π * (2 * k + 1)) - 1)) ∧
      (eulerNumber (2 * n) : ℝ) =
        (-1) ^ n * ∑' k : ℕ, ((k : ℝ) + 1) ^ (2 * n) / cosh (π * (k + 1) / 2) -
          4 * ∑' k : ℕ, (-1) ^ k * (2 * (k : ℝ) + 1) ^ (2 * n) /
            (exp (2 * π * (2 * k + 1)) - 1) := by
  sorry

end DLMF.BernoulliEuler
