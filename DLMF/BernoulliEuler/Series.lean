/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.Properties
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Bernoulli and Euler polynomials: series expansions (DLMF §24.8)

The Fourier series 24.8.1, 24.8.2 (`n ≥ 1`) and 24.8.3 (`n ≥ 2`) are Mathlib's
`hasSum_one_div_nat_pow_mul_cos`, `hasSum_one_div_nat_pow_mul_sin` and
`hasSum_one_div_pow_mul_fourier_mul_bernoulliFun` (pointers in `DLMF.Core.UpstreamElementary`).
This file adds the conditionally convergent boundary cases (24.8.2 with `n = 0` and 24.8.3 with
`n = 1`, for `0 < x < 1`) as limits of natural (resp. symmetric) partial sums, the Euler
Fourier series 24.8.4–24.8.5, and the series 24.8.6–24.8.9. Series over `k ≥ 1` are written
over `k + 1`, `k : ℕ`. In 24.8.8 and 24.8.9 two convergent series are combined; their
summability is part of the statement, so the `tsum`s are genuine sums.
-/

@[expose] public section

noncomputable section

open Finset Filter Real
open scoped Nat Real Topology

namespace DLMF.BernoulliEuler

/-! ### Helpers -/

/-- Real form of DLMF 24.4.23: `Eₙ(x) = 2ⁿ⁺¹/(n+1) (Bₙ₊₁(x/2 + 1/2) - Bₙ₊₁(x/2))`. -/
theorem q24a_eulerFun_eq_bernoulliFun_sub (n : ℕ) (x : ℝ) :
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
theorem q24a_hasSum_odd {f : ℕ → ℝ} {a : ℝ} (h : HasSum f a) (h0 : ∀ j, f (2 * j) = 0) :
    HasSum (fun k => f (2 * k + 1)) a := by
  have hinj : Function.Injective (fun m : ℕ => 2 * m + 1) := fun a b h => by simp at h; omega
  refine (hinj.hasSum_iff fun n hn => ?_).mpr h
  rcases Nat.even_or_odd n with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [← two_mul]; exact h0 j
  · exact absurd ⟨j, rfl⟩ hn

/-! ### §24.8(i) Fourier series -/

/-- The complex logarithmic series on the unit circle: for `w = e^{iθ}`, `0 < θ < 2π`, the partial
sums of `∑_{n≥1} wⁿ/n` converge to `-log(1 - w)` (Dirichlet's test and Abel's limit theorem). -/
theorem r24a_tendsto_log_series {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 2 * π) :
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
theorem r24a_arg_one_sub_exp {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 2 * π) :
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
theorem r24a_sum_symm_Icc {M : Type*} [AddCommMonoid M] (f : ℤ → M) (N : ℕ) :
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
  have h := r24a_tendsto_log_series (θ := 2 * π * x) (by positivity) (by nlinarith [pi_pos])
  have him := (Complex.continuous_im.tendsto _).comp h
  rw [← tendsto_add_atTop_iff_nat 1] at him
  rw [Complex.neg_im, Complex.log_im, r24a_arg_one_sub_exp (by positivity) (by nlinarith [pi_pos])]
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
  rw [r24a_sum_symm_Icc]
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
    rw [q24a_eulerFun_eq_bernoulliFun_sub]; push_cast; field_simp
  rw [hE] at hD
  refine (q24a_hasSum_odd hD fun j => ?_).congr_fun fun k => ?_
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
    rw [q24a_eulerFun_eq_bernoulliFun_sub, show 2 * n - 1 + 1 = 2 * n by omega]
    have : (2 * (n : ℝ)) ≠ 0 := by positivity
    rw [show ((2 * n - 1 : ℕ) : ℝ) + 1 = 2 * n by
      rw [Nat.cast_sub (by omega)]; push_cast; ring]
    field_simp
  rw [hE] at hD
  refine (q24a_hasSum_odd hD fun j => ?_).congr_fun fun k => ?_
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

/-! ### §24.8(ii) Other series -/

/-- **DLMF 24.8.6**: `B₄ₙ₊₂ = (8n+4) ∑_{k≥1} k^{4n+1}/(e^{2πk} - 1)`, `n ≥ 1`. -/
@[dlmf 24.8.E6]
theorem hasSum_bernoulli_four_mul_add_two {n : ℕ} (hn : 1 ≤ n) :
    HasSum (fun k : ℕ => (8 * n + 4) * (((k : ℝ) + 1) ^ (4 * n + 1) / (exp (2 * π * (k + 1)) - 1)))
      (bernoulli (4 * n + 2)) := by
  sorry

/-- **DLMF 24.8.7**: `B₂ₙ = (-1)ⁿ⁺¹ 4n/(2²ⁿ - 1) ∑_{k≥1} k^{2n-1}/(e^{πk} + (-1)^{k+n})`,
`n ≥ 2`. -/
@[dlmf 24.8.E7]
theorem hasSum_bernoulli_two_mul_alt {n : ℕ} (hn : 2 ≤ n) :
    HasSum (fun k : ℕ => (-1) ^ (n + 1) * (4 * n) / (2 ^ (2 * n) - 1) *
        (((k : ℝ) + 1) ^ (2 * n - 1) / (exp (π * (k + 1)) + (-1) ^ (k + 1 + n))))
      (bernoulli (2 * n)) := by
  sorry

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
  sorry

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
