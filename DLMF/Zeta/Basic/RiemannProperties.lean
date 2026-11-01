/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Basic.Riemann
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.LSeries.Deriv
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.HardyZ

/-!
# Basic properties of the Riemann zeta function (DLMF §§25.2, 25.4, 25.10)

The basic analytic properties of `ζ` and of the functions of `DLMF.Zeta.Basic.Riemann`: the
Stieltjes constants and the Laurent expansion at the pole, the Dirichlet series of the
derivatives, Riemann's `ξ`-function, and the Riemann–Siegel function `Z`. The Dirichlet series
25.2.1, the residue at `s = 1`, the Euler product 25.2.11 and the functional equation 25.4.1 are
Mathlib theorems (pointers in `DLMF.Core.UpstreamElementary`).

## Main definitions

* `riemannZetaRegular`: the regular part `ζ(s) - 1/(s-1)` of `ζ` at `s = 1`.

## Main results

* `tendsto_stieltjesSeq`, `stieltjesConstant_zero`: the limit defining `γₙ` exists, and `γ₀ = γ`
  (DLMF 25.2.5).
* `hasSum_deriv_riemannZeta`, `hasSum_iteratedDeriv_riemannZeta`: the Dirichlet series of the
  derivatives (DLMF 25.2.6–25.2.7).
* `differentiable_riemannZetaRegular`: the regular part of `ζ` at `1` is entire.
* `hasSum_riemannZeta_laurent`: the Laurent expansion at `s = 1` (DLMF 25.2.4).
* `differentiable_riemannXi`: `ξ` is entire.
* `riemannXi_eq_completed`, `riemannXi_eq`: `ξ` through Mathlib's `completedRiemannZeta`, and the
  printed product formula 25.4.4 wherever every factor is defined.
* `riemannXi_one_sub`: `ξ(s) = ξ(1-s)` (DLMF 25.4.3).
* `riemannXi_zero`, `riemannXi_one`: `ξ(0) = ξ(1) = ½`.
* `riemannSiegelZ_eq_hardyZ`, `riemannSiegelZ_im`, `norm_riemannSiegelZ`,
  `riemannSiegelZ_eq_zero_iff`: `Z` is Mathlib's `hardyZ`, real, `|Z(t)| = |ζ(½+it)|`, and it
  vanishes exactly at the zeros on the critical line (DLMF §25.10(i)).

## Implementation notes

The remaining results of §25.2 (the odd and alternating series 25.2.2–25.2.3, the
Euler–Maclaurin representations 25.2.8–25.2.10 and the Hadamard product 25.2.12) are in
`DLMF.Zeta.Riemann`; the reflection formulas of §25.4 are in `DLMF.Zeta.Reflection`, and the
zeros of §25.10 in `DLMF.Zeta.Zeros`.
-/

@[expose] public noncomputable section

open Complex Filter Topology MeasureTheory Set Finset
open scoped Real Nat

namespace DLMF.Zeta

/-! ### §25.2 The Stieltjes constants, derivatives and the Laurent expansion -/

/-- `(ln x)ⁿ/x` is antitone on `[eⁿ, ∞)`. -/
private lemma antitoneOn_log_pow_div (n : ℕ) :
    AntitoneOn (fun x : ℝ => Real.log x ^ n / x) (Ici (Real.exp n)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro x hx y hy hxy
    simp only [pow_zero, Nat.cast_zero, Real.exp_zero, Set.mem_Ici] at *
    exact one_div_le_one_div_of_le (by linarith) hxy
  · have hA := Real.log_div_self_rpow_antitoneOn (a := (n : ℝ)⁻¹) (by positivity)
    rw [inv_inv] at hA
    intro x hx y hy hxy
    have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
    have hy0 : 0 < y := (Real.exp_pos _).trans_le hy
    have hlogy : 0 ≤ Real.log y := by
      rw [Set.mem_Ici] at hy
      have := Real.add_one_le_exp (n : ℝ)
      exact Real.log_nonneg (by linarith [n.cast_nonneg (α := ℝ)])
    have e : ∀ z : ℝ, 0 < z → Real.log z ^ n / z = (Real.log z / z ^ (n : ℝ)⁻¹) ^ n := by
      intro z hz
      rw [div_pow, Real.rpow_inv_natCast_pow hz.le hn.ne']
    simp only
    rw [e x hx0, e y hy0]
    exact pow_le_pow_left₀ (div_nonneg hlogy (Real.rpow_nonneg hy0.le _)) (hA hx hy hxy) n

/-- `∫_a^b (ln x)ⁿ/x dx = ((ln b)^{n+1} - (ln a)^{n+1})/(n+1)` for `0 < a ≤ b`. -/
private lemma integral_log_pow_div (n : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun x : ℝ => Real.log x ^ n / x) volume a b ∧
    ∫ x in a..b, Real.log x ^ n / x =
      Real.log b ^ (n + 1) / (n + 1) - Real.log a ^ (n + 1) / (n + 1) := by
  have hpos : ∀ x ∈ uIcc a b, 0 < x := fun x hx => by
    rw [uIcc_of_le hab] at hx; linarith [hx.1]
  have hc : ContinuousOn (fun x : ℝ => Real.log x ^ n / x) (uIcc a b) :=
    ((Real.continuousOn_log.mono fun x hx => (hpos x hx).ne').pow n).div continuousOn_id
      fun x hx => (hpos x hx).ne'
  have hi := hc.intervalIntegrable (μ := volume)
  refine ⟨hi, ?_⟩
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => Real.log x ^ (n + 1) / (n + 1)) (fun x hx => ?_) hi
  have h := ((Real.hasDerivAt_log (hpos x hx).ne').pow (n + 1)).div_const ((n : ℝ) + 1)
  convert h using 1
  have : (n : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp

/-- One step of `stieltjesSeq`: `a_{m+1} - a_m = f(m+1) - ∫_m^{m+1} f`. -/
private lemma stieltjesSeq_succ (n : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    stieltjesSeq n (m + 1) = stieltjesSeq n m + Real.log (m + 1) ^ n / (m + 1) -
      ∫ x in (m : ℝ)..(m + 1), Real.log x ^ n / x := by
  rw [(integral_log_pow_div n (by exact_mod_cast hm) (by linarith)).2]
  simp only [stieltjesSeq]
  rw [sum_Icc_succ_top (by omega)]
  push_cast
  ring

/-- DLMF 25.2.5: the limit defining the Stieltjes constant `γₙ` exists. -/
@[dlmf 25.2.E5]
theorem tendsto_stieltjesSeq (n : ℕ) :
    Tendsto (stieltjesSeq n) atTop (𝓝 (stieltjesConstant n)) := by
  set M := ⌈Real.exp n⌉₊ + 1 with hM
  have hM1 : 1 ≤ M := by omega
  have hMe : Real.exp n ≤ M := by
    rw [hM]; push_cast; linarith [Nat.le_ceil (Real.exp n)]
  set f : ℝ → ℝ := fun x => Real.log x ^ n / x with hf
  -- for `m ≥ M`, `f(m+1) ≤ ∫_m^{m+1} f ≤ f(m)`
  have hbd : ∀ m : ℕ, M ≤ m → f (m + 1) ≤ ∫ x in (m : ℝ)..(m + 1), f x ∧
      ∫ x in (m : ℝ)..(m + 1), f x ≤ f m := by
    intro m hm
    have hm' : Real.exp n ≤ m := hMe.trans (by exact_mod_cast hm)
    have hi := (integral_log_pow_div n (a := m) (b := m + 1)
      (by exact_mod_cast (show 0 < m by omega)) (by linarith)).1
    have hA := antitoneOn_log_pow_div n
    have hle : (m : ℝ) ≤ m + 1 := by linarith
    constructor
    · have := intervalIntegral.integral_mono_on hle intervalIntegrable_const hi
        (fun x hx => hA (show Real.exp n ≤ x by linarith [hx.1])
          (show Real.exp n ≤ (m : ℝ) + 1 by linarith) hx.2)
      simpa using this
    · have := intervalIntegral.integral_mono_on hle hi intervalIntegrable_const
        (fun x hx => hA hm' (show Real.exp n ≤ x by linarith [hx.1]) hx.1)
      simpa using this
  set g : ℕ → ℝ := fun j => stieltjesSeq n (j + M) with hg
  have hstep : ∀ j, g (j + 1) = g j + f ((j + M : ℕ) + 1) -
      ∫ x in ((j + M : ℕ) : ℝ)..((j + M : ℕ) + 1), f x := by
    intro j
    simp only [hg, hf]
    rw [show j + 1 + M = (j + M) + 1 by ring, stieltjesSeq_succ n (by omega)]
  have hanti : Antitone g := antitone_nat_of_succ_le fun j => by
    rw [hstep]; linarith [(hbd (j + M) (by omega)).1]
  have hfnn : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x := fun x hx =>
    div_nonneg (pow_nonneg (Real.log_nonneg hx) _) (by linarith)
  have hlow : ∀ j, g 0 - f M ≤ g j - f ((j + M : ℕ) : ℝ) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 := (hbd (j + M) (by omega)).2
      rw [hstep]
      push_cast at ih h1 ⊢
      rw [show (j : ℝ) + 1 + M = j + M + 1 by ring]
      linarith
  have hbdd : BddBelow (range g) := ⟨g 0 - f M, by
    rintro _ ⟨j, rfl⟩
    have := hlow j
    have := hfnn ((j + M : ℕ) : ℝ) (by exact_mod_cast (show 1 ≤ j + M by omega))
    linarith⟩
  have hT := tendsto_atTop_ciInf hanti hbdd
  have hT' : Tendsto (stieltjesSeq n) atTop (𝓝 (⨅ j, g j)) :=
    (tendsto_add_atTop_iff_nat M).mp hT
  rw [stieltjesConstant, hT'.limUnder_eq]
  exact hT'

/-- The `n = 0` case of DLMF 25.2.5: the sequence `H_m - ln m` tends to Euler's constant. -/
theorem tendsto_stieltjesSeq_zero :
    Tendsto (stieltjesSeq 0) atTop (𝓝 Real.eulerMascheroniConstant) := by
  refine Real.tendsto_harmonic_sub_log.congr fun m => ?_
  simp [stieltjesSeq, harmonic_eq_sum_Icc, div_eq_mul_inv]

/-- DLMF 25.2.5 (with 25.2.4): `γ₀ = γ`, Euler's constant. -/
@[dlmf 25.2.E5]
theorem stieltjesConstant_zero : stieltjesConstant 0 = Real.eulerMascheroniConstant :=
  tendsto_stieltjesSeq_zero.limUnder_eq

/-- The `k`-fold `logMul` of the constant sequence `1` is `(ln n)^k`. -/
private lemma logMul_iterate_one (k n : ℕ) :
    (LSeries.logMul^[k] (1 : ℕ → ℂ)) n = (Real.log n : ℂ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', LSeries.logMul, ih, pow_succ, Complex.natCast_log, mul_comm]

/-- DLMF 25.2.7: `ζ^{(k)}(s) = (-1)^k ∑_{n≥2} (ln n)^k n^{-s}` for `Re s > 1`. The sum is over
all `n : ℕ`; the terms `n = 0` (`0^{-s} = 0`) and, for `k ≥ 1`, `n = 1` (`ln 1 = 0`) vanish.
Stronger than DLMF: also `k = 0`. Proved from Mathlib's `LSeries_iteratedDeriv`. -/
@[dlmf 25.2.E7]
theorem hasSum_iteratedDeriv_riemannZeta {s : ℂ} (hs : 1 < s.re) (k : ℕ) :
    HasSum (fun n : ℕ => (-1 : ℂ) ^ k * (Real.log n : ℂ) ^ k * (n : ℂ) ^ (-s))
      (iteratedDeriv k riemannZeta s) := by
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
  have heq : riemannZeta =ᶠ[𝓝 s] LSeries 1 := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact (LSeries_one_eq_riemannZeta hz).symm
  have habs : LSeries.abscissaOfAbsConv (1 : ℕ → ℂ) < s.re := by
    rw [LSeries.abscissaOfAbsConv_one]; exact_mod_cast hs
  rw [(heq.iteratedDeriv k).eq_of_nhds, LSeries_iteratedDeriv k habs]
  have hsum : LSeriesSummable (LSeries.logMul^[k] (1 : ℕ → ℂ)) s :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (by rw [LSeries.abscissaOfAbsConv_logPowMul]; exact habs)
  refine (hsum.LSeriesHasSum.mul_left ((-1 : ℂ) ^ k)).congr_fun fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · have : (-s) ≠ 0 := by
      intro h; have := congrArg re h; simp at this; linarith
    simp [LSeries.term, zero_cpow this]
  · simp only [LSeries.term, hn, ite_false, logMul_iterate_one, cpow_neg]
    ring

/-- DLMF 25.2.6: `ζ'(s) = -∑_{n≥2} (ln n) n^{-s}` for `Re s > 1` (the terms `n = 0, 1`
vanish). -/
@[dlmf 25.2.E6]
theorem hasSum_deriv_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => -(Real.log n : ℂ) * (n : ℂ) ^ (-s)) (deriv riemannZeta s) := by
  have := hasSum_iteratedDeriv_riemannZeta hs 1
  simp only [iteratedDeriv_one, pow_one] at this
  exact this.congr_fun fun n => by ring

/-- `g_σ(x) = (ln x)ⁿ x^{-σ}`. -/
noncomputable def logPowMulRpowNeg (n : ℕ) (σ x : ℝ) : ℝ := Real.log x ^ n * x ^ (-σ)

/-- `c_k(σ) = g_σ(k+1) - ∫_{k+1}^{k+2} g_σ`. -/
noncomputable def stieltjesIncrement (n : ℕ) (σ : ℝ) (k : ℕ) : ℝ :=
  logPowMulRpowNeg n σ (k + 1) - ∫ x in ((k : ℝ) + 1)..((k : ℝ) + 2), logPowMulRpowNeg n σ x

/-- `(ln x)^m ≤ 4ⁿ n! x^{1/4}` for `x ≥ 1`, `m ≤ n`. -/
private lemma log_pow_le_mul_rpow {x : ℝ} (hx : 1 ≤ x) {m n : ℕ} (hmn : m ≤ n) :
    Real.log x ^ m ≤ 4 ^ n * n ! * x ^ (1 / 4 : ℝ) := by
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have h := Real.pow_div_factorial_le_exp (Real.log x / 4) (by positivity) m
  rw [show Real.exp (Real.log x / 4) = x ^ (1 / 4 : ℝ) by
    rw [Real.rpow_def_of_pos (by linarith)]; congr 1; ring] at h
  rw [div_pow, div_div, div_le_iff₀ (by positivity)] at h
  have h4 : (4 : ℝ) ^ m * m ! ≤ 4 ^ n * n ! := by
    gcongr
    · norm_num
  calc Real.log x ^ m ≤ x ^ (1 / 4 : ℝ) * (4 ^ m * m !) := h
    _ ≤ x ^ (1 / 4 : ℝ) * (4 ^ n * n !) := by gcongr
    _ = _ := by ring

/-- The derivative of `g_σ`. -/
private lemma hasDerivAt_logPowMulRpowNeg (n : ℕ) (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (logPowMulRpowNeg n σ) (n * Real.log x ^ (n - 1) * x⁻¹ * x ^ (-σ) +
      Real.log x ^ n * (-σ * x ^ (-σ - 1))) x := by
  have h1 : HasDerivAt (fun y => Real.log y ^ n) (n * Real.log x ^ (n - 1) * x⁻¹) x := by
    exact (hasDerivAt_pow n (Real.log x)).comp x (Real.hasDerivAt_log hx.ne')
  have h2 := Real.hasDerivAt_rpow_const (x := x) (p := -σ) (Or.inl hx.ne')
  exact h1.mul h2

/-- Uniform bound on `c_k(σ)` for `1 ≤ σ ≤ 2`. -/
private lemma abs_stieltjesIncrement_le (n : ℕ) {σ : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (k : ℕ) :
    |stieltjesIncrement n σ k| ≤ (n + 2) * (4 ^ n * n !) * ((k : ℝ) + 1) ^ (-(7 / 4 : ℝ)) := by
  set a : ℝ := (k : ℝ) + 1 with ha_def
  have ha : 1 ≤ a := by simp [a]
  set C : ℝ := (n + 2) * (4 ^ n * n !) * a ^ (-(7 / 4 : ℝ)) with hC
  have hderiv : ∀ x ∈ Icc a (a + 1), ‖n * Real.log x ^ (n - 1) * x⁻¹ * x ^ (-σ) +
      Real.log x ^ n * (-σ * x ^ (-σ - 1))‖ ≤ C := by
    intro x hx
    have hx1 : 1 ≤ x := ha.trans hx.1
    have hx0 : 0 < x := by linarith
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hp : x⁻¹ * x ^ (-σ) = x ^ (-σ - 1) := by
      rw [Real.rpow_sub hx0, Real.rpow_one]; field_simp
    have hq : x ^ (1 / 4 : ℝ) * x ^ (-σ - 1) ≤ a ^ (-(7 / 4 : ℝ)) := by
      rw [← Real.rpow_add hx0]
      calc x ^ (1 / 4 + (-σ - 1)) ≤ x ^ (-(7 / 4 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
        _ ≤ a ^ (-(7 / 4 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (by linarith) hx.1 (by norm_num)
    have hpos : 0 ≤ x ^ (-σ - 1) := Real.rpow_nonneg hx0.le _
    have hb1 := log_pow_le_mul_rpow hx1 (Nat.sub_le n 1)
    have hb2 := log_pow_le_mul_rpow hx1 (le_refl n)
    have hK : 0 ≤ (4 : ℝ) ^ n * n ! := by positivity
    rw [Real.norm_eq_abs]
    calc |n * Real.log x ^ (n - 1) * x⁻¹ * x ^ (-σ) + Real.log x ^ n * (-σ * x ^ (-σ - 1))|
        ≤ n * Real.log x ^ (n - 1) * x ^ (-σ - 1) + 2 * (Real.log x ^ n * x ^ (-σ - 1)) := by
          rw [mul_assoc _ x⁻¹, hp]
          refine (abs_add_le _ _).trans ?_
          rw [abs_of_nonneg (by positivity), abs_mul, abs_of_nonneg (by positivity), abs_mul,
            abs_neg, abs_of_nonneg (by linarith), abs_of_nonneg hpos]
          nlinarith [mul_nonneg (pow_nonneg hl n) hpos]
      _ ≤ n * (4 ^ n * n ! * x ^ (1 / 4 : ℝ)) * x ^ (-σ - 1) +
            2 * ((4 ^ n * n ! * x ^ (1 / 4 : ℝ)) * x ^ (-σ - 1)) := by gcongr
      _ = (n + 2) * (4 ^ n * n !) * (x ^ (1 / 4 : ℝ) * x ^ (-σ - 1)) := by ring
      _ ≤ C := by rw [hC]; gcongr
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (f := logPowMulRpowNeg n σ) (C := C)
    (fun x hx => (hasDerivAt_logPowMulRpowNeg n σ (by linarith [hx.1])).hasDerivWithinAt)
    (fun x hx => hderiv x (Ico_subset_Icc_self hx))
  have hint : IntervalIntegrable (logPowMulRpowNeg n σ) volume a (a + 1) := by
    refine ContinuousOn.intervalIntegrable fun x hx => ?_
    rw [Set.uIcc_of_le (by linarith)] at hx
    exact (hasDerivAt_logPowMulRpowNeg n σ (by linarith [hx.1])).continuousAt.continuousWithinAt
  have he : stieltjesIncrement n σ k = ∫ x in a..(a + 1),
      (logPowMulRpowNeg n σ a - logPowMulRpowNeg n σ x) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hint,
      intervalIntegral.integral_const, stieltjesIncrement]
    simp only [a, smul_eq_mul]
    ring_nf
  rw [he, ← Real.norm_eq_abs]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := a + 1)
    (f := fun x => logPowMulRpowNeg n σ a - logPowMulRpowNeg n σ x) (C := C) (fun x hx => by
      rw [uIoc_of_le (by linarith)] at hx
      have h := hmvt x (Ioc_subset_Icc_self hx)
      rw [norm_sub_rev] at h
      calc _ ≤ C * (x - a) := h
        _ ≤ C * 1 :=
          mul_le_mul_of_nonneg_left (by linarith [hx.2]) (by rw [hC]; positivity)
        _ = C := mul_one C)
  rw [show |a + 1 - a| = 1 by norm_num, mul_one] at this
  exact this

/-- The bound of `abs_stieltjesIncrement_le` is summable. -/
private lemma summable_stieltjesIncrement_bound (n : ℕ) :
    Summable fun k : ℕ => (n + 2) * (4 ^ n * n !) * ((k : ℝ) + 1) ^ (-(7 / 4 : ℝ)) := by
  refine Summable.mul_left _ ?_
  have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (show -(7 / 4 : ℝ) < -1 by
    norm_num))
  simpa using h

/-- `σ ↦ c_k(σ)` is continuous. -/
private lemma continuous_stieltjesIncrement (n : ℕ) (k : ℕ) :
    Continuous fun σ => stieltjesIncrement n σ k := by
  have hcont : Continuous fun p : ℝ × ℝ => Real.log (max p.2 1) ^ n * (max p.2 1) ^ (-p.1) := by
    have hm : Continuous fun p : ℝ × ℝ => max p.2 1 := by fun_prop
    have hne : ∀ p : ℝ × ℝ, max p.2 1 ≠ 0 := fun p => by positivity
    exact ((hm.log hne).pow n).mul (hm.rpow (by fun_prop) fun p => Or.inl (hne p))
  have he : ∀ σ : ℝ, (∫ x in ((k : ℝ) + 1)..((k : ℝ) + 2), logPowMulRpowNeg n σ x) =
      ∫ x in ((k : ℝ) + 1)..((k : ℝ) + 2), Real.log (max x 1) ^ n * (max x 1) ^ (-σ) := by
    intro σ
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by linarith)] at hx
    have : max x 1 = x := max_eq_left (by linarith [hx.1, (k.cast_nonneg : (0 : ℝ) ≤ k)])
    simp only [logPowMulRpowNeg, this]
  simp only [stieltjesIncrement, he]
  refine Continuous.sub ?_ ?_
  · simp only [logPowMulRpowNeg]
    exact continuous_const.mul
      (continuous_const.rpow continuous_neg fun σ => Or.inl (by positivity))
  · exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun σ x => Real.log (max x 1) ^ n * (max x 1) ^ (-σ)) hcont _ _

/-- `c_k(1) = (ln(k+1))ⁿ/(k+1) - ((ln(k+2))^{n+1} - (ln(k+1))^{n+1})/(n+1)`. -/
private lemma stieltjesIncrement_one (n k : ℕ) :
    stieltjesIncrement n 1 k = Real.log ((k : ℝ) + 1) ^ n / ((k : ℝ) + 1) -
      (Real.log ((k : ℝ) + 2) ^ (n + 1) / (n + 1) -
        Real.log ((k : ℝ) + 1) ^ (n + 1) / (n + 1)) := by
  have hg : ∀ x : ℝ, logPowMulRpowNeg n 1 x = Real.log x ^ n / x := fun x => by
    simp [logPowMulRpowNeg, Real.rpow_neg_one, div_eq_mul_inv]
  simp only [stieltjesIncrement, hg]
  rw [(integral_log_pow_div n (by positivity) (by linarith)).2]

/-- DLMF 25.2.5 rearranged: `∑_k c_k(1) = γₙ`. -/
private lemma hasSum_stieltjesIncrement_one (n : ℕ) : HasSum (stieltjesIncrement n 1)
    (stieltjesConstant n) := by
  have hs : Summable (stieltjesIncrement n 1) :=
      (summable_stieltjesIncrement_bound n).of_norm_bounded
    (fun k => abs_stieltjesIncrement_le n le_rfl one_le_two k)
  rw [hs.hasSum_iff_tendsto_nat]
  have hpart : ∀ m : ℕ, ∑ k ∈ Finset.range m, stieltjesIncrement n 1 k =
      stieltjesSeq n (m + 1) - Real.log ((m : ℝ) + 1) ^ n / ((m : ℝ) + 1) := by
    intro m
    induction m with
    | zero => simp [stieltjesSeq]
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, stieltjesIncrement_one, stieltjesSeq_succ n (m := m + 1)
          (by omega),
        (integral_log_pow_div n (a := ((m + 1 : ℕ) : ℝ)) (b := ((m + 1 : ℕ) : ℝ) + 1)
          (by positivity) (by linarith)).2]
      push_cast
      ring_nf
  simp_rw [hpart]
  have h1 : Tendsto (fun m : ℕ => stieltjesSeq n (m + 1)) atTop (𝓝 (stieltjesConstant n)) :=
    (tendsto_stieltjesSeq n).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun m : ℕ => Real.log ((m : ℝ) + 1) ^ n / ((m : ℝ) + 1)) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 n one_ne_zero).comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
    simpa [Function.comp_def] using this
  simpa using h1.sub h2

/-- `∫₁^∞ (ln x)ⁿ x^{-σ} dx = n!/(σ-1)^{n+1}` for `σ > 1`. -/
private lemma integral_logPowMulRpowNeg (n : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (logPowMulRpowNeg n σ) (Ioi 1) ∧
      ∫ x in Ioi (1 : ℝ), logPowMulRpowNeg n σ x = n ! / (σ - 1) ^ (n + 1) := by
  have hr : 0 < σ - 1 := by linarith
  have he : ∀ x : ℝ, Real.exp x • logPowMulRpowNeg n σ (Real.exp x) =
      x ^ (((n : ℝ) + 1) - 1) * Real.exp (-((σ - 1) * x)) := by
    intro x
    rw [smul_eq_mul, logPowMulRpowNeg, Real.log_exp, Real.rpow_def_of_pos (Real.exp_pos x),
      Real.log_exp, add_sub_cancel_right, Real.rpow_natCast, mul_left_comm, ← Real.exp_add]
    congr 2; ring
  have hval := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ) + 1) (by positivity) hr
  rw [Real.Gamma_nat_eq_factorial] at hval
  have hne : (∫ t in Ioi (0 : ℝ), t ^ (((n : ℝ) + 1) - 1) * Real.exp (-((σ - 1) * t))) ≠ 0 := by
    rw [hval]; positivity
  have hint := Integrable.of_integral_ne_zero hne
  have h1 : IntegrableOn (fun x => Real.exp x • logPowMulRpowNeg n σ (Real.exp x)) (Ioi 0) := by
    simp_rw [he]; exact hint
  rw [integrableOn_comp_exp_Ioi, Real.exp_zero] at h1
  refine ⟨h1, ?_⟩
  have h2 := integral_comp_exp_Ioi (logPowMulRpowNeg n σ) 0
  rw [Real.exp_zero] at h2
  rw [← h2]
  simp_rw [he]
  rw [hval, Real.div_rpow zero_le_one hr.le, Real.one_rpow,
    show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  ring

/-- For `1 < σ ≤ 2`, `∑_k c_k(σ) = ∑_k (ln k)ⁿ k^{-σ} - n!/(σ-1)^{n+1}`. -/
private lemma hasSum_stieltjesIncrement (n : ℕ) {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) {S : ℝ}
    (hS : HasSum (fun k : ℕ => logPowMulRpowNeg n σ k) S) :
    HasSum (stieltjesIncrement n σ) (S - n ! / (σ - 1) ^ (n + 1)) := by
  have hs : Summable (stieltjesIncrement n σ) :=
      (summable_stieltjesIncrement_bound n).of_norm_bounded
    (fun k => abs_stieltjesIncrement_le n hσ1.le hσ2 k)
  rw [hs.hasSum_iff_tendsto_nat]
  obtain ⟨hI, hIv⟩ := integral_logPowMulRpowNeg n hσ1
  have hii : ∀ a b : ℝ, 1 ≤ a → a ≤ b → IntervalIntegrable (logPowMulRpowNeg n σ) volume a b := by
    intro a b ha hab
    refine ContinuousOn.intervalIntegrable fun x hx => ?_
    rw [Set.uIcc_of_le hab] at hx
    exact (hasDerivAt_logPowMulRpowNeg n σ (by linarith [hx.1])).continuousAt.continuousWithinAt
  have hpart : ∀ m : ℕ, ∑ k ∈ Finset.range m, stieltjesIncrement n σ k =
      ∑ k ∈ Finset.range m, logPowMulRpowNeg n σ ((k : ℝ) + 1) -
        ∫ x in (1 : ℝ)..((m : ℝ) + 1), logPowMulRpowNeg n σ x := by
    intro m
    have h := intervalIntegral.sum_integral_adjacent_intervals (f := logPowMulRpowNeg n σ)
        (μ := volume)
      (a := fun k : ℕ => (k : ℝ) + 1) (n := m)
      (fun k _ => hii _ _ (by simp) (by push_cast; linarith))
    simp only [Nat.cast_zero, zero_add, Nat.cast_add, Nat.cast_one] at h
    rw [← h, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [stieltjesIncrement]; congr 2; ring
  simp_rw [hpart]
  have hg0 : logPowMulRpowNeg n σ 0 = 0 := by
    simp [logPowMulRpowNeg, Real.zero_rpow (show -σ ≠ 0 by linarith)]
  have h1 : Tendsto (fun m : ℕ => ∑ k ∈ Finset.range m, logPowMulRpowNeg n σ ((k : ℝ) + 1)) atTop
      (𝓝 S) := by
    have := ((hasSum_nat_add_iff' 1).mpr hS).tendsto_sum_nat
    simpa [hg0] using this
  have h2 : Tendsto (fun m : ℕ => ∫ x in (1 : ℝ)..((m : ℝ) + 1), logPowMulRpowNeg n σ x) atTop
      (𝓝 (n ! / (σ - 1) ^ (n + 1))) := by
    rw [← hIv]
    exact (intervalIntegral_tendsto_integral_Ioi 1 hI tendsto_id).comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
  exact h1.sub h2

/-- The regular part `ζ(s) - 1/(s-1)` of `ζ` at `s = 1`, extended by `γ` at `s = 1`. -/
noncomputable def riemannZetaRegular : ℂ → ℂ :=
  Function.update (fun s : ℂ => riemannZeta s - 1 / (s - 1)) 1 (Real.eulerMascheroniConstant : ℂ)

/-- The regular part of `ζ` at `1` is entire. -/
lemma differentiable_riemannZetaRegular : Differentiable ℂ riemannZetaRegular := by
  rw [← differentiableOn_univ, ← differentiableOn_compl_singleton_and_continuousAt_iff
    (c := 1) Filter.univ_mem]
  refine ⟨fun s hs => ?_, ?_⟩
  · have hs1 : s ≠ 1 := hs.2
    have hd : DifferentiableAt ℂ (fun s : ℂ => riemannZeta s - 1 / (s - 1)) s :=
      (differentiableAt_riemannZeta hs1).sub
        ((differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _))
          (sub_ne_zero.mpr hs1))
    refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with z hz
    exact Function.update_of_ne hz _ _
  · rw [riemannZetaRegular, continuousAt_update_same]
    exact tendsto_riemannZeta_sub_one_div

/-- `ζ^{(n)}(σ) = (-1)ⁿ ∑_k (ln k)ⁿ k^{-σ}` as a real sum, for real `σ > 1`. -/
private lemma exists_hasSum_iteratedDeriv_riemannZeta_real (n : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    ∃ S : ℝ, HasSum (fun k : ℕ => logPowMulRpowNeg n σ k) S ∧
      iteratedDeriv n riemannZeta σ = (-1) ^ n * (S : ℂ) := by
  have h := hasSum_iteratedDeriv_riemannZeta (s := (σ : ℂ)) (by simpa using hσ) n
  have hterm : ∀ k : ℕ, (-1 : ℂ) ^ n * (Real.log k : ℂ) ^ n * (k : ℂ) ^ (-(σ : ℂ)) =
      (-1) ^ n * ((logPowMulRpowNeg n σ k : ℝ) : ℂ) := by
    intro k
    rw [logPowMulRpowNeg, ofReal_mul, ofReal_pow, ofReal_cpow (Nat.cast_nonneg k)]
    push_cast; ring
  simp_rw [hterm] at h
  have h' := h.mul_left ((-1 : ℂ) ^ n)
  have hpm : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  simp_rw [← mul_assoc, hpm, one_mul] at h'
  have hre : HasSum (fun k : ℕ => logPowMulRpowNeg n σ k)
      ((-1) ^ n * iteratedDeriv n riemannZeta σ).re := by
    simpa using Complex.hasSum_re h'
  refine ⟨_, hre, ?_⟩
  have := (Complex.ofRealCLM.hasSum hre).unique h'
  simp only [ofRealCLM_apply] at this
  rw [this, ← mul_assoc, hpm, one_mul]

/-- The `n`-th derivative of `1/(s-1)`. -/
private lemma iteratedDeriv_one_div_sub_one (n : ℕ) (s : ℂ) :
    iteratedDeriv n (fun s : ℂ => 1 / (s - 1)) s = (-1) ^ n * n ! * (s - 1) ^ (-1 - n : ℤ) := by
  have := congrFun (iteratedDeriv_comp_sub_const (n := n) (f := fun z : ℂ => z⁻¹) (s := 1)) s
  simp only [one_div]
  rw [this, iteratedDeriv_eq_iterate, iter_deriv_inv]

/-- The Taylor coefficients of the regular part at `1`: `G^{(n)}(1) = (-1)ⁿ γₙ`. -/
lemma iteratedDeriv_riemannZetaRegular_one (n : ℕ) :
    iteratedDeriv n riemannZetaRegular 1 = (-1) ^ n * (stieltjesConstant n : ℂ) := by
  have hG := differentiable_riemannZetaRegular
  have hcont : Continuous (iteratedDeriv n riemannZetaRegular) :=
    (hG.contDiff (n := (n : WithTop ℕ∞))).continuous_iteratedDeriv n le_rfl
  have hL : Tendsto (fun σ : ℝ => iteratedDeriv n riemannZetaRegular σ) (𝓝[>] 1)
      (𝓝 (iteratedDeriv n riemannZetaRegular 1)) := by
    have := (hcont.comp continuous_ofReal).tendsto 1
    rw [Function.comp_apply, ofReal_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hT : Tendsto (fun σ : ℝ => ∑' k, stieltjesIncrement n σ k) (𝓝[>] 1)
      (𝓝 (∑' k, stieltjesIncrement n 1 k)) := by
    refine tendsto_tsum_of_dominated_convergence (summable_stieltjesIncrement_bound n)
      (fun k => ((continuous_stieltjesIncrement n k).tendsto 1).mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num)] with σ hσ k
    rw [Real.norm_eq_abs]
    exact abs_stieltjesIncrement_le n hσ.1.le hσ.2.le k
  rw [(hasSum_stieltjesIncrement_one n).tsum_eq] at hT
  have hR : Tendsto (fun σ : ℝ => (-1) ^ n * ((∑' k, stieltjesIncrement n σ k : ℝ) : ℂ)) (𝓝[>] 1)
      (𝓝 ((-1) ^ n * (stieltjesConstant n : ℂ))) :=
    ((continuous_ofReal.tendsto _).comp hT).const_mul _
  refine tendsto_nhds_unique (hL.congr' ?_) hR
  filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num)] with σ hσ
  obtain ⟨S, hS, hd⟩ := exists_hasSum_iteratedDeriv_riemannZeta_real n hσ.1
  have hσ1 : (σ : ℂ) ≠ 1 := by
    intro h; have := congrArg re h; simp at this; linarith [hσ.1]
  have hev : riemannZetaRegular =ᶠ[𝓝 (σ : ℂ)] fun s => riemannZeta s - 1 / (s - 1) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hσ1] with z hz
    exact Function.update_of_ne hz _ _
  have hopen : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hζ : ContDiffAt ℂ n riemannZeta σ :=
    (DifferentiableOn.contDiffOn (f := riemannZeta) (s := {1}ᶜ)
      (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt) hopen).contDiffAt
        (hopen.mem_nhds hσ1)
  have hinv : ContDiffAt ℂ n (fun s : ℂ => 1 / (s - 1)) σ :=
    contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const) (sub_ne_zero.mpr hσ1)
  rw [hev.iteratedDeriv_eq, iteratedDeriv_fun_sub hζ hinv, hd, iteratedDeriv_one_div_sub_one,
    (hasSum_stieltjesIncrement n hσ.1 hσ.2.le hS).tsum_eq]
  have hr : (σ : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hσ1
  rw [show (-1 - n : ℤ) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  push_cast
  field_simp

/-- DLMF 25.2.4: the Laurent expansion `ζ(s) = 1/(s-1) + ∑_{n≥0} (-1)ⁿ γₙ (s-1)ⁿ/n!` at the pole
`s = 1`, valid for every `s ≠ 1` (the regular part is entire). -/
@[dlmf 25.2.E4]
theorem hasSum_riemannZeta_laurent {s : ℂ} (hs : s ≠ 1) :
    HasSum (fun n : ℕ => (-1 : ℂ) ^ n / n ! * stieltjesConstant n * (s - 1) ^ n)
      (riemannZeta s - 1 / (s - 1)) := by
  have h := Complex.hasSum_taylorSeries_of_entire differentiable_riemannZetaRegular 1 s
  rw [riemannZetaRegular, Function.update_of_ne hs] at h
  refine h.congr_fun fun n => ?_
  rw [← riemannZetaRegular, iteratedDeriv_riemannZetaRegular_one, smul_eq_mul, smul_eq_mul]
  ring

/-! ### §25.4 Riemann's ξ-function -/

/-- DLMF 25.4.4: `ξ` is entire. -/
@[dlmf 25.4.E4]
theorem differentiable_riemannXi : Differentiable ℂ riemannXi := by
  have := differentiable_completedZeta₀
  unfold riemannXi
  fun_prop

/-- `ξ(s) = ½ s(s-1) Λ(s)` with Mathlib's completed zeta function, for `s ≠ 0, 1`. -/
theorem riemannXi_eq_completed {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXi s = s * (s - 1) / 2 * completedRiemannZeta s := by
  have h1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have h2 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [riemannXi, completedRiemannZeta_eq]
  field_simp
  ring

/-- DLMF 25.4.4: `ξ(s) = ½ s(s-1) Γ(s/2) π^{-s/2} ζ(s)` for `s ≠ 1` and `s ∉ {0, -2, -4, …}`,
where every factor of the printed product is defined. -/
@[dlmf 25.4.E4]
theorem riemannXi_eq {s : ℂ} (hs1 : s ≠ 1) (hs : ∀ n : ℕ, s ≠ -(2 * n)) :
    riemannXi s = 1 / 2 * s * (s - 1) * Gamma (s / 2) * (π : ℂ) ^ (-s / 2) * riemannZeta s := by
  have hs0 : s ≠ 0 := by simpa using hs 0
  have hG : Gammaℝ s ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff, not_exists]; exact hs
  rw [riemannXi_eq_completed hs0 hs1, riemannZeta_def_of_ne_zero hs0]
  rw [Gammaℝ_def] at hG ⊢
  have hG2 : Gamma (s / 2) ≠ 0 := right_ne_zero_of_mul hG
  field_simp

/-- `ξ(0) = ½`. -/
@[simp]
theorem riemannXi_zero : riemannXi 0 = 1 / 2 := by simp [riemannXi]

/-- `ξ(1) = ½`. -/
@[simp]
theorem riemannXi_one : riemannXi 1 = 1 / 2 := by simp [riemannXi]

/-- DLMF 25.4.3: `ξ(s) = ξ(1-s)` for all `s`. -/
@[dlmf 25.4.E3]
theorem riemannXi_one_sub (s : ℂ) : riemannXi (1 - s) = riemannXi s := by
  rw [riemannXi, riemannXi, completedRiemannZeta₀_one_sub]
  ring

/-! ### §25.10 The Riemann–Siegel function Z -/

/-- `e^z = e^{Re z} e^{i Im z}`. -/
private lemma cexp_eq_exp_re_mul_cexp_im (z : ℂ) : cexp z = (Real.exp z.re : ℂ) * cexp
    (z.im * I) := by
  rw [ofReal_exp, ← Complex.exp_add]
  congr 1
  exact (re_add_im z).symm

/-- `e^{iθ(t)} = Γ_ℝ(½+it)/|Γ_ℝ(½+it)|`: the phase of the archimedean factor. -/
private lemma norm_Gammaℝ_mul_cexp_riemannSiegelTheta (t : ℝ) :
    ((‖Gammaℝ (1 / 2 + t * I)‖ : ℝ) : ℂ) * cexp (I * riemannSiegelTheta t) =
      Gammaℝ (1 / 2 + t * I) := by
  have hw : (1 / 2 + t * I) / 2 = 1 / 4 + t / 2 * I := by ring
  have hG : Gamma (1 / 4 + t / 2 * I) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by simp)
  have hπ : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  set z : ℂ := Complex.log π * (-(1 / 2 + t * I) / 2) with hz
  have hcp : (π : ℂ) ^ (-(1 / 2 + t * I) / 2) = cexp z := by
    rw [cpow_def_of_ne_zero hπ]
  have hzre : z.re = -(1 / 4) * Real.log π := by
    rw [hz, ← ofReal_log Real.pi_pos.le]
    simp; ring
  have hzim : z.im = -(t / 2) * Real.log π := by
    rw [hz, ← ofReal_log Real.pi_pos.le]
    simp; ring
  set G := Gamma (1 / 4 + t / 2 * I) with hGdef
  have hG' : G = ((‖G‖ : ℝ) : ℂ) * cexp ((arg G : ℂ) * I) :=
    (Complex.norm_mul_exp_arg_mul_I G).symm
  have he : cexp (I * ((riemannSiegelTheta t : ℝ) : ℂ)) =
      cexp ((z.im : ℂ) * I) * cexp ((arg G : ℂ) * I) := by
    rw [← Complex.exp_add, hzim, riemannSiegelTheta]
    congr 1
    push_cast
    ring
  rw [Gammaℝ_def, hw, ← hGdef, hcp, norm_mul, Complex.norm_exp, he]
  conv_rhs => rw [cexp_eq_exp_re_mul_cexp_im z, hG']
  push_cast
  ring

/-- DLMF §25.10(i): `Z(t)` is Mathlib's Hardy `Z`-function `hardyZ t`; in particular `Z` is real. -/
@[dlmf 25.10.E1]
theorem riemannSiegelZ_eq_hardyZ (t : ℝ) : riemannSiegelZ t = hardyZ t := by
  have hs0 : (1 / 2 + t * I : ℂ) ≠ 0 := by
    intro h; have := congrArg re h; simp at this
  have hg : Gammaℝ (1 / 2 + t * I) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp)
  have hn : ((‖Gammaℝ (1 / 2 + t * I)‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr hg
  rw [ofReal_hardyZ, riemannSiegelZ, riemannZeta_def_of_ne_zero hs0]
  conv_lhs => rw [← norm_Gammaℝ_mul_cexp_riemannSiegelTheta t]
  field_simp

/-- DLMF 25.10.1–25.10.2: `Z(t)` is real. -/
@[dlmf 25.10.E1]
theorem riemannSiegelZ_im (t : ℝ) : (riemannSiegelZ t).im = 0 := by
  rw [riemannSiegelZ_eq_hardyZ, ofReal_im]

/-- DLMF §25.10(i): `|Z(t)| = |ζ(½ + it)|`. -/
@[dlmf 25.10.i]
theorem norm_riemannSiegelZ (t : ℝ) : ‖riemannSiegelZ t‖ = ‖riemannZeta (1 / 2 + t * I)‖ := by
  rw [riemannSiegelZ_eq_hardyZ, norm_real, Real.norm_eq_abs, abs_hardyZ]

/-- DLMF §25.10(i): `Z(t)` vanishes exactly at the zeros of `ζ(½ + it)`. -/
@[dlmf 25.10.i]
theorem riemannSiegelZ_eq_zero_iff (t : ℝ) :
    riemannSiegelZ t = 0 ↔ riemannZeta (1 / 2 + t * I) = 0 := by
  rw [← norm_eq_zero, norm_riemannSiegelZ, norm_eq_zero]


end DLMF.Zeta
