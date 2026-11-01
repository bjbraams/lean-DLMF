/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.SeriesExpansions
public import DLMFMathlib.NumberTheory.BernoulliTaylor
public import Mathlib.Analysis.SpecialFunctions.Integrals.Log
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
public import DLMF.Zeta.CotangentMoments
public import DLMF.Zeta.Riemann

/-!
# Power series with zeta-value coefficients (DLMF 25.8.4–25.8.8)

The power series 25.8.5–25.8.8 are derived from the Taylor series of `ψ(1+z)` and
`ln Γ(1+z)` (DLMF 5.7.3, 5.7.4) and the cotangent series `Complex.hasSum_pi_mul_cot_zeta`
(DLMF 4.19.6). Logarithms are principal: for `|z| < 1` the values `Γ(1-z)` and `πz/sin(πz)`
stay off the negative real axis, so DLMF's branches agree with `Complex.log` there.

## Main results

* `hasSum_neg_one_pow_riemannZeta_mul_sub_one`: 25.8.4.
* `hasSum_riemannZeta_mul_pow`, `hasSum_riemannZeta_two_mul_mul_pow`: 25.8.5 and 25.8.6;
  the latter excludes `z = 0`, where `πz cot(πz)` is a removable `0 · ∞` form.
* `hasSum_riemannZeta_div_mul_pow`, `hasSum_riemannZeta_two_mul_div_mul_pow`: 25.8.7 and 25.8.8.
-/

@[expose] public noncomputable section

open Complex Filter Topology Finset
open scoped Real Nat

namespace DLMF.Zeta

/-- `∑_{n≥0} 1/(n+1)^N = ζ(N)` for `N ≥ 2`. -/
private lemma hasSum_one_div_pow_riemannZeta_natCast {N : ℕ} (hN : 2 ≤ N) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ N) (riemannZeta N) := by
  have hs : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ N) := by
    refine Summable.of_norm_bounded (g := fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) ?_ fun n => ?_
    · have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
      simpa using this
    · rw [norm_div, norm_one, norm_pow, show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring,
        Complex.norm_natCast]
      push_cast
      gcongr
      · linarith
  convert hs.hasSum using 1
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simp; exact_mod_cast (by omega : 1 < N))]
  congr 1; funext n; rw [cpow_natCast]

open Polynomial in
/-- `∏_{j<n} (x - e^{(2j+1)πi/n}) = xⁿ + 1`. -/
private lemma prod_sub_exp_odd_roots {n : ℕ} (hn : 0 < n) (x : ℂ) :
    ∏ j ∈ range n, (x - cexp ((2 * j + 1) * π * I / n)) = x ^ n + 1 := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hζ := Complex.isPrimitiveRoot_exp n hn.ne'
  have hα : cexp (π * I / n) ^ n = -1 := by
    rw [← Complex.exp_nat_mul, show (n : ℂ) * (π * I / n) = π * I by field_simp,
      Complex.exp_pi_mul_I]
  have h := congrArg (Polynomial.eval x) (X_pow_sub_C_eq_prod hζ hn hα)
  simp only [eval_sub, eval_pow, eval_X, eval_C, eval_prod] at h
  rw [sub_neg_eq_add] at h
  rw [h]
  refine prod_congr rfl fun j _ => ?_
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 2
  field_simp

/-- `∑_{j<n} e^{(2j+1)πi/n} = 0` for `n ≥ 2`. -/
private lemma sum_exp_odd_roots {n : ℕ} (hn : 2 ≤ n) :
    ∑ j ∈ range n, cexp ((2 * j + 1) * π * I / n) = 0 := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hζ := Complex.isPrimitiveRoot_exp n (by omega)
  have h := hζ.geom_sum_eq_zero (by omega)
  have : ∀ j ∈ range n, cexp ((2 * j + 1) * π * I / n) =
      cexp (2 * π * I / n) ^ j * cexp (π * I / n) := by
    intro j _
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    field_simp
  rw [sum_congr rfl this, ← sum_mul, h, zero_mul]

/-- `∏_{j<n} x^{a_j} = x^{∑ a_j}` for `x ≠ 0`. -/
private lemma prod_cpow_eq_cpow_sum {x : ℂ} (hx : x ≠ 0) (a : ℕ → ℂ) (n : ℕ) :
    ∏ j ∈ range n, x ^ a j = x ^ (∑ j ∈ range n, a j) := by
  induction n with
  | zero => simp
  | succ n ih => rw [prod_range_succ, sum_range_succ, ih, cpow_add _ _ hx]

/-- The product of the Gamma sequences at `2 - e^{(2j+1)πi/n}`. -/
private lemma prod_GammaSeq_two_sub_exp_odd_roots {n : ℕ} (hn : 2 ≤ n) {N : ℕ} (hN : 1 ≤ N) :
    ∏ j ∈ range n, GammaSeq (2 - cexp ((2 * j + 1) * π * I / n)) N =
      (N : ℂ) ^ (2 * n) * (N ! : ℂ) ^ n / ∏ k ∈ range (N + 1), (((k : ℂ) + 2) ^ n + 1) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  simp only [GammaSeq]
  rw [prod_div_distrib, prod_mul_distrib, prod_cpow_eq_cpow_sum hN0, sum_sub_distrib, sum_exp_odd_roots hn,
    prod_const, card_range, Finset.prod_comm]
  congr 1
  · congr 1
    rw [sub_zero, sum_const, card_range, nsmul_eq_mul, show (n : ℂ) * 2 = ((2 * n : ℕ) : ℂ) by
      push_cast; ring, cpow_natCast]
  · refine prod_congr rfl fun k _ => ?_
    rw [← prod_sub_exp_odd_roots (by omega)]
    refine prod_congr rfl fun j _ => ?_
    ring

/-- The double series behind DLMF 25.8.4. -/
private lemma exists_hasSum_riemannZeta_mul_sub_one_and_neg_log {n : ℕ} (hn : 2 ≤ n) :
    ∃ T : ℂ, HasSum (fun k : ℕ => (-1) ^ (k + 1) / (k + 1) * (riemannZeta (n * (k + 1)) - 1)) T ∧
      HasSum (fun m : ℕ => -log (1 + 1 / ((m : ℂ) + 2) ^ n)) T := by
  set f : ℕ × ℕ → ℂ := fun p => (-1) ^ (p.1 + 1) / (p.1 + 1) * (1 / ((p.2 : ℂ) + 2) ^ n) ^ (p.1 + 1)
    with hf
  have hu : ∀ m : ℕ, ‖1 / ((m : ℂ) + 2) ^ n‖ = 1 / ((m : ℝ) + 2) ^ n := by
    intro m
    rw [norm_div, norm_one, norm_pow, show ((m : ℂ) + 2) = ((m + 2 : ℕ) : ℂ) by push_cast; ring,
      Complex.norm_natCast]
    push_cast; ring
  have hu2 : ∀ m : ℕ, 1 / ((m : ℝ) + 2) ^ n ≤ 1 / ((m : ℝ) + 2) ^ 2 := by
    intro m
    gcongr
    · linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hq : ∀ m : ℕ, 1 / ((m : ℝ) + 2) ^ 2 ≤ 1 / 4 := by
    intro m
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hsum : Summable f := by
    have hg : Summable fun k : ℕ => (1 / 4 : ℝ) ^ k :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have hh : Summable fun m : ℕ => 1 / ((m : ℝ) + 2) ^ 2 := by
      have := (summable_nat_add_iff 2).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
      simpa using this
    refine Summable.of_norm_bounded (hg.mul_of_nonneg hh (fun k => by positivity)
      (fun m => by positivity)) fun p => ?_
    have hk : (1 : ℝ) ≤ ‖((p.1 : ℂ) + 1)‖ := by
      rw [show ((p.1 : ℂ) + 1) = ((p.1 + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      exact_mod_cast (by omega : 1 ≤ p.1 + 1)
    simp only [hf, norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, hu]
    set u : ℝ := 1 / ((p.2 : ℝ) + 2) ^ n
    set v : ℝ := 1 / ((p.2 : ℝ) + 2) ^ 2
    have hu0 : 0 ≤ u := by positivity
    have huv : u ≤ v := hu2 p.2
    have hv : v ≤ 1 / 4 := hq p.2
    calc 1 / ‖(p.1 : ℂ) + 1‖ * u ^ (p.1 + 1) ≤ 1 * u ^ (p.1 + 1) := by
          gcongr; exact div_le_one_of_le₀ hk (norm_nonneg _)
      _ = u * u ^ p.1 := by ring
      _ ≤ v * (1 / 4) ^ p.1 := by gcongr; linarith
      _ = (1 / 4) ^ p.1 * v := by ring
  have hk : ∀ k : ℕ, HasSum (fun m : ℕ => f (k, m))
      ((-1) ^ (k + 1) / (k + 1) * (riemannZeta (n * (k + 1)) - 1)) := by
    intro k
    have h0 := hasSum_one_div_pow_riemannZeta_natCast (N := n * (k + 1)) (by nlinarith)
    have h1 := ((hasSum_nat_add_iff' 1).mpr h0).mul_left ((-1 : ℂ) ^ (k + 1) / ((k : ℂ) + 1))
    simp only [range_one, sum_singleton, Nat.cast_zero, zero_add, one_pow, div_one] at h1
    push_cast at h1
    convert h1 using 1
    funext m
    simp only [hf]
    rw [div_pow, one_pow, ← pow_mul, show (m : ℂ) + 1 + 1 = m + 2 by ring]
  have hm : ∀ m : ℕ, HasSum (fun k : ℕ => f (k, m)) (-log (1 + 1 / ((m : ℂ) + 2) ^ n)) := by
    intro m
    have hn1 : ‖-(1 / ((m : ℂ) + 2) ^ n)‖ < 1 := by
      rw [norm_neg, hu]
      exact (hu2 m).trans_lt ((hq m).trans_lt (by norm_num))
    have h := Complex.hasSum_taylorSeries_neg_log' hn1
    rw [sub_neg_eq_add] at h
    convert h using 1
    funext k
    simp only [hf]
    rw [neg_pow, mul_comm ((-1 : ℂ) ^ (k + 1)), div_eq_mul_inv, div_eq_mul_inv]
    ring
  refine ⟨_, hsum.hasSum.prod_fiberwise hk, ?_⟩
  have hswap : HasSum (f ∘ Prod.swap) (∑' p, f p) :=
    (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hsum.hasSum
  exact hswap.prod_fiberwise fun m => hm m

/-- `∏_{k≤N} (k+2) = (N+2)!`. -/
private lemma prod_range_add_two_eq_factorial (N : ℕ) : ∏ k ∈ range (N + 1), ((k : ℝ) + 2) = ((N + 2) ! : ℝ) := by
  induction N with
  | zero => simp [Nat.factorial]
  | succ N ih =>
    rw [prod_range_succ, ih]
    show _ = (((N + 2) + 1) ! : ℝ)
    rw [Nat.factorial_succ (N + 2)]
    push_cast; ring

/-- The Gamma-sequence product in terms of the partial products of `1 + (m+2)^{-n}`. -/
private lemma pow_mul_factorial_pow_div_prod_eq (n : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ^ (2 * n) * (N ! : ℝ) ^ n / ∏ k ∈ range (N + 1), (((k : ℝ) + 2) ^ n + 1) =
      ((N : ℝ) / (N + 1) * (N / (N + 2))) ^ n /
        ∏ k ∈ range (N + 1), (1 + 1 / ((k : ℝ) + 2) ^ n) := by
  have hprod : ∏ k ∈ range (N + 1), (((k : ℝ) + 2) ^ n + 1) =
      (∏ k ∈ range (N + 1), (1 + 1 / ((k : ℝ) + 2) ^ n)) * ((N + 2) ! : ℝ) ^ n := by
    rw [← prod_range_add_two_eq_factorial, ← prod_pow, ← prod_mul_distrib]
    refine prod_congr rfl fun k _ => ?_
    have : ((k : ℝ) + 2) ^ n ≠ 0 := by positivity
    field_simp
  have hQ : 0 < ∏ k ∈ range (N + 1), (1 + 1 / ((k : ℝ) + 2) ^ n) :=
    prod_pos fun k _ => by positivity
  have hfac : ((N + 2) ! : ℝ) = ((N : ℝ) + 2) * ((N : ℝ) + 1) * (N ! : ℝ) := by
    show (((N + 1) + 1) ! : ℝ) = _
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  rw [hprod, hfac]
  have h1 : (N : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (N : ℝ) + 2 ≠ 0 := by positivity
  have h3 : ((N ! : ℕ) : ℝ) ≠ 0 := by positivity
  calc (N : ℝ) ^ (2 * n) * (N ! : ℝ) ^ n /
        ((∏ k ∈ range (N + 1), (1 + 1 / ((k : ℝ) + 2) ^ n)) *
          (((N : ℝ) + 2) * ((N : ℝ) + 1) * (N ! : ℝ)) ^ n)
      = ((N : ℝ) ^ 2 * (N ! : ℝ) / (((N : ℝ) + 2) * ((N : ℝ) + 1) * (N ! : ℝ))) ^ n /
          ∏ k ∈ range (N + 1), (1 + 1 / ((k : ℝ) + 2) ^ n) := by
        rw [div_pow, mul_pow, pow_mul]; ring
    _ = _ := by
        congr 2
        field_simp

/-- DLMF 25.8.4: for `n ≥ 2`,
`∑_{k≥1} ((-1)^k/k) (ζ(nk) - 1) = ln ∏_{j=0}^{n-1} Γ(2 - e^{(2j+1)πi/n})` (the product is a
positive real number). -/
@[dlmf 25.8.E4]
theorem hasSum_neg_one_pow_riemannZeta_mul_sub_one {n : ℕ} (hn : 2 ≤ n) :
    HasSum (fun k : ℕ => (-1) ^ (k + 1) / (k + 1) * (riemannZeta (n * (k + 1)) - 1))
      (log (∏ j ∈ range n, Gamma (2 - cexp ((2 * j + 1) * π * I / n)))) := by
  obtain ⟨T, h1, h2⟩ := exists_hasSum_riemannZeta_mul_sub_one_and_neg_log hn
  set a : ℕ → ℝ := fun m => 1 + 1 / ((m : ℝ) + 2) ^ n with ha_def
  have ha : ∀ m, 0 < a m := fun m => by positivity
  have hterm : ∀ m : ℕ, -log (1 + 1 / ((m : ℂ) + 2) ^ n) = ((-Real.log (a m) : ℝ) : ℂ) := by
    intro m
    rw [ofReal_neg, ofReal_log (ha m).le, ha_def]
    push_cast; rfl
  simp_rw [hterm] at h2
  have hre : HasSum (fun m => -Real.log (a m)) T.re := by
    simpa using Complex.hasSum_re h2
  have hT : T = (T.re : ℂ) := ((Complex.ofRealCLM.hasSum hre).unique h2).symm
  have hlog : HasSum (fun m => Real.log (a m)) (-T.re) := by simpa using hre.neg
  have hQ : Tendsto (fun N : ℕ => ∏ k ∈ range (N + 1), a k) atTop (𝓝 (Real.exp (-T.re))) := by
    have := (Real.continuous_exp.tendsto _).comp
      (hlog.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1))
    refine this.congr fun N => ?_
    simp only [Function.comp_apply]
    rw [Real.exp_sum]
    exact prod_congr rfl fun k _ => Real.exp_log (ha k)
  have hr : Tendsto (fun N : ℕ => ((N : ℝ) / (N + 1) * (N / (N + 2))) ^ n) atTop (𝓝 1) := by
    have h1' := tendsto_natCast_div_add_atTop (𝕜 := ℝ) 1
    have h2' := tendsto_natCast_div_add_atTop (𝕜 := ℝ) 2
    simpa using (h1'.mul h2').pow n
  have hlim : Tendsto (fun N : ℕ => ∏ j ∈ range n, GammaSeq (2 - cexp ((2 * j + 1) * π * I / n)) N)
      atTop (𝓝 (((Real.exp (-T.re))⁻¹ : ℝ) : ℂ)) := by
    have := (continuous_ofReal.tendsto _).comp (hr.div hQ (Real.exp_pos _).ne')
    rw [one_div] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    simp only [Function.comp_apply, Pi.div_apply, ha_def]
    rw [prod_GammaSeq_two_sub_exp_odd_roots hn hN, ← pow_mul_factorial_pow_div_prod_eq n hN]
    push_cast; rfl
  have hG := tendsto_finsetProd (range n)
    (fun j _ => GammaSeq_tendsto_Gamma (2 - cexp ((2 * j + 1) * π * I / n)))
  rw [tendsto_nhds_unique hG hlim, ← Real.exp_neg, neg_neg, ← ofReal_log (Real.exp_pos _).le,
    Real.log_exp, ← hT]
  exact h1

/-- DLMF 25.8.5: `∑_{k≥2} ζ(k) z^k = -γz - zψ(1-z)` for `|z| < 1`. Proved from the Taylor
series of `ψ(1+z)` (DLMF 5.7.4). -/
@[dlmf 25.8.E5]
theorem hasSum_riemannZeta_mul_pow {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => riemannZeta (k + 2) * z ^ (k + 2))
      (-Real.eulerMascheroniConstant * z - z * digamma (1 - z)) := by
  have hz' : ‖-z‖ < 1 := by rwa [norm_neg]
  have h := (DLMF.Gamma.hasSum_digamma_one_add_zeta hz').mul_left (-z)
  rw [show (1 : ℂ) + -z = 1 - z by ring] at h
  convert h using 1
  · funext k
    have h1 : ((-1 : ℂ)) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
    rw [neg_pow]
    simp only [pow_succ]
    linear_combination (riemannZeta (k + 2) * z ^ k * z * z) * (-h1)
  · ring

/-- DLMF 25.8.6: `∑_{k≥0} ζ(2k) z^{2k} = -½ πz cot(πz)` for `0 < |z| < 1` (at `z = 0` the right
side is a removable singularity with value `ζ(0) = -½`). Proved from the cotangent series. -/
@[dlmf 25.8.E6]
theorem hasSum_riemannZeta_two_mul_mul_pow {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    HasSum (fun k : ℕ => riemannZeta (2 * k) * z ^ (2 * k)) (-(1 / 2) * π * z * cot (π * z)) := by
  have h := (_root_.Complex.hasSum_pi_mul_cot_zeta hz hz0).mul_left (-(1 / 2) : ℂ)
  refine (hasSum_nat_add_iff' 1).mp ?_
  simp only [range_one, sum_singleton, Nat.cast_zero, mul_zero, pow_zero, mul_one,
    riemannZeta_zero]
  convert h using 1
  · funext k
    push_cast
    ring
  · ring

/-- DLMF 25.8.7: `∑_{k≥2} (ζ(k)/k) z^k = -γz + ln Γ(1-z)` for `|z| < 1`, with the principal
logarithm. -/
@[dlmf 25.8.E7]
theorem hasSum_riemannZeta_div_mul_pow {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => riemannZeta (k + 2) / (k + 2) * z ^ (k + 2))
      (-Real.eulerMascheroniConstant * z + log (Gamma (1 - z))) := by
  have hz' : ‖-z‖ < 1 := by rwa [norm_neg]
  set A : ℕ → ℂ := fun k => (riemannZeta (k + 2) - 1) * z ^ (k + 2) / (k + 2) with hA
  have hAs : Summable A := by
    refine Summable.of_norm_bounded (g := fun k : ℕ => (1 / 2 : ℝ) ^ k)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)) fun k => ?_
    have hk : (1 : ℝ) ≤ ‖((k : ℂ) + 2)‖ := by
      rw [show ((k : ℂ) + 2) = ((k + 2 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      exact_mod_cast (by omega : 1 ≤ k + 2)
    have hzk : ‖z ^ (k + 2)‖ ≤ 1 := by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hz.le
    simp only [hA, norm_div, norm_mul]
    calc ‖riemannZeta (k + 2) - 1‖ * ‖z ^ (k + 2)‖ / ‖(k : ℂ) + 2‖
        ≤ ‖riemannZeta (k + 2) - 1‖ * ‖z ^ (k + 2)‖ := div_le_self (by positivity) hk
      _ ≤ (1 / 2 : ℝ) ^ k * 1 := by
          gcongr
          · exact DLMF.Gamma.norm_riemannZeta_add_two_sub_one_le k
      _ = _ := mul_one _
  have hlog := DLMF.Gamma.log_Gamma_one_add hz'
  have hterm : ∀ k : ℕ, (-1 : ℂ) ^ (k + 2) * (riemannZeta (k + 2) - 1) * (-z) ^ (k + 2) / (k + 2) =
      A k := by
    intro k
    simp only [hA]
    have h1 : ((-1 : ℂ)) ^ (k + 2) * (-1) ^ (k + 2) = 1 := by rw [← mul_pow]; norm_num
    rw [neg_pow z]
    linear_combination ((riemannZeta (k + 2) - 1) * z ^ (k + 2) / (k + 2)) * h1
  simp_rw [hterm, show (1 : ℂ) + -z = 1 - z by ring] at hlog
  have hB : HasSum (fun k : ℕ => z ^ (k + 2) / (k + 2)) (-log (1 - z) - z) := by
    have h := (hasSum_nat_add_iff' 2).mpr (Complex.hasSum_taylorSeries_neg_log hz)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, Nat.cast_zero, div_zero,
      zero_add, pow_one, Nat.cast_one, div_one] at h
    convert h using 2 with k
    push_cast; ring
  convert hAs.hasSum.add hB using 1
  · funext k
    simp only [hA]
    have hk : ((k : ℂ) + 2) ≠ 0 := by
      rw [show ((k : ℂ) + 2) = ((k + 2 : ℕ) : ℂ) by push_cast; ring]
      exact_mod_cast (by omega : k + 2 ≠ 0)
    field_simp
    ring
  · have : ∑' k, A k =
        log (Gamma (1 - z)) + log (1 - z) - -z * (1 - Real.eulerMascheroniConstant) := by
      rw [hlog]; ring
    rw [this]; ring

/-- The double series behind DLMF 25.8.8. -/
private lemma exists_hasSum_riemannZeta_two_mul_and_neg_log {z : ℂ} (hz : ‖z‖ < 1) :
    ∃ F : ℂ, HasSum (fun k : ℕ => riemannZeta (2 * (k + 1)) / (k + 1) * z ^ (2 * (k + 1))) F ∧
      HasSum (fun m : ℕ => -log (1 - z ^ 2 / ((m : ℂ) + 1) ^ 2)) F := by
  set f : ℕ × ℕ → ℂ := fun p => (z ^ 2 / ((p.2 : ℂ) + 1) ^ 2) ^ (p.1 + 1) / (p.1 + 1) with hf
  have hw : ∀ m : ℕ, ‖z ^ 2 / ((m : ℂ) + 1) ^ 2‖ = ‖z‖ ^ 2 / ((m : ℝ) + 1) ^ 2 := by
    intro m
    rw [norm_div, norm_pow, norm_pow, show ((m : ℂ) + 1) = ((m + 1 : ℕ) : ℂ) by push_cast; ring,
      Complex.norm_natCast]
    push_cast; ring
  have hw1 : ∀ m : ℕ, ‖z ^ 2 / ((m : ℂ) + 1) ^ 2‖ < 1 := by
    intro m
    rw [hw, div_lt_one (by positivity)]
    have : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
    nlinarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hsum : Summable f := by
    have hz2 : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
    have hg : Summable fun k : ℕ => (‖z‖ ^ 2) ^ (k + 1) :=
      ((summable_geometric_of_lt_one (by positivity) hz2).mul_left (‖z‖ ^ 2)).congr
        fun k => by ring
    have hh : Summable fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2 := by
      have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
      simpa using this
    refine Summable.of_norm_bounded (hg.mul_of_nonneg hh (fun k => by positivity)
      (fun m => by positivity)) fun p => ?_
    have hk : (1 : ℝ) ≤ ‖((p.1 : ℂ) + 1)‖ := by
      rw [show ((p.1 : ℂ) + 1) = ((p.1 + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      exact_mod_cast (by omega : 1 ≤ p.1 + 1)
    have hm : (1 : ℝ) ≤ ((p.2 : ℝ) + 1) ^ 2 := by
      have : (1 : ℝ) ≤ (p.2 : ℝ) + 1 := by linarith [(p.2.cast_nonneg : (0 : ℝ) ≤ p.2)]
      nlinarith
    simp only [hf, norm_div, norm_pow, hw]
    calc (‖z‖ ^ 2 / ((p.2 : ℝ) + 1) ^ 2) ^ (p.1 + 1) / ‖(p.1 : ℂ) + 1‖
        ≤ (‖z‖ ^ 2 / ((p.2 : ℝ) + 1) ^ 2) ^ (p.1 + 1) := div_le_self (by positivity) hk
      _ = (‖z‖ ^ 2) ^ (p.1 + 1) / (((p.2 : ℝ) + 1) ^ 2) ^ (p.1 + 1) := by rw [div_pow]
      _ ≤ (‖z‖ ^ 2) ^ (p.1 + 1) / ((p.2 : ℝ) + 1) ^ 2 := by
          gcongr
          exact le_self_pow₀ hm (by omega)
      _ = _ := by ring
  have hk : ∀ k : ℕ, HasSum (fun m : ℕ => f (k, m))
      (riemannZeta (2 * (k + 1)) / (k + 1) * z ^ (2 * (k + 1))) := by
    intro k
    have h := (hasSum_one_div_pow_riemannZeta_natCast (N := 2 * (k + 1)) (by omega)).mul_left
      (z ^ (2 * (k + 1)) / (k + 1))
    push_cast at h
    convert h using 1
    · funext m
      simp only [hf]
      rw [div_pow, ← pow_mul, ← pow_mul]
      ring
    · ring
  have hm : ∀ m : ℕ, HasSum (fun k : ℕ => f (k, m)) (-log (1 - z ^ 2 / ((m : ℂ) + 1) ^ 2)) := by
    intro m
    have h := Complex.hasSum_taylorSeries_neg_log' (hw1 m)
    simpa [hf] using h
  refine ⟨_, hsum.hasSum.prod_fiberwise hk, ?_⟩
  have hswap : HasSum (f ∘ Prod.swap) (∑' p, f p) :=
    (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hsum.hasSum
  exact hswap.prod_fiberwise fun m => hm m

/-- `‖z²/(m+1)²‖ < 1/(m+1)²` for `‖z‖ < 1`. -/
private lemma norm_sq_div_succ_sq_le {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    ‖z ^ 2 / ((m : ℂ) + 1) ^ 2‖ ≤ 1 / ((m : ℝ) + 1) ^ 2 := by
  rw [norm_div, norm_pow, norm_pow, show ((m : ℂ) + 1) = ((m + 1 : ℕ) : ℂ) by push_cast; ring,
    Complex.norm_natCast]
  push_cast
  gcongr
  nlinarith [norm_nonneg z]

/-- `‖z²/(m+1)²‖ < 1` for `‖z‖ < 1`. -/
private lemma norm_sq_div_succ_sq_lt_one {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) : ‖z ^ 2 / ((m : ℂ) + 1) ^ 2‖ < 1 := by
  rw [norm_div, norm_pow, norm_pow, show ((m : ℂ) + 1) = ((m + 1 : ℕ) : ℂ) by push_cast; ring,
    Complex.norm_natCast, div_lt_one (by positivity)]
  have : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
  push_cast
  nlinarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]

/-- The exponential of the double series is `πz/sin(πz)`. -/
private lemma exp_eq_pi_mul_div_sin_of_hasSum_neg_log {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) {F : ℂ}
    (hF : HasSum (fun m : ℕ => -log (1 - z ^ 2 / ((m : ℂ) + 1) ^ 2)) F) :
    cexp F = π * z / sin (π * z) := by
  have hsin : sin (π * z) ≠ 0 := by
    rw [Ne, Complex.sin_eq_zero_iff]
    rintro ⟨k, hk⟩
    have hz' : z = k := by
      have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
      field_simp at hk; linear_combination hk
    rw [hz', Complex.norm_intCast] at hz
    have : k = 0 := by
      have : |(k : ℝ)| < 1 := hz
      rw [abs_lt] at this
      have h1 : (-1 : ℤ) < k := by exact_mod_cast this.1
      have h2 : k < 1 := by exact_mod_cast this.2
      omega
    exact hz0 (by rw [hz', this]; simp)
  have hne : ∀ m : ℕ, (1 : ℂ) - z ^ 2 / ((m : ℂ) + 1) ^ 2 ≠ 0 := by
    intro m h
    have h1 : z ^ 2 / ((m : ℂ) + 1) ^ 2 = 1 := by linear_combination -h
    have := norm_sq_div_succ_sq_lt_one hz m
    rw [h1, norm_one] at this
    exact lt_irrefl _ this
  set P : ℕ → ℂ := fun N => ∏ j ∈ range N, ((1 : ℂ) - z ^ 2 / ((j : ℂ) + 1) ^ 2) with hP
  have h1 : Tendsto (fun N => (P N)⁻¹) atTop (𝓝 (cexp F)) := by
    have := (continuous_exp.tendsto F).comp hF.tendsto_sum_nat
    refine this.congr fun N => ?_
    simp only [Function.comp_apply, hP]
    rw [Complex.exp_sum, ← prod_inv_distrib]
    refine prod_congr rfl fun j _ => ?_
    rw [Complex.exp_neg, Complex.exp_log (hne j)]
  have h2 : Tendsto (fun N => (P N)⁻¹) atTop (𝓝 (π * z / sin (π * z))) := by
    have hπz : (π : ℂ) * z ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) hz0
    have := ((Complex.tendsto_euler_sin_prod z).inv₀ hsin).const_mul ((π : ℂ) * z)
    refine this.congr fun N => ?_
    simp only [hP]
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hπz, one_mul]
  exact tendsto_nhds_unique h1 h2

/-- `|Im F| < π` for the double series. -/
private lemma abs_im_lt_pi_of_hasSum_neg_log {z : ℂ} (hz : ‖z‖ < 1) {F : ℂ}
    (hF : HasSum (fun m : ℕ => -log (1 - z ^ 2 / ((m : ℂ) + 1) ^ 2)) F) :
    |F.im| < π := by
  set L : ℕ → ℂ := fun m => -log (1 - z ^ 2 / ((m : ℂ) + 1) ^ 2) with hL
  have hbd : ∀ m : ℕ, ‖L (m + 1)‖ ≤ 2 * (1 / ((m : ℝ) + 2) ^ 2) := by
    intro m
    set w : ℂ := z ^ 2 / (((m + 1 : ℕ) : ℂ) + 1) ^ 2 with hwdef
    have hw : ‖w‖ ≤ 1 / ((m : ℝ) + 2) ^ 2 := by
      have := norm_sq_div_succ_sq_le hz (m + 1)
      rw [show ((m + 1 : ℕ) : ℝ) + 1 = (m : ℝ) + 2 by push_cast; ring] at this
      exact this
    have hq : 1 / ((m : ℝ) + 2) ^ 2 ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have hw' : ‖w‖ ≤ 1 / 4 := hw.trans hq
    have hl := Complex.norm_log_one_add_le (z := -w) (by rw [norm_neg]; linarith)
    rw [norm_neg] at hl
    have hLe : L (m + 1) = -log (1 + -w) := by
      simp only [hL, hwdef]; ring_nf
    rw [hLe, norm_neg]
    have hnn : 0 ≤ ‖w‖ := norm_nonneg _
    have hpos : 0 < 1 - ‖w‖ := by linarith
    have hinv : (1 - ‖w‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hpos (by norm_num)]; linarith
    have : ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ / 2 ≤ ‖w‖ := by
      have h2 : ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ ≤ ‖w‖ ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      nlinarith
    linarith
  have hsL : Summable fun m : ℕ => L (m + 1) := (summable_nat_add_iff 1).mpr hF.summable
  have hb : HasSum (fun m : ℕ => 2 * (1 / ((m : ℝ) + 2) ^ 2)) (2 * (π ^ 2 / 6 - 1)) := by
    have h := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one] at h
    norm_num at h
    refine (h.mul_left 2).congr_fun fun m => ?_
    ring_nf
  have hF' : F = L 0 + ∑' m, L (m + 1) := by
    rw [← hF.tsum_eq, hF.summable.tsum_eq_zero_add]
  have h0 : |(L 0).im| < π / 2 := by
    simp only [hL, neg_im, log_im, abs_neg, Nat.cast_zero, zero_add, one_pow, div_one]
    refine abs_arg_lt_pi_div_two_iff.mpr (Or.inl ?_)
    have : (z ^ 2).re ≤ ‖z‖ ^ 2 := by
      rw [← norm_pow]; exact re_le_norm _
    simp only [sub_re, one_re]
    nlinarith [norm_nonneg z]
  have hrest : |(∑' m, L (m + 1)).im| ≤ 2 * (π ^ 2 / 6 - 1) :=
    (abs_im_le_norm _).trans ((norm_tsum_le_tsum_norm hsL.norm).trans
      (hb.tsum_eq ▸ hsL.norm.tsum_le_tsum hbd hb.summable))
  rw [hF', add_im]
  have hπ := Real.pi_lt_d2
  have hπ3 := Real.pi_gt_three
  calc |(L 0).im + (∑' m, L (m + 1)).im| ≤ |(L 0).im| + |(∑' m, L (m + 1)).im| := abs_add_le _ _
    _ < π / 2 + 2 * (π ^ 2 / 6 - 1) := by linarith
    _ ≤ π := by nlinarith

/-- DLMF 25.8.8: `∑_{k≥1} (ζ(2k)/k) z^{2k} = ln(πz/sin(πz))` for `|z| < 1`, with the principal
logarithm (at `z = 0` both sides are `0`). -/
@[dlmf 25.8.E8]
theorem hasSum_riemannZeta_two_mul_div_mul_pow {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => riemannZeta (2 * (k + 1)) / (k + 1) * z ^ (2 * (k + 1)))
      (log (π * z / sin (π * z))) := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  obtain ⟨F, h1, h2⟩ := exists_hasSum_riemannZeta_two_mul_and_neg_log hz
  have him := abs_im_lt_pi_of_hasSum_neg_log hz h2
  rw [← exp_eq_pi_mul_div_sin_of_hasSum_neg_log hz hz0 h2, Complex.log_exp (by linarith [(abs_lt.mp him).1])
    (by linarith [(abs_lt.mp him).2])]
  exact h1

end DLMF.Zeta
