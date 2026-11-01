/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.Basic
public import Mathlib.Analysis.PSeriesComplex
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The Barnes G-function

This file defines the Barnes G-function by the Weierstrass product for `G(z+1)`
(DLMF 5.17.3) and the Glaisher–Kinkelin constant (DLMF 5.17.6), and proves the convergence of
the product, the functional equation and the values at the integers (DLMF 5.17.1–5.17.2).

## Main definitions

* `barnesGTerm`: the Weierstrass factors of DLMF 5.17.3.
* `barnesGSucc`: `G(z+1)` defined by the Weierstrass product (DLMF 5.17.3).
* `barnesG`: `G(z) = G((z-1)+1)`.
* `barnesShiftSeq`: the partial products used to compare `G(z+2)` with `Γ(z+1) G(z+1)`.
* `glaisherKinkelin`: the Glaisher–Kinkelin constant `A` (DLMF 5.17.6).

## Main results

* `multipliable_barnesGTerm`: the Weierstrass product converges.
* `barnesG_one`, `barnesG_add_one`, `barnesGSucc_eq_Gamma_mul`: `G(1) = 1` and the functional
  equation `G(z + 1) = Γ(z) G(z)` (DLMF 5.17.1).
* `barnesG_nat`: `G(n) = ∏_{k=1}^{n-2} k!` (DLMF 5.17.2).

## Implementation notes

At `z = 0` the functional equation reads `G(1) = Γ(0) G(0)`, a limit `∞ · 0`; with the
totalized `Γ(0) = 0` it fails there, so `barnesG_add_one` excludes `z = 0`. The integral formula
for `ln G(x+1)` and the zeta form of `ln A` are in `DLMF.Gamma.BarnesG.WeierstrassProduct`.
-/

@[expose] public section

open Complex Filter

open scoped Real Topology

noncomputable section

namespace DLMF.Gamma

/-- Weierstrass factors in DLMF 5.17.3. -/
def barnesGTerm (z : ℂ) (k : ℕ) : ℂ :=
  let n : ℂ := k + 1
  (1 + z / n) ^ n * Complex.exp (-z + z ^ 2 / (2 * n))

/-- Barnes `G(z+1)` via the Weierstrass product. -/
@[dlmf 5.17.E3]
def barnesGSucc (z : ℂ) : ℂ :=
  (2 * π : ℂ) ^ (z / 2) *
    Complex.exp (-(z * (z + 1) / 2) - (Real.eulerMascheroniConstant : ℂ) * z ^ 2 / 2) *
      ∏' k : ℕ, barnesGTerm z k

/-- Barnes `G(z) = G((z-1)+1)`. -/
def barnesG (z : ℂ) : ℂ := barnesGSucc (z - 1)

/-- DLMF 5.17.1: `G(1) = 1`. -/
@[dlmf 5.17.E1]
theorem barnesG_one : barnesG 1 = 1 := by
  unfold barnesG
  rw [sub_self]
  have hterm : ∀ k : ℕ, barnesGTerm 0 k = 1 := by
    intro k
    unfold barnesGTerm
    simp [one_cpow, Complex.exp_zero]
  unfold barnesGSucc
  simp [hterm, cpow_zero, Complex.exp_zero, tprod_one]

/-- The Weierstrass factor of 5.17.3: `(1 + z/(k+1))^(k+1) exp(-z + z²/(2(k+1)))`. -/
theorem barnesGTerm_eq (z : ℂ) (k : ℕ) :
    barnesGTerm z k = (1 + z / (k + 1)) ^ (k + 1) *
      Complex.exp (-z + z ^ 2 / (2 * (k + 1))) := by
  unfold barnesGTerm
  simp only
  congr 1
  rw [show ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) by push_cast; ring, cpow_natCast]

/-- For `2|z| ≤ k + 1`, the Weierstrass factor is `exp((k+1)(log(1 + z/(k+1)) - (u - u²/2)))` with
`u = z/(k+1)`, the logarithm minus its degree-2 Taylor polynomial. -/
theorem barnesGTerm_eq_exp {z : ℂ} {k : ℕ} (hk : 2 * ‖z‖ ≤ k + 1) :
    barnesGTerm z k = Complex.exp ((k + 1) *
      (Complex.log (1 + z / (k + 1)) - logTaylor 3 (z / (k + 1)))) := by
  have hn : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
  have hw : ‖z / (k + 1)‖ < 1 := by
    rw [norm_div, show ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) by push_cast; ring,
      Complex.norm_natCast, div_lt_one (by positivity)]
    push_cast
    nlinarith [norm_nonneg z]
  have h1 : (1 + z / (k + 1)) ≠ 0 := by
    intro h
    have : z / (k + 1) = -1 := by linear_combination h
    rw [this] at hw; simp at hw
  rw [barnesGTerm_eq]
  have hT : logTaylor 3 (z / (k + 1)) = z / (k + 1) - (z / (k + 1)) ^ 2 / 2 := by
    simp [logTaylor, Finset.sum_range_succ]; ring
  rw [hT, show ((k : ℂ) + 1) * (Complex.log (1 + z / (k + 1)) -
      (z / (k + 1) - (z / (k + 1)) ^ 2 / 2)) =
      ((k + 1 : ℕ) : ℂ) * Complex.log (1 + z / (k + 1)) + (-z + z ^ 2 / (2 * (k + 1))) by
    push_cast; field_simp; ring, Complex.exp_add (((k + 1 : ℕ) : ℂ) * _), Complex.exp_nat_mul,
    Complex.exp_log h1]

/-- For large `k`, the Weierstrass factor of 5.17.3 satisfies `|factor - 1| ≤ 2|z|³/(k+1)²`. -/
theorem norm_barnesGTerm_sub_one_le {z : ℂ} {k : ℕ} (hk : 2 * ‖z‖ ≤ k + 1)
    (hk' : ‖z‖ ^ 3 ≤ ((k : ℝ) + 1) ^ 2) :
    ‖barnesGTerm z k - 1‖ ≤ 2 * ‖z‖ ^ 3 / ((k : ℝ) + 1) ^ 2 := by
  have hn : (0 : ℝ) < k + 1 := by positivity
  have hnw : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
    rw [show ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    push_cast; ring
  set w := z / ((k : ℂ) + 1) with hw_def
  have hwn : ‖w‖ = ‖z‖ / (k + 1) := by rw [hw_def, norm_div, hnw]
  have hw2 : ‖w‖ ≤ 1 / 2 := by
    rw [hwn, div_le_iff₀ hn]; linarith
  have hw1 : ‖w‖ < 1 := by linarith
  have hlog := Complex.norm_log_sub_logTaylor_le 2 hw1
  set e := ((k : ℂ) + 1) * (Complex.log (1 + w) - logTaylor 3 w) with he_def
  have hinv : (1 - ‖w‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have he : ‖e‖ ≤ (2 / 3) * ‖z‖ ^ 3 / ((k : ℝ) + 1) ^ 2 := by
    rw [he_def, norm_mul, hnw]
    have h3 : ‖w‖ ^ (2 + 1) * (1 - ‖w‖)⁻¹ / (2 + 1 : ℕ) ≤ ‖w‖ ^ 3 * 2 / 3 := by
      push_cast
      gcongr
    calc ((k : ℝ) + 1) * ‖Complex.log (1 + w) - logTaylor 3 w‖
        ≤ ((k : ℝ) + 1) * (‖w‖ ^ 3 * 2 / 3) := by
          gcongr
          exact hlog.trans (by exact_mod_cast h3)
      _ = (2 / 3) * ‖z‖ ^ 3 / ((k : ℝ) + 1) ^ 2 := by
          rw [hwn]; field_simp
  have he1 : ‖e‖ ≤ 1 := by
    refine he.trans ?_
    rw [div_le_one (by positivity)]; nlinarith [norm_nonneg z]
  rw [barnesGTerm_eq_exp hk]
  refine (Complex.norm_exp_sub_one_le he1).trans ?_
  calc 2 * ‖e‖ ≤ 2 * ((2 / 3) * ‖z‖ ^ 3 / ((k : ℝ) + 1) ^ 2) := by gcongr
    _ ≤ 2 * ‖z‖ ^ 3 / ((k : ℝ) + 1) ^ 2 := by
      have hq : 0 ≤ ‖z‖ ^ 3 / ((k : ℝ) + 1) ^ 2 := by positivity
      rw [mul_div_assoc, mul_div_assoc]
      nlinarith

/-- `∑ₖ |factor_k(z) - 1|` converges. -/
theorem summable_norm_barnesGTerm_sub_one (z : ℂ) :
    Summable fun k : ℕ => ‖barnesGTerm z k - 1‖ := by
  have hs : Summable fun k : ℕ => 2 * ‖z‖ ^ 3 / ((k : ℝ) + 1) ^ 2 := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    refine (this.mul_left (2 * ‖z‖ ^ 3)).congr fun k => ?_
    push_cast; ring
  refine Summable.of_norm_bounded_eventually_nat hs ?_
  have h1 : ∀ᶠ k : ℕ in atTop, 2 * ‖z‖ ≤ (k : ℝ) + 1 :=
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).eventually_ge_atTop _
  have h2 : ∀ᶠ k : ℕ in atTop, ‖z‖ ^ 3 ≤ ((k : ℝ) + 1) ^ 2 :=
    ((tendsto_pow_atTop two_ne_zero).comp
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)).eventually_ge_atTop _
  filter_upwards [h1, h2] with k hk hk'
  rw [norm_norm]
  exact norm_barnesGTerm_sub_one_le hk hk'

/-- The Weierstrass product of 5.17.3 is multipliable. -/
theorem multipliable_barnesGTerm (z : ℂ) : Multipliable (barnesGTerm z) := by
  have h := Complex.multipliable_one_add_of_summable
    (Summable.of_norm (summable_norm_barnesGTerm_sub_one z))
  simpa using h

/-- Shift relation between the Weierstrass factors at `z` and at `z - 1`. -/
theorem barnesGTerm_shift (z : ℂ) (k : ℕ) :
    ((k : ℂ) + z) ^ (k + 1) * barnesGTerm z k =
      ((k : ℂ) + 1 + z) ^ (k + 1) * barnesGTerm (z - 1) k *
        Complex.exp (-1 + (z - 1 / 2) / (k + 1)) := by
  have hn : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  rw [barnesGTerm_eq, barnesGTerm_eq,
    show 1 + z / ((k : ℂ) + 1) = ((k : ℂ) + 1 + z) / ((k : ℂ) + 1) by field_simp,
    show 1 + (z - 1) / ((k : ℂ) + 1) = ((k : ℂ) + z) / ((k : ℂ) + 1) by field_simp; ring,
    show -z + z ^ 2 / (2 * ((k : ℂ) + 1)) = (-(z - 1) + (z - 1) ^ 2 / (2 * ((k : ℂ) + 1))) +
      (-1 + (z - 1 / 2) / ((k : ℂ) + 1)) by field_simp; ring,
    Complex.exp_add, div_pow, div_pow]
  field_simp

open Finset in
/-- Partial-product form of the recurrence `G(z + 1) = Γ(z) G(z)`. -/
theorem barnesG_partial (z : ℂ) (N : ℕ) :
    (∏ m ∈ range N, (z + m)) * ∏ k ∈ range N, barnesGTerm z k =
      (z + N) ^ N * (∏ k ∈ range N, Complex.exp (-1 + (z - 1 / 2) / (k + 1))) *
        ∏ k ∈ range N, barnesGTerm (z - 1) k := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hs := barnesGTerm_shift z N
    simp only [prod_range_succ]
    push_cast
    linear_combination ((z + N) * barnesGTerm z N) * ih +
      ((∏ k ∈ range N, Complex.exp (-1 + (z - 1 / 2) / (k + 1))) *
        ∏ k ∈ range N, barnesGTerm (z - 1) k) * hs

open Finset in
/-- The correction factor relating the partial products of `G(z+1)` and `Γ(z) G(z)`. -/
def barnesShiftSeq (z : ℂ) (N : ℕ) : ℂ :=
  (z + N) ^ (N + 1) * (∏ k ∈ range N, Complex.exp (-1 + (z - 1 / 2) / (k + 1))) /
    ((N : ℂ) ^ z * N.factorial)

open Finset in
/-- Closed form of the correction factor `barnesShiftSeq z N` through the harmonic numbers and
Stirling's sequence. -/
theorem barnesShiftSeq_eq (z : ℂ) {N : ℕ} (hN : 1 ≤ N) :
    barnesShiftSeq z N = (1 + z / N) ^ (N + 1) *
      Complex.exp ((z - 1 / 2) * (((harmonic N : ℝ) - Real.log N : ℝ) : ℂ)) /
        ((Stirling.stirlingSeq N * √2 : ℝ) : ℂ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  set L : ℂ := (Real.log N : ℂ) with hL
  have hexpL : Complex.exp L = N := by
    rw [hL, Complex.natCast_log, Complex.exp_log hN0]
  have hcpow : (N : ℂ) ^ z = Complex.exp (L * z) := by
    rw [cpow_def_of_ne_zero hN0, hL, Complex.natCast_log]
  have hH : ((harmonic N : ℝ) : ℂ) = ∑ k ∈ range N, 1 / ((k : ℂ) + 1) := by
    simp [harmonic]
  have hE : (∏ k ∈ range N, Complex.exp (-1 + (z - 1 / 2) / (k + 1))) =
      Complex.exp (-N + (z - 1 / 2) * ((harmonic N : ℝ) : ℂ)) := by
    rw [← Complex.exp_sum, hH, Finset.mul_sum]
    congr 1
    rw [Finset.sum_add_distrib]
    simp only [sum_const, card_range, nsmul_eq_mul]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun k _ => ?_
      ring
  have hsq : ((√(N : ℝ) : ℝ) : ℂ) = Complex.exp (L / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hNr, Complex.ofReal_exp, hL]
    push_cast; ring_nf
  have hfac : (N.factorial : ℂ) = ((Stirling.stirlingSeq N * √2 : ℝ) : ℂ) *
      ((√(N : ℝ) : ℝ) : ℂ) * (N : ℂ) ^ N / Complex.exp N := by
    have hpos : 0 < √(2 * N : ℝ) * (N / Real.exp 1) ^ N := by positivity
    have h1 : (N.factorial : ℝ) =
        Stirling.stirlingSeq N * (√(2 * N : ℝ) * (N / Real.exp 1) ^ N) := by
      rw [Stirling.stirlingSeq, div_mul_cancel₀ _ hpos.ne']
    have h2 : √(2 * N : ℝ) = √2 * √(N : ℝ) := Real.sqrt_mul (by norm_num) _
    have h3 : (Real.exp 1) ^ N = Real.exp N := by rw [← Real.exp_nat_mul, mul_one]
    have h4 : (N.factorial : ℂ) = ((N.factorial : ℝ) : ℂ) := by push_cast; rfl
    rw [h4, h1, h2, div_pow, h3]
    push_cast
    ring
  have hz : (z + N) ^ (N + 1) = (N : ℂ) ^ N * Complex.exp L * (1 + z / N) ^ (N + 1) := by
    rw [hexpL, show z + N = N * (1 + z / N) by field_simp; ring, mul_pow, pow_succ]
  rw [barnesShiftSeq, hE, hcpow, hfac, hsq, hz, Complex.ofReal_sub, ← hL, Complex.ofReal_mul]
  have hs0 : ((Stirling.stirlingSeq N : ℝ) : ℂ) ≠ 0 := by
    have := Stirling.stirlingSeq'_pos (N - 1)
    rw [show N - 1 + 1 = N by omega] at this
    exact_mod_cast this.ne'
  have h20 : ((√2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  field_simp
  have e1 : Complex.exp L *
      Complex.exp ((-(N * 2) + (z * 2 - 1) * ((harmonic N : ℝ) : ℂ)) / 2) * Complex.exp N =
      Complex.exp (z * L) * Complex.exp (L / 2) *
        Complex.exp ((z * 2 - 1) * (((harmonic N : ℝ) : ℂ) - L) / 2) := by
    simp only [← Complex.exp_add]
    congr 1
    ring
  linear_combination (((N : ℂ) + z) / N) ^ (N + 1) * e1

/-- `barnesShiftSeq z N → e^z e^((z - 1/2)γ) / √(2π)`. -/
theorem tendsto_barnesShiftSeq (z : ℂ) :
    Tendsto (barnesShiftSeq z) atTop
      (𝓝 (Complex.exp z * Complex.exp ((z - 1 / 2) * Real.eulerMascheroniConstant) /
        ((√π * √2 : ℝ) : ℂ))) := by
  have h1 : Tendsto (fun N : ℕ => (1 + z / N) ^ (N + 1)) atTop (𝓝 (Complex.exp z * 1)) := by
    have ha := Complex.tendsto_one_add_div_pow_exp z
    have hb : Tendsto (fun N : ℕ => 1 + z / N) atTop (𝓝 1) := by
      simpa using (tendsto_const_div_atTop_nhds_zero_nat z).const_add 1
    simpa [pow_succ] using ha.mul hb
  have h2 : Tendsto (fun N : ℕ => Complex.exp ((z - 1 / 2) *
      (((harmonic N : ℝ) - Real.log N : ℝ) : ℂ))) atTop
      (𝓝 (Complex.exp ((z - 1 / 2) * Real.eulerMascheroniConstant))) := by
    have := (Complex.continuous_ofReal.tendsto _).comp Real.tendsto_harmonic_sub_log
    exact ((this.const_mul (z - 1 / 2)).cexp)
  have h3 : Tendsto (fun N : ℕ => ((Stirling.stirlingSeq N * √2 : ℝ) : ℂ)) atTop
      (𝓝 ((√π * √2 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp
      (Stirling.tendsto_stirlingSeq_sqrt_pi.mul_const _)
  have hne : ((√π * √2 : ℝ) : ℂ) ≠ 0 := by
    have : 0 < √π * √2 := by positivity
    exact_mod_cast this.ne'
  have h := (h1.mul h2).div h3 hne
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [barnesShiftSeq_eq z hN]
  rfl

open Finset in
/-- For `z` not a nonpositive integer, the partial products at `z` equal `Γ_N(z) · barnesShiftSeq z
N` times the partial products at `z - 1`. -/
theorem prod_barnesGTerm_eq (z : ℂ) (hz : ∀ m : ℕ, z ≠ -m) {N : ℕ} (hN : 1 ≤ N) :
    ∏ k ∈ range N, barnesGTerm z k =
      GammaSeq z N * barnesShiftSeq z N * ∏ k ∈ range N, barnesGTerm (z - 1) k := by
  have hQ : ∀ n : ℕ, ∏ m ∈ range n, (z + m) ≠ 0 := fun n =>
    prod_ne_zero_iff.mpr fun m _ h => hz m (by linear_combination h)
  have hzN : z + N ≠ 0 := fun h => hz N (by linear_combination h)
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hpow : (N : ℂ) ^ z ≠ 0 := by
    rw [cpow_def_of_ne_zero hN0]; exact Complex.exp_ne_zero _
  have hfac : (N.factorial : ℂ) ≠ 0 := by exact_mod_cast N.factorial_ne_zero
  have hpart := barnesG_partial z N
  have hQN := hQ N
  rw [GammaSeq, barnesShiftSeq, prod_range_succ]
  generalize ∏ m ∈ range N, (z + m) = Q at hQN hpart ⊢
  generalize ∏ k ∈ range N, Complex.exp (-1 + (z - 1 / 2) / (k + 1)) = E at hpart ⊢
  generalize ∏ k ∈ range N, barnesGTerm z k = P at hpart ⊢
  generalize ∏ k ∈ range N, barnesGTerm (z - 1) k = P' at hpart ⊢
  field_simp
  linear_combination (z + N) * hpart

/-- DLMF 5.17.1 in the form `G(z + 1) = Γ(z) G(z)` for `z ≠ 0`. -/
theorem barnesGSucc_eq_Gamma_mul {z : ℂ} (hz : z ≠ 0) :
    barnesGSucc z = Complex.Gamma z * barnesGSucc (z - 1) := by
  by_cases hneg : ∃ m : ℕ, z = -m
  · obtain ⟨m, rfl⟩ := hneg
    have hm : m ≠ 0 := by rintro rfl; simp at hz
    rw [Complex.Gamma_neg_nat_eq_zero, zero_mul]
    unfold barnesGSucc
    rw [tprod_of_exists_eq_zero ⟨m - 1, ?_⟩, mul_zero]
    have hcast : ((m - 1 : ℕ) : ℂ) + 1 = m := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm
    rw [barnesGTerm_eq, hcast, show 1 + -(m : ℂ) / m = 0 by field_simp; ring,
      zero_pow (by omega), zero_mul]
  · push Not at hneg
    have hlim1 := (multipliable_barnesGTerm z).hasProd.tendsto_prod_nat
    have hlim2 := ((GammaSeq_tendsto_Gamma z).mul (tendsto_barnesShiftSeq z)).mul
      (multipliable_barnesGTerm (z - 1)).hasProd.tendsto_prod_nat
    have heq := tendsto_nhds_unique hlim1 (hlim2.congr' (by
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact (prod_barnesGTerm_eq z hneg hN).symm))
    unfold barnesGSucc
    rw [heq]
    have h2pi : (2 * π : ℂ) ≠ 0 := by
      have : (0 : ℝ) < 2 * π := by positivity
      exact_mod_cast this.ne'
    have hsqrt : (2 * π : ℂ) ^ (1 / 2 : ℂ) = ((√π * √2 : ℝ) : ℂ) := by
      rw [← Real.sqrt_mul' _ (by norm_num : (0 : ℝ) ≤ 2), mul_comm π 2,
        Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
      push_cast; ring_nf
    have hne : ((√π * √2 : ℝ) : ℂ) ≠ 0 := by
      have : 0 < √π * √2 := by positivity
      exact_mod_cast this.ne'
    have hsplit : (2 * π : ℂ) ^ (z / 2) =
        (2 * π : ℂ) ^ ((z - 1) / 2) * (2 * π : ℂ) ^ (1 / 2 : ℂ) := by
      rw [← cpow_add _ _ h2pi]; congr 1; ring
    have hexp : Complex.exp (-(z * (z + 1) / 2) - (Real.eulerMascheroniConstant : ℂ) * z ^ 2 / 2) *
        (Complex.exp z * Complex.exp ((z - 1 / 2) * Real.eulerMascheroniConstant)) =
        Complex.exp (-((z - 1) * (z - 1 + 1) / 2) -
          (Real.eulerMascheroniConstant : ℂ) * (z - 1) ^ 2 / 2) := by
      simp only [← Complex.exp_add]; congr 1; ring
    rw [hsplit, hsqrt, ← hexp]
    field_simp

/-- The functional equation of Barnes' G-function. At `z = 0` it reads `G(1) = Γ(0) G(0)`, a
limit `∞ · 0`; the totalized `Γ(0) = 0` gives `0`, so `z = 0` is excluded. -/
@[dlmf 5.17.E1]
theorem barnesG_add_one {z : ℂ} (hz : z ≠ 0) :
    barnesG (z + 1) = Complex.Gamma z * barnesG z := by
  rw [barnesG, barnesG, add_sub_cancel_right]
  exact barnesGSucc_eq_Gamma_mul hz

/-- DLMF 5.17.2: `G(n) = ∏_{k=1}^{n-2} k!` for `n ≥ 2`. -/
@[dlmf 5.17.E2]
theorem barnesG_nat (n : ℕ) (hn : 2 ≤ n) :
    barnesG n = ∏ k ∈ Finset.Icc 1 (n - 2), (k.factorial : ℂ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 2 = m by omega]
  induction m with
  | zero =>
    have h := barnesG_add_one (z := 1) one_ne_zero
    rw [Complex.Gamma_one, one_mul, barnesG_one] at h
    rw [show ((0 + 2 : ℕ) : ℂ) = 1 + 1 by norm_num, h]
    simp
  | succ m ih =>
    have h := barnesG_add_one (z := ((m + 2 : ℕ) : ℂ)) (by exact_mod_cast (by omega : m + 2 ≠ 0))
    rw [Finset.prod_Icc_succ_top (by omega), ← ih (by omega)]
    push_cast at h ⊢
    rw [show (m : ℂ) + 1 + 2 = (m : ℂ) + 2 + 1 by ring, h,
      show (m : ℂ) + 2 = ((m + 1 : ℕ) : ℂ) + 1 by push_cast; ring, Complex.Gamma_nat_eq_factorial]
    push_cast
    ring

/-- Glaisher–Kinkelin constant, via the first closed form for `C` in 5.17.7. -/
@[dlmf 5.17.E6]
def glaisherKinkelin : ℝ :=
  Real.exp ((Real.eulerMascheroniConstant + Real.log (2 * π)) / 12 -
    (deriv riemannZeta 2).re / (2 * π ^ 2))

end DLMF.Gamma
