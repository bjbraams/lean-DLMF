/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.PSeriesComplex
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import DLMF.Gamma.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import DLMF.Gamma.IntegralRepresentations

/-!
# The Weierstrass product for Barnes G

Convergence, the shift identity and the real logarithm of the Barnes G product.

Source references and common attribution are retained in
`DLMF.Gamma.BarnesG`.
-/

@[expose] public section

open Complex Filter MeasureTheory intervalIntegral

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

/-! ### The Weierstrass product: convergence and the shift identity -/

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

/-- DLMF 5.17.2 in the form `G(z + 1) = Γ(z) G(z)` for `z ≠ 0`. -/
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

/-! ### The real logarithm of the Weierstrass product -/

/-- `u - u²/2 ≤ log(1 + u)` for `u ≥ 0`. -/
theorem sub_sq_div_two_le_log_one_add {u : ℝ} (hu : 0 ≤ u) : u - u ^ 2 / 2 ≤ Real.log (1 + u) := by
  let F : ℝ → ℝ := fun y => Real.log (1 + y) - y + y ^ 2 / 2
  have A : ∀ y ∈ Set.Icc 0 u, HasDerivAt F (1 / (1 + y) - 1 + y) y := by
    intro y hy
    have h1 : (1 + y) ≠ 0 := by linarith [hy.1]
    have := (((hasDerivAt_id y).const_add 1).log h1).sub (hasDerivAt_id y)
    have h2 : HasDerivAt F (1 / (1 + y) - 1 + (2 : ℕ) * y ^ (2 - 1) / 2) y :=
      this.add ((hasDerivAt_pow 2 y).div_const 2)
    convert h2 using 1
    norm_num
  have hmono : MonotoneOn F (Set.Icc 0 u) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 u)
      (fun y hy ↦ (A y hy).continuousAt.continuousWithinAt)
      (fun y hy ↦ (A y (interior_subset hy)).hasDerivWithinAt) ?_
    intro y hy
    simp only [interior_Icc, Set.mem_Ioo] at hy
    have h1 : 0 < 1 + y := by linarith
    rw [show 1 / (1 + y) - 1 + y = y ^ 2 / (1 + y) by field_simp; ring]
    positivity
  have := hmono ⟨le_rfl, hu⟩ ⟨hu, le_rfl⟩ hu
  simp only [F, add_zero, Real.log_one, sub_zero] at this
  norm_num at this
  linarith

/-- The terms of the Weierstrass series for `log Γ(t+1)`. -/
def logGammaTerm (t : ℝ) (n : ℕ) : ℝ := t / (n + 1) - Real.log (1 + t / (n + 1))

/-- `t/(n+1) - log(1 + t/(n+1)) ≥ 0` for `t ≥ 0`. -/
theorem logGammaTerm_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : 0 ≤ logGammaTerm t n := by
  have := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + t / (n + 1))
  unfold logGammaTerm; linarith

/-- `t/(n+1) - log(1 + t/(n+1)) ≤ t²/(2(n+1)²)` for `t ≥ 0`. -/
theorem logGammaTerm_le {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    logGammaTerm t n ≤ t ^ 2 / (2 * ((n : ℝ) + 1) ^ 2) := by
  have := sub_sq_div_two_le_log_one_add (by positivity : 0 ≤ t / (n + 1))
  unfold logGammaTerm
  rw [div_pow] at this
  have : t ^ 2 / (2 * ((n : ℝ) + 1) ^ 2) = t ^ 2 / ((n : ℝ) + 1) ^ 2 / 2 := by
    rw [div_div, mul_comm]
  linarith

/-- `∑ₙ (t/(n+1) - log(1 + t/(n+1)))` converges for `t ≥ 0`. -/
theorem summable_logGammaTerm {t : ℝ} (ht : 0 ≤ t) : Summable (logGammaTerm t) := by
  have hs : Summable fun n : ℕ => t ^ 2 / (2 * ((n : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    refine (this.mul_left (t ^ 2 / 2)).congr fun k => ?_
    push_cast; field_simp
  exact Summable.of_nonneg_of_le (logGammaTerm_nonneg ht) (logGammaTerm_le ht) hs

/-- `∑ₙ (t/(n+1) - log(1 + t/(n+1))) = log Γ(t + 1) + γ t` for `t ≥ 0`. -/
theorem hasSum_logGammaTerm {t : ℝ} (ht : 0 ≤ t) :
    HasSum (logGammaTerm t)
      (Real.log (Real.Gamma (t + 1)) + Real.eulerMascheroniConstant * t) := by
  rcases ht.eq_or_lt with rfl | ht
  · have h0 : logGammaTerm 0 = 0 := by funext n; simp [logGammaTerm]
    rw [h0]
    simp only [zero_add, Real.Gamma_one, Real.log_one, mul_zero]
    exact hasSum_zero
  have hW : ∀ n : ℕ, 0 < Real.weierstrassGammaTerm t n := fun n => by
    unfold Real.weierstrassGammaTerm; positivity
  have hlogW : ∀ n : ℕ, Real.log (Real.weierstrassGammaTerm t n) = -logGammaTerm t n := by
    intro n
    unfold Real.weierstrassGammaTerm logGammaTerm
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hsum : Summable fun n => Real.log (Real.weierstrassGammaTerm t n) := by
    simp only [hlogW]; exact (summable_logGammaTerm ht.le).neg
  have hprod := Real.rexp_tsum_eq_tprod hW hsum
  have hG := Real.one_div_Gamma_eq_tprod t
  rw [← hprod] at hG
  simp only [hlogW, tsum_neg] at hG
  have hGpos : 0 < Real.Gamma t := Real.Gamma_pos_of_pos ht
  have hG1 : Real.Gamma (t + 1) = Real.exp (∑' n, logGammaTerm t n -
      Real.eulerMascheroniConstant * t) := by
    rw [Real.Gamma_add_one ht.ne', Real.exp_sub]
    have : Real.Gamma t = (t * Real.exp (Real.eulerMascheroniConstant * t) *
        Real.exp (-∑' n, logGammaTerm t n))⁻¹ := by rw [← hG, inv_inv]
    rw [this, Real.exp_neg]
    field_simp
  rw [hG1, Real.log_exp, sub_add_cancel]
  exact (summable_logGammaTerm ht.le).hasSum

/-- Each term `t/(n+1) - log(1 + t/(n+1))` is continuous on `[0, ∞)`. -/
theorem continuousOn_logGammaTerm (n : ℕ) :
    ContinuousOn (fun t => logGammaTerm t n) (Set.Ici 0) := by
  intro t ht
  have h1 : (1 + t / (n + 1)) ≠ 0 := by
    have : (0 : ℝ) ≤ t := ht
    positivity
  unfold logGammaTerm
  exact (((continuous_id.div_const _).continuousAt).sub
    ((continuous_const.add (continuous_id.div_const _)).continuousAt.log h1)).continuousWithinAt

/-- `∫₀ˣ (t/(n+1) - log(1 + t/(n+1))) dt = x²/(2(n+1)) - ((n + 1 + x) log(1 + x/(n+1)) - x)`. -/
theorem integral_logGammaTerm {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    ∫ t in (0 : ℝ)..x, logGammaTerm t n =
      x ^ 2 / (2 * (n + 1)) - (((n : ℝ) + 1 + x) * Real.log (1 + x / (n + 1)) - x) := by
  have hm : (0 : ℝ) < n + 1 := by positivity
  have hsub : Set.uIcc 0 x ⊆ Set.Ici 0 := by
    rw [Set.uIcc_of_le hx]; exact Set.Icc_subset_Ici_self
  have hderiv : ∀ t ∈ Set.uIcc 0 x, HasDerivAt
      (fun t : ℝ => t ^ 2 / (2 * (n + 1)) - (((n : ℝ) + 1 + t) * Real.log (1 + t / (n + 1)) - t))
      (logGammaTerm t n) t := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := hsub ht
    have h1 : (1 + t / (n + 1)) ≠ 0 := by positivity
    have hlog : HasDerivAt (fun t : ℝ => Real.log (1 + t / (n + 1)))
        ((1 / (n + 1)) / (1 + t / (n + 1))) t := by
      have := ((hasDerivAt_id t).div_const ((n : ℝ) + 1)).const_add 1
      exact this.log h1
    have h := (((hasDerivAt_pow 2 t).div_const (2 * ((n : ℝ) + 1))).sub
      ((((hasDerivAt_id t).const_add ((n : ℝ) + 1)).mul hlog).sub (hasDerivAt_id t)))
    refine h.congr_deriv ?_
    unfold logGammaTerm
    simp only [id]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuousOn_logGammaTerm n).mono hsub).intervalIntegrable]
  simp

/-- The logarithms of the factors in the Weierstrass product for `G(x+1)`, for real `x`. -/
def barnesLogTerm (x : ℝ) (n : ℕ) : ℝ :=
  (n + 1) * Real.log (1 + x / (n + 1)) - x + x ^ 2 / (2 * (n + 1))

/-- `barnesLogTerm x n = x · logGammaTerm x n - ∫₀ˣ logGammaTerm t n dt`. -/
theorem barnesLogTerm_eq {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    barnesLogTerm x n = x * logGammaTerm x n - ∫ t in (0 : ℝ)..x, logGammaTerm t n := by
  have hm : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [integral_logGammaTerm hx, barnesLogTerm, logGammaTerm]
  field_simp
  ring

/-- Termwise integration of `∑ₙ logGammaTerm t n` over `[0, x]`. -/
theorem hasSum_integral_logGammaTerm {x : ℝ} (hx : 0 ≤ x) :
    HasSum (fun n => ∫ t in (0 : ℝ)..x, logGammaTerm t n)
      (∫ t in (0 : ℝ)..x, ∑' n, logGammaTerm t n) := by
  have hsub : Set.uIoc 0 x ⊆ Set.Ici 0 := by
    rw [Set.uIoc_of_le hx]; exact fun t ht => le_of_lt ht.1
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n _ => x ^ 2 / (2 * ((n : ℝ) + 1) ^ 2)) (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
  · exact ((continuousOn_logGammaTerm n).mono hsub).aestronglyMeasurable measurableSet_uIoc
  · refine Filter.Eventually.of_forall fun t ht => ?_
    rw [Set.uIoc_of_le hx] at ht
    have ht0 : 0 ≤ t := le_of_lt ht.1
    rw [Real.norm_of_nonneg (logGammaTerm_nonneg ht0 n)]
    refine (logGammaTerm_le ht0 n).trans ?_
    gcongr
    exact ht.2
  · refine Filter.Eventually.of_forall fun t _ => ?_
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    refine (this.mul_left (x ^ 2 / 2)).congr fun k => ?_
    push_cast; field_simp
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun t ht => ?_
    exact (summable_logGammaTerm (hsub ht)).hasSum

/-- `t ↦ log Γ(t + 1)` is continuous on `[0, ∞)`. -/
theorem continuousOn_log_Gamma_add_one :
    ContinuousOn (fun t : ℝ => Real.log (Real.Gamma (t + 1))) (Set.Ici 0) := by
  intro t ht
  have ht0 : (0 : ℝ) < t + 1 := by have : (0 : ℝ) ≤ t := ht; linarith
  have hG : ContinuousAt Real.Gamma (t + 1) := by
    refine (Real.differentiableAt_Gamma fun m h => ?_).continuousAt
    have : (0 : ℝ) ≤ m := m.cast_nonneg
    linarith
  have hc : ContinuousAt (fun s : ℝ => Real.Gamma (s + 1)) t :=
    ContinuousAt.comp (g := Real.Gamma) (f := fun s : ℝ => s + 1) hG (by fun_prop)
  exact (hc.log (Real.Gamma_pos_of_pos ht0).ne').continuousWithinAt

/-- `∑ₙ barnesLogTerm x n = x log Γ(x + 1) - ∫₀ˣ log Γ(t + 1) dt + γx²/2` for `x ≥ 0`. -/
theorem hasSum_barnesLogTerm {x : ℝ} (hx : 0 ≤ x) :
    HasSum (barnesLogTerm x)
      (x * Real.log (Real.Gamma (x + 1)) - (∫ t in (0 : ℝ)..x, Real.log (Real.Gamma (t + 1))) +
        Real.eulerMascheroniConstant * x ^ 2 / 2) := by
  set γ := Real.eulerMascheroniConstant
  have hsub : Set.uIcc 0 x ⊆ Set.Ici 0 := by
    rw [Set.uIcc_of_le hx]; exact Set.Icc_subset_Ici_self
  have hI : ∫ t in (0 : ℝ)..x, ∑' n, logGammaTerm t n =
      (∫ t in (0 : ℝ)..x, Real.log (Real.Gamma (t + 1))) + γ * (x ^ 2 / 2) := by
    rw [intervalIntegral.integral_congr (g := fun t => Real.log (Real.Gamma (t + 1)) + γ * t)
      fun t ht => (hasSum_logGammaTerm (hsub ht)).tsum_eq]
    rw [intervalIntegral.integral_add (f := fun t => Real.log (Real.Gamma (t + 1)))
      (g := fun t => γ * t) (continuousOn_log_Gamma_add_one.mono hsub).intervalIntegrable
      ((continuous_const.mul continuous_id : Continuous fun t : ℝ => γ * t).intervalIntegrable 0 x),
      intervalIntegral.integral_const_mul, integral_id]
    ring
  have h := ((hasSum_logGammaTerm hx).mul_left x).sub (hasSum_integral_logGammaTerm hx)
  rw [hI] at h
  convert h using 1
  · funext n; exact barnesLogTerm_eq hx n
  · ring

/-- At real `x ≥ 0` the Weierstrass factor is `exp(barnesLogTerm x k)`. -/
theorem barnesGTerm_ofReal {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    barnesGTerm x k = Complex.exp (barnesLogTerm x k) := by
  have hpos : (0 : ℝ) < 1 + x / (k + 1) := by positivity
  have hreal : (1 + x / (k + 1)) ^ (k + 1) * Real.exp (-x + x ^ 2 / (2 * (k + 1))) =
      Real.exp (barnesLogTerm x k) := by
    rw [barnesLogTerm, show ((k : ℝ) + 1) * Real.log (1 + x / (k + 1)) - x +
      x ^ 2 / (2 * (k + 1)) = ((k + 1 : ℕ) : ℝ) * Real.log (1 + x / (k + 1)) +
        (-x + x ^ 2 / (2 * (k + 1))) by push_cast; ring,
      Real.exp_add (((k + 1 : ℕ) : ℝ) * _), Real.exp_nat_mul, Real.exp_log hpos]
  rw [barnesGTerm_eq, ← Complex.ofReal_exp, ← hreal]
  push_cast
  rfl

/-- For real `x ≥ 0`, `G(x + 1) = exp((x/2) log 2π - x(x+1)/2 - γx²/2 + ∑ₙ barnesLogTerm x n)`. -/
theorem barnesGSucc_ofReal {x : ℝ} (hx : 0 ≤ x) :
    barnesGSucc x = Real.exp (x / 2 * Real.log (2 * π) - x * (x + 1) / 2 -
      Real.eulerMascheroniConstant * x ^ 2 / 2 + ∑' n, barnesLogTerm x n) := by
  have hb := (hasSum_barnesLogTerm hx).summable.hasSum
  have hc : HasSum (fun n => (barnesLogTerm x n : ℂ)) (∑' n, barnesLogTerm x n : ℝ) :=
    Complex.hasSum_ofReal.mpr hb
  have hprod : ∏' k : ℕ, barnesGTerm x k = Complex.exp (∑' n, barnesLogTerm x n : ℝ) := by
    rw [← hc.cexp.tprod_eq]
    congr 1
    funext k
    exact barnesGTerm_ofReal hx k
  have h2pi : (2 * π : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 2 * π := by positivity
    exact_mod_cast this.ne'
  have hlog : Complex.log (2 * π) = ((Real.log (2 * π) : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by positivity)]; push_cast; rfl
  unfold barnesGSucc
  rw [hprod, cpow_def_of_ne_zero h2pi, hlog, ← Complex.exp_add, ← Complex.exp_add,
    Complex.ofReal_exp]
  congr 1
  push_cast
  ring

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

/-- DLMF 5.17.4: `Ln G(x + 1) = (x/2) ln 2π - x(x+1)/2 + x ln Γ(x + 1) - ∫₀ˣ ln Γ(t + 1) dt` for `x
> 0`. -/
@[dlmf 5.17.E4]
theorem log_barnesGSucc {x : ℝ} (hx : 0 < x) :
    Complex.log (barnesGSucc x) =
      (1 / 2 : ℂ) * x * Complex.log (2 * π) - (1 / 2 : ℂ) * x * (x + 1) +
        x * Complex.log (Complex.Gamma (x + 1)) -
        ∫ t : ℝ in (0 : ℝ)..x, Complex.log (Complex.Gamma (t + 1)) := by
  have hsub : Set.uIcc 0 x ⊆ Set.Ici 0 := by
    rw [Set.uIcc_of_le hx.le]; exact Set.Icc_subset_Ici_self
  have hG : ∀ t : ℝ, 0 ≤ t →
      Complex.log (Complex.Gamma (t + 1)) = ((Real.log (Real.Gamma (t + 1)) : ℝ) : ℂ) := by
    intro t ht
    rw [show (t : ℂ) + 1 = ((t + 1 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal,
      Complex.ofReal_log (Real.Gamma_pos_of_pos (by linarith)).le]
  have hlog : Complex.log (2 * π) = ((Real.log (2 * π) : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by positivity)]; push_cast; rfl
  rw [barnesGSucc_ofReal hx.le, ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp,
    hG x hx.le, intervalIntegral.integral_congr
      (g := fun t : ℝ => ((Real.log (Real.Gamma (t + 1)) : ℝ) : ℂ)) fun t ht => hG t (hsub ht),
    intervalIntegral.integral_ofReal, hlog, (hasSum_barnesLogTerm hx.le).tsum_eq]
  push_cast
  ring

/-- Glaisher–Kinkelin constant, via the first closed form for `C` in 5.17.7. -/
@[dlmf 5.17.E6]
def glaisherKinkelin : ℝ :=
  Real.exp ((Real.eulerMascheroniConstant + Real.log (2 * π)) / 12 -
    (deriv riemannZeta 2).re / (2 * π ^ 2))

/-- DLMF 5.17.7: `ln A = 1/12 - ζ'(-1)` for the Glaisher–Kinkelin constant `A`. -/
@[dlmf 5.17.E7]
theorem glaisherKinkelin_eq_zeta_neg_one :
    Real.log glaisherKinkelin = 1 / 12 - (deriv riemannZeta (-1)).re := by
  set γ := Real.eulerMascheroniConstant
  set Z := deriv riemannZeta 2
  -- Differentiate the functional equation `ζ(1 - s) = 2 (2π)^{-s} Γ(s) cos(πs/2) ζ(s)` at `s = 2`.
  have h2pi : (2 * π : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 2 * π := by positivity
    exact_mod_cast this.ne'
  have hA : HasDerivAt (fun s : ℂ => (2 * π : ℂ) ^ (-s))
      ((2 * π : ℂ) ^ (-(2 : ℂ)) * Complex.log (2 * π) * (-1)) 2 :=
    (hasDerivAt_neg (2 : ℂ)).const_cpow (Or.inl h2pi)
  have hG : HasDerivAt Complex.Gamma (1 - γ) 2 := by
    have := Complex.hasDerivAt_Gamma_nat 1
    norm_num [harmonic] at this
    convert this using 1; ring
  have hC : HasDerivAt (fun s : ℂ => Complex.cos (π * s / 2))
      (-Complex.sin (π * 2 / 2) * (π / 2)) 2 := by
    have h : HasDerivAt (fun s : ℂ => π * s / 2) (π / 2) 2 := by
      simpa using ((hasDerivAt_id (2 : ℂ)).const_mul (π : ℂ)).div_const 2
    exact h.ccos
  have hZ : HasDerivAt riemannZeta Z 2 :=
    (differentiableAt_riemannZeta (by norm_num)).hasDerivAt
  have hR := ((((hA.const_mul 2).mul hG).mul hC).mul hZ)
  have hL : HasDerivAt (fun s => riemannZeta (1 - s)) (deriv riemannZeta (-1) * (-1)) 2 := by
    have h1 : HasDerivAt (fun s : ℂ => 1 - s) (-1) 2 := by
      simpa using (hasDerivAt_id (2 : ℂ)).const_sub 1
    have hz : HasDerivAt riemannZeta (deriv riemannZeta (-1)) (1 - 2) := by
      rw [show (1 : ℂ) - 2 = -1 by norm_num]
      exact (differentiableAt_riemannZeta (by norm_num)).hasDerivAt
    exact hz.comp 2 h1
  have heq : (fun s => riemannZeta (1 - s)) =ᶠ[𝓝 2]
      fun s => 2 * (2 * π : ℂ) ^ (-s) * Complex.Gamma s * Complex.cos (π * s / 2) *
        riemannZeta s := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with s hs
    refine riemannZeta_one_sub (fun n h => ?_) (fun h => ?_)
    · have := congrArg Complex.re h; simp at this hs; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    · rw [h] at hs; simp at hs
  have huniq := hL.unique (hR.congr_of_eventuallyEq heq)
  simp only [Pi.mul_apply] at huniq
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hpow : (2 * π : ℂ) ^ (-(2 : ℂ)) = 1 / (4 * (π : ℂ) ^ 2) := by
    rw [cpow_neg, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, cpow_natCast]; ring
  have hlog : Complex.log (2 * π) = ((Real.log (2 * π) : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by positivity)]; push_cast; rfl
  have hG2 : Complex.Gamma 2 = 1 := by
    rw [show (2 : ℂ) = ((1 : ℕ) : ℂ) + 1 by norm_num, Complex.Gamma_nat_eq_factorial]; simp
  rw [show (π : ℂ) * 2 / 2 = π by ring, Complex.cos_pi, Complex.sin_pi, riemannZeta_two,
    hpow, hlog, hG2] at huniq
  have h : deriv riemannZeta (-1) =
      (((1 / 12 - (γ + Real.log (2 * π)) / 12 : ℝ) : ℂ)) + Z / ((2 * π ^ 2 : ℝ) : ℂ) := by
    rw [show deriv riemannZeta (-1) = -(deriv riemannZeta (-1) * -1) by ring, huniq]
    push_cast
    field_simp
    ring
  rw [h, Complex.add_re, Complex.ofReal_re, Complex.div_ofReal_re, glaisherKinkelin,
    Real.log_exp]
  ring

end DLMF.Gamma
end
end
