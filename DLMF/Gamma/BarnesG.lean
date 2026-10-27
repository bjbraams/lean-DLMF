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
# Barnes G-function (DLMF §5.17)

The Weierstrass product 5.17.3 is taken as the definition of `G(z+1)`.
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

theorem barnesGTerm_eq (z : ℂ) (k : ℕ) :
    barnesGTerm z k = (1 + z / (k + 1)) ^ (k + 1) *
      Complex.exp (-z + z ^ 2 / (2 * (k + 1))) := by
  unfold barnesGTerm
  simp only
  congr 1
  rw [show ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) by push_cast; ring, cpow_natCast]

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

theorem multipliable_barnesGTerm (z : ℂ) : Multipliable (barnesGTerm z) := by
  have h := Complex.multipliable_one_add_of_summable
    (Summable.of_norm (summable_norm_barnesGTerm_sub_one z))
  simpa using h

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

theorem logGammaTerm_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : 0 ≤ logGammaTerm t n := by
  have := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + t / (n + 1))
  unfold logGammaTerm; linarith

theorem logGammaTerm_le {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    logGammaTerm t n ≤ t ^ 2 / (2 * ((n : ℝ) + 1) ^ 2) := by
  have := sub_sq_div_two_le_log_one_add (by positivity : 0 ≤ t / (n + 1))
  unfold logGammaTerm
  rw [div_pow] at this
  have : t ^ 2 / (2 * ((n : ℝ) + 1) ^ 2) = t ^ 2 / ((n : ℝ) + 1) ^ 2 / 2 := by
    rw [div_div, mul_comm]
  linarith

theorem summable_logGammaTerm {t : ℝ} (ht : 0 ≤ t) : Summable (logGammaTerm t) := by
  have hs : Summable fun n : ℕ => t ^ 2 / (2 * ((n : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    refine (this.mul_left (t ^ 2 / 2)).congr fun k => ?_
    push_cast; field_simp
  exact Summable.of_nonneg_of_le (logGammaTerm_nonneg ht) (logGammaTerm_le ht) hs

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

theorem continuousOn_logGammaTerm (n : ℕ) : ContinuousOn (fun t => logGammaTerm t n) (Set.Ici 0) := by
  intro t ht
  have h1 : (1 + t / (n + 1)) ≠ 0 := by
    have : (0 : ℝ) ≤ t := ht
    positivity
  unfold logGammaTerm
  exact (((continuous_id.div_const _).continuousAt).sub
    ((continuous_const.add (continuous_id.div_const _)).continuousAt.log h1)).continuousWithinAt

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

theorem barnesLogTerm_eq {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    barnesLogTerm x n = x * logGammaTerm x n - ∫ t in (0 : ℝ)..x, logGammaTerm t n := by
  have hm : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [integral_logGammaTerm hx, barnesLogTerm, logGammaTerm]
  field_simp
  ring

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

/-! ### Proof of 5.17.5

Write `D(t)` for the difference in 5.17.5. By 5.17.4, `D(t) = E(t) - ∫₀ᵗ log Γ(s+1) ds` with `E`
elementary. With `Ψ(t) = ∫₀¹ x log Γ(x+t) dx`, Binet's bound `0 ≤ μ(x) ≤ 1/(12x)` gives
`D(t) - V(t) = B(t) = O(1/t)`, where `V` has derivative `R(t) - ∫ₜ^{t+1} log Γ` with zero
derivative, so `V` is affine. At the integers `G(n+1) = ∏ k!` (5.17.2) turns `D(n)` into
`log A - h(n)` with `h(n) = ∑ k log k - (n²/2 + n/2 + 1/12) log n + n²/4`. The Euler–Maclaurin
continuation `ζ(s) = 1/(s-1) + 1/2 + s/12 + ∑ eₙ(s)` (valid for `re s > -2`, by the identity
theorem), differentiated termwise at `s = -1`, gives `h(n) → 1/12 - ζ'(-1) = log A` (5.17.7).
Hence `V(n) → 0`, so `V = 0` and `D = B`.
-/

namespace BarnesAsymp

/-- The local Euler–Maclaurin error on `[n, n+1]` for `x ↦ x^{-s}`, with the `B₂` correction. -/
def zetaTerm (s : ℂ) (n : ℕ) : ℂ :=
  ((n : ℂ) ^ (-s) + ((n : ℂ) + 1) ^ (-s)) / 2 -
    (((n : ℂ) + 1) ^ (1 - s) - (n : ℂ) ^ (1 - s)) / (1 - s) +
    s / 12 * (((n : ℂ) + 1) ^ (-s - 1) - (n : ℂ) ^ (-s - 1))

theorem hasDerivAt_pw {N : ℝ} (a : ℂ) {v : ℝ} (hv : 0 < N + v) :
    HasDerivAt (fun v : ℝ => ((N + v : ℝ) : ℂ) ^ a) (a * ((N + v : ℝ) : ℂ) ^ (a - 1)) v := by
  have h1 : HasDerivAt (fun v : ℝ => ((N + v : ℝ) : ℂ)) 1 v := by
    simpa using ((hasDerivAt_id v).const_add N).ofReal_comp
  have h2 := (Complex.hasStrictDerivAt_cpow_const (c := a)
    (Complex.ofReal_mem_slitPlane.2 hv)).hasDerivAt
  have h3 := h2.comp v h1
  simp only [Function.comp_def, mul_one] at h3
  exact h3

lemma mvt01 {f f' : ℝ → ℂ} {C : ℝ} (hf : ∀ v ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' v) v)
    (hC : ∀ v ∈ Set.Icc (0 : ℝ) 1, ‖f' v‖ ≤ C) (hC0 : 0 ≤ C) :
    ∀ v ∈ Set.Icc (0 : ℝ) 1, ‖f v - f 0‖ ≤ C := by
  intro v hv
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := f) (a := 0) (b := 1)
    (fun x hx => (hf x hx).hasDerivWithinAt) (fun x hx => hC x (Set.Ico_subset_Icc_self hx)) v hv
  calc ‖f v - f 0‖ ≤ C * (v - 0) := this
    _ ≤ C * 1 := by gcongr; linarith [hv.2]
    _ = C := mul_one C

theorem norm_zetaTerm_le {s : ℂ} (hs : s ≠ 1) (hre : -3 ≤ s.re) {n : ℕ} (hn : 1 ≤ n) :
    ‖zetaTerm s n‖ ≤ ‖s * (s + 1) * (s + 2)‖ * (n : ℝ) ^ (-s.re - 3) := by
  set N : ℝ := (n : ℝ) with hNdef
  have hN : 0 < N := by rw [hNdef]; exact_mod_cast hn
  have hs1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  set pw : ℂ → ℝ → ℂ := fun a v => ((N + v : ℝ) : ℂ) ^ a with hpw_def
  have hpw : ∀ a : ℂ, ∀ v ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (pw a) (a * pw (a - 1) v) v :=
    fun a v hv => hasDerivAt_pw a (by linarith [hv.1])
  set M : ℝ := ‖s * (s + 1) * (s + 2)‖ * N ^ (-s.re - 3) with hM
  have hM0 : 0 ≤ M := by positivity
  let g0 : ℝ → ℂ := fun v => pw (-s) v
  let g1 : ℝ → ℂ := fun v => -s * pw (-s - 1) v
  let g2 : ℝ → ℂ := fun v => s * (s + 1) * pw (-s - 2) v
  let g3 : ℝ → ℂ := fun v => -(s * (s + 1) * (s + 2)) * pw (-s - 3) v
  have hg0 : ∀ v ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g0 (g1 v) v := fun v hv => hpw (-s) v hv
  have hg1 : ∀ v ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g1 (g2 v) v := by
    intro v hv
    refine ((hpw (-s - 1) v hv).const_mul (-s)).congr_deriv ?_
    simp only [g2, show -s - 1 - 1 = -s - 2 by ring]
    ring
  have hg2 : ∀ v ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g2 (g3 v) v := by
    intro v hv
    refine ((hpw (-s - 2) v hv).const_mul (s * (s + 1))).congr_deriv ?_
    simp only [g3, show -s - 2 - 1 = -s - 3 by ring]
    ring
  have hg3 : ∀ v ∈ Set.Icc (0 : ℝ) 1, ‖g3 v‖ ≤ M := by
    intro v hv
    have hNv : 0 < N + v := by linarith [hv.1]
    show ‖-(s * (s + 1) * (s + 2)) * ((N + v : ℝ) : ℂ) ^ (-s - 3)‖ ≤ M
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hNv, hM,
      show (-s - 3).re = -s.re - 3 by simp]
    gcongr ?_ * ?_
    exact Real.rpow_le_rpow_of_nonpos hN (by linarith [hv.1]) (by linarith)
  -- step (a)
  have ha : ∀ w ∈ Set.Icc (0 : ℝ) 1, ‖g2 w - g2 0‖ ≤ M := mvt01 hg2 hg3 hM0
  -- step (b)
  have hb : ∀ v ∈ Set.Icc (0 : ℝ) 1, ‖g1 v - (v : ℂ) * g2 v - g1 0‖ ≤ 2 * M := by
    intro v hv
    let h : ℝ → ℂ := fun w => g1 w - (w : ℂ) * g2 v
    have hh : ∀ w ∈ Set.Icc (0 : ℝ) 1, HasDerivAt h (g2 w - g2 v) w := by
      intro w hw
      have := (hg1 w hw).sub ((hasDerivAt_id w).ofReal_comp.mul_const (g2 v))
      exact this.congr_deriv (by push_cast; ring)
    have hbd : ∀ w ∈ Set.Icc (0 : ℝ) 1, ‖g2 w - g2 v‖ ≤ 2 * M := by
      intro w hw
      calc ‖g2 w - g2 v‖ = ‖(g2 w - g2 0) - (g2 v - g2 0)‖ := by ring_nf
        _ ≤ ‖g2 w - g2 0‖ + ‖g2 v - g2 0‖ := norm_sub_le _ _
        _ ≤ M + M := add_le_add (ha w hw) (ha v hv)
        _ = 2 * M := by ring
    have := mvt01 hh hbd (by positivity) v hv
    simpa [h] using this
  -- the error function
  let E : ℝ → ℂ := fun v => (v : ℂ) / 2 * (g0 0 + g0 v) - (pw (1 - s) v - pw (1 - s) 0) / (1 - s)
    - (v : ℂ) ^ 2 / 12 * (g1 v - g1 0)
  let E' : ℝ → ℂ := fun v => (g0 0 - g0 v) / 2 + (v : ℂ) / 3 * g1 v + (v : ℂ) / 6 * g1 0
    - (v : ℂ) ^ 2 / 12 * g2 v
  let E'' : ℝ → ℂ := fun v => -(g1 v - (v : ℂ) * g2 v - g1 0) / 6 - (v : ℂ) ^ 2 / 12 * g3 v
  have hE : ∀ v ∈ Set.Icc (0 : ℝ) 1, HasDerivAt E (E' v) v := by
    intro v hv
    have hx : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 v := (hasDerivAt_id v).ofReal_comp
    have h1 := (hx.div_const 2).mul ((hg0 v hv).const_add (g0 0))
    have h2 := ((hpw (1 - s) v hv).sub_const (pw (1 - s) 0)).div_const (1 - s)
    have h3 := ((hx.pow 2).div_const 12).mul ((hg1 v hv).sub_const (g1 0))
    refine ((h1.sub h2).sub h3).congr_deriv ?_
    simp only [E', g0, Pi.pow_apply, show (1 : ℂ) - s - 1 = -s by ring]
    field_simp
    ring
  have hE' : ∀ v ∈ Set.Icc (0 : ℝ) 1, HasDerivAt E' (E'' v) v := by
    intro v hv
    have hx : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 v := (hasDerivAt_id v).ofReal_comp
    have h1 := ((hg0 v hv).const_sub (g0 0)).div_const 2
    have h2 := (hx.div_const 3).mul (hg1 v hv)
    have h3 := (hx.div_const 6).mul_const (g1 0)
    have h4 := ((hx.pow 2).div_const 12).mul (hg2 v hv)
    refine (((h1.add h2).add h3).sub h4).congr_deriv ?_
    simp only [E'', Pi.pow_apply]
    ring
  have hE'' : ∀ v ∈ Set.Icc (0 : ℝ) 1, ‖E'' v‖ ≤ M := by
    intro v hv
    have hv2 : ‖(v : ℂ) ^ 2 / 12‖ ≤ 1 / 12 := by
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv.1]
      norm_num
      nlinarith [hv.1, hv.2]
    calc ‖E'' v‖ ≤ ‖g1 v - (v : ℂ) * g2 v - g1 0‖ / 6 + ‖(v : ℂ) ^ 2 / 12‖ * ‖g3 v‖ := by
          simp only [E'']
          refine (norm_sub_le _ _).trans ?_
          rw [norm_div, norm_neg, norm_mul]
          norm_num
      _ ≤ 2 * M / 6 + 1 / 12 * M := by
          gcongr
          · exact hb v hv
          · exact hg3 v hv
      _ ≤ M := by linarith
  have hE'0 : E' 0 = 0 := by simp [E']
  have hE'b : ∀ v ∈ Set.Icc (0 : ℝ) 1, ‖E' v‖ ≤ M := by
    intro v hv
    simpa [hE'0] using mvt01 hE' hE'' hM0 v hv
  have hE0 : E 0 = 0 := by simp [E]
  have hE1 := mvt01 hE hE'b hM0 1 ⟨zero_le_one, le_rfl⟩
  rw [hE0, sub_zero] at hE1
  have hEq : E 1 = zetaTerm s n := by
    simp only [E, g0, g1, pw, zetaTerm, hNdef]
    push_cast
    simp only [add_zero]
    field_simp
    ring
  rw [← hEq]
  exact hE1

theorem sum_zetaTerm (s : ℂ) (N : ℕ) :
    ∑ i ∈ Finset.range N, zetaTerm s (i + 1) =
      ∑ k ∈ Finset.range (N + 1), ((k : ℂ) + 1) ^ (-s) - (1 + ((N : ℂ) + 1) ^ (-s)) / 2 -
        (((N : ℂ) + 1) ^ (1 - s) - 1) / (1 - s) + s / 12 * (((N : ℂ) + 1) ^ (-s - 1) - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (n := N + 1)]
    simp only [zetaTerm]
    push_cast
    ring

theorem summable_rpow_succ {p : ℝ} (hp : p < -1) :
    Summable (fun i : ℕ => ((i : ℝ) + 1) ^ p) := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hp)
  refine this.congr fun i => ?_
  push_cast
  rfl

/-- A locally uniform bound for the terms near `s₀` with `-2 < re s₀`. -/
theorem norm_zetaTerm_le_near {s₀ s : ℂ} (h₀ : -2 < s₀.re)
    (hs : s ∈ Metric.ball s₀ ((s₀.re + 2) / 2)) (hs1 : s ≠ 1) (i : ℕ) :
    ‖zetaTerm s (i + 1)‖ ≤
      (‖s₀‖ + (s₀.re + 2) / 2 + 2) ^ 3 * ((i : ℝ) + 1) ^ (-1 - (s₀.re + 2) / 2) := by
  set δ := (s₀.re + 2) / 2 with hδ
  have hd : ‖s - s₀‖ < δ := by simpa [dist_eq_norm] using hs
  have hre : s₀.re - δ < s.re := by
    have := Complex.abs_re_le_norm (s - s₀)
    rw [Complex.sub_re] at this
    have := (abs_lt.mp (lt_of_le_of_lt this hd)).1
    linarith
  have hsn : ‖s‖ ≤ ‖s₀‖ + δ := by
    have := norm_sub_norm_le s s₀
    linarith
  have hb := norm_zetaTerm_le hs1 (by linarith) (n := i + 1) (by omega)
  refine hb.trans ?_
  push_cast
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have h1 : ‖s + 1‖ ≤ ‖s₀‖ + δ + 2 := by
    have := norm_add_le s 1
    rw [norm_one] at this
    linarith
  have h2 : ‖s + 2‖ ≤ ‖s₀‖ + δ + 2 := by
    have := norm_add_le s 2
    rw [show ‖(2 : ℂ)‖ = 2 by simp] at this
    linarith
  have h0 : ‖s‖ ≤ ‖s₀‖ + δ + 2 := by linarith
  have hA : ‖s * (s + 1) * (s + 2)‖ ≤ (‖s₀‖ + δ + 2) ^ 3 := by
    rw [norm_mul, norm_mul, pow_three]
    calc ‖s‖ * ‖s + 1‖ * ‖s + 2‖ ≤ (‖s₀‖ + δ + 2) * (‖s₀‖ + δ + 2) * (‖s₀‖ + δ + 2) := by
          gcongr
      _ = _ := by ring
  have hB : ((i : ℝ) + 1) ^ (-s.re - 3) ≤ ((i : ℝ) + 1) ^ (-1 - δ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [(i.cast_nonneg : (0 : ℝ) ≤ i)])
      (by linarith)
  exact mul_le_mul hA hB (by positivity) (by positivity)

theorem differentiableAt_zetaTerm {s : ℂ} (hs : s ≠ 1) (n : ℕ) (hn : 1 ≤ n) :
    DifferentiableAt ℂ (fun s => zetaTerm s n) s := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
  have hs1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have e1 : ∀ c : ℂ, c ≠ 0 → ∀ b : ℂ,
      DifferentiableAt ℂ (fun s : ℂ => c ^ (b - s)) s := fun c hc b =>
    ((differentiableAt_const b).sub differentiableAt_id).const_cpow (Or.inl hc)
  have e2 : ∀ c : ℂ, c ≠ 0 → DifferentiableAt ℂ (fun s : ℂ => c ^ (-s)) s := fun c hc =>
    differentiableAt_id.neg.const_cpow (Or.inl hc)
  have e3 : ∀ c : ℂ, c ≠ 0 → DifferentiableAt ℂ (fun s : ℂ => c ^ (-s - 1)) s := fun c hc =>
    (differentiableAt_id.neg.sub_const 1).const_cpow (Or.inl hc)
  unfold zetaTerm
  exact ((((e2 _ hn0).add (e2 _ hn1)).div_const 2).sub
    (((e1 _ hn1 1).sub (e1 _ hn0 1)).div ((differentiableAt_const 1).sub differentiableAt_id)
      hs1)).add ((differentiableAt_id.div_const 12).mul ((e3 _ hn1).sub (e3 _ hn0)))

/-- The domain: the half-plane `re s > -2` slit along `[1, ∞)`. -/
def zetaDom : Set ℂ := {s | -2 < s.re} \ {s | s.im = 0 ∧ 1 ≤ s.re}

theorem isOpen_zetaDom : IsOpen zetaDom :=
  (isOpen_lt continuous_const Complex.continuous_re).sdiff
    ((isClosed_eq Complex.continuous_im continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_re))

theorem ne_one_of_mem_zetaDom {s : ℂ} (hs : s ∈ zetaDom) : s ≠ 1 := by
  rintro rfl
  exact hs.2 ⟨by simp, by simp⟩

theorem isPreconnected_zetaDom : IsPreconnected zetaDom := by
  have h0 : (0 : ℂ) ∈ zetaDom := ⟨by simp, fun h => by norm_num at h⟩
  have hstar : StarConvex ℝ 0 zetaDom := by
    intro y hy a b ha hb hab
    simp only [smul_zero, zero_add]
    obtain ⟨hy1, hy2⟩ := hy
    simp only [Set.mem_ofPred_eq] at hy1 hy2
    refine ⟨?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      rcases le_or_gt 0 y.re with h | h
      · nlinarith
      · nlinarith
    · rintro ⟨h1, h2⟩
      simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, Complex.mul_im, add_zero] at h1 h2
      have hb0 : 0 < b := by
        rcases eq_or_lt_of_le hb with h | h
        · rw [← h] at h2; simp at h2; linarith
        · exact h
      have him : y.im = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · linarith
        · exact h
      have hre : 0 < y.re := by
        by_contra hc
        push Not at hc
        nlinarith
      exact hy2 ⟨him, by nlinarith⟩
  exact (hstar.isPathConnected h0).isConnected.isPreconnected

/-- The continued series. -/
def zetaSeries (s : ℂ) : ℂ := ∑' i : ℕ, zetaTerm s (i + 1)

/-- The Euler–Maclaurin continuation of `ζ` to `re s > -2`. -/
def zetaEM (s : ℂ) : ℂ := 1 / (s - 1) + 1 / 2 + s / 12 + zetaSeries s

theorem differentiableAt_zetaSeries {s₀ : ℂ} (h : s₀ ∈ zetaDom) :
    DifferentiableAt ℂ zetaSeries s₀ := by
  have h₀ : -2 < s₀.re := h.1
  set W := zetaDom ∩ Metric.ball s₀ ((s₀.re + 2) / 2) with hW
  have hWo : IsOpen W := isOpen_zetaDom.inter Metric.isOpen_ball
  have hs₀W : s₀ ∈ W := ⟨h, Metric.mem_ball_self (by linarith)⟩
  have hd : DifferentiableOn ℂ (fun w : ℂ => ∑' i : ℕ, zetaTerm w (i + 1)) W := by
    refine differentiableOn_tsum_of_summable_norm
      ((summable_rpow_succ (p := -1 - (s₀.re + 2) / 2) (by linarith)).mul_left
        ((‖s₀‖ + (s₀.re + 2) / 2 + 2) ^ 3)) (fun i w hw => ?_) hWo (fun i w hw => ?_)
    · exact (differentiableAt_zetaTerm (ne_one_of_mem_zetaDom hw.1) (i + 1)
        (by omega)).differentiableWithinAt
    · exact norm_zetaTerm_le_near h₀ hw.2 (ne_one_of_mem_zetaDom hw.1) i
  exact hd.differentiableAt (hWo.mem_nhds hs₀W)

theorem differentiableAt_zetaEM {s : ℂ} (h : s ∈ zetaDom) : DifferentiableAt ℂ zetaEM s := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (ne_one_of_mem_zetaDom h)
  have hA : DifferentiableAt ℂ (fun s : ℂ => 1 / (s - 1)) s :=
    (differentiableAt_const (1 : ℂ)).div (differentiableAt_id.sub_const 1) hs1
  have hB : DifferentiableAt ℂ (fun s : ℂ => s / 12) s := differentiableAt_id.div_const 12
  exact ((hA.add_const (1 / 2 : ℂ)).add hB).add (differentiableAt_zetaSeries h)

theorem tendsto_cpow_neg {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun N : ℕ => ((N : ℂ) + 1) ^ (-w)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h : ∀ N : ℕ, ‖((N : ℂ) + 1) ^ (-w)‖ = ((N : ℝ) + 1) ^ (-w.re) := by
    intro N
    have : ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re]
  simp only [h]
  exact (tendsto_rpow_neg_atTop hw).comp
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)

theorem zeta_eq_zetaEM {s : ℂ} (hs : 1 < s.re) : riemannZeta s = zetaEM s := by
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs
  have hs1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hsum : Summable (fun i : ℕ => zetaTerm s (i + 1)) := by
    refine Summable.of_norm_bounded
      ((summable_rpow_succ (p := -s.re - 3) (by linarith)).mul_left ‖s * (s + 1) * (s + 2)‖)
      (fun i => ?_)
    have := norm_zetaTerm_le hs1 (by linarith) (n := i + 1) (by omega)
    simpa using this
  have hA := hsum.hasSum.tendsto_sum_nat
  -- the partial sums of `ζ`
  have hz : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (N + 1), ((k : ℂ) + 1) ^ (-s)) atTop
      (𝓝 (riemannZeta s)) := by
    have hsz : Summable (fun k : ℕ => 1 / ((k : ℂ) + 1) ^ s) := by
      have := (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs)
      refine this.congr fun k => ?_
      push_cast
      rfl
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    have := (hsz.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    refine this.congr fun N => ?_
    simp only [Function.comp_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.cpow_neg, one_div]
  have hB : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, zetaTerm s (i + 1)) atTop
      (𝓝 (riemannZeta s - (1 + 0) / 2 - (0 - 1) / (1 - s) + s / 12 * (0 - 1))) := by
    simp only [sum_zetaTerm]
    refine (((hz.sub ((tendsto_const_nhds.add (tendsto_cpow_neg (w := s) (by linarith))).div_const
      2)).sub (((?_ : Tendsto (fun N : ℕ => ((N : ℂ) + 1) ^ (1 - s)) atTop (𝓝 0)).sub_const
        1).div_const _)).add
      (((?_ : Tendsto (fun N : ℕ => ((N : ℂ) + 1) ^ (-s - 1)) atTop (𝓝 0)).sub_const
        1).const_mul _))
    · have := tendsto_cpow_neg (w := s - 1) (by simp; linarith)
      simpa using this
    · have := tendsto_cpow_neg (w := s + 1) (by simp; linarith)
      refine this.congr fun N => ?_
      congr 1
      ring
  have heq := tendsto_nhds_unique hA hB
  unfold zetaEM zetaSeries
  rw [heq]
  have hs2 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp
  ring

theorem eqOn_zeta_zetaEM : Set.EqOn riemannZeta zetaEM zetaDom := by
  have hζ : AnalyticOnNhd ℂ riemannZeta zetaDom :=
    DifferentiableOn.analyticOnNhd (fun s hs =>
      (differentiableAt_riemannZeta (ne_one_of_mem_zetaDom hs)).differentiableWithinAt)
      isOpen_zetaDom
  have hZ : AnalyticOnNhd ℂ zetaEM zetaDom :=
    DifferentiableOn.analyticOnNhd (fun s hs => (differentiableAt_zetaEM hs).differentiableWithinAt)
      isOpen_zetaDom
  have hz₀ : (2 + I : ℂ) ∈ zetaDom := ⟨by norm_num, fun h => by norm_num at h⟩
  refine hζ.eqOn_of_preconnected_of_eventuallyEq hZ isPreconnected_zetaDom hz₀ ?_
  have : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 + I : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [this] with s hs using zeta_eq_zetaEM hs

/-- The derivative at `s = -1` of the `n`-th term. -/
def dz (n : ℕ) : ℝ :=
  -((n : ℝ) * Real.log n + ((n : ℝ) + 1) * Real.log ((n : ℝ) + 1)) / 2 +
    (((n : ℝ) + 1) ^ 2 * Real.log ((n : ℝ) + 1) - (n : ℝ) ^ 2 * Real.log n) / 2 -
    (2 * (n : ℝ) + 1) / 4 + (Real.log ((n : ℝ) + 1) - Real.log n) / 12

theorem hasDerivAt_zetaTerm (n : ℕ) (hn : 1 ≤ n) :
    HasDerivAt (fun s => zetaTerm s n) (dz n : ℂ) (-1) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
  have hlog0 : Complex.log (n : ℂ) = (Real.log n : ℂ) := Complex.natCast_log.symm
  have hlog1 : Complex.log ((n : ℂ) + 1) = (Real.log ((n : ℝ) + 1) : ℂ) := by
    rw [Complex.ofReal_log (by positivity)]
    push_cast
    rfl
  have hid : HasDerivAt (fun s : ℂ => s) 1 (-1) := hasDerivAt_id _
  have p1 := fun (c : ℂ) (hc : c ≠ 0) => hid.neg.const_cpow (c := c) (Or.inl hc)
  have p2 := fun (c : ℂ) (hc : c ≠ 0) => (hid.const_sub 1).const_cpow (c := c) (Or.inl hc)
  have p3 := fun (c : ℂ) (hc : c ≠ 0) => (hid.neg.sub_const 1).const_cpow (c := c) (Or.inl hc)
  have hden : HasDerivAt (fun s : ℂ => 1 - s) (-1) (-1) := by simpa using hid.const_sub 1
  have hT := ((((p1 _ hn0).add (p1 _ hn1)).div_const 2).sub
    (((p2 _ hn1).sub (p2 _ hn0)).div hden (by norm_num))).add
    ((hid.div_const 12).mul ((p3 _ hn1).sub (p3 _ hn0)))
  unfold zetaTerm
  refine hT.congr_deriv ?_
  simp only [Pi.neg_apply, Pi.sub_apply, neg_neg, cpow_one, sub_self, cpow_zero,
    show (1 : ℂ) - -1 = 2 by norm_num, hlog0, hlog1, dz, cpow_ofNat]
  push_cast
  ring

/-- The normalized hyperfactorial sequence. -/
def hseq (N : ℕ) : ℝ := ∑ k ∈ Finset.range (N + 1), (k : ℝ) * Real.log k -
    ((N : ℝ) ^ 2 / 2 + N / 2 + 1 / 12) * Real.log N + (N : ℝ) ^ 2 / 4

theorem sum_dz (M : ℕ) : ∑ i ∈ Finset.range M, dz (i + 1) = 1 / 4 - hseq (M + 1) := by
  induction M with
  | zero => simp [hseq, Finset.sum_range_succ]
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [hseq, dz]
    rw [Finset.sum_range_succ _ (M + 1 + 1)]
    push_cast
    ring

/-- Glaisher's limit, with the constant identified through `ζ'(-1)`. -/
theorem tendsto_hseq : Tendsto hseq atTop (𝓝 (Real.log glaisherKinkelin)) := by
  have hm1 : (-1 : ℂ) ∈ zetaDom := ⟨by norm_num, fun h => by norm_num at h⟩
  have hEv : riemannZeta =ᶠ[𝓝 (-1)] zetaEM := by
    filter_upwards [isOpen_zetaDom.mem_nhds hm1] with s hs using eqOn_zeta_zetaEM hs
  set S := deriv zetaSeries (-1) with hSdef
  have hne : ∀ w ∈ Metric.ball (-1 : ℂ) (((-1 : ℂ).re + 2) / 2), w ≠ 1 := by
    intro w hw h
    rw [h] at hw
    simp [dist_eq_norm] at hw
    norm_num at hw
  have hS0 : HasSum (fun i : ℕ => deriv (fun w => zetaTerm w (i + 1)) (-1)) S :=
    hasSum_deriv_of_summable_norm
      ((summable_rpow_succ (p := -1 - ((-1 : ℂ).re + 2) / 2) (by norm_num)).mul_left
        ((‖(-1 : ℂ)‖ + ((-1 : ℂ).re + 2) / 2 + 2) ^ 3))
      (fun i w hw => (differentiableAt_zetaTerm (hne w hw) (i + 1)
        (by omega)).differentiableWithinAt)
      Metric.isOpen_ball
      (fun i w hw => norm_zetaTerm_le_near (by norm_num) hw (hne w hw) i)
      (Metric.mem_ball_self (by norm_num))
  have hS1 : HasSum (fun i : ℕ => (dz (i + 1) : ℂ)) S := by
    refine hS0.congr_fun fun i => ?_
    exact ((hasDerivAt_zetaTerm (i + 1) (by omega)).deriv).symm
  have hS2 : HasSum (fun i : ℕ => dz (i + 1)) S.re := by
    simpa using Complex.hasSum_re hS1
  -- the derivative of `ζ` at `-1`
  have hZ : HasDerivAt zetaEM (-1 / 4 + 1 / 12 + S) (-1) := by
    have h1 : HasDerivAt (fun s : ℂ => 1 / (s - 1)) (-1 / 4) (-1) := by
      have := (hasDerivAt_const (-1 : ℂ) (1 : ℂ)).div ((hasDerivAt_id (-1 : ℂ)).sub_const 1)
        (by norm_num)
      refine this.congr_deriv ?_
      norm_num
    have h2 : HasDerivAt (fun s : ℂ => s / 12) (1 / 12) (-1) := (hasDerivAt_id _).div_const 12
    have h3 : HasDerivAt zetaSeries S (-1) := (differentiableAt_zetaSeries hm1).hasDerivAt
    exact ((h1.add_const (1 / 2 : ℂ)).add h2).add h3
  have hd : deriv riemannZeta (-1) = -1 / 4 + 1 / 12 + S := by
    rw [hEv.deriv_eq]
    exact hZ.deriv
  have hlim : Tendsto (fun M : ℕ => hseq (M + 1)) atTop (𝓝 (1 / 4 - S.re)) := by
    have := hS2.tendsto_sum_nat
    refine (tendsto_const_nhds.sub this).congr fun M => ?_
    rw [sum_dz]
    ring
  rw [← tendsto_add_atTop_iff_nat 1]
  convert hlim using 2
  rw [glaisherKinkelin_eq_zeta_neg_one, hd]
  simp
  ring

/-! ### The real form of 5.17.4 and the integer values -/

theorem log_barnesGSucc_re {x : ℝ} (hx : 0 < x) :
    Real.log (barnesGSucc x).re =
      x / 2 * Real.log (2 * π) - x * (x + 1) / 2 + x * Real.log (Real.Gamma (x + 1)) -
        ∫ t in (0 : ℝ)..x, Real.log (Real.Gamma (t + 1)) := by
  have hsub : Set.uIcc 0 x ⊆ Set.Ici 0 := by
    rw [Set.uIcc_of_le hx.le]; exact Set.Icc_subset_Ici_self
  have hG : ∀ t : ℝ, 0 ≤ t →
      Complex.log (Complex.Gamma (t + 1)) = ((Real.log (Real.Gamma (t + 1)) : ℝ) : ℂ) := by
    intro t ht
    rw [show (t : ℂ) + 1 = ((t + 1 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal,
      Complex.ofReal_log (Real.Gamma_pos_of_pos (by linarith)).le]
  have hlog : Complex.log (2 * π) = ((Real.log (2 * π) : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by positivity)]; push_cast; rfl
  have h := log_barnesGSucc hx
  set r : ℝ := x / 2 * Real.log (2 * π) - x * (x + 1) / 2 -
    Real.eulerMascheroniConstant * x ^ 2 / 2 + ∑' n, barnesLogTerm x n with hr
  have hb : barnesGSucc x = ((Real.exp r : ℝ) : ℂ) := barnesGSucc_ofReal hx.le
  rw [hb, ← Complex.ofReal_log (Real.exp_pos _).le, hG x hx.le, intervalIntegral.integral_congr
      (g := fun t : ℝ => ((Real.log (Real.Gamma (t + 1)) : ℝ) : ℂ)) fun t ht => hG t (hsub ht),
    intervalIntegral.integral_ofReal, hlog] at h
  rw [hb, Complex.ofReal_re]
  apply Complex.ofReal_injective
  rw [h]
  push_cast
  ring

theorem sum_log_factorial (n : ℕ) :
    ∑ k ∈ Finset.range n, Real.log (k.factorial : ℝ) =
      n * Real.log (n.factorial : ℝ) - ∑ k ∈ Finset.range (n + 1), (k : ℝ) * Real.log k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ _ (n + 1), Nat.factorial_succ]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity)]
    ring

/-- The statement's function at a positive integer. -/
theorem barnes_nat_eq (n : ℕ) (hn : 1 ≤ n) :
    Real.log (barnesGSucc ((n : ℝ) : ℂ)).re -
        ((1 / 4) * (n : ℝ) ^ 2 + n * Real.log (Real.Gamma (n + 1)) -
          ((1 / 2) * n * (n + 1) + 1 / 12) * Real.log n - Real.log glaisherKinkelin) =
      Real.log glaisherKinkelin - hseq n := by
  have hG : barnesGSucc ((n : ℝ) : ℂ) = ∏ k ∈ Finset.Icc 1 (n - 1), (k.factorial : ℂ) := by
    have := barnesG_nat (n + 1) (by omega)
    rw [show n + 1 - 2 = n - 1 by omega] at this
    rw [← this, barnesG]
    push_cast
    ring_nf
  have hprod : (∏ k ∈ Finset.Icc 1 (n - 1), (k.factorial : ℂ)).re =
      ∏ k ∈ Finset.Icc 1 (n - 1), (k.factorial : ℝ) := by
    have : (∏ k ∈ Finset.Icc 1 (n - 1), (k.factorial : ℂ)) =
        ((∏ k ∈ Finset.Icc 1 (n - 1), (k.factorial : ℝ) : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.ofReal_re]
  have hsum : Real.log (∏ k ∈ Finset.Icc 1 (n - 1), (k.factorial : ℝ)) =
      ∑ k ∈ Finset.range n, Real.log (k.factorial : ℝ) := by
    rw [Real.log_prod (fun k _ => by positivity)]
    have : Finset.range n = insert 0 (Finset.Icc 1 (n - 1)) := by
      ext k; simp; omega
    rw [this, Finset.sum_insert (by simp)]
    simp
  rw [hG, hprod, hsum, sum_log_factorial, Real.Gamma_nat_eq_factorial, hseq]
  ring

/-! ### The averaged Binet remainder -/

theorem continuousOn_logGamma : ContinuousOn (fun t => Real.log (Real.Gamma t)) (Set.Ioi 0) := by
  intro t ht
  have ht' : (0 : ℝ) < t := ht
  have hc : ContinuousAt Real.Gamma t :=
    (Real.differentiableAt_Gamma fun m h => by
      have : (0 : ℝ) ≤ m := m.cast_nonneg
      linarith).continuousAt
  exact (hc.log (Real.Gamma_pos_of_pos ht').ne').continuousWithinAt

/-- `Ψ(t) = ∫₀¹ x log Γ(x+t) dx`. -/
def barnesPsi (t : ℝ) : ℝ := ∫ x in (0 : ℝ)..1, x * Real.log (Real.Gamma (x + t))

/-- The comparison function `B(t)`. -/
def barnesB (t : ℝ) : ℝ :=
  (t / 2 + 1 / 12) * Real.log t - t / 2 + Real.log (2 * π) / 4 - barnesPsi t

theorem log_one_add_bounds {x t : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (ht : 1 ≤ t) :
    |(x + t - 1 / 2) * (Real.log (x + t) - Real.log t) - x| ≤ 1 / t := by
  have ht0 : 0 < t := by linarith
  have hu : 0 ≤ x / t := div_nonneg hx0 ht0.le
  have hL : Real.log (x + t) - Real.log t = Real.log (1 + x / t) := by
    rw [← Real.log_div (by linarith) ht0.ne']
    congr 1
    field_simp
    ring
  rw [hL]
  set L := Real.log (1 + x / t)
  have hL1 : L ≤ x / t := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + x / t by positivity)
    linarith
  have hL2 : x / t - (x / t) ^ 2 / 2 ≤ L := sub_sq_div_two_le_log_one_add hu
  have hc : 0 ≤ x + t - 1 / 2 := by linarith
  have hup : (x + t - 1 / 2) * L ≤ (x + t - 1 / 2) * (x / t) := mul_le_mul_of_nonneg_left hL1 hc
  have hlo : (x + t - 1 / 2) * (x / t - (x / t) ^ 2 / 2) ≤ (x + t - 1 / 2) * L :=
    mul_le_mul_of_nonneg_left hL2 hc
  have e1 : (x + t - 1 / 2) * (x / t) - x = (x ^ 2 - x / 2) / t := by
    field_simp
    ring
  have e2 : (x + t - 1 / 2) * (x / t - (x / t) ^ 2 / 2) - x =
      (x ^ 2 - x / 2) / t - (x + t - 1 / 2) * x ^ 2 / (2 * t ^ 2) := by
    field_simp
    ring
  have b1 : (x ^ 2 - x / 2) / t ≤ 1 / t := by
    apply div_le_div_of_nonneg_right _ ht0.le
    nlinarith
  have b2 : -(1 / 16) / t ≤ (x ^ 2 - x / 2) / t := by
    apply div_le_div_of_nonneg_right _ ht0.le
    nlinarith [sq_nonneg (x - 1 / 4)]
  have b3 : (x + t - 1 / 2) * x ^ 2 / (2 * t ^ 2) ≤ 3 / 4 / t := by
    rw [div_le_div_iff₀ (by positivity) ht0]
    have hx2 : x ^ 2 ≤ 1 := by nlinarith
    have h1 : (x + t - 1 / 2) * x ^ 2 ≤ (x + t - 1 / 2) * 1 := mul_le_mul_of_nonneg_left hx2 hc
    have h2 : (x + t - 1 / 2) * x ^ 2 * t ≤ (3 / 2 * t) * t :=
      mul_le_mul_of_nonneg_right (by linarith) ht0.le
    nlinarith
  rw [abs_le]
  constructor
  · have : -(1 / 16) / t - 3 / 4 / t ≥ -(1 / t) := by
      rw [ge_iff_le, ← sub_nonneg]
      have : -(1 / 16) / t - 3 / 4 / t - -(1 / t) = (3 / 16) / t := by ring
      rw [this]; positivity
    linarith
  · linarith

theorem abs_barnesB_le {t : ℝ} (ht : 1 ≤ t) : |barnesB t| ≤ 2 / t := by
  have ht0 : 0 < t := by linarith
  set g : ℝ → ℝ := fun x => x * (x + t - 1 / 2) * Real.log t - t * x + x / 2 * Real.log (2 * π)
    with hg
  have hgint : ∫ x in (0 : ℝ)..1, g x =
      (t / 2 + 1 / 12) * Real.log t - t / 2 + Real.log (2 * π) / 4 := by
    have hF : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt
        (fun x : ℝ => (x ^ 3 / 3 + (t - 1 / 2) * x ^ 2 / 2) * Real.log t - t * x ^ 2 / 2 +
          x ^ 2 / 4 * Real.log (2 * π)) (g x) x := by
      intro x _
      have := ((((((hasDerivAt_pow 3 x).div_const 3).add
        (((hasDerivAt_pow 2 x).const_mul (t - 1 / 2)).div_const 2)).mul_const (Real.log t)).sub
          (((hasDerivAt_pow 2 x).const_mul t).div_const 2)).add
          (((hasDerivAt_pow 2 x).div_const 4).mul_const (Real.log (2 * π))))
      refine this.congr_deriv ?_
      simp only [hg]
      push_cast
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
      ((by fun_prop : Continuous g).intervalIntegrable 0 1)]
    ring
  have hcont : ContinuousOn (fun x : ℝ => x * Real.log (Real.Gamma (x + t))) (Set.uIcc 0 1) := by
    refine continuousOn_id.mul ?_
    refine continuousOn_logGamma.comp (continuousOn_id.add continuousOn_const) ?_
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    show (0 : ℝ) < x + t
    linarith [hx.1]
  have hpt : ∀ x ∈ Set.uIoc (0 : ℝ) 1,
      ‖x * Real.log (Real.Gamma (x + t)) - g x‖ ≤ 2 / t := by
    intro x hx
    rw [Set.uIoc_of_le zero_le_one] at hx
    have hx0 : 0 ≤ x := hx.1.le
    have hx1 : x ≤ 1 := hx.2
    have hxt : 0 < x + t := by linarith
    obtain ⟨hμ0, hμ1⟩ := binetIntegral_mem hxt
    have hρ := log_one_add_bounds hx0 hx1 ht
    have hμ : binetIntegral (x + t) ≤ 1 / (12 * t) :=
      hμ1.trans (one_div_le_one_div_of_le (by positivity) (by linarith))
    have he : x * Real.log (Real.Gamma (x + t)) - g x =
        x * (((x + t - 1 / 2) * (Real.log (x + t) - Real.log t) - x) +
          binetIntegral (x + t)) := by
      rw [log_Gamma_eq_add_binetIntegral hxt, hg]
      ring
    rw [he, Real.norm_eq_abs, abs_mul, abs_of_nonneg hx0]
    have h12 : 1 / (12 * t) ≤ 1 / t := one_div_le_one_div_of_le ht0 (by linarith)
    have : |((x + t - 1 / 2) * (Real.log (x + t) - Real.log t) - x) + binetIntegral (x + t)|
        ≤ 2 / t := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_of_nonneg hμ0]
      have : 2 / t = 1 / t + 1 / t := by ring
      linarith
    calc x * |((x + t - 1 / 2) * (Real.log (x + t) - Real.log t) - x) + binetIntegral (x + t)|
        ≤ 1 * (2 / t) := by
          gcongr
      _ = 2 / t := one_mul _
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [intervalIntegral.integral_sub (hcont.intervalIntegrable)
    ((by fun_prop : Continuous g).intervalIntegrable 0 1), hgint] at hint
  have hB : barnesB t = -((∫ x in (0 : ℝ)..1, x * Real.log (Real.Gamma (x + t))) -
      ((t / 2 + 1 / 12) * Real.log t - t / 2 + Real.log (2 * π) / 4)) := by
    rw [barnesB, barnesPsi]; ring
  rw [hB, abs_neg]
  simpa using hint

/-! ### `D - B` is constant -/

theorem hasDerivAt_integral_one {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioi 0)) {y : ℝ}
    (hy : 0 < y) : HasDerivAt (fun y => ∫ u in (1 : ℝ)..y, f u) (f y) y := by
  have hsub : Set.uIcc 1 y ⊆ Set.Ioi 0 := by
    intro u hu
    rcases Set.mem_uIcc.mp hu with h | h
    · show (0 : ℝ) < u; linarith [h.1]
    · show (0 : ℝ) < u; linarith [h.1]
  exact intervalIntegral.integral_hasDerivAt_right ((hf.mono hsub).intervalIntegrable)
    (hf.stronglyMeasurableAtFilter isOpen_Ioi y hy) (hf.continuousAt (Ioi_mem_nhds hy))

/-- `Λ(y) = ∫₁^y log Γ`. -/
def barnesLam (y : ℝ) : ℝ := ∫ u in (1 : ℝ)..y, Real.log (Real.Gamma u)

/-- `P(y) = ∫₁^y u log Γ(u) du`. -/
def barnesP (y : ℝ) : ℝ := ∫ u in (1 : ℝ)..y, u * Real.log (Real.Gamma u)

theorem continuousOn_mul_logGamma :
    ContinuousOn (fun u : ℝ => u * Real.log (Real.Gamma u)) (Set.Ioi 0) :=
  continuousOn_id.mul continuousOn_logGamma

theorem intervalIntegrable_of_pos {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioi 0)) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) : IntervalIntegrable f volume a b := by
  refine (hf.mono fun u hu => ?_).intervalIntegrable
  rcases Set.mem_uIcc.mp hu with h | h
  · show (0 : ℝ) < u; linarith [h.1]
  · show (0 : ℝ) < u; linarith [h.1]

theorem barnesPsi_eq {t : ℝ} (ht : 0 < t) :
    barnesPsi t = (barnesP (t + 1) - barnesP t) - t * (barnesLam (t + 1) - barnesLam t) := by
  have h1 : barnesPsi t = ∫ u in t..t + 1, (u - t) * Real.log (Real.Gamma u) := by
    have := intervalIntegral.integral_comp_add_right
      (fun u => (u - t) * Real.log (Real.Gamma u)) t (a := 0) (b := 1)
    simp only [zero_add, add_sub_cancel_right] at this
    rw [barnesPsi, this, add_comm 1 t]
  have ht1 : 0 < t + 1 := by linarith
  have hI1 := intervalIntegrable_of_pos continuousOn_logGamma ht ht1
  have hI2 := intervalIntegrable_of_pos continuousOn_mul_logGamma ht ht1
  have h2 : ∫ u in t..t + 1, (u - t) * Real.log (Real.Gamma u) =
      (∫ u in t..t + 1, u * Real.log (Real.Gamma u)) -
        t * ∫ u in t..t + 1, Real.log (Real.Gamma u) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hI2
      (hI1.const_mul t)]
    congr 1
    ext u
    ring
  rw [h1, h2, barnesP, barnesP, barnesLam, barnesLam,
    intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_of_pos continuousOn_mul_logGamma one_pos ht1)
      (intervalIntegrable_of_pos continuousOn_mul_logGamma one_pos ht),
    intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_of_pos continuousOn_logGamma one_pos ht1)
      (intervalIntegrable_of_pos continuousOn_logGamma one_pos ht)]

/-- The function in 5.17.5. -/
def barnesD (t : ℝ) : ℝ :=
  Real.log (barnesGSucc t).re -
    ((1 / 4) * t ^ 2 + t * Real.log (Real.Gamma (t + 1)) -
      ((1 / 2) * t * (t + 1) + 1 / 12) * Real.log t - Real.log glaisherKinkelin)

/-- `D - B` in terms of `Λ` and `P`. -/
def barnesV (t : ℝ) : ℝ :=
  t / 2 * Real.log (2 * π) - 3 * t ^ 2 / 4 + t ^ 2 / 2 * Real.log t - barnesLam (t + 1) +
    ((barnesP (t + 1) - barnesP t) - t * (barnesLam (t + 1) - barnesLam t)) +
    Real.log glaisherKinkelin - Real.log (2 * π) / 4

theorem barnesD_sub_barnesB {t : ℝ} (ht : 0 < t) : barnesD t - barnesB t = barnesV t := by
  have hΛ : ∫ s in (0 : ℝ)..t, Real.log (Real.Gamma (s + 1)) = barnesLam (t + 1) := by
    have := intervalIntegral.integral_comp_add_right
      (fun u => Real.log (Real.Gamma u)) 1 (a := 0) (b := t)
    simp only [zero_add] at this
    rw [this, barnesLam]
  rw [barnesD, log_barnesGSucc_re ht, hΛ, barnesB, barnesPsi_eq ht, barnesV]
  ring

/-- The derivative of `V`. -/
def barnesW (t : ℝ) : ℝ :=
  Real.log (2 * π) / 2 - t + t * Real.log t - (barnesLam (t + 1) - barnesLam t)

theorem hasDerivAt_barnesV {t : ℝ} (ht : 0 < t) : HasDerivAt barnesV (barnesW t) t := by
  have ht1 : 0 < t + 1 := by linarith
  have hL := hasDerivAt_integral_one continuousOn_logGamma ht
  have hL1 := (hasDerivAt_integral_one continuousOn_logGamma ht1).comp_add_const t 1
  have hP := hasDerivAt_integral_one continuousOn_mul_logGamma ht
  have hP1 := (hasDerivAt_integral_one continuousOn_mul_logGamma ht1).comp_add_const t 1
  have a1 := ((hasDerivAt_id t).div_const 2).mul_const (Real.log (2 * π))
  have a2 := ((hasDerivAt_pow 2 t).const_mul (3 : ℝ)).div_const 4
  have a3 := ((hasDerivAt_pow 2 t).div_const 2).mul (Real.hasDerivAt_log ht.ne')
  have a7 := (hasDerivAt_id t).mul (hL1.sub hL)
  have hT := (((((a1.sub a2).add a3).sub hL1).add ((hP1.sub hP).sub a7)).add_const
    (Real.log glaisherKinkelin)).sub_const (Real.log (2 * π) / 4)
  refine hT.congr_deriv ?_
  simp only [barnesW, barnesLam, id, Pi.sub_apply]
  field_simp
  ring

theorem hasDerivAt_barnesW {t : ℝ} (ht : 0 < t) : HasDerivAt barnesW 0 t := by
  have ht1 : 0 < t + 1 := by linarith
  have hL := hasDerivAt_integral_one continuousOn_logGamma ht
  have hL1 := (hasDerivAt_integral_one continuousOn_logGamma ht1).comp_add_const t 1
  have b1 := (hasDerivAt_id t).mul (Real.hasDerivAt_log ht.ne')
  have hT := (((hasDerivAt_const t (Real.log (2 * π) / 2)).sub (hasDerivAt_id t)).add b1).sub
    (hL1.sub hL)
  refine hT.congr_deriv ?_
  have hG : Real.log (Real.Gamma (t + 1)) = Real.log t + Real.log (Real.Gamma t) := by
    rw [Real.Gamma_add_one ht.ne', Real.log_mul ht.ne' (Real.Gamma_pos_of_pos ht).ne']
  simp only [id, hG]
  field_simp
  ring

theorem barnesV_eq {t : ℝ} (ht : 0 < t) :
    barnesV t = barnesV 1 + barnesW 1 * (t - 1) := by
  have hWc : ∀ t ∈ Set.Ioi (0 : ℝ), barnesW t = barnesW 1 := fun t ht =>
    isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun x hx => (hasDerivAt_barnesW hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hasDerivAt_barnesW hx).deriv) ht (Set.mem_Ioi.mpr one_pos)
  have hU : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun t => barnesV t - barnesW 1 * t) 0 x := by
    intro x hx
    have := (hasDerivAt_barnesV hx).sub ((hasDerivAt_id x).const_mul (barnesW 1))
    refine this.congr_deriv ?_
    rw [hWc x hx]
    simp
  have := isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun x hx => (hU x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hU x hx).deriv) (Set.mem_Ioi.mpr ht) (Set.mem_Ioi.mpr one_pos)
  linarith

theorem isBigO_barnesD :
    Asymptotics.IsBigO atTop barnesD (fun t : ℝ => t ^ (-(1 : ℝ))) := by
  set α := barnesV 1 - barnesW 1
  set β := barnesW 1
  have hDB : ∀ t : ℝ, 0 < t → barnesD t = barnesB t + (α + β * t) := by
    intro t ht
    have := barnesD_sub_barnesB ht
    rw [barnesV_eq ht] at this
    simp only [α, β]
    linarith
  have hD : Tendsto (fun n : ℕ => barnesD n) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := Real.log glaisherKinkelin)).sub tendsto_hseq
    rw [sub_self] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (barnes_nat_eq n hn).symm
  have hB : Tendsto (fun n : ℕ => barnesB n) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n : ℕ => 2 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    refine squeeze_zero_norm' ?_ h2
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact abs_barnesB_le (by exact_mod_cast hn)
  have hab : Tendsto (fun n : ℕ => α + β * n) atTop (𝓝 0) := by
    have h := hD.sub hB
    rw [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [hDB n (by exact_mod_cast hn)]
    ring
  have hβ : β = 0 := by
    have h := ((hab.comp (tendsto_add_atTop_nat 1)).sub hab)
    rw [sub_zero] at h
    have h' : (fun n : ℕ => ((fun n : ℕ => α + β * n) ∘ fun n => n + 1) n - (α + β * n)) =
        fun _ => β := by
      ext n; simp only [Function.comp_apply]; push_cast; ring
    rw [h'] at h
    exact tendsto_nhds_unique tendsto_const_nhds h
  have hα : α = 0 := by
    simp only [hβ, zero_mul, add_zero] at hab
    exact tendsto_nhds_unique tendsto_const_nhds hab
  refine Asymptotics.IsBigO.of_bound 2 ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  have ht0 : 0 < t := by linarith
  rw [hDB t ht0, hα, hβ, zero_mul, add_zero, add_zero, Real.rpow_neg_one, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht0)]
  simpa [div_eq_mul_inv] using abs_barnesB_le ht

end BarnesAsymp

@[dlmf 5.17.E5]
theorem log_barnesG_asymptotic :
    Asymptotics.IsBigO atTop
      (fun t : ℝ => Real.log (barnesGSucc t).re -
        ((1 / 4) * t ^ 2 + t * Real.log (Real.Gamma (t + 1)) -
          ((1 / 2) * t * (t + 1) + 1 / 12) * Real.log t -
          Real.log glaisherKinkelin))
      (fun t : ℝ => (t : ℝ) ^ (-(1 : ℝ))) :=
  BarnesAsymp.isBigO_barnesD

end DLMF.Gamma
