/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.SeriesProperties
public import DLMF.Hypergeometric.ConnectionFormulas

/-!
# Parameter dependence and boundary convergence (DLMF §§15.2, 15.4)

Already in Mathlib, without duplicate declarations here:
* DLMF 15.2.E1: `ordinaryHypergeometric_eq_tsum`.
* DLMF 15.2.E2: `coeff_regularizedGaussHGFunSeries` and the definition
  `regularizedGaussHGFun`; `ordinaryHypergeometric_div_Gamma_eq` compares them.
* DLMF 15.2.i: `ordinaryHypergeometricSeries_radius_eq_one` and
  `ordinaryHypergeometric_radius_top_of_neg_nat₁/₂/₃` cover the series radius.
See https://dlmf.nist.gov/15.2 . These Mathlib functions are sums of series;
their values outside convergence are not DLMF's analytic continuations.
Conditional convergence is therefore stated with ordered finite partial sums.
The terminating identity E4 and absolute convergence on the unit circle already
appear in `Basic`. E5/E6 prescribe different singular-parameter limit conventions;
the diagonal convention E6 must not be confused with totalized division.
-/

@[expose] public section

open Complex Filter FormalMultilinearSeries
open scoped Real Topology

noncomputable section

namespace DLMF.Hypergeometric

/-- Identity under the stated parameter and domain assumptions: `regularizedGaussHGFun a b (-n) z
= poch a (n + 1) * poch b (n + 1) / ((n + 1).factorial : ℂ) * z ^ (n + 1) * ₂F₁ (a + n + 1) (b
+ n + 1) (n + 2) z`. -/
@[dlmf 15.2.E3_5]
theorem regularized_at_neg_nat (a b : ℂ) (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    regularizedGaussHGFun a b (-n) z =
      poch a (n + 1) * poch b (n + 1) / ((n + 1).factorial : ℂ) * z ^ (n + 1) *
        ₂F₁ (a + n + 1) (b + n + 1) (n + 2) z := by
  rw [regularizedGaussHGFun_eq_tsum]
  have hs := summable_regularizedGaussHGFun_term a b (-n) hz
  rw [← hs.sum_add_tsum_nat_add (n + 1)]
  have hzero : ∀ k ∈ Finset.range (n + 1),
      (ascPochhammer ℂ k).eval a * (ascPochhammer ℂ k).eval b * z ^ k / k.factorial *
        (Gamma (-(n : ℂ) + k))⁻¹ = 0 := by
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have : (-(n : ℂ) + k) = -((n - k : ℕ) : ℂ) := by push_cast [Nat.cast_sub hk']; ring
    rw [this, Complex.Gamma_neg_nat_eq_zero, inv_zero, mul_zero]
  rw [Finset.sum_eq_zero hzero, zero_add]
  have hF := (hasFPowerSeriesOnBall_ordinaryHypergeometric (a + n + 1) (b + n + 1)
    (n + 2)).hasSum_mul_pow (mem_eball_one_of_norm_lt_one hz)
  rw [← hF.tsum_eq, ← tsum_mul_left]
  congr 1
  funext j
  have hpole : ∀ k : ℕ, ((n : ℂ) + 2) ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.natCast_re, Complex.re_ofNat, Complex.neg_re] at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hΓ : Gamma ((n : ℂ) + 2 + j) = (ascPochhammer ℂ j).eval ((n : ℂ) + 2) * Gamma ((n : ℂ) + 2) := by
    rw [← Gamma_add_nat_div_Gamma_eq (n := j) ((n : ℂ) + 2) hpole]
    field_simp [Gamma_ne_zero hpole]
  have hΓ1 : Gamma ((n : ℂ) + 2 + j) = ((n + 1 + j).factorial : ℂ) := by
    rw [show (n : ℂ) + 2 + j = ((n + 1 + j : ℕ) : ℂ) + 1 by push_cast; ring]
    exact Complex.Gamma_nat_eq_factorial _
  have hΓ2 : Gamma ((n : ℂ) + 2) = ((n + 1).factorial : ℂ) := by
    rw [show (n : ℂ) + 2 = ((n + 1 : ℕ) : ℂ) + 1 by push_cast; ring]
    exact Complex.Gamma_nat_eq_factorial _
  have hΓ3 : Gamma (-(n : ℂ) + ((n + 1 + j : ℕ) : ℂ)) = (j.factorial : ℂ) := by
    rw [show -(n : ℂ) + ((n + 1 + j : ℕ) : ℂ) = (j : ℂ) + 1 by push_cast; ring]
    exact Complex.Gamma_nat_eq_factorial _
  have hp : (ascPochhammer ℂ j).eval ((n : ℂ) + 2) ≠ 0 := poch_ne_zero_of_not_neg_nat hpole j
  have hf1 : ((n + 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf2 : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf3 : ((n + 1 + j).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [hΓ1, hΓ2] at hΓ
  simp only [gaussHGCoeff, poch]
  rw [add_comm j (n + 1), ascPochhammer_eval_add a, ascPochhammer_eval_add b, hΓ3,
    show a + ((n + 1 : ℕ) : ℂ) = a + n + 1 by push_cast; ring,
    show b + ((n + 1 : ℕ) : ℂ) = b + n + 1 by push_cast; ring, pow_add]
  field_simp
  linear_combination (-((ascPochhammer ℂ (n + 1)).eval a * (ascPochhammer ℂ j).eval (a + n + 1) *
    (ascPochhammer ℂ (n + 1)).eval b * (ascPochhammer ℂ j).eval (b + n + 1) *
    z ^ (n + 1) * z ^ j)) * hΓ

/-- Differentiability of the indicated parameterized function: `Differentiable ℂ (fun p : ℂ × ℂ ×
ℂ => regularizedGaussHGFun p.1 p.2.1 p.2.2 z)`. -/
@[dlmf 15.2.ii]
theorem entire_regularized_parameters {z : ℂ} (hz : ‖z‖ < 1) :
    Differentiable ℂ (fun p : ℂ × ℂ × ℂ =>
      regularizedGaussHGFun p.1 p.2.1 p.2.2 z) :=
  differentiable_regularizedGaussHGFun_of_differentiable differentiable_fst
    (differentiable_fst.comp differentiable_snd) (differentiable_snd.comp differentiable_snd) hz

/-- The map `(fun c : ℂ => ₂F₁ a b c z / Gamma c)` tends to `(𝓝 (regularizedGaussHGFun a b (-n)
z))` along `(𝓝[≠] (-(n : ℂ)))`. -/
@[dlmf 15.2.E3_5]
theorem tendsto_regularized_at_neg_nat (a b : ℂ) (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    Tendsto (fun c : ℂ => ₂F₁ a b c z / Gamma c) (𝓝[≠] (-(n : ℂ)))
      (𝓝 (regularizedGaussHGFun a b (-n) z)) := by
  have hcont : ContinuousAt (fun c => regularizedGaussHGFun a b c z) (-(n : ℂ)) :=
    ((analyticOnNhd_regularizedGaussHGFun_c a b hz) _ (Set.mem_univ _)).continuousAt
  refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [eventually_nhdsWithin_ne_neg_nat n] with c hc
  exact regularizedGaussHGFun_eq_div_Gamma hc z

/-- Dirichlet's test with a sequence of bounded variation tending to zero. -/
theorem exists_tendsto_sum_mul_of_bdd_variation {f g : ℕ → ℂ} {B : ℝ}
    (hf0 : Tendsto f atTop (𝓝 0)) (hvar : Summable fun k => ‖f (k + 1) - f k‖)
    (hG : ∀ n, ‖∑ i ∈ Finset.range n, g i‖ ≤ B) :
    ∃ s : ℂ, Tendsto (fun n => ∑ i ∈ Finset.range n, f i * g i) atTop (𝓝 s) := by
  set G : ℕ → ℂ := fun n => ∑ i ∈ Finset.range n, g i with hGdef
  set h : ℕ → ℂ := fun i => (f (i + 1) - f i) * G (i + 1) with hh
  have hhs : Summable h := by
    refine Summable.of_norm_bounded (g := fun i => B * ‖f (i + 1) - f i‖) (hvar.mul_left B)
      fun i => ?_
    rw [hh, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hG _) (norm_nonneg _)
  refine ⟨0 - ∑' i, h i, ?_⟩
  have hparts : ∀ n, ∑ i ∈ Finset.range n, f i * g i =
      f (n - 1) * G n - ∑ i ∈ Finset.range (n - 1), h i := by
    intro n
    have := Finset.sum_range_by_parts (n := n) f g
    simpa [smul_eq_mul, hGdef, hh] using this
  simp_rw [hparts]
  refine Tendsto.sub ?_ ?_
  · have hB : ∀ n, ‖G n‖ ≤ B := hG
    have hf1 : Tendsto (fun n => f (n - 1)) atTop (𝓝 0) := hf0.comp (tendsto_sub_atTop_nat 1)
    rw [tendsto_zero_iff_norm_tendsto_zero] at hf1 ⊢
    have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using hf1.mul_const B)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB n) (norm_nonneg _)
  · exact hhs.hasSum.tendsto_sum_nat.comp (tendsto_sub_atTop_nat 1)

/-- Formula under the stated hypotheses: `(∃ s : ℂ, Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
gaussHGCoeff a b c k * z ^ k) atTop (𝓝 s)) ∧ ¬ Summable (fun k : ℕ => ‖gaussHGCoeff a b c k *
z ^ k‖)`. -/
@[dlmf 15.2.i]
theorem conditional_convergence_on_circle
    {a b c z : ℂ}
    (ha : ∀ k : ℕ, a ≠ -(k : ℂ))
    (hb : ∀ k : ℕ, b ≠ -(k : ℂ))
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hz : ‖z‖ = 1)
    (hz1 : z ≠ 1)
    (hlo : -1 < (c - a - b).re) (hhi : (c - a - b).re ≤ 0) :
    (∃ s : ℂ, Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
      gaussHGCoeff a b c k * z ^ k) atTop (𝓝 s)) ∧
      ¬ Summable (fun k : ℕ => ‖gaussHGCoeff a b c k * z ^ k‖) := by
  set α := a + b - c - 1 with hα
  set σ := α.re with hσ
  have hσ0 : σ < 0 := by simp only [hσ, hα, sub_re, add_re, one_re] at hlo ⊢; simp at hlo; linarith
  have hσ1 : -1 ≤ σ := by simp only [hσ, hα, sub_re, add_re, one_re] at hhi ⊢; simp at hhi; linarith
  set L := Gamma c / (Gamma a * Gamma b) with hL
  have hL0 : L ≠ 0 :=
    div_ne_zero (Gamma_ne_zero hc) (mul_ne_zero (Gamma_ne_zero ha) (Gamma_ne_zero hb))
  have hLpos : 0 < ‖L‖ := norm_pos_iff.mpr hL0
  have hlim := tendsto_gaussHGCoeff_div_cpow ha hb hc
  -- two-sided bounds on the coefficients
  have hev : ∀ᶠ k : ℕ in atTop, ‖L‖ / 2 * (k : ℝ) ^ σ ≤ ‖gaussHGCoeff a b c k‖ ∧
      ‖gaussHGCoeff a b c k‖ ≤ 3 * ‖L‖ / 2 * (k : ℝ) ^ σ := by
    have h1 := (hlim.sub_const L).norm.eventually (gt_mem_nhds (show ‖L - L‖ < ‖L‖ / 2 by
      rw [sub_self, norm_zero]; linarith))
    filter_upwards [h1, eventually_ge_atTop 1] with k hk hk1
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
    have hnk : ‖(k : ℂ) ^ α‖ = (k : ℝ) ^ σ := norm_natCast_cpow_of_pos (by exact_mod_cast hk1) α
    have hkσ : 0 < (k : ℝ) ^ σ := Real.rpow_pos_of_pos hkpos σ
    have hk0 : (k : ℂ) ^ α ≠ 0 := by
      intro h; rw [h, norm_zero] at hnk; linarith
    have heq : gaussHGCoeff a b c k = (gaussHGCoeff a b c k / (k : ℂ) ^ α) * (k : ℂ) ^ α := by
      rw [div_mul_cancel₀ _ hk0]
    have hn : ‖gaussHGCoeff a b c k‖ = ‖gaussHGCoeff a b c k / (k : ℂ) ^ α‖ * (k : ℝ) ^ σ := by
      rw [heq, norm_mul, hnk, mul_div_cancel_right₀ _ hk0]
    have hq := norm_sub_norm_le (gaussHGCoeff a b c k / (k : ℂ) ^ α) L
    have hq' := norm_sub_norm_le L (gaussHGCoeff a b c k / (k : ℂ) ^ α)
    rw [norm_sub_rev] at hq'
    constructor
    · rw [hn]; nlinarith
    · rw [hn]; nlinarith
  have hzk : ∀ k : ℕ, ‖z ^ k‖ = 1 := fun k => by rw [norm_pow, hz, one_pow]
  refine ⟨?_, ?_⟩
  · -- Dirichlet's test
    have hf0 : Tendsto (gaussHGCoeff a b c) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hr : Tendsto (fun k : ℕ => 3 * ‖L‖ / 2 * (k : ℝ) ^ σ) atTop (𝓝 0) := by
        have := (tendsto_rpow_neg_atTop (y := -σ) (by linarith)).comp tendsto_natCast_atTop_atTop
        simpa [Function.comp_def] using this.const_mul (3 * ‖L‖ / 2)
      exact squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _)
        (hev.mono fun k hk => hk.2) hr
    set M := ‖α‖ + ‖a * b - c‖ with hM
    have hvar : Summable fun k => ‖gaussHGCoeff a b c (k + 1) - gaussHGCoeff a b c k‖ := by
      refine Summable.of_norm_bounded_eventually_nat (g := fun k : ℕ => 3 * M * ‖L‖ * (k : ℝ) ^ (σ - 1))
        ((Real.summable_nat_rpow.mpr (by linarith)).mul_left _) ?_
      obtain ⟨K, hK⟩ : ∃ K : ℕ, 2 * ‖c‖ + 1 ≤ K := exists_nat_ge _
      filter_upwards [hev, eventually_ge_atTop (K + 1)] with k hk hkK
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
      have hkK' : (K : ℝ) + 1 ≤ k := by exact_mod_cast hkK
      have hrec := gaussHGCoeff_recurrence (a := a) (b := b) hc k
      have hck : (k + 1 : ℝ) / 2 ≤ ‖c + k‖ := by
        have := norm_sub_norm_le ((k : ℂ)) (-c)
        rw [Complex.norm_natCast, norm_neg, sub_neg_eq_add, add_comm] at this
        linarith
      have hck0 : c + k ≠ 0 := fun h => by rw [h, norm_zero] at hck; linarith
      have hk10 : (k : ℂ) + 1 ≠ 0 := by
        have : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        simpa using this
      have hdiff : gaussHGCoeff a b c (k + 1) - gaussHGCoeff a b c k =
          (α * k + (a * b - c)) * gaussHGCoeff a b c k / ((k + 1) * (c + k)) := by
        rw [eq_div_iff (mul_ne_zero hk10 hck0)]
        simp only [hα]
        linear_combination hrec
      rw [norm_norm, hdiff, norm_div, norm_mul, norm_mul]
      have hnum : ‖α * k + (a * b - c)‖ ≤ M * (k + 1) := by
        calc ‖α * k + (a * b - c)‖ ≤ ‖α‖ * k + ‖a * b - c‖ := by
              refine (norm_add_le _ _).trans ?_
              rw [norm_mul, Complex.norm_natCast]
          _ ≤ M * (k + 1) := by
              simp only [hM]
              nlinarith [norm_nonneg α, norm_nonneg (a * b - c)]
      have hk1' : ‖(k : ℂ) + 1‖ = k + 1 := by
        rw [show (k : ℂ) + 1 = ((k + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
        push_cast; ring
      rw [hk1']
      have hkσ : (k : ℝ) ^ (σ - 1) = (k : ℝ) ^ σ / k := by
        rw [Real.rpow_sub (by linarith), Real.rpow_one]
      rw [hkσ, div_le_iff₀ (by positivity)]
      have hcpos : 0 < ‖c + k‖ := by linarith
      have hM0 : 0 ≤ M := by positivity
      calc ‖α * k + (a * b - c)‖ * ‖gaussHGCoeff a b c k‖
          ≤ M * (k + 1) * (3 * ‖L‖ / 2 * (k : ℝ) ^ σ) :=
            mul_le_mul hnum hk.2 (norm_nonneg _) (by positivity)
        _ ≤ 3 * M * ‖L‖ * ((k : ℝ) ^ σ / k) * ((k + 1) * ‖c + k‖) := by
            rw [div_mul_eq_mul_div, mul_div_assoc]
            have hkσ0 : 0 ≤ (k : ℝ) ^ σ := by positivity
            have : (k : ℝ) ≤ 2 * ‖c + k‖ := by linarith
            have key : (k + 1) * (3 * ‖L‖ / 2 * (k : ℝ) ^ σ) * M * k ≤
                3 * M * ‖L‖ * (k : ℝ) ^ σ * ((k + 1) * ‖c + k‖) := by
              have h0 : 0 ≤ (k + 1) * (3 * ‖L‖ / 2 * (k : ℝ) ^ σ) * M := by positivity
              nlinarith
            rw [div_eq_mul_inv]
            field_simp
            nlinarith [key]
    have hG : ∀ n, ‖∑ i ∈ Finset.range n, z ^ i‖ ≤ 2 / ‖z - 1‖ := by
      intro n
      rw [geom_sum_eq hz1, norm_div]
      have h1 : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
      rw [div_le_div_iff_of_pos_right h1]
      calc ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [hzk, norm_one]; norm_num
    exact exists_tendsto_sum_mul_of_bdd_variation hf0 hvar hG
  · -- the series is not absolutely convergent
    intro hsum
    apply Real.not_summable_natCast_inv
    have hs : Summable fun k : ℕ => ‖gaussHGCoeff a b c k‖ := by
      simpa [norm_mul, hzk] using hsum
    have hs' := hs.mul_left (2 / ‖L‖)
    refine Summable.of_norm_bounded_eventually_nat hs' ?_
    filter_upwards [hev, eventually_ge_atTop 1] with k hk hk1
    have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hpow : (k : ℝ)⁻¹ ≤ (k : ℝ) ^ σ := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hk1' hσ1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (k : ℝ)⁻¹ ≤ (k : ℝ) ^ σ := hpow
      _ = 2 / ‖L‖ * (‖L‖ / 2 * (k : ℝ) ^ σ) := by field_simp
      _ ≤ 2 / ‖L‖ * ‖gaussHGCoeff a b c k‖ := by gcongr; exact hk.1

/-- Formula under the stated hypotheses: `¬ ∃ s : ℂ, Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
gaussHGCoeff a b c k * z ^ k) atTop (𝓝 s)`. -/
@[dlmf 15.2.i]
theorem divergence_on_circle
    {a b c z : ℂ}
    (ha : ∀ k : ℕ, a ≠ -(k : ℂ))
    (hb : ∀ k : ℕ, b ≠ -(k : ℂ))
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hz : ‖z‖ = 1)
    (h :
    (c - a - b).re ≤ -1) :
    ¬ ∃ s : ℂ, Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
      gaussHGCoeff a b c k * z ^ k) atTop (𝓝 s) := by
  rintro ⟨S, hS⟩
  -- The terms of a convergent series tend to zero.
  have hterm : Tendsto (fun n : ℕ => gaussHGCoeff a b c n * z ^ n) atTop (𝓝 0) := by
    have h1 := hS.comp (tendsto_add_atTop_nat 1)
    have h2 := h1.sub hS
    rw [sub_self] at h2
    refine h2.congr fun n => ?_
    simp [Finset.sum_range_succ]
  -- But the normalized coefficients tend to a nonzero limit.
  have hlim := tendsto_gaussHGCoeff_div_cpow ha hb hc
  have hL : Gamma c / (Gamma a * Gamma b) ≠ 0 :=
    div_ne_zero (Gamma_ne_zero hc) (mul_ne_zero (Gamma_ne_zero ha) (Gamma_ne_zero hb))
  have hre : 0 ≤ (a + b - c - 1).re := by
    simp only [sub_re, add_re, one_re] at h ⊢; linarith
  have hbound : ∀ᶠ n : ℕ in atTop, ‖Gamma c / (Gamma a * Gamma b)‖ / 2 ≤
      ‖gaussHGCoeff a b c n * z ^ n‖ := by
    have hev := hlim.norm.eventually (lt_mem_nhds (show ‖Gamma c / (Gamma a * Gamma b)‖ / 2 <
      ‖Gamma c / (Gamma a * Gamma b)‖ by have := norm_pos_iff.mpr hL; linarith))
    filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [norm_div (gaussHGCoeff a b c n), norm_natCast_cpow_of_pos (by exact_mod_cast hn1)] at hn
    have hpow : 1 ≤ (n : ℝ) ^ (a + b - c - 1).re := Real.one_le_rpow (by exact_mod_cast hn1) hre
    have hp0 : 0 < (n : ℝ) ^ (a + b - c - 1).re := by positivity
    rw [norm_mul, norm_pow, hz, one_pow, mul_one]
    rw [lt_div_iff₀ hp0] at hn
    nlinarith [norm_nonneg (gaussHGCoeff a b c n)]
  have hpos : 0 < ‖Gamma c / (Gamma a * Gamma b)‖ / 2 := by
    have := norm_pos_iff.mpr hL; linarith
  have := (hterm.norm.eventually (gt_mem_nhds (show ‖(0 : ℂ)‖ <
    ‖Gamma c / (Gamma a * Gamma b)‖ / 2 by rw [norm_zero]; exact hpos))).and hbound
  obtain ⟨n, h1, h2⟩ := this.exists
  linarith

/-- `₂F₁(p,q;r;1-x) → 1` as `x → 1⁻`. -/
theorem tendsto_ordinaryHypergeometric_one_sub_left (p q r : ℂ) :
    Tendsto (fun x : ℝ => ₂F₁ p q r (1 - (x : ℂ))) (𝓝[<] 1) (𝓝 1) := by
  have hc : ContinuousAt (₂F₁ p q r : ℂ → ℂ) (0 : ℂ) :=
    ((hasFPowerSeriesOnBall_ordinaryHypergeometric p q r).analyticAt_of_mem
      (mem_eball_one_of_norm_lt_one (by simp))).continuousAt
  have h0 : Tendsto (fun x : ℝ => 1 - (x : ℂ)) (𝓝[<] 1) (𝓝 0) := by
    have : Tendsto (fun x : ℝ => 1 - (x : ℂ)) (𝓝 1) (𝓝 (1 - ((1 : ℝ) : ℂ))) :=
      (continuous_const.sub continuous_ofReal).tendsto 1
    rw [ofReal_one, sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have := hc.tendsto.comp h0
  simpa [Function.comp_def, ordinaryHypergeometric_zero] using this

/-- `(-log(1-x))⁻¹ → 0` as `x → 1⁻`. -/
theorem tendsto_recip_neg_log_one_sub_left :
    Tendsto (fun x : ℝ => ((-Real.log (1 - x) : ℝ) : ℂ)⁻¹) (𝓝[<] 1) (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] 1) (𝓝[>] 0) := by
    have hc : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] 1) (𝓝 0) := by
      have h : Tendsto (fun x : ℝ => 1 - x) (𝓝 1) (𝓝 (1 - 1)) :=
        tendsto_const_nhds.sub tendsto_id
      rw [sub_self] at h
      exact h.mono_left nhdsWithin_le_nhds
    refine tendsto_nhdsWithin_iff.mpr ⟨hc, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_Ioi, sub_pos]; exact hx
  have h2 : Tendsto (fun x : ℝ => -Real.log (1 - x)) (𝓝[<] 1) atTop :=
    tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp h1)
  have h3 := (tendsto_inv_atTop_zero.comp h2)
  have h4 := (continuous_ofReal.tendsto 0).comp h3
  simpa [Function.comp_def] using h4

/-- The map `(fun x : ℝ => ₂F₁ a b (a + b) (x : ℂ) / (-Real.log (1 - x) : ℂ))` tends to `(𝓝 (Gamma
(a + b) / (Gamma a * Gamma b)))` along `(𝓝[<] 1)`. -/
@[dlmf 15.4.E21]
theorem zero_balanced_limit {a b : ℂ} (hc : ∀ k : ℕ, a + b ≠ -(k : ℂ)) :
    Tendsto (fun x : ℝ => ₂F₁ a b (a + b) (x : ℂ) / (-Real.log (1 - x) : ℂ))
      (𝓝[<] 1) (𝓝 (Gamma (a + b) / (Gamma a * Gamma b))) := by
  have hL := tendsto_recip_neg_log_one_sub_left
  have hev : ∀ᶠ x : ℝ in 𝓝[<] 1, x ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
  by_cases hab : (∀ k : ℕ, a ≠ -(k : ℂ)) ∧ (∀ k : ℕ, b ≠ -(k : ℂ))
  · obtain ⟨ha, hb⟩ := hab
    set δ : ℕ → ℂ := fun k => -digamma (k + 1) - digamma (k + 1) + digamma (a + k) + digamma (b + k)
      with hδ
    set h : ℕ → ℂ := fun k => gaussHGCoeff a b 1 k * δ k with hh
    obtain ⟨Ca, hCa⟩ := exists_norm_digamma_add_nat_le ha
    obtain ⟨Cb, hCb⟩ := exists_norm_digamma_add_nat_le hb
    obtain ⟨C1, hC1⟩ := exists_norm_digamma_add_nat_le (x := 1) (fun m hm => by
      have := congrArg re hm; simp at this; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    have hr : 1 ≤ (ofScalars ℂ h).radius := by
      refine one_le_radius_of_le_gaussHGCoeff a b 1 (C := Ca + Cb + C1 + C1) 0 fun k _ => ?_
      simp only [hh, hδ, norm_mul]
      have h1 : digamma ((k : ℂ) + 1) = digamma (1 + k) := by rw [add_comm]
      rw [h1]
      have : ‖-digamma (1 + k) - digamma (1 + k) + digamma (a + k) + digamma (b + k)‖ ≤
          (Ca + Cb + C1 + C1) * (k + 1) := by
        rw [show -digamma (1 + k) - digamma (1 + k) + digamma (a + k) + digamma (b + k) =
          (digamma (a + k) + digamma (b + k)) - (digamma (1 + k) + digamma (1 + k)) by ring]
        calc ‖(digamma (a + k) + digamma (b + k)) - (digamma (1 + k) + digamma (1 + k))‖
            ≤ ‖digamma (1 + k)‖ + ‖digamma (1 + k)‖ + ‖digamma (a + k)‖ + ‖digamma (b + k)‖ := by
              refine (norm_sub_le _ _).trans ?_
              have h1 := norm_add_le (digamma (a + k)) (digamma (b + k))
              have h2 := norm_add_le (digamma (1 + k)) (digamma (1 + k))
              linarith
          _ ≤ C1 * (k + 1) + C1 * (k + 1) + Ca * (k + 1) + Cb * (k + 1) := by
              gcongr
              · exact hC1 k
              · exact hC1 k
              · exact hCa k
              · exact hCb k
          _ = _ := by ring
      calc ‖gaussHGCoeff a b 1 k‖ * ‖-digamma (1 + k) - digamma (1 + k) + digamma (a + k) +
            digamma (b + k)‖ ≤ ‖gaussHGCoeff a b 1 k‖ * ((Ca + Cb + C1 + C1) * (k + 1)) := by gcongr
        _ = _ := by ring
    have hH := hasFPowerSeriesOnBall_ofScalars_sum hr
    set H := (ofScalars ℂ h).sum with hHdef
    have hcab : ∀ k : ℕ, a + b ≠ -(k : ℂ) := hc
    -- the representation for `0 < x < 1`
    have hrep : ∀ x : ℝ, 0 < x → x < 1 →
        ₂F₁ a b (a + b) (x : ℂ) / (-Real.log (1 - x) : ℂ) =
          Gamma (a + b) / (Gamma a * Gamma b) * (₂F₁ a b 1 (1 - (x : ℂ)) +
            H (1 - (x : ℂ)) * -((-Real.log (1 - x) : ℝ) : ℂ)⁻¹) := by
      intro x hx0 hx1
      have hxn : ‖(x : ℂ)‖ < 1 := by rw [norm_real, Real.norm_eq_abs, abs_of_pos hx0]; exact hx1
      have hwr : (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) := by push_cast; ring
      have hwn : ‖1 - (x : ℂ)‖ < 1 := by
        rw [hwr, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith
      have hE := logarithmic_connection_one_sub (a := a) (b := b) (z := (x : ℂ)) 0 ha hb hxn hwn
      simp only [Nat.cast_zero, add_zero, Finset.range_zero, Finset.sum_empty, mul_zero, pow_zero,
        zero_sub] at hE
      have hlog : log (1 - (x : ℂ)) = ((Real.log (1 - x) : ℝ) : ℂ) := by
        rw [hwr, ofReal_log (by linarith)]
      have hL0 : ((Real.log (1 - x) : ℝ) : ℂ) ≠ 0 := by
        rw [ofReal_ne_zero]
        exact (Real.log_neg (by linarith) (by linarith)).ne
      have hwb : 1 - (x : ℂ) ∈ Metric.eball (0 : ℂ) 1 := mem_eball_one_of_norm_lt_one hwn
      have hF1 := (hasFPowerSeriesOnBall_ordinaryHypergeometric a b 1).hasSum_mul_pow hwb
      have hHs := hH.hasSum_mul_pow hwb
      have hsum : HasSum (fun k : ℕ => poch a k * poch b k / ((k.factorial : ℂ) * (k.factorial : ℂ)) *
          (1 - (x : ℂ)) ^ k * (log (1 - (x : ℂ)) - digamma (k + 1) - digamma (k + 1) +
            digamma (a + k) + digamma (b + k)))
          (log (1 - (x : ℂ)) * ₂F₁ a b 1 (1 - (x : ℂ)) + H (1 - (x : ℂ))) := by
        convert (hF1.mul_left (log (1 - (x : ℂ)))).add hHs using 1
        funext k
        simp only [hh, hδ, gaussHGCoeff, poch_nat_one]
        ring
      rw [hsum.tsum_eq] at hE
      have hFR : ₂F₁ a b (a + b) (x : ℂ) = Gamma (a + b) * regularizedGaussHGFun a b (a + b) x := by
        rw [regularizedGaussHGFun_eq_div_Gamma hcab, mul_div_cancel₀ _ (Gamma_ne_zero hcab)]
      rw [hFR, hE, ← hlog]
      have hL0' : log (1 - (x : ℂ)) ≠ 0 := by rw [hlog]; exact hL0
      push_cast
      rw [← hlog]
      field_simp
    have hF1 := tendsto_ordinaryHypergeometric_one_sub_left a b 1
    have hH0 : Tendsto (fun x : ℝ => H (1 - (x : ℂ))) (𝓝[<] 1) (𝓝 (H 0)) := by
      have hcH : ContinuousAt H 0 :=
        (hH.analyticAt_of_mem (mem_eball_one_of_norm_lt_one (by simp))).continuousAt
      have h0 : Tendsto (fun x : ℝ => 1 - (x : ℂ)) (𝓝[<] 1) (𝓝 0) := by
        have : Tendsto (fun x : ℝ => 1 - (x : ℂ)) (𝓝 1) (𝓝 (1 - ((1 : ℝ) : ℂ))) :=
          (continuous_const.sub continuous_ofReal).tendsto 1
        rw [ofReal_one, sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      exact hcH.tendsto.comp h0
    have hlim := (hF1.add (hH0.mul hL.neg)).const_mul (Gamma (a + b) / (Gamma a * Gamma b))
    rw [neg_zero, mul_zero, add_zero, mul_one] at hlim
    refine hlim.congr' ?_
    filter_upwards [hev] with x hx
    exact (hrep x hx.1 hx.2).symm
  · -- a terminating numerator: the series is a polynomial
    have hpoly : ∃ n : ℕ, ∃ b' : ℂ, (₂F₁ a b (a + b) : ℂ → ℂ) = ₂F₁ (-(n : ℂ)) b' (a + b) ∧
        Gamma a * Gamma b = 0 := by
      simp only [not_and_or, not_forall, not_not] at hab
      rcases hab with ⟨n, hn⟩ | ⟨n, hn⟩
      · exact ⟨n, b, by rw [hn], by rw [hn, Gamma_neg_nat_eq_zero, zero_mul]⟩
      · exact ⟨n, a, by rw [hn, ordinaryHypergeometric_symm], by
          rw [hn, Gamma_neg_nat_eq_zero, mul_zero]⟩
    obtain ⟨n, b', hF, hG⟩ := hpoly
    rw [hG, div_zero]
    have hcont : Tendsto (fun x : ℝ => ₂F₁ a b (a + b) (x : ℂ)) (𝓝[<] 1)
        (𝓝 (∑ k ∈ Finset.range (n + 1), gaussHGCoeff (-(n : ℂ)) b' (a + b) k * ((1 : ℝ) : ℂ) ^ k)) := by
      rw [hF]
      simp_rw [ordinaryHypergeometric_eq_sum_neg_nat]
      refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      exact (by fun_prop : Continuous fun x : ℝ =>
        ∑ k ∈ Finset.range (n + 1), gaussHGCoeff (-(n : ℂ)) b' (a + b) k * (x : ℂ) ^ k).tendsto 1
    have := hcont.mul hL
    rw [mul_zero] at this
    exact this.congr fun x => by rw [div_eq_mul_inv, ofReal_neg]

/-- The map `(fun x : ℝ => (1 - (x : ℂ)) ^ (a + b - c) * (₂F₁ a b c (x : ℂ) - Gamma c * Gamma (c -
a - b) / (Gamma (c - a) * Gamma (c - b))))` tends to `(𝓝 (Gamma c * Gamma (a + b - c) / (Gamma
a * Gamma b)))` along `(𝓝[<] 1)`. -/
@[dlmf 15.4.E22]
theorem imaginary_excess_limit
    {a b c : ℂ}
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (h :
    (c - a - b).re = 0)
    (hne : c ≠ a + b) :
    Tendsto (fun x : ℝ => (1 - (x : ℂ)) ^ (a + b - c) *
      (₂F₁ a b c (x : ℂ) - Gamma c * Gamma (c - a - b) / (Gamma (c - a) * Gamma (c - b))))
      (𝓝[<] 1) (𝓝 (Gamma c * Gamma (a + b - c) / (Gamma a * Gamma b))) := by
  set s := c - a - b with hs
  have hs0 : s ≠ 0 := fun h0 => hne (by linear_combination h0)
  have hsint : ∀ k : ℤ, s ≠ (k : ℂ) := by
    intro k hk
    have hre := congrArg re hk
    rw [h, intCast_re] at hre
    have hk0 : k = 0 := by exact_mod_cast hre.symm
    exact hs0 (by rw [hk, hk0]; simp)
  have hsnat : ∀ k : ℕ, s ≠ -(k : ℂ) := fun k hk => hsint (-k) (by rw [hk]; push_cast; ring)
  have hsin : sin (π * s) ≠ 0 := sin_pi_mul_ne_zero_of_not_int hsint
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hre1 : ∀ w : ℂ, w.re = 1 → ∀ k : ℕ, w ≠ -(k : ℂ) := by
    intro w hw k hk
    rw [hk] at hw; simp at hw; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have h1s : ∀ k : ℕ, 1 - s ≠ -(k : ℂ) := hre1 _ (by simp [h])
  have h1s' : ∀ k : ℕ, s + 1 ≠ -(k : ℂ) := hre1 _ (by simp [h])
  have hG1s : Gamma (1 - s) ≠ 0 := Gamma_ne_zero h1s
  have hGs1 : Gamma (s + 1) ≠ 0 := Gamma_ne_zero h1s'
  have hGs : Gamma s ≠ 0 := Gamma_ne_zero hsnat
  have hGc : Gamma c ≠ 0 := Gamma_ne_zero hc
  have hrefl := Gamma_mul_Gamma_one_sub s
  have hGs1' : Gamma (s + 1) = s * Gamma s := Gamma_add_one s hs0
  have hGms : Gamma (1 - s) = -s * Gamma (-s) := by
    rw [show 1 - s = -s + 1 by ring, Gamma_add_one _ (neg_ne_zero.mpr hs0)]
  set u := (Gamma (c - a) * Gamma (c - b))⁻¹
  set v := (Gamma a * Gamma b)⁻¹
  -- the connection formula, rewritten
  have key : ∀ x : ℝ, 0 < x → x < 1 →
      (1 - (x : ℂ)) ^ (a + b - c) *
        (₂F₁ a b c (x : ℂ) - Gamma c * Gamma (c - a - b) / (Gamma (c - a) * Gamma (c - b))) =
      Gamma c * Gamma s * u * ((1 - (x : ℂ)) ^ (-s) * (₂F₁ a b (1 - s) (1 - (x : ℂ)) - 1)) +
        Gamma c * Gamma (-s) * v * ₂F₁ (c - a) (c - b) (s + 1) (1 - (x : ℂ)) := by
    intro x hx0 hx1
    have hxn : ‖(x : ℂ)‖ < 1 := by
      rw [norm_real, Real.norm_eq_abs, abs_of_pos hx0]; exact hx1
    have h1xn : ‖1 - (x : ℂ)‖ < 1 := by
      rw [show 1 - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]; linarith
    have hcon := regularized_connection_one_sub a b c hxn h1xn
    rw [regularizedGaussHGFun_eq_div_Gamma hc,
      show a + b - c + 1 = 1 - s by rw [hs]; ring, regularizedGaussHGFun_eq_div_Gamma h1s,
      show c - a - b + 1 = s + 1 by rw [hs], regularizedGaussHGFun_eq_div_Gamma h1s'] at hcon
    have hpos : (0 : ℝ) < 1 - x := by linarith
    have hq : (1 - (x : ℂ)) ^ (-s) * (1 - (x : ℂ)) ^ s = 1 := by
      have hne0 : (1 - (x : ℂ)) ≠ 0 := by
        rw [show 1 - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; ring]
        exact ofReal_ne_zero.mpr hpos.ne'
      rw [← cpow_add _ _ hne0, neg_add_cancel, cpow_zero]
    rw [show a + b - c = -s by rw [hs]; ring, show c - a - b = s from rfl,
      div_eq_mul_inv (Gamma c * Gamma s)]
    rw [div_eq_mul_inv _ (Gamma (c - a) * Gamma (c - b)), div_eq_mul_inv _ (Gamma a * Gamma b)] at hcon
    change _ = _ * u - _ * v * _ at hcon
    rw [hGs1'] at hcon
    rw [hGms] at hrefl hcon
    have hsGs : Gamma (-s) ≠ 0 := by
      intro h0; rw [h0] at hGms; simp at hGms; exact hG1s (by rw [hGms])
    rw [hGms] at hG1s
    rw [← hs] at hcon
    field_simp at hcon hrefl
    rw [show (Gamma (c - a) * Gamma (c - b))⁻¹ = u from rfl]
    apply mul_left_cancel₀ hπ
    linear_combination (-(1 - (x : ℂ)) ^ (-s)) * hcon +
      (-(1 - (x : ℂ)) ^ (-s) * ₂F₁ a b c (x : ℂ)) * hrefl +
      π * Gamma c * Gamma (-s) * v * ₂F₁ (c - a) (c - b) (s + 1) (1 - (x : ℂ)) * hq
  have hev : ∀ᶠ x : ℝ in 𝓝[<] 1, x ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
  have hq0 : Tendsto (fun x : ℝ => (1 - (x : ℂ)) ^ (-s) * (₂F₁ a b (1 - s) (1 - (x : ℂ)) - 1))
      (𝓝[<] 1) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h1 : Tendsto (fun x : ℝ => ‖₂F₁ a b (1 - s) (1 - (x : ℂ)) - 1‖) (𝓝[<] 1) (𝓝 0) := by
      have := (tendsto_ordinaryHypergeometric_one_sub_left a b (1 - s)).sub_const 1
      rw [sub_self] at this
      simpa using this.norm
    refine h1.congr' ?_
    filter_upwards [hev] with x hx
    rw [norm_mul, show 1 - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; ring,
      norm_cpow_eq_rpow_re_of_pos (by linarith [hx.2]), neg_re, h, neg_zero, Real.rpow_zero,
      one_mul]
  have hlim := ((hq0.const_mul (Gamma c * Gamma s * u)).add
    ((tendsto_ordinaryHypergeometric_one_sub_left (c - a) (c - b) (s + 1)).const_mul
      (Gamma c * Gamma (-s) * v)))
  rw [mul_zero, zero_add, mul_one] at hlim
  rw [show Gamma c * Gamma (a + b - c) / (Gamma a * Gamma b) = Gamma c * Gamma (-s) * v by
    rw [show a + b - c = -s by rw [hs]; ring]; rfl]
  refine hlim.congr' ?_
  filter_upwards [hev] with x hx
  exact (key x hx.1 hx.2).symm

/-- The map `(fun c : ℂ => Filter.limUnder (𝓝[≠] (-(m : ℂ))) (fun a => ₂F₁ a b c z))` tends to `(𝓝
(₂F₁ (-m : ℂ) b (-(m : ℂ) - l) z))` along `(𝓝[≠] (-(m : ℂ) - l))`. -/
@[dlmf 15.2.E5]
theorem terminating_iterated_parameter_limit (b : ℂ) (m l : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    Tendsto (fun c : ℂ => Filter.limUnder (𝓝[≠] (-(m : ℂ))) (fun a => ₂F₁ a b c z))
      (𝓝[≠] (-(m : ℂ) - l)) (𝓝 (₂F₁ (-m : ℂ) b (-(m : ℂ) - l) z)) := by
  -- the inner limit is the value at `a = -m`, by continuity in `a` off the poles of `Γ(c)`
  have hlim : ∀ c : ℂ, (∀ k : ℕ, c ≠ -(k : ℂ)) →
      Filter.limUnder (𝓝[≠] (-(m : ℂ))) (fun a => ₂F₁ a b c z) = ₂F₁ (-(m : ℂ)) b c z := by
    intro c hc
    apply Filter.Tendsto.limUnder_eq
    have hfun : (fun a => ₂F₁ a b c z) = fun a => Gamma c * regularizedGaussHGFun a b c z := by
      funext a
      rw [regularizedGaussHGFun_eq_div_Gamma hc, mul_div_cancel₀ _ (Gamma_ne_zero hc)]
    have hcont : ContinuousAt (fun a => ₂F₁ a b c z) (-(m : ℂ)) := by
      rw [hfun]
      exact continuousAt_const.mul
        ((analyticOnNhd_regularizedGaussHGFun_a b c hz) _ (Set.mem_univ _)).continuousAt
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  -- the outer limit, by continuity of the terminating series in `c` at `c = -m-l`
  have hmem : (-(m : ℂ) - l) ∈ {c : ℂ | ∀ j : ℕ, j < m → c ≠ -(j : ℂ)} := fun j hj h => by
    have : ((m + l : ℕ) : ℂ) = j := by push_cast; linear_combination -h
    have : m + l = j := by exact_mod_cast this
    omega
  have hcont2 : ContinuousAt (fun c => ₂F₁ (-(m : ℂ)) b c z) (-(m : ℂ) - l) :=
    ((analyticOnNhd_gauss_neg_nat_param m b z) _ hmem).continuousAt
  refine (hcont2.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  have hev := eventually_nhdsWithin_ne_neg_nat (m + l)
  rw [show -((m + l : ℕ) : ℂ) = -(m : ℂ) - l by push_cast; ring] at hev
  filter_upwards [hev] with c hc
  exact (hlim c hc).symm

/-- The diagonal limit has a different coefficient ratio from the terminating convention E5. -/
@[dlmf 15.2.E6]
theorem diagonal_parameter_limit (b : ℂ) (m l : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    Tendsto (fun a : ℂ => ₂F₁ a b (a - l) z) (𝓝[≠] (-(m : ℂ)))
      (𝓝 (∑' k : ℕ, poch (-(m : ℂ) - l + k) l * poch b k /
        (poch (-(m : ℂ) - l) l * (k.factorial : ℂ)) * z ^ k)) := by
  set T : ℂ → ℕ → ℂ := fun a k => poch (a - l + k) l * poch b k /
    (poch (a - l) l * (k.factorial : ℂ)) * z ^ k with hT
  have hP0 : poch (-(m : ℂ) - l) l ≠ 0 := by
    apply poch_ne_zero_of_lt
    intro j hj h
    have : ((m + l : ℕ) : ℂ) = j := by push_cast; linear_combination -h
    have : m + l = j := by exact_mod_cast this
    omega
  have hPc : Continuous fun a : ℂ => poch (a - l) l :=
    ((Polynomial.differentiable (ascPochhammer ℂ l)).comp (differentiable_id.sub_const _)).continuous
  set δ := ‖poch (-(m : ℂ) - l) l‖ / 2 with hδ
  have hδ0 : 0 < δ := by have := norm_pos_iff.mpr hP0; positivity
  -- eventual properties near `-m`
  have hev1 : ∀ᶠ a in 𝓝[≠] (-(m : ℂ)), ∀ j : ℕ, a - l ≠ -(j : ℂ) := by
    have h2 : ∀ᶠ a in 𝓝[≠] (-(m : ℂ)), dist a (-(m : ℂ)) < 1 / 2 :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds _ (by norm_num))
    filter_upwards [h2, self_mem_nhdsWithin] with a ha hne j hj
    have ha' : a = (((l : ℤ) - j : ℤ) : ℂ) := by push_cast; linear_combination hj
    rw [dist_eq_norm, ha', show (((l : ℤ) - j : ℤ) : ℂ) - -(m : ℂ) = (((l : ℤ) - j + m : ℤ) : ℂ) by
      push_cast; ring, Complex.norm_intCast] at ha
    have h0 : (l : ℤ) - j + m = 0 := by
      by_contra h0
      have := Int.one_le_abs h0
      have : (1 : ℝ) ≤ |(((l : ℤ) - j + m : ℤ) : ℝ)| := by exact_mod_cast this
      linarith
    apply hne
    rw [ha']
    simp only [Set.mem_singleton_iff]
    have : (l : ℤ) - j = -m := by linarith
    rw [this]; push_cast; ring
  have hev2 : ∀ᶠ a in 𝓝[≠] (-(m : ℂ)), ‖a‖ ≤ m + 1 := by
    have h2 : ∀ᶠ a in 𝓝[≠] (-(m : ℂ)), dist a (-(m : ℂ)) < 1 :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds _ (by norm_num))
    filter_upwards [h2] with a ha
    rw [dist_eq_norm] at ha
    calc ‖a‖ = ‖(a - -(m : ℂ)) + -(m : ℂ)‖ := by ring_nf
      _ ≤ ‖a - -(m : ℂ)‖ + ‖-(m : ℂ)‖ := norm_add_le _ _
      _ ≤ 1 + m := by rw [norm_neg, Complex.norm_natCast]; linarith
      _ = m + 1 := by ring
  have hev3 : ∀ᶠ a in 𝓝[≠] (-(m : ℂ)), δ < ‖poch (a - l) l‖ :=
    nhdsWithin_le_nhds (hPc.norm.continuousAt.eventually
      (lt_mem_nhds (half_lt_self (norm_pos_iff.mpr hP0))))
  -- the series for `a` near `-m`
  have hser : ∀ᶠ a in 𝓝[≠] (-(m : ℂ)), ₂F₁ a b (a - l) z = ∑' k, T a k := by
    filter_upwards [hev1] with a ha
    rw [ordinaryHypergeometric_eq_tsum]
    simp only [smul_eq_mul]
    congr 1
    funext k
    have hk : poch (a - l) k ≠ 0 := poch_ne_zero_of_not_neg_nat ha k
    have hl : poch (a - l) l ≠ 0 := poch_ne_zero_of_not_neg_nat ha l
    have hf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have e1 := poch_add (a - l) l k
    have e2 := poch_add (a - l) k l
    rw [show a - l + l = a by ring, add_comm l k] at e1
    simp only [hT]
    rw [show (ascPochhammer ℂ k).eval a = poch a k from rfl,
      show (ascPochhammer ℂ k).eval b = poch b k from rfl,
      show (ascPochhammer ℂ k).eval (a - l) = poch (a - l) k from rfl]
    field_simp
    linear_combination (-(poch b k * z ^ k)) * (e2.symm.trans e1)
  set R : ℝ := m + 1 + l with hR
  have hR0 : 0 < R := by positivity
  have hRne : ∀ j : ℕ, (R : ℂ) ≠ -(j : ℂ) := by
    intro j h
    have := congrArg re h
    simp at this
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hshift : ∀ k : ℕ, ‖poch ((R + k : ℝ) : ℂ) l‖ =
      ‖poch (R : ℂ) l‖ * ‖poch ((R + l : ℝ) : ℂ) k‖ / ‖poch (R : ℂ) k‖ := by
    intro k
    have hk := norm_pos_iff.mpr (poch_ne_zero_of_not_neg_nat hRne k)
    have e1 := poch_add (R : ℂ) k l
    have e2 := poch_add (R : ℂ) l k
    rw [add_comm l k, e1] at e2
    rw [eq_div_iff hk.ne', ← norm_mul, ← norm_mul,
      show ((R + k : ℝ) : ℂ) = (R : ℂ) + k by push_cast; ring,
      show ((R + l : ℝ) : ℂ) = (R : ℂ) + l by push_cast; ring, mul_comm, ← e2]
  set bound : ℕ → ℝ := fun k => δ⁻¹ * (‖poch (R : ℂ) l‖ *
    ‖gaussHGCoeff ((R + l : ℝ) : ℂ) (‖b‖ : ℂ) (R : ℂ) k * z ^ k‖) with hbound
  have hsum : Summable bound :=
    ((summable_norm_gaussHGCoeff_mul_pow _ _ _ hz).mul_left _).mul_left _
  have hdom : ∀ᶠ a in 𝓝[≠] (-(m : ℂ)), ∀ k, ‖T a k‖ ≤ bound k := by
    filter_upwards [hev2, hev3] with a ha2 ha3 k
    have hk := norm_pos_iff.mpr (poch_ne_zero_of_not_neg_nat hRne k)
    have hf : (0 : ℝ) < k.factorial := by positivity
    have h1 : ‖poch (a - l + k) l‖ ≤ ‖poch ((R + k : ℝ) : ℂ) l‖ := by
      apply norm_ascPochhammer_eval_le
      calc ‖a - l + k‖ ≤ ‖a‖ + l + k := by
            refine (norm_add_le _ _).trans ?_
            rw [Complex.norm_natCast]
            gcongr
            refine (norm_sub_le _ _).trans ?_
            rw [Complex.norm_natCast]
        _ ≤ R + k := by rw [hR]; linarith
    have h2 : ‖poch b k‖ ≤ ‖poch (‖b‖ : ℂ) k‖ := norm_ascPochhammer_eval_le le_rfl k
    simp only [hT, hbound, gaussHGCoeff]
    simp only [norm_mul, norm_div, Complex.norm_natCast]
    have h3 : ‖poch (a - l + k) l‖ * ‖poch b k‖ / (‖poch (a - l) l‖ * k.factorial) ≤
        δ⁻¹ * (‖poch ((R + k : ℝ) : ℂ) l‖ * ‖poch (‖b‖ : ℂ) k‖ / k.factorial) := by
      rw [div_le_iff₀ (mul_pos (hδ0.trans ha3) hf)]
      calc ‖poch (a - l + k) l‖ * ‖poch b k‖ ≤ ‖poch ((R + k : ℝ) : ℂ) l‖ * ‖poch (‖b‖ : ℂ) k‖ :=
            mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
        _ = δ⁻¹ * (‖poch ((R + k : ℝ) : ℂ) l‖ * ‖poch (‖b‖ : ℂ) k‖ / k.factorial) *
              (δ * k.factorial) := by field_simp
        _ ≤ _ := by gcongr
    rw [hshift k] at h3
    calc ‖poch (a - l + k) l‖ * ‖poch b k‖ / (‖poch (a - l) l‖ * k.factorial) * ‖z ^ k‖
        ≤ δ⁻¹ * (‖poch (R : ℂ) l‖ * ‖poch ((R + l : ℝ) : ℂ) k‖ / ‖poch (R : ℂ) k‖ *
            ‖poch (‖b‖ : ℂ) k‖ / k.factorial) * ‖z ^ k‖ := by gcongr
      _ = _ := by push_cast; field_simp
  have hpt : ∀ k, Tendsto (fun a => T a k) (𝓝[≠] (-(m : ℂ))) (𝓝 (T (-(m : ℂ)) k)) := by
    intro k
    have hc1 : Continuous fun a : ℂ => poch (a - l + k) l :=
      ((Polynomial.differentiable (ascPochhammer ℂ l)).comp
        ((differentiable_id.sub_const _).add_const _)).continuous
    have hca : ContinuousAt (fun a => T a k) (-(m : ℂ)) := by
      simp only [hT]
      refine ((hc1.continuousAt.mul continuousAt_const).div
        (hPc.continuousAt.mul continuousAt_const) ?_).mul continuousAt_const
      exact mul_ne_zero hP0 (Nat.cast_ne_zero.mpr k.factorial_ne_zero)
    exact hca.tendsto.mono_left nhdsWithin_le_nhds
  exact (tendsto_tsum_of_dominated_convergence hsum hpt hdom).congr' (hser.mono fun a h => h.symm)

end DLMF.Hypergeometric
