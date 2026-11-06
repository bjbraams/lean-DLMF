/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.SearsLimit
public import DLMF.QHypergeometric.FiniteBilateralTransformations
public import DLMFMathlib.Analysis.SpecificLimits.PowMulPowChoose
public import DLMFMathlib.Topology.Algebra.InfiniteSum.Int

/-!
# Gaussian bilateral transformations

The bilateral Watson transformation has a Gaussian limit. The two halves of its
four-psi-four series are controlled by geometric majorants; the moving ratios are
those of the terminating Sears limit. Gaussian majorants control the eight-psi-eight.
-/

@[expose] public noncomputable section

open Complex Filter Finset
open scoped Topology
open DLMF.QSeries

namespace DLMF.QHypergeometric.BilateralGaussian

/-- The natural-index half of the finite four-psi-four, with its moving ratio normalized. -/
def fourPositiveTerm (a b c d w z q : ℂ) (N k : ℕ) : ℂ :=
  SearsLimit.coefficient a b q c d q k * SearsLimit.ratio z q N k *
    qPochhammer (w * q ^ N) q k / qPochhammer (q * q ^ N) q k

/-- For fixed index the moving finite four-psi-four term approaches its bilateral-series term.
-/
lemma tendsto_fourPositiveTerm {q : ℂ} (hq : ‖q‖ < 1) (a b c d w z : ℂ) (k : ℕ) :
    Tendsto (fun N => fourPositiveTerm a b c d w z q N k) atTop
      (𝓝 (SearsLimit.coefficient a b q c d q k * z ^ k)) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq
  have hw : Tendsto (fun N : ℕ => w * q ^ N) atTop (𝓝 (0 : ℂ)) := by
    simpa only [mul_zero] using hp.const_mul w
  have hq' : Tendsto (fun N : ℕ => q * q ^ N) atTop (𝓝 (0 : ℂ)) := by
    simpa only [mul_zero] using hp.const_mul q
  have hnum := (continuous_qPochhammer q k).tendsto 0 |>.comp hw
  have hden := (continuous_qPochhammer q k).tendsto 0 |>.comp hq'
  simp only [qPochhammer_zero_param] at hnum hden
  have H := ((tendsto_const_nhds (x := SearsLimit.coefficient a b q c d q k)).mul
    (SearsLimit.tendsto_ratio (z := z) hq k)).mul (hnum.div hden one_ne_zero)
  simpa only [fourPositiveTerm, one_div_one, mul_one, Function.comp_def, Pi.div_apply,
    div_eq_mul_inv, inv_one, mul_assoc] using H

/-- The finite four-psi-four terms have a geometric majorant uniform in the truncation. -/
lemma exists_norm_fourPositiveTerm_le {a b c d w z q : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1)
    (hcd : QDenominatorRegular [c, d] q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N k : ℕ,
      ‖fourPositiveTerm a b c d w z q N k‖ ≤ C * ‖z‖ ^ k := by
  obtain ⟨A, hA0, hA⟩ := SearsLimit.exists_norm_coefficient_le
    (a := a) (b := b) (c := q) hq hcd
  obtain ⟨B, hB0, hB⟩ := SearsLimit.exists_norm_ratio_le hq hz
  obtain ⟨D, hD0, hD⟩ := SearsLimit.exists_norm_inv_qPochhammer_shift_le hq hq
  let E := Real.exp (‖w‖ / (1 - ‖q‖))
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hE (N k : ℕ) : ‖qPochhammer (w * q ^ N) q k‖ ≤ E := by
    refine (norm_qPochhammer_le_exp hq k).trans (Real.exp_le_exp.mpr ?_)
    apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hq.le)
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg q) hq.le)
  refine ⟨A * B * E * D, by positivity, ?_⟩
  intro N k
  simp only [fourPositiveTerm, div_eq_mul_inv, norm_mul]
  have H := mul_le_mul
    (mul_le_mul (mul_le_mul (hA k) (hB N k) (norm_nonneg _) hA0)
      (hE N k) (norm_nonneg _) (by positivity))
    (hD N k) (norm_nonneg _) (by positivity)
  exact H.trans_eq (by ring)

/-- Dominated convergence gives the natural-index limit of the finite four-psi-four series.
-/
lemma tendsto_tsum_fourPositiveTerm {a b c d w z q : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1)
    (hcd : QDenominatorRegular [c, d] q) :
    Tendsto (fun N => ∑' k, fourPositiveTerm a b c d w z q N k) atTop
      (𝓝 (qPhi [a, b, q] [c, d] q z)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_fourPositiveTerm_le
    (a := a) (b := b) (w := w) hq hz hcd
  have H := tendsto_tsum_of_dominated_convergence
    ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left C)
    (tendsto_fourPositiveTerm hq a b c d w z)
    (Eventually.of_forall fun N k => hC N k)
  simpa only [← SearsLimit.qPhi_eq_tsum] using H

/-- The normalized natural-index term equals the corresponding terminating four-psi-four term.
-/
lemma qPsiTerm_natCast_eq_fourPositiveTerm {a b c d w z q : ℂ} (hz0 : z ≠ 0)
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (N k : ℕ) :
    qPsiTerm [q ^ (-(N : ℤ)), a, b, w * q ^ N]
      [q ^ (N + 1), c, d, SearsLimit.movingParameter z q N] q q (k : ℤ) =
      fourPositiveTerm a b c d w z q N k := by
  by_cases hk : k ≤ N
  · have H := SearsLimit.ratio_eq (z := z) hz0 hq0 hk
    rw [show q⁻¹ ^ N = q ^ (-(N : ℤ)) by
      simp only [zpow_neg, zpow_natCast, inv_pow]] at H
    have hQ := qPochhammer_self_ne_zero hq k
    have he : qPsiExponent [q ^ (-(N : ℤ)), a, b, w * q ^ N]
        [q ^ (N + 1), c, d, SearsLimit.movingParameter z q N] = 0 := by simp [qPsiExponent]
    rw [fourPositiveTerm, H]
    simp only [qPsiTerm, he, zpow_zero, mul_one, qPochhammerListInt_natCast,
      qPochhammerList, SearsLimit.coefficient, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, zpow_natCast]
    rw [show q ^ (N + 1) = q * q ^ N by rw [pow_succ]; ring]
    field_simp [hQ]
  · have hzero : qPochhammer (q ^ (-(N : ℤ))) q k = 0 := by
      simpa only [zpow_neg, zpow_natCast] using
        qPochhammer_recip_pow_eq_zero hq0 (Nat.lt_of_not_ge hk)
    simp only [qPsiTerm, qPochhammerListInt_natCast, qPochhammerList,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      hzero, zero_mul, zero_div, fourPositiveTerm, SearsLimit.ratio, ite_eq_right hk]
    ring

/-- The coefficient of the Gaussian four-parameter bilateral summation at a natural index.
-/
def gaussianCoefficient (a c d e f q : ℂ) (k : ℕ) : ℂ :=
  (1 - a * q ^ (2 * k)) / (1 - a) * qPochhammerList [c, d, e, f] q k /
    qPochhammerList [a * q / c, a * q / d, a * q / e, a * q / f] q k

/-- The natural-index half of the finite eight-psi-eight after reversing its two moving uppers.
-/
def eightPositiveTerm (a c d e f q : ℂ) (N k : ℕ) : ℂ :=
  if k ≤ N then
    gaussianCoefficient a c d e f q k * (q * a ^ 3 / (c * d * e * f)) ^ k * q ^ (k * k) *
      (qPochhammer (q ^ (N + 1 - k) / a) q k * qPochhammer (q ^ (N + 1 - k)) q k) /
      (qPochhammer (q ^ (N + 1)) q k * qPochhammer (a * q ^ (N + 1)) q k)
  else 0

/-- Each natural-index eight-psi-eight term approaches its Gaussian limit. -/
lemma tendsto_eightPositiveTerm {q : ℂ} (hq : ‖q‖ < 1) (a c d e f : ℂ) (k : ℕ) :
    Tendsto (fun N => eightPositiveTerm a c d e f q N k) atTop
      (𝓝 (gaussianCoefficient a c d e f q k *
        (q * a ^ 3 / (c * d * e * f)) ^ k * q ^ (k * k))) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq
  have hsub : Tendsto (fun N : ℕ => q ^ (N - k)) atTop (𝓝 (0 : ℂ)) := by
    simpa only [Function.comp_def] using hp.comp (tendsto_sub_atTop_nat k)
  have hs : Tendsto (fun N : ℕ => q ^ (N + 1 - k)) atTop (𝓝 (0 : ℂ)) := by
    have H := hsub.mul_const q
    simp only [zero_mul] at H
    apply H.congr'
    filter_upwards [eventually_ge_atTop k] with N hN
    rw [show N + 1 - k = N - k + 1 by omega, pow_succ]
  have hnext : Tendsto (fun N : ℕ => q ^ (N + 1)) atTop (𝓝 (0 : ℂ)) := by
    simpa only [pow_succ, zero_mul] using hp.mul_const q
  have hsdiv : Tendsto (fun N : ℕ => q ^ (N + 1 - k) / a) atTop (𝓝 (0 : ℂ)) := by
    simpa only [zero_div] using hs.div_const a
  have hanext : Tendsto (fun N : ℕ => a * q ^ (N + 1)) atTop (𝓝 (0 : ℂ)) := by
    simpa only [mul_zero] using hnext.const_mul a
  have h1 := (continuous_qPochhammer q k).tendsto 0 |>.comp hsdiv
  have h2 := (continuous_qPochhammer q k).tendsto 0 |>.comp hs
  have h3 := (continuous_qPochhammer q k).tendsto 0 |>.comp hnext
  have h4 := (continuous_qPochhammer q k).tendsto 0 |>.comp hanext
  simp only [qPochhammer_zero_param] at h1 h2 h3 h4
  have H := (tendsto_const_nhds (x := gaussianCoefficient a c d e f q k *
    (q * a ^ 3 / (c * d * e * f)) ^ k * q ^ (k * k))).mul
    ((h1.mul h2).div (h3.mul h4) (by simp))
  simp only [div_one, mul_one] at H
  apply H.congr'
  filter_upwards [eventually_ge_atTop k] with N hN
  simp only [eightPositiveTerm, ite_eq_left hN, Function.comp_def, Pi.div_apply]
  ring

/-- The fixed Gaussian coefficients are bounded throughout the natural indices. -/
lemma exists_norm_gaussianCoefficient_le {a c d e f q : ℂ} (hq : ‖q‖ < 1)
    (hden : QDenominatorRegular [a * q / c, a * q / d, a * q / e, a * q / f] q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, ‖gaussianCoefficient a c d e f q k‖ ≤ C := by
  obtain ⟨B, hB0, hB⟩ := FiniteBilateral.exists_norm_qPochhammerList_ratio_le
    [c, d, e, f] hq hden
  have hq2 : ‖q ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg q]
  have hp : Tendsto (fun k : ℕ => q ^ (2 * k)) atTop (𝓝 (0 : ℂ)) := by
    simpa only [pow_mul] using tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq2
  have H := ((tendsto_const_nhds (x := (1 : ℂ))).sub (hp.const_mul a)).div_const (1 - a)
  obtain ⟨A, hA⟩ := H.norm.bddAbove_range
  have hbound (k : ℕ) : ‖(1 - a * q ^ (2 * k)) / (1 - a)‖ ≤ A := hA ⟨k, rfl⟩
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hbound 0)
  refine ⟨A * B, by positivity, fun k => ?_⟩
  rw [gaussianCoefficient, mul_div_assoc, norm_mul]
  exact mul_le_mul (hbound k) (hB k) (norm_nonneg _) hA0

/-- A natural q-shift does not enlarge the exponential finite-product bound. -/
lemma norm_qPochhammer_mul_pow_le {q : ℂ} (hq : ‖q‖ < 1) (w : ℂ) (M k : ℕ) :
    ‖qPochhammer (w * q ^ M) q k‖ ≤ Real.exp (‖w‖ / (1 - ‖q‖)) := by
  refine (norm_qPochhammer_le_exp hq k).trans (Real.exp_le_exp.mpr ?_)
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hq.le)
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg q) hq.le)

/-- The natural-index finite eight-psi-eight terms have a uniform Gaussian majorant. -/
lemma exists_norm_eightPositiveTerm_le {a c d e f q : ℂ} (hq : ‖q‖ < 1)
    (haq : qPochhammerInf (a * q) q ≠ 0)
    (hden : QDenominatorRegular [a * q / c, a * q / d, a * q / e, a * q / f] q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N k : ℕ, ‖eightPositiveTerm a c d e f q N k‖ ≤
      C * (‖q * a ^ 3 / (c * d * e * f)‖ ^ k * ‖q‖ ^ k.choose 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_gaussianCoefficient_le hq hden
  obtain ⟨B, hB0, hB⟩ := SearsLimit.exists_norm_inv_qPochhammer_shift_le hq hq
  obtain ⟨D, hD0, hD⟩ := FiniteBilateral.exists_norm_inv_qPochhammer_shift_le hq haq
  let E1 := Real.exp (‖a⁻¹‖ / (1 - ‖q‖))
  let E2 := Real.exp (1 / (1 - ‖q‖))
  have hE10 : 0 ≤ E1 := (Real.exp_pos _).le
  have hE20 : 0 ≤ E2 := (Real.exp_pos _).le
  refine ⟨C * E1 * E2 * B * D, by positivity, ?_⟩
  intro N k
  by_cases hk : k ≤ N
  · have h1 : ‖qPochhammer (q ^ (N + 1 - k) / a) q k‖ ≤ E1 := by
      rw [show q ^ (N + 1 - k) / a = a⁻¹ * q ^ (N + 1 - k) by ring]
      exact norm_qPochhammer_mul_pow_le hq a⁻¹ (N + 1 - k) k
    have h2 : ‖qPochhammer (q ^ (N + 1 - k)) q k‖ ≤ E2 := by
      simpa only [one_mul, norm_one] using
        norm_qPochhammer_mul_pow_le hq 1 (N + 1 - k) k
    have h3 : ‖(qPochhammer (q ^ (N + 1)) q k)⁻¹‖ ≤ B := by
      rw [show q ^ (N + 1) = q * q ^ N by rw [pow_succ]; ring]
      exact hB N k
    have h4 : ‖(qPochhammer (a * q ^ (N + 1)) q k)⁻¹‖ ≤ D := by
      rw [show a * q ^ (N + 1) = (a * q) * q ^ N by rw [pow_succ]; ring]
      exact hD N k
    have hmove : ‖(qPochhammer (q ^ (N + 1 - k) / a) q k *
        qPochhammer (q ^ (N + 1 - k)) q k) /
        (qPochhammer (q ^ (N + 1)) q k * qPochhammer (a * q ^ (N + 1)) q k)‖ ≤
        (E1 * E2) * (B * D) := by
      have hnum := mul_le_mul h1 h2 (norm_nonneg _) hE10
      have hdiv := mul_le_mul h3 h4 (norm_nonneg _) hB0
      have H := mul_le_mul hnum hdiv (by positivity) (by positivity)
      simpa only [div_eq_mul_inv, mul_inv_rev, norm_mul, mul_assoc,
        mul_left_comm, mul_comm] using H
    have hweight : ‖gaussianCoefficient a c d e f q k *
        (q * a ^ 3 / (c * d * e * f)) ^ k * q ^ (k * k)‖ ≤
        C * ‖q * a ^ 3 / (c * d * e * f)‖ ^ k * ‖q‖ ^ (k * k) := by
      simp only [norm_mul, norm_pow]
      gcongr
      exact hC k
    have hchoose : k.choose 2 ≤ k * k := by
      have H := choose_two_mul_two_add_self k
      nlinarith
    rw [eightPositiveTerm, ite_eq_left hk, mul_div_assoc, norm_mul]
    calc
      _ ≤ (C * ‖q * a ^ 3 / (c * d * e * f)‖ ^ k * ‖q‖ ^ (k * k)) *
          ((E1 * E2) * (B * D)) := mul_le_mul hweight hmove (norm_nonneg _) (by positivity)
      _ ≤ (C * ‖q * a ^ 3 / (c * d * e * f)‖ ^ k * ‖q‖ ^ k.choose 2) *
          ((E1 * E2) * (B * D)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one (norm_nonneg q) hq.le hchoose) (by positivity)) (by positivity)
      _ = _ := by ring
  · simp only [eightPositiveTerm, ite_eq_right hk, norm_zero]
    positivity

/-- Dominated convergence gives the Gaussian limit of the natural-index eight-psi-eight half.
-/
lemma tendsto_tsum_eightPositiveTerm {a c d e f q : ℂ} (hq : ‖q‖ < 1)
    (haq : qPochhammerInf (a * q) q ≠ 0)
    (hden : QDenominatorRegular [a * q / c, a * q / d, a * q / e, a * q / f] q) :
    Tendsto (fun N => ∑' k, eightPositiveTerm a c d e f q N k) atTop
      (𝓝 (∑' k, gaussianCoefficient a c d e f q k *
        (q * a ^ 3 / (c * d * e * f)) ^ k * q ^ (k * k))) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_eightPositiveTerm_le hq haq hden
  exact tendsto_tsum_of_dominated_convergence
    ((summable_pow_mul_pow_choose_two (norm_nonneg _) (norm_nonneg q) hq).mul_left C)
    (tendsto_eightPositiveTerm hq a c d e f)
    (Eventually.of_forall fun N k => hC N k)

/-- Reversing the two moving upper products gives the Gaussian normalization of each finite
natural-index eight-psi-eight term. -/
lemma qPsiTerm_natCast_eq_eightPositiveTerm {a r c d e f q : ℂ} (hr : r ^ 2 = a)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (hc0 : c ≠ 0) (hd0 : d ≠ 0)
    (he0 : e ≠ 0) (hf0 : f ≠ 0) (hq0 : q ≠ 0) (N k : ℕ)
    (hroot : qPochhammer r q N * qPochhammer (-r) q N ≠ 0) :
    qPsiTerm [q ^ (-(N : ℤ)), q * r, -q * r, c, d, e, f, a / q ^ N]
      [q ^ (N + 1), r, -r, a * q / c, a * q / d, a * q / e, a * q / f,
        a * q * q ^ N] q (a ^ 2 * q ^ 2 * (q ^ N) ^ 2 / (c * d * e * f)) (k : ℤ) =
      eightPositiveTerm a c d e f q N k := by
  by_cases hk : k ≤ N
  · have ht := pow_ne_zero N hq0
    have hrootk : qPochhammer r q k * qPochhammer (-r) q k ≠ 0 :=
      mul_ne_zero (qPochhammer_ne_zero_of_le (left_ne_zero_of_mul hroot) hk)
        (qPochhammer_ne_zero_of_le (right_ne_zero_of_mul hroot) hk)
    have hA1 : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
    have hS := DLMF.Bailey.qPochhammer_sqrt_factor (q := q) hr k
    have hR : qPochhammer (q * r) q k * qPochhammer (-q * r) q k /
        (qPochhammer r q k * qPochhammer (-r) q k) = (1 - a * q ^ (2 * k)) / (1 - a) :=
      (div_eq_div_iff hrootk hA1).mpr (by linear_combination hS)
    have hNk : q ^ (N - k) * q ^ k = q ^ N := by rw [← pow_add, Nat.sub_add_cancel hk]
    have harg : q * q⁻¹ ^ k / (1 / q ^ N) = q ^ (N + 1 - k) := by
      rw [show N + 1 - k = N - k + 1 by omega, pow_succ]
      simp only [inv_pow]
      field_simp
      linear_combination -hNk
    have hargA : q * q⁻¹ ^ k / (a / q ^ N) = q ^ (N + 1 - k) / a := by
      rw [show q * q⁻¹ ^ k / (a / q ^ N) = (q * q⁻¹ ^ k / (1 / q ^ N)) / a by field_simp,
        harg]
    have hA := SearsTransformation.qPochhammer_reverse' (div_ne_zero ha0 ht) hq0 k
    have hQ := SearsTransformation.qPochhammer_reverse' (one_div_ne_zero ht) hq0 k
    rw [hargA] at hA
    rw [harg] at hQ
    have hscalar : (-a / q ^ N) * (-1 / q ^ N) *
        (a ^ 2 * q ^ 2 * (q ^ N) ^ 2 / (c * d * e * f)) =
          (q * a ^ 3 / (c * d * e * f)) * q := by field_simp
    have hpower : (-a / q ^ N) ^ k * (-1 / q ^ N) ^ k *
        q ^ k.choose 2 * q ^ k.choose 2 *
        (a ^ 2 * q ^ 2 * (q ^ N) ^ 2 / (c * d * e * f)) ^ k =
        (q * a ^ 3 / (c * d * e * f)) ^ k * q ^ (k * k) := by
      calc
        _ = ((-a / q ^ N) * (-1 / q ^ N) *
            (a ^ 2 * q ^ 2 * (q ^ N) ^ 2 / (c * d * e * f))) ^ k *
            q ^ (k.choose 2 + k.choose 2) := by rw [mul_pow, mul_pow, pow_add]; ring
        _ = _ := by
          rw [hscalar, mul_pow, mul_assoc, ← pow_add]
          congr 1
          have H := choose_two_mul_two_add_self k
          congr 1
          omega
    have he : qPsiExponent
        [q ^ (-(N : ℤ)), q * r, -q * r, c, d, e, f, a / q ^ N]
        [q ^ (N + 1), r, -r, a * q / c, a * q / d, a * q / e, a * q / f,
          a * q * q ^ N] = 0 := by simp [qPsiExponent]
    have Hfirst : qPsiTerm
        [q ^ (-(N : ℤ)), q * r, -q * r, c, d, e, f, a / q ^ N]
        [q ^ (N + 1), r, -r, a * q / c, a * q / d, a * q / e, a * q / f,
          a * q * q ^ N] q (a ^ 2 * q ^ 2 * (q ^ N) ^ 2 / (c * d * e * f)) (k : ℤ) =
        gaussianCoefficient a c d e f q k *
          (qPochhammer (a / q ^ N) q k * qPochhammer (1 / q ^ N) q k) *
          (a ^ 2 * q ^ 2 * (q ^ N) ^ 2 / (c * d * e * f)) ^ k /
          (qPochhammer (q ^ (N + 1)) q k * qPochhammer (a * q ^ (N + 1)) q k) := by
      rw [gaussianCoefficient, ← hR]
      simp only [qPsiTerm, he, zpow_zero, mul_one, qPochhammerListInt_natCast,
        qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        zpow_natCast, show a * q ^ (N + 1) = a * q * q ^ N by rw [pow_succ]; ring]
      rw [show q ^ (-(N : ℤ)) = 1 / q ^ N by simp [zpow_neg, zpow_natCast]]
      ring
    rw [Hfirst, eightPositiveTerm, ite_eq_left hk, hA, hQ]
    simp only [neg_div] at hpower ⊢
    linear_combination (gaussianCoefficient a c d e f q k *
      qPochhammer (q ^ (N + 1 - k) / a) q k * qPochhammer (q ^ (N + 1 - k)) q k /
      (qPochhammer (q ^ (N + 1)) q k * qPochhammer (a * q ^ (N + 1)) q k)) * hpower
  · have hzero : qPochhammer (q ^ (-(N : ℤ))) q k = 0 := by
      simpa only [zpow_neg, zpow_natCast] using
        qPochhammer_recip_pow_eq_zero hq0 (Nat.lt_of_not_ge hk)
    simp only [qPsiTerm, qPochhammerListInt_natCast, qPochhammerList,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, hzero,
      zero_mul, zero_div, eightPositiveTerm, ite_eq_right hk]

/-- Each finite natural-index four-psi-four half is summable under its geometric majorant. -/
lemma summable_fourPositiveTerm {a b c d w z q : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1)
    (hcd : QDenominatorRegular [c, d] q) (N : ℕ) :
    Summable (fun k => fourPositiveTerm a b c d w z q N k) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_fourPositiveTerm_le
    (a := a) (b := b) (w := w) hq hz hcd
  exact Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hC N)
    ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left C))

/-- The normalized zero-index four-psi-four term is one. -/
@[simp] lemma fourPositiveTerm_zero (a b c d w z q : ℂ) (N : ℕ) :
    fourPositiveTerm a b c d w z q N 0 = 1 := by
  simp [fourPositiveTerm, SearsLimit.coefficient, SearsLimit.ratio]

/-- Reflecting the balanced finite four-psi-four interchanges its two geometric arguments.
-/
lemma qPsiTerm_neg_natCast_eq_fourPositiveTerm {a b c d w z q : ℂ}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0) (hd0 : d ≠ 0)
    (hw0 : w ≠ 0) (hz0 : z ≠ 0) (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hbal : c * d = a * b * w * z) (N k : ℕ) :
    qPsiTerm [q ^ (-(N : ℤ)), a, b, w * q ^ N]
      [q ^ (N + 1), c, d, SearsLimit.movingParameter z q N] q q (-(k : ℤ)) =
      fourPositiveTerm (q / c) (q / d) (q / a) (q / b) z w q N k := by
  have ht := pow_ne_zero N hq0
  have hU : ∀ x ∈ [q ^ (-(N : ℤ)), a, b, w * q ^ N], x ≠ 0 := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [ha0, hb0, hw0, hq0]
  have hL : ∀ x ∈ [q ^ (N + 1), c, d, SearsLimit.movingParameter z q N], x ≠ 0 := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      simp [hc0, hd0, hz0, hq0, SearsLimit.movingParameter]
  have H := FiniteBilateral.qPsiTerm_reflect (z := q) hq0 (by simp) hU hL k
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at H
  have harg : q ^ (N + 1) * (c * (d * SearsLimit.movingParameter z q N)) /
      (q ^ (-(N : ℤ)) * (a * (b * (w * q ^ N))) * q) = q := by
    calc
      _ = q * (c * d) / (a * b * w * z) := by
        simp only [SearsLimit.movingParameter, zpow_neg, zpow_natCast, inv_pow, pow_succ]
        field_simp
      _ = q := by rw [hbal]; field_simp
  rw [harg, show q / q ^ (N + 1) = q ^ (-(N : ℤ)) by
      simp only [pow_succ, zpow_neg, zpow_natCast]; field_simp,
    show q / SearsLimit.movingParameter z q N = z * q ^ N by
      simp only [SearsLimit.movingParameter, inv_pow]; field_simp,
    show q / q ^ (-(N : ℤ)) = q ^ (N + 1) by
      simp only [zpow_neg, zpow_natCast, pow_succ]; field_simp,
    show q / (w * q ^ N) = SearsLimit.movingParameter w q N by
      simp only [SearsLimit.movingParameter, inv_pow]; field_simp,
    qPsiTerm_natCast_eq_fourPositiveTerm hw0 hq0 hq N k] at H
  exact H

/-- A two-psi-two term at a natural index is its fixed three-phi-two coefficient times the
argument power; the upper parameter `q` cancels the factorial. -/
lemma qPsiTerm_two_natCast_eq {q : ℂ} (hq : ‖q‖ < 1) (a b c d z : ℂ) (k : ℕ) :
    qPsiTerm [a, b] [c, d] q z (k : ℤ) =
      SearsLimit.coefficient a b q c d q k * z ^ k := by
  have hQ := qPochhammer_self_ne_zero hq k
  simp only [qPsiTerm, qPsiExponent, List.length_cons, List.length_nil]
  norm_num only
  simp only [zpow_zero, mul_one, zpow_natCast, qPochhammerListInt_natCast,
    qPochhammerList, SearsLimit.coefficient, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]
  field_simp

/-- The finite balanced four-psi-four is the sum of its two geometric natural-index halves.
-/
lemma qPsi_four_eq_tsum_halves {a b c d w z q : ℂ}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0) (hd0 : d ≠ 0)
    (hw0 : w ≠ 0) (hz0 : z ≠ 0) (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hw : ‖w‖ < 1) (hz : ‖z‖ < 1) (hbal : c * d = a * b * w * z)
    (hcd : QDenominatorRegular [c, d] q)
    (hab : QDenominatorRegular [q / a, q / b] q) (N : ℕ) :
    qPsi [q ^ (-(N : ℤ)), a, b, w * q ^ N]
      [q ^ (N + 1), c, d, SearsLimit.movingParameter z q N] q q =
      (∑' k, fourPositiveTerm a b c d w z q N k) +
        (∑' k, fourPositiveTerm (q / c) (q / d) (q / a) (q / b) z w q N k) - 1 := by
  let F := qPsiTerm [q ^ (-(N : ℤ)), a, b, w * q ^ N]
    [q ^ (N + 1), c, d, SearsLimit.movingParameter z q N] q q
  have hpos (k : ℕ) : F (k : ℤ) = fourPositiveTerm a b c d w z q N k :=
    qPsiTerm_natCast_eq_fourPositiveTerm hz0 hq0 hq N k
  have hneg (k : ℕ) : F (-(k : ℤ)) =
      fourPositiveTerm (q / c) (q / d) (q / a) (q / b) z w q N k :=
    qPsiTerm_neg_natCast_eq_fourPositiveTerm ha0 hb0 hc0 hd0 hw0 hz0 hq0 hq hbal N k
  have hp : Summable (fun k : ℕ => F (k : ℤ)) :=
    (summable_fourPositiveTerm (a := a) (b := b) (w := w) hq hz hcd N).congr
      (fun k => (hpos k).symm)
  have hn : Summable (fun k : ℕ => F (-(k : ℤ))) :=
    (summable_fourPositiveTerm (a := q / c) (b := q / d) (w := z) hq hw hab N).congr
      (fun k => (hneg k).symm)
  have hzero : F 0 = 1 := by simpa only [Nat.cast_zero, fourPositiveTerm_zero] using hpos 0
  change (∑' k : ℤ, F k) = _
  rw [tsum_int_eq_tsum_natCast_add_tsum_neg_natCast_sub hp hn, hzero,
    tsum_congr hpos, tsum_congr hneg]

/-- A two-psi-two in its annulus is the sum of its two reciprocal three-phi-two halves. -/
lemma qPsi_two_eq_qPhi_halves {a b c d w z q : ℂ} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hc0 : c ≠ 0) (hd0 : d ≠ 0) (hz0 : z ≠ 0) (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hw : ‖w‖ < 1) (hz : ‖z‖ < 1) (hbal : c * d = a * b * w * z)
    (hB : QBilateralRegular [a, b] [c, d] q) :
    qPsi [a, b] [c, d] q z = qPhi [a, b, q] [c, d] q z +
      qPhi [q / c, q / d, q] [q / a, q / b] q w - 1 := by
  have hratio : c * d / (a * b * z) = w := by rw [hbal]; field_simp
  have hprod : [a, b].prod ≠ 0 := by simp [ha0, hb0]
  have H := qPsi_hasSum hq0 hq hB hprod hz0 (by simp)
    (by simpa only [List.prod_cons, List.prod_nil, mul_one, hratio] using hw)
    (fun _ => hz)
  have hp : Summable (fun k : ℕ => qPsiTerm [a, b] [c, d] q z (k : ℤ)) :=
    H.summable.comp_injective Nat.cast_injective
  have hinj : Function.Injective (fun k : ℕ => -(k : ℤ)) := by
    intro i j he
    have h := neg_injective he
    exact_mod_cast h
  have hn : Summable (fun k : ℕ => qPsiTerm [a, b] [c, d] q z (-(k : ℤ))) :=
    H.summable.comp_injective hinj
  have hneg (k : ℕ) : qPsiTerm [a, b] [c, d] q z (-(k : ℤ)) =
      SearsLimit.coefficient (q / c) (q / d) q (q / a) (q / b) q k * w ^ k := by
    have hU : ∀ x ∈ [a, b], x ≠ 0 := by simp [ha0, hb0]
    have hL : ∀ x ∈ [c, d], x ≠ 0 := by simp [hc0, hd0]
    have R := FiniteBilateral.qPsiTerm_reflect (z := z) hq0 (by simp) hU hL k
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at R
    rw [hratio, qPsiTerm_two_natCast_eq hq] at R
    exact R
  have hzero : qPsiTerm [a, b] [c, d] q z 0 = 1 := by
    have Z := qPsiTerm_two_natCast_eq hq a b c d z 0
    simpa [SearsLimit.coefficient] using Z
  unfold qPsi
  rw [tsum_int_eq_tsum_natCast_add_tsum_neg_natCast_sub hp hn, hzero,
    tsum_congr (qPsiTerm_two_natCast_eq hq a b c d z), tsum_congr hneg,
    ← SearsLimit.qPhi_eq_tsum, ← SearsLimit.qPhi_eq_tsum]

/-- The balanced finite four-psi-four approaches a two-psi-two throughout its convergence annulus.
-/
lemma tendsto_qPsi_four {a b c d w z q : ℂ} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hc0 : c ≠ 0) (hd0 : d ≠ 0) (hw0 : w ≠ 0) (hz0 : z ≠ 0)
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hw : ‖w‖ < 1) (hz : ‖z‖ < 1)
    (hbal : c * d = a * b * w * z) (hB : QBilateralRegular [a, b] [c, d] q) :
    Tendsto (fun N : ℕ => qPsi [q ^ (-(N : ℤ)), a, b, w * q ^ N]
      [q ^ (N + 1), c, d, SearsLimit.movingParameter z q N] q q) atTop
      (𝓝 (qPsi [a, b] [c, d] q z)) := by
  have hab : QDenominatorRegular [q / a, q / b] q := by
    simpa only [List.map_cons, List.map_nil] using
      FiniteBilateral.qDenominatorRegular_reciprocal (by simp [ha0, hb0]) hB.2
  have H := ((tendsto_tsum_fourPositiveTerm (a := a) (b := b) (w := w) hq hz hB.1).add
    (tendsto_tsum_fourPositiveTerm (a := q / c) (b := q / d) (w := z) hq hw hab)).sub_const 1
  rw [← qPsi_two_eq_qPhi_halves ha0 hb0 hc0 hd0 hz0 hq0 hq hw hz hbal hB] at H
  apply H.congr'
  exact Eventually.of_forall fun N =>
    (qPsi_four_eq_tsum_halves ha0 hb0 hc0 hd0 hw0 hz0 hq0 hq hw hz hbal hB.1 hab N).symm

/-- Reflection of the balanced terminating eight-psi-eight inverts its central parameter.
The transformation is valid at exceptional products because no division cancellation is used.
-/
lemma qPsiTerm_eight_reflect {a r c d e f q : ℂ} (hr : r ^ 2 = a)
    (ha0 : a ≠ 0) (hc0 : c ≠ 0) (hd0 : d ≠ 0) (he0 : e ≠ 0) (hf0 : f ≠ 0)
    (hq0 : q ≠ 0) (N k : ℕ) :
    qPsiTerm [q ^ (-(N : ℤ)), q * r, -q * r, c, d, e, f, a / q ^ N]
      [q ^ (N + 1), r, -r, a * q / c, a * q / d, a * q / e, a * q / f,
        a * q * q ^ N] q (a ^ 2 * q ^ 2 * (q ^ N) ^ 2 / (c * d * e * f)) (-(k : ℤ)) =
    qPsiTerm [q ^ (-(N : ℤ)), q * (1 / r), -q * (1 / r), c / a, d / a, e / a,
        f / a, (1 / a) / q ^ N]
      [q ^ (N + 1), 1 / r, -(1 / r), (1 / a) * q / (c / a),
        (1 / a) * q / (d / a), (1 / a) * q / (e / a), (1 / a) * q / (f / a),
        (1 / a) * q * q ^ N] q
      ((1 / a) ^ 2 * q ^ 2 * (q ^ N) ^ 2 / ((c / a) * (d / a) * (e / a) * (f / a)))
      (k : ℤ) := by
  have hr0 : r ≠ 0 := by intro h; apply ha0; rw [← hr, h]; simp
  have ht := pow_ne_zero N hq0
  have hU : ∀ x ∈ [q ^ (-(N : ℤ)), q * r, -q * r, c, d, e, f, a / q ^ N], x ≠ 0 := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [hq0, hr0, ha0, hc0, hd0, he0, hf0]
  have hL : ∀ x ∈ [q ^ (N + 1), r, -r, a * q / c, a * q / d, a * q / e,
      a * q / f, a * q * q ^ N], x ≠ 0 := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [hq0, hr0, ha0, hc0, hd0, he0, hf0]
  have H := FiniteBilateral.qPsiTerm_reflect
    (z := a ^ 2 * q ^ 2 * (q ^ N) ^ 2 / (c * d * e * f)) hq0 (by simp) hU hL k
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at H
  have harg :
      q ^ (N + 1) * (r * (-r * (a * q / c * (a * q / d *
        (a * q / e * (a * q / f * (a * q * q ^ N))))))) /
      (q ^ (-(N : ℤ)) * (q * r * (-q * r * (c * (d * (e * (f * (a / q ^ N))))))) *
        (a ^ 2 * q ^ 2 * (q ^ N) ^ 2 / (c * d * e * f))) =
      (1 / a) ^ 2 * q ^ 2 * (q ^ N) ^ 2 / ((c / a) * (d / a) * (e / a) * (f / a)) := by
    simp only [zpow_neg, zpow_natCast, pow_succ]
    field_simp
  rw [harg] at H
  convert H using 1; congr 2
  · simp only [zpow_neg, zpow_natCast, pow_succ]
    field_simp
  · simp only [List.cons.injEq, and_true]
    and_intros <;> field_simp
  · simp only [zpow_neg, zpow_natCast, pow_succ]
    field_simp
  · simp only [List.cons.injEq, and_true]
    and_intros <;> field_simp

/-- The bilateral Gaussian summand in DLMF 17.10.4, with its integer-index products. -/
def gaussianTerm (a c d e f q : ℂ) (k : ℤ) : ℂ :=
  (1 - a * q ^ (2 * k)) / (1 - a) * qPochhammerListInt [c, d, e, f] q k /
    qPochhammerListInt [a * q / c, a * q / d, a * q / e, a * q / f] q k *
    (q * a ^ 3 / (c * d * e * f)) ^ k * q ^ (k * k)

/-- The natural-index Gaussian summand has the fixed-product coefficient used in its bounds.
-/
lemma gaussianTerm_natCast_eq (a c d e f q : ℂ) (k : ℕ) :
    gaussianTerm a c d e f q (k : ℤ) = gaussianCoefficient a c d e f q k *
      (q * a ^ 3 / (c * d * e * f)) ^ k * q ^ (k * k) := by
  simp only [gaussianTerm, gaussianCoefficient, qPochhammerListInt_natCast,
    show (2 : ℤ) * (k : ℤ) = ((2 * k : ℕ) : ℤ) by omega,
    ← Nat.cast_mul, zpow_natCast]

/-- The negative Gaussian half is the positive half with all parameters divided by the central
parameter, and the central parameter inverted. -/
lemma gaussianTerm_neg_natCast_eq {a c d e f q : ℂ} (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (hc0 : c ≠ 0) (hd0 : d ≠ 0) (he0 : e ≠ 0) (hf0 : f ≠ 0)
    (hq0 : q ≠ 0) (k : ℕ) :
    gaussianTerm a c d e f q (-(k : ℤ)) =
      gaussianTerm (1 / a) (c / a) (d / a) (e / a) (f / a) q (k : ℤ) := by
  have hU : ∀ x ∈ [c, d, e, f], x ≠ 0 := by simp [hc0, hd0, he0, hf0]
  have hL : ∀ x ∈ [a * q / c, a * q / d, a * q / e, a * q / f], x ≠ 0 := by
    simp [ha0, hq0, hc0, hd0, he0, hf0]
  have R := FiniteBilateral.qPsiTerm_reflect
    (z := q * a ^ 3 / (c * d * e * f)) hq0 (by simp) hU hL k
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at R
  have harg : a * q / c * (a * q / d * (a * q / e * (a * q / f))) /
      (c * (d * (e * f)) * (q * a ^ 3 / (c * d * e * f))) =
      ((q * (1 / a) ^ 3 / ((c / a) * (d / a) * (e / a) * (f / a))) * q ^ 2) := by
    field_simp
  rw [harg] at R
  have hargs : [q / (a * q / c), q / (a * q / d), q / (a * q / e), q / (a * q / f)] =
      [c / a, d / a, e / a, f / a] := by congr 1 <;> field_simp
  have hargs' : [q / c, q / d, q / e, q / f] =
      [(1 / a) * q / (c / a), (1 / a) * q / (d / a), (1 / a) * q / (e / a),
        (1 / a) * q / (f / a)] := by congr 1 <;> field_simp
  rw [hargs, hargs'] at R
  have he : qPsiExponent [c, d, e, f]
      [a * q / c, a * q / d, a * q / e, a * q / f] = 0 := by simp [qPsiExponent]
  have he' : qPsiExponent [c / a, d / a, e / a, f / a]
      [(1 / a) * q / (c / a), (1 / a) * q / (d / a), (1 / a) * q / (e / a),
        (1 / a) * q / (f / a)] = 0 := by simp [qPsiExponent]
  simp only [qPsiTerm, he, he', zpow_zero, mul_one, zpow_natCast] at R
  have hroot : (1 - a * q ^ (2 * -(k : ℤ))) / (1 - a) * (q ^ 2) ^ k =
      (1 - (1 / a) * q ^ (2 * (k : ℤ))) / (1 - 1 / a) := by
    rw [show 2 * -(k : ℤ) = -((2 * k : ℕ) : ℤ) by push_cast; ring,
      show 2 * (k : ℤ) = ((2 * k : ℕ) : ℤ) by push_cast; ring]
    simp only [zpow_neg, zpow_natCast, ← pow_mul]
    field_simp
    ring
  unfold gaussianTerm
  rw [show (-(k : ℤ)) * -(k : ℤ) = ((k * k : ℕ) : ℤ) by push_cast; ring,
    mul_div_assoc, mul_assoc ((1 - a * q ^ (2 * -(k : ℤ))) / (1 - a)), R,
    mul_pow]
  simp only [← Nat.cast_mul, zpow_natCast]
  linear_combination
    (qPochhammerListInt [c / a, d / a, e / a, f / a] q (k : ℤ) /
      qPochhammerListInt [(1 / a) * q / (c / a), (1 / a) * q / (d / a),
        (1 / a) * q / (e / a), (1 / a) * q / (f / a)] q (k : ℤ) *
      (q * (1 / a) ^ 3 / ((c / a) * (d / a) * (e / a) * (f / a))) ^ k *
      q ^ (k * k)) * hroot

end DLMF.QHypergeometric.BilateralGaussian
