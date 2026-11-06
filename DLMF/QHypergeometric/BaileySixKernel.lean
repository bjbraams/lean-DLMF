/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.SixPhiFiveCleared
public import DLMF.QHypergeometric.BaileyBilateral

/-!
# Cleared kernels for Bailey's six-psi-six summation

The positive half uses the very-well-poised factor `(1-aq^{2n})/(1-a)`.
The negative half is its parameter reflection `a ↦ 1/a`, `b ↦ b/a`, and so on.
Clearing all lower and reciprocal-upper products makes both halves entire in `x = 1/e`.
-/

@[expose] public noncomputable section

open Complex Filter Finset Set
open scoped Topology
open DLMF.QSeries

namespace DLMF.QHypergeometric.BaileySixSummation

/-- The factor left after cancelling the two very-well-poised root parameters. -/
def naturalFactor (a q : ℂ) (n : ℕ) : ℂ := (1 - a * q ^ (2 * n)) / (1 - a)

/-- The geometric scale in the reciprocal fourth upper parameter. -/
def scale (a b c d q : ℂ) : ℂ := q * a ^ 2 / (b * c * d)

/-- The fixed-index coefficient after clearing the six fixed denominator products. -/
def coefficient (a b c d q : ℂ) (n : ℕ) : ℂ :=
  naturalFactor a q n * qPochhammer b q n * qPochhammer c q n * qPochhammer d q n *
    qPochhammerInf (a * q / b * q ^ n) q *
    qPochhammerInf (a * q / c * q ^ n) q *
    qPochhammerInf (a * q / d * q ^ n) q *
    qPochhammerInf (q / b) q * qPochhammerInf (q / c) q * qPochhammerInf (q / d) q

/-- The cleared nonnegative-index term, entire in `x`. -/
def positiveTerm (a b c d q x : ℂ) (n : ℕ) : ℂ :=
  coefficient a b c d q n * BaileyBilateral.reversedProduct 1 q x n *
    qPochhammerInf (a * q * x * q ^ n) q * qPochhammerInf (q * x) q *
    qPochhammerInf (scale a b c d q * x) q * scale a b c d q ^ n

/-- The cleared bilateral term, with its negative half written by reflection. -/
def term (a b c d q x : ℂ) : ℤ → ℂ
  | .ofNat n => positiveTerm a b c d q x n
  | .negSucc n => positiveTerm a⁻¹ (b / a) (c / a) (d / a) q (a * x) (n + 1)

/-- The product side after every variable denominator product has been cleared. -/
def productSide (a b c d q x : ℂ) : ℂ :=
  qPochhammerListInf [a * q, a * q / (b * c), a * q / (b * d), a * q * x / b,
    a * q / (c * d), a * q * x / c, a * q * x / d, q, q / a] q

/-- The common clearing product of the positive and reflected series. -/
def denominator (a b c d q x : ℂ) : ℂ :=
  qPochhammerListInf [a * q / b, a * q / c, a * q / d, a * q * x,
    q / b, q / c, q / d, q * x, scale a b c d q * x] q

/-- The fixed coefficients form a bounded sequence, including vanishing product factors. -/
lemma exists_norm_coefficient_le {q : ℂ} (hq : ‖q‖ < 1) (a b c d : ℂ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n, ‖coefficient a b c d q n‖ ≤ M := by
  have hQ : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq two_ne_zero
  have hp : Tendsto (fun n : ℕ => q ^ (2 * n)) atTop (𝓝 (0 : ℂ)) := by
    simpa only [pow_mul] using tendsto_pow_atTop_nhds_zero_of_norm_lt_one hQ
  have hF : Tendsto (naturalFactor a q) atTop (𝓝 (1 / (1 - a))) := by
    change Tendsto (fun n : ℕ => (1 - a * q ^ (2 * n)) / (1 - a)) atTop _
    simpa only [mul_zero, sub_zero] using
      (tendsto_const_nhds.sub (hp.const_mul a)).div_const (1 - a)
  have hI : ContinuousAt (fun u : ℂ => qPochhammerInf u q) 0 :=
    (differentiable_qPochhammerInf_left hq).continuous.continuousAt
  have hshift (u : ℂ) : Tendsto (fun n : ℕ => qPochhammerInf (u * q ^ n) q)
      atTop (𝓝 (1 : ℂ)) := by
    have hu : Tendsto (fun n : ℕ => u * q ^ n) atTop (𝓝 (0 : ℂ)) := by
      simpa only [mul_zero] using
        (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).const_mul u
    simpa only [Function.comp_def, qPochhammerInf_zero] using hI.tendsto.comp hu
  have H : Tendsto (coefficient a b c d q) atTop
      (𝓝 ((1 / (1 - a)) * qPochhammerInf b q * qPochhammerInf c q * qPochhammerInf d q *
        1 * 1 * 1 * qPochhammerInf (q / b) q * qPochhammerInf (q / c) q *
        qPochhammerInf (q / d) q)) :=
    (((((((((hF.mul (tendsto_qPochhammer hq)).mul (tendsto_qPochhammer hq)).mul
      (tendsto_qPochhammer hq)).mul (hshift (a * q / b))).mul (hshift (a * q / c))).mul
      (hshift (a * q / d))).mul_const _).mul_const _).mul_const _)
  obtain ⟨M, hM⟩ := H.norm.bddAbove_range
  have hbound : ∀ n, ‖coefficient a b c d q n‖ ≤ M := fun n => hM ⟨n, rfl⟩
  exact ⟨M, (norm_nonneg _).trans (hbound 0), hbound⟩

/-- The positive cleared terms are entire in the reciprocal upper parameter. -/
lemma differentiable_positiveTerm {q : ℂ} (hq : ‖q‖ < 1) (a b c d : ℂ) (n : ℕ) :
    Differentiable ℂ (fun x => positiveTerm a b c d q x n) := by
  have hrev : Differentiable ℂ (fun x => BaileyBilateral.reversedProduct 1 q x n) := by
    unfold BaileyBilateral.reversedProduct
    fun_prop
  have hI := differentiable_qPochhammerInf_left hq
  unfold positiveTerm
  exact (((((hrev.const_mul _).mul (hI.comp (by fun_prop))).mul
    (hI.comp (by fun_prop))).mul (hI.comp (by fun_prop))).mul_const _)

/-- Every cleared bilateral term is entire in the reciprocal upper parameter. -/
lemma differentiable_term {q : ℂ} (hq : ‖q‖ < 1) (a b c d : ℂ) (n : ℤ) :
    Differentiable ℂ (fun x => term a b c d q x n) := by
  cases n with
  | ofNat n => exact differentiable_positiveTerm hq a b c d n
  | negSucc n =>
    exact (differentiable_positiveTerm hq a⁻¹ (b / a) (c / a) (d / a) (n + 1)).comp
      (by fun_prop)

/-- Positive terms admit a uniform geometric bound on any closed parameter disk. -/
lemma exists_norm_positiveTerm_le {q : ℂ} (hq : ‖q‖ < 1) (a b c d : ℂ)
    {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℂ, ‖x‖ ≤ r → ∀ n : ℕ,
      ‖positiveTerm a b c d q x n‖ ≤ C * (r * ‖scale a b c d q‖) ^ n := by
  obtain ⟨M, hM, hcoef⟩ := exists_norm_coefficient_le hq a b c d
  let Y := ‖a * q‖ * r + ‖q‖ * r + ‖scale a b c d q‖ * r
  let E := Real.exp (Y / (1 - ‖q‖))
  let K := Real.exp (1 / (r * (1 - ‖q‖)))
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hK : 0 ≤ K := (Real.exp_pos _).le
  refine ⟨M * K * E ^ 3, by positivity, fun x hx n => ?_⟩
  have hshift : ∀ u : ℂ, ‖u‖ ≤ Y → ‖u * q ^ n‖ ≤ Y := by
    intro u hu
    rw [norm_mul, norm_pow]
    exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hq.le)).trans hu
  have hinf : ∀ u : ℂ, ‖u‖ ≤ Y → ‖qPochhammerInf u q‖ ≤ E := by
    intro u hu
    exact (norm_qPochhammerInf_le_exp hq).trans
      (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hu (by linarith)))
  have haqx : ‖a * q * x‖ ≤ Y := by
    rw [norm_mul]
    have H := mul_le_mul_of_nonneg_left hx (norm_nonneg (a * q))
    dsimp only [Y]
    nlinarith [norm_nonneg q, norm_nonneg (scale a b c d q)]
  have hqx : ‖q * x‖ ≤ Y := by
    rw [norm_mul]
    have H := mul_le_mul_of_nonneg_left hx (norm_nonneg q)
    dsimp only [Y]
    nlinarith [norm_nonneg (a * q), norm_nonneg (scale a b c d q)]
  have hzx : ‖scale a b c d q * x‖ ≤ Y := by
    rw [norm_mul]
    have H := mul_le_mul_of_nonneg_left hx (norm_nonneg (scale a b c d q))
    dsimp only [Y]
    nlinarith [norm_nonneg (a * q), norm_nonneg q]
  have hrev := BaileyBilateral.norm_reversedProduct_le (d := (1 : ℂ)) hq hr hx n
  simp only [norm_one] at hrev
  simp only [positiveTerm, norm_mul, norm_pow]
  calc _ ≤ M * (r ^ n * K) * E * E * E * ‖scale a b c d q‖ ^ n := by
          gcongr
          · exact hcoef n
          · exact hinf _ (hshift _ haqx)
          · exact hinf _ hqx
          · exact hinf _ hzx
    _ = _ := by rw [mul_pow]; ring


/-- Parameter reflection preserves the argument after rescaling the reciprocal parameter. -/
lemma scale_reflected_mul {a b c d q : ℂ} (ha : a ≠ 0) (hbcd : b * c * d ≠ 0) :
    scale a⁻¹ (b / a) (c / a) (d / a) q * a = scale a b c d q := by
  have hb := left_ne_zero_of_mul (left_ne_zero_of_mul hbcd)
  have hc := right_ne_zero_of_mul (left_ne_zero_of_mul hbcd)
  have hd := right_ne_zero_of_mul hbcd
  unfold scale
  field_simp

/-- Both cleared halves admit the same geometric majorant. -/
lemma norm_terms_le {a b c d q : ℂ} (hq : ‖q‖ < 1) (ha : a ≠ 0)
    (hbcd : b * c * d ≠ 0) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℂ, ‖x‖ ≤ r → ∀ n : ℕ,
      ‖positiveTerm a b c d q x n‖ ≤ C * (r * ‖scale a b c d q‖) ^ n ∧
      ‖positiveTerm a⁻¹ (b / a) (c / a) (d / a) q (a * x) n‖ ≤
        C * (r * ‖scale a b c d q‖) ^ n := by
  obtain ⟨C₁, hC₁, hpos⟩ := exists_norm_positiveTerm_le hq a b c d hr
  obtain ⟨C₂, hC₂, hneg⟩ := exists_norm_positiveTerm_le hq a⁻¹ (b / a) (c / a) (d / a)
    (mul_pos (norm_pos_iff.mpr ha) hr)
  have hscale : ‖a‖ * r * ‖scale a⁻¹ (b / a) (c / a) (d / a) q‖ =
      r * ‖scale a b c d q‖ := by
    have H := congrArg norm (scale_reflected_mul (q := q) ha hbcd)
    rw [norm_mul] at H
    nlinarith
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun x hx n => ⟨?_, ?_⟩⟩
  · exact (hpos x hx n).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC₂) (by positivity))
  · have H := hneg (a * x) (by rw [norm_mul]; gcongr) n
    rw [hscale] at H
    exact H.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₁) (by positivity))

/-- On each strictly interior disk the bilateral terms have a summable majorant. -/
lemma exists_summable_bound {a b c d q : ℂ} (hq : ‖q‖ < 1) (ha : a ≠ 0)
    (hbcd : b * c * d ≠ 0) {r : ℝ} (hr : 0 < r)
    (hρ : r * ‖scale a b c d q‖ < 1) :
    ∃ u : ℤ → ℝ, Summable u ∧ ∀ n x, ‖x‖ ≤ r → ‖term a b c d q x n‖ ≤ u n := by
  obtain ⟨C, hC, hbound⟩ := norm_terms_le hq ha hbcd hr
  let ρ := r * ‖scale a b c d q‖
  have hρ0 : 0 ≤ ρ := mul_nonneg hr.le (norm_nonneg _)
  let u : ℤ → ℝ := fun n => match n with
    | .ofNat k => C * ρ ^ k
    | .negSucc k => C * ρ ^ (k + 1)
  refine ⟨u, ?_, ?_⟩
  · refine Summable.of_nat_of_neg_add_one ?_ ?_
    · exact (summable_geometric_of_lt_one hρ0 hρ).mul_left C
    · exact ((summable_nat_add_iff 1).mpr
        (summable_geometric_of_lt_one hρ0 hρ)).mul_left C
  · intro n x hx
    cases n with
    | ofNat n => exact (hbound x hx n).1
    | negSucc n => exact (hbound x hx (n + 1)).2

/-- The fully cleared bilateral series is analytic inside its convergence disk. -/
lemma analyticOnNhd_tsum_term {a b c d q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha : a ≠ 0) (hbcd : b * c * d ≠ 0) :
    AnalyticOnNhd ℂ (fun x => ∑' n : ℤ, term a b c d q x n)
      (Metric.ball 0 ‖scale a b c d q‖⁻¹) := by
  have hT : 0 < ‖scale a b c d q‖ :=
    norm_pos_iff.mpr (div_ne_zero (mul_ne_zero hq0 (pow_ne_zero 2 ha)) hbcd)
  apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
  apply differentiableOn_tsum_of_locally_dominated Metric.isOpen_ball
  · intro n
    exact (differentiable_term hq a b c d n).differentiableOn
  · intro x hx
    obtain ⟨r, hxr, hrR⟩ := exists_between
      (show ‖x‖ < ‖scale a b c d q‖⁻¹ by simpa using hx)
    have hr : 0 < r := lt_of_le_of_lt (norm_nonneg _) hxr
    have hρ : r * ‖scale a b c d q‖ < 1 := by
      have H := mul_lt_mul_of_pos_right hrR hT
      simpa only [inv_mul_cancel₀ hT.ne'] using H
    obtain ⟨u, hu, hbound⟩ := exists_summable_bound hq ha hbcd hr hρ
    refine ⟨Metric.ball 0 r, Metric.isOpen_ball.mem_nhds (by simpa using hxr), u, hu, ?_⟩
    intro n z hz
    exact hbound n z (by simpa using (Metric.mem_ball.mp hz).le)

/-- The series converges absolutely throughout the same disk. -/
lemma summable_term {a b c d q x : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha : a ≠ 0) (hbcd : b * c * d ≠ 0) (hx : ‖x‖ < ‖scale a b c d q‖⁻¹) :
    Summable (term a b c d q x) := by
  have hT : 0 < ‖scale a b c d q‖ :=
    norm_pos_iff.mpr (div_ne_zero (mul_ne_zero hq0 (pow_ne_zero 2 ha)) hbcd)
  obtain ⟨r, hxr, hrR⟩ := exists_between hx
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg _) hxr
  have hρ : r * ‖scale a b c d q‖ < 1 := by
    have H := mul_lt_mul_of_pos_right hrR hT
    simpa only [inv_mul_cancel₀ hT.ne'] using H
  obtain ⟨u, hu, hbound⟩ := exists_summable_bound hq ha hbcd hr hρ
  exact Summable.of_norm_bounded hu (fun n => hbound n x hxr.le)

/-- The cleared product is entire in the reciprocal upper parameter. -/
lemma differentiable_productSide {q : ℂ} (hq : ‖q‖ < 1) (a b c d : ℂ) :
    Differentiable ℂ (productSide a b c d q) := by
  have hI := differentiable_qPochhammerInf_left hq
  unfold productSide
  simp only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  exact (differentiable_const _).mul ((differentiable_const _).mul
    ((differentiable_const _).mul ((hI.comp (by fun_prop)).mul
      ((differentiable_const _).mul ((hI.comp (by fun_prop)).mul
        ((hI.comp (by fun_prop)).mul ((differentiable_const _).mul
          (differentiable_const _))))))))

end DLMF.QHypergeometric.BaileySixSummation
