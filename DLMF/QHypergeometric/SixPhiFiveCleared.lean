/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.VeryWellPoisedSums
public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy

/-!
# The fully cleared very-well-poised six-phi-five sum

The unit Bailey numerator removes the two square-root factors. Multiplying by all
three remaining lower-parameter products gives an analytic series in the central
parameter, including the zeros of those products. This form of DLMF 17.7.15 supports
bilateral index shifts without introducing artificial lower-parameter exclusions.
-/

@[expose] public noncomputable section

open Complex Filter Finset Set
open scoped Topology
open DLMF.QSeries

namespace DLMF.QHypergeometric.SixPhiFiveCleared

/-- The part of a six-phi-five coefficient independent of the central parameter. -/
def coefficient (b c d q : ℂ) (n : ℕ) : ℂ :=
  qPochhammer b q n * qPochhammer c q n * qPochhammer d q n / qPochhammer q q n

/-- A six-phi-five term after clearing every nontrivial lower shifted factorial. -/
def term (b c d q a : ℂ) (n : ℕ) : ℂ :=
  DLMF.Bailey.unitD a q n * coefficient b c d q n *
    qPochhammerInf (a * q / b * q ^ n) q *
    qPochhammerInf (a * q / c * q ^ n) q *
    qPochhammerInf (a * q / d * q ^ n) q * (a * q / (b * c * d)) ^ n

/-- The lower-product-cleared value of the six-phi-five sum. -/
def productSide (b c d q a : ℂ) : ℂ :=
  qPochhammerListInf [a * q, a * q / (b * c), a * q / (b * d), a * q / (c * d)] q /
    qPochhammerInf (a * q / (b * c * d)) q

/-- The fixed finite coefficient is uniformly bounded in its index. -/
lemma exists_norm_coefficient_le {q : ℂ} (hq : ‖q‖ < 1) (b c d : ℂ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n, ‖coefficient b c d q n‖ ≤ M := by
  have hqI : qPochhammerInf q q ≠ 0 := by
    apply qPochhammerInf_ne_zero hq
    intro j
    simpa only [pow_succ', pow_one] using qPochhammerInf_pow_succ_ne_zero hq j
  have ht : Tendsto (coefficient b c d q) atTop
      (𝓝 (qPochhammerInf b q * qPochhammerInf c q * qPochhammerInf d q /
        qPochhammerInf q q)) :=
    (((tendsto_qPochhammer (w := b) hq).mul (tendsto_qPochhammer (w := c) hq)).mul
      (tendsto_qPochhammer (w := d) hq)).div (tendsto_qPochhammer hq) hqI
  obtain ⟨M, hM⟩ := ht.norm.bddAbove_range
  have hbound : ∀ n, ‖coefficient b c d q n‖ ≤ M := fun n => hM ⟨n, rfl⟩
  exact ⟨M, (norm_nonneg _).trans (hbound 0), hbound⟩

/-- The unit Bailey numerator is polynomial in its central parameter. -/
lemma differentiable_unitD (q : ℂ) (n : ℕ) :
    Differentiable ℂ (fun a : ℂ => DLMF.Bailey.unitD a q n) := by
  cases n with
  | zero => simp only [DLMF.Bailey.unitD]; exact differentiable_const _
  | succ n =>
    simp only [DLMF.Bailey.unitD, qPochhammer_eq_prod]
    fun_prop

/-- Each fully cleared term is entire in the central parameter. -/
lemma differentiable_term {q : ℂ} (hq : ‖q‖ < 1) (b c d : ℂ) (n : ℕ) :
    Differentiable ℂ (fun a => term b c d q a n) := by
  have hI := differentiable_qPochhammerInf_left hq
  unfold term
  exact (((((differentiable_unitD q n).mul_const _).mul (hI.comp (by fun_prop))).mul
    (hI.comp (by fun_prop))).mul (hI.comp (by fun_prop))).mul (by fun_prop)

/-- A uniform bound for the unit Bailey numerator on a central-parameter disk. -/
lemma norm_unitD_le {a q : ℂ} {r : ℝ} (hq : ‖q‖ < 1) (hr : 0 ≤ r)
    (ha : ‖a‖ ≤ r) (n : ℕ) :
    ‖DLMF.Bailey.unitD a q n‖ ≤ (1 + r) * Real.exp (r * ‖q‖ / (1 - ‖q‖)) := by
  have hE : 1 ≤ Real.exp (r * ‖q‖ / (1 - ‖q‖)) := Real.one_le_exp (by positivity)
  cases n with
  | zero => simp only [DLMF.Bailey.unitD, norm_one]; nlinarith
  | succ n =>
    simp only [DLMF.Bailey.unitD, norm_mul]
    have hP : ‖qPochhammer (a * q) q n‖ ≤ Real.exp (r * ‖q‖ / (1 - ‖q‖)) := by
      refine (norm_qPochhammer_le_exp hq n).trans (Real.exp_le_exp.mpr ?_)
      rw [norm_mul]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
        (by linarith)
    have hV : ‖1 - a * q ^ (2 * (n + 1))‖ ≤ 1 + r := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one, norm_mul, norm_pow]
      simpa only [add_comm] using add_le_add_left
        ((mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hq.le)).trans ha) 1
    nlinarith [mul_le_mul hP hV (norm_nonneg _) (Real.exp_pos _).le]

/-- A geometric majorant for the fully cleared six-phi-five terms on a closed disk. -/
lemma exists_norm_term_le {q : ℂ} (hq : ‖q‖ < 1) (b c d : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : ℂ, ‖a‖ ≤ r → ∀ n : ℕ,
      ‖term b c d q a n‖ ≤ M * (r * ‖q / (b * c * d)‖) ^ n := by
  obtain ⟨M, hM, hcoef⟩ := exists_norm_coefficient_le hq b c d
  let E (u : ℂ) := Real.exp (r * ‖q / u‖ / (1 - ‖q‖))
  let U := (1 + r) * Real.exp (r * ‖q‖ / (1 - ‖q‖))
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hE (u : ℂ) : 0 ≤ E u := (Real.exp_pos _).le
  refine ⟨U * M * E b * E c * E d, by positivity, fun a ha n => ?_⟩
  have hinf (u : ℂ) : ‖qPochhammerInf (a * q / u * q ^ n) q‖ ≤ E u := by
    refine (norm_qPochhammerInf_le_exp hq).trans (Real.exp_le_exp.mpr ?_)
    refine div_le_div_of_nonneg_right ?_ (by linarith)
    rw [show a * q / u * q ^ n = a * (q / u) * q ^ n by ring, norm_mul, norm_mul, norm_pow]
    calc ‖a‖ * ‖q / u‖ * ‖q‖ ^ n ≤ ‖a‖ * ‖q / u‖ :=
          mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg _) hq.le)
      _ ≤ r * ‖q / u‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
  have harg : ‖a * q / (b * c * d)‖ ≤ r * ‖q / (b * c * d)‖ := by
    rw [show a * q / (b * c * d) = a * (q / (b * c * d)) by ring, norm_mul]
    exact mul_le_mul_of_nonneg_right ha (norm_nonneg _)
  simp only [term, norm_mul, norm_pow]
  calc _ ≤ U * M * E b * E c * E d * (r * ‖q / (b * c * d)‖) ^ n := by
          gcongr
          · exact norm_unitD_le hq hr ha n
          · exact hcoef n
          · exact hinf b
          · exact hinf c
          · exact hinf d
      _ = _ := rfl


/-- The argument lies in the unit disk throughout the central-parameter convergence disk. -/
lemma norm_argument_lt_one {a b c d q : ℂ} (hq0 : q ≠ 0) (hbcd : b * c * d ≠ 0)
    (ha : a ∈ Metric.ball (0 : ℂ) ‖q / (b * c * d)‖⁻¹) :
    ‖a * q / (b * c * d)‖ < 1 := by
  have hT : 0 < ‖q / (b * c * d)‖ := norm_pos_iff.mpr (div_ne_zero hq0 hbcd)
  have ha' : ‖a‖ < ‖q / (b * c * d)‖⁻¹ := by simpa using ha
  have H := mul_lt_mul_of_pos_right ha' hT
  rw [inv_mul_cancel₀ hT.ne'] at H
  simpa only [show a * q / (b * c * d) = a * (q / (b * c * d)) by ring, norm_mul] using H

/-- The cleared sum is analytic throughout its central-parameter convergence disk. -/
lemma analyticOnNhd_tsum_term {b c d q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hbcd : b * c * d ≠ 0) :
    AnalyticOnNhd ℂ (fun a => ∑' n : ℕ, term b c d q a n)
      (Metric.ball 0 ‖q / (b * c * d)‖⁻¹) := by
  have hT : 0 < ‖q / (b * c * d)‖ := norm_pos_iff.mpr (div_ne_zero hq0 hbcd)
  apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
  apply differentiableOn_tsum_of_locally_dominated Metric.isOpen_ball
  · intro n
    exact (differentiable_term hq b c d n).differentiableOn
  · intro a ha
    obtain ⟨r, har, hrR⟩ := exists_between (show ‖a‖ < ‖q / (b * c * d)‖⁻¹ by simpa using ha)
    have hr : 0 < r := lt_of_le_of_lt (norm_nonneg _) har
    have hρ : r * ‖q / (b * c * d)‖ < 1 := by
      have H := mul_lt_mul_of_pos_right hrR hT
      simpa only [inv_mul_cancel₀ hT.ne'] using H
    obtain ⟨M, hM, hbound⟩ := exists_norm_term_le hq b c d hr.le
    refine ⟨Metric.ball 0 r, Metric.isOpen_ball.mem_nhds (by simpa using har),
      fun n => M * (r * ‖q / (b * c * d)‖) ^ n,
      (summable_geometric_of_lt_one (by positivity) hρ).mul_left M, ?_⟩
    intro n z hz
    exact hbound z (by simpa using (Metric.mem_ball.mp hz).le) n

/-- The product side is analytic on the same convergence disk. -/
lemma analyticOnNhd_productSide {b c d q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hbcd : b * c * d ≠ 0) :
    AnalyticOnNhd ℂ (productSide b c d q) (Metric.ball 0 ‖q / (b * c * d)‖⁻¹) := by
  intro a ha
  have hI := differentiable_qPochhammerInf_left hq
  unfold productSide
  simp only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  refine AnalyticAt.div ?_ ((hI.comp (by fun_prop)).analyticAt a)
    (qPochhammerInf_ne_zero_of_norm_lt_one (norm_argument_lt_one hq0 hbcd ha) hq)
  exact ((hI.comp (by fun_prop)).mul ((hI.comp (by fun_prop)).mul
    ((hI.comp (by fun_prop)).mul (hI.comp (by fun_prop))))).analyticAt a

/-- At regular lower parameters, clearing the series gives the Rogers product quotient. -/
lemma tsum_term_eq_of_regular {a b c d q : ℂ} (hq : ‖q‖ < 1)
    (ha : a ≠ 1) (hz : ‖a * q‖ < ‖b * c * d‖)
    (hreg : QDenominatorRegular
      [Complex.sqrt a, -Complex.sqrt a, a * q / b, a * q / c, a * q / d] q) :
    (∑' n : ℕ, term b c d q a n) = productSide b c d q a := by
  let D := qPochhammerInf (a * q / b) q * qPochhammerInf (a * q / c) q *
    qPochhammerInf (a * q / d) q
  have hfinite (x : ℂ) (hx : x ∈
      [Complex.sqrt a, -Complex.sqrt a, a * q / b, a * q / c, a * q / d]) (n : ℕ) :
      qPochhammer x q n ≠ 0 :=
    qPochhammer_ne_zero_of_mem_qDenominatorRegular hq hreg hx n
  have hinfinite (x : ℂ) (hx : x ∈
      [Complex.sqrt a, -Complex.sqrt a, a * q / b, a * q / c, a * q / d]) :
      qPochhammerInf x q ≠ 0 := qPochhammerInf_ne_zero hq
        (fun j h => hreg x hx j (sub_eq_zero.mp h).symm)
  have hterm (n : ℕ) : term b c d q a n = D *
      qPhiTerm [a, q * Complex.sqrt a, -q * Complex.sqrt a, b, c, d]
        [Complex.sqrt a, -Complex.sqrt a, a * q / b, a * q / c, a * q / d]
        q (a * q / (b * c * d)) n := by
    have hR := mul_ne_zero (hfinite (Complex.sqrt a) (by simp) n)
      (hfinite (-Complex.sqrt a) (by simp) n)
    have hB := hfinite (a * q / b) (by simp) n
    have hC := hfinite (a * q / c) (by simp) n
    have hD := hfinite (a * q / d) (by simp) n
    have hQ := qPochhammer_self_ne_zero hq n
    have hunit := veryWellPoised_factor_eq_unitD n (Or.inr ⟨ha, hR⟩)
    have hseries : qPhiTerm [a, q * Complex.sqrt a, -q * Complex.sqrt a, b, c, d]
        [Complex.sqrt a, -Complex.sqrt a, a * q / b, a * q / c, a * q / d]
        q (a * q / (b * c * d)) n =
        DLMF.Bailey.unitD a q n * coefficient b c d q n /
          (qPochhammer (a * q / b) q n * qPochhammer (a * q / c) q n *
            qPochhammer (a * q / d) q n) * (a * q / (b * c * d)) ^ n := by
      rw [← hunit]
      simp only [qPhiTerm, qPhiExponent, List.length_cons, List.length_nil]
      norm_num only
      simp only [coefficient, qPochhammerList, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one, div_eq_mul_inv, mul_inv_rev, zpow_zero]
      ring
    rw [hseries]
    have hcancel (B C D U V W T Z : ℂ) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0) :
        (B * U * (C * V) * (D * W)) * (T / (B * C * D) * Z) =
          T * U * V * W * Z := by field_simp
    dsimp only [D]
    rw [qPochhammerInf_mul_qPochhammer hq n (a := a * q / b),
      qPochhammerInf_mul_qPochhammer hq n (a := a * q / c),
      qPochhammerInf_mul_qPochhammer hq n (a := a * q / d)]
    exact (hcancel _ _ _ _ _ _ _ _ hB hC hD).symm
  rw [tsum_congr hterm, tsum_mul_left, show (∑' n : ℕ,
      qPhiTerm [a, q * Complex.sqrt a, -q * Complex.sqrt a, b, c, d]
      [Complex.sqrt a, -Complex.sqrt a, a * q / b, a * q / c, a * q / d]
      q (a * q / (b * c * d)) n) = qPhi _ _ _ _ from rfl,
    six_phi_five_sum hq hz hreg]
  unfold productSide
  dsimp only [D]
  simp only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  field_simp [hinfinite (a * q / b) (by simp), hinfinite (a * q / c) (by simp),
    hinfinite (a * q / d) (by simp)]

/-- The fully cleared Rogers sum, including every zero of the lower products. -/
theorem tsum_term_eq_productSide {a b c d q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hz : ‖a * q‖ < ‖b * c * d‖) :
    (∑' n : ℕ, term b c d q a n) = productSide b c d q a := by
  have hbcd : b * c * d ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    exact (norm_nonneg _).not_gt hz
  have hT : 0 < ‖q / (b * c * d)‖ := norm_pos_iff.mpr (div_ne_zero hq0 hbcd)
  have hsmall (u : ℂ) : ∀ᶠ x : ℂ in 𝓝 0, ‖x * u‖ < 1 := by
    have H : Tendsto (fun x : ℂ => ‖x * u‖) (𝓝 0) (𝓝 0) := by
      simpa only [id_eq, zero_mul, norm_zero] using
        ((continuous_id.mul_const u).continuousAt (x := (0 : ℂ))).norm.tendsto
    exact H.eventually (gt_mem_nhds one_pos)
  have hnear : (fun x => ∑' n : ℕ, term b c d q x n) =ᶠ[𝓝 0] productSide b c d q := by
    filter_upwards [hsmall 1, hsmall (q / b), hsmall (q / c), hsmall (q / d),
      hsmall (q / (b * c * d))] with x hx hB hC hD hz'
    have hx' : ‖x‖ < 1 := by simpa only [mul_one] using hx
    have ha : x ≠ 1 := by
      intro h
      rw [h, norm_one] at hx'
      exact lt_irrefl _ hx'
    have hs : (Complex.sqrt x) ^ 2 = x := by
      rw [Complex.sqrt, ← Complex.cpow_nat_mul]
      norm_num
    have hrs : ‖Complex.sqrt x‖ < 1 := by
      have H : ‖Complex.sqrt x‖ ^ 2 = ‖x‖ := by rw [← norm_pow, hs]
      nlinarith [norm_nonneg (Complex.sqrt x)]
    have hregular (u : ℂ) (hu : ‖u‖ < 1) (j : ℕ) : u * q ^ j ≠ 1 := by
      intro he
      have H := norm_mul_pow_lt_one hu hq j
      rw [he, norm_one] at H
      exact lt_irrefl _ H
    apply tsum_term_eq_of_regular hq ha
    · have H : ‖x * q / (b * c * d)‖ < 1 := by
        simpa only [div_eq_mul_inv, mul_assoc] using hz'
      rw [norm_div, div_lt_one (norm_pos_iff.mpr hbcd)] at H
      exact H
    · intro u hu j
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl
      · exact hregular _ hrs j
      · exact hregular _ (by simpa only [norm_neg] using hrs) j
      · exact hregular _ (by simpa only [div_eq_mul_inv, mul_assoc] using hB) j
      · exact hregular _ (by simpa only [div_eq_mul_inv, mul_assoc] using hC) j
      · exact hregular _ (by simpa only [div_eq_mul_inv, mul_assoc] using hD) j
  have heq := (analyticOnNhd_tsum_term hq0 hq hbcd).eqOn_of_preconnected_of_eventuallyEq
    (analyticOnNhd_productSide hq0 hq hbcd) (convex_ball (0 : ℂ) _).isPreconnected
    (Metric.mem_ball_self (inv_pos.mpr hT)) hnear
  apply heq
  have H : ‖a * q / (b * c * d)‖ < 1 := by
    rwa [norm_div, div_lt_one (norm_pos_iff.mpr hbcd)]
  have H' : ‖a‖ * ‖q / (b * c * d)‖ < 1 := by
    simpa only [show a * q / (b * c * d) = a * (q / (b * c * d)) by ring, norm_mul] using H
  simpa only [mem_ball_zero_iff, ← one_div] using
    (lt_div_iff₀ hT).mpr H'

end DLMF.QHypergeometric.SixPhiFiveCleared
