/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.CubicTools
public import DLMFMathlib.Analysis.Complex.SegmentPrimitive
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

/-!
# Quadratic connection formulas (DLMF §15.8(iv))

## Main results

* `quadratic_connection_well_poised`, `quadratic_connection_half_sum`,
  `quadratic_connection_complementary`: DLMF 15.8.24–15.8.26.
* `quadratic_even_connection`, `quadratic_odd_connection`: DLMF 15.8.27–15.8.28.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace DLMF.Hypergeometric

/-- `1/2` is not an integer. -/
theorem half_not_int : ∀ k : ℤ, (1 / 2 : ℂ) ≠ (k : ℂ) := by
  intro k h
  have h2 : (1 : ℝ) = 2 * k := by
    have := congrArg Complex.re h
    simp at this
    linarith
  have : (1 : ℤ) = 2 * k := by exact_mod_cast h2
  omega

/-- Identity under the stated parameter and domain assumptions: `₂F₁ a b (a - b + 1) z = (1 - z) ^
(-a) * Gamma (a - b + 1) * Gamma (1 / 2) / (Gamma ((a + 1) / 2) * Gamma (a / 2 - b + 1)) * ₂F₁
(a / 2) (a / 2 - b + 1 / 2) (1 / 2) (((z + 1) / (z - 1)) ^ 2) + (1 + z) * (1 - z) ^ (-a - 1) *
Gamma (a - b + 1) * Gamma (-1 / 2) / (Gamma (a / 2) * Gamma (a / 2 - b + 1 / 2)) * ₂F₁ ((a +
1) / 2) (a / 2 - b + 1) (3 / 2) (((z + 1) / (z - 1)) ^ 2)`. -/
@[dlmf 15.8.E24]
theorem quadratic_connection_well_poised
    {a b z : ℂ}
    (hc : ∀ k : ℕ, a - b + 1 ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hw : ‖((z + 1) /
    (z - 1)) ^ 2‖ < 1) :
    ₂F₁ a b (a - b + 1) z =
      (1 - z) ^ (-a) * Gamma (a - b + 1) * Gamma (1 / 2) /
          (Gamma ((a + 1) / 2) * Gamma (a / 2 - b + 1)) *
        ₂F₁ (a / 2) (a / 2 - b + 1 / 2) (1 / 2) (((z + 1) / (z - 1)) ^ 2) +
      (1 + z) * (1 - z) ^ (-a - 1) * Gamma (a - b + 1) * Gamma (-1 / 2) /
          (Gamma (a / 2) * Gamma (a / 2 - b
        + 1 / 2)) * ₂F₁ ((a + 1) / 2) (a / 2 - b + 1) (3 / 2) (((z + 1) / (z - 1)) ^ 2) := by
  set C := a - b + 1 with hCdef
  set q : ℂ → ℂ := fun z => ((z + 1) / (z - 1)) ^ 2 with hqdef
  set E : ℂ → ℂ := fun z =>
    (1 - z) ^ (-a) * Gamma C * Gamma (1 / 2) / (Gamma ((a + 1) / 2) * Gamma (a / 2 - b + 1)) *
        ₂F₁ (a / 2) (a / 2 - b + 1 / 2) (1 / 2) (q z) +
      (1 + z) * (1 - z) ^ (-a - 1) * Gamma C * Gamma (-1 / 2) /
        (Gamma (a / 2) * Gamma (a / 2 - b + 1 / 2)) *
        ₂F₁ ((a + 1) / 2) (a / 2 - b + 1) (3 / 2) (q z) with hE
  set D : Set ℂ := {z | ‖z‖ < 1 ∧ ‖((z + 1) / (z - 1)) ^ 2‖ < 1} with hD
  have hDc : Convex ℝ D := by
    have : D = Metric.ball 0 1 ∩ {z : ℂ | z.re < 0} := by
      ext z
      simp only [hD, Set.mem_ofPred_eq, Set.mem_inter_iff, Metric.mem_ball, dist_zero_right]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        have hz1 : z - 1 ≠ 0 := by
          intro h; have : z = 1 := by linear_combination h
          rw [this] at h1; simp at h1
        rw [norm_pow, norm_div] at h2
        have h3 : ‖z + 1‖ < ‖z - 1‖ := by
          have hp : 0 < ‖z - 1‖ := norm_pos_iff.mpr hz1
          have : ‖z + 1‖ / ‖z - 1‖ < 1 := by
            nlinarith [div_nonneg (norm_nonneg (z + 1)) hp.le]
          rwa [div_lt_one hp] at this
        have h4 := (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h3
        rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq, normSq_apply, normSq_apply] at h4
        simp at h4
        nlinarith
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        have hz1 : z - 1 ≠ 0 := by
          intro h; have : z = 1 := by linear_combination h
          rw [this] at h2; simp at h2; linarith
        have hp : 0 < ‖z - 1‖ := norm_pos_iff.mpr hz1
        have h3 : ‖z + 1‖ < ‖z - 1‖ := by
          rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), ← normSq_eq_norm_sq,
            ← normSq_eq_norm_sq, normSq_apply, normSq_apply]
          simp; nlinarith
        rw [norm_pow, norm_div]
        have : ‖z + 1‖ / ‖z - 1‖ < 1 := by rwa [div_lt_one hp]
        have h0 : 0 ≤ ‖z + 1‖ / ‖z - 1‖ := by positivity
        nlinarith
    rw [this]
    exact (convex_ball 0 1).inter (convex_halfSpace_re_lt 0)
  -- The chain near `z = -1/5`.
  have hloc : ∀ z ∈ Metric.ball (-1 / 5 : ℂ) (1 / 20), ₂F₁ a b C z = E z := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm, show z - -1 / 5 = z + 1 / 5 by ring] at hz
    have hre : z.re < -3 / 20 := by
      have := re_le_norm (z + 1 / 5)
      simp only [add_re, div_re, one_re, re_ofNat, im_ofNat, normSq_ofNat] at this
      norm_num at this
      linarith
    have hzn : ‖z‖ ≤ 1 / 4 := by
      calc ‖z‖ = ‖(z + 1 / 5) + (-1 / 5)‖ := by ring_nf
        _ ≤ ‖z + 1 / 5‖ + ‖(-1 / 5 : ℂ)‖ := norm_add_le _ _
        _ ≤ 1 / 4 := by rw [show ‖(-1 / 5 : ℂ)‖ = 1 / 5 by norm_num]; linarith
    have hz1 : 23 / 20 ≤ ‖z - 1‖ := by
      have := neg_le_of_abs_le (abs_re_le_norm (z - 1))
      simp only [sub_re, one_re] at this; linarith
    have hz1' : 0 < ‖1 - z‖ := by rw [norm_sub_rev]; linarith
    have hzp : ‖z + 1‖ ≤ 9 / 10 := by
      calc ‖z + 1‖ = ‖(z + 1 / 5) + (4 / 5 : ℂ)‖ := by ring_nf
        _ ≤ ‖z + 1 / 5‖ + ‖(4 / 5 : ℂ)‖ := norm_add_le _ _
        _ ≤ 9 / 10 := by rw [show ‖(4 / 5 : ℂ)‖ = 4 / 5 by norm_num]; linarith
    have hzl : ‖z‖ < 1 := by linarith
    have h1z : 1 - z ≠ 0 := norm_pos_iff.mp hz1'
    have hzm1 : z - 1 ≠ 0 := by intro h; apply h1z; linear_combination -h
    have hvn : ‖-4 * z / (1 - z) ^ 2‖ < 1 := by
      rw [norm_div, norm_mul, norm_pow, show ‖(-4 : ℂ)‖ = 4 by norm_num, norm_sub_rev,
        div_lt_one (by positivity)]
      nlinarith [norm_nonneg z]
    have hqv : 1 - -4 * z / (1 - z) ^ 2 = q z := by
      simp only [hqdef]
      rw [div_pow, show (z - 1) ^ 2 = (1 - z) ^ 2 by ring]
      field_simp
      ring
    have hqn : ‖q z‖ < 1 := by
      simp only [hqdef]
      rw [norm_pow, norm_div]
      have : ‖z + 1‖ / ‖z - 1‖ < 1 := by rw [div_lt_one (by linarith)]; linarith
      have h0 : 0 ≤ ‖z + 1‖ / ‖z - 1‖ := by positivity
      nlinarith
    have h16 := quadratic_well_poised_minus (a := a) (b := b) hc hzl hvn
    have hconn := zero_first_connection_one_of_not_neg_nat (a := a / 2) (b := a / 2 - b + 1 / 2)
      (c := C) hc
      (by rw [show C - a / 2 - (a / 2 - b + 1 / 2) = 1 / 2 by rw [hCdef]; ring]; exact half_not_int)
      hvn (by rw [hqv]; exact hqn)
    rw [h16, hconn]
    simp only [oneFirst, oneSecond, hE]
    have hsq : q z = ((1 + z) / (1 - z)) ^ 2 := by
      simp only [hqdef]; rw [div_pow, div_pow]; ring
    have hrez : 0 < ((1 + z) / (1 - z)).re := by
      have := re_one_sub_div_one_add_pos (z := -z) (by rwa [norm_neg])
      rwa [show (1 - -z) / (1 + -z) = (1 + z) / (1 - z) by ring] at this
    rw [hqv, show C - a / 2 - (a / 2 - b + 1 / 2) = 1 / 2 by rw [hCdef]; ring,
      show a / 2 + (a / 2 - b + 1 / 2) - C + 1 = 1 / 2 by rw [hCdef]; ring,
      show a / 2 + (a / 2 - b + 1 / 2) - C = -1 / 2 by rw [hCdef]; ring,
      show C - a / 2 = a / 2 - b + 1 by rw [hCdef]; ring,
      show C - (a / 2 - b + 1 / 2) = (a + 1) / 2 by rw [hCdef]; ring,
      show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num,
      ordinaryHypergeometric_symm (a / 2 - b + 1), hsq, sq_cpow_half hrez,
      show (1 - z) ^ (-a - 1) = (1 - z) ^ (-a) / (1 - z) by rw [cpow_sub _ _ h1z, cpow_one]]
    ring
  have hLan : AnalyticOnNhd ℂ (₂F₁ a b C : ℂ → ℂ) D := fun z hz =>
    analyticAt_ordinaryHypergeometric hz.1
  have hRan : AnalyticOnNhd ℂ E D := by
    intro z hz
    have hz1 : z - 1 ≠ 0 := by
      intro h; have : z = 1 := by linear_combination h
      rw [this] at hz; simp [hD] at hz
    have hslit : 1 - z ∈ slitPlane := by
      refine mem_slitPlane_iff.mpr (Or.inl ?_)
      have := (re_le_norm z).trans_lt hz.1
      simp only [sub_re, one_re]; linarith
    have hqa : AnalyticAt ℂ q z :=
      ((analyticAt_id.add analyticAt_const).div (analyticAt_id.sub analyticAt_const) hz1).pow 2
    have h1 := (analyticAt_ordinaryHypergeometric (a := a / 2) (b := a / 2 - b + 1 / 2)
      (c := 1 / 2) hz.2).comp (f := q) hqa
    have h2 := (analyticAt_ordinaryHypergeometric (a := (a + 1) / 2) (b := a / 2 - b + 1)
      (c := 3 / 2) hz.2).comp (f := q) hqa
    have hp1 : AnalyticAt ℂ (fun z : ℂ => (1 - z) ^ (-a)) z :=
      (analyticAt_const.sub analyticAt_id).cpow analyticAt_const hslit
    have hp2 : AnalyticAt ℂ (fun z : ℂ => (1 - z) ^ (-a - 1)) z :=
      (analyticAt_const.sub analyticAt_id).cpow analyticAt_const hslit
    exact ((hp1.mul analyticAt_const).mul analyticAt_const).div_const.mul h1 |>.add
      ((((analyticAt_const.add analyticAt_id).mul hp2).mul analyticAt_const).mul
        analyticAt_const |>.div_const |>.mul h2)
  have h0 : (-1 / 5 : ℂ) ∈ D := by
    refine ⟨by norm_num, ?_⟩
    rw [norm_pow, norm_div]
    norm_num
  have hev : (₂F₁ a b C : ℂ → ℂ) =ᶠ[𝓝 (-1 / 5)] E := by
    filter_upwards [Metric.ball_mem_nhds (-1 / 5 : ℂ) (by norm_num : (0 : ℝ) < 1 / 20)] with z hz
    exact hloc z hz
  exact hLan.eqOn_of_preconnected_of_eventuallyEq hRan hDc.isPreconnected h0 hev ⟨hz, hw⟩

/-- Identity under the stated parameter and domain assumptions: `₂F₁ a b ((a + b + 1) / 2) z =
Gamma ((a + b + 1) / 2) * Gamma (1 / 2) / (Gamma ((a + 1) / 2) * Gamma ((b + 1) / 2)) * ₂F₁ (a
/ 2) (b / 2) (1 / 2) ((1 - 2 * z) ^ 2) + (1 - 2 * z) * Gamma ((a + b + 1) / 2) * Gamma (-1 /
2) / (Gamma (a / 2) * Gamma (b / 2)) * ₂F₁ ((a + 1) / 2) ((b + 1) / 2) (3 / 2) ((1 - 2 * z) ^
2)`. -/
@[dlmf 15.8.E25]
theorem quadratic_connection_half_sum
    {a b z : ℂ}
    (hc : ∀ k : ℕ,
    (a + b + 1) / 2 ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hw : ‖(1 - 2 * z) ^ 2‖ < 1) :
    ₂F₁ a b ((a + b + 1) / 2) z =
      Gamma ((a + b + 1) / 2) * Gamma (1 / 2) /
          (Gamma ((a + 1) / 2) * Gamma ((b + 1) / 2)) * ₂F₁ (a / 2) (b
        / 2) (1 / 2) ((1 - 2 * z) ^ 2) +
      (1 - 2 * z) * Gamma ((a + b + 1) / 2) * Gamma (-1 / 2) /
          (Gamma (a / 2) * Gamma (b / 2)) * ₂F₁ ((a +
        1) / 2) ((b + 1) / 2) (3 / 2) ((1 - 2 * z) ^ 2) := by
  set C := (a + b + 1) / 2 with hCdef
  set E : ℂ → ℂ := fun z => Gamma C * Gamma (1 / 2) / (Gamma ((a + 1) / 2) * Gamma ((b + 1) / 2)) *
      ₂F₁ (a / 2) (b / 2) (1 / 2) ((1 - 2 * z) ^ 2) +
    (1 - 2 * z) * Gamma C * Gamma (-1 / 2) / (Gamma (a / 2) * Gamma (b / 2)) *
      ₂F₁ ((a + 1) / 2) ((b + 1) / 2) (3 / 2) ((1 - 2 * z) ^ 2) with hE
  set D : Set ℂ := {z | ‖z‖ < 1 ∧ ‖(1 - 2 * z) ^ 2‖ < 1} with hD
  have hDc : Convex ℝ D := by
    have : D = Metric.ball 0 1 ∩ {z : ℂ | ‖1 - 2 * z‖ < 1} := by
      ext z
      simp only [hD, Set.mem_ofPred_eq, Set.mem_inter_iff, Metric.mem_ball, dist_zero_right,
        norm_pow]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, by nlinarith [norm_nonneg (1 - 2 * z)]⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, by nlinarith [norm_nonneg (1 - 2 * z)]⟩
    rw [this]
    refine (convex_ball 0 1).inter ?_
    have : {z : ℂ | ‖1 - 2 * z‖ < 1} = Metric.ball (1 / 2) (1 / 2) := by
      ext z
      simp only [Set.mem_ofPred_eq, Metric.mem_ball, dist_eq_norm]
      rw [show (1 : ℂ) - 2 * z = -2 * (z - 1 / 2) by ring, norm_mul, norm_neg,
        show ‖(2 : ℂ)‖ = 2 by norm_num]
      constructor <;> intro h <;> linarith
    rw [this]; exact convex_ball _ _
  -- The chain near `z = 1/4`.
  have hloc : ∀ z ∈ Metric.ball (1 / 4 : ℂ) (1 / 16), ₂F₁ a b C z = E z := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    set δ := z - 1 / 4 with hδ
    have hzδ : z = 1 / 4 + δ := by rw [hδ]; ring
    have hzn : ‖z‖ < 1 := by
      rw [hzδ]; calc ‖(1 / 4 : ℂ) + δ‖ ≤ ‖(1 / 4 : ℂ)‖ + ‖δ‖ := norm_add_le _ _
        _ < 1 := by rw [show ‖(1 / 4 : ℂ)‖ = 1 / 4 by norm_num]; linarith
    have hre : z.re < 1 / 2 := by
      have := re_le_norm δ
      rw [hzδ]; simp; linarith
    have h1 : ‖1 - 2 * z‖ ≤ 5 / 8 := by
      rw [hzδ, show (1 : ℂ) - 2 * (1 / 4 + δ) = 1 / 2 - 2 * δ by ring]
      calc ‖(1 / 2 : ℂ) - 2 * δ‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖2 * δ‖ := norm_sub_le _ _
        _ ≤ 5 / 8 := by
          rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num, show ‖(2 : ℂ)‖ = 2 by norm_num]
          linarith
    have hw1 : ‖(1 - 2 * z) ^ 2‖ < 1 := by
      rw [norm_pow]; nlinarith [norm_nonneg (1 - 2 * z)]
    have hwn : ‖4 * z * (1 - z)‖ < 1 := by
      rw [show 4 * z * (1 - z) = 3 / 4 + (2 * δ - 4 * δ ^ 2) by rw [hzδ]; ring]
      calc ‖(3 / 4 : ℂ) + (2 * δ - 4 * δ ^ 2)‖ ≤ ‖(3 / 4 : ℂ)‖ + ‖2 * δ - 4 * δ ^ 2‖ :=
            norm_add_le _ _
        _ ≤ 3 / 4 + (2 * ‖δ‖ + 4 * ‖δ‖ ^ 2) := by
            rw [show ‖(3 / 4 : ℂ)‖ = 3 / 4 by norm_num]
            gcongr
            calc ‖2 * δ - 4 * δ ^ 2‖ ≤ ‖2 * δ‖ + ‖4 * δ ^ 2‖ := norm_sub_le _ _
              _ = 2 * ‖δ‖ + 4 * ‖δ‖ ^ 2 := by
                rw [norm_mul, norm_mul, norm_pow, show ‖(2 : ℂ)‖ = 2 by norm_num,
                  show ‖(4 : ℂ)‖ = 4 by norm_num]
        _ < 1 := by nlinarith [norm_nonneg δ]
    have hq := gauss_quadratic (a := a / 2) (b := b / 2)
      (by rw [show a / 2 + b / 2 + 1 / 2 = C by rw [hCdef]; ring]; exact hc) hzn hwn hre
    rw [show a / 2 + b / 2 + 1 / 2 = C by rw [hCdef]; ring, show 2 * (a / 2) = a by ring,
      show 2 * (b / 2) = b by ring] at hq
    have hlens : ‖1 - 4 * z * (1 - z)‖ < 1 := by
      rw [show 1 - 4 * z * (1 - z) = (1 - 2 * z) ^ 2 by ring]; exact hw1
    have hconn := zero_first_connection_one_of_not_neg_nat (a := a / 2) (b := b / 2) (c := C)
      hc (by rw [show C - a / 2 - b / 2 = 1 / 2 by rw [hCdef]; ring]; exact half_not_int) hwn hlens
    rw [hq, hconn]
    simp only [oneFirst, oneSecond, hE]
    have hsq : 1 - 4 * z * (1 - z) = (1 - 2 * z) ^ 2 := by ring
    have hrez : 0 < (1 - 2 * z).re := by simp; linarith
    rw [hsq, show C - a / 2 - b / 2 = 1 / 2 by rw [hCdef]; ring,
      show a / 2 + b / 2 - C + 1 = 1 / 2 by rw [hCdef]; ring,
      show a / 2 + b / 2 - C = -1 / 2 by rw [hCdef]; ring,
      show C - a / 2 = (b + 1) / 2 by rw [hCdef]; ring,
      show C - b / 2 = (a + 1) / 2 by rw [hCdef]; ring,
      show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num, sq_cpow_half hrez,
      ordinaryHypergeometric_symm ((b + 1) / 2)]
    ring
  have hLan : AnalyticOnNhd ℂ (₂F₁ a b C : ℂ → ℂ) D := fun z hz =>
    analyticAt_ordinaryHypergeometric hz.1
  have hRan : AnalyticOnNhd ℂ E D := by
    intro z hz
    have h1 := analyticAt_ordinaryHypergeometric (a := a / 2) (b := b / 2) (c := 1 / 2) hz.2
    have h2 := analyticAt_ordinaryHypergeometric (a := (a + 1) / 2) (b := (b + 1) / 2)
      (c := 3 / 2) hz.2
    have hp : AnalyticAt ℂ (fun z : ℂ => (1 - 2 * z) ^ 2) z :=
      (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).pow 2
    exact (analyticAt_const.mul (h1.comp (f := fun z : ℂ => (1 - 2 * z) ^ 2) hp)).add
      ((((analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).mul analyticAt_const).mul
        analyticAt_const).div_const |>.mul (h2.comp (f := fun z : ℂ => (1 - 2 * z) ^ 2) hp))
  have h14 : (1 / 4 : ℂ) ∈ D := by
    refine ⟨by norm_num, ?_⟩
    rw [norm_pow]; norm_num
  have hev : (₂F₁ a b C : ℂ → ℂ) =ᶠ[𝓝 (1 / 4)] E := by
    filter_upwards [Metric.ball_mem_nhds (1 / 4 : ℂ) (by norm_num : (0 : ℝ) < 1 / 16)] with z hz
    exact hloc z hz
  exact hLan.eqOn_of_preconnected_of_eventuallyEq hRan hDc.isPreconnected h14 hev ⟨hz, hw⟩

/-- Identity under the stated parameter and domain assumptions: `₂F₁ a (1 - a) c z = (1 - z) ^ (c
- 1) * Gamma c * Gamma (1 / 2) / (Gamma ((c - a + 1) / 2) * Gamma ((c + a) / 2)) * ₂F₁ ((c -
a) / 2) ((c + a - 1) / 2) (1 / 2) ((1 - 2 * z) ^ 2) + (1 - 2 * z) * (1 - z) ^ (c - 1) * Gamma
c * Gamma (-1 / 2) / (Gamma ((c - a) / 2) * Gamma ((c + a - 1) / 2)) * ₂F₁ ((c - a + 1) / 2)
((c + a) / 2) (3 / 2) ((1 - 2 * z) ^ 2)`. -/
@[dlmf 15.8.E26]
theorem quadratic_connection_complementary
    {a c z : ℂ}
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hw : ‖(1 - 2 * z) ^ 2‖ < 1) :
    ₂F₁ a (1 - a) c z =
      (1 - z) ^ (c - 1) * Gamma c * Gamma (1 / 2) /
          (Gamma ((c - a + 1) / 2) * Gamma ((c + a) / 2)) * ₂F₁
        ((c - a) / 2) ((c + a - 1) / 2) (1 / 2) ((1 - 2 * z) ^ 2) +
      (1 - 2 * z) * (1 - z) ^ (c - 1) * Gamma c * Gamma (-1 / 2) /
          (Gamma ((c - a) / 2) * Gamma ((c + a - 1)
        / 2)) * ₂F₁ ((c - a + 1) / 2) ((c + a) / 2) (3 / 2) ((1 - 2 * z) ^ 2) := by
  have h := quadratic_connection_half_sum (a := c - a) (b := c + a - 1)
    (by rw [show (c - a + (c + a - 1) + 1) / 2 = c by ring]; exact hc) hz hw
  rw [show (c - a + (c + a - 1) + 1) / 2 = c by ring, show (c + a - 1 + 1) / 2 =
                                                  (c + a) / 2 by ring]
    at h
  rw [euler_transformation_of_ne_neg_nat hc hz, show c - a - (1 - a) = c - 1 by ring,
    show c - (1 - a) = c + a - 1 by ring, h]
  ring

/-- The complementary quadratic connection, regularized in every lower parameter.
Analyticity along parameter curves extends the ordinary formula through Gamma poles. -/
theorem regularized_quadratic_connection_complementary (a c : ℂ) {z : ℂ}
    (hz : ‖z‖<1) (hw : ‖(1-2*z)^2‖<1) :
    regularizedGaussHGFun a (1-a) c z=
      (1-z)^(c-1)*Gamma (1/2)^2*(1/Gamma ((c-a+1)/2))*(1/Gamma ((c+a)/2))*
        regularizedGaussHGFun ((c-a)/2) ((c+a-1)/2) (1/2) ((1-2*z)^2)+
      (1-2*z)*(1-z)^(c-1)*(Gamma (-1/2)*Gamma (3/2))*
        (1/Gamma ((c-a)/2))*(1/Gamma ((c+a-1)/2))*
        regularizedGaussHGFun ((c-a+1)/2) ((c+a)/2) (3/2) ((1-2*z)^2) := by
  have hb : 1-z≠0 := by
    intro h
    have he : z=1 := by linear_combination -h
    rw [he] at hz
    norm_num at hz
  have hP : Differentiable ℂ (fun c : ℂ=>(1-z)^(c-1)) := by
    have he : (fun c : ℂ=>(1-z)^(c-1))=(fun c=>exp (log (1-z)*(c-1))) :=
      funext fun c=>cpow_def_of_ne_zero hb (c-1)
    rw [he]
    fun_prop
  have h1 : Differentiable ℂ (fun c : ℂ=>1/Gamma ((c-a+1)/2)) := by
    simpa only [Function.comp_def, one_div] using differentiable_one_div_Gamma.comp
      (show Differentiable ℂ (fun c : ℂ=>(c-a+1)/2) by fun_prop)
  have h2 : Differentiable ℂ (fun c : ℂ=>1/Gamma ((c+a)/2)) := by
    simpa only [Function.comp_def, one_div] using differentiable_one_div_Gamma.comp
      (show Differentiable ℂ (fun c : ℂ=>(c+a)/2) by fun_prop)
  have h3 : Differentiable ℂ (fun c : ℂ=>1/Gamma ((c-a)/2)) := by
    simpa only [Function.comp_def, one_div] using differentiable_one_div_Gamma.comp
      (show Differentiable ℂ (fun c : ℂ=>(c-a)/2) by fun_prop)
  have h4 : Differentiable ℂ (fun c : ℂ=>1/Gamma ((c+a-1)/2)) := by
    simpa only [Function.comp_def, one_div] using differentiable_one_div_Gamma.comp
      (show Differentiable ℂ (fun c : ℂ=>(c+a-1)/2) by fun_prop)
  have hG1 : Differentiable ℂ
      (fun c : ℂ=>regularizedGaussHGFun ((c-a)/2) ((c+a-1)/2) (1/2) ((1-2*z)^2)) :=
    fun c=>(analyticOnNhd_regularizedGaussHypergeometricFun_comp (by fun_prop) (by fun_prop)
      (differentiable_const (1/2)) hw c (Set.mem_univ c)).differentiableAt
  have hG2 : Differentiable ℂ
      (fun c : ℂ=>regularizedGaussHGFun ((c-a+1)/2) ((c+a)/2) (3/2) ((1-2*z)^2)) :=
    fun c=>(analyticOnNhd_regularizedGaussHypergeometricFun_comp (by fun_prop) (by fun_prop)
      (differentiable_const (3/2)) hw c (Set.mem_univ c)).differentiableAt
  have he := Complex.eq_of_differentiable_of_eqOn_pos_reals
    (f:=fun c=>regularizedGaussHGFun a (1-a) c z)
    (g:=fun c=>(1-z)^(c-1)*Gamma (1/2)^2*(1/Gamma ((c-a+1)/2))*(1/Gamma ((c+a)/2))*
      regularizedGaussHGFun ((c-a)/2) ((c+a-1)/2) (1/2) ((1-2*z)^2)+
      (1-2*z)*(1-z)^(c-1)*(Gamma (-1/2)*Gamma (3/2))*(1/Gamma ((c-a)/2))*
      (1/Gamma ((c+a-1)/2))*regularizedGaussHGFun ((c-a+1)/2) ((c+a)/2) (3/2) ((1-2*z)^2))
    (fun c=>(analyticOnNhd_regularizedGaussHypergeometricFun_c a (1-a) hz c
        (Set.mem_univ c)).differentiableAt)
    (by fun_prop) (fun x hx=>?_)
  · exact congrFun he c
  · have hc : ∀ k : ℕ, (x:ℂ)≠-k := by
      intro k h
      have h' := congrArg Complex.re h
      simp at h'
      linarith [show (0:ℝ)≤k by positivity]
    have hhalf : ∀ k : ℕ, (1/2:ℂ)≠-k := by
      intro k h
      have h' := congrArg Complex.re h
      simp at h'
      linarith [show (0:ℝ)≤k by positivity]
    have hthree : ∀ k : ℕ, (3/2:ℂ)≠-k := by
      intro k h
      have h' := congrArg Complex.re h
      simp at h'
      linarith [show (0:ℝ)≤k by positivity]
    rw [regularizedGaussHypergeometricFun_eq_div_Gamma hc,
        regularizedGaussHypergeometricFun_eq_div_Gamma hhalf,
      regularizedGaussHypergeometricFun_eq_div_Gamma hthree,
          quadratic_connection_complementary hc hz hw]
    simp only [div_eq_mul_inv, mul_inv_rev]
    have hGc := Gamma_ne_zero hc
    have hGh := Gamma_ne_zero hhalf
    have hGt := Gamma_ne_zero hthree
    field_simp [hGc, hGh, hGt]

/-- Identity under the stated parameter and domain assumptions: `2 * Gamma (1 / 2) * Gamma (a + b
+ 1 / 2) / (Gamma (a + 1 / 2) * Gamma (b + 1 / 2)) * ₂F₁ a b (1 / 2) (x : ℂ) = ₂F₁ (2 * a) (2
* b) (a + b + 1 / 2) ((1 - Real.sqrt x) / 2 : ℂ) + ₂F₁ (2 * a) (2 * b) (a + b + 1 / 2) ((1 +
Real.sqrt x) / 2 : ℂ)`. -/
@[dlmf 15.8.E27]
theorem quadratic_even_connection
    {a b : ℂ}
    {x : ℝ}
    (hc : ∀ k : ℕ, a + b + 1 / 2 ≠ -(k : ℂ))
    (hx : 0 < x)
    (hx1 : x < 1) :
    2 * Gamma (1 / 2) * Gamma (a + b + 1 / 2) / (Gamma (a + 1 / 2) * Gamma (b + 1 / 2)) *
        ₂F₁ a b (1 / 2) (x
      : ℂ) =
      ₂F₁ (2 * a) (2 * b) (a + b + 1 / 2) ((1 - Real.sqrt x) / 2 : ℂ) +
          ₂F₁ (2 * a) (2 * b) (a + b + 1 / 2)
        ((1 + Real.sqrt x) / 2 : ℂ) := by
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hs1 : Real.sqrt x < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt hx.le hx1
  have hsq : ((Real.sqrt x : ℂ)) ^ 2 = (x : ℂ) := by
    rw [← ofReal_pow, Real.sq_sqrt hx.le]
  have hm : ‖((1 - Real.sqrt x) / 2 : ℂ)‖ < 1 := by
    rw [show ((1 - Real.sqrt x) / 2 : ℂ) = (((1 - Real.sqrt x) / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  have hp : ‖((1 + Real.sqrt x) / 2 : ℂ)‖ < 1 := by
    rw [show ((1 + Real.sqrt x) / 2 : ℂ) = (((1 + Real.sqrt x) / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  have hxn : ‖(x : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]; exact hx1
  have em : (1 - 2 * ((1 - Real.sqrt x) / 2 : ℂ)) = (Real.sqrt x : ℂ) := by ring
  have ep : (1 - 2 * ((1 + Real.sqrt x) / 2 : ℂ)) = -(Real.sqrt x : ℂ) := by ring
  have hc' : ∀ k : ℕ, (2 * a + 2 * b + 1) / 2 ≠ -(k : ℂ) := by
    rw [show (2 * a + 2 * b + 1) / 2 = a + b + 1 / 2 by ring]; exact hc
  have h1 := quadratic_connection_half_sum (a := 2 * a) (b := 2 * b) hc' hm
    (by rw [em, hsq]; exact hxn)
  have h2 := quadratic_connection_half_sum (a := 2 * a) (b := 2 * b) hc' hp
    (by rw [ep, neg_sq, hsq]; exact hxn)
  rw [em, hsq] at h1
  rw [ep, neg_sq, hsq] at h2
  simp only [show (2 * a + 2 * b + 1) / 2 = a + b + 1 / 2 by ring,
    show (2 * a + 1) / 2 = a + 1 / 2 by ring, show (2 * b + 1) / 2 = b + 1 / 2 by ring,
    show 2 * a / 2 = a by ring, show 2 * b / 2 = b by ring] at h1 h2
  rw [h1, h2]
  ring

/-- Identity under the stated parameter and domain assumptions: `2 * (Real.sqrt x : ℂ) * Gamma (-1
/ 2) * Gamma (a + b - 1 / 2) / (Gamma (a - 1 / 2) * Gamma (b - 1 / 2)) * ₂F₁ a b (3 / 2) (x :
ℂ) = ₂F₁ (2 * a - 1) (2 * b - 1) (a + b - 1 / 2) ((1 - Real.sqrt x) / 2 : ℂ) - ₂F₁ (2 * a - 1)
(2 * b - 1) (a + b - 1 / 2) ((1 + Real.sqrt x) / 2 : ℂ)`. -/
@[dlmf 15.8.E28]
theorem quadratic_odd_connection
    {a b : ℂ}
    {x : ℝ}
    (hc : ∀ k : ℕ, a + b - 1 / 2 ≠ -(k : ℂ))
    (hx : 0 < x)
    (hx1 : x < 1) :
    2 * (Real.sqrt x : ℂ) * Gamma (-1 / 2) * Gamma (a + b - 1 / 2) /
        (Gamma (a - 1 / 2) * Gamma (b - 1 / 2))
      * ₂F₁ a b (3 / 2) (x : ℂ) =
      ₂F₁ (2 * a - 1) (2 * b - 1) (a + b - 1 / 2) ((1 - Real.sqrt x) / 2 : ℂ) -
          ₂F₁ (2 * a - 1) (2 * b - 1)
        (a + b - 1 / 2) ((1 + Real.sqrt x) / 2 : ℂ) := by
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hs1 : Real.sqrt x < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt hx.le hx1
  have hsq : ((Real.sqrt x : ℂ)) ^ 2 = (x : ℂ) := by
    rw [← ofReal_pow, Real.sq_sqrt hx.le]
  have hm : ‖((1 - Real.sqrt x) / 2 : ℂ)‖ < 1 := by
    rw [show ((1 - Real.sqrt x) / 2 : ℂ) = (((1 - Real.sqrt x) / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  have hp : ‖((1 + Real.sqrt x) / 2 : ℂ)‖ < 1 := by
    rw [show ((1 + Real.sqrt x) / 2 : ℂ) = (((1 + Real.sqrt x) / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  have hxn : ‖(x : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]; exact hx1
  have em : (1 - 2 * ((1 - Real.sqrt x) / 2 : ℂ)) = (Real.sqrt x : ℂ) := by ring
  have ep : (1 - 2 * ((1 + Real.sqrt x) / 2 : ℂ)) = -(Real.sqrt x : ℂ) := by ring
  have hc' : ∀ k : ℕ, (2 * a - 1 + (2 * b - 1) + 1) / 2 ≠ -(k : ℂ) := by
    rw [show (2 * a - 1 + (2 * b - 1) + 1) / 2 = a + b - 1 / 2 by ring]; exact hc
  have h1 := quadratic_connection_half_sum (a := 2 * a - 1) (b := 2 * b - 1) hc' hm
    (by rw [em, hsq]; exact hxn)
  have h2 := quadratic_connection_half_sum (a := 2 * a - 1) (b := 2 * b - 1) hc' hp
    (by rw [ep, neg_sq, hsq]; exact hxn)
  rw [em, hsq] at h1
  rw [ep, neg_sq, hsq] at h2
  simp only [show (2 * a - 1 + (2 * b - 1) + 1) / 2 = a + b - 1 / 2 by ring,
    show (2 * a - 1 + 1) / 2 = a by ring, show (2 * b - 1 + 1) / 2 = b by ring,
    show (2 * a - 1) / 2 = a - 1 / 2 by ring, show (2 * b - 1) / 2 = b - 1 / 2 by ring] at h1 h2
  rw [h1, h2]
  ring

end DLMF.Hypergeometric
