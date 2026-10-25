/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.FurtherTransformations
public import DLMF.Hypergeometric.CubicTools
public import DLMFMathlib.Analysis.Complex.SegmentPrimitive
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Quadratic and logarithmic connection formulas (DLMF §15.8)

The logarithmic formulas are stated on intersections of convergence regions.
Nonintegrality assumptions avoid products involving the totalized value of
digamma at its poles. They can later be weakened using the source's explicitly
prescribed limits. Finite sums use `range m`, including the empty sum at `m = 0`.

The cubic connection formula 15.8.32 is proved in the variable `u = 1/ζ` with the tools of
`DLMF.Hypergeometric.CubicTools`: Goursat's cubic transformation near `u = 0`, the connection
15.10.17 continued in `a`, the identity theorem on `{Im u > 0, |u| < 1}`, and a check of
principal branches on the image of the ray `x < -1`.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace DLMF.Hypergeometric

lemma half_not_int : ∀ k : ℤ, (1 / 2 : ℂ) ≠ (k : ℂ) := by
  intro k h
  have h2 : (1 : ℝ) = 2 * k := by
    have := congrArg Complex.re h
    simp at this
    linarith
  have : (1 : ℤ) = 2 * k := by exact_mod_cast h2
  omega

lemma neg_half_not_int : ∀ k : ℤ, (-1 / 2 : ℂ) ≠ (k : ℂ) := by
  intro k h
  apply half_not_int (-k)
  push_cast
  linear_combination -h

@[dlmf 15.8.E24]
theorem quadratic_connection_well_poised
    {a b z : ℂ}
    (hc : ∀ k : ℕ, a - b + 1 ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hw : ‖((z + 1) /
    (z - 1)) ^ 2‖ < 1) :
    ₂F₁ a b (a - b + 1) z =
      (1 - z) ^ (-a) * Gamma (a - b + 1) * Gamma (1 / 2) / (Gamma ((a + 1) / 2) * Gamma (a / 2 - b + 1)) *
        ₂F₁ (a / 2) (a / 2 - b + 1 / 2) (1 / 2) (((z + 1) / (z - 1)) ^ 2) +
      (1 + z) * (1 - z) ^ (-a - 1) * Gamma (a - b + 1) * Gamma (-1 / 2) / (Gamma (a / 2) * Gamma (a / 2 - b
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

@[dlmf 15.8.E25]
theorem quadratic_connection_half_sum
    {a b z : ℂ}
    (hc : ∀ k : ℕ,
    (a + b + 1) / 2 ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hw : ‖(1 - 2 * z) ^ 2‖ < 1) :
    ₂F₁ a b ((a + b + 1) / 2) z =
      Gamma ((a + b + 1) / 2) * Gamma (1 / 2) / (Gamma ((a + 1) / 2) * Gamma ((b + 1) / 2)) * ₂F₁ (a / 2) (b
        / 2) (1 / 2) ((1 - 2 * z) ^ 2) +
      (1 - 2 * z) * Gamma ((a + b + 1) / 2) * Gamma (-1 / 2) / (Gamma (a / 2) * Gamma (b / 2)) * ₂F₁ ((a +
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

@[dlmf 15.8.E26]
theorem quadratic_connection_complementary
    {a c z : ℂ}
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hw : ‖(1 - 2 * z) ^ 2‖ < 1) :
    ₂F₁ a (1 - a) c z =
      (1 - z) ^ (c - 1) * Gamma c * Gamma (1 / 2) / (Gamma ((c - a + 1) / 2) * Gamma ((c + a) / 2)) * ₂F₁
        ((c - a) / 2) ((c + a - 1) / 2) (1 / 2) ((1 - 2 * z) ^ 2) +
      (1 - 2 * z) * (1 - z) ^ (c - 1) * Gamma c * Gamma (-1 / 2) / (Gamma ((c - a) / 2) * Gamma ((c + a - 1)
        / 2)) * ₂F₁ ((c - a + 1) / 2) ((c + a) / 2) (3 / 2) ((1 - 2 * z) ^ 2) := by
  have h := quadratic_connection_half_sum (a := c - a) (b := c + a - 1)
    (by rw [show (c - a + (c + a - 1) + 1) / 2 = c by ring]; exact hc) hz hw
  rw [show (c - a + (c + a - 1) + 1) / 2 = c by ring, show (c + a - 1 + 1) / 2 = (c + a) / 2 by ring]
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
  have hG1 : Differentiable ℂ (fun c : ℂ=>regularizedGaussHGFun ((c-a)/2) ((c+a-1)/2) (1/2) ((1-2*z)^2)) :=
    fun c=>(analyticOnNhd_regularizedGaussHGFun_comp (by fun_prop) (by fun_prop)
      (differentiable_const (1/2)) hw c (Set.mem_univ c)).differentiableAt
  have hG2 : Differentiable ℂ (fun c : ℂ=>regularizedGaussHGFun ((c-a+1)/2) ((c+a)/2) (3/2) ((1-2*z)^2)) :=
    fun c=>(analyticOnNhd_regularizedGaussHGFun_comp (by fun_prop) (by fun_prop)
      (differentiable_const (3/2)) hw c (Set.mem_univ c)).differentiableAt
  have he := Complex.eq_of_differentiable_of_eqOn_pos_reals
    (f:=fun c=>regularizedGaussHGFun a (1-a) c z)
    (g:=fun c=>(1-z)^(c-1)*Gamma (1/2)^2*(1/Gamma ((c-a+1)/2))*(1/Gamma ((c+a)/2))*
      regularizedGaussHGFun ((c-a)/2) ((c+a-1)/2) (1/2) ((1-2*z)^2)+
      (1-2*z)*(1-z)^(c-1)*(Gamma (-1/2)*Gamma (3/2))*(1/Gamma ((c-a)/2))*
      (1/Gamma ((c+a-1)/2))*regularizedGaussHGFun ((c-a+1)/2) ((c+a)/2) (3/2) ((1-2*z)^2))
    (fun c=>(analyticOnNhd_regularizedGaussHGFun_c a (1-a) hz c (Set.mem_univ c)).differentiableAt)
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
    rw [regularizedGaussHGFun_eq_div_Gamma hc,regularizedGaussHGFun_eq_div_Gamma hhalf,
      regularizedGaussHGFun_eq_div_Gamma hthree,quadratic_connection_complementary hc hz hw]
    simp only [div_eq_mul_inv, mul_inv_rev]
    have hGc := Gamma_ne_zero hc
    have hGh := Gamma_ne_zero hhalf
    have hGt := Gamma_ne_zero hthree
    field_simp [hGc, hGh, hGt] <;> ring

@[dlmf 15.8.E27]
theorem quadratic_even_connection
    {a b : ℂ}
    {x : ℝ}
    (hc : ∀ k : ℕ, a + b + 1 / 2 ≠ -(k : ℂ))
    (hx : 0 < x)
    (hx1 : x < 1) :
    2 * Gamma (1 / 2) * Gamma (a + b + 1 / 2) / (Gamma (a + 1 / 2) * Gamma (b + 1 / 2)) * ₂F₁ a b (1 / 2) (x
      : ℂ) =
      ₂F₁ (2 * a) (2 * b) (a + b + 1 / 2) ((1 - Real.sqrt x) / 2 : ℂ) + ₂F₁ (2 * a) (2 * b) (a + b + 1 / 2)
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

@[dlmf 15.8.E28]
theorem quadratic_odd_connection
    {a b : ℂ}
    {x : ℝ}
    (hc : ∀ k : ℕ, a + b - 1 / 2 ≠ -(k : ℂ))
    (hx : 0 < x)
    (hx1 : x < 1) :
    2 * (Real.sqrt x : ℂ) * Gamma (-1 / 2) * Gamma (a + b - 1 / 2) / (Gamma (a - 1 / 2) * Gamma (b - 1 / 2))
      * ₂F₁ a b (3 / 2) (x : ℂ) =
      ₂F₁ (2 * a - 1) (2 * b - 1) (a + b - 1 / 2) ((1 - Real.sqrt x) / 2 : ℂ) - ₂F₁ (2 * a - 1) (2 * b - 1)
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

/-! ### Parameter derivatives for the logarithmic cases -/

/-- `(1/Γ)' = -ψ/Γ` away from the poles. -/
lemma hasDerivAt_recip_Gamma {x : ℂ} (hx : ∀ m : ℕ, x ≠ -(m : ℂ)) :
    HasDerivAt (fun y => (Gamma y)⁻¹) (-(digamma x) * (Gamma x)⁻¹) x := by
  have hG := (differentiableAt_Gamma x hx).hasDerivAt
  have h0 := Gamma_ne_zero hx
  refine (hG.inv h0).congr_deriv ?_
  rw [digamma_def, logDeriv_apply]
  field_simp

/-- `(1/Γ)'(-p) = (-1)^p p!`. -/
lemma hasDerivAt_recip_Gamma_neg_nat (p : ℕ) :
    HasDerivAt (fun y => (Gamma y)⁻¹) ((-1 : ℂ) ^ p * (p.factorial : ℂ)) (-(p : ℂ)) := by
  have heq : (fun y => (Gamma y)⁻¹) = fun y => poch y p * (y + p) * (Gamma (y + (p + 1 : ℕ)))⁻¹ := by
    funext y; rw [recip_Gamma_eq_poch_mul p y, poch_succ]
  rw [heq]
  have hp := (Polynomial.hasDerivAt (ascPochhammer ℂ p) (-(p : ℂ)))
  have h1 : HasDerivAt (fun y : ℂ => y + p) 1 (-(p : ℂ)) := (hasDerivAt_id _).add_const _
  have hpole : ∀ m : ℕ, -(p : ℂ) + ((p + 1 : ℕ) : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    have := congrArg re hm
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have h2 := (hasDerivAt_recip_Gamma hpole).comp (-(p : ℂ)) ((hasDerivAt_id (-(p : ℂ))).add_const
    ((p + 1 : ℕ) : ℂ))
  have h := (hp.mul h1).mul h2
  refine h.congr_deriv ?_
  have e1 : -(p : ℂ) + ((p + 1 : ℕ) : ℂ) = 1 := by push_cast; ring
  simp only [_root_.id, e1, Gamma_one, inv_one, mul_one, Function.comp_apply, Pi.mul_apply]
  rw [show (Polynomial.eval (-(p : ℂ)) (ascPochhammer ℂ p)) = poch (-(p : ℂ)) p from rfl,
    poch_neg_coe_nat, Nat.descFactorial_self]
  ring

/-- Logarithmic derivative of the Pochhammer symbol. -/
lemma hasDerivAt_poch {x : ℂ} (hx : ∀ m : ℕ, x ≠ -(m : ℂ)) (n : ℕ) :
    HasDerivAt (fun y => poch y n) (poch x n * (digamma (x + n) - digamma x)) x := by
  induction n with
  | zero => simpa [poch_zero] using hasDerivAt_const x (1 : ℂ)
  | succ n ih =>
    have h := ih.mul ((hasDerivAt_id x).add_const (n : ℂ))
    have hfun : (fun y => poch y (n + 1)) = fun y => poch y n * (_root_.id y + n) := by
      funext y; rw [poch_succ]; rfl
    rw [hfun]
    refine h.congr_deriv ?_
    have hxn : x + n ≠ 0 := by simpa using not_neg_nat_add_nat hx n 0
    rw [poch_succ, show x + ((n + 1 : ℕ) : ℂ) = (x + n) + 1 by push_cast; ring,
      digamma_apply_add_one _ (not_neg_nat_add_nat hx n)]
    simp only [_root_.id]
    field_simp
    ring

/-- Termwise differentiation of the regularized Gauss series along entire parameter curves. -/
theorem hasSum_deriv_regularizedGaussHGFun_comp {A B C : ℂ → ℂ} (hA : Differentiable ℂ A)
    (hB : Differentiable ℂ B) (hC : Differentiable ℂ C) {z : ℂ} (hz : ‖z‖ < 1) (w₀ : ℂ) :
    HasSum (fun n : ℕ => deriv (fun w => poch (A w) n * poch (B w) n * z ^ n / n.factorial *
        (Gamma (C w + n))⁻¹) w₀)
      (deriv (fun w => regularizedGaussHGFun (A w) (B w) (C w) z) w₀) := by
  set T : ℕ → ℂ → ℂ := fun n w => poch (A w) n * poch (B w) n * z ^ n / n.factorial *
    (Gamma (C w + n))⁻¹ with hT
  have hTd : ∀ n, Differentiable ℂ (T n) := by
    intro n
    have h1 : Differentiable ℂ fun w => (ascPochhammer ℂ n).eval (A w) :=
      (Polynomial.differentiable (ascPochhammer ℂ n)).comp hA
    have h2 : Differentiable ℂ fun w => (ascPochhammer ℂ n).eval (B w) :=
      (Polynomial.differentiable (ascPochhammer ℂ n)).comp hB
    exact (((h1.mul h2).mul_const _).div_const _).mul
      (differentiable_one_div_Gamma.comp (hC.add_const _))
  have hfun : (fun w => regularizedGaussHGFun (A w) (B w) (C w) z) = fun w => ∑' n, T n w := by
    funext w; rw [regularizedGaussHGFun_eq_tsum]
  rw [hfun]
  -- domination near `w₀`
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 3 - (C w₀).re ≤ N := exists_nat_ge _
  have hre0 : 2 ≤ (C w₀ + N).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith
  obtain ⟨V, hVopen, hc₀V, hV⟩ := exists_open_norm_Gamma_add_nat_gt hre0
  have hevA : ∀ᶠ w in 𝓝 w₀, ‖A w‖ < ‖A w₀‖ + 1 :=
    hA.continuous.continuousAt.norm.eventually (gt_mem_nhds (by linarith))
  have hevB : ∀ᶠ w in 𝓝 w₀, ‖B w‖ < ‖B w₀‖ + 1 :=
    hB.continuous.continuousAt.norm.eventually (gt_mem_nhds (by linarith))
  have hevC : ∀ᶠ w in 𝓝 w₀, (C w₀).re - 1 < (C w).re :=
    (Complex.continuous_re.comp hC.continuous).continuousAt.eventually
      (lt_mem_nhds (by show (C w₀).re - 1 < (C w₀).re; linarith))
  have hevV : ∀ᶠ w in 𝓝 w₀, C w ∈ V := hC.continuous.continuousAt (hVopen.mem_nhds hc₀V)
  have hevF : ∀ᶠ w in 𝓝 w₀, ∀ n ∈ Finset.range N, ‖T n w‖ < ‖T n w₀‖ + 1 := by
    rw [Finset.eventually_all]
    intro n _
    exact (hTd n).continuous.continuousAt.norm.eventually (gt_mem_nhds (by linarith))
  obtain ⟨U, hU, hUopen, hw₀U⟩ :=
    eventually_nhds_iff.mp (hevA.and (hevB.and (hevC.and (hevV.and hevF))))
  set p := regularizedGaussHGFunSeries ((‖A w₀‖ + 1 : ℝ) : ℂ) ((‖B w₀‖ + 1 : ℝ) : ℂ) (1 - N)
    with hp
  have hz' : (‖z‖₊ : ENNReal) < p.radius := by
    refine lt_of_lt_of_le ?_ (radius_regularizedGaussHGFunSeries_ge_one _ _ _)
    rw [← ENNReal.coe_one, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]
    exact hz
  have hm : 0 < ‖Gamma (C w₀ + N)‖ / 2 := by
    have hpole : ∀ k : ℕ, C w₀ + N ≠ -k := fun k h => by
      have := congrArg Complex.re h
      simp only [Complex.neg_re, Complex.natCast_re] at this
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have := norm_pos_iff.mpr (Gamma_ne_zero hpole)
    positivity
  set u : ℕ → ℝ := fun n => if n < N then ‖T n w₀‖ + 1 else
    (‖Gamma (C w₀ + N)‖ / 2)⁻¹ * (‖p n‖ * (‖z‖₊ : ℝ) ^ n) with hu
  have hus : Summable u := by
    refine (summable_nat_add_iff N).mp ?_
    have := ((p.summable_norm_mul_pow hz').mul_left ((‖Gamma (C w₀ + N)‖ / 2)⁻¹))
    refine ((summable_nat_add_iff N).mpr this).congr fun n => ?_
    simp only [hu, show ¬ n + N < N by omega, ite_false]
  refine hasSum_deriv_of_summable_norm hus (fun n => (hTd n).differentiableOn) hUopen
    (fun n w hw => ?_) hw₀U
  obtain ⟨hAw, hBw, hCw, hVw, hFw⟩ := hU w hw
  by_cases hn : n < N
  · simp only [hu, hn, ite_true]
    exact (hFw n (Finset.mem_range.mpr hn)).le
  · simp only [hu, hn, ite_false]
    have hre : 1 ≤ (C w + N).re := by
      simp only [Complex.add_re, Complex.natCast_re] at hre0 ⊢
      linarith
    simpa only [coe_nnnorm] using
      norm_term_le_majorant hAw.le hBw.le hre hm (hV _ hVw).le (not_lt.mp hn)

lemma deriv_recip_Gamma_eq {x : ℂ} (hx : ∀ m : ℕ, x ≠ -(m : ℂ)) :
    deriv (fun y => (Gamma y)⁻¹) x = -(digamma x) * (Gamma x)⁻¹ := (hasDerivAt_recip_Gamma hx).deriv

lemma deriv_recip_Gamma_neg_nat (p : ℕ) :
    deriv (fun y => (Gamma y)⁻¹) (-(p : ℂ)) = (-1 : ℂ) ^ p * (p.factorial : ℂ) :=
  (hasDerivAt_recip_Gamma_neg_nat p).deriv

lemma hasDerivAt_recip_Gamma_any (x : ℂ) :
    HasDerivAt (fun y => (Gamma y)⁻¹) (deriv (fun y => (Gamma y)⁻¹) x) x :=
  (differentiable_one_div_Gamma x).hasDerivAt

@[dlmf 15.8.E10]
theorem logarithmic_connection_one_sub {a b z : ℂ} (m : ℕ)
    (ha : ∀ k : ℕ, a ≠ -(k : ℂ)) (hb : ∀ k : ℕ, b ≠ -(k : ℂ))
    (hz : ‖z‖ < 1) (hw : ‖1 - z‖ < 1) :
    regularizedGaussHGFun a b (a + b + m) z =
      (1 / (Gamma (a + m) * Gamma (b + m))) *
        (∑ k ∈ Finset.range m, poch a k * poch b k * ((m - k - 1).factorial : ℂ)/
          (k.factorial : ℂ) * (z - 1) ^ k) -
      (z - 1) ^ m / (Gamma a * Gamma b) * ∑' k : ℕ,
        poch (a + m) k * poch (b + m) k / ((k.factorial : ℂ) * ((k + m).factorial : ℂ)) *
          (1 - z) ^ k * (log (1 - z) - digamma (k + 1) - digamma (k + m + 1)+
            digamma (a + k + m) + digamma (b + k + m)) := by
  set w := 1 - z with hwdef
  set c₀ := a + b + m with hc₀
  set D : ℂ → ℂ := deriv (fun y : ℂ => (Gamma y)⁻¹) with hD
  have hw0 : w ≠ 0 := by
    intro h; rw [hwdef, sub_eq_zero] at h; rw [← h] at hz; simp at hz
  have ham := not_neg_nat_add_nat ha m
  have hbm := not_neg_nat_add_nat hb m
  -- the connection formula for every `c`
  have hconn : ∀ c : ℂ, sin (Real.pi * (c - a - b)) / Real.pi * regularizedGaussHGFun a b c z =
      regularizedGaussHGFun a b (a + b - c + 1) w * ((Gamma (c - a))⁻¹ * (Gamma (c - b))⁻¹) -
        (Gamma a * Gamma b)⁻¹ * (w ^ (c - a - b) * regularizedGaussHGFun (c - a) (c - b)
          (c - a - b + 1) w) := by
    intro c
    rw [regularized_connection_one_sub a b c hz hw]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  -- derivative of the left side
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hRc := (analyticOnNhd_regularizedGaussHGFun_c a b hz c₀ (Set.mem_univ _)).differentiableAt
  have hsin : HasDerivAt (fun c : ℂ => sin (Real.pi * (c - a - b)) / Real.pi)
      (cos (Real.pi * (c₀ - a - b)) * (Real.pi * 1) / Real.pi) c₀ :=
    ((((hasDerivAt_id c₀).sub_const a).sub_const b).const_mul (Real.pi : ℂ)).csin.div_const _
  have hm1 : c₀ - a - b = m := by rw [hc₀]; ring
  have hL := hsin.mul hRc.hasDerivAt
  have hcos : cos ((m : ℂ) * Real.pi) = (-1) ^ m := by
    rw [show ((m : ℂ) * Real.pi) = ((m * Real.pi : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos,
      Real.cos_nat_mul_pi]
    push_cast; ring
  rw [hm1, mul_comm (Real.pi : ℂ) (m : ℂ), hcos, Complex.sin_nat_mul_pi, zero_div, zero_mul,
    add_zero, mul_one, mul_div_cancel_right₀ _ hπ] at hL
  have hwn : ‖w‖ < 1 := hw
  -- the first series and its derivative
  set S : ℂ → ℂ := fun c => regularizedGaussHGFun a b (a + b - c + 1) w with hSdef
  have hSa : DifferentiableAt ℂ S c₀ :=
    (analyticOnNhd_regularizedGaussHGFun_comp (A := fun _ => a) (B := fun _ => b)
      (C := fun c => a + b - c + 1) (differentiable_const _) (differentiable_const _)
      (by fun_prop) hwn c₀ (Set.mem_univ _)).differentiableAt
  have hSsum := hasSum_deriv_regularizedGaussHGFun_comp (A := fun _ => a) (B := fun _ => b)
    (C := fun c => a + b - c + 1) (differentiable_const _) (differentiable_const _)
    (by fun_prop) hwn c₀
  have htd : ∀ n : ℕ, deriv (fun c => poch ((fun _ => a) c) n * poch ((fun _ => b) c) n * w ^ n /
      n.factorial * (Gamma ((fun c => a + b - c + 1) c + n))⁻¹) c₀ =
      -(poch a n * poch b n * w ^ n / n.factorial) * D (1 - m + n) := by
    intro n
    have h1 : HasDerivAt (fun c : ℂ => a + b - c + 1 + n) (-1) c₀ := by
      simpa using (((hasDerivAt_id c₀).const_sub (a + b)).add_const 1).add_const (n : ℂ)
    have h2 := ((hasDerivAt_recip_Gamma_any (a + b - c₀ + 1 + n)).comp c₀ h1).const_mul
      (poch a n * poch b n * w ^ n / n.factorial)
    rw [show a + b - c₀ + 1 + n = 1 - m + n by rw [hc₀]; ring] at h2
    rw [show (fun c => poch ((fun _ => a) c) n * poch ((fun _ => b) c) n * w ^ n /
      n.factorial * (Gamma ((fun c => a + b - c + 1) c + n))⁻¹) = (fun c =>
      poch a n * poch b n * w ^ n / n.factorial *
        ((fun y => (Gamma y)⁻¹) ∘ fun c : ℂ => a + b - c + 1 + n) c) from rfl, h2.deriv, hD]
    ring
  -- the second series and its derivative
  set Q : ℂ → ℂ := fun c => regularizedGaussHGFun (c - a) (c - b) (c - a - b + 1) w with hQdef
  have hQa : DifferentiableAt ℂ Q c₀ :=
    (analyticOnNhd_regularizedGaussHGFun_comp (A := fun c => c - a) (B := fun c => c - b)
      (C := fun c => c - a - b + 1) (by fun_prop) (by fun_prop) (by fun_prop) hwn c₀
      (Set.mem_univ _)).differentiableAt
  have hQsum := hasSum_deriv_regularizedGaussHGFun_comp (A := fun c => c - a) (B := fun c => c - b)
    (C := fun c => c - a - b + 1) (by fun_prop) (by fun_prop) (by fun_prop) hwn c₀
  have hmn : ∀ n : ℕ, ∀ j : ℕ, (m : ℂ) + 1 + n ≠ -(j : ℂ) := by
    intro n j hj
    have := congrArg re hj
    simp at this
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j), (Nat.cast_nonneg m : (0 : ℝ) ≤ m),
      (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hqd : ∀ n : ℕ, deriv (fun c => poch ((fun c => c - a) c) n * poch ((fun c => c - b) c) n *
      w ^ n / n.factorial * (Gamma ((fun c => c - a - b + 1) c + n))⁻¹) c₀ =
      poch (b + m) n * poch (a + m) n * w ^ n / n.factorial * (Gamma (m + 1 + n))⁻¹ *
        (digamma (b + m + n) - digamma (b + m) + digamma (a + m + n) - digamma (a + m) -
          digamma (m + 1 + n)) := by
    intro n
    have e1 : c₀ - a = b + m := by rw [hc₀]; ring
    have e2 : c₀ - b = a + m := by rw [hc₀]; ring
    have e3 : c₀ - a - b + 1 + n = m + 1 + n := by rw [hc₀]; ring
    have hp1' : HasDerivAt (fun y => poch y n) (poch (b + m) n * (digamma (b + m + n) -
        digamma (b + m))) (c₀ - a) := by rw [e1]; exact hasDerivAt_poch hbm n
    have hp2' : HasDerivAt (fun y => poch y n) (poch (a + m) n * (digamma (a + m + n) -
        digamma (a + m))) (c₀ - b) := by rw [e2]; exact hasDerivAt_poch ham n
    have hg' : HasDerivAt (fun y => (Gamma y)⁻¹) (-(digamma (m + 1 + n)) * (Gamma (m + 1 + n))⁻¹)
        (c₀ - a - b + 1 + n) := by rw [e3]; exact hasDerivAt_recip_Gamma (hmn n)
    have hl1 : HasDerivAt (fun c : ℂ => c - a) 1 c₀ := (hasDerivAt_id c₀).sub_const a
    have hl2 : HasDerivAt (fun c : ℂ => c - b) 1 c₀ := (hasDerivAt_id c₀).sub_const b
    have hl3 : HasDerivAt (fun c : ℂ => c - a - b + 1 + n) 1 c₀ :=
      ((((hasDerivAt_id c₀).sub_const a).sub_const b).add_const 1).add_const _
    have h := ((((hp1'.comp c₀ hl1).mul (hp2'.comp c₀ hl2)).mul_const (w ^ n)).div_const
      (n.factorial : ℂ)).mul (hg'.comp c₀ hl3)
    have h' : HasDerivAt (fun c => ((fun y => poch y n) ∘ fun c : ℂ => c - a) c *
        ((fun y => poch y n) ∘ fun c : ℂ => c - b) c * w ^ n / n.factorial *
        ((fun y => (Gamma y)⁻¹) ∘ fun c : ℂ => c - a - b + 1 + n) c) _ c₀ := h
    rw [show (fun c => poch ((fun c => c - a) c) n * poch ((fun c => c - b) c) n *
      w ^ n / n.factorial * (Gamma ((fun c => c - a - b + 1) c + n))⁻¹) =
      fun c => ((fun y => poch y n) ∘ fun c : ℂ => c - a) c * ((fun y => poch y n) ∘ fun c : ℂ => c - b) c *
        w ^ n / n.factorial * ((fun y => (Gamma y)⁻¹) ∘ fun c : ℂ => c - a - b + 1 + n) c from rfl,
      h'.deriv]
    simp only [Pi.mul_apply, Function.comp_apply, e1, e2]
    ring_nf
  -- derivative of the right side of the connection formula
  have e1 : c₀ - a = b + m := by rw [hc₀]; ring
  have e2 : c₀ - b = a + m := by rw [hc₀]; ring
  have hG1 : HasDerivAt (fun c : ℂ => (Gamma (c - a))⁻¹) (-(digamma (b + m)) * (Gamma (b + m))⁻¹) c₀ := by
    have h1 : HasDerivAt (fun y => (Gamma y)⁻¹) (-(digamma (b + m)) * (Gamma (b + m))⁻¹)
        (c₀ - a) := by rw [e1]; exact hasDerivAt_recip_Gamma hbm
    simpa [Function.comp_def] using h1.comp c₀ ((hasDerivAt_id c₀).sub_const a)
  have hG2 : HasDerivAt (fun c : ℂ => (Gamma (c - b))⁻¹) (-(digamma (a + m)) * (Gamma (a + m))⁻¹) c₀ := by
    have h1 : HasDerivAt (fun y => (Gamma y)⁻¹) (-(digamma (a + m)) * (Gamma (a + m))⁻¹)
        (c₀ - b) := by rw [e2]; exact hasDerivAt_recip_Gamma ham
    simpa [Function.comp_def] using h1.comp c₀ ((hasDerivAt_id c₀).sub_const b)
  have hP : HasDerivAt (fun c : ℂ => w ^ (c - a - b)) (w ^ (m : ℂ) * log w * 1) c₀ := by
    have h := (((hasDerivAt_id c₀).sub_const a).sub_const b).const_cpow (c := w) (Or.inl hw0)
    rw [show _root_.id c₀ - a - b = (m : ℂ) by simp only [_root_.id]; rw [hc₀]; ring] at h
    exact h
  have hR := (hSa.hasDerivAt.mul (hG1.mul hG2)).sub
    ((hP.mul hQa.hasDerivAt).const_mul ((Gamma a * Gamma b)⁻¹))
  have hfun : (fun c => sin (Real.pi * (c - a - b)) / Real.pi * regularizedGaussHGFun a b c z) =
      fun c => S c * ((Gamma (c - a))⁻¹ * (Gamma (c - b))⁻¹) -
        (Gamma a * Gamma b)⁻¹ * (w ^ (c - a - b) * Q c) := funext hconn
  have hL' : HasDerivAt (fun c => sin (Real.pi * (c - a - b)) / Real.pi *
      regularizedGaussHGFun a b c z) ((-1) ^ m * regularizedGaussHGFun a b c₀ z) c₀ := hL
  rw [hfun] at hL'
  have hkey := hL'.unique hR
  simp only [Pi.mul_apply] at hkey
  rw [hm1, e1, e2, cpow_natCast] at hkey
  -- the two series at `c₀`
  set P : ℂ := poch a m * poch b m with hPdef
  set q : ℕ → ℂ := fun k => poch (b + m) k * poch (a + m) k * w ^ k / k.factorial *
    (Gamma (m + 1 + k))⁻¹ with hq
  set sS : ℕ → ℂ := fun n => poch a n * poch b n * w ^ n / n.factorial *
    (Gamma (1 - m + n))⁻¹ with hsS
  have hS0 : HasSum sS (S c₀) := by
    have h := (summable_regularizedGaussHGFun_term a b (1 - m) hwn).hasSum
    rw [← regularizedGaussHGFun_eq_tsum] at h
    convert h using 1
    simp only [hSdef]; congr 1; rw [hc₀]; ring
  have hQ0 : HasSum q (Q c₀) := by
    have h := (summable_regularizedGaussHGFun_term (b + m) (a + m) (m + 1) hwn).hasSum
    rw [← regularizedGaussHGFun_eq_tsum] at h
    convert h using 1
    simp only [hQdef]; rw [hm1, e1, e2]
  have hGk : ∀ k : ℕ, Gamma ((m : ℂ) + 1 + k) = ((k + m).factorial : ℂ) := by
    intro k
    rw [show (m : ℂ) + 1 + k = ((k + m : ℕ) : ℂ) + 1 by push_cast; ring, Gamma_nat_eq_factorial]
  have hG1k : ∀ k : ℕ, Gamma (1 - (m : ℂ) + ((k + m : ℕ) : ℂ)) = (k.factorial : ℂ) := by
    intro k
    rw [show 1 - (m : ℂ) + ((k + m : ℕ) : ℂ) = (k : ℂ) + 1 by push_cast; ring, Gamma_nat_eq_factorial]
  have hsS_shift : ∀ k : ℕ, sS (k + m) = P * w ^ m * q k := by
    intro k
    simp only [hsS, hq, hPdef, hGk, hG1k]
    rw [add_comm k m, poch_add a m k, poch_add b m k, pow_add, add_comm m k]
    have hk : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have hkm : ((k + m).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
  have hpole : ∀ n : ℕ, n < m → 1 - (m : ℂ) + n = -((m - 1 - n : ℕ) : ℂ) := by
    intro n hn
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have hsS_low : ∀ n ∈ Finset.range m, sS n = 0 := by
    intro n hn
    rw [Finset.mem_range] at hn
    simp only [hsS, hpole n hn, Gamma_neg_nat_eq_zero, inv_zero, mul_zero]
  have hS0eq : S c₀ = P * w ^ m * Q c₀ := by
    have h := (hasSum_nat_add_iff' m).mpr hS0
    rw [Finset.sum_eq_zero hsS_low, sub_zero] at h
    exact h.unique ((hQ0.mul_left (P * w ^ m)).congr_fun fun k => (hsS_shift k).symm ▸ rfl)
  -- derivatives of the first series
  set dt : ℕ → ℂ := fun n => deriv (fun c => poch ((fun _ => a) c) n * poch ((fun _ => b) c) n *
      w ^ n / n.factorial * (Gamma ((fun c => a + b - c + 1) c + n))⁻¹) c₀ with hdt
  have hdt_shift : ∀ k : ℕ, dt (k + m) = P * w ^ m * q k * digamma (k + 1) := by
    intro k
    simp only [hdt]
    have hk1 : ∀ j : ℕ, (k : ℂ) + 1 ≠ -(j : ℂ) := by
      intro j hj
      have := congrArg re hj
      simp at this
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j), (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    rw [htd, show 1 - (m : ℂ) + ((k + m : ℕ) : ℂ) = (k : ℂ) + 1 by push_cast; ring, hD,
      deriv_recip_Gamma_eq hk1, ← hsS_shift k]
    simp only [hsS, show 1 - (m : ℂ) + ((k + m : ℕ) : ℂ) = (k : ℂ) + 1 by push_cast; ring]
    ring
  have hdt_low : ∀ n : ℕ, n < m → dt n =
      -(poch a n * poch b n * w ^ n / n.factorial) * ((-1) ^ (m - 1 - n) * ((m - 1 - n).factorial : ℂ)) := by
    intro n hn
    simp only [hdt]
    rw [htd, hpole n hn, hD, deriv_recip_Gamma_neg_nat]
  have hSshift := (hasSum_nat_add_iff' m).mpr hSsum
  set ψs := digamma (a + m) + digamma (b + m) with hψs
  have hEsum : HasSum (fun k => P * w ^ m * (q k * (log w - digamma (k + 1) - digamma (m + 1 + k) +
      digamma (a + m + k) + digamma (b + m + k))))
      (P * w ^ m * (log w + ψs) * Q c₀ + P * w ^ m * deriv Q c₀ -
        (deriv S c₀ - ∑ i ∈ Finset.range m, dt i)) := by
    have h := ((hQ0.mul_left (P * w ^ m * (log w + ψs))).add (hQsum.mul_left (P * w ^ m))).sub hSshift
    convert h using 1
    funext k
    rw [hqd k, hdt_shift k]
    simp only [hψs]
    ring
  have htsum : (∑' k : ℕ, poch (a + m) k * poch (b + m) k / ((k.factorial : ℂ) * ((k + m).factorial : ℂ)) *
      w ^ k * (log w - digamma (k + 1) - digamma (k + m + 1) + digamma (a + k + m) +
        digamma (b + k + m))) = ∑' k : ℕ, q k * (log w - digamma (k + 1) - digamma (m + 1 + k) +
      digamma (a + m + k) + digamma (b + m + k)) := by
    refine tsum_congr fun k => ?_
    simp only [hq, hGk]
    rw [show (k : ℂ) + m + 1 = m + 1 + k by ring, show a + k + m = a + m + k by ring,
      show b + k + m = b + m + k by ring]
    field_simp
  have hEval := hEsum.tsum_eq
  rw [tsum_mul_left] at hEval
  rw [htsum]
  set SE := ∑' k : ℕ, q k * (log w - digamma (k + 1) - digamma (m + 1 + k) +
      digamma (a + m + k) + digamma (b + m + k)) with hSE
  -- Gamma bookkeeping
  have hPa : poch a m ≠ 0 := poch_ne_zero_of_not_neg_nat ha m
  have hPb : poch b m ≠ 0 := poch_ne_zero_of_not_neg_nat hb m
  have hGa : Gamma a ≠ 0 := Gamma_ne_zero ha
  have hGb : Gamma b ≠ 0 := Gamma_ne_zero hb
  have hGam : Gamma (a + m) = poch a m * Gamma a := by
    have h := Gamma_add_nat_div_Gamma_eq (n := m) a ha
    rw [div_eq_iff hGa] at h
    rw [h]
  have hGbm : Gamma (b + m) = poch b m * Gamma b := by
    have h := Gamma_add_nat_div_Gamma_eq (n := m) b hb
    rw [div_eq_iff hGb] at h
    rw [h]
  have hGP : (Gamma (b + m))⁻¹ * (Gamma (a + m))⁻¹ * P = (Gamma a * Gamma b)⁻¹ := by
    rw [hGam, hGbm, hPdef]; field_simp
  have hzw : (z - 1) ^ m = (-1) ^ m * w ^ m := by
    rw [← mul_pow, hwdef]; ring
  have hσ : ((-1 : ℂ) ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hFin : (-1 : ℂ) ^ m * ∑ i ∈ Finset.range m, dt i = ∑ k ∈ Finset.range m,
      poch a k * poch b k * ((m - k - 1).factorial : ℂ) / (k.factorial : ℂ) * (z - 1) ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [hdt_low k hk, show m - 1 - k = m - k - 1 by omega]
    obtain ⟨j, hj⟩ : ∃ j, m = k + 1 + j := ⟨m - k - 1, by omega⟩
    have hzk : (z - 1) ^ k = (-1) ^ k * w ^ k := by
      rw [show z - 1 = -w by rw [hwdef]; ring, neg_pow]
    rw [show m - k - 1 = j by omega, hzk, hj]
    have hj2 : ((-1 : ℂ) ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    linear_combination (poch a k * poch b k * w ^ k / k.factorial * (j.factorial : ℂ) * (-1) ^ k) * hj2
  rw [hψs] at hEval
  rw [one_div, mul_inv, div_eq_mul_inv]
  linear_combination (-1 : ℂ) ^ m * hkey +
    (-((-1 : ℂ) ^ m) * ((Gamma (b + m))⁻¹ * (Gamma (a + m))⁻¹) *
      (digamma (a + m) + digamma (b + m))) * hS0eq +
    ((-1 : ℂ) ^ m * ((Gamma (b + m))⁻¹ * (Gamma (a + m))⁻¹)) * hEval +
    ((-1 : ℂ) ^ m * w ^ m * (-SE + log w * Q c₀ + deriv Q c₀)) * hGP +
    ((Gamma (b + m))⁻¹ * (Gamma (a + m))⁻¹) * hFin + ((Gamma a * Gamma b)⁻¹ * SE) * hzw +
    (-regularizedGaussHGFun a b c₀ z) * hσ

@[dlmf 15.8.E9]
theorem logarithmic_connection_one_div_one_sub {a c z : ℂ} (m : ℕ)
    (ha : ∀ k : ℤ, a ≠ (k : ℂ)) (hca : ∀ k : ℤ, c - a ≠ (k : ℂ))
    (hz : ‖z‖ < 1) (hw : 1 < ‖1 - z‖) :
    regularizedGaussHGFun a (a + m) c z =
      (1 - z) ^ (-a) / (Gamma (a + m) * Gamma (c - a)) *
        (∑ k ∈ Finset.range m, poch a k * poch (c - a - m) k * ((m - k - 1).factorial : ℂ)/
          (k.factorial : ℂ) * ((z - 1)⁻¹) ^ k) +
      (-1 : ℂ) ^ m * (1 - z) ^ (-a - m) / (Gamma a * Gamma (c - a - m)) *
        ∑' k : ℕ, poch (a + m) k * poch (c - a) k /
          ((k.factorial : ℂ) * ((k + m).factorial : ℂ)) * ((1 - z)⁻¹) ^ k *
          (log (1 - z) + digamma (k + 1) + digamma (k + m + 1) - digamma (a + k + m) - digamma (c - a + k))
            := by
  have h1z : 1 - z ≠ 0 := by
    intro h; rw [h, norm_zero] at hw; linarith
  have hz1 : z - 1 ≠ 0 := by intro h; apply h1z; linear_combination -h
  have hzlt : ‖z‖ < ‖z - 1‖ := by rw [norm_sub_rev]; linarith
  have hζ : ‖z / (z - 1)‖ < 1 := by
    rw [norm_div, div_lt_one (by linarith [norm_nonneg z])]; exact hzlt
  have h1ζ : 1 - z / (z - 1) = (1 - z)⁻¹ := by field_simp; ring
  have hζ1 : z / (z - 1) - 1 = (z - 1)⁻¹ := by field_simp; ring
  have h1ζn : ‖1 - z / (z - 1)‖ < 1 := by
    rw [h1ζ, norm_inv]; exact inv_lt_one_of_one_lt₀ hw
  have ha' : ∀ k : ℕ, a ≠ -(k : ℂ) := fun k h => ha (-k) (by rw [h]; push_cast; ring)
  have hb' : ∀ k : ℕ, c - a - m ≠ -(k : ℂ) := fun k h =>
    hca (m - k) (by push_cast; linear_combination h)
  have hp := regularized_pfaff a (a + m) c hz (by rwa [show z / (z - 1) = z / (z - 1) from rfl])
  rw [hp, show c - (a + m) = c - a - m by ring]
  have hE := logarithmic_connection_one_sub (a := a) (b := c - a - m) (z := z / (z - 1)) m ha' hb'
    hζ h1ζn
  rw [show a + (c - a - m) + m = c by ring, h1ζ, hζ1, show c - a - m + m = c - a by ring] at hE
  rw [hE]
  have hlog : log (1 - z)⁻¹ = -log (1 - z) := by
    rw [log_inv]
    · intro h
      have hre : 0 < (1 - z).re := by
        have := (re_le_norm z).trans_lt hz
        simp only [sub_re, one_re]; linarith
      have := (arg_eq_pi_iff.mp h).1
      linarith
  rw [hlog]
  have hpow : (1 - z) ^ (-a - m) = (1 - z) ^ (-a) * ((1 - z)⁻¹) ^ m := by
    rw [cpow_sub _ _ h1z, cpow_natCast, inv_pow, div_eq_mul_inv]
  have hzm : ((z - 1)⁻¹) ^ m = (-1) ^ m * ((1 - z)⁻¹) ^ m := by
    rw [show z - 1 = -(1 - z) by ring, inv_neg, neg_pow]
  rw [hpow, hzm]
  have hdig : ∀ k : ℕ, digamma (c - a - m + k + m) = digamma (c - a + k) := fun k => by
    congr 1; ring
  simp only [hdig]
  rw [show (∑' k : ℕ, poch (a + m) k * poch (c - a) k /
          ((k.factorial : ℂ) * ((k + m).factorial : ℂ)) * ((1 - z)⁻¹) ^ k *
          (log (1 - z) + digamma (k + 1) + digamma (k + m + 1) - digamma (a + k + m) -
            digamma (c - a + k))) =
      -∑' k : ℕ, poch (a + m) k * poch (c - a) k /
          ((k.factorial : ℂ) * ((k + m).factorial : ℂ)) * ((1 - z)⁻¹) ^ k *
          (-log (1 - z) - digamma (k + 1) - digamma (k + m + 1) + digamma (a + k + m) +
            digamma (c - a + k)) by
    rw [← tsum_neg]; exact tsum_congr fun k => by ring]
  ring

/-- The regularized function is symmetric in its numerator parameters. -/
lemma regularizedGaussHGFun_comm (a b c z : ℂ) :
    regularizedGaussHGFun a b c z = regularizedGaussHGFun b a c z := by
  rw [regularizedGaussHGFun_eq_tsum, regularizedGaussHGFun_eq_tsum]
  exact tsum_congr fun n => by ring

/-- 15.8.5 with the second series Euler-transformed, so that both series share their
logarithmic limits termwise. -/
lemma regularized_connection_one_sub_recip' (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1)
    (ht : ‖1 - 1 / z‖ < 1) :
    sin (Real.pi * (c - a - b)) / Real.pi * regularizedGaussHGFun a b c z =
      z ^ (-a) / (Gamma (c - a) * Gamma (c - b)) * regularizedGaussHGFun a (a - c + 1)
        (a + b - c + 1) (1 - 1 / z) - z ^ (-a) * ((1 - z) / z) ^ (c - a - b) / (Gamma a * Gamma b) *
        regularizedGaussHGFun (c - b) (1 - b) (c - a - b + 1) (1 - 1 / z) := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at ht
  have h1z : 1 - z ≠ 0 := by rintro h; rw [sub_eq_zero] at h; rw [← h] at hz; simp at hz
  rw [regularized_connection_one_sub_recip a b c hz ht,
    regularized_euler (c - a) (1 - a) (c - a - b + 1) ht,
    regularizedGaussHGFun_comm (c - a - b + 1 - (c - a)),
    show c - a - b + 1 - (c - a) = 1 - b by ring, show c - a - b + 1 - (1 - a) = c - b by ring,
    show 1 - b - (1 - a) = a - b by ring, show (1 : ℂ) - (1 - 1 / z) = z⁻¹ by ring]
  -- the elementary factors
  have hre : 0 < z.re := by
    have h1 : ‖z - 1‖ < ‖z‖ := by
      have : ‖(z - 1) / z‖ < 1 := by rw [show (z - 1) / z = 1 - 1 / z by field_simp]; exact ht
      rwa [norm_div, div_lt_one (norm_pos_iff.mpr hz0)] at this
    by_contra hneg
    rw [not_lt] at hneg
    have : ‖z‖ ≤ ‖z - 1‖ := by
      rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← normSq_eq_norm_sq, ← normSq_eq_norm_sq,
        normSq_apply, normSq_apply]
      simp only [sub_re, one_re, sub_im, one_im, sub_zero]
      nlinarith
    linarith
  have hre1 : 0 < (1 - z).re := by
    have := (re_le_norm z).trans_lt hz
    simp only [sub_re, one_re]; linarith
  have hargz : z.arg ≠ Real.pi := by
    intro h; have := (arg_eq_pi_iff.mp h).1; linarith
  have habs : ∀ w : ℂ, 0 < w.re → |w.arg| < Real.pi / 2 := fun w hw =>
    abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)
  have hlog : log ((1 - z) / z) = log (1 - z) + log z⁻¹ := by
    rw [div_eq_mul_inv]
    refine log_mul h1z (inv_ne_zero hz0) ?_
    have h1 := habs _ hre1
    have h2 := habs z⁻¹ (by rw [inv_re]; exact div_pos hre (normSq_pos.mpr hz0))
    rw [abs_lt] at h1 h2
    constructor <;> linarith [Real.pi_pos]
  have hfac : (1 - z) ^ (c - a - b) * z ^ (a - c) * z⁻¹ ^ (a - b) =
      z ^ (-a) * ((1 - z) / z) ^ (c - a - b) := by
    have hq : (1 - z) / z ≠ 0 := div_ne_zero h1z hz0
    rw [cpow_def_of_ne_zero hq, hlog, add_mul, exp_add, ← cpow_def_of_ne_zero h1z,
      ← cpow_def_of_ne_zero (inv_ne_zero hz0), inv_cpow _ _ hargz, inv_cpow _ _ hargz,
      ← cpow_neg, ← cpow_neg]
    have e : z ^ (a - c) * z ^ (-(a - b)) = z ^ (-a) * z ^ (-(c - a - b)) := by
      rw [← cpow_add _ _ hz0, ← cpow_add _ _ hz0]; congr 1; ring
    linear_combination (1 - z) ^ (c - a - b) * e
  rw [← hfac]
  ring

lemma not_neg_nat_of_not_int_sub {x : ℂ} (hx : ∀ k : ℤ, x ≠ (k : ℂ)) (n : ℕ) :
    ∀ j : ℕ, x - n ≠ -(j : ℂ) := fun j h => hx (n - j) (by push_cast; linear_combination h)

/-- `(1-x)_n = (-1)^n Γ(x)/Γ(x-n)`. -/
lemma poch_one_sub_eq {x : ℂ} (hx : ∀ k : ℤ, x ≠ (k : ℂ)) (n : ℕ) :
    poch (1 - x) n = (-1) ^ n * Gamma x / Gamma (x - n) := by
  induction n with
  | zero => simp [poch_zero, Gamma_ne_zero (not_neg_nat_of_not_int_sub hx 0 |> fun h j => by
      simpa using h j)]
  | succ n ih =>
    have h1 := Gamma_ne_zero (not_neg_nat_of_not_int_sub hx n)
    have h2 := Gamma_ne_zero (not_neg_nat_of_not_int_sub hx (n + 1))
    have hrec : Gamma (x - n) = (x - (n + 1 : ℕ)) * Gamma (x - (n + 1 : ℕ)) := by
      rw [← Gamma_add_one _ (fun h => by
        have := not_neg_nat_of_not_int_sub hx (n + 1) 0; simp_all)]
      congr 1; push_cast; ring
    have hxn1 : x - ((n + 1 : ℕ) : ℂ) ≠ 0 := fun h => hx (n + 1) (by
      push_cast at h ⊢; linear_combination h)
    rw [poch_succ, ih, hrec]
    push_cast at hxn1 h2 ⊢
    field_simp
    ring

/-- `ψ(1-x+n) - ψ(1-x) = ψ(x-n) - ψ(x)`. -/
lemma digamma_one_sub_add_nat {x : ℂ} (hx : ∀ k : ℤ, x ≠ (k : ℂ)) (n : ℕ) :
    digamma (1 - x + n) - digamma (1 - x) = digamma (x - n) - digamma x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1x : ∀ j : ℕ, 1 - x + n ≠ -(j : ℂ) := fun j h => hx (1 + n + j) (by
      push_cast; linear_combination -h)
    have hxn : ∀ j : ℕ, x - (n + 1 : ℕ) ≠ -(j : ℂ) := not_neg_nat_of_not_int_sub hx (n + 1)
    have e1 : digamma (1 - x + ((n + 1 : ℕ) : ℂ)) = digamma (1 - x + n) + (1 - x + n)⁻¹ := by
      rw [show 1 - x + ((n + 1 : ℕ) : ℂ) = (1 - x + n) + 1 by push_cast; ring]
      exact digamma_apply_add_one _ h1x
    have e2 : digamma (x - n) = digamma (x - ((n + 1 : ℕ) : ℂ)) + (x - ((n + 1 : ℕ) : ℂ))⁻¹ := by
      rw [show x - (n : ℂ) = (x - ((n + 1 : ℕ) : ℂ)) + 1 by push_cast; ring]
      exact digamma_apply_add_one _ hxn
    have e3 : (x - ((n + 1 : ℕ) : ℂ))⁻¹ = -(1 - x + n)⁻¹ := by
      rw [show x - ((n + 1 : ℕ) : ℂ) = -(1 - x + n) by push_cast; ring, inv_neg]
    rw [e1]
    linear_combination ih + e2 + e3

@[dlmf 15.8.E11]
theorem logarithmic_connection_one_sub_recip {a b z : ℂ} (m : ℕ)
    (ha : ∀ k : ℕ, a ≠ -(k : ℂ)) (hb : ∀ k : ℤ, b ≠ (k : ℂ))
    (hz : ‖z‖ < 1) (hw : ‖1 - 1 / z‖ < 1) :
    regularizedGaussHGFun a b (a + b + m) z =
      z ^ (-a) / Gamma (a + m) *
        (∑ k ∈ Finset.range m, poch a k * ((m - k - 1).factorial : ℂ)/
          ((k.factorial : ℂ) * Gamma (b + m - k)) * (1 - 1 / z) ^ k) -
      z ^ (-a) / Gamma a * ∑' k : ℕ,
        poch (a + m) k / ((k.factorial : ℂ) * ((k + m).factorial : ℂ) * Gamma (b - k)) *
          (-1 : ℂ) ^ k * (1 - 1 / z) ^ (k + m) * (log ((1 - z) / z) - digamma (k + 1) - digamma (k + m + 1)+
            digamma (a + k + m) + digamma (b - k)) := by
  set c₀ := a + b + m with hc₀
  set D : ℂ → ℂ := deriv (fun y : ℂ => (Gamma y)⁻¹) with hD
  have hz0 : z ≠ 0 := by rintro rfl; simp at hw
  have h1z : 1 - z ≠ 0 := by intro h; rw [sub_eq_zero] at h; rw [← h] at hz; simp at hz
  have hq0 : (1 - z) / z ≠ 0 := div_ne_zero h1z hz0
  have hb' : ∀ k : ℕ, b ≠ -(k : ℂ) := fun k h => hb (-k) (by rw [h]; push_cast; ring)
  have ham := not_neg_nat_add_nat ha m
  have hbm := not_neg_nat_add_nat hb' m
  have hbmZ : ∀ k : ℤ, b + m ≠ (k : ℂ) := fun k h => hb (k - m) (by push_cast; linear_combination h)
  set β : ℂ := 1 - (b + m) with hβ
  have hβnp : ∀ j : ℕ, β ≠ -(j : ℂ) := fun j h => hbmZ (1 + j) (by push_cast; linear_combination -h)
  have hconn : ∀ c : ℂ, sin (Real.pi * (c - a - b)) / Real.pi * regularizedGaussHGFun a b c z =
      regularizedGaussHGFun a (a - c + 1) (a + b - c + 1) (1 - 1 / z) *
          (z ^ (-a) * ((Gamma (c - a))⁻¹ * (Gamma (c - b))⁻¹)) -
        (Gamma a * Gamma b)⁻¹ * z ^ (-a) * (((1 - z) / z) ^ (c - a - b) *
          regularizedGaussHGFun (c - b) (1 - b) (c - a - b + 1) (1 - 1 / z)) := by
    intro c
    rw [regularized_connection_one_sub_recip' a b c hz hw]
    generalize (1 - 1 / z) = v
    simp only [div_eq_mul_inv, mul_inv]
    ring
  set v := 1 - 1 / z with hvdef
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hRc := (analyticOnNhd_regularizedGaussHGFun_c a b hz c₀ (Set.mem_univ _)).differentiableAt
  have hsin : HasDerivAt (fun c : ℂ => sin (Real.pi * (c - a - b)) / Real.pi)
      (cos (Real.pi * (c₀ - a - b)) * (Real.pi * 1) / Real.pi) c₀ :=
    ((((hasDerivAt_id c₀).sub_const a).sub_const b).const_mul (Real.pi : ℂ)).csin.div_const _
  have hm1 : c₀ - a - b = m := by rw [hc₀]; ring
  have hL := hsin.mul hRc.hasDerivAt
  have hcos : cos ((m : ℂ) * Real.pi) = (-1) ^ m := by
    rw [show ((m : ℂ) * Real.pi) = ((m * Real.pi : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos,
      Real.cos_nat_mul_pi]
    push_cast; ring
  rw [hm1, mul_comm (Real.pi : ℂ) (m : ℂ), hcos, Complex.sin_nat_mul_pi, zero_div, zero_mul,
    add_zero, mul_one, mul_div_cancel_right₀ _ hπ] at hL
  have hvn : ‖v‖ < 1 := hw
  -- the first series
  set S : ℂ → ℂ := fun c => regularizedGaussHGFun a (a - c + 1) (a + b - c + 1) v with hSdef
  have hSa : DifferentiableAt ℂ S c₀ :=
    (analyticOnNhd_regularizedGaussHGFun_comp (A := fun _ => a) (B := fun c => a - c + 1)
      (C := fun c => a + b - c + 1) (differentiable_const _) (by fun_prop)
      (by fun_prop) hvn c₀ (Set.mem_univ _)).differentiableAt
  have hSsum := hasSum_deriv_regularizedGaussHGFun_comp (A := fun _ => a) (B := fun c => a - c + 1)
    (C := fun c => a + b - c + 1) (differentiable_const _) (by fun_prop) (by fun_prop) hvn c₀
  have eβ : a - c₀ + 1 = β := by rw [hc₀, hβ]; ring
  have htd : ∀ n : ℕ, deriv (fun c => poch ((fun _ => a) c) n * poch ((fun c => a - c + 1) c) n *
      v ^ n / n.factorial * (Gamma ((fun c => a + b - c + 1) c + n))⁻¹) c₀ =
      poch a n * v ^ n / n.factorial * (-(poch β n * (digamma (β + n) - digamma β)) *
        (Gamma (1 - m + n))⁻¹ - poch β n * D (1 - m + n)) := by
    intro n
    have hp' : HasDerivAt (fun y => poch y n) (poch β n * (digamma (β + n) - digamma β))
        (a - c₀ + 1) := by rw [eβ]; exact hasDerivAt_poch hβnp n
    have hl1 : HasDerivAt (fun c : ℂ => a - c + 1) (-1) c₀ := by
      simpa using ((hasDerivAt_id c₀).const_sub a).add_const (1 : ℂ)
    have hl2 : HasDerivAt (fun c : ℂ => a + b - c + 1 + n) (-1) c₀ := by
      simpa using (((hasDerivAt_id c₀).const_sub (a + b)).add_const 1).add_const (n : ℂ)
    have hg := (hasDerivAt_recip_Gamma_any (a + b - c₀ + 1 + n)).comp c₀ hl2
    have h := ((((hp'.comp c₀ hl1).const_mul (poch a n)).mul_const (v ^ n)).div_const
      (n.factorial : ℂ)).mul hg
    have h' : HasDerivAt (fun c => poch a n * ((fun y => poch y n) ∘ fun c : ℂ => a - c + 1) c *
        v ^ n / n.factorial * ((fun y => (Gamma y)⁻¹) ∘ fun c : ℂ => a + b - c + 1 + n) c) _ c₀ := h
    rw [show (fun c => poch ((fun _ => a) c) n * poch ((fun c => a - c + 1) c) n *
      v ^ n / n.factorial * (Gamma ((fun c => a + b - c + 1) c + n))⁻¹) =
      fun c => poch a n * ((fun y => poch y n) ∘ fun c : ℂ => a - c + 1) c *
        v ^ n / n.factorial * ((fun y => (Gamma y)⁻¹) ∘ fun c : ℂ => a + b - c + 1 + n) c from rfl,
      h'.deriv]
    simp only [Function.comp_apply, eβ, hD,
      show a + b - c₀ + 1 + n = 1 - m + n by rw [hc₀]; ring]
    ring
  -- the second series
  set Q : ℂ → ℂ := fun c => regularizedGaussHGFun (c - b) (1 - b) (c - a - b + 1) v with hQdef
  have hQa : DifferentiableAt ℂ Q c₀ :=
    (analyticOnNhd_regularizedGaussHGFun_comp (A := fun c => c - b) (B := fun _ => 1 - b)
      (C := fun c => c - a - b + 1) (by fun_prop) (differentiable_const _) (by fun_prop) hvn c₀
      (Set.mem_univ _)).differentiableAt
  have hQsum := hasSum_deriv_regularizedGaussHGFun_comp (A := fun c => c - b) (B := fun _ => 1 - b)
    (C := fun c => c - a - b + 1) (by fun_prop) (differentiable_const _) (by fun_prop) hvn c₀
  have hmn : ∀ n : ℕ, ∀ j : ℕ, (m : ℂ) + 1 + n ≠ -(j : ℂ) := by
    intro n j hj
    have := congrArg re hj
    simp at this
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j), (Nat.cast_nonneg m : (0 : ℝ) ≤ m),
      (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have e1 : c₀ - a = b + m := by rw [hc₀]; ring
  have e2 : c₀ - b = a + m := by rw [hc₀]; ring
  have hqd : ∀ n : ℕ, deriv (fun c => poch ((fun c => c - b) c) n * poch ((fun _ => 1 - b) c) n *
      v ^ n / n.factorial * (Gamma ((fun c => c - a - b + 1) c + n))⁻¹) c₀ =
      poch (a + m) n * poch (1 - b) n * v ^ n / n.factorial * (Gamma (m + 1 + n))⁻¹ *
        (digamma (a + m + n) - digamma (a + m) - digamma (m + 1 + n)) := by
    intro n
    have e3 : c₀ - a - b + 1 + n = m + 1 + n := by rw [hc₀]; ring
    have hp' : HasDerivAt (fun y => poch y n) (poch (a + m) n * (digamma (a + m + n) -
        digamma (a + m))) (c₀ - b) := by rw [e2]; exact hasDerivAt_poch ham n
    have hg' : HasDerivAt (fun y => (Gamma y)⁻¹) (-(digamma (m + 1 + n)) * (Gamma (m + 1 + n))⁻¹)
        (c₀ - a - b + 1 + n) := by rw [e3]; exact hasDerivAt_recip_Gamma (hmn n)
    have hl1 : HasDerivAt (fun c : ℂ => c - b) 1 c₀ := (hasDerivAt_id c₀).sub_const b
    have hl3 : HasDerivAt (fun c : ℂ => c - a - b + 1 + n) 1 c₀ :=
      ((((hasDerivAt_id c₀).sub_const a).sub_const b).add_const 1).add_const _
    have h := ((((hp'.comp c₀ hl1).mul_const (poch (1 - b) n)).mul_const (v ^ n)).div_const
      (n.factorial : ℂ)).mul (hg'.comp c₀ hl3)
    have h' : HasDerivAt (fun c => ((fun y => poch y n) ∘ fun c : ℂ => c - b) c * poch (1 - b) n *
        v ^ n / n.factorial * ((fun y => (Gamma y)⁻¹) ∘ fun c : ℂ => c - a - b + 1 + n) c) _ c₀ := h
    rw [show (fun c => poch ((fun c => c - b) c) n * poch ((fun _ => 1 - b) c) n *
      v ^ n / n.factorial * (Gamma ((fun c => c - a - b + 1) c + n))⁻¹) =
      fun c => ((fun y => poch y n) ∘ fun c : ℂ => c - b) c * poch (1 - b) n *
        v ^ n / n.factorial * ((fun y => (Gamma y)⁻¹) ∘ fun c : ℂ => c - a - b + 1 + n) c from rfl,
      h'.deriv]
    simp only [Function.comp_apply, e2, e3]
    ring
  -- derivative of the right side
  have hG1 : HasDerivAt (fun c : ℂ => (Gamma (c - a))⁻¹) (-(digamma (b + m)) * (Gamma (b + m))⁻¹) c₀ := by
    have h1 : HasDerivAt (fun y => (Gamma y)⁻¹) (-(digamma (b + m)) * (Gamma (b + m))⁻¹)
        (c₀ - a) := by rw [e1]; exact hasDerivAt_recip_Gamma hbm
    simpa [Function.comp_def] using h1.comp c₀ ((hasDerivAt_id c₀).sub_const a)
  have hG2 : HasDerivAt (fun c : ℂ => (Gamma (c - b))⁻¹) (-(digamma (a + m)) * (Gamma (a + m))⁻¹) c₀ := by
    have h1 : HasDerivAt (fun y => (Gamma y)⁻¹) (-(digamma (a + m)) * (Gamma (a + m))⁻¹)
        (c₀ - b) := by rw [e2]; exact hasDerivAt_recip_Gamma ham
    simpa [Function.comp_def] using h1.comp c₀ ((hasDerivAt_id c₀).sub_const b)
  have hU : HasDerivAt (fun c : ℂ => ((1 - z) / z) ^ (c - a - b))
      (((1 - z) / z) ^ (m : ℂ) * log ((1 - z) / z) * 1) c₀ := by
    have h := (((hasDerivAt_id c₀).sub_const a).sub_const b).const_cpow (c := (1 - z) / z) (Or.inl hq0)
    rw [show _root_.id c₀ - a - b = (m : ℂ) by simp only [_root_.id]; rw [hc₀]; ring] at h
    exact h
  have hR := (hSa.hasDerivAt.mul ((hG1.mul hG2).const_mul (z ^ (-a)))).sub
    ((hU.mul hQa.hasDerivAt).const_mul ((Gamma a * Gamma b)⁻¹ * z ^ (-a)))
  have hfun : (fun c => sin (Real.pi * (c - a - b)) / Real.pi * regularizedGaussHGFun a b c z) =
      fun c => S c * (z ^ (-a) * ((Gamma (c - a))⁻¹ * (Gamma (c - b))⁻¹)) -
        (Gamma a * Gamma b)⁻¹ * z ^ (-a) * (((1 - z) / z) ^ (c - a - b) * Q c) := funext hconn
  have hL' : HasDerivAt (fun c => sin (Real.pi * (c - a - b)) / Real.pi *
      regularizedGaussHGFun a b c z) ((-1) ^ m * regularizedGaussHGFun a b c₀ z) c₀ := hL
  rw [hfun] at hL'
  have hkey := hL'.unique hR
  simp only [Pi.mul_apply] at hkey
  rw [hm1, e1, e2, cpow_natCast] at hkey
  set P : ℂ := poch a m * poch β m with hPdef
  set q : ℕ → ℂ := fun k => poch (a + m) k * poch (1 - b) k * v ^ k / k.factorial *
    (Gamma (m + 1 + k))⁻¹ with hq
  set sS : ℕ → ℂ := fun n => poch a n * poch β n * v ^ n / n.factorial *
    (Gamma (1 - m + n))⁻¹ with hsS
  have hS0 : HasSum sS (S c₀) := by
    have h := (summable_regularizedGaussHGFun_term a β (1 - m) hvn).hasSum
    rw [← regularizedGaussHGFun_eq_tsum] at h
    convert h using 1
    simp only [hSdef, eβ]; congr 1; rw [hc₀]; ring
  have hQ0 : HasSum q (Q c₀) := by
    have h := (summable_regularizedGaussHGFun_term (a + m) (1 - b) (m + 1) hvn).hasSum
    rw [← regularizedGaussHGFun_eq_tsum] at h
    convert h using 1
    simp only [hQdef]; rw [hm1, e2]
  have hGk : ∀ k : ℕ, Gamma ((m : ℂ) + 1 + k) = ((k + m).factorial : ℂ) := by
    intro k
    rw [show (m : ℂ) + 1 + k = ((k + m : ℕ) : ℂ) + 1 by push_cast; ring, Gamma_nat_eq_factorial]
  have hG1k : ∀ k : ℕ, Gamma (1 - (m : ℂ) + ((k + m : ℕ) : ℂ)) = (k.factorial : ℂ) := by
    intro k
    rw [show 1 - (m : ℂ) + ((k + m : ℕ) : ℂ) = (k : ℂ) + 1 by push_cast; ring, Gamma_nat_eq_factorial]
  have hβm : β + m = 1 - b := by rw [hβ]; ring
  have hsS_shift : ∀ k : ℕ, sS (k + m) = P * v ^ m * q k := by
    intro k
    simp only [hsS, hq, hPdef, hGk, hG1k]
    rw [add_comm k m, poch_add a m k, poch_add β m k, hβm, pow_add, add_comm m k]
    have hk : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have hkm : ((k + m).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
  have hpole : ∀ n : ℕ, n < m → 1 - (m : ℂ) + n = -((m - 1 - n : ℕ) : ℂ) := by
    intro n hn
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have hsS_low : ∀ n ∈ Finset.range m, sS n = 0 := by
    intro n hn
    rw [Finset.mem_range] at hn
    simp only [hsS, hpole n hn, Gamma_neg_nat_eq_zero, inv_zero, mul_zero]
  have hS0eq : S c₀ = P * v ^ m * Q c₀ := by
    have h := (hasSum_nat_add_iff' m).mpr hS0
    rw [Finset.sum_eq_zero hsS_low, sub_zero] at h
    exact h.unique ((hQ0.mul_left (P * v ^ m)).congr_fun fun k => (hsS_shift k).symm ▸ rfl)
  set dt : ℕ → ℂ := fun n => deriv (fun c => poch ((fun _ => a) c) n *
      poch ((fun c => a - c + 1) c) n * v ^ n / n.factorial *
      (Gamma ((fun c => a + b - c + 1) c + n))⁻¹) c₀ with hdt
  have hdt_shift : ∀ k : ℕ, dt (k + m) = P * v ^ m * q k *
      (digamma (k + 1) - digamma (b - k) + digamma (b + m)) := by
    intro k
    have hk1 : ∀ j : ℕ, (k : ℂ) + 1 ≠ -(j : ℂ) := by
      intro j hj
      have := congrArg re hj
      simp at this
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j), (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hrefl := digamma_one_sub_add_nat hbmZ (k + m)
    rw [show 1 - (b + m) + ((k + m : ℕ) : ℂ) = β + ((k + m : ℕ) : ℂ) by rw [hβ],
      show b + m - ((k + m : ℕ) : ℂ) = b - k by push_cast; ring] at hrefl
    simp only [hdt]
    rw [htd, show 1 - (m : ℂ) + ((k + m : ℕ) : ℂ) = (k : ℂ) + 1 by push_cast; ring, hD,
      deriv_recip_Gamma_eq hk1, ← hsS_shift k]
    simp only [hsS, show 1 - (m : ℂ) + ((k + m : ℕ) : ℂ) = (k : ℂ) + 1 by push_cast; ring]
    rw [hβ] at hrefl ⊢
    linear_combination (-(poch a (k + m) * v ^ (k + m) / ((k + m).factorial : ℂ) *
      poch (1 - (b + m)) (k + m) * (Gamma ((k : ℂ) + 1))⁻¹)) * hrefl
  have hdt_low : ∀ n : ℕ, n < m → dt n =
      -(poch a n * v ^ n / n.factorial) * (poch β n * ((-1) ^ (m - 1 - n) *
        ((m - 1 - n).factorial : ℂ))) := by
    intro n hn
    simp only [hdt]
    rw [htd, hpole n hn, hD, deriv_recip_Gamma_neg_nat, Gamma_neg_nat_eq_zero, inv_zero]
    ring
  have hSshift := (hasSum_nat_add_iff' m).mpr hSsum
  set L := log ((1 - z) / z) with hLdef
  have hEsum : HasSum (fun k => P * v ^ m * (q k * (L - digamma (k + 1) - digamma (m + 1 + k) +
      digamma (a + m + k) + digamma (b - k))))
      (P * v ^ m * (L + (digamma (a + m) + digamma (b + m))) * Q c₀ + P * v ^ m * deriv Q c₀ -
        (deriv S c₀ - ∑ i ∈ Finset.range m, dt i)) := by
    have h := ((hQ0.mul_left (P * v ^ m * (L + (digamma (a + m) + digamma (b + m))))).add
      (hQsum.mul_left (P * v ^ m))).sub hSshift
    convert h using 1
    funext k
    rw [hqd k, hdt_shift k]
    ring
  have hGb : Gamma b ≠ 0 := Gamma_ne_zero hb'
  have htsum : (∑' k : ℕ, poch (a + m) k / ((k.factorial : ℂ) * ((k + m).factorial : ℂ) *
      Gamma (b - k)) * (-1 : ℂ) ^ k * v ^ (k + m) * (L - digamma (k + 1) - digamma (k + m + 1) +
        digamma (a + k + m) + digamma (b - k))) = v ^ m * (Gamma b)⁻¹ * ∑' k : ℕ,
      q k * (L - digamma (k + 1) - digamma (m + 1 + k) + digamma (a + m + k) + digamma (b - k)) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    have hbk : Gamma (b - k) ≠ 0 := Gamma_ne_zero (not_neg_nat_of_not_int_sub hb k)
    simp only [hq, hGk]
    rw [poch_one_sub_eq hb k, show (k : ℂ) + m + 1 = m + 1 + k by ring,
      show a + k + m = a + m + k by ring, pow_add]
    have hk : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have hkm : ((k + m).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
  have hEval := hEsum.tsum_eq
  rw [tsum_mul_left] at hEval
  rw [htsum]
  set SE := ∑' k : ℕ, q k * (L - digamma (k + 1) - digamma (m + 1 + k) +
      digamma (a + m + k) + digamma (b - k)) with hSE
  have hGa : Gamma a ≠ 0 := Gamma_ne_zero ha
  have hGam : Gamma (a + m) = poch a m * Gamma a := by
    have h := Gamma_add_nat_div_Gamma_eq (n := m) a ha
    rw [div_eq_iff hGa] at h
    rw [h]
  have hpβ : poch β m = (-1) ^ m * Gamma (b + m) / Gamma b := by
    rw [hβ, poch_one_sub_eq hbmZ m, show b + m - (m : ℂ) = b by ring]
  have hGbm : Gamma (b + m) ≠ 0 := Gamma_ne_zero hbm
  have hGP : (Gamma (b + m))⁻¹ * (Gamma (a + m))⁻¹ * P = (-1) ^ m * (Gamma a * Gamma b)⁻¹ := by
    rw [hPdef, hpβ, hGam]
    have hPa : poch a m ≠ 0 := poch_ne_zero_of_not_neg_nat ha m
    field_simp
  have hvU : v ^ m = (-1) ^ m * ((1 - z) / z) ^ m := by
    rw [← mul_pow, hvdef]; congr 1; field_simp; ring
  have hσ : ((-1 : ℂ) ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hFin : (-1 : ℂ) ^ m * ∑ i ∈ Finset.range m, dt i = Gamma (b + m) * ∑ k ∈ Finset.range m,
      poch a k * ((m - k - 1).factorial : ℂ) / ((k.factorial : ℂ) * Gamma (b + m - k)) * v ^ k := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    have hbk : Gamma (b + m - k) ≠ 0 := Gamma_ne_zero (not_neg_nat_of_not_int_sub hbmZ k)
    rw [hdt_low k hk, show m - 1 - k = m - k - 1 by omega, hβ, poch_one_sub_eq hbmZ k]
    obtain ⟨j, hj⟩ : ∃ j, m = k + 1 + j := ⟨m - k - 1, by omega⟩
    have hσm : (-1 : ℂ) ^ m = (-1) ^ (k + 1 + j) := by rw [hj]
    rw [show m - k - 1 = j by omega, hσm]
    have hj2 : ((-1 : ℂ) ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    have hk2 : ((-1 : ℂ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    have hk0 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    field_simp
    linear_combination (poch a k * v ^ k * (j.factorial : ℂ)) * ((-1) ^ j) ^ 2 * hk2 +
      (poch a k * v ^ k * (j.factorial : ℂ)) * hj2
  have hgb' : (Gamma (b + m))⁻¹ * Gamma (b + m) = 1 := inv_mul_cancel₀ hGbm
  rw [div_eq_mul_inv (z ^ (-a)), div_eq_mul_inv (z ^ (-a))]
  set σ : ℂ := (-1) ^ m with hσdef
  set Z := z ^ (-a)
  set G0 := (Gamma (b + m))⁻¹ * (Gamma (a + m))⁻¹
  set K := (Gamma a * Gamma b)⁻¹
  set U := ((1 - z) / z) ^ m
  set ψ := digamma (a + m) + digamma (b + m)
  set R := regularizedGaussHGFun a b c₀ z
  linear_combination σ * hkey +
    (-R + σ * K * Z * U * (L * Q c₀ + deriv Q c₀) - K * Z * v ^ m * (L * Q c₀ + deriv Q c₀) -
      Z * ψ * v ^ m * Q c₀ * K - Z * K * v ^ m * SE +
      Z * K * v ^ m * ((L + ψ) * Q c₀ + deriv Q c₀)) * hσ +
    (-σ * Z * G0 * ψ) * hS0eq + (σ ^ 2 * K * Z * (L * Q c₀ + deriv Q c₀)) * hvU +
    (-σ * Z * ψ * v ^ m * Q c₀ - σ * Z * v ^ m * SE + σ * Z * v ^ m * ((L + ψ) * Q c₀ + deriv Q c₀)) * hGP +
    (σ * Z * G0) * hEval + (Z * G0) * hFin +
    (Z * (Gamma (a + m))⁻¹ * ∑ k ∈ Finset.range m,
      poch a k * ((m - k - 1).factorial : ℂ) / ((k.factorial : ℂ) * Gamma (b + m - k)) * v ^ k) * hgb'

/-- DLMF 15.8.32 on the ray `x < -1`, for all `a` with `2a + 2/3, a + 1/3 ∉ -ℕ`. -/
@[dlmf 15.8.E32]
theorem cubic_connection {a : ℂ} {x : ℝ} (hx : x < -1)
    (hc : ∀ k : ℕ, 2 * a + 2 / 3 ≠ -(k : ℂ)) (ha : ∀ k : ℕ, a + 1 / 3 ≠ -(k : ℂ)) :
    let z : ℂ := x
    let ζ := exp (2 * Real.pi * I / 3) * (1 - z) / (z - exp (4 * Real.pi * I / 3))
    (1 - z ^ 3) ^ a / (-z) ^ (3 * a) *
      (₂F₁ a (a + 1 / 3) (2 / 3) ((z⁻¹) ^ 3) / (Gamma (a + 2 / 3) * Gamma (2 / 3)) +
        exp (Real.pi * I / 3) / (z * Gamma a * Gamma (4 / 3)) * ₂F₁ (a + 1 / 3) (a + 2 / 3) (4 / 3) ((z⁻¹) ^
          3)) =
      (3 : ℂ) ^ (3 * a / 2 + 1 / 2) * exp (a * Real.pi * I / 2) * Gamma (a + 1 / 3) * (1 - ζ) ^ a /
        (2 * Real.pi * Gamma (2 * a + 2 / 3) * (-ζ) ^ (2 * a)) * ₂F₁ (a + 1 / 3) (3 * a) (2 * a + 2 / 3) (1
          / ζ) := by
  intro z ζ
  simp only [ζ, z, hcub_exp_two_third, hcub_exp_four_third]
  have ht : ((Real.sqrt 3 : ℂ) * I) ^ 2 = -3 := hcub_t_sq
  set t : ℂ := (Real.sqrt 3 : ℂ) * I with htdef
  set X : ℂ := (x : ℂ) with hXdef
  have him_t : t.im = Real.sqrt 3 := by simp [htdef]
  have hre_t : t.re = 0 := by simp [htdef]
  have hω : -1 + t ≠ 0 := by
    intro h; have := congrArg im h; simp [him_t] at this
  have h1 : 1 - X ≠ 0 := by
    intro h; have := congrArg re h; simp [hXdef] at this; linarith
  have hxm : 2 * X + 1 + t ≠ 0 := by
    intro h; have := congrArg im h; simp [him_t, hXdef] at this
  have hX0 : X ≠ 0 := by rw [hXdef]; exact_mod_cast (show x ≠ 0 by linarith)
  -- the point `u = 1/ζ`
  set Y : ℝ := -(Real.sqrt 3 / 2) * (x + 1) / (1 - x) with hY
  have hu : 1 / ((-1 + t) / 2 * (1 - X) / (X - (-1 - t) / 2)) = 1 / 2 - t / 2 * (X + 1) / (1 - X) :=
    hcub_seg_u ht hω h1 hxm
  set u : ℂ := 1 / 2 - t / 2 * (X + 1) / (1 - X) with hudef
  have huY : u = 1 / 2 + (Y : ℂ) * I := by
    rw [hudef, hY, htdef, hXdef]; push_cast; ring
  have hY0 : 0 < Y := by
    rw [hY]; apply div_pos _ (by linarith)
    nlinarith [hcub_sqrt3_pos]
  have hY1 : Y < Real.sqrt 3 / 2 := by
    rw [hY, div_lt_iff₀ (by linarith)]; nlinarith [hcub_sqrt3_pos]
  have hure : u.re = 1 / 2 := by rw [huY]; simp
  have huim : 0 < u.im := by rw [huY]; simpa using hY0
  have hun : ‖u‖ < 1 := by
    have hns : normSq u < 1 := by
      rw [huY, normSq_apply]; simp
      nlinarith [hcub_sqrt3_sq, hcub_sqrt3_pos]
    rw [normSq_eq_norm_sq] at hns
    nlinarith [norm_nonneg u]
  have hu0 : u ≠ 0 := by rintro h; rw [h] at huim; simp at huim
  have hζ : (-1 + t) / 2 * (1 - X) / (X - (-1 - t) / 2) = 1 / u := by
    rw [← hu, one_div_one_div]
  rw [hu, hζ]
  have hmain := hcub_main hc ha huim hun
  rw [← htdef, hcub_seg_Z ht h1 hX0] at hmain
  have hrel := hcub_seg_rel ht h1 hX0 hu0
  have hcp := hcub_cpow (a := a) hx hure huim hun (by rw [← htdef]; exact hrel)
  rw [← htdef] at hcp
  have hB : ₂F₁ a (a + 1 / 3) (2 / 3) (X⁻¹ ^ 3) / (Gamma (a + 2 / 3) * Gamma (2 / 3)) +
      exp (Real.pi * I / 3) / (X * Gamma a * Gamma (4 / 3)) *
        ₂F₁ (a + 1 / 3) (a + 2 / 3) (4 / 3) (X⁻¹ ^ 3) =
      Real.sqrt 3 * Gamma (a + 1 / 3) / (2 * π * Gamma (2 * a + 2 / 3)) *
        (1 + (-1 - t) / 2 * u) ^ (3 * a) * ₂F₁ (a + 1 / 3) (3 * a) (2 * a + 2 / 3) u := by
    rw [← hmain]; ring
  rw [hB]
  linear_combination (Gamma (a + 1 / 3) / (2 * π * Gamma (2 * a + 2 / 3)) *
    ₂F₁ (a + 1 / 3) (3 * a) (2 * a + 2 / 3) u) * hcp

end DLMF.Hypergeometric
