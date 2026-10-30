/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy

/-!
# Taylor coefficients obstruct separated analytic products

For a convergent bivariate power series, a local representation as `f(x) * g(y)`
forces `c(1, 1) * c(0, 0) = c(1, 0) * c(0, 1)`. The proof restricts the series to
its coordinate axes and diagonal, differentiates term by term, and uses Mathlib's
Leibniz rule `iteratedDeriv_fun_mul`.
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory
open scoped Topology

namespace Complex

open Finset

/-- Restricting a convergent bivariate series to a complex line gives its homogeneous
Taylor coefficients. -/
private lemma line_iterated {c : ℕ × ℕ → ℂ} {r : ℝ} (hr : 0 < r)
    (hc : Summable (fun q => ‖c q‖ * r ^ q.1 * r ^ q.2))
    (X Y : ℂ) (hX : ‖X‖ ≤ 1) (hY : ‖Y‖ ≤ 1) (n : ℕ) :
    iteratedDeriv n (fun t : ℂ => ∑' q : ℕ × ℕ, c q * (t * X) ^ q.1 * (t * Y) ^ q.2) 0 =
      ∑ q ∈ (range (n + 1)).product (range (n + 1)),
        if n = q.1 + q.2 then (q.1 + q.2).factorial * c q * X ^ q.1 * Y ^ q.2 else 0 := by
  have hdom : ∀ z ∈ Metric.ball (0 : ℂ) r, ∃ V ∈ 𝓝 z, ∃ g : ℕ × ℕ → ℝ,
      Summable g ∧ ∀ q, ∀ t ∈ V, ‖c q * (t * X) ^ q.1 * (t * Y) ^ q.2‖ ≤ g q := by
    intro z hz
    refine ⟨Metric.ball 0 r, Metric.isOpen_ball.mem_nhds hz, _, hc, fun q t ht => ?_⟩
    rw [mem_ball_zero_iff] at ht
    simp only [norm_mul, norm_pow]
    have h1 : ‖t‖ * ‖X‖ ≤ r := (mul_le_of_le_one_right (norm_nonneg t) hX).trans ht.le
    have h2 : ‖t‖ * ‖Y‖ ≤ r := (mul_le_of_le_one_right (norm_nonneg t) hY).trans ht.le
    gcongr
  rw [Complex.iteratedDeriv_tsum_of_locally_dominated Metric.isOpen_ball (fun q => by fun_prop)
    hdom n (Metric.mem_ball_self hr)]
  have hterm : ∀ q : ℕ × ℕ,
      iteratedDeriv n (fun t : ℂ => c q * (t * X) ^ q.1 * (t * Y) ^ q.2) 0 =
        if n = q.1 + q.2 then (q.1 + q.2).factorial * c q * X ^ q.1 * Y ^ q.2 else 0 := by
    intro q
    have heq : (fun t : ℂ => c q * (t * X) ^ q.1 * (t * Y) ^ q.2) =
        (fun t => (c q * X ^ q.1 * Y ^ q.2) * t ^ (q.1 + q.2)) := by
      funext t
      simp only [mul_pow, pow_add]
      ring
    rw [heq, iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
    split_ifs <;> ring
  simp_rw [hterm]
  apply tsum_eq_sum
  intro q hq
  have hn : n ≠ q.1 + q.2 := by
    intro he
    apply hq
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
  simp [hn]

/-- The constant coefficient is the value of a convergent bivariate series at the origin. -/
private lemma line_zero {c : ℕ × ℕ → ℂ} {r : ℝ} (hr : 0 < r)
    (hc : Summable (fun q => ‖c q‖ * r ^ q.1 * r ^ q.2))
    (X Y : ℂ) (hX : ‖X‖ ≤ 1) (hY : ‖Y‖ ≤ 1) :
    (∑' q : ℕ × ℕ, c q * ((0 : ℂ) * X) ^ q.1 * ((0 : ℂ) * Y) ^ q.2) = c (0, 0) := by
  simpa [Finset.sum_product, Finset.sum_range_succ] using line_iterated hr hc X Y hX hY 0

/-- The first derivative along a line is determined by the two linear coefficients. -/
private lemma line_one {c : ℕ × ℕ → ℂ} {r : ℝ} (hr : 0 < r)
    (hc : Summable (fun q => ‖c q‖ * r ^ q.1 * r ^ q.2))
    (X Y : ℂ) (hX : ‖X‖ ≤ 1) (hY : ‖Y‖ ≤ 1) :
    deriv (fun t : ℂ => ∑' q : ℕ × ℕ, c q * (t * X) ^ q.1 * (t * Y) ^ q.2) 0 =
      c (1, 0) * X + c (0, 1) * Y := by
  have h := line_iterated hr hc X Y hX hY 1
  norm_num [Finset.sum_product, Finset.sum_range_succ, Nat.factorial] at h
  convert h using 1
  ring

/-- The second derivative along a line is determined by the three quadratic coefficients. -/
private lemma line_two {c : ℕ × ℕ → ℂ} {r : ℝ} (hr : 0 < r)
    (hc : Summable (fun q => ‖c q‖ * r ^ q.1 * r ^ q.2))
    (X Y : ℂ) (hX : ‖X‖ ≤ 1) (hY : ‖Y‖ ≤ 1) :
    iteratedDeriv 2 (fun t : ℂ => ∑' q : ℕ × ℕ, c q * (t * X) ^ q.1 * (t * Y) ^ q.2) 0 =
      2 * c (2, 0) * X ^ 2 + 2 * c (1, 1) * X * Y + 2 * c (0, 2) * Y ^ 2 := by
  have h := line_iterated hr hc X Y hX hY 2
  norm_num [Finset.sum_product, Finset.sum_range_succ, Nat.factorial] at h
  convert h using 1
  ring

/-- An analytic product decomposition forces the constant, linear and mixed coefficients
to have zero determinant. -/
private lemma nonsep_coeff {c : ℕ × ℕ → ℂ} {r : ℝ} (hr : 0 < r)
    (hc : Summable (fun q => ‖c q‖ * r ^ q.1 * r ^ q.2))
    (hbad : c (1, 1) * c (0, 0) ≠ c (1, 0) * c (0, 1)) :
    ¬ ∃ f g : ℂ → ℂ, AnalyticAt ℂ f 0 ∧ AnalyticAt ℂ g 0 ∧
      (fun p : ℂ × ℂ => ∑' q : ℕ × ℕ, c q * p.1 ^ q.1 * p.2 ^ q.2) =ᶠ[𝓝 (0, 0)]
        (fun p => f p.1 * g p.2) := by
  rintro ⟨f, g, hf, hg, hfg⟩
  let F : ℂ → ℂ := fun t => ∑' q : ℕ × ℕ, c q * t ^ q.1 * t ^ q.2
  let A : ℂ → ℂ := fun t => ∑' q : ℕ × ℕ, c q * t ^ q.1 * (0 : ℂ) ^ q.2
  let B : ℂ → ℂ := fun t => ∑' q : ℕ × ℕ, c q * (0 : ℂ) ^ q.1 * t ^ q.2
  have hF := hfg.comp_tendsto (show Tendsto (fun t : ℂ => (t, t)) (𝓝 0) (𝓝 (0, 0))
    from tendsto_id.prodMk_nhds tendsto_id)
  have hA := hfg.comp_tendsto (show Tendsto (fun t : ℂ => (t, 0)) (𝓝 0) (𝓝 (0, 0))
    from tendsto_id.prodMk_nhds tendsto_const_nhds)
  have hB := hfg.comp_tendsto (show Tendsto (fun t : ℂ => (0, t)) (𝓝 0) (𝓝 (0, 0))
    from tendsto_const_nhds.prodMk_nhds tendsto_id)
  change F =ᶠ[𝓝 (0 : ℂ)] (fun t => f t * g t) at hF
  change A =ᶠ[𝓝 (0 : ℂ)] (fun t => f t * g 0) at hA
  change B =ᶠ[𝓝 (0 : ℂ)] (fun t => f 0 * g t) at hB
  have h00 : c (0, 0) = f 0 * g 0 := by
    have h0 := line_zero hr hc 1 1 (by norm_num) (by norm_num)
    simp only [mul_one] at h0
    simpa only [F] using h0.symm.trans hF.eq_of_nhds
  have h10 : c (1, 0) = deriv f 0 * g 0 := by
    have h := hA.deriv_eq
    have h0 := line_one hr hc 1 0 (by norm_num) (by norm_num)
    simp only [mul_one, mul_zero] at h0
    rw [show (fun t => f t * g 0) = fun t => g 0 * f t by funext t; ring,
      (hf.differentiableAt.hasDerivAt.const_mul (g 0)).deriv] at h
    simpa [A, mul_comm] using h0.symm.trans h
  have h01 : c (0, 1) = f 0 * deriv g 0 := by
    have h := hB.deriv_eq
    have h0 := line_one hr hc 0 1 (by norm_num) (by norm_num)
    simp only [mul_one, mul_zero] at h0
    rw [(hg.differentiableAt.hasDerivAt.const_mul (f 0)).deriv] at h
    simpa [B] using h0.symm.trans h
  have h20 : 2 * c (2, 0) = iteratedDeriv 2 f 0 * g 0 := by
    have h := hA.iteratedDeriv_eq 2
    have h0 := line_two hr hc 1 0 (by norm_num) (by norm_num)
    simp only [mul_one, mul_zero] at h0
    rw [iteratedDeriv_mul_const_field] at h
    simpa [A] using h0.symm.trans h
  have h02 : 2 * c (0, 2) = f 0 * iteratedDeriv 2 g 0 := by
    have h := hB.iteratedDeriv_eq 2
    have h0 := line_two hr hc 0 1 (by norm_num) (by norm_num)
    simp only [mul_one, mul_zero] at h0
    rw [iteratedDeriv_const_mul_field] at h
    simpa [B] using h0.symm.trans h
  have h11 : c (1, 1) = deriv f 0 * deriv g 0 := by
    have h := hF.iteratedDeriv_eq 2
    have h0 := line_two hr hc 1 1 (by norm_num) (by norm_num)
    simp only [mul_one] at h0
    rw [iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt] at h
    simp [F, sum_range_succ, iteratedDeriv_zero,
      iteratedDeriv_one] at h0 h
    linear_combination (h0.symm.trans h) / 2 - h20 / 2 - h02 / 2
  apply hbad
  rw [h00, h10, h01, h11]
  ring

/-- A nonzero determinant of the constant, linear and mixed Taylor coefficients rules out
a local product of one-variable analytic functions. -/
lemma not_exists_mul_analyticAt_of_coeff_ne {c : ℕ × ℕ → ℂ}
    (hdom : ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ Summable (fun q => ‖c q‖ * A ^ q.1 * B ^ q.2))
    (hbad : c (1, 1) * c (0, 0) ≠ c (1, 0) * c (0, 1)) :
    ¬ ∃ f g : ℂ → ℂ, AnalyticAt ℂ f 0 ∧ AnalyticAt ℂ g 0 ∧
      (fun p : ℂ × ℂ => ∑' q : ℕ × ℕ, c q * p.1 ^ q.1 * p.2 ^ q.2) =ᶠ[𝓝 (0, 0)]
        (fun p => f p.1 * g p.2) := by
  obtain ⟨A, B, hA, hB, hc⟩ := hdom
  apply nonsep_coeff (lt_min hA hB) _ hbad
  refine Summable.of_nonneg_of_le (fun q => by positivity) (fun q => ?_) hc
  gcongr
  · exact min_le_left A B
  · exact min_le_right A B

end Complex
