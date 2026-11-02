/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.SpecialFunctions.ChebyshevSeries
public import Mathlib.Analysis.PSeries

/-!
# Decay of Chebyshev coefficients of twice differentiable functions

If `h(θ) = f(cos θ)` is twice differentiable on `(0, π)`, with `h`, `h'` and `h''` continuous on
`[0, π]` and `h'` vanishing at both endpoints, then two integrations by parts give
`|cₙ| ≤ 2 M / n²` for the Chebyshev coefficients of `f`, where `M` bounds `|h''|`. In particular
the coefficients are absolutely summable and the Chebyshev series of `f` converges to `f` on
`[-1, 1]`. The hypotheses are stated for `h` rather than `f`, so that `f` may fail to be
differentiable at the endpoints `±1` (as for functions with an essential singularity at an
endpoint whose derivatives all vanish there).

## Main results

* `Polynomial.Chebyshev.norm_complexCoeff_le_of_hasDerivAt`: the bound `|cₙ| ≤ 2 M / n²`.
* `Polynomial.Chebyshev.summable_norm_complexCoeff_of_hasDerivAt`: absolute summability.
* `Polynomial.Chebyshev.exists_summable_series_of_hasDerivAt`: a summable Chebyshev expansion
  converging on `[-1, 1]`.
-/

@[expose] public noncomputable section
open Complex Filter MeasureTheory Set Polynomial intervalIntegral
open scoped Real Topology Interval
namespace Polynomial.Chebyshev

/-- `∫₀^π h(θ) cos(nθ) dθ = -n⁻² ∫₀^π h''(θ) cos(nθ) dθ` for `n ≥ 1` when `h'` vanishes at the
endpoints. -/
theorem integral_mul_cos_eq_of_hasDerivAt {h g₁ g₂ : ℝ → ℂ}
    (hh : ContinuousOn h (Icc 0 π)) (hh' : ∀ θ ∈ Ioo 0 π, HasDerivAt h (g₁ θ) θ)
    (hg₁ : ContinuousOn g₁ (Icc 0 π)) (hg₁0 : g₁ 0 = 0) (hg₁π : g₁ π = 0)
    (hg₁' : ∀ θ ∈ Ioo 0 π, HasDerivAt g₁ (g₂ θ) θ) (hg₂ : ContinuousOn g₂ (Icc 0 π))
    {n : ℕ} (hn : 1 ≤ n) :
    ∫ θ in (0 : ℝ)..π, h θ * (Real.cos (n * θ) : ℂ) =
      -(1 / (n : ℂ) ^ 2) * ∫ θ in (0 : ℝ)..π, g₂ θ * (Real.cos (n * θ) : ℂ) := by
  have hπ : (0 : ℝ) ≤ π := Real.pi_pos.le
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hI : [[(0 : ℝ), π]] = Icc 0 π := uIcc_of_le hπ
  have hO : Ioo (min (0 : ℝ) π) (max 0 π) = Ioo 0 π := by
    rw [min_eq_left hπ, max_eq_right hπ]
  -- first integration by parts, with `v = sin(nθ)/n`
  set v : ℝ → ℂ := fun θ => (Real.sin (n * θ) : ℂ) / n with hv
  have hvd : ∀ θ, HasDerivAt v ((Real.cos (n * θ) : ℂ)) θ := by
    intro θ
    have h1 : HasDerivAt (fun θ : ℝ => (n : ℝ) * θ) (n : ℝ) θ := by
      simpa using (hasDerivAt_id θ).const_mul (n : ℝ)
    have h2 := (h1.sin.ofReal_comp).div_const (n : ℂ)
    convert h2 using 1
    push_cast
    field_simp
  -- second integration by parts, with `w = -cos(nθ)/n²`
  set w : ℝ → ℂ := fun θ => -(Real.cos (n * θ) : ℂ) / (n : ℂ) ^ 2 with hw
  have hwd : ∀ θ, HasDerivAt w ((Real.sin (n * θ) : ℂ) / n) θ := by
    intro θ
    have h1 : HasDerivAt (fun θ : ℝ => (n : ℝ) * θ) (n : ℝ) θ := by
      simpa using (hasDerivAt_id θ).const_mul (n : ℝ)
    have h2 := ((h1.cos.ofReal_comp).neg).div_const ((n : ℂ) ^ 2)
    convert h2 using 1
    push_cast
    field_simp
  have hcosc : Continuous fun θ : ℝ => (Real.cos (n * θ) : ℂ) := by fun_prop
  have hsinc : Continuous fun θ : ℝ => (Real.sin (n * θ) : ℂ) / n := by fun_prop
  have e1 := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt (u := h) (v := v)
    (u' := g₁) (v' := fun θ => (Real.cos (n * θ) : ℂ)) (a := 0) (b := π)
    (by rw [hI]; exact hh) (fun θ _ => (hvd θ).continuousAt.continuousWithinAt)
    (by rw [hO]; exact hh') (fun θ _ => hvd θ)
    (hg₁.intervalIntegrable_of_Icc hπ)
    (hcosc.intervalIntegrable _ _)
  have e2 := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt (u := g₁) (v := w)
    (u' := g₂) (v' := fun θ => (Real.sin (n * θ) : ℂ) / n) (a := 0) (b := π)
    (by rw [hI]; exact hg₁) (fun θ _ => (hwd θ).continuousAt.continuousWithinAt)
    (by rw [hO]; exact hg₁') (fun θ _ => hwd θ)
    (hg₂.intervalIntegrable_of_Icc hπ) (hsinc.intervalIntegrable _ _)
  have hvπ : v π = 0 := by
    simp only [hv, Real.sin_nat_mul_pi, ofReal_zero, zero_div]
  have hv0 : v 0 = 0 := by simp [hv]
  rw [e1, hvπ, hv0, mul_zero, mul_zero, sub_zero, zero_sub]
  have e1' : (∫ θ in (0 : ℝ)..π, g₁ θ * v θ) =
      ∫ θ in (0 : ℝ)..π, g₁ θ * ((Real.sin (n * θ) : ℂ) / n) := rfl
  rw [e1', e2, hg₁0, hg₁π, zero_mul, zero_mul, sub_zero, zero_sub]
  have e3 : (∫ θ in (0 : ℝ)..π, g₂ θ * w θ) =
      -(1 / (n : ℂ) ^ 2) * ∫ θ in (0 : ℝ)..π, g₂ θ * (Real.cos (n * θ) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [hw]
    ring
  rw [e3]
  ring

/-- **Chebyshev coefficients of `C²` data.** If `h(θ) = f(cos θ)` has derivatives `g₁`, `g₂` on
`(0, π)` that are continuous on `[0, π]`, with `g₁(0) = g₁(π) = 0` and `|g₂| ≤ M`, then
`‖cₙ‖ ≤ 2 M / n²` for `n ≥ 1`. -/
theorem norm_complexCoeff_le_of_hasDerivAt {f g₁ g₂ : ℝ → ℂ} {M : ℝ}
    (hf : ContinuousOn (fun θ => f (Real.cos θ)) (Icc 0 π))
    (hf' : ∀ θ ∈ Ioo 0 π, HasDerivAt (fun θ => f (Real.cos θ)) (g₁ θ) θ)
    (hg₁ : ContinuousOn g₁ (Icc 0 π)) (hg₁0 : g₁ 0 = 0) (hg₁π : g₁ π = 0)
    (hg₁' : ∀ θ ∈ Ioo 0 π, HasDerivAt g₁ (g₂ θ) θ) (hg₂ : ContinuousOn g₂ (Icc 0 π))
    (hM : ∀ θ ∈ Icc 0 π, ‖g₂ θ‖ ≤ M) {n : ℕ} (hn : 1 ≤ n) :
    ‖complexCoeff f n‖ ≤ 2 * M / (n : ℝ) ^ 2 := by
  have hπ := Real.pi_pos
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  rw [complexCoeff, integral_mul_cos_eq_of_hasDerivAt hf hf' hg₁ hg₁0 hg₁π hg₁' hg₂ hn]
  have hb : ‖∫ θ in (0 : ℝ)..π, g₂ θ * (Real.cos (n * θ) : ℂ)‖ ≤ M * |π - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθ => ?_
    rw [uIoc_of_le hπ.le] at hθ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖g₂ θ‖ * |Real.cos (n * θ)| ≤ M * 1 :=
          mul_le_mul (hM θ (Ioc_subset_Icc_self hθ)) (Real.abs_cos_le_one _) (abs_nonneg _)
            ((norm_nonneg _).trans (hM θ (Ioc_subset_Icc_self hθ)))
      _ = M := mul_one M
  rw [sub_zero, abs_of_pos hπ] at hb
  rw [norm_mul, norm_mul, norm_neg, norm_div, norm_div, norm_one, norm_pow, Complex.norm_natCast,
    Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg hπ.le]
  calc 2 / π * (1 / (n : ℝ) ^ 2 * ‖∫ θ in (0 : ℝ)..π, g₂ θ * (Real.cos (n * θ) : ℂ)‖)
      ≤ 2 / π * (1 / (n : ℝ) ^ 2 * (M * π)) := by gcongr
    _ = 2 * M / (n : ℝ) ^ 2 := by field_simp

/-- Under the hypotheses of `norm_complexCoeff_le_of_hasDerivAt` the Chebyshev coefficients are
absolutely summable. -/
theorem summable_norm_complexCoeff_of_hasDerivAt {f g₁ g₂ : ℝ → ℂ}
    (hf : ContinuousOn (fun θ => f (Real.cos θ)) (Icc 0 π))
    (hf' : ∀ θ ∈ Ioo 0 π, HasDerivAt (fun θ => f (Real.cos θ)) (g₁ θ) θ)
    (hg₁ : ContinuousOn g₁ (Icc 0 π)) (hg₁0 : g₁ 0 = 0) (hg₁π : g₁ π = 0)
    (hg₁' : ∀ θ ∈ Ioo 0 π, HasDerivAt g₁ (g₂ θ) θ) (hg₂ : ContinuousOn g₂ (Icc 0 π)) :
    Summable fun n => ‖complexCoeff f n‖ := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hg₂
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (((summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr one_lt_two)).mul_left (2 * M))
  have h := norm_complexCoeff_le_of_hasDerivAt hf hf' hg₁ hg₁0 hg₁π hg₁' hg₂ hM
    (n := n + 1) (by omega)
  refine h.trans (le_of_eq ?_)
  ring

/-- A summable Chebyshev expansion on `[-1, 1]` for `f` with `C²` data `θ ↦ f(cos θ)` as in
`norm_complexCoeff_le_of_hasDerivAt`, including the endpoints. -/
theorem exists_summable_series_of_hasDerivAt {f g₁ g₂ : ℝ → ℂ}
    (hfc : ContinuousOn f (Icc (-1) 1))
    (hf' : ∀ θ ∈ Ioo 0 π, HasDerivAt (fun θ => f (Real.cos θ)) (g₁ θ) θ)
    (hg₁ : ContinuousOn g₁ (Icc 0 π)) (hg₁0 : g₁ 0 = 0) (hg₁π : g₁ π = 0)
    (hg₁' : ∀ θ ∈ Ioo 0 π, HasDerivAt g₁ (g₂ θ) θ) (hg₂ : ContinuousOn g₂ (Icc 0 π)) :
    ∃ c : ℕ → ℂ, Summable c ∧ ∀ x ∈ Icc (-1 : ℝ) 1,
      HasSum (fun n : ℕ => c n * (T ℂ (n : ℤ)).eval (x : ℂ)) (f x) := by
  have hf : ContinuousOn (fun θ => f (Real.cos θ)) (Icc 0 π) :=
    hfc.comp Real.continuous_cos.continuousOn fun θ _ =>
      ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have hs := summable_norm_complexCoeff_of_hasDerivAt hf hf' hg₁ hg₁0 hg₁π hg₁' hg₂
  let c : ℕ → ℂ := fun n => (if n = 0 then 1 / 2 else 1) * complexCoeff f n
  have hc : Summable c := by
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hs
    dsimp [c]
    split_ifs
    · rw [norm_mul]
      norm_num
      exact mul_le_of_le_one_left (norm_nonneg _) (by norm_num)
    · simp
  exact ⟨c, hc, fun x hx => hasSum_complexCoeff_mul_T hfc hs hx⟩

end Polynomial.Chebyshev
