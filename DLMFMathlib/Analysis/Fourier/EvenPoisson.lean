/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.BoundedVariation.Sampling
public import Mathlib.Analysis.Fourier.PoissonSummation
import DLMFMathlib.Analysis.Fourier.BoundedVariationPeriodization
import DLMFMathlib.MeasureTheory.Integral.HalfLine
import DLMFMathlib.Algebra.BigOperators
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Fourier transforms and Poisson summation for even extensions

The Fourier transform of an even extension is twice the positive-half cosine integral.
The target may be any complex normed space; no completeness assumption is needed for this
integral identity. The proof imports the project's half-line integral splitting and
TauCeti's integrability of even extensions, with Mathlib's Fourier-character normalization.
The full-line bounded-variation Poisson theorem then gives the half-line cosine formula,
without a separate assumption of decay at infinity.

* `Real.fourier_comp_abs_eq_cos_integral`: the even-extension transform identity.
* `Real.exists_limit_poisson_cos_of_boundedVariationOn`: the half-line Poisson formula.
-/

public noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology FourierTransform Real

/-- The Fourier transform of an integrable even extension is twice its half-line cosine
integral, for any complex normed target. -/
lemma Real.fourier_comp_abs_eq_cos_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℝ → E}
    (hi : IntegrableOn f (Ioi 0)) (w : ℝ) :
    𝓕 (fun t : ℝ => f |t|) w =
      (2 : ℂ) • ∫ t in Ioi (0 : ℝ), (Real.cos (2 * π * w * t) : ℂ) • f t := by
  have hfull := TauCeti.MeasureTheory.integrable_comp_abs hi
  have hphase := (Real.fourierIntegral_convergent_iff (f := fun t : ℝ => f |t|) w).mpr hfull
  rw [Real.fourier_eq, integral_eq_integral_Ioi_add_neg hphase,
    ← integral_smul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [Real.inner_apply, abs_neg, abs_of_pos ht, Circle.smul_def,
    Real.fourierChar_apply]
  rw [← add_smul, ← mul_smul]
  congr 1
  rw [Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf


namespace Real
/-- Poisson's cosine formula for a continuous integrable function of bounded variation on
the positive half-line. Both sequences of partial sums converge to a common value. -/
lemma exists_limit_poisson_cos_of_boundedVariationOn {f : ℝ → ℂ}
    (hc : ContinuousOn f (Ici 0)) (hbv : BoundedVariationOn f (Ici 0))
    (hi : IntegrableOn f (Ioi 0)) :
    ∃ s : ℂ, Tendsto (fun N : ℕ => f 0 / 2 + ∑ n ∈ Finset.range N, f (n + 1)) atTop (𝓝 s) ∧
      Tendsto (fun N : ℕ => (∫ x in Ioi (0 : ℝ), f x) + 2 * ∑ n ∈ Finset.range N,
        ∫ x in Ioi (0 : ℝ), f x * (Real.cos (2 * π * (n + 1 : ℕ) * x) : ℂ)) atTop (𝓝 s) := by
  let g : ℝ → ℂ := fun t => f |t|
  have hgc : Continuous g := hc.comp_continuous continuous_abs (fun t => abs_nonneg t)
  have hgi : Integrable g := TauCeti.MeasureTheory.integrable_comp_abs hi
  have hgbv : BoundedVariationOn g univ := hbv.comp_abs
  have hP := tendsto_sum_Icc_fourier_of_boundedVariationOn hgc hgi hgbv
  have hsfnorm : Summable (fun n : ℕ => ‖f (n : ℝ)‖) := by
    simpa only [zero_add] using hbv.summable_norm_comp_nat_add_of_integrableOn
      hi.norm (x := 0) ⟨le_rfl, zero_le_one⟩
  have hsf : Summable (fun n : ℕ => f (n : ℝ)) := hsfnorm.of_norm
  have hsnext := (summable_nat_add_iff 1).mpr hsf
  have hgnat : Summable (fun n : ℕ => g (n : ℤ)) := by
    apply hsf.congr
    intro n
    simp only [g, Int.cast_natCast]
    rw [abs_of_nonneg (Nat.cast_nonneg n)]
  have hgneg : Summable (fun n : ℕ => g ((-((n : ℤ) + 1) : ℤ) : ℝ)) := by
    apply hsnext.congr
    intro n
    simp only [g, Int.cast_neg, Int.cast_add, Int.cast_one, Int.cast_natCast,
      abs_neg, Nat.cast_add, Nat.cast_one]
    rw [abs_of_nonneg (by positivity)]
  have hgsum : Summable (fun n : ℤ => g n) := hgnat.of_nat_of_neg_add_one hgneg
  have hgeven : (fun n : ℤ => g n).Even := by
    intro n
    simp only [g, Int.cast_neg, abs_neg]
  have hZ : (∑' n : ℤ, g n) = f 0 + 2 * ∑' n : ℕ, f ((n + 1 : ℕ) : ℝ) := by
    rw [tsum_int_eq_zero_add_two_mul_tsum_pnat hgeven hgsum]
    have he : (∑' n : ℕ+, g (n : ℤ)) = ∑' n : ℕ, f ((n + 1 : ℕ) : ℝ) := by
      calc
        _ = ∑' n : ℕ, g ((n + 1 : ℕ) : ℤ) :=
          tsum_pnat_eq_tsum_succ (f := fun n : ℕ => g (n : ℤ))
        _ = _ := by
          apply tsum_congr
          intro n
          simp only [g, Int.cast_natCast]
          rw [abs_of_nonneg (Nat.cast_nonneg (n + 1))]
    rw [he]
    simp only [g, Int.cast_zero, abs_zero, two_smul]
    ring
  let s : ℂ := f 0 / 2 + ∑' n : ℕ, f ((n + 1 : ℕ) : ℝ)
  refine ⟨s, ?_, ?_⟩
  · dsimp only [s]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_const_nhds (x := f 0 / 2)).add hsnext.hasSum.tendsto_sum_nat
  · have hhalf := hP.div_const (2 : ℂ)
    rw [hZ] at hhalf
    have hlim : (f 0 + 2 * ∑' n : ℕ, f ((n + 1 : ℕ) : ℝ)) / 2 = s := by
      dsimp only [s]
      ring
    rw [hlim] at hhalf
    apply hhalf.congr
    intro N
    rw [Finset.sum_Icc_neg_natCast_eq_sum_range]
    have ht (n : ℤ) : 𝓕 g (n : ℝ) =
        2 * ∫ x in Ioi (0 : ℝ), f x * (Real.cos (2 * π * (n : ℝ) * x) : ℂ) := by
      simpa only [g, smul_eq_mul, mul_comm] using fourier_comp_abs_eq_cos_integral hi (n : ℝ)
    simp_rw [ht]
    simp only [Int.cast_zero, mul_zero, zero_mul, Real.cos_zero, ofReal_one, mul_one, Int.cast_neg,
      Int.cast_add, Int.cast_one, Int.cast_natCast, mul_neg, neg_mul, cos_neg,
      Nat.cast_add, Nat.cast_one]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
end Real
