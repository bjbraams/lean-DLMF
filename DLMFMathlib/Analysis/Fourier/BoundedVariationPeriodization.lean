/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import DLMFMathlib.Analysis.Fourier.CosinePartialSumKernel
import DLMFMathlib.Analysis.Fourier.CosineKernelConvergence
import DLMFMathlib.Algebra.BigOperators
import DLMFMathlib.Analysis.BoundedVariation.Sampling
import DLMFMathlib.Analysis.BoundedVariation.Series
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
# Periodization of integrable functions of bounded variation

The integer translates of an integrable continuous bounded-variation function form a locally
normally convergent series. Its periodization is continuous and has bounded variation on the
unit interval.

* `BoundedVariationOn.summable_norm_restrict`: local normal convergence of the periodization.
* `BoundedVariationOn.continuous_tsum_comp_add_int`: continuity of the periodization.
* `BoundedVariationOn.boundedVariationOn_tsum_comp_add_int_unit`: bounded variation.
* `Real.tendsto_sum_Icc_fourierCoeff_of_boundedVariationOn`: Fourier series at zero.
* `Real.tendsto_sum_Icc_fourier_of_boundedVariationOn`: Poisson summation with symmetric
  Fourier partial sums.

The proof uses Mathlib's continuous-map summation and Poisson summation APIs. The sampling and
variation estimates come from `DLMFMathlib.Analysis.BoundedVariation`. The endpoint
Dirichlet–Jordan limit is in `DLMFMathlib.Analysis.Fourier.CosineKernelConvergence`.
-/

public noncomputable section
open Set MeasureTheory Filter Topology TopologicalSpace
open scoped Real FourierTransform

namespace BoundedVariationOn
variable {E : Type*} [NormedAddCommGroup E] {f : C(ℝ, E)}
/-- The sup norms on a unit interval of all integer translates are summable for an integrable
continuous function of bounded variation on the real line. -/
lemma summable_norm_restrict_unit (hbv : BoundedVariationOn f univ)
    (hi : Integrable f) :
    Summable (fun n : ℤ => ‖(f.comp (ContinuousMap.addRight n)).restrict
      (⟨Icc (0 : ℝ) 1, isCompact_Icc⟩ : Compacts ℝ)‖) := by
  obtain ⟨B, hB, hbound⟩ := (hbv.mono (subset_univ (Ici 0))).exists_summable_bound_nat_unit
    (hi.norm.integrableOn)
  have hbvneg : BoundedVariationOn (fun t : ℝ => f (-t)) (Ici 0) :=
    ne_top_of_le_ne_top hbv (eVariationOn.comp_le_of_antitoneOn f (fun t : ℝ => -t)
      (fun _ _ _ _ h => neg_le_neg h) (fun _ _ => mem_univ _))
  obtain ⟨C, hC, hcbound⟩ := hbvneg.exists_summable_bound_nat_unit (hi.comp_neg.norm.integrableOn)
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor
  · apply hB.of_nonneg_of_le (fun _ => norm_nonneg _)
    intro n
    apply (ContinuousMap.norm_le _ (le_trans (norm_nonneg (f n))
      (by simpa using hbound n 0 ⟨le_rfl, zero_le_one⟩))).mpr
    intro x
    exact hbound n x x.property
  · apply (summable_nat_add_iff 1).mp
    apply hC.of_nonneg_of_le (fun _ => norm_nonneg _)
    intro n
    apply (ContinuousMap.norm_le _ (le_trans (norm_nonneg (f (-(n : ℝ))))
      (by simpa using hcbound n 0 ⟨le_rfl, zero_le_one⟩))).mpr
    intro x
    have h := hcbound n (1 - x) ⟨by linarith [x.property.2], by linarith [x.property.1]⟩
    convert h using 1
    simp only [ContinuousMap.restrict_apply, ContinuousMap.comp_apply, ContinuousMap.coe_addRight]
    congr 2
    push_cast
    ring
end BoundedVariationOn
namespace BoundedVariationOn
variable {E : Type*} [NormedAddCommGroup E] {f : C(ℝ, E)}
/-- The sup norms on every compact set of all integer translates are summable for an integrable
continuous function of bounded variation on the real line. -/
lemma summable_norm_restrict (hbv : BoundedVariationOn f univ)
    (hi : Integrable f) (K : Compacts ℝ) :
    Summable (fun n : ℤ => ‖(f.comp (ContinuousMap.addRight n)).restrict K‖) := by
  let U : ℤ → ℝ := fun n => ‖(f.comp (ContinuousMap.addRight n)).restrict
    (⟨Icc (0 : ℝ) 1, isCompact_Icc⟩ : Compacts ℝ)‖
  have hU : Summable U := hbv.summable_norm_restrict_unit hi
  have hUnonneg (n : ℤ) : 0 ≤ U n := norm_nonneg _
  obtain ⟨a, ha⟩ := K.isCompact.bddBelow
  obtain ⟨b, hb⟩ := K.isCompact.bddAbove
  obtain ⟨A, hA⟩ := exists_int_le a
  obtain ⟨B, hB⟩ := exists_int_ge b
  have hsum : Summable (fun n : ℤ => ∑ k ∈ Finset.Icc A B, U (n + k)) := by
    apply summable_sum
    intro k _
    exact (Equiv.addRight k).summable_iff.mpr hU
  apply hsum.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  apply (ContinuousMap.norm_le _ (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mpr
  intro x
  let k : ℤ := ⌊(x : ℝ)⌋
  have hk : k ∈ Finset.Icc A B := by
    rw [Finset.mem_Icc]
    constructor
    · exact Int.le_floor.mpr (hA.trans (ha x.property))
    · have hxb : (x : ℝ) ≤ B := (hb x.property).trans hB
      exact_mod_cast (Int.floor_le (x : ℝ)).trans hxb
  have hxunit : (x : ℝ) - k ∈ Icc (0 : ℝ) 1 :=
    ⟨sub_nonneg.mpr (Int.floor_le _), by have := Int.lt_floor_add_one (x : ℝ); linarith⟩
  have hpoint : ‖f ((x : ℝ) + n)‖ ≤ U (n + k) := by
    have h := ((f.comp (ContinuousMap.addRight (n + k))).restrict
      (⟨Icc (0 : ℝ) 1, isCompact_Icc⟩ : Compacts ℝ)).norm_coe_le_norm
        ⟨(x : ℝ) - k, hxunit⟩
    convert h using 1
    · simp only [ContinuousMap.restrict_apply, ContinuousMap.comp_apply, ContinuousMap.coe_addRight]
      congr 2
      ring
    · simp only [U, Int.cast_add]
  exact hpoint.trans (Finset.single_le_sum (fun i _ => hUnonneg (n + i)) hk)
end BoundedVariationOn
namespace BoundedVariationOn
variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] {f : C(ℝ, E)}
/-- The integer periodization of an integrable continuous bounded-variation function
is continuous. -/
lemma continuous_tsum_comp_add_int (hbv : BoundedVariationOn f univ) (hi : Integrable f) :
    Continuous (fun x : ℝ => ∑' n : ℤ, f (x + n)) := by
  have hs := ContinuousMap.summable_of_locally_summable_norm
    (fun K => hbv.summable_norm_restrict hi K)
  have he : (fun x : ℝ => ∑' n : ℤ, f (x + n)) =
      (∑' n : ℤ, f.comp (ContinuousMap.addRight n)) := by
    funext x
    exact ContinuousMap.tsum_apply hs x
  rw [he]
  exact ContinuousMap.continuous _
end BoundedVariationOn
namespace BoundedVariationOn
variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] {f : C(ℝ, E)}
/-- The integer periodization of an integrable continuous bounded-variation function has bounded
variation on the unit interval. -/
lemma boundedVariationOn_tsum_comp_add_int_unit (hbv : BoundedVariationOn f univ)
    (hi : Integrable f) : BoundedVariationOn (fun x : ℝ => ∑' n : ℤ, f (x + n)) (Icc 0 1) := by
  have hv := hbv.summable_variation_int_unit
  have hcell (n : ℤ) : eVariationOn f (Icc (n : ℝ) (n + 1)) ≠ ⊤ :=
    hbv.mono (subset_univ _)
  have hfin : (∑' n : ℤ, eVariationOn f (Icc (n : ℝ) (n + 1))) ≠ ⊤ := by
    have he := ENNReal.ofReal_tsum_of_nonneg
      (fun n : ℤ => ENNReal.toReal_nonneg (a := eVariationOn f (Icc (n : ℝ) (n + 1)))) hv
    simp only [ENNReal.ofReal_toReal (hcell _)] at he
    rw [← he]
    exact ENNReal.ofReal_ne_top
  apply ne_top_of_le_ne_top hfin
  have hs := ContinuousMap.summable_of_locally_summable_norm
    (fun K => hbv.summable_norm_restrict hi K)
  have hbound := eVariationOn.tsum_le (F := fun n : ℤ => fun x : ℝ => f (x + n))
    (s := Icc 0 1) (fun x _ => (ContinuousMap.hasSum_apply hs.hasSum x).summable)
  apply hbound.trans
  apply tsum_le_tsum
  intro n
  apply eVariationOn.comp_le_of_monotoneOn f (fun x : ℝ => x + n)
    (fun _ _ _ _ h => by dsimp only; linarith)
  intro x hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
end BoundedVariationOn

namespace Real
/-- A symmetric finite sum of the period-one Fourier functions is twice the cosine kernel. -/
lemma sum_fourier_eq_cosinePartialSumKernel (N : ℕ) (x : ℝ) :
    (∑ n ∈ Finset.Icc (-(N : ℤ)) N, @fourier 1 n (x : UnitAddCircle)) =
      (2 : ℂ) * (cosinePartialSumKernel N (2 * π * x) : ℂ) := by
  rw [Finset.sum_Icc_neg_natCast_eq_sum_range]
  simp only [fourier_zero, cosinePartialSumKernel_def, Complex.ofReal_add,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_sum]
  rw [mul_add, Finset.mul_sum]
  norm_num only [mul_div_cancel₀ (1 : ℂ) (by norm_num : (2 : ℂ) ≠ 0)]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  simp only [fourier_coe_apply, Complex.ofReal_one, div_one, Int.cast_neg, Int.cast_add,
    Int.cast_natCast, Int.cast_one]
  have he₁ : 2 * (π : ℂ) * Complex.I * ((n : ℂ) + 1) * x =
      (((n + 1 : ℕ) : ℝ) * (2 * π * x) : ℝ) * Complex.I := by push_cast; ring
  have he₂ : 2 * (π : ℂ) * Complex.I * -((n : ℂ) + 1) * x =
      -((((n + 1 : ℕ) : ℝ) * (2 * π * x) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [he₁, he₂, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    ← Complex.ofReal_cos]
  ring
end Real
namespace Real
/-- A symmetric Fourier partial sum at zero is twice the integral against the cosine kernel. -/
lemma sum_fourierCoeff_eq_integral_cosinePartialSumKernel {P : UnitAddCircle → ℂ}
    (hc : Continuous P) (N : ℕ) :
    (∑ n ∈ Finset.Icc (-(N : ℤ)) N, fourierCoeff P n) =
      (2 : ℂ) * ∫ x in (0 : ℝ)..1, P x * (cosinePartialSumKernel N (2 * π * x) : ℂ) := by
  simp_rw [fourierCoeff_eq_intervalIntegral _ _ 0, zero_add, div_one, one_smul, smul_eq_mul]
  have hi (n : ℤ) : IntervalIntegrable
      (fun x : ℝ => @fourier 1 (-n) (x : UnitAddCircle) * P x) volume 0 1 := by
    exact (((fourier (-n)).continuous.comp continuous_quotient_mk').mul
      (hc.comp continuous_quotient_mk')).intervalIntegrable 0 1
  rw [← intervalIntegral.integral_finsetSum (fun n _ => hi n),
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [← Finset.sum_mul]
  have hn : (∑ n ∈ Finset.Icc (-(N : ℤ)) N, @fourier 1 (-n) (x : UnitAddCircle)) =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) N, @fourier 1 n (x : UnitAddCircle) := by
    apply Finset.sum_bij (fun n _ => -n)
    · intro n hn
      simp only [Finset.mem_Icc] at hn ⊢
      omega
    · intro a _ b _ hab
      omega
    · intro n hn
      refine ⟨-n, ?_, by simp⟩
      simp only [Finset.mem_Icc] at hn ⊢
      omega
    · intro n _
      rfl
  rw [hn, sum_fourier_eq_cosinePartialSumKernel]
  ring
end Real
namespace Real
/-- The symmetric Fourier series of a continuous function of bounded variation converges
to its value at zero. -/
lemma tendsto_sum_Icc_fourierCoeff_of_boundedVariationOn {P : UnitAddCircle → ℂ}
    (hc : Continuous P) (hbv : BoundedVariationOn (fun x : ℝ => P x) (Icc 0 1)) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, fourierCoeff P n)
      atTop (𝓝 (P 0)) := by
  let g : ℝ → ℂ := fun t => P ((t / (2 * π) : ℝ) : UnitAddCircle)
  have hpipos : 0 < 2 * π := by positivity
  have hpine : 2 * π ≠ 0 := hpipos.ne'
  have hgbv : BoundedVariationOn g (Icc 0 (2 * π)) := by
    apply ne_top_of_le_ne_top hbv
    apply eVariationOn.comp_le_of_monotoneOn (fun x : ℝ => P x) (fun t : ℝ => t / (2 * π))
      (fun _ _ _ _ h => div_le_div_of_nonneg_right h hpipos.le)
    intro t ht
    exact ⟨div_nonneg ht.1 hpipos.le, (div_le_one hpipos).mpr ht.2⟩
  have hgc : ContinuousOn g (Icc 0 (2 * π)) :=
    ((hc.comp continuous_quotient_mk').comp (continuous_id.div_const _)).continuousOn
  have hconv := tendsto_integral_cosinePartialSumKernel_zero_of_boundedVariationOn hgbv hgc
  have hper : Function.Periodic (fun x : ℝ => P x) 1 :=
    fun x => congrArg P (AddCircle.coe_add_period 1 x)
  have hgend : (g 0 + g (2 * π)) / 2 = P 0 := by
    simp only [g, zero_div, div_self hpine]
    have hp : P ((1 : ℝ) : UnitAddCircle) = P ((0 : ℝ) : UnitAddCircle) := by simpa using hper 0
    rw [hp]
    simp
  rw [hgend] at hconv
  apply hconv.congr
  intro N
  rw [sum_fourierCoeff_eq_integral_cosinePartialSumKernel hc N]
  have hscale := intervalIntegral.integral_comp_div
    (a := 0) (b := 2 * π) (c := 2 * π)
    (fun x : ℝ => P x * (cosinePartialSumKernel N (2 * π * x) : ℂ)) hpine
  simp only [zero_div, div_self hpine, Complex.real_smul] at hscale
  have he : (∫ t in (0 : ℝ)..2 * π, g t * (cosinePartialSumKernel N t : ℂ)) =
      ((2 * π : ℝ) : ℂ) * ∫ x in (0 : ℝ)..1, P x *
        (cosinePartialSumKernel N (2 * π * x) : ℂ) := by
    rw [← hscale]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [g]
    rw [mul_div_cancel₀ t hpine]
  rw [he]
  push_cast
  field_simp
end Real
namespace Real
/-- For a continuous integrable function of bounded variation on the real line, the symmetric
partial sums of its Fourier transform at the integers converge to the sum of its integer samples. -/
lemma tendsto_sum_Icc_fourier_of_boundedVariationOn {g : ℝ → ℂ} (hc : Continuous g)
    (hi : Integrable g) (hbv : BoundedVariationOn g univ) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, 𝓕 g (n : ℝ))
      atTop (𝓝 (∑' n : ℤ, g (n : ℝ))) := by
  let f : C(ℝ, ℂ) := ⟨g, hc⟩
  have hn := hbv.summable_norm_restrict (f := f) hi
  have hs := ContinuousMap.summable_of_locally_summable_norm hn
  let P : UnitAddCircle → ℂ := (f.periodic_tsum_comp_add_zsmul 1).lift
  have hcoe (x : ℝ) : P x = ∑' n : ℤ, g (x + n) := by
    simp only [P, Function.Periodic.lift_coe, zsmul_one, ← ContinuousMap.tsum_apply hs,
      ContinuousMap.comp_apply, ContinuousMap.coe_addRight, f, ContinuousMap.coe_mk]
  have hPcont : Continuous P := by
    apply continuous_coinduced_dom.mpr
    have h := hbv.continuous_tsum_comp_add_int (f := f) hi
    simp only [f, ContinuousMap.coe_mk] at h
    convert h using 1
    funext x
    exact hcoe x
  have hPbv : BoundedVariationOn (fun x : ℝ => P x) (Icc 0 1) := by
    have h := hbv.boundedVariationOn_tsum_comp_add_int_unit (f := f) hi
    simpa only [hcoe, f, ContinuousMap.coe_mk] using h
  have h := tendsto_sum_Icc_fourierCoeff_of_boundedVariationOn hPcont hPbv
  have hcoeff (n : ℤ) : fourierCoeff P n = 𝓕 g (n : ℝ) := Real.fourierCoeff_tsum_comp_add hn n
  simp only [hcoeff] at h
  have hzero : P 0 = ∑' n : ℤ, g (n : ℝ) := by
    rw [← QuotientAddGroup.mk_zero]
    simpa only [zero_add] using hcoe 0
  rwa [hzero] at h
end Real
