/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import DLMFMathlib.Analysis.Integral.HilbertKernel
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# Principal values and conjugate-Poisson regularization

For an integrable function on the line that is continuous everywhere and differentiable
at zero, cancellation between its two half-lines makes the Hilbert principal value
absolutely integrable as an odd difference. Dominated convergence then identifies the
same limit for the conjugate-Poisson kernels. Values may be real or complex.

The proof uses Mathlib's continuous divided slopes and dominated convergence, together
with the symmetric cutoff identity in `DLMFMathlib.Analysis.Integral.HilbertKernel`.

* `MeasureTheory.integrableOn_Ioi_symmetric_div`: integrability after odd cancellation.
* `MeasureTheory.tendsto_integral_cut_div_eq_integral_symmetric_div`: the symmetric cutoff.
* `MeasureTheory.tendsto_integral_conjugatePoissonKernel`: conjugate-Poisson regularization.
-/

public noncomputable section

open Set Filter MeasureTheory RCLike
open scoped Topology

namespace MeasureTheory

variable {K : Type*} [RCLike K]
/-- The odd difference of an integrable function, continuous everywhere and differentiable at
zero, is integrable after division by the coordinate on the positive half-line. -/
lemma integrableOn_Ioi_symmetric_div {f : ℝ → K} (hc : Continuous f)
    (hd : DifferentiableAt ℝ f 0) (hi : Integrable f) :
    IntegrableOn (fun t : ℝ => (f t - f (-t)) / (t : K)) (Ioi 0) := by
  have hds : Continuous (dslope f 0) := by
    rw [← continuousOn_univ]
    exact (continuousOn_dslope (by simp)).mpr ⟨hc.continuousOn, hd⟩
  let q : ℝ → K := fun t => dslope f 0 t + dslope f 0 (-t)
  have hq : Continuous q := hds.add (hds.comp continuous_neg)
  have he {t : ℝ} (ht : t ≠ 0) : q t = (f t - f (-t)) / (t : K) := by
    dsimp [q]
    rw [dslope_of_ne _ ht, dslope_of_ne _ (neg_ne_zero.mpr ht)]
    simp only [slope_def_module, sub_zero, inv_neg, neg_smul]
    rw [RCLike.real_smul_eq_coe_mul, RCLike.real_smul_eq_coe_mul, ofReal_inv]
    field_simp
    ring
  have ht1 := integrableOn_Ioi_div_of_memLp (p := 1) le_rfl (by simp)
    (memLp_one_iff_integrable.mpr hi) (by norm_num : (0 : ℝ) < 1)
  have ht2 : IntegrableOn (fun t : ℝ => f (-t) / (t : K)) (Ioi 1) :=
    integrableOn_Ioi_div_of_memLp (p := 1) le_rfl (by simp)
      (memLp_one_iff_integrable.mpr hi.comp_neg) (by norm_num : (0 : ℝ) < 1)
  have ht : IntegrableOn q (Ioi 1) := by
    refine (ht1.sub ht2).congr_fun (fun t ht => ?_) measurableSet_Ioi
    -- Expose pointwise subtraction before using the quotient identity.
    change f t / (t : K) - f (-t) / (t : K) = q t
    rw [← sub_div, he (ne_of_gt (lt_trans zero_lt_one ht))]
  have hiq : IntegrableOn q (Ioi 0) :=
    ((hq.integrableOn_Icc (a := 0) (b := 1)).union ht).mono_set (by
      intro t ht
      by_cases h : t ≤ 1
      · exact Or.inl ⟨ht.le, h⟩
      · exact Or.inr (lt_of_not_ge h))
  exact hiq.congr_fun (fun t ht => he ht.ne') measurableSet_Ioi
/-- The symmetric principal value at zero equals the integral of the odd difference quotient. -/
lemma tendsto_integral_cut_div_eq_integral_symmetric_div {f : ℝ → K}
    (hc : Continuous f) (hd : DifferentiableAt ℝ f 0) (hi : Integrable f) :
    Tendsto (fun ε : ℝ => ∫ t in {t : ℝ | ε < |t|}, f t / (t : K)) (𝓝[>] 0)
      (𝓝 (∫ t in Ioi 0, (f t - f (-t)) / (t : K))) := by
  have hq := integrableOn_Ioi_symmetric_div hc hd hi
  have hlim : Tendsto (fun ε : ℝ => ∫ t in Ioi ε, (f t - f (-t)) / (t : K))
      (𝓝[>] 0) (𝓝 (∫ t in Ioi 0, (f t - f (-t)) / (t : K))) :=
    hq.continuousWithinAt_Ici_primitive_Ioi.mono Ioi_subset_Ici_self
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hp := integrableOn_Ioi_div_of_memLp (p := 1) le_rfl (by simp)
    (memLp_one_iff_integrable.mpr hi) hε
  have hm := integrableOn_Ioi_div_of_memLp (p := 1) le_rfl (by simp)
    (memLp_one_iff_integrable.mpr hi.comp_neg) hε
  have h := integral_abs_sub_cut_eq_integral_Ioi (x := 0) hε
    (by simpa only [zero_add] using hp) (by simpa only [zero_sub] using hm)
  convert h.symm using 2 <;> simp

/-- An integrable function remains integrable after multiplication by a conjugate-Poisson kernel. -/
lemma integrable_mul_conjugatePoissonKernel {f : ℝ → K} (hi : Integrable f)
    {a : ℝ} (ha : 0 < a) :
    Integrable (fun t : ℝ => ((t / (t ^ 2 + a ^ 2) : ℝ) : K) * f t) := by
  have hb (t : ℝ) : |t / (t ^ 2 + a ^ 2)| ≤ a⁻¹ := by
    have hden : 0 < t ^ 2 + a ^ 2 := by positivity
    rw [abs_div, abs_of_pos hden, div_le_iff₀ hden, inv_mul_eq_div, le_div_iff₀ ha]
    nlinarith [sq_nonneg (|t| - a), sq_abs t, sq_nonneg t]
  refine (hi.norm.const_mul a⁻¹).mono' ?_ (Eventually.of_forall fun t => ?_)
  · exact (by fun_prop : Measurable (fun t : ℝ =>
      ((t / (t ^ 2 + a ^ 2) : ℝ) : K))).aestronglyMeasurable.mul hi.aestronglyMeasurable
  · rw [norm_mul, RCLike.norm_ofReal]
    exact mul_le_mul_of_nonneg_right (hb t) (norm_nonneg _)

/-- Pairing the half-lines expresses the conjugate-Poisson integral through an odd difference. -/
lemma integral_conjugatePoissonKernel_eq_integral_Ioi {f : ℝ → K} (hi : Integrable f)
    {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ, ((t / (t ^ 2 + a ^ 2) : ℝ) : K) * f t) =
      ∫ t in Ioi (0 : ℝ), ((t ^ 2 / (t ^ 2 + a ^ 2) : ℝ) : K) *
        ((f t - f (-t)) / (t : K)) := by
  let F : ℝ → K := fun t => ((t / (t ^ 2 + a ^ 2) : ℝ) : K) * f t
  have hF : Integrable F := integrable_mul_conjugatePoissonKernel hi ha
  rw [← intervalIntegral.integral_Iic_add_Ioi hF.integrableOn hF.integrableOn,
    ← integral_comp_neg_Ioi 0 F]
  rw [neg_zero, ← integral_add hF.comp_neg.integrableOn hF.integrableOn]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only [F]
  have ht0 : (t : K) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hden : ((t : K) ^ 2 + (a : K) ^ 2) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < t ^ 2 + a ^ 2 by positivity))
  push_cast
  field_simp [ht0, hden]
  ring

/-- Conjugate-Poisson regularization converges to the integral of the odd difference quotient. -/
lemma tendsto_integral_conjugatePoissonKernel {f : ℝ → K}
    (hc : Continuous f) (hd : DifferentiableAt ℝ f 0) (hi : Integrable f) :
    Tendsto (fun a : ℝ => ∫ t : ℝ, ((t / (t ^ 2 + a ^ 2) : ℝ) : K) * f t)
      (𝓝[>] 0) (𝓝 (∫ t in Ioi (0 : ℝ), (f t - f (-t)) / (t : K))) := by
  let q : ℝ → K := fun t => (f t - f (-t)) / (t : K)
  have hq : IntegrableOn q (Ioi 0) := integrableOn_Ioi_symmetric_div hc hd hi
  have hlim : Tendsto (fun a : ℝ => ∫ t in Ioi (0 : ℝ),
      ((t ^ 2 / (t ^ 2 + a ^ 2) : ℝ) : K) * q t) (𝓝[>] 0)
      (𝓝 (∫ t in Ioi (0 : ℝ), q t)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun t => ‖q t‖)
    · exact Eventually.of_forall fun a => (by fun_prop : Measurable (fun t : ℝ =>
        ((t ^ 2 / (t ^ 2 + a ^ 2) : ℝ) : K))).aestronglyMeasurable.restrict.mul
          hq.aestronglyMeasurable
    · exact Eventually.of_forall fun a =>
        (ae_restrict_mem measurableSet_Ioi).mono fun t ht => by
          have ht0 : 0 < t := ht
          rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (by positivity)]
          have hb : t ^ 2 / (t ^ 2 + a ^ 2) ≤ 1 :=
            (div_le_one (by positivity)).mpr (by nlinarith [sq_nonneg a])
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hb (norm_nonneg (q t))
    · exact hq.norm
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hn : t ^ 2 ≠ 0 := pow_ne_zero 2 ht.ne'
      have ha0 : Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
      have hden : Tendsto (fun a : ℝ => t ^ 2 + a ^ 2) (𝓝[>] 0) (𝓝 (t ^ 2)) := by
        simpa using tendsto_const_nhds.add (ha0.pow 2)
      have hr : Tendsto (fun a : ℝ => t ^ 2 / (t ^ 2 + a ^ 2)) (𝓝[>] 0) (𝓝 1) := by
        have hv := (tendsto_const_nhds (x := t ^ 2)).div hden hn
        rw [div_self hn] at hv
        exact hv
      simpa only [Function.comp_def, ofReal_one, one_mul] using
        ((RCLike.continuous_ofReal.tendsto 1).comp hr).mul_const (q t)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
  exact (integral_conjugatePoissonKernel_eq_integral_Ioi hi ha).symm

end MeasureTheory
