/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import TauCeti.Topology.FilledHull
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.Analysis.Meromorphic.Order
public import TauCeti.Analysis.Contour.Residue.LogDeriv
import Mathlib.Tactic
import TauCeti.Analysis.Contour.Residue.Cycle
import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.UnboundedComponent
import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On.AbsolutelyContinuous
/-!
# Weighted argument principle on filled hulls

Analytic nonvanishing data on a set away from finitely many interior points extends to an
open neighborhood. For a closed piecewise smooth contour this allows TauCeti's
null-homologous residue theorem to count meromorphic orders with an arbitrary analytic weight.
The argument uses TauCeti's logarithmic-derivative principal part and residue-limit APIs,
without imposing a pointwise normalization at zeros or poles.

## Main results

* `Complex.exists_isOpen_superset_analyticAt_ne_zero_sdiff`: open-neighborhood extension.
* `Complex.residue_mul_logDeriv_eq_mul_order`: the weighted logarithmic-derivative residue.
* `Complex.integral_deriv_smul_mul_logDeriv_eq_sum`: the weighted argument principle.
-/

public noncomputable section
open Set Filter Complex MeasureTheory
open scoped Topology
namespace Complex
/-- Analytic nonvanishing data off an interior exceptional set extends to an open superset. -/
lemma exists_isOpen_superset_analyticAt_ne_zero_sdiff
    {f : ℂ → ℂ} {K S : Set ℂ}
    (hS : S ⊆ interior K) (hf : ∀ z ∈ K \ S, AnalyticAt ℂ f z ∧ f z ≠ 0) :
    ∃ U : Set ℂ, IsOpen U ∧ K ⊆ U ∧
      ∀ z ∈ U \ S, AnalyticAt ℂ f z ∧ f z ≠ 0 := by
  let V : Set ℂ := {z | AnalyticAt ℂ f z ∧ f z ≠ 0}
  have hV : IsOpen V := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    exact hz.1.eventually_analyticAt.and (hz.1.continuousAt.eventually_ne hz.2)
  refine ⟨interior K ∪ V, isOpen_interior.union hV, ?_, ?_⟩
  · intro z hz
    by_cases hs : z ∈ S
    · exact Or.inl (hS hs)
    · exact Or.inr (hf z ⟨hz, hs⟩)
  · rintro z ⟨hz | hz, hs⟩
    · exact hf z ⟨interior_subset hz, hs⟩
    · exact hz
/-- An analytic weight multiplies the logarithmic-derivative residue by its value. -/
lemma residue_mul_logDeriv_eq_mul_order
    {f g : ℂ → ℂ} {z : ℂ} (hf : MeromorphicAt f z)
    (hord : meromorphicOrderAt f z ≠ ⊤) (hg : AnalyticAt ℂ g z) :
    TauCeti.Contour.residue (fun w => g w * logDeriv f w) z =
      g z * ((meromorphicOrderAt f z).untop₀ : ℂ) := by
  have hn : meromorphicOrderAt f z =
      (((meromorphicOrderAt f z).untop₀ : ℤ) : WithTop ℤ) :=
    (WithTop.coe_untop₀_of_ne_top hord).symm
  obtain ⟨h, hh, hh0, heq⟩ := TauCeti.Contour.logDeriv_eventuallyEq_principalPart hf hn
  have hlog := TauCeti.Contour.analyticAt_logDeriv_of_analyticAt hh hh0
  have hlim : Tendsto (fun w : ℂ => (w - z) * logDeriv f w) (𝓝[≠] z)
      (𝓝 (((meromorphicOrderAt f z).untop₀ : ℤ) : ℂ)) := by
    have hsub : Tendsto (fun w : ℂ => w - z) (𝓝[≠] z) (𝓝 0) := by
      simpa only [sub_self] using
        ((continuous_sub_right z).tendsto z).mono_left
          nhdsWithin_le_nhds
    have hl : Tendsto (logDeriv h) (𝓝[≠] z) (𝓝 (logDeriv h z)) :=
      hlog.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have htail := hsub.mul hl
    simp only [zero_mul] at htail
    have hconst := htail.const_add (((meromorphicOrderAt f z).untop₀ : ℤ) : ℂ)
    simp only [add_zero] at hconst
    apply hconst.congr'
    filter_upwards [heq, self_mem_nhdsWithin] with w hw hwz
    rw [hw]
    have hwz0 : w - z ≠ 0 := sub_ne_zero.mpr hwz
    field_simp [hwz0]
  have hmero : MeromorphicAt (fun w => g w * logDeriv f w) z := by
    simpa only [Pi.mul_apply, Pi.div_apply, logDeriv_apply] using
      hg.meromorphicAt.fun_mul (hf.deriv.fun_div hf)
  apply TauCeti.Contour.residue_eq_of_tendsto_sub_mul hmero
  convert (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul hlim using 1
  funext w
  ring_nf
/-- The contour integral of an analytic weight times a logarithmic derivative is the
winding-weighted sum of meromorphic orders, for exceptional points inside the filled hull. -/
lemma integral_deriv_smul_mul_logDeriv_eq_sum
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : TauCeti.IsPiecewiseC1On γ a b) (hcl : γ a = γ b)
    {f g : ℂ → ℂ} {S : Finset ℂ}
    (hS : (S : Set ℂ) ⊆ interior (TauCeti.filledHull (γ '' uIcc a b)))
    (hoff : ∀ t ∈ uIcc a b, γ t ∉ (S : Set ℂ))
    (hf : ∀ z ∈ TauCeti.filledHull (γ '' uIcc a b) \ (S : Set ℂ),
      AnalyticAt ℂ f z ∧ f z ≠ 0)
    (hm : ∀ z ∈ S, MeromorphicAt f z ∧ meromorphicOrderAt f z ≠ ⊤)
    (hg : AnalyticOnNhd ℂ g (TauCeti.filledHull (γ '' uIcc a b))) :
    (2 * (Real.pi : ℂ) * I)⁻¹ * ∫ t in a..b, deriv γ t • (g (γ t) * logDeriv f (γ t)) =
      ∑ z ∈ S, TauCeti.Contour.windingNumber γ a b z * g z *
        ((meromorphicOrderAt f z).untop₀ : ℂ) := by
  obtain ⟨U, ho, hKU, hU⟩ := exists_isOpen_superset_analyticAt_ne_zero_sdiff hS hf
  let V : Set ℂ := {z | AnalyticAt ℂ g z}
  have hv : IsOpen V := isOpen_iff_mem_nhds.mpr fun _ hz => hz.eventually_analyticAt
  have hKUV : TauCeti.filledHull (γ '' uIcc a b) ⊆ U ∩ V :=
    fun z hz => ⟨hKU hz, hg z hz⟩
  have hγU : ∀ t ∈ uIcc a b, γ t ∈ U ∩ V := fun t ht =>
    hKUV (TauCeti.subset_filledHull ⟨t, ht, rfl⟩)
  have hnull : TauCeti.Contour.IsNullHomologous γ a b (U ∩ V) := by
    apply TauCeti.Contour.isNullHomologous_iff.mpr
    intro z hz
    exact hγ.absolutelyContinuousOnInterval.windingNumber_eq_zero_of_notMem_filledHull hcl
      (fun hzK => hz (hKUV hzK))
  have hd : DifferentiableOn ℂ (fun z => g z * logDeriv f z) ((U ∩ V) \ (S : Set ℂ)) := by
    rintro z ⟨hz, hs⟩
    exact (hz.2.mul
      (TauCeti.Contour.analyticAt_logDeriv_of_analyticAt (hU z ⟨hz.1, hs⟩).1
        (hU z ⟨hz.1, hs⟩).2)).differentiableAt.differentiableWithinAt
  have hmero : ∀ z ∈ S, z ∈ U ∩ V → MeromorphicAt (fun w => g w * logDeriv f w) z := by
    intro z hz hzU
    simpa only [Pi.mul_apply, Pi.div_apply, logDeriv_apply] using
      hzU.2.meromorphicAt.fun_mul ((hm z hz).1.deriv.fun_div (hm z hz).1)
  have h := TauCeti.Contour.classicalResidueTheorem_nullHomologous (ho.inter hv) hd hmero
    hγ hγU hcl hoff hnull
  rw [h, ← mul_assoc, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_mul]
  apply Finset.sum_congr rfl
  intro z hz
  rw [residue_mul_logDeriv_eq_mul_order (hm z hz).1 (hm z hz).2
    (hg z (interior_subset (hS hz)))]
  ring
end Complex
