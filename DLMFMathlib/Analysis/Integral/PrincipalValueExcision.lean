/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Principal values under asymmetric excision

Let `F` have a simple singularity at an interior point `c` of a measurable set `S`, in the sense
that `F t - A/(t - c)` (the singular part cut off outside an interval `[a, b] ⊆ S` around `c`)
is integrable on `S`. Excising an interval `[c - α, c + β]` with `α, β → 0⁺` and `α/β → 1`, the
integrals `∫_{S \ [c - α, c + β]} F` converge, and the limit does not depend on how `α` and `β`
approach `0`. In particular the Cauchy principal value (symmetric excision, `α = β = ε`) equals
every such asymmetric limit. This is what is needed to transport a principal value through a
change of variables `t = φ(u)`: the preimage of a symmetric interval about `c` is an interval
about `φ⁻¹(c)` that is symmetric only to first order.

## Main results

* `MeasureTheory.integral_Icc_diff_Icc_inv_sub`: the excised integral of `(t - c)⁻¹`.
* `MeasureTheory.tendsto_setIntegral_diff_Icc_of_integrableOn_sub`: the limit of the excised
  integrals for `α, β → 0⁺` with `α/β → 1`.
* `MeasureTheory.tendsto_setIntegral_diff_Icc_symm_of_integrableOn_sub`: the symmetric case.
* `MeasureTheory.setIntegral_comp_const_div`: the change of variables `u = K/t` on a measurable
  subset of `(0, ∞)`.
-/

@[expose] public section

noncomputable section

open Filter Set MeasureTheory

open scoped Topology

namespace MeasureTheory

/-- The integral of `(t - c)⁻¹` over `[a, b] \ [c - α, c + β]` is
`log ((b - c)/(c - a)) + log (α/β)`. -/
theorem integral_Icc_diff_Icc_inv_sub {a b c α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hαa : α < c - a) (hβb : β < b - c) :
    ∫ t in Icc a b \ Icc (c - α) (c + β), (t - c)⁻¹ =
      Real.log ((b - c) / (c - a)) + Real.log (α / β) := by
  have hset : Icc a b \ Icc (c - α) (c + β) = Ico a (c - α) ∪ Ioc (c + β) b := by
    ext t
    simp only [Set.mem_sdiff, mem_Icc, mem_union, mem_Ico, mem_Ioc, not_and_or, not_le]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3 | h3⟩
      · exact Or.inl ⟨h1, h3⟩
      · exact Or.inr ⟨h3, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨⟨h1, by linarith⟩, Or.inl h2⟩
      · exact ⟨⟨by linarith, h2⟩, Or.inr h1⟩
  have hdisj : Disjoint (Ico a (c - α)) (Ioc (c + β) b) := by
    rw [Set.disjoint_left]
    intro t h1 h2
    linarith [h1.2, h2.1]
  have hi1 : IntegrableOn (fun t : ℝ => (t - c)⁻¹) (Ico a (c - α)) := by
    refine (ContinuousOn.integrableOn_Icc (a := a) (b := c - α) ?_).mono_set Ico_subset_Icc_self
    exact ContinuousOn.inv₀ (by fun_prop) fun t ht => by linarith [ht.2]
  have hi2 : IntegrableOn (fun t : ℝ => (t - c)⁻¹) (Ioc (c + β) b) := by
    refine (ContinuousOn.integrableOn_Icc (a := c + β) (b := b) ?_).mono_set Ioc_subset_Icc_self
    exact ContinuousOn.inv₀ (by fun_prop) fun t ht => by linarith [ht.1]
  rw [hset, setIntegral_union hdisj measurableSet_Ioc hi1 hi2, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith),
    ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_comp_sub_right (fun t => t⁻¹),
    intervalIntegral.integral_comp_sub_right (fun t => t⁻¹),
    integral_inv_of_neg (by linarith) (by linarith),
    integral_inv_of_pos (by linarith) (by linarith),
    ← Real.log_mul (by apply div_ne_zero <;> linarith) (by apply div_ne_zero <;> linarith),
    ← Real.log_mul (by apply div_ne_zero <;> linarith) (by apply div_ne_zero <;> linarith)]
  congr 1
  have h1 : a - c ≠ 0 := by linarith
  have h2 : c - a ≠ 0 := by linarith
  have h3 : β ≠ 0 := hβ.ne'
  rw [show c - α - c = -α by ring, show c + β - c = β by ring, div_mul_div_comm,
    div_mul_div_comm, div_eq_div_iff (mul_ne_zero h1 h3) (mul_ne_zero h2 h3)]
  ring

/-- **Principal values under asymmetric excision.** Let `a < c < b`, `[a, b] ⊆ S` with `S`
measurable, and suppose that `G t = F t - 1_{[a,b]}(t) A/(t - c)` is integrable on `S`. If
`α, β → 0⁺` along a filter with `α/β → 1`, then
`∫_{S \ [c - α, c + β]} F → ∫_S G + A log ((b - c)/(c - a))`. -/
theorem tendsto_setIntegral_diff_Icc_of_integrableOn_sub {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated]
    {F : ℝ → ℂ} {S : Set ℝ} {a b c : ℝ} (A : ℂ) (hac : a < c) (hcb : c < b)
    (hS : MeasurableSet S) (habS : Icc a b ⊆ S)
    (hG : IntegrableOn (fun t => F t - (Icc a b).indicator (fun t => A / ((t : ℂ) - c)) t) S)
    {α β : ι → ℝ} (hα : Tendsto α l (𝓝[>] 0)) (hβ : Tendsto β l (𝓝[>] 0))
    (hαβ : Tendsto (fun i => α i / β i) l (𝓝 1)) :
    Tendsto (fun i => ∫ t in S \ Icc (c - α i) (c + β i), F t) l
      (𝓝 ((∫ t in S, (F t - (Icc a b).indicator (fun t => A / ((t : ℂ) - c)) t)) +
        A * Real.log ((b - c) / (c - a)))) := by
  set G : ℝ → ℂ := fun t => F t - (Icc a b).indicator (fun t => A / ((t : ℂ) - c)) t with hGdef
  set H : ℝ → ℂ := (Icc a b).indicator (fun t => A / ((t : ℂ) - c)) with hHdef
  have hα0 : ∀ᶠ i in l, 0 < α i := hα.eventually self_mem_nhdsWithin
  have hβ0 : ∀ᶠ i in l, 0 < β i := hβ.eventually self_mem_nhdsWithin
  have hαs : ∀ᶠ i in l, α i < c - a :=
    (tendsto_nhds_of_tendsto_nhdsWithin hα).eventually (gt_mem_nhds (by linarith))
  have hβs : ∀ᶠ i in l, β i < b - c :=
    (tendsto_nhds_of_tendsto_nhdsWithin hβ).eventually (gt_mem_nhds (by linarith))
  -- the singular part
  have hsing : ∀ᶠ i in l, ∫ t in S \ Icc (c - α i) (c + β i), H t =
      A * ((Real.log ((b - c) / (c - a)) + Real.log (α i / β i) : ℝ) : ℂ) := by
    filter_upwards [hα0, hβ0, hαs, hβs] with i h1 h2 h3 h4
    rw [hHdef, setIntegral_indicator measurableSet_Icc,
      show (S \ Icc (c - α i) (c + β i)) ∩ Icc a b = Icc a b \ Icc (c - α i) (c + β i) by
        ext t; constructor
        · rintro ⟨⟨_, h⟩, h'⟩; exact ⟨h', h⟩
        · rintro ⟨h', h⟩; exact ⟨⟨habS h', h⟩, h'⟩,
      ← integral_Icc_diff_Icc_inv_sub h1 h2 h3 h4, ← integral_complex_ofReal,
      ← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_Icc.diff measurableSet_Icc) fun t _ => ?_
    push_cast
    ring
  have hHi : ∀ᶠ i in l, IntegrableOn H (S \ Icc (c - α i) (c + β i)) := by
    filter_upwards [hα0, hβ0] with i h1 h2
    rw [hHdef, integrableOn_indicator_iff measurableSet_Icc.nullMeasurableSet]
    have hsub : Icc a b ∩ (S \ Icc (c - α i) (c + β i)) ⊆ Icc a (c - α i) ∪ Icc (c + β i) b := by
      rintro t ⟨⟨h3, h4⟩, -, h5⟩
      simp only [mem_Icc, not_and_or, not_le] at h5
      rcases h5 with h5 | h5
      · exact Or.inl ⟨h3, h5.le⟩
      · exact Or.inr ⟨h5.le, h4⟩
    refine IntegrableOn.mono_set (IntegrableOn.union ?_ ?_) hsub
    · refine ContinuousOn.integrableOn_Icc (continuousOn_const.div (by fun_prop) ?_)
      intro t ht h
      have : t = c := by exact_mod_cast sub_eq_zero.mp h
      linarith [ht.2]
    · refine ContinuousOn.integrableOn_Icc (continuousOn_const.div (by fun_prop) ?_)
      intro t ht h
      have : t = c := by exact_mod_cast sub_eq_zero.mp h
      linarith [ht.1]
  have hsplit : ∀ᶠ i in l, ∫ t in S \ Icc (c - α i) (c + β i), F t =
      (∫ t in S \ Icc (c - α i) (c + β i), G t) +
        A * ((Real.log ((b - c) / (c - a)) + Real.log (α i / β i) : ℝ) : ℂ) := by
    filter_upwards [hsing, hHi] with i h1 h2
    rw [← h1, ← integral_add (hG.mono_set sdiff_subset) h2]
    refine setIntegral_congr_fun (hS.diff measurableSet_Icc) fun t _ => ?_
    simp only [hGdef, hHdef]
    ring
  refine Tendsto.congr' (EventuallyEq.symm hsplit) (Tendsto.add ?_ ?_)
  · -- dominated convergence for the regular part
    have he : ∀ i, ∫ t in S \ Icc (c - α i) (c + β i), G t =
        ∫ t in S, (Icc (c - α i) (c + β i))ᶜ.indicator G t := by
      intro i
      rw [setIntegral_indicator measurableSet_Icc.compl, sdiff_eq]
    simp only [he]
    refine tendsto_integral_filter_of_dominated_convergence (fun t => ‖G t‖) ?_ ?_ hG.norm ?_
    · exact Eventually.of_forall fun i =>
        (hG.aestronglyMeasurable.indicator measurableSet_Icc.compl)
    · refine Eventually.of_forall fun i => Eventually.of_forall fun t => ?_
      by_cases ht : t ∈ (Icc (c - α i) (c + β i))ᶜ
      · simp [indicator_of_mem ht]
      · simp [indicator_of_notMem ht]
    · have hae : ∀ᵐ t ∂(volume.restrict S), t ≠ c :=
        ae_restrict_of_ae (by
          rw [ae_iff]; simp only [ne_eq, not_not, ofPred_eq_eq_singleton]
          exact measure_singleton c)
      filter_upwards [hae] with t htc
      have hpos : 0 < |t - c| := abs_pos.mpr (sub_ne_zero.mpr htc)
      refine tendsto_const_nhds.congr' ?_
      have h1 : ∀ᶠ i in l, α i < |t - c| :=
        (tendsto_nhds_of_tendsto_nhdsWithin hα).eventually (gt_mem_nhds hpos)
      have h2 : ∀ᶠ i in l, β i < |t - c| :=
        (tendsto_nhds_of_tendsto_nhdsWithin hβ).eventually (gt_mem_nhds hpos)
      filter_upwards [h1, h2] with i h1 h2
      have hmem : t ∈ (Icc (c - α i) (c + β i))ᶜ := by
        rintro ⟨h3, h4⟩
        rcases le_or_gt c t with h | h
        · rw [abs_of_nonneg (by linarith)] at h2; linarith
        · rw [abs_of_neg (by linarith)] at h1; linarith
      rw [indicator_of_mem hmem]
  · -- the logarithmic correction tends to zero
    have hlog : Tendsto (fun i => Real.log (α i / β i)) l (𝓝 0) := by
      have := (Real.continuousAt_log one_ne_zero).tendsto.comp hαβ
      simpa [Function.comp_def] using this
    have := ((Complex.continuous_ofReal.tendsto _).comp
      (tendsto_const_nhds (x := Real.log ((b - c) / (c - a))) |>.add hlog)).const_mul A
    simpa [Function.comp_def] using this

/-- The symmetric case (`α = β = ε`) of
`tendsto_setIntegral_diff_Icc_of_integrableOn_sub`: the Cauchy principal value. -/
theorem tendsto_setIntegral_diff_Icc_symm_of_integrableOn_sub {F : ℝ → ℂ} {S : Set ℝ}
    {a b c : ℝ} (A : ℂ) (hac : a < c) (hcb : c < b) (hS : MeasurableSet S) (habS : Icc a b ⊆ S)
    (hG : IntegrableOn (fun t => F t - (Icc a b).indicator (fun t => A / ((t : ℂ) - c)) t) S) :
    Tendsto (fun ε : ℝ => ∫ t in S \ Icc (c - ε) (c + ε), F t) (𝓝[>] 0)
      (𝓝 ((∫ t in S, (F t - (Icc a b).indicator (fun t => A / ((t : ℂ) - c)) t)) +
        A * Real.log ((b - c) / (c - a)))) := by
  refine tendsto_setIntegral_diff_Icc_of_integrableOn_sub A hac hcb hS habS hG tendsto_id
    tendsto_id (tendsto_const_nhds.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (div_self (ne_of_gt hε)).symm

/-- The inversion `t ↦ K/t` (`K > 0`) as a change of variables on a measurable subset `U` of
`(0, ∞)`: `∫_U g = ∫_{t : K/t ∈ U} (K/t²) g(K/t) dt`. -/
theorem setIntegral_comp_const_div {K : ℝ} (hK : 0 < K) {U : Set ℝ} (hU : MeasurableSet U)
    (hU0 : U ⊆ Ioi 0) (g : ℝ → ℂ) :
    ∫ u in U, g u = ∫ t in (fun t : ℝ => K / t) ⁻¹' U, (K / t ^ 2) • g (K / t) := by
  set φ : ℝ → ℝ := fun t => K / t with hφ
  have hinv : Function.Involutive φ := fun t => by
    simp only [hφ]
    rcases eq_or_ne t 0 with rfl | ht
    · simp
    · field_simp
  have hs : MeasurableSet (φ ⁻¹' U) := (measurable_const.div measurable_id) hU
  have hpos : ∀ t ∈ φ ⁻¹' U, 0 < t := fun t ht => by
    have h := hU0 ht
    simp only [hφ, mem_Ioi] at h
    by_contra h'
    push Not at h'
    rcases h'.eq_or_lt with h0 | h0
    · rw [h0, div_zero] at h; exact lt_irrefl _ h
    · exact absurd h (not_lt.mpr (div_nonpos_of_nonneg_of_nonpos hK.le h0.le))
  have himg : φ '' (φ ⁻¹' U) = U := by
    rw [hinv.image_eq_preimage_symm, ← preimage_comp, hinv.comp_self, preimage_id]
  have h := integral_image_eq_integral_abs_deriv_smul hs
    (f' := fun t => -(K / t ^ 2))
    (fun t ht => by
      have ht0 := (hpos t ht).ne'
      have := ((hasDerivAt_inv ht0).const_mul K).hasDerivWithinAt (s := φ ⁻¹' U)
      convert this using 1
      · funext u; simp only [hφ, div_eq_mul_inv]
      · ring)
    hinv.injective.injOn g
  rw [himg] at h
  rw [h]
  refine setIntegral_congr_fun hs fun t ht => ?_
  simp only [hφ, abs_neg, abs_of_pos (by have := hpos t ht; positivity : 0 < K / t ^ 2)]

end MeasureTheory
