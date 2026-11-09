/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Mellin.Transforms
public import DLMFMathlib.Analysis.Complex.VerticalResidues
public import DLMFMathlib.Analysis.Complex.MeromorphicUniqueness

/-!
# Meromorphic finite Mellin continuations and their residues

The holomorphic regular-part formulas give meromorphic finite continuations. When the
exponents are distinct, their simple principal parts have the coefficients prescribed
by DLMF 2.5.25 and 2.5.27, with residues computed by Tau Ceti.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Finset Asymptotics Complex
open scoped Topology

namespace DLMF.AsymptoticApproximations

/-- The finite zero-endpoint continuation is meromorphic on its enlarged strip. -/
theorem meromorphicOn_mellinContinuationAtZero {f : ℝ → ℂ} {a α : ℕ → ℂ} {b : ℝ}
    (hfc : LocallyIntegrableOn f (Ioi 0))
    (hf : HasAsymptoticExpansion (𝓝[>] 0) (fun k (t : ℝ) => (t : ℂ) ^ α k) a f)
    (hb : f =O[atTop] fun t => t ^ (-b)) (N : ℕ) :
    MeromorphicOn (mellinContinuationAtZero f a α N)
      {z : ℂ | -(α N).re < z.re ∧ z.re < b} := by
  let R : ℂ → ℂ := fun z => mellinContinuationAtZero f a α N z -
    ∑ k ∈ range N, a k / (z + α k)
  have hU : IsOpen {z : ℂ | -(α N).re < z.re ∧ z.re < b} :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  have ha : AnalyticOnNhd ℂ R {z : ℂ | -(α N).re < z.re ∧ z.re < b} :=
    (show DifferentiableOn ℂ R {z : ℂ | -(α N).re < z.re ∧ z.re < b} from fun z hz =>
      (mellinContinuationAtZero_sub_principalParts_differentiableAt hfc hf hb N
        hz.1 hz.2).differentiableWithinAt).analyticOnNhd hU
  intro z hz
  have hs : MeromorphicAt (fun w : ℂ => ∑ k ∈ range N, a k / (w + α k)) z :=
    MeromorphicAt.fun_sum fun k _ =>
      analyticAt_const.meromorphicAt.div ((analyticAt_id.add analyticAt_const).meromorphicAt)
  convert (ha z hz).meromorphicAt.add hs using 1
  funext w
  simp [R]

/-- The finite infinity-endpoint continuation is meromorphic on its enlarged strip. -/
theorem meromorphicOn_mellinContinuationAtTop {f : ℝ → ℂ} {b β : ℕ → ℂ} {c : ℝ}
    (hfc : LocallyIntegrableOn f (Ioi 0))
    (hf : HasAsymptoticExpansion atTop (fun k (t : ℝ) => (t : ℂ) ^ (-β k)) b f)
    (hc : f =O[𝓝[>] 0] fun t => t ^ c) (N : ℕ) :
    MeromorphicOn (mellinContinuationAtTop f b β N)
      {z : ℂ | -c < z.re ∧ z.re < (β N).re} := by
  let R : ℂ → ℂ := fun z => mellinContinuationAtTop f b β N z +
    ∑ k ∈ range N, b k / (z - β k)
  have hU : IsOpen {z : ℂ | -c < z.re ∧ z.re < (β N).re} :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  have ha : AnalyticOnNhd ℂ R {z : ℂ | -c < z.re ∧ z.re < (β N).re} :=
    (show DifferentiableOn ℂ R {z : ℂ | -c < z.re ∧ z.re < (β N).re} from fun z hz =>
      (mellinContinuationAtTop_add_principalParts_differentiableAt hfc hf hc N
        hz.1 hz.2).differentiableWithinAt).analyticOnNhd hU
  intro z hz
  have hs : MeromorphicAt (fun w : ℂ => ∑ k ∈ range N, b k / (w - β k)) z :=
    MeromorphicAt.fun_sum fun k _ =>
      analyticAt_const.meromorphicAt.div ((analyticAt_id.sub analyticAt_const).meromorphicAt)
  convert (ha z hz).meromorphicAt.sub hs using 1
  funext w
  simp [R]

/-- Distinct exponents give residue `a_k` at `-α_k` in the zero-endpoint continuation. -/
theorem residue_mellinContinuationAtZero {f : ℝ → ℂ} {a α : ℕ → ℂ} {b : ℝ}
    (hfc : LocallyIntegrableOn f (Ioi 0)) (hα : StrictMono fun k => (α k).re)
    (hf : HasAsymptoticExpansion (𝓝[>] 0) (fun k (t : ℝ) => (t : ℂ) ^ α k) a f)
    (hb : f =O[atTop] fun t => t ^ (-b)) (N k : ℕ) (hk : k < N)
    (hkb : -(α k).re < b) :
    TauCeti.Contour.residue (mellinContinuationAtZero f a α N) (-α k) = a k := by
  have hp : Function.Injective (fun k => -α k) := fun i j hij =>
    hα.injective (congrArg re (neg_injective hij))
  have hreg : AnalyticAt ℂ (fun z => mellinContinuationAtZero f a α N z -
      ∑ s ∈ range N, a s / (z + α s)) (-α k) := by
    have hU : IsOpen {z : ℂ | -(α N).re < z.re ∧ z.re < b} :=
      (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
    exact (show DifferentiableOn ℂ _ {z : ℂ | -(α N).re < z.re ∧ z.re < b} from
      fun z hz => (mellinContinuationAtZero_sub_principalParts_differentiableAt hfc hf hb N
        hz.1 hz.2).differentiableWithinAt).analyticOnNhd hU _
          (by simpa only [mem_setOf_eq, neg_re] using And.intro (neg_lt_neg (hα hk)) hkb)
  apply Complex.residue_eq_of_analyticAt_sub_sum_div (range N) (fun k => -α k) a hp
    (mem_range.mpr hk)
  simpa only [sub_neg_eq_add] using hreg

/-- Distinct exponents give residue `-b_k` at `β_k` in the infinity-endpoint continuation. -/
theorem residue_mellinContinuationAtTop {f : ℝ → ℂ} {b β : ℕ → ℂ} {c : ℝ}
    (hfc : LocallyIntegrableOn f (Ioi 0)) (hβ : StrictMono fun k => (β k).re)
    (hf : HasAsymptoticExpansion atTop (fun k (t : ℝ) => (t : ℂ) ^ (-β k)) b f)
    (hc : f =O[𝓝[>] 0] fun t => t ^ c) (N k : ℕ) (hk : k < N)
    (hkc : -c < (β k).re) :
    TauCeti.Contour.residue (mellinContinuationAtTop f b β N) (β k) = -b k := by
  have hp : Function.Injective β := fun i j hij => hβ.injective (congrArg re hij)
  have hreg : AnalyticAt ℂ (fun z => mellinContinuationAtTop f b β N z +
      ∑ s ∈ range N, b s / (z - β s)) (β k) := by
    have hU : IsOpen {z : ℂ | -c < z.re ∧ z.re < (β N).re} :=
      (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
    exact (show DifferentiableOn ℂ _ {z : ℂ | -c < z.re ∧ z.re < (β N).re} from
      fun z hz => (mellinContinuationAtTop_add_principalParts_differentiableAt hfc hf hc N
        hz.1 hz.2).differentiableWithinAt).analyticOnNhd hU _ ⟨hkc, hβ hk⟩
  apply Complex.residue_eq_of_analyticAt_sub_sum_div (range N) β (fun k => -b k) hp
    (mem_range.mpr hk)
  simpa only [neg_div, Finset.sum_neg_distrib, sub_neg_eq_add] using hreg

/-- Unbounded zero-endpoint exponents glue the finite subtractions to a meromorphic
continuation on the whole half-plane of convergence of the unchanged high tail. -/
theorem exists_meromorphic_mellinContinuationAtZero {f : ℝ → ℂ} {a α : ℕ → ℂ} {b : ℝ}
    (hfc : LocallyIntegrableOn f (Ioi 0)) (hα : StrictMono fun k => (α k).re)
    (hαinf : Tendsto (fun k => (α k).re) atTop atTop)
    (hf : HasAsymptoticExpansion (𝓝[>] 0) (fun k (t : ℝ) => (t : ℂ) ^ α k) a f)
    (hb : f =O[atTop] fun t => t ^ (-b)) :
    ∃ G : ℂ → ℂ, MeromorphicOn G {z | z.re < b} ∧
      ∀ N z, -(α N).re < z.re → z.re < b → G z = mellinContinuationAtZero f a α N z := by
  classical
  have hex (z : ℂ) : ∃ N, -(α N).re < z.re := by
    obtain ⟨N, hN⟩ := (hαinf.eventually_gt_atTop (-z.re)).exists
    exact ⟨N, by linarith⟩
  let G : ℂ → ℂ := fun z => mellinContinuationAtZero f a α (Nat.find (hex z)) z
  have he (N : ℕ) {z : ℂ} (hz : -(α N).re < z.re) :
      G z = mellinContinuationAtZero f a α N z :=
    mellinContinuationAtZero_eq hfc hα hf (Nat.find_spec (hex z)) hz
  refine ⟨G, ?_, fun N z hz _ => he N hz⟩
  intro z hz
  let N := Nat.find (hex z)
  have hN : -(α N).re < z.re := Nat.find_spec (hex z)
  have hg := meromorphicOn_mellinContinuationAtZero hfc hf hb N z ⟨hN, hz⟩
  apply hg.congr
  have hnb : ∀ᶠ w : ℂ in 𝓝[≠] z, -(α N).re < w.re :=
    nhdsWithin_le_nhds ((isOpen_lt continuous_const continuous_re).mem_nhds hN)
  filter_upwards [hnb] with w hw
  exact (he N hw).symm

/-- Unbounded infinity-endpoint exponents glue the finite subtractions to a meromorphic
continuation on the whole half-plane of convergence of the unchanged low tail. -/
theorem exists_meromorphic_mellinContinuationAtTop {f : ℝ → ℂ} {b β : ℕ → ℂ} {c : ℝ}
    (hfc : LocallyIntegrableOn f (Ioi 0)) (hβ : StrictMono fun k => (β k).re)
    (hβinf : Tendsto (fun k => (β k).re) atTop atTop)
    (hf : HasAsymptoticExpansion atTop (fun k (t : ℝ) => (t : ℂ) ^ (-β k)) b f)
    (hc : f =O[𝓝[>] 0] fun t => t ^ c) :
    ∃ G : ℂ → ℂ, MeromorphicOn G {z | -c < z.re} ∧
      ∀ N z, -c < z.re → z.re < (β N).re → G z = mellinContinuationAtTop f b β N z := by
  classical
  have hex (z : ℂ) : ∃ N, z.re < (β N).re :=
    (hβinf.eventually_gt_atTop z.re).exists
  let G : ℂ → ℂ := fun z => mellinContinuationAtTop f b β (Nat.find (hex z)) z
  have he (N : ℕ) {z : ℂ} (hz : z.re < (β N).re) :
      G z = mellinContinuationAtTop f b β N z :=
    mellinContinuationAtTop_eq hfc hβ hf (Nat.find_spec (hex z)) hz
  refine ⟨G, ?_, fun N z _ hz => he N hz⟩
  intro z hz
  let N := Nat.find (hex z)
  have hN : z.re < (β N).re := Nat.find_spec (hex z)
  have hg := meromorphicOn_mellinContinuationAtTop hfc hf hc N z ⟨hz, hN⟩
  apply hg.congr
  have hnb : ∀ᶠ w : ℂ in 𝓝[≠] z, w.re < (β N).re :=
    nhdsWithin_le_nhds ((isOpen_lt continuous_re continuous_const).mem_nhds hN)
  filter_upwards [hnb] with w hw
  exact (he N hw).symm

end DLMF.AsymptoticApproximations
