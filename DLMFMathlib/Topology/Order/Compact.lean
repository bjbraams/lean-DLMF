/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Compact regions between continuous graphs

The region between two ordered continuous real-valued functions over a compact base is
compact, as the continuous image of the base times the unit interval. No separation or
metrizability assumption is needed on the base space.
-/

@[expose] public section

open Set

/-- The region between two continuous real-valued graphs over a compact base is compact.
The conclusion allows the two bounds to coincide. -/
theorem IsCompact.setOf_mem_Icc {E : Type*} [TopologicalSpace E] {K : Set E}
    (hK : IsCompact K) {lo hi : E → ℝ} (hlo : ContinuousOn lo K) (hhi : ContinuousOn hi K)
    (hle : ∀ x ∈ K, lo x ≤ hi x) :
    IsCompact {q : E × ℝ | q.1 ∈ K ∧ q.2 ∈ Icc (lo q.1) (hi q.1)} := by
  let F : E × ℝ → E × ℝ := fun q => (q.1, (1 - q.2) * lo q.1 + q.2 * hi q.1)
  have hc₁ : ContinuousOn (fun q : E × ℝ => lo q.1) (K ×ˢ Icc 0 1) :=
    hlo.comp continuous_fst.continuousOn (fun q hq => hq.1)
  have hc₂ : ContinuousOn (fun q : E × ℝ => hi q.1) (K ×ˢ Icc 0 1) :=
    hhi.comp continuous_fst.continuousOn (fun q hq => hq.1)
  have hc : ContinuousOn F (K ×ˢ Icc 0 1) :=
    continuousOn_fst.prodMk (((continuousOn_const.sub continuousOn_snd).mul hc₁).add
      (continuousOn_snd.mul hc₂))
  have him : F '' (K ×ˢ Icc 0 1) =
      {q : E × ℝ | q.1 ∈ K ∧ q.2 ∈ Icc (lo q.1) (hi q.1)} := by
    ext q
    constructor
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      refine ⟨hx, ?_, ?_⟩
      · change lo x ≤ (1 - t) * lo x + t * hi x
        nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr (hle x hx))]
      · change (1 - t) * lo x + t * hi x ≤ hi x
        nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr (hle x hx))]
    · rintro ⟨hx, hy⟩
      by_cases he : lo q.1 = hi q.1
      · refine ⟨(q.1, 0), ⟨hx, ⟨le_rfl, zero_le_one⟩⟩, ?_⟩
        have hq : q.2 = lo q.1 := by linarith [hy.1, hy.2]
        ext <;> simp [F, hq]
      · have hgap : 0 < hi q.1 - lo q.1 := sub_pos.mpr (lt_of_le_of_ne (hle q.1 hx) he)
        refine ⟨(q.1, (q.2 - lo q.1) / (hi q.1 - lo q.1)), ⟨hx, ?_⟩, ?_⟩
        · exact ⟨div_nonneg (sub_nonneg.mpr hy.1) hgap.le,
            (div_le_one hgap).mpr (by linarith [hy.2])⟩
        · ext
          · rfl
          · change (1 - (q.2 - lo q.1) / (hi q.1 - lo q.1)) * lo q.1 +
              (q.2 - lo q.1) / (hi q.1 - lo q.1) * hi q.1 = q.2
            field_simp
            ring
  rw [← him]
  exact (hK.prod isCompact_Icc).image_of_continuousOn hc
