/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Topology.Connected.TotallyDisconnected
public import TauCeti.Analysis.Complex.Conformal.Rouche
public import TauCeti.Analysis.Normed.Module.FilledHull

/-!
# Rouché's theorem for the filled hull of a compact set

Let `C ⊆ ℂ` be compact and let `K = TauCeti.filledHull C` be `C` together with the bounded
components of its complement, so that `K \ C` is the "inside" of `C`. If `f` and `g` are
analytic on (a neighbourhood of) `K` and `‖g‖ < ‖f‖` on `C`, then `f` and `f + g` have the same
number of zeros in `K \ C`, counted with multiplicity.

No Jordan curve theorem or winding-number computation is needed: the zero count
`N(h) = ∑ᶠ z ∈ K \ C, ord_z h` is locally constant under uniformly small perturbations of `h`
on `K` (Rouché's theorem on small discs around the zeros, `TauCeti.rouche`), and the
deformation `f + t g`, `0 ≤ t ≤ 1`, never vanishes on `C`.

## Main results

* `Complex.finite_zeros_filledHull`: an analytic function on `K` without zeros on `C` has
  finitely many zeros in `K`.
* `Complex.exists_finsum_analyticOrderNatAt_filledHull_eq`: local constancy of the zero count.
* `Complex.rouche_filledHull`: Rouché's theorem for `K \ C`.
-/

@[expose] public section

open Set Filter Metric TauCeti
open scoped Topology

namespace Complex

variable {C : Set ℂ}

/-- The filled hull of a compact subset of `ℂ` is compact. -/
private lemma isCompact_filledHull_of_isCompact (hC : IsCompact C) :
    IsCompact (filledHull C) :=
  Metric.isCompact_of_isClosed_isBounded hC.isClosed.isClosed_filledHull
    (isBounded_filledHull.mpr hC.isBounded)

/-- The analytic order of `h` at a point where `h` does not vanish is `0`. -/
private lemma analyticOrderNatAt_eq_zero_of_ne {h : ℂ → ℂ} {z : ℂ} (hz : h z ≠ 0) :
    analyticOrderNatAt h z = 0 := by
  simp [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hz)]

/-- An analytic function on the filled hull `K` of a compact set `C` that does not vanish on `C`
does not vanish identically near any point of `K`. -/
private lemma not_eventuallyEq_zero_filledHull (hC : IsCompact C) {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (filledHull C)) (hne : ∀ z ∈ C, h z ≠ 0) {z : ℂ}
    (hz : z ∈ filledHull C) : ¬ h =ᶠ[𝓝 z] 0 := by
  intro hev
  have hK := isCompact_filledHull_of_isCompact hC
  have hI : IsOpen (filledHull C \ C) := hC.isClosed.isOpen_filledHull_sdiff
  have hzC : z ∉ C := fun h' => hne z h' hev.eq_of_nhds
  set V := connectedComponentIn (filledHull C \ C) z
  have hVo : IsOpen V := hI.connectedComponentIn
  have hVI : V ⊆ filledHull C \ C := connectedComponentIn_subset _ _
  have hzV : z ∈ V := mem_connectedComponentIn ⟨hz, hzC⟩
  have h0V : EqOn h 0 V :=
    (hh.mono (hVI.trans sdiff_subset)).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_connectedComponentIn hzV hev
  have hVne : V ≠ univ := fun hV =>
    NormedSpace.unbounded_univ ℝ ℂ (hV ▸ hK.isBounded.subset (hVI.trans sdiff_subset))
  obtain ⟨w, hw⟩ := nonempty_frontier_iff.mpr ⟨⟨z, hzV⟩, hVne⟩
  have hwcl : w ∈ closure V := hw.1
  have hwK : w ∈ filledHull C :=
    closure_minimal (hVI.trans sdiff_subset) hK.isClosed hwcl
  have hwC : w ∈ C := by
    by_contra hwC
    have hwI : w ∈ filledHull C \ C := ⟨hwK, hwC⟩
    obtain ⟨u, hu1, hu2⟩ := mem_closure_iff.mp hwcl _ hI.connectedComponentIn
      (mem_connectedComponentIn hwI)
    have hwV : w ∈ V := by
      have hV : V = connectedComponentIn (filledHull C \ C) w :=
        (connectedComponentIn_eq hu2).trans (connectedComponentIn_eq hu1).symm
      rw [hV]
      exact mem_connectedComponentIn hwI
    rw [hVo.frontier_eq] at hw
    exact hw.2 hwV
  have hcont : ContinuousOn h (insert w V) := fun y hy =>
    (hh y (by rcases hy with rfl | hy; exacts [hwK, (hVI hy).1])).continuousAt.continuousWithinAt
  have hEq := h0V.of_subset_closure hcont continuousOn_const (subset_insert w V)
    (insert_subset hwcl subset_closure)
  exact hne w hwC (hEq (mem_insert w V))

/-- An analytic function on the filled hull `K` of a compact set `C ⊆ ℂ` without zeros on `C`
has only finitely many zeros in `K`. -/
theorem finite_zeros_filledHull (hC : IsCompact C) {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (filledHull C)) (hne : ∀ z ∈ C, h z ≠ 0) :
    {z ∈ filledHull C | h z = 0}.Finite := by
  have hK := isCompact_filledHull_of_isCompact hC
  have hZc : IsClosed (filledHull C ∩ h ⁻¹' {0}) :=
    hh.continuousOn.preimage_isClosed_of_isClosed hK.isClosed isClosed_singleton
  refine (hK.of_isClosed_subset hZc inter_subset_left).finite ?_
  refine isDiscrete_iff_nhdsNE.mpr fun x hx => ?_
  have hev := ((hh x hx.1).eventually_eq_zero_or_eventually_ne_zero).resolve_left
    (not_eventuallyEq_zero_filledHull hC hh hne hx.1)
  rw [inf_principal_eq_bot]
  filter_upwards [hev] with y hy using fun hy' => hy hy'.2

/-- **Local constancy of the zero count.** Let `h` be analytic on the filled hull `K` of a
compact set `C ⊆ ℂ`, without zeros on `C`. Every `k` analytic on `K` and uniformly close enough
to `h` on `K` has as many zeros in `K \ C` as `h`, counted with multiplicity. -/
theorem exists_finsum_analyticOrderNatAt_filledHull_eq (hC : IsCompact C) {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (filledHull C)) (hne : ∀ z ∈ C, h z ≠ 0) :
    ∃ δ > 0, ∀ k : ℂ → ℂ, AnalyticOnNhd ℂ k (filledHull C) →
      (∀ z ∈ filledHull C, ‖k z - h z‖ < δ) →
      (∑ᶠ z ∈ filledHull C \ C, analyticOrderNatAt k z) =
        ∑ᶠ z ∈ filledHull C \ C, analyticOrderNatAt h z := by
  classical
  set K := filledHull C
  have hK := isCompact_filledHull_of_isCompact hC
  have hI : IsOpen (K \ C) := hC.isClosed.isOpen_filledHull_sdiff
  have hCK : C ⊆ K := subset_filledHull
  set Z := (finite_zeros_filledHull hC hh hne).toFinset
  have hZ : ∀ z, z ∈ Z ↔ z ∈ K ∧ h z = 0 := fun z => by
    rw [Set.Finite.mem_toFinset]; rfl
  have hZI : ∀ z ∈ Z, z ∈ K \ C := fun z hz =>
    ⟨((hZ z).mp hz).1, fun hzC => hne z hzC ((hZ z).mp hz).2⟩
  -- choice of a common radius `r`
  have hloc : ∀ z ∈ Z, ∀ᶠ r in 𝓝[>] (0 : ℝ), closedBall z r ⊆ K \ C ∧
      (∀ y ∈ closedBall z r, y ≠ z → h y ≠ 0) ∧ ∀ z' ∈ Z, z' ≠ z → 2 * r < dist z z' := by
    intro z hz
    refine (Filter.Eventually.and (nhdsWithin_le_nhds
      (eventually_closedBall_subset (hI.mem_nhds (hZI z hz)))) (Filter.Eventually.and ?_ ?_))
    · have hev := ((hh z ((hZ z).mp hz).1).eventually_eq_zero_or_eventually_ne_zero).resolve_left
        (not_eventuallyEq_zero_filledHull hC hh hne ((hZ z).mp hz).1)
      obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhdsWithin_iff.mp hev
      filter_upwards [Ioo_mem_nhdsGT hε] with r hr y hy hyz
      exact hεs ⟨closedBall_subset_ball hr.2 hy, hyz⟩
    · rw [Filter.eventually_all_finset]
      intro z' _
      by_cases hzz : z' = z
      · exact Eventually.of_forall fun r h' => absurd hzz h'
      · have hd : 0 < dist z z' := dist_pos.mpr (Ne.symm hzz)
        have ht : Tendsto (fun r : ℝ => 2 * r) (𝓝[>] 0) (𝓝 0) := by
          simpa using ((continuous_const_mul (2 : ℝ)).tendsto 0).mono_left nhdsWithin_le_nhds
        filter_upwards [ht.eventually (gt_mem_nhds hd)] with r hr _ using hr
  obtain ⟨r, hr, hr0⟩ :=
    (((Filter.eventually_all_finset Z).mpr hloc).and self_mem_nhdsWithin).exists
  have hr0' : (0 : ℝ) < r := hr0
  set B := ⋃ z ∈ Z, ball z r
  set L := K \ B
  have hLc : IsCompact L := hK.diff (isOpen_biUnion fun z _ => isOpen_ball)
  have hhL : ∀ y ∈ L, h y ≠ 0 := fun y hy hy0 =>
    hy.2 (mem_biUnion ((hZ y).mpr ⟨hy.1, hy0⟩) (mem_ball_self hr0'))
  obtain ⟨δ, hδ, hδL⟩ : ∃ δ > 0, ∀ y ∈ L, δ ≤ ‖h y‖ := by
    rcases L.eq_empty_or_nonempty with hL | hL
    · exact ⟨1, one_pos, by simp [hL]⟩
    · obtain ⟨y₀, hy₀, hmin⟩ := hLc.exists_isMinOn hL
        (hh.continuousOn.norm.mono sdiff_subset)
      exact ⟨‖h y₀‖, norm_pos_iff.mpr (hhL y₀ hy₀), fun y hy => hmin hy⟩
  have hBI : ∀ z ∈ Z, closedBall z r ⊆ K \ C := fun z hz => (hr z hz).1
  have hCL : C ⊆ L := fun y hy => ⟨hCK hy, fun hyB => by
    obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.mp hyB
    exact (hBI z hz (ball_subset_closedBall hyz)).2 hy⟩
  have hsphere : ∀ z ∈ Z, sphere z r ⊆ L := by
    intro z hz y hy
    refine ⟨(hBI z hz (sphere_subset_closedBall hy)).1, fun hyB => ?_⟩
    obtain ⟨z', hz', hyz'⟩ := mem_iUnion₂.mp hyB
    rw [mem_ball] at hyz'
    rw [mem_sphere] at hy
    by_cases hzz : z' = z
    · subst hzz; linarith
    · have h2 := (hr z hz).2.2 z' hz' hzz
      have := dist_triangle z y z'
      rw [dist_comm z y] at this
      linarith
  -- decomposition of the zero count over the discs
  have hdecomp : ∀ k : ℂ → ℂ, AnalyticOnNhd ℂ k K → (∀ y ∈ L, k y ≠ 0) →
      (∑ᶠ y ∈ K \ C, analyticOrderNatAt k y) =
        ∑ z ∈ Z, ∑ᶠ y ∈ ball z r, analyticOrderNatAt k y := by
    intro k hk hkL
    have hkf := finite_zeros_filledHull hC hk fun y hy => hkL y (hCL hy)
    have hsupp : ∀ y, analyticOrderNatAt k y ≠ 0 → y ∈ K → k y = 0 := fun y hy _ => by
      by_contra h'; exact hy (analyticOrderNatAt_eq_zero_of_ne h')
    have hfin : ∀ z ∈ (Z : Set ℂ),
        (ball z r ∩ Function.support (fun y => analyticOrderNatAt k y)).Finite := by
      intro z hz
      refine hkf.subset fun y hy => ?_
      have hyK : y ∈ K := (hBI z hz (ball_subset_closedBall hy.1)).1
      exact ⟨hyK, hsupp y hy.2 hyK⟩
    have hdisj : (Z : Set ℂ).PairwiseDisjoint
        (fun z => ball z r ∩ Function.support (fun y => analyticOrderNatAt k y)) := by
      intro z hz z' hz' hzz
      refine Set.disjoint_left.mpr fun y hy hy' => ?_
      have h2 := (hr z hz).2.2 z' hz' (Ne.symm hzz)
      have h1 := mem_ball.mp hy.1
      have h1' := mem_ball.mp hy'.1
      have := dist_triangle z y z'
      rw [dist_comm z y] at this
      linarith
    rw [← finsum_mem_inter_support, ← finsum_mem_coe_finset]
    have hU : (K \ C) ∩ Function.support (fun y => analyticOrderNatAt k y) =
        ⋃ z ∈ (Z : Set ℂ), ball z r ∩ Function.support (fun y => analyticOrderNatAt k y) := by
      ext y
      simp only [mem_inter_iff, mem_iUnion, exists_prop]
      constructor
      · rintro ⟨hyI, hy⟩
        have hy0 := hsupp y hy hyI.1
        have hyB : y ∈ B := by
          by_contra hyB; exact hkL y ⟨hyI.1, hyB⟩ hy0
        obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.mp hyB
        exact ⟨z, hz, hyz, hy⟩
      · rintro ⟨z, hz, hyz, hy⟩
        exact ⟨hBI z hz (ball_subset_closedBall hyz), hy⟩
    rw [hU, finsum_mem_biUnion hdisj Z.finite_toSet hfin]
    exact finsum_mem_congr rfl fun z _ => finsum_mem_inter_support _ _
  refine ⟨δ, hδ, fun k hk hkh => ?_⟩
  have hkL : ∀ y ∈ L, k y ≠ 0 := by
    intro y hy hk0
    have h1 := hkh y hy.1
    rw [hk0, zero_sub, norm_neg] at h1
    linarith [hδL y hy]
  rw [hdecomp k hk hkL, hdecomp h hh hhL]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hcb : closedBall z r ⊆ K := fun y hy => (hBI z hz hy).1
  refine (TauCeti.rouche (hh.mono hcb) (hk.mono hcb) fun y hy => ?_).symm
  rw [norm_sub_rev]
  exact (hkh y (hcb (sphere_subset_closedBall hy))).trans_le (hδL y (hsphere z hz hy))

/-- **Rouché's theorem for the inside of a compact set.** Let `C ⊆ ℂ` be compact and `K` its
filled hull. If `f`, `g` are analytic on `K` and `‖g z‖ < ‖f z‖` on `C`, then `f` and `f + g`
have the same number of zeros in `K \ C`, counted with multiplicity. -/
theorem rouche_filledHull (hC : IsCompact C) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (filledHull C)) (hg : AnalyticOnNhd ℂ g (filledHull C))
    (hlt : ∀ z ∈ C, ‖g z‖ < ‖f z‖) :
    (∑ᶠ z ∈ filledHull C \ C, analyticOrderNatAt f z) =
      ∑ᶠ z ∈ filledHull C \ C, analyticOrderNatAt (fun w => f w + g w) z := by
  set K := filledHull C
  have hK := isCompact_filledHull_of_isCompact hC
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  set H : ℝ → ℂ → ℂ := fun t w => f w + (t : ℂ) * g w
  have hH : ∀ t, AnalyticOnNhd ℂ (H t) K := fun t => hf.add (analyticOnNhd_const.mul hg)
  have hHC : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ C, H t z ≠ 0 := by
    intro t ht z hz h0
    have h1 : ‖f z‖ ≤ t * ‖g z‖ := by
      have : f z = -((t : ℂ) * g z) := by simp only [H] at h0; linear_combination h0
      rw [this, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
    have h2 : t * ‖g z‖ ≤ ‖g z‖ := mul_le_of_le_one_left (norm_nonneg _) ht.2
    linarith [hlt z hz]
  set N : ℝ → ℕ := fun t => ∑ᶠ z ∈ K \ C, analyticOrderNatAt (H t) z
  have hloc : ∀ t₀ ∈ Icc (0 : ℝ) 1, ∀ᶠ t in 𝓝 t₀, N t = N t₀ := by
    intro t₀ ht₀
    obtain ⟨δ, hδ, hδk⟩ :=
      exists_finsum_analyticOrderNatAt_filledHull_eq hC (hH t₀) (hHC t₀ ht₀)
    have hM0 : 0 < max M 0 + 1 := by positivity
    filter_upwards [Metric.ball_mem_nhds t₀ (div_pos hδ hM0)] with t ht
    refine hδk _ (hH t) fun z hz => ?_
    have he : H t z - H t₀ z = ((t - t₀ : ℝ) : ℂ) * g z := by
      simp only [H]; push_cast; ring
    rw [he, norm_mul, Complex.norm_real]
    rw [mem_ball, Real.dist_eq, lt_div_iff₀ hM0] at ht
    calc ‖t - t₀‖ * ‖g z‖ ≤ |t - t₀| * (max M 0 + 1) := by
          rw [Real.norm_eq_abs]
          gcongr
          exact (hM z hz).trans ((le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one))
      _ < δ := ht
  have hcont : ContinuousOn N (Icc (0 : ℝ) 1) := fun t ht =>
    (tendsto_nhds_of_eventually_eq (hloc t ht)).mono_left nhdsWithin_le_nhds
  have h01 := isPreconnected_Icc.constant hcont (left_mem_Icc.mpr zero_le_one)
    (right_mem_Icc.mpr zero_le_one)
  have hH0 : H 0 = f := by funext w; simp [H]
  have hH1 : H 1 = fun w => f w + g w := by funext w; simp [H]
  simpa only [N, hH0, hH1] using h01

end Complex
