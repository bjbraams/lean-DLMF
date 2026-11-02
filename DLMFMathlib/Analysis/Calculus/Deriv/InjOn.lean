/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.LocalExtr.Rolle
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Injectivity and images of real functions with nonvanishing derivative

A continuous real function whose derivative does not vanish on an interval is injective there
(Rolle's theorem), hence strictly monotone. This file records that fact together with the images
of initial open intervals under continuous strictly monotone functions, and the corresponding
statement on `(0, c]` for a function tending to `+∞` at `0`.

## Main results

* `injOn_Icc_of_hasDerivAt_ne_zero`: a continuous function with nonvanishing derivative on the
  interior is injective on `[α, β]`.
* `image_Ioo_of_strictAntiOn_Icc`, `image_Ioo_of_strictMonoOn_Icc`: `f '' (lo, y)` for a continuous
  strictly monotone function on `[lo, hi]`.
* `strictAntiOn_Ioc_of_tendsto_atTop`: a function on `(0, c]` with nonvanishing derivative and
  limit `+∞` at `0⁺` is strictly decreasing and maps `(0, x)` onto `(f x, ∞)`.
-/

@[expose] public section

open Set Filter Topology

/-- Rolle: a continuous function whose derivative never vanishes is injective. -/
theorem injOn_Icc_of_hasDerivAt_ne_zero {f f' : ℝ → ℝ} {α β : ℝ} (hc : ContinuousOn f (Icc α β))
    (hd : ∀ t ∈ Ioo α β, HasDerivAt f (f' t) t) (hne : ∀ t ∈ Ioo α β, f' t ≠ 0) :
    InjOn f (Icc α β) := by
  have key : ∀ x ∈ Icc α β, ∀ y ∈ Icc α β, x < y → f x ≠ f y := by
    intro x hx y hy hxy hfxy
    obtain ⟨c, hc', hc0⟩ := exists_hasDerivAt_eq_zero hxy (hc.mono (Icc_subset_Icc hx.1 hy.2))
      hfxy (fun t ht => hd t ⟨hx.1.trans_lt ht.1, ht.2.trans_le hy.2⟩)
    exact hne c ⟨hx.1.trans_lt hc'.1, hc'.2.trans_le hy.2⟩ hc0
  intro x hx y hy hxy
  by_contra hne'
  rcases lt_or_gt_of_ne hne' with h | h
  · exact key x hx y hy h hxy
  · exact key y hy x hx h hxy.symm

/-- Image of an initial open interval under a continuous strictly decreasing function. -/
theorem image_Ioo_of_strictAntiOn_Icc {f : ℝ → ℝ} {lo hi y : ℝ}
    (hc : ContinuousOn f (Icc lo hi)) (ha : StrictAntiOn f (Icc lo hi)) (hy : y ∈ Icc lo hi) :
    f '' Ioo lo y = Ioo (f y) (f lo) := by
  have hlo : lo ∈ Icc lo hi := ⟨le_rfl, hy.1.trans hy.2⟩
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    have htI : t ∈ Icc lo hi := ⟨ht.1.le, ht.2.le.trans hy.2⟩
    exact ⟨ha htI hy ht.2, ha hlo htI ht.1⟩
  · intro hu
    obtain ⟨t, ht, rfl⟩ := intermediate_value_Icc' hy.1 (hc.mono (Icc_subset_Icc le_rfl hy.2))
      ⟨hu.1.le, hu.2.le⟩
    refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩, rfl⟩
    · rintro rfl; exact hu.2.ne rfl
    · rintro rfl; exact hu.1.ne' rfl

/-- Image of an initial open interval under a continuous strictly increasing function. -/
theorem image_Ioo_of_strictMonoOn_Icc {f : ℝ → ℝ} {lo hi y : ℝ}
    (hc : ContinuousOn f (Icc lo hi)) (ha : StrictMonoOn f (Icc lo hi)) (hy : y ∈ Icc lo hi) :
    f '' Ioo lo y = Ioo (f lo) (f y) := by
  have hlo : lo ∈ Icc lo hi := ⟨le_rfl, hy.1.trans hy.2⟩
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    have htI : t ∈ Icc lo hi := ⟨ht.1.le, ht.2.le.trans hy.2⟩
    exact ⟨ha hlo htI ht.1, ha htI hy ht.2⟩
  · intro hu
    obtain ⟨t, ht, rfl⟩ := intermediate_value_Icc hy.1 (hc.mono (Icc_subset_Icc le_rfl hy.2))
      ⟨hu.1.le, hu.2.le⟩
    refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩, rfl⟩
    · rintro rfl; exact hu.1.ne rfl
    · rintro rfl; exact hu.2.ne rfl

/-- A function on `(0, c]` with nonvanishing derivative tending to `+∞` at `0` is strictly
decreasing, and maps `(0, x)` onto `(f x, ∞)`. -/
theorem strictAntiOn_Ioc_of_tendsto_atTop {f f' : ℝ → ℝ} {c : ℝ}
    (hcont : ∀ t ∈ Ioc 0 c, ContinuousAt f t) (hd : ∀ t ∈ Ioo 0 c, HasDerivAt f (f' t) t)
    (hne : ∀ t ∈ Ioo 0 c, f' t ≠ 0) (hlim : Tendsto f (𝓝[>] 0) atTop) :
    StrictAntiOn f (Ioc 0 c) ∧ ∀ x ∈ Ioc 0 c, f '' Ioo 0 x = Ioi (f x) := by
  -- on `[ε, c]` with `f ε > f c`, `f` is strictly decreasing
  have hanti : ∀ ε ∈ Ioo 0 c, f c ≤ f ε → StrictAntiOn f (Icc ε c) := by
    intro ε hε hfε
    have hcI : ContinuousOn f (Icc ε c) := fun t ht =>
      (hcont t ⟨hε.1.trans_le ht.1, ht.2⟩).continuousWithinAt
    exact hcI.strictAntiOn_of_injOn_Icc hε.2.le hfε (injOn_Icc_of_hasDerivAt_ne_zero hcI
      (fun t ht => hd t ⟨hε.1.trans ht.1, ht.2⟩) (fun t ht => hne t ⟨hε.1.trans ht.1, ht.2⟩))
  -- small `ε` with `f ε` large
  have hsmall : ∀ M : ℝ, ∀ s > 0, ∃ ε ∈ Ioo 0 s, M < f ε := by
    intro M s hs
    have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), M < f t := hlim.eventually (eventually_gt_atTop M)
    have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 s := Ioo_mem_nhdsGT hs
    obtain ⟨ε, h1, h2⟩ := (h1.and h2).exists
    exact ⟨ε, h2, h1⟩
  have hSA : StrictAntiOn f (Ioc 0 c) := by
    intro s hs t ht hst
    obtain ⟨ε, hε, hfε⟩ := hsmall (f c) s hs.1
    have hεc : ε ∈ Ioo 0 c := ⟨hε.1, hε.2.trans_le hs.2⟩
    exact hanti ε hεc hfε.le ⟨hε.2.le, hs.2⟩ ⟨hε.2.le.trans hst.le, ht.2⟩ hst
  refine ⟨hSA, fun x hx => ?_⟩
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact hSA ⟨ht.1, ht.2.le.trans hx.2⟩ hx ht.2
  · intro hu
    obtain ⟨ε, hε, hfε⟩ := hsmall u x hx.1
    have hcI : ContinuousOn f (Icc ε x) := fun t ht =>
      (hcont t ⟨hε.1.trans_le ht.1, ht.2.trans hx.2⟩).continuousWithinAt
    obtain ⟨t, ht, rfl⟩ := intermediate_value_Icc' hε.2.le hcI ⟨(mem_Ioi.mp hu).le, hfε.le⟩
    refine ⟨t, ⟨hε.1.trans_le ht.1, lt_of_le_of_ne ht.2 ?_⟩, rfl⟩
    rintro rfl; exact (mem_Ioi.mp hu).ne rfl
