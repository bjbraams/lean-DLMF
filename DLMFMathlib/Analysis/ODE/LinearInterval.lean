/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.LinearGlobal

/-!
# Linear initial-value problems on an open interval

Continuous coefficients on an open bounded interval give a solution throughout that
interval with arbitrary interior initial data. Compact-interval solutions agree by
uniqueness on their common intervals, so their pointwise gluing has ordinary derivatives.
-/

@[expose] public noncomputable section

open Set Filter Topology

namespace ODE

variable {𝕜 : Type*} [NormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [NormedSpace 𝕜 E]

/-- A continuous linear system has a solution on an open bounded interval with data at any
interior point. -/
theorem exists_linear_system_Ioo {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    {a₁₁ a₁₂ a₂₁ a₂₂ : ℝ → 𝕜} (c₁₁ : ContinuousOn a₁₁ (Ioo a b))
    (c₁₂ : ContinuousOn a₁₂ (Ioo a b)) (c₂₁ : ContinuousOn a₂₁ (Ioo a b))
    (c₂₂ : ContinuousOn a₂₂ (Ioo a b)) (u₀ v₀ : E) :
    ∃ u v : ℝ → E, u t₀ = u₀ ∧ v t₀ = v₀ ∧ ∀ t ∈ Ioo a b,
      HasDerivAt u (a₁₁ t • u t + a₁₂ t • v t) t ∧
      HasDerivAt v (a₂₁ t • u t + a₂₂ t • v t) t := by
  let l (x : Ioo a b) := (a + min t₀ (x : ℝ)) / 2
  let r (x : Ioo a b) := (b + max t₀ (x : ℝ)) / 2
  let J (x : Ioo a b) := Icc (l x) (r x)
  have hl (x : Ioo a b) : a < l x ∧ l x < min t₀ (x : ℝ) := by
    have h : a < min t₀ (x : ℝ) := lt_min ht₀.1 x.property.1
    dsimp only [l]
    constructor <;> linarith
  have hr (x : Ioo a b) : max t₀ (x : ℝ) < r x ∧ r x < b := by
    have h : max t₀ (x : ℝ) < b := max_lt ht₀.2 x.property.2
    dsimp only [r]
    constructor <;> linarith
  have hJ (x : Ioo a b) : J x ⊆ Ioo a b := fun y hy =>
    ⟨(hl x).1.trans_le hy.1, hy.2.trans_lt (hr x).2⟩
  have ht (x : Ioo a b) : t₀ ∈ J x :=
    ⟨((hl x).2.trans_le (min_le_left _ _)).le,
      ((le_max_left _ _).trans_lt (hr x).1).le⟩
  have hx (x : Ioo a b) : (x : ℝ) ∈ Ioo (l x) (r x) :=
    ⟨(hl x).2.trans_le (min_le_right _ _), (le_max_right _ _).trans_lt (hr x).1⟩
  choose U V hU hV hUV using fun x : Ioo a b =>
    exists_linear_system_Icc_of_mem (E := E) (ht x) (c₁₁.mono (hJ x))
      (c₁₂.mono (hJ x)) (c₂₁.mono (hJ x)) (c₂₂.mono (hJ x)) u₀ v₀
  have hcons (x y : Ioo a b) (hy : (y : ℝ) ∈ J x) :
      U y y = U x y ∧ V y y = V x y := by
    let K := Icc (min t₀ (y : ℝ)) (max t₀ (y : ℝ))
    have hkx : K ⊆ J x := uIcc_subset_Icc (ht x) hy
    have hky : K ⊆ J y := uIcc_subset_Icc (ht y) ⟨(hx y).1.le, (hx y).2.le⟩
    have hkin : K ⊆ Ioo a b := hkx.trans (hJ x)
    have hk₀ : t₀ ∈ K := ⟨min_le_left _ _, le_max_left _ _⟩
    have hky' : (y : ℝ) ∈ K := ⟨min_le_right _ _, le_max_right _ _⟩
    have H := eqOn_Icc_of_linear_system hk₀ (c₁₁.mono hkin) (c₁₂.mono hkin)
      (c₂₁.mono hkin) (c₂₂.mono hkin)
      (fun t ht => ⟨(hUV y t (hky ht)).1.mono hky, (hUV y t (hky ht)).2.mono hky⟩)
      (fun t ht => ⟨(hUV x t (hkx ht)).1.mono hkx, (hUV x t (hkx ht)).2.mono hkx⟩)
      (by rw [hU, hU]) (by rw [hV, hV])
    exact ⟨H.1 hky', H.2 hky'⟩
  let u (t : ℝ) := if h : t ∈ Ioo a b then U ⟨t, h⟩ t else 0
  let v (t : ℝ) := if h : t ∈ Ioo a b then V ⟨t, h⟩ t else 0
  have huv (x : Ioo a b) {t : ℝ} (ht : t ∈ J x) :
      u t = U x t ∧ v t = V x t := by
    have htin := hJ x ht
    simpa only [u, v, dite_eq_left htin] using hcons x ⟨t, htin⟩ ht
  refine ⟨u, v, ?_, ?_, fun t htin => ?_⟩
  · simpa only [u, dite_eq_left ht₀] using hU ⟨t₀, ht₀⟩
  · simpa only [v, dite_eq_left ht₀] using hV ⟨t₀, ht₀⟩
  let x : Ioo a b := ⟨t, htin⟩
  have hnhds : J x ∈ 𝓝 t := Icc_mem_nhds (hx x).1 (hx x).2
  have hmem : t ∈ J x := mem_of_mem_nhds hnhds
  have heu : u =ᶠ[𝓝 t] U x := eventually_of_mem hnhds fun s hs => (huv x hs).1
  have hev : v =ᶠ[𝓝 t] V x := eventually_of_mem hnhds fun s hs => (huv x hs).2
  rw [(huv x hmem).1, (huv x hmem).2]
  exact ⟨((hUV x t hmem).1.hasDerivAt hnhds).congr_of_eventuallyEq heu,
    ((hUV x t hmem).2.hasDerivAt hnhds).congr_of_eventuallyEq hev⟩

/-- A second-order linear equation with continuous coefficients has a solution throughout
an open bounded interval for arbitrary interior initial data. -/
theorem exists_linear_ode_Ioo {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    {p q : ℝ → 𝕜} (hp : ContinuousOn p (Ioo a b)) (hq : ContinuousOn q (Ioo a b))
    (y₀ y₁ : E) :
    ∃ f f' : ℝ → E, f t₀ = y₀ ∧ f' t₀ = y₁ ∧ ∀ t ∈ Ioo a b,
      HasDerivAt f (f' t) t ∧ HasDerivAt f' (p t • f' t + q t • f t) t := by
  obtain ⟨u, v, hu, hv, h⟩ := exists_linear_system_Ioo (E := E) ht₀
    (a₁₁ := fun _ => (0 : 𝕜)) (a₁₂ := fun _ => (1 : 𝕜))
    continuousOn_const continuousOn_const hq hp y₀ y₁
  refine ⟨u, v, hu, hv, fun t ht => ⟨?_, ?_⟩⟩
  · simpa using (h t ht).1
  · simpa [add_comm] using (h t ht).2

end ODE
