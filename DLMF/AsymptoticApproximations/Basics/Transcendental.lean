/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Basics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Transcendental equations (DLMF §2.2)

* 2.2.1–2.2.2: if `f` is continuous and strictly increasing on `[a, ∞)` with `f(x) ∼ x`, the
  equation `f(x) = y` has a unique root `x(y) > a` for `y > f(a)`, and `x(y) ∼ y`.
* 2.2.3–2.2.6: the example `t² - ln t = y`.
* 2.2.7–2.2.8: Lagrange's formula for the reversion of `f(x) ∼ x + f₀ + f₁x⁻¹ + ⋯`
  (coefficients `lagrangeReversionCoeff`, checked symbolically against the reversion of the
  series through `F₃`). The project's general asymptotic inversion theorem is
  `Asymptotics.HasAsymptoticPowerSeries.inversion`.
-/

@[expose] public noncomputable section

open Filter Asymptotics Set
open scoped Topology

namespace DLMF.AsymptoticApproximations

/-- DLMF 2.2.1 and the statement after it: if `f` is continuous and strictly increasing on
`[a, ∞)` and `f(x) ∼ x` as `x → ∞`, then for every `y > f(a)` the equation `f(x) = y` has a
unique root `x` in `(a, ∞)`. -/
@[dlmf 2.2.E1, dlmf 2.2]
theorem existsUnique_root_of_isEquivalent {f : ℝ → ℝ} {a : ℝ} (hf : ContinuousOn f (Ici a))
    (hmono : StrictMonoOn f (Ici a)) (hfx : f ~[atTop] id) {y : ℝ} (hy : f a < y) :
    ∃! x, a < x ∧ f x = y := by
  have htop : Tendsto f atTop atTop := hfx.symm.tendsto_atTop tendsto_id
  obtain ⟨b, hb⟩ := (htop.eventually (eventually_gt_atTop y)).and (eventually_ge_atTop a)
    |>.exists
  obtain ⟨x, hx, hfx'⟩ := intermediate_value_Icc hb.2 (hf.mono Icc_subset_Ici_self)
    ⟨hy.le, hb.1.le⟩
  have hax : a < x := lt_of_le_of_ne hx.1 fun h => by subst h; exact hy.ne hfx'
  refine ⟨x, ⟨hax, hfx'⟩, fun x' hx' => ?_⟩
  exact hmono.injOn (mem_Ici.mpr hx'.1.le) (mem_Ici.mpr hax.le) (hx'.2.trans hfx'.symm)

/-- DLMF 2.2.2: under the hypotheses of 2.2.1, the root `x(y)` of `f(x) = y` in `(a, ∞)`
satisfies `x(y) ∼ y` as `y → ∞`. Any function `x(·)` that is eventually such a root is
covered. -/
@[dlmf 2.2.E2, dlmf 2.2]
theorem root_isEquivalent {f : ℝ → ℝ} {a : ℝ} (hmono : StrictMonoOn f (Ici a))
    (hfx : f ~[atTop] id) {g : ℝ → ℝ} (hg : ∀ᶠ y in atTop, a < g y ∧ f (g y) = y) :
    g ~[atTop] id := by
  have hgt : Tendsto g atTop atTop := by
    refine tendsto_atTop.mpr fun M => ?_
    set M' := max M a
    filter_upwards [hg, eventually_gt_atTop (f M')] with y hy hyM
    by_contra hlt
    push Not at hlt
    have h1 : f (g y) ≤ f M' := hmono.monotoneOn (mem_Ici.mpr hy.1.le)
      (mem_Ici.mpr (le_max_right M a)) (hlt.le.trans (le_max_left M a))
    linarith [hy.2]
  have h := hfx.comp_tendsto hgt
  refine (IsEquivalent.congr_left h ?_).symm
  filter_upwards [hg] with y hy
  simpa using hy.2

/-- The function `f(x) = x - ½ ln x` of the example 2.2.3 (with `x = t²`) is strictly
increasing on `[½, ∞)`. -/
theorem strictMonoOn_sub_half_log : StrictMonoOn (fun x : ℝ => x - Real.log x / 2) (Ici (1 / 2)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici _) ?_ fun x hx => ?_
  · refine (continuousOn_id.sub ((Real.continuousOn_log.mono fun x hx => ?_).div_const 2))
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) (mem_Ici.mp hx))
  · rw [interior_Ici] at hx
    have hx0 : 0 < x := lt_trans (by norm_num) hx
    have hd : HasDerivAt (fun x : ℝ => x - Real.log x / 2) (1 - x⁻¹ / 2) x :=
      (hasDerivAt_id x).sub ((Real.hasDerivAt_log hx0.ne').div_const 2)
    rw [hd.deriv]
    have : x⁻¹ < 2 := by
      rw [inv_lt_comm₀ hx0 (by norm_num)]; simpa [one_div] using mem_Ioi.mp hx
    linarith

/-- `x - ½ ln x ∼ x` as `x → ∞`. -/
theorem sub_half_log_isEquivalent : (fun x : ℝ => x - Real.log x / 2) ~[atTop] id := by
  have h : (fun x : ℝ => -(Real.log x / 2)) =o[atTop] id :=
    (Real.isLittleO_log_id_atTop.const_mul_left (1 / 2)).neg_left.congr_left fun x => by ring
  exact h.congr_left fun x => by simp [sub_eq_add_neg]

/-- DLMF 2.2.3: for every `y > ½(1 + ln 2)` the equation `t² - ln t = y` has a unique root
`t > 2^{-1/2}` (with `x = t²`, `f(x) = x - ½ ln x`, `a = ½`). -/
@[dlmf 2.2.E3]
theorem existsUnique_sq_sub_log_eq {y : ℝ} (hy : (1 + Real.log 2) / 2 < y) :
    ∃! t : ℝ, (Real.sqrt 2)⁻¹ < t ∧ t ^ 2 - Real.log t = y := by
  have hf0 : (fun x : ℝ => x - Real.log x / 2) (1 / 2) < y := by
    simp only [one_div, Real.log_inv]; linarith
  obtain ⟨x, ⟨hx, hfx⟩, hu⟩ := existsUnique_root_of_isEquivalent
    ((continuousOn_id.sub ((Real.continuousOn_log.mono fun x hx =>
      ne_of_gt (lt_of_lt_of_le (by norm_num) (mem_Ici.mp hx))).div_const 2)))
    strictMonoOn_sub_half_log sub_half_log_isEquivalent hf0
  have hx0 : 0 < x := lt_trans (by norm_num) hx
  have hlogsqrt : ∀ u : ℝ, 0 < u → Real.log (Real.sqrt u) = Real.log u / 2 := fun u hu => by
    rw [Real.log_sqrt hu.le]
  have hs2 : (Real.sqrt 2)⁻¹ = Real.sqrt (1 / 2) := by
    rw [Real.sqrt_div' 1 (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_one, one_div]
  refine ⟨Real.sqrt x, ⟨?_, ?_⟩, fun t ht => ?_⟩
  · rw [hs2]; exact Real.sqrt_lt_sqrt (by norm_num) hx
  · rw [Real.sq_sqrt hx0.le, hlogsqrt x hx0]; exact hfx
  · have ht0 : 0 < t := lt_trans (by positivity) ht.1
    have h1 : 1 / 2 < t ^ 2 := by
      have := pow_lt_pow_left₀ ht.1 (by positivity) (two_ne_zero)
      rwa [inv_pow, Real.sq_sqrt (by norm_num), ← one_div] at this
    have h2 := hu (t ^ 2) ⟨h1, by
      show t ^ 2 - Real.log (t ^ 2) / 2 = y
      rw [Real.log_pow]; push_cast; linarith [ht.2]⟩
    rw [← h2, Real.sqrt_sq ht0.le]

/-- DLMF 2.2.4: a root `t(y) > 2^{-1/2}` of `t² - ln t = y` satisfies
`t = y^{1/2}(1 + o(1))`, that is, `t(y) ∼ y^{1/2}` as `y → ∞`. -/
@[dlmf 2.2.E4]
theorem sq_sub_log_root_isEquivalent {t : ℝ → ℝ}
    (ht : ∀ᶠ y in atTop, (Real.sqrt 2)⁻¹ < t y ∧ t y ^ 2 - Real.log (t y) = y) :
    t ~[atTop] fun y => Real.sqrt y := by
  sorry

/-- DLMF 2.2.5: `t² = y + ln t = y + ½ ln y + o(1)` as `y → ∞`. -/
@[dlmf 2.2.E5]
theorem sq_sub_log_root_sq {t : ℝ → ℝ}
    (ht : ∀ᶠ y in atTop, (Real.sqrt 2)⁻¹ < t y ∧ t y ^ 2 - Real.log (t y) = y) :
    (∀ᶠ y in atTop, t y ^ 2 = y + Real.log (t y)) ∧
      (fun y => t y ^ 2 - (y + Real.log y / 2)) =o[atTop] fun _ => (1 : ℝ) := by
  sorry

/-- DLMF 2.2.6: `t = y^{1/2}(1 + ¼ y⁻¹ ln y + o(y⁻¹))` as `y → ∞`. -/
@[dlmf 2.2.E6]
theorem sq_sub_log_root_second {t : ℝ → ℝ}
    (ht : ∀ᶠ y in atTop, (Real.sqrt 2)⁻¹ < t y ∧ t y ^ 2 - Real.log (t y) = y) :
    (fun y => t y - Real.sqrt y * (1 + y⁻¹ * Real.log y / 4)) =o[atTop]
      fun y => Real.sqrt y * y⁻¹ := by
  sorry

/-- DLMF 2.2.7–2.2.8 (Lagrange's formula for the reversion of series): if
`f(x) ∼ x + f₀ + f₁x⁻¹ + f₂x⁻² + ⋯` as `x → +∞` (2.2.7) and `x(y) → ∞` solves `f(x(y)) = y`
for large `y`, then `x(y) ∼ y - F₀ - F₁y⁻¹ - F₂y⁻² - ⋯` as `y → +∞`, where `F₀ = f₀` and `sFₛ` is
the coefficient of `x⁻¹` in the expansion of `f(x)ˢ` (`lagrangeReversionCoeff`). Expansions
as `x → +∞` are Poincaré expansions on `𝐗 = (0, ∞)`. -/
@[dlmf 2.2.E7, dlmf 2.2.E8]
theorem lagrange_reversion {f : ℝ → ℝ} {fc : ℕ → ℝ}
    (hf : HasPoincareExpansion (Ioi 0) fc fun x => f x - x) {x : ℝ → ℝ}
    (hx : Tendsto x atTop atTop) (hxy : ∀ᶠ y in atTop, f (x y) = y) :
    HasPoincareExpansion (Ioi 0) (fun s => -lagrangeReversionCoeff fc s) fun y => x y - y := by
  sorry

end DLMF.AsymptoticApproximations
