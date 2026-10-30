/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.LHopital
public import Mathlib.Topology.Order.Basic

/-!
# L'Hôpital's rule with an unbounded denominator

The derivative-quotient limit implies the function-quotient limit when the absolute value
of the denominator tends to infinity at a punctured finite point. No limit of the numerator
is required. Cauchy's mean value theorem bounds increments relative to the denominator;
fixed anchors on the two sides of the puncture then contribute vanishing constant terms.
The proof uses Mathlib's `exists_ratio_deriv_eq_ratio_slope` and metric/filter APIs.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace deriv
/-- Cauchy’s mean value theorem transports a bound on a derivative quotient to a bound
on the corresponding affine increments over an ordered interval. -/
private lemma abs_increment_sub_mul_le_of_deriv_div_bound {f g : ℝ → ℝ} {x y l ε : ℝ} (hxy : x < y)
    (hf : ∀ z ∈ Icc x y, DifferentiableAt ℝ f z)
    (hg : ∀ z ∈ Icc x y, DifferentiableAt ℝ g z)
    (hgz : ∀ z ∈ Ioo x y, deriv g z ≠ 0)
    (hbound : ∀ z ∈ Ioo x y, |deriv f z / deriv g z - l| ≤ ε) :
    |f y - f x - l * (g y - g x)| ≤ ε * |g y - g x| := by
  obtain ⟨z, hz, he⟩ := exists_ratio_deriv_eq_ratio_slope f hxy
    (fun z hz => (hf z hz).continuousAt.continuousWithinAt)
    (fun z hz => (hf z (Ioo_subset_Icc_self hz)).differentiableWithinAt) g
    (fun z hz => (hg z hz).continuousAt.continuousWithinAt)
    (fun z hz => (hg z (Ioo_subset_Icc_self hz)).differentiableWithinAt)
  have hrel : f y - f x = deriv f z / deriv g z * (g y - g x) := by
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff (hgz z hz)).mpr
    nlinarith [he]
  calc
    |f y - f x - l * (g y - g x)| = |deriv f z / deriv g z - l| * |g y - g x| := by
      rw [hrel, ← abs_mul]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hbound z hz) (abs_nonneg _)

/-- A small affine increment error and a negligible fixed anchor bound the error in
a quotient whose denominator is nonzero. -/
private lemma abs_quotient_sub_lt_of_increment_bound {f g F G l ε : ℝ} (hε : 0 < ε) (hg : 0 < |g|)
    (hG : |G| ≤ |g|) (hF : 2 * |F - l * G| < ε * |g|)
    (hinc : |f - F - l * (g - G)| ≤ ε / 4 * |g - G|) :
    |f / g - l| < ε := by
  have hdiff : |g - G| ≤ 2 * |g| := (abs_sub g G).trans (by linarith)
  have hsum : |f - l * g| ≤ |f - F - l * (g - G)| + |F - l * G| := by
    calc
      _ = |(f - F - l * (g - G)) + (F - l * G)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have hnum : |f - l * g| < ε * |g| := by
    have := mul_le_mul_of_nonneg_left hdiff (show 0 ≤ ε / 4 by positivity)
    nlinarith
  rw [show f / g - l = (f - l * g) / g by field_simp [abs_pos.mp hg], abs_div, div_lt_iff₀ hg]
  exact hnum
end deriv
namespace deriv
/-- A derivative-quotient bound controls affine increments in either orientation of
a closed interval. -/
private lemma abs_increment_sub_mul_le_of_deriv_div_bound_uIcc {f g : ℝ → ℝ} {x y l ε : ℝ}
    (hf : ∀ z ∈ uIcc x y, DifferentiableAt ℝ f z)
    (hg : ∀ z ∈ uIcc x y, DifferentiableAt ℝ g z)
    (hgz : ∀ z ∈ uIcc x y, deriv g z ≠ 0)
    (hbound : ∀ z ∈ uIcc x y, |deriv f z / deriv g z - l| ≤ ε) :
    |f y - f x - l * (g y - g x)| ≤ ε * |g y - g x| := by
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · rw [uIcc_of_le hxy.le] at *
    exact abs_increment_sub_mul_le_of_deriv_div_bound hxy hf hg
      (fun z hz => hgz z (Ioo_subset_Icc_self hz)) (fun z hz => hbound z (Ioo_subset_Icc_self hz))
  · simp
  · rw [uIcc_of_ge hyx.le] at *
    have h := abs_increment_sub_mul_le_of_deriv_div_bound hyx hf hg
      (fun z hz => hgz z (Ioo_subset_Icc_self hz)) (fun z hz => hbound z (Ioo_subset_Icc_self hz))
    have he : |f y - f x - l * (g y - g x)| = |f x - f y - l * (g x - g y)| := by
      rw [← abs_neg]
      congr 1
      ring
    calc
      _ = |f x - f y - l * (g x - g y)| := he
      _ ≤ ε * |g x - g y| := h
      _ = _ := by rw [abs_sub_comm (g x) (g y)]

/-- An unbounded absolute denominator eventually dominates any fixed anchor and its
affine error by the constants needed in a quotient estimate. -/
private lemma eventually_quotient_anchor_bounds {g : ℝ → ℝ} {L : Filter ℝ}
    (hgtop : Tendsto (fun x => |g x|) L atTop) {F G l ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in L, 0 < |g x| ∧ |G| ≤ |g x| ∧ 2 * |F - l * G| < ε * |g x| := by
  have h := (tendsto_atTop.mp hgtop) (1 + |G| + 2 * |F - l * G| / ε)
  filter_upwards [h] with x hx
  have hdiv : 0 ≤ 2 * |F - l * G| / ε := by positivity
  have hg : 0 < |g x| := by linarith [abs_nonneg G]
  refine ⟨hg, by linarith, ?_⟩
  rw [mul_comm ε]
  apply (div_lt_iff₀ hε).mp
  linarith [abs_nonneg G]
end deriv
namespace deriv
/-- A point near a puncture can be compared with a fixed anchor on the same side,
so the intervening interval stays inside the differentiability region. -/
private lemma punctured_increment_bound_or {f g : ℝ → ℝ} {a δ l η x : ℝ}
    (hlocal : ∀ z, |z - a| < δ → z ≠ a →
      DifferentiableAt ℝ f z ∧ DifferentiableAt ℝ g z ∧ deriv g z ≠ 0 ∧
        |deriv f z / deriv g z - l| ≤ η)
    (hx : |x - a| < δ / 2) (hxne : x ≠ a) :
    (|f x - f (a - δ / 2) - l * (g x - g (a - δ / 2))| ≤
        η * |g x - g (a - δ / 2)|) ∨
    (|f x - f (a + δ / 2) - l * (g x - g (a + δ / 2))| ≤
        η * |g x - g (a + δ / 2)|) := by
  have hxm := (abs_lt.mp hx).1
  have hxp := (abs_lt.mp hx).2
  rcases lt_or_gt_of_ne hxne with hxa | hax
  · left
    have hset : ∀ z ∈ uIcc (a - δ / 2) x, |z - a| < δ ∧ z ≠ a := by
      rw [uIcc_of_le (by linarith : a - δ / 2 ≤ x)]
      intro z hz
      refine ⟨abs_lt.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩, by linarith [hz.2]⟩
    have hh (z) (hz : z ∈ uIcc (a - δ / 2) x) := hlocal z (hset z hz).1 (hset z hz).2
    exact abs_increment_sub_mul_le_of_deriv_div_bound_uIcc (fun z hz => (hh z hz).1) (fun z hz => (hh z hz).2.1)
      (fun z hz => (hh z hz).2.2.1) (fun z hz => (hh z hz).2.2.2)
  · right
    have hset : ∀ z ∈ uIcc (a + δ / 2) x, |z - a| < δ ∧ z ≠ a := by
      rw [uIcc_of_ge (by linarith : x ≤ a + δ / 2)]
      intro z hz
      refine ⟨abs_lt.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩, by linarith [hz.1]⟩
    have hh (z) (hz : z ∈ uIcc (a + δ / 2) x) := hlocal z (hset z hz).1 (hset z hz).2
    exact abs_increment_sub_mul_le_of_deriv_div_bound_uIcc (fun z hz => (hh z hz).1) (fun z hz => (hh z hz).2.1)
      (fun z hz => (hh z hz).2.2.1) (fun z hz => (hh z hz).2.2.2)

/-- L’Hôpital’s rule at a punctured finite point when the denominator is unbounded in
absolute value. The numerator need not have a limit. -/
theorem lhopital_infty_nhdsNE {f g : ℝ → ℝ} {a l : ℝ}
    (hf : ∀ᶠ x in 𝓝[≠] a, DifferentiableAt ℝ f x)
    (hg : ∀ᶠ x in 𝓝[≠] a, DifferentiableAt ℝ g x)
    (hg' : ∀ᶠ x in 𝓝[≠] a, deriv g x ≠ 0)
    (hgtop : Tendsto (fun x => |g x|) (𝓝[≠] a) atTop)
    (hdiv : Tendsto (fun x => deriv f x / deriv g x) (𝓝[≠] a) (𝓝 l)) :
    Tendsto (fun x => f x / g x) (𝓝[≠] a) (𝓝 l) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hder := (Metric.tendsto_nhds.mp hdiv) (ε / 4) (by positivity)
  have hevent : ∀ᶠ x in 𝓝[≠] a, DifferentiableAt ℝ f x ∧ DifferentiableAt ℝ g x ∧
      deriv g x ≠ 0 ∧ |deriv f x / deriv g x - l| ≤ ε / 4 := by
    filter_upwards [hf, hg, hg', hder] with x hfx hgx hgx' hx
    exact ⟨hfx, hgx, hgx', (by simpa only [Real.dist_eq] using hx.le)⟩
  obtain ⟨δ, hδ, hall⟩ := Metric.mem_nhdsWithin_iff.mp hevent
  have hlocal : ∀ z, |z - a| < δ → z ≠ a →
      DifferentiableAt ℝ f z ∧ DifferentiableAt ℝ g z ∧ deriv g z ≠ 0 ∧
        |deriv f z / deriv g z - l| ≤ ε / 4 := by
    intro z hz hzne
    exact hall ⟨by simpa only [Metric.mem_ball, Real.dist_eq] using hz, hzne⟩
  have hid : Tendsto (fun x : ℝ => x) (𝓝[≠] a) (𝓝 a) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hnear : ∀ᶠ x in 𝓝[≠] a, |x - a| < δ / 2 := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hid) (δ / 2) (by positivity)
  have hminus := eventually_quotient_anchor_bounds (F := f (a - δ / 2)) (G := g (a - δ / 2)) (l := l) hgtop hε
  have hplus := eventually_quotient_anchor_bounds (F := f (a + δ / 2)) (G := g (a + δ / 2)) (l := l) hgtop hε
  filter_upwards [hnear, hminus, hplus, self_mem_nhdsWithin] with x hx hm hp hxne
  rw [Real.dist_eq]
  rcases punctured_increment_bound_or hlocal hx hxne with hm' | hp'
  · exact abs_quotient_sub_lt_of_increment_bound hε hm.1 hm.2.1 hm.2.2 hm'
  · exact abs_quotient_sub_lt_of_increment_bound hε hp.1 hp.2.1 hp.2.2 hp'
end deriv
