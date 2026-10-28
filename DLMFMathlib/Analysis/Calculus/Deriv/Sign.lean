/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Signs of real functions near zeros, and two derivatives

Facts used in zero-counting arguments for real solutions of differential equations:
the sign of the derivative at a zero next to an interval of positivity, nonnegativity at
the endpoints of such an interval, and constancy of sign of a nonvanishing continuous
function on an order-connected set. Also the derivative of the real part of a complex
curve and `x ↦ x²` as a map of `𝓝[<] 1` to itself.
-/

@[expose] public section
open Filter Set
open scoped Topology

namespace HasDerivAt

/-- At a zero `a` followed by positive values on `(a, b)`, the derivative is nonnegative. -/
theorem nonneg_of_eq_zero_of_pos_Ioo {f : ℝ → ℝ} {d a b : ℝ} (hd : HasDerivAt f d a)
    (h0 : f a = 0) (hab : a < b) (hpos : ∀ x ∈ Ioo a b, 0 < f x) : 0 ≤ d := by
  have hs := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left (nhdsGT_le_nhdsNE a)
  refine ge_of_tendsto hs ?_
  filter_upwards [Ioo_mem_nhdsGT hab] with x hx
  rw [slope_def_field, h0, sub_zero]
  exact (div_pos (hpos x hx) (sub_pos.mpr hx.1)).le

/-- At a zero `b` preceded by positive values on `(a, b)`, the derivative is nonpositive. -/
theorem nonpos_of_eq_zero_of_pos_Ioo {f : ℝ → ℝ} {d a b : ℝ} (hd : HasDerivAt f d b)
    (h0 : f b = 0) (hab : a < b) (hpos : ∀ x ∈ Ioo a b, 0 < f x) : d ≤ 0 := by
  have hs := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left (nhdsLT_le_nhdsNE b)
  refine le_of_tendsto hs ?_
  filter_upwards [Ioo_mem_nhdsLT hab] with x hx
  rw [slope_def_field, h0, sub_zero]
  exact (div_neg_of_pos_of_neg (hpos x hx) (sub_neg.mpr hx.2)).le

/-- The real part of a differentiable complex curve has the real part of its derivative. -/
theorem complex_re {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun y => (f y).re) f'.re x :=
  (Complex.reCLM.hasFDerivAt (x := f x)).comp_hasDerivAt x h

end HasDerivAt

namespace ContinuousAt

/-- A function continuous at `a` and positive on `(a, b)` is nonnegative at `a`. -/
theorem nonneg_of_pos_Ioo_left {f : ℝ → ℝ} {a b : ℝ} (hc : ContinuousAt f a) (hab : a < b)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x) : 0 ≤ f a := by
  refine ge_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi a))) ?_
  filter_upwards [Ioo_mem_nhdsGT hab] with x hx using (hpos x hx).le

/-- A function continuous at `b` and positive on `(a, b)` is nonnegative at `b`. -/
theorem nonneg_of_pos_Ioo_right {f : ℝ → ℝ} {a b : ℝ} (hc : ContinuousAt f b) (hab : a < b)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x) : 0 ≤ f b := by
  refine ge_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio b))) ?_
  filter_upwards [Ioo_mem_nhdsLT hab] with x hx using (hpos x hx).le

end ContinuousAt

/-- A continuous function without zeros on an order-connected set of reals has constant
sign there. -/
theorem ContinuousOn.pos_or_neg_of_ne_zero {f : ℝ → ℝ} {s : Set ℝ} (hs : s.OrdConnected)
    (hc : ContinuousOn f s) (hne : ∀ x ∈ s, f x ≠ 0) :
    (∀ x ∈ s, 0 < f x) ∨ (∀ x ∈ s, f x < 0) := by
  by_contra h
  push Not at h
  obtain ⟨⟨x₁, hx₁, h₁⟩, ⟨x₂, hx₂, h₂⟩⟩ := h
  have h₁' : f x₁ < 0 := lt_of_le_of_ne h₁ (hne x₁ hx₁)
  have h₂' : 0 < f x₂ := lt_of_le_of_ne h₂ (hne x₂ hx₂).symm
  rcases le_total x₁ x₂ with hle | hle
  · obtain ⟨c, hc', hc0⟩ := intermediate_value_Icc hle (hc.mono (hs.out hx₁ hx₂))
      ⟨h₁'.le, h₂'.le⟩
    exact hne c (hs.out hx₁ hx₂ hc') hc0
  · obtain ⟨c, hc', hc0⟩ := intermediate_value_Icc' hle (hc.mono (hs.out hx₂ hx₁))
      ⟨h₁'.le, h₂'.le⟩
    exact hne c (hs.out hx₂ hx₁ hc') hc0

/-- Squaring maps the left neighbourhoods of `1` into themselves. -/
theorem tendsto_sq_nhdsLT_one :
    Tendsto (fun x : ℝ => x ^ 2) (𝓝[<] (1 : ℝ)) (𝓝[<] 1) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have := ((continuous_pow 2).tendsto (1 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Iio 1))
    simpa using this
  · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
    simp only [mem_Iio]; nlinarith [hx.1, hx.2]
