/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Analytic.Uniqueness

/-!
# The identity theorem on the strip `0 < Re z < 1`

Two functions holomorphic on the vertical strip `0 < Re z < 1` that agree on the real segment
`(0, 1)` agree on the whole strip.

## Main results

* `Complex.eqOn_strip_of_eq_ofReal`: the identity theorem on the strip from agreement on `(0, 1)`.
-/

@[expose] public section

open Set Filter Topology

namespace Complex

/-- Identity theorem on the strip `0 < Re x < 1` from agreement on `(0, 1)`. -/
theorem eqOn_strip_of_eq_ofReal {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {x : ℂ | 0 < x.re ∧ x.re < 1})
    (hg : DifferentiableOn ℂ g {x : ℂ | 0 < x.re ∧ x.re < 1})
    (h : ∀ x : ℝ, 0 < x → x < 1 → f x = g x) {z : ℂ} (hz : 0 < z.re ∧ z.re < 1) :
    f z = g z := by
  have hU : IsOpen {x : ℂ | 0 < x.re ∧ x.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hconv : Convex ℝ {x : ℂ | 0 < x.re ∧ x.re < 1} :=
    (convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)
  have h0 : ((1 / 2 : ℝ) : ℂ) ∈ {x : ℂ | 0 < x.re ∧ x.re < 1} := by
    simp only [mem_ofPred_eq, Complex.ofReal_re]; norm_num
  refine (hf.analyticOnNhd hU).eqOn_of_preconnected_of_frequently_eq (hg.analyticOnNhd hU)
    hconv.isPreconnected h0 ?_ hz
  have hev : ∀ᶠ x : ℝ in 𝓝[≠] (1 / 2), f x = g x := by
    filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1))] with x hx
    exact h x hx.1 hx.2
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (1 / 2)) (𝓝[≠] ((1 / 2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun x hx =>
      Complex.ofReal_injective.ne hx
  exact ht.frequently hev.frequently

end Complex
