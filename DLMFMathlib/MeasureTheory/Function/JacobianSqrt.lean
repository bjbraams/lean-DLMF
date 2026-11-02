/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# A change of variables for `∫ du/√Q(u)`

If `|f'| = 2√(Q ∘ f)` on a measurable set `s` on which `f` is injective, the one-dimensional change
of variables formula gives `∫_{f(s)} du/√Q(u) = 2 |s|`. This is the form in which elliptic-type
integrals `∫ du/√Q(u)` are inverted by a function satisfying `f'² = 4 Q(f)`.

## Main results

* `MeasureTheory.integral_image_one_div_sqrt`: `∫_{f(s)} du/√Q(u) = 2 · vol(s)`.
-/

@[expose] public section

open Set

namespace MeasureTheory

/-- Change of variables for `∫ du/√Q(u)`: if `|f'| = 2√(Q ∘ f)` on `s` and `f` is injective
there, then the integral of `1/√Q` over `f(s)` is twice the measure of `s`. -/
theorem integral_image_one_div_sqrt {s : Set ℝ} (hs : MeasurableSet s) {f f' Q : ℝ → ℝ}
    (hf : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hinj : InjOn f s)
    (hQ : ∀ x ∈ s, 0 < Q (f x)) (hd : ∀ x ∈ s, |f' x| = 2 * Real.sqrt (Q (f x))) :
    ∫ u in f '' s, 1 / Real.sqrt (Q u) = 2 * volume.real s := by
  rw [integral_image_eq_integral_abs_deriv_smul hs hf hinj]
  rw [setIntegral_congr_fun hs (g := fun _ => (2 : ℝ)) (fun x hx => ?_)]
  · rw [setIntegral_const, smul_eq_mul, mul_comm]
  · have := Real.sqrt_pos.mpr (hQ x hx)
    simp only [smul_eq_mul]
    rw [hd x hx]
    field_simp

end MeasureTheory
