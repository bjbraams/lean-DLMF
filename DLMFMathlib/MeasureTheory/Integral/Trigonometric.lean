/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Trigonometric changes of variables on a quarter period

`MeasureTheory.integral_Ioo_eq_integral_cos_sq` substitutes `u = cos² θ` between `(0, 1)`
and `(0, π/2)`, with the absolute Jacobian `2 sin θ cos θ`. It applies to arbitrary real
normed target spaces and retains Mathlib's totalized Bochner-integral convention.
-/

@[expose] public noncomputable section

open Set
open scoped Real

namespace MeasureTheory

/-- The substitution `u = cos² θ` on a quarter period. The open intervals omit both
limiting endpoints, so no endpoint regularity of the integrand is needed. -/
lemma integral_Ioo_eq_integral_cos_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : ℝ → E) :
    ∫ u in Ioo (0 : ℝ) 1, G u =
      ∫ θ in Ioo (0 : ℝ) (π / 2), (2 * Real.sin θ * Real.cos θ) • G (Real.cos θ ^ 2) := by
  have hmono : StrictAntiOn (fun θ => Real.cos θ ^ 2) (Icc 0 (π / 2)) := by
    intro u hu v hv huv
    have hc : 0 ≤ Real.cos v :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hv.1, Real.pi_pos], hv.2⟩
    exact pow_lt_pow_left₀ (Real.strictAntiOn_cos
      ⟨hu.1, by linarith [hu.2, Real.pi_pos]⟩
      ⟨hv.1, by linarith [hv.2, Real.pi_pos]⟩ huv) hc two_ne_zero
  have himg := ContinuousOn.image_Ioo_of_strictAntiOn
    (show (0 : ℝ) ≤ π / 2 by positivity) (Real.continuous_cos.pow 2).continuousOn hmono
  change (fun θ => Real.cos θ ^ 2) '' Ioo (0 : ℝ) (π / 2) =
    Ioo (Real.cos (π / 2) ^ 2) (Real.cos 0 ^ 2) at himg
  simp only [Real.cos_zero, one_pow, Real.cos_pi_div_two, zero_pow two_ne_zero] at himg
  have H := integral_image_eq_integral_abs_deriv_smul (s := Ioo (0 : ℝ) (π / 2))
    measurableSet_Ioo (f := fun θ => Real.cos θ ^ 2)
    (f' := fun θ => -(2 * Real.sin θ * Real.cos θ))
    (fun θ _ => ((Real.hasDerivAt_cos θ).pow 2).hasDerivWithinAt.congr_deriv (by ring))
    (hmono.injOn.mono Ioo_subset_Icc_self) G
  rw [himg] at H
  rw [H]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have hs : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  simp [abs_neg, abs_of_pos (by positivity : 0 < 2 * Real.sin θ * Real.cos θ)]

end MeasureTheory
