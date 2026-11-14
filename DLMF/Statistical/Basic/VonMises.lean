/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.Analysis.SpecialFunctions.BesselI

/-!
# The von Mises distribution function

Temme, *Special Functions* (1996), §11.5, (11.85)–(11.89), synopsis TEM-11-20.
The angular density is normalized by the upstream real modified Bessel function.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped Real
namespace DLMF.Statistical

/-- The von Mises angular distribution function, Temme (11.85), synopsis TEM-11-20.
For `κ ≥ 0`, it is a cumulative distribution on `[-π,π]`; the integral formula
also defines its extension to every real `θ,κ`. -/
def Real.vonMisesCDF (θ κ : ℝ) : ℝ :=
  (∫ t : ℝ in -Real.pi..θ, Real.exp (κ * Real.cos t)) /
    (2 * Real.pi * Real.besselI 0 κ)

/-- The integral defining the von Mises distribution, Temme (11.85). -/
theorem Real.vonMisesCDF_def (θ κ : ℝ) :
    Real.vonMisesCDF θ κ =
      (∫ t : ℝ in -Real.pi..θ, Real.exp (κ * Real.cos t)) /
        (2 * Real.pi * Real.besselI 0 κ) := rfl

/-- The left endpoint value of the angular distribution, Temme (11.85). -/
@[simp] theorem Real.vonMisesCDF_neg_pi (κ : ℝ) : Real.vonMisesCDF (-Real.pi) κ = 0 := by
  simp [Real.vonMisesCDF]

/-- The right endpoint value of the angular distribution, Temme (11.85). -/
@[simp] theorem Real.vonMisesCDF_pi (κ : ℝ) : Real.vonMisesCDF Real.pi κ = 1 := by
  have h := _root_.Real.integral_exp_mul_cos_mul_cos κ 0
  simp only [Nat.cast_zero, zero_mul, Real.cos_zero, mul_one] at h
  rw [Real.vonMisesCDF, h]
  exact div_self (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero)
    (ne_of_gt (_root_.Real.besselI_zero_left_pos κ)))

end DLMF.Statistical
