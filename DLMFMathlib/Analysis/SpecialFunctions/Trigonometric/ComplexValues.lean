/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Special values and identities of the complex trigonometric functions

Complex-argument companions of real facts in Mathlib: `cos (n π) = (-1)ⁿ`,
`sin ((ν + 1) π) = -sin (ν π)`, the nonvanishing of `sin (ν π)` off the integers,
De Moivre's formula for integer exponents, `e^{πi/3} = (1 + √3 i)/2`, and the constants
`π ≠ 0`, `√π √π = π` and `2 i ≠ 0` in `ℂ`.
-/

@[expose] public section
open scoped Real

namespace Complex

/-- `π ≠ 0` as a complex number. -/
theorem ofReal_pi_ne_zero : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero

/-- `√π · √π = π` in `ℂ`. -/
theorem ofReal_sqrt_pi_mul_self : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
  rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]

/-- `2 i ≠ 0`. -/
theorem two_mul_I_ne_zero : (2 * I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero

/-- `cos (n π) = (-1)ⁿ` for natural `n`, in `ℂ`. -/
theorem cos_nat_mul_pi (n : ℕ) : cos (n * π) = (-1) ^ n := by
  rw [← ofReal_natCast, ← ofReal_mul, ← ofReal_cos, Real.cos_nat_mul_pi]
  push_cast; rfl

/-- `sin ((ν + 1) π) = -sin (ν π)`. -/
theorem sin_add_one_mul_pi (ν : ℂ) : sin ((ν + 1) * π) = -sin (ν * π) := by
  rw [add_mul, one_mul, sin_add_pi]

/-- `sin (ν π) ≠ 0` when `ν` is not an integer. -/
theorem sin_mul_pi_ne_zero {ν : ℂ} (hν : ∀ k : ℤ, ν ≠ k) : sin (ν * π) ≠ 0 := by
  rw [Ne, sin_eq_zero_iff]
  rintro ⟨k, hk⟩
  exact hν k (mul_right_cancel₀ ofReal_pi_ne_zero hk)

/-- De Moivre's formula for integer exponents and complex `θ`:
`cos (n θ) + i sin (n θ) = (cos θ + i sin θ)ⁿ`. -/
theorem cos_add_I_mul_sin_zpow (θ : ℂ) (n : ℤ) :
    cos (n * θ) + I * sin (n * θ) = (cos θ + I * sin θ) ^ n := by
  rw [mul_comm I, mul_comm I, cos_add_sin_I, cos_add_sin_I, ← exp_int_mul, mul_assoc]

/-- `e^{πi/3} = (1 + √3 i)/2`. -/
theorem exp_pi_mul_I_div_three : exp (π * I / 3) = (1 + (Real.sqrt 3 : ℂ) * I) / 2 := by
  rw [show (π : ℂ) * I / 3 = ((π / 3 : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I,
    ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast; ring

end Complex
