/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.RCLike.Sqrt

/-!
# Arguments, logarithms and the slit plane

Elementary facts on the principal argument and logarithm: arguments of rays
`ρ e^{is}` and of rotations `z e^{iα}`, `arg w = arctan (Im w / Re w)` in the right
half-plane, `log (a²) = 2 log a` there, invariance of the slit plane under positive real
scaling and inversion, and `Re (√z) ≥ 0`.
-/

@[expose] public section
open scoped Real

namespace Complex

/-- `‖r e^{iu}‖ = r` for real `r ≥ 0`. -/
theorem norm_ofReal_mul_exp_ofReal_mul_I {r : ℝ} (hr : 0 ≤ r) (u : ℝ) :
    ‖(r : ℂ) * exp (u * I)‖ = r := by
  rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hr]

/-- The argument of the ray point `ρ e^{is}` is `s` when `ρ > 0` and `s ∈ (-π, π]`. -/
theorem arg_ofReal_mul_exp_ofReal_mul_I {ρ s : ℝ} (hρ : 0 < ρ) (hs : s ∈ Set.Ioc (-π) π) :
    arg ((ρ : ℂ) * exp (s * I)) = s := by
  rw [arg_real_mul _ hρ, exp_mul_I, arg_cos_add_sin_mul_I hs]

/-- Rotating `z ≠ 0` by `α` adds `α` to the argument as long as `arg z + α ∈ (-π, π]`. -/
theorem arg_mul_exp_ofReal_mul_I {z : ℂ} (hz : z ≠ 0) {α : ℝ} (h1 : -π < arg z + α)
    (h2 : arg z + α ≤ π) : arg (z * exp (α * I)) = arg z + α := by
  have hlog : log (z * exp (α * I)) = log z + α * I := by
    have : z * exp (α * I) = exp (log z + α * I) := by rw [exp_add, exp_log hz]
    rw [this, log_exp] <;> simp [log_im] <;> linarith
  rw [← log_im, hlog]; simp [log_im]

/-- In the open right half-plane, `arg w = arctan (Im w / Re w)`. -/
theorem arg_eq_arctan_of_re_pos {w : ℂ} (hw : 0 < w.re) : arg w = Real.arctan (w.im / w.re) := by
  have h := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw))
  rw [← tan_arg, Real.arctan_tan h.1 h.2]

/-- In the open right half-plane the principal logarithm satisfies `log (a²) = 2 log a`. -/
theorem log_sq_of_re_pos {a : ℂ} (ha : 0 < a.re) : log (a ^ 2) = 2 * log a := by
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  have harg := abs_lt.mp (abs_arg_lt_pi_div_two_iff.2 (Or.inl ha))
  rw [show a ^ 2 = exp (2 * log a) by rw [two_mul, exp_add, exp_log ha0, sq]]
  refine log_exp ?_ ?_
  · simp [log_im]; linarith
  · simp [log_im]; linarith

/-- The slit plane is invariant under multiplication by a positive real. -/
theorem ofReal_mul_mem_slitPlane {l : ℝ} (hl : 0 < l) {x : ℂ} (hx : x ∈ slitPlane) :
    (l : ℂ) * x ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hx ⊢
  rw [re_ofReal_mul, im_ofReal_mul]
  rcases hx with h | h
  · exact Or.inl (mul_pos hl h)
  · exact Or.inr (mul_ne_zero hl.ne' h)

/-- The slit plane is invariant under inversion. -/
theorem inv_mem_slitPlane {w : ℂ} (hw : w ∈ slitPlane) : w⁻¹ ∈ slitPlane := by
  have hn : 0 < normSq w := normSq_pos.mpr (slitPlane_ne_zero hw)
  rw [mem_slitPlane_iff] at hw ⊢
  rcases hw with h | h
  · left; rw [inv_re]; positivity
  · right; rw [inv_im]; exact div_ne_zero (neg_ne_zero.mpr h) hn.ne'

/-- The principal square root has nonnegative real part. -/
theorem re_sqrt_nonneg (z : ℂ) : 0 ≤ z.sqrt.re := by
  rw [Complex.sqrt, cpow_inv_two_re]; exact Real.sqrt_nonneg _

end Complex
