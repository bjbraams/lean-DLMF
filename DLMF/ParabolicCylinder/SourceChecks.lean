/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.ParabolicCylinder
public import Mathlib.Analysis.PSeries

/-!
# Source discrepancies in the parabolic cylinder addition formulas

At `n = 0` and `z = 0` the printed formula DLMF 12.13.6 would give `U(1/2, 0) = 1`, but
`U(1/2, 0) = √π/√2`.

At `a = -1/2 + 2i`, `x = y = 0` and `t = π/4`, the rotational addition summands in
DLMF 12.13.5 are not summable as an unordered complex family. The norms of the even terms
are bounded below by a nonzero constant times `1/n`. Thus an endpoint assertion of
`HasSum` needs a stricter domain than `Re a ≤ -1/2` at this boundary.

## Main results

* `parabolicCylinderU_half_zero_ne_one`: `U(1/2, 0) ≠ 1`.
* `parabolicCylinderU_half_zero_ne_erfc_mul`: the printed formula DLMF 12.13.6 fails at `n = 0`,
  `z = 0`.
* `RotationalAdditionEndpoint.not_hasSum_rotational_addition_endpoint`: the complex endpoint
  `a = -1/2+2i`, `x = y = 0`, `t = π/4` does not have an unordered sum.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

/-- At n=0 and z=0, DLMF 12.13.6 would incorrectly assert this value equals one. -/
theorem parabolicCylinderU_half_zero_ne_one  :
    parabolicCylinderU (1/2) 0 ≠ 1 := by
  intro h
  rw [parabolicCylinderU_zero] at h
  norm_num at h
  have hp : (2:ℂ)^(1/2:ℂ)=(Real.sqrt 2:ℂ) := by
    have hh := (Complex.ofReal_cpow (by norm_num : 0 ≤ (2:ℝ)) (1/2:ℝ)).symm
    rw [← Real.sqrt_eq_rpow 2] at hh
    simpa using hh
  rw [hp] at h
  have hr : Real.sqrt π/Real.sqrt 2=1 := by exact_mod_cast h
  have he : Real.sqrt π=Real.sqrt 2 := (div_eq_one_iff_eq (by positivity)).mp hr
  have hsπ:=Real.sq_sqrt Real.pi_pos.le
  have hs2:=Real.sq_sqrt (by norm_num : 0 ≤ (2:ℝ))
  have hπ:=Real.pi_gt_three
  rw [← he] at hs2
  linarith

/-- Counterexample to the printed formula, using only the pre-existing cylinder and error-function
theory. -/
theorem parabolicCylinderU_half_zero_ne_erfc_mul  :
    parabolicCylinderU (1/2) 0 ≠
        exp (-(0:ℂ)^2/2)*erfc (0/Real.sqrt 2)*parabolicCylinderU (-1/2) (I*0) := by
  simpa [erfc,erf_zero,parabolicCylinderU_neg_half] using parabolicCylinderU_half_zero_ne_one

namespace RotationalAdditionEndpoint

/-- The even terms of the rotational addition formula at `a = -1/2+2i`, `x = y = 0`,
omitting the common nonzero cosine factor. -/
def evenTerm (n : ℕ) : ℂ :=
  pochhammer (2*I) (2*n)/((2*n).factorial:ℂ) *
    parabolicCylinderU (2*n-1/2+2*I) 0 * parabolicCylinderU (-2*n-1/2) 0

/-- The two-step parameter recurrence for `U` at zero. -/
theorem parameter_step (a : ℂ) :
    (a+3/2)*parabolicCylinderU (a+2) 0 = parabolicCylinderU a 0 := by
  have h := parabolicCylinderU_three_term (a+1) 0
  rw [show a+1-1=a by ring, show a+1+1=a+2 by ring] at h
  linear_combination h

/-- The initial even term is the nonzero value `U(-1/2+2i,0)`. -/
theorem evenTerm_zero : evenTerm 0 = parabolicCylinderU (-1/2+2*I) 0 := by
  unfold evenTerm
  rw [Nat.mul_zero, pochhammer_zero]
  norm_num only [Nat.factorial_zero, Nat.cast_zero, Nat.cast_one, mul_zero, zero_sub,
    zero_add, div_one, one_mul]
  rw [show -(1/2:ℂ) = -1/2 by ring, parabolicCylinderU_neg_half]
  simp

/-- The value of `U` occurring in the initial even term does not vanish. -/
theorem initial_ne_zero : parabolicCylinderU (-1/2+2*I) 0 ≠ 0 := by
  rw [parabolicCylinderU_zero]
  refine div_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne')
    (mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)) ?_)
  refine Complex.Gamma_ne_zero fun n hn => ?_
  have h := congrArg Complex.im hn
  norm_num at h

/-- Recurrence for the even rotational addition summands at the endpoint. -/
theorem evenTerm_recurrence (n : ℕ) :
    ((n:ℂ)+1)*evenTerm (n+1) = -((n:ℂ)+I)*evenTerm n := by
  have hupper : (2*n+1+2*I)*parabolicCylinderU (2*(n+1)-1/2+2*I) 0 =
      parabolicCylinderU (2*n-1/2+2*I) 0 := by
    convert parameter_step (2*n-1/2+2*I) using 1; congr 1 <;> ring_nf
  have hlower : parabolicCylinderU (-2*(n+1)-1/2) 0 =
      (-2*n-1)*parabolicCylinderU (-2*n-1/2) 0 := by
    convert (parameter_step (-2*(n+1)-1/2)).symm using 1; congr 1 <;> ring_nf
  have hd : (2*n+1+2*I:ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    norm_num at this
  have hupper' : parabolicCylinderU (2*(n+1)-1/2+2*I) 0 =
      parabolicCylinderU (2*n-1/2+2*I) 0/(2*n+1+2*I) := by
    apply (eq_div_iff hd).mpr
    simpa only [mul_comm] using hupper
  unfold evenTerm
  push_cast
  rw [hupper', hlower, show 2*(n+1)=2*n+1+1 by omega, pochhammer_succ,
    pochhammer_succ, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  have hn1 : (2*(n:ℂ)+1) ≠ 0 := by
    have hn := Nat.cast_nonneg (α := ℝ) n
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hn2 : (2*(n:ℂ)+2) ≠ 0 := by
    have hn := Nat.cast_nonneg (α := ℝ) n
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [show (2*(n:ℂ)+1+1) = 2*n+2 by ring]
  have hs : ((n:ℂ)+1)*(2*I+2*n)*(2*I+(2*n+1))*(-2*n-1) /
      ((2*n+2)*(2*n+1)*(2*n+1+2*I)) = -((n:ℂ)+I) := by
    apply (div_eq_iff (mul_ne_zero (mul_ne_zero hn2 hn1) hd)).mpr
    ring
  calc
    _ = (((n:ℂ)+1)*(2*I+2*n)*(2*I+(2*n+1))*(-2*n-1) /
        ((2*n+2)*(2*n+1)*(2*n+1+2*I))) *
        (pochhammer (2*I) (2*n)/((2*n).factorial:ℂ) *
          parabolicCylinderU (2*n-1/2+2*I) 0 * parabolicCylinderU (-2*n-1/2) 0) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [hs]

/-- A harmonic lower bound for the norms of the even endpoint terms. -/
theorem initial_norm_le (n : ℕ) :
    ‖parabolicCylinderU (-1/2+2*I) 0‖ ≤ (n+1:ℝ)*‖evenTerm (n+1)‖ := by
  have hnorm (k : ℕ) : ((k:ℝ)+1)*‖evenTerm (k+1)‖ = ‖(k:ℂ)+I‖*‖evenTerm k‖ := by
    have hc : ‖(k:ℂ)+1‖ = (k:ℝ)+1 := by
      rw [show (k:ℂ)+1 = ((k+1:ℕ):ℂ) by push_cast; rfl, Complex.norm_natCast]
      push_cast
      rfl
    have h := congrArg norm (evenTerm_recurrence k)
    simpa only [norm_mul, norm_neg, hc] using h
  induction n with
  | zero => simpa [evenTerm_zero] using (hnorm 0).ge
  | succ n ih =>
    have hle : (n+1:ℝ) ≤ ‖(n+1:ℕ)+I‖ := by
      simpa using Complex.re_le_norm (((n+1:ℕ):ℂ)+I)
    exact (ih.trans (mul_le_mul_of_nonneg_right hle (norm_nonneg _))).trans_eq
      (hnorm (n+1)).symm

/-- The even terms of the endpoint rotational addition formula are not summable. -/
theorem not_summable_evenTerm : ¬ Summable evenTerm := by
  intro h
  have hbound (n : ℕ) : ‖parabolicCylinderU (-1/2+2*I) 0‖*(n:ℝ)⁻¹ ≤ ‖evenTerm n‖ := by
    rcases n with _ | n
    · simp
    · rw [mul_inv_le_iff₀ (by positivity)]
      simpa only [mul_comm, Nat.cast_add, Nat.cast_one] using initial_norm_le n
  have hs : Summable (fun n : ℕ => ‖parabolicCylinderU (-1/2+2*I) 0‖*(n:ℝ)⁻¹) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hbound h.norm
  exact Real.not_summable_natCast_inv
    ((summable_mul_left_iff (norm_ne_zero_iff.mpr initial_ne_zero)).mp hs)

/-- The endpoint summands without their common cosine factor are not summable. -/
theorem not_summable_endpoint : ¬ Summable (fun m : ℕ =>
    (-1:ℂ)^m*pochhammer (2*I) m/(m.factorial:ℂ) *
      parabolicCylinderU (m-1/2+2*I) 0 * parabolicCylinderU (-m-1/2) 0) := by
  intro h
  apply not_summable_evenTerm
  have hi : Function.Injective (fun n : ℕ => 2*n) := fun n m h => by dsimp at h; omega
  have he := h.comp_injective hi
  refine he.congr fun n => ?_
  simp only [Function.comp_apply, evenTerm, pow_mul]
  norm_num

/-- The unordered `HasSum` version of rotational addition fails at
`a = -1/2+2i`, `x = y = 0` and `t = π/4`. -/
theorem not_hasSum_rotational_addition_endpoint : ¬ HasSum (fun m : ℕ =>
    (Real.cos (π/4):ℂ)^(-(-1/2+2*I)-1/2)*
      exp (((0:ℂ)*Real.sin (π/4)-0*Real.cos (π/4))^2/4)*(-1)^m*
      pochhammer ((-1/2+2*I)+1/2) m/(m.factorial:ℂ)*(Real.tan (π/4):ℂ)^m*
      parabolicCylinderU (m+(-1/2+2*I)) 0*parabolicCylinderU (-m-1/2) 0)
    (parabolicCylinderU (-1/2+2*I) 0) := by
  intro h
  have hc : (Real.cos (π/4):ℂ)^(-(-1/2+2*I)-1/2) ≠ 0 := by
    refine Complex.cpow_ne_zero_iff.mpr (Or.inl ?_)
    exact_mod_cast (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
      by linarith [Real.pi_pos]⟩).ne'
  apply not_summable_endpoint
  apply (summable_mul_left_iff hc).mp
  refine h.summable.congr fun m => ?_
  rw [show (-1/2+2*I:ℂ)+1/2=2*I by ring,
    show (m:ℂ)+(-1/2+2*I)=m-1/2+2*I by ring]
  simp only [zero_mul, sub_zero, zero_pow two_ne_zero, zero_div, Complex.exp_zero,
    Real.tan_pi_div_four, Complex.ofReal_one, one_pow, mul_one]
  ring

end RotationalAdditionEndpoint

end DLMF.Confluent
