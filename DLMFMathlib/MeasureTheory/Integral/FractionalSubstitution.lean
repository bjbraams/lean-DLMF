/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# A fractional substitution between a half-line and a bounded interval

The map `u ↦ u/(1+u)` identifies `(0,∞)` with `(0,1)`. Its positive Jacobian is
`1/(1+u)^2`, giving a change-of-variables formula for real normed-space valued integrals.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped Topology
namespace MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- The substitution `t = u/(1+u)` maps the positive half-line onto the open unit interval. -/
theorem integral_comp_div_one_add_Ioi (g : ℝ → E) :
    (∫ u : ℝ in Ioi 0, (1/(1+u)^2) • g (u/(1+u))) = ∫ t : ℝ in Ioo 0 1, g t := by
  have him : (fun u : ℝ => u/(1+u)) '' Ioi 0 = Ioo 0 1 := by
    ext t
    constructor
    · rintro ⟨u,hu,rfl⟩
      have hu : 0 < u := hu
      exact ⟨div_pos hu (by linarith), (div_lt_one (by linarith)).mpr (by linarith)⟩
    · intro ht
      refine ⟨t/(1-t), div_pos ht.1 (by linarith [ht.2]), ?_⟩
      field_simp [(sub_pos.mpr ht.2).ne']
      ring
  have hd (u : ℝ) (hu : u ∈ Ioi 0) :
      HasDerivWithinAt (fun u : ℝ => u/(1+u)) (1/(1+u)^2) (Ioi 0) u := by
    have hu : 0 < u := hu
    have h := (hasDerivAt_id u).div ((hasDerivAt_id u).const_add 1)
      (by change 1+u ≠ 0; linarith)
    simpa only [id_eq, one_mul, mul_one, add_sub_cancel_right] using! h.hasDerivWithinAt
  have hinj : InjOn (fun u : ℝ => u/(1+u)) (Ioi 0) := by
    intro u hu v hv h
    have hu : 0 < u := hu
    have hv : 0 < v := hv
    rw [div_eq_div_iff (by linarith) (by linarith)] at h
    linarith
  symm
  rw [← him]
  simpa only [abs_div, abs_one, abs_sq] using
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hinj g
end MeasureTheory
