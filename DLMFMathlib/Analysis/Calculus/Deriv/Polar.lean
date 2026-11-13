/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Calculus.Deriv.CompCurve
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Second derivatives in polar coordinates

The sum of second derivatives along two fixed vectors is expressed using radial and angular
curves in their span. The vectors need not be orthogonal or linearly independent.
-/

public section

open Filter
open scoped Topology

/-- The second derivative trace along two vectors equals the radial second derivative,
the radial first derivative divided by the radius, and the angular second derivative divided
by the squared radius. The radius is nonzero and may have either sign. -/
theorem ContDiffAt.secondFDeriv_polar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {v w : E} {r θ : ℝ} (hr : r ≠ 0)
    (hf : ContDiffAt ℝ 2 f (r • (Real.cos θ • v + Real.sin θ • w))) :
    fderiv ℝ (fderiv ℝ f) (r • (Real.cos θ • v + Real.sin θ • w)) v v +
        fderiv ℝ (fderiv ℝ f) (r • (Real.cos θ • v + Real.sin θ • w)) w w =
      deriv (deriv fun t : ℝ => f (t • (Real.cos θ • v + Real.sin θ • w))) r +
        deriv (fun t : ℝ => f (t • (Real.cos θ • v + Real.sin θ • w))) r / r +
        deriv (deriv fun t : ℝ => f (r • (Real.cos t • v + Real.sin t • w))) θ / r ^ 2 := by
  have hR (t : ℝ) : HasDerivAt (fun t : ℝ => t • (Real.cos θ • v + Real.sin θ • w))
      (Real.cos θ • v + Real.sin θ • w) t := by
    simpa using (hasDerivAt_id t).smul_const (Real.cos θ • v + Real.sin θ • w)
  have hRR := hf.deriv_comp_curve (c := fun t : ℝ => t •
    (Real.cos θ • v + Real.sin θ • w))
    (c' := fun _ => Real.cos θ • v + Real.sin θ • w) (c'' := (0 : E))
    (Eventually.of_forall hR) (hasDerivAt_const r (Real.cos θ • v + Real.sin θ • w))
  have hA (t : ℝ) : HasDerivAt (fun t : ℝ => r • (Real.cos t • v + Real.sin t • w))
      (r • (-Real.sin t • v + Real.cos t • w)) t := by
    exact (((Real.hasDerivAt_cos t).smul_const v).add
      ((Real.hasDerivAt_sin t).smul_const w)).const_smul r
  have hAA' : HasDerivAt (fun t : ℝ => r • (-Real.sin t • v + Real.cos t • w))
      (r • (-Real.cos θ • v + -Real.sin θ • w)) θ := by
    exact ((((Real.hasDerivAt_sin θ).neg).smul_const v).add
      ((Real.hasDerivAt_cos θ).smul_const w)).const_smul r
  have hAA := hf.deriv_comp_curve (c := fun t : ℝ =>
    r • (Real.cos t • v + Real.sin t • w))
    (c' := fun t => r • (-Real.sin t • v + Real.cos t • w))
    (Eventually.of_forall hA) hAA'
  rw [hRR.1, hRR.2, hAA.2]
  simp only [map_zero, add_zero]
  set L := fderiv ℝ f (r • (Real.cos θ • v + Real.sin θ • w))
  set S := fderiv ℝ (fderiv ℝ f) (r • (Real.cos θ • v + Real.sin θ • w))
  have hcs := Real.cos_sq_add_sin_sq θ
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  field_simp [hr]
  linear_combination -r * (S v v + S w w) * hcs
