/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.LegendreAddition

/-!
# The singular integral of a Legendre polynomial

The quotient `(P_n(x)-P_n(t))/|x-t|` is interval integrable: on either side
of `t=x` it agrees with a continuous divided slope up to sign. The Mathlib
contributors’ `dslope` continuity and interval-integral congruence theorems
justify the split without changing the totalized diagonal value.

The degree recurrence reduces the integral to a signed Legendre integral.
The derivative ladders supply its primitive, and the resulting recurrence
has eigenvalue twice the finite harmonic sum (DLMF 18.17.44).
-/

@[expose] public section

open Complex Polynomial Filter Set MeasureTheory
open scoped Nat Topology
open DLMF.Hypergeometric
noncomputable section

namespace DLMF.OrthogonalPolynomials.LegendreSingular
/-- The signed kernel of the split singular integral. -/
def signKernel (x t : ℝ) : ℂ := (x-t : ℝ) / (|x-t| : ℝ)
/-- The divided difference with its totalized diagonal value. -/
def dq (n : ℕ) (x t : ℝ) : ℂ :=
  (legendrePolyP n x-legendrePolyP n t) / (|x-t| : ℝ)
/-- The divided difference extends continuously on either side of the diagonal. -/
theorem continuous_dslope (n : ℕ) (x : ℝ) :
    Continuous (dslope (fun t : ℝ => legendrePolyP n t) x) := by
  have hd (t : ℝ) : DifferentiableAt ℝ (fun t : ℝ => legendrePolyP n t) t :=
    ((LegendreAddition.diff_jet n 0 t).hasDerivAt.comp_ofReal).differentiableAt
  apply continuous_iff_continuousAt.2
  intro t
  by_cases h : t=x
  · subst t; exact continuousAt_dslope_same.2 (hd x)
  · exact (continuousAt_dslope_of_ne h).2 (hd t).continuousAt
/-- The left-hand divided difference is the continuous divided slope. -/
theorem dq_eq_dslope {x t : ℝ} (h : t < x) (n : ℕ) :
    dq n x t = dslope (fun t : ℝ => legendrePolyP n t) x t := by
  rw [dq, dslope_of_ne _ h.ne, slope_def_module, real_smul, abs_of_pos (sub_pos.mpr h)]
  push_cast
  rw [show (t : ℂ)-x = -((x : ℂ)-t) by ring, inv_neg]
  ring
/-- The right-hand divided difference has the opposite sign. -/
theorem dq_eq_neg_dslope {x t : ℝ} (h : x < t) (n : ℕ) :
    dq n x t = -dslope (fun t : ℝ => legendrePolyP n t) x t := by
  rw [dq, dslope_of_ne _ h.ne', slope_def_module, real_smul, abs_of_neg (sub_neg.mpr h)]
  push_cast
  ring
/-- Integrability on both sides of the diagonal. -/
theorem dq_integrable (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1) 1) :
    IntervalIntegrable (dq n x) volume (-1) x ∧ IntervalIntegrable (dq n x) volume x 1 := by
  constructor
  · apply ((continuous_dslope n x).intervalIntegrable (-1) x).congr_uIoo
    intro t ht
    rw [uIoo_of_lt hx.1] at ht
    exact (dq_eq_dslope ht.2 n).symm
  · apply ((continuous_dslope n x).neg.intervalIntegrable x 1).congr_uIoo
    intro t ht
    rw [uIoo_of_lt hx.2] at ht
    exact (dq_eq_neg_dslope ht.1 n).symm
/-- The signed kernel on the left interval. -/
theorem signKernel_of_lt {x t : ℝ} (h : t < x) : signKernel x t = 1 := by
  rw [signKernel, abs_of_pos (sub_pos.mpr h)]
  exact div_self (ofReal_ne_zero.mpr (sub_pos.mpr h).ne')
/-- The signed kernel on the right interval. -/
theorem signKernel_of_gt {x t : ℝ} (h : x < t) : signKernel x t = -1 := by
  rw [signKernel, abs_of_neg (sub_neg.mpr h)]
  have hne : ((x-t : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (sub_neg.mpr h).ne
  rw [ofReal_neg, div_neg, div_self hne]
/-- Integrability of a signed continuous function. -/
theorem signed_integrable {f : ℝ → ℂ} (hf : Continuous f) {x : ℝ} (hx : x ∈ Ioo (-1) 1) :
    IntervalIntegrable (fun t => signKernel x t*f t) volume (-1) x ∧
    IntervalIntegrable (fun t => signKernel x t*f t) volume x 1 := by
  constructor
  · apply (hf.intervalIntegrable (-1) x).congr_uIoo
    intro t ht
    rw [uIoo_of_lt hx.1] at ht
    dsimp only
    rw [signKernel_of_lt ht.2, one_mul]
  · apply (hf.neg.intervalIntegrable x 1).congr_uIoo
    intro t ht
    rw [uIoo_of_lt hx.2] at ht
    dsimp only
    rw [signKernel_of_gt ht.1, neg_one_mul]
    rfl
/-- Splitting the signed integral at its sign change. -/
theorem integral_signed {f : ℝ → ℂ} (hf : Continuous f) {x : ℝ} (hx : x ∈ Ioo (-1) 1) :
    (∫ t : ℝ in (-1)..1, signKernel x t*f t) =
      (∫ t : ℝ in (-1)..x, f t) - ∫ t : ℝ in x..1, f t := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (signed_integrable hf hx).1 (signed_integrable hf hx).2]
  have hL : (∫ t : ℝ in (-1)..x, signKernel x t*f t) = ∫ t : ℝ in (-1)..x, f t := by
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    rw [uIoo_of_lt hx.1] at ht
    dsimp only
    rw [signKernel_of_lt ht.2, one_mul]
  have hR : (∫ t : ℝ in x..1, signKernel x t*f t) = -(∫ t : ℝ in x..1, f t) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    rw [uIoo_of_lt hx.2] at ht
    dsimp only
    rw [signKernel_of_gt ht.1, neg_one_mul]
  rw [hL, hR]
  ring
end DLMF.OrthogonalPolynomials.LegendreSingular
namespace DLMF.OrthogonalPolynomials.LegendreSingular
/-- Legendre endpoint values. -/
theorem endpoints (n : ℕ) : legendrePolyP n 1 = 1 ∧ legendrePolyP n (-1) = (-1)^n := by
  have h1 : legendrePolyP n 1 = 1 := by
    rw [legendrePolyP, jacobiPolyP_one ]
    simp [Nat.cast_ne_zero.mpr n.factorial_ne_zero]
  refine ⟨h1, ?_⟩
  change jacobiPolyP 0 0 n (-1) = _
  rw [jacobi_reflection (by norm_num) (by norm_num), ← legendrePolyP, h1, mul_one]

/-- A primitive of a positive-degree Legendre polynomial. -/
def primitive (n : ℕ) (t : ℝ) : ℂ :=
  (legendrePolyP (n+2) t-legendrePolyP n t)/(2*n+3)
/-- Its endpoint values vanish. -/
theorem primitive_endpoints (n : ℕ) : primitive n (-1) = 0 ∧ primitive n 1 = 0 := by
  simp [primitive, (endpoints _).1, (endpoints _).2, pow_add]
/-- The derivative of the primitive. -/
theorem hasDerivAt_primitive (n : ℕ) (t : ℝ) :
    HasDerivAt (primitive n) (legendrePolyP (n+1) t) t := by
  have h1 := (LegendreAddition.hderiv_jet (n+2) 0 t).comp_ofReal
  have h0 := (LegendreAddition.hderiv_jet n 0 t).comp_ofReal
  have hh := (h1.sub h0).div_const (2*n+3 : ℂ)
  change HasDerivAt (primitive n)
    ((LegendreAddition.jet (n+2) 1 t-LegendreAddition.jet n 1 t)/(2*n+3)) t at hh
  apply hh.congr_deriv
  have hr := LegendreAddition.jet_raise (n+1) 0 t
  have hl := LegendreAddition.jet_lower n 0 t
  rw [LegendreAddition.jet_zero] at hr hl
  have hn : (2*n+3 : ℂ) ≠ 0 := by exact_mod_cast (show 2*n+3 ≠ 0 by omega)
  field_simp
  push_cast at hr hl
  linear_combination hr-hl
/-- A signed Legendre integral, evaluated by its primitive. -/
theorem integral_signed_legendre (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1) 1) :
    (∫ t : ℝ in (-1)..1, signKernel x t*legendrePolyP (n+1) t) =
      2*(legendrePolyP (n+2) x-legendrePolyP n x)/(2*n+3) := by
  have hc : Continuous (fun t : ℝ => legendrePolyP (n+1) t) :=
    (LegendreAddition.diff_jet (n+1) 0).continuous.comp continuous_ofReal
  rw [integral_signed hc hx,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_primitive n t) (hc.intervalIntegrable _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_primitive n t) (hc.intervalIntegrable _ _),
    (primitive_endpoints n).1, (primitive_endpoints n).2, primitive]
  ring

/-- The recurrence for the divided differences. -/
theorem dq_recurrence (n : ℕ) (x t : ℝ) :
    (n+2)*dq (n+2) x t =
      (2*n+3)*((x : ℂ)*dq (n+1) x t + signKernel x t*legendrePolyP (n+1) t) - (n+1)*dq n x t := by
  have hx := legendrePolyP_recurrence n (x : ℂ)
  have ht := legendrePolyP_recurrence n (t : ℂ)
  dsimp only [dq, signKernel]
  push_cast
  linear_combination (((|x-t| : ℝ) : ℂ))⁻¹ * (hx-ht)

/-- Finite harmonic sums in the normalization of the stated singular integral. -/
def harmonicSum (n : ℕ) : ℂ := ∑ k ∈ Finset.range n, (k+1 : ℂ)⁻¹
/-- Adding the next reciprocal to the finite harmonic sum. -/
theorem harmonicSum_succ (n : ℕ) : harmonicSum (n+1) = harmonicSum n+(n+1 : ℂ)⁻¹ := by
  exact Finset.sum_range_succ _ _
/-- The singular integral of a Legendre polynomial. -/
theorem singular_integral (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1) 1) :
    (∫ t : ℝ in (-1)..1, dq n x t) = 2*harmonicSum n*legendrePolyP n x := by
  have hI (k : ℕ) := (dq_integrable k hx).1.trans (dq_integrable k hx).2
  have hC (k : ℕ) : Continuous (fun t : ℝ => legendrePolyP k t) :=
    (LegendreAddition.diff_jet k 0).continuous.comp continuous_ofReal
  induction n using Nat.twoStepInduction with
  | zero => simp [dq, legendrePolyP_zero, harmonicSum]
  | one =>
    have he : dq 1 x = fun t => signKernel x t * (1 : ℂ) := by
      funext t
      simp only [dq, legendrePolyP_one, signKernel, mul_one]
      push_cast
      rfl
    rw [he, integral_signed continuous_const hx]
    norm_num [harmonicSum, legendrePolyP_one]
    ring
  | more n ih0 ih1 =>
    have hS := (signed_integrable (hC (n+1)) hx).1.trans (signed_integrable (hC (n+1)) hx).2
    have hr : (n+2)*(∫ t : ℝ in (-1)..1, dq (n+2) x t) =
        (2*n+3)*((x : ℂ)*(∫ t : ℝ in (-1)..1, dq (n+1) x t) +
          (∫ t : ℝ in (-1)..1, signKernel x t*legendrePolyP (n+1) t)) -
            (n+1)*(∫ t : ℝ in (-1)..1, dq n x t) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add ((hI (n+1)).const_mul _) hS,
        ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub (((hI (n+1)).const_mul _ |>.add hS).const_mul _) ((hI n).const_mul _)]
      apply intervalIntegral.integral_congr
      intro t _
      exact dq_recurrence n x t
    rw [ih0, ih1, integral_signed_legendre n hx] at hr
    have hp := legendrePolyP_recurrence n (x : ℂ)
    have hn : (n+2 : ℂ) ≠ 0 := by exact_mod_cast (show n+2 ≠ 0 by omega)
    have hn1 : (n+1 : ℂ) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    have hn3 : (2*n+3 : ℂ) ≠ 0 := by exact_mod_cast (show 2*n+3 ≠ 0 by omega)
    apply mul_left_cancel₀ hn
    rw [harmonicSum_succ] at hr
    rw [harmonicSum_succ, harmonicSum_succ]
    push_cast
    simp only [show ∀ z : ℂ, z+1+1 = z+2 by intro z; ring]
    linear_combination (norm := ring_nf) hr - (2*(harmonicSum n+(n+1 : ℂ)⁻¹))*hp
    have hna : (1+(n : ℂ)) ≠ 0 := by convert hn1 using 1; ring
    have hnb : (2+(n : ℂ)) ≠ 0 := by convert hn using 1; ring
    have hnc : (3+(n : ℂ)*2) ≠ 0 := by convert hn3 using 1; ring
    field_simp [hna, hnb, hnc]
    ring
end DLMF.OrthogonalPolynomials.LegendreSingular
