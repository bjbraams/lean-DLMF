/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
/-!
# Derivatives of improper tail integrals

An integrable function on a half-line has an improper tail integral. At an interior
continuity point its derivative is minus the integrand, by TauCeti's
`MeasureTheory.IntegrableOn.hasDerivAt_integral_Ioi`. The endpoint continuity result
below extends that API to the closed half-line. Integration by parts against compactly
supported test functions also retains the finite endpoint term.
-/

public section

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {f : ℝ → E} {a x : ℝ}
/-- An improper tail integral is continuous from within its closed half-line. -/
theorem IntegrableOn.continuousWithinAt_integral_Ioi (hf : IntegrableOn f (Ioi a))
    (hax : a ≤ x) (hfm : StronglyMeasurableAtFilter f (𝓝 x)) (hfx : ContinuousAt f x) :
    ContinuousWithinAt (fun y => ∫ t in Ioi y, f t) (Ici a) x := by
  have hi : IntervalIntegrable f volume a x := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hax]
    exact hf.mono_set Ioc_subset_Ioi_self
  have hc : ContinuousWithinAt
      (fun y => (∫ t in Ioi a, f t) - ∫ t in a..y, f t) (Ici a) x :=
    ((hasDerivAt_const x (∫ t in Ioi a, f t)).sub
    (intervalIntegral.integral_hasDerivAt_right hi hfm hfx)).continuousAt.continuousWithinAt
  apply hc.congr
  · intro y hy
    rw [eq_sub_iff_add_eq, add_comm]
    exact (sub_eq_iff_eq_add.mp (intervalIntegral.integral_Ioi_sub_Ioi hf hy)).symm
  · rw [eq_sub_iff_add_eq, add_comm]
    exact (sub_eq_iff_eq_add.mp (intervalIntegral.integral_Ioi_sub_Ioi hf hax)).symm

/-- Integration by parts against a compactly supported `C¹` function on a half-line.
The identity holds in any Banach algebra over the real numbers. -/
lemma integral_Ioi_deriv_mul_eq_of_hasCompactSupport
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] {f φ : ℝ → A}
    (hf : ContDiff ℝ 1 f) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (a : ℝ) :
    (∫ x in Ioi a, deriv φ x * f x) = -φ a * f a - ∫ x in Ioi a, φ x * deriv f x := by
  have hi : Integrable (fun x => deriv φ x * f x) :=
    ((hφ.continuous_deriv le_rfl).mul hf.continuous).integrable_of_hasCompactSupport
      hc.deriv.mul_right
  have hj : Integrable (fun x => φ x * deriv f x) :=
    (hφ.continuous.mul (hf.continuous_deriv le_rfl)).integrable_of_hasCompactSupport hc.mul_right
  have hd : deriv (fun x => φ x * f x) = fun x => deriv φ x * f x + φ x * deriv f x := by
    funext x
    exact deriv_mul (hφ.differentiable one_ne_zero x) (hf.differentiable one_ne_zero x)
  have hv := HasCompactSupport.integral_Ioi_deriv_eq (hφ.mul hf) hc.mul_right a
  rw [hd, integral_add hi.integrableOn hj.integrableOn] at hv
  apply (eq_sub_iff_add_eq).mpr
  simpa only [neg_mul] using hv

end MeasureTheory
