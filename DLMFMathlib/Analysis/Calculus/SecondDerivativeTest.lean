/-
Copyright (c) 2025 Yury G. Kudryashov. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, The Tau Ceti contributors, Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import TauCeti.Analysis.Calculus.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.Order.Compact

/-!
# Second-order remainders and the minimum test

A `C²` map between real normed spaces has a quadratic Taylor expansion with remainder
`o(‖h‖²)`. At a critical point this proves the minimum test when the second derivative is
coercive, or positive definite on a finite-dimensional domain.

The mean-value argument adapts Mathlib's
`sub_isBigO_norm_rpow_add_one_of_fderiv` to an arbitrary small constant. The quadratic
remainder proof adapts TauCeti's `isBigO_sub_taylor_two_of_hasFDerivAt`, using
only differentiability of the first derivative at the center. No completeness of the
target is required. Compactness of the unit sphere gives the finite-dimensional bound.

## Main results

* `sub_isLittleO_norm_rpow_add_one_of_fderiv`: integrate a small derivative estimate.
* `ContDiffAt.isLittleO_sub_taylor_two`: the quadratic Peano remainder under `C²` regularity.
* `ContDiffAt.isLocalMin_of_fderiv_eq_zero_of_le_secondFDeriv`: the coercive minimum test.
* `ContDiffAt.isLocalMin_of_fderiv_eq_zero_of_pos_secondFDeriv`: its finite-dimensional form.
-/

public noncomputable section

open Filter Asymptotics Metric Set
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- If a derivative is `o(‖x-a‖^r)` for `r ≥ 0`, the function increment is
`o(‖x-a‖^(r+1))`. -/
theorem sub_isLittleO_norm_rpow_add_one_of_fderiv {f : E → F} {a : E} {r : ℝ} (hr : 0 ≤ r)
    (hdf : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f x)
    (hderiv : fderiv ℝ f =o[𝓝 a] (fun x => ‖x - a‖ ^ r)) :
    (fun x => f x - f a) =o[𝓝 a] (fun x => ‖x - a‖ ^ (r + 1)) := by
  rw [isLittleO_iff]
  intro C hC
  have hd := hderiv.def hC
  obtain ⟨ε, hε₀, hε⟩ := eventually_nhds_iff_ball.mp (hdf.and hd)
  rw [eventually_nhds_iff_ball]
  refine ⟨ε, hε₀, fun y hy => ?_⟩
  rw [Real.norm_of_nonneg (by positivity), Real.rpow_add_one' (by positivity) (by positivity),
    ← mul_assoc]
  have hsub : closedBall a ‖y - a‖ ⊆ ball a ε :=
    closedBall_subset_ball (mem_ball_iff_norm.mp hy)
  apply (convex_closedBall a ‖y - a‖).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
  · exact fun z hz => (hε z (hsub hz)).1
  · intro z hz
    grw [(hε z (hsub hz)).2, Real.norm_of_nonneg (by positivity),
      mem_closedBall_iff_norm.mp hz]
  · simp
  · simp [dist_eq_norm_sub]

/-- A `C²` map has its second-order Taylor expansion with Peano remainder. -/
theorem ContDiffAt.isLittleO_sub_taylor_two {f : E → F} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    (fun y => f y - f x - fderiv ℝ f x (y - x) -
      (2⁻¹ : ℝ) • fderiv ℝ (fderiv ℝ f) x (y - x) (y - x)) =o[𝓝 x]
        (fun y => ‖y - x‖ ^ 2) := by
  have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 f y := hf.eventually (by simp)
  have hdf : ∀ᶠ y in 𝓝 x, HasFDerivAt f (fderiv ℝ f y) y :=
    hev.mono fun y hy => (hy.differentiableAt (by norm_num)).hasFDerivAt
  have hdf' : ∀ᶠ y in 𝓝 x, HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) y) y :=
    hev.mono fun y hy =>
      ((hy.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  let S := fderiv ℝ (fderiv ℝ f) x
  have hsymm : ∀ v w, S v w = S w v :=
    second_derivative_symmetric_of_eventually hdf hdf'.self_of_nhds
  let q : E → E →L[ℝ] F := fun y => fderiv ℝ f y - fderiv ℝ f x - S (y - x)
  let g : E → F := fun y => f y - f x - fderiv ℝ f x (y - x) -
    (2⁻¹ : ℝ) • S (y - x) (y - x)
  have hg' : ∀ᶠ y in 𝓝 x, HasFDerivAt g (q y) y := by
    filter_upwards [hdf] with y hy
    have hQ : HasFDerivAt (fun y => (2⁻¹ : ℝ) • S (y - x) (y - x)) (S (y - x)) y := by
      refine (((S.hasFDerivAt_apply_self (y - x)).comp y
        ((hasFDerivAt_id y).sub_const x)).const_smul (2⁻¹ : ℝ)).congr_fderiv
          (ContinuousLinearMap.ext fun v => ?_)
      simp only [smul_apply, ContinuousLinearMap.comp_apply, add_apply,
        ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply, hsymm v (y - x)]
      module
    exact (((hy.sub_const (f x)).sub
      ((fderiv ℝ f x).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const x))).sub hQ).congr_fderiv
        (by ext v; simp [q])
  have hq : q =o[𝓝 x] (fun y => ‖y - x‖ ^ (1 : ℝ)) := by
    have h := hdf'.self_of_nhds.isLittleO.norm_right
    simpa only [q, S, Real.rpow_one] using h
  have hsmall : fderiv ℝ g =o[𝓝 x] (fun y => ‖y - x‖ ^ (1 : ℝ)) :=
    hq.congr' (hg'.mono fun y hy => hy.fderiv.symm) EventuallyEq.rfl
  have hzero : g x = 0 := by simp [g]
  have h := sub_isLittleO_norm_rpow_add_one_of_fderiv (r := 1) zero_le_one
    (hg'.mono fun y hy => hy.differentiableAt) hsmall
  simpa only [hzero, sub_zero, show (1 : ℝ) + 1 = 2 by norm_num, Real.rpow_two] using h

/-- A critical point with a coercive second derivative is a local minimum. -/
theorem ContDiffAt.isLocalMin_of_fderiv_eq_zero_of_le_secondFDeriv
    {f : E → ℝ} {x : E} {c : ℝ} (hf : ContDiffAt ℝ 2 f x)
    (hx : fderiv ℝ f x = 0) (hc : 0 < c)
    (hQ : ∀ v, c * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v) : IsLocalMin f x := by
  filter_upwards [hf.isLittleO_sub_taylor_two.def (show 0 < c / 4 by positivity)] with y hy
  have hq := hQ (y - x)
  simp only [hx, zero_apply, sub_zero, smul_eq_mul,
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖y - x‖)] at hy
  have he := neg_abs_le (f y - f x - (2⁻¹ : ℝ) * fderiv ℝ (fderiv ℝ f) x (y - x) (y - x))
  nlinarith [mul_nonneg hc.le (sq_nonneg ‖y - x‖)]

/-- In finite dimensions, a critical point with positive definite second derivative
is a local minimum. -/
theorem ContDiffAt.isLocalMin_of_fderiv_eq_zero_of_pos_secondFDeriv [FiniteDimensional ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hx : fderiv ℝ f x = 0)
    (hQ : ∀ v : E, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ f) x v v) : IsLocalMin f x := by
  rcases subsingleton_or_nontrivial E with h | h
  · let _ : Subsingleton E := h
    exact Eventually.of_forall fun y => by rw [Subsingleton.elim y x]
  let _ : Nontrivial E := h
  let Q : E → ℝ := fun v => fderiv ℝ (fderiv ℝ f) x v v
  obtain ⟨v, hv, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr (zero_le_one : (0 : ℝ) ≤ 1))
    ((by fun_prop : Continuous Q).continuousOn)
  have hvnorm : ‖v‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hv
  have hv0 : v ≠ 0 := by
    intro hzero
    simp only [hzero, norm_zero, zero_ne_one] at hvnorm
  have hc : 0 < Q v := hQ v hv0
  refine hf.isLocalMin_of_fderiv_eq_zero_of_le_secondFDeriv hx hc ?_
  intro w
  by_cases hw : w = 0
  · subst w
    simp
  have hnorm : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hws : ‖w‖⁻¹ • w ∈ sphere (0 : E) 1 := by
    simp only [mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg w), inv_mul_cancel₀ hnorm]
  have hs : Q v ≤ Q (‖w‖⁻¹ • w) := hmin hws
  dsimp only [Q] at hs ⊢
  simp only [map_smul, smul_apply, smul_eq_mul] at hs
  have hmul := mul_le_mul_of_nonneg_left hs (sq_nonneg ‖w‖)
  field_simp [hnorm] at hmul
  nlinarith [hmul]
