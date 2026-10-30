/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Coordinate derivatives of jointly analytic functions

The coordinate partial derivatives of an analytic function on `ℂ × ℂ` are analytic and
its two mixed partial derivatives agree. The proofs express coordinate derivatives as
evaluations of Fréchet derivatives, then apply symmetry of the second Fréchet derivative.
-/

open Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace Complex

/-- A derivative along the first coordinate is evaluation of the Fréchet derivative at `(1, 0)`. -/
lemma deriv_fst_eq_fderiv {F : ℂ × ℂ → ℂ} {x y : ℂ}
    (hF : DifferentiableAt ℂ F (x, y)) :
    deriv (fun z => F (z, y)) x = fderiv ℂ F (x, y) (1, 0) := by
  exact (hF.hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))).deriv

/-- A derivative along the second coordinate is evaluation of the Fréchet derivative at `(0, 1)`. -/
lemma deriv_snd_eq_fderiv {F : ℂ × ℂ → ℂ} {x y : ℂ}
    (hF : DifferentiableAt ℂ F (x, y)) :
    deriv (fun z => F (x, z)) y = fderiv ℂ F (x, y) (0, 1) := by
  exact (hF.hasFDerivAt.comp_hasDerivAt y
    ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))).deriv

/-- The first coordinate partial derivative of a jointly analytic function is jointly analytic. -/
lemma analyticAt_deriv_fst {F : ℂ × ℂ → ℂ} {x y : ℂ}
    (hF : AnalyticAt ℂ F (x, y)) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => deriv (fun z => F (z, p.2)) p.1) (x, y) := by
  have hA := ((ContinuousLinearMap.apply ℂ ℂ (1, 0)).analyticAt
    (fderiv ℂ F (x, y))).comp hF.fderiv
  apply hA.congr
  filter_upwards [hF.eventually_analyticAt] with p hp
  rcases p with ⟨u, v⟩
  exact (deriv_fst_eq_fderiv hp.differentiableAt).symm

/-- The second coordinate partial derivative of a jointly analytic function is jointly analytic. -/
lemma analyticAt_deriv_snd {F : ℂ × ℂ → ℂ} {x y : ℂ}
    (hF : AnalyticAt ℂ F (x, y)) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => deriv (fun z => F (p.1, z)) p.2) (x, y) := by
  have hA := ((ContinuousLinearMap.apply ℂ ℂ (0, 1)).analyticAt
    (fderiv ℂ F (x, y))).comp hF.fderiv
  apply hA.congr
  filter_upwards [hF.eventually_analyticAt] with p hp
  rcases p with ⟨u, v⟩
  exact (deriv_snd_eq_fderiv hp.differentiableAt).symm

/-- Differentiating first in the second coordinate and then in the first evaluates the Hessian. -/
private lemma mixed_x_y_hessian {F : ℂ × ℂ → ℂ} {x y : ℂ}
    (hF : AnalyticAt ℂ F (x, y)) :
    deriv (fun z => deriv (fun w => F (z, w)) y) x =
      fderiv ℂ (fderiv ℂ F) (x, y) (1, 0) (0, 1) := by
  have he := (show Tendsto (fun z : ℂ => (z, y)) (𝓝 x) (𝓝 (x, y)) from
      tendsto_id.prodMk_nhds tendsto_const_nhds).eventually hF.eventually_analyticAt
  have heq : (fun z => deriv (fun w => F (z, w)) y) =ᶠ[𝓝 x]
      (fun z => fderiv ℂ F (z, y) (0, 1)) := by
    filter_upwards [he] with z hz using deriv_snd_eq_fderiv hz.differentiableAt
  rw [heq.deriv_eq]
  have hD := hF.fderiv.differentiableAt.hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))
  have hE := (ContinuousLinearMap.apply ℂ ℂ (0, 1)).hasFDerivAt.comp_hasDerivAt x hD
  exact hE.deriv

/-- Differentiating first in the first coordinate and then in the second evaluates the Hessian. -/
private lemma mixed_y_x_hessian {F : ℂ × ℂ → ℂ} {x y : ℂ}
    (hF : AnalyticAt ℂ F (x, y)) :
    deriv (fun w => deriv (fun z => F (z, w)) x) y =
      fderiv ℂ (fderiv ℂ F) (x, y) (0, 1) (1, 0) := by
  have he := (show Tendsto (fun w : ℂ => (x, w)) (𝓝 y) (𝓝 (x, y)) from
      tendsto_const_nhds.prodMk_nhds tendsto_id).eventually hF.eventually_analyticAt
  have heq : (fun w => deriv (fun z => F (z, w)) x) =ᶠ[𝓝 y]
      (fun w => fderiv ℂ F (x, w) (1, 0)) := by
    filter_upwards [he] with w hw using deriv_fst_eq_fderiv hw.differentiableAt
  rw [heq.deriv_eq]
  have hD := hF.fderiv.differentiableAt.hasFDerivAt.comp_hasDerivAt y
    ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))
  have hE := (ContinuousLinearMap.apply ℂ ℂ (1, 0)).hasFDerivAt.comp_hasDerivAt y hD
  exact hE.deriv

/-- The mixed coordinate partial derivatives of a jointly complex analytic function commute. -/
lemma deriv_snd_deriv_fst_comm {F : ℂ × ℂ → ℂ} {x y : ℂ}
    (hF : AnalyticAt ℂ F (x, y)) :
    deriv (fun w => deriv (fun z => F (z, w)) x) y =
      deriv (fun z => deriv (fun w => F (z, w)) y) x := by
  rw [mixed_y_x_hessian hF, mixed_x_y_hessian hF]
  exact (hF.contDiffAt (n := ⊤)).isSymmSndFDerivAt le_top |>.eq _ _

end Complex
