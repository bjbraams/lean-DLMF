/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import DLMFMathlib.Analysis.Integral.ImproperDerivatives
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Distributional derivatives across a jump

Ordinary derivatives agree with distributional derivatives for `C¹` functions on the line.
Restricting a real function to `(a, ∞)` contributes the Dirac mass of weight `f(a)` at `a`.
Both identities follow from integration by parts against compactly supported test functions.
The test-function derivative identification uses TauCeti's
`TestFunction.lineDerivOp_one_apply_eq_deriv`.

* `Distribution.lineDerivOp_ofFun_of_contDiff`: the derivative of a regular distribution.
* `Distribution.lineDerivOp_ofFun_indicator_Ioi`: the endpoint jump of a half-line restriction.
* `Distribution.lineDerivOp_ofFun_piecewise`: the jump between two smooth pieces.
-/

public noncomputable section

open Set Filter MeasureTheory
open scoped Topology Distributions LineDeriv

namespace Distribution

/-- The distributional derivative of a `C¹` function equals its ordinary derivative.
The target may be any real normed vector space. -/
lemma lineDerivOp_ofFun_of_contDiff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} (hf : ContDiff ℝ 1 f) :
    ∂_{(1 : ℝ)} (ofFun ⊤ f volume ⊤) = ofFun ⊤ (deriv f) volume ⊤ := by
  ext φ
  rw [lineDerivOp_apply_apply, ofFun_apply (hf.continuous.locallyIntegrable.locallyIntegrableOn _),
    ofFun_apply ((hf.continuous_deriv le_rfl).locallyIntegrable.locallyIntegrableOn _)]
  simp only [FunLike.coe_neg, Pi.neg_apply, funext (TestFunction.lineDerivOp_one_apply_eq_deriv φ),
    neg_smul, integral_neg]
  have hφ : ContDiff ℝ 1 ⇑φ := φ.contDiff.of_le (by simp)
  have hi : Integrable (fun x => deriv ⇑φ x • f x) :=
    ((hφ.continuous_deriv le_rfl).smul hf.continuous).integrable_of_hasCompactSupport
      φ.hasCompactSupport.deriv.smul_right
  have hj : Integrable (fun x => φ x • deriv f x) :=
    (φ.continuous.smul (hf.continuous_deriv le_rfl)).integrable_of_hasCompactSupport
      φ.hasCompactSupport.smul_right
  have hprod : Integrable (fun x => φ x • f x) :=
    (φ.continuous.smul hf.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.smul_right
  have h := integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (L := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F))
    (fun x _ => (hφ.differentiable one_ne_zero x).hasDerivAt)
    (fun x _ => (hf.differentiable one_ne_zero x).hasDerivAt) hj hi hprod
  exact h.symm

/-- Restricting a `C¹` function to a right half-line adds its endpoint jump to the derivative. -/
lemma lineDerivOp_ofFun_indicator_Ioi {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (a : ℝ) :
    ∂_{(1 : ℝ)} (ofFun ⊤ ((Ioi a).indicator f) volume ⊤) =
      ofFun ⊤ ((Ioi a).indicator (deriv f)) volume ⊤ +
        f a • (delta a : 𝓓'((⊤ : TopologicalSpace.Opens ℝ), ℝ)) := by
  have hi : LocallyIntegrable ((Ioi a).indicator f) volume :=
    (hf.continuous.locallyIntegrable (μ := volume)).indicator measurableSet_Ioi
  have hj : LocallyIntegrable ((Ioi a).indicator (deriv f)) volume :=
    ((hf.continuous_deriv le_rfl).locallyIntegrable (μ := volume)).indicator
    measurableSet_Ioi
  ext φ
  rw [lineDerivOp_apply_apply, ofFun_apply (hi.locallyIntegrableOn _), add_apply,
    ofFun_apply (hj.locallyIntegrableOn _), smul_apply, delta_apply]
  simp only [FunLike.coe_neg, Pi.neg_apply,
    funext (TestFunction.lineDerivOp_one_apply_eq_deriv φ), smul_eq_mul,
    neg_mul, integral_neg]
  have he (g : ℝ → ℝ) (k : ℝ → ℝ) :
      (fun x => g x * (Ioi a).indicator k x) = (Ioi a).indicator (fun x => g x * k x) := by
    funext x
    by_cases hx : x ∈ Ioi a <;> simp [hx]
  rw [he, he, integral_indicator measurableSet_Ioi, integral_indicator measurableSet_Ioi]
  have h := integral_Ioi_deriv_mul_eq_of_hasCompactSupport hf
    (φ.contDiff.of_le (by simp)) φ.hasCompactSupport a
  linarith

/-- The derivative of two `C¹` pieces includes their jump as a Dirac mass. -/
lemma lineDerivOp_ofFun_piecewise {g h : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hh : ContDiff ℝ 1 h) (a : ℝ) :
    ∂_{(1 : ℝ)} (ofFun ⊤ (fun x => if a < x then g x else h x) volume ⊤) =
      ofFun ⊤ (fun x => if a < x then deriv g x else deriv h x) volume ⊤ +
        (g a - h a) • (delta a : 𝓓'((⊤ : TopologicalSpace.Opens ℝ), ℝ)) := by
  have he (u v : ℝ → ℝ) :
      (fun x => if a < x then u x else v x) = v + (Ioi a).indicator (u - v) := by
    funext x
    by_cases hx : a < x <;> simp [hx]
  have hli : LocallyIntegrable h volume := hh.continuous.locallyIntegrable
  have hlj : LocallyIntegrable ((Ioi a).indicator (g - h)) volume :=
    ((hg.sub hh).continuous.locallyIntegrable).indicator measurableSet_Ioi
  have hldi : LocallyIntegrable (deriv h) volume :=
    (hh.continuous_deriv le_rfl).locallyIntegrable
  have hldj : LocallyIntegrable ((Ioi a).indicator (deriv g - deriv h)) volume :=
    (((hg.continuous_deriv le_rfl).sub (hh.continuous_deriv le_rfl)).locallyIntegrable).indicator
      measurableSet_Ioi
  rw [he, ofFun_add (hli.locallyIntegrableOn _) (hlj.locallyIntegrableOn _),
    LineDeriv.lineDerivOp_add, lineDerivOp_ofFun_of_contDiff hh,
    lineDerivOp_ofFun_indicator_Ioi (f := g - h) (hg.sub hh) a, he,
    ofFun_add (hldi.locallyIntegrableOn _) (hldj.locallyIntegrableOn _)]
  have hd : deriv (g - h) = deriv g - deriv h := by
    funext x
    exact deriv_sub (hg.differentiable one_ne_zero x)
      (hh.differentiable one_ne_zero x)
  rw [hd, add_assoc]
  rfl

end Distribution
