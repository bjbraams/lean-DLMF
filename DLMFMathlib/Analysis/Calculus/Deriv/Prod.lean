/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
import DLMFMathlib.Analysis.Calculus.Deriv.CompCurve
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
/-!
# Coordinate derivatives on a product

For a differentiable map on `𝕜 × 𝕜`, the coordinate derivatives are evaluations of its
Fréchet derivative on `(1,0)` and `(0,1)`. Under `C²` regularity, the second coordinate
partials similarly evaluate the second Fréchet derivative. The target may be any normed
space over the nontrivially normed scalar field.

The diagonal identities specialize `ContDiffAt.deriv_comp_curve` to affine coordinate
lines. The mixed identities differentiate the first coordinate formulas locally.

## Main results

* `DifferentiableAt.hasDerivAt_section_fst`, `DifferentiableAt.hasDerivAt_section_snd`:
  derivatives along coordinate lines.
* `ContDiffAt.deriv_deriv_section_fst`, `ContDiffAt.deriv_deriv_section_snd`:
  repeated coordinate derivatives.
* `ContDiffAt.deriv_deriv_section_snd_fst`, `ContDiffAt.deriv_deriv_section_fst_snd`:
  mixed coordinate derivatives, without exchanging their order.
-/

public noncomputable section
open Filter
open scoped Topology
variable {𝕜 G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
/-- The first coordinate section has derivative `Df(p)(1,0)`. -/
theorem DifferentiableAt.hasDerivAt_section_fst {f : 𝕜 × 𝕜 → G} {p : 𝕜 × 𝕜}
    (hf : DifferentiableAt 𝕜 f p) :
    HasDerivAt (fun t => f (t, p.2)) (fderiv 𝕜 f p (1, 0)) p.1 := by
  have h := (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  have hh := hf.hasFDerivAt.comp_hasDerivAt (x := p.1) (by simpa using h)
  simpa only [Function.comp_def] using hh
/-- The second coordinate section has derivative `Df(p)(0,1)`. -/
theorem DifferentiableAt.hasDerivAt_section_snd {f : 𝕜 × 𝕜 → G} {p : 𝕜 × 𝕜}
    (hf : DifferentiableAt 𝕜 f p) :
    HasDerivAt (fun t => f (p.1, t)) (fderiv 𝕜 f p (0, 1)) p.2 := by
  have h := (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have hh := hf.hasFDerivAt.comp_hasDerivAt (x := p.2) (by simpa using h)
  simpa only [Function.comp_def] using hh
/-- The repeated first-coordinate derivative evaluates `D²f` on `(1,0)` twice. -/
theorem ContDiffAt.deriv_deriv_section_fst {f : 𝕜 × 𝕜 → G} {a b : 𝕜}
    (hf : ContDiffAt 𝕜 2 f (a, b)) :
    deriv (fun s => deriv (fun t => f (t, b)) s) a =
      fderiv 𝕜 (fderiv 𝕜 f) (a, b) (1, 0) (1, 0) := by
  have h := hf.deriv_comp_curve (c := fun t => (t, b)) (c' := fun _ => (1, 0))
    (c'' := (0 : 𝕜 × 𝕜)) (τ := a)
    (Eventually.of_forall fun t => (hasDerivAt_id t).prodMk (hasDerivAt_const t b))
    (hasDerivAt_const a (1, 0))
  simpa only [map_zero, add_zero] using h.2
/-- The repeated second-coordinate derivative evaluates `D²f` on `(0,1)` twice. -/
theorem ContDiffAt.deriv_deriv_section_snd {f : 𝕜 × 𝕜 → G} {a b : 𝕜}
    (hf : ContDiffAt 𝕜 2 f (a, b)) :
    deriv (fun s => deriv (fun t => f (a, t)) s) b =
      fderiv 𝕜 (fderiv 𝕜 f) (a, b) (0, 1) (0, 1) := by
  have h := hf.deriv_comp_curve (c := fun t => (a, t)) (c' := fun _ => (0, 1))
    (c'' := (0 : 𝕜 × 𝕜)) (τ := b)
    (Eventually.of_forall fun t => (hasDerivAt_const t a).prodMk (hasDerivAt_id t))
    (hasDerivAt_const b (0, 1))
  simpa only [map_zero, add_zero] using h.2
/-- Differentiating the first-coordinate derivative in the second coordinate evaluates `D²f`. -/
theorem ContDiffAt.deriv_deriv_section_snd_fst {f : 𝕜 × 𝕜 → G} {a b : 𝕜}
    (hf : ContDiffAt 𝕜 2 f (a, b)) :
    deriv (fun s => deriv (fun t => f (t, s)) a) b =
      fderiv 𝕜 (fderiv 𝕜 f) (a, b) (0, 1) (1, 0) := by
  have hev : ∀ᶠ q in 𝓝 (a, b), DifferentiableAt 𝕜 f q :=
    (hf.eventually (by simp)).mono fun q hq => hq.differentiableAt (by norm_num)
  have hd : DifferentiableAt 𝕜 (fderiv 𝕜 f) (a, b) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : (fun s => deriv (fun t => f (t, s)) a) =ᶠ[𝓝 b]
      (fun s => fderiv 𝕜 f (a, s) (1, 0)) := by
    have hc : ContinuousAt (fun s : 𝕜 => (a, s)) b := by fun_prop
    have he := hc.eventually (by simpa using hev)
    filter_upwards [he] with s hs using (hs.hasDerivAt_section_fst (p := (a, s))).deriv
  rw [heq.deriv_eq]
  have heval : DifferentiableAt 𝕜 (fun q : 𝕜 × 𝕜 => fderiv 𝕜 f q (1, 0)) (a, b) :=
    hd.clm_apply (differentiableAt_const _)
  have h := heval.hasDerivAt_section_snd
  rw [h.deriv, fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [fderiv_const_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, zero_apply, map_zero, zero_add]
/-- Differentiating the second-coordinate derivative in the first coordinate evaluates `D²f`. -/
theorem ContDiffAt.deriv_deriv_section_fst_snd {f : 𝕜 × 𝕜 → G} {a b : 𝕜}
    (hf : ContDiffAt 𝕜 2 f (a, b)) :
    deriv (fun s => deriv (fun t => f (s, t)) b) a =
      fderiv 𝕜 (fderiv 𝕜 f) (a, b) (1, 0) (0, 1) := by
  have hev : ∀ᶠ q in 𝓝 (a, b), DifferentiableAt 𝕜 f q :=
    (hf.eventually (by simp)).mono fun q hq => hq.differentiableAt (by norm_num)
  have hd : DifferentiableAt 𝕜 (fderiv 𝕜 f) (a, b) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : (fun s => deriv (fun t => f (s, t)) b) =ᶠ[𝓝 a]
      (fun s => fderiv 𝕜 f (s, b) (0, 1)) := by
    have hc : ContinuousAt (fun s : 𝕜 => (s, b)) a := by fun_prop
    have he := hc.eventually (by simpa using hev)
    filter_upwards [he] with s hs using (hs.hasDerivAt_section_snd (p := (s, b))).deriv
  rw [heq.deriv_eq]
  have heval : DifferentiableAt 𝕜 (fun q : 𝕜 × 𝕜 => fderiv 𝕜 f q (0, 1)) (a, b) :=
    hd.clm_apply (differentiableAt_const _)
  have h := heval.hasDerivAt_section_fst
  rw [h.deriv, fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [fderiv_const_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, zero_apply, map_zero, zero_add]
