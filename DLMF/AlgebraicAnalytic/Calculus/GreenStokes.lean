/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.Analysis.Green.IndexOne
public import DLMF.AlgebraicAnalytic.Calculus.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Green's theorem in the plane and Stokes's theorem (DLMF 1.6.43–1.6.44, 1.6.57)

Green's theorem 1.6.44 is TauCeti's `TauCeti.Green.green_ac_index_one` (credited in the
pointer file `DLMF.AlgebraicAnalytic.Calculus.MathlibCoverage`): the plane is `ℂ`, the curve
`γ` is closed and absolutely continuous on `[a, b]`, and the region `S` is the part of the
filled hull of the trace off the trace, on which the winding number of `γ` is `1`. This
covers DLMF's positively oriented simple closed piecewise differentiable curves (whose
interior has winding number `1` by the Jordan curve theorem, not in Mathlib), and more: the
curve may cross itself. This file proves the area formulas below 1.6.44 from it, and states
Stokes's theorem 1.6.57 for a parametrized surface over such a region.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology Matrix

namespace DLMF.AlgebraicAnalytic

/-- Green's theorem for a field with constant curl `1` gives the area of the region. -/
lemma g1b_green_area {γ : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hindex : ∀ z ∈ TauCeti.filledHull (γ '' uIcc a b) \ (γ '' uIcc a b),
      TauCeti.Contour.windingNumber γ a b z = 1)
    {P Q : ℂ → ℝ} (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q)
    (hcurl : ∀ z, TauCeti.Green.curl P Q z = 1) :
    volume.real (TauCeti.filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)) =
      ∫ t in a..b, (P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im) := by
  obtain ⟨-, -, h⟩ := TauCeti.Green.green_ac_index_one hab hγ hclosed isOpen_univ
    (subset_univ _) hP.contDiffOn hQ.contDiffOn hindex
  simp only [TauCeti.Green.circulationFun, hcurl] at h
  rw [h, setIntegral_const, smul_eq_mul, mul_one]

/-- DLMF §1.6(iv), after 1.6.44: the area of the region `S` bounded by `γ` (winding number `1`
on `S`) is `∫_C -y dx = ∫_C x dy = ½ ∫_C (x dy - y dx)`. -/
@[dlmf 1.6.iv]
theorem volume_real_eq_green_area {γ : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hindex : ∀ z ∈ TauCeti.filledHull (γ '' uIcc a b) \ (γ '' uIcc a b),
      TauCeti.Contour.windingNumber γ a b z = 1) :
    let A := volume.real (TauCeti.filledHull (γ '' uIcc a b) \ (γ '' uIcc a b))
    A = ∫ t in a..b, -(γ t).im * (deriv γ t).re ∧
      A = ∫ t in a..b, (γ t).re * (deriv γ t).im ∧
      A = ∫ t in a..b, (-(γ t).im / 2 * (deriv γ t).re + (γ t).re / 2 * (deriv γ t).im) := by
  intro A
  have hre (z : ℂ) : HasFDerivAt (fun z : ℂ => z.re) Complex.reCLM z :=
    Complex.reCLM.hasFDerivAt
  have him (z : ℂ) : HasFDerivAt (fun z : ℂ => z.im) Complex.imCLM z :=
    Complex.imCLM.hasFDerivAt
  have cre : ContDiff ℝ 1 (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have cim : ContDiff ℝ 1 (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  have hn (z : ℂ) : HasFDerivAt (fun z : ℂ => -z.im) (-Complex.imCLM) z := (him z).neg
  have h0 (z : ℂ) : HasFDerivAt (fun _ : ℂ => (0 : ℝ)) (0 : ℂ →L[ℝ] ℝ) z := hasFDerivAt_const _ _
  have hn2 (z : ℂ) : HasFDerivAt (fun z : ℂ => -z.im / 2) ((2 : ℝ)⁻¹ • -Complex.imCLM) z := by
    simp only [div_eq_mul_inv]; exact (hn z).mul_const _
  have hr2 (z : ℂ) : HasFDerivAt (fun z : ℂ => z.re / 2) ((2 : ℝ)⁻¹ • Complex.reCLM) z := by
    simp only [div_eq_mul_inv]; exact (hre z).mul_const _
  refine ⟨?_, ?_, ?_⟩
  · have h := g1b_green_area hab hγ hclosed hindex (P := fun z => -z.im) (Q := fun _ => 0)
      cim.neg contDiff_const (fun z => by
        rw [TauCeti.Green.curl, (hn z).fderiv, (h0 z).fderiv]; simp)
    simpa using h
  · have h := g1b_green_area hab hγ hclosed hindex (P := fun _ => 0) (Q := fun z => z.re)
      contDiff_const cre (fun z => by
        rw [TauCeti.Green.curl, (hre z).fderiv, (h0 z).fderiv]; simp)
    simpa using h
  · have h := g1b_green_area hab hγ hclosed hindex (P := fun z => -z.im / 2)
      (Q := fun z => z.re / 2) (cim.neg.div_const 2) (cre.div_const 2) (fun z => by
        rw [TauCeti.Green.curl, (hn2 z).fderiv, (hr2 z).fderiv]; simp; norm_num)
    exact h

/-- DLMF 1.6.57 (Stokes's theorem) for a parametrized surface: let the parameter region
`D ⊆ ℝ²` be the region bounded by the closed absolutely continuous curve `γ` in the
`(u, v)`-plane (identified with `ℂ`; winding number `1` on `D`, i.e. `∂D` positively
oriented), `Φ` of class `C²` on `ℝ²`, and `F` of class `C¹`. Then, with `S = Φ(D)` oriented by
`T_u × T_v` and `∂S = Φ ∘ γ` (anticlockwise relative to that normal),
`∬_S (∇ × F) · dS = ∫_{∂S} F · ds`. -/
@[dlmf 1.6.E57]
theorem fluxIntegral_curl_eq_lineIntegral {γ : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hindex : ∀ z ∈ TauCeti.filledHull (γ '' uIcc a b) \ (γ '' uIcc a b),
      TauCeti.Contour.windingNumber γ a b z = 1)
    {Φ : ℝ × ℝ → Fin 3 → ℝ} (hΦ : ContDiff ℝ 2 Φ)
    {F : (Fin 3 → ℝ) → Fin 3 → ℝ} (hF : ContDiff ℝ 1 F) :
    fluxIntegral (curl F) Φ
        (Complex.equivRealProd '' (TauCeti.filledHull (γ '' uIcc a b) \ (γ '' uIcc a b))) =
      lineIntegral F (fun t => Φ (Complex.equivRealProd (γ t))) a b := by
  sorry

end DLMF.AlgebraicAnalytic
