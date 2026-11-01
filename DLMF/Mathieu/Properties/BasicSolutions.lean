/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elementary.Trigonometric
public import DLMF.Mathieu.Basic.Properties
public import DLMF.Mathieu.SturmBridge
public import DLMF.Mathieu.SpectralExistence
public import DLMFMathlib.Analysis.Fourier.P1a2EntirePeriodic
public import DLMFMathlib.Analysis.ODE.Singularities
public import Mathlib.Analysis.Convex.Contractible
public import SeveralComplexVariables.SeparateAnalytic

/-!
# Joint analyticity of the basic Mathieu solutions

The basic solutions `w_I(z; a, q)`, `w_II(z; a, q)` of Mathieu's equation are entire functions
of `(z, a, q)` (DLMF §28.2(ii)).

## Main results

* `differentiable_mathieuWI_mathieuWII`: `w_I`, `w_II` are entire in `(z, a, q)`
  (DLMF §28.2(ii)).

## Implementation notes

The joint analyticity in `(z, a, q)` is obtained from holomorphic dependence on each parameter
separately (`differentiable_family_in_a`, `differentiable_family_in_q` in
`DLMF.Mathieu.Basic.Properties`) and Hartogs's theorem on separately holomorphic functions.
The other basic-solution results of §28.2 (symmetries, Wronskian, half-period relations) are in
`DLMF.Mathieu.Basic.Properties`.
-/

@[expose] public noncomputable section

open Complex Set Filter ComplexConjugate

open scoped Topology Real

namespace DLMF.Mathieu

/-- Hartogs for three variables on `ℂ × ℂ × ℂ`. -/
private lemma differentiable_of_separately₃ {f : ℂ × ℂ × ℂ → ℂ}
    (h1 : ∀ b c, Differentiable ℂ (fun x => f (x, b, c)))
    (h2 : ∀ x c, Differentiable ℂ (fun b => f (x, b, c)))
    (h3 : ∀ x b, Differentiable ℂ (fun c => f (x, b, c))) : Differentiable ℂ f := by
  let g : (Fin 3 → ℂ) → ℂ := fun v => f (v 0, v 1, v 2)
  have hg : AnalyticOnNhd ℂ g univ := by
    refine SeveralComplexVariables.analyticOnNhd_of_separately_analytic isOpen_univ ?_
    intro v _ i
    fin_cases i
    · have := (h1 (v 1) (v 2)).analyticAt (v 0)
      simpa [g, Function.update] using this
    · have := (h2 (v 0) (v 2)).analyticAt (v 1)
      simpa [g, Function.update] using this
    · have := (h3 (v 0) (v 1)).analyticAt (v 2)
      simpa [g, Function.update] using this
  have hL : Differentiable ℂ (fun p : ℂ × ℂ × ℂ => (![p.1, p.2.1, p.2.2] : Fin 3 → ℂ)) := by
    refine differentiable_pi.2 fun i => ?_
    fin_cases i <;> simp
  exact (differentiableOn_univ.1 hg.differentiableOn).comp hL

/-- **Analytic dependence** (DLMF §28.2(ii)): the solution with given initial values at a point
is an entire function of `z`, `a` and `q`; for the basic solutions, `(z, a, q) ↦ w_I(z; a, q)`
and `(z, a, q) ↦ w_II(z; a, q)` are entire on `ℂ³`. -/
@[dlmf 28.2.ii]
theorem differentiable_mathieuWI_mathieuWII :
    Differentiable ℂ (fun p : ℂ × ℂ × ℂ => mathieuWI p.2.1 p.2.2 p.1) ∧
      Differentiable ℂ (fun p : ℂ × ℂ × ℂ => mathieuWII p.2.1 p.2.2 p.1) := by
  have hI := differentiable_family_in_a (W := mathieuWI) isMathieuSolution_mathieuWI
    (fun a q => (mathieuWI_spec a q).2.1) (fun a q => (mathieuWI_spec a q).2.2)
  have hI' := differentiable_family_in_q (W := mathieuWI) isMathieuSolution_mathieuWI
    (fun a q => (mathieuWI_spec a q).2.1) (fun a q => (mathieuWI_spec a q).2.2)
  have hII := differentiable_family_in_a (W := mathieuWII) isMathieuSolution_mathieuWII
    (fun a q => (mathieuWII_spec a q).2.1) (fun a q => (mathieuWII_spec a q).2.2)
  have hII' := differentiable_family_in_q (W := mathieuWII) isMathieuSolution_mathieuWII
    (fun a q => (mathieuWII_spec a q).2.1) (fun a q => (mathieuWII_spec a q).2.2)
  exact ⟨differentiable_of_separately₃
      (fun a q => (isMathieuSolution_mathieuWI a q).differentiable)
      (fun z q => (hI q z).1) (fun z a => (hI' a z).1),
    differentiable_of_separately₃ (fun a q => (isMathieuSolution_mathieuWII a q).differentiable)
      (fun z q => (hII q z).1) (fun z a => (hII' a z).1)⟩

end DLMF.Mathieu
end
