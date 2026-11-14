/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Haar transfer from uniformly convergent improper Fourier tails

Olver, *Asymptotics and Special Functions*, Chapter 8, §11,
pp. 316–320, synopsis O-8.15. This boundary-function formulation needs no
holomorphic extension across the contour. Positive and negative tails are kept
separate, as in the source's uniform convergence hypothesis.
-/

@[expose] public noncomputable section
open Filter Asymptotics
open scoped Topology
namespace Complex

/-- Uniform ordinary Fourier-tail convergence for each derivative gives Haar's
full inverse-power decay. Olver, Chapter 8, §11, pp. 316–320. Applying this
boundary theorem to `(F-G)(r+i*y)` and multiplying by `exp(r*t)/(2*pi)` yields
the source inverse-Laplace transfer after the assumed contour deformation. -/
theorem isLittleO_sum_improper_fourier_limits
    {H : ℝ → ℂ} {m : ℕ} (hH : ContDiff ℝ m H)
    {T : ℝ} {Lplus Lminus : ℕ → ℝ → ℂ}
    (hplus : ∀ j ≤ m, TendstoUniformlyOn
      (fun R t : ℝ => ∫ y in (0 : ℝ)..R,
        exp (I * t * y) * iteratedDeriv j H y) (Lplus j) atTop (Set.Ici T))
    (hminus : ∀ j ≤ m, TendstoUniformlyOn
      (fun R t : ℝ => ∫ y in -R..(0 : ℝ),
        exp (I * t * y) * iteratedDeriv j H y) (Lminus j) atTop (Set.Ici T)) :
    (fun t : ℝ => Lplus 0 t + Lminus 0 t) =o[atTop]
      (fun t : ℝ => t ^ (-(m : ℝ))) := by
  sorry

end Complex
