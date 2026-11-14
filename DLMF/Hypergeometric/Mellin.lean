/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic.PrincipalBranch
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Mellin integral of the Gauss hypergeometric function

Temme, *Special Functions* (1996), Chapter 5, §5.6, pp. 119–121,
synopsis TEM-05-08. Euler's integral supplies an absolutely convergent representation
on the initial parameter domain. The regularized Gauss function uses its principal continuation
on the negative real axis, not a totalized power series beyond the unit disc.
-/

@[expose] public noncomputable section
open Complex MeasureTheory Set
namespace DLMF.Hypergeometric

/-- The Mellin transform of the principal regularized Gauss function on the negative real ray,
Temme Chapter 5, §5.6, synopsis TEM-05-08. The four real-part hypotheses are
the initial absolute-convergence domain of the Euler-integral derivation. -/
theorem integrableOn_and_integral_cpow_mul_regularizedGaussHypergeometric_neg
    {a b c s : ℂ} (hs : 0 < s.re) (has : 0 < (a - s).re)
    (hbs : 0 < (b - s).re) (hcb : 0 < (c - b).re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) *
      regularizedGaussHypergeometric a b c (-(t : ℂ))) (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) *
      regularizedGaussHypergeometric a b c (-(t : ℂ))) =
      Gamma s * Gamma (a - s) * Gamma (b - s) /
        (Gamma a * Gamma b * Gamma (c - s)) := by
  sorry

end DLMF.Hypergeometric
