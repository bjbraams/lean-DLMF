/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Clausen
public import DLMF.GeneralizedHypergeometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# Hypergeometric series for the inverse hyperbolic sine

Duverney, *An Introduction to Hypergeometric Functions*, Appendix C,
equations (C.7)–(C.10), gives the real `arsinh` and its square as hypergeometric
functions, including the alternating reciprocal central-binomial expansion.
-/

@[expose] public noncomputable section

open Complex

namespace DLMF.Elementary

/-- The principal real inverse hyperbolic sine as a Gauss hypergeometric function.
Duverney Appendix C, (C.7), synopsis DU-C.02. -/
theorem arsinh_eq_ordinaryHypergeometric {x : ℝ} (hx : |x| < 1) :
    (Real.arsinh x : ℂ) = x * ordinaryHypergeometric (1 / 2 : ℂ) (1 / 2) (3 / 2)
      (-(x : ℂ) ^ 2) := by
  sorry

/-- The square of inverse hyperbolic sine as a generalized hypergeometric function.
Duverney Appendix C, (C.8), synopsis DU-C.02. -/
theorem arsinh_sq_eq_generalizedHypergeometric {x : ℝ} (hx : |x| < 1) :
    ((Real.arsinh x : ℂ) ^ 2) = (x : ℂ) ^ 2 *
      DLMF.Hypergeometric.generalizedHypergeometric {1, 1, 1} {2, 3 / 2}
        (-(x : ℂ) ^ 2) := by
  sorry

/-- The alternating central-binomial series of inverse-hyperbolic-sine squared.
Duverney Appendix C, (C.9)–(C.10), synopsis DU-C.02. -/
theorem hasSum_arsinh_sq {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n * (2 * x) ^ (2 * (n + 1)) /
      (2 * (n + 1 : ℝ) ^ 2 * ((2 * (n + 1)).choose (n + 1) : ℝ)))
      (Real.arsinh x ^ 2) := by
  sorry

end DLMF.Elementary
