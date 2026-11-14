/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Calculus.ProlateCoordinates
public import DLMF.Spheroidal.Basic

/-!
# Prolate spheroidal separation of Helmholtz's equation

The radial and angular equations use the same algebraic expression on their
respective domains, with the prolate sign of the spectral term. Source:
Kristensson, *Second Order Differential Equations*, Chapter 8, §8.6,
pp. 159–161.
-/

@[expose] public noncomputable section

open Complex EuclideanSpace Set
open scoped Real

namespace DLMF.WaveEquation

/-- A separated prolate mode solves Helmholtz's equation in the regular chart.
The angular constant is `Lambda`, so its spectral term is
`Lambda-c^2*k^2*eta^2`; this differs from the oblate sign.
Kristensson, Chapter 8, §8.6, pp. 159–161. -/
theorem helmholtz_prolate_product (R S : ℝ → ℂ) (m : ℤ)
    (separationConstant k c : ℝ) (hc : 0 < c) (q : EuclideanSpace ℝ (Fin 3))
    (hxi : 1 < q 0) (heta : q 1 ∈ Ioo (-1 : ℝ) 1)
    (hR : ContDiffAt ℝ 2 R (q 0)) (hS : ContDiffAt ℝ 2 S (q 1))
    (hRode : ((q 0) ^ 2 - 1 : ℝ) * iteratedDeriv 2 R (q 0) +
      (2 * q 0 : ℝ) * deriv R (q 0) +
      (c ^ 2 * k ^ 2 * (q 0) ^ 2 - separationConstant -
        (m : ℝ) ^ 2 / ((q 0) ^ 2 - 1) : ℝ) * R (q 0) = 0)
    (hSode : (1 - (q 1) ^ 2 : ℝ) * iteratedDeriv 2 S (q 1) -
      (2 * q 1 : ℝ) * deriv S (q 1) +
      (separationConstant - c ^ 2 * k ^ 2 * (q 1) ^ 2 -
        (m : ℝ) ^ 2 / (1 - (q 1) ^ 2) : ℝ) * S (q 1) = 0) :
    let U := fun p : EuclideanSpace ℝ (Fin 3) => R (p 0) * S (p 1) * exp (I * m * p 2)
    orthogonalLaplacian (fun j p => if j = 0 then
      c * Real.sqrt (((p 0) ^ 2 - (p 1) ^ 2) / ((p 0) ^ 2 - 1)) else if j = 1 then
      c * Real.sqrt (((p 0) ^ 2 - (p 1) ^ 2) / (1 - (p 1) ^ 2)) else
      c * Real.sqrt (((p 0) ^ 2 - 1) * (1 - (p 1) ^ 2))) U q + k ^ 2 * U q = 0 := by
  sorry

end DLMF.WaveEquation
