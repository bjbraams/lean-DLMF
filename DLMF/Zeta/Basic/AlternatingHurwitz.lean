/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Basic.Polylog

/-!
# Real alternating Hurwitz zeta and Dirichlet beta

The canonical Lerch continuation defines these real functions even in the range of
conditional ordered convergence. Duverney, *An Introduction to Hypergeometric Functions*,
Chapter 2, equations (2.81) and (2.86).
-/

@[expose] public noncomputable section

namespace DLMF.Zeta.Real

/-- The real alternating Hurwitz zeta is the real part of the principal Lerch
continuation at `z = -1`. Its ordered alternating series converges for `s,a > 0`.
Duverney (2.81), synopsis DU-2.20. -/
def alternatingHurwitzZeta (s a : ℝ) : ℝ :=
  (lerchPhi (-1) s a).re

/-- The defining Lerch boundary value. Duverney (2.81), DU-2.20 and Appendix A. -/
theorem alternatingHurwitzZeta_def (s a : ℝ) :
    alternatingHurwitzZeta s a = (lerchPhi (-1) s a).re := rfl

/-- Dirichlet beta as a scaled real Lerch value. This agrees with the ordered
alternating odd-denominator series for `s > 0`. Duverney (2.86), synopsis DU-2.21. -/
def dirichletBeta (s : ℝ) : ℝ :=
  (2 : ℝ) ^ (-s) * alternatingHurwitzZeta s (1 / 2)

/-- The defining alternating Hurwitz value of beta. Duverney (2.86), DU-2.21. -/
theorem dirichletBeta_def (s : ℝ) :
    dirichletBeta s = (2 : ℝ) ^ (-s) * alternatingHurwitzZeta s (1 / 2) := rfl

end DLMF.Zeta.Real
