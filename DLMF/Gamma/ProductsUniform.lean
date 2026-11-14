/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.Basic
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Local uniform convergence of gamma products

Andrews, Askey and Roy, *Special Functions*, Definition 1.1.1 and Theorem 1.1.2.
These strengthen the existing pointwise Euler and Weierstrass product limits with
the locally uniform convergence asserted by the book.
-/

@[expose] public section

open Filter

namespace DLMF.Gamma

/-- Euler's finite gamma quotients converge locally uniformly away from the poles.
Andrews–Askey–Roy, *Special Functions*, Definition 1.1.1, pp. 1–2
(synopsis AAR-1.1.1–1.1.5). -/
theorem tendstoLocallyUniformlyOn_GammaSeq :
    TendstoLocallyUniformlyOn (fun n z => Complex.GammaSeq z n) Complex.Gamma atTop
      {z : ℂ | ∀ n : ℕ, z ≠ -(n : ℂ)} := by
  sorry

/-- The reciprocal gamma Weierstrass products converge locally uniformly on the whole
complex plane, including the simple zeros. Andrews–Askey–Roy, *Special Functions*,
Theorem 1.1.2, p. 3 (synopsis AAR-1.1.1–1.1.5). -/
theorem tendstoLocallyUniformly_weierstrassGamma_prod :
    TendstoLocallyUniformly
      (fun n z => z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z) *
        ∏ k ∈ Finset.range n, weierstrassGammaTerm z k)
      (fun z => (Complex.Gamma z)⁻¹) atTop := by
  sorry

end DLMF.Gamma
