/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Struve.Asymptotics

/-!
# Debye polynomials in the Anger–Weber coefficient formula (DLMF §11.11(iii))

## Main definitions

* `angerDebyePoly`: the Debye polynomials, with their primitive normalized to vanish at zero.

## Main results

* `angerScaledB_debye`: the unnumbered general coefficient formula of DLMF §11.11(iii), with
  the Debye normalization of DLMF §10.41(ii).
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Struve

open Polynomial

/-- Debye polynomials, with their primitive normalized to vanish at zero. -/
def angerDebyePoly : ℕ → Polynomial ℂ
  | 0 => 1
  | k+1 => C (1/2)*X^2*(1-X^2)*derivative (angerDebyePoly k) +
      C (1/8)*((1-C 5*X^2)*angerDebyePoly k).sum (fun n a => C (a/(n+1))*X^(n+1))

/-- Unnumbered general coefficient formula in DLMF 11.11(iii), with the Debye normalization from
10.41(ii). -/
theorem angerScaledB_debye {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) (k : ℕ) :
    pochhammer (1/2) k*angerScaledB lam k=(-1)^k/(1-lam^2:ℂ)^(1/4:ℂ)*(angerDebyePoly k).eval
        (1/(1-lam^2:ℂ)^(1/2:ℂ)) := by
  sorry

end DLMF.Struve
