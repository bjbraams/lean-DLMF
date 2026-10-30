/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic.GaussCoefficients
public import Mathlib.Data.Nat.Choose.Cast

/-!
# Defining coefficients and series for Appell F4
-/

@[expose] public noncomputable section

open Complex Filter Set Polynomial
open scoped Real Nat Topology ENNReal Interval

namespace DLMF.Hypergeometric

/-- The coefficients of Appell's `F₄`:
`(a)_{m+n} (b)_{m+n} / ((c)_m (c')_n m! n!)`. -/
noncomputable def appF4Coeff (a b c c' : ℂ) (m n : ℕ) : ℂ :=
  poch a (m + n) * poch b (m + n) / (poch c m * poch c' n * (m ! * n !))

/-- The summand of the coefficient comparison in Bailey's formula. -/
noncomputable def appF4Term (a b c c' : ℂ) (M N m n : ℕ) : ℂ :=
  appF4Coeff a b c c' m n * ((-1) ^ (M - m) * (n.choose (M - m) : ℂ)) *
    ((-1) ^ (N - n) * (m.choose (N - n) : ℂ))

/-- The coefficient of `X^M` in `X^m (1 - X)^n`. -/
noncomputable def appF4E (m n M : ℕ) : ℂ :=
  if m ≤ M then (-1) ^ (M - m) * (n.choose (M - m) : ℂ) else 0

/-- The four-index family behind Bailey's formula. -/
noncomputable def appF4Fam (a b c c' X Y : ℂ) (p : (ℕ × ℕ) × (ℕ × ℕ)) : ℂ :=
  appF4Coeff a b c c' p.1.1 p.1.2 * (appF4E p.1.1 p.1.2 p.2.1 * X ^ p.2.1) *
    (appF4E p.1.2 p.1.1 p.2.2 * Y ^ p.2.2)

/-- **Appell's function `F₄`** (DLMF 16.13.4), as the sum of its double series
`∑ (a)_{m+n}(b)_{m+n}/((c)_m(c')_n m! n!) sᵐ tⁿ` (totalized to `0` where it diverges). -/
@[dlmf 16.13.E4]
noncomputable def appF4 (a b c c' s t : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ, appF4Coeff a b c c' p.1 p.2 * s ^ p.1 * t ^ p.2

end DLMF.Hypergeometric
