/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Basic.Polylog
public import DLMF.GeneralizedHypergeometric.Basic

/-!
# Polylogarithms as generalized hypergeometric series

Andrews, Askey and Roy, *Special Functions*, §2.6, pp. 102–107
(synopsis AAR-2.6.1–2.6.3). Canonical continued polylogarithms agree with their
hypergeometric power series on the complete complex unit disk.
-/

@[expose] public section

namespace DLMF.Zeta

/-- A nonnegative integer-order polylogarithm is a generalized hypergeometric series
on the complex unit disk. Andrews–Askey–Roy, *Special Functions*, §2.6,
pp. 102–107 (synopsis AAR-2.6.1–2.6.3). At order two this is the `3F2`
dilogarithm representation; order zero is included. -/
theorem polylog_natCast_eq_generalizedHypergeometric {z : ℂ} (hz : ‖z‖ < 1) (n : ℕ) :
    polylog (n : ℂ) z = z *
      DLMF.Hypergeometric.generalizedHypergeometric
        (Multiset.replicate (n + 1) (1 : ℂ)) (Multiset.replicate n (2 : ℂ)) z := by
  sorry

end DLMF.Zeta
