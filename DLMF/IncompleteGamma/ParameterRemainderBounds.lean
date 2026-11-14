/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.RealIntegrals
public import DLMF.IncompleteGamma.UniformAsymptotics

/-!
# Real-parameter gamma remainder bounds and stable scaling

Temme, *Special Functions* (1996), Chapter 11, equations (11.9)–(11.12)
and (11.26)–(11.28), pages 279–280 and 286–288. The tail bound retains the
source's condition `z > max(0,a-N)`, allowing truncations before the terms decrease.
-/

@[expose] public noncomputable section

open Complex
open scoped Real

namespace DLMF.Confluent

/-- A gamma-tail majorant valid for every real shape once the argument exceeds it.
Temme (11.12), synopsis TEM-11-04. -/
theorem norm_upperIncompleteGamma_le_of_lt_argument {a z : ℝ}
    (hz : 0 < z) (haz : a < z) :
    ‖upperIncompleteGamma a z‖ ≤ z ^ a * _root_.Real.exp (-z) / (z - a) := by
  sorry

/-- The complete source-domain remainder bound after `N` integrations by parts.
Temme (11.11)–(11.12), synopsis TEM-11-04. -/
theorem norm_upperIncompleteGamma_remainder_le {a z : ℝ} (N : ℕ)
    (hz : 0 < z) (haz : a - N < z) :
    ‖(-1 : ℂ) ^ N * DLMF.Hypergeometric.pochhammer (1 - a) N *
      upperIncompleteGamma (a - N) z‖ ≤
        ‖DLMF.Hypergeometric.pochhammer (1 - a) N‖ *
          z ^ (a - N) * _root_.Real.exp (-z) / (z - a + N) := by
  sorry

/-- Stable gamma scaling separates the scaled gamma factor from the small exponent.
Temme (11.26)–(11.28), synopsis TEM-11-08. This is an exact identity.
-/
theorem gamma_density_scaled_identity {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    ((x ^ a * _root_.Real.exp (-x) / _root_.Real.Gamma (a + 1) : ℝ) : ℂ) =
      exp ((a : ℂ) * (_root_.Real.log (1 + (x - a) / a) - (x - a) / a)) /
        (_root_.Real.sqrt (2 * π * a) * gammaScaled a) := by
  sorry

end DLMF.Confluent
