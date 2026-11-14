/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.Stirling.DefinitionsAndSeries
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Complex exponential generating functions for Stirling numbers

Temme, *Special Functions* (1996), §1.4, (1.30)–(1.31), p. 20.
The logarithm is principal on the disc `‖z‖ < 1`; the second-kind series is entire.
-/

@[expose] public noncomputable section
open Complex
namespace DLMF.Combinatorics

/-- The complex first-kind exponential generating series, Temme (1.30),
synopsis TEM-01-16. -/
theorem hasSum_signedStirlingFirst_complex (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (signedStirlingFirst n m : ℂ) * z ^ n / n.factorial)
      (log (1 + z) ^ m / m.factorial) := by
  sorry

/-- The entire second-kind exponential generating series, Temme (1.31),
synopsis TEM-01-16. -/
theorem hasSum_stirlingSecond_complex (m : ℕ) (z : ℂ) :
    HasSum (fun n : ℕ => (n.stirlingSecond m : ℂ) * z ^ n / n.factorial)
      ((exp z - 1) ^ m / m.factorial) := by
  sorry

end DLMF.Combinatorics
