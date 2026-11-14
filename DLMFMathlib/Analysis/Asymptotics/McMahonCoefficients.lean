/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.AsymptoticInversion

/-!
# Fourth McMahon reversion coefficient

Olver, *Asymptotics and Special Functions*, Chapter 1, §8.4, p. 21,
synopsis O-1.14. The source uses `ζ = z + a₀ + a₁/z + ⋯` and
`z = ζ - b₀ - b₁/ζ - ⋯`; `mcMahonSeries` stores the negative coefficients.
-/

@[expose] public noncomputable section

open PowerSeries

namespace Asymptotics

/-- The fourth coefficient for inversion of `ζ = z + a₀ + a₁/z + ⋯`.
Olver, Chapter 1, §8.4, p. 21, synopsis O-1.14, with the source's forward sign. -/
theorem mcMahonSeries_coeff_three {K : Type*} [NormedField K] [CharZero K] (P : K⟦X⟧) :
    coeff 3 (mcMahonSeries P) = -(coeff 0 P ^ 2 * coeff 1 P + coeff 1 P ^ 2 +
      2 * coeff 0 P * coeff 2 P + coeff 3 P) := by
  sorry

end Asymptotics
