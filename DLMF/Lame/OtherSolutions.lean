/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Lame.Polynomials.Defs

/-!
# Lamé functions: second solutions (DLMF §29.17(i))

If Lamé's equation 29.2.1 has a Lamé polynomial solution `E` (eigenvalue
`h = ½(H_m + ν(ν+1)k²)`, 29.15.7 and analogues), a second solution is
`F(z) = E(z) ∫_{iK'}^z du/E(u)²` (29.17.1). The base point `iK'` is a pole of `sn`, hence of
`E` (of order `ν`), where `1/E²` has a zero; the integral is taken along the segment from `iK'`
to `z`, parametrized as `∫₀¹ (z - iK')/E(iK' + s(z - iK'))² ds` (the integrand at `s = 0`, a
single point, does not affect the integral). The statement is local: on an open set `U` such
that the segments from `iK'` to points of `U` meet no zero of `E` and no pole of `sn` other than
their initial point. The Wronskian `E F' - E' F` equals `1`, so `F` is independent of `E`.
§29.17(ii) (algebraic Lamé functions) and §29.17(iii) (Lamé–Wangerin functions) are
descriptive with references only and are not acquired. Admitted.
-/

@[expose] public section

open Complex DLMF.JacobiElliptic DLMF.Elliptic Set
open scoped Real

noncomputable section

namespace DLMF.Lame

variable {k : ℝ}

/-- 29.17.1: `F(z) = E(z) ∫_{iK'}^z du/E(u)²` is a second solution of Lamé's equation with
`E F' - E' F = 1`, `E = lamePolyEk t n m · k`, `ν = t.order n`, `h = ½(H_m + ν(ν+1)k²)`.
Admitted. -/
@[dlmf 29.17.E1]
theorem lamePolyEk_second_solution (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolyType)
    {n m : ℕ} (hm : m ≤ n) {U : Set ℂ} (hU : IsOpen U)
    (hseg : ∀ z ∈ U, ∀ s ∈ Ioc (0 : ℝ) 1,
      let u := I * Real.compEllIntKm (1 - k ^ 2) + s * (z - I * Real.compEllIntKm (1 - k ^ 2))
      lamePolyEk t n m u k ≠ 0 ∧ ∀ p q : ℤ,
        u ≠ 2 * p * Real.compEllIntKm (k ^ 2) + (2 * q + 1) * I * Real.compEllIntKm (1 - k ^ 2)) :
    IsLameSolutionOn ((lamePolyH t n m k + t.order n * (t.order n + 1) * k ^ 2) / 2)
        (t.order n) k
        (fun z => lamePolyEk t n m z k * ∫ s in (0 : ℝ)..1,
          (z - I * Real.compEllIntKm (1 - k ^ 2)) /
            lamePolyEk t n m (I * Real.compEllIntKm (1 - k ^ 2) +
              s * (z - I * Real.compEllIntKm (1 - k ^ 2))) k ^ 2) U ∧
      ∀ z ∈ U, lamePolyEk t n m z k * deriv (fun z => lamePolyEk t n m z k * ∫ s in (0 : ℝ)..1,
          (z - I * Real.compEllIntKm (1 - k ^ 2)) /
            lamePolyEk t n m (I * Real.compEllIntKm (1 - k ^ 2) +
              s * (z - I * Real.compEllIntKm (1 - k ^ 2))) k ^ 2) z -
        deriv (fun z => lamePolyEk t n m z k) z * (lamePolyEk t n m z k * ∫ s in (0 : ℝ)..1,
          (z - I * Real.compEllIntKm (1 - k ^ 2)) /
            lamePolyEk t n m (I * Real.compEllIntKm (1 - k ^ 2) +
              s * (z - I * Real.compEllIntKm (1 - k ^ 2))) k ^ 2) = 1 := by
  sorry

end DLMF.Lame
