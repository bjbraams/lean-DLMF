/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Modified.Basic.Functions

public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-!
# Defining data for large-argument and Goldstein Mathieu expansions
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Topology Real Classical

namespace DLMF.Mathieu

/-! ### Coefficients of the expansion for large `Re z` (§28.25) -/

/-- The pair `(D_{m-1}, D_m)` of the recurrence 28.25.3 with sign `σ = ±1`. -/
def modMathieuAsympDPair (σ a h : ℂ) : ℕ → ℂ × ℂ
  | 0 => (0, 1)
  | m + 1 =>
    let p := modMathieuAsympDPair σ a h m
    (p.2, -((((m : ℂ) + 1 / 2) ^ 2 + σ * ((m : ℂ) + 1 / 4) * (8 * I * h) + 2 * h ^ 2 - a) *
      p.2 + σ * ((m : ℂ) - 1 / 2) * (8 * I * h * m) * p.1) / ((m : ℂ) + 1))

/-- The coefficients `D^±_m` of DLMF 28.25.1, defined by 28.25.2 (`D_{-1} = 0`, `D_0 = 1`) and
the recurrence 28.25.3; `σ = 1` gives `D^+_m` (for `M^{(3)}_ν`), `σ = -1` gives `D^-_m` (for
`M^{(4)}_ν`); `a = λ_ν(h²)`. -/
@[dlmf 28.25.E2, dlmf 28.25.E3]
def modMathieuAsympD (σ a h : ℂ) (m : ℕ) : ℂ :=
  (modMathieuAsympDPair σ a h m).2

/-- The prefactor `e^{±i(2h cosh z - (ν/2 + 1/4)π)} / (π h (cosh z + 1))^{1/2}` of DLMF 28.25.1,
`σ = ±1`; the square root is continued in `z` as `(2πh)^{1/2} cosh(z/2)`. -/
def modMathieuAsympPrefactor (σ ν h z : ℂ) : ℂ :=
  Complex.exp (σ * I * (2 * h * Complex.cosh z - (ν / 2 + 1 / 4) * π)) /
    ((2 * π * h) ^ (1 / 2 : ℂ) * Complex.cosh (z / 2))

/-- The sector filter of DLMF 28.25.4–28.25.5: `Re z → +∞` with
`a ≤ ph h + Im z ≤ b`. -/
def modMathieuAsympFilter (h : ℂ) (a b : ℝ) : Filter ℂ :=
  comap Complex.re atTop ⊓ 𝓟 {z : ℂ | a ≤ Complex.arg h + z.im ∧ Complex.arg h + z.im ≤ b}

/-! ### Goldstein's functions (§28.26(i)) -/

/-- The phase `φ = 2h sinh z - (m + 1/2) arctan(sinh z)` of DLMF 28.26.3 (principal complex
`arctan`, which is analytic for `Re z > 0`, `|Im z| < π/2`). -/
@[dlmf 28.26.E3]
def goldsteinPhase (m : ℕ) (z : ℂ) (h : ℝ) : ℂ :=
  2 * h * Complex.sinh z - ((m : ℂ) + 1 / 2) * Complex.arctan (Complex.sinh z)

/-- Goldstein's `Fc_m(z, h)`, defined with `Gc_m` so that 28.26.1 holds:
`Fc_m = (π h cosh z)^{1/2} (cos φ Mc^{(1)}_m + sin φ Mc^{(2)}_m)`. -/
@[dlmf 28.26.E1]
def goldsteinFc (m : ℕ) (z : ℂ) (h : ℝ) : ℂ :=
  (π * h * Complex.cosh z) ^ (1 / 2 : ℂ) *
    (Complex.cos (goldsteinPhase m z h) * radialMathieuMc 1 m z h +
      Complex.sin (goldsteinPhase m z h) * radialMathieuMc 2 m z h)

/-- Goldstein's `Gc_m(z, h) = (π h cosh z)^{1/2} (sin φ Mc^{(1)}_m - cos φ Mc^{(2)}_m)`; with
`Fc_m` it gives `Mc^{(3)}_m = e^{iφ} (π h cosh z)^{-1/2} (Fc_m - i Gc_m)` (DLMF 28.26.1). -/
@[dlmf 28.26.E1]
def goldsteinGc (m : ℕ) (z : ℂ) (h : ℝ) : ℂ :=
  (π * h * Complex.cosh z) ^ (1 / 2 : ℂ) *
    (Complex.sin (goldsteinPhase m z h) * radialMathieuMc 1 m z h -
      Complex.cos (goldsteinPhase m z h) * radialMathieuMc 2 m z h)

/-- Goldstein's `Fs_m(z, h) = (π h cosh z)^{1/2} (sin φ Ms^{(1)}_{m+1} - cos φ Ms^{(2)}_{m+1})`;
with `Gs_m` it gives `i Ms^{(3)}_{m+1} = e^{iφ} (π h cosh z)^{-1/2} (Fs_m - i Gs_m)`
(DLMF 28.26.2). -/
@[dlmf 28.26.E2]
def goldsteinFs (m : ℕ) (z : ℂ) (h : ℝ) : ℂ :=
  (π * h * Complex.cosh z) ^ (1 / 2 : ℂ) *
    (Complex.sin (goldsteinPhase m z h) * radialMathieuMs 1 (m + 1) z h -
      Complex.cos (goldsteinPhase m z h) * radialMathieuMs 2 (m + 1) z h)

/-- Goldstein's `Gs_m(z, h) = -(π h cosh z)^{1/2} (cos φ Ms^{(1)}_{m+1} + sin φ Ms^{(2)}_{m+1})`
(DLMF 28.26.2). -/
@[dlmf 28.26.E2]
def goldsteinGs (m : ℕ) (z : ℂ) (h : ℝ) : ℂ :=
  -((π * h * Complex.cosh z) ^ (1 / 2 : ℂ) *
    (Complex.cos (goldsteinPhase m z h) * radialMathieuMs 1 (m + 1) z h +
      Complex.sin (goldsteinPhase m z h) * radialMathieuMs 2 (m + 1) z h))

/-- The partial sum `1 + s/(8h cosh² z) + … ` of Goldstein's expansion 28.26.4 of `Fc_m`
through the `h⁻³` term, `s = 2m + 1`. -/
def goldsteinFcApprox (m : ℕ) (z : ℂ) (h : ℝ) : ℂ :=
  let s : ℂ := 2 * m + 1
  let C := Complex.cosh z
  1 + s / (8 * h * C ^ 2) +
    1 / (2 ^ 11 * h ^ 2) *
      ((s ^ 4 + 86 * s ^ 2 + 105) / C ^ 4 - (s ^ 4 + 22 * s ^ 2 + 57) / C ^ 2) +
    1 / (2 ^ 14 * h ^ 3) * (-(s ^ 5 + 14 * s ^ 3 + 33 * s) / C ^ 2 -
      (2 * s ^ 5 + 124 * s ^ 3 + 1122 * s) / C ^ 4 + (3 * s ^ 5 + 290 * s ^ 3 + 1627 * s) / C ^ 6)

/-- The partial sum of Goldstein's expansion 28.26.5 of `Gc_m` through the `h⁻³` term. -/
def goldsteinGcApprox (m : ℕ) (z : ℂ) (h : ℝ) : ℂ :=
  let s : ℂ := 2 * m + 1
  let C := Complex.cosh z
  Complex.sinh z / C ^ 2 * ((s ^ 2 + 3) / (2 ^ 5 * h) +
    1 / (2 ^ 9 * h ^ 2) * (s ^ 3 + 3 * s + (4 * s ^ 3 + 44 * s) / C ^ 2) +
    1 / (2 ^ 14 * h ^ 3) * (5 * s ^ 4 + 34 * s ^ 2 + 9 -
      (s ^ 6 - 47 * s ^ 4 + 667 * s ^ 2 + 2835) / (12 * C ^ 2) +
      (s ^ 6 + 505 * s ^ 4 + 12139 * s ^ 2 + 10395) / (12 * C ^ 4)))

end DLMF.Mathieu
