/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Lame.Basic.SpectralData

/-!
# Lamé recurrences, Fourier coefficients, stability and asymptotic data
-/

@[expose] public noncomputable section

open Complex DLMF.JacobiElliptic DLMF.Elliptic Set Filter
open scoped Real Topology

namespace DLMF.Lame

/-! ### Three-term recurrences and continued fractions (§§29.3(iii), 29.6) -/

/-- The eight three-term recurrences of DLMF §§29.3(iii) and 29.6: `A0` (29.3.11–29.3.12, for
`a^{2m}`, coefficients `A_{2p}`), `A1` (29.3.13–29.3.14, `a^{2m+1}`, `A_{2p+1}`), `B1`
(29.3.15–29.3.16, `b^{2m+1}`, `B_{2p+1}`), `B2` (29.3.17, `b^{2m+2}`, `B_{2p+2}`), `C0`
(29.6.11, `a^{2m}`, `C_{2p}`), `C1` (29.6.26, `a^{2m+1}`, `C_{2p+1}`), `D1` (29.6.41,
`b^{2m+1}`, `D_{2p+1}`) and `D2` (29.6.56, `b^{2m+2}`, `D_{2p+2}`). -/
inductive LameRecurrence
  | A0 | A1 | B1 | B2 | C0 | C1 | D1 | D2
  deriving DecidableEq

namespace LameRecurrence

/-- The coefficient `α_p` (DLMF 29.3.11, 29.3.14, 29.3.16, 29.3.17, 29.6.11, 29.6.26, 29.6.41,
29.6.56). -/
@[dlmf 29.3.E11, dlmf 29.3.E14, dlmf 29.3.E16, dlmf 29.3.E17, dlmf 29.6.E11, dlmf 29.6.E26,
  dlmf 29.6.E41, dlmf 29.6.E56]
def alpha : LameRecurrence → ℝ → ℝ → ℕ → ℝ
  | A0, ν, k, p =>
      if p = 0 then (ν - 1) * (ν + 2) * k ^ 2 else (ν - 2 * p - 1) * (ν + 2 * p + 2) * k ^ 2 / 2
  | A1, ν, k, p => (ν - 2 * p - 2) * (ν + 2 * p + 3) * k ^ 2 / 2
  | B1, ν, k, p => (ν - 2 * p - 2) * (ν + 2 * p + 3) * k ^ 2 / 2
  | B2, ν, k, p => (ν - 2 * p - 3) * (ν + 2 * p + 4) * k ^ 2 / 2
  | C0, ν, k, p =>
      if p = 0 then ν * (ν + 1) * k ^ 2 else (ν - 2 * p) * (ν + 2 * p + 1) * k ^ 2 / 2
  | C1, ν, k, p => (ν - 2 * p - 1) * (ν + 2 * p + 2) * k ^ 2 / 2
  | D1, ν, k, p => (ν - 2 * p - 1) * (ν + 2 * p + 2) * k ^ 2 / 2
  | D2, ν, k, p => (ν - 2 * p - 2) * (ν + 2 * p + 3) * k ^ 2 / 2

/-- The coefficient `β_p` (DLMF 29.3.12, 29.3.13, 29.3.15, 29.3.17, 29.6.11, 29.6.26, 29.6.41,
29.6.56). -/
@[dlmf 29.3.E12, dlmf 29.3.E13, dlmf 29.3.E15, dlmf 29.3.E17, dlmf 29.6.E11, dlmf 29.6.E26,
  dlmf 29.6.E41, dlmf 29.6.E56]
def beta : LameRecurrence → ℝ → ℝ → ℕ → ℝ
  | A0, _, k, p => 4 * p ^ 2 * (2 - k ^ 2)
  | A1, ν, k, p =>
      if p = 0 then 2 - k ^ 2 + ν * (ν + 1) * k ^ 2 / 2 else (2 * p + 1) ^ 2 * (2 - k ^ 2)
  | B1, ν, k, p =>
      if p = 0 then 2 - k ^ 2 - ν * (ν + 1) * k ^ 2 / 2 else (2 * p + 1) ^ 2 * (2 - k ^ 2)
  | B2, _, k, p => (2 * p + 2) ^ 2 * (2 - k ^ 2)
  | C0, _, k, p => 4 * p ^ 2 * (2 - k ^ 2)
  | C1, ν, k, p =>
      if p = 0 then 2 - k ^ 2 + ν * (ν + 1) * k ^ 2 / 2 else (2 * p + 1) ^ 2 * (2 - k ^ 2)
  | D1, ν, k, p =>
      if p = 0 then 2 - k ^ 2 - ν * (ν + 1) * k ^ 2 / 2 else (2 * p + 1) ^ 2 * (2 - k ^ 2)
  | D2, _, k, p => (2 * p + 2) ^ 2 * (2 - k ^ 2)

/-- The coefficient `γ_p` (DLMF 29.3.12, 29.3.14, 29.3.16, 29.3.17, 29.6.11, 29.6.26, 29.6.41,
29.6.56). -/
@[dlmf 29.3.E12, dlmf 29.3.E14, dlmf 29.3.E16, dlmf 29.3.E17, dlmf 29.6.E11, dlmf 29.6.E26,
  dlmf 29.6.E41, dlmf 29.6.E56]
def gamma : LameRecurrence → ℝ → ℝ → ℕ → ℝ
  | A0, ν, k, p => (ν - 2 * p + 2) * (ν + 2 * p - 1) * k ^ 2 / 2
  | A1, ν, k, p => (ν - 2 * p + 1) * (ν + 2 * p) * k ^ 2 / 2
  | B1, ν, k, p => (ν - 2 * p + 1) * (ν + 2 * p) * k ^ 2 / 2
  | B2, ν, k, p => (ν - 2 * p) * (ν + 2 * p + 1) * k ^ 2 / 2
  | C0, ν, k, p => (ν - 2 * p + 1) * (ν + 2 * p) * k ^ 2 / 2
  | C1, ν, k, p => (ν - 2 * p) * (ν + 2 * p + 1) * k ^ 2 / 2
  | D1, ν, k, p => (ν - 2 * p) * (ν + 2 * p + 1) * k ^ 2 / 2
  | D2, ν, k, p => (ν - 2 * p - 1) * (ν + 2 * p + 2) * k ^ 2 / 2

/-- `c` satisfies the three-term recurrence `r` with eigenparameter `H` (DLMF 29.6.3–29.6.4 and
their analogues): `(β₀ - H)c₀ + α₀c₁ = 0` and
`γ_p c_{p-1} + (β_p - H)c_p + α_p c_{p+1} = 0` for `p ≥ 1`. The index `p` of `c` is the
position in the coefficient list (`c p = A_{2p}`, `A_{2p+1}`, `B_{2p+2}`, …). -/
def Satisfies (r : LameRecurrence) (ν k H : ℝ) (c : ℕ → ℝ) : Prop :=
  (r.beta ν k 0 - H) * c 0 + r.alpha ν k 0 * c 1 = 0 ∧
    ∀ p : ℕ, r.gamma ν k (p + 1) * c p + (r.beta ν k (p + 1) - H) * c (p + 1) +
      r.alpha ν k (p + 1) * c (p + 2) = 0

end LameRecurrence

/-- The left side of the continued-fraction equation 29.3.10 (finite):
`β_p - H - α_{p-1}γ_p/(β_{p-1} - H - ⋯ - α₀γ₁/(β₀ - H))`. -/
@[dlmf 29.3.E10]
def lameCFLeft (r : LameRecurrence) (ν k H : ℝ) : ℕ → ℝ
  | 0 => r.beta ν k 0 - H
  | p + 1 => r.beta ν k (p + 1) - H - r.alpha ν k p * r.gamma ν k (p + 1) / lameCFLeft r ν k H p

/-- The truncation at depth `d` of the right side of 29.3.10:
`α_pγ_{p+1}/(β_{p+1} - H - α_{p+1}γ_{p+2}/(β_{p+2} - H - ⋯))` with `d` partial denominators. -/
@[dlmf 29.3.E10]
def lameCFRight (r : LameRecurrence) (ν k H : ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 0
  | p, d + 1 => r.alpha ν k p * r.gamma ν k (p + 1) /
      (r.beta ν k (p + 1) - H - lameCFRight r ν k H (p + 1) d)

/-! ### Fourier coefficients (§29.6) -/

/-- The cosine Fourier coefficient of a real function `w` in the variable `φ = π/2 - am(x, k)`
of 29.2.5, `(4/π) ∫₀^K w(x) cos(jφ(x)) ρ(x) dx` with `ρ = dn(x, k)` (`weighted`; this is
`(4/π) ∫₀^{π/2} w cos(jφ) dφ`, giving `A_j` in 29.6.1 and 29.6.16) or `ρ = 1` (giving `C_j` in
29.6.8 and 29.6.23, where `w/dn` is expanded). -/
def Real.lameCosCoeff (w : ℝ → ℝ) (k : ℝ) (weighted : Bool) (j : ℕ) : ℝ :=
  4 / π * ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2),
    w x * Real.cos (j * Real.lamePhi x k) * (if weighted then Real.jacobiDnm x (k ^ 2) else 1)

/-- The sine Fourier coefficient `(4/π) ∫₀^K w(x) sin(jφ(x)) ρ(x) dx` (`ρ = dn` if `weighted`,
giving `B_j` in 29.6.31 and 29.6.46; `ρ = 1` giving `D_j` in 29.6.38 and 29.6.53). -/
def Real.lameSinCoeff (w : ℝ → ℝ) (k : ℝ) (weighted : Bool) (j : ℕ) : ℝ :=
  4 / π * ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2),
    w x * Real.sin (j * Real.lamePhi x k) * (if weighted then Real.jacobiDnm x (k ^ 2) else 1)

/-! ### Stability (§29.9) -/

/-- Lamé's equation 29.2.1 with parameters `k, h, ν` is stable if all its real solutions are
bounded on `ℝ` (DLMF §29.9). -/
@[dlmf 29.9]
def Real.IsLameStable (h ν k : ℝ) : Prop :=
  ∀ w : ℝ → ℝ, Real.IsLameSolution h ν k w → ∃ C, ∀ x, |w x| ≤ C

/-! ### Asymptotic coefficients (§29.7(i)) -/

/-- `κ = k(ν(ν+1))^{1/2}` (DLMF 29.7.2). -/
@[dlmf 29.7.E2]
def lameKappa (ν k : ℝ) : ℝ := k * Real.sqrt (ν * (ν + 1))

/-- The coefficient `τ₀ = (1 + k²)(1 + p²)/2³` (DLMF 29.7.3). -/
@[dlmf 29.7.E3]
def lameTau0 (p k : ℝ) : ℝ := (1 + k ^ 2) * (1 + p ^ 2) / 2 ^ 3

/-- The coefficient `τ₁ = p((1 + k²)²(p² + 3) - 4k²(p² + 5))/2⁶` (DLMF 29.7.4). -/
@[dlmf 29.7.E4]
def lameTau1 (p k : ℝ) : ℝ := p / 2 ^ 6 * ((1 + k ^ 2) ^ 2 * (p ^ 2 + 3) - 4 * k ^ 2 * (p ^ 2 + 5))

/-- The coefficient `τ₂ = (1 + k²)(1 - k²)²(5p⁴ + 34p² + 9)/2¹⁰` (DLMF 29.7.6). -/
@[dlmf 29.7.E6]
def lameTau2 (p k : ℝ) : ℝ := (1 + k ^ 2) * (1 - k ^ 2) ^ 2 * (5 * p ^ 4 + 34 * p ^ 2 + 9) / 2 ^ 10

/-- The coefficient `τ₃` of DLMF 29.7.7. -/
@[dlmf 29.7.E7]
def lameTau3 (p k : ℝ) : ℝ :=
  p / 2 ^ 14 * ((1 + k ^ 2) ^ 4 * (33 * p ^ 4 + 410 * p ^ 2 + 405) -
    24 * k ^ 2 * (1 + k ^ 2) ^ 2 * (7 * p ^ 4 + 90 * p ^ 2 + 95) +
    16 * k ^ 4 * (9 * p ^ 4 + 130 * p ^ 2 + 173))

/-- The coefficient `τ₄` of DLMF 29.7.8. -/
@[dlmf 29.7.E8]
def lameTau4 (p k : ℝ) : ℝ :=
  1 / 2 ^ 16 * ((1 + k ^ 2) ^ 5 * (63 * p ^ 6 + 1260 * p ^ 4 + 2943 * p ^ 2 + 486) -
    8 * k ^ 2 * (1 + k ^ 2) ^ 3 * (49 * p ^ 6 + 1010 * p ^ 4 + 2493 * p ^ 2 + 432) +
    16 * k ^ 4 * (1 + k ^ 2) * (35 * p ^ 6 + 760 * p ^ 4 + 2043 * p ^ 2 + 378))

/-- The coefficients of Lamé's equation 29.2.1 in the form of `Complex.linearODEValue`
(index `0`: coefficient of `w`, index `1`: coefficient of `w'`). -/
def lameODECoeff (h ν k : ℂ) : Fin 2 → ℂ → ℂ :=
  ![fun z => h - ν * (ν + 1) * k ^ 2 * jacobiSnk z k ^ 2, fun _ => 0]

end DLMF.Lame
