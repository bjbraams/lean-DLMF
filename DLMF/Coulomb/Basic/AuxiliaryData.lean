/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Coulomb.Basic.Functions
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Coulomb functions in `ρ, η`: auxiliary definitions (DLMF §§33.4–33.13)

Definitions used by the statements of DLMF §§33.4–33.13, on top of the functions
`F_ℓ`, `G_ℓ`, `H^±_ℓ`, `C_ℓ`, `σ_ℓ`, `θ_ℓ` of `DLMF.Coulomb.Basic` (namespace `DLMF.Confluent`).

* `recurrenceR`, `recurrenceS`, `recurrenceT`: the coefficients `R_ℓ`, `S_ℓ`, `T_ℓ` of the
  recurrences (DLMF 33.4.1).
* `phaseShift`: the Coulomb phase shift `σ_ℓ(η)` with DLMF's branch (zero at `η = 0`,
  continuous in `η`), as `-γη + ∑_{n ≥ 1} (η/n - arctan(η/n)) + ∑_{k=1}^{ℓ} arctan(η/k)`.
  The principal-branch `DLMF.Confluent.coulombSigma` differs from it by a multiple of `2π`.
* `powerSeriesCoeff`: the coefficients `A_k^ℓ(η)` of the power series 33.6.1, by the
  recurrence 33.6.3 with `A_{ℓ+1}^ℓ = 1`, `A_{ℓ+2}^ℓ = η/(ℓ+1)`.
* `besselSeriesCoeffA`, `besselSeriesCoeffB`: the coefficients `a_k` of 33.9.1 (recurrence
  33.9.2) and `b_k` of 33.9.3–33.9.4 (recurrence 33.9.5).
* `largeRhoF`, `largeRhoG`, `largeRhoFHat`, `largeRhoGHat`: the amplitude functions
  `f, g, f̂, ĝ` of DLMF 33.11.2–33.11.3, and `largeRhoTerm`: the terms
  `(f_k, g_k, f̂_k, ĝ_k)` of the expansions 33.11.5–33.11.6 (recurrence 33.11.8–33.11.9).
* `transitionX`, `transitionMu`, `transitionA`, `transitionB`: the variables and polynomials
  of the transition-region expansions DLMF 33.12.1, 33.12.4–33.12.5.
* `coulombWaveComplex`: the unnormalized regular solution
  `ρ^{ℓ+1} e^{-iρ} M(ℓ+1-iη, 2ℓ+2, 2iρ)` for complex `ℓ`, `η`, `ρ` (DLMF §33.13).
-/

@[expose] public section

open Complex
open scoped Real Nat

noncomputable section

namespace DLMF.Coulomb

open DLMF.Confluent

/-- The recurrence coefficient `R_ℓ = (1 + η²/ℓ²)^{1/2}` (DLMF 33.4.1), for `ℓ ≥ 1`. -/
@[dlmf 33.4.E1]
def recurrenceR (ℓ : ℕ) (η : ℝ) : ℝ := Real.sqrt (1 + η ^ 2 / (ℓ : ℝ) ^ 2)

/-- The recurrence coefficient `S_ℓ = ℓ/ρ + η/ℓ` (DLMF 33.4.1), for `ℓ ≥ 1`. -/
@[dlmf 33.4.E1]
def recurrenceS (ℓ : ℕ) (η ρ : ℝ) : ℝ := ℓ / ρ + η / ℓ

/-- The recurrence coefficient `T_ℓ = S_ℓ + S_{ℓ+1}` (DLMF 33.4.1), for `ℓ ≥ 1`. -/
@[dlmf 33.4.E1]
def recurrenceT (ℓ : ℕ) (η ρ : ℝ) : ℝ := recurrenceS ℓ η ρ + recurrenceS (ℓ + 1) η ρ

/-- The Coulomb phase shift `σ_ℓ(η) = ph Γ(ℓ+1+iη)` with the branch of DLMF 33.2.10: zero at
`η = 0` and continuous in `η`. It is given by the Weierstrass product of `Γ`:
`σ_ℓ(η) = -γη + ∑_{n ≥ 1} (η/n - arctan(η/n)) + ∑_{k=1}^{ℓ} arctan(η/k)`. -/
@[dlmf 33.2.E10]
def phaseShift (ℓ : ℕ) (η : ℝ) : ℝ :=
  -Real.eulerMascheroniConstant * η +
    ∑' n : ℕ, (η / (n + 1) - Real.arctan (η / (n + 1))) +
    ∑ k ∈ Finset.range ℓ, Real.arctan (η / (k + 1))

/-- The coefficients `A_{ℓ+1+n}^ℓ(η)` of DLMF 33.6.1 indexed by `n`: `1`, `η/(ℓ+1)`, and the
recurrence DLMF 33.6.3, `(k+ℓ)(k-ℓ-1) A_k = 2η A_{k-1} - A_{k-2}` with `k = ℓ+3+n`. -/
def powerSeriesCoeffAux (ℓ : ℕ) (η : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => η / (ℓ + 1)
  | n + 2 => (2 * η * powerSeriesCoeffAux ℓ η (n + 1) - powerSeriesCoeffAux ℓ η n) /
      (((n : ℝ) + 2 * ℓ + 3) * ((n : ℝ) + 2))

/-- The coefficient `A_k^ℓ(η)` of the power series `F_ℓ = C_ℓ ∑_{k ≥ ℓ+1} A_k^ℓ ρ^k`
(DLMF 33.6.1, 33.6.3), extended by `0` for `k ≤ ℓ`. -/
@[dlmf 33.6.E3]
def powerSeriesCoeff (ℓ : ℕ) (η : ℝ) (k : ℕ) : ℝ :=
  if ℓ + 1 ≤ k then powerSeriesCoeffAux ℓ η (k - (ℓ + 1)) else 0

/-- The coefficients `a_k` of the spherical Bessel series DLMF 33.9.1:
`a_0 = (2ℓ+1)!! C_ℓ(η)`, `a_{-1} = 0` and the recurrence DLMF 33.9.2,
`k(k+2ℓ+1)/(2k+2ℓ+1) a_k - 2η a_{k-1} + (k-2)(k+2ℓ-1)/(2k+2ℓ-3) a_{k-2} = 0`. -/
@[dlmf 33.9.E2]
def besselSeriesCoeffA (ℓ : ℕ) (η : ℝ) : ℕ → ℝ
  | 0 => ((2 * ℓ + 1)‼ : ℝ) * coulombC ℓ η
  | 1 => 2 * η * (((2 * ℓ + 1)‼ : ℝ) * coulombC ℓ η) * (2 * ℓ + 3) / (2 * ℓ + 2)
  | k + 2 => (2 * η * besselSeriesCoeffA ℓ η (k + 1) -
      (k : ℝ) * (k + 2 * ℓ + 1) / (2 * k + 2 * ℓ + 1) * besselSeriesCoeffA ℓ η k) *
      (2 * k + 2 * ℓ + 5) / (((k : ℝ) + 2) * (k + 2 * ℓ + 3))

/-- The coefficients `b_{2ℓ+n}` of DLMF 33.9.3–33.9.4 indexed by `n`: `b_{2ℓ} = 0`,
`b_{2ℓ+1} = 1`, `b_{2ℓ+2} = 0` and the recurrence DLMF 33.9.5,
`4η²(k-2ℓ) b_{k+1} + k b_{k-1} + b_{k-2} = 0` with `k = 2ℓ+2+n`. -/
def besselSeriesCoeffBAux (ℓ : ℕ) (η : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | n + 3 => -(((n : ℝ) + 2 + 2 * ℓ) * besselSeriesCoeffBAux ℓ η (n + 1) +
      besselSeriesCoeffBAux ℓ η n) / (4 * η ^ 2 * ((n : ℝ) + 2))

/-- The coefficient `b_k` of DLMF 33.9.3–33.9.5 (`η ≠ 0`), extended by `0` for `k < 2ℓ`. -/
@[dlmf 33.9.E5]
def besselSeriesCoeffB (ℓ : ℕ) (η : ℝ) (k : ℕ) : ℝ :=
  if 2 * ℓ ≤ k then besselSeriesCoeffBAux ℓ η (k - 2 * ℓ) else 0

/-- The amplitude `f(η,ρ) = G_ℓ cos θ_ℓ + F_ℓ sin θ_ℓ` of DLMF 33.11.2 (the unique `f` with
33.11.2 together with `largeRhoG`). -/
@[dlmf 33.11.E2]
def largeRhoF (ℓ : ℕ) (η ρ : ℝ) : ℝ :=
  coulombG ℓ η ρ * Real.cos (coulombTheta ℓ η ρ) + coulombF ℓ η ρ * Real.sin (coulombTheta ℓ η ρ)

/-- The amplitude `g(η,ρ) = F_ℓ cos θ_ℓ - G_ℓ sin θ_ℓ` of DLMF 33.11.2. -/
@[dlmf 33.11.E2]
def largeRhoG (ℓ : ℕ) (η ρ : ℝ) : ℝ :=
  coulombF ℓ η ρ * Real.cos (coulombTheta ℓ η ρ) - coulombG ℓ η ρ * Real.sin (coulombTheta ℓ η ρ)

/-- The amplitude `f̂(η,ρ) = G_ℓ' cos θ_ℓ + F_ℓ' sin θ_ℓ` of DLMF 33.11.3 (derivatives in
`ρ`). -/
@[dlmf 33.11.E3]
def largeRhoFHat (ℓ : ℕ) (η ρ : ℝ) : ℝ :=
  deriv (coulombG ℓ η) ρ * Real.cos (coulombTheta ℓ η ρ) +
    deriv (coulombF ℓ η) ρ * Real.sin (coulombTheta ℓ η ρ)

/-- The amplitude `ĝ(η,ρ) = F_ℓ' cos θ_ℓ - G_ℓ' sin θ_ℓ` of DLMF 33.11.3. -/
@[dlmf 33.11.E3]
def largeRhoGHat (ℓ : ℕ) (η ρ : ℝ) : ℝ :=
  deriv (coulombF ℓ η) ρ * Real.cos (coulombTheta ℓ η ρ) -
    deriv (coulombG ℓ η) ρ * Real.sin (coulombTheta ℓ η ρ)

/-- The terms `(f_k, g_k, f̂_k, ĝ_k)` of DLMF 33.11.5–33.11.6: `f_0 = 1`, `g_0 = 0`,
`f̂_0 = 0`, `ĝ_0 = 1 - η/ρ` and the recurrence DLMF 33.11.8 with `λ_k`, `μ_k` of 33.11.9. -/
@[dlmf 33.11.E8]
def largeRhoTerm (ℓ : ℕ) (η ρ : ℝ) : ℕ → ℝ × ℝ × ℝ × ℝ
  | 0 => (1, 0, 0, 1 - η / ρ)
  | k + 1 =>
    let t := largeRhoTerm ℓ η ρ k
    let lam : ℝ := (2 * k + 1) * η / ((2 * k + 2) * ρ)
    let mu : ℝ := ((ℓ : ℝ) * (ℓ + 1) - k * (k + 1) + η ^ 2) / ((2 * k + 2) * ρ)
    let f := lam * t.1 - mu * t.2.1
    let g := lam * t.2.1 + mu * t.1
    (f, g, lam * t.2.2.1 - mu * t.2.2.2 - f / ρ, lam * t.2.2.2 + mu * t.2.2.1 - g / ρ)

/-- The unnormalized regular Coulomb function `ρ^{ℓ+1} e^{-iρ} M(ℓ+1-iη, 2ℓ+2, 2iρ)` for complex
`ℓ`, `η`, `ρ` (DLMF §33.13), with the principal power `ρ^{ℓ+1}`. For `ℓ ∈ ℕ` it agrees with
`DLMF.Confluent.coulombWave`. -/
def coulombWaveComplex (ℓ η ρ : ℂ) : ℂ :=
  ρ ^ (ℓ + 1) * exp (-I * ρ) * kummerM (ℓ + 1 - I * η) (2 * ℓ + 2) (2 * I * ρ)

/-- The transition-region variable `x = (2η - ρ)/(2η)^{1/3}` of DLMF 33.12.1 (`η > 0`). -/
@[dlmf 33.12.E1]
def transitionX (η ρ : ℝ) : ℝ := (2 * η - ρ) / (2 * η) ^ (1 / 3 : ℝ)

/-- The large parameter `μ = (2η)^{2/3}` of DLMF 33.12.1 (`η > 0`). -/
@[dlmf 33.12.E1]
def transitionMu (η : ℝ) : ℝ := (2 * η) ^ (2 / 3 : ℝ)

/-- The polynomials `A_1, A_2, A_3` of DLMF 33.12.4 (`A_k = 0` for other `k`). -/
@[dlmf 33.12.E4]
def transitionA (k : ℕ) (x : ℝ) : ℝ :=
  match k with
  | 1 => x ^ 2 / 5
  | 2 => (2 * x ^ 3 + 6) / 35
  | 3 => (21 * x ^ 7 + 370 * x ^ 4 + 580 * x) / 15750
  | _ => 0

/-- The polynomials `B_1, B_2, B_3` of DLMF 33.12.5 (`B_k = 0` for other `k`). -/
@[dlmf 33.12.E5]
def transitionB (k : ℕ) (x : ℝ) : ℝ :=
  match k with
  | 1 => -x / 5
  | 2 => (7 * x ^ 5 - 30 * x ^ 2) / 350
  | 3 => (264 * x ^ 6 - 290 * x ^ 3 - 560) / 15750
  | _ => 0

end DLMF.Coulomb
