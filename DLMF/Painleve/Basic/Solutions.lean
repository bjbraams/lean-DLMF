/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.Basic
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt

/-!
# Definitions for the solutions, reductions and applications of Painlevé equations

Definitions for DLMF §§32.8–32.15 (agent ACQ32B), building on `DLMF.Painleve.Basic.Equations`.

* `yablonskiiVorobievQ` (32.8.6, the Yablonskii–Vorob'ev polynomials `Q_n`), the generating
  polynomials `yablonskiiVorobievP` of 32.8.8 and the Wronskians `yablonskiiVorobievTau` of
  32.8.10; the rational solutions `rationalPainleveII n` of `PII` with `α = n` (32.8.5).
* `wronskianTau φ n z` (32.10.9), the `n × n` Wronskian of `φ, φ', …, φ⁽ⁿ⁻¹⁾`.
* `IsRationalOn`, `IsAlgebraicOn`: a function agrees on `U` with a polynomial quotient, or
  satisfies a nontrivial polynomial relation `P(z, w(z)) = 0` (used in 32.8 and 32.9).
* Real-variable equations for §32.11: `IsRealODE2SolutionOn`, with the right-hand sides of
  real `PI`, the modified `PII` (32.11.12), real `PIII` and `PIV`.
* Partial differential equations of §32.13 (`IsMKdVOn`, `IsKdVOn`, `IsSineGordonOn`,
  `IsBoussinesqOn`) for holomorphic functions of `(x, t)`, using sections `x ↦ u(x, t)` and
  `t ↦ u(x, t)`.
* The longest increasing subsequence length `longestIncreasingLength` and the Tracy–Widom type
  distribution `tracyWidomF` of §32.14.
-/

@[expose] public noncomputable section

open Polynomial Set Filter MeasureTheory
open scoped Topology

namespace DLMF.Painleve

/-! ## Rational solutions of `PII` (§32.8(ii)) -/

/-- DLMF 32.8.6: the Yablonskii–Vorob'ev polynomials, `Q₀ = 1`, `Q₁ = z` and
`Q_{n+1} Q_{n-1} = z Q_n² + 4 (Q_n')² - 4 Q_n Q_n''`. The recurrence is implemented with
polynomial division by `Q_{n-1}`; that the division is exact is part of 32.8.6. -/
@[dlmf 32.8.E6]
def yablonskiiVorobievQ : ℕ → ℂ[X]
  | 0 => 1
  | 1 => X
  | n + 2 =>
      (X * yablonskiiVorobievQ (n + 1) ^ 2 + C 4 * (derivative (yablonskiiVorobievQ (n + 1))) ^ 2 -
          C 4 * yablonskiiVorobievQ (n + 1) *
            derivative (derivative (yablonskiiVorobievQ (n + 1)))) / yablonskiiVorobievQ n

/-- DLMF 32.8.5: the rational solution `w(z; n) = d/dz ln(Q_{n-1}(z)/Q_n(z))` of `PII` with
`α = n`, written as the difference of logarithmic derivatives `Q_{n-1}'/Q_{n-1} - Q_n'/Q_n`
(no logarithm branch is involved). For `n = 0` it is the seed `0`, and for negative `n` it is
`w(z; n) = -w(z; -n)` (the symmetry `w ↦ -w`, `α ↦ -α`). -/
@[dlmf 32.8.E5]
def rationalPainleveII (n : ℤ) (z : ℂ) : ℂ :=
  if 0 < n then
    (derivative (yablonskiiVorobievQ (n.toNat - 1))).eval z /
        (yablonskiiVorobievQ (n.toNat - 1)).eval z -
      (derivative (yablonskiiVorobievQ n.toNat)).eval z / (yablonskiiVorobievQ n.toNat).eval z
  else if n = 0 then 0
  else
    -((derivative (yablonskiiVorobievQ ((-n).toNat - 1))).eval z /
          (yablonskiiVorobievQ ((-n).toNat - 1)).eval z -
        (derivative (yablonskiiVorobievQ (-n).toNat)).eval z /
          (yablonskiiVorobievQ (-n).toNat).eval z)

/-- DLMF 32.8.8: the polynomials `p_m(z)` with `∑ p_m(z) λ^m = exp(zλ - (4/3)λ³)`,
`p_m(z) = ∑_{3j ≤ m} (-4/3)^j z^{m-3j} / (j! (m-3j)!)`. (DLMF also sets `p_m = 0` for
`m < 0`; only `m ≥ 0` occurs here.) -/
@[dlmf 32.8.E8]
def yablonskiiVorobievP (m : ℕ) : ℂ[X] :=
  ∑ j ∈ Finset.range (m / 3 + 1),
    C ((-4 / 3 : ℂ) ^ j / ((j.factorial : ℂ) * ((m - 3 * j).factorial : ℂ))) * X ^ (m - 3 * j)

/-- DLMF 32.8.10: the `n × n` Wronskian `τ_n = 𝒲{p₁, p₃, …, p_{2n-1}}`, the determinant of
`(p_{2j+1}^{(i)})_{0 ≤ i, j < n}`; `τ₀ = 1`. -/
@[dlmf 32.8.E10]
def yablonskiiVorobievTau (n : ℕ) : ℂ[X] :=
  (Matrix.of fun i j : Fin n => derivative^[i] (yablonskiiVorobievP (2 * j + 1))).det

/-! ## Wronskian tau functions (§32.10(ii)) -/

/-- DLMF 32.10.9: the `n × n` Wronskian `τ_n(z) = 𝒲{φ, φ', …, φ⁽ⁿ⁻¹⁾}(z)`, the determinant of
`(φ^{(i+j)}(z))_{0 ≤ i, j < n}`; `τ₀ = 1`. -/
@[dlmf 32.10.E9]
def wronskianTau (φ : ℂ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  (Matrix.of fun i j : Fin n => iteratedDeriv (i + j) φ z).det

/-! ## Rational and algebraic functions -/

/-- `w` agrees on `U` with a polynomial quotient `p/q` whose denominator has no zero in `U`.
This is the meaning of "rational solution" in §32.8. -/
def IsRationalOn (w : ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∃ p q : ℂ[X], ∀ z ∈ U, q.eval z ≠ 0 ∧ w z = p.eval z / q.eval z

/-- `w` is algebraic on `U`: a nonzero bivariate polynomial `P` satisfies `P(z, w(z)) = 0`
on `U` (`P ∈ ℂ[X][Y]`, evaluated with `Polynomial.evalEval`). This is the meaning of
"algebraic solution" in §32.9. -/
def IsAlgebraicOn (w : ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∃ P : ℂ[X][X], P ≠ 0 ∧ ∀ z ∈ U, P.evalEval z (w z) = 0

/-! ## Real-variable equations (§32.11) -/

/-- A real solution of `w'' = F(x, w, w')` on `s ⊆ ℝ`, with genuine differentiability of `w`
and of `w'` on `s` (the real analogue of `IsODE2SolutionOn`). -/
structure IsRealODE2SolutionOn (F : ℝ → ℝ → ℝ → ℝ) (w : ℝ → ℝ) (s : Set ℝ) : Prop where
  /-- The solution is differentiable at every point of the domain. -/
  differentiableAt : ∀ x ∈ s, DifferentiableAt ℝ w x
  /-- The first derivative has the derivative prescribed by the differential equation. -/
  hasDerivAt_deriv : ∀ x ∈ s, HasDerivAt (deriv w) (F x (w x) (deriv w x)) x

/-- The right-hand side `6w² + x` of real `PI` (32.2.1 on the real line). -/
def realPainleveIRhs (x w _v : ℝ) : ℝ := 6 * w ^ 2 + x

/-- The right-hand side `2w³ + xw + α` of real `PII` (32.2.2 on the real line); with `α = 0`
it is DLMF 32.11.4. -/
def realPainleveIIRhs (α : ℝ) (x w _v : ℝ) : ℝ := 2 * w ^ 3 + x * w + α

/-- The right-hand side `-2w³ + xw` of the modified `PII` equation, DLMF 32.11.12. -/
@[dlmf 32.11.E12]
def modifiedPainleveIIRhs (x w _v : ℝ) : ℝ := -2 * w ^ 3 + x * w

/-- The right-hand side of real `PIII` (32.2.3 on the real line, `x ≠ 0`, `w ≠ 0`). -/
def realPainleveIIIRhs (α β γ δ : ℝ) (x w v : ℝ) : ℝ :=
  v ^ 2 / w - v / x + (α * w ^ 2 + β) / x + γ * w ^ 3 + δ / w

/-- The right-hand side of real `PIV` (32.2.4 on the real line, `w ≠ 0`); with `α = 2ν + 1`,
`β = 0` it is DLMF 32.11.29. -/
def realPainleveIVRhs (α β : ℝ) (x w v : ℝ) : ℝ :=
  v ^ 2 / (2 * w) + 3 / 2 * w ^ 3 + 4 * x * w ^ 2 + 2 * (x ^ 2 - α) * w + β / w

/-! ## Partial differential equations (§32.13)

Functions `u : ℂ → ℂ → ℂ` of `(x, t)`; `x`-derivatives are iterated derivatives of the section
`x ↦ u x t` and `t`-derivatives derivatives of `t ↦ u x t`. Each predicate requires the
sections to be differentiable to the orders used, at every point of `U`. -/

/-- DLMF 32.13.1: the modified Korteweg–de Vries equation `v_t - 6v²v_x + v_xxx = 0` on
`U ⊆ ℂ × ℂ`. -/
@[dlmf 32.13.E1]
structure IsMKdVOn (v : ℂ → ℂ → ℂ) (U : Set (ℂ × ℂ)) : Prop where
  /-- The solution has three continuous complex derivatives in the spatial variable. -/
  contDiffAt_x : ∀ p ∈ U, ContDiffAt ℂ 3 (fun x => v x p.2) p.1
  /-- The solution is complex differentiable in time. -/
  differentiableAt_t : ∀ p ∈ U, DifferentiableAt ℂ (fun t => v p.1 t) p.2
  /-- The modified Korteweg-de Vries equation `v_t - 6v²v_x + v_xxx = 0` holds throughout the
  domain. -/
  eq : ∀ p ∈ U, deriv (fun t => v p.1 t) p.2 -
      6 * v p.1 p.2 ^ 2 * deriv (fun x => v x p.2) p.1 +
        iteratedDeriv 3 (fun x => v x p.2) p.1 = 0

/-- DLMF 32.13.3: the Korteweg–de Vries equation `u_t + 6uu_x + u_xxx = 0` on `U`. -/
@[dlmf 32.13.E3]
structure IsKdVOn (u : ℂ → ℂ → ℂ) (U : Set (ℂ × ℂ)) : Prop where
  /-- The solution has three continuous complex derivatives in the spatial variable. -/
  contDiffAt_x : ∀ p ∈ U, ContDiffAt ℂ 3 (fun x => u x p.2) p.1
  /-- The solution is complex differentiable in time. -/
  differentiableAt_t : ∀ p ∈ U, DifferentiableAt ℂ (fun t => u p.1 t) p.2
  /-- The Korteweg-de Vries equation `u_t + 6uu_x + u_xxx = 0` holds throughout the domain. -/
  eq : ∀ p ∈ U, deriv (fun t => u p.1 t) p.2 +
      6 * u p.1 p.2 * deriv (fun x => u x p.2) p.1 +
        iteratedDeriv 3 (fun x => u x p.2) p.1 = 0

/-- DLMF 32.13.6: the sine-Gordon equation `u_xt = sin u` on `U`; the mixed derivative is the
`t`-derivative of `u_x`. -/
@[dlmf 32.13.E6]
structure IsSineGordonOn (u : ℂ → ℂ → ℂ) (U : Set (ℂ × ℂ)) : Prop where
  /-- The solution is complex differentiable in the spatial variable. -/
  differentiableAt_x : ∀ p ∈ U, DifferentiableAt ℂ (fun x => u x p.2) p.1
  /-- The spatial derivative is complex differentiable in time. -/
  differentiableAt_xt : ∀ p ∈ U, DifferentiableAt ℂ (fun t => deriv (fun x => u x t) p.1) p.2
  /-- The sine-Gordon equation `u_xt = sin u` holds throughout the domain. -/
  eq : ∀ p ∈ U, deriv (fun t => deriv (fun x => u x t) p.1) p.2 = Complex.sin (u p.1 p.2)

/-- DLMF 32.13.8: the Boussinesq equation `u_tt = u_xx - 6(u²)_xx + u_xxxx` on `U`. -/
@[dlmf 32.13.E8]
structure IsBoussinesqOn (u : ℂ → ℂ → ℂ) (U : Set (ℂ × ℂ)) : Prop where
  /-- The solution has four continuous complex derivatives in the spatial variable at every point
  of the domain. -/
  contDiffAt_x : ∀ p ∈ U, ContDiffAt ℂ 4 (fun x => u x p.2) p.1
  /-- The solution has two continuous complex derivatives in time at every point of the domain. -/
  contDiffAt_t : ∀ p ∈ U, ContDiffAt ℂ 2 (fun t => u p.1 t) p.2
  /-- The Boussinesq equation `u_tt = u_xx - 6(u²)_xx + u_xxxx` holds throughout the domain. -/
  eq : ∀ p ∈ U, iteratedDeriv 2 (fun t => u p.1 t) p.2 =
      iteratedDeriv 2 (fun x => u x p.2) p.1 -
        6 * iteratedDeriv 2 (fun x => u x p.2 ^ 2) p.1 +
          iteratedDeriv 4 (fun x => u x p.2) p.1

/-! ## Combinatorics (§32.14) -/

open Classical in
/-- §32.14: the length `ℓ_N(π)` of the longest increasing subsequence of a permutation `π`
of `{0, …, N-1}`: the largest cardinality of a set of positions on which `π` is strictly
increasing. -/
@[dlmf 32.14]
def longestIncreasingLength {N : ℕ} (π : Equiv.Perm (Fin N)) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin N))).filter
    fun s : Finset (Fin N) => StrictMonoOn π (s : Set (Fin N))).sup
    Finset.card

/-- DLMF 32.14.2: `F(s) = exp(-∫_s^∞ (x - s) w(x)² dx)` for a real function `w` (in 32.14
the Hastings–McLeod solution of `PII` with `α = 0`). The integral is a Bochner integral over
`(s, ∞)`, totalized to `0` when not integrable. -/
@[dlmf 32.14.E2]
def tracyWidomF (w : ℝ → ℝ) (s : ℝ) : ℝ :=
  Real.exp (-∫ x in Ioi s, (x - s) * w x ^ 2)

/-! ## Orthogonal polynomials (§32.15) -/

/-- The moments `μ_k(z) = ∫_ℝ ξ^k exp(-ξ⁴/4 - zξ²) dξ` of the weight of DLMF 32.15.1. -/
@[dlmf 32.15.E1]
def freudMoment (z : ℝ) (k : ℕ) : ℝ :=
  ∫ ξ : ℝ, ξ ^ k * Real.exp (-(ξ ^ 4 / 4) - z * ξ ^ 2)

/-- The Hankel determinant `D_n(z) = det[μ_{i+j}(z)]_{0 ≤ i, j < n}` of the moments of the
weight of DLMF 32.15.1 (`D_0 = 1`). -/
def freudHankel (z : ℝ) (n : ℕ) : ℝ :=
  (Matrix.of fun i j : Fin n => freudMoment z (i + j)).det

/-- DLMF 32.15.2: the squared recurrence coefficient `u_n(z) = a_n(z)²` of the orthonormal
polynomials of DLMF 32.15.1, in the classical Hankel-determinant form
`a_n² = D_{n-1}D_{n+1}/D_n²` (`n ≥ 1`; `u_0 = 0`, the convention `a_0 = 0` that makes 32.15.2
also hold for `n = 0` with `p_{-1} = 0`). -/
@[dlmf 32.15.E2]
def freudRecurrenceSq (z : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else freudHankel z (n - 1) * freudHankel z (n + 1) / freudHankel z n ^ 2

/-! ### Picard's solution of PVI (DLMF 32.10.32–32.10.34) -/

/-- The invariant `g₂(z) = (z² - z + 1)/12` of Picard's elliptic function: with
`Λ = 4℘ + (1 + z)/3` the equation `(∂Λ/∂u)² = Λ(Λ - 1)(Λ - z)` of DLMF 32.10.32 becomes
`℘'² = 4℘³ - g₂℘ - g₃`, with roots `e₁ = -(1 + z)/12`, `e₂ = (2 - z)/12`, `e₃ = (2z - 1)/12`. -/
def picardG₂ (z : ℂ) : ℂ := (z ^ 2 - z + 1) / 12

/-- The invariant `g₃(z) = -(1 + z)(2 - z)(2z - 1)/432` of Picard's elliptic function
(see `picardG₂`). -/
def picardG₃ (z : ℂ) : ℂ := -((1 + z) * (2 - z) * (2 * z - 1)) / 432

/-- **Picard's elliptic function** `Λ(u, z)` (DLMF 32.10.32), the inverse of
`u = ∫_0^Λ dt/√(t(t-1)(t-z))`, in Weierstrass form
`Λ(u, z) = 4℘(u + ω₀; g₂(z), g₃(z)) + (1 + z)/3`, where `ω₀` is a half-period with
`℘(ω₀) = e₁ = -(1 + z)/12`, so that `Λ(0, z) = 0`. Meaningful for `z ∉ {0, 1}` (where
`g₂³ ≠ 27g₃²`) and `u + ω₀` off the lattice (the poles of `Λ`). -/
def picardLambda (ω₀ u z : ℂ) : ℂ :=
  4 * DLMF.Weierstrass.weierstrassPInvariants (picardG₂ z) (picardG₃ z) (u + ω₀) + (1 + z) / 3

end DLMF.Painleve
