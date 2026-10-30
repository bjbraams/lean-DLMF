/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.CubicDiscriminant
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Zeros of polynomials: definitions (DLMF §1.11)

Mathlib's `Polynomial` supplies the polynomials, their roots, the division algorithm, the
discriminant `Polynomial.discr` and Descartes' sign changes `Polynomial.signVariations`. This
file adds the few objects of DLMF §1.11 that Mathlib does not name:

* `hornerB f α k` (1.11.2–1.11.4): the coefficients `b_k` of Horner's scheme, `b_0 = f(α)` and
  `b_k` (`k ≥ 1`) the coefficients of the quotient `f /ₘ (X - α)`;
* `hornerC f α k` (1.11.5–1.11.6): the coefficients `c_k` (`k ≥ 1`) of the extended scheme,
  Horner's scheme applied to the quotient;
* `dlmfResolventCubic p q r` (1.11.18): the resolvent cubic `z³ - 2pz² + (p² - 4r)z + q²` of the
  reduced quartic `w⁴ + pw² + qw + r` in DLMF's normalization (TauCeti's
  `TauCeti.resolventCubic` is a different normalization);
* `IsStablePolynomial f` (1.11.24) and the Hurwitz determinants `hurwitzDet f k`
  (1.11.25–1.11.26).
-/

@[expose] public noncomputable section

open Polynomial

namespace DLMF.AlgebraicAnalytic

variable {K : Type*} [Field K]

/-- DLMF 1.11.2–1.11.4, **Horner's scheme**: `hornerB f α 0 = f(α)` and, for `k ≥ 1`,
`hornerB f α k` is the coefficient of `z^{k-1}` in the quotient of `f(z)` by `z - α`, so that
`f(z) = (z - α)(b_n z^{n-1} + ⋯ + b_1) + b_0`. The recurrence 1.11.3 is a theorem
(`DLMF.AlgebraicAnalytic.hornerB_rec`). -/
@[dlmf 1.11.E3]
def hornerB (f : K[X]) (α : K) (k : ℕ) : K :=
  if k = 0 then f.eval α else (f /ₘ (X - C α)).coeff (k - 1)

/-- DLMF 1.11.5, **extended Horner scheme**: `hornerC f α k = c_k` (`k ≥ 1`) is Horner's
scheme for the quotient `f /ₘ (X - α)` (whose coefficients are `b_1, …, b_n`), shifted by one
index, so that `c_n = a_n`, `c_k = α c_{k+1} + b_k` and `c_1 = f'(α)` (1.11.6). -/
@[dlmf 1.11.E5]
def hornerC (f : K[X]) (α : K) (k : ℕ) : K :=
  hornerB (f /ₘ (X - C α)) α (k - 1)

/-- DLMF 1.11.18: the **resolvent cubic** `z³ - 2pz² + (p² - 4r)z + q²` of the reduced quartic
`w⁴ + pw² + qw + r` (1.11.16), as a Mathlib `Cubic`. Its roots are `θ_j = -(α_1 + α_{j+1})²`
for the roots `α_i` of the quartic. -/
@[dlmf 1.11.E18]
def dlmfResolventCubic (p q r : K) : Cubic K :=
  ⟨1, -2 * p, p ^ 2 - 4 * r, q ^ 2⟩

/-- DLMF 1.11.24: a real polynomial `f(z) = a_0 + a_1 z + ⋯ + a_n z^n` is **stable** if all of
its complex zeros have strictly negative real part. (The zero polynomial has no roots in
Mathlib's sense and is stable by this definition; the Hurwitz criterion assumes `a_n ≠ 0`.) -/
@[dlmf 1.11.E24]
def IsStablePolynomial (f : ℝ[X]) : Prop :=
  ∀ z ∈ (f.map (algebraMap ℝ ℂ)).roots, z.re < 0

/-- The coefficient `a_m` of a polynomial at an integer index, with `a_m = 0` for `m < 0`
(and automatically for `m > n`), as used in the Hurwitz determinants (DLMF 1.11.26). -/
def coeffInt {R : Type*} [Semiring R] (f : R[X]) (m : ℤ) : R :=
  if 0 ≤ m then f.coeff m.toNat else 0

/-- DLMF 1.11.26: the `k × k` **Hurwitz matrix** of `f`, whose `j`-th column (`j = 0, …, k-1`)
is `h_k^{(2j+1)}`, the first `k` members of `a_{2j+1}, a_{2j}, a_{2j-1}, …`; that is, its
`(i, j)` entry is `a_{2j+1-i}` (with `a_m = 0` outside `0 ≤ m ≤ n`). -/
@[dlmf 1.11.E26]
def hurwitzMatrix (f : ℝ[X]) (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => coeffInt f (2 * (j : ℤ) + 1 - i)

/-- DLMF 1.11.25–1.11.26: the **Hurwitz determinant** `D_k = det[h_k^{(1)}, h_k^{(3)}, …,
h_k^{(2k-1)}]`. -/
@[dlmf 1.11.E25, dlmf 1.11.E26]
def hurwitzDet (f : ℝ[X]) (k : ℕ) : ℝ :=
  (hurwitzMatrix f k).det

end DLMF.AlgebraicAnalytic
