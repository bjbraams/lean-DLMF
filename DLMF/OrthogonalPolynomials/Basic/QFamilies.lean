/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.Basic.Series

/-!
# The `q`-analogues of the Askey scheme

The canonical definitions of the basic hypergeometric orthogonal polynomials of DLMF §18.27
and §18.28.

## Main definitions

* `terminatingBasicHG`: a terminating basic hypergeometric sum.
* `qHahn`, `bigQJacobi`, `littleQJacobi`, `littleQLaguerre`, `qLaguerre`: DLMF 18.27.3–18.27.15.
* `stieltjesWigert`, `discreteQHermiteI`, `discreteQHermiteII`: DLMF 18.27.18–18.27.23.
* `askeyWilson`, `askeyWilsonLaurent`, `alSalamChihara`: DLMF 18.28.1, 18.28.1_5, 18.28.7.
* `continuousQHermiteLaurent`: the continuous `q`-Hermite polynomial in the Laurent variable
  (DLMF 18.28.16).
* `qRacah`: DLMF 18.28.19.

## Implementation notes

The properties of these families are in `DLMF.OrthogonalPolynomials.QFamilies`.
-/

@[expose] public section

open DLMF.QSeries

noncomputable section

namespace DLMF.OrthogonalPolynomials

/-- Terminating basic hypergeometric sum with the standard integer exponent
`1 + s - r`; in particular this handles both ₁phi₁ and balanced ₄phi₃. -/
def terminatingBasicHG (n : ℕ) (a b : List ℂ) (q z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    (a.map (fun t => qPochhammer t q k)).prod /
      ((b.map (fun t => qPochhammer t q k)).prod * qPochhammer q q k) *
      ((-1 : ℂ) ^ k * q ^ (k * (k - 1) / 2)) ^ (1 + (b.length : ℤ) - a.length) * z ^ k

/-- The `q`-Hahn polynomial `Q_n(x; a, b, N; q)` as a terminating `₃φ₂` (DLMF 18.27.3). -/
@[dlmf 18.27.E3]
def qHahn (a b q : ℂ) (N n : ℕ) (x : ℂ) : ℂ :=
  terminatingBasicHG n [q⁻¹ ^ n, a * b * q ^ (n + 1), x] [a * q, q⁻¹ ^ N] q q

/-- The big `q`-Jacobi polynomial `P_n(x; a, b, c; q)` as a terminating `₃φ₂` (DLMF 18.27.5). -/
@[dlmf 18.27.E5]
def bigQJacobi (a b c q : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  terminatingBasicHG n [q⁻¹ ^ n, a * b * q ^ (n + 1), x] [a * q, c * q] q q

/-- The little `q`-Jacobi polynomial `p_n(x; a, b; q)` as a terminating `₂φ₁` (DLMF 18.27.13). -/
@[dlmf 18.27.E13]
def littleQJacobi (a b q : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  terminatingBasicHG n [q⁻¹ ^ n, a * b * q ^ (n + 1)] [a * q] q (q * x)

/-- The little `q`-Laguerre (Wall) polynomial, the little `q`-Jacobi polynomial with `b = 0`
(DLMF 18.27.14_5). -/
@[dlmf 18.27.E14_5]
def littleQLaguerre (a q : ℂ) (n : ℕ) (x : ℂ) : ℂ := littleQJacobi a 0 q n x

/-- The `q`-Laguerre polynomial `L_n^{(α)}(x; q)` as a terminating `₁φ₁` (DLMF 18.27.15). -/
@[dlmf 18.27.E15]
def qLaguerre (α q : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  qPochhammer (q ^ (α + 1)) q n / qPochhammer q q n *
    terminatingBasicHG n [q⁻¹ ^ n] [q ^ (α + 1)] q (-x * q ^ (n + α + 1))

/-- The Stieltjes–Wigert polynomial `S_n(x; q)` as an explicit finite sum (DLMF 18.27.18). -/
@[dlmf 18.27.E18]
def stieltjesWigert (q : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), q ^ (k ^ 2) * (-x) ^ k /
    (qPochhammer q q k * qPochhammer q q (n - k))

/-- The discrete `q`-Hermite I polynomial `h_n(x; q)` as an explicit finite sum (DLMF 18.27.21). -/
@[dlmf 18.27.E21]
def discreteQHermiteI (q : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  qPochhammer q q n * ∑ k ∈ Finset.range (n / 2 + 1),
    (-1 : ℂ) ^ k * q ^ (k * (k - 1)) * x ^ (n - 2 * k) /
      (qPochhammer (q ^ 2) (q ^ 2) k * qPochhammer q q (n - 2 * k))

/-- The discrete `q`-Hermite II polynomial `h̃_n(x; q)` as an explicit finite sum
(DLMF 18.27.23). -/
@[dlmf 18.27.E23]
def discreteQHermiteII (q : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  qPochhammer q q n * ∑ k ∈ Finset.range (n / 2 + 1),
    (-1 : ℂ) ^ k * q⁻¹ ^ (2 * n * k) * q ^ (k * (2 * k + 1)) * x ^ (n - 2 * k) /
      (qPochhammer (q ^ 2) (q ^ 2) k * qPochhammer q q (n - 2 * k))

/-- Finite polynomial form. The displayed formula requires `a ≠ 0`; claims below
retain that hypothesis rather than assigning continuation values at `a = 0`. -/
@[dlmf 18.28.E1]
def askeyWilson (a b c d q : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  a⁻¹ ^ n * ∑ k ∈ Finset.range (n + 1), q ^ k *
    qPochhammer (a * b * q ^ k) q (n - k) * qPochhammer (a * c * q ^ k) q (n - k) *
    qPochhammer (a * d * q ^ k) q (n - k) * qPochhammer (q⁻¹ ^ n) q k *
    qPochhammer (a * b * c * d * q ^ ((n : ℤ) - 1)) q k / qPochhammer q q k *
    ∏ j ∈ Finset.range k, (1 - 2 * a * q ^ j * x + a ^ 2 * q ^ (2 * j))

/-- The Askey–Wilson polynomial in the Laurent variable `z`, `x = (z + z⁻¹)/2`, as a
terminating `₄φ₃` (DLMF 18.28.1_5). -/
@[dlmf 18.28.E1_5]
def askeyWilsonLaurent (a b c d q : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  terminatingBasicHG n [q⁻¹ ^ n, a * b * c * d * q ^ ((n : ℤ) - 1), a * z, a / z]
    [a * b, a * c, a * d] q q

/-- The Al-Salam–Chihara polynomials, the Askey–Wilson polynomials with `c = d = 0`
(DLMF 18.28.7). -/
@[dlmf 18.28.E7]
def alSalamChihara (a b q : ℂ) (n : ℕ) (x : ℂ) : ℂ := askeyWilson a b 0 0 q n x

/-- Laurent argument `z`, representing the polynomial argument `(z + z⁻¹)/2`. -/
@[dlmf 18.28.E16]
def continuousQHermiteLaurent (q : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  qPochhammer q q n * qGegenbauer 0 q n z

/-- The `q`-Racah polynomial `R_n(x; α, β, γ, δ | q)` as a terminating `₄φ₃` (DLMF 18.28.19). -/
@[dlmf 18.28.E19]
def qRacah (a b c d q : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), q ^ k * qPochhammer (q⁻¹ ^ n) q k *
    qPochhammer (a * b * q ^ (n + 1)) q k /
      (qPochhammer (a * q) q k * qPochhammer (b * d * q) q k *
        qPochhammer (c * q) q k * qPochhammer q q k) *
      ∏ j ∈ Finset.range k, (1 - q ^ j * x + c * d * q ^ (2 * j + 1))
end DLMF.OrthogonalPolynomials
