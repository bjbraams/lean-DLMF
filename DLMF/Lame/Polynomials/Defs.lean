/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Lame.Basic
public import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Lamé polynomials: explicit construction (DLMF §§29.12, 29.14, 29.15)

For a nonnegative integer order `ν` the Lamé functions `Ec^m_ν`, `m ≤ ν`, and `Es^m_ν`,
`1 ≤ m ≤ ν`, are polynomials in `sn, cn, dn`, of the eight types of Table 29.12.1
(`LamePolyType`): `uE^m_{2n}`, `sE^m_{2n+1}`, `cE^m_{2n+1}`, `dE^m_{2n+1}`, `scE^m_{2n+2}`,
`sdE^m_{2n+2}`, `cdE^m_{2n+2}`, `scdE^m_{2n+3}`, `0 ≤ m ≤ n`.

## Explicit construction (DLMF §29.15)

Following §29.15(i) each polynomial is built from the `(n+1) × (n+1)` tridiagonal matrix
29.15.2 (`lameMatrix`, with the `α_p, β_p, γ_p` of the type's recurrence, `LameRecurrence`):

* `H_m` is the `m`th smallest root of the characteristic polynomial (`lameMatrixEigenvalue`,
  the roots sorted increasingly; 29.15.3 says they are real and distinct);
* the eigenvector is computed by forward recursion from the first `n` rows of `M v = H v`
  starting with `v₀ = 1` (`lameRecVec`; all `α_p`, `p < n`, are nonzero for these orders and
  `0 < k`), then scaled to satisfy the normalization (29.15.5, 29.15.10, …) and the sign
  condition (29.15.6, 29.15.11, …) of its type (`lamePolyCoeff`);
* the function is the Chebyshev series 29.15.43–29.15.50 in `sn(z, k)` (`lamePolyEk`), with
  the project's complex `sn, cn, dn` (`DLMF.JacobiElliptic.jacobiSnk` etc.) and Mathlib's
  `Polynomial.Chebyshev.T`, `U`.

No choice is involved. The identification with the eigenfunctions `Ec`, `Es` of §29.3
(29.12.1–29.12.8) and of `½(H_m + ν(ν+1)k²)` with the eigenvalues (29.15.7, …) are theorems
in `DLMF.Lame.Polynomials`.

The inner product of §29.14 (`lameInner`, weight `lameOrthWeight`, 29.14.2–29.14.3) is also
defined here.
-/

@[expose] public section

open Complex DLMF.JacobiElliptic DLMF.Elliptic Polynomial
open scoped Real

noncomputable section

namespace DLMF.Lame

/-- The eight types of Lamé polynomials of DLMF Table 29.12.1. -/
inductive LamePolyType
  | uE | sE | cE | dE | scE | sdE | cdE | scdE
  deriving DecidableEq

namespace LamePolyType

/-- The three-term recurrence (§§29.3(iii), 29.6) whose truncation gives the Fourier or
Chebyshev coefficients of a Lamé polynomial type (DLMF §29.15(i)). -/
def recurrence : LamePolyType → LameRecurrence
  | uE => .A0 | sE => .A1 | cE => .B1 | dE => .C0
  | scE => .B2 | sdE => .C1 | cdE => .D1 | scdE => .D2

/-- The order `ν` of the Lamé polynomial of type `t` with index `n` (Table 29.12.1):
`2n`, `2n+1` (`sE, cE, dE`), `2n+2` (`scE, sdE, cdE`) or `2n+3` (`scdE`). -/
def order : LamePolyType → ℕ → ℕ
  | uE, n => 2 * n
  | sE, n => 2 * n + 1 | cE, n => 2 * n + 1 | dE, n => 2 * n + 1
  | scE, n => 2 * n + 2 | sdE, n => 2 * n + 2 | cdE, n => 2 * n + 2
  | scdE, n => 2 * n + 3

/-- The normalization quadratic form of the coefficient vector `c₀, …, cₙ` (DLMF 29.15.5,
29.15.10, 29.15.15, 29.15.20, 29.15.25, 29.15.30, 29.15.35, 29.15.40); the normalization is
`t.normForm k n c = 1`. -/
@[dlmf 29.15.E5, dlmf 29.15.E10, dlmf 29.15.E15, dlmf 29.15.E20, dlmf 29.15.E25,
  dlmf 29.15.E30, dlmf 29.15.E35, dlmf 29.15.E40]
def normForm (t : LamePolyType) (k : ℝ) (n : ℕ) (c : ℕ → ℝ) : ℝ :=
  let sq := ∑ p ∈ Finset.range (n + 1), c p ^ 2
  let cross := ∑ p ∈ Finset.range n, c p * c (p + 1)
  match t with
  | uE => c 0 ^ 2 / 2 + (sq - c 0 ^ 2)
  | sE => sq | cE => sq | scE => sq
  | dE => (1 - k ^ 2 / 2) * (c 0 ^ 2 / 2 + (sq - c 0 ^ 2)) - k ^ 2 / 2 * cross
  | sdE => (1 - k ^ 2 / 2) * sq - k ^ 2 / 2 * (c 0 ^ 2 / 2 + cross)
  | cdE => (1 - k ^ 2 / 2) * sq + k ^ 2 / 2 * (c 0 ^ 2 / 2 - cross)
  | scdE => (1 - k ^ 2 / 2) * sq - k ^ 2 / 2 * cross

/-- The linear form of the sign condition (DLMF 29.15.6, 29.15.11, 29.15.16, 29.15.21,
29.15.26, 29.15.31, 29.15.36, 29.15.41); the condition is `0 < t.signForm n c`. -/
@[dlmf 29.15.E6, dlmf 29.15.E11, dlmf 29.15.E16, dlmf 29.15.E21, dlmf 29.15.E26,
  dlmf 29.15.E31, dlmf 29.15.E36, dlmf 29.15.E41]
def signForm (t : LamePolyType) (n : ℕ) (c : ℕ → ℝ) : ℝ :=
  match t with
  | uE | dE => c 0 / 2 + ∑ p ∈ Finset.Ioc 0 n, c p
  | sE | sdE => ∑ p ∈ Finset.range (n + 1), c p
  | cE | cdE => ∑ p ∈ Finset.range (n + 1), (2 * p + 1 : ℝ) * c p
  | scE | scdE => ∑ p ∈ Finset.range (n + 1), (2 * p + 2 : ℝ) * c p

/-- The prefactor of the Chebyshev series of type `t` (DLMF 29.15.43–29.15.50): `1`, `1`,
`cn`, `dn`, `cn`, `dn`, `cn dn`, `cn dn`. -/
def prefactor : LamePolyType → ℂ → ℂ → ℂ
  | uE, _, _ => 1
  | sE, _, _ => 1
  | cE, z, k => jacobiCnk z k
  | dE, z, k => jacobiDnk z k
  | scE, z, k => jacobiCnk z k
  | sdE, z, k => jacobiDnk z k
  | cdE, z, k => jacobiCnk z k * jacobiDnk z k
  | scdE, z, k => jacobiCnk z k * jacobiDnk z k

/-- The `p`th Chebyshev basis function of type `t` at `s = sn(z, k)` (DLMF 29.15.43–29.15.50):
`½T₀, T_{2p}` (`uE`, `dE`), `T_{2p+1}` (`sE`, `sdE`), `U_{2p}` (`cE`, `cdE`), `U_{2p+1}`
(`scE`, `scdE`). -/
def basis : LamePolyType → ℕ → ℂ → ℂ
  | uE, p, s => (if p = 0 then 1 / 2 else 1) * (Chebyshev.T ℂ (2 * p : ℕ)).eval s
  | dE, p, s => (if p = 0 then 1 / 2 else 1) * (Chebyshev.T ℂ (2 * p : ℕ)).eval s
  | sE, p, s => (Chebyshev.T ℂ (2 * p + 1 : ℕ)).eval s
  | sdE, p, s => (Chebyshev.T ℂ (2 * p + 1 : ℕ)).eval s
  | cE, p, s => (Chebyshev.U ℂ (2 * p : ℕ)).eval s
  | cdE, p, s => (Chebyshev.U ℂ (2 * p : ℕ)).eval s
  | scE, p, s => (Chebyshev.U ℂ (2 * p + 1 : ℕ)).eval s
  | scdE, p, s => (Chebyshev.U ℂ (2 * p + 1 : ℕ)).eval s

end LamePolyType

/-- The `(n+1) × (n+1)` tridiagonal matrix of DLMF 29.15.2 for the recurrence `r`:
`β_p` on the diagonal, `α_p` above and `γ_p` below it (row `p`, `0 ≤ p ≤ n`). -/
@[dlmf 29.15.E2]
def lameMatrix (r : LameRecurrence) (ν k : ℝ) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j =>
    if (j : ℕ) = i + 1 then r.alpha ν k i
    else if (j : ℕ) = i then r.beta ν k i
    else if (j : ℕ) + 1 = i then r.gamma ν k i
    else 0

/-- The `m`th smallest eigenvalue `H_m` of the matrix 29.15.2: the `m`th element (from `0`) of
the increasingly sorted list of roots of its characteristic polynomial (junk `0` past the end).
DLMF 29.15.3 states that the eigenvalues are real and simple. -/
def lameMatrixEigenvalue (r : LameRecurrence) (ν k : ℝ) (n m : ℕ) : ℝ :=
  ((lameMatrix r ν k n).charpoly.roots.sort (· ≤ ·)).getD m 0

/-- The pair `(v_{p-1}, v_p)` of the forward recursion for an eigenvector of 29.15.2:
`v₋₁ = 0`, `v₀ = 1`, `v_{p+1} = ((H - β_p)v_p - γ_p v_{p-1})/α_p` (rows `p` of `M v = H v`). -/
def lameRecVecPair (r : LameRecurrence) (ν k H : ℝ) : ℕ → ℝ × ℝ
  | 0 => (0, 1)
  | p + 1 =>
      ((lameRecVecPair r ν k H p).2,
        ((H - r.beta ν k p) * (lameRecVecPair r ν k H p).2 -
          r.gamma ν k p * (lameRecVecPair r ν k H p).1) / r.alpha ν k p)

/-- The unnormalized eigenvector `v_p` of 29.15.2 by forward recursion from `v₀ = 1`. -/
def lameRecVec (r : LameRecurrence) (ν k H : ℝ) (p : ℕ) : ℝ := (lameRecVecPair r ν k H p).2

/-- The eigenvalue `H_m` of the matrix 29.15.2 for the Lamé polynomial of type `t`, index `n`
(order `ν = t.order n`) and modulus `k`. -/
def lamePolyH (t : LamePolyType) (n m : ℕ) (k : ℝ) : ℝ :=
  lameMatrixEigenvalue t.recurrence (t.order n) k n m

/-- The normalized coefficients `c_p`, `0 ≤ p ≤ n` (`0` for `p > n`), of the Lamé polynomial
of type `t` (DLMF 29.15.4, 29.15.9, 29.15.14, 29.15.19, 29.15.24, 29.15.29, 29.15.34,
29.15.39): the eigenvector for `H_m`, scaled to satisfy the normalization `t.normForm = 1` and
the sign condition `t.signForm > 0`. For `uE` these are `A₀, A₂, …, A_{2n}`; for `sE`
`A₁, …, A_{2n+1}`; for `cE` `B₁, …`; for `dE` `C₀, …`; for `scE` `B₂, …`; for `sdE` `C₁, …`;
for `cdE` `D₁, …`; for `scdE` `D₂, …`. -/
@[dlmf 29.15.E4, dlmf 29.15.E9, dlmf 29.15.E14, dlmf 29.15.E19, dlmf 29.15.E24,
  dlmf 29.15.E29, dlmf 29.15.E34, dlmf 29.15.E39]
def lamePolyCoeff (t : LamePolyType) (n m : ℕ) (k : ℝ) (p : ℕ) : ℝ :=
  if p ≤ n then
    (if t.signForm n (lameRecVec t.recurrence (t.order n) k (lamePolyH t n m k)) < 0 then -1
      else 1) * lameRecVec t.recurrence (t.order n) k (lamePolyH t n m k) p /
      Real.sqrt (t.normForm k n (lameRecVec t.recurrence (t.order n) k (lamePolyH t n m k)))
  else 0

/-- The Lamé polynomial of type `t`, index `n` and number of zeros `m` in `(0, K)`, as an
explicit Chebyshev series in `sn(z, k)` (DLMF 29.15.43–29.15.50):
`prefactor(z) · ∑_{p=0}^n c_p basis_p(sn(z, k))`. -/
def lamePolyEk (t : LamePolyType) (n m : ℕ) (z : ℂ) (k : ℝ) : ℂ :=
  t.prefactor z k *
    ∑ p ∈ Finset.range (n + 1), (lamePolyCoeff t n m k p : ℂ) * t.basis p (jacobiSnk z k)

/-- `uE^m_{2n}(z, k²) = ½A₀ + ∑_{p=1}^n A_{2p} T_{2p}(sn(z, k))` (DLMF 29.15.43). -/
@[dlmf 29.15.E43]
def lameUEk (n m : ℕ) (z : ℂ) (k : ℝ) : ℂ := lamePolyEk .uE n m z k

/-- `sE^m_{2n+1}(z, k²) = ∑_{p=0}^n A_{2p+1} T_{2p+1}(sn(z, k))` (DLMF 29.15.44). -/
@[dlmf 29.15.E44]
def lameSEk (n m : ℕ) (z : ℂ) (k : ℝ) : ℂ := lamePolyEk .sE n m z k

/-- `cE^m_{2n+1}(z, k²) = cn(z, k) ∑_{p=0}^n B_{2p+1} U_{2p}(sn(z, k))` (DLMF 29.15.45). -/
@[dlmf 29.15.E45]
def lameCEk (n m : ℕ) (z : ℂ) (k : ℝ) : ℂ := lamePolyEk .cE n m z k

/-- `dE^m_{2n+1}(z, k²) = dn(z, k)(½C₀ + ∑_{p=1}^n C_{2p} T_{2p}(sn(z, k)))` (DLMF 29.15.46). -/
@[dlmf 29.15.E46]
def lameDEk (n m : ℕ) (z : ℂ) (k : ℝ) : ℂ := lamePolyEk .dE n m z k

/-- `scE^m_{2n+2}(z, k²) = cn(z, k) ∑_{p=0}^n B_{2p+2} U_{2p+1}(sn(z, k))` (DLMF 29.15.47). -/
@[dlmf 29.15.E47]
def lameSCEk (n m : ℕ) (z : ℂ) (k : ℝ) : ℂ := lamePolyEk .scE n m z k

/-- `sdE^m_{2n+2}(z, k²) = dn(z, k) ∑_{p=0}^n C_{2p+1} T_{2p+1}(sn(z, k))` (DLMF 29.15.48). -/
@[dlmf 29.15.E48]
def lameSDEk (n m : ℕ) (z : ℂ) (k : ℝ) : ℂ := lamePolyEk .sdE n m z k

/-- `cdE^m_{2n+2}(z, k²) = cn(z, k) dn(z, k) ∑_{p=0}^n D_{2p+1} U_{2p}(sn(z, k))`
(DLMF 29.15.49). -/
@[dlmf 29.15.E49]
def lameCDEk (n m : ℕ) (z : ℂ) (k : ℝ) : ℂ := lamePolyEk .cdE n m z k

/-- `scdE^m_{2n+3}(z, k²) = cn(z, k) dn(z, k) ∑_{p=0}^n D_{2p+2} U_{2p+1}(sn(z, k))`
(DLMF 29.15.50). -/
@[dlmf 29.15.E50]
def lameSCDEk (n m : ℕ) (z : ℂ) (k : ℝ) : ℂ := lamePolyEk .scdE n m z k

/-! ### The inner product of §29.14 -/

/-- The weight `w(s, t) = sn²(K + it, k) - sn²(s, k)` of DLMF 29.14.3 (real `s, t`; it is real
and nonnegative on `[0, K] × [0, K']`). -/
@[dlmf 29.14.E3]
def lameOrthWeight (k s t : ℝ) : ℂ :=
  jacobiSnk ((Real.compEllIntKm (k ^ 2) : ℂ) + I * t) k ^ 2 - jacobiSnk s k ^ 2

/-- The inner product `⟨g, h⟩ = ∫₀^a ∫₀^b w(s, t) g(s, t) h(s, t) dt ds` of DLMF 29.14.2
(`a = K`, `b = K'`) and 29.14.11 (`a = 4K`, `b = 2K'`); no complex conjugation, as in DLMF. -/
@[dlmf 29.14.E2, dlmf 29.14.E11]
def lameInner (k a b : ℝ) (g h : ℝ → ℝ → ℂ) : ℂ :=
  ∫ s in (0 : ℝ)..a, ∫ t in (0 : ℝ)..b, lameOrthWeight k s t * g s t * h s t

/-- The product `E(s, k²) E(K + it, k²)` of a Lamé polynomial of type `t` at `s` and at
`K + it` (DLMF 29.14.1, 29.14.4–29.14.10). -/
@[dlmf 29.14.E1, dlmf 29.14.E4, dlmf 29.14.E5, dlmf 29.14.E6, dlmf 29.14.E7, dlmf 29.14.E8,
  dlmf 29.14.E9, dlmf 29.14.E10]
def lameProduct (t : LamePolyType) (n m : ℕ) (k : ℝ) (s τ : ℝ) : ℂ :=
  lamePolyEk t n m s k * lamePolyEk t n m ((Real.compEllIntKm (k ^ 2) : ℂ) + I * τ) k

end DLMF.Lame
