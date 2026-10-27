/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Means, tridiagonal matrices and infinite determinants (DLMF §§1.2–1.3): definitions

Most of DLMF §§1.2–1.3 is about objects that Mathlib already has (binomial coefficients,
matrices, determinants, norms); the pointers are in
`DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean`. This file defines the few notions that
are not upstream:

* the arithmetic, geometric and harmonic means of finitely many reals (1.2.17–1.2.19) and the
  weighted power mean `M(r)` (1.2.20–1.2.22);
* tridiagonal square matrices (1.2.57);
* the symmetric truncations `D_n[a_{j,k}]` of a doubly infinite matrix, convergence of the
  infinite determinant, and determinants of Hill's type (1.3.18–1.3.19).

The finitely many numbers `a₁, …, aₙ` of DLMF are a family `a : ι → ℝ` over a finite type `ι`;
`n` is `Fintype.card ι`.
-/

@[expose] public noncomputable section

open Finset Filter Topology

namespace DLMF.AlgebraicAnalytic

variable {ι : Type*} [Fintype ι]

/-! ### Means (§1.2(iv)) -/

/-- DLMF 1.2.17: the arithmetic mean `A = (a₁ + ⋯ + aₙ)/n` of finitely many reals. For the
empty family the value is `0` (Lean's `0/0 = 0`). -/
@[dlmf 1.2.E17]
def arithmeticMean (a : ι → ℝ) : ℝ :=
  (∑ i, a i) / Fintype.card ι

/-- DLMF 1.2.18: the geometric mean `G = (a₁ a₂ ⋯ aₙ)^{1/n}`, for positive numbers (DLMF's
domain); the real power `Real.rpow` is used. -/
@[dlmf 1.2.E18]
def geometricMean (a : ι → ℝ) : ℝ :=
  (∏ i, a i) ^ ((1 : ℝ) / Fintype.card ι)

/-- DLMF 1.2.19: the harmonic mean `H`, defined by `1/H = (1/n)(1/a₁ + ⋯ + 1/aₙ)`, for positive
numbers (DLMF's domain). -/
@[dlmf 1.2.E19]
def harmonicMean (a : ι → ℝ) : ℝ :=
  ((∑ i, (a i)⁻¹) / Fintype.card ι)⁻¹

/-- DLMF 1.2.21 and 1.2.22: the weighted power mean
`M(r) = (p₁ a₁^r + ⋯ + pₙ aₙ^r)^{1/r}` of nonnegative numbers `a_j` with positive weights `p_j`,
`p₁ + ⋯ + pₙ = 1` (1.2.20), for real `r ≠ 0`, with the exception `M(r) = 0` when `r < 0` and
`a₁ a₂ ⋯ aₙ = 0` (1.2.22). DLMF leaves `M(0)` undefined; here `M(0)` is the weighted geometric
mean `∏ a_j^{p_j}`, the limit 1.2.26 (an extension by continuity, not part of DLMF's
definition). The hypotheses on `p` and `a` are carried by the theorems, not by the definition. -/
@[dlmf 1.2.E20, dlmf 1.2.E21, dlmf 1.2.E22]
def weightedPowerMean (p a : ι → ℝ) (r : ℝ) : ℝ :=
  if r = 0 then ∏ i, a i ^ p i
  else if r < 0 ∧ ∏ i, a i = 0 then 0
  else (∑ i, p i * a i ^ r) ^ (1 / r)

/-! ### Tridiagonal matrices (§1.2(vi)) -/

/-- DLMF 1.2.57: a square matrix indexed by `Fin n` is tridiagonal if `a_{ij} = 0` for
`|i - j| > 1`. -/
@[dlmf 1.2.E57]
def IsTridiagonal {R : Type*} [Zero R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j : Fin n, 1 < |(i : ℤ) - (j : ℤ)| → A i j = 0

/-! ### Infinite determinants (§1.3(iii)) -/

/-- DLMF 1.3.18: the `(2n+1) × (2n+1)` determinant `D_n[a_{j,k}]` of the entries `a_{j,k}`,
`-n ≤ j, k ≤ n`, of a doubly infinite matrix `a : ℤ → ℤ → R`. The row and column with index
`i : Fin (2n+1)` carry the DLMF index `i - n`. -/
@[dlmf 1.3.E18]
def truncDet {R : Type*} [CommRing R] (a : ℤ → ℤ → R) (n : ℕ) : R :=
  Matrix.det (Matrix.of fun i j : Fin (2 * n + 1) => a ((i : ℤ) - n) ((j : ℤ) - n))

/-- DLMF §1.3(iii): the infinite determinant `D_∞[a_{j,k}]` converges to `L` if
`D_n[a_{j,k}] → L` as `n → ∞`. -/
@[dlmf 1.3.iii]
def HasInfiniteDet {R : Type*} [CommRing R] [TopologicalSpace R] (a : ℤ → ℤ → R) (L : R) :
    Prop :=
  Tendsto (truncDet a) atTop (𝓝 L)

/-- DLMF 1.3.19: a doubly infinite matrix is of Hill's type if
`∑_{j,k=-∞}^{∞} |a_{j,k} - δ_{j,k}|` converges. -/
@[dlmf 1.3.E19]
def IsHillType (a : ℤ → ℤ → ℂ) : Prop :=
  Summable fun jk : ℤ × ℤ => ‖a jk.1 jk.2 - if jk.1 = jk.2 then 1 else 0‖

end DLMF.AlgebraicAnalytic
