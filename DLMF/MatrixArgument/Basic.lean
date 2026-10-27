/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Lebesgue
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.Algebra.Star.Real

/-!
# Functions of matrix argument: definitions (DLMF Chapter 35)

This file holds the definitions of DLMF Chapter 35 (namespace `DLMF.MatrixArgument`).

## Notation of §35.1

* Matrices are `Matrix (Fin m) (Fin m) ℝ`. The space `𝓢` of real symmetric matrices is Tau
  Ceti's `selfAdjoint.submodule ℝ (Matrix (Fin m) (Fin m) ℝ)` (abbreviation `SymMatrix m`), and
  DLMF's `dX = ∏_{j ≤ k} dx_{j,k}` is Tau Ceti's `TauCeti.symmetricLebesgue m`, the push-forward
  of Lebesgue measure on the `m(m+1)/2` upper-triangular coordinates. With this normalization
  Tau Ceti proves `∫_Ω etr(-X) |X|^{a-(m+1)/2} dX = Γ_m(a)` (DLMF 35.3.1, real `a`).
* `Ω` is `posDefCone m`, and DLMF's matrix interval `S < X < T` is `matrixInterval S T`.
* `etr X = exp(tr X)` is `etr`; `|(X)_j|` is `leadingMinor X j`; the spectral norm `‖T‖` is
  `matrixSpectralNorm T`.
* The orthogonal group `O(m)` is Mathlib's `Matrix.orthogonalGroup (Fin m) ℝ`. It is compact
  (`instCompactSpaceOrthogonalGroup`), and its normalized Haar measure `dH` is
  `orthogonalHaar m`, the Haar measure giving the whole group mass `1`.
* Integrals with a convergence claim use `HasIntegralOn s f I`: `f` is integrable on `s` for
  `dX` and its integral is `I`, so the Lean convention that a non-integrable function has
  integral `0` never enters a statement.

## Partitions and zonal polynomials (§35.4)

* A partition `κ = (k₁, …, k_m)` is a nonincreasing vector `κ : Fin m → ℕ` (DLMF's definition,
  with at most `m` nonzero parts); `partitions m k` is the finite set of partitions of weight
  `|κ| = k`, and `partitionLength κ` is `ℓ(κ)`.
* `partitionalShiftedFactorial a κ = [a]_κ = ∏_j (a - (j-1)/2)_{k_j}` (35.4.1), over any field.
* `zonalPolynomialAtOne κ` is the right-hand side of 35.4.2, and `zonalPolynomial κ T` is the
  defining integral 35.4.3 over `O(m)`, for every real matrix `T`. This is DLMF's own definition
  (35.4.2–35.4.3), so it is honest; the properties of §35.4(ii) are theorems. The two factors
  `|T|^{k_m}` and `∏_{j<m} |(HTH⁻¹)_j|^{k_j - k_{j+1}}` of 35.4.3 are combined as
  `∏_{j=1}^{m} |(HTHᵀ)_j|^{k_j - k_{j+1}}` with `k_{m+1} = 0`, using `|HTHᵀ| = |T|`.
* DLMF's `Z_κ` is a function on `𝓢`. Where DLMF evaluates a function of matrix argument at a
  product such as `TX` with `X ∈ Ω`, meaning the function of the (real) eigenvalues of `TX`,
  the statements use the symmetric matrix `X^{1/2} T X^{1/2}` (`CFC.sqrt X * T * CFC.sqrt X`),
  which has the same eigenvalues.

## Functions (§§35.3, 35.5–35.8)

* `multivariateGamma m a` (35.3.4, the product formula; it is the meromorphic continuation of
  the integral 35.3.1), `multivariateGammaVec m s` (35.3.5), `multivariateBeta m a b` (35.3.7).
  Tau Ceti's real `TauCeti.multivariateGamma` agrees on real arguments.
* `hypergeometricPFQ a b T` (35.8.1), the series over partitions with the Lean `tsum`
  totalization in the weight `k`, and its special cases `hyp0F0`, `hyp1F0`, `hyp0F1`, `hyp1F1`
  (35.6.1), `hyp2F1` (35.7.1), `hyp3F2`.
* `besselA ν T` (35.5.1–35.5.2), `besselB ν T` (35.5.3), `kummerPsi a b T` (35.6.2),
  `laguerreL γ ν T` (35.6.3), `jacobiP γ δ ν T` (35.7.2), `laplaceTransform f Z` (35.2.1) and
  `matrixConvolution f₁ f₂ T` (35.2.3).
-/

@[expose] public noncomputable section

open MeasureTheory Matrix Finset
open scoped Nat

namespace DLMF.MatrixArgument

/-! ## The spaces `𝓢`, `Ω` and the measure `dX` -/

/-- DLMF §35.1: the space `𝓢` of real symmetric `m × m` matrices, as Tau Ceti's self-adjoint
submodule. Its measure `dX = ∏_{j ≤ k} dx_{j,k}` is `TauCeti.symmetricLebesgue m`. -/
abbrev SymMatrix (m : ℕ) : Type := selfAdjoint.submodule ℝ (Matrix (Fin m) (Fin m) ℝ)

/-- DLMF §35.1: the cone `Ω` of positive-definite real symmetric matrices, as a subset of `𝓢`. -/
@[dlmf 35.1]
def posDefCone (m : ℕ) : Set (SymMatrix m) :=
  {X | (X : Matrix (Fin m) (Fin m) ℝ).PosDef}

/-- DLMF §35.1: the matrix interval `S < X < T`, that is `X - S` and `T - X` positive definite,
as a subset of `𝓢`. DLMF's `0 < X < T` is `matrixInterval 0 T`. -/
def matrixInterval {m : ℕ} (S T : Matrix (Fin m) (Fin m) ℝ) : Set (SymMatrix m) :=
  {X | ((X : Matrix (Fin m) (Fin m) ℝ) - S).PosDef ∧ (T - (X : Matrix (Fin m) (Fin m) ℝ)).PosDef}

/-- `HasIntegralOn s f I`: the complex function `f` of a symmetric matrix is integrable on
`s ⊆ 𝓢` for `dX` (`TauCeti.symmetricLebesgue m`) and its integral is `I`. -/
def HasIntegralOn {m : ℕ} (s : Set (SymMatrix m)) (f : Matrix (Fin m) (Fin m) ℝ → ℂ)
    (I : ℂ) : Prop :=
  IntegrableOn (fun X : SymMatrix m => f X) s (TauCeti.symmetricLebesgue m) ∧
    ∫ X in s, f X ∂TauCeti.symmetricLebesgue m = I

/-- DLMF §35.1: `etr(X) = exp(tr X)`. -/
def etr {m : ℕ} (X : Matrix (Fin m) (Fin m) ℝ) : ℝ := Real.exp X.trace

/-- DLMF §35.1: the `j`th (leading) principal minor `|(X)_j|`, the determinant of the upper-left
`j × j` block of `X`; it is `1` for `j = 0` and (by convention here) `0` for `j > m`. -/
def leadingMinor {R : Type*} [CommRing R] {m : ℕ} (X : Matrix (Fin m) (Fin m) R) (j : ℕ) : R :=
  if h : j ≤ m then (X.submatrix (Fin.castLE h) (Fin.castLE h)).det else 0

/-- DLMF §35.1: the spectral norm `‖T‖`, the operator norm of `T` acting on Euclidean space
(for symmetric `T`, the largest absolute value of an eigenvalue). -/
def matrixSpectralNorm {m : ℕ} (T : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin T)‖

/-- The complex symmetric matrix with upper-triangular entries `z`; used to state analyticity
of a Laplace transform in the independent entries `z_{j,k}` (`j ≤ k`) of `𝐙` (DLMF 35.2). -/
def complexSymmetricOfCoords {m : ℕ} (z : TauCeti.upperTriangle m → ℂ) :
    Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j => if h : i ≤ j then z ⟨(i, j), h⟩ else z ⟨(j, i), le_of_not_ge h⟩

/-! ## The orthogonal group and its Haar measure -/

/-- The orthogonal group `O(m)` is compact: it is closed and its entries are bounded by `1`. -/
instance instCompactSpaceOrthogonalGroup (m : ℕ) :
    CompactSpace (Matrix.orthogonalGroup (Fin m) ℝ) := by
  refine isCompact_iff_compactSpace.mp ?_
  have hK : IsCompact ((Set.pi Set.univ fun _ : Fin m =>
      Set.pi Set.univ fun _ : Fin m => Set.Icc (-1 : ℝ) 1) : Set (Matrix (Fin m) (Fin m) ℝ)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  refine hK.of_isClosed_subset (isClosed_unitary (R := Matrix (Fin m) (Fin m) ℝ)) ?_
  intro U hU i _ j _
  have h := entry_norm_bound_of_unitary hU i j
  rw [Real.norm_eq_abs] at h
  exact abs_le.mp h

/-- DLMF §35.1: the normalized Haar measure `dH` on `O(m)`, the Haar measure for which the
whole (compact) group has measure `1`. -/
@[dlmf 35.1]
def orthogonalHaar (m : ℕ) : Measure (Matrix.orthogonalGroup (Fin m) ℝ) :=
  Measure.haarMeasure ⊤

/-! ## Partitions and the partitional shifted factorial -/

/-- DLMF 35.4(i): the partitions `κ = (k₁, …, k_m)` (nonincreasing vectors of nonnegative
integers) of weight `|κ| = k₁ + ⋯ + k_m = k`. Every part is at most `k`. -/
@[dlmf 35.4.i]
def partitions (m k : ℕ) : Finset (Fin m → ℕ) :=
  (Fintype.piFinset fun _ : Fin m => Finset.range (k + 1)).filter fun κ =>
    (∀ i j : Fin m, i ≤ j → κ j ≤ κ i) ∧ ∑ j, κ j = k

/-- DLMF 35.4(i): the length `ℓ(κ)`, the number of nonzero parts of `κ`. -/
def partitionLength {m : ℕ} (κ : Fin m → ℕ) : ℕ :=
  (Finset.univ.filter fun j : Fin m => κ j ≠ 0).card

/-- The part `k_{j+2}` following the part `κ j = k_{j+1}` (with `j` zero-based), and `0` after
the last part: `k_{m+1} = 0`. -/
def nextPart {m : ℕ} (κ : Fin m → ℕ) (j : Fin m) : ℕ :=
  if h : j.1 + 1 < m then κ ⟨j.1 + 1, h⟩ else 0

/-- DLMF 35.4.1: the partitional shifted factorial `[a]_κ = ∏_{j=1}^{m} (a - (j-1)/2)_{k_j}`,
over any field (in Lean the index `j` is zero-based, so the shift is `j / 2`). -/
@[dlmf 35.4.E1]
def partitionalShiftedFactorial {𝕜 : Type*} [Field 𝕜] {m : ℕ} (a : 𝕜) (κ : Fin m → ℕ) : 𝕜 :=
  ∏ j : Fin m, (ascPochhammer 𝕜 (κ j)).eval (a - (j : 𝕜) / 2)

/-! ## Multivariate gamma and beta functions -/

/-- DLMF 35.3.4: the multivariate gamma function
`Γ_m(a) = π^{m(m-1)/4} ∏_{j=1}^{m} Γ(a - (j-1)/2)`. This product is the meromorphic
continuation of the integral 35.3.1 (`multivariateGamma_eq_integral`, `ℜa > (m-1)/2`); it
agrees with Tau Ceti's real `TauCeti.multivariateGamma` on real arguments. -/
@[dlmf 35.3.E4]
def multivariateGamma (m : ℕ) (a : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (((m : ℂ) * ((m : ℂ) - 1)) / 4) *
    ∏ j : Fin m, Complex.Gamma (a - (j : ℂ) / 2)

/-- DLMF 35.3.5: the generalized multivariate gamma function
`Γ_m(s₁, …, s_m) = π^{m(m-1)/4} ∏_{j=1}^{m} Γ(s_j - (j-1)/2)`, the continuation of the
integral 35.3.2. -/
@[dlmf 35.3.E5]
def multivariateGammaVec (m : ℕ) (s : Fin m → ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (((m : ℂ) * ((m : ℂ) - 1)) / 4) *
    ∏ j : Fin m, Complex.Gamma (s j - (j : ℂ) / 2)

/-- DLMF 35.3.7: the multivariate beta function `B_m(a, b) = Γ_m(a) Γ_m(b) / Γ_m(a + b)`; for
`ℜa, ℜb > (m-1)/2` it is the integral 35.3.3 (`multivariateBeta_eq_integral`). -/
@[dlmf 35.3.E7]
def multivariateBeta (m : ℕ) (a b : ℂ) : ℂ :=
  multivariateGamma m a * multivariateGamma m b / multivariateGamma m (a + b)

/-! ## Zonal polynomials -/

/-- DLMF 35.4.2: the value
`Z_κ(I) = |κ|! 2^{2|κ|} [m/2]_κ ∏_{1≤j<l≤ℓ} (2k_j - 2k_l - j + l) / ∏_{j=1}^{ℓ} (2k_j + ℓ - j)!`
(indices zero-based in Lean; the factor `2k_j - 2k_l - j + l` is unchanged by the shift and the
factorial is `(2k_j + ℓ - 1 - j)!`). -/
@[dlmf 35.4.E2]
def zonalPolynomialAtOne {m : ℕ} (κ : Fin m → ℕ) : ℝ :=
  ((∑ j, κ j)! : ℝ) * 2 ^ (2 * ∑ j, κ j) * partitionalShiftedFactorial ((m : ℝ) / 2) κ *
    (∏ j : Fin m, ∏ l : Fin m,
        if j < l ∧ l.1 < partitionLength κ then
          (2 * (κ j : ℝ) - 2 * (κ l : ℝ) - (j : ℝ) + (l : ℝ)) else 1) /
    ∏ j : Fin m, if j.1 < partitionLength κ then
        (((2 * κ j + partitionLength κ - 1 - j.1)! : ℕ) : ℝ) else 1

/-- DLMF 35.4.3: the zonal polynomial
`Z_κ(T) = Z_κ(I) |T|^{k_m} ∫_{O(m)} ∏_{j=1}^{m-1} |(HTH⁻¹)_j|^{k_j - k_{j+1}} dH`, written as
`Z_κ(I) ∫_{O(m)} ∏_{j=1}^{m} |(HTHᵀ)_j|^{k_j - k_{j+1}} dH` with `k_{m+1} = 0` (the factor
`j = m` is `|HTHᵀ|^{k_m} = |T|^{k_m}`; see `zonalPolynomial_eq_dlmf`). DLMF defines `Z_κ` on
`𝓢` and for partitions `κ`; the formula is evaluated here for every real matrix `T` and every
`κ`, and is meaningful for symmetric `T` and nonincreasing `κ`. -/
@[dlmf 35.4.E3]
def zonalPolynomial {m : ℕ} (κ : Fin m → ℕ) (T : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  zonalPolynomialAtOne κ *
    ∫ H, ∏ j : Fin m,
      leadingMinor ((H : Matrix (Fin m) (Fin m) ℝ) * T * (H : Matrix (Fin m) (Fin m) ℝ)ᵀ)
        (j.1 + 1) ^ (κ j - nextPart κ j) ∂orthogonalHaar m

/-! ## Hypergeometric functions of matrix argument -/

/-- DLMF 35.8.1: the generalized hypergeometric function of matrix argument
`pFq(a; b; T) = ∑_{k=0}^∞ (1/k!) ∑_{|κ|=k} [a₁]_κ ⋯ [a_p]_κ / ([b₁]_κ ⋯ [b_q]_κ) Z_κ(T)`,
as the Lean `tsum` over `k` of the finite sums over partitions of weight `k` (so it is `0` where
the series in `k` diverges; convergence is §35.8(i)). DLMF requires
`-b_j + (k+1)/2 ∉ ℕ` (`1 ≤ k ≤ m`), which is where no `[b_j]_κ` vanishes; otherwise the Lean
quotient `x / 0 = 0` applies. Meaningful for symmetric `T`. -/
@[dlmf 35.8.E1]
def hypergeometricPFQ {m p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ)
    (T : Matrix (Fin m) (Fin m) ℝ) : ℂ :=
  ∑' k : ℕ, (1 / (k ! : ℂ)) * ∑ κ ∈ partitions m k,
    (∏ i, partitionalShiftedFactorial (a i) κ) / (∏ j, partitionalShiftedFactorial (b j) κ) *
      (zonalPolynomial κ T : ℂ)

/-- DLMF 35.8.2: `₀F₀(−; −; T)` of matrix argument. -/
def hyp0F0 {m : ℕ} (T : Matrix (Fin m) (Fin m) ℝ) : ℂ := hypergeometricPFQ ![] ![] T

/-- DLMF 35.8.3: `₁F₀(a; −; T)` of matrix argument. -/
def hyp1F0 {m : ℕ} (a : ℂ) (T : Matrix (Fin m) (Fin m) ℝ) : ℂ := hypergeometricPFQ ![a] ![] T

/-- DLMF 35.8.4: `₀F₁(−; b; T)` of matrix argument. -/
def hyp0F1 {m : ℕ} (b : ℂ) (T : Matrix (Fin m) (Fin m) ℝ) : ℂ := hypergeometricPFQ ![] ![b] T

/-- DLMF 35.6.1: the confluent hypergeometric function of matrix argument
`₁F₁(a; b; T) = ∑_k (1/k!) ∑_{|κ|=k} [a]_κ / [b]_κ Z_κ(T)`. -/
@[dlmf 35.6.E1]
def hyp1F1 {m : ℕ} (a b : ℂ) (T : Matrix (Fin m) (Fin m) ℝ) : ℂ :=
  hypergeometricPFQ ![a] ![b] T

/-- DLMF 35.7.1: the Gaussian hypergeometric function of matrix argument
`₂F₁(a, b; c; T) = ∑_k (1/k!) ∑_{|κ|=k} [a]_κ [b]_κ / [c]_κ Z_κ(T)`; DLMF requires
`-c + (j+1)/2 ∉ ℕ` (`1 ≤ j ≤ m`) and `‖T‖ < 1`. -/
@[dlmf 35.7.E1]
def hyp2F1 {m : ℕ} (a b c : ℂ) (T : Matrix (Fin m) (Fin m) ℝ) : ℂ :=
  hypergeometricPFQ ![a, b] ![c] T

/-- DLMF §35.8(iii): `₃F₂(a₁, a₂, a₃; b₁, b₂; T)` of matrix argument. -/
def hyp3F2 {m : ℕ} (a₁ a₂ a₃ b₁ b₂ : ℂ) (T : Matrix (Fin m) (Fin m) ℝ) : ℂ :=
  hypergeometricPFQ ![a₁, a₂, a₃] ![b₁, b₂] T

/-! ## Bessel functions and the confluent function `Ψ` -/

/-- DLMF 35.5.1–35.5.2: the Bessel function of the first kind of matrix argument
`A_ν(T) = A_ν(0) ∑_k ((-1)^k / k!) ∑_{|κ|=k} Z_κ(T) / [ν + (m+1)/2]_κ` with
`A_ν(0) = 1 / Γ_m(ν + (m+1)/2)` (`ν ∈ ℂ`, `T ∈ 𝓢`). -/
@[dlmf 35.5.E2]
def besselA {m : ℕ} (ν : ℂ) (T : Matrix (Fin m) (Fin m) ℝ) : ℂ :=
  1 / multivariateGamma m (ν + ((m : ℂ) + 1) / 2) *
    ∑' k : ℕ, ((-1) ^ k / (k ! : ℂ)) * ∑ κ ∈ partitions m k,
      1 / partitionalShiftedFactorial (ν + ((m : ℂ) + 1) / 2) κ * (zonalPolynomial κ T : ℂ)

/-- DLMF 35.5.3: the Bessel function of the second kind of matrix argument
`B_ν(T) = ∫_Ω etr(-(TX + X⁻¹)) |X|^{ν-(m+1)/2} dX` (`ν ∈ ℂ`, `T ∈ Ω`; principal power of the
positive determinant). -/
@[dlmf 35.5.E3]
def besselB {m : ℕ} (ν : ℂ) (T : Matrix (Fin m) (Fin m) ℝ) : ℂ :=
  ∫ X in posDefCone m,
    (etr (-(T * (X : Matrix (Fin m) (Fin m) ℝ) + (X : Matrix (Fin m) (Fin m) ℝ)⁻¹)) : ℂ) *
      (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (ν - ((m : ℂ) + 1) / 2))
    ∂TauCeti.symmetricLebesgue m

/-- DLMF 35.6.2: the confluent hypergeometric function of the second kind of matrix argument
`Ψ(a; b; T) = Γ_m(a)⁻¹ ∫_Ω etr(-TX) |X|^{a-(m+1)/2} |I + X|^{b-a-(m+1)/2} dX`
(`ℜa > (m-1)/2`, `T ∈ Ω`). -/
@[dlmf 35.6.E2]
def kummerPsi {m : ℕ} (a b : ℂ) (T : Matrix (Fin m) (Fin m) ℝ) : ℂ :=
  1 / multivariateGamma m a *
    ∫ X in posDefCone m,
      (etr (-(T * (X : Matrix (Fin m) (Fin m) ℝ))) : ℂ) *
        (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (a - ((m : ℂ) + 1) / 2)) *
        (((1 + (X : Matrix (Fin m) (Fin m) ℝ)).det : ℂ) ^ (b - a - ((m : ℂ) + 1) / 2))
      ∂TauCeti.symmetricLebesgue m

/-- DLMF 35.6.3: the Laguerre form
`L_ν^{(γ)}(T) = Γ_m(γ + ν + (m+1)/2) / Γ_m(γ + (m+1)/2) ₁F₁(-ν; γ + (m+1)/2; T)`
(DLMF: `ℜγ, ℜ(γ + ν) > -1`). -/
@[dlmf 35.6.E3]
def laguerreL {m : ℕ} (γ ν : ℂ) (T : Matrix (Fin m) (Fin m) ℝ) : ℂ :=
  multivariateGamma m (γ + ν + ((m : ℂ) + 1) / 2) / multivariateGamma m (γ + ((m : ℂ) + 1) / 2) *
    hyp1F1 (-ν) (γ + ((m : ℂ) + 1) / 2) T

/-- DLMF 35.7.2: the Jacobi form
`P_ν^{(γ,δ)}(T) = Γ_m(γ + ν + (m+1)/2) / Γ_m(γ + (m+1)/2)
  ₂F₁(-ν, γ + δ + ν + (m+1)/2; γ + (m+1)/2; T)` (DLMF: `0 < T < I`, `ℜγ > -1`). -/
@[dlmf 35.7.E2]
def jacobiP {m : ℕ} (γ δ ν : ℂ) (T : Matrix (Fin m) (Fin m) ℝ) : ℂ :=
  multivariateGamma m (γ + ν + ((m : ℂ) + 1) / 2) / multivariateGamma m (γ + ((m : ℂ) + 1) / 2) *
    hyp2F1 (-ν) (γ + δ + ν + ((m : ℂ) + 1) / 2) (γ + ((m : ℂ) + 1) / 2) T

/-! ## Laplace transform and convolution -/

/-- DLMF 35.2.1: the Laplace transform `g(𝐙) = ∫_Ω etr(-𝐙X) f(X) dX` of a complex function `f`
on `Ω`, at a complex (symmetric) matrix `𝐙`. -/
@[dlmf 35.2.E1]
def laplaceTransform {m : ℕ} (f : Matrix (Fin m) (Fin m) ℝ → ℂ)
    (Z : Matrix (Fin m) (Fin m) ℂ) : ℂ :=
  ∫ X in posDefCone m,
    Complex.exp (-(Z * (X : Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ))).trace) * f X
    ∂TauCeti.symmetricLebesgue m

/-- DLMF 35.2.3: the convolution `(f₁ * f₂)(T) = ∫_{0<X<T} f₁(T - X) f₂(X) dX`. -/
@[dlmf 35.2.E3]
def matrixConvolution {m : ℕ} (f₁ f₂ : Matrix (Fin m) (Fin m) ℝ → ℂ)
    (T : Matrix (Fin m) (Fin m) ℝ) : ℂ :=
  ∫ X in matrixInterval 0 T, f₁ (T - X) * f₂ X ∂TauCeti.symmetricLebesgue m

/-! ## Partial derivatives in the eigenvalues (§35.7(iii)) -/

/-- The partial derivative `∂F/∂t_k` of a complex function `F` of `t = (t₁, …, t_m) ∈ ℝ^m`, as
the derivative of `s ↦ F(t₁, …, s, …, t_m)` at `s = t_k`. -/
def coordDeriv {m : ℕ} (F : (Fin m → ℝ) → ℂ) (k : Fin m) (t : Fin m → ℝ) : ℂ :=
  deriv (fun s : ℝ => F (Function.update t k s)) (t k)

/-- DLMF 35.7.9: the `j`th partial differential operator of the system for `₂F₁` of matrix
argument, minus its right-hand side `abF`:
`t_j(1-t_j) ∂²F/∂t_j² - ½ ∑_{k≠j} t_k(1-t_k)/(t_j-t_k) ∂F/∂t_k
  + (c - ½(m-1) - (a+b-½(m-3)) t_j + ½ ∑_{k≠j} t_j(1-t_j)/(t_j-t_k)) ∂F/∂t_j - abF`.
It is used at points with pairwise distinct `t_k`, where no denominator vanishes. -/
@[dlmf 35.7.E9]
def gaussPDEOperator {m : ℕ} (a b c : ℂ) (F : (Fin m → ℝ) → ℂ) (j : Fin m)
    (t : Fin m → ℝ) : ℂ :=
  ((t j * (1 - t j) : ℝ) : ℂ) * coordDeriv (coordDeriv F j) j t -
    (1 / 2 : ℂ) * ∑ k ∈ Finset.univ.erase j,
      ((t k * (1 - t k) / (t j - t k) : ℝ) : ℂ) * coordDeriv F k t +
    (c - ((m : ℂ) - 1) / 2 - (a + b - ((m : ℂ) - 3) / 2) * (t j : ℂ) +
      (1 / 2 : ℂ) * ∑ k ∈ Finset.univ.erase j, ((t j * (1 - t j) / (t j - t k) : ℝ) : ℂ)) *
      coordDeriv F j t -
    a * b * F t

end DLMF.MatrixArgument
