/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Second-order differential operators and eigenfunction expansions: definitions
(DLMF §1.18)

Hilbert spaces, `L²` spaces, orthonormal bases (`HilbertBasis`), bounded operators and their
adjoints, unbounded operators (`LinearPMap`) with their adjoints and self-adjointness are
Mathlib's. This file adds:

* `schrodingerOp q` (1.18.28), `hermiteOp` (1.18.41), `besselOp ν` (1.18.55) and the radial
  operator `radialSchrodingerOp ℓ V` (1.18.67), acting on functions `ℝ → ℂ`;
* the eigenfunctions of the examples: `sinEigenfunction`, `cosEigenfunction`,
  `expEigenfunction` (1.18.36–1.18.38) and the Hermite functions `hermiteFunction` (1.18.42),
  via Mathlib's `Polynomial.hermite`;
* for an unbounded operator `T : E →ₗ.[ℂ] E`: `IsSymmetricOp` (1.18.70),
  `IsEssentiallySelfAdjoint`, the resolvent set and the point, continuous and residual spectra
  (§1.18(ix)), the deficiency subspaces `deficiencySubspace T z` and indices;
* for the Weyl theory of `-d²/dx² + q`: `IsSchrodingerSolOn`, `AllSolutionsL2Left/Right`,
  `IsLimitCircleLeft/Right`, the `L²` solution space `l2SolutionSpace` and the boundary value
  `boundaryValueLeft` (1.18.71);
* `IsEigenfunctionTransform` (1.18.44–1.18.47, 1.18.60–1.18.63): a unitary map from `L²(X)`
  onto `L²(ν)`, `ν` the spectral measure on `σ = σ_c ∪ σ_p`, given on compactly supported
  continuous functions by `f̂(λ) = ⟨f, φ_λ⟩`; and `IsDiagonalizedBy` (`T ↔ λ`).

DLMF's inner product `⟨u, v⟩` is linear in `u`; Mathlib's `⟪u, v⟫` is linear in `v`, so
DLMF's `⟨u, v⟩` is Mathlib's `⟪v, u⟫`.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory Complex
open scoped Topology InnerProductSpace

namespace DLMF.AlgebraicAnalytic

/-! ## §1.18(iv): formally self-adjoint second-order operators -/

/-- DLMF 1.18.28: the formally self-adjoint operator `𝓛 f = -f'' + q f` on functions
`f : ℝ → ℂ`, with a real potential `q`. -/
@[dlmf 1.18.E28]
def schrodingerOp (q : ℝ → ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  -deriv (deriv f) x + (q x : ℂ) * f x

/-- DLMF 1.18.41: the Hermite operator `-d²/dx² + x²` on `ℝ`. -/
@[dlmf 1.18.E41]
def hermiteOp : (ℝ → ℂ) → ℝ → ℂ := schrodingerOp fun x => x ^ 2

/-- DLMF 1.18.55: the Bessel operator `-d²/dx² + (ν² - ¼)/x²` on `(0, ∞)` (real `ν`). -/
@[dlmf 1.18.E55]
def besselOp (ν : ℝ) : (ℝ → ℂ) → ℝ → ℂ := schrodingerOp fun x => (ν ^ 2 - 1 / 4) / x ^ 2

/-- DLMF 1.18.67: the radial Schrödinger operator
`𝓛_ℓ = -½ d²/dr² + ℓ(ℓ+1)/(2r²) + V(r)` on `(0, ∞)`. -/
@[dlmf 1.18.E67]
def radialSchrodingerOp (ℓ : ℕ) (V : ℝ → ℝ) (f : ℝ → ℂ) (r : ℝ) : ℂ :=
  -(1 / 2 : ℂ) * deriv (deriv f) r + ((ℓ * (ℓ + 1) / (2 * r ^ 2) + V r : ℝ) : ℂ) * f r

/-- DLMF 1.18.36: the Dirichlet eigenfunctions `√(2/π) sin(nx)` on `[0, π]`. -/
@[dlmf 1.18.E36]
def sinEigenfunction (n : ℕ) (x : ℝ) : ℂ := (Real.sqrt (2 / Real.pi) * Real.sin (n * x) : ℝ)

/-- DLMF 1.18.37: the Neumann eigenfunctions `1/√π` (`n = 0`) and `√(2/π) cos(nx)` on
`[0, π]`. -/
@[dlmf 1.18.E37]
def cosEigenfunction (n : ℕ) (x : ℝ) : ℂ :=
  if n = 0 then ((1 / Real.sqrt Real.pi : ℝ) : ℂ)
  else (Real.sqrt (2 / Real.pi) * Real.cos (n * x) : ℝ)

/-- DLMF 1.18.38: the periodic eigenfunctions `e^{2inx}/√π` on `[0, π]`, `n ∈ ℤ`. -/
@[dlmf 1.18.E38]
def expEigenfunction (n : ℤ) (x : ℝ) : ℂ := exp (2 * I * n * x) / Real.sqrt Real.pi

/-- DLMF 1.18.42: the normalized Hermite functions
`φₙ(x) = (π^{1/2} 2ⁿ n!)^{-1/2} e^{-x²/2} Hₙ(x)`. DLMF's (physicists') `Hₙ` is written
through Mathlib's probabilists' `Polynomial.hermite n = Heₙ` as `Hₙ(x) = 2^{n/2} Heₙ(√2 x)`
(DLMF 18.7.11–18.7.12; `DLMF.OrthogonalPolynomials.hermitePolyH` is the same polynomial). -/
@[dlmf 1.18.E42]
def hermiteFunction (n : ℕ) (x : ℝ) : ℂ :=
  ((Real.sqrt (Real.sqrt Real.pi * 2 ^ n * n.factorial))⁻¹ * Real.exp (-x ^ 2 / 2) *
    (Real.sqrt 2 ^ n * ((Polynomial.hermite n).map (Int.castRingHom ℝ)).eval
      (Real.sqrt 2 * x)) : ℝ)

/-! ## §1.18(iii), §1.18(ix): unbounded operators and their spectra -/

section Operators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- DLMF 1.18.70: a densely defined operator `T` is symmetric if `⟨Tv, w⟩ = ⟨v, Tw⟩` for
`v, w ∈ 𝓓(T)` (Mathlib: `T.IsFormalAdjoint T`). -/
@[dlmf 1.18.E70]
def IsSymmetricOp (T : E →ₗ.[ℂ] E) : Prop :=
  Dense (T.domain : Set E) ∧ T.IsFormalAdjoint T

/-- §1.18(ix): a symmetric operator is essentially self-adjoint if `T** = T*`. -/
@[dlmf 1.18.ix]
def IsEssentiallySelfAdjoint (T : E →ₗ.[ℂ] E) : Prop :=
  IsSymmetricOp T ∧ T.adjoint.adjoint = T.adjoint

/-- The map `v ↦ z v - T v` on the domain of `T`. -/
def shiftedOp (T : E →ₗ.[ℂ] E) (z : ℂ) : T.domain →ₗ[ℂ] E :=
  z • T.domain.subtype - T.toFun

/-- §1.18(ix): the resolvent set `ρ(T)`: the `z` for which `z - T` is injective with dense
range and bounded inverse on its range. -/
@[dlmf 1.18.ix]
def opResolventSet (T : E →ₗ.[ℂ] E) : Set ℂ :=
  {z | Function.Injective (shiftedOp T z) ∧ Dense (Set.range (shiftedOp T z)) ∧
    ∃ C : ℝ, ∀ v : T.domain, ‖(v : E)‖ ≤ C * ‖shiftedOp T z v‖}

/-- §1.18(ix): the spectrum `σ(T) = ℂ \ ρ(T)`. -/
@[dlmf 1.18.ix]
def opSpectrum (T : E →ₗ.[ℂ] E) : Set ℂ := (opResolventSet T)ᶜ

/-- §1.18(ix): the point spectrum, the `z` for which `z - T` is not injective (the
eigenvalues). -/
@[dlmf 1.18.ix]
def opPointSpectrum (T : E →ₗ.[ℂ] E) : Set ℂ := {z | ¬ Function.Injective (shiftedOp T z)}

/-- §1.18(ix): the continuous spectrum: `z - T` injective with dense range but unbounded
inverse. -/
@[dlmf 1.18.ix]
def opContinuousSpectrum (T : E →ₗ.[ℂ] E) : Set ℂ :=
  {z | Function.Injective (shiftedOp T z) ∧ Dense (Set.range (shiftedOp T z)) ∧
    ¬ ∃ C : ℝ, ∀ v : T.domain, ‖(v : E)‖ ≤ C * ‖shiftedOp T z v‖}

/-- §1.18(ix): the residual spectrum: `z - T` injective without dense range. -/
@[dlmf 1.18.ix]
def opResidualSpectrum (T : E →ₗ.[ℂ] E) : Set ℂ :=
  {z | Function.Injective (shiftedOp T z) ∧ ¬ Dense (Set.range (shiftedOp T z))}

/-- §1.18(ix): the deficiency subspace `N_z`, the `z`-eigenspace of the adjoint `T*`. -/
@[dlmf 1.18.ix]
def deficiencySubspace (T : E →ₗ.[ℂ] E) (z : ℂ) : Submodule ℂ E :=
  (LinearMap.ker (T.adjoint.toFun - z • T.adjoint.domain.subtype)).map T.adjoint.domain.subtype

/-- §1.18(ix): the deficiency indices `n₊ = dim N_z` (`ℑz > 0`) and `n₋ = dim N_z`
(`ℑz < 0`), here at `z = i` and `z = -i`. -/
@[dlmf 1.18.ix]
def deficiencyIndices (T : E →ₗ.[ℂ] E) : Cardinal × Cardinal :=
  (Module.rank ℂ (deficiencySubspace T I), Module.rank ℂ (deficiencySubspace T (-I)))

end Operators

/-! ## §1.18(ix): Weyl's alternative for `-d²/dx² + q` -/

/-- `f` solves `-f'' + q f = z f` on `S`: `f` and `f'` are differentiable at every point of
`S` and `f'' = (q - z) f` there. -/
def IsSchrodingerSolOn (q : ℝ → ℝ) (z : ℂ) (f : ℝ → ℂ) (S : Set ℝ) : Prop :=
  ∀ x ∈ S, HasDerivAt f (deriv f x) x ∧ HasDerivAt (deriv f) (((q x : ℂ) - z) * f x) x

/-- All solutions of `-f'' + q f = z f` on `(a, c]` are square integrable near `a`. -/
def AllSolutionsL2Left (q : ℝ → ℝ) (z : ℂ) (a c : ℝ) : Prop :=
  ∀ f, IsSchrodingerSolOn q z f (Ioc a c) → MemLp f 2 (volume.restrict (Ioc a c))

/-- All solutions of `-f'' + q f = z f` on `[c, b)` are square integrable near `b`
(`b = ∞` is `AllSolutionsL2Ici`). -/
def AllSolutionsL2Right (q : ℝ → ℝ) (z : ℂ) (c b : ℝ) : Prop :=
  ∀ f, IsSchrodingerSolOn q z f (Ico c b) → MemLp f 2 (volume.restrict (Ico c b))

/-- All solutions on `[c, ∞)` are square integrable at `+∞`. -/
def AllSolutionsL2Ici (q : ℝ → ℝ) (z : ℂ) (c : ℝ) : Prop :=
  ∀ f, IsSchrodingerSolOn q z f (Ici c) → MemLp f 2 (volume.restrict (Ici c))

/-- §1.18(ix): the limit circle case at the left end point `a` (all solutions square
integrable near `a`, for every `z`); otherwise `a` is in the limit point case. -/
@[dlmf 1.18.ix]
def IsLimitCircleLeft (q : ℝ → ℝ) (a c : ℝ) : Prop := ∀ z : ℂ, AllSolutionsL2Left q z a c

/-- §1.18(ix): the limit circle case at the right end point `b`. -/
@[dlmf 1.18.ix]
def IsLimitCircleRight (q : ℝ → ℝ) (c b : ℝ) : Prop := ∀ z : ℂ, AllSolutionsL2Right q z c b

/-- The space of solutions of `-f'' + q f = z f` on the open interval `S` that are square
integrable on `S` (DLMF's `N_z`, §1.18(ix): `f ∈ N_z` iff `f` is a `C²` solution in `L²`),
as the span of the solution set (which is itself a subspace). -/
def l2SolutionSpace (q : ℝ → ℝ) (z : ℂ) (S : Set ℝ) : Submodule ℂ (ℝ → ℂ) :=
  Submodule.span ℂ {f | (∀ x ∈ S, DifferentiableAt ℝ f x ∧ DifferentiableAt ℝ (deriv f) x ∧
      deriv (deriv f) x = ((q x : ℂ) - z) * f x) ∧ MemLp f 2 (volume.restrict S)}

/-- DLMF 1.18.71: the boundary value `𝓑(f) = lim_{x→a+} (α(x) f(x) + β(x) f'(x))` at the
left end point `a` (Lean's `limUnder`; meaningful when the limit exists). -/
@[dlmf 1.18.E71]
def boundaryValueLeft (α β : ℝ → ℂ) (a : ℝ) (f : ℝ → ℂ) : ℂ :=
  limUnder (𝓝[>] a) fun x => α x * f x + β x * deriv f x

/-- The maximal domain (`C²` part) of `-d²/dx² + q` on `(a, b)`: twice differentiable
`f ∈ L²(a, b)` with `-f'' + q f ∈ L²(a, b)` (the domain `𝓓(𝓛*)` of §1.18(ix) consists of the
`f` with `f'` locally absolutely continuous and `𝓛 f ∈ L²`; its `C²` elements suffice for the
statements made here). -/
def schrodingerMaxDomainC2 (q : ℝ → ℝ) (a b : ℝ) : Set (ℝ → ℂ) :=
  {f | ContDiffOn ℝ 2 f (Ioo a b) ∧ MemLp f 2 (volume.restrict (Ioo a b)) ∧
    MemLp (schrodingerOp q f) 2 (volume.restrict (Ioo a b))}

/-- The Wronskian (Lagrange bracket) `W(f, g)(x) = f(x) g'(x) - f'(x) g(x)`. -/
def wronskianC (f g : ℝ → ℂ) (x : ℝ) : ℂ := f x * deriv g x - deriv f x * g x

/-! ## §1.18(vi), §1.18(viii): eigenfunction transforms -/

/-- DLMF 1.18.47 and 1.18.32: the eigenfunction coefficient
`f̂(λ) = ⟨f, φ_λ⟩ = ∫_X f(x) conj(φ_λ(x)) dx`. -/
@[dlmf 1.18.E47, dlmf 1.18.E32]
def eigenCoeff (X : Set ℝ) (φ : ℝ → ℝ → ℂ) (f : ℝ → ℂ) (μ : ℝ) : ℂ :=
  ∫ x in X, f x * starRingEnd ℂ (φ μ x)

/-- **Generalized eigenfunction expansion** (DLMF 1.18.44–1.18.47 and 1.18.60–1.18.63), the
rigorous content of the formal orthonormality and completeness relations. `ν` is the spectral
measure on `σ = σ_c ∪ σ_p` (Lebesgue measure on the continuous spectrum `σ_c` plus a unit
point mass at each simple eigenvalue `λₙ ∈ σ_p`, as DLMF assumes), `φ λ` are the
eigenfunctions (`L²` for `λ ∈ σ_p`, Dirac-delta normalized for `λ ∈ σ_c`) and `U` is a unitary
map `L²(X) → L²(ℝ, ν)` given on compactly supported continuous functions by the coefficient
`f̂ = eigenCoeff X φ f` (1.18.47). Unitarity of `U` is equivalent to the completeness relations
1.18.45, 1.18.63 (isometry) together with the orthonormality relations 1.18.44,
1.18.60–1.18.62 (surjectivity). -/
@[dlmf 1.18.E44, dlmf 1.18.E45, dlmf 1.18.E60, dlmf 1.18.E61, dlmf 1.18.E62,
  dlmf 1.18.E63]
def IsEigenfunctionTransform (X : Set ℝ) (ν : Measure ℝ) (φ : ℝ → ℝ → ℂ)
    (U : Lp ℂ 2 (volume.restrict X) ≃ₗᵢ[ℂ] Lp ℂ 2 ν) : Prop :=
  ∀ (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict X)), Continuous f → HasCompactSupport f →
    tsupport f ⊆ X → (U (hf.toLp f) : ℝ → ℂ) =ᵐ[ν] eigenCoeff X φ f

/-- DLMF 1.18.49–1.18.50: the operator `T` on `L²(X)` is diagonalized by `U` (the operator
`F(T)` of 1.18.50 is then `U⁻¹ F(λ) U`): `U(Tf)(λ) = λ (Uf)(λ)` for `f ∈ 𝓓(T)`. -/
@[dlmf 1.18.E49, dlmf 1.18.E50]
def IsDiagonalizedBy {X : Set ℝ} {ν : Measure ℝ}
    (T : Lp ℂ 2 (volume.restrict X) →ₗ.[ℂ] Lp ℂ 2 (volume.restrict X))
    (U : Lp ℂ 2 (volume.restrict X) ≃ₗᵢ[ℂ] Lp ℂ 2 ν) : Prop :=
  ∀ f : T.domain, (U (T f) : ℝ → ℂ) =ᵐ[ν] fun μ => (μ : ℂ) * (U f : ℝ → ℂ) μ

end DLMF.AlgebraicAnalytic
