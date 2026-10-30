/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Basic.Real.Sign

/-!
# Distributions and the Dirac delta: definitions (DLMF §§1.16–1.17)

Definitions for DLMF §1.16 (distributions, tempered distributions, Fourier transforms of
tempered distributions) and §1.17 (delta sequences). Mathlib already provides the spaces:

* `𝓓'(Ω, F)` (`Distribution`): continuous `ℝ`-linear maps on the real test functions
  `𝓓(Ω, ℝ)` on an open set `Ω`, with values in `F`; complex distributions take `F = ℂ`
  (testing against real test functions only is equivalent, Mathlib's implementation notes);
* `𝓢'(E, F)` (`TemperedDistribution`): continuous `ℂ`-linear maps on the Schwartz space
  `𝓢(E, ℂ)`, with the topology of pointwise convergence;
* `Distribution.delta`, `TemperedDistribution.delta`, `Distribution.ofFun`, the distributional
  derivatives `∂_{v}`, the Fourier transform `𝓕` on `𝓢'` (Mathlib's convention
  `𝓕 f ξ = ∫ e^{-2πi⟪x, ξ⟫} f x dx`).

This file adds the DLMF objects that are not upstream:

* `heaviside` (1.16.13), `xPlusRpow` (1.16.19), `logPlus` (1.16.22);
* `stieltjesDistribution α` (1.16.3_5), the distribution `φ ↦ ∫ φ dα` of a Stieltjes function;
* `distribIterDeriv k T` (1.16.9), the `k`-th distributional derivative on the line;
* `xPlusDistrib α` (1.16.19, 1.16.21, 1.16.23), the distributions `x₊^α` for all real `α`;
* `dlmfFourierSchwartz` (1.16.29): DLMF's Fourier transform
  `𝓕φ(x) = (2π)^{-n/2} ∫ φ(t) e^{i x·t} dt` on Schwartz space (DLMF convention 1.14.1, not
  Mathlib's), and `dlmfFourierTempered` (1.16.35) its transpose on `𝓢'`;
* `dlmfD j` (1.16.30), `polyOp` and `polyDiffOp P` (1.16.32), `polyMul P` (1.16.31) on
  Schwartz space, and their transposes `temperedPolyDiffOp P`, `temperedPolyMul P` on `𝓢'`;
* `IsDeltaSequence` (1.17.3), `gaussianDeltaSeq` (1.17.5), `dirichletKernel` (1.17.20).
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory Complex
open scoped Topology Distributions SchwartzMap FourierTransform LineDeriv

namespace DLMF.AlgebraicAnalytic

/-! ## §1.16(iv): the Heaviside function and `x₊^α` -/

/-- **The Heaviside function** (DLMF 1.16.13): `H(x) = 1` for `x > 0` and `H(x) = 0` for
`x ≤ 0`. The shifted function of 1.16.14 is `heaviside (x - x₀)`. -/
@[dlmf 1.16.E13, dlmf 1.16.E14]
def heaviside (x : ℝ) : ℝ := if 0 < x then 1 else 0

/-- DLMF 1.16.19: `x₊^α = x^α H(x)`, that is `x^α` for `x > 0` and `0` for `x ≤ 0` (real
power `Real.rpow`). DLMF uses it as a locally integrable function for `α > -1`. -/
@[dlmf 1.16.E19]
def xPlusRpow (α x : ℝ) : ℝ := if 0 < x then x ^ α else 0

/-- DLMF 1.16.22: `ln₊ x = H(x) ln x`, that is `ln x` for `x > 0` and `0` for `x ≤ 0`. -/
@[dlmf 1.16.E22]
def logPlus (x : ℝ) : ℝ := if 0 < x then Real.log x else 0

/-! ## §1.16(i)–(ii): distributions on an open set of the line -/

/-- DLMF 1.16.3_5: the distribution `⟨μ_α, φ⟩ = ∫ φ(x) dα(x)` of the Lebesgue–Stieltjes
measure of a Stieltjes function `α` (nondecreasing and right continuous; Mathlib's
`StieltjesFunction`, real valued, while DLMF allows the values `±∞` at the end points of a
closed interval). It is `Distribution.ofFun` of the constant `1` against `α.measure`. -/
@[dlmf 1.16.E3_5]
def stieltjesDistribution (Ω : TopologicalSpace.Opens ℝ) (α : StieltjesFunction ℝ) :
    𝓓'(Ω, ℝ) :=
  Distribution.ofFun Ω (fun _ => (1 : ℝ)) α.measure ⊤

/-- DLMF 1.16.9: the `k`-th distributional derivative `Λ^{(k)}` of a distribution on an
open subset of the line, the `k`-fold iterate of Mathlib's `∂_{1}` (1.16.8). -/
@[dlmf 1.16.E9]
def distribIterDeriv {Ω : TopologicalSpace.Opens ℝ} {F : Type*} [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] (k : ℕ)
    (T : 𝓓'(Ω, F)) : 𝓓'(Ω, F) :=
  (fun S : 𝓓'(Ω, F) => ∂_{(1 : ℝ)} S)^[k] T

/-- DLMF 1.16.6: the product `αΛ` of a distribution with a smooth function `α`,
`⟨αΛ, φ⟩ = ⟨Λ, αφ⟩`. -/
@[dlmf 1.16.E6]
def smoothMul {Ω : TopologicalSpace.Opens ℝ} {F : Type*} [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] {α : ℝ → ℝ}
    (hα : ContDiff ℝ (⊤ : ℕ∞) α) : 𝓓'(Ω, F) →L[ℝ] 𝓓'(Ω, F) :=
  (TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) hα).precompCompactConvergenceCLM F

/-- The distribution of the whole line attached to a function (zero if the function is not
locally integrable), `Distribution.ofFun` with Lebesgue measure. -/
def lineDistrib (f : ℝ → ℝ) : 𝓓'((⊤ : TopologicalSpace.Opens ℝ), ℝ) :=
  Distribution.ofFun ⊤ f volume ⊤

open Classical in
/-- **The distributions `x₊^α`** (DLMF 1.16.19, 1.16.21, 1.16.23), for every real `α`:

* for `α > -1`, the regular distribution of the locally integrable `x₊^α` (1.16.19);
* for `α < -1` not an integer, `x₊^α = D^n x₊^{α+n} / (α+1)_n` (1.16.21) with
  `n = ⌊-α⌋₊`, the least `n` with `α + n > -1`;
* for `α = -1-n` with `n ∈ ℕ`, `x₊^{-1-n} = (-1)^n D^{n+1} ln₊ x / n!` (1.16.23).

That the value in 1.16.21 does not depend on the admissible `n` is
`xPlusDistrib_eq_iterDeriv` (in `DLMF.AlgebraicAnalytic.Distributions.Theory`). -/
@[dlmf 1.16.E19, dlmf 1.16.E21, dlmf 1.16.E23]
def xPlusDistrib (α : ℝ) : 𝓓'((⊤ : TopologicalSpace.Opens ℝ), ℝ) :=
  if -1 < α then lineDistrib (xPlusRpow α)
  else if ∃ n : ℕ, α = -1 - n then
    ((-1 : ℝ) ^ ⌊-1 - α⌋₊ / (⌊-1 - α⌋₊).factorial) •
      distribIterDeriv (⌊-1 - α⌋₊ + 1) (lineDistrib logPlus)
  else
    (ascPochhammer ℝ ⌊-α⌋₊).eval (α + 1) ⁻¹ •
      distribIterDeriv ⌊-α⌋₊ (lineDistrib (xPlusRpow (α + ⌊-α⌋₊)))

/-! ## §1.16(vii): DLMF Fourier transform on Schwartz space and on `𝓢'` -/

section Fourier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The linear equivalence `x ↦ c • x` of a real vector space, for `c ≠ 0`. -/
def scaleEquiv (c : ℝ) (hc : c ≠ 0) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.equivOfInverse (c • ContinuousLinearMap.id ℝ E)
    (c⁻¹ • ContinuousLinearMap.id ℝ E)
    (fun x => by simp [smul_smul, mul_inv_cancel₀ hc])
    (fun x => by simp [smul_smul, inv_mul_cancel₀ hc])

/-- **DLMF's Fourier transform on Schwartz space** (DLMF 1.16.29):
`𝓕φ(x) = (2π)^{-n/2} ∫_{ℝⁿ} φ(t) e^{i x·t} dt`, `n = dim E`, in the normalization of DLMF
1.14.1 (kernel `e^{+ixt}`, symmetric factor). It is built from Mathlib's inverse transform
`𝓕⁻φ(w) = ∫ e^{2πi⟪t, w⟫} φ(t) dt` as `(2π)^{-n/2} 𝓕⁻φ(x / 2π)`; the integral formula is
`dlmfFourierSchwartz_apply`. That it maps `𝓢` to `𝓢` (DLMF's "`𝓕φ ∈ 𝓣ₙ`") is built in. -/
@[dlmf 1.16.E29, dlmf 1.16.vii]
def dlmfFourierSchwartz : 𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ) :=
  (((2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) : ℝ) : ℂ) •
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (scaleEquiv (2 * Real.pi)⁻¹ (by positivity)) ∘L
      FourierTransform.fourierInvCLM ℂ 𝓢(E, ℂ))

/-- **DLMF's Fourier transform of a tempered distribution** (DLMF 1.16.35):
`⟨𝓕(u), φ⟩ = ⟨u, 𝓕(φ)⟩` with DLMF's transform `dlmfFourierSchwartz` on test functions. -/
@[dlmf 1.16.E35]
def dlmfFourierTempered : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ) :=
  PointwiseConvergenceCLM.precomp ℂ dlmfFourierSchwartz

/-- The tempered distribution `φ ↦ ∫ φ(x) f(x) dx` of an essentially bounded function
`f : ℝ → ℂ` (through Mathlib's `Lp.toTemperedDistribution` for `p = ∞`); zero if `f` is not
essentially bounded. -/
def boundedTempered (f : ℝ → ℂ) : 𝓢'(ℝ, ℂ) :=
  open Classical in
  if h : MemLp f ⊤ volume then MeasureTheory.Lp.toTemperedDistribution (h.toLp f) else 0

/-- The sign function `sign x` (DLMF 1.16.44) as a tempered distribution. -/
def signTempered : 𝓢'(ℝ, ℂ) := boundedTempered fun x => (Real.sign x : ℂ)

/-- The Heaviside function `H` (DLMF 1.16.13) as a tempered distribution. -/
def heavisideTempered : 𝓢'(ℝ, ℂ) := boundedTempered fun x => (heaviside x : ℂ)

end Fourier

/-! ## §1.16(vii): polynomial differential operators -/

section PolyOps

variable {n : ℕ}

/-- The noncommutative evaluation of a multivariate polynomial `P = Σ_α c_α X^α` at a family
`D` of elements of an algebra: `Σ_α c_α D₁^{α₁} ⋯ Dₙ^{αₙ}` (the factors in the order of the
variables). For commuting `D_j` this is the usual evaluation. -/
def polyOp {A : Type*} [Ring A] [Algebra ℂ A] (P : MvPolynomial (Fin n) ℂ) (D : Fin n → A) :
    A :=
  ∑ α ∈ P.support, P.coeff α • (List.ofFn fun j => D j ^ α j).prod

/-- DLMF 1.16.30: the operator `D_j = (1/i) ∂/∂x_j` on Schwartz space of
`EuclideanSpace ℝ (Fin n)`, a linear endomorphism. -/
@[dlmf 1.16.E30]
def dlmfD (j : Fin n) : Module.End ℂ 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
  (-I) • (LineDeriv.lineDerivOpCLM ℂ 𝓢(EuclideanSpace ℝ (Fin n), ℂ)
    (EuclideanSpace.single j (1 : ℝ))).toLinearMap

/-- DLMF 1.16.32: the partial differential operator `P(𝐃) = Σ_α c_α 𝐃^α` on Schwartz space,
for a polynomial `P(𝐱) = Σ_α c_α 𝐱^α` (1.16.31) given as an `MvPolynomial`. -/
@[dlmf 1.16.E32]
def polyDiffOp (P : MvPolynomial (Fin n) ℂ) : Module.End ℂ 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
  polyOp P dlmfD

/-- DLMF 1.16.31: the polynomial function `P(𝐱) = Σ_α c_α x₁^{α₁} ⋯ xₙ^{αₙ}`. -/
@[dlmf 1.16.E31]
def polyEval (P : MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  MvPolynomial.eval (fun j => (x j : ℂ)) P

/-- Multiplication `φ ↦ Pφ` by the polynomial function `P(𝐱)` (1.16.31) on Schwartz space. -/
def polyMul (P : MvPolynomial (Fin n) ℂ) :
    𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (polyEval P)

/-- The polynomial `P₋(𝐱) = P(-𝐱)` (DLMF, below 1.16.37). -/
def polyNeg (P : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin n) ℂ :=
  MvPolynomial.aeval (fun j => -MvPolynomial.X j) P

/-- The operator `𝐃_j = (1/i) ∂/∂x_j` on tempered distributions, in the sense of
distributions: `⟨𝐃_j u, φ⟩ = ⟨u, -𝐃_j φ⟩` (DLMF 1.16.8 with Mathlib's `∂_{v}` on `𝓢'`). -/
def temperedD (j : Fin n) : Module.End ℂ 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (-I) • (LineDeriv.lineDerivOpCLM ℂ 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)
    (EuclideanSpace.single j (1 : ℝ))).toLinearMap

/-- The partial differential operator `P(𝐃)` on tempered distributions, the derivatives
understood in the sense of distributions (DLMF, below 1.16.37). -/
def temperedPolyDiffOp (P : MvPolynomial (Fin n) ℂ) :
    Module.End ℂ 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  polyOp P temperedD

/-- Multiplication `u ↦ P u` of a tempered distribution by the polynomial `P(𝐱)` (convention
1.16.6: `⟨P u, φ⟩ = ⟨u, P φ⟩`). -/
def temperedPolyMul (P : MvPolynomial (Fin n) ℂ) :
    𝓢'(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  TemperedDistribution.smulLeftCLM ℂ (polyEval P)

end PolyOps

/-! ## §1.17: delta sequences -/

/-- **Delta sequence** (DLMF 1.17.3–1.17.4): `δₙ` is a delta sequence if
`lim_{n→∞} ∫ δₙ(x - a) φ(x) dx = φ(a)` for every `a ∈ ℝ` and every smooth compactly supported
`φ : ℝ → ℂ`; this is the meaning of the symbolic `lim δₙ(x) = δ(x)` of 1.17.4 (weak
convergence against test functions). -/
@[dlmf 1.17.E3, dlmf 1.17.E4]
def IsDeltaSequence (δ : ℕ → ℝ → ℂ) : Prop :=
  ∀ φ : ℝ → ℂ, ContDiff ℝ ⊤ φ → HasCompactSupport φ → ∀ a : ℝ,
    Tendsto (fun n => ∫ x, δ n (x - a) * φ x) atTop (𝓝 (φ a))

/-- DLMF 1.17.5: the Gaussian delta sequence `δₙ(x) = √(n/π) e^{-n x²}`. -/
@[dlmf 1.17.E5]
def gaussianDeltaSeq (n : ℕ) (x : ℝ) : ℂ := (Real.sqrt (n / Real.pi) * Real.exp (-(n * x ^ 2)) : ℝ)

/-- A smooth compactly supported complex function on `ℝ` supported in the open set `U`: the
test functions against which the representations of §1.17 are stated. -/
def IsTestFunctionOn (U : Set ℝ) (φ : ℝ → ℂ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U

/-- The normalized Gaussian `e^{-x²}/√π`, of integral one (the profile of 1.17.5). -/
def normalizedGaussian (x : ℝ) : ℝ := Real.exp (-x ^ 2) / Real.sqrt Real.pi

/-- DLMF 1.17.20: the Dirichlet kernel `δₙ(x) = (1/2π) Σ_{k=-n}^{n} e^{ikx}`. -/
@[dlmf 1.17.E20]
def dirichletKernel (n : ℕ) (x : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∑ k ∈ Finset.Icc (-(n : ℤ)) n, exp (I * k * x)

end DLMF.AlgebraicAnalytic
