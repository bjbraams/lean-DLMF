/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.Basic.Pochhammer
public import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
public import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

/-!
# Generating functions of number theory (DLMF §§27.7, 27.13, 27.14)

The series and products of DLMF Chapter 27 that serve as generating functions: Lambert series
(§27.7), the representation numbers by sums of squares and Jacobi's theta series (§27.13(iv)),
Euler's product `∏ (1 - xᵐ)` (§27.14(ii)), the discriminant and Ramanujan's `τ` (§27.14(vi)).

## Main definitions

* `lambertSeries`: the Lambert series `∑_{n≥1} f(n) xⁿ/(1 - xⁿ)` (DLMF 27.7.1).
* `sumSquaresCount`: `r_k(n)`, the number of representations of `n` as a sum of `k` squares
  (DLMF 27.13.3).
* `jacobiThetaSeries`: `ϑ(x) = 1 + 2 ∑_{m≥1} x^{m²}` (DLMF 27.13.4).
* `eulerReciprocal`: Euler's reciprocal function `f(x) = ∏_{m≥1} (1 - xᵐ)` (DLMF 27.14.2).
* `modularDiscriminant`: the discriminant `Δ(τ) = (2π)¹² η(τ)²⁴` (DLMF 27.14.16).
* `ramanujanTau`: Ramanujan's `τ(n)` (DLMF 27.14.18).

## Main results

* `jacobiTheta_eq_jacobiThetaSeries`: `ϑ(e^{πiτ})` is Mathlib's `jacobiTheta τ`.
* `eulerReciprocal_eq_qPochhammerInf`, `hasProd_eulerReciprocal`: `f(x) = (x; x)_∞`, and for
  `|x| < 1` the product converges to Mathlib's `eulerFunction x`.
* `modularDiscriminant_eq`, `modularDiscriminant_transform`: `Δ` is `(2π)¹²` times Mathlib's
  `ModularForm.discriminant`, and its modular transformation (DLMF 27.14.17).

## Implementation notes

The series and products are totalized (`tsum`, `tprod`); the theorem modules
(`DLMF.NumberTheory.DivisorSums`, `DLMF.NumberTheory.Additive`,
`DLMF.NumberTheory.Partitions`) assert convergence where they use them. Dedekind's `η` is
Mathlib's `ModularForm.eta`.
-/

@[expose] public noncomputable section

open Complex
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm

namespace DLMF.NumberTheory

/-! ### §27.7 Lambert series -/

/-- DLMF 27.7.1: the Lambert series `∑_{n≥1} f(n) xⁿ/(1 - xⁿ)` (a totalized `tsum`; the
statements below assert convergence). -/
@[dlmf 27.7.E1]
def lambertSeries (f : ℕ → ℂ) (x : ℂ) : ℂ :=
  ∑' n : ℕ, f (n + 1) * x ^ (n + 1) / (1 - x ^ (n + 1))

/-! ### §27.13(iv) Representation by squares -/

/-- DLMF 27.13.3: `r_k(n)`, the number of solutions of `n = x₁² + ⋯ + x_k²` in integers
(positive, negative or zero, order taken into account). -/
@[dlmf 27.13.E3]
def sumSquaresCount (k n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin k ↦ Finset.Icc (-(n : ℤ)) n).filter
    fun x ↦ ∑ i, x i ^ 2 = (n : ℤ)).card

/-- DLMF 27.13.4: `ϑ(x) = 1 + 2 ∑_{m≥1} x^{m²}`, `|x| < 1` (a totalized `tsum`). -/
@[dlmf 27.13.E4]
def jacobiThetaSeries (x : ℂ) : ℂ := 1 + 2 * ∑' m : ℕ, x ^ ((m + 1) ^ 2)

/-- §27.13(iv) after 27.13.4: `ϑ(e^{πiτ})` is Mathlib's `jacobiTheta τ` (`= θ₃(0|τ)`),
`ℑτ > 0`. -/
@[dlmf 27.13.E4]
theorem jacobiTheta_eq_jacobiThetaSeries {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta τ = jacobiThetaSeries (Complex.exp (π * Complex.I * τ)) := by
  rw [jacobiTheta_eq_tsum_nat hτ, jacobiThetaSeries]
  congr 3
  funext n
  rw [← Complex.exp_nat_mul]
  push_cast
  ring_nf

/-! ### §27.14 Euler's product, the discriminant and Ramanujan's tau function -/

/-- DLMF 27.14.2: Euler's reciprocal function `f(x) = ∏_{m≥1} (1 - xᵐ)`, `|x| < 1`
(a totalized `tprod`). -/
@[dlmf 27.14.E2]
def eulerReciprocal (x : ℂ) : ℂ := ∏' m : ℕ, (1 - x ^ (m + 1))

/-- DLMF 27.14.2: `f(x) = (x; x)_∞`. -/
@[dlmf 27.14.E2]
theorem eulerReciprocal_eq_qPochhammerInf (x : ℂ) :
    eulerReciprocal x = DLMF.QSeries.qPochhammerInf x x := by
  simp only [eulerReciprocal, DLMF.QSeries.qPochhammerInf, pow_succ']

/-- DLMF 27.14.2: for `|x| < 1` the product converges to Mathlib's `eulerFunction x`. -/
@[dlmf 27.14.E2]
theorem hasProd_eulerReciprocal {x : ℂ} (hx : ‖x‖ < 1) :
    HasProd (fun m : ℕ ↦ 1 - x ^ (m + 1)) (eulerReciprocal x) ∧
      eulerReciprocal x = eulerFunction x := by
  have h := hasProd_eulerFunction hx
  exact ⟨by rw [eulerReciprocal, h.tprod_eq]; exact h, h.tprod_eq⟩

/-- DLMF 27.14.16: the discriminant `Δ(τ) = (2π)¹² η(τ)²⁴`, `ℑτ > 0`. -/
@[dlmf 27.14.E16]
def modularDiscriminant (τ : ℂ) : ℂ := (2 * π) ^ 12 * η τ ^ 24

/-- DLMF 27.14.16: `Δ_DLMF = (2π)¹² Δ_Mathlib`. -/
@[dlmf 27.14.E16]
theorem modularDiscriminant_eq (τ : ℍ) :
    modularDiscriminant τ = (2 * π) ^ 12 * ModularForm.discriminant τ := rfl

/-- DLMF 27.14.17: `Δ((aτ + b)/(cτ + d)) = (cτ + d)¹² Δ(τ)` for all `𝒜 ∈ SL(2, ℤ)`
(stronger than DLMF, which assumes `c > 0`). -/
@[dlmf 27.14.E17]
theorem modularDiscriminant_transform (A : SL(2, ℤ)) (τ : ℍ) :
    modularDiscriminant (A • τ : ℍ) = ((A 1 0 : ℂ) * τ + A 1 1) ^ 12 * modularDiscriminant τ := by
  have h := SlashInvariantForm.slash_action_eqn' CuspForm.discriminant (Γ := 𝒮ℒ)
    (γ := Matrix.SpecialLinearGroup.mapGL ℝ A) (MonoidHom.mem_range.mpr ⟨A, rfl⟩) τ
  simp only [CuspForm.coe_discriminant] at h
  have h' : ModularForm.discriminant (A • τ : ℍ) =
      ((A 1 0 : ℂ) * τ + A 1 1) ^ 12 * ModularForm.discriminant τ := by
    convert h using 2 <;> rfl
  rw [modularDiscriminant_eq, modularDiscriminant_eq, h']
  ring

/-- DLMF 27.14.18: Ramanujan's `τ(n)`, the `n`th coefficient of `x ∏_{m≥1} (1 - xᵐ)²⁴`. -/
@[dlmf 27.14.E18]
def ramanujanTau (n : ℕ) : ℤ :=
  PowerSeries.coeff n (PowerSeries.X * PowerSeries.pentagonalSeries ℤ ^ 24)

end DLMF.NumberTheory
