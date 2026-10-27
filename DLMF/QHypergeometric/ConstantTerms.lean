/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Basic

/-!
# Constant terms of q-products (DLMF §17.14)

The finite q-Dyson product is a genuine multivariate Laurent polynomial, represented
by its finitely supported integer exponent vectors. Infinite-product constant terms
are Laurent coefficients computed by the normalized integral on `|z|=ρ`, `ρ>1`.
This annulus fixes the expansion of inverse powers and excludes all denominator poles.

The printed left side of 17.14.3 repeats 17.14.2. Its coefficient of q is −1,
whereas the printed G(q)/(-q;q²)∞ has coefficient 0. The correct denominator is
`(-q;q²)_n`, as also obtained from the constant-term expression. The corrected
formula is recorded explicitly below; no false identity is admitted.
-/

@[expose] public noncomputable section
open Complex Finset MeasureTheory
open scoped Real
open DLMF.QSeries
namespace DLMF.QHypergeometric

/-- The finite q-Dyson Laurent polynomial in `n` variables. -/
def qDysonLaurent (n : ℕ) (a : Fin n → ℕ) (q : ℂ) :
    AddMonoidAlgebra ℂ (Fin n → ℤ) :=
  ∏ j : Fin n, ∏ k : Fin n, if j < k then
    (∏ t ∈ range (a j), (1 - AddMonoidAlgebra.single
      (Pi.single j 1 - Pi.single k 1) (q^t))) *
    (∏ t ∈ range (a k), (1 - AddMonoidAlgebra.single
      (Pi.single k 1 - Pi.single j 1) (q^(t+1)))) else 1

/-- Polynomial form of the q-Dyson identity, valid even at roots of unity. -/
@[dlmf 17.14.E1]
theorem qDyson_constantTerm_mul (n : ℕ) (a : Fin n → ℕ) (q : ℂ) :
    (qDysonLaurent n a q).coeff 0 * (∏ i, qPochhammer q q (a i)) =
      qPochhammer q q (∑ i, a i) := by
  sorry

/-- The quotient form of the q-Dyson identity, with exactly the needed denominator condition. -/
@[dlmf 17.14.E1]
theorem qDyson_constantTerm (n : ℕ) (a : Fin n → ℕ) (q : ℂ)
    (hden : ∀ i, qPochhammer q q (a i) ≠ 0) :
    (qDysonLaurent n a q).coeff 0 =
      qPochhammer q q (∑ i, a i) / (∏ i, qPochhammer q q (a i)) := by
  exact (eq_div_iff (Finset.prod_ne_zero_iff.mpr fun i _ => hden i)).mpr
    (qDyson_constantTerm_mul n a q)

/-- Laurent coefficient of order zero on a specified positively oriented circle. -/
def circleConstantTerm (f : ℂ → ℂ) (ρ : ℝ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * ∫ θ : ℝ in 0..(2 * Real.pi), f (ρ * exp (θ * I))

/-- The Jacobi triple-product numerator used in the four constant-term identities. -/
def rogersThetaProduct (q z : ℂ) : ℂ :=
  qPochhammerInf (-z*q) (q^2) * qPochhammerInf (-q/z) (q^2) *
    qPochhammerInf (q^2) (q^2)

/-- First infinite-product constant term; all three displayed equalities are retained. -/
@[dlmf 17.14.E2]
theorem rogers_constantTerm_H (q : ℂ) (hq : ‖q‖<1) (ρ : ℝ) (hρ : 1<ρ) :
    let f := fun z => rogersThetaProduct q z /
      (qPochhammerInf (q^2/z) (q^2) * qPochhammerInf (-q) (q^2) *
        qPochhammerInf (q/z) (q^2))
    let g := fun z => rogersThetaProduct q z / qPochhammerInf (q/z) q
    (∑' n : ℕ, q^(n*(n+1)) /
      (qPochhammer (q^2) (q^2) n * qPochhammer (-q) (q^2) (n+1))) =
        circleConstantTerm f ρ ∧
    circleConstantTerm f ρ = circleConstantTerm g ρ / qPochhammerInf (-q) (q^2) ∧
    circleConstantTerm g ρ / qPochhammerInf (-q) (q^2) =
      rogersH q / qPochhammerInf (-q) (q^2) ∧
    IntervalIntegrable (fun θ : ℝ => f (ρ * exp (θ * I))) volume 0 (2*Real.pi) := by
  sorry

/-- Corrected 17.14.3: the finite factor is `(-q;q²)_n`, rather than the repeated `n+1`.
The constant-term side and G(q) side are retained exactly. -/
@[dlmf 17.14.E3]
theorem rogers_constantTerm_G_corrected (q : ℂ) (hq : ‖q‖<1) (ρ : ℝ) (hρ : 1<ρ) :
    let f := fun z => rogersThetaProduct q z /
      (qPochhammerInf z⁻¹ (q^2) * qPochhammerInf (-q) (q^2) *
        qPochhammerInf (q/z) (q^2))
    let g := fun z => rogersThetaProduct q z / qPochhammerInf z⁻¹ q
    (∑' n : ℕ, q^(n*(n+1)) /
      (qPochhammer (q^2) (q^2) n * qPochhammer (-q) (q^2) n)) =
        circleConstantTerm f ρ ∧
    circleConstantTerm f ρ = circleConstantTerm g ρ / qPochhammerInf (-q) (q^2) ∧
    circleConstantTerm g ρ / qPochhammerInf (-q) (q^2) =
      rogersG q / qPochhammerInf (-q) (q^2) ∧
    IntervalIntegrable (fun θ : ℝ => f (ρ * exp (θ * I))) volume 0 (2*Real.pi) := by
  sorry

/-- The constant-term form of G(q⁴). -/
@[dlmf 17.14.E4]
theorem rogers_constantTerm_G_four (q : ℂ) (hq : ‖q‖<1) (ρ : ℝ) (hρ : 1<ρ) :
    let f := fun z => rogersThetaProduct q z /
      (qPochhammerInf (-z⁻¹) (q^2) * qPochhammerInf q (q^2) *
        qPochhammerInf z⁻¹ (q^2))
    let g := fun z => rogersThetaProduct q z / qPochhammerInf (z⁻¹^2) (q^4)
    (∑' n : ℕ, q^(n*n) / (qPochhammer (q^2) (q^2) n * qPochhammer q (q^2) n)) =
        circleConstantTerm f ρ ∧
    circleConstantTerm f ρ = circleConstantTerm g ρ / qPochhammerInf q (q^2) ∧
    circleConstantTerm g ρ / qPochhammerInf q (q^2) =
      rogersG (q^4) / qPochhammerInf q (q^2) ∧
    IntervalIntegrable (fun θ : ℝ => f (ρ * exp (θ * I))) volume 0 (2*Real.pi) := by
  sorry

/-- The constant-term form of H(q⁴). -/
@[dlmf 17.14.E5]
theorem rogers_constantTerm_H_four (q : ℂ) (hq : ‖q‖<1) (ρ : ℝ) (hρ : 1<ρ) :
    let f := fun z => rogersThetaProduct q z /
      (qPochhammerInf (-q^2/z) (q^2) * qPochhammerInf q (q^2) *
        qPochhammerInf (q^2/z) (q^2))
    let g := fun z => rogersThetaProduct q z / qPochhammerInf (q^4/z^2) (q^4)
    (∑' n : ℕ, q^(n*n+2*n) /
      (qPochhammer (q^2) (q^2) n * qPochhammer q (q^2) (n+1))) =
        circleConstantTerm f ρ ∧
    circleConstantTerm f ρ = circleConstantTerm g ρ / qPochhammerInf q (q^2) ∧
    circleConstantTerm g ρ / qPochhammerInf q (q^2) =
      rogersH (q^4) / qPochhammerInf q (q^2) ∧
    IntervalIntegrable (fun θ : ℝ => f (ρ * exp (θ * I))) volume 0 (2*Real.pi) := by
  sorry

end DLMF.QHypergeometric
