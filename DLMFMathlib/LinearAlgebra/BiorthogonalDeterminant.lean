/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The biorthogonal determinant construction

Andrews, Askey and Roy, *Special Functions*, Lemma 6.3.1 and Corollary 6.3.2,
pp. 293–294. Distinct row and column families are permitted, and positivity
and linear independence are unnecessary for the orthogonality identity itself.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X]

/-- The moment determinant whose last row consists of the column functions evaluated at `x`.
Andrews–Askey–Roy, *Special Functions*, Lemma 6.3.1 and Corollary 6.3.2
(synopsis AAR-6.3.1–6.4.3). -/
def biorthogonalDeterminant (μ : Measure X) {n : ℕ}
    (φ : Fin n → X → ℂ) (ψ : Fin (n + 1) → X → ℂ) (x : X) : ℂ :=
  Matrix.det (fun i j : Fin (n + 1) =>
    if h : i.val < n then ∫ t : X, φ ⟨i.val, h⟩ t * ψ j t ∂μ else ψ j x)

/-- The defining bordered moment determinant. -/
theorem biorthogonalDeterminant_def (μ : Measure X) {n : ℕ}
    (φ : Fin n → X → ℂ) (ψ : Fin (n + 1) → X → ℂ) (x : X) :
    biorthogonalDeterminant μ φ ψ x =
      Matrix.det (fun i j : Fin (n + 1) =>
        if h : i.val < n then ∫ t : X, φ ⟨i.val, h⟩ t * ψ j t ∂μ else ψ j x) := rfl

/-- The bordered moment determinant is orthogonal to every row function.
Andrews–Askey–Roy, *Special Functions*, Lemma 6.3.1 and Corollary 6.3.2,
pp. 293–294 (synopsis AAR-6.3.1–6.4.3). Taking the same functions in both
slots is the Gram determinant construction; no positivity assumption is needed. -/
theorem integral_mul_biorthogonalDeterminant_eq_zero (μ : Measure X) {n : ℕ}
    (φ : Fin n → X → ℂ) (ψ : Fin (n + 1) → X → ℂ)
    (hint : ∀ i j, Integrable (fun x : X => φ i x * ψ j x) μ) (k : Fin n) :
    Integrable (fun x : X => φ k x * biorthogonalDeterminant μ φ ψ x) μ ∧
      (∫ x : X, φ k x * biorthogonalDeterminant μ φ ψ x ∂μ) = 0 := by
  sorry

end MeasureTheory
