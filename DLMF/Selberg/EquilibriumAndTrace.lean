/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Selberg.Applications
public import DLMF.OrthogonalPolynomials.Basic
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Electrostatic extrema and traces of totally positive algebraic integers

Andrews, Askey and Roy, *Special Functions*, §§8.5–8.7. Root discriminants here
are products of squared root differences, without a leading-coefficient factor.
The trace statements retain squarefreeness or irreducibility explicitly.
-/

@[expose] public section

open Polynomial Finset
open scoped Real

noncomputable section

namespace DLMF.Selberg

/-- The Jacobi electrostatic product on the unit cube. Andrews–Askey–Roy,
*Special Functions*, Theorem 8.5.1, p. 415 (synopsis AAR-8.5.1–8.5.5). -/
def jacobiElectrostaticProduct {n : ℕ} (p q : ℝ) (x : Fin n → ℝ) : ℝ :=
  (∏ i, x i ^ p * (1 - x i) ^ q) *
    ∏ i, ∏ j, if i < j then |x i - x j| else 1

/-- The Jacobi electrostatic product, unfolded. -/
theorem jacobiElectrostaticProduct_def {n : ℕ} (p q : ℝ) (x : Fin n → ℝ) :
    jacobiElectrostaticProduct p q x = (∏ i, x i ^ p * (1 - x i) ^ q) *
      ∏ i, ∏ j, if i < j then |x i - x j| else 1 := rfl

/-- The maximizing configurations are exactly the Jacobi zero sets, including permutations.
Andrews–Askey–Roy, *Special Functions*, Theorem 8.5.1, p. 415
(synopsis AAR-8.5.1–8.5.5). -/
theorem jacobiElectrostaticProduct_maximizes_iff {n : ℕ} (hn : 0 < n)
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {x : Fin n → ℝ}
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) :
    (∀ y : Fin n → ℝ, (∀ i, y i ∈ Set.Icc (0 : ℝ) 1) →
      jacobiElectrostaticProduct p q y ≤ jacobiElectrostaticProduct p q x) ↔
      Function.Injective x ∧ ∀ i,
        DLMF.OrthogonalPolynomials.jacobiPolynomialP (2 * p - 1 : ℂ) (2 * q - 1 : ℂ)
          n (1 - 2 * (x i : ℂ)) = 0 := by
  sorry

/-- Exact maximum of the squared Jacobi electrostatic product.
Andrews–Askey–Roy, *Special Functions*, Theorem 8.5.2, p. 417
(synopsis AAR-8.5.1–8.5.5). -/
theorem jacobiElectrostaticProduct_sq_maximum {n : ℕ} (hn : 0 < n)
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ∃ x : Fin n → ℝ, (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ y : Fin n → ℝ, (∀ i, y i ∈ Set.Icc (0 : ℝ) 1) →
        jacobiElectrostaticProduct p q y ≤ jacobiElectrostaticProduct p q x) ∧
      jacobiElectrostaticProduct p q x ^ 2 =
        ∏ j ∈ Icc 1 n,
          (2 * p + j - 1) ^ (2 * p + j - 1) *
            (2 * q + j - 1) ^ (2 * q + j - 1) * (j : ℝ) ^ j /
            (2 * p + 2 * q + n + j - 2) ^ (2 * p + 2 * q + n + j - 2) := by
  sorry

/-- Laguerre electrostatic equilibrium on the positive half-line.
Andrews–Askey–Roy, *Special Functions*, Theorem 8.5.4, p. 418
(synopsis AAR-8.5.1–8.5.5). -/
theorem laguerreElectrostaticProduct_maximizes_iff {n : ℕ} (hn : 0 < n)
    {p : ℝ} (hp : 0 < p) {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i) :
    (∀ y : Fin n → ℝ, (∀ i, 0 ≤ y i) →
      (∏ i, y i ^ p * Real.exp (-y i)) *
          (∏ i, ∏ j, if i < j then |y i - y j| else 1) ≤
        (∏ i, x i ^ p * Real.exp (-x i)) *
          (∏ i, ∏ j, if i < j then |x i - x j| else 1)) ↔
      Function.Injective x ∧ ∀ i,
        DLMF.OrthogonalPolynomials.laguerrePolynomialL (2 * p - 1 : ℂ) n
          (2 * (x i : ℂ)) = 0 := by
  sorry

/-- Hermite electrostatic equilibrium on the real line.
Andrews–Askey–Roy, *Special Functions*, Theorem 8.5.5, p. 419
(synopsis AAR-8.5.1–8.5.5). -/
theorem hermiteElectrostaticProduct_maximizes_iff {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) :
    (∀ y : Fin n → ℝ,
      Real.exp (-(∑ i, y i ^ 2) / 2) *
          (∏ i, ∏ j, if i < j then |y i - y j| else 1) ≤
        Real.exp (-(∑ i, x i ^ 2) / 2) *
          (∏ i, ∏ j, if i < j then |x i - x j| else 1)) ↔
      Function.Injective x ∧ ∀ i,
        (DLMF.OrthogonalPolynomials.hermitePolynomialH n).eval₂ (Int.castRingHom ℝ)
          (x i) = 0 := by
  sorry

/-- The positive Siegel parameter exists uniquely for every distinct positive configuration.
Andrews–Askey–Roy, *Special Functions*, Theorem 8.6.2, p. 420
(synopsis AAR-8.6.1–8.6.7). -/
theorem existsUnique_siegelParameter {n : ℕ} (hn : 2 ≤ n) {x : Fin n → ℝ}
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x) :
    ∃! t : ℝ, 0 < t ∧ siegelP n t = (∏ i, x i) ^ (n - 1) / siegelDiscriminant x := by
  sorry

/-- Schur's trace–discriminant inequality.
Andrews–Askey–Roy, *Special Functions*, Corollary 8.6.4, p. 422
(synopsis AAR-8.6.1–8.6.7). -/
theorem discriminant_le_mean_pow {n : ℕ} (hn : 2 ≤ n) {x : Fin n → ℝ}
    (hx : ∀ i, 0 < x i) :
    ((n - 1 : ℕ) : ℝ) ^ (n * (n - 1)) * siegelDiscriminant x /
        (∏ k ∈ Icc 2 n, (k : ℝ) ^ k * ((k - 1 : ℕ) : ℝ) ^ (k - 1)) ≤
      ((∑ i, x i) / n) ^ (n * (n - 1)) := by
  sorry

/-- The Siegel constant gives an eventual lower bound for traces of squarefree monic
integer polynomials with positive roots. Andrews–Askey–Roy, *Special Functions*,
Theorem 8.6.5, p. 423 (synopsis AAR-8.6.1–8.6.7). Squarefreeness excludes repeated-root
counterexamples to the standalone printed statement. -/
theorem eventually_trace_gt_siegelConstant {θ : ℝ} (hθ : 0 < θ)
    (heq : (1 + θ) ^ 2 * Real.log (1 + 1 / θ) + Real.log θ - θ - 1 = 0)
    {lam : ℝ} (hlam : lam < Real.exp 1 * (1 + 1 / θ) ^ (-θ)) :
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ P : ℤ[X], P.Monic → Squarefree P →
      ∀ x : Fin n → ℝ, (∀ i, 0 < x i) →
        P.map (Int.castRingHom ℝ) = ∏ i, (X - C (x i)) →
          lam * n < ∑ i, x i := by
  sorry

/-- The trace of a totally positive algebraic integer exceeds three halves of its degree,
apart from the three explicitly listed conjugate values.
Andrews–Askey–Roy, *Special Functions*, Theorem 8.6.7, p. 425
(synopsis AAR-8.6.1–8.6.7). Irreducible polynomials encode conjugates without repetition. -/
theorem trace_gt_three_halves {n : ℕ} (hn : 0 < n) {P : ℤ[X]}
    (hmonic : P.Monic) (hirred : Irreducible P)
    (hlinear : P ≠ X - 1) (hquadratic : P ≠ X ^ 2 - C 3 * X + 1)
    (x : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    (hfactor : P.map (Int.castRingHom ℝ) = ∏ i, (X - C (x i))) :
    3 * n / 2 < ∑ i, x i := by
  sorry

/-- Equally spaced unit-circle points maximize the product of pairwise distances.
Andrews–Askey–Roy, *Special Functions*, Theorem 8.7.1, p. 425
(synopsis AAR-8.7.1–8.9.1). The product formulation also covers collisions. -/
theorem prod_unitCircle_dist_le {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) :
    (∏ i, ∏ j, if i < j then ‖z i - z j‖ ^ 2 else 1) ≤ (n : ℝ) ^ n := by
  sorry

/-- Equality in the circle energy bound characterizes rotated regular polygons.
Andrews–Askey–Roy, *Special Functions*, Theorem 8.7.1, p. 425
(synopsis AAR-8.7.1–8.9.1). -/
theorem prod_unitCircle_dist_eq_iff {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) :
    (∏ i, ∏ j, if i < j then ‖z i - z j‖ ^ 2 else 1) = (n : ℝ) ^ n ↔
      Function.Injective z ∧ ∃ w : ℂ, ‖w‖ = 1 ∧ ∀ i, z i ^ n = w := by
  sorry

end DLMF.Selberg
