/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.SphericalHarmonics.Basic
public import DLMF.OrthogonalPolynomials.Basic
public import TauCeti.Analysis.MvPolynomial.Sphere
public import TauCeti.RingTheory.MvPolynomial.Harmonic.Orthogonal

/-!
# Zonal harmonics and addition in arbitrary dimension

The algebraic Fischer decomposition and dimension formulas are supplied by pinned TauCeti.
This module states the zonal, unisolvence, addition and Funk–Hecke results of Andrews,
Askey and Roy, *Special Functions*, §§9.3–9.7 beyond the three-dimensional API.
Surface integrals use the existing unnormalized `Measure.toSphere` convention.
-/

@[expose] public section

open MvPolynomial MeasureTheory
open scoped Real

noncomputable section

namespace DLMF.SphericalHarmonics

/-- The polynomial-coordinate spherical Laplacian eigenvalue identity for a homogeneous
harmonic polynomial. Andrews–Askey–Roy, *Special Functions*, §9.5
(synopsis AAR-9.1–9.5). The expression is the tangential Laplacian on the unit sphere. -/
theorem spherical_laplacian_eigenvalue {n k : ℕ} (hn : 2 ≤ n)
    {P : MvPolynomial (Fin n) ℝ} (hP : IsHarmonicHomogeneous k P)
    (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    (∑ i, eval x (pderiv i (pderiv i P))) -
        (∑ i, ∑ j, x i * x j * eval x (pderiv i (pderiv j P))) -
        (n - 1 : ℝ) * (∑ i, x i * eval x (pderiv i P)) =
      -(k : ℝ) * (k + n - 2) * eval x P := by
  sorry

/-- Zonal harmonics invariant under the stabilizer of a unit vector form a line.
Andrews–Askey–Roy, *Special Functions*, Lemma 9.6.1, p. 454
(synopsis AAR-9.6.1–9.8.1). Invariance is polynomial invariance, including all radii. -/
theorem exists_zonal_generator {n : ℕ} (hn : 3 ≤ n) (k : ℕ)
    (η : Fin n → ℝ) (hη : ∑ i, η i ^ 2 = 1) :
    ∃ Z : MvPolynomial (Fin n) ℝ, IsHarmonicHomogeneous k Z ∧ Z ≠ 0 ∧
      (∀ (A : Matrix.orthogonalGroup (Fin n) ℝ),
        (A : Matrix (Fin n) (Fin n) ℝ).mulVec η = η →
        ∀ x : Fin n → ℝ, eval ((A : Matrix (Fin n) (Fin n) ℝ).mulVec x) Z = eval x Z) ∧
      ∀ P : MvPolynomial (Fin n) ℝ, IsHarmonicHomogeneous k P →
        (∀ (A : Matrix.orthogonalGroup (Fin n) ℝ),
          (A : Matrix (Fin n) (Fin n) ℝ).mulVec η = η →
          ∀ x : Fin n → ℝ, eval ((A : Matrix (Fin n) (Fin n) ℝ).mulVec x) P = eval x P) →
        ∃ c : ℝ, P = c • Z := by
  sorry

/-- A set of as many sphere points as the harmonic dimension determines every harmonic
of a fixed degree. Andrews–Askey–Roy, *Special Functions*, Theorem 9.6.4, p. 458
(synopsis AAR-9.6.1–9.8.1). This is the evaluation-functional form of the zonal basis result. -/
theorem exists_unisolvent_sphere_points {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    ∃ η : Fin (harmonicHomogeneousDim n k) →
        Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      Function.Injective (fun P : harmonicSubmodule (Fin n) ℝ k =>
        fun j => eval (fun i => (η j).val i) P.val) := by
  sorry

/-- The addition formula for an orthonormal real harmonic basis in any dimension at least
three. Andrews–Askey–Roy, *Special Functions*, Theorem 9.6.3, p. 456
(synopsis AAR-9.6.1–9.8.1). The coefficient uses unnormalized surface area. -/
theorem spherical_addition_dimension {n : ℕ} (hn : 3 ≤ n) (k : ℕ)
    (S : Fin (harmonicHomogeneousDim n k) → MvPolynomial (Fin n) ℝ)
    (hS : ∀ j, IsHarmonicHomogeneous k (S j))
    (horth : ∀ i j, sphericalHarmonicInner (S i) (S j) = if i = j then 1 else 0)
    (x y : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) (hy : ∑ i, y i ^ 2 = 1) :
    (∑ j, (eval x (S j) : ℂ) * (eval y (S j) : ℂ)) =
      (harmonicHomogeneousDim n k : ℂ) * Complex.Gamma ((n : ℂ) / 2) /
        (2 * (Real.pi : ℂ) ^ ((n : ℂ) / 2)) *
        (DLMF.OrthogonalPolynomials.ultrasphericalPolynomial (((n : ℂ) - 2) / 2) k
          (∑ i, x i * y i : ℝ) /
        DLMF.OrthogonalPolynomials.ultrasphericalPolynomial (((n : ℂ) - 2) / 2) k 1) := by
  sorry

/-- Funk–Hecke in arbitrary dimension, for the actual surface measure of the sphere.
Andrews–Askey–Roy, *Special Functions*, Theorem 9.7.1, p. 460
(synopsis AAR-9.6.1–9.8.1). -/
theorem funk_hecke_dimension {n : ℕ} (hn : 3 ≤ n) (k : ℕ)
    {f : ℝ → ℂ} (hf : ContinuousOn f (Set.Icc (-1) 1))
    (P : MvPolynomial (Fin n) ℝ) (hP : IsHarmonicHomogeneous k P)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (∫ y : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      f (∑ i, x.val i * y.val i) * (eval (fun i => y.val i) P : ℂ)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) =
      (2 * (Real.pi : ℂ) ^ (((n : ℂ) - 1) / 2) /
        (Complex.Gamma (((n : ℂ) - 1) / 2) *
          DLMF.OrthogonalPolynomials.ultrasphericalPolynomial (((n : ℂ) - 2) / 2) k 1)) *
        (∫ t : ℝ in (-1 : ℝ)..1, f t *
          DLMF.OrthogonalPolynomials.ultrasphericalPolynomial (((n : ℂ) - 2) / 2) k t *
          ((1 - t ^ 2) ^ (((n : ℝ) - 3) / 2) : ℝ)) *
        (eval (fun i => x.val i) P : ℂ) := by
  sorry

end DLMF.SphericalHarmonics
