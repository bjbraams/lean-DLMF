/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic.NormsAndKernels
public import Mathlib.MeasureTheory.Measure.Sum
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Summable perturbations of constant Jacobi coefficients

Andrews, Askey and Roy, *Special Functions*, Theorem 6.6.2. The orthogonality
measure has a continuous positive interior density and only pure point mass
outside that interval. Endpoint masses are retained explicitly.
-/

@[expose] public section

open MeasureTheory Filter Polynomial
open scoped Topology NNReal ENNReal

noncomputable section

namespace DLMF.OrthogonalPolynomials

/-- Summable Jacobi recurrence perturbations give the absolutely continuous interior
measure and the almost-everywhere Szegő limsup. Andrews–Askey–Roy,
*Special Functions*, Theorem 6.6.2 (synopsis AAR-6.5.1–6.6.2). -/
theorem exists_density_of_summable_recurrence_perturbation
    (μ : Measure ℝ) [IsFiniteMeasure μ] (p : ℕ → ℝ[X])
    (hp : IsOrthogonalPolynomials μ p) (A B C : ℕ → ℝ)
    (hA : ∀ n : ℕ, 0 < A n) (hC : ∀ n : ℕ, 0 < C (n + 1))
    (hzero : p 1 = (Polynomial.C (A 0) * X + Polynomial.C (B 0)) * p 0)
    (hrec : ∀ n : ℕ, p (n + 2) =
      (Polynomial.C (A (n + 1)) * X + Polynomial.C (B (n + 1))) * p (n + 1) -
        Polynomial.C (C (n + 1)) * p n)
    {δ : ℝ} (hδ : 0 < δ)
    (hsum : Summable (fun n : ℕ => |B n / A n| +
      |Real.sqrt (C (n + 1) / (A n * A (n + 1))) - δ / 2|)) :
    ∃ w : ℝ → ℝ, ∃ locations : ℕ → ℝ, ∃ masses : ℕ → ℝ≥0∞,
      (∀ x : ℝ, 0 ≤ w x) ∧ ContinuousOn w (Set.Ioo (-δ) δ) ∧
      (∀ x ∈ Set.Ioo (-δ) δ, 0 < w x) ∧
      (∀ x : ℝ, x ∉ Set.Icc (-δ) δ → w x = 0) ∧
      (∀ j : ℕ, masses j ≠ 0 → locations j ∉ Set.Ioo (-δ) δ) ∧
      μ = volume.withDensity (fun x => ENNReal.ofReal (w x)) +
        Measure.sum (fun j : ℕ => masses j • Measure.dirac (locations j)) ∧
      ∀ᵐ x ∂volume.restrict (Set.Ioo (-δ) δ),
        limsup (fun n : ℕ => w x * Real.sqrt (δ ^ 2 - x ^ 2) *
          (p n).eval x ^ 2 / squaredNorm μ p n) atTop = 2 / Real.pi := by
  sorry

end DLMF.OrthogonalPolynomials
