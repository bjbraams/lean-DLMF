/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# Time-harmonic and Cartesian separation of the wave equation

Temme, *Special Functions* (1996), Chapter 4, pp. 79–82, synopsis TEM-04-01.
The Laplacian is Mathlib's Cartesian Laplacian on Euclidean three-space.
Complex separation constants allow oscillatory and exponentially growing factors alike.
-/

@[expose] public noncomputable section
open Complex Laplacian
namespace Complex

/-- Time-harmonic separation of the wave equation is equivalent to Helmholtz's equation,
Temme Chapter 4, pp. 79–82, synopsis TEM-04-01. -/
theorem wave_time_harmonic_iff {f : EuclideanSpace ℝ (Fin 3) → ℂ}
    {x : EuclideanSpace ℝ (Fin 3)} (hf : ContDiffAt ℝ 2 f x) (t ω c : ℝ) (hc : c ≠ 0) :
    (iteratedDeriv 2 (fun s : ℝ => f x * exp (I * ω * s)) t =
      c ^ 2 * laplacian (fun y => f y * exp (I * ω * t)) x) ↔
      laplacian f x + ((ω / c : ℝ) : ℂ) ^ 2 * f x = 0 := by
  sorry

/-- A Cartesian product of three one-variable modes solves Helmholtz's equation,
Temme Chapter 4, pp. 79–82, synopsis TEM-04-01. -/
theorem laplacian_prod_eq_neg_sq_mul (f : Fin 3 → ℝ → ℂ) (α : Fin 3 → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hode : ∀ i x, iteratedDeriv 2 (f i) x + (α i) ^ 2 * f i x = 0)
    (x : EuclideanSpace ℝ (Fin 3)) :
    laplacian (fun y : EuclideanSpace ℝ (Fin 3) => ∏ i : Fin 3, f i (y i)) x =
      -(∑ i : Fin 3, (α i) ^ 2) * ∏ i : Fin 3, f i (x i) := by
  sorry

/-- Conversely, a nonzero Cartesian product solution has constant separated frequencies,
Temme Chapter 4, pp. 79–82, synopsis TEM-04-01. Nonzero factors exclude the
identically zero product, which imposes no differential equation on its factors. -/
theorem exists_separation_constants_of_laplacian_prod (f : Fin 3 → ℝ → ℂ) (k : ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hne : ∀ i, ∃ x, f i x ≠ 0)
    (hpde : ∀ x : EuclideanSpace ℝ (Fin 3),
      laplacian (fun y : EuclideanSpace ℝ (Fin 3) => ∏ i : Fin 3, f i (y i)) x +
        k ^ 2 * ∏ i : Fin 3, f i (x i) = 0) :
    ∃ α : Fin 3 → ℂ, (∑ i, (α i) ^ 2) = k ^ 2 ∧
      ∀ i x, iteratedDeriv 2 (f i) x + (α i) ^ 2 * f i x = 0 := by
  sorry

end Complex
