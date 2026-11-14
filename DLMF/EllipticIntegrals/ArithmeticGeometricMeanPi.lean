/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Quadratic

/-!
# Monotone arithmetic-geometric-mean approximants to pi

Andrews, Askey and Roy, *Special Functions*, Lemmas 3.2.9–3.2.10 and
Theorem 3.2.11, pp. 136–139. The canonical arithmetic and geometric sequences
are reused; the squared difference is kept before any square root is introduced.
-/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped NNReal

namespace DLMF.EllipticIntegrals

/-- The one-step relation between the complete elliptic square-root and inverse-square-root
integrals along the arithmetic-geometric-mean sequence. Andrews–Askey–Roy,
*Special Functions*, Lemmas 3.2.9–3.2.10, pp. 136–138
(synopsis AAR-3.2.3–3.2.11). -/
theorem agm_squareRoot_integral_step (a₀ b₀ : ℝ≥0) (ha₀ : 0 < a₀) (hb₀ : 0 < b₀) (n : ℕ) :
    let a := fun j : ℕ => (agmSeqA a₀ b₀ j : ℝ)
    let b := fun j : ℕ => (agmSeqG a₀ b₀ j : ℝ)
    2 * (∫ t : ℝ in 0..(Real.pi / 2),
        Real.sqrt (a (n + 1) ^ 2 * Real.cos t ^ 2 + b (n + 1) ^ 2 * Real.sin t ^ 2)) -
      (∫ t : ℝ in 0..(Real.pi / 2),
        Real.sqrt (a n ^ 2 * Real.cos t ^ 2 + b n ^ 2 * Real.sin t ^ 2)) =
      a n * b n * ∫ t : ℝ in 0..(Real.pi / 2),
        (Real.sqrt (a n ^ 2 * Real.cos t ^ 2 + b n ^ 2 * Real.sin t ^ 2))⁻¹ := by
  sorry

/-- The exact AGM evaluation of the circle constant with its convergent correction series.
Andrews–Askey–Roy, *Special Functions*, Theorem 3.2.11, p. 139
(synopsis AAR-3.2.3–3.2.11). -/
theorem pi_eq_agm_correction_series :
    let b₀ : ℝ≥0 := NNReal.sqrt (1 / 2)
    let c := fun n : ℕ => (agmSeqA 1 b₀ n : ℝ) ^ 2 - (agmSeqG 1 b₀ n : ℝ) ^ 2
    Summable (fun n : ℕ => (2 : ℝ) ^ n * c n) ∧
      (∑' n : ℕ, (2 : ℝ) ^ n * c n) < 1 ∧
      Real.pi = (NNReal.agm (NNReal.sqrt 2) 1 : ℝ) ^ 2 /
        (1 - ∑' n : ℕ, (2 : ℝ) ^ n * c n) := by
  sorry

/-- The finite AGM correction quotients increase strictly to pi.
Andrews–Askey–Roy, *Special Functions*, Theorem 3.2.11, p. 139
(synopsis AAR-3.2.3–3.2.11). Their denominators remain strictly positive. -/
theorem strictMono_tendsto_agm_pi_approximants :
    let b₀ : ℝ≥0 := NNReal.sqrt (1 / 2)
    let a := fun n : ℕ => (agmSeqA 1 b₀ n : ℝ)
    let b := fun n : ℕ => (agmSeqG 1 b₀ n : ℝ)
    let D := fun m : ℕ => 1 - ∑ n ∈ Finset.range (m + 1), (2 : ℝ) ^ n * (a n ^ 2 - b n ^ 2)
    let P := fun m : ℕ => 2 * a (m + 1) ^ 2 / D m
    (∀ m, 0 < D m) ∧ StrictMono P ∧ Tendsto P atTop (nhds Real.pi) := by
  sorry

end DLMF.EllipticIntegrals
