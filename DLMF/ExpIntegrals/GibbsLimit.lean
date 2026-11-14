/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ExpIntegrals.Basic

/-!
# The exact Gibbs limit for the square-wave Fourier sums

Temme, *Special Functions* (1996), §7.4, pp. 181–183, synopsis TEM-07-10.
The overshoot is described by an exact sine integral and a strict inequality,
without a decimal approximation.
-/

@[expose] public noncomputable section
open Filter Finset
open scoped Real Topology Nat
namespace DLMF.Confluent

/-- The odd-frequency square-wave Fourier partial sum,
Temme pp. 181–183, synopsis TEM-07-10. -/
def Real.squareWaveFourierSum (n : ℕ) (x : ℝ) : ℝ :=
  4 / Real.pi * ∑ k ∈ range n, Real.sin ((2 * k + 1) * x) / (2 * k + 1)

/-- The defining trigonometric sum for the Gibbs limit, Temme §7.4. -/
theorem Real.squareWaveFourierSum_def (n : ℕ) (x : ℝ) : Real.squareWaveFourierSum n x =
    4 / Real.pi * ∑ k ∈ range n, Real.sin ((2 * k + 1) * x) / (2 * k + 1) := rfl

/-- Uniform sine-integral approximation away from the second discontinuity,
Temme pp. 181–183, synopsis TEM-07-10. -/
theorem Real.squareWaveFourierSum_sinIntegral_uniform {δ : ℝ}
    (hδ : 0 < δ) (hδπ : δ < Real.pi) :
    ∃ C : ℝ, 0 < C ∧ ∃ A : ℕ, 1 ≤ A ∧ ∀ n ≥ A,
      ∀ x ∈ Set.Icc (0 : ℝ) (Real.pi - δ),
        |Real.squareWaveFourierSum n x -
          2 / Real.pi * Real.sinIntegral (2 * n * x)| ≤ C / n := by
  sorry

/-- The scaled Gibbs profile, Temme pp. 181–183, synopsis TEM-07-10. -/
theorem Real.tendsto_squareWaveFourierSum_scaled {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun n : ℕ => Real.squareWaveFourierSum n (c / (2 * n)))
      atTop (𝓝 (2 / Real.pi * Real.sinIntegral c)) := by
  sorry

/-- The first positive Fourier peak occurs at `π/(2n)`, Temme's Gibbs discussion,
pp. 181–183, synopsis TEM-07-10. -/
theorem Real.squareWaveFourierSum_le_first_peak {n : ℕ} (hn : 1 ≤ n)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (Real.pi / n)) :
    Real.squareWaveFourierSum n x ≤ Real.squareWaveFourierSum n (Real.pi / (2 * n)) := by
  sorry

/-- The exact first-peak limiting value is larger than the limiting plateau,
Temme pp. 181–183, synopsis TEM-07-10. -/
theorem Real.one_lt_gibbs_peak : 1 < 2 / Real.pi * Real.sinIntegral Real.pi := by
  sorry

end DLMF.Confluent
