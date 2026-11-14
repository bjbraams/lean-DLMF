/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.PositiveZeroSequence
public import DLMF.Bessel.Lommel
public import Mathlib.Analysis.BoundedVariation

/-!
# Fourier–Bessel convergence

Temme, *Special Functions* (1996), §9.8, (9.64)–(9.67), pp. 246–247,
synopsis TEM-09-16. Positive zeros are completely enumerated, with the first
zero at index zero. Partial sums are ordered; no absolute convergence is asserted.
-/

@[expose] public noncomputable section
open Complex Filter MeasureTheory
open scoped Real Nat Topology
namespace DLMF.Bessel

/-- A complete increasing enumeration of the positive `J_ν` zeros, Temme
Theorem 9.3 and §9.8, synopses TEM-09-12/16. -/
def IsPositiveBesselZeroSequence (ν : ℝ) (j : ℕ → ℝ) : Prop :=
  StrictMono j ∧ Tendsto j atTop atTop ∧ (∀ n, 0 < j n ∧ besselJ ν (j n) = 0) ∧
    ∀ x : ℝ, (0 < x ∧ besselJ ν x = 0) ↔ ∃ n, j n = x

/-- The defining positivity, completeness and ordering conditions, TEM-09-12/16. -/
theorem isPositiveBesselZeroSequence_iff (ν : ℝ) (j : ℕ → ℝ) :
    IsPositiveBesselZeroSequence ν j ↔
      StrictMono j ∧ Tendsto j atTop atTop ∧ (∀ n, 0 < j n ∧ besselJ ν (j n) = 0) ∧
        ∀ x : ℝ, (0 < x ∧ besselJ ν x = 0) ↔ ∃ n, j n = x := Iff.rfl

/-- A sequence entry is positive, Temme Theorem 9.3. -/
theorem IsPositiveBesselZeroSequence.pos {ν : ℝ} {j : ℕ → ℝ}
    (hj : IsPositiveBesselZeroSequence ν j) (n : ℕ) : 0 < j n := hj.2.2.1 n |>.1

/-- A sequence entry is a zero, Temme Theorem 9.3. -/
theorem IsPositiveBesselZeroSequence.eq_zero {ν : ℝ} {j : ℕ → ℝ}
    (hj : IsPositiveBesselZeroSequence ν j) (n : ℕ) : besselJ ν (j n) = 0 := hj.2.2.1 n |>.2

/-- The Fourier–Bessel coefficient in Temme (9.64)–(9.65), synopsis TEM-09-16.
The integral formula is totalized; convergence theorems specify its integrability. -/
def fourierBesselCoefficient (ν : ℝ) (j : ℕ → ℝ) (f : ℝ → ℂ) (n : ℕ) : ℂ :=
  2 * (∫ t : ℝ in (0 : ℝ)..1, (t : ℂ) * f t * besselJ ν (j n * t)) /
    besselJ (ν + 1) (j n) ^ 2

/-- The coefficient's defining weighted integral, Temme (9.64)–(9.65). -/
theorem fourierBesselCoefficient_def (ν : ℝ) (j : ℕ → ℝ) (f : ℝ → ℂ) (n : ℕ) :
    fourierBesselCoefficient ν j f n =
      2 * (∫ t : ℝ in (0 : ℝ)..1, (t : ℂ) * f t * besselJ ν (j n * t)) /
        besselJ (ν + 1) (j n) ^ 2 := rfl

/-- Dirichlet–Jordan convergence in the interior, Temme §9.8,
(9.64)–(9.67), pp. 246–247, synopsis TEM-09-16. -/
theorem tendsto_sum_fourierBesselCoefficient {ν : ℝ} (hν : -1 / 2 < ν)
    (j : ℕ → ℝ) (hj : IsPositiveBesselZeroSequence ν j)
    (f : ℝ → ℂ) (hf : IntegrableOn (fun t : ℝ => (Real.sqrt t : ℂ) * f t) (Set.Icc 0 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hBV : ∃ δ : ℝ, 0 < δ ∧ BoundedVariationOn f (Set.Icc (x - δ) (x + δ)))
    (fm fp : ℂ) (hleft : Tendsto f (𝓝[<] x) (𝓝 fm))
    (hright : Tendsto f (𝓝[>] x) (𝓝 fp)) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      fourierBesselCoefficient ν j f n * besselJ ν (j n * x))
      atTop (𝓝 ((fm + fp) / 2)) := by
  sorry

/-- The explicit power expansion, Temme (9.67), synopsis TEM-09-16.
The endpoint `x=1` is excluded, since all individual modes vanish there. -/
theorem tendsto_sum_besselJ_div_zero_mul_succ {ν : ℝ} (hν : 0 < ν)
    (j : ℕ → ℝ) (hj : IsPositiveBesselZeroSequence ν j)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      2 * besselJ ν (j n * x) / (j n * besselJ (ν + 1) (j n)))
      atTop (𝓝 ((x ^ ν : ℝ) : ℂ)) := by
  sorry

end DLMF.Bessel
