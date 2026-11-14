/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Statistical.Basic.VonMises
public import TauCeti.Analysis.SpecialFunctions.Erf
public import DLMF.Confluent.Basic.IncompleteGamma

/-!
# Fourier and Gaussian expansions of the von Mises distribution

Temme, *Special Functions* (1996), §11.5, (11.85)–(11.89), synopsis TEM-11-20.
The Gaussian moments are oriented integrals, retaining the sign at negative angles.
The error estimates are uniform over the full closed angular interval.
-/

@[expose] public noncomputable section
open MeasureTheory Filter Asymptotics
open scoped Real Topology Nat
namespace DLMF.Statistical

/-- The oriented Gaussian moment of Temme (11.88), synopsis TEM-11-20. -/
def Real.vonMisesGaussianMoment (n : ℕ) (θ κ : ℝ) : ℝ :=
  ∫ u : ℝ in (0 : ℝ)..Real.sin (θ / 2), Real.exp (-2 * κ * u ^ 2) * u ^ (2 * n)

/-- The Gaussian moment's defining formula, Temme (11.88). -/
theorem Real.vonMisesGaussianMoment_def (n : ℕ) (θ κ : ℝ) :
    Real.vonMisesGaussianMoment n θ κ =
      ∫ u : ℝ in (0 : ℝ)..Real.sin (θ / 2), Real.exp (-2 * κ * u ^ 2) * u ^ (2 * n) := rfl

/-- Reflection symmetry, Temme (11.85)–(11.86), synopsis TEM-11-20. -/
theorem Real.vonMisesCDF_neg (θ κ : ℝ) :
    Real.vonMisesCDF (-θ) κ = 1 - Real.vonMisesCDF θ κ := by
  sorry

/-- The Fourier expansion, Temme (11.86), synopsis TEM-11-20. -/
theorem Real.hasSum_vonMisesCDF_fourier (κ : ℝ) {θ : ℝ}
    (hθ : θ ∈ Set.Icc (-Real.pi) Real.pi) :
    HasSum (fun n : ℕ => Real.besselI (n + 1) κ * Real.sin ((n + 1) * θ) /
      (Real.pi * (n + 1) * Real.besselI 0 κ))
      (Real.vonMisesCDF θ κ - (θ + Real.pi) / (2 * Real.pi)) := by
  sorry

/-- The convergent Gaussian-moment expansion, Temme (11.88), synopsis TEM-11-20. -/
theorem Real.hasSum_vonMisesGaussianMoment {κ θ : ℝ} (hκ : 0 < κ)
    (hθ : θ ∈ Set.Icc (-Real.pi) Real.pi) :
    HasSum (fun n : ℕ => (ascPochhammer ℝ n).eval (1 / 2) / n.factorial *
      Real.vonMisesGaussianMoment n θ κ)
      ((Real.vonMisesCDF θ κ - 1 / 2) *
        (Real.pi * Real.besselI 0 κ) / Real.exp κ) := by
  sorry

/-- The Gaussian moments in terms of lower incomplete Gamma, including the
negative-angle sign, Temme (11.89), synopsis TEM-11-20. -/
theorem Real.vonMisesGaussianMoment_eq_lowerIncompleteGamma {κ : ℝ} (hκ : 0 < κ)
    (n : ℕ) (θ : ℝ) :
    (Real.vonMisesGaussianMoment n θ κ : ℂ) =
      (if Real.sin (θ / 2) < 0 then (-1 : ℝ) else if Real.sin (θ / 2) = 0 then 0 else 1) *
        DLMF.Confluent.lowerIncompleteGamma (n + 1 / 2)
          (2 * κ * Real.sin (θ / 2) ^ 2) /
        (2 * ((2 * κ : ℝ) ^ ((n : ℝ) + 1 / 2) : ℝ)) := by
  sorry

/-- Uniform finite Gaussian-moment error bound, Temme (11.88), synopsis TEM-11-20. -/
theorem Real.vonMisesCDF_gaussian_uniform (N : ℕ) (hN : 1 ≤ N) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ κ ≥ A, ∀ θ ∈ Set.Icc (-Real.pi) Real.pi,
      |Real.vonMisesCDF θ κ - 1 / 2 - Real.exp κ / (Real.pi * Real.besselI 0 κ) *
        ∑ n ∈ Finset.range N, (ascPochhammer ℝ n).eval (1 / 2) / n.factorial *
          Real.vonMisesGaussianMoment n θ κ| ≤ C * κ ^ (-(N : ℝ)) := by
  sorry

/-- Uniform leading Gaussian approximation, Temme (11.88)–(11.89),
synopsis TEM-11-20. -/
theorem Real.vonMisesCDF_erfc_uniform :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ κ ≥ A, ∀ θ ∈ Set.Icc (-Real.pi) Real.pi,
      |Real.vonMisesCDF θ κ -
        TauCeti.Real.erfc (-Real.sqrt (2 * κ) * Real.sin (θ / 2)) / 2| ≤ C / κ := by
  sorry

end DLMF.Statistical
