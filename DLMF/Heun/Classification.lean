/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Heun.Basic
public import DLMFMathlib.Analysis.ODE.FuchsianClassification

/-!
# Classification of the normalized four-singularity equation

After moving three finite singularities to `0,1,A` and setting one exponent at
each to zero, the equation has exactly Heun's coefficients and one arbitrary
accessory parameter. This is Kristensson, *Second Order Differential Equations*,
Chapter 4, §4.4, pp. 56–58. Actual analytic functions off the marked points are
specified, so arbitrary totalizations do not invalidate the coefficient identities.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Topology

namespace DLMF.Heun

/-- The normalized finite/infinity indicial germs identify Heun's equation and its
unique accessory parameter. The infinity exponent sum derives the Fuchs relation;
the exponent product fixes the leading numerator but leaves the accessory free.
Kristensson, Chapter 4, (4.10)–(4.11), pp. 56–58. -/
theorem existsUnique_heun_coefficients_of_regularSingular
    {A α β c d e : ℂ} (hA₀ : A ≠ 0) (hA₁ : A ≠ 1) {p q : ℂ → ℂ}
    (hp : AnalyticOnNhd ℂ p ({0, 1, A} : Set ℂ)ᶜ)
    (hq : AnalyticOnNhd ℂ q ({0, 1, A} : Set ℂ)ᶜ)
    (hlocal : ∀ i : Fin 3, ∃ P Q : ℂ → ℂ,
      AnalyticAt ℂ P (![0, 1, A] i) ∧ AnalyticAt ℂ Q (![0, 1, A] i) ∧
      (fun z => (z - ![0, 1, A] i) * p z) =ᶠ[𝓝[≠] ![0, 1, A] i] P ∧
      (fun z => (z - ![0, 1, A] i) ^ 2 * q z) =ᶠ[𝓝[≠] ![0, 1, A] i] Q ∧
      P (![0, 1, A] i) = ![c, d, e] i ∧ Q (![0, 1, A] i) = 0)
    (hinfty : ∃ P Q : ℂ → ℂ, AnalyticAt ℂ P 0 ∧ AnalyticAt ℂ Q 0 ∧
      (fun t => 2 - p t⁻¹ / t) =ᶠ[𝓝[≠] 0] P ∧
      (fun t => q t⁻¹ / t ^ 2) =ᶠ[𝓝[≠] 0] Q ∧
      P 0 = 1 - α - β ∧ Q 0 = α * β) :
    α + β + 1 = c + d + e ∧
      ∃! accessory : ℂ, ∀ z : ℂ, z ∉ ({0, 1, A} : Set ℂ) →
        p z = heunCoeffP A c d e z ∧ q z = heunCoeffR A accessory α β z := by
  sorry

end DLMF.Heun
