/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Riemann
public import DLMFMathlib.Analysis.ODE.FuchsianClassification

/-!
# Identifying a three-singularity equation from its exponent data

The rational Fuchsian classification fixes every normalized coefficient: unlike
Heun's four-singularity case, no accessory parameter remains. The finite triple
is the Papperitz operator, and the normalized triple `0,1,infinity` is Gauss's
equation. Sources: Kristensson, *Second Order Differential Equations*, Chapter 4,
§4.3, pp. 49–55; Olver, *Asymptotics and Special Functions*, Chapter 5,
Theorem 8.1, pp. 156–158.
-/

@[expose] public noncomputable section

open Complex Filter Set
open scoped Topology

namespace DLMF.Hypergeometric

/-- Finite regular singularities at zero and one with the Gauss indicial data and
a regular infinity give exactly the Gauss coefficients. The infinity product is
specified as an analytic germ, not by a totalized point evaluation of `q`.
Kristensson, Chapter 4, (4.3), pp. 49–50; Olver, Chapter 5, Theorem 8.1. -/
theorem coefficients_eq_gauss_of_regularSingular {a b c : ℂ} {p q : ℂ → ℂ}
    (hp : AnalyticOnNhd ℂ p ({0, 1} : Set ℂ)ᶜ)
    (hq : AnalyticOnNhd ℂ q ({0, 1} : Set ℂ)ᶜ)
    (hlocal : ∀ i : Fin 2, ∃ P Q : ℂ → ℂ,
      AnalyticAt ℂ P (![0, 1] i) ∧ AnalyticAt ℂ Q (![0, 1] i) ∧
      (fun z => (z - ![0, 1] i) * p z) =ᶠ[𝓝[≠] ![0, 1] i] P ∧
      (fun z => (z - ![0, 1] i) ^ 2 * q z) =ᶠ[𝓝[≠] ![0, 1] i] Q ∧
      P (![0, 1] i) = ![c, a + b + 1 - c] i ∧ Q (![0, 1] i) = 0)
    (hinfty : LinearODEAtMostRegularAtInfinity ![q, p])
    (hproduct : ∃ Q : ℂ → ℂ, AnalyticAt ℂ Q 0 ∧
      (fun t => q t⁻¹ / t ^ 2) =ᶠ[𝓝[≠] 0] Q ∧ Q 0 = a * b) :
    ∀ z : ℂ, z ∉ ({0, 1} : Set ℂ) →
      p z = (c - (a + b + 1) * z) / (z * (1 - z)) ∧
      q z = -(a * b) / (z * (1 - z)) := by
  sorry


end DLMF.Hypergeometric
