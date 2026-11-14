/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.Basic.Logarithm
public import DLMF.QHypergeometric.Elementary
public import DLMF.QSeries.QExponential

/-!
# The unscaled q-logarithm

Duverney, *An Introduction to Hypergeometric Functions*, Chapter 10,
equations (10.30)–(10.32), defines the logarithmic derivative of the unscaled
little q-exponential. Here its convergent partial-fraction series is the definition.
The DLMF exponential `DLMF.QHypergeometric.qExp` is scaled by `1-q`.
-/

@[expose] public noncomputable section

open Complex Filter
open scoped Topology Real

namespace DLMF.QSeries

/-- Convergence away from the poles. Duverney (10.30), synopsis DU-10.08. -/
theorem summable_qLogarithm {q z : ℂ} (hq : ‖q‖ < 1)
    (hz : ∀ n : ℕ, 1 - q ^ n * z ≠ 0) :
    Summable (fun k : ℕ => q ^ k * z / (1 - q ^ k * z)) := by
  sorry

/-- The q-logarithm is the logarithmic derivative of the unscaled little exponential.
Duverney (10.30), synopsis DU-10.08. -/
theorem qLogarithm_eq_logarithmicDeriv {q z : ℂ} (hq : ‖q‖ < 1)
    (hz : ∀ n : ℕ, 1 - q ^ n * z ≠ 0) :
    qLogarithm q z = z * deriv (fun w => (qPochhammerInf w q)⁻¹) z /
      (qPochhammerInf z q)⁻¹ := by
  sorry

/-- The q-logarithm shift equation. Duverney (10.31), synopsis DU-10.08. -/
theorem qLogarithm_mul {q z : ℂ} (hq : ‖q‖ < 1)
    (hz : ∀ n : ℕ, 1 - q ^ n * z ≠ 0) :
    qLogarithm q (q * z) = qLogarithm q z - z / (1 - z) := by
  sorry

/-- The Lambert series expansion of the q-logarithm.
Duverney (10.32), synopsis DU-10.06 and DU-10.08. -/
theorem hasSum_qLogarithm {q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => z ^ (k + 1) / (1 - q ^ (k + 1))) (qLogarithm q z) := by
  sorry

/-- The classical limit of the q-logarithm.
Duverney (10.32), synopsis DU-10.08. -/
theorem tendsto_qLogarithm {z : ℂ} (hz : ‖z‖ < 1) :
    Tendsto (fun q : ℝ => (1 - (q : ℂ)) * qLogarithm q z)
      (𝓝[<] 1) (𝓝 (-log (1 - z))) := by
  sorry

end DLMF.QSeries
