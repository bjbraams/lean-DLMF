/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Coulomb.Basic

/-!
# Minimal solutions and stable recurrence directions

Temme, *Special Functions* (1996), Chapter 13, §§13.3–13.4. Consecutive ratios,
relative growth and normalized backward approximation are distinguished from
large-argument asymptotics.
-/

@[expose] public noncomputable section
open Filter Asymptotics
open scoped Topology Nat Real
namespace DLMF.Confluent

/-- Consecutive-order ratio of regular Coulomb waves, Temme §13.3,
Example 4, pp. 339–340, synopsis TEM-13-04. -/
theorem Real.tendsto_order_mul_coulombF_ratio (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun n : ℕ => (n : ℝ) * coulombF (n + 1) η ρ / coulombF n η ρ)
      atTop (𝓝 (ρ / 2)) := by
  sorry

/-- Consecutive-order ratio of irregular Coulomb waves, Temme §13.3,
Example 4, synopsis TEM-13-04. -/
theorem Real.tendsto_coulombG_order_ratio_div (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun n : ℕ => coulombG (n + 1) η ρ / coulombG n η ρ / n)
      atTop (𝓝 (2 / ρ)) := by
  sorry

/-- Regular Coulomb waves form the minimal order solution, Temme §13.3,
Example 4, synopsis TEM-13-04. -/
theorem Real.tendsto_coulombF_div_coulombG_order (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun n : ℕ => coulombF n η ρ / coulombG n η ρ) atTop (𝓝 0) := by
  sorry

end DLMF.Confluent
