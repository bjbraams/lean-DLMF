/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Associated

/-!
# Minimal solutions in Legendre degree and order recurrences

Temme, *Special Functions* (1996), §13.3, Examples 2–3, pp. 338–339.
Positive integral order is distinguished from a terminating integral degree.
-/

@[expose] public noncomputable section
open Filter Complex
open scoped Topology
namespace DLMF.Legendre

/-- The large-integral-order ratio for the first kind, Temme §13.3, Example 2,
synopsis TEM-13-05. Integral degrees are excluded because their tails terminate. -/
theorem tendsto_associatedP_order_ratio_div (ν : ℂ) (hν : ∀ n : ℤ, ν ≠ n)
    {z : ℝ} (hz : 1 < z) :
    Tendsto (fun m : ℕ => associatedP ν (m + 1) z / associatedP ν m z / m)
      atTop (𝓝 (-(z - 1) / Real.sqrt (z ^ 2 - 1) : ℂ)) := by
  sorry

/-- The dominant integral-order ratio for the second kind, Temme §13.3,
Example 2, synopsis TEM-13-05. -/
theorem tendsto_associatedQ_order_ratio_div (ν : ℂ) (hν : ∀ n : ℤ, ν ≠ n)
    {z : ℝ} (hz : 1 < z) :
    Tendsto (fun m : ℕ => associatedQ ν (m + 1) z / associatedQ ν m z / m)
      atTop (𝓝 (-(z + 1) / Real.sqrt (z ^ 2 - 1) : ℂ)) := by
  sorry

/-- The first kind is minimal in integral order for a nonintegral degree,
Temme §13.3, Example 2, synopsis TEM-13-05. -/
theorem tendsto_associatedP_div_associatedQ_order (ν : ℂ)
    (hν : ∀ n : ℤ, ν ≠ n) {z : ℝ} (hz : 1 < z) :
    Tendsto (fun m : ℕ => associatedP ν m z / associatedQ ν m z) atTop (𝓝 0) := by
  sorry

/-- The dominant consecutive-degree ratio, Temme §13.3, Example 3,
synopsis TEM-13-05, with arbitrary fixed complex degree shift and order. -/
theorem tendsto_associatedP_degree_ratio (ν μ : ℂ) {z : ℝ} (hz : 1 < z) :
    Tendsto (fun n : ℕ => associatedP (n + ν + 1) μ z / associatedP (n + ν) μ z)
      atTop (𝓝 (z + Real.sqrt (z ^ 2 - 1) : ℂ)) := by
  sorry

/-- The minimal consecutive-degree ratio, Temme §13.3, Example 3,
synopsis TEM-13-05. Possible initial exceptional degrees do not affect the limit. -/
theorem tendsto_associatedQ_degree_ratio (ν μ : ℂ) {z : ℝ} (hz : 1 < z) :
    Tendsto (fun n : ℕ => associatedQ (n + ν + 1) μ z / associatedQ (n + ν) μ z)
      atTop (𝓝 (z - Real.sqrt (z ^ 2 - 1) : ℂ)) := by
  sorry

/-- The second kind is minimal in degree outside the interval of oscillation,
Temme §13.3, Example 3, synopsis TEM-13-05. -/
theorem tendsto_associatedQ_div_associatedP_degree (ν μ : ℂ)
    {z : ℝ} (hz : 1 < z) :
    Tendsto (fun n : ℕ => associatedQ (n + ν) μ z / associatedP (n + ν) μ z)
      atTop (𝓝 0) := by
  sorry

end DLMF.Legendre
