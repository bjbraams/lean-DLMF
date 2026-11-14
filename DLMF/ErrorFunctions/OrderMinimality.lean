/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ErrorFunctions.Repeated

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

/-- Equal characteristic moduli do not prevent minimality: the signed reflected
repeated Gaussian tail is dominant, Temme §13.3, Example 6, synopsis TEM-13-06. -/
theorem Real.tendsto_iteratedErfc_div_reflected_order {z : ℝ} (hz : 0 < z) :
    Tendsto (fun n : ℕ => iteratedErfc n z / ((-1 : ℂ) ^ n * iteratedErfc n (-z)))
      atTop (𝓝 0) := by
  sorry

/-- The precise logarithmic separation of repeated Gaussian tails,
Temme §13.3, Example 6, synopsis TEM-13-06. -/
theorem Real.tendsto_log_norm_iteratedErfc_div_reflected_order {z : ℝ} (hz : 0 < z) :
    Tendsto (fun n : ℕ => Real.log ‖iteratedErfc n z / iteratedErfc n (-z)‖ /
      Real.sqrt n) atTop (𝓝 (-2 * z * Real.sqrt 2)) := by
  sorry

/-- The common factorially normalized growth of repeated Gaussian tails,
Temme §13.3, Example 6, synopsis TEM-13-06. -/
theorem Real.limsup_iteratedErfc_factorial_order (z : ℝ) :
    Filter.limsup (fun n : ℕ => (‖iteratedErfc n z‖ * Real.sqrt n.factorial) ^
      ((n : ℝ)⁻¹)) atTop = (Real.sqrt 2)⁻¹ := by
  sorry

end DLMF.Confluent
