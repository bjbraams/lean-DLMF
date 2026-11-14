/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Asymptotics.LargeParameter

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

/-- Upper-parameter Tricomi logarithmic growth, Temme §13.3, Example 7,
p. 341, synopsis TEM-13-07. -/
theorem Real.tendsto_log_norm_kummerU_upper_parameter {a c z : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hz : 0 < z) :
    Tendsto (fun n : ℕ => Real.log ‖Complex.Gamma (a + n) *
      kummerU (a + n) c z / Complex.Gamma a‖ / Real.sqrt n)
      atTop (𝓝 (-2 * Real.sqrt z)) := by
  sorry

/-- Upper-parameter Kummer logarithmic growth, Temme §13.3, Example 7,
p. 341, synopsis TEM-13-07. -/
theorem Real.tendsto_log_norm_kummerM_upper_parameter {a c z : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hz : 0 < z) :
    Tendsto (fun n : ℕ => Real.log ‖Complex.Gamma (a + n) *
      kummerM (a + n) c z / Complex.Gamma (a + n + 1 - c)‖ / Real.sqrt n)
      atTop (𝓝 (2 * Real.sqrt z)) := by
  sorry

/-- The upper-parameter Tricomi solution is minimal, Temme §13.3, Example 7,
synopsis TEM-13-07. -/
theorem Real.tendsto_kummerU_div_kummerM_upper_parameter {a c z : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hz : 0 < z) :
    Tendsto (fun n : ℕ =>
      (Complex.Gamma (a + n) * kummerU (a + n) c z / Complex.Gamma a) /
        (Complex.Gamma (a + n) * kummerM (a + n) c z /
          Complex.Gamma (a + n + 1 - c))) atTop (𝓝 0) := by
  sorry

/-- The normalized lower-parameter Kummer solution, Temme §13.3, Example 8,
p. 342, synopsis TEM-13-07. -/
theorem Real.isEquivalent_kummerM_lower_parameter {a c z : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hz : 0 < z) :
    (fun n : ℕ => Complex.Gamma (c + n - a) * kummerM a (c + n) z /
      Complex.Gamma (c + n)) ~[atTop] (fun n : ℕ => (n : ℂ) ^ (-(a : ℂ))) := by
  sorry

/-- The lower-parameter Tricomi dominant solution, including the factor `exp z`,
Temme §13.3, Example 8, synopsis TEM-13-07, corrected target TEM-E10. -/
theorem Real.isEquivalent_kummerU_lower_parameter {a c z : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hz : 0 < z) :
    (fun n : ℕ => kummerU a (c + n) z) ~[atTop]
      (fun n : ℕ => Complex.exp z * (z : ℂ) ^ (1 - c - n : ℂ) *
        Complex.Gamma (c + n - 1) / Complex.Gamma a) := by
  sorry

end DLMF.Confluent
