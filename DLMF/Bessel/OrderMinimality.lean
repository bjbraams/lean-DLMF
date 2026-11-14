/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.LargeOrder
public import DLMF.Bessel.SecondKind
public import DLMFMathlib.Analysis.SpecificLimits.SecondOrderRecurrence

/-!
# Minimal solutions and stable recurrence directions

Temme, *Special Functions* (1996), Chapter 13, §§13.3–13.4. Consecutive ratios,
relative growth and normalized backward approximation are distinguished from
large-argument asymptotics.
-/

@[expose] public noncomputable section
open Filter Asymptotics Complex
open scoped Topology Nat Real
namespace DLMF.Bessel

/-- The consecutive-order `J` ratio, Temme §13.3, Example 1, pp. 338–339,
synopsis TEM-13-04. -/
theorem tendsto_order_mul_besselJ_ratio {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun n : ℕ => (n : ℂ) * besselJ (n + 1) z / besselJ n z)
      atTop (𝓝 (z / 2)) := by
  sorry

/-- The consecutive-order `Y` ratio, Temme §13.3, Example 1, synopsis TEM-13-04. -/
theorem tendsto_besselY_order_ratio_div {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun n : ℕ => besselY (n + 1) z / besselY n z / n)
      atTop (𝓝 (2 / z)) := by
  sorry

/-- First-kind Bessel functions are minimal in the order recurrence,
Temme §13.3, Example 1, synopsis TEM-13-04. -/
theorem tendsto_besselJ_div_besselY_order {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun n : ℕ => besselJ n z / besselY n z) atTop (𝓝 0) := by
  sorry

/-- The consecutive-order `I` ratio, Temme §13.3, Example 1, synopsis TEM-13-04. -/
theorem tendsto_order_mul_besselI_ratio {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => (n : ℂ) * besselI (n + 1) x / besselI n x)
      atTop (𝓝 (x / 2 : ℂ)) := by
  sorry

/-- The consecutive-order `K` ratio, Temme §13.3, Example 1, synopsis TEM-13-04. -/
theorem tendsto_besselK_order_ratio_div {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => besselK (n + 1) x / besselK n x / n)
      atTop (𝓝 (2 / x : ℂ)) := by
  sorry

/-- The modified first kind is minimal against the signed modified second kind,
Temme §13.3, Example 1, synopsis TEM-13-04. -/
theorem tendsto_besselI_div_signed_besselK_order {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => besselI n x / ((-1 : ℂ) ^ n * besselK n x))
      atTop (𝓝 0) := by
  sorry

/-- The Bessel normalization makes Miller backward recursion converge,
Temme (13.14), synopsis TEM-13-11. -/
theorem tendsto_miller_besselI {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Tendsto (fun N : ℕ => Complex.SecondOrderRecurrence.millerApproximation
      (fun k => besselI k x) (fun k => (-1 : ℂ) ^ k * besselK k x)
      (fun k => if k = 0 then 1 else 2) (Complex.exp x) N n)
      atTop (𝓝 (besselI n x)) := by
  sorry

end DLMF.Bessel
