/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Volterra function and its logarithmic expansion

Olver, *Asymptotics and Special Functions*, Chapter 8, §11,
pp. 316–320, synopsis O-8.15. The Gamma integral defines an auxiliary
special function of positive real argument. Its Laplace transform includes the
boundary parameter a=0; the pole at p=1 supplies the separate exponential term.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology
namespace DLMF.Gamma.Volterra

/-- The Volterra function `V(a,t)` in Olver, Chapter 8, §11, pp. 316–320.
The intended domain is `a≥0,t>0`; the reciprocal Gamma is totalized at zero. -/
def value (a t : ℝ) : ℝ := ∫ v in Ici a, t ^ (v - 1) / Real.Gamma v

/-- The defining integral of the Volterra function. -/
theorem value_def (a t : ℝ) :
    value a t = ∫ v in Ici a, t ^ (v - 1) / Real.Gamma v := rfl

/-- Absolute convergence of the defining Volterra integral. Olver §11. -/
theorem integrableOn_value {a t : ℝ} (ha : 0 ≤ a) (ht : 0 < t) :
    IntegrableOn (fun v : ℝ => t ^ (v - 1) / Real.Gamma v) (Ici a) := by
  sorry

/-- The Volterra Laplace transform converges absolutely for `p>1` and equals
`p^(-a)/log p`. Olver, Chapter 8, §11, pp. 316–320. -/
theorem integral_exp_mul_value {a p : ℝ} (ha : 0 ≤ a) (hp : 1 < p) :
    IntegrableOn (fun t => Real.exp (-p * t) * value a t) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), Real.exp (-p * t) * value a t) = p ^ (-a) / Real.log p := by
  sorry

/-- The all-orders logarithmic expansion after the exponential residue has been
removed. Olver, Chapter 8, §11, pp. 316–320. -/
theorem isBigO_sub_exp_add_sum {a : ℝ} (ha : 0 ≤ a) (N : ℕ) :
    (fun t : ℝ => value a t - Real.exp t + t ^ (a - 1) *
      ∑ s ∈ Finset.range N, (-1 : ℝ) ^ s *
        iteratedDeriv s (fun v : ℝ => (Real.Gamma v)⁻¹) a / (Real.log t) ^ (s + 1))
      =O[atTop] (fun t : ℝ => t ^ (a - 1) / (Real.log t) ^ (N + 1)) := by
  sorry

end DLMF.Gamma.Volterra
