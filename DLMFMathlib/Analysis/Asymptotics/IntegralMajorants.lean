/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Integral power majorants at infinity

Olver, *Asymptotics and Special Functions*, Chapter 1, §4.1, pp. 8–9,
synopsis O-1.04. Local Bochner integrability is retained independently of the tail bound.
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory Asymptotics
open scoped Topology

namespace Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Integrating a growing power majorant. Olver, Chapter 1, §4.1, synopsis O-1.04. -/
theorem IsBigO.intervalIntegral_rpow {f : ℝ → E} {a r : ℝ} (ha : 0 < a)
    (hf : ∀ b, a ≤ b → IntervalIntegrable f volume a b)
    (h : f =O[atTop] fun t : ℝ => t ^ r) (hr : -1 < r) :
    (fun x => ∫ t in a..x, f t) =O[atTop] fun x : ℝ => x ^ (r + 1) := by
  sorry

/-- Integrating a little-oh growing power majorant. Olver, Chapter 1, §4.1,
synopsis O-1.04. -/
theorem IsLittleO.intervalIntegral_rpow {f : ℝ → E} {a r : ℝ} (ha : 0 < a)
    (hf : ∀ b, a ≤ b → IntervalIntegrable f volume a b)
    (h : f =o[atTop] fun t : ℝ => t ^ r) (hr : -1 < r) :
    (fun x => ∫ t in a..x, f t) =o[atTop] fun x : ℝ => x ^ (r + 1) := by
  sorry

/-- The borderline inverse-linear majorant gives a logarithmic primitive bound.
Olver, Chapter 1, §4.1, synopsis O-1.04. -/
theorem IsBigO.intervalIntegral_log {f : ℝ → E} {a : ℝ} (ha : 0 < a)
    (hf : ∀ b, a ≤ b → IntervalIntegrable f volume a b)
    (h : f =O[atTop] fun t : ℝ => t⁻¹) :
    (fun x => ∫ t in a..x, f t) =O[atTop] Real.log := by
  sorry

/-- The little-oh borderline bound gives a little-oh logarithmic primitive.
Olver, Chapter 1, §4.1, synopsis O-1.04. -/
theorem IsLittleO.intervalIntegral_log {f : ℝ → E} {a : ℝ} (ha : 0 < a)
    (hf : ∀ b, a ≤ b → IntervalIntegrable f volume a b)
    (h : f =o[atTop] fun t : ℝ => t⁻¹) :
    (fun x => ∫ t in a..x, f t) =o[atTop] Real.log := by
  sorry

/-- An integrable power bound makes every positive-half-line tail integrable.
Olver, Chapter 1, §4.1, synopsis O-1.04. -/
theorem IsBigO.integrableOn_Ioi_of_rpow {f : ℝ → E} {a r : ℝ} (ha : 0 < a)
    (hf : ∀ b, a ≤ b → IntervalIntegrable f volume a b)
    (h : f =O[atTop] fun t : ℝ => t ^ r) (hr : r < -1) :
    IntegrableOn f (Ioi a) := by
  sorry

/-- Little-oh integrable power bounds pass to little-oh tail bounds.
Olver, Chapter 1, §4.1, synopsis O-1.04. -/
theorem IsLittleO.integral_Ioi_rpow {f : ℝ → E} {a r : ℝ} (ha : 0 < a)
    (hf : ∀ b, a ≤ b → IntervalIntegrable f volume a b)
    (h : f =o[atTop] fun t : ℝ => t ^ r) (hr : r < -1) :
    (fun x => ∫ t in Ioi x, f t) =o[atTop] fun x : ℝ => x ^ (r + 1) := by
  sorry

end Asymptotics
