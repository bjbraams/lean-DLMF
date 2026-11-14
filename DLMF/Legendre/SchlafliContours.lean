/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Basic
public import DLMF.AlgebraicAnalytic.Complex.Basic
public import DLMFMathlib.Analysis.Complex.LogarithmicLift
public import Mathlib.Analysis.Complex.SqrtDeriv

/-!
# Schläfli contours for Legendre functions

Kristensson, *Second Order Differential Equations*, Theorems 6.1–6.2,
pp. 110–115, and Example 6.1, pp. 115–118. Contour powers use continuous
logarithmic lifts with initial normalizations. The figure-eight contour for `Q`
traverses its clockwise right lobe before its counterclockwise left lobe;
this specifies the upper-bank initial normalization without an ambiguous phase.
-/

@[expose] public section

open Complex Set MeasureTheory
open DLMF.AlgebraicAnalytic
open scoped Real Topology

noncomputable section

namespace DLMF.Legendre

/-- Kristensson, Theorem 6.1, p. 110: the first Schläfli contour for `P_ν`.
The curve encloses `1,z` in the branch domain cut at `(-∞,-1]`; the logarithms
of `t-1` and `t-z` continue from their principal values at a positive real base point. -/
theorem legendreP_schlafli_contour (ν : ℂ) {z : ℂ} (hz : z + 1 ∈ slitPlane)
    {γ L₁ Lz : ℝ → ℂ} {b : ℝ}
    (hγ : IsSimpleClosedContour γ 0 1) (hpositive : IsPositivelyOriented γ 0 1)
    (hinside₁ : (1 : ℂ) ∈ contourInterior γ 0 1)
    (hinsidez : z ∈ contourInterior γ 0 1)
    (hbranch : γ '' Icc 0 1 ∪ contourInterior γ 0 1 ⊆ {t : ℂ | t + 1 ∈ slitPlane})
    (hbase : γ 0 = (b : ℂ)) (hb : ‖z‖ + 2 < b)
    (hL₁ : IsLogarithmicLiftOn (fun t => γ t - 1) (Icc 0 1) L₁)
    (hLz : IsLogarithmicLiftOn (fun t => γ t - z) (Icc 0 1) Lz)
    (hL₁zero : L₁ 0 = log (γ 0 - 1)) (hLzzero : Lz 0 = log (γ 0 - z)) :
    legendreP ν z = (2 : ℂ) ^ (-ν) / (2 * Real.pi * I) *
      ∫ t : ℝ in 0..1, exp (ν * (L₁ t + log (γ t + 1)) - (ν + 1) * Lz t) *
        deriv γ t := by
  sorry

/-- Kristensson, Theorem 6.2, pp. 112–115: the figure-eight Schläfli integral
for Hobson's `Q_ν`, represented by `associatedQ ν 0`. The right lobe is traversed
clockwise first, the left lobe counterclockwise second, starting on the upper bank
of the focal cut. Analytic-domain conditions specify the correlated branches. -/
theorem associatedQ_zero_order_schlafli_contour (ν : ℂ)
    (hν : sin (Real.pi * ν) ≠ 0) {z : ℂ} (hz : z - 1 ∈ slitPlane)
    {γ L₁ Lminus₁ Lz : ℝ → ℂ} {b : ℝ}
    (hright : IsSimpleClosedContour γ 0 (1 / 2))
    (hleft : IsSimpleClosedContour γ (1 / 2) 1)
    (hright₁ : (1 : ℂ) ∈ contourInterior γ 0 (1 / 2))
    (hleft₁ : (-1 : ℂ) ∈ contourInterior γ (1 / 2) 1)
    (hrightneg : ∀ t ∈ contourInterior γ 0 (1 / 2),
      TauCeti.Contour.windingNumber γ 0 (1 / 2) t = -1)
    (hleftpos : IsPositivelyOriented γ (1 / 2) 1)
    (hrightbranch : γ '' Icc 0 (1 / 2) ∪ contourInterior γ 0 (1 / 2) ⊆
      {t : ℂ | t + 1 ∈ slitPlane ∧ z - t ∈ slitPlane})
    (hleftbranch : γ '' Icc (1 / 2) 1 ∪ contourInterior γ (1 / 2) 1 ⊆
      {t : ℂ | 1 - t ∈ slitPlane ∧ z - t ∈ slitPlane})
    (hbase : γ 0 = (b : ℂ)) (hb : b ∈ Ioo (-1) 1)
    (hL₁ : IsLogarithmicLiftOn (fun t => γ t - 1) (Icc 0 1) L₁)
    (hLminus₁ : IsLogarithmicLiftOn (fun t => γ t + 1) (Icc 0 1) Lminus₁)
    (hLz : IsLogarithmicLiftOn (fun t => z - γ t) (Icc 0 1) Lz)
    (hL₁zero : L₁ 0 = log (γ 0 - 1))
    (hLminus₁zero : Lminus₁ 0 = log (γ 0 + 1))
    (hLzzero : Lz 0 = log (z - γ 0)) :
    associatedQ ν 0 z = (2 : ℂ) ^ (-ν) / (4 * I * sin (Real.pi * ν)) *
      ∫ t : ℝ in 0..1, exp (ν * (L₁ t + Lminus₁ t) - (ν + 1) * Lz t) *
        deriv γ t := by
  sorry

/-- Kristensson, Theorem 6.2, p. 113: the collapsed Schläfli integral on the
principal Hobson branch, for `Re ν>-1`. The endpoint powers have positive real bases. -/
theorem associatedQ_zero_order_eq_intervalIntegral (ν : ℂ) (hν : -1 < ν.re)
    {z : ℂ} (hz : z - 1 ∈ slitPlane) :
    associatedQ ν 0 z = (2 : ℂ) ^ (-ν - 1) * ∫ t : ℝ in -1..1,
      (1 - (t : ℂ) ^ 2) ^ ν * (z - t) ^ (-ν - 1) := by
  sorry

/-- Kristensson, Example 6.1, (6.5), pp. 115–118: a finite/infinite real-integral
combination for Hobson's `Q_ν(z)`, with absolute convergence of its infinite tail. -/
theorem associatedQ_zero_order_eq_mixed_integrals {ν : ℂ} (hν : -1 < ν.re)
    {z : ℝ} (hz : 1 < z) :
    IntegrableOn (fun t : ℝ => exp (-(ν + 1 / 2) * t) /
      (Real.sqrt (z + Real.cosh t) : ℂ)) (Ioi 0) ∧
    associatedQ ν 0 z = (Real.sqrt 2 : ℂ)⁻¹ *
      ((∫ t : ℝ in 0..Real.pi, cos ((ν + 1 / 2) * t) /
        (Real.sqrt (z - Real.cos t) : ℂ)) - cos (Real.pi * ν) *
          ∫ t : ℝ in Ioi 0, exp (-(ν + 1 / 2) * t) /
            (Real.sqrt (z + Real.cosh t) : ℂ)) := by
  sorry

/-- The mixed finite/infinite representation continues to the whole principal
Hobson cut using correlated principal complex square roots. Both integrability
statements are explicit. Kristensson, Chapter 6, Example 6.1, (6.5), pp. 115–118. -/
theorem associatedQ_zero_order_eq_mixed_integrals_complex {ν : ℂ} (hν : -1 < ν.re)
    {z : ℂ} (hz : z - 1 ∈ slitPlane) :
    IntervalIntegrable (fun t : ℝ => cos ((ν + 1 / 2) * t) /
      sqrt (z - Real.cos t)) volume 0 Real.pi ∧
    IntegrableOn (fun t : ℝ => exp (-(ν + 1 / 2) * t) /
      sqrt (z + Real.cosh t)) (Ioi 0) ∧
    associatedQ ν 0 z = (Real.sqrt 2 : ℂ)⁻¹ *
      ((∫ t : ℝ in 0..Real.pi, cos ((ν + 1 / 2) * t) / sqrt (z - Real.cos t)) -
        cos (Real.pi * ν) *
          ∫ t : ℝ in Ioi 0, exp (-(ν + 1 / 2) * t) / sqrt (z + Real.cosh t)) := by
  sorry

end DLMF.Legendre
