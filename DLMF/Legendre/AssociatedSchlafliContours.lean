/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.SchlafliContours

/-!
# Arbitrary-order Schläfli loops with their full infinite tails

Olver, *Asymptotics and Special Functions*, Chapter 5, Theorems 13.1–13.2,
pp. 174–175 and 177–178, synopsis O-5.20–O-5.21. An infinite based P-loop
is represented by a finite positively oriented simple loop and its two positive
real tails. Their difference includes the actual monodromy multiplier. The Q-loop
traverses the positive right lobe before the negative left lobe, as in Olver.
Gamma-pole values use limits of the complete normalized expression.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open DLMF.AlgebraicAnalytic
open scoped Real Topology

namespace DLMF.Legendre

/-- A finite middle part of the positive-infinity based Schläfli loop, with both
continued logarithms normalized at its positive base point.
Olver, Chapter 5, Theorem 13.1, synopsis O-5.20. -/
structure SchlafliPBasedLoop (z : ℂ) where
  curve : ℝ → ℂ
  base : ℝ
  simple : IsSimpleClosedContour curve 0 1
  positive : IsPositivelyOriented curve 0 1
  one_inside : (1 : ℂ) ∈ contourInterior curve 0 1
  argument_inside : z ∈ contourInterior curve 0 1
  branch : curve '' Icc 0 1 ∪ contourInterior curve 0 1 ⊆
    {t : ℂ | t + 1 ∈ slitPlane}
  curve_zero : curve 0 = (base : ℂ)
  base_large : ‖z‖ + 2 < base
  logarithmOne : ℝ → ℂ
  logarithmArgument : ℝ → ℂ
  liftOne : IsLogarithmicLiftOn (fun t => curve t - 1) (Icc 0 1) logarithmOne
  liftArgument : IsLogarithmicLiftOn (fun t => curve t - z) (Icc 0 1) logarithmArgument
  logarithmOne_zero : logarithmOne 0 = log (curve 0 - 1)
  logarithmArgument_zero : logarithmArgument 0 = log (curve 0 - z)

/-- The geometric and logarithmic data of the source P-loop exist throughout its cut.
Olver, Chapter 5, Theorem 13.1, pp. 174–175, synopsis O-5.20. -/
theorem nonempty_schlafliPBasedLoop {z : ℂ} (hz : z + 1 ∈ slitPlane) :
    Nonempty (SchlafliPBasedLoop z) := by
  sorry

/-- The first principal positive-ray integrand of the infinite P-loop. -/
def schlafliPFirstTail (ν μ z : ℂ) (t : ℝ) : ℂ :=
  exp (ν * (log ((t : ℂ) - 1) + log ((t : ℂ) + 1)) -
    (ν + μ + 1) * log ((t : ℂ) - z))

/-- The second principal positive-ray integrand of the infinite P-loop. -/
def schlafliPSecondTail (ν μ z : ℂ) (t : ℝ) : ℂ :=
  exp ((ν - μ) * log ((t : ℂ) - z) -
    (ν + 1) * (log ((t : ℂ) - 1) + log ((t : ℂ) + 1)))

/-- The complete first infinite based-loop integral, including both oriented real tails.
The return-tail branch has multiplier `exp(-2*pi*i*mu)`. -/
def schlafliPFirstLoopIntegral (ν μ : ℂ) {z : ℂ} (C : SchlafliPBasedLoop z) : ℂ :=
  (∫ t : ℝ in 0..1,
    exp (ν * (C.logarithmOne t + log (C.curve t + 1)) -
      (ν + μ + 1) * C.logarithmArgument t) * deriv C.curve t) +
    (exp (-2 * π * I * μ) - 1) * ∫ t : ℝ in Ioi C.base, schlafliPFirstTail ν μ z t

/-- The complete second infinite based-loop integral, with the same return-tail multiplier. -/
def schlafliPSecondLoopIntegral (ν μ : ℂ) {z : ℂ} (C : SchlafliPBasedLoop z) : ℂ :=
  (∫ t : ℝ in 0..1,
    exp ((ν - μ) * C.logarithmArgument t -
      (ν + 1) * (C.logarithmOne t + log (C.curve t + 1))) * deriv C.curve t) +
    (exp (-2 * π * I * μ) - 1) * ∫ t : ℝ in Ioi C.base, schlafliPSecondTail ν μ z t

/-- The whole first Gamma-normalized Schläfli expression before taking any pole limit.
Olver, Chapter 5, Theorem 13.1, first formula, synopsis O-5.20. -/
def schlafliPFirstExpression (ν μ : ℂ) {z : ℂ} (C : SchlafliPBasedLoop z) : ℂ :=
  exp (μ * π * I) * Gamma (-ν) / ((2 : ℂ) ^ (ν + 1) * π * I * Gamma (μ - ν)) *
    legendreBranchPower μ z * schlafliPFirstLoopIntegral ν μ C

/-- The whole second Gamma-normalized Schläfli expression before its pole limits.
Olver, Chapter 5, Theorem 13.1, second formula, synopsis O-5.20. -/
def schlafliPSecondExpression (ν μ : ℂ) {z : ℂ} (C : SchlafliPBasedLoop z) : ℂ :=
  (2 : ℂ) ^ ν * exp (μ * π * I) * Gamma (ν + 1) / (π * I * Gamma (ν + μ + 1)) *
    legendreBranchPower μ z * schlafliPSecondLoopIntegral ν μ C

/-- The explicit first ray integrand. -/
theorem schlafliPFirstTail_def (ν μ z : ℂ) (t : ℝ) : schlafliPFirstTail ν μ z t =
    exp (ν * (log ((t : ℂ) - 1) + log ((t : ℂ) + 1)) -
      (ν + μ + 1) * log ((t : ℂ) - z)) := rfl

/-- The explicit second ray integrand. -/
theorem schlafliPSecondTail_def (ν μ z : ℂ) (t : ℝ) : schlafliPSecondTail ν μ z t =
    exp ((ν - μ) * log ((t : ℂ) - z) -
      (ν + 1) * (log ((t : ℂ) - 1) + log ((t : ℂ) + 1))) := rfl

/-- The finite middle and two oriented tails of the first loop. -/
theorem schlafliPFirstLoopIntegral_def (ν μ : ℂ) {z : ℂ} (C : SchlafliPBasedLoop z) :
    schlafliPFirstLoopIntegral ν μ C =
      (∫ t : ℝ in 0..1,
        exp (ν * (C.logarithmOne t + log (C.curve t + 1)) -
          (ν + μ + 1) * C.logarithmArgument t) * deriv C.curve t) +
      (exp (-2 * π * I * μ) - 1) * ∫ t : ℝ in Ioi C.base, schlafliPFirstTail ν μ z t := rfl

/-- The finite middle and two oriented tails of the second loop. -/
theorem schlafliPSecondLoopIntegral_def (ν μ : ℂ) {z : ℂ} (C : SchlafliPBasedLoop z) :
    schlafliPSecondLoopIntegral ν μ C =
      (∫ t : ℝ in 0..1,
        exp ((ν - μ) * C.logarithmArgument t -
          (ν + 1) * (C.logarithmOne t + log (C.curve t + 1))) * deriv C.curve t) +
      (exp (-2 * π * I * μ) - 1) * ∫ t : ℝ in Ioi C.base, schlafliPSecondTail ν μ z t := rfl

/-- The first whole normalized expression. -/
theorem schlafliPFirstExpression_def (ν μ : ℂ) {z : ℂ} (C : SchlafliPBasedLoop z) :
    schlafliPFirstExpression ν μ C =
      exp (μ * π * I) * Gamma (-ν) / ((2 : ℂ) ^ (ν + 1) * π * I * Gamma (μ - ν)) *
        legendreBranchPower μ z * schlafliPFirstLoopIntegral ν μ C := rfl

/-- The second whole normalized expression. -/
theorem schlafliPSecondExpression_def (ν μ : ℂ) {z : ℂ} (C : SchlafliPBasedLoop z) :
    schlafliPSecondExpression ν μ C =
      (2 : ℂ) ^ ν * exp (μ * π * I) * Gamma (ν + 1) / (π * I * Gamma (ν + μ + 1)) *
        legendreBranchPower μ z * schlafliPSecondLoopIntegral ν μ C := rfl

/-- Absolute convergence of the first improper P-loop tail under its precise source
parameter inequality. Olver, Chapter 5, Theorem 13.1, synopsis O-5.20. -/
theorem integrableOn_schlafliPFirstTail {ν μ z : ℂ} (C : SchlafliPBasedLoop z)
    (hμ : ν.re < μ.re) : IntegrableOn (schlafliPFirstTail ν μ z) (Ioi C.base) := by
  sorry

/-- Absolute convergence of the second improper P-loop tail under its different source
inequality. Olver, Chapter 5, Theorem 13.1, synopsis O-5.20. -/
theorem integrableOn_schlafliPSecondTail {ν μ z : ℂ} (C : SchlafliPBasedLoop z)
    (hμ : -1 < ν.re + μ.re) : IntegrableOn (schlafliPSecondTail ν μ z) (Ioi C.base) := by
  sorry

/-- First arbitrary-order infinite Schläfli P-loop formula on its literal Gamma-regular
locus. The singular point `z=1` is treated by endpoint limits.
Olver, Chapter 5, Theorem 13.1, pp. 174–175, synopsis O-5.20. -/
theorem associatedP_eq_schlafliPFirstExpression {ν μ z : ℂ} (C : SchlafliPBasedLoop z)
    (hz : z ≠ 1) (hμ : ν.re < μ.re) (hν : ∀ n : ℕ, ν ≠ (n : ℂ)) :
    associatedP ν (-μ) z = schlafliPFirstExpression ν μ C := by
  sorry

/-- Second arbitrary-order infinite Schläfli P-loop formula.
Olver, Chapter 5, Theorem 13.1, pp. 174–175, synopsis O-5.20. -/
theorem associatedP_eq_schlafliPSecondExpression {ν μ z : ℂ} (C : SchlafliPBasedLoop z)
    (hz : z ≠ 1) (hμ : -1 < ν.re + μ.re) (hν : ∀ n : ℕ, ν ≠ -(n + 1 : ℂ)) :
    associatedP ν (-μ) z = schlafliPSecondExpression ν μ C := by
  sorry

/-- Gamma-pole cancellation is the limit of the entire first normalized expression.
Olver, Chapter 5, Theorem 13.1, synopsis O-5.20. -/
theorem tendsto_schlafliPFirstExpression {ν μ z : ℂ} (C : SchlafliPBasedLoop z)
    (hz : z ≠ 1) (hμ : ν.re < μ.re) :
    Tendsto (fun v => schlafliPFirstExpression v μ C)
      (𝓝[{v : ℂ | ∀ n : ℕ, v ≠ (n : ℂ)}] ν) (𝓝 (associatedP ν (-μ) z)) := by
  sorry

/-- Gamma-pole cancellation is the limit of the entire second normalized expression.
Olver, Chapter 5, Theorem 13.1, synopsis O-5.20. -/
theorem tendsto_schlafliPSecondExpression {ν μ z : ℂ} (C : SchlafliPBasedLoop z)
    (hz : z ≠ 1) (hμ : -1 < ν.re + μ.re) :
    Tendsto (fun v => schlafliPSecondExpression v μ C)
      (𝓝[{v : ℂ | ∀ n : ℕ, v ≠ -(n + 1 : ℂ)}] ν) (𝓝 (associatedP ν (-μ) z)) := by
  sorry

/-- The Olver Q-loop traverses a positive right lobe and then a negative left lobe.
The logarithms of `1-t`, `1+t`, and `z-t` start with their principal values at
an interior real base point. Olver, Theorem 13.2, synopsis O-5.21. -/
structure SchlafliQOppositeLobes (z : ℂ) where
  curve : ℝ → ℂ
  base : ℝ
  right_simple : IsSimpleClosedContour curve 0 (1 / 2)
  left_simple : IsSimpleClosedContour curve (1 / 2) 1
  one_inside : (1 : ℂ) ∈ contourInterior curve 0 (1 / 2)
  minus_one_inside : (-1 : ℂ) ∈ contourInterior curve (1 / 2) 1
  right_positive : IsPositivelyOriented curve 0 (1 / 2)
  left_negative : ∀ t ∈ contourInterior curve (1 / 2) 1,
    TauCeti.Contour.windingNumber curve (1 / 2) 1 t = -1
  right_branch : curve '' Icc 0 (1 / 2) ∪ contourInterior curve 0 (1 / 2) ⊆
    {t : ℂ | t + 1 ∈ slitPlane ∧ z - t ∈ slitPlane}
  left_branch : curve '' Icc (1 / 2) 1 ∪ contourInterior curve (1 / 2) 1 ⊆
    {t : ℂ | 1 - t ∈ slitPlane ∧ z - t ∈ slitPlane}
  curve_zero : curve 0 = (base : ℂ)
  base_mem : base ∈ Ioo (-1) 1
  logarithmRight : ℝ → ℂ
  logarithmLeft : ℝ → ℂ
  logarithmArgument : ℝ → ℂ
  liftRight : IsLogarithmicLiftOn (fun t => 1 - curve t) (Icc 0 1) logarithmRight
  liftLeft : IsLogarithmicLiftOn (fun t => curve t + 1) (Icc 0 1) logarithmLeft
  liftArgument : IsLogarithmicLiftOn (fun t => z - curve t) (Icc 0 1) logarithmArgument
  logarithmRight_zero : logarithmRight 0 = log (1 - curve 0)
  logarithmLeft_zero : logarithmLeft 0 = log (curve 0 + 1)
  logarithmArgument_zero : logarithmArgument 0 = log (z - curve 0)

/-- The source Q-loop geometry and lifted branches exist throughout the principal cut.
Olver, Chapter 5, Theorem 13.2, pp. 177–178, synopsis O-5.21. -/
theorem nonempty_schlafliQOppositeLobes {z : ℂ} (hz : z - 1 ∈ slitPlane) :
    Nonempty (SchlafliQOppositeLobes z) := by
  sorry

/-- The complete arbitrary-order normalized Olver Q-loop expression.
Olver, Chapter 5, Theorem 13.2, synopsis O-5.21. -/
def schlafliQExpression (ν μ : ℂ) {z : ℂ} (C : SchlafliQOppositeLobes z) : ℂ :=
  exp (-ν * π * I) * Gamma (-ν) / ((2 : ℂ) ^ (ν + 2) * π * I) *
    legendreBranchPower μ z * ∫ t : ℝ in 0..1,
      exp (ν * (C.logarithmRight t + C.logarithmLeft t) -
        (ν + μ + 1) * C.logarithmArgument t) * deriv C.curve t

/-- The complete Q-loop prefactor and continued integrand. -/
theorem schlafliQExpression_def (ν μ : ℂ) {z : ℂ} (C : SchlafliQOppositeLobes z) :
    schlafliQExpression ν μ C =
      exp (-ν * π * I) * Gamma (-ν) / ((2 : ℂ) ^ (ν + 2) * π * I) *
        legendreBranchPower μ z * ∫ t : ℝ in 0..1,
          exp (ν * (C.logarithmRight t + C.logarithmLeft t) -
            (ν + μ + 1) * C.logarithmArgument t) * deriv C.curve t := rfl

/-- The arbitrary-order Q-loop formula with Olver's orientation and normalization.
Only the nonnegative integer degree Gamma poles are excluded from the literal form.
Olver, Chapter 5, Theorem 13.2, pp. 177–178, synopsis O-5.21. -/
theorem olverQ_eq_schlafliQExpression {ν μ z : ℂ} (C : SchlafliQOppositeLobes z)
    (hz : z - 1 ∈ slitPlane) (hν : ∀ n : ℕ, ν ≠ (n : ℂ)) :
    olverQ ν μ z = schlafliQExpression ν μ C := by
  sorry

/-- The normalized whole Q-loop expression has the required degree-pole cancellations.
Olver, Chapter 5, Theorem 13.2, synopsis O-5.21. -/
theorem tendsto_schlafliQExpression {ν μ z : ℂ} (C : SchlafliQOppositeLobes z)
    (hz : z - 1 ∈ slitPlane) :
    Tendsto (fun v => schlafliQExpression v μ C)
      (𝓝[{v : ℂ | ∀ n : ℕ, v ≠ (n : ℂ)}] ν) (𝓝 (olverQ ν μ z)) := by
  sorry

end DLMF.Legendre
