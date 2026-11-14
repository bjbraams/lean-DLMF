/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.LogarithmicAsymptotics
public import DLMF.Bessel.ZeroAsymptotics
public import DLMFMathlib.Analysis.Asymptotics.AsymptoticInversion
public import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Complete McMahon expansions with effective formal coefficients

Olver, *Asymptotics and Special Functions*, Chapter 7, §6.5 and §7,
pp. 247–249, synopsis O-7.11. The formal phase is the zero-constant
primitive of `(P Q'-Q P')/(P²+Q²)`, hence `atan(Q/P)` as a formal germ.
Generic McMahon reversion then determines every zero correction coefficient.
Both enumerations are complete; Y indexing is continued from order one half
on the component `nu>-1/2`, where no positive zero disappears at the origin.
-/

@[expose] public noncomputable section

open Complex Filter Asymptotics PowerSeries
open scoped Real Topology

namespace DLMF.Bessel

/-- The even formal Hankel amplitude `P`, including its unit constant coefficient.
Olver, Chapter 7, §6.5, synopsis O-7.11. -/
def hankelCosineSeries (ν : ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk fun n => if n % 2 = 0 then (-1 : ℂ) ^ (n / 2) * largeArgumentCoefficient ν n
    else 0

/-- The odd formal Hankel amplitude `Q`.
Olver, Chapter 7, §6.5, synopsis O-7.11. -/
def hankelSineSeries (ν : ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk fun n => if n % 2 = 1 then
    (-1 : ℂ) ^ ((n - 1) / 2) * largeArgumentCoefficient ν n else 0

/-- The actual zero-constant arctangent phase coefficient algorithm, formed by a
formal derivative and primitive. No analytic sum of this generally divergent series
is used. Olver, Chapter 7, §6.5, synopsis O-7.11. -/
def besselZeroPhaseSeries (ν : ℂ) : ℂ⟦X⟧ :=
  let P := hankelCosineSeries ν
  let Q := hankelSineSeries ν
  PowerSeries.mk fun n => if n = 0 then 0 else
    PowerSeries.coeff (n - 1)
      ((P * PowerSeries.derivative Q - Q * PowerSeries.derivative P) * (P ^ 2 + Q ^ 2)⁻¹) /
      (n : ℂ)

/-- The complete correction series obtained by formal McMahon inversion of the actual
Bessel tangent equation. Olver, Chapter 7, §6.5, synopsis O-7.11. -/
def besselZeroCorrectionSeries (ν : ℂ) : ℂ⟦X⟧ := mcMahonSeries (besselZeroPhaseSeries ν)

/-- The even Hankel coefficient formula. -/
theorem hankelCosineSeries_def (ν : ℂ) : hankelCosineSeries ν =
    PowerSeries.mk (fun n => if n % 2 = 0 then
      (-1 : ℂ) ^ (n / 2) * largeArgumentCoefficient ν n else 0) := rfl

/-- The odd Hankel coefficient formula. -/
theorem hankelSineSeries_def (ν : ℂ) : hankelSineSeries ν =
    PowerSeries.mk (fun n => if n % 2 = 1 then
      (-1 : ℂ) ^ ((n - 1) / 2) * largeArgumentCoefficient ν n else 0) := rfl

/-- The explicit formal phase derivative and primitive. -/
theorem besselZeroPhaseSeries_def (ν : ℂ) : besselZeroPhaseSeries ν =
    let P := hankelCosineSeries ν
    let Q := hankelSineSeries ν
    PowerSeries.mk (fun n => if n = 0 then 0 else
      PowerSeries.coeff (n - 1)
        ((P * PowerSeries.derivative Q - Q * PowerSeries.derivative P) * (P ^ 2 + Q ^ 2)⁻¹) /
        (n : ℂ)) := rfl

/-- The defining complete reversion algorithm. -/
theorem besselZeroCorrectionSeries_def (ν : ℂ) :
    besselZeroCorrectionSeries ν = mcMahonSeries (besselZeroPhaseSeries ν) := rfl

/-- The first four correction coefficients recover the printed McMahon terms.
Olver, Chapter 7, §6.5, (6.03), pp. 247–248, synopsis O-7.11. -/
theorem coeff_besselZeroCorrectionSeries_le_three (ν : ℂ) :
    ![PowerSeries.coeff 0 (besselZeroCorrectionSeries ν),
      PowerSeries.coeff 1 (besselZeroCorrectionSeries ν),
      PowerSeries.coeff 2 (besselZeroCorrectionSeries ν),
      PowerSeries.coeff 3 (besselZeroCorrectionSeries ν)] =
      ![0, -(4 * ν ^ 2 - 1) / 8, 0,
        -4 * (4 * ν ^ 2 - 1) * (28 * ν ^ 2 - 31) / (3 * 8 ^ 3)] := by
  sorry

/-- The full all-orders J-zero expansion for its complete ordered positive enumeration.
Olver, Chapter 7, §6.5, pp. 247–248, synopsis O-7.11. -/
theorem Real.hasAsymptoticPowerSeries_besselJ_positive_zeros {ν : ℝ} (hν : -1 < ν)
    (j : ℕ → ℝ) (hjpos : ∀ n, 0 < j n) (hjmono : StrictMono j)
    (hjrange : ∀ x : ℝ, 0 < x → (besselJ ν x = 0 ↔ ∃ n, j n = x))
    (hjlim : Tendsto j atTop atTop) :
    let β := fun n : ℕ => ((n : ℝ) + 1 + ν / 2 - 1 / 4) * Real.pi
    HasAsymptoticPowerSeries atTop (fun n => (β n : ℂ)⁻¹)
      (besselZeroCorrectionSeries ν) (fun n => ((j n - β n : ℝ) : ℂ)) := by
  sorry

/-- The full all-orders Y-zero expansion with its source-continuous positive indexing.
The range `nu>-1/2` is the complete positive-zero component containing `nu=1/2`.
Olver, Chapter 7, §§6.5–7.3, pp. 247–249, synopsis O-7.11. -/
theorem Real.hasAsymptoticPowerSeries_besselY_positive_zeros {ν : ℝ} (hν : -1 / 2 < ν)
    (y : ℕ → ℝ) (hypos : ∀ n, 0 < y n) (hymono : StrictMono y)
    (hyrange : ∀ x : ℝ, 0 < x → (besselY ν x = 0 ↔ ∃ n, y n = x))
    (hylim : Tendsto y atTop atTop) :
    let β := fun n : ℕ => ((n : ℝ) + 1 + ν / 2 - 3 / 4) * Real.pi
    HasAsymptoticPowerSeries atTop (fun n => (β n : ℂ)⁻¹)
      (besselZeroCorrectionSeries ν) (fun n => ((y n - β n : ℝ) : ℂ)) := by
  sorry

end DLMF.Bessel
