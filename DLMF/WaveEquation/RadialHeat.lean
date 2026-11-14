/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.WaveEquation.Helmholtz
public import DLMF.Bessel.FourierBessel
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# The cooled cylinder as a Fourier–Bessel heat expansion

Temme, *Special Functions* (1996), §10.3.1, (10.3)–(10.9), pp. 268–270,
synopsis TEM-10-06. Initial data have finite radial `L²` norm. Smoothness and
termwise differentiation apply at strictly positive times.
-/

@[expose] public noncomputable section
open Complex MeasureTheory Filter DLMF.Bessel
open scoped Real Nat Topology ContDiff
namespace DLMF.WaveEquation

/-- The radial volume `r dr` on the unit cylinder, Temme (10.3)–(10.9), TEM-10-06. -/
def radialVolume : Measure ℝ :=
  (volume.restrict (Set.Icc (0 : ℝ) 1)).withDensity (fun r => ENNReal.ofReal r)

/-- The defining radial measure, Temme §10.3.1. -/
theorem radialVolume_def : radialVolume =
    (volume.restrict (Set.Icc (0 : ℝ) 1)).withDensity (fun r => ENNReal.ofReal r) := rfl

/-- The radial heat expansion with initial data `Φ`, Temme (10.3)–(10.9),
synopsis TEM-10-06. Positive zeros are indexed from zero. -/
def radialHeatSeries (j : ℕ → ℝ) (Φ : ℝ → ℂ) (r t : ℝ) : ℂ :=
  ∑' n : ℕ, fourierBesselCoefficient 0 j Φ n * heatMode (j n) r t

/-- The defining cylinder heat series, Temme (10.3)–(10.9). -/
theorem radialHeatSeries_def (j : ℕ → ℝ) (Φ : ℝ → ℂ) (r t : ℝ) :
    radialHeatSeries j Φ r t =
      ∑' n : ℕ, fourierBesselCoefficient 0 j Φ n * heatMode (j n) r t := rfl

/-- Absolute convergence at positive times, Temme §10.3.1, synopsis TEM-10-06. -/
theorem summable_radialHeatSeries (j : ℕ → ℝ) (hj : IsPositiveBesselZeroSequence 0 j)
    (Φ : ℝ → ℂ) (hΦ : MemLp Φ 2 radialVolume) (r : ℝ) {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => fourierBesselCoefficient 0 j Φ n * heatMode (j n) r t) := by
  sorry

/-- The radial cylinder heat equation, Temme (10.3)–(10.9), synopsis TEM-10-06. -/
theorem radialHeatSeries_pde (j : ℕ → ℝ) (hj : IsPositiveBesselZeroSequence 0 j)
    (Φ : ℝ → ℂ) (hΦ : MemLp Φ 2 radialVolume) {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    iteratedDeriv 2 (fun r => radialHeatSeries j Φ r t) r +
      ((1 / r : ℝ) : ℂ) * deriv (fun r => radialHeatSeries j Φ r t) r =
        deriv (fun t => radialHeatSeries j Φ r t) t := by
  sorry

/-- Every heat mode vanishes at the cylinder boundary, hence so does the sum,
Temme §10.3.1, synopsis TEM-10-06. -/
theorem radialHeatSeries_boundary (j : ℕ → ℝ) (hj : IsPositiveBesselZeroSequence 0 j)
    (Φ : ℝ → ℂ) (t : ℝ) : radialHeatSeries j Φ 1 t = 0 := by
  have hmode (n : ℕ) : heatMode (j n) 1 t = 0 := heatMode_boundary (hj.eq_zero n) t
  simp only [radialHeatSeries, hmode, mul_zero, tsum_zero]

/-- Smoothness at positive times, including the even radial extension through the axis,
Temme §10.3.1, synopsis TEM-10-06. -/
theorem contDiffOn_radialHeatSeries (j : ℕ → ℝ) (hj : IsPositiveBesselZeroSequence 0 j)
    (Φ : ℝ → ℂ) (hΦ : MemLp Φ 2 radialVolume) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => radialHeatSeries j Φ p.1 p.2) {p | 0 < p.2} := by
  sorry

/-- Axis regularity of the heat expansion, Temme §10.3.1, synopsis TEM-10-06. -/
theorem deriv_radialHeatSeries_zero (j : ℕ → ℝ) (hj : IsPositiveBesselZeroSequence 0 j)
    (Φ : ℝ → ℂ) (hΦ : MemLp Φ 2 radialVolume) {t : ℝ} (ht : 0 < t) :
    deriv (fun r => radialHeatSeries j Φ r t) 0 = 0 := by
  sorry

/-- Convergence of every fixed spatial/time derivative on compact positive-time sets,
Temme §10.3.1, synopsis TEM-10-06. -/
theorem tendstoLocallyUniformlyOn_radialHeatSeries_derivatives
    (j : ℕ → ℝ) (hj : IsPositiveBesselZeroSequence 0 j)
    (Φ : ℝ → ℂ) (hΦ : MemLp Φ 2 radialVolume) (k l : ℕ) :
    TendstoLocallyUniformlyOn
      (fun N : ℕ => fun p : ℝ × ℝ => iteratedDeriv k
        (fun r => iteratedDeriv l (fun t => ∑ n ∈ Finset.range N,
          fourierBesselCoefficient 0 j Φ n * heatMode (j n) r t) p.2) p.1)
      (fun p : ℝ × ℝ => iteratedDeriv k
        (fun r => iteratedDeriv l (fun t => radialHeatSeries j Φ r t) p.2) p.1)
      atTop {p | 0 < p.2} := by
  sorry

/-- Recovery of the initial condition in radial mean square,
Temme §10.3.1, synopsis TEM-10-06. -/
theorem tendsto_integral_norm_radialHeatSeries_sub_sq
    (j : ℕ → ℝ) (hj : IsPositiveBesselZeroSequence 0 j)
    (Φ : ℝ → ℂ) (hΦ : MemLp Φ 2 radialVolume) :
    Tendsto (fun t : ℝ => ∫ r : ℝ, ‖radialHeatSeries j Φ r t - Φ r‖ ^ 2 ∂radialVolume)
      (𝓝[>] 0) (𝓝 0) := by
  sorry

/-- Recovery at an interior continuity point of the initial temperature,
Temme §10.3.1, synopsis TEM-10-06. -/
theorem tendsto_radialHeatSeries_initial (j : ℕ → ℝ)
    (hj : IsPositiveBesselZeroSequence 0 j) (Φ : ℝ → ℂ) (hΦ : MemLp Φ 2 radialVolume)
    {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 1) (hcont : ContinuousAt Φ r) :
    Tendsto (radialHeatSeries j Φ r) (𝓝[>] 0) (𝓝 (Φ r)) := by
  sorry

/-- The constant-temperature coefficients, Temme (10.9), synopsis TEM-10-06. -/
theorem fourierBesselCoefficient_constant (j : ℕ → ℝ)
    (hj : IsPositiveBesselZeroSequence 0 j) (u₀ : ℂ) (n : ℕ) :
    fourierBesselCoefficient 0 j (fun _ => u₀) n =
      2 * u₀ / (j n * besselJ 1 (j n)) := by
  sorry

end DLMF.WaveEquation
