/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.ODE.BesselEnvelopes
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Radial scattering with weighted Bessel error bounds

The origin normalization is a limit of the actual solution divided by the
recessive Bessel comparison function. The phase at infinity is fixed modulo
`2*pi` by a principal interval; the small-control bound selects its small branch.
Source: Olver, *Asymptotics and Special Functions*, Chapter 12,
Theorem 6.1 and §6.2, pp. 449–451.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Real Topology Asymptotics

namespace DLMF.AsymptoticApproximations.Real

/-- The weighted radial error control `G_nu(u,r)`.
Olver, Chapter 12, (6.02), p. 449. -/
def radialScatteringControl (ν u : ℝ) (g : ℝ → ℝ) (r : ℝ) : ℝ :=
  Real.pi / 2 * ∫ t in 0..r, t * BesselEnvelope.modulus ν (u * t) ^ 2 * |g t|

/-- The defining finite-radius weighted integral. -/
theorem radialScatteringControl_def (ν u : ℝ) (g : ℝ → ℝ) (r : ℝ) :
    radialScatteringControl ν u g r = Real.pi / 2 *
      ∫ t in 0..r, t * BesselEnvelope.modulus ν (u * t) ^ 2 * |g t| := rfl

/-- The total weighted radial control, under the stated integrability hypothesis.
Olver, Chapter 12, §6.2, p. 450. -/
def totalRadialScatteringControl (ν u : ℝ) (g : ℝ → ℝ) : ℝ :=
  Real.pi / 2 * ∫ t in Ioi (0 : ℝ), t * BesselEnvelope.modulus ν (u * t) ^ 2 * |g t|

/-- The defining infinite-radius control integral. -/
theorem totalRadialScatteringControl_def (ν u : ℝ) (g : ℝ → ℝ) :
    totalRadialScatteringControl ν u g = Real.pi / 2 *
      ∫ t in Ioi (0 : ℝ), t * BesselEnvelope.modulus ν (u * t) ^ 2 * |g t| := rfl

/-- The first Born phase integral, with the source's negative sign.
Olver, Chapter 12, (6.16), p. 451. -/
def bornPhaseShift (ν u : ℝ) (g : ℝ → ℝ) : ℝ :=
  -Real.pi / 2 * ∫ t in Ioi (0 : ℝ), t * (Complex.besselJ ν (u * t)).re ^ 2 * g t

/-- The defining first Born integral. -/
theorem bornPhaseShift_def (ν u : ℝ) (g : ℝ → ℝ) : bornPhaseShift ν u g =
    -Real.pi / 2 * ∫ t in Ioi (0 : ℝ), t * (Complex.besselJ ν (u * t)).re ^ 2 * g t := rfl

/-- The origin-normalized real radial solution. Olver, Chapter 12,
Theorem 6.1, pp. 449–450. -/
def IsRadialScatteringSolution (l u : ℝ) (g w : ℝ → ℝ) : Prop :=
  ContinuousOn w (Ici 0) ∧ w 0 = 0 ∧ ContDiffOn ℝ 2 w (Ioi 0) ∧
    (∀ r : ℝ, 0 < r → deriv (deriv w) r =
      (-u ^ 2 + l * (l + 1) / r ^ 2 + g r) * w r) ∧
    Tendsto (fun r => w r / (Real.sqrt r * (Complex.besselJ (l + 1 / 2) (u * r)).re))
      (𝓝[>] 0) (𝓝 1)

/-- The exact regularity, equation and recessive normalization. -/
theorem isRadialScatteringSolution_iff (l u : ℝ) (g w : ℝ → ℝ) :
    IsRadialScatteringSolution l u g w ↔
      ContinuousOn w (Ici 0) ∧ w 0 = 0 ∧ ContDiffOn ℝ 2 w (Ioi 0) ∧
        (∀ r : ℝ, 0 < r → deriv (deriv w) r =
          (-u ^ 2 + l * (l + 1) / r ^ 2 + g r) * w r) ∧
        Tendsto (fun r => w r / (Real.sqrt r * (Complex.besselJ (l + 1 / 2) (u * r)).re))
          (𝓝[>] 0) (𝓝 1) := Iff.rfl

/-- The singular-endpoint existence theorem and its exact normalized error.
Olver, Chapter 12, Theorem 6.1, (6.03)–(6.04), p. 449. -/
theorem exists_radialScatteringSolution {l u : ℝ} (hl : -1 / 2 ≤ l) (hu : 0 < u)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Ioi 0))
    (hweighted : ∀ r : ℝ, 0 < r → IntervalIntegrable
      (fun t => t * BesselEnvelope.modulus (l + 1 / 2) (u * t) ^ 2 * |g t|) volume 0 r) :
    ∃ w : ℝ → ℝ, IsRadialScatteringSolution l u g w ∧
      ∀ r : ℝ, 0 < r →
        |w r / Real.sqrt r - (Complex.besselJ (l + 1 / 2) (u * r)).re| ≤
          BesselEnvelope.modulus (l + 1 / 2) (u * r) /
            BesselEnvelope.weight (l + 1 / 2) (u * r) *
              (Real.exp (radialScatteringControl (l + 1 / 2) u g r) - 1) := by
  sorry

/-- A real integrable tail gives a nonzero limiting amplitude and a principal
phase shift; both function and derivative have their sinusoidal limits. The
small-control phase estimate includes the source's explicit linear bound.
Olver, Chapter 12, §6.2, (6.10)–(6.15), pp. 450–451. -/
theorem exists_radialScattering_phase {l u : ℝ} (hl : -1 / 2 ≤ l) (hu : 0 < u)
    {g w : ℝ → ℝ} (hg : ContinuousOn g (Ioi 0))
    (hsolution : IsRadialScatteringSolution l u g w)
    (hweighted : IntegrableOn
      (fun t => t * BesselEnvelope.modulus (l + 1 / 2) (u * t) ^ 2 * |g t|) (Ioi 0))
    (htail : IntegrableOn g (Ioi 1)) :
    ∃ amplitude δ : ℝ, 0 < amplitude ∧ δ ∈ Ioc (-Real.pi) Real.pi ∧
      Tendsto (fun r => w r - Real.sqrt (2 / (Real.pi * u)) * amplitude *
        Real.sin (u * r - l * Real.pi / 2 + δ)) atTop (𝓝 0) ∧
      Tendsto (fun r => deriv w r - Real.sqrt (2 * u / Real.pi) * amplitude *
        Real.cos (u * r - l * Real.pi / 2 + δ)) atTop (𝓝 0) ∧
      (Real.exp (totalRadialScatteringControl (l + 1 / 2) u g) - 1 ≤ 1 →
        2 * |δ| / Real.pi ≤ Real.exp (totalRadialScatteringControl (l + 1 / 2) u g) - 1) := by
  sorry

/-- Along any large-parameter family with vanishing total control, the first
Born integral has a quadratic-in-control phase error. The principal phase is
specified by the asymptotic normalization, not an arbitrary multiple of `2*pi`.
Olver, Chapter 12, (6.16)–(6.18), p. 451. -/
theorem isBigO_radialScattering_phase_sub_born
    {l : ℝ} (hl : -1 / 2 ≤ l) {g : ℝ → ℝ} (hg : ContinuousOn g (Ioi 0))
    (htail : IntegrableOn g (Ioi 1))
    (w : ℝ → ℝ → ℝ) (amplitude δ : ℝ → ℝ)
    (hsolution : ∀ u : ℝ, 0 < u → IsRadialScatteringSolution l u g (w u))
    (hweighted : ∀ u : ℝ, 0 < u → IntegrableOn
      (fun t => t * BesselEnvelope.modulus (l + 1 / 2) (u * t) ^ 2 * |g t|) (Ioi 0))
    (hphase : ∀ u : ℝ, 0 < u → 0 < amplitude u ∧ δ u ∈ Ioc (-Real.pi) Real.pi ∧
      Tendsto (fun r => w u r - Real.sqrt (2 / (Real.pi * u)) * amplitude u *
        Real.sin (u * r - l * Real.pi / 2 + δ u)) atTop (𝓝 0))
    (hsmall : Tendsto (fun u => totalRadialScatteringControl (l + 1 / 2) u g) atTop (𝓝 0)) :
    (fun u => δ u - bornPhaseShift (l + 1 / 2) u g) =O[atTop]
      (fun u => totalRadialScatteringControl (l + 1 / 2) u g ^ 2) := by
  sorry

end DLMF.AsymptoticApproximations.Real
