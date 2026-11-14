/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.ODE.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Weighted real Bessel envelopes

The first crossing of `J_nu+Y_nu` is the existing canonical `besselEnvCrit`.
The weight, modulus and unwrapped phase retain the near-origin normalization
needed for simple-pole error bounds. Source: Olver, *Asymptotics and Special
Functions*, Chapter 12, §1, pp. 435–438, and Lemma 4.1, pp. 443–444.
-/

@[expose] public noncomputable section

open Complex Filter Set
open scoped Real Topology Asymptotics

namespace DLMF.AsymptoticApproximations.Real.BesselEnvelope

/-- Olver's Bessel weight `E_nu`, balancing `J_nu` and `Y_nu` before their
first crossing and equal to one afterward. Olver, Chapter 12, §1, pp. 435–436. -/
def weight (ν x : ℝ) : ℝ :=
  if x ≤ besselEnvCrit ν then
    Real.sqrt (-(DLMF.Bessel.besselY ν x).re / (Complex.besselJ ν x).re)
  else 1

/-- The defining two branches of the Bessel weight. -/
theorem weight_def (ν x : ℝ) : weight ν x =
    if x ≤ besselEnvCrit ν then
      Real.sqrt (-(DLMF.Bessel.besselY ν x).re / (Complex.besselJ ν x).re) else 1 := rfl

/-- The Bessel weight is one after its first crossing. -/
theorem weight_of_gt (ν : ℝ) {x : ℝ} (hx : besselEnvCrit ν < x) : weight ν x = 1 := by
  simp [weight, hx.not_ge]

/-- The weighted Bessel modulus `M_nu`. Olver, Chapter 12, §1, p. 436. -/
def modulus (ν x : ℝ) : ℝ :=
  Real.sqrt ((weight ν x * (Complex.besselJ ν x).re) ^ 2 +
    ((DLMF.Bessel.besselY ν x).re / weight ν x) ^ 2)

/-- The defining sum of weighted Bessel squares. -/
theorem modulus_def (ν x : ℝ) : modulus ν x =
    Real.sqrt ((weight ν x * (Complex.besselJ ν x).re) ^ 2 +
      ((DLMF.Bessel.besselY ν x).re / weight ν x) ^ 2) := rfl

/-- The unwrapped weighted Bessel phase, constant `-pi/4` before the crossing.
The positive integral gives the normalized increasing phase after the crossing.
Olver, Chapter 12, §1, pp. 436–437. -/
def phase (ν x : ℝ) : ℝ :=
  if x ≤ besselEnvCrit ν then -Real.pi / 4 else
    -Real.pi / 4 + ∫ t in besselEnvCrit ν..x, 2 / (Real.pi * t * modulus ν t ^ 2)

/-- The defining normalized phase branches. -/
theorem phase_def (ν x : ℝ) : phase ν x =
    if x ≤ besselEnvCrit ν then -Real.pi / 4 else
      -Real.pi / 4 + ∫ t in besselEnvCrit ν..x, 2 / (Real.pi * t * modulus ν t ^ 2) := rfl

/-- The phase is constant up to the first crossing. -/
theorem phase_of_le (ν : ℝ) {x : ℝ} (hx : x ≤ besselEnvCrit ν) :
    phase ν x = -Real.pi / 4 := by
  simp [phase, hx]

/-- The transition is the smallest positive crossing, occurs before every positive
zero of either cylinder function, and has positive `J` and negative `Y` there.
Olver, Chapter 12, §1, pp. 435–436. -/
theorem transition_properties {ν : ℝ} (hν : 0 ≤ ν) :
    0 < besselEnvCrit ν ∧
    Complex.besselJ ν (besselEnvCrit ν) + DLMF.Bessel.besselY ν (besselEnvCrit ν) = 0 ∧
    0 < (Complex.besselJ ν (besselEnvCrit ν)).re ∧
    (DLMF.Bessel.besselY ν (besselEnvCrit ν)).re < 0 ∧
    (∀ x : ℝ, 0 < x → Complex.besselJ ν x + DLMF.Bessel.besselY ν x = 0 →
      besselEnvCrit ν ≤ x) ∧
    (∀ x : ℝ, 0 < x → DLMF.Bessel.besselY ν x = 0 → besselEnvCrit ν < x) ∧
    (∀ x : ℝ, 0 < x → Complex.besselJ ν x = 0 → besselEnvCrit ν < x) := by
  sorry

/-- The first crossing increases with order. Olver, Chapter 12, §1, p. 436. -/
theorem strictMonoOn_transition : StrictMonoOn besselEnvCrit (Ici 0) := by
  sorry

/-- Joint continuity in nonnegative order and positive argument.
Olver, Chapter 12, §1, pp. 436–437. -/
theorem continuousOn_weight_modulus :
    ContinuousOn (fun p : ℝ × ℝ => weight p.1 p.2) {p | 0 ≤ p.1 ∧ 0 < p.2} ∧
      ContinuousOn (fun p : ℝ × ℝ => modulus p.1 p.2) {p | 0 ≤ p.1 ∧ 0 < p.2} := by
  sorry

/-- The weight decreases with its positive argument and remains at least one.
Olver, Chapter 12, §1, pp. 436–437. -/
theorem weight_properties {ν : ℝ} (hν : 0 ≤ ν) :
    AntitoneOn (weight ν) (Ioi 0) ∧ ∀ x : ℝ, 0 < x → 1 ≤ weight ν x := by
  sorry

/-- Raising the nonnegative order by one increases the weight.
Olver, Chapter 12, Lemma 4.1, pp. 443–444. -/
theorem weight_le_succ {ν x : ℝ} (hν : 0 ≤ ν) (hx : 0 < x) :
    weight ν x ≤ weight (ν + 1) x := by
  sorry

/-- The weighted modulus is strictly positive throughout its real domain.
Olver, Chapter 12, §1, p. 436. -/
theorem modulus_pos {ν x : ℝ} (hν : 0 ≤ ν) (hx : 0 < x) : 0 < modulus ν x := by
  sorry

/-- The sine/cosine representation fixes the phase without a hidden integer
multiple of `2pi`. Olver, Chapter 12, §1, pp. 436–437. -/
theorem phase_representations {ν x : ℝ} (hν : 0 ≤ ν) (hx : 0 < x) :
    (Complex.besselJ ν x).re = modulus ν x / weight ν x * Real.cos (phase ν x) ∧
      (DLMF.Bessel.besselY ν x).re = modulus ν x * weight ν x * Real.sin (phase ν x) := by
  sorry

/-- The phase is continuous on the positive axis, and has the Wronskian derivative
after the crossing. Olver, Chapter 12, §1, pp. 436–437. -/
theorem phase_properties {ν : ℝ} (hν : 0 ≤ ν) :
    ContinuousOn (phase ν) (Ioi 0) ∧ ∀ x : ℝ, besselEnvCrit ν < x →
      deriv (phase ν) x = 2 / (Real.pi * x * modulus ν x ^ 2) := by
  sorry

/-- The phase has the standard large-argument normalization with an `O(1/x)` error.
Olver, Chapter 12, §1, p. 437. -/
theorem isBigO_phase_sub_linear {ν : ℝ} (hν : 0 ≤ ν) :
    (fun x : ℝ => phase ν x - (x - Real.pi * ν / 2 - Real.pi / 4)) =O[atTop]
      (fun x : ℝ => x⁻¹) := by
  sorry

/-- The weighted modulus agrees with the existing Chapter 2 envelope convention.
Olver, Chapter 12, §1, pp. 436–437; DLMF 2.8.33–2.8.34. -/
theorem modulus_envelope {ν x : ℝ} (hν : 0 ≤ ν) (hx : 0 < x) :
    modulus ν x / weight ν x = envelopeJ ν x ∧
      modulus ν x * weight ν x = envelopeY ν x := by
  sorry

end DLMF.AsymptoticApproximations.Real.BesselEnvelope
