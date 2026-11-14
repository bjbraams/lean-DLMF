/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.ODE.BesselEnvelopes
public import DLMFMathlib.Analysis.ODE.SimplePoleCoefficients
public import Mathlib.Analysis.BoundedVariation

/-!
# Real simple-pole compound expansions with explicit Bessel bounds

The comparison functions have the Chapter12 scale `u*sqrt(abs(zeta))`.
All constants are actual suprema of canonical Bessel functions; no numerical
constant or undefined coefficient family occurs in the error bounds.
Source: Olver, *Asymptotics and Special Functions*, Chapter 12,
Theorems 3.1 and 4.1, pp. 441–445, and §5, pp. 447–448.
-/

@[expose] public noncomputable section

open Complex ODE Set Filter
open scoped Real Topology

namespace DLMF.AsymptoticApproximations.Real.BesselComparison

/-- The positive-variable comparison pair and its companion, choosing `I` for
index zero and `K` for index one. Olver, Chapter 12, (3.02)–(3.03), p. 441. -/
def positivePair (k : Fin 2) (ν u x : ℝ) : ℂ × ℂ :=
  if k = 0 then
    (Real.sqrt x * DLMF.Bessel.besselI ν (u * Real.sqrt x),
      (x / u : ℝ) * DLMF.Bessel.besselI (ν + 1) (u * Real.sqrt x))
  else
    (Real.sqrt x * DLMF.Bessel.besselK ν (u * Real.sqrt x),
      -(x / u : ℝ) * DLMF.Bessel.besselK (ν + 1) (u * Real.sqrt x))

/-- The defining positive-variable pair. -/
theorem positivePair_def (k : Fin 2) (ν u x : ℝ) : positivePair k ν u x =
    if k = 0 then
      (Real.sqrt x * DLMF.Bessel.besselI ν (u * Real.sqrt x),
        (x / u : ℝ) * DLMF.Bessel.besselI (ν + 1) (u * Real.sqrt x))
    else
      (Real.sqrt x * DLMF.Bessel.besselK ν (u * Real.sqrt x),
        -(x / u : ℝ) * DLMF.Bessel.besselK (ν + 1) (u * Real.sqrt x)) := rfl

/-- The negative-variable comparison pair, choosing `J` or `Y`.
Olver, Chapter 12, (4.09)–(4.10), pp. 444–445. -/
def negativePair (k : Fin 2) (ν u x : ℝ) : ℂ × ℂ :=
  let C := if k = 0 then Complex.besselJ else DLMF.Bessel.besselY
  (Real.sqrt |x| * C ν (u * Real.sqrt |x|),
    -(|x| / u : ℝ) * C (ν + 1) (u * Real.sqrt |x|))

/-- The defining negative-variable pair and its source sign. -/
theorem negativePair_def (k : Fin 2) (ν u x : ℝ) : negativePair k ν u x =
    let C := if k = 0 then Complex.besselJ else DLMF.Bessel.besselY
    (Real.sqrt |x| * C ν (u * Real.sqrt |x|),
      -(|x| / u : ℝ) * C (ν + 1) (u * Real.sqrt |x|)) := rfl

/-- The modified-Bessel kernel constant `lambda_1(nu)`.
Olver, Chapter 12, (3.01), pp. 440–441. -/
def modifiedConstant (ν : ℝ) : ℝ :=
  sSup ((fun x : ℝ => 2 * x * (DLMF.Bessel.besselI ν x).re *
    (DLMF.Bessel.besselK ν x).re) '' Ioi 0)

/-- The defining supremum of the positive Bessel product. -/
theorem modifiedConstant_def (ν : ℝ) : modifiedConstant ν =
    sSup ((fun x : ℝ => 2 * x * (DLMF.Bessel.besselI ν x).re *
      (DLMF.Bessel.besselK ν x).re) '' Ioi 0) := rfl

/-- The oscillatory kernel constant `lambda_2(nu)`.
Olver, Chapter 12, (4.06), p. 444. -/
def oscillatoryConstant (ν : ℝ) : ℝ :=
  sSup ((fun x : ℝ => Real.pi * x * BesselEnvelope.modulus ν x ^ 2) '' Ioi 0)

/-- The defining supremum of the oscillatory kernel majorant. -/
theorem oscillatoryConstant_def (ν : ℝ) : oscillatoryConstant ν =
    sSup ((fun x : ℝ => Real.pi * x * BesselEnvelope.modulus ν x ^ 2) '' Ioi 0) := rfl

/-- The `J` or `Y` error constant `lambda_3` or `lambda_4`.
Olver, Chapter 12, (4.07)–(4.08), p. 444. -/
def oscillatoryErrorConstant (k : Fin 2) (ν : ℝ) : ℝ :=
  sSup ((fun x : ℝ => Real.pi * x * BesselEnvelope.modulus ν x *
    if k = 0 then ‖Complex.besselJ ν x‖ * BesselEnvelope.weight ν x
    else ‖DLMF.Bessel.besselY ν x‖ / BesselEnvelope.weight ν x) '' Ioi 0)

/-- The defining supremum of either oscillatory error constant. -/
theorem oscillatoryErrorConstant_def (k : Fin 2) (ν : ℝ) :
    oscillatoryErrorConstant k ν =
      sSup ((fun x : ℝ => Real.pi * x * BesselEnvelope.modulus ν x *
        if k = 0 then ‖Complex.besselJ ν x‖ * BesselEnvelope.weight ν x
        else ‖DLMF.Bessel.besselY ν x‖ / BesselEnvelope.weight ν x) '' Ioi 0) := rfl

/-- The kernel and error suprema are finite, positive and continuous in the
nonnegative order. `lambda_1` is at least one. Olver, Chapter 12,
§3.1 and Lemma 4.1, pp. 440–444. -/
theorem constants_properties :
    ContinuousOn modifiedConstant (Ici 0) ∧
      ContinuousOn oscillatoryConstant (Ici 0) ∧
      (∀ k, ContinuousOn (oscillatoryErrorConstant k) (Ici 0)) ∧
      ∀ ν : ℝ, 0 ≤ ν → 1 ≤ modifiedConstant ν ∧ 0 < oscillatoryConstant ν ∧
        (∀ x : ℝ, 0 < x →
          2 * x * (DLMF.Bessel.besselI ν x).re * (DLMF.Bessel.besselK ν x).re ≤
            modifiedConstant ν) ∧
        (∀ x : ℝ, 0 < x → Real.pi * x * BesselEnvelope.modulus ν x ^ 2 ≤
          oscillatoryConstant ν) ∧ ∀ k, 0 < oscillatoryErrorConstant k ν := by
  sorry

/-- The exact ordinary square-root Bessel Green kernel in the negative
simple-pole variable; its Wronskian is `-1/pi`.
Olver, Chapter 12, §4, pp. 444–445. -/
def ordinaryGreenKernel (ν u x t : ℝ) : ℂ :=
  -Real.pi * ((negativePair 0 ν u t).1 * (negativePair 1 ν u x).1 -
    (negativePair 1 ν u t).1 * (negativePair 0 ν u x).1)

/-- The defining ordinary Bessel Green kernel. -/
theorem ordinaryGreenKernel_def (ν u x t : ℝ) : ordinaryGreenKernel ν u x t =
    -Real.pi * ((negativePair 0 ν u t).1 * (negativePair 1 ν u x).1 -
      (negativePair 1 ν u t).1 * (negativePair 0 ν u x).1) := rfl

/-- The explicit source function-error majorant on the negative interval.
The source reference is zero for `J` and the left endpoint for `Y`. -/
def negativeErrorMajorant (B : ℕ → ℝ → ℂ) (α : EReal)
    (k : Fin 2) (ν u : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  let V := fun s => (eVariationOn (fun t : ℝ => (Real.sqrt |t| : ℂ) * B s t)
    (if k = 0 then Icc x 0 else {t : ℝ | α < (t : EReal) ∧ t ≤ x})).toReal
  let E := if k = 0 then (BesselEnvelope.weight ν (u * Real.sqrt |x|))⁻¹
    else BesselEnvelope.weight ν (u * Real.sqrt |x|)
  Real.sqrt |x| * BesselEnvelope.modulus ν (u * Real.sqrt |x|) * E *
    oscillatoryErrorConstant k ν * Real.exp (oscillatoryConstant ν * V 0 / u) *
      V n / u ^ (2 * n + 1)

/-- The defining weighted function-error majorant. -/
theorem negativeErrorMajorant_def (B : ℕ → ℝ → ℂ) (α : EReal)
    (k : Fin 2) (ν u : ℝ) (n : ℕ) (x : ℝ) : negativeErrorMajorant B α k ν u n x =
    let V := fun s => (eVariationOn (fun t : ℝ => (Real.sqrt |t| : ℂ) * B s t)
      (if k = 0 then Icc x 0 else {t : ℝ | α < (t : EReal) ∧ t ≤ x})).toReal
    let E := if k = 0 then (BesselEnvelope.weight ν (u * Real.sqrt |x|))⁻¹
      else BesselEnvelope.weight ν (u * Real.sqrt |x|)
    Real.sqrt |x| * BesselEnvelope.modulus ν (u * Real.sqrt |x|) * E *
      oscillatoryErrorConstant k ν * Real.exp (oscillatoryConstant ν * V 0 / u) *
        V n / u ^ (2 * n + 1) := rfl

/-- A completely explicit derivative majorant, using the differentiated known
Green kernel and the already specified function bound. No unknown error occurs
inside this integral. Olver, Chapter 12, §4 and Chapter6 §10. -/
def negativeDerivativeMajorant (ψ : ℝ → ℂ) (B : ℕ → ℝ → ℂ)
    (α : EReal) (k : Fin 2) (ν u : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∫ t in (if k = 0 then Ioo x 0 else {t : ℝ | α < (t : EReal) ∧ t < x}),
    ‖deriv (fun z => ordinaryGreenKernel ν u z t) x‖ *
      (‖ψ t / t‖ * negativeErrorMajorant B α k ν u n t +
        ‖if k = 0 then Complex.besselJ ν (u * Real.sqrt |t|)
          else DLMF.Bessel.besselY ν (u * Real.sqrt |t|)‖ *
          ‖deriv (fun z : ℝ => (Real.sqrt |z| : ℂ) * B n z) t‖ / u ^ (2 * n))

/-- The defining derivative-kernel integral majorant. -/
theorem negativeDerivativeMajorant_def (ψ : ℝ → ℂ) (B : ℕ → ℝ → ℂ)
    (α : EReal) (k : Fin 2) (ν u : ℝ) (n : ℕ) (x : ℝ) :
    negativeDerivativeMajorant ψ B α k ν u n x =
      ∫ t in (if k = 0 then Ioo x 0 else {t : ℝ | α < (t : EReal) ∧ t < x}),
        ‖deriv (fun z => ordinaryGreenKernel ν u z t) x‖ *
          (‖ψ t / t‖ * negativeErrorMajorant B α k ν u n t +
            ‖if k = 0 then Complex.besselJ ν (u * Real.sqrt |t|)
              else DLMF.Bessel.besselY ν (u * Real.sqrt |t|)‖ *
              ‖deriv (fun z : ℝ => (Real.sqrt |z| : ℂ) * B n z) t‖ / u ^ (2 * n)) := rfl

end DLMF.AsymptoticApproximations.Real.BesselComparison

namespace DLMF.AsymptoticApproximations.Real

/-- Full positive-variable compound expansions with both exact derivative
bounds. Infinite right endpoints are allowed when the weighted coefficient
variations converge. Olver, Chapter 12, Theorem 3.1, (3.02)–(3.07), p. 441. -/
theorem exists_positive_bessel_compound_expansion
    {D : Set ℝ} (hD : IsOpen D) (hconvex : Convex ℝ D) (hzero : 0 ∈ D)
    {β : EReal} (hβ : 0 < β) (hinterval : {x : ℝ | 0 ≤ x ∧ (x : EReal) < β} ⊆ D)
    {ψ : ℝ → ℂ} {A B : ℕ → ℝ → ℂ} {ν u : ℝ} (hν : 0 ≤ ν) (hu : 0 < u)
    (hcoeff : IsSimplePoleCoefficientSequence ψ ν A B D) (n : ℕ)
    (hvar : ∀ s ∈ ({0, n} : Set ℕ),
      BoundedVariationOn (fun x : ℝ => (Real.sqrt x : ℂ) * B s x)
        {x : ℝ | 0 < x ∧ (x : EReal) < β}) :
    ∃ ε : Fin 2 → ℝ → ℂ,
      (∀ k, ContDiffOn ℝ ⊤ (ε k) {x : ℝ | 0 < x ∧ (x : EReal) < β}) ∧
      (∀ (k : Fin 2) (x : ℝ), 0 < x → (x : EReal) < β →
        let P := fun t => (BesselComparison.positivePair k ν u t).1
        let Q := fun t => (BesselComparison.positivePair k ν u t).2
        let W := fun t => simplePolePartialSum A B P Q u n t + ε k t
        deriv (deriv W) x =
          (u ^ 2 / (4 * x) + (ν ^ 2 - 1) / (4 * x ^ 2) + ψ x / x) * W x) ∧
      ∀ x : ℝ, 0 < x → (x : EReal) < β →
        let F := fun s t => (Real.sqrt t : ℂ) * B s t
        let left := fun s => (eVariationOn (F s) (Icc 0 x)).toReal
        let right := fun s => (eVariationOn (F s)
          {t : ℝ | x ≤ t ∧ (t : EReal) < β}).toReal
        let c := BesselComparison.modifiedConstant ν
        let I := (DLMF.Bessel.besselI ν (u * Real.sqrt x)).re
        let K := (DLMF.Bessel.besselK ν (u * Real.sqrt x)).re
        let Knext := (DLMF.Bessel.besselK (ν + 1) (u * Real.sqrt x)).re
        ‖ε 0 x‖ ≤ c * Real.sqrt x * I * Real.exp (c * left 0 / u) *
          left n / u ^ (2 * n + 1) ∧
        ‖ε 1 x‖ ≤ c * Real.sqrt x * K * Real.exp (c * right 0 / u) *
          right n / u ^ (2 * n + 1) ∧
        ‖deriv (ε 0) x - ((ν + 1) / (2 * x) : ℝ) * ε 0 x‖ ≤
          c * (Knext / K) * I * Real.exp (c * left 0 / u) * left n / u ^ (2 * n) ∧
        ‖deriv (ε 1) x - ((ν + 1) / (2 * x) : ℝ) * ε 1 x‖ ≤
          c * Knext * Real.exp (c * right 0 / u) * right n / u ^ (2 * n) := by
  sorry

/-- Full negative-variable compound expansions with the explicit order-dependent
weighted modulus bounds for `J` and `Y`. Olver, Chapter 12, Theorem 4.1,
(4.09)–(4.12), pp. 444–445. -/
theorem exists_negative_bessel_compound_expansion
    {D : Set ℝ} (hD : IsOpen D) (hconvex : Convex ℝ D) (hzero : 0 ∈ D)
    {α : EReal} (hα : α < 0) (hinterval : {x : ℝ | α < (x : EReal) ∧ x ≤ 0} ⊆ D)
    {ψ : ℝ → ℂ} {A B : ℕ → ℝ → ℂ} {ν u : ℝ} (hν : 0 ≤ ν) (hu : 0 < u)
    (hcoeff : IsSimplePoleCoefficientSequence ψ ν A B D) (n : ℕ)
    (hvar : ∀ s ∈ ({0, n} : Set ℕ),
      BoundedVariationOn (fun x : ℝ => (Real.sqrt |x| : ℂ) * B s x)
        {x : ℝ | α < (x : EReal) ∧ x < 0}) :
    ∃ ε : Fin 2 → ℝ → ℂ,
      (∀ k, ContDiffOn ℝ ⊤ (ε k) {x : ℝ | α < (x : EReal) ∧ x < 0}) ∧
      (∀ (k : Fin 2) (x : ℝ), α < (x : EReal) → x < 0 →
        let P := fun t => (BesselComparison.negativePair k ν u t).1
        let Q := fun t => (BesselComparison.negativePair k ν u t).2
        let W := fun t => simplePolePartialSum A B P Q u n t + ε k t
        deriv (deriv W) x =
          (u ^ 2 / (4 * x) + (ν ^ 2 - 1) / (4 * x ^ 2) + ψ x / x) * W x) ∧
      ∀ x : ℝ, α < (x : EReal) → x < 0 →
        let F := fun s t => (Real.sqrt |t| : ℂ) * B s t
        let left := fun s => (eVariationOn (F s)
          {t : ℝ | α < (t : EReal) ∧ t ≤ x}).toReal
        let right := fun s => (eVariationOn (F s) (Icc x 0)).toReal
        let E := BesselEnvelope.weight ν (u * Real.sqrt |x|)
        let M := BesselEnvelope.modulus ν (u * Real.sqrt |x|)
        ‖ε 0 x‖ ≤ Real.sqrt |x| * M / E * BesselComparison.oscillatoryErrorConstant 0 ν *
          Real.exp (BesselComparison.oscillatoryConstant ν * right 0 / u) *
            right n / u ^ (2 * n + 1) ∧
        ‖ε 1 x‖ ≤ Real.sqrt |x| * M * E * BesselComparison.oscillatoryErrorConstant 1 ν *
          Real.exp (BesselComparison.oscillatoryConstant ν * left 0 / u) *
            left n / u ^ (2 * n + 1) ∧
        ∀ k : Fin 2, ‖deriv (ε k) x‖ ≤
          BesselComparison.negativeDerivativeMajorant ψ B α k ν u n x := by
  sorry

end DLMF.AsymptoticApproximations.Real
