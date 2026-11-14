/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Basic
public import DLMF.AsymptoticApproximations.ODE.RealBesselExpansion
public import DLMF.AsymptoticApproximations.ODE.ComplexBesselExpansion

/-!
# Large-degree Legendre expansions with canonical simple-pole coefficients

The removable perturbation and every integration constant are explicit. Negative
coefficient order in the `P^{-m}` formula is paired with `I_m,I_(m-1)`, not
with `I_(-m),I_(1-m)`. The exterior `Q` normalization retains its exact
finite-truncation multiplier. Source: Olver, *Asymptotics and Special Functions*,
Chapter 12, §§12–13, pp. 463–474.
-/

@[expose] public noncomputable section

open Complex Set Filter ODE
open DLMF.AsymptoticApproximations.Real
open scoped Real Topology

namespace DLMF.Legendre.SimplePole

/-- The analytic perturbation at `zeta=0`, with its exact removable value.
Its other poles are `zeta=-(k*pi)^2`, `k>=1`.
Olver, Chapter 12, (12.07), p. 464. -/
def perturbation (m ζ : ℂ) : ℂ :=
  if ζ = 0 then -(m ^ 2 - 1 / 4) / 12 else
    (m ^ 2 - 1 / 4) / 4 * ((sinh (sqrt ζ))⁻¹ ^ 2 - ζ⁻¹)

/-- The defining removable simple-pole perturbation. -/
theorem perturbation_def (m ζ : ℂ) : perturbation m ζ =
    if ζ = 0 then -(m ^ 2 - 1 / 4) / 12 else
      (m ^ 2 - 1 / 4) / 4 * ((sinh (sqrt ζ))⁻¹ ^ 2 - ζ⁻¹) := rfl

/-- The canonical coefficient normalization is
`A_(s+1)(0)=2*m*B_s(0)`. Substitution of negative `m` retains that sign.
Olver, Chapter 12, (12.10)–(12.12), p. 465. -/
def IsCoefficientSequence (m : ℂ) (A B : ℕ → ℂ → ℂ) (D : Set ℂ) : Prop :=
  IsSimplePoleCoefficientSequence (perturbation m) m A B D ∧
    ∀ s, A (s + 1) 0 = 2 * m * B s 0

/-- The recurrence and the exact integration constants. -/
theorem isCoefficientSequence_iff (m : ℂ) (A B : ℕ → ℂ → ℂ) (D : Set ℂ) :
    IsCoefficientSequence m A B D ↔
      IsSimplePoleCoefficientSequence (perturbation m) m A B D ∧
        ∀ s, A (s + 1) 0 = 2 * m * B s 0 := Iff.rfl

/-- On every simply connected continuation domain containing zero and avoiding
the nonzero `pi*i` action poles, the canonical coefficients exist analytically.
Olver, Chapter 12, (12.11)–(12.12) and §13, pp. 465, 469–474. -/
theorem exists_coefficientSequence {D : Set ℂ} (hD : IsOpen D)
    (hsc : IsSimplyConnected D) (hzero : 0 ∈ D)
    (hpoles : ∀ k : ℕ, 0 < k → -((k : ℂ) * Real.pi) ^ 2 ∉ D) (m : ℂ) :
    AnalyticOnNhd ℂ (perturbation m) D ∧
      ∃ A B : ℕ → ℂ → ℂ, IsCoefficientSequence m A B D ∧
        ∀ s, AnalyticOnNhd ℂ (A s) D ∧ AnalyticOnNhd ℂ (B s) D := by
  sorry

/-- The actual exterior `P` compound approximation, using the signed coefficients
at `-m` and the consecutive orders `m,m-1`. Olver, Chapter 12,
(12.16), p. 466. -/
def approximationP (A B : ℕ → ℂ → ℂ) (m u ξ : ℝ) (n : ℕ) : ℂ :=
  DLMF.Bessel.besselI m (u * ξ) * ∑ s ∈ Finset.range (n + 1), A s (ξ ^ 2) / (u : ℂ) ^ (2 * s) +
    (ξ / u : ℝ) * DLMF.Bessel.besselI (m - 1) (u * ξ) *
      ∑ s ∈ Finset.range n, B s (ξ ^ 2) / (u : ℂ) ^ (2 * s)

/-- The defining normalized exterior `P` approximation. -/
theorem approximationP_def (A B : ℕ → ℂ → ℂ) (m u ξ : ℝ) (n : ℕ) :
    approximationP A B m u ξ n =
      DLMF.Bessel.besselI m (u * ξ) *
          ∑ s ∈ Finset.range (n + 1), A s (ξ ^ 2) / (u : ℂ) ^ (2 * s) +
        (ξ / u : ℝ) * DLMF.Bessel.besselI (m - 1) (u * ξ) *
          ∑ s ∈ Finset.range n, B s (ξ ^ 2) / (u : ℂ) ^ (2 * s) := rfl

/-- The actual exterior `Q` compound approximation. Olver, Chapter 12,
(12.13), p. 465. -/
def approximationQ (A B : ℕ → ℂ → ℂ) (m u ξ : ℝ) (n : ℕ) : ℂ :=
  DLMF.Bessel.besselK m (u * ξ) * ∑ s ∈ Finset.range (n + 1), A s (ξ ^ 2) / (u : ℂ) ^ (2 * s) -
    (ξ / u : ℝ) * DLMF.Bessel.besselK (m + 1) (u * ξ) *
      ∑ s ∈ Finset.range n, B s (ξ ^ 2) / (u : ℂ) ^ (2 * s)

/-- The defining normalized exterior `Q` approximation. -/
theorem approximationQ_def (A B : ℕ → ℂ → ℂ) (m u ξ : ℝ) (n : ℕ) :
    approximationQ A B m u ξ n =
      DLMF.Bessel.besselK m (u * ξ) *
          ∑ s ∈ Finset.range (n + 1), A s (ξ ^ 2) / (u : ℂ) ^ (2 * s) -
        (ξ / u : ℝ) * DLMF.Bessel.besselK (m + 1) (u * ξ) *
          ∑ s ∈ Finset.range n, B s (ξ ^ 2) / (u : ℂ) ^ (2 * s) := rfl

/-- Exact exterior identities and all four function/derivative variation bounds.
The `Q` identity is cleared of its possibly vanishing finite-truncation multiplier;
when its displayed bound is below one, division is valid. Olver,
Chapter 12, (12.13)–(12.17), pp. 465–466. -/
theorem exists_exterior_expansion_errors
    {D : Set ℂ} (hD : IsOpen D) (hsc : IsSimplyConnected D)
    (hpositive : ∀ x : ℝ, 0 ≤ x → (x : ℂ) ∈ D)
    {m u : ℝ} (hm : 0 ≤ m) (hu : 0 < u)
    {Aplus Bplus Aminus Bminus : ℕ → ℂ → ℂ}
    (hplus : IsCoefficientSequence m Aplus Bplus D)
    (hminus : IsCoefficientSequence (-m) Aminus Bminus D) (n : ℕ) :
    ∃ (δ : ℂ) (ηP ηQ : ℝ → ℂ), ContDiffOn ℝ 1 ηP (Ioi 0) ∧
      ContDiffOn ℝ 1 ηQ (Ioi 0) ∧
      (let V := fun s => (eVariationOn
        (fun ξ : ℝ => (ξ : ℂ) * Bplus s (ξ ^ 2)) (Ioi 0)).toReal
       let c := BesselComparison.modifiedConstant m
       ‖δ‖ ≤ c * Real.exp (c * V 0 / u) * V n / u ^ (2 * n + 1)) ∧
      ∀ ξ : ℝ, 0 < ξ →
        let pref := Real.sqrt (ξ / Real.sinh ξ)
        let c := BesselComparison.modifiedConstant m
        let left := fun s => (eVariationOn
          (fun t : ℝ => (t : ℂ) * Bminus s (t ^ 2)) (Icc 0 ξ)).toReal
        let right := fun s => (eVariationOn
          (fun t : ℝ => (t : ℂ) * Bplus s (t ^ 2)) (Ici ξ)).toReal
        let I := (DLMF.Bessel.besselI m (u * ξ)).re
        let K := (DLMF.Bessel.besselK m (u * ξ)).re
        let Knext := (DLMF.Bessel.besselK (m + 1) (u * ξ)).re
        associatedP (u - 1 / 2) (-m) (Real.cosh ξ) =
          (u ^ (-m) * pref : ℝ) * (approximationP Aminus Bminus m u ξ n + ηP ξ) ∧
        (1 + δ) * associatedQ (u - 1 / 2) m (Real.cosh ξ) =
          exp (m * Real.pi * Complex.I) * (u ^ m * pref : ℝ) *
            (approximationQ Aplus Bplus m u ξ n + ηQ ξ) ∧
        ‖ηP ξ‖ ≤ c * I * Real.exp (c * left 0 / u) * left n / u ^ (2 * n + 1) ∧
        ‖ηQ ξ‖ ≤ c * K * Real.exp (c * right 0 / u) * right n / u ^ (2 * n + 1) ∧
        ‖deriv ηP ξ‖ ≤ m / ξ * ‖ηP ξ‖ +
          2 * c * Knext / K * I * Real.exp (c * left 0 / u) * left n / u ^ (2 * n) ∧
        ‖deriv ηQ ξ‖ ≤ m / ξ * ‖ηQ ξ‖ +
          2 * c * Knext * Real.exp (c * right 0 / u) * right n / u ^ (2 * n) := by
  sorry

/-- The full Ferrers `P^{-m}` expansion and its exact weighted `J` error,
uniformly up to the regular singular endpoint but away from the other pole.
Olver, Chapter 12, (12.18)–(12.19), p. 467. -/
theorem exists_ferrersP_expansion_error
    {D : Set ℂ} (hD : IsOpen D) (hsc : IsSimplyConnected D)
    (hinterval : ∀ x : ℝ, -(Real.pi ^ 2) < x → x ≤ 0 → (x : ℂ) ∈ D)
    {m u : ℝ} (hm : 0 ≤ m) (hu : 0 < u)
    {Aminus Bminus : ℕ → ℂ → ℂ}
    (hminus : IsCoefficientSequence (-m) Aminus Bminus D) (n : ℕ) :
    ∃ η : ℝ → ℂ, ContDiffOn ℝ 1 η (Ioo 0 Real.pi) ∧
      ∀ θ : ℝ, 0 < θ → θ < Real.pi →
        let V := fun s => (eVariationOn
          (fun t : ℝ => (t : ℂ) * Bminus s (-(t ^ 2))) (Icc 0 θ)).toReal
        ferrersP (u - 1 / 2) (-m) (Real.cos θ) =
          (u ^ (-m) * Real.sqrt (θ / Real.sin θ) : ℝ) *
            (besselJ m (u * θ) *
              ∑ s ∈ Finset.range (n + 1), Aminus s (-(θ ^ 2)) / (u : ℂ) ^ (2 * s) +
            (θ / u : ℝ) * besselJ (m - 1) (u * θ) *
              ∑ s ∈ Finset.range n, Bminus s (-(θ ^ 2)) / (u : ℂ) ^ (2 * s) + η θ) ∧
        ‖η θ‖ ≤ BesselEnvelope.modulus m (u * θ) / BesselEnvelope.weight m (u * θ) *
          BesselComparison.oscillatoryErrorConstant 0 m *
          Real.exp (BesselComparison.oscillatoryConstant m * V 0 / u) *
            V n / u ^ (2 * n + 1) := by
  sorry

/-- The canonical coefficient variations are bounded uniformly on each bounded
signed-order interval, on the full positive ray and each negative interval
separated from the next action pole. This supplies the uniform-in-order constants
in all the exact expansion errors above. Olver, Chapter12 §§12–13, pp. 463–474. -/
theorem exists_uniform_coefficient_variation_bound
    {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (hεpi : ε < Real.pi)
    (A B : ℝ → ℕ → ℂ → ℂ)
    (hcoeff : ∀ m ∈ Icc (-M) M, IsCoefficientSequence m (A m) (B m)
      {ζ : ℂ | -(Real.pi ^ 2) < ζ.re}) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m ∈ Icc (-M) M,
      BoundedVariationOn (fun x : ℝ => (Real.sqrt |x| : ℂ) * B m n x)
        (Ici (-((Real.pi - ε) ^ 2))) ∧
      (eVariationOn (fun x : ℝ => (Real.sqrt |x| : ℂ) * B m n x)
        (Ici (-((Real.pi - ε) ^ 2)))).toReal ≤ C := by
  sorry

/-- The actual principal Legendre functions pull back to the normal action
ODE, on the principal `cosh` chart. Analytic continuation of this identity along
paths avoiding the nonzero `pi*i` poles gives the comparison equation used in
§13. The generic complex simple-pole theorem supplies its progressive-path errors.
Olver, Chapter12 (13.01)–(13.04), pp. 469–470. -/
theorem principal_cosh_normal_equation {u m ξ : ℂ}
    (hξ : 0 < ξ.re) (hξim : |ξ.im| < Real.pi)
    (hregular : DLMF.Legendre.LegendreQRegular (u - 1 / 2) m) :
    let P := fun t : ℂ => (sinh t) ^ (1 / 2 : ℂ) * associatedP (u - 1 / 2) (-m) (cosh t)
    let Q := fun t : ℂ => (sinh t) ^ (1 / 2 : ℂ) * associatedQ (u - 1 / 2) m (cosh t)
    deriv (deriv P) ξ = (u ^ 2 + (m ^ 2 - 1 / 4) / sinh ξ ^ 2) * P ξ ∧
      deriv (deriv Q) ξ = (u ^ 2 + (m ^ 2 - 1 / 4) / sinh ξ ^ 2) * Q ξ := by
  sorry

end DLMF.Legendre.SimplePole
