/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.UniformCoordinates
public import DLMF.Legendre.IntegralRepresentations

/-!
# Legendre uniform large-degree and large-order approximations

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Legendre

open DLMF.Bessel DLMF.Confluent

/-- ferrersP large order uniform. -/
@[dlmf 14.15.E1]
theorem ferrersP_large_order_uniform (ν : ℂ) (J : ℕ) :
    (fun p : ℝ × ℝ => ((1+p.2)/(1-p.2):ℂ)^((p.1:ℂ)/2)*ferrersP ν (-p.1) p.2-∑ j ∈ Finset.range J, poch (ν+1) j*poch (-ν) j/((j.factorial:ℂ)*Gamma (j+1+p.1))*((1-p.2)/2:ℂ)^j) =O[comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | p.2 ∈ Ioo (-1:ℝ) 1}] (fun p : ℝ × ℝ => 1/Gamma (J+1+p.1)) := by
  sorry

/-- associatedP large order uniform. -/
@[dlmf 14.15.E2]
theorem associatedP_large_order_uniform {ν : ℝ} (hν : -1/2 ≤ ν) :
    (fun p : ℝ × ℝ => associatedP ν (-p.1) p.2/(1/Gamma (p.1+1)*(2*p.1*legendreUCoordinate p.2/π:ℂ)^(1/2:ℂ)*besselK (ν+1/2) (p.1*legendreUCoordinate p.2))-1) =O[comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 1 < p.2}] (fun p : ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

/-- olverQ large order uniform. -/
@[dlmf 14.15.E3]
theorem olverQ_large_order_uniform {ν : ℝ} (hν : -1/2 ≤ ν) :
    (fun p : ℝ × ℝ => olverQ ν p.1 p.2/((p.1:ℂ)^(-(ν:ℂ)-1/2)*(π*legendreUCoordinate p.2/2:ℂ)^(1/2:ℂ)*besselI (ν+1/2) (p.1*legendreUCoordinate p.2))-1) =O[comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 1 < p.2}] (fun p : ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

/-- legendreOrderPrefactor. -/
def legendreOrderPrefactor (ν μ x : ℝ) : ℂ :=
  let α:=legendreOrderAlpha ν μ; 1/Gamma (μ+1)*(1-α^2:ℂ)^(-(μ:ℂ)/2)*((1-α)/(1+α):ℂ)^((ν:ℂ)/2+1/4)*(α^2*x^2+1-α^2:ℂ)^(-1/4:ℂ)*exp (-μ*legendreOrderRho α x)

/-- ferrersP two large parameters. -/
@[dlmf 14.15.E4]
theorem ferrersP_two_large_parameters {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (fun p : ℝ × ℝ × ℝ => ferrersP p.2.1 (-p.1) p.2.2/legendreOrderPrefactor p.2.1 p.1 p.2.2-1) =O[legendreUniformFilter {p : ℝ × ℝ × ℝ | p.2.2 ∈ Ioo (-1:ℝ) 1 ∧ 0 ≤ p.2.1+1/2 ∧ p.2.1+1/2 ≤ (1-δ)*p.1}] (fun p : ℝ × ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

/-- associatedP two large order uniform. -/
@[dlmf 14.15.E8]
theorem associatedP_two_large_order_uniform {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (fun p : ℝ × ℝ × ℝ => let μ:=p.1; let ν:=p.2.1; let x:=p.2.2; let α:=legendreOrderAlpha ν μ; let η:=legendreOrderEta α x; associatedP ν (-μ) x/((2*μ/π:ℂ)^(1/2:ℂ)/Gamma (μ+1)*((1-α)/(1+α):ℂ)^((ν:ℂ)/2+1/4)*(1-α^2:ℂ)^(-(μ:ℂ)/2)*((α^2+η^2)/(α^2*(x^2-1)+1):ℂ)^(1/4:ℂ)*besselK (ν+1/2) (μ*η))-1) =O[legendreUniformFilter {p : ℝ × ℝ × ℝ | 1 < p.2.2 ∧ 0 ≤ p.2.1+1/2 ∧ p.2.1+1/2 ≤ (1-δ)*p.1}] (fun p : ℝ × ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

/-- olverQ two large order uniform. -/
@[dlmf 14.15.E9]
theorem olverQ_two_large_order_uniform {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (fun p : ℝ × ℝ × ℝ => let μ:=p.1; let ν:=p.2.1; let x:=p.2.2; let α:=legendreOrderAlpha ν μ; let η:=legendreOrderEta α x; olverQ ν μ x/((π/2:ℂ)^(1/2:ℂ)*(Real.exp 1/μ:ℂ)^(ν+1/2:ℂ)*((1-α)/(1+α):ℂ)^((μ:ℂ)/2)*(1-α^2:ℂ)^(-(ν:ℂ)/2-1/4)*((α^2+η^2)/(α^2*(x^2-1)+1):ℂ)^(1/4:ℂ)*besselI (ν+1/2) (μ*η))-1) =O[legendreUniformFilter {p : ℝ × ℝ × ℝ | 1 < p.2.2 ∧ 0 ≤ p.2.1+1/2 ∧ p.2.1+1/2 ≤ (1-δ)*p.1}] (fun p : ℝ × ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

/-- ferrersP large degree uniform. -/
@[dlmf 14.15.E11]
theorem ferrersP_large_degree_uniform {μ : ℝ} (hμ : 0 ≤ μ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun p : ℝ × ℝ => ferrersP p.1 (-μ) (Real.cos p.2)/((p.1:ℂ)^(-(μ:ℂ))*(p.2/Real.sin p.2:ℂ)^(1/2:ℂ))-besselJ μ ((p.1+1/2)*p.2)) =O[comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ π-δ}] (fun p : ℝ × ℝ => legendreBesselEnvelope false μ ((p.1+1/2)*p.2)/p.1) := by
  sorry

/-- ferrersQ large degree uniform. -/
@[dlmf 14.15.E12]
theorem ferrersQ_large_degree_uniform {μ : ℝ} (hμ : 0 ≤ μ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun p : ℝ × ℝ => ferrersQ p.1 (-μ) (Real.cos p.2)/(-π/2*(p.1:ℂ)^(-(μ:ℂ))*(p.2/Real.sin p.2:ℂ)^(1/2:ℂ))-besselY μ ((p.1+1/2)*p.2)) =O[comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ π-δ}] (fun p : ℝ × ℝ => legendreBesselEnvelope true μ ((p.1+1/2)*p.2)/p.1) := by
  sorry

/-- associatedP large degree uniform. -/
@[dlmf 14.15.E13]
theorem associatedP_large_degree_uniform {μ : ℝ} (hμ : 0 ≤ μ) :
    (fun p : ℝ × ℝ => let ν:=p.1; let ξ:=p.2; associatedP ν (-μ) (Real.cosh ξ)/((ν:ℂ)^(-(μ:ℂ))*(ξ/Real.sinh ξ:ℂ)^(1/2:ℂ)*besselI μ ((ν+1/2)*ξ))-1) =O[comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 0 < p.2}] (fun p : ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

/-- olverQ large degree uniform. -/
@[dlmf 14.15.E14]
theorem olverQ_large_degree_uniform {μ : ℝ} (hμ : 0 ≤ μ) :
    (fun p : ℝ × ℝ => let ν:=p.1; let ξ:=p.2; olverQ ν μ (Real.cosh ξ)/((ν:ℂ)^(μ:ℂ)/Gamma (ν+μ+1)*(ξ/Real.sinh ξ:ℂ)^(1/2:ℂ)*besselK μ ((ν+1/2)*ξ))-1) =O[comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 0 < p.2}] (fun p : ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

/-- ferrersP two large degree uniform. -/
@[dlmf 14.15.E15]
theorem ferrersP_two_large_degree_uniform {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (fun p : ℝ × ℝ × ℝ => let ν:=p.1; let μ:=p.2.1; let x:=p.2.2; let α:=legendreDegreeAlpha ν μ; ferrersP ν (-μ) x/(legendreDegreeBeta ν μ*legendreDegreeAmplitude α x)-besselJ μ ((ν+1/2)*Real.sqrt (legendreDegreeY α x))) =O[legendreUniformFilter {p : ℝ × ℝ × ℝ | p.2.2 ∈ Ico 0 1 ∧ 0 ≤ p.2.1 ∧ p.2.1 ≤ (1-δ)*(p.1+1/2)}] (fun p : ℝ × ℝ × ℝ => legendreBesselEnvelope false p.2.1 ((p.1+1/2)*Real.sqrt (legendreDegreeY (legendreDegreeAlpha p.1 p.2.1) p.2.2))/p.1) := by
  sorry

/-- ferrersQ two large degree uniform. -/
@[dlmf 14.15.E16]
theorem ferrersQ_two_large_degree_uniform {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (fun p : ℝ × ℝ × ℝ => let ν:=p.1; let μ:=p.2.1; let x:=p.2.2; let α:=legendreDegreeAlpha ν μ; ferrersQ ν (-μ) x/(-π/2*legendreDegreeBeta ν μ*legendreDegreeAmplitude α x)-besselY μ ((ν+1/2)*Real.sqrt (legendreDegreeY α x))) =O[legendreUniformFilter {p : ℝ × ℝ × ℝ | p.2.2 ∈ Ico 0 1 ∧ 0 ≤ p.2.1 ∧ p.2.1 ≤ (1-δ)*(p.1+1/2)}] (fun p : ℝ × ℝ × ℝ => legendreBesselEnvelope true p.2.1 ((p.1+1/2)*Real.sqrt (legendreDegreeY (legendreDegreeAlpha p.1 p.2.1) p.2.2))/p.1) := by
  sorry

/-- associatedP two large degree modified. -/
@[dlmf 14.15.E17]
theorem associatedP_two_large_degree_modified {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (fun p : ℝ × ℝ × ℝ => let ν:=p.1; let μ:=p.2.1; let x:=p.2.2; let α:=legendreDegreeAlpha ν μ; let y:=legendreDegreeY α x; associatedP ν (-μ) x/(legendreDegreeBeta ν μ*((α^2-y)/(x^2-1+α^2):ℂ)^(1/4:ℂ)*besselI μ ((ν+1/2)*Real.sqrt |y|))-1) =O[legendreUniformFilter {p : ℝ × ℝ × ℝ | 1 < p.2.2 ∧ 0 ≤ p.2.1 ∧ p.2.1 ≤ (1-δ)*(p.1+1/2)}] (fun p : ℝ × ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

/-- olverQ two large degree modified. -/
@[dlmf 14.15.E18]
theorem olverQ_two_large_degree_modified {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (fun p : ℝ × ℝ × ℝ => let ν:=p.1; let μ:=p.2.1; let x:=p.2.2; let α:=legendreDegreeAlpha ν μ; let y:=legendreDegreeY α x; olverQ ν μ x/(1/(legendreDegreeBeta ν μ*Gamma (ν+μ+1))*((α^2-y)/(x^2-1+α^2):ℂ)^(1/4:ℂ)*besselK μ ((ν+1/2)*Real.sqrt |y|))-1) =O[legendreUniformFilter {p : ℝ × ℝ × ℝ | 1 < p.2.2 ∧ 0 ≤ p.2.1 ∧ p.2.1 ≤ (1-δ)*(p.1+1/2)}] (fun p : ℝ × ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

/-- ferrersP cylinder uniform. -/
@[dlmf 14.15.E24]
theorem ferrersP_cylinder_uniform {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (fun p : ℝ × ℝ × ℝ => let ν:=p.1; let μ:=p.2.1; let x:=p.2.2; ferrersP ν (-μ) x/(1/((ν+1/2:ℂ)^(1/4:ℂ)*2^((ν+μ:ℂ)/2)*Gamma ((ν+μ:ℂ)/2+3/4))*legendreCylinderAmplitude ν μ x)-pcfU (μ-ν-1/2) (Real.sqrt (2*ν+1)*legendreCylinderZeta ν μ x)) =O[legendreUniformFilter {p : ℝ × ℝ × ℝ | p.2.2 ∈ Ico 0 1 ∧ δ*(p.1+1/2) ≤ p.2.1 ∧ p.2.1 ≤ p.1+1/2}] (fun p : ℝ × ℝ × ℝ => p.1^(-2/3:ℝ)*legendreCylinderEnvelope false (p.1+1/2-p.2.1) (Real.sqrt (2*p.1+1)*legendreCylinderZeta p.1 p.2.1 p.2.2)) := by
  sorry

/-- ferrersQ cylinder uniform. -/
@[dlmf 14.15.E25]
theorem ferrersQ_cylinder_uniform {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (fun p : ℝ × ℝ × ℝ => let ν:=p.1; let μ:=p.2.1; let x:=p.2.2; ferrersQ ν (-μ) x/(π/2*1/((ν+1/2:ℂ)^(1/4:ℂ)*2^((ν+μ:ℂ)/2)*Gamma ((ν+μ:ℂ)/2+3/4))*legendreCylinderAmplitude ν μ x)-pcfUBar (μ-ν-1/2) (Real.sqrt (2*ν+1)*legendreCylinderZeta ν μ x)) =O[legendreUniformFilter {p : ℝ × ℝ × ℝ | p.2.2 ∈ Ico 0 1 ∧ δ*(p.1+1/2) ≤ p.2.1 ∧ p.2.1 ≤ p.1+1/2}] (fun p : ℝ × ℝ × ℝ => p.1^(-2/3:ℝ)*legendreCylinderEnvelope true (p.1+1/2-p.2.1) (Real.sqrt (2*p.1+1)*legendreCylinderZeta p.1 p.2.1 p.2.2)) := by
  sorry

/-- ferrersP cylinder exponential uniform. -/
@[dlmf 14.15.E30]
theorem ferrersP_cylinder_exponential_uniform {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (fun p : ℝ × ℝ × ℝ => let ν:=p.1; let μ:=p.2.1; let x:=p.2.2; ferrersP ν (-μ) x/(1/((ν+1/2:ℂ)^(1/4:ℂ)*2^((ν+μ:ℂ)/2)*Gamma ((ν+μ:ℂ)/2+3/4))*legendreCylinderAmplitude ν μ x*pcfU (μ-ν-1/2) (Real.sqrt (2*ν+1)*legendreCylinderZeta ν μ x))-1) =O[legendreUniformFilter {p : ℝ × ℝ × ℝ | p.2.2 ∈ Ioo (-1:ℝ) 1 ∧ p.1+1/2 ≤ p.2.1 ∧ p.2.1 ≤ (p.1+1/2)/δ}] (fun p : ℝ × ℝ × ℝ => Real.log p.1/p.1) := by
  sorry

end DLMF.Legendre
