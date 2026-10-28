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

/-- DLMF 14.15.1: for fixed `ν` and `J ∈ ℕ`, `((1+x)/(1−x))^{μ/2} 𝖯^{−μ}_ν(x) = Σ_{j<J} (ν+1)_j
(−ν)_j/(j! Γ(j+1+μ)) ((1−x)/2)^j + O(1/Γ(J+1+μ))` as `μ → ∞`, uniformly for `-1 < x < 1`. -/
@[dlmf 14.15.E1]
theorem ferrersP_large_order_uniform (ν : ℂ) (J : ℕ) :
    (fun p : ℝ × ℝ => ((1+p.2)/(1-p.2):ℂ)^((p.1:ℂ)/2)*ferrersP ν (-p.1) p.2-∑ j ∈ Finset.range J, poch (ν+1) j*poch (-ν) j/((j.factorial:ℂ)*Gamma (j+1+p.1))*((1-p.2)/2:ℂ)^j) =O[comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | p.2 ∈ Ioo (-1:ℝ) 1}] (fun p : ℝ × ℝ => 1/Gamma (J+1+p.1)) := by
  sorry

/-- DLMF 14.15.2: for fixed real `ν ≥ −1/2`, `P^{−μ}_ν(x) = (1/Γ(μ+1)) (2μu/π)^{1/2} K_{ν+1/2}(μu)
(1 + O(1/μ))` as `μ → ∞`, uniformly for `x > 1`, where `u = ½ ln((x+1)/(x−1))`. -/
@[dlmf 14.15.E2]
theorem associatedP_large_order_uniform {ν : ℝ} (hν : -1/2 ≤ ν) :
    (fun p : ℝ × ℝ => associatedP ν (-p.1) p.2/(1/Gamma (p.1+1)*(2*p.1*legendreUCoordinate p.2/π:ℂ)^(1/2:ℂ)*besselK (ν+1/2) (p.1*legendreUCoordinate p.2))-1) =O[comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 1 < p.2}] (fun p : ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

/-- DLMF 14.15.3: for fixed real `ν ≥ −1/2`, `𝑸^μ_ν(x) = μ^{−ν−1/2} (πu/2)^{1/2} I_{ν+1/2}(μu) (1 +
O(1/μ))` as `μ → ∞`, uniformly for `x > 1`, where `u = ½ ln((x+1)/(x−1))`. -/
@[dlmf 14.15.E3]
theorem olverQ_large_order_uniform {ν : ℝ} (hν : -1/2 ≤ ν) :
    (fun p : ℝ × ℝ => olverQ ν p.1 p.2/((p.1:ℂ)^(-(ν:ℂ)-1/2)*(π*legendreUCoordinate p.2/2:ℂ)^(1/2:ℂ)*besselI (ν+1/2) (p.1*legendreUCoordinate p.2))-1) =O[comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 1 < p.2}] (fun p : ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

/-- The leading factor of DLMF 14.15.4: `(1/Γ(μ+1)) (1−α²)^{−μ/2} ((1−α)/(1+α))^{ν/2+1/4} (α²x² + 1
− α²)^{−1/4} e^{−μρ}`, with `α = (ν+1/2)/μ` (14.15.5) and `ρ` from 14.15.7. -/
def legendreOrderPrefactor (ν μ x : ℝ) : ℂ :=
  let α:=legendreOrderAlpha ν μ; 1/Gamma (μ+1)*(1-α^2:ℂ)^(-(μ:ℂ)/2)*((1-α)/(1+α):ℂ)^((ν:ℂ)/2+1/4)*(α^2*x^2+1-α^2:ℂ)^(-1/4:ℂ)*exp (-μ*legendreOrderRho α x)

/-- DLMF 14.15.4: for fixed `δ ∈ (0,1)`, `𝖯^{−μ}_ν(x) = legendreOrderPrefactor ν μ x · (1 + O(1/μ))`
as `μ → ∞`, uniformly for `-1 < x < 1` and `0 ≤ ν + 1/2 ≤ (1−δ)μ`. -/
@[dlmf 14.15.E4]
theorem ferrersP_two_large_parameters {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (fun p : ℝ × ℝ × ℝ => ferrersP p.2.1 (-p.1) p.2.2/legendreOrderPrefactor p.2.1 p.1 p.2.2-1) =O[legendreUniformFilter {p : ℝ × ℝ × ℝ | p.2.2 ∈ Ioo (-1:ℝ) 1 ∧ 0 ≤ p.2.1+1/2 ∧ p.2.1+1/2 ≤ (1-δ)*p.1}] (fun p : ℝ × ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

/-- DLMF 14.15.8: for fixed `δ ∈ (0,1)`, `P^{−μ}_ν(x) = (2μ/π)^{1/2}/Γ(μ+1) ·
((1−α)/(1+α))^{ν/2+1/4} (1−α²)^{−μ/2} ((α²+η²)/(α²(x²−1)+1))^{1/4} K_{ν+1/2}(μη) (1 + O(1/μ))`
as `μ → ∞`, uniformly for `x > 1` and `0 ≤ ν + 1/2 ≤ (1−δ)μ`, with `α = (ν+1/2)/μ` and `η` from
14.15.10. -/
@[dlmf 14.15.E8]
theorem associatedP_two_large_order_uniform {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (fun p : ℝ × ℝ × ℝ => let μ:=p.1; let ν:=p.2.1; let x:=p.2.2; let α:=legendreOrderAlpha ν μ; let η:=legendreOrderEta α x; associatedP ν (-μ) x/((2*μ/π:ℂ)^(1/2:ℂ)/Gamma (μ+1)*((1-α)/(1+α):ℂ)^((ν:ℂ)/2+1/4)*(1-α^2:ℂ)^(-(μ:ℂ)/2)*((α^2+η^2)/(α^2*(x^2-1)+1):ℂ)^(1/4:ℂ)*besselK (ν+1/2) (μ*η))-1) =O[legendreUniformFilter {p : ℝ × ℝ × ℝ | 1 < p.2.2 ∧ 0 ≤ p.2.1+1/2 ∧ p.2.1+1/2 ≤ (1-δ)*p.1}] (fun p : ℝ × ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

/-- DLMF 14.15.9: for fixed `δ ∈ (0,1)`, `𝑸^μ_ν(x) = (π/2)^{1/2} (e/μ)^{ν+1/2} ((1−α)/(1+α))^{μ/2}
(1−α²)^{−ν/2−1/4} ((α²+η²)/(α²(x²−1)+1))^{1/4} I_{ν+1/2}(μη) (1 + O(1/μ))` as `μ → ∞`, uniformly for
`x > 1` and `0 ≤ ν + 1/2 ≤ (1−δ)μ`, with `α = (ν+1/2)/μ` and `η` from 14.15.10. -/
@[dlmf 14.15.E9]
theorem olverQ_two_large_order_uniform {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (fun p : ℝ × ℝ × ℝ => let μ:=p.1; let ν:=p.2.1; let x:=p.2.2; let α:=legendreOrderAlpha ν μ; let η:=legendreOrderEta α x; olverQ ν μ x/((π/2:ℂ)^(1/2:ℂ)*(Real.exp 1/μ:ℂ)^(ν+1/2:ℂ)*((1-α)/(1+α):ℂ)^((μ:ℂ)/2)*(1-α^2:ℂ)^(-(ν:ℂ)/2-1/4)*((α^2+η^2)/(α^2*(x^2-1)+1):ℂ)^(1/4:ℂ)*besselI (ν+1/2) (μ*η))-1) =O[legendreUniformFilter {p : ℝ × ℝ × ℝ | 1 < p.2.2 ∧ 0 ≤ p.2.1+1/2 ∧ p.2.1+1/2 ≤ (1-δ)*p.1}] (fun p : ℝ × ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

/-- DLMF 14.15.11: for fixed `μ ≥ 0` and `δ ∈ (0, π)`, `𝖯^{−μ}_ν(cos θ) = ν^{−μ} (θ/sin θ)^{1/2}
(J_μ((ν+1/2)θ) + env J_μ((ν+1/2)θ) · O(1/ν))` as `ν → ∞`, uniformly for `0 < θ ≤ π − δ`. -/
@[dlmf 14.15.E11]
theorem ferrersP_large_degree_uniform {μ : ℝ} (hμ : 0 ≤ μ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun p : ℝ × ℝ => ferrersP p.1 (-μ) (Real.cos p.2)/((p.1:ℂ)^(-(μ:ℂ))*(p.2/Real.sin p.2:ℂ)^(1/2:ℂ))-besselJ μ ((p.1+1/2)*p.2)) =O[comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ π-δ}] (fun p : ℝ × ℝ => legendreBesselEnvelope false μ ((p.1+1/2)*p.2)/p.1) := by
  sorry

/-- DLMF 14.15.12: for fixed `μ ≥ 0` and `δ ∈ (0, π)`, `𝖰^{−μ}_ν(cos θ) = −(π/2) ν^{−μ} (θ/sin
θ)^{1/2} (Y_μ((ν+1/2)θ) + env Y_μ((ν+1/2)θ) · O(1/ν))` as `ν → ∞`, uniformly for `0 < θ ≤ π − δ`. -/
@[dlmf 14.15.E12]
theorem ferrersQ_large_degree_uniform {μ : ℝ} (hμ : 0 ≤ μ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun p : ℝ × ℝ => ferrersQ p.1 (-μ) (Real.cos p.2)/(-π/2*(p.1:ℂ)^(-(μ:ℂ))*(p.2/Real.sin p.2:ℂ)^(1/2:ℂ))-besselY μ ((p.1+1/2)*p.2)) =O[comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ π-δ}] (fun p : ℝ × ℝ => legendreBesselEnvelope true μ ((p.1+1/2)*p.2)/p.1) := by
  sorry

/-- DLMF 14.15.13: for fixed `μ ≥ 0`, `P^{−μ}_ν(cosh ξ) = ν^{−μ} (ξ/sinh ξ)^{1/2} I_μ((ν+1/2)ξ) (1 +
O(1/ν))` as `ν → ∞`, uniformly for `ξ > 0`. -/
@[dlmf 14.15.E13]
theorem associatedP_large_degree_uniform {μ : ℝ} (hμ : 0 ≤ μ) :
    (fun p : ℝ × ℝ => let ν:=p.1; let ξ:=p.2; associatedP ν (-μ) (Real.cosh ξ)/((ν:ℂ)^(-(μ:ℂ))*(ξ/Real.sinh ξ:ℂ)^(1/2:ℂ)*besselI μ ((ν+1/2)*ξ))-1) =O[comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 0 < p.2}] (fun p : ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

/-- DLMF 14.15.14: for fixed `μ ≥ 0`, `𝑸^μ_ν(cosh ξ) = ν^μ/Γ(ν+μ+1) · (ξ/sinh ξ)^{1/2} K_μ((ν+1/2)ξ)
(1 + O(1/ν))` as `ν → ∞`, uniformly for `ξ > 0`. -/
@[dlmf 14.15.E14]
theorem olverQ_large_degree_uniform {μ : ℝ} (hμ : 0 ≤ μ) :
    (fun p : ℝ × ℝ => let ν:=p.1; let ξ:=p.2; olverQ ν μ (Real.cosh ξ)/((ν:ℂ)^(μ:ℂ)/Gamma (ν+μ+1)*(ξ/Real.sinh ξ:ℂ)^(1/2:ℂ)*besselK μ ((ν+1/2)*ξ))-1) =O[comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 0 < p.2}] (fun p : ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

/-- DLMF 14.15.15: for fixed `δ ∈ (0,1)`, `𝖯^{−μ}_ν(x) = β ((y−α²)/(1−α²−x²))^{1/4} (J_μ((ν+1/2)
y^{1/2}) + env J_μ((ν+1/2) y^{1/2}) · O(1/ν))` as `ν → ∞`, uniformly for `0 ≤ x < 1` and `0 ≤ μ ≤
(1−δ)(ν+1/2)`, with `α`, `β`, `y` from 14.15.19–14.15.21. -/
@[dlmf 14.15.E15]
theorem ferrersP_two_large_degree_uniform {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (fun p : ℝ × ℝ × ℝ => let ν:=p.1; let μ:=p.2.1; let x:=p.2.2; let α:=legendreDegreeAlpha ν μ; ferrersP ν (-μ) x/(legendreDegreeBeta ν μ*legendreDegreeAmplitude α x)-besselJ μ ((ν+1/2)*Real.sqrt (legendreDegreeY α x))) =O[legendreUniformFilter {p : ℝ × ℝ × ℝ | p.2.2 ∈ Ico 0 1 ∧ 0 ≤ p.2.1 ∧ p.2.1 ≤ (1-δ)*(p.1+1/2)}] (fun p : ℝ × ℝ × ℝ => legendreBesselEnvelope false p.2.1 ((p.1+1/2)*Real.sqrt (legendreDegreeY (legendreDegreeAlpha p.1 p.2.1) p.2.2))/p.1) := by
  sorry

/-- DLMF 14.15.16: for fixed `δ ∈ (0,1)`, `𝖰^{−μ}_ν(x) = −(π/2) β ((y−α²)/(1−α²−x²))^{1/4}
(Y_μ((ν+1/2) y^{1/2}) + env Y_μ((ν+1/2) y^{1/2}) · O(1/ν))` as `ν → ∞`, uniformly for `0 ≤ x < 1`
and `0 ≤ μ ≤ (1−δ)(ν+1/2)`, with `α`, `β`, `y` from 14.15.19–14.15.21. -/
@[dlmf 14.15.E16]
theorem ferrersQ_two_large_degree_uniform {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (fun p : ℝ × ℝ × ℝ => let ν:=p.1; let μ:=p.2.1; let x:=p.2.2; let α:=legendreDegreeAlpha ν μ; ferrersQ ν (-μ) x/(-π/2*legendreDegreeBeta ν μ*legendreDegreeAmplitude α x)-besselY μ ((ν+1/2)*Real.sqrt (legendreDegreeY α x))) =O[legendreUniformFilter {p : ℝ × ℝ × ℝ | p.2.2 ∈ Ico 0 1 ∧ 0 ≤ p.2.1 ∧ p.2.1 ≤ (1-δ)*(p.1+1/2)}] (fun p : ℝ × ℝ × ℝ => legendreBesselEnvelope true p.2.1 ((p.1+1/2)*Real.sqrt (legendreDegreeY (legendreDegreeAlpha p.1 p.2.1) p.2.2))/p.1) := by
  sorry

/-- DLMF 14.15.17: for fixed `δ ∈ (0,1)`, `P^{−μ}_ν(x) = β ((α²−y)/(x²−1+α²))^{1/4}
I_μ((ν+1/2)|y|^{1/2}) (1 + O(1/ν))` as `ν → ∞`, uniformly for `x > 1` and `0 ≤ μ ≤ (1−δ)(ν+1/2)`,
with `α`, `β`, `y` from 14.15.19, 14.15.20, 14.15.22. -/
@[dlmf 14.15.E17]
theorem associatedP_two_large_degree_modified {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (fun p : ℝ × ℝ × ℝ => let ν:=p.1; let μ:=p.2.1; let x:=p.2.2; let α:=legendreDegreeAlpha ν μ; let y:=legendreDegreeY α x; associatedP ν (-μ) x/(legendreDegreeBeta ν μ*((α^2-y)/(x^2-1+α^2):ℂ)^(1/4:ℂ)*besselI μ ((ν+1/2)*Real.sqrt |y|))-1) =O[legendreUniformFilter {p : ℝ × ℝ × ℝ | 1 < p.2.2 ∧ 0 ≤ p.2.1 ∧ p.2.1 ≤ (1-δ)*(p.1+1/2)}] (fun p : ℝ × ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

/-- DLMF 14.15.18: for fixed `δ ∈ (0,1)`, `𝑸^μ_ν(x) = 1/(β Γ(ν+μ+1)) · ((α²−y)/(x²−1+α²))^{1/4}
K_μ((ν+1/2)|y|^{1/2}) (1 + O(1/ν))` as `ν → ∞`, uniformly for `x > 1` and `0 ≤ μ ≤ (1−δ)(ν+1/2)`,
with `α`, `β`, `y` from 14.15.19, 14.15.20, 14.15.22. -/
@[dlmf 14.15.E18]
theorem olverQ_two_large_degree_modified {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (fun p : ℝ × ℝ × ℝ => let ν:=p.1; let μ:=p.2.1; let x:=p.2.2; let α:=legendreDegreeAlpha ν μ; let y:=legendreDegreeY α x; olverQ ν μ x/(1/(legendreDegreeBeta ν μ*Gamma (ν+μ+1))*((α^2-y)/(x^2-1+α^2):ℂ)^(1/4:ℂ)*besselK μ ((ν+1/2)*Real.sqrt |y|))-1) =O[legendreUniformFilter {p : ℝ × ℝ × ℝ | 1 < p.2.2 ∧ 0 ≤ p.2.1 ∧ p.2.1 ≤ (1-δ)*(p.1+1/2)}] (fun p : ℝ × ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

/-- DLMF 14.15.24: for fixed `δ ∈ (0,1)`, `𝖯^{−μ}_ν(x) = A(x) U(μ−ν−1/2, (2ν+1)^{1/2}
ζ)/((ν+1/2)^{1/4} 2^{(ν+μ)/2} Γ((ν+μ)/2+3/4)) + O(ν^{−2/3}) · env U(μ−ν−1/2, (2ν+1)^{1/2} ζ)` as `ν
→ ∞`, uniformly for `0 ≤ x < 1` and `δ(ν+1/2) ≤ μ ≤ ν+1/2`, with `ζ` from 14.15.27–14.15.29 and
amplitude `A = ((ζ²−α²)/(x²−a²))^{1/4}` (`legendreCylinderAmplitude`); the error is stated for the
quotient by the prefactor. -/
@[dlmf 14.15.E24]
theorem ferrersP_cylinder_uniform {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (fun p : ℝ × ℝ × ℝ => let ν:=p.1; let μ:=p.2.1; let x:=p.2.2; ferrersP ν (-μ) x/(1/((ν+1/2:ℂ)^(1/4:ℂ)*2^((ν+μ:ℂ)/2)*Gamma ((ν+μ:ℂ)/2+3/4))*legendreCylinderAmplitude ν μ x)-pcfU (μ-ν-1/2) (Real.sqrt (2*ν+1)*legendreCylinderZeta ν μ x)) =O[legendreUniformFilter {p : ℝ × ℝ × ℝ | p.2.2 ∈ Ico 0 1 ∧ δ*(p.1+1/2) ≤ p.2.1 ∧ p.2.1 ≤ p.1+1/2}] (fun p : ℝ × ℝ × ℝ => p.1^(-2/3:ℝ)*legendreCylinderEnvelope false (p.1+1/2-p.2.1) (Real.sqrt (2*p.1+1)*legendreCylinderZeta p.1 p.2.1 p.2.2)) := by
  sorry

/-- DLMF 14.15.25: for fixed `δ ∈ (0,1)`, `𝖰^{−μ}_ν(x) = (π/2) A(x) Ū(μ−ν−1/2, (2ν+1)^{1/2}
ζ)/((ν+1/2)^{1/4} 2^{(ν+μ)/2} Γ((ν+μ)/2+3/4)) + O(ν^{−2/3}) · env Ū(μ−ν−1/2, (2ν+1)^{1/2} ζ)` as `ν
→ ∞`, uniformly for `0 ≤ x < 1` and `δ(ν+1/2) ≤ μ ≤ ν+1/2`, with `ζ` and the amplitude `A` as in
14.15.24; the error is stated for the quotient by the prefactor. -/
@[dlmf 14.15.E25]
theorem ferrersQ_cylinder_uniform {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (fun p : ℝ × ℝ × ℝ => let ν:=p.1; let μ:=p.2.1; let x:=p.2.2; ferrersQ ν (-μ) x/(π/2*1/((ν+1/2:ℂ)^(1/4:ℂ)*2^((ν+μ:ℂ)/2)*Gamma ((ν+μ:ℂ)/2+3/4))*legendreCylinderAmplitude ν μ x)-pcfUBar (μ-ν-1/2) (Real.sqrt (2*ν+1)*legendreCylinderZeta ν μ x)) =O[legendreUniformFilter {p : ℝ × ℝ × ℝ | p.2.2 ∈ Ico 0 1 ∧ δ*(p.1+1/2) ≤ p.2.1 ∧ p.2.1 ≤ p.1+1/2}] (fun p : ℝ × ℝ × ℝ => p.1^(-2/3:ℝ)*legendreCylinderEnvelope true (p.1+1/2-p.2.1) (Real.sqrt (2*p.1+1)*legendreCylinderZeta p.1 p.2.1 p.2.2)) := by
  sorry

/-- DLMF 14.15.30: for fixed `δ ∈ (0,1)`, `𝖯^{−μ}_ν(x) = A(x) U(μ−ν−1/2, (2ν+1)^{1/2}
ζ)/((ν+1/2)^{1/4} 2^{(ν+μ)/2} Γ((ν+μ)/2+3/4)) · (1 + O(ln ν/ν))` as `ν → ∞`, uniformly for `-1
< x < 1` and `ν+1/2 ≤ μ ≤ (ν+1/2)/δ`, with `ζ` from 14.15.31 and amplitude `A =
((ζ²+α²)/(x²+a²))^{1/4}`. -/
@[dlmf 14.15.E30]
theorem ferrersP_cylinder_exponential_uniform {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (fun p : ℝ × ℝ × ℝ => let ν:=p.1; let μ:=p.2.1; let x:=p.2.2; ferrersP ν (-μ) x/(1/((ν+1/2:ℂ)^(1/4:ℂ)*2^((ν+μ:ℂ)/2)*Gamma ((ν+μ:ℂ)/2+3/4))*legendreCylinderAmplitude ν μ x*pcfU (μ-ν-1/2) (Real.sqrt (2*ν+1)*legendreCylinderZeta ν μ x))-1) =O[legendreUniformFilter {p : ℝ × ℝ × ℝ | p.2.2 ∈ Ioo (-1:ℝ) 1 ∧ p.1+1/2 ≤ p.2.1 ∧ p.2.1 ≤ (p.1+1/2)/δ}] (fun p : ℝ × ℝ × ℝ => Real.log p.1/p.1) := by
  sorry

end DLMF.Legendre
