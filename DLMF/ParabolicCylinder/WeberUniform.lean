/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ParabolicCylinder.TurningPoint
public import DLMF.ParabolicCylinder.Weber

/-!
# Uniform expansions of the oscillatory W solution

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

/-- pcfW parameter scaling. -/
@[dlmf 12.14.E24]
theorem pcfW_parameter_scaling (μ : ℝ) (z : ℂ) :
    iteratedDeriv 2 (fun t : ℂ => pcfW (μ^2/2) (μ*t*Real.sqrt 2)) z=(μ:ℂ)^4*(1-z^2)*pcfW (μ^2/2) (μ*z*Real.sqrt 2) := by
  have hs2 : (Real.sqrt 2:ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hf : Differentiable ℂ (pcfW (μ^2/2)) := fun w => (hasDerivAt_pcfW _ w).differentiableAt
  have hf2 : Differentiable ℂ (deriv (pcfW (μ^2/2))) := by
    rw [deriv_pcfW]; exact fun w => (hasDerivAt_pcfWDeriv _ w).differentiableAt
  have e : (fun t : ℂ => pcfW (μ^2/2) (μ*t*Real.sqrt 2)) = fun t => pcfW (μ^2/2) ((μ*Real.sqrt 2)*t) := by
    funext t; ring_nf
  rw [e, iteratedDeriv_two_comp_const_mul hf hf2, show (μ:ℂ)*z*Real.sqrt 2 = (μ*Real.sqrt 2)*z by ring,
    show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, deriv_pcfW,
    (hasDerivAt_pcfWDeriv _ _).deriv]
  push_cast
  linear_combination (μ:ℂ)^4 * pcfW (μ^2/2) ((μ*Real.sqrt 2)*z) * (1/2 - ((Real.sqrt 2:ℂ)^2+2)*z^2/4) * hs2

/-- pcfWSigma. -/
@[dlmf 12.14.E27]
def pcfWSigma (μ t : ℝ) : ℝ :=
  μ^2*pcfXi t+π/4

/-- pcfWSigmaBar. -/
@[dlmf 12.14.E36]
def pcfWSigmaBar (μ t : ℝ) : ℝ :=
  μ^2*pcfXiBar t+π/4

/-- pcfWOlverL. -/
@[dlmf 12.14.E28]
def pcfWOlverL (g : ℂ → ℂ) (μ : ℝ) : ℂ :=
  Real.sqrt 2*exp (π*μ^2/8)*exp (I*(pcfGammaPhase (μ^2/2)/2-π/8))*g (μ*exp (-π*I/4))

/-- IsCylinderLNormalizer. -/
@[dlmf 12.14.E29, dlmf 12.14.E30]
def IsCylinderLNormalizer (l : ℝ → ℂ) (c : ℕ → ℂ) : Prop :=
  c 0=1 ∧ c 1=-1/1152 ∧ c 2=-16123/39813120 ∧ ∀ N : ℕ, (fun μ : ℝ => l μ/(2^(1/4:ℂ)*(μ:ℂ)^(-1/2:ℂ))-∑ s ∈ Finset.range N, c s/(μ:ℂ)^(4*s)) =O[atTop] (fun μ : ℝ => (μ:ℂ)^(-(4*N:ℤ)))

/-- pcfW elementary uniform. -/
@[dlmf 12.14.E25, dlmf 12.14.E26, dlmf 12.14.E31, dlmf 12.14.E34, dlmf 12.14.E35]
theorem pcfW_elementary_uniform  :
    ∃ g : ℂ → ℂ, ∃ c : ℕ → ℂ, IsCylinderGNormalizer (fun μ : ℝ => g μ) ∧ IsCylinderLNormalizer (pcfWOlverL g) c ∧ ∀ δ : ℝ, 0 < δ → δ < 1 → let l:=pcfWOlverL g; (∀ N : ℕ, (fun p : ℝ × ℝ => pcfW (p.1^2/2) (1*p.1*p.2*Real.sqrt 2)/(2^(-1/2:ℂ)*exp (-π*p.1^2/4)*l p.1/(p.2^2-1:ℂ)^(1/4:ℂ))-∑ k ∈ Finset.range N, Real.cos (pcfWSigma p.1 p.2+k*π/2)*pcfOlverA k p.2/(p.1:ℂ)^(2*k)) =O[pcfUniformFilter (Ici (1+δ))] (fun p : ℝ × ℝ => (p.1:ℂ)^(-(2*N:ℤ)))) ∧ (∀ N : ℕ, (fun p : ℝ × ℝ => pcfW (p.1^2/2) (-1*p.1*p.2*Real.sqrt 2)/(2^(1/2:ℂ)*exp (π*p.1^2/4)*l p.1/(p.2^2-1:ℂ)^(1/4:ℂ))-∑ k ∈ Finset.range N, Real.sin (pcfWSigma p.1 p.2+k*π/2)*pcfOlverA k p.2/(p.1:ℂ)^(2*k)) =O[pcfUniformFilter (Ici (1+δ))] (fun p : ℝ × ℝ => (p.1:ℂ)^(-(2*N:ℤ)))) ∧ (HasCylinderUniformExpansion (fun μ t => pcfW (μ^2/2) (μ*t*Real.sqrt 2)/(l μ*exp (μ^2*pcfEta t)/(Real.sqrt 2*exp (π*μ^2/4)*(1-t^2:ℂ)^(1/4:ℂ)))) (fun s t => (-1)^s*pcfOlverATilde s t) (Icc (-1+δ) (1-δ))) ∧ (∀ N : ℕ, (fun p : ℝ × ℝ => pcfW (-p.1^2/2) (p.1*p.2*Real.sqrt 2)/(l p.1/(p.2^2+1:ℂ)^(1/4:ℂ))-∑ k ∈ Finset.range N, Real.cos (pcfWSigmaBar p.1 p.2+k*π/2)*pcfOlverUBar k p.2/((p.2^2+1:ℂ)^(3*(k:ℂ)/2)*(p.1:ℂ)^(2*k))) =O[pcfUniformFilter univ] (fun p : ℝ × ℝ => (p.1:ℂ)^(-(2*N:ℤ)))) ∧ (∀ N : ℕ, (fun p : ℝ × ℝ => (deriv (pcfW (-p.1^2/2))) (p.1*p.2*Real.sqrt 2)/(-(p.1:ℂ)/Real.sqrt 2*l p.1*(p.2^2+1:ℂ)^(1/4:ℂ))-∑ k ∈ Finset.range N, Real.sin (pcfWSigmaBar p.1 p.2+k*π/2)*pcfOlverVBar k p.2/((p.2^2+1:ℂ)^(3*(k:ℂ)/2)*(p.1:ℂ)^(2*k))) =O[pcfUniformFilter univ] (fun p : ℝ × ℝ => (p.1:ℂ)^(-(2*N:ℤ)))) := by
  sorry

open DLMF.Airy

/-- pcfW airy uniform. -/
@[dlmf 12.14.E32, dlmf 12.14.E33]
theorem pcfW_airy_uniform  :
    ∃ g : ℂ → ℂ, ∃ c : ℕ → ℂ, IsCylinderGNormalizer (fun μ : ℝ => g μ) ∧ IsCylinderLNormalizer (pcfWOlverL g) c ∧ ∀ δ : ℝ, 0 < δ → δ < 2 → ∀ N : ℕ, let l:=pcfWOlverL g; ((fun p : ℝ × ℝ => let μ:=p.1; let t:=p.2; let ζ:=pcfZeta t; let u : ℂ:=-((μ^(4/3:ℝ):ℝ):ℂ)*ζ; pcfW (μ^2/2) (1*μ*t*Real.sqrt 2)/(Real.sqrt π*(μ:ℂ)^(1/3:ℂ)*l μ/(2^(1/2:ℂ)*exp (1*π*μ^2/4))*pcfPhi ζ)-(airyBi u*(∑ k ∈ Finset.range N, (-1)^k*pcfAiryA k ζ/(μ:ℂ)^(4*k))+airyBiDeriv u/(μ:ℂ)^(8/3:ℂ)*(∑ k ∈ Finset.range N, (-1)^k*pcfAiryB k ζ/(μ:ℂ)^(4*k)))) =O[pcfUniformFilter (Ici (-1+δ))] (fun p : ℝ × ℝ => p.1^(-(4*N:ℝ))*(‖airyBi (-((p.1^(4/3:ℝ):ℝ):ℂ)*pcfZeta p.2)‖+p.1^(-8/3:ℝ)*‖airyBiDeriv (-((p.1^(4/3:ℝ):ℝ):ℂ)*pcfZeta p.2)‖))) ∧ ((fun p : ℝ × ℝ => let μ:=p.1; let t:=p.2; let ζ:=pcfZeta t; let u : ℂ:=-((μ^(4/3:ℝ):ℝ):ℂ)*ζ; pcfW (μ^2/2) (-1*μ*t*Real.sqrt 2)/(Real.sqrt π*(μ:ℂ)^(1/3:ℂ)*l μ/(2^(-1/2:ℂ)*exp (-1*π*μ^2/4))*pcfPhi ζ)-(airyAi u*(∑ k ∈ Finset.range N, (-1)^k*pcfAiryA k ζ/(μ:ℂ)^(4*k))+airyAiDeriv u/(μ:ℂ)^(8/3:ℂ)*(∑ k ∈ Finset.range N, (-1)^k*pcfAiryB k ζ/(μ:ℂ)^(4*k)))) =O[pcfUniformFilter (Ici (-1+δ))] (fun p : ℝ × ℝ => p.1^(-(4*N:ℝ))*(‖airyAi (-((p.1^(4/3:ℝ):ℝ):ℂ)*pcfZeta p.2)‖+p.1^(-8/3:ℝ)*‖airyAiDeriv (-((p.1^(4/3:ℝ):ℝ):ℂ)*pcfZeta p.2)‖))) := by
  sorry

end DLMF.Confluent
