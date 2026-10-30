/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Zeros
public import DLMF.ParabolicCylinder.Uniform

/-!
# Cylinder turning-point expansions and large-parameter zeros

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

open DLMF.Airy

/-- Second derivative of a linear rescaling: `(f(c t))'' = c² f''(c t)`. -/
theorem iteratedDeriv_two_comp_const_mul {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf2 : Differentiable ℂ (deriv f)) (c t : ℂ) :
    iteratedDeriv 2 (fun t => f (c*t)) t = c^2 * iteratedDeriv 2 f (c*t) := by
  have hl : ∀ w : ℂ, HasDerivAt (fun w : ℂ => c*w) c w := fun w =>
    ((hasDerivAt_id w).const_mul c).congr_deriv (mul_one c)
  have d1 : deriv (fun t => f (c*t)) = fun t => deriv f (c*t) * c := by
    funext w; exact ((hf _).hasDerivAt.comp w (hl w)).deriv
  have d2 : deriv (fun t => deriv f (c*t) * c) t = deriv (deriv f) (c*t) * c * c :=
    (((hf2 _).hasDerivAt.comp t (hl t)).mul_const c).deriv
  rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_succ,
    iteratedDeriv_one, d1, d2]
  ring

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv 2 (fun t : ℂ => f
(μ*t*Real.sqrt 2)) t=(μ:ℂ)^4*(t^2+s)*f (μ*t*Real.sqrt 2)`. -/
@[dlmf 12.10.E1, dlmf 12.10.E2]
theorem pcf_parameter_scaling (μ : ℝ) (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hf2 : Differentiable ℂ (deriv f)) (s : ℂ) (hode : ∀ z, iteratedDeriv 2 f z-(z^2/4+s*μ^2/2)*f z=0) (t : ℂ) :
    iteratedDeriv 2 (fun t : ℂ => f (μ*t*Real.sqrt 2)) t=(μ:ℂ)^4*(t^2+s)*f (μ*t*Real.sqrt 2) := by
  have hs2 : (Real.sqrt 2:ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have e : (fun t : ℂ => f (μ*t*Real.sqrt 2)) = fun t => f ((μ*Real.sqrt 2)*t) := by
    funext t; ring_nf
  rw [e, iteratedDeriv_two_comp_const_mul hf hf2, show (μ:ℂ)*t*Real.sqrt 2 = (μ*Real.sqrt 2)*t by ring]
  have h := hode ((μ*Real.sqrt 2)*t)
  linear_combination (μ*Real.sqrt 2:ℂ)^2 * h + (μ:ℂ)^4 * f ((μ*Real.sqrt 2)*t) *
    (((Real.sqrt 2:ℂ)^2+2)*t^2/4 + s/2) * hs2

/-- Absolute Airy envelopes allow uniform error bounds through zeros. -/
def pcfAiryEnvelope (A D : ℂ → ℂ) (isDeriv : Bool) (μ t : ℝ) : ℝ :=
  let u : ℂ := ((μ^(4/3:ℝ):ℝ):ℂ)*pcfZeta t; if isDeriv then μ^(-4/3:ℝ)*‖A u‖+‖D u‖ else ‖A u‖+μ^(-8/3:ℝ)*‖D u‖

/-- A uniform Airy-type cylinder expansion on the indicated real set, with both coefficient series
and the derivative scaling controlled at every truncation order. -/
def HasCylinderAiryExpansion (F : ℝ → ℝ → ℂ) (A D : ℂ → ℂ) (isDeriv : Bool) (S : Set ℝ) : Prop :=
  ∀ N : ℕ, (fun p : ℝ × ℝ => let μ:=p.1; let t:=p.2; let ζ:=pcfZeta t; let u : ℂ:=((μ^(4/3:ℝ):ℝ):ℂ)*ζ; F μ t-(if isDeriv then A u/(μ:ℂ)^(4/3:ℂ)*(∑ s ∈ Finset.range N, pcfAiryC s ζ/(μ:ℂ)^(4*s))+D u*(∑ s ∈ Finset.range N, pcfAiryD s ζ/(μ:ℂ)^(4*s)) else A u*(∑ s ∈ Finset.range N, pcfAiryA s ζ/(μ:ℂ)^(4*s))+D u/(μ:ℂ)^(8/3:ℂ)*(∑ s ∈ Finset.range N, pcfAiryB s ζ/(μ:ℂ)^(4*s)))) =O[pcfUniformFilter S] (fun p : ℝ × ℝ => p.1^(-(4*N:ℝ))*pcfAiryEnvelope A D isDeriv p.1 p.2)

/-- A cylinder normalizer gives uniform Airy-type expansions of U and its derivative through the
turning point, for `t ≥ -1+δ`. -/
@[dlmf 12.10.E35, dlmf 12.10.E36, dlmf 12.10.E37, dlmf 12.10.E38]
theorem pcf_airy_uniform  :
    ∃ g : ℝ → ℂ, IsCylinderGNormalizer g ∧ ∀ δ : ℝ, 0 < δ → δ < 2 → HasCylinderAiryExpansion (fun μ t => pcfU (-μ^2/2) (μ*t*Real.sqrt 2)/(2*Real.sqrt π*(μ:ℂ)^(1/3:ℂ)*g μ*pcfPhi (pcfZeta t))) airyAi airyAiDeriv false (Ici (-1+δ)) ∧ HasCylinderAiryExpansion (fun μ t => pcfUDeriv (-μ^2/2) (μ*t*Real.sqrt 2)/(Real.sqrt (2*π)*(μ:ℂ)^(2/3:ℂ)*g μ/pcfPhi (pcfZeta t))) airyAi airyAiDeriv true (Ici (-1+δ)) ∧ HasCylinderAiryExpansion (fun μ t => pcfV (-μ^2/2) (μ*t*Real.sqrt 2)/(2*Real.sqrt π*(μ:ℂ)^(1/3:ℂ)*g μ*pcfPhi (pcfZeta t) /Gamma (1/2+μ^2/2))) airyBi airyBiDeriv false (Ici (-1+δ)) ∧ HasCylinderAiryExpansion (fun μ t => pcfVDeriv (-μ^2/2) (μ*t*Real.sqrt 2)/(Real.sqrt (2*π)*(μ:ℂ)^(2/3:ℂ)*g μ/pcfPhi (pcfZeta t) /Gamma (1/2+μ^2/2))) airyBi airyBiDeriv true (Ici (-1+δ)) := by
  sorry

/-- Real zero counted in descending order; existence and finiteness are separate assertions. -/
def pcfDescendingZero (a : ℝ) (isDeriv : Bool) (s : ℕ) : ℝ :=
  Classical.epsilon (fun x : ℝ => let F : ℝ → ℂ:=if isDeriv then fun x => pcfUDeriv a x else fun x => pcfU a x; F x=0 ∧ ({y : ℝ | x < y ∧ F y=0}:Set ℝ).ncard=s-1)

/-- The stated relation follows from the given hypotheses: `∀ᶠ μ : ℝ in atTop, let x`. -/
theorem pcfDescendingZero_eventually (s : ℕ) (hs : 0 < s) (isDeriv : Bool) :
    ∀ᶠ μ : ℝ in atTop, let x:=pcfDescendingZero (-μ^2/2) isDeriv s; let F : ℝ → ℂ:=if isDeriv then fun x => pcfUDeriv (-μ^2/2) x else fun x => pcfU (-μ^2/2) x; F x=0 ∧ Set.Finite {y : ℝ | x < y ∧ F y=0} ∧ ({y : ℝ | x < y ∧ F y=0}:Set ℝ).ncard=s-1 := by
  sorry

/-- The first correction in the cylinder turning-point zero expansion, defined by its removable
limit in the uniform zeta coordinate. -/
@[dlmf 12.11.E6]
def pcfZeroP1 (ζ : ℝ) : ℝ :=
  limUnder (𝓝[≠] ζ) (fun u : ℝ => let t:=pcfInverseZeta u; (t^3-6*t)/(24*(t^2-1)^2)+5/(48*Real.sqrt ((t^2-1)*u^3)))

/-- The map `(fun u : ℝ => let t:=pcfInverseZeta u; (t^3-6*t)/(24*(t^2-1)^2)+5/(48*Real.sqrt
((t^2-1)*u^3)))` tends to `(𝓝 (pcfZeroP1 ζ))` along `(𝓝[≠] ζ)`. -/
@[dlmf 12.11.E6]
theorem pcfZeroP1_limit {ζ : ℝ} (hζ : -(3*π/4)^(2/3:ℝ) < ζ) :
    Tendsto (fun u : ℝ => let t:=pcfInverseZeta u; (t^3-6*t)/(24*(t^2-1)^2)+5/(48*Real.sqrt ((t^2-1)*u^3))) (𝓝[≠] ζ) (𝓝 (pcfZeroP1 ζ)) := by
  sorry

/-- Asymptotic bound with the indicated comparison function: `∃ p : ℕ → ℝ → ℝ, p 0=pcfInverseZeta
∧ p 1=pcfZeroP1 ∧ ∀ s : ℕ, 0 < s → ∀ N : ℕ, (fun μ : ℝ => pcfDescendingZero (-μ^2/2) false
s/(Real.sqrt 2*μ)-∑ j ∈ Finset.range N, p j (μ^(-4/3:ℝ)*airyAiZero s)/(μ^(4*j))) =O[atTop]
(fun μ : ℝ => μ^(-(4*N:ℝ)))`. -/
@[dlmf 12.11.E4, dlmf 12.11.E5]
theorem pcf_real_zero_expansion_4  :
    ∃ p : ℕ → ℝ → ℝ, p 0=pcfInverseZeta ∧ p 1=pcfZeroP1 ∧ ∀ s : ℕ, 0 < s → ∀ N : ℕ, (fun μ : ℝ => pcfDescendingZero (-μ^2/2) false s/(Real.sqrt 2*μ)-∑ j ∈ Finset.range N, p j (μ^(-4/3:ℝ)*airyAiZero s)/(μ^(4*j))) =O[atTop] (fun μ : ℝ => μ^(-(4*N:ℝ))) := by
  sorry

/-- Asymptotic bound with the indicated comparison function: `∃ p : ℕ → ℝ → ℝ, p 0=pcfInverseZeta
∧ ∀ s : ℕ, 0 < s → ∀ N : ℕ, (fun μ : ℝ => pcfDescendingZero (-μ^2/2) true s/(Real.sqrt 2*μ)-∑
j ∈ Finset.range N, p j (μ^(-4/3:ℝ)*airyAiDerivZero s)/(μ^(4*j))) =O[atTop] (fun μ : ℝ =>
μ^(-(4*N:ℝ)))`. -/
@[dlmf 12.11.E7, dlmf 12.11.E8]
theorem pcf_real_zero_expansion_7  :
    ∃ p : ℕ → ℝ → ℝ, p 0=pcfInverseZeta ∧ ∀ s : ℕ, 0 < s → ∀ N : ℕ, (fun μ : ℝ => pcfDescendingZero (-μ^2/2) true s/(Real.sqrt 2*μ)-∑ j ∈ Finset.range N, p j (μ^(-4/3:ℝ)*airyAiDerivZero s)/(μ^(4*j))) =O[atTop] (fun μ : ℝ => μ^(-(4*N:ℝ))) := by
  sorry

/-- Exact coefficients, rather than rounded decimals treated as exact asymptotic constants. -/
@[dlmf 12.11.E9]
def pcfFirstZeroCoeff (k : ℕ) : ℂ :=
  asymptoticCoeff (fun v : ℝ => ((pcfDescendingZero (-v^3/2) false 1/(Real.sqrt 2*v^(3/2:ℝ)):ℝ):ℂ)) (2*k)

/-- Asymptotic bound with the indicated comparison function: `(fun μ : ℝ => (pcfDescendingZero
(-μ^2/2) false 1/(Real.sqrt 2*μ):ℂ)-∑ j ∈ Finset.range N, pcfFirstZeroCoeff
j*(μ:ℂ)^(-4*(j:ℂ)/3)) =O[atTop] (fun μ : ℝ => μ^(-4*(N:ℝ)/3))`. -/
@[dlmf 12.11.E9]
theorem pcfFirstZero_expansion (N : ℕ) :
    (fun μ : ℝ => (pcfDescendingZero (-μ^2/2) false 1/(Real.sqrt 2*μ):ℂ)-∑ j ∈ Finset.range N, pcfFirstZeroCoeff j*(μ:ℂ)^(-4*(j:ℂ)/3)) =O[atTop] (fun μ : ℝ => μ^(-4*(N:ℝ)/3)) := by
  sorry

/-- Structural facts about the coefficients of DLMF 12.11.9. The decimal values of the
coefficients printed there are numerical results and out of scope. -/
@[dlmf 12.11.E9]
theorem pcfFirstZero_coefficients :
    pcfFirstZeroCoeff 0 = 1 ∧ ∀ k : ℕ, (pcfFirstZeroCoeff k).im = 0 := by
  sorry

end DLMF.Confluent
