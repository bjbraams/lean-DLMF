/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.BetaEndpointBounds

/-!
# Incomplete Beta asymptotic expansions and inverse (DLMF §8.18)

## Main definitions

* `betaAuxF`, `Real.betaXi`, `Real.betaGeneratingCoeff`: the endpoint auxiliary functions, the
  endpoint variable and the generating coefficients, DLMF 8.18.2–8.18.7.
* `Real.betaCenter`, `Real.betaEta`, `betaSymmetricC`: the transition variable and coefficients
  of the symmetric case, DLMF 8.18.8–8.18.12.
* `Real.betaZeta`, `betaGeneralH`: the transition variable and coefficients of the general case,
  DLMF 8.18.15–8.18.17.
* `Real.incBetaInverse`: the inverse of the normalized incomplete Beta function, DLMF 8.18.18.

## Main results

* `incompleteBeta_large_a_fixed_x`, `incompleteBeta_large_a_integer_b_exact`: the fixed-argument
  expansion, DLMF 8.18.1.
* `betaAuxF_recurrence`, `betaAuxF_initial`, `Real.betaGenerating_hasSum`: DLMF 8.18.4–8.18.6.
* `incompleteBeta_large_a_uniform`: the uniform endpoint expansion, DLMF 8.18.3.
* `incompleteBeta_symmetric_uniform_expansion`: the symmetric uniform expansion, DLMF 8.18.9.
* `incompleteBeta_general_uniform_expansion`: the general uniform expansion, DLMF 8.18.14.
* `Real.incBetaInverse_spec`: DLMF 8.18.18.

## Implementation notes

Results already in Mathlib are referenced, not reproved. The fixed-argument expansion uses
finite diagonal shifts and a binomial-series majorant independent of the large positive
parameter.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
open DLMF.Core

namespace DLMF.Statistical

open DLMF.Confluent

/-- The endpoint expansion of the incomplete Beta function, DLMF 8.18.3, has remainder
`O(a^(-N) F₀)` as `a → ∞`, uniformly for `0 < x ≤ 1`, for fixed `b > 0` and positive
truncation order `N`. -/
@[dlmf 8.18.E3]
theorem incompleteBeta_large_a_uniform {b : ℝ} (hb : 0 < b) (N : ℕ) (hN : 1 ≤ N) :
    IsBigO (comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 ≤ 1})
        (fun p => Gamma p.1/Gamma (p.1+b)*regularizedIncompleteBeta p.1 b p.2-∑ k ∈ Finset.range N,
        Real.betaGeneratingCoeff b (Real.betaXi p.2) k*betaAuxF k p.1 b (Real.betaXi p.2))
        (fun p => (p.1 : ℂ)^(-(N : ℤ))*betaAuxF 0 p.1 b (Real.betaXi p.2)) := by
  exact DLMF.Confluent.incompleteBeta_large_a_uniform_of_pos_order hb hN

/-- The transition center x₀. -/
@[dlmf 8.18.E8]
def Real.betaCenter (a b : ℝ) : ℝ :=
  a/(a+b)

/-- The signed transition variable, continuous with η/(x-x₀)>0. -/
@[dlmf 8.18.E10]
def Real.betaEta (x₀ x : ℝ) : ℝ :=
  (if x < x₀ then -1 else 1)*Real.sqrt (-2*(x₀*Real.log (x/x₀)+(1-x₀)*Real.log ((1-x)/(1-x₀))))

/-- The real inverse of the monotone signed transition map. -/
def Real.betaEtaInverse (x₀ η : ℝ) : ℝ :=
  Classical.epsilon (fun x : ℝ => 0 < x ∧ x < 1 ∧ Real.betaEta x₀ x=η)

/-- Estimate under the stated parameter and domain assumptions: `-Real.betaEta x₀
x^2/2=x₀*Real.log (x/x₀)+(1-x₀)*Real.log ((1-x)/(1-x₀)) ∧ (x ≠ x₀ → 0 < Real.betaEta x₀
x/(x-x₀))`. -/
@[dlmf 8.18.E10]
theorem Real.betaEta_equation {x₀ x : ℝ} (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) (hx : 0 < x) (hx1 : x < 1) :
    -Real.betaEta x₀ x^2/2=x₀*Real.log (x/x₀)+(1-x₀)*Real.log ((1-x)/(1-x₀)) ∧
        (x ≠ x₀ → 0 < Real.betaEta x₀ x/(x-x₀)) := by
  set L := x₀*Real.log (x/x₀)+(1-x₀)*Real.log ((1-x)/(1-x₀)) with hL
  have h1 : 0 < x/x₀ := div_pos hx hx₀
  have h2 : 0 < (1-x)/(1-x₀) := div_pos (by linarith) (by linarith)
  have hsum : x₀*(x/x₀-1)+(1-x₀)*((1-x)/(1-x₀)-1) = 0 := by
    field_simp; ring
  have hLle : L ≤ 0 := by
    have e1 := Real.log_le_sub_one_of_pos h1
    have e2 := Real.log_le_sub_one_of_pos h2
    have : x₀*Real.log (x/x₀) ≤ x₀*(x/x₀-1) := mul_le_mul_of_nonneg_left e1 hx₀.le
    have : (1-x₀)*Real.log ((1-x)/(1-x₀)) ≤ (1-x₀)*((1-x)/(1-x₀)-1) :=
      mul_le_mul_of_nonneg_left e2 (by linarith)
    linarith
  have hsq : Real.betaEta x₀ x^2 = -2*L := by
    rw [Real.betaEta, mul_pow, Real.sq_sqrt (by linarith)]
    split_ifs <;> ring
  refine ⟨by rw [hsq]; ring, fun hne => ?_⟩
  have hLlt : L < 0 := by
    have hne1 : x/x₀ ≠ 1 := by
      intro h; apply hne; field_simp at h; linarith
    have e1 := Real.log_lt_sub_one_of_pos h1 hne1
    have e2 := Real.log_le_sub_one_of_pos h2
    have : x₀*Real.log (x/x₀) < x₀*(x/x₀-1) := mul_lt_mul_of_pos_left e1 hx₀
    have : (1-x₀)*Real.log ((1-x)/(1-x₀)) ≤ (1-x₀)*((1-x)/(1-x₀)-1) :=
      mul_le_mul_of_nonneg_left e2 (by linarith)
    linarith
  have hs : 0 < Real.sqrt (-2*L) := Real.sqrt_pos.mpr (by linarith)
  rw [Real.betaEta, ← hL]
  rcases lt_or_gt_of_ne hne with h | h
  · simp only [h, ↓reduceIte]
    exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  · simp only [not_lt.mpr h.le, ↓reduceIte]
    exact div_pos (by linarith) (by linarith)

/-- The radicand of the transition map is continuous on `(0,1)`. -/
theorem IncompleteBetaUniform.betaEta_sqrt_continuousOn {x₀ : ℝ} (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) :
    ContinuousOn (fun x : ℝ => Real.sqrt (-2*(x₀*Real.log (x/x₀)+(1-x₀)*Real.log ((1-x)/(1-x₀)))))
      (Ioo 0 1) := by
  refine Real.continuous_sqrt.comp_continuousOn (ContinuousOn.mul continuousOn_const ?_)
  refine ContinuousOn.add (continuousOn_const.mul ?_) (continuousOn_const.mul ?_)
  · exact Real.continuousOn_log.comp (continuousOn_id.div_const _) fun x hx =>
      (div_pos hx.1 hx₀).ne'
  · exact Real.continuousOn_log.comp ((continuousOn_const.sub continuousOn_id).div_const _)
      fun x hx => (div_pos (by linarith [hx.2]) (by linarith)).ne'

/-- Every real value is taken by the transition map on `(0,1)`. -/
theorem IncompleteBetaUniform.betaEta_exists {x₀ : ℝ} (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) (η : ℝ) :
    ∃ x : ℝ, 0 < x ∧ x < 1 ∧ Real.betaEta x₀ x = η := by
  set g : ℝ → ℝ := fun x => Real.sqrt (-2*(x₀*Real.log (x/x₀)+(1-x₀)*Real.log ((1-x)/(1-x₀))))
  have hg := IncompleteBetaUniform.betaEta_sqrt_continuousOn hx₀ hx₀1
  have hgx₀ : g x₀ = 0 := by simp [g, div_self hx₀.ne', div_self (show 1-x₀ ≠ 0 by linarith)]
  have hE : ∀ x, Real.betaEta x₀ x = (if x < x₀ then -1 else 1) * g x := fun x => rfl
  have hl0 : Real.log x₀ < 0 := Real.log_neg hx₀ hx₀1
  have hl1 : Real.log (1-x₀) < 0 := Real.log_neg (by linarith) (by linarith)
  rcases lt_trichotomy η 0 with hη | hη | hη
  · -- left branch
    set M : ℝ := (η^2-2*(1-x₀)*Real.log (1-x₀))/(2*x₀)+1
    have hM : 0 < M := by
      have : 0 ≤ (η^2-2*(1-x₀)*Real.log (1-x₀))/(2*x₀) := by
        apply div_nonneg _ (by linarith); nlinarith
      linarith
    set x₁ := x₀*Real.exp (-M)
    have he : Real.exp (-M) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hx₁0 : 0 < x₁ := by positivity
    have hx₁ : x₁ < x₀ := by nlinarith
    have hgx₁ : -η ≤ g x₁ := by
      have hq : Real.log (x₁/x₀) = -M := by
        rw [show x₁/x₀ = Real.exp (-M) by simp only [x₁]; field_simp]; exact Real.log_exp _
      have hr : Real.log ((1-x₁)/(1-x₀)) ≤ -Real.log (1-x₀) := by
        rw [Real.log_div (by linarith) (by linarith)]
        have : Real.log (1-x₁) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
        linarith
      have hrad : η^2 ≤ -2*(x₀*Real.log (x₁/x₀)+(1-x₀)*Real.log ((1-x₁)/(1-x₀))) := by
        rw [hq]
        have : (1-x₀)*Real.log ((1-x₁)/(1-x₀)) ≤ (1-x₀)*(-Real.log (1-x₀)) :=
          mul_le_mul_of_nonneg_left hr (by linarith)
        have hMx : 2*x₀*M = η^2-2*(1-x₀)*Real.log (1-x₀) + 2*x₀ := by
          simp only [M]; field_simp
        nlinarith
      calc -η = Real.sqrt (η^2) := by rw [Real.sqrt_sq_eq_abs, abs_of_neg hη]
        _ ≤ g x₁ := Real.sqrt_le_sqrt hrad
    have hc : ContinuousOn (fun x => -g x) (Icc x₁ x₀) :=
      (hg.mono fun x (hx : x ∈ Icc x₁ x₀) =>
          ⟨lt_of_lt_of_le hx₁0 hx.1, lt_of_le_of_lt hx.2 hx₀1⟩).neg
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hx₁.le hc
      (show η ∈ Icc (-g x₁) (-g x₀) by rw [hgx₀]; constructor <;> linarith)
    have hxx : x < x₀ := by
      rcases hx.2.lt_or_eq with h | h
      · exact h
      · simp only at hfx; rw [h, hgx₀] at hfx; linarith
    refine ⟨x, lt_of_lt_of_le hx₁0 hx.1, by linarith [hx.2], ?_⟩
    rw [hE]; simp only [hxx, ↓reduceIte]; simp only at hfx; linarith
  · subst hη
    exact ⟨x₀, hx₀, hx₀1, by rw [hE, hgx₀]; ring⟩
  · -- right branch
    set M : ℝ := (η^2-2*x₀*Real.log x₀)/(2*(1-x₀))+1
    have hM : 0 < M := by
      have : 0 ≤ (η^2-2*x₀*Real.log x₀)/(2*(1-x₀)) := by
        apply div_nonneg _ (by linarith); nlinarith
      linarith
    set x₁ := 1-(1-x₀)*Real.exp (-M)
    have he : Real.exp (-M) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hep : 0 < Real.exp (-M) := Real.exp_pos _
    have hx₁1 : x₁ < 1 := by have : 0 < (1-x₀)*Real.exp (-M) := by nlinarith
                             linarith
    have hx₁ : x₀ < x₁ := by nlinarith
    have hgx₁ : η ≤ g x₁ := by
      have hq : Real.log ((1-x₁)/(1-x₀)) = -M := by
        rw [show (1-x₁)/(1-x₀) = Real.exp (-M) by simp only [x₁]; field_simp; ring];
            exact Real.log_exp _
      have hr : Real.log (x₁/x₀) ≤ -Real.log x₀ := by
        rw [Real.log_div (by linarith) (by linarith)]
        have : Real.log x₁ ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
        linarith
      have hrad : η^2 ≤ -2*(x₀*Real.log (x₁/x₀)+(1-x₀)*Real.log ((1-x₁)/(1-x₀))) := by
        rw [hq]
        have : x₀*Real.log (x₁/x₀) ≤ x₀*(-Real.log x₀) := mul_le_mul_of_nonneg_left hr hx₀.le
        have hMx : 2*(1-x₀)*M = η^2-2*x₀*Real.log x₀ + 2*(1-x₀) := by
          simp only [M]; field_simp
        nlinarith
      calc η = Real.sqrt (η^2) := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hη]
        _ ≤ g x₁ := Real.sqrt_le_sqrt hrad
    have hc : ContinuousOn g (Icc x₀ x₁) :=
      hg.mono fun x (hx : x ∈ Icc x₀ x₁) => ⟨lt_of_lt_of_le hx₀ hx.1, lt_of_le_of_lt hx.2 hx₁1⟩
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hx₁.le hc
      (show η ∈ Icc (g x₀) (g x₁) by rw [hgx₀]; constructor <;> linarith)
    refine ⟨x, lt_of_lt_of_le hx₀ hx.1, lt_of_le_of_lt hx.2 hx₁1, ?_⟩
    rw [hE]; simp only [not_lt.mpr hx.1, ↓reduceIte, one_mul]; exact hfx

/-- Estimate under the stated parameter and domain assumptions: `0 < Real.betaEtaInverse x₀ η ∧
Real.betaEtaInverse x₀ η < 1 ∧ Real.betaEta x₀ (Real.betaEtaInverse x₀ η)=η`. -/
@[dlmf 8.18.E10]
theorem Real.betaEtaInverse_spec {x₀ : ℝ} (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) (η : ℝ) :
    0 < Real.betaEtaInverse x₀ η ∧ Real.betaEtaInverse x₀ η < 1 ∧
        Real.betaEta x₀ (Real.betaEtaInverse x₀ η)=η := by
  exact Classical.epsilon_spec (IncompleteBetaUniform.betaEta_exists hx₀ hx₀1 η)

/-- The symmetric coefficients c_k(η), with x₀ retained as a parameter. -/
def betaSymmetricC (k : ℕ) (x₀ η : ℝ) : ℂ :=
  (-1 : ℂ)^k*asymptoticCoeff
      (fun t : ℝ => let x := Real.betaEtaInverse x₀ η;
      Real.sqrt (2*π*t)*Real.exp
      (t*η^2/2)*(regularizedIncompleteBeta (t*x₀) (t*(1-x₀)) x-DLMF.Confluent.erfc
          (-η*Real.sqrt (t/2))/2)) k

/-- Identity under the stated parameter and domain assumptions: `betaSymmetricC 0 x₀
η=(1/η-Real.sqrt (x₀*(1-x₀))/(Real.betaEtaInverse x₀ η-x₀) : ℝ)`. -/
@[dlmf 8.18.E11]
theorem betaSymmetricC_first {x₀ η : ℝ} (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) (hη : η ≠ 0) :
    betaSymmetricC 0 x₀ η=(1/η-Real.sqrt (x₀*(1-x₀))/(Real.betaEtaInverse x₀ η-x₀) : ℝ) := by
  sorry

/-- Identity under the stated parameter and domain assumptions: `betaSymmetricC 0 x₀
0=((1-2*x₀)/(3*Real.sqrt (x₀*(1-x₀))) : ℝ)`. -/
@[dlmf 8.18.E12]
theorem betaSymmetricC_at_zero {x₀ : ℝ} (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) :
    betaSymmetricC 0 x₀ 0=((1-2*x₀)/(3*Real.sqrt (x₀*(1-x₀))) : ℝ) := by
  sorry

/-- The removable singularities of all c_k at η=0. -/
theorem betaSymmetricC_analytic (k : ℕ) {x₀ : ℝ} (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) :
    AnalyticAt ℝ (betaSymmetricC k x₀) 0 := by
  sorry

/-- Uniform Gaussian expansion of the symmetric incomplete Beta function as the shape parameter
grows, away from both endpoint parameters. -/
@[dlmf 8.18.E9]
theorem incompleteBeta_symmetric_uniform_expansion {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1/2) (N : ℕ) :
    IsBigO (comap (fun p : ℝ × ℝ × ℝ => p.1) atTop ⊓ 𝓟
        {p : ℝ × ℝ × ℝ | 0 < p.1 ∧ δ ≤ p.2.1 ∧ p.2.1 ≤ 1-δ ∧ 0 < p.2.2 ∧ p.2.2 < 1})
        (fun p => let η := Real.betaEta p.2.1 p.2.2;
        Real.sqrt (2*π*p.1)*Real.exp
        (p.1*η^2/2)*(regularizedIncompleteBeta (p.1*p.2.1) (p.1*(1-p.2.1)) p.2.2-DLMF.Confluent.erfc
        (-η*Real.sqrt (p.1/2))/2)-∑ k ∈ Finset.range N,
        (-1 : ℂ)^k*betaSymmetricC k p.2.1 η/(p.1 : ℂ)^k) (fun p => p.1^(-(N : ℤ))) := by
  sorry

/-- The general-case transition variable ζ with its required branch. -/
@[dlmf 8.18.E15]
def Real.betaZeta (μ x : ℝ) : ℝ :=
  if x=1/(1+μ) then μ else
      Classical.epsilon (fun ζ : ℝ => 0 < ζ ∧
      μ*Real.log ζ-ζ=Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log (1+μ)-μ ∧ 0 < (ζ-μ)/(1/(1+μ)-x))

/-- The inverse real transition map. -/
def Real.betaGeneralX (μ ζ : ℝ) : ℝ :=
  if ζ=μ then 1/(1+μ) else
      Classical.epsilon (fun x : ℝ => 0 < x ∧ x < 1 ∧
      μ*Real.log ζ-ζ=Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log (1+μ)-μ ∧ 0 < (ζ-μ)/(1/(1+μ)-x))

/-- `ζ ↦ μ log ζ - ζ` increases strictly on `(0, μ]`. -/
theorem IncompleteBetaUniform.betaPhi_strictMonoOn (μ : ℝ) :
    StrictMonoOn (fun ζ : ℝ => μ*Real.log ζ-ζ) (Ioc 0 μ) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioc 0 μ) ?_ ?_
  · intro ζ hζ
    exact ((continuousAt_const.mul (Real.continuousAt_log hζ.1.ne')).sub
      continuousAt_id).continuousWithinAt
  · intro ζ hζ
    rw [interior_Ioc] at hζ
    have hd : HasDerivAt (fun ζ : ℝ => μ*Real.log ζ-ζ) (μ*ζ⁻¹-1) ζ :=
      ((Real.hasDerivAt_log hζ.1.ne').const_mul μ).sub (hasDerivAt_id ζ)
    rw [hd.deriv, sub_pos, ← div_eq_mul_inv, one_lt_div hζ.1]; exact hζ.2

/-- `ζ ↦ μ log ζ - ζ` decreases strictly on `[μ, ∞)`. -/
theorem IncompleteBetaUniform.betaPhi_strictAntiOn {μ : ℝ} (hμ : 0 < μ) :
    StrictAntiOn (fun ζ : ℝ => μ*Real.log ζ-ζ) (Ici μ) := by
  refine strictAntiOn_of_deriv_neg (convex_Ici μ) ?_ ?_
  · intro ζ hζ
    exact ((continuousAt_const.mul (Real.continuousAt_log (by
      have : μ ≤ ζ := hζ; linarith : (0:ℝ) < ζ).ne')).sub continuousAt_id).continuousWithinAt
  · intro ζ hζ
    rw [interior_Ici] at hζ
    have hζ0 : 0 < ζ := hμ.trans hζ
    have hd : HasDerivAt (fun ζ : ℝ => μ*Real.log ζ-ζ) (μ*ζ⁻¹-1) ζ :=
      ((Real.hasDerivAt_log hζ0.ne').const_mul μ).sub (hasDerivAt_id ζ)
    rw [hd.deriv, sub_neg, ← div_eq_mul_inv, div_lt_one hζ0]; exact hζ

/-- At `x`, the function `(fun x : ℝ => Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log (1+μ)-μ)` has
derivative `(x⁻¹ - μ*(1-x)⁻¹)`. -/
theorem IncompleteBetaUniform.betaR_hasDerivAt {μ x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun x : ℝ => Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log (1+μ)-μ)
      (x⁻¹ - μ*(1-x)⁻¹) x := by
  have h1 := Real.hasDerivAt_log hx.ne'
  have h2 := ((hasDerivAt_id x).const_sub 1).log (by simp; linarith)
  have := ((h1.add (h2.const_mul μ)).add_const ((1+μ)*Real.log (1+μ))).sub_const μ
  convert this using 1
  · funext y; simp only [Pi.add_apply, id]
  · simp only [id]; rw [neg_div, one_div]; ring

/-- The function `(fun x : ℝ => Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log (1+μ)-μ)` is continuous
at `x`. -/
theorem IncompleteBetaUniform.betaR_continuousAt {μ x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    ContinuousAt (fun x : ℝ => Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log (1+μ)-μ) x :=
  (IncompleteBetaUniform.betaR_hasDerivAt hx hx1).continuousAt

/-- `R` increases strictly on `(0, 1/(1+μ)]`. -/
theorem IncompleteBetaUniform.betaR_strictMonoOn {μ : ℝ} (hμ : 0 < μ) :
    StrictMonoOn (fun x : ℝ => Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log (1+μ)-μ)
      (Ioc 0 (1/(1+μ))) := by
  have hx0 : 1/(1+μ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  refine strictMonoOn_of_deriv_pos (convex_Ioc _ _) ?_ ?_
  · intro x hx
    exact (IncompleteBetaUniform.betaR_continuousAt hx.1 (hx.2.trans_lt hx0)).continuousWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    have h1 : x < 1 := hx.2.trans hx0
    rw [(IncompleteBetaUniform.betaR_hasDerivAt hx.1 h1).deriv]
    have hlt : x*(1+μ) < 1 := by have h := hx.2; rw [lt_div_iff₀ (by linarith)] at h; linarith
    have : 0 < 1 - x := by linarith
    rw [sub_pos, ← div_eq_mul_inv, ← one_div, div_lt_div_iff₀ this hx.1]; nlinarith

/-- `R` decreases strictly on `[1/(1+μ), 1)`. -/
theorem IncompleteBetaUniform.betaR_strictAntiOn {μ : ℝ} (hμ : 0 < μ) :
    StrictAntiOn (fun x : ℝ => Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log (1+μ)-μ)
      (Ico (1/(1+μ)) 1) := by
  have hx0 : 0 < 1/(1+μ) := by positivity
  refine strictAntiOn_of_deriv_neg (convex_Ico _ _) ?_ ?_
  · intro x hx
    exact (IncompleteBetaUniform.betaR_continuousAt (hx0.trans_le hx.1) hx.2).continuousWithinAt
  · intro x hx
    rw [interior_Ico] at hx
    have h0 : 0 < x := hx0.trans hx.1
    rw [(IncompleteBetaUniform.betaR_hasDerivAt h0 hx.2).deriv]
    have hgt : 1 < x*(1+μ) := by have h := hx.1; rw [div_lt_iff₀ (by linarith)] at h; linarith
    have : 0 < 1 - x := by linarith [hx.2]
    rw [sub_neg, ← div_eq_mul_inv, ← one_div, div_lt_div_iff₀ h0 this]; nlinarith

/-- The two sides agree at the turning points. -/
theorem IncompleteBetaUniform.betaR_turning {μ : ℝ} (hμ : 0 < μ) :
    Real.log (1/(1+μ))+μ*Real.log (1-1/(1+μ))+(1+μ)*Real.log (1+μ)-μ = μ*Real.log μ-μ := by
  have h1 : (1:ℝ) - 1/(1+μ) = μ/(1+μ) := by field_simp; ring
  rw [h1, one_div, Real.log_inv, Real.log_div hμ.ne' (by linarith)]; ring

/-- Existence of the transition variable on the correct side. -/
theorem IncompleteBetaUniform.betaZeta_exists {μ x : ℝ} (hμ : 0 < μ) (hx : 0 < x) (hx1 : x < 1)
    (hne : x ≠ 1/(1+μ)) :
    ∃ ζ : ℝ, 0 < ζ ∧ μ*Real.log ζ-ζ=Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log (1+μ)-μ ∧
      0 < (ζ-μ)/(1/(1+μ)-x) := by
  set R := Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log (1+μ)-μ with hR
  have hx0 : 0 < 1/(1+μ) := by positivity
  have hx01 : 1/(1+μ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hRlt : R < μ*Real.log μ-μ := by
    rw [← IncompleteBetaUniform.betaR_turning hμ]
    rcases lt_or_gt_of_ne hne with h | h
    · exact IncompleteBetaUniform.betaR_strictMonoOn hμ ⟨hx, h.le⟩ ⟨hx0, le_rfl⟩ h
    · exact IncompleteBetaUniform.betaR_strictAntiOn hμ ⟨le_rfl, hx01⟩ ⟨h.le, hx1⟩ h
  rcases lt_or_gt_of_ne hne with h | h
  · -- ζ > μ
    set s : ℝ := 2*μ + |R| + 1
    have hs : 0 < s := by positivity
    have hμs : μ ≤ s^2 := by nlinarith [abs_nonneg R]
    have hφs : μ*Real.log (s^2) - s^2 ≤ R := by
      have hl : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs
      rw [Real.log_pow]; push_cast
      have : -|R| ≤ R := neg_abs_le R
      nlinarith [abs_nonneg R]
    have hcont : ContinuousOn (fun ζ : ℝ => μ*Real.log ζ-ζ) (Icc μ (s^2)) := fun ζ hζ =>
      ((continuousAt_const.mul (Real.continuousAt_log (by linarith [hζ.1] : (0:ℝ) < ζ).ne')).sub
        continuousAt_id).continuousWithinAt
    obtain ⟨ζ, hζ, hζR⟩ := intermediate_value_Icc' hμs hcont ⟨hφs, hRlt.le⟩
    have hζμ : ζ ≠ μ := by rintro rfl; simp only at hζR; linarith
    have hgt : μ < ζ := lt_of_le_of_ne hζ.1 (Ne.symm hζμ)
    exact ⟨ζ, hμ.trans hgt, hζR, div_pos (by linarith) (by linarith)⟩
  · -- ζ < μ
    set e : ℝ := Real.exp (R/μ)
    have he : 0 < e := Real.exp_pos _
    have heμ : e < μ := by
      rw [← Real.exp_log hμ]; refine Real.exp_lt_exp.mpr ?_
      rw [div_lt_iff₀ hμ]; nlinarith
    have hφe : μ*Real.log e - e ≤ R := by
      rw [Real.log_exp]; field_simp; linarith
    have hcont : ContinuousOn (fun ζ : ℝ => μ*Real.log ζ-ζ) (Icc e μ) := fun ζ hζ =>
      ((continuousAt_const.mul (Real.continuousAt_log (by linarith [hζ.1] : (0:ℝ) < ζ).ne')).sub
        continuousAt_id).continuousWithinAt
    obtain ⟨ζ, hζ, hζR⟩ := intermediate_value_Icc heμ.le hcont ⟨hφe, hRlt.le⟩
    have hζμ : ζ ≠ μ := by rintro rfl; simp only at hζR; linarith
    have hlt : ζ < μ := lt_of_le_of_ne hζ.2 hζμ
    exact ⟨ζ, he.trans_le hζ.1, hζR, div_pos_of_neg_of_neg (by linarith) (by linarith)⟩

/-- Estimate under the stated parameter and domain assumptions: `0 < Real.betaZeta μ x ∧
μ*Real.log (Real.betaZeta μ x)-Real.betaZeta μ x=Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log
(1+μ)-μ ∧ Real.betaGeneralX μ (Real.betaZeta μ x)=x ∧ (x ≠ 1/(1+μ) → 0 < (Real.betaZeta μ
x-μ)/(1/(1+μ)-x))`. -/
theorem IncompleteBetaUniform.betaZeta_spec {μ x : ℝ} (hμ : 0 < μ) (hx : 0 < x) (hx1 : x < 1) :
    0 < Real.betaZeta μ x ∧
        μ*Real.log (Real.betaZeta μ x)-Real.betaZeta μ x=Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log
        (1+μ)-μ ∧ Real.betaGeneralX μ (Real.betaZeta μ x)=x ∧
        (x ≠ 1/(1+μ) → 0 < (Real.betaZeta μ x-μ)/(1/(1+μ)-x)) := by
  have hx0 : 0 < 1/(1+μ) := by positivity
  have hx01 : 1/(1+μ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  by_cases hne : x = 1/(1+μ)
  · have hz : Real.betaZeta μ x = μ := by simp [Real.betaZeta, hne]
    rw [hz]
    refine ⟨hμ, ?_, by simp [Real.betaGeneralX, hne], fun h => absurd hne h⟩
    rw [hne, IncompleteBetaUniform.betaR_turning hμ]
  have hspec := Classical.epsilon_spec (IncompleteBetaUniform.betaZeta_exists hμ hx hx1 hne)
  have hz : Real.betaZeta μ x =
      Classical.epsilon (fun ζ : ℝ => 0 < ζ ∧
      μ*Real.log ζ-ζ=Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log (1+μ)-μ ∧ 0 <
      (ζ-μ)/(1/(1+μ)-x)) := by
    simp only [Real.betaZeta, hne, ↓reduceIte]
  rw [← hz] at hspec
  obtain ⟨hζ0, hζR, hsign⟩ := hspec
  set ζ := Real.betaZeta μ x
  refine ⟨hζ0, hζR, ?_, fun _ => hsign⟩
  have hζμ : ζ ≠ μ := by rintro h; rw [h, sub_self, zero_div] at hsign; exact lt_irrefl _ hsign
  have hX : Real.betaGeneralX μ ζ =
      Classical.epsilon (fun x : ℝ => 0 < x ∧ x < 1 ∧
      μ*Real.log ζ-ζ=Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log (1+μ)-μ ∧ 0 <
      (ζ-μ)/(1/(1+μ)-x)) := by
    simp only [Real.betaGeneralX, hζμ, ↓reduceIte]
  have hex : ∃ y : ℝ, 0 < y ∧ y < 1 ∧
      μ*Real.log ζ-ζ=Real.log y+μ*Real.log (1-y)+(1+μ)*Real.log (1+μ)-μ ∧ 0 < (ζ-μ)/(1/(1+μ)-y) :=
    ⟨x, hx, hx1, hζR, hsign⟩
  obtain ⟨hy0, hy1, hyR, hysign⟩ := Classical.epsilon_spec hex
  rw [hX]
  set y := Classical.epsilon
      (fun x : ℝ => 0 < x ∧ x < 1 ∧
      μ*Real.log ζ-ζ=Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log (1+μ)-μ ∧ 0 < (ζ-μ)/(1/(1+μ)-x))
  have hRR : (fun x : ℝ => Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log (1+μ)-μ) y =
      (fun x : ℝ => Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log (1+μ)-μ) x := by
    simp only; rw [← hyR, hζR]
  rcases div_pos_iff.mp hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h2' : 0 < 1/(1+μ) - y := by
      rcases div_pos_iff.mp hysign with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · linarith
    exact (IncompleteBetaUniform.betaR_strictMonoOn hμ).injOn ⟨hy0, by linarith⟩
        ⟨hx, by linarith⟩ hRR
  · have h2' : 1/(1+μ) - y < 0 := by
      rcases div_pos_iff.mp hysign with ⟨h, _⟩ | ⟨_, h⟩
      · linarith
      · exact h
    exact (IncompleteBetaUniform.betaR_strictAntiOn hμ).injOn ⟨by linarith, hy1⟩
        ⟨by linarith, hx1⟩ hRR

/-- Estimate under the stated parameter and domain assumptions: `0 < Real.betaZeta μ x ∧
μ*Real.log (Real.betaZeta μ x)-Real.betaZeta μ x=Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log
(1+μ)-μ ∧ Real.betaGeneralX μ (Real.betaZeta μ x)=x ∧ (x ≠ 1/(1+μ) → 0 < (Real.betaZeta μ
x-μ)/(1/(1+μ)-x))`. -/
@[dlmf 8.18.E15]
theorem Real.betaZeta_spec {μ x : ℝ} (hμ : 0 < μ) (hx : 0 < x) (hx1 : x < 1) :
    0 < Real.betaZeta μ x ∧
        μ*Real.log (Real.betaZeta μ x)-Real.betaZeta μ x=Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log
        (1+μ)-μ ∧ Real.betaGeneralX μ (Real.betaZeta μ x)=x ∧
        (x ≠ 1/(1+μ) → 0 < (Real.betaZeta μ x-μ)/(1/(1+μ)-x)) :=
  IncompleteBetaUniform.betaZeta_spec hμ hx hx1

/-- The general coefficients h_k(ζ,μ) extracted from the exact normalized remainder. -/
def betaGeneralH (k : ℕ) (ζ μ : ℝ) : ℂ :=
  asymptoticCoeff (fun a : ℝ => let x := Real.betaGeneralX μ ζ; let x₀ := 1/(1+μ);
      -gammaScaled (a*μ)*Real.sqrt (2*π*a*μ)*Real.exp
      (-a*Real.log (x/x₀)-a*μ*Real.log ((1-x)/(1-x₀)))*(regularizedIncompleteBeta a (a*μ)
      x-regularizedIncompleteGammaQ (a*μ) (a*ζ))) k

/-- Identity under the stated parameter and domain assumptions: `betaGeneralH 0 ζ
μ=(μ*(1/(ζ-μ)-(1+μ)^(-3/2 : ℝ)/(1/(1+μ)-Real.betaGeneralX μ ζ)) : ℝ)`. -/
@[dlmf 8.18.E16]
theorem betaGeneralH_first {μ ζ : ℝ} (hμ : 0 < μ) (hζ : 0 < ζ) (hζμ : ζ ≠ μ) :
    betaGeneralH 0 ζ μ=(μ*(1/(ζ-μ)-(1+μ)^(-3/2 : ℝ)/(1/(1+μ)-Real.betaGeneralX μ ζ)) : ℝ) := by
  sorry

/-- Identity under the stated parameter and domain assumptions: `betaGeneralH 0 μ
μ=(((1-μ)/Real.sqrt (1+μ)-1)/3 : ℝ)`. -/
@[dlmf 8.18.E17]
theorem betaGeneralH_at_transition {μ : ℝ} (hμ : 0 < μ) :
    betaGeneralH 0 μ μ=(((1-μ)/Real.sqrt (1+μ)-1)/3 : ℝ) := by
  sorry

/-- All general-case coefficient singularities at ζ=μ are removable. -/
theorem betaGeneralH_analytic (k : ℕ) {μ : ℝ} (hμ : 0 < μ) :
    AnalyticAt ℝ (fun ζ => betaGeneralH k ζ μ) μ := by
  sorry

/-- Uniform normalized remainder with the natural sqrt(1+b/a) coefficient-growth envelope. -/
@[dlmf 8.18.E14]
theorem incompleteBeta_general_uniform_expansion (N : ℕ) :
    IsBigO (comap (fun p : ℝ × ℝ × ℝ => p.1) atTop ⊓ 𝓟
        {p : ℝ × ℝ × ℝ | 0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2 ∧ p.2.2 < 1})
        (fun p => let μ := p.2.1/p.1; let x₀ := 1/(1+μ); let ζ := Real.betaZeta μ p.2.2;
        -gammaScaled p.2.1*Real.sqrt (2*π*p.2.1)*Real.exp
        (-p.1*Real.log (p.2.2/x₀)-p.2.1*Real.log
            ((1-p.2.2)/(1-x₀)))*(regularizedIncompleteBeta p.1 p.2.1
        p.2.2-regularizedIncompleteGammaQ p.2.1 (p.1*ζ))-∑ k ∈ Finset.range N,
        betaGeneralH k ζ μ/(p.1 : ℂ)^k) (fun p => p.1^(-(N : ℤ))*Real.sqrt (1+p.2.1/p.1)) := by
  sorry

/-- Inverse of normalized incomplete Beta on [0,1]. -/
@[dlmf 8.18.E18]
def Real.incBetaInverse (a b p : ℝ) : ℝ :=
  if p=0 then 0 else if p=1 then 1 else
      Classical.epsilon (fun x : ℝ => x ∈ Icc (0 : ℝ) 1 ∧ (regularizedIncompleteBeta a b x).re=p)

/-- For real positive parameters, `x ↦ Re I_x(a,b)` takes every value of `[0,1]` on `[0,1]`. -/
theorem IncompleteBetaUniform.exists_regularizedIncompleteBeta_eq {a b p : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hp : 0 ≤ p)
    (hp1 : p ≤ 1) :
    ∃ x ∈ Icc (0:ℝ) 1, (Real.regularizedIncompleteBeta a b x).re = p := by
  have ha' : 0 < (a:ℂ).re := by simpa using ha
  have hb' : 0 < (b:ℂ).re := by simpa using hb
  set f : ℝ → ℝ := fun x => (Real.regularizedIncompleteBeta a b x).re
  have hc : ContinuousOn f (Icc 0 1) := by
    have hi : IntegrableOn (fun t : ℝ => (t : ℂ) ^ ((a:ℂ) - 1) * (1 - (t : ℂ)) ^ ((b:ℂ) - 1))
        (uIcc 0 1) := by
      have := betaIntegral_convergent ha' hb'
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one] at this
      simpa [uIcc_of_le zero_le_one] using this
    have := intervalIntegral.continuousOn_primitive_interval hi
    rw [uIcc_of_le zero_le_one] at this
    exact Complex.continuous_re.comp_continuousOn (this.div_const _)
  have h0 : f 0 = 0 := by simp [f, Real.regularizedIncompleteBeta, Real.incompleteBeta_zero]
  have h1 : f 1 = 1 := by simp [f, Real.regularizedIncompleteBeta_one ha' hb']
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc zero_le_one hc
    (show p ∈ Icc (f 0) (f 1) by rw [h0, h1]; exact ⟨hp, hp1⟩)
  exact ⟨x, hx, hfx⟩

/-- Formula under the stated hypotheses: `Real.incBetaInverse a b p ∈ Icc (0 : ℝ) 1 ∧
(regularizedIncompleteBeta a b (Real.incBetaInverse a b p)).re=p`. -/
@[dlmf 8.18.E18]
theorem Real.incBetaInverse_spec {a b p : ℝ} (ha : 0 < a) (hb : 0 < b) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.incBetaInverse a b p ∈ Icc (0 : ℝ) 1 ∧
        (regularizedIncompleteBeta a b (Real.incBetaInverse a b p)).re=p := by
  rcases hp.eq_or_lt with h0 | h0
  · subst h0
    simp [Real.incBetaInverse, Real.regularizedIncompleteBeta, Real.incompleteBeta_zero]
  rcases hp1.eq_or_lt with h1 | h1
  · subst h1
    simp [Real.incBetaInverse,
        Real.regularizedIncompleteBeta_one (a := (a:ℂ)) (b := (b:ℂ)) (by simpa using ha)
      (by simpa using hb)]
  have hs := Classical.epsilon_spec
      (IncompleteBetaUniform.exists_regularizedIncompleteBeta_eq ha hb hp hp1)
  simp only [Real.incBetaInverse, h0.ne', h1.ne, ite_false]
  exact hs

end DLMF.Statistical
