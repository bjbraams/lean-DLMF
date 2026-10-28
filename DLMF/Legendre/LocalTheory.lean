/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Zeros

/-!
# Singular exponents and independence of Legendre solutions

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Legendre

/-- Normalized first-derivative coefficient of the associated Legendre equation. -/
def legendreEquationP (z : ℂ) : ℂ :=
  -2*z/(1-z^2)

/-- Normalized zeroth-derivative coefficient. -/
def legendreEquationQ (ν μ z : ℂ) : ℂ :=
  (ν*(ν+1)-μ^2/(1-z^2))/(1-z^2)

/-- Regular singularity and the exponent pair minus/plus order over two, DLMF 14.2(iii). -/
theorem legendre_finite_singular_exponents_1 (ν μ : ℂ) :
    Tendsto (fun z : ℂ => (z-1)*legendreEquationP z) (𝓝[≠] (1:ℂ)) (𝓝 1) ∧ Tendsto (fun z : ℂ => (z-1)^2*legendreEquationQ ν μ z) (𝓝[≠] (1:ℂ)) (𝓝 (-μ^2/4)) ∧ ∀ r : ℂ, r*(r-1)+r-μ^2/4=(r-μ/2)*(r+μ/2) := by
  have hev : ∀ᶠ z in 𝓝[≠] (1:ℂ), z ≠ 1 ∧ z + 1 ≠ 0 := by
    have h1 : ∀ᶠ z in 𝓝 (1:ℂ), z + 1 ≠ 0 :=
      (continuous_id.add continuous_const).continuousAt.eventually_ne (by norm_num)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds h1] with z hz h2 using ⟨hz, h2⟩
  refine ⟨?_, ?_, fun r => by ring⟩
  · have heq : (fun z : ℂ => (z-1)*legendreEquationP z) =ᶠ[𝓝[≠] 1] (fun z => 2*z/(1+z)) := by
      filter_upwards [hev] with z ⟨hz1, hz2⟩
      have : z - 1 ≠ 0 := sub_ne_zero.2 hz1
      have h3 : 1 + z ≠ 0 := by rwa [add_comm]
      rw [legendreEquationP, show (1:ℂ) - z^2 = -(z-1)*(1+z) by ring]
      field_simp
    apply Tendsto.congr' heq.symm
    have := (by fun_prop (disch := norm_num) : ContinuousAt (fun z : ℂ => 2*z/(1+z)) 1).tendsto
    norm_num at this
    exact this.mono_left nhdsWithin_le_nhds
  · have heq : (fun z : ℂ => (z-1)^2*legendreEquationQ ν μ z) =ᶠ[𝓝[≠] 1]
        (fun z => (ν*(ν+1)*(1-z^2)-μ^2)/(1+z)^2) := by
      filter_upwards [hev] with z ⟨hz1, hz2⟩
      have : z - 1 ≠ 0 := sub_ne_zero.2 hz1
      have h3 : 1 + z ≠ 0 := by rwa [add_comm]
      rw [legendreEquationQ, show (1:ℂ) - z^2 = -(z-1)*(1+z) by ring]
      field_simp
      ring
    apply Tendsto.congr' heq.symm
    have := (by fun_prop (disch := norm_num) : ContinuousAt (fun z : ℂ => (ν*(ν+1)*(1-z^2)-μ^2)/(1+z)^2) 1).tendsto
    norm_num at this
    exact this.mono_left nhdsWithin_le_nhds

/-- Regular singularity and the exponent pair minus/plus order over two, DLMF 14.2(iii). -/
theorem legendre_finite_singular_exponents_2 (ν μ : ℂ) :
    Tendsto (fun z : ℂ => (z-(-1))*legendreEquationP z) (𝓝[≠] (-1:ℂ)) (𝓝 1) ∧ Tendsto (fun z : ℂ => (z-(-1))^2*legendreEquationQ ν μ z) (𝓝[≠] (-1:ℂ)) (𝓝 (-μ^2/4)) ∧ ∀ r : ℂ, r*(r-1)+r-μ^2/4=(r-μ/2)*(r+μ/2) := by
  have hev : ∀ᶠ z in 𝓝[≠] (-1:ℂ), z ≠ -1 ∧ 1 - z ≠ 0 := by
    have h1 : ∀ᶠ z in 𝓝 (-1:ℂ), 1 - z ≠ 0 :=
      (continuous_const.sub continuous_id).continuousAt.eventually_ne (by norm_num)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds h1] with z hz h2 using ⟨hz, h2⟩
  refine ⟨?_, ?_, fun r => by ring⟩
  · have heq : (fun z : ℂ => (z-(-1))*legendreEquationP z) =ᶠ[𝓝[≠] (-1)] (fun z => -(2*z)/(1-z)) := by
      filter_upwards [hev] with z ⟨hz1, hz2⟩
      have : z + 1 ≠ 0 := by intro h; apply hz1; linear_combination h
      rw [legendreEquationP, show (1:ℂ) - z^2 = (1-z)*(z+1) by ring, sub_neg_eq_add]
      field_simp
    apply Tendsto.congr' heq.symm
    have := (by fun_prop (disch := norm_num) : ContinuousAt (fun z : ℂ => -(2*z)/(1-z)) (-1)).tendsto
    norm_num at this
    exact this.mono_left nhdsWithin_le_nhds
  · have heq : (fun z : ℂ => (z-(-1))^2*legendreEquationQ ν μ z) =ᶠ[𝓝[≠] (-1)]
        (fun z => (ν*(ν+1)*(1-z^2)-μ^2)/(1-z)^2) := by
      filter_upwards [hev] with z ⟨hz1, hz2⟩
      have : z + 1 ≠ 0 := by intro h; apply hz1; linear_combination h
      rw [legendreEquationQ, show (1:ℂ) - z^2 = (1-z)*(z+1) by ring, sub_neg_eq_add]
      field_simp
    apply Tendsto.congr' heq.symm
    have := (by fun_prop (disch := norm_num) : ContinuousAt (fun z : ℂ => (ν*(ν+1)*(1-z^2)-μ^2)/(1-z)^2) (-1)).tendsto
    norm_num at this
    exact this.mono_left nhdsWithin_le_nhds

/-- Reciprocal-coordinate equation has exponents minus degree and degree plus one at infinity. -/
theorem legendre_infinite_singular_exponents (ν μ : ℂ) :
    Tendsto (fun t : ℂ => t*(2*t/(t^2-1))) (𝓝[≠] 0) (𝓝 0) ∧ Tendsto (fun t : ℂ => t^2*(ν*(ν+1)/(t^2*(t^2-1))-μ^2/(t^2-1)^2)) (𝓝[≠] 0) (𝓝 (-ν*(ν+1))) ∧ ∀ r : ℂ, r*(r-1)-ν*(ν+1)=(r+ν)*(r-ν-1) := by
  constructor
  · simpa using (by fun_prop (disch := norm_num) : ContinuousAt (fun t : ℂ => t*(2*t/(t^2-1))) 0).tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0:ℂ) ≤ 𝓝 (0:ℂ))
  · constructor
    · have heq : (fun t : ℂ => t^2*(ν*(ν+1)/(t^2*(t^2-1))-μ^2/(t^2-1)^2)) =ᶠ[𝓝[≠] 0]
          (fun t => ν*(ν+1)/(t^2-1)-t^2*μ^2/(t^2-1)^2) := by
        filter_upwards [self_mem_nhdsWithin] with t ht
        have ht0 : t ≠ 0 := ht
        field_simp
      apply Tendsto.congr' heq.symm
      simpa [div_neg] using (by fun_prop (disch := norm_num) : ContinuousAt (fun t : ℂ => ν*(ν+1)/(t^2-1)-t^2*μ^2/(t^2-1)^2) 0).tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0:ℂ) ≤ 𝓝 (0:ℂ))
    · intro r; ring

/-- The reflected first-kind pair is dependent exactly at the exceptional parameters in DLMF 14.2(iii). -/
theorem ferrersP_reflected_dependence (ν μ : ℂ) :
    (∃ A B : ℂ, (A ≠ 0 ∨ B ≠ 0) ∧ ∀ x ∈ Ioo (-1:ℝ) 1, A*ferrersP ν (-μ) x+B*ferrersP ν (-μ) (-x)=0) ↔ (∃ n : ℕ, μ-ν=-n) ∨ (∃ n : ℕ, μ+ν=-(n+1)) := by
  set α : ℂ := 2^(-μ)*π*((Gamma ((1-ν+μ)/2))⁻¹*(Gamma ((ν+μ+2)/2))⁻¹) with hα
  set β : ℂ := 2^(-μ)*π*((Gamma ((μ-ν)/2))⁻¹*(Gamma ((ν+μ+1)/2))⁻¹) with hβ
  have hf : EqOn (ferrersP ν (-μ)) (fun y => α*ferrersEven ν μ y + -β*ferrersOdd ν μ y)
      (Ioo (-1:ℝ) 1) := ferrersP_neg_eqOn_even_odd ν μ
  have hg : EqOn (fun x => ferrersP ν (-μ) (-x)) (fun y => α*ferrersEven ν μ y + β*ferrersOdd ν μ y)
      (Ioo (-1:ℝ) 1) := ferrersP_neg_reflect_eqOn_even_odd ν μ
  have hg' : ∀ y ∈ Ioo (-1:ℝ) 1, ferrersP ν (-μ) (-y) = α*ferrersEven ν μ y + β*ferrersOdd ν μ y :=
    fun y hy => hg hy
  have h0 : (0:ℝ) ∈ Ioo (-1:ℝ) 1 := by norm_num
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  -- αβ vanishes exactly at the exceptional parameters
  have hW : 4*(α*β)/π = 2/(Gamma (μ-ν)*Gamma (ν+μ+1)) := by
    have e1 := ferrersWronskian_of_even_odd hf hg h0
    have e2 := ferrers_wronskian_3 ν μ h0
    rw [e1] at e2
    simp only [ofReal_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
      mul_one] at e2
    rw [← e2]; ring
  have hab : α*β = 0 ↔ (∃ n : ℕ, μ-ν=-n) ∨ (∃ n : ℕ, μ+ν=-(n+1)) := by
    have : α*β = 0 ↔ Gamma (μ-ν)*Gamma (ν+μ+1) = 0 := by
      constructor
      · intro h; rw [h, mul_zero, zero_div] at hW
        by_contra hc; exact (div_ne_zero two_ne_zero hc) hW.symm
      · intro h; rw [h, div_zero] at hW
        have := hW; field_simp at this; simpa using this
    rw [this, mul_eq_zero, Complex.Gamma_eq_zero_iff, Complex.Gamma_eq_zero_iff]
    refine or_congr Iff.rfl ⟨fun ⟨n, hn⟩ => ⟨n, by linear_combination hn⟩,
      fun ⟨n, hn⟩ => ⟨n, by linear_combination hn⟩⟩
  rw [← hab]
  constructor
  · rintro ⟨A, B, hAB, hrel⟩
    by_contra hne
    have hα0 : α ≠ 0 := left_ne_zero_of_mul hne
    have hβ0 : β ≠ 0 := right_ne_zero_of_mul hne
    have hz : EqOn (fun _ : ℝ => (0:ℂ)) (fun y => ((A+B)*α)*ferrersEven ν μ y+((B-A)*β)*ferrersOdd ν μ y)
        (Ioo (-1:ℝ) 1) := by
      intro y hy
      have := hrel y hy
      simp only at this ⊢
      rw [hf hy, hg' y hy] at this
      linear_combination -this
    have hE : EqOn (ferrersEven ν μ) (fun y => (1:ℂ)*ferrersEven ν μ y+0*ferrersOdd ν μ y) (Ioo (-1:ℝ) 1) :=
      fun y _ => by simp
    have hO : EqOn (ferrersOdd ν μ) (fun y => (0:ℂ)*ferrersEven ν μ y+1*ferrersOdd ν μ y) (Ioo (-1:ℝ) 1) :=
      fun y _ => by simp
    have w1 := ferrersWronskian_of_even_odd hz hO h0
    have w2 := ferrersWronskian_of_even_odd hz hE h0
    simp only [ferrersWronskian, zero_mul, sub_zero, deriv_const, mul_zero, ofReal_zero,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_one, zero_sub] at w1 w2
    have hk : (2:ℂ)/π ≠ 0 := div_ne_zero two_ne_zero hpi
    have a1 : (A+B)*α = 0 := by
      rcases mul_eq_zero.mp w1.symm with h | h
      · exact h
      · exact absurd h hk
    have a2 : (B-A)*β = 0 := by
      have : -((B-A)*β)*(2/π) = 0 := by linear_combination -w2
      rcases mul_eq_zero.mp this with h | h
      · exact neg_eq_zero.mp h
      · exact absurd h hk
    have s1 : A+B = 0 := (mul_eq_zero.mp a1).resolve_right hα0
    have s2 : B-A = 0 := (mul_eq_zero.mp a2).resolve_right hβ0
    have hA : A = 0 := by linear_combination (s1 - s2)/2
    have hB : B = 0 := by linear_combination (s1 + s2)/2
    rcases hAB with h | h
    · exact h hA
    · exact h hB
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · refine ⟨1, 1, Or.inl one_ne_zero, fun x hx => ?_⟩
      rw [hf hx, hg' x hx, h]; ring
    · refine ⟨1, -1, Or.inl one_ne_zero, fun x hx => ?_⟩
      rw [hf hx, hg' x hx, h]; ring

/-- Independence of the recessive principal pair in DLMF 14.2(iii) and 14.21(ii). -/
theorem associatedPQ_independent {ν μ : ℂ} (hν : -1/2 ≤ ν.re) (hμ : 0 ≤ μ.re) :
    ¬∃ A B : ℂ, (A ≠ 0 ∨ B ≠ 0) ∧ ∀ x : ℝ, 1 < x → A*associatedP ν (-μ) x+B*olverQ ν μ x=0 := by
  rintro ⟨A, B, hAB, hrel⟩
  have h2 : ((2:ℝ):ℂ) - 1 ∈ slitPlane := by norm_num
  have hfa := (associatedP_analytic ν (-μ) _ h2).differentiableAt
  have hga := (olverQ_analytic ν μ _ h2).differentiableAt
  set h : ℂ → ℂ := fun z => A*associatedP ν (-μ) z + B*olverQ ν μ z with hh
  have hd : HasDerivAt h (A*deriv (associatedP ν (-μ)) ((2:ℝ):ℂ) + B*deriv (olverQ ν μ) ((2:ℝ):ℂ))
      ((2:ℝ):ℂ) := (hfa.hasDerivAt.const_mul A).add (hga.hasDerivAt.const_mul B)
  have hr := hd.comp_ofReal
  have hz : HasDerivAt (fun x : ℝ => h x) 0 2 := by
    refine (hasDerivAt_const (2:ℝ) (0:ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds (show (1:ℝ) < 2 by norm_num)] with x hx
    exact hrel x hx
  have e1 : A*deriv (associatedP ν (-μ)) ((2:ℝ):ℂ) + B*deriv (olverQ ν μ) ((2:ℝ):ℂ) = 0 :=
    hr.unique hz
  have e0 : A*associatedP ν (-μ) ((2:ℝ):ℂ) + B*olverQ ν μ ((2:ℝ):ℂ) = 0 := hrel 2 (by norm_num)
  have hW := associated_wronskian_8 ν μ h2
  unfold LegendreWronskian at hW
  have hG : Gamma (ν+μ+1) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp only [add_re, one_re]; linarith)
  have hR : -1/(Gamma (ν+μ+1)*(((2:ℝ):ℂ)^2-1)) ≠ 0 := by
    refine div_ne_zero (by norm_num) (mul_ne_zero hG (by push_cast; norm_num))
  apply hR
  rw [← hW]
  rcases hAB with hA | hB
  · have : A * (associatedP ν (-μ) ((2:ℝ):ℂ) * deriv (olverQ ν μ) ((2:ℝ):ℂ) -
        olverQ ν μ ((2:ℝ):ℂ) * deriv (associatedP ν (-μ)) ((2:ℝ):ℂ)) = 0 := by
      linear_combination deriv (olverQ ν μ) ((2:ℝ):ℂ) * e0 - olverQ ν μ ((2:ℝ):ℂ) * e1
    exact (mul_eq_zero.mp this).resolve_left hA
  · have : B * (associatedP ν (-μ) ((2:ℝ):ℂ) * deriv (olverQ ν μ) ((2:ℝ):ℂ) -
        olverQ ν μ ((2:ℝ):ℂ) * deriv (associatedP ν (-μ)) ((2:ℝ):ℂ)) = 0 := by
      linear_combination associatedP ν (-μ) ((2:ℝ):ℂ) * e1 - deriv (associatedP ν (-μ)) ((2:ℝ):ℂ) * e0
    exact (mul_eq_zero.mp this).resolve_left hB

end DLMF.Legendre
