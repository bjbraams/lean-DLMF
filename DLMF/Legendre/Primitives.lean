/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.AssociatedRecurrences

/-!
# Indefinite Ferrers integrals as derivative identities

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Legendre

/-- Select either Ferrers solution in the source primitive formulas. -/
def ferrersSolution (second : Bool) (ν μ : ℂ) (x : ℝ) : ℂ :=
  if second then ferrersQ ν μ x else ferrersP ν μ x

/-- `𝖯^μ_ν` is differentiable on `(-1,1)`. -/
theorem differentiableAt_ferrersP (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    DifferentiableAt ℝ (ferrersP ν μ) x :=
  (((hasDerivAt_ferrersEven ν μ hx).const_mul _).add ((hasDerivAt_ferrersOdd ν μ hx).const_mul _)
    ).differentiableAt.congr_of_eventuallyEq
    ((ferrersP_eqOn_even_odd ν μ).eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hx))

/-- Either Ferrers solution is differentiable on `(-1,1)`. -/
theorem differentiableAt_ferrersSolution (second : Bool) (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    DifferentiableAt ℝ (ferrersSolution second ν μ) x := by
  cases second
  · exact differentiableAt_ferrersP ν μ hx
  · exact differentiableAt_ferrersQ ν μ hx

/-- Order raising for either Ferrers solution. -/
theorem ferrersSolution_order_raise (second : Bool) (ν μ : ℂ) (h : second = true → LegendreQRegular ν μ)
    {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (1-x^2:ℂ)^(1/2:ℂ)*ferrersSolution second ν (μ+1) x =
      -(1-x^2:ℂ)*deriv (ferrersSolution second ν μ) x-μ*x*ferrersSolution second ν μ x := by
  cases second
  · have h2 := ferrersP_recurrence_2 ν μ hx
    have h4 := ferrersP_recurrence_4 ν μ hx
    simp only [ferrersSolution]
    simp only [Bool.false_eq_true, ↓reduceIte] at *
    show _ = -(1-x^2:ℂ)*deriv (ferrersP ν μ) x - _
    linear_combination h2 + h4
  · simp only [ferrersSolution]
    simp only [↓reduceIte]
    show _ = -(1-x^2:ℂ)*deriv (ferrersQ ν μ) x - _
    exact ferrersQ_order_raise ν μ (h rfl) hx

/-- Three-term order recurrence for either Ferrers solution. -/
theorem ferrersSolution_recurrence_1 (second : Bool) (ν μ : ℂ) (h : second = true → LegendreQRegular ν μ)
    {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersSolution second ν (μ+2) x+2*(μ+1)*x*(1-x^2:ℂ)^(-1/2:ℂ)*ferrersSolution second ν (μ+1) x
      +(ν-μ)*(ν+μ+1)*ferrersSolution second ν μ x=0 := by
  cases second
  · exact ferrersP_recurrence_1 ν μ hx
  · exact ferrersQ_recurrence_1 ν μ (h rfl) hx

/-- Derivative of `(1-x²)^c` on `(-1,1)`. -/
theorem hasDerivAt_one_sub_sq_cpow (c : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (fun y : ℝ => (1-(y:ℂ)^2)^c) (c*(1-(x:ℂ)^2)^(c-1)*(-2*x)) x := by
  have hs := ferrers_one_sub_sq_mem_slitPlane hx
  have h := ((hasStrictDerivAt_cpow_const (c := c) hs).hasDerivAt.comp (x:ℂ)
    ((hasDerivAt_pow 2 (x:ℂ)).const_sub 1)).comp_ofReal
  refine h.congr_deriv ?_
  push_cast; ring

/-- DLMF 14.17.1: for `-1 < x < 1` and `w = 𝖯` or `𝖰` (for `𝖰`, with `ν + μ + k` not a negative
integer for `k = -1, 0, 1`), `-(1-x²)^{-(μ-1)/2} w^{μ-1}_ν(x)` is an antiderivative of
`(1-x²)^{-μ/2} w^μ_ν(x)`. -/
@[dlmf 14.17.E1]
theorem ferrers_primitive_1 (second : Bool) (ν μ : ℂ) (hr : second=true → ∀ k ∈ Finset.Icc (-1:ℤ) 1, LegendreQRegular ν (μ+k))  {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (fun x : ℝ => -(1-x^2:ℂ)^(-(μ-1)/2)*ferrersSolution second ν (μ-1) x) ((1-x^2:ℂ)^(-μ/2)*ferrersSolution second ν μ x) x := by
  have hne := slitPlane_ne_zero (ferrers_one_sub_sq_mem_slitPlane hx)
  have hG := (differentiableAt_ferrersSolution second ν (μ-1) hx).hasDerivAt
  have hw := hasDerivAt_one_sub_sq_cpow (-(μ-1)/2) hx
  have hraise := ferrersSolution_order_raise second ν (μ-1)
    (fun hs => by simpa [sub_eq_add_neg] using hr hs (-1) (by simp)) hx
  rw [sub_add_cancel] at hraise
  refine (hw.neg.mul hG).congr_deriv ?_
  have e1 : (1-(x:ℂ)^2)^(-(μ-1)/2) = (1-(x:ℂ)^2)^(-(μ-1)/2-1)*(1-(x:ℂ)^2) := by
    conv_lhs => rw [show -(μ-1)/2 = (-(μ-1)/2-1)+1 by ring]
    rw [cpow_add _ _ hne, cpow_one]
  have e2 : (1-(x:ℂ)^2)^(-μ/2) = (1-(x:ℂ)^2)^(-(μ-1)/2-1)*(1-(x:ℂ)^2)^(1/2:ℂ) := by
    rw [← cpow_add _ _ hne]; ring_nf
  simp only [Pi.neg_apply]
  rw [e1, e2]
  linear_combination -(1-(x:ℂ)^2)^(-(μ-1)/2-1)*hraise

/-- DLMF 14.17.2: for `μ ≠ ν`, `μ ≠ -ν-1`, `-1 < x < 1` and `w = 𝖯` or `𝖰` (for `𝖰`, with `ν + μ +
k` not a negative integer for `k = -1, 0, 1`), `(1-x²)^{(μ+1)/2} w^{μ+1}_ν(x)/((ν-μ)(ν+μ+1))` is an
antiderivative of `(1-x²)^{μ/2} w^μ_ν(x)`. -/
@[dlmf 14.17.E2]
theorem ferrers_primitive_2 (second : Bool) (ν μ : ℂ) (hr : second=true → ∀ k ∈ Finset.Icc (-1:ℤ) 1, LegendreQRegular ν (μ+k)) (h0 : μ ≠ ν) (h1 : μ ≠ -ν-1) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (fun x : ℝ => (1-x^2:ℂ)^((μ+1)/2)/((ν-μ)*(ν+μ+1))*ferrersSolution second ν (μ+1) x) ((1-x^2:ℂ)^(μ/2)*ferrersSolution second ν μ x) x := by
  have hne := slitPlane_ne_zero (ferrers_one_sub_sq_mem_slitPlane hx)
  have hd : (ν-μ)*(ν+μ+1) ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm h0))
    (fun h => h1 (by linear_combination h))
  have hreg0 : second = true → LegendreQRegular ν μ := fun hs => by simpa using hr hs 0 (by simp)
  have hreg1 : second = true → LegendreQRegular ν (μ+1) := fun hs => by simpa using hr hs 1 (by simp)
  have hG := (differentiableAt_ferrersSolution second ν (μ+1) hx).hasDerivAt
  have hw := hasDerivAt_one_sub_sq_cpow ((μ+1)/2) hx
  have hraise := ferrersSolution_order_raise second ν (μ+1) hreg1 hx
  have hrec := ferrersSolution_recurrence_1 second ν μ hreg0 hx
  rw [show μ+1+1 = μ+2 by ring] at hraise
  refine ((hw.div_const _).mul hG).congr_deriv ?_
  have e1 : (1-(x:ℂ)^2)^((μ+1)/2) = (1-(x:ℂ)^2)^((μ+1)/2-1)*(1-(x:ℂ)^2) := by
    conv_lhs => rw [show (μ+1)/2 = ((μ+1)/2-1)+1 by ring]
    rw [cpow_add _ _ hne, cpow_one]
  have e2 : (1-(x:ℂ)^2)^(μ/2) = (1-(x:ℂ)^2)^((μ+1)/2-1)*(1-(x:ℂ)^2)^(1/2:ℂ) := by
    rw [← cpow_add _ _ hne]; ring_nf
  have e3 : (1-(x:ℂ)^2)^(-1/2:ℂ)*(1-(x:ℂ)^2)^(1/2:ℂ) = 1 := by
    rw [← cpow_add _ _ hne]; norm_num
  have key : (1-(x:ℂ)^2)*deriv (ferrersSolution second ν (μ+1)) x =
      (μ+1)*x*ferrersSolution second ν (μ+1) x + (ν-μ)*(ν+μ+1)*(1-(x:ℂ)^2)^(1/2:ℂ)*ferrersSolution second ν μ x := by
    linear_combination hraise - (1-(x:ℂ)^2)^(1/2:ℂ)*hrec + 2*(μ+1)*x*ferrersSolution second ν (μ+1) x*e3
  have hdd : (ν-μ)*(ν+μ+1)*((ν-μ)*(ν+μ+1))⁻¹ = 1 := mul_inv_cancel₀ hd
  rw [e1, e2]
  linear_combination ((1-(x:ℂ)^2)^((μ+1)/2-1)*((ν-μ)*(ν+μ+1))⁻¹)*key
    + (1-(x:ℂ)^2)^((μ+1)/2-1)*(1-(x:ℂ)^2)^(1/2:ℂ)*ferrersSolution second ν μ x*hdd

/-- DLMF 14.17.3 and 14.17.4: the closed-form primitive built from `F, G` at degrees `ν` and `ν+1`;
for Ferrers solutions it is an antiderivative of `x F G` (`singular = false`, requires `ν ≠ 0, -1`)
or of `x (1-x²)^{-3/2} F G` (`singular = true`). -/
@[dlmf 14.17.E3, dlmf 14.17.E4]
def ferrersProductPrimitive (singular : Bool) (F G : ℂ → ℂ → ℝ → ℂ) (ν μ : ℂ) (x : ℝ) : ℂ :=
  if singular then ((1-2*μ^2+2*ν*(ν+1))*F ν μ x*G ν μ x+(2*ν+1)*(μ-ν-1)*x*(F ν μ x*G (ν+1) μ x+F (ν+1) μ x*G ν μ x)+2*(μ-ν-1)^2*F (ν+1) μ x*G (ν+1) μ x)/((1-4*μ^2)*(1-x^2:ℂ)^(1/2:ℂ)) else ((μ^2-(ν+1)*(ν+x^2))*F ν μ x*G ν μ x+(ν+1)*(ν-μ+1)*x*(F ν μ x*G (ν+1) μ x+F (ν+1) μ x*G ν μ x)-(ν-μ+1)^2*F (ν+1) μ x*G (ν+1) μ x)/(2*ν*(ν+1))

/-- Degree-raising derivative relation for either Ferrers solution. -/
theorem ferrersSolution_deriv_degree (second : Bool) (ν μ : ℂ) (h : second = true → LegendreQRegular ν μ)
    {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (1-x^2:ℂ)*deriv (ferrersSolution second ν μ) x =
      (μ-ν-1)*ferrersSolution second (ν+1) μ x+(ν+1)*x*ferrersSolution second ν μ x := by
  cases second
  · exact ferrersP_recurrence_4 ν μ hx
  · exact ferrersQ_recurrence_4 ν μ (h rfl) hx

/-- Degree-lowering derivative relation at degree `ν+1`. -/
theorem ferrersSolution_deriv_degree_succ (second : Bool) (ν μ : ℂ) (h : second = true → LegendreQRegular ν μ)
    {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (1-x^2:ℂ)*deriv (ferrersSolution second (ν+1) μ) x =
      (ν+1+μ)*ferrersSolution second ν μ x-(ν+1)*x*ferrersSolution second (ν+1) μ x := by
  cases second
  · have := ferrersP_recurrence_5 (ν+1) μ hx
    rwa [add_sub_cancel_right] at this
  · have := ferrersQ_recurrence_5 (ν+1) μ (by rw [add_sub_cancel_right]; exact h rfl) hx
    rwa [add_sub_cancel_right] at this

/-- DLMF 14.17.3: for `ν ≠ 0, -1`, `-1 < x < 1` and Ferrers solutions `v, w ∈ {𝖯, 𝖰}` (with `ν + μ`
not a negative integer when a `𝖰` occurs), the closed form `ferrersProductPrimitive false` is an
antiderivative of `x v^μ_ν(x) w^μ_ν(x)`. -/
@[dlmf 14.17.E3]
theorem ferrers_product_primitive_3 (second₁ second₂ : Bool) (ν μ : ℂ) (hr : (second₁=true ∨ second₂=true) → LegendreQRegular ν μ) (hν0 : ν ≠ 0) (hν1 : ν ≠ -1) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (ferrersProductPrimitive false (ferrersSolution second₁) (ferrersSolution second₂) ν μ) (x*ferrersSolution second₁ ν μ x*ferrersSolution second₂ ν μ x) x := by
  have hr1 : second₁ = true → LegendreQRegular ν μ := fun h => hr (Or.inl h)
  have hr2 : second₂ = true → LegendreQRegular ν μ := fun h => hr (Or.inr h)
  have hF := (differentiableAt_ferrersSolution second₁ ν μ hx).hasDerivAt
  have hF1 := (differentiableAt_ferrersSolution second₁ (ν+1) μ hx).hasDerivAt
  have hG := (differentiableAt_ferrersSolution second₂ ν μ hx).hasDerivAt
  have hG1 := (differentiableAt_ferrersSolution second₂ (ν+1) μ hx).hasDerivAt
  have eF := ferrersSolution_deriv_degree second₁ ν μ hr1 hx
  have eF1 := ferrersSolution_deriv_degree_succ second₁ ν μ hr1 hx
  have eG := ferrersSolution_deriv_degree second₂ ν μ hr2 hx
  have eG1 := ferrersSolution_deriv_degree_succ second₂ ν μ hr2 hx
  have ha : HasDerivAt (fun y : ℝ => μ^2-(ν+1)*(ν+(y:ℂ)^2)) (-((ν+1)*(2*(x:ℂ)))) x := by
    have := ((hasDerivAt_id (x:ℂ)).pow 2).comp_ofReal
    simpa using ((this.const_add ν).const_mul (ν+1)).const_sub (μ^2)
  have hb : HasDerivAt (fun y : ℝ => (ν+1)*(ν-μ+1)*(y:ℂ)) ((ν+1)*(ν-μ+1)) x := by
    simpa using ((hasDerivAt_id (x:ℂ)).comp_ofReal).const_mul ((ν+1)*(ν-μ+1))
  have H := ((((ha.mul hF).mul hG).add (hb.mul ((hF.mul hG1).add (hF1.mul hG)))).sub
    ((hF1.mul hG1).const_mul ((ν-μ+1)^2))).div_const (2*ν*(ν+1))
  have e : ferrersProductPrimitive false (ferrersSolution second₁) (ferrersSolution second₂) ν μ =
      fun y : ℝ => ((μ^2-(ν+1)*(ν+(y:ℂ)^2))*ferrersSolution second₁ ν μ y*ferrersSolution second₂ ν μ y+(ν+1)*(ν-μ+1)*y*(ferrersSolution second₁ ν μ y*ferrersSolution second₂ (ν+1) μ y+ferrersSolution second₁ (ν+1) μ y*ferrersSolution second₂ ν μ y)
        -(ν-μ+1)^2*(ferrersSolution second₁ (ν+1) μ y*ferrersSolution second₂ (ν+1) μ y))/(2*ν*(ν+1)) := by
    funext y; simp [ferrersProductPrimitive]; ring
  rw [e]
  refine H.congr_deriv ?_
  have hne := slitPlane_ne_zero (ferrers_one_sub_sq_mem_slitPlane hx)
  have h2 : (2*ν*(ν+1)) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hν0)
    (fun h => hν1 (by linear_combination h))
  simp only [Pi.mul_apply, Pi.add_apply]
  rw [div_eq_iff h2]
  apply mul_left_cancel₀ hne
  linear_combination ((μ^2-(ν+1)*(ν+(x:ℂ)^2))*ferrersSolution second₂ ν μ x + (ν+1)*(ν-μ+1)*x*ferrersSolution second₂ (ν+1) μ x)*eF
    + ((μ^2-(ν+1)*(ν+(x:ℂ)^2))*ferrersSolution second₁ ν μ x + (ν+1)*(ν-μ+1)*x*ferrersSolution second₁ (ν+1) μ x)*eG
    + ((ν+1)*(ν-μ+1)*x*ferrersSolution second₂ ν μ x - (ν-μ+1)^2*ferrersSolution second₂ (ν+1) μ x)*eF1
    + ((ν+1)*(ν-μ+1)*x*ferrersSolution second₁ ν μ x - (ν-μ+1)^2*ferrersSolution second₁ (ν+1) μ x)*eG1

/-- DLMF 14.17.4: for `μ ≠ ±1/2`, `-1 < x < 1` and Ferrers solutions `v, w ∈ {𝖯, 𝖰}` (with `ν + μ`
not a negative integer when a `𝖰` occurs), the closed form `ferrersProductPrimitive true` is an
antiderivative of `x (1-x²)^{-3/2} v^μ_ν(x) w^μ_ν(x)`. -/
@[dlmf 14.17.E4]
theorem ferrers_product_primitive_4 (second₁ second₂ : Bool) (ν μ : ℂ) (hr : (second₁=true ∨ second₂=true) → LegendreQRegular ν μ) (hμ : μ ≠ 1/2) (hmμ : μ ≠ -1/2) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (ferrersProductPrimitive true (ferrersSolution second₁) (ferrersSolution second₂) ν μ) (x/(1-x^2:ℂ)^(3/2:ℂ)*ferrersSolution second₁ ν μ x*ferrersSolution second₂ ν μ x) x := by
  have hr1 : second₁ = true → LegendreQRegular ν μ := fun h => hr (Or.inl h)
  have hr2 : second₂ = true → LegendreQRegular ν μ := fun h => hr (Or.inr h)
  have hF := (differentiableAt_ferrersSolution second₁ ν μ hx).hasDerivAt
  have hF1 := (differentiableAt_ferrersSolution second₁ (ν+1) μ hx).hasDerivAt
  have hG := (differentiableAt_ferrersSolution second₂ ν μ hx).hasDerivAt
  have hG1 := (differentiableAt_ferrersSolution second₂ (ν+1) μ hx).hasDerivAt
  have eF := ferrersSolution_deriv_degree second₁ ν μ hr1 hx
  have eF1 := ferrersSolution_deriv_degree_succ second₁ ν μ hr1 hx
  have eG := ferrersSolution_deriv_degree second₂ ν μ hr2 hx
  have eG1 := ferrersSolution_deriv_degree_succ second₂ ν μ hr2 hx
  have hne := slitPlane_ne_zero (ferrers_one_sub_sq_mem_slitPlane hx)
  have hS0 : (1-(x:ℂ)^2)^(1/2:ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hne)
  have hk : (1-4*μ^2) ≠ 0 := by
    intro h
    have : (2*μ-1)*(2*μ+1) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp this with h' | h'
    · exact hμ (by linear_combination h'/2)
    · exact hmμ (by linear_combination h'/2)
  have hb : HasDerivAt (fun y : ℝ => (2*ν+1)*(μ-ν-1)*(y:ℂ)) ((2*ν+1)*(μ-ν-1)) x := by
    simpa using ((hasDerivAt_id (x:ℂ)).comp_ofReal).const_mul ((2*ν+1)*(μ-ν-1))
  have hS := (hasDerivAt_one_sub_sq_sqrt hx).const_mul (1-4*μ^2)
  have H := ((((hF.mul hG).const_mul (1-2*μ^2+2*ν*(ν+1))).add (hb.mul ((hF.mul hG1).add (hF1.mul hG)))).add
    ((hF1.mul hG1).const_mul (2*(μ-ν-1)^2))).div hS (mul_ne_zero hk hS0)
  have e : ferrersProductPrimitive true (ferrersSolution second₁) (ferrersSolution second₂) ν μ =
      fun y : ℝ => ((1-2*μ^2+2*ν*(ν+1))*(ferrersSolution second₁ ν μ y*ferrersSolution second₂ ν μ y)
        +(2*ν+1)*(μ-ν-1)*y*(ferrersSolution second₁ ν μ y*ferrersSolution second₂ (ν+1) μ y
          +ferrersSolution second₁ (ν+1) μ y*ferrersSolution second₂ ν μ y)
        +2*(μ-ν-1)^2*(ferrersSolution second₁ (ν+1) μ y*ferrersSolution second₂ (ν+1) μ y))
        /((1-4*μ^2)*(1-(y:ℂ)^2)^(1/2:ℂ)) := by
    funext y; simp [ferrersProductPrimitive]; ring
  rw [e]
  refine H.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.add_apply]
  have e32 : (1-(x:ℂ)^2)^(3/2:ℂ) = (1-(x:ℂ)^2)^(1/2:ℂ)*(1-(x:ℂ)^2) := by
    conv_lhs => rw [show (3/2:ℂ) = 1/2+1 by norm_num]
    rw [cpow_add _ _ hne, cpow_one]
  have hS2 : (1-(x:ℂ)^2)^(1/2:ℂ)*(1-(x:ℂ)^2)^(1/2:ℂ) = 1-(x:ℂ)^2 := by
    rw [← cpow_add _ _ hne]; norm_num
  rw [e32]
  have key : (1-(x:ℂ)^2)*(
      (1-2*μ^2+2*ν*(ν+1))*(deriv (ferrersSolution second₁ ν μ) x*ferrersSolution second₂ ν μ x
        + ferrersSolution second₁ ν μ x*deriv (ferrersSolution second₂ ν μ) x)
      + (2*ν+1)*(μ-ν-1)*(ferrersSolution second₁ ν μ x*ferrersSolution second₂ (ν+1) μ x
          +ferrersSolution second₁ (ν+1) μ x*ferrersSolution second₂ ν μ x)
      + (2*ν+1)*(μ-ν-1)*x*(deriv (ferrersSolution second₁ ν μ) x*ferrersSolution second₂ (ν+1) μ x
          + ferrersSolution second₁ ν μ x*deriv (ferrersSolution second₂ (ν+1) μ) x
          + deriv (ferrersSolution second₁ (ν+1) μ) x*ferrersSolution second₂ ν μ x
          + ferrersSolution second₁ (ν+1) μ x*deriv (ferrersSolution second₂ ν μ) x)
      + 2*(μ-ν-1)^2*(deriv (ferrersSolution second₁ (ν+1) μ) x*ferrersSolution second₂ (ν+1) μ x
          + ferrersSolution second₁ (ν+1) μ x*deriv (ferrersSolution second₂ (ν+1) μ) x))
      + x*((1-2*μ^2+2*ν*(ν+1))*(ferrersSolution second₁ ν μ x*ferrersSolution second₂ ν μ x)
        +(2*ν+1)*(μ-ν-1)*x*(ferrersSolution second₁ ν μ x*ferrersSolution second₂ (ν+1) μ x
          +ferrersSolution second₁ (ν+1) μ x*ferrersSolution second₂ ν μ x)
        +2*(μ-ν-1)^2*(ferrersSolution second₁ (ν+1) μ x*ferrersSolution second₂ (ν+1) μ x))
      = (1-4*μ^2)*x*ferrersSolution second₁ ν μ x*ferrersSolution second₂ ν μ x := by
    linear_combination
      ((1-2*μ^2+2*ν*(ν+1))*ferrersSolution second₂ ν μ x + (2*ν+1)*(μ-ν-1)*x*ferrersSolution second₂ (ν+1) μ x)*eF
      + ((1-2*μ^2+2*ν*(ν+1))*ferrersSolution second₁ ν μ x + (2*ν+1)*(μ-ν-1)*x*ferrersSolution second₁ (ν+1) μ x)*eG
      + ((2*ν+1)*(μ-ν-1)*x*ferrersSolution second₂ ν μ x + 2*(μ-ν-1)^2*ferrersSolution second₂ (ν+1) μ x)*eF1
      + ((2*ν+1)*(μ-ν-1)*x*ferrersSolution second₁ ν μ x + 2*(μ-ν-1)^2*ferrersSolution second₁ (ν+1) μ x)*eG1
  generalize (1-(x:ℂ)^2)^(1/2:ℂ) = S at hS0 hS2 ⊢
  rw [← hS2] at key ⊢
  have hk' : 1 - μ^2*4 ≠ 0 := by rw [mul_comm]; exact hk
  field_simp
  linear_combination key

end DLMF.Legendre
