/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.BoundaryIntegrals
public import DLMF.Legendre.Connections
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Barnes's integral for Ferrers functions

Euler's and Gauss's quadratic transformations express the Ferrers function at `0 < x < 1`
through a regularized Gauss function at `1-x²`. The substitution `u = 1-x²` and the
boundary fractional integral give DLMF 14.17.5 for `Re σ > -1`, `Re μ > -1`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory DLMF.Hypergeometric
open scoped Real Topology Nat

namespace DLMF.Legendre.FerrersBarnes

/-- A quadratic representation of the negative-order Ferrers function for `0 < x < 1`. -/
lemma ferrersP_quadratic {μ ν : ℂ} (hμ : -1 < μ.re) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    ferrersP ν (-μ) x = (2 : ℂ)^(-μ) * (1-(x : ℂ)^2)^(μ/2) *
      regularizedGaussHypergeometric ((μ-ν)/2) ((ν+μ+1)/2) (μ+1) (1-(x : ℂ)^2) := by
  have hxI : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1],hx.2⟩
  have hz : ‖(1-(x : ℂ))/2‖ < 1 := by
    rw [show (1-(x : ℂ))/2 = (((1-x)/2:ℝ):ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hx.2])]
    linarith [hx.1]
  have hw : ‖1-(x : ℂ)^2‖ < 1 := by
    rw [show 1-(x : ℂ)^2 = ((1-x^2:ℝ):ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by nlinarith [hx.1,hx.2])]
    nlinarith [hx.1]
  have hc : ∀ k : ℕ, μ+1 ≠ -k := not_neg_nat_of_re_pos (by simp; linarith)
  have hden : (μ-ν)/2 + (ν+μ+1)/2 + 1/2 = μ+1 := by ring
  have harg : 4*((1-(x : ℂ))/2)*(1-((1-(x : ℂ))/2)) = 1-(x : ℂ)^2 := by ring
  have hq := gauss_quadratic (a := (μ-ν)/2) (b := (ν+μ+1)/2)
    (by rw [hden]; exact hc) hz
    (by rw [harg]; exact hw)
    (by simp; linarith [hx.1])
  rw [show 2*((μ-ν)/2) = μ-ν by ring,
    show 2*((ν+μ+1)/2) = ν+μ+1 by ring,
    show (μ-ν)/2+(ν+μ+1)/2+1/2 = μ+1 by ring,
    show 4*((1-(x : ℂ))/2)*(1-((1-(x : ℂ))/2)) = 1-(x : ℂ)^2 by ring,
    ordinaryHypergeometric_eq_Gamma_mul_regularizedGaussHypergeometric hc hz,
    ordinaryHypergeometric_eq_Gamma_mul_regularizedGaussHypergeometric hc hw] at hq
  have he := mul_left_cancel₀ (Gamma_ne_zero hc) hq
  have hg := ferrers_quadratic_gauge (-μ) hxI
  simp only [neg_neg,neg_div] at hg
  rw [ferrersP, show 1-(-μ) = μ+1 by ring,
    regularizedGaussHypergeometric_euler _ _ _ (mem_cutPlane_of_norm_lt_one hz),
    show μ+1-(ν+1)-(-ν) = μ by ring,
    show μ+1-(ν+1) = μ-ν by ring,
    show μ+1-(-ν) = ν+μ+1 by ring,
    show 1-(1-(x : ℂ))/2 = (1+(x : ℂ))/2 by ring,
    ←mul_assoc]
  rw [show -μ/2 = -(μ/2) by ring, hg, he]


/-- The substitution `u = 1 - x²` converts the Ferrers moment to a beta-weighted Gauss integral. -/
lemma integral_kernel_transform (σ μ ν : ℂ) :
    (∫ x : ℝ in (0 : ℝ)..1, (x : ℂ)^σ * (1-(x : ℂ)^2)^μ *
      regularizedGaussHypergeometric ((μ-ν)/2) ((ν+μ+1)/2) (μ+1) (1-(x : ℂ)^2)) =
      (1 / 2 : ℂ) * ∫ u : ℝ in (0 : ℝ)..1,
        regularizedGaussHGFun ((μ-ν)/2) ((ν+μ+1)/2) (μ+1) u *
          (u : ℂ)^μ * (1-(u : ℂ))^((σ-1)/2) := by
  let f : ℝ → ℝ := fun x => 1-x^2
  let g : ℝ → ℂ := fun u =>
    regularizedGaussHGFun ((μ-ν)/2) ((ν+μ+1)/2) (μ+1) u *
      (u : ℂ)^μ * (1-(u : ℂ))^((σ-1)/2)
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt f (-2*x) (Ioo 0 1) x := by
    intro x _
    have h := ((hasDerivAt_id x).pow 2).const_sub 1
    simpa [f, Pi.pow_apply, id] using! h.hasDerivWithinAt
  have hinj : InjOn f (Ioo (0 : ℝ) 1) := by
    intro a ha b hb he
    dsimp [f] at he
    nlinarith [ha.1,hb.1]
  have himage : f '' Ioo (0 : ℝ) 1 = Ioo (0 : ℝ) 1 := by
    ext u
    constructor
    · rintro ⟨x,hx,rfl⟩
      dsimp [f]
      constructor <;> nlinarith [hx.1,hx.2]
    · intro hu
      refine ⟨Real.sqrt (1-u),⟨Real.sqrt_pos.mpr (by linarith [hu.2]),?_⟩,?_⟩
      · have := Real.sq_sqrt (by linarith [hu.2] : 0 ≤ 1-u)
        nlinarith [Real.sqrt_nonneg (1-u),hu.1]
      · dsimp [f]
        rw [Real.sq_sqrt (by linarith [hu.2])]
        ring
  have hcov := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj g
  rw [himage] at hcov
  have hpoint : ∀ x ∈ Ioo (0 : ℝ) 1, |-2*x| • g (f x) =
      2*((x : ℂ)^σ * (1-(x : ℂ)^2)^μ *
        regularizedGaussHypergeometric ((μ-ν)/2) ((ν+μ+1)/2) (μ+1) (1-(x : ℂ)^2)) := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.1.ne'
    have hx2 : 0 < 1-x^2 := by nlinarith [hx.1,hx.2]
    have hw : ‖1-(x : ℂ)^2‖ < 1 := by
      rw [show 1-(x : ℂ)^2 = ((1-x^2:ℝ):ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx2]
      nlinarith [hx.1]
    have hp : ((x : ℂ)^2)^((σ-1)/2) = (x : ℂ)^(σ-1) := by
      rw [← cpow_natCast,←cpow_mul]
      · congr 1
        ring
      · simp [mul_im,log_im,arg_ofReal_of_nonneg hx.1.le,Real.pi_pos]
      · simp [mul_im,log_im,arg_ofReal_of_nonneg hx.1.le,Real.pi_pos.le]
    dsimp [f,g]
    rw [abs_of_neg (by nlinarith [hx.1])]
    push_cast
    rw [show (1:ℂ)-(1-(x : ℂ)^2) = (x : ℂ)^2 by ring, hp,
      ← regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricFun _ _ _ hw]
    have hc : (x : ℂ) * (x : ℂ)^(σ-1) = (x : ℂ)^σ := by
      calc (x : ℂ) * (x : ℂ)^(σ-1) = (x : ℂ)^(1+(σ-1)) := by
            rw [cpow_add _ _ hx0, cpow_one]
        _ = _ := by congr 1; ring
    calc _ = 2*((x : ℂ) * (x : ℂ)^(σ-1)) * (1-(x : ℂ)^2)^μ *
        regularizedGaussHypergeometric ((μ-ν)/2) ((ν+μ+1)/2) (μ+1) (1-(x : ℂ)^2) := by ring
      _ = _ := by rw [hc]; ring
  rw [setIntegral_congr_fun measurableSet_Ioo hpoint, integral_const_mul] at hcov
  rw [intervalIntegral.integral_of_le zero_le_one,integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le zero_le_one,integral_Ioc_eq_integral_Ioo, hcov]
  ring


/-- Barnes's Ferrers integral on `Re σ > -1`, `Re μ > -1`, with arbitrary complex degree. -/
lemma integral_value {σ μ : ℂ} (hσ : -1 < σ.re) (hμ : -1 < μ.re) (ν : ℂ) :
    (∫ x : ℝ in 0..1, (x : ℂ)^σ*(1-x^2:ℂ)^(μ/2)*ferrersP ν (-μ) x)=Gamma ((σ+1)/2)*Gamma
        (σ/2+1)/(2^(μ+1)*Gamma ((σ-ν+μ)/2+1)*Gamma ((σ+ν+μ+3)/2)) := by
  have hp : (∫ x : ℝ in 0..1, (x : ℂ)^σ*(1-x^2:ℂ)^(μ/2)*ferrersP ν (-μ) x) =
      (2 : ℂ)^(-μ) * (∫ x : ℝ in 0..1, (x : ℂ)^σ * (1-(x : ℂ)^2)^μ *
        regularizedGaussHypergeometric ((μ-ν)/2) ((ν+μ+1)/2) (μ+1) (1-(x : ℂ)^2)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro x hx
    dsimp only
    rw [ferrersP_quadratic hμ hx]
    have hx0 : 1-(x : ℂ)^2 ≠ 0 := by
      exact_mod_cast (by nlinarith [hx.1,hx.2] : 1-x^2 ≠ 0)
    have hpow : (1-(x : ℂ)^2)^(μ/2) * (1-(x : ℂ)^2)^(μ/2) = (1-(x : ℂ)^2)^μ := by
      rw [←cpow_add _ _ hx0,add_halves]
    linear_combination (2 : ℂ)^(-μ) * (x : ℂ)^σ *
      regularizedGaussHypergeometric ((μ-ν)/2) ((ν+μ+1)/2) (μ+1) (1-(x : ℂ)^2) * hpow
  rw [hp,integral_kernel_transform]
  have hG : Gamma ((σ+1)/2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hf := fractional_integral_one (a := (μ-ν)/2) (b := (ν+μ+1)/2)
    (c := μ+(σ+3)/2) (d := μ+1) (by simp; linarith)
    (by simp; linarith) (by simp; ring_nf; norm_num)
  rw [show μ+(σ+3)/2-(μ+1) = (σ+1)/2 by ring,
    show μ+1-1 = μ by ring,
    show (σ+1)/2-1 = (σ-1)/2 by ring,
    show μ+(σ+3)/2-(μ-ν)/2-((ν+μ+1)/2) = σ/2+1 by ring,
    show μ+(σ+3)/2-(μ-ν)/2 = (σ+ν+μ+3)/2 by ring,
    show μ+(σ+3)/2-((ν+μ+1)/2) = (σ-ν+μ)/2+1 by ring] at hf
  have hJ : (∫ t : ℝ in 0..1,
      regularizedGaussHGFun ((μ-ν)/2) ((ν+μ+1)/2) (μ+1) t *
        (t : ℂ)^μ * (1-(t : ℂ))^((σ-1)/2)) =
      Gamma ((σ+1)/2) * (Gamma (σ/2+1) /
        (Gamma ((σ+ν+μ+3)/2) * Gamma ((σ-ν+μ)/2+1))) := by
    rw [←hf]
    field_simp
  rw [hJ]
  have hpow : (2 : ℂ)^(-μ)*(1 / 2 : ℂ) = ((2 : ℂ)^(μ+1))⁻¹ := by
    rw [← cpow_neg,neg_add,cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
    simp only [cpow_neg,cpow_one]
    ring
  calc _ = ((2 : ℂ)^(-μ)*(1 / 2 : ℂ)) *
      (Gamma ((σ+1)/2) * Gamma (σ/2+1) /
        (Gamma ((σ+ν+μ+3)/2) * Gamma ((σ-ν+μ)/2+1))) := by ring
    _ = _ := by rw [hpow]; ring


end DLMF.Legendre.FerrersBarnes
