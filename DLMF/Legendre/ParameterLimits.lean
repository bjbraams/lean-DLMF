/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Integrals
public import DLMF.Gamma.RecipGammaDeriv

/-!
# Removable parameter values in source formulas

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Legendre

/-- Sine-weighted digamma with its removable values at negative integral degree. -/
def legendreSinDigamma (ν : ℂ) : ℂ :=
  limUnder (𝓝[≠] ν) (fun v => sin (π*v)*digamma (v+1))

/-- Sine-squared-weighted trigamma with removable values. -/
def legendreSinSqTrigamma (ν : ℂ) : ℂ :=
  limUnder (𝓝[≠] ν) (fun v => (sin (π*v))^2*deriv digamma (v+1))

/-- Reflection in the form `Γ(-v)⁻¹ = -sin(πv) Γ(v+1) / π`, valid when `Γ(-v)` is finite. -/
theorem recip_Gamma_neg_eq_of_sin_ne_zero {v : ℂ} (hv : ∀ m : ℕ, v + 1 ≠ -(m : ℂ)) (hs : sin (π * v) ≠ 0) :
    (Gamma (-v))⁻¹ = -(sin (π * v) * Gamma (v + 1)) / π := by
  have h := Complex.Gamma_mul_Gamma_one_sub (v + 1)
  rw [show 1 - (v + 1) = -v by ring, show (π : ℂ) * (v + 1) = π * v + π by ring, sin_add_pi] at h
  have hG := Complex.Gamma_ne_zero hv
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have h' : Gamma (v + 1) * Gamma (-v) * sin (π * v) = -π := by
    rw [h]; field_simp
  refine inv_eq_of_mul_eq_one_right ?_
  calc Gamma (-v) * (-(sin (π * v) * Gamma (v + 1)) / π)
      = -(Gamma (v + 1) * Gamma (-v) * sin (π * v)) / π := by ring
    _ = 1 := by rw [h']; field_simp

/-- `sin(πv) ψ(v+1) = π (1/Γ)'(v+1) / Γ(-v)` off the negative integers. -/
theorem sin_mul_digamma_add_one_eq {v : ℂ} (hv : ∀ m : ℕ, v + 1 ≠ -(m : ℂ)) :
    sin (π * v) * digamma (v + 1) = π * DLMF.Gamma.recipGammaDeriv 1 (v + 1) * (Gamma (-v))⁻¹ := by
  by_cases hs : sin (π * v) = 0
  · obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hs
    have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    have hvk : v = k := by
      have : (π : ℂ) * v = π * k := by rw [hk]; ring
      exact mul_left_cancel₀ hpi this
    rcases k with k | k
    · have : Gamma (-v) = 0 := by
        rw [hvk]; simpa using Complex.Gamma_neg_nat_eq_zero k
      rw [hs, this]; simp
    · exfalso; apply hv k
      rw [hvk]; push_cast; ring
  · rw [recip_Gamma_neg_eq_of_sin_ne_zero hv hs, DLMF.Gamma.recipGammaDeriv_one_eq hv]
    have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    have hG := Complex.Gamma_ne_zero hv
    field_simp

/-- `sin²(πv) ψ'(v+1) = π² (((1/Γ)')² - (1/Γ)(1/Γ)'')(v+1) / Γ(-v)²` off the negative integers. -/
theorem sin_sq_mul_deriv_digamma_add_one_eq {v : ℂ} (hv : ∀ m : ℕ, v + 1 ≠ -(m : ℂ)) :
    sin (π * v) ^ 2 * deriv digamma (v + 1) =
      π ^ 2 * (DLMF.Gamma.recipGammaDeriv 1 (v + 1) ^ 2 - (Gamma (v + 1))⁻¹ * DLMF.Gamma.recipGammaDeriv 2 (v + 1)) *
        ((Gamma (-v))⁻¹) ^ 2 := by
  by_cases hs : sin (π * v) = 0
  · obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hs
    have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    have hvk : v = k := by
      have : (π : ℂ) * v = π * k := by rw [hk]; ring
      exact mul_left_cancel₀ hpi this
    rcases k with k | k
    · have : Gamma (-v) = 0 := by
        rw [hvk]; simpa using Complex.Gamma_neg_nat_eq_zero k
      rw [hs, this]; simp
    · exfalso; apply hv k
      rw [hvk]; push_cast; ring
  · rw [recip_Gamma_neg_eq_of_sin_ne_zero hv hs, ← DLMF.Gamma.deriv_digamma_mul_recip_Gamma_sq hv]
    have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    have hG := Complex.Gamma_ne_zero hv
    field_simp

/-- The removable limit of `sin(πv) ψ(v+1)`, in closed form. -/
theorem tendsto_sin_mul_digamma_add_one (ν : ℂ) :
    Tendsto (fun v => sin (π*v)*digamma (v+1)) (𝓝[≠] ν)
      (𝓝 (π * DLMF.Gamma.recipGammaDeriv 1 (ν + 1) * (Gamma (-ν))⁻¹)) := by
  have hc : Continuous fun v : ℂ => π * DLMF.Gamma.recipGammaDeriv 1 (v + 1) * (Gamma (-v))⁻¹ :=
    (continuous_const.mul ((DLMF.Gamma.continuous_recipGammaDeriv 1).comp
      (continuous_id.add continuous_const))).mul
      (DLMF.Gamma.differentiable_recip_Gamma.continuous.comp continuous_neg)
  refine ((hc.tendsto ν).mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [eventually_affine_ne_neg_nat one_ne_zero 1 ν] with v hv
  exact (sin_mul_digamma_add_one_eq fun m h => hv m (by rw [one_mul]; exact h)).symm

/-- The removable limit of `sin²(πv) ψ'(v+1)`, in closed form. -/
theorem tendsto_sin_sq_mul_deriv_digamma_add_one (ν : ℂ) :
    Tendsto (fun v => (sin (π*v))^2*deriv digamma (v+1)) (𝓝[≠] ν)
      (𝓝 (π ^ 2 * (DLMF.Gamma.recipGammaDeriv 1 (ν + 1) ^ 2 -
        (Gamma (ν + 1))⁻¹ * DLMF.Gamma.recipGammaDeriv 2 (ν + 1)) * ((Gamma (-ν))⁻¹) ^ 2)) := by
  have hs : Continuous fun v : ℂ => v + 1 := continuous_id.add continuous_const
  have hc : Continuous fun v : ℂ => π ^ 2 * (DLMF.Gamma.recipGammaDeriv 1 (v + 1) ^ 2 -
      (Gamma (v + 1))⁻¹ * DLMF.Gamma.recipGammaDeriv 2 (v + 1)) * ((Gamma (-v))⁻¹) ^ 2 :=
    (continuous_const.mul ((((DLMF.Gamma.continuous_recipGammaDeriv 1).comp hs).pow 2).sub
      ((DLMF.Gamma.differentiable_recip_Gamma.continuous.comp hs).mul
        ((DLMF.Gamma.continuous_recipGammaDeriv 2).comp hs)))).mul
      ((DLMF.Gamma.differentiable_recip_Gamma.continuous.comp continuous_neg).pow 2)
  refine ((hc.tendsto ν).mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [eventually_affine_ne_neg_nat one_ne_zero 1 ν] with v hv
  exact (sin_sq_mul_deriv_digamma_add_one_eq fun m h => hv m (by rw [one_mul]; exact h)).symm

/-- Closed form of `legendreSinDigamma`: `sin(πν) ψ(ν+1)` extended to all `ν`. -/
theorem legendreSinDigamma_eq (ν : ℂ) :
    legendreSinDigamma ν = π * DLMF.Gamma.recipGammaDeriv 1 (ν + 1) * (Gamma (-ν))⁻¹ :=
  (tendsto_sin_mul_digamma_add_one ν).limUnder_eq

/-- Closed form of `legendreSinSqTrigamma`: `sin²(πν) ψ'(ν+1)` extended to all `ν`. -/
theorem legendreSinSqTrigamma_eq (ν : ℂ) :
    legendreSinSqTrigamma ν = π ^ 2 * (DLMF.Gamma.recipGammaDeriv 1 (ν + 1) ^ 2 -
      (Gamma (ν + 1))⁻¹ * DLMF.Gamma.recipGammaDeriv 2 (ν + 1)) * ((Gamma (-ν))⁻¹) ^ 2 :=
  (tendsto_sin_sq_mul_deriv_digamma_add_one ν).limUnder_eq

/-- `sin(πv) ψ(v+1)` tends to `legendreSinDigamma ν` as `v → ν`, `v ≠ ν`, for every complex `ν` (the
singularities at negative integers are removable). -/
theorem legendreSinDigamma_limit (ν : ℂ) :
    Tendsto (fun v => sin (π*v)*digamma (v+1)) (𝓝[≠] ν) (𝓝 (legendreSinDigamma ν)) := by
  rw [legendreSinDigamma_eq]; exact tendsto_sin_mul_digamma_add_one ν

/-- `sin²(πv) ψ'(v+1)` tends to `legendreSinSqTrigamma ν` as `v → ν`, `v ≠ ν`, for every complex `ν`
(the singularities at negative integers are removable). -/
theorem legendreSinSqTrigamma_limit (ν : ℂ) :
    Tendsto (fun v => (sin (π*v))^2*deriv digamma (v+1)) (𝓝[≠] ν) (𝓝 (legendreSinSqTrigamma ν)) := by
  rw [legendreSinSqTrigamma_eq]; exact tendsto_sin_sq_mul_deriv_digamma_add_one ν

/-- DLMF 14.17.10: for `λ ≠ ν` and `λ ≠ -ν-1`, `∫_{-1}^{1} 𝖯_ν(x) 𝖯_λ(x) dx = 2(2(sin(πλ) sin(πν)
ψ(ν+1) - sin(πν) sin(πλ) ψ(λ+1)) + π sin((λ-ν)π))/(π² (λ-ν)(λ+ν+1))`, where `sin(πν) ψ(ν+1)` is
taken by continuity at negative integers. -/
@[dlmf 14.17.E10]
theorem ferrersPP_integral_all_degrees (ν lam : ℂ) (h0 : lam ≠ ν) (h1 : lam ≠ -ν-1) :
    (∫ x : ℝ in -1..1, ferrersP ν 0 x*ferrersP lam 0 x)=2*(2*(sin (π*lam)*legendreSinDigamma ν-sin (π*ν)*legendreSinDigamma lam)+π*sin ((lam-ν)*π))/(π^2*(lam-ν)*(lam+ν+1)) := by
  have hd1 : lam - ν ≠ 0 := sub_ne_zero.mpr h0
  have hd2 : lam + ν + 1 ≠ 0 := fun h => h1 (by linear_combination h)
  have hc : ν*(ν+1) - lam*(lam+1) ≠ 0 := by
    rw [show ν*(ν+1) - lam*(lam+1) = -((lam-ν)*(lam+ν+1)) by ring]
    exact neg_ne_zero.mpr (mul_ne_zero hd1 hd2)
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hB := legPI_boundary_const_all ν lam
  rw [legPI_integral_PP ν lam hc, legendreSinDigamma_eq, legendreSinDigamma_eq,
    show 2*(sin (π*lam)*(π * DLMF.Gamma.recipGammaDeriv 1 (ν+1) * (Gamma (-ν))⁻¹) -
      sin (π*ν)*(π * DLMF.Gamma.recipGammaDeriv 1 (lam+1) * (Gamma (-lam))⁻¹)) + π*sin ((lam-ν)*π) =
      (π:ℂ)^2 * (legPIK ν * legPIC lam - legPIK lam * legPIC ν) by rw [hB]; ring]
  field_simp
  ring

/-- DLMF 14.17.11: for `ν ≠ -1/2`, `∫_{-1}^{1} (𝖯_ν(x))² dx = (π² - 2 sin²(πν) ψ'(ν+1))/(π²
(ν+1/2))`, where `sin²(πν) ψ'(ν+1)` is taken by continuity at negative integers. -/
@[dlmf 14.17.E11]
theorem ferrersP_sq_integral_all_degrees {ν : ℂ} (hν : ν ≠ -1/2) :
    (∫ x : ℝ in -1..1, (ferrersP ν 0 x)^2)=(π^2-2*legendreSinSqTrigamma ν)/(π^2*(ν+1/2)) := by
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h3 : ν + 1/2 ≠ 0 := fun h => hν (by linear_combination h)
  have hne : ∀ᶠ v in 𝓝[≠] ν, v ≠ -1/2 :=
    nhdsWithin_le_nhds (continuousAt_id.eventually_ne hν)
  have heq : (fun v : ℂ => ∫ x : ℝ in -1..1, (ferrersP v 0 x)^2) =ᶠ[𝓝[≠] ν]
      fun v => (π^2-2*((sin (π*v))^2*deriv digamma (v+1)))/(π^2*(v+1/2)) := by
    filter_upwards [eventually_affine_ne_neg_nat one_ne_zero 1 ν, hne] with v hv hv2
    have hr : LegendreQRegular v 0 := fun n h => hv n (by rw [one_mul]; linear_combination h)
    rw [ferrers_product_integral_11 v hv2 hr, mul_comm (v:ℂ) π]; ring
  have hR : Tendsto (fun v : ℂ => (π^2-2*((sin (π*v))^2*deriv digamma (v+1)))/(π^2*(v+1/2)))
      (𝓝[≠] ν) (𝓝 ((π^2-2*legendreSinSqTrigamma ν)/(π^2*(ν+1/2)))) := by
    refine (tendsto_const_nhds.sub (tendsto_const_nhds.mul (legendreSinSqTrigamma_limit ν))).div
      ((tendsto_const_nhds.mul ((continuousAt_id.add continuousAt_const).tendsto)).mono_left
        nhdsWithin_le_nhds) (mul_ne_zero (pow_ne_zero 2 hπ) h3)
  exact tendsto_nhds_unique (((legPIU_tendsto_sq ν).mono_left nhdsWithin_le_nhds).congr' heq) hR

/-- DLMF 14.9.3 (limit form): for natural `m` and `-1 < x < 1`, `(-1)^m Γ(v-m+1)/Γ(v+m+1) 𝖯^m_v(x) →
𝖯^{-m}_ν(x)` as `v → ν`, `v ≠ ν`; this covers the degrees where the Gamma quotient is singular. -/
@[dlmf 14.9.E3]
theorem ferrersP_negative_order_parameter_limit (ν : ℂ) (m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    Tendsto (fun v : ℂ => (-1)^m*Gamma (v-m+1)/Gamma (v+m+1)*ferrersP v m x) (𝓝[≠] ν) (𝓝 (ferrersP ν (-m) x)) := by
  have ht : ((1:ℂ)-x)/2 ∈ cutPlane := by
    rw [mem_cutPlane, show (1:ℂ) - (1-(x:ℂ))/2 = (((1+x)/2 : ℝ) : ℂ) by push_cast; ring]
    exact Or.inl (by simp only [ofReal_re]; linarith [hx.1])
  have hc : Continuous fun v : ℂ => ferrersP v (-m) x := by
    unfold ferrersP
    exact continuous_const.mul (differentiable_regularizedGaussHG_comp (A := fun v => v+1) (B := fun v => -v)
      (C := fun _ => 1-(-(m:ℂ))) (by fun_prop) (by fun_prop) (by fun_prop) ht).continuous
  refine ((hc.tendsto ν).mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [eventually_affine_ne_neg_nat one_ne_zero (-(m:ℂ)+1) ν] with v hv
  exact ferrersP_negative_integer_order v m (fun n hn => hv n (by linear_combination hn)) hx

/-- DLMF 14.9.13 (limit form): for natural `m` and `z ∉ (-∞, 1]`, `Γ(v-m+1)/Γ(v+m+1) P^m_v(z) →
P^{-m}_ν(z)` as `v → ν`, `v ≠ ν`; this covers the degrees where the Gamma quotient is singular. -/
@[dlmf 14.9.E13]
theorem associatedP_negative_order_parameter_limit (ν : ℂ) (m : ℕ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    Tendsto (fun v : ℂ => Gamma (v-m+1)/Gamma (v+m+1)*associatedP v m z) (𝓝[≠] ν) (𝓝 (associatedP ν (-m) z)) := by
  have ht := mem_cutPlane_of_one_add (one_add_mem_slitPlane_of_sub_one hz)
  have hc : Continuous fun v : ℂ => associatedP v (-m) z := by
    unfold associatedP
    exact continuous_const.mul (differentiable_regularizedGaussHG_comp (A := fun v => v+1) (B := fun v => -v)
      (C := fun _ => 1-(-(m:ℂ))) (by fun_prop) (by fun_prop) (by fun_prop) ht).continuous
  refine ((hc.tendsto ν).mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [eventually_affine_ne_neg_nat one_ne_zero (-(m:ℂ)+1) ν] with v hv
  exact associatedP_negative_integer_order v m (fun n hn => hv n (by linear_combination hn)) hz

end DLMF.Legendre
