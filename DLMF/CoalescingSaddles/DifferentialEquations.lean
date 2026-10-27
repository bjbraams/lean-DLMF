/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.CoalescingSaddles.Defs
public import DLMF.CoalescingSaddles.CanonicalIntegrals

/-!
# Differential equations for the canonical integrals: DLMF §36.10

The canonical integrals are defined (`DLMF.CoalescingSaddles.Basic`) as absolutely convergent
integrals over rotated contours, on which the integrand and all its polynomial moments have
Gaussian decay. This file proves

* differentiation under the integral sign: `∂Ψ_K/∂x_m` is `i` times the moment of order `m`
  (`hasDerivAt_cuspoidMoment_update`, `iteratedDeriv_cuspoidIntegral_update`), so that
  `∂ⁿΨ_K/∂x_mⁿ = iⁿ ∫ t^{mn} exp(iΦ_K) dt`;
* integration by parts along the contour: `∫ (∂Φ_K/∂t) exp(iΦ_K) dt = 0`
  (`cuspoidMoment_ibp`), since the integrand is `-i d/dt exp(iΦ_K)` and `exp(iΦ_K)` vanishes at
  both ends of the contour.

From these, the operator equation 36.10.1, the ordinary differential equation 36.10.2 in `x₁`,
its special cases 36.10.3–36.10.5, and the relations 36.10.6–36.10.10 between partial derivatives
are proved. Of the umbilic equations 36.10.11–36.10.18, those for `Ψ^{(H)}` (36.10.15, 36.10.16,
36.10.18) are proved in the same way on the product of two cubic contours
(`hasDerivAt_hyperbolicUmbilicMoment_x`, Fubini and integration by parts in each variable); those
for `Ψ^{(E)}` (36.10.13, 36.10.14, 36.10.17) are proved on the 2-cycle of
`ellipticUmbilicIntegral` in the coordinates `a = s + it`, `b = s - it`, with weighted moments
`q2t_EM` and integration by parts along each ray (the boundary terms cancel over the cycle).

Partial derivatives are written with `Function.update`: `∂ⁿΨ_K/∂x_mⁿ` at `x` is
`iteratedDeriv n (fun s => cuspoidIntegral K (Function.update x m s)) (x m)`, where (as in
`DLMF.CoalescingSaddles.Basic`) the Lean index `m : Fin K` is DLMF's `x_{m+1}`. All
differentiability used in these statements is proved here (the canonical integrals are smooth
in each variable), so the Lean convention `deriv f = 0` at non-differentiable points never
enters.

The integrability lemmas for the rotated contour (`norm_cuspoidContour`, `cuspoidContour_pow`,
`s36a_norm_integrand_le`, …) are those of `DLMF.CoalescingSaddles.CanonicalIntegrals`.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set Filter Function
open scoped Real Topology

namespace DLMF.CoalescingSaddles

/-! ### Helpers: Gaussian bounds for the moment integrands -/

/-- `|r|^p exp(-r²/2)` is integrable on `ℝ`. -/
lemma s36b_integrable_pow_mul_gauss (p : ℕ) :
    Integrable fun r : ℝ => |r| ^ p * Real.exp (-(1 / 2) * r ^ 2) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (s := (p : ℝ))
    (by have := p.cast_nonneg (α := ℝ); linarith)
  refine h.norm.congr (ae_of_all _ fun r => ?_)
  simp only [Real.rpow_natCast, norm_mul, Real.norm_eq_abs, abs_pow,
    abs_of_pos (Real.exp_pos _)]

/-- The constant of the Gaussian bound `s36a_norm_integrand_le`, monotone in `C ≥ ∑ |xₘ|`. -/
lemma s36b_const_mono (K : ℕ) {S C : ℝ} (hS : 0 ≤ S) (hSC : S ≤ C) :
    Real.exp (1 / 2 + S + S * (1 + 2 * S) ^ K) ≤ Real.exp (1 / 2 + C + C * (1 + 2 * C) ^ K) := by
  apply Real.exp_le_exp.mpr
  have h1 : (1 + 2 * S) ^ K ≤ (1 + 2 * C) ^ K := pow_le_pow_left₀ (by linarith) (by linarith) K
  have h2 : S * (1 + 2 * S) ^ K ≤ C * (1 + 2 * C) ^ K :=
    mul_le_mul hSC h1 (pow_nonneg (by linarith) K) (by linarith)
  linarith

/-- Gaussian bound for the moment integrand, uniform in `x` with `∑ |xₘ| ≤ C`. -/
lemma s36b_norm_moment_integrand_le (K : ℕ) (x : Fin K → ℝ) (p : ℕ) (r : ℝ) {C : ℝ}
    (hC : ∑ m, |x m| ≤ C) :
    ‖cuspoidContourDir K r * cuspoidContour K r ^ p *
        exp (I * cuspoidPotential K (cuspoidContour K r) x)‖ ≤
      Real.exp (1 / 2 + C + C * (1 + 2 * C) ^ K) * (|r| ^ p * Real.exp (-(1 / 2) * r ^ 2)) := by
  have h := s36a_norm_integrand_le K x one_pos r
  simp only [ofReal_one, mul_one, one_mul] at h
  have hS : 0 ≤ ∑ m, |x m| := Finset.sum_nonneg fun m _ => abs_nonneg _
  have hmono := s36b_const_mono K hS hC
  have hsplit : ‖cuspoidContourDir K r * cuspoidContour K r ^ p *
      exp (I * cuspoidPotential K (cuspoidContour K r) x)‖ =
      |r| ^ p * ‖cuspoidContourDir K r * exp (I * cuspoidPotential K (cuspoidContour K r) x)‖ := by
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_cuspoidContour]; ring
  rw [hsplit]
  have hg : 0 ≤ Real.exp (-(1 / 2) * r ^ 2) := (Real.exp_pos _).le
  have hp : 0 ≤ |r| ^ p := pow_nonneg (abs_nonneg r) p
  calc |r| ^ p * ‖cuspoidContourDir K r * exp (I * cuspoidPotential K (cuspoidContour K r) x)‖
      ≤ |r| ^ p * (Real.exp (1 / 2 + ∑ m, |x m| + (∑ m, |x m|) * (1 + 2 * ∑ m, |x m|) ^ K) *
          Real.exp (-(1 / 2) * r ^ 2)) := mul_le_mul_of_nonneg_left h hp
    _ ≤ |r| ^ p * (Real.exp (1 / 2 + C + C * (1 + 2 * C) ^ K) * Real.exp (-(1 / 2) * r ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmono hg) hp
    _ = _ := by ring

lemma s36b_measurable_moment_integrand (K : ℕ) (x : Fin K → ℝ) (p : ℕ) :
    Measurable fun r : ℝ => cuspoidContourDir K r * cuspoidContour K r ^ p *
      exp (I * cuspoidPotential K (cuspoidContour K r) x) :=
  ((measurable_cuspoidContourDir K).mul ((measurable_cuspoidContour K).pow_const p)).mul
    (measurable_exp.comp (measurable_const.mul
      ((continuous_cuspoidPotential K x).measurable.comp (measurable_cuspoidContour K))))

/-- The moment integrands are integrable. -/
theorem s36b_integrable_moment_integrand (K : ℕ) (x : Fin K → ℝ) (p : ℕ) :
    Integrable fun r : ℝ => cuspoidContourDir K r * cuspoidContour K r ^ p *
      exp (I * cuspoidPotential K (cuspoidContour K r) x) :=
  Integrable.mono' ((s36b_integrable_pow_mul_gauss p).const_mul _)
    (s36b_measurable_moment_integrand K x p).aestronglyMeasurable
    (ae_of_all _ fun r => s36b_norm_moment_integrand_le K x p r le_rfl)

/-- `Ψ_K` is the moment of order `0`. -/
theorem cuspoidIntegral_eq_cuspoidMoment_zero (K : ℕ) (x : Fin K → ℝ) :
    cuspoidIntegral K x = cuspoidMoment K x 0 := by
  simp [cuspoidIntegral, cuspoidMoment]

/-! ### Differentiation under the integral sign -/

/-- The potential is affine in each parameter: `Φ_K(t; x[m ↦ s]) = Φ_K(t; x[m ↦ 0]) + s t^{m+1}`. -/
lemma s36b_potential_update (K : ℕ) (t : ℂ) (x : Fin K → ℝ) (m : Fin K) (s : ℝ) :
    cuspoidPotential K t (update x m s) =
      cuspoidPotential K t (update x m 0) + (s : ℂ) * t ^ ((m : ℕ) + 1) := by
  have key : ∀ s' : ℝ, ∑ j : Fin K, ((update x m s' j : ℝ) : ℂ) * t ^ ((j : ℕ) + 1) =
      (s' : ℂ) * t ^ ((m : ℕ) + 1) +
        ∑ j ∈ Finset.univ.erase m, ((x j : ℝ) : ℂ) * t ^ ((j : ℕ) + 1) := by
    intro s'
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m), update_self]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [update_of_ne (Finset.ne_of_mem_erase hj)]
  unfold cuspoidPotential
  rw [key s, key 0]
  push_cast
  ring

lemma s36b_sum_abs_update_le (K : ℕ) (x : Fin K → ℝ) (m : Fin K) {s : ℝ}
    (hs : |s - x m| ≤ 1) : ∑ j, |update x m s j| ≤ ∑ j, |x j| + 1 := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m), update_self,
    ← Finset.add_sum_erase _ (fun j => |x j|) (Finset.mem_univ m)]
  have hsum : ∑ j ∈ Finset.univ.erase m, |update x m s j| =
      ∑ j ∈ Finset.univ.erase m, |x j| :=
    Finset.sum_congr rfl fun j hj => by rw [update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hsum]
  have := abs_sub_abs_le_abs_sub s (x m)
  linarith

lemma s36b_hasDerivAt_integrand (K : ℕ) (x : Fin K → ℝ) (m : Fin K) (p : ℕ) (r s : ℝ) :
    HasDerivAt (fun s' : ℝ => cuspoidContourDir K r * cuspoidContour K r ^ p *
        exp (I * cuspoidPotential K (cuspoidContour K r) (update x m s')))
      (I * (cuspoidContourDir K r * cuspoidContour K r ^ (p + ((m : ℕ) + 1)) *
        exp (I * cuspoidPotential K (cuspoidContour K r) (update x m s)))) s := by
  set A := cuspoidPotential K (cuspoidContour K r) (update x m 0)
  set B := cuspoidContour K r ^ ((m : ℕ) + 1)
  have hfun : (fun s' : ℝ => cuspoidContourDir K r * cuspoidContour K r ^ p *
      exp (I * cuspoidPotential K (cuspoidContour K r) (update x m s'))) =
      fun s' : ℝ => cuspoidContourDir K r * cuspoidContour K r ^ p * exp (I * (A + (s' : ℂ) * B)) :=
    funext fun s' => by rw [s36b_potential_update K (cuspoidContour K r) x m s']
  rw [hfun, s36b_potential_update K (cuspoidContour K r) x m s]
  have h1 : HasDerivAt (fun s' : ℝ => I * (A + (s' : ℂ) * B)) (I * B) s := by
    have := (((hasDerivAt_id s).ofReal_comp).mul_const B).const_add A
    simpa using this.const_mul I
  have h2 := h1.cexp.const_mul (cuspoidContourDir K r * cuspoidContour K r ^ p)
  convert h2 using 1
  rw [pow_add]; ring

/-- Differentiation under the integral sign: `∂/∂x_m ∫ t^p e^{iΦ_K} = i ∫ t^{p+m+1} e^{iΦ_K}`
(Lean index `m`, DLMF's `x_{m+1}`). -/
theorem hasDerivAt_cuspoidMoment_update (K : ℕ) (x : Fin K → ℝ) (m : Fin K) (p : ℕ) (s₀ : ℝ) :
    HasDerivAt (fun s => cuspoidMoment K (update x m s) p)
      (I * cuspoidMoment K (update x m s₀) (p + ((m : ℕ) + 1))) s₀ := by
  set x' := update x m s₀
  set C := ∑ j, |x' j| + 1
  have hx' : ∀ s, update x m s = update x' m s := fun s => by
    simp only [x', update_idem]
  have hbd : ∀ s ∈ Metric.ball s₀ 1, ∑ j, |update x m s j| ≤ C := by
    intro s hs
    rw [hx']
    have : |s - x' m| ≤ 1 := by
      simp only [x', update_self]; exact (Metric.mem_ball.mp hs).le
    exact s36b_sum_abs_update_le K x' m this
  have hF := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := s₀)
    (F := fun s r => cuspoidContourDir K r * cuspoidContour K r ^ p *
      exp (I * cuspoidPotential K (cuspoidContour K r) (update x m s)))
    (F' := fun s r => I * (cuspoidContourDir K r * cuspoidContour K r ^ (p + ((m : ℕ) + 1)) *
      exp (I * cuspoidPotential K (cuspoidContour K r) (update x m s))))
    (bound := fun r => Real.exp (1 / 2 + C + C * (1 + 2 * C) ^ K) *
      (|r| ^ (p + ((m : ℕ) + 1)) * Real.exp (-(1 / 2) * r ^ 2)))
    (Metric.ball_mem_nhds s₀ one_pos)
    (Eventually.of_forall fun s =>
      (s36b_measurable_moment_integrand K (update x m s) p).aestronglyMeasurable)
    (s36b_integrable_moment_integrand K (update x m s₀) p)
    ((s36b_measurable_moment_integrand K (update x m s₀) _).const_mul I).aestronglyMeasurable
    (ae_of_all _ fun r s hs => by
      rw [norm_mul, norm_I, one_mul]
      exact s36b_norm_moment_integrand_le K _ _ r (hbd s hs))
    ((s36b_integrable_pow_mul_gauss _).const_mul _)
    (ae_of_all _ fun r s _ => s36b_hasDerivAt_integrand K x m p r s)
  have h2 := hF.2
  rw [integral_const_mul] at h2
  exact h2

/-- Iterated derivatives: `∂ⁿ/∂x_mⁿ ∫ t^p e^{iΦ_K} = iⁿ ∫ t^{p + n(m+1)} e^{iΦ_K}`. -/
theorem iteratedDeriv_cuspoidMoment_update (K : ℕ) (x : Fin K → ℝ) (m : Fin K) :
    ∀ (n p : ℕ) (s₀ : ℝ), iteratedDeriv n (fun s => cuspoidMoment K (update x m s) p) s₀ =
      I ^ n * cuspoidMoment K (update x m s₀) (p + n * ((m : ℕ) + 1))
  | 0, p, s₀ => by simp
  | n + 1, p, s₀ => by
    have ih : iteratedDeriv n (fun s => cuspoidMoment K (update x m s) p) =
        fun s => I ^ n * cuspoidMoment K (update x m s) (p + n * ((m : ℕ) + 1)) :=
      funext fun s => iteratedDeriv_cuspoidMoment_update K x m n p s
    rw [iteratedDeriv_succ, ih]
    have hd := (hasDerivAt_cuspoidMoment_update K x m (p + n * ((m : ℕ) + 1)) s₀).const_mul
      (I ^ n)
    rw [hd.deriv, show p + n * ((m : ℕ) + 1) + ((m : ℕ) + 1) = p + (n + 1) * ((m : ℕ) + 1) by
      ring]
    ring

/-- `∂ⁿΨ_K/∂x_mⁿ = iⁿ ∫ t^{n(m+1)} e^{iΦ_K} dt` at `x` (Lean index `m`, DLMF's `x_{m+1}`). -/
theorem iteratedDeriv_cuspoidIntegral_update (K : ℕ) (x : Fin K → ℝ) (m : Fin K) (n : ℕ) :
    iteratedDeriv n (fun s => cuspoidIntegral K (update x m s)) (x m) =
      I ^ n * cuspoidMoment K x (n * ((m : ℕ) + 1)) := by
  simp_rw [cuspoidIntegral_eq_cuspoidMoment_zero]
  rw [iteratedDeriv_cuspoidMoment_update, update_eq_self, zero_add]

/-- Each partial derivative of `Ψ_K` exists: `∂Ψ_K/∂x_m = i ∫ t^{m+1} e^{iΦ_K} dt`. -/
theorem hasDerivAt_cuspoidIntegral_update (K : ℕ) (x : Fin K → ℝ) (m : Fin K) (s₀ : ℝ) :
    HasDerivAt (fun s => cuspoidIntegral K (update x m s))
      (I * cuspoidMoment K (update x m s₀) ((m : ℕ) + 1)) s₀ := by
  simp_rw [cuspoidIntegral_eq_cuspoidMoment_zero]
  simpa using hasDerivAt_cuspoidMoment_update K x m 0 s₀

/-! ### Derivatives at the origin (DLMF 36.2.17) -/

/-- `∂^p Ψ_K/∂x₁^p (0) = i^p ∫ d(r) t(r)^p exp(i t(r)^{K+2}) dr`, evaluated by
`q2s_moment_at_zero` (helper for 36.2.17). -/
lemma q2t_iteratedDeriv_single (K : ℕ) (h0 : 0 < K) (p : ℕ) :
    iteratedDeriv p (fun a : ℝ => cuspoidIntegral K (Pi.single (⟨0, h0⟩ : Fin K) a)) 0 =
      I ^ p * ((exp ((cuspoidAngle K : ℂ) * I) ^ (p + 1) +
        (-1) ^ p * cuspoidContourDir K (-1) ^ (p + 1)) *
        ((1 / ((K : ℝ) + 2) * Real.Gamma ((p + 1) / ((K : ℝ) + 2)) : ℝ) : ℂ)) := by
  have h := iteratedDeriv_cuspoidIntegral_update K 0 ⟨0, h0⟩ p
  have e : (fun a : ℝ => cuspoidIntegral K (Pi.single (⟨0, h0⟩ : Fin K) a)) =
      fun s => cuspoidIntegral K (Function.update 0 ⟨0, h0⟩ s) := rfl
  rw [e]
  simp only [Pi.zero_apply] at h
  rw [h, zero_add, mul_one, cuspoidMoment, q2s_moment_at_zero]

/-- Derivatives at the origin for odd `K` (DLMF 36.2.17, first line):
`∂^p Ψ_K/∂x₁^p (0) = (2/(K+2)) Γ((p+1)/(K+2)) cos((π/2)((p+1)/(K+2) + p))`. -/
@[dlmf 36.2.E17]
theorem iteratedDeriv_cuspoidIntegral_odd {K : ℕ} (hK : ¬ Even K) (h0 : 0 < K) (p : ℕ) :
    iteratedDeriv p (fun a : ℝ => cuspoidIntegral K (Pi.single (⟨0, h0⟩ : Fin K) a)) 0 =
      2 / ((K : ℂ) + 2) * (Real.Gamma ((p + 1) / ((K : ℝ) + 2)) : ℂ) *
        (Real.cos (π / 2 * ((p + 1) / ((K : ℝ) + 2) + p)) : ℂ) := by
  rw [q2t_iteratedDeriv_single, s36a_dir_neg_one, ite_eq_right hK]
  set α : ℝ := π / 2 * ((p + 1) / ((K : ℝ) + 2) + p) with hα
  have hK2 : (K : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : K + 2 ≠ 0)
  have e1 : I ^ p * exp ((cuspoidAngle K : ℂ) * I) ^ (p + 1) = exp ((α : ℂ) * I) := by
    rw [show (cuspoidAngle K : ℂ) * I = ((1 * cuspoidAngle K : ℝ) : ℂ) * I by push_cast; ring,
      q2s_exp_angle_pow, q2s_I_pow, ← exp_add]
    congr 1; rw [hα]; push_cast; field_simp; ring
  have e2 : I ^ p * ((-1) ^ p * exp (-(cuspoidAngle K : ℂ) * I) ^ (p + 1)) =
      exp (-(α : ℂ) * I) := by
    rw [show -(cuspoidAngle K : ℂ) * I = ((-1 * cuspoidAngle K : ℝ) : ℂ) * I by push_cast; ring,
      q2s_exp_angle_pow, ← mul_assoc, mul_comm (I ^ p), q2s_negI_pow, ← exp_add]
    congr 1; rw [hα]; push_cast; field_simp; ring
  rw [ofReal_cos, Complex.cos]
  push_cast
  linear_combination (1 / ((K : ℂ) + 2) * (Real.Gamma ((p + 1) / ((K : ℝ) + 2)) : ℂ)) * (e1 + e2)

/-- Derivatives at the origin for even `K` (DLMF 36.2.17, second and third lines): the odd
derivatives vanish and `∂^{2q} Ψ_K/∂x₁^{2q} (0) = (2/(K+2)) Γ((2q+1)/(K+2))
exp(i(π/2)((2q+1)/(K+2) + 2q))`. -/
@[dlmf 36.2.E17]
theorem iteratedDeriv_cuspoidIntegral_even {K : ℕ} (hK : Even K) (h0 : 0 < K) (q : ℕ) :
    iteratedDeriv (2 * q + 1)
        (fun a : ℝ => cuspoidIntegral K (Pi.single (⟨0, h0⟩ : Fin K) a)) 0 = 0 ∧
      iteratedDeriv (2 * q)
        (fun a : ℝ => cuspoidIntegral K (Pi.single (⟨0, h0⟩ : Fin K) a)) 0 =
      2 / ((K : ℂ) + 2) * (Real.Gamma ((2 * q + 1) / ((K : ℝ) + 2)) : ℂ) *
        exp (I * (π / 2 * ((2 * q + 1) / ((K : ℂ) + 2) + 2 * q))) := by
  refine ⟨?_, ?_⟩
  · rw [q2t_iteratedDeriv_single, s36a_dir_neg_one, ite_eq_left hK,
      show (-1 : ℂ) ^ (2 * q + 1) = -1 by rw [pow_succ, pow_mul]; norm_num]
    ring
  · rw [q2t_iteratedDeriv_single, s36a_dir_neg_one, ite_eq_left hK,
      show (-1 : ℂ) ^ (2 * q) = 1 by rw [pow_mul]; norm_num]
    have hK2 : (K : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : K + 2 ≠ 0)
    have e1 : I ^ (2 * q) * exp ((cuspoidAngle K : ℂ) * I) ^ (2 * q + 1) =
        exp (I * (π / 2 * ((2 * q + 1) / ((K : ℂ) + 2) + 2 * q))) := by
      rw [show (cuspoidAngle K : ℂ) * I = ((1 * cuspoidAngle K : ℝ) : ℂ) * I by push_cast; ring,
        q2s_exp_angle_pow, q2s_I_pow, ← exp_add]
      congr 1; push_cast; field_simp; ring
    push_cast
    linear_combination (2 / ((K : ℂ) + 2) *
      (Real.Gamma ((2 * q + 1) / ((K : ℝ) + 2)) : ℂ)) * e1

/-! ### Integration by parts along the contour -/

/-- The `t`-derivative of the cuspoid potential:
`∂Φ_K/∂t = (K+2) t^{K+1} + ∑ₘ m xₘ t^{m-1}` (Lean index `m`, coefficient `(m+1) x_m t^m`). -/
theorem hasDerivAt_cuspoidPotential (K : ℕ) (x : Fin K → ℝ) (t : ℂ) :
    HasDerivAt (fun u => cuspoidPotential K u x)
      (((K : ℂ) + 2) * t ^ (K + 1) +
        ∑ m : Fin K, (((m : ℕ) : ℂ) + 1) * ((x m : ℝ) : ℂ) * t ^ (m : ℕ)) t := by
  unfold cuspoidPotential
  have h1 := hasDerivAt_pow (K + 2) t
  have h2 : HasDerivAt (fun u => ∑ m : Fin K, ((x m : ℝ) : ℂ) * u ^ ((m : ℕ) + 1))
      (∑ m : Fin K, (((m : ℕ) : ℂ) + 1) * ((x m : ℝ) : ℂ) * t ^ (m : ℕ)) t := by
    apply HasDerivAt.fun_sum
    intro m _
    have := (hasDerivAt_pow ((m : ℕ) + 1) t).const_mul ((x m : ℝ) : ℂ)
    convert this using 1
    simp only [Nat.add_sub_cancel]; push_cast; ring
  convert h1.add h2 using 1
  rw [show K + 2 - 1 = K + 1 by omega]; push_cast; ring

lemma s36b_dir_pos (K : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    cuspoidContourDir K y = cuspoidContourDir K 1 := by
  rw [s36a_dir_of_nonneg K hy, s36a_dir_of_nonneg K zero_le_one]

lemma s36b_dir_neg (K : ℕ) {y : ℝ} (hy : y < 0) :
    cuspoidContourDir K y = cuspoidContourDir K (-1) := by
  unfold cuspoidContourDir
  simp [not_le.mpr hy, show ¬ ((1 : ℝ) ≤ 0) by norm_num]

lemma s36b_hasDerivAt_exp_line {P P' : ℂ → ℂ} (hP : ∀ u, HasDerivAt P (P' u) u) (ω : ℂ)
    (r : ℝ) :
    HasDerivAt (fun r : ℝ => exp (I * P ((r : ℂ) * ω)))
      (I * (ω * P' ((r : ℂ) * ω) * exp (I * P ((r : ℂ) * ω)))) r := by
  have hl : HasDerivAt (fun r : ℝ => (r : ℂ) * ω) ω r := by
    simpa using ((hasDerivAt_id r).ofReal_comp).mul_const ω
  have h := (((hP ((r : ℂ) * ω)).comp r hl).const_mul I).cexp
  simp only [Function.comp_def] at h
  convert h using 1
  ring

lemma s36b_continuous_exp_line {P P' : ℂ → ℂ} (hP : ∀ u, HasDerivAt P (P' u) u) (ω : ℂ) :
    Continuous fun r : ℝ => exp (I * P ((r : ℂ) * ω)) :=
  continuous_exp.comp (continuous_const.mul
    ((continuous_iff_continuousAt.mpr fun u => (hP u).continuousAt).comp
      (continuous_ofReal.mul continuous_const)))

lemma s36b_tendsto_exp_potential (K : ℕ) (x : Fin K → ℝ) {l : Filter ℝ}
    (hl : Tendsto (fun r : ℝ => -(1 / 2) * r ^ 2) l atBot) :
    Tendsto (fun r => exp (I * cuspoidPotential K (cuspoidContour K r) x)) l (𝓝 0) := by
  set A := Real.exp (1 / 2 + ∑ m, |x m| + (∑ m, |x m|) * (1 + 2 * ∑ m, |x m|) ^ K)
  have hb : Tendsto (fun r : ℝ => A * Real.exp (-(1 / 2) * r ^ 2)) l (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp hl).const_mul A
  refine squeeze_zero_norm (fun r => ?_) hb
  have h := s36a_norm_integrand_le K x one_pos r
  simp only [ofReal_one, mul_one, one_mul, norm_mul, norm_cuspoidContourDir] at h
  exact h

lemma s36b_tendsto_neg_half_sq_atTop : Tendsto (fun r : ℝ => -(1 / 2) * r ^ 2) atTop atBot :=
  (tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by norm_num)

lemma s36b_tendsto_neg_half_sq_atBot : Tendsto (fun r : ℝ => -(1 / 2) * r ^ 2) atBot atBot := by
  have h2 : Tendsto (fun r : ℝ => r ^ 2) atBot atTop :=
    ((tendsto_pow_atTop two_ne_zero).comp tendsto_abs_atBot_atTop).congr fun r => by
      simp [sq_abs]
  exact h2.const_mul_atTop_of_neg (by norm_num)

/-- Integration by parts along the rotated contour of `cuspoidIntegral K`, for an entire phase
`P`: if `exp(iP(t))` tends to `0` at both ends of the contour and `P'(t) exp(iP(t))` is
integrable along it, then `∫ P'(t) exp(iP(t)) dt = 0` (the integrand is `-i d/dt exp(iP)`). -/
lemma s36b_contour_ibp (K : ℕ) {P P' : ℂ → ℂ} (hP : ∀ u, HasDerivAt P (P' u) u)
    (hint : Integrable fun r : ℝ => cuspoidContourDir K r * P' (cuspoidContour K r) *
      exp (I * P (cuspoidContour K r)))
    (htop : Tendsto (fun r : ℝ => exp (I * P (cuspoidContour K r))) atTop (𝓝 0))
    (hbot : Tendsto (fun r : ℝ => exp (I * P (cuspoidContour K r))) atBot (𝓝 0)) :
    ∫ r : ℝ, cuspoidContourDir K r * P' (cuspoidContour K r) *
      exp (I * P (cuspoidContour K r)) = 0 := by
  set G : ℝ → ℂ := fun r => exp (I * P (cuspoidContour K r)) with hG
  set f : ℝ → ℂ := fun r => cuspoidContourDir K r * P' (cuspoidContour K r) * G r with hf
  have hderivR : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt G (I * f r) r := by
    intro r hr
    have h := s36b_hasDerivAt_exp_line hP (cuspoidContourDir K 1) r
    have heq : G =ᶠ[𝓝 r] fun r : ℝ => exp (I * P ((r : ℂ) * cuspoidContourDir K 1)) := by
      filter_upwards [Ioi_mem_nhds hr] with y hy
      simp only [hG, cuspoidContour, s36b_dir_pos K (le_of_lt hy)]
    have hfr : f r = cuspoidContourDir K 1 * P' ((r : ℂ) * cuspoidContourDir K 1) *
        exp (I * P ((r : ℂ) * cuspoidContourDir K 1)) := by
      simp only [hf, hG, cuspoidContour, s36b_dir_pos K (le_of_lt hr)]
    rw [hfr]
    exact h.congr_of_eventuallyEq heq
  have hderivL : ∀ r ∈ Iio (0 : ℝ), HasDerivAt G (I * f r) r := by
    intro r hr
    have h := s36b_hasDerivAt_exp_line hP (cuspoidContourDir K (-1)) r
    have heq : G =ᶠ[𝓝 r] fun r : ℝ => exp (I * P ((r : ℂ) * cuspoidContourDir K (-1))) := by
      filter_upwards [Iio_mem_nhds hr] with y hy
      simp only [hG, cuspoidContour, s36b_dir_neg K hy]
    have hfr : f r = cuspoidContourDir K (-1) * P' ((r : ℂ) * cuspoidContourDir K (-1)) *
        exp (I * P ((r : ℂ) * cuspoidContourDir K (-1))) := by
      simp only [hf, hG, cuspoidContour, s36b_dir_neg K hr]
    rw [hfr]
    exact h.congr_of_eventuallyEq heq
  have hcontR : ContinuousWithinAt G (Ici 0) 0 := by
    refine ((s36b_continuous_exp_line hP (cuspoidContourDir K 1)).continuousWithinAt).congr
      (fun y hy => ?_) ?_
    · simp only [hG, cuspoidContour, s36b_dir_pos K (show (0 : ℝ) ≤ y from hy)]
    · simp only [hG, cuspoidContour, s36b_dir_pos K le_rfl]
  have hcontL : ContinuousWithinAt G (Iic 0) 0 := by
    refine ((s36b_continuous_exp_line hP (cuspoidContourDir K (-1))).continuousWithinAt).congr
      (fun y hy => ?_) ?_
    · rcases (show y ≤ 0 from hy).lt_or_eq with hy | hy
      · simp only [hG, cuspoidContour, s36b_dir_neg K hy]
      · subst hy; simp [hG, cuspoidContour]
    · simp [hG, cuspoidContour]
  have hIf : Integrable fun r => I * f r := hint.const_mul I
  have hR := integral_Ioi_of_hasDerivAt_of_tendsto hcontR hderivR hIf.integrableOn htop
  have hL := integral_Iic_of_hasDerivAt_of_tendsto hcontL hderivL hIf.integrableOn hbot
  have htot := intervalIntegral.integral_Iic_add_Ioi (b := 0) (μ := volume) hIf.integrableOn
    hIf.integrableOn
  rw [hR, hL, integral_const_mul] at htot
  have : I * ∫ r, f r = 0 := by rw [← htot]; ring
  exact (mul_eq_zero.mp this).resolve_left I_ne_zero

/-- Integration by parts along the contour:
`∫ (∂Φ_K/∂t)(t; x) exp(iΦ_K(t; x)) dt = 0`, i.e.
`(K+2) M_{K+1} + ∑ₘ m xₘ M_{m-1} = 0` for the moments `M_p = ∫ t^p exp(iΦ_K) dt`. -/
theorem cuspoidMoment_ibp (K : ℕ) (x : Fin K → ℝ) :
    ((K : ℂ) + 2) * cuspoidMoment K x (K + 1) +
      ∑ m : Fin K, (((m : ℕ) : ℂ) + 1) * ((x m : ℝ) : ℂ) * cuspoidMoment K x m = 0 := by
  set Φ' : ℂ → ℂ := fun t => ((K : ℂ) + 2) * t ^ (K + 1) +
    ∑ m : Fin K, (((m : ℕ) : ℂ) + 1) * ((x m : ℝ) : ℂ) * t ^ (m : ℕ) with hΦ'def
  set f : ℝ → ℂ := fun r => cuspoidContourDir K r * Φ' (cuspoidContour K r) *
    exp (I * cuspoidPotential K (cuspoidContour K r) x) with hf
  have hfeq : f = fun r => ((K : ℂ) + 2) * (cuspoidContourDir K r * cuspoidContour K r ^ (K + 1) *
      exp (I * cuspoidPotential K (cuspoidContour K r) x)) +
      ∑ m : Fin K, (((m : ℕ) : ℂ) + 1) * ((x m : ℝ) : ℂ) *
        (cuspoidContourDir K r * cuspoidContour K r ^ (m : ℕ) *
          exp (I * cuspoidPotential K (cuspoidContour K r) x)) := by
    funext r
    simp only [hf, hΦ'def, add_mul, mul_add, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun m _ => by ring
  have hint_sum : Integrable fun r => ∑ m : Fin K, (((m : ℕ) : ℂ) + 1) * ((x m : ℝ) : ℂ) *
      (cuspoidContourDir K r * cuspoidContour K r ^ (m : ℕ) *
        exp (I * cuspoidPotential K (cuspoidContour K r) x)) :=
    integrable_finsetSum _ fun m _ => (s36b_integrable_moment_integrand K x m).const_mul _
  have hfint : Integrable f := by
    rw [hfeq]
    exact ((s36b_integrable_moment_integrand K x (K + 1)).const_mul _).add hint_sum
  have hcomb : ((K : ℂ) + 2) * cuspoidMoment K x (K + 1) +
      ∑ m : Fin K, (((m : ℕ) : ℂ) + 1) * ((x m : ℝ) : ℂ) * cuspoidMoment K x m = ∫ r, f r := by
    rw [hfeq, integral_add ((s36b_integrable_moment_integrand K x (K + 1)).const_mul _) hint_sum,
      integral_const_mul, integral_finsetSum Finset.univ fun (m : Fin K) _ =>
        (s36b_integrable_moment_integrand K x (m : ℕ)).const_mul
          ((((m : ℕ) : ℂ) + 1) * ((x m : ℝ) : ℂ))]
    simp_rw [integral_const_mul]
    rfl
  rw [hcomb]
  exact s36b_contour_ibp K (hasDerivAt_cuspoidPotential K x) hfint
    (s36b_tendsto_exp_potential K x s36b_tendsto_neg_half_sq_atTop)
    (s36b_tendsto_exp_potential K x s36b_tendsto_neg_half_sq_atBot)

/-! ### §36.10(i): equations for `Ψ_K` -/

lemma s36b_iteratedDeriv_vec (K : ℕ) (v : Fin K → ℝ) (m : Fin K) (n : ℕ) {g : ℝ → ℂ}
    (hg : ∀ s, g s = cuspoidIntegral K (update v m s)) :
    iteratedDeriv n g (v m) = I ^ n * cuspoidMoment K v (n * ((m : ℕ) + 1)) := by
  rw [show g = fun s => cuspoidIntegral K (update v m s) from funext hg]
  exact iteratedDeriv_cuspoidIntegral_update K v m n

theorem s36b_negI_pow_mul_I_pow (n : ℕ) : (-I) ^ n * I ^ n = 1 := by
  rw [← mul_pow]; simp

/-- The operator equation `Φ_K'(-i ∂/∂x₁; x) Ψ_K(x) = 0` (DLMF 36.10.1), where
`Φ_K'(t; x) = ∂Φ_K/∂t = (K+2) t^{K+1} + ∑_{m=1}^K m xₘ t^{m-1}` (Lean index `m`: the coefficient
`(m+1) x_m` of `t^m`), for `K ≥ 1`. The derivatives in `x₁` (Lean `x 0`) exist
(`hasDerivAt_cuspoidIntegral_update`). -/
@[dlmf 36.10.E1]
theorem cuspoidIntegral_operator_eq (K : ℕ) (hK : 0 < K) (x : Fin K → ℝ) :
    ((K : ℂ) + 2) * (-I) ^ (K + 1) *
        iteratedDeriv (K + 1) (fun s => cuspoidIntegral K (update x ⟨0, hK⟩ s)) (x ⟨0, hK⟩) +
      ∑ m : Fin K, (((m : ℕ) : ℂ) + 1) * ((x m : ℝ) : ℂ) * (-I) ^ (m : ℕ) *
        iteratedDeriv m (fun s => cuspoidIntegral K (update x ⟨0, hK⟩ s)) (x ⟨0, hK⟩) = 0 := by
  have hd : ∀ n, iteratedDeriv n (fun s => cuspoidIntegral K (update x ⟨0, hK⟩ s))
      (x ⟨0, hK⟩) = I ^ n * cuspoidMoment K x n := fun n => by
    rw [iteratedDeriv_cuspoidIntegral_update]; simp
  simp_rw [hd]
  have h1 : ((K : ℂ) + 2) * (-I) ^ (K + 1) * (I ^ (K + 1) * cuspoidMoment K x (K + 1)) =
      ((K : ℂ) + 2) * cuspoidMoment K x (K + 1) := by
    calc _ = ((K : ℂ) + 2) * ((-I) ^ (K + 1) * I ^ (K + 1)) * cuspoidMoment K x (K + 1) := by
          ring
      _ = _ := by rw [s36b_negI_pow_mul_I_pow, mul_one]
  have h2 : ∀ m : Fin K, (((m : ℕ) : ℂ) + 1) * ((x m : ℝ) : ℂ) * (-I) ^ (m : ℕ) *
      (I ^ (m : ℕ) * cuspoidMoment K x m) =
      (((m : ℕ) : ℂ) + 1) * ((x m : ℝ) : ℂ) * cuspoidMoment K x m := fun m => by
    calc _ = (((m : ℕ) : ℂ) + 1) * ((x m : ℝ) : ℂ) * ((-I) ^ (m : ℕ) * I ^ (m : ℕ)) *
          cuspoidMoment K x m := by ring
      _ = _ := by rw [s36b_negI_pow_mul_I_pow, mul_one]
  rw [h1, Finset.sum_congr rfl fun m _ => h2 m]
  exact cuspoidMoment_ibp K x

/-- The ordinary differential equation in `x₁` (DLMF 36.10.2):
`∂^{K+1}Ψ_K/∂x₁^{K+1} + ∑_{m=1}^K (-i)^{m-K-2} (m xₘ/(K+2)) ∂^{m-1}Ψ_K/∂x₁^{m-1} = 0`, for
`K ≥ 1`. In Lean the sum runs over `m : Fin K` (DLMF's `m + 1`), so the power of `-i` is the
integer `m - K - 1`. -/
@[dlmf 36.10.E2]
theorem cuspoidIntegral_ode (K : ℕ) (hK : 0 < K) (x : Fin K → ℝ) :
    iteratedDeriv (K + 1) (fun s => cuspoidIntegral K (update x ⟨0, hK⟩ s)) (x ⟨0, hK⟩) +
      ∑ m : Fin K, (-I) ^ ((m : ℤ) - K - 1) *
        ((((m : ℕ) : ℂ) + 1) * ((x m : ℝ) : ℂ) / ((K : ℂ) + 2)) *
        iteratedDeriv m (fun s => cuspoidIntegral K (update x ⟨0, hK⟩ s)) (x ⟨0, hK⟩) = 0 := by
  have hd : ∀ n, iteratedDeriv n (fun s => cuspoidIntegral K (update x ⟨0, hK⟩ s))
      (x ⟨0, hK⟩) = I ^ n * cuspoidMoment K x n := fun n => by
    rw [iteratedDeriv_cuspoidIntegral_update]; simp
  simp_rw [hd]
  have hK2 : (K : ℂ) + 2 ≠ 0 := by norm_cast
  have hnI : (-I) ≠ 0 := neg_ne_zero.mpr I_ne_zero
  set u := ((-I) ^ (K + 1))⁻¹ with hu
  have hIu : I ^ (K + 1) = u := by
    rw [hu]; exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact s36b_negI_pow_mul_I_pow _)
  have hz : ∀ m : Fin K, (-I) ^ ((m : ℤ) - K - 1) = (-I) ^ (m : ℕ) * u := fun m => by
    rw [show (m : ℤ) - K - 1 = ((m : ℕ) : ℤ) - ((K + 1 : ℕ) : ℤ) by push_cast; ring,
      zpow_sub₀ hnI, zpow_natCast, zpow_natCast, hu, div_eq_mul_inv]
  have h2 : ∀ m : Fin K, (-I) ^ ((m : ℤ) - K - 1) *
      ((((m : ℕ) : ℂ) + 1) * ((x m : ℝ) : ℂ) / ((K : ℂ) + 2)) *
      (I ^ (m : ℕ) * cuspoidMoment K x m) =
      u / ((K : ℂ) + 2) * ((((m : ℕ) : ℂ) + 1) * ((x m : ℝ) : ℂ) * cuspoidMoment K x m) :=
    fun m => by
      rw [hz]
      calc _ = ((-I) ^ (m : ℕ) * I ^ (m : ℕ)) * u / ((K : ℂ) + 2) *
            ((((m : ℕ) : ℂ) + 1) * ((x m : ℝ) : ℂ) * cuspoidMoment K x m) := by ring
        _ = _ := by rw [s36b_negI_pow_mul_I_pow, one_mul]
  rw [Finset.sum_congr rfl fun m _ => h2 m, ← Finset.mul_sum, hIu]
  have h := cuspoidMoment_ibp K x
  calc u * cuspoidMoment K x (K + 1) + u / ((K : ℂ) + 2) *
        ∑ m : Fin K, (((m : ℕ) : ℂ) + 1) * ((x m : ℝ) : ℂ) * cuspoidMoment K x m
      = u / ((K : ℂ) + 2) * (((K : ℂ) + 2) * cuspoidMoment K x (K + 1) +
        ∑ m : Fin K, (((m : ℕ) : ℂ) + 1) * ((x m : ℝ) : ℂ) * cuspoidMoment K x m) := by
        field_simp
    _ = 0 := by rw [h, mul_zero]

/-- The fold case of 36.10.1: Airy's equation `∂²Ψ₁/∂x² - (x/3) Ψ₁ = 0` (DLMF 36.10.3). -/
@[dlmf 36.10.E3]
theorem cuspoidIntegral_one_ode (x : ℝ) :
    iteratedDeriv 2 (fun s => cuspoidIntegral 1 ![s]) x - x / 3 * cuspoidIntegral 1 ![x] = 0 := by
  have hu : ∀ s : ℝ, cuspoidIntegral 1 ![s] = cuspoidIntegral 1 (update ![x] 0 s) := fun s => by
    congr 1; funext i; fin_cases i; rfl
  have h2 := s36b_iteratedDeriv_vec 1 ![x] 0 2 hu
  have h0 := s36b_iteratedDeriv_vec 1 ![x] 0 0 hu
  simp only [Matrix.cons_val_fin_one, iteratedDeriv_zero, Fin.val_zero] at h2 h0
  have h := cuspoidMoment_ibp 1 ![x]
  simp only [Fin.sum_univ_one, Fin.val_zero, Matrix.cons_val_fin_one] at h
  rw [h2, h0]
  norm_num at h ⊢
  linear_combination (-1 / 3 : ℂ) * h

/-- The cusp case of 36.10.1:
`∂³Ψ₂/∂x³ - (y/2) ∂Ψ₂/∂x - (i/4) x Ψ₂ = 0` (DLMF 36.10.4). -/
@[dlmf 36.10.E4]
theorem cuspoidIntegral_two_ode (x y : ℝ) :
    iteratedDeriv 3 (fun s => cuspoidIntegral 2 ![s, y]) x -
      y / 2 * deriv (fun s => cuspoidIntegral 2 ![s, y]) x -
      I / 4 * x * cuspoidIntegral 2 ![x, y] = 0 := by
  have hu : ∀ s : ℝ, cuspoidIntegral 2 ![s, y] = cuspoidIntegral 2 (update ![x, y] 0 s) :=
    fun s => by congr 1; funext i; fin_cases i <;> rfl
  have h3 := s36b_iteratedDeriv_vec 2 ![x, y] 0 3 hu
  have h1 := s36b_iteratedDeriv_vec 2 ![x, y] 0 1 hu
  have h0 := s36b_iteratedDeriv_vec 2 ![x, y] 0 0 hu
  simp only [Matrix.cons_val_zero, iteratedDeriv_zero, iteratedDeriv_one, Fin.val_zero] at h3 h1 h0
  have h := cuspoidMoment_ibp 2 ![x, y]
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
  rw [h3, h1, h0]
  norm_num at h ⊢
  linear_combination (-I / 4) * h

/-- The swallowtail case of 36.10.1:
`∂⁴Ψ₃/∂x⁴ - (3/5) z ∂²Ψ₃/∂x² - (2i/5) y ∂Ψ₃/∂x + (1/5) x Ψ₃ = 0` (DLMF 36.10.5). -/
@[dlmf 36.10.E5]
theorem cuspoidIntegral_three_ode (x y z : ℝ) :
    iteratedDeriv 4 (fun s => cuspoidIntegral 3 ![s, y, z]) x -
      3 / 5 * z * iteratedDeriv 2 (fun s => cuspoidIntegral 3 ![s, y, z]) x -
      2 * I / 5 * y * deriv (fun s => cuspoidIntegral 3 ![s, y, z]) x +
      x / 5 * cuspoidIntegral 3 ![x, y, z] = 0 := by
  have hu : ∀ s : ℝ, cuspoidIntegral 3 ![s, y, z] =
      cuspoidIntegral 3 (update ![x, y, z] 0 s) :=
    fun s => by congr 1; funext i; fin_cases i <;> rfl
  have h4 := s36b_iteratedDeriv_vec 3 ![x, y, z] 0 4 hu
  have h2 := s36b_iteratedDeriv_vec 3 ![x, y, z] 0 2 hu
  have h1 := s36b_iteratedDeriv_vec 3 ![x, y, z] 0 1 hu
  have h0 := s36b_iteratedDeriv_vec 3 ![x, y, z] 0 0 hu
  simp only [Matrix.cons_val_zero, iteratedDeriv_zero, iteratedDeriv_one,
    Fin.val_zero] at h4 h2 h1 h0
  have h := cuspoidMoment_ibp 3 ![x, y, z]
  simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h
  rw [h4, h2, h1, h0]
  norm_num at h ⊢
  linear_combination (1 / 5 : ℂ) * h +
    (-2 / 5 * (y : ℂ) * cuspoidMoment 3 ![x, y, z] 1) * I_sq

/-! ### §36.10(ii): partial derivatives with respect to the `xₙ` -/

/-- `∂^{ln}Ψ_K/∂x_m^{ln} = i^{n(l-m)} ∂^{mn}Ψ_K/∂x_l^{mn}` for `1 ≤ m, l ≤ K` (DLMF 36.10.6). In
Lean `m l : Fin K` are DLMF's `m - 1`, `l - 1`; both sides equal `i^{ln} ∫ t^{lmn} e^{iΦ_K} dt`. -/
@[dlmf 36.10.E6]
theorem cuspoidIntegral_iteratedDeriv_swap (K : ℕ) (x : Fin K → ℝ) (m l : Fin K) (n : ℕ) :
    iteratedDeriv (((l : ℕ) + 1) * n) (fun s => cuspoidIntegral K (update x m s)) (x m) =
      I ^ ((n : ℤ) * (((l : ℕ) : ℤ) - ((m : ℕ) : ℤ))) *
        iteratedDeriv (((m : ℕ) + 1) * n) (fun s => cuspoidIntegral K (update x l s)) (x l) := by
  rw [iteratedDeriv_cuspoidIntegral_update, iteratedDeriv_cuspoidIntegral_update,
    show ((m : ℕ) + 1) * n * ((l : ℕ) + 1) = ((l : ℕ) + 1) * n * ((m : ℕ) + 1) by ring,
    ← mul_assoc, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ I_ne_zero]
  congr 2
  push_cast; ring

/-- The cusp case of 36.10.6: `∂^{2n}Ψ₂/∂x^{2n} = iⁿ ∂ⁿΨ₂/∂yⁿ` (DLMF 36.10.7). -/
@[dlmf 36.10.E7]
theorem cuspoidIntegral_two_iteratedDeriv (x y : ℝ) (n : ℕ) :
    iteratedDeriv (2 * n) (fun s => cuspoidIntegral 2 ![s, y]) x =
      I ^ n * iteratedDeriv n (fun s => cuspoidIntegral 2 ![x, s]) y := by
  have hx := s36b_iteratedDeriv_vec 2 ![x, y] 0 (2 * n) (g := fun s => cuspoidIntegral 2 ![s, y])
    fun s => by congr 1; funext i; fin_cases i <;> rfl
  have hy := s36b_iteratedDeriv_vec 2 ![x, y] 1 n (g := fun s => cuspoidIntegral 2 ![x, s])
    fun s => by congr 1; funext i; fin_cases i <;> rfl
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.val_zero,
    Fin.val_one] at hx hy
  rw [hx, hy, pow_mul, ← mul_assoc, ← pow_add,
    show 2 * n * (0 + 1) = n * (1 + 1) by ring]
  ring_nf

/-- The swallowtail case of 36.10.6: `∂^{2n}Ψ₃/∂x^{2n} = iⁿ ∂ⁿΨ₃/∂yⁿ` (DLMF 36.10.8). -/
@[dlmf 36.10.E8]
theorem cuspoidIntegral_three_iteratedDeriv_xy (x y z : ℝ) (n : ℕ) :
    iteratedDeriv (2 * n) (fun s => cuspoidIntegral 3 ![s, y, z]) x =
      I ^ n * iteratedDeriv n (fun s => cuspoidIntegral 3 ![x, s, z]) y := by
  have hx := s36b_iteratedDeriv_vec 3 ![x, y, z] 0 (2 * n)
    (g := fun s => cuspoidIntegral 3 ![s, y, z]) fun s => by
      congr 1; funext i; fin_cases i <;> rfl
  have hy := s36b_iteratedDeriv_vec 3 ![x, y, z] 1 n
    (g := fun s => cuspoidIntegral 3 ![x, s, z]) fun s => by
      congr 1; funext i; fin_cases i <;> rfl
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_zero, Fin.val_one] at hx hy
  rw [hx, hy, show 2 * n * (0 + 1) = n * (1 + 1) by ring]
  ring

/-- The swallowtail case of 36.10.6: `∂^{3n}Ψ₃/∂x^{3n} = (-1)ⁿ ∂ⁿΨ₃/∂zⁿ` (DLMF 36.10.9). -/
@[dlmf 36.10.E9]
theorem cuspoidIntegral_three_iteratedDeriv_xz (x y z : ℝ) (n : ℕ) :
    iteratedDeriv (3 * n) (fun s => cuspoidIntegral 3 ![s, y, z]) x =
      (-1) ^ n * iteratedDeriv n (fun s => cuspoidIntegral 3 ![x, y, s]) z := by
  have hx := s36b_iteratedDeriv_vec 3 ![x, y, z] 0 (3 * n)
    (g := fun s => cuspoidIntegral 3 ![s, y, z]) fun s => by
      congr 1; funext i; fin_cases i <;> rfl
  have hz := s36b_iteratedDeriv_vec 3 ![x, y, z] 2 n
    (g := fun s => cuspoidIntegral 3 ![x, y, s]) fun s => by
      congr 1; funext i; fin_cases i <;> rfl
  simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
    Fin.val_zero, Fin.val_two] at hx hz
  rw [hx, hz, show 3 * n * (0 + 1) = n * (2 + 1) by ring, pow_mul, ← mul_assoc]
  congr 1
  rw [show I ^ 3 = -I by rw [pow_succ, I_sq]; ring, neg_pow]

/-- The swallowtail case of 36.10.6: `∂^{3n}Ψ₃/∂y^{3n} = iⁿ ∂^{2n}Ψ₃/∂z^{2n}` (DLMF 36.10.10). -/
@[dlmf 36.10.E10]
theorem cuspoidIntegral_three_iteratedDeriv_yz (x y z : ℝ) (n : ℕ) :
    iteratedDeriv (3 * n) (fun s => cuspoidIntegral 3 ![x, s, z]) y =
      I ^ n * iteratedDeriv (2 * n) (fun s => cuspoidIntegral 3 ![x, y, s]) z := by
  have hy := s36b_iteratedDeriv_vec 3 ![x, y, z] 1 (3 * n)
    (g := fun s => cuspoidIntegral 3 ![x, s, z]) fun s => by
      congr 1; funext i; fin_cases i <;> rfl
  have hz := s36b_iteratedDeriv_vec 3 ![x, y, z] 2 (2 * n)
    (g := fun s => cuspoidIntegral 3 ![x, y, s]) fun s => by
      congr 1; funext i; fin_cases i <;> rfl
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, Fin.val_one, Fin.val_two] at hy hz
  rw [hy, hz, show 3 * n * (1 + 1) = 2 * n * (2 + 1) by ring, ← mul_assoc, ← pow_add]
  congr 2
  ring

/-! ### Helpers: the hyperbolic umbilic integrand

On the product of the cubic V-contours, `s = σ d(σ)`, `t = τ d(τ)`, the cubic part of
`Φ^{(H)}` has imaginary part `|σ|³ + |τ|³`, so all moments `∫∫ s^a t^b exp(iΦ^{(H)})` converge
absolutely, uniformly for bounded parameters. -/

theorem s36b_cubic_le {a C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) :
    (C / 2 + 1 / 2) * a ^ 2 + C * a ≤ a ^ 3 + ((3 * C + 1) / 2) ^ 3 + (3 * C + 1) / 2 := by
  set B := (3 * C + 1) / 2 with hB
  have hB0 : 0 ≤ B := by positivity
  have h1 : C * a ≤ C + C * a ^ 2 := by nlinarith [sq_nonneg (a - 1 / 2)]
  have h2 : B * a ^ 2 ≤ a ^ 3 + B ^ 3 := by
    rcases le_total B a with h | h
    · nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg a), pow_nonneg hB0 3]
    · have h3 : a ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ ha h 2
      nlinarith [mul_le_mul_of_nonneg_left h3 hB0, pow_nonneg ha 3]
  nlinarith

lemma s36b_im_hyperbolic_ge (σ τ x y z : ℝ) :
    |σ| ^ 3 + |τ| ^ 3 - |z| * |σ| * |τ| - |y| * |τ| - |x| * |σ| ≤
      (hyperbolicUmbilicPotential (cuspoidContour 1 σ) (cuspoidContour 1 τ) x y z).im := by
  have hs : cuspoidContour 1 σ ^ 3 = I * ((|σ| ^ 3 : ℝ) : ℂ) := cuspoidContour_pow 1 σ
  have ht : cuspoidContour 1 τ ^ 3 = I * ((|τ| ^ 3 : ℝ) : ℂ) := cuspoidContour_pow 1 τ
  unfold hyperbolicUmbilicPotential
  rw [hs, ht]
  simp only [add_im, I_mul_im, ofReal_re]
  have e1 := abs_im_le_norm ((z : ℂ) * cuspoidContour 1 σ * cuspoidContour 1 τ)
  have e2 := abs_im_le_norm ((y : ℂ) * cuspoidContour 1 τ)
  have e3 := abs_im_le_norm ((x : ℂ) * cuspoidContour 1 σ)
  simp only [norm_mul, norm_real, Real.norm_eq_abs, norm_cuspoidContour] at e1 e2 e3
  linarith [neg_abs_le ((z : ℂ) * cuspoidContour 1 σ * cuspoidContour 1 τ).im,
    neg_abs_le ((y : ℂ) * cuspoidContour 1 τ).im, neg_abs_le ((x : ℂ) * cuspoidContour 1 σ).im]

/-- Gaussian bound for the hyperbolic umbilic moment integrands, uniform for
`|x|, |y|, |z| ≤ C`. -/
lemma s36b_norm_hyperbolic_integrand_le (σ τ x y z : ℝ) (a b : ℕ) {C : ℝ} (hC0 : 0 ≤ C)
    (hx : |x| ≤ C) (hy : |y| ≤ C) (hz : |z| ≤ C) :
    ‖cuspoidContourDir 1 σ * cuspoidContourDir 1 τ *
        (cuspoidContour 1 σ ^ a * cuspoidContour 1 τ ^ b) *
        exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 σ) (cuspoidContour 1 τ) x y z)‖ ≤
      Real.exp (2 * (((3 * C + 1) / 2) ^ 3 + (3 * C + 1) / 2)) *
        ((|σ| ^ a * Real.exp (-(1 / 2) * σ ^ 2)) * (|τ| ^ b * Real.exp (-(1 / 2) * τ ^ 2))) := by
  set B := (3 * C + 1) / 2 with hB
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_cuspoidContourDir,
    norm_cuspoidContourDir, norm_cuspoidContour, norm_cuspoidContour, norm_exp]
  have hre : (I * hyperbolicUmbilicPotential (cuspoidContour 1 σ) (cuspoidContour 1 τ)
      x y z).re = -(hyperbolicUmbilicPotential (cuspoidContour 1 σ) (cuspoidContour 1 τ)
      x y z).im := by simp [mul_re]
  rw [hre]
  have him := s36b_im_hyperbolic_ge σ τ x y z
  have hσ := s36b_cubic_le (abs_nonneg σ) hC0
  have hτ := s36b_cubic_le (abs_nonneg τ) hC0
  rw [← hB] at hσ hτ
  have hst : 2 * (|σ| * |τ|) ≤ |σ| ^ 2 + |τ| ^ 2 := by nlinarith [sq_nonneg (|σ| - |τ|)]
  have h1 : |z| * |σ| * |τ| ≤ C * (|σ| ^ 2 + |τ| ^ 2) / 2 := by
    have := mul_le_mul_of_nonneg_right hz (mul_nonneg (abs_nonneg σ) (abs_nonneg τ))
    nlinarith
  have h2 : |y| * |τ| ≤ C * |τ| := mul_le_mul_of_nonneg_right hy (abs_nonneg τ)
  have h3 : |x| * |σ| ≤ C * |σ| := mul_le_mul_of_nonneg_right hx (abs_nonneg σ)
  have hσ2 : |σ| ^ 2 = σ ^ 2 := sq_abs σ
  have hτ2 : |τ| ^ 2 = τ ^ 2 := sq_abs τ
  have key : -(hyperbolicUmbilicPotential (cuspoidContour 1 σ) (cuspoidContour 1 τ) x y z).im ≤
      2 * (B ^ 3 + B) + (-(1 / 2) * σ ^ 2 + -(1 / 2) * τ ^ 2) := by
    rw [← hσ2, ← hτ2]; linarith
  have hexp := Real.exp_le_exp.mpr key
  rw [Real.exp_add, Real.exp_add] at hexp
  have hp : 0 ≤ |σ| ^ a * |τ| ^ b := by positivity
  calc 1 * 1 * (|σ| ^ a * |τ| ^ b) *
        Real.exp (-(hyperbolicUmbilicPotential (cuspoidContour 1 σ) (cuspoidContour 1 τ)
          x y z).im)
      ≤ |σ| ^ a * |τ| ^ b * (Real.exp (2 * (B ^ 3 + B)) *
          (Real.exp (-(1 / 2) * σ ^ 2) * Real.exp (-(1 / 2) * τ ^ 2))) := by
        rw [one_mul, one_mul]; exact mul_le_mul_of_nonneg_left hexp hp
    _ = _ := by ring

lemma s36b_measurable_hyperbolic_weight (a b : ℕ) :
    Measurable fun p : ℝ × ℝ => cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
      (cuspoidContour 1 p.1 ^ a * cuspoidContour 1 p.2 ^ b) :=
  (((measurable_cuspoidContourDir 1).comp measurable_fst).mul
    ((measurable_cuspoidContourDir 1).comp measurable_snd)).mul
    ((((measurable_cuspoidContour 1).comp measurable_fst).pow_const a).mul
      (((measurable_cuspoidContour 1).comp measurable_snd).pow_const b))

lemma s36b_measurable_hyperbolic_phase (x y z : ℝ) :
    Measurable fun p : ℝ × ℝ =>
      hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2) x y z := by
  have hc1 : Measurable fun p : ℝ × ℝ => cuspoidContour 1 p.1 :=
    (measurable_cuspoidContour 1).comp measurable_fst
  have hc2 : Measurable fun p : ℝ × ℝ => cuspoidContour 1 p.2 :=
    (measurable_cuspoidContour 1).comp measurable_snd
  unfold hyperbolicUmbilicPotential
  fun_prop

lemma s36b_measurable_hyperbolic_integrand (x y z : ℝ) (a b : ℕ) :
    Measurable fun p : ℝ × ℝ => cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
      (cuspoidContour 1 p.1 ^ a * cuspoidContour 1 p.2 ^ b) *
      exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2) x y z) :=
  (s36b_measurable_hyperbolic_weight a b).mul
    (measurable_exp.comp ((s36b_measurable_hyperbolic_phase x y z).const_mul I))

theorem s36b_integrable_gauss_prod (a b : ℕ) :
    Integrable fun p : ℝ × ℝ => (|p.1| ^ a * Real.exp (-(1 / 2) * p.1 ^ 2)) *
      (|p.2| ^ b * Real.exp (-(1 / 2) * p.2 ^ 2)) :=
  (s36b_integrable_pow_mul_gauss a).mul_prod (s36b_integrable_pow_mul_gauss b)

lemma s36b_integrable_hyperbolic_integrand (x y z : ℝ) (a b : ℕ) :
    Integrable fun p : ℝ × ℝ => cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
      (cuspoidContour 1 p.1 ^ a * cuspoidContour 1 p.2 ^ b) *
      exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2) x y z) :=
  Integrable.mono' ((s36b_integrable_gauss_prod a b).const_mul _)
    (s36b_measurable_hyperbolic_integrand x y z a b).aestronglyMeasurable
    (ae_of_all _ fun p => s36b_norm_hyperbolic_integrand_le p.1 p.2 x y z a b
      (C := |x| + |y| + |z|) (by positivity)
      (by linarith [abs_nonneg y, abs_nonneg z]) (by linarith [abs_nonneg x, abs_nonneg z])
      (by linarith [abs_nonneg x, abs_nonneg y]))

/-- `Ψ^{(H)}` is the moment of order `(0, 0)`. -/
theorem hyperbolicUmbilicIntegral_eq_moment (x y z : ℝ) :
    hyperbolicUmbilicIntegral x y z = hyperbolicUmbilicMoment x y z 0 0 := by
  simp [hyperbolicUmbilicIntegral, hyperbolicUmbilicMoment]

/-- Differentiation under the integral sign in a parameter entering the phase linearly. -/
lemma s36b_hasDerivAt_param_integral {W A B : ℝ × ℝ → ℂ} {bound : ℝ × ℝ → ℝ} (w₀ : ℝ)
    (hW : Measurable W) (hA : Measurable A) (hB : Measurable B)
    (hint : Integrable fun p => W p * exp (I * (A p + (w₀ : ℂ) * B p)))
    (hbound : Integrable bound)
    (hle : ∀ p, ∀ w ∈ Metric.ball w₀ 1,
      ‖W p * (I * B p) * exp (I * (A p + (w : ℂ) * B p))‖ ≤ bound p) :
    HasDerivAt (fun w : ℝ => ∫ p, W p * exp (I * (A p + (w : ℂ) * B p)))
      (∫ p, W p * (I * B p) * exp (I * (A p + (w₀ : ℂ) * B p))) w₀ := by
  have hE : ∀ w : ℝ, Measurable fun p => exp (I * (A p + (w : ℂ) * B p)) := fun w =>
    measurable_exp.comp (measurable_const.mul (hA.add (measurable_const.mul hB)))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds w₀ one_pos)
    (Eventually.of_forall fun w => (hW.mul (hE w)).aestronglyMeasurable) hint
    ((hW.mul (measurable_const.mul hB)).mul (hE w₀)).aestronglyMeasurable
    (ae_of_all _ fun p w hw => hle p w hw) hbound (ae_of_all _ fun p w _ => ?_)).2
  have h1 : HasDerivAt (fun w : ℝ => I * (A p + (w : ℂ) * B p)) (I * B p) w := by
    simpa using ((((hasDerivAt_id w).ofReal_comp).mul_const (B p)).const_add (A p)).const_mul I
  convert h1.cexp.const_mul (W p) using 1
  ring

lemma s36b_hyperbolic_potential_x (s t : ℂ) (x y z : ℝ) :
    hyperbolicUmbilicPotential s t x y z = hyperbolicUmbilicPotential s t 0 y z + (x : ℂ) * s := by
  unfold hyperbolicUmbilicPotential; push_cast; ring

lemma s36b_hyperbolic_potential_y (s t : ℂ) (x y z : ℝ) :
    hyperbolicUmbilicPotential s t x y z = hyperbolicUmbilicPotential s t x 0 z + (y : ℂ) * t := by
  unfold hyperbolicUmbilicPotential; push_cast; ring

lemma s36b_hyperbolic_potential_z (s t : ℂ) (x y z : ℝ) :
    hyperbolicUmbilicPotential s t x y z =
      hyperbolicUmbilicPotential s t x y 0 + (z : ℂ) * (s * t) := by
  unfold hyperbolicUmbilicPotential; push_cast; ring

/-- `∂/∂x ∫∫ s^a t^b e^{iΦ^{(H)}} = i ∫∫ s^{a+1} t^b e^{iΦ^{(H)}}`. -/
theorem hasDerivAt_hyperbolicUmbilicMoment_x (x y z : ℝ) (a b : ℕ) :
    HasDerivAt (fun w => hyperbolicUmbilicMoment w y z a b)
      (I * hyperbolicUmbilicMoment x y z (a + 1) b) x := by
  set C := |x| + 1 + |y| + |z|
  have hfun : (fun w => hyperbolicUmbilicMoment w y z a b) = fun w : ℝ => ∫ p : ℝ × ℝ,
      (cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
        (cuspoidContour 1 p.1 ^ a * cuspoidContour 1 p.2 ^ b)) *
      exp (I * (hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2) 0 y z +
        (w : ℂ) * cuspoidContour 1 p.1)) := by
    funext w; unfold hyperbolicUmbilicMoment
    simp_rw [← s36b_hyperbolic_potential_x]
  have hval : I * hyperbolicUmbilicMoment x y z (a + 1) b = ∫ p : ℝ × ℝ,
      (cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
        (cuspoidContour 1 p.1 ^ a * cuspoidContour 1 p.2 ^ b)) * (I * cuspoidContour 1 p.1) *
      exp (I * (hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2) 0 y z +
        (x : ℂ) * cuspoidContour 1 p.1)) := by
    unfold hyperbolicUmbilicMoment
    rw [← integral_const_mul]
    congr 1; funext p
    rw [← s36b_hyperbolic_potential_x, pow_succ]; ring
  rw [hfun, hval]
  refine s36b_hasDerivAt_param_integral x (s36b_measurable_hyperbolic_weight a b)
    (s36b_measurable_hyperbolic_phase 0 y z) ((measurable_cuspoidContour 1).comp measurable_fst)
    ?_ ((s36b_integrable_gauss_prod (a + 1) b).const_mul
      (Real.exp (2 * (((3 * C + 1) / 2) ^ 3 + (3 * C + 1) / 2)))) fun p w hw => ?_
  · simp_rw [← s36b_hyperbolic_potential_x]
    exact s36b_integrable_hyperbolic_integrand x y z a b
  · rw [← s36b_hyperbolic_potential_x]
    have hw' : |w| ≤ C := by
      have := abs_sub_abs_le_abs_sub w x
      have := (Metric.mem_ball.mp hw); rw [Real.dist_eq] at this
      linarith [abs_nonneg y, abs_nonneg z]
    have h := s36b_norm_hyperbolic_integrand_le p.1 p.2 w y z (a + 1) b (C := C) (by positivity)
      hw' (by linarith [abs_nonneg x, abs_nonneg z]) (by linarith [abs_nonneg x, abs_nonneg y])
    calc _ = ‖cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
          (cuspoidContour 1 p.1 ^ (a + 1) * cuspoidContour 1 p.2 ^ b) *
          exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2)
            w y z)‖ := by
          rw [show cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
              (cuspoidContour 1 p.1 ^ a * cuspoidContour 1 p.2 ^ b) * (I * cuspoidContour 1 p.1) *
              exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2)
                w y z) = I * (cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
              (cuspoidContour 1 p.1 ^ (a + 1) * cuspoidContour 1 p.2 ^ b) *
              exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2)
                w y z)) by rw [pow_succ]; ring, norm_mul, norm_I, one_mul]
      _ ≤ _ := h

/-- `∂/∂y ∫∫ s^a t^b e^{iΦ^{(H)}} = i ∫∫ s^a t^{b+1} e^{iΦ^{(H)}}`. -/
theorem hasDerivAt_hyperbolicUmbilicMoment_y (x y z : ℝ) (a b : ℕ) :
    HasDerivAt (fun w => hyperbolicUmbilicMoment x w z a b)
      (I * hyperbolicUmbilicMoment x y z a (b + 1)) y := by
  set C := |x| + |y| + 1 + |z|
  have hfun : (fun w => hyperbolicUmbilicMoment x w z a b) = fun w : ℝ => ∫ p : ℝ × ℝ,
      (cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
        (cuspoidContour 1 p.1 ^ a * cuspoidContour 1 p.2 ^ b)) *
      exp (I * (hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2) x 0 z +
        (w : ℂ) * cuspoidContour 1 p.2)) := by
    funext w; unfold hyperbolicUmbilicMoment
    simp_rw [← s36b_hyperbolic_potential_y]
  have hval : I * hyperbolicUmbilicMoment x y z a (b + 1) = ∫ p : ℝ × ℝ,
      (cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
        (cuspoidContour 1 p.1 ^ a * cuspoidContour 1 p.2 ^ b)) * (I * cuspoidContour 1 p.2) *
      exp (I * (hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2) x 0 z +
        (y : ℂ) * cuspoidContour 1 p.2)) := by
    unfold hyperbolicUmbilicMoment
    rw [← integral_const_mul]
    congr 1; funext p
    rw [← s36b_hyperbolic_potential_y, pow_succ]; ring
  rw [hfun, hval]
  refine s36b_hasDerivAt_param_integral y (s36b_measurable_hyperbolic_weight a b)
    (s36b_measurable_hyperbolic_phase x 0 z) ((measurable_cuspoidContour 1).comp measurable_snd)
    ?_ ((s36b_integrable_gauss_prod a (b + 1)).const_mul
      (Real.exp (2 * (((3 * C + 1) / 2) ^ 3 + (3 * C + 1) / 2)))) fun p w hw => ?_
  · simp_rw [← s36b_hyperbolic_potential_y]
    exact s36b_integrable_hyperbolic_integrand x y z a b
  · rw [← s36b_hyperbolic_potential_y]
    have hw' : |w| ≤ C := by
      have := abs_sub_abs_le_abs_sub w y
      have := (Metric.mem_ball.mp hw); rw [Real.dist_eq] at this
      linarith [abs_nonneg x, abs_nonneg z]
    have h := s36b_norm_hyperbolic_integrand_le p.1 p.2 x w z a (b + 1) (C := C) (by positivity)
      (by linarith [abs_nonneg y, abs_nonneg z]) hw' (by linarith [abs_nonneg x, abs_nonneg y])
    calc _ = ‖cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
          (cuspoidContour 1 p.1 ^ a * cuspoidContour 1 p.2 ^ (b + 1)) *
          exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2)
            x w z)‖ := by
          rw [show cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
              (cuspoidContour 1 p.1 ^ a * cuspoidContour 1 p.2 ^ b) * (I * cuspoidContour 1 p.2) *
              exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2)
                x w z) = I * (cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
              (cuspoidContour 1 p.1 ^ a * cuspoidContour 1 p.2 ^ (b + 1)) *
              exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2)
                x w z)) by rw [pow_succ]; ring, norm_mul, norm_I, one_mul]
      _ ≤ _ := h

/-- `∂/∂z ∫∫ s^a t^b e^{iΦ^{(H)}} = i ∫∫ s^{a+1} t^{b+1} e^{iΦ^{(H)}}`. -/
theorem hasDerivAt_hyperbolicUmbilicMoment_z (x y z : ℝ) (a b : ℕ) :
    HasDerivAt (fun w => hyperbolicUmbilicMoment x y w a b)
      (I * hyperbolicUmbilicMoment x y z (a + 1) (b + 1)) z := by
  set C := |x| + |y| + |z| + 1
  have hfun : (fun w => hyperbolicUmbilicMoment x y w a b) = fun w : ℝ => ∫ p : ℝ × ℝ,
      (cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
        (cuspoidContour 1 p.1 ^ a * cuspoidContour 1 p.2 ^ b)) *
      exp (I * (hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2) x y 0 +
        (w : ℂ) * (cuspoidContour 1 p.1 * cuspoidContour 1 p.2))) := by
    funext w; unfold hyperbolicUmbilicMoment
    simp_rw [← s36b_hyperbolic_potential_z]
  have hval : I * hyperbolicUmbilicMoment x y z (a + 1) (b + 1) = ∫ p : ℝ × ℝ,
      (cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
        (cuspoidContour 1 p.1 ^ a * cuspoidContour 1 p.2 ^ b)) *
        (I * (cuspoidContour 1 p.1 * cuspoidContour 1 p.2)) *
      exp (I * (hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2) x y 0 +
        (z : ℂ) * (cuspoidContour 1 p.1 * cuspoidContour 1 p.2))) := by
    unfold hyperbolicUmbilicMoment
    rw [← integral_const_mul]
    congr 1; funext p
    rw [← s36b_hyperbolic_potential_z, pow_succ, pow_succ]; ring
  rw [hfun, hval]
  refine s36b_hasDerivAt_param_integral z (s36b_measurable_hyperbolic_weight a b)
    (s36b_measurable_hyperbolic_phase x y 0)
    (((measurable_cuspoidContour 1).comp measurable_fst).mul
      ((measurable_cuspoidContour 1).comp measurable_snd))
    ?_ ((s36b_integrable_gauss_prod (a + 1) (b + 1)).const_mul
      (Real.exp (2 * (((3 * C + 1) / 2) ^ 3 + (3 * C + 1) / 2)))) fun p w hw => ?_
  · simp_rw [← s36b_hyperbolic_potential_z]
    exact s36b_integrable_hyperbolic_integrand x y z a b
  · rw [← s36b_hyperbolic_potential_z]
    have hw' : |w| ≤ C := by
      have := abs_sub_abs_le_abs_sub w z
      have := (Metric.mem_ball.mp hw); rw [Real.dist_eq] at this
      linarith [abs_nonneg x, abs_nonneg y]
    have h := s36b_norm_hyperbolic_integrand_le p.1 p.2 x y w (a + 1) (b + 1) (C := C)
      (by positivity) (by linarith [abs_nonneg y, abs_nonneg z])
      (by linarith [abs_nonneg x, abs_nonneg z]) hw'
    calc _ = ‖cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
          (cuspoidContour 1 p.1 ^ (a + 1) * cuspoidContour 1 p.2 ^ (b + 1)) *
          exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2)
            x y w)‖ := by
          rw [show cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
              (cuspoidContour 1 p.1 ^ a * cuspoidContour 1 p.2 ^ b) *
              (I * (cuspoidContour 1 p.1 * cuspoidContour 1 p.2)) *
              exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2)
                x y w) = I * (cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
              (cuspoidContour 1 p.1 ^ (a + 1) * cuspoidContour 1 p.2 ^ (b + 1)) *
              exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2)
                x y w)) by rw [pow_succ, pow_succ]; ring, norm_mul, norm_I, one_mul]
      _ ≤ _ := h

/-- Integrability in `σ` of the hyperbolic umbilic moment integrand for fixed `τ`. -/
lemma s36b_integrable_hyperbolic_s (x y z τ : ℝ) (a : ℕ) :
    Integrable fun σ : ℝ => cuspoidContourDir 1 σ * cuspoidContour 1 σ ^ a *
      exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 σ) (cuspoidContour 1 τ) x y z) := by
  set C := |x| + |y| + |z|
  have hm : Measurable fun σ : ℝ =>
      hyperbolicUmbilicPotential (cuspoidContour 1 σ) (cuspoidContour 1 τ) x y z := by
    have hc : Measurable (cuspoidContour 1) := measurable_cuspoidContour 1
    unfold hyperbolicUmbilicPotential
    fun_prop
  refine Integrable.mono' (((s36b_integrable_pow_mul_gauss a).mul_const
      (|τ| ^ 0 * Real.exp (-(1 / 2) * τ ^ 2))).const_mul
      (Real.exp (2 * (((3 * C + 1) / 2) ^ 3 + (3 * C + 1) / 2))))
    ((((measurable_cuspoidContourDir 1).mul ((measurable_cuspoidContour 1).pow_const a)).mul
      (measurable_exp.comp (hm.const_mul I))).aestronglyMeasurable)
    (ae_of_all _ fun σ => ?_)
  have h := s36b_norm_hyperbolic_integrand_le σ τ x y z a 0 (C := C) (by positivity)
    (by linarith [abs_nonneg y, abs_nonneg z]) (by linarith [abs_nonneg x, abs_nonneg z])
    (by linarith [abs_nonneg x, abs_nonneg y])
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_cuspoidContourDir, norm_cuspoidContourDir]
    at h
  rw [norm_mul, norm_mul, norm_cuspoidContourDir]
  simp only [pow_zero, norm_one, mul_one, one_mul] at h ⊢
  linarith

/-- Integrability in `τ` of the hyperbolic umbilic moment integrand for fixed `σ`. -/
lemma s36b_integrable_hyperbolic_t (x y z σ : ℝ) (b : ℕ) :
    Integrable fun τ : ℝ => cuspoidContourDir 1 τ * cuspoidContour 1 τ ^ b *
      exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 σ) (cuspoidContour 1 τ) x y z) := by
  set C := |x| + |y| + |z|
  have hm : Measurable fun τ : ℝ =>
      hyperbolicUmbilicPotential (cuspoidContour 1 σ) (cuspoidContour 1 τ) x y z := by
    have hc : Measurable (cuspoidContour 1) := measurable_cuspoidContour 1
    unfold hyperbolicUmbilicPotential
    fun_prop
  refine Integrable.mono' (((s36b_integrable_pow_mul_gauss b).const_mul
      (|σ| ^ 0 * Real.exp (-(1 / 2) * σ ^ 2))).const_mul
      (Real.exp (2 * (((3 * C + 1) / 2) ^ 3 + (3 * C + 1) / 2))))
    ((((measurable_cuspoidContourDir 1).mul ((measurable_cuspoidContour 1).pow_const b)).mul
      (measurable_exp.comp (hm.const_mul I))).aestronglyMeasurable)
    (ae_of_all _ fun τ => ?_)
  have h := s36b_norm_hyperbolic_integrand_le σ τ x y z 0 b (C := C) (by positivity)
    (by linarith [abs_nonneg y, abs_nonneg z]) (by linarith [abs_nonneg x, abs_nonneg z])
    (by linarith [abs_nonneg x, abs_nonneg y])
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_cuspoidContourDir, norm_cuspoidContourDir]
    at h
  rw [norm_mul, norm_mul, norm_cuspoidContourDir]
  simp only [pow_zero, norm_one, mul_one, one_mul] at h ⊢
  linarith

/-- `‖exp(iΦ^{(H)})‖ ≤ A e^{-σ²/2} e^{-τ²/2}` on the contour. -/
lemma s36b_norm_hyperbolic_exp_le (x y z σ τ : ℝ) :
    ‖exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 σ) (cuspoidContour 1 τ) x y z)‖ ≤
      Real.exp (2 * (((3 * (|x| + |y| + |z|) + 1) / 2) ^ 3 + (3 * (|x| + |y| + |z|) + 1) / 2)) *
        (Real.exp (-(1 / 2) * σ ^ 2) * Real.exp (-(1 / 2) * τ ^ 2)) := by
  have h := s36b_norm_hyperbolic_integrand_le σ τ x y z 0 0 (C := |x| + |y| + |z|)
    (by positivity) (by linarith [abs_nonneg y, abs_nonneg z])
    (by linarith [abs_nonneg x, abs_nonneg z]) (by linarith [abs_nonneg x, abs_nonneg y])
  rw [norm_mul, norm_mul, norm_mul, norm_cuspoidContourDir, norm_cuspoidContourDir] at h
  simpa using h

/-- Integration by parts in `s`: `∫ (3s² + zt + x) e^{iΦ^{(H)}} ds = 0` for fixed `t = t(τ)`. -/
lemma s36b_hyperbolic_ibp_s (x y z τ : ℝ) :
    ∫ σ : ℝ, cuspoidContourDir 1 σ *
      (3 * cuspoidContour 1 σ ^ 2 + (z : ℂ) * cuspoidContour 1 τ + x) *
      exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 σ) (cuspoidContour 1 τ) x y z) =
      0 := by
  set t := cuspoidContour 1 τ with ht
  have hP : ∀ u, HasDerivAt (fun u => hyperbolicUmbilicPotential u t x y z)
      (3 * u ^ 2 + (z : ℂ) * t + x) u := by
    intro u
    unfold hyperbolicUmbilicPotential
    have := ((((((hasDerivAt_pow 3 u).add_const (t ^ 3)).add
      (((hasDerivAt_id u).const_mul (z : ℂ)).mul_const t)).add_const ((y : ℂ) * t)).add
        ((hasDerivAt_id u).const_mul (x : ℂ))))
    convert this using 1
    · funext v; simp
    · simp
  have hlim : ∀ {l : Filter ℝ}, Tendsto (fun r : ℝ => -(1 / 2) * r ^ 2) l atBot →
      Tendsto (fun σ : ℝ => exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 σ) t x y z))
        l (𝓝 0) := by
    intro l hl
    refine squeeze_zero_norm (fun σ => s36b_norm_hyperbolic_exp_le x y z σ τ) ?_
    have := ((Real.tendsto_exp_atBot.comp hl).mul_const (Real.exp (-(1 / 2) * τ ^ 2))).const_mul
      (Real.exp (2 * (((3 * (|x| + |y| + |z|) + 1) / 2) ^ 3 + (3 * (|x| + |y| + |z|) + 1) / 2)))
    simpa using this
  refine s36b_contour_ibp 1 (P := fun u => hyperbolicUmbilicPotential u t x y z) hP ?_
    (hlim s36b_tendsto_neg_half_sq_atTop) (hlim s36b_tendsto_neg_half_sq_atBot)
  refine (((s36b_integrable_hyperbolic_s x y z τ 2).const_mul 3).add
    ((s36b_integrable_hyperbolic_s x y z τ 0).const_mul ((z : ℂ) * t + x))).congr
    (ae_of_all _ fun σ => ?_)
  simp only [← ht, Pi.add_apply, pow_zero, mul_one]
  ring

/-- Integration by parts in `t`: `∫ (3t² + zs + y) e^{iΦ^{(H)}} dt = 0` for fixed `s = s(σ)`. -/
lemma s36b_hyperbolic_ibp_t (x y z σ : ℝ) :
    ∫ τ : ℝ, cuspoidContourDir 1 τ *
      (3 * cuspoidContour 1 τ ^ 2 + (z : ℂ) * cuspoidContour 1 σ + y) *
      exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 σ) (cuspoidContour 1 τ) x y z) =
      0 := by
  set s := cuspoidContour 1 σ with hs
  have hP : ∀ u, HasDerivAt (fun u => hyperbolicUmbilicPotential s u x y z)
      (3 * u ^ 2 + (z : ℂ) * s + y) u := by
    intro u
    unfold hyperbolicUmbilicPotential
    have := (((((hasDerivAt_pow 3 u).const_add (s ^ 3)).add
      ((hasDerivAt_id u).const_mul ((z : ℂ) * s))).add
        ((hasDerivAt_id u).const_mul (y : ℂ))).add_const ((x : ℂ) * s))
    convert this using 1
    · funext v; simp
    · simp
  have hlim : ∀ {l : Filter ℝ}, Tendsto (fun r : ℝ => -(1 / 2) * r ^ 2) l atBot →
      Tendsto (fun τ : ℝ => exp (I * hyperbolicUmbilicPotential s (cuspoidContour 1 τ) x y z))
        l (𝓝 0) := by
    intro l hl
    refine squeeze_zero_norm (fun τ => s36b_norm_hyperbolic_exp_le x y z σ τ) ?_
    have := ((Real.tendsto_exp_atBot.comp hl).const_mul (Real.exp (-(1 / 2) * σ ^ 2))).const_mul
      (Real.exp (2 * (((3 * (|x| + |y| + |z|) + 1) / 2) ^ 3 + (3 * (|x| + |y| + |z|) + 1) / 2)))
    simpa using this
  refine s36b_contour_ibp 1 (P := fun u => hyperbolicUmbilicPotential s u x y z) hP ?_
    (hlim s36b_tendsto_neg_half_sq_atTop) (hlim s36b_tendsto_neg_half_sq_atBot)
  refine (((s36b_integrable_hyperbolic_t x y z σ 2).const_mul 3).add
    ((s36b_integrable_hyperbolic_t x y z σ 0).const_mul ((z : ℂ) * s + y))).congr
    (ae_of_all _ fun τ => ?_)
  simp only [← hs, Pi.add_apply, pow_zero, mul_one]
  ring

/-- The moment relation behind 36.10.15: `3M_{2,0} + zM_{0,1} + xM_{0,0} = 0`. -/
lemma s36b_hyperbolic_moment_rel_s (x y z : ℝ) :
    3 * hyperbolicUmbilicMoment x y z 2 0 + (z : ℂ) * hyperbolicUmbilicMoment x y z 0 1 +
      (x : ℂ) * hyperbolicUmbilicMoment x y z 0 0 = 0 := by
  have h1 := s36b_integrable_hyperbolic_integrand x y z 2 0
  have h2 := s36b_integrable_hyperbolic_integrand x y z 0 1
  have h3 := s36b_integrable_hyperbolic_integrand x y z 0 0
  have hsum : 3 * hyperbolicUmbilicMoment x y z 2 0 +
      (z : ℂ) * hyperbolicUmbilicMoment x y z 0 1 +
      (x : ℂ) * hyperbolicUmbilicMoment x y z 0 0 = ∫ p : ℝ × ℝ,
        (3 * (cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
          (cuspoidContour 1 p.1 ^ 2 * cuspoidContour 1 p.2 ^ 0) *
          exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2)
            x y z)) +
        (z : ℂ) * (cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
          (cuspoidContour 1 p.1 ^ 0 * cuspoidContour 1 p.2 ^ 1) *
          exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2)
            x y z))) +
        (x : ℂ) * (cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
          (cuspoidContour 1 p.1 ^ 0 * cuspoidContour 1 p.2 ^ 0) *
          exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2)
            x y z)) := by
    unfold hyperbolicUmbilicMoment
    rw [integral_add _ (h3.const_mul _), integral_add (h1.const_mul _) (h2.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul]
    exact (h1.const_mul _).add (h2.const_mul _)
  have hF := ((h1.const_mul (3 : ℂ)).add (h2.const_mul (z : ℂ))).add (h3.const_mul (x : ℂ))
  rw [hsum]
  rw [Measure.volume_eq_prod] at hF ⊢
  rw [integral_prod_symm]
  swap
  · exact hF
  refine integral_eq_zero_of_ae (ae_of_all _ fun τ => ?_)
  simp only [Pi.zero_apply]
  rw [← mul_zero (cuspoidContourDir 1 τ), ← s36b_hyperbolic_ibp_s x y z τ, ← integral_const_mul]
  congr 1; funext σ
  ring

/-- The moment relation behind 36.10.16: `3M_{0,2} + zM_{1,0} + yM_{0,0} = 0`. -/
lemma s36b_hyperbolic_moment_rel_t (x y z : ℝ) :
    3 * hyperbolicUmbilicMoment x y z 0 2 + (z : ℂ) * hyperbolicUmbilicMoment x y z 1 0 +
      (y : ℂ) * hyperbolicUmbilicMoment x y z 0 0 = 0 := by
  have h1 := s36b_integrable_hyperbolic_integrand x y z 0 2
  have h2 := s36b_integrable_hyperbolic_integrand x y z 1 0
  have h3 := s36b_integrable_hyperbolic_integrand x y z 0 0
  have hsum : 3 * hyperbolicUmbilicMoment x y z 0 2 +
      (z : ℂ) * hyperbolicUmbilicMoment x y z 1 0 +
      (y : ℂ) * hyperbolicUmbilicMoment x y z 0 0 = ∫ p : ℝ × ℝ,
        (3 * (cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
          (cuspoidContour 1 p.1 ^ 0 * cuspoidContour 1 p.2 ^ 2) *
          exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2)
            x y z)) +
        (z : ℂ) * (cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
          (cuspoidContour 1 p.1 ^ 1 * cuspoidContour 1 p.2 ^ 0) *
          exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2)
            x y z))) +
        (y : ℂ) * (cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
          (cuspoidContour 1 p.1 ^ 0 * cuspoidContour 1 p.2 ^ 0) *
          exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2)
            x y z)) := by
    unfold hyperbolicUmbilicMoment
    rw [integral_add _ (h3.const_mul _), integral_add (h1.const_mul _) (h2.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul]
    exact (h1.const_mul _).add (h2.const_mul _)
  have hF := ((h1.const_mul (3 : ℂ)).add (h2.const_mul (z : ℂ))).add (h3.const_mul (y : ℂ))
  rw [hsum]
  rw [Measure.volume_eq_prod] at hF ⊢
  rw [integral_prod]
  swap
  · exact hF
  refine integral_eq_zero_of_ae (ae_of_all _ fun σ => ?_)
  simp only [Pi.zero_apply]
  rw [← mul_zero (cuspoidContourDir 1 σ), ← s36b_hyperbolic_ibp_t x y z σ, ← integral_const_mul]
  congr 1; funext τ
  ring

lemma s36b_deriv_hyperbolicUmbilicMoment_x (y z : ℝ) (a b : ℕ) :
    deriv (fun w => hyperbolicUmbilicMoment w y z a b) =
      fun w => I * hyperbolicUmbilicMoment w y z (a + 1) b :=
  funext fun w => (hasDerivAt_hyperbolicUmbilicMoment_x w y z a b).deriv

lemma s36b_deriv_hyperbolicUmbilicMoment_y (x z : ℝ) (a b : ℕ) :
    deriv (fun w => hyperbolicUmbilicMoment x w z a b) =
      fun w => I * hyperbolicUmbilicMoment x w z a (b + 1) :=
  funext fun w => (hasDerivAt_hyperbolicUmbilicMoment_y x w z a b).deriv

/-! ### Helpers: the elliptic umbilic integral with polynomial weights

The elliptic umbilic integral is an integral over the 2-cycle `∑ ε_{jk} ρ_j × ρ_k` in the
coordinates `a = s + it`, `b = s - it` (`ellipticUmbilicIntegral`). For a continuous,
polynomially bounded weight `W(a, b)`, `q2t_EM W` is the corresponding moment. On `ρ_j × ρ_k`
the integrand is bounded by `A e^{-r} e^{-q}` uniformly for bounded parameters, so the moments
may be differentiated under the integral sign (`q2t_hasDerivAt_EM`), and integration by parts
along a ray in `a` (or `b`) leaves a boundary term at `a = 0` (or `b = 0`) independent of `j`
(or `k`); these cancel because the columns (rows) of `ε` sum to zero (`q2t_EM_Wa`,
`q2t_EM_Wb`). -/

/-- A weight `W(a, b)` that is continuous and polynomially bounded. -/
def q2t_PolyBdd (W : ℂ → ℂ → ℂ) : Prop :=
  Continuous (fun p : ℂ × ℂ => W p.1 p.2) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ a b, ‖W a b‖ ≤ C * (1 + ‖a‖ + ‖b‖) ^ N

lemma q2t_polyBdd_const (c : ℂ) : q2t_PolyBdd fun _ _ => c :=
  ⟨continuous_const, ‖c‖, norm_nonneg _, 0, fun a b => by simp⟩

lemma q2t_polyBdd_fst : q2t_PolyBdd fun a _ => a :=
  ⟨continuous_fst, 1, zero_le_one, 1, fun a b => by
    simp only [pow_one, one_mul]; linarith [norm_nonneg b]⟩

lemma q2t_polyBdd_snd : q2t_PolyBdd fun _ b => b :=
  ⟨continuous_snd, 1, zero_le_one, 1, fun a b => by
    simp only [pow_one, one_mul]; linarith [norm_nonneg a]⟩

lemma q2t_one_le_base (a b : ℂ) : 1 ≤ 1 + ‖a‖ + ‖b‖ := by
  linarith [norm_nonneg a, norm_nonneg b]

lemma q2t_polyBdd_add {W₁ W₂ : ℂ → ℂ → ℂ} (h₁ : q2t_PolyBdd W₁) (h₂ : q2t_PolyBdd W₂) :
    q2t_PolyBdd fun a b => W₁ a b + W₂ a b := by
  obtain ⟨c₁, C₁, hC₁, N₁, hb₁⟩ := h₁
  obtain ⟨c₂, C₂, hC₂, N₂, hb₂⟩ := h₂
  refine ⟨c₁.add c₂, C₁ + C₂, by positivity, N₁ + N₂, fun a b => ?_⟩
  have h1 := q2t_one_le_base a b
  have e1 : (1 + ‖a‖ + ‖b‖) ^ N₁ ≤ (1 + ‖a‖ + ‖b‖) ^ (N₁ + N₂) :=
    pow_le_pow_right₀ h1 (by omega)
  have e2 : (1 + ‖a‖ + ‖b‖) ^ N₂ ≤ (1 + ‖a‖ + ‖b‖) ^ (N₁ + N₂) :=
    pow_le_pow_right₀ h1 (by omega)
  calc ‖W₁ a b + W₂ a b‖ ≤ ‖W₁ a b‖ + ‖W₂ a b‖ := norm_add_le _ _
    _ ≤ C₁ * (1 + ‖a‖ + ‖b‖) ^ N₁ + C₂ * (1 + ‖a‖ + ‖b‖) ^ N₂ := add_le_add (hb₁ a b) (hb₂ a b)
    _ ≤ C₁ * (1 + ‖a‖ + ‖b‖) ^ (N₁ + N₂) + C₂ * (1 + ‖a‖ + ‖b‖) ^ (N₁ + N₂) :=
        add_le_add (mul_le_mul_of_nonneg_left e1 hC₁) (mul_le_mul_of_nonneg_left e2 hC₂)
    _ = (C₁ + C₂) * (1 + ‖a‖ + ‖b‖) ^ (N₁ + N₂) := by ring

lemma q2t_polyBdd_mul {W₁ W₂ : ℂ → ℂ → ℂ} (h₁ : q2t_PolyBdd W₁) (h₂ : q2t_PolyBdd W₂) :
    q2t_PolyBdd fun a b => W₁ a b * W₂ a b := by
  obtain ⟨c₁, C₁, hC₁, N₁, hb₁⟩ := h₁
  obtain ⟨c₂, C₂, hC₂, N₂, hb₂⟩ := h₂
  refine ⟨c₁.mul c₂, C₁ * C₂, by positivity, N₁ + N₂, fun a b => ?_⟩
  rw [norm_mul, pow_add]
  calc ‖W₁ a b‖ * ‖W₂ a b‖ ≤ (C₁ * (1 + ‖a‖ + ‖b‖) ^ N₁) * (C₂ * (1 + ‖a‖ + ‖b‖) ^ N₂) :=
        mul_le_mul (hb₁ a b) (hb₂ a b) (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma q2t_norm_rayDir (j : Fin 3) : ‖ellipticUmbilicRayDir j‖ = 1 := by
  rw [ellipticUmbilicRayDir]; exact norm_exp_ofReal_mul_I _

lemma q2t_rayDir_ne_zero (j : Fin 3) : ellipticUmbilicRayDir j ≠ 0 := by
  intro h; have := q2t_norm_rayDir j; rw [h, norm_zero] at this; exact zero_ne_one this

/-- The phase of the elliptic umbilic integrand on a product of rays. -/
lemma q2t_re_phase_le (x y z : ℝ) {C : ℝ} (hC : |x| + |y| + |z| ≤ C) (j k : Fin 3)
    {r q : ℝ} (hr : 0 ≤ r) (hq : 0 ≤ q) :
    (I * ellipticUmbilicPotentialAB ((r : ℂ) * ellipticUmbilicRayDir j)
      ((q : ℂ) * ellipticUmbilicRayDir k) x y z).re ≤
      -(r ^ 3 + q ^ 3) / 2 + C * (r * q + r + q) := by
  set ej := ellipticUmbilicRayDir j
  set ek := ellipticUmbilicRayDir k
  have hej : ‖ej‖ = 1 := q2t_norm_rayDir j
  have hek : ‖ek‖ = 1 := q2t_norm_rayDir k
  rw [ellipticUmbilicPotentialAB_eq]
  have hc : ((r : ℂ) * ej) ^ 3 = (r : ℂ) ^ 3 * I := by rw [mul_pow, s36a_rayDir_cube]
  have hd : ((q : ℂ) * ek) ^ 3 = (q : ℂ) ^ 3 * I := by rw [mul_pow, s36a_rayDir_cube]
  set R := (z : ℂ) * ((r : ℂ) * ej) * ((q : ℂ) * ek) + (x - I * y) / 2 * ((r : ℂ) * ej) +
    (x + I * y) / 2 * ((q : ℂ) * ek) with hR
  have hsplit : I * ((((r : ℂ) * ej) ^ 3 + ((q : ℂ) * ek) ^ 3) / 2 + (z : ℂ) * ((r : ℂ) * ej) *
      ((q : ℂ) * ek) + (x - I * y) / 2 * ((r : ℂ) * ej) + (x + I * y) / 2 * ((q : ℂ) * ek)) =
      (((-(r ^ 3 + q ^ 3) / 2 : ℝ)) : ℂ) + I * R := by
    rw [hc, hd, hR]; push_cast; linear_combination (((r : ℂ) ^ 3 + (q : ℂ) ^ 3) / 2) * I_sq
  rw [hsplit, add_re, ofReal_re]
  have hxy1 : ‖((x : ℂ) - I * y) / 2‖ ≤ (|x| + |y|) / 2 := by
    rw [norm_div, Complex.norm_two]
    have := norm_sub_le (x : ℂ) (I * y)
    simp only [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] at this
    linarith
  have hxy2 : ‖((x : ℂ) + I * y) / 2‖ ≤ (|x| + |y|) / 2 := by
    rw [norm_div, Complex.norm_two]
    have := norm_add_le (x : ℂ) (I * y)
    simp only [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] at this
    linarith
  have hRn : ‖R‖ ≤ |z| * (r * q) + (|x| + |y|) / 2 * r + (|x| + |y|) / 2 * q := by
    rw [hR]
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_
    · simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, hej, hek, abs_of_nonneg hr,
        abs_of_nonneg hq]; nlinarith
    · rw [norm_mul]; simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, hej,
        abs_of_nonneg hr]
      nlinarith
    · rw [norm_mul]; simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, hek,
        abs_of_nonneg hq]
      nlinarith
  have hIR : (I * R).re ≤ ‖R‖ := by
    calc (I * R).re ≤ ‖I * R‖ := re_le_norm _
      _ = ‖R‖ := by rw [norm_mul, norm_I, one_mul]
  have hx := abs_nonneg x; have hy := abs_nonneg y; have hz := abs_nonneg z
  have hrq := mul_nonneg hr hq
  nlinarith

/-- The cubic decay of the integrand beats any polynomial and the quadratic phase terms. -/
lemma q2t_cubic_poly_le {C : ℝ} (hC : 0 ≤ C) {r q : ℝ} (hr : 0 ≤ r) (hq : 0 ≤ q) :
    -(r ^ 3 + q ^ 3) / 2 + C * (r * q + r + q) + 2 * (r + q) + 1 ≤
      256 * (C + 2) ^ 3 + 16 * (C + 2) ^ 2 + 1 := by
  set u := r + q with hu
  set D := C + 2 with hD
  have hu0 : 0 ≤ u := by positivity
  have hD2 : 2 ≤ D := by linarith
  have h3 : u ^ 3 / 4 ≤ r ^ 3 + q ^ 3 := by
    have : r ^ 3 + q ^ 3 - u ^ 3 / 4 = 3 / 4 * u * (r - q) ^ 2 := by rw [hu]; ring
    nlinarith [mul_nonneg hu0 (sq_nonneg (r - q))]
  have h2 : r * q ≤ u ^ 2 / 4 := by rw [hu]; nlinarith [sq_nonneg (r - q)]
  have hle : -(r ^ 3 + q ^ 3) / 2 + C * (r * q + r + q) + 2 * (r + q) + 1 ≤
      -u ^ 3 / 8 + D * u ^ 2 + D * u + 1 := by
    have : C * (r * q) ≤ D * u ^ 2 := by
      calc C * (r * q) ≤ C * (u ^ 2 / 4) := mul_le_mul_of_nonneg_left h2 hC
        _ ≤ D * u ^ 2 := by nlinarith [sq_nonneg u]
    have e : C * (r * q + r + q) + 2 * (r + q) = C * (r * q) + D * u := by rw [hu, hD]; ring
    nlinarith
  refine hle.trans ?_
  rcases le_or_gt u (16 * D) with h | h
  · have hu2 : D * u ^ 2 ≤ 256 * D ^ 3 := by
      have : u ^ 2 ≤ (16 * D) ^ 2 := pow_le_pow_left₀ hu0 h 2
      nlinarith
    have hu1 : D * u ≤ 16 * D ^ 2 := by nlinarith
    nlinarith [pow_nonneg hu0 3]
  · have hu1 : 1 ≤ u := by linarith
    have e1 : D * u ^ 2 ≤ u ^ 3 / 16 := by nlinarith [sq_nonneg u]
    have e2 : D * u ≤ u ^ 3 / 16 := by nlinarith [sq_nonneg u]
    nlinarith [pow_pos (by linarith : (0 : ℝ) < D) 3, sq_nonneg D]

/-- Polynomial weights times the elliptic umbilic decay are bounded by `A e^{-r} e^{-q}`. -/
lemma q2t_poly_exp_le {C : ℝ} (hC : 0 ≤ C) (N : ℕ) {r q : ℝ} (hr : 0 ≤ r) (hq : 0 ≤ q) :
    (1 + r + q) ^ N * Real.exp (-(r ^ 3 + q ^ 3) / 2 + C * (r * q + r + q)) ≤
      (N.factorial * Real.exp (256 * (C + 2) ^ 3 + 16 * (C + 2) ^ 2 + 1)) *
        Real.exp (-r) * Real.exp (-q) := by
  have h1 : (1 + r + q) ^ N ≤ N.factorial * Real.exp (1 + r + q) := by
    have := Real.pow_div_factorial_le_exp (1 + r + q) (by positivity) N
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have hpoly := q2t_cubic_poly_le hC hr hq
  calc (1 + r + q) ^ N * Real.exp (-(r ^ 3 + q ^ 3) / 2 + C * (r * q + r + q))
      ≤ (N.factorial * Real.exp (1 + r + q)) *
          Real.exp (-(r ^ 3 + q ^ 3) / 2 + C * (r * q + r + q)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = N.factorial * Real.exp ((-(r ^ 3 + q ^ 3) / 2 + C * (r * q + r + q) + 2 * (r + q) + 1)
          + (-r) + (-q)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ N.factorial * Real.exp ((256 * (C + 2) ^ 3 + 16 * (C + 2) ^ 2 + 1) + (-r) + (-q)) := by
        gcongr
    _ = _ := by rw [Real.exp_add, Real.exp_add]; ring

/-- The weighted integrand `e_j e_k W(a, b) exp(iΦ^{(E)})` on the product of rays `ρ_j × ρ_k`,
`a = r e_j`, `b = q e_k`. -/
def q2t_integrand (W : ℂ → ℂ → ℂ) (x y z : ℝ) (j k : Fin 3) (p : ℝ × ℝ) : ℂ :=
  ellipticUmbilicRayDir j * ellipticUmbilicRayDir k *
    W ((p.1 : ℂ) * ellipticUmbilicRayDir j) ((p.2 : ℂ) * ellipticUmbilicRayDir k) *
    exp (I * ellipticUmbilicPotentialAB ((p.1 : ℂ) * ellipticUmbilicRayDir j)
      ((p.2 : ℂ) * ellipticUmbilicRayDir k) x y z)

/-- The weighted quadrant integral `∫_{ρ_j × ρ_k} W exp(iΦ^{(E)}) da db`. -/
def q2t_quad (W : ℂ → ℂ → ℂ) (x y z : ℝ) (j k : Fin 3) : ℂ :=
  ∫ p : ℝ × ℝ in Ioi 0 ×ˢ Ioi 0, q2t_integrand W x y z j k p

/-- The weighted elliptic umbilic integral `(i/2) ∑ ε_{jk} ∫_{ρ_j × ρ_k} W exp(iΦ^{(E)}) da db`,
the moment of `Ψ^{(E)}` with weight `W(a, b)`. -/
def q2t_EM (W : ℂ → ℂ → ℂ) (x y z : ℝ) : ℂ :=
  I / 2 * ∑ j : Fin 3, ∑ k : Fin 3, (ellipticUmbilicCycle j k : ℂ) * q2t_quad W x y z j k

lemma q2t_EM_one (x y z : ℝ) : q2t_EM (fun _ _ => 1) x y z = ellipticUmbilicIntegral x y z := by
  simp [q2t_EM, q2t_quad, q2t_integrand, ellipticUmbilicIntegral, ellipticUmbilicQuadrant]

lemma q2t_continuous_potential (x y z : ℝ) (j k : Fin 3) :
    Continuous fun p : ℝ × ℝ => ellipticUmbilicPotentialAB ((p.1 : ℂ) * ellipticUmbilicRayDir j)
      ((p.2 : ℂ) * ellipticUmbilicRayDir k) x y z := by
  simp only [ellipticUmbilicPotentialAB_eq]; fun_prop

lemma q2t_continuous_integrand {W : ℂ → ℂ → ℂ} (hW : q2t_PolyBdd W) (x y z : ℝ) (j k : Fin 3) :
    Continuous (q2t_integrand W x y z j k) := by
  have h1 : Continuous fun p : ℝ × ℝ =>
      W ((p.1 : ℂ) * ellipticUmbilicRayDir j) ((p.2 : ℂ) * ellipticUmbilicRayDir k) :=
    hW.1.comp (by fun_prop : Continuous fun p : ℝ × ℝ =>
      ((p.1 : ℂ) * ellipticUmbilicRayDir j, (p.2 : ℂ) * ellipticUmbilicRayDir k))
  have h2 := q2t_continuous_potential x y z j k
  unfold q2t_integrand
  exact (continuous_const.mul h1).mul (continuous_exp.comp (continuous_const.mul h2))

/-- Uniform bound `A e^{-r} e^{-q}` for the weighted integrand, for `|x| + |y| + |z| ≤ C`. -/
lemma q2t_norm_integrand_le {W : ℂ → ℂ → ℂ} (hW : q2t_PolyBdd W) {C : ℝ} (hC : 0 ≤ C) :
    ∃ A : ℝ, ∀ x y z : ℝ, |x| + |y| + |z| ≤ C → ∀ (j k : Fin 3) (p : ℝ × ℝ), 0 ≤ p.1 → 0 ≤ p.2 →
      ‖q2t_integrand W x y z j k p‖ ≤ A * Real.exp (-p.1) * Real.exp (-p.2) := by
  obtain ⟨-, CW, hCW, N, hb⟩ := hW
  refine ⟨CW * (N.factorial * Real.exp (256 * (C + 2) ^ 3 + 16 * (C + 2) ^ 2 + 1)),
    fun x y z hxyz j k p hr hq => ?_⟩
  have hn1 : ‖(p.1 : ℂ) * ellipticUmbilicRayDir j‖ = p.1 := by
    rw [norm_mul, q2t_norm_rayDir, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr, mul_one]
  have hn2 : ‖(p.2 : ℂ) * ellipticUmbilicRayDir k‖ = p.2 := by
    rw [norm_mul, q2t_norm_rayDir, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq, mul_one]
  have hWb := hb ((p.1 : ℂ) * ellipticUmbilicRayDir j) ((p.2 : ℂ) * ellipticUmbilicRayDir k)
  rw [hn1, hn2] at hWb
  have hE : ‖exp (I * ellipticUmbilicPotentialAB ((p.1 : ℂ) * ellipticUmbilicRayDir j)
      ((p.2 : ℂ) * ellipticUmbilicRayDir k) x y z)‖ ≤
      Real.exp (-(p.1 ^ 3 + p.2 ^ 3) / 2 + C * (p.1 * p.2 + p.1 + p.2)) := by
    rw [norm_exp]; exact Real.exp_le_exp.mpr (q2t_re_phase_le x y z hxyz j k hr hq)
  have hP := q2t_poly_exp_le hC N hr hq
  unfold q2t_integrand
  rw [norm_mul, norm_mul, norm_mul, q2t_norm_rayDir, q2t_norm_rayDir, one_mul, one_mul]
  calc _ ≤ (CW * (1 + p.1 + p.2) ^ N) *
        Real.exp (-(p.1 ^ 3 + p.2 ^ 3) / 2 + C * (p.1 * p.2 + p.1 + p.2)) :=
        mul_le_mul hWb hE (norm_nonneg _) (by positivity)
    _ = CW * ((1 + p.1 + p.2) ^ N *
        Real.exp (-(p.1 ^ 3 + p.2 ^ 3) / 2 + C * (p.1 * p.2 + p.1 + p.2))) := by ring
    _ ≤ CW * ((N.factorial * Real.exp (256 * (C + 2) ^ 3 + 16 * (C + 2) ^ 2 + 1)) *
        Real.exp (-p.1) * Real.exp (-p.2)) := mul_le_mul_of_nonneg_left hP hCW
    _ = _ := by ring

lemma q2t_integrableOn_exp_prod (A : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => A * Real.exp (-p.1) * Real.exp (-p.2)) (Ioi 0 ×ˢ Ioi 0) := by
  have h1 : IntegrableOn (fun r : ℝ => Real.exp (-r)) (Ioi 0) := by
    simpa using exp_neg_integrableOn_Ioi 0 (b := 1) one_pos
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact (h1.const_mul A).mul_prod h1

lemma q2t_integrableOn {W : ℂ → ℂ → ℂ} (hW : q2t_PolyBdd W) (x y z : ℝ) (j k : Fin 3) :
    IntegrableOn (q2t_integrand W x y z j k) (Ioi 0 ×ˢ Ioi 0) := by
  obtain ⟨A, hA⟩ := q2t_norm_integrand_le hW (C := |x| + |y| + |z|) (by positivity)
  refine (q2t_integrableOn_exp_prod A).mono'
    (q2t_continuous_integrand hW x y z j k).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioi) fun p hp => ?_
  exact hA x y z le_rfl j k p (le_of_lt hp.1) (le_of_lt hp.2)

lemma q2t_quad_add {W₁ W₂ : ℂ → ℂ → ℂ} (h₁ : q2t_PolyBdd W₁) (h₂ : q2t_PolyBdd W₂)
    (x y z : ℝ) (j k : Fin 3) :
    q2t_quad (fun a b => W₁ a b + W₂ a b) x y z j k =
      q2t_quad W₁ x y z j k + q2t_quad W₂ x y z j k := by
  unfold q2t_quad
  rw [← integral_add (q2t_integrableOn h₁ x y z j k) (q2t_integrableOn h₂ x y z j k)]
  congr 1; funext p; unfold q2t_integrand; ring

lemma q2t_quad_const_mul (c : ℂ) (W : ℂ → ℂ → ℂ) (x y z : ℝ) (j k : Fin 3) :
    q2t_quad (fun a b => c * W a b) x y z j k = c * q2t_quad W x y z j k := by
  unfold q2t_quad
  rw [← integral_const_mul]
  congr 1; funext p; unfold q2t_integrand; ring

lemma q2t_EM_add {W₁ W₂ : ℂ → ℂ → ℂ} (h₁ : q2t_PolyBdd W₁) (h₂ : q2t_PolyBdd W₂) (x y z : ℝ) :
    q2t_EM (fun a b => W₁ a b + W₂ a b) x y z = q2t_EM W₁ x y z + q2t_EM W₂ x y z := by
  simp only [q2t_EM, q2t_quad_add h₁ h₂, mul_add, Finset.sum_add_distrib]

lemma q2t_EM_const_mul (c : ℂ) (W : ℂ → ℂ → ℂ) (x y z : ℝ) :
    q2t_EM (fun a b => c * W a b) x y z = c * q2t_EM W x y z := by
  simp only [q2t_EM, q2t_quad_const_mul, Finset.mul_sum]
  congr 1; ext j; congr 1; ext k; ring

/-- The `w`-derivative of the elliptic umbilic potential along `x = x₀ + w dx`, etc. -/
def q2t_L (dx dy dz : ℝ) (a b : ℂ) : ℂ :=
  dz * a * b + (dx - I * dy) / 2 * a + (dx + I * dy) / 2 * b

lemma q2t_polyBdd_L (dx dy dz : ℝ) : q2t_PolyBdd (q2t_L dx dy dz) := by
  unfold q2t_L
  refine q2t_polyBdd_add (q2t_polyBdd_add ?_ ?_) ?_
  · exact q2t_polyBdd_mul (q2t_polyBdd_mul (q2t_polyBdd_const _) q2t_polyBdd_fst) q2t_polyBdd_snd
  · exact q2t_polyBdd_mul (q2t_polyBdd_const _) q2t_polyBdd_fst
  · exact q2t_polyBdd_mul (q2t_polyBdd_const _) q2t_polyBdd_snd

lemma q2t_potential_affine (a b : ℂ) (x₀ y₀ z₀ dx dy dz w : ℝ) :
    ellipticUmbilicPotentialAB a b (x₀ + w * dx) (y₀ + w * dy) (z₀ + w * dz) =
      ellipticUmbilicPotentialAB a b x₀ y₀ z₀ + (w : ℂ) * q2t_L dx dy dz a b := by
  rw [ellipticUmbilicPotentialAB_eq, ellipticUmbilicPotentialAB_eq, q2t_L]; push_cast; ring

/-- Differentiation under the integral sign along an affine path in the parameters. -/
lemma q2t_hasDerivAt_quad {W : ℂ → ℂ → ℂ} (hW : q2t_PolyBdd W) (x₀ y₀ z₀ dx dy dz w₀ : ℝ)
    (j k : Fin 3) :
    HasDerivAt (fun w : ℝ => q2t_quad W (x₀ + w * dx) (y₀ + w * dy) (z₀ + w * dz) j k)
      (q2t_quad (fun a b => W a b * (I * q2t_L dx dy dz a b))
        (x₀ + w₀ * dx) (y₀ + w₀ * dy) (z₀ + w₀ * dz) j k) w₀ := by
  have hW' : q2t_PolyBdd fun a b => W a b * (I * q2t_L dx dy dz a b) :=
    q2t_polyBdd_mul hW (q2t_polyBdd_mul (q2t_polyBdd_const I) (q2t_polyBdd_L dx dy dz))
  set C := |x₀| + |y₀| + |z₀| + (|w₀| + 1) * (|dx| + |dy| + |dz|) with hCdef
  have hC : 0 ≤ C := by positivity
  obtain ⟨A, hA⟩ := q2t_norm_integrand_le hW' hC
  have hball : ∀ w ∈ Metric.ball w₀ 1,
      |x₀ + w * dx| + |y₀ + w * dy| + |z₀ + w * dz| ≤ C := by
    intro w hw
    rw [Metric.mem_ball, Real.dist_eq] at hw
    have hw' : |w| ≤ |w₀| + 1 := by
      have := abs_sub_abs_le_abs_sub w w₀; linarith
    have e1 : |x₀ + w * dx| ≤ |x₀| + |w| * |dx| := (abs_add_le _ _).trans (by rw [abs_mul])
    have e2 : |y₀ + w * dy| ≤ |y₀| + |w| * |dy| := (abs_add_le _ _).trans (by rw [abs_mul])
    have e3 : |z₀ + w * dz| ≤ |z₀| + |w| * |dz| := (abs_add_le _ _).trans (by rw [abs_mul])
    have : |w| * (|dx| + |dy| + |dz|) ≤ (|w₀| + 1) * (|dx| + |dy| + |dz|) :=
      mul_le_mul_of_nonneg_right hw' (by positivity)
    rw [hCdef]; nlinarith
  have hmeas : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    measurableSet_Ioi.prod measurableSet_Ioi
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds w₀ one_pos)
    (F := fun w p => q2t_integrand W (x₀ + w * dx) (y₀ + w * dy) (z₀ + w * dz) j k p)
    (F' := fun w p => q2t_integrand (fun a b => W a b * (I * q2t_L dx dy dz a b))
      (x₀ + w * dx) (y₀ + w * dy) (z₀ + w * dz) j k p)
    (bound := fun p => A * Real.exp (-p.1) * Real.exp (-p.2))
    (Eventually.of_forall fun w =>
      (q2t_continuous_integrand hW _ _ _ j k).aestronglyMeasurable)
    (q2t_integrableOn hW _ _ _ j k)
    (q2t_continuous_integrand hW' _ _ _ j k).aestronglyMeasurable
    (ae_restrict_of_forall_mem hmeas fun p hp w hw =>
      hA _ _ _ (hball w hw) j k p (le_of_lt hp.1) (le_of_lt hp.2))
    (q2t_integrableOn_exp_prod A) (ae_of_all _ fun p w _ => ?_)).2
  -- pointwise derivative
  set a : ℂ := (p.1 : ℂ) * ellipticUmbilicRayDir j
  set b : ℂ := (p.2 : ℂ) * ellipticUmbilicRayDir k
  set c : ℂ := ellipticUmbilicRayDir j * ellipticUmbilicRayDir k * W a b
  set P₀ := ellipticUmbilicPotentialAB a b x₀ y₀ z₀
  set L := q2t_L dx dy dz a b
  have hfun : (fun w : ℝ => q2t_integrand W (x₀ + w * dx) (y₀ + w * dy) (z₀ + w * dz) j k p) =
      fun w : ℝ => c * exp (I * (P₀ + (w : ℂ) * L)) := by
    funext w; simp only [q2t_integrand, q2t_potential_affine]; rfl
  have hval : q2t_integrand (fun a b => W a b * (I * q2t_L dx dy dz a b))
      (x₀ + w * dx) (y₀ + w * dy) (z₀ + w * dz) j k p =
      c * (exp (I * (P₀ + id (w : ℂ) * L)) * (I * (1 * L))) := by
    simp only [q2t_integrand, q2t_potential_affine]
    simp only [c, P₀, L, a, b, id]; ring
  rw [hfun, hval]
  exact ((((hasDerivAt_id (w : ℂ)).mul_const L).const_add P₀).const_mul I).cexp.const_mul c
    |>.comp_ofReal

/-- Differentiation of the weighted elliptic umbilic integral along an affine path. -/
lemma q2t_hasDerivAt_EM {W : ℂ → ℂ → ℂ} (hW : q2t_PolyBdd W) (x₀ y₀ z₀ dx dy dz w₀ : ℝ) :
    HasDerivAt (fun w : ℝ => q2t_EM W (x₀ + w * dx) (y₀ + w * dy) (z₀ + w * dz))
      (q2t_EM (fun a b => W a b * (I * q2t_L dx dy dz a b))
        (x₀ + w₀ * dx) (y₀ + w₀ * dy) (z₀ + w₀ * dz)) w₀ := by
  unfold q2t_EM
  refine HasDerivAt.const_mul _ (HasDerivAt.fun_sum fun j _ => HasDerivAt.fun_sum fun k _ => ?_)
  exact (q2t_hasDerivAt_quad hW x₀ y₀ z₀ dx dy dz w₀ j k).const_mul _

lemma q2t_hasDerivAt_EM_x {W : ℂ → ℂ → ℂ} (hW : q2t_PolyBdd W) (x y z : ℝ) :
    HasDerivAt (fun s : ℝ => q2t_EM W s y z)
      (q2t_EM (fun a b => W a b * (I * q2t_L 1 0 0 a b)) x y z) x := by
  have h := q2t_hasDerivAt_EM hW 0 y z 1 0 0 x
  simp only [zero_add, mul_one, mul_zero, add_zero] at h
  exact h

lemma q2t_hasDerivAt_EM_y {W : ℂ → ℂ → ℂ} (hW : q2t_PolyBdd W) (x y z : ℝ) :
    HasDerivAt (fun t : ℝ => q2t_EM W x t z)
      (q2t_EM (fun a b => W a b * (I * q2t_L 0 1 0 a b)) x y z) y := by
  have h := q2t_hasDerivAt_EM hW x 0 z 0 1 0 y
  simp only [zero_add, mul_one, mul_zero, add_zero] at h
  exact h

lemma q2t_hasDerivAt_EM_z {W : ℂ → ℂ → ℂ} (hW : q2t_PolyBdd W) (x y z : ℝ) :
    HasDerivAt (fun w : ℝ => q2t_EM W x y w)
      (q2t_EM (fun a b => W a b * (I * q2t_L 0 0 1 a b)) x y z) z := by
  have h := q2t_hasDerivAt_EM hW x y 0 0 0 1 z
  simp only [zero_add, mul_one, mul_zero, add_zero] at h
  exact h

lemma q2t_polyBdd_mulL {W : ℂ → ℂ → ℂ} (hW : q2t_PolyBdd W) (dx dy dz : ℝ) :
    q2t_PolyBdd fun a b => W a b * (I * q2t_L dx dy dz a b) :=
  q2t_polyBdd_mul hW (q2t_polyBdd_mul (q2t_polyBdd_const I) (q2t_polyBdd_L dx dy dz))

/-- Integration by parts along a ray `r ↦ r e`, `r > 0`, for `exp(iP)` decaying at infinity. -/
lemma q2t_ray_ibp {P P' : ℂ → ℂ} (hP : ∀ u, HasDerivAt P (P' u) u) (e : ℂ)
    (hint : IntegrableOn (fun r : ℝ => e * P' ((r : ℂ) * e) * exp (I * P ((r : ℂ) * e))) (Ioi 0))
    (htend : Tendsto (fun r : ℝ => exp (I * P ((r : ℂ) * e))) atTop (𝓝 0)) :
    ∫ r in Ioi (0 : ℝ), e * P' ((r : ℂ) * e) * exp (I * P ((r : ℂ) * e)) = I * exp (I * P 0) := by
  have hd : ∀ r : ℝ, HasDerivAt (fun r : ℝ => -I * exp (I * P ((r : ℂ) * e)))
      (e * P' ((r : ℂ) * e) * exp (I * P ((r : ℂ) * e))) r := by
    intro r
    have h1 : HasDerivAt (fun u : ℂ => -I * exp (I * P (u * e)))
        (-I * (exp (I * P ((r : ℂ) * e)) * (I * (P' ((r : ℂ) * e) * (1 * e))))) (r : ℂ) :=
      ((((hP _).comp (r : ℂ) ((hasDerivAt_id (r : ℂ)).mul_const e)).const_mul I).cexp).const_mul
        (-I)
    have h2 := h1.comp_ofReal
    convert h2 using 1
    linear_combination (e * P' ((r : ℂ) * e) * exp (I * P ((r : ℂ) * e))) * I_sq
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (a := 0) (m := 0)
    (hd 0).continuousAt.continuousWithinAt (fun r _ => hd r) hint
    (by simpa using htend.const_mul (-I))
  rw [h]; simp

/-- Slices of the weighted integrand are integrable. -/
lemma q2t_integrableOn_slice_fst {W : ℂ → ℂ → ℂ} (hW : q2t_PolyBdd W) (x y z : ℝ) (j k : Fin 3)
    {q : ℝ} (hq : 0 ≤ q) :
    IntegrableOn (fun r : ℝ => q2t_integrand W x y z j k (r, q)) (Ioi 0) := by
  obtain ⟨A, hA⟩ := q2t_norm_integrand_le hW (C := |x| + |y| + |z|) (by positivity)
  have h1 : IntegrableOn (fun r : ℝ => A * Real.exp (-q) * Real.exp (-r)) (Ioi 0) := by
    have := (exp_neg_integrableOn_Ioi 0 (b := 1) one_pos).const_mul (A * Real.exp (-q))
    simp only [neg_mul, one_mul] at this; exact this
  refine h1.mono' ((q2t_continuous_integrand hW x y z j k).comp
    (by fun_prop : Continuous fun r : ℝ => (r, q))).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_
  have := hA x y z le_rfl j k (r, q) (le_of_lt hr) hq
  simp only at this; linarith

lemma q2t_integrableOn_slice_snd {W : ℂ → ℂ → ℂ} (hW : q2t_PolyBdd W) (x y z : ℝ) (j k : Fin 3)
    {r : ℝ} (hr : 0 ≤ r) :
    IntegrableOn (fun q : ℝ => q2t_integrand W x y z j k (r, q)) (Ioi 0) := by
  obtain ⟨A, hA⟩ := q2t_norm_integrand_le hW (C := |x| + |y| + |z|) (by positivity)
  have h1 : IntegrableOn (fun q : ℝ => A * Real.exp (-r) * Real.exp (-q)) (Ioi 0) := by
    have := (exp_neg_integrableOn_Ioi 0 (b := 1) one_pos).const_mul (A * Real.exp (-r))
    simp only [neg_mul, one_mul] at this; exact this
  refine h1.mono' ((q2t_continuous_integrand hW x y z j k).comp
    (by fun_prop : Continuous fun q : ℝ => (r, q))).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun q hq => ?_
  exact hA x y z le_rfl j k (r, q) hr (le_of_lt hq)

/-- `exp(iΦ^{(E)})` decays along each ray. -/
lemma q2t_norm_exp_le (x y z : ℝ) (j k : Fin 3) :
    ∃ A : ℝ, ∀ r q : ℝ, 0 ≤ r → 0 ≤ q →
      ‖exp (I * ellipticUmbilicPotentialAB ((r : ℂ) * ellipticUmbilicRayDir j)
        ((q : ℂ) * ellipticUmbilicRayDir k) x y z)‖ ≤ A * Real.exp (-r) * Real.exp (-q) := by
  obtain ⟨A, hA⟩ := q2t_norm_integrand_le (q2t_polyBdd_const 1) (C := |x| + |y| + |z|)
    (by positivity)
  refine ⟨A, fun r q hr hq => ?_⟩
  have := hA x y z le_rfl j k (r, q) hr hq
  simpa [q2t_integrand, norm_mul, q2t_norm_rayDir] using this

lemma q2t_tendsto_exp_fst (x y z : ℝ) (j k : Fin 3) {q : ℝ} (hq : 0 ≤ q) :
    Tendsto (fun r : ℝ => exp (I * ellipticUmbilicPotentialAB ((r : ℂ) * ellipticUmbilicRayDir j)
      ((q : ℂ) * ellipticUmbilicRayDir k) x y z)) atTop (𝓝 0) := by
  obtain ⟨A, hA⟩ := q2t_norm_exp_le x y z j k
  have h0 : Tendsto (fun r : ℝ => A * Real.exp (-q) * Real.exp (-r)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (A * Real.exp (-q))
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [eventually_ge_atTop 0] with r hr
  have := hA r q hr hq; linarith

lemma q2t_tendsto_exp_snd (x y z : ℝ) (j k : Fin 3) {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun q : ℝ => exp (I * ellipticUmbilicPotentialAB ((r : ℂ) * ellipticUmbilicRayDir j)
      ((q : ℂ) * ellipticUmbilicRayDir k) x y z)) atTop (𝓝 0) := by
  obtain ⟨A, hA⟩ := q2t_norm_exp_le x y z j k
  have h0 : Tendsto (fun q : ℝ => A * Real.exp (-r) * Real.exp (-q)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (A * Real.exp (-r))
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [eventually_ge_atTop 0] with q hq
  exact hA r q hr hq

lemma q2t_polyBdd_congr {W W' : ℂ → ℂ → ℂ} (h : q2t_PolyBdd W) (e : ∀ a b, W a b = W' a b) :
    q2t_PolyBdd W' := by
  have : W = W' := funext fun a => funext fun b => e a b
  exact this ▸ h

/-- `∂Φ^{(E)}/∂a = 3a²/2 + zb + (x - iy)/2`. -/
def q2t_Wa (x y z : ℝ) (a b : ℂ) : ℂ := 3 * a ^ 2 / 2 + z * b + (x - I * y) / 2

/-- `∂Φ^{(E)}/∂b = 3b²/2 + za + (x + iy)/2`. -/
def q2t_Wb (x y z : ℝ) (a b : ℂ) : ℂ := 3 * b ^ 2 / 2 + z * a + (x + I * y) / 2

lemma q2t_polyBdd_Wa (x y z : ℝ) : q2t_PolyBdd (q2t_Wa x y z) := by
  refine q2t_polyBdd_congr (q2t_polyBdd_add (q2t_polyBdd_add (q2t_polyBdd_mul
    (q2t_polyBdd_const (3 / 2)) (q2t_polyBdd_mul q2t_polyBdd_fst q2t_polyBdd_fst))
    (q2t_polyBdd_mul (q2t_polyBdd_const (z : ℂ)) q2t_polyBdd_snd))
    (q2t_polyBdd_const (((x : ℂ) - I * y) / 2))) fun a b => ?_
  simp only [q2t_Wa]; ring

lemma q2t_polyBdd_Wb (x y z : ℝ) : q2t_PolyBdd (q2t_Wb x y z) := by
  refine q2t_polyBdd_congr (q2t_polyBdd_add (q2t_polyBdd_add (q2t_polyBdd_mul
    (q2t_polyBdd_const (3 / 2)) (q2t_polyBdd_mul q2t_polyBdd_snd q2t_polyBdd_snd))
    (q2t_polyBdd_mul (q2t_polyBdd_const (z : ℂ)) q2t_polyBdd_fst))
    (q2t_polyBdd_const (((x : ℂ) + I * y) / 2))) fun a b => ?_
  simp only [q2t_Wb]; ring

lemma q2t_hasDerivAt_potential_a (x y z : ℝ) (b u : ℂ) :
    HasDerivAt (fun u => ellipticUmbilicPotentialAB u b x y z) (q2t_Wa x y z u b) u := by
  simp only [ellipticUmbilicPotentialAB_eq, q2t_Wa]
  have h := ((((hasDerivAt_pow 3 u).add_const (b ^ 3)).div_const 2).add
    (((hasDerivAt_id u).const_mul ((z : ℂ))).mul_const b)).add
    (((hasDerivAt_id u).const_mul (((x : ℂ) - I * y) / 2)).add_const (((x : ℂ) + I * y) / 2 * b))
  convert h using 1
  · funext v; simp only [Pi.add_apply, id]; ring
  · push_cast; ring

lemma q2t_hasDerivAt_potential_b (x y z : ℝ) (a u : ℂ) :
    HasDerivAt (fun u => ellipticUmbilicPotentialAB a u x y z) (q2t_Wb x y z a u) u := by
  simp only [ellipticUmbilicPotentialAB_eq, q2t_Wb]
  have h := ((((hasDerivAt_pow 3 u).const_add (a ^ 3)).div_const 2).add
    (((hasDerivAt_id u).const_mul ((z : ℂ) * a)))).add
    (((hasDerivAt_id u).const_mul (((x : ℂ) + I * y) / 2)).const_add (((x : ℂ) - I * y) / 2 * a))
  convert h using 1
  · funext v; simp only [Pi.add_apply, id]; ring
  · push_cast; ring

lemma q2t_integrable_prod {W : ℂ → ℂ → ℂ} (hW : q2t_PolyBdd W) (x y z : ℝ) (j k : Fin 3) :
    Integrable (q2t_integrand W x y z j k)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have h := q2t_integrableOn hW x y z j k
  rwa [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at h

/-- Integration by parts in `a`: the quadrant integral of `∂Φ/∂a` is independent of `j`. -/
lemma q2t_quad_Wa (x y z : ℝ) (j k : Fin 3) :
    q2t_quad (q2t_Wa x y z) x y z j k = ∫ q in Ioi (0 : ℝ),
      ellipticUmbilicRayDir k * (I * exp (I * ellipticUmbilicPotentialAB 0
        ((q : ℂ) * ellipticUmbilicRayDir k) x y z)) := by
  unfold q2t_quad
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
    integral_prod_symm _ (q2t_integrable_prod (q2t_polyBdd_Wa x y z) x y z j k)]
  refine setIntegral_congr_fun measurableSet_Ioi fun q hq => ?_
  set ej := ellipticUmbilicRayDir j
  set ek := ellipticUmbilicRayDir k
  set P : ℂ → ℂ := fun u => ellipticUmbilicPotentialAB u ((q : ℂ) * ek) x y z
  set P' : ℂ → ℂ := fun u => q2t_Wa x y z u ((q : ℂ) * ek)
  have hfun : (fun r : ℝ => q2t_integrand (q2t_Wa x y z) x y z j k (r, q)) =
      fun r : ℝ => ek * (ej * P' ((r : ℂ) * ej) * exp (I * P ((r : ℂ) * ej))) := by
    funext r; simp only [q2t_integrand, P, P', ej, ek]; ring
  rw [hfun, integral_const_mul]
  have hint : IntegrableOn (fun r : ℝ => ej * P' ((r : ℂ) * ej) * exp (I * P ((r : ℂ) * ej)))
      (Ioi 0) := by
    have h := (q2t_integrableOn_slice_fst (q2t_polyBdd_Wa x y z) x y z j k
      (le_of_lt (mem_Ioi.mp hq))).const_mul ek⁻¹
    refine IntegrableOn.congr_fun h (fun r _ => ?_) measurableSet_Ioi
    have hek : ek ≠ 0 := q2t_rayDir_ne_zero k
    simp only [q2t_integrand, P, P', ej, ek] at hek ⊢
    field_simp
  rw [q2t_ray_ibp (fun u => q2t_hasDerivAt_potential_a x y z _ u) ej hint
    (q2t_tendsto_exp_fst x y z j k (le_of_lt (mem_Ioi.mp hq)))]

/-- Integration by parts in `b`: the quadrant integral of `∂Φ/∂b` is independent of `k`. -/
lemma q2t_quad_Wb (x y z : ℝ) (j k : Fin 3) :
    q2t_quad (q2t_Wb x y z) x y z j k = ∫ r in Ioi (0 : ℝ),
      ellipticUmbilicRayDir j * (I * exp (I * ellipticUmbilicPotentialAB
        ((r : ℂ) * ellipticUmbilicRayDir j) 0 x y z)) := by
  unfold q2t_quad
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
    integral_prod _ (q2t_integrable_prod (q2t_polyBdd_Wb x y z) x y z j k)]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  set ej := ellipticUmbilicRayDir j
  set ek := ellipticUmbilicRayDir k
  set P : ℂ → ℂ := fun u => ellipticUmbilicPotentialAB ((r : ℂ) * ej) u x y z
  set P' : ℂ → ℂ := fun u => q2t_Wb x y z ((r : ℂ) * ej) u
  have hfun : (fun q : ℝ => q2t_integrand (q2t_Wb x y z) x y z j k (r, q)) =
      fun q : ℝ => ej * (ek * P' ((q : ℂ) * ek) * exp (I * P ((q : ℂ) * ek))) := by
    funext q; simp only [q2t_integrand, P, P', ej, ek]; ring
  rw [hfun, integral_const_mul]
  have hint : IntegrableOn (fun q : ℝ => ek * P' ((q : ℂ) * ek) * exp (I * P ((q : ℂ) * ek)))
      (Ioi 0) := by
    have h := (q2t_integrableOn_slice_snd (q2t_polyBdd_Wb x y z) x y z j k
      (le_of_lt (mem_Ioi.mp hr))).const_mul ej⁻¹
    refine IntegrableOn.congr_fun h (fun q _ => ?_) measurableSet_Ioi
    have hej : ej ≠ 0 := q2t_rayDir_ne_zero j
    simp only [q2t_integrand, P, P', ej, ek] at hej ⊢
    field_simp
  rw [q2t_ray_ibp (fun u => q2t_hasDerivAt_potential_b x y z _ u) ek hint
    (q2t_tendsto_exp_snd x y z j k (le_of_lt (mem_Ioi.mp hr)))]

/-- `∫_{cycle} (∂Φ^{(E)}/∂a) exp(iΦ^{(E)}) = 0`: the boundary terms cancel since the columns of
`ε` sum to zero. -/
lemma q2t_EM_Wa (x y z : ℝ) : q2t_EM (q2t_Wa x y z) x y z = 0 := by
  simp only [q2t_EM, q2t_quad_Wa, Fin.sum_univ_three]
  simp [ellipticUmbilicCycle]
  ring

/-- `∫_{cycle} (∂Φ^{(E)}/∂b) exp(iΦ^{(E)}) = 0` (the rows of `ε` sum to zero). -/
lemma q2t_EM_Wb (x y z : ℝ) : q2t_EM (q2t_Wb x y z) x y z = 0 := by
  simp only [q2t_EM, q2t_quad_Wb, Fin.sum_univ_three]
  simp [ellipticUmbilicCycle]

lemma q2t_deriv_EM_x {W : ℂ → ℂ → ℂ} (hW : q2t_PolyBdd W) (y z : ℝ) :
    deriv (fun s : ℝ => q2t_EM W s y z) =
      fun x => q2t_EM (fun a b => W a b * (I * q2t_L 1 0 0 a b)) x y z :=
  funext fun x => (q2t_hasDerivAt_EM_x hW x y z).deriv

lemma q2t_deriv_EM_y {W : ℂ → ℂ → ℂ} (hW : q2t_PolyBdd W) (x z : ℝ) :
    deriv (fun t : ℝ => q2t_EM W x t z) =
      fun y => q2t_EM (fun a b => W a b * (I * q2t_L 0 1 0 a b)) x y z :=
  funext fun y => (q2t_hasDerivAt_EM_y hW x y z).deriv

lemma q2t_deriv_EM_z {W : ℂ → ℂ → ℂ} (hW : q2t_PolyBdd W) (x y : ℝ) :
    deriv (fun w : ℝ => q2t_EM W x y w) =
      fun z => q2t_EM (fun a b => W a b * (I * q2t_L 0 0 1 a b)) x y z :=
  funext fun z => (q2t_hasDerivAt_EM_z hW x y z).deriv

lemma q2t_EM_congr {W W' : ℂ → ℂ → ℂ} (e : ∀ a b, W a b = W' a b) (x y z : ℝ) :
    q2t_EM W x y z = q2t_EM W' x y z := by
  have : W = W' := funext fun a => funext fun b => e a b
  rw [this]

lemma q2t_polyBdd_cmul {W : ℂ → ℂ → ℂ} (hW : q2t_PolyBdd W) (c : ℂ) :
    q2t_PolyBdd fun a b => c * W a b := q2t_polyBdd_mul (q2t_polyBdd_const c) hW

/-- The combination `i(∂Φ/∂a - ∂Φ/∂b) = ∂Φ/∂t` integrates to zero. -/
lemma q2t_EM_Wt (x y z : ℝ) :
    q2t_EM (fun a b => I * q2t_Wa x y z a b + (-I) * q2t_Wb x y z a b) x y z = 0 := by
  rw [q2t_EM_add (q2t_polyBdd_cmul (q2t_polyBdd_Wa x y z) _)
    (q2t_polyBdd_cmul (q2t_polyBdd_Wb x y z) _), q2t_EM_const_mul, q2t_EM_const_mul,
    q2t_EM_Wa, q2t_EM_Wb]
  ring

/-- The combination `∂Φ/∂a + ∂Φ/∂b = ∂Φ/∂s` integrates to zero. -/
lemma q2t_EM_Ws (x y z : ℝ) :
    q2t_EM (fun a b => q2t_Wa x y z a b + q2t_Wb x y z a b) x y z = 0 := by
  rw [q2t_EM_add (q2t_polyBdd_Wa x y z) (q2t_polyBdd_Wb x y z), q2t_EM_Wa, q2t_EM_Wb]
  ring

/-! ### §36.10(iii)–(iv): umbilics

The operator equations 36.10.11, `Φ_s^{(U)}(-i∂/∂x, -i∂/∂y; x)Ψ^{(U)} = 0` and
`Φ_t^{(U)}(-i∂/∂x, -i∂/∂y; x)Ψ^{(U)} = 0` with `Φ_s = ∂Φ/∂s`, `Φ_t = ∂Φ/∂t` (36.10.12), are, written
out, 36.10.13–36.10.14 for `U = E` (`Φ_t^{(E)} = -6st + 2zt + y`, `Φ_s^{(E)} = 3s² - 3t² + 2zs + x`)
and 36.10.15–36.10.16 for `U = H` (`Φ_s^{(H)} = 3s² + zt + x`, `Φ_t^{(H)} = 3t² + zs + y`); the
substitution `s ↦ -i∂/∂x`, `t ↦ -i∂/∂y` and multiplication by `-1` give the printed forms. They are
tagged on those four statements. -/

/-- The elliptic umbilic equation from `Φ_t^{(E)}` (DLMF 36.10.13, and 36.10.11–36.10.12):
`6 ∂²Ψ^{(E)}/∂x∂y - 2iz ∂Ψ^{(E)}/∂y + yΨ^{(E)} = 0`. -/
@[dlmf 36.10.E13, dlmf 36.10.E11, dlmf 36.10.E12]
theorem ellipticUmbilicIntegral_pde_xy (x y z : ℝ) :
    6 * deriv (fun s => deriv (fun t => ellipticUmbilicIntegral s t z) y) x -
      2 * I * z * deriv (fun t => ellipticUmbilicIntegral x t z) y +
      y * ellipticUmbilicIntegral x y z = 0 := by
  have h1 := q2t_polyBdd_const (1 : ℂ)
  have hy := q2t_polyBdd_mulL h1 0 1 0
  have hyx := q2t_polyBdd_mulL hy 1 0 0
  simp only [← q2t_EM_one, q2t_deriv_EM_y h1, q2t_deriv_EM_x hy]
  have e := q2t_EM_add (q2t_polyBdd_cmul hyx 6)
    (q2t_polyBdd_add (q2t_polyBdd_cmul hy (-(2 * I * z))) (q2t_polyBdd_cmul h1 y)) x y z
  rw [q2t_EM_const_mul 6 (fun a b => 1 * (I * q2t_L 0 1 0 a b) * (I * q2t_L 1 0 0 a b)),
    q2t_EM_add (q2t_polyBdd_cmul hy _) (q2t_polyBdd_cmul h1 _),
    q2t_EM_const_mul (-(2 * I * z)) (fun a b => 1 * (I * q2t_L 0 1 0 a b)),
    q2t_EM_const_mul (y : ℂ) (fun _ _ => 1)] at e
  rw [q2t_EM_congr (W' := fun a b => I * q2t_Wa x y z a b + (-I) * q2t_Wb x y z a b)
    (fun a b => ?_), q2t_EM_Wt] at e
  · linear_combination -e
  · simp only [q2t_L, q2t_Wa, q2t_Wb]; push_cast
    linear_combination (-(3 / 2) * (a ^ 2 - b ^ 2) * I + z * (a - b) * I + y) * I_sq

/-- The elliptic umbilic equation from `Φ_s^{(E)}` (DLMF 36.10.14, and 36.10.11–36.10.12):
`3(∂²Ψ^{(E)}/∂x² - ∂²Ψ^{(E)}/∂y²) + 2iz ∂Ψ^{(E)}/∂x - xΨ^{(E)} = 0`, as corrected in DLMF
version 1.0.1 (the term `2iz ∂Ψ^{(E)}/∂x` originally appeared with `Ψ^{(H)}`). -/
@[dlmf 36.10.E14, dlmf 36.10.E11, dlmf 36.10.E12]
theorem ellipticUmbilicIntegral_pde_xx_yy (x y z : ℝ) :
    3 * (iteratedDeriv 2 (fun s => ellipticUmbilicIntegral s y z) x -
        iteratedDeriv 2 (fun t => ellipticUmbilicIntegral x t z) y) +
      2 * I * z * deriv (fun s => ellipticUmbilicIntegral s y z) x -
      x * ellipticUmbilicIntegral x y z = 0 := by
  have h1 := q2t_polyBdd_const (1 : ℂ)
  have hx := q2t_polyBdd_mulL h1 1 0 0
  have hy := q2t_polyBdd_mulL h1 0 1 0
  have hxx := q2t_polyBdd_mulL hx 1 0 0
  have hyy := q2t_polyBdd_mulL hy 0 1 0
  simp only [← q2t_EM_one, iteratedDeriv_succ, iteratedDeriv_zero, q2t_deriv_EM_x h1,
    q2t_deriv_EM_y h1, q2t_deriv_EM_x hx, q2t_deriv_EM_y hy]
  have e := q2t_EM_add (q2t_polyBdd_cmul hxx 3)
    (q2t_polyBdd_add (q2t_polyBdd_cmul hyy (-3))
      (q2t_polyBdd_add (q2t_polyBdd_cmul hx (2 * I * z)) (q2t_polyBdd_cmul h1 (-x)))) x y z
  rw [q2t_EM_const_mul 3 (fun a b => 1 * (I * q2t_L 1 0 0 a b) * (I * q2t_L 1 0 0 a b)),
    q2t_EM_add (q2t_polyBdd_cmul hyy _)
      (q2t_polyBdd_add (q2t_polyBdd_cmul hx _) (q2t_polyBdd_cmul h1 _)),
    q2t_EM_const_mul (-3) (fun a b => 1 * (I * q2t_L 0 1 0 a b) * (I * q2t_L 0 1 0 a b)),
    q2t_EM_add (q2t_polyBdd_cmul hx _) (q2t_polyBdd_cmul h1 _),
    q2t_EM_const_mul (2 * I * z) (fun a b => 1 * (I * q2t_L 1 0 0 a b)),
    q2t_EM_const_mul (-(x : ℂ)) (fun _ _ => 1)] at e
  rw [q2t_EM_congr (W' := fun a b => (-1) * (q2t_Wa x y z a b + q2t_Wb x y z a b))
    (fun a b => ?_), q2t_EM_const_mul (-1) (fun a b => q2t_Wa x y z a b + q2t_Wb x y z a b),
    q2t_EM_Ws] at e
  · linear_combination -e
  · simp only [q2t_L, q2t_Wa, q2t_Wb]; push_cast
    linear_combination (-(3 / 4) * (a - b) ^ 2 * I ^ 2 + 3 * (a ^ 2 + b ^ 2) / 2 + z * (a + b)) *
      I_sq

/-- The hyperbolic umbilic equation from `Φ_s^{(H)}` (DLMF 36.10.15, and 36.10.11–36.10.12):
`3 ∂²Ψ^{(H)}/∂x² + iz ∂Ψ^{(H)}/∂y - xΨ^{(H)} = 0`. -/
@[dlmf 36.10.E15, dlmf 36.10.E11, dlmf 36.10.E12]
theorem hyperbolicUmbilicIntegral_pde_x (x y z : ℝ) :
    3 * iteratedDeriv 2 (fun s => hyperbolicUmbilicIntegral s y z) x +
      I * z * deriv (fun t => hyperbolicUmbilicIntegral x t z) y -
      x * hyperbolicUmbilicIntegral x y z = 0 := by
  simp only [hyperbolicUmbilicIntegral_eq_moment, iteratedDeriv_succ, iteratedDeriv_zero,
    s36b_deriv_hyperbolicUmbilicMoment_x, s36b_deriv_hyperbolicUmbilicMoment_y]
  rw [(((hasDerivAt_hyperbolicUmbilicMoment_x x y z 1 0).const_mul I)).deriv]
  simp only [Nat.reduceAdd, zero_add]
  linear_combination (-1 : ℂ) * s36b_hyperbolic_moment_rel_s x y z +
    (3 * hyperbolicUmbilicMoment x y z 2 0 + (z : ℂ) * hyperbolicUmbilicMoment x y z 0 1) * I_sq

/-- The hyperbolic umbilic equation from `Φ_t^{(H)}` (DLMF 36.10.16, and 36.10.11–36.10.12):
`3 ∂²Ψ^{(H)}/∂y² + iz ∂Ψ^{(H)}/∂x - yΨ^{(H)} = 0`. -/
@[dlmf 36.10.E16, dlmf 36.10.E11, dlmf 36.10.E12]
theorem hyperbolicUmbilicIntegral_pde_y (x y z : ℝ) :
    3 * iteratedDeriv 2 (fun t => hyperbolicUmbilicIntegral x t z) y +
      I * z * deriv (fun s => hyperbolicUmbilicIntegral s y z) x -
      y * hyperbolicUmbilicIntegral x y z = 0 := by
  simp only [hyperbolicUmbilicIntegral_eq_moment, iteratedDeriv_succ, iteratedDeriv_zero,
    s36b_deriv_hyperbolicUmbilicMoment_x, s36b_deriv_hyperbolicUmbilicMoment_y]
  rw [(((hasDerivAt_hyperbolicUmbilicMoment_y x y z 0 1).const_mul I)).deriv]
  simp only [Nat.reduceAdd, zero_add]
  linear_combination (-1 : ℂ) * s36b_hyperbolic_moment_rel_t x y z +
    (3 * hyperbolicUmbilicMoment x y z 0 2 + (z : ℂ) * hyperbolicUmbilicMoment x y z 1 0) * I_sq

/-- The `z`-derivative of the elliptic umbilic integral (DLMF 36.10.17):
`i ∂Ψ^{(E)}/∂z = ∂²Ψ^{(E)}/∂x² + ∂²Ψ^{(E)}/∂y²`. -/
@[dlmf 36.10.E17]
theorem ellipticUmbilicIntegral_pde_z (x y z : ℝ) :
    I * deriv (fun w => ellipticUmbilicIntegral x y w) z =
      iteratedDeriv 2 (fun s => ellipticUmbilicIntegral s y z) x +
        iteratedDeriv 2 (fun t => ellipticUmbilicIntegral x t z) y := by
  have h1 := q2t_polyBdd_const (1 : ℂ)
  simp only [← q2t_EM_one, iteratedDeriv_succ, iteratedDeriv_zero, q2t_deriv_EM_x h1,
    q2t_deriv_EM_y h1, q2t_deriv_EM_z h1, q2t_deriv_EM_x (q2t_polyBdd_mulL h1 1 0 0),
    q2t_deriv_EM_y (q2t_polyBdd_mulL h1 0 1 0)]
  rw [← q2t_EM_const_mul, ← q2t_EM_add (q2t_polyBdd_mulL (q2t_polyBdd_mulL h1 1 0 0) 1 0 0)
    (q2t_polyBdd_mulL (q2t_polyBdd_mulL h1 0 1 0) 0 1 0)]
  refine q2t_EM_congr (fun a b => ?_) x y z
  simp only [q2t_L]; push_cast
  linear_combination (-I ^ 2 * (a - b) ^ 2 / 4) * I_sq

/-- The `z`-derivative of the hyperbolic umbilic integral (DLMF 36.10.18):
`i ∂Ψ^{(H)}/∂z = ∂²Ψ^{(H)}/∂x∂y`. -/
@[dlmf 36.10.E18]
theorem hyperbolicUmbilicIntegral_pde_z (x y z : ℝ) :
    I * deriv (fun w => hyperbolicUmbilicIntegral x y w) z =
      deriv (fun s => deriv (fun t => hyperbolicUmbilicIntegral s t z) y) x := by
  simp only [hyperbolicUmbilicIntegral_eq_moment]
  have hy : ∀ s, deriv (fun t => hyperbolicUmbilicMoment s t z 0 0) y =
      I * hyperbolicUmbilicMoment s y z 0 1 := fun s =>
    (hasDerivAt_hyperbolicUmbilicMoment_y s y z 0 0).deriv
  simp only [hy]
  rw [((hasDerivAt_hyperbolicUmbilicMoment_x x y z 0 1).const_mul I).deriv,
    (hasDerivAt_hyperbolicUmbilicMoment_z x y z 0 0).deriv]

end DLMF.CoalescingSaddles
