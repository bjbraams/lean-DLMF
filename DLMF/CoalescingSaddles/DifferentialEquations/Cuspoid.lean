/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.CoalescingSaddles.Basic.AuxiliaryData
public import DLMF.CoalescingSaddles.CanonicalIntegrals

/-!
# Differential equations for cuspoid integrals

Gaussian domination, differentiation under the integral and integration by parts give the
cuspoid differential equations.

Source references and common attribution are retained in
`DLMF.CoalescingSaddles.DifferentialEquations`.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set Filter Function

open scoped Real Topology

namespace DLMF.CoalescingSaddles

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

/-- The cuspoid moment integrand `r ↦ d(r) t(r)^p exp(iΦ_K(t(r); x))` is measurable. -/
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

/-- Changing one coordinate `x_m` by at most `1` raises `∑ |x_j|` by at most `1`. -/
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

/-- Derivative of the cuspoid moment integrand in the coordinate `x_m`: it multiplies by `i
t^{m+1}`. -/
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

/-- The contour direction is constant on `[0, ∞)`. -/
lemma s36b_dir_pos (K : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    cuspoidContourDir K y = cuspoidContourDir K 1 := by
  rw [s36a_dir_of_nonneg K hy, s36a_dir_of_nonneg K zero_le_one]

/-- Chain rule for `r ↦ exp(i P(r ω))` along the line `r ω`. -/
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

/-- `r ↦ exp(i P(r ω))` is continuous for differentiable `P`. -/
lemma s36b_continuous_exp_line {P P' : ℂ → ℂ} (hP : ∀ u, HasDerivAt P (P' u) u) (ω : ℂ) :
    Continuous fun r : ℝ => exp (I * P ((r : ℂ) * ω)) :=
  continuous_exp.comp (continuous_const.mul
    ((continuous_iff_continuousAt.mpr fun u => (hP u).continuousAt).comp
      (continuous_ofReal.mul continuous_const)))

/-- The integrand `exp(iΦ_K(t(r); x))` tends to `0` along any filter on which `-r²/2 → -∞`. -/
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

/-- `-r²/2 → -∞` as `r → ∞`. -/
lemma s36b_tendsto_neg_half_sq_atTop : Tendsto (fun r : ℝ => -(1 / 2) * r ^ 2) atTop atBot :=
  (tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by norm_num)

/-- `-r²/2 → -∞` as `r → -∞`. -/
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
      simp only [hG, cuspoidContour, s36a_dir_neg hy]
    have hfr : f r = cuspoidContourDir K (-1) * P' ((r : ℂ) * cuspoidContourDir K (-1)) *
        exp (I * P ((r : ℂ) * cuspoidContourDir K (-1))) := by
      simp only [hf, hG, cuspoidContour, s36a_dir_neg hr]
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
      · simp only [hG, cuspoidContour, s36a_dir_neg hy]
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

/-- The `n`-th derivative of `Ψ_K` in `x_m` is `iⁿ` times the moment of order `n(m+1)`. -/
lemma s36b_iteratedDeriv_vec (K : ℕ) (v : Fin K → ℝ) (m : Fin K) (n : ℕ) {g : ℝ → ℂ}
    (hg : ∀ s, g s = cuspoidIntegral K (update v m s)) :
    iteratedDeriv n g (v m) = I ^ n * cuspoidMoment K v (n * ((m : ℕ) + 1)) := by
  rw [show g = fun s => cuspoidIntegral K (update v m s) from funext hg]
  exact iteratedDeriv_cuspoidIntegral_update K v m n

/-- `(-i)ⁿ iⁿ = 1`. -/
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

end DLMF.CoalescingSaddles
end
