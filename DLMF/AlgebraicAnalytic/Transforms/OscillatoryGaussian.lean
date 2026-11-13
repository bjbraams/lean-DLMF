/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Transforms.Fourier
import DLMF.Gamma.IntegralRepresentations.PrymAndOscillatory

/-!
# Fourier limits of oscillatory Gaussians

Completing the square and using the Fresnel limits gives the symmetric improper Fourier
transform of `exp(i a t²)` for `a > 0`, with the symmetric DLMF normalization.
-/

public noncomputable section

open Complex MeasureTheory Filter Set
open scoped Topology ComplexConjugate

namespace DLMF.AlgebraicAnalytic

/-- The symmetric improper Fourier transform of an oscillatory Gaussian with positive
quadratic coefficient, in the normalization of DLMF 1.14.1. -/
theorem tendsto_fourierTransform_exp_sq {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Tendsto (fun R : ℝ => ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) *
      ∫ t in -R..R, exp (I * a * t ^ 2) * exp (I * x * t)) atTop
      (𝓝 (((Real.sqrt (2 * a))⁻¹ : ℂ) *
        exp (I * (Real.pi / 4 - (x : ℂ) ^ 2 / (4 * a))))) := by
  let g : ℝ → ℂ := fun t => exp (I * (t : ℂ) ^ 2)
  let P : ℝ → ℂ := fun t => ∫ u in (0 : ℝ)..t, g u
  let B : ℝ := Real.sqrt (Real.pi / 2) / 2
  have hv (op : ℝ → ℝ) (hop : op (Real.pi / 4) = Real.sqrt 2 / 2) :
      Real.Gamma (1 + 1 / (2 : ℕ)) * op (Real.pi / (2 * (2 : ℕ))) = B := by
    rw [show (1 + 1 / (2 : ℕ) : ℝ) = 1 / 2 + 1 by norm_num,
      Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq,
      show (Real.pi / (2 * (2 : ℕ)) : ℝ) = Real.pi / 4 by norm_num, hop]
    dsimp [B]
    rw [Real.sqrt_div Real.pi_pos.le]
    have h2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    field_simp
    nlinarith
  have hc := DLMF.Gamma.Gamma_cos_pow 2 le_rfl
  have hs := DLMF.Gamma.Gamma_sin_pow 2 le_rfl
  rw [hv Real.cos Real.cos_pi_div_four] at hc
  rw [hv Real.sin Real.sin_pi_div_four] at hs
  have hP : Tendsto P atTop (𝓝 ((B : ℂ) + B * I)) := by
    have h := ((continuous_ofReal.tendsto _).comp hc).add
      (((continuous_ofReal.tendsto _).comp hs).mul_const I)
    refine h.congr (fun R => ?_)
    dsimp [P, g, Function.comp_def]
    rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_ofReal,
      ← intervalIntegral.integral_mul_const,
      ← intervalIntegral.integral_add
        ((show Continuous (fun t : ℝ => (Real.cos (t ^ 2) : ℂ)) by
          fun_prop).intervalIntegrable _ _)
        ((show Continuous (fun t : ℝ => (Real.sin (t ^ 2) : ℂ) * I) by
          fun_prop).intervalIntegrable _ _)]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [show I * (t : ℂ) ^ 2 = ((t ^ 2 : ℝ) : ℂ) * I by push_cast; ring,
      exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  have hneg (t : ℝ) : P (-t) = -P t := by
    dsimp [P]
    have h := intervalIntegral.integral_comp_neg (f := g) (a := 0) (b := t)
    have he : (fun u : ℝ => g (-u)) = g := by
      funext u
      simp [g]
    rw [he, neg_zero] at h
    calc
      (∫ u in (0 : ℝ)..-t, g u) = -(∫ u in -t..0, g u) :=
        intervalIntegral.integral_symm _ _
      _ = -(∫ u in (0 : ℝ)..t, g u) := congrArg Neg.neg h.symm
  have hPB : Tendsto P atBot (𝓝 (-((B : ℂ) + B * I))) := by
    have h := (hP.comp tendsto_neg_atBot_atTop).neg
    simpa only [Function.comp_def, hneg, neg_neg] using h
  let r := Real.sqrt a
  have hr : 0 < r := Real.sqrt_pos.mpr ha
  have hr2 : r ^ 2 = a := Real.sq_sqrt ha.le
  let d := x / (2 * r)
  have hright : Tendsto (fun R : ℝ => r * R + d) atTop atTop :=
    tendsto_atTop_add_const_right _ d (tendsto_id.const_mul_atTop hr)
  have hleft : Tendsto (fun R : ℝ => r * (-R) + d) atTop atBot :=
    tendsto_atBot_add_const_right _ d (tendsto_neg_atTop_atBot.const_mul_atBot hr)
  have hlim := ((hP.comp hright).sub (hPB.comp hleft)).const_mul
    (((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) * exp (-I * (x : ℂ) ^ 2 / (4 * a)) * r⁻¹)
  have he (t : ℝ) : exp (I * a * (t : ℂ) ^ 2) * exp (I * x * t) =
      exp (-I * (x : ℂ) ^ 2 / (4 * a)) * g (r * t + d) := by
    dsimp [g, d]
    rw [← exp_add, ← exp_add]
    congr 1
    push_cast
    rw [← hr2]
    push_cast
    field_simp [ofReal_ne_zero.mpr hr.ne']
    ring
  have hval (R : ℝ) :
      ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) *
          ∫ t in -R..R, exp (I * a * t ^ 2) * exp (I * x * t) =
        (((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) *
          exp (-I * (x : ℂ) ^ 2 / (4 * a)) * r⁻¹) * (P (r * R + d) - P (r * (-R) + d)) := by
    simp_rw [he]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_add g hr.ne' d]
    have hint : (∫ t in r * (-R) + d..r * R + d, g t) =
        P (r * R + d) - P (r * (-R) + d) := by
      dsimp [P]
      exact (intervalIntegral.integral_interval_sub_left
        ((by fun_prop : Continuous g).intervalIntegrable _ _)
        ((by fun_prop : Continuous g).intervalIntegrable _ _)).symm
    rw [hint]
    simp only [Complex.real_smul]
    ring
  have hnorm : (((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) *
        exp (-I * (x : ℂ) ^ 2 / (4 * a)) * r⁻¹) *
        (((B : ℂ) + B * I) - -((B : ℂ) + B * I)) =
      ((Real.sqrt (2 * a))⁻¹ : ℂ) *
        exp (I * (Real.pi / 4 - (x : ℂ) ^ 2 / (4 * a))) := by
    have hNB : (Real.sqrt (2 * Real.pi))⁻¹ * (2 * B) = 1 / 2 := by
      dsimp [B]
      rw [Real.sqrt_div Real.pi_pos.le,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have hp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
      have h2 : 0 < Real.sqrt 2 := by positivity
      have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      field_simp [hp.ne', h2.ne']
      nlinarith
    have hCa : (Real.sqrt (2 * a))⁻¹ * (Real.sqrt 2 / 2) = (1 / 2) * r⁻¹ := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      -- Express the scalar normalization using the positive square root r.
      change (Real.sqrt 2 * r)⁻¹ * (Real.sqrt 2 / 2) = (1 / 2) * r⁻¹
      field_simp
    have hphase : exp (I * (Real.pi / 4 - (x : ℂ) ^ 2 / (4 * a))) =
        exp (((Real.pi / 4 : ℝ) : ℂ) * I) * exp (-I * (x : ℂ) ^ 2 / (4 * a)) := by
      rw [← exp_add]
      congr 1
      push_cast
      ring
    rw [hphase, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
      Real.cos_pi_div_four, Real.sin_pi_div_four]
    have hNB' := congrArg Complex.ofReal hNB
    have hCa' := congrArg Complex.ofReal hCa
    push_cast at hNB' hCa' ⊢
    linear_combination
      (r : ℂ)⁻¹ * (1 + I) * exp (-I * (x : ℂ) ^ 2 / (4 * a)) * hNB' -
        (1 + I) * exp (-I * (x : ℂ) ^ 2 / (4 * a)) * hCa'
  rw [hnorm] at hlim
  exact hlim.congr (fun R => (hval R).symm)

/-- The sine and cosine components of the symmetric improper Fourier transform of an
oscillatory Gaussian, in the normalization of DLMF 1.14.1. -/
theorem tendsto_fourierTransform_sin_cos_sq {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Tendsto (fun R : ℝ => ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) *
        ∫ t in -R..R, (Real.sin (a * t ^ 2) : ℂ) * exp (I * x * t)) atTop
      (𝓝 (-(Real.sqrt (2 * a))⁻¹ * Real.sin (x ^ 2 / (4 * a) - Real.pi / 4) : ℝ)) ∧
    Tendsto (fun R : ℝ => ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) *
        ∫ t in -R..R, (Real.cos (a * t ^ 2) : ℂ) * exp (I * x * t)) atTop
      (𝓝 ((Real.sqrt (2 * a))⁻¹ * Real.cos (x ^ 2 / (4 * a) - Real.pi / 4) : ℝ)) := by
  let N : ℂ := (Real.sqrt (2 * Real.pi))⁻¹
  let k : ℝ := (Real.sqrt (2 * a))⁻¹
  let θ : ℝ := Real.pi / 4 - x ^ 2 / (4 * a)
  let p : ℝ → ℂ := fun t => exp (I * a * t ^ 2) * exp (I * x * t)
  let n : ℝ → ℂ := fun t => exp (I * a * t ^ 2) * exp (I * (-x) * t)
  let L : ℂ := k * exp ((θ : ℂ) * I)
  have hLeq : L = ((Real.sqrt (2 * a))⁻¹ : ℂ) *
      exp (I * (Real.pi / 4 - (x : ℂ) ^ 2 / (4 * a))) := by
    dsimp [L, k, θ]
    congr 2 <;> push_cast <;> ring
  have hpos : Tendsto (fun R : ℝ => N * ∫ t in -R..R, p t) atTop (𝓝 L) := by
    rw [hLeq]
    exact tendsto_fourierTransform_exp_sq ha x
  have hneg : Tendsto (fun R : ℝ => N * ∫ t in -R..R, n t) atTop (𝓝 L) := by
    rw [hLeq]
    simpa only [N, n, ofReal_neg, neg_sq] using tendsto_fourierTransform_exp_sq ha (-x)
  have hconj (t : ℝ) : conj (n t) =
      exp (-I * a * (t : ℂ) ^ 2) * exp (I * x * t) := by
    dsimp [n]
    simp only [map_mul, ← exp_conj, conj_I, conj_ofReal, map_neg, map_pow]
    congr 2
    ring
  have hsin (t : ℝ) : (p t - conj (n t)) / (2 * I) =
      (Real.sin (a * t ^ 2) : ℂ) * exp (I * x * t) := by
    rw [hconj, ofReal_sin, Complex.sin]
    dsimp [p]
    push_cast
    rw [show ((a : ℂ) * t ^ 2) * I = I * a * t ^ 2 by ring,
      show -((a : ℂ) * t ^ 2) * I = -I * a * t ^ 2 by ring]
    field_simp
    simp only [I_sq]
    ring
  have hcos (t : ℝ) : (p t + conj (n t)) / 2 =
      (Real.cos (a * t ^ 2) : ℂ) * exp (I * x * t) := by
    rw [hconj, ofReal_cos, Complex.cos]
    dsimp [p]
    push_cast
    rw [show ((a : ℂ) * t ^ 2) * I = I * a * t ^ 2 by ring,
      show -((a : ℂ) * t ^ 2) * I = -I * a * t ^ 2 by ring]
    ring
  have hNc : conj N = N := by simp [N]
  have hLc : (L - conj L) / (2 * I) =
      (-(Real.sqrt (2 * a))⁻¹ * Real.sin (x ^ 2 / (4 * a) - Real.pi / 4) : ℝ) := by
    dsimp [L]
    rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
    simp only [map_mul, conj_ofReal, map_add, conj_I]
    have he : θ = -(x ^ 2 / (4 * a) - Real.pi / 4) := by dsimp [θ]; ring
    rw [he, Real.sin_neg, Real.cos_neg]
    push_cast
    dsimp [k]
    simp only [ofReal_inv]
    field_simp
    ring
  have hLr : (L + conj L) / 2 =
      ((Real.sqrt (2 * a))⁻¹ * Real.cos (x ^ 2 / (4 * a) - Real.pi / 4) : ℝ) := by
    dsimp [L]
    rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
    simp only [map_mul, conj_ofReal, map_add, conj_I]
    have he : θ = -(x ^ 2 / (4 * a) - Real.pi / 4) := by dsimp [θ]; ring
    rw [he, Real.sin_neg, Real.cos_neg]
    push_cast
    dsimp [k]
    simp only [ofReal_inv]
    ring
  have hc := continuous_conj.tendsto L |>.comp hneg
  have hs := (hpos.sub hc).div_const (2 * I)
  have hr := (hpos.add hc).div_const 2
  rw [hLc] at hs
  rw [hLr] at hr
  constructor
  · refine hs.congr (fun R => ?_)
    simp only [Function.comp_apply, map_mul, hNc]
    rw [← intervalIntegral.intervalIntegral_conj]
    rw [← mul_sub, div_eq_mul_inv, mul_assoc,
      ← intervalIntegral.integral_sub
        ((show Continuous p by dsimp [p]; fun_prop).intervalIntegrable _ _)
        ((show Continuous (fun t => conj (n t)) by dsimp [n]; fun_prop).intervalIntegrable _ _),
      ← intervalIntegral.integral_mul_const]
    -- Expose the pointwise kernel before applying its sine or cosine identity.
    change N * (∫ t in -R..R, (p t - conj (n t)) * (2 * I)⁻¹) = _
    simp_rw [← div_eq_mul_inv, hsin]
    simp only [N]
  · refine hr.congr (fun R => ?_)
    simp only [Function.comp_apply, map_mul, hNc]
    rw [← intervalIntegral.intervalIntegral_conj]
    rw [← mul_add, div_eq_mul_inv, mul_assoc,
      ← intervalIntegral.integral_add
        ((show Continuous p by dsimp [p]; fun_prop).intervalIntegrable _ _)
        ((show Continuous (fun t => conj (n t)) by dsimp [n]; fun_prop).intervalIntegrable _ _),
      ← intervalIntegral.integral_mul_const]
    -- Expose the pointwise kernel before applying its sine or cosine identity.
    change N * (∫ t in -R..R, (p t + conj (n t)) * 2⁻¹) = _
    simp_rw [← div_eq_mul_inv, hcos]
    simp only [N]

end DLMF.AlgebraicAnalytic
