/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.VerticalBounds
public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
# The exponential Mellin inversion integral

For `c > 0` and `Re w > 0`, the Cahen–Mellin integral is
`∫ Γ(c + iy) w^(-c-iy) dy = 2π exp(-w)`, with the principal power.
Mellin inversion proves the formula on the positive real axis; exponential decay of Gamma
on vertical lines and the identity theorem extend it to the right half-plane. This is the
exponential kernel used in the Mellin-transform methods of DLMF §2.5.
-/

@[expose] public noncomputable section

open Complex Filter MeasureTheory Set
open scoped Real Topology

namespace DLMF.Gamma

/-- The Gamma function restricted to a vertical line in the right half-plane is continuous. -/
theorem continuous_Gamma_vertical {c : ℝ} (hc : 0 < c) :
    Continuous (fun y : ℝ => Complex.Gamma (c + I * y)) := by
  refine continuous_iff_continuousAt.mpr fun y => ?_
  exact (hasDerivAt_Gamma_of_re_pos (by simpa using hc)).continuousAt.comp (by fun_prop)

/-- The Cahen–Mellin integrand is absolutely integrable in the right half-plane. -/
theorem integrable_Gamma_mul_cpow_neg {c : ℝ} (hc : 0 < c) {w : ℂ} (hw : 0 < w.re) :
    Integrable (fun y : ℝ => Complex.Gamma (c + y * I) * w ^ (-((c : ℂ) + y * I))) := by
  obtain ⟨C, K, hb⟩ := exists_norm_Gamma_le hc
  have hb' : ∀ y : ℝ, ‖Complex.Gamma (c + I * y)‖ ≤
      C * (1 + |y|) ^ K * Real.exp (-(π / 2 * |y|)) := by
    intro y
    rw [show -(π / 2 * |y|) = -(π * |y|) / 2 by ring]
    exact hb y
  have harg : |(-Complex.log w).im| < π / 2 := by
    simpa only [neg_im, abs_neg, log_im] using
      (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw))
  have hi := integrable_mul_exp_of_exp_decay (continuous_Gamma_vertical hc).aestronglyMeasurable
    hb' c harg
  convert hi using 1
  funext y
  rw [mul_comm I, cpow_def_of_ne_zero (ne_zero_of_re_pos hw)]
  congr 1
  congr 1
  ring

/-- The Fourier–Laplace form of exponential Mellin inversion on its full logarithmic strip. -/
theorem integral_Gamma_mul_exp {c : ℝ} (hc : 0 < c) {v : ℂ} (hv : |v.im| < π / 2) :
    (∫ y : ℝ, Complex.Gamma (c + I * y) * Complex.exp (((c : ℂ) + I * y) * v)) =
      2 * π * Complex.exp (-Complex.exp (-v)) := by
  obtain ⟨C, K, hb⟩ := exists_norm_Gamma_le hc
  have hb' : ∀ y : ℝ, ‖Complex.Gamma (c + I * y)‖ ≤
      C * (1 + |y|) ^ K * Real.exp (-(π / 2 * |y|)) := by
    intro y
    rw [show -(π / 2 * |y|) = -(π * |y|) / 2 by ring]
    exact hb y
  have hmeas : AEStronglyMeasurable (fun y : ℝ => Complex.Gamma (c + I * y)) volume :=
    (continuous_Gamma_vertical hc).aestronglyMeasurable
  refine eqOn_horizontalStrip_of_eq_ofReal_neg
    (f := fun v : ℂ => ∫ y : ℝ,
      Complex.Gamma (c + I * y) * Complex.exp (((c : ℂ) + I * y) * v))
    (g := fun v : ℂ => 2 * π * Complex.exp (-Complex.exp (-v))) (by positivity)
    (differentiableOn_integral_mul_exp_of_exp_decay hmeas hb' c)
    (by fun_prop) ?_ hv
  intro x _
  let f : ℝ → ℂ := fun t => (Real.exp (-t) : ℂ)
  have hf : MellinConvergent f (c : ℂ) := by
    refine (GammaIntegral_convergent (s := (c : ℂ)) (by simpa using hc)).congr_fun
      (fun t _ => ?_) measurableSet_Ioi
    simp only [f, smul_eq_mul, ofReal_exp, mul_comm]
  have hΓ (y : ℝ) : mellin f (c + y * I) = Complex.Gamma (c + y * I) := by
    rw [Gamma_eq_integral (by simpa using hc), GammaIntegral_eq_mellin]
  have hint : VerticalIntegrable (mellin f) c := by
    have hi := integrable_mul_exp_of_exp_decay hmeas hb' c
      (w := 0) (by simpa using (half_pos Real.pi_pos))
    simpa only [VerticalIntegrable, hΓ, mul_zero, Complex.exp_zero, mul_one, mul_comm I] using hi
  have hm := mellinInv_mellin_eq c f (Real.exp_pos (-x)) hf hint (by fun_prop)
  have hpow (y : ℝ) : ((Real.exp (-x) : ℝ) : ℂ) ^ (-((c : ℂ) + y * I)) =
      Complex.exp (((c : ℂ) + I * y) * (x : ℂ)) := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
      ← ofReal_log (Real.exp_pos (-x)).le, Real.log_exp]
    congr 1
    push_cast
    ring
  simp only [mellinInv, hΓ, hpow, smul_eq_mul, Complex.real_smul] at hm
  have hscalar : ((1 / (2 * π) : ℝ) : ℂ) = (2 * (π : ℂ))⁻¹ := by
    push_cast
    rw [one_div]
  rw [hscalar] at hm
  have hmain := congrArg (fun z : ℂ => (2 * π) * z) hm
  rw [mul_inv_cancel_left₀ (by exact_mod_cast (ne_of_gt (by positivity : 0 < 2 * π)))] at hmain
  convert hmain using 1
  · apply integral_congr_ae
    exact Eventually.of_forall fun y => by dsimp only; rw [mul_comm I, mul_comm]
  · dsimp only [f]
    rw [← ofReal_neg, ← ofReal_exp, ← ofReal_neg, ← ofReal_exp]

/-- The Cahen–Mellin formula with the principal complex power, for `c > 0` and `Re w > 0`. -/
theorem integral_Gamma_mul_cpow_neg {c : ℝ} (hc : 0 < c) {w : ℂ} (hw : 0 < w.re) :
    (∫ y : ℝ, Complex.Gamma (c + y * I) * w ^ (-((c : ℂ) + y * I))) =
      2 * π * Complex.exp (-w) := by
  have harg : |(-Complex.log w).im| < π / 2 := by
    simpa only [neg_im, abs_neg, log_im] using
      (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw))
  have h := integral_Gamma_mul_exp hc harg
  rw [neg_neg, exp_log (ne_zero_of_re_pos hw)] at h
  convert h using 1
  apply integral_congr_ae
  refine Eventually.of_forall fun y => ?_
  dsimp only
  rw [mul_comm I, cpow_def_of_ne_zero (ne_zero_of_re_pos hw)]
  congr 1
  congr 1
  ring

end DLMF.Gamma
