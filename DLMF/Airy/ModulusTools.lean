/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Asymptotics

/-!
# Tools for the Airy modulus: Nicholson's integral

* `airyMod_I k`: the moments `∫₀^∞ t^{k-1/2} e^{-t³/12} dt` in closed form, with the recurrence
  `I_{k+3} = (4k+2) I_k` and the values of `I_0, I_1, I_2` through the duplication and
  reflection formulas for `Γ`.
* `airyMod_hasSum`: the Nicholson integral `∫₀^∞ e^{zt - t³/12} t^{-1/2} dt` is the power series
  `∑ I_k z^k / k!`.
* `airyMod_iteratedDeriv_rec`: the Taylor recurrence of the product equation
  `w''' = 4 z w' + 2 w` (DLMF 9.11.1).
* `airyMod_modulus_sq_exp_integral`: DLMF 9.11.4, `Ai(z)² + Bi(z)² =
  π^{-3/2} ∫₀^∞ e^{zt - t³/12} t^{-1/2} dt` for all complex `z`, proved by comparing Taylor
  coefficients at `0`.
* The oscillatory expansions 9.7.9–9.7.12 restricted to the positive real axis
  (`airyInt_osc_real`), the growth `Ai(-s), Bi(-s) = O(s^{-1/4})`, `Ai'(-s), Bi'(-s) = O(s^{1/4})`
  and the leading terms of `Ai'(-s)`, `Bi'(-s)` with an `O(s^{-5/4})` error.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF.Confluent
open scoped Real Topology Nat
namespace DLMF.Airy

/-- `e^{at - t³/12} t^{-1/2}` is integrable on `(0, ∞)` for every real `a`. -/
theorem airyMod_integrableOn_exp (a : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (a * t) * (Real.exp (-(t ^ 3 / 12)) * t ^ (-(1 / 2) : ℝ)))
      (Ioi 0) := by
  set c : ℝ := |a| + 1
  have hc : 1 ≤ c := by simp only [c]; linarith [abs_nonneg a]
  have hint := (Real.GammaIntegral_convergent (s := 1 / 2) (by norm_num)).const_mul
    (Real.exp (12 * c ^ 2))
  refine hint.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousAt.mul
      ((Real.continuous_exp.comp (by fun_prop)).continuousAt.mul
        (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt ht))))).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    rw [Real.norm_of_nonneg (by positivity), show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num]
    have key : a * t - t ^ 3 / 12 ≤ 12 * c ^ 2 - t := by
      have h1 : a * t ≤ (c - 1) * t := by
        have : a ≤ c - 1 := by simp only [c]; linarith [le_abs_self a]
        nlinarith
      rcases le_or_gt t (12 * c) with h | h
      · nlinarith [pow_pos ht 3]
      · have : 12 * c * t ≤ t ^ 3 / 12 := by
          have : 144 * c ^ 2 ≤ t ^ 2 := by nlinarith
          nlinarith
        nlinarith
    calc Real.exp (a * t) * (Real.exp (-(t ^ 3 / 12)) * t ^ (-(1 / 2) : ℝ))
        = Real.exp (a * t - t ^ 3 / 12) * t ^ (-(1 / 2) : ℝ) := by
          rw [sub_eq_add_neg, Real.exp_add]; ring
      _ ≤ Real.exp (12 * c ^ 2 - t) * t ^ (-(1 / 2) : ℝ) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr key) (by positivity)
      _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; ring

noncomputable def airyMod_I (k : ℕ) : ℝ :=
  (1 / 12 : ℝ) ^ (-((k : ℝ) + 1 / 2) / 3) * (1 / 3) * Real.Gamma (((k : ℝ) + 1 / 2) / 3)

/-- The moment integral `∫₀^∞ t^{k-1/2} e^{-t³/12} dt` converges and equals `airyMod_I k`. -/
theorem airyMod_integral_I (k : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ ((k : ℝ) - 1 / 2) * Real.exp (-(1 / 12) * t ^ (3 : ℝ))) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), t ^ ((k : ℝ) - 1 / 2) * Real.exp (-(1 / 12) * t ^ (3 : ℝ)) =
        airyMod_I k := by
  have hq : -1 < (k : ℝ) - 1 / 2 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  refine ⟨integrableOn_rpow_mul_exp_neg_mul_rpow hq (by norm_num) (by norm_num), ?_⟩
  rw [_root_.integral_rpow_mul_exp_neg_mul_rpow (by norm_num) hq (by norm_num), airyMod_I]
  congr 3 <;> ring

/-- `I_{k+3} = (4k+2) I_k`. -/
theorem airyMod_I_add_three (k : ℕ) : airyMod_I (k + 3) = (4 * k + 2) * airyMod_I k := by
  have ha : 0 < ((k : ℝ) + 1 / 2) / 3 := by positivity
  rw [airyMod_I, airyMod_I, show (((k + 3 : ℕ) : ℝ) + 1 / 2) / 3 = ((k : ℝ) + 1 / 2) / 3 + 1 by
    push_cast; ring, Real.Gamma_add_one ha.ne',
    show -(((k + 3 : ℕ) : ℝ) + 1 / 2) / 3 = -((k : ℝ) + 1 / 2) / 3 + (-1) by push_cast; ring,
    Real.rpow_add (by norm_num), Real.rpow_neg_one]
  ring


/-- `(1/12)^{-m/6} = (2^{1/3} 3^{1/6})^m`. -/
theorem airyMod_twelve_rpow (m : ℕ) :
    (1 / 12 : ℝ) ^ (-((m : ℝ) / 6)) = ((2 : ℝ) ^ (1 / 3 : ℝ) * (3 : ℝ) ^ (1 / 6 : ℝ)) ^ m := by
  rw [Real.rpow_neg (by norm_num), one_div, Real.inv_rpow (by norm_num), inv_inv,
    show (m : ℝ) / 6 = (1 / 6) * m by ring, Real.rpow_mul_natCast (by norm_num)]
  congr 1
  rw [show (12 : ℝ) = 2 ^ (2 : ℝ) * 3 by norm_num, Real.mul_rpow (by positivity) (by norm_num),
    ← Real.rpow_mul (by norm_num)]
  norm_num

/-- Powers of `3^{1/6}`. -/
theorem airyMod_three_rpow (m : ℕ) : (3 : ℝ) ^ ((m : ℝ) / 6) = ((3 : ℝ) ^ (1 / 6 : ℝ)) ^ m := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; congr 1; ring

/-- Powers of `2^{1/3}`. -/
theorem airyMod_two_rpow (m : ℕ) : (2 : ℝ) ^ ((m : ℝ) / 3) = ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ m := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; congr 1; ring

/-- `Γ(1/3) Γ(2/3) = 2π/√3`. -/
theorem airyMod_gamma_third_reflection :
    Real.Gamma (1 / 3) * Real.Gamma (2 / 3) * Real.sqrt 3 = 2 * π := by
  have h := Real.Gamma_mul_Gamma_one_sub (1 / 3)
  rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num, show π * (1 / 3) = π / 3 by ring,
    Real.sin_pi_div_three] at h
  rw [h]; have : Real.sqrt 3 ≠ 0 := by positivity
  field_simp

/-- `I_0 = 4π^{3/2} / (3^{2/3} Γ(2/3))²`. -/
theorem airyMod_I_zero : airyMod_I 0 = 4 * π * Real.sqrt π / ((3 : ℝ) ^ (2 / 3 : ℝ) * Real.Gamma (2 / 3)) ^ 2 := by
  set u : ℝ := (3 : ℝ) ^ (1 / 6 : ℝ) with hu
  set v : ℝ := (2 : ℝ) ^ (1 / 3 : ℝ) with hv
  have hu6 : u ^ 6 = 3 := by rw [hu, ← airyMod_three_rpow]; norm_num
  have hv3 : v ^ 3 = 2 := by rw [hv, ← airyMod_two_rpow]; norm_num
  have hs3 : Real.sqrt 3 = u ^ 3 := by
    rw [Real.sqrt_eq_rpow, hu, ← airyMod_three_rpow]; norm_num
  have h23 : (3 : ℝ) ^ (2 / 3 : ℝ) = u ^ 4 := by rw [hu, ← airyMod_three_rpow]; norm_num
  have R1 := airyMod_gamma_third_reflection
  have R2 := Real.Gamma_mul_Gamma_add_half (1 / 6)
  rw [show (1 / 6 : ℝ) + 1 / 2 = 2 / 3 by norm_num, show (2 : ℝ) * (1 / 6) = 1 / 3 by norm_num,
    show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num, show (2 / 3 : ℝ) = (2 : ℕ) / 3 by norm_num,
    airyMod_two_rpow, ← hv] at R2
  rw [airyMod_I, show -(((0 : ℕ) : ℝ) + 1 / 2) / 3 = -(((1 : ℕ) : ℝ) / 6) by norm_num,
    airyMod_twelve_rpow, ← hu, ← hv, h23, show (((0 : ℕ) : ℝ) + 1 / 2) / 3 = 1 / 6 by norm_num]
  rw [hs3] at R1
  have hg : Real.Gamma (2 / 3) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have hupos : 0 < u := by positivity
  field_simp
  linear_combination (v * u ^ 9 * Real.Gamma (2 / 3)) * R2 +
    (u ^ 9 * Real.Gamma (1 / 3) * Real.Gamma (2 / 3) * Real.sqrt π) * hv3 +
    (2 * u ^ 6 * Real.sqrt π) * R1 + (4 * π * Real.sqrt π) * hu6


/-- `I_1 = 4π^{3/2} / (3^{2/3} Γ(2/3) 3^{1/3} Γ(1/3))`. -/
theorem airyMod_I_one : airyMod_I 1 = 4 * π * Real.sqrt π /
    (((3 : ℝ) ^ (2 / 3 : ℝ) * Real.Gamma (2 / 3)) * ((3 : ℝ) ^ (1 / 3 : ℝ) * Real.Gamma (1 / 3))) := by
  set u : ℝ := (3 : ℝ) ^ (1 / 6 : ℝ) with hu
  set v : ℝ := (2 : ℝ) ^ (1 / 3 : ℝ) with hv
  have hu6 : u ^ 6 = 3 := by rw [hu, ← airyMod_three_rpow]; norm_num
  have hv3 : v ^ 3 = 2 := by rw [hv, ← airyMod_two_rpow]; norm_num
  have hs3 : Real.sqrt 3 = u ^ 3 := by
    rw [Real.sqrt_eq_rpow, hu, ← airyMod_three_rpow]; norm_num
  have h23 : (3 : ℝ) ^ (2 / 3 : ℝ) = u ^ 4 := by rw [hu, ← airyMod_three_rpow]; norm_num
  have h13 : (3 : ℝ) ^ (1 / 3 : ℝ) = u ^ 2 := by rw [hu, ← airyMod_three_rpow]; norm_num
  have R1 := airyMod_gamma_third_reflection
  rw [hs3] at R1
  rw [airyMod_I, show -(((1 : ℕ) : ℝ) + 1 / 2) / 3 = -(((3 : ℕ) : ℝ) / 6) by norm_num,
    airyMod_twelve_rpow, ← hu, ← hv, h23, h13, show (((1 : ℕ) : ℝ) + 1 / 2) / 3 = 1 / 2 by norm_num,
    Real.Gamma_one_half_eq]
  have hg : Real.Gamma (2 / 3) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have hg' : Real.Gamma (1 / 3) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have hupos : 0 < u := by positivity
  field_simp
  linear_combination (u ^ 9 * Real.Gamma (1 / 3) * Real.Gamma (2 / 3)) * hv3 + (2 * u ^ 6) * R1 +
    (4 * π) * hu6

/-- `I_2 = 8π^{3/2} / (3^{1/3} Γ(1/3))²`. -/
theorem airyMod_I_two : airyMod_I 2 = 8 * π * Real.sqrt π / ((3 : ℝ) ^ (1 / 3 : ℝ) * Real.Gamma (1 / 3)) ^ 2 := by
  set u : ℝ := (3 : ℝ) ^ (1 / 6 : ℝ) with hu
  set v : ℝ := (2 : ℝ) ^ (1 / 3 : ℝ) with hv
  have hu6 : u ^ 6 = 3 := by rw [hu, ← airyMod_three_rpow]; norm_num
  have hv3 : v ^ 3 = 2 := by rw [hv, ← airyMod_two_rpow]; norm_num
  have hs3 : Real.sqrt 3 = u ^ 3 := by
    rw [Real.sqrt_eq_rpow, hu, ← airyMod_three_rpow]; norm_num
  have h13 : (3 : ℝ) ^ (1 / 3 : ℝ) = u ^ 2 := by rw [hu, ← airyMod_three_rpow]; norm_num
  have R1 := airyMod_gamma_third_reflection
  rw [hs3] at R1
  have R3 := Real.Gamma_mul_Gamma_add_half (1 / 3)
  rw [show (1 / 3 : ℝ) + 1 / 2 = 5 / 6 by norm_num, show (2 : ℝ) * (1 / 3) = 2 / 3 by norm_num,
    show (1 : ℝ) - 2 / 3 = 1 / 3 by norm_num, ← hv] at R3
  rw [airyMod_I, show -(((2 : ℕ) : ℝ) + 1 / 2) / 3 = -(((5 : ℕ) : ℝ) / 6) by norm_num,
    airyMod_twelve_rpow, ← hu, ← hv, h13, show (((2 : ℕ) : ℝ) + 1 / 2) / 3 = 5 / 6 by norm_num]
  have hg : Real.Gamma (2 / 3) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have hg' : Real.Gamma (1 / 3) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have hupos : 0 < u := by positivity
  field_simp
  linear_combination (v ^ 5 * u ^ 9 * Real.Gamma (1 / 3)) * R3 +
    (u ^ 9 * Real.Gamma (1 / 3) * Real.Gamma (2 / 3) * Real.sqrt π * (v ^ 3 + 2)) * hv3 +
    (4 * u ^ 6 * Real.sqrt π) * R1 + (8 * π * Real.sqrt π) * hu6

/-- Norm of `t^{-1/2}` for `t > 0`. -/
theorem airyMod_norm_cpow_half {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (-1 / 2 : ℂ)‖ = t ^ (-(1 / 2) : ℝ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht]; norm_num

/-- `e^{at - t³/12} t^m t^{-1/2}` is integrable on `(0, ∞)` for every real `a` and `m : ℕ`. -/
theorem airyMod_integrableOn_exp_pow (a : ℝ) (m : ℕ) :
    IntegrableOn (fun t : ℝ => Real.exp (a * t) *
      (Real.exp (-(t ^ 3 / 12)) * (t ^ m * t ^ (-(1 / 2) : ℝ)))) (Ioi 0) := by
  refine ((airyMod_integrableOn_exp (a + 1)).const_mul (m ! : ℝ)).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousAt.mul
      ((Real.continuous_exp.comp (by fun_prop)).continuousAt.mul
        ((continuous_pow m).continuousAt.mul
          (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt ht)))))).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    rw [Real.norm_of_nonneg (by positivity)]
    have h1 : t ^ m ≤ m ! * Real.exp t := by
      have := Real.pow_div_factorial_le_exp t ht.le m
      rwa [div_le_iff₀ (by positivity), mul_comm] at this
    have h2 : 0 ≤ Real.exp (a * t) * (Real.exp (-(t ^ 3 / 12)) * t ^ (-(1 / 2) : ℝ)) := by positivity
    calc Real.exp (a * t) * (Real.exp (-(t ^ 3 / 12)) * (t ^ m * t ^ (-(1 / 2) : ℝ)))
        = t ^ m * (Real.exp (a * t) * (Real.exp (-(t ^ 3 / 12)) * t ^ (-(1 / 2) : ℝ))) := by ring
      _ ≤ (m ! * Real.exp t) * (Real.exp (a * t) * (Real.exp (-(t ^ 3 / 12)) *
            t ^ (-(1 / 2) : ℝ))) := mul_le_mul_of_nonneg_right h1 h2
      _ = m ! * (Real.exp ((a + 1) * t) * (Real.exp (-(t ^ 3 / 12)) * t ^ (-(1 / 2) : ℝ))) := by
          rw [add_mul, one_mul, Real.exp_add]; ring

/-- The weighted Nicholson integrand `e^{zt - t³/12} t^m t^{-1/2}` is integrable on `(0, ∞)`,
and its integral is the power series `∑ I_{k+m} z^k / k!`. -/
theorem airyMod_hasSum_pow (m : ℕ) (z : ℂ) :
    IntegrableOn (fun t : ℝ => exp (z * t - (t : ℂ) ^ 3 / 12) * ((t : ℂ) ^ m * (t : ℂ) ^ (-1 / 2 : ℂ)))
      (Ioi 0) ∧
    HasSum (fun k : ℕ => z ^ k / k ! * (airyMod_I (k + m) : ℂ))
      (∫ t : ℝ in Ioi 0, exp (z * t - (t : ℂ) ^ 3 / 12) * ((t : ℂ) ^ m * (t : ℂ) ^ (-1 / 2 : ℂ))) := by
  set F : ℕ → ℝ → ℂ := fun k t =>
    (z * t) ^ k / k ! * (exp (-((t : ℂ) ^ 3 / 12)) * ((t : ℂ) ^ m * (t : ℂ) ^ (-1 / 2 : ℂ)))
  set bound : ℕ → ℝ → ℝ := fun k t =>
    (‖z‖ * t) ^ k / k ! * (Real.exp (-(t ^ 3 / 12)) * (t ^ m * t ^ (-(1 / 2) : ℝ)))
  have hexp : ∀ t : ℝ, exp (z * t - (t : ℂ) ^ 3 / 12) * ((t : ℂ) ^ m * (t : ℂ) ^ (-1 / 2 : ℂ)) =
      exp (z * t) * (exp (-((t : ℂ) ^ 3 / 12)) * ((t : ℂ) ^ m * (t : ℂ) ^ (-1 / 2 : ℂ))) :=
    fun t => by rw [sub_eq_add_neg, Complex.exp_add]; ring
  have hsumF : ∀ t : ℝ, HasSum (fun k => F k t)
      (exp (z * t - (t : ℂ) ^ 3 / 12) * ((t : ℂ) ^ m * (t : ℂ) ^ (-1 / 2 : ℂ))) := fun t => by
    have e := (NormedSpace.expSeries_div_hasSum_exp (z * t)).mul_right
      (exp (-((t : ℂ) ^ 3 / 12)) * ((t : ℂ) ^ m * (t : ℂ) ^ (-1 / 2 : ℂ)))
    rw [← Complex.exp_eq_exp_ℂ] at e
    rw [hexp]; exact e
  have hsumB : ∀ t : ℝ, HasSum (fun k => bound k t)
      (Real.exp (‖z‖ * t) * (Real.exp (-(t ^ 3 / 12)) * (t ^ m * t ^ (-(1 / 2) : ℝ)))) := fun t => by
    have e := (NormedSpace.expSeries_div_hasSum_exp (‖z‖ * t)).mul_right
      (Real.exp (-(t ^ 3 / 12)) * (t ^ m * t ^ (-(1 / 2) : ℝ)))
    rw [← Real.exp_eq_exp_ℝ] at e
    exact e
  have hnorm : ∀ k, ∀ t : ℝ, 0 < t → ‖F k t‖ = bound k t := fun k t ht => by
    simp only [F, bound, norm_mul, norm_div, norm_pow, norm_real, Real.norm_of_nonneg ht.le,
      Complex.norm_natCast, airyMod_norm_cpow_half ht, Complex.norm_exp]
    congr 3
    rw [show -((t : ℂ) ^ 3 / 12) = ((-(t ^ 3 / 12) : ℝ) : ℂ) by push_cast; ring, ofReal_re]
  have hcpow : ∀ t : ℝ, 0 < t → ContinuousAt (fun s : ℝ => (s : ℂ) ^ (-1 / 2 : ℂ)) t :=
    fun t ht => (continuousAt_cpow_const (Or.inl (by simpa using ht))).comp
      continuous_ofReal.continuousAt
  have hcont : ∀ k, ContinuousOn (F k) (Ioi 0) := fun k t ht => by
    refine ContinuousAt.continuousWithinAt ?_
    simp only [F]
    exact ((by fun_prop : Continuous fun s : ℝ => (z * s) ^ k / k !).continuousAt).mul
      ((by fun_prop : Continuous fun s : ℝ => exp (-((s : ℂ) ^ 3 / 12))).continuousAt.mul
        ((by fun_prop : Continuous fun s : ℝ => (s : ℂ) ^ m).continuousAt.mul (hcpow t ht)))
  have hint := airyMod_integrableOn_exp_pow ‖z‖ m
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => exp (z * t - (t : ℂ) ^ 3 / 12) * ((t : ℂ) ^ m * (t : ℂ) ^ (-1 / 2 : ℂ)))
      (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable (fun t ht => ContinuousAt.continuousWithinAt ?_)
      measurableSet_Ioi
    exact ((by fun_prop : Continuous fun s : ℝ => exp (z * s - (s : ℂ) ^ 3 / 12)).continuousAt).mul
      ((by fun_prop : Continuous fun s : ℝ => (s : ℂ) ^ m).continuousAt.mul (hcpow t ht))
  constructor
  · refine hint.mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    rw [← (hsumF t).tsum_eq, ← (hsumB t).tsum_eq]
    refine (norm_tsum_le_tsum_norm ?_).trans_eq (tsum_congr fun k => hnorm k t ht)
    exact (hsumB t).summable.congr fun k => (hnorm k t ht).symm
  have h := hasSum_integral_of_dominated_convergence (μ := volume.restrict (Ioi 0)) bound
    (fun k => (hcont k).aestronglyMeasurable measurableSet_Ioi)
    (fun k => by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
      exact (hnorm k t ht).le)
    (Eventually.of_forall fun t => (hsumB t).summable)
    (hint.congr_fun (fun t _ => (hsumB t).tsum_eq.symm) measurableSet_Ioi)
    (Eventually.of_forall hsumF)
  refine h.congr_fun fun k => ?_
  have hI := (airyMod_integral_I (k + m)).2
  rw [← hI, ← integral_complex_ofReal, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
  simp only [F]
  have e1 : t ^ (3 : ℝ) = t ^ 3 := by norm_cast
  have e2 : ((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) = (t : ℂ) ^ (1 / 2 : ℂ) := by
    rw [ofReal_cpow ht.le]; push_cast; ring_nf
  have e3 : (t : ℂ) ^ (-1 / 2 : ℂ) = ((t : ℂ) ^ (1 / 2 : ℂ))⁻¹ := by
    rw [← cpow_neg]; ring_nf
  have e4 : (t : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; simp [ht.ne']
  rw [Real.rpow_sub ht, Real.rpow_natCast, e1, ofReal_mul, ofReal_div, e2, ofReal_exp, e3]
  push_cast
  field_simp
  ring_nf

/-- The Nicholson integrand `e^{zt - t³/12} t^{-1/2}` is integrable on `(0, ∞)`, and its integral
is the power series `∑ I_k z^k / k!`. -/
theorem airyMod_hasSum (z : ℂ) :
    IntegrableOn (fun t : ℝ => exp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)) (Ioi 0) ∧
    HasSum (fun k : ℕ => z ^ k / k ! * (airyMod_I k : ℂ))
      (∫ t : ℝ in Ioi 0, exp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)) := by
  simpa using airyMod_hasSum_pow 0 z

/-- Taylor recurrence at `0` for solutions of `f''' = 4 z f' + 2 f`. -/
theorem airyMod_iteratedDeriv_rec {f f1 f2 : ℂ → ℂ} (h0 : ∀ z, HasDerivAt f (f1 z) z)
    (h1 : ∀ z, HasDerivAt f1 (f2 z) z) (h2 : ∀ z, HasDerivAt f2 (4 * z * f1 z + 2 * f z) z)
    (n : ℕ) : iteratedDeriv (n + 3) f 0 = (4 * n + 2) * iteratedDeriv n f 0 := by
  have d0 : deriv f = f1 := funext fun z => (h0 z).deriv
  have d1 : deriv f1 = f2 := funext fun z => (h1 z).deriv
  have d2 : deriv f2 = fun z => 4 * z * f1 z + 2 * f z := funext fun z => (h2 z).deriv
  have hf : Differentiable ℂ f := fun z => (h0 z).differentiableAt
  have hf1 : Differentiable ℂ f1 := fun z => (h1 z).differentiableAt
  have cf : ContDiff ℂ ⊤ f := hf.contDiff
  have cf1 : ContDiff ℂ ⊤ f1 := hf1.contDiff
  have cid : ContDiff ℂ ⊤ (fun z : ℂ => z) := contDiff_id
  rw [show n + 3 = n + 1 + 1 + 1 by ring, iteratedDeriv_succ', iteratedDeriv_succ',
    iteratedDeriv_succ', d0, d1, d2]
  have e : (fun z => 4 * z * f1 z + 2 * f z) = (fun z => 4 * (z * f1 z)) + (fun z => 2 * f z) := by
    funext z; simp only [Pi.add_apply]; ring
  have cm : ContDiff ℂ ⊤ (fun z => z * f1 z) := cid.mul cf1
  rw [e, iteratedDeriv_add ((contDiff_const (c := (4 : ℂ)).mul cm).contDiffAt.of_le le_top)
      ((contDiff_const (c := (2 : ℂ)).mul cf).contDiffAt.of_le le_top),
    iteratedDeriv_const_mul _ (cm.contDiffAt.of_le le_top),
    iteratedDeriv_const_mul _ (cf.contDiffAt.of_le le_top),
    iteratedDeriv_fun_mul (cid.contDiffAt.of_le le_top) (cf1.contDiffAt.of_le le_top)]
  simp only [iteratedDeriv_fun_id_zero]
  rcases n with _ | m
  · simp
  · rw [Finset.sum_eq_single 1 (fun i _ hi => by simp [hi]) (fun h => by simp at h)]
    simp only [ite_true, Nat.choose_one_right, mul_one, Nat.add_sub_cancel]
    rw [← d0, ← iteratedDeriv_succ']
    push_cast; ring


/-- The square sum `Ai² + Bi²` and its first two derivatives. -/
theorem airyMod_hasDerivAt_sq (z : ℂ) :
    HasDerivAt (fun w => airyAi w ^ 2 + airyBi w ^ 2)
      (2 * (airyAi z * airyAiDeriv z + airyBi z * airyBiDeriv z)) z ∧
    HasDerivAt (fun w => 2 * (airyAi w * airyAiDeriv w + airyBi w * airyBiDeriv w))
      (2 * (airyAiDeriv z ^ 2 + airyBiDeriv z ^ 2) + 2 * z * (airyAi z ^ 2 + airyBi z ^ 2)) z ∧
    HasDerivAt (fun w => 2 * (airyAiDeriv w ^ 2 + airyBiDeriv w ^ 2) +
        2 * w * (airyAi w ^ 2 + airyBi w ^ 2))
      (4 * z * (2 * (airyAi z * airyAiDeriv z + airyBi z * airyBiDeriv z)) +
        2 * (airyAi z ^ 2 + airyBi z ^ 2)) z := by
  have a := hasDerivAt_airyAi z
  have a' := hasDerivAt_airyAiDeriv z
  have b := hasDerivAt_airyBi z
  have b' := hasDerivAt_airyBiDeriv z
  refine ⟨?_, ?_, ?_⟩
  · convert (a.pow 2).add (b.pow 2) using 1; push_cast; ring
  · convert ((a.mul a').add (b.mul b')).const_mul (2 : ℂ) using 1; ring
  · have h := (((a'.pow 2).add (b'.pow 2)).const_mul (2 : ℂ)).add
      ((((hasDerivAt_id z).const_mul (2 : ℂ))).mul ((a.pow 2).add (b.pow 2)))
    exact h.congr_deriv (by simp only [id, Pi.add_apply, Pi.pow_apply]; push_cast; ring)

/-- `π^{3/2} = π √π`. -/
theorem airyMod_pi_cpow : (π : ℂ) ^ (3 / 2 : ℂ) = ((π * Real.sqrt π : ℝ) : ℂ) := by
  rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow Real.pi_pos.le,
    show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add Real.pi_pos, Real.rpow_one,
    ← Real.sqrt_eq_rpow]

/-- The Taylor coefficients of `Ai² + Bi²` at `0` are `π^{-3/2} I_n`. -/
theorem airyMod_iteratedDeriv_sq (n : ℕ) :
    iteratedDeriv n (fun w => airyAi w ^ 2 + airyBi w ^ 2) 0 =
      ((π * Real.sqrt π : ℝ) : ℂ)⁻¹ * (airyMod_I n : ℂ) := by
  have hπ := Real.pi_pos
  have hsp : 0 < Real.sqrt π := Real.sqrt_pos.mpr hπ
  have hd : ∀ z, _ := airyMod_hasDerivAt_sq
  have hA0 : airyAi 0 = ((1 / ((3 : ℝ) ^ (2 / 3 : ℝ) * Real.Gamma (2 / 3)) : ℝ) : ℂ) := by
    rw [airyAi_zero, show (2 / 3 : ℂ) = ((2 / 3 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal]
    push_cast; ring
  have hA1 : airyAiDeriv 0 = ((-1 / ((3 : ℝ) ^ (1 / 3 : ℝ) * Real.Gamma (1 / 3)) : ℝ) : ℂ) := by
    rw [airyAiDeriv_zero, show (1 / 3 : ℂ) = ((1 / 3 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal]
    push_cast; ring
  have hB0 : airyBi 0 = (Real.sqrt 3 : ℂ) * airyAi 0 := by
    simp only [airyBi, airyAi, airyG_zero, mul_zero, add_zero, sub_zero]
  have hB1 : airyBiDeriv 0 = -((Real.sqrt 3 : ℂ) * airyAiDeriv 0) := by
    simp only [airyBiDeriv, airyAiDeriv, airyFDeriv_zero, mul_zero, zero_add, zero_sub]
    ring
  have h3 : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring
  have hg2 : 0 < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have hg1 : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have p23 : 0 < (3 : ℝ) ^ (2 / 3 : ℝ) := by positivity
  have p13 : 0 < (3 : ℝ) ^ (1 / 3 : ℝ) := by positivity
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | _ | m
    · rw [iteratedDeriv_zero, airyMod_I_zero]
      rw [hB0, mul_pow, h3, hA0]
      push_cast
      field_simp
      ring
    · rw [iteratedDeriv_one, (hd 0).1.deriv, airyMod_I_one, hB0, hB1]
      have e : (2 : ℂ) * (airyAi 0 * airyAiDeriv 0 + (Real.sqrt 3 : ℂ) * airyAi 0 *
          -((Real.sqrt 3 : ℂ) * airyAiDeriv 0)) = -4 * airyAi 0 * airyAiDeriv 0 := by
        linear_combination (-2 * airyAi 0 * airyAiDeriv 0) * h3
      rw [e, hA0, hA1]
      push_cast
      field_simp
    · rw [iteratedDeriv_succ, iteratedDeriv_one]
      have d0 : deriv (fun w => airyAi w ^ 2 + airyBi w ^ 2) =
          fun w => 2 * (airyAi w * airyAiDeriv w + airyBi w * airyBiDeriv w) :=
        funext fun z => (hd z).1.deriv
      rw [d0, (hd 0).2.1.deriv, airyMod_I_two, hB1, mul_zero, zero_mul, add_zero, neg_sq, mul_pow, h3,
        hA1]
      push_cast
      field_simp
      ring
    · rw [airyMod_iteratedDeriv_rec (fun z => (hd z).1) (fun z => (hd z).2.1) (fun z => (hd z).2.2) m,
        ih m (by omega), airyMod_I_add_three]
      push_cast; ring

/-- **Nicholson-type integral** (DLMF 9.11.4): `Ai(z)² + Bi(z)² =
π^{-3/2} ∫₀^∞ e^{zt - t³/12} t^{-1/2} dt` for every complex `z`. -/
theorem airyMod_modulus_sq_exp_integral (z : ℂ) :
    IntegrableOn (fun t : ℝ => exp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)) (Ioi 0) ∧
      airyAi z ^ 2 + airyBi z ^ 2 =
        (∫ t : ℝ in Ioi 0, exp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)) /
          (π : ℂ) ^ (3 / 2 : ℂ) := by
  obtain ⟨hint, hsum⟩ := airyMod_hasSum z
  refine ⟨hint, ?_⟩
  have hp : Differentiable ℂ (fun w => airyAi w ^ 2 + airyBi w ^ 2) :=
    (differentiable_airyAi.pow 2).add (differentiable_airyBi.pow 2)
  have ht := hasSum_taylorSeries_of_entire hp 0 z
  simp only [sub_zero, airyMod_iteratedDeriv_sq, smul_eq_mul] at ht
  have h2 := hsum.mul_left (((π * Real.sqrt π : ℝ) : ℂ)⁻¹)
  rw [airyMod_pi_cpow, div_eq_inv_mul]
  refine ht.unique (h2.congr_fun fun k => ?_)
  ring

/-- The companion Nicholson-type formula for the derivatives:
`Ai'(z)² + Bi'(z)² = π^{-3/2} ∫₀^∞ e^{zt - t³/12} (t^{3/2}/2 - z t^{-1/2}) dt`, written with the
two moment integrals. -/
theorem airyMod_derivModulus_sq_integral (z : ℂ) :
    airyAiDeriv z ^ 2 + airyBiDeriv z ^ 2 =
      (∫ t : ℝ in Ioi 0, exp (z * t - (t : ℂ) ^ 3 / 12) * ((t : ℂ) ^ 2 * (t : ℂ) ^ (-1 / 2 : ℂ))) /
          (2 * (π : ℂ) ^ (3 / 2 : ℂ)) -
        z * ((∫ t : ℝ in Ioi 0, exp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)) /
          (π : ℂ) ^ (3 / 2 : ℂ)) := by
  set p : ℂ → ℂ := fun w => airyAi w ^ 2 + airyBi w ^ 2 with hp
  have hd := airyMod_hasDerivAt_sq
  have d0 : deriv p = fun w => 2 * (airyAi w * airyAiDeriv w + airyBi w * airyBiDeriv w) :=
    funext fun w => (hd w).1.deriv
  have d1 : deriv (deriv p) = fun w => 2 * (airyAiDeriv w ^ 2 + airyBiDeriv w ^ 2) +
      2 * w * (airyAi w ^ 2 + airyBi w ^ 2) := by
    rw [d0]; exact funext fun w => (hd w).2.1.deriv
  have hg : Differentiable ℂ (deriv (deriv p)) := by
    rw [d1]; exact fun w => ((hd w).2.2).differentiableAt
  have ht := hasSum_taylorSeries_of_entire hg 0 z
  have hit : ∀ n, iteratedDeriv n (deriv (deriv p)) 0 =
      ((π * Real.sqrt π : ℝ) : ℂ)⁻¹ * (airyMod_I (n + 2) : ℂ) := fun n => by
    rw [← iteratedDeriv_succ', ← iteratedDeriv_succ', hp, airyMod_iteratedDeriv_sq]
  simp only [sub_zero, hit, smul_eq_mul] at ht
  have h2 := (airyMod_hasSum_pow 2 z).2.mul_left (((π * Real.sqrt π : ℝ) : ℂ)⁻¹)
  have hg2 := ht.unique (h2.congr_fun fun k => by ring)
  rw [d1] at hg2
  have hp2 := (airyMod_modulus_sq_exp_integral z).2
  simp only at hg2
  rw [← hp2, airyMod_pi_cpow]
  linear_combination (1 / 2 : ℂ) * hg2

/-- The Nicholson-type formula for the cross term:
`Ai(z) Ai'(z) + Bi(z) Bi'(z) = π^{-3/2}/2 ∫₀^∞ e^{zt - t³/12} t^{1/2} dt`. -/
theorem airyMod_cross_integral (z : ℂ) :
    airyAi z * airyAiDeriv z + airyBi z * airyBiDeriv z =
      (∫ t : ℝ in Ioi 0, exp (z * t - (t : ℂ) ^ 3 / 12) * ((t : ℂ) ^ 1 * (t : ℂ) ^ (-1 / 2 : ℂ))) /
          (2 * (π : ℂ) ^ (3 / 2 : ℂ)) := by
  set p : ℂ → ℂ := fun w => airyAi w ^ 2 + airyBi w ^ 2 with hp
  have hd := airyMod_hasDerivAt_sq
  have d0 : deriv p = fun w => 2 * (airyAi w * airyAiDeriv w + airyBi w * airyBiDeriv w) :=
    funext fun w => (hd w).1.deriv
  have hg : Differentiable ℂ (deriv p) := by
    rw [d0]; exact fun w => ((hd w).2.1).differentiableAt
  have ht := hasSum_taylorSeries_of_entire hg 0 z
  have hit : ∀ n, iteratedDeriv n (deriv p) 0 =
      ((π * Real.sqrt π : ℝ) : ℂ)⁻¹ * (airyMod_I (n + 1) : ℂ) := fun n => by
    rw [← iteratedDeriv_succ', hp, airyMod_iteratedDeriv_sq]
  simp only [sub_zero, hit, smul_eq_mul] at ht
  have h2 := (airyMod_hasSum_pow 1 z).2.mul_left (((π * Real.sqrt π : ℝ) : ℂ)⁻¹)
  have hg2 := ht.unique (h2.congr_fun fun k => by ring)
  rw [d0] at hg2
  simp only at hg2
  rw [airyMod_pi_cpow]
  linear_combination (1 / 2 : ℂ) * hg2

/-! ### The oscillatory expansions on the positive real axis -/

/-- The positive real axis tends to infinity inside every Airy sector. -/
theorem airyInt_tendsto_ofReal_sector {α : ℝ} (hα : 0 ≤ α) :
    Tendsto (fun s : ℝ => (s : ℂ)) atTop (airySector α) := by
  unfold airySector
  refine tendsto_inf.2 ⟨tendsto_comap_iff.2 ?_, tendsto_principal.2 ?_⟩
  · refine tendsto_abs_atTop_atTop.congr fun s => ?_
    simp [Complex.norm_real]
  · filter_upwards [eventually_gt_atTop 0] with s hs
    exact ⟨ofReal_ne_zero.2 hs.ne', by rw [arg_ofReal_of_nonneg hs.le]; simpa using hα⟩

/-- `‖s^{1/4}‖ = s^{1/4}` for `s > 0`. -/
theorem airyInt_norm_cpow_quarter {s : ℝ} (hs : 0 < s) :
    ‖(s : ℂ) ^ (1 / 4 : ℂ)‖ = s ^ (1 / 4 : ℝ) := by
  rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hs.le,
    Complex.norm_real, Real.norm_of_nonneg (by positivity)]

/-- The oscillatory error envelope on the positive real axis. -/
theorem airyInt_oscError_ofReal (kind : AiryKind) (N M : ℕ) {s : ℝ} (hs : 0 < s) :
    airyOscError kind N M s = ‖airyOscPrefactor kind s‖ *
      (airyZeta s ^ (-(2 * N : ℤ)) + airyZeta s ^ (-(2 * M + 1 : ℤ))) := by
  rw [airyOscError, airyReal_zeta_ofReal hs, ofReal_im, abs_zero, Real.exp_zero, mul_one,
    Complex.norm_real, Real.norm_of_nonneg (airyZeta_pos hs).le]

/-- Norm of the oscillatory prefactor of `Ai(-s)`. -/
theorem airyInt_norm_oscPrefactor_ai {s : ℝ} (hs : 0 < s) :
    ‖airyOscPrefactor .ai s‖ = (Real.sqrt π)⁻¹ * s ^ (-(1 / 4) : ℝ) := by
  rw [airyOscPrefactor, norm_div, norm_one, norm_mul, airyInt_norm_cpow_quarter hs,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.rpow_neg hs.le]
  field_simp

/-- Norm of the oscillatory prefactor of `Bi(-s)`. -/
theorem airyInt_norm_oscPrefactor_bi {s : ℝ} (hs : 0 < s) :
    ‖airyOscPrefactor .bi s‖ = (Real.sqrt π)⁻¹ * s ^ (-(1 / 4) : ℝ) := by
  rw [airyOscPrefactor, norm_div, norm_one, norm_mul, airyInt_norm_cpow_quarter hs,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.rpow_neg hs.le]
  field_simp

/-- Norm of the oscillatory prefactor of `Ai'(-s)`. -/
theorem airyInt_norm_oscPrefactor_aiDeriv {s : ℝ} (hs : 0 < s) :
    ‖airyOscPrefactor .aiDeriv s‖ = (Real.sqrt π)⁻¹ * s ^ (1 / 4 : ℝ) := by
  rw [airyOscPrefactor, norm_div, airyInt_norm_cpow_quarter hs,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  ring

/-- Norm of the oscillatory prefactor of `Bi'(-s)`. -/
theorem airyInt_norm_oscPrefactor_biDeriv {s : ℝ} (hs : 0 < s) :
    ‖airyOscPrefactor .biDeriv s‖ = (Real.sqrt π)⁻¹ * s ^ (1 / 4 : ℝ) := by
  rw [airyOscPrefactor, norm_div, airyInt_norm_cpow_quarter hs,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  ring

/-- `ζ(s)⁻¹ = (3/2) s^{-3/2}`. -/
theorem airyInt_airyZeta_recip {s : ℝ} (hs : 0 < s) :
    (airyZeta s)⁻¹ = 3 / 2 * s ^ (-(3 / 2) : ℝ) := by
  rw [airyZeta, Real.rpow_neg hs.le]; field_simp

/-- `ζ(s) ≥ 2/3` for `s ≥ 1`. -/
theorem airyInt_two_thirds_le_airyZeta {s : ℝ} (hs : 1 ≤ s) : 2 / 3 ≤ airyZeta s := by
  unfold airyZeta
  have : 1 ≤ s ^ (3 / 2 : ℝ) := Real.one_le_rpow hs (by norm_num)
  linarith

/-- The envelope with `N = M = 0` is at most `(5/2)|pref|` for `s ≥ 1`. -/
theorem airyInt_oscError_zero_le (kind : AiryKind) {s : ℝ} (hs : 1 ≤ s) :
    airyOscError kind 0 0 s ≤ 5 / 2 * ‖airyOscPrefactor kind s‖ := by
  have hs0 : 0 < s := by linarith
  rw [airyInt_oscError_ofReal kind 0 0 hs0]
  have hz := airyInt_two_thirds_le_airyZeta hs
  have hz0 : 0 < airyZeta s := by linarith
  norm_num only [Nat.cast_zero, mul_zero, neg_zero, zpow_zero, zero_add, zpow_neg_one]
  have : (airyZeta s)⁻¹ ≤ 3 / 2 := by
    rw [inv_le_comm₀ hz0 (by norm_num)]; linarith
  have hp := norm_nonneg (airyOscPrefactor kind s)
  nlinarith

/-- The envelope with `N = 1, M = 0` is at most `(15/4)|pref| s^{-3/2}` for `s ≥ 1`. -/
theorem airyInt_oscError_one_zero_le (kind : AiryKind) {s : ℝ} (hs : 1 ≤ s) :
    airyOscError kind 1 0 s ≤ 15 / 4 * ‖airyOscPrefactor kind s‖ * s ^ (-(3 / 2) : ℝ) := by
  have hs0 : 0 < s := by linarith
  rw [airyInt_oscError_ofReal kind 1 0 hs0]
  have hz := airyInt_two_thirds_le_airyZeta hs
  have hz0 : 0 < airyZeta s := by linarith
  have hi := airyInt_airyZeta_recip hs0
  norm_num only [Nat.cast_one, Nat.cast_zero, mul_one, mul_zero, zero_add, zpow_neg_one]
  rw [show (-(2 : ℤ)) = (-1) * 2 by norm_num, zpow_mul, zpow_neg_one, hi]
  have hsr : s ^ (-(3 / 2) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hs (by norm_num)
  have hsr0 : 0 < s ^ (-(3 / 2) : ℝ) := Real.rpow_pos_of_pos hs0 _
  have hp := norm_nonneg (airyOscPrefactor kind s)
  have : (3 / 2 * s ^ (-(3 / 2) : ℝ)) ^ (2 : ℤ) ≤ 9 / 4 * s ^ (-(3 / 2) : ℝ) := by
    rw [zpow_two]; nlinarith
  nlinarith


/-- The four oscillatory expansions 9.7.9–9.7.12 restricted to the positive real axis. -/
theorem airyInt_osc_real (kind : AiryKind) (N M : ℕ) :
    (fun s : ℝ => airyFunction kind (-(s : ℂ)) - airyOscApprox kind N M s) =O[atTop]
      (fun s : ℝ => airyOscError kind N M s) := by
  have hπ := Real.pi_pos
  have hδ : (0 : ℝ) < π / 3 := by positivity
  have hδ' : π / 3 < 2 * π / 3 := by linarith
  have hT := airyInt_tendsto_ofReal_sector (α := 2 * π / 3 - π / 3) (by linarith)
  cases kind
  · exact (airy_ai_oscillatory_expansion hδ hδ' N M).comp_tendsto hT
  · exact (airy_aiDeriv_oscillatory_expansion hδ hδ' N M).comp_tendsto hT
  · exact (airy_bi_oscillatory_expansion hδ hδ' N M).comp_tendsto hT
  · exact (airy_biDeriv_oscillatory_expansion hδ hδ' N M).comp_tendsto hT

/-- The oscillatory error bound is nonnegative. -/
theorem airyInt_oscError_nonneg (kind : AiryKind) (N M : ℕ) (z : ℂ) :
    0 ≤ airyOscError kind N M z := by
  unfold airyOscError; positivity

/-- Crude growth on the negative axis: `w(-s) = O(|prefactor|)`. -/
theorem airyInt_neg_isBigO_prefactor (kind : AiryKind) :
    (fun s : ℝ => airyFunction kind (-(s : ℂ))) =O[atTop]
      (fun s : ℝ => ‖airyOscPrefactor kind s‖) := by
  have h := airyInt_osc_real kind 0 0
  have h0 : ∀ s : ℝ, airyOscApprox kind 0 0 s = 0 := fun s => by
    cases kind <;> simp [airyOscApprox, airyOscSum]
  simp only [h0, sub_zero] at h
  refine h.trans (IsBigO.of_bound (5 / 2) ?_)
  filter_upwards [eventually_ge_atTop 1] with s hs
  rw [Real.norm_of_nonneg (airyInt_oscError_nonneg kind 0 0 _), norm_norm]
  exact airyInt_oscError_zero_le kind hs


/-- Transfer a big-O bound by a prefactor of the form `π^{-1/2} s^a`. -/
theorem airyInt_isBigO_of_norm_prefactor {g : ℝ → ℂ} {p : ℝ → ℝ} {a : ℝ}
    (hg : g =O[atTop] p) (hp : ∀ s : ℝ, 0 < s → p s = (Real.sqrt π)⁻¹ * s ^ a) :
    g =O[atTop] (fun s : ℝ => s ^ a) := by
  refine hg.trans (IsBigO.of_bound ((Real.sqrt π)⁻¹) ?_)
  filter_upwards [eventually_gt_atTop 0] with s hs
  rw [hp s hs, norm_mul, Real.norm_of_nonneg (by positivity)]

/-- `Ai(-s) = O(s^{-1/4})` as `s → ∞`. -/
theorem airyInt_ai_neg_isBigO :
    (fun s : ℝ => airyAi (-(s : ℂ))) =O[atTop] (fun s : ℝ => s ^ (-(1 / 4) : ℝ)) :=
  airyInt_isBigO_of_norm_prefactor (airyInt_neg_isBigO_prefactor .ai)
    fun _ hs => airyInt_norm_oscPrefactor_ai hs

/-- `Bi(-s) = O(s^{-1/4})` as `s → ∞`. -/
theorem airyInt_bi_neg_isBigO :
    (fun s : ℝ => airyBi (-(s : ℂ))) =O[atTop] (fun s : ℝ => s ^ (-(1 / 4) : ℝ)) :=
  airyInt_isBigO_of_norm_prefactor (airyInt_neg_isBigO_prefactor .bi)
    fun _ hs => airyInt_norm_oscPrefactor_bi hs

/-- `Ai'(-s) = O(s^{1/4})` as `s → ∞`. -/
theorem airyInt_aiDeriv_neg_isBigO :
    (fun s : ℝ => airyAiDeriv (-(s : ℂ))) =O[atTop] (fun s : ℝ => s ^ (1 / 4 : ℝ)) :=
  airyInt_isBigO_of_norm_prefactor (airyInt_neg_isBigO_prefactor .aiDeriv)
    fun _ hs => airyInt_norm_oscPrefactor_aiDeriv hs

/-- `Bi'(-s) = O(s^{1/4})` as `s → ∞`. -/
theorem airyInt_biDeriv_neg_isBigO :
    (fun s : ℝ => airyBiDeriv (-(s : ℂ))) =O[atTop] (fun s : ℝ => s ^ (1 / 4 : ℝ)) :=
  airyInt_isBigO_of_norm_prefactor (airyInt_neg_isBigO_prefactor .biDeriv)
    fun _ hs => airyInt_norm_oscPrefactor_biDeriv hs

/-- The complex power `s^{1/4}` of a positive real is real. -/
theorem airyInt_cpow_quarter_ofReal {s : ℝ} (hs : 0 < s) :
    (s : ℂ) ^ (1 / 4 : ℂ) = ((s ^ (1 / 4 : ℝ) : ℝ) : ℂ) := by
  rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hs.le]

/-- The phase `ζ(s) - π/4` is real for `s > 0`. -/
theorem airyInt_theta_ofReal {s : ℝ} (hs : 0 < s) :
    airyZetaComplex s - π / 4 = ((airyZeta s - π / 4 : ℝ) : ℂ) := by
  rw [airyReal_zeta_ofReal hs]; push_cast; ring

/-- Envelope `N = 1, M = 0` for the derivative kinds is `O(s^{-5/4})`. -/
theorem airyInt_oscError_deriv_isBigO {kind : AiryKind} (hk : kind = .aiDeriv ∨ kind = .biDeriv) :
    (fun s : ℝ => airyOscError kind 1 0 s) =O[atTop] (fun s : ℝ => s ^ (-(5 / 4) : ℝ)) := by
  refine IsBigO.of_bound (15 / 4 * (Real.sqrt π)⁻¹) ?_
  filter_upwards [eventually_ge_atTop 1] with s hs
  have hs0 : 0 < s := by linarith
  have hn : ‖airyOscPrefactor kind s‖ = (Real.sqrt π)⁻¹ * s ^ (1 / 4 : ℝ) := by
    rcases hk with rfl | rfl
    · exact airyInt_norm_oscPrefactor_aiDeriv hs0
    · exact airyInt_norm_oscPrefactor_biDeriv hs0
  rw [Real.norm_of_nonneg (airyInt_oscError_nonneg _ _ _ _), Real.norm_of_nonneg (by positivity)]
  have h := airyInt_oscError_one_zero_le kind hs
  rw [hn] at h
  have e : s ^ (-(5 / 4) : ℝ) = s ^ (1 / 4 : ℝ) * s ^ (-(3 / 2) : ℝ) := by
    rw [← Real.rpow_add hs0]; norm_num
  rw [e]; linarith

/-- `Ai'(-s) = π^{-1/2} s^{1/4} sin(ζ - π/4) + O(s^{-5/4})`. -/
theorem airyInt_aiDeriv_neg_sub :
    (fun s : ℝ => airyAiDeriv (-(s : ℂ)) -
      ((s ^ (1 / 4 : ℝ) / Real.sqrt π * Real.sin (airyZeta s - π / 4) : ℝ) : ℂ))
      =O[atTop] (fun s : ℝ => s ^ (-(5 / 4) : ℝ)) := by
  refine ((airyInt_osc_real .aiDeriv 1 0).trans
    (airyInt_oscError_deriv_isBigO (Or.inl rfl))).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with s hs
  simp only [airyOscApprox, airyOscPrefactor, airyOscSum, airyFunction]
  rw [airyInt_theta_ofReal hs, airyInt_cpow_quarter_ofReal hs]
  simp [airyReal_airyV_zero, ofReal_sin]

/-- `Bi'(-s) = π^{-1/2} s^{1/4} cos(ζ - π/4) + O(s^{-5/4})`. -/
theorem airyInt_biDeriv_neg_sub :
    (fun s : ℝ => airyBiDeriv (-(s : ℂ)) -
      ((s ^ (1 / 4 : ℝ) / Real.sqrt π * Real.cos (airyZeta s - π / 4) : ℝ) : ℂ))
      =O[atTop] (fun s : ℝ => s ^ (-(5 / 4) : ℝ)) := by
  refine ((airyInt_osc_real .biDeriv 1 0).trans
    (airyInt_oscError_deriv_isBigO (Or.inr rfl))).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with s hs
  simp only [airyOscApprox, airyOscPrefactor, airyOscSum, airyFunction]
  rw [airyInt_theta_ofReal hs, airyInt_cpow_quarter_ofReal hs]
  simp [airyReal_airyV_zero, ofReal_cos]

/-- Envelope `N = 1, M = 0` for `Ai`, `Bi` is `O(s^{-7/4})`. -/
theorem airyMod_oscError_isBigO {kind : AiryKind} (hk : kind = .ai ∨ kind = .bi) :
    (fun s : ℝ => airyOscError kind 1 0 s) =O[atTop] (fun s : ℝ => s ^ (-(7 / 4) : ℝ)) := by
  refine IsBigO.of_bound (15 / 4 * (Real.sqrt π)⁻¹) ?_
  filter_upwards [eventually_ge_atTop 1] with s hs
  have hs0 : 0 < s := by linarith
  have hn : ‖airyOscPrefactor kind s‖ = (Real.sqrt π)⁻¹ * s ^ (-(1 / 4) : ℝ) := by
    rcases hk with rfl | rfl
    · exact airyInt_norm_oscPrefactor_ai hs0
    · exact airyInt_norm_oscPrefactor_bi hs0
  rw [Real.norm_of_nonneg (airyInt_oscError_nonneg _ _ _ _), Real.norm_of_nonneg (by positivity)]
  have h := airyInt_oscError_one_zero_le kind hs
  rw [hn] at h
  have e : s ^ (-(7 / 4) : ℝ) = s ^ (-(1 / 4) : ℝ) * s ^ (-(3 / 2) : ℝ) := by
    rw [← Real.rpow_add hs0]; norm_num
  rw [e]; linarith

/-- `Ai(-s) = π^{-1/2} s^{-1/4} cos(ζ - π/4) + O(s^{-7/4})`. -/
theorem airyMod_ai_neg_sub :
    (fun s : ℝ => airyAi (-(s : ℂ)) -
      ((s ^ (-(1 / 4) : ℝ) / Real.sqrt π * Real.cos (airyZeta s - π / 4) : ℝ) : ℂ))
      =O[atTop] (fun s : ℝ => s ^ (-(7 / 4) : ℝ)) := by
  refine ((airyInt_osc_real .ai 1 0).trans
    (airyMod_oscError_isBigO (Or.inl rfl))).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with s hs
  simp only [airyOscApprox, airyOscPrefactor, airyOscSum, airyFunction]
  rw [airyInt_theta_ofReal hs, airyInt_cpow_quarter_ofReal hs, Real.rpow_neg hs.le]
  simp [airyReal_airyU_zero, ofReal_cos]
  ring_nf
  simp

/-- `Bi(-s) = -π^{-1/2} s^{-1/4} sin(ζ - π/4) + O(s^{-7/4})`. -/
theorem airyMod_bi_neg_sub :
    (fun s : ℝ => airyBi (-(s : ℂ)) +
      ((s ^ (-(1 / 4) : ℝ) / Real.sqrt π * Real.sin (airyZeta s - π / 4) : ℝ) : ℂ))
      =O[atTop] (fun s : ℝ => s ^ (-(7 / 4) : ℝ)) := by
  refine ((airyInt_osc_real .bi 1 0).trans
    (airyMod_oscError_isBigO (Or.inr rfl))).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with s hs
  simp only [airyOscApprox, airyOscPrefactor, airyOscSum, airyFunction]
  rw [airyInt_theta_ofReal hs, airyInt_cpow_quarter_ofReal hs, Real.rpow_neg hs.le]
  simp [airyReal_airyU_zero, ofReal_sin]
  ring_nf
  simp

end DLMF.Airy
