/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ErrorFunctions.Integrals.GaussianAndCauchy

/-!
# Mellin-Barnes and Laplace transforms of Fresnel functions

Mellin-Barnes representations of auxiliary Fresnel functions and Laplace transforms of
oscillatory Gaussian kernels.

Source references and common attribution are retained in
`DLMF.ErrorFunctions.Integrals`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Confluent

/-! ### Mellin–Barnes integrals for the auxiliary Fresnel functions (DLMF 7.7.13–14)

The Laplace forms 7.7.10–11 and the Gaussian Mellin transform give the Mellin transform of
`X ↦ f(2 X^{1/4}/√π)` and `X ↦ g(2 X^{1/4}/√π)`; Mellin inversion
(`mellinInv_mellin_eq`) gives 7.7.13–14 on the positive axis, and analytic continuation in
`1/z` (`DLMF.Gamma.differentiableOn_integral_mul_cpow`) extends them to `|arg z| < π/2`. -/

section FresnelMellinBarnes

/-- `∫₀^∞ t^{2a-1}/(t²+1) dt = Γ(a) Γ(1-a)/2` for `0 < Re a < 1`. -/
theorem fresMB_integral_cpow_div {a : ℂ} (h0 : 0 < a.re) (h1 : a.re < 1) :
    ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (2 * a - 1) / ((t : ℂ) ^ 2 + 1) = Gamma a * Gamma (1 - a) / 2 := by
  have h1a : 0 < (1 - a).re := by simp; linarith
  have hb := DLMF.Gamma.beta_on_Ioi h0 h1a
  rw [show a + (1 - a) = 1 by ring] at hb
  simp only [cpow_one] at hb
  have hG := Complex.Gamma_mul_Gamma_eq_betaIntegral h0 h1a
  rw [show a + (1 - a) = 1 by ring, Complex.Gamma_one, one_mul] at hG
  have h := integral_comp_rpow_Ioi
    (fun u : ℝ => (1 / 2 : ℂ) * ((u : ℂ) ^ (a - 1) / (1 + (u : ℂ)))) (p := 2) two_ne_zero
  rw [integral_const_mul, hb, ← hG] at h
  rw [show Gamma a * Gamma (1 - a) / 2 = 1 / 2 * (Gamma a * Gamma (1 - a)) by ring, ← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx : 0 < x := hx
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  rw [abs_two, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two,
    DLMF.Bessel.kMel_ofReal_sq_cpow hx, real_smul]
  have hd : (1 : ℂ) + ((x ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 1 + x ^ 2 := by positivity
    exact_mod_cast this.ne'
  have hd' : (x : ℂ) ^ 2 + 1 ≠ 0 := by
    have : (0 : ℝ) < x ^ 2 + 1 := by positivity
    exact_mod_cast this.ne'
  have e : (x : ℂ) * (x : ℂ) ^ (2 * (a - 1)) = (x : ℂ) ^ (2 * a - 1) := by
    conv_lhs => arg 1; rw [← cpow_one (x : ℂ)]
    rw [← cpow_add _ _ hx0]; ring_nf
  push_cast
  rw [add_comm (1 : ℂ) ((x : ℂ) ^ 2), ← e]
  field_simp

/-- Integrability of `t^q/(t²+1)` on `(0, ∞)` for `-1 < q < 1`. -/
theorem fresMB_integrableOn_rpow_div {q : ℝ} (h0 : -1 < q) (h1 : q < 1) :
    IntegrableOn (fun t : ℝ => t ^ q / (t ^ 2 + 1)) (Ioi 0) := by
  set p : ℝ := (q + 1) / 2 with hp
  have hp0 : 0 < p := by rw [hp]; linarith
  have hp1 : 0 < 1 - p := by rw [hp]; linarith
  obtain ⟨hint, -⟩ := DLMF.Gamma.real_beta_on_Ioi hp0 hp1
  rw [show p + (1 - p) = 1 by ring] at hint
  simp only [Real.rpow_one] at hint
  have h := (integrableOn_Ioi_comp_rpow_iff
    (fun u : ℝ => (1 / 2 : ℝ) * (u ^ (p - 1) / (1 + u))) (p := 2) two_ne_zero).mpr
    (hint.const_mul _)
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx : 0 < x := hx
  simp only [smul_eq_mul]
  rw [abs_two, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, ← Real.rpow_mul hx.le,
    show (2 : ℝ) * (p - 1) = q - 1 by rw [hp]; ring, Real.rpow_two, Real.rpow_sub hx, Real.rpow_one]
  have : (0 : ℝ) < x ^ 2 + 1 := by positivity
  field_simp
  ring

/-- The Fresnel auxiliary functions `f` (`aux = false`) and `g` (`aux = true`). -/
def fresMB_aux (aux : Bool) (z : ℂ) : ℂ := if aux then fresnelAuxGComplex z else fresnelAuxFComplex z

/-- The kernel of the double integral for the Mellin transform of the auxiliary functions. -/
def fresMB_kernel (k : ℕ) (w : ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.1 : ℂ) ^ ((k : ℂ) - 1 / 2) / ((p.1 : ℂ) ^ 2 + 1) *
    ((p.2 : ℂ) ^ (w - 1) * exp (-(((π * p.1 / 2 : ℝ) : ℂ) * (p.2 : ℂ) ^ 2)))

/-- Measurability of the indicated function: `Measurable (fresMB_kernel k w)`. -/
theorem fresMB_measurable_kernel (k : ℕ) (w : ℂ) : Measurable (fresMB_kernel k w) := by
  unfold fresMB_kernel; fun_prop

/-- Identity under the stated parameter and domain assumptions: `∫ x : ℝ in Ioi 0, ‖fresMB_kernel
k w (t, x)‖ = (π / 2) ^ (-w.re / 2) * (1 / 2) * Real.Gamma (w.re / 2) * (t ^ ((k : ℝ) - 1 / 2
- w.re / 2) / (t ^ 2 + 1))`. -/
theorem fresMB_norm_inner (k : ℕ) {w : ℂ} (hw : 0 < w.re) {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ in Ioi 0, ‖fresMB_kernel k w (t, x)‖ =
      (π / 2) ^ (-w.re / 2) * (1 / 2) * Real.Gamma (w.re / 2) *
        (t ^ ((k : ℝ) - 1 / 2 - w.re / 2) / (t ^ 2 + 1)) := by
  have hb : (0 : ℝ) < π * t / 2 := by positivity
  simp only [fresMB_kernel, norm_mul]
  rw [integral_const_mul, DLMF.Bessel.kMel_norm_integral_gauss hw hb, norm_div,
    norm_cpow_eq_rpow_re_of_pos ht]
  have hd : ‖(t : ℂ) ^ 2 + 1‖ = t ^ 2 + 1 := by
    rw [show (t : ℂ) ^ 2 + 1 = ((t ^ 2 + 1 : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hd, show π * t / 2 = (π / 2) * t by ring, Real.mul_rpow (by positivity) ht.le]
  have hre : ((k : ℂ) - 1 / 2).re = (k : ℝ) - 1 / 2 := by simp
  rw [hre]
  rw [show (k : ℝ) - 1 / 2 - w.re / 2 = ((k : ℝ) - 1 / 2) + (-w.re / 2) by ring,
    Real.rpow_add ht]
  norm_num
  ring

/-- Integrability of the indicated kernel: `Integrable (fresMB_kernel k w) ((volume.restrict (Ioi
(0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))`. -/
theorem fresMB_integrable_kernel {k : ℕ} (hk : k ≤ 1) {w : ℂ} (hw : 0 < w.re)
    (hw1 : w.re < 2 * k + 1) :
    Integrable (fresMB_kernel k w) ((volume.restrict (Ioi (0 : ℝ))).prod
      (volume.restrict (Ioi (0 : ℝ)))) := by
  have hk' : (k : ℝ) ≤ 1 := by exact_mod_cast hk
  refine (integrable_prod_iff (fresMB_measurable_kernel k w).aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht : 0 < t := ht
    have hb : (0 : ℝ) < π * t / 2 := by positivity
    simp only [fresMB_kernel]
    exact (DLMF.Bessel.kMel_integrableOn_gauss hw hb).const_mul _
  · refine IntegrableOn.congr_fun ((fresMB_integrableOn_rpow_div (q := (k : ℝ) - 1 / 2 - w.re / 2)
      (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) (by linarith)).const_mul
      ((π / 2) ^ (-w.re / 2) * (1 / 2) * Real.Gamma (w.re / 2))) (fun t ht => ?_) measurableSet_Ioi
    exact (fresMB_norm_inner k hw ht).symm

/-- Identity under the stated parameter and domain assumptions: `(x : ℂ) ^ (w - 1) • fresMB_aux
aux x = 1 / (π * Real.sqrt 2) * ∫ t : ℝ in Ioi 0, fresMB_kernel (if aux then 1 else 0) w (t,
x)`. -/
theorem fresMB_pointwise (aux : Bool) (w : ℂ) {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ (w - 1) • fresMB_aux aux x = 1 / (π * Real.sqrt 2) *
      ∫ t : ℝ in Ioi 0, fresMB_kernel (if aux then 1 else 0) w (t, x) := by
  have harg : |arg (x : ℂ)| ≤ π / 4 := by
    rw [arg_ofReal_of_nonneg hx.le, abs_zero]; positivity
  have h := erfInt_fresnelAux_laplace aux harg
  rw [smul_eq_mul, fresMB_aux, h]
  rw [← mul_assoc, mul_comm ((x : ℂ) ^ (w - 1)), mul_assoc, ← integral_const_mul]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [fresMB_kernel]
  have e : exp (-↑π * (x : ℂ) ^ 2 * ↑t / 2) = exp (-(((π * t / 2 : ℝ) : ℂ) * (x : ℂ) ^ 2)) := by
    congr 1; push_cast; ring
  rw [e]; ring

/-- Identity under the stated parameter and domain assumptions: `∫ x : ℝ in Ioi 0, fresMB_kernel k
w (t, x) = ((2 / π : ℝ) : ℂ) ^ (w / 2) * Gamma (w / 2) / 2 * ((t : ℂ) ^ (2 * ((k : ℂ) / 2 + 1
/ 4 - w / 4) - 1) / ((t : ℂ) ^ 2 + 1))`. -/
theorem fresMB_inner (k : ℕ) {w : ℂ} (hw : 0 < w.re) {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ in Ioi 0, fresMB_kernel k w (t, x) =
      ((2 / π : ℝ) : ℂ) ^ (w / 2) * Gamma (w / 2) / 2 *
        ((t : ℂ) ^ (2 * ((k : ℂ) / 2 + 1 / 4 - w / 4) - 1) / ((t : ℂ) ^ 2 + 1)) := by
  have hb : (0 : ℝ) < π * t / 2 := by positivity
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  simp only [fresMB_kernel]
  rw [integral_const_mul, DLMF.Bessel.kMel_integral_gauss hw hb]
  have e1 : (1 / ((π * t / 2 : ℝ) : ℂ)) = ((2 / π : ℝ) : ℂ) * ((t⁻¹ : ℝ) : ℂ) := by
    push_cast; field_simp
  rw [e1, mul_cpow_ofReal_nonneg (by positivity) (inv_nonneg.mpr ht.le), ofReal_inv,
    inv_cpow_ofReal_nonneg ht.le, ← cpow_neg]
  have e2 : (t : ℂ) ^ ((k : ℂ) - 1 / 2) * (t : ℂ) ^ (-(w / 2)) =
      (t : ℂ) ^ (2 * ((k : ℂ) / 2 + 1 / 4 - w / 4) - 1) := by
    rw [← cpow_add _ _ ht0]; ring_nf
  rw [← e2]
  ring

/-- Identity under the stated parameter and domain assumptions: `MellinConvergent (fun x : ℝ =>
fresMB_aux aux x) w ∧ mellin (fun x : ℝ => fresMB_aux aux x) w = 1 / (π * Real.sqrt 2) * (((2
/ π : ℝ) : ℂ) ^ (w / 2) * Gamma (w / 2) / 2 * (Gamma (((if aux then 1 else 0 : ℕ) : ℂ) / 2 + 1
/ 4 - w / 4) * Gamma (1 - (((if aux then 1 else 0 : ℕ) : ℂ) / 2 + 1 / 4 - w / 4)) / 2))`. -/
theorem fresMB_mellin (aux : Bool) {w : ℂ} (hw : 0 < w.re)
    (hw1 : w.re < 2 * ((if aux then 1 else 0 : ℕ) : ℝ) + 1) :
    MellinConvergent (fun x : ℝ => fresMB_aux aux x) w ∧
      mellin (fun x : ℝ => fresMB_aux aux x) w = 1 / (π * Real.sqrt 2) *
        (((2 / π : ℝ) : ℂ) ^ (w / 2) * Gamma (w / 2) / 2 *
          (Gamma (((if aux then 1 else 0 : ℕ) : ℂ) / 2 + 1 / 4 - w / 4) *
            Gamma (1 - (((if aux then 1 else 0 : ℕ) : ℂ) / 2 + 1 / 4 - w / 4)) / 2)) := by
  set k : ℕ := if aux then 1 else 0 with hkdef
  have hk : k ≤ 1 := by simp only [k]; split_ifs <;> norm_num
  have hint := fresMB_integrable_kernel hk hw hw1
  have hpt := fun x (hx : x ∈ Ioi (0 : ℝ)) => fresMB_pointwise aux w hx
  refine ⟨IntegrableOn.congr_fun ((hint.integral_prod_right).const_mul (1 / (π * Real.sqrt 2)))
    (fun x hx => (hpt x hx).symm) measurableSet_Ioi, ?_⟩
  rw [mellin, setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  have hswap := integral_integral_swap (f := fun t x => fresMB_kernel k w (t, x)) hint
  rw [← hswap, setIntegral_congr_fun measurableSet_Ioi fun t ht => fresMB_inner k hw ht,
    integral_const_mul]
  have hk' : (k : ℝ) ≤ 1 := by exact_mod_cast hk
  have ha0 : 0 < ((k : ℂ) / 2 + 1 / 4 - w / 4).re := by
    simp [div_ofNat_re]; linarith
  have ha1 : ((k : ℂ) / 2 + 1 / 4 - w / 4).re < 1 := by
    simp [div_ofNat_re]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  rw [fresMB_integral_cpow_div ha0 ha1]

/-- The Gamma product of the Mellin–Barnes integrands of DLMF 7.7.13–14. -/
def fresMB_G (b : ℝ) (s : ℂ) : ℂ :=
  Gamma s * Gamma (s + 1 / 2) * Gamma (s + b) * Gamma (1 - b - s)

/-- Continuity of the indicated function: `Continuous fun y : ℝ => fresMB_G b (c + y * I)`. -/
theorem fresMB_continuous_G {b c : ℝ} (hc : 0 < c) (hcb : 0 < c + b) (hcb1 : c < 1 - b) :
    Continuous fun y : ℝ => fresMB_G b (c + y * I) := by
  refine continuous_iff_continuousAt.mpr fun y => ?_
  unfold fresMB_G
  refine ((ContinuousAt.mul ?_ ?_).mul ?_).mul ?_
  · exact (DLMF.Gamma.continuousAt_Gamma_of_re_pos (by simp [hc])).comp (by fun_prop)
  · exact (DLMF.Gamma.continuousAt_Gamma_of_re_pos (by simp; linarith)).comp (by fun_prop)
  · exact (DLMF.Gamma.continuousAt_Gamma_of_re_pos (by simp; linarith)).comp (by fun_prop)
  · exact (DLMF.Gamma.continuousAt_Gamma_of_re_pos (by simp; linarith)).comp (by fun_prop)

/-- Estimate under the stated parameter and domain assumptions: `∃ C : ℝ, ∃ K : ℕ, ∀ y : ℝ,
‖fresMB_G b (c + y * I)‖ ≤ C * (1 + |y|) ^ K * Real.exp (-(2 * π * |y|))`. -/
theorem fresMB_bound_G {b c : ℝ} (hc : 0 < c) (hcb : 0 < c + b) (hcb1 : c < 1 - b) :
    ∃ C : ℝ, ∃ K : ℕ, ∀ y : ℝ,
      ‖fresMB_G b (c + y * I)‖ ≤ C * (1 + |y|) ^ K * Real.exp (-(2 * π * |y|)) := by
  obtain ⟨C₁, K₁, h₁⟩ := DLMF.Gamma.exists_norm_Gamma_shift_le hc 0
  obtain ⟨C₂, K₂, h₂⟩ := DLMF.Gamma.exists_norm_Gamma_shift_le (x := c + 1 / 2) (by linarith) 0
  obtain ⟨C₃, K₃, h₃⟩ := DLMF.Gamma.exists_norm_Gamma_shift_le (x := c + b) hcb 0
  obtain ⟨C₄, K₄, h₄⟩ := DLMF.Gamma.exists_norm_Gamma_shift_le (x := 1 - b - c) (by linarith) 0
  refine ⟨C₁ * C₂ * C₃ * C₄, K₁ + K₂ + K₃ + K₄, fun y => ?_⟩
  have e₁ : (c : ℂ) + y * I = ((c : ℝ) : ℂ) + I * (((0 : ℝ) : ℂ) + (y : ℂ)) := by push_cast; ring
  have e₂ : (c : ℂ) + y * I + 1 / 2 = ((c + 1 / 2 : ℝ) : ℂ) + I * (((0 : ℝ) : ℂ) + (y : ℂ)) := by
    push_cast; ring
  have e₃ : (c : ℂ) + y * I + b = ((c + b : ℝ) : ℂ) + I * (((0 : ℝ) : ℂ) + (y : ℂ)) := by
    push_cast; ring
  have e₄ : 1 - (b : ℂ) - (c + y * I) = ((1 - b - c : ℝ) : ℂ) + I * (((0 : ℝ) : ℂ) + ((-y : ℝ) : ℂ)) := by
    push_cast; ring
  have b₁ := h₁ y; have b₂ := h₂ y; have b₃ := h₃ y; have b₄ := h₄ (-y)
  rw [← e₁] at b₁; rw [← e₂] at b₂; rw [← e₃] at b₃; rw [← e₄, abs_neg] at b₄
  unfold fresMB_G
  rw [norm_mul, norm_mul, norm_mul]
  have hE : Real.exp (-(2 * π * |y|)) = Real.exp (-(π * |y|) / 2) * Real.exp (-(π * |y|) / 2) *
      Real.exp (-(π * |y|) / 2) * Real.exp (-(π * |y|) / 2) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
  rw [hE]
  have p₁ := (norm_nonneg _).trans b₁
  have p₂ := (norm_nonneg _).trans b₂
  have p₃ := (norm_nonneg _).trans b₃
  calc _ ≤ (C₁ * (1 + |y|) ^ K₁ * Real.exp (-(π * |y|) / 2)) *
        (C₂ * (1 + |y|) ^ K₂ * Real.exp (-(π * |y|) / 2)) *
        (C₃ * (1 + |y|) ^ K₃ * Real.exp (-(π * |y|) / 2)) *
        (C₄ * (1 + |y|) ^ K₄ * Real.exp (-(π * |y|) / 2)) := by
          gcongr
    _ = _ := by rw [pow_add, pow_add, pow_add]; ring

/-- Integrability of the indicated kernel: `Integrable fun y : ℝ => fresMB_G b (c + y * I)`. -/
theorem fresMB_integrable_G {b c : ℝ} (hc : 0 < c) (hcb : 0 < c + b) (hcb1 : c < 1 - b) :
    Integrable fun y : ℝ => fresMB_G b (c + y * I) := by
  obtain ⟨C, K, hC⟩ := fresMB_bound_G hc hcb hcb1
  refine ((DLMF.Gamma.integrable_one_add_abs_pow_mul_exp_neg (by positivity : 0 < 2 * π) K).const_mul
    C).mono' (fresMB_continuous_G hc hcb hcb1).aestronglyMeasurable
    (Eventually.of_forall fun y => (hC y).trans (le_of_eq (by ring)))

/-- The auxiliary function in the Mellin variable `X = (π x²/4)²`. -/
def fresMB_g (aux : Bool) : ℝ → ℂ :=
  fun X => fresMB_aux aux (((2 / Real.sqrt π * X ^ (1 / 4 : ℝ) : ℝ)) : ℂ)

/-- Identity under the stated parameter and domain assumptions: `((r : ℝ) : ℂ) ^ z = exp
(((Real.log r : ℝ) : ℂ) * z)`. -/
theorem fresMB_cpow_eq_exp {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ((r : ℝ) : ℂ) ^ z = exp (((Real.log r : ℝ) : ℂ) * z) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hr.ne'), ← ofReal_log hr.le]

/-- Identity under the stated parameter and domain assumptions: `(2 * π : ℂ) ^ (3 / 2 : ℂ) = 2 * π
* ((Real.sqrt 2 * Real.sqrt π : ℝ) : ℂ)`. -/
theorem fresMB_two_pi_cpow :
    (2 * π : ℂ) ^ (3 / 2 : ℂ) = 2 * π * ((Real.sqrt 2 * Real.sqrt π : ℝ) : ℂ) := by
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have e : (2 * π : ℂ) ^ (3 / 2 : ℂ) = (((2 * π) ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [ofReal_cpow h2π]; push_cast; rfl
  rw [e, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by positivity), Real.rpow_one,
    ← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num)]
  push_cast; ring

/-- Identity under the stated parameter and domain assumptions: `MellinConvergent (fresMB_g aux) s
∧ mellin (fresMB_g aux) s = ((2 * π : ℂ) ^ (3 / 2 : ℂ))⁻¹ * fresMB_G (3 / 4 - ((if aux then 1
else 0 : ℕ) : ℝ) / 2) s`. -/
theorem fresMB_mellin_g (aux : Bool) {s : ℂ} (hs : 0 < s.re)
    (hs1 : s.re < ((if aux then 1 else 0 : ℕ) : ℝ) / 2 + 1 / 4) :
    MellinConvergent (fresMB_g aux) s ∧
      mellin (fresMB_g aux) s = ((2 * π : ℂ) ^ (3 / 2 : ℂ))⁻¹ *
        fresMB_G (3 / 4 - ((if aux then 1 else 0 : ℕ) : ℝ) / 2) s := by
  set k : ℕ := if aux then 1 else 0 with hkdef
  set f : ℝ → ℂ := fun x => fresMB_aux aux x with hf
  set F : ℝ → ℂ := fun u => f (2 / Real.sqrt π * u) with hF
  have hgF : fresMB_g aux = fun X => F (X ^ (1 / 4 : ℝ)) := rfl
  set w : ℂ := s / ((1 / 4 : ℝ) : ℂ) with hw
  have hw4 : w = 4 * s := by rw [hw]; push_cast; field_simp
  have hwre : 0 < w.re := by rw [hw4]; simp; linarith
  have hwre1 : w.re < 2 * (k : ℝ) + 1 := by rw [hw4]; simp; linarith
  obtain ⟨hconv, hval⟩ := fresMB_mellin aux hwre hwre1
  have hsq : (0 : ℝ) < 2 / Real.sqrt π := by positivity
  refine ⟨?_, ?_⟩
  · rw [hgF, MellinConvergent.comp_rpow (by norm_num), ← hw]
    exact (MellinConvergent.comp_mul_left hsq).mpr hconv
  rw [hgF, mellin_comp_rpow, ← hw, hF, mellin_comp_mul_left _ _ hsq, hval, hw4]
  -- Gamma algebra
  have hdup := Complex.Gamma_mul_Gamma_add_half s
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsp : ((Real.sqrt π : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  have hP : (2 : ℂ) ^ (2 * s) ≠ 0 := by rw [cpow_def_of_ne_zero two_ne_zero]; exact exp_ne_zero _
  have hE : ((2 / Real.sqrt π : ℝ) : ℂ) ^ (-(4 * s)) * ((2 / π : ℝ) : ℂ) ^ (4 * s / 2) *
      (2 : ℂ) ^ (2 * s) = 1 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, fresMB_cpow_eq_exp hsq,
      fresMB_cpow_eq_exp (by positivity), fresMB_cpow_eq_exp two_pos, ← exp_add, ← exp_add,
      Real.log_div (by norm_num) (Real.sqrt_pos.mpr Real.pi_pos).ne',
      Real.log_div (by norm_num) Real.pi_ne_zero, Real.log_sqrt Real.pi_pos.le]
    rw [← exp_zero]; congr 1; push_cast; ring
  have h12 : (2 : ℂ) ^ (1 - 2 * s) = 2 / (2 : ℂ) ^ (2 * s) := by
    rw [cpow_sub _ _ two_ne_zero, cpow_one]
  have hsqrt : ((Real.sqrt π : ℝ) : ℂ) = ↑√π := rfl
  rw [h12] at hdup
  have ha1 : (1 : ℂ) - ((k : ℂ) / 2 + 1 / 4 - 4 * s / 4) = s + ((3 / 4 - (k : ℝ) / 2 : ℝ) : ℂ) := by
    push_cast; ring
  have ha2 : (k : ℂ) / 2 + 1 / 4 - 4 * s / 4 = 1 - ((3 / 4 - (k : ℝ) / 2 : ℝ) : ℂ) - s := by
    push_cast; ring
  rw [ha1, ha2, fresMB_two_pi_cpow, show 4 * s / 2 = 2 * s by ring]
  rw [show 4 * s / 2 = 2 * s by ring] at hE
  unfold fresMB_G
  simp only [smul_eq_mul, abs_div, abs_one, Nat.abs_ofNat, Complex.real_smul]
  generalize ((2 / Real.sqrt π : ℝ) : ℂ) ^ (-(4 * s)) = A at hE ⊢
  generalize ((2 / π : ℝ) : ℂ) ^ (2 * s) = B at hE ⊢
  generalize (2 : ℂ) ^ (2 * s) = P at hE hP hdup ⊢
  have hB : B = 1 / (A * P) := by
    have hA : A ≠ 0 := by rintro rfl; simp at hE
    field_simp; linear_combination hE
  subst hB
  have hA : A ≠ 0 := by rintro rfl; simp at hE
  rw [hdup]
  field_simp
  push_cast
  ring

/-- Differentiability of the indicated parameterized function: `Differentiable ℂ (fresMB_aux
aux)`. -/
lemma fresMB_differentiable_aux (aux : Bool) : Differentiable ℂ (fresMB_aux aux) := by
  unfold fresMB_aux; cases aux
  · exact fresnelAuxFComplex_entire
  · exact fresnelAuxGComplex_entire

/-- The Mellin–Barnes integrand of DLMF 7.7.13–14. -/
def fresMB_E (b c : ℝ) (z : ℂ) (y : ℝ) : ℂ :=
  exp (-((c : ℂ) + y * I) * (2 * log (π : ℂ) - log 16 + 4 * log z)) * fresMB_G b (c + y * I)

/-- Integrability of the indicated kernel: `Integrable (fresMB_E (3 / 4 - ((if aux then 1 else 0 :
ℕ) : ℝ) / 2) c x) ∧ ∫ y : ℝ, fresMB_E (3 / 4 - ((if aux then 1 else 0 : ℕ) : ℝ) / 2) c x y = 2
* π * (2 * π : ℂ) ^ (3 / 2 : ℂ) * fresMB_aux aux x`. -/
theorem fresMB_real (aux : Bool) {c : ℝ} (hc : 0 < c)
    (hc1 : c < ((if aux then 1 else 0 : ℕ) : ℝ) / 2 + 1 / 4) {x : ℝ} (hx : 0 < x) :
    Integrable (fresMB_E (3 / 4 - ((if aux then 1 else 0 : ℕ) : ℝ) / 2) c x) ∧
      ∫ y : ℝ, fresMB_E (3 / 4 - ((if aux then 1 else 0 : ℕ) : ℝ) / 2) c x y =
        2 * π * (2 * π : ℂ) ^ (3 / 2 : ℂ) * fresMB_aux aux x := by
  set k : ℕ := if aux then 1 else 0 with hkdef
  set b : ℝ := 3 / 4 - (k : ℝ) / 2 with hb
  have hk : (k : ℝ) ≤ 1 := by simp only [k]; split_ifs <;> norm_num
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hcb : 0 < c + b := by rw [hb]; linarith
  have hcb1 : c < 1 - b := by rw [hb]; linarith
  set X : ℝ := (π * x ^ 2 / 4) ^ 2 with hX
  have hX0 : 0 < X := by positivity
  -- the point `X` corresponds to `x`
  have hgX : fresMB_g aux X = fresMB_aux aux x := by
    unfold fresMB_g
    congr 2
    have h1 : X ^ (1 / 4 : ℝ) = Real.sqrt π * x / 2 := by
      rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
      rw [← Real.sqrt_eq_rpow, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4),
        Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq hx.le,
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h1]
    have : Real.sqrt π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    field_simp
  -- the power `X^{-s}`
  have hlog : Real.log X = 2 * Real.log π - Real.log 16 + 4 * Real.log x := by
    rw [hX, Real.log_pow, Real.log_div (by positivity) (by norm_num), Real.log_mul
      Real.pi_ne_zero (by positivity), Real.log_pow, show (16 : ℝ) = 4 ^ 2 by norm_num,
      Real.log_pow]
    push_cast; ring
  have hpow : ∀ y : ℝ, ((X : ℝ) : ℂ) ^ (-((c : ℂ) + y * I)) =
      exp (-((c : ℂ) + y * I) * (2 * log (π : ℂ) - log 16 + 4 * log (x : ℂ))) := by
    intro y
    rw [fresMB_cpow_eq_exp hX0, hlog, ← ofReal_log Real.pi_pos.le, ← ofReal_log hx.le,
      show (16 : ℂ) = ((16 : ℝ) : ℂ) by norm_num, ← ofReal_log (by norm_num)]
    congr 1; push_cast; ring
  -- Mellin inversion
  have hconv := (fresMB_mellin_g aux (s := (c : ℂ)) (by simpa using hc) (by have h := hc1; rw [hkdef] at h; simpa using h)).1
  have hmel : ∀ y : ℝ, mellin (fresMB_g aux) ((c : ℂ) + y * I) =
      ((2 * π : ℂ) ^ (3 / 2 : ℂ))⁻¹ * fresMB_G b (c + y * I) := fun y =>
    (fresMB_mellin_g aux (s := (c : ℂ) + y * I) (by simpa using hc) (by have h := hc1; rw [hkdef] at h; simpa using h)).2
  have hGint := fresMB_integrable_G hc hcb hcb1
  have hvert : VerticalIntegrable (mellin (fresMB_g aux)) c := by
    unfold VerticalIntegrable
    simp_rw [hmel]
    exact hGint.const_mul _
  have hcont : ContinuousAt (fresMB_g aux) X := by
    unfold fresMB_g
    refine (fresMB_differentiable_aux aux).continuous.continuousAt.comp ?_
    refine continuous_ofReal.continuousAt.comp ?_
    exact (Real.continuousAt_rpow_const _ _ (Or.inl hX0.ne')).const_mul _
  have hinv := mellinInv_mellin_eq c (fresMB_g aux) hX0 hconv hvert hcont
  rw [mellinInv, hgX] at hinv
  have hEeq : ∀ y : ℝ, (X : ℂ) ^ (-((c : ℂ) + y * I)) • mellin (fresMB_g aux) ((c : ℂ) + y * I) =
      ((2 * π : ℂ) ^ (3 / 2 : ℂ))⁻¹ * fresMB_E b c x y := by
    intro y; rw [hmel, smul_eq_mul, hpow, fresMB_E]; ring
  simp_rw [hEeq] at hinv
  rw [integral_const_mul] at hinv
  -- integrability
  have hEint : Integrable (fresMB_E b c x) := by
    have hc' : Continuous (fresMB_E b c x) := by
      unfold fresMB_E
      exact (by fun_prop : Continuous fun y : ℝ => exp (-((c : ℂ) + y * I) *
        (2 * log (π : ℂ) - log 16 + 4 * log (x : ℂ))))|>.mul (fresMB_continuous_G hc hcb hcb1)
    refine (hGint.norm.const_mul (X ^ (-c))).mono' hc'.aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [fresMB_E, ← hpow, norm_mul, norm_cpow_eq_rpow_re_of_pos hX0]
    simp
  refine ⟨hEint, ?_⟩
  have h2π : ((2 * π : ℂ) ^ (3 / 2 : ℂ)) ≠ 0 := by
    rw [fresMB_two_pi_cpow]
    have : (0 : ℝ) < Real.sqrt 2 * Real.sqrt π := by positivity
    have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero hp) (ofReal_ne_zero.mpr this.ne')
  rw [← hinv, real_smul]
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

/-- An absolutely integrable function has a convergent whole-line improper integral. -/
theorem fresMB_hasIntegralWholeLine {f : ℝ → ℂ} (hf : Integrable f) :
    HasIntegralWholeLine f (∫ y, f y) :=
  ⟨∫ y in Iic 0, f y, ∫ y in Ioi 0, f y,
    intervalIntegral_tendsto_integral_Iic 0 hf.integrableOn tendsto_id,
    intervalIntegral_tendsto_integral_Ioi 0 hf.integrableOn tendsto_id,
    intervalIntegral.integral_Iic_add_Ioi hf.integrableOn hf.integrableOn⟩

/-- The function `(fresMB_E b c z)` is continuous. -/
theorem fresMB_continuous_E {b c : ℝ} (hc : 0 < c) (hcb : 0 < c + b) (hcb1 : c < 1 - b) (z : ℂ) :
    Continuous (fresMB_E b c z) := by
  unfold fresMB_E
  exact (by fun_prop : Continuous fun y : ℝ => exp (-((c : ℂ) + y * I) *
    (2 * log (π : ℂ) - log 16 + 4 * log z))).mul (fresMB_continuous_G hc hcb hcb1)

/-- Identity under the stated parameter and domain assumptions: `(2 * log (π : ℂ) - log 16 + 4 *
log z).im = 4 * arg z`. -/
theorem fresMB_im_A (z : ℂ) : (2 * log (π : ℂ) - log 16 + 4 * log z).im = 4 * arg z := by
  have h1 : (log (π : ℂ)).im = 0 := by
    rw [log_im, arg_ofReal_of_nonneg Real.pi_pos.le]
  have h2 : (log (16 : ℂ)).im = 0 := by
    rw [log_im, show (16 : ℂ) = ((16 : ℝ) : ℂ) by norm_num, arg_ofReal_of_nonneg (by norm_num)]
  simp [h1, h2, log_im]

/-- Absolute integrability of the Mellin–Barnes integrand in the sector `|arg z| < π/2`. -/
theorem fresMB_integrable_E {b c : ℝ} (hc : 0 < c) (hcb : 0 < c + b) (hcb1 : c < 1 - b) {z : ℂ}
    (hz : |arg z| < π / 2) : Integrable (fresMB_E b c z) := by
  obtain ⟨C, K, hC⟩ := fresMB_bound_G hc hcb hcb1
  set A : ℂ := 2 * log (π : ℂ) - log 16 + 4 * log z with hA
  have hAim : |A.im| < 2 * π := by
    rw [hA, fresMB_im_A, abs_mul]; norm_num; linarith
  have hpos : 0 < 2 * π - |A.im| := by linarith
  refine (((DLMF.Gamma.integrable_one_add_abs_pow_mul_exp_neg hpos K).const_mul
    (C * Real.exp (-(c * A.re))))).mono' (fresMB_continuous_E hc hcb hcb1 z).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [fresMB_E, ← hA, norm_mul, norm_exp]
  have hre : (-((c : ℂ) + y * I) * A).re = -(c * A.re) + y * A.im := by
    simp [mul_re]
  rw [hre]
  have hy : y * A.im ≤ |A.im| * |y| := by
    rw [mul_comm]; exact (le_abs_self _).trans (by rw [abs_mul])
  have hC0 : 0 ≤ C := (norm_nonneg _).trans ((hC 0).trans (by simp))
  calc Real.exp (-(c * A.re) + y * A.im) * ‖fresMB_G b (c + y * I)‖
      ≤ (Real.exp (-(c * A.re)) * Real.exp (|A.im| * |y|)) *
          (C * (1 + |y|) ^ K * Real.exp (-(2 * π * |y|))) := by
        rw [← Real.exp_add]
        exact mul_le_mul (Real.exp_le_exp.mpr (by linarith)) (hC y) (norm_nonneg _)
          (Real.exp_pos _).le
    _ = C * Real.exp (-(c * A.re)) * ((1 + |y|) ^ K * Real.exp (-((2 * π - |A.im|) * |y|))) := by
        have : Real.exp (|A.im| * |y|) * Real.exp (-(2 * π * |y|)) =
            Real.exp (-((2 * π - |A.im|) * |y|)) := by rw [← Real.exp_add]; ring_nf
        calc _ = C * Real.exp (-(c * A.re)) * (1 + |y|) ^ K *
              (Real.exp (|A.im| * |y|) * Real.exp (-(2 * π * |y|))) := by ring
          _ = _ := by rw [this]; ring

/-- The rescaled Mellin–Barnes amplitude, in the form used by
`DLMF.Gamma.differentiableOn_integral_mul_cpow`. -/
def fresMB_B (b c : ℝ) (y : ℝ) : ℂ :=
  exp (-((c : ℂ) + (y / 4 : ℝ) * I) * (2 * log (π : ℂ) - log 16)) *
    fresMB_G b (c + (y / 4 : ℝ) * I)

/-- Identity under the stated parameter and domain assumptions: `fresMB_E b c z y = fresMB_B b c
(4 * y) * z⁻¹ ^ (((4 * c : ℝ) : ℂ) + I * ((4 * y : ℝ) : ℂ))`. -/
theorem fresMB_E_eq {b c : ℝ} {z : ℂ} (hz : 0 < z.re) (y : ℝ) :
    fresMB_E b c z y = fresMB_B b c (4 * y) * z⁻¹ ^ (((4 * c : ℝ) : ℂ) + I * ((4 * y : ℝ) : ℂ)) := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have harg : z.arg ≠ π := by
    intro h
    have := (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz))
    rw [h, abs_of_pos Real.pi_pos] at this; linarith [Real.pi_pos]
  rw [fresMB_E, fresMB_B, cpow_def_of_ne_zero (inv_ne_zero hz0), log_inv z harg,
    show (4 * y / 4 : ℝ) = y by ring]
  have he : exp (-((c : ℂ) + y * I) * (2 * log (π : ℂ) - log 16 + 4 * log z)) =
      exp (-((c : ℂ) + y * I) * (2 * log (π : ℂ) - log 16)) *
        exp (-log z * (((4 * c : ℝ) : ℂ) + I * ((4 * y : ℝ) : ℂ))) := by
    rw [← exp_add]; congr 1; push_cast; ring
  rw [he]; ring

/-- Identity under the stated parameter and domain assumptions: `∫ y, fresMB_E b c z y = (1 / 4 :
ℂ) * ∫ y, fresMB_B b c y * z⁻¹ ^ (((4 * c : ℝ) : ℂ) + I * (y : ℂ))`. -/
theorem fresMB_integral_E_eq {b c : ℝ} {z : ℂ} (hz : 0 < z.re) :
    ∫ y, fresMB_E b c z y =
      (1 / 4 : ℂ) * ∫ y, fresMB_B b c y * z⁻¹ ^ (((4 * c : ℝ) : ℂ) + I * (y : ℂ)) := by
  simp_rw [fresMB_E_eq hz]
  rw [Measure.integral_comp_mul_left (fun y : ℝ =>
    fresMB_B b c y * z⁻¹ ^ (((4 * c : ℝ) : ℂ) + I * (y : ℂ))) 4]
  rw [real_smul]; norm_num

/-- Estimate under the stated parameter and domain assumptions: `∃ C : ℝ, ∃ K : ℕ, ∀ y : ℝ,
‖fresMB_B b c y‖ ≤ C * (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2)`. -/
theorem fresMB_bound_B {b c : ℝ} (hc : 0 < c) (hcb : 0 < c + b) (hcb1 : c < 1 - b) :
    ∃ C : ℝ, ∃ K : ℕ, ∀ y : ℝ,
      ‖fresMB_B b c y‖ ≤ C * (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2) := by
  obtain ⟨C, K, hC⟩ := fresMB_bound_G hc hcb hcb1
  have hC0 : 0 ≤ C := (norm_nonneg _).trans ((hC 0).trans (by simp))
  set r : ℝ := 2 * Real.log π - Real.log 16
  have hA : (2 * log (π : ℂ) - log 16) = (r : ℂ) := by
    rw [← ofReal_log Real.pi_pos.le, show (16 : ℂ) = ((16 : ℝ) : ℂ) by norm_num,
      ← ofReal_log (by norm_num)]
    simp only [r]; push_cast; ring
  refine ⟨C * Real.exp (-(c * r)), K, fun y => ?_⟩
  rw [fresMB_B, hA, norm_mul, norm_exp]
  have hre : (-((c : ℂ) + ((y / 4 : ℝ) : ℂ) * I) * (r : ℂ)).re = -(c * r) := by
    simp [mul_re]
  rw [hre]
  have h1 := hC (y / 4)
  have hy : |y / 4| = |y| / 4 := by rw [abs_div]; norm_num
  rw [hy] at h1
  have hK : (1 + |y| / 4) ^ K ≤ (1 + |y|) ^ K :=
    pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg y]) K
  have he : Real.exp (-(2 * π * (|y| / 4))) = Real.exp (-(π * |y|) / 2) := by ring_nf
  rw [he] at h1
  calc Real.exp (-(c * r)) * ‖fresMB_G b (c + ((y / 4 : ℝ) : ℂ) * I)‖
      ≤ Real.exp (-(c * r)) * (C * (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2)) := by
        refine mul_le_mul_of_nonneg_left (h1.trans ?_) (Real.exp_pos _).le
        gcongr
    _ = _ := by ring

/-- The function `(fresMB_B b c)` is continuous. -/
theorem fresMB_continuous_B {b c : ℝ} (hc : 0 < c) (hcb : 0 < c + b) (hcb1 : c < 1 - b) :
    Continuous (fresMB_B b c) := by
  unfold fresMB_B
  refine Continuous.mul (by fun_prop) ?_
  exact (fresMB_continuous_G hc hcb hcb1).comp (continuous_id.div_const 4)

/-- The Mellin–Barnes integral for the auxiliary Fresnel functions (DLMF 7.7.13–14),
in the right half-plane. -/
theorem fresMB_complex (aux : Bool) {c : ℝ} (hc : 0 < c)
    (hc1 : c < ((if aux then 1 else 0 : ℕ) : ℝ) / 2 + 1 / 4) {z : ℂ} (hz : 0 < z.re) :
    ∫ y : ℝ, fresMB_E (3 / 4 - ((if aux then 1 else 0 : ℕ) : ℝ) / 2) c z y =
      2 * π * (2 * π : ℂ) ^ (3 / 2 : ℂ) * fresMB_aux aux z := by
  set k : ℕ := if aux then 1 else 0 with hkdef
  set b : ℝ := 3 / 4 - (k : ℝ) / 2 with hb
  have hk : (k : ℝ) ≤ 1 := by simp only [k]; split_ifs <;> norm_num
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hcb : 0 < c + b := by rw [hb]; linarith
  have hcb1 : c < 1 - b := by rw [hb]; linarith
  obtain ⟨C, K, hCK⟩ := fresMB_bound_B hc hcb hcb1
  have hG := DLMF.Gamma.differentiableOn_integral_mul_cpow (fresMB_continuous_B hc hcb hcb1)
    hCK (4 * c)
  set V : ℂ := 2 * π * (2 * π : ℂ) ^ (3 / 2 : ℂ)
  have hR : DifferentiableOn ℂ (fun w : ℂ => 4 * V * fresMB_aux aux w⁻¹) {w | 0 < w.re} := by
    intro w hw
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw
    exact (((fresMB_differentiable_aux aux).differentiableAt.comp w
      (differentiableAt_inv hw0)).const_mul _).differentiableWithinAt
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const continuous_re
  have hconv : Convex ℝ {w : ℂ | 0 < w.re} := convex_halfSpace_re_gt 0
  have h1 : (1 : ℂ) ∈ {w : ℂ | 0 < w.re} := by simp
  have hzi : 0 < z⁻¹.re := by
    rw [inv_re]; exact div_pos hz (normSq_pos.mpr (by rintro rfl; simp at hz))
  have key := AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq (z₀ := 1)
    (hG.analyticOnNhd hU) (hR.analyticOnNhd hU) hconv.isPreconnected h1 ?_ hzi
  · rw [fresMB_integral_E_eq hz]
    simp only at key
    rw [key, inv_inv]; ring
  have hev : ∀ᶠ x : ℝ in 𝓝[≠] 1,
      (∫ y : ℝ, fresMB_B b c y * (x : ℂ) ^ (((4 * c : ℝ) : ℂ) + I * y)) =
        4 * V * fresMB_aux aux (x : ℂ)⁻¹ := by
    filter_upwards [nhdsWithin_le_nhds (lt_mem_nhds one_pos)] with x hx
    have hxr : 0 < ((x : ℂ)⁻¹).re := by
      rw [← ofReal_inv, ofReal_re]; exact inv_pos.mpr hx
    have h := fresMB_integral_E_eq (b := b) (c := c) hxr
    rw [inv_inv] at h
    have hr := (fresMB_real aux hc hc1 (inv_pos.mpr hx)).2
    rw [← hkdef, ← hb, ofReal_inv, h] at hr
    show _ = 4 * (2 * π * (2 * π : ℂ) ^ (3 / 2 : ℂ)) * _
    linear_combination 4 * hr
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] 1) (𝓝[≠] 1) :=
    Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun x hx => by
      simpa using hx
  exact ht.frequently hev.frequently

end FresnelMellinBarnes

/-- Identity under the stated parameter and domain assumptions: `HasIntegralWholeLine (fun y : ℝ
=> let s : ℂ := c+y*I; exp (-s*(2*log (π : ℂ)-log 16+4*log z))*Gamma s*Gamma (s+1/2)*Gamma
(s+3/4)*Gamma (1/4-s)) (2*π*(2*π : ℂ)^(3/2 : ℂ)*fresnelAuxFComplex z)`. -/
@[dlmf 7.7.E13]
theorem fresnelAuxFComplex_mellinBarnes {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/2) {c : ℝ} (hc : 0 < c) (hc1 : c < 1/4) :
    HasIntegralWholeLine (fun y : ℝ => let s : ℂ := c+y*I; exp (-s*(2*log (π : ℂ)-log 16+4*log z))*Gamma s*Gamma (s+1/2)*Gamma (s+3/4)*Gamma (1/4-s)) (2*π*(2*π : ℂ)^(3/2 : ℂ)*fresnelAuxFComplex z) := by
  have hre : 0 < z.re := (abs_arg_lt_pi_div_two_iff.mp hz).resolve_right hz0
  have hv := fresMB_complex false hc (by norm_num; linarith) hre
  have e : (3 / 4 - ((if false = true then 1 else 0 : ℕ) : ℝ) / 2) = 3 / 4 := by norm_num
  rw [e] at hv
  have hI := fresMB_integrable_E (b := 3 / 4) hc (by linarith) (by linarith) hz
  have h := fresMB_hasIntegralWholeLine hI
  rw [hv] at h
  convert h using 2 with y
  simp only [fresMB_E, fresMB_G]
  push_cast
  ring_nf
  simp [fresMB_aux]

/-- Identity under the stated parameter and domain assumptions: `HasIntegralWholeLine (fun y : ℝ
=> let s : ℂ := c+y*I; exp (-s*(2*log (π : ℂ)-log 16+4*log z))*Gamma s*Gamma (s+1/2)*Gamma
(s+1/4)*Gamma (3/4-s)) (2*π*(2*π : ℂ)^(3/2 : ℂ)*fresnelAuxGComplex z)`. -/
@[dlmf 7.7.E14]
theorem fresnelAuxGComplex_mellinBarnes {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/2) {c : ℝ} (hc : 0 < c) (hc1 : c < 3/4) :
    HasIntegralWholeLine (fun y : ℝ => let s : ℂ := c+y*I; exp (-s*(2*log (π : ℂ)-log 16+4*log z))*Gamma s*Gamma (s+1/2)*Gamma (s+1/4)*Gamma (3/4-s)) (2*π*(2*π : ℂ)^(3/2 : ℂ)*fresnelAuxGComplex z) := by
  have hre : 0 < z.re := (abs_arg_lt_pi_div_two_iff.mp hz).resolve_right hz0
  have hv := fresMB_complex true hc (by norm_num; linarith) hre
  have e : (3 / 4 - ((if true = true then 1 else 0 : ℕ) : ℝ) / 2) = 1 / 4 := by norm_num
  rw [e] at hv
  have hI := fresMB_integrable_E (b := 1 / 4) hc (by linarith) (by linarith) hz
  have h := fresMB_hasIntegralWholeLine hI
  rw [hv] at h
  convert h using 2 with y
  simp only [fresMB_E, fresMB_G]
  push_cast
  ring_nf
  simp [fresMB_aux]

/-- The half-line Gaussian Laplace transform on the boundary `Re b = 0`, obtained from the
case `Re b > 0` by dominated convergence. -/
theorem laplace_gaussian_boundary {a b0 : ℂ} (ha : 0 < a.re) (hb0re : b0.re = 0) (hb0ne : b0 ≠ 0)
    (hslit : b0 ∈ slitPlane) (hslit2 : (π:ℂ)/b0 ∈ slitPlane) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*exp (-(b0*(t:ℂ)^2))) =
      (π/b0)^(1/2 : ℂ)/2*exp ((a/2)^2/b0)*erfc ((a/2)/b0^(1/2 : ℂ)) := by
  set R : ℂ → ℂ := fun b => (π/b)^(1/2 : ℂ)/2*exp (((a/2)^2-b*0)/b)*
    erfc (b^(1/2 : ℂ)*((0:ℝ):ℂ)+(a/2)/b^(1/2 : ℂ)) with hR
  set A : ℝ → ℂ := fun δ => (δ:ℂ)+b0 with hA
  have hT : ∀ δ : ℝ, 0 < δ →
      (∫ t : ℝ in Ioi 0, exp (-(A δ*(t:ℂ)^2+2*(a/2)*t+0))) = R (A δ) := by
    intro δ hδ
    exact gaussian_quadratic_tail (by simp [hA, hb0re, hδ]) (a/2) 0 0
  have hDCT : Tendsto (fun δ : ℝ => ∫ t : ℝ in Ioi 0, exp (-(A δ*(t:ℂ)^2+2*(a/2)*t+0)))
      (𝓝[>] 0) (𝓝 (∫ t : ℝ in Ioi 0, exp (-a*t)*exp (-(b0*(t:ℂ)^2)))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => Real.exp (-a.re*t)) ?_ ?_
      (exp_neg_integrableOn_Ioi 0 ha) ?_
    · exact Eventually.of_forall fun δ =>
        (by fun_prop : Continuous fun t : ℝ => exp (-(A δ*(t:ℂ)^2+2*(a/2)*t+0))).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hδ : (0:ℝ) < δ := hδ
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
      have ht : (0:ℝ) < t := ht
      rw [Complex.norm_exp, Real.exp_le_exp]
      have : (-(A δ*(t:ℂ)^2+2*(a/2)*t+0)).re = -(δ*t^2) - a.re*t := by
        simp [hA, hb0re, ← ofReal_pow]; ring
      rw [this]
      nlinarith [mul_pos hδ (pow_pos ht 2)]
    · refine Eventually.of_forall fun t => ?_
      have hc : Continuous fun δ : ℝ => exp (-(A δ*(t:ℂ)^2+2*(a/2)*t+0)) := by fun_prop
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      convert this using 2
      rw [← Complex.exp_add]
      congr 1
      simp only [hA]
      push_cast
      ring
  have hs0 : b0^(1/2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; simp [hb0ne]
  have hRc : ContinuousAt R b0 := by
    have h1 : ContinuousAt (fun b : ℂ => (π/b)^(1/2 : ℂ)) b0 :=
      (continuousAt_cpow_const hslit2).comp (continuousAt_const.div continuousAt_id hb0ne)
    have h2 : ContinuousAt (fun b : ℂ => b^(1/2 : ℂ)) b0 := continuousAt_cpow_const hslit
    have he : Continuous erfc := by
      have : Continuous erf := differentiable_erf_complex.continuous
      unfold erfc; fun_prop
    simp only [hR]
    refine ((h1.div_const 2).mul ?_).mul ?_
    · exact Complex.continuous_exp.continuousAt.comp
        ((continuousAt_const.sub (continuousAt_id.mul continuousAt_const)).div continuousAt_id hb0ne)
    · exact he.continuousAt.comp ((h2.mul continuousAt_const).add (continuousAt_const.div h2 hs0))
  have hAt : Tendsto A (𝓝[>] 0) (𝓝 b0) := by
    have : Tendsto A (𝓝 0) (𝓝 (((0:ℝ):ℂ)+b0)) := ((continuous_ofReal.add continuous_const).tendsto 0)
    simpa using this.mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto (fun δ : ℝ => ∫ t : ℝ in Ioi 0, exp (-(A δ*(t:ℂ)^2+2*(a/2)*t+0)))
      (𝓝[>] 0) (𝓝 (R b0)) := by
    refine (hRc.tendsto.comp hAt).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (hT δ hδ).symm
  rw [tendsto_nhds_unique hDCT hlim2]
  simp [hR]

/-- Laplace transform of `exp(± i t²)`: for `ε = ±1` and `Re a > 0`,
`∫₀^∞ e^{-at} e^{iεt²} dt = √(π/2) (f(z) + iε g(z))` with `z = a/√(2π)`. -/
theorem laplace_exp_I_sq {a : ℂ} (ha : 0 < a.re) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*exp (ε*I*(t:ℂ)^2)) =
      Real.sqrt (π/2)*(fresnelAuxFComplex (a/Real.sqrt (2*π)) +
        ε*I*fresnelAuxGComplex (a/Real.sqrt (2*π))) := by
  have hneg : (-ε = 1 ∨ -ε = -1) := by rcases hε with rfl | rfl <;> norm_num
  have hF := fresnelAux_signed_erfc (a/Real.sqrt (2*π)) hneg
  have hζ : fresnelZetaComplex (-ε) (a/Real.sqrt (2*π)) =
      Real.sqrt π/2*(1+ε*I)*(a/Real.sqrt (2*π)) := by
    unfold fresnelZetaComplex; push_cast; ring
  rw [hζ] at hF
  push_cast at hF
  rw [show -(ε:ℂ)*I = -((ε:ℂ)*I) by ring] at hF
  have hσre : ((ε:ℂ)*I).re = 0 := by simp
  have hσim : ((ε:ℂ)*I).im ≠ 0 := by simp; rcases hε with rfl | rfl <;> norm_num
  have hσ2 : ((ε:ℂ)*I)^2 = -1 := by
    rw [mul_pow, I_sq]; rcases hε with rfl | rfl <;> norm_num
  have heI : ∀ t : ℝ, exp (ε*I*(t:ℂ)^2) = exp (-(-((ε:ℂ)*I)*(t:ℂ)^2)) := fun t => by ring_nf
  simp_rw [heI]
  generalize (ε:ℂ)*I = σ at hσre hσim hσ2 hF ⊢
  have hb0ne : -σ ≠ 0 := fun h => hσim (by simpa using congrArg Complex.im h)
  have hslit : -σ ∈ slitPlane := by
    rw [mem_slitPlane_iff]; right; simpa using hσim
  have hpσ : (π:ℂ)/(-σ) = π*σ := by
    have : σ ≠ 0 := fun h => hb0ne (by simp [h])
    rw [eq_comm, eq_div_iff hb0ne]; linear_combination -(π:ℂ)*hσ2
  have hslit2 : (π:ℂ)/(-σ) ∈ slitPlane := by
    rw [hpσ, mem_slitPlane_iff]; right
    simp [Real.pi_ne_zero, hσim, hσre]
  rw [laplace_gaussian_boundary ha (by simpa using hσre) hb0ne hslit hslit2]
  have hsq2 : ((Real.sqrt 2:ℝ):ℂ)^2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hsqp : ((Real.sqrt π:ℝ):ℂ)^2 = π := by exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have hs2 : (Real.sqrt 2:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr two_pos).ne'
  have hsp : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hsb : (-σ)^(1/2 : ℂ) = (1-σ)/Real.sqrt 2 := by
    rw [show -σ = ((1-σ)/Real.sqrt 2)^2 by
      rw [div_pow, hsq2]; linear_combination (-1/2:ℂ)*hσ2]
    refine sq_cpow_half ?_
    rw [div_ofReal_re]; refine div_pos ?_ (Real.sqrt_pos.mpr two_pos); simp [hσre]
  have hpb : ((π:ℂ)/(-σ))^(1/2 : ℂ) = Real.sqrt π*(1+σ)/Real.sqrt 2 := by
    rw [hpσ, show (π:ℂ)*σ = (Real.sqrt π*(1+σ)/Real.sqrt 2)^2 by
      rw [div_pow, mul_pow, hsq2, hsqp]; linear_combination (-(π:ℂ)/2)*hσ2]
    refine sq_cpow_half ?_
    rw [div_ofReal_re]; refine div_pos ?_ (Real.sqrt_pos.mpr two_pos)
    rw [re_ofReal_mul]; simp [hσre]; exact Real.pi_pos
  have h2p : ((Real.sqrt (2*π):ℝ):ℂ) = Real.sqrt 2*Real.sqrt π := by
    rw [Real.sqrt_mul (by norm_num)]; push_cast; ring
  have h1σ : (1:ℂ)-σ ≠ 0 := by
    intro h; apply hσim; have := congrArg Complex.im h; simp at this; simp [← this]
  set ζ := Real.sqrt π/2*(1+σ)*(a/Real.sqrt (2*π))
  have hz : (a/2)/(-σ)^(1/2 : ℂ) = ζ := by
    rw [hsb]; simp only [ζ]; rw [h2p]
    field_simp
    linear_combination a*hσ2 + a*hsq2
  have hz2 : (a/2)^2/(-σ) = ζ^2 := by
    rw [← hz, div_pow (a/2), cpow_half_sq hb0ne]
  rw [hpb, hz, hz2]
  set E := exp (ζ^2)*erfc ζ
  set f := fresnelAuxFComplex (a/Real.sqrt (2*π))
  set g := fresnelAuxGComplex (a/Real.sqrt (2*π))
  have hE : E = (1+σ)*(g-σ*f) := by
    linear_combination (-(1+σ))*hF + E/2*hσ2
  have hsq : (Real.sqrt (π/2):ℂ) = Real.sqrt π/Real.sqrt 2 := by
    rw [Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 2)]; push_cast; ring
  rw [hsq, mul_assoc _ (exp _), show exp (ζ^2)*erfc ζ = E from rfl]
  linear_combination (Real.sqrt π/Real.sqrt 2*(1+σ)/2)*hE +
    (Real.sqrt π/Real.sqrt 2*(-f+(g-σ*f)/2))*hσ2

/-- Integrability of `e^{-at} e^{iεt²}` on `(0, ∞)`. -/
theorem integrableOn_exp_mul_exp_I_sq {a : ℂ} (ha : 0 < a.re) (ε : ℝ) :
    IntegrableOn (fun t : ℝ => exp (-a*t)*exp (ε*I*(t:ℂ)^2)) (Ioi 0) := by
  refine (exp_neg_integrableOn_Ioi 0 ha).mono' (by fun_prop : Continuous fun t : ℝ =>
    exp (-a*t)*exp (ε*I*(t:ℂ)^2)).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
  have h1 : (ε*I*(t:ℂ)^2).re = 0 := by simp [← ofReal_pow]
  rw [h1]; simp

/-- Identity under the stated parameter and domain assumptions: `(∫ t : ℝ in Ioi 0, exp (-a*t)*cos
((t : ℂ)^2))=Real.sqrt (π/2)*fresnelAuxFComplex (a/Real.sqrt (2*π))`. -/
@[dlmf 7.7.E15]
theorem fresnelAuxFComplex_laplace_square {a : ℂ} (ha : 0 < a.re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*cos ((t : ℂ)^2))=Real.sqrt (π/2)*fresnelAuxFComplex (a/Real.sqrt (2*π)) := by
  have h1 := laplace_exp_I_sq ha (Or.inl rfl)
  have h2 := laplace_exp_I_sq ha (Or.inr rfl)
  have e : (fun t : ℝ => exp (-a*t)*cos ((t : ℂ)^2)) = fun t : ℝ =>
      (exp (-a*t)*exp (((1:ℝ):ℂ)*I*(t:ℂ)^2) + exp (-a*t)*exp (((-1:ℝ):ℂ)*I*(t:ℂ)^2))/2 := by
    funext t; rw [Complex.cos]; push_cast; ring_nf
  rw [e, integral_div, integral_add (integrableOn_exp_mul_exp_I_sq ha 1)
    (integrableOn_exp_mul_exp_I_sq ha (-1)), h1, h2]
  push_cast; ring

/-- Identity under the stated parameter and domain assumptions: `(∫ t : ℝ in Ioi 0, exp (-a*t)*sin
((t : ℂ)^2))=Real.sqrt (π/2)*fresnelAuxGComplex (a/Real.sqrt (2*π))`. -/
@[dlmf 7.7.E16]
theorem fresnelAuxGComplex_laplace_square {a : ℂ} (ha : 0 < a.re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*sin ((t : ℂ)^2))=Real.sqrt (π/2)*fresnelAuxGComplex (a/Real.sqrt (2*π)) := by
  have h1 := laplace_exp_I_sq ha (Or.inl rfl)
  have h2 := laplace_exp_I_sq ha (Or.inr rfl)
  have e : (fun t : ℝ => exp (-a*t)*sin ((t : ℂ)^2)) = fun t : ℝ =>
      (exp (-a*t)*exp (((-1:ℝ):ℂ)*I*(t:ℂ)^2) - exp (-a*t)*exp (((1:ℝ):ℂ)*I*(t:ℂ)^2))*I/2 := by
    funext t; rw [Complex.sin]; push_cast; ring_nf
  rw [e, integral_div, integral_mul_const, integral_sub (integrableOn_exp_mul_exp_I_sq ha (-1))
    (integrableOn_exp_mul_exp_I_sq ha 1), h1, h2]
  push_cast; ring_nf; rw [I_sq]; ring

/-- Identity under the stated parameter and domain assumptions: `(∫ t : ℝ in Ioi 0, exp
(2*I*a*t)*erfc (b*t))=if a=0 then 1/(b*Real.sqrt π) else dawsonF (a/b)/(a*Real.sqrt
π)+I/(2*a)*(1-exp (-(a/b)^2))`. -/
@[dlmf 7.14.E1]
theorem erfc_fourier_halfLine {b : ℂ} (hb0 : b ≠ 0) (hb : |arg b| < π/4) (a : ℂ) :
    (∫ t : ℝ in Ioi 0, exp (2*I*a*t)*erfc (b*t))=if a=0 then 1/(b*Real.sqrt π) else dawsonF (a/b)/(a*Real.sqrt π)+I/(2*a)*(1-exp (-(a/b)^2)) := by
  have hbr : 0 < b.re := re_pos_of_abs_arg_lt hb0 (by linarith [Real.pi_pos])
  have hb2 := re_sq_pos_of_abs_arg_lt hb0 hb
  set β := (b^2).re
  have hp0 : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hsq : (b^2)^(1/2 : ℂ) = b := sq_cpow_half hbr
  obtain ⟨C, hC0, hC⟩ := exists_norm_erfc_mul_le hb0 hb
  -- the Gaussian majorant
  have hnexp (t : ℝ) : ‖exp (2*I*a*t)‖ = Real.exp (-2*a.im*t) := by
    rw [Complex.norm_exp]; congr 1; simp
  have hmaj : ∀ t : ℝ, 0 < t → ‖exp (2*I*a*t)*erfc (b*t)‖ ≤ C*Real.exp (-β*t^2+(-2*a.im)*t) := by
    intro t ht
    rw [norm_mul, hnexp, show -β*t^2+(-2*a.im)*t = -2*a.im*t + -β*t^2 by ring, Real.exp_add]
    have := hC t ht
    have : 0 ≤ Real.exp (-2*a.im*t) := (Real.exp_pos _).le
    nlinarith
  have hgint : Integrable (fun t : ℝ => C*Real.exp (-β*t^2+(-2*a.im)*t)) := by
    have := (integrable_cexp_quadratic (b := (β:ℂ)) (by simpa using hb2) ((-2*a.im:ℝ):ℂ) 0).norm
    refine (this.const_mul C).congr (ae_of_all _ fun t => ?_)
    simp only
    rw [Complex.norm_exp]
    congr 2; simp [← ofReal_pow]
  have hmajlim : Tendsto (fun t : ℝ => C*Real.exp (-β*t^2+(-2*a.im)*t)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => t*(β*t+2*a.im)) atTop atTop :=
      tendsto_id.atTop_mul_atTop₀ (tendsto_atTop_add_const_right _ _
        (tendsto_id.const_mul_atTop' hb2))
    have h2 := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
    have h3 := h2.const_mul C
    rw [mul_zero] at h3
    refine h3.congr fun t => ?_
    simp only [Function.comp_apply]; congr 2; ring
  have hint : IntegrableOn (fun t : ℝ => exp (2*I*a*t)*erfc (b*t)) (Ioi 0) := by
    refine Integrable.mono' hgint.integrableOn ?_ ?_
    · exact (Continuous.aestronglyMeasurable (by
        have : Continuous erfc := by unfold erfc; have := differentiable_erf_complex.continuous; fun_prop
        fun_prop))
    · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => hmaj t ht)
  have hPlim : Tendsto (fun t : ℝ => exp (2*I*a*t)*erfc (b*t)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hmajlim
    filter_upwards [eventually_gt_atTop 0] with t ht using hmaj t ht
  have herfc (t : ℝ) : HasDerivAt (fun t : ℝ => erfc (b*(t:ℂ))) (-(2/Real.sqrt π*exp (-(b*t)^2)*b)) t := by
    have := (hasDerivAt_erf_complex (b*t)).comp t (((hasDerivAt_id (t:ℂ)).const_mul b).comp_ofReal)
    simpa [erfc, Function.comp_def] using this.const_sub 1
  split_ifs with ha
  · subst ha
    simp only [mul_zero, zero_mul, Complex.exp_zero, one_mul]
    set F : ℝ → ℂ := fun t => t*erfc (b*t) - exp (-(b^2)*t^2)/(b*Real.sqrt π) with hF
    have hd (t : ℝ) : HasDerivAt F (erfc (b*t)) t := by
      have h1 : HasDerivAt (fun t : ℝ => exp (-(b^2)*(t:ℂ)^2)) (exp (-(b^2)*t^2)*(-(b^2)*(2*t))) t := by
        have := (((hasDerivAt_id (t:ℂ)).pow 2).const_mul (-(b^2))).cexp
        simpa using this.comp_ofReal
      have := ((hasDerivAt_id t).ofReal_comp.mul (herfc t)).sub (h1.div_const (b*Real.sqrt π))
      convert this using 1
      · funext s; simp [F]
      · have e : exp (-(b*t)^2) = exp (-(b^2)*t^2) := by congr 1; ring
        rw [e]; simp; field_simp; ring
    have hlim : Tendsto F atTop (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ => (t:ℂ)*erfc (b*t)) atTop (𝓝 0) := by
        have hs0 : 0 < Real.sqrt (π*β) := Real.sqrt_pos.mpr (by positivity)
        have hm : Tendsto (fun t : ℝ => Real.exp (-β*t^2)/Real.sqrt (π*β)) atTop (𝓝 0) := by
          have := (Real.tendsto_exp_atBot.comp ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg
            (by linarith : -β < 0))).div_const (Real.sqrt (π*β))
          simpa using this
        refine squeeze_zero_norm' ?_ hm
        filter_upwards [eventually_gt_atTop 0] with t ht
        obtain ⟨h1, h2⟩ := re_mul_ofReal_pos_and_sq hb0 hb ht
        have hre : ((b*t)^2).re = β*t^2 := by rw [mul_pow, ← ofReal_pow, re_mul_ofReal]
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
        have hb := norm_erfc_le h1 h2
        rw [Complex.norm_exp, neg_re, hre, show π*(β*t^2) = (π*β)*t^2 by ring,
          Real.sqrt_mul' _ (sq_nonneg t), Real.sqrt_sq ht.le] at hb
        calc t*‖erfc (b*t)‖ ≤ t*(Real.exp (-(β*t^2))/(Real.sqrt (π*β)*t)) :=
              mul_le_mul_of_nonneg_left hb ht.le
          _ = _ := by rw [show -(β*t^2) = -β*t^2 by ring]; field_simp
      have h2 : Tendsto (fun t : ℝ => exp (-(b^2)*(t:ℂ)^2)) atTop (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have : Tendsto (fun t : ℝ => Real.exp (-β*t^2)) atTop (𝓝 0) :=
          Real.tendsto_exp_atBot.comp ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by linarith))
        refine this.congr fun t => ?_
        rw [Complex.norm_exp]; congr 1
        rw [← ofReal_pow, re_mul_ofReal, neg_re]
      simpa [hF] using h1.sub (h2.div_const (b*Real.sqrt π))
    have hint0 : IntegrableOn (fun t : ℝ => erfc (b*t)) (Ioi 0) := by
      refine hint.congr_fun (fun t _ => by simp) measurableSet_Ioi
    rw [integral_Ioi_of_hasDerivAt_of_tendsto (hd 0).continuousAt.continuousWithinAt
      (fun t _ => hd t) hint0 hlim]
    simp [hF]
  · have hQ := hasDerivAt_gaussianQuadratic hb2 (-I*a) 0
    simp only [hsq] at hQ
    set Q : ℝ → ℂ := fun t => -(Real.sqrt π/(2*b))*exp (((-I*a)^2-b^2*0)/b^2)*erfc (b*t+(-I*a)/b)
    set F : ℝ → ℂ := fun t => exp (2*I*a*t)*erfc (b*t)/(2*I*a) + b/(I*a*Real.sqrt π)*Q t with hF
    have hd (t : ℝ) : HasDerivAt F (exp (2*I*a*t)*erfc (b*t)) t := by
      have h1 : HasDerivAt (fun t : ℝ => exp (2*I*a*(t:ℂ))) (exp (2*I*a*t)*(2*I*a)) t := by
        have := ((hasDerivAt_id (t:ℂ)).const_mul (2*I*a)).cexp
        simpa using this.comp_ofReal
      have := ((h1.mul (herfc t)).div_const (2*I*a)).add ((hQ t).const_mul (b/(I*a*Real.sqrt π)))
      convert this using 1
      have e : exp (-(b^2*(t:ℂ)^2+2*(-I*a)*t+0)) = exp (2*I*a*t)*exp (-(b*t)^2) := by
        rw [← Complex.exp_add]; congr 1; ring
      rw [e]; field_simp; ring
    have hlim : Tendsto F atTop (𝓝 0) := by
      have hQ0 : Tendsto Q atTop (𝓝 0) := by
        have := (tendsto_erfc_mul_add_atTop hbr hb2 ((-I*a)/b)).const_mul
          (-(Real.sqrt π/(2*b))*exp (((-I*a)^2-b^2*0)/b^2))
        simpa [Q] using this
      have := (hPlim.div_const (2*I*a)).add (hQ0.const_mul (b/(I*a*Real.sqrt π)))
      simpa [hF] using this
    rw [integral_Ioi_of_hasDerivAt_of_tendsto (hd 0).continuousAt.continuousWithinAt
      (fun t _ => hd t) hint hlim]
    simp only [hF, Q, ofReal_zero, mul_zero, Complex.exp_zero, zero_add]
    set w := a/b
    have hD := (dawsonF_faddeeva w).2
    have hk : ((-I*a)^2-0)/b^2 = -w^2 := by
      simp only [w]; field_simp; ring_nf; rw [I_sq]; ring
    have hm : -I*a/b = -(I*w) := by simp only [w]; ring
    rw [hk, hm, erfc_negative, hD]
    have hb' : b ≠ 0 := hb0
    simp only [erfc, erf_zero, sub_zero]
    field_simp
    ring_nf
    rw [I_sq]
    ring

/-- Identity under the stated parameter and domain assumptions: `(∫ t : ℝ in Ioi 0, exp (-a*t)*erf
(b*t))=exp (a^2/(4*b^2))/a*erfc (a/(2*b))`. -/
@[dlmf 7.14.E2]
theorem erf_laplace {a b : ℂ} (ha : 0 < a.re) (hb0 : b ≠ 0) (hb : |arg b| < π/4) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*erf (b*t))=exp (a^2/(4*b^2))/a*erfc (a/(2*b)) := by
  have hbr : 0 < b.re := re_pos_of_abs_arg_lt hb0 (by linarith [Real.pi_pos])
  have hb2 := re_sq_pos_of_abs_arg_lt hb0 hb
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hp0 : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hsq : (b^2)^(1/2 : ℂ) = b := sq_cpow_half hbr
  have hQ := hasDerivAt_gaussianQuadratic hb2 (a/2) 0
  simp only [hsq] at hQ
  set Q : ℝ → ℂ := fun t => -(Real.sqrt π/(2*b))*exp (((a/2)^2-b^2*0)/b^2)*erfc (b*t+a/2/b)
  set F : ℝ → ℂ := fun t => -(exp (-a*t)*erf (b*t))/a + 2*b/(a*Real.sqrt π)*Q t with hF
  have hd (t : ℝ) : HasDerivAt F (exp (-a*t)*erf (b*t)) t := by
    have h1 : HasDerivAt (fun t : ℝ => exp (-a*(t:ℂ))) (exp (-a*t)*(-a)) t := by
      have := ((hasDerivAt_id (t:ℂ)).const_mul (-a)).cexp
      simpa using this.comp_ofReal
    have h2 : HasDerivAt (fun t : ℝ => erf (b*(t:ℂ))) (2/Real.sqrt π*exp (-(b*t)^2)*b) t := by
      have := (hasDerivAt_erf_complex (b*t)).comp t
        (((hasDerivAt_id (t:ℂ)).const_mul b).comp_ofReal)
      simpa [Function.comp_def] using this
    have := ((h1.mul h2).neg.div_const a).add ((hQ t).const_mul (2*b/(a*Real.sqrt π)))
    convert this using 1
    have e : exp (-(b^2*(t:ℂ)^2+2*(a/2)*t+0)) = exp (-a*t)*exp (-(b*t)^2) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [e]; field_simp; ring
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hQ0 : Tendsto Q atTop (𝓝 0) := by
      have := (tendsto_erfc_mul_add_atTop hbr hb2 (a/2/b)).const_mul
        (-(Real.sqrt π/(2*b))*exp (((a/2)^2-b^2*0)/b^2))
      simpa [Q] using this
    have hP : Tendsto (fun t : ℝ => exp (-a*t)*erf (b*t)) atTop (𝓝 0) := by
      have hev : ∀ᶠ t : ℝ in atTop, ‖exp (-a*t)*erf (b*t)‖ ≤ 2*Real.exp (-a.re*t) := by
        filter_upwards [eventually_gt_atTop 0] with t ht
        obtain ⟨h1, h2⟩ := re_mul_ofReal_pos_and_sq hb0 hb ht
        rw [norm_mul, Complex.norm_exp]
        have : (-a*(t:ℂ)).re = -a.re*t := by simp
        rw [this, mul_comm]
        exact mul_le_mul_of_nonneg_right (norm_erf_le_two h1 h2) (Real.exp_pos _).le
      refine squeeze_zero_norm' hev ?_
      have : Tendsto (fun t : ℝ => -a.re*t) atTop atBot :=
        tendsto_id.const_mul_atTop_of_neg (by linarith)
      simpa using (Real.tendsto_exp_atBot.comp this).const_mul 2
    have := (hP.neg.div_const a).add (hQ0.const_mul (2*b/(a*Real.sqrt π)))
    simpa [hF] using this
  have hint : IntegrableOn (fun t : ℝ => exp (-a*t)*erf (b*t)) (Ioi 0) := by
    have hg : IntegrableOn (fun t : ℝ => 2*Real.exp (-a.re*t)) (Ioi 0) :=
      ((exp_neg_integrableOn_Ioi 0 ha).const_mul 2 :)
    refine Integrable.mono' hg ?_ ?_
    · exact (Continuous.aestronglyMeasurable (by
        have := differentiable_erf_complex.continuous; fun_prop))
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
      obtain ⟨h1, h2⟩ := re_mul_ofReal_pos_and_sq hb0 hb ht
      rw [norm_mul, Complex.norm_exp]
      have : (-a*(t:ℂ)).re = -a.re*t := by simp
      rw [this, mul_comm]
      exact mul_le_mul_of_nonneg_right (norm_erf_le_two h1 h2) (Real.exp_pos _).le
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (hd 0).continuousAt.continuousWithinAt
    (fun t _ => hd t) hint hlim]
  simp only [hF, Q, ofReal_zero, mul_zero, erf_zero, zero_add]
  have hb0' : b^2 ≠ 0 := pow_ne_zero 2 hb0
  rw [show ((a/2)^2-0)/b^2 = a^2/(4*b^2) by field_simp; ring, show a/2/b = a/(2*b) by ring]
  field_simp
  ring

/-- `(b/c)^{1/2} = b^{1/2}/c^{1/2}` in the right half-plane. -/
theorem div_cpow_half {b c : ℂ} (hb : 0 < b.re) (hc : 0 < c.re) :
    (b/c)^(1/2 : ℂ) = b^(1/2 : ℂ)/c^(1/2 : ℂ) := by
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  set p := b^(1/2 : ℂ); set q := c^(1/2 : ℂ)
  have hp2 : p^2 = b := cpow_half_sq hb0
  have hq2 : q^2 = c := cpow_half_sq hc0
  have hp : 0 < p.re := re_cpow_half_pos hb
  have hq : 0 < q.re := re_cpow_half_pos hc
  have hq0 : q ≠ 0 := fun h => by simp [h] at hq
  have ep : (p^2).re = p.re^2 - p.im^2 := by simp [sq]
  have eq : (q^2).re = q.re^2 - q.im^2 := by simp [sq]
  rw [hp2] at ep; rw [hq2] at eq
  have hre : 0 < (p/q).re := by
    rw [div_re]
    have hn : 0 < normSq q := normSq_pos.mpr hq0
    have hlt : (p.im*q.im)^2 < (p.re*q.re)^2 := by
      rw [mul_pow, mul_pow]
      have h3 : p.im^2*q.im^2 ≤ p.re^2*q.im^2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      have h4 : p.re^2*q.im^2 < p.re^2*q.re^2 := mul_lt_mul_of_pos_left (by linarith) (by positivity)
      linarith
    have := abs_lt_of_sq_lt_sq hlt (by positivity)
    have h5 : 0 < p.re*q.re + p.im*q.im := by linarith [neg_abs_le (p.im*q.im)]
    rw [← add_div]
    exact div_pos (by linarith) hn
  rw [← sq_cpow_half hre, div_pow, hp2, hq2]

/-- Identity under the stated parameter and domain assumptions: `(∫ t : ℝ in Ioi 0, exp (-a*t)*erf
((b*t)^(1/2 : ℂ)))=(b/(a+b))^(1/2 : ℂ)/a`. -/
@[dlmf 7.14.E3]
theorem erf_sqrt_laplace {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*erf ((b*t)^(1/2 : ℂ)))=(b/(a+b))^(1/2 : ℂ)/a := by
  set c := a+b with hcdef
  have hc : 0 < c.re := by simp [hcdef]; linarith
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  set p := b^(1/2 : ℂ); set q := c^(1/2 : ℂ)
  have hp2 : p^2 = b := cpow_half_sq hb0
  have hq2 : q^2 = c := cpow_half_sq hc0
  have hpre : 0 < p.re := re_cpow_half_pos hb
  have hqre : 0 < q.re := re_cpow_half_pos hc
  have hq0 : q ≠ 0 := fun h => by simp [h] at hqre
  have hp0 : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hsplit (t : ℝ) (ht : 0 < t) : (b*t)^(1/2 : ℂ) = p*(t:ℂ)^(1/2 : ℂ) := by
    rw [mul_comm, ofReal_mul_cpow_of_pos ht hb0, mul_comm]
  set K := p/(a*q)
  set F : ℝ → ℂ := fun t => -(exp (-a*t)/a)*erf (p*(t:ℂ)^(1/2 : ℂ)) + K*erf (q*(t:ℂ)^(1/2 : ℂ))
    with hF
  have hd : ∀ t : ℝ, 0 < t → HasDerivAt F (exp (-a*t)*erf ((b*t)^(1/2 : ℂ))) t := by
    intro t ht
    have hm : (t:ℂ) ∈ slitPlane := by simp [mem_slitPlane_iff, ht]
    have ht0 : (t:ℂ)^(1/2 : ℂ) ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]; simp [ht.ne']
    have hts : ((t:ℂ)^(1/2 : ℂ))^2 = t := cpow_half_sq (by exact_mod_cast ht.ne')
    have h1 : HasDerivAt (fun t : ℝ => (t:ℂ)^(1/2 : ℂ)) ((1/2:ℂ)*(((t:ℂ)^(1/2 : ℂ))⁻¹)) t := by
      have := ((hasDerivAt_id (t:ℂ)).cpow_const (c := (1/2:ℂ)) hm).comp_ofReal
      rw [show (1/2:ℂ)-1 = -(1/2) by norm_num, cpow_neg] at this
      simpa using this
    have hE (r : ℂ) : HasDerivAt (fun t : ℝ => erf (r*(t:ℂ)^(1/2 : ℂ)))
        (2/Real.sqrt π*exp (-(r*(t:ℂ)^(1/2 : ℂ))^2)*(r*((1/2:ℂ)*(((t:ℂ)^(1/2 : ℂ))⁻¹)))) t :=
      (hasDerivAt_erf_complex _).comp t (h1.const_mul r)
    have hexp : HasDerivAt (fun t : ℝ => exp (-a*(t:ℂ))) (exp (-a*t)*(-a)) t := by
      have := ((hasDerivAt_id (t:ℂ)).const_mul (-a)).cexp
      simpa using this.comp_ofReal
    have h := (((hexp.div_const a).mul (hE p)).neg).add ((hE q).const_mul K)
    convert h using 1
    · funext s; simp [hF]
    · rw [hsplit t ht, mul_pow, mul_pow, hts, hp2, hq2]
      have hex : exp (-((a:ℂ)*t))*exp (-((t:ℂ)*b)) = exp (-((t:ℂ)*c)) := by
        rw [← Complex.exp_add]; congr 1; simp [hcdef]; ring
      simp only [K]
      field_simp
      linear_combination p*hex
  have hsqrt (t : ℝ) (ht : 0 ≤ t) : (t:ℂ)^(1/2 : ℂ) = ((Real.sqrt t:ℝ):ℂ) := by
    rw [show (1/2:ℂ) = ((1/2:ℝ):ℂ) by push_cast; ring, ← ofReal_cpow ht, Real.sqrt_eq_rpow]
  have hcont : ContinuousWithinAt F (Ici 0) 0 := by
    have h1 : ContinuousAt (fun t : ℝ => (t:ℂ)^(1/2 : ℂ)) 0 := by
      have : ContinuousAt (fun y : ℂ => y^(1/2:ℂ)) ((0:ℝ):ℂ) :=
        continuousAt_cpow_const_of_re_pos (Or.inl (by simp)) (by norm_num)
      exact this.comp (f := fun t : ℝ => (t:ℂ)) (by fun_prop)
    have he : Continuous erf := differentiable_erf_complex.continuous
    refine ContinuousAt.continuousWithinAt ?_
    simp only [hF]
    exact (((by fun_prop : Continuous fun t : ℝ => exp (-a*t)/a).continuousAt.neg).mul
      (he.continuousAt.comp (h1.const_mul p))).add (continuousAt_const.mul
      (he.continuousAt.comp (h1.const_mul q)))
  have hlim : Tendsto F atTop (𝓝 (0 + K*1)) := by
    refine Tendsto.add ?_ (Tendsto.const_mul K ?_)
    · have hev : ∀ᶠ t : ℝ in atTop, ‖-(exp (-a*t)/a)*erf (p*(t:ℂ)^(1/2 : ℂ))‖ ≤
          2/‖a‖*Real.exp (-a.re*t) := by
        filter_upwards [eventually_gt_atTop 0] with t ht
        rw [hsqrt t ht.le, norm_mul, norm_neg, norm_div, Complex.norm_exp]
        have h1 : 0 < (p*((Real.sqrt t:ℝ):ℂ)).re := by
          rw [re_mul_ofReal]; exact mul_pos hpre (Real.sqrt_pos.mpr ht)
        have h2 : 0 < ((p*((Real.sqrt t:ℝ):ℂ))^2).re := by
          rw [mul_pow, ← ofReal_pow, Real.sq_sqrt ht.le, hp2, re_mul_ofReal]; positivity
        have := norm_erf_le_two h1 h2
        have hre : (-a*(t:ℂ)).re = -a.re*t := by simp
        rw [hre]
        have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha0
        calc Real.exp (-a.re*t)/‖a‖*‖erf (p*((Real.sqrt t:ℝ):ℂ))‖ ≤ Real.exp (-a.re*t)/‖a‖*2 := by
              gcongr
          _ = _ := by ring
      refine squeeze_zero_norm' hev ?_
      have : Tendsto (fun t : ℝ => -a.re*t) atTop atBot :=
        tendsto_id.const_mul_atTop_of_neg (by linarith)
      simpa using (Real.tendsto_exp_atBot.comp this).const_mul (2/‖a‖)
    · have h0 : Tendsto (fun t : ℝ => erfc (q*(t:ℂ)^(1/2 : ℂ))) atTop (𝓝 0) := by
        refine tendsto_erfc_zero_of_re_sq ?_ ?_
        · filter_upwards [eventually_gt_atTop 0] with t ht
          rw [hsqrt t ht.le, re_mul_ofReal]; exact mul_pos hqre (Real.sqrt_pos.mpr ht)
        · have h0 : Tendsto (fun t : ℝ => c.re*t) atTop atTop := tendsto_id.const_mul_atTop' hc
          refine h0.congr' ?_
          filter_upwards [eventually_ge_atTop 0] with t ht
          rw [hsqrt t ht, mul_pow, ← ofReal_pow, Real.sq_sqrt ht, hq2, re_mul_ofReal]
      have := h0.const_sub 1
      simp only [sub_zero] at this
      refine this.congr fun t => ?_
      simp [erfc]
  have hint : IntegrableOn (fun t : ℝ => exp (-a*t)*erf ((b*t)^(1/2 : ℂ))) (Ioi 0) := by
    have hg : IntegrableOn (fun t : ℝ => 2*Real.exp (-a.re*t)) (Ioi 0) :=
      ((exp_neg_integrableOn_Ioi 0 ha).const_mul 2 :)
    refine hg.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
      have ht : (0:ℝ) < t := ht
      have hm : b*(t:ℂ) ∈ slitPlane := Or.inl (by rw [re_mul_ofReal]; positivity)
      have hc1 : ContinuousAt (fun y : ℂ => y^(1/2:ℂ)) (b*(t:ℂ)) := continuousAt_cpow_const hm
      refine ContinuousAt.continuousWithinAt ?_
      exact (by fun_prop : Continuous fun t : ℝ => exp (-a*t)).continuousAt.mul
        (differentiable_erf_complex.continuous.continuousAt.comp
          (hc1.comp (f := fun t : ℝ => b*(t:ℂ)) (by fun_prop)))
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
      have ht : (0:ℝ) < t := ht
      have hbt : 0 < (b*(t:ℂ)).re := by rw [re_mul_ofReal]; positivity
      have h1 := re_cpow_half_pos hbt
      have h2 : 0 < (((b*(t:ℂ))^(1/2 : ℂ))^2).re := by
        rw [cpow_half_sq (fun h => by simp [h] at hbt)]; exact hbt
      rw [norm_mul, Complex.norm_exp, mul_comm]
      have : (-a*(t:ℂ)).re = -a.re*t := by simp
      rw [this]
      exact mul_le_mul_of_nonneg_right (norm_erf_le_two h1 h2) (Real.exp_pos _).le
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont (fun t ht => hd t ht) hint hlim]
  have h00 : ((0:ℝ):ℂ)^(1/2 : ℂ) = 0 := by simp
  simp only [hF, h00, mul_zero, erf_zero, zero_add, sub_zero]
  rw [div_cpow_half hb hc]
  simp only [K]
  change p/(a*q)*1 = p/q/a
  field_simp

end DLMF.Confluent
end
