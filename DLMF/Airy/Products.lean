/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.SquareTools
public import DLMF.Gamma.MellinBarnes
public import DLMFMathlib.Analysis.MellinParseval
public import DLMFMathlib.Analysis.Fourier.HyperbolicSecantLog

/-!
# Products of Airy functions (DLMF §9.11)

The third-order equation satisfied by products of Airy solutions, its Wronskian, integral
representations of `Ai²` and `Ai² + Bi²`, antiderivatives of products and quotients, and
definite integrals of products.

## Main results

* `airy_product_ode`: `w''' - 4z w' - 2w = 0` for a product of two solutions (DLMF 9.11.1).
* `airy_product_wronskian`: the Wronskian of `Ai², Ai Bi, Bi²` is `2/π³` (DLMF 9.11.2).
* `airyAi_sq_bessel_integral`: DLMF 9.11.3.
* `airy_modulus_sq_exp_integral`: `Ai² + Bi²` as a Nicholson-type integral (DLMF 9.11.4).
* `airy_product_antiderivative_5`, …, `airy_product_antiderivative_10`: DLMF 9.11.5–9.11.10.
* `airy_quotient_antiderivative`, `airyAi_recip_sq_antiderivative`,
  `airyAiBi_recip_antiderivative`, `airy_modulus_rational_antiderivative`:
  DLMF 9.11.11–9.11.14.
* `airyAi_sq_mellin`: the Mellin transform of `Ai²` (DLMF 9.11.15).
* `airyAi_cube_integral`, `airyAi_sq_airyBi_integral`, `airyAi_fourth_integral`:
  DLMF 9.11.16–9.11.18.
* `airy_modulus_reciprocal_integrals`: DLMF 9.11.19.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF.Confluent
open scoped Real Topology
open DLMF.Core

namespace DLMF.Airy

/-- The derivative of a product of Airy solutions. -/
theorem airy_product_deriv {f f' g g' : ℂ → ℂ} (hf : IsAirySolution f f')
    (hg : IsAirySolution g g') :
    deriv (fun z => f z * g z) = fun z => f' z * g z + f z * g' z :=
  ODE.product_deriv (fun z => (hf z).1) (fun z => (hg z).1)

/-- The second derivative of a product of Airy solutions. -/
theorem airy_product_second_deriv {f f' g g' : ℂ → ℂ} (hf : IsAirySolution f f')
    (hg : IsAirySolution g g') :
    deriv (deriv (fun z => f z * g z)) = fun z => 2 * z * f z * g z + 2 * f' z * g' z :=
  ODE.product_second_deriv hf hg

/-- A product `w = f g` of two Airy solutions satisfies the third-order equation
`w''' - 4 z w' - 2 w = 0` (DLMF 9.11.1). -/
@[dlmf 9.11.E1]
theorem airy_product_ode {f f' g g' : ℂ → ℂ} (hf : IsAirySolution f f')
    (hg : IsAirySolution g g') (z : ℂ) :
    iteratedDeriv 3 (fun t => f t * g t) z - 4 * z * deriv (fun t => f t * g t) z - 2 *
        f z * g z = 0 := by
  have h := ODE.product_third_deriv hf hg (fun z => hasDerivAt_id z) z
  linear_combination h

/-- The Wronskian of `Ai², Ai Bi, Bi²` is `2/π³` (DLMF 9.11.2). -/
@[dlmf 9.11.E2]
theorem airy_product_wronskian (z : ℂ) :
    airyWronskian3 (fun t => airyAi t ^ 2) (fun t => airyAi t * airyBi t) (fun t => airyBi t ^ 2) z
        = 2 / π ^ 3 := by
  have hA : (fun t => airyAi t ^ 2) = fun t => airyAi t * airyAi t := by funext t; ring
  have hB : (fun t => airyBi t ^ 2) = fun t => airyBi t * airyBi t := by funext t; ring
  unfold airyWronskian3
  rw [hA, hB]
  rw [airy_product_second_deriv isAirySolution_airyAi isAirySolution_airyAi,
    airy_product_second_deriv isAirySolution_airyAi isAirySolution_airyBi,
    airy_product_second_deriv isAirySolution_airyBi isAirySolution_airyBi]
  simp only [airy_product_deriv isAirySolution_airyAi isAirySolution_airyAi,
    airy_product_deriv isAirySolution_airyAi isAirySolution_airyBi,
    airy_product_deriv isAirySolution_airyBi isAirySolution_airyBi]
  calc
    _ = 2 * (airyAi z * airyBiDeriv z - airyAiDeriv z * airyBi z) ^ 3 := by ring
    _ = 2 / π ^ 3 := by rw [wronskian_airyAi_airyBi]; ring

/-- For `x ≥ 0`, `∫₀^∞ J₀(t³/12 + x t) t dt = 4π√3 Ai(x)²` as an improper integral (DLMF 9.11.3). -/
@[dlmf 9.11.E3]
theorem airyAi_sq_bessel_integral {x : ℝ} (hx : 0 ≤ x) :
    HasIntegralAtTop (fun t : ℝ => Complex.besselJ 0 ((t : ℂ) ^ 3 / 12 + x * t) * t)
      0 (4 * π * Real.sqrt 3 * airyAi x ^ 2) := by
  sorry

/-- `Ai(z)² + Bi(z)² = π^{-3/2} ∫₀^∞ exp(z t - t³/12) t^{-1/2} dt`, the integral converging
absolutely (DLMF 9.11.4). -/
@[dlmf 9.11.E4]
theorem airy_modulus_sq_exp_integral (z : ℂ) :
    IntegrableOn (fun t : ℝ => exp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)) (Ioi 0) ∧
      airyAi z ^ 2 + airyBi z ^ 2 =
        (∫ t : ℝ in Ioi 0, exp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)) /
          (π : ℂ) ^ (3 / 2 : ℂ) :=
  ModulusPhase.modulus_sq_exp_integral z

/-- For Airy solutions `f, g`, an antiderivative of `f g` is `-f' g' + z f g` (DLMF 9.11.5). -/
@[dlmf 9.11.E5]
theorem airy_product_antiderivative_5 {f f' g g' : ℂ → ℂ} (hf : IsAirySolution f f')
    (hg : IsAirySolution g g') (z : ℂ) :
    HasDerivAt (fun t => -f' t * g' t + t * f t * g t) (f z * g z) z := by
  have h := ((hf z).2.neg.mul (hg z).2).add
    (((hasDerivAt_id z).mul (hf z).1).mul (hg z).1)
  exact h.congr_deriv (by simp only [_root_.id, Pi.mul_apply, Pi.neg_apply]; ring)

/-- For Airy solutions `f, g` with Wronskian `𝒲 = f g' - f' g`, an antiderivative of `f g'` is
`(f g + 𝒲 z)/2` (DLMF 9.11.6). -/
@[dlmf 9.11.E6]
theorem airy_product_antiderivative_6 {f f' g g' : ℂ → ℂ} (hf : IsAirySolution f f')
    (hg : IsAirySolution g g') (z : ℂ) :
    HasDerivAt (fun t => (f t * g t + t * (f 0 * g' 0 - f' 0 * g 0)) / 2) (f z * g' z) z := by
  have h := (((hf z).1.mul (hg z).1).add
    ((hasDerivAt_id z).mul_const (f 0 * g' 0 - f' 0 * g 0))).div_const 2
  have hW := hf.wronskian_eq hg z
  exact h.congr_deriv (by linear_combination -hW / 2)

/-- For Airy solutions `f, g`, an antiderivative of `f' g'` is `(f g' + f' g + z f' g' - z² f g)/3`
(DLMF 9.11.7). -/
@[dlmf 9.11.E7]
theorem airy_product_antiderivative_7 {f f' g g' : ℂ → ℂ} (hf : IsAirySolution f f')
    (hg : IsAirySolution g g') (z : ℂ) :
    HasDerivAt (fun t => (f t * g' t + f' t * g t + t * f' t * g' t - t ^ 2 * f t * g t) / 3)
        (f' z * g' z) z := by
  have h := (((((hf z).1.mul (hg z).2).add ((hf z).2.mul (hg z).1)).add
    (((hasDerivAt_id z).mul (hf z).2).mul (hg z).2)).sub
      (((hasDerivAt_pow 2 z).mul (hf z).1).mul (hg z).1)).div_const 3
  exact h.congr_deriv (by simp only [_root_.id, Pi.mul_apply]; ring)

/-- For Airy solutions `f, g`, an antiderivative of `z f g` is
`(f g' + f' g)/6 - (z f' g' - z² f g)/3` (DLMF 9.11.8). -/
@[dlmf 9.11.E8]
theorem airy_product_antiderivative_8 {f f' g g' : ℂ → ℂ} (hf : IsAirySolution f f')
    (hg : IsAirySolution g g') (z : ℂ) :
    HasDerivAt (fun t => (f t * g' t + f' t * g t) / 6 - (t * f' t * g' t - t ^ 2 * f t * g t) / 3)
        (z * f z * g z) z := by
  have h := ((((hf z).1.mul (hg z).2).add ((hf z).2.mul (hg z).1)).div_const 6).sub
    (((((hasDerivAt_id z).mul (hf z).2).mul (hg z).2).sub
      (((hasDerivAt_pow 2 z).mul (hf z).1).mul (hg z).1)).div_const 3)
  exact h.congr_deriv (by simp only [_root_.id, Pi.mul_apply]; ring)

/-- For Airy solutions `f, g` with Wronskian `𝒲`, an antiderivative of `z f g'` is
`f' g'/2 + 𝒲 z²/4` (DLMF 9.11.9). -/
@[dlmf 9.11.E9]
theorem airy_product_antiderivative_9 {f f' g g' : ℂ → ℂ} (hf : IsAirySolution f f')
    (hg : IsAirySolution g g') (z : ℂ) :
    HasDerivAt (fun t => f' t * g' t / 2 + t ^ 2 * (f 0 * g' 0 - f' 0 * g 0) / 4)
        (z * f z * g' z) z := by
  have h := (((hf z).2.mul (hg z).2).div_const 2).add
    (((hasDerivAt_pow 2 z).mul_const (f 0 * g' 0 - f' 0 * g 0)).div_const 4)
  have hW := hf.wronskian_eq hg z
  exact h.congr_deriv (by linear_combination -(z / 2) * hW)

/-- For Airy solutions `f, g`, an antiderivative of `z f' g'` is
`(3/10)(-f g + z f g' + z f' g) + (z² f' g' - z³ f g)/5` (DLMF 9.11.10). -/
@[dlmf 9.11.E10]
theorem airy_product_antiderivative_10 {f f' g g' : ℂ → ℂ} (hf : IsAirySolution f f')
    (hg : IsAirySolution g g') (z : ℂ) :
    HasDerivAt (fun t => 3 / 10 * (-f t * g t + t * f t * g' t + t * f' t * g t) +
        (t ^ 2 * f' t * g' t - t ^ 3 * f t * g t) / 5) (z * f' z * g' z) z := by
  have h := (((((hf z).1.mul (hg z).1).neg.add
    (((hasDerivAt_id z).mul (hf z).1).mul (hg z).2)).add
      (((hasDerivAt_id z).mul (hf z).2).mul (hg z).1)).const_mul (3 / 10 : ℂ)).add
    (((((hasDerivAt_pow 2 z).mul (hf z).2).mul (hg z).2).sub
      (((hasDerivAt_pow 3 z).mul (hf z).1).mul (hg z).1)).div_const 5)
  convert h using 1
  · funext t
    simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, _root_.id]
    ring
  · simp only [Pi.mul_apply, _root_.id]
    ring

/-- For Airy solutions `f, g` with nonzero Wronskian `𝒲`, if `F` has derivative `F'` at `g(z)/f(z)`
and `f(z) ≠ 0`, then `F(g/f)/𝒲` has derivative `F'/f(z)²` at `z` (DLMF 9.11.11). -/
@[dlmf 9.11.E11]
theorem airy_quotient_antiderivative {f f' g g' : ℂ → ℂ} (hf : IsAirySolution f f')
    (hg : IsAirySolution g g')
    {F : ℂ → ℂ} {F' z : ℂ}
    (hF : HasDerivAt F F' (g z / f z)) (hfz : f z ≠ 0)
    (hW : f 0 * g' 0 - f' 0 * g 0 ≠ 0) :
    HasDerivAt (fun t => F (g t / f t) / (f 0 * g' 0 - f' 0 * g 0)) (F' / f z ^ 2) z := by
  have h := (hF.comp z ((hg z).1.div (hf z).1 hfz)).div_const (f 0 * g' 0 - f' 0 * g 0)
  have he : g' z * f z - g z * f' z = f 0 * g' 0 - f' 0 * g 0 := by
    linear_combination hf.wronskian_eq hg z
  exact h.congr_deriv (by rw [he]; field_simp)

/-- Where `Ai z ≠ 0`, an antiderivative of `1/Ai(z)²` is `π Bi(z)/Ai(z)` (DLMF 9.11.12). -/
@[dlmf 9.11.E12]
theorem airyAi_recip_sq_antiderivative {z : ℂ} (hz : airyAi z ≠ 0) :
    HasDerivAt (fun t => π * airyBi t / airyAi t) (1 / airyAi z ^ 2) z := by
  have h := ((hasDerivAt_airyBi z).div (hasDerivAt_airyAi z) hz).const_mul (π : ℂ)
  have he : airyBiDeriv z * airyAi z - airyBi z * airyAiDeriv z = 1 / π := by
    linear_combination wronskian_airyAi_airyBi z
  convert h using 1
  · funext t; simp only [Pi.div_apply]; ring
  · rw [he]
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp

/-- Where `Ai Bi ≠ 0` and `Bi/Ai` lies in the slit plane, an antiderivative of `1/(Ai Bi)` is
`π ln(Bi/Ai)` (DLMF 9.11.13). -/
@[dlmf 9.11.E13]
theorem airyAiBi_recip_antiderivative {z : ℂ} (ha : airyAi z ≠ 0) (hb : airyBi z ≠ 0)
    (hlog : airyBi z / airyAi z ∈ slitPlane) :
    HasDerivAt (fun t => π * log (airyBi t / airyAi t)) (1 / (airyAi z * airyBi z)) z := by
  have hq := (hasDerivAt_airyBi z).div (hasDerivAt_airyAi z) ha
  have h := ((Complex.hasDerivAt_log hlog).comp z hq).const_mul (π : ℂ)
  have he : airyBiDeriv z * airyAi z - airyBi z * airyAiDeriv z = 1 / π := by
    linear_combination wronskian_airyAi_airyBi z
  convert h using 1
  · funext t
    simp only [Function.comp_apply, Pi.div_apply]
  · rw [he]
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp [ha, hb, hπ]

/-- Where `Ai² + Bi² ≠ 0`, an antiderivative of `Ai Bi/(Ai² + Bi²)²` is `(π/2) Bi²/(Ai² + Bi²)`
(DLMF 9.11.14). -/
@[dlmf 9.11.E14]
theorem airy_modulus_rational_antiderivative {z : ℂ} (hz : airyAi z ^ 2 + airyBi z ^ 2 ≠ 0) :
    HasDerivAt (fun t => π / 2 * airyBi t ^ 2 / (airyAi t ^ 2 + airyBi t ^ 2))
      (airyAi z * airyBi z / (airyAi z ^ 2 + airyBi z ^ 2) ^ 2) z := by
  have hnum := ((hasDerivAt_airyBi z).pow 2).const_mul (π / 2 : ℂ)
  have hden := ((hasDerivAt_airyAi z).pow 2).add ((hasDerivAt_airyBi z).pow 2)
  have h := hnum.div hden hz
  simp only [Pi.pow_apply, Pi.add_apply] at h
  refine h.congr_deriv ?_
  have hW : (π : ℂ) * (airyAi z * airyBiDeriv z - airyAiDeriv z * airyBi z) = 1 := by
    rw [wronskian_airyAi_airyBi]
    simpa only [one_div] using mul_inv_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero : (π : ℂ) ≠ 0)
  field_simp
  linear_combination 2 * airyAi z * airyBi z * hW

/-- The Mellin transform of `Ai²`: for `Re α > 0`,
`∫₀^∞ t^{α-1} Ai(t)² dt = 2Γ(α)/(√π 12^{(2α+5)/6} Γ(α/3 + 5/6))` (DLMF 9.11.15). Proved from
the representation
`Ai(x)² = (2^{2/3}/π) ∫₀^∞ Ai(2^{2/3}(x + t²)) dt` (`airyAi_sq_eq_integral`), Fubini with the
Beta integral, and the Mellin transform of `Ai` (9.10.17). -/
@[dlmf 9.11.E15]
theorem airyAi_sq_mellin {α : ℂ} (hα : 0 < α.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (α - 1) * airyAi t ^ 2) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (α - 1) * airyAi t ^ 2) =
        2 * Gamma α / (Real.sqrt π * (12 : ℂ) ^ ((2 * α + 5) / 6) * Gamma (α / 3 + 5 / 6)) := by
  refine ⟨AiSquare.integrableOn_mellin hα, ?_⟩
  have hw : 0 < (α + 1 / 2).re := by simp; linarith
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => AiSquare.mellin_pt α x),
      integral_const_mul,
    AiSquare.integral_integral_mellinKernel hα, show α + 1 / 2 - 1 = (α + 1 / 2) - 1 by
        ring, AiSquare.scaled_mellin hw,
    show (α + 1 / 2 + 2) / 3 = (2 * α + 5) / 6 by ring,
    show (α + 1 / 2) / 3 + 2 / 3 = α / 3 + 5 / 6 by ring]
  have hB := Gamma_mul_Gamma_eq_betaIntegral hα (show (0 : ℝ) < (1 / 2 : ℂ).re by norm_num)
  have hG : Gamma (1 / 2 : ℂ) = (Real.sqrt π : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal,
      Real.Gamma_one_half_eq]
  rw [hG] at hB
  have hGw := Gamma_ne_zero_of_re_pos hw
  have hG5 : Gamma (α / 3 + 5 / 6) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hs : (Real.sqrt π : ℂ) ^ 2 = π := by
    rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hsp : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hlc : Real.log AiSquare.scale = 2 / 3 * Real.log 2 := by
    rw [AiSquare.scale, Real.log_rpow two_pos]
  have hl12 : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
    rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]; push_cast; ring
  have h12 : (12 : ℂ) ^ ((2 * α + 5) / 6) = exp ((Real.log 12 : ℂ) * ((2 * α + 5) / 6)) := by
    rw [show (12 : ℂ) = ((12 : ℝ) : ℂ) by norm_num, Complex.ofReal_cpow_eq_exp (by
        norm_num)]
  have h3 : (3 : ℂ) ^ ((2 * α + 5) / 6) = exp ((Real.log 3 : ℂ) * ((2 * α + 5) / 6)) := by
    rw [show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num, Complex.ofReal_cpow_eq_exp (by norm_num)]
  have hc : ((AiSquare.scale : ℝ) : ℂ) = exp (Real.log AiSquare.scale : ℂ) := by
    rw [← ofReal_exp, Real.exp_log AiSquare.scale_pos]
  have key : ((AiSquare.scale : ℝ) : ℂ) * exp (-(Real.log AiSquare.scale : ℂ) * (α + 1 / 2)) *
      (12 : ℂ) ^ ((2 * α + 5) / 6) = 4 * (3 : ℂ) ^ ((2 * α + 5) / 6) := by
    rw [h12, h3, hc, ← Complex.exp_add, ← Complex.exp_add, hlc, hl12,
      show (4 : ℂ) = exp ((Real.log 4 : ℂ)) by
                                              rw [← ofReal_exp, Real.exp_log
                                                (by norm_num)]; norm_num,
      ← Complex.exp_add, show Real.log 4 = 2 * Real.log 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring]
    congr 1; push_cast; ring
  have h3ne : (3 : ℂ) ^ ((2 * α + 5) / 6) ≠ 0 := by rw [h3]; exact Complex.exp_ne_zero _
  have h12ne : (12 : ℂ) ^ ((2 * α + 5) / 6) ≠ 0 := by rw [h12]; exact Complex.exp_ne_zero _
  have hB' : betaIntegral α (1 / 2) = Gamma α * (Real.sqrt π : ℂ) / Gamma (α + 1 / 2) := by
    rw [eq_div_iff hGw]; linear_combination -hB
  rw [hB']
  have hCE : ((AiSquare.scale : ℝ) : ℂ) * exp (-(Real.log AiSquare.scale : ℂ) * (α + 1 / 2)) ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.mpr AiSquare.scale_pos.ne') (Complex.exp_ne_zero _)
  have hT : (12 : ℂ) ^ ((2 * α + 5) / 6) = 4 * (3 : ℂ) ^ ((2 * α + 5) / 6) /
      (((AiSquare.scale : ℝ) : ℂ) * exp (-(Real.log AiSquare.scale : ℂ) * (α + 1 / 2))) := by
    rw [eq_div_iff hCE]; linear_combination key
  rw [hT, ofReal_div, ofReal_mul, ← hs]
  generalize Gamma α = Ga at *
  generalize Gamma (α + 1 / 2) = Gw at *
  generalize Gamma (α / 3 + 5 / 6) = G5 at *
  generalize exp (-(Real.log AiSquare.scale : ℂ) * (α + 1 / 2)) = E at *
  generalize (3 : ℂ) ^ ((2 * α + 5) / 6) = T3 at *
  generalize ((AiSquare.scale : ℝ) : ℂ) = C at *
  generalize ((Real.sqrt π : ℝ) : ℂ) = S at *
  have hE : E ≠ 0 := right_ne_zero_of_mul hCE
  have hC : C ≠ 0 := left_ne_zero_of_mul hCE
  push_cast
  field_simp
  ring

namespace AiSquare

/-- The Gamma quotient giving the Mellin transform of the square of `Ai`. -/
def mellinValue (s : ℂ) : ℂ :=
  2 * Complex.Gamma s /
    (Real.sqrt Real.pi * (12 : ℂ) ^ ((2 * s + 5) / 6) * Complex.Gamma (s / 3 + 5 / 6))

/-- The square of `Ai` has the stated Mellin transform in the right half-plane. -/
lemma mellin_eq_value {s : ℂ} (hs : 0 < s.re) :
    mellin (fun x : ℝ => airyAi x ^ 2) s = mellinValue s := by
  simpa only [mellin, smul_eq_mul, mellinValue] using (airyAi_sq_mellin hs).2

/-- Reflection evaluates the product of complementary Mellin values. -/
lemma mellinValue_mul_mellinValue_one_sub (s : ℂ) (hs : 1 - 2 * s ≠ 0)
    (hG : Complex.Gamma (s / 3 + 5 / 6) ≠ 0)
    (hG' : Complex.Gamma (7 / 6 - s / 3) ≠ 0) :
    mellinValue s * mellinValue (1 - s) =
      Complex.sin (Real.pi * (s / 3 + 5 / 6)) /
        (6 * Real.pi * (1 - 2 * s) * Complex.sin (Real.pi * s)) := by
  have hP : (12 : ℂ) ^ ((2 * s + 5) / 6) *
      (12 : ℂ) ^ ((2 * (1 - s) + 5) / 6) = 144 := by
    rw [← Complex.cpow_add _ _ (by norm_num), show
      (2 * s + 5) / 6 + (2 * (1 - s) + 5) / 6 = (2 : ℂ) by ring]
    norm_num [Complex.cpow_two]
  have hR := Complex.Gamma_mul_Gamma_one_sub s
  have hA := Complex.Gamma_mul_Gamma_one_sub (s / 3 + 5 / 6)
  have hr : 1 - (s / 3 + 5 / 6) ≠ 0 := by
    intro h; apply hs; linear_combination 6 * h
  have hstep := Complex.Gamma_add_one (1 - (s / 3 + 5 / 6)) hr
  rw [show 1 - (s / 3 + 5 / 6) + 1 = 7 / 6 - s / 3 by ring] at hstep
  have hprod : Complex.Gamma (s / 3 + 5 / 6) *
      Complex.Gamma (7 / 6 - s / 3) =
      (1 - 2 * s) * Real.pi / (6 * Complex.sin (Real.pi * (s / 3 + 5 / 6))) := by
    rw [hstep, mul_left_comm, hA]
    ring
  have hsa : Complex.sin (Real.pi * (s / 3 + 5 / 6)) ≠ 0 := by
    intro h
    simp only [h, mul_zero, div_zero] at hprod
    exact mul_ne_zero hG hG' hprod
  dsimp [mellinValue]
  rw [show (1 - s) / 3 + 5 / 6 = 7 / 6 - s / 3 by ring]
  have hp : (Real.sqrt Real.pi : ℂ) ^ 2 = Real.pi := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have heq :
      2 * Complex.Gamma s /
        (Real.sqrt Real.pi * (12 : ℂ) ^ ((2 * s + 5) / 6) * Complex.Gamma (s / 3 + 5 / 6)) *
      (2 * Complex.Gamma (1 - s) /
        (Real.sqrt Real.pi * (12 : ℂ) ^ ((2 * (1 - s) + 5) / 6) *
          Complex.Gamma (7 / 6 - s / 3))) =
      4 * (Complex.Gamma s * Complex.Gamma (1 - s)) /
        ((Real.sqrt Real.pi : ℂ)^2 *
          ((12 : ℂ)^((2*s+5)/6)*(12:ℂ)^((2*(1-s)+5)/6)) *
          (Complex.Gamma (s/3+5/6)*Complex.Gamma (7/6-s/3))) := by ring
  rw [heq, hp, hP, hR, hprod]
  field_simp
  ring

end AiSquare

namespace AiSquare

/-- On the central vertical line, the reflected product is a hyperbolic secant kernel. -/
lemma mellinValue_half_mul_reflected {y : ℝ} (hy : y ≠ 0) :
    mellinValue ((1 / 2 : ℂ) + y * I) * mellinValue ((1 / 2 : ℂ) - y * I) =
      (Real.sinh (Real.pi * y / 3) / (12 * Real.pi * y * Real.cosh (Real.pi * y)) : ℝ) := by
  have hs : (1 : ℂ) - 2 * ((1 / 2 : ℂ) + y * I) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
    exact hy (by linarith)
  have hG : Gamma (((1 / 2 : ℂ) + y * I) / 3 + 5 / 6) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  have hG' : Gamma (7 / 6 - ((1 / 2 : ℂ) + y * I) / 3) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  have h := mellinValue_mul_mellinValue_one_sub ((1 / 2 : ℂ) + y * I) hs hG hG'
  rw [show (1 : ℂ) - ((1 / 2 : ℂ) + y * I) = 1 / 2 - y * I by ring] at h
  rw [h]
  have hs1 : Complex.sin (Real.pi * ((1 / 2 : ℂ) + y * I)) =
      (Real.cosh (Real.pi * y) : ℝ) := by
    rw [show (Real.pi : ℂ) * ((1 / 2 : ℂ) + y * I) =
      (Real.pi : ℂ) / 2 + ((Real.pi * y : ℝ) : ℂ) * I by push_cast; ring,
      Complex.sin_add, Complex.sin_pi_div_two, Complex.cos_pi_div_two]
    simp [Complex.cos_mul_I, Complex.ofReal_cosh]
  have hs2 : Complex.sin (Real.pi * (((1 / 2 : ℂ) + y * I) / 3 + 5 / 6)) =
      -I * (Real.sinh (Real.pi * y / 3) : ℝ) := by
    rw [show (Real.pi : ℂ) * (((1 / 2 : ℂ) + y * I) / 3 + 5 / 6) =
      (Real.pi : ℂ) + ((Real.pi * y / 3 : ℝ) : ℂ) * I by push_cast; ring,
      Complex.sin_add, Complex.sin_pi, Complex.cos_pi]
    simp only [zero_mul, neg_mul, zero_add]
    rw [Complex.sin_mul_I, ← Complex.ofReal_sinh]
    ring
  rw [hs1, hs2]
  push_cast
  have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hcosh : (Real.cosh (Real.pi * y) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'
  field_simp
  ring

/-- The norm of the central Mellin value factors into Gamma norms. -/
lemma norm_mellinValue_half (y : ℝ) :
    ‖mellinValue ((1 / 2 : ℂ) + y * I)‖ =
      (1 / (6 * Real.sqrt Real.pi)) * ‖Gamma ((1 / 2 : ℂ) + I * y)‖ *
        ‖(Gamma (1 + I * (y / 3 : ℝ)))⁻¹‖ := by
  have hp : ‖(12 : ℂ) ^ ((2 * ((1 / 2 : ℂ) + y * I) + 5) / 6)‖ = 12 := by
    rw [show (12 : ℂ) = ((12 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    norm_num
  have hsq : ‖(Real.sqrt Real.pi : ℂ)‖ = Real.sqrt Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  dsimp [mellinValue]
  rw [norm_div, norm_mul, norm_mul, norm_mul, hp, hsq, norm_inv]
  norm_num
  rw [show ((1 / 2 : ℂ) + y * I) / 3 + 5 / 6 =
    1 + I * (y / 3 : ℝ) by push_cast; ring, mul_comm (y : ℂ) I]
  push_cast
  ring

/-- The Mellin transform of `Ai²` is absolutely integrable on its central vertical line. -/
lemma integrable_mellinValue_half :
    Integrable (fun y : ℝ => mellinValue ((1 / 2 : ℂ) + y * I)) := by
  obtain ⟨C, K, hC⟩ := DLMF.Gamma.exists_norm_Gamma_le (x := 1 / 2) (by norm_num)
  obtain ⟨D, L, hD⟩ := DLMF.Gamma.exists_norm_recip_Gamma_shift_le 1 0
  have hC0 : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hC 0)
    simpa using h
  have hD0 : 0 ≤ D := by
    have h := (norm_nonneg _).trans (hD 0)
    simpa using h
  have hcont : Continuous (fun y : ℝ => mellinValue ((1 / 2 : ℂ) + y * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    dsimp [mellinValue]
    refine ContinuousAt.div ?_ ?_ ?_
    · exact continuousAt_const.mul
        ((DLMF.Gamma.continuousAt_Gamma_of_re_pos (by norm_num)).comp (by fun_prop))
    · refine (continuousAt_const.mul ?_).mul ?_
      · exact (continuousAt_const_cpow (by norm_num)).comp (by fun_prop)
      · exact (DLMF.Gamma.continuousAt_Gamma_of_re_pos (by norm_num)).comp (by fun_prop)
    · refine mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr
        (Real.sqrt_pos.mpr Real.pi_pos).ne') ?_) ?_
      · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
      · exact Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  refine ((Real.integrable_one_add_abs_pow_mul_exp_neg
    (c := Real.pi / 3) (by positivity) (K + L)).const_mul
      ((1 / (6 * Real.sqrt Real.pi)) * C * D)).mono' hcont.aestronglyMeasurable ?_
  filter_upwards [] with y
  rw [norm_mellinValue_half]
  have hn := hC y
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hn
  have hd := hD (y / 3)
  simp only [Complex.ofReal_one, Complex.ofReal_zero, zero_add] at hd
  have hle : |y / 3| ≤ |y| := by rw [abs_div]; norm_num; linarith [abs_nonneg y]
  calc
    _ ≤ (1 / (6 * Real.sqrt Real.pi)) *
        (C * (1 + |y|) ^ K * Real.exp (-(Real.pi * |y|) / 2)) *
        (D * (1 + |y / 3|) ^ L * Real.exp (Real.pi * |y / 3| / 2)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hn (by positivity)) hd
        (norm_nonneg _) (by positivity)
    _ ≤ (1 / (6 * Real.sqrt Real.pi)) *
        (C * (1 + |y|) ^ K * Real.exp (-(Real.pi * |y|) / 2)) *
        (D * (1 + |y|) ^ L * Real.exp (Real.pi * |y / 3| / 2)) := by
      gcongr
    _ = _ := by
      rw [pow_add, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 3)]
      rw [show -(Real.pi / 3 * |y|) = -(Real.pi * |y|) / 2 +
        Real.pi * (|y| / 3) / 2 by ring, Real.exp_add]
      ring

end AiSquare

/-- `∫_{-∞}^{∞} Ai(t)³ dt = Γ(1/3)²/(4π²)` (DLMF 9.11.16). -/
@[dlmf 9.11.E16]
theorem airyAi_cube_integral  :
    HasIntegralWholeLine (fun t => airyAi t ^ 3) (Gamma (1 / 3) ^ 2 / (4 * π ^ 2)) := by
  sorry

/-- `∫_{-∞}^{∞} Ai(t)² Bi(t) dt = Γ(1/3)²/(4√3 π²)` (DLMF 9.11.17). -/
@[dlmf 9.11.E17]
theorem airyAi_sq_airyBi_integral  :
    HasIntegralWholeLine (fun t => airyAi t ^ 2 * airyBi t)
        (Gamma (1 / 3) ^ 2 / (4 * Real.sqrt 3 * π ^ 2)) := by
  sorry

/-- `∫₀^∞ Ai(t)⁴ dt = ln 3/(24π²)` (DLMF 9.11.18). -/
@[dlmf 9.11.E18]
theorem airyAi_fourth_integral  :
    (∫ t : ℝ in Ioi 0, airyAi t ^ 4) = log 3 / (24 * π ^ 2) := by
  have hmel : MellinConvergent (fun x : ℝ => airyAi x ^ 2) (1 / 2) := by
    simpa only [MellinConvergent, smul_eq_mul] using
      (airyAi_sq_mellin (α := 1 / 2) (by norm_num)).1
  have hv : Complex.VerticalIntegrable (mellin (fun x : ℝ => airyAi x ^ 2)) (1 / 2) := by
    refine AiSquare.integrable_mellinValue_half.congr (Eventually.of_forall fun y => ?_)
    change AiSquare.mellinValue _ = mellin (fun x : ℝ => airyAi x ^ 2) _
    rw [AiSquare.mellin_eq_value (by norm_num)]
    norm_num
  have hmel' : MellinConvergent (fun x : ℝ => airyAi x ^ 2) (1 - (1 / 2 : ℝ)) := by
    norm_num
    exact hmel
  have hp := integral_mul_eq_mellin_parseval (f := fun x : ℝ => airyAi x ^ 2)
    (g := fun x : ℝ => airyAi x ^ 2) (σ := 1 / 2)
    hmel' (by norm_num; exact hmel) (Or.inl hv)
  have ha : (∫ x in Ioi (0 : ℝ), airyAi x ^ 4) =
      (1 / (2 * Real.pi) : ℂ) * ∫ y : ℝ,
        (Real.sinh (Real.pi * y / 3) /
          (12 * Real.pi * y * Real.cosh (Real.pi * y)) : ℝ) := by
    convert hp using 1
    · congr 1
      funext x
      ring
    · congr 1
      rw [← integral_complex_ofReal]
      apply integral_congr_ae
      filter_upwards [volume.ae_ne (0 : ℝ)] with y hy
      rw [AiSquare.mellin_eq_value (by norm_num), AiSquare.mellin_eq_value (by norm_num),
        show (1 : ℂ) - ((1 / 2 : ℝ) + y * I) = 1 / 2 - y * I by push_cast; ring,
        show ((1 / 2 : ℝ) : ℂ) = 1 / 2 by push_cast; ring]
      rw [mul_comm (AiSquare.mellinValue ((1 / 2 : ℂ) - y * I))]
      exact (AiSquare.mellinValue_half_mul_reflected hy).symm
  rw [ha]
  have hscale : (∫ y : ℝ, Real.sinh (Real.pi * y / 3) /
      (12 * Real.pi * y * Real.cosh (Real.pi * y))) = Real.log 3 / (12 * Real.pi) := by
    have hi := MeasureTheory.Measure.integral_comp_mul_left
      (fun x : ℝ => Real.sinh (x / 3) / (x * Real.cosh x)) Real.pi
    simp only [abs_of_pos Real.pi_pos, smul_eq_mul,
      Real.integral_sinh_div_three_div_mul_cosh, abs_inv] at hi
    calc
      _ = (1 / 12) * ∫ y : ℝ,
          Real.sinh (Real.pi * y / 3) / (Real.pi * y * Real.cosh (Real.pi * y)) := by
        rw [← integral_const_mul]
        congr 1; ext y; ring
      _ = _ := by rw [hi]; ring
  rw [hscale]
  have hl : Complex.log (3 : ℂ) = (Real.log 3 : ℝ) := by
    simpa only [Complex.ofReal_ofNat] using (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 3)).symm
  rw [hl]
  push_cast
  ring

/-- `Bi'(x) ≥ Bi'(0)` for `x ≥ 0`, since `Bi'' = x Bi ≥ 0` there. -/
theorem Real.airyBiDeriv_ge {x : ℝ} (hx : 0 ≤ x) : DLMF.Airy.Real.airyBiDeriv 0 ≤
    DLMF.Airy.Real.airyBiDeriv x := by
  have hmono : MonotoneOn DLMF.Airy.Real.airyBiDeriv (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (continuous_iff_continuousAt.mpr fun t =>
        (DLMF.Airy.Real.hasDerivAt_airyBiDeriv t).continuousAt).continuousOn
      (fun t _ => (DLMF.Airy.Real.hasDerivAt_airyBiDeriv t).differentiableAt.differentiableWithinAt)
      fun t ht => ?_
    rw [interior_Ici, mem_Ioi] at ht
    rw [(DLMF.Airy.Real.hasDerivAt_airyBiDeriv t).deriv]
    exact mul_nonneg ht.le (DLMF.Airy.Real.airyBi_pos ht.le).le
  exact hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx

/-- `Bi(x) ≥ Bi(0) + Bi'(0) x` for `x ≥ 0`. -/
theorem Real.airyBi_ge {x : ℝ} (hx : 0 ≤ x) :
    DLMF.Airy.Real.airyBi 0 + DLMF.Airy.Real.airyBiDeriv 0 * x ≤ DLMF.Airy.Real.airyBi x := by
  have hmono : MonotoneOn
      (fun t => DLMF.Airy.Real.airyBi t - DLMF.Airy.Real.airyBiDeriv 0 * t) (Ici 0) := by
    have hd : ∀ t, HasDerivAt (fun t => DLMF.Airy.Real.airyBi t - DLMF.Airy.Real.airyBiDeriv 0 * t)
        (DLMF.Airy.Real.airyBiDeriv t - DLMF.Airy.Real.airyBiDeriv 0) t := fun t =>
      ((DLMF.Airy.Real.hasDerivAt_airyBi t).sub
          ((hasDerivAt_id t).const_mul _)).congr_deriv (by simp)
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt).continuousOn
      (fun t _ => (hd t).differentiableAt.differentiableWithinAt) fun t ht => ?_
    rw [interior_Ici, mem_Ioi] at ht
    rw [(hd t).deriv]
    linarith [DLMF.Airy.Real.airyBiDeriv_ge ht.le]
  have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx
  simp only [mul_zero, sub_zero] at this
  linarith

/-- `Bi(x) → ∞` as `x → +∞`. -/
theorem Real.tendsto_airyBi_atTop : Tendsto DLMF.Airy.Real.airyBi atTop atTop := by
  refine tendsto_atTop_mono' _
      (eventually_ge_atTop 0 |>.mono fun x hx => DLMF.Airy.Real.airyBi_ge hx) ?_
  exact tendsto_atTop_add_const_left _ _
      (tendsto_id.const_mul_atTop DLMF.Airy.Real.airyBiDeriv_zero_pos)

/-- `Ai(x)/Bi(x) → 0` as `x → +∞`. -/
theorem tendsto_airyAi_div_airyBi : Tendsto
    (fun x => DLMF.Airy.Real.airyAi x / DLMF.Airy.Real.airyBi x) atTop (𝓝 0) :=
  DLMF.Airy.Real.tendsto_airyAi_atTop.div_atTop DLMF.Airy.Real.tendsto_airyBi_atTop

/-- `Ai'(x)/Bi'(x) → 0` as `x → +∞`, via the Wronskian. -/
theorem tendsto_airyAiDeriv_div_airyBiDeriv :
    Tendsto (fun x => DLMF.Airy.Real.airyAiDeriv x / DLMF.Airy.Real.airyBiDeriv x) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x => DLMF.Airy.Real.airyBi x * DLMF.Airy.Real.airyBiDeriv x) atTop atTop :=
    tendsto_atTop_mono' _ (eventually_ge_atTop 0 |>.mono fun x hx =>
      mul_le_mul_of_nonneg_left (DLMF.Airy.Real.airyBiDeriv_ge hx)
          (DLMF.Airy.Real.airyBi_pos hx).le)
      (DLMF.Airy.Real.tendsto_airyBi_atTop.atTop_mul_const DLMF.Airy.Real.airyBiDeriv_zero_pos)
  have h2 := (h1.const_mul_atTop Real.pi_pos).inv_tendsto_atTop
  have h3 := tendsto_airyAi_div_airyBi.sub h2
  rw [sub_zero] at h3
  refine h3.congr' (eventually_ge_atTop 0 |>.mono fun x hx => ?_)
  have hb := (DLMF.Airy.Real.airyBi_pos hx).ne'
  have hb' := (DLMF.Airy.Real.airyBiDeriv_zero_pos.trans_le (DLMF.Airy.Real.airyBiDeriv_ge hx)).ne'
  have hW := wronskian_airyReal x
  have hπ := Real.pi_ne_zero
  simp only [Pi.inv_apply]
  field_simp
  field_simp at hW
  linear_combination hW

/-- `arctan(1/√3) = π/6`. -/
theorem arctan_recip_sqrt_three : Real.arctan (1 / Real.sqrt 3) = π / 6 := by
  rw [← Real.tan_pi_div_six,
      Real.arctan_tan (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]

/-- `Ai(0)/Bi(0) = 1/√3`. -/
theorem RealRemainders.zero_ratio : DLMF.Airy.Real.airyAi 0 / DLMF.Airy.Real.airyBi 0 = 1 /
    Real.sqrt 3 := by
  have hA : DLMF.Airy.Real.airyAi 0 = 1 / ((3 : ℝ) ^ (2 / 3 : ℝ) * Real.Gamma (2 / 3)) := by
    have h := airyAi_zero
    rw [Gamma_two_thirds_eq, ← ofReal_mul, ← ofReal_one, ← ofReal_div] at h
    simp [DLMF.Airy.Real.airyAi, h]
  have hB : DLMF.Airy.Real.airyBi 0 = 1 / ((3 : ℝ) ^ (1 / 6 : ℝ) * Real.Gamma (2 / 3)) := by
    have h := airyBi_zero
    rw [Gamma_two_thirds_eq, ← ofReal_mul, ← ofReal_one, ← ofReal_div] at h
    simp [DLMF.Airy.Real.airyBi, h]
  have hG := (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 2 / 3)).ne'
  have h1 : (3 : ℝ) ^ (1 / 6 : ℝ) = (3 : ℝ) ^ (2 / 3 : ℝ) * (Real.sqrt 3)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by norm_num), ← Real.rpow_add (by norm_num)]
    norm_num
  have h2 : (0 : ℝ) < (3 : ℝ) ^ (2 / 3 : ℝ) := by positivity
  have h3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  rw [hA, hB, h1]
  field_simp

/-- `Ai'(0)/Bi'(0) = -1/√3`. -/
theorem airyDerivReal_zero_ratio : DLMF.Airy.Real.airyAiDeriv 0 / DLMF.Airy.Real.airyBiDeriv 0 =
    -(1 / Real.sqrt 3) := by
  have hG' : Complex.Gamma (1 / 3) = ((Real.Gamma (1 / 3) : ℝ) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
  have hA : DLMF.Airy.Real.airyAiDeriv 0 = -1 / ((3 : ℝ) ^ (1 / 3 : ℝ) * Real.Gamma (1 / 3)) := by
    have h := airyAiDeriv_zero
    rw [hG', ← ofReal_mul, show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by simp, ← ofReal_div] at h
    rw [DLMF.Airy.Real.airyAiDeriv, ofReal_zero, h, ofReal_re]
  have hB : DLMF.Airy.Real.airyBiDeriv 0 = (3 : ℝ) ^ (1 / 6 : ℝ) / Real.Gamma (1 / 3) := by
    have h := airyBiDeriv_zero
    rw [hG', ← ofReal_div] at h
    simp [DLMF.Airy.Real.airyBiDeriv, h]
  have hG := (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 3)).ne'
  have h1 : (3 : ℝ) ^ (1 / 3 : ℝ) * (3 : ℝ) ^ (1 / 6 : ℝ) = Real.sqrt 3 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by norm_num)]; norm_num
  have h2 : (0 : ℝ) < (3 : ℝ) ^ (1 / 3 : ℝ) := by positivity
  have h2' : (0 : ℝ) < (3 : ℝ) ^ (1 / 6 : ℝ) := by positivity
  rw [hA, hB, ← h1]
  field_simp

/-- A primitive of `1/(Ai² + Bi²)` on `[0, ∞)`. -/
theorem hasDerivAt_arctan_airy_ratio {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun t => -π * Real.arctan (DLMF.Airy.Real.airyAi t / DLMF.Airy.Real.airyBi t))
      (1 / (DLMF.Airy.Real.airyAi x ^ 2 + DLMF.Airy.Real.airyBi x ^ 2)) x := by
  have hb := (DLMF.Airy.Real.airyBi_pos hx).ne'
  have h := (((DLMF.Airy.Real.hasDerivAt_airyAi x).div (DLMF.Airy.Real.hasDerivAt_airyBi x)
      hb).arctan).const_mul (-π)
  refine h.congr_deriv ?_
  have hW := wronskian_airyReal x
  have hπ := Real.pi_ne_zero
  have hM := (airyModulusSq_pos x).ne'
  simp only [Pi.div_apply]
  field_simp
  field_simp at hW
  linear_combination (DLMF.Airy.Real.airyAi x ^ 2 + DLMF.Airy.Real.airyBi x ^ 2) * hW

/-- A primitive of `x/(Ai'² + Bi'²)` on `[0, ∞)`. -/
theorem hasDerivAt_arctan_airyDeriv_ratio {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun t => π *
        Real.arctan (DLMF.Airy.Real.airyAiDeriv t / DLMF.Airy.Real.airyBiDeriv t))
      (x / (DLMF.Airy.Real.airyAiDeriv x ^ 2 + DLMF.Airy.Real.airyBiDeriv x ^ 2)) x := by
  have hb := (DLMF.Airy.Real.airyBiDeriv_zero_pos.trans_le (DLMF.Airy.Real.airyBiDeriv_ge hx)).ne'
  have h := (((DLMF.Airy.Real.hasDerivAt_airyAiDeriv x).div
      (DLMF.Airy.Real.hasDerivAt_airyBiDeriv x)
      hb).arctan).const_mul π
  refine h.congr_deriv ?_
  have hW := wronskian_airyReal x
  have hπ := Real.pi_ne_zero
  have hN := (airyDerivModulusSq_pos x).ne'
  simp only [Pi.div_apply]
  field_simp
  field_simp at hW
  linear_combination (x *
      (DLMF.Airy.Real.airyAiDeriv x ^ 2 + DLMF.Airy.Real.airyBiDeriv x ^ 2)) * hW

/-- `∫₀^∞ dt/(Ai(t)² + Bi(t)²) = ∫₀^∞ t dt/(Ai'(t)² + Bi'(t)²) = π²/6` (DLMF 9.11.19). -/
@[dlmf 9.11.E19]
theorem airy_modulus_reciprocal_integrals  :
    (∫ t : ℝ in Ioi 0, 1 / (airyAi t ^ 2 + airyBi t ^ 2)) = (π : ℂ) ^ 2 / 6 ∧
      (∫ t : ℝ in Ioi 0, (t : ℂ) / (airyAiDeriv t ^ 2 + airyBiDeriv t ^ 2)) = (π : ℂ) ^ 2 / 6 := by
  have e1 : (fun t : ℝ => 1 / (airyAi t ^ 2 + airyBi t ^ 2)) =
      fun t : ℝ => ((1 / (DLMF.Airy.Real.airyAi t ^ 2 + DLMF.Airy.Real.airyBi t ^ 2) : ℝ) : ℂ) := by
    funext t; rw [airyAi_ofReal_eq, airyBi_ofReal_eq]; push_cast; ring
  have e2 : (fun t : ℝ => (t : ℂ) / (airyAiDeriv t ^ 2 + airyBiDeriv t ^ 2)) =
      fun t : ℝ => ((t / (DLMF.Airy.Real.airyAiDeriv t ^ 2 +
          DLMF.Airy.Real.airyBiDeriv t ^ 2) : ℝ) : ℂ) := by
    funext t; rw [airyAiDeriv_ofReal_eq, airyBiDeriv_ofReal_eq]; push_cast; ring
  rw [e1, e2, _root_.integral_complex_ofReal, _root_.integral_complex_ofReal]
  have i1 := integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0)
    (fun x hx => hasDerivAt_arctan_airy_ratio hx)
    (fun x _ => (one_div_pos.mpr (airyModulusSq_pos x)).le)
    (by simpa [Real.arctan_zero] using
      ((Real.continuous_arctan.tendsto 0).comp tendsto_airyAi_div_airyBi).const_mul (-π))
  have i2 := integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0)
    (fun x hx => hasDerivAt_arctan_airyDeriv_ratio hx)
    (fun x hx => div_nonneg (le_of_lt hx) (airyDerivModulusSq_pos x).le)
    (by simpa [Real.arctan_zero] using
      ((Real.continuous_arctan.tendsto 0).comp tendsto_airyAiDeriv_div_airyBiDeriv).const_mul π)
  rw [i1, i2, RealRemainders.zero_ratio, airyDerivReal_zero_ratio, Real.arctan_neg,
    arctan_recip_sqrt_three]
  constructor <;> push_cast <;> ring

end DLMF.Airy
