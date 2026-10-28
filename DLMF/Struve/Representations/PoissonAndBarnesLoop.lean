/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.YIntegralRep
public import TauCeti.Analysis.Contour.WorkedExamples.HalfDisc.SineIntegral
public import DLMFMathlib.Analysis.Integral.Improper
public import DLMF.Struve.BarnesTools

/-!
# Poisson integrals and Struve Barnes loops

Poisson and sine-transform representations and the convergent Barnes loop for the modified
Struve function.

Source references and common attribution are retained in
`DLMF.Struve.Representations`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Struve

open DLMF.Bessel

/-- Identity under the stated parameter and domain assumptions: `struveH ν z =
2*(z/2)^ν/(Real.sqrt π*Gamma (ν+1/2)) * ∫ θ : ℝ in 0..π/2, sin (z*Real.cos θ)*(Real.sin θ :
ℂ)^(2*ν)`. -/
@[dlmf 11.5.E1]
theorem struveH_trig_integral {ν : ℂ} (hν : -1/2 < ν.re) {z : ℂ} (hz : z ∈ slitPlane) :
    struveH ν z = 2*(z/2)^ν/(Real.sqrt π*Gamma (ν+1/2)) * ∫ θ : ℝ in 0..π/2, sin (z*Real.cos θ)*(Real.sin θ : ℂ)^(2*ν) := by
  rw [struveH_eq_poisson hν (slitPlane_ne_zero hz),
    integral_poissonWeight_eq_trig ν (fun t => sin (z*t))]

/-- Identity under the stated parameter and domain assumptions: `struveL ν z =
2*(z/2)^ν/(Real.sqrt π*Gamma (ν+1/2)) * ∫ θ : ℝ in 0..π/2, sinh (z*Real.cos θ)*(Real.sin θ :
ℂ)^(2*ν)`. -/
@[dlmf 11.5.E6]
theorem struveL_trig_integral {ν : ℂ} (hν : -1/2 < ν.re) {z : ℂ} (hz : z ∈ slitPlane) :
    struveL ν z = 2*(z/2)^ν/(Real.sqrt π*Gamma (ν+1/2)) * ∫ θ : ℝ in 0..π/2, sinh (z*Real.cos θ)*(Real.sin θ : ℂ)^(2*ν) := by
  rw [struveL_eq_poisson hν (slitPlane_ne_zero hz),
    integral_poissonWeight_eq_trig ν (fun t => sinh (z*t))]

/-- Identity under the stated parameter and domain assumptions: `struveH ν z =
2*(z/2)^ν/(Real.sqrt π*Gamma (ν+1/2)) * ∫ t : ℝ in 0..1, (1-t^2:ℂ)^(ν-1/2)*sin (z*t)`. -/
@[dlmf 11.5.E1]
theorem struveH_integral {ν : ℂ} (hν : -1/2 < ν.re) {z : ℂ} (hz : z ∈ slitPlane) :
    struveH ν z = 2*(z/2)^ν/(Real.sqrt π*Gamma (ν+1/2)) * ∫ t : ℝ in 0..1, (1-t^2:ℂ)^(ν-1/2)*sin (z*t) := by
  exact struveH_eq_poisson hν (slitPlane_ne_zero hz)

/-- Laplace representation retaining the reciprocal-gamma prefactor at exceptional orders. -/
@[dlmf 11.5.E2]
theorem struveK_laplace (ν : ℂ) {z : ℂ} (hz : 0 < z.re) :
    HasIntegralAtTop (fun t : ℝ => 2*(z/2)^ν/(Real.sqrt π*Gamma (ν+1/2))*exp (-z*t)*(1+t^2:ℂ)^(ν-1/2)) 0 (struveK ν z) := by
  -- `DLMF.Bessel.struveK_eq_besselYLaplace` (contour rotation plus downward induction in `ν`)
  have h := intervalIntegral_tendsto_integral_Ioi 0
    ((integrableOn_yLaplaceKernel ν hz).const_mul (2*(z/2)^ν/(Real.sqrt π*Gamma (ν+1/2))))
    tendsto_id
  rw [integral_const_mul, show 2*(z/2)^ν/(Real.sqrt π*Gamma (ν+1/2)) *
    ∫ a in Ioi (0:ℝ), yLaplaceKernel ν z a = besselYLaplace ν z from rfl,
    ← struveK_eq_besselYLaplace ν hz] at h
  refine h.congr fun R => ?_
  simp only [id, yLaplaceKernel, mul_assoc]

/-- The real hyperbolic sine tends to infinity. -/
theorem tendsto_real_sinh_atTop : Tendsto Real.sinh atTop atTop :=
  tendsto_atTop_mono' atTop (eventually_ge_atTop 0 |>.mono fun _ hx => Real.self_le_sinh_iff.mpr hx)
    tendsto_id

/-- Horizontal-ray integral representation: `HasIntegralAtTop (fun t : ℝ => 2/π*exp (-z*Real.sinh
t)) 0 (struveK 0 z)`. -/
@[dlmf 11.5.E3]
theorem struveK_zero_laplace {z : ℂ} (hz : 0 < z.re) :
    HasIntegralAtTop (fun t : ℝ => 2/π*exp (-z*Real.sinh t)) 0 (struveK 0 z) := by
  -- DLMF 11.5.2 at `ν = 0` with the substitution `t = sinh u`
  set c : ℂ := 2*(z/2)^(0:ℂ)/(Real.sqrt π*Gamma (0+1/2))
  have hc : c = (2/π : ℂ) := by
    simp only [c]
    rw [cpow_zero, zero_add, DLMF.Confluent.Gamma_one_half_eq_sqrt, ← ofReal_mul,
      Real.mul_self_sqrt Real.pi_pos.le]; ring
  have h := intervalIntegral_tendsto_integral_Ioi 0
    ((integrableOn_yLaplaceKernel 0 hz).const_mul c) tendsto_real_sinh_atTop
  rw [integral_const_mul, show c * ∫ a in Ioi (0:ℝ), yLaplaceKernel 0 z a = besselYLaplace 0 z
    from rfl, ← struveK_eq_besselYLaplace 0 hz] at h
  refine h.congr fun R => ?_
  have hsub := intervalIntegral.integral_deriv_smul_comp (a := 0) (b := R) (f := Real.sinh)
    (f' := Real.cosh) (g := fun t => c * yLaplaceKernel 0 z t)
    (fun x _ => Real.hasDerivAt_sinh x) Real.continuous_cosh.continuousOn
    ((continuous_yLaplaceKernel 0 z).const_mul c)
  rw [Real.sinh_zero] at hsub
  rw [← hsub]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [Function.comp, yLaplaceKernel, hc, real_smul]
  have hch : 0 < Real.cosh u := Real.cosh_pos u
  have h1 : (1 + ((Real.sinh u : ℝ) : ℂ) ^ 2) ^ ((0:ℂ) - 1/2) = ((Real.cosh u)⁻¹ : ℝ) := by
    rw [show (1 + ((Real.sinh u : ℝ) : ℂ) ^ 2) = ((Real.cosh u ^ 2 : ℝ) : ℂ) by
      rw [Real.cosh_sq]; push_cast; ring,
      show ((0:ℂ) - 1/2) = ((-1/2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow (sq_nonneg _), ← Real.rpow_natCast, ← Real.rpow_mul hch.le]
    norm_num [Real.rpow_neg_one]
  have h2 : ((Real.cosh u : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hch.ne'
  rw [h1, ofReal_inv]; field_simp

/-- Identity under the stated parameter and domain assumptions: `struveM ν z =
-2*(z/2)^ν/(Real.sqrt π*Gamma (ν+1/2)) * ∫ t : ℝ in 0..1, exp (-z*t)*(1-t^2:ℂ)^(ν-1/2)`. -/
@[dlmf 11.5.E4]
theorem struveM_integral {ν : ℂ} (hν : -1/2 < ν.re) {z : ℂ} (hz : z ∈ slitPlane) :
    struveM ν z = -2*(z/2)^ν/(Real.sqrt π*Gamma (ν+1/2)) * ∫ t : ℝ in 0..1, exp (-z*t)*(1-t^2:ℂ)^(ν-1/2) := by
  exact struveM_eq_poisson hν hz

/-- Two continuous functions on `ℂ` that agree on the slit plane agree everywhere. -/
theorem eq_of_continuous_of_eqOn_slitPlane {f g : ℂ → ℂ} (hf : Continuous f)
    (hg : Continuous g) (h : ∀ z ∈ slitPlane, f z = g z) (z : ℂ) : f z = g z := by
  have hd : Dense slitPlane := by
    intro z
    by_cases hz : z ∈ slitPlane
    · exact subset_closure hz
    · have ht : Tendsto (fun n : ℕ => z + I*((1:ℂ)/(n+1))) atTop (𝓝 z) := by
        have : Tendsto (fun n : ℕ => (1:ℂ)/(n+1)) atTop (𝓝 0) := by
          simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)
        simpa using (this.const_mul I).const_add z
      refine mem_closure_of_tendsto ht (Eventually.of_forall fun n => ?_)
      have hzim : z.im = 0 := by
        by_contra hne; exact hz (Or.inr hne)
      apply Or.inr
      have : ((1:ℂ)/(n+1)) = ((1/(n+1:ℝ) : ℝ) : ℂ) := by push_cast; ring
      rw [this]
      simp only [add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, hzim]
      positivity
  exact congrFun (hf.ext_on hd hg h) z

/-- `I₀` is entire. -/
theorem continuous_besselI_zero : Continuous (besselI 0) := by
  have he : besselI 0 = fun z => regularizedHGFun (∅ : Multiset ℂ) {0+1} (z^2/4) := by
    funext z; rw [besselI, cpow_zero, one_mul]
  rw [he]
  have hF : Differentiable ℂ (regularizedHGFun (∅ : Multiset ℂ) {(0:ℂ)+1}) :=
    fun w => (analyticAt_regularizedHGFun_of_card_le (by simp) w).differentiableAt
  exact (hF.comp (by fun_prop)).continuous

/-- Identity under the stated parameter and domain assumptions: `struveM 0 z = -2/π * ∫ θ : ℝ in
0..π/2, exp (-z*Real.cos θ)`. -/
@[dlmf 11.5.E5]
theorem struveM_zero_integral (z : ℂ) :
    struveM 0 z = -2/π * ∫ θ : ℝ in 0..π/2, exp (-z*Real.cos θ) := by
  refine eq_of_continuous_of_eqOn_slitPlane (f := struveM 0)
    (g := fun z => -2/π * ∫ θ : ℝ in 0..π/2, exp (-z*Real.cos θ)) ?_ ?_ (fun z hz => ?_) z
  · have h1 : Continuous (struveL 0) := by
      simpa using (struveL_nat_entire 0).continuous
    exact h1.sub continuous_besselI_zero
  · refine continuous_const.mul ?_
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (by fun_prop) _ _
  · rw [struveM_eq_poisson (by norm_num) hz]
    have := integral_poissonWeight_eq_trig 0 (fun t => exp (-z*t))
    rw [show (∫ t : ℝ in 0..1, exp (-z*t)*(1-t^2:ℂ)^((0:ℂ)-1/2)) =
      ∫ t : ℝ in 0..1, (1-(t:ℂ)^2)^((0:ℂ)-1/2) * exp (-z*t) from
      intervalIntegral.integral_congr fun t _ => by ring, this]
    simp only [mul_zero, cpow_zero, mul_one, zero_add]
    rw [Complex.Gamma_one_half_eq]
    have hs : (π:ℂ)^(1/2:ℂ) = (Real.sqrt π : ℂ) := by
      rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]; push_cast; ring_nf
    have hp : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
      rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
    rw [hs, hp]

/-! ### The sine transform of `(1+t²)^{ν-1/2}` (DLMF 11.5.7) -/
/-- `(±i x/2)^w = (x/2)^w e^{±iπw/2}` for `x > 0`. -/
theorem struveFour_cpow_I_mul {x : ℝ} (hx : 0 < x) (w : ℂ) :
    (I * x / 2) ^ w = ((x : ℂ) / 2) ^ w * exp (I * w * π / 2) := by
  have hx2 : ((x : ℂ) / 2) ≠ 0 := by
    exact div_ne_zero (ofReal_ne_zero.mpr hx.ne') two_ne_zero
  have harg : arg ((x : ℂ) / 2) = 0 := by
    rw [show ((x : ℂ) / 2) = ((x / 2 : ℝ) : ℂ) by push_cast; ring]
    exact arg_ofReal_of_nonneg (by positivity)
  have hc := DLMF.Confluent.cpow_mul_exp_mul_I hx2 (α := π / 2)
    (by rw [harg]; linarith [Real.pi_pos]) (by rw [harg]; linarith [Real.pi_pos]) w
  rw [exp_pi_div_two_mul_I'] at hc
  rw [show I * (x : ℂ) / 2 = (x : ℂ) / 2 * I by ring, hc]
  congr 2
  push_cast; ring

/-- `(-i x/2)^w = (x/2)^w e^{-iπw/2}` for `x > 0`. -/
theorem struveFour_cpow_neg_I_mul {x : ℝ} (hx : 0 < x) (w : ℂ) :
    (-I * x / 2) ^ w = ((x : ℂ) / 2) ^ w * exp (-(I * w * π / 2)) := by
  have hx2 : ((x : ℂ) / 2) ≠ 0 := by
    exact div_ne_zero (ofReal_ne_zero.mpr hx.ne') two_ne_zero
  have harg : arg ((x : ℂ) / 2) = 0 := by
    rw [show ((x : ℂ) / 2) = ((x / 2 : ℝ) : ℂ) by push_cast; ring]
    exact arg_ofReal_of_nonneg (by positivity)
  have hc := DLMF.Confluent.cpow_mul_exp_mul_I hx2 (α := -(π / 2))
    (by rw [harg]; linarith [Real.pi_pos]) (by rw [harg]; linarith [Real.pi_pos]) w
  rw [exp_neg_pi_div_two_mul_I'] at hc
  rw [show -I * (x : ℂ) / 2 = (x : ℂ) / 2 * -I by ring, hc]
  congr 2
  push_cast; ring

/-- `(x/2)^ν (i x/2)^{-ν} = e^{-iπν/2}`. -/
theorem struveFour_ratio_I {x : ℝ} (hx : 0 < x) (ν : ℂ) :
    ((x : ℂ) / 2) ^ ν * (I * x / 2) ^ (-ν) = exp (-(I * ν * π / 2)) := by
  have hx2 : ((x : ℂ) / 2) ≠ 0 := div_ne_zero (ofReal_ne_zero.mpr hx.ne') two_ne_zero
  rw [struveFour_cpow_I_mul hx, cpow_neg, ← mul_assoc, mul_inv_cancel₀ (by
    rw [Ne, cpow_eq_zero_iff]; tauto)]
  ring_nf

/-- `(x/2)^ν (-i x/2)^{-ν} = e^{iπν/2}`. -/
theorem struveFour_ratio_neg_I {x : ℝ} (hx : 0 < x) (ν : ℂ) :
    ((x : ℂ) / 2) ^ ν * (-I * x / 2) ^ (-ν) = exp (I * ν * π / 2) := by
  have hx2 : ((x : ℂ) / 2) ≠ 0 := div_ne_zero (ofReal_ne_zero.mpr hx.ne') two_ne_zero
  rw [struveFour_cpow_neg_I_mul hx, cpow_neg, ← mul_assoc, mul_inv_cancel₀ (by
    rw [Ne, cpow_eq_zero_iff]; tauto)]
  ring_nf

/-- The Struve `H` series at `i x` is the Struve `L` series at `x`. -/
theorem struveFour_core_I (ν : ℂ) (x : ℝ) : struveHCore ν (I * x) = struveLCore ν x := by
  rw [struveHCore, struveLCore]
  refine tsum_congr fun n => ?_
  rw [pow_mul, pow_mul, show (I * x / 2) ^ 2 = -(((x : ℂ) / 2) ^ 2) by ring_nf; rw [I_sq]; ring,
    neg_pow (((x : ℂ) / 2) ^ 2), ← mul_assoc, ← mul_pow]
  norm_num

/-- The Struve `H` series at `-i x` is the Struve `L` series at `x`. -/
theorem struveFour_core_neg_I (ν : ℂ) (x : ℝ) : struveHCore ν (-I * x) = struveLCore ν x := by
  rw [struveHCore, struveLCore]
  refine tsum_congr fun n => ?_
  rw [pow_mul, pow_mul, show (-I * x / 2) ^ 2 = -(((x : ℂ) / 2) ^ 2) by ring_nf; rw [I_sq]; ring,
    neg_pow (((x : ℂ) / 2) ^ 2), ← mul_assoc, ← mul_pow]
  norm_num

/-- `H_ν(i x) = i e^{iπν/2} L_ν(x)` for `x > 0`. -/
theorem struveFour_H_I {x : ℝ} (hx : 0 < x) (ν : ℂ) :
    struveH ν (I * x) = I * exp (I * ν * π / 2) * struveL ν x := by
  rw [struveH, struveL, struveFour_core_I, struveFour_cpow_I_mul hx]
  rw [show I * (ν + 1) * π / 2 = I * ν * π / 2 + π / 2 * I by ring, exp_add,
    show (π / 2 * I : ℂ) = ((π / 2 : ℝ) : ℂ) * I by push_cast; ring, exp_pi_div_two_mul_I']
  ring

/-- `H_ν(-i x) = -i e^{-iπν/2} L_ν(x)` for `x > 0`. -/
theorem struveFour_H_neg_I {x : ℝ} (hx : 0 < x) (ν : ℂ) :
    struveH ν (-I * x) = -I * exp (-(I * ν * π / 2)) * struveL ν x := by
  rw [struveH, struveL, struveFour_core_neg_I, struveFour_cpow_neg_I_mul hx]
  rw [show -(I * (ν + 1) * π / 2) = -(I * ν * π / 2) + (-(π / 2) : ℝ) * I by push_cast; ring,
    exp_add, exp_neg_pi_div_two_mul_I']
  ring

/-- `J_μ(i x) = e^{iπμ/2} I_μ(x)` for `x > 0`. -/
theorem struveFour_J_I {x : ℝ} (hx : 0 < x) (μ : ℂ) :
    besselJ μ (I * x) = exp (I * μ * π / 2) * besselI μ x := by
  have hz : I * (x : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hx.ne')
  have harg : arg (I * (x : ℂ)) = π / 2 := by rw [mul_comm, arg_real_mul I hx, arg_I]
  have h := besselI_neg_I_mul hz (by rw [harg]; linarith [Real.pi_pos]) μ
  rw [show -I * (I * (x : ℂ)) = x by ring_nf; rw [I_sq]; ring] at h
  rw [h, ← mul_assoc, ← exp_add]
  simp

/-- `J_μ(-i x) = e^{-iπμ/2} I_μ(x)` for `x > 0`. -/
theorem struveFour_J_neg_I {x : ℝ} (hx : 0 < x) (μ : ℂ) :
    besselJ μ (-I * x) = exp (-(I * μ * π / 2)) * besselI μ x := by
  have hz : -I * (x : ℂ) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (ofReal_ne_zero.mpr hx.ne')
  have harg : arg (-I * (x : ℂ)) = -(π / 2) := by rw [mul_comm, arg_real_mul _ hx, arg_neg_I]
  have h := besselI_I_mul hz (by rw [harg]; linarith [Real.pi_pos]) μ
  rw [show I * (-I * (x : ℂ)) = x by ring_nf; rw [I_sq]; ring] at h
  rw [h, ← mul_assoc, ← exp_add]
  simp

/-- `i x` lies in the slit plane for `x > 0`. -/
theorem struveFour_mem_slitPlane_I {x : ℝ} (hx : 0 < x) : I * (x : ℂ) ∈ slitPlane := by
  right; simp [hx.ne']

/-- `-i x` lies in the slit plane for `x > 0`. -/
theorem struveFour_mem_slitPlane_neg_I {x : ℝ} (hx : 0 < x) : -I * (x : ℂ) ∈ slitPlane := by
  right; simp [hx.ne']

/-- `e^{iπν/2} Y_ν(-ix) - e^{-iπν/2} Y_ν(ix) = -2i I_{-ν}(x)` for all orders `ν`. -/
theorem struveFour_Y {x : ℝ} (hx : 0 < x) (ν : ℂ) :
    exp (I * ν * π / 2) * besselY ν (-I * x) - exp (-(I * ν * π / 2)) * besselY ν (I * x) =
      -2 * I * besselI (-ν) x := by
  refine DLMF.Confluent.eq_of_continuousAt_of_integerComplement
    (f := fun μ => exp (I * μ * π / 2) * besselY μ (-I * x) -
      exp (-(I * μ * π / 2)) * besselY μ (I * x))
    (g := fun μ => -2 * I * besselI (-μ) x) ?_ ?_ (fun c hc => ?_)
  · exact ((by fun_prop : Continuous fun μ : ℂ => exp (I * μ * π / 2)).continuousAt.mul
      (continuousAt_besselY_order (fun μ => μ) continuous_id ν
        (struveFour_mem_slitPlane_neg_I hx))).sub
      ((by fun_prop : Continuous fun μ : ℂ => exp (-(I * μ * π / 2))).continuousAt.mul
      (continuousAt_besselY_order (fun μ => μ) continuous_id ν (struveFour_mem_slitPlane_I hx)))
  · exact continuousAt_const.mul (continuousAt_besselI_order (fun μ => -μ) continuous_neg ν
      (by simpa using ofReal_mem_slitPlane.mpr hx))
  · have hc' := DLMF.Confluent.forall_of_mem_integerComplement hc
    have hs : sin (c * π) ≠ 0 := by
      rw [Ne, Complex.sin_eq_zero_iff]
      rintro ⟨k, hk⟩
      exact hc' k (by
        have := Real.pi_pos
        have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr this.ne'
        field_simp at hk; exact hk)
    rw [besselY_eq_of_not_int hc', besselY_eq_of_not_int hc', besselD, besselD,
      struveFour_J_I hx, struveFour_J_neg_I hx, struveFour_J_I hx, struveFour_J_neg_I hx]
    have hsin : sin (c * π) = (exp (I * c * π) - exp (-(I * c * π))) / (2 * I) := by
      rw [eq_div_iff (mul_ne_zero two_ne_zero I_ne_zero), Complex.sin]; ring_nf; rw [I_sq]; ring_nf
    rw [hsin]
    have e1 : exp (I * c * π) = exp (I * c * π / 2) * exp (I * c * π / 2) := by
      rw [← exp_add]; ring_nf
    have e2 : exp (-(I * c * π)) = exp (-(I * c * π / 2)) * exp (-(I * c * π / 2)) := by
      rw [← exp_add]; ring_nf
    have e3 : exp (I * c * π / 2) * exp (-(I * c * π / 2)) = 1 := by
      rw [← exp_add]; simp
    rw [e1, e2]
    rw [show -(I * -c * π / 2) = I * c * π / 2 by ring, show I * -c * π / 2 = -(I * c * π / 2) by ring]
    set E := exp (I * c * π / 2)
    set F := exp (-(I * c * π / 2))
    have hd : E * E - F * F ≠ 0 := by
      intro h; apply hs; rw [hsin, e1, e2, h]; simp
    have hd2 : E ^ 2 - F ^ 2 ≠ 0 := by rwa [sq, sq]
    field_simp
    ring_nf

/-- The boundary value of the regularized sine transform, DLMF 11.5.7. -/
theorem struveFour_value {x : ℝ} (hx : 0 < x) (ν : ℂ) :
    1 / (2 * I) * (((x : ℂ) / 2) ^ ν * (-I * x / 2) ^ (-ν) * struveK ν (-I * x) -
      ((x : ℂ) / 2) ^ ν * (I * x / 2) ^ (-ν) * struveK ν (I * x)) =
      besselI (-ν) x - struveL ν x := by
  rw [struveFour_ratio_neg_I hx, struveFour_ratio_I hx, struveK, struveK, struveFour_H_I hx,
    struveFour_H_neg_I hx]
  have hY := struveFour_Y hx ν
  have e3 : exp (I * ν * π / 2) * exp (-(I * ν * π / 2)) = 1 := by rw [← exp_add]; simp
  set Ym := besselY ν (-I * x)
  set Yp := besselY ν (I * x)
  field_simp
  linear_combination (-(1:ℂ)) * hY + (-2 * I * struveL ν x) * e3

/-- `1 + t²` as a real cast. -/
theorem struveFour_one_add_sq (t : ℝ) : (1 + (t : ℂ) ^ 2) = ((1 + t ^ 2 : ℝ) : ℂ) := by
  push_cast; ring

/-- `1 + t²` lies in the slit plane. -/
theorem struveFour_mem_slitPlane (t : ℝ) : (1 + (t : ℂ) ^ 2) ∈ slitPlane := by
  rw [struveFour_one_add_sq]; exact ofReal_mem_slitPlane.mpr (by positivity)

/-- `t ↦ (1+t²)^w` is continuous. -/
theorem struveFour_continuous_cpow (w : ℂ) : Continuous fun t : ℝ => (1 + (t : ℂ) ^ 2) ^ w :=
  (by fun_prop : Continuous fun t : ℝ => 1 + (t : ℂ) ^ 2).cpow continuous_const
    struveFour_mem_slitPlane

/-- `‖(1+t²)^w‖ = (1+t²)^{re w}`. -/
theorem struveFour_norm_cpow (w : ℂ) (t : ℝ) : ‖(1 + (t : ℂ) ^ 2) ^ w‖ = (1 + t ^ 2) ^ w.re := by
  rw [struveFour_one_add_sq, norm_cpow_eq_rpow_re_of_pos (by positivity)]

/-- Derivative of `t ↦ (1+t²)^w`. -/
theorem struveFour_hasDerivAt_cpow (w : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => (1 + (t : ℂ) ^ 2) ^ w)
      (w * (1 + (t : ℂ) ^ 2) ^ (w - 1) * (2 * t)) t := by
  have h1 : HasDerivAt (fun z : ℂ => 1 + z ^ 2) (2 * (t : ℂ)) (t : ℂ) := by
    simpa using ((hasDerivAt_pow 2 (t : ℂ)).const_add 1)
  have h2 := (h1.cpow_const (c := w) (struveFour_mem_slitPlane t)).comp_ofReal
  simpa using h2

/-- `(1+t²)^s → 0` as `t → ∞` for `s < 0`. -/
theorem struveFour_tendsto_rpow {s : ℝ} (hs : s < 0) :
    Tendsto (fun t : ℝ => (1 + t ^ 2) ^ s) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (y := -s) (by linarith)).comp
    (tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop (two_ne_zero (α := ℕ))))
  simpa [Function.comp_def] using h

/-- `t (1+t²)^{s-1}` is integrable on `(0, ∞)` for `s < 0`. -/
theorem struveFour_integrableOn {s : ℝ} (hs : s < 0) :
    IntegrableOn (fun t : ℝ => t * (1 + t ^ 2) ^ (s - 1)) (Ioi 0) := by
  have hG : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => -(1 + t ^ 2) ^ s)
      (-(2 * s) * (t * (1 + t ^ 2) ^ (s - 1))) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
      simpa using ((hasDerivAt_pow 2 t).const_add 1)
    have h2 := (h1.rpow_const (p := s) (Or.inl (by positivity))).neg
    convert h2 using 1; ring
  have hi := integrableOn_Ioi_deriv_of_nonneg (g := fun t : ℝ => -(1 + t ^ 2) ^ s)
    (l := -0) ((by fun_prop : Continuous fun t : ℝ => 1 + t ^ 2).rpow_const
      (fun _ => Or.inl (by positivity))).neg.continuousWithinAt hG
    (fun t ht => mul_nonneg (by linarith) (mul_nonneg (le_of_lt ht) (by positivity)))
    (struveFour_tendsto_rpow hs).neg
  have := hi.const_mul (-(2 * s))⁻¹
  have hs0 : s ≠ 0 := hs.ne
  refine IntegrableOn.congr_fun this (fun t _ => ?_) measurableSet_Ioi
  field_simp

/-- Existence of the improper integral `∫₀^∞ (1+t²)^a sin(xt) dt` for `re a < 0`. -/
theorem struveFour_exists {a : ℂ} (ha : a.re < 0) {x : ℝ} (hx : 0 < x) :
    ∃ L, Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R, (1 + (t : ℂ) ^ 2) ^ a * Real.sin (x * t))
      atTop (𝓝 L) := by
  set u' : ℝ → ℂ := fun t => a * (1 + (t : ℂ) ^ 2) ^ (a - 1) * (2 * t)
  set v : ℝ → ℂ := fun t => -(Real.cos (x * t) : ℂ) / x
  have hv : ∀ t : ℝ, HasDerivAt v (Real.sin (x * t) : ℂ) t := by
    intro t
    have h := (((Real.hasDerivAt_cos (x * t)).comp t
      ((hasDerivAt_id t).const_mul x)).ofReal_comp).neg.div_const (x : ℂ)
    have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
    convert h using 1
    · funext y; simp [v]
    · push_cast; field_simp
  have hu'c : Continuous u' := by
    have := struveFour_continuous_cpow (a - 1)
    fun_prop
  have hibp : ∀ X : ℝ, ∫ t in (0 : ℝ)..X, (1 + (t : ℂ) ^ 2) ^ a * Real.sin (x * t) =
      (1 + (X : ℂ) ^ 2) ^ a * v X - (1 + ((0 : ℝ) : ℂ) ^ 2) ^ a * v 0 -
        ∫ t in (0 : ℝ)..X, u' t * v t := by
    intro X
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (fun t _ => struveFour_hasDerivAt_cpow a t) (fun t _ => hv t)
      (hu'c.intervalIntegrable _ _)
      ((continuous_ofReal.comp (Real.continuous_sin.comp (continuous_const.mul continuous_id)))
        |>.intervalIntegrable _ _)
  have hgi : IntegrableOn (fun t => u' t * v t) (Ioi 0) := by
    refine ((struveFour_integrableOn ha).const_mul (2 * ‖a‖ / x)).mono' ?_ ?_
    · exact (hu'c.mul (by fun_prop)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simp only [u', v, norm_mul, norm_div, norm_neg, norm_real, Real.norm_eq_abs,
        struveFour_norm_cpow, norm_ofNat]
      have hc : |Real.cos (x * t)| ≤ 1 := Real.abs_cos_le_one _
      rw [abs_of_pos hx, abs_of_pos (show (0:ℝ) < t from ht)]
      have hre : (a - 1).re = a.re - 1 := by simp
      rw [hre]
      have h0 : 0 ≤ ‖a‖ * (1 + t ^ 2) ^ (a.re - 1) * (2 * t) / x := by
        have := le_of_lt (show (0:ℝ) < t from ht); positivity
      calc ‖a‖ * (1 + t ^ 2) ^ (a.re - 1) * (2 * t) * (|Real.cos (x * t)| / x)
          ≤ ‖a‖ * (1 + t ^ 2) ^ (a.re - 1) * (2 * t) * (1 / x) := by
            gcongr
            have := le_of_lt (show (0:ℝ) < t from ht); positivity
        _ = 2 * ‖a‖ / x * (t * (1 + t ^ 2) ^ (a.re - 1)) := by ring
  have hb : Tendsto (fun X : ℝ => (1 + (X : ℂ) ^ 2) ^ a * v X) atTop (𝓝 0) := by
    have hlim : Tendsto (fun X : ℝ => (1 + X ^ 2) ^ a.re / x) atTop (𝓝 0) := by
      simpa using (struveFour_tendsto_rpow ha).div_const x
    refine squeeze_zero_norm (fun X => ?_) hlim
    simp only [v, norm_mul, norm_div, norm_neg, norm_real, Real.norm_eq_abs, struveFour_norm_cpow]
    rw [abs_of_pos hx]
    have hc : |Real.cos (x * X)| ≤ 1 := Real.abs_cos_le_one _
    calc (1 + X ^ 2) ^ a.re * (|Real.cos (x * X)| / x) ≤ (1 + X ^ 2) ^ a.re * (1 / x) := by
          gcongr
      _ = _ := by ring
  refine ⟨0 - (1 + ((0 : ℝ) : ℂ) ^ 2) ^ a * v 0 - ∫ t in Ioi 0, u' t * v t, ?_⟩
  have := (hb.sub (tendsto_const_nhds (x := (1 + ((0 : ℝ) : ℂ) ^ 2) ^ a * v 0))).sub (intervalIntegral_tendsto_integral_Ioi 0 hgi tendsto_id)
  exact this.congr fun X => (hibp X).symm

/-- The regularized integrand splits into two Laplace kernels. -/
theorem struveFour_regularized_eq (ν C : ℂ) (x ε t : ℝ) :
    Real.exp (-(ε * t)) • (C * (1 + (t : ℂ) ^ 2) ^ (ν - 1 / 2) * Real.sin (x * t)) =
      C / (2 * I) * (yLaplaceKernel ν (ε - I * x) t - yLaplaceKernel ν (ε + I * x) t) := by
  rw [yLaplaceKernel, yLaplaceKernel, Complex.real_smul, ofReal_exp, ofReal_sin, Complex.sin]
  rw [show -((ε : ℂ) - I * x) * t = -(ε * t : ℝ) + (x * t : ℝ) * I by push_cast; ring,
    show -((ε : ℂ) + I * x) * t = -(ε * t : ℝ) + -((x * t : ℝ) * I) by push_cast; ring,
    exp_add, exp_add]
  push_cast
  rw [show -(↑x * ↑t * I) = -(x * t : ℂ) * I by ring]
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- `C ∫ e^{-zt}(1+t²)^{ν-1/2} dt = (x/2)^ν (z/2)^{-ν} K_ν(z)` for `re z > 0`. -/
theorem struveFour_laplace (ν : ℂ) (x : ℝ) {z : ℂ} (hz : 0 < z.re) :
    2 * ((x : ℂ) / 2) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2)) *
      ∫ t in Ioi (0 : ℝ), yLaplaceKernel ν z t =
      ((x : ℂ) / 2) ^ ν * (z / 2) ^ (-ν) * struveK ν z := by
  have hz0 : z / 2 ≠ 0 := div_ne_zero (fun h => by simp [h] at hz) two_ne_zero
  have hp : (z / 2) ^ ν ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; tauto
  rw [struveK_eq_besselYLaplace ν hz, besselYLaplace, cpow_neg]
  field_simp

/-- `ε ↦ (x/2)^ν ((ε + w)/2)^{-ν} K_ν(ε + w)` is continuous at `0` for `w ∈ slitPlane`. -/
theorem struveFour_continuousAt (ν : ℂ) (x : ℝ) {w : ℂ} (hw : w ∈ slitPlane) :
    ContinuousAt (fun ε : ℝ => ((x : ℂ) / 2) ^ ν * ((ε + w) / 2) ^ (-ν) * struveK ν (ε + w)) 0 := by
  have hw2 : w / 2 ∈ slitPlane := by
    rw [div_eq_mul_inv, show (2 : ℂ)⁻¹ = ((2⁻¹ : ℝ) : ℂ) by push_cast; ring]
    rcases hw with h | h
    · left; simpa using h
    · right; simpa using h
  have hc : ContinuousAt (fun ε : ℝ => (ε : ℂ) + w) 0 := by fun_prop
  have h1 : ContinuousAt (fun z : ℂ => (z / 2) ^ (-ν)) w :=
    (continuousAt_id.div_const 2).cpow continuousAt_const hw2
  have h2 : ContinuousAt (struveK ν) w := (analyticOnNhd_struveK ν w hw).continuousAt
  exact (continuousAt_const.mul (h1.comp_of_eq hc (by simp))).mul (h2.comp_of_eq hc (by simp))

/-- Horizontal-ray integral representation: `HasIntegralAtTop (fun t : ℝ => 2*(x/2:ℂ)^ν/(Real.sqrt
π*Gamma (ν+1/2))*(1+t^2:ℂ)^(ν-1/2)*Real.sin (x*t)) 0 (besselI (-ν) x-struveL ν x)`. -/
@[dlmf 11.5.E7]
theorem struveL_fourier {ν : ℂ} (hν : ν.re < 1/2) {x : ℝ} (hx : 0 < x) :
    HasIntegralAtTop (fun t : ℝ => 2*(x/2:ℂ)^ν/(Real.sqrt π*Gamma (ν+1/2))*(1+t^2:ℂ)^(ν-1/2)*Real.sin (x*t)) 0 (besselI (-ν) x-struveL ν x) := by
  set C : ℂ := 2*(x/2:ℂ)^ν/(Real.sqrt π*Gamma (ν+1/2)) with hC
  set f : ℝ → ℂ := fun t => C*(1+t^2:ℂ)^(ν-1/2)*Real.sin (x*t) with hf
  have hfc : Continuous f := by
    have := struveFour_continuous_cpow (ν - 1 / 2)
    simp only [f]; fun_prop
  have hfi : ∀ b, IntervalIntegrable f volume 0 b := fun b => hfc.intervalIntegrable _ _
  obtain ⟨L0, hL0⟩ := struveFour_exists (a := ν - 1 / 2) (by simp; linarith) hx
  have hL : Tendsto (fun R => ∫ t in (0 : ℝ)..R, f t) atTop (𝓝 (C * L0)) := by
    refine (hL0.const_mul C).congr fun R => ?_
    simp only [f, mul_assoc]
    rw [intervalIntegral.integral_const_mul]
  have hint : ∀ ε > (0 : ℝ), IntegrableOn (fun t => Real.exp (-(ε * t)) • f t) (Ioi 0) := by
    intro ε hε
    have h1 := integrableOn_yLaplaceKernel ν (z := ε - I * x) (by simpa using hε)
    have h2 := integrableOn_yLaplaceKernel ν (z := ε + I * x) (by simpa using hε)
    refine IntegrableOn.congr_fun ((h1.sub h2).const_mul (C / (2 * I))) (fun t _ => ?_)
      measurableSet_Ioi
    exact (struveFour_regularized_eq ν C x ε t).symm
  set G : ℝ → ℂ := fun ε => ∫ t in Ioi (0 : ℝ), Real.exp (-(ε * t)) • f t
  have hG : ∀ ε > (0 : ℝ), G ε = 1 / (2 * I) *
      (((x : ℂ) / 2) ^ ν * ((ε + -I * x) / 2) ^ (-ν) * struveK ν (ε + -I * x) -
        ((x : ℂ) / 2) ^ ν * ((ε + I * x) / 2) ^ (-ν) * struveK ν (ε + I * x)) := by
    intro ε hε
    have h1 := integrableOn_yLaplaceKernel ν (z := ε - I * x) (by simpa using hε)
    have h2 := integrableOn_yLaplaceKernel ν (z := ε + I * x) (by simpa using hε)
    simp only [G]
    rw [integral_congr_ae (g := fun t => C / (2 * I) *
      (yLaplaceKernel ν (ε - I * x) t - yLaplaceKernel ν (ε + I * x) t))
      (Eventually.of_forall fun t => struveFour_regularized_eq ν C x ε t),
      integral_const_mul, integral_sub h1 h2]
    rw [show (ε : ℂ) + -I * x = ε - I * x by ring]
    rw [← struveFour_laplace ν x (z := ε - I * x) (by simpa using hε),
      ← struveFour_laplace ν x (z := ε + I * x) (by simpa using hε)]
    simp only [C]
    ring
  have hM : Tendsto G (𝓝[>] 0) (𝓝 (besselI (-ν) x - struveL ν x)) := by
    rw [← struveFour_value hx ν]
    have hc := (struveFour_continuousAt ν x (struveFour_mem_slitPlane_neg_I hx)).sub
      (struveFour_continuousAt ν x (struveFour_mem_slitPlane_I hx))
    have hc' := (hc.const_mul (1 / (2 * I))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    convert hc'.congr' ?_ using 2
    · simp
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (hG ε hε).symm
  have hLM := MeasureTheory.eq_of_tendsto_abel hfc.continuousOn hfi hL
    (fun ε hε => intervalIntegral_tendsto_integral_Ioi 0 (hint ε hε) tendsto_id) hM
  rw [hLM] at hL
  exact hL

/-- Separating loop from positive infinity above the poles to positive infinity below them. -/
def positiveBarnesLoop (f : ℂ → ℂ) (c h R : ℝ) : ℂ :=
  segmentIntegral f (R+h*I) (c+h*I) + segmentIntegral f (c+h*I) (c-h*I) + segmentIntegral f (c-h*I) (R-h*I)

/-! ### The Barnes loop for `L_ν` (DLMF 11.5.9)

The loop integral is a rectangle boundary integral minus its right side. The residue theorem for
rectangles with one simple pole (proved directly from the rectangle Cauchy theorem and the
explicit boundary integral of `(s - p)⁻¹`) gives the partial sums of the residue series on
`[c, N + 1/2] × [-h, h]`; the right sides tend to `0` by the uniform bounds for `1/Γ` on
right-shifted lines (`DLMF.Gamma.shiftB_norm_recip_Gamma_le`, `DLMF.Gamma.shiftB_Gamma_ge`), and the
horizontal integrals converge absolutely. -/

section StruveLoop
open scoped Interval

/-- The boundary integral of `F` over the rectangle `[a, b] × [-h, h]`, in the orientation of
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn` (counterclockwise, `ds` with the
factor `I` on the vertical sides). -/
def struveLoop_rect (F : ℂ → ℂ) (a b h : ℝ) : ℂ :=
  (∫ x : ℝ in a..b, F (x + (-h : ℝ) * I)) - (∫ x : ℝ in a..b, F (x + h * I)) +
    I • (∫ y : ℝ in (-h)..h, F (b + y * I)) - I • ∫ y : ℝ in (-h)..h, F (a + y * I)

/-- The rectangle boundary integral of `(s - p)⁻¹` around a real point `p` is `2πi`. -/
theorem struveLoop_rect_recip {a b p h : ℝ} (ha : a < p) (hb : p < b) (hh : 0 < h) :
    struveLoop_rect (fun s => (s - p)⁻¹) a b h = 2 * π * I := by
  unfold struveLoop_rect
  have hv : ∀ d : ℝ, d ≠ p → ∫ y : ℝ in (-h)..h, (((d : ℂ) + y * I) - p)⁻¹ =
      2 * (Real.arctan (h / (d - p)) : ℂ) := by
    intro d hd
    rw [← Complex.barnesRes_integral_recip (c := d - p) (sub_ne_zero.mpr hd) h]
    congr 1; funext y; push_cast; ring_nf
  have hne : ∀ (x t : ℝ), t ≠ 0 → ((x : ℂ) + t * I - p) ≠ 0 := by
    intro x t ht h0; apply ht; simpa using congrArg Complex.im h0
  have hc : ∀ t : ℝ, t ≠ 0 → Continuous fun x : ℝ => ((x : ℂ) + t * I - p)⁻¹ := fun t ht =>
    Continuous.inv₀ (by fun_prop) fun x => hne x t ht
  have hpt : ∀ x : ℝ, ((x : ℂ) + ((-h : ℝ) : ℂ) * I - p)⁻¹ - ((x : ℂ) + h * I - p)⁻¹ =
      ((2 * h / ((x - p) ^ 2 + h ^ 2) : ℝ) : ℂ) * I := by
    intro x
    have h1 := hne x (-h) (by linarith)
    have h2 := hne x h hh.ne'
    have h3 : ((x - p) ^ 2 + h ^ 2 : ℝ) ≠ 0 := by positivity
    have hden : ((x : ℂ) + ((-h : ℝ) : ℂ) * I - p) * ((x : ℂ) + h * I - p) =
        (((x - p) ^ 2 + h ^ 2 : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [I_sq]; ring
    rw [inv_sub_inv h1 h2, hden]
    have h3' : ((x : ℂ) - p) ^ 2 + (h : ℂ) ^ 2 ≠ 0 := by exact_mod_cast h3
    push_cast
    field_simp
    ring
  have hH : (∫ x : ℝ in a..b, ((x : ℂ) + ((-h : ℝ) : ℂ) * I - p)⁻¹) -
      (∫ x : ℝ in a..b, ((x : ℂ) + h * I - p)⁻¹) =
      ((2 * (Real.arctan ((b - p) / h) - Real.arctan ((a - p) / h)) : ℝ) : ℂ) * I := by
    rw [← intervalIntegral.integral_sub ((hc _ (by linarith)).intervalIntegrable _ _)
      ((hc _ hh.ne').intervalIntegrable _ _)]
    simp_rw [hpt]
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal]
    congr 2
    have hd : ∀ x : ℝ, HasDerivAt (fun x => 2 * Real.arctan ((x - p) / h))
        (2 * h / ((x - p) ^ 2 + h ^ 2)) x := by
      intro x
      have := (((hasDerivAt_id' x).sub_const p).div_const h).arctan.const_mul 2
      convert this using 1
      field_simp
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      (Continuous.intervalIntegrable (by
        refine Continuous.div (by fun_prop) (by fun_prop) fun x => by positivity) _ _)]
    ring
  simp only
  rw [hH, smul_eq_mul, smul_eq_mul, hv b hb.ne', hv a ha.ne]
  have hB : Real.arctan (h / (b - p)) = π / 2 - Real.arctan ((b - p) / h) := by
    rw [← inv_div, Real.arctan_inv_of_pos (div_pos (by linarith) hh)]
  have hA : Real.arctan (h / (a - p)) = -(π / 2) - Real.arctan ((a - p) / h) := by
    rw [← inv_div, Real.arctan_inv_of_neg (div_neg_of_neg_of_pos (by linarith) hh)]
  rw [hB, hA]
  push_cast
  ring

/-- Linearity of the rectangle boundary integral, for functions continuous on the four sides. -/
theorem struveLoop_rect_add {f g : ℂ → ℂ} {a b h : ℝ}
    (hf : ContinuousOn f ([[a, b]] ×ℂ [[-h, h]] \ (re ⁻¹' Ioo a b ∩ im ⁻¹' Ioo (-h) h)))
    (hg : ContinuousOn g ([[a, b]] ×ℂ [[-h, h]] \ (re ⁻¹' Ioo a b ∩ im ⁻¹' Ioo (-h) h))) :
    struveLoop_rect (fun s => f s + g s) a b h = struveLoop_rect f a b h + struveLoop_rect g a b h := by
  have hh : ∀ t : ℝ, (t = -h ∨ t = h) → ∀ k : ℂ → ℂ,
      ContinuousOn k ([[a, b]] ×ℂ [[-h, h]] \ (re ⁻¹' Ioo a b ∩ im ⁻¹' Ioo (-h) h)) →
      IntervalIntegrable (fun x : ℝ => k (x + t * I)) volume a b := by
    intro t ht k hk
    refine ContinuousOn.intervalIntegrable ?_
    refine hk.comp (by fun_prop) fun x hx => ?_
    refine ⟨⟨by simpa using hx, ?_⟩, ?_⟩
    · show (((x : ℂ) + t * I).im) ∈ [[-h, h]]
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, zero_add, add_zero]
      rcases ht with ht | ht <;> rw [ht]
      exacts [Set.left_mem_uIcc (a := -h) (b := h), Set.right_mem_uIcc (a := -h) (b := h)]
    · rintro ⟨-, h2⟩
      simp only [mem_preimage, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re,
        mul_zero, zero_add, add_zero, mem_Ioo] at h2
      rcases ht with ht | ht <;> rw [ht] at h2 <;> linarith [h2.1, h2.2]
  have hv : ∀ x : ℝ, (x = a ∨ x = b) → ∀ k : ℂ → ℂ,
      ContinuousOn k ([[a, b]] ×ℂ [[-h, h]] \ (re ⁻¹' Ioo a b ∩ im ⁻¹' Ioo (-h) h)) →
      IntervalIntegrable (fun y : ℝ => k (x + y * I)) volume (-h) h := by
    intro x hx k hk
    refine ContinuousOn.intervalIntegrable ?_
    refine hk.comp (by fun_prop) fun y hy => ?_
    refine ⟨⟨?_, by simpa using hy⟩, ?_⟩
    · show (((x : ℂ) + y * I).re) ∈ [[a, b]]
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_self,
        add_zero]
      rcases hx with hx | hx <;> rw [hx]
      exacts [Set.left_mem_uIcc (a := a) (b := b), Set.right_mem_uIcc (a := a) (b := b)]
    · rintro ⟨h1, -⟩
      simp only [mem_preimage, add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im,
        mul_one, sub_self, add_zero, mem_Ioo] at h1
      rcases hx with hx | hx <;> rw [hx] at h1 <;> linarith [h1.1, h1.2]
  unfold struveLoop_rect
  rw [intervalIntegral.integral_add (hh _ (Or.inl rfl) f hf) (hh _ (Or.inl rfl) g hg),
    intervalIntegral.integral_add (hh _ (Or.inr rfl) f hf) (hh _ (Or.inr rfl) g hg),
    intervalIntegral.integral_add (hv _ (Or.inr rfl) f hf) (hv _ (Or.inr rfl) g hg),
    intervalIntegral.integral_add (hv _ (Or.inl rfl) f hf) (hv _ (Or.inl rfl) g hg)]
  simp only [smul_eq_mul]
  ring

/-- The boundary of the rectangle `[a, b] × [-h, h]`. -/
def struveLoop_bdry (a b h : ℝ) : Set ℂ :=
  [[a, b]] ×ℂ [[-h, h]] \ (re ⁻¹' Ioo a b ∩ im ⁻¹' Ioo (-h) h)

/-- Points of the horizontal sides lie on the rectangle boundary. -/
theorem struveLoop_mem_bdry_h {a b h t x : ℝ} (ht : t = -h ∨ t = h) (hx : x ∈ [[a, b]]) :
    (x : ℂ) + t * I ∈ struveLoop_bdry a b h := by
  refine ⟨⟨by simpa using hx, ?_⟩, ?_⟩
  · show (((x : ℂ) + t * I).im) ∈ [[-h, h]]
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, zero_add,
      add_zero]
    rcases ht with ht | ht <;> rw [ht]
    exacts [Set.left_mem_uIcc (a := -h) (b := h), Set.right_mem_uIcc (a := -h) (b := h)]
  · rintro ⟨-, h2⟩
    simp only [mem_preimage, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re,
      mul_zero, zero_add, add_zero, mem_Ioo] at h2
    rcases ht with ht | ht <;> rw [ht] at h2 <;> linarith [h2.1, h2.2]

/-- Points of the vertical sides lie on the rectangle boundary. -/
theorem struveLoop_mem_bdry_v {a b h x y : ℝ} (hx : x = a ∨ x = b) (hy : y ∈ [[-h, h]]) :
    (x : ℂ) + y * I ∈ struveLoop_bdry a b h := by
  refine ⟨⟨?_, by simpa using hy⟩, ?_⟩
  · show (((x : ℂ) + y * I).re) ∈ [[a, b]]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_self,
      add_zero]
    rcases hx with hx | hx <;> rw [hx]
    exacts [Set.left_mem_uIcc (a := a) (b := b), Set.right_mem_uIcc (a := a) (b := b)]
  · rintro ⟨h1, -⟩
    simp only [mem_preimage, add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im,
      mul_one, sub_self, add_zero, mem_Ioo] at h1
    rcases hx with hx | hx <;> rw [hx] at h1 <;> linarith [h1.1, h1.2]

/-- The rectangle boundary integral only depends on the values on the boundary. -/
theorem struveLoop_rect_congr {F G : ℂ → ℂ} {a b h : ℝ} (hFG : EqOn F G (struveLoop_bdry a b h)) :
    struveLoop_rect F a b h = struveLoop_rect G a b h := by
  unfold struveLoop_rect
  rw [intervalIntegral.integral_congr (g := fun x : ℝ => G (x + (-h : ℝ) * I))
      fun x hx => hFG (struveLoop_mem_bdry_h (Or.inl rfl) hx),
    intervalIntegral.integral_congr (g := fun x : ℝ => G (x + h * I))
      fun x hx => hFG (struveLoop_mem_bdry_h (Or.inr rfl) hx),
    intervalIntegral.integral_congr (g := fun y : ℝ => G (b + y * I))
      fun y hy => hFG (struveLoop_mem_bdry_v (Or.inr rfl) hy),
    intervalIntegral.integral_congr (g := fun y : ℝ => G (a + y * I))
      fun y hy => hFG (struveLoop_mem_bdry_v (Or.inl rfl) hy)]

/-- The rectangle boundary integral is homogeneous. -/
theorem struveLoop_rect_const_mul (F : ℂ → ℂ) (c : ℂ) (a b h : ℝ) :
    struveLoop_rect (fun s => c * F s) a b h = c * struveLoop_rect F a b h := by
  unfold struveLoop_rect
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul]
  ring

/-- **Residue theorem for a rectangle with one simple pole on the real axis.** -/
theorem struveLoop_rect_pole {F Φ : ℂ → ℂ} {a b p h : ℝ} (ha : a < p) (hb : p < b) (hh : 0 < h)
    (hΦ : DifferentiableOn ℂ Φ ([[a, b]] ×ℂ [[-h, h]]))
    (hF : ∀ s ∈ struveLoop_bdry a b h, F s = Φ s / (s - p)) :
    struveLoop_rect F a b h = 2 * π * I * Φ p := by
  have hS : [[a, b]] ×ℂ [[-h, h]] ∈ 𝓝 (p : ℂ) := by
    have ho : IsOpen (re ⁻¹' Ioo a b ∩ im ⁻¹' Ioo (-h) h) :=
      (isOpen_Ioo.preimage continuous_re).inter (isOpen_Ioo.preimage continuous_im)
    refine Filter.mem_of_superset (ho.mem_nhds ⟨by simp [ha, hb], by simp [hh]⟩) ?_
    rintro s ⟨h1, h2⟩
    exact ⟨Ioo_subset_Icc_self.trans Icc_subset_uIcc h1, Ioo_subset_Icc_self.trans Icc_subset_uIcc h2⟩
  set g := dslope Φ p with hgdef
  have hg : DifferentiableOn ℂ g ([[a, b]] ×ℂ [[-h, h]]) := (differentiableOn_dslope hS).mpr hΦ
  have hne : ∀ s ∈ struveLoop_bdry a b h, s ≠ (p : ℂ) := by
    rintro s hs rfl
    exact hs.2 ⟨by simp [ha, hb], by simp [hh]⟩
  have hdec : EqOn F (fun s => Φ p * (s - p)⁻¹ + g s) (struveLoop_bdry a b h) := by
    intro s hs
    have hsp : s - p ≠ 0 := sub_ne_zero.mpr (hne s hs)
    simp only [hgdef, dslope_of_ne _ (hne s hs), slope_def_module, smul_eq_mul]
    rw [hF s hs]
    field_simp
    ring
  have hinv : ContinuousOn (fun s : ℂ => Φ p * (s - p)⁻¹) (struveLoop_bdry a b h) :=
    continuousOn_const.mul (ContinuousOn.inv₀ (by fun_prop) fun s hs => sub_ne_zero.mpr (hne s hs))
  rw [struveLoop_rect_congr hdec, struveLoop_rect_add hinv (hg.continuousOn.mono sdiff_subset),
    struveLoop_rect_const_mul (fun s => (s - p)⁻¹), struveLoop_rect_recip ha hb hh]
  have h0 := integral_boundary_rect_eq_zero_of_differentiableOn g ⟨a, -h⟩ ⟨b, h⟩ hg
  have : struveLoop_rect g a b h = 0 := h0
  rw [this]; ring

/-- The positive Barnes loop as a rectangle boundary integral minus its right side. -/
theorem struveLoop_loop_eq (F : ℂ → ℂ) (c h R : ℝ) :
    positiveBarnesLoop F c h R =
      struveLoop_rect F c R h - I * ∫ y : ℝ in (-h)..h, F (R + y * I) := by
  unfold positiveBarnesLoop segmentIntegral struveLoop_rect
  have e1 : ((c : ℂ) + h * I - (R + h * I)) * ∫ t : ℝ in (0 : ℝ)..1,
      F (R + h * I + t * ((c : ℂ) + h * I - (R + h * I))) =
      -∫ x : ℝ in c..R, F (x + h * I) := by
    have := intervalIntegral.smul_integral_comp_mul_add (fun x : ℝ => F (x + h * I))
      (a := 0) (b := 1) (c - R) R
    simp only [mul_zero, zero_add, mul_one, sub_add_cancel] at this
    rw [intervalIntegral.integral_symm R c, ← this, real_smul]
    have : (fun t : ℝ => F (R + h * I + t * ((c : ℂ) + h * I - (R + h * I)))) =
        fun t : ℝ => F (((c - R) * t + R : ℝ) + h * I) := by
      funext t; congr 1; push_cast; ring
    rw [this]; push_cast; ring
  have e2 : ((c : ℂ) - h * I - (c + h * I)) * ∫ t : ℝ in (0 : ℝ)..1,
      F (c + h * I + t * ((c : ℂ) - h * I - (c + h * I))) =
      -(I * ∫ y : ℝ in (-h)..h, F (c + y * I)) := by
    have := intervalIntegral.smul_integral_comp_mul_add (fun y : ℝ => F (c + y * I))
      (a := 0) (b := 1) (-2 * h) h
    simp only [mul_zero, zero_add, mul_one, show -2 * h + h = -h by ring] at this
    rw [intervalIntegral.integral_symm h (-h), ← this, real_smul]
    have : (fun t : ℝ => F (c + h * I + t * ((c : ℂ) - h * I - (c + h * I)))) =
        fun t : ℝ => F (c + ((-2 * h) * t + h : ℝ) * I) := by
      funext t; congr 1; push_cast; ring
    rw [this]; push_cast; ring
  have e3 : ((R : ℂ) - h * I - (c - h * I)) * ∫ t : ℝ in (0 : ℝ)..1,
      F (c - h * I + t * ((R : ℂ) - h * I - (c - h * I))) =
      ∫ x : ℝ in c..R, F (x + (-h : ℝ) * I) := by
    have := intervalIntegral.smul_integral_comp_mul_add (fun x : ℝ => F (x + (-h : ℝ) * I))
      (a := 0) (b := 1) (R - c) c
    simp only [mul_zero, zero_add, mul_one, sub_add_cancel] at this
    rw [← this, real_smul]
    have : (fun t : ℝ => F (c - h * I + t * ((R : ℂ) - h * I - (c - h * I)))) =
        fun t : ℝ => F (((R - c) * t + c : ℝ) + (-h : ℝ) * I) := by
      funext t; congr 1; push_cast; ring
    rw [this]; push_cast; ring
  rw [e1, e2, e3, smul_eq_mul, smul_eq_mul]
  ring

/-- Additivity of the rectangle boundary integral over adjacent rectangles. -/
theorem struveLoop_rect_adj {F : ℂ → ℂ} {a b d h : ℝ}
    (hcont : ∀ t : ℝ, (t = -h ∨ t = h) → Continuous fun x : ℝ => F (x + t * I)) :
    struveLoop_rect F a b h + struveLoop_rect F b d h = struveLoop_rect F a d h := by
  unfold struveLoop_rect
  rw [← intervalIntegral.integral_add_adjacent_intervals
      ((hcont _ (Or.inl rfl)).intervalIntegrable a b) ((hcont _ (Or.inl rfl)).intervalIntegrable b d),
    ← intervalIntegral.integral_add_adjacent_intervals
      ((hcont _ (Or.inr rfl)).intervalIntegrable a b) ((hcont _ (Or.inr rfl)).intervalIntegrable b d)]
  ring

/-- The left end of the `n`-th rectangle: `c` for `n = 0`, `n - 1/2` otherwise. -/
def struveLoop_cut (c : ℝ) (n : ℕ) : ℝ := if n = 0 then c else (n : ℝ) - 1 / 2

/-- **Residue theorem for the rectangles `[c, N + 1/2] × [-h, h]`** with simple poles at
`0, 1, …, N`. -/
theorem struveLoop_rect_sum {F : ℂ → ℂ} {Φ : ℕ → ℂ → ℂ} {c h : ℝ} (hc0 : c < 0) (hh : 0 < h)
    (hcont : ∀ t : ℝ, (t = -h ∨ t = h) → Continuous fun x : ℝ => F (x + t * I))
    (hΦ : ∀ n : ℕ, DifferentiableOn ℂ (Φ n) ([[struveLoop_cut c n, n + 1 / 2]] ×ℂ [[-h, h]]))
    (hF : ∀ n : ℕ, ∀ s ∈ struveLoop_bdry (struveLoop_cut c n) (n + 1 / 2) h,
      F s = Φ n s / (s - n)) (N : ℕ) :
    struveLoop_rect F c (N + 1 / 2) h = 2 * π * I * ∑ n ∈ Finset.range (N + 1), Φ n n := by
  have hpole : ∀ n : ℕ, struveLoop_rect F (struveLoop_cut c n) (n + 1 / 2) h =
      2 * π * I * Φ n n := by
    intro n
    have hcut : struveLoop_cut c n < n := by
      unfold struveLoop_cut; split_ifs with hn
      · subst hn; simpa using hc0
      · linarith
    have := struveLoop_rect_pole (F := F) (Φ := Φ n) (p := (n : ℝ)) hcut (by linarith) hh (hΦ n)
      (fun s hs => by rw [hF n s hs, ofReal_natCast])
    rwa [ofReal_natCast] at this
  induction N with
  | zero =>
    have := hpole 0
    simp only [struveLoop_cut, Nat.cast_zero] at this
    simpa using this
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ← ih, ← hpole (N + 1)]
    have hc : struveLoop_cut c (N + 1) = (N : ℝ) + 1 / 2 := by
      simp only [struveLoop_cut, Nat.succ_ne_zero, ite_false]; push_cast; ring
    rw [hc, struveLoop_rect_adj hcont]

/-- Exponential decay of `w^s / (Γ(3/2+s) Γ(3/2+ν+s))` in a horizontal strip as `Re s → ∞`. -/
theorem struveLoop_tail_bound (ν : ℂ) {w : ℂ} (hw : w ≠ 0) (h : ℝ) :
    ∃ X K : ℝ, ∀ x : ℝ, X ≤ x → ∀ y : ℝ, |y| ≤ h →
      ‖(Gamma (3 / 2 + (x + y * I)))⁻¹ * (Gamma (3 / 2 + ν + (x + y * I)))⁻¹ *
        w ^ ((x : ℂ) + y * I)‖ ≤ K * Real.exp (-x) := by
  set A : ℝ := Real.exp 1 * (‖w‖ + 1) with hA
  have hA0 : 0 < A := by positivity
  have hwA : ‖w‖ / A ≤ Real.exp (-1) := by
    rw [div_le_iff₀ hA0, hA, ← mul_assoc, ← Real.exp_add]; simp
  refine ⟨max 0 (-1 / 2 - ν.re), Real.exp (π * h) * (Real.exp (π * h / 2) *
    (A ^ (-(1 / 2 : ℝ)) * Real.exp (A + 1))) * (Real.exp (π * (|ν.im| + h) / 2) * Real.exp 2),
    fun x hx y hy => ?_⟩
  have hx0 : 0 ≤ x := le_trans (le_max_left _ _) hx
  have hxν : -1 / 2 - ν.re ≤ x := le_trans (le_max_right _ _) hx
  -- the power
  have hpow : ‖w ^ ((x : ℂ) + y * I)‖ ≤ ‖w‖ ^ x * Real.exp (π * h) := by
    rw [norm_cpow_of_ne_zero hw]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add]
    rw [div_eq_mul_inv, ← Real.exp_neg]
    gcongr
    have h1 := abs_arg_le_pi w
    have h2 : |arg w * y| ≤ π * h := by
      rw [abs_mul]; exact mul_le_mul h1 hy (abs_nonneg _) Real.pi_pos.le
    linarith [neg_abs_le (arg w * y)]
  -- the first Gamma
  have hG1 : ‖(Gamma (3 / 2 + (x + y * I)))⁻¹‖ ≤
      Real.exp (π * h / 2) * (A ^ (-(1 / 2 : ℝ)) * Real.exp (A + 1)) * (A ^ x)⁻¹ := by
    have e : (3 / 2 : ℂ) + (x + y * I) = ((3 / 2 + x : ℝ) : ℂ) + y * I := by push_cast; ring
    rw [e]
    refine (DLMF.Gamma.shiftB_norm_recip_Gamma_le (by linarith) y).trans ?_
    have hg := DLMF.Gamma.shiftB_Gamma_ge (t := 3 / 2 + x) (by linarith) hA0
    have hGp : 0 < Real.Gamma (3 / 2 + x) := Real.Gamma_pos_of_pos (by linarith)
    rw [div_le_iff₀ hGp]
    have hE : Real.exp (π * |y| / 2) ≤ Real.exp (π * h / 2) := by
      gcongr
    have hk : A ^ (-(1 / 2 : ℝ)) * Real.exp (A + 1) * (A ^ x)⁻¹ *
        (A ^ (3 / 2 + x - 1) * Real.exp (-(A + 1))) = 1 := by
      rw [show (3 / 2 + x - 1 : ℝ) = 1 / 2 + x by ring, Real.rpow_add hA0, Real.rpow_neg hA0.le]
      have : Real.exp (A + 1) * Real.exp (-(A + 1)) = 1 := by rw [← Real.exp_add]; simp
      have h1 : 0 < A ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hA0 _
      have h2 : 0 < A ^ x := Real.rpow_pos_of_pos hA0 _
      field_simp
      exact this
    have hC : 0 ≤ Real.exp (π * h / 2) * (A ^ (-(1 / 2 : ℝ)) * Real.exp (A + 1)) * (A ^ x)⁻¹ := by
      positivity
    calc Real.exp (π * |y| / 2) ≤ Real.exp (π * h / 2) := hE
      _ = (Real.exp (π * h / 2) * (A ^ (-(1 / 2 : ℝ)) * Real.exp (A + 1)) * (A ^ x)⁻¹) *
            (A ^ (3 / 2 + x - 1) * Real.exp (-(A + 1))) := by
          linear_combination (-Real.exp (π * h / 2)) * hk
      _ ≤ _ := mul_le_mul_of_nonneg_left hg hC
  -- the second Gamma
  have hG2 : ‖(Gamma (3 / 2 + ν + (x + y * I)))⁻¹‖ ≤
      Real.exp (π * (|ν.im| + h) / 2) * Real.exp 2 := by
    have e : (3 / 2 : ℂ) + ν + (x + y * I) = ((3 / 2 + ν.re + x : ℝ) : ℂ) + (ν.im + y : ℝ) * I := by
      apply Complex.ext <;> simp
    rw [e]
    refine (DLMF.Gamma.shiftB_norm_recip_Gamma_le (by linarith) _).trans ?_
    have hg := DLMF.Gamma.shiftB_Gamma_ge (t := 3 / 2 + ν.re + x) (by linarith) one_pos
    rw [Real.one_rpow, one_mul, show (1 : ℝ) + 1 = 2 by norm_num] at hg
    have hGp : 0 < Real.Gamma (3 / 2 + ν.re + x) := Real.Gamma_pos_of_pos (by linarith)
    rw [div_le_iff₀ hGp]
    have hE : Real.exp (π * |ν.im + y| / 2) ≤ Real.exp (π * (|ν.im| + h) / 2) := by
      gcongr; exact (abs_add_le _ _).trans (by linarith)
    have h22 : Real.exp 2 * Real.exp (-2) = 1 := by rw [← Real.exp_add]; simp
    have hC : 0 ≤ Real.exp (π * (|ν.im| + h) / 2) * Real.exp 2 := by positivity
    calc Real.exp (π * |ν.im + y| / 2) ≤ Real.exp (π * (|ν.im| + h) / 2) := hE
      _ = (Real.exp (π * (|ν.im| + h) / 2) * Real.exp 2) * Real.exp (-2) := by
          linear_combination (-Real.exp (π * (|ν.im| + h) / 2)) * h22
      _ ≤ _ := mul_le_mul_of_nonneg_left hg hC
  -- assemble
  have hfin : ‖w‖ ^ x * (A ^ x)⁻¹ ≤ Real.exp (-x) := by
    rw [← div_eq_mul_inv, ← Real.div_rpow (norm_nonneg _) hA0.le]
    calc (‖w‖ / A) ^ x ≤ Real.exp (-1) ^ x :=
          Real.rpow_le_rpow (by positivity) hwA hx0
      _ = Real.exp (-x) := by rw [← Real.exp_mul]; ring_nf
  rw [norm_mul, norm_mul]
  calc ‖(Gamma (3 / 2 + (x + y * I)))⁻¹‖ * ‖(Gamma (3 / 2 + ν + (x + y * I)))⁻¹‖ *
        ‖w ^ ((x : ℂ) + y * I)‖
      ≤ (Real.exp (π * h / 2) * (A ^ (-(1 / 2 : ℝ)) * Real.exp (A + 1)) * (A ^ x)⁻¹) *
        (Real.exp (π * (|ν.im| + h) / 2) * Real.exp 2) * (‖w‖ ^ x * Real.exp (π * h)) := by
        gcongr
    _ = Real.exp (π * h) * (Real.exp (π * h / 2) * (A ^ (-(1 / 2 : ℝ)) * Real.exp (A + 1))) *
        (Real.exp (π * (|ν.im| + h) / 2) * Real.exp 2) * (‖w‖ ^ x * (A ^ x)⁻¹) := by ring
    _ ≤ _ := by gcongr

/-- The integrand of the Barnes loop for `L_ν` (DLMF 11.5.9). -/
def struveLoop_F (ν z : ℂ) : ℂ → ℂ :=
  fun s : ℂ => π/sin (π*s)/(Gamma (3/2+s)*Gamma (3/2+ν+s))*(-z^2/4)^s

/-- `sin(πs)/(s - n)`, holomorphic (removable at `s = n`). -/
def struveLoop_D (n : ℕ) : ℂ → ℂ := dslope (fun u : ℂ => sin (π * u)) n

/-- The numerator of the integrand at the pole `n`: `F s = Φ_n s / (s - n)`. -/
def struveLoop_num (ν z : ℂ) (n : ℕ) : ℂ → ℂ :=
  fun s : ℂ => π / struveLoop_D n s / (Gamma (3/2+s)*Gamma (3/2+ν+s)) * (-z^2/4)^s

/-- The zeros of `sin(πs)` are the integers. -/
theorem struveLoop_sin_eq_zero {s : ℂ} (hs : sin (π * s) = 0) : ∃ k : ℤ, s = k := by
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hs
  refine ⟨k, ?_⟩
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have := hk; field_simp at this
  linear_combination this

/-- `sin(πs)/(s - n)` is entire. -/
theorem struveLoop_differentiable_D (n : ℕ) : Differentiable ℂ (struveLoop_D n) := by
  have := (differentiableOn_dslope (f := fun u : ℂ => sin (π * u)) (c := (n : ℂ))
    (s := univ) Filter.univ_mem).mpr (by fun_prop)
  exact differentiableOn_univ.mp this

/-- `D_n(s) = sin(πs)/(s - n)` for `s ≠ n`. -/
theorem struveLoop_D_of_ne {n : ℕ} {s : ℂ} (hs : s ≠ n) :
    struveLoop_D n s = sin (π * s) / (s - n) := by
  rw [struveLoop_D, dslope_of_ne _ hs, slope_def_module, smul_eq_mul,
    show (π : ℂ) * n = n * π by ring, Complex.sin_nat_mul_pi, sub_zero, div_eq_inv_mul]

/-- `D_n(n) = π cos(πn) = π (-1)^n`. -/
theorem struveLoop_D_self (n : ℕ) : struveLoop_D n n = π * (-1) ^ n := by
  rw [struveLoop_D, dslope_same]
  have hd : HasDerivAt (fun u : ℂ => sin (π * u)) (cos (π * n) * π) n := by
    have := ((hasDerivAt_id (n : ℂ)).const_mul (π : ℂ)).csin
    simpa using this
  have hc : Complex.cos (π * n) = (-1) ^ n := by
    rw [show (π : ℂ) * n = ((n * π : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos,
      Real.cos_nat_mul_pi]; push_cast; ring
  rw [hd.deriv, hc]
  ring

/-- `D_n` has no zeros on the `n`-th rectangle. -/
theorem struveLoop_D_ne_zero {c h : ℝ} (hc : -1 < c) (hc0 : c < 0) {n : ℕ} {s : ℂ}
    (hs : s ∈ [[struveLoop_cut c n, n + 1 / 2]] ×ℂ [[-h, h]]) : struveLoop_D n s ≠ 0 := by
  by_cases hsn : s = n
  · rw [hsn, struveLoop_D_self]
    exact mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) (pow_ne_zero _ (by norm_num))
  rw [struveLoop_D_of_ne hsn]
  refine div_ne_zero (fun h0 => hsn ?_) (sub_ne_zero.mpr hsn)
  obtain ⟨k, rfl⟩ := struveLoop_sin_eq_zero h0
  have hre : ((k : ℂ)).re ∈ [[struveLoop_cut c n, n + 1 / 2]] := hs.1
  simp only [intCast_re] at hre
  have hcut : (n : ℝ) - 1 < struveLoop_cut c n := by
    unfold struveLoop_cut; split_ifs with hn
    · subst hn; simpa using hc
    · linarith
  have hle : struveLoop_cut c n ≤ n + 1 / 2 := by
    unfold struveLoop_cut; split_ifs with hn
    · subst hn; simp; linarith
    · linarith
  rw [Set.uIcc_of_le hle] at hre
  have h1 : ((n : ℤ) : ℝ) - 1 < (k : ℝ) := by push_cast; linarith [hre.1]
  have h2 : (k : ℝ) < ((n : ℤ) : ℝ) + 1 := by push_cast; linarith [hre.2]
  have h1' : (n : ℤ) - 1 < k := by exact_mod_cast h1
  have h2' : k < (n : ℤ) + 1 := by exact_mod_cast h2
  have : k = (n : ℤ) := by omega
  subst this; simp

/-- The numerator `Φ_n` is holomorphic on the closed `n`-th rectangle. -/
theorem struveLoop_differentiableOn_Φ (ν z : ℂ) {c h : ℝ} (hc : -1 < c) (hc0 : c < 0) (hz : z ≠ 0) (n : ℕ) :
    DifferentiableOn ℂ (struveLoop_num ν z n) ([[struveLoop_cut c n, n + 1 / 2]] ×ℂ [[-h, h]]) := by
  have hw : -z ^ 2 / 4 ≠ 0 := by
    have := pow_ne_zero 2 hz; intro h0; apply this; linear_combination -4 * h0
  have e : struveLoop_num ν z n = fun s => π / struveLoop_D n s *
      ((Gamma (3/2+s))⁻¹ * (Gamma (3/2+ν+s))⁻¹) * (-z^2/4)^s := by
    funext s; simp only [struveLoop_num]; rw [div_eq_mul_inv _ (Gamma _ * Gamma _), mul_inv]
  rw [e]
  refine DifferentiableOn.mul (DifferentiableOn.mul ?_ ?_) ?_
  · exact DifferentiableOn.div (differentiableOn_const _)
      (struveLoop_differentiable_D n).differentiableOn fun s hs => struveLoop_D_ne_zero hc hc0 hs
  · have hg1 : Differentiable ℂ fun s : ℂ => (Gamma (3/2+s))⁻¹ := fun s =>
      (differentiable_one_div_Gamma (3/2+s)).comp s ((differentiableAt_id).const_add _)
    have hg2 : Differentiable ℂ fun s : ℂ => (Gamma (3/2+ν+s))⁻¹ := fun s =>
      (differentiable_one_div_Gamma (3/2+ν+s)).comp s ((differentiableAt_id).const_add _)
    exact (hg1.mul hg2).differentiableOn
  · exact (differentiable_id.const_cpow (Or.inl hw)).differentiableOn

/-- On the boundary of the `n`-th rectangle, `F(s) = Φ_n(s)/(s - n)`. -/
theorem struveLoop_F_eq_Φ (ν z : ℂ) {c h : ℝ} (hc0 : c < 0) (hh : 0 < h) (n : ℕ) {s : ℂ}
    (hs : s ∈ struveLoop_bdry (struveLoop_cut c n) (n + 1 / 2) h) :
    struveLoop_F ν z s = struveLoop_num ν z n s / (s - n) := by
  have hsn : s ≠ n := by
    rintro rfl
    refine hs.2 ⟨?_, by simp [hh]⟩
    simp only [mem_preimage, natCast_re, mem_Ioo]
    refine ⟨?_, by linarith⟩
    unfold struveLoop_cut; split_ifs with hn
    · subst hn; simpa using hc0
    · linarith
  simp only [struveLoop_F, struveLoop_num, struveLoop_D_of_ne hsn]
  have hsn' : s - n ≠ 0 := sub_ne_zero.mpr hsn
  rcases eq_or_ne (sin (π * s)) 0 with h0 | h0
  · simp [h0]
  · field_simp

/-- The integrand as `π/sin(πs)` times an entire function. -/
theorem struveLoop_F_eq (ν z s : ℂ) : struveLoop_F ν z s = π / sin (π * s) *
    ((Gamma (3/2+s))⁻¹ * (Gamma (3/2+ν+s))⁻¹ * (-z^2/4)^s) := by
  simp only [struveLoop_F, div_eq_mul_inv _ (Gamma _ * Gamma _), mul_inv]; ring

/-- `-z²/4 ≠ 0` for `z ≠ 0`. -/
theorem struveLoop_w_ne_zero {z : ℂ} (hz : z ≠ 0) : -z ^ 2 / 4 ≠ 0 := by
  have := pow_ne_zero 2 hz; intro h0; apply this; linear_combination -4 * h0

/-- The entire factor `w^s/(Γ(3/2+s)Γ(3/2+ν+s))` is continuous. -/
theorem struveLoop_continuous_G (ν : ℂ) {z : ℂ} (hz : z ≠ 0) :
    Continuous fun s : ℂ => (Gamma (3/2+s))⁻¹ * (Gamma (3/2+ν+s))⁻¹ * (-z^2/4)^s := by
  have hg1 : Differentiable ℂ fun s : ℂ => (Gamma (3/2+s))⁻¹ := fun s =>
    (differentiable_one_div_Gamma (3/2+s)).comp s ((differentiableAt_id).const_add _)
  have hg2 : Differentiable ℂ fun s : ℂ => (Gamma (3/2+ν+s))⁻¹ := fun s =>
    (differentiable_one_div_Gamma (3/2+ν+s)).comp s ((differentiableAt_id).const_add _)
  exact (hg1.continuous.mul hg2.continuous).mul (continuous_const_cpow' (struveLoop_w_ne_zero hz))

/-- The integrand is continuous on every horizontal line off the real axis. -/
theorem struveLoop_continuous_line (ν : ℂ) {z : ℂ} (hz : z ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    Continuous fun x : ℝ => struveLoop_F ν z (x + t * I) := by
  simp_rw [struveLoop_F_eq]
  refine Continuous.mul (Continuous.div continuous_const (by fun_prop) fun x h0 => ?_)
    ((struveLoop_continuous_G ν hz).comp (by fun_prop))
  obtain ⟨k, hk⟩ := struveLoop_sin_eq_zero h0
  apply ht; simpa using congrArg Complex.im hk

/-- `|π/sin(π(x+it))| ≤ π/|sinh(πt)|`. -/
theorem struveLoop_norm_pi_div_sin_le_line {x t : ℝ} (ht : t ≠ 0) :
    ‖(π : ℂ) / sin (π * (x + t * I))‖ ≤ π / |Real.sinh (π * t)| := by
  have hs := Complex.barnesRes_abs_sinh_le_norm_sin (π * x) (π * t)
  have hpos : 0 < |Real.sinh (π * t)| := by
    rw [abs_pos, Real.sinh_ne_zero]; exact mul_ne_zero Real.pi_ne_zero ht
  rw [show (π : ℂ) * (x + t * I) = ((π * x : ℝ) : ℂ) + ((π * t : ℝ) : ℂ) * I by push_cast; ring,
    norm_div, norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  exact div_le_div_of_nonneg_left Real.pi_pos.le hpos hs

/-- The integrand is integrable on horizontal half-lines `Re s > c`, `Im s = t ≠ 0`. -/
theorem struveLoop_integrableOn (ν : ℂ) {z : ℂ} (hz : z ≠ 0) (c : ℝ) {t : ℝ} (ht : t ≠ 0) :
    IntegrableOn (fun x : ℝ => struveLoop_F ν z (x + t * I)) (Ioi c) := by
  obtain ⟨X, K, hK⟩ := struveLoop_tail_bound ν (struveLoop_w_ne_zero hz) |t|
  set X' := max X c
  have hc := struveLoop_continuous_line ν hz ht
  have h1 : IntegrableOn (fun x : ℝ => struveLoop_F ν z (x + t * I)) (Icc c X') :=
    hc.integrableOn_Icc
  have h2 : IntegrableOn (fun x : ℝ => struveLoop_F ν z (x + t * I)) (Ioi X') := by
    refine ((exp_neg_integrableOn_Ioi X' one_pos).const_mul
      (π / |Real.sinh (π * t)| * K)).mono' hc.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
    have hx : X ≤ x := le_trans (le_max_left _ _) (le_of_lt hx)
    rw [struveLoop_F_eq, norm_mul, neg_one_mul]
    refine le_of_le_of_eq (mul_le_mul (struveLoop_norm_pi_div_sin_le_line (x := x) ht)
      (hK x hx t le_rfl) (norm_nonneg _) (by positivity)) (by ring)
  refine (integrableOn_union.mpr ⟨h1, h2⟩).mono_set fun x hx => ?_
  by_cases hxX : x ≤ X'
  · exact Or.inl ⟨le_of_lt hx, hxX⟩
  · exact Or.inr (lt_of_not_ge hxX)

/-- The integrals over the right sides `Re s = N + 1/2` tend to `0`. -/
theorem struveLoop_tendsto_vertical (ν : ℂ) {z : ℂ} (hz : z ≠ 0) {h : ℝ} (hh : 0 < h) :
    Tendsto (fun N : ℕ => ∫ y : ℝ in (-h)..h, struveLoop_F ν z (((N + 1 / 2 : ℝ) : ℂ) + y * I))
      atTop (𝓝 0) := by
  obtain ⟨X, K, hK⟩ := struveLoop_tail_bound ν (struveLoop_w_ne_zero hz) h
  have hbound : ∀ᶠ N : ℕ in atTop, ‖∫ y : ℝ in (-h)..h,
      struveLoop_F ν z (((N + 1 / 2 : ℝ) : ℂ) + y * I)‖ ≤
      π * K * Real.exp (-((N : ℝ) + 1 / 2)) * |h - -h| := by
    obtain ⟨N₀, hN₀⟩ := exists_nat_ge X
    filter_upwards [eventually_ge_atTop N₀] with N hN
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
    rw [Set.uIoc_of_le (by linarith)] at hy
    have hy' : |y| ≤ h := abs_le.mpr ⟨le_of_lt hy.1, hy.2⟩
    have hX : X ≤ (N : ℝ) + 1 / 2 := by
      have : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    rw [struveLoop_F_eq, norm_mul]
    refine le_of_le_of_eq (mul_le_mul ?_ (hK _ hX y hy') (norm_nonneg _) Real.pi_pos.le)
      (by ring)
    have hs := Complex.barnesRes_abs_sin_mul_cosh_le_norm_sin (π * ((N : ℝ) + 1 / 2)) (π * y)
    have hsin : |Real.sin (π * ((N : ℝ) + 1 / 2))| = 1 := by
      rw [mul_add, show π * (1 / 2) = π / 2 by ring, Real.sin_add_pi_div_two,
        show π * (N : ℝ) = N * π by ring, Real.cos_nat_mul_pi, abs_pow, abs_neg, abs_one, one_pow]
    rw [hsin, one_mul] at hs
    have hs1 : 1 ≤ ‖sin (π * ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) + y * I))‖ := by
      refine le_trans (Real.one_le_cosh _) (le_of_le_of_eq hs ?_)
      congr 2; push_cast; ring
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    exact div_le_self Real.pi_pos.le hs1
  refine squeeze_zero_norm' hbound ?_
  have : Tendsto (fun N : ℕ => Real.exp (-((N : ℝ) + 1 / 2))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  simpa using ((this.const_mul (π * K)).mul_const |h - -h|)

/-- The residue series is the Struve `L` series: `∑ Φ_n(n) = struveLCore ν z`. -/
theorem struveLoop_hasSum (ν : ℂ) (z : ℂ) :
    HasSum (fun n : ℕ => struveLoop_num ν z n n) (struveLCore ν z) := by
  convert hasSum_struveLCore ν z using 1
  funext n
  rw [struveLoop_num, struveLoop_D_self, cpow_natCast, struveCoeff,
    show (3 / 2 : ℂ) + n = n + 3 / 2 by ring, show (3 / 2 : ℂ) + ν + n = n + ν + 3 / 2 by ring]
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have h1 : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  have hm : ((-1 : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have e : (-z ^ 2 / 4 : ℂ) ^ n = (-1) ^ n * (z / 2) ^ (2 * n) := by
    rw [pow_mul, ← mul_pow]; congr 1; ring
  rw [e]
  field_simp

end StruveLoop

/-- struveL barnes loop (DLMF 11.5.9): residue theorem on rectangles `[c, N+1/2] × [-h, h]`. -/
@[dlmf 11.5.E9]
theorem struveL_barnes_loop (ν : ℂ) {z : ℂ} (hz : z ≠ 0) {c h : ℝ} (hc : -1 < c) (hc0 : c < 0) (hh : 0 < h) :
    Tendsto (fun R => positiveBarnesLoop (fun s : ℂ => π/sin (π*s)/(Gamma (3/2+s)*Gamma (3/2+ν+s))*(-z^2/4)^s) c h R) atTop (𝓝 (2*π*I*(z/2)^(-ν-1)*struveL ν z)) := by
  change Tendsto (fun R => positiveBarnesLoop (struveLoop_F ν z) c h R) atTop _
  set F := struveLoop_F ν z with hFdef
  have hcont : ∀ t : ℝ, (t = -h ∨ t = h) → Continuous fun x : ℝ => F (x + t * I) := by
    intro t ht
    exact struveLoop_continuous_line ν hz (by rcases ht with rfl | rfl <;> [linarith; linarith])
  have hint : ∀ t : ℝ, (t = -h ∨ t = h) → IntegrableOn (fun x : ℝ => F (x + t * I)) (Ioi c) := by
    intro t ht
    exact struveLoop_integrableOn ν hz c (by rcases ht with rfl | rfl <;> [linarith; linarith])
  -- the loop through the two horizontal integrals
  have hform : ∀ R : ℝ, positiveBarnesLoop F c h R =
      (∫ x : ℝ in c..R, F (x + (-h : ℝ) * I)) - (∫ x : ℝ in c..R, F (x + h * I)) -
        I * ∫ y : ℝ in (-h)..h, F (c + y * I) := by
    intro R
    rw [struveLoop_loop_eq, struveLoop_rect, smul_eq_mul, smul_eq_mul]
    ring
  set Lval := (∫ x : ℝ in Ioi c, F (x + (-h : ℝ) * I)) - (∫ x : ℝ in Ioi c, F (x + h * I)) -
    I * ∫ y : ℝ in (-h)..h, F (c + y * I) with hLval
  have hL : Tendsto (fun R => positiveBarnesLoop F c h R) atTop (𝓝 Lval) := by
    simp_rw [hform]
    exact ((intervalIntegral_tendsto_integral_Ioi c (hint _ (Or.inl rfl)) tendsto_id).sub
      (intervalIntegral_tendsto_integral_Ioi c (hint _ (Or.inr rfl)) tendsto_id)).sub
      tendsto_const_nhds
  -- the residue sums along `R = N + 1/2`
  have hrect := struveLoop_rect_sum (F := F) (Φ := struveLoop_num ν z) hc0 hh hcont
    (fun n => struveLoop_differentiableOn_Φ ν z hc hc0 hz n)
    (fun n s hs => struveLoop_F_eq_Φ ν z hc0 hh n hs)
  have hseq : Tendsto (fun N : ℕ => positiveBarnesLoop F c h ((N : ℝ) + 1 / 2)) atTop
      (𝓝 (2 * π * I * struveLCore ν z)) := by
    have hs := ((struveLoop_hasSum ν z).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).const_mul
      (2 * π * I)
    have hv := (struveLoop_tendsto_vertical ν hz hh).const_mul I
    rw [mul_zero] at hv
    have := hs.sub hv
    rw [sub_zero] at this
    refine this.congr fun N => ?_
    simp only [Function.comp_apply]
    rw [struveLoop_loop_eq, hrect N]
  have hRN : Tendsto (fun N : ℕ => (N : ℝ) + 1 / 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hval : Lval = 2 * π * I * struveLCore ν z := tendsto_nhds_unique (hL.comp hRN) hseq
  have hz2 : z / 2 ≠ 0 := div_ne_zero hz two_ne_zero
  have hpow : (z / 2) ^ (-ν - 1) * (z / 2) ^ (ν + 1) = 1 := by
    rw [← cpow_add _ _ hz2]; simp
  rw [struveL, show 2 * π * I * (z / 2) ^ (-ν - 1) * ((z / 2) ^ (ν + 1) * struveLCore ν z) =
    2 * π * I * struveLCore ν z * ((z / 2) ^ (-ν - 1) * (z / 2) ^ (ν + 1)) by ring, hpow,
    mul_one, ← hval]
  exact hL

end DLMF.Struve
end
