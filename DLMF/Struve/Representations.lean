/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Struve.Properties
public import DLMF.Bessel.YIntegralRep
public import TauCeti.Analysis.Contour.WorkedExamples.HalfDisc.SineIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import DLMF.Bessel.Asymptotics
public import DLMFMathlib.Analysis.Integral.Improper
public import DLMF.Gamma.ShiftedLineBounds
public import DLMF.Struve.BarnesTools

/-!
# Struve integrals and Laplace transforms

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Struve

open DLMF.Bessel

/-- struveH trig integral. -/
@[dlmf 11.5.E1]
theorem struveH_trig_integral {ν : ℂ} (hν : -1/2 < ν.re) {z : ℂ} (hz : z ∈ slitPlane) :
    struveH ν z = 2*(z/2)^ν/(Real.sqrt π*Gamma (ν+1/2)) * ∫ θ : ℝ in 0..π/2, sin (z*Real.cos θ)*(Real.sin θ : ℂ)^(2*ν) := by
  rw [struveH_eq_poisson hν (slitPlane_ne_zero hz),
    integral_poissonWeight_eq_trig ν (fun t => sin (z*t))]

/-- struveL trig integral. -/
@[dlmf 11.5.E6]
theorem struveL_trig_integral {ν : ℂ} (hν : -1/2 < ν.re) {z : ℂ} (hz : z ∈ slitPlane) :
    struveL ν z = 2*(z/2)^ν/(Real.sqrt π*Gamma (ν+1/2)) * ∫ θ : ℝ in 0..π/2, sinh (z*Real.cos θ)*(Real.sin θ : ℂ)^(2*ν) := by
  rw [struveL_eq_poisson hν (slitPlane_ne_zero hz),
    integral_poissonWeight_eq_trig ν (fun t => sinh (z*t))]

/-- struveH integral. -/
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

/-- struveK zero laplace. -/
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

/-- struveM integral. -/
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

/-- struveM zero integral. -/
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
lemma struveFour_cpow_I_mul {x : ℝ} (hx : 0 < x) (w : ℂ) :
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
lemma struveFour_cpow_neg_I_mul {x : ℝ} (hx : 0 < x) (w : ℂ) :
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
lemma struveFour_ratio_I {x : ℝ} (hx : 0 < x) (ν : ℂ) :
    ((x : ℂ) / 2) ^ ν * (I * x / 2) ^ (-ν) = exp (-(I * ν * π / 2)) := by
  have hx2 : ((x : ℂ) / 2) ≠ 0 := div_ne_zero (ofReal_ne_zero.mpr hx.ne') two_ne_zero
  rw [struveFour_cpow_I_mul hx, cpow_neg, ← mul_assoc, mul_inv_cancel₀ (by
    rw [Ne, cpow_eq_zero_iff]; tauto)]
  ring_nf

/-- `(x/2)^ν (-i x/2)^{-ν} = e^{iπν/2}`. -/
lemma struveFour_ratio_neg_I {x : ℝ} (hx : 0 < x) (ν : ℂ) :
    ((x : ℂ) / 2) ^ ν * (-I * x / 2) ^ (-ν) = exp (I * ν * π / 2) := by
  have hx2 : ((x : ℂ) / 2) ≠ 0 := div_ne_zero (ofReal_ne_zero.mpr hx.ne') two_ne_zero
  rw [struveFour_cpow_neg_I_mul hx, cpow_neg, ← mul_assoc, mul_inv_cancel₀ (by
    rw [Ne, cpow_eq_zero_iff]; tauto)]
  ring_nf

/-- The Struve `H` series at `i x` is the Struve `L` series at `x`. -/
lemma struveFour_core_I (ν : ℂ) (x : ℝ) : struveHCore ν (I * x) = struveLCore ν x := by
  rw [struveHCore, struveLCore]
  refine tsum_congr fun n => ?_
  rw [pow_mul, pow_mul, show (I * x / 2) ^ 2 = -(((x : ℂ) / 2) ^ 2) by ring_nf; rw [I_sq]; ring,
    neg_pow (((x : ℂ) / 2) ^ 2), ← mul_assoc, ← mul_pow]
  norm_num

/-- The Struve `H` series at `-i x` is the Struve `L` series at `x`. -/
lemma struveFour_core_neg_I (ν : ℂ) (x : ℝ) : struveHCore ν (-I * x) = struveLCore ν x := by
  rw [struveHCore, struveLCore]
  refine tsum_congr fun n => ?_
  rw [pow_mul, pow_mul, show (-I * x / 2) ^ 2 = -(((x : ℂ) / 2) ^ 2) by ring_nf; rw [I_sq]; ring,
    neg_pow (((x : ℂ) / 2) ^ 2), ← mul_assoc, ← mul_pow]
  norm_num

/-- `H_ν(i x) = i e^{iπν/2} L_ν(x)` for `x > 0`. -/
lemma struveFour_H_I {x : ℝ} (hx : 0 < x) (ν : ℂ) :
    struveH ν (I * x) = I * exp (I * ν * π / 2) * struveL ν x := by
  rw [struveH, struveL, struveFour_core_I, struveFour_cpow_I_mul hx]
  rw [show I * (ν + 1) * π / 2 = I * ν * π / 2 + π / 2 * I by ring, exp_add,
    show (π / 2 * I : ℂ) = ((π / 2 : ℝ) : ℂ) * I by push_cast; ring, exp_pi_div_two_mul_I']
  ring

/-- `H_ν(-i x) = -i e^{-iπν/2} L_ν(x)` for `x > 0`. -/
lemma struveFour_H_neg_I {x : ℝ} (hx : 0 < x) (ν : ℂ) :
    struveH ν (-I * x) = -I * exp (-(I * ν * π / 2)) * struveL ν x := by
  rw [struveH, struveL, struveFour_core_neg_I, struveFour_cpow_neg_I_mul hx]
  rw [show -(I * (ν + 1) * π / 2) = -(I * ν * π / 2) + (-(π / 2) : ℝ) * I by push_cast; ring,
    exp_add, exp_neg_pi_div_two_mul_I']
  ring


/-- `J_μ(i x) = e^{iπμ/2} I_μ(x)` for `x > 0`. -/
lemma struveFour_J_I {x : ℝ} (hx : 0 < x) (μ : ℂ) :
    besselJ μ (I * x) = exp (I * μ * π / 2) * besselI μ x := by
  have hz : I * (x : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hx.ne')
  have harg : arg (I * (x : ℂ)) = π / 2 := by rw [mul_comm, arg_real_mul I hx, arg_I]
  have h := besselI_neg_I_mul hz (by rw [harg]; linarith [Real.pi_pos]) μ
  rw [show -I * (I * (x : ℂ)) = x by ring_nf; rw [I_sq]; ring] at h
  rw [h, ← mul_assoc, ← exp_add]
  simp

/-- `J_μ(-i x) = e^{-iπμ/2} I_μ(x)` for `x > 0`. -/
lemma struveFour_J_neg_I {x : ℝ} (hx : 0 < x) (μ : ℂ) :
    besselJ μ (-I * x) = exp (-(I * μ * π / 2)) * besselI μ x := by
  have hz : -I * (x : ℂ) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (ofReal_ne_zero.mpr hx.ne')
  have harg : arg (-I * (x : ℂ)) = -(π / 2) := by rw [mul_comm, arg_real_mul _ hx, arg_neg_I]
  have h := besselI_I_mul hz (by rw [harg]; linarith [Real.pi_pos]) μ
  rw [show I * (-I * (x : ℂ)) = x by ring_nf; rw [I_sq]; ring] at h
  rw [h, ← mul_assoc, ← exp_add]
  simp

/-- `i x` lies in the slit plane for `x > 0`. -/
lemma struveFour_mem_slitPlane_I {x : ℝ} (hx : 0 < x) : I * (x : ℂ) ∈ slitPlane := by
  right; simp [hx.ne']

/-- `-i x` lies in the slit plane for `x > 0`. -/
lemma struveFour_mem_slitPlane_neg_I {x : ℝ} (hx : 0 < x) : -I * (x : ℂ) ∈ slitPlane := by
  right; simp [hx.ne']

/-- `e^{iπν/2} Y_ν(-ix) - e^{-iπν/2} Y_ν(ix) = -2i I_{-ν}(x)` for all orders `ν`. -/
lemma struveFour_Y {x : ℝ} (hx : 0 < x) (ν : ℂ) :
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
lemma struveFour_value {x : ℝ} (hx : 0 < x) (ν : ℂ) :
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
lemma struveFour_one_add_sq (t : ℝ) : (1 + (t : ℂ) ^ 2) = ((1 + t ^ 2 : ℝ) : ℂ) := by
  push_cast; ring

/-- `1 + t²` lies in the slit plane. -/
lemma struveFour_mem_slitPlane (t : ℝ) : (1 + (t : ℂ) ^ 2) ∈ slitPlane := by
  rw [struveFour_one_add_sq]; exact ofReal_mem_slitPlane.mpr (by positivity)

/-- `t ↦ (1+t²)^w` is continuous. -/
lemma struveFour_continuous_cpow (w : ℂ) : Continuous fun t : ℝ => (1 + (t : ℂ) ^ 2) ^ w :=
  (by fun_prop : Continuous fun t : ℝ => 1 + (t : ℂ) ^ 2).cpow continuous_const
    struveFour_mem_slitPlane

/-- `‖(1+t²)^w‖ = (1+t²)^{re w}`. -/
lemma struveFour_norm_cpow (w : ℂ) (t : ℝ) : ‖(1 + (t : ℂ) ^ 2) ^ w‖ = (1 + t ^ 2) ^ w.re := by
  rw [struveFour_one_add_sq, norm_cpow_eq_rpow_re_of_pos (by positivity)]

/-- Derivative of `t ↦ (1+t²)^w`. -/
lemma struveFour_hasDerivAt_cpow (w : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => (1 + (t : ℂ) ^ 2) ^ w)
      (w * (1 + (t : ℂ) ^ 2) ^ (w - 1) * (2 * t)) t := by
  have h1 : HasDerivAt (fun z : ℂ => 1 + z ^ 2) (2 * (t : ℂ)) (t : ℂ) := by
    simpa using ((hasDerivAt_pow 2 (t : ℂ)).const_add 1)
  have h2 := (h1.cpow_const (c := w) (struveFour_mem_slitPlane t)).comp_ofReal
  simpa using h2

/-- `(1+t²)^s → 0` as `t → ∞` for `s < 0`. -/
lemma struveFour_tendsto_rpow {s : ℝ} (hs : s < 0) :
    Tendsto (fun t : ℝ => (1 + t ^ 2) ^ s) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (y := -s) (by linarith)).comp
    (tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop (two_ne_zero (α := ℕ))))
  simpa [Function.comp_def] using h

/-- `t (1+t²)^{s-1}` is integrable on `(0, ∞)` for `s < 0`. -/
lemma struveFour_integrableOn {s : ℝ} (hs : s < 0) :
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
lemma struveFour_exists {a : ℂ} (ha : a.re < 0) {x : ℝ} (hx : 0 < x) :
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
lemma struveFour_regularized_eq (ν C : ℂ) (x ε t : ℝ) :
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
lemma struveFour_laplace (ν : ℂ) (x : ℝ) {z : ℂ} (hz : 0 < z.re) :
    2 * ((x : ℂ) / 2) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2)) *
      ∫ t in Ioi (0 : ℝ), yLaplaceKernel ν z t =
      ((x : ℂ) / 2) ^ ν * (z / 2) ^ (-ν) * struveK ν z := by
  have hz0 : z / 2 ≠ 0 := div_ne_zero (fun h => by simp [h] at hz) two_ne_zero
  have hp : (z / 2) ^ ν ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; tauto
  rw [struveK_eq_besselYLaplace ν hz, besselYLaplace, cpow_neg]
  field_simp

/-- `ε ↦ (x/2)^ν ((ε + w)/2)^{-ν} K_ν(ε + w)` is continuous at `0` for `w ∈ slitPlane`. -/
lemma struveFour_continuousAt (ν : ℂ) (x : ℝ) {w : ℂ} (hw : w ∈ slitPlane) :
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

/-- struveL fourier. -/
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
lemma struveLoop_rect_recip {a b p h : ℝ} (ha : a < p) (hb : p < b) (hh : 0 < h) :
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
lemma struveLoop_rect_add {f g : ℂ → ℂ} {a b h : ℝ}
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
lemma struveLoop_mem_bdry_h {a b h t x : ℝ} (ht : t = -h ∨ t = h) (hx : x ∈ [[a, b]]) :
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
lemma struveLoop_mem_bdry_v {a b h x y : ℝ} (hx : x = a ∨ x = b) (hy : y ∈ [[-h, h]]) :
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
lemma struveLoop_rect_congr {F G : ℂ → ℂ} {a b h : ℝ} (hFG : EqOn F G (struveLoop_bdry a b h)) :
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
lemma struveLoop_rect_const_mul (F : ℂ → ℂ) (c : ℂ) (a b h : ℝ) :
    struveLoop_rect (fun s => c * F s) a b h = c * struveLoop_rect F a b h := by
  unfold struveLoop_rect
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul]
  ring

/-- **Residue theorem for a rectangle with one simple pole on the real axis.** -/
lemma struveLoop_rect_pole {F Φ : ℂ → ℂ} {a b p h : ℝ} (ha : a < p) (hb : p < b) (hh : 0 < h)
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
lemma struveLoop_loop_eq (F : ℂ → ℂ) (c h R : ℝ) :
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
lemma struveLoop_rect_adj {F : ℂ → ℂ} {a b d h : ℝ}
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
lemma struveLoop_rect_sum {F : ℂ → ℂ} {Φ : ℕ → ℂ → ℂ} {c h : ℝ} (hc0 : c < 0) (hh : 0 < h)
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
lemma struveLoop_tail_bound (ν : ℂ) {w : ℂ} (hw : w ≠ 0) (h : ℝ) :
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
lemma struveLoop_sin_eq_zero {s : ℂ} (hs : sin (π * s) = 0) : ∃ k : ℤ, s = k := by
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hs
  refine ⟨k, ?_⟩
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have := hk; field_simp at this
  linear_combination this

/-- `sin(πs)/(s - n)` is entire. -/
lemma struveLoop_differentiable_D (n : ℕ) : Differentiable ℂ (struveLoop_D n) := by
  have := (differentiableOn_dslope (f := fun u : ℂ => sin (π * u)) (c := (n : ℂ))
    (s := univ) Filter.univ_mem).mpr (by fun_prop)
  exact differentiableOn_univ.mp this

/-- `D_n(s) = sin(πs)/(s - n)` for `s ≠ n`. -/
lemma struveLoop_D_of_ne {n : ℕ} {s : ℂ} (hs : s ≠ n) :
    struveLoop_D n s = sin (π * s) / (s - n) := by
  rw [struveLoop_D, dslope_of_ne _ hs, slope_def_module, smul_eq_mul,
    show (π : ℂ) * n = n * π by ring, Complex.sin_nat_mul_pi, sub_zero, div_eq_inv_mul]

/-- `D_n(n) = π cos(πn) = π (-1)^n`. -/
lemma struveLoop_D_self (n : ℕ) : struveLoop_D n n = π * (-1) ^ n := by
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
lemma struveLoop_D_ne_zero {c h : ℝ} (hc : -1 < c) (hc0 : c < 0) {n : ℕ} {s : ℂ}
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
lemma struveLoop_differentiableOn_Φ (ν z : ℂ) {c h : ℝ} (hc : -1 < c) (hc0 : c < 0) (hz : z ≠ 0) (n : ℕ) :
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
lemma struveLoop_F_eq_Φ (ν z : ℂ) {c h : ℝ} (hc0 : c < 0) (hh : 0 < h) (n : ℕ) {s : ℂ}
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
lemma struveLoop_F_eq (ν z s : ℂ) : struveLoop_F ν z s = π / sin (π * s) *
    ((Gamma (3/2+s))⁻¹ * (Gamma (3/2+ν+s))⁻¹ * (-z^2/4)^s) := by
  simp only [struveLoop_F, div_eq_mul_inv _ (Gamma _ * Gamma _), mul_inv]; ring

/-- `-z²/4 ≠ 0` for `z ≠ 0`. -/
lemma struveLoop_w_ne_zero {z : ℂ} (hz : z ≠ 0) : -z ^ 2 / 4 ≠ 0 := by
  have := pow_ne_zero 2 hz; intro h0; apply this; linear_combination -4 * h0

/-- The entire factor `w^s/(Γ(3/2+s)Γ(3/2+ν+s))` is continuous. -/
lemma struveLoop_continuous_G (ν : ℂ) {z : ℂ} (hz : z ≠ 0) :
    Continuous fun s : ℂ => (Gamma (3/2+s))⁻¹ * (Gamma (3/2+ν+s))⁻¹ * (-z^2/4)^s := by
  have hg1 : Differentiable ℂ fun s : ℂ => (Gamma (3/2+s))⁻¹ := fun s =>
    (differentiable_one_div_Gamma (3/2+s)).comp s ((differentiableAt_id).const_add _)
  have hg2 : Differentiable ℂ fun s : ℂ => (Gamma (3/2+ν+s))⁻¹ := fun s =>
    (differentiable_one_div_Gamma (3/2+ν+s)).comp s ((differentiableAt_id).const_add _)
  exact (hg1.continuous.mul hg2.continuous).mul (continuous_const_cpow' (struveLoop_w_ne_zero hz))

/-- The integrand is continuous on every horizontal line off the real axis. -/
lemma struveLoop_continuous_line (ν : ℂ) {z : ℂ} (hz : z ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    Continuous fun x : ℝ => struveLoop_F ν z (x + t * I) := by
  simp_rw [struveLoop_F_eq]
  refine Continuous.mul (Continuous.div continuous_const (by fun_prop) fun x h0 => ?_)
    ((struveLoop_continuous_G ν hz).comp (by fun_prop))
  obtain ⟨k, hk⟩ := struveLoop_sin_eq_zero h0
  apply ht; simpa using congrArg Complex.im hk

/-- `|π/sin(π(x+it))| ≤ π/|sinh(πt)|`. -/
lemma struveLoop_norm_pi_div_sin_le_line {x t : ℝ} (ht : t ≠ 0) :
    ‖(π : ℂ) / sin (π * (x + t * I))‖ ≤ π / |Real.sinh (π * t)| := by
  have hs := Complex.barnesRes_abs_sinh_le_norm_sin (π * x) (π * t)
  have hpos : 0 < |Real.sinh (π * t)| := by
    rw [abs_pos, Real.sinh_ne_zero]; exact mul_ne_zero Real.pi_ne_zero ht
  rw [show (π : ℂ) * (x + t * I) = ((π * x : ℝ) : ℂ) + ((π * t : ℝ) : ℂ) * I by push_cast; ring,
    norm_div, norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  exact div_le_div_of_nonneg_left Real.pi_pos.le hpos hs

/-- The integrand is integrable on horizontal half-lines `Re s > c`, `Im s = t ≠ 0`. -/
lemma struveLoop_integrableOn (ν : ℂ) {z : ℂ} (hz : z ≠ 0) (c : ℝ) {t : ℝ} (ht : t ≠ 0) :
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
lemma struveLoop_tendsto_vertical (ν : ℂ) {z : ℂ} (hz : z ≠ 0) {h : ℝ} (hh : 0 < h) :
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
lemma struveLoop_hasSum (ν : ℂ) (z : ℂ) :
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

/-! ### The Barnes integral for `H_ν` (DLMF 11.5.8) -/

/-- `-(ix)²/4 = x²/4`. -/
lemma struveBar_w (x : ℝ) : -(I * x) ^ 2 / 4 = ((x ^ 2 / 4 : ℝ) : ℂ) := by
  push_cast; ring_nf; rw [I_sq]; ring

/-- The modulus of the 11.5.8 integrand `F(s)` at `s = t + iy`. -/
lemma struveBar_norm_F (ν : ℂ) {x : ℝ} (hx : 0 < x) (t y : ℝ) :
    ‖struveLoop_F ν (I * x) (t + y * I)‖ = (x ^ 2 / 4) ^ t * (π / ‖sin (π * ((t : ℂ) + y * I))‖ *
      (‖Gamma (((3 / 2 + t : ℝ) : ℂ) + y * I)‖)⁻¹ *
      (‖Gamma (((3 / 2 + ν.re + t : ℝ) : ℂ) + ((y : ℂ) + ν.im) * I)‖)⁻¹) := by
  have e1 : (3 / 2 : ℂ) + (t + y * I) = ((3 / 2 + t : ℝ) : ℂ) + y * I := by push_cast; ring
  have e2 : (3 / 2 : ℂ) + ν + (t + y * I) =
      ((3 / 2 + ν.re + t : ℝ) : ℂ) + ((y : ℂ) + ν.im) * I := by
    apply Complex.ext <;> simp; ring
  simp only [struveLoop_F]
  rw [struveBar_w, e1, e2, norm_mul, norm_div, norm_div, norm_mul,
    norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp only [norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, add_re, ofReal_re, mul_re,
    I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]
  rw [div_eq_mul_inv _ (_ * _), mul_inv]
  ring

/-- The modulus of the 11.5.8 integrand at `s = t - iy`, by conjugation. -/
lemma struveBar_norm_F_neg (ν : ℂ) {x : ℝ} (hx : 0 < x) (t y : ℝ) :
    ‖struveLoop_F ν (I * x) (t + (-y : ℝ) * I)‖ = (x ^ 2 / 4) ^ t *
      (π / ‖sin (π * ((t : ℂ) + y * I))‖ * (‖Gamma (((3 / 2 + t : ℝ) : ℂ) + y * I)‖)⁻¹ *
      (‖Gamma (((3 / 2 + ν.re + t : ℝ) : ℂ) + ((y : ℂ) + ((-ν.im : ℝ) : ℂ)) * I)‖)⁻¹) := by
  rw [struveBar_norm_F ν hx]
  have h1 : (π : ℂ) * ((t : ℂ) + ((-y : ℝ) : ℂ) * I) = (starRingEnd ℂ) (π * ((t : ℂ) + y * I)) := by
    apply Complex.ext <;> simp
  have h2 : ((3 / 2 + t : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I =
      (starRingEnd ℂ) (((3 / 2 + t : ℝ) : ℂ) + y * I) := by
    rw [map_add, map_mul, conj_ofReal, conj_ofReal, conj_I]; push_cast; ring
  have h3 : ((3 / 2 + ν.re + t : ℝ) : ℂ) + ((((-y : ℝ) : ℂ)) + ν.im) * I =
      (starRingEnd ℂ) (((3 / 2 + ν.re + t : ℝ) : ℂ) + ((y : ℂ) + ((-ν.im : ℝ) : ℂ)) * I) := by
    rw [map_add, map_mul, map_add, conj_ofReal, conj_ofReal, conj_ofReal, conj_I]; push_cast; ring
  rw [h1, h2, h3, sin_conj, Gamma_conj, Gamma_conj, norm_conj, norm_conj, norm_conj]

/-- **The horizontal sides vanish.** If `‖G h t‖` is the modulus of the 11.5.8 integrand at
`t ± ih` (with shift `m = ±Im ν`), then `∫_{(c,∞)} G h → 0` as `h → ∞`: dominated convergence
with the uniform bounds `DLMF.Gamma.shiftB_norm_recip_Gamma_le` and the pointwise Stirling decay
`struveBar_isBigO`. -/
lemma struveBar_tendsto_horizontal (ν : ℂ) {x c : ℝ} (hx : 0 < x) (hc : -1 < c) (hc0 : c < 0)
    (hv : -1 < ν.re + 2 * c) (m : ℝ) (G : ℝ → ℝ → ℂ)
    (hG : ∀ h t : ℝ, ‖G h t‖ = (x ^ 2 / 4) ^ t * (π / ‖sin (π * ((t : ℂ) + h * I))‖ *
      (‖Gamma (((3 / 2 + t : ℝ) : ℂ) + h * I)‖)⁻¹ *
      (‖Gamma (((3 / 2 + ν.re + t : ℝ) : ℂ) + ((h : ℂ) + m) * I)‖)⁻¹))
    (hGc : ∀ h : ℝ, 1 ≤ h → Continuous (G h)) :
    Tendsto (fun h => ∫ t in Ioi c, G h t) atTop (𝓝 0) := by
  have hw : 0 < x ^ 2 / 4 := by positivity
  set D : ℝ → ℝ := fun t => 4 * π * Real.exp (π * |m| / 2) *
    ((x ^ 2 / 4) ^ t / (Real.Gamma (3 / 2 + t) * Real.Gamma (3 / 2 + ν.re + t))) with hD
  have hDi : IntegrableOn D (Ioi c) :=
    (struveBar_integrableOn_rpow_div_Gamma (α := 3 / 2) (β := 3 / 2 + ν.re) (by linarith)
      (by linarith) hw).const_mul _
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioi c))
    (F := fun h t => G h t) (f := fun _ => (0 : ℂ)) (l := atTop) D ?_ ?_ hDi ?_
  · simpa using hlim
  · filter_upwards [eventually_ge_atTop 1] with h hh
    exact (hGc h hh).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop 1] with h hh
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht' : c < t := ht
    rw [hG]
    have ha : 1 / 2 ≤ 3 / 2 + t := by linarith
    have hb : 1 / 2 ≤ 3 / 2 + ν.re + t := by linarith
    have hGa := Real.Gamma_pos_of_pos (by linarith : (0 : ℝ) < 3 / 2 + t)
    have hGb := Real.Gamma_pos_of_pos (by linarith : (0 : ℝ) < 3 / 2 + ν.re + t)
    have g1 := DLMF.Gamma.shiftB_norm_recip_Gamma_le ha h
    have g2 := DLMF.Gamma.shiftB_norm_recip_Gamma_le hb (h + m)
    rw [norm_inv] at g1 g2
    have e : ((h : ℂ) + m) = ((h + m : ℝ) : ℂ) := by push_cast; ring
    rw [e]
    have hS := struveBar_pi_div_sin_le t hh
    have hexp : Real.exp (-(π * h)) * Real.exp (π * |h| / 2) * Real.exp (π * |h + m| / 2) ≤
        Real.exp (π * |m| / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 : |h| = h := abs_of_nonneg (by linarith)
      have h2 : |h + m| ≤ h + |m| := (abs_add_le h m).trans (by rw [h1])
      rw [h1]; nlinarith [Real.pi_pos]
    calc (x ^ 2 / 4) ^ t * (π / ‖sin (π * ((t : ℂ) + h * I))‖ *
          (‖Gamma (((3 / 2 + t : ℝ) : ℂ) + h * I)‖)⁻¹ *
          (‖Gamma (((3 / 2 + ν.re + t : ℝ) : ℂ) + ((h + m : ℝ) : ℂ) * I)‖)⁻¹)
        ≤ (x ^ 2 / 4) ^ t * (4 * π * Real.exp (-(π * h)) *
          (Real.exp (π * |h| / 2) / Real.Gamma (3 / 2 + t)) *
          (Real.exp (π * |h + m| / 2) / Real.Gamma (3 / 2 + ν.re + t))) := by
          gcongr
      _ = 4 * π * (Real.exp (-(π * h)) * Real.exp (π * |h| / 2) * Real.exp (π * |h + m| / 2)) *
          ((x ^ 2 / 4) ^ t / (Real.Gamma (3 / 2 + t) * Real.Gamma (3 / 2 + ν.re + t))) := by
          field_simp
      _ ≤ D t := by
          simp only [hD]
          gcongr
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht' : c < t := ht
    have hO := struveBar_isBigO t (3 / 2 + t) (3 / 2 + ν.re + t) m
    have hq : 0 < 2 + ν.re + 2 * t := by linarith
    have hO' : (fun h : ℝ => G h t) =O[atTop] fun h : ℝ => h ^ (-(2 + ν.re + 2 * t)) := by
      refine Asymptotics.IsBigO.of_norm_left ?_
      simp_rw [hG]
      have := hO.const_mul_left ((x ^ 2 / 4) ^ t)
      rw [show (1 - (3 / 2 + t) - (3 / 2 + ν.re + t)) = -(2 + ν.re + 2 * t) by ring] at this
      exact this
    exact hO'.trans_tendsto (tendsto_rpow_neg_atTop hq)

/-- `L_ν`'s normalized series at `iz` is `H_ν`'s at `z`. -/
lemma struveBar_LCore_I (ν z : ℂ) : struveLCore ν (I * z) = struveHCore ν z := by
  unfold struveLCore struveHCore
  congr 1; funext n
  have e : (I * z / 2) ^ 2 = -1 * (z / 2) ^ 2 := by ring_nf; rw [I_sq]; ring
  rw [pow_mul, pow_mul, e, mul_pow]
  ring

/-- The 11.5.8 integrand is continuous on the vertical line `Re s = c`, `-1 < c < 0`. -/
lemma struveBar_continuous_vertical (ν : ℂ) {x c : ℝ} (hx : 0 < x) (hc : -1 < c) (hc0 : c < 0) :
    Continuous fun y : ℝ => struveLoop_F ν (I * x) (c + y * I) := by
  have hz : I * (x : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hx.ne')
  simp_rw [struveLoop_F_eq]
  refine Continuous.mul (Continuous.div continuous_const (by fun_prop) fun y h0 => ?_)
    ((struveLoop_continuous_G ν hz).comp (by fun_prop))
  obtain ⟨k, hk⟩ := struveLoop_sin_eq_zero h0
  have hre : c = (k : ℝ) := by simpa using congrArg Complex.re hk
  have h1 : (-1 : ℝ) < k := hre ▸ hc
  have h2 : (k : ℝ) < 0 := hre ▸ hc0
  have h1' : (-1 : ℤ) < k := by exact_mod_cast h1
  have h2' : k < 0 := by exact_mod_cast h2
  omega

/-- The 11.5.8 integrand is integrable on the vertical line: it is `O(|y|^{-2-Re ν-2c})`. -/
lemma struveBar_integrable_vertical (ν : ℂ) {x c : ℝ} (hx : 0 < x) (hc : -1 < c) (hc0 : c < 0)
    (hv : -1 < ν.re + 2 * c) :
    Integrable fun y : ℝ => struveLoop_F ν (I * x) (c + y * I) := by
  have hp : -(2 + ν.re + 2 * c) < -1 := by linarith
  have e : (1 - (3 / 2 + c) - (3 / 2 + ν.re + c)) = -(2 + ν.re + 2 * c) := by ring
  refine struveBar_integrable_of_isBigO (struveBar_continuous_vertical ν hx hc hc0) hp ?_ ?_
  · refine Asymptotics.IsBigO.of_norm_left ?_
    simp_rw [struveBar_norm_F ν hx]
    have := (struveBar_isBigO c (3 / 2 + c) (3 / 2 + ν.re + c) ν.im).const_mul_left
      ((x ^ 2 / 4) ^ c)
    rwa [e] at this
  · refine Asymptotics.IsBigO.of_norm_left ?_
    simp_rw [struveBar_norm_F_neg ν hx]
    have := (struveBar_isBigO c (3 / 2 + c) (3 / 2 + ν.re + c) (-ν.im)).const_mul_left
      ((x ^ 2 / 4) ^ c)
    rwa [e] at this

/-- The closed rectangle identity at height `h`, after `R → ∞`: the two horizontal half-line
integrals and the vertical segment give `2πi` times the residue sum `H`-core. -/
lemma struveBar_rect_identity (ν : ℂ) {x c h : ℝ} (hx : 0 < x) (hc : -1 < c) (hc0 : c < 0)
    (hh : 0 < h) :
    (∫ t in Ioi c, struveLoop_F ν (I * x) (t + (-h : ℝ) * I)) -
      (∫ t in Ioi c, struveLoop_F ν (I * x) (t + h * I)) -
      I * ∫ y in (-h)..h, struveLoop_F ν (I * x) (c + y * I) = 2 * π * I * struveHCore ν x := by
  have hz : I * (x : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hx.ne')
  set F := struveLoop_F ν (I * x) with hFdef
  have hloop := struveL_barnes_loop ν hz hc hc0 hh
  change Tendsto (fun R => positiveBarnesLoop F c h R) atTop _ at hloop
  have hint : ∀ t : ℝ, t ≠ 0 → IntegrableOn (fun x : ℝ => F (x + t * I)) (Ioi c) :=
    fun t ht => struveLoop_integrableOn ν hz c ht
  have hform : ∀ R : ℝ, positiveBarnesLoop F c h R =
      (∫ x : ℝ in c..R, F (x + (-h : ℝ) * I)) - (∫ x : ℝ in c..R, F (x + h * I)) -
        I * ∫ y : ℝ in (-h)..h, F (c + y * I) := by
    intro R
    rw [struveLoop_loop_eq, struveLoop_rect, smul_eq_mul, smul_eq_mul]
    ring
  have hL : Tendsto (fun R => positiveBarnesLoop F c h R) atTop
      (𝓝 ((∫ t in Ioi c, F (t + (-h : ℝ) * I)) - (∫ t in Ioi c, F (t + h * I)) -
        I * ∫ y in (-h)..h, F (c + y * I))) := by
    simp_rw [hform]
    exact ((intervalIntegral_tendsto_integral_Ioi c (hint _ (by linarith)) tendsto_id).sub
      (intervalIntegral_tendsto_integral_Ioi c (hint _ hh.ne') tendsto_id)).sub
      tendsto_const_nhds
  rw [tendsto_nhds_unique hL hloop, struveL, struveBar_LCore_I]
  have hz2 : I * (x : ℂ) / 2 ≠ 0 := div_ne_zero hz two_ne_zero
  have hpow : (I * (x : ℂ) / 2) ^ (-ν - 1) * (I * (x : ℂ) / 2) ^ (ν + 1) = 1 := by
    rw [← cpow_add _ _ hz2]; simp
  linear_combination (2 * π * I * struveHCore ν x) * hpow

/-- struveH barnes (DLMF 11.5.8). Proof: the residue theorem on the rectangles
`[c, N + 1/2] × [-h, h]` (as for 11.5.9, `struveL_barnes_loop` at `z = ix`) gives the identity
`struveBar_rect_identity` for every height `h`; the horizontal half-line integrals tend to `0` as
`h → ∞` by dominated convergence (`struveBar_tendsto_horizontal`), and the vertical integrand is
`O(|y|^{-2-Re ν-2c})` by Stirling's formula on vertical lines, hence integrable
(`struveBar_integrable_vertical`). A 30-digit numerical check (2026-10-22) is recorded in
REVIEW.md. -/
@[dlmf 11.5.E8]
theorem struveH_barnes {ν : ℂ} (hν : -1 < ν.re) {x c : ℝ} (hx : 0 < x) (hc : -1 < c) (hc0 : c < 0) (hv : -1 < ν.re+2*c) :
    HasIntegralWholeLine (fun y : ℝ => let s : ℂ := c+y*I; π/sin (π*s)/(Gamma (3/2+s)*Gamma (3/2+ν+s))*(x^2/4:ℂ)^s) (-2*π*(x/2:ℂ)^(-ν-1)*struveH ν x) := by
  set f : ℝ → ℂ := fun y => struveLoop_F ν (I * x) (c + y * I) with hfdef
  have hfe : (fun y : ℝ => let s : ℂ := c+y*I; π/sin (π*s)/(Gamma (3/2+s)*Gamma (3/2+ν+s))*(x^2/4:ℂ)^s) = f := by
    funext y
    simp only [hfdef, struveLoop_F]
    congr 2
    ring_nf; rw [I_sq]; ring
  have hval : -2*π*(x/2:ℂ)^(-ν-1)*struveH ν x = -2 * π * struveHCore ν x := by
    have hx2 : (x : ℂ) / 2 ≠ 0 := div_ne_zero (ofReal_ne_zero.mpr hx.ne') two_ne_zero
    have hpow : ((x : ℂ) / 2) ^ (-ν - 1) * ((x : ℂ) / 2) ^ (ν + 1) = 1 := by
      rw [← cpow_add _ _ hx2]; simp
    rw [struveH]
    linear_combination (-2 * π * struveHCore ν x) * hpow
  rw [hfe, hval]
  have hfi : Integrable f := struveBar_integrable_vertical ν hx hc hc0 hv
  -- the symmetric integrals
  have hJ : Tendsto (fun h : ℝ => ∫ y in (-h)..h, f y) atTop (𝓝 (-2 * π * struveHCore ν x)) := by
    have hP := struveBar_tendsto_horizontal ν hx hc hc0 hv ν.im
      (fun h t => struveLoop_F ν (I * x) (t + h * I))
      (fun h t => struveBar_norm_F ν hx t h)
      (fun h hh => struveLoop_continuous_line ν (mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hx.ne'))
        (by linarith))
    have hM := struveBar_tendsto_horizontal ν hx hc hc0 hv (-ν.im)
      (fun h t => struveLoop_F ν (I * x) (t + (-h : ℝ) * I))
      (fun h t => struveBar_norm_F_neg ν hx t h)
      (fun h hh => struveLoop_continuous_line ν (mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hx.ne'))
        (by linarith))
    have hlim := ((hM.sub hP).sub (tendsto_const_nhds (x := 2 * π * I * struveHCore ν x))).const_mul (-I)
    have e : -I * ((0 : ℂ) - 0 - 2 * π * I * struveHCore ν x) = -2 * π * struveHCore ν x := by
      ring_nf; rw [I_sq]; ring
    rw [e] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with h hh
    have := struveBar_rect_identity ν hx hc hc0 hh
    simp only [hfdef]
    linear_combination (-I) * this - (I_sq) * (∫ y in (-h)..h, struveLoop_F ν (I * x) (c + y * I))
  have hint := intervalIntegral_tendsto_integral hfi tendsto_neg_atTop_atBot tendsto_id
  have hI : ∫ y, f y = -2 * π * struveHCore ν x := tendsto_nhds_unique hint hJ
  rw [← hI]
  exact ⟨_, _, intervalIntegral_tendsto_integral_Iic 0 hfi.integrableOn tendsto_id,
    intervalIntegral_tendsto_integral_Ioi 0 hfi.integrableOn tendsto_id,
    intervalIntegral.integral_Iic_add_Ioi hfi.integrableOn hfi.integrableOn⟩


/-- struveHPrimitive. -/
@[dlmf 11.7.E5]
def struveHPrimitive (ν z : ℂ) : ℂ :=
  primitive (fun t => t^ν*struveH ν t) z

/-- A positive real multiple of a slit-plane point lies in the slit plane. -/
theorem ofReal_mul_mem_slitPlane {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z ∈ slitPlane) :
    (s:ℂ)*z ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hz ⊢
  rcases hz with h | h
  · left; simp; positivity
  · right; simp; exact ⟨hs.ne', h⟩

/-- Derivative of the antiderivative used in the primitive recurrence. -/
theorem hasDerivAt_struveHPrimitive_aux {ν : ℂ} (hν1 : ν + 1 ≠ 0) {w : ℂ} (hw : w ∈ slitPlane) :
    HasDerivAt (fun w : ℂ => -(w^(ν+1)*struveH ν w) +
        w^(2*ν+2)/(2^(ν+1)*(ν+1)*Real.sqrt π*Gamma (ν+3/2)))
      (w^(ν+1)*struveH (ν+1) w - (2*ν+1)*(w^ν*struveH ν w)) w := by
  have hw0 := slitPlane_ne_zero hw
  have h28 := struveH_weighted_deriv_28 ν hw
  have hp := (hasStrictDerivAt_cpow_const (c := 2*ν+1) hw).hasDerivAt
  have hprod := hp.mul h28
  have heq : (fun u : ℂ => u^(2*ν+1) * (u^(-1*ν) * struveH ν u)) =ᶠ[𝓝 w]
      fun u => u^(ν+1)*struveH ν u := by
    filter_upwards [isOpen_slitPlane.mem_nhds hw] with u hu
    rw [← mul_assoc, ← cpow_add _ _ (slitPlane_ne_zero hu)]; ring_nf
  have hA := hprod.congr_of_eventuallyEq heq.symm
  have hB := (hasStrictDerivAt_cpow_const (c := 2*ν+2) hw).hasDerivAt.div_const
    (2^(ν+1)*(ν+1)*Real.sqrt π*Gamma (ν+3/2))
  refine (hA.neg.add hB).congr_deriv ?_
  have e1 : w^(2*ν+1-1) * w^(-1*ν) = w^ν := by
    rw [← cpow_add _ _ hw0]; ring_nf
  have e2 : w^(2*ν+1) * w^(-ν) = w^(ν+1) := by
    rw [← cpow_add _ _ hw0]; ring_nf
  have e3 : w^(2*ν+2-1) = w^(2*ν+1) := by ring_nf
  have key : (2*ν+2)/(2^(ν+1)*(ν+1)*Real.sqrt π*Gamma (ν+3/2)) =
      2^(-ν)/(Real.sqrt π*Gamma (ν+3/2)) := by
    rw [cpow_neg, cpow_add _ _ two_ne_zero, cpow_one]
    have h2 : (2:ℂ)^ν ≠ 0 := cpow_ne_zero_iff.2 (Or.inl two_ne_zero)
    by_cases hg : (Real.sqrt π:ℂ)*Gamma (ν+3/2) = 0
    · rw [hg, div_zero, show (2:ℂ)^ν*2*(ν+1)*Real.sqrt π*Gamma (ν+3/2) =
        2^ν*2*(ν+1)*((Real.sqrt π)*Gamma (ν+3/2)) by ring, hg, mul_zero, div_zero]
    · field_simp
  rw [e3]
  have : (2*ν+2) * w^(2*ν+1) / (2^(ν+1)*(ν+1)*Real.sqrt π*Gamma (ν+3/2)) =
      w^(2*ν+1) * (2^(-ν)/(Real.sqrt π*Gamma (ν+3/2))) := by
    rw [← key]; ring
  rw [this]
  linear_combination (-(2*ν+1)*struveH ν w) * e1 + struveH (ν+1) w * e2

/-- The power of z squared carries twice the argument of z, and is expressed using the inherited logarithm. -/
@[dlmf 11.7.E6]
theorem struveHPrimitive_recurrence {ν : ℂ} (hν : -1 < ν.re) {z : ℂ} (hz : z ∈ slitPlane) :
    struveHPrimitive (ν+1) z = (2*ν+1)*struveHPrimitive ν z-z^(ν+1)*struveH ν z+exp ((ν+1)*(2*log z-log 2))/((ν+1)*Real.sqrt π*Gamma (ν+3/2)) := by
  have hν1 : ν+1 ≠ 0 := fun h => by have := congrArg re h; simp at this; linarith
  have hν2 : 2*ν+2 ≠ 0 := fun h => hν1 (by linear_combination h/2)
  have hz0 := slitPlane_ne_zero hz
  set D : ℂ := 2^(ν+1)*(ν+1)*Real.sqrt π*Gamma (ν+3/2) with hD
  set G : ℂ → ℂ := fun w => -(w^(ν+1)*struveH ν w) + w^(2*ν+2)/D with hG
  have hcore : ∀ μ : ℂ, Continuous (struveHCore μ) := fun μ => (entire_struveHCore μ).continuous
  have hf : ∀ μ : ℂ, ∀ s : ℝ, 0 < s → ((s:ℂ)*z)^μ * struveH μ ((s:ℂ)*z) =
      (s:ℂ)^(2*μ+1) * (z^μ*(z/2)^(μ+1)*struveHCore μ ((s:ℂ)*z)) := by
    intro μ s hs
    rw [struveH, show (s:ℂ)*z/2 = (s:ℂ)*(z/2) by ring, DLMF.Confluent.ofReal_mul_cpow' hs hz0,
      DLMF.Confluent.ofReal_mul_cpow' hs (div_ne_zero hz0 two_ne_zero)]
    have : (s:ℂ)^(2*μ+1) = (s:ℂ)^μ * (s:ℂ)^(μ+1) := by
      rw [← cpow_add _ _ (ofReal_ne_zero.2 hs.ne')]; ring_nf
    rw [this]; ring
  have hint : ∀ μ : ℂ, -1 < μ.re →
      IntervalIntegrable (fun s : ℝ => ((s:ℂ)*z)^μ * struveH μ ((s:ℂ)*z)) volume 0 1 := by
    intro μ hμ
    have h1 : IntervalIntegrable (fun s : ℝ => (s:ℂ)^(2*μ+1)) volume 0 1 :=
      intervalIntegral.intervalIntegrable_cpow' (by simp; linarith)
    have hc : Continuous fun s : ℝ => z^μ*(z/2)^(μ+1)*struveHCore μ ((s:ℂ)*z) :=
      continuous_const.mul ((hcore μ).comp (by fun_prop))
    have h2 := h1.mul_continuousOn hc.continuousOn
    refine h2.congr fun s hs => ?_
    rw [uIoc_of_le zero_le_one] at hs
    exact (hf μ s hs.1).symm
  set ψ : ℝ → ℂ := fun s => -(z^(ν+1)*(z/2)^(ν+1)*struveHCore ν ((s:ℂ)*z)) + z^(2*ν+2)/D
  have hφ : ∀ s : ℝ, 0 ≤ s → G ((s:ℂ)*z) = (s:ℂ)^(2*ν+2) * ψ s := by
    intro s hs
    rcases hs.eq_or_lt with h0 | hpos
    · subst h0
      simp only [G, ψ, ofReal_zero, zero_mul, zero_cpow hν1, zero_cpow hν2]
      ring
    · simp only [G, ψ]
      rw [struveH, show (s:ℂ)*z/2 = (s:ℂ)*(z/2) by ring, DLMF.Confluent.ofReal_mul_cpow' hpos hz0,
        DLMF.Confluent.ofReal_mul_cpow' hpos (div_ne_zero hz0 two_ne_zero),
        DLMF.Confluent.ofReal_mul_cpow' hpos hz0]
      have : (s:ℂ)^(2*ν+2) = (s:ℂ)^(ν+1) * (s:ℂ)^(ν+1) := by
        rw [← cpow_add _ _ (ofReal_ne_zero.2 hpos.ne')]; ring_nf
      rw [this]; ring
  have hcontφ : ContinuousOn (fun s : ℝ => G ((s:ℂ)*z)) (Icc 0 1) := by
    have hψ : Continuous ψ :=
      (continuous_const.mul ((hcore ν).comp (by fun_prop))).neg.add continuous_const
    have : ContinuousOn (fun s : ℝ => (s:ℂ)^(2*ν+2) * ψ s) (Icc 0 1) := fun s _ =>
      ((continuousAt_ofReal_cpow_const s _ (Or.inl (by simp; linarith))).mul
        hψ.continuousAt).continuousWithinAt
    exact this.congr fun s hs => hφ s hs.1
  have hderiv : ∀ s ∈ Ioo (0:ℝ) 1, HasDerivAt (fun s : ℝ => G ((s:ℂ)*z))
      (z * (((s:ℂ)*z)^(ν+1)*struveH (ν+1) ((s:ℂ)*z) -
        (2*ν+1)*(((s:ℂ)*z)^ν*struveH ν ((s:ℂ)*z)))) s := by
    intro s hs
    have h1 := hasDerivAt_struveHPrimitive_aux hν1 (ofReal_mul_mem_slitPlane hs.1 hz)
    have h2 : HasDerivAt (fun s : ℝ => (s:ℂ)*z) z s :=
      ((hasDerivAt_id s).ofReal_comp.mul_const z).congr_deriv (by simp)
    refine (h1.comp s h2).congr_deriv ?_
    ring
  have hII := ((hint (ν+1) (by simp; linarith)).sub ((hint ν hν).const_mul (2*ν+1))).const_mul z
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcontφ hderiv hII
  have hP : ∀ μ, struveHPrimitive μ z =
      z * ∫ s : ℝ in 0..1, ((s:ℂ)*z)^μ*struveH μ ((s:ℂ)*z) := by
    intro μ; simp [struveHPrimitive, primitive, segmentIntegral]
  have hG0 : G (((0:ℝ):ℂ)*z) = 0 := by
    rw [hφ 0 le_rfl, ofReal_zero, zero_cpow hν2, zero_mul]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (hint (ν+1)
    (by simp; linarith)) ((hint ν hν).const_mul (2*ν+1)), intervalIntegral.integral_const_mul,
    hG0, ofReal_one, one_mul] at hFTC
  rw [hP, hP]
  have hexp : exp ((ν+1)*(2*log z-log 2)) = z^(2*ν+2)/2^(ν+1) := by
    rw [cpow_def_of_ne_zero hz0, cpow_def_of_ne_zero two_ne_zero, ← Complex.exp_sub]; ring_nf
  rw [hexp]
  simp only [G, hD] at hFTC
  have hsplit : z^(2*ν+2)/(2^(ν+1)*(ν+1)*Real.sqrt π*Gamma (ν+3/2)) =
      z^(2*ν+2)/2^(ν+1)/((ν+1)*Real.sqrt π*Gamma (ν+3/2)) := by
    rw [div_div, ← mul_assoc, ← mul_assoc]
  rw [hsplit] at hFTC
  linear_combination hFTC

/-- `sin²` maps `(0, π/2)` onto `(0, 1)`. -/
theorem sin_sq_image_Ioo : (fun θ : ℝ => Real.sin θ^2) '' Ioo 0 (π/2) = Ioo 0 1 := by
  ext x; constructor
  · rintro ⟨θ, ⟨h0, h1⟩, rfl⟩
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
    have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, h1⟩
    have := Real.sin_sq_add_cos_sq θ
    exact ⟨by positivity, by nlinarith⟩
  · rintro ⟨h0, h1⟩
    refine ⟨Real.arcsin (Real.sqrt x), ⟨Real.arcsin_pos.2 (Real.sqrt_pos.2 h0), ?_⟩, ?_⟩
    · rw [Real.arcsin_lt_pi_div_two, Real.sqrt_lt' one_pos]; simpa using h1
    · show Real.sin (Real.arcsin (Real.sqrt x))^2 = x
      rw [Real.sin_arcsin (by linarith [Real.sqrt_nonneg x]) (by
        rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt h1.le), Real.sq_sqrt h0.le]

/-- `sin²` is injective on `(0, π/2)`. -/
theorem sin_sq_injOn : InjOn (fun θ : ℝ => Real.sin θ^2) (Ioo 0 (π/2)) := by
  intro a ha b hb hab
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha.1 (by linarith [ha.2, Real.pi_pos])
  have hsb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb.1 (by linarith [hb.2, Real.pi_pos])
  have : Real.sin a = Real.sin b := by
    simp only at hab; nlinarith [sq_nonneg (Real.sin a - Real.sin b)]
  exact Real.injOn_sin ⟨by linarith [ha.1, Real.pi_pos], ha.2.le⟩
    ⟨by linarith [hb.1, Real.pi_pos], hb.2.le⟩ this

/-- Derivative of `sin²`. -/
theorem hasDerivWithinAt_sin_sq (θ : ℝ) :
    HasDerivWithinAt (fun θ : ℝ => Real.sin θ^2) (2*Real.sin θ*Real.cos θ) (Ioo 0 (π/2)) θ := by
  have := ((Real.hasDerivAt_sin θ).pow 2).hasDerivWithinAt (s := Ioo 0 (π/2))
  convert this using 1; push_cast; ring

/-- The weight `sin^(2a-1) θ cos^(2b-1) θ` after the substitution `x = sin² θ`. -/
theorem trigBeta_integrand_eq {a b : ℂ} {θ : ℝ} (hθ : θ ∈ Ioo 0 (π/2)) :
    |2*Real.sin θ*Real.cos θ| • (((Real.sin θ^2:ℝ):ℂ)^(a-1)*(1-((Real.sin θ^2:ℝ):ℂ))^(b-1)) =
      2*((Real.sin θ:ℂ)^(2*a-1)*(Real.cos θ:ℂ)^(2*b-1)) := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have h1 : 1-((Real.sin θ^2:ℝ):ℂ) = ((Real.cos θ^2:ℝ):ℂ) := by
    have := Real.sin_sq_add_cos_sq θ
    rw [show Real.cos θ^2 = 1 - Real.sin θ^2 by linarith]; push_cast; ring
  rw [abs_of_pos (by positivity), h1, Complex.real_smul]
  have e1 := ofReal_mul_sq_cpow' hs (a-1)
  have e2 := ofReal_mul_sq_cpow' hc (b-1)
  rw [show 2*(a-1)+1 = 2*a-1 by ring] at e1
  rw [show 2*(b-1)+1 = 2*b-1 by ring] at e2
  rw [← e1, ← e2]; push_cast; ring

/-- **Trigonometric Beta integral**, with integrability. -/
theorem trigBeta {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    IntervalIntegrable (fun θ : ℝ => (Real.sin θ:ℂ)^(2*a-1)*(Real.cos θ:ℂ)^(2*b-1)) volume 0 (π/2) ∧
    (∫ θ : ℝ in 0..π/2, (Real.sin θ:ℂ)^(2*a-1)*(Real.cos θ:ℂ)^(2*b-1)) =
      Gamma a * Gamma b / (2*Gamma (a+b)) := by
  set g : ℝ → ℂ := fun x => (x:ℂ)^(a-1)*(1-(x:ℂ))^(b-1)
  have hconv := Complex.betaIntegral_convergent ha hb
  have hg : IntegrableOn g (Ioo 0 1) := by
    have := hconv.1
    exact (integrableOn_Ioc_iff_integrableOn_Ioo'
      (by simp)).1 this
  set W : ℝ → ℂ := fun θ => (Real.sin θ:ℂ)^(2*a-1)*(Real.cos θ:ℂ)^(2*b-1)
  have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun θ _ => hasDerivWithinAt_sin_sq θ) sin_sq_injOn g
  have heq := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun θ _ => hasDerivWithinAt_sin_sq θ) sin_sq_injOn g
  rw [sin_sq_image_Ioo] at hiff heq
  have hcongr : EqOn (fun θ => |2*Real.sin θ*Real.cos θ| • g (Real.sin θ^2))
      (fun θ => 2 * W θ) (Ioo 0 (π/2)) := fun θ hθ => by
    simp only [g, W]; exact trigBeta_integrand_eq hθ
  have hW2 : IntegrableOn (fun θ => 2 * W θ) (Ioo 0 (π/2)) :=
    (hiff.1 hg).congr_fun hcongr measurableSet_Ioo
  have hW : IntegrableOn W (Ioo 0 (π/2)) := by
    exact IntegrableOn.congr_fun (hW2.const_mul (1/2:ℂ)) (fun θ _ => by ring) measurableSet_Ioo
  have hWi : IntervalIntegrable W volume 0 (π/2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by positivity)]
    exact hW
  refine ⟨hWi, ?_⟩
  have hB := Complex.Gamma_mul_Gamma_eq_betaIntegral ha hb
  have hG : Gamma (a+b) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  rw [hB, mul_comm (2:ℂ), ← div_div, mul_div_cancel_left₀ _ hG, Complex.betaIntegral,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  change _ = (∫ t in Ioo 0 1, g t)/2
  rw [heq, setIntegral_congr_fun measurableSet_Ioo hcongr, integral_const_mul,
    intervalIntegral.integral_of_le (by positivity), integral_Ioc_eq_integral_Ioo]
  ring

/-- struveH sonine. -/
@[dlmf 11.7.E7]
theorem struveH_sonine {ν : ℂ} (hν0 : -3/2 < ν.re) (hν1 : ν.re < 1/2) {z : ℂ} (hz : z ∈ slitPlane) :
    (∫ θ : ℝ in 0..π/2, struveH ν (z*Real.sin θ)*(Real.sin θ:ℂ)^(ν+1)/(Real.cos θ:ℂ)^(2*ν)) = 2^(-ν)/Real.sqrt π*Gamma (1/2-ν)*z^(ν-1)*(1-cos z) := by
  have hz0 := slitPlane_ne_zero hz
  have hz2 : z/2 ≠ 0 := div_ne_zero hz0 two_ne_zero
  have hb : 0 < (1/2-ν).re := by simp; linarith
  have ha : ∀ k : ℕ, 0 < ((k:ℂ)+ν+3/2).re := fun k => by
    simp; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  set W : ℕ → ℝ → ℂ := fun k θ =>
    (Real.sin θ:ℂ)^(2*((k:ℂ)+ν+3/2)-1)*(Real.cos θ:ℂ)^(2*(1/2-ν)-1)
  have hTB := fun k => trigBeta (ha k) hb
  set c : ℕ → ℂ := fun k => (z/2)^(ν+1)*((-1)^k*(z/2)^(2*k)*struveCoeff ν k)
  have hc : Summable fun k => ‖c k‖ := by
    rw [summable_norm_iff]
    exact ((hasSum_struveHCore ν z).mul_left _).summable
  have hWk : ∀ k : ℕ, ∀ θ ∈ Ioo (0:ℝ) (π/2), W k θ = (Real.sin θ:ℂ)^(2*k) * W 0 θ := by
    intro k θ hθ
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hs0 : (Real.sin θ:ℂ) ≠ 0 := ofReal_ne_zero.2 hs.ne'
    simp only [W]
    rw [← cpow_natCast, ← mul_assoc, ← cpow_add _ _ hs0]
    push_cast; ring_nf
  have hpt : ∀ θ ∈ Ioo (0:ℝ) (π/2), HasSum (fun k => c k * W k θ)
      (struveH ν (z*Real.sin θ)*(Real.sin θ:ℂ)^(ν+1)/(Real.cos θ:ℂ)^(2*ν)) := by
    intro θ hθ
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hs0 : (Real.sin θ:ℂ) ≠ 0 := ofReal_ne_zero.2 hs.ne'
    have hzs : z*Real.sin θ/2 = (Real.sin θ:ℂ)*(z/2) := by ring
    rw [struveH, hzs, DLMF.Confluent.ofReal_mul_cpow' hs hz2]
    have hser := (hasSum_struveHCore ν ((Real.sin θ:ℂ)*z)).mul_left
      ((Real.sin θ:ℂ)^(ν+1)*(z/2)^(ν+1)*(Real.sin θ:ℂ)^(ν+1)/(Real.cos θ:ℂ)^(2*ν))
    rw [show (Real.sin θ:ℂ)*z = z*Real.sin θ by ring] at hser
    convert hser using 1
    · funext k
      simp only [c, W]
      rw [show 2*((k:ℂ)+ν+3/2)-1 = (2*k:ℕ) + ((ν+1)+(ν+1)) by push_cast; ring,
        cpow_add _ _ hs0, cpow_add _ _ hs0, cpow_natCast,
        show 2*(1/2-ν)-1 = -(2*ν) by ring, cpow_neg]
      rw [show z*(Real.sin θ:ℂ)/2 = (Real.sin θ:ℂ)*(z/2) by ring, mul_pow]
      field_simp
    · ring
  have hne : ∀ᵐ t ∂(volume:Measure ℝ), t ≠ π/2 := by
    rw [ae_iff]; simp
  have hIoo : ∀ᵐ t ∂(volume:Measure ℝ), t ∈ uIoc (0:ℝ) (π/2) → t ∈ Ioo (0:ℝ) (π/2) := by
    filter_upwards [hne] with t ht h
    rw [uIoc_of_le (by positivity)] at h
    exact ⟨h.1, lt_of_le_of_ne h.2 ht⟩
  have hS := intervalIntegral.hasSum_integral_of_dominated_convergence
    (F := fun k θ => c k * W k θ) (μ := volume) (a := 0) (b := π/2)
    (f := fun θ => struveH ν (z*Real.sin θ)*(Real.sin θ:ℂ)^(ν+1)/(Real.cos θ:ℂ)^(2*ν))
    (fun k θ => ‖c k‖ * ‖W 0 θ‖)
    (fun k => (((hTB k).1.const_mul (c k)).def').aestronglyMeasurable)
    (fun k => by
      filter_upwards [hIoo] with θ hθ h
      have h' := hθ h
      show ‖c k * W k θ‖ ≤ ‖c k‖ * ‖W 0 θ‖
      rw [norm_mul (c k), hWk k θ h', norm_mul ((Real.sin θ:ℂ)^(2*k)), norm_pow,
        Complex.norm_real]
      have h1 : ‖Real.sin θ‖^(2*k) ≤ 1 := pow_le_one₀ (norm_nonneg _)
        (by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one θ)
      have := mul_le_mul_of_nonneg_right h1 (norm_nonneg (W 0 θ))
      rw [one_mul] at this
      exact mul_le_mul_of_nonneg_left this (norm_nonneg _))
    (Eventually.of_forall fun θ _ => hc.mul_right _)
    (by simp_rw [tsum_mul_right]; exact (hTB 0).1.norm.const_mul _)
    (by filter_upwards [hIoo] with θ hθ h; exact hpt θ (hθ h))
  simp only [intervalIntegral.integral_const_mul] at hS
  refine hS.unique ?_
  -- the cosine series
  have hcos := Complex.hasSum_cos z
  rw [← hasSum_nat_add_iff' 1] at hcos
  simp only [Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one] at hcos
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h2 : (2:ℂ)^(-ν) * 2^(ν+1) = 2 := by
    rw [← cpow_add _ _ two_ne_zero, show -ν+(ν+1) = 1 by ring, cpow_one]
  have hzp : z^(ν-1) * z^2 = 2^(ν+1) * (z/2)^(ν+1) := by
    rw [← cpow_natCast, ← cpow_add _ _ hz0, show ν-1+((2:ℕ):ℂ) = ν+1 by push_cast; ring]
    conv_lhs => rw [show z = ((2:ℝ):ℂ)*(z/2) by push_cast; ring]
    rw [DLMF.Confluent.ofReal_mul_cpow' (by norm_num : (0:ℝ) < 2) hz2]
    push_cast; ring
  have hTQ : (2:ℂ)^(-ν) * z^(ν-1) * z^2 = 2 * (z/2)^(ν+1) := by
    rw [mul_assoc, hzp, ← mul_assoc, h2]
  convert hcos.neg.mul_left (2^(-ν)/Real.sqrt π*Gamma (1/2-ν)*z^(ν-1)) using 1
  · funext k
    simp only [W]
    rw [(hTB k).2]
    rw [show (2:ℂ)^(-ν)/Real.sqrt π*Gamma (1/2-ν)*z^(ν-1) *
        -((-1)^(k+1)*z^(2*(k+1))/(((2*(k+1))! : ℕ) : ℂ)) =
        ((2:ℂ)^(-ν) * z^(ν-1) * z^2) * (Gamma (1/2-ν)*(-1)^k*z^(2*k)/
          (Real.sqrt π*(((2*(k+1))! : ℕ) : ℂ))) by ring, hTQ]
    have hf : (((2*(k+1))! : ℕ):ℂ) = oddProduct k * 2^(k+1) * (((k+1)! : ℕ) : ℂ) := by
      rw [show 2*(k+1) = (2*k+1)+1 by ring, Nat.factorial_succ, Nat.cast_mul,
        factorial_odd_eq_oddProduct, Nat.factorial_succ]
      push_cast; ring
    have ho : oddProduct k ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro j _
      have : (0:ℝ) < 2*j+1 := by positivity
      exact_mod_cast this.ne'
    have hG : Gamma ((k:ℂ)+ν+3/2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (ha k)
    have hk : (((k+1)! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    rw [hf, show (k:ℂ)+ν+3/2+(1/2-ν) = ((k+1:ℕ):ℂ)+1 by push_cast; ring,
      Complex.Gamma_nat_eq_factorial]
    simp only [c, struveCoeff, Gamma_oddProduct]
    rw [show (k:ℂ)+ν+3/2 = (k:ℂ)+ν+3/2 from rfl, div_pow z 2 (2*k)]
    generalize (z/2)^(ν+1) = P
    generalize Gamma ((k:ℂ)+ν+3/2) = G at hG ⊢
    field_simp
    ring
  · ring

/-- The sine integral `Si(x) = ∫₀ˣ sinc` is bounded on `[0,∞)`. -/
theorem exists_bound_integral_sinc : ∃ C : ℝ, ∀ x : ℝ, 0 ≤ x → |∫ u in (0:ℝ)..x, Real.sinc u| ≤ C := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp
    ((TauCeti.Contour.tendsto_integral_sinc_atTop).eventually (Metric.ball_mem_nhds (π/2) one_pos))
  refine ⟨max X (π/2 + 1), fun x hx => ?_⟩
  by_cases h : X ≤ x
  · have := hX x h
    rw [Real.dist_eq] at this
    have := abs_sub_abs_le_abs_sub (∫ u in (0:ℝ)..x, Real.sinc u) (π/2)
    rw [abs_of_pos (by positivity : (0:ℝ) < π/2)] at this
    exact (by linarith : _ ≤ π/2+1).trans (le_max_right _ _)
  · push Not at h
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := x) (C := 1)
      (f := Real.sinc) (fun u _ => by rw [Real.norm_eq_abs]; exact Real.abs_sinc_le_one u)
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hx, one_mul] at hb
    exact hb.trans (by linarith [le_max_left X (π/2+1)])

/-- `∫₀^R c sinc(tc) dt = ∫₀^{Rc} sinc`. -/
lemma integral_mul_sinc_mul (c R : ℝ) :
    ∫ t in (0:ℝ)..R, c * Real.sinc (t * c) = ∫ u in (0:ℝ)..R * c, Real.sinc u := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · have := intervalIntegral.integral_comp_mul_right (a := 0) (b := R) Real.sinc hc
    rw [intervalIntegral.integral_const_mul, this, zero_mul, smul_eq_mul]
    field_simp

/-- Dirichlet's integral under a parametric integral: for `g` continuous on `[a,b]` and `c ≥ 0`
continuous, positive on `(a,b)`,
`∫₀^R ∫_a^b g(s) c(s) sinc(t c(s)) ds dt → (π/2) ∫_a^b g`. -/
theorem tendsto_integral_integral_mul_sinc {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℂ} {c : ℝ → ℝ}
    (hg : ContinuousOn g (Icc a b)) (hc : ContinuousOn c (Icc a b))
    (hc0 : ∀ s ∈ Icc a b, 0 ≤ c s) (hc1 : ∀ s ∈ Ioo a b, 0 < c s) :
    Tendsto (fun R : ℝ => ∫ t in (0:ℝ)..R, ∫ s in a..b, g s * ((c s * Real.sinc (t * c s) : ℝ) : ℂ))
      atTop (𝓝 (((π/2 : ℝ) : ℂ) * ∫ s in a..b, g s)) := by
  obtain ⟨C, hC⟩ := exists_bound_integral_sinc
  set Si : ℝ → ℝ := fun x => ∫ u in (0:ℝ)..x, Real.sinc u
  have hSi : Continuous Si := by
    have := intervalIntegral.continuous_primitive (μ := volume) (f := Real.sinc)
      (fun x y => Real.continuous_sinc.intervalIntegrable x y) 0
    exact this
  -- Fubini and substitution
  have hswap : ∀ R : ℝ, 0 ≤ R → (∫ t in (0:ℝ)..R, ∫ s in a..b,
      g s * ((c s * Real.sinc (t * c s) : ℝ) : ℂ)) = ∫ s in a..b, g s * (Si (R * c s) : ℂ) := by
    intro R hR
    rw [intervalIntegral_intervalIntegral_swap]
    · refine intervalIntegral.integral_congr fun s _ => ?_
      rw [intervalIntegral.integral_const_mul]
      congr 1
      rw [intervalIntegral.integral_ofReal, integral_mul_sinc_mul]
    · have hK : ContinuousOn (Function.uncurry fun t s => g s * ((c s * Real.sinc (t * c s) : ℝ) : ℂ))
          (Icc 0 R ×ˢ Icc a b) := by
        have hm : MapsTo Prod.snd (Icc 0 R ×ˢ Icc a b) (Icc a b) := fun p hp => hp.2
        refine (hg.comp continuousOn_snd hm).mul ?_
        refine continuous_ofReal.comp_continuousOn ?_
        exact (hc.comp continuousOn_snd hm).mul
          (Real.continuous_sinc.comp_continuousOn (continuousOn_fst.mul
            (hc.comp continuousOn_snd hm)))
      refine (hK.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set ?_
      rw [uIoc_of_le hR, uIoc_of_le hab]
      exact prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
  have hlim : Tendsto (fun R : ℝ => ∫ s in a..b, g s * (Si (R * c s) : ℂ)) atTop
      (𝓝 (∫ s in a..b, g s * ((π/2 : ℝ) : ℂ))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun s => ‖g s‖ * C) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun R => ?_
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
      refine (hg.mul (continuous_ofReal.comp_continuousOn (hSi.comp_continuousOn
        (continuousOn_const.mul hc)))).mono ?_
      rw [uIoc_of_le hab]; exact Ioc_subset_Icc_self
    · filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
      refine Eventually.of_forall fun s hs => ?_
      rw [uIoc_of_le hab] at hs
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hC _ (mul_nonneg hR (hc0 s (Ioc_subset_Icc_self hs))))
        (norm_nonneg _)
    · refine (ContinuousOn.intervalIntegrable ?_).mul_const C
      rw [uIcc_of_le hab]; exact continuous_norm.comp_continuousOn hg
    · have hb : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ b := by
        rw [ae_iff]; simp [measure_singleton]
      filter_upwards [hb] with s hsb hs
      rw [uIoc_of_le hab] at hs
      have hcs := hc1 s ⟨hs.1, lt_of_le_of_ne hs.2 hsb⟩
      refine Tendsto.const_mul _ ?_
      exact (continuous_ofReal.tendsto _).comp
        ((TauCeti.Contour.tendsto_integral_sinc_atTop).comp
          (tendsto_id.atTop_mul_const hcs))
  rw [intervalIntegral.integral_mul_const, mul_comm] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
  rw [hswap R hR]


/-- `sin(tc)/t = c sinc(tc)` for `t ≠ 0`. -/
lemma sin_mul_div_eq_mul_sinc (t c : ℝ) (ht : t ≠ 0) :
    Real.sin (t * c) / t = c * Real.sinc (t * c) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · rw [Real.sinc_of_ne_zero (mul_ne_zero ht hc)]; field_simp

/-- `c sinc(tc) t = sin(tc)` for `t ≠ 0`. -/
lemma mul_sinc_mul_mul (t c : ℝ) (ht : t ≠ 0) :
    c * Real.sinc (t * c) * t = Real.sin (t * c) := by
  rw [← sin_mul_div_eq_mul_sinc t c ht]; field_simp

/-- `√π √π = π` in `ℂ`. -/
lemma sqrt_pi_mul_sqrt_pi_complex : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
  rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]

/-- `∫₀¹ √(1-s²) ds = π/4`. -/
lemma integral_sqrt_one_sub_sq_unit : ∫ s in (0:ℝ)..1, √(1 - s ^ 2) = π / 4 := by
  have h := integral_sqrt_one_sub_sq
  have hc : Continuous fun s : ℝ => √(1 - s ^ 2) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)] at h
  have hneg : ∫ s in (-1:ℝ)..0, √(1 - s ^ 2) = ∫ s in (0:ℝ)..1, √(1 - s ^ 2) := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := 1) (fun s : ℝ => √(1 - s ^ 2))
    simp only [neg_sq, neg_zero] at this
    exact this.symm
  linarith

/-- struveH integral zero div. -/
@[dlmf 11.7.E8]
theorem struveH_integral_zero_div  :
    HasIntegralAtTop (fun t : ℝ => struveH 0 t/t) 0 (π/2) := by
  -- Poisson's integral, Fubini, and Dirichlet's integral (TauCeti `tendsto_integral_sinc_atTop`)
  have h := tendsto_integral_integral_mul_sinc (a := 0) (b := π/2) (by positivity)
    (g := fun _ => ((2/π : ℝ) : ℂ)) (c := Real.cos) continuousOn_const
    Real.continuous_cos.continuousOn (fun s hs => Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hs.1, Real.pi_pos], hs.2⟩)
    (fun s hs => Real.cos_pos_of_mem_Ioo ⟨by linarith [hs.1, Real.pi_pos], hs.2⟩)
  rw [intervalIntegral.integral_const, sub_zero, real_smul] at h
  have hv : (((π/2 : ℝ) : ℂ) * (((π/2 : ℝ) : ℂ) * ((2/π : ℝ) : ℂ))) = (π/2 : ℂ) := by
    push_cast; field_simp
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
  rw [uIoc_of_le hR] at ht
  have ht0 : (0:ℝ) < t := ht.1
  have ht' : (t:ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
  rw [struveH_trig_integral (by norm_num) (ofReal_mem_slitPlane.mpr ht0), eq_div_iff ht',
    ← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hr := mul_sinc_mul_mul t (Real.cos θ) ht0.ne'
  have hr' : ((Real.cos θ * Real.sinc (t * Real.cos θ) : ℝ) : ℂ) * t =
      sin ((t:ℂ) * (Real.cos θ : ℂ)) := by
    rw [← ofReal_mul, hr, ofReal_sin, ofReal_mul]
  simp only [cpow_zero, mul_zero, mul_one, zero_add, DLMF.Confluent.Gamma_one_half_eq_sqrt]
  rw [mul_assoc, hr', sqrt_pi_mul_sqrt_pi_complex]
  push_cast
  ring



/-- struveH integral one div sq. -/
@[dlmf 11.7.E8]
theorem struveH_integral_one_div_sq  :
    HasIntegralAtTop (fun t : ℝ => struveH 1 t/t^2) 0 (π/4) := by
  -- Poisson's integral, Fubini, and Dirichlet's integral
  have h := tendsto_integral_integral_mul_sinc (a := 0) (b := 1) zero_le_one
    (g := fun s => ((2/π * √(1 - s ^ 2) : ℝ) : ℂ)) (c := id)
    (continuous_ofReal.comp (by fun_prop)).continuousOn continuous_id.continuousOn
    (fun s hs => hs.1) (fun s hs => hs.1)
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul,
    integral_sqrt_one_sub_sq_unit] at h
  have hv : (((π/2 : ℝ) : ℂ) * ((2/π * (π/4) : ℝ) : ℂ)) = (π/4 : ℂ) := by
    push_cast; field_simp
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
  rw [uIoc_of_le hR] at ht
  have ht0 : (0:ℝ) < t := ht.1
  have ht' : (t:ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
  rw [struveH_integral (by norm_num) (ofReal_mem_slitPlane.mpr ht0), eq_div_iff (pow_ne_zero 2 ht'),
    ← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le zero_le_one] at hs
  have hr := mul_sinc_mul_mul t s ht0.ne'
  have hsq : (1 - (s : ℂ) ^ 2) ^ ((1:ℂ) - 1/2) = ((√(1 - s ^ 2) : ℝ) : ℂ) := by
    rw [show (1 - (s : ℂ) ^ 2) = ((1 - s ^ 2 : ℝ) : ℂ) by push_cast; ring,
      show ((1:ℂ) - 1/2) = ((1/2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow (by nlinarith [hs.1, hs.2]), Real.sqrt_eq_rpow]
  have hG : Gamma (1 + 1/2) = (Real.sqrt π : ℂ) / 2 := by
    rw [show (1:ℂ) + 1/2 = 1/2 + 1 by ring, Complex.Gamma_add_one _ (by norm_num),
      DLMF.Confluent.Gamma_one_half_eq_sqrt]; ring
  have hsin : sin ((t:ℂ) * (s:ℂ)) = ((Real.sin (t * s) : ℝ) : ℂ) := by push_cast; ring_nf
  rw [hsq, hG, cpow_one, hsin, ← hr]
  have hp : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs0 : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  simp only [id]
  push_cast
  rw [← sqrt_pi_mul_sqrt_pi_complex]
  field_simp



/-! ### Mellin transforms of `H_ν` (DLMF 11.7.9–11.7.11)

The improper integrals `∫₀^∞ t^{μ-ν-1} H_ν(t) dt` converge only conditionally. For `re ν > -1/2`
the Poisson representation, the conditionally convergent Mellin transform of the sine
(`Complex.tendsto_integral_cpow_mul_sin`, obtained by Abel regularization) and dominated
convergence for improper parametric integrals give the value. Integration by parts with
`d/dt (t^{ν+1} H_{ν+1}) = t^{ν+1} H_ν` extends it to `re ν > re μ - 3/2`; the boundary terms
vanish by `H_ν = Y_ν + K_ν`, Hankel's expansion of `Y_ν` and the Laplace representation of `K_ν`.
-/

/-- `u^{μ-1} sin u = u^μ sinc u` for `u ≠ 0`. -/
lemma struveMel_cpow_mul_sin_eq (μ : ℂ) {u : ℝ} (hu : u ≠ 0) :
    (u : ℂ) ^ (μ - 1) * (Real.sin u : ℂ) = (u : ℂ) ^ μ * (Real.sinc u : ℂ) := by
  rw [Real.sinc_of_ne_zero hu, cpow_sub _ _ (ofReal_ne_zero.mpr hu), cpow_one]
  push_cast
  field_simp

/-- The Mellin sine integrand is interval integrable for `re μ > -1`. -/
lemma struveMel_intervalIntegrable {μ : ℂ} (h0 : -1 < μ.re) (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ (μ - 1) * (Real.sin u : ℂ)) volume a b := by
  have h := (intervalIntegral.intervalIntegrable_cpow' h0 (a := a) (b := b)).mul_continuousOn
    (continuous_ofReal.comp Real.continuous_sinc).continuousOn
  refine h.congr_ae ?_
  have hn : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := by
    rw [ae_iff]; simp [measure_singleton]
  refine ae_restrict_of_ae ?_
  filter_upwards [hn] with u hu
  exact (struveMel_cpow_mul_sin_eq μ hu).symm

/-- **Mellin transform of the sine** including Dirichlet's integral at `μ = 0`:
`∫₀^X u^{μ-1} sin u du → Γ(μ) sin(πμ/2)` (`π/2` at `μ = 0`) for `-1 < re μ < 1`. -/
theorem struveMel_tendsto_sin {μ : ℂ} (h0 : -1 < μ.re) (h1 : μ.re < 1) :
    Tendsto (fun X : ℝ => ∫ u in (0 : ℝ)..X, (u : ℂ) ^ (μ - 1) * (Real.sin u : ℂ)) atTop
      (𝓝 (if μ = 0 then (π / 2 : ℂ) else Gamma μ * sin (π * μ / 2))) := by
  split_ifs with hμ
  · subst hμ
    have h := (continuous_ofReal.tendsto _).comp TauCeti.Contour.tendsto_integral_sinc_atTop
    refine (h.congr fun X => ?_).trans (by push_cast; exact le_rfl)
    simp only [Function.comp, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr_ae ?_
    have hn : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := by
      rw [ae_iff]; simp [measure_singleton]
    filter_upwards [hn] with u hu _
    rw [struveMel_cpow_mul_sin_eq 0 hu, cpow_zero, one_mul]
  · exact Complex.tendsto_integral_cpow_mul_sin h0 h1 hμ

/-- The partial Mellin sine integrals are bounded on `[0, ∞)`. -/
lemma struveMel_exists_bound {μ : ℂ} (h0 : -1 < μ.re) (h1 : μ.re < 1) :
    ∃ C, ∀ X : ℝ, 0 ≤ X →
      ‖∫ u in (0 : ℝ)..X, (u : ℂ) ^ (μ - 1) * (Real.sin u : ℂ)‖ ≤ C := by
  have hc : Continuous (fun X : ℝ => ∫ u in (0 : ℝ)..X, (u : ℂ) ^ (μ - 1) * (Real.sin u : ℂ)) :=
    intervalIntegral.continuous_primitive (struveMel_intervalIntegrable h0) 0
  obtain ⟨C, hC⟩ := MeasureTheory.exists_norm_le_of_continuousOn_of_tendsto hc.continuousOn
    (struveMel_tendsto_sin h0 h1)
  exact ⟨C, fun X hX => hC X hX⟩

/-- Scaling: `∫₀^R t^{μ-1} sin(ct) dt = c^{-μ} ∫₀^{Rc} u^{μ-1} sin u du` for `c > 0`. -/
lemma struveMel_integral_scale (μ : ℂ) {c : ℝ} (hc : 0 < c) {R : ℝ} (hR : 0 ≤ R) :
    ∫ t in (0 : ℝ)..R, (t : ℂ) ^ (μ - 1) * (Real.sin (t * c) : ℂ) =
      (c : ℂ) ^ (-μ) * ∫ u in (0 : ℝ)..R * c, (u : ℂ) ^ (μ - 1) * (Real.sin u : ℂ) := by
  have h := intervalIntegral.integral_comp_mul_right
    (fun u : ℝ => (u : ℂ) ^ (μ - 1) * (Real.sin u : ℂ)) hc.ne' (a := 0) (b := R)
  simp only [zero_mul] at h
  have hc0 : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
  have hpt : ∀ t : ℝ, 0 ≤ t → (t : ℂ) ^ (μ - 1) * (Real.sin (t * c) : ℂ) =
      (c : ℂ) ^ (1 - μ) * (((t * c : ℝ) : ℂ) ^ (μ - 1) * (Real.sin (t * c) : ℂ)) := by
    intro t ht
    rw [ofReal_mul, mul_cpow_ofReal_nonneg ht hc.le, ← mul_assoc, ← mul_assoc,
      mul_comm ((c : ℂ) ^ (1 - μ)), mul_assoc ((t : ℂ) ^ (μ - 1)), ← cpow_add _ _ hc0]
    simp
  rw [intervalIntegral.integral_congr (g := fun t : ℝ => (c : ℂ) ^ (1 - μ) *
      (((t * c : ℝ) : ℂ) ^ (μ - 1) * (Real.sin (t * c) : ℂ))) (fun t ht => by
        rw [uIcc_of_le hR] at ht; exact hpt t ht.1),
    intervalIntegral.integral_const_mul, h, Complex.real_smul, ← mul_assoc]
  congr 1
  rw [show (1 - μ) = -μ + 1 by ring, cpow_add _ _ hc0, cpow_one, ofReal_inv]
  field_simp

/-- `sin^{2a-1} θ cos^{2b-1} θ` is integrable on `(0, π/2]` with the Beta value. -/
lemma struveMel_trigBeta {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    IntegrableOn (fun θ : ℝ => (Real.sin θ : ℂ) ^ (2 * a - 1) * (Real.cos θ : ℂ) ^ (2 * b - 1))
      (Ioc 0 (π / 2)) ∧
    ∫ θ in Ioc 0 (π / 2), (Real.sin θ : ℂ) ^ (2 * a - 1) * (Real.cos θ : ℂ) ^ (2 * b - 1) =
      Gamma a * Gamma b / (2 * Gamma (a + b)) := by
  obtain ⟨h1, h2⟩ := trigBeta ha hb
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mp h1, ?_⟩
  rw [← intervalIntegral.integral_of_le (by positivity), h2]

/-- The direct region of the Struve Mellin transform: for `re ν > -1/2` and `|re μ| < 1`,
`∫₀^R t^{μ-ν-1} H_ν(t) dt` converges to the Poisson–Beta value. -/
theorem struveMel_tendsto_direct {μ ν : ℂ} (hμ0 : -1 < μ.re) (hμ1 : μ.re < 1)
    (hν : -1 / 2 < ν.re) :
    Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R, (t : ℂ) ^ (μ - ν - 1) * struveH ν t) atTop
      (𝓝 (2 * (1 / 2 : ℂ) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2)) *
        ((if μ = 0 then (π / 2 : ℂ) else Gamma μ * sin (π * μ / 2)) *
          (Gamma (ν + 1 / 2) * Gamma ((1 - μ) / 2) / (2 * Gamma (ν + 1 / 2 + (1 - μ) / 2)))))) := by
  set S : ℂ := if μ = 0 then (π / 2 : ℂ) else Gamma μ * sin (π * μ / 2)
  set A : ℂ := 2 * (1 / 2 : ℂ) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2))
  set K : ℝ → ℝ → ℂ := fun t θ =>
    (t : ℂ) ^ (μ - 1) * (Real.sin (t * Real.cos θ) : ℂ) * (Real.sin θ : ℂ) ^ (2 * ν)
  set m : Measure ℝ := volume.restrict (Ioc 0 (π / 2))
  have ha : 0 < (ν + 1 / 2).re := by simp; linarith
  have hb : 0 < ((1 - μ) / 2).re := by simp; linarith
  have hb' : 0 < (1 / 2 : ℂ).re := by norm_num
  -- the weight `sin^{2ν}` and the Beta weight
  have hW := struveMel_trigBeta ha hb'
  have hB := struveMel_trigBeta ha hb
  have e1 : 2 * (ν + 1 / 2) - 1 = 2 * ν := by ring
  have e2 : 2 * (1 / 2 : ℂ) - 1 = 0 := by norm_num
  have e3 : 2 * ((1 - μ) / 2) - 1 = -μ := by ring
  simp only [e1, e2, e3, cpow_zero, mul_one] at hW hB
  obtain ⟨C, hC⟩ := struveMel_exists_bound hμ0 hμ1
  have hθ : ∀ᵐ θ ∂m, θ ∈ Ioo 0 (π / 2) := by
    have hn : ∀ᵐ θ : ℝ ∂volume, θ ≠ π / 2 := by
      rw [ae_iff]; simp [measure_singleton]
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hn] with θ h1 h2
    exact ⟨h1.1, lt_of_le_of_ne h1.2 h2⟩
  have hcos : ∀ θ ∈ Ioo 0 (π / 2), 0 < Real.cos θ := fun θ h =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [h.1, Real.pi_pos], h.2⟩
  have hinner : ∀ θ ∈ Ioo 0 (π / 2), ∀ R : ℝ, 0 ≤ R → ∫ t in (0 : ℝ)..R, K t θ =
      (Real.sin θ : ℂ) ^ (2 * ν) * (Real.cos θ : ℂ) ^ (-μ) *
        ∫ u in (0 : ℝ)..R * Real.cos θ, (u : ℂ) ^ (μ - 1) * (Real.sin u : ℂ) := by
    intro θ hθ R hR
    simp only [K]
    rw [intervalIntegral.integral_mul_const, struveMel_integral_scale μ (hcos θ hθ) hR]
    ring
  have hsinpos : ∀ θ ∈ Ioc 0 (π / 2), 0 < Real.sin θ := fun θ h =>
    Real.sin_pos_of_pos_of_lt_pi h.1 (by linarith [h.2, Real.pi_pos])
  have hmain : Tendsto (fun R => ∫ t in (0 : ℝ)..R, ∫ θ, K t θ ∂m) atTop
      (𝓝 (∫ θ, (Real.sin θ : ℂ) ^ (2 * ν) * (Real.cos θ : ℂ) ^ (-μ) * S ∂m)) := by
    refine MeasureTheory.tendsto_intervalIntegral_integral_of_dominated
      (bound := fun θ => C * ‖(Real.sin θ : ℂ) ^ (2 * ν) * (Real.cos θ : ℂ) ^ (-μ)‖)
      (fun R hR => ?_) (fun R hR => ?_) (hB.1.norm.const_mul C) ?_
    · have hT : Integrable (fun t : ℝ => t ^ μ.re) (volume.restrict (Ioc 0 R)) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mp
          (intervalIntegral.intervalIntegrable_rpow' hμ0)
      have hF : Integrable (fun p : ℝ × ℝ => p.1 ^ μ.re * ‖(Real.sin p.2 : ℂ) ^ (2 * ν)‖)
          ((volume.restrict (Ioc 0 R)).prod m) := Integrable.mul_prod hT hW.1.norm
      refine hF.mono' ?_ ?_
      · rw [Measure.prod_restrict]
        refine ContinuousOn.aestronglyMeasurable (fun p hp => ?_)
          (measurableSet_Ioc.prod measurableSet_Ioc)
        have ht : 0 < p.1 := hp.1.1
        have hs : 0 < Real.sin p.2 := hsinpos p.2 hp.2
        refine ContinuousAt.continuousWithinAt ?_
        simp only [K]
        refine ContinuousAt.mul (ContinuousAt.mul ?_ (by fun_prop)) ?_
        · exact ((continuous_ofReal.continuousAt).cpow continuousAt_const
            (ofReal_mem_slitPlane.mpr ht)).comp continuousAt_fst
        · exact ContinuousAt.comp (x := p) (f := fun q : ℝ × ℝ => Real.sin q.2)
            (g := fun x : ℝ => (x : ℂ) ^ (2 * ν))
            ((continuous_ofReal.continuousAt).cpow continuousAt_const
              (ofReal_mem_slitPlane.mpr hs)) (by fun_prop)
      · rw [Measure.prod_restrict]
        filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
        have ht : 0 < p.1 := hp.1.1
        simp only [K, Function.uncurry, norm_mul, norm_real, Real.norm_eq_abs,
          norm_cpow_eq_rpow_re_of_pos ht]
        have hsin : |Real.sin (p.1 * Real.cos p.2)| ≤ p.1 := by
          refine (Real.abs_sin_le_abs).trans ?_
          rw [abs_mul, abs_of_pos ht]
          exact mul_le_of_le_one_right ht.le (Real.abs_cos_le_one _)
        have hre : (μ - 1).re = μ.re - 1 := by simp
        rw [hre]
        have hp1 : p.1 ^ (μ.re - 1) * p.1 = p.1 ^ μ.re := by
          rw [Real.rpow_sub_one ht.ne']; field_simp
        calc p.1 ^ (μ.re - 1) * |Real.sin (p.1 * Real.cos p.2)| * ‖(Real.sin p.2 : ℂ) ^ (2 * ν)‖
            ≤ p.1 ^ (μ.re - 1) * p.1 * ‖(Real.sin p.2 : ℂ) ^ (2 * ν)‖ := by gcongr
          _ = _ := by rw [hp1]
    · filter_upwards [hθ] with θ hθ'
      rw [hinner θ hθ' R hR, norm_mul, mul_comm C]
      exact mul_le_mul_of_nonneg_left (hC _ (mul_nonneg hR (hcos θ hθ').le)) (norm_nonneg _)
    · filter_upwards [hθ] with θ hθ'
      have h := ((struveMel_tendsto_sin hμ0 hμ1).comp
        (tendsto_id.atTop_mul_const (hcos θ hθ'))).const_mul
        ((Real.sin θ : ℂ) ^ (2 * ν) * (Real.cos θ : ℂ) ^ (-μ))
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop 0] with R hR
      rw [hinner θ hθ' R hR]
      rfl
  rw [integral_mul_const, hB.2] at hmain
  have hpt : ∀ t : ℝ, 0 < t → (t : ℂ) ^ (μ - ν - 1) * struveH ν t = A * ∫ θ, K t θ ∂m := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    rw [struveH_trig_integral hν (ofReal_mem_slitPlane.mpr ht),
      intervalIntegral.integral_of_le (by positivity)]
    have hK : ∀ θ, K t θ = (t : ℂ) ^ (μ - 1) *
        (sin ((t : ℂ) * (Real.cos θ : ℂ)) * (Real.sin θ : ℂ) ^ (2 * ν)) := by
      intro θ; simp only [K]; push_cast; ring
    simp_rw [hK]
    rw [integral_const_mul]
    have hh : (t : ℂ) / 2 = ((t : ℝ) : ℂ) * ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hh, mul_cpow_ofReal_nonneg ht.le (by norm_num)]
    have hc : (t : ℂ) ^ (μ - ν - 1) * (t : ℂ) ^ ν = (t : ℂ) ^ (μ - 1) := by
      rw [← cpow_add _ _ ht0]; ring_nf
    simp only [A, m]
    rw [show ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) by push_cast; ring, ← hc]
    ring
  refine (hmain.const_mul A).congr' ?_ |>.trans (by rw [mul_comm S])
  filter_upwards [eventually_ge_atTop 0] with R hR
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
  rw [uIoc_of_le hR] at ht
  exact (hpt t ht.1).symm

/-- `(1/2)^ν = 2^{-ν}`. -/
lemma struveMel_half_cpow (ν : ℂ) : (1 / 2 : ℂ) ^ ν = (2 : ℂ) ^ (-ν) := by
  have h : (2 : ℂ).arg = 0 := by simp
  rw [one_div, inv_cpow _ _ (by rw [h]; exact Real.pi_ne_zero.symm), cpow_neg]

/-- `z / Γ(z+1) = 1/Γ(z)` for every complex `z` (with Mathlib's conventions at the poles). -/
lemma struveMel_div_Gamma_add_one (z : ℂ) : z / Gamma (z + 1) = (Gamma z)⁻¹ := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · rw [Complex.Gamma_add_one z hz]
    rcases eq_or_ne (Gamma z) 0 with h | h
    · simp [h]
    · field_simp

/-- The Struve Mellin value `V(μ, ν)` of DLMF 11.7.10–11.7.11. -/
lemma struveMel_value_eq {μ ν : ℂ} (hμ0 : -1 < μ.re) (hμ1 : μ.re < 1) (hν : -1 / 2 < ν.re) :
    2 * (1 / 2 : ℂ) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2)) *
        ((if μ = 0 then (π / 2 : ℂ) else Gamma μ * sin (π * μ / 2)) *
          (Gamma (ν + 1 / 2) * Gamma ((1 - μ) / 2) / (2 * Gamma (ν + 1 / 2 + (1 - μ) / 2)))) =
      if μ = 0 then π / (2 ^ (ν + 1) * Gamma (ν + 1))
      else Gamma (μ / 2) * 2 ^ (μ - ν - 1) * sin (π * μ / 2) /
        (cos (π * μ / 2) * Gamma (ν - μ / 2 + 1)) := by
  have hG1 : Gamma (ν + 1 / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hsq : (Real.sqrt π : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hsq2 : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have h2 : (2 : ℂ) ^ (-ν) * (2 : ℂ) ^ ν = 1 := by
    rw [← cpow_add _ _ two_ne_zero]; simp
  rw [struveMel_half_cpow]
  split_ifs with hμ
  · subst hμ
    have hG : Gamma (ν + 1 / 2 + (1 - 0) / 2) = Gamma (ν + 1) := by ring_nf
    rw [hG, show (1 - (0 : ℂ)) / 2 = 1 / 2 by ring, DLMF.Confluent.Gamma_one_half_eq_sqrt,
      cpow_add _ _ two_ne_zero, cpow_one]
    generalize Gamma (ν + 1 / 2) = G at hG1 ⊢
    rcases eq_or_ne (Gamma (ν + 1)) 0 with h | h
    · simp [h]
    · field_simp
      linear_combination h2
  · have hG2 : Gamma (ν + 1 / 2 + (1 - μ) / 2) = Gamma (ν - μ / 2 + 1) := by ring_nf
    rw [hG2]
    have hh : Gamma (μ / 2 + 1 / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
    have hD : Gamma (ν - μ / 2 + 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
    have hc : cos (π * μ / 2) ≠ 0 := by
      rw [Ne, Complex.cos_eq_zero_iff]
      rintro ⟨k, hk⟩
      have hμk : μ = 2 * k + 1 := by
        have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
        field_simp at hk
        linear_combination hk
      have hre := congrArg Complex.re hμk
      simp at hre
      have h1 : (2 * k + 1 : ℝ) < 1 := by linarith
      have h2 : -1 < (2 * k + 1 : ℝ) := by linarith
      have h3 : k < 0 := by exact_mod_cast (show (k : ℝ) < 0 by linarith)
      have h4 : -1 < k := by exact_mod_cast (show (-1 : ℝ) < k by linarith)
      omega
    have hQ : (2 : ℂ) ^ (1 - μ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
    have hdup := Complex.Gamma_mul_Gamma_add_half (μ / 2)
    rw [show 2 * (μ / 2) = μ by ring] at hdup
    have hrefl := Complex.Gamma_mul_Gamma_one_sub (μ / 2 + 1 / 2)
    rw [show 1 - (μ / 2 + 1 / 2) = (1 - μ) / 2 by ring,
      show (π : ℂ) * (μ / 2 + 1 / 2) = π * μ / 2 + π / 2 by ring, Complex.sin_add_pi_div_two]
      at hrefl
    have hQT : (2 : ℂ) ^ (-ν) = (2 : ℂ) ^ (1 - μ) * (2 : ℂ) ^ (μ - ν - 1) := by
      rw [← cpow_add _ _ two_ne_zero]; ring_nf
    have ha : Gamma μ = Gamma (μ / 2) * Gamma (μ / 2 + 1 / 2) / ((2 : ℂ) ^ (1 - μ) * Real.sqrt π) := by
      rw [hdup]; field_simp
    have hb : Gamma ((1 - μ) / 2) = Real.sqrt π * Real.sqrt π /
        (cos (π * μ / 2) * Gamma (μ / 2 + 1 / 2)) := by
      rw [hsq2, eq_div_iff (mul_ne_zero hc hh), ← mul_assoc, mul_comm _ (cos _),
        mul_assoc, mul_comm (Gamma _) (Gamma _), hrefl]
      field_simp
    rw [ha, hb, hQT]
    generalize Gamma (ν + 1 / 2) = G at hG1 ⊢
    generalize Gamma (μ / 2 + 1 / 2) = H at hh ⊢
    generalize Gamma (ν - μ / 2 + 1) = D at hD ⊢
    generalize cos (π * μ / 2) = c at hc ⊢
    field_simp

/-- `x^a = O(x^b)` at infinity when `a ≤ b`. -/
lemma struveMel_rpow_isBigO_rpow {a b : ℝ} (h : a ≤ b) :
    (fun x : ℝ => x ^ a) =O[atTop] (fun x : ℝ => x ^ b) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _),
    abs_of_pos (Real.rpow_pos_of_pos (by linarith) _), one_mul]
  exact Real.rpow_le_rpow_of_exponent_le hx h

/-- `Y_ν(x) = O(x^{-1/2})` as `x → +∞`, for every complex order. -/
lemma struveMel_besselY_isBigO (ν : ℂ) :
    (fun x : ℝ => besselY ν x) =O[atTop] (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) := by
  -- the Hankel function
  have hH : (fun x : ℝ => hankelH1 ν x) =O[atTop] (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) := by
    have h0 := hasAsymptoticExpansion_hankelH1 ν 0
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero, Nat.cast_zero, zero_add] at h0
    have hs : (fun x : ℝ => (2 * (-I * x)) ^ (-(1 / 2 : ℂ))) =O[atTop]
        (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [eventually_gt_atTop 0] with x hx
      have hz : (2 * (-I * (x : ℂ))) ≠ 0 := by
        simp [hx.ne', I_ne_zero]
      rw [norm_cpow_of_ne_zero hz]
      have him : (-(1 / 2 : ℂ)).im = 0 := by simp
      have hre : (-(1 / 2 : ℂ)).re = -(1 / 2) := by norm_num
      rw [him, hre, mul_zero, Real.exp_zero, div_one, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos hx _), one_mul]
      have hn : ‖2 * (-I * (x : ℂ))‖ = 2 * x := by
        simp [abs_of_pos hx]
      rw [hn, Real.mul_rpow (by norm_num) hx.le]
      have h2 : (2 : ℝ) ^ (-(1 / 2) : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
      exact mul_le_of_le_one_left (Real.rpow_nonneg hx.le _) h2
    have h1 := h0.trans hs
    have he : (fun x : ℝ => exp (I * x)) =O[atTop] (fun _ : ℝ => (1 : ℝ)) :=
      IsBigO.of_bound 1 (Eventually.of_forall fun x => by
        rw [norm_exp_I_mul_ofReal]; simp)
    have h2 := he.mul h1
    simp only [one_mul] at h2
    refine h2.congr' (Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => rfl)
    dsimp only
    rw [← mul_assoc, ← Complex.exp_add]
    simp
  -- the Bessel function `J`
  have hJ : (fun x : ℝ => besselJ ν x) =O[atTop] (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) := by
    have h1 := (besselJ_sub_cos_isBigO ν).trans (struveMel_rpow_isBigO_rpow
      (show (-(3 / 2) : ℝ) ≤ -(1 / 2) by norm_num))
    set c : ℂ := ν * π / 2 + π / 4
    have hc : (fun x : ℝ => (Real.sqrt (2 / (π * x)) : ℂ) * cos (x - ν * π / 2 - π / 4)) =O[atTop]
        (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) := by
      refine IsBigO.of_bound (Real.sqrt (2 / π) * Real.exp |c.im|) ?_
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [norm_mul, norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos (Real.rpow_pos_of_pos hx _)]
      have hs : Real.sqrt (2 / (π * x)) = Real.sqrt (2 / π) * x ^ (-(1 / 2) : ℝ) := by
        rw [show 2 / (π * x) = 2 / π * x⁻¹ by field_simp, Real.sqrt_mul (by positivity),
          Real.sqrt_inv, Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
      have hcos : ‖cos ((x : ℂ) - ν * π / 2 - π / 4)‖ ≤ Real.exp |c.im| := by
        rw [show (x : ℂ) - ν * π / 2 - π / 4 = x - c by simp only [c]; ring, Complex.cos]
        have e1 : ‖exp ((x - c) * I)‖ = Real.exp c.im := by
          rw [Complex.norm_exp]; simp
        have e2 : ‖exp (-(x - c) * I)‖ = Real.exp (-c.im) := by
          rw [Complex.norm_exp]; simp
        calc ‖(exp ((x - c) * I) + exp (-(x - c) * I)) / 2‖
            ≤ (‖exp ((x - c) * I)‖ + ‖exp (-(x - c) * I)‖) / 2 := by
              rw [norm_div]; simp only [Complex.norm_ofNat]
              gcongr; exact norm_add_le _ _
          _ ≤ (Real.exp |c.im| + Real.exp |c.im|) / 2 := by
              rw [e1, e2]; gcongr
              · exact le_abs_self _
              · exact neg_le_abs _
          _ = Real.exp |c.im| := by ring
      rw [hs]
      calc Real.sqrt (2 / π) * x ^ (-(1 / 2) : ℝ) * ‖cos ((x : ℂ) - ν * π / 2 - π / 4)‖
          ≤ Real.sqrt (2 / π) * x ^ (-(1 / 2) : ℝ) * Real.exp |c.im| := by gcongr
        _ = _ := by ring
    exact (h1.add hc).congr' (Eventually.of_forall fun x => by ring)
      (Eventually.of_forall fun x => rfl)
  have h := (hH.sub hJ).const_mul_left (-I)
  refine h.congr' (Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => rfl)
  simp only [hankelH1]
  ring_nf
  rw [I_sq]; ring

/-- `K_ν(x) = O(x^{re ν - 1})` as `x → +∞` when `re ν ≤ 1/2`, from the Laplace representation
DLMF 11.5.2. -/
lemma struveMel_struveK_isBigO {ν : ℂ} (hν : ν.re ≤ 1 / 2) :
    (fun x : ℝ => struveK ν x) =O[atTop] (fun x : ℝ => x ^ (ν.re - 1)) := by
  set A : ℝ := ‖2 / ((Real.sqrt π : ℂ) * Gamma (ν + 1 / 2))‖
  refine IsBigO.of_bound (A * 2 ^ (-ν.re)) ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hre : 0 < (x : ℂ).re := by simpa using hx
  rw [struveK_eq_besselYLaplace ν hre, besselYLaplace]
  have hint : ‖∫ t in Ioi (0 : ℝ), yLaplaceKernel ν x t‖ ≤ 1 / x := by
    have hg : IntegrableOn (fun t : ℝ => Real.exp (-x * t)) (Ioi 0) :=
      exp_neg_integrableOn_Ioi 0 hx
    have hval : ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) = 1 / x := by
      have := integral_exp_mul_Ioi (a := -x) (by linarith) 0
      simp only [mul_zero, Real.exp_zero] at this
      rw [this]; field_simp
    rw [← hval]
    refine norm_integral_le_of_norm_le hg ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [yLaplaceKernel, norm_mul, Complex.norm_exp]
    have h1 : (1 + (t : ℂ) ^ 2) = ((1 + t ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [h1, norm_cpow_eq_rpow_re_of_pos (by positivity)]
    have h2 : (1 + t ^ 2) ^ (ν - 1 / 2).re ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith) (by simp; linarith)
    have h3 : (-(x : ℂ) * t).re = -x * t := by simp
    rw [h3]
    exact mul_le_of_le_one_right (Real.exp_pos _).le h2
  have hpow : ‖((x : ℂ) / 2) ^ ν‖ = 2 ^ (-ν.re) * x ^ ν.re := by
    rw [show (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) by push_cast; ring,
      norm_cpow_eq_rpow_re_of_pos (by positivity), Real.div_rpow hx.le (by norm_num),
      Real.rpow_neg (by norm_num)]
    ring
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx _)]
  calc ‖2 * ((x : ℂ) / 2) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2)) *
        ∫ t in Ioi (0 : ℝ), yLaplaceKernel ν x t‖
      = A * ‖((x : ℂ) / 2) ^ ν‖ * ‖∫ t in Ioi (0 : ℝ), yLaplaceKernel ν x t‖ := by
        simp only [A, norm_mul, norm_div]; ring
    _ ≤ A * (2 ^ (-ν.re) * x ^ ν.re) * (1 / x) := by
        rw [hpow]; gcongr
    _ = A * 2 ^ (-ν.re) * x ^ (ν.re - 1) := by
        rw [Real.rpow_sub_one hx.ne']; ring

/-- `H_ν(x) = O(x^{-1/2} + x^{re ν - 1})` as `x → +∞` when `re ν ≤ 1/2`. -/
lemma struveMel_struveH_isBigO {ν : ℂ} (hν : ν.re ≤ 1 / 2) :
    (fun x : ℝ => struveH ν x) =O[atTop] (fun x : ℝ => x ^ (-(1 / 2) : ℝ) + x ^ (ν.re - 1)) := by
  have hY := struveMel_besselY_isBigO ν
  have hK := struveMel_struveK_isBigO hν
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < x := eventually_gt_atTop 0
  have h1 : (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) =O[atTop]
      (fun x : ℝ => x ^ (-(1 / 2) : ℝ) + x ^ (ν.re - 1)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [hpos] with x hx
    have a := Real.rpow_pos_of_pos hx (-(1 / 2))
    have b := Real.rpow_pos_of_pos hx (ν.re - 1)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos a, abs_of_pos (by linarith)]
    linarith
  have h2 : (fun x : ℝ => x ^ (ν.re - 1)) =O[atTop]
      (fun x : ℝ => x ^ (-(1 / 2) : ℝ) + x ^ (ν.re - 1)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [hpos] with x hx
    have a := Real.rpow_pos_of_pos hx (-(1 / 2))
    have b := Real.rpow_pos_of_pos hx (ν.re - 1)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos b, abs_of_pos (by linarith)]
    linarith
  refine ((hY.trans h1).add (hK.trans h2)).congr' (Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => rfl)
  simp only [struveK]; ring

/-- The integration-by-parts boundary term `R^{μ-ν} H_ν(R)` tends to zero when `re ν ≤ 1/2`,
`re μ < 1` and `re μ < re ν + 1/2`. -/
lemma struveMel_tendsto_boundary {μ ν : ℂ} (hν : ν.re ≤ 1 / 2) (h1 : μ.re < 1)
    (h2 : μ.re < ν.re + 1 / 2) :
    Tendsto (fun R : ℝ => (R : ℂ) ^ (μ - ν) * struveH ν R) atTop (𝓝 0) := by
  have hp : (fun R : ℝ => (R : ℂ) ^ (μ - ν)) =O[atTop] (fun R : ℝ => R ^ (μ.re - ν.re)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    rw [norm_cpow_eq_rpow_re_of_pos hR, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hR _), one_mul]
    simp
  have hb := hp.mul (struveMel_struveH_isBigO hν)
  refine hb.trans_tendsto ?_
  have t1 := tendsto_rpow_neg_atTop (y := -(μ.re - ν.re - 1 / 2)) (by linarith)
  have t2 := tendsto_rpow_neg_atTop (y := -(μ.re - 1)) (by linarith)
  simp only [neg_neg] at t1 t2
  refine (t1.add t2).congr' ?_ |>.trans (by rw [add_zero])
  filter_upwards [eventually_gt_atTop 0] with R hR
  rw [mul_add, ← Real.rpow_add hR, ← Real.rpow_add hR]
  congr 1; ring_nf

/-- For `t > 0`, `t^a H_ν(t) = t^{a+ν+1} (1/2)^{ν+1} H̃_ν(t)` with the entire core `H̃_ν`. -/
lemma struveMel_cpow_mul_struveH (a ν : ℂ) {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ a * struveH ν t = (t : ℂ) ^ (a + ν + 1) * ((1 / 2 : ℂ) ^ (ν + 1) * struveHCore ν t) := by
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  rw [struveH, show (t : ℂ) / 2 = ((t : ℝ) : ℂ) * ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    mul_cpow_ofReal_nonneg ht.le (by norm_num), show ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) by push_cast; ring,
    show a + ν + 1 = a + (ν + 1) by ring, cpow_add a (ν + 1) ht0]
  ring

/-- The Struve Mellin integrand `t^{μ-ν-1} H_ν(t)` is interval integrable on `[0, R]`
when `re μ > -1`. -/
lemma struveMel_intervalIntegrable_struveH {μ : ℂ} (hμ0 : -1 < μ.re) (ν : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (μ - ν - 1) * struveH ν t) volume 0 R := by
  have h := (intervalIntegral.intervalIntegrable_cpow' hμ0 (a := 0) (b := R)).mul_continuousOn
    (g := fun t : ℝ => (1 / 2 : ℂ) ^ (ν + 1) * struveHCore ν t)
    (continuous_const.mul ((entire_struveHCore ν).continuous.comp continuous_ofReal)).continuousOn
  refine h.congr (fun t ht => ?_)
  rw [uIoc_of_le hR] at ht
  rw [struveMel_cpow_mul_struveH _ _ ht.1]
  ring_nf

/-- **Integration by parts** in the Struve Mellin integral, from `d/dt (t^{ν+1} H_{ν+1}) =
t^{ν+1} H_ν` (DLMF 11.4.27). -/
lemma struveMel_integral_by_parts {μ : ℂ} (hμ0 : -1 < μ.re) (ν : ℂ) {R : ℝ} (hR : 0 < R) :
    ∫ t in (0 : ℝ)..R, (t : ℂ) ^ (μ - ν - 1) * struveH ν t =
      (R : ℂ) ^ (μ - (ν + 1)) * struveH (ν + 1) R -
        (μ - 2 * ν - 2) * ∫ t in (0 : ℝ)..R, (t : ℂ) ^ (μ - (ν + 1) - 1) * struveH (ν + 1) t := by
  set F : ℝ → ℂ := fun t => (t : ℂ) ^ (μ + 1) * ((1 / 2 : ℂ) ^ (ν + 1 + 1) * struveHCore (ν + 1) t)
  have hF : ∀ t : ℝ, 0 < t → F t = (t : ℂ) ^ (μ - (ν + 1)) * struveH (ν + 1) t := by
    intro t ht
    rw [struveMel_cpow_mul_struveH _ _ ht]
    simp only [F]; ring_nf
  have hFc : ContinuousOn F (Icc 0 R) := by
    refine Continuous.continuousOn ?_
    refine Continuous.mul ?_ (continuous_const.mul
      ((entire_struveHCore (ν + 1)).continuous.comp continuous_ofReal))
    exact continuous_iff_continuousAt.mpr fun t =>
      continuousAt_ofReal_cpow_const t (μ + 1) (Or.inl (by simp; linarith))
  have hF0 : F 0 = 0 := by
    simp only [F, ofReal_zero]
    rw [zero_cpow (by intro h; have := congrArg Complex.re h; simp at this; linarith), zero_mul]
  set f' : ℝ → ℂ := fun t => (t : ℂ) ^ (μ - ν - 1) * struveH ν t +
    (μ - 2 * ν - 2) * ((t : ℂ) ^ (μ - (ν + 1) - 1) * struveH (ν + 1) t)
  have hderiv : ∀ t ∈ Ioo 0 R, HasDerivAt F (f' t) t := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
    have hs : (t : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr ht0
    have hφ := (struveH_weighted_deriv_27 (ν + 1) hs).comp_ofReal
    simp only [one_mul, add_sub_cancel_right] at hφ
    have hψ : HasDerivAt (fun x : ℝ => (x : ℂ) ^ (μ - 2 * ν - 2))
        ((μ - 2 * ν - 2) * (t : ℂ) ^ (μ - 2 * ν - 2 - 1)) t := by
      have h := ((hasDerivAt_id (t : ℂ)).cpow_const (c := μ - 2 * ν - 2) hs).comp_ofReal
      simpa using h
    have hprod := hψ.mul hφ
    have hev : (fun x : ℝ => (x : ℂ) ^ (μ - 2 * ν - 2) * ((x : ℂ) ^ (ν + 1) * struveH (ν + 1) x))
        =ᶠ[𝓝 t] F := by
      filter_upwards [Ioi_mem_nhds ht0] with x hx
      have hxc : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hx)
      rw [hF x hx, ← mul_assoc, ← cpow_add _ _ hxc]
      ring_nf
    refine (hprod.congr_of_eventuallyEq hev.symm).congr_deriv ?_
    simp only [f']
    have e1 : (t : ℂ) ^ (μ - 2 * ν - 2 - 1) * ((t : ℂ) ^ (ν + 1) * struveH (ν + 1) t) =
        (t : ℂ) ^ (μ - (ν + 1) - 1) * struveH (ν + 1) t := by
      rw [← mul_assoc, ← cpow_add _ _ htc]; ring_nf
    have e2 : (t : ℂ) ^ (μ - 2 * ν - 2) * ((t : ℂ) ^ (ν + 1) * struveH ν t) =
        (t : ℂ) ^ (μ - ν - 1) * struveH ν t := by
      rw [← mul_assoc, ← cpow_add _ _ htc]; ring_nf
    linear_combination (μ - 2 * ν - 2) * e1 + e2
  have hint1 := struveMel_intervalIntegrable_struveH hμ0 ν hR.le
  have hint2 := struveMel_intervalIntegrable_struveH hμ0 (ν + 1) hR.le
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR.le hFc hderiv
    (hint1.add (hint2.const_mul _))
  rw [hF0, sub_zero, hF R hR] at hftc
  simp only [f'] at hftc
  rw [intervalIntegral.integral_add hint1 (hint2.const_mul _),
    intervalIntegral.integral_const_mul] at hftc
  linear_combination hftc

/-- The value of the Struve Mellin transform, DLMF 11.7.10–11.7.11 (removable case `μ = 0`). -/
noncomputable def struveMel_value (μ ν : ℂ) : ℂ :=
  if μ = 0 then π / (2 ^ (ν + 1) * Gamma (ν + 1))
  else Gamma (μ / 2) * 2 ^ (μ - ν - 1) * sin (π * μ / 2) / (cos (π * μ / 2) * Gamma (ν - μ / 2 + 1))

/-- The recurrence `V(μ, ν) = 2 (ν + 1 - μ/2) V(μ, ν + 1)`, valid for all parameters. -/
lemma struveMel_value_succ (μ ν : ℂ) :
    struveMel_value μ ν = -(μ - 2 * ν - 2) * struveMel_value μ (ν + 1) := by
  have h2 : ∀ w : ℂ, (2 : ℂ) ^ (w + 1) = 2 * 2 ^ w := fun w => by
    rw [cpow_add _ _ two_ne_zero, cpow_one]; ring
  unfold struveMel_value
  split_ifs with hμ
  · have h := struveMel_div_Gamma_add_one (ν + 1)
    rw [show ν + 1 + 1 = (ν + 1) + 1 by ring, h2 (ν + 1)]
    rw [show -(μ - 2 * ν - 2) = 2 * (ν + 1) by rw [hμ]; ring]
    calc π / (2 ^ (ν + 1) * Gamma (ν + 1)) = π / 2 ^ (ν + 1) * (Gamma (ν + 1))⁻¹ := by
          rw [div_mul_eq_div_div, div_eq_mul_inv]
      _ = π / 2 ^ (ν + 1) * ((ν + 1) / Gamma (ν + 1 + 1)) := by rw [h]
      _ = _ := by
          have h0 : (2 : ℂ) ^ (ν + 1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
          field_simp
  · have h := struveMel_div_Gamma_add_one (ν - μ / 2 + 1)
    rw [show ν + 1 - μ / 2 + 1 = (ν - μ / 2 + 1) + 1 by ring,
      show μ - ν - 1 = (μ - (ν + 1) - 1) + 1 by ring, h2 (μ - (ν + 1) - 1),
      show -(μ - 2 * ν - 2) = 2 * (ν - μ / 2 + 1) by ring]
    calc Gamma (μ / 2) * (2 * 2 ^ (μ - (ν + 1) - 1)) * sin (π * μ / 2) /
          (cos (π * μ / 2) * Gamma (ν - μ / 2 + 1)) =
        Gamma (μ / 2) * (2 * 2 ^ (μ - (ν + 1) - 1)) * sin (π * μ / 2) / cos (π * μ / 2) *
          (Gamma (ν - μ / 2 + 1))⁻¹ := by
          rw [div_mul_eq_div_div, div_eq_mul_inv]
      _ = Gamma (μ / 2) * (2 * 2 ^ (μ - (ν + 1) - 1)) * sin (π * μ / 2) / cos (π * μ / 2) *
          ((ν - μ / 2 + 1) / Gamma (ν - μ / 2 + 1 + 1)) := by rw [h]
      _ = _ := by
          rw [mul_div_assoc', div_mul_eq_div_div]
          ring

/-- **The Struve Mellin transform** as an improper integral: for `|re μ| < 1` and
`re μ - 3/2 < re ν`, `∫₀^R t^{μ-ν-1} H_ν(t) dt → V(μ, ν)`. -/
theorem struveMel_tendsto {μ ν : ℂ} (hμ0 : -1 < μ.re) (hμ1 : μ.re < 1)
    (hν : μ.re - 3 / 2 < ν.re) :
    Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R, (t : ℂ) ^ (μ - ν - 1) * struveH ν t) atTop
      (𝓝 (struveMel_value μ ν)) := by
  suffices h : ∀ n : ℕ, ∀ ν : ℂ, -1 / 2 < ν.re + n → μ.re - 3 / 2 < ν.re →
      Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R, (t : ℂ) ^ (μ - ν - 1) * struveH ν t) atTop
        (𝓝 (struveMel_value μ ν)) from h 2 ν (by push_cast; linarith) hν
  intro n
  induction n with
  | zero =>
    intro ν hν1 _
    simp only [Nat.cast_zero, add_zero] at hν1
    have h := struveMel_tendsto_direct hμ0 hμ1 hν1
    rwa [struveMel_value_eq hμ0 hμ1 hν1] at h
  | succ n ih =>
    intro ν hν1 hν2
    by_cases hd : -1 / 2 < ν.re
    · have h := struveMel_tendsto_direct hμ0 hμ1 hd
      rwa [struveMel_value_eq hμ0 hμ1 hd] at h
    push Not at hd
    have hnext := ih (ν + 1) (by simp; push_cast at hν1; linarith) (by simp; linarith)
    have hb := struveMel_tendsto_boundary (μ := μ) (ν := ν + 1) (by simp; linarith) hμ1
      (by simp; linarith)
    rw [struveMel_value_succ μ ν]
    have hlim := hb.sub (hnext.const_mul (μ - 2 * ν - 2))
    rw [zero_sub, ← neg_mul] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    rw [struveMel_integral_by_parts hμ0 ν hR]

/-- struveH integral plain. -/
@[dlmf 11.7.E9]
theorem struveH_integral_plain {ν : ℂ} (h0 : -2 < ν.re) (h1 : ν.re < 0) :
    HasIntegralAtTop (fun t : ℝ => struveH ν t) 0 (-cos (π*ν/2)/sin (π*ν/2)) := by
  have h := struveMel_tendsto (μ := ν + 1) (ν := ν) (by simp; linarith) (by simp; linarith)
    (by simp; linarith)
  have he : ∀ t : ℝ, (t : ℂ) ^ (ν + 1 - ν - 1) * struveH ν t = struveH ν t := fun t => by
    rw [show ν + 1 - ν - 1 = 0 by ring, cpow_zero, one_mul]
  simp only [he] at h
  unfold HasIntegralAtTop
  convert h using 2
  unfold struveMel_value
  have hs : sin (π * (ν + 1) / 2) = cos (π * ν / 2) := by
    rw [show (π : ℂ) * (ν + 1) / 2 = π * ν / 2 + π / 2 by ring, Complex.sin_add_pi_div_two]
  have hc : cos (π * (ν + 1) / 2) = -sin (π * ν / 2) := by
    rw [show (π : ℂ) * (ν + 1) / 2 = π * ν / 2 + π / 2 by ring, Complex.cos_add_pi_div_two]
  split_ifs with hν1
  · have hν' : ν = -1 := by linear_combination hν1
    subst hν'
    rw [show (-1 : ℂ) + 1 = 0 by ring, Complex.Gamma_zero]
    have h1 : sin (π * (-1 : ℂ) / 2) = -1 := by
      rw [show (π : ℂ) * (-1) / 2 = -(π / 2) by ring, Complex.sin_neg, Complex.sin_pi_div_two]
    have h2 : cos (π * (-1 : ℂ) / 2) = 0 := by
      rw [show (π : ℂ) * (-1) / 2 = -(π / 2) by ring, Complex.cos_neg, Complex.cos_pi_div_two]
    rw [h1, h2]; simp
  · rw [hs, hc, show ν + 1 - ν - 1 = 0 by ring, cpow_zero, mul_one,
      show ν - (ν + 1) / 2 + 1 = (ν + 1) / 2 by ring]
    have hG : Gamma ((ν + 1) / 2) ≠ 0 := by
      refine Complex.Gamma_ne_zero fun m hm => ?_
      have hre := congrArg Complex.re hm
      simp at hre
      rcases m with _ | m
      · exact hν1 (by simpa using hm)
      · push_cast at hre; linarith
    field_simp

/-- struveH integral mellin zero. -/
@[dlmf 11.7.E10]
theorem struveH_integral_mellin_zero {ν : ℂ} (hν : -3/2 < ν.re) :
    HasIntegralAtTop (fun t : ℝ => (t:ℂ)^(-ν-1)*struveH ν t) 0 (π/(2^(ν+1)*Gamma (ν+1))) := by
  have h := struveMel_tendsto (μ := 0) (ν := ν) (by norm_num) (by norm_num) (by simp; linarith)
  simp only [struveMel_value, zero_sub] at h
  exact h

/-- struveH integral mellin. -/
@[dlmf 11.7.E11]
theorem struveH_integral_mellin {μ ν : ℂ} (hμ : |μ.re| < 1) (hν : μ.re-3/2 < ν.re) :
    HasIntegralAtTop (fun t : ℝ => (t:ℂ)^(μ-ν-1)*struveH ν t) 0 (if μ=0 then π/(2^(ν+1)*Gamma (ν+1)) else Gamma (μ/2)*2^(μ-ν-1)*sin (π*μ/2)/(cos (π*μ/2)*Gamma (ν-μ/2+1))) := by
  obtain ⟨h0, h1⟩ := abs_lt.mp hμ
  exact struveMel_tendsto h0 h1 hν

/-- struveH integral product. DLMF 11.7.12 states only `Re(μ+ν) > 0`; the integral then
diverges, e.g. at `μ = 3`, `ν = -2` the integrand grows like `t^(1/2) cos(...)`. The cross terms
`t^(-ν-3/2)` and `t^(-μ-3/2)` of the large-`t` expansion require `Re μ, Re ν > -3/2`
(hypotheses added 2026-10-20). -/
@[dlmf 11.7.E12]
theorem struveH_integral_product {μ ν : ℂ} (h : 0 < (μ+ν).re) (hμ : -3/2 < μ.re)
    (hν : -3/2 < ν.re) :
    HasIntegralAtTop (fun t : ℝ => (t:ℂ)^(-μ-ν)*struveH μ t*struveH ν t) 0 (Real.sqrt π*Gamma (μ+ν)/(2^(μ+ν)*Gamma (μ+ν+1/2)*Gamma (μ+1/2)*Gamma (ν+1/2))) := by
  sorry

/-- Fubini for the Laplace transform of a Poisson-weighted integral. -/
theorem laplace_poissonWeight {a : ℂ} {β : ℝ} (hβ : β < a.re) {k : ℝ → ℝ → ℂ}
    (hk : Continuous (Function.uncurry k))
    (hkb : ∀ t s : ℝ, 0 < t → s ∈ Ioc (0:ℝ) 1 → ‖k t s‖ ≤ Real.exp (β*t)) :
    IntegrableOn (fun t : ℝ => exp (-a*t) * ∫ s : ℝ in 0..1, (1-(s:ℂ)^2)^(-1/2:ℂ) * k t s)
      (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, exp (-a*t) * ∫ s : ℝ in 0..1, (1-(s:ℂ)^2)^(-1/2:ℂ) * k t s) =
      ∫ s : ℝ in 0..1, (1-(s:ℂ)^2)^(-1/2:ℂ) * ∫ t : ℝ in Ioi 0, exp (-a*t) * k t s := by
  set w : ℝ → ℂ := fun s => (1-(s:ℂ)^2)^(-1/2:ℂ)
  have hw : IntegrableOn w (Ioc 0 1) := by
    have := intervalIntegrable_poissonWeight (ν := 0) (by norm_num)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
    convert this using 3; norm_num
  set F : ℝ × ℝ → ℂ := fun p => exp (-a*p.1) * (w p.2 * k p.1 p.2)
  have hwm : Measurable w := by
    simp only [w]; fun_prop
  have hFm : AEStronglyMeasurable F ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioc (0:ℝ) 1))) := by
    apply Measurable.aestronglyMeasurable
    simp only [F]
    have hk' : Measurable (fun p : ℝ × ℝ => k p.1 p.2) := hk.measurable
    have : Measurable (fun p : ℝ × ℝ => w p.2) := hwm.comp measurable_snd
    fun_prop
  have hG : Integrable (fun p : ℝ × ℝ => Real.exp ((β - a.re)*p.1) * ‖w p.2‖)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioc (0:ℝ) 1))) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).mul_prod hw.norm
  have hF : Integrable F ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioc (0:ℝ) 1))) := by
    refine hG.mono' hFm ?_
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioc)] with p hp
    obtain ⟨ht, hs⟩ := hp
    simp only [F, norm_mul, Complex.norm_exp]
    have h1 := hkb p.1 p.2 ht hs
    have : (-a*(p.1:ℂ)).re = -a.re*p.1 := by simp
    rw [this]
    calc Real.exp (-a.re*p.1) * (‖w p.2‖ * ‖k p.1 p.2‖)
        ≤ Real.exp (-a.re*p.1) * (‖w p.2‖ * Real.exp (β*p.1)) := by gcongr
      _ = Real.exp ((β - a.re)*p.1) * ‖w p.2‖ := by
        rw [show (β - a.re)*p.1 = -a.re*p.1 + β*p.1 by ring, Real.exp_add]; ring
  have hswap := integral_integral_swap (f := fun t s => F (t, s)) hF
  have hint := hF.integral_prod_left
  constructor
  · refine (hint.congr (Eventually.of_forall fun t => ?_))
    simp only [F]
    rw [integral_const_mul, intervalIntegral.integral_of_le zero_le_one]
  · rw [intervalIntegral.integral_of_le zero_le_one]
    convert hswap using 1
    · refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [F]
      rw [integral_const_mul, intervalIntegral.integral_of_le zero_le_one]
    · refine integral_congr_ae (Eventually.of_forall fun s => ?_)
      simp only [F]
      rw [← integral_const_mul]
      congr 1; funext t; ring

/-- `∫₀^∞ e^{-at} e^{ct} dt = 1/(a-c)` for `Re c < Re a`. -/
theorem integral_exp_neg_mul_exp_Ioi {a c : ℂ} (h : c.re < a.re) :
    IntegrableOn (fun t : ℝ => exp (-a*t) * exp (c*t)) (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, exp (-a*t) * exp (c*t)) = 1/(a-c) := by
  have he : (fun t : ℝ => exp (-a*t) * exp (c*t)) = fun t : ℝ => exp ((c-a)*t) := by
    funext t; rw [← Complex.exp_add]; ring_nf
  have hre : (c-a).re < 0 := by simp; linarith
  have hne : a - c ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0; simp at this; linarith
  rw [he]
  refine ⟨integrableOn_exp_mul_complex_Ioi hre 0, ?_⟩
  rw [integral_exp_mul_complex_Ioi hre 0]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  have hne' : c - a ≠ 0 := fun h0 => hne (by linear_combination -h0)
  field_simp
  ring

/-- Laplace transform of `sin(st)`. -/
theorem laplace_sin_mul {a : ℂ} (ha : 0 < a.re) (s : ℝ) :
    (∫ t : ℝ in Ioi 0, exp (-a*t) * sin ((t:ℂ)*s)) = s/(a^2+s^2) := by
  have h1 := integral_exp_neg_mul_exp_Ioi (a := a) (c := I*s) (by simpa using ha)
  have h2 := integral_exp_neg_mul_exp_Ioi (a := a) (c := -I*s) (by simpa using ha)
  have hsin : ∀ t : ℝ, exp (-a*t) * sin ((t:ℂ)*s) =
      (exp (-a*t) * exp (I*s*t) - exp (-a*t) * exp (-I*s*t)) / (2*I) := by
    intro t
    have h2I : (2:ℂ)*I ≠ 0 := by simp
    rw [eq_div_iff h2I, Complex.sin]
    ring_nf; rw [I_sq]; ring_nf
  simp_rw [hsin]
  rw [integral_div, integral_sub h1.1 h2.1, h1.2, h2.2]
  have hp : a - I*s ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0; simp at this; linarith
  have hm : a - -I*s ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0; simp at this; linarith
  have hprod : (a - I*s)*(a - -I*s) = a^2+s^2 := by ring_nf; rw [I_sq]; ring
  have key : 1/(a - I*s) - 1/(a - -I*s) = (2*I) * (s/(a^2+s^2)) := by
    rw [div_sub_div _ _ hp hm, hprod]; ring
  rw [key, mul_div_cancel_left₀ _ (by simp : (2:ℂ)*I ≠ 0)]

/-- Laplace transform of `sinh(st)`. -/
theorem laplace_sinh_mul {a : ℂ} (ha : 1 < a.re) {s : ℝ} (hs : s ∈ Ioc (0:ℝ) 1) :
    (∫ t : ℝ in Ioi 0, exp (-a*t) * sinh ((t:ℂ)*s)) = s/(a^2-s^2) := by
  have h1 := integral_exp_neg_mul_exp_Ioi (a := a) (c := (s:ℂ)) (by simp; linarith [hs.2])
  have h2 := integral_exp_neg_mul_exp_Ioi (a := a) (c := -(s:ℂ)) (by simp; linarith [hs.1])
  have hsinh : ∀ t : ℝ, exp (-a*t) * sinh ((t:ℂ)*s) =
      (exp (-a*t) * exp (s*t) - exp (-a*t) * exp (-s*t)) / 2 := by
    intro t
    rw [Complex.sinh]
    ring_nf
  simp_rw [hsinh]
  rw [integral_div, integral_sub h1.1 h2.1, h1.2, h2.2]
  have hp : a - s ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0; simp at this; linarith [hs.2]
  have hm : a - -(s:ℂ) ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0; simp at this; linarith [hs.1]
  have key : 1/(a - s) - 1/(a - -(s:ℂ)) = 2 * (s/(a^2-s^2)) := by
    rw [div_sub_div _ _ hp hm, show (a - s)*(a - -(s:ℂ)) = a^2-s^2 by ring]; ring
  rw [key, mul_div_cancel_left₀ _ (by norm_num : (2:ℂ) ≠ 0)]

/-- Principal square roots of slit-plane numbers lie in the open right half-plane. -/
theorem re_cpow_half_pos {x : ℂ} (hx : x ∈ slitPlane) : 0 < (x^(1/2:ℂ)).re := by
  rw [show (1/2:ℂ) = ((1/2:ℝ):ℂ) by push_cast; ring, cpow_ofReal_re]
  have hx0 := slitPlane_ne_zero hx
  have harg := (mem_slitPlane_iff_arg.1 hx).1
  have h1 : -π < arg x := neg_pi_lt_arg x
  have h2 : arg x < π := lt_of_le_of_ne (arg_le_pi x) harg
  apply mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.2 hx0) _)
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith [Real.pi_pos]

theorem cpow_half_sq (x : ℂ) : (x^(1/2:ℂ))^2 = x := by
  have := cpow_nat_inv_pow x (n := 2) two_ne_zero
  rwa [show ((2:ℕ):ℂ)⁻¹ = 1/2 by norm_num] at this

theorem eq_of_sq_eq_of_re_pos {r a : ℂ} (hr : 0 < r.re) (ha : 0 < a.re) (h : r^2 = a^2) :
    r = a := by
  have h0 : (r - a)*(r + a) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h0 with h1 | h1
  · linear_combination h1
  · exfalso; have := congrArg Complex.re h1; simp at this; linarith

theorem div_mem_slitPlane_of_re_pos {p r : ℂ} (hp : 0 < p.re) (hr : 0 < r.re) :
    p / r ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_contra hc
  push Not at hc
  have hr0 : r ≠ 0 := fun h => by rw [h] at hr; simp at hr
  have hpe : p = (p/r)*r := by field_simp
  have : p.re = (p/r).re * r.re := by
    conv_lhs => rw [hpe]
    simp [mul_re, hc.2]
  nlinarith [hc.1]

theorem sq_add_mem_slitPlane {a : ℂ} (ha : 0 < a.re) {u : ℝ} (hu : 0 ≤ u) :
    a^2 + u ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases him : a.im = 0
  · left
    have : (a^2 + u).re = a.re^2 - a.im^2 + u := by simp [sq, mul_re]
    rw [this, him]; nlinarith
  · right
    have : (a^2 + u).im = 2*a.re*a.im := by simp [sq, mul_im]; ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero two_ne_zero ha.ne') him

/-- `∫₀¹ du/(b²-u²) = log((1+b)/a)/b` with `b = (1+a²)^{1/2}`, `Re a > 0`. -/
theorem integral_recip_one_add_sq_sub_sq {a : ℂ} (ha : 0 < a.re) :
    (∫ u : ℝ in 0..1, 1/((1+a^2) - (u:ℂ)^2)) =
      log ((1+(1+a^2)^(1/2:ℂ))/a) / (1+a^2)^(1/2:ℂ) := by
  set b : ℂ := (1+a^2)^(1/2:ℂ) with hbdef
  have hslit : ∀ u : ℝ, u ∈ uIcc (0:ℝ) 1 → a^2 + ((1-u^2:ℝ):ℂ) ∈ slitPlane := by
    intro u hu
    rw [uIcc_of_le zero_le_one] at hu
    exact sq_add_mem_slitPlane ha (by nlinarith [hu.1, hu.2])
  have hb1 : a^2 + ((1-(0:ℝ)^2:ℝ):ℂ) = 1+a^2 := by push_cast; ring
  have hbre : 0 < b.re := by
    have := re_cpow_half_pos (hslit 0 (by simp))
    rwa [hb1] at this
  have hb2 : b^2 = 1+a^2 := cpow_half_sq _
  set r : ℝ → ℂ := fun u => (a^2 + ((1-u^2:ℝ):ℂ))^(1/2:ℂ) with hrdef
  have hrre : ∀ u ∈ uIcc (0:ℝ) 1, 0 < (r u).re := fun u hu => re_cpow_half_pos (hslit u hu)
  have hr2 : ∀ u : ℝ, (r u)^2 = b^2 - (u:ℂ)^2 := by
    intro u; simp only [r]; rw [cpow_half_sq, hb2]; push_cast; ring
  have hr0 : r 0 = b := by simp only [r]; rw [hb1]
  have hr1 : r 1 = a := by
    apply eq_of_sq_eq_of_re_pos (hrre 1 (by simp)) ha
    rw [hr2, hb2]; push_cast; ring
  set Φ : ℝ → ℂ := fun u => log ((b+u)/r u) / b
  have hbne : b ≠ 0 := fun h => by rw [h] at hbre; simp at hbre
  have hderiv : ∀ u ∈ uIcc (0:ℝ) 1, HasDerivAt Φ (1/((1+a^2) - (u:ℂ)^2)) u := by
    intro u hu
    have hrne : r u ≠ 0 := fun h => by have := hrre u hu; rw [h] at this; simp at this
    have hpre : 0 < (b + u).re := by
      rw [uIcc_of_le zero_le_one] at hu; simp; linarith [hu.1]
    have hpne : b + (u:ℂ) ≠ 0 := fun h => by rw [h] at hpre; simp at hpre
    have hq : HasDerivAt (fun u : ℝ => a^2 + ((1-u^2:ℝ):ℂ)) (-(2*(u:ℂ))) u := by
      have := ((hasDerivAt_pow 2 u).const_sub 1).ofReal_comp.const_add (a^2)
      convert this using 1; push_cast; ring
    have hr : HasDerivAt r (-(u:ℂ) / r u) u := by
      have := (hasStrictDerivAt_cpow_const (c := 1/2) (hslit u hu)).hasDerivAt.comp u hq
      refine this.congr_deriv ?_
      set Q : ℂ := a^2 + ((1-u^2:ℝ):ℂ) with hQdef
      have hQne : Q ≠ 0 := slitPlane_ne_zero (hslit u hu)
      have hru : r u = Q^(1/2:ℂ) := rfl
      have hQ : Q = (r u)^2 := (cpow_half_sq Q).symm
      have : Q^((1/2:ℂ)-1) = (r u)⁻¹ := by
        rw [cpow_sub _ _ hQne, cpow_one, ← hru]
        conv_lhs => rw [hQ]
        field_simp
      rw [this]; field_simp
    have hp : HasDerivAt (fun u : ℝ => b + (u:ℂ)) 1 u := by
      simpa using (hasDerivAt_id (u:ℝ)).ofReal_comp.const_add b
    have hdiv := hp.div hr hrne
    have hlog := hdiv.clog_real (div_mem_slitPlane_of_re_pos hpre (hrre u hu))
    have := hlog.div_const b
    convert this using 1
    have hr2u := hr2 u
    rw [← hb2]
    have hden : b^2 - (u:ℂ)^2 ≠ 0 := by rw [← hr2u]; exact pow_ne_zero 2 hrne
    simp only [Pi.div_apply]
    field_simp
    linear_combination (b*(u:ℂ) + (u:ℂ)^2) * hr2u
  have hcont : ContinuousOn (fun u : ℝ => 1/((1+a^2) - (u:ℂ)^2)) (uIcc 0 1) := by
    refine continuousOn_const.div (by fun_prop) fun u hu => ?_
    have hrne : r u ≠ 0 := fun h => by have := hrre u hu; rw [h] at this; simp at this
    rw [← hb2, ← hr2]; exact pow_ne_zero 2 hrne
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  simp only [Φ, hr0, hr1]
  push_cast
  rw [add_zero, div_self hbne, log_one, zero_div, sub_zero, add_comm]

theorem one_add_sq_sub_sq_ne_zero {a : ℂ} (ha : 0 < a.re) {u : ℝ} (hu : u ∈ uIcc (0:ℝ) 1) :
    (1+a^2) - (u:ℂ)^2 ≠ 0 := by
  rw [uIcc_of_le zero_le_one] at hu
  have := slitPlane_ne_zero (sq_add_mem_slitPlane ha (u := 1-u^2) (by nlinarith [hu.1, hu.2]))
  convert this using 1; push_cast; ring

/-- `∫₀¹ (1-s²)^{-1/2} s/(a²+s²) ds = log((1+b)/a)/b`. -/
theorem integral_poissonWeight_mul_div_sq_add {a : ℂ} (ha : 0 < a.re) :
    (∫ s : ℝ in 0..1, (1-(s:ℂ)^2)^(-1/2:ℂ) * ((s:ℂ)/(a^2+(s:ℂ)^2))) =
      log ((1+(1+a^2)^(1/2:ℂ))/a) / (1+a^2)^(1/2:ℂ) := by
  have h := integral_poissonWeight_eq_trig 0 (fun s : ℝ => (s:ℂ)/(a^2+(s:ℂ)^2))
  rw [show (0:ℂ)-1/2 = -1/2 by ring] at h
  rw [h, ← integral_recip_one_add_sq_sub_sq ha]
  simp only [mul_zero, cpow_zero, mul_one]
  set g : ℝ → ℂ := fun u => 1/((1+a^2) - (u:ℂ)^2)
  have hsub := intervalIntegral.integral_deriv_smul_comp' (a := 0) (b := π/2) (f := Real.sin)
    (f' := Real.cos) (g := g) (fun x _ => Real.hasDerivAt_sin x) Real.continuous_cos.continuousOn
    (by
      refine ContinuousOn.mono (s := uIcc 0 1) ?_ ?_
      · exact continuousOn_const.div (by fun_prop) fun u hu => one_add_sq_sub_sq_ne_zero ha hu
      · rintro _ ⟨x, hx, rfl⟩
        rw [uIcc_of_le (by positivity)] at hx
        rw [uIcc_of_le zero_le_one]
        exact ⟨Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2, Real.pi_pos]),
          Real.sin_le_one x⟩)
  rw [Real.sin_zero, Real.sin_pi_div_two] at hsub
  rw [← hsub]
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  simp only [g, Function.comp, real_smul]
  have hc : (Real.cos θ : ℂ)^2 = 1 - (Real.sin θ : ℂ)^2 := by
    rw [← ofReal_pow, ← ofReal_pow, Real.cos_sq']; push_cast; ring
  rw [hc]; ring

/-- `H₀` is bounded on the positive real axis. -/
theorem exists_bound_struveH_zero : ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ‖struveH 0 t‖ ≤ C := by
  set w : ℝ → ℂ := fun s => (1-(s:ℂ)^2)^(-1/2:ℂ)
  have hw : IntervalIntegrable w volume 0 1 := by
    have := intervalIntegrable_poissonWeight (ν := 0) (by norm_num)
    convert this using 3; norm_num
  refine ⟨2/π * ∫ s : ℝ in 0..1, ‖w s‖, fun t ht => ?_⟩
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    simp only [ofReal_zero, struveH, zero_div, zero_add, cpow_one, zero_mul, norm_zero]
    exact mul_nonneg (by positivity) (intervalIntegral.integral_nonneg zero_le_one fun _ _ =>
      norm_nonneg _)
  rw [struveH_eq_poisson (by norm_num) (ofReal_ne_zero.2 hpos.ne')]
  rw [cpow_zero, zero_add, Complex.Gamma_one_half_eq, show (0:ℂ)-1/2 = -1/2 by ring]
  have hs : (π:ℂ)^(1/2:ℂ) = (Real.sqrt π : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]; push_cast; ring_nf
  have hp : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  rw [hs, hp, mul_one, norm_mul]
  have h2 : ‖(2:ℂ)/π‖ = 2/π := by
    rw [norm_div, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [h2]
  gcongr
  refine (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans ?_
  refine intervalIntegral.integral_mono_on zero_le_one ?_ hw.norm fun s _ => ?_
  · exact (hw.mul_continuousOn (by fun_prop)).norm
  · rw [norm_mul]
    have : ‖sin ((t:ℂ)*s)‖ ≤ 1 := by
      rw [← ofReal_mul, ← ofReal_sin, norm_real, Real.norm_eq_abs]
      exact Real.abs_sin_le_one _
    calc ‖w s‖ * ‖sin ((t:ℂ)*s)‖ ≤ ‖w s‖ * 1 := by gcongr
      _ = ‖w s‖ := mul_one _

theorem sq_sub_one_add_mem_slitPlane {a : ℂ} (ha : 1 < a.re) {u : ℝ} (hu : 0 ≤ u) :
    a^2 - 1 + u ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases him : a.im = 0
  · left
    have : (a^2 - 1 + u).re = a.re^2 - a.im^2 - 1 + u := by simp [sq, mul_re]
    rw [this, him]; nlinarith
  · right
    have : (a^2 - 1 + u).im = 2*a.re*a.im := by simp [sq, mul_im]; ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (by linarith)) him

theorem one_sub_recip_sq_mem_slitPlane {a : ℂ} (ha : 1 < a.re) : 1 - 1/a^2 ∈ slitPlane := by
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha; linarith
  rw [mem_slitPlane_iff]
  by_cases him : a.im = 0
  · left
    have hae : a = (a.re:ℂ) := Complex.ext (by simp) (by simp [him])
    rw [hae, ← ofReal_pow, ← ofReal_one, ← ofReal_div, ← ofReal_sub, ofReal_re]
    have h1 : 1 < a.re^2 := by nlinarith
    have : 1/a.re^2 < 1 := by rw [div_lt_one (by positivity)]; exact h1
    linarith
  · right
    have h2 : (a^2).im ≠ 0 := by
      rw [sq, mul_im]; intro h; apply him; nlinarith [h]
    rw [sub_im, one_im, one_div, inv_im, zero_sub, neg_ne_zero, neg_div, neg_ne_zero]
    exact div_ne_zero h2 (normSq_pos.2 (pow_ne_zero 2 ha0)).ne'

/-- `√(a²-1) = a √(1-a⁻²)` for `Re a > 1`. -/
theorem cpow_half_sq_sub_one {a : ℂ} (ha : 1 < a.re) :
    (a^2-1)^(1/2:ℂ) = a * (1-1/a^2)^(1/2:ℂ) := by
  set S : Set ℂ := {z | 1 < z.re}
  have hS : IsPreconnected S := (convex_halfSpace_re_gt 1).isPreconnected
  have hslit1 : ∀ z ∈ S, z^2 - 1 ∈ slitPlane := fun z hz => by
    simpa using sq_sub_one_add_mem_slitPlane (u := 0) hz le_rfl
  have hf : ContinuousOn (fun z : ℂ => (z^2-1)^(1/2:ℂ)) S := fun z hz =>
    ((by fun_prop : ContinuousAt (fun z : ℂ => z^2-1) z).cpow continuousAt_const
      (hslit1 z hz)).continuousWithinAt
  have hz0 : ∀ z ∈ S, z ≠ 0 := fun z hz h => by
    simp only [S, mem_ofPred_eq] at hz; rw [h] at hz; simp at hz; linarith
  have hg : ContinuousOn (fun z : ℂ => z * (1-1/z^2)^(1/2:ℂ)) S := fun z hz => by
    have h1 : ContinuousAt (fun z : ℂ => 1 - 1/z^2) z :=
      continuousAt_const.sub (continuousAt_const.div (by fun_prop) (pow_ne_zero 2 (hz0 z hz)))
    exact (continuousAt_id.mul (h1.cpow continuousAt_const
      (one_sub_recip_sq_mem_slitPlane hz))).continuousWithinAt
  have hsq : EqOn ((fun z : ℂ => (z^2-1)^(1/2:ℂ))^2) ((fun z : ℂ => z * (1-1/z^2)^(1/2:ℂ))^2) S := by
    intro z hz
    simp only [Pi.pow_apply, mul_pow, cpow_half_sq]
    field_simp [hz0 z hz]
  have hne : ∀ {z : ℂ}, z ∈ S → z * (1-1/z^2)^(1/2:ℂ) ≠ 0 := by
    intro z hz
    refine mul_ne_zero (hz0 z hz) fun h => ?_
    have := re_cpow_half_pos (one_sub_recip_sq_mem_slitPlane hz)
    rw [h] at this; simp at this
  have h2 : (2:ℂ) ∈ S := by simp [S]
  rcases hS.eq_or_eq_neg_of_sq_eq hf hg hsq hne with h | h
  · exact h ha
  · exfalso
    have h1 := h h2
    have hp1 := re_cpow_half_pos (hslit1 2 h2)
    have hp2 := re_cpow_half_pos (one_sub_recip_sq_mem_slitPlane (a := 2) (by simp))
    simp only [Pi.neg_apply] at h1
    rw [h1] at hp1
    simp only [neg_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero] at hp1
    linarith

/-- For `Re q > 0` and `Re p = Re q`, the quotient `p/q` lies in the slit plane. -/
theorem div_mem_slitPlane_of_re_eq {p q : ℂ} (hq : 0 < q.re) (h : p.re = q.re) :
    p / q ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_contra hc
  push Not at hc
  have hq0 : q ≠ 0 := fun h0 => by rw [h0] at hq; simp at hq
  have hpe : p = (p/q)*q := by field_simp
  have : p.re = (p/q).re * q.re := by
    conv_lhs => rw [hpe]
    simp [mul_re, hc.2]
  nlinarith [hc.1]

theorem sq_sub_one_add_sq_ne_zero {a : ℂ} (ha : 1 < a.re) (u : ℝ) :
    (a^2-1) + (u:ℂ)^2 ≠ 0 := by
  have := slitPlane_ne_zero (sq_sub_one_add_mem_slitPlane ha (u := u^2) (sq_nonneg u))
  convert this using 1; push_cast; ring

/-- Logarithmic form of `∫₀¹ du/(c²+u²)`, `c = (a²-1)^{1/2}`. -/
theorem integral_recip_sq_sub_one_add_sq_log {a : ℂ} (ha : 1 < a.re) :
    (∫ u : ℝ in 0..1, 1/((a^2-1) + (u:ℂ)^2)) =
      -I*log (I/a+(1-1/a^2)^(1/2:ℂ)) / (a^2-1)^(1/2:ℂ) := by
  set c : ℂ := (a^2-1)^(1/2:ℂ) with hcdef
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha; linarith
  have hslit : ∀ u : ℝ, a^2 - 1 + ((u^2:ℝ):ℂ) ∈ slitPlane :=
    fun u => sq_sub_one_add_mem_slitPlane ha (sq_nonneg u)
  have hcre : 0 < c.re := by
    have := re_cpow_half_pos (hslit 0)
    rwa [show a^2-1+(((0:ℝ)^2:ℝ):ℂ) = a^2-1 by push_cast; ring] at this
  have hc2 : c^2 = a^2-1 := cpow_half_sq _
  have hcne : c ≠ 0 := fun h => by rw [h] at hcre; simp at hcre
  set r : ℝ → ℂ := fun u => (a^2 - 1 + ((u^2:ℝ):ℂ))^(1/2:ℂ) with hrdef
  have hrre : ∀ u, 0 < (r u).re := fun u => re_cpow_half_pos (hslit u)
  have hrne : ∀ u, r u ≠ 0 := fun u h => by have := hrre u; rw [h] at this; simp at this
  have hr2 : ∀ u : ℝ, (r u)^2 = c^2 + (u:ℂ)^2 := by
    intro u; simp only [r]; rw [cpow_half_sq, hc2]; push_cast; ring
  have hr0 : r 0 = c := by simp [r, c]
  have hr1 : r 1 = a := by
    have ha' : 0 < a.re := by linarith
    apply eq_of_sq_eq_of_re_pos (hrre 1) ha'
    rw [hr2, hc2]; push_cast; ring
  set Ψ : ℝ → ℂ := fun u => -I*log ((c+I*u)/r u) / c
  have hderiv : ∀ u ∈ uIcc (0:ℝ) 1, HasDerivAt Ψ (1/((a^2-1) + (u:ℂ)^2)) u := by
    intro u _
    have hpre : 0 < (c + I*u).re := by simp; exact hcre
    have hpne : c + I*(u:ℂ) ≠ 0 := fun h => by rw [h] at hpre; simp at hpre
    have hq : HasDerivAt (fun u : ℝ => a^2 - 1 + ((u^2:ℝ):ℂ)) (2*(u:ℂ)) u := by
      have := (hasDerivAt_pow 2 u).ofReal_comp.const_add (a^2-1)
      convert this using 1; push_cast; ring
    have hr : HasDerivAt r ((u:ℂ) / r u) u := by
      have := (hasStrictDerivAt_cpow_const (c := 1/2) (hslit u)).hasDerivAt.comp u hq
      refine this.congr_deriv ?_
      set Q : ℂ := a^2 - 1 + ((u^2:ℝ):ℂ) with hQdef
      have hQne : Q ≠ 0 := slitPlane_ne_zero (hslit u)
      have hru : r u = Q^(1/2:ℂ) := rfl
      have hQ : Q = (r u)^2 := (cpow_half_sq Q).symm
      have : Q^((1/2:ℂ)-1) = (r u)⁻¹ := by
        rw [cpow_sub _ _ hQne, cpow_one, ← hru]
        conv_lhs => rw [hQ]
        field_simp [hrne u]
      rw [this]; field_simp [hrne u]
    have hp : HasDerivAt (fun u : ℝ => c + I*(u:ℂ)) I u := by
      simpa using ((hasDerivAt_id (u:ℝ)).ofReal_comp.const_mul I).const_add c
    have hdiv := hp.div hr (hrne u)
    have hlog := hdiv.clog_real (div_mem_slitPlane_of_re_pos hpre (hrre u))
    have := (hlog.const_mul (-I)).div_const c
    convert this using 1
    have hr2u := hr2 u
    rw [← hc2]
    have hden : c^2 + (u:ℂ)^2 ≠ 0 := by rw [← hr2u]; exact pow_ne_zero 2 (hrne u)
    have hrn := hrne u
    have hpne' : c + (u:ℂ)*I ≠ 0 := by rw [mul_comm]; exact hpne
    simp only [Pi.div_apply]
    field_simp
    linear_combination (c*(u:ℂ)*I - (u:ℂ)^2) * hr2u +
      (c^2*(r u)^2 - c^2*(u:ℂ)^2 + (r u)^2*(u:ℂ)^2 - (u:ℂ)^4) * I_sq
  have hcont : ContinuousOn (fun u : ℝ => 1/((a^2-1) + (u:ℂ)^2)) (uIcc 0 1) :=
    continuousOn_const.div (by fun_prop) fun u _ => sq_sub_one_add_sq_ne_zero ha u
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  simp only [Ψ, hr0, hr1]
  push_cast
  rw [mul_zero, add_zero, div_self hcne, log_one, mul_zero, zero_div, sub_zero, mul_one]
  congr 3
  rw [hcdef, cpow_half_sq_sub_one ha]
  field_simp
  ring

/-- Arctangent form of `∫₀¹ du/(c²+u²)`, `c = (a²-1)^{1/2}`. -/
theorem integral_recip_sq_sub_one_add_sq_arctan {a : ℂ} (ha : 1 < a.re) :
    (∫ u : ℝ in 0..1, 1/((a^2-1) + (u:ℂ)^2)) =
      arctan (1/((a^2-1)^(1/2:ℂ))) / (a^2-1)^(1/2:ℂ) := by
  set c : ℂ := (a^2-1)^(1/2:ℂ) with hcdef
  have hcre : 0 < c.re := by
    have := re_cpow_half_pos (sq_sub_one_add_mem_slitPlane ha (u := 0) le_rfl)
    rwa [show a^2-1+((0:ℝ):ℂ) = a^2-1 by push_cast; ring] at this
  have hc2 : c^2 = a^2-1 := cpow_half_sq _
  have hcne : c ≠ 0 := fun h => by rw [h] at hcre; simp at hcre
  set Λ : ℝ → ℂ := fun u => -I/2 * log ((1+(u/c)*I)/(1-(u/c)*I)) / c
  have hderiv : ∀ u ∈ uIcc (0:ℝ) 1, HasDerivAt Λ (1/((a^2-1) + (u:ℂ)^2)) u := by
    intro u _
    have hD : 1-((u:ℂ)/c)*I ≠ 0 := by
      intro h
      have : c - (u:ℂ)*I = c * (1-((u:ℂ)/c)*I) := by field_simp
      rw [h, mul_zero] at this
      have := congrArg Complex.re this; simp at this; linarith
    have hN : 1+((u:ℂ)/c)*I ≠ 0 := by
      intro h
      have : c + (u:ℂ)*I = c * (1+((u:ℂ)/c)*I) := by field_simp
      rw [h, mul_zero] at this
      have := congrArg Complex.re this; simp at this; linarith
    have hslit : (1+((u:ℂ)/c)*I)/(1-((u:ℂ)/c)*I) ∈ slitPlane := by
      have : (1+((u:ℂ)/c)*I)/(1-((u:ℂ)/c)*I) = (c + (u:ℂ)*I)/(c - (u:ℂ)*I) := by
        field_simp
      rw [this]
      exact div_mem_slitPlane_of_re_eq (by simpa using hcre) (by simp)
    have hNd : HasDerivAt (fun u : ℝ => 1+((u:ℂ)/c)*I) (I/c) u := by
      have := (((hasDerivAt_id (u:ℝ)).ofReal_comp.div_const c).mul_const I).const_add 1
      exact this.congr_deriv (by norm_num; ring)
    have hDd : HasDerivAt (fun u : ℝ => 1-((u:ℂ)/c)*I) (-(I/c)) u := by
      have := (((hasDerivAt_id (u:ℝ)).ofReal_comp.div_const c).mul_const I).const_sub 1
      exact this.congr_deriv (by norm_num; ring)
    have hlog := (hNd.div hDd hD).clog_real hslit
    have := (hlog.const_mul (-I/2)).div_const c
    convert this using 1
    rw [← hc2]
    have hden : c^2 + (u:ℂ)^2 ≠ 0 := by rw [hc2]; exact sq_sub_one_add_sq_ne_zero ha u
    have hden' : c^2 - (u:ℂ)^2*I^2 ≠ 0 := by rw [I_sq]; convert hden using 1; ring
    simp only [Pi.div_apply]
    field_simp
    ring_nf
    rw [I_sq]
    ring_nf
    linear_combination (-2*c) * mul_inv_cancel₀ hden
  have hcont : ContinuousOn (fun u : ℝ => 1/((a^2-1) + (u:ℂ)^2)) (uIcc 0 1) :=
    continuousOn_const.div (by fun_prop) fun u _ => sq_sub_one_add_sq_ne_zero ha u
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  simp only [Λ, Complex.arctan]
  push_cast
  simp

/-- Poisson form of `L₀` on the positive axis. -/
theorem struveL_zero_eq_poisson {t : ℝ} (ht : 0 < t) :
    struveL 0 t = 2/π * ∫ s : ℝ in 0..1, (1-(s:ℂ)^2)^(-1/2:ℂ) * sinh ((t:ℂ)*s) := by
  rw [struveL_eq_poisson (by norm_num) (ofReal_ne_zero.2 ht.ne')]
  rw [cpow_zero, zero_add, Complex.Gamma_one_half_eq, show (0:ℂ)-1/2 = -1/2 by ring]
  have hs : (π:ℂ)^(1/2:ℂ) = (Real.sqrt π : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]; push_cast; ring_nf
  have hp : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  rw [hs, hp]; ring

theorem norm_sinh_mul_le {t s : ℝ} (ht : 0 < t) (hs : s ∈ Ioc (0:ℝ) 1) :
    ‖sinh ((t:ℂ)*s)‖ ≤ Real.exp (1*t) := by
  rw [← ofReal_mul, ← ofReal_sinh, norm_real, Real.norm_eq_abs, one_mul,
    abs_of_nonneg (Real.sinh_nonneg_iff.2 (by nlinarith [hs.1])), Real.sinh_eq]
  have h1 : Real.exp (t*s) ≤ Real.exp t := Real.exp_le_exp.2 (by nlinarith [hs.2])
  have h2 : 0 < Real.exp (-(t*s)) := Real.exp_pos _
  have h3 : 0 < Real.exp t := Real.exp_pos _
  linarith

/-- `L₀` grows at most like `e^t` on the positive axis. -/
theorem exists_bound_struveL_zero :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ‖struveL 0 t‖ ≤ C * Real.exp t := by
  set w : ℝ → ℂ := fun s => (1-(s:ℂ)^2)^(-1/2:ℂ)
  have hw : IntervalIntegrable w volume 0 1 := by
    have := intervalIntegrable_poissonWeight (ν := 0) (by norm_num)
    convert this using 3; norm_num
  set C : ℝ := 2/π * ∫ s : ℝ in 0..1, ‖w s‖
  have hC : 0 ≤ C := mul_nonneg (by positivity)
    (intervalIntegral.integral_nonneg zero_le_one fun _ _ => norm_nonneg _)
  refine ⟨C, fun t ht => ?_⟩
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    simp only [ofReal_zero, struveL, zero_div, zero_add, cpow_one, zero_mul, norm_zero]
    positivity
  rw [struveL_zero_eq_poisson hpos, norm_mul]
  have h2 : ‖(2:ℂ)/π‖ = 2/π := by
    rw [norm_div, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [h2, show C * Real.exp t = 2/π * ((∫ s : ℝ in 0..1, ‖w s‖) * Real.exp t) by ring]
  gcongr
  refine (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans ?_
  rw [← intervalIntegral.integral_mul_const]
  refine intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one ?_ (hw.norm.mul_const _)
    fun s hs => ?_
  · exact (hw.mul_continuousOn (by fun_prop)).norm
  · rw [norm_mul]
    have := norm_sinh_mul_le hpos ⟨hs.1, hs.2.le⟩
    rw [one_mul] at this
    exact mul_le_mul_of_nonneg_left this (norm_nonneg _)

/-- Laplace transform of `L₀` in terms of `∫₀¹ du/((a²-1)+u²)`. -/
theorem struveL_zero_laplace_aux {a : ℂ} (ha : 1 < a.re) :
    HasIntegralAtTop (fun t : ℝ => exp (-a*t)*struveL 0 t) 0
      (2/π * ∫ u : ℝ in 0..1, 1/((a^2-1) + (u:ℂ)^2)) := by
  set w : ℝ → ℂ := fun s => (1-(s:ℂ)^2)^(-1/2:ℂ)
  have hk : Continuous (Function.uncurry fun t s : ℝ => sinh ((t:ℂ)*s)) := by
    simp only [Function.uncurry_def]; fun_prop
  obtain ⟨hI, hV⟩ := laplace_poissonWeight (a := a) (β := 1) ha hk
    (fun t s ht hs => norm_sinh_mul_le ht hs)
  have hae : ∀ t ∈ Ioi (0:ℝ), exp (-a*t) * struveL 0 t =
      2/π * (exp (-a*t) * ∫ s : ℝ in 0..1, w s * sinh ((t:ℂ)*s)) := by
    intro t ht; rw [struveL_zero_eq_poisson ht]; ring
  have hI' : IntegrableOn (fun t : ℝ => exp (-a*t)*struveL 0 t) (Ioi 0) :=
    IntegrableOn.congr_fun (Integrable.const_mul hI (2/π:ℂ)) (fun t ht => (hae t ht).symm)
      measurableSet_Ioi
  have hval : (∫ t : ℝ in Ioi 0, exp (-a*t)*struveL 0 t) =
      2/π * ∫ u : ℝ in 0..1, 1/((a^2-1) + (u:ℂ)^2) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hae, integral_const_mul, hV]
    congr 1
    have h1 : (∫ s : ℝ in 0..1, w s * ∫ t : ℝ in Ioi 0, exp (-a*t) * sinh ((t:ℂ)*s)) =
        ∫ s : ℝ in 0..1, w s * ((s:ℂ)/(a^2-(s:ℂ)^2)) := by
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun s hs => ?_)
      rw [uIoc_of_le zero_le_one] at hs
      rw [laplace_sinh_mul ha hs]
    rw [h1]
    have h := integral_poissonWeight_eq_trig 0 (fun s : ℝ => (s:ℂ)/(a^2-(s:ℂ)^2))
    rw [show (0:ℂ)-1/2 = -1/2 by ring] at h
    rw [h]
    simp only [mul_zero, cpow_zero, mul_one]
    set g : ℝ → ℂ := fun u => 1/((a^2-1) + (u:ℂ)^2)
    have hsub := intervalIntegral.integral_deriv_smul_comp' (a := 0) (b := π/2) (f := Real.sin)
      (f' := Real.cos) (g := g) (fun x _ => Real.hasDerivAt_sin x) Real.continuous_cos.continuousOn
      (continuousOn_const.div (by fun_prop) fun u _ => sq_sub_one_add_sq_ne_zero ha u)
    rw [Real.sin_zero, Real.sin_pi_div_two] at hsub
    rw [← hsub]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [g, Function.comp, real_smul]
    have hc : (Real.cos θ : ℂ)^2 = 1 - (Real.sin θ : ℂ)^2 := by
      rw [← ofReal_pow, ← ofReal_pow, Real.cos_sq']; push_cast; ring
    rw [hc]; ring
  have := intervalIntegral_tendsto_integral_Ioi 0 hI' tendsto_id
  rw [hval] at this
  exact this

/-- struve laplace 13. -/
@[dlmf 11.7.E13]
theorem struve_laplace_13 {a : ℂ} (ha : 0 < a.re) :
    HasIntegralAtTop (fun t : ℝ => exp (-a*t)*struveH 0 t) 0 (2/(π*((1+a^2)^(1/2:ℂ)))*log ((1+((1+a^2)^(1/2:ℂ)))/a)) := by
  set w : ℝ → ℂ := fun s => (1-(s:ℂ)^2)^(-1/2:ℂ)
  have hH : ∀ t : ℝ, 0 < t → struveH 0 t = 2/π * ∫ s : ℝ in 0..1, w s * sin ((t:ℂ)*s) := by
    intro t ht
    rw [struveH_eq_poisson (by norm_num) (ofReal_ne_zero.2 ht.ne')]
    rw [cpow_zero, zero_add, Complex.Gamma_one_half_eq, show (0:ℂ)-1/2 = -1/2 by ring]
    have hs : (π:ℂ)^(1/2:ℂ) = (Real.sqrt π : ℂ) := by
      rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]; push_cast; ring_nf
    have hp : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
      rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
    rw [hs, hp]; ring
  have hk : Continuous (Function.uncurry fun t s : ℝ => sin ((t:ℂ)*s)) := by
    simp only [Function.uncurry_def]; fun_prop
  have hkb : ∀ t s : ℝ, 0 < t → s ∈ Ioc (0:ℝ) 1 → ‖sin ((t:ℂ)*s)‖ ≤ Real.exp (0*t) := by
    intro t s _ _
    rw [zero_mul, Real.exp_zero, ← ofReal_mul, ← ofReal_sin, norm_real, Real.norm_eq_abs]
    exact Real.abs_sin_le_one _
  obtain ⟨hI, hV⟩ := laplace_poissonWeight (a := a) (β := 0) ha hk hkb
  have hae : ∀ t ∈ Ioi (0:ℝ), exp (-a*t) * struveH 0 t =
      2/π * (exp (-a*t) * ∫ s : ℝ in 0..1, w s * sin ((t:ℂ)*s)) := by
    intro t ht; rw [hH t ht]; ring
  have hI' : IntegrableOn (fun t : ℝ => exp (-a*t)*struveH 0 t) (Ioi 0) :=
    IntegrableOn.congr_fun (Integrable.const_mul hI (2/π:ℂ)) (fun t ht => (hae t ht).symm)
      measurableSet_Ioi
  have hval : (∫ t : ℝ in Ioi 0, exp (-a*t)*struveH 0 t) =
      2/(π*((1+a^2)^(1/2:ℂ)))*log ((1+((1+a^2)^(1/2:ℂ)))/a) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hae, integral_const_mul, hV]
    have : (∫ s : ℝ in 0..1, w s * ∫ t : ℝ in Ioi 0, exp (-a*t) * sin ((t:ℂ)*s)) =
        ∫ s : ℝ in 0..1, w s * ((s:ℂ)/(a^2+(s:ℂ)^2)) :=
      intervalIntegral.integral_congr fun s _ => by rw [laplace_sin_mul ha]
    rw [this, integral_poissonWeight_mul_div_sq_add ha]
    ring
  have := intervalIntegral_tendsto_integral_Ioi 0 hI' tendsto_id
  rw [hval] at this
  exact this

/-- struve laplace 14. -/
@[dlmf 11.7.E14]
theorem struve_laplace_14 {a : ℂ} (ha : 0 < a.re) :
    HasIntegralAtTop (fun t : ℝ => exp (-a*t)*struveH 1 t) 0 (2/(π*a)-2*a/(π*((1+a^2)^(1/2:ℂ)))*log ((1+((1+a^2)^(1/2:ℂ)))/a)) := by
  set L : ℂ := 2/(π*((1+a^2)^(1/2:ℂ)))*log ((1+((1+a^2)^(1/2:ℂ)))/a)
  have h13 : Tendsto (fun R : ℝ => ∫ t in (0:ℝ)..R, exp (-a*t)*struveH 0 t) atTop (𝓝 L) :=
    struve_laplace_13 ha
  have hre : (-a).re < 0 := by simp; linarith
  have hexp : Tendsto (fun R : ℝ => ∫ t in (0:ℝ)..R, exp (-a*t)) atTop (𝓝 (1/a)) := by
    have := intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_exp_mul_complex_Ioi hre 0)
      tendsto_id
    rw [integral_exp_mul_complex_Ioi hre 0] at this
    have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
    convert this using 2
    · rfl
    · rw [ofReal_zero, mul_zero, Complex.exp_zero]
      field_simp
  obtain ⟨C, hC⟩ := exists_bound_struveH_zero
  have hbd : Tendsto (fun R : ℝ => exp (-a*R) * struveH 0 R) atTop (𝓝 0) := by
    have hE : Tendsto (fun R : ℝ => ‖exp (-a*R)‖) atTop (𝓝 0) := by
      have : (fun R : ℝ => ‖exp (-a*R)‖) = fun R => Real.exp ((-a).re * R) := by
        funext R; rw [Complex.norm_exp]; simp
      rw [this]
      exact Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hre)
    have hEC : Tendsto (fun R : ℝ => ‖exp (-a*R)‖ * C) atTop (𝓝 0) := by
      have := hE.mul_const C; rwa [zero_mul] at this
    refine squeeze_zero_norm' ?_ hEC
    filter_upwards [eventually_ge_atTop 0] with R hR
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC R hR) (norm_nonneg _)
  have hH0 : Differentiable ℂ (struveH 0) := by simpa using struveH_nat_entire 0
  have hH1 : Differentiable ℂ (struveH 1) := by simpa using struveH_nat_entire 1
  have hc0 : Continuous fun t : ℝ => struveH 0 t := hH0.continuous.comp continuous_ofReal
  have hc1 : Continuous fun t : ℝ => struveH 1 t := hH1.continuous.comp continuous_ofReal
  have hval : ∀ R : ℝ, (∫ t in (0:ℝ)..R, exp (-a*t)*struveH 1 t) =
      2/π * (∫ t in (0:ℝ)..R, exp (-a*t)) - (exp (-a*R) * struveH 0 R +
        a * ∫ t in (0:ℝ)..R, exp (-a*t)*struveH 0 t) := by
    intro R
    have hu : ∀ x ∈ uIcc (0:ℝ) R, HasDerivAt (fun t : ℝ => exp (-a*t)) (-a * exp (-a*x)) x := by
      intro x _
      have := ((hasDerivAt_id (x:ℝ)).ofReal_comp.const_mul (-a)).cexp
      exact this.congr_deriv (by simp only [id, ofReal_one, mul_one]; ring)
    have hv : ∀ x ∈ uIcc (0:ℝ) R, HasDerivAt (fun t : ℝ => struveH 0 t)
        (2/π - struveH 1 x) x := fun x _ => (struveH_zero_deriv x).comp_ofReal
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
      ((by fun_prop : Continuous fun x : ℝ => -a * exp (-a*x)).intervalIntegrable _ _)
      ((continuous_const.sub hc1).intervalIntegrable _ _)
    have hsplit : (∫ t in (0:ℝ)..R, exp (-a*t)*struveH 1 t) =
        (∫ t in (0:ℝ)..R, 2/π * exp (-a*t)) -
          ∫ t in (0:ℝ)..R, exp (-a*t) * (2/π - struveH 1 t) := by
      rw [← intervalIntegral.integral_sub]
      · congr 1; funext t; ring
      · exact (by fun_prop : Continuous fun t : ℝ => 2/π * exp (-a*t)).intervalIntegrable _ _
      · exact ((by fun_prop : Continuous fun t : ℝ => exp (-a*t)).mul
          (continuous_const.sub hc1)).intervalIntegrable _ _
    rw [hsplit, hibp, intervalIntegral.integral_const_mul]
    have hz : struveH 0 ((0:ℝ):ℂ) = 0 := by
      simp only [ofReal_zero, struveH, zero_div, zero_add, cpow_one, zero_mul]
    have hneg : (∫ x in (0:ℝ)..R, -a * exp (-a*x) * struveH 0 x) =
        -a * ∫ t in (0:ℝ)..R, exp (-a*t)*struveH 0 t := by
      rw [← intervalIntegral.integral_const_mul]; congr 1; funext t; ring
    rw [hneg, hz]
    ring
  have : (fun R : ℝ => ∫ t in (0:ℝ)..R, exp (-a*t)*struveH 1 t) = fun R =>
      2/π * (∫ t in (0:ℝ)..R, exp (-a*t)) - (exp (-a*R) * struveH 0 R +
        a * ∫ t in (0:ℝ)..R, exp (-a*t)*struveH 0 t) := funext hval
  unfold HasIntegralAtTop
  rw [this]
  have hlim := (hexp.const_mul (2/π:ℂ)).sub (hbd.add (h13.const_mul a))
  convert hlim using 2
  simp only [L, zero_add]
  ring

/-- struve laplace 15. -/
@[dlmf 11.7.E15]
theorem struve_laplace_15 {a : ℂ} (ha : 1 < a.re) :
    HasIntegralAtTop (fun t : ℝ => exp (-a*t)*struveL 0 t) 0 (2/(π*((a^2-1)^(1/2:ℂ)))*(-I*log (I/a+(1-1/a^2)^(1/2:ℂ)))) := by
  have h := struveL_zero_laplace_aux ha
  rw [integral_recip_sq_sub_one_add_sq_log ha] at h
  convert h using 1
  ring

/-- struve laplace 16. -/
@[dlmf 11.7.E16]
theorem struve_laplace_16 {a : ℂ} (ha : 1 < a.re) :
    HasIntegralAtTop (fun t : ℝ => exp (-a*t)*struveL 1 t) 0 (2*a/(π*((a^2-1)^(1/2:ℂ)))*arctan (1/((a^2-1)^(1/2:ℂ)))-2/(π*a)) := by
  set L : ℂ := 2/π * (arctan (1/((a^2-1)^(1/2:ℂ))) / (a^2-1)^(1/2:ℂ))
  have h15 : Tendsto (fun R : ℝ => ∫ t in (0:ℝ)..R, exp (-a*t)*struveL 0 t) atTop (𝓝 L) := by
    have h := struveL_zero_laplace_aux ha
    rwa [integral_recip_sq_sub_one_add_sq_arctan ha] at h
  have ha0' : 0 < a.re := by linarith
  have hre : (-a).re < 0 := by simp; linarith
  have hexp : Tendsto (fun R : ℝ => ∫ t in (0:ℝ)..R, exp (-a*t)) atTop (𝓝 (1/a)) := by
    have := intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_exp_mul_complex_Ioi hre 0)
      tendsto_id
    rw [integral_exp_mul_complex_Ioi hre 0] at this
    have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha; linarith
    convert this using 2
    · rfl
    · rw [ofReal_zero, mul_zero, Complex.exp_zero]
      field_simp
  obtain ⟨C, hC⟩ := exists_bound_struveL_zero
  have hbd : Tendsto (fun R : ℝ => exp (-a*R) * struveL 0 R) atTop (𝓝 0) := by
    have hE : Tendsto (fun R : ℝ => Real.exp ((1 - a.re) * R)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
    have hEC : Tendsto (fun R : ℝ => Real.exp ((1 - a.re) * R) * C) atTop (𝓝 0) := by
      have := hE.mul_const C; rwa [zero_mul] at this
    refine squeeze_zero_norm' ?_ hEC
    filter_upwards [eventually_ge_atTop 0] with R hR
    rw [norm_mul, Complex.norm_exp]
    have : (-a*(R:ℂ)).re = -a.re*R := by simp
    rw [this]
    calc Real.exp (-a.re*R) * ‖struveL 0 R‖ ≤ Real.exp (-a.re*R) * (C * Real.exp R) :=
          mul_le_mul_of_nonneg_left (hC R hR) (Real.exp_pos _).le
      _ = Real.exp ((1 - a.re) * R) * C := by
          rw [show (1 - a.re) * R = -a.re*R + R by ring, Real.exp_add]; ring
  have hL0 : Differentiable ℂ (struveL 0) := by simpa using struveL_nat_entire 0
  have hL1 : Differentiable ℂ (struveL 1) := by simpa using struveL_nat_entire 1
  have hc1 : Continuous fun t : ℝ => struveL 1 t := hL1.continuous.comp continuous_ofReal
  have hval : ∀ R : ℝ, (∫ t in (0:ℝ)..R, exp (-a*t)*struveL 1 t) =
      (exp (-a*R) * struveL 0 R + a * ∫ t in (0:ℝ)..R, exp (-a*t)*struveL 0 t) -
        2/π * (∫ t in (0:ℝ)..R, exp (-a*t)) := by
    intro R
    have hu : ∀ x ∈ uIcc (0:ℝ) R, HasDerivAt (fun t : ℝ => exp (-a*t)) (-a * exp (-a*x)) x := by
      intro x _
      have := ((hasDerivAt_id (x:ℝ)).ofReal_comp.const_mul (-a)).cexp
      exact this.congr_deriv (by simp only [id, ofReal_one, mul_one]; ring)
    have hv : ∀ x ∈ uIcc (0:ℝ) R, HasDerivAt (fun t : ℝ => struveL 0 t)
        (2/π + struveL 1 x) x := fun x _ => (struveL_zero_deriv x).comp_ofReal
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
      ((by fun_prop : Continuous fun x : ℝ => -a * exp (-a*x)).intervalIntegrable _ _)
      ((continuous_const.add hc1).intervalIntegrable _ _)
    have hsplit : (∫ t in (0:ℝ)..R, exp (-a*t)*struveL 1 t) =
        (∫ t in (0:ℝ)..R, exp (-a*t) * (2/π + struveL 1 t)) -
          ∫ t in (0:ℝ)..R, 2/π * exp (-a*t) := by
      rw [← intervalIntegral.integral_sub]
      · congr 1; funext t; ring
      · exact ((by fun_prop : Continuous fun t : ℝ => exp (-a*t)).mul
          (continuous_const.add hc1)).intervalIntegrable _ _
      · exact (by fun_prop : Continuous fun t : ℝ => 2/π * exp (-a*t)).intervalIntegrable _ _
    rw [hsplit, hibp, intervalIntegral.integral_const_mul]
    have hz : struveL 0 ((0:ℝ):ℂ) = 0 := by
      simp only [ofReal_zero, struveL, zero_div, zero_add, cpow_one, zero_mul]
    have hneg : (∫ x in (0:ℝ)..R, -a * exp (-a*x) * struveL 0 x) =
        -a * ∫ t in (0:ℝ)..R, exp (-a*t)*struveL 0 t := by
      rw [← intervalIntegral.integral_const_mul]; congr 1; funext t; ring
    rw [hneg, hz]
    ring
  unfold HasIntegralAtTop
  rw [funext hval]
  have hlim := (hbd.add (h15.const_mul a)).sub (hexp.const_mul (2/π:ℂ))
  convert hlim using 2
  simp only [L, zero_add]
  ring

end DLMF.Struve
