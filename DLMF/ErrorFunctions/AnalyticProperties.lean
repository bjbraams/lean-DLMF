/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ErrorFunctions.Basic

public import DLMF.Confluent.FresnelAsymptotics
public import DLMF.Core.Framework

/-!
# Entire error, Dawson, Fresnel and Goodwin–Staton functions, DLMF §7.2

Canonical definitions are in `DLMF.ErrorFunctions.Basic`; this module develops their properties.

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

/-- The proved Kummer Gaussian antiderivative gives the complex error-function derivative. -/
theorem hasDerivAt_erf_complex (z : ℂ) :
    HasDerivAt erf (2/Real.sqrt π*exp (-z^2)) z := by
  have he : erf = fun w : ℂ => (2/(Real.sqrt π:ℂ))*(w*kummerM (1/2) (3/2) (-w^2)) := by
    funext w
    unfold erf
    ring
  rw [he]
  exact (hasDerivAt_gaussianPrimitive z).const_mul _

/-- The complex error function is entire, directly from its Kummer derivative. -/
@[fun_prop] theorem differentiable_erf_complex : Differentiable ℂ erf :=
  fun z => (hasDerivAt_erf_complex z).differentiableAt

/-- Fresnel primitives differentiate to their entire cosine integrand. -/
theorem hasDerivAt_fresnelCosInt_complex (z : ℂ) :
    HasDerivAt fresnelCosInt (cos (π*z^2/2)) z :=
  hasDerivAt_primitive (by fun_prop) z

/-- Fresnel primitives differentiate to their entire sine integrand. -/
theorem hasDerivAt_fresnelSinInt_complex (z : ℂ) :
    HasDerivAt fresnelSinInt (sin (π*z^2/2)) z :=
  hasDerivAt_primitive (by fun_prop) z

/-- Factorial convergence supplies the uniform bounds used in the Fresnel primitives. -/
theorem summable_fresnel_coeff (ε : ℕ) (R : ℝ) :
    Summable (fun n : ℕ => ‖(-1:ℂ)^n*(π/2:ℂ)^(2*n+ε)/(2*n+ε).factorial‖*
      R^(2*(2*n+ε))) := by
  have hd : Function.Injective (fun n : ℕ=>2*n+ε) := by intro n m h; dsimp only at h; omega
  have h := (Real.summable_pow_div_factorial (π/2*R^2)).comp_injective hd
  have hp : ‖(π/2:ℂ)‖=π/2 := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    norm_num
  convert h using 1
  funext n
  simp only [Function.comp_apply,norm_div,norm_mul,norm_pow,norm_neg,norm_one,one_pow,
    one_mul,hp,Complex.norm_natCast,mul_pow]
  rw [pow_mul R 2 (2*n+ε)]
  ring

/-- The series with terms `(fun n : ℕ => (-1 :
ℂ)^n*(π/2)^(2*n+0)*z^(4*n+1)/((2*n+0).factorial*(4*n+1 : ℂ)))` converges to `(fresnelCosInt
z)`. -/
@[dlmf 7.6.E4]
theorem fresnelCosInt_hasSum (z : ℂ) :
    HasSum (fun n : ℕ => (-1 : ℂ)^n*(π/2)^(2*n+0)*z^(4*n+1)/((2*n+0).factorial*(4*n+1 : ℂ))) (fresnelCosInt z) := by
  have hs (w : ℂ) : HasSum (fun n : ℕ =>
      ((-1:ℂ)^n*(π/2:ℂ)^(2*n+0)/(2*n+0).factorial)*w^(2*(2*n+0)))
      (cos (π*w^2/2)) := by
    convert Complex.hasSum_cos (π*w^2/2) using 1
    funext n
    simp only [Nat.add_zero,div_pow,mul_pow,← pow_mul]
    ring
  have h := hasSum_primitive_monomials
    (fun n : ℕ=>(-1:ℂ)^n*(π/2:ℂ)^(2*n+0)/(2*n+0).factorial)
    (fun n=>2*(2*n+0)) hs z
  change HasSum _ (fresnelCosInt z) at h
  refine h.congr_fun fun n=>?_
  rw [show 2*(2*n+0)+1=4*n+1 by omega]
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- The series with terms `(fun n : ℕ => (-1 :
ℂ)^n*(π/2)^(2*n+1)*z^(4*n+3)/((2*n+1).factorial*(4*n+3 : ℂ)))` converges to `(fresnelSinInt
z)`. -/
@[dlmf 7.6.E6]
theorem fresnelSinInt_hasSum (z : ℂ) :
    HasSum (fun n : ℕ => (-1 : ℂ)^n*(π/2)^(2*n+1)*z^(4*n+3)/((2*n+1).factorial*(4*n+3 : ℂ))) (fresnelSinInt z) := by
  have hs (w : ℂ) : HasSum (fun n : ℕ =>
      ((-1:ℂ)^n*(π/2:ℂ)^(2*n+1)/(2*n+1).factorial)*w^(2*(2*n+1)))
      (sin (π*w^2/2)) := by
    convert Complex.hasSum_sin (π*w^2/2) using 1
    funext n
    simp only [Nat.add_zero,div_pow,mul_pow,← pow_mul]
    ring
  have h := hasSum_primitive_monomials
    (fun n : ℕ=>(-1:ℂ)^n*(π/2:ℂ)^(2*n+1)/(2*n+1).factorial)
    (fun n=>2*(2*n+1)) hs z
  change HasSum _ (fresnelSinInt z) at h
  refine h.congr_fun fun n=>?_
  rw [show 2*(2*n+1)+1=4*n+3 by omega]
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- Dawson differentiation uses only the entire Gaussian primitive. -/
theorem hasDerivAt_dawsonF_complex (z : ℂ) :
    HasDerivAt dawsonF (1-2*z*dawsonF z) z := by
  have hd := (((hasDerivAt_id z).pow 2).neg.cexp).mul
    (hasDerivAt_primitive (by fun_prop : Differentiable ℂ (fun t : ℂ => exp (t^2))) z)
  have he : exp (-z^2)*exp (z^2)=1 := by rw [← Complex.exp_add]; simp
  refine hd.congr_deriv ?_
  dsimp [dawsonF]
  linear_combination he

/-- Entire differentiability asserted in DLMF §7.2. -/
theorem faddeevaW_entire  :
    Differentiable ℂ faddeevaW := by
  unfold faddeevaW erfc
  fun_prop

/-- Entire differentiability asserted in DLMF §7.2. -/
theorem dawsonF_entire  :
    Differentiable ℂ dawsonF := by
  exact fun z => (hasDerivAt_dawsonF_complex z).differentiableAt

/-- Entire differentiability asserted in DLMF §7.2. -/
theorem fresnelCosInt_entire  :
    Differentiable ℂ fresnelCosInt := by
  exact differentiable_primitive (by fun_prop)

/-- Entire differentiability asserted in DLMF §7.2. -/
theorem fresnelSinInt_entire  :
    Differentiable ℂ fresnelSinInt := by
  exact differentiable_primitive (by fun_prop)

/-- Entire differentiability asserted in DLMF §7.2. -/
theorem fresnelTail_entire  :
    Differentiable ℂ fresnelTail := by
  unfold fresnelTail
  exact ((differentiable_const _).sub fresnelCosInt_entire).sub (fresnelSinInt_entire.const_mul I)

/-- Entire differentiability asserted in DLMF §7.2. -/
theorem fresnelAuxFComplex_entire  :
    Differentiable ℂ fresnelAuxFComplex := by
  unfold fresnelAuxFComplex
  exact (((differentiable_const (1/2:ℂ)).sub fresnelSinInt_entire).mul (by fun_prop)).sub
    (((differentiable_const (1/2:ℂ)).sub fresnelCosInt_entire).mul (by fun_prop))

/-- Entire differentiability asserted in DLMF §7.2. -/
theorem fresnelAuxGComplex_entire  :
    Differentiable ℂ fresnelAuxGComplex := by
  unfold fresnelAuxGComplex
  exact (((differentiable_const (1/2:ℂ)).sub fresnelCosInt_entire).mul (by fun_prop)).add
    (((differentiable_const (1/2:ℂ)).sub fresnelSinInt_entire).mul (by fun_prop))

/-- Agreement with the existing real-variable definition. -/
theorem dawsonF_ofReal (x : ℝ) :
    dawsonF x = (Real.dawsonF x : ℂ) := by
  rw [dawsonF, primitive_ofReal, Real.dawsonF, Complex.ofReal_mul,
    ← intervalIntegral.integral_ofReal]
  simp only [Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_pow]

/-- Agreement with the existing real-variable definition. -/
theorem fresnelCosInt_ofReal (x : ℝ) :
    fresnelCosInt x = (Real.fresnelCosInt x : ℂ) := by
  rw [fresnelCosInt, primitive_ofReal, Real.fresnelCosInt, ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro t ht
  push_cast
  rfl

/-- Agreement with the existing real-variable definition. -/
theorem fresnelSinInt_ofReal (x : ℝ) :
    fresnelSinInt x = (Real.fresnelSinInt x : ℂ) := by
  rw [fresnelSinInt, primitive_ofReal, Real.fresnelSinInt, ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro t ht
  push_cast
  rfl

/-- Agreement with the existing real-variable definition. -/
theorem fresnelAuxFComplex_ofReal (x : ℝ) :
    fresnelAuxFComplex x = (fresnelAuxF x : ℂ) := by
  simp only [fresnelAuxFComplex, fresnelAuxF, fresnelCosInt_ofReal, fresnelSinInt_ofReal]
  push_cast
  rfl

/-- Agreement with the existing real-variable definition. -/
theorem fresnelAuxGComplex_ofReal (x : ℝ) :
    fresnelAuxGComplex x = (fresnelAuxG x : ℂ) := by
  simp only [fresnelAuxGComplex, fresnelAuxG, fresnelCosInt_ofReal, fresnelSinInt_ofReal]
  push_cast
  rfl

/-- The entire Dawson integral is the same Kummer specialization on the full complex plane. -/
theorem dawsonF_eq_kummerM (z : ℂ) : dawsonF z=z*kummerM 1 (3/2) (-z^2) := by
  have hM : Differentiable ℂ (kummerM 1 (3/2)) := fun w =>
    ((hasFPowerSeriesOnBall_kummerM (a:=1) three_half_ne_neg_nat).analyticAt_of_mem (by simp)).differentiableAt
  have he := Complex.eq_of_differentiable_of_eqOn_pos_reals dawsonF_entire
    (show Differentiable ℂ (fun w => w*kummerM 1 (3/2) (-w^2)) by fun_prop)
    (fun x hx => by rw [dawsonF_ofReal, Real.dawsonF_eq_kummerM])
  exact congrFun he z

/-- Identity under the stated parameter and domain assumptions: `erf z = 2/Real.sqrt π*primitive
(fun t => exp (-t^2)) z`. -/
@[dlmf 7.2.E1]
theorem erf_complex_segment_integral (z : ℂ) :
    erf z = 2/Real.sqrt π*primitive (fun t => exp (-t^2)) z := by
  have h := primitive_eq_sub hasDerivAt_gaussianPrimitive z
  simp only [zero_mul, sub_zero] at h
  rw [h, erf]
  ring

/-- Where `Re z² ≥ 0`, the segment integral gives `‖erf z‖ ≤ 2‖z‖/√π`. -/
theorem norm_erf_le {z : ℂ} (hz : 0 ≤ (z^2).re) : ‖erf z‖ ≤ 2/Real.sqrt π*‖z‖ := by
  rw [erf_complex_segment_integral, primitive, segmentIntegral, norm_mul, norm_mul, sub_zero]
  have hb : ‖∫ t : ℝ in (0:ℝ)..1, exp (-(0+(t:ℂ)*z)^2)‖ ≤ 1 := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := 1)
      (f := fun t : ℝ => exp (-(0+(t:ℂ)*z)^2)) (fun t _ => by
        rw [Complex.norm_exp, Real.exp_le_one_iff, zero_add, mul_pow, neg_re, ← ofReal_pow,
          re_ofReal_mul]
        nlinarith [sq_nonneg t])
    simpa using this
  have h2 : ‖(2:ℂ)/Real.sqrt π‖ = 2/Real.sqrt π := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]; simp
  rw [h2]
  have : 0 ≤ 2/Real.sqrt π := by positivity
  calc 2/Real.sqrt π*(‖z‖*‖∫ t : ℝ in (0:ℝ)..1, exp (-(0+(t:ℂ)*z)^2)‖)
      ≤ 2/Real.sqrt π*(‖z‖*1) := by gcongr
    _ = _ := by ring

/-- The complex error function tends to `1` along every horizontal ray to the right. -/
theorem tendsto_erf_add_ofReal_atTop (z : ℂ) :
    Tendsto (fun R : ℝ => erf (z+R)) atTop (𝓝 1) := by
  have hπ : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hd (w : ℂ) : HasDerivAt (fun w => Real.sqrt π/2*erf w) (exp (-w^2)) w := by
    convert (hasDerivAt_erf_complex w).const_mul ((Real.sqrt π:ℂ)/2) using 1
    field_simp
  have hs (R : ℝ) : erf (z+R) = erf R + 2/Real.sqrt π*
      segmentIntegral (fun t => exp (-t^2)) R (z+R) := by
    rw [segmentIntegral_eq_sub hd]
    field_simp
    ring
  simp_rw [hs]
  have hR : Tendsto (fun R : ℝ => erf (R:ℂ)) atTop (𝓝 1) := by
    simp_rw [erf_ofReal]
    exact_mod_cast (Complex.continuous_ofReal.tendsto _).comp TauCeti.Real.tendsto_erf_atTop
  rw [show (1:ℂ) = 1 + 2/Real.sqrt π*0 by ring]
  refine hR.add (Tendsto.const_mul _ ?_)
  -- the segment integral is bounded by an exponentially small quantity
  set a := ‖z‖
  have hbound : ∀ᶠ R : ℝ in atTop, ‖segmentIntegral (fun t => exp (-t^2)) R (z+R)‖ ≤
      a*Real.exp (a^2-(R-a)^2) := by
    filter_upwards [eventually_ge_atTop a] with R hRa
    simp only [segmentIntegral, add_sub_cancel_right, norm_mul]
    gcongr
    have hle : ∀ s ∈ Set.uIoc (0:ℝ) 1, ‖exp (-((R:ℂ)+s*z)^2)‖ ≤ Real.exp (a^2-(R-a)^2) := by
      intro s hs
      rw [Set.uIoc_of_le zero_le_one] at hs
      rw [Complex.norm_exp, Real.exp_le_exp]
      have hre : (-((R:ℂ)+s*z)^2).re = -((R+s*z.re)^2-(s*z.im)^2) := by
        simp [sq]
      rw [hre]
      have hx : |z.re| ≤ a := Complex.abs_re_le_norm z
      have hy : |z.im| ≤ a := Complex.abs_im_le_norm z
      have h1 : R - a ≤ R + s*z.re := by
        have : |s*z.re| ≤ a := by
          rw [abs_mul, abs_of_pos hs.1]; nlinarith [abs_nonneg z.re, hs.2]
        linarith [neg_abs_le (s*z.re)]
      have h2 : (s*z.im)^2 ≤ a^2 := by
        have : |s*z.im| ≤ a := by
          rw [abs_mul, abs_of_pos hs.1]; nlinarith [abs_nonneg z.im, hs.2]
        nlinarith [sq_abs (s*z.im), abs_nonneg (s*z.im)]
      have h3 : (R-a)^2 ≤ (R+s*z.re)^2 := by nlinarith
      linarith
    have := intervalIntegral.norm_integral_le_of_norm_le_const hle
    simpa using this
  refine squeeze_zero_norm' hbound ?_
  have ht : Tendsto (fun R : ℝ => a^2-(R-a)^2) atTop atBot := by
    have : Tendsto (fun R : ℝ => (R-a)^2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).comp (tendsto_atTop_add_const_right _ (-a) tendsto_id)
    exact tendsto_atBot_add_const_left _ _ (tendsto_neg_atTop_atBot.comp this)
  simpa using (Real.tendsto_exp_atBot.comp ht).const_mul a

/-- Horizontal-ray integral representation: `HasIntegralAtTop (fun t : ℝ => exp (-(z+t)^2)) 0
(Real.sqrt π/2*erfc z)`. -/
@[dlmf 7.2.E2]
theorem erfc_horizontal_integral (z : ℂ) :
    HasIntegralAtTop (fun t : ℝ => exp (-(z+t)^2)) 0 (Real.sqrt π/2*erfc z) := by
  have hπ : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => Real.sqrt π/2*erf (z+t)) (exp (-(z+t)^2)) t := by
    have h2 : HasDerivAt (fun t : ℝ => erf (z+t)) (2/Real.sqrt π*exp (-(z+t)^2)) t := by
      have hc := (hasDerivAt_erf_complex (z+(t:ℂ))).comp (t:ℂ) ((hasDerivAt_id (t:ℂ)).const_add z)
      simpa using hc.comp_ofReal
    convert h2.const_mul ((Real.sqrt π:ℂ)/2) using 1
    field_simp
  have hi (R : ℝ) : (∫ t in (0:ℝ)..R, exp (-(z+t)^2)) =
      Real.sqrt π/2*erf (z+R) - Real.sqrt π/2*erf (z+(0:ℝ)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      (by apply Continuous.intervalIntegrable; fun_prop)
  unfold HasIntegralAtTop
  simp_rw [hi]
  have h := ((tendsto_erf_add_ofReal_atTop z).const_mul ((Real.sqrt π:ℂ)/2)).sub_const
    ((Real.sqrt π:ℂ)/2*erf (z+(0:ℝ)))
  convert h using 2
  simp [erfc]; ring

/-- Identity under the stated parameter and domain assumptions: `faddeevaW z = exp
(-z^2)*(1+2*I/Real.sqrt π*primitive (fun t => exp (t^2)) z)`. -/
@[dlmf 7.2.E3]
theorem faddeevaW_integral (z : ℂ) :
    faddeevaW z = exp (-z^2)*(1+2*I/Real.sqrt π*primitive (fun t => exp (t^2)) z) := by
  have he : erf (I*z)=2/Real.sqrt π*I*primitive (fun t => exp (t^2)) z := by
    rw [erf_complex_segment_integral]
    simp only [primitive, segmentIntegral, sub_zero, zero_add]
    have harg (t : ℝ) : -((t:ℂ)*(I*z))^2=((t:ℂ)*z)^2 := by simp [mul_pow, I_sq]
    simp_rw [harg]
    ring
  have hn : erf (-I*z) = -erf (I*z) := by simp [erf]
  rw [faddeevaW, erfc, hn, he]
  ring

/-- Laplace form of `erfc` from Tricomi `U(1/2,1/2,z²)`, for `Re z > 0` and `Re z² > 0`. -/
theorem erfc_eq_laplace {z : ℂ} (hz : 0 < z.re) (hz2 : 0 < (z^2).re) :
    erfc z = exp (-z^2)/π * ∫ t : ℝ in Ioi 0,
      exp (-z^2*t) * (t:ℂ)^(-1/2:ℂ) * (1+(t:ℂ))^(-1:ℂ) := by
  have hu := kummerU_erfc (Or.inl hz) hz
  have hl := kummerU_laplace (a := 1/2) (b := 1/2) (z := z^2) (by norm_num) hz2
  rw [show (1/2:ℂ)-1 = -1/2 by norm_num, show (1/2:ℂ)-1/2-1 = -1 by norm_num,
    Gamma_one_half_eq_sqrt] at hl
  set J := ∫ t : ℝ in Ioi 0, exp (-z^2*t) * (t:ℂ)^(-1/2:ℂ) * (1+(t:ℂ))^(-1:ℂ)
  have hp0 : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hpp : (Real.sqrt π:ℂ)*Real.sqrt π = π := by exact_mod_cast Real.mul_self_sqrt Real.pi_pos.le
  have he : exp (-z^2)*exp (z^2)=1 := by rw [← Complex.exp_add]; simp
  rw [hl] at hu
  have hpi0 : (π:ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have h2 : exp (z^2)*erfc z = J/π := by
    rw [← hpp]; field_simp at hu ⊢; linear_combination -hu
  calc erfc z = exp (-z^2) * (exp (z^2) * erfc z) := by rw [← mul_assoc, he, one_mul]
    _ = _ := by rw [h2]; ring

/-- The bound `‖erfc z‖ ≤ ‖e^{-z²}‖/√(π Re z²)` where `Re z > 0` and `Re z² > 0`. -/
theorem norm_erfc_le {z : ℂ} (hz : 0 < z.re) (hz2 : 0 < (z^2).re) :
    ‖erfc z‖ ≤ ‖exp (-z^2)‖/Real.sqrt (π*(z^2).re) := by
  set x := (z^2).re
  rw [erfc_eq_laplace hz hz2, norm_mul]
  have hg : IntegrableOn (fun t : ℝ => t^((1/2:ℝ)-1) * Real.exp (-(x*t))) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (1/2:ℝ)-1) (b := x)
      (by norm_num) one_pos hz2
    refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp [Real.rpow_one, neg_mul]
  have hb : ‖∫ t : ℝ in Ioi 0, exp (-z^2*t) * (t:ℂ)^(-1/2:ℂ) * (1+(t:ℂ))^(-1:ℂ)‖ ≤
      ∫ t : ℝ in Ioi 0, t^((1/2:ℝ)-1) * Real.exp (-(x*t)) := by
    refine norm_integral_le_of_norm_le hg ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht : (0:ℝ) < t := ht
    rw [norm_mul, norm_mul, Complex.norm_exp, norm_cpow_eq_rpow_re_of_pos ht,
      show 1 + (t:ℂ) = ((1+t:ℝ):ℂ) by push_cast; ring,
      norm_cpow_eq_rpow_re_of_pos (by linarith)]
    have h1 : (-z^2*(t:ℂ)).re = -(x*t) := by simp [x, mul_comm]
    rw [h1]
    have h2 : (1+t:ℝ)^((-1:ℂ).re) ≤ 1 := by
      simp only [neg_re, one_re]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have h3 : ((-1/2:ℂ)).re = (1/2:ℝ)-1 := by norm_num
    rw [h3]
    have h4 : 0 ≤ Real.exp (-(x*t)) * t^((1/2:ℝ)-1) := by positivity
    calc Real.exp (-(x*t)) * t^((1/2:ℝ)-1) * (1+t:ℝ)^((-1:ℂ).re)
        ≤ Real.exp (-(x*t)) * t^((1/2:ℝ)-1) * 1 := mul_le_mul_of_nonneg_left h2 h4
      _ = _ := by ring
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) hz2, Real.Gamma_one_half_eq] at hb
  have hπ : ‖(π:ℂ)‖ = π := by simp [abs_of_pos Real.pi_pos]
  rw [norm_div, hπ]
  have hsx : (1/x)^(1/2:ℝ) = 1/Real.sqrt x := by
    rw [Real.div_rpow zero_le_one hz2.le, Real.one_rpow, Real.sqrt_eq_rpow]
  rw [hsx] at hb
  calc ‖exp (-z^2)‖/π * ‖∫ t : ℝ in Ioi 0, exp (-z^2*t) * (t:ℂ)^(-1/2:ℂ) * (1+(t:ℂ))^(-1:ℂ)‖
      ≤ ‖exp (-z^2)‖/π * (1/Real.sqrt x * Real.sqrt π) := by gcongr
    _ = ‖exp (-z^2)‖/Real.sqrt (π*x) := by
      have hpi := Real.sqrt_pos.mpr Real.pi_pos
      have hxs := Real.sqrt_pos.mpr hz2
      rw [Real.sqrt_mul Real.pi_pos.le]
      have : Real.sqrt π ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
      field_simp
      rw [this]
/-- Comparison with the real complementary error function: `‖erfc z‖ ≤ erfc √(Re z²)`. -/
theorem norm_erfc_le_erfc_sqrt_re {z : ℂ} (hz : 0 < z.re) (hz2 : 0 < (z^2).re) :
    ‖erfc z‖ ≤ TauCeti.Real.erfc (Real.sqrt (z^2).re) := by
  set x := (z^2).re
  set y := Real.sqrt x
  have hy : 0 < y := Real.sqrt_pos.mpr hz2
  have hyx : (y:ℂ)^2 = (x:ℂ) := by rw [← ofReal_pow, Real.sq_sqrt hz2.le]
  have hy2 : 0 < ((y:ℂ)^2).re := by rw [hyx]; simpa using hz2
  have hreal := erfc_eq_laplace (z := (y:ℂ)) (by simpa using hy) hy2
  set k : ℝ → ℝ := fun t => Real.exp (-(x*t)) * t^(-1/2:ℝ) * (1+t)^(-1:ℝ)
  have hk : (∫ t : ℝ in Ioi 0, exp (-(y:ℂ)^2*t) * (t:ℂ)^(-1/2:ℂ) * (1+(t:ℂ))^(-1:ℂ)) =
      ((∫ t : ℝ in Ioi 0, k t : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht : (0:ℝ) < t := ht
    simp only [k, hyx]
    push_cast
    rw [ofReal_cpow ht.le, ofReal_cpow (by linarith)]
    push_cast; ring_nf
  have herfc : erfc (y:ℂ) = (TauCeti.Real.erfc y : ℂ) := by
    rw [erfc, erf_ofReal, TauCeti.Real.erfc_def]; push_cast; ring
  rw [hk, herfc, hyx] at hreal
  have hJ : ‖∫ t : ℝ in Ioi 0, exp (-z^2*t) * (t:ℂ)^(-1/2:ℂ) * (1+(t:ℂ))^(-1:ℂ)‖ ≤
      ∫ t : ℝ in Ioi 0, k t := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht : (0:ℝ) < t := ht
    rw [norm_mul, norm_mul, Complex.norm_exp, norm_cpow_eq_rpow_re_of_pos ht,
      show 1 + (t:ℂ) = ((1+t:ℝ):ℂ) by push_cast; ring,
      norm_cpow_eq_rpow_re_of_pos (by linarith)]
    simp only [k, x]
    congr 2
    · congr 1; simp [mul_comm]
    all_goals norm_num
  have hR : TauCeti.Real.erfc y = Real.exp (-x)/π * ∫ t : ℝ in Ioi 0, k t := by
    have := congrArg re hreal
    rw [ofReal_re] at this
    rw [this, show -(x:ℂ) = ((-x:ℝ):ℂ) by push_cast; ring, ← ofReal_exp]
    rw [show ((Real.exp (-x):ℂ)/(π:ℂ)) = ((Real.exp (-x)/π:ℝ):ℂ) by push_cast; ring,
      ← ofReal_mul, ofReal_re]
  rw [erfc_eq_laplace hz hz2, norm_mul, hR, norm_div, Complex.norm_exp, neg_re]
  have hπ : ‖(π:ℂ)‖ = π := by simp [abs_of_pos Real.pi_pos]
  rw [hπ]
  gcongr

/-- Where `Re z > 0` and `Re z² > 0`, `‖erfc z‖ ≤ 1`. -/
theorem norm_erfc_le_one {z : ℂ} (hz : 0 < z.re) (hz2 : 0 < (z^2).re) : ‖erfc z‖ ≤ 1 := by
  refine (norm_erfc_le_erfc_sqrt_re hz hz2).trans ?_
  rw [TauCeti.Real.erfc_def]
  linarith [TauCeti.Real.erf_nonneg (Real.sqrt_nonneg (z^2).re)]

/-- `erfc (f t) → 0` when both `Re f` and `Re f²` tend to `+∞`. -/
theorem tendsto_erfc_zero_of_re {α : Type*} {l : Filter α} {f : α → ℂ}
    (h1 : Tendsto (fun t => (f t).re) l atTop) (h2 : Tendsto (fun t => ((f t)^2).re) l atTop) :
    Tendsto (fun t => erfc (f t)) l (𝓝 0) := by
  have hev : ∀ᶠ t in l, ‖erfc (f t)‖ ≤ Real.exp (-((f t)^2).re)/Real.sqrt π := by
    filter_upwards [h1.eventually_gt_atTop 0, h2.eventually_ge_atTop 1] with t ht1 ht2
    refine (norm_erfc_le ht1 (by linarith)).trans ?_
    rw [Complex.norm_exp, neg_re]
    gcongr
    nlinarith [Real.pi_pos]
  refine squeeze_zero_norm' hev ?_
  have := (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h2)).div_const (Real.sqrt π)
  simpa using this

/-- In a sector `|arg z| ≤ α ≤ π/2`, the real part of `z²` is at least `‖z‖² cos 2α`. -/
theorem norm_sq_mul_cos_le_re_sq {z : ℂ} {α : ℝ} (hα : α ≤ π/2) (h : |arg z| ≤ α) :
    ‖z‖^2*Real.cos (2*α) ≤ (z^2).re := by
  have hre : (z^2).re = ‖z‖^2*Real.cos (2*arg z) := by
    have h1 := Complex.norm_mul_cos_arg z
    have h2 := Complex.norm_mul_sin_arg z
    have hsc := Real.sin_sq_add_cos_sq (arg z)
    have h3 : (z^2).re = z.re*z.re - z.im*z.im := by simp [sq]
    rw [Real.cos_two_mul, h3, ← h1, ← h2]
    linear_combination (-‖z‖^2)*hsc
  rw [hre]
  have hc : Real.cos (2*α) ≤ Real.cos (2*arg z) := by
    rw [← Real.cos_abs (2*arg z), abs_mul, abs_two]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)
  exact mul_le_mul_of_nonneg_left hc (by positivity)

/-- In an open sector `|arg z| < π/2` the real part is positive. -/
theorem re_pos_of_abs_arg_lt {z : ℂ} (hz : z ≠ 0) (h : |arg z| < π/2) : 0 < z.re := by
  rw [← Complex.norm_mul_cos_arg z]
  exact mul_pos (norm_pos_iff.mpr hz) (Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le (arg z)],
    by linarith [le_abs_self (arg z)]⟩)

/-- Limit formula in the specified filter: `Tendsto erf (sector (π/4-δ)) (𝓝 1) ∧ Tendsto erfc
(sector (π/4-δ)) (𝓝 0)`. -/
@[dlmf 7.2.E4]
theorem erf_sector_limit {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < π/4) :
    Tendsto erf (sector (π/4-δ)) (𝓝 1) ∧ Tendsto erfc (sector (π/4-δ)) (𝓝 0) := by
  have hc : 0 < Real.cos (2*(π/4-δ)) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  set C := Real.cos (2*(π/4-δ))
  have hC : Tendsto erfc (sector (π/4-δ)) (𝓝 0) := by
    have hev : ∀ᶠ z in sector (π/4-δ), ‖erfc z‖ ≤ 1/Real.sqrt (π*C) * ‖z‖⁻¹ := by
      refine Filter.mem_inf_of_right (Filter.mem_principal.mpr fun z hz => ?_)
      obtain ⟨hz0, harg⟩ := hz
      have hr := re_pos_of_abs_arg_lt hz0 (by linarith)
      have hq := norm_sq_mul_cos_le_re_sq (by linarith) harg
      have hn := norm_pos_iff.mpr hz0
      have hq0 : 0 < (z^2).re := lt_of_lt_of_le (by positivity) hq
      refine (norm_erfc_le hr hq0).trans ?_
      have he : ‖exp (-z^2)‖ ≤ 1 := by
        rw [Complex.norm_exp, Real.exp_le_one_iff]; simp only [neg_re]; linarith
      have hs : Real.sqrt (π*C)*‖z‖ ≤ Real.sqrt (π*(z^2).re) := by
        rw [← Real.sqrt_sq hn.le, ← Real.sqrt_mul (by positivity)]
        exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])
      have hpc : 0 < Real.sqrt (π*C) := Real.sqrt_pos.mpr (by positivity)
      calc ‖exp (-z^2)‖/Real.sqrt (π*(z^2).re) ≤ 1/(Real.sqrt (π*C)*‖z‖) := by
            gcongr
        _ = _ := by field_simp
    refine squeeze_zero_norm' hev ?_
    have ht : Tendsto (fun z : ℂ => ‖z‖⁻¹) (sector (π/4-δ)) (𝓝 0) :=
      (tendsto_inv_atTop_zero.comp tendsto_comap).mono_left inf_le_left
    simpa using ht.const_mul (1/Real.sqrt (π*C))
  refine ⟨?_, hC⟩
  have := hC.const_sub 1
  simp only [sub_zero] at this
  refine this.congr fun z => ?_
  simp [erfc]

/-- The map `(fun R : ℝ => segmentIntegral (fun t => exp (π*I*t^2/2)) z R)` tends to `(𝓝
(fresnelTail z))` along `atTop`. -/
@[dlmf 7.2.E6]
theorem fresnelTail_horizontal_integral (z : ℂ) :
    Tendsto (fun R : ℝ => segmentIntegral (fun t => exp (π*I*t^2/2)) z R) atTop (𝓝 (fresnelTail z)) := by
  have hd (w : ℂ) : HasDerivAt (fun w => fresnelCosInt w + I*fresnelSinInt w)
      (exp (π*I*w^2/2)) w := by
    convert (hasDerivAt_fresnelCosInt_complex w).add
      ((hasDerivAt_fresnelSinInt_complex w).const_mul I) using 1
    rw [show π*I*w^2/2 = (π*w^2/2)*I by ring, ← Complex.cos_add_sin_I]
    ring
  have hs (R : ℝ) : segmentIntegral (fun t => exp (π*I*t^2/2)) z R =
      ((Real.fresnelCosInt R : ℂ) + I*Real.fresnelSinInt R) -
        (fresnelCosInt z + I*fresnelSinInt z) := by
    rw [segmentIntegral_eq_sub hd, fresnelCosInt_ofReal, fresnelSinInt_ofReal]
  simp_rw [hs]
  have hC := (Complex.continuous_ofReal.tendsto _).comp Real.tendsto_fresnelCosInt_atTop
  have hS := (Complex.continuous_ofReal.tendsto _).comp Real.tendsto_fresnelSinInt_atTop
  have h := (hC.add (hS.const_mul I)).sub_const (fresnelCosInt z + I*fresnelSinInt z)
  convert h using 2
  · simp
  · simp only [fresnelTail]; push_cast; ring

/-- The kernel `(fun t : ℝ => exp (-(t : ℂ)^2)/(t+z))` is integrable on `(Ioi 0)`. -/
@[dlmf 7.2.E12]
theorem goodwinStatonG_integrable {z : ℂ} (hz : z ∈ slitPlane) :
    IntegrableOn (fun t : ℝ => exp (-(t : ℂ)^2)/(t+z)) (Ioi 0) := by
  obtain ⟨m, hm, hb⟩ : ∃ m : ℝ, 0 < m ∧ ∀ t : ℝ, 0 ≤ t → m ≤ ‖(t:ℂ)+z‖ := by
    rcases mem_slitPlane_iff.mp hz with h | h
    · refine ⟨z.re, h, fun t ht => ?_⟩
      have := Complex.re_le_norm ((t:ℂ)+z)
      simp only [add_re, ofReal_re] at this
      linarith
    · refine ⟨|z.im|, abs_pos.mpr h, fun t _ => ?_⟩
      have := Complex.abs_im_le_norm ((t:ℂ)+z)
      simpa using this
  have hg : Integrable (fun t : ℝ => Real.exp (-1*t^2)/m) := (integrable_exp_neg_mul_sq one_pos).div_const m
  refine Integrable.mono' hg.integrableOn ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => ?_
    intro h0
    have := hb t (le_of_lt ht)
    rw [h0, norm_zero] at this
    linarith
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
    rw [norm_div, Complex.norm_exp]
    have h1 : (-(t:ℂ)^2).re = -1*t^2 := by simp [← ofReal_pow]
    rw [h1]
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le hm (hb t (le_of_lt ht))

end DLMF.Confluent
