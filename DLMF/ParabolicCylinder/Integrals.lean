/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ParabolicCylinder.Relations
public import DLMF.ParabolicCylinder.IntegralTools
public import DLMF.ParabolicCylinder.ContourTools
public import DLMF.ParabolicCylinder.ProductTools
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import DLMFMathlib.Analysis.ODE.SymmetricSquare

/-!
# Cylinder real and contour integrals

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
The integral statements in this module are proved. See
`DLMF111214Acquisition.md` for coverage and validation.

The kernel of 12.12.4 is absolutely integrable and its integral is entire in the
argument. Integration by parts yields the shared symmetric-square Weber ODE;
three initial values identify the integral with the normalized squared product.
The ODE uniqueness machinery is shared with the Airy product proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

/-- pcfU integral 2. -/
@[dlmf 12.5.E2]
theorem pcfU_integral_2 {a z : ℂ} (ha : -1/2 < a.re) (hz : 0 < z.re) :
    HasIntegralAtTop (fun t : ℝ => z*exp (-z^2/4)/Gamma (a/2+1/4)*((t:ℂ)^(a/2-3/4)*exp (-t)*(z^2+2*t)^(-a/2-3/4))) 0 (pcfU a z) := by
  have hα : 0 < (a/2+1/4).re := by simp; linarith
  have hv : pcfU a z = z * exp (-z^2/4) / Gamma (a/2+1/4) * pcfInt_F (a/2+1/4) (-a/2-3/4) (z^2) := by
    refine pcfInt_eq_of_real (f := pcfU a)
      (g := fun z => z * exp (-z^2/4) / Gamma (a/2+1/4) * pcfInt_F (a/2+1/4) (-a/2-3/4) (z^2))
      (pcfU_entire a).differentiableOn ?_ (fun x hx => pcfInt_U_real_2 ha hx) hz
    exact ((differentiableOn_id.mul (differentiableOn_id.pow 2 |>.neg.div_const 4 |>.cexp)).div_const _).mul
      (pcfInt_differentiableOn_comp hα _)
  have hI := pcfInt_integrableOn hα (-a/2-3/4) (pcfInt_sq_mem_slitPlane hz)
  rw [show a/2+1/4-1 = a/2-3/4 by ring] at hI
  have T := intervalIntegral_tendsto_integral_Ioi 0 (hI.const_mul (z*exp (-z^2/4)/Gamma (a/2+1/4))) tendsto_id
  rw [integral_const_mul] at T
  unfold HasIntegralAtTop
  rw [hv]
  unfold pcfInt_F
  rw [show a/2+1/4-1 = a/2-3/4 by ring]
  exact T

/-- pcfU integral 3. -/
@[dlmf 12.5.E3]
theorem pcfU_integral_3 {a z : ℂ} (ha : -3/2 < a.re) (hz : 0 < z.re) :
    HasIntegralAtTop (fun t : ℝ => exp (-z^2/4)/Gamma (a/2+3/4)*((t:ℂ)^(a/2-1/4)*exp (-t)*(z^2+2*t)^(-a/2-1/4))) 0 (pcfU a z) := by
  have hα : 0 < (a/2+3/4).re := by simp; linarith
  have hv : pcfU a z = exp (-z^2/4) / Gamma (a/2+3/4) * pcfInt_F (a/2+3/4) (-a/2-1/4) (z^2) := by
    refine pcfInt_eq_of_real (f := pcfU a)
      (g := fun z => exp (-z^2/4) / Gamma (a/2+3/4) * pcfInt_F (a/2+3/4) (-a/2-1/4) (z^2))
      (pcfU_entire a).differentiableOn ?_ (fun x hx => pcfInt_U_real_3 ha hx) hz
    exact ((differentiableOn_id.pow 2 |>.neg.div_const 4 |>.cexp).div_const _).mul
      (pcfInt_differentiableOn_comp hα _)
  have hI := pcfInt_integrableOn hα (-a/2-1/4) (pcfInt_sq_mem_slitPlane hz)
  rw [show a/2+3/4-1 = a/2-1/4 by ring] at hI
  have T := intervalIntegral_tendsto_integral_Ioi 0 (hI.const_mul (exp (-z^2/4)/Gamma (a/2+3/4))) tendsto_id
  rw [integral_const_mul] at T
  unfold HasIntegralAtTop
  rw [hv]
  unfold pcfInt_F
  rw [show a/2+3/4-1 = a/2-1/4 by ring]
  exact T

/-- pcfU integral 4. -/
@[dlmf 12.5.E4]
theorem pcfU_integral_4 {a : ℂ} (ha : a.re < 1/2) (z : ℂ) :
    HasIntegralAtTop (fun t : ℝ => (Real.sqrt (2/π):ℂ)*exp (z^2/4)*((t:ℂ)^(-a-1/2)*exp (-t^2/2)*cos (z*t+(a/2+1/4)*π))) 0 (pcfU a z) := by
  have hc : -1 < (-a-1/2).re := by simp; linarith
  have ha' : -1/2 < (-a).re := by simp; linarith
  have han : ∀ n : ℕ, a ≠ n+1/2 := fun n h => by
    have := congrArg Complex.re h; simp at this; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
  have hΓ : Gamma (1/2 - a) ≠ 0 := Complex.Gamma_ne_zero fun n h => han n (by linear_combination -h)
  set θ : ℂ := (a/2+1/4)*π with hθ
  set K : ℂ := (Real.sqrt (2/π):ℂ)*exp (z^2/4)/2 with hK
  set gp := fun t : ℝ => (t : ℂ) ^ (-a-1/2) * exp (-(t : ℂ) ^ 2 / 2 - (-I*z) * t)
  set gm := fun t : ℝ => (t : ℂ) ^ (-a-1/2) * exp (-(t : ℂ) ^ 2 / 2 - (I*z) * t)
  have ip : IntegrableOn gp (Ioi 0) := integrableOn_pcfIntegrand hc (-I*z)
  have im : IntegrableOn gm (Ioi 0) := integrableOn_pcfIntegrand hc (I*z)
  have hf : (fun t : ℝ => (Real.sqrt (2/π):ℂ)*exp (z^2/4)*((t:ℂ)^(-a-1/2)*exp (-t^2/2)*cos (z*t+(a/2+1/4)*π))) =
      fun t => K * (exp (I*θ) * gp t + exp (-I*θ) * gm t) := by
    funext t
    simp only [K, gp, gm, θ, Complex.cos]
    have e1 : exp (I*((a/2+1/4)*π)) * exp (-(t:ℂ)^2/2 - -I*z*t) = exp (-(t:ℂ)^2/2) * exp ((z*t+(a/2+1/4)*π)*I) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
    have e2 : exp (-I*((a/2+1/4)*π)) * exp (-(t:ℂ)^2/2 - I*z*t) = exp (-(t:ℂ)^2/2) * exp (-(z*t+(a/2+1/4)*π)*I) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
    linear_combination (-(Real.sqrt (2/π):ℂ)*exp (z^2/4)/2 * (t:ℂ)^(-a-1/2)) * (e1 + e2)
  have hp := pcfU_eq_integral ha' (-I*z)
  have hm := pcfU_eq_integral ha' (I*z)
  rw [show (1/2:ℂ) + -a = 1/2 - a by ring, show (-a) - 1/2 = -a-1/2 by ring] at hp hm
  have hsq : (-I*z)^2 = -z^2 := by rw [mul_pow, neg_pow, I_sq]; ring
  have hsq' : (I*z)^2 = -z^2 := by rw [mul_pow, I_sq]; ring
  rw [hsq] at hp; rw [hsq'] at hm
  have hconn := pcfU_rotated_connection_pos han z
  unfold HasIntegralAtTop
  rw [hf]
  have H : IntegrableOn (fun t => K*(exp (I*θ)*gp t + exp (-I*θ)*gm t)) (Ioi 0) :=
    ((ip.const_mul (exp (I*θ))).add (im.const_mul (exp (-I*θ)))).const_mul K
  have T := intervalIntegral_tendsto_integral_Ioi 0 H tendsto_id
  suffices hv : ∫ t in Ioi (0:ℝ), K*(exp (I*θ)*gp t + exp (-I*θ)*gm t) = pcfU a z by
    rw [← hv]; exact T
  rw [integral_const_mul, integral_add (ip.const_mul _) (im.const_mul _), integral_const_mul, integral_const_mul]
  have hs : (Real.sqrt (2/π):ℂ) * Real.sqrt (2*π) = 2 := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by positivity), show 2/π*(2*π) = 2^2 by field_simp,
      Real.sqrt_sq (by norm_num)]; norm_num
  have he : exp (-(-z^2)/4) * exp (-z^2/4) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
  have he2 : exp (z^2/4) * exp (-z^2/4) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
  have hIp : ∫ t in Ioi (0:ℝ), gp t = Gamma (1/2-a) * exp (-z^2/4) * pcfU (-a) (-I*z) := by
    rw [hp, show ∀ X : ℂ, Gamma (1/2-a) * exp (-z^2/4) * (exp (- -z^2/4) / Gamma (1/2-a) * X) =
      (exp (- -z^2/4) * exp (-z^2/4)) * X from fun X => by rw [div_mul_eq_mul_div, mul_div_assoc', div_eq_iff hΓ]; ring, he, one_mul]
  have hIm : ∫ t in Ioi (0:ℝ), gm t = Gamma (1/2-a) * exp (-z^2/4) * pcfU (-a) (I*z) := by
    rw [hm, show ∀ X : ℂ, Gamma (1/2-a) * exp (-z^2/4) * (exp (- -z^2/4) / Gamma (1/2-a) * X) =
      (exp (- -z^2/4) * exp (-z^2/4)) * X from fun X => by rw [div_mul_eq_mul_div, mul_div_assoc', div_eq_iff hΓ]; ring, he, one_mul]
  rw [hIp, hIm, hK]
  have q1 : exp (-I*θ) = exp (-1*I*π*(a/2+1/4)) := by rw [hθ]; congr 1; ring
  have q2 : exp (I*θ) = exp (1*I*π*(a/2+1/4)) := by rw [hθ]; congr 1; ring
  rw [q1, q2, show (1:ℂ)*I*z = I*z by ring, show (-1:ℂ)*I*z = -I*z by ring] at *
  linear_combination (Real.sqrt (2/π):ℂ)/2 * (Gamma (1/2-a) * (exp (1*I*π*(a/2+1/4)) * pcfU (-a) (-I*z) + exp (-1*I*π*(a/2+1/4)) * pcfU (-a) (I*z))) * he2 - (Real.sqrt (2/π):ℂ)/2 * hconn + pcfU a z / 2 * hs

/-- pcfU vertical integral. -/
@[dlmf 12.5.E6]
theorem pcfU_vertical_integral (a z : ℂ) {c : ℝ} (hc : 0 < c) :
    HasIntegralWholeLine (fun y : ℝ => let t : ℂ := c+y*I; exp (z^2/4)/Real.sqrt (2*π)*exp (-z*t+t^2/2)*t^(-a-1/2)) (pcfU a z) := by
  set K : ℂ := exp (z^2/4)/Real.sqrt (2*π)
  have hfun : (fun y : ℝ => let t : ℂ := c+y*I; exp (z^2/4)/Real.sqrt (2*π)*exp (-z*t+t^2/2)*t^(-a-1/2)) =
      fun y : ℝ => K * (exp (-z*((c:ℂ)+y*I) + ((c:ℂ)+y*I)^2/2) * ((c:ℂ)+y*I)^(-a-1/2)) := by
    funext y; simp only [K]; ring
  have h := pcfInt_hasIntegralWholeLine ((pcfCt_vert_integrable z (-a-1/2) hc).const_mul K)
  have hs : (Real.sqrt (2*π) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))
  have he : exp (z^2/4) * exp (-z^2/4) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
  rw [integral_const_mul, pcfCt_vertical a z hc] at h
  rw [hfun]
  convert h using 1
  rw [show K * ((Real.sqrt (2*π) : ℂ) * exp (-z^2/4) * pcfU a z) =
      (exp (z^2/4) * exp (-z^2/4)) * pcfU a z * ((Real.sqrt (2*π) : ℂ) / Real.sqrt (2*π)) by
    simp only [K]; ring, he, div_self hs]
  ring

/-- pcfV horizontal integral. -/
@[dlmf 12.5.E7]
theorem pcfV_horizontal_integral (a z : ℂ) {c : ℝ} (hc : 0 < c) :
    ∃ u v : ℂ, HasIntegralWholeLine (fun x : ℝ => let t : ℂ := x-c*I; exp (-z^2/4)/(2*π)*exp (z*t-t^2/2)*t^(a-1/2)) u ∧ HasIntegralWholeLine (fun x : ℝ => let t : ℂ := x+c*I; exp (-z^2/4)/(2*π)*exp (z*t-t^2/2)*t^(a-1/2)) v ∧ u+v=pcfV a z := by
  set K : ℂ := exp (-z^2/4)/(2*π)
  obtain ⟨hiu, hvu⟩ := pcfCt_horizontal_upper a z hc
  obtain ⟨hil, hvl⟩ := pcfCt_horizontal_lower a z hc
  have fl : (fun x : ℝ => let t : ℂ := x-c*I; exp (-z^2/4)/(2*π)*exp (z*t-t^2/2)*t^(a-1/2)) =
      fun x : ℝ => K * (exp (z*((x:ℂ)-c*I) - ((x:ℂ)-c*I)^2/2) * ((x:ℂ)-c*I)^(a-1/2)) := by
    funext x; simp only [K]; ring
  have fu : (fun x : ℝ => let t : ℂ := x+c*I; exp (-z^2/4)/(2*π)*exp (z*t-t^2/2)*t^(a-1/2)) =
      fun x : ℝ => K * (exp (z*((x:ℂ)+c*I) - ((x:ℂ)+c*I)^2/2) * ((x:ℂ)+c*I)^(a-1/2)) := by
    funext x; simp only [K]; ring
  refine ⟨_, _, fl ▸ pcfInt_hasIntegralWholeLine (hil.const_mul K),
    fu ▸ pcfInt_hasIntegralWholeLine (hiu.const_mul K), ?_⟩
  rw [fl, fu, integral_const_mul, integral_const_mul, hvl, hvu]
  have hV1 := pcfV_eq_mul_I a z
  have hV2 := pcfV_eq_mul_neg_I a z
  have hsum : 2 * pcfV a z = (Real.sqrt (2/π):ℂ) * (exp (-I*π*(a/2-1/4)) * pcfU (-a) (I*z) +
      exp (I*π*(a/2-1/4)) * pcfU (-a) (-I*z)) := by
    linear_combination hV1 + hV2
  have hs : (Real.sqrt (2*π) : ℂ) * (Real.sqrt (2/π) : ℂ) = 2 := by
    rw [← ofReal_mul, ← Real.sqrt_mul (by positivity), show 2*π*(2/π) = 2^2 by field_simp,
      Real.sqrt_sq (by norm_num)]; norm_num
  have he : exp (-z^2/4) * exp (z^2/4) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsq : (Real.sqrt (2*π) : ℂ)^2 = 2*π := by
    rw [← ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; ring
  have hc' : (Real.sqrt (2*π) : ℂ)/(2*π) = (Real.sqrt (2/π) : ℂ)/2 := by
    rw [div_eq_div_iff (by simp) two_ne_zero]
    linear_combination (-(Real.sqrt (2*π) : ℂ)) * hs + (Real.sqrt (2/π) : ℂ) * hsq
  rw [show K * (exp (-I*π*(a/2-1/4)) * ((Real.sqrt (2*π) : ℂ) * exp (z^2/4) * pcfU (-a) (I*z))) +
      K * (exp (I*π*(a/2-1/4)) * ((Real.sqrt (2*π) : ℂ) * exp (z^2/4) * pcfU (-a) (-I*z))) =
      (exp (-z^2/4) * exp (z^2/4)) * ((Real.sqrt (2*π) : ℂ)/(2*π)) *
        (exp (-I*π*(a/2-1/4)) * pcfU (-a) (I*z) + exp (I*π*(a/2-1/4)) * pcfU (-a) (-I*z)) by
    simp only [K]; ring, he, one_mul, hc']
  linear_combination (-1/2:ℂ) * hsum

/-- Hankel loop from negative infinity below the cut around zero to negative infinity above. -/
def pcfNegativeLoop (a z : ℂ) (r R : ℝ) : ℂ :=
  (∫ t : ℝ in r..R, exp (-z*t-t^2/2)*exp ((a-1/2)*(Real.log t-π*I))) + (∫ θ : ℝ in -π..π, let t := r*exp (I*θ); exp (z*t-t^2/2)*exp ((a-1/2)*(Real.log r+I*θ))*I*t) - (∫ t : ℝ in r..R, exp (-z*t-t^2/2)*exp ((a-1/2)*(Real.log t+π*I)))

/-- pcfU hankel integral. -/
@[dlmf 12.5.E5]
theorem pcfU_hankel_integral {a : ℂ} (ha : ∀ n : ℕ, a ≠ n+1/2) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun R => Gamma (1/2-a)/(2*π*I)*exp (-z^2/4)*pcfNegativeLoop a z r R) atTop (𝓝 (pcfU a z)) := by
  have hΓ : Gamma (1/2 - a) ≠ 0 := Complex.Gamma_ne_zero fun n h => ha n (by linear_combination -h)
  have hT := ((intervalIntegral_tendsto_integral_Ioi r (pcfCt_g_integrableOn a z hr)
    tendsto_id).const_mul (pcfCt_kappa a)).add_const (pcfCt_C a z r)
  rw [pcfCt_loop_value a z hr] at hT
  have hev : (fun R => pcfCt_kappa a * (∫ t in r..id R, pcfCt_g a z t) + pcfCt_C a z r) =ᶠ[atTop]
      (fun R => pcfNegativeLoop a z r R) := by
    filter_upwards [eventually_gt_atTop 0] with R hR
    exact (pcfCt_loop_eq a z hr hR).symm
  have hT' := (hT.congr' hev).const_mul (Gamma (1/2-a)/(2*π*I)*exp (-z^2/4))
  have hv : Gamma (1/2-a)/(2*π*I)*exp (-z^2/4) * (2*π*I * exp (z^2/4) * pcfU a z * (Gamma (1/2-a))⁻¹) =
      pcfU a z := by
    have he : exp (-z^2/4) * exp (z^2/4) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
    have hπ : (2*π*I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    rw [show Gamma (1/2-a)/(2*π*I)*exp (-z^2/4) * (2*π*I * exp (z^2/4) * pcfU a z * (Gamma (1/2-a))⁻¹) =
      (Gamma (1/2-a) * (Gamma (1/2-a))⁻¹) * ((2*π*I)/(2*π*I)) * (exp (-z^2/4) * exp (z^2/4)) * pcfU a z by
        ring, mul_inv_cancel₀ hΓ, div_self hπ, he]
    ring
  rw [hv] at hT'
  simpa only [mul_assoc] using hT'

/-- Straight separating Barnes contour; exceptional-parameter deformations need residue corrections. -/
@[dlmf 12.5.E8]
theorem pcfU_barnes_integral {a z : ℂ} (ha : ∀ n : ℕ, 1*a ≠ -n-1/2) (hz0 : z ≠ 0) (hz : |arg z| < 3*π/4) {c : ℝ} (hc : 0 < c) (hca : 2*c < 1/2+1*a.re) :
    HasIntegralWholeLine (fun y : ℝ => let t : ℂ := c+y*I; Gamma t*Gamma (1/2+1*a-2*t)*2^t*z^(2*t)*1) (2*π*Gamma (1/2+1*a)*(exp (z^2/4)*z^(a+1/2))*pcfU a z) := by
  have _ := ha
  have hca' : 2*c < 1/2 + a.re := by simpa using hca
  have hfun : (fun y : ℝ => let t : ℂ := c+y*I; Gamma t*Gamma (1/2+1*a-2*t)*2^t*z^(2*t)*1) =
      pcfInt_B a z c := rfl
  rw [hfun, ← pcfInt_B_integral a hz0 hz hc hca']
  exact pcfInt_hasIntegralWholeLine (pcfInt_B_integrable a hz0 hz hc hca')

/-- `arg (±i z) = arg z ± π/2` for `|arg z| < π/2`. -/
lemma pcfInt_arg_I_mul {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/2) :
    arg (I*z) = arg z + π/2 ∧ arg (-I*z) = arg z - π/2 := by
  obtain ⟨h1, h2⟩ := abs_lt.mp hz
  constructor
  · rw [arg_mul I_ne_zero hz0 (by rw [arg_I]; constructor <;> linarith), arg_I]; ring
  · rw [arg_mul (neg_ne_zero.mpr I_ne_zero) hz0 (by rw [arg_neg_I]; constructor <;> linarith),
      arg_neg_I]; ring

/-- `(±i z)^w = z^w e^{±iπw/2}` for `|arg z| < π/2`. -/
lemma pcfInt_I_mul_cpow {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/2) (w : ℂ) :
    (I*z)^w = z^w * exp (π/2*I*w) ∧ (-I*z)^w = z^w * exp (-(π/2)*I*w) := by
  obtain ⟨ha1, ha2⟩ := pcfInt_arg_I_mul hz0 hz
  have hl1 : log (I*z) = log z + π/2*I := by
    apply Complex.ext
    · simp [log_re]
    · rw [log_im, ha1, add_im, log_im]; simp
  have hl2 : log (-I*z) = log z - π/2*I := by
    apply Complex.ext
    · simp [log_re]
    · rw [log_im, ha2, sub_im, log_im]; simp
  constructor
  · rw [cpow_def_of_ne_zero (mul_ne_zero I_ne_zero hz0), cpow_def_of_ne_zero hz0, hl1,
      ← Complex.exp_add]; congr 1; ring
  · rw [cpow_def_of_ne_zero (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hz0),
      cpow_def_of_ne_zero hz0, hl2, ← Complex.exp_add]; congr 1; ring

/-- Straight separating Barnes contour; exceptional-parameter deformations need residue corrections. -/
@[dlmf 12.5.E9]
theorem pcfV_barnes_integral {a z : ℂ} (ha : ∀ n : ℕ, -1*a ≠ -n-1/2) (hz0 : z ≠ 0) (hz : |arg z| < π/4) {c : ℝ} (hc : 0 < c) (hca : 2*c < 1/2+-1*a.re) :
    HasIntegralWholeLine (fun y : ℝ => let t : ℂ := c+y*I; Gamma t*Gamma (1/2+-1*a-2*t)*2^t*z^(2*t)*cos (π*t)) (2*π*Gamma (1/2+-1*a)*((Real.sqrt (π/2):ℂ)*exp (-z^2/4)*z^(-a+1/2))*pcfV a z) := by
  have _ := ha
  have hca' : 2*c < 1/2 + (-a).re := by simpa using hca
  have hz2 : |arg z| < π/2 := by linarith [Real.pi_pos]
  obtain ⟨ha1, ha2⟩ := pcfInt_arg_I_mul hz0 hz2
  have hp0 : I*z ≠ 0 := mul_ne_zero I_ne_zero hz0
  have hm0 : -I*z ≠ 0 := mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hz0
  have hpa : |arg (I*z)| < 3*π/4 := by
    rw [ha1]; obtain ⟨h1, h2⟩ := abs_lt.mp hz; rw [abs_lt]; constructor <;> linarith
  have hma : |arg (-I*z)| < 3*π/4 := by
    rw [ha2]; obtain ⟨h1, h2⟩ := abs_lt.mp hz; rw [abs_lt]; constructor <;> linarith
  have hfun : (fun y : ℝ => let t : ℂ := c+y*I; Gamma t*Gamma (1/2+-1*a-2*t)*2^t*z^(2*t)*cos (π*t)) =
      fun y => (pcfInt_B (-a) (I*z) c y + pcfInt_B (-a) (-I*z) c y)/2 := by
    funext y
    simp only [pcfInt_B]
    obtain ⟨e1, e2⟩ := pcfInt_I_mul_cpow hz0 hz2 (2*((c:ℂ)+y*I))
    rw [e1, e2, show (1/2:ℂ)+1*(-a) = 1/2+-1*a by ring, Complex.cos]
    have q1 : exp (π/2*I*(2*((c:ℂ)+y*I))) = exp (π*((c:ℂ)+y*I)*I) := by congr 1; ring
    have q2 : exp (-(π/2)*I*(2*((c:ℂ)+y*I))) = exp (-(π*((c:ℂ)+y*I))*I) := by congr 1; ring
    rw [q1, q2]; ring
  have i1 := pcfInt_B_integrable (-a) hp0 hpa hc hca'
  have i2 := pcfInt_B_integrable (-a) hm0 hma hc hca'
  rw [hfun]
  suffices hI : ∫ y, (pcfInt_B (-a) (I*z) c y + pcfInt_B (-a) (-I*z) c y)/2 =
      2*π*Gamma (1/2+-1*a)*((Real.sqrt (π/2):ℂ)*exp (-z^2/4)*z^(-a+1/2))*pcfV a z by
    rw [← hI]; exact pcfInt_hasIntegralWholeLine ((i1.add i2).div_const 2)
  rw [integral_div, integral_add i1 i2, pcfInt_B_integral (-a) hp0 hpa hc hca',
    pcfInt_B_integral (-a) hm0 hma hc hca']
  have hV1 := pcfV_eq_mul_I a z
  have hV2 := pcfV_eq_mul_neg_I a z
  obtain ⟨f1, f2⟩ := pcfInt_I_mul_cpow hz0 hz2 (-a+1/2)
  rw [f1, f2, show (I*z)^2 = -z^2 by rw [mul_pow, I_sq]; ring,
    show (-I*z)^2 = -z^2 by rw [mul_pow, neg_sq, I_sq]; ring, show (1/2:ℂ)+1*(-a) = 1/2+-1*a by ring]
  have hs : (Real.sqrt (π/2):ℂ) * (Real.sqrt (2/π):ℂ) = 1 := by
    rw [← ofReal_mul, ← Real.sqrt_mul (by positivity), show π/2*(2/π) = 1 by field_simp]; simp
  have hq1 : exp (π/2*I*(-a+1/2)) = exp (-I*π*(a/2-1/4)) := by congr 1; ring
  have hq2 : exp (-(π/2)*I*(-a+1/2)) = exp (I*π*(a/2-1/4)) := by congr 1; ring
  rw [hq1, hq2]
  have hsum : 2 * pcfV a z = (Real.sqrt (2/π):ℂ) * (exp (-I*π*(a/2-1/4)) * pcfU (-a) (I*z) +
      exp (I*π*(a/2-1/4)) * pcfU (-a) (-I*z)) := by
    linear_combination hV1 + hV2
  linear_combination (-(π * Gamma (1/2+-1*a) * exp (-z^2/4) * z^(-a+1/2) * (Real.sqrt (π/2):ℂ))) * hsum -
    (π * Gamma (1/2+-1*a) * exp (-z^2/4) * z^(-a+1/2) * (exp (-I*π*(a/2-1/4)) * pcfU (-a) (I*z) +
      exp (I*π*(a/2-1/4)) * pcfU (-a) (-I*z))) * hs

/-- pcf integral 1. -/
@[dlmf 12.12.E1]
theorem pcf_integral_1 {μ : ℂ} (hμ : 0 < μ.re) (a : ℂ) :
    HasIntegralAtTop (fun t : ℝ => exp (-t^2/4)*(t:ℂ)^(μ-1)*pcfU a t) 0 (Real.sqrt π*2^(-(μ+a+1/2)/2)*Gamma μ/Gamma ((μ+a+3/2)/2)) := by
  obtain ⟨hI, hV⟩ := laplace_kummerU_gauss (a := a/2+1/4) (b := μ/2) (c := 1/2) (z := 1)
    (by simp; linarith) (by simp; linarith) (by simp)
  obtain ⟨hI2, hV2⟩ := pcfInt_sq_half_subst hI
  set C : ℂ := (2:ℂ)^(-(1/4)-a/2) * (2:ℂ)^(μ/2-1)
  have heq : EqOn (fun t : ℝ => C * ((t:ℂ) * tricomiLaplaceKernel (a/2+1/4) (μ/2) (1/2) 1 (t^2/2)))
      (fun t : ℝ => exp (-t^2/4)*(t:ℂ)^(μ-1)*pcfU a t) (Ioi 0) :=
    fun t ht => (pcfInt_integrand_1 μ a ht).symm
  have H := IntegrableOn.congr_fun (hI2.const_mul C) heq measurableSet_Ioi
  unfold HasIntegralAtTop
  have T := intervalIntegral_tendsto_integral_Ioi 0 H tendsto_id
  rw [← setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul, hV2, hV, sub_self,
    pcfInt_regularizedGaussHG_zero] at T
  have hd := Complex.Gamma_mul_Gamma_add_half (μ/2)
  rw [show 2*(μ/2) = μ by ring] at hd
  have h2 : C * (2:ℂ)^(1-μ) = (2:ℂ)^(-(μ+a+1/2)/2) := by
    simp only [C]
    rw [← cpow_add _ _ two_ne_zero, ← cpow_add _ _ two_ne_zero]; ring_nf
  have hval : C * (Gamma (μ / 2) * Gamma (μ / 2 + 1 / 2) * (Gamma (a / 2 + 1 / 4 + μ / 2 - 1 / 2 + 1))⁻¹) =
      Real.sqrt π*2^(-(μ+a+1/2)/2)*Gamma μ/Gamma ((μ+a+3/2)/2) := by
    rw [hd, show a/2+1/4 + μ/2 - 1/2 + 1 = (μ+a+3/2)/2 by ring]
    generalize Gamma ((μ+a+3/2)/2) = G
    linear_combination (Real.sqrt π * Gamma μ / G) * h2
  rw [show μ/2 - 1/2 + 1 = μ/2 + 1/2 by ring] at T
  rw [hval] at T
  exact T

/-- pcf integral 2. -/
@[dlmf 12.12.E2]
theorem pcf_integral_2 {a : ℂ} (ha : a.re < -1/2) :
    HasIntegralAtTop (fun t : ℝ => exp (-3*t^2/4)*(t:ℂ)^(-a-3/2)*pcfU a t) 0 (2^(1/4+a/2)*Gamma (-a-1/2)*cos ((a/4+1/8)*π)) := by
  set μ : ℂ := -a-1/2 with hμ
  have hb : 0 < (μ/2).re := by simp [hμ]; linarith
  have hab : a/2+1/4 = -(μ/2) := by rw [hμ]; ring
  have hI := (laplace_kummerU_gauss (a := a/2+1/4) (b := μ/2) (c := 1/2) (z := 2) hb
    (by simp [hμ]; linarith) (by simp)).1
  obtain ⟨hI2, hV2⟩ := pcfInt_sq_half_subst hI
  set C : ℂ := (2:ℂ)^(-(1/4)-a/2) * (2:ℂ)^(μ/2-1)
  have heq : EqOn (fun t : ℝ => C * ((t:ℂ) * tricomiLaplaceKernel (a/2+1/4) (μ/2) (1/2) 2 (t^2/2)))
      (fun t : ℝ => exp (-3*t^2/4)*(t:ℂ)^(-a-3/2)*pcfU a t) (Ioi 0) := fun t ht => by
    rw [show -a-3/2 = μ - 1 by rw [hμ]; ring]
    exact (pcfInt_integrand_2 μ a ht).symm
  have H := IntegrableOn.congr_fun (hI2.const_mul C) heq measurableSet_Ioi
  unfold HasIntegralAtTop
  have T := intervalIntegral_tendsto_integral_Ioi 0 H tendsto_id
  rw [← setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul, hV2, hab,
    pcfInt_laplace_two hb] at T
  have hd := Complex.Gamma_mul_Gamma_add_half (μ/2)
  rw [show 2*(μ/2) = μ by ring] at hd
  have h2 : C * (2:ℂ)^(1-μ) * (2:ℂ)^(-(μ/2)) = (2:ℂ)^(1/4+a/2) := by
    simp only [C]
    rw [← cpow_add _ _ two_ne_zero, ← cpow_add _ _ two_ne_zero, ← cpow_add _ _ two_ne_zero, hμ]
    ring_nf
  have hc : cos (μ/2*π/2) = cos ((a/4+1/8)*π) := by
    rw [← Complex.cos_neg, hμ]; ring_nf
  have hs : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  have hval : C * (Gamma (μ/2) * Gamma (μ/2 + 1/2) * (2:ℂ)^(-(μ/2)) * cos (μ/2*π/2) / Real.sqrt π) =
      2^(1/4+a/2)*Gamma (-a-1/2)*cos ((a/4+1/8)*π) := by
    rw [hd, hc, ← hμ]
    calc C * (Gamma μ * (2:ℂ)^(1-μ) * Real.sqrt π * (2:ℂ)^(-(μ/2)) * cos ((a/4+1/8)*π) / Real.sqrt π)
        = (C * (2:ℂ)^(1-μ) * (2:ℂ)^(-(μ/2))) * Gamma μ * cos ((a/4+1/8)*π) *
            ((Real.sqrt π : ℂ) / Real.sqrt π) := by ring
      _ = _ := by rw [h2, div_self hs]; ring
  rw [hval] at T
  exact T

/-- `‖cos w‖ ≤ e^{|Im w|}`. -/
lemma pcfCt_norm_cos_le (w : ℂ) : ‖cos w‖ ≤ Real.exp |w.im| := by
  rw [Complex.cos]
  have h1 : ‖exp (w*I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr; simp; linarith [neg_abs_le w.im]
  have h2 : ‖exp (-w*I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr; simp; linarith [le_abs_self w.im]
  rw [norm_div, show ‖(2:ℂ)‖ = 2 by simp]
  have := norm_add_le (exp (w*I)) (exp (-w*I))
  linarith

/-- DLMF 12.5.4 as a Lebesgue integral: `e^{-t²/4} U(a,t) = √(2/π) ∫₀^∞ s^{-a-1/2} e^{-s²/2}
cos(ts + (a/2+1/4)π) ds` for `re a < 1/2`, real `t`. -/
lemma pcfCt_U_cos {a : ℂ} (ha : a.re < 1/2) (t : ℝ) :
    IntegrableOn (fun s : ℝ => (s:ℂ)^(-a-1/2) * exp (-(s:ℂ)^2/2) * cos (t*s + (a/2+1/4)*π)) (Ioi 0) ∧
    exp (-(t:ℂ)^2/4) * pcfU a t =
      (Real.sqrt (2/π):ℂ) * ∫ s in Ioi (0:ℝ), (s:ℂ)^(-a-1/2) * exp (-(s:ℂ)^2/2) * cos (t*s + (a/2+1/4)*π) := by
  have hc : -1 < (-a-1/2).re := by simp; linarith
  have hI : IntegrableOn (fun s : ℝ => (s:ℂ)^(-a-1/2) * exp (-(s:ℂ)^2/2) * cos (t*s + (a/2+1/4)*π)) (Ioi 0) := by
    refine Integrable.mono' (((integrableOn_pcfIntegrand hc 0).norm).mul_const
      (Real.exp |((a/2+1/4)*π).im|)) ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun s hs => ?_) measurableSet_Ioi
      refine ContinuousAt.continuousWithinAt ?_
      refine ContinuousAt.mul (ContinuousAt.mul ?_ (by fun_prop)) (by fun_prop)
      exact (continuous_ofReal.continuousAt).cpow continuousAt_const (ofReal_mem_slitPlane.mpr hs)
    · refine Eventually.of_forall fun s => ?_
      have e : (s:ℂ)^(-a-1/2) * exp (-(s:ℂ)^2/2 - 0*s) = (s:ℂ)^(-a-1/2) * exp (-(s:ℂ)^2/2) := by
        simp
      rw [e, norm_mul]
      refine mul_le_mul_of_nonneg_left ((pcfCt_norm_cos_le _).trans (le_of_eq ?_)) (norm_nonneg _)
      congr 2; simp
  refine ⟨hI, ?_⟩
  have h4 := pcfU_integral_4 ha (t:ℂ)
  have hT := intervalIntegral_tendsto_integral_Ioi 0
    (hI.const_mul ((Real.sqrt (2/π):ℂ)*exp ((t:ℂ)^2/4))) tendsto_id
  unfold HasIntegralAtTop at h4
  have hU := tendsto_nhds_unique h4 (hT.congr fun R => by
    refine intervalIntegral.integral_congr fun s _ => ?_
    rfl)
  rw [hU, integral_const_mul]
  have he : exp (-(t:ℂ)^2/4) * exp ((t:ℂ)^2/4) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
  linear_combination ((Real.sqrt (2/π):ℂ) * ∫ s in Ioi (0:ℝ), (s:ℂ)^(-a-1/2) * exp (-(s:ℂ)^2/2) *
    cos (t*s + (a/2+1/4)*π)) * he


/-- DLMF 12.12.3 on the strip `-1/2 < re a < 1/2`, as a Lebesgue integral (Fubini against
12.5.4 and the kernel `pcfCt_kernel`). -/
lemma pcfCt_integral_3_strip {a : ℂ} (ha1 : -1/2 < a.re) (ha2 : a.re < 1/2) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => exp (-t^2/4)*(t:ℂ)^(-a-1/2)/(x^2+t^2:ℂ)*pcfU a t) (Ioi 0) ∧
    ∫ t in Ioi (0:ℝ), exp (-t^2/4)*(t:ℂ)^(-a-1/2)/(x^2+t^2:ℂ)*pcfU a t =
      (Real.sqrt (π/2):ℂ)*Gamma (1/2-a)*(x:ℂ)^(-a-3/2)*exp (x^2/4)*pcfU (-a) x := by
  set μ : ℂ := 1/2 - a with hμ
  have hm0 : 0 < μ.re := by simp [hμ]; linarith
  have hm2 : μ.re < 2 := by simp [hμ]; linarith
  have hμ1 : μ - 1 = -a-1/2 := by rw [hμ]; ring
  set θ : ℂ := (a/2+1/4)*π with hθ
  have hθμ : θ = π/2 - π*μ/2 := by rw [hθ, hμ]; ring
  -- the two factors
  set G1 : ℝ → ℂ := fun t => (t:ℂ)^(-a-1/2) / ((x:ℂ)^2 + (t:ℂ)^2)
  set G2 : ℝ → ℂ := fun s => (s:ℂ)^(-a-1/2) * exp (-(s:ℂ)^2/2)
  have hG1 : IntegrableOn G1 (Ioi 0) := by
    have h := (integrable_comp_exp (pcfCt_gs μ x 0)).mp
      ((funext (pcfCt_Phi_real μ x 0)) ▸ pcfCt_Phi_real_integrable hm0 hm2 hx 0)
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [pcfCt_gs, G1, hμ1]
  have hc : -1 < (-a-1/2).re := by simp; linarith
  have hG2 : IntegrableOn G2 (Ioi 0) := by
    refine (integrableOn_pcfIntegrand hc 0).congr_fun (fun s _ => ?_) measurableSet_Ioi
    simp [G2]
  set F : ℝ × ℝ → ℂ := fun q => G1 q.1 * (G2 q.2 * cos (q.1*q.2 + θ)) with hF
  have hprod : Integrable F ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    refine ((hG1.norm.mul_prod hG2.norm).mul_const (Real.exp |θ.im|)).mono' ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      simp only [hF, G1, G2]
      fun_prop
    · refine Eventually.of_forall fun q => ?_
      simp only [hF, norm_mul]
      have hcos : ‖cos ((q.1:ℂ)*q.2 + θ)‖ ≤ Real.exp |θ.im| :=
        (pcfCt_norm_cos_le _).trans (le_of_eq (by simp))
      calc ‖G1 q.1‖ * (‖G2 q.2‖ * ‖cos ((q.1:ℂ)*q.2 + θ)‖)
          ≤ ‖G1 q.1‖ * (‖G2 q.2‖ * Real.exp |θ.im|) := by gcongr
        _ = _ := by ring
  have hfeq : ∀ t : ℝ, exp (-t^2/4)*(t:ℂ)^(-a-1/2)/(x^2+t^2:ℂ)*pcfU a t =
      (Real.sqrt (2/π):ℂ) * ∫ s in Ioi (0:ℝ), F (t, s) := by
    intro t
    have h := (pcfCt_U_cos ha2 t).2
    rw [show exp (-t^2/4)*(t:ℂ)^(-a-1/2)/(x^2+t^2:ℂ)*pcfU a t =
      G1 t * (exp (-(t:ℂ)^2/4) * pcfU a t) by simp only [G1]; ring, h, ← integral_const_mul,
      ← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [hF, G2, hθ]; ring
  have hint : IntegrableOn (fun t : ℝ => exp (-t^2/4)*(t:ℂ)^(-a-1/2)/(x^2+t^2:ℂ)*pcfU a t) (Ioi 0) := by
    rw [funext hfeq]; exact hprod.integral_prod_left.const_mul _
  refine ⟨hint, ?_⟩
  rw [integral_congr_ae (Eventually.of_forall hfeq), integral_const_mul]
  rw [show (∫ t in Ioi (0:ℝ), ∫ s in Ioi (0:ℝ), F (t, s)) = ∫ s in Ioi (0:ℝ), ∫ t in Ioi (0:ℝ), F (t, s)
    from integral_integral_swap hprod]
  have hin : ∀ s ∈ Ioi (0:ℝ), ∫ t in Ioi (0:ℝ), F (t, s) =
      π/2 * (x:ℂ)^(-a-3/2) * ((s:ℂ)^(-a-1/2) * exp (-(s:ℂ)^2/2 - x*s)) := by
    intro s hs
    have hk := (pcfCt_kernel hm0 hm2 hx (le_of_lt hs)).2
    rw [hμ1, ← hθμ, show μ - 2 = -a-3/2 by rw [hμ]; ring] at hk
    rw [show (fun t : ℝ => F (t, s)) = fun t : ℝ => G2 s * ((t:ℂ)^(-a-1/2) * cos (t*s + θ) /
      ((x:ℂ)^2 + (t:ℂ)^2)) from funext fun t => by simp only [hF, G1]; ring, integral_const_mul, hk]
    simp only [G2]
    rw [show -(s:ℂ)^2/2 - x*s = -(s:ℂ)^2/2 + -(x*s) by ring, Complex.exp_add]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hin, integral_const_mul]
  have hU := pcfU_eq_integral (a := -a) (by simp; linarith) (x:ℂ)
  rw [show (-a) - 1/2 = -a-1/2 by ring, show (1/2:ℂ) + -a = 1/2 - a by ring] at hU
  have hΓ : Gamma (1/2 - a) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have he : exp ((x:ℂ)^2/4) * exp (-(x:ℂ)^2/4) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
  have hs : (Real.sqrt (2/π):ℂ) * (π/2) = Real.sqrt (π/2) := by
    have : Real.sqrt (π/2) = Real.sqrt (2/π) * (π/2) := by
      rw [show π/2 = 2/π * (π/2)^2 by field_simp, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by positivity)]
      field_simp
    rw [this]; push_cast; ring
  rw [hU]
  generalize (∫ s in Ioi (0:ℝ), (s:ℂ)^(-a-1/2) * exp (-(s:ℂ)^2/2 - x*s)) = J
  generalize Gamma (1/2 - a) = G at hΓ ⊢
  rw [← hs]
  have hG' : G * G⁻¹ = 1 := mul_inv_cancel₀ hΓ
  set K : ℂ := (Real.sqrt (2/π):ℂ) * (π/2) * (x:ℂ)^(-a-3/2) * J
  linear_combination (-K) * he + (-K * exp ((x:ℂ)^2/4) * exp (-(x:ℂ)^2/4)) * hG'


/-- Elementary: `t^r ≤ t^{q₁} + t^{q₂}` for `t > 0` and `q₁ ≤ r ≤ q₂`. -/
lemma pcfCt_rpow_le_add {t q1 q2 r : ℝ} (ht : 0 < t) (h1 : q1 ≤ r) (h2 : r ≤ q2) :
    t ^ r ≤ t ^ q1 + t ^ q2 := by
  rcases le_total t 1 with h | h
  · have := Real.rpow_le_rpow_of_exponent_ge ht h h1
    have := Real.rpow_nonneg ht.le q2
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h h2
    have := Real.rpow_nonneg ht.le q1
    linarith

/-- Local domination for the integrand of 12.12.3 in the parameter `a`. -/
lemma pcfCt_integral_3_dom {a0 : ℂ} (ha0 : a0.re < 1/2) {x : ℝ} (hx : 0 < x) :
    ∃ V ∈ 𝓝 a0, ∃ g : ℝ → ℝ, IntegrableOn g (Ioi 0) ∧ ∀ t ∈ Ioi (0:ℝ), ∀ a ∈ V,
      ‖exp (-t^2/4)*(t:ℂ)^(-a-1/2)/(x^2+t^2:ℂ)*pcfU a t‖ ≤ g t := by
  set δ := (1/2 - a0.re)/2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  obtain ⟨M, hM⟩ := pcfCt_U_decay (‖a0‖ + δ + 1/2)
  set q1 := -a0.re - 1/2 - δ
  set q2 := -a0.re - 1/2 + δ
  refine ⟨Metric.ball a0 δ, Metric.ball_mem_nhds _ hδ0,
    fun t => M / x^2 * ((Real.exp (-t) * t ^ (q1+1-1)) + (Real.exp (-t) * t ^ (q2+1-1))), ?_, ?_⟩
  · refine Integrable.const_mul (Integrable.add ?_ ?_) _
    · exact Real.GammaIntegral_convergent (by simp only [q1, hδ]; linarith)
    · exact Real.GammaIntegral_convergent (by simp only [q2, hδ]; linarith)
  · intro t ht a ha
    have ht : 0 < t := ht
    have hda : ‖a - a0‖ < δ := by simpa [dist_eq_norm] using ha
    have hre : |a.re - a0.re| < δ := by
      have := abs_re_le_norm (a - a0); simp at this; linarith
    have hP : ‖-a-1/2‖ ≤ ‖a0‖ + δ + 1/2 := by
      calc ‖-a-1/2‖ ≤ ‖a‖ + 1/2 := by
            have := norm_add_le (-a) (-(1/2:ℂ)); simp [sub_eq_add_neg] at this ⊢
            norm_num at this ⊢; linarith
        _ ≤ ‖a0‖ + δ + 1/2 := by
            have := norm_le_norm_add_norm_sub' a a0; linarith
    have hU := hM a hP t
    have hc : ‖(t:ℂ)^(-a-1/2)‖ = t ^ (-a.re - 1/2) := by
      rw [norm_cpow_eq_rpow_re_of_pos ht]; simp
    have hden : x^2 ≤ ‖((x:ℂ)^2+(t:ℂ)^2)‖ := by
      rw [show ((x:ℂ)^2+(t:ℂ)^2) = ((x^2+t^2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
      nlinarith
    have hrp := pcfCt_rpow_le_add (r := -a.re - 1/2) ht (q1 := q1) (q2 := q2)
      (by simp only [q1]; linarith [(abs_lt.mp hre).2]) (by simp only [q2]; linarith [(abs_lt.mp hre).1])
    have hx2 : 0 < x^2 := by positivity
    simp only [add_sub_cancel_right]
    calc ‖exp (-t^2/4)*(t:ℂ)^(-a-1/2)/(x^2+t^2:ℂ)*pcfU a t‖
        = ‖(t:ℂ)^(-a-1/2)‖ / ‖((x:ℂ)^2+(t:ℂ)^2)‖ * ‖exp (-(t:ℂ)^2/4) * pcfU a t‖ := by
          rw [norm_mul, norm_div, norm_mul, norm_mul]; ring
      _ ≤ (t ^ q1 + t ^ q2) / x^2 * (M * Real.exp (-t)) := by
          rw [hc]
          apply mul_le_mul _ hU (norm_nonneg _) (by positivity)
          exact div_le_div₀ (by positivity) hrp hx2 hden
      _ = _ := by ring
/-- DLMF 12.12.3 as a Lebesgue integral on `(0,∞)`, for all `Re a < 1/2`. -/
lemma pcfCt_integral_3_all {a : ℂ} (ha : a.re < 1/2) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => exp (-t^2/4)*(t:ℂ)^(-a-1/2)/(x^2+t^2:ℂ)*pcfU a t) (Ioi 0) ∧
    ∫ t in Ioi (0:ℝ), exp (-t^2/4)*(t:ℂ)^(-a-1/2)/(x^2+t^2:ℂ)*pcfU a t =
      (Real.sqrt (π/2):ℂ)*Gamma (1/2-a)*(x:ℂ)^(-a-3/2)*exp (x^2/4)*pcfU (-a) x := by
  set Ω : Set ℂ := {a | a.re < 1/2} with hΩ
  have hΩo : IsOpen Ω := isOpen_lt Complex.continuous_re continuous_const
  have hint : ∀ b ∈ Ω, IntegrableOn
      (fun t : ℝ => exp (-t^2/4)*(t:ℂ)^(-b-1/2)/(x^2+t^2:ℂ)*pcfU b t) (Ioi 0) := by
    intro b hb
    obtain ⟨V, hV, g, hg, hle⟩ := pcfCt_integral_3_dom (a0 := b) hb hx
    refine Integrable.mono' hg ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      intro t ht
      have ht : (0:ℝ) < t := ht
      refine ContinuousAt.continuousWithinAt ?_
      have hden : ((x:ℂ)^2 + (t:ℂ)^2) ≠ 0 := by
        rw [show ((x:ℂ)^2+(t:ℂ)^2) = ((x^2+t^2 : ℝ) : ℂ) by push_cast; ring]
        exact_mod_cast (by positivity : (0:ℝ) < x^2+t^2).ne'
      have hcp : ContinuousAt (fun s : ℝ => (s:ℂ)^(-b-1/2)) t :=
        Complex.continuous_ofReal.continuousAt.cpow continuousAt_const
          (Complex.ofReal_mem_slitPlane.mpr ht)
      have hU : ContinuousAt (fun s : ℝ => pcfU b s) t :=
        ((pcfU_entire b).continuous.comp Complex.continuous_ofReal).continuousAt
      exact (((by fun_prop : Continuous fun s : ℝ => exp (-(s:ℂ)^2/4)).continuousAt.mul hcp).div
        (by fun_prop) hden).mul hU
    · exact (ae_restrict_iff' measurableSet_Ioi).mpr
        (Eventually.of_forall fun t ht => hle t ht b (mem_of_mem_nhds hV))
  refine ⟨hint a ha, ?_⟩
  set Λ : ℂ → ℂ := fun b => ∫ t in Ioi (0:ℝ),
    exp (-t^2/4)*(t:ℂ)^(-b-1/2)/(x^2+t^2:ℂ)*pcfU b t
  set R : ℂ → ℂ := fun b =>
    (Real.sqrt (π/2):ℂ)*Gamma (1/2-b)*(x:ℂ)^(-b-3/2)*exp (x^2/4)*pcfU (-b) x
  have hΛ : DifferentiableOn ℂ Λ Ω := by
    refine differentiableOn_integral_of_locally_dominated hΩo
      (fun b hb => (hint b hb).aestronglyMeasurable) ?_ ?_
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
      have ht : (0:ℝ) < t := ht
      have htc : (t:ℂ) ≠ 0 := by exact_mod_cast ht.ne'
      refine Differentiable.differentiableOn ?_
      exact (((differentiable_const _).mul
        ((by fun_prop : Differentiable ℂ fun b : ℂ => -b-1/2).const_cpow (Or.inl htc))).div_const
        _).mul (pcfU_entire_order (t:ℂ))
    · intro b hb
      obtain ⟨V, hV, g, hg, hle⟩ := pcfCt_integral_3_dom (a0 := b) hb hx
      exact ⟨V, hV, g, hg, (ae_restrict_iff' measurableSet_Ioi).mpr
        (Eventually.of_forall fun t ht c hc => hle t ht c hc)⟩
  have hxc : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hR : DifferentiableOn ℂ R Ω := by
    intro b hb
    have hb : b.re < 1/2 := hb
    have hG : DifferentiableAt ℂ (fun c : ℂ => Gamma (1/2-c)) b := by
      refine (Complex.differentiableAt_Gamma _ ?_).comp b (by fun_prop)
      intro m hm
      have := congrArg Complex.re hm
      simp at this
      have : (0:ℝ) ≤ m := m.cast_nonneg
      linarith
    refine DifferentiableAt.differentiableWithinAt ?_
    exact ((((differentiableAt_const _).mul hG).mul
      ((by fun_prop : Differentiable ℂ fun c : ℂ => -c-3/2).const_cpow (Or.inl hxc) b)).mul
      (differentiableAt_const _)).mul
      ((pcfU_entire_order (x:ℂ)).comp (by fun_prop : Differentiable ℂ fun c : ℂ => -c) b)
  have h0 : (0:ℂ) ∈ Ω := by simp [hΩ]
  have hev : Λ =ᶠ[𝓝 (0:ℂ)] R := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) (by norm_num : (0:ℝ) < 1/2)] with b hb
    have hb' : ‖b‖ < 1/2 := by simpa using hb
    have := abs_re_le_norm b
    exact (pcfCt_integral_3_strip (by linarith [neg_abs_le b.re]) (by linarith [le_abs_self b.re])
      hx).2
  exact (hΛ.analyticOnNhd hΩo).eqOn_of_preconnected_of_eventuallyEq (hR.analyticOnNhd hΩo)
    (convex_halfSpace_re_lt (1/2)).isPreconnected h0 hev ha

/-- pcf integral 3. -/
@[dlmf 12.12.E3]
theorem pcf_integral_3 {a : ℂ} (ha : a.re < 1/2) {x : ℝ} (hx : 0 < x) :
    HasIntegralAtTop (fun t : ℝ => exp (-t^2/4)*(t:ℂ)^(-a-1/2)/(x^2+t^2:ℂ)*pcfU a t) 0 ((Real.sqrt (π/2):ℂ)*Gamma (1/2-a)*(x:ℂ)^(-a-3/2)*exp (x^2/4)*pcfU (-a) x) := by
  obtain ⟨hI, hv⟩ := pcfCt_integral_3_all ha hx
  unfold HasIntegralAtTop
  rw [← hv]
  exact intervalIntegral_tendsto_integral_Ioi 0 hI tendsto_id

/-- Exponential lower bound for the hyperbolic sine away from its zero. -/
lemma pcfIntegral4_sqrt_sinh_lower {t : ℝ} (ht : 1 ≤ t) :
    Real.exp t / 2 ≤ Real.sqrt (Real.sinh (2*t)) := by
  have he1 : 1 ≤ Real.exp (2*t) := Real.one_le_exp_iff.mpr (by linarith)
  have he2 : Real.exp (-2*t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have he3 : 3 ≤ Real.exp (2*t) := by linarith [Real.add_one_le_exp (2*t)]
  have hex : Real.exp t ^ 2 = Real.exp (2*t) := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  have hsin : Real.exp (2*t) / 4 ≤ Real.sinh (2*t) := by
    rw [Real.sinh_eq]; rw [show -(2*t) = -2*t by ring]; linarith
  apply (Real.le_sqrt (by positivity) (by positivity)).mpr
  nlinarith [Real.sq_sqrt (Real.sinh_nonneg_iff.mpr (by linarith))]

/-- The hyperbolic weight in the cylinder square integral is integrable
precisely on the needed exponential side of the parameter bound. -/
lemma pcfIntegral4_weight_integrable {b : ℝ} (hb : b < 1) :
    IntegrableOn (fun t : ℝ => Real.exp (b*t) / Real.sqrt (Real.sinh (2*t))) (Ioi 0) := by
  have hc : ContinuousOn (fun t : ℝ => Real.exp (b*t) / Real.sqrt (Real.sinh (2*t))) (Ioi 0) := by
    refine (by fun_prop : Continuous (fun t : ℝ => Real.exp (b*t))).continuousOn.div
      (by fun_prop) ?_
    intro t ht
    exact ne_of_gt (Real.sqrt_pos.mpr (Real.sinh_pos_iff.mpr (by linarith [show 0 < t from ht] : 0 < 2*t)))
  have hnear : IntegrableOn (fun t : ℝ => Real.exp (b*t) / Real.sqrt (Real.sinh (2*t))) (Ioc 0 1) := by
    have hr : IntegrableOn (fun t : ℝ => t^(-(1/2):ℝ)) (Ioc 0 1) := by
      rw [integrableOn_Ioc_iff_integrableOn_Ioo, intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one]
      norm_num
    refine (hr.const_mul (Real.exp |b|)).mono' ((hc.mono (by intro t ht; exact ht.1)).aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hsin : t ≤ Real.sinh (2*t) := by
      have := Real.self_le_sinh_iff.mpr (show 0 ≤ 2*t by linarith [ht.1])
      linarith [ht.1]
    have hnum : b*t ≤ |b| := by
      calc b*t ≤ |b| *t := mul_le_mul_of_nonneg_right (le_abs_self _) ht.1.le
           _ ≤ |b| *1 := mul_le_mul_of_nonneg_left ht.2 (abs_nonneg _)
           _ = |b| := mul_one _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc Real.exp (b*t) / Real.sqrt (Real.sinh (2*t)) ≤ Real.exp |b| / Real.sqrt t :=
        div_le_div₀ (by positivity) (Real.exp_le_exp.mpr hnum)
          (Real.sqrt_pos.mpr ht.1) (Real.sqrt_le_sqrt hsin)
      _ = Real.exp |b| * t^(-(1/2):ℝ) := by
        rw [Real.rpow_neg ht.1.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]
  have hfar : IntegrableOn (fun t : ℝ => Real.exp (b*t) / Real.sqrt (Real.sinh (2*t))) (Ioi 1) := by
    refine ((integrableOn_exp_mul_Ioi (a:=b-1) (by linarith) 1).const_mul 2).mono'
      ((hc.mono (Ioi_subset_Ioi (by norm_num))).aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc Real.exp (b*t) / Real.sqrt (Real.sinh (2*t)) ≤ Real.exp (b*t) / (Real.exp t/2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (pcfIntegral4_sqrt_sinh_lower ht.le)
      _ = 2 * Real.exp ((b-1)*t) := by
        rw [div_div_eq_mul_div, mul_comm (Real.exp (b*t)), mul_div_assoc, ← Real.exp_sub]
        congr 2
        ring
  have hU : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext t
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (ht | ht)
      · exact ht.1
      · linarith
    · intro ht
      by_cases h : t ≤ 1
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr (lt_of_not_ge h)
  rw [← hU]
  exact hnear.union hfar


/-- Uniform-in-`z` majorant for the cylinder square-integral kernel. -/
lemma pcfIntegral4_kernel_norm_le (a z : ℂ) {t : ℝ} (_ht : 0 < t) :
    ‖exp (2*a*t + z^2/2*Real.tanh t) / (Real.sqrt (Real.sinh (2*t)) : ℂ)‖ ≤
      Real.exp (‖z‖^2/2) * (Real.exp (2*a.re*t) / Real.sqrt (Real.sinh (2*t))) := by
  have harg : (z^2/2*(Real.tanh t : ℂ)).re ≤ ‖z‖^2/2 := by
    calc _ ≤ ‖z^2/2*(Real.tanh t : ℂ)‖ := Complex.re_le_norm _
      _ = ‖z‖^2/2 * |Real.tanh t| := by
        simp only [norm_mul, norm_div, norm_pow, Complex.norm_ofNat,
          Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖z‖^2/2 := mul_le_of_le_one_right (by positivity) (Real.abs_tanh_lt_one t).le
  rw [norm_div, Complex.norm_exp, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc Real.exp (2*a*t + z^2/2*Real.tanh t).re / Real.sqrt (Real.sinh (2*t)) ≤
      Real.exp (2*a.re*t + ‖z‖^2/2) / Real.sqrt (Real.sinh (2*t)) := by
        apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
        apply Real.exp_le_exp.mpr
        rw [Complex.add_re]
        have hre : (2*a*(t:ℂ)).re = 2*a.re*t := by simp
        rw [hre]
        exact add_le_add le_rfl harg
    _ = _ := by rw [Real.exp_add]; ring

/-- Continuity in the integration variable away from the integrable endpoint. -/
lemma pcfIntegral4_kernel_continuousOn (a z : ℂ) :
    ContinuousOn (fun t : ℝ =>
      exp (2*a*t + z^2/2*Real.tanh t) / (Real.sqrt (Real.sinh (2*t)) : ℂ)) (Ioi 0) := by
  have htan : Continuous (fun t : ℝ => Real.tanh t) := by
    simp only [Real.tanh_eq_sinh_div_cosh]
    exact Real.continuous_sinh.div Real.continuous_cosh fun t => ne_of_gt (Real.cosh_pos t)
  refine ((by fun_prop : Continuous (fun t : ℝ =>
    exp (2*a*t + z^2/2*Real.tanh t)))).continuousOn.div (by fun_prop) ?_
  intro t ht
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr
    (Real.sinh_pos_iff.mpr (mul_pos (by norm_num) ht))))

/-- Absolute convergence of the cylinder square-integral kernel. -/
lemma pcfIntegral4_kernel_integrable {a : ℂ} (ha : a.re < 1/2) (z : ℂ) :
    IntegrableOn (fun t : ℝ =>
      exp (2*a*t + z^2/2*Real.tanh t) / (Real.sqrt (Real.sinh (2*t)) : ℂ)) (Ioi 0) := by
  refine ((pcfIntegral4_weight_integrable (b := 2*a.re) (by linarith)).const_mul
    (Real.exp (‖z‖^2/2))).mono'
    ((pcfIntegral4_kernel_continuousOn a z).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact pcfIntegral4_kernel_norm_le a z ht

/-- Absolute convergence, including the original normalization, of DLMF 12.12.4. -/
theorem pcf_integral_4_integrable {a : ℂ} (ha : a.re < 1/2) (z : ℂ) :
    IntegrableOn (fun t : ℝ => 2^(3/2:ℂ)/π*Gamma (1/2-a)*
      exp (2*a*t+z^2/2*Real.tanh t)/(Real.sqrt (Real.sinh (2*t)):ℂ)) (Ioi 0) := by
  simpa only [mul_div_assoc, IntegrableOn] using
    (pcfIntegral4_kernel_integrable ha z).const_mul ((2:ℂ)^(3/2:ℂ)/π*Gamma (1/2-a))


/-- Products of Weber solutions obey the common symmetric-square equation.
This is the ODE needed to identify the convergent integral in DLMF 12.12.4. -/
theorem weber_product_ode {a : ℂ} {f f' g g' : ℂ → ℂ}
    (hf : IsWeberSol a f f') (hg : IsWeberSol a g g') (z : ℂ) :
    iteratedDeriv 3 (fun t => f t * g t) z -
      (z^2 + 4*a) * deriv (fun t => f t * g t) z - z * f z * g z = 0 := by
  have hq (w : ℂ) : HasDerivAt (fun t : ℂ => t^2/4 + a) (w/2) w := by
    exact ((((hasDerivAt_id w).pow 2).div_const 4).add_const a).congr_deriv (by
      simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
      ring)
  have he := ODE.product_third_deriv hf hg hq z
  linear_combination he

/-- The unnormalized kernel of the cylinder square integral. -/
def pcfIntegral4Kernel (a z : ℂ) (t : ℝ) : ℂ :=
  exp (2*a*t + z^2/2*Real.tanh t) / (Real.sqrt (Real.sinh (2*t)) : ℂ)

/-- Hyperbolic moments of the cylinder square-integral kernel. -/
def pcfIntegral4Moment (a : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, (Real.tanh t : ℂ)^n * pcfIntegral4Kernel a z t

/-- Continuity of the hyperbolic factor in the moment kernels. -/
lemma pcfIntegral4_tanh_continuous : Continuous (fun t : ℝ => (Real.tanh t : ℂ)) := by
  have htan : Continuous (fun t : ℝ => Real.tanh t) := by
    simp only [Real.tanh_eq_sinh_div_cosh]
    exact Real.continuous_sinh.div Real.continuous_cosh fun t => ne_of_gt (Real.cosh_pos t)
  exact Complex.continuous_ofReal.comp htan

/-- Hyperbolic moments have the same integrable majorant as the base kernel. -/
lemma pcfIntegral4_moment_norm_le (a z : ℂ) (n : ℕ) (t : ℝ) :
    ‖(Real.tanh t : ℂ)^n * pcfIntegral4Kernel a z t‖ ≤ ‖pcfIntegral4Kernel a z t‖ := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (abs_nonneg _) (Real.abs_tanh_lt_one t).le)

/-- Every nonnegative hyperbolic moment is absolutely integrable. -/
lemma pcfIntegral4_moment_integrable {a : ℂ} (ha : a.re < 1/2) (n : ℕ) (z : ℂ) :
    IntegrableOn (fun t : ℝ => (Real.tanh t : ℂ)^n * pcfIntegral4Kernel a z t) (Ioi 0) := by
  refine (pcfIntegral4_kernel_integrable ha z).norm.mono'
    (((pcfIntegral4_tanh_continuous.pow n).continuousOn.mul
      (pcfIntegral4_kernel_continuousOn a z)).aestronglyMeasurable measurableSet_Ioi) ?_
  exact Eventually.of_forall (pcfIntegral4_moment_norm_le a z n)

/-- Differentiating the argument raises the hyperbolic moment index. -/
lemma pcfIntegral4_hasDerivAt_kernel_arg (a z : ℂ) (n : ℕ) (t : ℝ) :
    HasDerivAt (fun w => (Real.tanh t : ℂ)^n * pcfIntegral4Kernel a w t)
      (z * ((Real.tanh t : ℂ)^(n+1) * pcfIntegral4Kernel a z t)) z := by
  unfold pcfIntegral4Kernel
  have h := ((((((hasDerivAt_id z).pow 2).div_const 2).mul_const (Real.tanh t : ℂ)).const_add
    (2*a*t)).cexp.div_const (Real.sqrt (Real.sinh (2*t)) : ℂ)).const_mul ((Real.tanh t : ℂ)^n)
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, mul_one, pow_succ]
  ring

/-- Differentiation under the absolutely convergent moment integral. -/
lemma pcfIntegral4_hasDerivAt_moment {a : ℂ} (ha : a.re < 1/2) (n : ℕ) (z : ℂ) :
    HasDerivAt (pcfIntegral4Moment a n) (z * pcfIntegral4Moment a (n+1) z) z := by
  have hm (w : ℂ) (k : ℕ) : AEStronglyMeasurable
      (fun t : ℝ => (Real.tanh t : ℂ)^k * pcfIntegral4Kernel a w t)
      (volume.restrict (Ioi 0)) :=
    (((pcfIntegral4_tanh_continuous.pow k).continuousOn.mul
      (pcfIntegral4_kernel_continuousOn a w)).aestronglyMeasurable measurableSet_Ioi)
  have he := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0))
    (F := fun w t => (Real.tanh t : ℂ)^n * pcfIntegral4Kernel a w t)
    (F' := fun w t => w * ((Real.tanh t : ℂ)^(n+1) * pcfIntegral4Kernel a w t))
    (bound := fun t => (‖z‖+1) * (Real.exp ((‖z‖+1)^2/2) *
      (Real.exp (2*a.re*t) / Real.sqrt (Real.sinh (2*t)))))
    (Metric.ball_mem_nhds z zero_lt_one)
    (Eventually.of_forall fun w => hm w n)
    (pcfIntegral4_moment_integrable ha n z)
    ((hm z (n+1)).const_mul z) ?_
    (((pcfIntegral4_weight_integrable (b := 2*a.re) (by linarith)).const_mul
      (Real.exp ((‖z‖+1)^2/2))).const_mul (‖z‖+1))
    (Eventually.of_forall fun t w _ => pcfIntegral4_hasDerivAt_kernel_arg a w n t)
  · convert he.2 using 1 <;> first | rfl | simp [pcfIntegral4Moment, integral_const_mul]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro w hw
    have hw' : ‖w‖ ≤ ‖z‖+1 := by
      have hdist : ‖w-z‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
      have := norm_add_le (w-z) z
      rw [sub_add_cancel] at this
      linarith
    rw [norm_mul]
    calc ‖w‖ * ‖(Real.tanh t : ℂ)^(n+1) * pcfIntegral4Kernel a w t‖ ≤
        (‖z‖+1) * ‖pcfIntegral4Kernel a w t‖ :=
          mul_le_mul hw' (pcfIntegral4_moment_norm_le a w (n+1) t)
            (norm_nonneg _) (by positivity)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine (pcfIntegral4_kernel_norm_le a w ht).trans ?_
        gcongr


/-- The hyperbolic derivative in the cylinder kernel. -/
lemma pcfIntegral4_tanh_hasDerivAt (t : ℝ) :
    HasDerivAt Real.tanh (1 - Real.tanh t ^ 2) t := by
  have hc : Real.cosh t ≠ 0 := (Real.cosh_pos t).ne'
  convert ((Real.hasDerivAt_sinh t).div (Real.hasDerivAt_cosh t) hc) using 1
  · funext u; exact Real.tanh_eq_sinh_div_cosh u
  · rw [Real.tanh_eq_sinh_div_cosh]
    field_simp

/-- Time derivative of the cylinder square-integral kernel. -/
lemma pcfIntegral4_hasDerivAt_kernel_time (a z : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (pcfIntegral4Kernel a z)
      ((2*a + z^2/2*(1-(Real.tanh t : ℂ)^2) -
        (Real.cosh (2*t) : ℂ)/(Real.sinh (2*t) : ℂ)) * pcfIntegral4Kernel a z t) t := by
  have hs : 0 < Real.sinh (2*t) := Real.sinh_pos_iff.mpr (by linarith)
  have hs0 : (Real.sqrt (Real.sinh (2*t)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hs).ne'
  have hsq : (Real.sinh (2*t) : ℂ) = (Real.sqrt (Real.sinh (2*t)) : ℂ)^2 := by
    exact_mod_cast (Real.sq_sqrt hs.le).symm
  have hr : HasDerivAt (fun u : ℝ => (Real.tanh u : ℂ))
      (1-(Real.tanh t : ℂ)^2) t := by
    convert (pcfIntegral4_tanh_hasDerivAt t).ofReal_comp using 1 <;> push_cast <;> rfl
  have hnum := (((hasDerivAt_id t).ofReal_comp.const_mul (2*a)).add
    (hr.const_mul (z^2/2))).cexp
  have hden := (((Real.hasDerivAt_sinh (2*t)).comp t
    ((hasDerivAt_id t).const_mul 2)).sqrt hs.ne').ofReal_comp
  have h := hnum.div hden hs0
  refine h.congr_deriv ?_
  simp only [pcfIntegral4Kernel, id_eq, Pi.add_apply, Function.comp_apply,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [hsq]
  field_simp

/-- The integrable total derivative that yields the moment recurrence. -/
lemma pcfIntegral4_hasDerivAt_tanh_kernel (a z : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u => (Real.tanh u : ℂ) * pcfIntegral4Kernel a z u)
      ((1/2 + 2*a*(Real.tanh t : ℂ) - 3/2*(Real.tanh t : ℂ)^2 +
        z^2/2*((Real.tanh t : ℂ) - (Real.tanh t : ℂ)^3)) * pcfIntegral4Kernel a z t) t := by
  have hr : HasDerivAt (fun u : ℝ => (Real.tanh u : ℂ))
      (1-(Real.tanh t : ℂ)^2) t := by
    convert (pcfIntegral4_tanh_hasDerivAt t).ofReal_comp using 1 <;> push_cast <;> rfl
  have hc : (Real.cosh t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.cosh_pos t).ne'
  have hs : (Real.sinh t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.sinh_pos_iff.mpr ht).ne'
  have hrat : (Real.tanh t : ℂ) * (Real.cosh (2*t) : ℂ) / (Real.sinh (2*t) : ℂ) =
      (1 + (Real.tanh t : ℂ)^2)/2 := by
    simp only [Real.tanh_eq_sinh_div_cosh, Real.sinh_two_mul, Real.cosh_two_mul,
      Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_pow,
      Complex.ofReal_ofNat]
    field_simp
  refine (hr.mul (pcfIntegral4_hasDerivAt_kernel_time a z ht)).congr_deriv ?_
  linear_combination -pcfIntegral4Kernel a z t * hrat



/-- The moment kernels vanish at the infinite endpoint. -/
lemma pcfIntegral4_moment_tendsto_zero {a : ℂ} (ha : a.re < 1/2) (n : ℕ) (z : ℂ) :
    Tendsto (fun t : ℝ => (Real.tanh t : ℂ)^n * pcfIntegral4Kernel a z t) atTop (𝓝 0) := by
  have hl : Tendsto (fun t : ℝ => 2*Real.exp (‖z‖^2/2) * Real.exp ((2*a.re-1)*t))
      atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by linarith : 2*a.re-1 < 0))).const_mul
        (2*Real.exp (‖z‖^2/2))
  refine squeeze_zero_norm' ?_ hl
  filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
  refine (pcfIntegral4_moment_norm_le a z n t).trans ?_
  refine (pcfIntegral4_kernel_norm_le a z (by linarith : 0 < t)).trans ?_
  calc Real.exp (‖z‖^2/2) * (Real.exp (2*a.re*t) / Real.sqrt (Real.sinh (2*t))) ≤
      Real.exp (‖z‖^2/2) * (Real.exp (2*a.re*t) / (Real.exp t/2)) := by
        gcongr
        exact pcfIntegral4_sqrt_sinh_lower ht
    _ = _ := by
      rw [div_div_eq_mul_div, mul_comm (Real.exp (2*a.re*t)), mul_div_assoc, ← Real.exp_sub]
      rw [show 2*a.re*t-t=(2*a.re-1)*t by ring]
      ring

/-- The hyperbolic factor removes the square-root singularity at zero. -/
lemma pcfIntegral4_tanh_kernel_continuous_zero (a z : ℂ) :
    ContinuousWithinAt (fun t => (Real.tanh t : ℂ) * pcfIntegral4Kernel a z t) (Ici 0) 0 := by
  have heq (t : ℝ) (ht : 0 ≤ t) :
      (Real.tanh t : ℂ) * pcfIntegral4Kernel a z t =
        exp (2*a*t+z^2/2*Real.tanh t) *
          (Real.sqrt (Real.sinh (2*t)) : ℂ)/(2*(Real.cosh t : ℂ)^2) := by
    rcases ht.eq_or_lt with rfl | ht
    · simp [pcfIntegral4Kernel]
    have hs : 0 < Real.sinh (2*t) := Real.sinh_pos_iff.mpr (by linarith)
    have hs0 : (Real.sqrt (Real.sinh (2*t)) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hs).ne'
    have hc0 : (Real.cosh t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.cosh_pos t).ne'
    have hsq : (Real.sqrt (Real.sinh (2*t)) : ℂ)^2 =
        2*(Real.sinh t : ℂ)*(Real.cosh t : ℂ) := by
      calc _ = (Real.sinh (2*t) : ℂ) := by exact_mod_cast Real.sq_sqrt hs.le
           _ = _ := by simp only [Real.sinh_two_mul, Complex.ofReal_mul, Complex.ofReal_ofNat]
    simp only [pcfIntegral4Kernel, Real.tanh_eq_sinh_div_cosh, Complex.ofReal_div]
    field_simp
    linear_combination -hsq
  have hc : Continuous (fun t : ℝ => exp (2*a*t+z^2/2*Real.tanh t) *
      (Real.sqrt (Real.sinh (2*t)) : ℂ)/(2*(Real.cosh t : ℂ)^2)) := by
    have := pcfIntegral4_tanh_continuous
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro t
    exact mul_ne_zero two_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.cosh_pos t).ne'))
  exact hc.continuousWithinAt.congr (fun t ht => heq t ht) (heq 0 le_rfl)


/-- Integration by parts gives the four-moment relation. -/
lemma pcfIntegral4_moment_relation {a : ℂ} (ha : a.re < 1/2) (z : ℂ) :
    pcfIntegral4Moment a 0 z + 4*a*pcfIntegral4Moment a 1 z -
      3*pcfIntegral4Moment a 2 z + z^2*(pcfIntegral4Moment a 1 z - pcfIntegral4Moment a 3 z) = 0 := by
  let T (n : ℕ) (t : ℝ) : ℂ := (Real.tanh t : ℂ)^n * pcfIntegral4Kernel a z t
  have hT (n : ℕ) : IntegrableOn (T n) (Ioi 0) := pcfIntegral4_moment_integrable ha n z
  let R' (t : ℝ) := (1/2:ℂ)*T 0 t + 2*a*T 1 t - (3/2:ℂ)*T 2 t +
    z^2/2*(T 1 t - T 3 t)
  have hA := (hT 0).const_mul (1/2:ℂ)
  have hB := (hT 1).const_mul (2*a)
  have hC := (hT 2).const_mul (3/2:ℂ)
  have hD := ((hT 1).sub (hT 3)).const_mul (z^2/2)
  have hR : IntegrableOn R' (Ioi 0) := ((hA.add hB).sub hC).add hD
  have hd (t : ℝ) (ht : t ∈ Ioi 0) :
      HasDerivAt (fun u => (Real.tanh u : ℂ)*pcfIntegral4Kernel a z u) (R' t) t := by
    refine (pcfIntegral4_hasDerivAt_tanh_kernel a z ht).congr_deriv ?_
    dsimp [R', T]
    ring
  have hv := integral_Ioi_of_hasDerivAt_of_tendsto
    (pcfIntegral4_tanh_kernel_continuous_zero a z) hd hR
    (by simpa only [pow_one] using pcfIntegral4_moment_tendsto_zero ha 1 z)
  have he : (∫ t : ℝ in Ioi 0, R' t) =
      (1/2:ℂ)*pcfIntegral4Moment a 0 z + 2*a*pcfIntegral4Moment a 1 z -
        (3/2:ℂ)*pcfIntegral4Moment a 2 z +
        z^2/2*(pcfIntegral4Moment a 1 z - pcfIntegral4Moment a 3 z) := by
    change (∫ t : ℝ in Ioi 0, (1/2:ℂ)*T 0 t + 2*a*T 1 t - (3/2:ℂ)*T 2 t +
      z^2/2*(T 1 t - T 3 t)) = _
    have e1 := integral_add ((hA.add hB).sub hC) hD
    have e2 := integral_sub (hA.add hB) hC
    have e3 := integral_add hA hB
    have e4 := integral_sub (hT 1) (hT 3)
    simp only [Pi.add_apply, Pi.sub_apply] at e1 e2 e3 e4
    rw [e1, e2, e3, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_const_mul, e4]
    rfl
  simp only [Real.tanh_zero, Complex.ofReal_zero, zero_mul, sub_zero] at hv
  linear_combination 2*hv - 2*he

/-- The cylinder square integral solves the symmetric-square Weber equation. -/
lemma pcfIntegral4_isThirdOrderSolution {a : ℂ} (ha : a.re < 1/2) :
    ODE.IsThirdOrderSolution (fun z : ℂ => z^2+4*a) (fun z => z)
      (pcfIntegral4Moment a 0) (fun z => z*pcfIntegral4Moment a 1 z)
      (fun z => pcfIntegral4Moment a 1 z + z^2*pcfIntegral4Moment a 2 z) := by
  intro z
  refine ⟨pcfIntegral4_hasDerivAt_moment ha 0 z, ?_, ?_⟩
  · refine ((hasDerivAt_id z).mul (pcfIntegral4_hasDerivAt_moment ha 1 z)).congr_deriv ?_
    simp only [id_eq]
    ring
  · have hd := (pcfIntegral4_hasDerivAt_moment ha 1 z).add
      (((hasDerivAt_id z).pow 2).mul (pcfIntegral4_hasDerivAt_moment ha 2 z))
    refine hd.congr_deriv ?_
    simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    linear_combination -z * pcfIntegral4_moment_relation ha z


/-- The convergent integral in DLMF 12.12.4 is entire in the argument.
This is the zeroth case of the common moment derivative theorem. -/
theorem pcfIntegral4_kernel_differentiable {a : ℂ} (ha : a.re < 1/2) :
    Differentiable ℂ (fun z : ℂ => ∫ t : ℝ in Ioi 0,
      exp (2*a*t + z^2/2*Real.tanh t) / (Real.sqrt (Real.sinh (2*t)) : ℂ)) := by
  intro z
  convert (pcfIntegral4_hasDerivAt_moment ha 0 z).differentiableAt using 1
  funext w
  simp only [pcfIntegral4Moment, pcfIntegral4Kernel, pow_zero, one_mul]






/-- A pole-safe sine/cosine factorization of the two cylinder solutions at the origin. -/
lemma pcfProduct_zero_pair_v {v : ℂ} (hv : 0 < v.re) :
    pcfU (1/2-2*v) 0 = ((2 : ℂ)^(v-1/2)*Gamma v/(Real.sqrt π))*sin (π*v) ∧
    pcfUBar (1/2-2*v) 0 = ((2 : ℂ)^(v-1/2)*Gamma v/(Real.sqrt π))*cos (π*v) := by
  have hG : Gamma v ≠ 0 := Gamma_ne_zero_of_re_pos hv
  have hG1 : Gamma (v+1/2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hs2 : (Real.sqrt π : ℂ)^2 = π := by norm_cast; exact Real.sq_sqrt Real.pi_pos.le
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  let C : ℂ := (2 : ℂ)^(v-1/2)*Gamma v/(Real.sqrt π)
  have hU : pcfU (1/2-2*v) 0 = C * sin (π*v) := by
    rw [pcfU_zero', show -((1/2-2*v)/2+1/4) = v-1/2 by ring,
      show 3/4+(1/2-2*v)/2 = 1-v by ring, recip_Gamma_one_sub_eq hG]
    dsimp only [C]
    field_simp
    rw [hs2]
  have hdup := Gamma_mul_Gamma_add_half v
  have hpows : (2 : ℂ)^(1-2*v)*(2 : ℂ)^(v-1/2) = (2 : ℂ)^(1/2-v) := by
    rw [← cpow_add _ _ h2]; congr 1; ring
  have hV : pcfUBar (1/2-2*v) 0 = C * cos (π*v) := by
    rw [pcfUBar, pcfV_zero', pcfVZero,
      show (1/2:ℂ)-(1/2-2*v) = 2*v by ring,
      show (1/2-2*v)/2+1/4 = 1/2-v by ring,
      show 3/4-(1/2-2*v)/2 = v+1/2 by ring,
      show 1/4+(1/2-2*v)/2 = 1-(v+1/2) by ring,
      recip_Gamma_one_sub_eq hG1]
    have hsin : sin (π*(v+1/2)) = cos (π*v) := by
      rw [show π*(v+1/2) = π*v+π/2 by ring, sin_add_pi_div_two]
    rw [hsin, ← hpows]
    dsimp only [C]
    generalize (2 : ℂ)^(1-2*v) = E at hdup ⊢
    generalize Gamma (v+1/2) = G at hdup hG1 ⊢
    generalize cos (π*v) = T
    field_simp
    linear_combination -T*hdup
  exact ⟨hU, hV⟩

/-- The cylinder-square initial value expressed through a beta integral. -/
lemma pcfProduct_zero_beta_v {v : ℂ} (hv : 0 < v.re) :
    Gamma (2*v) * betaIntegral v (1/2) / π =
      (pcfU (1/2-2*v) 0)^2 + (pcfUBar (1/2-2*v) 0)^2 := by
  have hG : Gamma v ≠ 0 := Gamma_ne_zero_of_re_pos hv
  have hG1 : Gamma (v+1/2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hs2 : (Real.sqrt π : ℂ)^2 = π := by norm_cast; exact Real.sq_sqrt Real.pi_pos.le
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hdup := Gamma_mul_Gamma_add_half v
  obtain ⟨hU, hV⟩ := pcfProduct_zero_pair_v hv
  rw [hU, hV]
  have hbeta := Gamma_mul_Gamma_eq_betaIntegral hv (show 0 < (1/2 : ℂ).re by norm_num)
  rw [Gamma_one_half_eq_sqrt] at hbeta
  have hpow : (2 : ℂ)^(1-2*v)*((2 : ℂ)^(v-1/2))^2 = 1 := by
    rw [pow_two, ← cpow_add _ _ h2, ← cpow_add _ _ h2]
    convert cpow_zero (2 : ℂ) using 1 <;> congr 1 <;> ring
  have hsc := sin_sq_add_cos_sq (π*v)
  generalize (2 : ℂ)^(v-1/2) = F at hpow ⊢
  generalize (2 : ℂ)^(1-2*v) = E at hdup hpow ⊢
  field_simp
  -- Eliminate the beta and duplication factors before the final square identity.
  have hg : Gamma (2*v)*betaIntegral v (1/2) = F^2 * Gamma v^2 := by
    apply mul_right_cancel₀ hG1
    calc _ = Gamma (2*v)*(Gamma v*(Real.sqrt π : ℂ)) := by rw [mul_assoc, mul_comm _ (Gamma (v+1/2)), ← hbeta]
         _ = F^2*Gamma v*(Gamma v*Gamma (v+1/2)) := by rw [hdup]; linear_combination -Gamma (2*v)*Gamma v*(Real.sqrt π : ℂ)*hpow
         _ = _ := by ring
  rw [hg]
  rw [hs2]
  rw [mul_comm (π : ℂ) v] at hsc
  linear_combination -F^2*Gamma v^2*π*hsc

/-- The normalized zeroth hyperbolic moment matches the cylinder-square initial value. -/
lemma pcfIntegral4_initial_value {a : ℂ} (ha : a.re < 1/2) :
    (2 : ℂ)^(3/2 : ℂ)/π*Gamma (1/2-a) *
      (∫ t : ℝ in Ioi 0, exp (2*a*t)/(Real.sqrt (Real.sinh (2*t)) : ℂ)) =
      (pcfU a 0)^2+(pcfUBar a 0)^2 := by
  have hv : 0 < (1/4-a/2).re := by simp; linarith
  have h := pcfProduct_zero_beta_v hv
  rw [show (2 : ℂ)*(1/4-a/2)=1/2-a by ring,
    show (1/2 : ℂ)-(1/2-a)=a by ring] at h
  rw [pcfIntegral4_base_beta]
  have h2 : (2 : ℂ)^(3/2 : ℂ)=2*(Real.sqrt 2 : ℂ) := by
    rw [show (3/2 : ℂ)=1+1/2 by norm_num, cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0), cpow_one,
      show (1/2 : ℂ)=((1/2 : ℝ) : ℂ) by norm_num,
      show (2 : ℂ)=((2 : ℝ) : ℂ) by norm_num,
      ← ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2), ← Real.sqrt_eq_rpow]
  rw [h2, ← h]
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  field_simp

/-- The normalized squared cylinder combination solves the symmetric-square equation. -/
lemma pcfIntegral4_product_isThirdOrderSolution (a : ℂ) :
    ODE.IsThirdOrderSolution (fun z : ℂ => z^2+4*a) (fun z => z)
      (fun z => (pcfU a z)^2+(pcfUBar a z)^2)
      (fun z => 2*(pcfU a z*pcfUDeriv a z+pcfUBar a z*pcfUBarDeriv a z))
      (fun z => 2*(z^2/4+a)*((pcfU a z)^2+(pcfUBar a z)^2)+
        2*((pcfUDeriv a z)^2+(pcfUBarDeriv a z)^2)) := by
  have hq (w : ℂ) : HasDerivAt (fun t : ℂ => t^2/4+a) (w/2) w := by
    exact ((((hasDerivAt_id w).pow 2).div_const 4).add_const a).congr_deriv (by
      simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
      ring)
  have hB : IsWeberSol a (pcfUBar a) (pcfUBarDeriv a) := fun z => by
    refine ⟨(hasDerivAt_pcfV a z).const_mul _, ?_⟩
    exact ((hasDerivAt_pcfVDeriv a z).const_mul (Gamma (1/2-a))).congr_deriv (by
      simp only [pcfUBar]
      ring)
  have hU := ODE.product_isThirdOrderSolution (isWeberSol_pcfU a) (isWeberSol_pcfU a) hq
  have hV := ODE.product_isThirdOrderSolution hB hB hq
  convert hU.add hV using 1 <;> funext z <;> ring


/-- Lowering the parameter identifies both initial derivatives, including
negative half-integral parameters of the barred solution. -/
lemma pcfIntegral4_deriv_zero_shift {a : ℂ} (ha : a.re < 1/2) :
    pcfUDeriv a 0 = -pcfU (a-1) 0 ∧ pcfUBarDeriv a 0 = -pcfUBar (a-1) 0 := by
  constructor
  · have h := pcfU_recurrence_sub a 0
    rw [(hasDerivAt_pcfU a 0).deriv] at h
    simp only [zero_div, zero_mul, sub_zero] at h
    linear_combination h
  · have h := pcfV_recurrence_sub a 0
    rw [(hasDerivAt_pcfV a 0).deriv] at h
    simp only [zero_div, zero_mul, sub_zero] at h
    have hg : (1/2:ℂ)-a ≠ 0 := by
      intro he
      have := congrArg Complex.re he
      simp at this
      linarith
    simp only [pcfUBarDeriv, pcfUBar]
    rw [show (1/2:ℂ)-(a-1)=(1/2-a)+1 by ring, Gamma_add_one _ hg]
    linear_combination Gamma (1/2-a)*h


/-- Initial values determine solutions of the Weber product equation. -/
lemma pcfProduct_eq_of_initial {a : ℂ} {y y1 y2 z z1 z2 : ℂ → ℂ}
    (hy : ODE.IsThirdOrderSolution (fun x => x^2+4*a) (fun x => x) y y1 y2)
    (hz : ODE.IsThirdOrderSolution (fun x => x^2+4*a) (fun x => x) z z1 z2)
    (h0 : y 0 = z 0) (h1 : y1 0 = z1 0) (h2 : y2 0 = z2 0) : y = z := by
  have hq (x : ℂ) : HasDerivAt (fun x : ℂ => x^2/4+a) (x/2) x := by
    exact ((((hasDerivAt_id x).pow 2).div_const 4).add_const a).congr_deriv (by
      simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
      ring)
  have hp {f f' g g' : ℂ → ℂ} (hf : IsWeberSol a f f') (hg : IsWeberSol a g g') :=
    ODE.product_isThirdOrderSolution hf hg hq
  have hp_eq : (fun x : ℂ => 4*(x^2/4+a)) = fun x => x^2+4*a := by funext x; ring
  have hq_eq : (fun x : ℂ => 2*(x/2)) = fun x => x := by funext x; ring
  simp only [hp_eq, hq_eq] at hp
  have hu := hp (isWeberSol_pcfEven a) (isWeberSol_pcfEven a)
  have hv := hp (isWeberSol_pcfEven a) (isWeberSol_pcfOdd a)
  have hw := hp (isWeberSol_pcfOdd a) (isWeberSol_pcfOdd a)
  apply ODE.thirdOrder_eq_of_initial hy hz hu hv hw (x₀ := 0) _ h0 h1 h2
  norm_num [ODE.thirdOrderWronskian, pcfEven_zero, pcfEvenDeriv_zero, pcfOdd_zero,
    pcfOddDeriv_zero]

/-- The squared cylinder combination has zero first derivative at the origin. -/
lemma pcfIntegral4_initial_deriv {a : ℂ} (ha : a.re < 1/2) :
    pcfU a 0 * pcfUDeriv a 0 + pcfUBar a 0 * pcfUBarDeriv a 0 = 0 := by
  let v : ℂ := 1/4-a/2
  have hv : 0 < v.re := by dsimp [v]; simp; linarith
  obtain ⟨hU, hB⟩ := pcfProduct_zero_pair_v hv
  obtain ⟨hU', hB'⟩ := pcfProduct_zero_pair_v (v:=v+1/2) (by simp; linarith)
  rw [show (1/2:ℂ)-2*v=a by dsimp [v]; ring] at hU hB
  rw [show (1/2:ℂ)-2*(v+1/2)=a-1 by dsimp [v]; ring,
    show (π:ℂ)*(v+1/2)=π*v+π/2 by ring, sin_add_pi_div_two] at hU'
  rw [show (1/2:ℂ)-2*(v+1/2)=a-1 by dsimp [v]; ring,
    show (π:ℂ)*(v+1/2)=π*v+π/2 by ring, cos_add_pi_div_two] at hB'
  rw [(pcfIntegral4_deriv_zero_shift ha).1, (pcfIntegral4_deriv_zero_shift ha).2,
    hU, hB, hU', hB']
  ring




/-- An exponential factor converts the singular kernel into the continuous tanh-weighted kernel. -/
lemma pcfIntegral4_exp_tanh (t : ℝ) :
    (1+exp (-2*(t : ℂ)))*(Real.tanh t : ℂ)=1-exp (-2*(t : ℂ)) := by
  have hr : (1+Real.exp (-2*t))*Real.tanh t=1-Real.exp (-2*t) := by
    have hc := (Real.cosh_pos t).ne'
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
    rw [Real.sinh_eq, Real.cosh_eq]
    simp only [show -2*t = -(t+t) by ring, show t*2 = t+t by ring, Real.exp_neg, Real.exp_add]
    have he := Real.exp_ne_zero t
    field_simp
    have he2 : Real.exp (2*t)=Real.exp t^2 := by rw [two_mul, Real.exp_add, pow_two]
    linear_combination -2*he2
  have hc := congrArg Complex.ofReal hr
  push_cast at hc
  simpa using hc

/-- The hyperbolic identity used when differentiating the first-moment primitive. -/
lemma pcfIntegral4_exp_coth {t : ℝ} (ht : 0 < t) :
    (1-exp (-2*(t : ℂ)))*(Real.cosh (2*t) : ℂ)/(Real.sinh (2*t) : ℂ)=
      (Real.tanh t : ℂ)+exp (-2*(t : ℂ)) := by
  have hr : (1-Real.exp (-2*t))*Real.cosh (2*t)/Real.sinh (2*t)=
      Real.tanh t+Real.exp (-2*t) := by
    have hc := (Real.cosh_pos t).ne'
    have hs := (Real.sinh_pos_iff.mpr (show 0 < 2*t by linarith)).ne'
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
    rw [Real.sinh_eq, Real.cosh_eq, Real.cosh_eq, Real.sinh_eq]
    simp only [show 2*t = t+t by ring, show -2*t = -(t+t) by ring, show t*2 = t+t by ring, Real.exp_neg, Real.exp_add]
    have he := Real.exp_ne_zero t
    field_simp
    ring
  have hc := congrArg Complex.ofReal hr
  push_cast at hc
  simpa using hc

/-- Multiplying the kernel by exp(-2t) decreases its parameter by one. -/
lemma pcfIntegral4_exp_shift (a : ℂ) (t : ℝ) :
    exp (-2*(t : ℂ))*pcfIntegral4Kernel a 0 t=pcfIntegral4Kernel (a-1) 0 t := by
  simp only [pcfIntegral4Kernel, zero_pow two_ne_zero, zero_div, zero_mul, add_zero]
  rw [← mul_div_assoc, ← exp_add]
  congr 2
  ring

/-- Integration by parts expresses the first hyperbolic moment through two zeroth moments. -/
lemma pcfIntegral4_first_moment {a : ℂ} (ha : a.re < 1/2) :
    pcfIntegral4Moment a 1 0 =
      2*a*pcfIntegral4Moment a 0 0+(1-2*a)*pcfIntegral4Moment (a-1) 0 0 := by
  let F (t : ℝ) := (1-exp (-2*(t : ℂ)))*pcfIntegral4Kernel a 0 t
  let g (t : ℝ) := 2*a*pcfIntegral4Kernel a 0 t+
    (1-2*a)*pcfIntegral4Kernel (a-1) 0 t-(Real.tanh t : ℂ)*pcfIntegral4Kernel a 0 t
  have hF : F = fun t : ℝ => (1+exp (-2*(t : ℂ)))*((Real.tanh t : ℂ)*pcfIntegral4Kernel a 0 t) := by
    funext t
    dsimp only [F]
    rw [← mul_assoc, pcfIntegral4_exp_tanh]
  have hcont : ContinuousWithinAt F (Ici 0) 0 := by
    rw [hF]
    exact (by fun_prop : Continuous fun t : ℝ => 1+exp (-2*(t : ℂ))).continuousWithinAt.mul
      (pcfIntegral4_tanh_kernel_continuous_zero a 0)
  have hd (t : ℝ) (ht : t ∈ Ioi 0) : HasDerivAt F (g t) t := by
    have hExp : HasDerivAt (fun u : ℝ => exp (-2*(u : ℂ)))
        (-2*exp (-2*(t : ℂ))) t := by
      convert (((hasDerivAt_id t).ofReal_comp.const_mul (-2 : ℂ)).cexp) using 1 <;> simp <;> ring
    have h := ((hasDerivAt_const t (1 : ℂ)).sub hExp).mul
      (pcfIntegral4_hasDerivAt_kernel_time a 0 ht)
    refine h.congr_deriv ?_
    simp only [zero_pow two_ne_zero, zero_div, zero_mul, add_zero, zero_sub, Pi.sub_apply]
    dsimp only [g]
    have hrat := pcfIntegral4_exp_coth ht
    have hshift := pcfIntegral4_exp_shift a t
    linear_combination -(pcfIntegral4Kernel a 0 t)*hrat + (1-2*a)*hshift
  have ha' : (a-1).re < 1/2 := by simp; linarith
  have hi0 : IntegrableOn (pcfIntegral4Kernel a 0) (Ioi 0) := by
    simpa using pcfIntegral4_moment_integrable ha 0 0
  have hi1 : IntegrableOn (pcfIntegral4Kernel (a-1) 0) (Ioi 0) := by
    simpa using pcfIntegral4_moment_integrable ha' 0 0
  have hit : IntegrableOn (fun t => (Real.tanh t : ℂ)*pcfIntegral4Kernel a 0 t) (Ioi 0) := by
    simpa using pcfIntegral4_moment_integrable ha 1 0
  have hig : IntegrableOn g (Ioi 0) := ((hi0.const_mul (2*a)).add (hi1.const_mul (1-2*a))).sub hit
  have ht : Tendsto F atTop (𝓝 0) := by
    have he : Tendsto (fun t : ℝ => exp (-2*(t : ℂ))) atTop (𝓝 0) := by
      have h := (continuous_ofReal.tendsto 0).comp
        (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-2 : ℝ) < 0)))
      change Tendsto (fun t : ℝ => (Real.exp (-2*t) : ℂ)) atTop (𝓝 0) at h
      refine h.congr' (Eventually.of_forall fun t => ?_)
      rw [ofReal_exp]
      congr 1
      push_cast
      ring
    have hk : Tendsto (pcfIntegral4Kernel a 0) atTop (𝓝 0) := by
      simpa using pcfIntegral4_moment_tendsto_zero ha 0 0
    simpa [F] using (tendsto_const_nhds.sub he).mul hk
  have hI := integral_Ioi_of_hasDerivAt_of_tendsto hcont hd hig ht
  simp only [F, ofReal_zero, mul_zero, exp_zero, sub_self, zero_mul, sub_zero] at hI
  simp only [g] at hI
  have hsub := integral_sub ((hi0.const_mul (2*a)).add (hi1.const_mul (1-2*a))) hit
  simp only [Pi.add_apply] at hsub
  rw [hsub, integral_add (hi0.const_mul (2*a)) (hi1.const_mul (1-2*a)),
    integral_const_mul, integral_const_mul] at hI
  simpa [pcfIntegral4Moment] using (sub_eq_zero.mp hI).symm

/-- The second initial value of the normalized cylinder square integral. -/
lemma pcfIntegral4_initial_second {a : ℂ} (ha : a.re < 1/2) :
    (2:ℂ)^(3/2:ℂ)/π*Gamma (1/2-a)*pcfIntegral4Moment a 1 0 =
      2*a*((pcfU a 0)^2+(pcfUBar a 0)^2)+
        2*((pcfUDeriv a 0)^2+(pcfUBarDeriv a 0)^2) := by
  let C (b : ℂ) := (2:ℂ)^(3/2:ℂ)/π*Gamma (1/2-b)
  have hM (b : ℂ) (hb : b.re < 1/2) :
      C b * pcfIntegral4Moment b 0 0 = (pcfU b 0)^2+(pcfUBar b 0)^2 := by
    simpa only [C, pcfIntegral4Moment, pcfIntegral4Kernel, pow_zero, one_mul,
      zero_pow (by norm_num : 2 ≠ 0), zero_div, zero_mul, add_zero]
      using pcfIntegral4_initial_value hb
  have hg : (1/2:ℂ)-a ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    simp at this
    linarith
  have hC : C a*(1-2*a) = 2*C (a-1) := by
    dsimp [C]
    rw [show (1/2:ℂ)-(a-1)=(1/2-a)+1 by ring, Gamma_add_one _ hg]
    ring
  have hrec := congrArg (fun w => C a*w) (pcfIntegral4_first_moment ha)
  rw [(pcfIntegral4_deriv_zero_shift ha).1, (pcfIntegral4_deriv_zero_shift ha).2,
    neg_sq, neg_sq]
  linear_combination hrec + 2*a*hM a ha +
    2*hM (a-1) (by simp; linarith) + pcfIntegral4Moment (a-1) 0 0*hC

/-- DLMF 12.12.4 from the product ODE and its three initial values. -/
@[dlmf 12.12.E4]
theorem pcf_integral_4 {a : ℂ} (ha : a.re < 1/2) (z : ℂ) :
    HasIntegralAtTop (fun t : ℝ => 2^(3/2:ℂ)/π*Gamma (1/2-a)*
      exp (2*a*t+z^2/2*Real.tanh t)/(Real.sqrt (Real.sinh (2*t)):ℂ)) 0
        ((pcfU a z)^2+(pcfUBar a z)^2) := by
  let C : ℂ := (2:ℂ)^(3/2:ℂ)/π*Gamma (1/2-a)
  have he := pcfProduct_eq_of_initial
    ((pcfIntegral4_isThirdOrderSolution ha).const_mul C)
    (pcfIntegral4_product_isThirdOrderSolution a)
    (by simpa only [C, pcfIntegral4Moment, pcfIntegral4Kernel, pow_zero, one_mul,
        zero_pow (by norm_num : 2 ≠ 0), zero_div, zero_mul, add_zero]
      using pcfIntegral4_initial_value ha)
    (by simp only [zero_mul, pcfIntegral4_initial_deriv ha, mul_zero])
    (by simpa only [C, zero_pow (by norm_num : 2 ≠ 0), zero_mul, add_zero, zero_div, zero_add]
      using pcfIntegral4_initial_second ha)
  have hv : (∫ t : ℝ in Ioi 0, (2:ℂ)^(3/2:ℂ)/π*Gamma (1/2-a)*
      exp (2*a*t+z^2/2*Real.tanh t)/(Real.sqrt (Real.sinh (2*t)):ℂ)) =
        (pcfU a z)^2+(pcfUBar a z)^2 := by
    rw [← congrFun he z]
    simp only [pcfIntegral4Moment, pow_zero, one_mul, C, pcfIntegral4Kernel,
      mul_div_assoc, integral_const_mul]
  unfold HasIntegralAtTop
  rw [← hv]
  exact intervalIntegral_tendsto_integral_Ioi 0 (pcf_integral_4_integrable ha z) tendsto_id

end DLMF.Confluent
