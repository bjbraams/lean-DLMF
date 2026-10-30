/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ExpIntegrals.AnalyticProperties

/-!
# Logarithmic continuation and boundary values, DLMF §§6.4–6.5

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

/-- E₁ on the logarithmic plane. -/
@[dlmf 6.4.E1]
def expIntE1OnLog (w : ℂ) : ℂ :=
  expIntEin (exp w) - w - Real.eulerMascheroniConstant

/-- Cosine integral on the logarithmic plane. -/
def cosIntOnLog (w : ℂ) : ℂ :=
  -cosIntCin (exp w) + w + Real.eulerMascheroniConstant

/-- Hyperbolic cosine integral on the logarithmic plane. -/
def coshIntOnLog (w : ℂ) : ℂ :=
  coshInt (exp w) - log (exp w) + w

/-- Continued auxiliary f. -/
def expIntAuxFOnLog (w : ℂ) : ℂ :=
  cosIntOnLog w * sin (exp w) - sinIntTail (exp w) * cos (exp w)

/-- Continued auxiliary g. -/
def expIntAuxGOnLog (w : ℂ) : ℂ :=
  -cosIntOnLog w * cos (exp w) - sinIntTail (exp w) * sin (exp w)

/-- Identity under the stated parameter and domain assumptions: `expIntE1OnLog (log z) =
genExpIntE 1 z`. -/
@[dlmf 6.4.E1]
theorem expIntE1OnLog_principal {z : ℂ} (hz : z ≠ 0) :
    expIntE1OnLog (log z) = genExpIntE 1 z := by
  rw [expIntE1OnLog, Complex.exp_log hz, expIntE1_eq_Ein_complex hz]

/-- Identity under the stated parameter and domain assumptions: `expIntE1OnLog (w+2*m*π*I) =
expIntE1OnLog w - 2*m*π*I`. -/
@[dlmf 6.4.E2]
theorem expIntE1OnLog_monodromy (w : ℂ) (m : ℤ) :
    expIntE1OnLog (w+2*m*π*I) = expIntE1OnLog w - 2*m*π*I := by
  have he : exp (w+2*m*π*I)=exp w := by
    rw [Complex.exp_add, show (2:ℂ)*m*π*I=(m:ℂ)*(2*π*I) by ring,
      Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp only [expIntE1OnLog, he]
  ring

/-- Identity under the stated parameter and domain assumptions: `expIntE1OnLog (w+ε*π*I) =
expIntEin (-exp w)-w-Real.eulerMascheroniConstant-ε*π*I`. -/
@[dlmf 6.4.E3]
theorem expIntE1OnLog_halfTurn (w : ℂ) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    expIntE1OnLog (w+ε*π*I) = expIntEin (-exp w)-w-Real.eulerMascheroniConstant-ε*π*I := by
  have he : exp (w+ε*π*I) = -exp w := by
    rcases hε with rfl | rfl <;> simp [Complex.exp_add, Complex.exp_pi_mul_I,
      show (-1:ℂ)*π*I=-(π*I) by ring, Complex.exp_neg]
  simp only [expIntE1OnLog, he]
  ring

/-- Identity under the stated parameter and domain assumptions: `cosIntOnLog (w+ε*π*I) =
cosIntOnLog w + ε*π*I`. -/
@[dlmf 6.4.E4]
theorem cosIntOnLog_halfTurn (w : ℂ) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    cosIntOnLog (w+ε*π*I) = cosIntOnLog w + ε*π*I := by
  have he : exp (w+ε*π*I) = -exp w := by
    rcases hε with rfl | rfl <;> simp [Complex.exp_add, Complex.exp_pi_mul_I,
      show (-1:ℂ)*π*I=-(π*I) by ring, Complex.exp_neg]
  simp only [cosIntOnLog, he, cosIntCin_even]
  ring

/-- Identity under the stated parameter and domain assumptions: `coshIntOnLog (w+ε*π*I) =
coshIntOnLog w + ε*π*I`. -/
@[dlmf 6.4.E5]
theorem coshIntOnLog_halfTurn (w : ℂ) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    coshIntOnLog (w+ε*π*I) = coshIntOnLog w + ε*π*I := by
  have he : exp (w+ε*π*I) = -exp w := by
    rcases hε with rfl | rfl <;> simp [Complex.exp_add, Complex.exp_pi_mul_I,
      show (-1:ℂ)*π*I=-(π*I) by ring, Complex.exp_neg]
  have hpar (z : ℂ) :
      (∑' k : ℕ, (-z)^(2*k+2)/((2*k+2).factorial*(2*k+2:ℂ))) =
        ∑' k : ℕ, z^(2*k+2)/((2*k+2).factorial*(2*k+2:ℂ)) := by
    apply tsum_congr
    intro k
    rw [neg_pow z, show (-1:ℂ)^(2*k+2)=1 by simp [pow_add, pow_mul], one_mul]
  simp only [coshIntOnLog, coshInt, he, hpar]
  ring

/-- Identity under the stated parameter and domain assumptions: `expIntAuxFOnLog (w+ε*π*I) = π*exp
(-ε*I*exp w) - expIntAuxFOnLog w`. -/
@[dlmf 6.4.E6]
theorem expIntAuxFOnLog_halfTurn (w : ℂ) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    expIntAuxFOnLog (w+ε*π*I) = π*exp (-ε*I*exp w) - expIntAuxFOnLog w := by
  have he : exp (w+ε*π*I)=-exp w := by
    rcases hε with rfl | rfl <;> simp [Complex.exp_add, Complex.exp_pi_mul_I,
      show (-1:ℂ)*π*I=-(π*I) by ring, Complex.exp_neg]
  have hc := cosIntOnLog_halfTurn w hε
  have hexp : exp (-ε*I*exp w)=cos (exp w)-ε*I*sin (exp w) := by
    rw [show -(ε:ℂ)*I*exp w=(-ε*exp w)*I by ring, Complex.exp_mul_I]
    rcases hε with rfl | rfl <;> simp [mul_comm, sub_eq_add_neg]
  simp only [expIntAuxFOnLog, expIntAuxGOnLog, he, hc, sinInt_odd,
    Complex.sin_neg, Complex.cos_neg, sinIntTail, sinInt_odd]
  rw [hexp]
  rcases hε with rfl | rfl <;> norm_num <;> ring_nf <;> simp [I_sq] <;> ring

/-- Identity under the stated parameter and domain assumptions: `expIntAuxGOnLog (w+ε*π*I) =
-ε*π*I*exp (-ε*I*exp w)+expIntAuxGOnLog w`. -/
@[dlmf 6.4.E7]
theorem expIntAuxGOnLog_halfTurn (w : ℂ) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    expIntAuxGOnLog (w+ε*π*I) = -ε*π*I*exp (-ε*I*exp w)+expIntAuxGOnLog w := by
  have he : exp (w+ε*π*I)=-exp w := by
    rcases hε with rfl | rfl <;> simp [Complex.exp_add, Complex.exp_pi_mul_I,
      show (-1:ℂ)*π*I=-(π*I) by ring, Complex.exp_neg]
  have hc := cosIntOnLog_halfTurn w hε
  have hexp : exp (-ε*I*exp w)=cos (exp w)-ε*I*sin (exp w) := by
    rw [show -(ε:ℂ)*I*exp w=(-ε*exp w)*I by ring, Complex.exp_mul_I]
    rcases hε with rfl | rfl <;> simp [mul_comm, sub_eq_add_neg]
  simp only [expIntAuxFOnLog, expIntAuxGOnLog, he, hc, sinInt_odd,
    Complex.sin_neg, Complex.cos_neg, sinIntTail, sinInt_odd]
  rw [hexp]
  rcases hε with rfl | rfl <;> norm_num <;> ring_nf <;> simp [I_sq] <;> ring

/-- The map `(fun y : ℝ => genExpIntE 1 (-x+ε*y*I))` tends to `(𝓝 (-(Real.expIntEi x : ℂ)-ε*π*I))`
along `(𝓝[>] 0)`. -/
@[dlmf 6.5.E1]
theorem expIntE1_negative_boundary {x : ℝ} (hx : 0 < x) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    Tendsto (fun y : ℝ => genExpIntE 1 (-x+ε*y*I)) (𝓝[>] 0) (𝓝 (-(Real.expIntEi x : ℂ)-ε*π*I)) := by
  have hEin : expIntEin (-(x:ℂ))-(Real.log x:ℂ)-(Real.eulerMascheroniConstant:ℂ)= -(Real.expIntEi x:ℂ) := by
    rw [Real.expIntEi,show -(x:ℂ)=(-x:ℝ) by simp,expIntEin_ofReal]
    simp only [abs_of_pos hx,Complex.ofReal_re,Complex.ofReal_neg]
    push_cast
    ring
  have hf : Tendsto (fun y : ℝ => -(x:ℂ)+(ε:ℂ)*y*I) (𝓝[>] 0) (𝓝 (-(x:ℂ))) := by
    have hc : ContinuousAt (fun y : ℝ => -(x:ℂ)+(ε:ℂ)*y*I) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hlog : Tendsto (fun y : ℝ => log (-(x:ℂ)+(ε:ℂ)*y*I)) (𝓝[>] 0)
      (𝓝 ((Real.log x:ℂ)+ε*π*I)) := by
    rcases hε with rfl | rfl
    · have ht : Tendsto (fun y : ℝ => -(x:ℂ)+(1:ℂ)*y*I) (𝓝[>] 0)
          (𝓝[{w : ℂ | 0≤w.im}] (-(x:ℂ))) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨by simpa only [Complex.ofReal_neg,Complex.ofReal_one] using hf,?_⟩
        filter_upwards [self_mem_nhdsWithin] with y hy
        simp only [one_mul,add_im,neg_im,ofReal_im,mul_I_im,ofReal_re,neg_zero,zero_add]
        exact hy.le
      have hh := (tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
        (by simpa using (neg_neg_of_pos hx)) (by simp) (z:= -(x:ℂ))).comp ht
      simpa [Function.comp_def,Complex.norm_real,Real.norm_of_nonneg hx.le] using hh
    · have ht : Tendsto (fun y : ℝ => -(x:ℂ)+(-1:ℂ)*y*I) (𝓝[>] 0)
          (𝓝[{w : ℂ | w.im<0}] (-(x:ℂ))) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨by simpa only [Complex.ofReal_neg,Complex.ofReal_one] using hf,?_⟩
        filter_upwards [self_mem_nhdsWithin] with y hy
        simp only [neg_one_mul,add_im,neg_im,ofReal_im,mul_I_im,neg_re,ofReal_re,neg_zero,zero_add]
        exact neg_neg_of_pos hy
      have hh := (tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero
        (by simpa using (neg_neg_of_pos hx)) (by simp) (z:= -(x:ℂ))).comp ht
      simpa [Function.comp_def,Complex.norm_real,Real.norm_of_nonneg hx.le,sub_eq_add_neg] using hh
  have hlim := ((expIntEin_entire.continuous.tendsto (-(x:ℂ))).comp hf).sub hlog
    |>.sub_const (Real.eulerMascheroniConstant:ℂ)
  have hvalue : expIntEin (-(x:ℂ))-((Real.log x:ℂ)+ε*π*I)-Real.eulerMascheroniConstant=
      -(Real.expIntEi x:ℂ)-ε*π*I := by linear_combination hEin
  rw [hvalue] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  symm
  apply expIntE1_eq_Ein_complex
  have heps : (ε:ℂ).im=0 := Complex.ofReal_im ε
  intro hz
  have hr := congrArg Complex.re hz
  simp [Complex.mul_re,Complex.mul_im] at hr
  linarith

/-- Identity under the stated parameter and domain assumptions: `(Real.expIntEi x : ℂ) =
-(expIntE1OnLog (Real.log x+π*I)+expIntE1OnLog (Real.log x-π*I))/2`. -/
@[dlmf 6.5.E2]
theorem expIntEi_boundary_average {x : ℝ} (hx : 0 < x) :
    (Real.expIntEi x : ℂ) = -(expIntE1OnLog (Real.log x+π*I)+expIntE1OnLog (Real.log x-π*I))/2 := by
  have h1 := expIntE1OnLog_halfTurn (Real.log x:ℂ) (ε:=1) (Or.inl rfl)
  have h2 := expIntE1OnLog_halfTurn (Real.log x:ℂ) (ε:=-1) (Or.inr rfl)
  have hxexp : exp (Real.log x:ℂ)=(x:ℂ) := by rw [← Complex.ofReal_exp, Real.exp_log hx]
  simp only [Complex.ofReal_one, Complex.ofReal_neg, one_mul, neg_one_mul] at h1 h2
  rw [hxexp] at h1 h2
  rw [show (Real.log x:ℂ)+(-π*I)=(Real.log x:ℂ)-π*I by ring] at h2
  have hr : (Real.expIntEi x:ℂ)=(Real.eulerMascheroniConstant:ℂ)+Real.log x-
      DLMF.Confluent.expIntEin (-x) := by
    rw [Real.expIntEi]
    have hEin := expIntEin_ofReal (-x)
    simp only [Complex.ofReal_neg] at hEin
    rw [hEin]
    simp only [Complex.ofReal_re, abs_of_pos hx]
    push_cast
    ring
  rw [hr]
  linear_combination (h1+h2)/2

/-- Even and odd parts of Ein give the hyperbolic integrals. -/
theorem expIntEin_hyperbolic (z : ℂ) :
    expIntEin z=sinhInt z+cosIntCin (I*z) ∧
    expIntEin (-z)= -sinhInt z+cosIntCin (I*z) := by
  have hm := expIntEin_mul_I (I*z)
  rw [show I*(I*z)= -z by simp only [←mul_assoc,Complex.I_mul_I,neg_one_mul],sinInt_mul_I] at hm
  have hp := expIntEin_mul_I (-(I*z))
  rw [show I*(-(I*z))=z by ring_nf; simp,cosIntCin_even,sinInt_odd,sinInt_mul_I] at hp
  constructor
  · linear_combination (norm := ring_nf) hp <;> simp [I_sq] <;> ring
  · linear_combination (norm := ring_nf) hm <;> simp [I_sq] <;> ring

/-- Real Ei in terms of the entire Ein normalization. -/
theorem expIntEi_eq_Ein {x : ℝ} (hx : 0<x) :
    (Real.expIntEi x:ℂ)=(Real.eulerMascheroniConstant:ℂ)+Real.log x-expIntEin (-(x:ℂ)) := by
  rw [Real.expIntEi,show -(x:ℂ)=(-x:ℝ) by simp,expIntEin_ofReal]
  simp only [abs_of_pos hx,Complex.ofReal_re]
  push_cast
  ring

/-- Identity under the stated parameter and domain assumptions: `((Real.expIntEi x : ℂ)+genExpIntE
1 x)/2 = sinhInt x ∧ sinhInt x = -I*sinInt (I*x)`. -/
@[dlmf 6.5.E3]
theorem sinhInt_eq_Ei {x : ℝ} (hx : 0 < x) :
    ((Real.expIntEi x : ℂ)+genExpIntE 1 x)/2 = sinhInt x ∧ sinhInt x = -I*sinInt (I*x) := by
  have hp := expIntEin_hyperbolic (x:ℂ)
  have he := expIntE1_eq_Ein_complex (Complex.ofReal_ne_zero.mpr hx.ne')
  rw [expIntEi_eq_Ein hx,Complex.ofReal_log hx.le]
  refine ⟨?_,?_⟩
  · rw [he,hp.1,hp.2]
    ring
  · rw [sinInt_mul_I]
    ring_nf
    simp [I_sq]

/-- Identity under the stated parameter and domain assumptions: `((Real.expIntEi x : ℂ)-genExpIntE
1 x)/2 = coshInt x ∧ coshInt x = cosInt (I*x)-π*I/2`. -/
@[dlmf 6.5.E4]
theorem coshInt_eq_Ei {x : ℝ} (hx : 0 < x) :
    ((Real.expIntEi x : ℂ)-genExpIntE 1 x)/2 = coshInt x ∧ coshInt x = cosInt (I*x)-π*I/2 := by
  have hp := expIntEin_hyperbolic (x:ℂ)
  have he := expIntE1_eq_Ein_complex (Complex.ofReal_ne_zero.mpr hx.ne')
  have hc := cosIntCin_mul_I (x:ℂ)
  rw [expIntEi_eq_Ein hx,Complex.ofReal_log hx.le]
  constructor
  · rw [he,hp.1,hp.2,hc]
    unfold coshInt
    ring
  · rw [cosInt, (log_quarter_turn hx).1]
    rw [hc]
    unfold coshInt
    ring

/-- `E₁(z(t-c)) → 0` as `t → ∞`, for `z ≠ 0` in the closed right half-plane. -/
theorem tendsto_expIntE1_mul_sub {z : ℂ} (hz0 : z ≠ 0) (hz : 0 ≤ z.re) (c : ℂ) :
    Tendsto (fun t : ℝ => genExpIntE 1 (z*(t-c))) atTop (𝓝 0) := by
  have harg : |arg z| ≤ π/2 := Complex.abs_arg_le_pi_div_two_iff.mpr hz
  set β : ℝ := -(arg z/2)
  have hβ : |β| < π/2 := by
    simp only [β, abs_neg, abs_div, abs_two]; linarith [Real.pi_pos]
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  set u : ℂ := exp ((arg z/2 : ℝ)*I)
  have hu : ‖u‖ = 1 := norm_exp_ofReal_mul_I _
  have hure : (1/2:ℝ) < u.re := by
    simp only [u, exp_ofReal_mul_I_re]
    have h1 : Real.cos (π/4) ≤ Real.cos (arg z/2) := by
      rw [← Real.cos_abs (arg z/2)]
      apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos])
      rw [abs_div, abs_two]; linarith
    rw [Real.cos_pi_div_four] at h1
    have : (1:ℝ) < Real.sqrt 2 := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  have hray : Tendsto (fun t : ℝ => z*(t-c)) atTop (rotSectorAtTop (1/2) β) := by
    apply tendsto_rotSectorAtTop_of_mul
    have h := (tendsto_ray_sectorAtTop (-c*‖z‖) u hu (by norm_num) hure).comp
      (tendsto_id.const_mul_atTop hr)
    have hz' : z = ‖z‖*exp (arg z*I) := (norm_mul_exp_arg_mul_I z).symm
    have key : z*exp ((β:ℂ)*I) = ‖z‖*u := by
      nth_rewrite 1 [hz']
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      simp only [β]; push_cast; ring
    refine h.congr fun t => ?_
    simp only [Function.comp_apply, id]
    rw [show z*((t:ℂ)-c)*exp ((β:ℂ)*I) = ((t:ℂ)-c)*(z*exp ((β:ℂ)*I)) by ring, key]
    push_cast; ring
  have hU := (tendsto_kummerU_rotSectorAtTop (a := 1) 1 (by norm_num) (by norm_num) hβ).comp hray
  have hU' := hU.norm.mul_const (Real.exp (z*c).re)
  rw [norm_zero, zero_mul] at hU'
  refine squeeze_zero_norm' ?_ hU'
  have hn : ∀ᶠ t : ℝ in atTop, z*(t-c) ≠ 0 := by
    have := (tendsto_norm_sectorAtTop (1/2)).comp ((tendsto_rotSectorAtTop _ _).comp hray)
    filter_upwards [this.eventually_gt_atTop 0] with t ht h0
    simp [h0] at ht
  filter_upwards [hn, eventually_ge_atTop 0] with t ht ht0
  rw [genExpIntE_eq_exp_mul_kummerU 1 ht, show (2:ℂ)-1=1 by norm_num, norm_mul, Complex.norm_exp,
    Function.comp_apply, mul_comm]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  have : (-(z*((t:ℂ)-c))).re = -(z.re*t) + (z*c).re := by simp [mul_sub]; ring
  rw [this]; nlinarith

/-- `(E₁ on the log plane)' = -exp(-e^w)`. -/
theorem hasDerivAt_expIntE1OnLog (w : ℂ) : HasDerivAt expIntE1OnLog (-exp (-exp w)) w := by
  have h := (((hasDerivAt_expIntEin_complex (Complex.exp_ne_zero w)).comp w
    (Complex.hasDerivAt_exp w)).sub (hasDerivAt_id w)).sub_const (Real.eulerMascheroniConstant:ℂ)
  refine h.congr_deriv ?_
  have he : exp w ≠ 0 := Complex.exp_ne_zero w
  field_simp
  ring

/-- The shifted Laplace integral `∫_x^∞ e^{-zt}/(t-c) dt`, on the logarithmic plane, for `z ≠ 0`
in the closed right half-plane. -/
theorem hasIntegralAtTop_exp_neg_mul_div_sub {z : ℂ} (hz0 : z ≠ 0) (hz : 0 ≤ z.re) (c : ℂ) (x : ℝ)
    (hc : ∀ t : ℝ, x ≤ t → (t:ℂ)-c ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => exp (-z*t)/(t-c)) x
      (exp (-z*c)*expIntE1OnLog (log z+log (x-c))) := by
  have hd : ∀ t : ℝ, x ≤ t → HasDerivAt (fun t : ℝ => -exp (-z*c)*expIntE1OnLog (log z+log (t-c)))
      (exp (-z*t)/(t-c)) t := by
    intro t ht
    have hl := ((Complex.hasDerivAt_log (hc t ht)).comp (t:ℂ) ((hasDerivAt_id (t:ℂ)).sub_const c)).const_add (log z)
    have h1 := ((hasDerivAt_expIntE1OnLog _).comp (t:ℂ) hl).comp_ofReal.const_mul (-exp (-z*c))
    refine h1.congr_deriv ?_
    have hne := slitPlane_ne_zero (hc t ht)
    simp only [id, Function.comp_apply, mul_one]
    rw [Complex.exp_add, Complex.exp_log hz0, Complex.exp_log hne,
      show -(z*((t:ℂ)-c)) = -z*t+z*c by ring, Complex.exp_add]
    have : exp (-z*c)*exp (z*c) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
    have this2 : exp (-z*c) = exp (-(z*c)) := by ring_nf
    field_simp
    linear_combination this - exp (z*c)*this2
  have hcont : ContinuousOn (fun t : ℝ => exp (-z*t)/(t-c)) (Ici x) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => slitPlane_ne_zero (hc t ht)
  have hl : Tendsto (fun t : ℝ => -exp (-z*c)*expIntE1OnLog (log z+log (t-c))) atTop (𝓝 0) := by
    have h := (tendsto_expIntE1_mul_sub hz0 hz c).const_mul (-exp (-z*c))
    rw [mul_zero] at h
    refine h.congr' ?_
    have harg : |arg z| ≤ π/2 := Complex.abs_arg_le_pi_div_two_iff.mpr hz
    filter_upwards [eventually_gt_atTop (c.re), eventually_ge_atTop x] with t ht htx
    have hre : 0 < ((t:ℂ)-c).re := by simp; linarith
    have ha := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre))
    have hne : (t:ℂ)-c ≠ 0 := fun h0 => by rw [h0] at hre; simp at hre
    rw [← Complex.log_mul hz0 hne (by
      constructor <;> linarith [abs_le.mp harg, Real.pi_pos]), expIntE1OnLog_principal (mul_ne_zero hz0 hne)]
  have h := hasIntegralAtTop_of_hasDerivAt_of_tendsto hd hcont hl
  simpa using h

/-- Laplace representations of the auxiliary functions `f` and `g` on the closed right
half-plane minus the origin, as improper integrals. -/
theorem expIntAux_laplace_hasIntegralAtTop {z : ℂ} (hz0 : z ≠ 0) (hz : 0 ≤ z.re) :
    HasIntegralAtTop (fun t : ℝ => exp (-z*t)/((t:ℂ)^2+1)) 0 (expIntAuxF z) ∧
    HasIntegralAtTop (fun t : ℝ => (t:ℂ)*exp (-z*t)/((t:ℂ)^2+1)) 0 (expIntAuxG z) := by
  have hs1 : ∀ t : ℝ, 0 ≤ t → (t:ℂ)-I ∈ slitPlane := fun t _ => by right; simp
  have hs2 : ∀ t : ℝ, 0 ≤ t → (t:ℂ)-(-I) ∈ slitPlane := fun t _ => by right; simp
  have hn1 (t : ℝ) : (t:ℂ)-I ≠ 0 := fun h => by have := congrArg Complex.im h; simp at this
  have hn2 (t : ℝ) : (t:ℂ)+I ≠ 0 := fun h => by have := congrArg Complex.im h; simp at this
  have hi1 : ∀ R, (0:ℝ) ≤ R → IntervalIntegrable (fun t : ℝ => exp (-z*t)/(t-I)) volume 0 R :=
    fun R _ => (Continuous.div (by fun_prop) (by fun_prop) hn1).intervalIntegrable _ _
  have hi2 : ∀ R, (0:ℝ) ≤ R → IntervalIntegrable (fun t : ℝ => exp (-z*t)/(t-(-I))) volume 0 R :=
    fun R _ => (Continuous.div (by fun_prop) (by fun_prop) fun t => by
      rw [sub_neg_eq_add]; exact hn2 t).intervalIntegrable _ _
  have h1 := hasIntegralAtTop_exp_neg_mul_div_sub hz0 hz I 0 hs1
  have h2 := hasIntegralAtTop_exp_neg_mul_div_sub hz0 hz (-I) 0 hs2
  have hf (t : ℝ) (F : ℂ) : F/((t:ℂ)^2+1) = 1/(2*I)*(F/(t-I)+(-1)*(F/(t-(-I)))) ∧
      (t:ℂ)*F/((t:ℂ)^2+1) = 1/2*(F/(t-I)+F/(t-(-I))) := by
    have hq : (t:ℂ)^2+1 = (t-I)*(t+I) := by ring_nf; rw [I_sq]; ring
    rw [hq, sub_neg_eq_add]
    have := hn1 t; have := hn2 t
    constructor
    · field_simp; ring_nf
    · field_simp; ring
  -- the common value
  have hEm : expIntE1OnLog (log z+log (((0:ℝ):ℂ)-I)) = cosIntCin z-I*sinInt z-log z+π*I/2-Real.eulerMascheroniConstant := by
    have he := expIntEin_mul_I (-z)
    rw [cosIntCin_even, sinInt_odd] at he
    rw [expIntE1OnLog, Complex.exp_add, Complex.exp_log hz0, show ((0:ℝ):ℂ)-I = -I by simp,
      Complex.exp_log (neg_ne_zero.mpr I_ne_zero), log_neg_I, show z*(-I) = I*(-z) by ring, he]
    ring
  have hEp : expIntE1OnLog (log z+log (((0:ℝ):ℂ)-(-I))) = cosIntCin z+I*sinInt z-log z-π*I/2-Real.eulerMascheroniConstant := by
    rw [expIntE1OnLog, Complex.exp_add, Complex.exp_log hz0, show ((0:ℝ):ℂ)-(-I) = I by simp,
      Complex.exp_log I_ne_zero, log_I, mul_comm z I, expIntEin_mul_I]
    ring
  have hsin : sin z = (exp (-z*I)-exp (z*I))*I/2 := by rw [Complex.sin]
  have hcos : cos z = (exp (z*I)+exp (-z*I))/2 := by rw [Complex.cos]
  constructor
  · have h := ((h1.add (h2.const_mul (-1)) hi1 (fun R hR => (hi2 R hR).const_mul _)).const_mul (1/(2*I))).congr
      fun t _ => ((hf t _).1).symm
    convert h using 1
    rw [hEm, hEp, expIntAuxF, cosInt, sinIntTail, hsin, hcos, show -z*I = -(z*I) by ring,
      show -z*(-I) = z*I by ring]
    field_simp
    ring_nf; rw [I_sq]; ring
  · have h := ((h1.add h2 hi1 hi2).const_mul (1/2)).congr fun t _ => ((hf t _).2).symm
    convert h using 1
    rw [hEm, hEp, expIntAuxG, cosInt, sinIntTail, hsin, hcos, show -z*I = -(z*I) by ring,
      show -z*(-I) = z*I by ring]
    field_simp
    ring_nf

end DLMF.Confluent
