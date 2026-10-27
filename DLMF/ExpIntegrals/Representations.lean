/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ExpIntegrals.Continuation
public import DLMF.IncompleteGamma.FractionTools

/-!
# Exponential integral representations and inequalities, DLMF §§6.7–6.9

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

/-- The Fourier-type ray integral `∫_x^∞ e^{it}/(t-c) dt = e^{ic} E₁(-i(x-c))`. -/
theorem hasIntegralAtTop_exp_I_div_sub (c : ℂ) (x : ℝ)
    (hc : ∀ t : ℝ, x ≤ t → -I*(t-c) ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => exp (I*t)/(t-c)) x (exp (I*c)*genExpIntE 1 (-I*(x-c))) := by
  have hd : ∀ t : ℝ, x ≤ t → HasDerivAt (fun t : ℝ => -exp (I*c)*genExpIntE 1 (-I*(t-c)))
      (exp (I*t)/(t-c)) t := by
    intro t ht
    have h1 := (hasDerivAt_genExpIntE 1 (hc t ht)).comp (t:ℂ)
      (((hasDerivAt_id (t:ℂ)).sub_const c).const_mul (-I))
    have h2 := (h1.comp_ofReal).const_mul (-exp (I*c))
    refine h2.congr_deriv ?_
    have hne : (t:ℂ)-c ≠ 0 := by
      intro h0; have := hc t ht; rw [h0, mul_zero] at this; exact slitPlane_ne_zero this rfl
    rw [show (1:ℂ)-1 = 0 by norm_num, genExpIntE_zero_eq]
    rw [show -(-I*((t:ℂ)-c)) = I*t+(-(I*c)) by ring, Complex.exp_add, Complex.exp_neg]
    have : exp (I*c) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  have hcont : ContinuousOn (fun t : ℝ => exp (I*t)/(t-c)) (Ici x) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht h0 => ?_
    have := hc t ht; rw [h0, mul_zero] at this; exact slitPlane_ne_zero this rfl
  have hl : Tendsto (fun t : ℝ => -exp (I*c)*genExpIntE 1 (-I*(t-c))) atTop (𝓝 0) := by
    have h := (tendsto_expIntE1_mul_I_add_ofReal (-c) (ε := -1) (Or.inr rfl)).const_mul (-exp (I*c))
    rw [mul_zero] at h
    refine h.congr fun t => ?_
    push_cast; ring_nf
  have h := hasIntegralAtTop_of_hasDerivAt_of_tendsto hd hcont hl
  simpa using h

/-- The Laplace-type ray integral `∫_x^∞ e^{-t}/(t-c) dt = e^{-c} E₁(x-c)`. -/
theorem hasIntegralAtTop_exp_neg_div_sub (c : ℂ) (x : ℝ)
    (hc : ∀ t : ℝ, x ≤ t → (t:ℂ)-c ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => exp (-t : ℂ)/(t-c)) x (exp (-c)*genExpIntE 1 (x-c)) := by
  have hd : ∀ t : ℝ, x ≤ t → HasDerivAt (fun t : ℝ => -exp (-c)*genExpIntE 1 ((t:ℂ)-c))
      (exp (-t : ℂ)/(t-c)) t := by
    intro t ht
    have h1 := (hasDerivAt_genExpIntE 1 (hc t ht)).comp (t:ℂ) ((hasDerivAt_id (t:ℂ)).sub_const c)
    have h2 := (h1.comp_ofReal).const_mul (-exp (-c))
    refine h2.congr_deriv ?_
    rw [show (1:ℂ)-1 = 0 by norm_num, genExpIntE_zero_eq]
    rw [show -((t:ℂ)-c) = -t+c by ring, Complex.exp_add]
    have : exp (-c)*exp c = 1 := by rw [← Complex.exp_add]; simp
    have hne : (t:ℂ)-c ≠ 0 := fun h0 => slitPlane_ne_zero (hc t ht) h0
    field_simp
    linear_combination this
  have hcont : ContinuousOn (fun t : ℝ => exp (-t : ℂ)/(t-c)) (Ici x) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht h0 => ?_
    have := hc t ht; rw [h0] at this; exact slitPlane_ne_zero this rfl
  have hl : Tendsto (fun t : ℝ => -exp (-c)*genExpIntE 1 ((t:ℂ)-c)) atTop (𝓝 0) := by
    have h := (tendsto_expIntE1_add_ofReal (-c)).const_mul (-exp (-c))
    rw [mul_zero] at h
    refine h.congr fun t => ?_
    ring_nf
  have h := hasIntegralAtTop_of_hasDerivAt_of_tendsto hd hcont hl
  simpa using h


/-- Real points avoid `±ia` for `a > 0`. -/
theorem ofReal_sub_I_mul_ne_zero {a : ℝ} (ha : 0 < a) (t : ℝ) :
    (t:ℂ)-I*a ≠ 0 ∧ (t:ℂ)-(-I*a) ≠ 0 := by
  constructor <;> intro h <;> have := congrArg Complex.im h <;> simp at this <;> linarith

/-- Partial fractions for `1/(a²+t²)` and `t/(a²+t²)`. -/
lemma expIntE1_rational_split {a : ℝ} (ha : 0 < a) (t : ℝ) (F : ℂ) :
    F/(a^2+(t:ℂ)^2) = 1/(2*I*a)*(F/(t-I*a)+(-1)*(F/(t-(-I*a)))) ∧
    (t:ℂ)*F/(a^2+(t:ℂ)^2) = 1/2*(F/(t-I*a)+F/(t-(-I*a))) := by
  obtain ⟨h1, h2⟩ := ofReal_sub_I_mul_ne_zero ha t
  have hf : (a:ℂ)^2+(t:ℂ)^2 = (t-I*a)*(t-(-I*a)) := by ring_nf; rw [I_sq]; ring
  have ha0 : (a:ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have he : (t:ℂ)-(-I*a) = t+I*a := by ring
  have h3 : (t:ℂ)+I*a ≠ 0 := by rwa [he] at h2
  have h4 : I*a+(t:ℂ) ≠ 0 := by rwa [add_comm]
  rw [hf, he]
  constructor
  · field_simp; ring
  · field_simp; ring


/-- The rotated arguments `-i(t∓ia)` lie in the slit plane for `t ≥ x > 0`. -/
lemma expIntE1_rational_slit_I {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    (∀ t : ℝ, x ≤ t → -I*(t-I*a) ∈ slitPlane) ∧ (∀ t : ℝ, x ≤ t → -I*(t-(-I*a)) ∈ slitPlane) := by
  constructor <;> intro t ht
  · right; simp; linarith
  · left; simp; exact ha

/-- The arguments `t∓ia` lie in the slit plane. -/
lemma expIntE1_rational_slit_real {a : ℝ} (ha : 0 < a) (x : ℝ) :
    (∀ t : ℝ, x ≤ t → (t:ℂ)-I*a ∈ slitPlane) ∧ (∀ t : ℝ, x ≤ t → (t:ℂ)-(-I*a) ∈ slitPlane) := by
  constructor <;> intro t _ <;> right <;> simp <;> linarith

/-- Interval integrability of the partial-fraction pieces. -/
lemma expIntE1_rational_intervalIntegrable (a x : ℝ) (ha : 0 < a) (G : ℝ → ℂ) (hG : Continuous G) :
    (∀ R, x ≤ R → IntervalIntegrable (fun t : ℝ => G t/(t-I*a)) volume x R) ∧
    (∀ R, x ≤ R → IntervalIntegrable (fun t : ℝ => G t/(t-(-I*a))) volume x R) := by
  constructor <;> intro R _
  · exact (hG.div (by fun_prop) fun t => (ofReal_sub_I_mul_ne_zero ha t).1).intervalIntegrable _ _
  · exact (hG.div (by fun_prop) fun t => (ofReal_sub_I_mul_ne_zero ha t).2).intervalIntegrable _ _

/-- expIntE1 scaled integrals. -/
@[dlmf 6.7.E1]
theorem expIntE1_scaled_integrals {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasIntegralAtTop (fun t : ℝ => exp (-a*t : ℂ)/(t+b)) 0 (exp (a*b : ℂ)*genExpIntE 1 (a*b)) ∧ HasIntegralAtTop (fun t : ℝ => exp (I*a*t)/(t+I*b)) 0 (exp (a*b : ℂ)*genExpIntE 1 (a*b)) := by
  have hat : Tendsto (fun t : ℝ => a*t) atTop atTop := tendsto_id.const_mul_atTop ha
  have ha0 : (a:ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have hab : exp (a*b : ℂ)*exp (-(a*b) : ℂ) = 1 := by rw [← Complex.exp_add]; simp
  constructor
  · have hs : ∀ t : ℝ, 0 ≤ t → (a:ℂ)*(t+b) ∈ slitPlane := fun t ht => by
      left; simp; positivity
    have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun t : ℝ => -exp (a*b : ℂ)*genExpIntE 1 (a*(t+b)))
        (exp (-a*t : ℂ)/(t+b)) t := by
      intro t ht
      have h1 := (hasDerivAt_genExpIntE 1 (hs t ht)).comp (t:ℂ)
        (((hasDerivAt_id (t:ℂ)).add_const (b:ℂ)).const_mul (a:ℂ))
      refine ((h1.comp_ofReal).const_mul (-exp (a*b : ℂ))).congr_deriv ?_
      have htb : (t:ℂ)+b ≠ 0 := by
        have : (0:ℝ) < t+b := by linarith
        exact_mod_cast this.ne'
      rw [show (1:ℂ)-1 = 0 by norm_num, genExpIntE_zero_eq, show -((a:ℂ)*(t+b)) = -a*t+(-(a*b)) by ring,
        Complex.exp_add]
      simp only [id, mul_one, Function.comp_apply]
      field_simp
      linear_combination hab
    have hc : ContinuousOn (fun t : ℝ => exp (-a*t : ℂ)/(t+b)) (Ici 0) :=
      ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht h0 => by
        have : (0:ℝ) < t+b := by simp at ht; linarith
        exact this.ne' (by exact_mod_cast h0)
    have hl : Tendsto (fun t : ℝ => -exp (a*b : ℂ)*genExpIntE 1 (a*(t+b))) atTop (𝓝 0) := by
      have h := ((tendsto_expIntE1_add_ofReal ((a*b:ℝ):ℂ)).comp hat).const_mul (-exp (a*b : ℂ))
      rw [mul_zero] at h
      refine h.congr fun t => ?_
      simp only [Function.comp_apply]; push_cast; ring_nf
    have h := hasIntegralAtTop_of_hasDerivAt_of_tendsto hd hc hl
    simpa using h
  · have hs : ∀ t : ℝ, 0 ≤ t → -I*(a*(t+I*b)) ∈ slitPlane := fun t ht => by
      left; simp; positivity
    have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun t : ℝ => -exp (a*b : ℂ)*genExpIntE 1 (-I*(a*(t+I*b))))
        (exp (I*a*t)/(t+I*b)) t := by
      intro t ht
      have h1 := (hasDerivAt_genExpIntE 1 (hs t ht)).comp (t:ℂ)
        ((((hasDerivAt_id (t:ℂ)).add_const (I*b)).const_mul (a:ℂ)).const_mul (-I))
      refine ((h1.comp_ofReal).const_mul (-exp (a*b : ℂ))).congr_deriv ?_
      have htb : (t:ℂ)+I*b ≠ 0 := by
        intro h0; have := congrArg Complex.im h0; simp at this; linarith
      rw [show (1:ℂ)-1 = 0 by norm_num, genExpIntE_zero_eq,
        show -(-I*((a:ℂ)*(t+I*b))) = I*a*t+(-(a*b)) by ring_nf; rw [I_sq]; ring, Complex.exp_add]
      simp only [id, mul_one, Function.comp_apply]
      have hI : -I*((a:ℂ)*(t+I*b)) = -I*a*(t+I*b) := by ring
      rw [hI]
      have htb' : (t:ℂ)+b*I ≠ 0 := by rwa [mul_comm (b:ℂ)]
      field_simp
      linear_combination hab
    have hc : ContinuousOn (fun t : ℝ => exp (I*a*t)/(t+I*b)) (Ici 0) :=
      ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht h0 => by
        have := congrArg Complex.im h0; simp at this; linarith
    have hl : Tendsto (fun t : ℝ => -exp (a*b : ℂ)*genExpIntE 1 (-I*(a*(t+I*b)))) atTop (𝓝 0) := by
      have h := ((tendsto_expIntE1_mul_I_add_ofReal (I*a*b) (ε := -1) (Or.inr rfl)).comp hat).const_mul
        (-exp (a*b : ℂ))
      rw [mul_zero] at h
      refine h.congr fun t => ?_
      simp only [Function.comp_apply]; push_cast; ring_nf
    have h := hasIntegralAtTop_of_hasDerivAt_of_tendsto hd hc hl
    convert h using 1
    push_cast
    rw [show -I*((a:ℂ)*(0+I*b)) = a*b by ring_nf; rw [I_sq]; ring]
    ring

/-- The real exponential integral differentiates to `e^u/u` on the positive axis. -/
theorem Real.hasDerivAt_expIntEi {u : ℝ} (hu : 0 < u) :
    HasDerivAt Real.expIntEi (Real.exp u/u) u := by
  have he : Real.expIntEi = fun u : ℝ => Real.eulerMascheroniConstant + Real.log u -
      (DLMF.Confluent.expIntEin (-(u:ℂ))).re := by
    funext v; rw [Real.expIntEi, Real.log_abs]
  rw [he]
  have hc : HasDerivAt (fun w : ℂ => DLMF.Confluent.expIntEin (-w))
      (-((1-exp (-(-(u:ℂ))))/(-(u:ℂ)))) (u:ℂ) := by
    have h0 : -(u:ℂ) ≠ 0 := by exact_mod_cast (neg_ne_zero.mpr hu.ne')
    exact (hasDerivAt_expIntEin_complex h0).comp (u:ℂ) (hasDerivAt_neg (u:ℂ)) |>.congr_deriv
      (by ring)
  have h := ((Real.hasDerivAt_log hu.ne').const_add Real.eulerMascheroniConstant).sub
    hc.real_of_complex
  convert h using 1
  have hre : (-((1-exp (-(-(u:ℂ))))/(-(u:ℂ)))).re = (1-Real.exp u)/u := by
    rw [neg_neg, div_neg, neg_neg, ← Complex.ofReal_exp, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [hre]
  field_simp
  ring

/-- expIntEi finite integral. -/
@[dlmf 6.7.E2]
theorem expIntEi_finite_integral {x α : ℝ} (hx : 0 < x) (hα : 0 ≤ α) (hα1 : α < 1) :
    Real.exp x * (∫ t in (0 : ℝ)..α, Real.exp (-x*t)/(1-t)) = Real.expIntEi x - Real.expIntEi ((1-α)*x) := by
  have hd : ∀ t ∈ uIcc 0 α, HasDerivAt (fun t => -Real.expIntEi ((1-t)*x))
      (Real.exp x * (Real.exp (-x*t)/(1-t))) t := by
    intro t ht
    rw [uIcc_of_le hα] at ht
    have h1 : 0 < 1-t := by linarith [ht.2]
    have hpos : 0 < (1-t)*x := mul_pos h1 hx
    have h := (Real.hasDerivAt_expIntEi hpos).comp t
      (((hasDerivAt_id t).const_sub 1).mul_const x)
    refine h.neg.congr_deriv ?_
    rw [show (1-t)*x = x + (-x*t) by ring, Real.exp_add, show x + -x*t = (1-t)*x by ring]
    field_simp
  rw [← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (ContinuousOn.intervalIntegrable (ContinuousOn.mul continuousOn_const
        (ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => by
          rw [uIcc_of_le hα] at ht; linarith [ht.2])))]
  simp
  ring

/-- expIntE1 rational fourier 0. -/
@[dlmf 6.7.E3]
theorem expIntE1_rational_fourier_0 {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    HasIntegralAtTop (fun t : ℝ => exp (I*t)/(a^2+(t : ℂ)^2)) x (I/(2*a)*(exp a*genExpIntE 1 (a-I*x)-exp (-a)*genExpIntE 1 (-a-I*x))) := by
  obtain ⟨s1, s2⟩ := expIntE1_rational_slit_I ha hx
  obtain ⟨i1, i2⟩ := expIntE1_rational_intervalIntegrable a x ha (fun t => exp (I*t)) (by fun_prop)
  have h1 := hasIntegralAtTop_exp_I_div_sub _ x s1
  have h2 := (hasIntegralAtTop_exp_I_div_sub _ x s2).const_mul (-1)
  have h := ((h1.add h2 i1 (fun R hR => (i2 R hR).const_mul _)).const_mul (1/(2*I*a))).congr
    fun t _ => ((expIntE1_rational_split ha t _).1).symm
  convert h using 1
  have ha0 : (a:ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  rw [show I*(I*(a:ℂ)) = -a by ring_nf; rw [I_sq]; ring, show I*(-I*(a:ℂ)) = a by ring_nf; rw [I_sq]; ring,
    show -I*((x:ℂ)-I*a) = -a-I*x by ring_nf; rw [I_sq]; ring,
    show -I*((x:ℂ)-(-I*a)) = a-I*x by ring_nf; rw [I_sq]; ring]
  field_simp
  ring_nf; rw [I_sq]; ring

/-- expIntE1 rational laplace 0. -/
@[dlmf 6.7.E5]
theorem expIntE1_rational_laplace_0 {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasIntegralAtTop (fun t : ℝ => exp (-t : ℂ)/(a^2+(t : ℂ)^2)) x (-1/(2*a*I)*(exp (I*a)*genExpIntE 1 (x+I*a)-exp (-I*a)*genExpIntE 1 (x-I*a))) := by
  obtain ⟨s1, s2⟩ := expIntE1_rational_slit_real ha x
  obtain ⟨i1, i2⟩ := expIntE1_rational_intervalIntegrable a x ha (fun t => exp (-t : ℂ)) (by fun_prop)
  have h1 := hasIntegralAtTop_exp_neg_div_sub _ x s1
  have h2 := (hasIntegralAtTop_exp_neg_div_sub _ x s2).const_mul (-1)
  have h := ((h1.add h2 i1 (fun R hR => (i2 R hR).const_mul _)).const_mul (1/(2*I*a))).congr
    fun t _ => ((expIntE1_rational_split ha t _).1).symm
  convert h using 1
  have ha0 : (a:ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  rw [show (x:ℂ)-(-I*a) = x+I*a by ring, show -(-I*(a:ℂ)) = I*a by ring, show -(I*(a:ℂ)) = -I*a by ring]
  field_simp
  ring_nf

/-- expIntE1 rational fourier 1. -/
@[dlmf 6.7.E4]
theorem expIntE1_rational_fourier_1 {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    HasIntegralAtTop (fun t : ℝ => (t : ℂ)*exp (I*t)/(a^2+(t : ℂ)^2)) x ((exp a*genExpIntE 1 (a-I*x)+exp (-a)*genExpIntE 1 (-a-I*x))/2) := by
  obtain ⟨s1, s2⟩ := expIntE1_rational_slit_I ha hx
  obtain ⟨i1, i2⟩ := expIntE1_rational_intervalIntegrable a x ha (fun t => exp (I*t)) (by fun_prop)
  have h1 := hasIntegralAtTop_exp_I_div_sub _ x s1
  have h2 := hasIntegralAtTop_exp_I_div_sub _ x s2
  have h := ((h1.add h2 i1 i2).const_mul (1/2)).congr
    fun t _ => ((expIntE1_rational_split ha t _).2).symm
  convert h using 1
  rw [show I*(I*(a:ℂ)) = -a by ring_nf; rw [I_sq]; ring, show I*(-I*(a:ℂ)) = a by ring_nf; rw [I_sq]; ring,
    show -I*((x:ℂ)-I*a) = -a-I*x by ring_nf; rw [I_sq]; ring,
    show -I*((x:ℂ)-(-I*a)) = a-I*x by ring_nf; rw [I_sq]; ring]
  ring

/-- expIntE1 rational laplace 1. -/
@[dlmf 6.7.E6]
theorem expIntE1_rational_laplace_1 {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasIntegralAtTop (fun t : ℝ => (t : ℂ)*exp (-t : ℂ)/(a^2+(t : ℂ)^2)) x ((exp (I*a)*genExpIntE 1 (x+I*a)+exp (-I*a)*genExpIntE 1 (x-I*a))/2) := by
  obtain ⟨s1, s2⟩ := expIntE1_rational_slit_real ha x
  obtain ⟨i1, i2⟩ := expIntE1_rational_intervalIntegrable a x ha (fun t => exp (-t : ℂ)) (by fun_prop)
  have h1 := hasIntegralAtTop_exp_neg_div_sub _ x s1
  have h2 := hasIntegralAtTop_exp_neg_div_sub _ x s2
  have h := ((h1.add h2 i1 i2).const_mul (1/2)).congr
    fun t _ => ((expIntE1_rational_split ha t _).2).symm
  convert h using 1
  rw [show (x:ℂ)-(-I*a) = x+I*a by ring, show -(-I*(a:ℂ)) = I*a by ring, show -(I*(a:ℂ)) = -I*a by ring]
  ring

/-- A removable-quotient primitive on a straight segment is an integral over the unit interval,
together with its integrability there. -/
theorem primitive_div_self_eq_integral {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hF0 : F 0 = 0)
    (z : ℂ) :
    IntervalIntegrable (fun s : ℝ => F (s*z)/s) volume 0 1 ∧
      primitive (fun t => F t/t) z = ∫ s : ℝ in 0..1, F (s*z)/s := by
  have hae : ∀ s : ℝ, s ≠ 0 → F (s*z)/s = z*dslope F 0 (s*z) := by
    intro s hs
    by_cases hz : z = 0
    · subst hz; simp [hF0]
    have hsz : (s:ℂ)*z ≠ 0 := mul_ne_zero (by exact_mod_cast hs) hz
    rw [dslope_of_ne _ hsz, slope_def_field, hF0, sub_zero, sub_zero]
    field_simp
  have hne : ∀ᵐ s : ℝ, s ≠ 0 := by simp [MeasureTheory.ae_iff]
  have hc : Continuous (fun s : ℝ => z*dslope F 0 (s*z)) :=
    continuous_const.mul ((differentiable_dslope_entire hF 0).continuous.comp (by fun_prop))
  constructor
  · refine (hc.intervalIntegrable 0 1).congr_ae ?_
    refine ae_restrict_of_ae ?_
    filter_upwards [hne] with s hs
    exact (hae s hs).symm
  · rw [← primitive_dslope_zero hF0]
    simp only [primitive, segmentIntegral, sub_zero, zero_add]
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hne] with s hs _
    exact (hae s hs).symm

/-- expIntEin real integral 7. -/
@[dlmf 6.7.E7]
theorem expIntEin_real_integral_7 (a b : ℝ) :
    (∫ t in (0 : ℝ)..1, Real.exp (-a*t)*Real.sin (b*t)/t) = (expIntEin (a+I*b)).im := by
  obtain ⟨hi, he⟩ := primitive_div_self_eq_integral (F := fun t => 1-exp (-t)) (by fun_prop)
    (by simp) (a+I*b)
  rw [expIntEin_segment_integral, he, ← Complex.imCLM_apply,
    ← ContinuousLinearMap.intervalIntegral_comp_comm _ hi]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [Complex.imCLM_apply]
  rw [Complex.div_ofReal_im]
  simp [Complex.exp_im, mul_comm]

/-- expIntEin real integral 8. -/
@[dlmf 6.7.E8]
theorem expIntEin_real_integral_8 (a b : ℝ) :
    (∫ t in (0 : ℝ)..1, Real.exp (-a*t)*(1-Real.cos (b*t))/t) = (expIntEin (a+I*b)).re-(expIntEin a).re := by
  obtain ⟨hi, he⟩ := primitive_div_self_eq_integral (F := fun t => 1-exp (-t)) (by fun_prop)
    (by simp) (a+I*b)
  obtain ⟨hi', he'⟩ := primitive_div_self_eq_integral (F := fun t => 1-exp (-t)) (by fun_prop)
    (by simp) (a:ℂ)
  rw [expIntEin_segment_integral, expIntEin_segment_integral, he, he', ← Complex.reCLM_apply,
    ← Complex.reCLM_apply, ← map_sub, ← intervalIntegral.integral_sub hi hi',
    ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hi.sub hi')]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [Complex.reCLM_apply, Complex.sub_re]
  rw [Complex.div_ofReal_re, Complex.div_ofReal_re]
  simp [Complex.exp_re, mul_comm]
  ring

/-- expIntEin real integral 11. -/
@[dlmf 6.7.E11]
theorem expIntEin_real_integral_11 (a b : ℝ) :
    (∫ t in (0 : ℝ)..1, (1-Real.exp (-a*t))*Real.cos (b*t)/t) = (expIntEin (a+I*b)).re-(cosIntCin b).re := by
  obtain ⟨hi, he⟩ := primitive_div_self_eq_integral (F := fun t => 1-exp (-t)) (by fun_prop)
    (by simp) (a+I*b)
  obtain ⟨hi', he'⟩ := primitive_div_self_eq_integral (F := fun t => 1-cos t) (by fun_prop)
    (by simp) (b:ℂ)
  rw [expIntEin_segment_integral, cosIntCin_segment_integral, he, he', ← Complex.reCLM_apply,
    ← Complex.reCLM_apply, ← map_sub, ← intervalIntegral.integral_sub hi hi',
    ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hi.sub hi')]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [Complex.reCLM_apply, Complex.sub_re]
  rw [Complex.div_ofReal_re, Complex.div_ofReal_re]
  have hc : (cos ((t:ℂ)*b)).re = Real.cos (b*t) := by
    rw [← Complex.ofReal_mul, Complex.cos_ofReal_re, mul_comm]
  simp only [Complex.sub_re, Complex.one_re, hc]
  simp [Complex.exp_re, mul_comm]
  ring

section AngularTools

/-- `cos t + i s sin t ≠ 0` for `s = ±1`. -/
theorem eiIn_arc_ne_zero {s : ℂ} (hs : s = 1 ∨ s = -1) (t : ℝ) :
    (Real.cos t : ℂ) + I*s*Real.sin t ≠ 0 := by
  intro h
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  rcases hs with rfl | rfl <;>
    simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, one_re, one_im,
      neg_re, neg_im, zero_re, zero_im] at h1 h2 <;>
    nlinarith [Real.sin_sq_add_cos_sq t]

/-- The quarter-circle integral of `1 - e^{-w}` along `w = z(cos t + i s sin t)`, `s = ±1`:
`∫₀^{π/2} (1 - e^{-w(t)}) dt = (Ein(isz) - Ein z)/(is)`. -/
theorem eiIn_arc_integral {s : ℂ} (hs : s = 1 ∨ s = -1) (z : ℂ) :
    ∫ t : ℝ in 0..(π/2), (1 - exp (-(z*((Real.cos t : ℂ) + I*s*Real.sin t)))) =
      (expIntEin (I*s*z) - expIntEin z)/(I*s) := by
  have hs0 : I*s ≠ 0 := by rcases hs with rfl | rfl <;> simp
  have hs1 : s ≠ 0 := by rcases hs with rfl | rfl <;> simp
  have hss : (I*s)^2 = -1 := by rcases hs with rfl | rfl <;> ring_nf <;> simp
  by_cases hz : z = 0
  · subst hz; simp
  set w : ℝ → ℂ := fun t => z*((Real.cos t : ℂ) + I*s*Real.sin t) with hw
  have hw0 : ∀ t, w t ≠ 0 := fun t => mul_ne_zero hz (eiIn_arc_ne_zero hs t)
  have hwd : ∀ t : ℝ, HasDerivAt w (I*s*w t) t := by
    intro t
    have hc := (Real.hasDerivAt_cos t).ofReal_comp
    have hsn := (Real.hasDerivAt_sin t).ofReal_comp
    refine ((hc.add (hsn.const_mul (I*s))).const_mul z).congr_deriv ?_
    simp only [hw, ofReal_neg]
    linear_combination (-(z*Real.sin t))*hss
  have hd : ∀ t ∈ uIcc (0:ℝ) (π/2), HasDerivAt (fun t => expIntEin (w t)/(I*s))
      (1 - exp (-(z*((Real.cos t : ℂ) + I*s*Real.sin t)))) t := by
    intro t _
    refine (((hasDerivAt_expIntEin_complex (hw0 t)).comp t (hwd t)).div_const (I*s)).congr_deriv ?_
    simp only [hw]; field_simp
    exact mul_div_cancel_left₀ _ (eiIn_arc_ne_zero hs t)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
    apply Continuous.intervalIntegrable; fun_prop)]
  simp only [hw, Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast
  rw [← sub_div]; congr 2 <;> ring_nf

/-- The quarter-circle integral of `e^{-w}`. -/
theorem eiIn_arc_integral_exp {s : ℂ} (hs : s = 1 ∨ s = -1) (z : ℂ) :
    ∫ t : ℝ in 0..(π/2), exp (-(z*((Real.cos t : ℂ) + I*s*Real.sin t))) =
      π/2 - (expIntEin (I*s*z) - expIntEin z)/(I*s) := by
  rw [← eiIn_arc_integral hs, intervalIntegral.integral_sub (by simp)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp

/-- `Ein(-iz) = Cin z - i Si z`. -/
theorem eiIn_Ein_neg_I (z : ℂ) : expIntEin (I*(-1)*z) = cosIntCin z - I*sinInt z := by
  rw [show I*(-1)*z = I*(-z) by ring, expIntEin_mul_I, cosIntCin_even, sinInt_odd]; ring

end AngularTools

/-- sinIntTail angular integral. -/
@[dlmf 6.7.E9]
theorem sinIntTail_angular_integral (z : ℂ) :
    sinIntTail z = -∫ t : ℝ in 0..(π/2), exp (-z*Real.cos t)*cos (z*Real.sin t) := by
  have hpt : ∀ t : ℝ, exp (-z*Real.cos t)*cos (z*Real.sin t) =
      (exp (-(z*((Real.cos t : ℂ) + I*(-1:ℂ)*Real.sin t))) +
        exp (-(z*((Real.cos t : ℂ) + I*(1:ℂ)*Real.sin t))))/2 := by
    intro t
    rw [Complex.cos, mul_div_assoc', mul_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 2 <;> congr 1 <;> ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
    eiIn_arc_integral_exp (Or.inl rfl), eiIn_arc_integral_exp (Or.inr rfl), eiIn_Ein_neg_I,
    show I*(1:ℂ)*z = I*z by ring, expIntEin_mul_I, sinIntTail]
  field_simp
  ring_nf

/-- Ein sub Cin angular integral. -/
@[dlmf 6.7.E10]
theorem Ein_sub_Cin_angular_integral (z : ℂ) :
    expIntEin z - cosIntCin z = ∫ t : ℝ in 0..(π/2), exp (-z*Real.cos t)*sin (z*Real.sin t) := by
  have hpt : ∀ t : ℝ, exp (-z*Real.cos t)*sin (z*Real.sin t) =
      (exp (-(z*((Real.cos t : ℂ) + I*(1:ℂ)*Real.sin t))) -
        exp (-(z*((Real.cos t : ℂ) + I*(-1:ℂ)*Real.sin t))))*I/2 := by
    intro t
    rw [Complex.sin, mul_div_assoc', ← mul_assoc, mul_sub, ← Complex.exp_add, ← Complex.exp_add]
    congr 3 <;> congr 1 <;> ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_mul_const, intervalIntegral.integral_sub
    (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
    eiIn_arc_integral_exp (Or.inl rfl), eiIn_arc_integral_exp (Or.inr rfl), eiIn_Ein_neg_I,
    show I*(1:ℂ)*z = I*z by ring, expIntEin_mul_I]
  field_simp
  ring_nf

/-- expIntAux horizontal integral. -/
@[dlmf 6.7.E12]
theorem expIntAux_horizontal_integral {z : ℂ} (hz : z ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => exp (I*(z+t))/(z+t)) 0 (exp (I*z)*(expIntAuxG z+I*expIntAuxF z)) := by
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun t : ℝ => -(exp (I*(z+t))*(expIntAuxG (z+t)+I*expIntAuxF (z+t))))
      (exp (I*(z+t))/(z+t)) t := by
    intro t ht
    have hm := add_ofReal_mem_slitPlane hz ht
    have h0 := slitPlane_ne_zero hm
    have hG : HasDerivAt (fun w => -(exp (I*w)*(expIntAuxG w+I*expIntAuxF w)))
        (-((I*exp (I*(z+t)))*(expIntAuxG (z+t)+I*expIntAuxF (z+t))+exp (I*(z+t))*((expIntAuxF (z+t)-1/(z+t))+I*(-expIntAuxG (z+t))))) (z+t) := by
      have he : HasDerivAt (fun w => exp (I*w)) (I*exp (I*(z+t))) (z+t) := by
        simpa [mul_comm] using ((hasDerivAt_id (z+t)).const_mul I).cexp
      exact (he.mul ((hasDerivAt_expIntAuxG hm).add ((hasDerivAt_expIntAuxF hm).const_mul I))).neg
    refine (hasDerivAt_comp_add_ofReal hG).congr_deriv ?_
    field_simp
    ring_nf; rw [I_sq]; ring
  have hc : ContinuousOn (fun t : ℝ => exp (I*(z+t))/(z+t)) (Ici 0) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => slitPlane_ne_zero (add_ofReal_mem_slitPlane hz ht)
  have hl : Tendsto (fun t : ℝ => -(exp (I*(z+t))*(expIntAuxG (z+t)+I*expIntAuxF (z+t)))) atTop (𝓝 0) := by
    have h := (tendsto_expIntE1_mul_I_add_ofReal z (ε := -1) (Or.inr rfl)).neg
    rw [neg_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_re_add_ofReal_pos z] with t ht
    have he := expIntAux_eq_E1 ht (ε := 1) (Or.inl rfl)
    push_cast at he ⊢
    simp only [one_mul, neg_mul] at he
    rw [he, mul_comm (genExpIntE 1 _), ← mul_assoc, ← Complex.exp_add]
    simp
  have h := hasIntegralAtTop_of_hasDerivAt_of_tendsto hd hc hl
  simpa using h

/-- expIntAuxF oscillatory integral. -/
@[dlmf 6.7.E13]
theorem expIntAuxF_oscillatory_integral {z : ℂ} (hz : z ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => (sin (t : ℂ))/(t+z)) 0 (expIntAuxF z) := by
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun t : ℝ => cos z*sinIntTail (z+t)-sin z*cosInt (z+t))
      ((sin (t : ℂ))/(t+z)) t := by
    intro t ht
    have hm := add_ofReal_mem_slitPlane hz ht
    have h0 := slitPlane_ne_zero hm
    have hG : HasDerivAt (fun w => cos z*sinIntTail w-sin z*cosInt w)
        (cos z*(sin (z+t)/(z+t))-sin z*(cos (z+t)/(z+t))) (z+t) :=
      (((hasDerivAt_sinInt_complex h0).sub_const _).const_mul _).sub ((hasDerivAt_cosInt_complex hm).const_mul _)
    refine (hasDerivAt_comp_add_ofReal hG).congr_deriv ?_
    have hs : sin (t:ℂ) = sin (z+t)*cos z-cos (z+t)*sin z := by
      rw [← Complex.sin_sub]; ring_nf
    rw [hs, add_comm (t:ℂ) z]
    field_simp
  have hc : ContinuousOn (fun t : ℝ => (sin (t : ℂ))/(t+z)) (Ici 0) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => by
      rw [add_comm]; exact slitPlane_ne_zero (add_ofReal_mem_slitPlane hz ht)
  have hl : Tendsto (fun t : ℝ => cos z*sinIntTail (z+t)-sin z*cosInt (z+t)) atTop (𝓝 0) := by
    simpa using ((tendsto_sinIntTail_add_ofReal z).const_mul (cos z)).sub
      ((tendsto_cosInt_add_ofReal z).const_mul (sin z))
  have h := hasIntegralAtTop_of_hasDerivAt_of_tendsto hd hc hl
  convert h using 1
  simp [expIntAuxF]; ring

/-- expIntAuxF laplace integral. -/
@[dlmf 6.7.E13]
theorem expIntAuxF_laplace_integral {z : ℂ} (hz : 0 ≤ z.re) :
    HasIntegralAtTop (fun t : ℝ => (t : ℂ)^0*exp (-z*t)/((t : ℂ)^2+1)) 0 (expIntAuxF z) := by
  by_cases hz0 : z = 0
  · subst hz0
    have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun t : ℝ => (Real.arctan t : ℂ))
        ((t : ℂ)^0*exp (-0*t)/((t : ℂ)^2+1)) t := by
      intro t _
      refine (Real.hasDerivAt_arctan t).ofReal_comp.congr_deriv ?_
      push_cast; simp; ring
    have hc : ContinuousOn (fun t : ℝ => (t : ℂ)^0*exp (-0*t)/((t : ℂ)^2+1)) (Ici 0) := by
      refine ContinuousOn.div (by fun_prop) (by fun_prop) fun t _ h => ?_
      rw [show ((t:ℂ)^2+1) = ((t^2+1:ℝ):ℂ) by push_cast; ring, ofReal_eq_zero] at h
      nlinarith [sq_nonneg t]
    have hl : Tendsto (fun t : ℝ => (Real.arctan t : ℂ)) atTop (𝓝 ((π/2 : ℝ) : ℂ)) :=
      (continuous_ofReal.tendsto _).comp (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds)
    have h := hasIntegralAtTop_of_hasDerivAt_of_tendsto hd hc hl
    convert h using 1
    have : sinInt 0 = 0 := by simp [sinInt]
    simp [expIntAuxF, sinIntTail, this]
  · exact (expIntAux_laplace_hasIntegralAtTop hz0 hz).1.congr fun t _ => by simp

section BesselKZeroIntegrals

open DLMF.Bessel

/-- `∫₀^∞ e^{-ct} e^{±it} dt = 1/(c ∓ i)`. -/
theorem integral_exp_neg_mul_exp_I {c : ℝ} (hc : 0 < c) (ε : ℂ) (hε : ε.re = 0) :
    ∫ t : ℝ in Ioi 0, exp ((-(c : ℂ) + ε) * t) = 1 / (c - ε) := by
  have ha : (-(c : ℂ) + ε).re < 0 := by simp [hε, hc]
  rw [integral_exp_mul_complex_Ioi ha 0]
  have hne : (c : ℂ) - ε ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hε] at this; linarith
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  have hne' : -(c : ℂ) + ε ≠ 0 := by
    intro h; apply hne; linear_combination -h
  rw [show (c : ℂ) - ε = -(-(c : ℂ) + ε) by ring]
  field_simp

/-- `∫₀^∞ e^{-ct} cos t dt = c/(c²+1)`. -/
theorem integral_exp_neg_mul_cos {c : ℝ} (hc : 0 < c) :
    ∫ t : ℝ in Ioi 0, exp (-(c : ℂ) * t) * cos t = c / (c ^ 2 + 1) := by
  have h1 := integral_exp_neg_mul_exp_I hc I (by simp)
  have h2 := integral_exp_neg_mul_exp_I hc (-I) (by simp)
  have i1 := integrableOn_exp_mul_complex_Ioi (a := -(c : ℂ) + I) (by simp [hc]) 0
  have i2 := integrableOn_exp_mul_complex_Ioi (a := -(c : ℂ) + -I) (by simp [hc]) 0
  have he : ∀ t : ℝ, exp (-(c : ℂ) * t) * cos t =
      (1 / 2 : ℂ) * (exp ((-(c : ℂ) + I) * t) + exp ((-(c : ℂ) + -I) * t)) := by
    intro t
    simp only [add_mul, exp_add, Complex.cos, neg_mul]
    ring_nf
  simp_rw [he]
  rw [MeasureTheory.integral_const_mul, integral_add i1 i2, h1, h2]
  have hne1 : (c : ℂ) - I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hne2 : (c : ℂ) - -I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hne3 : (c : ℂ) ^ 2 + 1 ≠ 0 := by
    have : ((c ^ 2 + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : c ^ 2 + 1 ≠ 0)
    push_cast at this; exact this
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- `∫₀^∞ e^{-ct} sin t dt = 1/(c²+1)`. -/
theorem integral_exp_neg_mul_sin {c : ℝ} (hc : 0 < c) :
    ∫ t : ℝ in Ioi 0, exp (-(c : ℂ) * t) * sin t = 1 / (c ^ 2 + 1) := by
  have h1 := integral_exp_neg_mul_exp_I hc I (by simp)
  have h2 := integral_exp_neg_mul_exp_I hc (-I) (by simp)
  have i1 := integrableOn_exp_mul_complex_Ioi (a := -(c : ℂ) + I) (by simp [hc]) 0
  have i2 := integrableOn_exp_mul_complex_Ioi (a := -(c : ℂ) + -I) (by simp [hc]) 0
  have he : ∀ t : ℝ, exp (-(c : ℂ) * t) * sin t =
      (-I / 2 : ℂ) * (exp ((-(c : ℂ) + I) * t) - exp ((-(c : ℂ) + -I) * t)) := by
    intro t
    simp only [add_mul, exp_add, Complex.sin, neg_mul]
    ring_nf
  simp_rw [he]
  rw [MeasureTheory.integral_const_mul, integral_sub i1 i2, h1, h2]
  have hne1 : (c : ℂ) - I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hne2 : (c : ℂ) - -I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hne3 : (c : ℂ) ^ 2 + 1 ≠ 0 := by
    have : ((c ^ 2 + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : c ^ 2 + 1 ≠ 0)
    push_cast at this; exact this
  field_simp
  ring_nf
  rw [I_sq]
  ring


/-- Schläfli's integral for `2 K₀(2√(xt))` with the `t`-dependence isolated. -/
theorem two_mul_besselK_zero_eq_integral {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    2 * besselK 0 (2 * ((x : ℂ) * t) ^ (1 / 2 : ℂ)) =
      ∫ s : ℝ in Ioi 0, exp (-(s : ℂ)) * (s : ℂ)⁻¹ * exp (-((x / s : ℝ) : ℂ) * t) := by
  have hxt : 0 < x * t := mul_pos hx ht
  have harg : 2 * ((x : ℂ) * t) ^ (1 / 2 : ℂ) = ((2 * Real.sqrt (x * t) : ℝ) : ℂ) := by
    rw [show (x : ℂ) * t = ((x * t : ℝ) : ℂ) by push_cast; ring,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← ofReal_cpow hxt.le, Real.sqrt_eq_rpow]
    push_cast; ring_nf
  have hy : 0 < 2 * Real.sqrt (x * t) := by positivity
  rw [harg, besselK_ofReal_eq_integral_schlafli' hy 0, neg_zero, cpow_zero, mul_one,
    ← mul_assoc, show (2 : ℂ) * (1 / 2) = 1 by norm_num, one_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs0 : (0 : ℝ) < s := hs
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hsq : (((2 * Real.sqrt (x * t) : ℝ) : ℂ)) ^ 2 = 4 * x * t := by
    rw [← ofReal_pow, mul_pow, Real.sq_sqrt hxt.le]; push_cast; ring
  rw [hsq, zero_sub, cpow_neg_one, mul_comm (exp _) _, mul_comm (exp _) _, mul_assoc,
    mul_assoc, ← exp_add]
  congr 2
  push_cast
  field_simp
  ring

/-- Fubini for the Schläfli kernel of `K₀(2√(xt))` against a bounded weight. -/
theorem integral_besselK_zero_swap {x : ℝ} (hx : 0 < x) {wt : ℝ → ℂ} (hwm : Measurable wt)
    (hw1 : ∀ t, ‖wt t‖ ≤ 1) :
    ∫ t : ℝ in Ioi 0, (∫ s : ℝ in Ioi 0,
        exp (-(s : ℂ)) * (s : ℂ)⁻¹ * exp (-((x / s : ℝ) : ℂ) * t)) * wt t =
      ∫ s : ℝ in Ioi 0, exp (-(s : ℂ)) * (s : ℂ)⁻¹ *
        ∫ t : ℝ in Ioi 0, exp (-((x / s : ℝ) : ℂ) * t) * wt t := by
  set f : ℝ → ℝ → ℂ := fun s t =>
    exp (-(s : ℂ)) * (s : ℂ)⁻¹ * exp (-((x / s : ℝ) : ℂ) * t) * wt t with hf
  have hmeas : Measurable (Function.uncurry f) := by
    simp only [hf]
    have : Measurable fun p : ℝ × ℝ => wt p.2 := hwm.comp measurable_snd
    fun_prop
  have hbound : ∀ s t : ℝ, 0 < s → ‖f s t‖ ≤ Real.exp (-s) * s⁻¹ * Real.exp (-(x / s) * t) := by
    intro s t hs
    simp only [hf, norm_mul, norm_inv, Complex.norm_exp, neg_re, ofReal_re, mul_re, ofReal_im,
      mul_zero, sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    calc _ ≤ Real.exp (-s) * s⁻¹ * Real.exp (-(x / s) * t) * 1 := by gcongr; exact hw1 t
      _ = _ := by ring
  have hint : Integrable (Function.uncurry f) ((volume.restrict (Ioi (0 : ℝ))).prod
      (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [integrable_prod_iff hmeas.aestronglyMeasurable]
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs0 : (0 : ℝ) < s := hs
      refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 (div_pos hx hs0)).const_mul
        (Real.exp (-s) * s⁻¹)) (hmeas.comp measurable_prodMk_left).aestronglyMeasurable ?_
      exact Eventually.of_forall fun t => by
        simpa [Function.uncurry, mul_assoc] using hbound s t hs0
    · refine Integrable.mono' (((exp_neg_integrableOn_Ioi 0 zero_lt_one).const_mul x⁻¹))
        (hmeas.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs0 : (0 : ℝ) < s := hs
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      have hb : 0 < x / s := div_pos hx hs0
      calc ∫ t in Ioi 0, ‖Function.uncurry f (s, t)‖ ≤
            ∫ t in Ioi 0, Real.exp (-s) * s⁻¹ * Real.exp (-(x / s) * t) := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
              ((exp_neg_integrableOn_Ioi 0 hb).const_mul _) (Eventually.of_forall fun t => ?_)
            exact hbound s t hs0
        _ = x⁻¹ * Real.exp (-1 * s) := by
            rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi (by linarith) 0]
            simp only [mul_zero, Real.exp_zero, neg_one_mul]
            field_simp
  have h := integral_integral_swap hint
  calc _ = ∫ t : ℝ in Ioi 0, ∫ s : ℝ in Ioi 0, f s t :=
        integral_congr_ae (Eventually.of_forall fun t => (integral_mul_const _ _).symm)
    _ = ∫ s : ℝ in Ioi 0, ∫ t : ℝ in Ioi 0, f s t := h.symm
    _ = _ := by
      refine integral_congr_ae (Eventually.of_forall fun s => ?_)
      simp only [hf]
      rw [← MeasureTheory.integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun t => by simp only; ring)

/-- `‖cos t‖ ≤ 1` for real `t`. -/
theorem norm_cos_ofReal_le_one (t : ℝ) : ‖cos (t : ℂ)‖ ≤ 1 := by
  rw [← ofReal_cos, Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one t

/-- `‖sin t‖ ≤ 1` for real `t`. -/
theorem norm_sin_ofReal_le_one (t : ℝ) : ‖sin (t : ℂ)‖ ≤ 1 := by
  rw [← ofReal_sin, Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_sin_le_one t

/-- Reduction of `2∫₀^∞ K₀(2√(xt)) wt(t) dt` to a single `s`-integral. -/
theorem two_mul_integral_besselK_zero_mul {x : ℝ} (hx : 0 < x) {wt : ℝ → ℂ} (hwm : Measurable wt)
    (hw1 : ∀ t, ‖wt t‖ ≤ 1) :
    2 * ∫ t : ℝ in Ioi 0, besselK 0 (2 * ((x : ℂ) * t) ^ (1 / 2 : ℂ)) * wt t =
      ∫ s : ℝ in Ioi 0, exp (-(s : ℂ)) * (s : ℂ)⁻¹ *
        ∫ t : ℝ in Ioi 0, exp (-((x / s : ℝ) : ℂ) * t) * wt t := by
  rw [← integral_besselK_zero_swap hx hwm hw1, ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [← two_mul_besselK_zero_eq_integral hx ht]
  ring

/-- The Laplace representations of `f(x)` and `g(x)` as Lebesgue integrals, for `x > 0`. -/
theorem expIntAux_ofReal_laplace_Ioi {x : ℝ} (hx : 0 < x) :
    expIntAuxF x = ∫ u : ℝ in Ioi 0, exp (-(x : ℂ) * u) / ((u : ℂ) ^ 2 + 1) ∧
    expIntAuxG x = ∫ u : ℝ in Ioi 0, (u : ℂ) * exp (-(x : ℂ) * u) / ((u : ℂ) ^ 2 + 1) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  obtain ⟨h1, h2⟩ := expIntAux_laplace_hasIntegralAtTop hx0 (by simp [hx.le])
  have hden : ∀ u : ℝ, 1 ≤ ‖(u : ℂ) ^ 2 + 1‖ := fun u => by
    rw [show ((u : ℂ) ^ 2 + 1) = ((u ^ 2 + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
    nlinarith [sq_nonneg u]
  have hne : ∀ u : ℝ, (u : ℂ) ^ 2 + 1 ≠ 0 := fun u h => by
    have := hden u; rw [h, norm_zero] at this; linarith
  have hE : ∀ u : ℝ, ‖exp (-(x : ℂ) * u)‖ = Real.exp (-x * u) := fun u => by
    rw [Complex.norm_exp]; congr 1; simp
  have hdom := exp_neg_integrableOn_Ioi 0 hx
  have i1 : IntegrableOn (fun u : ℝ => exp (-(x : ℂ) * u) / ((u : ℂ) ^ 2 + 1)) (Ioi 0) := by
    refine hdom.mono' ((Continuous.div (by fun_prop) (by fun_prop) hne).aestronglyMeasurable)
      (Eventually.of_forall fun u => ?_)
    rw [norm_div, hE]
    exact div_le_self (Real.exp_pos _).le (hden u)
  have i2 : IntegrableOn (fun u : ℝ => (u : ℂ) * exp (-(x : ℂ) * u) / ((u : ℂ) ^ 2 + 1))
      (Ioi 0) := by
    refine hdom.mono' ((Continuous.div (by fun_prop) (by fun_prop) hne).aestronglyMeasurable)
      ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := hu
    rw [norm_div, norm_mul, hE, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0,
      show ((u : ℂ) ^ 2 + 1) = ((u ^ 2 + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity), div_le_iff₀ (by positivity)]
    have := (Real.exp_pos (-x * u)).le
    nlinarith [sq_nonneg (u - 1)]
  exact ⟨(tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi 0 i1 tendsto_id) h1).symm,
    (tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi 0 i2 tendsto_id) h2).symm⟩

/-- Real-variable form of DLMF 6.7.15. -/
lemma expIntAuxF_ofReal_eq_integral_besselK {x : ℝ} (hx : 0 < x) :
    expIntAuxF x = 2 * ∫ t : ℝ in Ioi 0, besselK 0 (2 * ((x : ℂ) * t) ^ (1 / 2 : ℂ)) * cos t := by
  rw [two_mul_integral_besselK_zero_mul hx (by fun_prop) norm_cos_ofReal_le_one]
  have h1 : ∫ s : ℝ in Ioi 0, exp (-(s : ℂ)) * (s : ℂ)⁻¹ *
        ∫ t : ℝ in Ioi 0, exp (-((x / s : ℝ) : ℂ) * t) * cos t =
      ∫ s : ℝ in Ioi 0, exp (-(s : ℂ)) * x / ((s : ℂ) ^ 2 + x ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hs0 : (0 : ℝ) < s := hs
    rw [integral_exp_neg_mul_cos (div_pos hx hs0)]
    have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
    have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    have hne : (s : ℂ) ^ 2 + x ^ 2 ≠ 0 := by
      have : ((s ^ 2 + x ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : s ^ 2 + x ^ 2 ≠ 0)
      push_cast at this; exact this
    push_cast
    have hq : ((x : ℂ) / s) ^ 2 + 1 = ((s : ℂ) ^ 2 + x ^ 2) / s ^ 2 := by field_simp; ring
    rw [hq]
    field_simp
  have h2 : ∫ s : ℝ in Ioi 0, exp (-(s : ℂ)) * x / ((s : ℂ) ^ 2 + x ^ 2) =
      ∫ u : ℝ in Ioi 0, exp (-(x : ℂ) * u) / ((u : ℂ) ^ 2 + 1) := by
    have h := integral_comp_mul_left_Ioi
      (fun s : ℝ => exp (-(s : ℂ)) * x / ((s : ℂ) ^ 2 + x ^ 2)) 0 hx
    rw [mul_zero] at h
    rw [← smul_inv_smul₀ hx.ne' (∫ s : ℝ in Ioi 0, exp (-(s : ℂ)) * x / ((s : ℂ) ^ 2 + x ^ 2)),
      ← h, ← integral_smul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    have hne : (u : ℂ) ^ 2 + 1 ≠ 0 := by
      have : ((u ^ 2 + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : u ^ 2 + 1 ≠ 0)
      push_cast at this; exact this
    rw [Complex.real_smul]
    push_cast
    rw [show ((x : ℂ) * u) ^ 2 + x ^ 2 = x ^ 2 * (u ^ 2 + 1) by ring, neg_mul]
    field_simp
  rw [h1, h2]
  exact (expIntAux_ofReal_laplace_Ioi hx).1

/-- Real-variable form of DLMF 6.7.16. -/
lemma expIntAuxG_ofReal_eq_integral_besselK {x : ℝ} (hx : 0 < x) :
    expIntAuxG x = 2 * ∫ t : ℝ in Ioi 0, besselK 0 (2 * ((x : ℂ) * t) ^ (1 / 2 : ℂ)) * sin t := by
  rw [two_mul_integral_besselK_zero_mul hx (by fun_prop) norm_sin_ofReal_le_one]
  have h1 : ∫ s : ℝ in Ioi 0, exp (-(s : ℂ)) * (s : ℂ)⁻¹ *
        ∫ t : ℝ in Ioi 0, exp (-((x / s : ℝ) : ℂ) * t) * sin t =
      ∫ s : ℝ in Ioi 0, exp (-(s : ℂ)) * s / ((s : ℂ) ^ 2 + x ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hs0 : (0 : ℝ) < s := hs
    rw [integral_exp_neg_mul_sin (div_pos hx hs0)]
    have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
    have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    have hne : (s : ℂ) ^ 2 + x ^ 2 ≠ 0 := by
      have : ((s ^ 2 + x ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : s ^ 2 + x ^ 2 ≠ 0)
      push_cast at this; exact this
    push_cast
    have hq : ((x : ℂ) / s) ^ 2 + 1 = ((s : ℂ) ^ 2 + x ^ 2) / s ^ 2 := by field_simp; ring
    rw [hq]
    field_simp
  have h2 : ∫ s : ℝ in Ioi 0, exp (-(s : ℂ)) * s / ((s : ℂ) ^ 2 + x ^ 2) =
      ∫ u : ℝ in Ioi 0, (u : ℂ) * exp (-(x : ℂ) * u) / ((u : ℂ) ^ 2 + 1) := by
    have h := integral_comp_mul_left_Ioi
      (fun s : ℝ => exp (-(s : ℂ)) * s / ((s : ℂ) ^ 2 + x ^ 2)) 0 hx
    rw [mul_zero] at h
    rw [← smul_inv_smul₀ hx.ne' (∫ s : ℝ in Ioi 0, exp (-(s : ℂ)) * s / ((s : ℂ) ^ 2 + x ^ 2)),
      ← h, ← integral_smul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    have hne : (u : ℂ) ^ 2 + 1 ≠ 0 := by
      have : ((u ^ 2 + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : u ^ 2 + 1 ≠ 0)
      push_cast at this; exact this
    rw [Complex.real_smul]
    push_cast
    rw [show ((x : ℂ) * u) ^ 2 + x ^ 2 = x ^ 2 * (u ^ 2 + 1) by ring, neg_mul]
    field_simp
  rw [h1, h2]
  exact (expIntAux_ofReal_laplace_Ioi hx).2

/-- Holomorphy on the slit plane of `z ↦ ∫₀^∞ K₀(2√(zt)) wt(t) dt` for a bounded continuous `wt`. -/
theorem differentiableOn_integral_besselK_zero_mul {wt : ℝ → ℂ} (hwc : Continuous wt)
    (hw1 : ∀ t, ‖wt t‖ ≤ 1) :
    DifferentiableOn ℂ (fun z : ℂ => ∫ t : ℝ in Ioi 0,
      besselK 0 (2 * (z * t) ^ (1 / 2 : ℂ)) * wt t) slitPlane := by
  refine Complex.differentiableOn_integral_Ioi_of_locally_dominated isOpen_slitPlane 0
    (fun z hz => ?_) ?_ (fun z₀ hz₀ => ?_)
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    have ht0 : (0 : ℝ) < t := ht
    refine ContinuousAt.continuousWithinAt ?_
    have hzt : z * t ∈ slitPlane := mul_ofReal_mem_slitPlane hz ht0
    have hw := two_mul_cpow_half_mem_slitPlane hz ht0
    have hc : ContinuousAt (fun s : ℝ => (s : ℂ)) t := continuous_ofReal.continuousAt
    have hK : ContinuousAt (besselK 0) (2 * (z * t) ^ (1 / 2 : ℂ)) :=
      (differentiableOn_besselK_slitPlane 0).continuousOn.continuousAt
        (isOpen_slitPlane.mem_nhds hw)
    have hin : ContinuousAt (fun s : ℝ => 2 * (z * s) ^ (1 / 2 : ℂ)) t :=
      continuousAt_const.mul ((continuousAt_const.mul hc).cpow continuousAt_const hzt)
    exact (hK.comp (f := fun s : ℝ => 2 * (z * s) ^ (1 / 2 : ℂ)) hin).mul hwc.continuousAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    intro z hz
    have hzt : z * t ∈ slitPlane := mul_ofReal_mem_slitPlane hz ht0
    have hw := two_mul_cpow_half_mem_slitPlane hz ht0
    have hK := (hasDerivAt_besselK 0 hw).differentiableAt
    have hin : DifferentiableAt ℂ (fun z : ℂ => 2 * (z * t) ^ (1 / 2 : ℂ)) z :=
      ((differentiableAt_id.mul_const (t : ℂ)).cpow_const hzt).const_mul 2
    exact ((hK.comp z hin).mul_const _).differentiableWithinAt
  · set c := (z₀ ^ (1 / 2 : ℂ)).re / 2
    have hc0 : 0 < c := half_pos (re_cpow_half_pos_of_mem_slitPlane hz₀)
    have hcont : ContinuousAt (fun z : ℂ => (z ^ (1 / 2 : ℂ)).re) z₀ :=
      continuous_re.continuousAt.comp (continuousAt_id.cpow continuousAt_const hz₀)
    have hV : {z : ℂ | c < (z ^ (1 / 2 : ℂ)).re} ∩ slitPlane ∈ 𝓝 z₀ :=
      Filter.inter_mem (hcont.eventually (lt_mem_nhds (half_lt_self
        (re_cpow_half_pos_of_mem_slitPlane hz₀)))) (isOpen_slitPlane.mem_nhds hz₀)
    have hs : (0 : ℝ) < 1 / 2 := by norm_num
    have hνs : |(0 : ℂ).re| ≤ 1 / 2 := by norm_num
    refine ⟨_, hV, fun t => Real.Gamma (1 / 2) * (c / 2) ^ (-(1 / 2 : ℝ)) *
        (t ^ (-(1 / 4 : ℝ)) * Real.exp (-c * t ^ (1 / 2 : ℝ))),
      (integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) hc0).const_mul _, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
    have ht0 : (0 : ℝ) < t := ht
    have hzs : z ∈ slitPlane := hz.2
    have hzc : c < (z ^ (1 / 2 : ℂ)).re := hz.1
    have hz0 := slitPlane_ne_zero hzs
    have hsq := Real.sqrt_pos.mpr ht0
    have hre := re_two_mul_cpow_half_mul_ofReal hz0 ht0
    have hrepos : 0 < (2 * (z * t) ^ (1 / 2 : ℂ)).re := by rw [hre]; nlinarith
    have hKb := norm_besselK_le_exp hrepos hs hνs
    have hge : Real.sqrt t * c / 2 ≤ (2 * (z * t) ^ (1 / 2 : ℂ)).re / 4 := by
      rw [hre]; nlinarith
    have hge' : Real.sqrt t * c ≤ (2 * (z * t) ^ (1 / 2 : ℂ)).re / 2 := by
      rw [hre]; nlinarith
    have hpow : ((2 * (z * t) ^ (1 / 2 : ℂ)).re / 4) ^ (-(1 / 2 : ℝ)) ≤
        (Real.sqrt t * c / 2) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hge (by norm_num)
    have hsplit : (Real.sqrt t * c / 2) ^ (-(1 / 2 : ℝ)) =
        t ^ (-(1 / 4 : ℝ)) * (c / 2) ^ (-(1 / 2 : ℝ)) := by
      rw [mul_div_assoc, Real.mul_rpow hsq.le (by positivity), Real.sqrt_eq_rpow,
        ← Real.rpow_mul ht0.le]
      norm_num
    have hexp : Real.exp (-((2 * (z * t) ^ (1 / 2 : ℂ)).re / 2)) ≤
        Real.exp (-c * t ^ (1 / 2 : ℝ)) := by
      rw [Real.exp_le_exp, ← Real.sqrt_eq_rpow]; linarith
    have hG : 0 ≤ Real.Gamma (1 / 2) := (Real.Gamma_pos_of_pos hs).le
    rw [norm_mul]
    calc ‖besselK 0 (2 * (z * t) ^ (1 / 2 : ℂ))‖ * ‖wt t‖
        ≤ ‖besselK 0 (2 * (z * t) ^ (1 / 2 : ℂ))‖ * 1 := by gcongr; exact hw1 t
      _ ≤ Real.exp (-c * t ^ (1 / 2 : ℝ)) *
            (Real.Gamma (1 / 2) * (t ^ (-(1 / 4 : ℝ)) * (c / 2) ^ (-(1 / 2 : ℝ)))) := by
          rw [mul_one]
          refine hKb.trans (mul_le_mul hexp (mul_le_mul_of_nonneg_left (hpow.trans hsplit.le) hG)
            (by positivity) (Real.exp_pos _).le)
      _ = _ := by ring

/-- Identity-theorem extension from the positive axis for the Bessel-`K₀` integrals. -/
theorem eqOn_slitPlane_of_ofReal_besselK_zero {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f slitPlane)
    {wt : ℝ → ℂ} (hwc : Continuous wt) (hw1 : ∀ t, ‖wt t‖ ≤ 1)
    (hx : ∀ x : ℝ, 0 < x → f x =
      2 * ∫ t : ℝ in Ioi 0, besselK 0 (2 * ((x : ℂ) * t) ^ (1 / 2 : ℂ)) * wt t)
    {z : ℂ} (hz : z ∈ slitPlane) :
    f z = 2 * ∫ t : ℝ in Ioi 0, besselK 0 (2 * (z * t) ^ (1 / 2 : ℂ)) * wt t := by
  have hf' : AnalyticOnNhd ℂ f slitPlane := hf.analyticOnNhd isOpen_slitPlane
  have hg : AnalyticOnNhd ℂ (fun z : ℂ => 2 * ∫ t : ℝ in Ioi 0,
      besselK 0 (2 * (z * t) ^ (1 / 2 : ℂ)) * wt t) slitPlane :=
    ((differentiableOn_integral_besselK_zero_mul hwc hw1).const_mul 2).analyticOnNhd
      isOpen_slitPlane
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), f w =
      2 * ∫ t : ℝ in Ioi 0, besselK 0 (2 * (w * t) ^ (1 / 2 : ℂ)) * wt t := by
    have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] 1) (𝓝[≠] (1 : ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact ((continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds).trans (by simp)
      · filter_upwards [self_mem_nhdsWithin] with r hr
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, ofReal_eq_one] using hr
    apply ht.frequently
    apply Eventually.frequently
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one' ℝ))] with r hr
    exact hx r hr
  exact hf'.eqOn_of_preconnected_of_frequently_eq hg
    (starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected
    one_mem_slitPlane hfreq hz

end BesselKZeroIntegrals

/-- expIntAuxF besselK integral. -/
@[dlmf 6.7.E15]
theorem expIntAuxF_besselK_integral {z : ℂ} (hz : z ∈ slitPlane) :
    expIntAuxF z = 2*∫ t : ℝ in Ioi 0, DLMF.Bessel.besselK 0 (2*(z*t)^(1/2 : ℂ))*cos t :=
  eqOn_slitPlane_of_ofReal_besselK_zero (fun w hw => (hasDerivAt_expIntAuxF hw).differentiableAt
    |>.differentiableWithinAt) (by fun_prop) norm_cos_ofReal_le_one
    (fun x hx => expIntAuxF_ofReal_eq_integral_besselK hx) hz

/-- expIntAuxG oscillatory integral. -/
@[dlmf 6.7.E14]
theorem expIntAuxG_oscillatory_integral {z : ℂ} (hz : z ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => (cos (t : ℂ))/(t+z)) 0 (expIntAuxG z) := by
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun t : ℝ => cos z*cosInt (z+t)+sin z*sinIntTail (z+t))
      ((cos (t : ℂ))/(t+z)) t := by
    intro t ht
    have hm := add_ofReal_mem_slitPlane hz ht
    have h0 := slitPlane_ne_zero hm
    have hG : HasDerivAt (fun w => cos z*cosInt w+sin z*sinIntTail w)
        (cos z*(cos (z+t)/(z+t))+sin z*(sin (z+t)/(z+t))) (z+t) :=
      ((hasDerivAt_cosInt_complex hm).const_mul _).add (((hasDerivAt_sinInt_complex h0).sub_const _).const_mul _)
    refine (hasDerivAt_comp_add_ofReal hG).congr_deriv ?_
    have hs : cos (t:ℂ) = cos (z+t)*cos z+sin (z+t)*sin z := by
      rw [← Complex.cos_sub]; ring_nf
    rw [hs, add_comm (t:ℂ) z]
    field_simp
  have hc : ContinuousOn (fun t : ℝ => (cos (t : ℂ))/(t+z)) (Ici 0) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => by
      rw [add_comm]; exact slitPlane_ne_zero (add_ofReal_mem_slitPlane hz ht)
  have hl : Tendsto (fun t : ℝ => cos z*cosInt (z+t)+sin z*sinIntTail (z+t)) atTop (𝓝 0) := by
    simpa using ((tendsto_cosInt_add_ofReal z).const_mul (cos z)).add
      ((tendsto_sinIntTail_add_ofReal z).const_mul (sin z))
  have h := hasIntegralAtTop_of_hasDerivAt_of_tendsto hd hc hl
  convert h using 1
  simp [expIntAuxG]; ring

/-- expIntAuxG laplace integral. -/
@[dlmf 6.7.E14]
theorem expIntAuxG_laplace_integral {z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    HasIntegralAtTop (fun t : ℝ => (t : ℂ)^1*exp (-z*t)/((t : ℂ)^2+1)) 0 (expIntAuxG z) :=
  (expIntAux_laplace_hasIntegralAtTop hz0 hz).2.congr fun t _ => by simp

/-- expIntAuxG besselK integral. -/
@[dlmf 6.7.E16]
theorem expIntAuxG_besselK_integral {z : ℂ} (hz : z ∈ slitPlane) :
    expIntAuxG z = 2*∫ t : ℝ in Ioi 0, DLMF.Bessel.besselK 0 (2*(z*t)^(1/2 : ℂ))*sin t :=
  eqOn_slitPlane_of_ofReal_besselK_zero (fun w hw => (hasDerivAt_expIntAuxG hw).differentiableAt
    |>.differentiableWithinAt) (by fun_prop) norm_sin_ofReal_le_one
    (fun x hx => expIntAuxG_ofReal_eq_integral_besselK hx) hz

section InequalityTools

/-- The real part of `E₁` on the positive axis has derivative `-e^{-t}/t`. -/
theorem eiIn_hasDerivAt_re {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => (genExpIntE 1 s).re) (-(Real.exp (-t)/t)) t := by
  have hs : (t:ℂ) ∈ slitPlane := ofReal_mem_slitPlane.2 ht
  have h := (hasDerivAt_genExpIntE 1 hs).real_of_complex
  convert h using 1
  rw [show (1:ℂ)-1 = 0 by norm_num, genExpIntE_zero_eq, ← ofReal_neg, ← ofReal_exp,
    ← ofReal_div, neg_re, ofReal_re]

/-- `E₁(t) → 0` along the positive axis (real part). -/
theorem eiIn_tendsto_re :
    Tendsto (fun s : ℝ => (genExpIntE 1 s).re) atTop (𝓝 0) := by
  have h := (Complex.continuous_re.tendsto 0).comp (tendsto_expIntE1_add_ofReal 0)
  simpa [Function.comp_def] using h

/-- A function with negative derivative on `(0,∞)` and limit `0` at `+∞` is positive. -/
theorem eiIn_pos_of_deriv_neg {g g' : ℝ → ℝ} {x : ℝ} (hx : 0 < x)
    (hd : ∀ t, 0 < t → HasDerivAt g (g' t) t) (hneg : ∀ t, 0 < t → g' t < 0)
    (hlim : Tendsto g atTop (𝓝 0)) : 0 < g x := by
  have hanti : StrictAntiOn g (Ici x) := by
    refine strictAntiOn_of_deriv_neg (convex_Ici x)
      (fun t ht => (hd t (lt_of_lt_of_le hx ht)).continuousAt.continuousWithinAt) ?_
    intro t ht
    rw [interior_Ici] at ht
    have ht0 : 0 < t := lt_trans hx ht
    rw [(hd t ht0).deriv]; exact hneg t ht0
  have h1 : g (x+1) < g x := hanti (le_refl x) (by simp) (by linarith)
  have h2 : 0 ≤ g (x+1) := by
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop (x+1)] with s hs
    exact hanti.antitoneOn (show x ≤ x+1 by linarith) (show x ≤ s by linarith) hs
  linarith

/-- Comparison principle for `f(x) = eˣE₁(x)`, which solves `f' = f - 1/x`: if `R - R' - 1/t < 0`
on `(0,∞)` and `R → 0`, then `R < f`. -/
theorem eiIn_lt_of_sub_neg {R R' : ℝ → ℝ} {x : ℝ} (hx : 0 < x)
    (hd : ∀ t, 0 < t → HasDerivAt R (R' t) t) (hs : ∀ t, 0 < t → R t - R' t - 1/t < 0)
    (hlim : Tendsto R atTop (𝓝 0)) : R x < Real.exp x*(genExpIntE 1 x).re := by
  have key : 0 < (genExpIntE 1 x).re - Real.exp (-x)*R x := by
    refine eiIn_pos_of_deriv_neg (g := fun t => (genExpIntE 1 t).re - Real.exp (-t)*R t)
      (g' := fun t => Real.exp (-t)*(R t - R' t - 1/t)) hx ?_ ?_ ?_
    · intro t ht
      have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
        simpa using (hasDerivAt_neg t).exp
      refine ((eiIn_hasDerivAt_re ht).sub (he.mul (hd t ht))).congr_deriv ?_
      field_simp; ring
    · intro t ht; exact mul_neg_of_pos_of_neg (Real.exp_pos _) (hs t ht)
    · have h0 : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero
      simpa using eiIn_tendsto_re.sub (h0.mul hlim)
  have := mul_lt_mul_of_pos_left key (Real.exp_pos x)
  rw [mul_sub, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at this
  linarith

/-- Comparison principle, upper form: if `R - R' - 1/t > 0` on `(0,∞)` and `R → 0`, then
`eˣE₁(x) < R(x)`. -/
theorem eiIn_gt_of_sub_pos {R R' : ℝ → ℝ} {x : ℝ} (hx : 0 < x)
    (hd : ∀ t, 0 < t → HasDerivAt R (R' t) t) (hs : ∀ t, 0 < t → 0 < R t - R' t - 1/t)
    (hlim : Tendsto R atTop (𝓝 0)) : Real.exp x*(genExpIntE 1 x).re < R x := by
  have key : 0 < Real.exp (-x)*R x - (genExpIntE 1 x).re := by
    refine eiIn_pos_of_deriv_neg (g := fun t => Real.exp (-t)*R t - (genExpIntE 1 t).re)
      (g' := fun t => -(Real.exp (-t)*(R t - R' t - 1/t))) hx ?_ ?_ ?_
    · intro t ht
      have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
        simpa using (hasDerivAt_neg t).exp
      refine ((he.mul (hd t ht)).sub (eiIn_hasDerivAt_re ht)).congr_deriv ?_
      field_simp; ring
    · intro t ht; exact neg_neg_of_pos (mul_pos (Real.exp_pos _) (hs t ht))
    · have h0 : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero
      simpa using (h0.mul hlim).sub eiIn_tendsto_re
  have := mul_lt_mul_of_pos_left key (Real.exp_pos x)
  rw [mul_sub, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at this
  linarith


/-- `ln y < (y - 1/y)/2` for `y > 1`. -/
theorem eiIn_log_lt_half_sub_recip {y : ℝ} (hy : 1 < y) : Real.log y < (y - 1/y)/2 := by
  let h : ℝ → ℝ := fun s => (s - 1/s)/2 - Real.log s
  have hmono : StrictMonoOn h (Ici 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 1) ?_ ?_
    · intro s hs
      have hs0 : s ≠ 0 := by simp at hs; linarith
      exact (((continuousAt_id.sub (continuousAt_const.div continuousAt_id hs0)).div_const 2).sub
        (Real.continuousAt_log hs0)).continuousWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      have hs1 : 1 < s := hs
      have hs0 : s ≠ 0 := by linarith
      have hd : HasDerivAt h (((1 - (-(1:ℝ)/s^2)))/2 - 1/s) s := by
        have h1 : HasDerivAt (fun s : ℝ => 1/s) (-(1:ℝ)/s^2) s := by
          simpa [one_div, neg_div] using hasDerivAt_inv hs0
        exact (((hasDerivAt_id s).sub h1).div_const 2).sub (by simpa [one_div] using Real.hasDerivAt_log hs0)
      rw [hd.deriv, show ((1 - (-(1:ℝ)/s^2)))/2 - 1/s = (s-1)^2/(2*s^2) by field_simp; ring]
      have : 0 < s - 1 := by linarith
      positivity
  have := hmono (le_refl (1:ℝ)) (show (1:ℝ) ≤ y from hy.le) hy
  simp only [h, div_one, sub_self, zero_div, Real.log_one] at this
  linarith

/-- `t⁻¹ → 0` packaged for rational limits. -/
theorem eiIn_tendsto_rat {F : ℝ → ℝ} {R : ℝ → ℝ} (hF : ContinuousAt F 0) (hF0 : F 0 = 0)
    (hR : ∀ t : ℝ, 0 < t → R t = F t⁻¹) : Tendsto R atTop (𝓝 0) := by
  have h := hF.tendsto.comp (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0))
  rw [hF0] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  exact (hR t ht).symm

end InequalityTools

/-- expIntE1 inequality 1. -/
@[dlmf 6.8.E1]
theorem expIntE1_inequality_1 {x : ℝ} (hx : 0 < x) :
    Real.log (1+2/x)/2 < Real.exp x*(genExpIntE 1 x).re ∧ Real.exp x*(genExpIntE 1 x).re < Real.log (1+1/x) := by
  constructor
  · refine eiIn_lt_of_sub_neg (R := fun t => Real.log (1+2/t)/2) (R' := fun t => -(1/(t*(t+2)))) hx ?_ ?_ ?_
    · intro t ht
      have h1 : (1:ℝ)+2/t ≠ 0 := by positivity
      have hd : HasDerivAt (fun s : ℝ => 1+2/s) (-(2:ℝ)/t^2) t := by
        simpa [div_eq_mul_inv] using ((hasDerivAt_inv ht.ne').const_mul (2:ℝ)).const_add 1
      refine ((hd.log h1).div_const 2).congr_deriv ?_
      field_simp
    · intro t ht
      have hl := eiIn_log_lt_half_sub_recip (y := 1+2/t) (by linarith [show 0 < 2/t by positivity])
      have : (1+2/t - 1/(1+2/t))/2 = 2*(t+1)/(t*(t+2)) := by field_simp; ring
      have h2 : -(1/(t*(t+2))) = -(2/(2*t*(t+2))) := by field_simp
      rw [this] at hl
      have : Real.log (1+2/t)/2 - -(1/(t*(t+2))) - 1/t = (Real.log (1+2/t) - 2*(t+1)/(t*(t+2)))/2 := by
        field_simp; ring
      rw [this]; linarith
    · refine eiIn_tendsto_rat (F := fun u => Real.log (1+2*u)/2) ?_ (by simp) fun t ht => by
        simp [div_eq_mul_inv]
      exact ((Real.continuousAt_log (by norm_num)).comp (by fun_prop)).div_const 2
  · refine eiIn_gt_of_sub_pos (R := fun t => Real.log (1+1/t)) (R' := fun t => -(1/(t*(t+1)))) hx ?_ ?_ ?_
    · intro t ht
      have h1 : (1:ℝ)+1/t ≠ 0 := by positivity
      have hd : HasDerivAt (fun s : ℝ => 1+1/s) (-(1:ℝ)/t^2) t := by
        simpa [one_div, neg_div] using (hasDerivAt_inv ht.ne').const_add 1
      refine (hd.log h1).congr_deriv ?_
      field_simp
    · intro t ht
      have hy : 0 < 1/(1+1/t) := by positivity
      have hy1 : 1/(1+1/t) ≠ 1 := by
        rw [Ne, div_eq_one_iff_eq (by positivity)]; intro h
        have : 0 < 1/t := by positivity
        linarith
      have hl := Real.log_lt_sub_one_of_pos hy hy1
      rw [Real.log_div (by norm_num) (by positivity), Real.log_one, zero_sub] at hl
      have : 1/(1+1/t) - 1 = -(1/(t+1)) := by field_simp; ring
      rw [this] at hl
      have : Real.log (1+1/t) - -(1/(t*(t+1))) - 1/t = Real.log (1+1/t) - 1/(t+1) := by
        field_simp; ring
      rw [this]; linarith
    · refine eiIn_tendsto_rat (F := fun u => Real.log (1+u)) ?_ (by simp) fun t ht => by
        simp [div_eq_mul_inv]
      exact (Real.continuousAt_log (by norm_num)).comp (by fun_prop)

/-- expIntE1 inequality 2. -/
@[dlmf 6.8.E2]
theorem expIntE1_inequality_2 {x : ℝ} (hx : 0 < x) :
    x/(x+1) < x*Real.exp x*(genExpIntE 1 x).re ∧ x*Real.exp x*(genExpIntE 1 x).re < (x+1)/(x+2) := by
  have hlo : 1/(x+1) < Real.exp x*(genExpIntE 1 x).re := by
    refine eiIn_lt_of_sub_neg (R := fun t => 1/(t+1)) (R' := fun t => -(1/(t+1)^2)) hx ?_ ?_ ?_
    · intro t ht
      have h0 : t+1 ≠ 0 := by positivity
      refine (((hasDerivAt_id t).add_const 1).inv h0).congr_deriv ?_ |>.congr_of_eventuallyEq ?_
      · simp only [id]; field_simp
      · filter_upwards with s; simp [one_div]
    · intro t ht
      rw [show 1/(t+1) - -(1/(t+1)^2) - 1/t = -(1/(t*(t+1)^2)) by field_simp; ring]
      have : 0 < 1/(t*(t+1)^2) := by positivity
      linarith
    · exact eiIn_tendsto_rat (F := fun u => u/(1+u)) (by fun_prop (disch := norm_num)) (by simp)
        fun t ht => by field_simp
  have hhi : Real.exp x*(genExpIntE 1 x).re < (x+1)/(x*(x+2)) := by
    refine eiIn_gt_of_sub_pos (R := fun t => (t+1)/(t*(t+2))) (R' := fun t => (1*(t*(t+2)) - (t+1)*(2*t+2))/(t*(t+2))^2) hx ?_ ?_ ?_
    · intro t ht
      have h0 : t*(t+2) ≠ 0 := by positivity
      have hn : HasDerivAt (fun s : ℝ => s+1) 1 t := (hasDerivAt_id t).add_const 1
      have hd : HasDerivAt (fun s : ℝ => s*(s+2)) (2*t+2) t := by
        refine ((hasDerivAt_id t).mul ((hasDerivAt_id t).add_const 2)).congr_deriv ?_
        simp; ring
      exact hn.div hd h0
    · intro t ht
      rw [show (t+1)/(t*(t+2)) - (1*(t*(t+2)) - (t+1)*(2*t+2))/(t*(t+2))^2 - 1/t
        = 2/(t^2*(t+2)^2) by field_simp; ring]
      positivity
    · exact eiIn_tendsto_rat (F := fun u => u*(1+u)/(1+2*u)) (by fun_prop (disch := norm_num)) (by simp)
        fun t ht => by field_simp
  constructor
  · have := mul_lt_mul_of_pos_left hlo hx
    rw [mul_assoc]; convert this using 1; field_simp
  · have := mul_lt_mul_of_pos_left hhi hx
    rw [mul_assoc]; convert this using 1; field_simp

/-- expIntE1 inequality 3. -/
@[dlmf 6.8.E3]
theorem expIntE1_inequality_3 {x : ℝ} (hx : 0 < x) :
    x*(x+3)/(x^2+4*x+2) < x*Real.exp x*(genExpIntE 1 x).re ∧ x*Real.exp x*(genExpIntE 1 x).re < (x^2+5*x+2)/(x^2+6*x+6) := by
  have hlo : (x+3)/(x^2+4*x+2) < Real.exp x*(genExpIntE 1 x).re := by
    refine eiIn_lt_of_sub_neg (R := fun t => (t+3)/(t^2+4*t+2)) (R' := fun t => (1*(t^2+4*t+2) - (t+3)*(2*t+4))/(t^2+4*t+2)^2) hx ?_ ?_ ?_
    · intro t ht
      have h0 : t^2+4*t+2 ≠ 0 := by positivity
      have hn : HasDerivAt (fun s : ℝ => s+3) 1 t := (hasDerivAt_id t).add_const 3
      have hd : HasDerivAt (fun s : ℝ => s^2+4*s+2) (2*t+4) t := by
        refine ((((hasDerivAt_id t).pow 2).add ((hasDerivAt_id t).const_mul 4)).add_const 2).congr_deriv ?_
        simp
      exact hn.div hd h0
    · intro t ht
      rw [show (t+3)/(t^2+4*t+2) - (1*(t^2+4*t+2) - (t+3)*(2*t+4))/(t^2+4*t+2)^2 - 1/t
        = -(4/(t*(t^2+4*t+2)^2)) by field_simp; ring]
      have : 0 < 4/(t*(t^2+4*t+2)^2) := by positivity
      linarith
    · exact eiIn_tendsto_rat (F := fun u => u*(1+3*u)/(1+4*u+2*u^2)) (by fun_prop (disch := norm_num))
        (by simp) fun t ht => by field_simp
  have hhi : Real.exp x*(genExpIntE 1 x).re < (x^2+5*x+2)/(x*(x^2+6*x+6)) := by
    refine eiIn_gt_of_sub_pos (R := fun t => (t^2+5*t+2)/(t*(t^2+6*t+6))) (R' := fun t => ((2*t+5)*(t*(t^2+6*t+6)) - (t^2+5*t+2)*(3*t^2+12*t+6))/(t*(t^2+6*t+6))^2) hx ?_ ?_ ?_
    · intro t ht
      have h0 : t*(t^2+6*t+6) ≠ 0 := by positivity
      have hn : HasDerivAt (fun s : ℝ => s^2+5*s+2) (2*t+5) t := by
        refine ((((hasDerivAt_id t).pow 2).add ((hasDerivAt_id t).const_mul 5)).add_const 2).congr_deriv ?_
        simp
      have hd : HasDerivAt (fun s : ℝ => s*(s^2+6*s+6)) (3*t^2+12*t+6) t := by
        refine ((hasDerivAt_id t).mul ((((hasDerivAt_id t).pow 2).add
          ((hasDerivAt_id t).const_mul 6)).add_const 6)).congr_deriv ?_
        simp; ring
      exact hn.div hd h0
    · intro t ht
      rw [show (t^2+5*t+2)/(t*(t^2+6*t+6)) - ((2*t+5)*(t*(t^2+6*t+6)) - (t^2+5*t+2)*(3*t^2+12*t+6))/(t*(t^2+6*t+6))^2 - 1/t
        = 12/(t^2*(t^2+6*t+6)^2) by field_simp; ring]
      positivity
    · exact eiIn_tendsto_rat (F := fun u => u*(1+5*u+2*u^2)/(1+6*u+6*u^2)) (by fun_prop (disch := norm_num))
        (by simp) fun t ht => by field_simp
  constructor
  · have := mul_lt_mul_of_pos_left hlo hx
    rw [mul_assoc]; convert this using 1; field_simp
  · have := mul_lt_mul_of_pos_left hhi hx
    rw [mul_assoc]; convert this using 1; field_simp

/-- expIntE1 continuedFraction. -/
@[dlmf 6.9.E1]
theorem expIntE1_continuedFraction {z : ℂ} (hz : z ∈ slitPlane) :
    HasContinuedFraction (fun k => if k=0 then exp (-z) else ((k+1)/2 : ℕ)) (fun k => if Even k then z else 1) (genExpIntE 1 z) := by
  have hc : ∀ k, 1 ≤ k → (((k + 1) / 2 : ℕ) : ℂ) = (incGF_c 0 k : ℂ) := by
    intro k _
    unfold incGF_c
    split_ifs with h
    · have : (k + 1) / 2 = k / 2 + 1 := by omega
      rw [this]; push_cast; ring
    · have : (k + 1) / 2 = k / 2 := by omega
      rw [this]; push_cast; ring
  rw [incGF_hasContinuedFraction_iff (fun k hk => by
    simp only [show k ≠ 0 by omega, ↓reduceIte]
    exact Nat.cast_ne_zero.mpr (by omega))]
  have h := incGF_formB_tendsto (α := 0) (by norm_num) (exp (-z)) hz
    (a := fun k => if k=0 then exp (-z) else (((k+1)/2 : ℕ) : ℂ)) (by simp)
    (fun k hk => by simp only [show k ≠ 0 by omega, ↓reduceIte]; exact hc k hk)
  convert h using 2
  rw [genExpIntE]
  simp only [sub_self, cpow_zero, one_mul, ofReal_zero, neg_zero, mul_one]
  rw [← exp_add, neg_add_cancel, exp_zero, one_mul]

end DLMF.Confluent
