/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ErrorFunctions.IntegralTools
public import DLMF.Bessel.KMellin

/-!
# Gaussian and Cauchy representations of error functions

Quadratic Gaussian integrals, Faddeeva Cauchy transforms and their analytic continuation.

Source references and common attribution are retained in
`DLMF.ErrorFunctions.Integrals`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Confluent

/-- The principal square root `(π/a)^{1/2} = √π / a^{1/2}` for `Re a > 0`. -/
theorem cpow_half_pi_div {a : ℂ} (ha : 0 < a.re) : (π/a)^(1/2 : ℂ) = Real.sqrt π/a^(1/2 : ℂ) := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hrre : 0 < (a^(1/2 : ℂ)).re := re_cpow_half_pos ha
  have hr0 : a^(1/2 : ℂ) ≠ 0 := fun h => by rw [h] at hrre; simp at hrre
  have hps : (Real.sqrt π:ℂ)^2 = π := by exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have hre : 0 < ((Real.sqrt π:ℂ)/a^(1/2 : ℂ)).re := by
    rw [div_re]; simp only [ofReal_re, ofReal_im, zero_mul]
    have := Real.sqrt_pos.mpr Real.pi_pos
    have : 0 < normSq (a^(1/2 : ℂ)) := normSq_pos.mpr hr0
    positivity
  rw [← sq_cpow_half hre, div_pow, hps, cpow_half_sq ha0]

/-- `erfc (r t + w) → 0` as `t → ∞` when `Re r > 0` and `Re r² > 0`. -/
theorem tendsto_erfc_mul_add_atTop {r : ℂ} (hr : 0 < r.re) (hr2 : 0 < (r^2).re) (w : ℂ) :
    Tendsto (fun t : ℝ => erfc (r*t+w)) atTop (𝓝 0) := by
  refine tendsto_erfc_zero_of_re ?_ ?_
  · simp only [add_re, re_mul_ofReal]
    exact tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop' hr)
  · have he (t : ℝ) : ((r*(t:ℂ)+w)^2).re = t*((r^2).re*t+2*(r*w).re) + (w^2).re := by
      have : (r*(t:ℂ)+w)^2 = (t:ℂ)*(r^2*t+2*(r*w)) + w^2 := by ring
      rw [this]; simp [mul_re]
    simp_rw [he]
    refine tendsto_atTop_add_const_right _ _ (tendsto_id.atTop_mul_atTop₀ ?_)
    exact tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop' hr2)

/-- The `erfc` antiderivative of the complex Gaussian `exp (-(a t² + 2 b t + c))`. -/
theorem hasDerivAt_gaussianQuadratic {a : ℂ} (ha : 0 < a.re) (b c : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => -(Real.sqrt π/(2*a^(1/2 : ℂ)))*exp ((b^2-a*c)/a)*
      erfc (a^(1/2 : ℂ)*t+b/a^(1/2 : ℂ))) (exp (-(a*(t : ℂ)^2+2*b*t+c))) t := by
  set r := a^(1/2 : ℂ) with hr
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hr2 : r^2 = a := cpow_half_sq ha0
  have hrre : 0 < r.re := re_cpow_half_pos ha
  have hr0 : r ≠ 0 := fun h => by simp [h] at hrre
  have hp0 : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h1 : HasDerivAt (fun t : ℝ => r*(t:ℂ)+b/r) r t := by
    simpa using ((hasDerivAt_id (t:ℂ)).const_mul r).add_const (b/r) |>.comp_ofReal
  have h2 := (hasDerivAt_erf_complex (r*t+b/r)).comp t h1
  have h3 : HasDerivAt (fun t : ℝ => erfc (r*t+b/r)) (-(2/Real.sqrt π*exp (-(r*t+b/r)^2)*r)) t := by
    simpa [erfc, Function.comp_def] using h2.const_sub 1
  convert h3.const_mul (-(Real.sqrt π/(2*r))*exp ((b^2-a*c)/a)) using 1
  have he : exp (-(a*(t : ℂ)^2+2*b*t+c)) = exp ((b^2-a*c)/a) * exp (-(r*t+b/r)^2) := by
    rw [← Complex.exp_add]; congr 1
    field_simp; rw [← hr2]; ring
  rw [he]; field_simp

/-- In the open sector `|arg a| < π/4`, `Re a² > 0`. -/
theorem re_sq_pos_of_abs_arg_lt {a : ℂ} (ha0 : a ≠ 0) (ha : |arg a| < π/4) : 0 < (a^2).re := by
  have h := norm_sq_mul_cos_le_re_sq (z := a) (α := |arg a|) (by linarith [Real.pi_pos]) le_rfl
  have hc : 0 < Real.cos (2*|arg a|) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [abs_nonneg (arg a), Real.pi_pos], by linarith⟩
  have := norm_pos_iff.mpr ha0
  exact lt_of_lt_of_le (by positivity) h

/-- Derivative of `erfc (a t + c/t)` along the positive real axis. -/
theorem hasDerivAt_erfc_mul_add_div (a c : ℂ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun t : ℝ => erfc (a*t+c/t))
      (-(2/Real.sqrt π*exp (-(a*t+c/t)^2)*(a-c/(t:ℂ)^2))) t := by
  have ht' : (t:ℂ) ≠ 0 := by exact_mod_cast ht
  have h1 : HasDerivAt (fun w : ℂ => a*w+c/w) (a-c/(t:ℂ)^2) (t:ℂ) := by
    have := ((hasDerivAt_id (t:ℂ)).const_mul a).add ((hasDerivAt_inv ht').const_mul c)
    convert this using 1
    · funext w; simp [div_eq_mul_inv]
    · simp; ring
  have h2 := (hasDerivAt_erf_complex _).comp t (h1.comp_ofReal)
  simpa [erfc, Function.comp_def] using h2.const_sub 1

/-- `erfc (c x + d/x) → 0` as `x → 0⁺` when `Re d > 0` and `Re d² > 0`. -/
theorem tendsto_erfc_mul_add_div_nhdsGT (c : ℂ) {d : ℂ} (hd : 0 < d.re) (hd2 : 0 < (d^2).re) :
    Tendsto (fun x : ℝ => erfc (c*x+d/x)) (𝓝[>] 0) (𝓝 0) := by
  have hinv : Tendsto (fun x : ℝ => x⁻¹) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero
  have hx0 : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  refine tendsto_erfc_zero_of_re ?_ ?_
  · have h1 : Tendsto (fun x : ℝ => c.re*x) (𝓝[>] 0) (𝓝 0) := by
      simpa using hx0.const_mul c.re
    have : Tendsto (fun x : ℝ => d.re*x⁻¹ + c.re*x) (𝓝[>] 0) atTop :=
      (hinv.const_mul_atTop hd).atTop_add h1
    refine this.congr' ?_
    filter_upwards with x
    rw [add_re, div_ofReal_re, re_mul_ofReal]; ring
  · have h1 : Tendsto (fun x : ℝ => (c^2).re*x^2 + 2*(c*d).re) (𝓝[>] 0) (𝓝 (2*(c*d).re)) := by
      simpa using ((hx0.pow 2).const_mul (c^2).re).add_const (2*(c*d).re)
    have : Tendsto (fun x : ℝ => (d^2).re*(x⁻¹)^2 + ((c^2).re*x^2 + 2*(c*d).re)) (𝓝[>] 0) atTop :=
      (((tendsto_pow_atTop two_ne_zero).comp hinv).const_mul_atTop hd2).atTop_add h1
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : (x:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
    have : (c*(x:ℂ)+d/x)^2 = c^2*((x^2:ℝ):ℂ) + 2*(c*d) + d^2/((x^2:ℝ):ℂ) := by
      push_cast; field_simp; ring
    rw [this]
    simp only [add_re, div_ofReal_re]
    rw [mul_comm (c^2), re_ofReal_mul]
    simp; ring

/-- Where `Re z > 0` and `Re z² > 0`, `‖erf z‖ ≤ 2`. -/
theorem norm_erf_le_two {z : ℂ} (hz : 0 < z.re) (hz2 : 0 < (z^2).re) : ‖erf z‖ ≤ 2 := by
  have h := norm_erfc_le_one hz hz2
  have : erf z = 1 - erfc z := by simp [erfc]
  rw [this]
  calc ‖1 - erfc z‖ ≤ ‖(1:ℂ)‖ + ‖erfc z‖ := norm_sub_le _ _
    _ ≤ 2 := by simp; linarith

/-- On the ray `b t`, `t > 0`, inside `|arg b| < π/4`, both positivity hypotheses hold. -/
theorem re_mul_ofReal_pos_and_sq {b : ℂ} (hb0 : b ≠ 0) (hb : |arg b| < π/4) {t : ℝ} (ht : 0 < t) :
    0 < (b*t).re ∧ 0 < ((b*t)^2).re := by
  have hbr : 0 < b.re := re_pos_of_abs_arg_lt hb0 (by linarith [Real.pi_pos])
  have hb2 := re_sq_pos_of_abs_arg_lt hb0 hb
  constructor
  · rw [re_mul_ofReal]; positivity
  · rw [mul_pow, ← ofReal_pow, re_mul_ofReal]; positivity

/-- A Gaussian majorant for `erfc (b t)`, `t > 0`, inside `|arg b| < π/4`. -/
theorem exists_norm_erfc_mul_le {b : ℂ} (hb0 : b ≠ 0) (hb : |arg b| < π/4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ‖erfc (b*t)‖ ≤ C*Real.exp (-(b^2).re*t^2) := by
  have hb2 := re_sq_pos_of_abs_arg_lt hb0 hb
  set β := (b^2).re
  refine ⟨Real.exp β + 1/Real.sqrt (π*β), by positivity, fun t ht => ?_⟩
  obtain ⟨h1, h2⟩ := re_mul_ofReal_pos_and_sq hb0 hb ht
  have hre : ((b*t)^2).re = β*t^2 := by rw [mul_pow, ← ofReal_pow, re_mul_ofReal]
  have hpos : 0 < Real.exp (-β*t^2) := Real.exp_pos _
  rcases le_or_gt t 1 with h | h
  · refine (norm_erfc_le_one h1 h2).trans ?_
    have : 1 ≤ Real.exp β*Real.exp (-β*t^2) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      have : t^2 ≤ 1 := by nlinarith
      nlinarith
    nlinarith [show 0 ≤ 1/Real.sqrt (π*β)*Real.exp (-β*t^2) by positivity]
  · refine (norm_erfc_le h1 h2).trans ?_
    rw [Complex.norm_exp, neg_re, hre]
    have hs : Real.sqrt (π*β) ≤ Real.sqrt (π*(β*t^2)) :=
      Real.sqrt_le_sqrt (by have := Real.pi_pos; nlinarith [mul_pos hb2 (show 0 < t^2-1 by nlinarith)])
    have hs0 : 0 < Real.sqrt (π*β) := Real.sqrt_pos.mpr (by positivity)
    calc Real.exp (-(β*t^2))/Real.sqrt (π*(β*t^2)) ≤ Real.exp (-(β*t^2))/Real.sqrt (π*β) := by
          gcongr
      _ ≤ _ := by
          rw [show -(β*t^2) = -β*t^2 by ring, div_eq_mul_one_div, mul_comm]
          nlinarith [Real.exp_pos β]

/-- The Gaussian quadratic tail integral (used before DLMF 7.7.6 is stated). -/
lemma gaussian_quadratic_tail_aux {a : ℂ} (ha : 0 < a.re) (b c : ℂ) (x : ℝ) :
    (∫ t : ℝ in Ioi x, exp (-(a*(t : ℂ)^2+2*b*t+c)))=(π/a)^(1/2 : ℂ)/2*exp ((b^2-a*c)/a)*erfc (a^(1/2 : ℂ)*x+b/a^(1/2 : ℂ)) := by
  have hint : IntegrableOn (fun t : ℝ => exp (-(a*(t : ℂ)^2+2*b*t+c))) (Ioi x) := by
    have := integrable_cexp_quadratic ha (-2*b) (-c)
    refine this.integrableOn.congr_fun (fun t _ => ?_) measurableSet_Ioi
    ring_nf
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hlim := ((tendsto_erfc_mul_add_atTop (re_cpow_half_pos ha)
    (by rw [cpow_half_sq ha0]; exact ha) (b/a^(1/2 : ℂ))).const_mul
    (-(Real.sqrt π/(2*a^(1/2 : ℂ)))*exp ((b^2-a*c)/a)))
  rw [mul_zero] at hlim
  rw [integral_Ioi_of_hasDerivAt_of_tendsto
    (hasDerivAt_gaussianQuadratic ha b c x).continuousAt.continuousWithinAt
    (fun t _ => hasDerivAt_gaussianQuadratic ha b c t) hint hlim, cpow_half_pi_div ha]
  ring

/-- DLMF 7.7.1 where `Re w > 0` and `Re w² > 0`, from the Laplace form with `u = t²`. -/
theorem erfc_rational_gaussian_of_re_pos {w : ℂ} (hw : 0 < w.re) (hw2 : 0 < (w^2).re) :
    erfc w=2/π*exp (-w^2)*(∫ t : ℝ in Ioi 0, exp (-w^2*(t : ℂ)^2)/((t : ℂ)^2+1)) := by
  rw [erfc_eq_laplace hw hw2]
  have hc := integral_comp_rpow_Ioi_of_pos (p := 2) (g := fun u : ℝ =>
    exp (-w^2*(u:ℂ)) * (u:ℂ)^(-1/2:ℂ) * (1+(u:ℂ))^(-1:ℂ)) two_pos
  rw [← hc]
  have he : (∫ x in Ioi (0:ℝ), ((2:ℝ) * x ^ ((2:ℝ) - 1)) • (exp (-w^2*((x^(2:ℝ):ℝ):ℂ)) *
      ((x^(2:ℝ):ℝ):ℂ)^(-1/2:ℂ) * (1+((x^(2:ℝ):ℝ):ℂ))^(-1:ℂ))) =
      2 * ∫ t : ℝ in Ioi 0, exp (-w^2*(t : ℂ)^2)/((t : ℂ)^2+1) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx : (0:ℝ) < x := hx
    have hx2 : ((x^(2:ℝ):ℝ):ℂ) = (x:ℂ)^2 := by
      rw [Real.rpow_two]; push_cast; ring
    rw [hx2, show (-1/2:ℂ) = -(1/2) by ring, cpow_neg, sq_cpow_half (by simpa using hx),
      cpow_neg_one, show (2:ℝ)-1 = 1 by norm_num, Real.rpow_one, real_smul]
    have hx0 : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    have h1 : (1+(x:ℂ)^2) ≠ 0 := by
      have : (0:ℝ) < 1+x^2 := by positivity
      exact_mod_cast this.ne'
    push_cast
    rw [add_comm (1:ℂ)] at h1 ⊢
    field_simp
  rw [he]
  ring
/-- `erfc (f t) → 0` when eventually `Re f > 0` and `Re f² → +∞`. -/
theorem tendsto_erfc_zero_of_re_sq {α : Type*} {l : Filter α} {f : α → ℂ}
    (h1 : ∀ᶠ t in l, 0 < (f t).re) (h2 : Tendsto (fun t => ((f t)^2).re) l atTop) :
    Tendsto (fun t => erfc (f t)) l (𝓝 0) := by
  have hev : ∀ᶠ t in l, ‖erfc (f t)‖ ≤ Real.exp (-((f t)^2).re)/Real.sqrt π := by
    filter_upwards [h1, h2.eventually_ge_atTop 1] with t ht1 ht2
    refine (norm_erfc_le ht1 (by linarith)).trans ?_
    rw [Complex.norm_exp, neg_re]
    gcongr
    nlinarith [Real.pi_pos]
  refine squeeze_zero_norm' hev ?_
  have := (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h2)).div_const (Real.sqrt π)
  simpa using this

/-- If `Re q² > 0`, `Re q > 0`, `Re p > 0` and `Re p² > 0`, then `Re (q p) > 0`. -/
theorem re_mul_pos_of_re_sq_pos {p q : ℂ} (hq : 0 < q.re) (hq2 : 0 < (q^2).re) (hp : 0 < p.re)
    (hp2 : 0 ≤ (p^2).re) : 0 < (q*p).re := by
  have e1 : (q^2).re = q.re^2 - q.im^2 := by simp [sq]
  have e2 : (p^2).re = p.re^2 - p.im^2 := by simp [sq]
  rw [mul_re]
  have hlt : (q.im*p.im)^2 < (q.re*p.re)^2 := by
    rw [mul_pow, mul_pow]
    have : 0 < p.re^2 := by positivity
    have h3 : q.im^2*p.im^2 ≤ q.im^2*p.re^2 := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    nlinarith
  have := abs_lt_of_sq_lt_sq hlt (by positivity)
  linarith [le_abs_self (q.im*p.im)]

/-- Identity under the stated parameter and domain assumptions: `erfc z=2/π*exp (-z^2)*(∫ t : ℝ in
Ioi 0, exp (-z^2*(t : ℂ)^2)/((t : ℂ)^2+1))`. -/
@[dlmf 7.7.E1]
theorem erfc_rational_gaussian_integral {z : ℂ} (hz : |arg z| ≤ π/4) :
    erfc z=2/π*exp (-z^2)*(∫ t : ℝ in Ioi 0, exp (-z^2*(t : ℂ)^2)/((t : ℂ)^2+1)) := by
  have hre : 0 ≤ z.re := by
    rw [← Complex.norm_mul_cos_arg z]
    exact mul_nonneg (norm_nonneg _) (Real.cos_nonneg_of_mem_Icc ⟨by linarith [neg_abs_le (arg z),
      Real.pi_pos], by linarith [le_abs_self (arg z), Real.pi_pos]⟩)
  have hre2 : 0 ≤ (z^2).re := by
    have h := norm_sq_mul_cos_le_re_sq (by linarith [Real.pi_pos]) hz
    rwa [show 2*(π/4) = π/2 by ring, Real.cos_pi_div_two, mul_zero] at h
  set F : ℂ → ℂ := fun w => ∫ t : ℝ in Ioi 0, exp (-w^2*(t : ℂ)^2)/((t : ℂ)^2+1)
  have hpos : ∀ ε : ℝ, 0 < ε → 0 < (z+ε).re ∧ 0 < ((z+ε)^2).re := by
    intro ε hε
    constructor
    · simp; linarith
    · have : ((z+ε)^2).re = (z^2).re + 2*ε*z.re + ε^2 := by
        simp [sq, mul_re]; ring
      rw [this]; positivity
  have hnorm : ∀ w : ℂ, 0 ≤ (w^2).re → ∀ t : ℝ,
      ‖exp (-w^2*(t : ℂ)^2)/((t : ℂ)^2+1)‖ ≤ (1+t^2)⁻¹ := by
    intro w hw t
    have h1 : ((t:ℂ)^2+1) = ((1+t^2:ℝ):ℂ) := by push_cast; ring
    rw [h1, norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity), Complex.norm_exp,
      div_eq_mul_inv]
    have : (-w^2*(t:ℂ)^2).re ≤ 0 := by
      rw [← ofReal_pow, re_mul_ofReal, neg_re]; nlinarith [sq_nonneg t]
    have := Real.exp_le_one_iff.mpr this
    have : 0 ≤ (1+t^2)⁻¹ := by positivity
    nlinarith
  have hF : Tendsto (fun ε : ℝ => F (z+ε)) (𝓝[>] 0) (𝓝 (F z)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => (1+t^2)⁻¹) ?_ ?_
      integrable_inv_one_add_sq.integrableOn ?_
    · refine Eventually.of_forall fun ε => ContinuousOn.aestronglyMeasurable (fun t _ => ?_) measurableSet_Ioi
      have h1 : ((t:ℂ)^2+1) ≠ 0 := by
        have : (0:ℝ) < 1+t^2 := by positivity
        rw [show ((t:ℂ)^2+1) = ((1+t^2:ℝ):ℂ) by push_cast; ring]; exact_mod_cast this.ne'
      exact (ContinuousAt.continuousWithinAt (by fun_prop (disch := exact h1)))
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact Eventually.of_forall fun t => hnorm _ (hpos ε hε).2.le t
    · refine Eventually.of_forall fun t => ?_
      have : Continuous fun ε : ℝ => exp (-(z+ε)^2*(t : ℂ)^2)/((t : ℂ)^2+1) := by fun_prop
      have h := this.tendsto 0
      simp only [ofReal_zero, add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
  have hL : Tendsto (fun ε : ℝ => erfc (z+ε)) (𝓝[>] 0) (𝓝 (erfc z)) := by
    have hc : Continuous fun ε : ℝ => erfc (z+ε) := by
      unfold erfc; have := differentiable_erf_complex.continuous; fun_prop
    have h := hc.tendsto 0
    simp only [ofReal_zero, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hR : Tendsto (fun ε : ℝ => 2/π*exp (-(z+ε)^2)*F (z+ε)) (𝓝[>] 0)
      (𝓝 (2/π*exp (-z^2)*F z)) := by
    have hc : Continuous fun ε : ℝ => exp (-(z+ε)^2) := by fun_prop
    have h := hc.tendsto 0
    simp only [ofReal_zero, add_zero] at h
    exact ((h.mono_left nhdsWithin_le_nhds).const_mul _).mul hF
  have heq : (fun ε : ℝ => erfc (z+ε)) =ᶠ[𝓝[>] 0] fun ε => 2/π*exp (-(z+ε)^2)*F (z+ε) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact erfc_rational_gaussian_of_re_pos (hpos ε hε).1 (hpos ε hε).2
  exact tendsto_nhds_unique hL (hR.congr' heq.symm)

/-! ### Tools for DLMF 7.7.2 -/

/-- `1/(t-z) = i ∫₀^∞ e^{i(z-t)s} ds` for `Im z > 0`. -/
theorem erfInt_recip_sub_eq_integral {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    1/((t:ℂ)-z) = I * ∫ s in Ioi (0:ℝ), exp (I*(z-t)*s) := by
  have hre : (I*(z-t)).re < 0 := by simp; linarith
  have hne : z - (t:ℂ) ≠ 0 := fun h => by
    have := congrArg im h; simp at this; linarith
  rw [integral_exp_mul_complex_Ioi hre 0]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  have hne' : (t:ℂ) - z ≠ 0 := fun h => hne (by linear_combination -h)
  field_simp
  ring_nf

/-- The Gaussian Fourier integral `∫ e^{-t²} e^{-its} dt = √π e^{-s²/4}`. -/
theorem erfInt_gauss_fourier (s : ℝ) :
    ∫ t : ℝ, exp (-(t:ℂ)^2) * exp (-I*s*t) = Real.sqrt π * exp (-(s:ℂ)^2/4) := by
  have h := integral_cexp_quadratic (b := -1) (by simp) (-I*s) 0
  have hc : (π / -(-1:ℂ)) ^ (1/2:ℂ) = Real.sqrt π := by
    rw [neg_neg, div_one, show (1/2:ℂ) = ((1/2:ℝ):ℂ) by push_cast; ring,
      ← ofReal_cpow Real.pi_pos.le, ← Real.sqrt_eq_rpow]
  rw [hc] at h
  have e : (∫ t : ℝ, exp (-(t:ℂ)^2) * exp (-I*s*t)) =
      ∫ x : ℝ, cexp (-1 * (x:ℂ) ^ 2 + -I * s * x + 0) := by
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only; rw [← Complex.exp_add]; congr 1; ring
  rw [e, h]
  congr 1; congr 1
  ring_nf; rw [I_sq]; ring

/-- `√π ∫₀^∞ e^{izs} e^{-s²/4} ds = π w(z)`. -/
theorem erfInt_half_line_faddeeva (z : ℂ) :
    ∫ s in Ioi (0:ℝ), exp (I*z*s) * (Real.sqrt π * exp (-(s:ℂ)^2/4)) = π * faddeevaW z := by
  have h := gaussian_quadratic_tail_aux (a := 1/4) (by norm_num) (-I*z/2) 0 0
  have h4 : ((1/4:ℂ))^(1/2:ℂ) = 1/2 := by
    have := sq_cpow_half (x := (1/2:ℂ)) (by norm_num); norm_num at this ⊢; exact this
  rw [cpow_half_pi_div (by norm_num), h4] at h
  have e : (∫ s in Ioi (0:ℝ), exp (I*z*s) * (Real.sqrt π * exp (-(s:ℂ)^2/4))) =
      Real.sqrt π * ∫ t : ℝ in Ioi 0, exp (-(1/4*(t:ℂ)^2+2*(-I*z/2)*t+0)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [mul_left_comm, ← Complex.exp_add]; congr 2; ring
  rw [e, h, faddeevaW]
  have hπ : (Real.sqrt π : ℂ)^2 = π := by exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have e1 : ((-I*z/2)^2 - 1/4*0)/(1/4) = -z^2 := by ring_nf; rw [I_sq]; ring
  have e2 : (1/2:ℂ)*((0:ℝ):ℂ) + (-I*z/2)/(1/2) = -I*z := by push_cast; ring
  rw [e1, e2]
  linear_combination (exp (-z^2) * erfc (-I*z)) * hπ

/-- **DLMF 7.7.2, first form**: `∫_{-∞}^{∞} e^{-t²}/(t-z) dt = πi w(z)` for `Im z > 0`. -/
theorem erfInt_faddeeva_cauchy {z : ℂ} (hz : 0 < z.im) :
    ∫ t : ℝ, exp (-(t : ℂ)^2)/(t-z) = π*I*faddeevaW z := by
  set F : ℝ → ℝ → ℂ := fun t s => exp (-(t:ℂ)^2) * exp (I*(z-t)*s) with hF
  have hint : Integrable (Function.uncurry F) (volume.prod (volume.restrict (Ioi 0))) := by
    have h1 : Integrable (fun t : ℝ => Real.exp (-1 * t^2)) := integrable_exp_neg_mul_sq one_pos
    have h2 : Integrable (fun s : ℝ => Real.exp (-z.im * s)) (volume.restrict (Ioi 0)) :=
      exp_neg_integrableOn_Ioi 0 hz
    refine (h1.mul_prod h2).mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact (by fun_prop : Continuous (Function.uncurry F)).aestronglyMeasurable
    · simp only [Function.uncurry, hF, norm_mul, Complex.norm_exp]
      gcongr
      · simp [← ofReal_pow]
      · simp
  have hinner : ∀ t : ℝ, exp (-(t : ℂ)^2)/(t-z) = I * ∫ s in Ioi (0:ℝ), F t s := by
    intro t
    rw [div_eq_mul_one_div, erfInt_recip_sub_eq_integral hz t, hF]
    simp only
    rw [integral_const_mul]; ring
  simp_rw [hinner]
  rw [integral_const_mul, integral_integral_swap hint]
  have hs : ∀ s : ℝ, ∫ t : ℝ, F t s = exp (I*z*s) * (Real.sqrt π * exp (-(s:ℂ)^2/4)) := by
    intro s
    rw [← erfInt_gauss_fourier s, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hF]
    rw [mul_left_comm, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1; ring
  simp_rw [hs]
  rw [erfInt_half_line_faddeeva]; ring

/-- `e^{-t²}/(t-z)` is integrable on `ℝ` for `Im z > 0`. -/
theorem erfInt_integrable_gauss_div {z : ℂ} (hz : 0 < z.im) :
    Integrable (fun t : ℝ => exp (-(t : ℂ)^2)/(t-z)) := by
  have hne : ∀ t : ℝ, (t:ℂ) - z ≠ 0 := fun t h => by
    have := congrArg im h; simp at this; linarith
  have h1 : Integrable (fun t : ℝ => Real.exp (-1 * t^2) / z.im) :=
    (integrable_exp_neg_mul_sq one_pos).div_const _
  refine h1.mono' ?_ (Eventually.of_forall fun t => ?_)
  · exact (Continuous.div (by fun_prop) (by fun_prop) hne).aestronglyMeasurable
  · rw [norm_div, Complex.norm_exp]
    have hle : z.im ≤ ‖(t:ℂ) - z‖ := by
      have := abs_im_le_norm ((t:ℂ) - z)
      rw [sub_im, ofReal_im, zero_sub, abs_neg] at this
      exact (le_abs_self _).trans this
    have : (-(t:ℂ)^2).re = -1 * t^2 := by simp [← ofReal_pow]
    rw [this]
    gcongr

/-- **DLMF 7.7.2** (both forms). -/
theorem erfInt_faddeeva_cauchy_both {z : ℂ} (hz : 0 < z.im) :
    (∫ t : ℝ, exp (-(t : ℂ)^2)/(t-z))=π*I*faddeevaW z ∧
      (∫ t : ℝ in Ioi 0, exp (-(t : ℂ)^2)/((t : ℂ)^2-z^2))=π*I/(2*z)*faddeevaW z := by
  refine ⟨erfInt_faddeeva_cauchy hz, ?_⟩
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hne : ∀ t : ℝ, (t:ℂ) - z ≠ 0 := fun t h => by
    have := congrArg im h; simp at this; linarith
  have hne' : ∀ t : ℝ, (t:ℂ) + z ≠ 0 := fun t h => by
    have := congrArg im h; simp at this; linarith
  set g : ℝ → ℂ := fun t => exp (-(t : ℂ)^2)/(t-z) with hg
  have hgi := erfInt_integrable_gauss_div hz
  have hg2 : Integrable (fun t : ℝ => exp (-(t : ℂ)^2)/(t+z)) := by
    have := (hgi.comp_neg).neg
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.neg_apply, ofReal_neg, neg_sq]
    rw [show -(t:ℂ) - z = -((t:ℂ)+z) by ring, div_neg, neg_neg]
  have hsplit : (∫ t : ℝ in Ioi 0, exp (-(t : ℂ)^2)/((t : ℂ)^2-z^2)) =
      1/(2*z) * ((∫ t : ℝ in Ioi 0, g t) - ∫ t : ℝ in Ioi 0, exp (-(t : ℂ)^2)/(t+z)) := by
    rw [← integral_sub hgi.integrableOn hg2.integrableOn, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    have h1 := hne t
    have h2 := hne' t
    have h3 : (t:ℂ)^2 - z^2 ≠ 0 := by
      rw [show (t:ℂ)^2 - z^2 = ((t:ℂ)-z)*((t:ℂ)+z) by ring]; exact mul_ne_zero h1 h2
    field_simp
    ring
  have hneg : (∫ t : ℝ in Ioi 0, exp (-(t : ℂ)^2)/(t+z)) = -∫ t : ℝ in Iic 0, g t := by
    have := integral_comp_neg_Ioi (0:ℝ) g
    simp only [neg_zero] at this
    rw [← this, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [hg, ofReal_neg, neg_sq]
    rw [show -(t:ℂ) - z = -((t:ℂ)+z) by ring, div_neg, neg_neg]
  rw [hsplit, hneg, sub_neg_eq_add, add_comm,
    intervalIntegral.integral_Iic_add_Ioi hgi.integrableOn hgi.integrableOn,
    erfInt_faddeeva_cauchy hz]
  field_simp

/-- Identity under the stated parameter and domain assumptions: `(∫ t : ℝ, exp (-(t :
ℂ)^2)/(t-z))=π*I*faddeevaW z ∧ (∫ t : ℝ in Ioi 0, exp (-(t : ℂ)^2)/((t :
ℂ)^2-z^2))=π*I/(2*z)*faddeevaW z`. -/
@[dlmf 7.7.E2]
theorem faddeevaW_cauchy_integral {z : ℂ} (hz : 0 < z.im) :
    (∫ t : ℝ, exp (-(t : ℂ)^2)/(t-z))=π*I*faddeevaW z ∧ (∫ t : ℝ in Ioi 0, exp (-(t : ℂ)^2)/((t : ℂ)^2-z^2))=π*I/(2*z)*faddeevaW z :=
  erfInt_faddeeva_cauchy_both hz

/-- The Gaussian rational integral with numerator `2t` is an exponential integral. -/
theorem erfInt_goodwin_gaussian_e1 {z : ℂ} (hr : 0 < z.re) (hi : 0 < z.im) :
    (∫ t : ℝ in Ioi 0, (2*(t:ℂ))*exp (-(t:ℂ)^2)/((t:ℂ)^2-z^2)) =
      exp (-z^2)*genExpIntE 1 (-z^2) := by
  have hzi : 0 < (z^2).im := by
    simp only [pow_two, mul_im]
    positivity
  have hm : -z^2 ∈ slitPlane := Or.inr (by simpa using hzi.ne')
  have hne (u : ℝ) : (u:ℂ)-z^2 ≠ 0 := by
    intro h
    have := congrArg im h
    simp only [sub_im, ofReal_im, zero_sub, zero_im, neg_eq_zero] at this
    exact hzi.ne' this
  have hbound (u : ℝ) : (z^2).im ≤ ‖(u:ℂ)-z^2‖ := by
    have h := abs_im_le_norm ((u:ℂ)-z^2)
    simpa [abs_of_pos hzi] using h
  have hint : IntegrableOn (fun u : ℝ => exp (-(u:ℂ))/((u:ℂ)-z^2)) (Ioi 0) := by
    refine ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0:ℝ) < 1)).div_const (z^2).im).mono' ?_ ?_
    · exact (Continuous.div (by fun_prop) (by fun_prop) hne).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun u _ => ?_)
      simp only [norm_div, Complex.norm_exp, neg_re, ofReal_re]
      simpa using div_le_div_of_nonneg_left (Real.exp_pos (-u)).le hzi (hbound u)
  have hH := (expIntE1_horizontal_integral hm).const_mul (exp (-z^2))
  have hH' : HasIntegralAtTop (fun u : ℝ => exp (-(u:ℂ))/((u:ℂ)-z^2)) 0
      (exp (-z^2)*genExpIntE 1 (-z^2)) := hH.congr fun u _ => by
    rw [← mul_div_assoc, ← Complex.exp_add,
      show -z^2 + -(-z^2+(u:ℂ)) = -(u:ℂ) by ring,
      show -z^2+(u:ℂ) = (u:ℂ)-z^2 by ring]
  have he := tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id) hH'
  have hsub := integral_comp_rpow_Ioi_of_pos (p := 2)
    (g := fun u : ℝ => exp (-(u:ℂ))/((u:ℂ)-z^2)) (by norm_num)
  rw [← he, ← hsub]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [Real.rpow_two, show (2:ℝ)-1 = 1 by norm_num, Real.rpow_one, real_smul,
    ofReal_mul, ofReal_ofNat, ofReal_pow]
  ring

/-- Splitting the nonsingular upper-half-plane kernels gives the Goodwin integral. -/
theorem goodwinStatonG_eq_E1_of_re_pos_of_im_pos {z : ℂ} (hr : 0 < z.re) (hi : 0 < z.im) :
    goodwinStatonG z = exp (-z^2)/2*genExpIntE 1 (-z^2)-π*I/2*faddeevaW z := by
  let A := ∫ t : ℝ in Ioi 0, exp (-(t:ℂ)^2)/((t:ℂ)-z)
  have hA := (erfInt_integrable_gauss_div hi).integrableOn (s := Ioi (0:ℝ))
  have hB := goodwinStatonG_integrable (z := z) (Or.inl hr)
  have hne (t : ℝ) : (t:ℂ)-z ≠ 0 := by
    intro h
    have := congrArg im h
    simp at this
    exact hi.ne' this
  have hne' (t : ℝ) : (t:ℂ)+z ≠ 0 := by
    intro h
    have := congrArg im h
    simp at this
    exact hi.ne' this
  have hsum : A + goodwinStatonG z = exp (-z^2)*genExpIntE 1 (-z^2) := by
    dsimp only [A]
    rw [goodwinStatonG, ← integral_add hA hB, ← erfInt_goodwin_gaussian_e1 hr hi]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have hden : (t:ℂ)^2-z^2 ≠ 0 := by
      rw [sq_sub_sq]; exact mul_ne_zero (hne' t) (hne t)
    field_simp [hne t, hne' t]
    ring
  have hneg : (∫ t : ℝ in Iic 0, exp (-(t:ℂ)^2)/((t:ℂ)-z)) = -goodwinStatonG z := by
    have h := integral_comp_neg_Ioi (0:ℝ) (fun t : ℝ => exp (-(t:ℂ)^2)/((t:ℂ)-z))
    simp only [neg_zero] at h
    rw [← h, goodwinStatonG, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [ofReal_neg, neg_sq]
    rw [show -(t:ℂ)-z = -((t:ℂ)+z) by ring, div_neg]
  have hdiff : A-goodwinStatonG z = π*I*faddeevaW z := by
    dsimp only [A]
    rw [sub_eq_add_neg, ← hneg, add_comm,
      intervalIntegral.integral_Iic_add_Ioi (erfInt_integrable_gauss_div hi).integrableOn hA,
      erfInt_faddeeva_cauchy hi]
  linear_combination (hsum-hdiff)/2

/-- The principal logarithm needed when approaching the positive axis from above. -/
theorem erfInt_goodwin_log_neg_sq {z : ℂ} (hr : 0 < z.re) (hi : 0 < z.im) :
    log (-z^2) = 2*log z-π*I := by
  have hz : z ≠ 0 := fun h => by simp [h] at hr
  have ha : 0 < arg z := lt_of_le_of_ne (arg_nonneg_iff.mpr hi.le)
    (fun h => hi.ne' (arg_eq_zero_iff.mp h.symm).2)
  have hb : arg z < π/2 := arg_lt_pi_div_two_iff.mpr (Or.inl hr)
  have he : exp (2*log z-π*I) = -z^2 := by
    rw [Complex.exp_sub, show (2:ℂ)*log z=(2:ℕ)*log z by norm_num, Complex.exp_nat_mul, Complex.exp_log hz, Complex.exp_pi_mul_I]
    ring
  rw [← he, Complex.log_exp]
  · simp [mul_im, log_im]; linarith
  · simp [mul_im, log_im]; linarith [Real.pi_pos]

/-- Goodwin's logarithmic expression before taking the real boundary value. -/
theorem goodwinStatonG_eq_Ein_of_re_pos_of_im_pos {z : ℂ} (hr : 0 < z.re) (hi : 0 < z.im) :
    goodwinStatonG z = Real.sqrt π*dawsonF z - exp (-z^2)/2*
      (Real.eulerMascheroniConstant+2*log z-expIntEin (-z^2)) := by
  have hz : z ≠ 0 := fun h => by simp [h] at hr
  rw [goodwinStatonG_eq_E1_of_re_pos_of_im_pos hr hi, expIntE1_eq_Ein_complex (neg_ne_zero.mpr (pow_ne_zero 2 hz)),
    erfInt_goodwin_log_neg_sq hr hi, (dawsonF_faddeeva z).1]
  have hsq : (Real.sqrt π:ℂ)^2 = π := by exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  linear_combination -(I/2*(exp (-z^2)-faddeevaW z))*hsq

/-- Dominated continuity of the defining integral along a vertical line in the right half-plane. -/
theorem tendsto_goodwinStatonG_vertical {x : ℝ} (hx : 0 < x) :
    Tendsto (fun ε : ℝ => goodwinStatonG ((x:ℂ)+I*ε)) (𝓝 0) (𝓝 (goodwinStatonG x)) := by
  unfold goodwinStatonG
  refine tendsto_integral_filter_of_dominated_convergence (fun t => Real.exp (-t^2)/x)
    (Eventually.of_forall fun ε => (goodwinStatonG_integrable (z := (x:ℂ)+I*ε)
      (Or.inl (by simpa using hx))).aestronglyMeasurable) ?_ ?_ ?_
  · refine Eventually.of_forall fun ε => (ae_restrict_iff' measurableSet_Ioi).mpr
      (ae_of_all _ fun t ht => ?_)
    have hb : x ≤ ‖(t:ℂ)+((x:ℂ)+I*ε)‖ := by
      have h := re_le_norm ((t:ℂ)+((x:ℂ)+I*ε))
      simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, zero_mul,
        sub_zero, add_zero] at h
      have ht : 0 < t := ht
      linarith
    rw [norm_div, Complex.norm_exp]
    simp only [← ofReal_pow, neg_re, ofReal_re]
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le hx hb
  · convert ((integrable_exp_neg_mul_sq one_pos).div_const x).integrableOn (s := Ioi (0:ℝ)) using 1; norm_num [IntegrableOn]
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
    have ht : 0 < t := ht
    have hn : (t:ℂ)+(x:ℂ) ≠ 0 := by exact_mod_cast (show t+x ≠ 0 by linarith)
    have hc : ContinuousAt (fun ε : ℝ => exp (-(t:ℂ)^2)/((t:ℂ)+((x:ℂ)+I*ε))) 0 := by
      apply ContinuousAt.div continuousAt_const (by fun_prop)
      simpa using hn
    simpa using hc.tendsto

/-- The Goodwin–Staton integral in terms of Dawson's function and the exponential integral. -/
@[dlmf 7.5.E13]
theorem goodwinStatonG_dawson {x : ℝ} (hx : 0 < x) :
    goodwinStatonG x=Real.sqrt π*dawsonF x-Real.exp (-x^2)/2*Real.expIntEi (x^2) := by
  let p : ℝ → ℂ := fun ε => (x:ℂ)+I*ε
  let F : ℂ → ℂ := fun z => Real.sqrt π*dawsonF z - exp (-z^2)/2*
    (Real.eulerMascheroniConstant+2*log z-expIntEin (-z^2))
  have hp : Continuous p := by dsimp [p]; fun_prop
  have hlog : ContinuousAt (fun ε => log (p ε)) 0 := by
    apply ContinuousAt.comp (g := log) ?_ hp.continuousAt
    apply continuousAt_clog
    left
    simpa [p] using hx
  have hc : ContinuousAt (fun ε => F (p ε)) 0 := by
    have hD : Continuous (fun ε => dawsonF (p ε)) := dawsonF_entire.continuous.comp hp
    have hE : Continuous (fun ε => expIntEin (-(p ε)^2)) :=
      expIntEin_entire.continuous.comp (by fun_prop)
    dsimp only [F]
    exact (continuousAt_const.mul hD.continuousAt).sub
      ((show ContinuousAt (fun ε => exp (-(p ε)^2)/2) 0 by fun_prop).mul
        ((continuousAt_const.add (continuousAt_const.mul hlog)).sub hE.continuousAt))
  have hR : Tendsto (fun ε => F (p ε)) (𝓝 0) (𝓝 (F x)) := by
    simpa [p] using hc.tendsto
  have he : (fun ε : ℝ => goodwinStatonG (p ε)) =ᶠ[𝓝[>] 0] fun ε => F (p ε) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    apply goodwinStatonG_eq_Ein_of_re_pos_of_im_pos
    · simpa [p] using hx
    · simpa [p] using hε
  have h := tendsto_nhds_unique ((tendsto_goodwinStatonG_vertical hx).mono_left nhdsWithin_le_nhds)
    ((hR.mono_left nhdsWithin_le_nhds).congr' he.symm)
  have hEi : (Real.expIntEi (x^2):ℂ) =
      Real.eulerMascheroniConstant+2*log (x:ℂ)-expIntEin (-(x:ℂ)^2) := by
    have he := Real.expIntEi_Ein (sq_pos_of_pos hx) (ε := 1) (Or.inl rfl)
    simp only [one_mul, neg_one_mul] at he
    rw [Real.log_pow] at he
    rw [← ofReal_log hx.le]
    rw [show -(x:ℂ)^2 = ((-x^2:ℝ):ℂ) by push_cast; rfl, expIntEin_ofReal]
    push_cast at he ⊢
    linear_combination he
  rw [h]
  dsimp only [F]
  rw [← hEi]
  push_cast
  rfl
/-- Identity under the stated parameter and domain assumptions: `(∫ t : ℝ in Ioi 0, exp (-a*(t :
ℂ)^2+2*I*z*t))=(π/a)^(1/2 : ℂ)/2*exp (-z^2/a)+I/a^(1/2 : ℂ)*dawsonF (z/a^(1/2 : ℂ))`. -/
@[dlmf 7.7.E3]
theorem gaussian_fourier_halfLine {a : ℂ} (ha : 0 < a.re) (z : ℂ) :
    (∫ t : ℝ in Ioi 0, exp (-a*(t : ℂ)^2+2*I*z*t))=(π/a)^(1/2 : ℂ)/2*exp (-z^2/a)+I/a^(1/2 : ℂ)*dawsonF (z/a^(1/2 : ℂ)) := by
  have h := gaussian_quadratic_tail_aux ha (-I*z) 0 0
  have hi : (fun t : ℝ => exp (-a*(t : ℂ)^2+2*I*z*t)) =
      fun t : ℝ => exp (-(a*(t : ℂ)^2+2*(-I*z)*t+0)) := by
    funext t; congr 1; ring
  rw [hi, h, cpow_half_pi_div ha]
  set r := a^(1/2 : ℂ)
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hr2 : r^2 = a := cpow_half_sq ha0
  have hrre : 0 < r.re := re_cpow_half_pos ha
  have hr0 : r ≠ 0 := fun h => by simp [h] at hrre
  have hp0 : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  set w := z/r
  have hD := (dawsonF_faddeeva w).2
  have hw : ((-I*z)^2-a*0)/a = -w^2 := by
    simp only [w]; rw [← hr2]; field_simp; ring_nf; rw [I_sq]; ring
  have harg : r*((0:ℝ):ℂ)+(-I*z)/r = -(I*w) := by simp only [w]; push_cast; ring
  have hza : -z^2/a = -w^2 := by simp only [w]; rw [← hr2]; field_simp
  rw [hw, harg, hza, erfc_negative, hD]
  have he : exp (-w^2)*exp (w^2) = 1 := by rw [← Complex.exp_add]; simp
  simp only [erfc]
  field_simp
  linear_combination erf (w*I)*I_sq

/-- Identity under the stated parameter and domain assumptions: `(∫ t : ℝ in Ioi 0, exp
(-a*t)/(t+z^2)^(1/2 : ℂ))=(π/a)^(1/2 : ℂ)*exp (a*z^2)*erfc (a^(1/2 : ℂ)*z)`. -/
@[dlmf 7.7.E4]
theorem gaussian_sqrt_laplace {a z : ℂ} (ha : 0 < a.re) (hz : 0 < z.re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)/(t+z^2)^(1/2 : ℂ))=(π/a)^(1/2 : ℂ)*exp (a*z^2)*erfc (a^(1/2 : ℂ)*z) := by
  set w := z^2 with hw
  set q := a^(1/2 : ℂ) with hq
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hq2 : q^2 = a := cpow_half_sq ha0
  have hqre : 0 < q.re := re_cpow_half_pos ha
  have hq0 : q ≠ 0 := fun h => by simp [h] at hqre
  have hp0 : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hmem : ∀ s : ℝ, 0 ≤ s → (s:ℂ) + w ∈ slitPlane := by
    intro s hs
    rw [mem_slitPlane_iff]
    by_cases him : z.im = 0
    · left
      have : w = ((z.re^2:ℝ):ℂ) := by
        rw [hw]; apply Complex.ext <;> simp [sq, him]
      rw [this, ← ofReal_add, ofReal_re]; nlinarith [sq_pos_of_pos hz]
    · right
      simp only [hw, add_im, ofReal_im, zero_add, sq, mul_im]
      intro h
      have : z.re * z.im = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact him h
  set R : ℝ → ℂ := fun s => -((π/a)^(1/2 : ℂ)*erfc (q*((s:ℂ)+w)^(1/2 : ℂ))) with hR
  have hd : ∀ s : ℝ, 0 ≤ s → HasDerivAt R (exp (-a*((s:ℂ)+w))/((s:ℂ)+w)^(1/2 : ℂ)) s := by
    intro s hs
    have hm := hmem s hs
    have h1 : HasDerivAt (fun s : ℝ => ((s:ℂ)+w)^(1/2 : ℂ))
        ((1/2:ℂ)*((s:ℂ)+w)^((1/2:ℂ)-1)*1) s := by
      have := ((hasDerivAt_id (s:ℂ)).add_const w).cpow_const (c := (1/2:ℂ)) hm
      simpa using this.comp_ofReal
    have h2 := (hasDerivAt_erf_complex (q*((s:ℂ)+w)^(1/2 : ℂ))).comp s (h1.const_mul q)
    have h3 := ((h2.const_sub 1).const_mul ((π/a)^(1/2 : ℂ))).neg
    convert h3 using 1
    · funext r; simp [hR, erfc]
    · have hsq : (((s:ℂ)+w)^(1/2 : ℂ))^2 = (s:ℂ)+w := cpow_half_sq (slitPlane_ne_zero hm)
      have hne : ((s:ℂ)+w)^(1/2 : ℂ) ≠ 0 := fun h => by
        rw [h] at hsq; exact slitPlane_ne_zero hm (by rw [← hsq]; ring)
      have hm1 : ((s:ℂ)+w)^((1/2:ℂ)-1) = (((s:ℂ)+w)^(1/2 : ℂ))⁻¹ := by
        rw [show (1/2:ℂ)-1 = -(1/2) by norm_num, cpow_neg]
      rw [hm1, cpow_half_pi_div ha, ← hq, mul_pow, hsq, hq2]
      field_simp
  have hlim : Tendsto R atTop (𝓝 0) := by
    have he : Tendsto (fun s : ℝ => erfc (q*((s:ℂ)+w)^(1/2 : ℂ))) atTop (𝓝 0) := by
      refine tendsto_erfc_zero_of_re_sq ?_ ?_
      · filter_upwards [eventually_ge_atTop (max 0 (-w.re))] with s hs
        have hs0 : 0 ≤ s := le_trans (le_max_left _ _) hs
        have hm := hmem s hs0
        refine re_mul_pos_of_re_sq_pos hqre (by rw [hq2]; exact ha)
          (re_cpow_half_pos_of_mem_slitPlane hm) ?_
        rw [cpow_half_sq (slitPlane_ne_zero hm)]
        simp; linarith [le_max_right 0 (-w.re)]
      · have h0 : Tendsto (fun s : ℝ => a.re*s + (a*w).re) atTop atTop :=
          tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop' ha)
        refine h0.congr' ?_
        filter_upwards [eventually_ge_atTop 0] with s hs
        rw [mul_pow, cpow_half_sq (slitPlane_ne_zero (hmem s hs)), hq2, mul_add, add_re,
          re_mul_ofReal]
    have := he.const_mul ((π/a)^(1/2 : ℂ))
    simpa [hR] using this.neg
  obtain ⟨m, hm0, hmb⟩ : ∃ m : ℝ, 0 < m ∧ ∀ s : ℝ, 0 ≤ s → m ≤ ‖(s:ℂ)+w‖ := by
    rcases mem_slitPlane_iff.mp (by simpa using hmem 0 le_rfl) with h | h
    · refine ⟨w.re, h, fun s hs => ?_⟩
      have := Complex.re_le_norm ((s:ℂ)+w)
      simp only [add_re, ofReal_re] at this
      linarith
    · refine ⟨|w.im|, abs_pos.mpr h, fun s _ => ?_⟩
      have := Complex.abs_im_le_norm ((s:ℂ)+w)
      simpa using this
  have hint : IntegrableOn (fun s : ℝ => exp (-a*((s:ℂ)+w))/((s:ℂ)+w)^(1/2 : ℂ)) (Ioi 0) := by
    have hg : IntegrableOn (fun s : ℝ => Real.exp (-(a*w).re)/Real.sqrt m * Real.exp (-a.re*s))
        (Ioi 0) := (exp_neg_integrableOn_Ioi 0 ha).const_mul _
    refine hg.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun s hs => ?_) measurableSet_Ioi
      have hs : (0:ℝ) < s := hs
      have hm := hmem s hs.le
      refine ContinuousAt.continuousWithinAt ?_
      refine ContinuousAt.div (by fun_prop) ?_ ?_
      · have hc : ContinuousAt (fun y : ℂ => y^(1/2:ℂ)) ((s:ℂ)+w) := continuousAt_cpow_const hm
        exact hc.comp (f := fun s : ℝ => (s:ℂ)+w) (by fun_prop)
      · intro h
        have := cpow_half_sq (slitPlane_ne_zero hm)
        rw [h] at this; exact slitPlane_ne_zero hm (by rw [← this]; ring)
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_)
      have hs : (0:ℝ) < s := hs
      rw [norm_div, Complex.norm_exp, show (1/2:ℂ) = ((1/2:ℝ):ℂ) by push_cast; ring,
        norm_cpow_real, ← Real.sqrt_eq_rpow]
      have hre : (-a*((s:ℂ)+w)).re = -(a*w).re + -a.re*s := by
        rw [neg_mul, neg_re, mul_add, add_re, mul_comm a (s:ℂ), re_ofReal_mul]; ring
      rw [hre, Real.exp_add]
      have hsq : Real.sqrt m ≤ Real.sqrt ‖(s:ℂ)+w‖ := Real.sqrt_le_sqrt (hmb s hs.le)
      have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
      calc Real.exp (-(a*w).re) * Real.exp (-a.re*s) / Real.sqrt ‖(s:ℂ)+w‖
          ≤ Real.exp (-(a*w).re) * Real.exp (-a.re*s) / Real.sqrt m := by gcongr
        _ = _ := by ring
  have hI := integral_Ioi_of_hasDerivAt_of_tendsto (hd 0 le_rfl).continuousAt.continuousWithinAt
    (fun s hs => hd s (le_of_lt hs)) hint hlim
  have hL : (∫ t : ℝ in Ioi 0, exp (-a*t)/(t+z^2)^(1/2 : ℂ)) =
      exp (a*w) * ∫ s : ℝ in Ioi 0, exp (-a*((s:ℂ)+w))/((s:ℂ)+w)^(1/2 : ℂ) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [← hw, mul_div_assoc', ← Complex.exp_add]; congr 2; ring
  rw [hL, hI]
  simp only [hR, ofReal_zero, zero_add, zero_sub, neg_neg, hw, sq_cpow_half hz]
  ring

/-- The parametric integral `∫₀¹ e^{-a(1+t²)}/(1+t²) dt` is entire, with derivative
`-∫₀¹ e^{-a(1+t²)} dt`. -/
theorem hasDerivAt_integral_exp_div_one_add_sq (a0 : ℂ) :
    HasDerivAt (fun a : ℂ => ∫ t : ℝ in (0:ℝ)..1, exp (-a*(1+(t:ℂ)^2))/(1+(t:ℂ)^2))
      (∫ t : ℝ in (0:ℝ)..1, -exp (-a0*(1+(t:ℂ)^2))) a0 := by
  have hpos (t : ℝ) : (1+(t:ℂ)^2) ≠ 0 := by
    have : (1+(t:ℂ)^2) = ((1+t^2:ℝ):ℂ) := by push_cast; ring
    rw [this]; exact_mod_cast (by positivity : (0:ℝ) < 1+t^2).ne'
  set C : ℝ := Real.exp (2*(‖a0‖+1))
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => C)
    (F' := fun a (t : ℝ) => -exp (-a*(1+(t:ℂ)^2))) (Metric.ball_mem_nhds a0 one_pos)
    (Eventually.of_forall fun a => (by fun_prop : Continuous fun t : ℝ =>
      exp (-a*(1+(t:ℂ)^2))/(1+(t:ℂ)^2)).aestronglyMeasurable)
    ((by fun_prop : Continuous fun t : ℝ =>
      exp (-a0*(1+(t:ℂ)^2))/(1+(t:ℂ)^2)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t : ℝ => -exp (-a0*(1+(t:ℂ)^2))).aestronglyMeasurable)
    ?_ intervalIntegrable_const ?_).2
  · refine Eventually.of_forall fun t ht x hx => ?_
    rw [uIoc_of_le zero_le_one] at ht
    rw [norm_neg, Complex.norm_exp]
    refine Real.exp_le_exp.mpr ((re_le_norm _).trans ?_)
    rw [norm_mul, norm_neg]
    have h1 : ‖(1+(t:ℂ)^2)‖ ≤ 2 := by
      rw [show (1+(t:ℂ)^2) = ((1+t^2:ℝ):ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      nlinarith [ht.1, ht.2]
    have h2 : ‖x‖ ≤ ‖a0‖+1 := by
      have := Metric.mem_ball.mp hx
      rw [dist_eq_norm] at this
      linarith [norm_sub_norm_le x a0]
    calc ‖x‖*‖(1+(t:ℂ)^2)‖ ≤ (‖a0‖+1)*2 := by gcongr
      _ = _ := by ring
  · refine Eventually.of_forall fun t _ x _ => ?_
    have h := ((hasDerivAt_id x).neg.mul_const (1+(t:ℂ)^2)).cexp.div_const (1+(t:ℂ)^2)
    refine h.congr_deriv ?_
    simp only [Pi.neg_apply, id_eq]
    field_simp [hpos t]

/-- `∫₀¹ e^{-a t²} dt = (√π/2) erf(√a)/√a` for `a ≠ 0` with `w² = a`. -/
theorem integral_exp_neg_mul_sq_zero_one {w : ℂ} (hw : w ≠ 0) :
    (∫ t : ℝ in (0:ℝ)..1, exp (-w^2*(t:ℂ)^2)) = Real.sqrt π/2*erf w/w := by
  have h := erf_complex_segment_integral w
  have hp : primitive (fun t => exp (-t^2)) w = w*(∫ t : ℝ in 0..1, exp (-((t:ℂ)*w)^2)) := by
    simp [primitive, segmentIntegral]
  rw [hp] at h
  have hsp : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have he : (∫ t : ℝ in (0:ℝ)..1, exp (-((t:ℂ)*w)^2)) = ∫ t : ℝ in (0:ℝ)..1, exp (-w^2*(t:ℂ)^2) := by
    congr 1; funext t; congr 1; ring
  rw [he] at h
  rw [h]; field_simp

/-- Identity under the stated parameter and domain assumptions: `(∫ t : ℝ in 0..1, exp (-a*(t :
ℂ)^2)/((t : ℂ)^2+1))=π/4*exp a*(1-erf (a^(1/2 : ℂ))^2)`. -/
@[dlmf 7.7.E5]
theorem erf_squared_integral {a : ℂ} (ha : 0 < a.re) :
    (∫ t : ℝ in 0..1, exp (-a*(t : ℂ)^2)/((t : ℂ)^2+1))=π/4*exp a*(1-erf (a^(1/2 : ℂ))^2) := by
  set U : Set ℂ := {a : ℂ | 0 < a.re}
  set I : ℂ → ℂ := fun a => ∫ t : ℝ in (0:ℝ)..1, exp (-a*(1+(t:ℂ)^2))/(1+(t:ℂ)^2)
  set Φ : ℂ → ℂ := fun a => I a - π/4*(1-erf (a^(1/2 : ℂ))^2)
  have hsp : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hsq : (Real.sqrt π:ℂ)^2 = π := by exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have hΦd : ∀ b ∈ U, HasDerivAt Φ 0 b := by
    intro b hb
    have hb : 0 < b.re := hb
    have hb0 : b ≠ 0 := fun h => by simp [h] at hb
    have hm : b ∈ slitPlane := Or.inl hb
    set w := b^(1/2 : ℂ)
    have hw2 : w^2 = b := cpow_half_sq hb0
    have hw0 : w ≠ 0 := fun h => by simp [h] at hw2; exact hb0 hw2.symm
    have hI := hasDerivAt_integral_exp_div_one_add_sq b
    have hint : (∫ t : ℝ in (0:ℝ)..1, -exp (-b*(1+(t:ℂ)^2))) =
        -(exp (-b)*(Real.sqrt π/2*erf w/w)) := by
      rw [← integral_exp_neg_mul_sq_zero_one hw0, hw2, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_neg]
      congr 1; funext t; rw [← Complex.exp_add]; congr 2; ring
    rw [hint] at hI
    have hc : HasDerivAt (fun a : ℂ => a^(1/2 : ℂ)) ((1/2:ℂ)*b^((1/2:ℂ)-1)) b := by
      simpa using (hasDerivAt_id b).cpow_const (c := (1/2:ℂ)) hm
    have hc' : b^((1/2:ℂ)-1) = 1/w := by
      rw [cpow_sub _ _ hb0, cpow_one]; change w/b = 1/w; rw [← hw2]; field_simp
    rw [hc'] at hc
    have hE := (hasDerivAt_erf_complex w).comp b hc
    have hF := hI.sub (((hE.pow 2).const_sub 1).const_mul ((π:ℂ)/4))
    refine hF.congr_deriv ?_
    simp only [Function.comp_apply]
    rw [show b^(1/2:ℂ) = w from rfl, hw2]
    field_simp
    rw [hsq]
    ring
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hdiff : DifferentiableOn ℂ Φ U := fun b hb => (hΦd b hb).differentiableAt.differentiableWithinAt
  have hderiv : U.EqOn (deriv Φ) 0 := fun b hb => (hΦd b hb).deriv
  have hconst : ∀ ε : ℝ, 0 < ε → Φ ε = Φ a := fun ε hε =>
    hU.is_const_of_deriv_eq_zero hUc hdiff hderiv (by simp [U, hε]) ha
  have hcont : ContinuousAt (fun ε : ℝ => Φ ε) 0 := by
    have h1 : ContinuousAt I ((0:ℝ):ℂ) := (hasDerivAt_integral_exp_div_one_add_sq _).continuousAt
    have h2 : ContinuousAt (fun y : ℂ => y^(1/2:ℂ)) ((0:ℝ):ℂ) :=
      continuousAt_cpow_const_of_re_pos (Or.inl (by simp)) (by norm_num)
    have he : Continuous erf := differentiable_erf_complex.continuous
    have : ContinuousAt Φ ((0:ℝ):ℂ) := h1.sub (continuousAt_const.mul
      (continuousAt_const.sub ((he.continuousAt.comp h2).pow 2)))
    exact this.comp (f := fun t : ℝ => (t:ℂ)) (by fun_prop)
  have hlim := (hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ))))
  have hlim2 : Tendsto (fun ε : ℝ => Φ ε) (𝓝[>] 0) (𝓝 (Φ a)) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [self_mem_nhdsWithin] with ε hε using (hconst ε hε).symm)
  have hΦa : Φ a = Φ ((0:ℝ):ℂ) := tendsto_nhds_unique hlim2 hlim
  have hI0 : I 0 = π/4 := by
    simp only [I, neg_zero, zero_mul, Complex.exp_zero]
    have : (∫ t : ℝ in (0:ℝ)..1, (1:ℂ)/(1+(t:ℂ)^2)) =
        ((∫ t : ℝ in (0:ℝ)..1, 1/(1+t^2) : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]; push_cast; rfl
    rw [this, integral_one_div_one_add_sq, Real.arctan_one, Real.arctan_zero]
    push_cast; ring
  have hΦ0 : Φ ((0:ℝ):ℂ) = 0 := by
    simp only [Φ, ofReal_zero, hI0]
    rw [zero_cpow (by norm_num), erf_zero]; ring
  rw [hΦ0] at hΦa
  have hIa : I a = exp (-a)*(∫ t : ℝ in 0..1, exp (-a*(t : ℂ)^2)/((t : ℂ)^2+1)) := by
    simp only [I]
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext t
    rw [mul_div_assoc', ← Complex.exp_add, add_comm ((t:ℂ)^2) 1]; congr 2; ring
  have h3 : I a = π/4*(1-erf (a^(1/2 : ℂ))^2) := by
    have := hΦa; simp only [Φ] at this; linear_combination this
  rw [hIa] at h3
  have h4 : exp a*exp (-a) = 1 := by rw [← Complex.exp_add]; simp
  linear_combination exp a*h3 - (∫ t : ℝ in 0..1, exp (-a*(t : ℂ)^2)/((t : ℂ)^2+1))*h4

/-- Identity under the stated parameter and domain assumptions: `(∫ t : ℝ in Ioi x, exp (-(a*(t :
ℂ)^2+2*b*t+c)))=(π/a)^(1/2 : ℂ)/2*exp ((b^2-a*c)/a)*erfc (a^(1/2 : ℂ)*x+b/a^(1/2 : ℂ))`. -/
@[dlmf 7.7.E6]
theorem gaussian_quadratic_tail {a : ℂ} (ha : 0 < a.re) (b c : ℂ) (x : ℝ) :
    (∫ t : ℝ in Ioi x, exp (-(a*(t : ℂ)^2+2*b*t+c)))=(π/a)^(1/2 : ℂ)/2*exp ((b^2-a*c)/a)*erfc (a^(1/2 : ℂ)*x+b/a^(1/2 : ℂ)) := by
  exact gaussian_quadratic_tail_aux ha b c x

/-- Identity under the stated parameter and domain assumptions: `(∫ t : ℝ in Ioi x, exp (-a^2*(t :
ℂ)^2-b^2/(t : ℂ)^2))=Real.sqrt π/(4*a)*(exp (2*a*b)*erfc (a*x+b/x)+exp (-2*a*b)*erfc
(a*x-b/x))`. -/
@[dlmf 7.7.E7]
theorem gaussian_reciprocal_tail {a : ℂ} (ha0 : a ≠ 0) (ha : |arg a| < π/4) (b : ℂ) {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ in Ioi x, exp (-a^2*(t : ℂ)^2-b^2/(t : ℂ)^2))=Real.sqrt π/(4*a)*(exp (2*a*b)*erfc (a*x+b/x)+exp (-2*a*b)*erfc (a*x-b/x)) := by
  have ha2 := re_sq_pos_of_abs_arg_lt ha0 ha
  have har : 0 < a.re := re_pos_of_abs_arg_lt ha0 (by linarith [Real.pi_pos])
  have hp0 : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  set G : ℝ → ℂ := fun t => -(Real.sqrt π/(4*a))*(exp (2*a*b)*erfc (a*t+b/t)+
    exp (-2*a*b)*erfc (a*t+(-b)/t)) with hG
  have hd : ∀ t ∈ Ioi (0:ℝ), HasDerivAt G (exp (-a^2*(t : ℂ)^2-b^2/(t : ℂ)^2)) t := by
    intro t ht
    have ht0 : (t:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
    have h := ((hasDerivAt_erfc_mul_add_div a b (ne_of_gt ht)).const_mul (exp (2*a*b))).add
      ((hasDerivAt_erfc_mul_add_div a (-b) (ne_of_gt ht)).const_mul (exp (-2*a*b)))
    convert h.const_mul (-(Real.sqrt π/(4*a))) using 1
    have e1 : exp (2*a*b)*exp (-(a*t+b/t)^2) = exp (-a^2*(t : ℂ)^2-b^2/(t : ℂ)^2) := by
      rw [← Complex.exp_add]; congr 1; field_simp; ring
    have e2 : exp (-2*a*b)*exp (-(a*t+(-b)/t)^2) = exp (-a^2*(t : ℂ)^2-b^2/(t : ℂ)^2) := by
      rw [← Complex.exp_add]; congr 1; field_simp; ring
    have : -(Real.sqrt π/(4*a))*(exp (2*a*b)*-(2/Real.sqrt π*exp (-(a*t+b/t)^2)*(a-b/(t:ℂ)^2))+
        exp (-2*a*b)*-(2/Real.sqrt π*exp (-(a*t+(-b)/t)^2)*(a-(-b)/(t:ℂ)^2))) =
        (exp (2*a*b)*exp (-(a*t+b/t)^2))*(a-b/(t:ℂ)^2)/(2*a) +
        (exp (-2*a*b)*exp (-(a*t+(-b)/t)^2))*(a+b/(t:ℂ)^2)/(2*a) := by
      field_simp; ring
    rw [this, e1, e2]; field_simp; ring
  have hlim1 (c : ℂ) : Tendsto (fun t : ℝ => erfc (a*t+c/t)) atTop (𝓝 0) := by
    refine tendsto_erfc_zero_of_re ?_ ?_
    · have h0 : Tendsto (fun t : ℝ => c.re/t) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have : Tendsto (fun t : ℝ => a.re*t + c.re/t) atTop atTop :=
        (tendsto_id.const_mul_atTop har).atTop_add h0
      refine this.congr' ?_
      filter_upwards with t
      simp [div_ofReal_re]
    · have h0 : Tendsto (fun t : ℝ => 2*(a*c).re + (c^2).re/t^2) atTop (𝓝 (2*(a*c).re + 0)) :=
        tendsto_const_nhds.add (tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero))
      have : Tendsto (fun t : ℝ => (a^2).re*t^2 + (2*(a*c).re + (c^2).re/t^2)) atTop atTop :=
        ((tendsto_pow_atTop two_ne_zero).const_mul_atTop ha2).atTop_add h0
      refine this.congr' ?_
      filter_upwards [eventually_ne_atTop 0] with t ht
      have ht' : (t:ℂ) ≠ 0 := by exact_mod_cast ht
      have : (a*(t:ℂ)+c/t)^2 = (a^2)*((t^2:ℝ):ℂ) + (2*(a*c) + c^2/((t^2:ℝ):ℂ)) := by
        push_cast; field_simp; ring
      rw [this]
      simp only [add_re, div_ofReal_re]
      rw [mul_comm (a^2), re_ofReal_mul]
      simp; ring
  have hlim : Tendsto G atTop (𝓝 0) := by
    have := ((hlim1 b).const_mul (exp (2*a*b))).add ((hlim1 (-b)).const_mul (exp (-2*a*b)))
    simpa [hG] using this.const_mul (-(Real.sqrt π/(4*a)))
  have hint : IntegrableOn (fun t : ℝ => exp (-a^2*(t : ℂ)^2-b^2/(t : ℂ)^2)) (Ioi x) := by
    have hg : Integrable (fun t : ℝ => Real.exp (‖b^2‖/x^2) * Real.exp (-(a^2).re*t^2)) :=
      (integrable_exp_neg_mul_sq ha2).const_mul _
    refine Integrable.mono' hg.integrableOn ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
      have ht0 : (t:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_trans hx ht))
      exact (ContinuousAt.continuousWithinAt (by fun_prop (disch := exact pow_ne_zero 2 ht0)))
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
      have ht : x < t := ht
      have htp : 0 < t := lt_trans hx ht
      rw [Complex.norm_exp, ← Real.exp_add, Real.exp_le_exp]
      have h1 : (-a^2*(t:ℂ)^2-b^2/(t:ℂ)^2).re = -(a^2).re*t^2 - (b^2).re/t^2 := by
        rw [show (t:ℂ)^2 = ((t^2:ℝ):ℂ) by push_cast; ring, sub_re, div_ofReal_re, neg_mul,
          neg_re, re_mul_ofReal]
        ring
      rw [h1]
      have h2 : -(b^2).re/t^2 ≤ ‖b^2‖/x^2 := by
        have hb := neg_le_of_abs_le (Complex.abs_re_le_norm (b^2))
        have : ‖b^2‖/t^2 ≤ ‖b^2‖/x^2 := by gcongr
        calc -(b^2).re/t^2 ≤ ‖b^2‖/t^2 := by gcongr; linarith
          _ ≤ _ := this
      have : -(b^2).re/t^2 = -((b^2).re/t^2) := by ring
      linarith
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (hd x hx).continuousAt.continuousWithinAt
    (fun t ht => hd t (lt_trans hx ht)) hint hlim]
  simp only [hG, neg_div, ← sub_eq_add_neg]
  ring

/-- Identity under the stated parameter and domain assumptions: `(∫ t : ℝ in Ioi 0, exp (-a^2*(t :
ℂ)^2-b^2/(t : ℂ)^2))=Real.sqrt π/(2*a)*exp (-2*a*b)`. -/
@[dlmf 7.7.E8]
theorem gaussian_reciprocal_integral {a b : ℂ} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (ha : |arg a| < π/4) (hb : |arg b| < π/4) :
    (∫ t : ℝ in Ioi 0, exp (-a^2*(t : ℂ)^2-b^2/(t : ℂ)^2))=Real.sqrt π/(2*a)*exp (-2*a*b) := by
  have ha2 := re_sq_pos_of_abs_arg_lt ha0 ha
  have hb2 := re_sq_pos_of_abs_arg_lt hb0 hb
  have hbr : 0 < b.re := re_pos_of_abs_arg_lt hb0 (by linarith [Real.pi_pos])
  set E : ℝ → ℂ := fun t => exp (-a^2*(t : ℂ)^2-b^2/(t : ℂ)^2) with hE
  have hbnd : ∀ t : ℝ, 0 < t → ‖E t‖ ≤ Real.exp (-(a^2).re*t^2) := by
    intro t ht
    rw [hE, Complex.norm_exp, Real.exp_le_exp]
    have h1 : (-a^2*(t:ℂ)^2-b^2/(t:ℂ)^2).re = -(a^2).re*t^2 - (b^2).re/t^2 := by
      rw [show (t:ℂ)^2 = ((t^2:ℝ):ℂ) by push_cast; ring, sub_re, div_ofReal_re, neg_mul,
        neg_re, re_mul_ofReal]
      ring
    rw [h1]
    have : 0 ≤ (b^2).re/t^2 := by positivity
    linarith
  have hint : IntegrableOn E (Ioi 0) := by
    refine Integrable.mono' (integrable_exp_neg_mul_sq ha2).integrableOn ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
      have ht0 : (t:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (show (0:ℝ) < t from ht))
      exact (ContinuousAt.continuousWithinAt (by fun_prop (disch := exact pow_ne_zero 2 ht0)))
    · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => hbnd t ht)
  have hsplit : ∀ x : ℝ, 0 < x → (∫ t in Ioi 0, E t) = (∫ t in (0:ℝ)..x, E t) +
      Real.sqrt π/(4*a)*(exp (2*a*b)*erfc (a*x+b/x)+exp (-2*a*b)*erfc (a*x-b/x)) := by
    intro x hx
    rw [← gaussian_reciprocal_tail ha0 ha b hx, intervalIntegral.integral_of_le hx.le,
      ← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hx.le)),
      Ioc_union_Ioi_eq_Ioi hx.le]
  have hI : Tendsto (fun x : ℝ => ∫ t in (0:ℝ)..x, E t) (𝓝[>] 0) (𝓝 0) := by
    have hb : ∀ᶠ x in 𝓝[>] (0:ℝ), ‖∫ t in (0:ℝ)..x, E t‖ ≤ 1*|x-0| := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
      rw [uIoc_of_le (le_of_lt hx)] at ht
      exact (hbnd t ht.1).trans (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t]))
    refine squeeze_zero_norm' hb ?_
    have : Tendsto (fun x : ℝ => 1*|x-0|) (𝓝 0) (𝓝 0) := by
      simpa using continuous_abs.tendsto (0:ℝ)
    exact this.mono_left nhdsWithin_le_nhds
  have hR : Tendsto (fun x : ℝ => Real.sqrt π/(4*a)*(exp (2*a*b)*erfc (a*x+b/x)+
      exp (-2*a*b)*erfc (a*x-b/x))) (𝓝[>] 0) (𝓝 (Real.sqrt π/(4*a)*(exp (2*a*b)*0+
      exp (-2*a*b)*(2-0)))) := by
    have h1 := tendsto_erfc_mul_add_div_nhdsGT a hbr hb2
    have h2 := (tendsto_erfc_mul_add_div_nhdsGT (-a) hbr hb2).const_sub 2
    have h2' : Tendsto (fun x : ℝ => erfc (a*x-b/x)) (𝓝[>] 0) (𝓝 (2-0)) := by
      refine h2.congr fun x => ?_
      rw [← erfc_negative]; congr 1; ring
    exact ((h1.const_mul _).add (h2'.const_mul _)).const_mul _
  have hlim := hI.add hR
  have hc : Tendsto (fun x : ℝ => ∫ t in Ioi 0, E t) (𝓝[>] 0) (𝓝 (∫ t in Ioi 0, E t)) :=
    tendsto_const_nhds
  have heq := tendsto_nhds_unique (hc.congr' (by
    filter_upwards [self_mem_nhdsWithin] with x hx using hsplit x hx)) hlim
  rw [heq]
  have ha' : a ≠ 0 := ha0
  field_simp; ring

/-- Identity under the stated parameter and domain assumptions: `primitive erf z=z*erf z+(exp
(-z^2)-1)/Real.sqrt π`. -/
@[dlmf 7.7.E9]
theorem erf_primitive (z : ℂ) :
    primitive erf z=z*erf z+(exp (-z^2)-1)/Real.sqrt π := by
  have hπ : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hd (w : ℂ) : HasDerivAt (fun w => w*erf w+(exp (-w^2)-1)/Real.sqrt π) (erf w) w := by
    have h := ((hasDerivAt_id' w).mul (hasDerivAt_erf_complex w)).add
      ((((hasDerivAt_id' w).pow 2).neg.cexp.sub_const 1).div_const (Real.sqrt π:ℂ))
    convert h using 1
    simp only [Pi.neg_apply, Pi.pow_apply]
    field_simp
    ring
  rw [primitive_eq_sub differentiable_erf_complex.continuous hd]
  simp

/-- Identity under the stated parameter and domain assumptions: `fresnelAuxFComplex
z=1/(π*Real.sqrt 2)*(∫ t : ℝ in Ioi 0, (t : ℂ)^(-1/2 : ℂ)*exp (-π*z^2*t/2)/((t : ℂ)^2+1))`. -/
@[dlmf 7.7.E10]
theorem fresnelAuxFComplex_laplace_integral {z : ℂ} (hz : |arg z| ≤ π/4) :
    fresnelAuxFComplex z=1/(π*Real.sqrt 2)*(∫ t : ℝ in Ioi 0, (t : ℂ)^(-1/2 : ℂ)*exp (-π*z^2*t/2)/((t : ℂ)^2+1)) := by
  have h := erfInt_fresnelAux_laplace false hz
  simp only [Bool.false_eq_true, ite_false, Nat.cast_zero, zero_sub] at h
  rw [h]; congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [show (-1/2 : ℂ) = -(1/2) by ring]; ring

/-- Identity under the stated parameter and domain assumptions: `fresnelAuxGComplex
z=1/(π*Real.sqrt 2)*(∫ t : ℝ in Ioi 0, (t : ℂ)^(1/2 : ℂ)*exp (-π*z^2*t/2)/((t : ℂ)^2+1))`. -/
@[dlmf 7.7.E11]
theorem fresnelAuxGComplex_laplace_integral {z : ℂ} (hz : |arg z| ≤ π/4) :
    fresnelAuxGComplex z=1/(π*Real.sqrt 2)*(∫ t : ℝ in Ioi 0, (t : ℂ)^(1/2 : ℂ)*exp (-π*z^2*t/2)/((t : ℂ)^2+1)) := by
  have h := erfInt_fresnelAux_laplace true hz
  simp only [ite_true, Nat.cast_one] at h
  rw [h]; congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [show (1 : ℂ) - 1/2 = 1/2 by ring]; ring

/-- The map `(fun R : ℝ => exp (-π*I*z^2/2)*segmentIntegral (fun t => exp (π*I*t^2/2)) z R)` tends
to `(𝓝 (fresnelAuxGComplex z+I*fresnelAuxFComplex z))` along `atTop`. -/
@[dlmf 7.7.E12]
theorem fresnelAux_contour_tail (z : ℂ) :
    Tendsto (fun R : ℝ => exp (-π*I*z^2/2)*segmentIntegral (fun t => exp (π*I*t^2/2)) z R) atTop (𝓝 (fresnelAuxGComplex z+I*fresnelAuxFComplex z)) := by
  have h := (fresnelTail_horizontal_integral z).const_mul (exp (-π*I*z^2/2))
  convert h using 2
  have he : exp (-π*I*z^2/2) = cos (π*z^2/2) - sin (π*z^2/2)*I := by
    rw [show -π*I*z^2/2 = -(π*z^2/2)*I by ring, Complex.exp_mul_I, Complex.cos_neg,
      Complex.sin_neg]
    ring
  rw [he, fresnelAuxGComplex, fresnelAuxFComplex, fresnelTail]
  ring_nf
  rw [I_sq]
  ring

end DLMF.Confluent
end
