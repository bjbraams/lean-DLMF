/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ErrorFunctions.IntegralTools
public import DLMF.Bessel.KMellin

/-!
# Integral representations and transforms, DLMF §§7.7 and 7.14

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
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

/-- erfc rational gaussian integral. -/
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

/-- faddeevaW cauchy integral. -/
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
/-- gaussian fourier halfLine. -/
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

/-- gaussian sqrt laplace. -/
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

/-- erf squared integral. -/
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

/-- gaussian quadratic tail. -/
@[dlmf 7.7.E6]
theorem gaussian_quadratic_tail {a : ℂ} (ha : 0 < a.re) (b c : ℂ) (x : ℝ) :
    (∫ t : ℝ in Ioi x, exp (-(a*(t : ℂ)^2+2*b*t+c)))=(π/a)^(1/2 : ℂ)/2*exp ((b^2-a*c)/a)*erfc (a^(1/2 : ℂ)*x+b/a^(1/2 : ℂ)) := by
  exact gaussian_quadratic_tail_aux ha b c x

/-- gaussian reciprocal tail. -/
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

/-- gaussian reciprocal integral. -/
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

/-- erf primitive. -/
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

/-- fresnelAuxFComplex laplace integral. -/
@[dlmf 7.7.E10]
theorem fresnelAuxFComplex_laplace_integral {z : ℂ} (hz : |arg z| ≤ π/4) :
    fresnelAuxFComplex z=1/(π*Real.sqrt 2)*(∫ t : ℝ in Ioi 0, (t : ℂ)^(-1/2 : ℂ)*exp (-π*z^2*t/2)/((t : ℂ)^2+1)) := by
  have h := erfInt_fresnelAux_laplace false hz
  simp only [Bool.false_eq_true, ite_false, Nat.cast_zero, zero_sub] at h
  rw [h]; congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [show (-1/2 : ℂ) = -(1/2) by ring]; ring

/-- fresnelAuxGComplex laplace integral. -/
@[dlmf 7.7.E11]
theorem fresnelAuxGComplex_laplace_integral {z : ℂ} (hz : |arg z| ≤ π/4) :
    fresnelAuxGComplex z=1/(π*Real.sqrt 2)*(∫ t : ℝ in Ioi 0, (t : ℂ)^(1/2 : ℂ)*exp (-π*z^2*t/2)/((t : ℂ)^2+1)) := by
  have h := erfInt_fresnelAux_laplace true hz
  simp only [ite_true, Nat.cast_one] at h
  rw [h]; congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [show (1 : ℂ) - 1/2 = 1/2 by ring]; ring

/-- fresnelAux contour tail. -/
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

theorem fresMB_measurable_kernel (k : ℕ) (w : ℂ) : Measurable (fresMB_kernel k w) := by
  unfold fresMB_kernel; fun_prop

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

theorem fresMB_continuous_G {b c : ℝ} (hc : 0 < c) (hcb : 0 < c + b) (hcb1 : c < 1 - b) :
    Continuous fun y : ℝ => fresMB_G b (c + y * I) := by
  refine continuous_iff_continuousAt.mpr fun y => ?_
  unfold fresMB_G
  refine ((ContinuousAt.mul ?_ ?_).mul ?_).mul ?_
  · exact (DLMF.Gamma.continuousAt_Gamma_of_re_pos (by simp [hc])).comp (by fun_prop)
  · exact (DLMF.Gamma.continuousAt_Gamma_of_re_pos (by simp; linarith)).comp (by fun_prop)
  · exact (DLMF.Gamma.continuousAt_Gamma_of_re_pos (by simp; linarith)).comp (by fun_prop)
  · exact (DLMF.Gamma.continuousAt_Gamma_of_re_pos (by simp; linarith)).comp (by fun_prop)

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

theorem fresMB_integrable_G {b c : ℝ} (hc : 0 < c) (hcb : 0 < c + b) (hcb1 : c < 1 - b) :
    Integrable fun y : ℝ => fresMB_G b (c + y * I) := by
  obtain ⟨C, K, hC⟩ := fresMB_bound_G hc hcb hcb1
  refine ((DLMF.Gamma.integrable_one_add_abs_pow_mul_exp_neg (by positivity : 0 < 2 * π) K).const_mul
    C).mono' (fresMB_continuous_G hc hcb hcb1).aestronglyMeasurable
    (Eventually.of_forall fun y => (hC y).trans (le_of_eq (by ring)))

/-- The auxiliary function in the Mellin variable `X = (π x²/4)²`. -/
def fresMB_g (aux : Bool) : ℝ → ℂ :=
  fun X => fresMB_aux aux (((2 / Real.sqrt π * X ^ (1 / 4 : ℝ) : ℝ)) : ℂ)

theorem fresMB_cpow_eq_exp {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ((r : ℝ) : ℂ) ^ z = exp (((Real.log r : ℝ) : ℂ) * z) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hr.ne'), ← ofReal_log hr.le]

theorem fresMB_two_pi_cpow :
    (2 * π : ℂ) ^ (3 / 2 : ℂ) = 2 * π * ((Real.sqrt 2 * Real.sqrt π : ℝ) : ℂ) := by
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have e : (2 * π : ℂ) ^ (3 / 2 : ℂ) = (((2 * π) ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [ofReal_cpow h2π]; push_cast; rfl
  rw [e, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by positivity), Real.rpow_one,
    ← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num)]
  push_cast; ring

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

lemma fresMB_differentiable_aux (aux : Bool) : Differentiable ℂ (fresMB_aux aux) := by
  unfold fresMB_aux; cases aux
  · exact fresnelAuxFComplex_entire
  · exact fresnelAuxGComplex_entire

/-- The Mellin–Barnes integrand of DLMF 7.7.13–14. -/
def fresMB_E (b c : ℝ) (z : ℂ) (y : ℝ) : ℂ :=
  exp (-((c : ℂ) + y * I) * (2 * log (π : ℂ) - log 16 + 4 * log z)) * fresMB_G b (c + y * I)

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

theorem fresMB_continuous_E {b c : ℝ} (hc : 0 < c) (hcb : 0 < c + b) (hcb1 : c < 1 - b) (z : ℂ) :
    Continuous (fresMB_E b c z) := by
  unfold fresMB_E
  exact (by fun_prop : Continuous fun y : ℝ => exp (-((c : ℂ) + y * I) *
    (2 * log (π : ℂ) - log 16 + 4 * log z))).mul (fresMB_continuous_G hc hcb hcb1)

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

theorem fresMB_integral_E_eq {b c : ℝ} {z : ℂ} (hz : 0 < z.re) :
    ∫ y, fresMB_E b c z y =
      (1 / 4 : ℂ) * ∫ y, fresMB_B b c y * z⁻¹ ^ (((4 * c : ℝ) : ℂ) + I * (y : ℂ)) := by
  simp_rw [fresMB_E_eq hz]
  rw [Measure.integral_comp_mul_left (fun y : ℝ =>
    fresMB_B b c y * z⁻¹ ^ (((4 * c : ℝ) : ℂ) + I * (y : ℂ))) 4]
  rw [real_smul]; norm_num

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

/-- fresnelAuxFComplex mellinBarnes. -/
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

/-- fresnelAuxGComplex mellinBarnes. -/
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

/-- fresnelAuxFComplex laplace square. -/
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

/-- fresnelAuxGComplex laplace square. -/
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

/-- erfc fourier halfLine. -/
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

/-- erf laplace. -/
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

/-- erf sqrt laplace. -/
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

/-! ### Tools for DLMF 7.14.4 and its companion -/

/-- The antiderivative (in `x = √t`) for the Laplace transforms of DLMF 7.14.4. -/
noncomputable def erfInt_G (p α β γ : ℂ) (x : ℝ) : ℂ :=
  1/p*exp (p*(x:ℂ)^2)*erfc (α*x+γ/x) - exp (-2*α*γ)/p*((1+α/β)/2*exp (2*β*γ)*erfc (β*x+γ/x) +
    (α/β-1)/2*exp (-2*β*γ)*erfc (β*x+(-γ)/x))

theorem erfInt_hasDerivAt_G {p α β γ : ℂ} (hp : p = α^2-β^2) (hp0 : p ≠ 0) (hβ : β ≠ 0)
    {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (erfInt_G p α β γ) (2*x*exp (p*(x:ℂ)^2)*erfc (α*x+γ/x)) x := by
  have hx' : (x:ℂ) ≠ 0 := by exact_mod_cast hx
  have hsq : HasDerivAt (fun x : ℝ => exp (p*(x:ℂ)^2)) (exp (p*(x:ℂ)^2)*(p*(2*x))) x := by
    have h : HasDerivAt (fun w : ℂ => p*w^2) (p*(2*(x:ℂ))) (x:ℂ) := by
      simpa using ((hasDerivAt_pow 2 (x:ℂ)).const_mul p)
    exact h.cexp.comp_ofReal
  have h1 := hasDerivAt_erfc_mul_add_div α γ hx
  have h2 := hasDerivAt_erfc_mul_add_div β γ hx
  have h3 := hasDerivAt_erfc_mul_add_div β (-γ) hx
  have h := (((hsq.const_mul (1/p)).mul h1).sub ((((h2.const_mul
    ((1+α/β)/2*exp (2*β*γ))).add (h3.const_mul ((α/β-1)/2*exp (-2*β*γ)))).const_mul
    (exp (-2*α*γ)/p))))
  convert h using 1
  · funext y; simp only [erfInt_G, Pi.mul_apply, Pi.sub_apply, Pi.add_apply]
  · have e1 : exp (-(α*x+γ/x)^2) = exp (-2*α*γ)*exp (-(β^2*x^2+γ^2/x^2))*exp (-(p*(x:ℂ)^2)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; rw [hp]; field_simp; ring
    have e2 : exp (-(β*x+γ/x)^2) = exp (-(β^2*x^2+γ^2/x^2))*exp (-2*β*γ) := by
      rw [← Complex.exp_add]; congr 1; field_simp; ring
    have e3 : exp (-(β*x+(-γ)/x)^2) = exp (-(β^2*x^2+γ^2/x^2))*exp (2*β*γ) := by
      rw [← Complex.exp_add]; congr 1; field_simp; ring
    have hA : exp (p*(x:ℂ)^2) * exp (-(p*(x:ℂ)^2)) = 1 := by rw [← Complex.exp_add]; simp
    have hB : exp (2*β*γ) * exp (-2*β*γ) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
    rw [e1, e2, e3]
    generalize exp (-(β^2*x^2+γ^2/x^2)) = Q at *
    generalize exp (p*(x:ℂ)^2) = A at *
    generalize exp (-(p*(x:ℂ)^2)) = A' at *
    generalize exp (2*β*γ) = B at *
    generalize exp (-2*β*γ) = B' at *
    generalize (Real.sqrt π : ℂ) = P at *
    generalize erfc (α*x+γ/x) = F at *
    field_simp
    linear_combination (2*β*cexp (-(2*α*γ))*Q*((x:ℂ)^2*α-γ)/P) * hA -
      (2*β*cexp (-(2*α*γ))*Q*((x:ℂ)^2*α-γ)/P) * hB

/-- The derivative of `G(√t)`. -/
theorem erfInt_hasDerivAt_G_sqrt {p α β γ : ℂ} (hp : p = α^2-β^2) (hp0 : p ≠ 0) (hβ : β ≠ 0)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => erfInt_G p α β γ (Real.sqrt t))
      (exp (p*t)*erfc (α*Real.sqrt t+γ/Real.sqrt t)) t := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have h := (erfInt_hasDerivAt_G (γ := γ) hp hp0 hβ hs.ne').scomp t
    (Real.hasDerivAt_sqrt ht.ne')
  have hs' : (Real.sqrt t : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hsq : (Real.sqrt t : ℂ)^2 = t := by exact_mod_cast Real.sq_sqrt ht.le
  refine (h.congr_deriv ?_ :)
  rw [hsq, real_smul]; push_cast; field_simp

/-- `erfc (βx + δ/x) → 0` as `x → ∞` when `Re β > 0` and `Re β² > 0`. -/
theorem erfInt_tendsto_erfc_atTop {β : ℂ} (hβ : 0 < β.re) (hβ2 : 0 < (β^2).re) (δ : ℂ) :
    Tendsto (fun x : ℝ => erfc (β*x+δ/x)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  refine tendsto_erfc_zero_of_re ?_ ?_
  · have h1 : Tendsto (fun x : ℝ => δ.re*x⁻¹) atTop (𝓝 0) := by simpa using hinv.const_mul δ.re
    have : Tendsto (fun x : ℝ => β.re*x + δ.re*x⁻¹) atTop atTop :=
      (tendsto_id.const_mul_atTop hβ).atTop_add h1
    refine this.congr' ?_
    filter_upwards with x
    rw [add_re, div_ofReal_re, re_mul_ofReal]; simp [div_eq_mul_inv]
  · have h1 : Tendsto (fun x : ℝ => (δ^2).re*(x⁻¹)^2 + 2*(β*δ).re) atTop (𝓝 (2*(β*δ).re)) := by
      simpa using ((hinv.pow 2).const_mul (δ^2).re).add_const (2*(β*δ).re)
    have : Tendsto (fun x : ℝ => (β^2).re*x^2 + ((δ^2).re*(x⁻¹)^2 + 2*(β*δ).re)) atTop atTop :=
      ((tendsto_pow_atTop two_ne_zero).const_mul_atTop hβ2).atTop_add h1
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hx' : (x:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
    have : (β*(x:ℂ)+δ/x)^2 = β^2*((x^2:ℝ):ℂ) + 2*(β*δ) + δ^2/((x^2:ℝ):ℂ) := by
      push_cast; field_simp; ring
    rw [this]
    simp only [add_re, div_ofReal_re]
    rw [mul_comm (β^2), re_ofReal_mul]
    simp [div_eq_mul_inv]; ring

/-- **Core of DLMF 7.14.4**: with `p = α² - β²`, the Laplace-type integral
`∫₀^∞ e^{pt} erfc(α√t + γ/√t) dt` equals `e^{-2αγ-2βγ}/(β(α+β))`, given integrability and the
decay of `e^{px²} erfc(αx+γ/x)` at infinity. -/
theorem erfInt_laplace_core {p α β γ : ℂ} (hp : p = α^2-β^2) (hp0 : p ≠ 0) (hβ : 0 < β.re)
    (hβ2 : 0 < (β^2).re) (hγ : 0 < γ.re) (hγ2 : 0 < (γ^2).re) (hαβ : α + β ≠ 0)
    (hint : IntegrableOn (fun t : ℝ => exp (p*t)*erfc (α*Real.sqrt t+γ/Real.sqrt t)) (Ioi 0))
    (hlim : Tendsto (fun x : ℝ => exp (p*(x:ℂ)^2)*erfc (α*x+γ/x)) atTop (𝓝 0)) :
    (∫ t in Ioi (0:ℝ), exp (p*t)*erfc (α*Real.sqrt t+γ/Real.sqrt t)) =
      exp (-2*α*γ-2*β*γ)/(β*(α+β)) := by
  have hβ0 : β ≠ 0 := fun h => by simp [h] at hβ
  set L0 : ℂ := -(exp (-2*α*γ)/p*((α/β-1)*exp (-2*β*γ))) with hL0
  -- limit of `G` at `0⁺`
  have hG0 : Tendsto (erfInt_G p α β γ) (𝓝[>] 0) (𝓝 L0) := by
    have hx0 : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[>] 0) (𝓝 0) := by
      have := (Complex.continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
    have he : Tendsto (fun x : ℝ => exp (p*(x:ℂ)^2)) (𝓝[>] 0) (𝓝 1) := by
      have := ((hx0.pow 2).const_mul p).cexp
      simpa using this
    have h1 := tendsto_erfc_mul_add_div_nhdsGT α hγ hγ2
    have h2 := tendsto_erfc_mul_add_div_nhdsGT β hγ hγ2
    have h3 : Tendsto (fun x : ℝ => erfc (β*x+(-γ)/x)) (𝓝[>] 0) (𝓝 (2 - 0)) := by
      have := (tendsto_erfc_mul_add_div_nhdsGT (-β) hγ hγ2).const_sub 2
      refine this.congr fun x => ?_
      rw [← erfc_negative]; congr 1; ring
    have := ((he.const_mul (1/p)).mul h1).sub ((((h2.const_mul ((1+α/β)/2*exp (2*β*γ))).add
      (h3.const_mul ((α/β-1)/2*exp (-2*β*γ))))).const_mul (exp (-2*α*γ)/p))
    have hv : L0 = 1/p*1*0 - exp (-2*α*γ)/p*((1+α/β)/2*exp (2*β*γ)*0 +
        (α/β-1)/2*exp (-2*β*γ)*(2-0)) := by rw [hL0]; ring
    rw [hv]
    refine this.congr fun x => ?_
    rw [erfInt_G]
  -- limit of `G` at `∞`
  have hGi : Tendsto (erfInt_G p α β γ) atTop (𝓝 0) := by
    have h2 := erfInt_tendsto_erfc_atTop hβ hβ2 γ
    have h3 := erfInt_tendsto_erfc_atTop hβ hβ2 (-γ)
    have := (hlim.const_mul (1/p)).sub ((((h2.const_mul ((1+α/β)/2*exp (2*β*γ))).add
      (h3.const_mul ((α/β-1)/2*exp (-2*β*γ))))).const_mul (exp (-2*α*γ)/p))
    simp only [mul_zero, add_zero, sub_zero] at this
    refine this.congr fun x => ?_
    rw [erfInt_G]; ring
  set f : ℝ → ℂ := Function.update (fun t : ℝ => erfInt_G p α β γ (Real.sqrt t)) 0 L0 with hf
  have hsq0 : Tendsto Real.sqrt (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := (Real.continuous_sqrt.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with t ht using Real.sqrt_pos.2 ht
  have hcont : ContinuousWithinAt f (Ici 0) 0 := by
    rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt]
    have hf0 : f 0 = L0 := by simp [hf]
    rw [hf0]
    refine (hG0.comp hsq0).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp [hf, Function.update_of_ne (ne_of_gt (mem_Ioi.1 ht))]
  have hderiv : ∀ t ∈ Ioi (0:ℝ), HasDerivAt f
      (exp (p*t)*erfc (α*Real.sqrt t+γ/Real.sqrt t)) t := by
    intro t ht
    have ht : (0:ℝ) < t := ht
    refine (erfInt_hasDerivAt_G_sqrt hp hp0 hβ0 ht).congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds ht] with s hs
    simp [hf, Function.update_of_ne (ne_of_gt hs)]
  have hfi : Tendsto f atTop (𝓝 0) := by
    refine (hGi.comp Real.tendsto_sqrt_atTop).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp [hf, Function.update_of_ne (ne_of_gt ht)]
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hfi]
  have hf0 : f 0 = L0 := by simp [hf]
  rw [hf0, hL0, hp]
  have hp' : α^2-β^2 ≠ 0 := hp ▸ hp0
  have hab : α - β ≠ 0 := fun h => hp' (by linear_combination (α+β)*h)
  rw [show -2*α*γ-2*β*γ = -2*α*γ + (-2*β*γ) by ring, Complex.exp_add]
  field_simp
  ring

/-- If `Re a > 0` and `Re c ≥ 0`, then `ac` is not a negative real number. -/
theorem erfInt_re_mul_nonneg_or {a c : ℂ} (ha : 0 < a.re) (hc : 0 ≤ c.re) :
    0 ≤ (a*c).re ∨ (a*c).im ≠ 0 := by
  by_cases h : (a*c).im = 0
  · left
    simp only [mul_re, mul_im] at h ⊢
    have : (a.re*c.re - a.im*c.im) * a.re = c.re*(a.re^2+a.im^2) := by
      linear_combination (-a.im) * h
    have h2 : 0 ≤ c.re*(a.re^2+a.im^2) := by positivity
    by_contra hneg
    push Not at hneg
    nlinarith
  · exact Or.inr h

/-- `(a t)^{1/2} = a^{1/2} √t` for `Re a > 0`, `t > 0`. -/
theorem erfInt_cpow_half_mul_ofReal {a : ℂ} (ha : 0 < a.re) {t : ℝ} (ht : 0 < t) :
    (a*t)^(1/2 : ℂ) = a^(1/2 : ℂ)*Real.sqrt t := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hr : 0 < (a^(1/2 : ℂ)*(Real.sqrt t:ℂ)).re := by
    rw [re_mul_ofReal]; exact mul_pos (re_cpow_half_pos ha) (Real.sqrt_pos.2 ht)
  have hsq : (a^(1/2 : ℂ)*(Real.sqrt t:ℂ))^2 = a*t := by
    rw [mul_pow, cpow_half_sq ha0]; congr 1; exact_mod_cast Real.sq_sqrt ht.le
  rw [← hsq, sq_cpow_half hr]

/-- `(c/t)^{1/2} = c^{1/2}/√t` for `Re c > 0`, `t > 0`. -/
theorem erfInt_cpow_half_div_ofReal {c : ℂ} (hc : 0 < c.re) {t : ℝ} (ht : 0 < t) :
    (c/t)^(1/2 : ℂ) = c^(1/2 : ℂ)/Real.sqrt t := by
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hr : 0 < (c^(1/2 : ℂ)/(Real.sqrt t:ℂ)).re := by
    rw [div_ofReal_re]; exact div_pos (re_cpow_half_pos hc) hs
  have hsq : (c^(1/2 : ℂ)/(Real.sqrt t:ℂ))^2 = c/t := by
    rw [div_pow, cpow_half_sq hc0]; congr 1; exact_mod_cast Real.sq_sqrt ht.le
  rw [← hsq, sq_cpow_half hr]

/-- `(ac)^{1/2} = a^{1/2} c^{1/2}` for `Re a > 0`, `Re c > 0`. -/
theorem erfInt_cpow_half_mul {a c : ℂ} (ha : 0 < a.re) (hc : 0 < c.re) :
    (a*c)^(1/2 : ℂ) = a^(1/2 : ℂ)*c^(1/2 : ℂ) := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  have hr : 0 < (a^(1/2 : ℂ)*c^(1/2 : ℂ)).re := by
    refine re_mul_pos_of_re_sq_pos (re_cpow_half_pos ha) ?_ (re_cpow_half_pos hc) ?_
    · rw [cpow_half_sq ha0]; exact ha
    · rw [cpow_half_sq hc0]; exact hc.le
  have hsq : (a^(1/2 : ℂ)*c^(1/2 : ℂ))^2 = a*c := by
    rw [mul_pow, cpow_half_sq ha0, cpow_half_sq hc0]
  rw [← hsq, sq_cpow_half hr]

/-- The sharp bound for the integrand of DLMF 7.14.4: for `Re a > 0`, `Re c > 0`, `t > 0`,
`z = (at)^{1/2} + (c/t)^{1/2}` has `Re z > 0` and `Re z² ≥ Re a · t`. -/
theorem erfInt_re_sq_ge {a c : ℂ} (ha : 0 < a.re) (hc : 0 < c.re) {t : ℝ} (ht : 0 < t) :
    0 < ((a*t)^(1/2 : ℂ) + (c/t)^(1/2 : ℂ)).re ∧
      a.re*t ≤ (((a*t)^(1/2 : ℂ) + (c/t)^(1/2 : ℂ))^2).re := by
  have hat : 0 < (a*(t:ℂ)).re := by rw [re_mul_ofReal]; positivity
  have hct : 0 < (c/(t:ℂ)).re := by rw [div_ofReal_re]; positivity
  have hat0 : a*(t:ℂ) ≠ 0 := fun h => by rw [h] at hat; simp at hat
  have hct0 : c/(t:ℂ) ≠ 0 := fun h => by rw [h] at hct; simp at hct
  set u := (a*t)^(1/2 : ℂ)
  set v := (c/t)^(1/2 : ℂ)
  have hu := re_cpow_half_pos hat
  have hv := re_cpow_half_pos hct
  have hu2 : u^2 = a*t := cpow_half_sq hat0
  have hv2 : v^2 = c/t := cpow_half_sq hct0
  have huv : 0 < (u*v).re :=
    re_mul_pos_of_re_sq_pos hu (by rw [hu2]; exact hat) hv (by rw [hv2]; exact hct.le)
  refine ⟨by rw [add_re]; linarith, ?_⟩
  have : (u+v)^2 = u^2 + 2*(u*v) + v^2 := by ring
  rw [this, hu2, hv2]
  simp only [add_re, re_mul_ofReal, div_ofReal_re]
  have : (2*(u*v)).re = 2*(u*v).re := by simp
  rw [this]
  have : 0 < c.re / t := by positivity
  linarith

/-- Bound for the integrand of DLMF 7.14.4: `‖erfc((at)^{1/2} + (c/t)^{1/2})‖ ≤ 1` and
`≤ e^{-Re a t}/√(π Re a t)`. -/
theorem erfInt_norm_erfc_plus_le {a c : ℂ} (ha : 0 < a.re) (hc : 0 < c.re) {t : ℝ} (ht : 0 < t) :
    ‖erfc ((a*t)^(1/2 : ℂ) + (c/t)^(1/2 : ℂ))‖ ≤ 1 ∧
      ‖erfc ((a*t)^(1/2 : ℂ) + (c/t)^(1/2 : ℂ))‖ ≤
        Real.exp (-(a.re*t))/Real.sqrt (π*(a.re*t)) := by
  obtain ⟨h1, h2⟩ := erfInt_re_sq_ge ha hc ht
  have hat : 0 < a.re*t := by positivity
  have h2' : 0 < (((a*t)^(1/2 : ℂ) + (c/t)^(1/2 : ℂ))^2).re := lt_of_lt_of_le hat h2
  refine ⟨norm_erfc_le_one h1 h2', (norm_erfc_le h1 h2').trans ?_⟩
  rw [Complex.norm_exp, neg_re]
  gcongr

/-- A uniform exponential majorant for the integrand of DLMF 7.14.4. -/
theorem erfInt_norm_plus_le {a b c : ℂ} (ha : 0 < a.re) (hc : 0 < c.re) {t : ℝ} (ht : 0 < t) :
    ‖exp ((a-b)*t)*erfc ((a*t)^(1/2 : ℂ) + (c/t)^(1/2 : ℂ))‖ ≤
      (Real.exp (|(a-b).re| + |b.re|) + 1/Real.sqrt (π*a.re)) * Real.exp (-(b.re*t)) := by
  obtain ⟨h1, h2⟩ := erfInt_norm_erfc_plus_le ha hc ht
  have hre : ((a-b)*(t:ℂ)).re = (a.re - b.re)*t := by simp [sub_re]
  rw [norm_mul, Complex.norm_exp, hre]
  have hK : 0 ≤ 1/Real.sqrt (π*a.re) := by positivity
  rcases le_or_gt t 1 with h | h
  · have e1 : Real.exp ((a.re - b.re)*t) ≤ Real.exp (|(a-b).re|) := by
      gcongr
      have : (a-b).re = a.re - b.re := sub_re a b
      rw [← this]
      calc (a-b).re * t ≤ |(a-b).re| * t := by gcongr; exact le_abs_self _
        _ ≤ |(a-b).re| * 1 := by gcongr
        _ = _ := mul_one _
    have e2 : 1 ≤ Real.exp (|b.re|) * Real.exp (-(b.re*t)) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      have : b.re * t ≤ |b.re| := by
        calc b.re * t ≤ |b.re| * t := by gcongr; exact le_abs_self _
          _ ≤ |b.re| * 1 := by gcongr
          _ = _ := mul_one _
      linarith
    calc Real.exp ((a.re - b.re)*t) * ‖erfc ((a*t)^(1/2 : ℂ) + (c/t)^(1/2 : ℂ))‖
        ≤ Real.exp (|(a-b).re|) * 1 := by gcongr
      _ ≤ Real.exp (|(a-b).re|) * (Real.exp (|b.re|) * Real.exp (-(b.re*t))) := by gcongr
      _ = Real.exp (|(a-b).re| + |b.re|) * Real.exp (-(b.re*t)) := by
          rw [Real.exp_add]; ring
      _ ≤ _ := by gcongr; linarith
  · have hs : Real.sqrt (π*a.re) ≤ Real.sqrt (π*(a.re*t)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (le_mul_of_one_le_right ha.le h.le)
        Real.pi_pos.le)
    have hs0 : 0 < Real.sqrt (π*a.re) := Real.sqrt_pos.2 (by positivity)
    calc Real.exp ((a.re - b.re)*t) * ‖erfc ((a*t)^(1/2 : ℂ) + (c/t)^(1/2 : ℂ))‖
        ≤ Real.exp ((a.re - b.re)*t) * (Real.exp (-(a.re*t))/Real.sqrt (π*(a.re*t))) := by
          gcongr
      _ ≤ Real.exp ((a.re - b.re)*t) * (Real.exp (-(a.re*t))/Real.sqrt (π*a.re)) := by gcongr
      _ = 1/Real.sqrt (π*a.re) * Real.exp (-(b.re*t)) := by
          rw [mul_div_assoc', ← Real.exp_add]; ring_nf
      _ ≤ _ := by
          gcongr
          linarith [Real.exp_pos (|(a-b).re| + |b.re|)]

/-- Continuity of the integrand of DLMF 7.14.4 on `(0, ∞)`. -/
theorem erfInt_continuousOn_plus (s : ℂ) {a c : ℂ} (ha : 0 ≤ a.re) (hc : 0 ≤ c.re) (σ : ℂ) :
    ContinuousOn (fun t : ℝ => exp (s*t)*erfc (σ*(a*t)^(1/2 : ℂ) + (c/t)^(1/2 : ℂ))) (Ioi 0) := by
  intro t ht
  have ht : (0:ℝ) < t := ht
  have ht' : (t:ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  refine ContinuousAt.continuousWithinAt ?_
  have hE : Continuous erfc := by
    unfold erfc; have := differentiable_erf_complex.continuous; fun_prop
  have h1 : ContinuousAt (fun t : ℝ => (a*t)^(1/2 : ℂ)) t := by
    refine (continuousAt_cpow_const_of_re_pos (Or.inl ?_) (by norm_num)).comp
      (by fun_prop : Continuous fun t : ℝ => a*(t:ℂ)).continuousAt
    rw [re_mul_ofReal]; positivity
  have h2 : ContinuousAt (fun t : ℝ => (c/t)^(1/2 : ℂ)) t := by
    refine (continuousAt_cpow_const_of_re_pos (Or.inl ?_) (by norm_num)).comp ?_
    · rw [div_ofReal_re]; positivity
    · exact (continuous_const.continuousAt).div (Complex.continuous_ofReal.continuousAt) ht'
  exact ((by fun_prop : Continuous fun t : ℝ => exp (s*t)).continuousAt).mul
    (hE.continuousAt.comp ((continuousAt_const.mul h1).add h2))

/-- **DLMF 7.14.4 for `Re c > 0`, `a ≠ b`.** -/
theorem erfInt_laplace_plus_of_re_pos {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re)
    (hab : a ≠ b) :
    (∫ t : ℝ in Ioi 0, exp ((a-b)*t)*erfc ((a*t)^(1/2 : ℂ)+(c/t)^(1/2 : ℂ))) =
      exp (-2*((a*c)^(1/2 : ℂ)+(b*c)^(1/2 : ℂ)))/(b^(1/2 : ℂ)*(a^(1/2 : ℂ)+b^(1/2 : ℂ))) := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  set α := a^(1/2 : ℂ) with hα
  set β := b^(1/2 : ℂ) with hβ
  set γ := c^(1/2 : ℂ) with hγ
  have hαr : 0 < α.re := re_cpow_half_pos ha
  have hβr : 0 < β.re := re_cpow_half_pos hb
  have hγr : 0 < γ.re := re_cpow_half_pos hc
  have hα2 : α^2 = a := cpow_half_sq ha0
  have hβ2 : β^2 = b := cpow_half_sq hb0
  have hγ2 : γ^2 = c := cpow_half_sq hc0
  have hp : a - b = α^2 - β^2 := by rw [hα2, hβ2]
  have hp0 : a - b ≠ 0 := sub_ne_zero.2 hab
  have hαβ : α + β ≠ 0 := fun h => by
    have := congrArg re h; simp at this; linarith
  -- the integrand in `√t` form
  have hform : ∀ t : ℝ, 0 < t → exp ((a-b)*t)*erfc ((a*t)^(1/2 : ℂ)+(c/t)^(1/2 : ℂ)) =
      exp ((a-b)*t)*erfc (α*Real.sqrt t+γ/Real.sqrt t) := by
    intro t ht
    rw [erfInt_cpow_half_mul_ofReal ha ht, erfInt_cpow_half_div_ofReal hc ht]
  have hint0 : IntegrableOn (fun t : ℝ => exp ((a-b)*t)*erfc ((a*t)^(1/2 : ℂ)+(c/t)^(1/2 : ℂ)))
      (Ioi 0) := by
    have hg : IntegrableOn (fun t : ℝ => (Real.exp (|(a-b).re| + |b.re|) +
        1/Real.sqrt (π*a.re)) * Real.exp (-(b.re*t))) (Ioi 0) := by
      have : IntegrableOn (fun t : ℝ => (Real.exp (|(a-b).re| + |b.re|) +
          1/Real.sqrt (π*a.re)) * Real.exp (-b.re*t)) (Ioi 0) :=
        (exp_neg_integrableOn_Ioi 0 hb).const_mul _
      refine this.congr_fun (fun t _ => by ring_nf) measurableSet_Ioi
    refine hg.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall
      fun t ht => erfInt_norm_plus_le ha hc ht))
    have := erfInt_continuousOn_plus (a-b) ha.le hc.le 1
    simp only [one_mul] at this
    exact this.aestronglyMeasurable measurableSet_Ioi
  have hint : IntegrableOn (fun t : ℝ => exp ((a-b)*t)*erfc (α*Real.sqrt t+γ/Real.sqrt t))
      (Ioi 0) := hint0.congr_fun (fun t ht => hform t ht) measurableSet_Ioi
  have hlim : Tendsto (fun x : ℝ => exp ((a-b)*(x:ℂ)^2)*erfc (α*x+γ/x)) atTop (𝓝 0) := by
    have hd : Tendsto (fun x : ℝ => (Real.exp (|(a-b).re| + |b.re|) + 1/Real.sqrt (π*a.re)) *
        Real.exp (-(b.re*x^2))) atTop (𝓝 0) := by
      have : Tendsto (fun x : ℝ => -(b.re*x^2)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp ((tendsto_pow_atTop two_ne_zero).const_mul_atTop hb)
      simpa using (Real.tendsto_exp_atBot.comp this).const_mul
        (Real.exp (|(a-b).re| + |b.re|) + 1/Real.sqrt (π*a.re))
    refine squeeze_zero_norm' ?_ hd
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hx2 : (0:ℝ) < x^2 := by positivity
    have := erfInt_norm_plus_le (b := b) ha hc hx2
    rw [hform _ hx2, Real.sqrt_sq hx.le] at this
    push_cast at this
    exact this
  have hcore := erfInt_laplace_core hp hp0 hβr (by rw [hβ2]; exact hb) hγr (by rw [hγ2]; exact hc)
    hαβ hint hlim
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => hform t ht), hcore,
    erfInt_cpow_half_mul ha hc, erfInt_cpow_half_mul hb hc]
  simp only [hα, hβ, hγ]
  congr 1
  ring_nf

/-- Continuity of `w ↦ w^{1/2}` at points with `Re w ≥ 0`. -/
theorem erfInt_continuousAt_cpow_half {w : ℂ} (hw : 0 ≤ w.re ∨ w.im ≠ 0) :
    ContinuousAt (fun z : ℂ => z^(1/2 : ℂ)) w :=
  continuousAt_cpow_const_of_re_pos hw (by norm_num)

/-- `ε ↦ (c+ε)/t` and the half power: continuity at `ε = 0` for `Re c ≥ 0`, `t > 0`. -/
theorem erfInt_tendsto_cpow_half_shift {c : ℂ} (hc : 0 ≤ c.re) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun ε : ℝ => ((c+ε)/t)^(1/2 : ℂ)) (𝓝[>] 0) (𝓝 ((c/t)^(1/2 : ℂ))) := by
  have hg : ContinuousAt (fun z : ℂ => z^(1/2:ℂ)) ((c + ((0:ℝ):ℂ))/(t:ℂ)) :=
    erfInt_continuousAt_cpow_half (Or.inl (by
      simp only [ofReal_zero, add_zero, div_ofReal_re]; positivity))
  have hf : ContinuousAt (fun ε : ℝ => (c+(ε:ℂ))/(t:ℂ)) 0 := by fun_prop
  have h : ContinuousAt (fun ε : ℝ => ((c+ε)/t)^(1/2 : ℂ)) 0 :=
    ContinuousAt.comp (g := fun z : ℂ => z^(1/2:ℂ)) hg hf
  have := h.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  simpa using this

/-- **DLMF 7.14.4** in full: `Re a > 0`, `Re b > 0`, `Re c ≥ 0`. From
`erfInt_laplace_plus_of_re_pos` by continuity in `(b, c) ↦ (b+ε, c+ε)`, `ε → 0⁺`. -/
theorem erfInt_laplace_plus {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 ≤ c.re) :
    (∫ t : ℝ in Ioi 0, exp ((a-b)*t)*erfc ((a*t)^(1/2 : ℂ)+(c/t)^(1/2 : ℂ))) =
      exp (-2*((a*c)^(1/2 : ℂ)+(b*c)^(1/2 : ℂ)))/(b^(1/2 : ℂ)*(a^(1/2 : ℂ)+b^(1/2 : ℂ))) := by
  set F : ℝ → ℝ → ℂ := fun ε t => exp ((a-(b+ε))*t)*erfc ((a*t)^(1/2 : ℂ)+((c+ε)/t)^(1/2 : ℂ))
    with hF
  set R : ℝ → ℂ := fun ε => exp (-2*((a*(c+ε))^(1/2 : ℂ)+((b+ε)*(c+ε))^(1/2 : ℂ)))/
    ((b+ε)^(1/2 : ℂ)*(a^(1/2 : ℂ)+(b+ε)^(1/2 : ℂ))) with hR
  have hre1 : ∀ ε : ℝ, 0 < ε → 0 < (b+ε).re ∧ 0 < (c+ε).re := fun ε hε => by
    simp only [add_re, ofReal_re]; constructor <;> linarith
  -- the integrals converge
  set K : ℝ := Real.exp (|(a-b).re| + 1 + (|b.re| + 1)) + 1/Real.sqrt (π*a.re) with hK
  have hI : Tendsto (fun ε => ∫ t in Ioi (0:ℝ), F ε t) (𝓝[>] 0) (𝓝 (∫ t in Ioi (0:ℝ), F 0 t)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => K * Real.exp (-b.re*t))
      ?_ ?_ ((exp_neg_integrableOn_Ioi 0 hb).const_mul K) ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have := erfInt_continuousOn_plus (a-(b+ε)) (a := a) (c := c+ε) ha.le (hre1 ε hε).2.le 1
      simp only [one_mul] at this
      exact this.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with ε hε
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
      have ht : (0:ℝ) < t := ht
      have h := erfInt_norm_plus_le (b := b+ε) ha (hre1 ε hε.1).2 ht
      refine h.trans ?_
      have e1 : |(a-(b+ε)).re| ≤ |(a-b).re| + 1 := by
        have : (a-(b+ε)).re = (a-b).re - ε := by simp [sub_re]; ring
        rw [this]
        calc |(a-b).re - ε| ≤ |(a-b).re| + |ε| := abs_sub _ _
          _ ≤ _ := by rw [abs_of_pos hε.1]; linarith [hε.2]
      have e2 : |(b+ε).re| ≤ |b.re| + 1 := by
        simp only [add_re, ofReal_re]
        calc |b.re + ε| ≤ |b.re| + |ε| := abs_add_le _ _
          _ ≤ _ := by rw [abs_of_pos hε.1]; linarith [hε.2]
      have e3 : Real.exp (-((b+ε).re*t)) ≤ Real.exp (-b.re*t) := by
        gcongr; simp only [add_re, ofReal_re]; nlinarith [hε.1]
      have hK' : Real.exp (|(a-(b+ε)).re| + |(b+ε).re|) + 1/Real.sqrt (π*a.re) ≤ K := by
        simp only [hK]; gcongr
      exact mul_le_mul hK' e3 (by positivity) (by simp only [hK]; positivity)
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
      have ht : (0:ℝ) < t := ht
      have hE : Continuous erfc := by
        unfold erfc; have := differentiable_erf_complex.continuous; fun_prop
      have h1 : Tendsto (fun ε : ℝ => exp ((a-(b+ε))*t)) (𝓝[>] 0) (𝓝 (exp ((a-(b+((0:ℝ):ℂ)))*t))) :=
        ((by fun_prop : Continuous fun ε : ℝ => exp ((a-(b+ε))*t)).tendsto 0).mono_left
          nhdsWithin_le_nhds
      have h2 := ((hE.tendsto _).comp ((erfInt_tendsto_cpow_half_shift hc ht).const_add
        ((a*t)^(1/2 : ℂ))))
      have := h1.mul h2
      simp only [ofReal_zero, add_zero] at this
      simpa [hF] using this
  -- the right-hand sides converge
  have hRc : Tendsto R (𝓝[>] 0) (𝓝 (R 0)) := by
    have hbc : ContinuousAt (fun ε : ℝ => (b+ε)^(1/2 : ℂ)) 0 :=
      ContinuousAt.comp (g := fun z : ℂ => z^(1/2:ℂ)) (f := fun ε : ℝ => b+(ε:ℂ))
        (erfInt_continuousAt_cpow_half (Or.inl (by simp; exact hb.le))) (by fun_prop)
    have hac : ContinuousAt (fun ε : ℝ => (a*(c+ε))^(1/2 : ℂ)) 0 :=
      ContinuousAt.comp (g := fun z : ℂ => z^(1/2:ℂ)) (f := fun ε : ℝ => a*(c+(ε:ℂ)))
        (erfInt_continuousAt_cpow_half (by simpa using erfInt_re_mul_nonneg_or ha hc))
        (by fun_prop)
    have hbc' : ContinuousAt (fun ε : ℝ => ((b+ε)*(c+ε))^(1/2 : ℂ)) 0 :=
      ContinuousAt.comp (g := fun z : ℂ => z^(1/2:ℂ)) (f := fun ε : ℝ => (b+(ε:ℂ))*(c+(ε:ℂ)))
        (erfInt_continuousAt_cpow_half (by simpa using erfInt_re_mul_nonneg_or hb hc))
        (by fun_prop)
    have hden : ((b+((0:ℝ):ℂ))^(1/2 : ℂ)*(a^(1/2 : ℂ)+(b+((0:ℝ):ℂ))^(1/2 : ℂ))) ≠ 0 := by
      simp only [ofReal_zero, add_zero]
      have h1 := re_cpow_half_pos hb
      have h2 := re_cpow_half_pos ha
      refine mul_ne_zero (fun h => by rw [h] at h1; simp at h1) (fun h => ?_)
      have := congrArg re h; simp at this; linarith
    have hcont : ContinuousAt R 0 := by
      simp only [hR]
      refine ContinuousAt.div ?_ (hbc.mul (continuousAt_const.add hbc)) hden
      exact ((continuousAt_const.mul (hac.add hbc')).cexp)
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  -- they agree for small `ε > 0`
  have hne : ∀ᶠ ε : ℝ in 𝓝[>] 0, a ≠ b + ε := by
    by_cases hab : a = b
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      intro h
      have : ((ε:ℝ):ℂ) = 0 := by linear_combination hab - h
      have : ε = 0 := by exact_mod_cast this
      exact (ne_of_gt (mem_Ioi.1 hε)) this
    · have hc' : Tendsto (fun ε : ℝ => b + (ε:ℂ)) (𝓝[>] 0) (𝓝 b) := by
        have := ((by fun_prop : Continuous fun ε : ℝ => b+(ε:ℂ)).tendsto 0).mono_left
          (nhdsWithin_le_nhds (s := Ioi 0))
        simpa using this
      filter_upwards [hc'.eventually_ne (Ne.symm hab)] with ε hε using Ne.symm hε
  have heq : (fun ε => ∫ t in Ioi (0:ℝ), F ε t) =ᶠ[𝓝[>] 0] R := by
    filter_upwards [self_mem_nhdsWithin, hne] with ε hε hab
    obtain ⟨h1, h2⟩ := hre1 ε hε
    exact erfInt_laplace_plus_of_re_pos ha h1 h2 hab
  have := tendsto_nhds_unique (hI.congr' heq) hRc
  simpa [hF, hR] using this

/-- A crude global bound: `‖erf w‖ ≤ (2/√π) ‖w‖ e^{max(0, -Re w²)}`. -/
theorem erfInt_norm_erf_le (w : ℂ) :
    ‖erf w‖ ≤ 2/Real.sqrt π * Real.exp (max 0 (-(w^2).re)) * ‖w‖ := by
  have hs : Convex ℝ (segment ℝ (0:ℂ) w) := convex_segment _ _
  have h := hs.norm_image_sub_le_of_norm_hasDerivWithin_le (f := erf)
    (f' := fun z => 2/Real.sqrt π*exp (-z^2))
    (C := 2/Real.sqrt π * Real.exp (max 0 (-(w^2).re)))
    (fun z _ => (hasDerivAt_erf_complex z).hasDerivWithinAt) (fun z hz => ?_)
    (left_mem_segment ℝ 0 w) (right_mem_segment ℝ 0 w)
  · have he : erf 0 = 0 := by simp [erf]
    simpa [he] using h
  · rw [segment_eq_image'] at hz
    obtain ⟨τ, ⟨hτ0, hτ1⟩, rfl⟩ := hz
    simp only [zero_add, sub_zero]
    have hπ : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
    rw [norm_mul, Complex.norm_exp, norm_div, Complex.norm_real, Real.norm_of_nonneg hπ.le]
    simp only [Complex.norm_ofNat]
    gcongr
    have : (-(τ • w)^2).re = -(τ^2 * (w^2).re) := by
      rw [real_smul, mul_pow, ← ofReal_pow, neg_re, re_ofReal_mul]
    rw [this]
    have h1 : τ^2 ≤ 1 := by nlinarith
    have h2 : 0 ≤ τ^2 := sq_nonneg τ
    rcases le_total 0 (w^2).re with h | h
    · have : 0 ≤ τ^2 * (w^2).re := mul_nonneg h2 h
      linarith [le_max_left 0 (-(w^2).re)]
    · have : (w^2).re ≤ τ^2 * (w^2).re := by nlinarith
      linarith [le_max_right 0 (-(w^2).re)]

/-- Bound for the integrand of the companion of DLMF 7.14.4: for `Re a > 0`, `Re c > 0`,
`‖c‖ ≤ M`, `t > 0`. -/
theorem erfInt_norm_erfc_minus_le {a c : ℂ} (ha : 0 < a.re) (hc : 0 < c.re) {M : ℝ}
    (hM : ‖c‖ ≤ M) {t : ℝ} (ht : 0 < t) :
    ‖erfc (-(a*t)^(1/2 : ℂ) + (c/t)^(1/2 : ℂ))‖ ≤ 1 + 2/Real.sqrt π *
      Real.exp (2*Real.sqrt (‖a‖*M)) * (Real.sqrt ‖a‖ * Real.sqrt t + Real.sqrt M / Real.sqrt t) := by
  have hat : 0 < (a*(t:ℂ)).re := by rw [re_mul_ofReal]; positivity
  have hct : 0 < (c/(t:ℂ)).re := by rw [div_ofReal_re]; positivity
  have hat0 : a*(t:ℂ) ≠ 0 := fun h => by rw [h] at hat; simp at hat
  have hct0 : c/(t:ℂ) ≠ 0 := fun h => by rw [h] at hct; simp at hct
  set u := (a*t)^(1/2 : ℂ)
  set v := (c/t)^(1/2 : ℂ)
  have hu2 : u^2 = a*t := cpow_half_sq hat0
  have hv2 : v^2 = c/t := cpow_half_sq hct0
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hnu : ‖u‖ = Real.sqrt ‖a‖ * Real.sqrt t := by
    have : ‖u‖^2 = ‖a‖ * t := by
      rw [← norm_pow, hu2, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
    rw [← Real.sqrt_mul (norm_nonneg _), ← this, Real.sqrt_sq (norm_nonneg _)]
  have hnv : ‖v‖ ≤ Real.sqrt M / Real.sqrt t := by
    have : ‖v‖^2 = ‖c‖ / t := by
      rw [← norm_pow, hv2, norm_div, Complex.norm_real, Real.norm_of_nonneg ht.le]
    rw [← Real.sqrt_div' _ ht.le, ← Real.sqrt_sq (norm_nonneg v), this]
    exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hM ht.le)
  have hw : ‖-u + v‖ ≤ Real.sqrt ‖a‖ * Real.sqrt t + Real.sqrt M / Real.sqrt t := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, hnu]; linarith
  have hre : max 0 (-((-u+v)^2).re) ≤ 2*Real.sqrt (‖a‖*M) := by
    have hsq : (-u+v)^2 = u^2 - 2*(u*v) + v^2 := by ring
    have h1 : -((-u+v)^2).re ≤ 2*‖u*v‖ := by
      rw [hsq, hu2, hv2]
      simp only [sub_re, add_re, re_mul_ofReal, div_ofReal_re]
      have : (2*(u*v)).re = 2*(u*v).re := by simp
      rw [this]
      have : 0 < a.re * t := by positivity
      have : 0 < c.re / t := by positivity
      have := re_le_norm (u*v)
      linarith
    have h2 : ‖u*v‖ ≤ Real.sqrt (‖a‖*M) := by
      rw [norm_mul, hnu]
      calc Real.sqrt ‖a‖ * Real.sqrt t * ‖v‖ ≤ Real.sqrt ‖a‖ * Real.sqrt t *
            (Real.sqrt M / Real.sqrt t) := by gcongr
        _ = Real.sqrt (‖a‖*M) := by
            rw [Real.sqrt_mul (norm_nonneg _)]; field_simp
    refine max_le (by positivity) (by linarith)
  have herf := erfInt_norm_erf_le (-u+v)
  have : erfc (-u+v) = 1 - erf (-u+v) := rfl
  rw [this]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one]
  gcongr
  calc ‖erf (-u+v)‖ ≤ 2/Real.sqrt π * Real.exp (max 0 (-((-u+v)^2).re)) * ‖-u+v‖ := herf
    _ ≤ 2/Real.sqrt π * Real.exp (2*Real.sqrt (‖a‖*M)) *
        (Real.sqrt ‖a‖ * Real.sqrt t + Real.sqrt M / Real.sqrt t) := by gcongr

/-- Integrability of `(A + B√t + C/√t) e^{-λt}` on `(0, ∞)`. -/
theorem erfInt_integrableOn_majorant {l : ℝ} (hl : 0 < l) (A B C : ℝ) :
    IntegrableOn (fun t : ℝ => (A + B*Real.sqrt t + C/Real.sqrt t) * Real.exp (-(l*t))) (Ioi 0) := by
  have h0 : IntegrableOn (fun t : ℝ => t^(0:ℝ) * Real.exp (-l * t^(1:ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) one_pos hl
  have h1 : IntegrableOn (fun t : ℝ => t^(1/2:ℝ) * Real.exp (-l * t^(1:ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) one_pos hl
  have h2 : IntegrableOn (fun t : ℝ => t^(-1/2:ℝ) * Real.exp (-l * t^(1:ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) one_pos hl
  have := ((h0.const_mul A).add (h1.const_mul B)).add (h2.const_mul C)
  refine IntegrableOn.congr_fun this (fun t ht => ?_) measurableSet_Ioi
  have ht : (0:ℝ) < t := ht
  simp only [Real.rpow_zero, Real.rpow_one, one_mul, Pi.add_apply]
  rw [Real.sqrt_eq_rpow, show (-1/2:ℝ) = -(1/2) by norm_num, Real.rpow_neg ht.le]
  ring_nf

/-- **Companion of DLMF 7.14.4 for `Re c > 0`.** -/
theorem erfInt_laplace_minus_of_re_pos {a b c : ℂ} (ha : 0 < a.re) (hba : 0 < (b-a).re)
    (hc : 0 < c.re) :
    (∫ t : ℝ in Ioi 0, exp ((a-b)*t)*erfc (-(a*t)^(1/2 : ℂ)+(c/t)^(1/2 : ℂ))) =
      exp (2*((a*c)^(1/2 : ℂ)-(b*c)^(1/2 : ℂ)))/(b^(1/2 : ℂ)*(b^(1/2 : ℂ)-a^(1/2 : ℂ))) := by
  have hb : 0 < b.re := by have : (b-a).re = b.re - a.re := sub_re b a; linarith
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  set α := -a^(1/2 : ℂ) with hα
  set β := b^(1/2 : ℂ) with hβ
  set γ := c^(1/2 : ℂ) with hγ
  have hβr : 0 < β.re := re_cpow_half_pos hb
  have hγr : 0 < γ.re := re_cpow_half_pos hc
  have hα2 : α^2 = a := by rw [hα, neg_sq]; exact cpow_half_sq ha0
  have hβ2 : β^2 = b := cpow_half_sq hb0
  have hγ2 : γ^2 = c := cpow_half_sq hc0
  have hp : a - b = α^2 - β^2 := by rw [hα2, hβ2]
  have hab : a ≠ b := fun h => by rw [h, sub_self] at hba; simp at hba
  have hp0 : a - b ≠ 0 := sub_ne_zero.2 hab
  have hαβ : α + β ≠ 0 := fun h => by
    have : β = a^(1/2 : ℂ) := by rw [hα] at h; linear_combination h
    apply hab; rw [← hβ2, this, cpow_half_sq ha0]
  have hform : ∀ t : ℝ, 0 < t → exp ((a-b)*t)*erfc (-(a*t)^(1/2 : ℂ)+(c/t)^(1/2 : ℂ)) =
      exp ((a-b)*t)*erfc (α*Real.sqrt t+γ/Real.sqrt t) := by
    intro t ht
    rw [erfInt_cpow_half_mul_ofReal ha ht, erfInt_cpow_half_div_ofReal hc ht, hα, neg_mul]
  set l := (b-a).re with hl
  set Cst := 2/Real.sqrt π * Real.exp (2*Real.sqrt (‖a‖*‖c‖)) with hCst
  have hbnd : ∀ t : ℝ, 0 < t → ‖exp ((a-b)*t)*erfc (-(a*t)^(1/2 : ℂ)+(c/t)^(1/2 : ℂ))‖ ≤
      (1 + Cst*Real.sqrt ‖a‖*Real.sqrt t + Cst*Real.sqrt ‖c‖/Real.sqrt t) * Real.exp (-(l*t)) := by
    intro t ht
    have h := erfInt_norm_erfc_minus_le ha hc le_rfl ht
    have hre : ((a-b)*(t:ℂ)).re = -(l*t) := by simp [hl, sub_re]; ring
    rw [norm_mul, Complex.norm_exp, hre, mul_comm]
    gcongr
    refine h.trans (le_of_eq ?_)
    simp only [hCst]; ring
  have hint0 : IntegrableOn (fun t : ℝ => exp ((a-b)*t)*erfc (-(a*t)^(1/2 : ℂ)+(c/t)^(1/2 : ℂ)))
      (Ioi 0) := by
    refine (erfInt_integrableOn_majorant hba _ _ _).mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun t ht => hbnd t ht))
    have := erfInt_continuousOn_plus (a-b) ha.le hc.le (-1)
    simp only [neg_one_mul] at this
    exact this.aestronglyMeasurable measurableSet_Ioi
  have hint : IntegrableOn (fun t : ℝ => exp ((a-b)*t)*erfc (α*Real.sqrt t+γ/Real.sqrt t))
      (Ioi 0) := hint0.congr_fun (fun t ht => hform t ht) measurableSet_Ioi
  have hlim : Tendsto (fun x : ℝ => exp ((a-b)*(x:ℂ)^2)*erfc (α*x+γ/x)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun x : ℝ => erfc (α*x+γ/x)) atTop (𝓝 (2 - 0)) := by
      have ha2 : 0 < ((a^(1/2 : ℂ))^2).re := by rw [cpow_half_sq ha0]; exact ha
      have := (erfInt_tendsto_erfc_atTop (re_cpow_half_pos ha) ha2 (-γ)).const_sub 2
      refine this.congr fun x => ?_
      rw [← erfc_negative]; congr 1; rw [hα]; ring
    have h1 : Tendsto (fun x : ℝ => exp ((a-b)*(x:ℂ)^2)) atTop (𝓝 0) := by
      refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
      have : Tendsto (fun x : ℝ => -(l*x^2)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp ((tendsto_pow_atTop two_ne_zero).const_mul_atTop hba)
      refine (Real.tendsto_exp_atBot.comp this).congr fun x => ?_
      have hre : ((a-b)*(x:ℂ)^2).re = -(l*x^2) := by
        rw [← ofReal_pow, re_mul_ofReal, hl]; simp [sub_re]; ring
      simp only [Function.comp_apply]; rw [Complex.norm_exp, hre]
    simpa using h1.mul h2
  have hcore := erfInt_laplace_core hp hp0 hβr (by rw [hβ2]; exact hb) hγr (by rw [hγ2]; exact hc)
    hαβ hint hlim
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => hform t ht), hcore,
    erfInt_cpow_half_mul ha hc, erfInt_cpow_half_mul hb hc]
  simp only [hα, hβ, hγ]
  congr 1
  · congr 1; ring
  · ring

/-- **Companion of DLMF 7.14.4** in full (`Re c ≥ 0`), by continuity in `c ↦ c + ε`. -/
theorem erfInt_laplace_minus {a b c : ℂ} (ha : 0 < a.re) (hba : 0 < (b-a).re) (hc : 0 ≤ c.re) :
    (∫ t : ℝ in Ioi 0, exp ((a-b)*t)*erfc (-(a*t)^(1/2 : ℂ)+(c/t)^(1/2 : ℂ))) =
      exp (2*((a*c)^(1/2 : ℂ)-(b*c)^(1/2 : ℂ)))/(b^(1/2 : ℂ)*(b^(1/2 : ℂ)-a^(1/2 : ℂ))) := by
  have hb : 0 < b.re := by have : (b-a).re = b.re - a.re := sub_re b a; linarith
  set F : ℝ → ℝ → ℂ := fun ε t => exp ((a-b)*t)*erfc (-(a*t)^(1/2 : ℂ)+((c+ε)/t)^(1/2 : ℂ))
    with hF
  set R : ℝ → ℂ := fun ε => exp (2*((a*(c+ε))^(1/2 : ℂ)-(b*(c+ε))^(1/2 : ℂ)))/
    (b^(1/2 : ℂ)*(b^(1/2 : ℂ)-a^(1/2 : ℂ))) with hR
  have hre1 : ∀ ε : ℝ, 0 < ε → 0 < (c+ε).re := fun ε hε => by
    simp only [add_re, ofReal_re]; linarith
  set l := (b-a).re with hl
  set M := ‖c‖ + 1 with hM
  set Cst := 2/Real.sqrt π * Real.exp (2*Real.sqrt (‖a‖*M)) with hCst
  have hI : Tendsto (fun ε => ∫ t in Ioi (0:ℝ), F ε t) (𝓝[>] 0) (𝓝 (∫ t in Ioi (0:ℝ), F 0 t)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t => (1 + Cst*Real.sqrt ‖a‖*Real.sqrt t + Cst*Real.sqrt M/Real.sqrt t) *
        Real.exp (-(l*t))) ?_ ?_ (erfInt_integrableOn_majorant hba _ _ _) ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have := erfInt_continuousOn_plus (a-b) (a := a) (c := c+ε) ha.le (hre1 ε hε).le (-1)
      simp only [neg_one_mul] at this
      exact this.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with ε hε
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
      have ht : (0:ℝ) < t := ht
      have hcM : ‖c+ε‖ ≤ M := by
        refine (norm_add_le _ _).trans ?_
        rw [Complex.norm_real, Real.norm_of_nonneg hε.1.le]; linarith [hε.2]
      have h := erfInt_norm_erfc_minus_le ha (hre1 ε hε.1) hcM ht
      have hre : ((a-b)*(t:ℂ)).re = -(l*t) := by simp [hl, sub_re]; ring
      simp only [hF]
      rw [norm_mul, Complex.norm_exp, hre, mul_comm]
      gcongr
      refine h.trans (le_of_eq ?_)
      simp only [hCst]; ring
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
      have ht : (0:ℝ) < t := ht
      have hE : Continuous erfc := by
        unfold erfc; have := differentiable_erf_complex.continuous; fun_prop
      have h2 := ((hE.tendsto _).comp ((erfInt_tendsto_cpow_half_shift hc ht).const_add
        (-(a*t)^(1/2 : ℂ))))
      have := h2.const_mul (exp ((a-b)*t))
      simpa [hF] using this
  have hRc : Tendsto R (𝓝[>] 0) (𝓝 (R 0)) := by
    have hac : ContinuousAt (fun ε : ℝ => (a*(c+ε))^(1/2 : ℂ)) 0 :=
      ContinuousAt.comp (g := fun z : ℂ => z^(1/2:ℂ)) (f := fun ε : ℝ => a*(c+(ε:ℂ)))
        (erfInt_continuousAt_cpow_half (by simpa using erfInt_re_mul_nonneg_or ha hc))
        (by fun_prop)
    have hbc : ContinuousAt (fun ε : ℝ => (b*(c+ε))^(1/2 : ℂ)) 0 :=
      ContinuousAt.comp (g := fun z : ℂ => z^(1/2:ℂ)) (f := fun ε : ℝ => b*(c+(ε:ℂ)))
        (erfInt_continuousAt_cpow_half (by simpa using erfInt_re_mul_nonneg_or hb hc))
        (by fun_prop)
    have hcont : ContinuousAt R 0 := by
      simp only [hR]
      exact ((continuousAt_const.mul (hac.sub hbc)).cexp).div_const _
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have heq : (fun ε => ∫ t in Ioi (0:ℝ), F ε t) =ᶠ[𝓝[>] 0] R := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact erfInt_laplace_minus_of_re_pos ha hba (hre1 ε hε)
  have := tendsto_nhds_unique (hI.congr' heq) hRc
  simpa [hF, hR] using this

/-- erfc sqrt reciprocal laplace. -/
@[dlmf 7.14.E4]
theorem erfc_sqrt_reciprocal_laplace {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 ≤ c.re) :
    (∫ t : ℝ in Ioi 0, exp ((a-b)*t)*erfc ((a*t)^(1/2 : ℂ)+(c/t)^(1/2 : ℂ)))=exp (-2*((a*c)^(1/2 : ℂ)+(b*c)^(1/2 : ℂ)))/(b^(1/2 : ℂ)*(a^(1/2 : ℂ)+b^(1/2 : ℂ))) :=
  erfInt_laplace_plus ha hb hc

/-- Unnumbered transform following DLMF 7.14.4. -/
theorem erfc_sqrt_reciprocal_laplace_negative {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < (b-a).re) (hc : 0 ≤ c.re) :
    (∫ t : ℝ in Ioi 0, exp ((a-b)*t)*erfc (-(a*t)^(1/2 : ℂ)+(c/t)^(1/2 : ℂ)))=exp (2*((a*c)^(1/2 : ℂ)-(b*c)^(1/2 : ℂ)))/(b^(1/2 : ℂ)*(b^(1/2 : ℂ)-a^(1/2 : ℂ))) :=
  erfInt_laplace_minus ha hb hc

/-- A continuous function with a limit at `+∞` is bounded on `[0, ∞)`. -/
theorem exists_bound_Ici_of_tendsto {g : ℝ → ℂ} {L : ℂ} (hg : Continuous g)
    (hL : Tendsto g atTop (𝓝 L)) : ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → ‖g t‖ ≤ B := by
  obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.mp hL) 1 one_pos
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := max T 0)).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨max C (‖L‖+1), fun t ht => ?_⟩
  by_cases h : t ≤ max T 0
  · exact (hC t ⟨ht, h⟩).trans (le_max_left _ _)
  · have h1 := hT t ((le_max_left T 0).trans (not_le.mp h).le)
    rw [dist_eq_norm] at h1
    have : ‖g t‖ ≤ ‖g t - L‖ + ‖L‖ := by
      simpa using norm_add_le (g t - L) L
    exact (by linarith : ‖g t‖ ≤ ‖L‖+1).trans (le_max_right _ _)

/-- Laplace transform of a bounded function `u` with `u 0 = 0`, computed from an antiderivative
`G` of `e^{-at} u'(t)/a`, by integration by parts. -/
theorem integral_exp_mul_eq_of_antideriv {a : ℂ} (ha : 0 < a.re) {u u' G : ℝ → ℂ} {B : ℝ}
    {L : ℂ} (hu : Continuous u) (hu0 : u 0 = 0) (hB : ∀ t : ℝ, 0 ≤ t → ‖u t‖ ≤ B)
    (hud : ∀ t : ℝ, 0 < t → HasDerivAt u (u' t) t) (hG : ContinuousWithinAt G (Ici 0) 0)
    (hG0 : G 0 = 0) (hGd : ∀ t : ℝ, 0 < t → HasDerivAt G (exp (-a*t)*u' t/a) t)
    (hGl : Tendsto G atTop (𝓝 L)) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*u t) = L := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  set F : ℝ → ℂ := fun t => -(exp (-a*t)/a)*u t + G t with hF
  have hexp (t : ℝ) : HasDerivAt (fun t : ℝ => exp (-a*(t:ℂ))) (exp (-a*t)*(-a)) t := by
    have := ((hasDerivAt_id (t:ℂ)).const_mul (-a)).cexp
    simpa using this.comp_ofReal
  have hd : ∀ t : ℝ, 0 < t → HasDerivAt F (exp (-a*t)*u t) t := by
    intro t ht
    have h := (((hexp t).div_const a).mul (hud t ht)).neg.add (hGd t ht)
    convert h using 1
    · funext s; simp [hF, div_eq_mul_inv]
    · field_simp
      ring
  have hre (t : ℝ) : (-a*(t:ℂ)).re = -a.re*t := by simp
  have hcont : ContinuousWithinAt F (Ici 0) 0 := by
    refine ContinuousWithinAt.add ?_ hG
    exact ((by fun_prop : Continuous fun t : ℝ => exp (-a*t)/a).neg.mul hu).continuousWithinAt
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 le_rfl)
  have hdecay : Tendsto (fun t : ℝ => Real.exp (-a.re*t)) atTop (𝓝 0) := by
    have : Tendsto (fun t : ℝ => -a.re*t) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (by linarith)
    exact Real.tendsto_exp_atBot.comp this
  have hlim : Tendsto F atTop (𝓝 (0 + L)) := by
    refine Tendsto.add ?_ hGl
    have hev : ∀ᶠ t : ℝ in atTop, ‖-(exp (-a*t)/a)*u t‖ ≤ B/‖a‖*Real.exp (-a.re*t) := by
      filter_upwards [eventually_ge_atTop 0] with t ht
      rw [norm_mul, norm_neg, norm_div, Complex.norm_exp, hre]
      calc Real.exp (-a.re*t)/‖a‖*‖u t‖ ≤ Real.exp (-a.re*t)/‖a‖*B := by
            gcongr; exact hB t ht
        _ = _ := by ring
    refine squeeze_zero_norm' hev ?_
    simpa using hdecay.const_mul (B/‖a‖)
  have hint : IntegrableOn (fun t : ℝ => exp (-a*t)*u t) (Ioi 0) := by
    have hg : IntegrableOn (fun t : ℝ => B*Real.exp (-a.re*t)) (Ioi 0) :=
      ((exp_neg_integrableOn_Ioi 0 ha).const_mul B :)
    refine hg.mono' ((by fun_prop : Continuous fun t : ℝ => exp (-a*t)).mul hu).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [norm_mul, Complex.norm_exp, hre, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB t (le_of_lt ht)) (Real.exp_pos _).le
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont (fun t ht => hd t ht) hint hlim]
  simp [hF, hu0, hG0]

/-- Derivative of `w⁻¹ erf(w √t)`: it equals `e^{-w² t}/√(π t)`. -/
theorem hasDerivAt_recip_mul_erf_sqrt {w : ℂ} (hw : w ≠ 0) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => w⁻¹*erf (w*(Real.sqrt t : ℂ)))
      (exp (-(w^2*t))/((Real.sqrt π:ℂ)*(Real.sqrt t:ℂ))) t := by
  have hs : HasDerivAt (fun t : ℝ => ((Real.sqrt t:ℝ):ℂ)) ((1/(2*Real.sqrt t):ℝ):ℂ) t :=
    (Real.hasDerivAt_sqrt ht.ne').ofReal_comp
  have h := ((hasDerivAt_erf_complex _).comp t (hs.const_mul w)).const_mul w⁻¹
  refine h.congr_deriv ?_
  have hst : (Real.sqrt t:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr ht).ne'
  have hsp : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hsq : ((Real.sqrt t:ℂ))^2 = t := by exact_mod_cast Real.sq_sqrt ht.le
  rw [mul_pow, hsq]
  push_cast
  field_simp

/-- `w⁻¹ erf(w √t) → w⁻¹` as `t → ∞` when `Re w > 0` and `Re w² > 0`. -/
theorem tendsto_recip_mul_erf_sqrt {w : ℂ} (hw : 0 < w.re) (hw2 : 0 < (w^2).re) :
    Tendsto (fun t : ℝ => w⁻¹*erf (w*(Real.sqrt t : ℂ))) atTop (𝓝 (w⁻¹*1)) := by
  refine Tendsto.const_mul _ ?_
  have h0 : Tendsto (fun t : ℝ => erfc (w*(Real.sqrt t : ℂ))) atTop (𝓝 0) := by
    refine tendsto_erfc_zero_of_re_sq ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with t ht
      rw [re_mul_ofReal]; exact mul_pos hw (Real.sqrt_pos.mpr ht)
    · have h0 : Tendsto (fun t : ℝ => (w^2).re*t) atTop atTop := tendsto_id.const_mul_atTop' hw2
      refine h0.congr' ?_
      filter_upwards [eventually_ge_atTop 0] with t ht
      rw [mul_pow, ← ofReal_pow, Real.sq_sqrt ht, re_mul_ofReal]
  have := h0.const_sub 1
  simp only [sub_zero] at this
  refine this.congr fun t => ?_
  simp [erfc]

/-- `π √(2t/π) = √2 √π √t`. -/
theorem pi_mul_sqrt_two_mul_div_pi {t : ℝ} (ht : 0 ≤ t) :
    π*Real.sqrt (2*t/π) = Real.sqrt 2*Real.sqrt π*Real.sqrt t := by
  have hp := Real.pi_pos
  refine (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp ?_
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
    Real.sq_sqrt hp.le, Real.sq_sqrt ht]
  field_simp

/-- Derivative of `t ↦ √(2t/π)` (as a complex-valued function). -/
theorem hasDerivAt_sqrt_two_mul_div_pi {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => ((Real.sqrt (2*t/π):ℝ):ℂ)) (((1/(π*Real.sqrt (2*t/π))):ℝ):ℂ) t := by
  have hp := Real.pi_pos
  have hne : 2*t/π ≠ 0 := by positivity
  have h := ((Real.hasDerivAt_sqrt hne).comp t (((hasDerivAt_id t).const_mul 2).div_const π)).ofReal_comp
  refine h.congr_deriv ?_
  congr 1
  have : 0 < Real.sqrt (2*t/π) := Real.sqrt_pos.mpr (by positivity)
  field_simp

/-- `(√(2t/π))² π/2 = t`. -/
theorem pi_mul_sqrt_two_mul_div_pi_sq {t : ℝ} (ht : 0 ≤ t) :
    (π:ℂ)*((Real.sqrt (2*t/π):ℝ):ℂ)^2/2 = t := by
  rw [← ofReal_pow, Real.sq_sqrt (by have := Real.pi_pos; positivity)]
  have : (π:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-- If `Re u, Re u², Re v, Re v² > 0` then `Re (u v) > 0`. -/
theorem re_mul_pos_of_re_sq {u v : ℂ} (hu : 0 < u.re) (hu2 : 0 < (u^2).re) (hv : 0 < v.re)
    (hv2 : 0 < (v^2).re) : 0 < (u*v).re := by
  have e1 : (u^2).re = u.re^2 - u.im^2 := by simp [sq]
  have e2 : (v^2).re = v.re^2 - v.im^2 := by simp [sq]
  have hlt : (u.im*v.im)^2 < (u.re*v.re)^2 := by
    rw [mul_pow, mul_pow]
    have h3 : u.im^2*v.im^2 ≤ u.re^2*v.im^2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    have h4 : u.re^2*v.im^2 < u.re^2*v.re^2 := mul_lt_mul_of_pos_left (by linarith) (by positivity)
    linarith
  have := abs_lt_of_sq_lt_sq hlt (by positivity)
  rw [mul_re]
  linarith [le_abs_self (u.im*v.im)]

/-- The Fresnel functions along `√(2t/π)` are bounded on `[0, ∞)`. -/
theorem exists_bound_fresnel_sqrt {f : ℂ → ℂ} {g : ℝ → ℝ} (hf : Differentiable ℂ f)
    (hfg : ∀ x : ℝ, f x = g x) (hg : Tendsto g atTop (𝓝 (1/2))) :
    ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → ‖f ((Real.sqrt (2*t/π):ℝ):ℂ)‖ ≤ B := by
  refine exists_bound_Ici_of_tendsto (L := ((1/2:ℝ):ℂ)) (hf.continuous.comp (by fun_prop)) ?_
  have hs : Tendsto (fun t : ℝ => Real.sqrt (2*t/π)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp ((tendsto_id.const_mul_atTop' two_pos).atTop_div_const Real.pi_pos)
  have := ((continuous_ofReal.tendsto _).comp hg).comp hs
  refine this.congr fun t => ?_
  simp [hfg]

/-- Integration by parts for a Laplace transform: if `u` is bounded on `[0, ∞)` with `u 0 = 0`
and continuous derivative `u'`, then `∫₀^∞ e^{-at} u = a⁻¹ ∫₀^∞ e^{-at} u'`. -/
theorem integral_exp_mul_eq_of_deriv {a : ℂ} (ha : 0 < a.re) {u u' : ℝ → ℂ} {B : ℝ}
    (hu : Continuous u) (hu0 : u 0 = 0) (hB : ∀ t : ℝ, 0 ≤ t → ‖u t‖ ≤ B)
    (hud : ∀ t : ℝ, 0 < t → HasDerivAt u (u' t) t) (hu' : Continuous u')
    (hi : IntegrableOn (fun t : ℝ => exp (-a*t)*u' t) (Ioi 0)) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*u t) = (∫ t : ℝ in Ioi 0, exp (-a*t)*u' t)/a := by
  have hc : Continuous fun t : ℝ => exp (-a*t)*u' t := by fun_prop
  refine integral_exp_mul_eq_of_antideriv ha hu hu0 hB hud
    (G := fun t => (∫ s in (0:ℝ)..t, exp (-a*s)*u' s)/a) ?_ (by simp) ?_ ?_
  · exact (continuous_iff_continuousAt.mpr fun t =>
      ((hc.integral_hasStrictDerivAt 0 t).hasDerivAt.div_const a).continuousAt).continuousWithinAt
  · exact fun t _ => (hc.integral_hasStrictDerivAt 0 t).hasDerivAt.div_const a
  · exact (intervalIntegral_tendsto_integral_Ioi 0 hi tendsto_id).div_const a

/-- Laplace transform of `cos(πt²/2)`. -/
theorem laplace_cos_pi_sq {a : ℂ} (ha : 0 < a.re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*cos (π*(t:ℂ)^2/2)) = fresnelAuxFComplex (a/π) := by
  set c : ℝ := Real.sqrt (π/2)
  have hc : 0 < c := Real.sqrt_pos.mpr (by positivity)
  have hc0 : (c:ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hc2 : (c:ℂ)^2 = π/2 := by
    have := Real.sq_sqrt (by positivity : (0:ℝ) ≤ π/2); exact_mod_cast this
  have hre : 0 < (a/c).re := by rw [div_ofReal_re]; exact div_pos ha hc
  have h := integral_comp_mul_left_Ioi (fun x : ℝ => exp (-(a/c)*x)*cos ((x:ℂ)^2)) 0 hc
  rw [mul_zero, fresnelAuxFComplex_laplace_square hre] at h
  have e : (fun x : ℝ => exp (-(a/c)*((c*x:ℝ):ℂ))*cos (((c*x:ℝ):ℂ)^2)) =
      fun t : ℝ => exp (-a*t)*cos (π*(t:ℂ)^2/2) := by
    funext t; push_cast
    rw [mul_pow, hc2]; congr 2
    · field_simp
    · ring
  simp only [e] at h
  rw [h, real_smul]
  have h2 : (a/(c:ℂ))/((Real.sqrt (2*π):ℝ):ℂ) = a/π := by
    have : (c:ℂ)*((Real.sqrt (2*π):ℝ):ℂ) = π := by
      simp only [c]; rw [← ofReal_mul, ← Real.sqrt_mul (by positivity)]
      rw [show π/2*(2*π) = π^2 by ring, Real.sqrt_sq Real.pi_pos.le]
    rw [div_div, this]
  rw [h2]; push_cast; field_simp; rfl

/-- Laplace transform of `sin(πt²/2)`. -/
theorem laplace_sin_pi_sq {a : ℂ} (ha : 0 < a.re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*sin (π*(t:ℂ)^2/2)) = fresnelAuxGComplex (a/π) := by
  set c : ℝ := Real.sqrt (π/2)
  have hc : 0 < c := Real.sqrt_pos.mpr (by positivity)
  have hc0 : (c:ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hc2 : (c:ℂ)^2 = π/2 := by
    have := Real.sq_sqrt (by positivity : (0:ℝ) ≤ π/2); exact_mod_cast this
  have hre : 0 < (a/c).re := by rw [div_ofReal_re]; exact div_pos ha hc
  have h := integral_comp_mul_left_Ioi (fun x : ℝ => exp (-(a/c)*x)*sin ((x:ℂ)^2)) 0 hc
  rw [mul_zero, fresnelAuxGComplex_laplace_square hre] at h
  have e : (fun x : ℝ => exp (-(a/c)*((c*x:ℝ):ℂ))*sin (((c*x:ℝ):ℂ)^2)) =
      fun t : ℝ => exp (-a*t)*sin (π*(t:ℂ)^2/2) := by
    funext t; push_cast
    rw [mul_pow, hc2]; congr 2
    · field_simp
    · ring
  simp only [e] at h
  rw [h, real_smul]
  have h2 : (a/(c:ℂ))/((Real.sqrt (2*π):ℝ):ℂ) = a/π := by
    have : (c:ℂ)*((Real.sqrt (2*π):ℝ):ℂ) = π := by
      simp only [c]; rw [← ofReal_mul, ← Real.sqrt_mul (by positivity)]
      rw [show π/2*(2*π) = π^2 by ring, Real.sqrt_sq Real.pi_pos.le]
    rw [div_div, this]
  rw [h2]; push_cast; field_simp; rfl

/-- fresnelCosInt laplace. -/
@[dlmf 7.14.E5]
theorem fresnelCosInt_laplace {a : ℂ} (ha : 0 < a.re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*fresnelCosInt t)=fresnelAuxFComplex (a/π)/a := by
  obtain ⟨B, hB⟩ := exists_bound_Ici_of_tendsto (L := ((1/2:ℝ):ℂ))
    (g := fun t : ℝ => fresnelCosInt (t:ℂ)) (fresnelCosInt_entire.continuous.comp continuous_ofReal)
    (((continuous_ofReal.tendsto _).comp Real.tendsto_fresnelCosInt_atTop).congr
      fun t => (fresnelCosInt_ofReal t).symm)
  have hi : IntegrableOn (fun t : ℝ => exp (-a*t)*cos (π*(t:ℂ)^2/2)) (Ioi 0) := by
    refine (exp_neg_integrableOn_Ioi 0 ha).mono' (by fun_prop : Continuous fun t : ℝ =>
      exp (-a*t)*cos (π*(t:ℂ)^2/2)).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [norm_mul, Complex.norm_exp]
    have : (-a*(t:ℂ)).re = -a.re*t := by simp
    rw [this]
    have h1 : ‖cos (π*(t:ℂ)^2/2)‖ ≤ 1 := by
      rw [show (π:ℂ)*(t:ℂ)^2/2 = ((π*t^2/2:ℝ):ℂ) by push_cast; ring, ← ofReal_cos, norm_real,
        Real.norm_eq_abs]
      exact Real.abs_cos_le_one _
    simpa using mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-a.re*t)).le
  rw [integral_exp_mul_eq_of_deriv ha (u := fun t : ℝ => fresnelCosInt (t:ℂ)) (fresnelCosInt_entire.continuous.comp continuous_ofReal)
    (by simpa using (fresnelCosInt_ofReal 0).trans (by simp [Real.fresnelCosInt])) hB
    (fun t _ => (hasDerivAt_fresnelCosInt_complex t).comp_ofReal) (by fun_prop) hi,
    laplace_cos_pi_sq ha]

/-- fresnelCosInt sqrt laplace. -/
@[dlmf 7.14.E7]
theorem fresnelCosInt_sqrt_laplace {a : ℂ} (ha : 0 < a.re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*fresnelCosInt (Real.sqrt (2*t/π)))=(((a^2+1)^(1/2 : ℂ))+a)^(1/2 : ℂ)/(2*a*(a^2+1)^(1/2 : ℂ)) := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hm : (0:ℝ) < (a-I).re := by simpa using ha
  have hp : (0:ℝ) < (a+I).re := by simpa using ha
  set u1 := (a-I)^(1/2 : ℂ); set v1 := (a+I)^(1/2 : ℂ)
  have hu1 : u1^2 = a-I := cpow_half_sq (fun h => by simp [h] at hm)
  have hv1 : v1^2 = a+I := cpow_half_sq (fun h => by simp [h] at hp)
  have hu1r : 0 < u1.re := re_cpow_half_pos hm
  have hv1r : 0 < v1.re := re_cpow_half_pos hp
  have hu10 : u1 ≠ 0 := fun h => by simp [h] at hu1r
  have hv10 : v1 ≠ 0 := fun h => by simp [h] at hv1r
  have hu1r2 : 0 < (u1^2).re := by rw [hu1]; exact hm
  have hv1r2 : 0 < (v1^2).re := by rw [hv1]; exact hp
  have hs2 : (Real.sqrt 2:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr two_pos).ne'
  have hsp : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hec : Continuous erf := differentiable_erf_complex.continuous
  obtain ⟨B, hB⟩ := exists_bound_fresnel_sqrt fresnelCosInt_entire fresnelCosInt_ofReal
    Real.tendsto_fresnelCosInt_atTop
  set k : ℂ := 1/(2*a*Real.sqrt 2)
  have key := integral_exp_mul_eq_of_antideriv (a := a) (B := B) ha
    (u := fun t : ℝ => fresnelCosInt ((Real.sqrt (2*t/π):ℝ):ℂ))
    (u' := fun t : ℝ => cos (t:ℂ)*(((1/(π*Real.sqrt (2*t/π))):ℝ):ℂ))
    (G := fun t : ℝ => k*(u1⁻¹*erf (u1*(Real.sqrt t:ℂ)) + v1⁻¹*erf (v1*(Real.sqrt t:ℂ))))
    (L := k*(u1⁻¹*1 + v1⁻¹*1))
    (fresnelCosInt_entire.continuous.comp (by fun_prop))
    (by have h0 := fresnelCosInt_ofReal 0; simp [Real.fresnelCosInt] at h0; simpa using h0) hB
    (fun t ht => by
      have h := (hasDerivAt_fresnelCosInt_complex _).comp t (hasDerivAt_sqrt_two_mul_div_pi ht)
      rw [pi_mul_sqrt_two_mul_div_pi_sq ht.le] at h
      exact h)
    ((by fun_prop : Continuous fun t : ℝ =>
      k*(u1⁻¹*erf (u1*(Real.sqrt t:ℂ)) + v1⁻¹*erf (v1*(Real.sqrt t:ℂ)))).continuousWithinAt)
    (by simp [erf_zero])
    (fun t ht => by
      have h := (((hasDerivAt_recip_mul_erf_sqrt hu10 ht).add
        (hasDerivAt_recip_mul_erf_sqrt hv10 ht)).const_mul k)
      refine h.congr_deriv ?_
      rw [hu1, hv1, pi_mul_sqrt_two_mul_div_pi ht.le]
      have hst : (Real.sqrt t:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr ht).ne'
      have e1 : exp (-((a-I)*t)) = exp (-a*t)*exp (t*I) := by
        rw [← Complex.exp_add]; congr 1; ring
      have e2 : exp (-((a+I)*t)) = exp (-a*t)*exp (-t*I) := by
        rw [← Complex.exp_add]; congr 1; ring
      rw [e1, e2, Complex.cos]
      simp only [k]
      push_cast
      field_simp)
    (((tendsto_recip_mul_erf_sqrt hu1r hu1r2).add (tendsto_recip_mul_erf_sqrt hv1r hv1r2)).const_mul k)
  rw [key]
  have huv : (a^2+1)^(1/2 : ℂ) = u1*v1 := by
    rw [show a^2+1 = (u1*v1)^2 by rw [mul_pow, hu1, hv1]; ring_nf; rw [I_sq]; ring]
    exact sq_cpow_half (re_mul_pos_of_re_sq hu1r hu1r2 hv1r hv1r2)
  have hw : (u1*v1+a)^(1/2 : ℂ) = (u1+v1)/Real.sqrt 2 := by
    have h2 : ((Real.sqrt 2:ℂ))^2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    rw [show u1*v1+a = ((u1+v1)/Real.sqrt 2)^2 by
      rw [div_pow, h2, add_sq, hu1, hv1]; ring]
    refine sq_cpow_half ?_
    rw [div_ofReal_re]
    exact div_pos (by simp; linarith) (Real.sqrt_pos.mpr two_pos)
  rw [huv, hw]
  simp only [k]
  field_simp
  ring

/-- fresnelSinInt laplace. -/
@[dlmf 7.14.E6]
theorem fresnelSinInt_laplace {a : ℂ} (ha : 0 < a.re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*fresnelSinInt t)=fresnelAuxGComplex (a/π)/a := by
  obtain ⟨B, hB⟩ := exists_bound_Ici_of_tendsto (L := ((1/2:ℝ):ℂ))
    (g := fun t : ℝ => fresnelSinInt (t:ℂ)) (fresnelSinInt_entire.continuous.comp continuous_ofReal)
    (((continuous_ofReal.tendsto _).comp Real.tendsto_fresnelSinInt_atTop).congr
      fun t => (fresnelSinInt_ofReal t).symm)
  have hi : IntegrableOn (fun t : ℝ => exp (-a*t)*sin (π*(t:ℂ)^2/2)) (Ioi 0) := by
    refine (exp_neg_integrableOn_Ioi 0 ha).mono' (by fun_prop : Continuous fun t : ℝ =>
      exp (-a*t)*sin (π*(t:ℂ)^2/2)).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [norm_mul, Complex.norm_exp]
    have : (-a*(t:ℂ)).re = -a.re*t := by simp
    rw [this]
    have h1 : ‖sin (π*(t:ℂ)^2/2)‖ ≤ 1 := by
      rw [show (π:ℂ)*(t:ℂ)^2/2 = ((π*t^2/2:ℝ):ℂ) by push_cast; ring, ← ofReal_sin, norm_real,
        Real.norm_eq_abs]
      exact Real.abs_sin_le_one _
    simpa using mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-a.re*t)).le
  rw [integral_exp_mul_eq_of_deriv ha (u := fun t : ℝ => fresnelSinInt (t:ℂ)) (fresnelSinInt_entire.continuous.comp continuous_ofReal)
    (by simpa using (fresnelSinInt_ofReal 0).trans (by simp [Real.fresnelSinInt])) hB
    (fun t _ => (hasDerivAt_fresnelSinInt_complex t).comp_ofReal) (by fun_prop) hi,
    laplace_sin_pi_sq ha]

/-- fresnelSinInt sqrt laplace. -/
@[dlmf 7.14.E8]
theorem fresnelSinInt_sqrt_laplace {a : ℂ} (ha : 0 < a.re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*fresnelSinInt (Real.sqrt (2*t/π)))=(((a^2+1)^(1/2 : ℂ))-a)^(1/2 : ℂ)/(2*a*(a^2+1)^(1/2 : ℂ)) := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hm : (0:ℝ) < (a-I).re := by simpa using ha
  have hp : (0:ℝ) < (a+I).re := by simpa using ha
  set u1 := (a-I)^(1/2 : ℂ); set v1 := (a+I)^(1/2 : ℂ)
  have hu1 : u1^2 = a-I := cpow_half_sq (fun h => by simp [h] at hm)
  have hv1 : v1^2 = a+I := cpow_half_sq (fun h => by simp [h] at hp)
  have hu1r : 0 < u1.re := re_cpow_half_pos hm
  have hv1r : 0 < v1.re := re_cpow_half_pos hp
  have hu10 : u1 ≠ 0 := fun h => by simp [h] at hu1r
  have hv10 : v1 ≠ 0 := fun h => by simp [h] at hv1r
  have hu1r2 : 0 < (u1^2).re := by rw [hu1]; exact hm
  have hv1r2 : 0 < (v1^2).re := by rw [hv1]; exact hp
  have hs2 : (Real.sqrt 2:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr two_pos).ne'
  have hsp : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hec : Continuous erf := differentiable_erf_complex.continuous
  obtain ⟨B, hB⟩ := exists_bound_fresnel_sqrt fresnelSinInt_entire fresnelSinInt_ofReal
    Real.tendsto_fresnelSinInt_atTop
  set k : ℂ := 1/(2*a*Real.sqrt 2*I)
  have key := integral_exp_mul_eq_of_antideriv (a := a) (B := B) ha
    (u := fun t : ℝ => fresnelSinInt ((Real.sqrt (2*t/π):ℝ):ℂ))
    (u' := fun t : ℝ => sin (t:ℂ)*(((1/(π*Real.sqrt (2*t/π))):ℝ):ℂ))
    (G := fun t : ℝ => k*(u1⁻¹*erf (u1*(Real.sqrt t:ℂ)) - v1⁻¹*erf (v1*(Real.sqrt t:ℂ))))
    (L := k*(u1⁻¹*1 - v1⁻¹*1))
    (fresnelSinInt_entire.continuous.comp (by fun_prop))
    (by have h0 := fresnelSinInt_ofReal 0; simp [Real.fresnelSinInt] at h0; simpa using h0) hB
    (fun t ht => by
      have h := (hasDerivAt_fresnelSinInt_complex _).comp t (hasDerivAt_sqrt_two_mul_div_pi ht)
      rw [pi_mul_sqrt_two_mul_div_pi_sq ht.le] at h
      exact h)
    ((by fun_prop : Continuous fun t : ℝ =>
      k*(u1⁻¹*erf (u1*(Real.sqrt t:ℂ)) - v1⁻¹*erf (v1*(Real.sqrt t:ℂ)))).continuousWithinAt)
    (by simp [erf_zero])
    (fun t ht => by
      have h := (((hasDerivAt_recip_mul_erf_sqrt hu10 ht).sub
        (hasDerivAt_recip_mul_erf_sqrt hv10 ht)).const_mul k)
      refine h.congr_deriv ?_
      rw [hu1, hv1, pi_mul_sqrt_two_mul_div_pi ht.le]
      have hst : (Real.sqrt t:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr ht).ne'
      have e1 : exp (-((a-I)*t)) = exp (-a*t)*exp (t*I) := by
        rw [← Complex.exp_add]; congr 1; ring
      have e2 : exp (-((a+I)*t)) = exp (-a*t)*exp (-t*I) := by
        rw [← Complex.exp_add]; congr 1; ring
      rw [e1, e2, Complex.sin]
      simp only [k]
      push_cast
      field_simp
      ring_nf
      rw [I_sq]
      ring)
    (((tendsto_recip_mul_erf_sqrt hu1r hu1r2).sub (tendsto_recip_mul_erf_sqrt hv1r hv1r2)).const_mul k)
  rw [key]
  have huv : (a^2+1)^(1/2 : ℂ) = u1*v1 := by
    rw [show a^2+1 = (u1*v1)^2 by rw [mul_pow, hu1, hv1]; ring_nf; rw [I_sq]; ring]
    exact sq_cpow_half (re_mul_pos_of_re_sq hu1r hu1r2 hv1r hv1r2)
  have hw : (u1*v1-a)^(1/2 : ℂ) = (v1-u1)/(Real.sqrt 2*I) := by
    have h2 : ((Real.sqrt 2:ℂ))^2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    rw [show u1*v1-a = ((v1-u1)/(Real.sqrt 2*I))^2 by
      rw [div_pow, mul_pow, h2, I_sq, sub_sq, hu1, hv1]; field_simp; ring]
    refine sq_cpow_half ?_
    -- `Im (v1 - u1) > 0` since `(v1 - u1)(v1 + u1) = 2i` and `Re (v1 + u1) > 0`
    have hdw : (v1-u1)*(v1+u1) = 2*I := by
      rw [show (v1-u1)*(v1+u1) = v1^2-u1^2 by ring, hu1, hv1]; ring
    have hre := congrArg Complex.re hdw
    have him := congrArg Complex.im hdw
    simp only [mul_re, mul_im, sub_re, sub_im, add_re, add_im] at hre him
    norm_num at hre him
    have hwr : 0 < v1.re + u1.re := by linarith
    have hdim : 0 < v1.im - u1.im := by
      have hS : (v1.im-u1.im)*((v1.im+u1.im)^2+(v1.re+u1.re)^2) = 2*(v1.re+u1.re) := by
        linear_combination (-(v1.im+u1.im))*hre + (v1.re+u1.re)*him
      by_contra hc
      push Not at hc
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hc
        (by positivity : 0 ≤ (v1.im+u1.im)^2+(v1.re+u1.re)^2)]
    have : ((v1-u1)/(Real.sqrt 2*I)) = (-I*(v1-u1))/Real.sqrt 2 := by
      field_simp; rw [I_sq]; ring
    rw [this, div_ofReal_re]
    refine div_pos ?_ (Real.sqrt_pos.mpr two_pos)
    simpa using hdim
  rw [huv, hw]
  simp only [k]
  field_simp

end DLMF.Confluent
