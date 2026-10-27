/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.ExpIntegralAsymptotics

/-!
# Generalized sine and cosine integrals, DLMF §8.21

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

/-- Generalized lower sine integral on the logarithmic plane away from its parameter poles. -/
def genSinIntOnLog (a w : ℂ) : ℂ :=
  exp (a*w)*∑' k : ℕ, (-1 : ℂ)^k*exp ((2*k+1 : ℂ)*w)/((2*k+a+1)*(2*k+1).factorial)

/-- Generalized lower cosine integral on the logarithmic plane away from its parameter poles. -/
def genCosIntOnLog (a w : ℂ) : ℂ :=
  exp (a*w)*∑' k : ℕ, (-1 : ℂ)^k*exp ((2*k : ℂ)*w)/((2*k+a)*(2*k).factorial)

/-- Generalized upper sine integral, entire in a. -/
def genSinIntTailOnLog (a w : ℂ) : ℂ :=
  (exp (π*I*a/2)*upperIncGammaOnLog a (w-π*I/2)-exp (-π*I*a/2)*upperIncGammaOnLog a (w+π*I/2))/(2*I)

/-- Generalized upper cosine integral, entire in a. -/
def genCosIntTailOnLog (a w : ℂ) : ℂ :=
  (exp (π*I*a/2)*upperIncGammaOnLog a (w-π*I/2)+exp (-π*I*a/2)*upperIncGammaOnLog a (w+π*I/2))/2

/-- Principal branch for nonzero z by continued logarithmic coordinates. -/
def genSinInt (a z : ℂ) : ℂ :=
  genSinIntOnLog a (log z)

/-- Principal branch for nonzero z by continued logarithmic coordinates. -/
def genCosInt (a z : ℂ) : ℂ :=
  genCosIntOnLog a (log z)

/-- Principal branch for nonzero z by continued logarithmic coordinates. -/
def genSinIntTail (a z : ℂ) : ℂ :=
  genSinIntTailOnLog a (log z)

/-- Principal branch for nonzero z by continued logarithmic coordinates. -/
def genCosIntTail (a z : ℂ) : ℂ :=
  genCosIntTailOnLog a (log z)

/-- genUpperTrig gamma. -/
@[dlmf 8.21.E1]
theorem genUpperTrig_gamma (a w : ℂ) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    genCosIntTailOnLog a w+ε*I*genSinIntTailOnLog a w=exp (ε*π*I*a/2)*upperIncGammaOnLog a (w-ε*π*I/2) := by
  rcases hε with rfl | rfl <;>
    simp only [genCosIntTailOnLog,genSinIntTailOnLog,Complex.ofReal_one,Complex.ofReal_neg,
      neg_mul,one_mul,sub_neg_eq_add,neg_neg]
  all_goals field_simp; ring_nf

/-- genSinIntTail parameter entire. -/
theorem genSinIntTail_parameter_entire (w : ℂ) :
    Differentiable ℂ (fun a => genSinIntTailOnLog a w) := by
  have h1 := upperIncGammaOnLog_parameter_entire (w-π*I/2)
  have h2 := upperIncGammaOnLog_parameter_entire (w+π*I/2)
  exact (((by fun_prop : Differentiable ℂ fun a : ℂ => exp (π*I*a/2)).mul h1).sub
    ((by fun_prop : Differentiable ℂ fun a : ℂ => exp (-π*I*a/2)).mul h2)).div_const (2*I)

/-- genCosIntTail parameter entire. -/
theorem genCosIntTail_parameter_entire (w : ℂ) :
    Differentiable ℂ (fun a => genCosIntTailOnLog a w) := by
  have h1 := upperIncGammaOnLog_parameter_entire (w-π*I/2)
  have h2 := upperIncGammaOnLog_parameter_entire (w+π*I/2)
  exact (((by fun_prop : Differentiable ℂ fun a : ℂ => exp (π*I*a/2)).mul h1).add
    ((by fun_prop : Differentiable ℂ fun a : ℂ => exp (-π*I*a/2)).mul h2)).div_const 2

/-- Factorial decay controls the generalized trigonometric coefficients for every parameter;
totalized exceptional terms affect only finitely many coefficients. -/
theorem summable_genTrig_coeff (a z : ℂ) (ε : ℕ) :
    Summable (fun n : ℕ => (-1:ℂ)^n*z^(2*n+ε)/((2*n+ε).factorial*((2*n+ε:ℕ)+a))) := by
  have hd : Function.Injective (fun n : ℕ => 2*n+ε) := by intro n m h; dsimp only at h; omega
  apply Summable.of_norm_bounded_eventually_nat
    ((Real.summable_pow_div_factorial ‖z‖).comp_injective hd)
  obtain ⟨N,hN⟩ := exists_nat_gt (1+|a.re|)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnr : (N:ℝ)≤n := by exact_mod_cast hn
  have he0 : (0:ℝ)≤ε := by positivity
  have hb : 1≤‖((2*n+ε:ℕ):ℂ)+a‖ := by
    calc
      1 ≤ (((2*n+ε:ℕ):ℂ)+a).re := by
        rw [add_re,Complex.natCast_re]
        push_cast
        linarith [le_abs_self (-a.re),abs_neg a.re]
      _ ≤ ‖((2*n+ε:ℕ):ℂ)+a‖ := Complex.re_le_norm _
  rw [norm_div,norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,norm_pow,Complex.norm_natCast]
  calc
    ‖z‖^(2*n+ε)/((2*n+ε).factorial*‖((2*n+ε:ℕ):ℂ)+a‖)
      ≤ ‖z‖^(2*n+ε)/((2*n+ε).factorial*1) := by gcongr
    _ = _ := by simp only [Function.comp_apply,mul_one]

/-- Terms of the generalized trigonometric series, with a finite set of indices removed. -/
noncomputable def incG_trigTerm (z : ℂ) (ε : ℕ) (s : Finset ℕ) (k : ℕ) (a : ℂ) : ℂ :=
  if k ∈ s then 0 else (-1:ℂ)^k*z^(2*k+ε)/(((2*k+ε).factorial : ℂ)*(((2*k+ε:ℕ):ℂ)+a))

/-- Summability of the modified trigonometric series for every parameter. -/
theorem incG_trigTerm_summable (z : ℂ) (ε : ℕ) (s : Finset ℕ) (a : ℂ) :
    Summable (fun k => incG_trigTerm z ε s k a) := by
  have h := (summable_genTrig_coeff a z ε).indicator ((↑s : Set ℕ)ᶜ)
  refine h.congr fun k => ?_
  simp only [incG_trigTerm, Set.indicator, Set.mem_compl_iff, Finset.mem_coe]
  split_ifs <;> rfl

/-- The modified trigonometric series is analytic in the parameter at every point which is
not a pole of a retained term. -/
theorem incG_trigTerm_analyticAt (z : ℂ) (ε : ℕ) (s : Finset ℕ) {a₀ : ℂ}
    (ha : ∀ k ∉ s, ((2*k+ε:ℕ):ℂ)+a₀ ≠ 0) :
    AnalyticAt ℂ (fun a => ∑' k, incG_trigTerm z ε s k a) a₀ := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  obtain ⟨K, hK⟩ := exists_nat_gt (‖a₀‖+1)
  have hsplit : (fun a => ∑' k, incG_trigTerm z ε s k a) = fun a =>
      (∑ k ∈ Finset.range K, incG_trigTerm z ε s k a) + ∑' j, incG_trigTerm z ε s (j+K) a := by
    funext a; exact ((incG_trigTerm_summable z ε s a).sum_add_tsum_nat_add K).symm
  rw [hsplit]
  -- each term is differentiable where its denominator does not vanish
  have hterm : ∀ k, ∀ a, (k ∉ s → ((2*k+ε:ℕ):ℂ)+a ≠ 0) →
      DifferentiableAt ℂ (fun a => incG_trigTerm z ε s k a) a := by
    intro k a h
    unfold incG_trigTerm
    by_cases hk : k ∈ s
    · simp only [hk, ite_true]; exact differentiableAt_const _
    · simp only [hk, ite_false]
      refine (differentiableAt_const _).div ((differentiableAt_const _).mul
        ((differentiableAt_const _).add differentiableAt_id)) ?_
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) (h hk)
  have hfin : ∀ᶠ a in 𝓝 a₀, ∀ k ∈ Finset.range K,
      DifferentiableAt ℂ (fun a => incG_trigTerm z ε s k a) a := by
    rw [Filter.eventually_all_finset]
    intro k _
    by_cases hk : k ∈ s
    · exact Eventually.of_forall fun a => hterm k a (fun h => absurd hk h)
    · have hc : ContinuousAt (fun a : ℂ => ((2*k+ε:ℕ):ℂ)+a) a₀ := by fun_prop
      filter_upwards [hc.eventually_ne (ha k hk)] with a ha'
      exact hterm k a fun _ => ha'
  -- the tail is a locally uniform limit on the ball of radius 1/2
  have htail : DifferentiableOn ℂ (fun a => ∑' j, incG_trigTerm z ε s (j+K) a)
      (Metric.ball a₀ (1/2)) := by
    have hinj : Function.Injective (fun j : ℕ => 2*(j+K)+ε) := by
      intro i j h; dsimp only at h; omega
    have hlow : ∀ j : ℕ, ∀ a ∈ Metric.ball a₀ (1/2), 1 ≤ ‖((2*(j+K)+ε:ℕ):ℂ)+a‖ := by
      intro j a ha'
      have h1 : ‖a‖ ≤ ‖a₀‖ + 1/2 := by
        have := norm_le_norm_add_norm_sub' a a₀
        rw [Metric.mem_ball, dist_eq_norm] at ha'; linarith
      have h2 : (((2*(j+K)+ε:ℕ):ℂ)+a).re ≤ ‖((2*(j+K)+ε:ℕ):ℂ)+a‖ := Complex.re_le_norm _
      have h3 : -‖a‖ ≤ a.re := by have := Complex.abs_re_le_norm a; rw [abs_le] at this; linarith
      rw [add_re, Complex.natCast_re] at h2
      have : (2*K:ℝ) ≤ ((2*(j+K)+ε : ℕ):ℝ) := by push_cast; linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j),
        (Nat.cast_nonneg ε : (0:ℝ) ≤ ε), (Nat.cast_nonneg K : (0:ℝ) ≤ K)]
      linarith [norm_nonneg a₀]
    refine Complex.differentiableOn_tsum_of_summable_norm
      ((Real.summable_pow_div_factorial ‖z‖).comp_injective hinj)
      (fun j a ha' => (hterm (j+K) a fun _ h0 => by
        have := hlow j a ha'; rw [h0, norm_zero] at this; linarith).differentiableWithinAt)
      Metric.isOpen_ball fun j a ha' => ?_
    unfold incG_trigTerm
    split_ifs
    · simp only [norm_zero, Function.comp_apply]; positivity
    · simp only [Function.comp_apply, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
        one_mul, Complex.norm_natCast]
      have hl := hlow j a ha'
      have hf : (0:ℝ) < ((2*(j+K)+ε).factorial : ℝ) := by positivity
      rw [div_le_div_iff₀ (by positivity) hf]
      calc ‖z‖^(2*(j+K)+ε) * ((2*(j+K)+ε).factorial : ℝ)
          = ‖z‖^(2*(j+K)+ε) * ((2*(j+K)+ε).factorial : ℝ) * 1 := by ring
        _ ≤ ‖z‖^(2*(j+K)+ε) * (((2*(j+K)+ε).factorial : ℝ) * ‖((2*(j+K)+ε:ℕ):ℂ)+a‖) := by
          rw [← mul_assoc]; gcongr
  have htail' : ∀ᶠ a in 𝓝 a₀, DifferentiableAt ℂ (fun a => ∑' j, incG_trigTerm z ε s (j+K) a) a := by
    filter_upwards [Metric.ball_mem_nhds a₀ (by norm_num : (0:ℝ) < 1/2)] with a ha'
    exact htail.differentiableAt (Metric.isOpen_ball.mem_nhds ha')
  filter_upwards [hfin, htail'] with a h1 h2
  exact (DifferentiableAt.fun_sum fun k hk => h1 k hk).add h2

/-- The lower sine series in terms of `incG_trigTerm`. -/
theorem incG_genSinIntOnLog_eq (b w : ℂ) :
    genSinIntOnLog b w = exp (b*w)*∑' k, incG_trigTerm (exp w) 1 ∅ k b := by
  unfold genSinIntOnLog incG_trigTerm
  congr 1; refine tsum_congr fun k => ?_
  simp only [Finset.notMem_empty, ite_false]
  rw [show (2*k+1:ℂ)*w = ((2*k+1:ℕ):ℂ)*w by push_cast; ring, exp_nat_mul]
  push_cast; ring

/-- The lower cosine series in terms of `incG_trigTerm`. -/
theorem incG_genCosIntOnLog_eq (b w : ℂ) :
    genCosIntOnLog b w = exp (b*w)*∑' k, incG_trigTerm (exp w) 0 ∅ k b := by
  unfold genCosIntOnLog incG_trigTerm
  congr 1; refine tsum_congr fun k => ?_
  simp only [Finset.notMem_empty, ite_false]
  rw [show (2*k:ℂ)*w = ((2*k:ℕ):ℂ)*w by push_cast; ring, exp_nat_mul]
  push_cast; ring_nf

/-- Residue of the modified series at the pole `a = -(2n+ε)`. -/
theorem incG_trig_residue (w : ℂ) (ε n : ℕ) :
    Tendsto (fun a : ℂ => (a+((2*n+ε:ℕ):ℂ))*(exp (a*w)*∑' k, incG_trigTerm (exp w) ε ∅ k a))
      (𝓝[≠] (-((2*n+ε:ℕ):ℂ))) (𝓝 ((-1 : ℂ)^n/(2*n+ε).factorial)) := by
  set d : ℂ := ((2*n+ε:ℕ):ℂ)
  have hR := (incG_trigTerm_analyticAt (exp w) ε {n} (a₀ := -d) (fun k hk => by
    have hk' : k ≠ n := by simpa using hk
    simp only [d]; intro h
    have : ((2*k+ε:ℕ):ℂ) = ((2*n+ε:ℕ):ℂ) := by linear_combination h
    have := Nat.cast_injective this; omega)).continuousAt
  have hsplit : ∀ a, ∑' k, incG_trigTerm (exp w) ε ∅ k a =
      (∑' k, incG_trigTerm (exp w) ε {n} k a) +
        (-1:ℂ)^n*(exp w)^(2*n+ε)/(((2*n+ε).factorial : ℂ)*(d+a)) := by
    intro a
    rw [← (hasSum_ite_eq n ((-1:ℂ)^n*(exp w)^(2*n+ε)/(((2*n+ε).factorial : ℂ)*(d+a)))).tsum_eq,
      ← Summable.tsum_add (incG_trigTerm_summable _ _ _ _) (hasSum_ite_eq _ _).summable]
    refine tsum_congr fun k => ?_
    unfold incG_trigTerm
    by_cases hk : k = n
    · subst hk; simp [d]
    · simp [hk]
  have hlim : Tendsto (fun a : ℂ => exp (a*w)*((a+d)*(∑' k, incG_trigTerm (exp w) ε {n} k a) +
      (-1:ℂ)^n*(exp w)^(2*n+ε)/((2*n+ε).factorial : ℂ))) (𝓝 (-d))
      (𝓝 (exp (-d*w)*((-d+d)*(∑' k, incG_trigTerm (exp w) ε {n} k (-d)) +
        (-1:ℂ)^n*(exp w)^(2*n+ε)/((2*n+ε).factorial : ℂ)))) := by
    refine ((continuous_exp.comp (continuous_id.mul continuous_const)).continuousAt.tendsto).mul
      ((((continuous_id.add continuous_const).continuousAt.tendsto).mul hR.tendsto).add tendsto_const_nhds)
  have hval : exp (-d*w)*((-d+d)*(∑' k, incG_trigTerm (exp w) ε {n} k (-d)) +
      (-1:ℂ)^n*(exp w)^(2*n+ε)/((2*n+ε).factorial : ℂ)) = (-1 : ℂ)^n/(2*n+ε).factorial := by
    have : exp (-d*w)*(exp w)^(2*n+ε) = 1 := by
      rw [← exp_nat_mul, ← Complex.exp_add, show -d*w + ((2*n+ε:ℕ):ℂ)*w = 0 by simp only [d]; ring,
        Complex.exp_zero]
    rw [neg_add_cancel, zero_mul, zero_add]
    linear_combination ((-1:ℂ)^n/((2*n+ε).factorial : ℂ))*this
  rw [hval] at hlim
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a ha
  have had : d+a ≠ 0 := by
    intro h; apply ha; simp only [Set.mem_singleton_iff]; linear_combination h
  rw [hsplit a]
  field_simp
  ring

/-- genSinInt parameter analytic. -/
theorem genSinInt_parameter_analytic {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n+1)) (w : ℂ) :
    AnalyticAt ℂ (fun b => genSinIntOnLog b w) a := by
  simp_rw [incG_genSinIntOnLog_eq]
  refine (analyticAt_cexp.comp ((analyticAt_id).mul analyticAt_const)).mul
    (incG_trigTerm_analyticAt (exp w) 1 ∅ fun k _ h => ha k ?_)
  push_cast at h; linear_combination h

/-- genCosInt parameter analytic. -/
theorem genCosInt_parameter_analytic {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n : ℂ)) (w : ℂ) :
    AnalyticAt ℂ (fun b => genCosIntOnLog b w) a := by
  simp_rw [incG_genCosIntOnLog_eq]
  refine (analyticAt_cexp.comp ((analyticAt_id).mul analyticAt_const)).mul
    (incG_trigTerm_analyticAt (exp w) 0 ∅ fun k _ h => ha k ?_)
  push_cast at h; linear_combination h

/-- genSinInt parameter residue. -/
theorem genSinInt_parameter_residue (n : ℕ) (w : ℂ) :
    Tendsto (fun a : ℂ => (a+(2*n+1))*genSinIntOnLog a w) (𝓝[≠] (-(2*n+1 : ℂ))) (𝓝 ((-1 : ℂ)^n/(2*n+1).factorial)) := by
  have h := incG_trig_residue w 1 n
  push_cast at h
  simp_rw [incG_genSinIntOnLog_eq]
  exact h

/-- genCosInt parameter residue. -/
theorem genCosInt_parameter_residue (n : ℕ) (w : ℂ) :
    Tendsto (fun a : ℂ => (a+2*n)*genCosIntOnLog a w) (𝓝[≠] (-(2*n : ℂ))) (𝓝 ((-1 : ℂ)^n/(2*n).factorial)) := by
  have h := incG_trig_residue w 0 n
  push_cast at h
  simp_rw [incG_genCosIntOnLog_eq]
  simpa using h

/-- `Γ(a, ε i (z+t)) → 0` along horizontal rays when `re a < 1`. -/
theorem tendsto_upperIncGamma_mul_I_add_ofReal {a : ℂ} (ha : a.re < 1) (z : ℂ) {ε : ℝ}
    (hε : ε=1 ∨ ε = -1) :
    Tendsto (fun t : ℝ => upperIncGamma a (ε*I*(z+t))) atTop (𝓝 0) := by
  have hβ : |-ε*(π/4)| < π/2 := by
    rcases hε with rfl | rfl <;> simp [abs_of_pos (by positivity : (0:ℝ) < π/4)] <;> linarith [Real.pi_pos]
  have hr := tendsto_mul_I_add_ofReal_rotSectorAtTop z hε
  have hU := (tendsto_kummerU_rotSectorAtTop (a := 1-a) (1-a) (by simp; linarith) (by norm_num) hβ).comp hr
  have hU' := hU.norm.mul_const (Real.exp (ε*z.im))
  rw [norm_zero, zero_mul] at hU'
  refine squeeze_zero_norm' (Eventually.of_forall fun t => ?_) hU'
  rw [upperIncGamma, norm_mul, Complex.norm_exp, Function.comp_apply, mul_comm]
  apply le_of_eq
  congr 2
  rcases hε with rfl | rfl <;> simp

/-- A quarter turn down on the logarithmic plane. -/
theorem exp_sub_pi_I_half (w : ℂ) : exp (w-π*I/2) = -I*exp w := by
  rw [Complex.exp_sub, show (π:ℂ)*I/2 = (π/2:ℂ)*I by ring, Complex.exp_mul_I]
  simp [Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  field_simp

/-- A quarter turn up on the logarithmic plane. -/
theorem exp_add_pi_I_half (w : ℂ) : exp (w+π*I/2) = I*exp w := by
  rw [Complex.exp_add, show (π:ℂ)*I/2 = (π/2:ℂ)*I by ring, Complex.exp_mul_I]
  simp [Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  ring

/-- Derivatives of the generalized sine and cosine tails on the logarithmic plane. -/
theorem hasDerivAt_genTrigTailOnLog (a w : ℂ) :
    HasDerivAt (genSinIntTailOnLog a) (-exp (a*w)*sin (exp w)) w ∧
    HasDerivAt (genCosIntTailOnLog a) (-exp (a*w)*cos (exp w)) w := by
  have h1 := ((hasDerivAt_upperIncGammaOnLog a (w-π*I/2)).comp w ((hasDerivAt_id w).sub_const _)).const_mul
    (exp (π*I*a/2))
  have h2 := ((hasDerivAt_upperIncGammaOnLog a (w+π*I/2)).comp w ((hasDerivAt_id w).add_const _)).const_mul
    (exp (-π*I*a/2))
  have e1 : exp (π*I*a/2)*exp (a*(w-π*I/2)-exp (w-π*I/2)) = exp (a*w)*exp (I*exp w) := by
    rw [exp_sub_pi_I_half, ← Complex.exp_add, ← Complex.exp_add]; ring_nf
  have e2 : exp (-π*I*a/2)*exp (a*(w+π*I/2)-exp (w+π*I/2)) = exp (a*w)*exp (-(I*exp w)) := by
    rw [exp_add_pi_I_half, ← Complex.exp_add, ← Complex.exp_add]; ring_nf
  have hs : sin (exp w) = (exp (-(exp w)*I)-exp (exp w*I))*I/2 := rfl
  have hc : cos (exp w) = (exp (exp w*I)+exp (-(exp w)*I))/2 := rfl
  constructor
  · refine ((h1.sub h2).div_const (2*I)).congr_deriv ?_
    simp only [id, Function.comp_apply, mul_one]
    rw [hs, mul_neg, mul_neg, e1, e2]
    field_simp
    ring_nf; rw [I_sq]; ring
  · refine ((h1.add h2).div_const 2).congr_deriv ?_
    simp only [id, Function.comp_apply, mul_one]
    rw [hc, mul_neg, mul_neg, e1, e2]
    ring_nf

/-- Derivatives of the principal generalized sine and cosine tails on the slit plane. -/
theorem hasDerivAt_genTrigTail (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (genSinIntTail a) (-z^(a-1)*sin z) z ∧
    HasDerivAt (genCosIntTail a) (-z^(a-1)*cos z) z := by
  have hz0 := slitPlane_ne_zero hz
  have hl := Complex.hasDerivAt_log hz
  have hp : exp (a*log z)*z⁻¹ = z^(a-1) := by
    rw [cpow_sub _ _ hz0, cpow_one, cpow_def_of_ne_zero hz0, mul_comm a, div_eq_mul_inv]
  obtain ⟨hS, hC⟩ := hasDerivAt_genTrigTailOnLog a (log z)
  constructor
  · refine (hS.comp z hl).congr_deriv ?_
    rw [Complex.exp_log hz0, ← hp]; ring
  · refine (hC.comp z hl).congr_deriv ?_
    rw [Complex.exp_log hz0, ← hp]; ring

/-- Away from the cut the generalized tails are combinations of principal upper Gamma values. -/
theorem genTrigTail_eq_upperIncGamma (a : ℂ) {z : ℂ} (hz : 0 < z.re) :
    genSinIntTail a z = (exp (π*I*a/2)*upperIncGamma a (-I*z)-exp (-π*I*a/2)*upperIncGamma a (I*z))/(2*I) ∧
    genCosIntTail a z = (exp (π*I*a/2)*upperIncGamma a (-I*z)+exp (-π*I*a/2)*upperIncGamma a (I*z))/2 := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have ha := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz))
  have hm : upperIncGammaOnLog a (log z-π*I/2) = upperIncGamma a (-I*z) := by
    rw [upperIncGammaOnLog_eq_upperIncGamma, exp_sub_pi_I_half, Complex.exp_log hz0]
    · simp [Complex.log_im]; linarith [Real.pi_pos]
    · simp [Complex.log_im]; linarith [Real.pi_pos]
  have hp : upperIncGammaOnLog a (log z+π*I/2) = upperIncGamma a (I*z) := by
    rw [upperIncGammaOnLog_eq_upperIncGamma, exp_add_pi_I_half, Complex.exp_log hz0]
    · simp [Complex.log_im]; linarith [Real.pi_pos]
    · simp [Complex.log_im]; linarith [Real.pi_pos]
  simp only [genSinIntTail, genCosIntTail, genSinIntTailOnLog, genCosIntTailOnLog, hm, hp]
  exact ⟨trivial, trivial⟩

/-- Both generalized tails tend to zero along horizontal rays when `re a < 1`. -/
theorem tendsto_genTrigTail_add_ofReal {a : ℂ} (ha : a.re < 1) (z : ℂ) :
    Tendsto (fun t : ℝ => genSinIntTail a (z+t)) atTop (𝓝 0) ∧
    Tendsto (fun t : ℝ => genCosIntTail a (z+t)) atTop (𝓝 0) := by
  have hm := (tendsto_upperIncGamma_mul_I_add_ofReal ha z (ε := -1) (Or.inr rfl)).const_mul (exp (π*I*a/2))
  have hp := (tendsto_upperIncGamma_mul_I_add_ofReal ha z (ε := 1) (Or.inl rfl)).const_mul (exp (-π*I*a/2))
  rw [mul_zero] at hm hp
  constructor
  · have h := (hm.sub hp).div_const (2*I)
    rw [sub_zero, zero_div] at h
    refine h.congr' ?_
    filter_upwards [eventually_re_add_ofReal_pos z] with t ht
    rw [(genTrigTail_eq_upperIncGamma a ht).1]; push_cast; ring_nf
  · have h := (hm.add hp).div_const 2
    rw [add_zero, zero_div] at h
    refine h.congr' ?_
    filter_upwards [eventually_re_add_ofReal_pos z] with t ht
    rw [(genTrigTail_eq_upperIncGamma a ht).2]; push_cast; ring_nf

/-- `∫₀^R t^{a-1} e^{iεt} dt = (-iε)^{-a} (Γ(a) - Γ(a, -iεR))` for `R > 0`. -/
theorem incG_integral_rpow_mul_exp_I {a : ℂ} (ha0 : 0 < a.re) {ε : ℝ} (hε : ε=1 ∨ ε = -1)
    {R : ℝ} (hR : 0 < R) :
    (∫ t in (0:ℝ)..R, (t : ℂ)^(a-1)*exp (ε*I*t)) =
      (-(ε*I))^(-a) * (Gamma a - upperIncGamma a (-(ε*I)*R)) := by
  have ha' : ∀ k : ℕ, a ≠ -k := fun k hk => by
    have := congrArg Complex.re hk
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hG0 := Gamma_ne_zero ha'
  have hc0 : (-(ε*I) : ℂ) ≠ 0 := by
    rcases hε with rfl | rfl <;> simp
  have hw0 : (-(ε*I)*R : ℂ) ≠ 0 := mul_ne_zero hc0 (ofReal_ne_zero.mpr hR.ne')
  -- change of variables t = R s
  have hsub : (∫ t in (0:ℝ)..R, (t : ℂ)^(a-1)*exp (ε*I*t)) =
      R * ∫ s in (0:ℝ)..1, ((R*s : ℝ) : ℂ)^(a-1)*exp (ε*I*((R*s : ℝ) : ℂ)) := by
    have := intervalIntegral.integral_comp_mul_left
      (fun t : ℝ => (t : ℂ)^(a-1)*exp (ε*I*t)) (c := R) hR.ne' (a := 0) (b := 1)
    simp only [mul_zero, mul_one] at this
    rw [this, Complex.real_smul, ← mul_assoc, ofReal_inv, mul_inv_cancel₀ (ofReal_ne_zero.mpr hR.ne'),
      one_mul]
  have hpt : ∀ s ∈ Set.uIcc (0:ℝ) 1, ((R*s : ℝ) : ℂ)^(a-1)*exp (ε*I*((R*s : ℝ) : ℂ)) =
      (R:ℂ)^(a-1) * ((s:ℂ)^(a-1)*exp (-(-(ε*I)*R)*s)) := by
    intro s hs
    rw [Set.uIcc_of_le zero_le_one] at hs
    rw [ofReal_mul, mul_cpow_ofReal_nonneg hR.le hs.1]
    ring_nf
  rw [hsub, intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul]
  have hsc := scIncGamma_integral ha0 (-(ε*I)*R)
  have hQ := normIncGammaQContinued_eq ha' hw0
  rw [normIncGammaQContinued, normIncGammaPContinued, DLMF.Statistical.normIncGammaQ, hsc] at hQ
  have hpow : (-(ε*I)*(R:ℂ))^a = (-(ε*I))^a * (R:ℂ)^a := by
    rw [mul_comm, ofReal_mul_cpow_of_pos hR hc0, mul_comm]
  rw [hpow] at hQ
  have hRa : (R:ℂ) * (R:ℂ)^(a-1) = (R:ℂ)^a := by
    rw [cpow_sub _ _ (ofReal_ne_zero.mpr hR.ne'), cpow_one, ← mul_div_assoc,
      mul_div_cancel_left₀ _ (ofReal_ne_zero.mpr hR.ne')]
  have hca : (-(ε*I))^(-a) * (-(ε*I))^a = 1 := by
    have : (-(ε*I) : ℂ)^a ≠ 0 := by rw [cpow_def_of_ne_zero hc0]; exact Complex.exp_ne_zero _
    rw [cpow_neg, inv_mul_cancel₀ this]
  set J := ∫ (x : ℝ) in (0:ℝ)..1, (x:ℂ) ^ (a - 1) * exp (-(-(ε * I) * R) * x)
  have hU : upperIncGamma a (-(ε*I)*R) = Gamma a - (-(ε*I))^a * (R:ℂ)^a * J := by
    rw [eq_div_iff hG0] at hQ
    have e : (1 - (-(ε*I))^a * (R:ℂ)^a * (1 / Gamma a * J)) * Gamma a =
        Gamma a - (-(ε*I))^a * (R:ℂ)^a * J := by field_simp
    linear_combination -hQ + e
  rw [hU]
  linear_combination J * hRa - (R:ℂ)^a * J * hca

theorem incG_gamma_rotated_oscillatory_integral {a : ℂ} (ha0 : 0 < a.re) (ha1 : a.re < 1) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    HasIntegralAtTop (fun t : ℝ => (t : ℂ)^(a-1)*exp (ε*I*t)) 0 (exp (ε*π*I*a/2)*Gamma a) := by
  have hε' : -ε = 1 ∨ -ε = -1 := by rcases hε with rfl | rfl <;> simp
  have hT := tendsto_upperIncGamma_mul_I_add_ofReal ha1 0 hε'
  have hc : (-(ε*I) : ℂ)^(-a) = exp (ε*π*I*a/2) := by
    have hc0 : (-(ε*I) : ℂ) ≠ 0 := by rcases hε with rfl | rfl <;> simp
    rw [cpow_def_of_ne_zero hc0]
    rcases hε with rfl | rfl
    · simp only [ofReal_one, one_mul, log_neg_I]; congr 1; ring
    · simp only [ofReal_neg, ofReal_one, neg_mul, one_mul, neg_neg, log_I]; congr 1; ring
  have hL := ((tendsto_const_nhds (x := Gamma a)).sub hT).const_mul ((-(ε*I) : ℂ)^(-a))
  rw [sub_zero, hc] at hL
  unfold HasIntegralAtTop
  refine hL.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  rw [incG_integral_rpow_mul_exp_I ha0 hε hR, hc]
  congr 3
  push_cast; ring

/-- gamma rotated oscillatory integral. -/
@[dlmf 8.21.E3]
theorem gamma_rotated_oscillatory_integral {a : ℂ} (ha0 : 0 < a.re) (ha1 : a.re < 1) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    HasIntegralAtTop (fun t : ℝ => (t : ℂ)^(a-1)*exp (ε*I*t)) 0 (exp (ε*π*I*a/2)*Gamma a) :=
  incG_gamma_rotated_oscillatory_integral ha0 ha1 hε

/-- genSinIntTail horizontal integral. -/
@[dlmf 8.21.E4]
theorem genSinIntTail_horizontal_integral {a : ℂ} (ha : a.re < 1) {z : ℂ} (hz : z ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => (z+t)^(a-1)*sin (z+t)) 0 (genSinIntTail a z) := by
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun t : ℝ => -genSinIntTail a (z+t)) ((z+t)^(a-1)*sin (z+t)) t := by
    intro t ht
    refine (hasDerivAt_comp_add_ofReal (g := fun w => -genSinIntTail a w)
      (hasDerivAt_genTrigTail a (add_ofReal_mem_slitPlane hz ht)).1.neg).congr_deriv ?_
    ring
  have hc : ContinuousOn (fun t : ℝ => (z+t)^(a-1)*sin (z+t)) (Ici 0) := by
    refine ContinuousOn.mul (fun t ht => ?_) (by fun_prop)
    exact ((continuousAt_const.add continuous_ofReal.continuousAt).cpow continuousAt_const
      (add_ofReal_mem_slitPlane hz ht)).continuousWithinAt
  have h := hasIntegralAtTop_of_hasDerivAt_of_tendsto hd hc (tendsto_genTrigTail_add_ofReal ha z).1.neg
  simpa using h

/-- genCosIntTail horizontal integral. -/
@[dlmf 8.21.E5]
theorem genCosIntTail_horizontal_integral {a : ℂ} (ha : a.re < 1) {z : ℂ} (hz : z ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => (z+t)^(a-1)*cos (z+t)) 0 (genCosIntTail a z) := by
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun t : ℝ => -genCosIntTail a (z+t)) ((z+t)^(a-1)*cos (z+t)) t := by
    intro t ht
    refine (hasDerivAt_comp_add_ofReal (g := fun w => -genCosIntTail a w)
      (hasDerivAt_genTrigTail a (add_ofReal_mem_slitPlane hz ht)).2.neg).congr_deriv ?_
    ring
  have hc : ContinuousOn (fun t : ℝ => (z+t)^(a-1)*cos (z+t)) (Ici 0) := by
    refine ContinuousOn.mul (fun t ht => ?_) (by fun_prop)
    exact ((continuousAt_const.add continuous_ofReal.continuousAt).cpow continuousAt_const
      (add_ofReal_mem_slitPlane hz ht)).continuousWithinAt
  have h := hasIntegralAtTop_of_hasDerivAt_of_tendsto hd hc (tendsto_genTrigTail_add_ofReal ha z).2.neg
  simpa using h

/-- Γ(a)sin(πa/2), with removable even-integer singularities filled by limits. -/
def gammaSinHalfPiContinued (a : ℂ) : ℂ :=
  limUnder (𝓝[≠] a) (fun b : ℂ => Gamma b*sin (π*b/2))

/-- Γ(a)cos(πa/2), with removable odd-integer singularities filled by limits. -/
def gammaCosHalfPiContinued (a : ℂ) : ℂ :=
  limUnder (𝓝[≠] a) (fun b : ℂ => Gamma b*cos (π*b/2))

/-- Punctured neighbourhoods avoid the nonpositive integers. -/
theorem incG_eventually_nhdsNE_regular (a : ℂ) : ∀ᶠ b : ℂ in 𝓝[≠] a, ∀ m : ℕ, b ≠ -m := by
  by_cases h : ∃ n : ℕ, a = -n
  · obtain ⟨n, rfl⟩ := h; exact eventually_nhdsNE_neg_nat_ne n
  · push Not at h
    filter_upwards [nhdsWithin_le_nhds ((differentiable_one_div_Gamma a).continuousAt.eventually_ne
      (inv_ne_zero (Gamma_ne_zero h)))] with b hb m hm
    apply hb; rw [hm, Gamma_neg_nat_eq_zero, inv_zero]

theorem incG_exp_log_sub_half_pi {z : ℂ} (hz : z ≠ 0) : exp (log z - π*I/2) = -I*z := by
  have hI : exp (π*I/2) = I := by
    rw [show (π:ℂ)*I/2 = ((π/2:ℝ):ℂ)*I by push_cast; ring, Complex.exp_mul_I]; simp
  rw [Complex.exp_sub, Complex.exp_log hz, hI]; field_simp; rw [I_sq]; ring

theorem incG_exp_log_add_half_pi {z : ℂ} (hz : z ≠ 0) : exp (log z + π*I/2) = I*z := by
  have hI : exp (π*I/2) = I := by
    rw [show (π:ℂ)*I/2 = ((π/2:ℝ):ℂ)*I by push_cast; ring, Complex.exp_mul_I]; simp
  rw [Complex.exp_add, Complex.exp_log hz, hI]; ring

/-- `si(a,z) + Si(a,z) = Γ(a) sin(πa/2)` at regular parameters. -/
theorem incG_genSin_add_tail {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) {z : ℂ} (hz : z ≠ 0) :
    genSinInt a z + genSinIntTail a z = Gamma a * sin (π*a/2) := by
  have hG := Gamma_ne_zero ha
  have hs₁ := scIncGamma_hasSum_alternating ha (-I*z)
  have hs₂ := scIncGamma_hasSum_alternating ha (I*z)
  have hD := (hs₁.sub hs₂).mul_left (Gamma a/(2*I))
  have hodd : HasSum (fun m : ℕ => incG_trigTerm z 1 ∅ m a)
      (Gamma a/(2*I)*(DLMF.Statistical.scIncGamma a (-I*z) - DLMF.Statistical.scIncGamma a (I*z))) := by
    have hinj : Function.Injective (fun m : ℕ => 2*m+1) := fun m n h => by simp at h; omega
    rw [← hinj.hasSum_iff] at hD
    · refine hD.congr_fun fun m => ?_
      simp only [Function.comp_apply, incG_trigTerm, Finset.notMem_empty, ite_false]
      have hk : a + ((2*m+1:ℕ):ℂ) ≠ 0 := by
        intro h; exact ha (2*m+1) (by linear_combination h)
      have hI2 : I^(2*m+1) = I*(-1)^m := by rw [pow_succ, pow_mul, I_sq]; ring
      have hnI2 : (-I)^(2*m+1) = -(I*(-1)^m) := by rw [pow_succ, pow_mul, neg_sq, I_sq]; ring
      rw [show (-(-I*z)) = I*z by ring, show (-(I*z)) = (-I)*z by ring, mul_pow, mul_pow, hI2, hnI2]
      have hf : ((2*m+1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have hk' : ((2*m+1:ℕ):ℂ) + a ≠ 0 := by rw [add_comm]; exact hk
      field_simp
      ring
    · intro k hk
      obtain ⟨m, rfl⟩ : ∃ m, k = 2*m := by
        rcases Nat.even_or_odd k with ⟨r, hr⟩ | ⟨r, hr⟩
        · exact ⟨r, by omega⟩
        · exact absurd ⟨r, hr.symm⟩ hk
      have hI2 : I^(2*m) = (-1)^m := by rw [pow_mul, I_sq]
      have hnI2 : (-I)^(2*m) = (-1)^m := by rw [pow_mul, neg_sq, I_sq]
      rw [show (-(-I*z)) = I*z by ring, show (-(I*z)) = (-I)*z by ring, mul_pow, mul_pow, hI2, hnI2,
        sub_self, mul_zero]
  have hsi : genSinInt a z = exp (a*log z) * (Gamma a/(2*I)*(DLMF.Statistical.scIncGamma a (-I*z) - DLMF.Statistical.scIncGamma a (I*z))) := by
    rw [genSinInt, incG_genSinIntOnLog_eq, Complex.exp_log hz, hodd.tsum_eq]
  rw [hsi, genSinIntTail, genSinIntTailOnLog, upperIncGammaOnLog_eq_Gamma_sub ha,
    upperIncGammaOnLog_eq_Gamma_sub ha, lowerIncGammaOnLog, lowerIncGammaOnLog,
    incG_exp_log_sub_half_pi hz, incG_exp_log_add_half_pi hz,
    show a*(log z - π*I/2) = a*log z + (-π*I*a/2) by ring,
    show a*(log z + π*I/2) = a*log z + π*I*a/2 by ring, Complex.exp_add, Complex.exp_add]
  have hE : exp (π*I*a/2) * exp (-π*I*a/2) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
  have hsin : sin (π*a/2) = (exp (-π*I*a/2) - exp (π*I*a/2))*I/2 := by
    rw [Complex.sin]; ring_nf
  rw [hsin]
  set E := exp (π*I*a/2)
  set E' := exp (-π*I*a/2)
  set X := exp (a*log z)
  field_simp
  linear_combination (-(X*DLMF.Statistical.scIncGamma a (-(I*z))) + X*DLMF.Statistical.scIncGamma a (I*z))*hE + (E - E')*I_sq

/-- `ci(a,z) + Ci(a,z) = Γ(a) cos(πa/2)` at regular parameters. -/
theorem incG_genCos_add_tail {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) {z : ℂ} (hz : z ≠ 0) :
    genCosInt a z + genCosIntTail a z = Gamma a * cos (π*a/2) := by
  have hG := Gamma_ne_zero ha
  have hs₁ := scIncGamma_hasSum_alternating ha (-I*z)
  have hs₂ := scIncGamma_hasSum_alternating ha (I*z)
  have hD := (hs₁.add hs₂).mul_left (Gamma a/2)
  have heven : HasSum (fun m : ℕ => incG_trigTerm z 0 ∅ m a)
      (Gamma a/2*(DLMF.Statistical.scIncGamma a (-I*z) + DLMF.Statistical.scIncGamma a (I*z))) := by
    have hinj : Function.Injective (fun m : ℕ => 2*m) := fun m n h => by simp at h; omega
    rw [← hinj.hasSum_iff] at hD
    · refine hD.congr_fun fun m => ?_
      simp only [Function.comp_apply, incG_trigTerm, Finset.notMem_empty, ite_false, add_zero]
      have hk : a + ((2*m:ℕ):ℂ) ≠ 0 := by
        intro h; exact ha (2*m) (by linear_combination h)
      have hI2 : I^(2*m) = (-1)^m := by rw [pow_mul, I_sq]
      have hnI2 : (-I)^(2*m) = (-1)^m := by rw [pow_mul, neg_sq, I_sq]
      rw [show (-(-I*z)) = I*z by ring, show (-(I*z)) = (-I)*z by ring, mul_pow, mul_pow, hI2, hnI2]
      have hf : ((2*m).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have hk' : ((2*m:ℕ):ℂ) + a ≠ 0 := by rw [add_comm]; exact hk
      field_simp
      ring
    · intro k hk
      obtain ⟨m, rfl⟩ : ∃ m, k = 2*m+1 := by
        rcases Nat.even_or_odd k with ⟨r, hr⟩ | ⟨r, hr⟩
        · exact absurd ⟨r, by simp only; omega⟩ hk
        · exact ⟨r, hr⟩
      have hI2 : I^(2*m+1) = I*(-1)^m := by rw [pow_succ, pow_mul, I_sq]; ring
      have hnI2 : (-I)^(2*m+1) = -(I*(-1)^m) := by rw [pow_succ, pow_mul, neg_sq, I_sq]; ring
      rw [show (-(-I*z)) = I*z by ring, show (-(I*z)) = (-I)*z by ring, mul_pow, mul_pow, hI2, hnI2]
      ring
  have hci : genCosInt a z = exp (a*log z) * (Gamma a/2*(DLMF.Statistical.scIncGamma a (-I*z) + DLMF.Statistical.scIncGamma a (I*z))) := by
    rw [genCosInt, incG_genCosIntOnLog_eq, Complex.exp_log hz, heven.tsum_eq]
  rw [hci, genCosIntTail, genCosIntTailOnLog, upperIncGammaOnLog_eq_Gamma_sub ha,
    upperIncGammaOnLog_eq_Gamma_sub ha, lowerIncGammaOnLog, lowerIncGammaOnLog,
    incG_exp_log_sub_half_pi hz, incG_exp_log_add_half_pi hz,
    show a*(log z - π*I/2) = a*log z + (-π*I*a/2) by ring,
    show a*(log z + π*I/2) = a*log z + π*I*a/2 by ring, Complex.exp_add, Complex.exp_add]
  have hE : exp (π*I*a/2) * exp (-π*I*a/2) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
  have hcos : cos (π*a/2) = (exp (π*I*a/2) + exp (-π*I*a/2))/2 := by
    rw [Complex.cos]; ring_nf
  rw [hcos]
  set E := exp (π*I*a/2)
  set E' := exp (-π*I*a/2)
  set X := exp (a*log z)
  field_simp
  linear_combination (-(X*DLMF.Statistical.scIncGamma a (-(I*z))) - X*DLMF.Statistical.scIncGamma a (I*z))*hE

theorem incG_genSinIntTail_continuous (z : ℂ) : Continuous fun b => genSinIntTail b z := by
  unfold genSinIntTail genSinIntTailOnLog
  have h1 := continuous_upperIncGammaOnLog_param (log z - π*I/2)
  have h2 := continuous_upperIncGammaOnLog_param (log z + π*I/2)
  exact (((by fun_prop : Continuous fun b : ℂ => exp (π*I*b/2)).mul h1).sub
    ((by fun_prop : Continuous fun b : ℂ => exp (-π*I*b/2)).mul h2)).div_const _

theorem incG_genCosIntTail_continuous (z : ℂ) : Continuous fun b => genCosIntTail b z := by
  unfold genCosIntTail genCosIntTailOnLog
  have h1 := continuous_upperIncGammaOnLog_param (log z - π*I/2)
  have h2 := continuous_upperIncGammaOnLog_param (log z + π*I/2)
  exact (((by fun_prop : Continuous fun b : ℂ => exp (π*I*b/2)).mul h1).add
    ((by fun_prop : Continuous fun b : ℂ => exp (-π*I*b/2)).mul h2)).div_const _

theorem incG_genSinInt_complement {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n+1)) {z : ℂ} (hz : z ≠ 0) :
    genSinInt a z=gammaSinHalfPiContinued a-genSinIntTail a z := by
  have hcont : ContinuousAt (fun b => genSinInt b z + genSinIntTail b z) a :=
    (genSinInt_parameter_analytic ha (log z)).continuousAt.add
      (incG_genSinIntTail_continuous z).continuousAt
  have hlim : Tendsto (fun b : ℂ => Gamma b*sin (π*b/2)) (𝓝[≠] a)
      (𝓝 (genSinInt a z + genSinIntTail a z)) := by
    refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [incG_eventually_nhdsNE_regular a] with b hb
    exact incG_genSin_add_tail hb hz
  rw [gammaSinHalfPiContinued, hlim.limUnder_eq]; ring

theorem incG_genCosInt_complement {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n : ℂ)) {z : ℂ} (hz : z ≠ 0) :
    genCosInt a z=gammaCosHalfPiContinued a-genCosIntTail a z := by
  have hcont : ContinuousAt (fun b => genCosInt b z + genCosIntTail b z) a :=
    (genCosInt_parameter_analytic ha (log z)).continuousAt.add
      (incG_genCosIntTail_continuous z).continuousAt
  have hlim : Tendsto (fun b : ℂ => Gamma b*cos (π*b/2)) (𝓝[≠] a)
      (𝓝 (genCosInt a z + genCosIntTail a z)) := by
    refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [incG_eventually_nhdsNE_regular a] with b hb
    exact incG_genCos_add_tail hb hz
  rw [gammaCosHalfPiContinued, hlim.limUnder_eq]; ring

theorem incG_genSinInt_value_at_infinity {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n+1)) (ha1 : a.re < 1) :
    Tendsto (fun x : ℝ => genSinInt a x) atTop (𝓝 (gammaSinHalfPiContinued a)) := by
  have h := ((tendsto_genTrigTail_add_ofReal ha1 0).1).const_sub (gammaSinHalfPiContinued a)
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [zero_add, incG_genSinInt_complement ha (ofReal_ne_zero.mpr hx.ne')]

theorem incG_genCosInt_value_at_infinity {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n : ℂ)) (ha1 : a.re < 1) :
    Tendsto (fun x : ℝ => genCosInt a x) atTop (𝓝 (gammaCosHalfPiContinued a)) := by
  have h := ((tendsto_genTrigTail_add_ofReal ha1 0).2).const_sub (gammaCosHalfPiContinued a)
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [zero_add, incG_genCosInt_complement ha (ofReal_ne_zero.mpr hx.ne')]

/-- genSinInt complement. -/
@[dlmf 8.21.E8]
theorem genSinInt_complement {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n+1)) {z : ℂ} (hz : z ≠ 0) :
    genSinInt a z=gammaSinHalfPiContinued a-genSinIntTail a z :=
  incG_genSinInt_complement ha hz

/-- genCosInt complement. -/
@[dlmf 8.21.E9]
theorem genCosInt_complement {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n : ℂ)) {z : ℂ} (hz : z ≠ 0) :
    genCosInt a z=gammaCosHalfPiContinued a-genCosIntTail a z :=
  incG_genCosInt_complement ha hz

/-- Ein at the negative rotated argument, by the parities of Cin and Si. -/
theorem expIntEin_neg_mul_I_eq (z : ℂ) : expIntEin (-I*z)=cosIntCin z-I*sinInt z := by
  have h := expIntEin_mul_I (-z)
  rw [show I*(-z)=-I*z by ring, cosIntCin_even, sinInt_odd] at h
  rw [h]; ring

/-- genTrig order zero. -/
@[dlmf 8.21.E10]
theorem genTrig_order_zero {z : ℂ} (hz : z ≠ 0) :
    genSinIntTail 0 z = -sinIntTail z ∧ genCosIntTail 0 z = -cosInt z := by
  have h1 : exp (log z-π*I/2)=-I*z := by
    rw [Complex.exp_sub, Complex.exp_log hz, show (π:ℂ)*I/2=(π/2:ℂ)*I by ring,
      Complex.exp_mul_I]
    simp [Complex.cos_pi_div_two, Complex.sin_pi_div_two]
    field_simp
  have h2 : exp (log z+π*I/2)=I*z := by
    rw [Complex.exp_add, Complex.exp_log hz, show (π:ℂ)*I/2=(π/2:ℂ)*I by ring,
      Complex.exp_mul_I]
    simp [Complex.cos_pi_div_two, Complex.sin_pi_div_two]
    ring
  simp only [genSinIntTail, genCosIntTail, genSinIntTailOnLog, genCosIntTailOnLog, mul_zero,
    zero_div, Complex.exp_zero, one_mul, upperIncGammaOnLog_zero, h1, h2, expIntEin_mul_I,
    expIntEin_neg_mul_I_eq, sinIntTail, cosInt]
  constructor
  · field_simp; ring_nf
  · ring

/-- genSinInt order zero. -/
@[dlmf 8.21.E11]
theorem genSinInt_order_zero {z : ℂ} (hz : z ≠ 0) :
    genSinInt 0 z=sinInt z := by
  simp only [genSinInt,genSinIntOnLog,zero_mul,Complex.exp_zero,one_mul,add_zero]
  unfold sinInt
  apply tsum_congr
  intro k
  rw [show (2*k+1:ℂ)*log z=((2*k+1:ℕ):ℂ)*log z by push_cast; ring,Complex.exp_nat_mul,Complex.exp_log hz]
  ring

/-- Ordinary infinity limits need Re a<1; other values are interpreted by parameter continuation. -/
@[dlmf 8.21.E12]
theorem genSinInt_value_at_infinity {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n+1)) (ha1 : a.re < 1) :
    Tendsto (fun x : ℝ => genSinInt a x) atTop (𝓝 (gammaSinHalfPiContinued a)) :=
  incG_genSinInt_value_at_infinity ha ha1

/-- genCosInt value at infinity. -/
@[dlmf 8.21.E13]
theorem genCosInt_value_at_infinity {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n : ℂ)) (ha1 : a.re < 1) :
    Tendsto (fun x : ℝ => genCosInt a x) atTop (𝓝 (gammaCosHalfPiContinued a)) :=
  incG_genCosInt_value_at_infinity ha ha1

/-- The logarithmic cosine series is absolutely convergent at every logarithmic argument. -/
theorem genCosIntOnLog_hasSum (a w : ℂ) :
    HasSum (fun k : ℕ=>exp (a*w)*(-1:ℂ)^k*(exp w)^(2*k)/
      ((2*k+a)*(2*k).factorial)) (genCosIntOnLog a w) := by
  have hs := (summable_genTrig_coeff a (exp w) 0).hasSum.mul_left (exp (a*w))
  have he (k : ℕ) : exp ((2*k:ℂ)*w)=(exp w)^(2*k) := by
    rw [show (2*k:ℂ)=((2*k:ℕ):ℂ) by push_cast; ring,exp_nat_mul]
  unfold genCosIntOnLog
  simp_rw [he]
  convert hs using 1
  · funext k
    push_cast
    ring
  · congr 1
    apply tsum_congr
    intro k
    push_cast
    ring

/-- The logarithmic sine series is absolutely convergent at every logarithmic argument. -/
theorem genSinIntOnLog_hasSum (a w : ℂ) :
    HasSum (fun k : ℕ=>exp (a*w)*(-1:ℂ)^k*(exp w)^(2*k+1)/
      ((2*k+a+1)*(2*k+1).factorial)) (genSinIntOnLog a w) := by
  have hs := (summable_genTrig_coeff a (exp w) 1).hasSum.mul_left (exp (a*w))
  have he (k : ℕ) : exp ((2*k+1:ℂ)*w)=(exp w)^(2*k+1) := by
    rw [show (2*k+1:ℂ)=((2*k+1:ℕ):ℂ) by push_cast; ring,exp_nat_mul]
  unfold genSinIntOnLog
  simp_rw [he]
  convert hs using 1
  · funext k
    push_cast
    ring
  · congr 1
    apply tsum_congr
    intro k
    push_cast
    ring

/-- genLowerTrig gamma. -/
@[dlmf 8.21.E2]
theorem genLowerTrig_gamma {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (w : ℂ) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    genCosIntOnLog a w+ε*I*genSinIntOnLog a w=exp (ε*π*I*a/2)*lowerIncGammaOnLog a (w-ε*π*I/2) := by
  have ht : ((ε:ℂ)*I)^2= -1 := by
    rcases hε with rfl | rfl <;> norm_num [Complex.I_sq]
  have he : -exp (w-ε*π*I/2)=((ε:ℂ)*I)*exp w := by
    rw [sub_eq_add_neg,exp_add]
    rcases hε with rfl | rfl
    · simp only [ofReal_one,one_mul]
      rw [show -(π*I/2)= -π/2*I by ring,exp_neg_pi_div_two_mul_I]
      ring
    · simp only [ofReal_neg,ofReal_one,neg_mul,one_mul,neg_neg]
      rw [show -(-(π*I)/2)=π/2*I by ring,exp_pi_div_two_mul_I]
      ring
  let f : ℕ→ℂ := fun k=>exp (a*w)*((ε:ℂ)*I)^k*(exp w)^k/
    ((a+k)*(k.factorial:ℂ))
  have hce : HasSum (fun k=>f (2*k)) (genCosIntOnLog a w) := by
    refine (genCosIntOnLog_hasSum a w).congr_fun fun k=>?_
    dsimp [f]
    rw [pow_mul,ht]
    push_cast
    ring
  have hso : HasSum (fun k=>f (2*k+1)) (ε*I*genSinIntOnLog a w) := by
    refine ((genSinIntOnLog_hasSum a w).mul_left (ε*I)).congr_fun fun k=>?_
    dsimp [f]
    rw [pow_succ,pow_mul,ht]
    push_cast
    ring
  have hs := (scIncGamma_hasSum_alternating ha (exp (w-ε*π*I/2))).mul_left
    (Gamma a*exp (a*w))
  have hfull : HasSum f (Gamma a*exp (a*w)*DLMF.Statistical.scIncGamma a (exp (w-ε*π*I/2))) := by
    refine hs.congr_fun fun k=>?_
    dsimp [f]
    rw [he,mul_pow]
    field_simp [Gamma_ne_zero ha]
    simp only [mul_pow]
  have hsum := (hce.even_add_odd hso).unique hfull
  rw [hsum,lowerIncGammaOnLog]
  have hp : exp (a*w)=exp (ε*π*I*a/2)*exp (a*(w-ε*π*I/2)) := by
    rw [←exp_add]
    congr 1
    ring
  rw [hp]
  ring

/-- genSinInt hasSum. -/
@[dlmf 8.21.E14]
theorem genSinInt_hasSum {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n+1)) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => z^a*(-1 : ℂ)^k*z^(2*k+1)/((2*k+a+1)*(2*k+1).factorial)) (genSinInt a z) := by
  have hs := (summable_genTrig_coeff a z 1).hasSum.mul_left (z^a)
  have he (k : ℕ) : exp ((2*k+1:ℂ)*log z)=z^(2*k+1) := by
    rw [show (2*k+1:ℂ)*log z=((2*k+1:ℕ):ℂ)*log z by push_cast; ring,
      Complex.exp_nat_mul,Complex.exp_log hz]
  rw [genSinInt,genSinIntOnLog]
  rw [show exp (a*log z)=z^a by rw [cpow_def_of_ne_zero hz]; congr 1; ring]
  simp_rw [he]
  convert hs using 1
  · funext k
    push_cast
    ring
  · congr 1
    apply tsum_congr
    intro k
    push_cast
    ring

/-- genCosInt hasSum. -/
@[dlmf 8.21.E15]
theorem genCosInt_hasSum {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n : ℂ)) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => z^a*(-1 : ℂ)^k*z^(2*k)/((2*k+a)*(2*k).factorial)) (genCosInt a z) := by
  have hs := (summable_genTrig_coeff a z 0).hasSum.mul_left (z^a)
  have he (k : ℕ) : exp ((2*k+0:ℂ)*log z)=z^(2*k+0) := by
    rw [show (2*k+0:ℂ)*log z=((2*k+0:ℕ):ℂ)*log z by push_cast; ring,
      Complex.exp_nat_mul,Complex.exp_log hz]
  rw [genCosInt,genCosIntOnLog]
  rw [show exp (a*log z)=z^a by rw [cpow_def_of_ne_zero hz]; congr 1; ring]
  simp only [Nat.add_zero] at hs he
  simp only [add_zero] at he
  simp_rw [he]
  convert hs using 1
  · funext k
    push_cast
    ring
  · congr 1
    apply tsum_congr
    intro k
    push_cast
    ring

/-- Termwise integration of `∑ t^{s+2k} c_k` over `[0,1]`. -/
theorem hasSum_integral_cpow_two_mul {s : ℂ} (hs : -1 < s.re) {c : ℕ → ℂ}
    (hc : Summable fun k => ‖c k‖) :
    HasSum (fun k : ℕ => c k/(s+2*k+1))
      (∫ t : ℝ in (0:ℝ)..1, ∑' k : ℕ, (t:ℂ)^(s+2*k)*c k) := by
  have hb : ∀ k : ℕ, ∀ t : ℝ, t ∈ Set.uIoc (0:ℝ) 1 → ‖(t:ℂ)^(s+2*k)*c k‖ ≤ t^s.re*‖c k‖ := by
    intro k t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht.1]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 ?_
    simp
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := 0) (b := 1) (F := fun (k : ℕ) (t:ℝ) => (t:ℂ)^(s+2*k)*c k)
    (f := fun t : ℝ => ∑' k : ℕ, (t:ℂ)^(s+2*k)*c k)
    (fun (k : ℕ) (t : ℝ) => t^s.re*‖c k‖)
    (fun k => ((Complex.measurable_ofReal.pow_const _).mul_const _).aestronglyMeasurable)
    (fun k => Eventually.of_forall fun t ht => hb k t ht)
    (Eventually.of_forall fun t _ => hc.mul_left _)
    (by
      simp_rw [tsum_mul_left]
      exact (intervalIntegral.intervalIntegrable_rpow' hs).mul_const _)
    (Eventually.of_forall fun t ht => (Summable.of_norm_bounded (hc.mul_left (t^s.re))
      (fun k => hb k t ht)).hasSum)
  refine hsum.congr_fun fun k => ?_
  have hre : -1 < (s+2*k).re := by simp; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hne : s+2*k+1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  rw [intervalIntegral.integral_mul_const, integral_cpow (Or.inl hre)]
  simp only [ofReal_one, one_cpow, ofReal_zero, zero_cpow hne]
  field_simp
  ring

/-- genSinInt segment integral. -/
@[dlmf 8.21.E6]
theorem genSinInt_segment_integral {a : ℂ} (ha : -1 < a.re) {z : ℂ} (hz : z ∈ slitPlane) :
    genSinInt a z=primitive (fun t => t^(a-1)*sin t) z := by
  have hz0 := slitPlane_ne_zero hz
  set c : ℕ → ℂ := fun k => z^(a-1)*((-1:ℂ)^k*z^(2*k+1)/((2*k+1).factorial : ℂ))
  have hc : Summable fun k => ‖c k‖ := by
    have h := ((Real.summable_pow_div_factorial ‖z‖).comp_injective
      (strictMono_nat_of_lt_succ (f := fun k : ℕ => 2*k+1) (fun k => by omega)).injective).mul_left
      ‖z^(a-1)‖
    refine h.congr fun k => ?_
    simp [c]
  have hI := hasSum_integral_cpow_two_mul ha hc
  have hint : (∫ t : ℝ in (0:ℝ)..1, (0+(t:ℂ)*(z-0))^(a-1)*sin (0+(t:ℂ)*(z-0))) =
      ∫ t : ℝ in (0:ℝ)..1, ∑' k : ℕ, (t:ℂ)^(a+2*k)*c k := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
    rw [Set.uIoc_of_le zero_le_one] at ht
    have ht0 : (t:ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
    rw [zero_add, sub_zero, ofReal_mul_cpow_of_pos ht.1 hz0, ← (Complex.hasSum_sin _).tsum_eq,
      ← tsum_mul_left]
    congr 1; funext k
    simp only [c]
    rw [mul_pow, show a+2*(k:ℂ) = (a-1) + ((2*k+1 : ℕ) : ℂ) by push_cast; ring, cpow_add _ _ ht0,
      cpow_natCast]
    ring
  rw [primitive, segmentIntegral, hint, ← hI.tsum_eq, sub_zero, ← tsum_mul_left,
    ← (genSinInt_hasSum (fun n h => by
      have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]) hz0).tsum_eq]
  congr 1; funext k
  have hza : z ^ a = z * z ^ (a-1) := by
    conv_lhs => rw [show a = 1 + (a - 1) by ring]
    rw [Complex.cpow_add _ _ hz0, Complex.cpow_one]
  simp only [c]
  rw [hza]
  have hne : a+2*k+1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hne' : 2*k+a+1 ≠ 0 := by rw [show 2*(k:ℂ)+a+1 = a+2*k+1 by ring]; exact hne
  have hf : ((2*k+1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  ring

/-- genCosInt segment integral. -/
@[dlmf 8.21.E7]
theorem genCosInt_segment_integral {a : ℂ} (ha : 0 < a.re) {z : ℂ} (hz : z ∈ slitPlane) :
    genCosInt a z=primitive (fun t => t^(a-1)*cos t) z := by
  have hz0 := slitPlane_ne_zero hz
  set c : ℕ → ℂ := fun k => z^(a-1)*((-1:ℂ)^k*z^(2*k)/((2*k).factorial : ℂ))
  have hc : Summable fun k => ‖c k‖ := by
    have h := ((Real.summable_pow_div_factorial ‖z‖).comp_injective
      (strictMono_nat_of_lt_succ (f := fun k : ℕ => 2*k) (fun k => by omega)).injective).mul_left
      ‖z^(a-1)‖
    refine h.congr fun k => ?_
    simp [c]
  have hI := hasSum_integral_cpow_two_mul (s := a-1) (by simp; linarith) hc
  have hint : (∫ t : ℝ in (0:ℝ)..1, (0+(t:ℂ)*(z-0))^(a-1)*cos (0+(t:ℂ)*(z-0))) =
      ∫ t : ℝ in (0:ℝ)..1, ∑' k : ℕ, (t:ℂ)^(a-1+2*k)*c k := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
    rw [Set.uIoc_of_le zero_le_one] at ht
    have ht0 : (t:ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
    rw [zero_add, sub_zero, ofReal_mul_cpow_of_pos ht.1 hz0, ← (Complex.hasSum_cos _).tsum_eq,
      ← tsum_mul_left]
    congr 1; funext k
    simp only [c]
    rw [mul_pow, show a-1+2*(k:ℂ) = (a-1) + ((2*k : ℕ) : ℂ) by push_cast; ring, cpow_add _ _ ht0,
      cpow_natCast]
    ring
  rw [primitive, segmentIntegral, hint, ← hI.tsum_eq, sub_zero, ← tsum_mul_left,
    ← (genCosInt_hasSum (fun n h => by
      have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]) hz0).tsum_eq]
  congr 1; funext k
  have hza : z ^ a = z * z ^ (a-1) := by
    conv_lhs => rw [show a = 1 + (a - 1) by ring]
    rw [Complex.cpow_add _ _ hz0, Complex.cpow_one]
  simp only [c]
  rw [hza]
  have hne : a-1+2*k+1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hne' : 2*k+a ≠ 0 := by rw [show 2*(k:ℂ)+a = a-1+2*k+1 by ring]; exact hne
  have hf : ((2*k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  ring

/-- The entire part of the generalized sine integral, `∑ (-1)^k z^{2k+1}/((2k+1+a)(2k+1)!)`:
its Euler image `z H' + a H` is `sin z`. -/
theorem gsSph_sin_part {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n+1)) :
    let h : ℕ → ℂ → ℂ := fun k w => (-1 : ℂ)^k*w^(2*k+1)/((2*k+a+1)*(2*k+1).factorial)
    Differentiable ℂ (fun w => ∑' k, h k w) ∧
      ∀ w, w * deriv (fun w => ∑' k, h k w) w + a * ∑' k, h k w = sin w := by
  intro h
  have hne : ∀ k : ℕ, (2*k+a+1 : ℂ) ≠ 0 := fun k e => ha k (by linear_combination e)
  have hf : ∀ k w, HasDerivAt (h k) ((-1 : ℂ)^k*((2*k+1:ℕ) * w^(2*k))/
      ((2*k+a+1)*(2*k+1).factorial)) w := fun k w => by
    have := ((hasDerivAt_pow (2*k+1) w).const_mul ((-1:ℂ)^k)).div_const
      ((2*k+a+1)*(2*k+1).factorial)
    simpa using this
  have hb : ∀ R : ℝ, ∃ u : ℕ → ℝ, Summable u ∧ ∀ n w, ‖w‖ < R → ‖h n w‖ ≤ u n := by
    intro R
    refine ⟨fun k => ‖(2*k+a+1 : ℂ)⁻¹‖ * (|R|^(2*k+1)/(2*k+1).factorial), ?_, fun k w hw => ?_⟩
    · have hd : Function.Injective (fun n : ℕ => 2*n+1) := by intro n m e; dsimp at e; omega
      refine Summable.of_norm_bounded_eventually_nat
        ((Real.summable_pow_div_factorial |R|).comp_injective hd) ?_
      filter_upwards [eventually_ge_atTop ⌈‖a‖⌉₊] with k hk
      have hk' : ‖a‖ ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
      have h1 : 1 ≤ ‖(2*k+a+1 : ℂ)‖ := by
        have := norm_sub_norm_le ((2*k+1 : ℂ)) (-a)
        rw [show (2*k+1:ℂ) - -a = 2*k+a+1 by ring, norm_neg,
          show (2*k+1:ℂ) = ((2*k+1:ℕ):ℂ) by push_cast; ring, Complex.norm_natCast] at this
        push_cast at this; linarith
      have hp : 0 ≤ |R|^(2*k+1)/((2*k+1).factorial : ℝ) := by positivity
      rw [Real.norm_of_nonneg (by positivity), norm_inv]
      simp only [Function.comp_apply]
      calc ‖(2*k+a+1 : ℂ)‖⁻¹ * (|R|^(2*k+1)/((2*k+1).factorial : ℝ))
          ≤ 1 * (|R|^(2*k+1)/((2*k+1).factorial : ℝ)) := by
            gcongr; exact inv_le_one_of_one_le₀ h1
        _ = _ := one_mul _
    · have hw' : ‖w‖ ≤ |R| := hw.le.trans (le_abs_self R)
      simp only [h, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        Complex.norm_natCast]
      rw [div_eq_mul_inv, mul_inv, norm_inv]
      calc ‖w‖^(2*k+1) * (‖(2*k+a+1 : ℂ)‖⁻¹ * ((2*k+1).factorial : ℝ)⁻¹)
          ≤ |R|^(2*k+1) * (‖(2*k+a+1 : ℂ)‖⁻¹ * ((2*k+1).factorial : ℝ)⁻¹) := by gcongr
        _ = _ := by ring
  obtain ⟨hD, hS⟩ := sphSeries_euler_hasSum a hf hb
  refine ⟨hD, fun w => (hS w).unique ?_⟩
  refine (Complex.hasSum_sin w).congr_fun fun k => ?_
  have hf' : ((2*k+1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  simp only [h]
  field_simp [hne k]
  push_cast
  ring

/-- The entire part of the generalized cosine integral, `∑ (-1)^k z^{2k}/((2k+a)(2k)!)`:
its Euler image `z H' + a H` is `cos z`. -/
theorem gsSph_cos_part {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n : ℂ)) :
    let h : ℕ → ℂ → ℂ := fun k w => (-1 : ℂ)^k*w^(2*k)/((2*k+a)*(2*k).factorial)
    Differentiable ℂ (fun w => ∑' k, h k w) ∧
      ∀ w, w * deriv (fun w => ∑' k, h k w) w + a * ∑' k, h k w = cos w := by
  intro h
  have hne : ∀ k : ℕ, (2*k+a : ℂ) ≠ 0 := fun k e => ha k (by linear_combination e)
  have hf : ∀ k w, HasDerivAt (h k) ((-1 : ℂ)^k*((2*k:ℕ) * w^(2*k-1))/
      ((2*k+a)*(2*k).factorial)) w := fun k w => by
    have := ((hasDerivAt_pow (2*k) w).const_mul ((-1:ℂ)^k)).div_const
      ((2*k+a)*(2*k).factorial)
    simpa using this
  have hb : ∀ R : ℝ, ∃ u : ℕ → ℝ, Summable u ∧ ∀ n w, ‖w‖ < R → ‖h n w‖ ≤ u n := by
    intro R
    refine ⟨fun k => ‖(2*k+a : ℂ)⁻¹‖ * (|R|^(2*k)/(2*k).factorial), ?_, fun k w hw => ?_⟩
    · have hd : Function.Injective (fun n : ℕ => 2*n) := by intro n m e; dsimp at e; omega
      refine Summable.of_norm_bounded_eventually_nat
        ((Real.summable_pow_div_factorial |R|).comp_injective hd) ?_
      filter_upwards [eventually_ge_atTop (⌈‖a‖⌉₊+1)] with k hk
      have hk' : ‖a‖ + 1 ≤ 2*k := by
        have := (Nat.le_ceil ‖a‖).trans (by exact_mod_cast (Nat.le_of_succ_le hk) : (⌈‖a‖⌉₊:ℝ) ≤ k)
        have h1 : (1:ℝ) ≤ k := by exact_mod_cast (Nat.one_le_of_lt hk)
        linarith
      have h1 : 1 ≤ ‖(2*k+a : ℂ)‖ := by
        have := norm_sub_norm_le ((2*k : ℂ)) (-a)
        rw [show (2*k:ℂ) - -a = 2*k+a by ring, norm_neg,
          show (2*k:ℂ) = ((2*k:ℕ):ℂ) by push_cast; ring, Complex.norm_natCast] at this
        push_cast at this; linarith
      rw [Real.norm_of_nonneg (by positivity), norm_inv]
      simp only [Function.comp_apply]
      calc ‖(2*k+a : ℂ)‖⁻¹ * (|R|^(2*k)/((2*k).factorial : ℝ))
          ≤ 1 * (|R|^(2*k)/((2*k).factorial : ℝ)) := by
            gcongr; exact inv_le_one_of_one_le₀ h1
        _ = _ := one_mul _
    · have hw' : ‖w‖ ≤ |R| := hw.le.trans (le_abs_self R)
      simp only [h, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        Complex.norm_natCast]
      rw [div_eq_mul_inv, mul_inv, norm_inv]
      calc ‖w‖^(2*k) * (‖(2*k+a : ℂ)‖⁻¹ * ((2*k).factorial : ℝ)⁻¹)
          ≤ |R|^(2*k) * (‖(2*k+a : ℂ)‖⁻¹ * ((2*k).factorial : ℝ)⁻¹) := by gcongr
        _ = _ := by ring
  obtain ⟨hD, hS⟩ := sphSeries_euler_hasSum a hf hb
  refine ⟨hD, fun w => (hS w).unique ?_⟩
  refine (Complex.hasSum_cos w).congr_fun fun k => ?_
  have hf' : ((2*k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  simp only [h]
  rcases k with _ | k
  · have ha0 : a ≠ 0 := by simpa using hne 0
    simp; field_simp [ha0]
  · have hp : w * w^(2*(k+1)-1) = w^(2*(k+1)) := by
      rw [show 2*(k+1)-1 = 2*k+1 by omega, show 2*(k+1) = 2*k+1+1 by ring, pow_succ]; ring
    field_simp [hne (k+1)]
    rw [div_eq_iff (hne (k+1))]
    push_cast at hp ⊢
    linear_combination (2*((k:ℂ)+1)) * hp

/-- genSinInt spherical series. -/
@[dlmf 8.21.E16]
theorem genSinInt_spherical_series {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n+1)) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => z^a*(2*k+3/2 : ℂ)*poch (1-a/2) k/poch (1/2+a/2) (k+1)*sphericalJ (2*k+1) z) (genSinInt a z) := by
  obtain ⟨hHd, hHL⟩ := gsSph_sin_part ha
  set H : ℂ → ℂ := fun w => ∑' k : ℕ, (-1 : ℂ)^k*w^(2*k+1)/((2*k+a+1)*(2*k+1).factorial) with hH
  have hQ : ∀ k : ℕ, (1/2+a/2+k : ℂ) ≠ 0 := fun k e => ha k (by linear_combination 2*e)
  have hQk : ∀ k : ℕ, poch (1/2+a/2) k ≠ 0 := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [poch_succ]; exact mul_ne_zero ih (hQ k)
  set c : ℕ → ℂ := fun k => (2*k+3/2 : ℂ)*poch (1-a/2) k/poch (1/2+a/2) (k+1) with hc
  set e : ℕ → ℂ := fun k => poch (1-a/2) k/poch (1/2+a/2) k with he
  clear_value c e
  have hratio := sphSeries_eventually_norm_add_le (1-a/2) (1/2+a/2)
  have hratio2 := sphSeries_eventually_norm_add_le (1-a/2) (1/2+a/2+1)
  have he_r : ∀ᶠ k in atTop, ‖e (k+1)‖ ≤ 2 * ‖e k‖ := by
    filter_upwards [hratio] with k hk
    simp only [he, poch_succ]
    rw [mul_div_mul_comm, norm_mul, norm_div]
    have hq := norm_pos_iff.mpr (hQ k)
    rw [mul_comm, show (1/2+a/2+k : ℂ) = 1/2+a/2+(k:ℂ) from rfl]
    have hb : ‖(1-a/2+k : ℂ)‖/‖(1/2+a/2+k : ℂ)‖ ≤ 2 := by rw [div_le_iff₀ hq]; linarith
    exact mul_le_mul_of_nonneg_right (by rw [norm_div]; exact hb) (by positivity)
  have hc_r : ∀ᶠ k in atTop, ‖c (k+1)‖ ≤ 6 * ‖c k‖ := by
    filter_upwards [hratio2] with k hk
    have hq := norm_pos_iff.mpr (hQ (k+1))
    have e1 : c (k+1) = c k * ((2*k+7/2)/(2*k+3/2)) * ((1-a/2+k)/(1/2+a/2+(k+1:ℕ))) := by
      have h32 : (2*(k:ℂ)+3/2) ≠ 0 := by
        have : (0:ℝ) < 2*k+3/2 := by positivity
        have h' : ((2*k+3/2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast this.ne'
        push_cast at h'; exact h'
      have hQ1 : (1/2+a/2+((k:ℂ)+1)) ≠ 0 := by have := hQ (k+1); push_cast at this; exact this
      have hQ0 := hQ k
      simp only [hc, poch_succ]
      push_cast
      generalize poch (1-a/2) k = P
      have hQk' := hQk k
      generalize poch (1/2+a/2) k = Q at hQk' ⊢
      generalize (1/2+a/2+(k:ℂ)) = u at hQ0 ⊢
      generalize (1/2+a/2+((k:ℂ)+1)) = v at hQ1 ⊢
      generalize (2*(k:ℂ)+3/2) = t at h32 ⊢
      field_simp
      ring
    rw [e1, norm_mul, norm_mul, norm_div, norm_div]
    have h1 : ‖(2*k+7/2 : ℂ)‖ ≤ 3 * ‖(2*k+3/2 : ℂ)‖ := by
      rw [show (2*k+7/2 : ℂ) = ((2*k+7/2 : ℝ) : ℂ) by push_cast; ring,
        show (2*k+3/2 : ℂ) = ((2*k+3/2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (by positivity)]
      linarith
    have h2 : ‖(1-a/2+k : ℂ)‖ ≤ 2 * ‖(1/2+a/2+(k+1:ℕ) : ℂ)‖ := by
      push_cast; rw [show (1/2+a/2+((k:ℂ)+1)) = 1/2+a/2+1+(k:ℂ) by ring]; exact hk
    have hp1 : 0 < ‖(2*k+3/2 : ℂ)‖ := by
      rw [show (2*k+3/2 : ℂ) = ((2*k+3/2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      positivity
    have hq' : 0 < ‖(1/2+a/2+(k+1:ℕ) : ℂ)‖ := by push_cast at hq ⊢; exact hq
    calc ‖c k‖ * (‖(2*k+7/2 : ℂ)‖/‖(2*k+3/2 : ℂ)‖) *
          (‖(1-a/2+k : ℂ)‖/‖(1/2+a/2+(k+1:ℕ) : ℂ)‖) ≤ ‖c k‖ * 3 * 2 := by
          gcongr
          · rw [div_le_iff₀ hp1]; linarith
          · rw [div_le_iff₀ hq']; linarith
      _ = 6 * ‖c k‖ := by ring
  have hL : ∀ k w, w * (c k * (((((2*k:ℕ):ℂ)+1) * sphericalJ (2*k) w - (((2*k:ℕ):ℂ)+2) *
      sphericalJ (2*k+2) w) / (2*((2*k:ℕ):ℂ)+3))) + a * (c k * sphericalJ (2*k+1) w) =
      w * (e k * sphericalJ (2*k) w) - w * (e (k+1) * sphericalJ (2*(k+1)) w) := by
    intro k w
    have hr := sphSeries_sphericalJ_recurrence (2*k) w
    have h3 : (2*((2*k:ℕ):ℂ)+3) ≠ 0 := by
      have : (0:ℝ) < 2*((2*k:ℕ):ℝ)+3 := by positivity
      have h' : ((2*((2*k:ℕ):ℝ)+3 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast this.ne'
      push_cast at h' ⊢; exact h'
    have hJ : sphericalJ (2*k+1) w = w * (sphericalJ (2*k) w + sphericalJ (2*k+2) w) /
        (2*((2*k:ℕ):ℂ)+3) := by rw [eq_div_iff h3]; linear_combination -hr
    simp only [hc, he, poch_succ]
    rw [hJ, show 2*(k+1) = 2*k+2 by ring]
    have hQk' := hQk k
    have hQ' := hQ k
    push_cast at h3 ⊢
    generalize poch (1-a/2) k = P
    generalize poch (1/2+a/2) k = Q at hQk' ⊢
    generalize hu : (1/2+a/2+(k:ℂ)) = u at hQ' ⊢
    generalize ht : (2*(2*(k:ℂ))+3) = t at h3 ⊢
    field_simp
    subst hu ht
    ring
  have hpar : ∀ m : ℕ, a + m = 0 → iteratedDeriv m
      (fun w => ∑' n, c n * sphericalJ (2*n+1) w - H w) 0 = 0 := by
    intro m hm
    have hodd : ∀ w, (∑' n, c n * sphericalJ (2*n+1) (-w) - H (-w)) =
        (-1) * (∑' n, c n * sphericalJ (2*n+1) w - H w) := by
      intro w
      have h1 : ∑' n, c n * sphericalJ (2*n+1) (-w) = -∑' n, c n * sphericalJ (2*n+1) w := by
        rw [← tsum_neg]; congr 1; funext n
        rw [sphSeries_sphericalJ_neg, pow_succ, pow_mul]; simp
      have h2 : H (-w) = -H w := by
        simp only [hH]; rw [← tsum_neg]; congr 1; funext k
        rw [neg_pow w, pow_succ (-1:ℂ) (2*k), pow_mul]; simp; ring
      rw [h1, h2]; ring
    have hp := sphSeries_iteratedDeriv_parity
      (D := fun w => ∑' n, c n * sphericalJ (2*n+1) w - H w) hodd m
    rcases Nat.even_or_odd m with ⟨r, hr⟩ | ⟨r, hr⟩
    · subst hr
      rw [← two_mul, pow_mul, neg_one_sq, one_pow] at hp
      rw [← two_mul]
      have : (1 - (-1) : ℂ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp hp).resolve_left this
    · exact absurd (by rw [hr] at hm; push_cast at hm; linear_combination hm) (ha r)
  have key := sphSeries_hasSum_of_euler (f := fun k w => c k * sphericalJ (2*k+1) w)
    (f' := fun k w => c k * (((((2*k:ℕ):ℂ)+1) * sphericalJ (2*k) w - (((2*k:ℕ):ℂ)+2) *
      sphericalJ (2*k+2) w) / (2*((2*k:ℕ):ℂ)+3)))
    (g := fun k w => w * (e k * sphericalJ (2*k) w)) (F := H) a
    (fun k w => (sphSeries_hasDerivAt_sphericalJ_succ (2*k) w).const_mul (c k))
    hL
    (fun w => by simpa using (sphSeries_tendsto_coeff_mul_sphericalJ e he_r 0 w).const_mul w)
    (sphSeries_bound_coeff_mul_sphericalJ c hc_r 1)
    hHd (fun w => by
      rw [hHL w]; simp [he, poch_zero, ← sphSeries_mul_sphericalJ_zero])
    hpar z
  -- conclude
  have hG := genSinInt_hasSum ha hz
  have hval : genSinInt a z = z^a * H z := by
    rw [hH, ← tsum_mul_left]
    refine hG.tsum_eq.symm.trans ?_
    exact tsum_congr (fun k => by ring)
  rw [hval]
  convert key.mul_left (z^a) using 1
  funext k; simp only [hc]; ring

/-- genCosInt spherical series. -/
@[dlmf 8.21.E17]
theorem genCosInt_spherical_series {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n : ℂ)) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => z^a*(2*k+1/2 : ℂ)*poch (1/2-a/2) k/poch (a/2) (k+1)*sphericalJ (2*k) z) (genCosInt a z) := by
  obtain ⟨hHd, hHL⟩ := gsSph_cos_part ha
  set H : ℂ → ℂ := fun w => ∑' k : ℕ, (-1 : ℂ)^k*w^(2*k)/((2*k+a)*(2*k).factorial) with hH
  have hQ : ∀ k : ℕ, (a/2+k : ℂ) ≠ 0 := fun k e => ha k (by linear_combination 2*e)
  have hQk : ∀ k : ℕ, poch (a/2) k ≠ 0 := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [poch_succ]; exact mul_ne_zero ih (hQ k)
  set c : ℕ → ℂ := fun k => (2*k+1/2 : ℂ)*poch (1/2-a/2) k/poch (a/2) (k+1) with hc
  set e : ℕ → ℂ := fun k => poch (1/2-a/2) k/poch (a/2) k with he
  clear_value c e
  have hratio := sphSeries_eventually_norm_add_le (1/2-a/2) (a/2)
  have hratio2 := sphSeries_eventually_norm_add_le (1/2-a/2) (a/2+1)
  have he_r : ∀ᶠ k in atTop, ‖e (k+1)‖ ≤ 2 * ‖e k‖ := by
    filter_upwards [hratio] with k hk
    simp only [he, poch_succ]
    rw [mul_div_mul_comm, norm_mul, norm_div]
    have hq := norm_pos_iff.mpr (hQ k)
    rw [mul_comm]
    have hb : ‖(1/2-a/2+k : ℂ)‖/‖(a/2+k : ℂ)‖ ≤ 2 := by rw [div_le_iff₀ hq]; linarith
    exact mul_le_mul_of_nonneg_right (by rw [norm_div]; exact hb) (by positivity)
  have hc_r : ∀ᶠ k in atTop, ‖c (k+1)‖ ≤ 10 * ‖c k‖ := by
    filter_upwards [hratio2] with k hk
    have hq := norm_pos_iff.mpr (hQ (k+1))
    have e1 : c (k+1) = c k * ((2*k+5/2)/(2*k+1/2)) * ((1/2-a/2+k)/(a/2+(k+1:ℕ))) := by
      have h32 : (2*(k:ℂ)+1/2) ≠ 0 := by
        have : (0:ℝ) < 2*k+1/2 := by positivity
        have h' : ((2*k+1/2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast this.ne'
        push_cast at h'; exact h'
      have hQ1 : (a/2+((k:ℂ)+1)) ≠ 0 := by have := hQ (k+1); push_cast at this; exact this
      have hQ0 := hQ k
      simp only [hc, poch_succ]
      push_cast
      generalize poch (1/2-a/2) k = P
      have hQk' := hQk k
      generalize poch (a/2) k = Q at hQk' ⊢
      generalize (a/2+(k:ℂ)) = u at hQ0 ⊢
      generalize (a/2+((k:ℂ)+1)) = v at hQ1 ⊢
      generalize (2*(k:ℂ)+1/2) = t at h32 ⊢
      field_simp
      ring
    rw [e1, norm_mul, norm_mul, norm_div, norm_div]
    have h1 : ‖(2*k+5/2 : ℂ)‖ ≤ 5 * ‖(2*k+1/2 : ℂ)‖ := by
      rw [show (2*k+5/2 : ℂ) = ((2*k+5/2 : ℝ) : ℂ) by push_cast; ring,
        show (2*k+1/2 : ℂ) = ((2*k+1/2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (by positivity)]
      linarith
    have h2 : ‖(1/2-a/2+k : ℂ)‖ ≤ 2 * ‖(a/2+(k+1:ℕ) : ℂ)‖ := by
      push_cast; rw [show (a/2+((k:ℂ)+1)) = a/2+1+(k:ℂ) by ring]; exact hk
    have hp1 : 0 < ‖(2*k+1/2 : ℂ)‖ := by
      rw [show (2*k+1/2 : ℂ) = ((2*k+1/2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      positivity
    have hq' : 0 < ‖(a/2+(k+1:ℕ) : ℂ)‖ := by push_cast at hq ⊢; exact hq
    calc ‖c k‖ * (‖(2*k+5/2 : ℂ)‖/‖(2*k+1/2 : ℂ)‖) *
          (‖(1/2-a/2+k : ℂ)‖/‖(a/2+(k+1:ℕ) : ℂ)‖) ≤ ‖c k‖ * 5 * 2 := by
          gcongr
          · rw [div_le_iff₀ hp1]; linarith
          · rw [div_le_iff₀ hq']; linarith
      _ = 10 * ‖c k‖ := by ring
  set f' : ℕ → ℂ → ℂ := fun k w => c k * deriv (sphericalJ (2*k)) w with hf'
  have hdj0 := sphSeries_hasDerivAt_sphericalJ_zero
  have hdj : ∀ k w, HasDerivAt (sphericalJ (2*k)) (deriv (sphericalJ (2*k)) w) w := by
    intro k w
    rcases k with _ | k
    · exact (hdj0 w).differentiableAt.hasDerivAt
    · rw [show 2*(k+1) = (2*k+1)+1 by ring]
      exact (sphSeries_hasDerivAt_sphericalJ_succ (2*k+1) w).differentiableAt.hasDerivAt
  have hL : ∀ k w, w * f' k w + a * (c k * sphericalJ (2*k) w) =
      (if k = 0 then cos w else w * (e k * sphericalJ (2*k-1) w)) -
      (if k+1 = 0 then cos w else w * (e (k+1) * sphericalJ (2*(k+1)-1) w)) := by
    intro k w
    simp only [hf']
    rcases k with _ | k
    · rw [(hdj0 w).deriv]
      simp only [ite_true, one_ne_zero, ite_false,
        mul_zero, zero_add, show 2*(0+1)-1 = 1 by rfl]
      rw [← sphSeries_sphericalJ_zero_sub]
      have hQ0 := hQ 0
      have ha0 : a ≠ 0 := by have := ha 0; simpa using this
      simp only [hc, he, poch_succ, poch_zero]
      push_cast
      field_simp
      have hinv := mul_inv_cancel₀ ha0
      linear_combination (sphericalJ 0 w - w * sphericalJ 1 w) * hinv
    · rw [show 2*(k+1) = (2*k+1)+1 by ring, (sphSeries_hasDerivAt_sphericalJ_succ (2*k+1) w).deriv]
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
      rw [show 2*k+1+1-1 = 2*k+1 by omega, show 2*(k+1+1)-1 = 2*k+1+2 by omega]
      have hr := sphSeries_sphericalJ_recurrence (2*k+1) w
      have h3 : (2*((2*k+1:ℕ):ℂ)+3) ≠ 0 := by
        have : (0:ℝ) < 2*((2*k+1:ℕ):ℝ)+3 := by positivity
        have h' : ((2*((2*k+1:ℕ):ℝ)+3 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast this.ne'
        push_cast at h' ⊢; exact h'
      have hJ : sphericalJ (2*k+1+1) w = w * (sphericalJ (2*k+1) w + sphericalJ (2*k+1+2) w) /
          (2*((2*k+1:ℕ):ℂ)+3) := by rw [eq_div_iff h3]; linear_combination -hr
      simp only [hc, he, poch_succ]
      rw [hJ]
      have hQk' := hQk k
      have hQ' := hQ k
      have hQ'' : (a/2+((k:ℂ)+1)) ≠ 0 := by have := hQ (k+1); push_cast at this; exact this
      push_cast at h3 ⊢
      generalize poch (1/2-a/2) k = P
      generalize poch (a/2) k = Q at hQk' ⊢
      generalize hu : (a/2+(k:ℂ)) = u at hQ' ⊢
      generalize hv : (a/2+((k:ℂ)+1)) = v at hQ'' ⊢
      generalize ht : (2*(2*(k:ℂ)+1)+3) = t at h3 ⊢
      field_simp
      subst hu hv ht
      ring
  have hpar : ∀ m : ℕ, a + m = 0 → iteratedDeriv m
      (fun w => ∑' n, c n * sphericalJ (2*n) w - H w) 0 = 0 := by
    intro m hm
    have hev : ∀ w, (∑' n, c n * sphericalJ (2*n) (-w) - H (-w)) =
        1 * (∑' n, c n * sphericalJ (2*n) w - H w) := by
      intro w
      have h1 : ∑' n, c n * sphericalJ (2*n) (-w) = ∑' n, c n * sphericalJ (2*n) w := by
        congr 1; funext n
        rw [sphSeries_sphericalJ_neg, pow_mul]; simp
      have h2 : H (-w) = H w := by
        simp only [hH]; congr 1; funext k
        rw [neg_pow w, pow_mul (-1:ℂ)]; simp
      rw [h1, h2]; ring
    have hp := sphSeries_iteratedDeriv_parity
      (D := fun w => ∑' n, c n * sphericalJ (2*n) w - H w) hev m
    rcases Nat.even_or_odd m with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact absurd (by rw [hr] at hm; push_cast at hm; linear_combination hm) (ha r)
    · subst hr
      rw [pow_succ, pow_mul, neg_one_sq, one_pow] at hp
      have : ((1:ℂ) * (-1) - 1) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp hp).resolve_left this
  have hg : ∀ w, Tendsto (fun k => if k = 0 then cos w else
      w * (e k * sphericalJ (2*k-1) w)) atTop (𝓝 0) := by
    intro w
    rw [← tendsto_add_atTop_iff_nat 1]
    have he_r' : ∀ᶠ k in atTop, ‖e (k+1+1)‖ ≤ 2 * ‖e (k+1)‖ :=
      (tendsto_add_atTop_nat 1).eventually he_r
    have := (sphSeries_tendsto_coeff_mul_sphericalJ (fun k => e (k+1)) he_r' 1 w).const_mul w
    simp only [mul_zero] at this
    refine this.congr fun k => ?_
    simp [show 2*(k+1)-1 = 2*k+1 by omega]
  have key := sphSeries_hasSum_of_euler (f := fun k w => c k * sphericalJ (2*k) w)
    (f' := f') (F := H) a
    (fun k w => (hdj k w).const_mul (c k)) hL hg
    (sphSeries_bound_coeff_mul_sphericalJ c hc_r 0)
    hHd (fun w => by rw [hHL w]; simp)
    hpar z
  have hG := genCosInt_hasSum ha hz
  have hval : genCosInt a z = z^a * H z := by
    rw [hH, ← tsum_mul_left]
    refine hG.tsum_eq.symm.trans ?_
    exact tsum_congr (fun k => by ring)
  rw [hval]
  convert key.mul_left (z^a) using 1
  funext k; simp only [hc]; ring

/-- Generalized auxiliary f. -/
@[dlmf 8.21.E18]
def genTrigAuxF (a z : ℂ) : ℂ :=
  genSinIntTail a z*cos z-genCosIntTail a z*sin z

/-- Generalized auxiliary g. -/
@[dlmf 8.21.E19]
def genTrigAuxG (a z : ℂ) : ℂ :=
  genSinIntTail a z*sin z+genCosIntTail a z*cos z

/-- genSinIntTail aux. -/
@[dlmf 8.21.E20]
theorem genSinIntTail_aux (a z : ℂ) :
    genSinIntTail a z=genTrigAuxF a z*cos z+genTrigAuxG a z*sin z := by
  unfold genTrigAuxF genTrigAuxG
  have h := Complex.sin_sq_add_cos_sq z
  linear_combination -genSinIntTail a z*h

/-- genCosIntTail aux. -/
@[dlmf 8.21.E21]
theorem genCosIntTail_aux (a z : ℂ) :
    genCosIntTail a z = -genTrigAuxF a z*sin z+genTrigAuxG a z*cos z := by
  unfold genTrigAuxF genTrigAuxG
  have h := Complex.sin_sq_add_cos_sq z
  linear_combination -genCosIntTail a z*h

/-- genTrigAuxF oscillatory integral. -/
@[dlmf 8.21.E22]
theorem genTrigAuxF_oscillatory_integral {a : ℂ} (ha : a.re < 1) {z : ℂ} (hz : z ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => sin t*(t+z)^(a-1)) 0 (genTrigAuxF a z) := by
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun t : ℝ => -cos z*genSinIntTail a (z+t)+sin z*genCosIntTail a (z+t))
      (sin t*(t+z)^(a-1)) t := by
    intro t ht
    obtain ⟨hS, hC⟩ := hasDerivAt_genTrigTail a (add_ofReal_mem_slitPlane hz ht)
    refine (hasDerivAt_comp_add_ofReal (g := fun w => -cos z*genSinIntTail a w+sin z*genCosIntTail a w)
      ((hS.const_mul _).add (hC.const_mul _))).congr_deriv ?_
    have hs : sin (t:ℂ) = sin (z+t)*cos z-cos (z+t)*sin z := by rw [← Complex.sin_sub]; ring_nf
    rw [hs, add_comm (t:ℂ) z]
    ring
  have hc : ContinuousOn (fun t : ℝ => sin t*(t+z)^(a-1)) (Ici 0) := by
    refine ContinuousOn.mul (by fun_prop) (fun t ht => ?_)
    have := add_ofReal_mem_slitPlane hz ht
    rw [add_comm] at this
    exact ((continuous_ofReal.continuousAt.add continuousAt_const).cpow continuousAt_const
      this).continuousWithinAt
  have hl : Tendsto (fun t : ℝ => -cos z*genSinIntTail a (z+t)+sin z*genCosIntTail a (z+t)) atTop (𝓝 0) := by
    obtain ⟨h1, h2⟩ := tendsto_genTrigTail_add_ofReal ha z
    simpa using (h1.const_mul (-cos z)).add (h2.const_mul (sin z))
  have h := hasIntegralAtTop_of_hasDerivAt_of_tendsto hd hc hl
  convert h using 1
  simp [genTrigAuxF]; ring

/-- genTrigAuxG oscillatory integral. -/
@[dlmf 8.21.E23]
theorem genTrigAuxG_oscillatory_integral {a : ℂ} (ha : a.re < 1) {z : ℂ} (hz : z ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => cos t*(t+z)^(a-1)) 0 (genTrigAuxG a z) := by
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun t : ℝ => -sin z*genSinIntTail a (z+t)-cos z*genCosIntTail a (z+t))
      (cos t*(t+z)^(a-1)) t := by
    intro t ht
    obtain ⟨hS, hC⟩ := hasDerivAt_genTrigTail a (add_ofReal_mem_slitPlane hz ht)
    refine (hasDerivAt_comp_add_ofReal (g := fun w => -sin z*genSinIntTail a w-cos z*genCosIntTail a w)
      ((hS.const_mul _).sub (hC.const_mul _))).congr_deriv ?_
    have hs : cos (t:ℂ) = cos (z+t)*cos z+sin (z+t)*sin z := by rw [← Complex.cos_sub]; ring_nf
    rw [hs, add_comm (t:ℂ) z]
    ring
  have hc : ContinuousOn (fun t : ℝ => cos t*(t+z)^(a-1)) (Ici 0) := by
    refine ContinuousOn.mul (by fun_prop) (fun t ht => ?_)
    have := add_ofReal_mem_slitPlane hz ht
    rw [add_comm] at this
    exact ((continuous_ofReal.continuousAt.add continuousAt_const).cpow continuousAt_const
      this).continuousWithinAt
  have hl : Tendsto (fun t : ℝ => -sin z*genSinIntTail a (z+t)-cos z*genCosIntTail a (z+t)) atTop (𝓝 0) := by
    obtain ⟨h1, h2⟩ := tendsto_genTrigTail_add_ofReal ha z
    simpa using (h1.const_mul (-sin z)).sub (h2.const_mul (cos z))
  have h := hasIntegralAtTop_of_hasDerivAt_of_tendsto hd hc hl
  convert h using 1
  simp [genTrigAuxG]; ring

theorem incG_unit_cases {c : ℂ} (hc : c = I ∨ c = -I) : c.re = 0 ∧ (c.im = 1 ∨ c.im = -1) := by
  rcases hc with rfl | rfl <;> simp

/-- `(1+t)^k e^{-bt}` is integrable on `(0,∞)` for `b > 0`. -/
theorem incG_integrableOn_one_add_rpow_mul_exp {k b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => (1+t)^k * Real.exp (-b*t)) (Ioi 0) := by
  refine integrable_of_isBigO_exp_neg (b := b/2) (by positivity) ?_ ?_
  · intro t ht
    have ht0 : (0:ℝ) < 1+t := by have : (0:ℝ) ≤ t := ht; linarith
    exact ((Real.continuousAt_rpow_const _ _ (Or.inl ht0.ne')).comp
      (continuousAt_const.add continuousAt_id) |>.mul
      (Real.continuous_exp.continuousAt.comp (continuousAt_const.mul continuousAt_id))).continuousWithinAt
  · have h1 := (isLittleO_rpow_exp_pos_mul_atTop k (b := b/2) (by positivity)).isBigO.comp_tendsto
      (tendsto_atTop_add_const_left atTop 1 tendsto_id)
    have h := h1.mul (isBigO_refl (fun t : ℝ => Real.exp (-b*t)) atTop)
    have h2 : (fun t : ℝ => Real.exp (b/2*(1+t)) * Real.exp (-b*t)) =O[atTop]
        fun t => Real.exp (-(b/2)*t) := by
      refine (isBigO_const_mul_self (Real.exp (b/2)) _ _).congr' (Eventually.of_forall fun t => ?_)
        (Eventually.of_forall fun t => rfl)
      simp only; rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    exact (h.trans h2).congr' (Eventually.of_forall fun t => by simp [id]) (Eventually.of_forall fun _ => rfl)

theorem incG_norm_one_add_cpow_le {c : ℂ} (hc : c = I ∨ c = -I) (a : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ‖(1+c*t)^(a-1)‖ ≤ (1+t)^|a.re-1| * Real.exp (π/2*|a.im|) := by
  obtain ⟨hre, him⟩ := incG_unit_cases hc
  have hu0 : (1+c*t) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hre] at this
  have hre1 : (1+c*(t:ℂ)).re = 1 := by simp [hre]
  rw [norm_cpow_of_ne_zero hu0]
  have hn1 : 1 ≤ ‖1+c*(t:ℂ)‖ := by
    have := Complex.abs_re_le_norm (1+c*(t:ℂ)); rw [hre1] at this; simpa using this
  have hn2 : ‖1+c*(t:ℂ)‖ ≤ 1+t := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
    have : ‖c‖ = 1 := by rcases hc with rfl | rfl <;> simp
    rw [this, one_mul]
  have harg : |arg (1+c*(t:ℂ))| ≤ π/2 := abs_arg_le_pi_div_two_iff.mpr (by rw [hre1]; norm_num)
  have hA : ‖1+c*(t:ℂ)‖ ^ (a-1).re ≤ (1+t)^|a.re-1| := by
    rw [show (a-1).re = a.re - 1 by simp]
    rcases le_or_gt 0 (a.re-1) with h | h
    · rw [abs_of_nonneg h]; exact Real.rpow_le_rpow (by linarith) hn2 h
    · calc ‖1+c*(t:ℂ)‖ ^ (a.re-1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 h.le
        _ ≤ (1+t)^|a.re-1| := Real.one_le_rpow (by linarith) (abs_nonneg _)
  have hB : 1 / Real.exp (arg (1+c*(t:ℂ)) * (a-1).im) ≤ Real.exp (π/2*|a.im|) := by
    rw [one_div, ← Real.exp_neg, Real.exp_le_exp, show (a-1).im = a.im by simp]
    have := abs_mul (arg (1+c*(t:ℂ))) a.im
    have h2 : |arg (1+c*(t:ℂ))| * |a.im| ≤ π/2 * |a.im| := mul_le_mul_of_nonneg_right harg (abs_nonneg _)
    nlinarith [neg_abs_le (arg (1+c*(t:ℂ)) * a.im)]
  calc ‖1+c*(t:ℂ)‖ ^ (a-1).re / Real.exp (arg (1+c*(t:ℂ)) * (a-1).im)
      = ‖1+c*(t:ℂ)‖ ^ (a-1).re * (1 / Real.exp (arg (1+c*(t:ℂ)) * (a-1).im)) := by ring
    _ ≤ (1+t)^|a.re-1| * Real.exp (π/2*|a.im|) :=
        mul_le_mul hA hB (by positivity) (by positivity)

theorem incG_one_add_mul_mem_slitPlane {c : ℂ} (hc : c = I ∨ c = -I) (t : ℝ) :
    1 + c*t ∈ slitPlane := Or.inl (by obtain ⟨hre, _⟩ := incG_unit_cases hc; simp [hre])

theorem incG_integrableOn_trigLap {c : ℂ} (hc : c = I ∨ c = -I) (a : ℂ) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => (1+c*t)^(a-1)*exp (-z*t)) (Ioi 0) := by
  refine Integrable.mono' ((incG_integrableOn_one_add_rpow_mul_exp (k := |a.re-1|) hz).mul_const
    (Real.exp (π/2*|a.im|))) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun t _ => ContinuousAt.continuousWithinAt ?_) measurableSet_Ioi
    refine ContinuousAt.mul ?_ (by fun_prop)
    exact (continuousAt_const.add (continuousAt_const.mul continuous_ofReal.continuousAt)).cpow
      continuousAt_const (incG_one_add_mul_mem_slitPlane hc t)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0:ℝ) ≤ t := le_of_lt ht
    rw [norm_mul, Complex.norm_exp]
    have hre : (-z*(t:ℂ)).re = -z.re*t := by simp
    rw [hre]
    calc ‖(1+c*(t:ℂ))^(a-1)‖ * Real.exp (-z.re*t)
        ≤ ((1+t)^|a.re-1| * Real.exp (π/2*|a.im|)) * Real.exp (-z.re*t) :=
          mul_le_mul_of_nonneg_right (incG_norm_one_add_cpow_le hc a ht0) (Real.exp_pos _).le
      _ = (1+t)^|a.re-1| * Real.exp (-z.re*t) * Real.exp (π/2*|a.im|) := by ring

theorem incG_ray_mem_slitPlane {c : ℂ} (hc : c = I ∨ c = -I) {z : ℂ} (hz : 0 < z.re) {t : ℝ}
    (ht : 0 ≤ t) : z*(t-c) ∈ slitPlane := by
  obtain ⟨hre, him⟩ := incG_unit_cases hc
  rw [mem_slitPlane_iff]
  by_cases h : (z*((t:ℂ)-c)).im = 0
  · left
    simp only [mul_im, mul_re, sub_re, sub_im, ofReal_re, ofReal_im, hre] at h ⊢
    rcases him with h1 | h1 <;> rw [h1] at h ⊢ <;>
    · rcases ht.eq_or_lt with h0 | h0
      · subst h0; nlinarith
      · nlinarith [mul_pos hz h0, sq_nonneg t]
  · exact Or.inr h

/-- Splitting the power along the ray. -/
theorem incG_ray_cpow {c : ℂ} (hc : c = I ∨ c = -I) (a : ℂ) {z : ℂ} (hz : 0 < z.re) {t : ℝ}
    (ht : 0 ≤ t) :
    (z*(t-c))^(a-1) = z^(a-1)*((-c)^(a-1)*(1+c*t)^(a-1)) := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  obtain ⟨hre, him⟩ := incG_unit_cases hc
  have hc0 : c ≠ 0 := by intro h; rw [h] at him; simp at him
  have hw0 : ((t:ℂ)-c) ≠ 0 := by intro h; have := congrArg Complex.im h; simp at this; rcases him with h1 | h1 <;> linarith
  have hv0 : (1+c*(t:ℂ)) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hre] at this
  have hfac : ((t:ℂ)-c) = (-c)*(1+c*t) := by
    have : c*c = -1 := by rcases hc with rfl | rfl <;> simp
    linear_combination (t:ℂ) * this
  have hzarg : |arg z| < π/2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  have hwarg : |arg ((t:ℂ)-c)| ≤ π/2 := abs_arg_le_pi_div_two_iff.mpr (by simp [hre, ht])
  have hl1 : log (z*((t:ℂ)-c)) = log z + log ((t:ℂ)-c) := by
    refine Complex.log_mul hz0 hw0 ?_
    constructor <;> [skip; skip] <;> rw [abs_lt] at hzarg <;> rw [abs_le] at hwarg <;> linarith
  have hl2 : log ((-c)*(1+c*(t:ℂ))) = log (-c) + log (1+c*(t:ℂ)) := by
    refine Complex.log_mul (neg_ne_zero.mpr hc0) hv0 ?_
    have hv : |arg (1+c*(t:ℂ))| ≤ π/2 := abs_arg_le_pi_div_two_iff.mpr (by simp [hre])
    rcases hc with rfl | rfl
    · have : 0 ≤ arg (1+I*(t:ℂ)) := arg_nonneg_iff.mpr (by simp [ht])
      simp only [arg_neg_I]; rw [abs_le] at hv; constructor <;> linarith [Real.pi_pos]
    · have : arg (1+(-I)*(t:ℂ)) ≤ 0 := by
        rcases ht.eq_or_lt with h0 | h0
        · subst h0; simp
        · exact (arg_neg_iff.mpr (by simp [h0])).le
      simp only [neg_neg, arg_I]; rw [abs_le] at hv; constructor <;> linarith [Real.pi_pos]
  rw [cpow_def_of_ne_zero (mul_ne_zero hz0 hw0), hl1, cpow_def_of_ne_zero hz0,
    hfac, hl2, cpow_def_of_ne_zero (neg_ne_zero.mpr hc0), cpow_def_of_ne_zero hv0,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1; ring

/-- `Γ(a, z(t-c)) → 0` along the ray. -/
theorem incG_tendsto_upperIncGamma_ray (c : ℂ) (a : ℂ) {z : ℂ}
    (hz : 0 < z.re) :
    Tendsto (fun t : ℝ => upperIncGamma a (z*(t-c))) atTop (𝓝 0) := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hn : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
  set u : ℂ := z/‖z‖
  have hu : ‖u‖ = 1 := by simp [u, hn.ne']
  have hure : 0 < u.re := by simp [u]; exact div_pos hz hn
  have hray := tendsto_ray_sectorAtTop (-c*‖z‖) u hu (δ := u.re/2) (by positivity) (by linarith)
  have hs : Tendsto (fun t : ℝ => t*‖z‖) atTop atTop := tendsto_id.atTop_mul_const hn
  have h := (tendsto_exp_neg_mul_kummerU_sectorAtTop (1-a) (1-a) (δ := u.re/2) (by positivity)).comp
    (hray.comp hs)
  refine h.congr fun t => ?_
  simp only [Function.comp_apply, upperIncGamma]
  have hn' : ((‖z‖:ℝ):ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  congr 2 <;> · simp only [u]; push_cast; field_simp; ring

/-- Rotating the upper Gamma integral onto the ray `z(t - c)`, `c = ±i`. -/
theorem incG_upperIncGamma_rot {c : ℂ} (hc : c = I ∨ c = -I) (a : ℂ) {z : ℂ} (hz : 0 < z.re) :
    upperIncGamma a (-c*z) = z^a*(-c)^(a-1)*exp (c*z) *
      ∫ t : ℝ in Ioi 0, (1+c*t)^(a-1)*exp (-z*t) := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  set F : ℝ → ℂ := fun t => upperIncGamma a (z*(t-c))
  set F' : ℝ → ℂ := fun t => -(z*(t-c))^(a-1)*exp (-(z*(t-c)))*z
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt F (F' t) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => z*((t:ℂ)-c)) z t := by
      simpa using ((hasDerivAt_id t).ofReal_comp.sub_const c).const_mul z
    exact (hasDerivAt_upperIncGamma_complex a (incG_ray_mem_slitPlane hc hz ht)).comp t h1
  have hF' : ∀ t : ℝ, 0 ≤ t → F' t = -(z^a*(-c)^(a-1)*exp (c*z)) * ((1+c*t)^(a-1)*exp (-z*t)) := by
    intro t ht
    simp only [F']
    rw [incG_ray_cpow hc a hz ht, show -(z*((t:ℂ)-c)) = c*z + -z*t by ring, Complex.exp_add,
      cpow_sub _ _ hz0, cpow_one]
    field_simp
  have hint : IntegrableOn F' (Ioi 0) := by
    have h0 : IntegrableOn (fun t : ℝ => -(z^a*(-c)^(a-1)*exp (c*z)) * ((1+c*t)^(a-1)*exp (-z*t)))
        (Ioi 0) := (incG_integrableOn_trigLap hc a hz).const_mul _
    exact h0.congr_fun (fun t ht => (hF' t (le_of_lt ht)).symm) measurableSet_Ioi
  have hcont : ContinuousWithinAt F (Ici 0) 0 := (hd 0 le_rfl).continuousAt.continuousWithinAt
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont (fun t ht => hd t (le_of_lt ht)) hint
    (incG_tendsto_upperIncGamma_ray c a hz)
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => hF' t (le_of_lt ht)),
    integral_const_mul] at h
  simp only [F, ofReal_zero, zero_sub] at h
  rw [show z*(-c) = -c*z by ring] at h
  linear_combination h

/-- The two rotated upper Gamma values in the tails, as Laplace integrals. -/
theorem incG_trigTail_rot (a : ℂ) {z : ℂ} (hz : 0 < z.re) :
    genSinIntTail a z = (exp (π*I*a/2)*upperIncGamma a (-I*z) -
        exp (-π*I*a/2)*upperIncGamma a (I*z))/(2*I) ∧
    genCosIntTail a z = (exp (π*I*a/2)*upperIncGamma a (-I*z) +
        exp (-π*I*a/2)*upperIncGamma a (I*z))/2 := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have harg : |arg z| < π/2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  rw [abs_lt] at harg
  have h1 : upperIncGammaOnLog a (log z - π*I/2) = upperIncGamma a (-I*z) := by
    rw [upperIncGammaOnLog_eq_upperIncGamma]
    · rw [sub_eq_add_neg, Complex.exp_add, Complex.exp_log hz0]
      congr 1
      rw [show -(↑π*I/2) = ((-(π/2):ℝ):ℂ)*I by push_cast; ring, Complex.exp_mul_I]
      simp; ring
    · simp [log_im]; linarith
    · simp [log_im]; linarith
  have h2 : upperIncGammaOnLog a (log z + π*I/2) = upperIncGamma a (I*z) := by
    rw [upperIncGammaOnLog_eq_upperIncGamma]
    · rw [Complex.exp_add, Complex.exp_log hz0]
      congr 1
      rw [show (↑π*I/2) = (((π/2):ℝ):ℂ)*I by push_cast; ring, Complex.exp_mul_I]
      simp; ring
    · simp [log_im]; linarith
    · simp [log_im]; linarith
  constructor
  · rw [genSinIntTail, genSinIntTailOnLog, h1, h2]
  · rw [genCosIntTail, genCosIntTailOnLog, h1, h2]

theorem incG_negI_cpow (a : ℂ) : (-I)^(a-1) = exp (-π*I*a/2)*I := by
  rw [cpow_sub _ _ (neg_ne_zero.mpr I_ne_zero), cpow_one, cpow_def_of_ne_zero (neg_ne_zero.mpr I_ne_zero),
    log_neg_I]
  field_simp
  ring_nf
  rw [I_sq]

theorem incG_I_cpow (a : ℂ) : I^(a-1) = -(exp (π*I*a/2)*I) := by
  rw [cpow_sub _ _ I_ne_zero, cpow_one, cpow_def_of_ne_zero I_ne_zero, log_I]
  field_simp
  ring_nf
  rw [I_sq]; ring_nf

lemma incG_genTrigAux_laplace (a : ℂ) {z : ℂ} (hz : 0 < z.re) :
    genTrigAuxF a z=z^a/2*(∫ t : ℝ in Ioi 0, ((1+I*t)^(a-1)+(1-I*t)^(a-1))*exp (-z*t)) ∧
    genTrigAuxG a z=z^a/(2*I)*(∫ t : ℝ in Ioi 0, ((1-I*t)^(a-1)-(1+I*t)^(a-1))*exp (-z*t)) := by
  obtain ⟨hS, hC⟩ := incG_trigTail_rot a hz
  have K1 := incG_upperIncGamma_rot (c := I) (Or.inl rfl) a hz
  have K2 := incG_upperIncGamma_rot (c := -I) (Or.inr rfl) a hz
  rw [neg_neg] at K2
  have hJ2 : (∫ t : ℝ in Ioi 0, (1+(-I)*t)^(a-1)*exp (-z*t)) =
      ∫ t : ℝ in Ioi 0, (1-I*t)^(a-1)*exp (-z*t) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [neg_mul, ← sub_eq_add_neg]
  rw [hJ2, incG_I_cpow] at K2
  rw [incG_negI_cpow] at K1
  set Jp := ∫ t : ℝ in Ioi 0, (1+I*t)^(a-1)*exp (-z*t)
  set Jm := ∫ t : ℝ in Ioi 0, (1-I*t)^(a-1)*exp (-z*t)
  have hip := incG_integrableOn_trigLap (c := I) (Or.inl rfl) a hz
  have him : IntegrableOn (fun t : ℝ => (1-I*t)^(a-1)*exp (-z*t)) (Ioi 0) := by
    have := incG_integrableOn_trigLap (c := -I) (Or.inr rfl) a hz
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only; rw [neg_mul, ← sub_eq_add_neg]
  have hsum : (∫ t : ℝ in Ioi 0, ((1+I*t)^(a-1)+(1-I*t)^(a-1))*exp (-z*t)) = Jp + Jm := by
    rw [← integral_add hip him]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  have hdiff : (∫ t : ℝ in Ioi 0, ((1-I*t)^(a-1)-(1+I*t)^(a-1))*exp (-z*t)) = Jm - Jp := by
    rw [← integral_sub him hip]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  rw [hsum, hdiff]
  have e1 : exp (-π*I*a/2) = (exp (π*I*a/2))⁻¹ := by rw [← Complex.exp_neg]; ring_nf
  have e2 : exp (-I*z) = (exp (I*z))⁻¹ := by rw [← Complex.exp_neg]; ring_nf
  have hcos' : cos z = (exp (I*z) + (exp (I*z))⁻¹)/2 := by
    have := two_cos z
    rw [show z*I = I*z by ring, show -z*I = -(I*z) by ring, Complex.exp_neg] at this
    linear_combination this/2
  have hsin' : sin z = ((exp (I*z))⁻¹ - exp (I*z))*I/2 := by
    have := two_sin z
    rw [show z*I = I*z by ring, show -z*I = -(I*z) by ring, Complex.exp_neg] at this
    linear_combination this/2
  have hE0 := Complex.exp_ne_zero (π*I*a/2)
  have hW0 := Complex.exp_ne_zero (I*z)
  constructor
  · rw [genTrigAuxF, hS, hC, K1, K2, hcos', hsin', e1, e2]
    field_simp
    ring_nf; rw [I_sq]; ring
  · rw [genTrigAuxG, hS, hC, K1, K2, hcos', hsin', e1, e2]
    field_simp
    ring_nf; rw [I_sq]; ring

/-- genTrigAuxF laplace integral. -/
@[dlmf 8.21.E24]
theorem genTrigAuxF_laplace_integral (a : ℂ) {z : ℂ} (hz : 0 < z.re) :
    genTrigAuxF a z=z^a/2*(∫ t : ℝ in Ioi 0, ((1+I*t)^(a-1)+(1-I*t)^(a-1))*exp (-z*t)) :=
  (incG_genTrigAux_laplace a hz).1

/-- genTrigAuxG laplace integral. -/
@[dlmf 8.21.E25]
theorem genTrigAuxG_laplace_integral (a : ℂ) {z : ℂ} (hz : 0 < z.re) :
    genTrigAuxG a z=z^a/(2*I)*(∫ t : ℝ in Ioi 0, ((1-I*t)^(a-1)-(1+I*t)^(a-1))*exp (-z*t)) :=
  (incG_genTrigAux_laplace a hz).2

/-- `e^{e^w} Γ(a, e^w) ~ ∑ (-1)^k (1-a)_k e^{(a-1-k) w}` on the logarithmic sector
`|im w| ≤ 3π/2 - δ` (DLMF 8.11.2 continued to the logarithmic plane). -/
theorem upperIncGammaOnLog_logSector_asymptotic (a : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 3*π/2) :
    HasAsymptoticExpansion (logSector (3*π/2-δ)) (fun (k : ℕ) w => exp ((a-1-k)*w))
      (fun k => (-1 : ℂ)^k*poch (1-a) k) (fun w => exp (exp w) * upperIncGammaOnLog a w) := by
  have h := (genExpIntE_log_sector_asymptotic (1-a) hδ hδ1).mul_left (fun w => exp (a*w + exp w))
  have hφ : (fun (k : ℕ) (w : ℂ) => exp (a*w + exp w) * exp (-exp w-(k+1 : ℂ)*w)) =
      fun (k : ℕ) w => exp ((a-1-k)*w) := by
    funext k w; rw [← Complex.exp_add]; congr 1; ring
  have hf : (fun w => exp (a*w + exp w) • genExpIntEOnLog (1-a) w) =
      fun w => exp (exp w) * upperIncGammaOnLog a w := by
    funext w
    rw [smul_eq_mul, genExpIntEOnLog, show (1:ℂ) - (1 - a) = a by ring, ← mul_assoc,
      ← Complex.exp_add]
    congr 2; ring
  rw [hφ, hf] at h
  exact h

/-- `z ↦ log z + iπ s/2` (`s = ±1`) maps `|arg z| ≤ π - δ` into the logarithmic sector
`|im w| ≤ 3π/2 - δ`, uniformly towards infinity. -/
theorem tendsto_log_add_sector {s : ℝ} (hs : |s| ≤ 1) {δ : ℝ} :
    Tendsto (fun z : ℂ => log z + s*π*I/2) (sector (π-δ)) (logSector (3*π/2-δ)) := by
  unfold sector logSector
  refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr ?_⟩
  · refine (tendsto_comap.mono_left inf_le_left).congr' ?_
    filter_upwards [mem_inf_of_right (mem_principal_self _)] with z hz
    obtain ⟨hz0, -⟩ := hz
    simp only [Function.comp, add_re, log_re]
    simp [Real.exp_log (norm_pos_iff.mpr hz0)]
  · filter_upwards [mem_inf_of_right (mem_principal_self _)] with z hz
    obtain ⟨-, hza⟩ := hz
    show |(log z + s*π*I/2).im| ≤ 3*π/2-δ
    have him : (log z + s*π*I/2).im = arg z + s*π/2 := by simp [log_im]
    rw [him]
    have h1 := abs_le.mp hza
    have h2 := abs_le.mp hs
    rw [abs_le]; constructor <;> nlinarith [Real.pi_pos]

/-- `exp(s π i/2) = s i` for `s = ±1`. -/
theorem exp_sign_mul_pi_div_two_mul_I {s : ℝ} (hs : s = 1 ∨ s = -1) :
    exp ((s : ℂ) * π * I / 2) = s * I := by
  rcases hs with rfl | rfl
  · push_cast; rw [show (1:ℂ) * π * I / 2 = π / 2 * I by ring, exp_pi_div_two_mul_I]; ring
  · push_cast; rw [show (-1:ℂ) * π * I / 2 = -π / 2 * I by ring, exp_neg_pi_div_two_mul_I]; ring

/-- One exponential piece of the generalized auxiliary functions:
`e^{-sπia/2} e^{siz} Γ(a, z e^{sπi/2}) ~ ∑ e^{-s(k+1)πi/2} (-1)^k (1-a)_k z^{a-1-k}` (`s = ±1`)
in the sector `|arg z| ≤ π - δ`. -/
theorem upperIncGamma_rotated_piece_asymptotic (a : ℂ) {s : ℝ} (hs : s = 1 ∨ s = -1) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < π) :
    HasAsymptoticExpansion (sector (π-δ)) (fun (k : ℕ) z => z^(a-1-k))
      (fun k => exp (-((s : ℂ)*(k+1)*π*I/2)) * ((-1 : ℂ)^k*poch (1-a) k))
      (fun z => exp (-((s : ℂ)*π*I*a/2)) * (exp ((s : ℂ)*I*z) *
        upperIncGammaOnLog a (log z + s*π*I/2))) := by
  have hs1 : |s| ≤ 1 := by rcases hs with rfl | rfl <;> norm_num
  have hnz : ∀ᶠ z in sector (π-δ), z ≠ 0 := by
    filter_upwards [mem_inf_of_right (mem_principal_self _)] with z hz
    exact hz.1
  have h1 := (upperIncGammaOnLog_logSector_asymptotic a hδ (by linarith)).comp_tendsto
    (tendsto_log_add_sector hs1 (δ := δ))
  have h2 := h1.smul_scale (ψ := fun (k : ℕ) (z : ℂ) => z^(a-1-k))
    (κ := fun (k : ℕ) => exp ((a-1-k)*((s : ℂ)*π*I/2))) (fun k => by
      filter_upwards [hnz] with z hz0
      rw [cpow_def_of_ne_zero hz0, ← Complex.exp_add]; congr 1; ring)
  have h3 := h2.const_smul (exp (-((s : ℂ)*π*I*a/2)))
  refine (h3.congr' ?_).congr_coeff ?_
  · filter_upwards [hnz] with z hz0
    simp only [Pi.smul_apply, smul_eq_mul, Function.comp]
    rw [Complex.exp_add, Complex.exp_log hz0, exp_sign_mul_pi_div_two_mul_I hs]
    congr 2; ring_nf
  · funext k
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2; ring

/-- `exp(-s(k+1)πi/2) = (-s i)^{k+1}` for `s = ±1`. -/
theorem exp_neg_sign_mul_pi_div_two_mul_I_pow {s : ℝ} (hs : s = 1 ∨ s = -1) (k : ℕ) :
    exp (-((s : ℂ)*(k+1)*π*I/2)) = (-(s : ℂ) * I)^(k+1) := by
  have h := exp_sign_mul_pi_div_two_mul_I (s := -s) (by rcases hs with rfl | rfl <;> norm_num)
  rw [show -((s : ℂ)*(k+1)*π*I/2) = ((k+1 : ℕ) : ℂ) * (((-s : ℝ) : ℂ)*π*I/2) by push_cast; ring,
    Complex.exp_nat_mul, h]
  push_cast; ring

/-- The auxiliary functions in terms of the two exponential pieces. -/
lemma genTrigAux_eq_pieces (a z : ℂ) :
    genTrigAuxF a z = (exp (-(((-1:ℝ) : ℂ)*π*I*a/2)) * (exp (((-1:ℝ) : ℂ)*I*z) *
        upperIncGammaOnLog a (log z + ((-1:ℝ) : ℂ)*π*I/2)) -
      exp (-(((1:ℝ) : ℂ)*π*I*a/2)) * (exp (((1:ℝ) : ℂ)*I*z) *
        upperIncGammaOnLog a (log z + ((1:ℝ) : ℂ)*π*I/2))) / (2*I) ∧
    genTrigAuxG a z = (exp (-(((-1:ℝ) : ℂ)*π*I*a/2)) * (exp (((-1:ℝ) : ℂ)*I*z) *
        upperIncGammaOnLog a (log z + ((-1:ℝ) : ℂ)*π*I/2)) +
      exp (-(((1:ℝ) : ℂ)*π*I*a/2)) * (exp (((1:ℝ) : ℂ)*I*z) *
        upperIncGammaOnLog a (log z + ((1:ℝ) : ℂ)*π*I/2))) / 2 := by
  have e1 : log z + ((-1:ℝ) : ℂ)*π*I/2 = log z - π*I/2 := by push_cast; ring
  have e2 : log z + ((1:ℝ) : ℂ)*π*I/2 = log z + π*I/2 := by push_cast; ring
  have e3 : exp (-(((-1:ℝ) : ℂ)*π*I*a/2)) = exp (π*I*a/2) := by congr 1; push_cast; ring
  have e4 : exp (-(((1:ℝ) : ℂ)*π*I*a/2)) = exp (-π*I*a/2) := by congr 1; push_cast; ring
  have e5 : exp (((-1:ℝ) : ℂ)*I*z) = exp (-z*I) := by congr 1; push_cast; ring
  have e6 : exp (((1:ℝ) : ℂ)*I*z) = exp (z*I) := by congr 1; push_cast; ring
  rw [e1, e2, e3, e4, e5, e6]
  simp only [genTrigAuxF, genTrigAuxG, genSinIntTail, genCosIntTail, genSinIntTailOnLog,
    genCosIntTailOnLog, Complex.cos, Complex.sin]
  set X := upperIncGammaOnLog a (log z - π*I/2)
  set Y := upperIncGammaOnLog a (log z + π*I/2)
  set α := exp (π*I*a/2)
  set β := exp (-π*I*a/2)
  set u := exp (z*I)
  set v := exp (-z*I)
  constructor
  · field_simp
    ring_nf
    rw [I_sq]
    ring
  · field_simp
    ring_nf

/-- genTrigAuxF sector asymptotic. -/
@[dlmf 8.21.E26]
theorem genTrigAuxF_sector_asymptotic (a : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < π) :
    HasAsymptoticExpansion (sector (π-δ)) (fun k z => z^(a-1-2*k-0)) (fun k => (-1 : ℂ)^k*poch (1-a) (2*k+0)) (genTrigAuxF a) := by
  have hm := upperIncGamma_rotated_piece_asymptotic a (s := -1) (Or.inr rfl) hδ hδ1
  have hp := upperIncGamma_rotated_piece_asymptotic a (s := 1) (Or.inl rfl) hδ hδ1
  have h := (hm.sub hp).const_smul (1 / (2 * I))
  have hf : ((1 / (2 * I)) • ((fun z => exp (-(((-1:ℝ) : ℂ)*π*I*a/2)) * (exp (((-1:ℝ) : ℂ)*I*z) *
        upperIncGammaOnLog a (log z + ((-1:ℝ) : ℂ)*π*I/2))) -
      (fun z => exp (-(((1:ℝ) : ℂ)*π*I*a/2)) * (exp (((1:ℝ) : ℂ)*I*z) *
        upperIncGammaOnLog a (log z + ((1:ℝ) : ℂ)*π*I/2))))) = genTrigAuxF a := by
    funext z
    rw [(genTrigAux_eq_pieces a z).1]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [hf] at h
  have he := h.even (fun n => by
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [exp_neg_sign_mul_pi_div_two_mul_I_pow (Or.inr rfl),
      exp_neg_sign_mul_pi_div_two_mul_I_pow (Or.inl rfl)]
    push_cast
    rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring, pow_mul, pow_mul]
    simp)
  refine (he.congr_scale fun n => Eventually.of_forall fun z => ?_).congr_coeff ?_
  · simp only
    congr 1; push_cast; ring
  · funext n
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, add_zero]
    rw [exp_neg_sign_mul_pi_div_two_mul_I_pow (Or.inr rfl),
      exp_neg_sign_mul_pi_div_two_mul_I_pow (Or.inl rfl)]
    push_cast
    have h1 : (-(-1:ℂ) * I)^(2*n+1) = (-1)^n * I := by rw [pow_succ, pow_mul]; simp
    have h2 : (-(1:ℂ) * I)^(2*n+1) = -((-1)^n * I) := by rw [pow_succ, pow_mul]; simp
    rw [h1, h2, pow_mul (-1:ℂ) 2 n]
    field_simp
    ring

/-- genTrigAuxG sector asymptotic. -/
@[dlmf 8.21.E27]
theorem genTrigAuxG_sector_asymptotic (a : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < π) :
    HasAsymptoticExpansion (sector (π-δ)) (fun k z => z^(a-1-2*k-1)) (fun k => (-1 : ℂ)^k*poch (1-a) (2*k+1)) (genTrigAuxG a) := by
  have hm := upperIncGamma_rotated_piece_asymptotic a (s := -1) (Or.inr rfl) hδ hδ1
  have hp := upperIncGamma_rotated_piece_asymptotic a (s := 1) (Or.inl rfl) hδ hδ1
  have h := (hm.add hp).const_smul (1 / 2 : ℂ)
  have hf : ((1 / 2 : ℂ) • ((fun z => exp (-(((-1:ℝ) : ℂ)*π*I*a/2)) * (exp (((-1:ℝ) : ℂ)*I*z) *
        upperIncGammaOnLog a (log z + ((-1:ℝ) : ℂ)*π*I/2))) +
      (fun z => exp (-(((1:ℝ) : ℂ)*π*I*a/2)) * (exp (((1:ℝ) : ℂ)*I*z) *
        upperIncGammaOnLog a (log z + ((1:ℝ) : ℂ)*π*I/2))))) = genTrigAuxG a := by
    funext z
    rw [(genTrigAux_eq_pieces a z).2]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  rw [hf] at h
  have ho := h.odd (fun n => by
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [exp_neg_sign_mul_pi_div_two_mul_I_pow (Or.inr rfl),
      exp_neg_sign_mul_pi_div_two_mul_I_pow (Or.inl rfl)]
    push_cast
    have h1 : (-(-1:ℂ) * I)^(2*n+1) = (-1)^n * I := by rw [pow_succ, pow_mul]; simp
    have h2 : (-(1:ℂ) * I)^(2*n+1) = -((-1)^n * I) := by rw [pow_succ, pow_mul]; simp
    rw [h1, h2]
    ring)
  refine (ho.congr_scale fun n => Eventually.of_forall fun z => ?_).congr_coeff ?_
  · simp only
    congr 1; push_cast; ring
  · funext n
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [exp_neg_sign_mul_pi_div_two_mul_I_pow (Or.inr rfl),
      exp_neg_sign_mul_pi_div_two_mul_I_pow (Or.inl rfl)]
    push_cast
    have h1 : (-(-1:ℂ) * I)^(2*n+1+1) = (-1)^(n+1) := by
      rw [show 2*n+1+1 = 2*(n+1) by ring, pow_mul]; simp
    have h2 : (-(1:ℂ) * I)^(2*n+1+1) = (-1)^(n+1) := by
      rw [show 2*n+1+1 = 2*(n+1) by ring, pow_mul]; simp
    rw [h1, h2, pow_succ (-1:ℂ) (2*n), pow_mul (-1:ℂ) 2 n, pow_succ (-1:ℂ) n]
    ring

end DLMF.Confluent
