/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.ExpIntegralAsymptotics

/-!
# Generalized sine and cosine integrals through incomplete Gamma

Rotated Gamma tails and segment integrals give generalized sine and cosine integral
representations.

Source references and common attribution are retained in
`DLMF.IncompleteGamma.SineCosine`.
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

/-- Identity under the stated parameter and domain assumptions: `genCosIntTailOnLog a
w+ε*I*genSinIntTailOnLog a w=exp (ε*π*I*a/2)*upperIncGammaOnLog a (w-ε*π*I/2)`. -/
@[dlmf 8.21.E1]
theorem genUpperTrig_gamma (a w : ℂ) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    genCosIntTailOnLog a w+ε*I*genSinIntTailOnLog a w=exp (ε*π*I*a/2)*upperIncGammaOnLog a (w-ε*π*I/2) := by
  rcases hε with rfl | rfl <;>
    simp only [genCosIntTailOnLog,genSinIntTailOnLog,Complex.ofReal_one,Complex.ofReal_neg,
      neg_mul,one_mul,sub_neg_eq_add,neg_neg]
  all_goals field_simp; ring_nf

/-- Differentiability of the indicated parameterized function: `Differentiable ℂ (fun a =>
genSinIntTailOnLog a w)`. -/
theorem genSinIntTail_parameter_entire (w : ℂ) :
    Differentiable ℂ (fun a => genSinIntTailOnLog a w) := by
  have h1 := upperIncGammaOnLog_parameter_entire (w-π*I/2)
  have h2 := upperIncGammaOnLog_parameter_entire (w+π*I/2)
  exact (((by fun_prop : Differentiable ℂ fun a : ℂ => exp (π*I*a/2)).mul h1).sub
    ((by fun_prop : Differentiable ℂ fun a : ℂ => exp (-π*I*a/2)).mul h2)).div_const (2*I)

/-- Differentiability of the indicated parameterized function: `Differentiable ℂ (fun a =>
genCosIntTailOnLog a w)`. -/
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

/-- The function `(fun b => genSinIntOnLog b w)` is analytic over `ℂ` at `a`. -/
theorem genSinInt_parameter_analytic {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n+1)) (w : ℂ) :
    AnalyticAt ℂ (fun b => genSinIntOnLog b w) a := by
  simp_rw [incG_genSinIntOnLog_eq]
  refine (analyticAt_cexp.comp ((analyticAt_id).mul analyticAt_const)).mul
    (incG_trigTerm_analyticAt (exp w) 1 ∅ fun k _ h => ha k ?_)
  push_cast at h; linear_combination h

/-- The function `(fun b => genCosIntOnLog b w)` is analytic over `ℂ` at `a`. -/
theorem genCosInt_parameter_analytic {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n : ℂ)) (w : ℂ) :
    AnalyticAt ℂ (fun b => genCosIntOnLog b w) a := by
  simp_rw [incG_genCosIntOnLog_eq]
  refine (analyticAt_cexp.comp ((analyticAt_id).mul analyticAt_const)).mul
    (incG_trigTerm_analyticAt (exp w) 0 ∅ fun k _ h => ha k ?_)
  push_cast at h; linear_combination h

/-- The map `(fun a : ℂ => (a+(2*n+1))*genSinIntOnLog a w)` tends to `(𝓝 ((-1 :
ℂ)^n/(2*n+1).factorial))` along `(𝓝[≠] (-(2*n+1 : ℂ)))`. -/
theorem genSinInt_parameter_residue (n : ℕ) (w : ℂ) :
    Tendsto (fun a : ℂ => (a+(2*n+1))*genSinIntOnLog a w) (𝓝[≠] (-(2*n+1 : ℂ))) (𝓝 ((-1 : ℂ)^n/(2*n+1).factorial)) := by
  have h := incG_trig_residue w 1 n
  push_cast at h
  simp_rw [incG_genSinIntOnLog_eq]
  exact h

/-- The map `(fun a : ℂ => (a+2*n)*genCosIntOnLog a w)` tends to `(𝓝 ((-1 :
ℂ)^n/(2*n).factorial))` along `(𝓝[≠] (-(2*n : ℂ)))`. -/
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

/-- Horizontal-ray integral representation: `HasIntegralAtTop (fun t : ℝ => (t : ℂ)^(a-1)*exp
(ε*I*t)) 0 (exp (ε*π*I*a/2)*Gamma a)`. -/
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

/-- Horizontal-ray integral representation: `HasIntegralAtTop (fun t : ℝ => (t : ℂ)^(a-1)*exp
(ε*I*t)) 0 (exp (ε*π*I*a/2)*Gamma a)`. -/
@[dlmf 8.21.E3]
theorem gamma_rotated_oscillatory_integral {a : ℂ} (ha0 : 0 < a.re) (ha1 : a.re < 1) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    HasIntegralAtTop (fun t : ℝ => (t : ℂ)^(a-1)*exp (ε*I*t)) 0 (exp (ε*π*I*a/2)*Gamma a) :=
  incG_gamma_rotated_oscillatory_integral ha0 ha1 hε

/-- Horizontal-ray integral representation: `HasIntegralAtTop (fun t : ℝ => (z+t)^(a-1)*sin (z+t))
0 (genSinIntTail a z)`. -/
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

/-- Horizontal-ray integral representation: `HasIntegralAtTop (fun t : ℝ => (z+t)^(a-1)*cos (z+t))
0 (genCosIntTail a z)`. -/
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

/-- Identity under the stated parameter and domain assumptions: `exp (log z - π*I/2) = -I*z`. -/
theorem incG_exp_log_sub_half_pi {z : ℂ} (hz : z ≠ 0) : exp (log z - π*I/2) = -I*z := by
  have hI : exp (π*I/2) = I := by
    rw [show (π:ℂ)*I/2 = ((π/2:ℝ):ℂ)*I by push_cast; ring, Complex.exp_mul_I]; simp
  rw [Complex.exp_sub, Complex.exp_log hz, hI]; field_simp; rw [I_sq]; ring

/-- Identity under the stated parameter and domain assumptions: `exp (log z + π*I/2) = I*z`. -/
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

/-- Continuity of the indicated function: `Continuous fun b => genSinIntTail b z`. -/
theorem incG_genSinIntTail_continuous (z : ℂ) : Continuous fun b => genSinIntTail b z := by
  unfold genSinIntTail genSinIntTailOnLog
  have h1 := continuous_upperIncGammaOnLog_param (log z - π*I/2)
  have h2 := continuous_upperIncGammaOnLog_param (log z + π*I/2)
  exact (((by fun_prop : Continuous fun b : ℂ => exp (π*I*b/2)).mul h1).sub
    ((by fun_prop : Continuous fun b : ℂ => exp (-π*I*b/2)).mul h2)).div_const _

/-- Continuity of the indicated function: `Continuous fun b => genCosIntTail b z`. -/
theorem incG_genCosIntTail_continuous (z : ℂ) : Continuous fun b => genCosIntTail b z := by
  unfold genCosIntTail genCosIntTailOnLog
  have h1 := continuous_upperIncGammaOnLog_param (log z - π*I/2)
  have h2 := continuous_upperIncGammaOnLog_param (log z + π*I/2)
  exact (((by fun_prop : Continuous fun b : ℂ => exp (π*I*b/2)).mul h1).add
    ((by fun_prop : Continuous fun b : ℂ => exp (-π*I*b/2)).mul h2)).div_const _

/-- Identity under the stated parameter and domain assumptions: `genSinInt a
z=gammaSinHalfPiContinued a-genSinIntTail a z`. -/
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

/-- Identity under the stated parameter and domain assumptions: `genCosInt a
z=gammaCosHalfPiContinued a-genCosIntTail a z`. -/
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

/-- The map `(fun x : ℝ => genSinInt a x)` tends to `(𝓝 (gammaSinHalfPiContinued a))` along
`atTop`. -/
theorem incG_genSinInt_value_at_infinity {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n+1)) (ha1 : a.re < 1) :
    Tendsto (fun x : ℝ => genSinInt a x) atTop (𝓝 (gammaSinHalfPiContinued a)) := by
  have h := ((tendsto_genTrigTail_add_ofReal ha1 0).1).const_sub (gammaSinHalfPiContinued a)
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [zero_add, incG_genSinInt_complement ha (ofReal_ne_zero.mpr hx.ne')]

/-- The map `(fun x : ℝ => genCosInt a x)` tends to `(𝓝 (gammaCosHalfPiContinued a))` along
`atTop`. -/
theorem incG_genCosInt_value_at_infinity {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n : ℂ)) (ha1 : a.re < 1) :
    Tendsto (fun x : ℝ => genCosInt a x) atTop (𝓝 (gammaCosHalfPiContinued a)) := by
  have h := ((tendsto_genTrigTail_add_ofReal ha1 0).2).const_sub (gammaCosHalfPiContinued a)
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [zero_add, incG_genCosInt_complement ha (ofReal_ne_zero.mpr hx.ne')]

/-- Identity under the stated parameter and domain assumptions: `genSinInt a
z=gammaSinHalfPiContinued a-genSinIntTail a z`. -/
@[dlmf 8.21.E8]
theorem genSinInt_complement {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n+1)) {z : ℂ} (hz : z ≠ 0) :
    genSinInt a z=gammaSinHalfPiContinued a-genSinIntTail a z :=
  incG_genSinInt_complement ha hz

/-- Identity under the stated parameter and domain assumptions: `genCosInt a
z=gammaCosHalfPiContinued a-genCosIntTail a z`. -/
@[dlmf 8.21.E9]
theorem genCosInt_complement {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n : ℂ)) {z : ℂ} (hz : z ≠ 0) :
    genCosInt a z=gammaCosHalfPiContinued a-genCosIntTail a z :=
  incG_genCosInt_complement ha hz

/-- Ein at the negative rotated argument, by the parities of Cin and Si. -/
theorem expIntEin_neg_mul_I_eq (z : ℂ) : expIntEin (-I*z)=cosIntCin z-I*sinInt z := by
  have h := expIntEin_mul_I (-z)
  rw [show I*(-z)=-I*z by ring, cosIntCin_even, sinInt_odd] at h
  rw [h]; ring

/-- Identity under the stated parameter and domain assumptions: `genSinIntTail 0 z = -sinIntTail z
∧ genCosIntTail 0 z = -cosInt z`. -/
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

/-- Identity under the stated parameter and domain assumptions: `genSinInt 0 z=sinInt z`. -/
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

/-- The map `(fun x : ℝ => genCosInt a x)` tends to `(𝓝 (gammaCosHalfPiContinued a))` along
`atTop`. -/
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

/-- Identity under the stated parameter and domain assumptions: `genCosIntOnLog a
w+ε*I*genSinIntOnLog a w=exp (ε*π*I*a/2)*lowerIncGammaOnLog a (w-ε*π*I/2)`. -/
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

/-- The series with terms `(fun k : ℕ => z^a*(-1 : ℂ)^k*z^(2*k+1)/((2*k+a+1)*(2*k+1).factorial))`
converges to `(genSinInt a z)`. -/
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

/-- The series with terms `(fun k : ℕ => z^a*(-1 : ℂ)^k*z^(2*k)/((2*k+a)*(2*k).factorial))`
converges to `(genCosInt a z)`. -/
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

/-- Identity under the stated parameter and domain assumptions: `genSinInt a z=primitive (fun t =>
t^(a-1)*sin t) z`. -/
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

/-- Identity under the stated parameter and domain assumptions: `genCosInt a z=primitive (fun t =>
t^(a-1)*cos t) z`. -/
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

end DLMF.Confluent
end
