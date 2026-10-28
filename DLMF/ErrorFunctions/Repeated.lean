/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ErrorFunctions.BoundsAsymptotics
public import DLMF.ParabolicCylinder.Basic

/-!
# Repeated complementary error integrals, DLMF §7.18

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Remaining admitted statements are not completed proofs. The Taylor HasSum uses
Mathlib's `Complex.hasSum_taylorSeries_of_entire` and the proved weighted cylinder
derivative ladder, retaining reciprocal-Gamma zeros in all higher coefficients.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat Interval
namespace DLMF.Confluent

/-- Repeated complementary Gaussian tail; only indices at least -1 have mathematical meaning. -/
@[dlmf 7.18.E1, dlmf 7.18.E2]
def iteratedErfc (n : ℤ) (z : ℂ) : ℂ :=
  if n = -1 then 2/Real.sqrt π*exp (-z^2) else if n < 0 then 0 else 2/Real.sqrt π*(∫ t : ℝ in Ioi 0, (t : ℂ)^n.toNat/(n.toNat.factorial : ℂ)*exp (-(z+t)^2))

/-- Jeffreys probability function Hh_n with its Gaussian-tail normalization. -/
def gaussianProbabilityHh (n : ℕ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, (t : ℂ)^n/(n.factorial : ℂ)*exp (-(z+t)^2/2)

/-- Completing the square identifies the Gaussian probability moments with cylinder U. -/
theorem gaussianProbabilityHh_eq_pcfU (n : ℕ) (z : ℂ) :
    gaussianProbabilityHh n z=exp (-z^2/4)*pcfU (n+1/2) z := by
  rw [pcfU_eq_integral (by simp only [add_re, natCast_re]; norm_num; linarith [(Nat.cast_nonneg n : (0:ℝ)≤n)])]
  rw [show (1/2:ℂ)+(n+1/2)=(n:ℂ)+1 by ring, Gamma_nat_eq_factorial,
    show (n:ℂ)+1/2-1/2=n by ring]
  simp only [cpow_natCast]
  rw [gaussianProbabilityHh, ← mul_assoc, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  calc
    (t:ℂ)^n/(n.factorial:ℂ)*exp (-(z+t)^2/2)=
        (t:ℂ)^n/(n.factorial:ℂ)*(exp (-z^2/4)*exp (-z^2/4)*exp (-(t:ℂ)^2/2-z*t)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 2
      ring
    _ = _ := by ring

/-- The Gaussian change of scale, with its Jacobian and moment power retained. -/
theorem gaussianProbabilityHh_sqrt_two (n : ℕ) (z : ℂ) :
    gaussianProbabilityHh n ((Real.sqrt 2:ℂ)*z)=(Real.sqrt 2:ℂ)^(n+1)*
      ∫ t : ℝ in Ioi 0, (t:ℂ)^n/(n.factorial:ℂ)*exp (-(z+t)^2) := by
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs : (Real.sqrt 2:ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  let F : ℝ → ℂ := fun t => (t:ℂ)^n/(n.factorial:ℂ)*exp (-((Real.sqrt 2:ℂ)*z+t)^2/2)
  have hc := integral_comp_mul_left_Ioi' F 0 hspos
  simp only [mul_zero, Complex.real_smul] at hc
  calc
    gaussianProbabilityHh n ((Real.sqrt 2:ℂ)*z)=(Real.sqrt 2:ℂ)*∫ t : ℝ in Ioi 0, F (Real.sqrt 2*t) := hc.symm
    _ = (Real.sqrt 2:ℂ)*∫ t : ℝ in Ioi 0,
        (Real.sqrt 2:ℂ)^n*((t:ℂ)^n/(n.factorial:ℂ)*exp (-(z+t)^2)) := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp [F]
      push_cast
      rw [mul_pow]
      have he : -((Real.sqrt 2:ℂ)*z+(Real.sqrt 2:ℂ)*t)^2/2=-(z+t)^2 := by
        rw [← mul_add, mul_pow, hs]
        ring
      rw [he]
      ring
    _ = _ := by rw [integral_const_mul, pow_succ]; ring

/-- A natural-power normalization of the repeated complementary Gaussian integral. -/
theorem iteratedErfc_eq_pcfU_nat (n : ℕ) (z : ℂ) :
    iteratedErfc n z=2/((Real.sqrt π:ℂ)*(Real.sqrt 2:ℂ)^(n+1))*
      exp (-z^2/2)*pcfU (n+1/2) ((Real.sqrt 2:ℂ)*z) := by
  have hs0 : (Real.sqrt 2:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  have hs : (Real.sqrt 2:ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hH := gaussianProbabilityHh_eq_pcfU n ((Real.sqrt 2:ℂ)*z)
  have hS := gaussianProbabilityHh_sqrt_two n z
  rw [mul_pow, hs, show -(2*z^2)/4=-z^2/2 by ring] at hH
  rw [iteratedErfc, if_neg (by omega), if_neg (by omega)]
  simp only [Int.toNat_natCast]
  calc
    2/(Real.sqrt π:ℂ)*(∫ t : ℝ in Ioi 0, (t:ℂ)^n/(n.factorial:ℂ)*exp (-(z+t)^2)) =
        2/(Real.sqrt π:ℂ)*(gaussianProbabilityHh n ((Real.sqrt 2:ℂ)*z)/(Real.sqrt 2:ℂ)^(n+1)) := by
      rw [hS]
      field_simp
    _ = _ := by rw [hH]; ring

/-- The positive square-root normalization agrees with the natural Gaussian scale. -/
theorem iteratedErfc_normalization (n : ℕ) :
    ((2:ℂ)^((n:ℤ)-1)*π)^(1/2:ℂ)=(Real.sqrt π:ℂ)*(Real.sqrt 2:ℂ)^(n+1)/2 := by
  have hpow : (2:ℝ)^((n:ℤ)-1)=(2:ℝ)^n/2 := by
    rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_one]
  have hc : (2:ℂ)^((n:ℤ)-1)*π=(((2:ℝ)^n/2)*π:ℝ) := by
    rw [← Complex.ofReal_ofNat 2, ← Complex.ofReal_zpow, ← Complex.ofReal_mul, hpow]
  have hexp : (((2:ℝ)^n/2*π:ℝ):ℂ)^(1/2:ℂ)=(Real.sqrt ((2:ℝ)^n/2*π):ℂ) := by
    have h := Complex.ofReal_cpow (show 0 ≤ (2:ℝ)^n/2*π by positivity) (1/2:ℝ)
    rw [← Real.sqrt_eq_rpow] at h
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at h
    exact h.symm
  rw [hc,hexp]
  have hr : Real.sqrt ((2:ℝ)^n/2*π)=Real.sqrt π*(Real.sqrt 2)^(n+1)/2 := by
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
    have hp := Real.sq_sqrt Real.pi_pos.le
    have hh := Real.sq_sqrt (show 0 ≤ (2:ℝ)^n/2*π by positivity)
    have he : (Real.sqrt π*(Real.sqrt 2)^(n+1)/2)^2=(2:ℝ)^n/2*π := by
      rw [div_pow, mul_pow, ← pow_mul, mul_comm (n+1) 2, pow_mul, hs, hp, pow_succ]
      ring
    nlinarith [show 0 ≤ Real.sqrt π*(Real.sqrt 2)^(n+1)/2 by positivity,
      Real.sqrt_nonneg ((2:ℝ)^n/2*π)]
  rw [hr]
  push_cast
  rfl

/-- Identity under the stated parameter and domain assumptions: `iteratedErfc (-1) z=2/Real.sqrt
π*exp (-z^2) ∧ iteratedErfc 0 z=erfc z`. -/
@[dlmf 7.18.E1]
theorem iteratedErfc_initial (z : ℂ) :
    iteratedErfc (-1) z=2/Real.sqrt π*exp (-z^2) ∧ iteratedErfc 0 z=erfc z := by
  refine ⟨by simp [iteratedErfc], ?_⟩
  have h0 := iteratedErfc_eq_pcfU_nat 0 z
  norm_num only [Nat.cast_zero] at h0
  rw [h0, pcfU_half]
  have hs0 : (Real.sqrt 2:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  have hπ0 : (Real.sqrt π:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hs : (Real.sqrt 2:ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  rw [show ((Real.sqrt 2:ℂ)*z)/(Real.sqrt 2:ℂ)=z by field_simp,
    mul_pow, hs, show (2*z^2)/4=z^2/2 by ring]
  rw [show (Real.sqrt (π/2):ℂ)=(Real.sqrt π:ℂ)/(Real.sqrt 2:ℂ) by exact_mod_cast Real.sqrt_div Real.pi_pos.le 2]
  rw [← mul_assoc, show 2/((Real.sqrt π:ℂ)*(Real.sqrt 2:ℂ)^(0+1))*exp (-z^2/2)*
      ((Real.sqrt π:ℂ)/(Real.sqrt 2:ℂ)*exp (z^2/2))=
      (2/(Real.sqrt 2:ℂ)^2)*(exp (-z^2/2)*exp (z^2/2)) by field_simp; ring,
    hs, ← Complex.exp_add, show -z^2/2+z^2/2=(0:ℂ) by ring]
  simp

/-- Integer-index form of the Gaussian-cylinder bridge, including the initial index -1. -/
theorem iteratedErfc_eq_pcfU_int (n : ℤ) (hn : -1≤n) (z : ℂ) :
    iteratedErfc n z=2/((Real.sqrt π:ℂ)*(Real.sqrt 2:ℂ)^(n+1))*
      exp (-z^2/2)*pcfU ((n:ℂ)+1/2) ((Real.sqrt 2:ℂ)*z) := by
  by_cases h : n = -1
  · subst n
    norm_num only [Int.cast_neg, Int.cast_one, neg_add_cancel, zpow_zero, mul_one]
    rw [show -(1/2:ℂ)= -1/2 by ring, pcfU_neg_half, (iteratedErfc_initial z).1,
      mul_pow, show (Real.sqrt 2:ℂ)^2=2 by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  · have hn0 : 0≤n := by omega
    lift n to ℕ using hn0 with m
    simpa only [Int.cast_natCast, ← Int.natCast_add_one, zpow_natCast] using iteratedErfc_eq_pcfU_nat m z

/-- Entire differentiability of every nonnegative repeated erfc integral. -/
theorem differentiable_iteratedErfc (n : ℕ) : Differentiable ℂ (iteratedErfc n) := by
  have he := funext (iteratedErfc_eq_pcfU_nat n)
  rw [he]
  have hU : Differentiable ℂ (pcfU ((n:ℂ)+1/2)) := fun z => (hasDerivAt_pcfU _ z).differentiableAt
  fun_prop

/-- At `z`, the function `(iteratedErfc n)` has derivative `(-iteratedErfc ((n : ℤ)-1) z)`. -/
@[dlmf 7.18.E3]
theorem hasDerivAt_iteratedErfc (n : ℕ) (z : ℂ) :
    HasDerivAt (iteratedErfc n) (-iteratedErfc ((n : ℤ)-1) z) z := by
  let s : ℂ := Real.sqrt 2
  let c (k : ℤ) : ℂ := 2/((Real.sqrt π:ℂ)*s^(k+1))
  have hs : s^2=2 := by dsimp [s]; exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hs0 : s≠0 := by intro h; rw [h] at hs; norm_num at hs
  have hc : c ((n:ℤ)-1)=c n*s := by
    dsimp [c]
    rw [sub_add_cancel, zpow_add₀ hs0, zpow_one]
    field_simp
  have he : iteratedErfc n = fun w => c n*exp (-w^2/2)*pcfU ((n:ℂ)+1/2) (s*w) := by
    funext w
    exact iteratedErfc_eq_pcfU_int n (by omega) w
  rw [he]
  have hd : HasDerivAt (fun w : ℂ => exp (-w^2/2)) (-z*exp (-z^2/2)) z := by
    convert (((hasDerivAt_pow 2 z).neg).div_const 2).cexp using 1 <;> simp only [Pi.neg_apply, Function.comp_apply] <;> ring
  have hu := (hasDerivAt_pcfU ((n:ℂ)+1/2) (s*z)).comp z ((hasDerivAt_id z).const_mul s)
  refine (((hd.const_mul (c n)).mul hu).congr_of_eventuallyEq (Eventually.of_forall fun w=>rfl)).congr_deriv ?_
  rw [iteratedErfc_eq_pcfU_int ((n:ℤ)-1) (by omega), ← deriv_pcfU]
  change _ = -(c ((n:ℤ)-1)*exp (-z^2/2)*pcfU (((n:ℤ)-1:ℤ)+1/2) (s*z))
  rw [hc]
  have hr := pcfU_recurrence_sub ((n:ℂ)+1/2) (s*z)
  norm_num only [Int.cast_sub, Int.cast_natCast, Int.cast_one] at *
  rw [show (n:ℂ)-1+1/2=n+1/2-1 by ring]
  simp only [Function.comp_apply, id_eq]
  linear_combination (norm := ring_nf) c n*s*exp (-z^2/2)*hr
  try rw [hs]
  ring

/-- The repeated erfc integrals decay along the positive real direction. -/
theorem tendsto_iteratedErfc_add_atTop (n : ℕ) (z : ℂ) :
    Tendsto (fun R : ℝ => iteratedErfc n (z+R)) atTop (𝓝 0) := by
  have hdef (w : ℂ) : iteratedErfc n w =
      2/Real.sqrt π*(∫ t : ℝ in Ioi 0, (t : ℂ)^n/(n.factorial : ℂ)*exp (-(w+t)^2)) := by
    have h1 : ¬((n:ℤ) = -1) := by omega
    have h2 : ¬((n:ℤ) < 0) := by omega
    simp only [iteratedErfc, h1, h2, ite_false, Int.toNat_natCast]
  set M : ℝ := ∫ t : ℝ in Ioi 0, t^n/(n.factorial:ℝ)*Real.exp (-t^2)
  have hgi : IntegrableOn (fun t : ℝ => t^n/(n.factorial:ℝ)*Real.exp (-t^2)) (Ioi 0) := by
    have : IntegrableOn (fun t : ℝ => t^(n:ℝ)*Real.exp (-1*t^2)/(n.factorial:ℝ)) (Ioi 0) :=
      (integrableOn_rpow_mul_exp_neg_mul_sq (b := 1) one_pos
        (s := (n:ℝ)) (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])).div_const (n.factorial:ℝ)
    refine IntegrableOn.congr_fun this (fun t _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_natCast]; ring_nf
  have hev : ∀ᶠ R : ℝ in atTop, ‖iteratedErfc n (z+R)‖ ≤
      2/Real.sqrt π*(Real.exp (z.im^2)*M)*Real.exp (-(z.re+R)^2) := by
    filter_upwards [eventually_ge_atTop (-z.re)] with R hR
    have hxR : 0 ≤ z.re+R := by linarith
    rw [hdef, norm_mul]
    have h2 : ‖(2:ℂ)/(Real.sqrt π:ℂ)‖ = 2/Real.sqrt π := by
      rw [norm_div, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.sqrt_pos.mpr Real.pi_pos)]
    rw [h2, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hb : ∀ t ∈ Ioi (0:ℝ), ‖(t : ℂ)^n/(n.factorial : ℂ)*exp (-(z+R+t)^2)‖ ≤
        Real.exp (z.im^2)*Real.exp (-(z.re+R)^2)*(t^n/(n.factorial:ℝ)*Real.exp (-t^2)) := by
      intro t ht
      have ht : (0:ℝ) < t := ht
      rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht,
        Complex.norm_natCast, Complex.norm_exp]
      have hre : (-(z+(R:ℂ)+(t:ℂ))^2).re = -((z.re+R+t)^2) + z.im^2 := by
        simp [sq]; ring
      rw [hre]
      have hle : Real.exp (-((z.re+R+t)^2) + z.im^2) ≤
          Real.exp (z.im^2)*Real.exp (-(z.re+R)^2)*Real.exp (-t^2) := by
        rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
        nlinarith [mul_nonneg hxR ht.le]
      calc t^n/(n.factorial:ℝ)*Real.exp (-((z.re+R+t)^2) + z.im^2)
          ≤ t^n/(n.factorial:ℝ)*(Real.exp (z.im^2)*Real.exp (-(z.re+R)^2)*Real.exp (-t^2)) :=
            mul_le_mul_of_nonneg_left hle (by positivity)
        _ = _ := by ring
    calc ‖∫ t : ℝ in Ioi 0, (t : ℂ)^n/(n.factorial : ℂ)*exp (-(z+R+t)^2)‖
        ≤ ∫ t : ℝ in Ioi 0, Real.exp (z.im^2)*Real.exp (-(z.re+R)^2)*
            (t^n/(n.factorial:ℝ)*Real.exp (-t^2)) :=
          norm_integral_le_of_norm_le (hgi.const_mul _)
            ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hb))
      _ = _ := by rw [integral_const_mul]; ring
  refine squeeze_zero_norm' hev ?_
  have : Tendsto (fun R : ℝ => -(z.re+R)^2) atTop atBot := by
    have h1 : Tendsto (fun R : ℝ => z.re+R) atTop atTop := tendsto_atTop_add_const_left _ _ tendsto_id
    exact tendsto_neg_atTop_atBot.comp ((tendsto_pow_atTop two_ne_zero).comp h1)
  simpa using (Real.tendsto_exp_atBot.comp this).const_mul (2/Real.sqrt π*(Real.exp (z.im^2)*M))

/-- Horizontal-ray integral representation: `HasIntegralAtTop (fun t : ℝ => iteratedErfc ((n :
ℤ)-1) (z+t)) 0 (iteratedErfc n z)`. -/
@[dlmf 7.18.E2]
theorem iteratedErfc_tail (n : ℕ) (z : ℂ) :
    HasIntegralAtTop (fun t : ℝ => iteratedErfc ((n : ℤ)-1) (z+t)) 0 (iteratedErfc n z) := by
  have hcont : Continuous (iteratedErfc ((n:ℤ)-1)) := by
    cases n with
    | zero =>
      have : iteratedErfc (((0:ℕ):ℤ)-1) = fun w => 2/Real.sqrt π*exp (-w^2) := by
        funext w; simpa using (iteratedErfc_initial w).1
      rw [this]; fun_prop
    | succ m =>
      have : ((m+1:ℕ):ℤ)-1 = ((m:ℕ):ℤ) := by push_cast; ring
      rw [this]; exact (differentiable_iteratedErfc m).continuous
  have hR : ∀ R : ℝ, (∫ t in (0:ℝ)..R, iteratedErfc ((n : ℤ)-1) (z+t)) =
      iteratedErfc n z - iteratedErfc n (z+R) := by
    intro R
    have hd : ∀ x ∈ uIcc (0:ℝ) R, HasDerivAt (fun t : ℝ => -iteratedErfc n (z+t))
        (iteratedErfc ((n : ℤ)-1) (z+x)) x := by
      intro x _
      have h2 : HasDerivAt (fun t : ℝ => z+(t:ℂ)) 1 x := by
        simpa using ((hasDerivAt_id (x:ℂ)).const_add z).comp_ofReal
      have h3 := ((hasDerivAt_iteratedErfc n (z+x)).comp x h2).neg
      exact h3.congr_deriv (by simp)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((hcont.comp (by fun_prop : Continuous fun t : ℝ => z+(t:ℂ))).intervalIntegrable _ _)]
    simp; ring
  unfold HasIntegralAtTop
  simp_rw [hR]
  simpa using (tendsto_iteratedErfc_add_atTop n z).const_sub (iteratedErfc n z)

/-- Identity under the stated parameter and domain assumptions: `iteratedErfc n z =
-z/n*iteratedErfc ((n : ℤ)-1) z+1/(2*n)*iteratedErfc ((n : ℤ)-2) z`. -/
@[dlmf 7.18.E7]
theorem iteratedErfc_recurrence {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    iteratedErfc n z = -z/n*iteratedErfc ((n : ℤ)-1) z+1/(2*n)*iteratedErfc ((n : ℤ)-2) z := by
  let s : ℂ := Real.sqrt 2
  have hs : s^2=2 := by dsimp [s]; exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hs0 : s≠0 := by intro h; rw [h] at hs; norm_num at hs
  have hn0 : (n:ℂ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  rw [iteratedErfc_eq_pcfU_int n (by omega), iteratedErfc_eq_pcfU_int ((n:ℤ)-1) (by omega),
    iteratedErfc_eq_pcfU_int ((n:ℤ)-2) (by omega)]
  change 2/((Real.sqrt π:ℂ)*s^((n:ℤ)+1))*exp (-z^2/2)*pcfU ((n:ℂ)+1/2) (s*z) = _
  have hp : s^((n:ℤ)+1)=s^((n:ℤ)-1)*2 := by
    rw [show (n:ℤ)+1=(n-1)+2 by ring, zpow_add₀ hs0, zpow_ofNat, hs]
  have hq : s^(n:ℤ)=s^((n:ℤ)-1)*s := by
    calc
      s^(n:ℤ)=s^(((n:ℤ)-1)+1) := by congr 1; ring
      _ = _ := by rw [zpow_add₀ hs0, zpow_one]
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_ofNat, Int.cast_one, sub_add_cancel,
    show (n:ℤ)-2+1=n-1 by ring]
  change _ = -z/n*(2/((Real.sqrt π:ℂ)*s^(n:ℤ))*exp (-z^2/2)*pcfU ((n:ℂ)-1+1/2) (s*z))+
    1/(2*n)*(2/((Real.sqrt π:ℂ)*s^((n:ℤ)-1))*exp (-z^2/2)*pcfU ((n:ℂ)-2+1/2) (s*z))
  rw [hp,hq]
  have hr := pcfU_three_term ((n:ℂ)-1/2) (s*z)
  rw [show (n:ℂ)-1/2-1=n-2+1/2 by ring, show (n:ℂ)-1/2+1=n+1/2 by ring,
    show (n:ℂ)-1/2+1/2=n by ring, show (n:ℂ)-1/2=n-1+1/2 by ring] at hr
  have hπ0 : (Real.sqrt π:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp [hs0,hπ0,hn0]
  linear_combination (norm := ring_nf) s*hr
  simp only [hs]
  ring

/-- The derivative of the exponentially weighted repeated Gaussian tail raises its index. -/
theorem hasDerivAt_exp_mul_iteratedErfc (n : ℕ) (z : ℂ) :
    HasDerivAt (fun t => exp (t^2)*iteratedErfc n t)
      (-2*(n+1)*exp (z^2)*iteratedErfc (n+1:ℕ) z) z := by
  have hd := ((hasDerivAt_pow 2 z).cexp).mul (hasDerivAt_iteratedErfc n z)
  refine (hd.congr_of_eventuallyEq (Eventually.of_forall fun t=>rfl)).congr_deriv ?_
  have hr := iteratedErfc_recurrence (n:=n+1) (by omega) z
  simp only [Nat.cast_succ, Int.natCast_add, Int.natCast_one,
    add_sub_cancel_right, show (n:ℤ)+1-2=n-1 by ring] at hr
  have hn0 : (n:ℂ)+1≠0 := by exact_mod_cast n.succ_ne_zero
  field_simp [hn0] at hr
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Int.natCast_add, Int.natCast_one]
  linear_combination exp (z^2)*hr

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv n (fun t => exp
(t^2)*erfc t) z=(-1 : ℂ)^n*2^n*n.factorial*exp (z^2)*iteratedErfc n z`. -/
@[dlmf 7.18.E4]
theorem iteratedDeriv_scaled_erfc (n : ℕ) (z : ℂ) :
    iteratedDeriv n (fun t => exp (t^2)*erfc t) z=(-1 : ℂ)^n*2^n*n.factorial*exp (z^2)*iteratedErfc n z := by
  induction n generalizing z with
  | zero => simp only [iteratedDeriv_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, Nat.cast_zero, one_mul]; rw [(iteratedErfc_initial z).2]
  | succ n ih =>
    rw [iteratedDeriv_succ,funext ih]
    have hf : (fun t : ℂ => (-1:ℂ)^n*2^n*(n.factorial:ℂ)*exp (t^2)*iteratedErfc n t)=
        (fun t : ℂ => ((-1:ℂ)^n*2^n*(n.factorial:ℂ))*(exp (t^2)*iteratedErfc n t)) := by funext t; ring
    rw [hf]
    rw [((hasDerivAt_exp_mul_iteratedErfc n z).const_mul _).deriv]
    rw [pow_succ,pow_succ,Nat.factorial_succ]
    push_cast
    ring

/-- The second derivative equation transferred from the first-derivative recurrence. -/
theorem hasDerivAt_deriv_iteratedErfc (n : ℕ) (z : ℂ) :
    HasDerivAt (deriv (iteratedErfc n))
      (2*n*iteratedErfc n z-2*z*deriv (iteratedErfc n) z) z := by
  cases n with
  | zero =>
    have he : deriv (iteratedErfc (0:ℕ))=(fun w : ℂ => -(2/(Real.sqrt π:ℂ)*exp (-w^2))) := by
      funext w
      rw [(hasDerivAt_iteratedErfc 0 w).deriv]
      norm_num only [Int.natCast_zero,zero_sub]
      rw [(iteratedErfc_initial w).1]
    rw [he]
    have hd := (((hasDerivAt_pow 2 z).neg).cexp).const_mul (-(2/(Real.sqrt π:ℂ)))
    refine (hd.congr_of_eventuallyEq (Eventually.of_forall fun w=>by simp only [Pi.neg_apply]; ring)).congr_deriv ?_
    simp only [Pi.neg_apply,Nat.cast_zero,zero_mul,zero_sub,Nat.cast_ofNat,pow_one]
    ring
  | succ n =>
    have he : deriv (iteratedErfc (n+1:ℕ))=(fun w : ℂ => -iteratedErfc n w) := by
      funext w
      rw [(hasDerivAt_iteratedErfc (n+1) w).deriv]
      norm_num only [Int.natCast_add,Int.natCast_one,add_sub_cancel_right]
    rw [he]
    have hd := (hasDerivAt_iteratedErfc n z).neg
    refine (hd.congr_of_eventuallyEq (Eventually.of_forall fun w=>rfl)).congr_deriv ?_
    have hr := iteratedErfc_recurrence (n:=n+1) (by omega) z
    simp only [Nat.cast_succ,Int.natCast_add,Int.natCast_one,add_sub_cancel_right,
      show (n:ℤ)+1-2=n-1 by ring] at hr
    have hn0 : (n:ℂ)+1≠0 := by exact_mod_cast n.succ_ne_zero
    field_simp [hn0] at hr
    simp only [Nat.cast_succ,Int.natCast_add,Int.natCast_one]
    linear_combination -hr

/-- The stated relation follows from the given hypotheses: `let W`. -/
@[dlmf 7.18.E5]
theorem iteratedErfc_ode (n : ℕ) (A B z : ℂ) :
    let W := fun t => A*iteratedErfc n t+B*iteratedErfc n (-t); deriv (deriv W) z+2*z*deriv W z-2*n*W z=0 := by
  dsimp only
  have h1 (w : ℂ) := (differentiable_iteratedErfc n w).hasDerivAt
  have h2 (w : ℂ) := hasDerivAt_deriv_iteratedErfc n w
  have hd : deriv (fun t=>A*iteratedErfc n t+B*iteratedErfc n (-t))=
      (fun t=>A*deriv (iteratedErfc n) t-B*deriv (iteratedErfc n) (-t)) := by
    funext t
    have hneg := (h1 (-t)).comp t (hasDerivAt_neg t)
    exact (((h1 t).const_mul A).add (hneg.const_mul B)).deriv.trans (by simp only [mul_neg]; ring)
  rw [hd]
  have hn := (h2 (-z)).comp z (hasDerivAt_neg z)
  have hh := ((h2 z).const_mul A).sub (hn.const_mul B)
  have hh' : HasDerivAt (fun t=>A*deriv (iteratedErfc n) t-B*deriv (iteratedErfc n) (-t)) _ z :=
    hh.congr_of_eventuallyEq (Eventually.of_forall fun t=>rfl)
  rw [hh'.deriv]
  simp only [Function.comp_apply]
  ring

/-- The Wronskian conservation law for the repeated-erfc differential equation. -/
theorem iteratedErfc_ode_wronskian (n : ℕ) {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hf2 : Differentiable ℂ (deriv f))
    (hg : Differentiable ℂ g) (hg2 : Differentiable ℂ (deriv g))
    (hfo : ∀ z, deriv (deriv f) z+2*z*deriv f z-2*n*f z=0)
    (hgo : ∀ z, deriv (deriv g) z+2*z*deriv g z-2*n*g z=0) (z : ℂ) :
    exp (z^2)*(f z*deriv g z-deriv f z*g z)=f 0*deriv g 0-deriv f 0*g 0 := by
  have hd (w : ℂ) : HasDerivAt
      (fun w=>exp (w^2)*(f w*deriv g w-deriv f w*g w)) 0 w := by
    have h := ((hasDerivAt_pow 2 w).cexp).mul
      (((hf w).hasDerivAt.mul (hg2 w).hasDerivAt).sub ((hf2 w).hasDerivAt.mul (hg w).hasDerivAt))
    refine (h.congr_of_eventuallyEq (Eventually.of_forall fun w=>rfl)).congr_deriv ?_
    simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one,Pi.mul_apply,Pi.sub_apply]
    linear_combination exp (w^2)*f w*hgo w-exp (w^2)*g w*hfo w
  have h := is_const_of_deriv_eq_zero (fun w=>(hd w).differentiableAt) (fun w=>(hd w).deriv) z 0
  simpa using h

/-- The Gaussian moment initial values do not vanish for indices at least -1. -/
theorem iteratedErfc_ne_zero_at_zero (k : ℤ) (hk : -1≤k) : iteratedErfc k 0≠0 := by
  have hs0 : (Real.sqrt 2:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  have hπ0 : (Real.sqrt π:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hkr : (-1:ℝ)≤k := by exact_mod_cast hk
  have hg : 0<(3/4+((k:ℂ)+1/2)/2).re := by
    norm_num
    linarith
  rw [iteratedErfc_eq_pcfU_int k hk, mul_zero,pcfU_zero']
  simp only [zero_pow (by norm_num : (2:ℕ)≠0),neg_zero,zero_div,Complex.exp_zero,mul_one]
  apply mul_ne_zero
  · exact div_ne_zero (by norm_num) (mul_ne_zero hπ0 (zpow_ne_zero _ hs0))
  · exact mul_ne_zero (mul_ne_zero hπ0 (cpow_ne_zero_iff.mpr (Or.inl (by norm_num))))
      (inv_ne_zero (Gamma_ne_zero_of_re_pos hg))

/-- Identity under the stated parameter and domain assumptions: `∃ A B : ℂ, ∀ z, W
z=A*iteratedErfc n z+B*iteratedErfc n (-z)`. -/
@[dlmf 7.18.E5]
theorem iteratedErfc_general_solution (n : ℕ) {W : ℂ → ℂ} (hW : Differentiable ℂ W) (hW2 : Differentiable ℂ (deriv W)) (hode : ∀ z, deriv (deriv W) z+2*z*deriv W z-2*n*W z=0) :
    ∃ A B : ℂ, ∀ z, W z=A*iteratedErfc n z+B*iteratedErfc n (-z) := by
  let f : ℂ → ℂ := iteratedErfc n
  let g : ℂ → ℂ := fun z=>iteratedErfc n (-z)
  have hf : Differentiable ℂ f := differentiable_iteratedErfc n
  have hf2 : Differentiable ℂ (deriv f) := fun z=>(hasDerivAt_deriv_iteratedErfc n z).differentiableAt
  have hgd : deriv g=(fun z=> -deriv f (-z)) := by
    funext z
    exact ((hf (-z)).hasDerivAt.comp z (hasDerivAt_neg z)).deriv.trans (by simp)
  have hg : Differentiable ℂ g := by
    change Differentiable ℂ (fun z=>f (-z))
    exact hf.comp (by fun_prop)
  have hg2 : Differentiable ℂ (deriv g) := by rw [hgd]; fun_prop
  have hfo (z : ℂ) : deriv (deriv f) z+2*z*deriv f z-2*n*f z=0 := by
    linear_combination (hasDerivAt_deriv_iteratedErfc n z).deriv
  have hgo (z : ℂ) : deriv (deriv g) z+2*z*deriv g z-2*n*g z=0 := by
    have h := iteratedErfc_ode n 0 1 z
    simpa only [zero_mul,one_mul,zero_add] using h
  let D : ℂ := f 0*deriv g 0-deriv f 0*g 0
  have hD : D≠0 := by
    have hf0 : f 0≠0 := iteratedErfc_ne_zero_at_zero n (by omega)
    have hdf0 : deriv f 0≠0 := by
      rw [(hasDerivAt_iteratedErfc n 0).deriv]
      exact neg_ne_zero.mpr (iteratedErfc_ne_zero_at_zero ((n:ℤ)-1) (by omega))
    dsimp only [D]
    rw [hgd]
    change f 0*(-deriv f (-0))-deriv f 0*f (-0)≠0
    simp only [neg_zero]
    rw [show f 0*(-deriv f 0)-deriv f 0*f 0= -2*f 0*deriv f 0 by ring]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hf0) hdf0
  let A : ℂ := (W 0*deriv g 0-deriv W 0*g 0)/D
  let B : ℂ := (f 0*deriv W 0-deriv f 0*W 0)/D
  refine ⟨A,B,fun z=>?_⟩
  have h1 := iteratedErfc_ode_wronskian n hW hW2 hg hg2 hode hgo z
  have h2 := iteratedErfc_ode_wronskian n hW hW2 hf hf2 hode hfo z
  have h3 := iteratedErfc_ode_wronskian n hf hf2 hg hg2 hfo hgo z
  change W z=A*f z+B*g z
  dsimp only [A,B]
  field_simp [hD]
  dsimp only [D]
  linear_combination f z*h1-g z*h2-W z*h3

/-- Positive real Gaussian scale as a principal complex half-power, at every integer exponent. -/
theorem two_cpow_int_half (k : ℤ) : (2:ℂ)^((k:ℂ)/2)=(Real.sqrt 2:ℂ)^k := by
  rw [show (k:ℂ)/2=(k:ℂ)*(1/2) by ring, cpow_int_mul, two_cpow_half]

/-- Every Taylor coefficient follows from the weighted cylinder derivative ladder, including
reciprocal-Gamma zeros after the repeated-integral index has been exhausted. -/
theorem iteratedDeriv_iteratedErfc_zero (n k : ℕ) :
    iteratedDeriv k (iteratedErfc n) 0=
      (-1:ℂ)^k/((2:ℂ)^((n:ℤ)-k)*Gamma (1+((n:ℂ)-k)/2)) := by
  let s : ℂ := Real.sqrt 2
  let F : ℂ → ℂ := fun w => exp (-1*w^2/4)*pcfU ((n:ℂ)+1/2) w
  have hs : s^2=2 := by dsimp [s]; exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hs0 : s≠0 := by intro h; rw [h] at hs; norm_num at hs
  have hp0 : (Real.sqrt π:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hF : Differentiable ℂ F := by
    have hu : Differentiable ℂ (pcfU ((n:ℂ)+1/2)) := fun w => (hasDerivAt_pcfU _ w).differentiableAt
    dsimp [F]; fun_prop
  have he : iteratedErfc n=fun z => 2/((Real.sqrt π:ℂ)*s^(n+1))*F (s*z) := by
    funext z
    rw [iteratedErfc_eq_pcfU_nat]
    have hexp : -1*(s*z)^2/4= -z^2/2 := by rw [mul_pow,hs]; ring
    simp only [F,hexp,s]
    ring
  rw [he,iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_mul (contDiffOn_univ.mp (hF.differentiableOn.contDiffOn isOpen_univ))]
  dsimp only [F]
  rw [pcfU_iterated_deriv_10, mul_zero,zero_pow two_ne_zero,mul_zero,zero_div,Complex.exp_zero,
    mul_one,pcfU_zero]
  rw [show ((n:ℂ)+1/2-k)/2+1/4=(((n:ℤ)-k+1:ℤ):ℂ)/2 by push_cast; ring,
    show 3/4+((n:ℂ)+1/2-k)/2=1+((n:ℂ)-k)/2 by ring,two_cpow_int_half]
  change 2/((Real.sqrt π:ℂ)*s^(n+1)) *
    (s^k*((-1:ℂ)^k*((Real.sqrt π:ℂ)/(s^((n:ℤ)-k+1)*Gamma (1+((n:ℂ)-k)/2))))) = _
  have hc : 2/((Real.sqrt π:ℂ)*s^(n+1))*s^k*(Real.sqrt π:ℂ)/s^((n:ℤ)-k+1)=
      1/(2:ℂ)^((n:ℤ)-k) := by
    rw [zpow_add₀ hs0,zpow_sub₀ hs0,zpow_natCast,zpow_natCast,zpow_one,
      zpow_sub₀ (by norm_num : (2:ℂ)≠0),zpow_natCast,zpow_natCast,← hs,pow_right_comm s 2 n,pow_right_comm s 2 k,pow_succ]
    field_simp
    ring
  generalize Gamma (1+((n:ℂ)-k)/2)=G
  simp only [div_eq_mul_inv,mul_inv_rev] at hc ⊢
  linear_combination ((-1:ℂ)^k*G⁻¹)*hc

/-- The series with terms `(fun k : ℕ => (-1 : ℂ)^k*z^k/((2 : ℂ)^((n : ℤ)-k)*(k.factorial :
ℂ)*Gamma (1+((n : ℂ)-k)/2)))` converges to `(iteratedErfc n z)`. -/
@[dlmf 7.18.E6]
theorem iteratedErfc_hasSum (n : ℕ) (z : ℂ) :
    HasSum (fun k : ℕ => (-1 : ℂ)^k*z^k/((2 : ℂ)^((n : ℤ)-k)*(k.factorial : ℂ)*Gamma (1+((n : ℂ)-k)/2))) (iteratedErfc n z) := by
  have h := Complex.hasSum_taylorSeries_of_entire (differentiable_iteratedErfc n) 0 z
  refine h.congr_fun fun k => ?_
  rw [iteratedDeriv_iteratedErfc_zero]
  simp only [sub_zero,smul_eq_mul,div_eq_mul_inv,mul_inv_rev]
  ring

/-- Identity under the stated parameter and domain assumptions: `(-1 : ℂ)^n*iteratedErfc n
z+iteratedErfc n (-z)=I^(-(n : ℤ))/((2 : ℂ)^((n : ℤ)-1)*(n.factorial : ℂ))*hermitePolyHEval n
(I*z)`. -/
@[dlmf 7.18.E8]
theorem iteratedErfc_hermite (n : ℕ) (z : ℂ) :
    (-1 : ℂ)^n*iteratedErfc n z+iteratedErfc n (-z)=I^(-(n : ℤ))/((2 : ℂ)^((n : ℤ)-1)*(n.factorial : ℂ))*hermitePolyHEval n (I*z) := by
  let J (k : ℕ) : ℂ := (-1:ℂ)^k*iteratedErfc k z+iteratedErfc k (-z)
  have hstep (k : ℕ) : 2*(k+2)*J (k+2)=2*z*J (k+1)+J k := by
    have hp := iteratedErfc_recurrence (n:=k+2) (by omega) z
    have hm := iteratedErfc_recurrence (n:=k+2) (by omega) (-z)
    have hk0 : (k:ℂ)+2≠0 := by exact_mod_cast (show k+2≠0 by omega)
    simp only [Nat.cast_add,Nat.cast_ofNat,Int.natCast_add,
      show (k:ℤ)+2-1=(k:ℤ)+1 by ring,add_sub_cancel_right] at hp hm
    field_simp [hk0] at hp hm
    dsimp only [J]
    simp only [pow_add,pow_one,neg_one_sq,mul_one,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,
      Int.natCast_add,Int.natCast_one]
    linear_combination (-1:ℂ)^k*hp+hm
  have hmain (k : ℕ) : (2:ℂ)^k*(k.factorial:ℂ)*J k=2*(-I)^k*hermitePolyHEval k (I*z) := by
    induction k using Nat.twoStepInduction with
    | zero =>
      dsimp only [J]
      norm_num only [Nat.cast_zero]
      rw [(iteratedErfc_initial z).2,(iteratedErfc_initial (-z)).2,erfc_negative]
      simp [hermitePolyHEval_zero]
    | one =>
      have hp := iteratedErfc_recurrence (n:=1) (by omega) z
      have hm := iteratedErfc_recurrence (n:=1) (by omega) (-z)
      norm_num only [Nat.cast_one,Int.natCast_one,sub_self,show (1:ℤ)-2= -1 by norm_num] at hp hm
      rw [(iteratedErfc_initial z).2,(iteratedErfc_initial z).1] at hp
      rw [(iteratedErfc_initial (-z)).2,(iteratedErfc_initial (-z)).1,erfc_negative,neg_sq] at hm
      dsimp only [J]
      norm_num only [pow_one,Nat.factorial_one,Nat.cast_one,one_mul,hermitePolyHEval_one]
      linear_combination (norm := ring_nf) -2*hp+2*hm
      simp [I_sq]
    | more k ih0 ih1 =>
      rw [hermitePolyHEval_succ_succ]
      have hs := hstep k
      rw [show k+2=(k+1)+1 by omega,Nat.factorial_succ,Nat.factorial_succ,pow_succ,pow_succ,pow_succ,pow_succ]
      push_cast
      simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one] at ih1
      linear_combination (norm := ring_nf) (2:ℂ)^(k+1)*((k:ℂ)+1)*(k.factorial:ℂ)*hs+2*z*ih1+2*((k:ℂ)+1)*ih0
      simp [I_sq]
  have hn0 : (n.factorial:ℂ)≠0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hIinv : I⁻¹= -I := by norm_num
  rw [zpow_neg,zpow_natCast,←inv_pow,hIinv,zpow_sub₀ (by norm_num : (2:ℂ)≠0),zpow_natCast,zpow_one]
  change J n = _
  have h := hmain n
  field_simp [hn0]
  linear_combination h

/-- Identity under the stated parameter and domain assumptions: `iteratedErfc n z=exp
(-z^2)*(kummerM ((n : ℂ)/2+1/2) (1/2) (z^2)/((2 : ℂ)^n*Gamma ((n : ℂ)/2+1))-z*kummerM ((n :
ℂ)/2+1) (3/2) (z^2)/((2 : ℂ)^((n : ℤ)-1)*Gamma ((n : ℂ)/2+1/2)))`. -/
@[dlmf 7.18.E9]
theorem iteratedErfc_kummerM (n : ℕ) (z : ℂ) :
    iteratedErfc n z=exp (-z^2)*(kummerM ((n : ℂ)/2+1/2) (1/2) (z^2)/((2 : ℂ)^n*Gamma ((n : ℂ)/2+1))-z*kummerM ((n : ℂ)/2+1) (3/2) (z^2)/((2 : ℂ)^((n : ℤ)-1)*Gamma ((n : ℂ)/2+1/2))) := by
  let s : ℂ := Real.sqrt 2
  have hs : s^2=2 := by dsimp [s]; exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hs0 : s≠0 := by intro h; rw [h] at hs; norm_num at hs
  have hπ0 : (Real.sqrt π:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hA : (2:ℂ)/s^(n+1)*s^(-(n:ℤ)-1)=1/(2:ℂ)^n := by
    rw [show -(n:ℤ)-1= -((n:ℤ)+1) by ring,zpow_neg,← Int.natCast_add_one,zpow_natCast]
    have hn : (s^(n+1))^2=(2:ℂ)^(n+1) := by rw [←pow_mul,mul_comm (n+1) 2,pow_mul,hs]
    calc
      2/s^(n+1)*(s^(n+1))⁻¹=2/((s^(n+1))^2) := by ring
      _ = _ := by rw [hn,pow_succ]; field_simp
  have hB : (2:ℂ)/s^(n+1)*s^(-(n:ℤ))*s=1/(2:ℂ)^((n:ℤ)-1) := by
    have hp : s^(-(n:ℤ))=s^(-(n:ℤ)-1)*s := by
      calc
        s^(-(n:ℤ))=s^((-(n:ℤ)-1)+1) := by congr 1; ring
        _ = _ := by rw [zpow_add₀ hs0,zpow_one]
    rw [hp,zpow_sub₀ (by norm_num : (2:ℂ)≠0),zpow_natCast,zpow_one]
    linear_combination (norm := ring_nf) 2*hA
    simp only [hs]
    ring
  rw [iteratedErfc_eq_pcfU_nat,pcfU,pcfEven,pcfOdd]
  change 2/((Real.sqrt π:ℂ)*s^(n+1))*exp (-z^2/2)*
    ((Real.sqrt π:ℂ)*2^(-(((n:ℂ)+1/2)/2+1/4))*(Gamma (3/4+((n:ℂ)+1/2)/2))⁻¹*
      (exp (-(s*z)^2/4)*kummerM (((n:ℂ)+1/2)/2+1/4) (1/2) ((s*z)^2/2))-
      (Real.sqrt π:ℂ)*2^(-(((n:ℂ)+1/2)/2-1/4))*(Gamma (1/4+((n:ℂ)+1/2)/2))⁻¹*
      (s*z*exp (-(s*z)^2/4)*kummerM (((n:ℂ)+1/2)/2+3/4) (3/2) ((s*z)^2/2))) = _
  rw [show -(((n:ℂ)+1/2)/2+1/4)=((-(n:ℤ)-1:ℤ):ℂ)/2 by push_cast; ring,
    show -(((n:ℂ)+1/2)/2-1/4)=((-(n:ℤ):ℤ):ℂ)/2 by push_cast; ring,
    two_cpow_int_half,two_cpow_int_half,mul_pow,hs]
  rw [show 3/4+((n:ℂ)+1/2)/2=n/2+1 by ring,
    show 1/4+((n:ℂ)+1/2)/2=n/2+1/2 by ring,
    show ((n:ℂ)+1/2)/2+1/4=n/2+1/2 by ring,
    show ((n:ℂ)+1/2)/2+3/4=n/2+1 by ring,
    show (2*z^2)/2=z^2 by ring,show -(2*z^2)/4= -z^2/2 by ring]
  have he : exp (-z^2/2)*exp (-z^2/2)=exp (-z^2) := by rw [←Complex.exp_add]; congr 1; ring
  calc
    _ = (exp (-z^2/2)*exp (-z^2/2))*
        ((2/s^(n+1)*s^(-(n:ℤ)-1))*kummerM ((n:ℂ)/2+1/2) (1/2) (z^2)/Gamma ((n:ℂ)/2+1)-
          (2/s^(n+1)*s^(-(n:ℤ))*s)*z*kummerM ((n:ℂ)/2+1) (3/2) (z^2)/Gamma ((n:ℂ)/2+1/2)) := by
      field_simp [hπ0]
      ring
    _ = _ := by rw [he,hA,hB]; ring

/-- Identity under the stated parameter and domain assumptions: `iteratedErfc n z=exp (-z^2)/((2 :
ℂ)^n*Real.sqrt π)*kummerU ((n : ℂ)/2+1/2) (1/2) (z^2)`. -/
@[dlmf 7.18.E10]
theorem iteratedErfc_kummerU (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    iteratedErfc n z=exp (-z^2)/((2 : ℂ)^n*Real.sqrt π)*kummerU ((n : ℂ)/2+1/2) (1/2) (z^2) := by
  let s : ℂ := Real.sqrt 2
  have hs : s^2=2 := by dsimp [s]; exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hspos : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs0 : s≠0 := by dsimp [s]; exact_mod_cast hspos.ne'
  rw [iteratedErfc_eq_pcfU_nat,pcfU_eq_kummerU _ (by simp only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]; positivity)]
  change 2/((Real.sqrt π:ℂ)*s^(n+1))*exp (-z^2/2)*
      ((2:ℂ)^(-(1/4)-((n:ℂ)+1/2)/2)*exp (-(s*z)^2/4)*
        kummerU (((n:ℂ)+1/2)/2+1/4) (1/2) ((s*z)^2/2)) = _
  rw [show (-(1/4)-((n:ℂ)+1/2)/2)=((-(n:ℤ)-1:ℤ):ℂ)/2 by push_cast; ring,
    two_cpow_int_half, mul_pow, hs,
    show (((n:ℂ)+1/2)/2+1/4)=(n:ℂ)/2+1/2 by ring,
    show (2*z^2)/2=z^2 by ring]
  have hscale : (2:ℂ)/s^(n+1)*s^(-(n:ℤ)-1)=1/(2:ℂ)^n := by
    rw [show -(n:ℤ)-1= -((n:ℤ)+1) by ring,zpow_neg,← Int.natCast_add_one,zpow_natCast]
    have hn : (s^(n+1))^2=(2:ℂ)^(n+1) := by
      rw [← pow_mul,mul_comm (n+1) 2,pow_mul,hs]
    calc
      2/s^(n+1)*(s^(n+1))⁻¹=2/((s^(n+1))^2) := by ring
      _ = _ := by rw [hn,pow_succ]; field_simp
  have he : exp (-z^2/2)*exp (-(2*z^2)/4)=exp (-z^2) := by rw [← Complex.exp_add]; congr 1; ring
  calc
    _ = (2/s^(n+1)*s^(-(n:ℤ)-1))/(Real.sqrt π:ℂ)*
        (exp (-z^2/2)*exp (-(2*z^2)/4))*kummerU ((n:ℂ)/2+1/2) (1/2) (z^2) := by ring
    _ = _ := by rw [hscale,he]; ring

/-- Identity under the stated parameter and domain assumptions: `iteratedErfc n z=exp (-z^2)/((2 :
ℂ)^n*Real.sqrt π)*kummerUOnLog ((n : ℂ)/2+1/2) (1/2) (2*log z)`. -/
@[dlmf 7.18.E10]
theorem iteratedErfc_kummerUOnLog (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    iteratedErfc n z=exp (-z^2)/((2 : ℂ)^n*Real.sqrt π)*kummerUOnLog ((n : ℂ)/2+1/2) (1/2) (2*log z) := by
  have hp0 : (Real.sqrt π:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hg : Gamma (-1/2:ℂ)= -2*(Real.sqrt π:ℂ) := by
    have h := Gamma_add_one (-1/2:ℂ) (by norm_num)
    rw [show (-1/2:ℂ)+1=1/2 by ring,Gamma_one_half_eq_sqrt] at h
    linear_combination 2*h
  have he : exp (2*log z)=z^2 := by simpa only [Nat.cast_ofNat,Complex.exp_log hz] using Complex.exp_nat_mul (log z) 2
  rw [iteratedErfc_kummerM,kummerUOnLog]
  norm_num only [show (1:ℂ)-1/2=1/2 by ring,show (1/2:ℂ)-1= -1/2 by ring,
    show (2:ℂ)-1/2=3/2 by ring]
  rw [show (n:ℂ)/2+1/2-1/2+1=n/2+1 by ring,
    show (1/2:ℂ)*(2*log z)=log z by ring,Complex.exp_log hz,he,
    Gamma_one_half_eq_sqrt,show -(1/2:ℂ)= -1/2 by ring,hg,zpow_sub₀ (by norm_num : (2:ℂ)≠0),zpow_natCast,zpow_one]
  field_simp [hp0]
  ring

/-- Identity under the stated parameter and domain assumptions: `iteratedErfc n z=exp (-z^2/2)/((2
: ℂ)^((n : ℤ)-1)*π)^(1/2 : ℂ)*pcfU (n+1/2) (z*Real.sqrt 2)`. -/
@[dlmf 7.18.E11]
theorem iteratedErfc_pcfU (n : ℕ) (z : ℂ) :
    iteratedErfc n z=exp (-z^2/2)/((2 : ℂ)^((n : ℤ)-1)*π)^(1/2 : ℂ)*pcfU (n+1/2) (z*Real.sqrt 2) := by
  rw [iteratedErfc_normalization, iteratedErfc_eq_pcfU_nat, mul_comm z (Real.sqrt 2:ℂ)]
  ring

/-- Identity under the stated parameter and domain assumptions: `iteratedErfc n
z=gaussianProbabilityHh n (Real.sqrt 2*z)/((2 : ℂ)^((n : ℤ)-1)*π)^(1/2 : ℂ)`. -/
@[dlmf 7.18.E12]
theorem iteratedErfc_probability (n : ℕ) (z : ℂ) :
    iteratedErfc n z=gaussianProbabilityHh n (Real.sqrt 2*z)/((2 : ℂ)^((n : ℤ)-1)*π)^(1/2 : ℂ) := by
  rw [iteratedErfc_normalization, gaussianProbabilityHh_sqrt_two,
    iteratedErfc, if_neg (by omega), if_neg (by omega)]
  simp only [Int.toNat_natCast]
  have hs0 : (Real.sqrt 2:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  field_simp [hs0]

/-- Continued-fraction representation: `HasContinuedFraction (fun k => if k=0 then 1/2 else (n+k :
ℂ)/2) (fun _ => z) (iteratedErfc n z/iteratedErfc ((n : ℤ)-1) z)`. -/
@[dlmf 7.18.E13]
theorem iteratedErfc_continuedFraction (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    HasContinuedFraction (fun k => if k=0 then 1/2 else (n+k : ℂ)/2) (fun _ => z) (iteratedErfc n z/iteratedErfc ((n : ℤ)-1) z) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  set aR : ℕ → ℕ → ℂ := fun n k => if k=0 then 1/2 else (n+k : ℂ)/2 with haR
  set ρ : ℕ → ℂ := fun n => iteratedErfc n z/iteratedErfc ((n : ℤ)-1) z with hρ
  have hpos : ∀ n k : ℕ, 1 ≤ k → aR n k = (((n + k : ℝ) / 2 : ℝ) : ℂ) := fun n k hk => by
    simp only [aR, show k ≠ 0 by omega, ↓reduceIte]; push_cast; ring
  have hpos' : ∀ n k : ℕ, 1 ≤ k → (0 : ℝ) < (n + k : ℝ) / 2 := fun n k hk => by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    positivity
  have hne : ∀ k, 1 ≤ k → aR n k ≠ 0 := fun k hk => by
    rw [hpos n k hk]; exact_mod_cast (hpos' n k hk).ne'
  rw [incGF_hasContinuedFraction_iff hne]
  suffices H : ∀ m, Tendsto (GenContFract.cfConv_ofFun 0 (aR m) (fun _ => z)).convs atTop
      (𝓝 (ρ m)) from H n
  intro m
  induction m with
  | zero =>
    -- the case `n = 0` is DLMF 7.9.1 after an equivalence transformation
    have h1 := erfc_continuedFraction_one hz
    rw [incGF_hasContinuedFraction_iff (fun k hk => by
      simp only [show k ≠ 0 by omega, ↓reduceIte]
      exact div_ne_zero (Nat.cast_ne_zero.mpr (by omega)) two_ne_zero)] at h1
    set r : ℕ → ℂ := fun k => if Even k then z⁻¹ else z with hr
    have hr0 : ∀ k, r k ≠ 0 := fun k => by
      simp only [r]; split_ifs
      · exact inv_ne_zero hz0
      · exact hz0
    set A1 : ℕ → ℂ := fun k => if k = 0 then 1 else (k : ℂ) / 2 with hA1
    have hEa : A1 = fun k => (if k = 0 then r 0 else r (k - 1) * r k) *
          (if k = 0 then z else (k : ℂ) / 2) := by
      funext k
      rcases k with _ | j
      · simp only [A1, r, ↓reduceIte, show Even 0 from ⟨0, rfl⟩]; field_simp
      · simp only [A1, r, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        rcases Nat.even_or_odd j with hj | hj
        · have hj' : ¬ Even (j + 1) := Nat.not_even_iff_odd.mpr hj.add_one
          simp only [hj, hj', ↓reduceIte]
          field_simp
        · have hj' : Even (j + 1) := hj.add_one
          have hj2 : ¬ Even j := Nat.not_even_iff_odd.mpr hj
          simp only [hj2, hj', ↓reduceIte]
          field_simp
    have hEb : (fun _ : ℕ => z) = fun k => r k * (if Even k then z ^ 2 else 1) := by
      funext k
      simp only [r]
      split_ifs
      · field_simp
      · rw [mul_one]
    have e0 : aR 0 = fun k : ℕ => if k = 0 then (1/2 : ℂ) * A1 0 else A1 k := by
      funext k; rcases k with _ | k <;> simp [aR, A1]
    have hconv : ∀ N, (GenContFract.cfConv_ofFun 0 (aR 0) (fun _ => z)).convs N =
        (1/2 : ℂ) * (GenContFract.cfConv_ofFun 0 (fun k => if k=0 then z else (k : ℂ)/2)
          (fun k => if Even k then z^2 else 1)).convs N := by
      intro N
      rw [e0, GenContFract.cfConv_convs_smul_a0, hEa, hEb, GenContFract.cfConv_equiv_convs r hr0]
    rw [show (GenContFract.cfConv_ofFun 0 (aR 0) (fun _ => z)).convs = fun N =>
      (1/2 : ℂ) * (GenContFract.cfConv_ofFun 0 (fun k => if k=0 then z else (k : ℂ)/2)
          (fun k => if Even k then z^2 else 1)).convs N from funext hconv]
    convert h1.const_mul (1/2 : ℂ) using 2
    obtain ⟨hm1, h0⟩ := iteratedErfc_initial z
    have hp : (Real.sqrt π : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
    simp only [ρ, Nat.cast_zero, zero_sub]
    rw [h0, hm1, show -z ^ 2 = -(z ^ 2) by ring, Complex.exp_neg]
    field_simp
  | succ m ih =>
    have hv : ρ m ≠ 0 := GenContFract.cfConv_sfrac_const_ne_zero hz (c := fun k => (m + k : ℝ) / 2)
      (fun k hk => hpos' m k hk) (fun k hk => hpos m k hk) (by simp [aR]) ih
    have ht := GenContFract.cfConv_tail_tendsto hv ih
    have e : aR (m + 1) = fun k => if k = 0 then ((m : ℂ) + 1)⁻¹ * aR m (0 + 1)
        else aR m (k + 1) := by
      funext k
      rcases k with _ | k
      · simp only [aR, ↓reduceIte, one_ne_zero, zero_add, Nat.cast_one]
        have : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
        field_simp
      · simp only [aR, Nat.succ_ne_zero, ↓reduceIte]; push_cast; ring
    rw [show (GenContFract.cfConv_ofFun 0 (aR (m + 1)) (fun _ => z)).convs = fun N =>
      ((m : ℂ) + 1)⁻¹ * (GenContFract.cfConv_ofFun 0 (fun k => aR m (k + 1))
        (fun _ => z)).convs N from funext fun N => by
          rw [e]
          exact GenContFract.cfConv_convs_smul_a0 (a := fun k => aR m (k + 1))
            (b := fun _ => z) _ N]
    convert ht.const_mul ((m : ℂ) + 1)⁻¹ using 2
    -- the three-term recurrence DLMF 7.18.7
    have hrec := iteratedErfc_recurrence (n := m + 1) (by omega) z
    have i1 : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by push_cast; ring
    have i2 : ((m + 1 : ℕ) : ℤ) - 2 = (m : ℤ) - 1 := by push_cast; ring
    rw [i1, i2] at hrec
    simp only [ρ] at hv ⊢
    rw [i1]
    set P := iteratedErfc (m : ℤ) z
    set Q := iteratedErfc ((m : ℤ) - 1) z
    have hP : P ≠ 0 := fun h0 => hv (by rw [h0, zero_div])
    have hQ : Q ≠ 0 := fun h0 => hv (by rw [h0, div_zero])
    have hm : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    rw [hrec]
    simp only [aR, ↓reduceIte]
    push_cast
    field_simp
    ring

/-- Integrability of the weighted Gaussian kernel `tⁿ e^{-t²/4}` along a ray `|arg t| < π/4`,
against any real exponential. -/
theorem erfRecip_integrableOn_pow_gauss_rotate (n : ℕ) (c : ℝ) {θ : ℝ} (hθ : |θ| < π / 4) :
    IntegrableOn (fun r : ℝ => Real.exp (-c * r) •
      ((((r : ℂ) * exp (θ * I)) ^ n) * cexp (-(((r : ℂ) * exp (θ * I)) ^ 2 / 4)))) (Ioi 0) := by
  obtain ⟨K, hK0, hK⟩ := exists_rpow_mul_exp_neg_le' (n : ℝ) one_pos
  have hint := (integrableOn_gauss_rotate (c - 1) hθ).norm.const_mul (max 1 K)
  refine hint.mono' (by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    fun_prop) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
  have hr : (0 : ℝ) < r := hr
  have hbound : r ^ n * Real.exp (-r) ≤ max 1 K := by
    rcases le_or_gt r 1 with h1 | h1
    · have : r ^ n ≤ 1 := pow_le_one₀ hr.le h1
      have : Real.exp (-r) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      calc r ^ n * Real.exp (-r) ≤ 1 * 1 := by gcongr
        _ ≤ _ := by simp
    · have := hK r h1.le
      rw [Real.rpow_natCast, neg_one_mul] at this
      exact this.trans (le_max_right _ _)
  rw [norm_smul, norm_smul, norm_mul, norm_pow, norm_mul, Complex.norm_real, norm_exp_ofReal_mul_I,
    mul_one, Real.norm_of_nonneg hr.le, Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  have he : Real.exp (-c * r) = (r ^ n * Real.exp (-r)) * Real.exp (-(c - 1) * r) / r ^ n := by
    rw [mul_assoc, ← Real.exp_add]
    field_simp
    ring_nf
  have hrn : 0 < r ^ n := pow_pos hr n
  calc Real.exp (-c * r) * (r ^ n * ‖cexp (-(((r : ℂ) * exp (θ * I)) ^ 2 / 4))‖)
      = (r ^ n * Real.exp (-r)) * (Real.exp (-(c - 1) * r) *
          ‖cexp (-(((r : ℂ) * exp (θ * I)) ^ 2 / 4))‖) := by
        rw [he]; field_simp
    _ ≤ max 1 K * (Real.exp (-(c - 1) * r) * ‖cexp (-(((r : ℂ) * exp (θ * I)) ^ 2 / 4))‖) := by
        gcongr
/-- Laplace form of the repeated erfc integral:
`iⁿerfc z = 2 π^{-1/2} e^{-z²} / (2^{n+1} n!) ∫₀^∞ e^{-zs} sⁿ e^{-s²/4} ds`. -/
theorem erfRecip_iteratedErfc_eq_laplace (n : ℕ) (z : ℂ) :
    iteratedErfc n z = 2 / Real.sqrt π * cexp (-z ^ 2) / (2 ^ (n + 1) * (n.factorial : ℂ)) *
      ∫ s in Ioi (0 : ℝ), cexp (-(z * s)) * ((s : ℂ) ^ n * cexp (-((s : ℂ) ^ 2 / 4))) := by
  have hn1 : (n : ℤ) ≠ -1 := by omega
  have hn0 : ¬ (n : ℤ) < 0 := by omega
  simp only [iteratedErfc, hn1, hn0, ↓reduceIte, Int.toNat_natCast]
  have h2 := integral_comp_mul_left_Ioi
    (fun t : ℝ => cexp (-(z * t)) * ((t : ℂ) ^ n * cexp (-((t : ℂ) ^ 2 / 4)))) 0
    (two_pos : (0 : ℝ) < 2)
  rw [mul_zero] at h2
  have hcomp : ∫ s in Ioi (0 : ℝ), cexp (-(z * ((2 * s : ℝ) : ℂ))) *
      ((((2 * s : ℝ) : ℂ)) ^ n * cexp (-((((2 * s : ℝ) : ℂ)) ^ 2 / 4))) =
      ∫ s in Ioi (0 : ℝ), (2 ^ n * (n.factorial : ℂ) * cexp (z ^ 2)) *
        ((s : ℂ) ^ n / (n.factorial : ℂ) * cexp (-(z + s) ^ 2)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    push_cast
    rw [mul_pow]
    field_simp
    have he : cexp (-(z * 2 * s)) * cexp (-(2 ^ 2 * (s : ℂ) ^ 2 / 4)) =
        cexp (z ^ 2) * cexp (-(z + s) ^ 2) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf
    linear_combination (s : ℂ) ^ n * he
  rw [hcomp, integral_const_mul] at h2
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hE : cexp (-z ^ 2) * cexp (z ^ 2) = 1 := by rw [← Complex.exp_add]; simp
  rw [Complex.real_smul] at h2
  generalize (∫ s in Ioi (0 : ℝ), cexp (-(z * s)) * ((s : ℂ) ^ n * cexp (-((s : ℂ) ^ 2 / 4)))) = I2
    at h2 ⊢
  generalize (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n / (n.factorial : ℂ) * cexp (-(z + t) ^ 2)) = I1
    at h2 ⊢
  push_cast at h2
  have hI2 : I2 = 2 * (2 ^ n * (n.factorial : ℂ) * cexp (z ^ 2) * I1) := by
    rw [h2]; ring
  rw [hI2]
  field_simp
  linear_combination (-(2 * 2 ^ n * I1)) * hE

/-- Rotated Laplace form of the repeated erfc integral, valid for every complex `z` and
`|θ| < π/4`. -/
theorem erfRecip_iteratedErfc_eq_rotate (n : ℕ) {θ : ℝ} (hθ : |θ| < π / 4) (z : ℂ) :
    iteratedErfc n z = 2 / Real.sqrt π * cexp (-z ^ 2) / (2 ^ (n + 1) * (n.factorial : ℂ)) *
      (exp (θ * I) * ∫ r in Ioi (0 : ℝ), cexp (-(z * exp (θ * I) * r)) *
        ((((r : ℂ) * exp (θ * I)) ^ n) * cexp (-(((r : ℂ) * exp (θ * I)) ^ 2 / 4)))) := by
  have hL : Differentiable ℂ (fun w : ℂ => ∫ r in Ioi (0 : ℝ), cexp (-(w * r)) •
      ((((r : ℂ) * exp (θ * I)) ^ n) * cexp (-(((r : ℂ) * exp (θ * I)) ^ 2 / 4)))) := fun w =>
    (differentiableOn_integral_cexp_neg_mul_smul
      (erfRecip_integrableOn_pow_gauss_rotate n (w.re - 1) hθ)).differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds (by simp))
  simp only [smul_eq_mul] at hL
  have hd2 : Differentiable ℂ (fun z : ℂ => 2 / Real.sqrt π * cexp (-z ^ 2) /
      (2 ^ (n + 1) * (n.factorial : ℂ)) * (exp (θ * I) * ∫ r in Ioi (0 : ℝ),
        cexp (-(z * exp (θ * I) * r)) *
        ((((r : ℂ) * exp (θ * I)) ^ n) * cexp (-(((r : ℂ) * exp (θ * I)) ^ 2 / 4))))) := by
    have := hL.comp (differentiable_id.mul_const (exp (θ * I)))
    exact (((differentiable_const _).mul (by fun_prop)).div_const _).mul
      ((differentiable_const _).mul this)
  have hreal : ∀ x : ℝ, 0 < x → iteratedErfc n x = 2 / Real.sqrt π * cexp (-(x : ℂ) ^ 2) /
      (2 ^ (n + 1) * (n.factorial : ℂ)) * (exp (θ * I) * ∫ r in Ioi (0 : ℝ),
        cexp (-((x : ℂ) * exp (θ * I) * r)) *
        ((((r : ℂ) * exp (θ * I)) ^ n) * cexp (-(((r : ℂ) * exp (θ * I)) ^ 2 / 4)))) := by
    intro x hx
    rw [erfRecip_iteratedErfc_eq_laplace n x]
    congr 1
    have hy : ∀ y ∈ [[0, θ]], |y| ≤ π / 4 := fun y hy =>
      (abs_le_abs_of_mem_uIcc_zero hy).trans hθ.le
    refine integral_cexp_neg_mul_mul_eq_rotate (F := fun t => t ^ n * cexp (-(t ^ 2 / 4)))
      (σ := 1) (C := 1) (k := n) one_pos (fun r _ y _ => by fun_prop)
      (fun r hr hr1 y hy' => ?_) (fun r hr y hy' => ?_) (fun y hy' => ?_)
    · rw [sub_self, Real.rpow_zero, mul_one, norm_mul, norm_pow, norm_mul, Complex.norm_real,
        norm_exp_ofReal_mul_I, mul_one, Real.norm_of_nonneg hr.le]
      have h1 : r ^ n ≤ 1 := pow_le_one₀ hr.le hr1
      have h2 := norm_cexp_neg_ofReal_mul_exp_ofReal_mul_I_sq_le_one r (hy y hy')
      calc r ^ n * _ ≤ 1 * 1 := by gcongr
        _ = 1 := one_mul 1
    · rw [one_mul, Real.rpow_natCast, norm_mul, norm_pow, norm_mul, Complex.norm_real,
        norm_exp_ofReal_mul_I, mul_one, Real.norm_of_nonneg (by linarith)]
      have h2 := norm_cexp_neg_ofReal_mul_exp_ofReal_mul_I_sq_le_one r (hy y hy')
      calc r ^ n * _ ≤ r ^ n * 1 := by gcongr
        _ = r ^ n := mul_one _
    · rw [re_ofReal_mul, exp_ofReal_mul_I_re]
      have := hy y hy'
      exact mul_pos hx (Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le y, Real.pi_pos],
        by linarith [le_abs_self y, Real.pi_pos]⟩)
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), iteratedErfc n w = 2 / Real.sqrt π * cexp (-w ^ 2) /
      (2 ^ (n + 1) * (n.factorial : ℂ)) * (exp (θ * I) * ∫ r in Ioi (0 : ℝ),
        cexp (-(w * exp (θ * I) * r)) *
        ((((r : ℂ) * exp (θ * I)) ^ n) * cexp (-(((r : ℂ) * exp (θ * I)) ^ 2 / 4)))) := by
    have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have := (continuous_ofReal.tendsto (1 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := ({1}ᶜ : Set ℝ)))
        rwa [ofReal_one] at this
      · filter_upwards [self_mem_nhdsWithin] with r hr
        simpa using hr
    apply ht.frequently
    apply Eventually.frequently
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one' ℝ))] with r hr
    exact hreal r hr
  exact ((differentiable_iteratedErfc n).differentiableOn.analyticOnNhd isOpen_univ
    ).eqOn_of_preconnected_of_frequently_eq
    (hd2.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (mem_univ _) hfreq
    (mem_univ z)

/-- Taylor remainders of `tⁿ e^{-t²/4}` along a ray, in the form required by Watson's lemma
with `μ = n + 1`. -/
theorem erfRecip_pow_gauss_sub_sum_isBigO (n : ℕ) (θ : ℝ) (N : ℕ) :
    (fun r : ℝ => ((r : ℂ) * exp (θ * I)) ^ n * cexp (-(((r : ℂ) * exp (θ * I)) ^ 2 / 4)) -
      ∑ k ∈ Finset.range N,
        (((r : ℂ) * exp (θ * I)) ^ ((k : ℂ) + ((n : ℂ) + 1) - 1)) • gaussQuarterCoeff k)
      =O[𝓝[>] 0] fun r => r ^ ((N : ℝ) + ((n : ℂ) + 1).re - 1) := by
  have h1 : (fun r : ℝ => ((r : ℂ) * exp (θ * I)) ^ n) =O[𝓝[>] 0] fun r : ℝ => r ^ n := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun r => ?_)
    rw [norm_pow, norm_mul, Complex.norm_real, norm_exp_ofReal_mul_I, mul_one, norm_pow, one_mul]
  have h := h1.mul (gauss_sub_sum_isBigO θ N)
  refine h.congr' (Eventually.of_forall fun r => ?_) ?_
  · simp only [add_sub_cancel_right, cpow_natCast, smul_eq_mul, mul_sub,
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show (k : ℂ) + ((n : ℂ) + 1) - 1 = ((k + n : ℕ) : ℂ) by push_cast; ring, cpow_natCast,
      pow_add]
    ring
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have hr : (0 : ℝ) < r := hr
    simp only [one_re, add_sub_cancel_right, add_re, natCast_re]
    rw [← Real.rpow_natCast, ← Real.rpow_add hr]
    congr 1
    ring

/-- `iⁿerfc z ~ 2π^{-1/2} e^{-z²} ∑ (-1)ᵐ (2m+n)!/(n! m!) (2z)^{-n-1-2m}` in a rotated sector. -/
theorem erfRecip_iteratedErfc_rotSector (n : ℕ) {θ δ : ℝ} (hθ : |θ| < π / 4) (hδ : 0 < δ) :
    HasAsymptoticExpansion (comap (fun z : ℂ => z * exp (θ * I)) (sectorAtTop δ))
      (fun m z => 2 / Real.sqrt π * exp (-z ^ 2) / (2 * z) ^ (n + 1 + 2 * m))
      (fun m => (-1 : ℂ) ^ m * (2 * m + n).factorial / ((n.factorial : ℂ) * m.factorial))
      (iteratedErfc n) := by
  have hθ' : |θ| < π / 2 := by linarith [Real.pi_pos]
  have hW := hasAsymptoticExpansion_integral_cexp_smul_rotate_comap
    (F := fun t => t ^ n * cexp (-(t ^ 2 / 4))) (a := gaussQuarterCoeff) (μ := (n : ℂ) + 1)
    (c := 0) hθ' (by simp; positivity) hδ (erfRecip_integrableOn_pow_gauss_rotate n 0 hθ)
    (erfRecip_pow_gauss_sub_sum_isBigO n θ)
  have hE := hW.even (fun m => by
    have : ¬ Even (2 * m + 1) := by simp
    simp [gaussQuarterCoeff, this])
  set c0 : ℂ := 2 / Real.sqrt π / (2 ^ (n + 1) * (n.factorial : ℂ)) with hc0
  have h3 := (hE.const_smul c0).mul_left (fun z : ℂ => cexp (-z ^ 2))
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  refine ((h3.congr' (Eventually.of_forall fun z => ?_)).smul_scale
    (κ := fun m => (Real.sqrt π / 2 : ℂ) * 2 ^ (n + 1 + 2 * m))
    (ψ := fun m z => 2 / Real.sqrt π * exp (-z ^ 2) / (2 * z) ^ (n + 1 + 2 * m))
    fun m => Eventually.of_forall fun z => ?_).congr_coeff ?_
  · simp only [Pi.smul_apply, smul_eq_mul]
    rw [erfRecip_iteratedErfc_eq_rotate n hθ z, hc0]
    ring
  · simp only
    rw [show -(((2 * m : ℕ) : ℂ) + ((n : ℂ) + 1)) = -((n + 1 + 2 * m : ℕ) : ℂ) by push_cast; ring,
      cpow_neg, cpow_natCast, mul_pow]
    field_simp
  · funext m
    have hm : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    simp only [Pi.smul_apply, smul_eq_mul, gaussQuarterCoeff, even_two_mul, ite_true,
      show 2 * m / 2 = m by omega, hc0]
    rw [show ((2 * m : ℕ) : ℂ) + ((n : ℂ) + 1) = ((2 * m + n : ℕ) : ℂ) + 1 by push_cast; ring,
      Complex.Gamma_nat_eq_factorial]
    rw [div_pow, pow_add 2 (n + 1), pow_mul]
    have h4 : (4 : ℂ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
    norm_num
    field_simp

/-- Identity under the stated parameter and domain assumptions: `HasAsymptoticExpansion (sector
(3*π/4-δ)) (fun m z => 2/Real.sqrt π*exp (-z^2)/(2*z)^(n+1+2*m)) (fun m => (-1 :
ℂ)^m*(2*m+n).factorial/((n.factorial : ℂ)*m.factorial)) (iteratedErfc n)`. -/
@[dlmf 7.18.E14]
theorem iteratedErfc_asymptotic (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 3*π/4) :
    HasAsymptoticExpansion (sector (3*π/4-δ)) (fun m z => 2/Real.sqrt π*exp (-z^2)/(2*z)^(n+1+2*m)) (fun m => (-1 : ℂ)^m*(2*m+n).factorial/((n.factorial : ℂ)*m.factorial)) (iteratedErfc n) := by
  set d := min δ (π / 4) with hd
  have hd0 : 0 < d := lt_min hδ (by positivity)
  have hdδ : d ≤ δ := min_le_left _ _
  have hdπ : d ≤ π / 4 := min_le_right _ _
  have hcov := le_sup_comap_rotate (α := 3 * π / 4 - δ) (β := π / 4 - d / 2) (γ := π / 2 - d / 2)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have hcos : 0 < Real.cos (π / 2 - d / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hβ : |π / 4 - d / 2| < π / 4 := by
    rw [abs_lt]; constructor <;> linarith
  have h1 := erfRecip_iteratedErfc_rotSector n (θ := -(π / 4 - d / 2)) (by rwa [abs_neg]) hcos
  have h2 := erfRecip_iteratedErfc_rotSector n (θ := π / 4 - d / 2) hβ hcos
  exact (h1.sup h2).mono hcov

end DLMF.Confluent
