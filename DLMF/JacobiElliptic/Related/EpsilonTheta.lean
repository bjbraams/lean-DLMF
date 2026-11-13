/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Basic.EpsilonProperties
public import DLMF.JacobiElliptic.Basic.Definitions
import DLMF.JacobiElliptic.Addition.ThetaAndQuotients
import DLMF.JacobiElliptic.SpecialValues.RealAndHalfPeriods
import DLMF.Theta.ZeroValues
import DLMFMathlib.Analysis.Calculus.Deriv.MulComp
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Jacobi's Epsilon as a theta logarithmic derivative

Differentiating theta addition twice gives the derivative of the normalized logarithmic
derivative of `θ₄`. Comparing this with the derivative of Jacobi's Epsilon and evaluating
at `2K` gives DLMF 22.16.30.
-/

public section

set_option maxHeartbeats 0
open Complex Filter DLMF.EllipticIntegrals DLMF.Elliptic DLMF.Theta
open scoped Real Topology
namespace DLMF.JacobiElliptic.EpsilonTheta

/-- The second derivative of theta addition at a zero increment. -/
lemma thetaFour_second_relation {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiThetaFourTau 0 τ ^ 2 *
        (jacobiThetaFourTau z τ * deriv (deriv (fun w => jacobiThetaFourTau w τ)) z -
          deriv (fun w => jacobiThetaFourTau w τ) z ^ 2) =
      jacobiThetaFourTau z τ ^ 2 * jacobiThetaFourTau 0 τ *
        deriv (deriv (fun w => jacobiThetaFourTau w τ)) 0 -
      jacobiThetaOneTau z τ ^ 2 * deriv (fun w => jacobiThetaOneTau w τ) 0 ^ 2 := by
  let f : ℂ → ℂ := fun w => jacobiThetaFourTau w τ
  let g : ℂ → ℂ := fun w => jacobiThetaOneTau w τ
  have hf (x : ℂ) : AnalyticAt ℂ f x := by
    simpa only [f, jacobiThetaTau] using (differentiable_jacobiThetaTau 4 hτ).analyticAt x
  have hg (x : ℂ) : AnalyticAt ℂ g x := by
    simpa only [g, jacobiThetaTau] using (differentiable_jacobiThetaTau 1 hτ).analyticAt x
  have hsquare (F : ℂ → ℂ) (C : ℂ) (hF : AnalyticAt ℂ F 0) :
      deriv (deriv (fun w => C * F w * F w)) 0 =
        2 * C * deriv F 0 ^ 2 + 2 * C * F 0 * deriv (deriv F) 0 := by
    have h := deriv_deriv_mul_comp_mul_comp
      (P := fun _ : ℂ => C) (P1 := fun _ => 0) (P2 := 0)
      (u := fun w => w) (u1 := fun _ => 1) (u2 := 0)
      (v := fun w => w) (v1 := fun _ => 1) (v2 := 0)
      (F := F) (G := F) (z := 0)
      (Eventually.of_forall fun w => hasDerivAt_const w C) (hasDerivAt_const 0 0)
      (Eventually.of_forall fun w => hasDerivAt_id w) (hasDerivAt_const 0 1)
      (Eventually.of_forall fun w => hasDerivAt_id w) (hasDerivAt_const 0 1) hF hF
    simp only [zero_mul, mul_zero, zero_add, add_zero, one_pow, mul_one] at h
    linear_combination h.2
  have hleft := deriv_deriv_mul_comp_mul_comp
    (P := fun _ : ℂ => f 0 ^ 2) (P1 := fun _ => 0) (P2 := 0)
    (u := fun w => z + w) (u1 := fun _ => 1) (u2 := 0)
    (v := fun w => z - w) (v1 := fun _ => -1) (v2 := 0)
    (F := f) (G := f) (z := 0)
    (Eventually.of_forall fun w => hasDerivAt_const w (f 0 ^ 2)) (hasDerivAt_const 0 0)
    (Eventually.of_forall fun w => (hasDerivAt_id w).const_add z) (hasDerivAt_const 0 1)
    (Eventually.of_forall fun w => (hasDerivAt_id w).const_sub z) (hasDerivAt_const 0 (-1))
    (by simpa only [add_zero] using hf z) (by simpa only [sub_zero] using hf z)
  let R0 : ℂ → ℂ := fun w => f z ^ 2 * f w * f w
  let R1 : ℂ → ℂ := fun w => g z ^ 2 * g w * g w
  have hR0 : Differentiable ℂ R0 := by
    intro w
    exact (((hf w).differentiableAt.const_mul _).mul (hf w).differentiableAt)
  have hR1 : Differentiable ℂ R1 := by
    intro w
    exact (((hg w).differentiableAt.const_mul _).mul (hg w).differentiableAt)
  have hsub : deriv (deriv (fun w => R0 w - R1 w)) 0 =
      deriv (deriv R0) 0 - deriv (deriv R1) 0 := by
    have hd : deriv (fun w => R0 w - R1 w) = fun w => deriv R0 w - deriv R1 w :=
      funext fun w => deriv_sub (hR0 w) (hR1 w)
    rw [hd]
    have heq : (fun w => deriv R0 w - deriv R1 w) = deriv R0 - deriv R1 := rfl
    rw [heq]
    exact deriv_sub ((hR0.analyticAt 0).deriv.differentiableAt)
      ((hR1.analyticAt 0).deriv.differentiableAt)
  have heq : (fun w => f 0 ^ 2 * f (z + w) * f (z - w)) = fun w => R0 w - R1 w := by
    funext w
    simpa only [f, g, R0, R1, pow_two, mul_assoc] using
      jacobiThetaFourTau_add_mul_jacobiThetaFourTau_sub z w τ hτ
  have hd2 := congrArg (fun F : ℂ → ℂ => deriv (deriv F) 0) heq
  rw [hsub, hsquare f (f z ^ 2) (hf 0), hsquare g (g z ^ 2) (hg 0)] at hd2
  rw [hleft.2] at hd2
  have hf0 : deriv f 0 = 0 := (jacobiTheta_zero_values τ).2.2.2
  have hg0 : g 0 = 0 := jacobiThetaOneTau_zero τ
  simp only [hf0, hg0, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero,
    sub_zero, add_zero, zero_add, add_zero, sub_zero, neg_one_sq, one_pow, mul_one,
    add_zero, sub_zero] at hd2
  dsimp only [f, g] at hd2
  linear_combination hd2 / 2

/-- The logarithmic derivative of `θ₄` has a derivative determined by theta addition. -/
lemma hasDerivAt_thetaFour_logDeriv {τ z : ℂ} (hτ : 0 < τ.im)
    (hz : jacobiThetaFourTau z τ ≠ 0) :
    HasDerivAt (fun w => deriv (fun u => jacobiThetaFourTau u τ) w / jacobiThetaFourTau w τ)
      (deriv (deriv (fun u => jacobiThetaFourTau u τ)) 0 / jacobiThetaFourTau 0 τ -
        (deriv (fun u => jacobiThetaOneTau u τ) 0) ^ 2 / jacobiThetaFourTau 0 τ ^ 2 *
          (jacobiThetaOneTau z τ / jacobiThetaFourTau z τ) ^ 2) z := by
  have hf : AnalyticAt ℂ (fun w => jacobiThetaFourTau w τ) z := by
    simpa only [jacobiThetaTau] using (differentiable_jacobiThetaTau 4 hτ).analyticAt z
  have hd := hf.deriv.differentiableAt.hasDerivAt.div hf.differentiableAt.hasDerivAt hz
  have h0 := jacobiThetaFourTau_zero_ne_zero hτ
  have heq := thetaFour_second_relation hτ z
  refine hd.congr_deriv ?_
  field_simp [h0, hz]
  linear_combination heq

/-- The normalized theta logarithmic derivative has derivative `C - k² sn²`. -/
lemma hasDerivAt_normalized_thetaFour_logDeriv {k z : ℂ} (hk : k ∈ jacobiModulusDomain)
    (hz : IsJacobiRegular .n z k) :
    let τ := jacobiTau k
    let A := jacobiThetaThreeTau 0 τ ^ 2
    HasDerivAt (fun w => deriv (fun u => jacobiThetaFourTau u τ) (w / A) /
        (A * jacobiThetaFourTau (w / A) τ))
      (deriv (deriv (fun u => jacobiThetaFourTau u τ)) 0 /
        (A ^ 2 * jacobiThetaFourTau 0 τ) - k ^ 2 * jacobiSn z k ^ 2) z := by
  dsimp only
  let τ := jacobiTau k
  let A := jacobiThetaThreeTau 0 τ ^ 2
  have hτ : 0 < τ.im := jacobiTau_im_pos hk
  have hK := (jacobi_inversion_k hk).2.2
  have harg (w : ℂ) : jacobiThetaArgument w k = w / A := by
    rw [jacobiThetaArgument, ← hK, completeEllipticKOfTau]
    dsimp only [τ, A]
    field_simp [ofReal_ne_zero.mpr Real.pi_ne_zero,
      jacobiThetaThreeTau_zero_ne_zero hτ]
  have hz4 : jacobiThetaFourTau (z / A) τ ≠ 0 := by
    have hzn := hz
    rw [IsJacobiRegular, jacobiLetterTheta, harg] at hzn
    exact (div_ne_zero_iff.mp hzn).1
  have hd := ((hasDerivAt_thetaFour_logDeriv hτ hz4).comp z
    ((hasDerivAt_id z).div_const A)).div_const A
  have hmod := (jacobi_inversion_k hk).1
  rw [jacobiModulusOfTau] at hmod
  have hzero := jacobiThetaOneDerivNullTau_eq_mul hτ
  simp only [jacobiThetaOneDerivNullTau, jacobiThetaTwoNullTau,
    jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at hzero
  have hT2 := jacobiThetaTwoTau_zero_ne_zero hτ
  have hT3 := jacobiThetaThreeTau_zero_ne_zero hτ
  have hT4 := jacobiThetaFourTau_zero_ne_zero hτ
  have heqfun : (fun w : ℂ => deriv (fun u => jacobiThetaFourTau u τ) (w / A) /
        (A * jacobiThetaFourTau (w / A) τ)) =
      fun w => (deriv (fun u => jacobiThetaFourTau u τ) (w / A) /
        jacobiThetaFourTau (w / A) τ) / A := by
    funext w
    rw [div_div, mul_comm A]
  rw [heqfun]
  refine hd.congr_deriv ?_
  rw [hzero]
  simp only [jacobiSn, jacobiPQ, jacobiGlaisher, reduceCtorEq, ↓reduceIte,
    jacobiLetterTheta, harg]
  dsimp only [A, τ] at hmod hT2 hT3 hT4 hz4 ⊢
  field_simp [hT2, hT3, hT4, hz4] at hmod ⊢
  have hmod4 : jacobiThetaTwoTau 0 (jacobiTau k) ^ 4 =
      jacobiThetaThreeTau 0 (jacobiTau k) ^ 4 * k ^ 2 := by
    calc
      _ = (jacobiThetaTwoTau 0 (jacobiTau k) ^ 2) ^ 2 := by ring_nf
      _ = _ := by rw [hmod]; ring_nf
  linear_combination -jacobiThetaThreeTau 0 (jacobiTau k) ^ 2 *
    jacobiThetaFourTau 0 (jacobiTau k) *
    jacobiThetaOneTau (z / jacobiThetaThreeTau 0 (jacobiTau k) ^ 2) (jacobiTau k) ^ 2 * hmod4

/-- Jacobi's Epsilon equals a normalized theta logarithmic derivative plus `(E/K)x`. -/
lemma epsilon_eq_theta {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (x : ℝ) :
    (Real.jacobiEpsilon x k : ℂ) =
      deriv (fun ξ => jacobiThetaFourTau ξ (jacobiTau k))
          (x / jacobiThetaThreeTau 0 (jacobiTau k) ^ 2) /
        (jacobiThetaThreeTau 0 (jacobiTau k) ^ 2 *
          jacobiThetaFourTau (x / jacobiThetaThreeTau 0 (jacobiTau k) ^ 2) (jacobiTau k)) +
      (Real.completeEllipticEOfParameter (k ^ 2) /
        Real.completeEllipticKOfParameter (k ^ 2) * x : ℝ) := by
  let τ := jacobiTau (k : ℂ)
  let A := jacobiThetaThreeTau 0 τ ^ 2
  let K := Real.completeEllipticKOfParameter (k ^ 2)
  let E := Real.completeEllipticEOfParameter (k ^ 2)
  let Γ : ℂ → ℂ := fun z => deriv (fun w => jacobiThetaFourTau w τ) (z / A) /
    (A * jacobiThetaFourTau (z / A) τ)
  let C := deriv (deriv (fun w => jacobiThetaFourTau w τ)) 0 /
    (A ^ 2 * jacobiThetaFourTau 0 τ)
  have hm : k ^ 2 < 1 := by nlinarith [hk0, hk1]
  have hk := ofReal_mem_jacobiModulusDomain hk0 hk1
  have hτ : 0 < τ.im := jacobiTau_im_pos hk
  have hKpos : 0 < K := Real.completeEllipticKOfParameter_pos hm
  have hscale : A = ((2 * K / π : ℝ) : ℂ) := by
    have h := (jacobi_inversion_k hk).2.2
    rw [completeEllipticKOfTau, completeEllipticK_ofReal hm] at h
    dsimp only [A, τ, K]
    push_cast
    apply (eq_div_iff (ofReal_ne_zero.mpr Real.pi_ne_zero)).2
    linear_combination 2 * h
  have harg (z : ℂ) : jacobiThetaArgument z (k : ℂ) = z / A := by
    rw [jacobiThetaArgument, completeEllipticK_ofReal hm, hscale]
    dsimp only [K]
    push_cast
    field_simp [ofReal_ne_zero.mpr Real.pi_ne_zero,
      ofReal_ne_zero.mpr (ne_of_gt hKpos)]
  have hnonzero (u : ℝ) : jacobiThetaFourTau (u : ℂ) τ ≠ 0 := by
    rw [Ne, (DLMF.Theta.jacobiThetaTau_eq_zero_iff hτ _).2.2.2]
    rintro ⟨m, n, he⟩
    have hi := congrArg Complex.im he
    simp only [ofReal_im, mul_im, add_im, intCast_im, ofReal_re, intCast_re, div_ofNat_re,
      div_ofNat_im, add_re, mul_zero, zero_add, one_re, one_im] at hi
    have hn : (2 : ℝ) * (n : ℝ) + 1 = 0 := by
      have hi' : ((n : ℝ) + 1 / 2) * τ.im * π = 0 := by simpa using hi.symm
      have ht : (n : ℝ) + 1 / 2 = 0 :=
        (mul_eq_zero.mp ((mul_eq_zero.mp hi').resolve_right Real.pi_ne_zero)).resolve_right
          (ne_of_gt hτ)
      linarith
    have hn' : (2 : ℤ) * n + 1 = 0 := by exact_mod_cast hn
    omega
  have hregular (u : ℝ) : IsJacobiRegular .n (u : ℂ) (k : ℂ) := by
    rw [IsJacobiRegular, jacobiLetterTheta, harg]
    refine div_ne_zero ?_ (jacobiThetaFourTau_zero_ne_zero hτ)
    rw [hscale, ← ofReal_div]
    exact hnonzero _
  have hdΓ (u : ℝ) : HasDerivAt (fun u : ℝ => Γ (u : ℂ))
      (C - (k : ℂ) ^ 2 * jacobiSn (u : ℂ) (k : ℂ) ^ 2) u :=
    (hasDerivAt_normalized_thetaFour_logDeriv hk (hregular u)).comp_ofReal
  have hΓ0 : Γ 0 = 0 := by
    dsimp only [Γ]
    rw [zero_div, (jacobiTheta_zero_values τ).2.2.2, zero_div]
  let G : ℝ → ℂ := fun u => (Real.jacobiEpsilon u k : ℂ) - Γ (u : ℂ) -
    (1 - C) * (u : ℂ)
  have hdG (u : ℝ) : HasDerivAt G 0 u := by
    have he := (Real.hasDerivAt_jacobiEpsilon hm u).ofReal_comp
    have hl := ((hasDerivAt_id u).ofReal_comp).const_mul (1 - C)
    have hd := (he.sub (hdΓ u)).sub hl
    refine hd.congr_deriv ?_
    rw [jacobiSn_ofReal hk0 hk1]
    have h := Real.mul_jacobiSnOfParameter_sq_add_jacobiDnOfParameter_sq hm u
    have hc : (k : ℂ) ^ 2 * (Real.jacobiSnOfParameter u (k ^ 2) : ℂ) ^ 2 +
        (Real.jacobiDnOfParameter u (k ^ 2) : ℂ) ^ 2 = 1 := by exact_mod_cast h
    push_cast
    linear_combination hc
  have hvalue (u : ℝ) : (Real.jacobiEpsilon u k : ℂ) = Γ (u : ℂ) + (1 - C) * (u : ℂ) := by
    have h := is_const_of_deriv_eq_zero (fun u => (hdG u).differentiableAt)
      (fun u => (hdG u).deriv) u 0
    dsimp only [G] at h
    rw [Real.jacobiEpsilon_zero, ofReal_zero, hΓ0, mul_zero, sub_zero, sub_zero] at h
    linear_combination h
  have hΓperiod : Γ (2 * K : ℝ) = 0 := by
    have hperiod : (fun z : ℂ => jacobiThetaFourTau (z + π) τ) =
        fun z => jacobiThetaFourTau z τ :=
      funext fun z => jacobiThetaFourTau_add_pi z τ
    have hd := congrArg (fun F : ℂ → ℂ => deriv F 0) hperiod
    have hf : DifferentiableAt ℂ (fun z => jacobiThetaFourTau z τ) (π : ℂ) := by
      simpa only [jacobiThetaTau] using differentiable_jacobiThetaTau 4 hτ (π : ℂ)
    have hshift := (hf.hasDerivAt.comp_of_eq (h := fun z : ℂ => z + π) 0
      ((hasDerivAt_id (0 : ℂ)).add_const (π : ℂ)) (by simp)).deriv
    simp only [Function.comp_def, mul_one] at hshift
    rw [hshift, (jacobiTheta_zero_values τ).2.2.2] at hd
    have ha : ((2 * K : ℝ) : ℂ) / A = π := by
      rw [hscale]
      push_cast
      field_simp [ne_of_gt hKpos]
    dsimp only [Γ]
    rw [ha, hd, zero_div]
  have hcoefficient : 1 - C = ((E / K : ℝ) : ℂ) := by
    have hp := Real.jacobiEpsilon_add_two_completeEllipticKOfParameter hm 0
    simp only [zero_add, Real.jacobiEpsilon_zero] at hp
    have hv := hvalue (2 * K)
    rw [hΓperiod, hp, zero_add] at hv
    dsimp only [E, K] at *
    push_cast at hv ⊢
    apply (eq_div_iff (ofReal_ne_zero.mpr (ne_of_gt hKpos))).2
    linear_combination -hv / 2
  rw [hcoefficient] at hvalue
  simpa only [Γ, τ, A, ofReal_mul, ofReal_div, E, K] using hvalue x

/-- The normalized second logarithmic derivative at zero equals `1 - E/K`. -/
lemma thetaFour_second_deriv_zero_div_eq {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    deriv (deriv (fun w => jacobiThetaFourTau w (jacobiTau k))) 0 /
        (jacobiThetaThreeTau 0 (jacobiTau k) ^ 4 * jacobiThetaFourTau 0 (jacobiTau k)) =
      1 - (Real.completeEllipticEOfParameter (k ^ 2) : ℂ) /
        completeEllipticK (k : ℂ) := by
  have hm : k ^ 2 < 1 := by nlinarith [hk0, hk1]
  have hk := ofReal_mem_jacobiModulusDomain hk0 hk1
  have hr : IsJacobiRegular .n 0 (k : ℂ) := by
    rw [IsJacobiRegular, jacobiLetterTheta, jacobiThetaArgument, mul_zero, zero_div]
    exact div_ne_zero (jacobiThetaFourTau_zero_ne_zero (jacobiTau_im_pos hk))
      (jacobiThetaFourTau_zero_ne_zero (jacobiTau_im_pos hk))
  have hd := (hasDerivAt_normalized_thetaFour_logDeriv hk hr).comp_ofReal
  simp only [jacobiSn_zero hk, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero,
    sub_zero] at hd
  have hl := ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul
    ((Real.completeEllipticEOfParameter (k ^ 2) : ℂ) /
      (Real.completeEllipticKOfParameter (k ^ 2) : ℂ))
  have he := (Real.hasDerivAt_jacobiEpsilon hm 0).ofReal_comp
  have heq : (fun x : ℝ => (Real.jacobiEpsilon x k : ℂ)) = fun x : ℝ =>
      deriv (fun ξ => jacobiThetaFourTau ξ (jacobiTau k))
          (x / jacobiThetaThreeTau 0 (jacobiTau k) ^ 2) /
        (jacobiThetaThreeTau 0 (jacobiTau k) ^ 2 *
          jacobiThetaFourTau (x / jacobiThetaThreeTau 0 (jacobiTau k) ^ 2) (jacobiTau k)) +
      ((Real.completeEllipticEOfParameter (k ^ 2) : ℂ) /
        (Real.completeEllipticKOfParameter (k ^ 2) : ℂ)) * x := by
    funext x
    simpa only [ofReal_mul, ofReal_div] using epsilon_eq_theta hk0 hk1 x
  rw [heq] at he
  have h := he.unique ((hd.add hl).congr_of_eventuallyEq
    (Eventually.of_forall fun _ => rfl))
  simp only [Real.jacobiDnOfParameter, Real.jacobiSnOfParameter_zero hm,
    zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, sub_zero, Real.one_rpow, one_pow,
    ofReal_one, mul_one] at h
  have hpow : jacobiThetaThreeTau 0 (jacobiTau k) ^ 4 =
      (jacobiThetaThreeTau 0 (jacobiTau k) ^ 2) ^ 2 := by ring_nf
  rw [hpow, completeEllipticK_ofReal hm]
  linear_combination -h

end DLMF.JacobiElliptic.EpsilonTheta
