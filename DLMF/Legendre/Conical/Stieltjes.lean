/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Stieltjes
public import DLMF.Legendre.Basic.Associated
public import DLMF.Core.Basic
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The self-Stieltjes representation of a conical function

The substitution `t = 1+2u` turns the Gauss self-Stieltjes identity into DLMF 14.20.13
for every real `τ` and `x > 1`. Gamma reflection gives the factor `cosh(πτ)/π`.
The half-line integral is absolutely convergent, and therefore converges as an ordinary
improper integral.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory DLMF.Hypergeometric
open scoped Real Topology Nat ComplexConjugate
open DLMF.Hypergeometric.GaussMoments DLMF.Core

namespace DLMF.Legendre.ConicalStieltjes

/-- The conical self-Stieltjes integral converges absolutely and has the stated improper value. -/
lemma hasIntegralAtTop (τ : ℝ) {x : ℝ} (hx : 1 < x) :
    HasIntegralAtTop (fun t : ℝ => Real.cosh (τ*π)/π*associatedP (-1/2+I*τ) 0 t/(x+t)) 1
      (associatedP (-1/2+I*τ) 0 x) := by
  set a : ℂ := 1/2+I*τ with hadef
  set w : ℝ := (x-1)/2 with hwdef
  set C : ℂ := Real.cosh (τ*π)/π with hCdef
  let f : ℝ → ℂ := fun t => C*associatedP (-1/2+I*τ) 0 t/(x+t)
  have ha0 : 0 < a.re := by norm_num [hadef]
  have ha1 : a.re < 1 := by norm_num [hadef]
  have hw : 0 < w := by dsimp [w];linarith
  have hP (t : ℝ) : associatedP (-1/2+I*τ) 0 t =
      regularizedGaussHypergeometric a (1-a) 1 ((1-(t:ℂ))/2) := by
    simp only [associatedP,zero_div,zero_mul,exp_zero,one_mul,sub_zero]
    congr 1 <;> dsimp [a] <;> ring
  have hsin : sin (π*a) = (Real.cosh (τ*π):ℂ) := by
    rw [show (π:ℂ)*a = ((π/2:ℝ):ℂ)+((τ*π:ℝ):ℂ)*I by dsimp [a];push_cast;ring,
      sin_add_mul_I,←ofReal_sin,←ofReal_cos,←ofReal_cosh,Real.sin_pi_div_two,Real.cos_pi_div_two]
    simp
  have hC : C*(Gamma a*Gamma (1-a)) = 1 := by
    rw [Gamma_mul_Gamma_one_sub,hsin]
    dsimp [C]
    have hc0 : (Real.cosh (τ*π):ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.cosh_pos _).ne'
    have hp0 : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
  have himage : (fun u : ℝ => 1+2*u) '' Ioi 0 = Ioi 1 := by
    ext t
    constructor
    · rintro ⟨u,hu,rfl⟩
      have hu : 0 < u := hu
      change 1 < 1+2*u
      linarith
    · intro ht
      have ht : 1 < t := ht
      refine ⟨(t-1)/2,by change 0 < (t-1)/2;linarith,?_⟩
      dsimp
      ring
  have hd (u : ℝ) (_hu : u ∈ Ioi (0:ℝ)) :
      HasDerivWithinAt (fun u : ℝ => 1+2*u) 2 (Ioi 0) u := by
    simpa using (((hasDerivAt_id u).const_mul 2).const_add 1).hasDerivWithinAt
  have hinj : InjOn (fun u : ℝ => 1+2*u) (Ioi (0:ℝ)) := by
    intro u _ v _ h
    linarith
  have hpoint : ∀ u ∈ Ioi (0:ℝ), |(2:ℝ)| • f (1+2*u) =
      C*(regularizedGaussHypergeometric a (1-a) 1 (-(u:ℂ))/((u:ℂ)+(1+w))) := by
    intro u hu
    have hu : 0 < u := hu
    have hden : (u:ℂ)+(1+w) ≠ 0 := by
      exact_mod_cast (by linarith : (u+(1+w):ℝ) ≠ 0)
    dsimp [f]
    rw [hP,show (1-((1+2*u:ℝ):ℂ))/2 = -(u:ℂ) by push_cast;ring]
    simp only [abs_of_pos (by norm_num : (0:ℝ)<2)]
    push_cast
    have he : (x:ℂ)+(1+2*u) = 2*((u:ℂ)+(1+w)) := by dsimp [w];push_cast;ring
    rw [he]
    field_simp
  have hi := (integrable_stieltjes_kernel ha0 ha1 hw).const_mul C
  have hfi : IntegrableOn (fun u : ℝ => |(2:ℝ)| • f (1+2*u)) (Ioi 0) :=
    IntegrableOn.congr_fun hi (fun u hu => (hpoint u hu).symm) measurableSet_Ioi
  have hfo := (integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi hd hinj f).mpr hfi
  rw [himage] at hfo
  have hv := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hinj f
  rw [himage,setIntegral_congr_fun measurableSet_Ioi hpoint,integral_const_mul,
    symmetric_stieltjes ha0 ha1 hw] at hv
  have hvalue : (∫ t : ℝ in Ioi 1, f t) = associatedP (-1/2+I*τ) 0 x := by
    rw [hv,←mul_assoc,hC,one_mul,hP]
    congr 1
    dsimp [w]
    push_cast
    ring
  rw [←hvalue]
  exact intervalIntegral_tendsto_integral_Ioi 1 hfo tendsto_id


end DLMF.Legendre.ConicalStieltjes
