/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.PowerSeriesUniqueness
public import DLMF.ParabolicCylinder.SectorAsymptotics

/-!
# Weber functions and their connection formulas

Solutions of Weber's equation, connection formulas and real-parameter identities for parabolic
cylinder functions.

Source references and common attribution are retained in
`DLMF.ParabolicCylinder.Weber`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat ComplexConjugate

namespace DLMF.Confluent

open DLMF.Bessel

/-- The value at zero of the normalized real Weber function W, given by the modulus of a
quarter-shifted Gamma ratio. -/
@[dlmf 12.14.E1]
def pcfWZero (a : ℝ) : ℝ :=
  2^(-3/4:ℝ)*Real.sqrt ‖Gamma (1/4+I*a/2)/Gamma (3/4+I*a/2)‖

/-- The derivative at zero of the normalized real Weber function W, with its negative Gamma-ratio
normalization. -/
@[dlmf 12.14.E2]
def pcfWDerivZero (a : ℝ) : ℝ :=
  -2^(-1/4:ℝ)*Real.sqrt ‖Gamma (3/4+I*a/2)/Gamma (1/4+I*a/2)‖

/-- The even entire solution of the oscillatory Weber equation, obtained by rotating the even
cylinder solution. -/
@[dlmf 12.14.E15]
def pcfWEven (a z : ℂ) : ℂ :=
  pcfEven (-I*a) (exp (π*I/4)*z)

/-- The odd entire solution of the oscillatory Weber equation, with the phase factor chosen to
preserve its initial derivative. -/
@[dlmf 12.14.E16]
def pcfWOdd (a z : ℂ) : ℂ :=
  exp (-π*I/4)*pcfOdd (-I*a) (exp (π*I/4)*z)

/-- The real-normalized Weber function W, formed from its even and odd entire solutions with the
prescribed initial values. -/
@[dlmf 12.14.E8]
def pcfW (a : ℝ) (z : ℂ) : ℂ :=
  pcfWZero a*pcfWEven a z+pcfWDerivZero a*pcfWOdd a z

/-- Identity under the stated parameter and domain assumptions: `pcfW a 0=pcfWZero a ∧ HasDerivAt
(pcfW a) (pcfWDerivZero a) 0`. -/
@[dlmf 12.14.E1, dlmf 12.14.E2]
theorem pcfW_initial (a : ℝ) :
    pcfW a 0=pcfWZero a ∧ HasDerivAt (pcfW a) (pcfWDerivZero a) 0 := by
  constructor
  · simp [pcfW, pcfWEven, pcfWOdd, pcfEven, pcfOdd]
  · have he : HasDerivAt (pcfWEven (a:ℂ)) 0 0 := by
      have h := (hasDerivAt_pcfEven (-I*a) (exp (π*I/4)*0)).comp 0
        ((hasDerivAt_id (0:ℂ)).const_mul (exp (π*I/4)))
      have h' : HasDerivAt (pcfWEven (a:ℂ)) _ 0 :=
        h.congr_of_eventuallyEq (Eventually.of_forall fun w => rfl)
      simpa [pcfEvenDeriv] using h'
    have ho : HasDerivAt (pcfWOdd (a:ℂ)) 1 0 := by
      have h := ((hasDerivAt_pcfOdd (-I*a) (exp (π*I/4)*0)).comp 0
        ((hasDerivAt_id (0:ℂ)).const_mul (exp (π*I/4)))).const_mul (exp (-π*I/4))
      have h' : HasDerivAt (pcfWOdd (a:ℂ)) _ 0 :=
        h.congr_of_eventuallyEq (Eventually.of_forall fun w => rfl)
      simpa [pcfOddDeriv, ← Complex.exp_add, neg_div] using h'
    have h : HasDerivAt (pcfW a) _ 0 :=
      ((he.const_mul (pcfWZero a:ℂ)).add (ho.const_mul (pcfWDerivZero a:ℂ))).congr_of_eventuallyEq
        (Eventually.of_forall fun w => rfl)
    simpa only [mul_zero, mul_one, zero_add] using h

/-- `(e^{iπ/4})² = i`. -/
theorem exp_pi_I_quarter_sq : exp (π*I/4)^2 = I := by
  rw [← Complex.exp_nat_mul, show ((2:ℕ):ℂ)*(π*I/4) = (π/2:ℝ)*I by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  simp

/-- `e^{-iπ/4} e^{iπ/4} = 1`. -/
theorem exp_neg_pi_I_quarter_mul : exp (-π*I/4) * exp (π*I/4) = 1 := by
  rw [← Complex.exp_add]; ring_nf; simp

/-- Identity under the stated parameter and domain assumptions: `pcfWEven a z = exp
(-I*z^2/4)*kummerM (1/4-I*a/2) (1/2) (I*z^2/2) ∧ pcfWEven a z = exp (I*z^2/4)*kummerM
(1/4+I*a/2) (1/2) (-I*z^2/2)`. -/
@[dlmf 12.14.E15]
theorem pcfWEven_kummer (a z : ℂ) :
    pcfWEven a z = exp (-I*z^2/4)*kummerM (1/4-I*a/2) (1/2) (I*z^2/2) ∧ pcfWEven a z = exp (I*z^2/4)*kummerM (1/4+I*a/2) (1/2) (-I*z^2/2) := by
  constructor
  · rw [pcfWEven, pcfEven, mul_pow, exp_pi_I_quarter_sq, show -I*a/2 + 1/4 = 1/4-I*a/2 by ring,
      show -(I*z^2)/4 = -I*z^2/4 by ring]
  · rw [pcfWEven, pcfEven_kummer_alternative, mul_pow, exp_pi_I_quarter_sq,
      show -(-I*a)/2 + 1/4 = 1/4+I*a/2 by ring, show -(I*z^2)/2 = -I*z^2/2 by ring]

/-- Identity under the stated parameter and domain assumptions: `pcfWOdd a z = z*exp
(-I*z^2/4)*kummerM (3/4-I*a/2) (3/2) (I*z^2/2) ∧ pcfWOdd a z = z*exp (I*z^2/4)*kummerM
(3/4+I*a/2) (3/2) (-I*z^2/2)`. -/
@[dlmf 12.14.E16]
theorem pcfWOdd_kummer (a z : ℂ) :
    pcfWOdd a z = z*exp (-I*z^2/4)*kummerM (3/4-I*a/2) (3/2) (I*z^2/2) ∧ pcfWOdd a z = z*exp (I*z^2/4)*kummerM (3/4+I*a/2) (3/2) (-I*z^2/2) := by
  have h1 := exp_neg_pi_I_quarter_mul
  constructor
  · rw [pcfWOdd, pcfOdd, mul_pow, exp_pi_I_quarter_sq, show -I*a/2 + 3/4 = 3/4-I*a/2 by ring,
      show -(I*z^2)/4 = -I*z^2/4 by ring]
    linear_combination (z * exp (-I*z^2/4)*kummerM (3/4-I*a/2) (3/2) (I*z^2/2)) * h1
  · rw [pcfWOdd, pcfOdd_kummer_alternative, mul_pow, exp_pi_I_quarter_sq,
      show -(-I*a)/2 + 3/4 = 3/4+I*a/2 by ring, show -(I*z^2)/2 = -I*z^2/2 by ring]
    linear_combination (z * exp (I*z^2/4)*kummerM (3/4+I*a/2) (3/2) (-I*z^2/2)) * h1

/-- Derivative of `W(a,z)`. -/
def pcfWDeriv (a : ℝ) (z : ℂ) : ℂ :=
  pcfWZero a * (exp (π*I/4) * pcfEvenDeriv (-I*a) (exp (π*I/4)*z)) +
    pcfWDerivZero a * pcfOddDeriv (-I*a) (exp (π*I/4)*z)

/-- A rotated solution of Weber's equation. -/
theorem IsWeberSol.hasDerivAt_rot {b : ℂ} {f f' : ℂ → ℂ} (hf : IsWeberSol b f f') (c z : ℂ) :
    HasDerivAt (fun w => f (c*w)) (c * f' (c*z)) z ∧
      HasDerivAt (fun w => c * f' (c*w)) (c^2*((c*z)^2/4+b) * f (c*z)) z := by
  have hl : ∀ w : ℂ, HasDerivAt (fun w : ℂ => c*w) c w := fun w =>
    ((hasDerivAt_id w).const_mul c).congr_deriv (mul_one c)
  constructor
  · exact ((hf (c*z)).1.comp z (hl z)).congr_deriv (mul_comm _ _)
  · exact (((hf (c*z)).2.comp z (hl z)).const_mul c).congr_deriv (by ring)

/-- `W` has derivative `pcfWDeriv`. -/
theorem hasDerivAt_pcfW (a : ℝ) (z : ℂ) : HasDerivAt (pcfW a) (pcfWDeriv a z) z := by
  have he := ((isWeberSol_pcfEven (-I*a)).hasDerivAt_rot (exp (π*I/4)) z).1
  have ho := ((isWeberSol_pcfOdd (-I*a)).hasDerivAt_rot (exp (π*I/4)) z).1
  have h := (he.const_mul (pcfWZero a : ℂ)).add ((ho.const_mul (exp (-π*I/4))).const_mul (pcfWDerivZero a : ℂ))
  convert h using 1
  · funext w; simp [pcfW, pcfWEven, pcfWOdd]
  · rw [pcfWDeriv, ← mul_assoc (exp (-π*I/4)), exp_neg_pi_I_quarter_mul, one_mul]

/-- Weber's oscillatory equation `W'' = (a - z²/4) W`. -/
theorem hasDerivAt_pcfWDeriv (a : ℝ) (z : ℂ) :
    HasDerivAt (pcfWDeriv a) ((a - z^2/4) * pcfW a z) z := by
  have he := ((isWeberSol_pcfEven (-I*a)).hasDerivAt_rot (exp (π*I/4)) z).2
  have ho := ((isWeberSol_pcfOdd (-I*a)).hasDerivAt_rot (exp (π*I/4)) z).2
  have h := (he.const_mul (pcfWZero a : ℂ)).add ((ho.const_mul (exp (-π*I/4))).const_mul (pcfWDerivZero a : ℂ))
  have h1 := exp_neg_pi_I_quarter_mul
  have h2 := exp_pi_I_quarter_sq
  convert h using 1
  · funext w; simp only [Pi.add_apply, pcfWDeriv]
    linear_combination (-(pcfWDerivZero a : ℂ) * pcfOddDeriv (-I*a) (exp (π*I/4)*w)) * h1
  · rw [pcfW, pcfWEven, pcfWOdd, mul_pow, h2]
    linear_combination ((a:ℂ) - z^2/4) * ((pcfWZero a : ℂ) * pcfEven (-I*a) (exp (π*I/4)*z) +
      (pcfWDerivZero a : ℂ) * (exp (-π*I/4) * pcfOdd (-I*a) (exp (π*I/4)*z))) * I_sq

/-- The derivative of `W`. -/
theorem deriv_pcfW (a : ℝ) : deriv (pcfW a) = pcfWDeriv a :=
  funext fun z => (hasDerivAt_pcfW a z).deriv

/-- The stated relation follows from the given hypotheses: `IsOscillatoryCylinderSolution a (pcfW
a)`. -/
@[dlmf 12.2.E3]
theorem pcfW_ode (a : ℝ) :
    IsOscillatoryCylinderSolution a (pcfW a) := by
  intro z
  rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, deriv_pcfW,
    (hasDerivAt_pcfWDeriv a z).deriv]
  ring

/-- `W(a, z̄) = conj W(a, z)`. -/
theorem conj_pcfW_conj (a : ℝ) (z : ℂ) : conj (pcfW a (conj z)) = pcfW a z := by
  have hE : conj (pcfWEven a (conj z)) = pcfWEven a z := by
    rw [(pcfWEven_kummer _ _).1, (pcfWEven_kummer _ _).2]
    simp [conj_kummerM, ← Complex.exp_conj, map_div₀, map_ofNat]
    ring_nf
  have hO : conj (pcfWOdd a (conj z)) = pcfWOdd a z := by
    rw [(pcfWOdd_kummer _ _).1, (pcfWOdd_kummer _ _).2]
    simp [conj_kummerM, ← Complex.exp_conj, map_div₀, map_ofNat]
    left; ring_nf
  simp only [pcfW, map_add, map_mul, Complex.conj_ofReal, hE, hO]

/-- W is real on the real axis. -/
theorem pcfW_real (a x : ℝ) :
    (pcfW a x).im=0 := by
  rw [← Complex.conj_eq_iff_im]
  simpa using conj_pcfW_conj a x

/-- `W'(a,x)` is real for real `x`. -/
theorem conj_pcfWDeriv_ofReal (a x : ℝ) : conj (pcfWDeriv a x) = pcfWDeriv a x := by
  have h := (hasDerivAt_pcfW a (conj (x:ℂ))).conj_conj
  have he : (conj ∘ pcfW a ∘ conj) = pcfW a := funext fun z => conj_pcfW_conj a z
  rw [he, Complex.conj_conj, Complex.conj_ofReal] at h
  exact h.unique (hasDerivAt_pcfW a x)

/-- The Wronskian of `W(a,z)` and `W(a,-z)`. -/
lemma pcfW_wronskian_aux (a : ℝ) (z : ℂ) :
    pcfW a z*(-pcfWDeriv a (-z))-pcfW a (-z)*pcfWDeriv a z = -2 * pcfWZero a * pcfWDerivZero a := by
  have hn : ∀ w : ℂ, HasDerivAt (fun w => pcfW a (-w)) (-pcfWDeriv a (-w)) w := fun w => by
    exact ((hasDerivAt_pcfW a (-w)).comp w (hasDerivAt_neg w)).congr_deriv (by ring)
  have hn' : ∀ w : ℂ, HasDerivAt (fun w => -pcfWDeriv a (-w)) ((a - (-w)^2/4) * pcfW a (-w)) w := fun w => by
    exact ((hasDerivAt_pcfWDeriv a (-w)).comp w (hasDerivAt_neg w)).neg.congr_deriv (by ring)
  have hd : ∀ w, HasDerivAt (fun w => pcfW a w*(-pcfWDeriv a (-w))-pcfW a (-w)*pcfWDeriv a w) 0 w :=
    fun w => (((hasDerivAt_pcfW a w).mul (hn' w)).sub ((hn w).mul (hasDerivAt_pcfWDeriv a w))).congr_deriv
      (by ring)
  have := is_const_of_deriv_eq_zero (fun w => (hd w).differentiableAt) (fun w => (hd w).deriv) z 0
  rw [this, neg_zero]
  have h0 : pcfW a 0 = pcfWZero a := by simp [pcfW, pcfWEven, pcfWOdd, pcfEven, pcfOdd]
  have h1 : pcfWDeriv a 0 = pcfWDerivZero a := by
    simp [pcfWDeriv, pcfEvenDeriv_zero, pcfOddDeriv_zero]
  rw [h0, h1]; ring

/-- `W(a,0) W'(a,0) = -1/2`. -/
theorem pcfWZero_mul_pcfWDerivZero (a : ℝ) : pcfWZero a * pcfWDerivZero a = -1/2 := by
  have hpos : 0 < ‖Gamma (1/4+I*a/2)/Gamma (3/4+I*a/2)‖ := by
    refine norm_pos_iff.mpr (div_ne_zero ?_ ?_) <;> apply Complex.Gamma_ne_zero_of_re_pos <;> simp
  have hinv : ‖Gamma (3/4+I*a/2)/Gamma (1/4+I*a/2)‖ = ‖Gamma (1/4+I*a/2)/Gamma (3/4+I*a/2)‖⁻¹ := by
    rw [← norm_inv, inv_div]
  rw [pcfWZero, pcfWDerivZero, hinv]
  have hs : Real.sqrt ‖Gamma (1/4+I*a/2)/Gamma (3/4+I*a/2)‖ * Real.sqrt ‖Gamma (1/4+I*a/2)/Gamma (3/4+I*a/2)‖⁻¹ = 1 := by
    rw [← Real.sqrt_mul hpos.le, mul_inv_cancel₀ hpos.ne', Real.sqrt_one]
  have h2 : (2:ℝ)^(-3/4:ℝ) * 2^(-1/4:ℝ) = 1/2 := by
    rw [← Real.rpow_add (by norm_num)]; norm_num
  linear_combination (-(2:ℝ)^(-3/4:ℝ) * 2^(-1/4:ℝ)) * hs - h2

/-- Identity under the stated parameter and domain assumptions: `pcfW a z*(-deriv (pcfW a)
(-z))-pcfW a (-z)*deriv (pcfW a) z=1`. -/
@[dlmf 12.14.E3]
theorem pcfW_wronskian (a : ℝ) (z : ℂ) :
    pcfW a z*(-deriv (pcfW a) (-z))-pcfW a (-z)*deriv (pcfW a) z=1 := by
  rw [deriv_pcfW, pcfW_wronskian_aux]
  have := pcfWZero_mul_pcfWDerivZero a
  have : (pcfWZero a : ℂ) * pcfWDerivZero a = -1/2 := by exact_mod_cast this
  linear_combination (-2) * this

/-- The positive connection factor `√(1+exp(2πa)) - exp(πa)` for the real Weber function. -/
@[dlmf 12.14.E5]
def pcfWK (a : ℝ) : ℝ :=
  Real.sqrt (1+Real.exp (2*π*a))-Real.exp (π*a)

/-- pcfWK reciprocal. -/
@[dlmf 12.14.E5]
theorem pcfWK_recip (a : ℝ) :
    0 < pcfWK a ∧ (pcfWK a)⁻¹=Real.sqrt (1+Real.exp (2*π*a))+Real.exp (π*a) := by
  unfold pcfWK
  have hE : Real.exp (2*π*a)=(Real.exp (π*a))^2 := by
    rw [show 2*π*a=π*a+π*a by ring, Real.exp_add, pow_two]
  have hs:=Real.sq_sqrt (by positivity : 0 ≤ 1+Real.exp (2*π*a))
  have hp : 0 < Real.sqrt (1+Real.exp (2*π*a))-Real.exp (π*a) := by
    nlinarith [hE, Real.sqrt_nonneg (1+Real.exp (2*π*a)),Real.exp_pos (π*a)]
  refine ⟨hp, ?_⟩
  apply (mul_eq_one_iff_inv_eq₀ hp.ne').mp
  nlinarith [hE]

/-- Continuous argument of Gamma along the vertical line, normalized to zero at a=0. -/
@[dlmf 12.14.E7]
def pcfGammaPhase (a : ℝ) : ℝ :=
  ∫ t : ℝ in 0..a, (Complex.digamma (1/2+I*t)).re

/-- The digamma function is continuous on the line `Re s = 1/2`. -/
theorem continuous_digamma_half_line : Continuous fun t : ℝ => Complex.digamma (1/2+I*t) := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hG : DifferentiableOn ℂ Gamma {s : ℂ | 0 < s.re} := fun s hs =>
    (Complex.differentiableAt_Gamma s (fun m h => by
      have : (s).re = -(m:ℝ) := by rw [h]; simp
      have hs : (0:ℝ) < s.re := hs
      linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])).differentiableWithinAt
  have hdG : ContinuousOn (deriv Gamma) {s : ℂ | 0 < s.re} := (hG.deriv hU).continuousOn
  have hψ : ContinuousOn Complex.digamma {s : ℂ | 0 < s.re} := by
    have : ContinuousOn (fun s => deriv Gamma s / Gamma s) {s : ℂ | 0 < s.re} :=
      hdG.div hG.continuousOn (fun s hs => Complex.Gamma_ne_zero_of_re_pos hs)
    exact this.congr fun s _ => rfl
  refine hψ.comp_continuous (by fun_prop) fun t => ?_
  show (0:ℝ) < (1/2+I*t).re
  simp

/-- Identity under the stated parameter and domain assumptions: `Gamma (1/2+I*a) = ‖Gamma
(1/2+I*a)‖*exp (I*pcfGammaPhase a)`. -/
@[dlmf 12.14.E7]
theorem pcfGammaPhase_spec (a : ℝ) :
    Gamma (1/2+I*a) = ‖Gamma (1/2+I*a)‖*exp (I*pcfGammaPhase a) := by
  have hψc := continuous_digamma_half_line
  set Ph : ℝ → ℝ := fun a => ∫ t : ℝ in 0..a, (Complex.digamma (1/2+I*t)).re with hPh
  set Th : ℝ → ℝ := fun a => ∫ t : ℝ in 0..a, (Complex.digamma (1/2+I*t)).im with hTh
  have hPhd (x : ℝ) : HasDerivAt Ph (Complex.digamma (1/2+I*x)).re x :=
    ((Complex.continuous_re.comp hψc).integral_hasStrictDerivAt 0 x).hasDerivAt
  have hThd (x : ℝ) : HasDerivAt Th (Complex.digamma (1/2+I*x)).im x :=
    ((Complex.continuous_im.comp hψc).integral_hasStrictDerivAt 0 x).hasDerivAt
  set h : ℝ → ℂ := fun x => Gamma (1/2+I*x)*exp (-I*Ph x)*exp (Th x) with hh
  have hre (x : ℝ) : 0 < (1/2+I*(x:ℂ)).re := by simp
  have hGd (x : ℝ) : HasDerivAt (fun x : ℝ => Gamma (1/2+I*x))
      (deriv Gamma (1/2+I*x)*I) x := by
    have hd := (Complex.differentiableAt_Gamma (1/2+I*x) (fun m hm => by
      have := congrArg Complex.re hm; simp at this
      linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])).hasDerivAt
    have hl : HasDerivAt (fun x : ℝ => (1/2:ℂ)+I*x) I x := by
      simpa using ((hasDerivAt_id (x:ℂ)).const_mul I).const_add (1/2:ℂ) |>.comp_ofReal
    exact hd.comp x hl
  have hhd (x : ℝ) : HasDerivAt h 0 x := by
    have h1 := hGd x
    have h2 : HasDerivAt (fun x : ℝ => exp (-I*Ph x)) (exp (-I*Ph x)*(-I*(Complex.digamma (1/2+I*x)).re)) x := by
      have := ((hPhd x).ofReal_comp.const_mul (-I)).cexp
      simpa using this
    have h3 : HasDerivAt (fun x : ℝ => exp ((Th x : ℂ))) (exp (Th x)*(Complex.digamma (1/2+I*x)).im) x := by
      have := ((hThd x).ofReal_comp).cexp
      simpa using this
    have hd := (h1.mul h2).mul h3
    refine hd.congr_deriv ?_
    have hG0 : Gamma (1/2+I*x) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (hre x)
    have hψ : deriv Gamma (1/2+I*x) = Gamma (1/2+I*x)*
        (((Complex.digamma (1/2+I*x)).re:ℂ) + ((Complex.digamma (1/2+I*x)).im:ℂ)*I) := by
      rw [Complex.re_add_im, Complex.digamma_def, logDeriv_apply, mul_div_assoc', eq_div_iff hG0]
      ring
    simp only [Pi.mul_apply]
    rw [hψ]
    ring_nf
    rw [I_sq]
    ring
  have hdiff : Differentiable ℝ h := fun x => (hhd x).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff (fun x => (hhd x).deriv) a 0
  have h0 : h 0 = Real.sqrt π := by
    simp [hh, hPh, hTh]
    rw [← one_div, Gamma_one_half_eq_sqrt]
  rw [h0] at hconst
  simp only [hh] at hconst
  have e1 : exp (I*Ph a)*exp (-I*Ph a) = 1 := by rw [← Complex.exp_add]; simp
  have e2 : exp (-((Th a:ℝ):ℂ))*exp ((Th a:ℝ):ℂ) = 1 := by rw [← Complex.exp_add]; simp
  have hE : Gamma (1/2+I*a) = (Real.sqrt π:ℂ)*exp (-((Th a:ℝ):ℂ))*exp (I*Ph a) := by
    linear_combination (exp (I*Ph a)*exp (-((Th a:ℝ):ℂ)))*hconst +
      (-(Gamma (1/2+I*a))*(exp (-((Th a:ℝ):ℂ))*exp ((Th a:ℝ):ℂ)))*e1 + (-(Gamma (1/2+I*a)))*e2
  have hn : ‖Gamma (1/2+I*a)‖ = Real.sqrt π*Real.exp (-Th a) := by
    rw [hE, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr Real.pi_pos)]
    simp
  rw [hn]
  conv_lhs => rw [hE]
  rw [show pcfGammaPhase a = Ph a from rfl]
  push_cast
  ring

/-- The Weber connection phase `π/8` plus half the chosen Gamma phase. -/
@[dlmf 12.14.E6]
def pcfWRho (a : ℝ) : ℝ :=
  π/8+pcfGammaPhase a/2

/-- `e^{iπ/4} · conj (sin (π (1/4 + i a/2))) = (e^{πa/2} + i e^{-πa/2}) / 2`. -/
lemma pcfW_aux_T (a : ℝ) :
    exp (π*I/4) * conj (sin (π*(1/4+I*a/2))) =
      ((Real.exp (π*a/2) : ℝ) + I * (Real.exp (-π*a/2) : ℝ)) / 2 := by
  have hc : conj (sin (π*(1/4+I*a/2))) = sin (π*(1/4-I*a/2)) := by
    rw [← Complex.sin_conj]; congr 1; simp [map_add, map_mul, map_div₀, map_ofNat]; ring
  rw [hc, Complex.sin]
  have e1 : exp (-(π*(1/4-I*a/2)) * I) = exp (-π*I/4) * exp (-π*a/2) := by
    rw [← Complex.exp_add]; congr 1; ring_nf; rw [I_sq]; ring
  have e2 : exp (π*(1/4-I*a/2) * I) = exp (π*I/4) * exp (π*a/2) := by
    rw [← Complex.exp_add]; congr 1; ring_nf; rw [I_sq]; ring
  rw [e1, e2]
  have h1 := exp_neg_pi_I_quarter_mul
  have h2 := exp_pi_I_quarter_sq
  push_cast
  rw [show (-(π:ℂ)*a/2) = -π*a/2 by ring]
  linear_combination (I * exp (-π*a/2) / 2) * h1 - (I * exp (π*a/2) / 2) * h2 - (exp (π*a/2) / 2) * I_sq

/-- Algebraic core of `pcfW_aux_V_sq`. -/
lemma pcfW_aux_alg {e4 eφ s S g g1 g3 c3 W2 W' p : ℂ} {ng n3 : ℝ} (P : g = ng * eφ)
    (D : g1 * g3 = g * W' * s) (Rf : g1 * c3 = p / S) (N3 : g3 * c3 = (n3:ℂ)^2)
    (h2 : W2 * W' = 2) (hS : S ≠ 0) (hg3 : g3 ≠ 0) (hW2 : W2 ≠ 0) (hs0 : s ≠ 0) (hW' : W' ≠ 0) :
    e4 * eφ * (s^2 / (W2 * g3^2)) * S * (2 * ng * n3^2) = e4 * p * s := by
  have Rf' : g1 * c3 * S = p := by rw [Rf]; field_simp
  have key : e4 * eφ * s^2 * S * 2 * ng * n3^2 * (W' * s) = e4 * p * s * (W2 * g3^2) * (W' * s) := by
    linear_combination (-(e4*s^2*S*2*W'*s*n3^2)) * P - (e4*s^2*S*2*W'*s*g) * N3
      - (e4*s^2*S*2*g3*c3) * D + (2*e4*s^2*g3^2) * Rf' - (e4*p*s^2*g3^2) * h2
  rw [show e4 * eφ * (s^2 / (W2 * g3^2)) * S * (2 * ng * n3^2) =
    e4 * eφ * s^2 * S * 2 * ng * n3^2 / (W2 * g3^2) by ring, div_eq_iff (by simp [hW2, hg3])]
  exact mul_right_cancel₀ (mul_ne_zero hW' hs0) key

/-- `V(a)² sin(π(1/4+ia/2)) (2 |Γ(1/2+ia)| |Γ(3/4+ia/2)|²) = e^{iπ/4} π √π` for
`V(a) = e^{iρ} U(ia, 0)`, from the duplication and reflection formulas. -/
lemma pcfW_aux_V_sq (a : ℝ) :
    (exp (I*pcfWRho a) * pcfU (I*a) 0)^2 * sin (π*(1/4+I*a/2)) *
      (2 * ‖Gamma (1/2+I*a)‖ * ‖Gamma (3/4+I*a/2)‖^2) = exp (π*I/4) * π * Real.sqrt π := by
  have hρ : exp (I*pcfWRho a)^2 = exp (π*I/4) * exp (I*pcfGammaPhase a) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add, pcfWRho]; congr 1; push_cast; ring
  have hw : ((2:ℂ)^(I*a/2+1/4))^2 = (2:ℂ)^(I*a+1/2) := by
    rw [← cpow_nat_mul]; congr 1; push_cast; ring
  have h2 : (2:ℂ)^(I*a+1/2) * (2:ℂ)^(1/2-I*a) = 2 := by
    rw [← cpow_add _ _ two_ne_zero, show I*a+1/2+(1/2-I*a) = (1:ℂ) by ring, cpow_one]
  have P := pcfGammaPhase_spec a
  have D := Complex.Gamma_mul_Gamma_add_half (1/4+I*a/2)
  rw [show 1/4+I*(a:ℂ)/2+1/2 = 3/4+I*a/2 by ring, show 2*(1/4+I*(a:ℂ)/2) = 1/2+I*a by ring,
    show (1:ℂ)-(1/2+I*a) = 1/2-I*a by ring] at D
  have Rf := Complex.Gamma_mul_Gamma_one_sub (1/4+I*a/2)
  rw [show 1-(1/4+I*(a:ℂ)/2) = conj (3/4+I*a/2) by simp [map_add, map_mul, map_div₀, map_ofNat]; ring,
    Complex.Gamma_conj] at Rf
  have N3 := Complex.mul_conj' (Gamma (3/4+I*a/2))
  have hs : ((Real.sqrt π : ℝ) : ℂ)^2 = π := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hS : sin (π*(1/4+I*a/2)) ≠ 0 := by
    intro h; rw [h, div_zero] at Rf
    exact mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
      ((map_ne_zero _).mpr (Complex.Gamma_ne_zero_of_re_pos (by norm_num))) Rf
  have hg3 : Gamma (3/4+I*a/2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  have hW : (2:ℂ)^(I*a/2+1/4) ≠ 0 := by simp
  rw [pcfU_zero, show I*(a:ℂ)/2+1/4 = I*a/2+1/4 by ring, show 3/4+I*(a:ℂ)/2 = 3/4+I*a/2 by ring,
    mul_pow, div_pow, mul_pow, hρ, hw]
  exact pcfW_aux_alg P D Rf N3 h2 hS hg3 (by rw [← hw]; exact pow_ne_zero 2 hW) (by simp [Real.sqrt_ne_zero', Real.pi_pos]) (by simp)

/-- Algebraic core of `pcfW_aux_V'_sq`. -/
lemma pcfW_aux_alg' {e4 eφ s cS g g1 g3 c1 W2 W' p : ℂ} {ng n1 : ℝ} (P : g = ng * eφ)
    (D : g1 * g3 = g * W' * s) (Rf : g3 * c1 = p / cS) (N1 : g1 * c1 = (n1:ℂ)^2)
    (h2 : W2 * W' = 1) (hS : cS ≠ 0) (hg1 : g1 ≠ 0) (hW2 : W2 ≠ 0) (hs0 : s ≠ 0) (hW' : W' ≠ 0) :
    e4 * eφ * (-I * (s^2 / (W2 * g1^2))) * cS * (ng * n1^2) = -I * e4 * p * s := by
  have Rf' : g3 * c1 * cS = p := by rw [Rf]; field_simp
  have key : -I * e4 * eφ * s^2 * cS * ng * n1^2 * (W' * s) =
      -I * e4 * p * s * (W2 * g1^2) * (W' * s) := by
    linear_combination (-(-I*e4*s^2*cS*W'*s*n1^2)) * P - (-I*e4*s^2*cS*W'*s*g) * N1
      - (-I*e4*s^2*cS*g1*c1) * D + (-I*e4*s^2*g1^2) * Rf' - (-I*e4*p*s^2*g1^2) * h2
  rw [show e4 * eφ * (-I * (s^2 / (W2 * g1^2))) * cS * (ng * n1^2) =
    -I * e4 * eφ * s^2 * cS * ng * n1^2 / (W2 * g1^2) by ring, div_eq_iff (by simp [hW2, hg1])]
  exact mul_right_cancel₀ (mul_ne_zero hW' hs0) key

/-- The analogue of `pcfW_aux_V_sq` for `V'(a) = e^{iρ} e^{-iπ/4} U'(ia, 0)`. -/
lemma pcfW_aux_V'_sq (a : ℝ) :
    (exp (I*pcfWRho a) * (exp (-π*I/4) * pcfUDeriv (I*a) 0))^2 * conj (sin (π*(1/4+I*a/2))) *
      (‖Gamma (1/2+I*a)‖ * ‖Gamma (1/4+I*a/2)‖^2) = -I * exp (π*I/4) * π * Real.sqrt π := by
  have hρ : exp (I*pcfWRho a)^2 = exp (π*I/4) * exp (I*pcfGammaPhase a) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add, pcfWRho]; congr 1; push_cast; ring
  have hq : exp (-π*I/4)^2 = -I := by
    have h1 := exp_neg_pi_I_quarter_mul
    have h2 := exp_pi_I_quarter_sq
    linear_combination I * exp (-π*I/4)^2 * h2 - I * (exp (-π*I/4) * exp (π*I/4) + 1) * h1 + exp (-π*I/4)^2 * I_sq
  have hw : ((2:ℂ)^(I*a/2-1/4))^2 = (2:ℂ)^(I*a-1/2) := by
    rw [← cpow_nat_mul]; congr 1; push_cast; ring
  have h2 : (2:ℂ)^(I*a-1/2) * (2:ℂ)^(1/2-I*a) = 1 := by
    rw [← cpow_add _ _ two_ne_zero, show I*a-1/2+(1/2-I*a) = (0:ℂ) by ring, cpow_zero]
  have P := pcfGammaPhase_spec a
  have D := Complex.Gamma_mul_Gamma_add_half (1/4+I*a/2)
  rw [show 1/4+I*(a:ℂ)/2+1/2 = 3/4+I*a/2 by ring, show 2*(1/4+I*(a:ℂ)/2) = 1/2+I*a by ring,
    show (1:ℂ)-(1/2+I*a) = 1/2-I*a by ring] at D
  have Rf := Complex.Gamma_mul_Gamma_one_sub (1/4+I*a/2)
  rw [show 1-(1/4+I*(a:ℂ)/2) = conj (3/4+I*a/2) by simp [map_add, map_mul, map_div₀, map_ofNat]; ring,
    Complex.Gamma_conj] at Rf
  have Rfc : Gamma (3/4+I*a/2) * conj (Gamma (1/4+I*a/2)) = π / conj (sin (π*(1/4+I*a/2))) := by
    have := congrArg conj Rf
    simp only [map_mul, map_div₀, Complex.conj_conj, Complex.conj_ofReal] at this
    rw [← this]; ring
  have N1 := Complex.mul_conj' (Gamma (1/4+I*a/2))
  have hS : conj (sin (π*(1/4+I*a/2))) ≠ 0 := by
    intro h; rw [h, div_zero] at Rfc
    exact mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
      ((map_ne_zero _).mpr (Complex.Gamma_ne_zero_of_re_pos (by norm_num))) Rfc
  have hg1 : Gamma (1/4+I*a/2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  have hW : (2:ℂ)^(I*a/2-1/4) ≠ 0 := by simp
  rw [pcfUDeriv_zero, show I*(a:ℂ)/2-1/4 = I*a/2-1/4 by ring, show 1/4+I*(a:ℂ)/2 = 1/4+I*a/2 by ring,
    mul_pow, mul_pow, div_pow, neg_pow, mul_pow, hρ, hq, hw]
  have := pcfW_aux_alg' (e4 := exp (π*I/4)) P D Rfc N1 h2 hS hg1 (by rw [← hw]; exact pow_ne_zero 2 hW)
    (by simp [Real.sqrt_ne_zero', Real.pi_pos]) (by simp)
  rw [← this]; ring

/-- `V(a)² = r (e^{πa/2} + i e^{-πa/2}) / 2` with `r > 0`, for `V(a) = e^{iρ} U(ia, 0)`. -/
lemma pcfW_aux_V_sq_pos (a : ℝ) : ∃ r : ℝ, 0 < r ∧
    (exp (I*pcfWRho a) * pcfU (I*a) 0)^2 =
      r * (((Real.exp (π*a/2) : ℝ) + I * (Real.exp (-π*a/2) : ℝ)) / 2) := by
  have h := pcfW_aux_V_sq a
  have hT := pcfW_aux_T a
  have hng : 0 < ‖Gamma (1/2+I*a)‖ := norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
  have hn3 : 0 < ‖Gamma (3/4+I*a/2)‖ := norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
  rw [← hT]
  generalize sin (π*(1/4+I*a/2)) = S at h ⊢
  generalize ‖Gamma (1/2+I*a)‖ = ng at h hng ⊢
  generalize ‖Gamma (3/4+I*a/2)‖ = n3 at h hn3 ⊢
  generalize exp (I*pcfWRho a) * pcfU (I*a) 0 = V at h ⊢
  have hS : S ≠ 0 := by
    have hne : exp (π*I/4) * π * Real.sqrt π ≠ 0 := by
      simp [Real.pi_pos.ne', Real.sqrt_ne_zero', Real.pi_pos, Complex.exp_ne_zero]
    rintro rfl; apply hne; rw [← h]; ring
  have hnS : 0 < ‖S‖ := norm_pos_iff.mpr hS
  refine ⟨π * Real.sqrt π / (2 * ng * n3^2 * ‖S‖^2), by positivity, ?_⟩
  have hSS := Complex.mul_conj' S
  push_cast
  have : (ng:ℂ) ≠ 0 := by exact_mod_cast hng.ne'
  have : (n3:ℂ) ≠ 0 := by exact_mod_cast hn3.ne'
  have : (‖S‖:ℂ) ≠ 0 := by exact_mod_cast hnS.ne'
  field_simp
  linear_combination (conj S) * h - V^2 * (2 * ng * n3^2) * hSS

/-- `e^{-iπ/4} = -i e^{iπ/4}`. -/
theorem exp_neg_pi_I_quarter_eq : exp (-π*I/4) = -I * exp (π*I/4) := by
  have h1 := exp_neg_pi_I_quarter_mul
  have h2 := exp_pi_I_quarter_sq
  linear_combination (exp (-π*I/4) * (exp (π*I/4)^2 + I) - exp (π*I/4)) * h2
    - exp (π*I/4)^3 * h1 + exp (-π*I/4) * I_sq

/-- `V'(a)² = r (e^{πa/2} - i e^{-πa/2}) / 2` with `r > 0`, for
`V'(a) = e^{iρ} e^{-iπ/4} U'(ia, 0)`. -/
lemma pcfW_aux_V'_sq_pos (a : ℝ) : ∃ r : ℝ, 0 < r ∧
    (exp (I*pcfWRho a) * (exp (-π*I/4) * pcfUDeriv (I*a) 0))^2 =
      r * conj (((Real.exp (π*a/2) : ℝ) + I * (Real.exp (-π*a/2) : ℝ)) / 2) := by
  have h := pcfW_aux_V'_sq a
  have hT := pcfW_aux_T a
  have hng : 0 < ‖Gamma (1/2+I*a)‖ := norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
  have hn1 : 0 < ‖Gamma (1/4+I*a/2)‖ := norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
  have he : conj (exp (π*I/4)) = -I * exp (π*I/4) := by
    rw [← Complex.exp_conj, ← exp_neg_pi_I_quarter_eq]; congr 1
    simp [map_div₀, map_ofNat]
  rw [← hT, map_mul, he, Complex.conj_conj]
  generalize sin (π*(1/4+I*a/2)) = S at h ⊢
  generalize ‖Gamma (1/2+I*a)‖ = ng at h hng ⊢
  generalize ‖Gamma (1/4+I*a/2)‖ = n1 at h hn1 ⊢
  generalize exp (I*pcfWRho a) * (exp (-π*I/4) * pcfUDeriv (I*a) 0) = V at h ⊢
  have hS : S ≠ 0 := by
    have hne : -I * exp (π*I/4) * π * Real.sqrt π ≠ 0 := by
      simp [Real.pi_pos.ne', Real.sqrt_ne_zero', Real.pi_pos, Complex.exp_ne_zero]
    rintro rfl; apply hne; rw [← h]; simp
  have hnS : 0 < ‖S‖ := norm_pos_iff.mpr hS
  refine ⟨π * Real.sqrt π / (ng * n1^2 * ‖S‖^2), by positivity, ?_⟩
  have hSS := Complex.mul_conj' S
  push_cast
  have : (ng:ℂ) ≠ 0 := by exact_mod_cast hng.ne'
  have : (n1:ℂ) ≠ 0 := by exact_mod_cast hn1.ne'
  have : (‖S‖:ℂ) ≠ 0 := by exact_mod_cast hnS.ne'
  field_simp
  linear_combination S * h - V^2 * (ng * n1^2) * hSS

/-- A continuous real function without zeros that is positive at `0` is positive. -/
lemma pcfW_aux_pos_of_continuous {f : ℝ → ℝ} (hf : Continuous f) (h : ∀ x, f x ≠ 0)
    (h0 : 0 < f 0) (x : ℝ) : 0 < f x := by
  by_contra hx
  push Not at hx
  obtain ⟨c, -, hc⟩ := intermediate_value_uIcc (a := 0) (b := x) hf.continuousOn
    (show (0:ℝ) ∈ uIcc (f 0) (f x) from Set.mem_uIcc.mpr (Or.inr ⟨hx, h0.le⟩))
  exact h c hc

/-- `Γ(s + i t/2)` is continuous in `t` for `s > 0`. -/
lemma pcfW_aux_continuous_Gamma {s : ℝ} (hs : 0 < s) :
    Continuous fun t : ℝ => Gamma (s + I*t/2) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hd := Complex.differentiableAt_Gamma (s + I*t/2) (fun m hm => by
    have := congrArg Complex.re hm; simp at this
    linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])
  exact ContinuousAt.comp (g := Gamma) hd.continuousAt
    (by fun_prop : ContinuousAt (fun t : ℝ => (s:ℂ) + I*t/2) t)

/-- `pcfGammaPhase` is continuous. -/
theorem continuous_pcfGammaPhase : Continuous pcfGammaPhase :=
  continuous_iff_continuousAt.mpr fun x =>
    ((Complex.continuous_re.comp continuous_digamma_half_line).integral_hasStrictDerivAt 0
      x).hasDerivAt.continuousAt

/-- Signs of `V = e^{iρ} U(ia,0)` and `V' = e^{iρ} e^{-iπ/4} U'(ia,0)`. -/
lemma pcfW_aux_signs (a : ℝ) :
    (0 < (exp (I*pcfWRho a) * pcfU (I*a) 0).re ∧ 0 < (exp (I*pcfWRho a) * pcfU (I*a) 0).im) ∧
    ((exp (I*pcfWRho a) * (exp (-π*I/4) * pcfUDeriv (I*a) 0)).re < 0 ∧
      0 < (exp (I*pcfWRho a) * (exp (-π*I/4) * pcfUDeriv (I*a) 0)).im) := by
  have hρc : Continuous fun a : ℝ => exp (I*pcfWRho a) := by
    unfold pcfWRho; have := continuous_pcfGammaPhase; fun_prop
  have hVc : Continuous fun a : ℝ => exp (I*pcfWRho a) * pcfU (I*a) 0 := by
    have hG := pcfW_aux_continuous_Gamma (s := 3/4) (by norm_num)
    have : (fun a : ℝ => exp (I*pcfWRho a) * pcfU (I*a) 0) = fun a : ℝ =>
        exp (I*pcfWRho a) * ((Real.sqrt π : ℂ) / ((2:ℂ)^(I*a/2+1/4) * Gamma ((3/4:ℝ) + I*a/2))) := by
      funext a; rw [pcfU_zero]; push_cast; ring_nf
    rw [this]
    refine hρc.mul (continuous_const.div (Continuous.mul ?_ hG) fun a => mul_ne_zero (by simp)
      (Complex.Gamma_ne_zero_of_re_pos (by norm_num)))
    exact continuous_const.cpow (by fun_prop) (fun _ => Or.inl (by norm_num))
  have hV'c : Continuous fun a : ℝ => exp (I*pcfWRho a) * (exp (-π*I/4) * pcfUDeriv (I*a) 0) := by
    have hG := pcfW_aux_continuous_Gamma (s := 1/4) (by norm_num)
    have : (fun a : ℝ => exp (I*pcfWRho a) * (exp (-π*I/4) * pcfUDeriv (I*a) 0)) = fun a : ℝ =>
        exp (I*pcfWRho a) * (exp (-π*I/4) *
          (-(Real.sqrt π : ℂ) / ((2:ℂ)^(I*a/2-1/4) * Gamma ((1/4:ℝ) + I*a/2)))) := by
      funext a; rw [pcfUDeriv_zero]; push_cast; ring_nf
    rw [this]
    refine hρc.mul (continuous_const.mul (continuous_const.div (Continuous.mul ?_ hG) fun a =>
      mul_ne_zero (by simp) (Complex.Gamma_ne_zero_of_re_pos (by norm_num))))
    exact continuous_const.cpow (by fun_prop) (fun _ => Or.inl (by norm_num))
  -- products of real and imaginary parts
  have hprod : ∀ a : ℝ, 0 < (exp (I*pcfWRho a) * pcfU (I*a) 0).re *
      (exp (I*pcfWRho a) * pcfU (I*a) 0).im := fun a => by
    obtain ⟨r, hr, h⟩ := pcfW_aux_V_sq_pos a
    generalize exp (I*pcfWRho a) * pcfU (I*a) 0 = V at h ⊢
    have hB := Real.exp_pos (-π*a/2)
    generalize Real.exp (π*a/2) = A at h
    generalize Real.exp (-π*a/2) = B at h hB
    have := congrArg Complex.im h
    rw [sq, Complex.mul_im] at this
    have hR : (↑r * ((↑A + I * ↑B) / 2 : ℂ)).im = r * B / 2 := by simp; ring
    rw [hR] at this
    nlinarith
  have hprod' : ∀ a : ℝ, (exp (I*pcfWRho a) * (exp (-π*I/4) * pcfUDeriv (I*a) 0)).re *
      (exp (I*pcfWRho a) * (exp (-π*I/4) * pcfUDeriv (I*a) 0)).im < 0 := fun a => by
    obtain ⟨r, hr, h⟩ := pcfW_aux_V'_sq_pos a
    generalize exp (I*pcfWRho a) * (exp (-π*I/4) * pcfUDeriv (I*a) 0) = V at h ⊢
    have hB := Real.exp_pos (-π*a/2)
    generalize Real.exp (π*a/2) = A at h
    generalize Real.exp (-π*a/2) = B at h hB
    have := congrArg Complex.im h
    rw [sq, Complex.mul_im] at this
    have hR : (↑r * conj ((↑A + I * ↑B) / 2 : ℂ)).im = -(r * B / 2) := by
      simp [map_div₀, map_ofNat]; ring
    rw [hR] at this
    nlinarith
  have hρ0 : pcfWRho 0 = π/8 := by simp [pcfWRho, pcfGammaPhase]
  have hc8 : 0 < Real.cos (π/8) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hG3 : Gamma (3/4:ℂ) = (Real.Gamma (3/4) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; rfl
  have hG1 : Gamma (1/4:ℂ) = (Real.Gamma (1/4) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; rfl
  have hp1 : (2:ℂ)^(1/4:ℂ) = ((2:ℝ)^(1/4:ℝ) : ℝ) := by
    rw [Complex.ofReal_cpow (by norm_num)]; push_cast; rfl
  have hp2 : (2:ℂ)^(-1/4:ℂ) = ((2:ℝ)^(-1/4:ℝ) : ℝ) := by
    rw [Complex.ofReal_cpow (by norm_num)]; push_cast; rfl
  have g3p := Real.Gamma_pos_of_pos (show (0:ℝ) < 3/4 by norm_num)
  have g1p := Real.Gamma_pos_of_pos (show (0:ℝ) < 1/4 by norm_num)
  have hV0 : 0 < (exp (I*pcfWRho 0) * pcfU (I*(0:ℝ)) 0).re := by
    rw [hρ0, show I*((0:ℝ):ℂ) = 0 by simp, pcfU_zero,
      show (0:ℂ)/2+1/4 = 1/4 by ring, show (3/4:ℂ)+0/2 = 3/4 by ring, hG3, hp1,
      show (Real.sqrt π : ℂ) / ((((2:ℝ)^(1/4:ℝ) : ℝ) : ℂ) * (Real.Gamma (3/4) : ℂ)) =
        ((Real.sqrt π / ((2:ℝ)^(1/4:ℝ) * Real.Gamma (3/4)) : ℝ) : ℂ) by push_cast; ring,
      Complex.re_mul_ofReal, mul_comm I, Complex.exp_ofReal_mul_I_re]
    positivity
  have hV'0 : (exp (I*pcfWRho 0) * (exp (-π*I/4) * pcfUDeriv (I*(0:ℝ)) 0)).re < 0 := by
    rw [hρ0, show I*((0:ℝ):ℂ) = 0 by simp, pcfUDeriv_zero,
      show (0:ℂ)/2-1/4 = -1/4 by ring, show (1/4:ℂ)+0/2 = 1/4 by ring, hG1, hp2,
      show -(Real.sqrt π : ℂ) / ((((2:ℝ)^(-1/4:ℝ) : ℝ) : ℂ) * (Real.Gamma (1/4) : ℂ)) =
        ((-(Real.sqrt π / ((2:ℝ)^(-1/4:ℝ) * Real.Gamma (1/4))) : ℝ) : ℂ) by push_cast; ring,
      ← mul_assoc, ← Complex.exp_add,
      show I * ((π/8 : ℝ) : ℂ) + -π*I/4 = ((-(π/8) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    have : 0 < Real.sqrt π / ((2:ℝ)^(-1/4:ℝ) * Real.Gamma (1/4)) := by positivity
    nlinarith
  have hre : ∀ a : ℝ, 0 < (exp (I*pcfWRho a) * pcfU (I*a) 0).re :=
    pcfW_aux_pos_of_continuous (f := fun a : ℝ => (exp (I*pcfWRho a) * pcfU (I*a) 0).re)
      (Complex.continuous_re.comp hVc) (fun a h => by
        have := hprod a; rw [show (exp (I*pcfWRho a) * pcfU (I*a) 0).re = 0 from h, zero_mul] at this
        exact lt_irrefl _ this) hV0
  have hre' : ∀ a : ℝ, 0 < -(exp (I*pcfWRho a) * (exp (-π*I/4) * pcfUDeriv (I*a) 0)).re :=
    pcfW_aux_pos_of_continuous
      (f := fun a : ℝ => -(exp (I*pcfWRho a) * (exp (-π*I/4) * pcfUDeriv (I*a) 0)).re)
      (Complex.continuous_re.comp hV'c).neg (fun a h => by
        have := hprod' a; rw [neg_eq_zero.mp h, zero_mul] at this; exact lt_irrefl _ this)
      (neg_pos.mpr hV'0)
  refine ⟨⟨hre a, ?_⟩, ⟨neg_pos.mp (hre' a), ?_⟩⟩
  · exact pos_of_mul_pos_right (hprod a) (hre a).le
  · have h1 := hprod' a
    have h2 := hre' a
    nlinarith

/-- Norm facts for the connection formula. -/
lemma pcfW_aux_norms (a : ℝ) :
    ‖exp (I*pcfWRho a) * pcfU (I*a) 0‖ = Real.sqrt π / ((2:ℝ)^(1/4:ℝ) * ‖Gamma (3/4+I*a/2)‖) ∧
    ‖exp (I*pcfWRho a) * (exp (-π*I/4) * pcfUDeriv (I*a) 0)‖ =
      Real.sqrt π * (2:ℝ)^(1/4:ℝ) / ‖Gamma (1/4+I*a/2)‖ ∧
    ‖Gamma (1/4+I*a/2)‖ * ‖Gamma (3/4+I*a/2)‖ *
      ‖((Real.exp (π*a/2) : ℝ) + I * (Real.exp (-π*a/2) : ℝ)) / 2‖ = π := by
  have he : ∀ x : ℝ, ‖exp (I*x)‖ = 1 := fun x => by rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x
  have he4 : ‖exp (-π*I/4)‖ = 1 := by
    rw [show -(π:ℂ)*I/4 = ((-π/4 : ℝ) : ℂ) * I by push_cast; ring]; exact Complex.norm_exp_ofReal_mul_I _
  have he4' : ‖exp (π*I/4)‖ = 1 := by
    rw [show (π:ℂ)*I/4 = ((π/4 : ℝ) : ℂ) * I by push_cast; ring]; exact Complex.norm_exp_ofReal_mul_I _
  have h2 : ∀ w : ℂ, ‖(2:ℂ)^w‖ = (2:ℝ)^w.re := fun w => by
    rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos two_pos]
  have hsq : ‖(Real.sqrt π : ℂ)‖ = Real.sqrt π := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_mul, he, one_mul, pcfU_zero, norm_div, norm_mul, h2, hsq]
    congr 3; simp
  · rw [norm_mul, he, one_mul, norm_mul, he4, one_mul, pcfUDeriv_zero, norm_div, norm_mul, h2,
      norm_neg, hsq]
    have : (I * (a:ℂ) / 2 - 1/4).re = -(1/4) := by simp
    rw [this, Real.rpow_neg (by norm_num), show I*(a:ℂ)/2 = I*a/2 by ring]
    field_simp
  · rw [← pcfW_aux_T, norm_mul, he4', one_mul, Complex.norm_conj]
    have Rf := Complex.Gamma_mul_Gamma_one_sub (1/4+I*a/2)
    rw [show 1-(1/4+I*(a:ℂ)/2) = conj (3/4+I*a/2) by simp [map_add, map_mul, map_div₀, map_ofNat]; ring,
      Complex.Gamma_conj] at Rf
    have := congrArg norm Rf
    rw [norm_mul, Complex.norm_conj, norm_div, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le] at this
    have hS : sin (π*(1/4+I*a/2)) ≠ 0 := by
      intro h; rw [h, div_zero] at Rf
      exact mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
        ((map_ne_zero _).mpr (Complex.Gamma_ne_zero_of_re_pos (by norm_num))) Rf
    rw [this, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hS)]

/-- Real identities linking `K = √(1+e^{2πa}) - e^{πa}` and `N = ‖(e^{πa/2} + i e^{-πa/2})/2‖`. -/
lemma pcfW_aux_K (a : ℝ) {A B N : ℝ} (hA : A = Real.exp (π*a/2)) (hB : B = Real.exp (-π*a/2))
    (hN : N = ‖((A : ℂ) + I * B) / 2‖) :
    pcfWK a * A * (2*N + A) = 1 ∧ 2*A*N - A^2 = pcfWK a ∧ A*B = 1 := by
  have hA0 : 0 < A := hA ▸ Real.exp_pos _
  have hAB : A * B = 1 := by rw [hA, hB, ← Real.exp_add]; ring_nf; simp
  have hN2 : N^2 = (A^2 + B^2)/4 := by
    rw [hN, Complex.sq_norm, Complex.normSq_apply]
    simp; ring
  have hN0 : 0 ≤ N := hN ▸ norm_nonneg _
  have hE2 : A^2 = Real.exp (π*a) := by rw [hA, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hE4 : A^4 = Real.exp (2*π*a) := by rw [hA, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hQ := Real.sq_sqrt (show 0 ≤ 1 + Real.exp (2*π*a) by positivity)
  have hQ0 := Real.sqrt_nonneg (1 + Real.exp (2*π*a))
  have h2NA : 2*N*A = Real.sqrt (1 + Real.exp (2*π*a)) := by
    have hsq : (2*N*A)^2 = (Real.sqrt (1 + Real.exp (2*π*a)))^2 := by
      rw [hQ, ← hE4]
      have : (2*N*A)^2 = 4*N^2*A^2 := by ring
      rw [this, hN2]
      have : B = A⁻¹ := eq_inv_of_mul_eq_one_right hAB
      rw [this]; field_simp; ring
    exact (pow_left_inj₀ (by positivity) hQ0 two_ne_zero).mp hsq
  have hK := (pcfWK_recip a).2
  have hKpos := (pcfWK_recip a).1
  refine ⟨?_, ?_, hAB⟩
  · have : pcfWK a * A * (2*N + A) =
        pcfWK a * (Real.sqrt (1 + Real.exp (2*π*a)) + Real.exp (π*a)) := by
      rw [← h2NA, ← hE2]; ring
    rw [this, ← hK, mul_inv_cancel₀ hKpos.ne']
  · rw [show 2*A*N = 2*N*A by ring, h2NA, hE2, pcfWK]

/-- Real and imaginary parts of `V` from `V² = r T` (or `r T̄`). -/
lemma pcfW_aux_sq_re_im {V T : ℂ} {r : ℝ} (hr : 0 ≤ r) (h : V^2 = r * T ∨ V^2 = r * conj T) :
    V.re^2 = (r * ‖T‖ + r * T.re)/2 ∧ V.im^2 = (r * ‖T‖ - r * T.re)/2 := by
  have hn : V.re^2 + V.im^2 = r * ‖T‖ := by
    have : ‖V‖^2 = ‖V^2‖ := (norm_pow V 2).symm
    rw [Complex.sq_norm, Complex.normSq_apply] at this
    rcases h with h | h <;> rw [h, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr] at this <;>
      [skip; rw [Complex.norm_conj] at this] <;> nlinarith
  have hre : V.re^2 - V.im^2 = r * T.re := by
    rcases h with h | h <;> have := congrArg Complex.re h <;> simp [sq] at this <;> nlinarith
  constructor <;> linarith

/-- The four scalar identities behind the connection formulas of DLMF 12.14(iv). -/
lemma pcfW_aux_scalar (a : ℝ) :
    let V := exp (I*pcfWRho a) * pcfU (I*a) 0
    let V' := exp (I*pcfWRho a) * (exp (-π*I/4) * pcfUDeriv (I*a) 0)
    pcfWZero a = Real.sqrt (pcfWK a/2) * Real.exp (π*a/4) * (2 * V.re) ∧
    -pcfWDerivZero a = Real.sqrt (pcfWK a/2) * Real.exp (π*a/4) * (2 * -V'.re) ∧
    pcfWZero a = 2 * V.im * Real.exp (π*a/4) / Real.sqrt (2*pcfWK a) ∧
    -pcfWDerivZero a = 2 * V'.im * Real.exp (π*a/4) / Real.sqrt (2*pcfWK a) := by
  intro V V'
  obtain ⟨⟨hx, hy⟩, ⟨hx', hy'⟩⟩ := pcfW_aux_signs a
  obtain ⟨r, hr, hV⟩ := pcfW_aux_V_sq_pos a
  obtain ⟨r', hr', hV'⟩ := pcfW_aux_V'_sq_pos a
  obtain ⟨nV, nV', nP⟩ := pcfW_aux_norms a
  set A := Real.exp (π*a/2) with hA
  set B := Real.exp (-π*a/2) with hB
  set T : ℂ := ((A:ℂ) + I * B) / 2 with hT
  set N := ‖T‖ with hN
  obtain ⟨K1, K2, hAB⟩ := pcfW_aux_K a hA hB hN
  have hTre : T.re = A/2 := by simp [hT]
  obtain ⟨hx2, hy2⟩ := pcfW_aux_sq_re_im hr.le (Or.inl hV)
  obtain ⟨hx2', hy2'⟩ := pcfW_aux_sq_re_im hr'.le (Or.inr hV')
  rw [hTre, ← hN] at hx2 hy2 hx2' hy2'
  set n1 := ‖Gamma (1/4+I*a/2)‖ with hn1
  set n3 := ‖Gamma (3/4+I*a/2)‖ with hn3
  set c := (2:ℝ)^(1/4:ℝ) with hc
  have hn1p : 0 < n1 := norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
  have hn3p : 0 < n3 := norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
  have hcp : 0 < c := by positivity
  have hc4 : c^4 = 2 := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have hNp : 0 < N := by
    rw [hN, norm_pos_iff]; intro h0; have := congrArg Complex.re h0
    rw [hTre] at this; simp at this; linarith [Real.exp_pos (π*a/2)]
  have hA0 : 0 < A := Real.exp_pos _
  have hE : Real.exp (π*a/4)^2 = A := by rw [hA, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hK0 := (pcfWK_recip a).1
  have hs := Real.sq_sqrt (show 0 ≤ pcfWK a / 2 by positivity)
  have hs' := Real.sq_sqrt (show 0 ≤ 2 * pcfWK a by positivity)
  have hs'p : 0 < Real.sqrt (2 * pcfWK a) := Real.sqrt_pos.mpr (by positivity)
  -- `‖V‖² = r N`, `‖V'‖² = r' N`
  have hVn : V.re^2 + V.im^2 = r * N := by linarith
  have hVn' : V'.re^2 + V'.im^2 = r' * N := by linarith
  have nV2 : V.re^2 + V.im^2 = π / (c^2 * n3^2) := by
    have : ‖V‖^2 = V.re^2 + V.im^2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [← this, nV, div_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le]
  have nV2' : V'.re^2 + V'.im^2 = π * c^2 / n1^2 := by
    have : ‖V'‖^2 = V'.re^2 + V'.im^2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [← this, nV', div_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le]
  -- `2^{-3/4} = c⁻³`, `2^{-1/4} = c⁻¹`
  have ht3 : (2:ℝ)^(-3/4:ℝ) = (c^3)⁻¹ := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_neg (by norm_num)]
    norm_num
  have ht1 : (2:ℝ)^(-1/4:ℝ) = c⁻¹ := by
    rw [hc, ← Real.rpow_neg (by norm_num)]; norm_num
  have hW0 : pcfWZero a = (c^3)⁻¹ * Real.sqrt (n1/n3) := by
    rw [pcfWZero, ht3, norm_div]
  have hW1 : -pcfWDerivZero a = c⁻¹ * Real.sqrt (n3/n1) := by
    rw [pcfWDerivZero, ht1, norm_div]; ring
  have hq1 : n1 / n3 = r * c^2 := by
    have e : r * N * (c^2 * n3^2) = π := (eq_div_iff (by positivity)).mp (hVn.symm.trans nV2)
    have : n1 * (n3 * N) = (r * c^2 * n3) * (n3 * N) := by
      rw [show n1 * (n3 * N) = n1 * n3 * N by ring, nP, ← e]; ring
    rw [mul_right_cancel₀ (by positivity) this]; field_simp
  have hq3 : n3 / n1 = r' / c^2 := by
    have e : r' * N * n1^2 = π * c^2 := (eq_div_iff (by positivity)).mp (hVn'.symm.trans nV2')
    have : (n3 * c^2) * (n1 * N) = (r' * n1) * (n1 * N) := by
      linear_combination c^2 * nP - e
    rw [div_eq_div_iff hn1p.ne' (by positivity), mul_right_cancel₀ (by positivity) this]
  have hEp := Real.exp_pos (π*a/4)
  have hW0p : 0 ≤ pcfWZero a := by rw [hW0]; positivity
  have hW1p : 0 ≤ -pcfWDerivZero a := by rw [hW1]; positivity
  have L0 : pcfWZero a ^ 2 = r / 2 := by
    rw [hW0, mul_pow, Real.sq_sqrt (by positivity), hq1,
      show ((c^3)⁻¹)^2 * (r*c^2) = r / c^4 by field_simp, hc4]
  have L1 : (-pcfWDerivZero a) ^ 2 = r' / 2 := by
    rw [hW1, mul_pow, Real.sq_sqrt (by positivity), hq3,
      show (c⁻¹)^2 * (r'/c^2) = r' / c^4 by field_simp, hc4]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (pow_left_inj₀ hW0p (by positivity) two_ne_zero).mp ?_
    rw [L0, mul_pow, mul_pow, hs, hE, mul_pow, hx2]
    linear_combination (-(r/2)) * K1
  · refine (pow_left_inj₀ hW1p
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hEp.le) (by linarith)) two_ne_zero).mp ?_
    rw [L1, mul_pow, mul_pow, hs, hE, mul_pow, neg_sq, hx2']
    linear_combination (-(r'/2)) * K1
  · refine (pow_left_inj₀ hW0p (by positivity) two_ne_zero).mp ?_
    rw [L0, div_pow, mul_pow, mul_pow, hs', hE, hy2]
    field_simp
    linear_combination (-1:ℝ) * K2
  · refine (pow_left_inj₀ hW1p (by positivity) two_ne_zero).mp ?_
    rw [L1, div_pow, mul_pow, mul_pow, hs', hE, hy2']
    field_simp
    linear_combination (-1:ℝ) * K2

end DLMF.Confluent
end
