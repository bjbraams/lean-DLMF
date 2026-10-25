/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ParabolicCylinder.Integrals
public import DLMFMathlib.Analysis.ODE.PowerSeriesUniqueness
public import DLMF.ParabolicCylinder.SectorAsymptotics

/-!
# The oscillatory parabolic cylinder function W

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat ComplexConjugate
namespace DLMF.Confluent

open DLMF.Bessel

/-- pcfWZero. -/
@[dlmf 12.14.E1]
def pcfWZero (a : ℝ) : ℝ :=
  2^(-3/4:ℝ)*Real.sqrt ‖Gamma (1/4+I*a/2)/Gamma (3/4+I*a/2)‖

/-- pcfWDerivZero. -/
@[dlmf 12.14.E2]
def pcfWDerivZero (a : ℝ) : ℝ :=
  -2^(-1/4:ℝ)*Real.sqrt ‖Gamma (3/4+I*a/2)/Gamma (1/4+I*a/2)‖

/-- pcfWEven. -/
@[dlmf 12.14.E15]
def pcfWEven (a z : ℂ) : ℂ :=
  pcfEven (-I*a) (exp (π*I/4)*z)

/-- pcfWOdd. -/
@[dlmf 12.14.E16]
def pcfWOdd (a z : ℂ) : ℂ :=
  exp (-π*I/4)*pcfOdd (-I*a) (exp (π*I/4)*z)

/-- pcfW. -/
@[dlmf 12.14.E8]
def pcfW (a : ℝ) (z : ℂ) : ℂ :=
  pcfWZero a*pcfWEven a z+pcfWDerivZero a*pcfWOdd a z

/-- pcfW initial. -/
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
lemma exp_pi_I_quarter_sq : exp (π*I/4)^2 = I := by
  rw [← Complex.exp_nat_mul, show ((2:ℕ):ℂ)*(π*I/4) = (π/2:ℝ)*I by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  simp

/-- `e^{-iπ/4} e^{iπ/4} = 1`. -/
lemma exp_neg_pi_I_quarter_mul : exp (-π*I/4) * exp (π*I/4) = 1 := by
  rw [← Complex.exp_add]; ring_nf; simp

/-- pcfWEven kummer. -/
@[dlmf 12.14.E15]
theorem pcfWEven_kummer (a z : ℂ) :
    pcfWEven a z = exp (-I*z^2/4)*kummerM (1/4-I*a/2) (1/2) (I*z^2/2) ∧ pcfWEven a z = exp (I*z^2/4)*kummerM (1/4+I*a/2) (1/2) (-I*z^2/2) := by
  constructor
  · rw [pcfWEven, pcfEven, mul_pow, exp_pi_I_quarter_sq, show -I*a/2 + 1/4 = 1/4-I*a/2 by ring,
      show -(I*z^2)/4 = -I*z^2/4 by ring]
  · rw [pcfWEven, pcfEven_kummer_alternative, mul_pow, exp_pi_I_quarter_sq,
      show -(-I*a)/2 + 1/4 = 1/4+I*a/2 by ring, show -(I*z^2)/2 = -I*z^2/2 by ring]

/-- pcfWOdd kummer. -/
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
lemma IsWeberSol.hasDerivAt_rot {b : ℂ} {f f' : ℂ → ℂ} (hf : IsWeberSol b f f') (c z : ℂ) :
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

/-- pcfW ode. -/
@[dlmf 12.2.E3]
theorem pcfW_ode (a : ℝ) :
    IsOscillatoryCylinderSolution a (pcfW a) := by
  intro z
  rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, deriv_pcfW,
    (hasDerivAt_pcfWDeriv a z).deriv]
  ring

/-- `W(a, z̄) = conj W(a, z)`. -/
lemma conj_pcfW_conj (a : ℝ) (z : ℂ) : conj (pcfW a (conj z)) = pcfW a z := by
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
lemma conj_pcfWDeriv_ofReal (a x : ℝ) : conj (pcfWDeriv a x) = pcfWDeriv a x := by
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
lemma pcfWZero_mul_pcfWDerivZero (a : ℝ) : pcfWZero a * pcfWDerivZero a = -1/2 := by
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

/-- pcfW wronskian. -/
@[dlmf 12.14.E3]
theorem pcfW_wronskian (a : ℝ) (z : ℂ) :
    pcfW a z*(-deriv (pcfW a) (-z))-pcfW a (-z)*deriv (pcfW a) z=1 := by
  rw [deriv_pcfW, pcfW_wronskian_aux]
  have := pcfWZero_mul_pcfWDerivZero a
  have : (pcfWZero a : ℂ) * pcfWDerivZero a = -1/2 := by exact_mod_cast this
  linear_combination (-2) * this

/-- pcfWK. -/
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

/-- pcfGammaPhase spec. -/
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

/-- pcfWRho. -/
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
lemma exp_neg_pi_I_quarter_eq : exp (-π*I/4) = -I * exp (π*I/4) := by
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
lemma continuous_pcfGammaPhase : Continuous pcfGammaPhase :=
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

/-- Two entire solutions of `w'' = (a - z²/4) w` with the same data at `0` coincide. -/
lemma weberOsc_eq_of_initial {a : ℂ} {f f1 g g1 : ℂ → ℂ}
    (hf : ∀ z, HasDerivAt f (f1 z) z ∧ HasDerivAt f1 ((a - z^2/4) * f z) z)
    (hg : ∀ z, HasDerivAt g (g1 z) z ∧ HasDerivAt g1 ((a - z^2/4) * g z) z)
    (h0 : f 0 = g 0) (h1 : f1 0 = g1 0) : f = g := by
  have df : deriv f = f1 := funext fun z => (hf z).1.deriv
  have dg : deriv g = g1 := funext fun z => (hg z).1.deriv
  have hfd : Differentiable ℂ f := fun z => (hf z).1.differentiableAt
  have hgd : Differentiable ℂ g := fun z => (hg z).1.differentiableAt
  have h := ODE.eqOn_of_ode (p := fun _ => (0:ℂ)) (q := fun z => a - z^2/4) isOpen_univ
    isPreconnected_univ (fun z _ => hfd.analyticAt z) (fun z _ => hgd.analyticAt z) (mem_univ 0)
    (by fun_prop) (by fun_prop)
    (fun z _ => by rw [df, (hf z).2.deriv]; ring) (fun z _ => by rw [dg, (hg z).2.deriv]; ring)
    h0 (by rw [df, dg, h1])
  exact funext fun z => h (mem_univ z)

/-- `e^{-iπ/4}² = -i`. -/
lemma exp_neg_pi_I_quarter_sq : exp (-π*I/4)^2 = -I := by
  have h1 := exp_neg_pi_I_quarter_mul
  have h2 := exp_pi_I_quarter_sq
  linear_combination I * exp (-π*I/4)^2 * h2 - I * (exp (-π*I/4) * exp (π*I/4) + 1) * h1 +
    exp (-π*I/4)^2 * I_sq

/-- `U(± i a, c z)` for `c = e^{∓iπ/4}` solves `w'' = (a - z²/4) w`. -/
lemma pcfU_rot_weberOsc (a : ℝ) (z : ℂ) :
    (HasDerivAt (fun w => pcfU (I*a) (exp (-π*I/4) * w))
      (exp (-π*I/4) * pcfUDeriv (I*a) (exp (-π*I/4) * z)) z ∧
    HasDerivAt (fun w => exp (-π*I/4) * pcfUDeriv (I*a) (exp (-π*I/4) * w))
      ((a - z^2/4) * pcfU (I*a) (exp (-π*I/4) * z)) z) ∧
    (HasDerivAt (fun w => pcfU (-I*a) (exp (π*I/4) * w))
      (exp (π*I/4) * pcfUDeriv (-I*a) (exp (π*I/4) * z)) z ∧
    HasDerivAt (fun w => exp (π*I/4) * pcfUDeriv (-I*a) (exp (π*I/4) * w))
      ((a - z^2/4) * pcfU (-I*a) (exp (π*I/4) * z)) z) := by
  obtain ⟨h1, h2⟩ := (isWeberSol_pcfU (I*a)).hasDerivAt_rot (exp (-π*I/4)) z
  obtain ⟨h3, h4⟩ := (isWeberSol_pcfU (-I*a)).hasDerivAt_rot (exp (π*I/4)) z
  refine ⟨⟨h1, h2.congr_deriv ?_⟩, ⟨h3, h4.congr_deriv ?_⟩⟩
  · rw [mul_pow, exp_neg_pi_I_quarter_sq]
    linear_combination (z^2/4 - a) * pcfU (I*a) (exp (-π*I/4) * z) * I_sq
  · rw [mul_pow, exp_pi_I_quarter_sq]
    linear_combination (z^2/4 - a) * pcfU (-I*a) (exp (π*I/4) * z) * I_sq

/-- `conj (e^{ix}) = e^{-ix}` for real `x`. -/
lemma conj_exp_I_ofReal (x : ℝ) : conj (exp (I*x)) = exp (-I*x) := by
  rw [← Complex.exp_conj]; congr 1; simp

/-- `conj (e^{-iπ/4}) = e^{iπ/4}`. -/
lemma conj_exp_neg_pi_I_quarter : conj (exp (-π*I/4)) = exp (π*I/4) := by
  rw [← Complex.exp_conj]; congr 1; simp [map_div₀, map_ofNat]

/-- pcfW connection. -/
@[dlmf 12.14.E4]
theorem pcfW_connection (a : ℝ) (z : ℂ) :
    pcfW a z=(Real.sqrt (pcfWK a/2):ℂ)*exp (π*a/4)*(exp (I*pcfWRho a)*pcfU (I*a) (z*exp (-π*I/4))+exp (-I*pcfWRho a)*pcfU (-I*a) (z*exp (π*I/4))) := by
  set K : ℂ := (Real.sqrt (pcfWK a/2):ℂ)*exp (π*a/4)
  set eρ := exp (I*pcfWRho a)
  set eρ' := exp (-I*pcfWRho a)
  set R : ℂ → ℂ := fun w => K * (eρ * pcfU (I*a) (exp (-π*I/4) * w) +
    eρ' * pcfU (-I*a) (exp (π*I/4) * w))
  set R1 : ℂ → ℂ := fun w => K * (eρ * (exp (-π*I/4) * pcfUDeriv (I*a) (exp (-π*I/4) * w)) +
    eρ' * (exp (π*I/4) * pcfUDeriv (-I*a) (exp (π*I/4) * w)))
  have hR : ∀ w, HasDerivAt R (R1 w) w ∧ HasDerivAt R1 ((a - w^2/4) * R w) w := fun w => by
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := pcfU_rot_weberOsc a w
    exact ⟨((h1.const_mul eρ).add (h3.const_mul eρ')).const_mul K,
      (((h2.const_mul eρ).add (h4.const_mul eρ')).const_mul K).congr_deriv (by ring)⟩
  have hW : ∀ w, HasDerivAt (pcfW a) (pcfWDeriv a w) w ∧
      HasDerivAt (pcfWDeriv a) ((a - w^2/4) * pcfW a w) w :=
    fun w => ⟨hasDerivAt_pcfW a w, hasDerivAt_pcfWDeriv a w⟩
  obtain ⟨s1, s2, -, -⟩ := pcfW_aux_scalar a
  have hK : K = ((Real.sqrt (pcfWK a/2) * Real.exp (π*a/4) : ℝ) : ℂ) := by
    simp only [K]; push_cast; rfl
  have hc1 : eρ' * pcfU (-I*a) 0 = conj (eρ * pcfU (I*a) 0) := by
    rw [map_mul, conj_exp_I_ofReal, conj_pcfU]; congr 2 <;> simp
  have hc2 : eρ' * (exp (π*I/4) * pcfUDeriv (-I*a) 0) =
      conj (eρ * (exp (-π*I/4) * pcfUDeriv (I*a) 0)) := by
    rw [map_mul, map_mul, conj_exp_I_ofReal, conj_exp_neg_pi_I_quarter, conj_pcfUDeriv]
    congr 3 <;> simp
  have h0 : pcfW a 0 = R 0 := by
    rw [(pcfW_initial a).1]
    simp only [R, mul_zero]
    rw [hc1, Complex.add_conj, hK, s1]; push_cast; ring
  have h1 : pcfWDeriv a 0 = R1 0 := by
    have : pcfWDeriv a 0 = pcfWDerivZero a := by
      simp [pcfWDeriv, pcfEvenDeriv_zero, pcfOddDeriv_zero]
    rw [this]
    simp only [R1, mul_zero]
    rw [hc2, Complex.add_conj, hK]
    have s2' : pcfWDerivZero a = Real.sqrt (pcfWK a/2) * Real.exp (π*a/4) *
        (2 * (eρ * (exp (-π*I/4) * pcfUDeriv (I*a) 0)).re) := by linarith
    rw [s2']; push_cast; ring
  have := congrFun (weberOsc_eq_of_initial hW hR h0 h1) z
  rw [this]; simp only [R, mul_comm _ z]

/-- Unnumbered companion connection formula in DLMF 12.14(iv). -/
theorem pcfW_connection_neg (a : ℝ) (z : ℂ) :
    pcfW a (-z)=-I/Real.sqrt (2*pcfWK a)*exp (π*a/4)*(exp (I*pcfWRho a)*pcfU (I*a) (z*exp (-π*I/4))-exp (-I*pcfWRho a)*pcfU (-I*a) (z*exp (π*I/4))) := by
  obtain ⟨-, -, s3, s4⟩ := pcfW_aux_scalar a
  set K : ℂ := -I/Real.sqrt (2*pcfWK a)*exp (π*a/4)
  set eρ := exp (I*pcfWRho a)
  set eρ' := exp (-I*pcfWRho a)
  set R : ℂ → ℂ := fun w => K * (eρ * pcfU (I*a) (exp (-π*I/4) * w) -
    eρ' * pcfU (-I*a) (exp (π*I/4) * w))
  set R1 : ℂ → ℂ := fun w => K * (eρ * (exp (-π*I/4) * pcfUDeriv (I*a) (exp (-π*I/4) * w)) -
    eρ' * (exp (π*I/4) * pcfUDeriv (-I*a) (exp (π*I/4) * w)))
  have hR : ∀ w, HasDerivAt R (R1 w) w ∧ HasDerivAt R1 ((a - w^2/4) * R w) w := fun w => by
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := pcfU_rot_weberOsc a w
    exact ⟨((h1.const_mul eρ).sub (h3.const_mul eρ')).const_mul K,
      (((h2.const_mul eρ).sub (h4.const_mul eρ')).const_mul K).congr_deriv (by ring)⟩
  have hW : ∀ w, HasDerivAt (fun w => pcfW a (-w)) (-pcfWDeriv a (-w)) w ∧
      HasDerivAt (fun w => -pcfWDeriv a (-w)) ((a - w^2/4) * pcfW a (-w)) w := fun w =>
    ⟨((hasDerivAt_pcfW a (-w)).comp w (hasDerivAt_neg w)).congr_deriv (by ring),
      ((hasDerivAt_pcfWDeriv a (-w)).comp w (hasDerivAt_neg w)).neg.congr_deriv (by ring)⟩
  have hsp : (Real.sqrt (2*pcfWK a) : ℂ) ≠ 0 := by
    have := (pcfWK_recip a).1
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity)).ne'
  have hc1 : eρ' * pcfU (-I*a) 0 = conj (eρ * pcfU (I*a) 0) := by
    rw [map_mul, conj_exp_I_ofReal, conj_pcfU]; congr 2 <;> simp
  have hc2 : eρ' * (exp (π*I/4) * pcfUDeriv (-I*a) 0) =
      conj (eρ * (exp (-π*I/4) * pcfUDeriv (I*a) 0)) := by
    rw [map_mul, map_mul, conj_exp_I_ofReal, conj_exp_neg_pi_I_quarter, conj_pcfUDeriv]
    congr 3 <;> simp
  have hE : exp (π*a/4) = ((Real.exp (π*a/4) : ℝ) : ℂ) := by push_cast; rfl
  have h0 : pcfW a (-0) = R 0 := by
    rw [neg_zero, (pcfW_initial a).1]
    simp only [R, mul_zero]
    rw [hc1, Complex.sub_conj, s3]
    simp only [K, hE]
    generalize (eρ * pcfU (I*a) 0).im = y
    push_cast
    field_simp
    linear_combination (y : ℂ) * I_sq
  have h1 : -pcfWDeriv a (-0) = R1 0 := by
    have : pcfWDeriv a 0 = pcfWDerivZero a := by
      simp [pcfWDeriv, pcfEvenDeriv_zero, pcfOddDeriv_zero]
    rw [neg_zero, this]
    simp only [R1, mul_zero]
    rw [hc2, Complex.sub_conj]
    have s4' : -(pcfWDerivZero a : ℂ) = ((2 * (eρ * (exp (-π*I/4) * pcfUDeriv (I*a) 0)).im *
        Real.exp (π*a/4) / Real.sqrt (2*pcfWK a) : ℝ) : ℂ) := by rw [← s4]; push_cast; ring
    rw [s4']
    simp only [K, hE]
    generalize (eρ * (exp (-π*I/4) * pcfUDeriv (I*a) 0)).im = y
    push_cast
    field_simp
    linear_combination (y : ℂ) * I_sq
  have := congrFun (weberOsc_eq_of_initial hW hR h0 h1) z
  rw [this]; simp only [R, mul_comm _ z]

/-- Maclaurin recurrence for the pcfWAlpha coefficients. -/
def pcfWAlpha (a : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => a
  | n+2 => a*pcfWAlpha a (n+1)-1/2*(n+1)*(2*n+1)*pcfWAlpha a n

/-- Maclaurin recurrence for the pcfWBeta coefficients. -/
def pcfWBeta (a : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => a
  | n+2 => a*pcfWBeta a (n+1)-1/2*(n+1)*(2*n+3)*pcfWBeta a n

open scoped ContDiff in
/-- Taylor recurrence at `0` for solutions of `w'' = (a - z²/4) w`. -/
lemma weberOsc_iteratedDeriv_add_two {F F1 : ℂ → ℂ} {a : ℂ}
    (h : ∀ z, HasDerivAt F (F1 z) z ∧ HasDerivAt F1 ((a - z^2/4) * F z) z) (n : ℕ) :
    iteratedDeriv (n+2) F 0 =
      a * iteratedDeriv n F 0 - 1/4 * ((n.descFactorial 2 : ℕ) * iteratedDeriv (n-2) F 0) := by
  have hF : Differentiable ℂ F := fun z => (h z).1.differentiableAt
  have hc : ContDiff ℂ ∞ F := hF.contDiff
  have h1 : deriv F = F1 := funext fun z => (h z).1.deriv
  have h2 : deriv (deriv F) = fun z => a * F z - 1/4 * (z^2 * F z) := by
    rw [h1]; funext z; rw [(h z).2.deriv]; ring
  have hcn : ContDiffAt ℂ n F 0 := (hc.of_le (by exact_mod_cast le_top)).contDiffAt
  have hq : ContDiffAt ℂ n (fun z : ℂ => z^2 * F z) 0 := by fun_prop
  have hA : ContDiffAt ℂ n (fun z : ℂ => a * F z) 0 := by fun_prop
  have hB : ContDiffAt ℂ n (fun z : ℂ => 1/4 * (z^2 * F z)) 0 := by fun_prop
  rw [iteratedDeriv_succ', iteratedDeriv_succ', h2, iteratedDeriv_fun_sub hA hB,
    iteratedDeriv_const_mul a hcn, iteratedDeriv_const_mul _ hq, ODE.iteratedDeriv_pow_mul_zero hcn]


/-- First and second derivatives of `pcfWEven`: Weber's equation `w'' = (a - z²/4) w`. -/
lemma pcfWEven_hasDerivAt_two (a z : ℂ) :
    HasDerivAt (pcfWEven a) (exp (π*I/4) * pcfEvenDeriv (-I*a) (exp (π*I/4)*z)) z ∧
      HasDerivAt (fun w => exp (π*I/4) * pcfEvenDeriv (-I*a) (exp (π*I/4)*w))
        ((a - z^2/4) * pcfWEven a z) z := by
  obtain ⟨h1, h2⟩ := (isWeberSol_pcfEven (-I*a)).hasDerivAt_rot (exp (π*I/4)) z
  refine ⟨h1, h2.congr_deriv ?_⟩
  rw [pcfWEven, mul_pow, exp_pi_I_quarter_sq]
  linear_combination (z^2/4 - a) * pcfEven (-I * a) (exp (↑π * I / 4) * z) * I_sq

/-- First and second derivatives of `pcfWOdd`: Weber's equation `w'' = (a - z²/4) w`. -/
lemma pcfWOdd_hasDerivAt_two (a z : ℂ) :
    HasDerivAt (pcfWOdd a) (exp (-π*I/4) * (exp (π*I/4) * pcfOddDeriv (-I*a) (exp (π*I/4)*z))) z ∧
      HasDerivAt (fun w => exp (-π*I/4) * (exp (π*I/4) * pcfOddDeriv (-I*a) (exp (π*I/4)*w)))
        ((a - z^2/4) * pcfWOdd a z) z := by
  obtain ⟨h1, h2⟩ := (isWeberSol_pcfOdd (-I*a)).hasDerivAt_rot (exp (π*I/4)) z
  refine ⟨h1.const_mul _, (h2.const_mul _).congr_deriv ?_⟩
  rw [pcfWOdd, mul_pow, exp_pi_I_quarter_sq]
  linear_combination (exp (-π*I/4)) * (z^2/4 - a) * pcfOdd (-I * a) (exp (↑π * I / 4) * z) * I_sq

/-- Derivatives of `pcfWEven` at `0`: the `pcfWAlpha` recurrence and vanishing odd orders. -/
lemma pcfWEven_iteratedDeriv (a : ℂ) (n : ℕ) :
    (iteratedDeriv (2*n) (pcfWEven a) 0 = pcfWAlpha a n ∧
      iteratedDeriv (2*n+2) (pcfWEven a) 0 = pcfWAlpha a (n+1)) ∧
    (iteratedDeriv (2*n+1) (pcfWEven a) 0 = 0 ∧ iteratedDeriv (2*n+3) (pcfWEven a) 0 = 0) := by
  have hr := weberOsc_iteratedDeriv_add_two (fun z => pcfWEven_hasDerivAt_two a z)
  have d0 : iteratedDeriv 0 (pcfWEven a) 0 = 1 := by simp [pcfWEven, pcfEven]
  have d1 : iteratedDeriv 1 (pcfWEven a) 0 = 0 := by
    rw [iteratedDeriv_one, (pcfWEven_hasDerivAt_two a 0).1.deriv]; simp [pcfEvenDeriv_zero]
  induction n with
  | zero =>
    refine ⟨⟨by simpa [pcfWAlpha] using d0, ?_⟩, ⟨by simpa using d1, ?_⟩⟩
    · rw [hr 0, d0]; simp [pcfWAlpha]
    · rw [hr 1, d1]; simp
  | succ n ih =>
    refine ⟨⟨by rw [show 2*(n+1) = 2*n+2 by ring]; exact ih.1.2, ?_⟩,
      ⟨by rw [show 2*(n+1)+1 = 2*n+3 by ring]; exact ih.2.2, ?_⟩⟩
    · rw [show 2*(n+1)+2 = (2*n+2)+2 by ring, hr, ih.1.2, show 2*n+2-2 = 2*n by omega, ih.1.1,
        pcfWAlpha]
      simp only [Nat.descFactorial, Nat.succ_sub_one]
      push_cast; ring
    · rw [show 2*(n+1)+3 = (2*n+3)+2 by ring, hr, ih.2.2, show 2*n+3-2 = 2*n+1 by omega, ih.2.1]
      simp

/-- Derivatives of `pcfWOdd` at `0`: the `pcfWBeta` recurrence and vanishing even orders. -/
lemma pcfWOdd_iteratedDeriv (a : ℂ) (n : ℕ) :
    (iteratedDeriv (2*n+1) (pcfWOdd a) 0 = pcfWBeta a n ∧
      iteratedDeriv (2*n+3) (pcfWOdd a) 0 = pcfWBeta a (n+1)) ∧
    (iteratedDeriv (2*n) (pcfWOdd a) 0 = 0 ∧ iteratedDeriv (2*n+2) (pcfWOdd a) 0 = 0) := by
  have hr := weberOsc_iteratedDeriv_add_two (fun z => pcfWOdd_hasDerivAt_two a z)
  have d0 : iteratedDeriv 0 (pcfWOdd a) 0 = 0 := by simp [pcfWOdd, pcfOdd]
  have d1 : iteratedDeriv 1 (pcfWOdd a) 0 = 1 := by
    rw [iteratedDeriv_one, (pcfWOdd_hasDerivAt_two a 0).1.deriv, ← mul_assoc,
      exp_neg_pi_I_quarter_mul]; simp [pcfOddDeriv_zero]
  induction n with
  | zero =>
    refine ⟨⟨by simpa [pcfWBeta] using d1, ?_⟩, ⟨by simpa using d0, ?_⟩⟩
    · rw [hr 1, d1]; simp [pcfWBeta]
    · rw [hr 0, d0]; simp
  | succ n ih =>
    refine ⟨⟨by rw [show 2*(n+1)+1 = 2*n+3 by ring]; exact ih.1.2, ?_⟩,
      ⟨by rw [show 2*(n+1) = 2*n+2 by ring]; exact ih.2.2, ?_⟩⟩
    · rw [show 2*(n+1)+3 = (2*n+3)+2 by ring, hr, ih.1.2, show 2*n+3-2 = 2*n+1 by omega, ih.1.1,
        pcfWBeta]
      simp only [Nat.descFactorial, Nat.succ_sub_one]
      push_cast; ring
    · rw [show 2*(n+1)+2 = (2*n+2)+2 by ring, hr, ih.2.2, show 2*n+2-2 = 2*n by omega, ih.2.1]
      simp

/-- pcfWEven series. -/
@[dlmf 12.14.E9, dlmf 12.14.E11, dlmf 12.14.E12]
theorem pcfWEven_series (a z : ℂ) :
    HasSum (fun n : ℕ => pcfWAlpha a n*z^(2*n)/((2*n).factorial:ℂ)) (pcfWEven a z) := by
  have hd : Differentiable ℂ (pcfWEven a) := fun w => (pcfWEven_hasDerivAt_two a w).1.differentiableAt
  have hT := Complex.hasSum_taylorSeries_of_entire hd 0 z
  have hinj : Function.Injective (fun n : ℕ => 2*n) := fun m n h => by simpa using h
  rw [← hinj.hasSum_iff] at hT
  · convert hT using 1
    funext n
    simp only [Function.comp_apply, sub_zero, smul_eq_mul, (pcfWEven_iteratedDeriv a n).1.1]
    field_simp
  · intro x hx
    obtain ⟨k, rfl⟩ : Odd x := by
      rcases Nat.even_or_odd x with ⟨k, hk⟩ | h
      · exact absurd ⟨k, by simp [hk]; ring⟩ hx
      · exact h
    simp [(pcfWEven_iteratedDeriv a k).2.1]

/-- pcfWOdd series. -/
@[dlmf 12.14.E10, dlmf 12.14.E11, dlmf 12.14.E12]
theorem pcfWOdd_series (a z : ℂ) :
    HasSum (fun n : ℕ => pcfWBeta a n*z^(2*n+1)/((2*n+1).factorial:ℂ)) (pcfWOdd a z) := by
  have hd : Differentiable ℂ (pcfWOdd a) := fun w => (pcfWOdd_hasDerivAt_two a w).1.differentiableAt
  have hT := Complex.hasSum_taylorSeries_of_entire hd 0 z
  have hinj : Function.Injective (fun n : ℕ => 2*n+1) := fun m n h => by simpa using h
  rw [← hinj.hasSum_iff] at hT
  · convert hT using 1
    funext n
    simp only [Function.comp_apply, sub_zero, smul_eq_mul, (pcfWOdd_iteratedDeriv a n).1.1]
    field_simp
  · intro x hx
    obtain ⟨k, rfl⟩ : Even x := by
      rcases Nat.even_or_odd x with h | ⟨k, hk⟩
      · exact h
      · exact absurd ⟨k, hk.symm⟩ hx
    simp [← two_mul, (pcfWOdd_iteratedDeriv a k).2.1]

/-- `Γ(1/4) Γ(3/4) = π √2`. -/
lemma real_Gamma_quarter_mul : Real.Gamma (1/4) * Real.Gamma (3/4) = π * Real.sqrt 2 := by
  have h := Real.Gamma_mul_Gamma_one_sub (1/4)
  rw [show (1:ℝ) - 1/4 = 3/4 by norm_num, show π * (1/4) = π/4 by ring, Real.sin_pi_div_four] at h
  rw [h]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  rw [Real.sq_sqrt (by norm_num)]

/-- `W(0,0) = 2^{-3/4} √(Γ(1/4)/Γ(3/4))`. -/
lemma pcfWZero_zero : pcfWZero 0 = 2^(-3/4:ℝ) * Real.sqrt (Real.Gamma (1/4) / Real.Gamma (3/4)) := by
  rw [pcfWZero]
  congr 2
  simp only [Complex.ofReal_zero, mul_zero, zero_div, add_zero]
  rw [show (1/4:ℂ) = ((1/4:ℝ):ℂ) by push_cast; ring, show (3/4:ℂ) = ((3/4:ℝ):ℂ) by push_cast; ring,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal, ← Complex.ofReal_div, Complex.norm_real,
    Real.norm_of_nonneg (div_nonneg (Real.Gamma_pos_of_pos (by norm_num)).le (Real.Gamma_pos_of_pos (by norm_num)).le)]

/-- `W'(0,0) = -2^{-1/4} √(Γ(3/4)/Γ(1/4))`. -/
lemma pcfWDerivZero_zero : pcfWDerivZero 0 = -2^(-1/4:ℝ) * Real.sqrt (Real.Gamma (3/4) / Real.Gamma (1/4)) := by
  rw [pcfWDerivZero]
  congr 2
  simp only [Complex.ofReal_zero, mul_zero, zero_div, add_zero]
  rw [show (1/4:ℂ) = ((1/4:ℝ):ℂ) by push_cast; ring, show (3/4:ℂ) = ((3/4:ℝ):ℂ) by push_cast; ring,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal, ← Complex.ofReal_div, Complex.norm_real,
    Real.norm_of_nonneg (div_nonneg (Real.Gamma_pos_of_pos (by norm_num)).le (Real.Gamma_pos_of_pos (by norm_num)).le)]

lemma rpow_quarter_pow_four {y : ℝ} (hy : 0 ≤ y) (r : ℝ) : (y^(r/4))^4 = y^r := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy]; norm_num

/-- Equality of positive reals from equality of fourth powers. -/
lemma eq_of_pow_four_eq {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (h : u^4 = v^4) : u = v :=
  (pow_left_inj₀ hu hv (by norm_num : (4:ℕ) ≠ 0)).mp h

/-- The real coefficient of `J_{-1/4}` in `W(0,x)`. -/
lemma pcfW_zero_coeffA {x : ℝ} (hx : 0 < x) :
    pcfWZero 0 * Real.Gamma (3/4) * (x^2/8)^(1/4:ℝ) = 2^(-5/4:ℝ) * (π*x)^(1/2:ℝ) := by
  have g1 := Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 1/4)
  have g3 := Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 3/4)
  rw [pcfWZero_zero]
  apply eq_of_pow_four_eq (by positivity) (by positivity)
  rw [mul_pow, mul_pow, mul_pow, mul_pow, show (-3/4:ℝ) = -3/4 by ring, show (1/4:ℝ) = 1/4 by ring,
    show (-3/4:ℝ) = (-3)/4 by ring, rpow_quarter_pow_four (by norm_num), show (1/4:ℝ) = 1/4 from rfl,
    rpow_quarter_pow_four (by positivity) 1, show (-5/4:ℝ) = (-5)/4 by ring, rpow_quarter_pow_four (by norm_num),
    show (1/2:ℝ) = 2/4 by norm_num, rpow_quarter_pow_four (by positivity),
    show (Real.sqrt (Real.Gamma (1/4) / Real.Gamma (3/4)))^4 = (Real.Gamma (1/4) / Real.Gamma (3/4))^2 by
      rw [show 4 = 2*2 by rfl, pow_mul, Real.sq_sqrt (by positivity)]]
  have hq := real_Gamma_quarter_mul
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  simp only [Real.rpow_one, Real.rpow_two, Real.rpow_neg (show (0:ℝ) ≤ 2 by norm_num)]
  field_simp
  linear_combination 32*(Real.Gamma (1/4) * Real.Gamma (3/4) + π*Real.sqrt 2) * hq + 32*π^2 * hs

/-- The real coefficient of `J_{1/4}` in `W(0,x)`. -/
lemma pcfW_zero_coeffB {x : ℝ} (hx : 0 < x) :
    -pcfWDerivZero 0 * x * Real.Gamma (5/4) * (x^2/8)^(-1/4:ℝ) = 2^(-5/4:ℝ) * (π*x)^(1/2:ℝ) := by
  have g1 := Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 1/4)
  have g3 := Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 3/4)
  have g5 : Real.Gamma (5/4) = Real.Gamma (1/4) / 4 := by
    rw [show (5/4:ℝ) = 1/4 + 1 by norm_num, Real.Gamma_add_one (by norm_num)]; ring
  rw [pcfWDerivZero_zero, g5]
  simp only [neg_mul, neg_neg]
  apply eq_of_pow_four_eq (by positivity) (by positivity)
  rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow,
    show (-1/4:ℝ) = (-1)/4 by ring, rpow_quarter_pow_four (by norm_num),
    rpow_quarter_pow_four (by positivity) (-1), show (-5/4:ℝ) = (-5)/4 by ring, rpow_quarter_pow_four (by norm_num),
    show (1/2:ℝ) = 2/4 by norm_num, rpow_quarter_pow_four (by positivity),
    show (Real.sqrt (Real.Gamma (3/4) / Real.Gamma (1/4)))^4 = (Real.Gamma (3/4) / Real.Gamma (1/4))^2 by
      rw [show 4 = 2*2 by rfl, pow_mul, Real.sq_sqrt (by positivity)]]
  have hq := real_Gamma_quarter_mul
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  simp only [Real.rpow_one, Real.rpow_two, Real.rpow_neg (show (0:ℝ) ≤ 2 by norm_num),
    Real.rpow_neg (show (0:ℝ) ≤ x^2/8 by positivity)]
  field_simp
  linear_combination 256*(Real.Gamma (1/4) * Real.Gamma (3/4) + π*Real.sqrt 2) * hq + 256*π^2 * hs

/-- Real `cpow` of a nonnegative real is real. -/
lemma ofReal_cpow_real {y : ℝ} (hy : 0 ≤ y) (r : ℝ) : (y:ℂ)^(r:ℂ) = ((y^r : ℝ) : ℂ) :=
  (Complex.ofReal_cpow hy r).symm

/-- `W`'s even solution at `a = 0` through `J_{-1/4}`. -/
lemma pcfWEven_zero_besselJ {t : ℝ} (ht : 0 < t) :
    pcfWEven 0 t = Gamma (3/4) * (((t^2/8)^(1/4:ℝ) : ℝ) : ℂ) * besselJ (-1/4) ((t:ℂ)^2/4) := by
  have hν : ∀ k : ℕ, (-1/4:ℂ) + 1 ≠ -k := fun k h => by
    have := congrArg Complex.re h; simp at this; norm_num at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have h2ν : ∀ k : ℕ, 2*(-1/4:ℂ) + 1 ≠ -k := fun k h => by
    have := congrArg Complex.re h; simp at this; norm_num at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hy : (0:ℝ) < t^2/8 := by positivity
  rw [besselJ_eq_kummerM hν h2ν, (pcfWEven_kummer _ _).1,
    show (t:ℂ)^2/4/2 = ((t^2/8 : ℝ) : ℂ) by push_cast; ring, show (-1/4:ℂ) = ((-1/4:ℝ):ℂ) by push_cast; ring,
    ofReal_cpow_real hy.le]
  have hG : Gamma (3/4:ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  have hm : ((t^2/8)^(1/4:ℝ) : ℝ) * (t^2/8)^(-1/4:ℝ) = 1 := by
    rw [← Real.rpow_add hy]; norm_num
  have hm' : (((t^2/8)^(1/4:ℝ) : ℝ) : ℂ) * (((t^2/8)^(-1/4:ℝ) : ℝ) : ℂ) = 1 := by exact_mod_cast hm
  rw [show ((-1/4:ℝ):ℂ) + 1 = 3/4 by push_cast; ring, show ((-1/4:ℝ):ℂ) + 1/2 = 1/4 by push_cast; ring,
    show 2*((-1/4:ℝ):ℂ) + 1 = 1/2 by push_cast; ring, show 2*I*((t:ℂ)^2/4) = I*(t:ℂ)^2/2 by ring,
    show -I*((t:ℂ)^2/4) = -I*(t:ℂ)^2/4 by ring]
  simp only [mul_zero, zero_div, sub_zero]
  have hg := mul_inv_cancel₀ hG
  linear_combination (-(exp (-I*(t:ℂ)^2/4) * kummerM (1/4) (1/2) (I*(t:ℂ)^2/2))) * hm'
    - ((((t^2/8)^(1/4:ℝ) : ℝ) : ℂ) * (((t^2/8)^(-1/4:ℝ) : ℝ) : ℂ) *
      exp (-I*(t:ℂ)^2/4) * kummerM (1/4) (1/2) (I*(t:ℂ)^2/2)) * hg

/-- `W`'s odd solution at `a = 0` through `J_{1/4}`. -/
lemma pcfWOdd_zero_besselJ {t : ℝ} (ht : 0 < t) :
    pcfWOdd 0 t = t * Gamma (5/4) * (((t^2/8)^(-1/4:ℝ) : ℝ) : ℂ) * besselJ (1/4) ((t:ℂ)^2/4) := by
  have hν : ∀ k : ℕ, (1/4:ℂ) + 1 ≠ -k := fun k h => by
    have := congrArg Complex.re h; simp at this; norm_num at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have h2ν : ∀ k : ℕ, 2*(1/4:ℂ) + 1 ≠ -k := fun k h => by
    have := congrArg Complex.re h; simp at this; norm_num at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hy : (0:ℝ) < t^2/8 := by positivity
  rw [besselJ_eq_kummerM hν h2ν, (pcfWOdd_kummer _ _).1,
    show (t:ℂ)^2/4/2 = ((t^2/8 : ℝ) : ℂ) by push_cast; ring, show (1/4:ℂ) = ((1/4:ℝ):ℂ) by push_cast; ring,
    ofReal_cpow_real hy.le]
  have hG : Gamma (5/4:ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  have hm : ((t^2/8)^(1/4:ℝ) : ℝ) * (t^2/8)^(-1/4:ℝ) = 1 := by
    rw [← Real.rpow_add hy]; norm_num
  have hm' : (((t^2/8)^(1/4:ℝ) : ℝ) : ℂ) * (((t^2/8)^(-1/4:ℝ) : ℝ) : ℂ) = 1 := by exact_mod_cast hm
  rw [show ((1/4:ℝ):ℂ) + 1 = 5/4 by push_cast; ring, show ((1/4:ℝ):ℂ) + 1/2 = 3/4 by push_cast; ring,
    show 2*((1/4:ℝ):ℂ) + 1 = 3/2 by push_cast; ring, show 2*I*((t:ℂ)^2/4) = I*(t:ℂ)^2/2 by ring,
    show -I*((t:ℂ)^2/4) = -I*(t:ℂ)^2/4 by ring]
  simp only [mul_zero, zero_div, sub_zero]
  have hg := mul_inv_cancel₀ hG
  linear_combination (-(t * exp (-I*(t:ℂ)^2/4) * kummerM (3/4) (3/2) (I*(t:ℂ)^2/2))) * hm'
    - (t * (((t^2/8)^(1/4:ℝ) : ℝ) : ℂ) * (((t^2/8)^(-1/4:ℝ) : ℝ) : ℂ) *
      exp (-I*(t:ℂ)^2/4) * kummerM (3/4) (3/2) (I*(t:ℂ)^2/2)) * hg

/-- `pcfWEven` is even. -/
lemma pcfWEven_neg (a z : ℂ) : pcfWEven a (-z) = pcfWEven a z := by
  simp [pcfWEven, pcfEven, mul_neg]

/-- `pcfWOdd` is odd. -/
lemma pcfWOdd_neg (a z : ℂ) : pcfWOdd a (-z) = -pcfWOdd a z := by
  simp [pcfWOdd, pcfOdd, mul_neg]

/-- Complex form of the `J_{-1/4}` coefficient. -/
lemma pcfW_zero_coeffA' {x : ℝ} (hx : 0 < x) :
    (pcfWZero 0 : ℂ) * Gamma (3/4) * (((x^2/8)^(1/4:ℝ) : ℝ) : ℂ) = 2^(-5/4:ℂ)*(π*x:ℂ)^(1/2:ℂ) := by
  have h := congrArg (fun r : ℝ => (r:ℂ)) (pcfW_zero_coeffA hx)
  simp only [Complex.ofReal_mul] at h
  rw [show (3/4:ℂ) = ((3/4:ℝ):ℂ) by push_cast; ring, Complex.Gamma_ofReal, h,
    Complex.ofReal_cpow (by norm_num), Complex.ofReal_cpow (by positivity)]
  push_cast; ring_nf

/-- Complex form of the `J_{1/4}` coefficient. -/
lemma pcfW_zero_coeffB' {x : ℝ} (hx : 0 < x) :
    -(pcfWDerivZero 0 : ℂ) * x * Gamma (5/4) * (((x^2/8)^(-1/4:ℝ) : ℝ) : ℂ) = 2^(-5/4:ℂ)*(π*x:ℂ)^(1/2:ℂ) := by
  have h := congrArg (fun r : ℝ => (r:ℂ)) (pcfW_zero_coeffB hx)
  simp only [Complex.ofReal_mul, Complex.ofReal_neg] at h
  rw [show (5/4:ℂ) = ((5/4:ℝ):ℂ) by push_cast; ring, Complex.Gamma_ofReal, h,
    Complex.ofReal_cpow (by norm_num), Complex.ofReal_cpow (by positivity)]
  push_cast; ring_nf

/-- Derivative of the complex Bessel form of `W(0, ±w)`. -/
lemma pcfW_zero_bessel_hasDerivAt_aux (ε : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun w : ℂ => 2^(-5/4:ℂ)*(π*w)^(1/2:ℂ)*(besselJ (-1/4) (w^2/4)-ε*besselJ (1/4) (w^2/4)))
      (-2^(-9/4:ℂ)*x*(π*x:ℂ)^(1/2:ℂ)*(besselJ (3/4) (x^2/4)+ε*besselJ (-3/4) (x^2/4))) (x:ℂ) := by
  have hz : ((x:ℂ)^2/4) ∈ slitPlane := by
    rw [show (x:ℂ)^2/4 = ((x^2/4:ℝ):ℂ) by push_cast; ring]
    exact ofReal_mem_slitPlane.2 (by positivity)
  have hp : (π*(x:ℂ)) ∈ slitPlane := by
    rw [show (π:ℂ)*(x:ℂ) = ((π*x:ℝ):ℂ) by push_cast; ring]
    exact ofReal_mem_slitPlane.2 (by positivity)
  have hsq : HasDerivAt (fun w : ℂ => w^2/4) ((x:ℂ)/2) x := by
    exact ((hasDerivAt_pow 2 (x:ℂ)).div_const 4).congr_deriv (by simp; ring)
  have h1 := (hasDerivAt_besselJ (ν := -1/4) hz).comp (x:ℂ) hsq
  have h2 := (hasDerivAt_besselJ' (ν := 1/4) hz).comp (x:ℂ) hsq
  have hc := ((hasDerivAt_id (x:ℂ)).const_mul (π:ℂ)).cpow_const (c := 1/2) (by simpa using hp)
  have := (hc.const_mul (2^(-5/4:ℂ))).mul (h1.sub (h2.const_mul ε))
  convert this using 1
  · ext w; simp
  simp only [id, Function.comp, Pi.sub_apply]
  have hx0 : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hπ : (π:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hpx : (π:ℂ)*x ≠ 0 := mul_ne_zero hπ hx0
  rw [Complex.cpow_sub _ _ hpx, Complex.cpow_one, show (-9/4:ℂ) = -5/4 - 1 by norm_num,
    Complex.cpow_sub _ _ two_ne_zero, Complex.cpow_one,
    show (-1/4:ℂ) + 1 = 3/4 by norm_num, show (1/4:ℂ) - 1 = -3/4 by norm_num]
  field_simp
  ring

/-- pcfW zero bessel 1. -/
@[dlmf 12.14.E13]
theorem pcfW_zero_bessel_1 {x : ℝ} (hx : 0 < x) :
    pcfW 0 (1*x)=2^(-5/4:ℂ)*(π*x:ℂ)^(1/2:ℂ)*(besselJ (-1/4) (x^2/4)-(1:ℂ)*besselJ (1/4) (x^2/4)) := by
  rw [one_mul, pcfW, Complex.ofReal_zero, pcfWEven_zero_besselJ hx, pcfWOdd_zero_besselJ hx]
  linear_combination besselJ (-1/4) ((x:ℂ)^2/4) * pcfW_zero_coeffA' hx
    - besselJ (1/4) ((x:ℂ)^2/4) * pcfW_zero_coeffB' hx

/-- pcfW zero bessel deriv 1. -/
@[dlmf 12.14.E14]
theorem pcfW_zero_bessel_deriv_1 {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => pcfW 0 (1*t)) (-2^(-9/4:ℂ)*x*(π*x:ℂ)^(1/2:ℂ)*(besselJ (3/4) (x^2/4)+(1:ℂ)*besselJ (-3/4) (x^2/4))) x := by
  refine (pcfW_zero_bessel_hasDerivAt_aux 1 hx).comp_ofReal.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hx] with t ht
  exact pcfW_zero_bessel_1 ht

/-- pcfW zero bessel 2. -/
@[dlmf 12.14.E13]
theorem pcfW_zero_bessel_2 {x : ℝ} (hx : 0 < x) :
    pcfW 0 (-1*x)=2^(-5/4:ℂ)*(π*x:ℂ)^(1/2:ℂ)*(besselJ (-1/4) (x^2/4)-(-1:ℂ)*besselJ (1/4) (x^2/4)) := by
  rw [neg_one_mul, pcfW, Complex.ofReal_zero, pcfWEven_neg, pcfWOdd_neg, pcfWEven_zero_besselJ hx,
    pcfWOdd_zero_besselJ hx]
  linear_combination besselJ (-1/4) ((x:ℂ)^2/4) * pcfW_zero_coeffA' hx
    + besselJ (1/4) ((x:ℂ)^2/4) * pcfW_zero_coeffB' hx

/-- pcfW zero bessel deriv 2. -/
@[dlmf 12.14.E14]
theorem pcfW_zero_bessel_deriv_2 {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => pcfW 0 (-1*t)) (-2^(-9/4:ℂ)*x*(π*x:ℂ)^(1/2:ℂ)*(besselJ (3/4) (x^2/4)+(-1:ℂ)*besselJ (-3/4) (x^2/4))) x := by
  refine (pcfW_zero_bessel_hasDerivAt_aux (-1) hx).comp_ofReal.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hx] with t ht
  exact pcfW_zero_bessel_2 ht

/-- pcfWOmega. -/
@[dlmf 12.14.E19]
def pcfWOmega (a x : ℝ) : ℝ :=
  x^2/4-a*Real.log x+π/4+pcfGammaPhase a/2

/-- `W(a,x)` is real. -/
lemma pcfW_ofReal_im (a x : ℝ) : (pcfW a x).im = 0 := by
  rw [← Complex.conj_eq_iff_im]; simpa using conj_pcfW_conj a x

/-- `W(a,z)` and `W(a,-z)` do not vanish together. -/
lemma pcfW_one_ne (a : ℝ) (z : ℂ) (h1 : pcfW a z = 0) (h2 : pcfW a (-z) = 0) : False := by
  have hw := pcfW_wronskian_aux a z
  have := pcfWZero_mul_pcfWDerivZero a
  have : (pcfWZero a : ℂ) * pcfWDerivZero a = -1/2 := by exact_mod_cast this
  rw [h1, h2] at hw
  have : (0:ℂ) = 1 := by linear_combination hw - 2 * this
  exact zero_ne_one this

/-- `W'(a,z)` and `W'(a,-z)` do not vanish together. -/
lemma pcfWDeriv_one_ne (a : ℝ) (z : ℂ) (h1 : pcfWDeriv a z = 0) (h2 : pcfWDeriv a (-z) = 0) : False := by
  have hw := pcfW_wronskian_aux a z
  have := pcfWZero_mul_pcfWDerivZero a
  have : (pcfWZero a : ℂ) * pcfWDerivZero a = -1/2 := by exact_mod_cast this
  rw [h1, h2] at hw
  have : (0:ℂ) = 1 := by linear_combination hw - 2 * this
  exact zero_ne_one this

/-- Combined exact amplitude s1+i s2, recovered from the two real W solutions. -/
@[dlmf 12.14.E17, dlmf 12.14.E18]
def pcfWS (a x : ℝ) : ℂ :=
  exp (-I*pcfWOmega a x)*(Real.sqrt (x/(2*pcfWK a))*pcfW a x+I*Real.sqrt (pcfWK a*x/2)*pcfW a (-x))

/-- pcfW amplitude. -/
@[dlmf 12.14.E17, dlmf 12.14.E18]
theorem pcfW_amplitude (a : ℝ) {x : ℝ} (hx : 0 < x) :
    pcfW a x=Real.sqrt (2*pcfWK a/x)*((pcfWS a x).re*Real.cos (pcfWOmega a x)-(pcfWS a x).im*Real.sin (pcfWOmega a x)) ∧ pcfW a (-x)=Real.sqrt (2/(pcfWK a*x))*((pcfWS a x).re*Real.sin (pcfWOmega a x)+(pcfWS a x).im*Real.cos (pcfWOmega a x)) := by
  have h1r := pcfW_ofReal_im a x
  have h2r := pcfW_ofReal_im a (-x)
  push_cast at h2r
  have hk := (pcfWK_recip a).1
  set ω := pcfWOmega a x
  set k := pcfWK a
  set p := Real.sqrt (x/(2*k))
  set q := Real.sqrt (k*x/2)
  have hT : exp (I*ω) * pcfWS a x = p * pcfW a x + I * (q * pcfW a (-x)) := by
    rw [pcfWS, ← mul_assoc, ← Complex.exp_add, show I*ω + -I*ω = 0 by ring, Complex.exp_zero, one_mul]
    ring
  have hre := congrArg Complex.re hT
  have him := congrArg Complex.im hT
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    h1r, h2r, mul_comm I] at hre him
  have hp : Real.sqrt (2*k/x) * p = 1 := by
    rw [← Real.sqrt_mul (by positivity)]; field_simp; simp
  have hq : Real.sqrt (2/(k*x)) * q = 1 := by
    rw [← Real.sqrt_mul (by positivity)]; field_simp; simp
  have e1 : pcfW a x = ((pcfW a x).re : ℂ) := (Complex.ext (by simp) (by simp [h1r]))
  have e2 : pcfW a (-x) = ((pcfW a (-x)).re : ℂ) := (Complex.ext (by simp) (by simp [h2r]))
  constructor
  · rw [e1]
    have : (pcfW a x).re = Real.sqrt (2*k/x) * ((pcfWS a x).re * Real.cos ω - (pcfWS a x).im * Real.sin ω) := by
      linear_combination (-Real.sqrt (2*k/x)) * hre - (pcfW a x).re * hp
    rw [this]; push_cast; ring
  · rw [e2]
    have : (pcfW a (-x)).re = Real.sqrt (2/(k*x)) * ((pcfWS a x).re * Real.sin ω + (pcfWS a x).im * Real.cos ω) := by
      linear_combination (-Real.sqrt (2/(k*x))) * him - (pcfW a (-x)).re * hq
    rw [this]; push_cast; ring

/-- pcfWCoeff. -/
@[dlmf 12.14.E22]
def pcfWCoeff (a : ℝ) (r : ℕ) : ℂ :=
  poch (1/2+I*a) (2*r)

/- DLMF 12.14.22 is Mathlib's `Complex.Gamma_add_nat_div_Gamma_eq`,
with z=1/2+i*a and n=2*r. The real part of z is positive, so its regularity
hypothesis holds. `pcfWCoeff` uses the equivalent Pochhammer definition.
This upstream gamma-ratio identity is not reproved here. -/

/-- `s₁ + i s₂` of DLMF 12.14.17–18 is the normalized `e^{ζ²/4} ζ^{ia+1/2} U(ia, ζ)` at
`ζ = x e^{-iπ/4}` (from the connection formula DLMF 12.14.4). -/
lemma pcfSect_pcfWS_eq (a : ℝ) {x : ℝ} (hx : 0 < x) :
    pcfWS a x = pcfSect_G (I * a) (exp ((Real.log x : ℂ) + ((-(π/4) : ℝ) : ℂ) * I)) := by
  set v : ℂ := (Real.log x : ℂ) + ((-(π/4) : ℝ) : ℂ) * I
  have hv1 : -π < v.im := by simp [v]; linarith [Real.pi_pos]
  have hv2 : v.im ≤ π := by simp [v]; linarith [Real.pi_pos]
  have hζ : (x : ℂ) * exp (-π * I / 4) = exp v := by
    simp only [v]
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hx]
    congr 1; push_cast; ring_nf
  have hk := (pcfWK_recip a).1
  have hs1 : (Real.sqrt (x / (2 * pcfWK a)) : ℂ) * (Real.sqrt (pcfWK a / 2) : ℂ) =
      (Real.sqrt x : ℂ) / 2 := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by positivity),
      show x / (2 * pcfWK a) * (pcfWK a / 2) = x / 4 by field_simp; ring,
      Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4),
      show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    push_cast; ring
  have hs2 : (Real.sqrt (pcfWK a * x / 2) : ℂ) / (Real.sqrt (2 * pcfWK a) : ℂ) =
      (Real.sqrt x : ℂ) / 2 := by
    rw [← Complex.ofReal_div, ← Real.sqrt_div' _ (by positivity),
      show pcfWK a * x / 2 / (2 * pcfWK a) = x / 4 by field_simp; ring,
      Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4),
      show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    push_cast; ring
  have hsq : (Real.sqrt x : ℂ) = exp ((Real.log x : ℂ) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx, Complex.ofReal_exp]; push_cast; ring_nf
  have hW1 := pcfW_connection a x
  have hW2 := pcfW_connection_neg a x
  rw [hζ, pcfSect_pcfU_exp (I * a) hv1 hv2] at hW1 hW2
  set P := exp (-exp (2 * v) / 4 - (I * a + 1 / 2) * v)
  set G := pcfSect_G (I * a) (exp v)
  set U2 := pcfU (-I * a) (x * exp (π * I / 4))
  set eA := exp (π * (a:ℂ) / 4)
  set eρ := exp (I * (pcfWRho a : ℂ))
  set eρ' := exp (-I * (pcfWRho a : ℂ))
  have hW2' : I * (Real.sqrt (pcfWK a * x / 2) : ℂ) * pcfW a (-x) =
      ((Real.sqrt (pcfWK a * x / 2) : ℂ) / (Real.sqrt (2 * pcfWK a) : ℂ)) * eA *
        (eρ * (P * G) - eρ' * U2) := by
    rw [hW2]
    linear_combination (-((Real.sqrt (pcfWK a * x / 2) : ℂ) / (Real.sqrt (2 * pcfWK a) : ℂ)) *
      eA * (eρ * (P * G) - eρ' * U2)) * I_sq
  have h2v : exp (2 * v) = -I * (x : ℂ) ^ 2 := by
    rw [show (2:ℂ) * v = ((2:ℕ):ℂ) * v by norm_num, Complex.exp_nat_mul, ← hζ, mul_pow,
      exp_neg_pi_I_quarter_sq]; ring
  have key : exp (-I * (pcfWOmega a x : ℂ)) * (Real.sqrt x : ℂ) * eA * eρ * P = 1 := by
    simp only [P, eA, eρ]
    rw [hsq, h2v, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    refine (congrArg exp ?_).trans Complex.exp_zero
    simp only [v, pcfWOmega, pcfWRho]
    push_cast
    linear_combination (π * a / 4) * I_sq
  unfold pcfWS
  rw [hW2', hW1]
  linear_combination (exp (-I * (pcfWOmega a x : ℂ)) * eA * (eρ * (P * G) + eρ' * U2)) * hs1 +
    (exp (-I * (pcfWOmega a x : ℂ)) * eA * (eρ * (P * G) - eρ' * U2)) * hs2 + G * key

/-- pcfWS asymptotic. -/
@[dlmf 12.14.E20, dlmf 12.14.E21, dlmf 12.14.E23]
theorem pcfWS_asymptotic (a : ℝ) (N : ℕ) :
    (fun x : ℝ => pcfWS a x-∑ r ∈ Finset.range N, (-I)^r*pcfWCoeff a r/(2^r*(r.factorial:ℂ)*(x:ℂ)^(2*r))) =O[atTop] (fun x : ℝ => (x:ℂ)^(-(2*N:ℤ))) := by
  have hT : Tendsto (fun x : ℝ => (Real.log x : ℂ)) atTop (pcfSect_logWedge 0 0) := by
    refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr
      (Eventually.of_forall fun x => by simp)⟩
    refine tendsto_id.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp [Real.exp_log hx]
  have hS := (pcfSect_tendsto_exp_logWedge (δ := π/4) (by positivity) (-(π/4)) (lo := 0) (hi := 0)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])).comp hT
  have h := (pcfSect_U_sector (I * a) (δ := π/4) (by positivity) N).comp_tendsto hS
  refine IsBigO.trans (h.congr' ?_ EventuallyEq.rfl) ?_
  · filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [Function.comp_apply]
    rw [pcfSect_pcfWS_eq a hx]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    have hsq : (exp ((Real.log x : ℂ) + ((-(π/4) : ℝ) : ℂ) * I)) ^ 2 = -I * (x : ℂ) ^ 2 := by
      rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hx, mul_pow,
        show ((-(π/4) : ℝ) : ℂ) * I = -π * I / 4 by push_cast; ring, exp_neg_pi_I_quarter_sq]
      ring
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    have hII : (-I) ^ r * (-I) ^ r = (-1) ^ r := by rw [← mul_pow]; simp
    have hf : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
    rw [pcfSect_uTerm, hsq, pcfWCoeff, mul_pow, mul_pow, ← pow_mul, ← hII]
    have hI : (-I) ^ r ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr I_ne_zero)
    field_simp
  · refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [Function.comp_apply, norm_zpow, Complex.norm_exp, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hx]
    simp [Real.exp_log hx]

/-- pcfWF. -/
@[dlmf 12.14.E37]
def pcfWF (a x : ℝ) : ℝ :=
  ‖1/Real.sqrt (pcfWK a)*(pcfW a) x+I*Real.sqrt (pcfWK a)*(pcfW a) (-x)‖

/-- pcfWTheta. -/
@[dlmf 12.14.E37]
def pcfWTheta (a x : ℝ) : ℝ :=
  arg ((1/Real.sqrt (pcfWK a)*(pcfW a) x+I*Real.sqrt (pcfWK a)*(pcfW a) (-x)))

/-- pcfWF phase. -/
@[dlmf 12.14.E37]
theorem pcfWF_phase (a x : ℝ) :
    0 < pcfWF a x ∧ 1/Real.sqrt (pcfWK a)*(pcfW a) x+I*Real.sqrt (pcfWK a)*(pcfW a) (-x)=(pcfWF a x*exp (I*pcfWTheta a x)) := by
  have hk := (pcfWK_recip a).1
  have hs : (Real.sqrt (pcfWK a) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hk).ne'
  have hne : 1/Real.sqrt (pcfWK a)*(pcfW a) x+I*Real.sqrt (pcfWK a)*(pcfW a) (-x) ≠ 0 := by
    rw [mul_assoc I]
    refine add_I_mul_ne_zero_of_real ?_ ?_ ?_
    · rw [map_mul, Complex.conj_eq_iff_im.mpr (pcfW_ofReal_im a x)]; simp
    · have := pcfW_ofReal_im a (-x); push_cast at this
      rw [map_mul, Complex.conj_eq_iff_im.mpr this, Complex.conj_ofReal]
    · rintro ⟨h1, h2⟩
      exact pcfW_one_ne a x (by simpa [hs] using h1) (by simpa [hs] using h2)
  refine ⟨norm_pos_iff.mpr hne, ?_⟩
  have h := norm_mul_exp_arg_mul_I (1/Real.sqrt (pcfWK a)*(pcfW a) x+I*Real.sqrt (pcfWK a)*(pcfW a) (-x))
  rw [mul_comm ((arg _ : ℝ) : ℂ) I] at h
  exact h.symm

/-- pcfWG. -/
@[dlmf 12.14.E38]
def pcfWG (a x : ℝ) : ℝ :=
  ‖1/Real.sqrt (pcfWK a)*(deriv (pcfW a)) x+I*Real.sqrt (pcfWK a)*(deriv (pcfW a)) (-x)‖

/-- pcfWPsi. -/
@[dlmf 12.14.E38]
def pcfWPsi (a x : ℝ) : ℝ :=
  arg (-(1/Real.sqrt (pcfWK a)*(deriv (pcfW a)) x+I*Real.sqrt (pcfWK a)*(deriv (pcfW a)) (-x)))

/-- pcfWG phase. -/
@[dlmf 12.14.E38]
theorem pcfWG_phase (a x : ℝ) :
    0 < pcfWG a x ∧ 1/Real.sqrt (pcfWK a)*(deriv (pcfW a)) x+I*Real.sqrt (pcfWK a)*(deriv (pcfW a)) (-x)=-(pcfWG a x*exp (I*pcfWPsi a x)) := by
  have hk := (pcfWK_recip a).1
  have hs : (Real.sqrt (pcfWK a) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hk).ne'
  have hne : 1/Real.sqrt (pcfWK a)*(deriv (pcfW a)) x+I*Real.sqrt (pcfWK a)*(deriv (pcfW a)) (-x) ≠ 0 := by
    rw [mul_assoc I, deriv_pcfW]
    refine add_I_mul_ne_zero_of_real ?_ ?_ ?_
    · rw [map_mul, conj_pcfWDeriv_ofReal]; simp
    · have := conj_pcfWDeriv_ofReal a (-x); push_cast at this
      rw [map_mul, this, Complex.conj_ofReal]
    · rintro ⟨h1, h2⟩
      exact pcfWDeriv_one_ne a x (by simpa [hs] using h1) (by simpa [hs] using h2)
  refine ⟨norm_pos_iff.mpr hne, ?_⟩
  have h := norm_mul_exp_arg_mul_I (-(1/Real.sqrt (pcfWK a)*(deriv (pcfW a)) x+I*Real.sqrt (pcfWK a)*(deriv (pcfW a)) (-x)))
  rw [mul_comm ((arg _ : ℝ) : ℂ) I, norm_neg] at h
  rw [pcfWG, pcfWPsi, h, neg_neg]

end DLMF.Confluent
