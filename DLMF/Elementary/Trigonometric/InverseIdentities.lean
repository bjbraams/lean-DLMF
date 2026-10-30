/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elementary.Trigonometric.InverseBranches
public import DLMFMathlib.Analysis.Complex.Sqrt
public import DLMF.Elementary.LogExpAnalysis
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import DLMF.Hypergeometric.SeriesProperties
public import Pochhammer.BinomialSeries
public import ToMathlib.Algebra.Polynomial.PochhammerIdentities
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# General inverse trigonometric identities

General inverse values, sum and difference formulas and continued fractions with their branch
conditions.

Source references and common attribution are retained in
`DLMF.Elementary.Trigonometric`.
The boundary and exterior arctangent series reuse the natural-order odd logarithm
series from `DLMF.Elementary.LogExpAnalysis`, retaining the principal branch correction.
Euler’s transformed series integrates a dominated geometric kernel; its factorial moments
come from Mathlib’s Beta integral, and the principal arctangent derivative evaluates the kernel.
The closed-disk arcsine series uses the lean-codes binomial series and Pochhammer
duplication, with Gauss summability from `DLMF.Hypergeometric.Basic` at the boundary.
The binomial series in `Pochhammer.BinomialSeries` imports the Tau Ceti contributors’
complex binomial theorem; see `CREDITS.md`.
The arccosine expansion follows from the principal half-angle identity. Its positive
real cut values use the lower-bank limit already proved in `InverseBranches`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Polynomial

open scoped Real Topology Nat

namespace DLMF.Elementary

/-- DLMF 4.23.E32: arccos general values. -/
@[dlmf 4.23.E32]
theorem arccos_general_values (z w : ℂ) :
    w∈arccosGeneral z ↔ ∃ k : ℤ,w=arccosPrincipal z+2*k*π ∨ w= -arccosPrincipal z+2*k*π := by
  change Complex.cos w=z ↔ _
  have he:Complex.cos w=z ↔ Complex.cos (arccosPrincipal z)=Complex.cos w := by
    rw [cos_arccos_principal]
    exact eq_comm
  rw [he,Complex.cos_eq_cos_iff]
  simp only [sub_eq_add_neg,add_comm]

/-- DLMF 4.23.E33: arctan general values. -/
@[dlmf 4.23.E33]
theorem arctan_general_values {z : ℂ} (hp : z≠I) (hm : z≠ -I) (w : ℂ) :
    w∈arctanGeneral z ↔ ∃ k : ℤ,w=Complex.arctan z+k*π := by
  have hb:=Complex.tan_arctan hp hm
  have hA:Complex.cos (Complex.arctan z)≠0 := by
    intro h
    have hz:z=0 := by simpa [Complex.tan,h] using hb.symm
    subst z
    simpa [Complex.arctan] using h
  constructor
  · rintro ⟨hc,ht⟩
    have he:Complex.tan w=Complex.tan (Complex.arctan z) := ht.trans hb.symm
    have hs:Complex.sin (w-Complex.arctan z)=0 := by
      rw [Complex.tan,Complex.tan,div_eq_div_iff hc hA] at he
      rw [Complex.sin_sub]
      linear_combination he
    obtain ⟨k,hk⟩:=Complex.sin_eq_zero_iff.mp hs
    exact ⟨k,by linear_combination hk⟩
  · rintro ⟨k,rfl⟩
    refine ⟨?_,?_⟩
    · have hcos:Complex.cos (Complex.arctan z+k*π)=(-1:ℂ)^k*Complex.cos (Complex.arctan z) :=
        k.cast_negOnePow ℂ ▸ Complex.cos_antiperiodic.add_int_mul_eq k
      rw [hcos]
      exact mul_ne_zero (zpow_ne_zero _ (by norm_num)) hA
    · rw [Complex.tan_add_int_mul_pi,hb]

/-- The half-sum of distances to the inverse sine branch points. -/
@[dlmf 4.23.E37]
def inverseTrigAlpha (z : ℂ) : ℝ := (‖z+1‖+‖z-1‖)/2

/-- The half-difference of distances to the inverse sine branch points. -/
@[dlmf 4.23.E38]
def inverseTrigBeta (z : ℂ) : ℝ := (‖z+1‖-‖z-1‖)/2

/-- The principal square root is the square root with positive real part. -/
lemma trigR4_sqrt_eq_of_sq {a w : ℂ} (hw : w^2 = a) (hre : 0 < w.re) :
    Complex.sqrt a = w := by
  have h1 := trig_sqrt_sq a
  have h : (Complex.sqrt a - w)*(Complex.sqrt a + w) = 0 := by linear_combination h1 - hw
  rcases mul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have hr : 0 ≤ (Complex.sqrt a).re := by
      rw [Complex.sqrt, Complex.cpow_inv_two_re]; positivity
    have : (Complex.sqrt a).re = -w.re := by
      have := congrArg Complex.re h; simp at this; linarith
    linarith

/-- Algebraic identities for the half-sum and half-difference of distances to `±1`. -/
lemma trigR4_alpha_beta (z : ℂ) :
    inverseTrigAlpha z*inverseTrigBeta z=z.re ∧
    (1-(inverseTrigBeta z)^2)*((inverseTrigAlpha z)^2-1)=z.im^2 ∧
    1 ≤ inverseTrigAlpha z ∧ |inverseTrigBeta z| ≤ 1 := by
  have hp : ‖z+1‖^2 = (z.re+1)^2+z.im^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
  have hm : ‖z-1‖^2 = (z.re-1)^2+z.im^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
  have h2 : ‖(z+1)-(z-1)‖ = 2 := by norm_num
  have t1 := norm_sub_le (z+1) (z-1)
  have t2 := abs_norm_sub_norm_le (z+1) (z-1)
  rw [h2] at t1 t2
  have n1 := norm_nonneg (z+1)
  have n2 := norm_nonneg (z-1)
  simp only [inverseTrigAlpha, inverseTrigBeta]
  refine ⟨?_, ?_, by linarith, ?_⟩
  · nlinarith
  · nlinarith
  · rw [abs_le] at t2 ⊢; constructor <;> linarith [t2.1, t2.2]

/-- DLMF 4.23.E34: arcsin real imag. -/
@[dlmf 4.23.E34]
theorem arcsin_real_imag {z : ℂ} (hz : z.im≠0 ∨ |z.re|≤1) :
    arcsinPrincipal z=(Real.arcsin (inverseTrigBeta z):ℂ)+
      I*(trigRealSign z.im:ℂ)*Real.log (inverseTrigAlpha z+Real.sqrt ((inverseTrigAlpha z)^2-1)) := by
  obtain ⟨hab, hsq, ha1, hb1⟩ := trigR4_alpha_beta z
  set a := inverseTrigAlpha z
  set b := inverseTrigBeta z
  by_cases hy : z.im = 0
  · have hx : |z.re| ≤ 1 := hz.resolve_left (not_not.mpr hy)
    have hz' : z = (z.re:ℂ) := by apply Complex.ext <;> simp [hy]
    have hb : b = z.re := by
      simp only [b, inverseTrigBeta]
      rw [hz']
      have e1 : ((z.re:ℂ)+1) = ((z.re+1:ℝ):ℂ) := by push_cast; ring
      have e2 : ((z.re:ℂ)-1) = ((z.re-1:ℝ):ℂ) := by push_cast; ring
      rw [e1, e2, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      rw [abs_le] at hx
      rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
      simp; ring
    rw [abs_le] at hx
    have hs : trigRealSign z.im = 0 := by simp [trigRealSign, hy]
    rw [hb, hs, hz']
    simp only [Complex.ofReal_re]
    rw [(inverse_principal_real ⟨hx.1, hx.2⟩).1]
    simp
  · have hσ : trigRealSign z.im = 1 ∨ trigRealSign z.im = -1 := by
      rcases lt_or_gt_of_ne hy with h | h
      · right; simp [trigRealSign, h, not_lt.mpr h.le]
      · left; simp [trigRealSign, h]
    set σ := trigRealSign z.im
    have hσy : σ * |z.im| = z.im := by
      rcases lt_or_gt_of_ne hy with h | h
      · have : σ = -1 := by simp [σ, trigRealSign, h, not_lt.mpr h.le]
        rw [this, abs_of_neg h]; ring
      · have : σ = 1 := by simp [σ, trigRealSign, h]
        rw [this, abs_of_pos h]; ring
    have hσ2 : σ^2 = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
    have hpos : 0 < z.im^2 := by positivity
    have hb21 : b^2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg b]
    have hb2 : b^2 < 1 := by
      by_contra h
      have h' : b^2 = 1 := by linarith
      rw [h'] at hsq; linarith
    have ha2 : 1 < a^2 := by
      by_contra h; push Not at h; nlinarith
    set r := Real.sqrt (a^2-1)
    have hr : r^2 = a^2-1 := Real.sq_sqrt (by linarith)
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have har : 0 < a + r := by linarith
    set L := Real.log (a+r)
    have heL : Real.exp L = a + r := Real.exp_log har
    have heL' : Real.exp (-L) = a - r := by
      rw [Real.exp_neg, heL]; field_simp; nlinarith
    set t := σ * L
    have hcosh : Real.cosh t = a := by
      rcases hσ with h | h <;> simp only [t, h, one_mul, neg_one_mul, Real.cosh_neg] <;>
        rw [Real.cosh_eq, heL, heL'] <;> ring
    have hsinh : Real.sinh t = σ * r := by
      rcases hσ with h | h <;> simp only [t, h, one_mul, neg_one_mul, Real.sinh_neg] <;>
        rw [Real.sinh_eq, heL, heL'] <;> ring
    set s := Real.arcsin b
    have hb1' := abs_le.mp hb1
    have hsin : Real.sin s = b := Real.sin_arcsin hb1'.1 hb1'.2
    have hcos : Real.cos s = Real.sqrt (1-b^2) := Real.cos_arcsin b
    have hcpos : 0 < Real.cos s := by rw [hcos]; exact Real.sqrt_pos.mpr (by linarith)
    have hprod : Real.cos s * r = |z.im| := by
      rw [hcos, ← Real.sqrt_mul (by linarith), hsq, Real.sqrt_sq_eq_abs]
    set w : ℂ := (s:ℂ) + (t:ℂ)*I
    have hsinw : Complex.sin w = z := by
      simp only [w, Complex.sin_add, Complex.sin_mul_I, Complex.cos_mul_I]
      rw [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sinh,
        ← Complex.ofReal_cosh, hsin, hcosh, hsinh]
      apply Complex.ext <;> simp
      · linarith
      · rw [Complex.cos_ofReal_re]; linear_combination hσy + σ*hprod
    have hcosre : 0 < (Complex.cos w).re := by
      simp only [w, Complex.cos_add, Complex.sin_mul_I, Complex.cos_mul_I]
      rw [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sinh,
        ← Complex.ofReal_cosh, hcosh]
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      nlinarith
    have hsq' : Complex.sqrt (1-z^2) = Complex.cos w := by
      apply trigR4_sqrt_eq_of_sq _ hcosre
      rw [← hsinw]; linear_combination Complex.sin_sq_add_cos_sq w
    have he : Complex.sqrt (1-z^2)+I*z = Complex.exp (w*I) := by
      rw [hsq', Complex.exp_mul_I, hsinw]; ring
    have hwI : (w*I).im = s := by simp [w]
    rw [arcsinPrincipal, he, Complex.log_exp]
    · simp only [w, t]; push_cast
      linear_combination (-(s:ℂ) - (σ:ℂ)*(L:ℂ)*I)*Complex.I_sq
    · rw [hwI]; linarith [Real.neg_pi_div_two_le_arcsin b, Real.pi_pos]
    · rw [hwI]; linarith [Real.arcsin_le_pi_div_two b, Real.pi_pos]

/-- DLMF 4.23.E35: arccos real imag. -/
@[dlmf 4.23.E35]
theorem arccos_real_imag {z : ℂ} (hz : z.im≠0 ∨ |z.re|≤1) :
    arccosPrincipal z=(Real.arccos (inverseTrigBeta z):ℂ)-
      I*(trigRealSign z.im:ℂ)*Real.log (inverseTrigAlpha z+Real.sqrt ((inverseTrigAlpha z)^2-1)) := by
  rw [arccosPrincipal, arcsin_real_imag hz, Real.arccos_eq_pi_div_two_sub_arcsin]
  push_cast; ring

/-- On the arcsine cut plane the half-difference of distances lies strictly inside `(-1,1)`. -/
lemma trigR4_beta_lt {z : ℂ} (hz : z∈arcsinCutPlane) : |inverseTrigBeta z|<1 := by
  obtain ⟨hab, hsq, ha1, hb1⟩ := trigR4_alpha_beta z
  rcases lt_or_eq_of_le hb1 with h | h
  · exact h
  exfalso
  have hb2 : (inverseTrigBeta z)^2 = 1 := by rw [← sq_abs, h]; norm_num
  rw [hb2, sub_self, zero_mul] at hsq
  have hy : z.im = 0 := by nlinarith
  rcases hz with hz | hz
  · exact hz hy
  · have : |z.re| = inverseTrigAlpha z := by
      rw [← hab, abs_mul, h, mul_one, abs_of_pos (by linarith)]
    linarith

/-- Real and imaginary parts of the complex cosine and sine. -/
lemma trigR4_cos_sin_re (w : ℂ) :
    (Complex.cos w).re = Real.cos w.re*Real.cosh w.im ∧
    (Complex.sin w).re = Real.sin w.re*Real.cosh w.im := by
  have hw : w = (w.re:ℂ) + (w.im:ℂ)*I := (Complex.re_add_im w).symm
  constructor
  · conv_lhs => rw [hw]
    rw [Complex.cos_add, Complex.cos_mul_I, Complex.sin_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
    simp [-Complex.ofReal_cos, -Complex.ofReal_sin, -Complex.ofReal_cosh, -Complex.ofReal_sinh,
      Complex.ofReal_re, Complex.ofReal_im]
  · conv_lhs => rw [hw]
    rw [Complex.sin_add, Complex.cos_mul_I, Complex.sin_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
    simp [-Complex.ofReal_cos, -Complex.ofReal_sin, -Complex.ofReal_cosh, -Complex.ofReal_sinh,
      Complex.ofReal_re, Complex.ofReal_im]

/-- DLMF 4.23.E23: arccos principal log half. -/
@[dlmf 4.23.E23]
theorem arccos_principal_log_half {z : ℂ} (hz : z∈arcsinCutPlane) :
    arccosPrincipal z= -2*I*Complex.log (Complex.sqrt ((1+z)/2)+I*Complex.sqrt ((1-z)/2)) := by
  have hz' : z.im≠0 ∨ |z.re|≤1 := by
    rcases hz with h | h
    · exact Or.inl h
    · exact Or.inr h.le
  set θ := arccosPrincipal z
  have hre : θ.re = Real.arccos (inverseTrigBeta z) := by
    rw [show θ = _ from arccos_real_imag hz']
    simp
  have hb := abs_lt.mp (trigR4_beta_lt hz)
  have h0 : 0 < θ.re := by rw [hre]; exact Real.arccos_pos.mpr hb.2
  have hπ : θ.re < π := by rw [hre]; exact Real.arccos_lt_pi.mpr hb.1
  have hc : Complex.cos θ = z := cos_arccos_principal z
  have hu0 : 0 < Real.cos (θ/2).re := by
    apply Real.cos_pos_of_mem_Ioo; simp; constructor <;> linarith
  have hv0 : 0 < Real.sin (θ/2).re := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> simp <;> linarith
  have h1 : Complex.sqrt ((1+z)/2) = Complex.cos (θ/2) := by
    apply trigR4_sqrt_eq_of_sq
    · rw [Complex.cos_sq, ← hc]; ring_nf
    · rw [(trigR4_cos_sin_re _).1]; exact mul_pos hu0 (Real.cosh_pos _)
  have h2 : Complex.sqrt ((1-z)/2) = Complex.sin (θ/2) := by
    apply trigR4_sqrt_eq_of_sq
    · rw [Complex.sin_sq, Complex.cos_sq, ← hc]; ring_nf
    · rw [(trigR4_cos_sin_re _).2]; exact mul_pos hv0 (Real.cosh_pos _)
  rw [h1, h2, show Complex.cos (θ/2) + I*Complex.sin (θ/2) = Complex.exp (θ/2*I) by
    rw [Complex.exp_mul_I]; ring, Complex.log_exp]
  · linear_combination θ*Complex.I_sq
  · simp; linarith
  · simp; linarith

/-- In the open right half-plane the argument is the arctangent of the slope. -/
lemma trigR4_arg_of_re_pos {w : ℂ} (hw : 0<w.re) : Complex.arg w=Real.arctan (w.im/w.re) := by
  have h := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)
  rw [← Complex.tan_arg, Real.arctan_tan (abs_lt.mp h).1 (abs_lt.mp h).2]

/-- DLMF 4.23.E36: arctan real imag. -/
@[dlmf 4.23.E36]
theorem arctan_real_imag {z : ℂ} (hz : ‖z‖<1) :
    Complex.arctan z=(Real.arctan (2*z.re/(1-z.re^2-z.im^2)):ℂ)/2+
      I/4*Real.log ((z.re^2+(z.im+1)^2)/(z.re^2+(z.im-1)^2)) := by
  obtain ⟨x, y⟩ := z
  simp only at hz ⊢
  have hz2 : x^2+y^2<1 := by
    have := Complex.sq_norm ⟨x, y⟩
    rw [Complex.normSq_apply] at this
    simp only at this
    nlinarith [norm_nonneg (⟨x, y⟩ : ℂ)]
  have hD : 0 < x^2+(y+1)^2 := by nlinarith
  have hN : 0 < x^2+(y-1)^2 := by nlinarith
  have hzI : 1 - (⟨x, y⟩ : ℂ)*I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; nlinarith
  have hw : (1+(⟨x, y⟩ : ℂ)*I)/(1-(⟨x, y⟩ : ℂ)*I) = ⟨(1-x^2-y^2)/(x^2+(y+1)^2), 2*x/(x^2+(y+1)^2)⟩ := by
    rw [div_eq_iff hzI]
    have hD' : x^2+(y+1)^2 ≠ 0 := hD.ne'
    apply Complex.ext <;> simp <;> field_simp <;> ring
  have hre : 0 < ((1+(⟨x, y⟩ : ℂ)*I)/(1-(⟨x, y⟩ : ℂ)*I)).re := by rw [hw]; exact div_pos (by linarith) hD
  have hnorm : ‖(1+(⟨x, y⟩ : ℂ)*I)/(1-(⟨x, y⟩ : ℂ)*I)‖^2 = (x^2+(y-1)^2)/(x^2+(y+1)^2) := by
    rw [norm_div, div_pow, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply, Complex.normSq_apply]
    simp; ring_nf
  rw [Complex.arctan]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.log_re, Complex.log_im, Complex.add_re, Complex.div_re,
      Complex.ofReal_re, Complex.ofReal_im]
    rw [trigR4_arg_of_re_pos hre, hw]
    simp
    rw [div_div_div_cancel_right₀ hD.ne']
    ring
  · have e : Real.log ((x^2+(y+1)^2)/(x^2+(y-1)^2)) =
        -(2 * Real.log ‖(1+(⟨x, y⟩ : ℂ)*I)/(1-(⟨x, y⟩ : ℂ)*I)‖) := by
      rw [← inv_div, Real.log_inv, ← hnorm, Real.log_pow]; push_cast; ring
    rw [e, Complex.add_im, Complex.div_ofNat_im, Complex.ofReal_im, zero_div, zero_add]
    simp [Complex.log_re, -Complex.norm_div]
    ring

/-- The Gudermannian, real and odd on the full real line. -/
@[dlmf 4.23.E39]
def gudermannian (x : ℝ) : ℝ := ∫ t in (0:ℝ)..x,(Real.cosh t)⁻¹

/-- The inverse Gudermannian on the open strip (-pi/2,pi/2). -/
@[dlmf 4.23.E41]
def inverseGudermannian (x : ℝ) : ℝ := ∫ t in (0:ℝ)..x,(Real.cos t)⁻¹

/-- Identity under the stated parameter and domain assumptions: `gudermannian x=f x`. -/
private lemma trig_gd_integral {f:ℝ→ℝ}
    (hf:∀x,HasDerivAt f (Real.cosh x)⁻¹ x) (h0:f 0=0) (x:ℝ) : gudermannian x=f x := by
  have hc:Continuous (fun t:ℝ=>(Real.cosh t)⁻¹) := Real.continuous_cosh.inv₀ (fun t=>(Real.cosh_pos t).ne')
  rw [gudermannian,intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _=>hf t) (hc.intervalIntegrable 0 x),h0,sub_zero]

/-- Identity under the stated parameter and domain assumptions: `Real.sqrt (1-(Real.tanh
x)^2)=(Real.cosh x)⁻¹`. -/
private lemma trig_sqrt_one_sub_tanh (x:ℝ) :
    Real.sqrt (1-(Real.tanh x)^2)=(Real.cosh x)⁻¹ := by
  have hc:0<Real.cosh x := Real.cosh_pos x
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (inv_nonneg.mpr hc.le)).mp
  rw [Real.sq_sqrt (by linarith [Real.tanh_sq_lt_one x]),Real.tanh_eq_sinh_div_cosh]
  field_simp
  linear_combination Real.cosh_sq_sub_sinh_sq x

/-- Identity under the stated parameter and domain assumptions: `Real.sqrt (1+(Real.tan
x)^2)=(Real.cos x)⁻¹`. -/
private lemma trig_sqrt_one_add_tan {x:ℝ} (hx:|x|<π/2) :
    Real.sqrt (1+(Real.tan x)^2)=(Real.cos x)⁻¹ := by
  simpa only [inv_inv] using congrArg Inv.inv
    (Real.inv_sqrt_one_add_tan_sq (Real.cos_pos_of_mem_Ioo (abs_lt.mp hx)))

/-- Identity under the stated parameter and domain assumptions: `inverseGudermannian x=f x`. -/
private lemma trig_inverse_gd_integral {f:ℝ→ℝ}
    (hf:∀t,|t|<π/2→HasDerivAt f (Real.cos t)⁻¹ t) (h0:f 0=0)
    {x:ℝ} (hx:|x|<π/2) : inverseGudermannian x=f x := by
  have hmem:∀t∈uIcc (0:ℝ) x,|t|<π/2 := by
    intro t ht
    apply abs_lt.mpr
    rcases le_total 0 x with h|h
    · rw [uIcc_of_le h] at ht
      exact ⟨by linarith [ht.1,Real.pi_pos],by linarith [ht.2,(abs_lt.mp hx).2]⟩
    · rw [uIcc_of_ge h] at ht
      exact ⟨by linarith [ht.1,(abs_lt.mp hx).1],by linarith [ht.2,Real.pi_pos]⟩
  have hcos:∀t∈uIcc (0:ℝ) x,Real.cos t≠0 := fun t ht=>
    (Real.cos_pos_of_mem_Ioo (abs_lt.mp (hmem t ht))).ne'
  have hc:ContinuousOn (fun t:ℝ=>(Real.cos t)⁻¹) (uIcc 0 x) := Real.continuous_cos.continuousOn.inv₀ hcos
  rw [inverseGudermannian,intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht=>hf t (hmem t ht)) hc.intervalIntegrable,h0,sub_zero]

/-- Identity under the stated parameter and domain assumptions: `inverseGudermannian x=Real.arsinh
(Real.tan x)`. -/
private lemma trig_inverse_gd_arsinh {x:ℝ} (hx:|x|<π/2) :
    inverseGudermannian x=Real.arsinh (Real.tan x) := by
  refine trig_inverse_gd_integral (f:=fun t=>Real.arsinh (Real.tan t)) ?_ ?_ hx
  · intro t ht
    have hc:Real.cos t≠0 := (Real.cos_pos_of_mem_Ioo (abs_lt.mp ht)).ne'
    have hd:=(Real.hasDerivAt_tan hc).arsinh
    convert hd using 1
    rw [smul_eq_mul,trig_sqrt_one_add_tan ht]
    field_simp
  · simp

/-- DLMF 4.23.E40: gudermannian elementary. -/
@[dlmf 4.23.E40]
theorem gudermannian_elementary (x : ℝ) :
    gudermannian x=2*Real.arctan (Real.exp x)-π/2 ∧
    gudermannian x=Real.arcsin (Real.tanh x) ∧
    gudermannian x=Real.arctan (Real.sinh x) := by
  have he: gudermannian x=2*Real.arctan (Real.exp x)-π/2 := by
    apply trig_gd_integral
    · intro t
      have hd:=((Real.hasDerivAt_exp t).arctan.const_mul 2).sub_const (π/2)
      convert hd using 1
      rw [Real.cosh_eq,Real.exp_neg]
      field_simp
      ring
    · norm_num
      ring
  have hs: gudermannian x=Real.arctan (Real.sinh x) := by
    apply trig_gd_integral
    · intro t
      have hd:=(Real.hasDerivAt_sinh t).arctan
      convert hd using 1
      have hc:Real.cosh t≠0 := (Real.cosh_pos t).ne'
      have hp:1+(Real.sinh t)^2≠0 := by positivity
      field_simp
      linear_combination -Real.cosh_sq_sub_sinh_sq t
    · simp
  refine ⟨he,?_,hs⟩
  rw [Real.arcsin_eq_arctan ⟨Real.neg_one_lt_tanh x,Real.tanh_lt_one x⟩,trig_sqrt_one_sub_tanh]
  convert hs using 2
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

/-- DLMF 4.23.E40: gudermannian reciprocal. -/
@[dlmf 4.23.E40]
theorem gudermannian_reciprocal {x : ℝ} (hx : x≠0) :
    gudermannian x=Real.arcsin ((Real.cosh x/Real.sinh x)⁻¹) ∧
    gudermannian x=Real.arctan (((Real.sinh x)⁻¹)⁻¹) := by
  constructor
  · simpa only [inv_div,Real.tanh_eq_sinh_div_cosh] using (gudermannian_elementary x).2.1
  · simpa only [inv_inv] using (gudermannian_elementary x).2.2

/-- The principal arccosine/secant forms require x nonnegative. -/
@[dlmf 4.23.E40]
theorem gudermannian_nonneg_cosine {x : ℝ} (hx : 0≤x) :
    gudermannian x=Real.arccos ((Real.cosh x)⁻¹) := by
  have hcos:Real.cos (Real.arctan (Real.sinh x))=(Real.cosh x)⁻¹ := by
    rw [Real.cos_arctan,← Real.cosh_sq',Real.sqrt_sq (Real.cosh_pos x).le,one_div]
  rw [← hcos,Real.arccos_cos]
  · exact (gudermannian_elementary x).2.2
  · exact Real.arctan_nonneg.mpr (Real.sinh_nonneg_iff.mpr hx)
  · exact (Real.arctan_lt_pi_div_two _).le.trans (by linarith [Real.pi_pos])

/-- DLMF 4.23.E42: inverse gudermannian elementary. -/
@[dlmf 4.23.E42]
theorem inverse_gudermannian_elementary {x : ℝ} (hx : |x|<π/2) :
    inverseGudermannian x=Real.log (Real.tan (x/2+π/4)) ∧
    inverseGudermannian x=Real.log ((Real.cos x)⁻¹+Real.tan x) ∧
    inverseGudermannian x=Real.arsinh (Real.tan x) ∧
    inverseGudermannian x=Real.artanh (Real.sin x) := by
  have ha:=trig_inverse_gd_arsinh hx
  have hc:0<Real.cos x := Real.cos_pos_of_mem_Ioo (abs_lt.mp hx)
  have hinv:gudermannian (inverseGudermannian x)=x := by
    rw [(gudermannian_elementary _).2.2,ha,Real.sinh_arsinh]
    exact Real.arctan_tan (abs_lt.mp hx).1 (abs_lt.mp hx).2
  have he:Real.exp (inverseGudermannian x)=Real.tan (x/2+π/4) := by
    rw [← Real.tan_arctan (Real.exp (inverseGudermannian x))]
    congr 1
    linarith [(gudermannian_elementary (inverseGudermannian x)).1]
  refine ⟨?_,?_,ha,?_⟩
  · rw [← he,Real.log_exp]
  · rw [ha,Real.arsinh,trig_sqrt_one_add_tan hx]
    congr 1
    ring
  · have hs:Real.sin x∈Ioo (-1:ℝ) 1 := by
      have hcircle:=Real.sin_sq_add_cos_sq x
      have hp:=sq_pos_of_pos hc
      constructor <;> nlinarith
    have hsqrt:Real.sqrt (1-(Real.sin x)^2)=Real.cos x := by
      rw [show 1-(Real.sin x)^2=(Real.cos x)^2 by nlinarith [Real.sin_sq_add_cos_sq x],Real.sqrt_sq hc.le]
    rw [ha]
    apply Real.sinh_injective
    rw [Real.sinh_arsinh,Real.sinh_artanh hs,hsqrt,Real.tan_eq_sin_div_cos]

/-- DLMF 4.23.E42: inverse gudermannian reciprocal. -/
@[dlmf 4.23.E42]
theorem inverse_gudermannian_reciprocal {x : ℝ} (hx : |x|<π/2) (hx0 : x≠0) :
    inverseGudermannian x=Real.arsinh (Real.cot x)⁻¹ ∧
    inverseGudermannian x=Real.artanh (((Real.sin x)⁻¹)⁻¹) := by
  refine ⟨?_,?_⟩
  · simpa only [Real.cot_eq_cos_div_sin,inv_div,Real.tan_eq_sin_div_cos] using
      (inverse_gudermannian_elementary hx).2.2.1
  · simpa only [inv_inv] using (inverse_gudermannian_elementary hx).2.2.2

/-- The principal arccosh/arcsech forms require x nonnegative. -/
@[dlmf 4.23.E42]
theorem inverse_gudermannian_nonneg_cosh {x : ℝ} (hx : 0≤x) (hπ : x<π/2) :
    inverseGudermannian x=Real.arcosh ((Real.cos x)⁻¹) := by
  have hbound:|x|<π/2 := by rwa [abs_of_nonneg hx]
  have hc:0<Real.cos x := Real.cos_pos_of_mem_Ioo (abs_lt.mp hbound)
  have ht:0≤Real.tan x := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx (by linarith [Real.pi_pos])) hc.le
  have hcosh:Real.cosh (Real.arsinh (Real.tan x))=(Real.cos x)⁻¹ := by
    rw [Real.cosh_arsinh,trig_sqrt_one_add_tan hbound]
  rw [← hcosh,Real.arcosh_cosh (Real.arsinh_nonneg_iff.mpr ht)]
  exact (inverse_gudermannian_elementary hbound).2.2.1

/-- DLMF 4.23.viii: gudermannian inverse. -/
@[dlmf 4.23.viii]
theorem gudermannian_inverse {x : ℝ} (hx : |x|<π/2) (y : ℝ) :
    gudermannian (inverseGudermannian x)=x ∧ inverseGudermannian (gudermannian y)=y := by
  constructor
  · rw [(gudermannian_elementary _).2.2,(inverse_gudermannian_elementary hx).2.2.1,Real.sinh_arsinh]
    exact Real.arctan_tan (abs_lt.mp hx).1 (abs_lt.mp hx).2
  · have hy:|gudermannian y|<π/2 := by
      rw [(gudermannian_elementary y).2.2]
      exact abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan _,Real.arctan_lt_pi_div_two _⟩
    rw [(inverse_gudermannian_elementary hy).2.2.1,(gudermannian_elementary y).2.2,
      Real.tan_arctan,Real.arsinh_sinh]

/-- The half-parameter binomial coefficient is a scaled central binomial coefficient; duplication uses lean-codes. -/
private lemma half_poch_coefficient (n : ℕ) :
    (ascPochhammer ℂ n).eval (1/2:ℂ)/(n.factorial:ℂ) = ((2*n).choose n:ℂ)/(4:ℂ)^n := by
  have hd := ascPochhammer_eval_double (1/2:ℂ) n
  norm_num only [show (2:ℂ)*(1/2)=1 by norm_num,
    show (1/2:ℂ)+1/2=1 by norm_num, ascPochhammer_eval_one] at hd
  have hc := congrArg (fun k : ℕ => (k:ℂ)) (Nat.add_choose_mul_factorial_mul_factorial n n)
  rw [show n+n=2*n by omega] at hc
  push_cast at hc
  have hn : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have h4 : (4:ℂ)^n ≠ 0 := pow_ne_zero n (by norm_num)
  apply (div_eq_div_iff hn h4).mpr
  apply (mul_right_cancel₀ hn)
  linear_combination -hd-hc
/-- The Gauss coefficient for parameters `(1/2, 1/2; 3/2)` equals the arcsine coefficient. -/
private lemma arcsin_gauss_coefficient (n : ℕ) :
    DLMF.Hypergeometric.gaussHGCoeff (1/2:ℂ) (1/2) (3/2) n =
      ((2*n).choose n:ℂ)/((4:ℂ)^n*(2*n+1)) := by
  have hp : DLMF.Hypergeometric.poch (1/2:ℂ) n ≠ 0 := by
    apply DLMF.Hypergeometric.poch_ne_zero_of_not_neg_nat
    intro k h
    have hh := congrArg Complex.re h
    norm_num at hh
    linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  rw [DLMF.Hypergeometric.gaussHGCoeff, DLMF.Hypergeometric.poch_three_halves_eq]
  have hhalf := half_poch_coefficient n
  unfold DLMF.Hypergeometric.poch at *
  have hn : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have h2 : (2*n+1:ℂ) ≠ 0 := by exact_mod_cast (show 2*n+1 ≠ 0 by omega)
  field_simp at hhalf ⊢
  linear_combination hhalf
/-- Gauss convergence at one gives absolute convergence of the arcsine coefficients. -/
private lemma arcsin_coeff_summable :
    Summable (fun n : ℕ => ((2*n).choose n:ℂ)/((4:ℂ)^n*(2*n+1))) := by
  have h := DLMF.Hypergeometric.ordinaryHypergeometric_summable_of_mem_sphere
    (a:=(1/2:ℂ)) (b:=1/2) (c:=3/2) (z:=1) (by simp) (by norm_num)
  simpa only [one_pow,mul_one,arcsin_gauss_coefficient] using h
/-- The binomial derivative series integrates to the principal arcsine on the open unit disk. -/
private lemma arcsin_series_open {z : ℂ} (hz : ‖z‖<1) :
    HasSum (fun n : ℕ => ((2*n).choose n:ℂ)*z^(2*n+1)/(4^n*(2*n+1))) (arcsinPrincipal z) := by
  have hdom {w : ℂ} (hw : ‖w‖<1) : w ∈ arcsinCutPlane :=
    Or.inr ((Complex.abs_re_le_norm w).trans_lt hw)
  have hb : ∀ w : ℂ, ‖w‖<1 →
      HasSum (fun n : ℕ => (((2*n).choose n:ℂ)/(4:ℂ)^n)*w^(2*n)) (deriv arcsinPrincipal w) := by
    intro w hw
    have hw2 : ‖w^2‖<1 := by rw [norm_pow]; nlinarith [norm_nonneg w]
    have h := Complex.hasSum_ascPochhammer_mul_pow_div_factorial (1/2:ℂ) (w^2) hw2
    have hpow (n : ℕ) : (w^2)^n=w^(2*n) := (pow_mul w 2 n).symm
    simp_rw [half_poch_coefficient, hpow] at h
    rw [(trig_hasDerivAt_arcsin (hdom hw)).deriv]
    simpa only [Complex.sqrt, one_div] using h
  have h := Complex.hasSum_even_primitive_on_ball (by norm_num : (0:ℝ)<1)
    (fun w hw => (trig_hasDerivAt_arcsin (hdom (by simpa using hw))).differentiableAt.differentiableWithinAt)
    (by simp [arcsinPrincipal]) hb hz
  convert h using 1
  ext n
  field_simp

/-- The central-binomial expansion of the principal arcsine converges absolutely
on the closed unit disk, including both branch points. -/
@[dlmf 4.24.E1]
theorem hasSum_arcsin_principal {z : ℂ} (hz : ‖z‖≤1) :
    HasSum (fun n : ℕ => ((2*n).choose n:ℂ)*z^(2*n+1)/(4^n*(2*n+1))) (arcsinPrincipal z) := by
  let c : ℕ → ℂ := fun n => ((2*n).choose n:ℂ)/((4:ℂ)^n*(2*n+1))
  let S := fun w : ℂ => ∑' n, c n*w^(2*n+1)
  have hsum : Summable (fun n => ‖c n‖) := arcsin_coeff_summable.norm
  have hbound {w : ℂ} (hw : ‖w‖≤1) (n : ℕ) : ‖c n*w^(2*n+1)‖ ≤ ‖c n‖ := by
    rw [norm_mul,norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hw)
  have hc : ContinuousOn S (Metric.closedBall (0:ℂ) 1) :=
    continuousOn_tsum (fun n => (by fun_prop : Continuous (fun w : ℂ => c n*w^(2*n+1))).continuousOn)
      hsum (fun n w hw => hbound (by simpa using hw) n)
  have ha : ContinuousOn arcsinPrincipal (Metric.closedBall (0:ℂ) 1) := fun w hw =>
    (continuousAt_arcsin_principal_of_norm_le_one (by simpa using hw)).continuousWithinAt
  have he : EqOn S arcsinPrincipal (Metric.ball (0:ℂ) 1) := by
    intro w hw
    have h := arcsin_series_open (z:=w) (by simpa using hw)
    have hf : (fun n : ℕ => ((2*n).choose n:ℂ)*w^(2*n+1)/(4^n*(2*n+1))) =
        fun n => c n*w^(2*n+1) := by
      funext n
      dsimp only [c]
      ring
    rw [hf] at h
    exact h.tsum_eq
  have hval : S z=arcsinPrincipal z := he.of_subset_closure hc ha Metric.ball_subset_closedBall
    (by rw [closure_ball (0:ℂ) (by norm_num : (1:ℝ)≠0)]) (by simpa using hz)
  have hsz : Summable (fun n => c n*z^(2*n+1)) := Summable.of_norm_bounded hsum (hbound hz)
  have hh := hsz.hasSum
  change HasSum (fun n => c n*z^(2*n+1)) (S z) at hh
  rw [hval] at hh
  convert hh using 1
  ext n
  dsimp only [c]
  ring

/-- The principal half-angle logarithm identifies arccosine with twice an arcsine off the cuts. -/
private lemma arccos_half_cut {z : ℂ} (hz : z ∈ arcsinCutPlane) :
    arccosPrincipal z = 2*arcsinPrincipal (Complex.sqrt ((1-z)/2)) := by
  rw [arccos_principal_log_half hz, arcsinPrincipal, trig_sqrt_sq,
    show 1-(1-z)/2 = (1+z)/2 by ring]
  ring
/-- The value on the positive real cut agrees with the lower-bank convention. -/
private lemma arcsin_real_cut {x : ℝ} (hx : 1≤x) :
    arcsinPrincipal x = arcsinRightBank false x := by
  have hp : 0 < Real.sqrt (x^2-1)+x := by positivity
  rw [arcsinPrincipal, trigR4_sqrt_eq_up (by simp [pow_two]), trigR4_one_sub_sq_real,
    trigR4_sqrtUp_neg (by nlinarith)]
  rw [show I*(Real.sqrt (x^2-1):ℂ)+I*x = I*((Real.sqrt (x^2-1)+x:ℝ):ℂ) by push_cast; ring,
    trigR4_log_I_mul_pos hp]
  simp only [arcsinRightBank, trigBankSign, Bool.false_eq_true, ite_false]
  linear_combination (-(π:ℂ)/2)*Complex.I_sq
/-- The principal half-angle square root maps the shifted closed disk into the closed unit disk. -/
private lemma half_root_norm_le {z : ℂ} (hz : ‖1-z‖≤2) : ‖Complex.sqrt ((1-z)/2)‖≤1 := by
  have he : ‖Complex.sqrt ((1-z)/2)‖^2 = ‖(1-z)/2‖ := by
    rw [← norm_pow, trig_sqrt_sq]
  rw [norm_div] at he
  norm_num at he
  nlinarith [norm_nonneg (Complex.sqrt ((1-z)/2))]
/-- The half-angle identity on the positive cut follows by approaching along the lower bank. -/
private lemma arccos_half_positive_cut {x : ℝ} (hx : 1<x) (hx3 : x≤3) :
    arccosPrincipal x = 2*arcsinPrincipal (Complex.sqrt ((1-(x:ℂ))/2)) := by
  let z : ℕ → ℂ := fun n => x-I/(n+1:ℂ)
  have hi (n : ℕ) : (z n).im < 0 := by
    dsimp only [z]
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.div_im, Complex.I_im,
      Complex.I_re, Complex.add_re, Complex.natCast_re, Complex.one_re, Complex.add_im,
      Complex.natCast_im, Complex.one_im, zero_add, zero_mul, zero_sub]
    have hn : 0 < Complex.normSq (n+1:ℂ) := Complex.normSq_pos.mpr (by exact_mod_cast Nat.succ_ne_zero n)
    have hn' : 0 < (n+1:ℝ) := by positivity
    simpa using neg_neg_of_pos (div_pos hn' hn)
  have hseq : Tendsto z atTop (𝓝 (x:ℂ)) := by
    have h := tendsto_const_div_atTop_nhds_zero_nat (I:ℂ)
    have hh := h.comp (tendsto_add_atTop_nat 1)
    simpa [z] using tendsto_const_nhds.sub hh
  have hseqT : Tendsto z atTop (𝓝[{w : ℂ | w.im<0}] (x:ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hseq,Eventually.of_forall hi⟩
  have hL := (arccos_right_cut_limit hx.le false).comp hseqT
  rw [← arcsin_real_cut hx.le] at hL
  change Tendsto (arccosPrincipal ∘ z) atTop (𝓝 (arccosPrincipal x)) at hL
  have hn : ‖1-(x:ℂ)‖≤2 := by
    rw [show 1-(x:ℂ)=((1-x:ℝ):ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (by linarith)]
    linarith
  have hp := continuousAt_arcsin_principal_of_norm_le_one (half_root_norm_le hn)
  have hroot := (trigR4_continuous_sqrtUp.comp
    (by fun_prop : Continuous (fun w : ℂ => (1-w)/2))).continuousAt.tendsto.comp hseq
  have he : trigR4_sqrtUp ((1-(x:ℂ))/2) = Complex.sqrt ((1-(x:ℂ))/2) :=
    (trigR4_sqrt_eq_up (by simp)).symm
  dsimp only [Function.comp_def] at hroot
  rw [he] at hroot
  have hR := (hp.tendsto.comp hroot).const_mul (2:ℂ)
  apply tendsto_nhds_unique hL
  refine hR.congr (fun n => ?_)
  dsimp only [Function.comp_def]
  rw [arccos_half_cut (Or.inl (ne_of_lt (hi n))),
    trigR4_sqrt_eq_up (by simp; linarith [hi n])]
/-- The principal half-angle identity holds on the whole shifted disk, including its cut values. -/
private lemma arccos_half_shifted_disk {z : ℂ} (hz : ‖1-z‖≤2) :
    arccosPrincipal z = 2*arcsinPrincipal (Complex.sqrt ((1-z)/2)) := by
  by_cases hcut : z ∈ arcsinCutPlane
  · exact arccos_half_cut hcut
  have him : z.im=0 := by
    by_contra h
    exact hcut (Or.inl h)
  have hab : 1≤|z.re| := le_of_not_gt fun h => hcut (Or.inr h)
  have hb := (Complex.abs_re_le_norm (1-z)).trans hz
  simp only [Complex.sub_re,Complex.one_re] at hb
  have hzrep : z=(z.re:ℂ) := by apply Complex.ext <;> simp [him]
  rcases lt_or_ge z.re 1 with hlt | hge
  · have hx : z.re = -1 := by
      rcases le_or_gt 0 z.re with hpos | hneg
      · rw [abs_of_nonneg hpos] at hab; linarith
      · rw [abs_of_neg hneg] at hab
        have hlow := (abs_le.mp hb).2
        linarith
    rw [hzrep,hx]
    norm_num [arccosPrincipal,arcsinPrincipal,Complex.log_I,Complex.log_neg_I]
    ring_nf
    rw [Complex.I_sq]
    ring
  · rcases eq_or_lt_of_le hge with heq | hgt
    · rw [hzrep,← heq]
      norm_num [arccosPrincipal,arcsinPrincipal,Complex.log_I]
      ring_nf
      rw [Complex.I_sq]
      ring
    · rw [hzrep]
      exact arccos_half_positive_cut hgt (by have hlow := (abs_le.mp hb).1; linarith)
/-- Multiplying by four scales the principal square root by two without changing its argument. -/
private lemma sqrt_four_mul (w : ℂ) : Complex.sqrt (4*w) = 2*Complex.sqrt w := by
  have h := Complex.sqrt_ofReal_mul (by norm_num : (0:ℝ)≤4) w
  norm_num at h
  exact h

/-- Arccosine series after factoring its square root, with the removable center handled separately. -/
@[dlmf 4.24.E2]
theorem hasSum_arccos_principal {z : ℂ} (hz : ‖1-z‖≤2) :
    HasSum (fun n : ℕ => Complex.sqrt (2*(1-z))*((2*n).choose n:ℂ)*(1-z)^n/(8^n*(2*n+1)))
      (arccosPrincipal z) := by
  have h := (hasSum_arcsin_principal (half_root_norm_le hz)).mul_left 2
  rw [← arccos_half_shifted_disk hz] at h
  convert h using 1
  ext n
  rw [show (2:ℂ)*(1-z)=4*((1-z)/2) by ring, sqrt_four_mul,
    pow_add, pow_mul, trig_sqrt_sq, pow_one, div_pow,
    show (8:ℂ)^n=4^n*2^n by rw [← mul_pow]; norm_num]
  field_simp

/-- DLMF 4.24.E2: arccos series center. -/
@[dlmf 4.24.E2]
theorem arccos_series_center : arccosPrincipal 1=0 := by
  norm_num [arccosPrincipal,arcsinPrincipal,Complex.sqrt_zero]
  rw [Complex.log_I]
  norm_num [div_eq_mul_inv]
  linear_combination Complex.I_sq* (Real.pi:ℂ)/2

/-- Ordered partial sums retain conditional convergence on the unit circle. -/
@[dlmf 4.24.E3]
theorem hasSum_arctan_closed_disc {z : ℂ} (hz : ‖z‖≤1) (hp : z≠I) (hm : z≠ -I) :
    Tendsto (fun N : ℕ => ∑ n∈Finset.range N,(-1:ℂ)^n*z^(2*n+1)/(2*n+1)) atTop
      (𝓝 (Complex.arctan z)) := by
  have hnorm : ‖z * I‖ ≤ 1 := by simpa using hz
  have hplus : z * I ≠ 1 := by
    intro h
    apply hm
    calc z = (z * I) * (-I) := by simp [mul_assoc]
         _ = -I := by rw [h]; ring
  have hminus : z * I ≠ -1 := by
    intro h
    apply hp
    calc z = (z * I) * (-I) := by simp [mul_assoc]
         _ = I := by rw [h]; ring
  have h := (logBoundary_odd hnorm hplus hminus).const_mul (-I/2)
  rw [← Complex.arctan] at h
  refine h.congr (fun N => ?_)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [mul_pow, pow_add I, pow_mul I, I_sq, pow_one I]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The exterior logarithmic form of arctangent keeps the principal branch correction
on the appropriate side of the imaginary axis. -/
private lemma trigR4_arctan_exterior_log {z : ℂ} (hr : z.re ≠ 0) :
    (if 0<z.re then (π:ℂ)/2 else -π/2) -
      I/2*Complex.log ((z*I+1)/(z*I-1)) = Complex.arctan z := by
  let v := (1 + z * I) / (1 - z * I)
  have hd : 1 - z * I ≠ 0 := by
    intro h
    apply hr
    have hi := congrArg Complex.im h
    simpa using hi
  have hns : 0 < Complex.normSq (1 - z * I) := Complex.normSq_pos.mpr hd
  have hvim : v.im = 2 * z.re / Complex.normSq (1 - z * I) := by
    dsimp only [v]
    rw [Complex.div_im]
    simp [Complex.normSq_apply]
    ring
  have hq : (z * I + 1) / (z * I - 1) = -v := by
    dsimp only [v]
    have hd' : z*I-1 ≠ 0 := by intro h; apply hd; linear_combination -h
    field_simp
    ring
  rw [hq]
  change (if 0<z.re then (π:ℂ)/2 else -π/2) - I/2*Complex.log (-v) = Complex.arctan z
  have hlog : (if 0<z.re then (π:ℂ)/2 else -π/2) - I/2*Complex.log (-v) = Complex.arctan z := by
    rw [Complex.arctan]
    change (if 0<z.re then (π:ℂ)/2 else -π/2) - I/2*Complex.log (-v) = -I/2*Complex.log v
    split_ifs with hp
    · have hi : 0 < v.im := by rw [hvim]; positivity
      have hl : Complex.log (-v) = Complex.log v - π*I := by
        rw [Complex.log, Complex.log, norm_neg, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hi]
        push_cast
        ring
      rw [hl]
      ring_nf
      rw [Complex.I_sq]
      ring
    · have hneg : z.re < 0 := lt_of_le_of_ne (not_lt.mp hp) hr
      have hi : v.im < 0 := by rw [hvim]; exact div_neg_of_neg_of_pos (by linarith) hns
      have hl : Complex.log (-v) = Complex.log v + π*I := by
        rw [Complex.log, Complex.log, norm_neg, Complex.arg_neg_eq_arg_add_pi_of_im_neg hi]
        push_cast
        ring
      rw [hl]
      ring_nf
      rw [Complex.I_sq]
      ring
  exact hlog

/-- DLMF 4.24.E4: arctan exterior series. -/
@[dlmf 4.24.E4]
theorem arctan_exterior_series {z : ℂ} (hz : 1≤‖z‖) (hr : z.re≠0) :
    Tendsto (fun N : ℕ => (if 0<z.re then (π:ℂ)/2 else -π/2)-
      ∑ n∈Finset.range N,(-1:ℂ)^n/(z^(2*n+1)*(2*n+1))) atTop (𝓝 (Complex.arctan z)) := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hr
  have hnorm : 1 ≤ ‖z * I‖ := by simpa using hz
  have hplus : z * I ≠ 1 := by
    intro h
    have hh := congrArg Complex.re (congrArg (fun w : ℂ => w * (-I)) h)
    simp [mul_assoc] at hh
    exact hr hh
  have hminus : z * I ≠ -1 := by
    intro h
    have hh := congrArg Complex.re (congrArg (fun w : ℂ => w * (-I)) h)
    simp [mul_assoc] at hh
    exact hr hh
  have h := (log_ratio_hasSum_odd hnorm hplus hminus).const_mul (I/2)
  have hc : ∀ N : ℕ, I/2 * (∑ n ∈ Finset.range N, 2 / ((2*n+1:ℂ)*(z*I)^(2*n+1))) =
      ∑ n ∈ Finset.range N, (-1:ℂ)^n/(z^(2*n+1)*(2*n+1)) := by
    intro N
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [mul_pow, pow_add I, pow_mul I, I_sq, pow_one I]
    have hn : (2*n+1:ℂ) ≠ 0 := by exact_mod_cast (show 2*n+1 ≠ 0 by omega)
    field_simp
    ring_nf
    simp
  simp_rw [hc] at h
  simpa only [trigR4_arctan_exterior_log hr] using
    ((tendsto_const_nhds (x := if 0<z.re then (π:ℂ)/2 else -π/2)).sub h)

/-- Integer Beta integrals give the factorial moments of the weight `4t(1-t)`. -/
private lemma euler_beta_moment (n : ℕ) :
    (∫ t : ℝ in (0:ℝ)..1, ((4*t*(1-t):ℝ):ℂ)^n) =
      (4:ℂ)^n*(n.factorial:ℂ)^2/((2*n+1).factorial:ℂ) := by
  have hh : Complex.betaIntegral ((n:ℂ)+1) ((n:ℂ)+1) =
      (n.factorial:ℂ)^2/((2*n+1).factorial:ℂ) := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simp; positivity) (by simp; positivity),
      Complex.Gamma_nat_eq_factorial]
    rw [show (n:ℂ)+1+(n+1) = ((2*n+1:ℕ):ℂ)+1 by push_cast; ring,
      Complex.Gamma_nat_eq_factorial]
    ring
  rw [mul_div_assoc, ← hh, Complex.betaIntegral, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [add_sub_cancel_right, Complex.cpow_natCast, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_sub, Complex.ofReal_one, mul_pow]
  ring
/-- Integrating a dominated geometric series gives the factorial-coefficient Euler kernel. -/
private lemma euler_kernel_series {w : ℂ} (hw : ‖w‖<1) :
    HasSum (fun n : ℕ => (4:ℂ)^n*(n.factorial:ℂ)^2/((2*n+1).factorial:ℂ)*w^n)
      (∫ t : ℝ in (0:ℝ)..1, (1-((4*t*(1-t):ℝ):ℂ)*w)⁻¹) := by
  let F : ℕ → ℝ → ℂ := fun n t => (((4*t*(1-t):ℝ):ℂ)*w)^n
  have hb {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : 0 ≤ 4*t*(1-t) ∧ 4*t*(1-t) ≤ 1 := by
    constructor
    · exact mul_nonneg (mul_nonneg (by norm_num) ht.1) (sub_nonneg.mpr ht.2)
    · nlinarith [sq_nonneg (2*t-1)]
  have hnorm {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : ‖((4*t*(1-t):ℝ):ℂ)*w‖ ≤ ‖w‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb ht).1]
    nlinarith [(hb ht).2, norm_nonneg w]
  have hbound (n : ℕ) (t : ℝ) (ht : t ∈ uIoc (0:ℝ) 1) : ‖F n t‖ ≤ ‖w‖^n := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hnorm ⟨by simpa using le_of_lt ht.1, by simpa using ht.2⟩) n
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := (0:ℝ)) (b := 1) (fun n _ => ‖w‖^n)
    (fun n => (by fun_prop : Continuous (F n)).aestronglyMeasurable)
    (fun n => Eventually.of_forall (hbound n))
    (Eventually.of_forall fun t ht => summable_geometric_of_lt_one (norm_nonneg _) hw)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => ∑' n : ℕ, ‖w‖^n) volume 0 1)
    (Eventually.of_forall fun t ht =>
      hasSum_geometric_of_norm_lt_one ((hnorm ⟨by simpa using le_of_lt ht.1, by simpa using ht.2⟩).trans_lt hw))
  convert hsum using 1
  ext n
  dsimp only [F]
  simp_rw [mul_pow]
  rw [intervalIntegral.integral_mul_const, euler_beta_moment]
/-- The parabolic convergence domain remains in the principal arctangent cut plane under real contractions. -/
private lemma arctan_scaled_cut {z : ℂ} (hz : -(1/2:ℝ)<(z^2).re)
    {u : ℝ} (hu : |u|≤1) : (u:ℂ)*z ∈ arctanCutPlane := by
  by_cases hu0 : u=0
  · simp [hu0, arctanCutPlane]
  by_cases hx0 : z.re=0
  · right
    have hh : |z.im|<1 := by
      rw [pow_two, Complex.mul_re, hx0] at hz
      rw [abs_lt]
      constructor <;> nlinarith
    simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, zero_mul, add_zero,
      abs_mul]
    exact (mul_le_mul_of_nonneg_right hu (abs_nonneg _)).trans_lt (by simpa using hh)
  · left
    simpa using mul_ne_zero hu0 hx0
/-- The arctangent derivative evaluates the Euler kernel along the symmetric segment from `-z` to `z`. -/
private lemma euler_arctan_integral {z : ℂ} (hz : -(1/2:ℝ)<(z^2).re) :
    (∫ t : ℝ in (0:ℝ)..1, z/(1+z^2*((2*t-1:ℝ):ℂ)^2)) = Complex.arctan z := by
  have hdom {t : ℝ} (ht : t ∈ uIcc (0:ℝ) 1) : ((2*t-1:ℝ):ℂ)*z ∈ arctanCutPlane := by
    apply arctan_scaled_cut hz
    have ht' : t ∈ Icc (0:ℝ) 1 := by simpa using ht
    rw [abs_le]
    constructor <;> linarith [ht'.1,ht'.2]
  have hden {t : ℝ} (ht : t ∈ uIcc (0:ℝ) 1) : 1+z^2*((2*t-1:ℝ):ℂ)^2 ≠ 0 := by
    have h := Complex.slitPlane_ne_zero (trig_one_add_sq_slit (hdom ht))
    convert h using 1
    ring
  have hint : IntervalIntegrable (fun t : ℝ => z/(1+z^2*((2*t-1:ℝ):ℂ)^2)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    exact fun t ht => hden ht
  have hd (t : ℝ) (ht : t ∈ uIcc (0:ℝ) 1) :
      HasDerivAt (fun u : ℝ => Complex.arctan (((2*u-1:ℝ):ℂ)*z)/2)
        (z/(1+z^2*((2*t-1:ℝ):ℂ)^2)) t := by
    have hu : HasDerivAt (fun u : ℝ => ((2*u-1:ℝ):ℂ)*z) (2*z) t := by
      simpa using (((Complex.ofRealCLM.hasDerivAt (x:=t)).const_mul (2:ℂ)).sub_const 1).mul_const z
    have hh := ((trig_hasDerivAt_arctan (hdom ht)).comp_hasFDerivAt t hu.hasFDerivAt).hasDerivAt
    convert hh.div_const (2:ℂ) using 1
    · rfl
    · simp only [smul_apply, smul_eq_mul]
      simp
      ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  have hzdom := arctan_scaled_cut hz (u:=1) (by norm_num)
  simp only [Complex.ofReal_one, one_mul] at hzdom
  convert h using 1
  norm_num [arctan_principal_neg hzdom]
  ring

/-- Euler’s transformed arctangent series on `Re (z²) > -1/2`, including the removable value at zero. -/
@[dlmf 4.24.E5]
theorem hasSum_arctan_euler {z : ℂ} (hz : -(1/2:ℝ)<(z^2).re) :
    HasSum (fun n : ℕ => z/(1+z^2)*(4:ℂ)^n*(n.factorial:ℂ)^2/(2*n+1)!*(z^2/(1+z^2))^n)
      (Complex.arctan z) := by
  have hden : 1+z^2 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    linarith
  have hw : ‖z^2/(1+z^2)‖<1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hden)]
    have hs : ‖1+z^2‖^2 = ‖z^2‖^2+1+2*(z^2).re := by
      rw [Complex.sq_norm,Complex.sq_norm]
      simp [Complex.normSq_apply]
      ring
    nlinarith [norm_nonneg (1+z^2),norm_nonneg (z^2)]
  have h := (euler_kernel_series hw).mul_left (z/(1+z^2))
  have he : z/(1+z^2)*(∫ t : ℝ in (0:ℝ)..1,
      (1-((4*t*(1-t):ℝ):ℂ)*(z^2/(1+z^2)))⁻¹) = Complex.arctan z := by
    rw [← intervalIntegral.integral_const_mul, ← euler_arctan_integral hz]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    have hp : 1-((4*t*(1-t):ℝ):ℂ)*(z^2/(1+z^2)) =
        (1+z^2*((2*t-1:ℝ):ℂ)^2)/(1+z^2) := by
      field_simp
      push_cast
      ring
    rw [hp, inv_div]
    field_simp
  rw [he] at h
  convert h using 1
  ext n
  ring

/-- DLMF 4.24.E6: arctan euler domain. -/
@[dlmf 4.24.E6]
theorem arctan_euler_domain (z : ℂ) : -(1/2:ℝ)<(z^2).re ↔ -(1/2:ℝ)<z.re^2-z.im^2 := by
  simp [Complex.mul_re,pow_two]

/-- DLMF 4.24.E7: hasDerivAt arcsin principal. -/
@[dlmf 4.24.E7]
theorem hasDerivAt_arcsin_principal {z : ℂ} (hz : z∈arcsinCutPlane) : HasDerivAt arcsinPrincipal ((Complex.sqrt (1-z^2))⁻¹) z := by
  exact trig_hasDerivAt_arcsin hz

/-- DLMF 4.24.E8: hasDerivAt arccos principal. -/
@[dlmf 4.24.E8]
theorem hasDerivAt_arccos_principal {z : ℂ} (hz : z∈arcsinCutPlane) : HasDerivAt arccosPrincipal (-(Complex.sqrt (1-z^2))⁻¹) z := by
  exact (trig_hasDerivAt_arcsin hz).const_sub ((π:ℂ)/2)

/-- DLMF 4.24.E9: hasDerivAt arctan principal. -/
@[dlmf 4.24.E9]
theorem hasDerivAt_arctan_principal {z : ℂ} (hz : z∈arctanCutPlane) : HasDerivAt Complex.arctan ((1+z^2)⁻¹) z := by
  exact trig_hasDerivAt_arctan hz

/-- Real and imaginary parts of the principal square root. -/
lemma trigR4_sqrt_re_im (a : ℂ) :
    (Complex.sqrt a).re = √((‖a‖ + a.re) / 2) ∧
    (Complex.sqrt a).im = (if 0 ≤ a.im then 1 else -1) * √((‖a‖ - a.re) / 2) := by
  rw [Complex.sqrt_eq_real_add_ite]
  constructor <;> split_ifs <;> simp

/-- The principal square root has positive real part off the closed negative axis. -/
lemma trigR4_sqrt_re_pos {a : ℂ} (h : a.im ≠ 0 ∨ 0 < a.re) : 0 < (Complex.sqrt a).re := by
  rw [(trigR4_sqrt_re_im a).1]
  apply Real.sqrt_pos.mpr
  rcases h with h | h
  · have := (Complex.abs_re_lt_norm).mpr h
    have := neg_abs_le a.re
    linarith
  · linarith [Complex.re_le_norm a]

/-- The principal square root preserves a positive imaginary part. -/
lemma trigR4_sqrt_im_pos {a : ℂ} (h : 0 < a.im) : 0 < (Complex.sqrt a).im := by
  rw [(trigR4_sqrt_re_im a).2, ite_eq_left_of_eq_true _ _ (eq_true h.le), one_mul]
  apply Real.sqrt_pos.mpr
  have := (Complex.abs_re_lt_norm).mpr h.ne'
  have := le_abs_self a.re
  linarith

/-- The principal square root preserves a negative imaginary part. -/
lemma trigR4_sqrt_im_neg {a : ℂ} (h : a.im < 0) : (Complex.sqrt a).im < 0 := by
  rw [(trigR4_sqrt_re_im a).2, ite_eq_right_of_eq_false _ _ (eq_false (not_le.mpr h)), neg_one_mul,
    neg_lt_zero]
  apply Real.sqrt_pos.mpr
  have := (Complex.abs_re_lt_norm).mpr h.ne
  have := le_abs_self a.re
  linarith

/-- The reciprocal square-root branch identity off the reciprocal cuts. -/
lemma trigR4_mul_sqrt_one_sub_inv_sq {z : ℂ} (hz : z∈arccscCutPlane) (hr : z.re≠0) :
    z*Complex.sqrt (1-(z⁻¹)^2) = (if 0<z.re then 1 else -1)*Complex.sqrt (z^2-1) := by
  obtain ⟨hz0, hc⟩ := hz
  have hN : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz0
  have hu : (z⁻¹).re = z.re / Complex.normSq z := Complex.inv_re z
  have hv : (z⁻¹).im = -z.im / Complex.normSq z := Complex.inv_im z
  have hw1im : (1-(z⁻¹)^2).im = -2*(z⁻¹).re*(z⁻¹).im := by simp [pow_two, Complex.mul_im]; ring
  have hw1re : (1-(z⁻¹)^2).re = 1-(z⁻¹).re^2+(z⁻¹).im^2 := by simp [pow_two, Complex.mul_re]; ring
  have hw2im : (z^2-1).im = 2*z.re*z.im := by simp [pow_two, Complex.mul_im]; ring
  have hw2re : (z^2-1).re = z.re^2-z.im^2-1 := by simp [pow_two, Complex.mul_re]
  have hzai : (z*Complex.sqrt (1-(z⁻¹)^2)).im =
      z.re*(Complex.sqrt (1-(z⁻¹)^2)).im + z.im*(Complex.sqrt (1-(z⁻¹)^2)).re := by
    simp [Complex.mul_im]
  have hzar : (z*Complex.sqrt (1-(z⁻¹)^2)).re =
      z.re*(Complex.sqrt (1-(z⁻¹)^2)).re - z.im*(Complex.sqrt (1-(z⁻¹)^2)).im := by
    simp [Complex.mul_re]
  set a := Complex.sqrt (1-(z⁻¹)^2) with ha
  set b := Complex.sqrt (z^2-1) with hb
  set s : ℂ := if 0<z.re then 1 else -1 with hs
  have hs2 : s^2 = 1 := by rw [hs]; split_ifs <;> norm_num
  have hsq : (z*a)^2 = (s*b)^2 := by
    rw [mul_pow, mul_pow, hs2, ha, hb, trig_sqrt_sq, trig_sqrt_sq, one_mul]
    field_simp
  have hne : z*a + s*b ≠ 0 := by
    intro h0
    have him := congrArg Complex.im h0
    have hre := congrArg Complex.re h0
    rw [Complex.add_im, hzai] at him
    rw [Complex.add_re, hzar] at hre
    by_cases hy : z.im = 0
    · have hv0 : (z⁻¹).im = 0 := by rw [hv, hy]; simp
      have hlt : |(z⁻¹).re| < 1 := hc.resolve_left (not_not.mpr hv0)
      have hre1 : 0 < (1-(z⁻¹)^2).re := by
        rw [hw1re, hv0]; nlinarith [abs_mul_abs_self (z⁻¹).re, abs_nonneg (z⁻¹).re]
      have hNx : Complex.normSq z = z.re^2 := by rw [Complex.normSq_apply, hy]; ring
      have hux : (z⁻¹).re * z.re = 1 := by
        rw [hu, hNx]; field_simp
      have hre2 : 0 < (z^2-1).re := by
        rw [hw2re, hy]
        have h1 : ((z⁻¹).re * z.re)^2 = 1 := by rw [hux]; norm_num
        nlinarith [abs_mul_abs_self (z⁻¹).re, abs_nonneg (z⁻¹).re, sq_nonneg z.re]
      have hapos := trigR4_sqrt_re_pos (Or.inr hre1)
      have hbpos := trigR4_sqrt_re_pos (Or.inr hre2)
      rw [hy] at hre
      by_cases hx : 0 < z.re
      · rw [hs, ite_eq_left_of_eq_true _ _ (eq_true hx), one_mul] at hre
        simp at hre
        nlinarith
      · have hx' : z.re < 0 := lt_of_le_of_ne (not_lt.mp hx) hr
        rw [hs, ite_eq_right_of_eq_false _ _ (eq_false hx)] at hre
        simp at hre
        nlinarith
    · have hw1 : (1-(z⁻¹)^2).im = 2*z.re*z.im/(Complex.normSq z)^2 := by
        rw [hw1im, hu, hv]; field_simp
      have hN2 : 0 < (Complex.normSq z)^2 := by positivity
      have hapos : 0 < a.re := by
        rw [ha]; apply trigR4_sqrt_re_pos; left; rw [hw1]
        exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hr) hy) hN2.ne'
      rcases lt_or_gt_of_ne hr with hx | hx <;> rcases lt_or_gt_of_ne hy with hy' | hy'
      · -- x<0, y<0
        have hxy : 0 < z.re*z.im := mul_pos_of_neg_of_neg hx hy'
        have h1 : 0 < a.im := by
          rw [ha]; apply trigR4_sqrt_im_pos; rw [hw1]; apply div_pos _ hN2; linarith
        have h2 : 0 < b.im := by rw [hb]; apply trigR4_sqrt_im_pos; rw [hw2im]; linarith
        rw [hs, ite_eq_right_of_eq_false _ _ (eq_false (not_lt.mpr hx.le))] at him
        simp at him; linarith [mul_pos_of_neg_of_neg hx (neg_neg_of_pos h1), mul_neg_of_neg_of_pos hy' hapos]
      · -- x<0, y>0
        have hxy : z.re*z.im < 0 := mul_neg_of_neg_of_pos hx hy'
        have h1 : a.im < 0 := by
          rw [ha]; apply trigR4_sqrt_im_neg; rw [hw1]; apply div_neg_of_neg_of_pos _ hN2; linarith
        have h2 : b.im < 0 := by rw [hb]; apply trigR4_sqrt_im_neg; rw [hw2im]; linarith
        rw [hs, ite_eq_right_of_eq_false _ _ (eq_false (not_lt.mpr hx.le))] at him
        simp at him; linarith [mul_pos_of_neg_of_neg hx h1, mul_pos hy' hapos]
      · -- x>0, y<0
        have hxy : z.re*z.im < 0 := mul_neg_of_pos_of_neg hx hy'
        have h1 : a.im < 0 := by
          rw [ha]; apply trigR4_sqrt_im_neg; rw [hw1]; apply div_neg_of_neg_of_pos _ hN2; linarith
        have h2 : b.im < 0 := by rw [hb]; apply trigR4_sqrt_im_neg; rw [hw2im]; linarith
        rw [hs, ite_eq_left_of_eq_true _ _ (eq_true hx), one_mul] at him
        simp at him; linarith [mul_neg_of_pos_of_neg hx h1, mul_neg_of_neg_of_pos hy' hapos]
      · -- x>0, y>0
        have hxy : 0 < z.re*z.im := mul_pos hx hy'
        have h1 : 0 < a.im := by
          rw [ha]; apply trigR4_sqrt_im_pos; rw [hw1]; apply div_pos _ hN2; linarith
        have h2 : 0 < b.im := by rw [hb]; apply trigR4_sqrt_im_pos; rw [hw2im]; linarith
        rw [hs, ite_eq_left_of_eq_true _ _ (eq_true hx), one_mul] at him
        simp at him; linarith [mul_pos hx h1, mul_pos hy' hapos]
  have hprod : (z*a - s*b)*(z*a + s*b) = 0 := by linear_combination hsq
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hne)

/-- DLMF 4.24.E10: hasDerivAt arccsc principal. -/
@[dlmf 4.24.E10]
theorem hasDerivAt_arccsc_principal {z : ℂ} (hz : z∈arccscCutPlane) (hr : z.re≠0) : HasDerivAt arccscPrincipal (-(if 0<z.re then 1 else -1)/(z*Complex.sqrt (z^2-1))) z := by
  have hb := trigR4_mul_sqrt_one_sub_inv_sq hz hr
  have hz0 := hz.1
  have hd := (hasDerivAt_arcsin_principal hz.2).comp z (hasDerivAt_inv hz0)
  convert hd using 1
  · funext w; rfl
  set a := Complex.sqrt (1-(z⁻¹)^2)
  set s : ℂ := if 0<z.re then 1 else -1 with hs
  have hs2 : s*s = 1 := by rw [hs]; split_ifs <;> norm_num
  have hb' : Complex.sqrt (z^2-1) = s*(z*a) := by rw [hb, ← mul_assoc, hs2, one_mul]
  rw [hb']
  by_cases ha : a = 0
  · simp [ha]
  · have hs0 : s ≠ 0 := by intro h; rw [h] at hs2; norm_num at hs2
    field_simp

/-- DLMF 4.24.E11: hasDerivAt arcsec principal. -/
@[dlmf 4.24.E11]
theorem hasDerivAt_arcsec_principal {z : ℂ} (hz : z∈arccscCutPlane) (hr : z.re≠0) : HasDerivAt arcsecPrincipal ((if 0<z.re then 1 else -1)/(z*Complex.sqrt (z^2-1))) z := by
  have h := (hasDerivAt_arccsc_principal hz hr).const_sub ((π:ℂ)/2)
  convert h using 1
  · funext w; rw [arcsec_principal_complement]
  · ring

/-- DLMF 4.24.E12: hasDerivAt arccot principal. -/
@[dlmf 4.24.E12]
theorem hasDerivAt_arccot_principal {z : ℂ} (hz : z∈arccotCutPlane) : HasDerivAt arccotPrincipal (-(1+z^2)⁻¹) z := by
  have hd:=(trig_hasDerivAt_arctan hz.2).comp z ((hasDerivAt_id z).inv hz.1)
  convert hd using 1
  · rfl
  · dsimp only [id]
    field_simp [hz.1]
    ring

/-- Minkowski addition with an independently chosen sign. -/
def inverseTrigSum (A B : Set ℂ) (σ : ℂ) : Set ℂ := {w | ∃ a∈A,∃ b∈B,w=a+σ*b}

/-- Arcsine addition with root signs correlated to the chosen inverse values. -/
@[dlmf 4.24.E13]
theorem arcsin_general_add (u v a b σ : ℂ) (hσ : σ=1 ∨ σ= -1)
    (ha : a∈arcsinGeneral u) (hb : b∈arcsinGeneral v) :
    (Complex.cos a)^2=1-u^2 ∧ (Complex.cos b)^2=1-v^2 ∧
    a+σ*b∈arcsinGeneral (u*Complex.cos b+σ*v*Complex.cos a) := by
  simp only [arcsinGeneral,mem_setOf_eq] at ha hb ⊢
  rcases hσ with rfl | rfl <;>
    simp_all [Complex.cos_sq',Complex.sin_add,Complex.sin_neg,Complex.cos_neg,mul_comm,mul_left_comm,mul_assoc]

/-- DLMF 4.24.E14: arccos general add. -/
@[dlmf 4.24.E14]
theorem arccos_general_add (u v σ : ℂ) (hσ : σ=1 ∨ σ= -1) :
    inverseTrigSum (arccosGeneral u) (arccosGeneral v) σ=
      {w | ∃ r : ℂ,r^2=(1-u^2)*(1-v^2) ∧ w∈arccosGeneral (u*v-σ*r)} := by
  ext w
  constructor
  · rintro ⟨a,ha,b,hb,rfl⟩
    change Complex.cos a=u at ha
    change Complex.cos b=v at hb
    refine ⟨Complex.sin a*Complex.sin b,?_,?_⟩
    · simp only [mul_pow,Complex.sin_sq,ha,hb]
    · change Complex.cos (a+σ*b)=u*v-σ*(Complex.sin a*Complex.sin b)
      rcases hσ with rfl|rfl <;>
        simp [Complex.cos_add,Complex.cos_neg,Complex.sin_neg,ha,hb] <;> ring
  · rintro ⟨r,hr,hc⟩
    change Complex.cos w=u*v-σ*r at hc
    have hs:(v-u*Complex.cos w)^2=(Complex.sin w*Complex.sin (arccosPrincipal u))^2 := by
      simp only [mul_pow,Complex.sin_sq,cos_arccos_principal,hc]
      rcases hσ with rfl|rfl <;> simp only [one_mul,neg_one_mul] <;> linear_combination hr
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hs|hs
    · refine ⟨arccosPrincipal u,cos_arccos_principal u,σ*(w-arccosPrincipal u),?_,?_⟩
      · change Complex.cos (σ*(w-arccosPrincipal u))=v
        rcases hσ with rfl|rfl <;> simp only [one_mul,neg_one_mul,Complex.cos_neg] <;>
          rw [Complex.cos_sub,cos_arccos_principal] <;> linear_combination -hs
      · rcases hσ with rfl|rfl <;> ring
    · refine ⟨-arccosPrincipal u,?_,σ*(w+arccosPrincipal u),?_,?_⟩
      · change Complex.cos (-arccosPrincipal u)=u
        rw [Complex.cos_neg,cos_arccos_principal]
      · change Complex.cos (σ*(w+arccosPrincipal u))=v
        rcases hσ with rfl|rfl <;> simp only [one_mul,neg_one_mul,Complex.cos_neg] <;>
          rw [Complex.cos_add,cos_arccos_principal] <;> linear_combination -hs
      · rcases hσ with rfl|rfl <;> ring

/-- The principal arctangent is a general arctangent value off the branch points `±i`. -/
lemma trigR4_arctan_mem {u : ℂ} (h1 : u≠I) (h2 : u≠ -I) : Complex.arctan u∈arctanGeneral u := by
  refine ⟨fun h => ?_, Complex.tan_arctan h1 h2⟩
  have ht := Complex.tan_arctan h1 h2
  rw [Complex.tan_eq_sin_div_cos, h, div_zero] at ht
  subst ht
  rw [show Complex.arctan 0 = 0 by simp [Complex.arctan], Complex.cos_zero] at h
  exact one_ne_zero h

/-- `1+u^2≠0` off the branch points `±i`. -/
lemma trigR4_one_add_sq_ne {u : ℂ} (h1 : u≠I) (h2 : u≠ -I) : 1+u^2≠0 := by
  intro h
  have : (u-I)*(u+I)=0 := by linear_combination h - Complex.I_sq
  rcases mul_eq_zero.mp this with h | h
  · exact h1 (by linear_combination h)
  · exact h2 (by linear_combination h)

/-- The tangent of a sum and its nonvanishing cosine, for general arctangent values. -/
lemma trigR4_tan_add_mem {a b u v σ : ℂ} (hσ : σ=1 ∨ σ= -1) (ha : a∈arctanGeneral u)
    (hb : b∈arctanGeneral v) (hd : 1-σ*u*v≠0) : a+σ*b∈arctanGeneral ((u+σ*v)/(1-σ*u*v)) := by
  obtain ⟨ca, ta⟩ := ha
  obtain ⟨cb, tb⟩ := hb
  rw [Complex.tan_eq_sin_div_cos, div_eq_iff ca] at ta
  rw [Complex.tan_eq_sin_div_cos, div_eq_iff cb] at tb
  have hc : Complex.cos (a+σ*b) = Complex.cos a*Complex.cos b*(1-σ*u*v) := by
    rcases hσ with rfl | rfl
    · rw [one_mul, Complex.cos_add, ta, tb]; ring
    · rw [neg_one_mul, ← sub_eq_add_neg, Complex.cos_sub, ta, tb]; ring
  have hs : Complex.sin (a+σ*b) = Complex.cos a*Complex.cos b*(u+σ*v) := by
    rcases hσ with rfl | rfl
    · rw [one_mul, Complex.sin_add, ta, tb]; ring
    · rw [neg_one_mul, ← sub_eq_add_neg, Complex.sin_sub, ta, tb]; ring
  have hne : Complex.cos (a+σ*b) ≠ 0 := by rw [hc]; exact mul_ne_zero (mul_ne_zero ca cb) hd
  refine ⟨hne, ?_⟩
  rw [Complex.tan_eq_sin_div_cos, hs, hc]
  field_simp

/-- DLMF 4.24.E15: arctan general add. -/
@[dlmf 4.24.E15]
theorem arctan_general_add (u v σ : ℂ) (hσ : σ=1 ∨ σ= -1)
    (hu : u≠I ∧ u≠ -I) (hv : v≠I ∧ v≠ -I) (hd : 1-σ*u*v≠0) :
    inverseTrigSum (arctanGeneral u) (arctanGeneral v) σ=arctanGeneral ((u+σ*v)/(1-σ*u*v)) := by
  ext w
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact trigR4_tan_add_mem hσ ha hb hd
  · rintro ⟨cw, tw⟩
    have ha := trigR4_arctan_mem hu.1 hu.2
    set a := Complex.arctan u
    obtain ⟨ca, ta⟩ := ha
    have hu2 := trigR4_one_add_sq_ne hu.1 hu.2
    have hσ2 : σ*σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
    rw [Complex.tan_eq_sin_div_cos, div_eq_iff ca] at ta
    rw [Complex.tan_eq_sin_div_cos, div_eq_iff cw] at tw
    set t := (u+σ*v)/(1-σ*u*v) with ht
    have ht' : t*(1-σ*u*v) = u+σ*v := by rw [ht, div_mul_cancel₀ _ hd]
    clear_value t a
    have h1 : 1+t*u ≠ 0 := by
      intro h0
      apply hu2
      linear_combination (1-σ*u*v)*h0 - u*ht'
    refine ⟨a, ⟨ca, by rw [Complex.tan_eq_sin_div_cos, div_eq_iff ca]; exact ta⟩, σ*(w-a), ⟨?_, ?_⟩, ?_⟩
    · have hc : Complex.cos (σ*(w-a)) = Complex.cos w*Complex.cos a*(1+t*u) := by
        rcases hσ with rfl | rfl
        · rw [one_mul, Complex.cos_sub, ta, tw]; ring
        · rw [neg_one_mul, Complex.cos_neg, Complex.cos_sub, ta, tw]; ring
      rw [hc]; exact mul_ne_zero (mul_ne_zero cw ca) h1
    · have hc : Complex.cos (σ*(w-a)) = Complex.cos w*Complex.cos a*(1+t*u) := by
        rcases hσ with rfl | rfl
        · rw [one_mul, Complex.cos_sub, ta, tw]; ring
        · rw [neg_one_mul, Complex.cos_neg, Complex.cos_sub, ta, tw]; ring
      have hs : Complex.sin (σ*(w-a)) = σ*(Complex.cos w*Complex.cos a*(t-u)) := by
        rcases hσ with rfl | rfl
        · rw [one_mul, Complex.sin_sub, ta, tw]; ring
        · rw [neg_one_mul, Complex.sin_neg, Complex.sin_sub, ta, tw]; ring
      rw [Complex.tan_eq_sin_div_cos, hs, hc, div_eq_iff (mul_ne_zero (mul_ne_zero cw ca) h1)]
      have : σ*(t-u) = v*(1+t*u) := by
        linear_combination σ*ht' + (t*u*v+v)*hσ2
      linear_combination Complex.cos w*Complex.cos a*this
    · rw [← mul_assoc, hσ2]; ring

/-- Mixed addition with consistent inverse and square-root branches. -/
@[dlmf 4.24.E16]
theorem arcsin_arccos_general_add (u v a b σ : ℂ) (hσ : σ=1 ∨ σ= -1)
    (ha : a∈arcsinGeneral u) (hb : b∈arccosGeneral v) :
    (Complex.cos a)^2=1-u^2 ∧ (Complex.sin b)^2=1-v^2 ∧
    a+σ*b∈arcsinGeneral (u*v+σ*Complex.cos a*Complex.sin b) ∧
    a+σ*b∈arccosGeneral (v*Complex.cos a-σ*u*Complex.sin b) := by
  simp only [arcsinGeneral,arccosGeneral,mem_setOf_eq] at ha hb ⊢
  rcases hσ with rfl | rfl <;>
    simp_all [Complex.cos_sq',Complex.sin_sq,Complex.sin_add,Complex.cos_add,
      Complex.sin_neg,Complex.cos_neg,mul_comm,mul_left_comm,mul_assoc]

/-- For a nonzero value, general arctangents and general arccotangents of the reciprocal agree. -/
lemma trigR4_arctanGeneral_eq_arccotGeneral {x : ℂ} (hx : x≠0) :
    arctanGeneral x=arccotGeneral x⁻¹ := by
  ext w
  simp only [arctanGeneral, arccotGeneral, Set.mem_setOf_eq, Complex.tan_eq_sin_div_cos,
    Complex.cot_eq_cos_div_sin]
  constructor
  · rintro ⟨hc, ht⟩
    have hs : Complex.sin w = x*Complex.cos w := by rw [← ht]; field_simp
    have hs0 : Complex.sin w ≠ 0 := by rw [hs]; exact mul_ne_zero hx hc
    exact ⟨hs0, by rw [hs]; field_simp⟩
  · rintro ⟨hs, ht⟩
    have hc : Complex.cos w = x⁻¹*Complex.sin w := by rw [← ht]; field_simp
    have hc0 : Complex.cos w ≠ 0 := by rw [hc]; exact mul_ne_zero (inv_ne_zero hx) hs
    exact ⟨hc0, by rw [hc]; field_simp⟩

/-- DLMF 4.24.E17: arctan arccot general add. -/
@[dlmf 4.24.E17]
theorem arctan_arccot_general_add (u v σ : ℂ) (hσ : σ=1 ∨ σ= -1)
    (hu : u≠I ∧ u≠ -I) (hv : v≠I ∧ v≠ -I)
    (h1 : v-σ*u≠0) (h2 : u*v+σ≠0) :
    inverseTrigSum (arctanGeneral u) (arccotGeneral v) σ=arctanGeneral ((u*v+σ)/(v-σ*u)) ∧
    inverseTrigSum (arctanGeneral u) (arccotGeneral v) σ=arccotGeneral ((v-σ*u)/(u*v+σ)) := by
  have hσ2 : σ*σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have first : inverseTrigSum (arctanGeneral u) (arccotGeneral v) σ =
      arctanGeneral ((u*v+σ)/(v-σ*u)) := by
    ext w
    constructor
    · rintro ⟨a, ⟨ca, ta⟩, b, ⟨sb, tb⟩, rfl⟩
      rw [Complex.tan_eq_sin_div_cos, div_eq_iff ca] at ta
      rw [Complex.cot_eq_cos_div_sin, div_eq_iff sb] at tb
      have hc : Complex.cos (a+σ*b) = Complex.cos a*Complex.sin b*(v-σ*u) := by
        rcases hσ with rfl | rfl
        · rw [one_mul, Complex.cos_add, ta, tb]; ring
        · rw [neg_one_mul, ← sub_eq_add_neg, Complex.cos_sub, ta, tb]; ring
      have hs : Complex.sin (a+σ*b) = Complex.cos a*Complex.sin b*(u*v+σ) := by
        rcases hσ with rfl | rfl
        · rw [one_mul, Complex.sin_add, ta, tb]; ring
        · rw [neg_one_mul, ← sub_eq_add_neg, Complex.sin_sub, ta, tb]; ring
      have hne : Complex.cos (a+σ*b) ≠ 0 := by rw [hc]; exact mul_ne_zero (mul_ne_zero ca sb) h1
      refine ⟨hne, ?_⟩
      rw [Complex.tan_eq_sin_div_cos, hs, hc]
      field_simp
    · rintro ⟨cw, tw⟩
      have ha := trigR4_arctan_mem hu.1 hu.2
      set a := Complex.arctan u
      obtain ⟨ca, ta⟩ := ha
      have hu2 := trigR4_one_add_sq_ne hu.1 hu.2
      rw [Complex.tan_eq_sin_div_cos, div_eq_iff ca] at ta
      rw [Complex.tan_eq_sin_div_cos, div_eq_iff cw] at tw
      set t := (u*v+σ)/(v-σ*u) with ht
      have ht' : t*(v-σ*u) = u*v+σ := by rw [ht, div_mul_cancel₀ _ h1]
      clear_value t a
      have hsub : t-u ≠ 0 := by
        intro h0
        apply hu2
        have htu : t = u := by linear_combination h0
        rw [htu] at ht'
        linear_combination (-σ)*ht' - (u^2+1)*hσ2
      have hc : Complex.cos (σ*(w-a)) = Complex.cos w*Complex.cos a*(1+t*u) := by
        rcases hσ with rfl | rfl
        · rw [one_mul, Complex.cos_sub, ta, tw]; ring
        · rw [neg_one_mul, Complex.cos_neg, Complex.cos_sub, ta, tw]; ring
      have hs : Complex.sin (σ*(w-a)) = σ*(Complex.cos w*Complex.cos a*(t-u)) := by
        rcases hσ with rfl | rfl
        · rw [one_mul, Complex.sin_sub, ta, tw]; ring
        · rw [neg_one_mul, Complex.sin_neg, Complex.sin_sub, ta, tw]; ring
      have hσ0 : σ ≠ 0 := by rintro rfl; simp at hσ2
      have hsne : Complex.sin (σ*(w-a)) ≠ 0 := by
        rw [hs]; exact mul_ne_zero hσ0 (mul_ne_zero (mul_ne_zero cw ca) hsub)
      refine ⟨a, ⟨ca, by rw [Complex.tan_eq_sin_div_cos, div_eq_iff ca]; exact ta⟩, σ*(w-a),
        ⟨hsne, ?_⟩, ?_⟩
      · rw [Complex.cot_eq_cos_div_sin, div_eq_iff hsne, hs, hc]
        have : 1+t*u = v*(σ*(t-u)) := by linear_combination (-σ)*ht' - (1+t*u)*hσ2
        linear_combination Complex.cos w*Complex.cos a*this
      · rw [← mul_assoc, hσ2]; ring
  refine ⟨first, ?_⟩
  rw [first, trigR4_arctanGeneral_eq_arccotGeneral (div_ne_zero h2 h1), inv_div]

/-- DLMF 4.25.E1: tan continued fraction. -/
@[dlmf 4.25.E1]
theorem tan_continued_fraction {z : ℂ} (hz : Complex.cos z≠0) :
    DLMF.HasContinuedFraction (fun k => if k=0 then z else -z^2)
      (fun k => 2*k+1) (Complex.tan z) := by
  sorry

/-- DLMF 4.25.E2: tan scaled continued fraction. -/
@[dlmf 4.25.E2]
theorem tan_scaled_continued_fraction (a : ℂ) {z : ℂ} (hz : |z.re|<π/2) (ha : Complex.cos (a*z)≠0) :
    DLMF.HasContinuedFraction
      (fun k => if k=0 then a*Complex.tan z else ((k:ℂ)^2-a^2)*(Complex.tan z)^2)
      (fun k => 2*k+1) (Complex.tan (a*z)) := by
  sorry

/-- DLMF 4.25.E3: arcsin continued fraction. -/
@[dlmf 4.25.E3]
theorem arcsin_continued_fraction {z : ℂ} (hz : z∈arcsinCutPlane) :
    DLMF.HasContinuedFraction
      (fun k => if k=0 then z else -(((2*((k+1)/2)-1)*(2*((k+1)/2)):ℕ):ℂ)*z^2)
      (fun k => 2*k+1) (arcsinPrincipal z/Complex.sqrt (1-z^2)) := by
  sorry

/-- DLMF 4.25.E4: arctan continued fraction. -/
@[dlmf 4.25.E4]
theorem arctan_continued_fraction {z : ℂ} (hz : z∈arctanCutPlane) :
    DLMF.HasContinuedFraction (fun k => if k=0 then z else (k:ℂ)^2*z^2)
      (fun k => 2*k+1) (Complex.arctan z) := by
  sorry

/-- DLMF 4.25.E5: exp arccot continued fraction. -/
@[dlmf 4.25.E5]
theorem exp_arccot_continued_fraction (a : ℂ) {z : ℂ} (hz : z∈arccotCutPlane) :
    DLMF.HasContinuedFraction (fun k => if k=0 then 2*a else a^2+(k:ℂ)^2)
      (fun k => if k=0 then z-a else (2*k+1)*z) (Complex.exp (2*a*arccotPrincipal z)-1) := by
  sorry

end DLMF.Elementary
end
