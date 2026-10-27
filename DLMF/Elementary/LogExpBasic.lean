/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

/-!
# Logarithms, exponentials and powers: DLMF §§4.2–4.3

Mathlib supplies the principal logarithm with argument in `(-π,π]`. DLMF also uses a
closed principal value with two values on the negative axis. `closedLogValues` retains
both values; `generalLogValues` retains every logarithm. Thus a boundary value is never
silently identified with Mathlib's upper-side convention. Upstream declarations are
indexed in `MathlibCoverage`; only missing statements and adapters occur here.
-/

@[expose] public section

open Complex Filter Set
open scoped Topology Real
noncomputable section
namespace DLMF.Elementary

/-- Every value of the complex logarithm, as an inverse relation of `exp` (4.2.25). -/
@[dlmf 4.2.E25]
def generalLogValues (z : ℂ) : Set ℂ := {w | Complex.exp w = z}

/-- The closed principal logarithm, retaining both sides of the negative-axis cut. -/
def closedLogValues (z : ℂ) : Set ℂ :=
  {w | Complex.exp w = z ∧ |w.im| ≤ Real.pi}

/-- A specified sheet of the general logarithm (4.2.6). -/
@[dlmf 4.2.E6]
def logSheet (k : ℤ) (z : ℂ) : ℂ := Complex.log z + k * (2 * Real.pi * I)

/-- All general logarithms are the integer translates of the principal logarithm. -/
@[dlmf 4.2.E6]
theorem mem_generalLogValues_iff {z w : ℂ} (hz : z ≠ 0) :
    w ∈ generalLogValues z ↔ ∃ k : ℤ, w = logSheet k z := by
  simpa [generalLogValues, logSheet, Complex.exp_log hz] using
    (Complex.exp_eq_exp_iff_exists_int (x := w) (y := Complex.log z))

/-- The negative real axis used as the logarithm branch cut (4.2.4). -/
@[dlmf 4.2.E4]
def logBranchCut : Set ℂ := {z | z.im = 0 ∧ z.re < 0}

/-- The two closed logarithm values on the cut (4.2.7). -/
@[dlmf 4.2.E7]
theorem closedLogValues_neg {x : ℝ} (hx : x < 0) :
    closedLogValues (x : ℂ) =
      {((Real.log |x| : ℝ) : ℂ) + Real.pi * I,
       ((Real.log |x| : ℝ) : ℂ) - Real.pi * I} := by
  have hlog : Complex.log (x:ℂ)=(Real.log |x|:ℂ)+Real.pi*I := by
    apply Complex.ext <;> simp [Complex.log_re,Complex.log_im,Complex.norm_real,Complex.arg_ofReal_of_neg hx]
  ext w
  constructor
  · rintro ⟨hw,hs⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    have hb := abs_le.mp hs
    by_cases hlow : w.im = -Real.pi
    · right
      have he : Complex.exp (w+2*Real.pi*I)=(x:ℂ) := by
        rw [Complex.exp_add,Complex.exp_two_pi_mul_I,hw,mul_one]
      have hl : Complex.log (x:ℂ)=w+2*Real.pi*I := by
        rw [← he]
        apply Complex.log_exp <;>
          norm_num [hlow,Complex.mul_im,Complex.mul_re] <;> linarith [Real.pi_pos]
      rw [hlog] at hl
      linear_combination -hl
    · left
      have hl := Complex.log_exp (lt_of_le_of_ne hb.1 (Ne.symm hlow)) hb.2
      rw [hw,hlog] at hl
      exact hl.symm
  · simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    rintro (rfl|rfl)
    · constructor
      · rw [Complex.exp_add,← Complex.ofReal_exp,Real.exp_log (abs_pos.mpr hx.ne),Complex.exp_pi_mul_I]
        simp [abs_of_neg hx]
      · simp [Complex.mul_im,abs_of_pos Real.pi_pos]
    · constructor
      · rw [Complex.exp_sub,← Complex.ofReal_exp,Real.exp_log (abs_pos.mpr hx.ne),Complex.exp_pi_mul_I]
        simp [abs_of_neg hx]
      · simp [Complex.mul_im,abs_of_pos Real.pi_pos]

/-- Real part of an absolutely continuous complex path. -/
lemma logR4_ac_re {f : ℝ → ℂ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => (f t).re) a b :=
  (Complex.reCLM.lipschitzWith).comp_absolutelyContinuousOnInterval hf

/-- Imaginary part of an absolutely continuous complex path. -/
lemma logR4_ac_im {f : ℝ → ℂ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => (f t).im) a b :=
  (Complex.imCLM.lipschitzWith).comp_absolutelyContinuousOnInterval hf

/-- A complex path whose real and imaginary parts have derivatives has the assembled derivative. -/
lemma logR4_hasDerivAt_of_re_im {f : ℝ → ℂ} {x r s : ℝ}
    (hr : HasDerivAt (fun t => (f t).re) r x) (hs : HasDerivAt (fun t => (f t).im) s x) :
    HasDerivAt f ((r:ℂ) + (s:ℂ)*I) x := by
  have h := hr.ofReal_comp.add (hs.ofReal_comp.mul_const I)
  convert h using 1
  ext1 t; simp only [Pi.add_apply]; exact (Complex.re_add_im (f t)).symm

/-- Absolutely continuous complex paths are differentiable almost everywhere, with
derivative assembled from the real and imaginary parts. -/
lemma logR4_ae_hasDerivAt {f : ℝ → ℂ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f (deriv f x) x ∧
      deriv f x = ((deriv (fun t : ℝ => (f t).re) x : ℝ) : ℂ) +
        ((deriv (fun t : ℝ => (f t).im) x : ℝ) : ℂ)*I := by
  filter_upwards [(logR4_ac_re hf).ae_differentiableAt, (logR4_ac_im hf).ae_differentiableAt]
    with x h1 h2 hx
  have h := logR4_hasDerivAt_of_re_im (h1 hx).hasDerivAt (h2 hx).hasDerivAt
  exact ⟨h.differentiableAt.hasDerivAt, h.deriv⟩

/-- Complexification preserves interval integrability. -/
lemma logR4_ii_ofReal {g : ℝ → ℝ} {a b : ℝ} (h : IntervalIntegrable g MeasureTheory.volume a b) :
    IntervalIntegrable (fun x => (g x : ℂ)) MeasureTheory.volume a b := ⟨h.1.ofReal, h.2.ofReal⟩

/-- The derivative of an absolutely continuous complex path is interval integrable. -/
lemma logR4_intervalIntegrable_deriv {f : ℝ → ℂ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) : IntervalIntegrable (deriv f) MeasureTheory.volume a b := by
  have h1 := (logR4_ac_re hf).intervalIntegrable_deriv
  have h2 := (logR4_ac_im hf).intervalIntegrable_deriv
  refine ((logR4_ii_ofReal h1).add ((logR4_ii_ofReal h2).mul_const I)).congr_ae ?_
  have := logR4_ae_hasDerivAt hf
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [this] with x hx hx'
  exact (hx (Set.uIoc_subset_uIcc hx')).2.symm

/-- Fundamental theorem of calculus for absolutely continuous complex paths. -/
lemma logR4_integral_deriv_eq_sub {f : ℝ → ℂ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) : ∫ x in a..b, deriv f x = f b - f a := by
  have h1 := (logR4_ac_re hf).intervalIntegrable_deriv
  have h2 := (logR4_ac_im hf).intervalIntegrable_deriv
  have hae : ∀ᵐ x, x ∈ Set.uIoc a b → deriv f x =
      ((deriv (fun t : ℝ => (f t).re) x : ℝ) : ℂ) + ((deriv (fun t : ℝ => (f t).im) x : ℝ) : ℂ)*I := by
    filter_upwards [logR4_ae_hasDerivAt hf] with x hx hx'
    exact (hx (Set.uIoc_subset_uIcc hx')).2
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_add (logR4_ii_ofReal h1)
    ((logR4_ii_ofReal h2).mul_const I), intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal, (logR4_ac_re hf).integral_deriv_eq_sub,
    (logR4_ac_im hf).integral_deriv_eq_sub]
  push_cast
  rw [← Complex.re_add_im (f b), ← Complex.re_add_im (f a)]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.add_im, Complex.mul_im]
  push_cast; ring

/-- A function `C¹` near a compact set is Lipschitz on it. -/
lemma logR4_lipschitzOnWith_of_compact {F : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K)
    (hF : ∀ w ∈ K, ContDiffAt ℝ 1 F w) : ∃ L, LipschitzOnWith L F K := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
  intro w hw
  obtain ⟨L, t, ht, hL⟩ := (hF w hw).exists_lipschitzOnWith
  exact ⟨L, t, mem_nhdsWithin_of_mem_nhds ht, hL⟩

/-- Composition of an absolutely continuous path with a function `C¹` along its image. -/
lemma logR4_ac_comp {F : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hF : ∀ t ∈ uIcc a b, ContDiffAt ℝ 1 F (γ t)) :
    AbsolutelyContinuousOnInterval (F ∘ γ) a b := by
  have hK : IsCompact (γ '' uIcc a b) := isCompact_uIcc.image_of_continuousOn hγ.continuousOn
  obtain ⟨L, hL⟩ := logR4_lipschitzOnWith_of_compact hK (by
    rintro _ ⟨t, ht, rfl⟩; exact hF t ht)
  exact hL.comp_absolutelyContinuousOnInterval (mapsTo_image _ _) hγ

/-- The principal logarithm is the integral of `dt/t` along any absolutely
continuous path in the slit plane from `1` to `z` (4.2.2). -/
@[dlmf 4.2.E2]
theorem log_eq_path_integral {z : ℂ} (γ : ℝ → ℂ)
    (hγ : AbsolutelyContinuousOnInterval γ 0 1)
    (hs : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ Complex.slitPlane)
    (h0 : γ 0 = 1) (h1 : γ 1 = z) :
    Complex.log z = ∫ t in (0 : ℝ)..1, deriv γ t / γ t := by
  have hs' : ∀ t ∈ uIcc (0:ℝ) 1, γ t ∈ Complex.slitPlane := by
    rw [uIcc_of_le zero_le_one]; exact hs
  have hac := logR4_ac_comp hγ (F := Complex.log) (fun t ht =>
    (Complex.contDiffAt_log (hs' t ht)).restrict_scalars ℝ |>.of_le le_top)
  have hft := logR4_integral_deriv_eq_sub hac
  simp only [Function.comp, h0, h1, Complex.log_one, sub_zero] at hft
  rw [← hft]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [logR4_ae_hasDerivAt hγ] with x hx hx'
  have hxi := Set.uIoc_subset_uIcc hx'
  show deriv (fun t => Complex.log (γ t)) x = _
  exact ((hx hxi).1.clog_real (hs' x hxi)).deriv

/-- Indefinite integrals of interval integrable complex functions are absolutely continuous. -/
lemma logR4_ac_integral {q : ℝ → ℂ} {a b c : ℝ} (hq : IntervalIntegrable q MeasureTheory.volume a b)
    (hc : c ∈ uIcc a b) : AbsolutelyContinuousOnInterval (fun x => ∫ s in c..x, q s) a b := by
  have hre : IntervalIntegrable (fun s => (q s).re) MeasureTheory.volume a b :=
    ⟨hq.1.re, hq.2.re⟩
  have him : IntervalIntegrable (fun s => (q s).im) MeasureTheory.volume a b :=
    ⟨hq.1.im, hq.2.im⟩
  have h1 := (Complex.ofRealCLM.lipschitzWith).comp_absolutelyContinuousOnInterval
    (hre.absolutelyContinuousOnInterval_intervalIntegral hc)
  have h2 := ((Complex.ofRealCLM.lipschitzWith).comp_absolutelyContinuousOnInterval
    (him.absolutelyContinuousOnInterval_intervalIntegral hc)).const_smul I
  refine (h1.add h2).congr ?_
  intro x hx
  have hsub : uIcc c x ⊆ uIcc a b := uIcc_subset_uIcc hc hx
  have hq' := hq.mono_set hsub
  simp only [Function.comp, Pi.add_apply, Complex.ofRealCLM_apply, smul_eq_mul]
  rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_ofReal,
    ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (logR4_ii_ofReal (hre.mono_set hsub))
      ((logR4_ii_ofReal (him.mono_set hsub)).const_mul I)]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [mul_comm]; exact Complex.re_add_im (q s)

/-- Every path integral avoiding zero gives a general logarithm (4.2.1).
Absolute continuity includes all piecewise continuously differentiable paths. -/
@[dlmf 4.2.E1]
theorem path_integral_mem_generalLogValues {z : ℂ} (γ : ℝ → ℂ)
    (hγ : AbsolutelyContinuousOnInterval γ 0 1)
    (hn : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ 0)
    (h0 : γ 0 = 1) (h1 : γ 1 = z) :
    (∫ t in (0 : ℝ)..1, deriv γ t / γ t) ∈ generalLogValues z := by
  have hn' : ∀ t ∈ uIcc (0:ℝ) 1, γ t ≠ 0 := by rw [uIcc_of_le zero_le_one]; exact hn
  have hq : IntervalIntegrable (fun t => deriv γ t / γ t) MeasureTheory.volume 0 1 := by
    simp only [div_eq_mul_inv]
    exact (logR4_intervalIntegrable_deriv hγ).mul_continuousOn
      (hγ.continuousOn.inv₀ hn')
  have h0mem : (0:ℝ) ∈ uIcc (0:ℝ) 1 := by simp
  set H : ℝ → ℂ := fun x => ∫ s in (0:ℝ)..x, deriv γ s / γ s
  have hH := logR4_ac_integral hq h0mem
  have hE : AbsolutelyContinuousOnInterval ((fun w => Complex.exp (-w)) ∘ H) 0 1 :=
    have hexp : ContDiff ℂ 1 (fun w : ℂ => Complex.exp (-w)) :=
      Complex.contDiff_exp.comp contDiff_id.neg
    logR4_ac_comp hH (fun t _ => (hexp.restrict_scalars ℝ).contDiffAt)
  have heq : (γ • ((fun w => Complex.exp (-w)) ∘ H)) = fun t => γ t * Complex.exp (-H t) := by
    funext t; simp [Function.comp]
  have hG := hγ.smul hE
  rw [heq] at hG
  have hd : ∀ᵐ x, x ∈ uIcc (0:ℝ) 1 → HasDerivAt (fun t => γ t * Complex.exp (-H t)) 0 x := by
    filter_upwards [logR4_ae_hasDerivAt hγ, hq.ae_hasDerivAt_integral] with x hx1 hx2 hx
    have dγ := (hx1 hx).1
    have dH : HasDerivAt H (deriv γ x / γ x) x := hx2 hx 0 h0mem
    have dE := dH.neg.cexp
    have := dγ.mul dE
    convert this using 1
    field_simp [hn' x hx]
    ring
  obtain ⟨C, hC⟩ := hG.const_of_ae_hasDerivAt_zero hd
  have e0 := hC 0 h0mem
  have e1 := hC 1 (by simp)
  have hH0 : H 0 = 0 := intervalIntegral.integral_same
  rw [h0, hH0, neg_zero, Complex.exp_zero, mul_one] at e0
  rw [h1, ← e0] at e1
  show Complex.exp (H 1) = z
  have := congrArg (fun w => w * Complex.exp (H 1)) e1
  simp only [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one,
    one_mul] at this
  exact this.symm

/-- Conversely every logarithm value is attained by a path integral (4.2.1). -/
@[dlmf 4.2.E1]
theorem generalLogValues_eq_pathIntegrals (z : ℂ) :
    generalLogValues z = {w | ∃ γ : ℝ → ℂ,
      AbsolutelyContinuousOnInterval γ 0 1 ∧ γ 0 = 1 ∧ γ 1 = z ∧
      (∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ 0) ∧
      w = ∫ t in (0 : ℝ)..1, deriv γ t / γ t} := by
  ext w
  constructor
  · intro hw
    change Complex.exp w = z at hw
    have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (t*w)) (w*Complex.exp (t*w)) t := by
      intro t
      have := ((hasDerivAt_id (t:ℂ)).mul_const w).cexp.comp_ofReal
      simpa [mul_comm] using this
    refine ⟨fun t : ℝ => Complex.exp (t*w), ?_, by simp, by simpa using hw,
      fun t _ => Complex.exp_ne_zero _, ?_⟩
    · apply ContDiffOn.absolutelyContinuousOnInterval
      have h1 : ContDiff ℂ 1 Complex.exp := Complex.contDiff_exp
      have h2 : ContDiff ℝ 1 (fun t : ℝ => (t:ℂ)*w) :=
        (Complex.ofRealCLM.contDiff).mul contDiff_const
      exact ((h1.restrict_scalars ℝ).comp h2).contDiffOn
    · have : ∀ t : ℝ, deriv (fun t : ℝ => Complex.exp (t*w)) t / Complex.exp (t*w) = w := by
        intro t; rw [(hd t).deriv]; field_simp [Complex.exp_ne_zero]
      simp only [this, intervalIntegral.integral_const, sub_zero, one_smul]
  · rintro ⟨γ, hac, h0, h1, hn, rfl⟩
    exact path_integral_mem_generalLogValues γ hac hn h0 h1

/-- The only zero of the principal logarithm on its nonzero domain (4.2(i), prose). -/
theorem log_eq_zero_iff {z : ℂ} (hz : z ≠ 0) : Complex.log z = 0 ↔ z = 1 := by
  constructor
  · intro h
    simpa [h] using (Complex.exp_log hz).symm
  · rintro rfl; exact Complex.log_one

/-- Complex logarithm to an arbitrary base, using principal logarithms (4.2.8). -/
@[dlmf 4.2.E8]
def complexLogb (a z : ℂ) : ℂ := Complex.log z / Complex.log a

/-- Complex change of logarithm base; both bases are nonzero and different from one. -/
@[dlmf 4.2.E9]
theorem complexLogb_change_base {a b z : ℂ}
    (ha : a ≠ 0) (ha1 : a ≠ 1) (hb : b ≠ 0) (hb1 : b ≠ 1) :
    complexLogb a z = complexLogb b z / complexLogb b a := by
  have hb' : Complex.log b ≠ 0 := by simpa [log_eq_zero_iff hb] using hb1
  simp only [complexLogb]
  field_simp

/-- Reciprocal change of base (4.2.10). -/
@[dlmf 4.2.E10]
theorem complexLogb_reciprocal (a b : ℂ) :
    complexLogb a b = 1 / complexLogb b a := by
  simp [complexLogb, div_div]

/-- Natural logarithms have base `exp 1` (4.2.14). -/
@[dlmf 4.2.E14]
theorem complexLogb_exp_one (z : ℂ) : complexLogb (Complex.exp 1) z = Complex.log z := by
  rw [complexLogb, Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]
  simp

/-- Common logarithms as a multiple of the natural logarithm (4.2.15). -/
@[dlmf 4.2.E15]
theorem complexLogb_ten (z : ℂ) :
    complexLogb 10 z = Complex.log z / Complex.log 10 ∧
    complexLogb 10 z = complexLogb 10 (Complex.exp 1) * Complex.log z := by
  rw [complexLogb, complexLogb, Complex.log_exp (by simp [Real.pi_pos])
    (by simp [Real.pi_pos.le])]
  constructor <;> ring

/-- Recovery of the natural logarithm from the common logarithm (4.2.16). -/
@[dlmf 4.2.E16]
theorem log_eq_log_ten_mul_logb (z : ℂ) :
    Complex.log z = Complex.log 10 * complexLogb 10 z := by
  have h : Complex.log (10 : ℂ) ≠ 0 := by
    intro h; have := (log_eq_zero_iff (by norm_num : (10 : ℂ) ≠ 0)).mp h; norm_num at this
  simp only [complexLogb]
  field_simp

/-- General powers, retaining all sheets of the base logarithm (4.2.26). -/
@[dlmf 4.2.E26]
def generalPowerValues (z a : ℂ) : Set ℂ :=
  {w | ∃ l ∈ generalLogValues z, w = Complex.exp (a * l)}

/-- Closed principal powers, retaining the two cut values. -/
def closedPowerValues (z a : ℂ) : Set ℂ :=
  {w | ∃ l ∈ closedLogValues z, w = Complex.exp (a * l)}

/-- Magnitude of a power on any logarithm sheet; this includes both closed cut values. -/
@[dlmf 4.2.E29]
theorem norm_power_of_logValue {z l : ℂ} (hz : z ≠ 0) (hl : l ∈ generalLogValues z)
    (a : ℂ) :
    ‖Complex.exp (a * l)‖ = ‖z‖ ^ a.re * Real.exp (-a.im * l.im) := by
  have hr : l.re = Real.log ‖z‖ := by
    simpa only [Complex.norm_exp, Real.log_exp] using
      congrArg (fun w : ℂ => Real.log ‖w‖) (show Complex.exp l = z from hl)
  rw [Complex.norm_exp, Complex.mul_re, hr,
    Real.rpow_def_of_pos (norm_pos_iff.mpr hz), ← Real.exp_add]
  congr 1
  ring

/-- Unreduced phase on every logarithm sheet, with no principal argument restriction. -/
@[dlmf 4.2.E30]
theorem power_phase_of_logValue {z l : ℂ} (hz : z ≠ 0) (hl : l ∈ generalLogValues z)
    (a : ℂ) :
    Complex.exp (a * l) = (‖z‖ ^ a.re * Real.exp (-a.im * l.im) : ℝ) *
      Complex.exp ((a.re * l.im + a.im * Real.log ‖z‖) * I) := by
  have hr : l.re = Real.log ‖z‖ := by
    simpa only [Complex.norm_exp, Real.log_exp] using
      congrArg (fun w : ℂ => Real.log ‖w‖) (show Complex.exp l = z from hl)
  have he : Real.exp (a * l).re = ‖z‖ ^ a.re * Real.exp (-a.im * l.im) := by
    simpa only [Complex.norm_exp] using norm_power_of_logValue hz hl a
  calc
    Complex.exp (a * l) = Complex.exp ((a * l).re + (a * l).im * I) := by
      rw [Complex.re_add_im]
    _ = (Real.exp (a * l).re : ℂ) * Complex.exp ((a * l).im * I) := by
      rw [Complex.exp_add, Complex.ofReal_exp]
    _ = _ := by
      rw [he]
      simp only [Complex.mul_im, hr, Complex.ofReal_add, Complex.ofReal_mul]

/-- Magnitude and unreduced phase of a real power on every logarithm sheet. -/
@[dlmf 4.2.E31]
theorem real_power_of_logValue {z l : ℂ} (hz : z ≠ 0) (hl : l ∈ generalLogValues z)
    (a : ℝ) :
    ‖Complex.exp (a * l)‖ = ‖z‖ ^ a ∧
      Complex.exp (a * l) = (‖z‖ ^ a : ℝ) * Complex.exp ((a * l.im : ℝ) * I) := by
  constructor
  · simpa using norm_power_of_logValue hz hl (a : ℂ)
  · simpa using power_phase_of_logValue hz hl (a : ℂ)


/-- The unreduced phase of a power, before reduction modulo `2π` (4.2.30). -/
@[dlmf 4.2.E30]
theorem power_phase {z a : ℂ} (hz : z ≠ 0) :
    z ^ a = (‖z‖ ^ a.re * Real.exp (-a.im * z.arg) : ℝ) *
      Complex.exp ((a.re * z.arg + a.im * Real.log ‖z‖) * I) := by
  rw [Complex.cpow_def_of_ne_zero hz, mul_comm]
  simpa only [Complex.log_im] using
    power_phase_of_logValue hz (Complex.exp_log hz) a

/-- General powers of `e`, in addition to its principal power (4.2.33). -/
@[dlmf 4.2.E33]
theorem generalPowerValues_exp_one (a : ℂ) :
    generalPowerValues (Complex.exp 1) a =
      {w | ∃ k : ℤ, w = Complex.exp a * Complex.exp (2 * k * a * Real.pi * I)} := by
  have hlog1 : Complex.log (Complex.exp (1:ℂ))=1 := by
    apply Complex.log_exp <;> norm_num [Real.pi_pos,Real.pi_pos.le]
  ext w
  constructor
  · rintro ⟨l,hl,rfl⟩
    obtain ⟨k,rfl⟩ := (mem_generalLogValues_iff (Complex.exp_ne_zero 1)).mp hl
    refine ⟨k,?_⟩
    have he : a*((k:ℂ)*(2*Real.pi*I))=2*k*a*Real.pi*I := by ring
    simp only [logSheet,hlog1,mul_add,mul_one,Complex.exp_add,he]
  · rintro ⟨k,rfl⟩
    refine ⟨logSheet k (Complex.exp 1),(mem_generalLogValues_iff (Complex.exp_ne_zero 1)).mpr ⟨k,rfl⟩,?_⟩
    have he : a*((k:ℂ)*(2*Real.pi*I))=2*k*a*Real.pi*I := by ring
    simp only [logSheet,hlog1,mul_add,mul_one,Complex.exp_add,he]

/-- Inversion of the full general power relation (4.2.35). -/
@[dlmf 4.2.E35]
theorem mem_generalPowerValues_iff {z a w : ℂ} (hz : z ≠ 0) (ha : a ≠ 0)
    (hw : w ≠ 0) :
    w ∈ generalPowerValues z a ↔
      ∃ l ∈ generalLogValues w, z = Complex.exp (l / a) := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨a * l, rfl, ?_⟩
    have hdiv : a * l / a = l := by field_simp
    rw [hdiv]
    exact hl.symm
  · rintro ⟨l, hl, hzl⟩
    refine ⟨l / a, hzl.symm, ?_⟩
    have hmul : a * (l / a) = l := by field_simp
    rw [hmul]
    exact hl.symm

/-- Principal-power inversion uses exactly those logarithms whose divided imaginary
part lies in the principal strip (4.2.36); both edges are retained. -/
@[dlmf 4.2.E36]
theorem mem_closedPowerValues_iff {z a w : ℂ} (hz : z ≠ 0) (ha : a ≠ 0)
    (hw : w ≠ 0) :
    w ∈ closedPowerValues z a ↔
      ∃ l ∈ generalLogValues w, |(l / a).im| ≤ Real.pi ∧ z = Complex.exp (l / a) := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    have hdiv : a * l / a = l := by field_simp
    refine ⟨a * l, rfl, ?_, ?_⟩
    · simpa only [hdiv] using hl.2
    · rw [hdiv]; exact hl.1.symm
  · rintro ⟨l, hl, hstrip, hzl⟩
    refine ⟨l / a, ⟨hzl.symm, hstrip⟩, ?_⟩
    have hmul : a * (l / a) = l := by field_simp
    rw [hmul]
    exact hl.symm

/-- Closed square-root values at `z²` on the right half-plane (4.2.37). -/
@[dlmf 4.2.E37]
theorem sqrt_sq_closed_right {z : ℂ} (hz : z ≠ 0) (hr : 0 ≤ z.re) :
    z ∈ closedPowerValues (z ^ 2) (1 / 2) := by
  refine ⟨2 * Complex.log z, ⟨?_, ?_⟩, ?_⟩
  · simpa using (Complex.exp_nat_mul (Complex.log z) 2)
      |>.trans (by rw [Complex.exp_log hz])
  · have harg := (Complex.abs_arg_le_pi_div_two_iff).mpr hr
    have hi : (2 * Complex.log z).im = 2 * z.arg := by simp [Complex.mul_im, Complex.log_im]
    rw [hi, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  · have heq : (1 / 2 : ℂ) * (2 * Complex.log z) = Complex.log z := by ring
    rw [heq, Complex.exp_log hz]

/-- Closed square-root values at `z²` on the left half-plane (4.2.37). -/
@[dlmf 4.2.E37]
theorem sqrt_sq_closed_left {z : ℂ} (hz : z ≠ 0) (hr : z.re ≤ 0) :
    -z ∈ closedPowerValues (z ^ 2) (1 / 2) := by
  have h := sqrt_sq_closed_right (z := -z) (neg_ne_zero.mpr hz) (by simpa using neg_nonneg.mpr hr)
  simpa only [neg_sq] using h

/-- The exponential maps horizontal lines to rays (4.3(ii), mathematical prose). -/
theorem exp_horizontal_image (y : ℝ) :
    (fun x : ℝ => Complex.exp (x + y * I)) '' univ =
      {w | ∃ r : ℝ, 0 < r ∧ w = r * Complex.exp (y * I)} := by
  ext w
  constructor
  · rintro ⟨x, _, rfl⟩
    refine ⟨Real.exp x, Real.exp_pos x, ?_⟩
    change Complex.exp ((x : ℂ) + (y : ℂ) * I) = _
    rw [Complex.exp_add, Complex.ofReal_exp]
  · rintro ⟨r, hr, rfl⟩
    refine ⟨Real.log r, Set.mem_univ _, ?_⟩
    change Complex.exp ((Real.log r : ℂ) + (y : ℂ) * I) = _
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr]

/-- The exponential maps vertical lines to circles (4.3(ii), mathematical prose). -/
theorem exp_vertical_image (x : ℝ) :
    (fun y : ℝ => Complex.exp (x + y * I)) '' univ = Metric.sphere 0 (Real.exp x) := by
  ext w
  constructor
  · rintro ⟨y, _, rfl⟩
    simp only [Metric.mem_sphere, dist_zero_right, Complex.norm_exp]
    congr 1
    simp
  · intro hw
    have hn : ‖w‖ = Real.exp x := by simpa only [Metric.mem_sphere, dist_zero_right] using hw
    have hw0 : w ≠ 0 := by
      intro h; simpa [h] using hn.trans_gt (Real.exp_pos x)
    have hr : Real.log ‖w‖ = x := by rw [hn, Real.log_exp]
    refine ⟨w.arg, Set.mem_univ _, ?_⟩
    change Complex.exp ((x : ℂ) + (w.arg : ℂ) * I) = w
    calc
      Complex.exp ((x : ℂ) + (w.arg : ℂ) * I) = Complex.exp (Complex.log w) := by
        congr 1
        apply Complex.ext <;> simp [Complex.log_re, Complex.log_im, hr]
      _ = w := Complex.exp_log hw0

/-- Principal powers of `e` are the complex exponential (4.2.32). -/
@[dlmf 4.2.E32]
theorem exp_one_cpow (a : ℂ) : (Complex.exp 1) ^ a = Complex.exp a := by
  rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le]), one_mul]

/-- The general power has one value exactly for integer exponents (4.2(iv), prose).
This records the nontrivial monodromy around the origin for every other exponent. -/
theorem generalPowerValues_subsingleton_iff {z : ℂ} (hz : z ≠ 0) (a : ℂ) :
    (generalPowerValues z a).Subsingleton ↔ ∃ n : ℤ, a = n := by
  constructor
  · intro hs
    let L := Complex.log z
    let P : ℂ := 2*Real.pi*I
    have hP : P≠0 := by dsimp [P]; exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
    have hL : L∈generalLogValues z := Complex.exp_log hz
    have hLP : L+P∈generalLogValues z := by
      change Complex.exp (L+P)=z
      rw [Complex.exp_add,show Complex.exp P=1 from Complex.exp_two_pi_mul_I]
      simpa only [mul_one] using (show Complex.exp L=z from hL)
    have he := hs (show Complex.exp (a*(L+P))∈generalPowerValues z a from ⟨L+P,hLP,rfl⟩)
      (show Complex.exp (a*L)∈generalPowerValues z a from ⟨L,hL,rfl⟩)
    obtain ⟨n,hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
    refine ⟨n,?_⟩
    have hm : a*P=(n:ℂ)*P := by dsimp [P]; linear_combination hn
    exact mul_right_cancel₀ hP hm
  · rintro ⟨n,rfl⟩
    rintro u ⟨l,hl,rfl⟩ v ⟨m,hm,rfl⟩
    rw [Complex.exp_int_mul,Complex.exp_int_mul,
      show Complex.exp l=z from hl,show Complex.exp m=z from hm]

/-- Every value of a logarithm exponentiates back to its argument (4.8.10). -/
@[dlmf 4.8.E10]
theorem exp_generalLog {z l : ℂ} (hl : l ∈ generalLogValues z) : Complex.exp l = z := hl

/-- General integer powers are single-valued, including exponent zero and negative integers. -/
@[dlmf 4.2.E27]
theorem generalPowerValues_int {z : ℂ} (hz : z ≠ 0) (n : ℤ) :
    generalPowerValues z (n : ℂ) = {z ^ n} := by
  ext w
  constructor
  · rintro ⟨l, hl, rfl⟩
    simp only [Set.mem_singleton_iff]
    rw [Complex.exp_int_mul, show Complex.exp l = z from hl]
  · intro hw
    have hw' : w = z ^ n := hw
    refine ⟨Complex.log z, Complex.exp_log hz, ?_⟩
    rw [Complex.exp_int_mul, Complex.exp_log hz]
    exact hw'


end DLMF.Elementary
