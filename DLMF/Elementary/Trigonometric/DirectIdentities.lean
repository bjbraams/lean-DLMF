/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Framework
public import DLMFMathlib.NumberTheory.EulerNumbers
public import DLMFMathlib.Analysis.Complex.TrigR4SeriesExtension
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import DLMF.Gamma.IntegralRepresentations
public import TauCeti.Analysis.Contour.WorkedExamples.HalfDisc.SineIntegral
public import Mathlib.Analysis.Complex.SqrtDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Orthogonality
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Complex trigonometric identities and products

Direct trigonometric functions, elementary identities, power series, multiple-angle products and
Cartesian forms.

Source references and common attribution are retained in
`DLMF.Elementary.Trigonometric`.
This module uses results of the Tau Ceti contributors; see also `CREDITS.md`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Polynomial

open scoped Real Topology Nat

namespace DLMF.Elementary

/-- Identity under the stated parameter and domain assumptions: `Real.sqrt (1-x⁻¹^2)=Real.sqrt
(x^2-1)/x`. -/
lemma trig_sqrt_inverse {x:ℝ} (hx:1<x) :
    Real.sqrt (1-x⁻¹^2)=Real.sqrt (x^2-1)/x := by
  have hx0 : 0<x := lt_trans zero_lt_one hx
  have hs : 0<x^2-1 := by nlinarith
  have hi : x⁻¹<1 := inv_lt_one_of_one_lt₀ hx
  have hip : 0<x⁻¹ := inv_pos.mpr hx0
  have hsi : 0≤1-x⁻¹^2 := by nlinarith
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (div_nonneg (Real.sqrt_nonneg _) hx0.le)).mp
  rw [Real.sq_sqrt hsi,div_pow,Real.sq_sqrt hs.le]
  field_simp

/-- Identity under the stated parameter and domain assumptions: `‖Complex.sin z‖^2=(Real.sin
z.re)^2+(Real.sinh z.im)^2`. -/
private lemma trig_norm_sq_sin (z : ℂ) : ‖Complex.sin z‖^2=(Real.sin z.re)^2+(Real.sinh z.im)^2 := by
  rw [Complex.sq_norm]
  conv_lhs => rw [← Complex.re_add_im z,Complex.sin_add_mul_I]
  simp [Complex.normSq,← Complex.ofReal_sin,← Complex.ofReal_cos,← Complex.ofReal_sinh,← Complex.ofReal_cosh]
  linear_combination (Real.sinh z.im)^2*(Real.sin_sq_add_cos_sq z.re) + (Real.sin z.re)^2*(Real.cosh_sq_sub_sinh_sq z.im)

/-- Identity under the stated parameter and domain assumptions: `‖Complex.cos z‖^2=(Real.cos
z.re)^2+(Real.sinh z.im)^2`. -/
private lemma trig_norm_sq_cos (z : ℂ) : ‖Complex.cos z‖^2=(Real.cos z.re)^2+(Real.sinh z.im)^2 := by
  rw [Complex.sq_norm]
  conv_lhs => rw [← Complex.re_add_im z,Complex.cos_add_mul_I]
  simp [Complex.normSq,← Complex.ofReal_sin,← Complex.ofReal_cos,← Complex.ofReal_sinh,← Complex.ofReal_cosh]
  linear_combination (Real.sinh z.im)^2*(Real.sin_sq_add_cos_sq z.re) + (Real.cos z.re)^2*(Real.cosh_sq_sub_sinh_sq z.im)

/-- Real sign, including zero, used in the DLMF branch and table formulas. -/
def trigRealSign (x : ℝ) : ℝ := if 0<x then 1 else if x<0 then -1 else 0

/-- Complex cosecant, totalized to zero at its poles. -/
@[dlmf 4.14.E5]
def csc (z : ℂ) : ℂ := (Complex.sin z)⁻¹

/-- Complex secant, totalized to zero at its poles. -/
@[dlmf 4.14.E6]
def sec (z : ℂ) : ℂ := (Complex.cos z)⁻¹

/-- DLMF 4.14.E7: cot eq inv tan. -/
@[dlmf 4.14.E7]
theorem cot_eq_inv_tan (z : ℂ) : Complex.cot z = (Complex.tan z)⁻¹ := by
  simp [Complex.cot,Complex.tan]

/-- DLMF 4.15.E2: cot eq neg tan add half pi. -/
@[dlmf 4.15.E2]
theorem cot_eq_neg_tan_add_half_pi (z : ℂ) : Complex.cot z = -Complex.tan (z+π/2) := by
  simp [Complex.tan,Complex.cot,Complex.sin_add_pi_div_two,Complex.cos_add_pi_div_two,div_neg]

/-- DLMF 4.15.E3: sec eq csc add half pi. -/
@[dlmf 4.15.E3]
theorem sec_eq_csc_add_half_pi (z : ℂ) : sec z = csc (z+π/2) := by
  simp [sec,csc,Complex.sin_add_pi_div_two]

/-- DLMF 4.14: meromorphic reciprocal trig. -/
@[dlmf 4.14]
theorem meromorphic_reciprocal_trig : Meromorphic csc ∧ Meromorphic sec ∧ Meromorphic Complex.cot := by
  have hs : Meromorphic Complex.sin := fun z => (Complex.differentiable_sin.analyticAt z).meromorphicAt
  have hc : Meromorphic Complex.cos := fun z => (Complex.differentiable_cos.analyticAt z).meromorphicAt
  exact ⟨hs.inv,hc.inv,hc.div hs⟩

/-- A product with a reciprocal has norm tending to infinity exactly at an isolated zero. -/
lemma trigR4_poles_aux {g h : ℂ → ℂ} {z : ℂ} (hgc : ContinuousAt g z) (hhc : ContinuousAt h z)
    (hiso : g z = 0 → ∀ᶠ w in 𝓝[≠] z, g w ≠ 0) (hh : g z = 0 → h z ≠ 0) :
    Tendsto (fun w => ‖h w * (g w)⁻¹‖) (𝓝[≠] z) atTop ↔ g z = 0 := by
  constructor
  · intro ht
    by_contra hz
    have hc : ContinuousAt (fun w => ‖h w * (g w)⁻¹‖) z :=
      (hhc.mul (hgc.inv₀ hz)).norm
    exact not_tendsto_atTop_of_tendsto_nhds (hc.tendsto.mono_left nhdsWithin_le_nhds) ht
  · intro hz
    have h0 : Tendsto (fun w => ‖g w‖) (𝓝[≠] z) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, ?_⟩
      · have := (hgc.norm).tendsto.mono_left (nhdsWithin_le_nhds (s := {z}ᶜ))
        simpa [hz] using this
      · filter_upwards [hiso hz] with w hw
        exact norm_pos_iff.mpr hw
    have hinv := tendsto_inv_nhdsGT_zero.comp h0
    have hn : Tendsto (fun w => ‖h w‖) (𝓝[≠] z) (𝓝 ‖h z‖) :=
      (hhc.norm).tendsto.mono_left nhdsWithin_le_nhds
    have := hn.pos_mul_atTop (norm_pos_iff.mpr (hh hz)) hinv
    refine this.congr' (Eventually.of_forall fun w => ?_)
    simp [norm_inv]

/-- DLMF 4.14: reciprocal trig poles. -/
@[dlmf 4.14]
theorem reciprocal_trig_poles (z : ℂ) :
    (Tendsto (fun w => ‖csc w‖) (𝓝[≠] z) atTop ↔ Complex.sin z=0) ∧
    (Tendsto (fun w => ‖sec w‖) (𝓝[≠] z) atTop ↔ Complex.cos z=0) ∧
    (Tendsto (fun w => ‖Complex.cot w‖) (𝓝[≠] z) atTop ↔ Complex.sin z=0) := by
  have hsc := Complex.sin_sq_add_cos_sq z
  have hs : Complex.sin z = 0 → ∀ᶠ w in 𝓝[≠] z, Complex.sin w ≠ 0 := by
    intro h0
    have hc : Complex.cos z ≠ 0 := by intro hc; rw [h0, hc] at hsc; norm_num at hsc
    simpa [h0] using (Complex.hasDerivAt_sin z).eventually_ne hc
  have hcz : Complex.cos z = 0 → ∀ᶠ w in 𝓝[≠] z, Complex.cos w ≠ 0 := by
    intro h0
    have hc : -Complex.sin z ≠ 0 := by
      intro hc; rw [neg_eq_zero] at hc; rw [h0, hc] at hsc; norm_num at hsc
    simpa [h0] using (Complex.hasDerivAt_cos z).eventually_ne hc
  refine ⟨?_, ?_, ?_⟩
  · simpa [csc] using trigR4_poles_aux (g := Complex.sin) (h := fun _ => 1)
      Complex.continuous_sin.continuousAt continuousAt_const hs (fun _ => one_ne_zero)
  · simpa [sec] using trigR4_poles_aux (g := Complex.cos) (h := fun _ => 1)
      Complex.continuous_cos.continuousAt continuousAt_const hcz (fun _ => one_ne_zero)
  · have := trigR4_poles_aux (g := Complex.sin) (h := Complex.cos)
      Complex.continuous_sin.continuousAt Complex.continuous_cos.continuousAt hs
      (fun h0 hc => by rw [h0, hc] at hsc; norm_num at hsc)
    simpa [Complex.cot, div_eq_mul_inv] using this

/-- DLMF 4.14: cot zeros. -/
@[dlmf 4.14]
theorem cot_zeros {z : ℂ} (hz : Complex.sin z ≠ 0) :
    Complex.cot z=0 ↔ ∃ k : ℤ,z=(2*k+1)*π/2 := by
  simp only [Complex.cot,div_eq_zero_iff,hz,or_false,Complex.cos_eq_zero_iff]

/-- DLMF 4.14: reciprocal trig nonzero. -/
@[dlmf 4.14]
theorem reciprocal_trig_nonzero {z : ℂ} (hs : Complex.sin z≠0) (hc : Complex.cos z≠0) : csc z≠0 ∧ sec z≠0 := by
  exact ⟨inv_ne_zero hs,inv_ne_zero hc⟩

/-- DLMF 4.18.E3: cos le sinc le one. -/
@[dlmf 4.18.E3]
theorem cos_le_sinc_le_one {x : ℝ} (hx : 0≤x) (hπ : x≤π) :
    Real.cos x ≤ Real.sinc x ∧ Real.sinc x≤1 := by
  refine ⟨?_,Real.sinc_le_one x⟩
  by_cases h : x<π/2
  · exact Real.cos_le_sinc (by rwa [abs_of_nonneg hx])
  · have hcos : Real.cos x≤0 := Real.cos_nonpos_of_pi_div_two_le_of_le (le_of_not_gt h) (by linarith [Real.pi_pos])
    have hsinc : 0≤Real.sinc x := by
      by_cases hx0 : x=0
      · simp [hx0]
      · rw [Real.sinc_of_ne_zero hx0]
        exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx hπ) hx
    exact hcos.trans hsinc

/-- The cubic Taylor bound gives the parabolic lower bound on the left half. -/
lemma trigR4_sin_pi_lower_half {x : ℝ} (hx : 0 < x) (h1 : x ≤ 1/2) :
    π * (x * (1 - x)) < Real.sin (π * x) := by
  have hp := Real.pi_pos
  have hp4 := Real.pi_lt_d2
  have hu : 0 < π * x := mul_pos hp hx
  have hc := Real.sin_gt_sub_cube hu
  have h6 : π * x * π ≤ 6 := by nlinarith
  have hb : (π * x)^3 / 6 ≤ π * x^2 := by
    have := mul_le_mul_of_nonneg_left h6 (sq_nonneg (π * x))
    have e1 : (π * x)^3 / 6 = (π * x)^2 * (π * x * π) / (6 * π) := by field_simp
    rw [e1, div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith

/-- Chord bound for sine on `[0, π/4]`. -/
lemma trigR4_sin_ge_chord {w : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ π/4) :
    2 * Real.sqrt 2 / π * w ≤ Real.sin w := by
  have hp := Real.pi_pos
  set t := w / (π/4) with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by rw [ht, div_le_one (by positivity)]; exact hw
  have hc := (strictConcaveOn_sin_Icc.concaveOn).2 (show (0:ℝ) ∈ Icc 0 π by simp; linarith)
    (show π/4 ∈ Icc 0 π by simp; constructor <;> linarith) (show 0 ≤ 1 - t by linarith) ht0
    (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.sin_zero, Real.sin_pi_div_four] at hc
  have he : t * (π/4) = w := by rw [ht]; field_simp
  rw [he] at hc
  have : 2 * Real.sqrt 2 / π * w = t * (Real.sqrt 2 / 2) := by rw [ht]; field_simp; ring
  linarith

/-- The parabolic upper bound for `sin (π x)`. -/
lemma trigR4_sin_pi_upper {x : ℝ} (hx : 0 < x) (h1 : x < 1) :
    Real.sin (π * x) ≤ 4 * (x * (1 - x)) := by
  have hp := Real.pi_pos
  set v := π * x - π / 2 with hv
  have hsv : Real.sin (π * x) = Real.cos v := by
    rw [hv, Real.cos_sub_pi_div_two]
  have habs : |v| ≤ π / 2 := by
    rw [abs_le]; constructor <;> nlinarith
  set w := |v| / 2 with hw
  have hw0 : 0 ≤ w := by positivity
  have hwπ : w ≤ π / 4 := by rw [hw]; linarith
  have hch := trigR4_sin_ge_chord hw0 hwπ
  have hs2 : Real.sin (v/2) ^ 2 = Real.sin w ^ 2 := by
    rw [hw]
    rcases abs_cases v with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, neg_div, Real.sin_neg, neg_sq]
  have hcos : Real.cos v = 1 - 2 * Real.sin (v/2) ^ 2 := by
    have h2 := Real.sin_sq_add_cos_sq (v/2)
    rw [show v = 2 * (v/2) by ring, Real.cos_two_mul]
    rw [show 2 * (v/2) / 2 = v/2 by ring]
    linarith
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hlow : (2 * Real.sqrt 2 / π * w)^2 ≤ Real.sin w ^ 2 := by
    have h0 : 0 ≤ 2 * Real.sqrt 2 / π * w := by positivity
    nlinarith
  have hval : (2 * Real.sqrt 2 / π * w)^2 = 2 * v^2 / π^2 := by
    rw [hw, mul_pow, div_pow, mul_pow, hsq, div_pow, sq_abs]; field_simp
  rw [hsv, hcos, hs2]
  have : 4 * (x * (1 - x)) = 1 - 4 * v^2 / π^2 := by rw [hv]; field_simp; ring
  rw [this]
  have : 2 * v^2 / π^2 ≤ Real.sin w ^ 2 := hval ▸ hlow
  have e : 4 * v^2 / π^2 = 2 * (2 * v^2 / π^2) := by ring
  rw [e]
  linarith

/-- DLMF 4.18.E4: sine parabolic bounds. -/
@[dlmf 4.18.E4]
theorem sine_parabolic_bounds {x : ℝ} (hx : 0<x) (h1 : x<1) :
    π < Real.sin (π*x)/(x*(1-x)) ∧ Real.sin (π*x)/(x*(1-x))≤4 := by
  have hd : 0 < x * (1 - x) := mul_pos hx (by linarith)
  constructor
  · rw [lt_div_iff₀ hd]
    rcases le_or_gt x (1/2) with h | h
    · exact trigR4_sin_pi_lower_half hx h
    · have := trigR4_sin_pi_lower_half (x := 1 - x) (by linarith) (by linarith)
      rw [show π * (1 - x) = π - π * x by ring, Real.sin_pi_sub] at this
      linarith [show (1 - x) * (1 - (1 - x)) = x * (1 - x) by ring]
  · rw [div_le_iff₀ hd]
    linarith [trigR4_sin_pi_upper hx h1]

/-- DLMF 4.18.E5: sinh im le norm sin le cosh im. -/
@[dlmf 4.18.E5]
theorem sinh_im_le_norm_sin_le_cosh_im (z : ℂ) :
    |Real.sinh z.im| ≤ ‖Complex.sin z‖ ∧ ‖Complex.sin z‖≤Real.cosh z.im := by
  have hn:=trig_norm_sq_sin z
  have hc:=Real.cosh_sq_sub_sinh_sq z.im
  have hs:=Real.sin_sq_add_cos_sq z.re
  have hp:=norm_nonneg (Complex.sin z)
  have hcp:=Real.cosh_pos z.im
  have ha:=abs_nonneg (Real.sinh z.im)
  have hasq:=sq_abs (Real.sinh z.im)
  constructor <;> nlinarith [sq_nonneg (Real.sin z.re),sq_nonneg (Real.cos z.re)]

/-- DLMF 4.18.E6: sinh im le norm cos le cosh im. -/
@[dlmf 4.18.E6]
theorem sinh_im_le_norm_cos_le_cosh_im (z : ℂ) :
    |Real.sinh z.im| ≤ ‖Complex.cos z‖ ∧ ‖Complex.cos z‖≤Real.cosh z.im := by
  have hn:=trig_norm_sq_cos z
  have hc:=Real.cosh_sq_sub_sinh_sq z.im
  have hs:=Real.sin_sq_add_cos_sq z.re
  have hp:=norm_nonneg (Complex.cos z)
  have hcp:=Real.cosh_pos z.im
  have ha:=abs_nonneg (Real.sinh z.im)
  have hasq:=sq_abs (Real.sinh z.im)
  constructor <;> nlinarith [sq_nonneg (Real.sin z.re),sq_nonneg (Real.cos z.re)]

/-- DLMF 4.18.E7: norm csc le csch im. -/
@[dlmf 4.18.E7]
theorem norm_csc_le_csch_im {z : ℂ} (hz : z.im≠0) :
    ‖csc z‖ ≤ (Real.sinh |z.im|)⁻¹ := by
  rw [csc,norm_inv]
  have hpos : 0 < |Real.sinh z.im| := abs_pos.mpr (Real.sinh_ne_zero.mpr hz)
  have h := (sinh_im_le_norm_sin_le_cosh_im z).1
  have habs : Real.sinh |z.im|=|Real.sinh z.im| := by
    rcases le_or_gt 0 z.im with hp|hn
    · rw [abs_of_nonneg hp,abs_of_nonneg (Real.sinh_nonneg_iff.mpr hp)]
    · rw [abs_of_neg hn,Real.sinh_neg,abs_of_neg (Real.sinh_neg_iff.mpr hn)]
  rw [habs]
  exact inv_anti₀ hpos h

/-- DLMF 4.18.E8: norm cos le cosh norm. -/
@[dlmf 4.18.E8]
theorem norm_cos_le_cosh_norm (z : ℂ) : ‖Complex.cos z‖ ≤ Real.cosh ‖z‖ := by
  apply (Complex.hasSum_cos z).norm_le_of_bounded (Real.hasSum_cosh ‖z‖)
  intro n
  simp [norm_div,norm_mul,norm_pow]

/-- DLMF 4.18.E9: norm sin le sinh norm. -/
@[dlmf 4.18.E9]
theorem norm_sin_le_sinh_norm (z : ℂ) : ‖Complex.sin z‖ ≤ Real.sinh ‖z‖ := by
  apply (Complex.hasSum_sin z).norm_le_of_bounded (Real.hasSum_sinh ‖z‖)
  intro n
  simp [norm_div,norm_mul,norm_pow]

/-- DLMF 4.18.E10: trig unit disc bounds. -/
@[dlmf 4.18.E10]
theorem trig_unit_disc_bounds {z : ℂ} (hz : ‖z‖<1) :
    ‖Complex.cos z‖<2 ∧ ‖Complex.sin z‖≤(6/5:ℝ)*‖z‖ := by
  have he := Real.exp_one_lt_d9
  have he' := Real.exp_one_gt_d9
  have hn := norm_nonneg z
  constructor
  · refine (norm_cos_le_cosh_norm z).trans_lt ?_
    have hm : Real.cosh ‖z‖ ≤ Real.cosh 1 := by
      rw [Real.cosh_le_cosh]; simp [abs_of_nonneg hn]; linarith
    refine hm.trans_lt ?_
    rw [Real.cosh_eq, Real.exp_neg]
    have : (Real.exp 1)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    linarith
  · have hs : HasSum (fun n : ℕ => ‖z‖ * (1:ℝ)^(2*n+1)/(2*n+1).factorial) (‖z‖*Real.sinh 1) := by
      simpa [div_eq_mul_inv] using (Real.hasSum_sinh 1).mul_left ‖z‖
    have hb : ‖Complex.sin z‖ ≤ ‖z‖*Real.sinh 1 := by
      apply (Complex.hasSum_sin z).norm_le_of_bounded hs
      intro n
      simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, RCLike.norm_natCast,
        one_mul, mul_one]
      apply div_le_div_of_nonneg_right _ (by positivity)
      rw [pow_succ]
      calc ‖z‖ ^ (2*n) * ‖z‖ ≤ 1 * ‖z‖ := by
            gcongr; exact pow_le_one₀ hn hz.le
        _ = ‖z‖ := one_mul _
    refine hb.trans ?_
    rw [mul_comm]
    gcongr
    rw [Real.sinh_eq, Real.exp_neg]
    have : (0.3678794 : ℝ) < (Real.exp 1)⁻¹ := by
      rw [lt_inv_comm₀ (by norm_num) (by linarith)]; linarith
    linarith

/-- The cosine has no zeros in the open disk of radius `π/2`. -/
lemma trigR4_cos_ne_zero_of_norm_lt {z : ℂ} (hz : ‖z‖ < π/2) : Complex.cos z ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp h
  have hn : ‖z‖ = |2*(k:ℝ)+1| * π / 2 := by
    rw [hk, show (2*(k:ℂ)+1)*π/2 = ((((2*k+1:ℝ))*π/2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos Real.pi_pos]
    norm_num
  have h1 : (1:ℝ) ≤ |2*(k:ℝ)+1| := by
    have : (1:ℤ) ≤ |2*k+1| := by rcases abs_cases (2*k+1) with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    exact_mod_cast this
  rw [hn] at hz
  nlinarith [Real.pi_pos]

/-- DLMF 4.19.E5: hasSum sec euler. -/
@[dlmf 4.19.E5]
theorem hasSum_sec_euler {z : ℂ} (hz : ‖z‖<π/2) :
    HasSum (fun n : ℕ => (-1:ℂ)^n*(eulerNumber (2*n):ℂ)*z^(2*n)/(2*n)!) (sec z) := by
  let c : ℕ → ℂ := fun m => if Even m then (-1:ℂ)^(m/2)*(eulerNumber m:ℂ)/(m)! else 0
  have hconv : ∀ w : ℂ, (fun m => c m * w^m) =
      fun m => if Even m then (fun n : ℕ => (-1:ℂ)^n*(eulerNumber (2*n):ℂ)*w^(2*n)/(2*n)!) (m/2)
        else 0 := by
    intro w; funext m
    by_cases hm : Even m
    · obtain ⟨k, rfl⟩ := hm
      simp only [c, show k + k = 2*k by ring, even_two_mul, ite_true,
        Nat.mul_div_cancel_left k two_pos]
      ring
    · simp [c, hm]
  have hf : DifferentiableOn ℂ sec (Metric.ball 0 (π/2)) := by
    intro w hw
    have hw' : ‖w‖ < π/2 := by simpa using hw
    exact ((Complex.differentiableAt_cos).inv (trigR4_cos_ne_zero_of_norm_lt hw')).differentiableWithinAt
  have hsmall : ∀ w : ℂ, ‖w‖ < 1/2 → HasSum (fun m => c m * w^m) (sec w) := by
    intro w hw
    rw [hconv]
    exact Complex.trigR4_hasSum_even_iff.mpr (Polynomial.hasSum_eulerNumber_sec hw)
  have h := Complex.trigR4_hasSum_of_differentiableOn_ball (by norm_num) hf hsmall hz
  rw [hconv] at h
  exact Complex.trigR4_hasSum_even_iff.mp h

/-- DLMF 4.19.E7: hasSum log sinc bernoulli. -/
@[dlmf 4.19.E7]
theorem hasSum_log_sinc_bernoulli {z : ℂ} (hz : ‖z‖<π) :
    HasSum (fun n : ℕ => ((-1:ℂ)^(n+1)*2^(2*(n+1)-1)*(bernoulli (2*(n+1)):ℂ)/((n+1)*(2*(n+1))!))*z^(2*(n+1))) (Complex.log (if z=0 then 1 else Complex.sin z/z)) := by
  sorry

/-- DLMF 4.19.E8: hasSum log cos bernoulli. -/
@[dlmf 4.19.E8]
theorem hasSum_log_cos_bernoulli {z : ℂ} (hz : ‖z‖<π/2) :
    HasSum (fun n : ℕ => ((-1:ℂ)^(n+1)*2^(2*(n+1)-1)*(2^(2*(n+1))-1)*(bernoulli (2*(n+1)):ℂ)/((n+1)*(2*(n+1))!))*z^(2*(n+1))) (Complex.log (Complex.cos z)) := by
  sorry

/-- DLMF 4.19.E9: hasSum log tan div bernoulli. -/
@[dlmf 4.19.E9]
theorem hasSum_log_tan_div_bernoulli {z : ℂ} (hz : ‖z‖<π/2) :
    HasSum (fun n : ℕ => ((-1:ℂ)^n*2^(2*(n+1))*(2^(2*(n+1)-1)-1)*(bernoulli (2*(n+1)):ℂ)/((n+1)*(2*(n+1))!))*z^(2*(n+1))) (Complex.log (if z=0 then 1 else Complex.tan z/z)) := by
  sorry

/-- DLMF 4.20.E4: hasDerivAt csc. -/
@[dlmf 4.20.E4]
theorem hasDerivAt_csc {z : ℂ} (hz : Complex.sin z≠0) :
    HasDerivAt csc (-csc z*Complex.cot z) z := by
  refine ((Complex.hasDerivAt_sin z).inv hz).congr_deriv ?_
  simp only [csc,Complex.cot,div_eq_mul_inv,inv_pow,pow_two]
  ring

/-- DLMF 4.20.E5: hasDerivAt sec. -/
@[dlmf 4.20.E5]
theorem hasDerivAt_sec {z : ℂ} (hz : Complex.cos z≠0) :
    HasDerivAt sec (sec z*Complex.tan z) z := by
  refine ((Complex.hasDerivAt_cos z).inv hz).congr_deriv ?_
  simp only [sec,Complex.tan,div_eq_mul_inv,inv_pow,pow_two]
  ring

/-- DLMF 4.20.E6: hasDerivAt cot. -/
@[dlmf 4.20.E6]
theorem hasDerivAt_cot {z : ℂ} (hz : Complex.sin z≠0) :
    HasDerivAt Complex.cot (-(csc z)^2) z := by
  have h := (Complex.hasDerivAt_cos z).div (Complex.hasDerivAt_sin z) hz
  refine h.congr_deriv ?_
  simp only [csc]
  field_simp
  linear_combination -(Complex.sin_sq_add_cos_sq z)

/-- Solutions of `f' = c f` on a preconnected open set are multiples of `exp (c z)`. -/
lemma trigR4_exp_ode {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U) {f : ℂ → ℂ} {c : ℂ}
    (hf : ∀ z∈U, HasDerivAt f (c*f z) z) : ∃ C : ℂ, ∀ z∈U, f z = C*Complex.exp (c*z) := by
  have hk : ∀ z∈U, HasDerivAt (fun z => f z*Complex.exp (-(c*z))) 0 z := by
    intro z hz
    have he : HasDerivAt (fun z => Complex.exp (-(c*z))) (Complex.exp (-(c*z))*(-c)) z := by
      have := ((hasDerivAt_id z).const_mul c).neg.cexp
      simpa using this
    have := (hf z hz).mul he
    convert this using 1; ring
  obtain ⟨C, hC⟩ := hU.exists_is_const_of_deriv_eq_zero hc
    (fun z hz => (hk z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hk z hz).deriv)
  refine ⟨C, fun z hz => ?_⟩
  have := hC z hz
  rw [← this, mul_assoc, ← Complex.exp_add]; simp

/-- On a preconnected open set, a product of analytic functions vanishes only if a factor does. -/
lemma trigR4_analytic_mul_eq_zero {U : Set ℂ} (hc : IsPreconnected U) {z₀ : ℂ} (hz₀ : z₀∈U)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U) (hU : IsOpen U)
    (h : ∀ z∈U, f z*g z=0) : (∀ z∈U, f z=0) ∨ (∀ z∈U, g z=0) := by
  have hev : (f*g) =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [hU.mem_nhds hz₀] with z hz using h z hz
  have htop : analyticOrderAt (f*g) z₀ = ⊤ := analyticOrderAt_eq_top.mpr hev
  rw [analyticOrderAt_mul (hf z₀ hz₀) (hg z₀ hz₀)] at htop
  rcases WithTop.add_eq_top.mp htop with h1 | h1
  · left
    exact fun z hz => (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hz₀
      (analyticOrderAt_eq_top.mp h1)) hz
  · right
    exact fun z hz => (hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hz₀
      (analyticOrderAt_eq_top.mp h1)) hz

/-- An analytic solution of `g' = h g` vanishing at one point vanishes identically. -/
lemma trigR4_zero_of_deriv_eq_mul {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U)
    {g h : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U) (hh : AnalyticOnNhd ℂ h U)
    (hd : ∀ z∈U, deriv g z=h z*g z) {z₀ : ℂ} (hz₀ : z₀∈U) (h0 : g z₀=0) :
    ∀ z∈U, g z=0 := by
  have hev : deriv g =ᶠ[𝓝 z₀] h*g := by
    filter_upwards [hU.mem_nhds hz₀] with z hz using hd z hz
  have h1 := (hg z₀ hz₀).analyticOrderAt_deriv_add_one
  simp only [h0, sub_zero] at h1
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul (hh z₀ hz₀) (hg z₀ hz₀)] at h1
  have htop : analyticOrderAt g z₀ = ⊤ := by
    generalize analyticOrderAt g z₀ = n at h1
    generalize analyticOrderAt h z₀ = m at h1
    cases n with
    | top => rfl
    | coe n =>
      exfalso
      cases m with
      | top => simp at h1
      | coe m =>
        have : ((m + n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) := by push_cast; exact h1
        have := Nat.cast_injective this
        omega
  exact fun z hz => (hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hz₀
    (analyticOrderAt_eq_top.mp htop)) hz

/-- DLMF 4.20.E12: trig linear ode general. -/
@[dlmf 4.20.E12]
theorem trig_linear_ode_general {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U) (hne : U.Nonempty)
    {a : ℂ} (ha : a≠0) {w : ℂ→ℂ} (hw : AnalyticOnNhd ℂ w U) (h : ∀ z∈U,deriv (deriv w) z+a^2*w z=0) :
    ∃ A B : ℂ,∀ z∈U,w z=A*Complex.cos (a*z)+B*Complex.sin (a*z) := by
  have hw' := hw.deriv
  have d0 : ∀ z∈U, HasDerivAt w (deriv w z) z := fun z hz => (hw z hz).differentiableAt.hasDerivAt
  have d1 : ∀ z∈U, HasDerivAt (deriv w) (-(a^2*w z)) z := fun z hz => by
    have := (hw' z hz).differentiableAt.hasDerivAt
    rwa [show deriv (deriv w) z = -(a^2*w z) by linear_combination h z hz] at this
  obtain ⟨C₁, hC₁⟩ := trigR4_exp_ode hU hc (f := fun z => deriv w z + I*a*w z) (c := I*a)
    (fun z hz => by
      convert (d1 z hz).add ((d0 z hz).const_mul (I*a)) using 1
      linear_combination (a^2)*(w z)*Complex.I_sq)
  obtain ⟨C₂, hC₂⟩ := trigR4_exp_ode hU hc (f := fun z => deriv w z - I*a*w z) (c := -(I*a))
    (fun z hz => by
      convert (d1 z hz).sub ((d0 z hz).const_mul (I*a)) using 1
      linear_combination (a^2)*(w z)*Complex.I_sq)
  refine ⟨(C₁-C₂)/(2*I*a), (C₁+C₂)/(2*a), fun z hz => ?_⟩
  have e1 := hC₁ z hz
  have e2 := hC₂ z hz
  have hI : I ≠ 0 := Complex.I_ne_zero
  have ex1 : Complex.exp (I*a*z) = Complex.cos (a*z) + Complex.sin (a*z)*I := by
    rw [← Complex.exp_mul_I]; ring_nf
  have ex2 : Complex.exp (-(I*a)*z) = Complex.cos (a*z) - Complex.sin (a*z)*I := by
    rw [show -(I*a)*z = -(a*z)*I by ring, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  rw [ex1] at e1; rw [ex2] at e2
  field_simp
  linear_combination e1 - e2

/-- Every point of the unit "circle" `p^2+q^2=1` is `(cos c, sin c)` for some complex `c`. -/
lemma trigR4_exists_cos_sin {p q : ℂ} (h : p^2+q^2=1) :
    ∃ c : ℂ, Complex.cos c=p ∧ Complex.sin c=q := by
  have hpq : (p+I*q)*(p-I*q) = 1 := by linear_combination h - q^2*Complex.I_sq
  have hne : p+I*q ≠ 0 := left_ne_zero_of_mul_eq_one hpq
  refine ⟨-I*Complex.log (p+I*q), ?_⟩
  have e1 : Complex.exp ((-I*Complex.log (p+I*q))*I) = p+I*q := by
    rw [show (-I*Complex.log (p+I*q))*I = -(I*I)*Complex.log (p+I*q) by ring, Complex.I_mul_I,
      neg_neg, one_mul, Complex.exp_log hne]
  have e2 : Complex.exp (-(-I*Complex.log (p+I*q))*I) = p-I*q := by
    rw [show -(-I*Complex.log (p+I*q))*I = -((-I*Complex.log (p+I*q))*I) by ring,
      Complex.exp_neg, e1]
    exact (eq_comm.mp (eq_inv_of_mul_eq_one_right hpq))
  rw [Complex.exp_mul_I] at e1
  rw [show -(-I*Complex.log (p+I*q))*I = (-(-I*Complex.log (p+I*q)))*I by ring,
    Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg] at e2
  constructor
  · linear_combination (e1 + e2)/2
  · have hI : I ≠ 0 := Complex.I_ne_zero
    have : Complex.sin (-I*Complex.log (p+I*q)) * (2*I) = q*(2*I) := by
      linear_combination (e1 - e2)
    exact mul_right_cancel₀ (mul_ne_zero two_ne_zero hI) this

/-- The energy equation has the displayed sine family and two singular constant solutions. -/
@[dlmf 4.20.E13]
theorem trig_energy_ode_general {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U) (hne : U.Nonempty)
    {a : ℂ} (ha : a≠0) {w : ℂ→ℂ} (hw : AnalyticOnNhd ℂ w U) (h : ∀ z∈U,(deriv w z)^2+a^2*(w z)^2=1) :
    (∃ c : ℂ,∀ z∈U,w z=Complex.sin (a*z+c)/a) ∨
      (∀ z∈U,w z=a⁻¹) ∨ (∀ z∈U,w z= -a⁻¹) := by
  obtain ⟨z₀, hz₀⟩ := hne
  have hw' := hw.deriv
  have hw'' := hw'.deriv
  have hprod : ∀ z∈U, deriv w z*(deriv (deriv w) z+a^2*w z)=0 := by
    intro z hz
    have d0 := (hw z hz).differentiableAt.hasDerivAt
    have d1 := (hw' z hz).differentiableAt.hasDerivAt
    have hE := (d1.pow 2).add ((d0.pow 2).const_mul (a^2))
    have hE0 : HasDerivAt (fun z => (deriv w z)^2+a^2*(w z)^2) 0 z := by
      apply (hasDerivAt_const z (1:ℂ)).congr_of_eventuallyEq
      filter_upwards [hU.mem_nhds hz] with y hy using h y hy
    have := hE.unique hE0
    simp only [Nat.cast_ofNat] at this
    linear_combination this/2
  rcases trigR4_analytic_mul_eq_zero hc hz₀ hw' (hw''.add (analyticOnNhd_const.mul hw)) hU hprod
    with h0 | h0
  · right
    obtain ⟨k, hk⟩ := hU.exists_is_const_of_deriv_eq_zero hc hw.differentiableOn
      (fun z hz => h0 z hz)
    have hk2 : (a*k-1)*(a*k+1) = 0 := by
      have := h z₀ hz₀; rw [h0 z₀ hz₀, hk z₀ hz₀] at this; linear_combination this
    rcases mul_eq_zero.mp hk2 with e | e
    · left; intro z hz; rw [hk z hz]; field_simp; linear_combination e
    · right; intro z hz; rw [hk z hz]; field_simp; linear_combination e
  · left
    obtain ⟨A, B, hAB⟩ := trig_linear_ode_general hU hc ⟨z₀, hz₀⟩ ha hw
      (fun z hz => by simpa using h0 z hz)
    have hder : ∀ z∈U, deriv w z = a*(-A*Complex.sin (a*z)+B*Complex.cos (a*z)) := by
      intro z hz
      have heq : w =ᶠ[𝓝 z] fun z => A*Complex.cos (a*z)+B*Complex.sin (a*z) := by
        filter_upwards [hU.mem_nhds hz] with y hy using hAB y hy
      rw [heq.deriv_eq]
      have := (((hasDerivAt_id z).const_mul a).ccos.const_mul A).add
        (((hasDerivAt_id z).const_mul a).csin.const_mul B)
      have e : ((fun y => A * Complex.cos (a * id y)) + fun y => B * Complex.sin (a * id y)) =
          fun z => A*Complex.cos (a*z)+B*Complex.sin (a*z) := by ext; simp
      rw [e] at this
      rw [this.deriv]; simp; ring
    have hn : (a*B)^2+(a*A)^2 = 1 := by
      have := h z₀ hz₀
      rw [hder z₀ hz₀, hAB z₀ hz₀] at this
      linear_combination this - a^2*(A^2+B^2)*Complex.sin_sq_add_cos_sq (a*z₀)
    obtain ⟨c, hc1, hc2⟩ := trigR4_exists_cos_sin hn
    refine ⟨c, fun z hz => ?_⟩
    rw [hAB z hz, Complex.sin_add, hc1, hc2]
    field_simp
    ring

/-- The Riccati equation has the displayed tangent family and two omitted constant solutions. -/
@[dlmf 4.20.E14]
theorem trig_riccati_ode_general {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U) (hne : U.Nonempty)
    {a : ℂ} (ha : a≠0) {w : ℂ→ℂ} (hw : AnalyticOnNhd ℂ w U) (h : ∀ z∈U,deriv w z-a^2*(w z)^2=1) :
    (∃ c : ℂ,∀ z∈U,Complex.cos (a*z+c)≠0 ∧ w z=Complex.tan (a*z+c)/a) ∨
      (∀ z∈U,w z=I/a) ∨ (∀ z∈U,w z= -I/a) := by
  obtain ⟨z₀, hz₀⟩ := hne
  have hI : I ≠ 0 := Complex.I_ne_zero
  have hd : ∀ z∈U, HasDerivAt w ((1-I*a*w z)*(1+I*a*w z)) z := by
    intro z hz
    have := (hw z hz).differentiableAt.hasDerivAt
    convert this using 1
    linear_combination (-(h z hz)) - a^2*(w z)^2*Complex.I_sq
  have hg1 : AnalyticOnNhd ℂ (fun z => 1-I*a*w z) U := analyticOnNhd_const.sub (analyticOnNhd_const.mul hw)
  have hg2 : AnalyticOnNhd ℂ (fun z => 1+I*a*w z) U := analyticOnNhd_const.add (analyticOnNhd_const.mul hw)
  have dg1 : ∀ z∈U, HasDerivAt (fun z => 1-I*a*w z) ((-I*a*(1+I*a*w z))*(1-I*a*w z)) z := by
    intro z hz
    convert ((hd z hz).const_mul (I*a)).const_sub 1 using 1; ring
  have dg2 : ∀ z∈U, HasDerivAt (fun z => 1+I*a*w z) ((I*a*(1-I*a*w z))*(1+I*a*w z)) z := by
    intro z hz
    convert ((hd z hz).const_mul (I*a)).const_add 1 using 1; ring
  by_cases h1 : ∃ z∈U, 1-I*a*w z = 0
  · right; right
    obtain ⟨z₁, hz₁, h1⟩ := h1
    have := trigR4_zero_of_deriv_eq_mul hU hc hg1
      ((analyticOnNhd_const.mul hg2) : AnalyticOnNhd ℂ (fun z => -I*a*(1+I*a*w z)) U)
      (fun z hz => (dg1 z hz).deriv) hz₁ h1
    intro z hz
    have e := this z hz
    field_simp
    first
      | linear_combination I*e + (a*w z)*Complex.I_sq
      | linear_combination (-I)*e - (a*w z)*Complex.I_sq
  by_cases h2 : ∃ z∈U, 1+I*a*w z = 0
  · right; left
    obtain ⟨z₁, hz₁, h2⟩ := h2
    have := trigR4_zero_of_deriv_eq_mul hU hc hg2
      ((analyticOnNhd_const.mul hg1) : AnalyticOnNhd ℂ (fun z => I*a*(1-I*a*w z)) U)
      (fun z hz => (dg2 z hz).deriv) hz₁ h2
    intro z hz
    have e := this z hz
    field_simp
    first
      | linear_combination (-I)*e + (a*w z)*Complex.I_sq
      | linear_combination I*e - (a*w z)*Complex.I_sq
  left
  push Not at h1 h2
  have dq : ∀ z∈U, HasDerivAt (fun z => (1+I*a*w z)/(1-I*a*w z))
      ((2*I*a)*((1+I*a*w z)/(1-I*a*w z))) z := by
    intro z hz
    convert (dg2 z hz).div (dg1 z hz) (h1 z hz) using 1
    field_simp
    ring
  obtain ⟨C, hC⟩ := trigR4_exp_ode hU hc dq
  have hC0 : C ≠ 0 := by
    intro h0
    have := hC z₀ hz₀
    rw [h0, zero_mul, div_eq_zero_iff] at this
    rcases this with e | e
    · exact h2 z₀ hz₀ e
    · exact h1 z₀ hz₀ e
  refine ⟨Complex.log C/(2*I), fun z hz => ?_⟩
  set θ := a*z+Complex.log C/(2*I)
  have hE : (Complex.cos θ + Complex.sin θ*I)^2 = C*Complex.exp (2*I*a*z) := by
    rw [← Complex.exp_mul_I, ← Complex.exp_nat_mul, ← Complex.exp_log hC0, ← Complex.exp_add]
    congr 1
    simp only [θ]; field_simp; ring_nf
  have key := hC z hz
  rw [← hE, div_eq_iff (h1 z hz)] at key
  have hsc := Complex.sin_sq_add_cos_sq θ
  have hu : (Complex.cos θ + Complex.sin θ*I)*(Complex.cos θ - Complex.sin θ*I) = 1 := by
    linear_combination hsc - (Complex.sin θ)^2*Complex.I_sq
  have hu0 : Complex.cos θ + Complex.sin θ*I ≠ 0 := left_ne_zero_of_mul_eq_one hu
  have main : (2*I*(Complex.cos θ + Complex.sin θ*I))*(a*w z*Complex.cos θ - Complex.sin θ) = 0 := by
    have hP1 : 1 + (Complex.cos θ + Complex.sin θ*I)^2 =
        2*Complex.cos θ*(Complex.cos θ + Complex.sin θ*I) := by
      linear_combination -hsc + (Complex.sin θ)^2*Complex.I_sq
    have hP2 : 1 - (Complex.cos θ + Complex.sin θ*I)^2 =
        -2*Complex.sin θ*I*(Complex.cos θ + Complex.sin θ*I) := by
      linear_combination -hsc + (Complex.sin θ)^2*Complex.I_sq
    linear_combination key - hP2 - I*a*w z*hP1
  have m2 := (mul_eq_zero.mp main).resolve_left (mul_ne_zero (mul_ne_zero two_ne_zero hI) hu0)
  have hcos : Complex.cos θ ≠ 0 := by
    intro h0
    rw [h0] at m2 hsc
    have : Complex.sin θ = 0 := by linear_combination -m2
    rw [this] at hsc; norm_num at hsc
  refine ⟨hcos, ?_⟩
  rw [Complex.tan_eq_sin_div_cos]
  field_simp
  first
    | linear_combination m2
    | linear_combination -m2

/-- The linear oscillator equation, with a nonzero complex frequency. -/
@[dlmf 4.20.E9]
def IsTrigLinearSolution (a : ℂ) (w : ℂ→ℂ) (U : Set ℂ) : Prop :=
  ∀ z∈U,deriv (deriv w) z+a^2*w z=0

/-- The trigonometric energy equation. -/
@[dlmf 4.20.E10]
def IsTrigEnergySolution (a : ℂ) (w : ℂ→ℂ) (U : Set ℂ) : Prop :=
  ∀ z∈U,(deriv w z)^2+a^2*(w z)^2=1

/-- The trigonometric Riccati equation, considered away from poles of solutions. -/
@[dlmf 4.20.E11]
def IsTrigRiccatiSolution (a : ℂ) (w : ℂ→ℂ) (U : Set ℂ) : Prop :=
  ∀ z∈U,deriv w z-a^2*(w z)^2=1

/-- DLMF 4.21.E1: sin add cos phase. -/
@[dlmf 4.21.E1]
theorem sin_add_cos_phase (u : ℂ) :
    Complex.sin u+Complex.cos u=(Real.sqrt 2:ℂ)*Complex.sin (u+π/4) ∧
    Complex.sin u-Complex.cos u=(Real.sqrt 2:ℂ)*Complex.sin (u-π/4) ∧
    Complex.sin u+Complex.cos u=(Real.sqrt 2:ℂ)*Complex.cos (u-π/4) ∧
    Complex.sin u-Complex.cos u= -(Real.sqrt 2:ℂ)*Complex.cos (u+π/4) := by
  have hs : Complex.sin ((Real.pi:ℂ)/4)=(Real.sqrt 2:ℂ)/2 := by exact_mod_cast Real.sin_pi_div_four
  have hc : Complex.cos ((Real.pi:ℂ)/4)=(Real.sqrt 2:ℂ)/2 := by exact_mod_cast Real.cos_pi_div_four
  have hr : (Real.sqrt 2:ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  rw [Complex.sin_add,Complex.sin_sub,Complex.cos_sub,Complex.cos_add,hs,hc]
  refine ⟨?_,?_,?_,?_⟩
  · linear_combination -((Complex.sin u+Complex.cos u)/2)*hr
  · linear_combination -((Complex.sin u-Complex.cos u)/2)*hr
  · linear_combination -((Complex.sin u+Complex.cos u)/2)*hr
  · linear_combination -((Complex.sin u-Complex.cos u)/2)*hr

/-- DLMF 4.21.E5: cot add sub. -/
@[dlmf 4.21.E5]
theorem cot_add_sub {u v : ℂ} (hu : Complex.sin u≠0) (hv : Complex.sin v≠0) :
    Complex.cot (u+v)=(Complex.cot u*Complex.cot v-1)/(Complex.cot u+Complex.cot v) ∧
    Complex.cot (u-v)=(-Complex.cot u*Complex.cot v-1)/(Complex.cot u-Complex.cot v) := by
  have hAdd (a b : ℂ) (ha : Complex.sin a≠0) (hb : Complex.sin b≠0) :
      Complex.cot (a+b)=(Complex.cot a*Complex.cot b-1)/(Complex.cot a+Complex.cot b) := by
    unfold Complex.cot
    rw [Complex.sin_add,Complex.cos_add]
    field_simp
    ring
  refine ⟨hAdd u v hu hv,?_⟩
  have hn : Complex.sin (-v)≠0 := by simpa only [Complex.sin_neg,neg_ne_zero] using hv
  simpa [Complex.cot,Complex.cos_neg,Complex.sin_neg,sub_eq_add_neg,div_neg] using hAdd u (-v) hu hn

/-- DLMF 4.21.E10: tan add sub values. -/
@[dlmf 4.21.E10]
theorem tan_add_sub_values {u v : ℂ} (hu : Complex.cos u≠0) (hv : Complex.cos v≠0) :
    Complex.tan u+Complex.tan v=Complex.sin (u+v)/(Complex.cos u*Complex.cos v) ∧
    Complex.tan u-Complex.tan v=Complex.sin (u-v)/(Complex.cos u*Complex.cos v) := by
  constructor
  · rw [Complex.tan_eq_sin_div_cos,Complex.tan_eq_sin_div_cos,Complex.sin_add]
    field_simp <;> ring
  · rw [Complex.tan_eq_sin_div_cos,Complex.tan_eq_sin_div_cos,Complex.sin_sub]
    field_simp <;> ring

/-- DLMF 4.21.E11: cot add sub values. -/
@[dlmf 4.21.E11]
theorem cot_add_sub_values {u v : ℂ} (hu : Complex.sin u≠0) (hv : Complex.sin v≠0) :
    Complex.cot u+Complex.cot v=Complex.sin (v+u)/(Complex.sin u*Complex.sin v) ∧
    Complex.cot u-Complex.cot v=Complex.sin (v-u)/(Complex.sin u*Complex.sin v) := by
  constructor
  · rw [Complex.cot,Complex.cot,Complex.sin_add]
    field_simp <;> ring
  · rw [Complex.cot,Complex.cot,Complex.sin_sub]
    field_simp <;> ring

/-- DLMF 4.21.E13: sec sq eq. -/
@[dlmf 4.21.E13]
theorem sec_sq_eq {z : ℂ} (hz : Complex.cos z≠0) : (sec z)^2=1+(Complex.tan z)^2 := by
  unfold sec Complex.tan
  field_simp
  linear_combination -(Complex.sin_sq_add_cos_sq z)

/-- DLMF 4.21.E14: csc sq eq. -/
@[dlmf 4.21.E14]
theorem csc_sq_eq {z : ℂ} (hz : Complex.sin z≠0) : (csc z)^2=1+(Complex.cot z)^2 := by
  unfold csc Complex.cot
  field_simp
  linear_combination -(Complex.sin_sq_add_cos_sq z)

/-- DLMF 4.21.E15: two sin mul sin. -/
@[dlmf 4.21.E15]
theorem two_sin_mul_sin (u v : ℂ) : 2*Complex.sin u*Complex.sin v=Complex.cos (u-v)-Complex.cos (u+v) := by
  rw [Complex.cos_sub,Complex.cos_add]
  ring

/-- DLMF 4.21.E16: two cos mul cos. -/
@[dlmf 4.21.E16]
theorem two_cos_mul_cos (u v : ℂ) : 2*Complex.cos u*Complex.cos v=Complex.cos (u-v)+Complex.cos (u+v) := by
  rw [Complex.cos_sub,Complex.cos_add]
  ring

/-- DLMF 4.21.E17: two sin mul cos. -/
@[dlmf 4.21.E17]
theorem two_sin_mul_cos (u v : ℂ) : 2*Complex.sin u*Complex.cos v=Complex.sin (u-v)+Complex.sin (u+v) := by
  rw [Complex.sin_sub,Complex.sin_add]
  ring

/-- DLMF 4.21.E18: sin sq sub sin sq. -/
@[dlmf 4.21.E18]
theorem sin_sq_sub_sin_sq (u v : ℂ) : (Complex.sin u)^2-(Complex.sin v)^2=Complex.sin (u+v)*Complex.sin (u-v) := by
  rw [Complex.sin_add,Complex.sin_sub]
  linear_combination -(Complex.sin u)^2*(Complex.sin_sq_add_cos_sq v)+
    (Complex.sin v)^2*(Complex.sin_sq_add_cos_sq u)

/-- DLMF 4.21.E19: cos sq sub cos sq. -/
@[dlmf 4.21.E19]
theorem cos_sq_sub_cos_sq (u v : ℂ) : (Complex.cos u)^2-(Complex.cos v)^2= -Complex.sin (u+v)*Complex.sin (u-v) := by
  rw [Complex.cos_sq',Complex.cos_sq']
  linear_combination -(sin_sq_sub_sin_sq u v)

/-- DLMF 4.21.E20: cos sq sub sin sq. -/
@[dlmf 4.21.E20]
theorem cos_sq_sub_sin_sq (u v : ℂ) : (Complex.cos u)^2-(Complex.sin v)^2=Complex.cos (u+v)*Complex.cos (u-v) := by
  rw [Complex.cos_add,Complex.cos_sub]
  linear_combination -(Complex.cos u)^2*(Complex.sin_sq_add_cos_sq v)+
    (Complex.sin v)^2*(Complex.sin_sq_add_cos_sq u)

/-- Squaring the principal complex square root returns its argument, including zero. -/
theorem trig_sqrt_sq (z : ℂ) : (Complex.sqrt z)^2=z := by
  rw [Complex.sqrt,← Complex.cpow_mul_nat]
  norm_num

/-- DLMF 4.21.E21: sin half roots. -/
@[dlmf 4.21.E21]
theorem sin_half_roots (z : ℂ) : Complex.sin (z/2)=Complex.sqrt ((1-Complex.cos z)/2) ∨
    Complex.sin (z/2)= -Complex.sqrt ((1-Complex.cos z)/2) := by
  apply (sq_eq_sq_iff_eq_or_eq_neg).mp
  rw [trig_sqrt_sq]
  have h := Complex.cos_two_mul_eq_one_sub (z/2)
  rw [show (2:ℂ)*(z/2)=z by ring] at h
  linear_combination h/2

/-- DLMF 4.21.E22: cos half roots. -/
@[dlmf 4.21.E22]
theorem cos_half_roots (z : ℂ) : Complex.cos (z/2)=Complex.sqrt ((1+Complex.cos z)/2) ∨
    Complex.cos (z/2)= -Complex.sqrt ((1+Complex.cos z)/2) := by
  apply (sq_eq_sq_iff_eq_or_eq_neg).mp
  rw [trig_sqrt_sq]
  have h := Complex.cos_two_mul (z/2)
  rw [show (2:ℂ)*(z/2)=z by ring] at h
  linear_combination -h/2

/-- DLMF 4.21.E23: tan half roots and ratios. -/
@[dlmf 4.21.E23]
theorem tan_half_roots_and_ratios {z : ℂ} (hs : Complex.sin z≠0) :
    (Complex.tan (z/2)=Complex.sqrt ((1-Complex.cos z)/(1+Complex.cos z)) ∨
      Complex.tan (z/2)= -Complex.sqrt ((1-Complex.cos z)/(1+Complex.cos z))) ∧
    Complex.tan (z/2)=(1-Complex.cos z)/Complex.sin z ∧
    Complex.tan (z/2)=Complex.sin z/(1+Complex.cos z) := by
  have hsin : Complex.sin z=2*Complex.sin (z/2)*Complex.cos (z/2) := by
    rw [← Complex.sin_two_mul,show (2:ℂ)*(z/2)=z by ring]
  have hcos : Complex.cos z=2*(Complex.cos (z/2))^2-1 := by
    rw [← Complex.cos_two_mul,show (2:ℂ)*(z/2)=z by ring]
  have hc : Complex.cos (z/2)≠0 := by intro h; apply hs; simp [hsin,h]
  have hp : 1+Complex.cos z≠0 := by
    rw [hcos]
    convert mul_ne_zero (two_ne_zero : (2:ℂ)≠0) (pow_ne_zero 2 hc) using 1 <;> ring
  have hcircle:=Complex.sin_sq_add_cos_sq (z/2)
  have hr1 : Complex.tan (z/2)=(1-Complex.cos z)/Complex.sin z := by
    rw [Complex.tan]
    field_simp [hc,hs]
    rw [hsin,hcos]
    linear_combination 2*Complex.cos (z/2)*hcircle
  have hr2 : Complex.tan (z/2)=Complex.sin z/(1+Complex.cos z) := by
    rw [Complex.tan]
    field_simp [hc,hp]
    rw [hsin,hcos]
    ring
  refine ⟨?_,hr1,hr2⟩
  apply (sq_eq_sq_iff_eq_or_eq_neg).mp
  rw [trig_sqrt_sq,Complex.tan]
  field_simp [hc,hp]
  rw [hcos]
  linear_combination 2*(Complex.cos (z/2))^2*hcircle

/-- DLMF 4.21.E27: sin double tan. -/
@[dlmf 4.21.E27]
theorem sin_double_tan {z : ℂ} (hc : Complex.cos z≠0) :
    Complex.sin (2*z)=2*Complex.tan z/(1+(Complex.tan z)^2) := by
  unfold Complex.tan
  rw [Complex.sin_two_mul]
  field_simp
  linear_combination (Complex.sin z)*(Complex.sin_sq_add_cos_sq z)

/-- DLMF 4.21.E28: cos double tan. -/
@[dlmf 4.21.E28]
theorem cos_double_tan {z : ℂ} (hc : Complex.cos z≠0) :
    Complex.cos (2*z)=(1-(Complex.tan z)^2)/(1+(Complex.tan z)^2) := by
  unfold Complex.tan
  rw [Complex.cos_two_mul']
  field_simp
  linear_combination ((Complex.cos z)^2-(Complex.sin z)^2)*(Complex.sin_sq_add_cos_sq z)

/-- DLMF 4.21.E29: tan double cot. -/
@[dlmf 4.21.E29]
theorem tan_double_cot {z : ℂ} (hs : Complex.sin z≠0) (hc : Complex.cos z≠0) :
    Complex.tan (2*z)=2*Complex.cot z/((Complex.cot z)^2-1) ∧
    Complex.tan (2*z)=2/(Complex.cot z-Complex.tan z) := by
  have ht : Complex.tan z≠0 := div_ne_zero hs hc
  rw [Complex.tan_two_mul,cot_eq_inv_tan]
  constructor <;> field_simp [ht] <;> ring

/-- DLMF 4.21.E32: sin quadruple. -/
@[dlmf 4.21.E32]
theorem sin_quadruple (z : ℂ) :
    Complex.sin (4*z)=8*(Complex.cos z)^3*Complex.sin z-4*Complex.cos z*Complex.sin z := by
  rw [show (4:ℂ)*z=2*(2*z) by ring,Complex.sin_two_mul,Complex.sin_two_mul,Complex.cos_two_mul]
  ring

/-- DLMF 4.21.E33: cos quadruple. -/
@[dlmf 4.21.E33]
theorem cos_quadruple (z : ℂ) :
    Complex.cos (4*z)=8*(Complex.cos z)^4-8*(Complex.cos z)^2+1 := by
  rw [show (4:ℂ)*z=2*(2*z) by ring,Complex.cos_two_mul,Complex.cos_two_mul]
  ring

/-- DLMF 4.21.E34: de moivre int. -/
@[dlmf 4.21.E34]
theorem de_moivre_int (z : ℂ) (n : ℤ) :
    Complex.cos (n*z)+I*Complex.sin (n*z)=(Complex.cos z+I*Complex.sin z)^n := by
  rw [mul_comm I,← Complex.exp_mul_I,mul_assoc,Complex.exp_int_mul]
  rw [mul_comm I,← Complex.exp_mul_I]

/-- Complex De Moivre formula with the precise principal logarithm strip convention. -/
@[dlmf 4.21]
theorem de_moivre_complex {z : ℂ} (hlo : -π<z.re) (hhi : z.re≤π) (n : ℂ) :
    Complex.cos (n*z)+I*Complex.sin (n*z)=(Complex.cos z+I*Complex.sin z)^n := by
  rw [mul_comm I,← Complex.exp_mul_I,mul_comm I,← Complex.exp_mul_I]
  rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),Complex.log_exp]
  · congr 1; ring
  · simpa using hlo
  · simpa using hhi

/-- Factorization of `x^n-y^n` over the powers of a primitive root of unity, indexed by `range n`. -/
lemma trigR4_pow_sub_pow_eq_prod_range {ζ : ℂ} {n : ℕ} (hn : 0<n) (h : IsPrimitiveRoot ζ n)
    (x y : ℂ) : x^n-y^n = ∏ k∈Finset.range n, (x-ζ^k*y) := by
  classical
  rw [h.pow_sub_pow_eq_prod_sub_mul x y hn]
  have hinj : Set.InjOn (fun k : ℕ => ζ^k) (Finset.range n : Set ℕ) := by
    intro i hi j hj hij
    exact h.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
  have himg : (Finset.range n).image (fun k : ℕ => ζ^k) = Polynomial.nthRootsFinset n (1:ℂ) := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hw
      rw [Polynomial.mem_nthRootsFinset hn]
      rw [← pow_mul, mul_comm, pow_mul, h.pow_eq_one, one_pow]
    · rw [h.card_nthRootsFinset, Finset.card_image_of_injOn hinj, Finset.card_range]
  rw [← himg, Finset.prod_image hinj]

/-- DLMF 4.21.E35: sin multiple product. -/
@[dlmf 4.21.E35]
theorem sin_multiple_product (z : ℂ) {n : ℕ} (hn : 0<n) :
    Complex.sin (n*z)=2^(n-1)*∏ k∈Finset.range n,Complex.sin (z+k*π/n) := by
  have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  set ζ := Complex.exp (2*π*I/n)
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn.ne'
  set u := Complex.exp (2*z*I)
  have hs : ∀ k : ℕ, Complex.sin (z+k*π/n) =
      Complex.exp (-(z*I)) * Complex.exp (-(π*I/n))^k * ((-1)*(1-ζ^k*u)/(2*I)) := by
    intro k
    set E := Complex.exp ((z+k*π/n)*I)
    have hE0 : E ≠ 0 := Complex.exp_ne_zero _
    have h1 : Complex.exp (-(z*I)) * Complex.exp (-(π*I/n))^k = E⁻¹ := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_neg]; congr 1; field_simp; ring
    have h2 : ζ^k*u = E^2 := by
      simp only [ζ, u, E]
      rw [← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_nat_mul]; congr 1; field_simp; ring
    have h3 : Complex.exp (-((z+k*π/n)*I)) = E⁻¹ := Complex.exp_neg _
    rw [Complex.sin, neg_mul, h3, h1, h2, show Complex.exp ((z+k*π/n)*I) = E from rfl]
    field_simp
    first
      | linear_combination (E^2 - 1)*Complex.I_sq
      | linear_combination (1 - E^2)*Complex.I_sq
      | linear_combination (2 - 2*E^2)*Complex.I_sq
      | linear_combination (2*E^2 - 2)*Complex.I_sq
  simp_rw [hs]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum,
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_range, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_range]
  have hprod : ∏ k∈Finset.range n, (1-ζ^k*u) = 1-u^n := by
    rw [← trigR4_pow_sub_pow_eq_prod_range hn hζ, one_pow]
  rw [hprod]
  obtain ⟨m, rfl⟩ : ∃ m, n = m+1 := ⟨n-1, by omega⟩
  have hS : ((∑ i ∈ Finset.range (m+1), i : ℕ) : ℂ) = (m+1)*m/2 := by
    have := Finset.sum_range_id_mul_two (m+1)
    rw [Nat.add_sub_cancel] at this
    have h' : ((∑ i ∈ Finset.range (m+1), i : ℕ) : ℂ) * 2 = (m+1)*m := by exact_mod_cast this
    linear_combination h'/2
  have hP : Complex.exp (-(π*I/((m+1:ℕ):ℂ)))^(∑ i ∈ Finset.range (m+1), i) = (-I)^m := by
    rw [← Complex.exp_nat_mul, hS]
    rw [show (m+1:ℂ)*m/2*(-(π*I/((m+1:ℕ):ℂ))) = m*(-(π/2*I)) by push_cast; field_simp,
      Complex.exp_nat_mul, show -(π/2*I) = -((π/2:ℂ)*I) by ring, Complex.exp_neg,
      Complex.exp_mul_I]
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_div, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp
  rw [hP, Nat.add_sub_cancel]
  set F := Complex.exp (((m+1:ℕ):ℂ)*z*I)
  have hF0 : F ≠ 0 := Complex.exp_ne_zero _
  have hF1 : Complex.exp (-(z*I))^(m+1) = F⁻¹ := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_neg]; congr 1; ring
  have hF2 : u^(m+1) = F^2 := by
    simp only [u, F]; rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]; congr 1; ring
  have hF3 : Complex.sin (((m+1:ℕ):ℂ)*z) = (F⁻¹ - F)*I/2 := by
    rw [Complex.sin, ← Complex.exp_neg]; simp only [F]; ring_nf
  rw [hF1, hF2, hF3, neg_pow, mul_pow, pow_succ (-1:ℂ), pow_succ I, pow_succ (2:ℂ)]
  have hm : ((-1:ℂ)^m)^2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have hIm : I^m ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  have h2m : (2:ℂ)^m ≠ 0 := pow_ne_zero _ two_ne_zero
  field_simp
  linear_combination (1-F^2)*Complex.I_sq + (1-F^2)*hm

/-- DLMF 4.21.E36: tan half substitution. -/
@[dlmf 4.21.E36]
theorem tan_half_substitution {z : ℂ} (hz : Complex.cos (z/2)≠0) :
    Complex.sin z=2*Complex.tan (z/2)/(1+(Complex.tan (z/2))^2) ∧
    Complex.cos z=(1-(Complex.tan (z/2))^2)/(1+(Complex.tan (z/2))^2) ∧
    HasDerivAt (fun w : ℂ => Complex.tan (w/2)) ((1+(Complex.tan (z/2))^2)/2) z := by
  have hsin := sin_double_tan hz
  have hcos := cos_double_tan hz
  rw [show (2:ℂ)*(z/2)=z by ring] at hsin hcos
  refine ⟨hsin,hcos,?_⟩
  have hd:=(Complex.hasDerivAt_tan hz).comp z ((hasDerivAt_id z).div_const 2)
  convert hd using 1
  · rfl
  · rw [Complex.tan]
    field_simp
    linear_combination (Complex.sin_sq_add_cos_sq (z/2))

/-- DLMF 4.21.E40: cot real imag. -/
@[dlmf 4.21.E40]
theorem cot_real_imag {z : ℂ} (hz : Complex.sin z≠0) :
    Complex.cot z=((Real.sin (2*z.re):ℂ)-I*Real.sinh (2*z.im))/
      ((Real.cosh (2*z.im):ℂ)-Real.cos (2*z.re)) := by
  obtain ⟨x, y, rfl⟩ : ∃ x y : ℝ, z = x + y*I := ⟨z.re, z.im, (Complex.re_add_im z).symm⟩
  have hre : ((x:ℂ) + y*I).re = x := by simp
  have him : ((x:ℂ) + y*I).im = y := by simp
  rw [hre, him]
  have hD : (Real.cosh (2*y):ℂ)-Real.cos (2*x) ≠ 0 := by
    rw [← Complex.ofReal_sub]
    intro h0
    have h0' : Real.cosh (2*y) - Real.cos (2*x) = 0 := by exact_mod_cast h0
    rw [Real.cosh_two_mul, Real.cos_two_mul, Real.cosh_sq] at h0'
    have h2 := Real.sin_sq_add_cos_sq x
    have hs : Real.sinh y = 0 := by nlinarith [sq_nonneg (Real.sinh y), sq_nonneg (Real.sin x)]
    have hsx : Real.sin x = 0 := by nlinarith [sq_nonneg (Real.sinh y), sq_nonneg (Real.sin x)]
    rw [Real.sinh_eq_zero] at hs
    apply hz
    rw [hs]; simp [← Complex.ofReal_sin, hsx]
  rw [Complex.cot, div_eq_div_iff hz hD]
  push_cast
  rw [Complex.sin_two_mul, Complex.cos_two_mul, Complex.sinh_two_mul, Complex.cosh_two_mul,
    Complex.cos_add_mul_I, Complex.sin_add_mul_I]
  have h1 := Complex.sin_sq_add_cos_sq (x:ℂ)
  have h2 := Complex.cosh_sq_sub_sinh_sq (y:ℂ)
  linear_combination (-(2:ℂ)*Complex.cosh y*Complex.cos x) * h1 +
    (Complex.cosh y*Complex.cos x + Complex.sinh y*I*Complex.sin x) * h2 +
    (2*Complex.cosh y*Complex.sinh y^2*Complex.cos x) * Complex.I_sq

/-- DLMF 4.21.E41: norm sin explicit. -/
@[dlmf 4.21.E41]
theorem norm_sin_explicit (z : ℂ) :
    ‖Complex.sin z‖=Real.sqrt ((Real.sin z.re)^2+(Real.sinh z.im)^2) ∧
    ‖Complex.sin z‖=Real.sqrt ((Real.cosh (2*z.im)-Real.cos (2*z.re))/2) := by
  have h : ‖Complex.sin z‖=Real.sqrt ((Real.sin z.re)^2+(Real.sinh z.im)^2) := by
    rw [← trig_norm_sq_sin,Real.sqrt_sq (norm_nonneg _)]
  refine ⟨h,?_⟩
  rw [h]
  congr 1
  rw [Real.cosh_two_mul,Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq z.re,Real.cosh_sq_sub_sinh_sq z.im]

/-- DLMF 4.21.E42: norm cos explicit. -/
@[dlmf 4.21.E42]
theorem norm_cos_explicit (z : ℂ) :
    ‖Complex.cos z‖=Real.sqrt ((Real.cos z.re)^2+(Real.sinh z.im)^2) ∧
    ‖Complex.cos z‖=Real.sqrt ((Real.cosh (2*z.im)+Real.cos (2*z.re))/2) := by
  have h : ‖Complex.cos z‖=Real.sqrt ((Real.cos z.re)^2+(Real.sinh z.im)^2) := by
    rw [← trig_norm_sq_cos,Real.sqrt_sq (norm_nonneg _)]
  refine ⟨h,?_⟩
  rw [h]
  congr 1
  rw [Real.cosh_two_mul,Real.cos_two_mul]
  nlinarith [Real.cosh_sq_sub_sinh_sq z.im]

/-- DLMF 4.21.E43: norm tan explicit. -/
@[dlmf 4.21.E43]
theorem norm_tan_explicit {z : ℂ} (hz : Complex.cos z≠0) :
    ‖Complex.tan z‖=Real.sqrt ((Real.cosh (2*z.im)-Real.cos (2*z.re))/
      (Real.cosh (2*z.im)+Real.cos (2*z.re))) := by
  have hp : 0≤(Real.cosh (2*z.im)-Real.cos (2*z.re))/2 := by
    rw [Real.cosh_two_mul,Real.cos_two_mul]
    nlinarith [Real.cosh_sq_sub_sinh_sq z.im,Real.sin_sq_add_cos_sq z.re,
      sq_nonneg (Real.sin z.re),sq_nonneg (Real.sinh z.im)]
  rw [Complex.tan,norm_div,(norm_sin_explicit z).2,(norm_cos_explicit z).2,← Real.sqrt_div hp]
  congr 1
  exact div_div_div_cancel_right₀ (two_ne_zero : (2:ℝ)≠0) _ _

/-- DLMF 4.22.E2: cos infinite product. -/
@[dlmf 4.22.E2]
theorem cos_infinite_product (z : ℂ) :
    Tendsto (fun N : ℕ => ∏ n∈Finset.range N,
      (1-4*z^2/(((2*n+1:ℕ):ℂ)^2*(π:ℂ)^2))) atTop (𝓝 (Complex.cos z)) := by
  sorry

/-- DLMF 4.22.E4: hasSum csc sq partial fraction. -/
@[dlmf 4.22.E4]
theorem hasSum_csc_sq_partial_fraction {z : ℂ} (hz : Complex.sin z≠0) :
    HasSum (fun n : ℤ => 1/(z-n*π)^2) ((csc z)^2) := by
  sorry

end DLMF.Elementary
end
