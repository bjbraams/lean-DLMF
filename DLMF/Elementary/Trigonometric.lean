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
# Trigonometric and inverse trigonometric functions (DLMF §§4.14–4.27)

Acquisition checked against NIST DLMF on 2026-10-24. Upstream results are recorded in
`MathlibCoverage`, without duplicate wrappers. This module supplies genuinely missing definitions
and statements. Admissions remain explicit. Complex inverse functions use principal logarithms
and square roots off their cuts; their two boundary values are represented separately. General
inverse values are sets, so identities between multivalued functions retain every branch.
Reciprocal functions are totalized at poles; all identities that need finite values state this.

Mathlib's full complex sine/cosine fibers and antiperiodicity provide the inverse families;
integer parity combines the two sine fibers without discarding any branch or endpoint.

The sine orthogonality API is imported from pinned TauCeti. The Bernoulli/Euler and partial-fraction
APIs are existing Mathlib-only `DLMFMathlib` developments. The general-solution and Gudermannian
statements record the necessary singular-solution and sign corrections to the displayed source.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Polynomial
open scoped Real Topology Nat
namespace DLMF.Elementary

private lemma trig_sqrt_inverse {x:ℝ} (hx:1<x) :
    Real.sqrt (1-x⁻¹^2)=Real.sqrt (x^2-1)/x := by
  have hx0 : 0<x := lt_trans zero_lt_one hx
  have hs : 0<x^2-1 := by nlinarith
  have hi : x⁻¹<1 := inv_lt_one_of_one_lt₀ hx
  have hip : 0<x⁻¹ := inv_pos.mpr hx0
  have hsi : 0≤1-x⁻¹^2 := by nlinarith
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (div_nonneg (Real.sqrt_nonneg _) hx0.le)).mp
  rw [Real.sq_sqrt hsi,div_pow,Real.sq_sqrt hs.le]
  field_simp


private lemma trig_norm_sq_sin (z : ℂ) : ‖Complex.sin z‖^2=(Real.sin z.re)^2+(Real.sinh z.im)^2 := by
  rw [Complex.sq_norm]
  conv_lhs => rw [← Complex.re_add_im z,Complex.sin_add_mul_I]
  simp [Complex.normSq,← Complex.ofReal_sin,← Complex.ofReal_cos,← Complex.ofReal_sinh,← Complex.ofReal_cosh]
  linear_combination (Real.sinh z.im)^2*(Real.sin_sq_add_cos_sq z.re) + (Real.sin z.re)^2*(Real.cosh_sq_sub_sinh_sq z.im)

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


/-! ## Principal and general inverse functions, including cut banks -/

/-- Principal complex arcsine off its cuts; its assigned cut values select one bank only. -/
@[dlmf 4.23.E19]
def arcsinPrincipal (z : ℂ) : ℂ := -I*Complex.log (Complex.sqrt (1-z^2)+I*z)

/-- Principal complex arccosine off its cuts. -/
@[dlmf 4.23.E16]
def arccosPrincipal (z : ℂ) : ℂ := π/2-arcsinPrincipal z

/-- Principal inverse cosecant, used on its cut domain with z nonzero. -/
@[dlmf 4.23.E7]
def arccscPrincipal (z : ℂ) : ℂ := arcsinPrincipal z⁻¹

/-- Principal inverse secant, used on its cut domain with z nonzero. -/
@[dlmf 4.23.E8]
def arcsecPrincipal (z : ℂ) : ℂ := arccosPrincipal z⁻¹

/-- Principal inverse cotangent off its central imaginary cut; its totalized value at zero is not a bank value. -/
@[dlmf 4.23.E9]
def arccotPrincipal (z : ℂ) : ℂ := Complex.arctan z⁻¹

/-- The open arcsine/arccosine cut plane, excluding the two branch points. -/
def arcsinCutPlane : Set ℂ := {z | z.im≠0 ∨ |z.re|<1}

/-- The open arctangent cut plane, excluding ±i. -/
def arctanCutPlane : Set ℂ := {z | z.re≠0 ∨ |z.im|<1}

/-- The reciprocal cut plane for inverse secant and cosecant. -/
def arccscCutPlane : Set ℂ := {z | z≠0 ∧ z⁻¹∈arcsinCutPlane}

/-- The central imaginary cut is deleted for inverse cotangent. -/
def arccotCutPlane : Set ℂ := {z | z≠0 ∧ z⁻¹∈arctanCutPlane}

/-- The sign of the upper bank, or of the right bank for vertical cuts. -/
def trigBankSign (upper : Bool) : ℂ := if upper then 1 else -1

/-- General arcsine values, retaining every inverse image. -/
def arcsinGeneral (z : ℂ) : Set ℂ := {w | Complex.sin w=z}

/-- General arccosine values, retaining every inverse image. -/
def arccosGeneral (z : ℂ) : Set ℂ := {w | Complex.cos w=z}

/-- General arctangent values; totalized tangent poles are excluded. -/
def arctanGeneral (z : ℂ) : Set ℂ := {w | Complex.cos w≠0 ∧ Complex.tan w=z}

/-- General inverse cosecant values, excluding poles of cosecant. -/
def arccscGeneral (z : ℂ) : Set ℂ := {w | Complex.sin w≠0 ∧ csc w=z}

/-- General inverse secant values, excluding poles of secant. -/
def arcsecGeneral (z : ℂ) : Set ℂ := {w | Complex.cos w≠0 ∧ sec w=z}

/-- General inverse cotangent values, excluding poles of cotangent. -/
def arccotGeneral (z : ℂ) : Set ℂ := {w | Complex.sin w≠0 ∧ Complex.cot w=z}

/-- A path together with a continuously continued square root starting at +1. -/
def ArcsinLift (γ r : ℝ→ℂ) (z : ℂ) : Prop :=
  ContDiffOn ℝ 1 γ (Icc 0 1) ∧ γ 0=0 ∧ γ 1=z ∧ ContinuousOn r (Icc 0 1) ∧ r 0=1 ∧
    ∀ t∈Icc 0 1,r t≠0 ∧ (r t)^2=1-(γ t)^2

/-- DLMF 4.23.E1: arcsin general integral. -/
@[dlmf 4.23.E1]
theorem arcsin_general_integral {z w : ℂ} (hzp : z≠1) (hzm : z≠ -1) :
    w∈arcsinGeneral z ↔ ∃ γ r : ℝ→ℂ,ArcsinLift γ r z ∧
      (∫ t in (0:ℝ)..1,deriv γ t/r t)=w := by
  sorry

/-- The integral from z to 1, normalized by the principal segment from zero to one. -/
@[dlmf 4.23.E2]
theorem arccos_general_integral {z w : ℂ} (hzp : z≠1) (hzm : z≠ -1) :
    w∈arccosGeneral z ↔ ∃ γ r : ℝ→ℂ,ArcsinLift γ r z ∧
      π/2-(∫ t in (0:ℝ)..1,deriv γ t/r t)=w := by
  sorry

/-- DLMF 4.23.E3: arctan general integral. -/
@[dlmf 4.23.E3]
theorem arctan_general_integral {z w : ℂ} (hzp : z≠I) (hzm : z≠ -I) :
    w∈arctanGeneral z ↔ ∃ γ : ℝ→ℂ,
      ContDiffOn ℝ 1 γ (Icc 0 1) ∧ γ 0=0 ∧ γ 1=z ∧
      (∀ t∈Icc 0 1,γ t≠I ∧ γ t≠ -I) ∧
      (∫ t in (0:ℝ)..1,deriv γ t/(1+(γ t)^2))=w := by
  sorry

private lemma trig_arctan_quotient_slit {z:ℂ} (hz:z∈arctanCutPlane) :
    (1+z*I)/(1-z*I)∈Complex.slitPlane := by
  have hre : ((1+z*I)/(1-z*I)).re=(1-z.im^2-z.re^2)/((1+z.im)^2+z.re^2) := by
    simp [Complex.div_re,Complex.normSq]
    ring
  have him : ((1+z*I)/(1-z*I)).im=(2*z.re)/((1+z.im)^2+z.re^2) := by
    simp [Complex.div_im,Complex.normSq]
    ring
  rw [Complex.mem_slitPlane_iff]
  by_cases hr:z.re≠0
  · right
    rw [him]
    have hD:0<(1+z.im)^2+z.re^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hr)
    exact div_ne_zero (mul_ne_zero two_ne_zero hr) hD.ne'
  · left
    have hr0:z.re=0 := not_ne_iff.mp hr
    have hi:|z.im|<1 := hz.resolve_left hr
    rw [hre,hr0]
    have hip:0<1+z.im := by linarith [(abs_lt.mp hi).1]
    apply div_pos
    · nlinarith [(abs_lt.mp hi).1,(abs_lt.mp hi).2]
    · positivity

private lemma trig_arctan_linear_ne {z:ℂ} (hz:z∈arctanCutPlane) :
    1+z*I≠0 ∧ 1-z*I≠0 := by
  have hgood: ¬(z.re=0 ∧ (z.im=1 ∨ z.im= -1)) := by
    rintro ⟨hr,hi⟩
    have h:|z.im|<1 := hz.resolve_left (not_ne_iff.mpr hr)
    rcases hi with hi|hi <;> simp [hi] at h
  constructor
  · intro h
    have hr:=congrArg Complex.re h
    have hi:=congrArg Complex.im h
    simp at hr hi
    exact hgood ⟨by linarith,Or.inl (by linarith)⟩
  · intro h
    have hr:=congrArg Complex.re h
    have hi:=congrArg Complex.im h
    simp at hr hi
    exact hgood ⟨by linarith,Or.inr (by linarith)⟩

private lemma trig_hasDerivAt_arctan {z:ℂ} (hz:z∈arctanCutPlane) :
    HasDerivAt Complex.arctan ((1+z^2)⁻¹) z := by
  obtain ⟨hp,hm⟩:=trig_arctan_linear_ne hz
  have hd0 := (((hasDerivAt_id z).mul_const I).const_add 1).div
    (((hasDerivAt_id z).mul_const I).const_sub 1) hm
  have hd1 := (Complex.hasDerivAt_log (trig_arctan_quotient_slit hz)).comp z hd0
  have hd:=hd1.const_mul (-I/2)
  convert hd using 1
  · rfl
  · dsimp only [id]
    have hfac:(1+z*I)*(1-z*I)=1+z^2 := by
      linear_combination -z^2*Complex.I_sq
    rw [← hfac]
    field_simp [hp,hm]
    linear_combination 2*Complex.I_sq


private lemma trig_one_add_sq_slit {z:ℂ} (hz:z∈arctanCutPlane) :
    1+z^2∈Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hr:z.re=0
  · left
    have hi:|z.im|<1 := hz.resolve_left (not_ne_iff.mpr hr)
    simp [Complex.add_re,pow_two,Complex.mul_re,hr]
    nlinarith [(abs_lt.mp hi).1,(abs_lt.mp hi).2]
  · by_cases hi:z.im=0
    · left
      simp [Complex.add_re,pow_two,Complex.mul_re,hi]
      nlinarith [sq_nonneg z.re]
    · right
      simp [Complex.add_im,pow_two,Complex.mul_im]
      convert mul_ne_zero (mul_ne_zero two_ne_zero hr) hi using 1 <;> ring

/-- DLMF 4.23.E4: arccsc general reciprocal. -/
@[dlmf 4.23.E4]
theorem arccsc_general_reciprocal {z : ℂ} (hz : z≠0) : arccscGeneral z=arcsinGeneral z⁻¹ := by
  ext w
  change (Complex.sin w≠0 ∧ (Complex.sin w)⁻¹=z) ↔ Complex.sin w=z⁻¹
  constructor
  · intro h
    have := congrArg Inv.inv h.2
    simpa using this
  · intro h
    exact ⟨by simpa [h] using inv_ne_zero hz,by simp [h]⟩


/-- DLMF 4.23.E5: arcsec general reciprocal. -/
@[dlmf 4.23.E5]
theorem arcsec_general_reciprocal {z : ℂ} (hz : z≠0) : arcsecGeneral z=arccosGeneral z⁻¹ := by
  ext w
  change (Complex.cos w≠0 ∧ (Complex.cos w)⁻¹=z) ↔ Complex.cos w=z⁻¹
  constructor
  · intro h
    have := congrArg Inv.inv h.2
    simpa using this
  · intro h
    exact ⟨by simpa [h] using inv_ne_zero hz,by simp [h]⟩


/-- DLMF 4.23.E6: arccot general reciprocal. -/
@[dlmf 4.23.E6]
theorem arccot_general_reciprocal {z : ℂ} (hz : z≠0) : arccotGeneral z=arctanGeneral z⁻¹ := by
  ext w
  change (Complex.sin w≠0 ∧ Complex.cot w=z) ↔ Complex.cos w≠0 ∧ Complex.tan w=z⁻¹
  rw [cot_eq_inv_tan]
  constructor
  · rintro ⟨hs,ht⟩
    have ht0 : Complex.tan w≠0 := by
      intro h
      apply hz
      simpa [h] using ht.symm
    refine ⟨?_,?_⟩
    · intro h; exact ht0 (by simp [Complex.tan,h])
    · simpa using congrArg Inv.inv ht
  · rintro ⟨hc,ht⟩
    refine ⟨?_,by simp [ht]⟩
    intro h
    have : (z⁻¹:ℂ)=0 := by simpa [Complex.tan,h] using ht.symm
    exact inv_ne_zero hz this


private lemma trig_arcsin_product (z:ℂ) :
    (Complex.sqrt (1-z^2)+I*z)*(Complex.sqrt (1-z^2)-I*z)=1 := by
  linear_combination trig_sqrt_sq (1-z^2) - z^2*Complex.I_sq

private lemma trig_arcsin_log_arg_ne (z:ℂ) : Complex.sqrt (1-z^2)+I*z≠0 := by
  intro h
  have hp:=trig_arcsin_product z
  rw [h,zero_mul] at hp
  exact zero_ne_one hp

private lemma trig_arcsin_log_slit (z:ℂ) : Complex.sqrt (1-z^2)+I*z∈Complex.slitPlane := by
  let r:=Complex.sqrt (1-z^2)
  change r+I*z∈Complex.slitPlane
  rw [Complex.mem_slitPlane_iff]
  by_cases hi:(r+I*z).im≠0
  · exact Or.inr hi
  · left
    have hi0:(r+I*z).im=0 := not_ne_iff.mp hi
    have hr:0≤r.re := by
      dsimp [r]
      rw [Complex.sqrt,Complex.cpow_inv_two_re]
      positivity
    have him:r.im= -z.re := by
      simp only [Complex.add_im,Complex.I_mul_im] at hi0
      linarith
    have hp:=congrArg Complex.re (trig_arcsin_product z)
    change ((r+I*z)*(r-I*z)).re=1 at hp
    simp only [Complex.mul_re,Complex.add_re,Complex.sub_re,Complex.add_im,Complex.sub_im,
      Complex.I_mul_re,Complex.I_mul_im,him] at hp
    norm_num only [Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub] at hp
    simp only [Complex.add_re,Complex.I_mul_re]
    nlinarith

private lemma trig_one_sub_sq_slit {z:ℂ} (hz:z∈arcsinCutPlane) : 1-z^2∈Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hi:z.im=0
  · left
    have hr:|z.re|<1 := hz.resolve_left (not_ne_iff.mpr hi)
    simp [pow_two,Complex.mul_re,hi]
    nlinarith [(abs_lt.mp hr).1,(abs_lt.mp hr).2]
  · by_cases hr:z.re=0
    · left
      simp [pow_two,Complex.mul_re,hr]
      nlinarith [sq_nonneg z.im]
    · right
      simp [pow_two,Complex.mul_im]
      convert neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero two_ne_zero hr) hi) using 1 <;> ring

private lemma trig_hasDerivAt_sqrt {q:ℂ} (hq:q∈Complex.slitPlane) :
    HasDerivAt Complex.sqrt ((Complex.sqrt q)⁻¹/2) q := by
  simpa only [Complex.sqrt,show (-1/2:ℂ)= -(2⁻¹:ℂ) by norm_num,Complex.cpow_neg] using
    Complex.hasDerivAt_sqrt hq

private lemma trig_hasDerivAt_arcsin {z:ℂ} (hz:z∈arcsinCutPlane) :
    HasDerivAt arcsinPrincipal (Complex.sqrt (1-z^2))⁻¹ z := by
  have hq:=trig_one_sub_sq_slit hz
  have hr:Complex.sqrt (1-z^2)≠0 := by
    intro h
    have hs:=trig_sqrt_sq (1-z^2)
    rw [h,zero_pow two_ne_zero] at hs
    exact (Complex.mem_slitPlane_iff_arg.mp hq).2 hs.symm
  have hd0:=(trig_hasDerivAt_sqrt hq).comp z (((hasDerivAt_id z).pow 2).const_sub 1)
  have hd1:=hd0.add ((hasDerivAt_id z).const_mul I)
  have hd2:=(Complex.hasDerivAt_log (trig_arcsin_log_slit z)).comp z hd1
  have hd:=hd2.const_mul (-I)
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.pow_apply,Pi.add_apply]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul]
    generalize heq : Complex.sqrt (1-z^2)=r at hr ⊢
    have hw:r+I*z≠0 := by rw [← heq]; exact trig_arcsin_log_arg_ne z
    field_simp [hr,hw]
    linear_combination r*Complex.I_sq

/-- DLMF 4.23.ii: analytic arcsin principal. -/
@[dlmf 4.23.ii]
theorem analytic_arcsin_principal : AnalyticOnNhd ℂ arcsinPrincipal arcsinCutPlane := by
  have hU:IsOpen arcsinCutPlane := by
    change IsOpen ({z:ℂ | z.im≠0}∪{z:ℂ | |z.re|<1})
    exact (isOpen_ne.preimage Complex.continuous_im).union
      (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const)
  exact (show DifferentiableOn ℂ arcsinPrincipal arcsinCutPlane from fun z hz=>
    (trig_hasDerivAt_arcsin hz).differentiableAt.differentiableWithinAt).analyticOnNhd hU


/-- DLMF 4.23.ii: analytic arccos principal. -/
@[dlmf 4.23.ii]
theorem analytic_arccos_principal : AnalyticOnNhd ℂ arccosPrincipal arcsinCutPlane := by
  intro z hz
  change AnalyticAt ℂ (fun w=>(π:ℂ)/2-arcsinPrincipal w) z
  exact analyticAt_const.sub (analytic_arcsin_principal z hz)


/-- DLMF 4.23.ii: analytic arctan principal. -/
@[dlmf 4.23.ii]
theorem analytic_arctan_principal : AnalyticOnNhd ℂ Complex.arctan arctanCutPlane := by
  have hU:IsOpen arctanCutPlane := by
    change IsOpen ({z:ℂ|z.re≠0}∪{z:ℂ | |z.im|<1})
    exact (isOpen_ne.preimage Complex.continuous_re).union
      (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)
  exact (show DifferentiableOn ℂ Complex.arctan arctanCutPlane from fun z hz=>
    (trig_hasDerivAt_arctan hz).differentiableAt.differentiableWithinAt).analyticOnNhd hU


/-- DLMF 4.23.ii: analytic arccsc principal. -/
@[dlmf 4.23.ii]
theorem analytic_arccsc_principal : AnalyticOnNhd ℂ arccscPrincipal arccscCutPlane := by
  intro z hz
  exact (analytic_arcsin_principal _ hz.2).comp (analyticAt_id.inv hz.1)


/-- DLMF 4.23.ii: analytic arcsec principal. -/
@[dlmf 4.23.ii]
theorem analytic_arcsec_principal : AnalyticOnNhd ℂ arcsecPrincipal arccscCutPlane := by
  intro z hz
  exact (analytic_arccos_principal _ hz.2).comp (analyticAt_id.inv hz.1)


/-- DLMF 4.23.ii: analytic arccot principal. -/
@[dlmf 4.23.ii]
theorem analytic_arccot_principal : AnalyticOnNhd ℂ arccotPrincipal arccotCutPlane := by
  intro z hz
  exact (analytic_arctan_principal _ hz.2).comp (analyticAt_id.inv hz.1)


open scoped ComplexOrder in
/-- DLMF 4.23.ii: inverse principal real. -/
@[dlmf 4.23.ii]
theorem inverse_principal_real {x : ℝ} (hx : x∈Icc (-1) 1) :
    arcsinPrincipal x=(Real.arcsin x:ℂ) ∧ arccosPrincipal x=(Real.arccos x:ℂ) := by
  have hs : arcsinPrincipal x=(Real.arcsin x:ℂ) := by
    have h1 : (1:ℂ) - (x:ℂ)^2 = ((1 - x^2 : ℝ) : ℂ) := by push_cast; ring
    have hnn : (0:ℂ) ≤ ((1 - x^2 : ℝ) : ℂ) := by
      rw [Complex.zero_le_real]; nlinarith [hx.1, hx.2]
    have hsq : Complex.sqrt (1 - (x:ℂ)^2) = (Real.cos (Real.arcsin x) : ℂ) := by
      rw [h1, Complex.sqrt_of_nonneg hnn, Complex.ofReal_re, Real.cos_arcsin]
    have he : Complex.sqrt (1 - (x:ℂ)^2) + I*x = Complex.exp ((Real.arcsin x:ℂ) * I) := by
      rw [hsq, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.sin_arcsin hx.1 hx.2]
      ring
    rw [arcsinPrincipal, he, Complex.log_exp]
    · linear_combination (-(Real.arcsin x:ℂ))*Complex.I_sq
    · simp; linarith [Real.neg_pi_div_two_le_arcsin x, Real.pi_pos]
    · simp; linarith [Real.arcsin_le_pi_div_two x, Real.pi_pos]
  refine ⟨hs, ?_⟩
  rw [arccosPrincipal, hs, Real.arccos_eq_pi_div_two_sub_arcsin]
  push_cast; ring

/-- DLMF 4.23.E10: arcsin principal neg. -/
@[dlmf 4.23.E10]
theorem arcsin_principal_neg {z : ℂ} (hz : z∈arcsinCutPlane) : arcsinPrincipal (-z)= -arcsinPrincipal z := by
  have hn:Complex.sqrt (1-(-z)^2)+I*(-z)=(Complex.sqrt (1-z^2)+I*z)⁻¹ := by
    apply (mul_left_cancel₀ (trig_arcsin_log_arg_ne z))
    rw [mul_inv_cancel₀ (trig_arcsin_log_arg_ne z)]
    convert trig_arcsin_product z using 1 <;> ring
  unfold arcsinPrincipal
  rw [hn,Complex.log_inv _ (Complex.mem_slitPlane_iff_arg.mp (trig_arcsin_log_slit z)).1]
  ring


/-- DLMF 4.23.E11: arccos principal neg. -/
@[dlmf 4.23.E11]
theorem arccos_principal_neg {z : ℂ} (hz : z∈arcsinCutPlane) : arccosPrincipal (-z)=π-arccosPrincipal z := by
  unfold arccosPrincipal
  rw [arcsin_principal_neg hz]
  ring


/-- DLMF 4.23.E12: arctan principal neg. -/
@[dlmf 4.23.E12]
theorem arctan_principal_neg {z : ℂ} (hz : z∈arctanCutPlane) : Complex.arctan (-z)= -Complex.arctan z := by
  have hq: (1+(-z)*I)/(1-(-z)*I)=((1+z*I)/(1-z*I))⁻¹ := by
    simp only [neg_mul,sub_neg_eq_add,sub_eq_add_neg,inv_div,neg_neg]
  rw [Complex.arctan,Complex.arctan,hq,Complex.log_inv _
    (Complex.mem_slitPlane_iff_arg.mp (trig_arctan_quotient_slit hz)).1]
  ring


/-- DLMF 4.23.E13: arccsc principal neg. -/
@[dlmf 4.23.E13]
theorem arccsc_principal_neg {z : ℂ} (hz : z∈arccscCutPlane) : arccscPrincipal (-z)= -arccscPrincipal z := by
  unfold arccscPrincipal
  rw [inv_neg]
  exact arcsin_principal_neg hz.2


/-- DLMF 4.23.E14: arcsec principal neg. -/
@[dlmf 4.23.E14]
theorem arcsec_principal_neg {z : ℂ} (hz : z∈arccscCutPlane) : arcsecPrincipal (-z)=π-arcsecPrincipal z := by
  unfold arcsecPrincipal
  rw [inv_neg]
  exact arccos_principal_neg hz.2


/-- DLMF 4.23.E15: arccot principal neg. -/
@[dlmf 4.23.E15]
theorem arccot_principal_neg {z : ℂ} (hz : z∈arccotCutPlane) : arccotPrincipal (-z)= -arccotPrincipal z := by
  unfold arccotPrincipal
  rw [inv_neg]
  exact arctan_principal_neg hz.2


/-- DLMF 4.23.E17: arcsec principal complement. -/
@[dlmf 4.23.E17]
theorem arcsec_principal_complement (z : ℂ) : arcsecPrincipal z=π/2-arccscPrincipal z := by
  rfl

/-- DLMF 4.23.E18: arccot principal complement. -/
@[dlmf 4.23.E18]
theorem arccot_principal_complement {z : ℂ} (hz : z.re≠0) :
    arccotPrincipal z=(if 0<z.re then π/2 else -π/2)-Complex.arctan z := by
  set w := (1+z*I)/(1-z*I) with hw
  have hD : 0<(1+z.im)^2+z.re^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hz)
  have him : w.im=(2*z.re)/((1+z.im)^2+z.re^2) := by
    simp [hw, Complex.div_im,Complex.normSq]
    ring
  have hm : 1 - z*I ≠ 0 := by
    intro h; have h2 := congrArg Complex.im h; simp at h2; exact hz h2
  have hzI : z - I ≠ 0 := by
    intro h; have h2 := congrArg Complex.re h; simp at h2; exact hz h2
  have h1 : (1+z⁻¹*I)/(1-z⁻¹*I) = -w⁻¹ := by
    have hz0 : z ≠ 0 := by rintro rfl; simp at hz
    have hp : 1 + z*I ≠ 0 := by
      intro h; have h2 := congrArg Complex.im h; simp at h2; exact hz h2
    have e1 : (1+z⁻¹*I)/(1-z⁻¹*I) = (z+I)/(z-I) := by
      rw [← mul_div_mul_left (1+z⁻¹*I) (1-z⁻¹*I) hz0]
      congr 1 <;> field_simp
    rw [e1, hw, inv_div, ← neg_div, div_eq_div_iff hzI hp]
    linear_combination (2*z)*Complex.I_sq
  have hl : ∀ s : ℝ, (Complex.arg (-w⁻¹) = -Complex.arg w + s) →
      Complex.log (-w⁻¹) = -Complex.log w + s * I := by
    intro s hs
    apply Complex.ext
    · simp [Complex.log_re, norm_inv, Real.log_inv]
    · simp [Complex.log_im, hs]
  rw [arccotPrincipal, Complex.arctan, Complex.arctan, h1, ← hw]
  have hinv : (w⁻¹).im = -w.im / Complex.normSq w := Complex.inv_im w
  split_ifs with hpos
  · have hwi : 0 < w.im := by rw [him]; positivity
    have hwi' : (w⁻¹).im < 0 := by
      rw [hinv, neg_div]; exact neg_neg_of_pos (div_pos hwi (Complex.normSq_pos.mpr (by
        intro h; rw [h] at hwi; simp at hwi)))
    have ha : Complex.arg w ≠ π := by
      intro h; have := Complex.arg_eq_pi_iff.mp h; linarith [this.2]
    rw [hl π (by rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg hwi', Complex.arg_inv, ite_cond_eq_false _ _ (eq_false ha)])]
    push_cast
    linear_combination (-(π:ℂ)/2)*Complex.I_sq
  · have hneg : z.re < 0 := lt_of_le_of_ne (not_lt.mp hpos) hz
    have hwi : w.im < 0 := by rw [him]; exact div_neg_of_neg_of_pos (by linarith) hD
    have hwi' : 0 < (w⁻¹).im := by
      rw [hinv, neg_div]; exact neg_pos.mpr (div_neg_of_neg_of_pos hwi (Complex.normSq_pos.mpr (by
        intro h; rw [h] at hwi; simp at hwi)))
    have ha : Complex.arg w ≠ π := by
      intro h; have := Complex.arg_eq_pi_iff.mp h; linarith [this.2]
    rw [hl (-π) (by rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos hwi', Complex.arg_inv, ite_cond_eq_false _ _ (eq_false ha)]; ring)]
    push_cast
    linear_combination ((π:ℂ)/2)*Complex.I_sq

/-- Arcsine on either bank of the positive real cut. -/
@[dlmf 4.23.E20]
def arcsinRightBank (upper : Bool) (x : ℝ) : ℂ :=
  π/2+trigBankSign upper*I*(Real.log (Real.sqrt (x^2-1)+x):ℂ)

/-- Arcsine on either bank of the negative real cut. -/
@[dlmf 4.23.E21]
def arcsinLeftBank (upper : Bool) (x : ℝ) : ℂ :=
  -π/2+trigBankSign upper*I*(Real.log (Real.sqrt (x^2-1)-x):ℂ)

/-- The principal square root formula valid on the lower half-plane, extended continuously. -/
def trigR4_sqrtLow (w : ℂ) : ℂ := (Real.sqrt ((‖w‖ + w.re)/2) : ℂ) - I * Real.sqrt ((‖w‖ - w.re)/2)

/-- The principal square root formula valid on the closed upper half-plane. -/
def trigR4_sqrtUp (w : ℂ) : ℂ := (Real.sqrt ((‖w‖ + w.re)/2) : ℂ) + I * Real.sqrt ((‖w‖ - w.re)/2)

/-- On the lower half-plane the principal root is `trigR4_sqrtLow`. -/
lemma trigR4_sqrt_eq_low {w : ℂ} (h : w.im < 0) : Complex.sqrt w = trigR4_sqrtLow w := by
  rw [Complex.sqrt_eq_real_add_ite, trigR4_sqrtLow, ite_eq_right_of_eq_false _ _ (eq_false (not_le.mpr h))]; ring

/-- On the closed upper half-plane the principal root is `trigR4_sqrtUp`. -/
lemma trigR4_sqrt_eq_up {w : ℂ} (h : 0 ≤ w.im) : Complex.sqrt w = trigR4_sqrtUp w := by
  rw [Complex.sqrt_eq_real_add_ite, trigR4_sqrtUp, ite_eq_left_of_eq_true _ _ (eq_true h)]; ring

/-- The lower-bank root formula is continuous. -/
lemma trigR4_continuous_sqrtLow : Continuous trigR4_sqrtLow := by
  unfold trigR4_sqrtLow; fun_prop

/-- The upper-bank root formula is continuous. -/
lemma trigR4_continuous_sqrtUp : Continuous trigR4_sqrtUp := by
  unfold trigR4_sqrtUp; fun_prop

/-- Lower-bank root of a nonpositive real. -/
lemma trigR4_sqrtLow_neg {t : ℝ} (ht : 0 ≤ t) : trigR4_sqrtLow (-(t:ℂ)) = -I * Real.sqrt t := by
  simp [trigR4_sqrtLow, abs_of_nonneg ht]

/-- Upper-bank root of a nonpositive real. -/
lemma trigR4_sqrtUp_neg {t : ℝ} (ht : 0 ≤ t) : trigR4_sqrtUp (-(t:ℂ)) = I * Real.sqrt t := by
  simp [trigR4_sqrtUp, abs_of_nonneg ht]

/-- Logarithm of a point on the positive imaginary axis. -/
lemma trigR4_log_I_mul_pos {s : ℝ} (hs : 0 < s) :
    Complex.log (I * s) = Real.log s + π/2 * I := by
  apply Complex.ext
  · simp [Complex.log_re, abs_of_pos hs]
  · simp [Complex.log_im, mul_comm I, Complex.arg_real_mul _ hs]

/-- Logarithm of a point on the negative imaginary axis. -/
lemma trigR4_log_I_mul_neg {s : ℝ} (hs : s < 0) :
    Complex.log (I * s) = Real.log (-s) - π/2 * I := by
  have he : I * (s:ℂ) = ((-s:ℝ):ℂ) * (-I) := by push_cast; ring
  apply Complex.ext
  · simp [Complex.log_re, abs_of_neg hs]
  · rw [he, Complex.log_im, Complex.arg_real_mul _ (by linarith), Complex.arg_neg_I]; simp

/-- Arcsine limits along a bank where the square root follows a continuous formula. -/
lemma trigR4_arcsin_bank {x : ℝ} {T : Set ℂ} {G : ℂ → ℂ} (hG : Continuous G)
    (hev : ∀ᶠ z in 𝓝[T] (x:ℂ), Complex.sqrt (1 - z^2) = G (1 - z^2))
    (hP : G (1 - (x:ℂ)^2) + I*x ∈ Complex.slitPlane) :
    Tendsto arcsinPrincipal (𝓝[T] (x:ℂ)) (𝓝 (-I * Complex.log (G (1 - (x:ℂ)^2) + I*x))) := by
  have hc : ContinuousAt (fun z : ℂ => -I * Complex.log (G (1 - z^2) + I*z)) (x:ℂ) := by
    apply ContinuousAt.mul continuousAt_const
    exact (((hG.comp (by fun_prop : Continuous fun z : ℂ => 1 - z^2)).add
      (by fun_prop : Continuous fun z : ℂ => I*z)).continuousAt).clog hP
  refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [hev] with z hz
  simp only [arcsinPrincipal, hz]

/-- Imaginary part of `1 - z^2`. -/
lemma trigR4_im_one_sub_sq (z : ℂ) : (1 - z^2).im = -(2 * z.re * z.im) := by
  simp [pow_two, Complex.mul_im]; ring

/-- `1 - x^2` as the negative of a real number. -/
lemma trigR4_one_sub_sq_real (x : ℝ) : (1:ℂ) - (x:ℂ)^2 = -((x^2 - 1 : ℝ) : ℂ) := by
  push_cast; ring

/-- DLMF 4.23.E20: arcsin right cut limit. -/
@[dlmf 4.23.E20]
theorem arcsin_right_cut_limit {x : ℝ} (hx : 1≤x) (upper : Bool) :
    Tendsto arcsinPrincipal (𝓝[{z : ℂ | if upper then 0<z.im else z.im<0}] (x:ℂ))
      (𝓝 (arcsinRightBank upper x)) := by
  have hx0 : 0 < x := by linarith
  have hr0 : 0 ≤ x^2 - 1 := by nlinarith
  set r := Real.sqrt (x^2 - 1) with hr
  have hrx : r < x + 1 := by
    rw [hr, Real.sqrt_lt' (by linarith)]; nlinarith
  have hrr : r * r = x^2 - 1 := Real.mul_self_sqrt hr0
  have hxr : 0 < x - r := by
    rw [hr, sub_pos, Real.sqrt_lt' hx0]; linarith
  have hxr' : 0 < x + r := by positivity
  have hprod : (x - r) * (x + r) = 1 := by nlinarith
  have hlog : Real.log (x - r) = -Real.log (r + x) := by
    have : x - r = (r + x)⁻¹ := by
      exact eq_inv_of_mul_eq_one_left (by linarith [hprod])
    rw [this, Real.log_inv]
  have hre : ∀ᶠ z in 𝓝 (x:ℂ), 0 < z.re :=
    (Complex.continuous_re.tendsto (x:ℂ)).eventually (lt_mem_nhds (by simpa using hx0))
  cases upper
  · -- lower bank: im z < 0, so im (1 - z^2) > 0
    have hev : ∀ᶠ z in 𝓝[{z : ℂ | if false = true then 0<z.im else z.im<0}] (x:ℂ),
        Complex.sqrt (1 - z^2) = trigR4_sqrtUp (1 - z^2) := by
      filter_upwards [nhdsWithin_le_nhds hre, self_mem_nhdsWithin] with z hz hzT
      simp only [Bool.false_eq_true, ite_false] at hzT
      apply trigR4_sqrt_eq_up
      rw [trigR4_im_one_sub_sq]; nlinarith
    have hP : trigR4_sqrtUp (1 - (x:ℂ)^2) + I*x = I * ((x + r : ℝ):ℂ) := by
      rw [trigR4_one_sub_sq_real, trigR4_sqrtUp_neg hr0]; push_cast; ring
    have h := trigR4_arcsin_bank trigR4_continuous_sqrtUp hev
      (by rw [hP]; exact Or.inr (by simp; linarith))
    rw [hP, trigR4_log_I_mul_pos hxr'] at h
    convert h using 2
    simp only [arcsinRightBank, trigBankSign, Bool.false_eq_true, ite_false]
    rw [add_comm r x]
    linear_combination ((π:ℂ)/2)*Complex.I_sq
  · have hev : ∀ᶠ z in 𝓝[{z : ℂ | if true = true then 0<z.im else z.im<0}] (x:ℂ),
        Complex.sqrt (1 - z^2) = trigR4_sqrtLow (1 - z^2) := by
      filter_upwards [nhdsWithin_le_nhds hre, self_mem_nhdsWithin] with z hz hzT
      simp only [ite_true] at hzT
      apply trigR4_sqrt_eq_low
      rw [trigR4_im_one_sub_sq]; nlinarith
    have hP : trigR4_sqrtLow (1 - (x:ℂ)^2) + I*x = I * ((x - r : ℝ):ℂ) := by
      rw [trigR4_one_sub_sq_real, trigR4_sqrtLow_neg hr0]; push_cast; ring
    have h := trigR4_arcsin_bank trigR4_continuous_sqrtLow hev
      (by rw [hP]; exact Or.inr (by simp; linarith))
    rw [hP, trigR4_log_I_mul_pos hxr, hlog] at h
    convert h using 2
    simp only [arcsinRightBank, trigBankSign, ite_true]
    push_cast
    linear_combination ((π:ℂ)/2)*Complex.I_sq

/-- DLMF 4.23.E21: arcsin left cut limit. -/
@[dlmf 4.23.E21]
theorem arcsin_left_cut_limit {x : ℝ} (hx : x≤ -1) (upper : Bool) :
    Tendsto arcsinPrincipal (𝓝[{z : ℂ | if upper then 0<z.im else z.im<0}] (x:ℂ))
      (𝓝 (arcsinLeftBank upper x)) := by
  have hx0 : x < 0 := by linarith
  have hr0 : 0 ≤ x^2 - 1 := by nlinarith
  set r := Real.sqrt (x^2 - 1) with hr
  have hrr : r * r = x^2 - 1 := Real.mul_self_sqrt hr0
  have hrn : 0 ≤ r := Real.sqrt_nonneg _
  have hxr : x + r < 0 := by
    have : r < -x := by rw [hr, Real.sqrt_lt' (by linarith)]; nlinarith
    linarith
  have hxr' : x - r < 0 := by linarith
  have hlog : Real.log (-(x + r)) = -Real.log (r - x) := by
    have : -(x + r) = (r - x)⁻¹ := eq_inv_of_mul_eq_one_left (by nlinarith [hrr])
    rw [this, Real.log_inv]
  have hre : ∀ᶠ z in 𝓝 (x:ℂ), z.re < 0 :=
    (Complex.continuous_re.tendsto (x:ℂ)).eventually (gt_mem_nhds (by simpa using hx0))
  cases upper
  · have hev : ∀ᶠ z in 𝓝[{z : ℂ | if false = true then 0<z.im else z.im<0}] (x:ℂ),
        Complex.sqrt (1 - z^2) = trigR4_sqrtLow (1 - z^2) := by
      filter_upwards [nhdsWithin_le_nhds hre, self_mem_nhdsWithin] with z hz hzT
      simp only [Bool.false_eq_true, ite_false] at hzT
      apply trigR4_sqrt_eq_low
      rw [trigR4_im_one_sub_sq]; nlinarith
    have hP : trigR4_sqrtLow (1 - (x:ℂ)^2) + I*x = I * ((x - r : ℝ):ℂ) := by
      rw [trigR4_one_sub_sq_real, trigR4_sqrtLow_neg hr0]; push_cast; ring
    have h := trigR4_arcsin_bank trigR4_continuous_sqrtLow hev
      (by rw [hP]; exact Or.inr (by simp; linarith))
    rw [hP, trigR4_log_I_mul_neg hxr', show -(x - r) = r - x by ring] at h
    convert h using 2
    simp only [arcsinLeftBank, trigBankSign, Bool.false_eq_true, ite_false]
    linear_combination (-(π:ℂ)/2)*Complex.I_sq
  · have hev : ∀ᶠ z in 𝓝[{z : ℂ | if true = true then 0<z.im else z.im<0}] (x:ℂ),
        Complex.sqrt (1 - z^2) = trigR4_sqrtUp (1 - z^2) := by
      filter_upwards [nhdsWithin_le_nhds hre, self_mem_nhdsWithin] with z hz hzT
      simp only [ite_true] at hzT
      apply trigR4_sqrt_eq_up
      rw [trigR4_im_one_sub_sq]; nlinarith
    have hP : trigR4_sqrtUp (1 - (x:ℂ)^2) + I*x = I * ((x + r : ℝ):ℂ) := by
      rw [trigR4_one_sub_sq_real, trigR4_sqrtUp_neg hr0]; push_cast; ring
    have h := trigR4_arcsin_bank trigR4_continuous_sqrtUp hev
      (by rw [hP]; exact Or.inr (by simp; linarith))
    rw [hP, trigR4_log_I_mul_neg hxr, hlog] at h
    convert h using 2
    simp only [arcsinLeftBank, trigBankSign, ite_true]
    push_cast
    linear_combination (-(π:ℂ)/2)*Complex.I_sq

/-- DLMF 4.23.E22: arccos principal log. -/
@[dlmf 4.23.E22]
theorem arccos_principal_log (z : ℂ) :
    arccosPrincipal z=π/2+I*Complex.log (Complex.sqrt (1-z^2)+I*z) := by
  unfold arccosPrincipal arcsinPrincipal; ring

/-- DLMF 4.23.E24: arccos right cut limit. -/
@[dlmf 4.23.E24]
theorem arccos_right_cut_limit {x : ℝ} (hx : 1≤x) (upper : Bool) :
    Tendsto arccosPrincipal (𝓝[{z : ℂ | if upper then 0<z.im else z.im<0}] (x:ℂ))
      (𝓝 (π/2-arcsinRightBank upper x)) := by
  exact (arcsin_right_cut_limit hx upper).const_sub ((π:ℂ)/2)

/-- DLMF 4.23.E25: arccos left cut limit. -/
@[dlmf 4.23.E25]
theorem arccos_left_cut_limit {x : ℝ} (hx : x≤ -1) (upper : Bool) :
    Tendsto arccosPrincipal (𝓝[{z : ℂ | if upper then 0<z.im else z.im<0}] (x:ℂ))
      (𝓝 (π/2-arcsinLeftBank upper x)) := by
  exact (arcsin_left_cut_limit hx upper).const_sub ((π:ℂ)/2)

/-- DLMF 4.23.E26: arctan principal log. -/
@[dlmf 4.23.E26]
theorem arctan_principal_log {z : ℂ} (hz : z∈arctanCutPlane) :
    Complex.arctan z=I/2*Complex.log ((I+z)/(I-z)) := by
  have hs := trig_arctan_quotient_slit hz
  have hv : (I+z)/(I-z) = ((1+z*I)/(1-z*I))⁻¹ := by
    rw [inv_div, show (1-z*I) = (-I)*(I+z) by linear_combination Complex.I_sq,
      show (1+z*I) = (-I)*(I-z) by linear_combination Complex.I_sq,
      mul_div_mul_left _ _ (neg_ne_zero.mpr Complex.I_ne_zero)]
  rw [hv, Complex.log_inv _ (Complex.slitPlane_arg_ne_pi hs), Complex.arctan]
  ring

/-- Arctangent bank values on the two exterior imaginary cuts. -/
@[dlmf 4.23.E27]
def arctanCutBank (right : Bool) (y : ℝ) : ℂ :=
  trigBankSign right*π/2+I/2*(Real.log ((y+1)/(y-1)):ℂ)

/-- Imaginary part of the arctangent logarithm argument. -/
lemma trigR4_arctan_quot_im (z : ℂ) :
    ((1+z*I)/(1-z*I)).im=(2*z.re)/((1+z.im)^2+z.re^2) := by
  simp [Complex.div_im,Complex.normSq]
  ring

/-- DLMF 4.23.E27: arctan cut limit. -/
@[dlmf 4.23.E27]
theorem arctan_cut_limit {y : ℝ} (hy : 1< |y|) (right : Bool) :
    Tendsto Complex.arctan (𝓝[{z : ℂ | if right then 0<z.re else z.re<0}] ((y:ℂ)*I))
      (𝓝 (arctanCutBank right y)) := by
  have hy1 : y + 1 ≠ 0 := by
    intro h; rw [show y = -1 by linarith] at hy; norm_num at hy
  have hym : y - 1 ≠ 0 := by
    intro h; rw [show y = 1 by linarith] at hy; norm_num at hy
  have hden : (1:ℂ) - (y:ℂ)*I*I ≠ 0 := by
    rw [mul_assoc, Complex.I_mul_I]
    exact_mod_cast (show (1:ℝ) - y * -1 ≠ 0 by intro h; apply hy1; linarith)
  set w0 : ℂ := (1+(y:ℂ)*I*I)/(1-(y:ℂ)*I*I) with hw0
  have hw0r : w0 = (((1 - y)/(1 + y) : ℝ) : ℂ) := by
    rw [hw0, mul_assoc, Complex.I_mul_I]; push_cast; ring_nf
  have hneg : (1 - y)/(1 + y) < 0 := by
    rcases lt_or_gt_of_ne (show y ≠ 0 by rintro rfl; norm_num at hy) with h | h
    · have : y < -1 := by rw [abs_of_neg h] at hy; linarith
      exact div_neg_of_pos_of_neg (by linarith) (by linarith)
    · have : 1 < y := by rw [abs_of_pos h] at hy; linarith
      exact div_neg_of_neg_of_pos (by linarith) (by linarith)
  have hw0re : w0.re < 0 := by rw [hw0r, Complex.ofReal_re]; exact hneg
  have hw0im : w0.im = 0 := by rw [hw0r, Complex.ofReal_im]
  have hnorm : Real.log ‖w0‖ = -Real.log ((y+1)/(y-1)) := by
    rw [hw0r, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hneg, ← Real.log_inv, inv_div,
      ← neg_div, neg_sub, add_comm 1 y]
  have hcont : ContinuousAt (fun z : ℂ => (1+z*I)/(1-z*I)) ((y:ℂ)*I) :=
    ((by fun_prop : Continuous fun z : ℂ => 1+z*I).continuousAt).div
      ((by fun_prop : Continuous fun z : ℂ => 1-z*I).continuousAt) hden
  have hD : ∀ z : ℂ, z.re ≠ 0 → 0 < (1+z.im)^2+z.re^2 := fun z hz =>
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hz)
  cases right
  · have hw : Tendsto (fun z : ℂ => (1+z*I)/(1-z*I))
        (𝓝[{z : ℂ | if false = true then 0<z.re else z.re<0}] ((y:ℂ)*I))
        (𝓝[{z : ℂ | z.im < 0}] w0) := by
      apply tendsto_nhdsWithin_iff.mpr ⟨hcont.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz' : z.re < 0 := by simpa using hz
      show ((1+z*I)/(1-z*I)).im < 0
      rw [trigR4_arctan_quot_im]
      exact div_neg_of_neg_of_pos (by linarith) (hD z hz'.ne)
    have h := ((Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero hw0re hw0im).comp
      hw).const_mul (-I/2)
    have h' : Tendsto Complex.arctan _ (𝓝 (-I/2 * (Real.log ‖w0‖ - π * I))) := h
    convert h' using 2
    simp only [arctanCutBank, trigBankSign, Bool.false_eq_true, ite_false, hnorm]
    push_cast
    linear_combination (-(π:ℂ)/2)*Complex.I_sq
  · have hw : Tendsto (fun z : ℂ => (1+z*I)/(1-z*I))
        (𝓝[{z : ℂ | if true = true then 0<z.re else z.re<0}] ((y:ℂ)*I))
        (𝓝[{z : ℂ | 0 ≤ z.im}] w0) := by
      apply tendsto_nhdsWithin_iff.mpr ⟨hcont.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz' : 0 < z.re := by simpa using hz
      show 0 ≤ ((1+z*I)/(1-z*I)).im
      rw [trigR4_arctan_quot_im]
      exact (div_pos (by linarith) (hD z hz'.ne')).le
    have h := ((Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hw0re hw0im).comp
      hw).const_mul (-I/2)
    have h' : Tendsto Complex.arctan _ (𝓝 (-I/2 * (Real.log ‖w0‖ + π * I))) := h
    convert h' using 2
    simp only [arctanCutBank, trigBankSign, ite_true, hnorm]
    push_cast
    linear_combination ((π:ℂ)/2)*Complex.I_sq

/-- DLMF 4.23.iv: reciprocal reverses real cut bank. -/
@[dlmf 4.23.iv]
theorem reciprocal_reverses_real_cut_bank {x : ℝ} (hx : x≠0) :
    Tendsto (fun y : ℝ => ((x:ℂ)+I*y)⁻¹) (𝓝[>] 0) (𝓝 ((x:ℂ)⁻¹)) ∧
    ∀ y : ℝ,0<y→(((x:ℂ)+I*y)⁻¹).im<0 := by
  constructor
  · have hc : ContinuousAt (fun y : ℝ => ((x:ℂ)+I*y)⁻¹) 0 := by
      apply ContinuousAt.inv₀ (by fun_prop)
      simpa using hx
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  · intro y hy
    rw [Complex.inv_im]
    have : 0 < Complex.normSq ((x:ℂ)+I*y) := by
      rw [Complex.normSq_pos]; intro h; have := congrArg Complex.re h; simp at this; exact hx this
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re]
    have h2 : (0:ℝ) < (0 * y + 1 * y) := by linarith
    rw [neg_div]
    simpa [zero_add] using div_pos (by linarith : (0:ℝ) < 0 + (0 * 0 + 1 * y)) this

/-- DLMF 4.23.E28: sin arcsin principal. -/
@[dlmf 4.23.E28]
theorem sin_arcsin_principal (z : ℂ) : Complex.sin (arcsinPrincipal z)=z := by
  let w:=Complex.sqrt (1-z^2)+I*z
  have hw:w≠0 := trig_arcsin_log_arg_ne z
  have hp:w*(Complex.sqrt (1-z^2)-I*z)=1 := trig_arcsin_product z
  have hi:w⁻¹=Complex.sqrt (1-z^2)-I*z := by
    apply (mul_left_cancel₀ hw)
    rw [mul_inv_cancel₀ hw,hp]
  have he:Complex.exp (arcsinPrincipal z*I)=w := by
    rw [arcsinPrincipal,show -I*Complex.log w*I=Complex.log w by linear_combination -Complex.log w*Complex.I_sq]
    exact Complex.exp_log hw
  have hn:Complex.exp (-(arcsinPrincipal z)*I)=w⁻¹ := by
    rw [neg_mul,Complex.exp_neg,he]
  rw [Complex.sin,he,hn,hi]
  dsimp [w]
  linear_combination -z*Complex.I_sq


/-- DLMF 4.23.E29: cos arccos principal. -/
@[dlmf 4.23.E29]
theorem cos_arccos_principal (z : ℂ) : Complex.cos (arccosPrincipal z)=z := by
  rw [arccosPrincipal,Complex.cos_pi_div_two_sub,sin_arcsin_principal]


/-- Mathlib gives the two sine fibers separately; this combines them using integer parity. -/
private lemma trig_sine_fiber_forms (A w : ℂ) :
    (∃ k : ℤ,w=2*k*π+A ∨ w=(2*k+1)*π-A) ↔
      ∃ k : ℤ,w=(-1:ℂ)^k*A+k*π := by
  constructor
  · rintro ⟨k,hk|hk⟩
    · have he:Even (2*k:ℤ) := ⟨k,by ring⟩
      refine ⟨2*k,?_⟩
      rw [he.neg_one_zpow]
      push_cast
      linear_combination hk
    · have ho:Odd (2*k+1:ℤ) := ⟨k,by ring⟩
      refine ⟨2*k+1,?_⟩
      rw [ho.neg_one_zpow]
      push_cast
      linear_combination hk
  · rintro ⟨n,hn⟩
    obtain ⟨k,hk|hk⟩:=Int.even_or_odd' n
    · have he:Even (2*k:ℤ) := ⟨k,by ring⟩
      rw [hk,he.neg_one_zpow] at hn
      refine ⟨k,Or.inl ?_⟩
      push_cast at hn
      linear_combination hn
    · have ho:Odd (2*k+1:ℤ) := ⟨k,by ring⟩
      rw [hk,ho.neg_one_zpow] at hn
      refine ⟨k,Or.inr ?_⟩
      push_cast at hn
      linear_combination hn

/-- DLMF 4.23.E31: arcsin general values. -/
@[dlmf 4.23.E31]
theorem arcsin_general_values (z w : ℂ) :
    w∈arcsinGeneral z ↔ ∃ k : ℤ,w=(-1:ℂ)^k*arcsinPrincipal z+k*π := by
  change Complex.sin w=z ↔ _
  have hb:=sin_arcsin_principal z
  constructor
  · intro h
    exact (trig_sine_fiber_forms _ _).mp (Complex.sin_eq_sin_iff.mp (hb.trans h.symm))
  · intro h
    exact (Complex.sin_eq_sin_iff.mpr ((trig_sine_fiber_forms _ _).mpr h)).symm.trans hb


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


private lemma trig_gd_integral {f:ℝ→ℝ}
    (hf:∀x,HasDerivAt f (Real.cosh x)⁻¹ x) (h0:f 0=0) (x:ℝ) : gudermannian x=f x := by
  have hc:Continuous (fun t:ℝ=>(Real.cosh t)⁻¹) := Real.continuous_cosh.inv₀ (fun t=>(Real.cosh_pos t).ne')
  rw [gudermannian,intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _=>hf t) (hc.intervalIntegrable 0 x),h0,sub_zero]

private lemma trig_sqrt_one_sub_tanh (x:ℝ) :
    Real.sqrt (1-(Real.tanh x)^2)=(Real.cosh x)⁻¹ := by
  have hc:0<Real.cosh x := Real.cosh_pos x
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (inv_nonneg.mpr hc.le)).mp
  rw [Real.sq_sqrt (by linarith [Real.tanh_sq_lt_one x]),Real.tanh_eq_sinh_div_cosh]
  field_simp
  linear_combination Real.cosh_sq_sub_sinh_sq x

private lemma trig_sqrt_one_add_tan {x:ℝ} (hx:|x|<π/2) :
    Real.sqrt (1+(Real.tan x)^2)=(Real.cos x)⁻¹ := by
  simpa only [inv_inv] using congrArg Inv.inv
    (Real.inv_sqrt_one_add_tan_sq (Real.cos_pos_of_mem_Ioo (abs_lt.mp hx)))

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


/-- DLMF 4.24.E1: hasSum arcsin principal. -/
@[dlmf 4.24.E1]
theorem hasSum_arcsin_principal {z : ℂ} (hz : ‖z‖≤1) :
    HasSum (fun n : ℕ => ((2*n).choose n:ℂ)*z^(2*n+1)/(4^n*(2*n+1))) (arcsinPrincipal z) := by
  sorry

/-- Arccosine series after factoring its square root, with the removable center handled separately. -/
@[dlmf 4.24.E2]
theorem hasSum_arccos_principal {z : ℂ} (hz : ‖1-z‖≤2) :
    HasSum (fun n : ℕ => Complex.sqrt (2*(1-z))*((2*n).choose n:ℂ)*(1-z)^n/(8^n*(2*n+1)))
      (arccosPrincipal z) := by
  sorry

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
  sorry

/-- DLMF 4.24.E4: arctan exterior series. -/
@[dlmf 4.24.E4]
theorem arctan_exterior_series {z : ℂ} (hz : 1≤‖z‖) (hr : z.re≠0) :
    Tendsto (fun N : ℕ => (if 0<z.re then (π:ℂ)/2 else -π/2)-
      ∑ n∈Finset.range N,(-1:ℂ)^n/(z^(2*n+1)*(2*n+1))) atTop (𝓝 (Complex.arctan z)) := by
  sorry

/-- Euler transformed arctangent series, with its removable zero excluded. -/
@[dlmf 4.24.E5]
theorem hasSum_arctan_euler {z : ℂ} (hz : -(1/2:ℝ)<(z^2).re) :
    HasSum (fun n : ℕ => z/(1+z^2)*(4:ℂ)^n*(n.factorial:ℂ)^2/(2*n+1)!*(z^2/(1+z^2))^n)
      (Complex.arctan z) := by
  sorry

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


/-! ## Exact trigonometric tables -/

/-- The six real trigonometric functions in the order used by the exact-value tables. -/
def trigRealVector (θ : ℝ) : Fin 6→ℝ :=
  ![Real.sin θ,Real.cos θ,Real.tan θ,(Real.sin θ)⁻¹,(Real.cos θ)⁻¹,Real.cot θ]

/-- Signs of the six functions in quadrants I, II, III and IV. -/
def trigQuadrantSigns : Fin 4→Fin 6→ℝ :=
  ![![1,1,1,1,1,1],![1,-1,-1,1,-1,-1],![-1,-1,1,-1,-1,1],![-1,1,-1,-1,1,-1]]

/-- Sign of a positive real. -/
private lemma trigR4_sign_pos {x : ℝ} (h : 0 < x) : trigRealSign x = 1 := by
  simp [trigRealSign, h]

/-- Sign of a negative real. -/
private lemma trigR4_sign_neg {x : ℝ} (h : x < 0) : trigRealSign x = -1 := by
  simp [trigRealSign, h, not_lt.mpr h.le]

/-- DLMF 4.16.T1: trig quadrant signs. -/
@[dlmf 4.16.T1]
theorem trig_quadrant_signs (q : Fin 4) {θ : ℝ}
    (hθ : θ∈Ioo ((q:ℝ)*π/2) (((q:ℝ)+1)*π/2)) (j : Fin 6) :
    trigRealSign (trigRealVector θ j)=trigQuadrantSigns q j := by
  have hp := Real.pi_pos
  obtain ⟨h1, h2⟩ := hθ
  fin_cases q
  · simp at h1 h2
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    fin_cases j <;> simp [trigRealVector, trigQuadrantSigns, Real.tan_eq_sin_div_cos,
      Real.cot_eq_cos_div_sin, trigR4_sign_pos, hs, hc]
  · simp at h1 h2
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hc : Real.cos θ < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)
    fin_cases j <;> simp [trigRealVector, trigQuadrantSigns, Real.tan_eq_sin_div_cos,
      Real.cot_eq_cos_div_sin, trigR4_sign_pos, trigR4_sign_neg, hs, hc, div_neg_of_pos_of_neg,
      div_neg_of_neg_of_pos]
  · simp at h1 h2
    norm_num at h1 h2
    have hs : Real.sin θ < 0 := by
      have := Real.sin_pos_of_pos_of_lt_pi (x := θ - π) (by linarith) (by linarith)
      rw [Real.sin_sub_pi] at this; linarith
    have hc : Real.cos θ < 0 := by
      have := Real.cos_pos_of_mem_Ioo (x := θ - π) ⟨by linarith, by linarith⟩
      rw [Real.cos_sub_pi] at this; linarith
    fin_cases j <;> simp [trigRealVector, trigQuadrantSigns, Real.tan_eq_sin_div_cos,
      Real.cot_eq_cos_div_sin, trigR4_sign_pos, trigR4_sign_neg, hs, hc, div_pos_of_neg_of_neg]
  · simp at h1 h2
    norm_num at h1 h2
    have hs : Real.sin θ < 0 := by
      have := Real.sin_pos_of_pos_of_lt_pi (x := θ - π) (by linarith) (by linarith)
      rw [Real.sin_sub_pi] at this; linarith
    have hc : 0 < Real.cos θ := by
      have := Real.cos_pos_of_mem_Ioo (x := θ - 2*π) ⟨by linarith, by linarith⟩
      rwa [Real.cos_sub_two_pi] at this
    fin_cases j <;> simp [trigRealVector, trigQuadrantSigns, Real.tan_eq_sin_div_cos,
      Real.cot_eq_cos_div_sin, trigR4_sign_pos, trigR4_sign_neg, hs, hc, div_neg_of_pos_of_neg,
      div_neg_of_neg_of_pos]

/-- All quarter-period identities; reflection and the full period supply both signs in Table 4.16.2. -/
@[dlmf 4.16.T2]
theorem trig_quarter_period_table (θ : ℝ) (q : Fin 4) :
    trigRealVector (θ+(q:ℝ)*π/2)=
    (![trigRealVector θ,
      ![Real.cos θ,-Real.sin θ,-Real.cot θ,(Real.cos θ)⁻¹,-(Real.sin θ)⁻¹,-Real.tan θ],
      ![-Real.sin θ,-Real.cos θ,Real.tan θ,-(Real.sin θ)⁻¹,-(Real.cos θ)⁻¹,Real.cot θ],
      ![-Real.cos θ,Real.sin θ,-Real.cot θ,-(Real.cos θ)⁻¹,(Real.sin θ)⁻¹,-Real.tan θ]] : Fin 4→Fin 6→ℝ) q := by
  have hs3 : Real.sin (3*Real.pi/2)= -1 := by
    rw [show (3:ℝ)*Real.pi/2=Real.pi+Real.pi/2 by ring,Real.sin_add]
    norm_num
  have hc3 : Real.cos (3*Real.pi/2)=0 := by
    rw [show (3:ℝ)*Real.pi/2=Real.pi+Real.pi/2 by ring,Real.cos_add]
    norm_num
  fin_cases q <;> ext j <;> fin_cases j <;>
    norm_num [trigRealVector,Real.tan_eq_sin_div_cos,Real.cot_eq_cos_div_sin,
      Real.sin_add,Real.cos_add,hs3,hc3,neg_div,div_neg]

/-- Algebraic interrelations; rows are output functions, columns are the known function. -/
def trigInterrelationTable (a : ℝ) : Fin 6→Fin 6→ℝ :=
  ![![a,Real.sqrt (1-a^2),a/Real.sqrt (1+a^2),a⁻¹,Real.sqrt (a^2-1)/a,(Real.sqrt (1+a^2))⁻¹],
    ![Real.sqrt (1-a^2),a,(Real.sqrt (1+a^2))⁻¹,Real.sqrt (a^2-1)/a,a⁻¹,a/Real.sqrt (1+a^2)],
    ![a/Real.sqrt (1-a^2),Real.sqrt (1-a^2)/a,a,(Real.sqrt (a^2-1))⁻¹,Real.sqrt (a^2-1),a⁻¹],
    ![a⁻¹,(Real.sqrt (1-a^2))⁻¹,Real.sqrt (1+a^2)/a,a,a/Real.sqrt (a^2-1),Real.sqrt (1+a^2)],
    ![(Real.sqrt (1-a^2))⁻¹,a⁻¹,Real.sqrt (1+a^2),a/Real.sqrt (a^2-1),a,Real.sqrt (1+a^2)/a],
    ![Real.sqrt (1-a^2)/a,a/Real.sqrt (1-a^2),a⁻¹,Real.sqrt (a^2-1),(Real.sqrt (a^2-1))⁻¹,a]]

/-- Every cell of the interrelation table, with its nonnegative finite principal-root convention. -/
@[dlmf 4.16.T3]
theorem trig_interrelation_table {θ : ℝ} (hs : 0<Real.sin θ) (hc : 0<Real.cos θ) (i j : Fin 6) :
    trigRealVector θ i=trigInterrelationTable (trigRealVector θ j) i j := by
  have key : trigRealVector θ = ![Real.sin θ, Real.cos θ, Real.sin θ / Real.cos θ,
      (Real.sin θ)⁻¹, (Real.cos θ)⁻¹, Real.cos θ / Real.sin θ] := by
    ext k; fin_cases k <;> simp [trigRealVector, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin]
  have hsc := Real.sin_sq_add_cos_sq θ
  rw [key]
  generalize Real.sin θ = s at hs hsc ⊢
  generalize Real.cos θ = c at hc hsc ⊢
  have hs0 : s ≠ 0 := hs.ne'
  have hc0 : c ≠ 0 := hc.ne'
  have f1 : Real.sqrt (1 - s^2) = c := by
    rw [show 1 - s^2 = c^2 by linarith, Real.sqrt_sq hc.le]
  have f2 : Real.sqrt (1 - c^2) = s := by
    rw [show 1 - c^2 = s^2 by linarith, Real.sqrt_sq hs.le]
  have f3 : Real.sqrt (1 + (s/c)^2) = c⁻¹ := by
    rw [show 1 + (s/c)^2 = (c⁻¹)^2 by field_simp; linarith, Real.sqrt_sq (inv_pos.mpr hc).le]
  have f4 : Real.sqrt (1 + (c/s)^2) = s⁻¹ := by
    rw [show 1 + (c/s)^2 = (s⁻¹)^2 by field_simp; linarith, Real.sqrt_sq (inv_pos.mpr hs).le]
  have f5 : Real.sqrt ((s⁻¹)^2 - 1) = c/s := by
    rw [show (s⁻¹)^2 - 1 = (c/s)^2 by field_simp; linarith, Real.sqrt_sq (div_pos hc hs).le]
  have f6 : Real.sqrt ((c⁻¹)^2 - 1) = s/c := by
    rw [show (c⁻¹)^2 - 1 = (s/c)^2 by field_simp; linarith, Real.sqrt_sq (div_pos hs hc).le]
  fin_cases i <;> fin_cases j <;> simp [trigInterrelationTable, f1, f2, f3, f4, f5, f6] <;>
    field_simp <;> grind

/-- Exact values at all multiples of pi/12 from zero to pi; pole cells contain placeholders. -/
def trigTwelfthTable : Fin 13→Fin 6→ℝ :=
  let r := Real.sqrt 2
  let t := Real.sqrt 3
  ![![0,1,0,0,1,0],
    ![r*(t-1)/4,r*(t+1)/4,2-t,r*(t+1),r*(t-1),2+t],
    ![1/2,t/2,t/3,2,2*t/3,t],
    ![r/2,r/2,1,r,r,1],
    ![t/2,1/2,t,2*t/3,2,t/3],
    ![r*(t+1)/4,r*(t-1)/4,2+t,r*(t-1),r*(t+1),2-t],
    ![1,0,0,1,0,0],
    ![r*(t+1)/4,-r*(t-1)/4,-(2+t),r*(t-1),-r*(t+1),-(2-t)],
    ![t/2,-1/2,-t,2*t/3,-2,-t/3],
    ![r/2,-r/2,-1,r,-r,-1],
    ![1/2,-t/2,-t/3,2,-2*t/3,-t],
    ![r*(t-1)/4,-r*(t+1)/4,-(2-t),r*(t+1),-r*(t-1),-(2+t)],
    ![0,-1,0,0,-1,0]]

/-- Pole cells of the exact trigonometric value table; they are not finite values. -/
def trigTwelfthPole (q : Fin 13) (j : Fin 6) : Prop :=
  ((q=0 ∨ q=12) ∧ (j=3 ∨ j=5)) ∨ (q=6 ∧ (j=2 ∨ j=4))

/-- Exact sine and cosine at `π/12`. -/
lemma trigR4_sin_cos_pi_div_twelve :
    Real.sin (π/12) = Real.sqrt 2 * (Real.sqrt 3 - 1) / 4 ∧
    Real.cos (π/12) = Real.sqrt 2 * (Real.sqrt 3 + 1) / 4 := by
  have h : π/12 = π/3 - π/4 := by ring
  rw [h, Real.sin_sub, Real.cos_sub, Real.sin_pi_div_three, Real.cos_pi_div_three,
    Real.sin_pi_div_four, Real.cos_pi_div_four]
  constructor <;> ring

/-- DLMF 4.17.T1: trig twelfth exact values. -/
@[dlmf 4.17.T1]
theorem trig_twelfth_exact_values (q : Fin 13) (j : Fin 6) (h : ¬trigTwelfthPole q j) :
    trigRealVector ((q:ℝ)*π/12) j=trigTwelfthTable q j := by
  obtain ⟨s1, c1⟩ := trigR4_sin_cos_pi_div_twelve
  have hr : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ht : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hr0 : 0 < Real.sqrt 2 := by positivity
  have ht1 : 1 < Real.sqrt 3 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have key : ∀ θ s c : ℝ, Real.sin θ = s → Real.cos θ = c →
      trigRealVector θ = ![s, c, s/c, s⁻¹, c⁻¹, c/s] := by
    intro θ s c hs hc
    ext k; fin_cases k <;> simp [trigRealVector, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin, hs, hc]
  fin_cases q
  · rw [key _ 0 1 (by simp) (by simp)]
    fin_cases j <;> simp [trigTwelfthTable, trigTwelfthPole] at h ⊢
  · rw [key _ _ _ (by simpa using s1) (by simpa using c1)]
    fin_cases j <;> simp [trigTwelfthTable, trigTwelfthPole] at h ⊢ <;> grind
  · have hs : Real.sin (2*π/12) = 1/2 := by rw [show (2:ℝ)*π/12 = π/6 by ring, Real.sin_pi_div_six]
    have hc : Real.cos (2*π/12) = Real.sqrt 3/2 := by rw [show (2:ℝ)*π/12 = π/6 by ring, Real.cos_pi_div_six]
    rw [key _ _ _ (by simpa using hs) (by simpa using hc)]
    fin_cases j <;> simp [trigTwelfthTable, trigTwelfthPole] at h ⊢ <;> grind
  · have hs : Real.sin (3*π/12) = Real.sqrt 2/2 := by rw [show (3:ℝ)*π/12 = π/4 by ring, Real.sin_pi_div_four]
    have hc : Real.cos (3*π/12) = Real.sqrt 2/2 := by rw [show (3:ℝ)*π/12 = π/4 by ring, Real.cos_pi_div_four]
    rw [key _ _ _ (by simpa using hs) (by simpa using hc)]
    fin_cases j <;> simp [trigTwelfthTable, trigTwelfthPole] at h ⊢
  · have hs : Real.sin (4*π/12) = Real.sqrt 3/2 := by rw [show (4:ℝ)*π/12 = π/3 by ring, Real.sin_pi_div_three]
    have hc : Real.cos (4*π/12) = 1/2 := by rw [show (4:ℝ)*π/12 = π/3 by ring, Real.cos_pi_div_three]
    rw [key _ _ _ (by simpa using hs) (by simpa using hc)]
    fin_cases j <;> simp [trigTwelfthTable, trigTwelfthPole] at h ⊢ <;> grind
  · have hs : Real.sin (5*π/12) = Real.sqrt 2 * (Real.sqrt 3 + 1) / 4 := by
      rw [show (5:ℝ)*π/12 = π/2 - π/12 by ring, Real.sin_pi_div_two_sub, c1]
    have hc : Real.cos (5*π/12) = Real.sqrt 2 * (Real.sqrt 3 - 1) / 4 := by
      rw [show (5:ℝ)*π/12 = π/2 - π/12 by ring, Real.cos_pi_div_two_sub, s1]
    rw [key _ _ _ (by simpa using hs) (by simpa using hc)]
    fin_cases j <;> simp [trigTwelfthTable, trigTwelfthPole] at h ⊢ <;> grind
  · have hs : Real.sin (6*π/12) = 1 := by rw [show (6:ℝ)*π/12 = π/2 by ring, Real.sin_pi_div_two]
    have hc : Real.cos (6*π/12) = 0 := by rw [show (6:ℝ)*π/12 = π/2 by ring, Real.cos_pi_div_two]
    rw [key _ _ _ (by simpa using hs) (by simpa using hc)]
    fin_cases j <;> simp [trigTwelfthTable, trigTwelfthPole] at h ⊢
  · have hs : Real.sin (7*π/12) = Real.sqrt 2 * (Real.sqrt 3 + 1) / 4 := by
      rw [show (7:ℝ)*π/12 = π - (π/2 - π/12) by ring, Real.sin_pi_sub, Real.sin_pi_div_two_sub, c1]
    have hc : Real.cos (7*π/12) = -(Real.sqrt 2 * (Real.sqrt 3 - 1) / 4) := by
      rw [show (7:ℝ)*π/12 = π - (π/2 - π/12) by ring, Real.cos_pi_sub, Real.cos_pi_div_two_sub, s1]
    rw [key _ _ _ (by simpa using hs) (by simpa using hc)]
    fin_cases j <;> simp [trigTwelfthTable, trigTwelfthPole] at h ⊢ <;> grind
  · have hs : Real.sin (8*π/12) = Real.sqrt 3/2 := by
      rw [show (8:ℝ)*π/12 = π - (π/3) by ring, Real.sin_pi_sub, Real.sin_pi_div_three]
    have hc : Real.cos (8*π/12) = -(1/2) := by
      rw [show (8:ℝ)*π/12 = π - (π/3) by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
    rw [key _ _ _ (by simpa using hs) (by simpa using hc)]
    fin_cases j <;> simp [trigTwelfthTable, trigTwelfthPole] at h ⊢ <;> grind
  · have hs : Real.sin (9*π/12) = Real.sqrt 2/2 := by
      rw [show (9:ℝ)*π/12 = π - (π/4) by ring, Real.sin_pi_sub, Real.sin_pi_div_four]
    have hc : Real.cos (9*π/12) = -(Real.sqrt 2/2) := by
      rw [show (9:ℝ)*π/12 = π - (π/4) by ring, Real.cos_pi_sub, Real.cos_pi_div_four]
    rw [key _ _ _ (by simpa using hs) (by simpa using hc)]
    fin_cases j <;> simp [trigTwelfthTable, trigTwelfthPole] at h ⊢ <;> grind
  · have hs : Real.sin (10*π/12) = 1/2 := by
      rw [show (10:ℝ)*π/12 = π - (π/6) by ring, Real.sin_pi_sub, Real.sin_pi_div_six]
    have hc : Real.cos (10*π/12) = -(Real.sqrt 3/2) := by
      rw [show (10:ℝ)*π/12 = π - (π/6) by ring, Real.cos_pi_sub, Real.cos_pi_div_six]
    rw [key _ _ _ (by simpa using hs) (by simpa using hc)]
    fin_cases j <;> simp [trigTwelfthTable, trigTwelfthPole] at h ⊢ <;> grind
  · have hs : Real.sin (11*π/12) = Real.sqrt 2 * (Real.sqrt 3 - 1) / 4 := by
      rw [show (11:ℝ)*π/12 = π - (π/12) by ring, Real.sin_pi_sub, s1]
    have hc : Real.cos (11*π/12) = -(Real.sqrt 2 * (Real.sqrt 3 + 1) / 4) := by
      rw [show (11:ℝ)*π/12 = π - (π/12) by ring, Real.cos_pi_sub, c1]
    rw [key _ _ _ (by simpa using hs) (by simpa using hc)]
    fin_cases j <;> simp [trigTwelfthTable, trigTwelfthPole] at h ⊢ <;> grind
  · rw [key _ 0 (-1) (by simp) (by simp)]
    fin_cases j <;> simp [trigTwelfthTable, trigTwelfthPole] at h ⊢

/-- Real reciprocal blow-up at a simple zero. -/
lemma trigR4_real_pole {g h : ℝ → ℝ} {a : ℝ} {g' : ℝ} (hg : HasDerivAt g g' a) (hg' : g' ≠ 0)
    (hga : g a = 0) (hh : ContinuousAt h a) (hha : h a ≠ 0) :
    Tendsto (fun θ => |h θ * (g θ)⁻¹|) (𝓝[≠] a) atTop := by
  have hne : ∀ᶠ θ in 𝓝[≠] a, g θ ≠ 0 := by simpa [hga] using hg.eventually_ne hg'
  have h0 : Tendsto (fun θ => |g θ|) (𝓝[≠] a) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := (hg.continuousAt.abs).tendsto.mono_left (nhdsWithin_le_nhds (s := {a}ᶜ))
      simpa [hga] using this
    · filter_upwards [hne] with θ hθ using abs_pos.mpr hθ
  have hinv := tendsto_inv_nhdsGT_zero.comp h0
  have hn : Tendsto (fun θ => |h θ|) (𝓝[≠] a) (𝓝 |h a|) :=
    (hh.abs).tendsto.mono_left nhdsWithin_le_nhds
  have := hn.pos_mul_atTop (abs_pos.mpr hha) hinv
  refine this.congr' (Eventually.of_forall fun θ => ?_)
  simp [abs_mul, abs_inv]

/-- DLMF 4.17.T1: trig twelfth poles. -/
@[dlmf 4.17.T1]
theorem trig_twelfth_poles (q : Fin 13) (j : Fin 6) (h : trigTwelfthPole q j) :
    Tendsto (fun θ : ℝ => |trigRealVector θ j|) (𝓝[≠] ((q:ℝ)*π/12)) atTop := by
  have hsin : ∀ a : ℝ, Real.sin a = 0 → Real.cos a ≠ 0 →
      Tendsto (fun θ : ℝ => |1 * (Real.sin θ)⁻¹|) (𝓝[≠] a) atTop ∧
      Tendsto (fun θ : ℝ => |Real.cos θ * (Real.sin θ)⁻¹|) (𝓝[≠] a) atTop := fun a h0 hc =>
    ⟨trigR4_real_pole (Real.hasDerivAt_sin a) hc h0 continuousAt_const one_ne_zero,
     trigR4_real_pole (Real.hasDerivAt_sin a) hc h0 Real.continuous_cos.continuousAt hc⟩
  have hcos : ∀ a : ℝ, Real.cos a = 0 → Real.sin a ≠ 0 →
      Tendsto (fun θ : ℝ => |1 * (Real.cos θ)⁻¹|) (𝓝[≠] a) atTop ∧
      Tendsto (fun θ : ℝ => |Real.sin θ * (Real.cos θ)⁻¹|) (𝓝[≠] a) atTop := fun a h0 hs =>
    ⟨trigR4_real_pole (Real.hasDerivAt_cos a) (neg_ne_zero.mpr hs) h0 continuousAt_const one_ne_zero,
     trigR4_real_pole (Real.hasDerivAt_cos a) (neg_ne_zero.mpr hs) h0 Real.continuous_sin.continuousAt hs⟩
  simp only [trigTwelfthPole] at h
  rcases h with ⟨hq | hq, hj | hj⟩ | ⟨hq, hj | hj⟩ <;> subst hq <;> subst hj
  · simpa [trigRealVector] using (hsin 0 (by simp) (by simp)).1
  · simpa [trigRealVector, Real.cot_eq_cos_div_sin, div_eq_mul_inv] using (hsin 0 (by simp) (by simp)).2
  · simpa [trigRealVector] using (hsin π (by simp) (by simp)).1
  · have e : ((12:Fin 13):ℝ)*π/12 = π := by norm_num
    rw [e]
    simpa [trigRealVector, Real.cot_eq_cos_div_sin, div_eq_mul_inv] using (hsin π (by simp) (by simp)).2
  · have e : ((6:Fin 13):ℝ)*π/12 = π/2 := by norm_num; ring
    rw [e]
    simpa [trigRealVector, Real.tan_eq_sin_div_cos, div_eq_mul_inv] using (hcos (π/2) (by simp) (by simp)).2
  · have e : ((6:Fin 13):ℝ)*π/12 = π/2 := by norm_num; ring
    rw [e]
    simpa [trigRealVector] using (hcos (π/2) (by simp) (by simp)).1

/-- Real inverse functions where the table specifies finite real values. -/
def inverseTrigRealVector (x : ℝ) : Fin 6→ℝ :=
  ![Real.arcsin x,Real.arccos x,Real.arctan x,Real.arcsin x⁻¹,Real.arccos x⁻¹,Real.arctan x⁻¹]

/-- DLMF 4.23.T1: inverse trig exact table. -/
@[dlmf 4.23.T1]
theorem inverse_trig_exact_table (q : Fin 3) (j : Fin 6) (h : q≠1 ∨ (j:ℕ)<3) :
    inverseTrigRealVector ((q:ℝ)-1) j=
      (![![-π/2,π,-π/4,-π/2,π,-π/4],![0,π/2,0,0,0,0],![π/2,0,π/4,π/2,0,π/4]] : Fin 3→Fin 6→ℝ) q j := by
  fin_cases q <;> fin_cases j <;>
    norm_num [inverseTrigRealVector,Real.arcsin_neg,Real.arccos_neg,Real.arctan_neg,neg_div] at *

/-- DLMF 4.23.T1: inverse reciprocal limits. -/
@[dlmf 4.23.T1]
theorem inverse_reciprocal_limits (positive : Bool) :
    Tendsto (fun x : ℝ => Real.arcsin x⁻¹) (if positive then atTop else atBot) (𝓝 0) ∧
    Tendsto (fun x : ℝ => Real.arccos x⁻¹) (if positive then atTop else atBot) (𝓝 (π/2)) ∧
    Tendsto (fun x : ℝ => Real.arctan x⁻¹) (if positive then atTop else atBot) (𝓝 0) := by
  have hi : Tendsto (fun x : ℝ => x⁻¹) (if positive then atTop else atBot) (𝓝 0) := by
    cases positive
    · exact tendsto_inv_atBot_zero
    · exact tendsto_inv_atTop_zero
  exact ⟨by simpa [Function.comp_def] using (Real.continuous_arcsin.tendsto 0).comp hi,
    by simpa [Function.comp_def] using (Real.continuous_arccos.tendsto 0).comp hi,
    by simpa [Function.comp_def] using (Real.continuous_arctan.tendsto 0).comp hi⟩

/-- DLMF 4.23.T1: arccot zero bank limits. -/
@[dlmf 4.23.T1]
theorem arccot_zero_bank_limits :
    Tendsto (fun x : ℝ => Real.arctan x⁻¹) (𝓝[>] 0) (𝓝 (π/2)) ∧
    Tendsto (fun x : ℝ => Real.arctan x⁻¹) (𝓝[<] 0) (𝓝 (-π/2)) := by
  constructor
  · have h := (Real.continuous_arctan.continuousAt (x:=0)).const_sub (Real.pi/2)
    have heq : (fun x : ℝ => Real.arctan x⁻¹)=ᶠ[𝓝[>] 0]
        (fun x => Real.pi/2-Real.arctan x) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact Real.arctan_inv_of_pos hx
    simpa using (h.mono_left nhdsWithin_le_nhds).congr' heq.symm
  · have h := (Real.continuous_arctan.continuousAt (x:=0)).const_sub (-Real.pi/2)
    have heq : (fun x : ℝ => Real.arctan x⁻¹)=ᶠ[𝓝[<] 0]
        (fun x => -Real.pi/2-Real.arctan x) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      simpa only [neg_div] using Real.arctan_inv_of_neg hx
    simpa using (h.mono_left nhdsWithin_le_nhds).congr' heq.symm

/-- The prose inverse secant/cotangent interrelation, with positive real finite principal roots. -/
@[dlmf 4.23.vii]
theorem arcsec_arccot_interrelation {a : ℝ} (ha : 1<a) :
    Real.arccos a⁻¹=Real.arctan (Real.sqrt (a^2-1)) := by
  rw [Real.arccos_eq_arctan (inv_pos.mpr (lt_trans zero_lt_one ha)),trig_sqrt_inverse ha]
  congr 1
  field_simp



/-! ## Antiderivatives and conditionally convergent improper integrals -/

/-- DLMF 4.26.E3: hasDerivAt neg log cos. -/
@[dlmf 4.26.E3]
theorem hasDerivAt_neg_log_cos {x : ℝ} (hx : |x|<π/2) : HasDerivAt (fun x : ℝ => -Real.log (Real.cos x)) (Real.tan x) x := by
  have hc : Real.cos x≠0 := (Real.cos_pos_of_mem_Ioo (abs_lt.mp hx)).ne'
  convert ((Real.hasDerivAt_cos x).log hc).neg using 1
  simp only [Real.tan_eq_sin_div_cos]
  ring

/-- DLMF 4.26.E4: hasDerivAt log tan half. -/
@[dlmf 4.26.E4]
theorem hasDerivAt_log_tan_half {x : ℝ} (hx : x∈Ioo 0 π) : HasDerivAt (fun x : ℝ => Real.log (Real.tan (x/2))) ((Real.sin x)⁻¹) x := by
  have hhalf : x/2∈Ioo (-(π/2)) (π/2) := ⟨by linarith [Real.pi_pos,hx.1],by linarith [hx.2]⟩
  have hc : Real.cos (x/2)≠0 := (Real.cos_pos_of_mem_Ioo hhalf).ne'
  have hs : Real.sin (x/2)≠0 := (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2,Real.pi_pos])).ne'
  have ht : Real.tan (x/2)≠0 := by simpa only [Real.tan_eq_sin_div_cos] using div_ne_zero hs hc
  have hd0 : HasDerivAt (fun t:ℝ=>Real.tan (t/2)) (1/Real.cos (x/2)^2*(1/2)) x := by
    exact (Real.hasDerivAt_tan (x:=x/2) hc).comp x ((hasDerivAt_id x).div_const (2:ℝ))
  have hd:=hd0.log ht
  convert hd using 1
  rw [Real.tan_eq_sin_div_cos]
  have hsin : Real.sin x=2*Real.sin (x/2)*Real.cos (x/2) := by
    rw [← Real.sin_two_mul,show (2:ℝ)*(x/2)=x by ring]
  rw [hsin]
  field_simp


/-- DLMF 4.26.E5: hasDerivAt inverse gudermannian. -/
@[dlmf 4.26.E5]
theorem hasDerivAt_inverse_gudermannian {x : ℝ} (hx : |x|<π/2) : HasDerivAt (inverseGudermannian) ((Real.cos x)⁻¹) x := by
  have hcos : ∀t∈uIcc (0:ℝ) x,Real.cos t≠0 := by
    intro t ht
    apply (Real.cos_pos_of_mem_Ioo _).ne'
    rcases le_total 0 x with h|h
    · rw [uIcc_of_le h] at ht
      exact ⟨by linarith [ht.1,Real.pi_pos],by linarith [ht.2,(abs_lt.mp hx).2]⟩
    · rw [uIcc_of_ge h] at ht
      exact ⟨by linarith [ht.1,(abs_lt.mp hx).1],by linarith [ht.2,Real.pi_pos]⟩
  have hcont : ContinuousOn (fun t:ℝ=>(Real.cos t)⁻¹) (uIcc 0 x) := Real.continuous_cos.continuousOn.inv₀ hcos
  have hxcos : Real.cos x≠0 := (Real.cos_pos_of_mem_Ioo (abs_lt.mp hx)).ne'
  apply intervalIntegral.integral_hasDerivAt_right hcont.intervalIntegrable
  · exact Real.continuous_cos.measurable.inv.aestronglyMeasurable.stronglyMeasurableAtFilter
  · exact Real.continuous_cos.continuousAt.inv₀ hxcos


/-- DLMF 4.26.E6: hasDerivAt log sin. -/
@[dlmf 4.26.E6]
theorem hasDerivAt_log_sin {x : ℝ} (hx : x∈Ioo 0 π) : HasDerivAt (fun x : ℝ => Real.log (Real.sin x)) (Real.cot x) x := by
  have hs : Real.sin x≠0 := (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2).ne'
  simpa only [Real.cot_eq_cos_div_sin] using (Real.hasDerivAt_sin x).log hs

/-- The exponential-trigonometric primitive, valid for complex parameters when its denominator is nonzero. -/
@[dlmf 4.26.E7]
theorem hasDerivAt_exp_sin_antiderivative {a b : ℂ} (h : a^2+b^2≠0) (z : ℂ) :
    HasDerivAt (fun z : ℂ => Complex.exp (a*z)/(a^2+b^2)*(a*Complex.sin (b*z)-b*Complex.cos (b*z)))
      (Complex.exp (a*z)*Complex.sin (b*z)) z := by
  have hd := ((((hasDerivAt_id z).const_mul a).cexp.div_const (a^2+b^2)).mul
    ((((hasDerivAt_id z).const_mul b).csin.const_mul a).sub
      (((hasDerivAt_id z).const_mul b).ccos.const_mul b)))
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
    field_simp
    ring

/-- The exponential-trigonometric primitive, valid for complex parameters when its denominator is nonzero. -/
@[dlmf 4.26.E8]
theorem hasDerivAt_exp_cos_antiderivative {a b : ℂ} (h : a^2+b^2≠0) (z : ℂ) :
    HasDerivAt (fun z : ℂ => Complex.exp (a*z)/(a^2+b^2)*(a*Complex.cos (b*z)+b*Complex.sin (b*z)))
      (Complex.exp (a*z)*Complex.cos (b*z)) z := by
  have hd := ((((hasDerivAt_id z).const_mul a).cexp.div_const (a^2+b^2)).mul
    ((((hasDerivAt_id z).const_mul b).ccos.const_mul a).add
      (((hasDerivAt_id z).const_mul b).csin.const_mul b)))
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
    field_simp
    ring

/-- Integer sine orthogonality requires both m not equal n and m not equal -n. -/
@[dlmf 4.26.E9]
theorem integral_sin_integer_orthogonal (m n : ℤ) (hne : m≠n) (hneg : m≠ -n) :
    (∫ t in (0:ℝ)..π,Real.sin ((m:ℝ)*t)*Real.sin ((n:ℝ)*t))=0 := by
  have hp : m+n≠0 := by omega
  have hm : m-n≠0 := by omega
  have hc (k : ℤ) : IntervalIntegrable (fun t : ℝ => Real.cos ((k:ℝ)*t)) volume 0 Real.pi :=
    (by fun_prop : Continuous (fun t : ℝ => Real.cos ((k:ℝ)*t))).intervalIntegrable _ _
  have he : ∀ t : ℝ,Real.sin ((m:ℝ)*t)*Real.sin ((n:ℝ)*t)=
      (Real.cos (((m-n:ℤ):ℝ)*t)-Real.cos (((m+n:ℤ):ℝ)*t))/2 := by
    intro t
    push_cast
    rw [sub_mul,add_mul,Real.cos_sub,Real.cos_add]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_div,intervalIntegral.integral_sub (hc _) (hc _),
    TauCeti.integral_cos_int_mul,TauCeti.integral_cos_int_mul,if_neg hm,if_neg hp]
  norm_num

/-- Integer cosine orthogonality with the missing opposite-frequency exclusion. -/
@[dlmf 4.26.E10]
theorem integral_cos_integer_orthogonal (m n : ℤ) (hne : m≠n) (hneg : m≠ -n) :
    (∫ t in (0:ℝ)..π,Real.cos ((m:ℝ)*t)*Real.cos ((n:ℝ)*t))=0 := by
  have hp : m+n≠0 := by omega
  have hm : m-n≠0 := by omega
  have hc (k : ℤ) : IntervalIntegrable (fun t : ℝ => Real.cos ((k:ℝ)*t)) volume 0 Real.pi :=
    (by fun_prop : Continuous (fun t : ℝ => Real.cos ((k:ℝ)*t))).intervalIntegrable _ _
  have he : ∀ t : ℝ,Real.cos ((m:ℝ)*t)*Real.cos ((n:ℝ)*t)=
      (Real.cos (((m-n:ℤ):ℝ)*t)+Real.cos (((m+n:ℤ):ℝ)*t))/2 := by
    intro t
    push_cast
    rw [sub_mul,add_mul,Real.cos_sub,Real.cos_add]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_div,intervalIntegral.integral_add (hc _) (hc _),
    TauCeti.integral_cos_int_mul,TauCeti.integral_cos_int_mul,if_neg hm,if_neg hp]
  norm_num

/-- DLMF 4.26.E11: integral trig integer squares. -/
@[dlmf 4.26.E11]
theorem integral_trig_integer_squares {n : ℤ} (hn : n≠0) :
    (∫ t in (0:ℝ)..π,(Real.sin ((n:ℝ)*t))^2)=π/2 ∧
    (∫ t in (0:ℝ)..π,(Real.cos ((n:ℝ)*t))^2)=π/2 := by
  have hn' : (n:ℝ)≠0 := Int.cast_ne_zero.mpr hn
  constructor
  · have h := intervalIntegral.mul_integral_comp_mul_left
      (f:=fun x : ℝ => Real.sin x^2) (a:=(0:ℝ)) (b:=Real.pi) (n:ℝ)
    rw [integral_sin_sq,mul_zero,Real.sin_zero,Real.sin_int_mul_pi] at h
    apply mul_left_cancel₀ hn'
    convert h using 1 <;> ring
  · have h := intervalIntegral.mul_integral_comp_mul_left
      (f:=fun x : ℝ => Real.cos x^2) (a:=(0:ℝ)) (b:=Real.pi) (n:ℝ)
    rw [integral_cos_sq,mul_zero,Real.sin_zero,Real.sin_int_mul_pi] at h
    apply mul_left_cancel₀ hn'
    convert h using 1 <;> ring

/-- Dirichlet integral as an ordered improper limit, stronger real frequency version. -/
@[dlmf 4.26.E12]
theorem dirichlet_integral_scaled (m : ℝ) :
    Tendsto (fun R : ℝ => ∫ t in (0:ℝ)..R,Real.sin (m*t)/t) atTop
      (𝓝 (trigRealSign m*π/2)) := by
  rcases lt_trichotomy m 0 with h | h | h
  · have := (TauCeti.Contour.tendsto_integral_sin_mul_div_atTop (neg_pos.mpr h)).neg
    have hs : trigRealSign m = -1 := by simp [trigRealSign, h, not_lt.mpr h.le]
    rw [hs]
    convert this using 1
    · funext R
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [neg_mul, Real.sin_neg]; ring
    · ring_nf
  · subst h; simp [trigRealSign]
  · have hs : trigRealSign m = 1 := by simp [trigRealSign, h]
    rw [hs, one_mul]
    exact TauCeti.Contour.tendsto_integral_sin_mul_div_atTop h

/-- DLMF 4.26.E13: fresnel integrals elementary. -/
@[dlmf 4.26.E13]
theorem fresnel_integrals_elementary :
    Tendsto (fun R : ℝ => ∫ t in (0:ℝ)..R,Real.sin (t^2)) atTop (𝓝 (Real.sqrt (π/2)/2)) ∧
    Tendsto (fun R : ℝ => ∫ t in (0:ℝ)..R,Real.cos (t^2)) atTop (𝓝 (Real.sqrt (π/2)/2)) := by
  have hv : Real.Gamma (1 + 1 / ((2:ℕ):ℝ)) = Real.sqrt π / 2 := by
    rw [show (1:ℝ) + 1/((2:ℕ):ℝ) = 1/2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]; ring
  have he : Real.sqrt π / 2 * (Real.sqrt 2 / 2) = Real.sqrt (π/2)/2 := by
    rw [Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 2)]
    have h2 : 0 < Real.sqrt 2 := by positivity
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hp : π / (2 * ((2:ℕ):ℝ)) = π/4 := by norm_num
  constructor
  · have := DLMF.Gamma.Gamma_sin_pow 2 le_rfl
    rwa [hv, hp, Real.sin_pi_div_four, he] at this
  · have := DLMF.Gamma.Gamma_cos_pow 2 le_rfl
    rwa [hv, hp, Real.cos_pi_div_four, he] at this

/-- DLMF 4.26.E14: hasDerivAt arcsin antiderivative. -/
@[dlmf 4.26.E14]
theorem hasDerivAt_arcsin_antiderivative {x : ℝ} (hx : |x|<1) : HasDerivAt (fun x : ℝ => x*Real.arcsin x+Real.sqrt (1-x^2)) (Real.arcsin x) x := by
  have hx1 : x≠1 := ne_of_lt (abs_lt.mp hx).2
  have hxm : x≠ -1 := ne_of_gt (abs_lt.mp hx).1
  have hs : 0<1-x^2 := by nlinarith [(abs_lt.mp hx).1,(abs_lt.mp hx).2]
  have hroot := Real.sq_sqrt hs.le
  have hroot0 : Real.sqrt (1-x^2)≠0 := (Real.sqrt_pos.mpr hs).ne'
  have hd := ((hasDerivAt_id x).mul (Real.hasDerivAt_arcsin hxm hx1)).add
    ((((hasDerivAt_id x).pow 2).const_sub 1).sqrt (ne_of_gt hs))
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul] <;> field_simp <;> nlinarith

/-- DLMF 4.26.E15: hasDerivAt arccos antiderivative. -/
@[dlmf 4.26.E15]
theorem hasDerivAt_arccos_antiderivative {x : ℝ} (hx : |x|<1) : HasDerivAt (fun x : ℝ => x*Real.arccos x-Real.sqrt (1-x^2)) (Real.arccos x) x := by
  have hx1 : x≠1 := ne_of_lt (abs_lt.mp hx).2
  have hxm : x≠ -1 := ne_of_gt (abs_lt.mp hx).1
  have hs : 0<1-x^2 := by nlinarith [(abs_lt.mp hx).1,(abs_lt.mp hx).2]
  have hroot := Real.sq_sqrt hs.le
  have hroot0 : Real.sqrt (1-x^2)≠0 := (Real.sqrt_pos.mpr hs).ne'
  have hd := ((hasDerivAt_id x).mul (Real.hasDerivAt_arccos hxm hx1)).sub
    ((((hasDerivAt_id x).pow 2).const_sub 1).sqrt (ne_of_gt hs))
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul] <;> field_simp <;> nlinarith

/-- DLMF 4.26.E16: hasDerivAt arctan antiderivative. -/
@[dlmf 4.26.E16]
theorem hasDerivAt_arctan_antiderivative {x : ℝ} : HasDerivAt (fun x : ℝ => x*Real.arctan x-Real.log (1+x^2)/2) (Real.arctan x) x := by
  have hlog : (1+x^2:ℝ)≠0 := by positivity
  have hd := ((hasDerivAt_id x).mul (Real.hasDerivAt_arctan x)).sub
    ((((hasDerivAt_id x).pow 2).const_add 1).log hlog |>.div_const 2)
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
    field_simp
    ring

/-- DLMF 4.26.E17: hasDerivAt arccsc antiderivative. -/
@[dlmf 4.26.E17]
theorem hasDerivAt_arccsc_antiderivative {x : ℝ} (hx : 1<x) : HasDerivAt (fun x : ℝ => x*Real.arcsin x⁻¹+Real.log (x+Real.sqrt (x^2-1))) (Real.arcsin x⁻¹) x := by
  have hx0 : 0<x := lt_trans zero_lt_one hx
  have hi : x⁻¹<1 := inv_lt_one_of_one_lt₀ hx
  have hip : 0<x⁻¹ := inv_pos.mpr hx0
  have hxm : x⁻¹≠ -1 := by linarith
  have hs : 0<x^2-1 := by nlinarith
  have hs0 : Real.sqrt (x^2-1)≠0 := (Real.sqrt_pos.mpr hs).ne'
  have hinv : HasDerivAt (fun t:ℝ=>Real.arcsin t⁻¹) ((Real.sqrt (1-x⁻¹^2))⁻¹ * (-1/x^2)) x := by
    simpa only [one_div,id_eq,Function.comp_def] using (Real.hasDerivAt_arcsin hxm hi.ne).comp x ((hasDerivAt_id x).inv hx0.ne')
  have hd := ((hasDerivAt_id x).mul hinv).add (Real.hasDerivAt_arcosh hx)
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.add_apply]
    rw [trig_sqrt_inverse hx]
    field_simp
    ring


/-- DLMF 4.26.E18: hasDerivAt arcsec antiderivative. -/
@[dlmf 4.26.E18]
theorem hasDerivAt_arcsec_antiderivative {x : ℝ} (hx : 1<x) : HasDerivAt (fun x : ℝ => x*Real.arccos x⁻¹-Real.log (x+Real.sqrt (x^2-1))) (Real.arccos x⁻¹) x := by
  have hx0 : 0<x := lt_trans zero_lt_one hx
  have hi : x⁻¹<1 := inv_lt_one_of_one_lt₀ hx
  have hip : 0<x⁻¹ := inv_pos.mpr hx0
  have hxm : x⁻¹≠ -1 := by linarith
  have hs : 0<x^2-1 := by nlinarith
  have hs0 : Real.sqrt (x^2-1)≠0 := (Real.sqrt_pos.mpr hs).ne'
  have hinv : HasDerivAt (fun t:ℝ=>Real.arccos t⁻¹) (-(Real.sqrt (1-x⁻¹^2))⁻¹ * (-1/x^2)) x := by
    simpa only [one_div,id_eq,Function.comp_def] using (Real.hasDerivAt_arccos hxm hi.ne).comp x ((hasDerivAt_id x).inv hx0.ne')
  have hd := ((hasDerivAt_id x).mul hinv).sub (Real.hasDerivAt_arcosh hx)
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply]
    rw [trig_sqrt_inverse hx]
    field_simp
    ring


/-- DLMF 4.26.E19: hasDerivAt arccot antiderivative. -/
@[dlmf 4.26.E19]
theorem hasDerivAt_arccot_antiderivative {x : ℝ} (hx : 0<x) : HasDerivAt (fun x : ℝ => x*Real.arctan x⁻¹+Real.log (1+x^2)/2) (Real.arctan x⁻¹) x := by
  have hx0 : x≠0 := hx.ne'
  have hlog : (1+x^2:ℝ)≠0 := by positivity
  have hd := ((hasDerivAt_id x).mul ((hasDerivAt_id x).inv hx0 |>.arctan)).add
    ((((hasDerivAt_id x).pow 2).const_add 1).log hlog |>.div_const 2)
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.inv_apply,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
    field_simp
    ring


/-- DLMF 4.26.E20: hasDerivAt mul arcsin antiderivative. -/
@[dlmf 4.26.E20]
theorem hasDerivAt_mul_arcsin_antiderivative {x : ℝ} (hx : |x|<1) : HasDerivAt (fun x : ℝ => (x^2/2-1/4)*Real.arcsin x+x/4*Real.sqrt (1-x^2)) (x*Real.arcsin x) x := by
  have hx1 : x≠1 := ne_of_lt (abs_lt.mp hx).2
  have hxm : x≠ -1 := ne_of_gt (abs_lt.mp hx).1
  have hs : 0<1-x^2 := by nlinarith [(abs_lt.mp hx).1,(abs_lt.mp hx).2]
  have hroot := Real.sq_sqrt hs.le
  have hroot0 : Real.sqrt (1-x^2)≠0 := (Real.sqrt_pos.mpr hs).ne'
  have hd := ((((hasDerivAt_id x).pow 2).div_const 2 |>.sub_const (1/4)).mul
    (Real.hasDerivAt_arcsin hxm hx1)).add
    (((hasDerivAt_id x).div_const 4).mul
      ((((hasDerivAt_id x).pow 2).const_sub 1).sqrt (ne_of_gt hs)))
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul] <;> field_simp <;> nlinarith

/-- DLMF 4.26.E21: hasDerivAt mul arccos antiderivative. -/
@[dlmf 4.26.E21]
theorem hasDerivAt_mul_arccos_antiderivative {x : ℝ} (hx : |x|<1) : HasDerivAt (fun x : ℝ => (x^2/2-1/4)*Real.arccos x-x/4*Real.sqrt (1-x^2)) (x*Real.arccos x) x := by
  have hx1 : x≠1 := ne_of_lt (abs_lt.mp hx).2
  have hxm : x≠ -1 := ne_of_gt (abs_lt.mp hx).1
  have hs : 0<1-x^2 := by nlinarith [(abs_lt.mp hx).1,(abs_lt.mp hx).2]
  have hroot := Real.sq_sqrt hs.le
  have hroot0 : Real.sqrt (1-x^2)≠0 := (Real.sqrt_pos.mpr hs).ne'
  have hd := ((((hasDerivAt_id x).pow 2).div_const 2 |>.sub_const (1/4)).mul
    (Real.hasDerivAt_arccos hxm hx1)).sub
    (((hasDerivAt_id x).div_const 4).mul
      ((((hasDerivAt_id x).pow 2).const_sub 1).sqrt (ne_of_gt hs)))
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul] <;> field_simp <;> nlinarith

/-- Complex antiderivatives use local continuous logarithm branches and exclude reciprocal poles. -/
@[dlmf 4.26.i]
theorem complex_trig_log_primitives {U : Set ℂ} (hU : IsOpen U) {L : ℂ→ℂ}
    (hL : AnalyticOnNhd ℂ L U) {z : ℂ} (hz : z∈U) :
    ((∀ w∈U,Complex.exp (L w)=Complex.cos w) → HasDerivAt (fun w => -L w) (Complex.tan z) z) ∧
    ((∀ w∈U,Complex.exp (L w)=Complex.sin w) → HasDerivAt L (Complex.cot z) z) ∧
    ((∀ w∈U,Complex.exp (L w)=sec w+Complex.tan w) →
      Complex.cos z≠0 → HasDerivAt L (sec z) z) := by
  have hdL:HasDerivAt L (deriv L z) z := (hL z hz).differentiableAt.hasDerivAt
  have hlog {f:ℂ→ℂ} {d:ℂ} (hf:HasDerivAt f d z)
      (he:∀w∈U,Complex.exp (L w)=f w) : HasDerivAt L (d/f z) z := by
    have heq:(fun w=>Complex.exp (L w))=ᶠ[𝓝 z] f := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact he w hw
    have hdexp:=hdL.cexp
    have hdeq:=hdexp.unique (hf.congr_of_eventuallyEq heq)
    have hf0:f z≠0 := by rw [← he z hz]; exact Complex.exp_ne_zero _
    convert hdL using 1
    rw [← hdeq,he z hz]
    field_simp
  refine ⟨?_,?_,?_⟩
  · intro he
    have hd:=(hlog (Complex.hasDerivAt_cos z) he).neg
    convert hd using 1
    simp [Complex.tan,neg_div]
  · intro he
    simpa only [Complex.cot] using hlog (Complex.hasDerivAt_sin z) he
  · intro he hc
    have hd:=hlog ((hasDerivAt_sec hc).add (Complex.hasDerivAt_tan hc)) he
    have hdEq:sec z*Complex.tan z+1/(Complex.cos z)^2=(sec z+Complex.tan z)*sec z := by
      rw [sec]
      ring
    rw [hdEq] at hd
    have he0:sec z+Complex.tan z≠0 := by rw [← he z hz]; exact Complex.exp_ne_zero _
    simpa only [Pi.add_apply,mul_div_cancel_left₀ (sec z) he0] using hd



/-- Real phase-amplitude reduction with its argument convention made explicit. -/
@[dlmf 4.21.E1_5]
theorem trig_phase_amplitude (A B : ℝ) (u : ℂ) :
    (A:ℂ)*Complex.cos u+B*Complex.sin u=(Real.sqrt (A^2+B^2):ℂ)*
      Complex.cos (u-(Complex.arg ((A:ℂ)+B*I):ℂ)) := by
  let z:ℂ:=(A:ℂ)+B*I
  have hn:Real.sqrt (A^2+B^2)=‖z‖ := by
    rw [Complex.norm_def]
    congr 1
    simp [z,Complex.normSq]
    ring
  have hc:(‖z‖:ℂ)*Complex.cos (Complex.arg z:ℂ)=(A:ℂ) := by
    rw [← Complex.ofReal_cos,← Complex.ofReal_mul,Complex.norm_mul_cos_arg]
    simp [z]
  have hs:(‖z‖:ℂ)*Complex.sin (Complex.arg z:ℂ)=(B:ℂ) := by
    rw [← Complex.ofReal_sin,← Complex.ofReal_mul,Complex.norm_mul_sin_arg]
    simp [z]
  rw [hn,Complex.cos_sub]
  linear_combination -Complex.cos u*hc -Complex.sin u*hs


/-- The two rectangular hyperbolas bounding Euler's transformed arctangent domain. -/
@[dlmf 4.24.E6]
theorem arctan_euler_boundary (z : ℂ) :
    (z^2).re= -(1/2:ℝ) ↔ z.re^2-z.im^2= -(1/2:ℝ) := by
  simp [Complex.mul_re,pow_two]

/-- No analytic inverse branch of sine or cosine crosses either finite branch point. -/
@[dlmf 4.23.i]
theorem inverse_sin_cos_branch_points (a : ℂ) (ha : a=1 ∨ a= -1) :
    ¬∃ U : Set ℂ,IsOpen U ∧ a∈U ∧ ∃ f : ℂ→ℂ,AnalyticOnNhd ℂ f U ∧
      ((∀ z∈U,Complex.sin (f z)=z) ∨ (∀ z∈U,Complex.cos (f z)=z)) := by
  rintro ⟨U,hU,haU,f,hf,hInv⟩
  have hdf:=(hf a haU).differentiableAt.hasDerivAt
  rcases hInv with hs|hc
  · have hzero:Complex.cos (f a)=0 := by
      apply sq_eq_zero_iff.mp
      rw [Complex.cos_sq',hs a haU]
      rcases ha with rfl|rfl <;> norm_num
    have hd:=(Complex.hasDerivAt_sin (f a)).comp a hdf
    rw [hzero,zero_mul] at hd
    have heq:id=ᶠ[𝓝 a] Complex.sin∘f := by
      filter_upwards [hU.mem_nhds haU] with z hz
      exact (hs z hz).symm
    have hcontra:=(hd.congr_of_eventuallyEq heq).unique (hasDerivAt_id a)
    norm_num at hcontra
  · have hzero:Complex.sin (f a)=0 := by
      apply sq_eq_zero_iff.mp
      rw [Complex.sin_sq,hc a haU]
      rcases ha with rfl|rfl <;> norm_num
    have hd:=(Complex.hasDerivAt_cos (f a)).comp a hdf
    rw [hzero,neg_zero,zero_mul] at hd
    have heq:id=ᶠ[𝓝 a] Complex.cos∘f := by
      filter_upwards [hU.mem_nhds haU] with z hz
      exact (hc z hz).symm
    have hcontra:=(hd.congr_of_eventuallyEq heq).unique (hasDerivAt_id a)
    norm_num at hcontra


/-- The logarithmic tangent branch points have no finite nonpolar inverse images. -/
@[dlmf 4.23.i]
theorem inverse_tan_cot_branch_points (a : ℂ) (ha : a=I ∨ a= -I) :
    arctanGeneral a=∅ ∧ arccotGeneral a=∅ := by
  have ha2:a^2= -1 := by rcases ha with rfl|rfl <;> simp
  constructor
  · apply Set.eq_empty_iff_forall_notMem.mpr
    rintro w ⟨hc,ht⟩
    have hs:Complex.sin w=a*Complex.cos w := (div_eq_iff hc).mp ht
    have hp:=Complex.sin_sq_add_cos_sq w
    rw [hs,mul_pow,ha2] at hp
    ring_nf at hp
    norm_num at hp
  · apply Set.eq_empty_iff_forall_notMem.mpr
    rintro w ⟨hs,ht⟩
    have hc:Complex.cos w=a*Complex.sin w := (div_eq_iff hs).mp ht
    have hp:=Complex.sin_sq_add_cos_sq w
    rw [hc,mul_pow,ha2] at hp
    ring_nf at hp
    norm_num at hp


/-- Reciprocal inverse sine/cosine branches have the same endpoint obstructions. -/
@[dlmf 4.23.i]
theorem inverse_reciprocal_branch_points (a : ℂ) (ha : a=1 ∨ a= -1) :
    ¬∃ U : Set ℂ,IsOpen U ∧ a∈U ∧ ∃ f : ℂ→ℂ,AnalyticOnNhd ℂ f U ∧
      ((∀ z∈U,Complex.sin (f z)≠0 ∧ csc (f z)=z) ∨
       (∀ z∈U,Complex.cos (f z)≠0 ∧ sec (f z)=z)) := by
  rintro ⟨U,hU,haU,f,hf,hInv⟩
  have hdf:=(hf a haU).differentiableAt.hasDerivAt
  have hai:a⁻¹=a := by rcases ha with rfl|rfl <;> norm_num
  rcases hInv with hs|hc
  · have hsval:Complex.sin (f a)=a := by
      simpa only [csc,inv_inv,hai] using congrArg Inv.inv (hs a haU).2
    have hzero:Complex.cos (f a)=0 := by
      apply sq_eq_zero_iff.mp
      rw [Complex.cos_sq',hsval]
      rcases ha with rfl|rfl <;> norm_num
    have hd:=(hasDerivAt_csc (hs a haU).1).comp a hdf
    have hcot:Complex.cot (f a)=0 := by simp [Complex.cot,hzero]
    rw [hcot,mul_zero,zero_mul] at hd
    have heq:id=ᶠ[𝓝 a] csc∘f := by
      filter_upwards [hU.mem_nhds haU] with z hz
      exact (hs z hz).2.symm
    have hcontra:=(hd.congr_of_eventuallyEq heq).unique (hasDerivAt_id a)
    norm_num at hcontra
  · have hcval:Complex.cos (f a)=a := by
      simpa only [sec,inv_inv,hai] using congrArg Inv.inv (hc a haU).2
    have hzero:Complex.sin (f a)=0 := by
      apply sq_eq_zero_iff.mp
      rw [Complex.sin_sq,hcval]
      rcases ha with rfl|rfl <;> norm_num
    have hd:=(hasDerivAt_sec (hc a haU).1).comp a hdf
    have htan:Complex.tan (f a)=0 := by simp [Complex.tan,hzero]
    rw [htan,mul_zero,zero_mul] at hd
    have heq:id=ᶠ[𝓝 a] sec∘f := by
      filter_upwards [hU.mem_nhds haU] with z hz
      exact (hc z hz).2.symm
    have hcontra:=(hd.congr_of_eventuallyEq heq).unique (hasDerivAt_id a)
    norm_num at hcontra


/-- Principal complex inverse-sine and cosine primitives on their common cut plane. -/
@[dlmf 4.26.i]
theorem complex_inverse_sin_cos_primitives {z : ℂ} (hz : z∈arcsinCutPlane) :
    HasDerivAt (fun w : ℂ => w*arcsinPrincipal w+Complex.sqrt (1-w^2)) (arcsinPrincipal z) z ∧
    HasDerivAt (fun w : ℂ => w*arccosPrincipal w-Complex.sqrt (1-w^2)) (arccosPrincipal z) z ∧
    HasDerivAt (fun w : ℂ => (w^2/2-1/4)*arcsinPrincipal w+w/4*Complex.sqrt (1-w^2))
      (z*arcsinPrincipal z) z ∧
    HasDerivAt (fun w : ℂ => (w^2/2-1/4)*arccosPrincipal w-w/4*Complex.sqrt (1-w^2))
      (z*arccosPrincipal z) z := by
  have hq:=trig_one_sub_sq_slit hz
  have hr:Complex.sqrt (1-z^2)≠0 := by
    intro h
    have hs:=trig_sqrt_sq (1-z^2)
    rw [h,zero_pow two_ne_zero] at hs
    exact (Complex.mem_slitPlane_iff_arg.mp hq).2 hs.symm
  have hS:HasDerivAt (fun w:ℂ=>Complex.sqrt (1-w^2)) (-z/Complex.sqrt (1-z^2)) z := by
    convert (trig_hasDerivAt_sqrt hq).comp z (((hasDerivAt_id z).pow 2).const_sub 1) using 1 <;>
      simp only [id_eq,Function.comp_def,Pi.pow_apply,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one] <;> ring
  have hA:=trig_hasDerivAt_arcsin hz
  have hC:=hasDerivAt_arccos_principal hz
  have hroot:=trig_sqrt_sq (1-z^2)
  refine ⟨?_,?_,?_,?_⟩
  · have hd:=((hasDerivAt_id z).mul hA).add hS
    convert hd using 1
    · rfl
    · dsimp only [id,Pi.mul_apply,Pi.add_apply]
      field_simp
      ring
  · have hd:=((hasDerivAt_id z).mul hC).sub hS
    convert hd using 1
    · rfl
    · dsimp only [id,Pi.mul_apply,Pi.sub_apply]
      field_simp
      ring
  · have hd:=((((hasDerivAt_id z).pow 2).div_const 2).sub_const (1/4)).mul hA |>.add
      (((hasDerivAt_id z).div_const 4).mul hS)
    convert hd using 1
    · rfl
    · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
      norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul]
      field_simp
      rw [hroot]
      ring
  · have hd:=((((hasDerivAt_id z).pow 2).div_const 2).sub_const (1/4)).mul hC |>.sub
      (((hasDerivAt_id z).div_const 4).mul hS)
    convert hd using 1
    · rfl
    · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
      norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul]
      field_simp
      rw [hroot]
      ring


/-- The complex arctangent primitive on its principal cut plane. -/
@[dlmf 4.26.i]
theorem complex_arctan_primitive {z : ℂ} (hz : z∈arctanCutPlane) :
    HasDerivAt (fun w : ℂ => w*Complex.arctan w-Complex.log (1+w^2)/2) (Complex.arctan z) z := by
  have hlog := (Complex.hasDerivAt_log (trig_one_add_sq_slit hz)).comp z
    (((hasDerivAt_id z).pow 2).const_add 1)
  have hd := ((hasDerivAt_id z).mul (trig_hasDerivAt_arctan hz)).sub (hlog.div_const 2)
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.pow_apply]
    field_simp
    ring


/-- Reciprocal inverse primitives on the right component, using principal square roots and logs. -/
@[dlmf 4.26.i]
theorem complex_reciprocal_inverse_primitives {z : ℂ} (hz : z∈arccscCutPlane) (hr : 0<z.re) :
    HasDerivAt (fun w : ℂ => w*arccscPrincipal w+Complex.log (w+Complex.sqrt (w^2-1)))
      (arccscPrincipal z) z ∧
    HasDerivAt (fun w : ℂ => w*arcsecPrincipal w-Complex.log (w+Complex.sqrt (w^2-1)))
      (arcsecPrincipal z) z := by
  have hq : z^2-1 ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    by_cases hy : z.im = 0
    · left
      have hv0 : (z⁻¹).im = 0 := by rw [Complex.inv_im, hy]; simp
      have hlt : |(z⁻¹).re| < 1 := hz.2.resolve_left (not_not.mpr hv0)
      have hNx : Complex.normSq z = z.re^2 := by rw [Complex.normSq_apply, hy]; ring
      have hux : (z⁻¹).re * z.re = 1 := by
        rw [Complex.inv_re, hNx]; field_simp
      have h1 : ((z⁻¹).re * z.re)^2 = 1 := by rw [hux]; norm_num
      simp only [Complex.sub_re, pow_two, Complex.mul_re, hy, Complex.one_re]
      nlinarith [abs_mul_abs_self (z⁻¹).re, abs_nonneg (z⁻¹).re, sq_nonneg z.re]
    · right
      simp only [Complex.sub_im, pow_two, Complex.mul_im, Complex.one_im]
      have : z.re*z.im ≠ 0 := mul_ne_zero hr.ne' hy
      intro h; apply this; linarith
  have hr0 : 0 ≤ (Complex.sqrt (z^2-1)).re := by
    rw [(trigR4_sqrt_re_im _).1]; exact Real.sqrt_nonneg _
  have hp : z + Complex.sqrt (z^2-1) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left; simp only [Complex.add_re]; linarith
  have hb0 : Complex.sqrt (z^2-1) ≠ 0 := by
    intro h
    have := trig_sqrt_sq (z^2-1); rw [h, zero_pow two_ne_zero] at this
    exact Complex.slitPlane_ne_zero hq this.symm
  have hp0 : z + Complex.sqrt (z^2-1) ≠ 0 := Complex.slitPlane_ne_zero hp
  have hS : HasDerivAt (fun w : ℂ => Complex.sqrt (w^2-1)) (z/Complex.sqrt (z^2-1)) z := by
    have hsq : HasDerivAt Complex.sqrt ((Complex.sqrt (z^2-1))⁻¹/2) (z^2-1) := by
      simpa only [Complex.sqrt,show (-1/2:ℂ)= -(2⁻¹:ℂ) by norm_num,Complex.cpow_neg] using
        Complex.hasDerivAt_sqrt hq
    have h1 := hsq.comp z (((hasDerivAt_id z).pow 2).sub_const 1)
    convert h1 using 1
    · funext w; rfl
    · simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
      field_simp
  have hL := (Complex.hasDerivAt_log hp).comp z ((hasDerivAt_id z).add hS)
  have hA := hasDerivAt_arccsc_principal hz hr.ne'
  have hzero : z ≠ 0 := hz.1
  simp only [hr, ite_true] at hA
  have hroot := trig_sqrt_sq (z^2-1)
  constructor
  · have hd := ((hasDerivAt_id z).mul hA).add hL
    convert hd using 1
    · rfl
    · simp only [id_eq]
      field_simp
      ring
  · have hA' : HasDerivAt arcsecPrincipal (1/(z*Complex.sqrt (z^2-1))) z := by
      have h := hA.const_sub ((π:ℂ)/2)
      convert h using 1
      · funext w; rw [arcsec_principal_complement]
      · ring
    have hd := ((hasDerivAt_id z).mul hA').sub hL
    convert hd using 1
    · rfl
    · simp only [id_eq]
      field_simp
      ring

/-- The inverse cotangent primitive away from the imaginary logarithm cuts. -/
@[dlmf 4.26.i]
theorem complex_arccot_primitive {z : ℂ} (hz : z∈arccotCutPlane) (hr : z.re≠0) :
    HasDerivAt (fun w : ℂ => w*arccotPrincipal w+Complex.log (1+w^2)/2) (arccotPrincipal z) z := by
  have hlog := (Complex.hasDerivAt_log (trig_one_add_sq_slit (Or.inl hr))).comp z
    (((hasDerivAt_id z).pow 2).const_add 1)
  have hd := ((hasDerivAt_id z).mul (hasDerivAt_arccot_principal hz)).add (hlog.div_const 2)
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.add_apply,Pi.pow_apply]
    field_simp
    ring


end DLMF.Elementary
