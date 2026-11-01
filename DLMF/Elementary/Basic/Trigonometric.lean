/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.SqrtDeriv
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ComplexDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

/-!
# Reciprocal trigonometric functions

This file defines the complex cosecant and secant of DLMF §4.14 and proves their basic
properties: the reciprocal relations, zeros and poles, meromorphy, derivatives and the
Pythagorean identities.

## Main definitions

* `csc`, `sec`: the complex cosecant and secant, totalized to zero at their poles
  (DLMF 4.14.5–4.14.6).

## Main results

* `cot_eq_inv_tan`, `cot_eq_neg_tan_add_half_pi`, `sec_eq_csc_add_half_pi`: DLMF 4.14.7,
  4.15.2, 4.15.3.
* `meromorphic_reciprocal_trig`, `reciprocal_trig_poles`, `cot_zeros`,
  `reciprocal_trig_nonzero`: zeros, poles and meromorphy (DLMF §4.14).
* `hasDerivAt_csc`, `hasDerivAt_sec`, `hasDerivAt_cot`: derivatives (DLMF 4.20.4–4.20.6).
* `sec_sq_eq`, `csc_sq_eq`: DLMF 4.21.13–4.21.14.
* `csc_neg`, `sec_neg`, `csc_zero`, `sec_zero`: parity and values at `0`.
* `trig_sqrt_sq`: the square of the principal square root.

## Implementation notes

Reciprocal functions are totalized at poles; identities that need finite values state the pole
exclusions. The identities, inequalities, series and products of DLMF §§4.14–4.22 are in
`DLMF.Elementary.Trigonometric.DirectIdentities`.
-/

@[expose] public noncomputable section

open Complex Filter Set

open scoped Real Topology

namespace DLMF.Elementary

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
theorem meromorphic_reciprocal_trig :
    Meromorphic csc ∧ Meromorphic sec ∧ Meromorphic Complex.cot := by
  have hs : Meromorphic Complex.sin := fun z =>
    (Complex.differentiable_sin.analyticAt z).meromorphicAt
  have hc : Meromorphic Complex.cos := fun z =>
    (Complex.differentiable_cos.analyticAt z).meromorphicAt
  exact ⟨hs.inv,hc.inv,hc.div hs⟩

/-- A product with a reciprocal has norm tending to infinity exactly at an isolated zero. -/
private lemma trigBasic_tendsto_norm_mul_inv_atTop_iff {g h : ℂ → ℂ} {z : ℂ}
    (hgc : ContinuousAt g z) (hhc : ContinuousAt h z)
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
  · simpa [csc] using trigBasic_tendsto_norm_mul_inv_atTop_iff (g := Complex.sin) (h := fun _ => 1)
      Complex.continuous_sin.continuousAt continuousAt_const hs (fun _ => one_ne_zero)
  · simpa [sec] using trigBasic_tendsto_norm_mul_inv_atTop_iff (g := Complex.cos) (h := fun _ => 1)
      Complex.continuous_cos.continuousAt continuousAt_const hcz (fun _ => one_ne_zero)
  · have := trigBasic_tendsto_norm_mul_inv_atTop_iff (g := Complex.sin) (h := Complex.cos)
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
theorem reciprocal_trig_nonzero {z : ℂ} (hs : Complex.sin z≠0) (hc : Complex.cos z≠0) :
    csc z≠0 ∧ sec z≠0 := by
  exact ⟨inv_ne_zero hs,inv_ne_zero hc⟩

/-- DLMF 4.20.E4: hasDerivAt csc. -/
@[dlmf 4.20.E4]
theorem hasDerivAt_csc {z : ℂ} (hz : Complex.sin z≠0) :
    HasDerivAt csc (-csc z*Complex.cot z) z := by
  refine ((Complex.hasDerivAt_sin z).inv hz).congr_deriv ?_
  simp only [csc,Complex.cot,div_eq_mul_inv,pow_two]
  ring

/-- DLMF 4.20.E5: hasDerivAt sec. -/
@[dlmf 4.20.E5]
theorem hasDerivAt_sec {z : ℂ} (hz : Complex.cos z≠0) :
    HasDerivAt sec (sec z*Complex.tan z) z := by
  refine ((Complex.hasDerivAt_cos z).inv hz).congr_deriv ?_
  simp only [sec,Complex.tan,div_eq_mul_inv,pow_two]
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

/-- Squaring the principal complex square root returns its argument, including zero. -/
theorem trig_sqrt_sq (z : ℂ) : (Complex.sqrt z)^2=z := by
  rw [Complex.sqrt,← Complex.cpow_mul_nat]
  norm_num

/-- The cosecant is odd. -/
theorem csc_neg (z : ℂ) : csc (-z) = -csc z := by
  simp [csc, Complex.sin_neg, inv_neg]

/-- The secant is even. -/
@[simp]
theorem sec_neg (z : ℂ) : sec (-z) = sec z := by
  simp [sec]

/-- The totalized value of the cosecant at its pole `0`. -/
@[simp]
theorem csc_zero : csc 0 = 0 := by
  simp [csc]

/-- `sec 0 = 1`. -/
@[simp]
theorem sec_zero : sec 0 = 1 := by
  simp [sec]

end DLMF.Elementary
