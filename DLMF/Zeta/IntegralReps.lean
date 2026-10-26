/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.Polygamma
public import DLMF.Zeta.Riemann
public import DLMF.Gamma.IntegralRepresentations
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import DLMF.Gamma.PolygammaHurwitz
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy

/-!
# Integral representations of the Riemann zeta function (DLMF §25.5)

Conventions.
* Integrals over `(0, ∞)` are Bochner integrals `∫ x in Ioi 0`, stated together with the
  integrability of the integrand, so that Lean's convention `∫ = 0` for non-integrable functions
  plays no role. Powers `x^{s-1}`, `(1+x²)^{s/2}`, `2^s`, `π^{s/2}` are principal complex powers
  of positive reals.
* 25.5.5 converges only conditionally at `∞` (for `-1 < Re s < 0`); it is stated as the limit of
  `∫₀^R` as `R → ∞`.
* Where DLMF divides by `1 - 2^{1-s}` (25.5.3, 25.5.4, 25.5.10, 25.5.21), which vanishes at
  `s = 1 + 2πik/ln 2`, the multiplied form is stated. It is equivalent to the printed form where
  the factor is nonzero and also holds at its zeros (stronger than DLMF).
* `1/Γ(s)` is kept as printed; Lean's `1 / Γ(s) = 0` at the poles of `Γ` agrees with the
  reciprocal Gamma function, so 25.5.6 and 25.5.7 hold also at `s = 0, -1, -2, …`.
* 25.5.13 has a removable singularity at `s = 0`, which is excluded.
* `ψ = Complex.digamma` and `ψ^{(m)} = DLMF.Gamma.polygamma m` (iterated derivatives of `ψ`).
* The loop integrals 25.5.20–25.5.21 are taken over the keyhole contours `keyholeLoopIntegral`
  (the two edges of the cut `(-∞, -δ]` and the circle `|z| = δ`), for every admissible radius
  `δ`; DLMF allows any loop of the stated kind, and the independence of the loop (Cauchy's
  theorem) is not formalized.
-/

@[expose] public noncomputable section

open Complex Filter Topology MeasureTheory Set Finset
open scoped Real

namespace DLMF.Zeta

/-! ### §25.5(i) In terms of elementary functions -/

/-- `t^{s-1} e^{-t}/(1 - e^{-t}) = t^{s-1}/(e^t - 1)` for `t > 0`. -/
lemma q25a_exp_div_one_sub_exp {s : ℂ} {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ (s - 1) * cexp (-((1 : ℝ) * (t : ℂ))) / (1 - cexp (-(t : ℂ))) =
      (t : ℂ) ^ (s - 1) / (cexp t - 1) := by
  have h1 : cexp (t : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero, ← ofReal_exp]
    exact_mod_cast (Real.one_lt_exp_iff.mpr ht).ne'
  have h2 : cexp (t : ℂ) ≠ 0 := Complex.exp_ne_zero _
  have h3 : (1 : ℂ) - cexp (-(t : ℂ)) ≠ 0 := by
    rw [sub_ne_zero, ← ofReal_neg, ← ofReal_exp]
    exact_mod_cast (Real.exp_lt_one_iff.mpr (by linarith)).ne'
  rw [ofReal_one, one_mul, Complex.exp_neg]
  field_simp
/-- The integrand of 25.5.1 is integrable for `Re s > 1`. -/
lemma q25a_integrableOn_exp_sub_one {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) / (cexp x - 1)) (Ioi 0) := by
  set σ : ℂ := (s.re : ℂ)
  have hσ : 1 < σ.re := by simpa [σ] using hs
  have hval := DLMF.Gamma.integral_cpow_mul_exp_div_one_sub_exp hσ (x := 1) one_pos
  have hne : (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (σ - 1) * cexp (-((1 : ℝ) * (t : ℂ))) /
      (1 - cexp (-(t : ℂ)))) ≠ 0 := by
    rw [hval]
    refine mul_ne_zero (Gamma_ne_zero_of_re_pos (by linarith)) ?_
    rw [show (∑' k : ℕ, 1 / ((k : ℂ) + ((1 : ℝ) : ℂ)) ^ σ) = riemannZeta σ by
      rw [zeta_eq_tsum_one_div_nat_add_one_cpow hσ]; push_cast; rfl]
    exact riemannZeta_ne_zero_of_one_lt_re hσ
  have hg := Integrable.of_integral_ne_zero hne
  refine hg.norm.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.div ?_ ?_ ?_
    · exact (continuousAt_ofReal_cpow_const _ _ (Or.inr hx0.ne'))
    · exact (Complex.continuous_exp.comp continuous_ofReal).continuousAt.sub continuousAt_const
    · rw [sub_ne_zero, ← ofReal_exp]
      exact_mod_cast (Real.one_lt_exp_iff.mpr hx0).ne'
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [q25a_exp_div_one_sub_exp ht0, norm_div, norm_div,
      norm_cpow_eq_rpow_re_of_pos ht0, norm_cpow_eq_rpow_re_of_pos ht0]
    simp [σ]
/-- `∫₀^∞ eᵗ tˢ/(eᵗ-1)² dt = Γ(s+1) ζ(s)` for `Re s > 1`, by termwise integration of
`eᵗ/(eᵗ-1)² = ∑ k e^{-kt}`. -/
lemma q25a_integral_exp_sub_one_sq {s : ℂ} (hs : 1 < s.re) :
    ∫ t in Ioi (0 : ℝ), cexp t * (t : ℂ) ^ s / (cexp t - 1) ^ 2 =
      Gamma (s + 1) * riemannZeta s := by
  have hs1 : 0 < (s + 1).re := by simp; linarith
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs; linarith
  set F : ℕ → ℝ → ℂ := fun k t => (t : ℂ) ^ s * ((k : ℂ) * cexp (-((k : ℂ) * t))) with hF
  have hFint (k : ℕ) : Integrable (F k) (volume.restrict (Ioi 0)) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hF]
    · have := (DLMF.Gamma.integrableOn_cpow_mul_exp_neg_mul hs1
        (r := (k : ℝ)) (by exact_mod_cast hk)).mul_const (k : ℂ)
      refine IntegrableOn.congr_fun this (fun t _ => ?_) measurableSet_Ioi
      simp only [hF, add_sub_cancel_right, ofReal_natCast]; ring
  have hFval (k : ℕ) : ∫ t in Ioi (0 : ℝ), F k t = Gamma (s + 1) * (1 / (k : ℂ) ^ s) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hF, zero_cpow hs0]
    · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      have h := integral_cpow_mul_exp_neg_mul_Ioi hs1 hk'
      simp only [add_sub_cancel_right, ofReal_natCast] at h
      rw [show (fun t => F k t) = fun t : ℝ => (k : ℂ) * ((t : ℂ) ^ s * cexp (-((k : ℂ) * t))) by
        funext t; simp only [hF]; ring, integral_const_mul, h]
      have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
      have harg : ((k : ℂ)).arg ≠ π := by
        rw [← ofReal_natCast, arg_ofReal_of_nonneg hk'.le]; exact Real.pi_ne_zero.symm
      rw [one_div, inv_cpow _ _ harg, cpow_add _ _ hkc, cpow_one]
      field_simp
  have hnorm (k : ℕ) : ∫ t in Ioi (0 : ℝ), ‖F k t‖ = k * ((1 / (k : ℝ)) ^ (s.re + 1) *
      Real.Gamma (s.re + 1)) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hF]
    · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith) hk', ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht' : (0 : ℝ) < t := ht
      simp only [hF]
      rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht',
        show -((k : ℂ) * t) = ((-((k : ℝ) * t) : ℝ) : ℂ) by push_cast; ring, norm_exp_ofReal,
        Complex.norm_natCast, add_sub_cancel_right]
      ring
  have hsum : Summable fun k => ∫ t in Ioi (0 : ℝ), ‖F k t‖ := by
    simp_rw [hnorm]
    have h := Real.summable_one_div_nat_rpow.mpr hs
    refine (h.mul_right (Real.Gamma (s.re + 1))).congr fun k => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [Real.zero_rpow (by linarith : s.re ≠ 0)]
    · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      rw [Real.div_rpow zero_le_one hk'.le, Real.one_rpow, Real.rpow_add hk', Real.rpow_one]
      field_simp
  have key := integral_tsum_of_summable_integral_norm hFint hsum
  simp_rw [hFval] at key
  rw [tsum_mul_left, ← zeta_eq_tsum_one_div_nat_cpow hs] at key
  rw [key]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : (0 : ℝ) < t := ht
  have hq : ‖cexp (-(t : ℂ))‖ < 1 := by
    rw [show -(t : ℂ) = ((-t : ℝ) : ℂ) by push_cast; ring, norm_exp_ofReal]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom := (hasSum_coe_mul_geometric_of_norm_lt_one hq).mul_left ((t : ℂ) ^ s)
  have hE : cexp (t : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero, ← ofReal_exp]
    exact_mod_cast (Real.one_lt_exp_iff.mpr ht').ne'
  have hE2 : (1 : ℂ) - cexp (-(t : ℂ)) ≠ 0 := by
    rw [sub_ne_zero, ← ofReal_neg, ← ofReal_exp]
    exact_mod_cast (Real.exp_lt_one_iff.mpr (by linarith)).ne'
  have : cexp t * (t : ℂ) ^ s / (cexp t - 1) ^ 2 =
      (t : ℂ) ^ s * (cexp (-(t : ℂ)) / (1 - cexp (-(t : ℂ))) ^ 2) := by
    rw [Complex.exp_neg] at hE2 ⊢
    have h0 : cexp (t : ℂ) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  rw [this, ← hgeom.tsum_eq]
  congr 1
  funext k
  simp only [hF]
  rw [← Complex.exp_nat_mul]
  ring_nf

/-- DLMF 25.5.1: `ζ(s) = Γ(s)⁻¹ ∫₀^∞ x^{s-1}/(eˣ - 1) dx` for `Re s > 1`. -/
@[dlmf 25.5.E1]
theorem riemannZeta_eq_integral_exp_sub_one {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) / (cexp x - 1)) (Ioi 0) ∧
      riemannZeta s = 1 / Gamma s * ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) / (cexp x - 1) := by
  refine ⟨q25a_integrableOn_exp_sub_one hs, ?_⟩
  have hval := DLMF.Gamma.integral_cpow_mul_exp_div_one_sub_exp hs (x := 1) one_pos
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => q25a_exp_div_one_sub_exp ht)] at hval
  rw [hval, show (∑' k : ℕ, 1 / ((k : ℂ) + ((1 : ℝ) : ℂ)) ^ s) = riemannZeta s by
      rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]; push_cast; rfl]
  have hG : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  field_simp

/-- `eᵗ - 1 ≠ 0` for `t > 0`. -/
lemma q25a_exp_sub_one_ne {t : ℝ} (ht : 0 < t) : cexp (t : ℂ) - 1 ≠ 0 := by
  rw [sub_ne_zero, ← ofReal_exp]
  exact_mod_cast (Real.one_lt_exp_iff.mpr ht).ne'
/-- Integrability transfers along equal norms on `(0, ∞)` for functions continuous there. -/
lemma q25a_integrableOn_of_norm_eq {f g : ℝ → ℂ} (hg : IntegrableOn g (Ioi 0))
    (hf : ContinuousOn f (Ioi 0)) (h : ∀ t : ℝ, 0 < t → ‖f t‖ = ‖g t‖) :
    IntegrableOn f (Ioi 0) := by
  refine hg.norm.mono' (hf.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (h t ht).le
/-- Integrability and value under the scaling `x ↦ 2x` on `(0, ∞)`. -/
lemma q25a_scale_two {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0)) :
    IntegrableOn (fun x => f (2 * x)) (Ioi 0) ∧
      ∫ x in Ioi (0 : ℝ), f (2 * x) = 1 / 2 * ∫ x in Ioi (0 : ℝ), f x := by
  refine ⟨(integrableOn_Ioi_comp_mul_left_iff f 0 two_pos).mpr (by simpa using hf), ?_⟩
  rw [integral_comp_mul_left_Ioi f 0 two_pos, mul_zero, Complex.real_smul]
  push_cast; ring
/-- The continuity of `t ↦ eᵗ tˢ / (eᵗ - 1)²` on `(0, ∞)`. -/
lemma q25a_continuousOn_exp_sq (s : ℂ) :
    ContinuousOn (fun t : ℝ => cexp t * (t : ℂ) ^ s / (cexp t - 1) ^ 2) (Ioi 0) := by
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  refine ContinuousAt.continuousWithinAt ?_
  refine ContinuousAt.div ?_ ?_ (pow_ne_zero _ (q25a_exp_sub_one_ne hx0))
  · exact (Complex.continuous_exp.comp continuous_ofReal).continuousAt.mul
      (continuousAt_ofReal_cpow_const _ _ (Or.inr hx0.ne'))
  · exact ((Complex.continuous_exp.comp continuous_ofReal).continuousAt.sub
      continuousAt_const).pow 2
/-- The integrand of 25.5.2 is integrable for `Re s > 1`. -/
lemma q25a_integrableOn_exp_sub_one_sq {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => cexp x * (x : ℂ) ^ s / (cexp x - 1) ^ 2) (Ioi 0) := by
  set σ : ℂ := (s.re : ℂ)
  have hσ : 1 < σ.re := by simpa [σ] using hs
  have hne : (∫ t in Ioi (0 : ℝ), cexp t * (t : ℂ) ^ σ / (cexp t - 1) ^ 2) ≠ 0 := by
    rw [q25a_integral_exp_sub_one_sq hσ]
    exact mul_ne_zero (Gamma_ne_zero_of_re_pos (by simp; linarith))
      (riemannZeta_ne_zero_of_one_lt_re hσ)
  refine q25a_integrableOn_of_norm_eq (Integrable.of_integral_ne_zero hne)
    (q25a_continuousOn_exp_sq s) fun t ht => ?_
  rw [norm_div, norm_div, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht,
    norm_cpow_eq_rpow_re_of_pos ht]
  simp [σ]

/-- DLMF 25.5.2: `ζ(s) = Γ(s+1)⁻¹ ∫₀^∞ eˣ xˢ/(eˣ - 1)² dx` for `Re s > 1`. -/
@[dlmf 25.5.E2]
theorem riemannZeta_eq_integral_exp_sub_one_sq {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => cexp x * (x : ℂ) ^ s / (cexp x - 1) ^ 2) (Ioi 0) ∧
      riemannZeta s =
        1 / Gamma (s + 1) * ∫ x in Ioi (0 : ℝ), cexp x * (x : ℂ) ^ s / (cexp x - 1) ^ 2 := by
  refine ⟨q25a_integrableOn_exp_sub_one_sq hs, ?_⟩
  rw [q25a_integral_exp_sub_one_sq hs]
  have hG : Gamma (s + 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  field_simp

/-- `x^a ≤ x^{a₁} + x^{a₂}` for `x > 0`, `a₁ ≤ a ≤ a₂`. -/
lemma q25a_rpow_le_add {x a a₁ a₂ : ℝ} (hx : 0 < x) (h1 : a₁ ≤ a) (h2 : a ≤ a₂) :
    x ^ a ≤ x ^ a₁ + x ^ a₂ := by
  rcases le_or_gt x 1 with hx1 | hx1
  · have := Real.rpow_le_rpow_of_exponent_ge hx hx1 h1
    linarith [Real.rpow_nonneg hx.le a₂]
  · have := Real.rpow_le_rpow_of_exponent_le hx1.le h2
    linarith [Real.rpow_nonneg hx.le a₁]
/-- `s ↦ ∫₀^∞ x^{s-1} φ(x) dx` is holomorphic on `Re s > 0` when `φ` is continuous on
`(0, ∞)` and `|φ(x)| ≤ e^{-x}`. -/
lemma q25a_differentiableOn_mellin {φ : ℝ → ℂ} (hφc : ContinuousOn φ (Ioi 0))
    (hφ : ∀ x : ℝ, 0 < x → ‖φ x‖ ≤ Real.exp (-x)) :
    DifferentiableOn ℂ (fun s : ℂ => ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * φ x)
      {s | 0 < s.re} := by
  have hmeasφ : AEStronglyMeasurable φ (volume.restrict (Ioi 0)) :=
    hφc.aestronglyMeasurable measurableSet_Ioi
  refine Complex.differentiableOn_integral_Ioi_of_locally_dominated
    (isOpen_lt continuous_const continuous_re) 0 ?_ ?_ ?_
  · intro s _
    refine AEStronglyMeasurable.mul ?_ hmeasφ
    refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
    exact (continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt hx))).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
    intro s _
    refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.mul_const ?_ _)
    exact (differentiableAt_id.sub_const 1).const_cpow (Or.inl ht0)
  · intro s0 hs0
    have hs0' : 0 < s0.re := hs0
    refine ⟨{s | s0.re / 2 < s.re ∧ s.re < s0.re + 1}, ?_,
      fun x => Real.exp (-x) * x ^ (s0.re / 2 - 1) + Real.exp (-x) * x ^ (s0.re + 1 - 1),
      (Real.GammaIntegral_convergent (s := s0.re / 2) (by linarith)).add
        (Real.GammaIntegral_convergent (s := s0.re + 1) (by linarith)), ?_⟩
    · exact ((isOpen_lt continuous_const continuous_re).inter
        (isOpen_lt continuous_re continuous_const)).mem_nhds
        (show s0.re / 2 < s0.re ∧ s0.re < s0.re + 1 from ⟨by linarith, by linarith⟩)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht s hs
      have ht0 : (0 : ℝ) < t := ht
      obtain ⟨hs1, hs2⟩ := hs
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, sub_re, one_re, ← mul_add]
      have h1 := q25a_rpow_le_add ht0 (a := s.re - 1) (a₁ := s0.re / 2 - 1)
        (a₂ := s0.re + 1 - 1) (by linarith) (by linarith)
      have := mul_le_mul h1 (hφ t ht0) (norm_nonneg _) (by positivity)
      exact this.trans_eq (by ring)
/-- The domain `Re s > a` minus the ray `[1, ∞)`, star-shaped about a real point `c`,
`a < c < 1`. -/
lemma q25a_isPreconnected_ray {a c : ℝ} (hac : a < c) (hc1 : c < 1) :
    IsPreconnected ({s : ℂ | a < s.re} \ {s : ℂ | s.im = 0 ∧ 1 ≤ s.re}) := by
  refine (StarConvex.isPathConnected (a := (c : ℂ)) ?_ ?_).isConnected.isPreconnected
  · intro z hz u v hu hv huv
    have hz1 : a < z.re := hz.1
    have hz2 : ¬ (z.im = 0 ∧ 1 ≤ z.re) := hz.2
    rw [Complex.real_smul, Complex.real_smul]
    refine ⟨?_, ?_⟩
    · show a < ((u : ℂ) * c + (v : ℂ) * z).re
      simp only [add_re, re_ofReal_mul, ofReal_re]
      rcases eq_or_lt_of_le hu with rfl | hu'
      · simp at huv; subst huv; linarith
      · nlinarith [mul_pos hu' (sub_pos.mpr hac), mul_nonneg hv (sub_nonneg.mpr hz1.le)]
    · rintro ⟨him, hre⟩
      simp only [add_im, im_ofReal_mul, ofReal_im, mul_zero, zero_add] at him
      simp only [add_re, re_ofReal_mul, ofReal_re] at hre
      rcases eq_or_lt_of_le hv with rfl | hv'
      · simp at huv; subst huv; linarith
      · have hzi : z.im = 0 := by
          rcases mul_eq_zero.mp him with h | h
          · linarith
          · exact h
        have : z.re < 1 := by
          by_contra h; exact hz2 ⟨hzi, not_lt.mp h⟩
        nlinarith
  · refine ⟨?_, ?_⟩
    · show a < (c : ℂ).re
      simpa using hac
    · rintro ⟨-, h⟩; simp at h; linarith
/-- `|1/(eˣ+1)| ≤ e^{-x}`. -/
lemma q25a_norm_inv_exp_add_one_le {x : ℝ} :
    ‖1 / (cexp x + 1)‖ ≤ Real.exp (-x) := by
  rw [show cexp (x : ℂ) + 1 = ((Real.exp x + 1 : ℝ) : ℂ) by push_cast; rfl, norm_div, norm_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), Real.exp_neg]
  exact (one_div_le_one_div_of_le (Real.exp_pos x) (by linarith)).trans_eq (one_div _)
/-- `|eˣ/(eˣ+1)²| ≤ e^{-x}`. -/
lemma q25a_norm_exp_div_exp_add_one_sq_le {x : ℝ} :
    ‖cexp x / (cexp x + 1) ^ 2‖ ≤ Real.exp (-x) := by
  rw [show cexp (x : ℂ) + 1 = ((Real.exp x + 1 : ℝ) : ℂ) by push_cast; rfl, ← ofReal_exp,
    ← ofReal_pow, ← ofReal_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity), Real.exp_neg, div_le_iff₀ (by positivity)]
  have h := Real.exp_pos x
  field_simp
  nlinarith
/-- 25.5.3 for `Re s > 1`: the integrand of 25.5.3 splits as `h(x) - 2^{2-s} h(2x)`. -/
lemma q25a_exp_add_one_split {s : ℂ} {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ (s - 1) / (cexp x + 1) = (x : ℂ) ^ (s - 1) / (cexp x - 1) -
      2 * (2 : ℂ) ^ (1 - s) * (((2 * x : ℝ) : ℂ) ^ (s - 1) / (cexp ((2 * x : ℝ) : ℂ) - 1)) := by
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  rw [ofReal_mul, mul_cpow_ofReal_nonneg (by norm_num) hx.le, ofReal_ofNat]
  have hE := q25a_exp_sub_one_ne hx
  have hE1 : cexp (x : ℂ) + 1 ≠ 0 := by
    rw [← ofReal_exp]; exact_mod_cast (by positivity : Real.exp x + 1 ≠ 0)
  have hc : (2 : ℂ) ^ (1 - s) * (2 : ℂ) ^ (s - 1) = 1 := by
    rw [← cpow_add _ _ h2]; simp
  rw [show cexp (2 * (x : ℂ)) - 1 = (cexp x - 1) * (cexp x + 1) by
    rw [show 2 * (x : ℂ) = x + x by ring, Complex.exp_add]; ring]
  rw [show 2 * (2 : ℂ) ^ (1 - s) * ((2 : ℂ) ^ (s - 1) * (x : ℂ) ^ (s - 1) /
      ((cexp x - 1) * (cexp x + 1))) = 2 * ((2 : ℂ) ^ (1 - s) * (2 : ℂ) ^ (s - 1)) *
      ((x : ℂ) ^ (s - 1) / ((cexp x - 1) * (cexp x + 1))) by ring, hc]
  field_simp
  ring

/-- DLMF 25.5.3 (multiplied form): `(1 - 2^{1-s}) Γ(s) ζ(s) = ∫₀^∞ x^{s-1}/(eˣ + 1) dx` for
`Re s > 0`, `s ≠ 1`. -/
@[dlmf 25.5.E3]
theorem riemannZeta_eq_integral_exp_add_one {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) / (cexp x + 1)) (Ioi 0) ∧
      (1 - 2 ^ (1 - s)) * Gamma s * riemannZeta s =
        ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) / (cexp x + 1) := by
  have hφc : ContinuousOn (fun x : ℝ => 1 / (cexp x + 1)) (Ioi 0) := by
    refine Continuous.continuousOn ?_
    refine continuous_const.div (by fun_prop) fun x => ?_
    rw [← ofReal_exp]; exact_mod_cast (by positivity : Real.exp x + 1 ≠ 0)
  have hint : ∀ z : ℂ, 0 < z.re →
      IntegrableOn (fun x : ℝ => (x : ℂ) ^ (z - 1) / (cexp x + 1)) (Ioi 0) := by
    intro z hz
    refine (show Integrable _ (volume.restrict (Ioi (0 : ℝ))) from
      DLMF.Gamma.integrableOn_cpow_mul_exp_neg_mul hz one_pos).norm.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
      have hx0 : (0 : ℝ) < x := hx
      refine ContinuousAt.continuousWithinAt (ContinuousAt.div ?_ ?_ ?_)
      · exact continuousAt_ofReal_cpow_const _ _ (Or.inr hx0.ne')
      · fun_prop
      · rw [← ofReal_exp]; exact_mod_cast (by positivity : Real.exp x + 1 ≠ 0)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : (0 : ℝ) < x := hx
      rw [div_eq_mul_one_div, norm_mul, norm_mul, ofReal_one, one_mul,
        show -((x : ℂ)) = ((-x : ℝ) : ℂ) by push_cast; ring, norm_exp_ofReal]
      exact mul_le_mul_of_nonneg_left q25a_norm_inv_exp_add_one_le (norm_nonneg _)
  refine ⟨hint s hs, ?_⟩
  -- the case `Re s > 1`
  have hgt : ∀ z : ℂ, 1 < z.re → (1 - 2 ^ (1 - z)) * Gamma z * riemannZeta z =
      ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (z - 1) / (cexp x + 1) := by
    intro z hz
    have hI := q25a_integrableOn_exp_sub_one hz
    obtain ⟨hI2, hV2⟩ := q25a_scale_two hI
    have hval := (riemannZeta_eq_integral_exp_sub_one hz).2
    have hG : Gamma z ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => q25a_exp_add_one_split hx),
      integral_sub hI (hI2.const_mul _), integral_const_mul, hV2]
    have hJ : ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (z - 1) / (cexp x - 1) = Gamma z * riemannZeta z := by
      rw [hval]; field_simp
    rw [hJ]
    ring
  set U : Set ℂ := {s : ℂ | 0 < s.re} \ {s : ℂ | s.im = 0 ∧ 1 ≤ s.re} with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const continuous_re).sdiff
    ((isClosed_eq continuous_im continuous_const).inter
      (isClosed_le continuous_const continuous_re))
  have hF : DifferentiableOn ℂ (fun z => (1 - 2 ^ (1 - z)) * Gamma z * riemannZeta z) U := by
    intro z hz
    have hz0 : 0 < z.re := hz.1
    have hz1 : z ≠ 1 := fun h => hz.2 ⟨by rw [h]; simp, by rw [h]; simp⟩
    refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.mul (DifferentiableAt.mul
      ?_ ?_) (differentiableAt_riemannZeta hz1))
    · exact (differentiableAt_const _).sub
        (((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl two_ne_zero))
    · refine differentiableAt_Gamma z fun m hm => ?_
      have := congrArg re hm; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hG : DifferentiableOn ℂ (fun z => ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (z - 1) / (cexp x + 1)) U
      := by
    have := q25a_differentiableOn_mellin hφc (fun x _ => q25a_norm_inv_exp_add_one_le)
    refine (this.mono (fun z (hz : z ∈ U) => hz.1)).congr fun z _ => ?_
    show ∫ x in Ioi (0 : ℝ), _ = ∫ x in Ioi (0 : ℝ), _
    congr 1; funext x; rw [div_eq_mul_one_div]
  have hz0 : (2 + I : ℂ) ∈ U := ⟨by show (0 : ℝ) < (2 + I : ℂ).re; simp,
    by rintro ⟨h, -⟩; simp at h⟩
  have hev : (fun z => (1 - 2 ^ (1 - z)) * Gamma z * riemannZeta z) =ᶠ[𝓝 (2 + I : ℂ)]
      (fun z => ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (z - 1) / (cexp x + 1)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show (1 : ℝ) < (2 + I : ℂ).re by simp)] with z hz
    exact hgt z hz
  have heq := (hF.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
    (hG.analyticOnNhd hUo) (q25a_isPreconnected_ray (a := 0) (c := 1 / 2) (by norm_num)
      (by norm_num)) hz0 hev
  by_cases hsU : s ∈ U
  · exact heq hsU
  · have hray : s.im = 0 ∧ 1 ≤ s.re := by
      by_contra h; exact hsU ⟨hs, h⟩
    have hre : 1 < s.re := by
      rcases eq_or_lt_of_le hray.2 with h | h
      · exfalso; apply hs1; apply Complex.ext <;> simp [hray.1, ← h]
      · exact h
    exact hgt s hre

/-- The integrand of 25.5.4 splits as `h(x) - 4·2^{-s} h(2x)` with `h(u) = eᵘ uˢ/(eᵘ-1)²`. -/
lemma q25a_exp_add_one_sq_split {s : ℂ} {x : ℝ} (hx : 0 < x) :
    cexp x * (x : ℂ) ^ s / (cexp x + 1) ^ 2 = cexp x * (x : ℂ) ^ s / (cexp x - 1) ^ 2 -
      4 * (2 : ℂ) ^ (-s) * (cexp ((2 * x : ℝ) : ℂ) * ((2 * x : ℝ) : ℂ) ^ s /
        (cexp ((2 * x : ℝ) : ℂ) - 1) ^ 2) := by
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  rw [ofReal_mul, mul_cpow_ofReal_nonneg (by norm_num) hx.le, ofReal_ofNat]
  have hE := q25a_exp_sub_one_ne hx
  have hE1 : cexp (x : ℂ) + 1 ≠ 0 := by
    rw [← ofReal_exp]; exact_mod_cast (by positivity : Real.exp x + 1 ≠ 0)
  have hc : (2 : ℂ) ^ (-s) * (2 : ℂ) ^ s = 1 := by
    rw [← cpow_add _ _ h2]; simp
  have he2 : cexp (2 * (x : ℂ)) = cexp x * cexp x := by
    rw [show 2 * (x : ℂ) = x + x by ring, Complex.exp_add]
  rw [he2, show 4 * (2 : ℂ) ^ (-s) * (cexp x * cexp x * ((2 : ℂ) ^ s * (x : ℂ) ^ s) /
      (cexp x * cexp x - 1) ^ 2) = 4 * ((2 : ℂ) ^ (-s) * (2 : ℂ) ^ s) *
      (cexp x * cexp x * (x : ℂ) ^ s / (cexp x * cexp x - 1) ^ 2) by ring, hc,
    show cexp (x : ℂ) * cexp x - 1 = (cexp x - 1) * (cexp x + 1) by ring]
  field_simp
  ring

/-- DLMF 25.5.4 (multiplied form): `(1 - 2^{1-s}) Γ(s+1) ζ(s) = ∫₀^∞ eˣ xˢ/(eˣ + 1)² dx` for
`Re s > 0`, `s ≠ 1`. -/
@[dlmf 25.5.E4]
theorem riemannZeta_eq_integral_exp_add_one_sq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    IntegrableOn (fun x : ℝ => cexp x * (x : ℂ) ^ s / (cexp x + 1) ^ 2) (Ioi 0) ∧
      (1 - 2 ^ (1 - s)) * Gamma (s + 1) * riemannZeta s =
        ∫ x in Ioi (0 : ℝ), cexp x * (x : ℂ) ^ s / (cexp x + 1) ^ 2 := by
  set φ : ℝ → ℂ := fun x => cexp x / (cexp x + 1) ^ 2 with hφdef
  have hφc : ContinuousOn φ (Ioi 0) := by
    refine Continuous.continuousOn ?_
    refine (by fun_prop : Continuous fun x : ℝ => cexp x).div (by fun_prop) fun x => ?_
    refine pow_ne_zero _ ?_
    rw [← ofReal_exp]; exact_mod_cast (by positivity : Real.exp x + 1 ≠ 0)
  have hform : ∀ z : ℂ, ∀ x : ℝ, 0 < x →
      cexp x * (x : ℂ) ^ z / (cexp x + 1) ^ 2 = (x : ℂ) ^ (z + 1 - 1) * φ x := by
    intro z x _; simp only [hφdef, add_sub_cancel_right]; ring
  have hint : ∀ z : ℂ, 0 < z.re →
      IntegrableOn (fun x : ℝ => cexp x * (x : ℂ) ^ z / (cexp x + 1) ^ 2) (Ioi 0) := by
    intro z hz
    have hz1 : 0 < (z + 1).re := by simp; linarith
    refine (show Integrable _ (volume.restrict (Ioi (0 : ℝ))) from
      DLMF.Gamma.integrableOn_cpow_mul_exp_neg_mul hz1 one_pos).norm.mono' ?_ ?_
    · refine (ContinuousOn.congr (f := fun x : ℝ => (x : ℂ) ^ (z + 1 - 1) * φ x) ?_
        (fun x hx => hform z x hx)).aestronglyMeasurable measurableSet_Ioi
      refine ContinuousOn.mul (fun x hx => ?_) hφc
      exact (continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt hx))).continuousWithinAt
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : (0 : ℝ) < x := hx
      rw [hform z x hx0, norm_mul, norm_mul, ofReal_one, one_mul,
        show -((x : ℂ)) = ((-x : ℝ) : ℂ) by push_cast; ring, norm_exp_ofReal]
      exact mul_le_mul_of_nonneg_left q25a_norm_exp_div_exp_add_one_sq_le (norm_nonneg _)
  refine ⟨hint s hs, ?_⟩
  have hgt : ∀ z : ℂ, 1 < z.re → (1 - 2 ^ (1 - z)) * Gamma (z + 1) * riemannZeta z =
      ∫ x in Ioi (0 : ℝ), cexp x * (x : ℂ) ^ z / (cexp x + 1) ^ 2 := by
    intro z hz
    have hI := q25a_integrableOn_exp_sub_one_sq hz
    obtain ⟨hI2, hV2⟩ := q25a_scale_two hI
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => q25a_exp_add_one_sq_split hx),
      integral_sub hI (hI2.const_mul _), integral_const_mul, hV2,
      q25a_integral_exp_sub_one_sq hz]
    have h1s : (2 : ℂ) ^ (1 - z) = 2 * (2 : ℂ) ^ (-z) := by
      rw [sub_eq_add_neg, cpow_add _ _ two_ne_zero, cpow_one]
    rw [h1s]
    ring
  set U : Set ℂ := {s : ℂ | 0 < s.re} \ {s : ℂ | s.im = 0 ∧ 1 ≤ s.re} with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const continuous_re).sdiff
    ((isClosed_eq continuous_im continuous_const).inter
      (isClosed_le continuous_const continuous_re))
  have hF : DifferentiableOn ℂ (fun z => (1 - 2 ^ (1 - z)) * Gamma (z + 1) * riemannZeta z) U := by
    intro z hz
    have hz0 : 0 < z.re := hz.1
    have hz1 : z ≠ 1 := fun h => hz.2 ⟨by rw [h]; simp, by rw [h]; simp⟩
    refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.mul (DifferentiableAt.mul
      ?_ ?_) (differentiableAt_riemannZeta hz1))
    · exact (differentiableAt_const _).sub
        (((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl two_ne_zero))
    · refine (differentiableAt_Gamma (z + 1) fun m hm => ?_).comp z
        (differentiableAt_id.add_const 1)
      have := congrArg re hm; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hG : DifferentiableOn ℂ
      (fun z => ∫ x in Ioi (0 : ℝ), cexp x * (x : ℂ) ^ z / (cexp x + 1) ^ 2) U := by
    have hM := q25a_differentiableOn_mellin hφc (fun x _ => q25a_norm_exp_div_exp_add_one_sq_le)
    have hcomp := hM.comp (differentiableOn_id.add_const (1 : ℂ))
      (fun z (hz : z ∈ U) => show 0 < (z + 1).re by have : 0 < z.re := hz.1; simp; linarith)
    refine hcomp.congr fun z _ => ?_
    show ∫ x in Ioi (0 : ℝ), _ = ∫ x in Ioi (0 : ℝ), _
    exact setIntegral_congr_fun measurableSet_Ioi fun x hx => hform z x hx
  have hz0 : (2 + I : ℂ) ∈ U := ⟨by show (0 : ℝ) < (2 + I : ℂ).re; simp,
    by rintro ⟨h, -⟩; simp at h⟩
  have hev : (fun z => (1 - 2 ^ (1 - z)) * Gamma (z + 1) * riemannZeta z) =ᶠ[𝓝 (2 + I : ℂ)]
      (fun z => ∫ x in Ioi (0 : ℝ), cexp x * (x : ℂ) ^ z / (cexp x + 1) ^ 2) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show (1 : ℝ) < (2 + I : ℂ).re by simp)] with z hz
    exact hgt z hz
  have heq := (hF.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
    (hG.analyticOnNhd hUo) (q25a_isPreconnected_ray (a := 0) (c := 1 / 2) (by norm_num)
      (by norm_num)) hz0 hev
  by_cases hsU : s ∈ U
  · exact heq hsU
  · have hray : s.im = 0 ∧ 1 ≤ s.re := by
      by_contra h; exact hsU ⟨hs, h⟩
    have hre : 1 < s.re := by
      rcases eq_or_lt_of_le hray.2 with h | h
      · exfalso; apply hs1; apply Complex.ext <;> simp [hray.1, ← h]
      · exact h
    exact hgt s hre

open DLMF.BernoulliEuler in
/-- `binom(s+2, 3) = (s+2)(s+1)s/6`. -/
lemma r25a_gbinom_three (s : ℂ) : z25a_gbinom (s + 2) 3 = (s + 2) * (s + 1) * s / 6 := by
  simp only [z25a_gbinom, descPochhammer_succ_right, descPochhammer_zero, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_natCast, Polynomial.eval_one,
    Polynomial.eval_ofNat, Nat.factorial, Nat.cast_ofNat]
  push_cast
  ring

open DLMF.BernoulliEuler in
/-- For `-1 < Re s`, `s ≠ 1`: `ζ(s) = ½ + 1/(s-1) + s/12 - s(s+1)/2 ∫₁^∞ B̃₂(x) x^{-s-2} dx`. -/
lemma r25a_zeta_eq_B2 {s : ℂ} (hs : -1 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = 1 / 2 + 1 / (s - 1) + s / 12 - s * (s + 1) / 2 *
      ∫ x in Ioi (1 : ℝ), (periodicBernoulliB 2 x : ℂ) / (x : ℂ) ^ (s + 2) := by
  have h := q25a_zeta_eq_emRHS (n := 1) (N := 1) le_rfl le_rfl (by simp; linarith) hs1
  simp [q25a_emRHS, q25a_gbinom_one] at h
  have hr := q25a_recursion (p := 2) (by norm_num) (w := s + 2) (by simp; linarith)
    (a := 1) one_pos
  have hB3 : periodicBernoulliB 3 1 = 0 := by
    simp [periodicBernoulliB, bernoulliFun_eval_zero, bernoulli_eq_zero_of_odd (n := 3)
      ⟨1, rfl⟩ (by norm_num)]
  rw [hB3] at hr
  simp only [ofReal_zero, ofReal_one, one_cpow, div_one, neg_zero, zero_add] at hr
  rw [h, r25a_gbinom_three]
  push_cast at hr
  have e : (2 : ℂ) + 1 = 3 := by norm_num
  rw [e] at hr
  linear_combination (s * (s + 1) / 6) * hr

open scoped Interval in
open DLMF.BernoulliEuler in
/-- DLMF 25.5.5: `ζ(s) = -s ∫₀^∞ (x - ⌊x⌋ - ½) x^{-s-1} dx` for `-1 < Re s < 0`. The integral
converges only conditionally at `∞`; it is the limit of `∫₀^R` as `R → ∞`. -/
@[dlmf 25.5.E5]
theorem tendsto_integral_fract_sub_half {s : ℂ} (hs : -1 < s.re) (hs' : s.re < 0) :
    Tendsto (fun R : ℝ => -s * ∫ x in (0 : ℝ)..R,
        ((Int.fract x - 1 / 2 : ℝ) : ℂ) / (x : ℂ) ^ (s + 1)) atTop (𝓝 (riemannZeta s)) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs'
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at hs'
  set f : ℝ → ℂ := fun x => ((Int.fract x - 1 / 2 : ℝ) : ℂ) / (x : ℂ) ^ (s + 1) with hf
  set g : ℝ → ℂ := fun x => (x : ℂ) ^ (-s) - 1 / 2 * (x : ℂ) ^ (-(s + 1)) with hg
  -- on `(0, 1)`, `f = g`
  have hne1 : ∀ᵐ x : ℝ ∂volume, x ≠ 1 := by rw [ae_iff]; simp
  have hfg : ∀ᵐ x : ℝ ∂volume, x ∈ Ι (0 : ℝ) 1 → f x = g x := by
    filter_upwards [hne1] with x hx1 hx
    rw [Set.uIoc_of_le zero_le_one] at hx
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.1.ne'
    have hfr : Int.fract x = x := Int.fract_eq_self.mpr ⟨hx.1.le, lt_of_le_of_ne hx.2 hx1⟩
    simp only [hf, hg, hfr]
    rw [show -s = 1 - (s + 1) by ring, cpow_sub _ _ hx0, cpow_one, cpow_neg]
    push_cast
    ring
  have hg1 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_cpow' (by simp; linarith)
  have hg2 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-(s + 1))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_cpow' (by simp; linarith)
  have hgI : IntervalIntegrable g volume 0 1 := hg1.sub (hg2.const_mul _)
  have hfI : IntervalIntegrable f volume 0 1 := hgI.congr_ae (by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hfg] with x hx hxm using (hx hxm).symm)
  have hint01 : ∫ x in (0 : ℝ)..1, f x = 1 / (1 - s) + 1 / (2 * s) := by
    rw [intervalIntegral.integral_congr_ae hfg, intervalIntegral.integral_sub hg1
      (hg2.const_mul _), intervalIntegral.integral_const_mul,
      integral_cpow (Or.inl (by simp; linarith)), integral_cpow (Or.inl (by simp; linarith))]
    have h1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
    rw [show -s + 1 = 1 - s by ring, show -(s + 1) + 1 = -s by ring]
    simp only [ofReal_one, one_cpow, ofReal_zero, zero_cpow h1, zero_cpow (neg_ne_zero.mpr hs0)]
    field_simp
    ring
  -- on `[1, R]`, integration by parts against `B̃₂`
  obtain ⟨C1, hC1⟩ := q25a_periodicBernoulliB_bound 1
  obtain ⟨C2, hC2⟩ := q25a_periodicBernoulliB_bound 2
  have hfB : ∀ x, f x = (periodicBernoulliB 1 x : ℂ) / (x : ℂ) ^ (s + 1) := fun x => by
    simp [hf, periodicBernoulliB, bernoulliFun_one]
  set I2 := ∫ x in Ioi (1 : ℝ), (periodicBernoulliB 2 x : ℂ) / (x : ℂ) ^ (s + 2) with hI2
  have hstep : ∀ R : ℝ, 1 ≤ R → ∫ x in (1 : ℝ)..R, f x =
      ((periodicBernoulliB 2 R : ℂ) / (R : ℂ) ^ (s + 1) - 1 / 6 +
        (s + 1) * ∫ x in (1 : ℝ)..R, (periodicBernoulliB 2 x : ℂ) / (x : ℂ) ^ (s + 2)) / 2 := by
    intro R hR
    have h := q25a_integral_ibp (p := 1) le_rfl (s + 1) one_pos hR
    have i1 := q25a_intervalIntegrable_bdd_div_cpow (q25a_measurable_periodicBernoulliB 1) hC1
      (s + 1) one_pos hR
    have i2 := q25a_intervalIntegrable_bdd_div_cpow (q25a_measurable_periodicBernoulliB 2) hC2
      (s + 1 + 1) one_pos hR
    rw [intervalIntegral.integral_sub (i1.const_mul _) (i2.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
    have hB2 : periodicBernoulliB 2 1 = 1 / 6 := by
      simp [periodicBernoulliB, bernoulliFun_eval_zero, bernoulli_two]
    rw [hB2] at h
    simp only [ofReal_one, one_cpow, div_one] at h
    simp_rw [hfB]
    rw [show s + 1 + 1 = s + 2 by ring] at h
    push_cast at h ⊢
    linear_combination h / 2
  have hlimB : Tendsto (fun R : ℝ => (periodicBernoulliB 2 R : ℂ) / (R : ℂ) ^ (s + 1)) atTop
      (𝓝 0) := q25a_tendsto_pB_div_cpow 2 (by simp; linarith)
  have hlimI : Tendsto (fun R : ℝ => ∫ x in (1 : ℝ)..R,
      (periodicBernoulliB 2 x : ℂ) / (x : ℂ) ^ (s + 2)) atTop (𝓝 I2) :=
    intervalIntegral_tendsto_integral_Ioi 1 (q25a_integrableOn_bdd_div_cpow
      (q25a_measurable_periodicBernoulliB 2) hC2 (by simp; linarith) one_pos) tendsto_id
  have hlim : Tendsto (fun R : ℝ => -s * ((1 / (1 - s) + 1 / (2 * s)) +
      ((periodicBernoulliB 2 R : ℂ) / (R : ℂ) ^ (s + 1) - 1 / 6 +
        (s + 1) * ∫ x in (1 : ℝ)..R, (periodicBernoulliB 2 x : ℂ) / (x : ℂ) ^ (s + 2)) / 2))
      atTop (𝓝 (-s * ((1 / (1 - s) + 1 / (2 * s)) + (0 - 1 / 6 + (s + 1) * I2) / 2))) :=
    ((((hlimB.sub_const _).add (hlimI.const_mul _)).div_const _).const_add _).const_mul _
  have hval : -s * ((1 / (1 - s) + 1 / (2 * s)) + (0 - 1 / 6 + (s + 1) * I2) / 2) =
      riemannZeta s := by
    rw [r25a_zeta_eq_B2 hs hs1]
    have h1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
    have h2 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    field_simp
    ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with R hR
  have hfR : IntervalIntegrable f volume 1 R := by
    have := q25a_intervalIntegrable_bdd_div_cpow (q25a_measurable_periodicBernoulliB 1) hC1
      (s + 1) one_pos hR
    refine this.congr_ae (ae_of_all _ fun x => (hfB x).symm)
  rw [← intervalIntegral.integral_add_adjacent_intervals hfI hfR, hint01, hstep R hR]

/-- `|1/(eˣ-1) - 1/x + 1/2| ≤ x` for `x > 0`. -/
lemma r25a_abs_bose_sub_le {x : ℝ} (hx : 0 < x) :
    |1 / (Real.exp x - 1) - 1 / x + 1 / 2| ≤ x := by
  set E := Real.exp x - 1 with hE
  have hq := Real.quadratic_le_exp_of_nonneg hx.le
  have hE0 : 0 < E := by nlinarith
  have key : 1 / E - 1 / x + 1 / 2 = (2 * x - 2 * E + x * E) / (2 * x * E) := by
    field_simp
  rw [key, abs_div, abs_of_pos (by positivity : 0 < 2 * x * E), div_le_iff₀ (by positivity),
    abs_le]
  constructor
  · rcases le_or_gt x 1 with hx1 | hx1
    · have hb := Real.exp_bound' hx.le hx1 (n := 3) (by norm_num)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one,
        pow_zero, pow_one, Nat.succ_eq_add_one, Nat.cast_ofNat] at hb
      norm_num at hb
      have hE' : E ≤ x + x ^ 2 / 2 + 2 / 9 * x ^ 3 := by rw [hE]; nlinarith
      nlinarith [mul_pos hx hx, mul_pos (mul_pos hx hx) hx, mul_pos (mul_pos hx hx) hE0,
        mul_le_mul_of_nonneg_left hE' (by positivity : (0 : ℝ) ≤ x ^ 2)]
    · nlinarith [mul_pos hx hE0, mul_pos (mul_pos hx hx) hE0]
  · nlinarith [mul_pos hx hx, mul_pos (mul_pos hx hx) hx, mul_pos (mul_pos hx hx) hE0,
      mul_pos (mul_pos (mul_pos hx hx) hx) hx]

/-- DLMF 25.5.6: `ζ(s) = ½ + 1/(s-1) + Γ(s)⁻¹ ∫₀^∞ (1/(eˣ-1) - 1/x + ½) x^{s-1} e^{-x} dx` for
`Re s > -1`, `s ≠ 1` (at `s = 0` the factor `1/Γ(0)` is `0`). -/
@[dlmf 25.5.E6]
theorem riemannZeta_eq_half_add_integral {s : ℂ} (hs : -1 < s.re) (hs1 : s ≠ 1) :
    IntegrableOn (fun x : ℝ => (1 / (cexp x - 1) - 1 / x + 1 / 2) * (x : ℂ) ^ (s - 1) /
        cexp x) (Ioi 0) ∧
      riemannZeta s = 1 / 2 + 1 / (s - 1) + 1 / Gamma s * ∫ x in Ioi (0 : ℝ),
        (1 / (cexp x - 1) - 1 / x + 1 / 2) * (x : ℂ) ^ (s - 1) / cexp x := by
  set Jf : ℂ → ℝ → ℂ := fun z x => (1 / (cexp x - 1) - 1 / x + 1 / 2) * (x : ℂ) ^ (z - 1) /
    cexp x with hJf
  set ph : ℝ → ℂ := fun x => (1 / (cexp x - 1) - 1 / x + 1 / 2) / x / cexp x with hph
  have hreal : ∀ x : ℝ, 0 < x → (1 / (cexp x - 1) - 1 / x + 1 / 2 : ℂ) =
      ((1 / (Real.exp x - 1) - 1 / x + 1 / 2 : ℝ) : ℂ) := fun x _ => by
    push_cast; rw [← ofReal_exp]
  have hphb : ∀ x : ℝ, 0 < x → ‖ph x‖ ≤ Real.exp (-x) := by
    intro x hx
    simp only [hph]
    rw [hreal x hx, norm_div, norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hx, Complex.norm_exp_ofReal, Real.exp_neg]
    rw [div_div, div_le_iff₀ (by positivity)]
    have := r25a_abs_bose_sub_le hx
    calc _ ≤ x := this
      _ = (Real.exp x)⁻¹ * (x * Real.exp x) := by field_simp
  have hphc : ContinuousOn ph (Ioi 0) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have h1 : cexp (x : ℂ) - 1 ≠ 0 := q25a_exp_sub_one_ne hx0
    have h2 : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    refine ContinuousAt.continuousWithinAt ?_
    simp only [hph]
    refine ContinuousAt.div (ContinuousAt.div ?_ (by fun_prop) h2) (by fun_prop)
      (Complex.exp_ne_zero _)
    refine ContinuousAt.add (ContinuousAt.sub ?_ ?_) continuousAt_const
    · exact continuousAt_const.div (by fun_prop) h1
    · exact continuousAt_const.div (by fun_prop) h2
  have hIph : ∀ z : ℂ, ∀ x : ℝ, 0 < x → Jf z x = (x : ℂ) ^ (z + 1 - 1) * ph x := by
    intro z x hx
    have h2 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    simp only [hJf, hph]
    rw [show z + 1 - 1 = (z - 1) + 1 by ring, cpow_add _ _ h2, cpow_one]
    field_simp
  -- integrability for `Re z > -1`
  have hint : ∀ z : ℂ, -1 < z.re → IntegrableOn (Jf z) (Ioi 0) := by
    intro z hz
    have hz' : 0 < (z + 1).re := by simp; linarith
    refine (show Integrable _ (volume.restrict (Ioi (0 : ℝ))) from
      DLMF.Gamma.integrableOn_cpow_mul_exp_neg_mul hz' one_pos).norm.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine ContinuousOn.congr (f := fun x : ℝ => (x : ℂ) ^ (z + 1 - 1) * ph x) ?_
        (fun x hx => hIph z x hx)
      refine ContinuousOn.mul (fun x hx => ?_) hphc
      exact (continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt hx))).continuousWithinAt
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : (0 : ℝ) < x := hx
      rw [hIph z x hx0, norm_mul, norm_mul, ofReal_one, one_mul,
        show -((x : ℂ)) = ((-x : ℝ) : ℂ) by push_cast; ring, norm_exp_ofReal]
      exact mul_le_mul_of_nonneg_left (hphb x hx0) (norm_nonneg _)
  refine ⟨hint s hs, ?_⟩
  -- the case `Re s > 1`
  have hgt : ∀ z : ℂ, 1 < z.re → riemannZeta z = 1 / 2 + 1 / (z - 1) +
      1 / Gamma z * ∫ x in Ioi (0 : ℝ), Jf z x := by
    intro z hz
    have hz0 : 0 < z.re := by linarith
    have hz1 : 0 < (z - 1).re := by simp; linarith
    have hA := q25a_integrableOn_exp_sub_one hz
    have hB := Complex.GammaIntegral_convergent hz0
    have hC := Complex.GammaIntegral_convergent hz1
    have hsplit : ∀ x ∈ Ioi (0 : ℝ), Jf z x = (x : ℂ) ^ (z - 1) / (cexp x - 1) -
        (((-x).exp : ℝ) : ℂ) * (x : ℂ) ^ (z - 1) - (((-x).exp : ℝ) : ℂ) * (x : ℂ) ^ (z - 1 - 1) +
        1 / 2 * ((((-x).exp : ℝ) : ℂ) * (x : ℂ) ^ (z - 1)) := by
      intro x hx
      have hx0 : (0 : ℝ) < x := hx
      have h1 := q25a_exp_sub_one_ne hx0
      have h2 : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
      have h3 : cexp (x : ℂ) ≠ 0 := Complex.exp_ne_zero _
      simp only [hJf]
      rw [show z - 1 = (z - 1 - 1) + 1 by ring, cpow_add _ _ h2, cpow_one, ofReal_exp,
        ofReal_neg, Complex.exp_neg]
      field_simp
      ring_nf
    rw [setIntegral_congr_fun measurableSet_Ioi hsplit, integral_add ?i1 ?i2,
      integral_sub ?i3 ?i4, integral_sub ?i5 ?i6, integral_const_mul]
    case i1 => exact (hA.sub hB).sub hC
    case i2 => exact hB.const_mul _
    case i3 => exact hA.sub hB
    case i4 => exact hC
    case i5 => exact hA
    case i6 => exact hB
    have hA' : ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (z - 1) / (cexp x - 1) = Gamma z * riemannZeta z := by
      have h := (riemannZeta_eq_integral_exp_sub_one hz).2
      have hG : Gamma z ≠ 0 := Gamma_ne_zero_of_re_pos hz0
      rw [h]; field_simp
    have hB' : ∫ x in Ioi (0 : ℝ), (((-x).exp : ℝ) : ℂ) * (x : ℂ) ^ (z - 1) = Gamma z :=
      (Gamma_eq_integral hz0).symm
    have hC' : ∫ x in Ioi (0 : ℝ), (((-x).exp : ℝ) : ℂ) * (x : ℂ) ^ (z - 1 - 1) = Gamma (z - 1) :=
      (Gamma_eq_integral hz1).symm
    rw [hA', hB', hC']
    have hz1' : z - 1 ≠ 0 := by
      intro h; have := congrArg re h; simp at this; linarith
    have hGz : Gamma z = (z - 1) * Gamma (z - 1) := by
      rw [← Complex.Gamma_add_one _ hz1', sub_add_cancel]
    have hG : Gamma z ≠ 0 := Gamma_ne_zero_of_re_pos hz0
    have hG1 : Gamma (z - 1) ≠ 0 := Gamma_ne_zero_of_re_pos hz1
    rw [hGz]
    field_simp
    ring
  set U : Set ℂ := {s : ℂ | -1 < s.re} \ {s : ℂ | s.im = 0 ∧ 1 ≤ s.re} with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const continuous_re).sdiff
    ((isClosed_eq continuous_im continuous_const).inter
      (isClosed_le continuous_const continuous_re))
  have hne1 : ∀ z ∈ U, z ≠ 1 := fun z hz h => hz.2 ⟨by rw [h]; simp, by rw [h]; simp⟩
  have hF : DifferentiableOn ℂ riemannZeta U := fun z hz =>
    (differentiableAt_riemannZeta (hne1 z hz)).differentiableWithinAt
  have hM := q25a_differentiableOn_mellin hphc hphb
  have hG : DifferentiableOn ℂ (fun z => 1 / 2 + 1 / (z - 1) + 1 / Gamma z *
      ∫ x in Ioi (0 : ℝ), Jf z x) U := by
    have hMI : DifferentiableOn ℂ (fun z => ∫ x in Ioi (0 : ℝ), Jf z x) U := by
      have h1 : DifferentiableOn ℂ (fun z : ℂ => ∫ x in Ioi (0 : ℝ),
          (x : ℂ) ^ (z + 1 - 1) * ph x) U :=
        hM.comp (differentiableOn_id.add_const 1) (fun z hz => by
          have h := hz.1
          simp only [Set.mem_ofPred_eq] at h
          show 0 < (z + 1).re
          simp; linarith)
      refine h1.congr fun z _ => setIntegral_congr_fun measurableSet_Ioi fun x hx => hIph z x hx
    refine DifferentiableOn.add (DifferentiableOn.add (differentiableOn_const _) ?_) ?_
    · exact DifferentiableOn.div (differentiableOn_const _) (differentiableOn_id.sub_const 1)
        fun z hz => sub_ne_zero.mpr (hne1 z hz)
    · refine DifferentiableOn.mul ?_ hMI
      simpa [one_div] using differentiable_one_div_Gamma.differentiableOn
  have hz0 : (2 + I : ℂ) ∈ U := ⟨by show (-1 : ℝ) < (2 + I : ℂ).re; simp; norm_num,
    by rintro ⟨h, -⟩; simp at h⟩
  have hev : riemannZeta =ᶠ[𝓝 (2 + I : ℂ)]
      (fun z => 1 / 2 + 1 / (z - 1) + 1 / Gamma z * ∫ x in Ioi (0 : ℝ), Jf z x) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show (1 : ℝ) < (2 + I : ℂ).re by simp)] with z hz
    exact hgt z hz
  have heq := (hF.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
    (hG.analyticOnNhd hUo) (q25a_isPreconnected_ray (a := -1) (c := 1 / 2) (by norm_num)
      (by norm_num)) hz0 hev
  by_cases hsU : s ∈ U
  · exact heq hsU
  · have hray : s.im = 0 ∧ 1 ≤ s.re := by
      by_contra h; exact hsU ⟨hs, h⟩
    have hre : 1 < s.re := by
      rcases eq_or_lt_of_le hray.2 with h | h
      · exfalso; apply hs1; apply Complex.ext <;> simp [hray.1, ← h]
      · exact h
    exact hgt s hre

/-- DLMF 25.5.7: for `n ≥ 1`, `Re s > -(2n+1)`, `s ≠ 1`,
`ζ(s) = ½ + 1/(s-1) + ∑_{m=1}^{n} (B_{2m}/(2m)!) (s)_{2m-1}
  + Γ(s)⁻¹ ∫₀^∞ (1/(eˣ-1) - 1/x + ½ - ∑_{m=1}^{n} (B_{2m}/(2m)!) x^{2m-1}) x^{s-1} e^{-x} dx`,
with the Pochhammer symbol `(s)_k = ascPochhammer ℂ k` evaluated at `s`. -/
@[dlmf 25.5.E7]
theorem riemannZeta_eq_half_add_bernoulli_integral {s : ℂ} {n : ℕ} (hn : 1 ≤ n)
    (hs : -(2 * n + 1 : ℝ) < s.re) (hs1 : s ≠ 1) :
    IntegrableOn (fun x : ℝ => (1 / (cexp x - 1) - 1 / x + 1 / 2 -
        ∑ m ∈ Finset.Icc (1 : ℕ) n, (bernoulli (2 * m) : ℂ) / (2 * m).factorial *
          (x : ℂ) ^ (2 * m - 1)) * (x : ℂ) ^ (s - 1) / cexp x) (Ioi 0) ∧
      riemannZeta s = 1 / 2 + 1 / (s - 1) +
        ∑ m ∈ Finset.Icc (1 : ℕ) n, (bernoulli (2 * m) : ℂ) / (2 * m).factorial *
          (ascPochhammer ℂ (2 * m - 1)).eval s +
        1 / Gamma s * ∫ x in Ioi (0 : ℝ), (1 / (cexp x - 1) - 1 / x + 1 / 2 -
          ∑ m ∈ Finset.Icc (1 : ℕ) n, (bernoulli (2 * m) : ℂ) / (2 * m).factorial *
            (x : ℂ) ^ (2 * m - 1)) * (x : ℂ) ^ (s - 1) / cexp x := by
  sorry

/-- DLMF 25.5.8: `ζ(s) = (2(1 - 2^{-s}) Γ(s))⁻¹ ∫₀^∞ x^{s-1}/sinh x dx` for `Re s > 1` (where
`1 - 2^{-s} ≠ 0`). -/
@[dlmf 25.5.E8]
theorem riemannZeta_eq_integral_sinh {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) / sinh x) (Ioi 0) ∧
      riemannZeta s = 1 / (2 * (1 - 2 ^ (-s)) * Gamma s) *
        ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) / sinh x := by
  set h : ℝ → ℂ := fun x => (x : ℂ) ^ (s - 1) / (cexp x - 1) with hh
  have hI := q25a_integrableOn_exp_sub_one hs
  obtain ⟨hI2, hV2⟩ := q25a_scale_two hI
  have hval := (riemannZeta_eq_integral_exp_sub_one hs).2
  have hG : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hpt : ∀ x : ℝ, 0 < x → (x : ℂ) ^ (s - 1) / sinh x =
      2 * h x - 2 * (2 : ℂ) ^ (1 - s) * h (2 * x) := by
    intro x hx
    simp only [hh]
    rw [ofReal_mul, mul_cpow_ofReal_nonneg (by norm_num) hx.le, ofReal_ofNat]
    have hE := q25a_exp_sub_one_ne hx
    have hE2 : cexp (2 * (x : ℂ)) - 1 ≠ 0 := by
      have := q25a_exp_sub_one_ne (by linarith : (0 : ℝ) < 2 * x); push_cast at this; exact this
    have hc : (2 : ℂ) ^ (1 - s) * (2 : ℂ) ^ (s - 1) = 1 := by
      rw [← cpow_add _ _ h2]; simp
    have hsh : sinh (x : ℂ) = (cexp x - 1) * (cexp x + 1) / (2 * cexp x) := by
      rw [Complex.sinh, Complex.exp_neg]
      field_simp
      ring
    have h0 : cexp (x : ℂ) ≠ 0 := Complex.exp_ne_zero _
    have hE1 : cexp (x : ℂ) + 1 ≠ 0 := by
      rw [← ofReal_exp]; exact_mod_cast (by positivity : Real.exp x + 1 ≠ 0)
    rw [hsh, show cexp (2 * (x : ℂ)) - 1 = (cexp x - 1) * (cexp x + 1) by
      rw [show 2 * (x : ℂ) = x + x by ring, Complex.exp_add]; ring]
    rw [show 2 * (2 : ℂ) ^ (1 - s) * ((2 : ℂ) ^ (s - 1) * (x : ℂ) ^ (s - 1) /
        ((cexp x - 1) * (cexp x + 1))) = 2 * ((2 : ℂ) ^ (1 - s) * (2 : ℂ) ^ (s - 1)) *
        ((x : ℂ) ^ (s - 1) / ((cexp x - 1) * (cexp x + 1))) by ring, hc]
    field_simp
    ring
  have hInt : IntegrableOn (fun x : ℝ => 2 * h x - 2 * (2 : ℂ) ^ (1 - s) * h (2 * x)) (Ioi 0) :=
    (hI.const_mul 2).sub (hI2.const_mul _)
  have hInt' : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) / sinh x) (Ioi 0) :=
    hInt.congr_fun (fun x hx => (hpt x hx).symm) measurableSet_Ioi
  refine ⟨hInt', ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub (hI.const_mul 2)
    (hI2.const_mul _), integral_const_mul, integral_const_mul, hV2]
  have hJ : ∫ x in Ioi (0 : ℝ), h x = Gamma s * riemannZeta s := by
    rw [hval]; field_simp; rfl
  rw [hJ]
  have h1s : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, cpow_add _ _ h2, cpow_one]
  rw [h1s]
  have hne : (1 : ℂ) - 2 ^ (-s) ≠ 0 := by
    have h2s : ‖(2 : ℂ) ^ (-s)‖ < 1 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, norm_cpow_eq_rpow_re_of_pos (by norm_num)]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by simp; linarith)
    intro h0; rw [sub_eq_zero] at h0; rw [← h0] at h2s; simp at h2s
  field_simp

/-- DLMF 25.5.9: `ζ(s) = 2^{s-1} Γ(s+1)⁻¹ ∫₀^∞ xˢ/sinh² x dx` for `Re s > 1`. -/
@[dlmf 25.5.E9]
theorem riemannZeta_eq_integral_sinh_sq {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ s / sinh x ^ 2) (Ioi 0) ∧
      riemannZeta s = 2 ^ (s - 1) / Gamma (s + 1) *
        ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ s / sinh x ^ 2 := by
  set h : ℝ → ℂ := fun x => cexp x * (x : ℂ) ^ s / (cexp x - 1) ^ 2 with hh
  have hI := q25a_integrableOn_exp_sub_one_sq hs
  obtain ⟨hI2, hV2⟩ := q25a_scale_two hI
  have hG : Gamma (s + 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hpt : ∀ x : ℝ, 0 < x → (x : ℂ) ^ s / sinh x ^ 2 = 4 * (2 : ℂ) ^ (-s) * h (2 * x) := by
    intro x hx
    simp only [hh]
    rw [ofReal_mul, mul_cpow_ofReal_nonneg (by norm_num) hx.le, ofReal_ofNat]
    have hc : (2 : ℂ) ^ (-s) * (2 : ℂ) ^ s = 1 := by
      rw [← cpow_add _ _ h2]; simp
    have hsh : sinh (x : ℂ) = (cexp x - 1) * (cexp x + 1) / (2 * cexp x) := by
      rw [Complex.sinh, Complex.exp_neg]
      field_simp
      ring
    have hE := q25a_exp_sub_one_ne hx
    have h0 : cexp (x : ℂ) ≠ 0 := Complex.exp_ne_zero _
    have hE1 : cexp (x : ℂ) + 1 ≠ 0 := by
      rw [← ofReal_exp]; exact_mod_cast (by positivity : Real.exp x + 1 ≠ 0)
    have he2 : cexp (2 * (x : ℂ)) = cexp x * cexp x := by
      rw [show 2 * (x : ℂ) = x + x by ring, Complex.exp_add]
    rw [hsh, he2]
    rw [show 4 * (2 : ℂ) ^ (-s) * (cexp x * cexp x * ((2 : ℂ) ^ s * (x : ℂ) ^ s) /
        (cexp x * cexp x - 1) ^ 2) = 4 * ((2 : ℂ) ^ (-s) * (2 : ℂ) ^ s) *
        (cexp x * cexp x * (x : ℂ) ^ s / (cexp x * cexp x - 1) ^ 2) by ring, hc]
    rw [show cexp (x : ℂ) * cexp x - 1 = (cexp x - 1) * (cexp x + 1) by ring]
    field_simp
    ring
  have hInt' : IntegrableOn (fun x : ℝ => (x : ℂ) ^ s / sinh x ^ 2) (Ioi 0) :=
    IntegrableOn.congr_fun (hI2.const_mul (4 * (2 : ℂ) ^ (-s)))
      (fun x hx => (hpt x hx).symm) measurableSet_Ioi
  refine ⟨hInt', ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, hV2,
    q25a_integral_exp_sub_one_sq hs]
  have hc : (2 : ℂ) ^ (s - 1) * (2 : ℂ) ^ (-s) = 1 / 2 := by
    rw [← cpow_add _ _ h2, show s - 1 + -s = -1 by ring, cpow_neg_one, one_div]
  rw [show 2 ^ (s - 1) / Gamma (s + 1) * (4 * 2 ^ (-s) * (1 / 2 * (Gamma (s + 1) *
      riemannZeta s))) = 2 * ((2 : ℂ) ^ (s - 1) * (2 : ℂ) ^ (-s)) * (Gamma (s + 1) /
      Gamma (s + 1)) * riemannZeta s by ring, hc, div_self hG]
  ring

/-- DLMF 25.5.10 (multiplied form): for `s ≠ 1`,
`(1 - 2^{1-s}) ζ(s) = 2^{s-1} ∫₀^∞ cos(s arctan x) / ((1+x²)^{s/2} cosh(πx/2)) dx`. -/
@[dlmf 25.5.E10]
theorem riemannZeta_eq_integral_arctan_cosh {s : ℂ} (hs1 : s ≠ 1) :
    IntegrableOn (fun x : ℝ => cos (s * Real.arctan x) /
        (((1 + x ^ 2 : ℝ) : ℂ) ^ (s / 2) * cosh (π * x / 2))) (Ioi 0) ∧
      (1 - 2 ^ (1 - s)) * riemannZeta s = 2 ^ (s - 1) * ∫ x in Ioi (0 : ℝ),
        cos (s * Real.arctan x) / (((1 + x ^ 2 : ℝ) : ℂ) ^ (s / 2) * cosh (π * x / 2)) := by
  sorry

/-- DLMF 25.5.11: for `s ≠ 1`,
`ζ(s) = ½ + 1/(s-1) + 2 ∫₀^∞ sin(s arctan x) / ((1+x²)^{s/2} (e^{2πx} - 1)) dx`. -/
@[dlmf 25.5.E11]
theorem riemannZeta_eq_integral_arctan_exp_sub_one {s : ℂ} (hs1 : s ≠ 1) :
    IntegrableOn (fun x : ℝ => sin (s * Real.arctan x) /
        (((1 + x ^ 2 : ℝ) : ℂ) ^ (s / 2) * (cexp (2 * π * x) - 1))) (Ioi 0) ∧
      riemannZeta s = 1 / 2 + 1 / (s - 1) + 2 * ∫ x in Ioi (0 : ℝ),
        sin (s * Real.arctan x) / (((1 + x ^ 2 : ℝ) : ℂ) ^ (s / 2) * (cexp (2 * π * x) - 1)) := by
  sorry

/-- DLMF 25.5.12: for `s ≠ 1`,
`ζ(s) = 2^{s-1}/(s-1) - 2^s ∫₀^∞ sin(s arctan x) / ((1+x²)^{s/2} (e^{πx} + 1)) dx`. -/
@[dlmf 25.5.E12]
theorem riemannZeta_eq_integral_arctan_exp_add_one {s : ℂ} (hs1 : s ≠ 1) :
    IntegrableOn (fun x : ℝ => sin (s * Real.arctan x) /
        (((1 + x ^ 2 : ℝ) : ℂ) ^ (s / 2) * (cexp (π * x) + 1))) (Ioi 0) ∧
      riemannZeta s = 2 ^ (s - 1) / (s - 1) - 2 ^ s * ∫ x in Ioi (0 : ℝ),
        sin (s * Real.arctan x) / (((1 + x ^ 2 : ℝ) : ℂ) ^ (s / 2) * (cexp (π * x) + 1)) := by
  sorry

/-! ### §25.5(ii) In terms of other functions -/

/-- DLMF 25.5.14: `ω(x) = ∑_{n≥1} e^{-n²πx}` (for `x > 0`; the `tsum` is `0` where the series
diverges, i.e. for `x ≤ 0`). -/
@[dlmf 25.5.E14]
def zetaOmega (x : ℝ) : ℝ :=
  ∑' n : ℕ, Real.exp (-((n + 1 : ℝ) ^ 2) * π * x)

/-- DLMF 25.5.14: `ω(x) = ½ (θ₃(0|ix) - 1)` for `x > 0`, with Mathlib's
`jacobiTheta τ = θ₃(0|τ) = ∑_{n ∈ ℤ} e^{πin²τ}`. -/
@[dlmf 25.5.E14]
theorem zetaOmega_eq_jacobiTheta {x : ℝ} (hx : 0 < x) :
    (zetaOmega x : ℂ) = (jacobiTheta (I * x) - 1) / 2 := by
  have hτ : 0 < (I * (x : ℂ)).im := by simpa using hx
  rw [jacobiTheta_eq_tsum_nat hτ]
  rw [zetaOmega, Complex.ofReal_tsum]
  have : ∀ n : ℕ, ((Real.exp (-((n + 1 : ℝ) ^ 2) * π * x) : ℝ) : ℂ) =
      cexp (π * I * ((n : ℂ) + 1) ^ 2 * (I * x)) := by
    intro n
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring_nf
    rw [I_sq]
    ring
  simp_rw [this]
  ring

section s25a
open HurwitzZeta

/-- The tail `x ↦ θ(x) - 1` of the even kernel on `(1, ∞)`. -/
noncomputable def s25a_tail : ℝ → ℂ :=
  (Set.Ioi 1).indicator (fun x => (hurwitzEvenFEPair 0).f x - (hurwitzEvenFEPair 0).f₀)

/-- On `(1, ∞)` the tail is `2ω(x)`. -/
lemma s25a_tail_eq {x : ℝ} (hx : 1 < x) : s25a_tail x = 2 * (zetaOmega x : ℂ) := by
  have hx0 : 0 < x := by linarith
  rw [s25a_tail, indicator_of_mem (Set.mem_Ioi.mpr hx), zetaOmega_eq_jacobiTheta hx0]
  simp only [hurwitzEvenFEPair, Function.comp_apply, ite_true]
  rw [show (0 : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) by simp, evenKernel_def,
    jacobiTheta_eq_jacobiTheta₂]
  simp
  ring_nf

/-- The modified even kernel is `tail(x) + x^{-1/2} tail(1/x)` on `(0, ∞)`. -/
lemma s25a_f_modif_eq {x : ℝ} (hx : 0 < x) :
    (hurwitzEvenFEPair 0).f_modif x =
      s25a_tail x + (x : ℂ) ^ (-(1 / 2 : ℂ)) * s25a_tail x⁻¹ := by
  rcases lt_trichotomy x 1 with h | rfl | h
  · have hi : 1 < x⁻¹ := one_lt_inv_iff₀.mpr ⟨hx, h⟩
    rw [WeakFEPair.f_modif, Pi.add_apply, indicator_of_notMem (notMem_Ioi.mpr h.le),
      indicator_of_mem (Set.mem_Ioo.mpr ⟨hx, h⟩), s25a_tail,
      indicator_of_notMem (notMem_Ioi.mpr h.le), indicator_of_mem (Set.mem_Ioi.mpr hi)]
    simp only [hurwitzEvenFEPair, Function.comp_apply, ite_true, zero_add, smul_eq_mul, mul_one,
      one_mul]
    rw [evenKernel_functional_equation, ← evenKernel_eq_cosKernel_of_zero]
    push_cast
    rw [ofReal_cpow hx.le, ofReal_cpow hx.le, cpow_neg, one_div, one_div]
    push_cast
    rw [cpow_neg, one_div x, one_div (2 : ℂ)]
    ring
  · simp [WeakFEPair.f_modif, s25a_tail]
  · have hi : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ h
    rw [WeakFEPair.f_modif, Pi.add_apply, indicator_of_notMem (notMem_Ioo_of_ge h.le),
      s25a_tail, indicator_of_notMem (notMem_Ioi.mpr hi.le)]
    simp


/-- The tail has a convergent Mellin transform everywhere. -/
lemma s25a_tail_mellinConvergent (a : ℂ) : MellinConvergent s25a_tail a := by
  have hloc : LocallyIntegrableOn s25a_tail (Set.Ioi 0) := by
    intro x hx
    obtain ⟨t, ht, ht'⟩ := (hurwitzEvenFEPair 0).hf_int.sub (locallyIntegrableOn_const _) x hx
    exact ⟨t, ht, ht'.indicator measurableSet_Ioi⟩
  refine mellinConvergent_of_isBigO_rpow (a := a.re + 1) (b := a.re - 1) hloc ?_
    (by linarith) ?_ (by linarith)
  · refine ((hurwitzEvenFEPair 0).hf_top (-(a.re + 1))).congr' ?_ .rfl
    filter_upwards [eventually_gt_atTop 1] with x hx
    rw [s25a_tail, indicator_of_mem (Set.mem_Ioi.mpr hx)]
  · refine (Asymptotics.isBigO_zero _ _).congr' ?_ .rfl
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    rw [s25a_tail, indicator_of_notMem (notMem_Ioi.mpr hx.2.le)]

/-- The Mellin transform of the tail as an integral of `ω` over `(1, ∞)`. -/
lemma s25a_tail_mellin (a : ℂ) :
    mellin s25a_tail a = 2 * ∫ x in Set.Ioi (1 : ℝ), (x : ℂ) ^ a * zetaOmega x / x := by
  rw [mellin, ← integral_const_mul]
  have : ∀ x ∈ Set.Ioi (0 : ℝ), (x : ℂ) ^ (a - 1) • s25a_tail x =
      (Set.Ioi 1).indicator (fun x : ℝ => 2 * ((x : ℂ) ^ a * zetaOmega x / x)) x := by
    intro x hx
    by_cases h : 1 < x
    · rw [indicator_of_mem (Set.mem_Ioi.mpr h), s25a_tail_eq h, smul_eq_mul,
        cpow_sub _ _ (ofReal_ne_zero.mpr (ne_of_gt hx)), cpow_one]
      ring
    · rw [indicator_of_notMem (notMem_Ioi.mpr (not_lt.mp h)), s25a_tail,
        indicator_of_notMem (notMem_Ioi.mpr (not_lt.mp h)), smul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi this, setIntegral_indicator measurableSet_Ioi,
    Set.Ioi_inter_Ioi, max_eq_right zero_le_one]

/-- `x^a ω(x)/x` is integrable on `(1, ∞)`. -/
lemma s25a_integrableOn (a : ℂ) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ a * zetaOmega x / x) (Set.Ioi 1) := by
  have h := ((s25a_tail_mellinConvergent a).mono_set (Set.Ioi_subset_Ioi zero_le_one)).const_mul
    (1 / 2 : ℂ)
  refine IntegrableOn.congr_fun h (fun x hx => ?_) measurableSet_Ioi
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  simp only [smul_eq_mul]
  rw [s25a_tail_eq hx, cpow_sub _ _ (ofReal_ne_zero.mpr hx0.ne'), cpow_one]
  ring

/-- The theta split of `Λ₀(s/2)`. -/
lemma s25a_Λ₀ (s : ℂ) : (hurwitzEvenFEPair 0).Λ₀ (s / 2) =
    mellin s25a_tail (s / 2) + mellin s25a_tail ((1 - s) / 2) := by
  have h2 : MellinConvergent (fun x : ℝ => (x : ℂ) ^ (-(1 / 2 : ℂ)) • s25a_tail x⁻¹)
      (s / 2) := by
    rw [MellinConvergent.cpow_smul]
    have e : (s / 2 + -(1 / 2)) / ((-1 : ℝ) : ℂ) = (1 - s) / 2 := by push_cast; ring
    have := (MellinConvergent.comp_rpow (f := s25a_tail) (s := s / 2 + -(1 / 2))
      (a := -1) (by norm_num)).mpr (by rw [e]; exact s25a_tail_mellinConvergent _)
    simpa only [Real.rpow_neg_one] using this
  have h3 : mellin (fun x : ℝ => (x : ℂ) ^ (-(1 / 2 : ℂ)) • s25a_tail x⁻¹) (s / 2) =
      mellin s25a_tail ((1 - s) / 2) := by
    rw [mellin_cpow_smul, mellin_comp_inv]; congr 1; ring
  rw [WeakFEPair.Λ₀, ← h3, ← (hasMellin_add (s25a_tail_mellinConvergent _) h2).2]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  simp only [s25a_f_modif_eq hx, smul_eq_mul]

end s25a

/-- DLMF 25.5.13: for `s ≠ 0, 1`,
`ζ(s) = π^{s/2}/(s(s-1)Γ(s/2)) + π^{s/2}/Γ(s/2) ∫₁^∞ (x^{s/2} + x^{(1-s)/2}) ω(x)/x dx`
(DLMF: `s ≠ 1`; at `s = 0` the printed first term is a removable `1/(0·∞)` form). -/
@[dlmf 25.5.E13]
theorem riemannZeta_eq_integral_zetaOmega {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    IntegrableOn (fun x : ℝ => ((x : ℂ) ^ (s / 2) + (x : ℂ) ^ ((1 - s) / 2)) * zetaOmega x / x)
        (Ioi 1) ∧
      riemannZeta s = (π : ℂ) ^ (s / 2) / (s * (s - 1) * Gamma (s / 2)) +
        (π : ℂ) ^ (s / 2) / Gamma (s / 2) * ∫ x in Ioi (1 : ℝ),
          ((x : ℂ) ^ (s / 2) + (x : ℂ) ^ ((1 - s) / 2)) * zetaOmega x / x := by
  have he : (fun x : ℝ => ((x : ℂ) ^ (s / 2) + (x : ℂ) ^ ((1 - s) / 2)) * zetaOmega x / x) =
      fun x : ℝ => (x : ℂ) ^ (s / 2) * zetaOmega x / x +
        (x : ℂ) ^ ((1 - s) / 2) * zetaOmega x / x := by
    funext x; ring
  refine ⟨he ▸ (s25a_integrableOn _).add (s25a_integrableOn _), ?_⟩
  rw [he, integral_add (s25a_integrableOn _) (s25a_integrableOn _),
    riemannZeta_eq_completedRiemannZeta₀ hs0]
  have hc : completedRiemannZeta₀ s = (HurwitzZeta.hurwitzEvenFEPair 0).Λ₀ (s / 2) / 2 := rfl
  rw [hc, s25a_Λ₀, s25a_tail_mellin, s25a_tail_mellin]
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hs1'' : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hπ : (π : ℂ) ^ (-s / 2) = ((π : ℂ) ^ (s / 2))⁻¹ := by
    rw [neg_div, cpow_neg]
  have hπ0 : (π : ℂ) ^ (s / 2) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  rw [hπ]
  rcases eq_or_ne (Gamma (s / 2)) 0 with hG | hG
  · simp [hG]
  · field_simp
    ring


/-- DLMF 25.5.15: for `0 < Re s < 1`,
`ζ(s) = 1/(s-1) + (sin(πs)/π) ∫₀^∞ (ln(1+x) - ψ(1+x)) x^{-s} dx`. -/
@[dlmf 25.5.E15]
theorem riemannZeta_eq_integral_log_sub_digamma {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    IntegrableOn (fun x : ℝ => ((Real.log (1 + x) : ℂ) - digamma (1 + x)) * (x : ℂ) ^ (-s))
        (Ioi 0) ∧
      riemannZeta s = 1 / (s - 1) + sin (π * s) / π * ∫ x in Ioi (0 : ℝ),
        ((Real.log (1 + x) : ℂ) - digamma (1 + x)) * (x : ℂ) ^ (-s) := by
  sorry

/-- DLMF 25.5.16: for `0 < Re s < 2`, `s ≠ 1` (DLMF's wider range for this formula),
`ζ(s) = 1/(s-1) + (sin(πs)/(π(s-1))) ∫₀^∞ (1/(1+x) - ψ'(1+x)) x^{1-s} dx`. -/
@[dlmf 25.5.E16]
theorem riemannZeta_eq_integral_inv_sub_trigamma {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 2)
    (hs1 : s ≠ 1) :
    IntegrableOn (fun x : ℝ => (1 / (1 + (x : ℂ)) - DLMF.Gamma.polygamma 1 (1 + x)) *
        (x : ℂ) ^ (1 - s)) (Ioi 0) ∧
      riemannZeta s = 1 / (s - 1) + sin (π * s) / (π * (s - 1)) * ∫ x in Ioi (0 : ℝ),
        (1 / (1 + (x : ℂ)) - DLMF.Gamma.polygamma 1 (1 + x)) * (x : ℂ) ^ (1 - s) := by
  sorry

/-- The real kernel `tᵐ e^{-t}/(1 - e^{-t})` of the polygamma Laplace integral. -/
noncomputable def r25a_Ar (m : ℕ) (t : ℝ) : ℝ := t ^ m * Real.exp (-t) / (1 - Real.exp (-t))

lemma r25a_Ar_pos (m : ℕ) {t : ℝ} (ht : 0 < t) : 0 < r25a_Ar m t := by
  have : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  unfold r25a_Ar
  have := Real.exp_pos (-t)
  positivity

/-- `r25a_Ar m t · t^{σ-1} = t^{m+σ-1}/(eᵗ-1)`. -/
lemma r25a_Ar_mul_rpow (m : ℕ) (σ : ℝ) {t : ℝ} (ht : 0 < t) :
    r25a_Ar m t * t ^ (σ - 1) = t ^ ((m : ℝ) + σ - 1) / (Real.exp t - 1) := by
  have h1 : Real.exp t - 1 ≠ 0 := by
    have := Real.add_one_lt_exp (x := t) ht.ne'; linarith
  have h2 : 1 - Real.exp (-t) ≠ 0 := by
    have : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  rw [show (m : ℝ) + σ - 1 = (m : ℝ) + (σ - 1) by ring, Real.rpow_add ht, Real.rpow_natCast]
  unfold r25a_Ar
  rw [Real.exp_neg]
  have := Real.exp_pos t
  field_simp

/-- DLMF 25.5.19 core: `∫₀^∞ ψ^{(m)}(1+x) x^{-s} dx = (-1)^{m+1} Γ(1-s) Γ(m+s) ζ(m+s)`. -/
theorem r25a_integral_polygamma {s : ℂ} {m : ℕ} (hm : 1 ≤ m) (hs : 0 < s.re) (hs' : s.re < 1) :
    IntegrableOn (fun x : ℝ => DLMF.Gamma.polygamma m (1 + x) * (x : ℂ) ^ (-s)) (Ioi 0) ∧
      ∫ x in Ioi (0 : ℝ), DLMF.Gamma.polygamma m (1 + x) * (x : ℂ) ^ (-s) =
        (-1) ^ (m + 1) * (Gamma (1 - s) * Gamma (m + s) * riemannZeta (m + s)) := by
  set μ := volume.restrict (Ioi (0 : ℝ))
  set K : ℝ → ℝ → ℂ := fun x t =>
    (x : ℂ) ^ (-s) * cexp (-((t : ℂ) * x)) * (r25a_Ar m t : ℂ) with hK
  have h1s : 0 < (1 - s).re := by simp; linarith
  -- pointwise: the polygamma Laplace integral
  have hpt : ∀ x : ℝ, 0 < x → DLMF.Gamma.polygamma m (1 + x) * (x : ℂ) ^ (-s) =
      (-1) ^ (m + 1) * ∫ t in Ioi (0 : ℝ), K x t := by
    intro x hx
    have h := DLMF.Gamma.polygamma_eq_integral (n := m) (by omega) (x := 1 + x) (by linarith)
    push_cast at h
    rw [h, mul_comm, ← mul_assoc, mul_comm ((x : ℂ) ^ (-s)), mul_assoc,
      ← integral_const_mul]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := ht
    simp only [hK, r25a_Ar]
    push_cast
    rw [show -((1 + (x : ℂ)) * t) = -(t : ℂ) + -((t : ℂ) * x) by ring, Complex.exp_add]
    ring
  -- the `x`-integral for fixed `t`
  have hxint : ∀ t : ℝ, 0 < t → Integrable (fun x => K x t) μ := by
    intro t ht
    have := (DLMF.Gamma.integrableOn_cpow_mul_exp_neg_mul h1s ht).mul_const (r25a_Ar m t : ℂ)
    simp only [sub_sub_cancel_left] at this
    exact this
  have hxval : ∀ t : ℝ, 0 < t → ∫ x in Ioi (0 : ℝ), K x t =
      Gamma (1 - s) * (t : ℂ) ^ (s - 1) * (r25a_Ar m t : ℂ) := by
    intro t ht
    simp only [hK]
    rw [integral_mul_const]
    have h := DLMF.Gamma.integral_cpow_mul_exp_neg_mul_Ioi h1s (z := (t : ℂ)) (by simpa using ht)
    simp only [sub_sub_cancel_left] at h
    rw [h, show -(1 - s) = s - 1 by ring]
  have hxnorm : ∀ t : ℝ, 0 < t → ∫ x in Ioi (0 : ℝ), ‖K x t‖ =
      Real.Gamma (1 - s.re) * (t ^ ((m : ℝ) + s.re - 1) / (Real.exp t - 1)) := by
    intro t ht
    have hA := r25a_Ar_pos m ht
    have e : ∀ x ∈ Ioi (0 : ℝ), ‖K x t‖ = x ^ ((1 - s.re) - 1) * Real.exp (-(t * x)) *
        r25a_Ar m t := by
      intro x hx
      have hx0 : (0 : ℝ) < x := hx
      simp only [hK, norm_mul, norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hA, neg_re]
      rw [show -((t : ℂ) * x) = ((-(t * x) : ℝ) : ℂ) by push_cast; ring, norm_exp_ofReal]
      ring_nf
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_mul_const,
      Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith) ht,
      ← r25a_Ar_mul_rpow m s.re ht, one_div, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]
    ring_nf
  -- product integrability
  have hcont : ContinuousOn (fun p : ℝ × ℝ => K p.1 p.2) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    have hp1' : (0 : ℝ) < p.1 := hp1
    have hp2' : (0 : ℝ) < p.2 := hp2
    have hne : 1 - Real.exp (-p.2) ≠ 0 := by
      have : Real.exp (-p.2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      linarith
    refine ContinuousAt.continuousWithinAt ?_
    simp only [hK, r25a_Ar]
    refine ContinuousAt.mul (ContinuousAt.mul ?_ (by fun_prop)) ?_
    · exact (continuousAt_ofReal_cpow_const _ _ (Or.inr hp1'.ne')).comp continuousAt_fst
    · refine Complex.continuous_ofReal.continuousAt.comp ?_
      exact ContinuousAt.div (by fun_prop) (by fun_prop) hne
  have hmeas : AEStronglyMeasurable (Function.uncurry K) (μ.prod μ) := by
    rw [show μ.prod μ = volume.restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) by
      rw [Measure.volume_eq_prod, Measure.prod_restrict]]
    exact hcont.aestronglyMeasurable (measurableSet_Ioi.prod measurableSet_Ioi)
  have hms : 1 < ((m : ℂ) + s.re).re := by
    simp
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hint : Integrable (Function.uncurry K) (μ.prod μ) := by
    refine (integrable_prod_iff' hmeas).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hxint t ht
    · have h := ((q25a_integrableOn_exp_sub_one hms).norm.const_mul (Real.Gamma (1 - s.re)))
      refine h.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := ht
      simp only [Function.uncurry_apply_pair]
      rw [hxnorm t ht0, norm_div, norm_cpow_eq_rpow_re_of_pos ht0]
      congr 1
      have h1 : 0 < Real.exp t - 1 := by have := Real.add_one_lt_exp (x := t) ht0.ne'; linarith
      rw [show cexp (t : ℂ) - 1 = ((Real.exp t - 1 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos h1]
      simp
  have hLHS : ∀ x ∈ Ioi (0 : ℝ), DLMF.Gamma.polygamma m (1 + x) * (x : ℂ) ^ (-s) =
      (-1) ^ (m + 1) * ∫ t, Function.uncurry K (x, t) ∂μ := fun x hx => hpt x hx
  refine ⟨?_, ?_⟩
  · refine ((hint.integral_prod_left).const_mul ((-1) ^ (m + 1))).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using (hLHS x hx).symm
  · rw [setIntegral_congr_fun measurableSet_Ioi hLHS, integral_const_mul]
    congr 1
    have hsw := integral_integral_swap (μ := μ) (ν := μ) (f := K) hint
    simp only [Function.uncurry_apply_pair]
    rw [hsw, setIntegral_congr_fun measurableSet_Ioi (fun t ht => hxval t ht)]
    have hval := DLMF.Gamma.integral_cpow_mul_exp_div_one_sub_exp (s := (m : ℂ) + s)
      (by simpa using hms) (x := 1) one_pos
    have e : ∀ t ∈ Ioi (0 : ℝ), Gamma (1 - s) * (t : ℂ) ^ (s - 1) * (r25a_Ar m t : ℂ) =
        Gamma (1 - s) * ((t : ℂ) ^ ((m : ℂ) + s - 1) * cexp (-(((1 : ℝ) : ℂ) * t)) /
          (1 - cexp (-(t : ℂ)))) := by
      intro t ht
      have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
      simp only [r25a_Ar]
      push_cast
      rw [show (m : ℂ) + s - 1 = (m : ℂ) + (s - 1) by ring, cpow_add _ _ ht0, cpow_natCast]
      ring_nf
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul, hval,
      zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hms)]
    push_cast
    ring

lemma r25a_sin_pi_ne_zero {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) : sin (π * s) ≠ 0 := by
  rw [Ne, Complex.sin_eq_zero_iff]
  rintro ⟨k, hk⟩
  have h := congrArg re hk
  simp at h
  have hk' : s.re = k := by
    have := Real.pi_pos
    field_simp at h
    linarith
  rw [hk'] at hs hs'
  have h1 : (0 : ℤ) < k := by exact_mod_cast hs
  have h2 : k < (1 : ℤ) := by exact_mod_cast hs'
  omega

/-- DLMF 25.5.19 in the form proved, for use in 25.5.18. -/
lemma r25a_zeta_nat_add_eq_integral {s : ℂ} {m : ℕ} (hm : 1 ≤ m)
    (hs : 0 < s.re) (hs' : s.re < 1) :
    IntegrableOn (fun x : ℝ => DLMF.Gamma.polygamma m (1 + x) * (x : ℂ) ^ (-s)) (Ioi 0) ∧
      riemannZeta (m + s) = (-1) ^ (m - 1) * (Gamma s * sin (π * s) / (π * Gamma (m + s))) *
        ∫ x in Ioi (0 : ℝ), DLMF.Gamma.polygamma m (1 + x) * (x : ℂ) ^ (-s) := by
  obtain ⟨hI, hv⟩ := r25a_integral_polygamma hm hs hs'
  refine ⟨hI, ?_⟩
  rw [hv]
  have hsin := r25a_sin_pi_ne_zero hs hs'
  have hG : Gamma ((m : ℂ) + s) ≠ 0 := Gamma_ne_zero_of_re_pos (by
    simp; have : (0 : ℝ) ≤ m := m.cast_nonneg; linarith)
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hr := Complex.Gamma_mul_Gamma_one_sub s
  have hpow : (-1 : ℂ) ^ (m - 1) * (-1) ^ (m + 1) = 1 := by
    rw [← pow_add, show m - 1 + (m + 1) = 2 * m by omega, pow_mul]; norm_num
  have key : Gamma s * Gamma (1 - s) * sin (π * s) = π := by
    rw [hr]; field_simp
  calc riemannZeta (m + s)
      = ((-1 : ℂ) ^ (m - 1) * (-1) ^ (m + 1)) * (Gamma s * Gamma (1 - s) * sin (π * s)) / π *
          (Gamma (m + s) / Gamma (m + s)) * riemannZeta (m + s) := by
        rw [hpow, key, one_mul, div_self hπ, div_self hG]; ring
    _ = _ := by ring

/-- `∫₀^∞ u^{-s-1}(1 - e^{-u}) du = -Γ(-s)` for `0 < Re s < 1`, with integrability. -/
lemma r25a_integral_cpow_one_sub_exp {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-s - 1) * (1 - cexp (-(u : ℂ)))) (Ioi 0) ∧
    ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (-s - 1) * (1 - cexp (-(u : ℂ))) = -Gamma (-s) := by
  have h := DLMF.Gamma.Gamma_truncated_exp (z := -s) (n := 0) (by simp; linarith)
    (by simp; linarith)
  simp at h
  have hG : Gamma (-s) ≠ 0 := by
    refine Complex.Gamma_ne_zero fun m hm => ?_
    have := congrArg re hm; simp at this
    rw [this] at hs hs'
    have h1 : 0 < m := by exact_mod_cast hs
    have h2 : m < 1 := by exact_mod_cast hs'
    omega
  have hI : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-s - 1) * (cexp (-(u : ℂ)) - 1)) (Ioi 0) := by
    by_contra hn
    rw [integral_undef hn] at h
    exact hG h
  refine ⟨hI.neg.congr_fun (fun u _ => by simp; ring) measurableSet_Ioi, ?_⟩
  rw [h, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  ring

/-- Scaling: `x^w (1 - e^{-tx}) = t^{-w} g(tx)` with `g(u) = u^w (1 - e^{-u})`. -/
lemma r25a_cpow_one_sub_exp_scale (w : ℂ) {t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    (x : ℂ) ^ w * (1 - cexp (-((t : ℂ) * x))) =
      (t : ℂ) ^ (-w) * (((t * x : ℝ) : ℂ) ^ w * (1 - cexp (-((t * x : ℝ) : ℂ)))) := by
  rw [Complex.ofReal_mul, mul_cpow_ofReal_nonneg ht.le hx.le, cpow_neg]
  have : (t : ℂ) ^ w ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast ht.ne'))
  field_simp

/-- DLMF 25.5.17: for `0 < Re s < 1`,
`ζ(1+s) = (sin(πs)/π) ∫₀^∞ (γ + ψ(1+x)) x^{-s-1} dx`. -/
@[dlmf 25.5.E17]
theorem riemannZeta_one_add_eq_integral_digamma {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    IntegrableOn (fun x : ℝ => ((Real.eulerMascheroniConstant : ℂ) + digamma (1 + x)) *
        (x : ℂ) ^ (-s - 1)) (Ioi 0) ∧
      riemannZeta (1 + s) = sin (π * s) / π * ∫ x in Ioi (0 : ℝ),
        ((Real.eulerMascheroniConstant : ℂ) + digamma (1 + x)) * (x : ℂ) ^ (-s - 1) := by
  set μ := volume.restrict (Ioi (0 : ℝ))
  set w : ℂ := -s - 1 with hw
  set g : ℝ → ℂ := fun u => (u : ℂ) ^ w * (1 - cexp (-(u : ℂ))) with hg
  obtain ⟨hgI, hgV⟩ := r25a_integral_cpow_one_sub_exp hs hs'
  set C := ∫ u in Ioi (0 : ℝ), g u with hC
  set Cn := ∫ u in Ioi (0 : ℝ), ‖g u‖ with hCn
  set K : ℝ → ℝ → ℂ := fun x t =>
    (x : ℂ) ^ w * (1 - cexp (-((t : ℂ) * x))) * (1 / (cexp t - 1)) with hK
  have hscale : ∀ t : ℝ, 0 < t → IntegrableOn (fun x : ℝ => (x : ℂ) ^ w *
      (1 - cexp (-((t : ℂ) * x)))) (Ioi 0) ∧ ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ w *
      (1 - cexp (-((t : ℂ) * x))) = (t : ℂ) ^ s * C ∧
      ∫ x in Ioi (0 : ℝ), ‖(x : ℂ) ^ w * (1 - cexp (-((t : ℂ) * x)))‖ = t ^ s.re * Cn := by
    intro t ht
    have hgt : IntegrableOn (fun x => g (t * x)) (Ioi 0) :=
      (integrableOn_Ioi_comp_mul_left_iff g 0 ht).mpr (by simpa using hgI)
    have e := fun x (hx : x ∈ Ioi (0 : ℝ)) => r25a_cpow_one_sub_exp_scale w ht hx
    refine ⟨IntegrableOn.congr_fun (hgt.const_mul ((t : ℂ) ^ (-w)))
      (fun x hx => (e x hx).symm) measurableSet_Ioi, ?_, ?_⟩
    · rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul]
      have := integral_comp_mul_left_Ioi g 0 ht
      simp only [mul_zero] at this
      simp only [hg] at this ⊢
      rw [this, Complex.real_smul, ← mul_assoc, ofReal_inv, ← cpow_neg_one,
        ← cpow_add _ _ (by exact_mod_cast ht.ne')]
      congr 2
      rw [hw]; ring
    · have e' : ∀ x ∈ Ioi (0 : ℝ), ‖(x : ℂ) ^ w * (1 - cexp (-((t : ℂ) * x)))‖ =
          t ^ (s.re + 1) * ‖g (t * x)‖ := by
        intro x hx
        rw [e x hx, norm_mul, norm_cpow_eq_rpow_re_of_pos ht]
        simp [hg, hw, add_comm]
      rw [setIntegral_congr_fun measurableSet_Ioi e', integral_const_mul]
      have := integral_comp_mul_left_Ioi (fun u => ‖g u‖) 0 ht
      simp only [mul_zero, smul_eq_mul] at this
      rw [this, ← mul_assoc, ← Real.rpow_neg_one, ← Real.rpow_add ht]
      congr 2; ring
  -- the digamma Laplace integral
  have hpt : ∀ x : ℝ, 0 < x → ((Real.eulerMascheroniConstant : ℂ) + digamma (1 + x)) *
      (x : ℂ) ^ w = ∫ t in Ioi (0 : ℝ), K x t := by
    intro x hx
    have h1x : (0 : ℝ) < 1 + x := by linarith
    have hd := DLMF.Gamma.digamma_ofReal h1x
    push_cast at hd
    rw [hd, ← ofReal_add, add_comm, DLMF.Gamma.digamma_add_euler_Ioi h1x, ← integral_complex_ofReal,
      ← integral_mul_const]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := ht
    have h1 : cexp (t : ℂ) - 1 ≠ 0 := q25a_exp_sub_one_ne ht0
    have h2 : (1 : ℂ) - cexp (-(t : ℂ)) ≠ 0 := by
      rw [sub_ne_zero, ← ofReal_neg, ← ofReal_exp]
      exact_mod_cast (Real.exp_lt_one_iff.mpr (by linarith)).ne'
    simp only [hK]
    push_cast
    rw [show -(1 + (x : ℂ)) * t = -(t : ℂ) + -((t : ℂ) * x) by ring, Complex.exp_add]
    rw [Complex.exp_neg (t : ℂ)] at h2 ⊢
    have h3 : cexp (t : ℂ) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  -- Fubini
  have hcont : ContinuousOn (fun p : ℝ × ℝ => K p.1 p.2) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    have hp1' : (0 : ℝ) < p.1 := hp1
    have hp2' : (0 : ℝ) < p.2 := hp2
    refine ContinuousAt.continuousWithinAt ?_
    simp only [hK]
    refine ContinuousAt.mul (ContinuousAt.mul ?_ (by fun_prop)) ?_
    · exact (continuousAt_ofReal_cpow_const _ _ (Or.inr hp1'.ne')).comp continuousAt_fst
    · exact continuousAt_const.div (by fun_prop) (q25a_exp_sub_one_ne hp2')
  have hmeas : AEStronglyMeasurable (Function.uncurry K) (μ.prod μ) := by
    rw [show μ.prod μ = volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) by
      rw [Measure.volume_eq_prod, Measure.prod_restrict]]
    exact hcont.aestronglyMeasurable (measurableSet_Ioi.prod measurableSet_Ioi)
  have hBn : ∀ t : ℝ, 0 < t → ‖(1 : ℂ) / (cexp t - 1)‖ = 1 / (Real.exp t - 1) := by
    intro t ht
    have h1 : 0 < Real.exp t - 1 := by have := Real.add_one_lt_exp (x := t) ht.ne'; linarith
    rw [show cexp (t : ℂ) - 1 = ((Real.exp t - 1 : ℝ) : ℂ) by push_cast; rfl, norm_div,
      norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1]
  have hms : 1 < ((1 : ℂ) + s.re).re := by simp; linarith
  have hint : Integrable (Function.uncurry K) (μ.prod μ) := by
    refine (integrable_prod_iff' hmeas).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simpa only [Function.uncurry_apply_pair, hK] using
        (hscale t ht).1.mul_const ((1 : ℂ) / (cexp (t : ℂ) - 1))
    · have h := ((q25a_integrableOn_exp_sub_one hms).norm.mul_const Cn)
      refine h.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := ht
      simp only [Function.uncurry_apply_pair, hK]
      rw [show (fun x : ℝ => ‖(x : ℂ) ^ w * (1 - cexp (-((t : ℂ) * x))) * (1 / (cexp t - 1))‖) =
        fun x : ℝ => ‖(x : ℂ) ^ w * (1 - cexp (-((t : ℂ) * x)))‖ * ‖(1 : ℂ) / (cexp t - 1)‖ from
        funext fun x => norm_mul _ _]
      rw [integral_mul_const, (hscale t ht0).2.2, hBn t ht0, norm_div,
        norm_cpow_eq_rpow_re_of_pos ht0]
      have h1 : 0 < Real.exp t - 1 := by have := Real.add_one_lt_exp (x := t) ht0.ne'; linarith
      rw [show cexp (t : ℂ) - 1 = ((Real.exp t - 1 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos h1]
      simp
      ring
  have hLHS : ∀ x ∈ Ioi (0 : ℝ), ((Real.eulerMascheroniConstant : ℂ) + digamma (1 + x)) *
      (x : ℂ) ^ (-s - 1) = ∫ t, Function.uncurry K (x, t) ∂μ := fun x hx => hpt x hx
  have hval : ∫ x in Ioi (0 : ℝ), ((Real.eulerMascheroniConstant : ℂ) + digamma (1 + x)) *
      (x : ℂ) ^ (-s - 1) = C * (Gamma (s + 1) * riemannZeta (s + 1)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hLHS]
    have hsw := integral_integral_swap (μ := μ) (ν := μ) (f := K) hint
    simp only [Function.uncurry_apply_pair]
    rw [hsw]
    have e : ∀ t ∈ Ioi (0 : ℝ), ∫ x, K x t ∂μ =
        C * ((t : ℂ) ^ (s + 1 - 1) / (cexp t - 1)) := by
      intro t ht
      simp only [hK]
      rw [integral_mul_const, (hscale t ht).2.1, show s + 1 - 1 = s by ring]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul]
    have hz := riemannZeta_eq_integral_exp_sub_one (s := s + 1) (by simp; linarith)
    have hG : Gamma (s + 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
    rw [hz.2]
    field_simp
  refine ⟨?_, ?_⟩
  · refine (hint.integral_prod_left).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using (hLHS x hx).symm
  · rw [hval, hgV, add_comm (1 : ℂ) s]
    have hs0 : s ≠ 0 := by rintro rfl; simp at hs
    have hsin := r25a_sin_pi_ne_zero hs hs'
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hr := Complex.Gamma_mul_Gamma_one_sub s
    have h1 : Gamma (1 - s) = -s * Gamma (-s) := by
      rw [show 1 - s = -s + 1 by ring, Complex.Gamma_add_one _ (neg_ne_zero.mpr hs0)]
    rw [Complex.Gamma_add_one s hs0]
    have key : Gamma s * Gamma (1 - s) * sin (π * s) = π := by rw [hr]; field_simp
    rw [h1] at key
    have key2 : sin (π * s) * (-Gamma (-s) * (s * Gamma s)) = π := by linear_combination key
    rw [show sin (π * s) / π * (-Gamma (-s) * (s * Gamma s * riemannZeta (s + 1))) =
      (sin (π * s) * (-Gamma (-s) * (s * Gamma s))) / π * riemannZeta (s + 1) by ring, key2,
      div_self hπ, one_mul]

/-- DLMF 25.5.18: for `0 < Re s < 1`, `ζ(1+s) = (sin(πs)/(πs)) ∫₀^∞ ψ'(1+x) x^{-s} dx`. -/
@[dlmf 25.5.E18]
theorem riemannZeta_one_add_eq_integral_trigamma {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    IntegrableOn (fun x : ℝ => DLMF.Gamma.polygamma 1 (1 + x) * (x : ℂ) ^ (-s)) (Ioi 0) ∧
      riemannZeta (1 + s) = sin (π * s) / (π * s) * ∫ x in Ioi (0 : ℝ),
        DLMF.Gamma.polygamma 1 (1 + x) * (x : ℂ) ^ (-s) := by
  obtain ⟨hI, hv⟩ := r25a_zeta_nat_add_eq_integral (m := 1) le_rfl hs hs'
  refine ⟨hI, ?_⟩
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hG : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos hs
  rw [Nat.cast_one] at hv
  rw [hv, add_comm (1 : ℂ) s, Complex.Gamma_add_one s hs0]
  simp only [Nat.sub_self, pow_zero, one_mul]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- DLMF 25.5.19: for `m ≥ 1` and `0 < Re s < 1`,
`ζ(m+s) = (-1)^{m-1} (Γ(s) sin(πs)/(π Γ(m+s))) ∫₀^∞ ψ^{(m)}(1+x) x^{-s} dx`. -/
@[dlmf 25.5.E19]
theorem riemannZeta_nat_add_eq_integral_polygamma {s : ℂ} {m : ℕ} (hm : 1 ≤ m)
    (hs : 0 < s.re) (hs' : s.re < 1) :
    IntegrableOn (fun x : ℝ => DLMF.Gamma.polygamma m (1 + x) * (x : ℂ) ^ (-s)) (Ioi 0) ∧
      riemannZeta (m + s) = (-1) ^ (m - 1) * (Gamma s * sin (π * s) / (π * Gamma (m + s))) *
        ∫ x in Ioi (0 : ℝ), DLMF.Gamma.polygamma m (1 + x) * (x : ℂ) ^ (-s) :=
  r25a_zeta_nat_add_eq_integral hm hs hs'

/-! ### §25.5(iii) Contour integrals -/

/-- The keyhole loop integral `∫_{-∞}^{(0+)} z^a g(z) dz` around the negative real axis: from
`-∞` along the lower edge of the cut (`arg z = -π`) to `-δ`, once around the circle `|z| = δ`
in the positive direction, and back along the upper edge (`arg z = π`) to `-∞`. The power `z^a`
takes the boundary values `x^a e^{∓iπa}` on the two edges and its principal value
`δ^a e^{iaθ}`, `-π < θ < π`, on the circle. Parametrized,
`(e^{-iπa} - e^{iπa}) ∫_δ^∞ x^a g(-x) dx + ∫_{-π}^{π} δ^a e^{iaθ} g(δe^{iθ}) iδe^{iθ} dθ`
(DLMF §25.5(iii), the contour of 25.5.20–25.5.21). -/
@[dlmf 25.5.iii]
def keyholeLoopIntegral (g : ℂ → ℂ) (a : ℂ) (δ : ℝ) : ℂ :=
  (cexp (-(π * I * a)) - cexp (π * I * a)) * (∫ x in Ioi δ, (x : ℂ) ^ a * g (-x)) +
    ∫ θ in (-π)..π, (δ : ℂ) ^ a * cexp (I * a * θ) * g (δ * cexp (I * θ)) *
      (I * δ * cexp (I * θ))

/-- DLMF 25.5.20: for `s ∉ {1, 2, 3, …}`,
`ζ(s) = (Γ(1-s)/(2πi)) ∫_{-∞}^{(0+)} z^{s-1}/(e^{-z} - 1) dz`, the loop encircling the origin
once positively without enclosing `±2πi, ±4πi, …`; here over the keyhole of radius
`0 < δ < 2π`. -/
@[dlmf 25.5.E20]
theorem riemannZeta_eq_loop_integral {s : ℂ} (hs : ∀ n : ℕ, s ≠ n + 1) {δ : ℝ} (hδ : 0 < δ)
    (hδ' : δ < 2 * π) :
    riemannZeta s = Gamma (1 - s) / (2 * π * I) *
      keyholeLoopIntegral (fun z => 1 / (cexp (-z) - 1)) (s - 1) δ := by
  sorry

/-- DLMF 25.5.21 (multiplied form): for `s ∉ {1, 2, 3, …}`,
`(1 - 2^{1-s}) ζ(s) = (Γ(1-s)/(2πi)) ∫_{-∞}^{(0+)} z^{s-1}/(e^{-z} + 1) dz`, the loop not
enclosing `±πi, ±3πi, …`; here over the keyhole of radius `0 < δ < π`. -/
@[dlmf 25.5.E21]
theorem riemannZeta_eq_loop_integral_add {s : ℂ} (hs : ∀ n : ℕ, s ≠ n + 1) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < π) :
    (1 - 2 ^ (1 - s)) * riemannZeta s = Gamma (1 - s) / (2 * π * I) *
      keyholeLoopIntegral (fun z => 1 / (cexp (-z) + 1)) (s - 1) δ := by
  sorry

end DLMF.Zeta
