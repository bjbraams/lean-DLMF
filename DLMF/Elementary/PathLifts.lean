/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ComplexDeriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Path lifts for the inverse sine and tangent

This file supplies the analytic core of the path-integral characterizations of the general
inverse trigonometric and hyperbolic functions (DLMF 4.23.1–4.23.3 and 4.37.1–4.37.3).

## Main definitions

* `pathDetour`: a parabolic path from `0` to `w` that avoids the real axis at interior times.

## Main results

* `sin_of_arcsin_lift`, `tan_of_arctan_lift`: path integrals of `γ' / √(1 - γ²)` and
  `γ' / (1 + γ²)` with a continued branch are arcsines and arctangents of the endpoint.
* `arcsin_lift_exists`, `arctan_lift_exists`: every arcsine (arctangent) arises in this way,
  along the image of `pathDetour` under `sin` (`tan`).

## Implementation notes

Soundness is proved by showing that `(r + iγ) e^{-iW}` and `(1 + iγ)/(1 - iγ) e^{-2iW}` are
constant along the path, where `W` is the running integral. Existence uses that the zeros of
the complex cosine are real, so the detour keeps `cos` away from zero.
-/

@[expose] public noncomputable section

open Complex Set MeasureTheory Filter Topology

namespace DLMF.Elementary

private lemma hasDerivAt_of_contDiffOn_Icc {γ : ℝ → ℂ} (hγ : ContDiffOn ℝ 1 γ (Icc 0 1)) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) : HasDerivAt γ (deriv γ s) s :=
  ((hγ.differentiableOn one_ne_zero s (Ioo_subset_Icc_self hs)).differentiableAt
    (Icc_mem_nhds hs.1 hs.2)).hasDerivAt

private lemma deriv_eqOn_derivWithin (γ : ℝ → ℂ) :
    EqOn (deriv γ) (derivWithin γ (Icc 0 1)) (Ioo 0 1) := fun _ hs =>
  (derivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)).symm

private lemma continuousOn_derivWithin_Icc {γ : ℝ → ℂ} (hγ : ContDiffOn ℝ 1 γ (Icc 0 1)) :
    ContinuousOn (derivWithin γ (Icc 0 1)) (Icc 0 1) :=
  hγ.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl

private lemma primitive_props {f F : ℝ → ℂ} (hF : ContinuousOn F (Icc 0 1))
    (hfF : EqOn f F (Ioo 0 1)) :
    IntervalIntegrable f volume 0 1 ∧ ContinuousOn (fun s => ∫ t in (0 : ℝ)..s, f t) (Icc 0 1) ∧
      ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun s => ∫ t in (0 : ℝ)..s, f t) (f s) s := by
  have hFi : IntervalIntegrable F volume 0 1 := hF.intervalIntegrable_of_Icc zero_le_one
  have heq : ∀ s ∈ Icc (0 : ℝ) 1, (∫ t in (0 : ℝ)..s, f t) = ∫ t in (0 : ℝ)..s, F t := by
    intro s hs
    refine intervalIntegral.integral_congr_uIoo fun x hx => ?_
    rw [uIoo_of_le hs.1] at hx
    exact hfF ⟨hx.1, hx.2.trans_le hs.2⟩
  have hfi : IntervalIntegrable f volume 0 1 := by
    refine hFi.congr_uIoo fun x hx => ?_
    rw [uIoo_of_le zero_le_one] at hx
    exact (hfF hx).symm
  refine ⟨hfi, ?_, ?_⟩
  · have hc : ContinuousOn (fun s => ∫ t in (0 : ℝ)..s, F t) (Icc 0 1) := by
      have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := 1)
        (f := F) (by rw [uIcc_of_le zero_le_one]; exact hF.integrableOn_Icc)
      simpa [uIcc_of_le zero_le_one] using this
    exact hc.congr fun s hs => heq s hs
  · intro s hs
    have hd : HasDerivAt (fun s => ∫ t in (0 : ℝ)..s, F t) (F s) s := by
      refine intervalIntegral.integral_hasDerivAt_right (hFi.mono_set ?_) ?_ ?_
      · rw [uIcc_of_le hs.1.le, uIcc_of_le zero_le_one]
        exact Icc_subset_Icc le_rfl hs.2.le
      · exact (hF.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo s hs
      · exact hF.continuousAt (Icc_mem_nhds hs.1 hs.2)
    rw [hfF hs]
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Icc_mem_nhds hs.1 hs.2] with x hx using heq x hx

private lemma eq_of_hasDerivAt_zero {F : ℝ → ℂ} (hc : ContinuousOn F (Icc 0 1))
    (hd : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt F 0 s) : F 1 = F 0 := by
  have h1 : ∀ t ∈ Ioo (0 : ℝ) 1, F 1 = F t := by
    intro t ht
    have := constant_of_has_deriv_right_zero (hc.mono (Icc_subset_Icc ht.1.le le_rfl))
      (fun x hx => (hd x ⟨ht.1.trans_le hx.1, hx.2⟩).hasDerivWithinAt) 1 ⟨ht.2.le, le_rfl⟩
    exact this
  have hlim : Tendsto F (𝓝[>] 0) (𝓝 (F 0)) := by
    have := (hc 0 ⟨le_rfl, zero_le_one⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGT zero_lt_one)
    exact this.tendsto
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hlim
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht using h1 t ht

private lemma hasDerivAt_of_sq_eq {γ r : ℝ → ℂ} {s : ℝ} {c σ γ' : ℂ}
    (h : ∀ᶠ x in 𝓝 s, r x ^ 2 = c + σ * γ x ^ 2) (hr : ContinuousAt r s) (hr0 : r s ≠ 0)
    (hγ : HasDerivAt γ γ' s) : HasDerivAt r (σ * γ s * γ' / r s) s := by
  rw [hasDerivAt_iff_tendsto_slope] at hγ ⊢
  have hγc := (hasDerivAt_iff_tendsto_slope.mpr hγ).continuousAt
  have hsum : Tendsto (fun x => σ * (γ x + γ s) / (r x + r s)) (𝓝[≠] s)
      (𝓝 (σ * (γ s + γ s) / (r s + r s))) := by
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    refine ((tendsto_const_nhds.mul (hγc.tendsto.add tendsto_const_nhds)).div
      (hr.tendsto.add tendsto_const_nhds) ?_)
    rw [← two_mul]; exact mul_ne_zero two_ne_zero hr0
  have hne : ∀ᶠ x in 𝓝 s, r x + r s ≠ 0 := by
    have : Tendsto (fun x => r x + r s) (𝓝 s) (𝓝 (r s + r s)) := hr.tendsto.add tendsto_const_nhds
    exact this.eventually_ne (by rw [← two_mul]; exact mul_ne_zero two_ne_zero hr0)
  have key := hsum.mul hγ
  have hlim : σ * (γ s + γ s) / (r s + r s) * γ' = σ * γ s * γ' / r s := by
    rw [← two_mul, ← two_mul]; field_simp
  rw [hlim] at key
  refine key.congr' ?_
  filter_upwards [nhdsWithin_le_nhds h, nhdsWithin_le_nhds hne, self_mem_nhdsWithin]
    with x hx hx2 hxs
  have hs := h.self_of_nhds
  have hxs' : x - s ≠ 0 := sub_ne_zero.mpr hxs
  have hxs'' : ((x - s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hxs'
  simp only [slope_def_module, Complex.real_smul]
  push_cast at hxs'' ⊢
  field_simp
  linear_combination -(hx - hs)


/-- The parabolic detour `s ↦ s w + i c s (1 - s)` from `0` to `w`; for `c ≠ 0` it leaves the
real line at interior times whenever `w` is real. -/
def pathDetour (w : ℂ) (c : ℝ) (s : ℝ) : ℂ :=
  (s : ℂ) * w + ((c * (s * (1 - s)) : ℝ) : ℂ) * I

/-- The derivative of `pathDetour`. -/
theorem hasDerivAt_pathDetour (w : ℂ) (c s : ℝ) :
    HasDerivAt (pathDetour w c) (w + ((c * (1 - 2 * s) : ℝ) : ℂ) * I) s := by
  have h1 := ((hasDerivAt_id (s : ℝ)).ofReal_comp).mul_const w
  have hp : HasDerivAt (fun x : ℝ => c * (x * (1 - x))) (c * (1 - 2 * s)) s := by
    have := ((hasDerivAt_id' s).mul ((hasDerivAt_const s (1 : ℝ)).sub
      (hasDerivAt_id' s))).const_mul c
    convert this using 1
    simp only [Pi.sub_apply]; ring
  have h2 := (hp.ofReal_comp).mul_const I
  convert h1.add h2 using 1
  · ext x; simp [pathDetour]
  · simp

/-- `pathDetour` is smooth. -/
theorem contDiff_pathDetour (w : ℂ) (c : ℝ) : ContDiff ℝ ⊤ (pathDetour w c) := by
  unfold pathDetour
  have hp : ContDiff ℝ ⊤ (fun x : ℝ => c * (x * (1 - x))) := by fun_prop
  exact (ofRealCLM.contDiff.mul contDiff_const).add
    ((ofRealCLM.contDiff.comp hp).mul contDiff_const)

/-- `pathDetour` starts at the origin. -/
@[simp] theorem pathDetour_zero (w : ℂ) (c : ℝ) : pathDetour w c 0 = 0 := by simp [pathDetour]
/-- `pathDetour` ends at `w`. -/
@[simp] theorem pathDetour_one (w : ℂ) (c : ℝ) : pathDetour w c 1 = w := by simp [pathDetour]

/-- The integral of the velocity of `pathDetour` is its endpoint. -/
theorem integral_deriv_pathDetour (w : ℂ) (c : ℝ) :
    ∫ s in (0 : ℝ)..1, (w + ((c * (1 - 2 * s) : ℝ) : ℂ) * I) = w := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_pathDetour w c x)
    (by apply Continuous.intervalIntegrable; fun_prop), pathDetour_one, pathDetour_zero, sub_zero]

/-- With the sign of `w.im`, the detour has nonzero imaginary part at interior times. -/
private lemma pathDetour_im_ne_zero (w : ℂ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    (pathDetour w (if 0 ≤ w.im then 1 else -1) s).im ≠ 0 := by
  simp only [pathDetour, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]
  obtain ⟨h0, h1⟩ := hs
  split_ifs with h
  · have : 0 < s * (1 - s) := mul_pos h0 (by linarith)
    nlinarith
  · have : 0 < s * (1 - s) := mul_pos h0 (by linarith)
    push Not at h
    nlinarith


/-- Integrability and the primitive of `deriv γ * g` for a `C¹` path and continuous `g`. -/
private lemma primitive_deriv_mul {γ g : ℝ → ℂ} (hγ : ContDiffOn ℝ 1 γ (Icc 0 1))
    (hg : ContinuousOn g (Icc 0 1)) :
    IntervalIntegrable (fun t => deriv γ t * g t) volume 0 1 ∧
      ContinuousOn (fun s => ∫ t in (0 : ℝ)..s, deriv γ t * g t) (Icc 0 1) ∧
      ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun s => ∫ t in (0 : ℝ)..s, deriv γ t * g t)
        (deriv γ s * g s) s :=
  primitive_props ((continuousOn_derivWithin_Icc hγ).mul hg) fun _ hs => by
    simp only [deriv_eqOn_derivWithin γ hs, Pi.mul_apply]

/-- Soundness of the arcsine path integral: if `r` is a continuous nonvanishing square root of
`1 - γ²` along a `C¹` path `γ` from `0` to `z` with `r 0 = 1`, then the integral of `γ' / r`
is an arcsine of `z`. -/
theorem sin_of_arcsin_lift {γ r : ℝ → ℂ} {z : ℂ} (hγ : ContDiffOn ℝ 1 γ (Icc 0 1))
    (h0 : γ 0 = 0) (h1 : γ 1 = z) (hr : ContinuousOn r (Icc 0 1)) (hr0 : r 0 = 1)
    (hrr : ∀ t ∈ Icc (0 : ℝ) 1, r t ≠ 0 ∧ r t ^ 2 = 1 - γ t ^ 2) :
    IntervalIntegrable (fun t => deriv γ t / r t) volume 0 1 ∧
      Complex.sin (∫ t in (0 : ℝ)..1, deriv γ t / r t) = z := by
  have hinv : ContinuousOn (fun t => (r t)⁻¹) (Icc 0 1) :=
    hr.inv₀ fun t ht => (hrr t ht).1
  obtain ⟨hi, hc, hd⟩ := primitive_deriv_mul hγ hinv
  simp only [← div_eq_mul_inv] at hi hc hd
  refine ⟨hi, ?_⟩
  set W := fun s => ∫ t in (0 : ℝ)..s, deriv γ t / r t with hW
  let H := fun s => (r s + I * γ s) * exp (-I * W s)
  have hHc : ContinuousOn H (Icc 0 1) :=
    (hr.add (continuousOn_const.mul hγ.continuousOn)).mul
      ((continuousOn_const.mul hc).cexp)
  have hHd : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt H 0 s := by
    intro s hs
    have hsI : s ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hs
    have hγd := hasDerivAt_of_contDiffOn_Icc hγ hs
    have hrd := hasDerivAt_of_sq_eq (c := 1) (σ := -1) (γ' := deriv γ s)
      (by filter_upwards [Icc_mem_nhds hs.1 hs.2] with x hx
          rw [(hrr x hx).2]; ring)
      (hr.continuousAt (Icc_mem_nhds hs.1 hs.2)) (hrr s hsI).1 hγd
    have hWd := hd s hs
    have := (hrd.add (hγd.const_mul I)).mul ((hWd.const_mul (-I)).cexp)
    convert this using 1
    have := (hrr s hsI).1
    simp only [Pi.add_apply]
    field_simp
    linear_combination (deriv γ s * cexp (-(I * W s)) * γ s) * I_sq
  have hH := eq_of_hasDerivAt_zero hHc hHd
  simp only [H, hW, h0, h1, hr0, intervalIntegral.integral_same, mul_zero, add_zero,
    Complex.exp_zero, mul_one] at hH
  set w := ∫ t in (0 : ℝ)..1, deriv γ t / r t
  have hp : r 1 + I * z = exp (I * w) := by
    have := congrArg (· * exp (I * w)) hH
    simp only [mul_assoc, ← Complex.exp_add, neg_mul, neg_add_cancel, Complex.exp_zero,
      mul_one, one_mul] at this
    exact this
  have hsq : (r 1 - I * z) * (r 1 + I * z) = 1 := by
    have := (hrr 1 ⟨zero_le_one, le_rfl⟩).2
    rw [h1] at this
    linear_combination this - z ^ 2 * I_sq
  have hm : r 1 - I * z = exp (-(w * I)) := by
    have he : exp (I * w) * exp (-(w * I)) = 1 := by
      rw [← Complex.exp_add]; ring_nf; simp
    rw [hp] at hsq
    have hne : exp (I * w) ≠ 0 := Complex.exp_ne_zero _
    calc r 1 - I * z = (r 1 - I * z) * (exp (I * w) * exp (-(w * I))) := by rw [he, mul_one]
      _ = exp (-(w * I)) := by rw [← mul_assoc, hsq, one_mul]
  rw [Complex.sin, neg_mul, ← hm, mul_comm w I, ← hp]
  ring_nf
  rw [I_sq]; ring


/-- The sign of the detour bulge, chosen to agree with the sign of `w.im`. -/
def pathDetourSign (w : ℂ) : ℝ := if 0 ≤ w.im then 1 else -1

/-- If `cos w ≠ 0`, the cosine does not vanish along the detour from `0` to `w`. -/
theorem cos_pathDetour_ne_zero {w : ℂ} (hw : Complex.cos w ≠ 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Complex.cos (pathDetour w (pathDetourSign w) t) ≠ 0 := by
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst h; simp [pathDetour_zero]
  rcases eq_or_lt_of_le ht.2 with h' | h'
  · subst h'; simpa [pathDetour_one] using hw
  intro hc
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hc
  apply pathDetour_im_ne_zero w ⟨h, h'⟩
  rw [show (if 0 ≤ w.im then (1 : ℝ) else -1) = pathDetourSign w from rfl, hk]
  norm_cast

/-- Every arcsine `w` of `z ≠ ±1` is the arcsine path integral along `sin ∘ pathDetour`, with
square root `cos ∘ pathDetour`. -/
theorem arcsin_lift_exists {z w : ℂ} (hzp : z ≠ 1) (hzm : z ≠ -1) (hw : Complex.sin w = z) :
    ContDiffOn ℝ 1 (fun t => Complex.sin (pathDetour w (pathDetourSign w) t)) (Icc 0 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Complex.cos (pathDetour w (pathDetourSign w) t) ≠ 0) ∧
      (∫ t in (0 : ℝ)..1, deriv (fun t => Complex.sin (pathDetour w (pathDetourSign w) t)) t /
        Complex.cos (pathDetour w (pathDetourSign w) t)) = w := by
  have hcw : Complex.cos w ≠ 0 := by
    intro h
    have := Complex.sin_sq_add_cos_sq w
    rw [h, hw] at this
    have : (z - 1) * (z + 1) = 0 := by linear_combination this
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hzp (sub_eq_zero.mp h1)
    · exact hzm (eq_neg_of_add_eq_zero_left h1)
  have hc := fun t (ht : t ∈ Icc (0 : ℝ) 1) => cos_pathDetour_ne_zero hcw ht
  refine ⟨((Complex.contDiff_sin.restrict_scalars ℝ).comp
    (contDiff_pathDetour _ _)).contDiffOn.of_le
    le_top, hc, ?_⟩
  refine (intervalIntegral.integral_congr
    (g := fun t => w + ((pathDetourSign w * (1 - 2 * t) : ℝ) : ℂ) * I)
    fun t ht => ?_).trans (integral_deriv_pathDetour w _)
  rw [uIcc_of_le zero_le_one] at ht
  have hd : HasDerivAt (fun t => Complex.sin (pathDetour w (pathDetourSign w) t)) _ t :=
    (Complex.hasDerivAt_sin _).comp t (hasDerivAt_pathDetour w _ t)
  rw [hd.deriv]
  field_simp [hc t ht]

/-- Every arctangent `w` (with `cos w ≠ 0`) is the arctangent path integral along
`tan ∘ pathDetour`. -/
theorem arctan_lift_exists {w : ℂ} (hw : Complex.cos w ≠ 0) :
    ContDiffOn ℝ 1 (fun t => Complex.tan (pathDetour w (pathDetourSign w) t)) (Icc 0 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Complex.tan (pathDetour w (pathDetourSign w) t) ≠ I ∧
        Complex.tan (pathDetour w (pathDetourSign w) t) ≠ -I) ∧
      (∫ t in (0 : ℝ)..1, deriv (fun t => Complex.tan (pathDetour w (pathDetourSign w) t)) t /
        (1 + Complex.tan (pathDetour w (pathDetourSign w) t) ^ 2)) = w := by
  have hc := fun t (ht : t ∈ Icc (0 : ℝ) 1) => cos_pathDetour_ne_zero hw ht
  have hsq : ∀ x : ℂ, Complex.cos x ≠ 0 → 1 + Complex.tan x ^ 2 = 1 / Complex.cos x ^ 2 := by
    intro x hx
    rw [Complex.tan_eq_sin_div_cos]
    field_simp
    linear_combination Complex.sin_sq_add_cos_sq x
  refine ⟨fun t ht => ?_, fun t ht => ?_, ?_⟩
  · exact (((Complex.contDiffAt_tan.mpr (hc t ht)).restrict_scalars ℝ).comp t
      ((contDiff_pathDetour _ _).contDiffAt.of_le le_top)).contDiffWithinAt
  · have h2 := hsq _ (hc t ht)
    constructor <;> intro h <;> rw [h] at h2 <;> simp at h2 <;>
      exact hc t ht ((pow_eq_zero_iff two_ne_zero).mp h2.symm)
  refine (intervalIntegral.integral_congr
    (g := fun t => w + ((pathDetourSign w * (1 - 2 * t) : ℝ) : ℂ) * I)
    fun t ht => ?_).trans (integral_deriv_pathDetour w _)
  rw [uIcc_of_le zero_le_one] at ht
  have hd : HasDerivAt (fun t => Complex.tan (pathDetour w (pathDetourSign w) t)) _ t :=
    (Complex.hasDerivAt_tan (hc t ht)).comp t (hasDerivAt_pathDetour w _ t)
  rw [hd.deriv,
    hsq _ (hc t ht)]
  field_simp [hc t ht]

/-- Soundness of the arctangent path integral along a `C¹` path from `0` to `z` avoiding `±i`. -/
theorem tan_of_arctan_lift {γ : ℝ → ℂ} {z : ℂ} (hγ : ContDiffOn ℝ 1 γ (Icc 0 1))
    (h0 : γ 0 = 0) (h1 : γ 1 = z) (hI : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ I ∧ γ t ≠ -I) :
    IntervalIntegrable (fun t => deriv γ t / (1 + γ t ^ 2)) volume 0 1 ∧
      Complex.cos (∫ t in (0 : ℝ)..1, deriv γ t / (1 + γ t ^ 2)) ≠ 0 ∧
      Complex.tan (∫ t in (0 : ℝ)..1, deriv γ t / (1 + γ t ^ 2)) = z := by
  have hm : ∀ t ∈ Icc (0 : ℝ) 1, 1 - I * γ t ≠ 0 := by
    intro t ht h
    apply (hI t ht).2
    linear_combination I * h + γ t * I_sq
  have hp : ∀ t ∈ Icc (0 : ℝ) 1, 1 + I * γ t ≠ 0 := by
    intro t ht h
    apply (hI t ht).1
    linear_combination (-I) * h + γ t * I_sq
  have hq : ∀ t ∈ Icc (0 : ℝ) 1, 1 + γ t ^ 2 ≠ 0 := by
    intro t ht h
    have : (1 + I * γ t) * (1 - I * γ t) = 0 := by linear_combination h - γ t ^ 2 * I_sq
    rcases mul_eq_zero.mp this with h' | h'
    · exact hp t ht h'
    · exact hm t ht h'
  have hinv : ContinuousOn (fun t => (1 + γ t ^ 2)⁻¹) (Icc 0 1) :=
    (continuousOn_const.add (hγ.continuousOn.pow 2)).inv₀ hq
  obtain ⟨hi, hc, hd⟩ := primitive_deriv_mul hγ hinv
  simp only [← div_eq_mul_inv] at hi hc hd
  set W := fun s => ∫ t in (0 : ℝ)..s, deriv γ t / (1 + γ t ^ 2) with hW
  let H := fun s => (1 + I * γ s) / (1 - I * γ s) * exp (-2 * I * W s)
  have hHc : ContinuousOn H (Icc 0 1) :=
    ((continuousOn_const.add (continuousOn_const.mul hγ.continuousOn)).div
      (continuousOn_const.sub (continuousOn_const.mul hγ.continuousOn)) hm).mul
      ((continuousOn_const.mul hc).cexp)
  have hHd : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt H 0 s := by
    intro s hs
    have hsI : s ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hs
    have hγd := hasDerivAt_of_contDiffOn_Icc hγ hs
    have := ((((hγd.const_mul I).const_add 1).div ((hγd.const_mul I).const_sub 1)
      (hm s hsI)).mul (((hd s hs).const_mul (-2 * I)).cexp))
    convert this using 1
    have h1 := hm s hsI
    have h2 := hp s hsI
    have h3 := hq s hsI
    simp only [Pi.div_apply]
    field_simp
    ring_nf
    simp only [I_pow_three]
    ring_nf
  have hH := eq_of_hasDerivAt_zero hHc hHd
  simp only [H, hW, h0, h1, intervalIntegral.integral_same, mul_zero, add_zero, sub_zero,
    div_one, Complex.exp_zero, mul_one] at hH
  refine ⟨hi, ?_⟩
  set w := ∫ t in (0 : ℝ)..1, deriv γ t / (1 + γ t ^ 2)
  have hm1 := hm 1 ⟨zero_le_one, le_rfl⟩
  rw [h1] at hm1
  set e := exp (w * I)
  set f := exp (-w * I)
  have hef : e * f = 1 := by rw [← Complex.exp_add]; ring_nf; simp
  have he : e ≠ 0 := Complex.exp_ne_zero _
  have h2 : exp (-2 * I * w) = f * f := by rw [← Complex.exp_add]; ring_nf
  rw [h2] at hH
  have hk : (1 + I * z) * f = (1 - I * z) * e := by
    field_simp at hH
    linear_combination e * hH - (1 + I * z) * f * hef
  have hcos : Complex.cos w = (e + f) / 2 := by
    rw [Complex.cos]
  have hsin : Complex.sin w = (f - e) * I / 2 := by
    rw [Complex.sin]
  have hc0 : Complex.cos w ≠ 0 := by
    rw [hcos]
    intro h
    have hf : f = -e := by linear_combination 2 * h
    rw [hf] at hk
    exact he (by linear_combination -hk / 2)
  refine ⟨hc0, ?_⟩
  rw [Complex.tan_eq_sin_div_cos, div_eq_iff hc0, hsin, hcos]
  linear_combination (I / 2) * hk - (z * (e + f) / 2) * I_sq


end DLMF.Elementary
