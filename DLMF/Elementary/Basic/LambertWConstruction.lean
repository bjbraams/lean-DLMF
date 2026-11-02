/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Construction of the Lambert W branches

This file constructs the integer branches of the Lambert W function. The map
`w ↦ w + log w` is a biholomorphism from the slit plane onto the plane with the two half-lines
`Im ζ = ±π`, `Re ζ ≤ -1` removed; its inverse (Wright's omega function off its cuts) gives
`W_k(z) = ω(log z + 2πik)` on the slit plane. On the negative real axis the values are the
upper-side limits; on `[-1/e, 0)` for `k ∈ {0, -1}` these are the real inverses of `y e^y`.

Injectivity and surjectivity are proved through the level-curve profile
`F_b(θ) = (b - θ) cot θ + log ((b - θ)/sin θ)` of `Im (w + log w) = b` with `θ = arg w`, which
is strictly decreasing. Continuity at the branch point and on the cuts follows from a
compactness argument with a unique solution over the limit point.

## Main definitions

* `lambertLogMap`: the map `w ↦ w + log w`.
* `lambertOmegaDomain`, `lambertLogMapInv`: its image domain and inverse.
* `lambertRealUpper`, `lambertRealLower`: the real inverses of `y e^y`.
* `lambertBranchValue`: the upper-side branch values `W_k(z)`.

## Main results

* `lambertLogMap_injOn`, `exists_lambertLogMap_eq`: bijectivity of `w + log w`.
* `differentiableAt_lambertLogMapInv`: holomorphy of the inverse.
* `lambertBranchValue_mul_exp`: the inverse equation `W e^W = z`.
* `differentiableAt_lambertBranchValue_of_mem_slitPlane`,
  `differentiableAt_lambertBranchValue_zero`: holomorphy of the branches.
* `tendsto_lambertBranchValue_upper`: upper-side continuity on the negative axis.
* `lambertBranchValue_one`: the basepoint values `W_k(1)`.
-/

@[expose] public section

open Complex Filter Set

open scoped Topology Real ComplexConjugate

noncomputable section

namespace DLMF.Elementary

/-- The map `w ↦ w + log w`, the logarithm of `w e^w` on the slit plane. -/
def lambertLogMap (w : ℂ) : ℂ := w + Complex.log w

/-- The real profile `F_b(θ)` of the level curve `Im (w + log w) = b`, with `θ = arg w`. -/
def lambertLevelProfile (b θ : ℝ) : ℝ :=
  (b - θ) * Real.cos θ / Real.sin θ + Real.log ((b - θ) / Real.sin θ)

/-- The real part of `w + log w`. -/
lemma lambertLogMap_re (w : ℂ) : (lambertLogMap w).re = w.re + Real.log ‖w‖ := by
  simp [lambertLogMap, Complex.log_re]

/-- The imaginary part of `w + log w`. -/
lemma lambertLogMap_im (w : ℂ) : (lambertLogMap w).im = w.im + arg w := by
  simp [lambertLogMap, Complex.log_im]

/-- Parametrization of the upper half-plane by `θ = arg w` and `b = Im (w + log w)`. -/
lemma lambertLogMap_param {w : ℂ} (hw : 0 < w.im) :
    0 < arg w ∧ arg w < π ∧ arg w < (lambertLogMap w).im ∧
      ‖w‖ = ((lambertLogMap w).im - arg w) / Real.sin (arg w) ∧
      (lambertLogMap w).re = lambertLevelProfile (lambertLogMap w).im (arg w) := by
  have h0 : 0 < arg w := lt_of_le_of_ne (arg_nonneg_iff.mpr hw.le) (by
    intro h; have := arg_eq_zero_iff.mp h.symm; linarith [this.2])
  have hpi : arg w < π := arg_lt_pi_iff.mpr (Or.inr hw.ne')
  have hs : 0 < Real.sin (arg w) := Real.sin_pos_of_pos_of_lt_pi h0 hpi
  have him := norm_mul_sin_arg w
  have hre := norm_mul_cos_arg w
  have hb : (lambertLogMap w).im - arg w = w.im := by rw [lambertLogMap_im]; ring
  have hn : ‖w‖ = w.im / Real.sin (arg w) := by field_simp; linarith
  refine ⟨h0, hpi, by linarith, by rw [hb]; exact hn, ?_⟩
  rw [lambertLogMap_re, lambertLevelProfile, hb, ← hn, ← hre, ← him]
  field_simp

/-- The derivative of the level profile, `-((u + cos θ sin θ)² + sin⁴ θ)/(u sin² θ)`. -/
lemma hasDerivAt_lambertLevelProfile {b θ : ℝ} (hu : 0 < b - θ) (hs : Real.sin θ ≠ 0) :
    HasDerivAt (lambertLevelProfile b)
      (-(((b - θ) + Real.cos θ * Real.sin θ) ^ 2 + Real.sin θ ^ 4) /
        ((b - θ) * Real.sin θ ^ 2)) θ := by
  have h1 : HasDerivAt (fun θ => (b - θ) * Real.cos θ / Real.sin θ)
      ((((-1) * Real.cos θ + (b - θ) * -Real.sin θ) * Real.sin θ -
        (b - θ) * Real.cos θ * Real.cos θ) / Real.sin θ ^ 2) θ :=
    ((((hasDerivAt_id θ).const_sub b).congr_deriv (by simp)).mul
      (Real.hasDerivAt_cos θ)).div (Real.hasDerivAt_sin θ) hs
  have h2 : HasDerivAt (fun θ => (b - θ) / Real.sin θ)
      (((-1) * Real.sin θ - (b - θ) * Real.cos θ) / Real.sin θ ^ 2) θ :=
    (((hasDerivAt_id θ).const_sub b).congr_deriv (by simp)).div (Real.hasDerivAt_sin θ) hs
  have hne : (b - θ) / Real.sin θ ≠ 0 := div_ne_zero hu.ne' hs
  refine (h1.add (h2.log hne)).congr_deriv ?_
  have hc := Real.sin_sq_add_cos_sq θ
  field_simp
  linear_combination (2 * b * θ - b ^ 2 - θ ^ 2 + Real.sin θ ^ 2) * hc

/-- The level profile is strictly decreasing on `(0, min b π)`. -/
lemma strictAntiOn_lambertLevelProfile (b : ℝ) :
    StrictAntiOn (lambertLevelProfile b) (Ioo 0 (min b π)) := by
  have hprop : ∀ θ ∈ Ioo 0 (min b π), 0 < b - θ ∧ 0 < Real.sin θ := fun θ hθ =>
    ⟨by linarith [hθ.2, min_le_left b π],
      Real.sin_pos_of_pos_of_lt_pi hθ.1 (lt_of_lt_of_le hθ.2 (min_le_right _ _))⟩
  apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
  · intro θ hθ
    obtain ⟨hu, hs⟩ := hprop θ hθ
    exact (hasDerivAt_lambertLevelProfile hu hs.ne').continuousAt.continuousWithinAt
  · intro θ hθ
    rw [interior_Ioo] at hθ
    obtain ⟨hu, hs⟩ := hprop θ hθ
    rw [(hasDerivAt_lambertLevelProfile hu hs.ne').deriv]
    apply div_neg_of_neg_of_pos
    · have : 0 < Real.sin θ ^ 4 := by positivity
      nlinarith [sq_nonneg ((b - θ) + Real.cos θ * Real.sin θ)]
    · positivity


/-- Points of the slit plane do not have argument `π`. -/
private lemma arg_ne_pi_of_mem_slitPlane {w : ℂ} (hw : w ∈ slitPlane) : arg w ≠ π := by
  intro h
  rcases arg_eq_pi_iff.mp h with ⟨h1, h2⟩
  rcases mem_slitPlane_iff.mp hw with h | h
  · linarith
  · exact h h2

/-- Conjugation symmetry of `w + log w` on the slit plane. -/
lemma lambertLogMap_conj {w : ℂ} (hw : w ∈ slitPlane) :
    lambertLogMap (conj w) = conj (lambertLogMap w) := by
  simp [lambertLogMap, Complex.log_conj w (arg_ne_pi_of_mem_slitPlane hw)]

private lemma conj_mem_slitPlane {w : ℂ} (hw : w ∈ slitPlane) : conj w ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hw ⊢
  simpa using hw

/-- The sign of `Im (w + log w)` is the sign of `Im w` on the slit plane. -/
lemma lambertLogMap_im_sign {w : ℂ} (hw : w ∈ slitPlane) :
    (0 < w.im → 0 < (lambertLogMap w).im) ∧ (w.im < 0 → (lambertLogMap w).im < 0) ∧
      (w.im = 0 → (lambertLogMap w).im = 0 ∧ 0 < w.re) := by
  rw [lambertLogMap_im]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · linarith [arg_nonneg_iff.mpr h.le]
  · linarith [arg_neg_iff.mpr h]
  · have hre : 0 < w.re := by
      rcases mem_slitPlane_iff.mp hw with h' | h'
      · exact h'
      · exact absurd h h'
    rw [h, arg_eq_zero_iff.mpr ⟨hre.le, h⟩]
    exact ⟨by simp, hre⟩

/-- Injectivity of `w + log w` on the upper half-plane. -/
lemma lambertLogMap_injOn_upper {w₁ w₂ : ℂ} (h₁ : 0 < w₁.im) (h₂ : 0 < w₂.im)
    (h : lambertLogMap w₁ = lambertLogMap w₂) : w₁ = w₂ := by
  obtain ⟨a1, b1, c1, n1, f1⟩ := lambertLogMap_param h₁
  obtain ⟨a2, b2, c2, n2, f2⟩ := lambertLogMap_param h₂
  set b := (lambertLogMap w₁).im
  have hb : (lambertLogMap w₂).im = b := by rw [← h]
  rw [hb] at c2 n2 f2
  have m1 : arg w₁ ∈ Ioo 0 (min b π) := ⟨a1, lt_min c1 b1⟩
  have m2 : arg w₂ ∈ Ioo 0 (min b π) := ⟨a2, lt_min c2 b2⟩
  have harg : arg w₁ = arg w₂ :=
    (strictAntiOn_lambertLevelProfile b).injOn m1 m2 (by rw [← f1, ← f2, h])
  exact ext_norm_arg (by rw [n1, n2, harg]) harg

/-- `x + log x` is injective on the positive reals. -/
private lemma add_log_injOn {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : x + Real.log x = y + Real.log y) : x = y := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · have := Real.log_lt_log hx hxy; linarith
  · exact hxy
  · have := Real.log_lt_log hy hxy; linarith

/-- Injectivity of `w + log w` on the slit plane. -/
lemma lambertLogMap_injOn : InjOn lambertLogMap slitPlane := by
  intro w₁ h₁ w₂ h₂ h
  obtain ⟨p1, n1, z1⟩ := lambertLogMap_im_sign h₁
  obtain ⟨p2, n2, z2⟩ := lambertLogMap_im_sign h₂
  rcases lt_trichotomy w₁.im 0 with hi | hi | hi
  · have hi2 : w₂.im < 0 := by
      rcases lt_trichotomy w₂.im 0 with h' | h' | h'
      · exact h'
      · have := (z2 h').1; have := n1 hi; rw [h] at *; linarith
      · have := p2 h'; have := n1 hi; rw [h] at *; linarith
    have := lambertLogMap_injOn_upper (w₁ := conj w₁) (w₂ := conj w₂) (by simpa using hi)
      (by simpa using hi2) (by rw [lambertLogMap_conj h₁, lambertLogMap_conj h₂, h])
    exact (RingHom.injective _ this)
  · obtain ⟨hz, hr⟩ := z1 hi
    have hi2 : w₂.im = 0 := by
      rcases lt_trichotomy w₂.im 0 with h' | h' | h'
      · have := n2 h'; rw [h] at hz; linarith
      · exact h'
      · have := p2 h'; rw [h] at hz; linarith
    obtain ⟨_, hr2⟩ := z2 hi2
    have hre := congrArg Complex.re h
    rw [lambertLogMap_re, lambertLogMap_re] at hre
    have e1 : ‖w₁‖ = w₁.re := by
      rw [← norm_mul_cos_arg w₁, arg_eq_zero_iff.mpr ⟨hr.le, hi⟩]; simp
    have e2 : ‖w₂‖ = w₂.re := by
      rw [← norm_mul_cos_arg w₂, arg_eq_zero_iff.mpr ⟨hr2.le, hi2⟩]; simp
    rw [e1, e2] at hre
    exact Complex.ext (add_log_injOn hr hr2 hre) (by rw [hi, hi2])
  · have hi2 : 0 < w₂.im := by
      rcases lt_trichotomy w₂.im 0 with h' | h' | h'
      · have := n2 h'; have := p1 hi; rw [h] at *; linarith
      · have := (z2 h').1; have := p1 hi; rw [h] at *; linarith
      · exact h'
    exact lambertLogMap_injOn_upper hi hi2 h

/-- `u cos u ≤ sin u` on `(0, π)`. -/
private lemma mul_cos_le_sin {u : ℝ} (h0 : 0 < u) (hπ : u < π) : u * Real.cos u ≤ Real.sin u := by
  have hs : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  rcases le_or_gt (Real.cos u) 0 with hc | hc
  · nlinarith
  · have hu2 : u < π / 2 := by
      by_contra hh
      have := Real.cos_nonpos_of_pi_div_two_le_of_le (not_lt.mp hh) (by linarith)
      linarith
    have := Real.le_tan h0.le hu2
    rw [Real.tan_eq_sin_div_cos, le_div_iff₀ hc] at this
    exact this

/-- On the slit plane, `Im (w + log w) = ±π` forces `Re (w + log w) > -1`. -/
lemma neg_one_lt_lambertLogMap_re {w : ℂ} (hw : w ∈ slitPlane)
    (h : |(lambertLogMap w).im| = π) : -1 < (lambertLogMap w).re := by
  have key : ∀ v : ℂ, 0 < v.im → (lambertLogMap v).im = π → -1 < (lambertLogMap v).re := by
    intro v hv hb
    obtain ⟨a1, b1, -, -, f1⟩ := lambertLogMap_param hv
    rw [f1, hb, lambertLevelProfile]
    set θ := arg v
    have hu0 : 0 < π - θ := by linarith
    have hs : Real.sin θ = Real.sin (π - θ) := (Real.sin_pi_sub θ).symm
    have hc : Real.cos θ = -Real.cos (π - θ) := by rw [Real.cos_pi_sub]; ring
    have hsp : 0 < Real.sin (π - θ) := Real.sin_pos_of_pos_of_lt_pi hu0 (by linarith)
    have hmc := mul_cos_le_sin hu0 (by linarith : π - θ < π)
    have hlt := Real.sin_lt hu0
    have hlog : 0 < Real.log ((π - θ) / Real.sin θ) := by
      apply Real.log_pos; rw [hs, one_lt_div hsp]; exact hlt
    have h1 : -1 ≤ (π - θ) * Real.cos θ / Real.sin θ := by
      rw [hs, hc, le_div_iff₀ hsp]; nlinarith
    linarith
  obtain ⟨p1, n1, z1⟩ := lambertLogMap_im_sign hw
  rcases lt_trichotomy w.im 0 with hi | hi | hi
  · have hc := lambertLogMap_conj hw
    have := key (conj w) (by simpa using hi) (by
      rw [hc, conj_im, abs_of_neg (n1 hi)] at *; linarith)
    rwa [hc, conj_re] at this
  · rw [(z1 hi).1] at h; simp at h; linarith [Real.pi_pos]
  · exact key w hi (by rw [abs_of_pos (p1 hi)] at h; exact h)

/-- On the slit plane, `|Im (w + log w)| ≤ π` forces `Re w > -1`. -/
lemma neg_one_lt_re_of_abs_lambertLogMap_im_le {w : ℂ} (hw : w ∈ slitPlane)
    (h : |(lambertLogMap w).im| ≤ π) : -1 < w.re := by
  have key : ∀ v : ℂ, 0 < v.im → (lambertLogMap v).im ≤ π → -1 < v.re := by
    intro v hv hb
    obtain ⟨a1, b1, -, -, -⟩ := lambertLogMap_param hv
    have him := norm_mul_sin_arg v
    have hre := norm_mul_cos_arg v
    have himv : v.im = (lambertLogMap v).im - arg v := by rw [lambertLogMap_im]; ring
    set θ := arg v
    rcases le_or_gt 0 (Real.cos θ) with hc | hc
    · rw [← hre]; nlinarith [norm_nonneg v]
    · have hθ : π / 2 < θ := by
        by_contra hh
        have := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (not_lt.mp hh)
        linarith
      have hu0 : 0 < π - θ := by linarith
      have ht := Real.lt_tan hu0 (by linarith : π - θ < π / 2)
      rw [Real.tan_eq_sin_div_cos, Real.sin_pi_sub, Real.cos_pi_sub] at ht
      have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi a1 b1
      have hlt : ‖v‖ * Real.sin θ < Real.sin θ / -Real.cos θ := by linarith
      rw [lt_div_iff₀ (by linarith)] at hlt
      rw [← hre]; nlinarith
  obtain ⟨p1, n1, z1⟩ := lambertLogMap_im_sign hw
  rcases lt_trichotomy w.im 0 with hi | hi | hi
  · have hc := lambertLogMap_conj hw
    have := key (conj w) (by simpa using hi) (by
      rw [hc, conj_im]; rw [abs_le] at h; linarith)
    simpa using this
  · linarith [(z1 hi).2]
  · exact key w hi (le_trans (le_abs_self _) h)

/-- On the slit plane, `|Im (w + log w)| ≥ π` forces `‖w‖ ≥ 1`. -/
lemma one_le_norm_of_pi_le_abs_lambertLogMap_im {w : ℂ} (hw : w ∈ slitPlane)
    (h : π ≤ |(lambertLogMap w).im|) : 1 ≤ ‖w‖ := by
  have key : ∀ v : ℂ, 0 < v.im → π ≤ (lambertLogMap v).im → 1 ≤ ‖v‖ := by
    intro v hv hb
    obtain ⟨a1, b1, -, -, -⟩ := lambertLogMap_param hv
    have him := norm_mul_sin_arg v
    have himv : v.im = (lambertLogMap v).im - arg v := by rw [lambertLogMap_im]; ring
    set θ := arg v
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi a1 b1
    have hle := Real.sin_le (by linarith : (0 : ℝ) ≤ π - θ)
    rw [Real.sin_pi_sub] at hle
    by_contra hh
    have : ‖v‖ * Real.sin θ < Real.sin θ := by nlinarith
    linarith
  obtain ⟨p1, n1, z1⟩ := lambertLogMap_im_sign hw
  rcases lt_trichotomy w.im 0 with hi | hi | hi
  · have hc := lambertLogMap_conj hw
    have := key (conj w) (by simpa using hi) (by
      rw [hc, conj_im, abs_of_neg (n1 hi)] at *; linarith)
    simpa using this
  · rw [(z1 hi).1] at h; simp at h; linarith [Real.pi_pos]
  · exact key w hi (by rw [abs_of_pos (p1 hi)] at h; exact h)

/-- A bound on `w` in terms of `w + log w`. -/
lemma norm_le_of_lambertLogMap (w : ℂ) : ‖w‖ ≤ 2 * (‖lambertLogMap w‖ + π) := by
  have hlog : ‖Complex.log w‖ ≤ |Real.log ‖w‖| + π := by
    refine (norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.log_re, Complex.log_im]
    gcongr
    exact abs_arg_le_pi w
  have htri : ‖w‖ ≤ ‖lambertLogMap w‖ + ‖Complex.log w‖ := by
    have : w = lambertLogMap w - Complex.log w := by simp [lambertLogMap]
    calc ‖w‖ = ‖lambertLogMap w - Complex.log w‖ := by rw [← this]
      _ ≤ _ := norm_sub_le _ _
  have hn := norm_nonneg (lambertLogMap w)
  rcases le_or_gt ‖w‖ 1 with h1 | h1
  · nlinarith [Real.two_le_pi]
  · have hl : Real.log ‖w‖ ≤ ‖w‖ / 2 := by
      rw [Real.log_le_iff_le_exp (by linarith)]
      have := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ ‖w‖ / 2)
      nlinarith [sq_nonneg (‖w‖ / 2 - 1)]
    rw [abs_of_pos (Real.log_pos h1)] at hlog
    linarith


/-- `sin` tends to `0⁺` at `0⁺`. -/
private lemma tendsto_sin_nhdsGT_zero :
    Tendsto Real.sin (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have := Real.continuous_sin.tendsto 0; rw [Real.sin_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsGT Real.pi_pos] with θ hθ
    exact Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2

/-- `sin` tends to `0⁺` at `π⁻`. -/
private lemma tendsto_sin_nhdsLT_pi :
    Tendsto Real.sin (𝓝[<] π) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have := Real.continuous_sin.tendsto π; rw [Real.sin_pi] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsLT Real.pi_pos] with θ hθ
    exact Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2

/-- The level profile tends to `+∞` at `0⁺`. -/
private lemma tendsto_lambertLevelProfile_zero {b : ℝ} (hb : 0 < b) :
    Tendsto (lambertLevelProfile b) (𝓝[>] 0) atTop := by
  have hinv : Tendsto (fun θ => (Real.sin θ)⁻¹) (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero.comp tendsto_sin_nhdsGT_zero
  have hc1 : Tendsto (fun θ : ℝ => (b - θ) * Real.cos θ) (𝓝[>] 0) (𝓝 b) := by
    have : Continuous (fun θ : ℝ => (b - θ) * Real.cos θ) := by fun_prop
    have h := this.tendsto 0
    simp only [sub_zero, Real.cos_zero, mul_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hc2 : Tendsto (fun θ : ℝ => b - θ) (𝓝[>] 0) (𝓝 b) := by
    have h : Tendsto (fun θ : ℝ => b - θ) (𝓝 0) (𝓝 (b - 0)) := tendsto_const_nhds.sub tendsto_id
    rw [sub_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hA := hc1.pos_mul_atTop hb hinv
  have hB := Real.tendsto_log_atTop.comp (hc2.pos_mul_atTop hb hinv)
  refine (hA.atTop_add_atTop hB).congr fun θ => ?_
  simp [lambertLevelProfile, div_eq_mul_inv]

/-- The level profile tends to `-∞` at `b⁻` when `b < π`. -/
private lemma tendsto_lambertLevelProfile_lt_pi {b : ℝ} (hb : 0 < b) (hbπ : b < π) :
    Tendsto (lambertLevelProfile b) (𝓝[<] b) atBot := by
  have hsb : Real.sin b ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hb hbπ).ne'
  have hA : Tendsto (fun θ => (b - θ) * Real.cos θ / Real.sin θ) (𝓝[<] b) (𝓝 0) := by
    have hcont : ContinuousAt (fun θ => (b - θ) * Real.cos θ / Real.sin θ) b :=
      ((continuousAt_const.sub continuousAt_id).mul Real.continuous_cos.continuousAt).div
        Real.continuous_sin.continuousAt hsb
    have h := hcont.tendsto
    simp only [sub_self, zero_mul, zero_div] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hq : Tendsto (fun θ => (b - θ) / Real.sin θ) (𝓝[<] b) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hcont : ContinuousAt (fun θ => (b - θ) / Real.sin θ) b :=
        (continuousAt_const.sub continuousAt_id).div Real.continuous_sin.continuousAt hsb
      have h := hcont.tendsto
      simp only [sub_self, zero_div] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT hb] with θ hθ
      exact div_pos (by linarith [hθ.2])
        (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2]))
  exact hA.add_atBot (Real.tendsto_log_nhdsGT_zero.comp hq)

/-- The level profile tends to `-∞` at `π⁻` when `b > π`. -/
private lemma tendsto_lambertLevelProfile_gt_pi {b : ℝ} (hbπ : π < b) :
    Tendsto (lambertLevelProfile b) (𝓝[<] π) atBot := by
  set N : ℝ → ℝ := fun θ => (b - θ) * Real.cos θ - Real.sin θ * Real.log (Real.sin θ)
  have hN : Tendsto N (𝓝[<] π) (𝓝 (-(b - π))) := by
    have hcont : Continuous N := by
      simp only [N]
      exact ((continuous_const.sub continuous_id).mul Real.continuous_cos).sub
        (Real.continuous_mul_log.comp Real.continuous_sin :)
    have h := hcont.tendsto π
    simp only [N, Real.cos_pi, Real.sin_pi, zero_mul, sub_zero, mul_neg, mul_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hinv : Tendsto (fun θ => (Real.sin θ)⁻¹) (𝓝[<] π) atTop :=
    tendsto_inv_nhdsGT_zero.comp tendsto_sin_nhdsLT_pi
  have hL : Tendsto (fun θ : ℝ => Real.log (b - θ)) (𝓝[<] π) (𝓝 (Real.log (b - π))) := by
    have hcont : ContinuousAt (fun θ : ℝ => Real.log (b - θ)) π :=
      (continuousAt_const.sub continuousAt_id).log (by simpa using (sub_pos.mpr hbπ).ne')
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hsum := (hN.neg_mul_atTop (by linarith) hinv).atBot_add hL
  refine hsum.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT Real.pi_pos] with θ hθ
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  simp only [N, lambertLevelProfile]
  rw [Real.log_div (by linarith [hθ.2]) hs.ne']
  field_simp
  ring

/-- The level profile tends to `-1` at `π⁻` when `b = π`. -/
private lemma tendsto_lambertLevelProfile_pi :
    Tendsto (lambertLevelProfile π) (𝓝[<] π) (𝓝 (-1)) := by
  set G : ℝ → ℝ := fun θ => Real.cos θ / Real.sinc (π - θ) - Real.log (Real.sinc (π - θ))
  have hG : Tendsto G (𝓝[<] π) (𝓝 (-1)) := by
    have hs : Continuous fun θ : ℝ => Real.sinc (π - θ) :=
      Real.continuous_sinc.comp (continuous_const.sub continuous_id)
    have hcont : ContinuousAt G π := by
      apply ContinuousAt.sub
      · exact Real.continuous_cos.continuousAt.div hs.continuousAt (by simp)
      · exact hs.continuousAt.log (by simp)
    have h := hcont.tendsto
    simp only [G, sub_self, Real.sinc_zero, Real.cos_pi, div_one, Real.log_one,
      sub_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine hG.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT Real.pi_pos] with θ hθ
  have hu : π - θ ≠ 0 := by linarith [hθ.2]
  have hs : 0 < Real.sin (π - θ) := Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.2])
    (by linarith [hθ.1])
  simp only [G, lambertLevelProfile, Real.sinc_of_ne_zero hu, Real.sin_pi_sub] at hs ⊢
  rw [Real.log_div hs.ne' hu, Real.log_div hu hs.ne']
  field_simp
  ring

/-- Surjectivity of `w + log w` from the upper half-plane onto the admissible upper values. -/
lemma exists_lambertLogMap_eq_upper {a b : ℝ} (hb : 0 < b) (hπ : b ≠ π ∨ -1 < a) :
    ∃ w : ℂ, 0 < w.im ∧ lambertLogMap w = ⟨a, b⟩ := by
  set m := min b π
  have hm : 0 < m := lt_min hb Real.pi_pos
  -- a point near `0` above level `a`
  obtain ⟨θ₁, h₁a, h₁m⟩ := (((tendsto_lambertLevelProfile_zero hb).eventually
    (eventually_gt_atTop a)).and (Ioo_mem_nhdsGT (half_pos hm))).exists
  -- a point near `m` below level `a`
  have hlow : ∃ θ₂ ∈ Ioo (m / 2) m, lambertLevelProfile b θ₂ < a := by
    rcases lt_trichotomy b π with hbπ | hbπ | hbπ
    · have hmb : m = b := min_eq_left hbπ.le
      obtain ⟨θ, h1, h2⟩ := (((tendsto_lambertLevelProfile_lt_pi hb hbπ).eventually
        (eventually_lt_atBot a)).and (Ioo_mem_nhdsLT (by rw [← hmb]; exact half_lt_self hm))).exists
      exact ⟨θ, ⟨h2.1, by rw [hmb]; exact h2.2⟩, h1⟩
    · have hmb : m = π := by simp [m, hbπ]
      have ha : -1 < a := hπ.resolve_left (not_not.mpr hbπ)
      subst hbπ
      obtain ⟨θ, h1, h2⟩ := ((tendsto_lambertLevelProfile_pi.eventually
        (eventually_lt_nhds ha)).and (Ioo_mem_nhdsLT (by rw [← hmb]; exact half_lt_self hm))).exists
      exact ⟨θ, ⟨h2.1, by rw [hmb]; exact h2.2⟩, h1⟩
    · have hmb : m = π := min_eq_right hbπ.le
      obtain ⟨θ, h1, h2⟩ := (((tendsto_lambertLevelProfile_gt_pi hbπ).eventually
        (eventually_lt_atBot a)).and (Ioo_mem_nhdsLT (by rw [← hmb]; exact half_lt_self hm))).exists
      exact ⟨θ, ⟨h2.1, by rw [hmb]; exact h2.2⟩, h1⟩
  obtain ⟨θ₂, h₂m, h₂a⟩ := hlow
  have hprop : ∀ θ ∈ Icc θ₁ θ₂, 0 < b - θ ∧ 0 < Real.sin θ ∧ 0 < θ ∧ θ < π := fun θ hθ =>
    ⟨by linarith [hθ.2, h₂m.2, min_le_left b π],
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, h₁m.1])
        (by linarith [hθ.2, h₂m.2, min_le_right b π]),
      by linarith [hθ.1, h₁m.1], by linarith [hθ.2, h₂m.2, min_le_right b π]⟩
  have hcont : ContinuousOn (lambertLevelProfile b) (Icc θ₁ θ₂) := fun θ hθ =>
    (hasDerivAt_lambertLevelProfile (hprop θ hθ).1
      (hprop θ hθ).2.1.ne').continuousAt.continuousWithinAt
  obtain ⟨θ, hθ, hFθ⟩ := intermediate_value_Icc' (by linarith [h₁m.2, h₂m.1]) hcont
    ⟨h₂a.le, h₁a.le⟩
  obtain ⟨hu, hs, h0, hπ'⟩ := hprop θ hθ
  set r := (b - θ) / Real.sin θ
  have hr : 0 < r := div_pos hu hs
  set w : ℂ := (r : ℂ) * (Complex.cos θ + Complex.sin θ * I)
  have hwim : w.im = b - θ := by
    have : w.im = r * Real.sin θ := by
      simp only [w, mul_im, ofReal_re, ofReal_im, add_im, add_re, mul_re, I_re, I_im,
        ← ofReal_cos, ← ofReal_sin]
      simp
    rw [this]; simp only [r]; field_simp
  have hwre : w.re = r * Real.cos θ := by
    simp only [w, mul_im, ofReal_re, ofReal_im, add_im, add_re, mul_re, I_re, I_im,
      ← ofReal_cos, ← ofReal_sin]
    simp
  have hwarg : arg w = θ := arg_mul_cos_add_sin_mul_I hr ⟨by linarith, hπ'.le⟩
  have hwnorm : ‖w‖ = r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      norm_cos_add_sin_mul_I, mul_one]
  refine ⟨w, by rw [hwim]; exact hu, Complex.ext ?_ ?_⟩
  · rw [lambertLogMap_re, hwre, hwnorm, ← hFθ, lambertLevelProfile]
    simp only [r]; ring
  · rw [lambertLogMap_im, hwim, hwarg]; simp


/-- The image domain of `w + log w` on the slit plane: the plane minus the half-lines
`Im ζ = ±π`, `Re ζ ≤ -1`. -/
def lambertOmegaDomain : Set ℂ := {ζ | -1 < ζ.re ∨ |ζ.im| ≠ π}

/-- The image domain is open. -/
lemma isOpen_lambertOmegaDomain : IsOpen lambertOmegaDomain :=
  (isOpen_lt continuous_const Complex.continuous_re).union
    (isOpen_ne_fun (continuous_abs.comp Complex.continuous_im) continuous_const)

/-- `w + log w` maps the slit plane into `lambertOmegaDomain`. -/
lemma lambertLogMap_mem_lambertOmegaDomain {w : ℂ} (hw : w ∈ slitPlane) :
    lambertLogMap w ∈ lambertOmegaDomain := by
  by_cases h : |(lambertLogMap w).im| = π
  · exact Or.inl (neg_one_lt_lambertLogMap_re hw h)
  · exact Or.inr h

/-- `x + log x` attains every real value on the positive reals. -/
private lemma exists_add_log_eq (a : ℝ) : ∃ r : ℝ, 0 < r ∧ r + Real.log r = a := by
  set r₁ := Real.exp (-|a| - 1)
  set r₂ := |a| + 1
  have h1 : r₁ < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 by simp]; apply Real.exp_lt_exp.mpr; linarith [abs_nonneg a]
  have hr₁ : 0 < r₁ := Real.exp_pos _
  have hr₂ : 1 ≤ r₂ := by linarith [abs_nonneg a]
  have hcont : ContinuousOn (fun r => r + Real.log r) (Icc r₁ r₂) := by
    apply ContinuousOn.add continuousOn_id
    exact Real.continuousOn_log.mono fun r hr => by
      simp only [mem_compl_iff, mem_singleton_iff]; linarith [hr.1]
  have hv1 : r₁ + Real.log r₁ ≤ a := by
    simp only [r₁, Real.log_exp]; linarith [neg_abs_le a]
  have hv2 : a ≤ r₂ + Real.log r₂ := by
    have := Real.log_nonneg hr₂; simp only [r₂] at *; linarith [le_abs_self a]
  obtain ⟨r, hr, hra⟩ := intermediate_value_Icc (by linarith) hcont ⟨hv1, hv2⟩
  exact ⟨r, by linarith [hr.1], hra⟩

/-- Surjectivity of `w + log w` from the slit plane onto `lambertOmegaDomain`. -/
lemma exists_lambertLogMap_eq {ζ : ℂ} (hζ : ζ ∈ lambertOmegaDomain) :
    ∃ w ∈ slitPlane, lambertLogMap w = ζ := by
  rcases lt_trichotomy ζ.im 0 with h | h | h
  · obtain ⟨v, hv, hgv⟩ := exists_lambertLogMap_eq_upper (a := ζ.re) (b := -ζ.im)
      (by linarith) (by
        rcases hζ with h' | h'
        · exact Or.inr h'
        · left; rw [abs_of_neg h] at h'; exact h')
    have hvS : v ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inr hv.ne')
    refine ⟨conj v, conj_mem_slitPlane hvS, ?_⟩
    rw [lambertLogMap_conj hvS, hgv]
    apply Complex.ext <;> simp
  · obtain ⟨r, hr, hra⟩ := exists_add_log_eq ζ.re
    refine ⟨r, mem_slitPlane_iff.mpr (Or.inl (by simpa using hr)), Complex.ext ?_ ?_⟩
    · rw [lambertLogMap_re]; simp [abs_of_pos hr, hra]
    · rw [lambertLogMap_im, h]; simp [arg_ofReal_of_nonneg hr.le]
  · obtain ⟨v, hv, hgv⟩ := exists_lambertLogMap_eq_upper (a := ζ.re) (b := ζ.im) h (by
        rcases hζ with h' | h'
        · exact Or.inr h'
        · left; rw [abs_of_pos h] at h'; exact h')
    exact ⟨v, mem_slitPlane_iff.mpr (Or.inr hv.ne'), by rw [hgv]⟩

/-- The inverse of `w ↦ w + log w` on `lambertOmegaDomain` (Wright's omega function off its
cuts), totalized by `0` elsewhere. -/
@[irreducible] def lambertLogMapInv (ζ : ℂ) : ℂ :=
  open Classical in if h : ∃ w ∈ slitPlane, lambertLogMap w = ζ then h.choose else 0

/-- The inverse lands in the slit plane and inverts `w + log w`. -/
lemma lambertLogMapInv_spec {ζ : ℂ} (hζ : ζ ∈ lambertOmegaDomain) :
    lambertLogMapInv ζ ∈ slitPlane ∧ lambertLogMap (lambertLogMapInv ζ) = ζ := by
  have h := exists_lambertLogMap_eq hζ
  unfold lambertLogMapInv
  split_ifs
  exact h.choose_spec

/-- The inverse is a left inverse on the slit plane. -/
lemma lambertLogMapInv_lambertLogMap {w : ℂ} (hw : w ∈ slitPlane) :
    lambertLogMapInv (lambertLogMap w) = w := by
  obtain ⟨h1, h2⟩ := lambertLogMapInv_spec (lambertLogMap_mem_lambertOmegaDomain hw)
  exact lambertLogMap_injOn h1 hw h2

/-- The inverse of `w + log w` is complex differentiable on `lambertOmegaDomain`. -/
lemma differentiableAt_lambertLogMapInv {ζ : ℂ} (hζ : ζ ∈ lambertOmegaDomain) :
    DifferentiableAt ℂ lambertLogMapInv ζ := by
  obtain ⟨hw0, hgw0⟩ := lambertLogMapInv_spec hζ
  set w0 := lambertLogMapInv ζ
  have hg : HasStrictDerivAt lambertLogMap (1 + w0⁻¹) w0 :=
    (hasStrictDerivAt_id w0).add (hasStrictDerivAt_log hw0)
  have hne : 1 + w0⁻¹ ≠ 0 := by
    intro h
    have hw0' : w0 ≠ 0 := slitPlane_ne_zero hw0
    have : w0 = -1 := by field_simp at h; linear_combination h
    rw [this] at hw0; norm_num [mem_slitPlane_iff] at hw0
  set φ := hg.localInverse lambertLogMap (1 + w0⁻¹) w0 hne
  have hφd : HasStrictDerivAt φ (1 + w0⁻¹)⁻¹ (lambertLogMap w0) := hg.to_localInverse hne
  have hφ0 : φ (lambertLogMap w0) = w0 := (hg.eventually_left_inverse hne).self_of_nhds
  have hφc : ContinuousAt φ (lambertLogMap w0) := hφd.hasDerivAt.continuousAt
  have hev : lambertLogMapInv =ᶠ[𝓝 (lambertLogMap w0)] φ := by
    have hS : φ ⁻¹' slitPlane ∈ 𝓝 (lambertLogMap w0) :=
      hφc.preimage_mem_nhds (by rw [hφ0]; exact isOpen_slitPlane.mem_nhds hw0)
    filter_upwards [hS, hg.eventually_right_inverse hne] with y hy1 hy2
    rw [← hy2, lambertLogMapInv_lambertLogMap hy1, hy2]
  rw [← hgw0]
  exact (hφd.hasDerivAt.congr_of_eventuallyEq hev).differentiableAt

/-- Continuity of the inverse on its domain. -/
lemma continuousAt_lambertLogMapInv {ζ : ℂ} (hζ : ζ ∈ lambertOmegaDomain) :
    ContinuousAt lambertLogMapInv ζ :=
  (differentiableAt_lambertLogMapInv hζ).continuousAt

/-- `exp (w + log w) = w e^w` for `w ≠ 0`. -/
lemma exp_lambertLogMap {w : ℂ} (hw : w ≠ 0) :
    Complex.exp (lambertLogMap w) = w * Complex.exp w := by
  rw [lambertLogMap, Complex.exp_add, Complex.exp_log hw, mul_comm]


/-! ### Real inverses of `y e^y` -/

/-- `y ↦ y e^y` is strictly increasing on `[-1, ∞)`. -/
lemma strictMonoOn_mul_exp_Ici :
    StrictMonoOn (fun y : ℝ => y * Real.exp y) (Ici (-1)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · exact (continuous_id.mul Real.continuous_exp).continuousOn
  · intro y hy
    rw [interior_Ici] at hy
    have : deriv (fun y : ℝ => y * Real.exp y) y = (y + 1) * Real.exp y := by
      have := (hasDerivAt_id y).fun_mul (Real.hasDerivAt_exp y)
      simp only [id] at this; rw [this.deriv]; ring
    rw [this]; exact mul_pos (by simp at hy; linarith) (Real.exp_pos _)

/-- `y ↦ y e^y` is strictly decreasing on `(-∞, -1]`. -/
lemma strictAntiOn_mul_exp_Iic :
    StrictAntiOn (fun y : ℝ => y * Real.exp y) (Iic (-1)) := by
  apply strictAntiOn_of_deriv_neg (convex_Iic _)
  · exact (continuous_id.mul Real.continuous_exp).continuousOn
  · intro y hy
    rw [interior_Iic] at hy
    have : deriv (fun y : ℝ => y * Real.exp y) y = (y + 1) * Real.exp y := by
      have := (hasDerivAt_id y).fun_mul (Real.hasDerivAt_exp y)
      simp only [id] at this; rw [this.deriv]; ring
    rw [this]; exact mul_neg_of_neg_of_pos (by simp at hy; linarith) (Real.exp_pos _)

/-- The real solution `y ≥ -1` of `y e^y = x`, totalized by `0`. -/
@[irreducible] def lambertRealUpper (x : ℝ) : ℝ :=
  open Classical in if h : ∃ y : ℝ, -1 ≤ y ∧ y * Real.exp y = x then h.choose else 0

/-- The real solution `y ≤ -1` of `y e^y = x`, totalized by `0`. -/
@[irreducible] def lambertRealLower (x : ℝ) : ℝ :=
  open Classical in if h : ∃ y : ℝ, y ≤ -1 ∧ y * Real.exp y = x then h.choose else 0

/-- The upper real inverse on `[-1/e, 0]`. -/
lemma lambertRealUpper_spec {x : ℝ} (hx : -Real.exp (-1) ≤ x) (hx0 : x ≤ 0) :
    -1 ≤ lambertRealUpper x ∧ lambertRealUpper x * Real.exp (lambertRealUpper x) = x := by
  have h : ∃ y : ℝ, -1 ≤ y ∧ y * Real.exp y = x := by
    have hcont : ContinuousOn (fun y : ℝ => y * Real.exp y) (Icc (-1) 0) :=
      (continuous_id.mul Real.continuous_exp).continuousOn
    obtain ⟨y, hy, hyx⟩ := intermediate_value_Icc (by norm_num) hcont
      ⟨by simpa using hx, by simpa using hx0⟩
    exact ⟨y, hy.1, hyx⟩
  unfold lambertRealUpper
  split_ifs
  exact h.choose_spec

/-- The lower real inverse on `[-1/e, 0)`. -/
lemma lambertRealLower_spec {x : ℝ} (hx : -Real.exp (-1) ≤ x) (hx0 : x < 0) :
    lambertRealLower x ≤ -1 ∧ lambertRealLower x * Real.exp (lambertRealLower x) = x := by
  have h : ∃ y : ℝ, y ≤ -1 ∧ y * Real.exp y = x := by
    set t := max 1 (2 / -x)
    have ht1 : 1 ≤ t := le_max_left _ _
    have ht2 : 2 / -x ≤ t := le_max_right _ _
    have hval : x ≤ -t * Real.exp (-t) := by
      have he := Real.quadratic_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ t)
      have hpos : 0 < Real.exp t := Real.exp_pos t
      rw [Real.exp_neg, neg_mul, ← div_eq_mul_inv, le_neg, div_le_iff₀ hpos]
      rw [div_le_iff₀ (by linarith)] at ht2
      nlinarith
    have hcont : ContinuousOn (fun y : ℝ => y * Real.exp y) (Icc (-t) (-1)) :=
      (continuous_id.mul Real.continuous_exp).continuousOn
    obtain ⟨y, hy, hyx⟩ := intermediate_value_Icc' (by linarith) hcont
      ⟨by simpa using hx, hval⟩
    exact ⟨y, hy.2, hyx⟩
  unfold lambertRealLower
  split_ifs
  exact h.choose_spec

/-! ### The branch values -/

/-- Upper-side values of the Lambert branch `W_k`: Wright's inverse of `w + log w` evaluated
at `log z + 2πik` off the cuts, and the real inverses of `y e^y` on the remaining cut pieces. -/
def lambertBranchValue (k : ℤ) (z : ℂ) : ℂ :=
  open Classical in if z = 0 then 0
  else if Complex.log z + 2 * π * I * k ∈ lambertOmegaDomain then
    lambertLogMapInv (Complex.log z + 2 * π * I * k)
  else if k = 0 then (lambertRealUpper z.re : ℂ) else (lambertRealLower z.re : ℂ)

/-- The real part of `log z + 2πik`. -/
lemma re_log_add_two_pi_mul_I_mul (k : ℤ) (z : ℂ) :
    (Complex.log z + 2 * π * I * k).re = Real.log ‖z‖ := by
  simp [Complex.log_re]

/-- The imaginary part of `log z + 2πik`. -/
lemma im_log_add_two_pi_mul_I_mul (k : ℤ) (z : ℂ) :
    (Complex.log z + 2 * π * I * k).im = arg z + 2 * π * k := by
  simp [Complex.log_im]

/-- Outside `lambertOmegaDomain` the argument lies on `[-1/e, 0)` and `k ∈ {0, -1}`. -/
lemma of_log_add_not_mem_lambertOmegaDomain {k : ℤ} {z : ℂ} (hz : z ≠ 0)
    (h : Complex.log z + 2 * π * I * k ∉ lambertOmegaDomain) :
    z.im = 0 ∧ z.re < 0 ∧ -Real.exp (-1) ≤ z.re ∧ (k = 0 ∨ k = -1) := by
  simp only [lambertOmegaDomain, mem_ofPred_eq, not_or, not_lt, not_not,
    re_log_add_two_pi_mul_I_mul,
    im_log_add_two_pi_mul_I_mul] at h
  obtain ⟨hre, him⟩ := h
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hnz : ‖z‖ ≤ Real.exp (-1) := (Real.log_le_iff_le_exp hn).mp hre
  have ha1 := neg_pi_lt_arg z
  have ha2 := arg_le_pi z
  have hπ := Real.pi_pos
  have key : arg z = π ∧ (k = 0 ∨ k = -1) := by
    rcases abs_eq hπ.le |>.mp him with h1 | h1
    · have hk1 : (k : ℝ) < 1 := by nlinarith
      have hk0 : (0 : ℝ) ≤ k := by nlinarith
      have : k = 0 := by
        have a : k < 1 := by exact_mod_cast hk1
        have b : 0 ≤ k := by exact_mod_cast hk0
        omega
      subst this
      exact ⟨by simpa using h1, Or.inl rfl⟩
    · have hk1 : (k : ℝ) < 0 := by nlinarith
      have hk0 : (-1 : ℝ) ≤ k := by nlinarith
      have : k = -1 := by
        have a : k < 0 := by exact_mod_cast hk1
        have b : -1 ≤ k := by exact_mod_cast hk0
        omega
      subst this
      refine ⟨by push_cast at h1; linarith, Or.inr rfl⟩
  obtain ⟨hre', him'⟩ := arg_eq_pi_iff.mp key.1
  have hnorm : ‖z‖ = -z.re := by
    rw [← norm_mul_cos_arg z, key.1, Real.cos_pi]; ring
  exact ⟨him', hre', by linarith, key.2⟩

/-- On the slit plane every `log z + 2πik` lies in the image domain. -/
lemma log_add_mem_lambertOmegaDomain (k : ℤ) {z : ℂ} (hz : z ∈ slitPlane) :
    Complex.log z + 2 * π * I * k ∈ lambertOmegaDomain := by
  by_contra h
  obtain ⟨him, hre, -⟩ := of_log_add_not_mem_lambertOmegaDomain (slitPlane_ne_zero hz) h
  rcases mem_slitPlane_iff.mp hz with h' | h'
  · linarith
  · exact h' him

/-- On the slit plane the branch values are given by the inverse of `w + log w`. -/
lemma lambertBranchValue_of_mem_slitPlane (k : ℤ) {z : ℂ} (hz : z ∈ slitPlane) :
    lambertBranchValue k z = lambertLogMapInv (Complex.log z + 2 * π * I * k) := by
  rw [lambertBranchValue, ite_eq_right (slitPlane_ne_zero hz),
    ite_eq_left (log_add_mem_lambertOmegaDomain k hz)]

/-- All branches are totalized to `0` at the origin. -/
lemma lambertBranchValue_zero_right (k : ℤ) : lambertBranchValue k 0 = 0 := by
  simp [lambertBranchValue]

/-- `exp (log z + 2πik) = z`. -/
lemma exp_log_add_two_pi_mul_I_mul (k : ℤ) {z : ℂ} (hz : z ≠ 0) :
    Complex.exp (Complex.log z + 2 * π * I * k) = z := by
  rw [Complex.exp_add, Complex.exp_log hz,
    show 2 * (π : ℂ) * I * k = k * (2 * π * I) by ring, exp_int_mul_two_pi_mul_I, mul_one]

/-- The inverse equation `W e^W = z` for every branch (and every `z` on the principal branch). -/
lemma lambertBranchValue_mul_exp (k : ℤ) (z : ℂ) (hz : z ≠ 0 ∨ k = 0) :
    lambertBranchValue k z * Complex.exp (lambertBranchValue k z) = z := by
  by_cases h0 : z = 0
  · subst h0; simp [lambertBranchValue]
  by_cases hΩ : Complex.log z + 2 * π * I * k ∈ lambertOmegaDomain
  · rw [lambertBranchValue, ite_eq_right h0, ite_eq_left hΩ]
    obtain ⟨hS, hg⟩ := lambertLogMapInv_spec hΩ
    rw [← exp_lambertLogMap (slitPlane_ne_zero hS), hg, exp_log_add_two_pi_mul_I_mul k h0]
  · obtain ⟨him, hre, hle, hk⟩ := of_log_add_not_mem_lambertOmegaDomain h0 hΩ
    have hz' : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [lambertBranchValue, ite_eq_right h0, ite_eq_right hΩ]
    split_ifs with hk0
    · obtain ⟨-, he⟩ := lambertRealUpper_spec hle hre.le
      conv_rhs => rw [hz']
      rw [← ofReal_exp, ← ofReal_mul, he]
    · obtain ⟨-, he⟩ := lambertRealLower_spec hle hre
      conv_rhs => rw [hz']
      rw [← ofReal_exp, ← ofReal_mul, he]


/-! ### Bounds on the principal and the `-1` branch -/

/-- The principal values have real part at least `-1` and `|Im (w + log w)| ≤ π`. -/
lemma lambertBranchValue_zero_bounds (z : ℂ) :
    -1 ≤ (lambertBranchValue 0 z).re ∧
      (lambertBranchValue 0 z ∈ slitPlane →
        |(lambertLogMap (lambertBranchValue 0 z)).im| ≤ π) := by
  by_cases h0 : z = 0
  · subst h0; simp [lambertBranchValue, mem_slitPlane_iff]
  by_cases hΩ : Complex.log z + 2 * π * I * (0 : ℤ) ∈ lambertOmegaDomain
  · rw [lambertBranchValue, ite_eq_right h0, ite_eq_left hΩ]
    obtain ⟨hS, hg⟩ := lambertLogMapInv_spec hΩ
    have him : |(lambertLogMap (lambertLogMapInv (Complex.log z + 2 * π * I * (0 : ℤ)))).im|
        ≤ π := by
      rw [hg, im_log_add_two_pi_mul_I_mul]; simpa using abs_arg_le_pi z
    exact ⟨(neg_one_lt_re_of_abs_lambertLogMap_im_le hS him).le, fun _ => him⟩
  · obtain ⟨-, hre, hle, -⟩ := of_log_add_not_mem_lambertOmegaDomain h0 hΩ
    rw [lambertBranchValue, ite_eq_right h0, ite_eq_right hΩ, ite_eq_left rfl]
    refine ⟨by simpa using (lambertRealUpper_spec hle hre.le).1, fun _ => ?_⟩
    rw [lambertLogMap_im]; simpa using abs_arg_le_pi _

/-- The principal values satisfy `‖W₀(z)‖ ≤ e ‖z‖`. -/
lemma norm_lambertBranchValue_zero_le (z : ℂ) :
    ‖lambertBranchValue 0 z‖ ≤ Real.exp 1 * ‖z‖ := by
  have he := lambertBranchValue_mul_exp 0 z (Or.inr rfl)
  have hre := (lambertBranchValue_zero_bounds z).1
  set w := lambertBranchValue 0 z
  have hz : ‖z‖ = ‖w‖ * Real.exp w.re := by rw [← he, norm_mul, Complex.norm_exp]
  have h1 : Real.exp (-1) ≤ Real.exp w.re := Real.exp_le_exp.mpr hre
  have h2 : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
  have h3 : 1 ≤ Real.exp 1 * Real.exp w.re := by
    calc (1 : ℝ) = Real.exp 1 * Real.exp (-1) := h2.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (Real.exp_pos 1).le
  rw [hz]
  calc ‖w‖ = ‖w‖ * 1 := by ring
    _ ≤ ‖w‖ * (Real.exp 1 * Real.exp w.re) := by gcongr
    _ = _ := by ring

/-- In the closed upper half-plane the `-1` branch has norm at least `1` and
`Im (w + log w) ∈ [-2π, -π]`. -/
lemma lambertBranchValue_neg_one_bounds {z : ℂ} (hz : 0 ≤ z.im) (hz0 : z ≠ 0) :
    1 ≤ ‖lambertBranchValue (-1) z‖ ∧
      (lambertBranchValue (-1) z ∈ slitPlane →
        -(2 * π) ≤ (lambertLogMap (lambertBranchValue (-1) z)).im ∧
          (lambertLogMap (lambertBranchValue (-1) z)).im ≤ -π) := by
  by_cases hΩ : Complex.log z + 2 * π * I * (-1 : ℤ) ∈ lambertOmegaDomain
  · rw [lambertBranchValue, ite_eq_right hz0, ite_eq_left hΩ]
    obtain ⟨hS, hg⟩ := lambertLogMapInv_spec hΩ
    have ha0 := arg_nonneg_iff.mpr hz
    have ha1 := arg_le_pi z
    have him : -(2 * π) ≤ (lambertLogMap (lambertLogMapInv
        (Complex.log z + 2 * π * I * (-1 : ℤ)))).im ∧ (lambertLogMap (lambertLogMapInv
        (Complex.log z + 2 * π * I * (-1 : ℤ)))).im ≤ -π := by
      rw [hg, im_log_add_two_pi_mul_I_mul]; push_cast; constructor <;> linarith
    refine ⟨one_le_norm_of_pi_le_abs_lambertLogMap_im hS ?_, fun _ => him⟩
    rw [abs_of_neg (by linarith [Real.pi_pos])]; linarith
  · obtain ⟨-, hre, hle, -⟩ := of_log_add_not_mem_lambertOmegaDomain hz0 hΩ
    rw [lambertBranchValue, ite_eq_right hz0, ite_eq_right hΩ, ite_eq_right (by decide)]
    obtain ⟨hlow, -⟩ := lambertRealLower_spec hle hre
    refine ⟨?_, fun h => ?_⟩
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]; linarith
    · exfalso; rw [mem_slitPlane_iff] at h; simp at h; linarith

/-! ### Limits by compactness -/

/-- Limits of solutions of `w e^w = z` confined to a compact set with a unique solution over
the limit point. -/
lemma tendsto_of_unique_mul_exp_root {l : Filter ℂ} {f : ℂ → ℂ} {C : Set ℂ} (hC : IsClosed C)
    {R : ℝ} {x₀ w₀ : ℂ} (hl : l ≤ 𝓝 x₀)
    (hf : ∀ᶠ z in l, f z ∈ C ∧ ‖f z‖ ≤ R ∧ f z * Complex.exp (f z) = z)
    (huniq : ∀ w ∈ C, w * Complex.exp w = x₀ → w = w₀) : Tendsto f l (𝓝 w₀) := by
  refine ((isCompact_closedBall (0 : ℂ) R).inter_left hC).tendsto_nhds_of_unique_mapClusterPt
    ?_ fun w hw hcl => huniq w hw.1 ?_
  · filter_upwards [hf] with z hz
    exact ⟨hz.1, mem_closedBall_zero_iff.mpr hz.2.1⟩
  · have hh : Tendsto (fun z => f z * Complex.exp (f z)) l (𝓝 x₀) := by
      refine (tendsto_id.mono_left hl).congr' ?_
      filter_upwards [hf] with z hz
      exact hz.2.2.symm
    have hc : ContinuousAt (fun w : ℂ => w * Complex.exp w) w := by fun_prop
    have hcl2 := hcl.continuousAt_comp hc
    by_contra hne
    have hbot : 𝓝 (w * Complex.exp w) ⊓ map ((fun w : ℂ => w * Complex.exp w) ∘ f) l = ⊥ :=
      le_bot_iff.mp ((inf_le_inf_left _ hh).trans (disjoint_nhds_nhds.mpr hne).le_bot)
    exact hcl2.neBot.ne hbot

/-- Sets defined by a closed condition on `w + log w` over the slit plane are closed. -/
lemma isClosed_setOf_mem_slitPlane_imp {P : Set ℂ} (hP : IsClosed P) :
    IsClosed {w : ℂ | w ∈ slitPlane → lambertLogMap w ∈ P} := by
  have hcont : ContinuousOn lambertLogMap slitPlane :=
    continuousOn_id.add fun w hw => (continuousAt_clog hw).continuousWithinAt
  have hopen := hcont.isOpen_inter_preimage isOpen_slitPlane hP.isOpen_compl
  rw [← isOpen_compl_iff]
  convert hopen using 1
  ext w; simp

/-- A solution in the slit plane of `w e^w = x` with `x ∈ [-1/e, 0)`. -/
lemma lambertLogMap_of_mul_exp_eq {w : ℂ} (hw : w ∈ slitPlane) {x : ℝ}
    (hx : -Real.exp (-1) ≤ x) (hx0 : x < 0) (h : w * Complex.exp w = x) :
    (lambertLogMap w).re ≤ -1 ∧ ∃ n : ℤ, (lambertLogMap w).im = π + 2 * π * n := by
  have he : Complex.exp (lambertLogMap w) = Complex.exp (Complex.log x) := by
    rw [exp_lambertLogMap (slitPlane_ne_zero hw), h, Complex.exp_log (by exact_mod_cast hx0.ne)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  constructor
  · have : (lambertLogMap w).re = Real.log ‖(x : ℂ)‖ := by rw [hn]; simp [Complex.log_re]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hx0]
    rw [Real.log_le_iff_le_exp (by linarith)]; linarith
  · refine ⟨n, ?_⟩
    have : (lambertLogMap w).im = arg (x : ℂ) + 2 * π * n := by
      rw [hn]; simp [Complex.log_im]; ring
    rw [this, arg_ofReal_of_neg hx0]

/-- The principal cut values on `[-1/e, 0)`. -/
lemma lambertBranchValue_zero_ofReal {x : ℝ} (hx : -Real.exp (-1) ≤ x) (hx0 : x < 0) :
    lambertBranchValue 0 x = lambertRealUpper x ∧
      lambertBranchValue (-1) x = lambertRealLower x := by
  have hne : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne
  have hnot : ∀ k : ℤ, k = 0 ∨ k = -1 →
      Complex.log x + 2 * π * I * k ∉ lambertOmegaDomain := by
    intro k hk
    simp only [lambertOmegaDomain, mem_ofPred_eq, not_or, not_lt, not_not,
      re_log_add_two_pi_mul_I_mul,
      im_log_add_two_pi_mul_I_mul, arg_ofReal_of_neg hx0, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg hx0]
    refine ⟨by rw [Real.log_le_iff_le_exp (by linarith)]; linarith, ?_⟩
    rcases hk with rfl | rfl
    · simp [abs_of_pos Real.pi_pos]
    · push_cast; rw [abs_of_neg (by linarith [Real.pi_pos])]; ring
  constructor
  · rw [lambertBranchValue, ite_eq_right hne, ite_eq_right (hnot 0 (Or.inl rfl)), ite_eq_left rfl]
    simp
  · rw [lambertBranchValue, ite_eq_right hne, ite_eq_right (hnot (-1) (Or.inr rfl)),
      ite_eq_right (by decide)]
    simp

/-- Continuity of the principal branch on `[-1/e, 0]`, through the branch point. -/
lemma continuousAt_lambertBranchValue_zero_ofReal {x : ℝ} (hx : -Real.exp (-1) ≤ x)
    (hx0 : x ≤ 0) : ContinuousAt (lambertBranchValue 0) x := by
  set C : Set ℂ := {w | -1 ≤ w.re} ∩ {w | w ∈ slitPlane → lambertLogMap w ∈ {ζ | |ζ.im| ≤ π}}
  have hC : IsClosed C := (isClosed_le continuous_const Complex.continuous_re).inter
    (isClosed_setOf_mem_slitPlane_imp
      (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const))
  refine tendsto_of_unique_mul_exp_root hC (R := Real.exp 1 * (‖(x : ℂ)‖ + 1)) le_rfl ?_ ?_
  · filter_upwards [Metric.ball_mem_nhds (x : ℂ) one_pos] with z hz
    obtain ⟨h1, h2⟩ := lambertBranchValue_zero_bounds z
    refine ⟨⟨h1, h2⟩, ?_, lambertBranchValue_mul_exp 0 z (Or.inr rfl)⟩
    refine (norm_lambertBranchValue_zero_le z).trans ?_
    have : ‖z‖ ≤ ‖(x : ℂ)‖ + 1 := by
      have := norm_le_norm_add_norm_sub' z (x : ℂ)
      rw [Metric.mem_ball, dist_eq_norm] at hz; linarith
    gcongr
  · rintro w ⟨hw1, hw2⟩ hwx
    by_cases hS : w ∈ slitPlane
    · exfalso
      have hx0' : x < 0 := by
        rcases hx0.lt_or_eq with h | h
        · exact h
        · subst h
          have : w = 0 := by simpa using hwx
          exact absurd this (slitPlane_ne_zero hS)
      obtain ⟨hre, n, hn⟩ := lambertLogMap_of_mul_exp_eq hS hx hx0' hwx
      have hb := hw2 hS
      simp only [mem_ofPred_eq, hn, abs_le] at hb
      have hπ := Real.pi_pos
      have hn1 : (n : ℝ) ≤ 0 := by nlinarith
      have hn2 : (-1 : ℝ) ≤ n := by nlinarith
      have : |(lambertLogMap w).im| = π := by
        have a : n ≤ 0 := by exact_mod_cast hn1
        have b : -1 ≤ n := by exact_mod_cast hn2
        rcases (show n = 0 ∨ n = -1 by omega) with rfl | rfl
        · simp [hn, abs_of_pos hπ]
        · rw [hn]; push_cast; rw [abs_of_neg (by linarith)]; ring
      linarith [neg_one_lt_lambertLogMap_re hS this]
    · rw [mem_slitPlane_iff] at hS; simp only [not_or, not_lt, not_not] at hS
      have hw : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [hS.2])
      rw [hw, ← ofReal_exp, ← ofReal_mul] at hwx
      have hwx' : w.re * Real.exp w.re = x := by exact_mod_cast hwx
      rcases hx0.lt_or_eq with hx0' | hx0'
      · rw [(lambertBranchValue_zero_ofReal hx hx0').1, hw]
        obtain ⟨hu1, hu2⟩ := lambertRealUpper_spec hx hx0'.le
        congr 1
        exact strictMonoOn_mul_exp_Ici.injOn (mem_Ici.mpr hw1) (mem_Ici.mpr hu1)
          (hwx'.trans hu2.symm)
      · subst hx0'
        rw [hw]; simp [lambertBranchValue]
        rcases mul_eq_zero.mp hwx' with h | h
        · exact h
        · exact absurd h (Real.exp_pos _).ne'

/-- Upper boundary limit of the `-1` branch on `[-1/e, 0)`. -/
lemma tendsto_lambertBranchValue_neg_one_ofReal {x : ℝ} (hx : -Real.exp (-1) ≤ x)
    (hx0 : x < 0) :
    Tendsto (lambertBranchValue (-1)) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
      (𝓝 (lambertBranchValue (-1) x)) := by
  set C : Set ℂ := {w | 1 ≤ ‖w‖} ∩
    {w | w ∈ slitPlane → lambertLogMap w ∈ {ζ | -(2 * π) ≤ ζ.im ∧ ζ.im ≤ -π}}
  have hC : IsClosed C := (isClosed_le continuous_const continuous_norm).inter
    (isClosed_setOf_mem_slitPlane_imp ((isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_le Complex.continuous_im continuous_const)))
  have hlog : Tendsto Complex.log (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (Complex.log x)) :=
    ((continuousWithinAt_log_of_re_neg_of_im_zero (by simpa using hx0) (by simp)).mono
      (ofPred_subset_ofPred.mpr fun z hz => le_of_lt hz)).tendsto
  refine tendsto_of_unique_mul_exp_root hC
    (R := 2 * (‖Complex.log x‖ + 1 + 2 * π + π)) nhdsWithin_le_nhds ?_ ?_
  · filter_upwards [self_mem_nhdsWithin, hlog.eventually (Metric.ball_mem_nhds _ one_pos)]
      with z hz hzl
    have hz0 : z ≠ 0 := by rintro rfl; simp at hz
    have hzS : z ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inr (ne_of_gt hz))
    obtain ⟨h1, h2⟩ := lambertBranchValue_neg_one_bounds (le_of_lt hz) hz0
    refine ⟨⟨h1, h2⟩, ?_, lambertBranchValue_mul_exp (-1) z (Or.inl hz0)⟩
    refine (norm_le_of_lambertLogMap _).trans ?_
    rw [lambertBranchValue_of_mem_slitPlane _ hzS,
      (lambertLogMapInv_spec (log_add_mem_lambertOmegaDomain _ hzS)).2]
    have hl : ‖Complex.log z‖ ≤ ‖Complex.log x‖ + 1 := by
      have := norm_le_norm_add_norm_sub' (Complex.log z) (Complex.log x)
      rw [dist_eq_norm] at hzl; linarith
    have hc : ‖2 * (π : ℂ) * I * ((-1 : ℤ) : ℂ)‖ = 2 * π := by
      simp [abs_of_pos Real.pi_pos]
    have := norm_add_le (Complex.log z) (2 * (π : ℂ) * I * ((-1 : ℤ) : ℂ))
    rw [hc] at this
    linarith
  · rintro w ⟨hw1, hw2⟩ hwx
    by_cases hS : w ∈ slitPlane
    · exfalso
      obtain ⟨hre, n, hn⟩ := lambertLogMap_of_mul_exp_eq hS hx hx0 hwx
      have hb := hw2 hS
      simp only [mem_ofPred_eq, hn] at hb
      have hπ := Real.pi_pos
      have hn1 : (n : ℝ) ≤ -1 := by nlinarith
      have hn2 : (-3 / 2 : ℝ) ≤ n := by nlinarith
      have : n = -1 := by
        have a : n ≤ -1 := by exact_mod_cast hn1
        have b : -2 < n := by
          have : (-2 : ℝ) < n := by linarith
          exact_mod_cast this
        omega
      subst this
      have habs : |(lambertLogMap w).im| = π := by
        rw [hn]; push_cast; rw [abs_of_neg (by linarith)]; ring
      linarith [neg_one_lt_lambertLogMap_re hS habs]
    · rw [mem_slitPlane_iff] at hS; simp only [not_or, not_lt, not_not] at hS
      have hw : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [hS.2])
      rw [hw, ← ofReal_exp, ← ofReal_mul] at hwx
      have hwx' : w.re * Real.exp w.re = x := by exact_mod_cast hwx
      have hw1' : w.re ≤ -1 := by
        have h' : 1 ≤ ‖w‖ := hw1
        rw [hw, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hS.1] at h'; linarith
      rw [(lambertBranchValue_zero_ofReal hx hx0).2, hw]
      obtain ⟨hl1, hl2⟩ := lambertRealLower_spec hx hx0
      congr 1
      exact strictAntiOn_mul_exp_Iic.injOn (mem_Iic.mpr hw1') (mem_Iic.mpr hl1)
        (hwx'.trans hl2.symm)

/-! ### Upper boundary values, holomorphy and the basepoint -/

/-- Every branch is continuous from the upper side at the negative real axis. -/
lemma tendsto_lambertBranchValue_upper (k : ℤ) {x : ℝ} (hx : x < 0) :
    Tendsto (lambertBranchValue k) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
      (𝓝 (lambertBranchValue k x)) := by
  have hne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne
  by_cases hΩ : Complex.log x + 2 * π * I * k ∈ lambertOmegaDomain
  · rw [lambertBranchValue, ite_eq_right hne, ite_eq_left hΩ]
    have hlog : Tendsto (fun z => Complex.log z + 2 * π * I * k)
        (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (Complex.log x + 2 * π * I * k)) :=
      (((continuousWithinAt_log_of_re_neg_of_im_zero (by simpa using hx) (by simp)).mono
        (ofPred_subset_ofPred.mpr fun z hz => le_of_lt hz)).tendsto).add tendsto_const_nhds
    refine ((continuousAt_lambertLogMapInv hΩ).tendsto.comp hlog).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (lambertBranchValue_of_mem_slitPlane k
      (mem_slitPlane_iff.mpr (Or.inr (ne_of_gt hz)))).symm
  · obtain ⟨-, -, hle, hk⟩ := of_log_add_not_mem_lambertOmegaDomain hne hΩ
    simp only [ofReal_re] at hle
    rcases hk with rfl | rfl
    · exact (continuousAt_lambertBranchValue_zero_ofReal hle hx.le).tendsto.mono_left
        nhdsWithin_le_nhds
    · exact tendsto_lambertBranchValue_neg_one_ofReal hle hx

/-- Every branch is holomorphic on the slit plane. -/
lemma differentiableAt_lambertBranchValue_of_mem_slitPlane (k : ℤ) {z : ℂ}
    (hz : z ∈ slitPlane) : DifferentiableAt ℂ (lambertBranchValue k) z := by
  have hev : lambertBranchValue k =ᶠ[𝓝 z]
      fun u => lambertLogMapInv (Complex.log u + 2 * π * I * k) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with u hu
    exact lambertBranchValue_of_mem_slitPlane k hu
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  exact (differentiableAt_lambertLogMapInv (log_add_mem_lambertOmegaDomain k hz)).comp z
    ((differentiableAt_log hz).add_const _)

/-- The principal branch is holomorphic off `(-∞, -1/e]`. -/
lemma differentiableAt_lambertBranchValue_zero {z : ℂ}
    (hz : -Real.exp (-1) < z.re ∨ z.im ≠ 0) : DifferentiableAt ℂ (lambertBranchValue 0) z := by
  by_cases hS : z ∈ slitPlane
  · exact differentiableAt_lambertBranchValue_of_mem_slitPlane 0 hS
  rw [mem_slitPlane_iff] at hS; simp only [not_or, not_lt, not_not] at hS
  have hre : -Real.exp (-1) < z.re := hz.resolve_right (not_not.mpr hS.2)
  have hzx : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hS.2])
  have hc : ContinuousAt (lambertBranchValue 0) z := by
    rw [hzx]; exact continuousAt_lambertBranchValue_zero_ofReal hre.le hS.1
  set W := lambertBranchValue 0 z
  have hW : W ≠ -1 := by
    intro h
    have he := lambertBranchValue_mul_exp 0 z (Or.inr rfl)
    rw [show lambertBranchValue 0 z = W from rfl, h] at he
    have : (-1 * Complex.exp (-1)).re = z.re := congrArg Complex.re he
    rw [show (-1 : ℂ) * Complex.exp (-1) = ((-Real.exp (-1) : ℝ) : ℂ) by push_cast; ring,
      ofReal_re] at this
    linarith
  have hf : HasDerivAt (fun w : ℂ => w * Complex.exp w)
      (1 * Complex.exp W + W * Complex.exp W) W :=
    (hasDerivAt_id W).mul (Complex.hasDerivAt_exp W)
  have hf' : 1 * Complex.exp W + W * Complex.exp W ≠ 0 := by
    rw [← add_mul]
    exact mul_ne_zero (fun h => hW (by linear_combination h)) (Complex.exp_ne_zero _)
  exact (hf.of_local_left_inverse hc hf'
    (Eventually.of_forall fun y => lambertBranchValue_mul_exp 0 y (Or.inr rfl))).differentiableAt

/-- The basepoint values `W_k(1)`. -/
lemma lambertBranchValue_one (k : ℤ) :
    (k = 0 → (lambertBranchValue k 1).im = 0 ∧ 0 ≤ (lambertBranchValue k 1).re) ∧
    (0 < k → (2 * k - 1 : ℝ) * π < (lambertBranchValue k 1).im ∧
      (lambertBranchValue k 1).im < 2 * k * π) ∧
    (k < 0 → 2 * k * π < (lambertBranchValue k 1).im ∧
      (lambertBranchValue k 1).im < (2 * k + 1 : ℝ) * π) := by
  have h1 : (1 : ℂ) ∈ slitPlane := by simp [mem_slitPlane_iff]
  rw [lambertBranchValue_of_mem_slitPlane k h1]
  obtain ⟨hS, hg⟩ := lambertLogMapInv_spec (log_add_mem_lambertOmegaDomain k h1)
  set w := lambertLogMapInv (Complex.log 1 + 2 * π * I * k)
  have him : w.im + arg w = 2 * π * k := by
    rw [← lambertLogMap_im, hg, im_log_add_two_pi_mul_I_mul]; simp
  obtain ⟨p1, n1, z1⟩ := lambertLogMap_im_sign hS
  have hπ := Real.pi_pos
  refine ⟨fun hk => ?_, fun hk => ?_, fun hk => ?_⟩
  · subst hk
    have hw0 : w.im = 0 := by
      rcases lt_trichotomy w.im 0 with h | h | h
      · have := n1 h; rw [lambertLogMap_im] at this; simp at him; linarith
      · exact h
      · have := p1 h; rw [lambertLogMap_im] at this; simp at him; linarith
    exact ⟨hw0, (z1 hw0).2.le⟩
  · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hpos : 0 < w.im := by
      rcases lt_trichotomy w.im 0 with h | h | h
      · have := n1 h; rw [lambertLogMap_im] at this; nlinarith
      · have := (z1 h).1; rw [lambertLogMap_im] at this; nlinarith
      · exact h
    have ha0 : 0 < arg w := lt_of_le_of_ne (arg_nonneg_iff.mpr hpos.le) (by
      intro h; have := arg_eq_zero_iff.mp h.symm; linarith [this.2])
    have ha1 : arg w < π := arg_lt_pi_iff.mpr (Or.inr hpos.ne')
    constructor <;> nlinarith
  · have hk' : (k : ℝ) ≤ -1 := by
      have : k ≤ -1 := by omega
      exact_mod_cast this
    have hneg : w.im < 0 := by
      rcases lt_trichotomy w.im 0 with h | h | h
      · exact h
      · have := (z1 h).1; rw [lambertLogMap_im] at this; nlinarith
      · have := p1 h; rw [lambertLogMap_im] at this; nlinarith
    have ha0 : arg w < 0 := arg_neg_iff.mpr hneg
    have ha1 := neg_pi_lt_arg w
    constructor <;> nlinarith

/-- The `-1` branch inverts `y e^y` on `(-∞, -1]`. -/
lemma lambertBranchValue_neg_one_mul_exp {x : ℝ} (hx : x ≤ -1) :
    lambertBranchValue (-1) ((x * Real.exp x : ℝ) : ℂ) = x := by
  have hlo : -Real.exp (-1) ≤ x * Real.exp x := by
    have := strictAntiOn_mul_exp_Iic.antitoneOn (mem_Iic.mpr hx) (mem_Iic.mpr le_rfl) hx
    simpa using this
  have hneg : x * Real.exp x < 0 := mul_neg_of_neg_of_pos (by linarith) (Real.exp_pos x)
  rw [(lambertBranchValue_zero_ofReal hlo hneg).2]
  obtain ⟨h1, h2⟩ := lambertRealLower_spec hlo hneg
  congr 1
  exact strictAntiOn_mul_exp_Iic.injOn (mem_Iic.mpr h1) (mem_Iic.mpr hx) h2

/-- Wright's omega relation for the branch with the unwinding index of `z`: either
`W + log W = z` with `W` off the logarithm cut, or `W` is negative real and `|Im z| = π`. -/
lemma lambertBranchValue_unwinding (z : ℂ) :
    (lambertBranchValue ⌈(z.im - π) / (2 * π)⌉ (Complex.exp z) ∈ slitPlane ∧
      lambertLogMap (lambertBranchValue ⌈(z.im - π) / (2 * π)⌉ (Complex.exp z)) = z) ∨
    ((lambertBranchValue ⌈(z.im - π) / (2 * π)⌉ (Complex.exp z)).im = 0 ∧
      (lambertBranchValue ⌈(z.im - π) / (2 * π)⌉ (Complex.exp z)).re < 0 ∧ |z.im| = π) := by
  set K := ⌈(z.im - π) / (2 * π)⌉
  have hπ := Real.pi_pos
  have hK1 : (z.im - π) / (2 * π) ≤ K := Int.le_ceil _
  have hK2 : (K : ℝ) < (z.im - π) / (2 * π) + 1 := Int.ceil_lt_add_one _
  rw [div_le_iff₀ (by positivity)] at hK1
  rw [← sub_lt_iff_lt_add, lt_div_iff₀ (by positivity)] at hK2
  have hlog : Complex.log (Complex.exp z) + 2 * π * I * K = z := by
    have hz' : Complex.exp z = Complex.exp (z - 2 * π * I * K) := by
      rw [Complex.exp_sub, show 2 * (π : ℂ) * I * K = K * (2 * π * I) by ring,
        exp_int_mul_two_pi_mul_I, div_one]
    rw [hz', Complex.log_exp]
    · ring
    · simp; nlinarith
    · simp; nlinarith
  have hne : Complex.exp z ≠ 0 := Complex.exp_ne_zero z
  by_cases hΩ : Complex.log (Complex.exp z) + 2 * π * I * K ∈ lambertOmegaDomain
  · left
    rw [lambertBranchValue, ite_eq_right hne, ite_eq_left hΩ]
    have := lambertLogMapInv_spec hΩ
    rw [hlog] at this ⊢
    exact this
  · right
    have hΩ' := hΩ
    obtain ⟨-, hre, hle, -⟩ := of_log_add_not_mem_lambertOmegaDomain hne hΩ
    simp only [lambertOmegaDomain, mem_ofPred_eq, not_or, not_not, hlog] at hΩ'
    rw [lambertBranchValue, ite_eq_right hne, ite_eq_right hΩ]
    split_ifs
    · obtain ⟨-, h2⟩ := lambertRealUpper_spec hle hre.le
      refine ⟨by simp, ?_, hΩ'.2⟩
      simp only [ofReal_re]
      by_contra hh
      have : 0 ≤ lambertRealUpper (Complex.exp z).re * Real.exp (lambertRealUpper
        (Complex.exp z).re) := mul_nonneg (not_lt.mp hh) (Real.exp_pos _).le
      linarith
    · obtain ⟨h1, -⟩ := lambertRealLower_spec hle hre
      exact ⟨by simp, by simp; linarith, hΩ'.2⟩

/-- Outside the unit disc the branch values are given by the inverse of `w + log w`. -/
lemma lambertBranchValue_of_one_lt_norm (k : ℤ) {z : ℂ} (hz : 1 < ‖z‖) :
    lambertBranchValue k z = lambertLogMapInv (Complex.log z + 2 * π * I * k) := by
  have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz
  have hΩ : Complex.log z + 2 * π * I * k ∈ lambertOmegaDomain := by
    left; rw [re_log_add_two_pi_mul_I_mul]; linarith [Real.log_pos hz]
  rw [lambertBranchValue, ite_eq_right hz0, ite_eq_left hΩ]

/-- `log ζ - log ω(ζ) → 0` as `Re ζ → ∞`, where `ω` inverts `w + log w`. -/
lemma tendsto_log_sub_log_lambertLogMapInv :
    Tendsto (fun ζ => Complex.log ζ - Complex.log (lambertLogMapInv ζ))
      (comap Complex.re atTop) (𝓝 0) := by
  set l := comap Complex.re atTop
  have hre : ∀ᶠ ζ in l, 1 ≤ ζ.re := (tendsto_comap.eventually (eventually_ge_atTop 1))
  have hnorm : Tendsto (fun ζ : ℂ => ‖ζ‖) l atTop :=
    tendsto_atTop_mono (fun ζ => Complex.re_le_norm ζ) tendsto_comap
  set u : ℂ → ℂ := fun ζ => lambertLogMapInv ζ / ζ
  -- the basic estimates for `Re ζ ≥ 1`
  have key : ∀ ζ : ℂ, 1 ≤ ζ.re → ζ ≠ 0 ∧ lambertLogMapInv ζ ∈ slitPlane ∧
      lambertLogMapInv ζ = ζ - Complex.log (lambertLogMapInv ζ) ∧
      ‖u ζ - 1‖ ≤ (8 * Real.sqrt ‖ζ‖ + π) / ‖ζ‖ := by
    intro ζ hζ
    have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ; linarith
    have hΩ : ζ ∈ lambertOmegaDomain := Or.inl (by linarith)
    obtain ⟨hS, hg⟩ := lambertLogMapInv_spec hΩ
    set W := lambertLogMapInv ζ
    have hWe : W = ζ - Complex.log W := by rw [← hg, lambertLogMap]; ring
    have hW1 : 1 ≤ ‖W‖ := by
      by_contra h
      have h1 : Real.log ‖W‖ < 0 :=
        Real.log_neg (norm_pos_iff.mpr (slitPlane_ne_zero hS)) (not_le.mp h)
      have h2 := Complex.re_le_norm W
      have := congrArg Complex.re hg
      rw [lambertLogMap_re] at this
      linarith
    have hn1 : 1 ≤ ‖ζ‖ := hζ.trans (Complex.re_le_norm ζ)
    have hWn := norm_le_of_lambertLogMap W
    rw [hg] at hWn
    have hlog : ‖Complex.log W‖ ≤ Real.log ‖W‖ + π := by
      refine (norm_le_abs_re_add_abs_im _).trans ?_
      rw [Complex.log_re, Complex.log_im, abs_of_nonneg (Real.log_nonneg hW1)]
      gcongr; exact abs_arg_le_pi W
    have hlog2 : Real.log ‖W‖ ≤ 8 * Real.sqrt ‖ζ‖ := by
      have h4 : ‖W‖ ≤ 16 * ‖ζ‖ := by nlinarith [Real.pi_le_four]
      have hs : Real.log ‖W‖ ≤ 2 * Real.sqrt ‖W‖ := by
        have hpos : 0 < Real.sqrt ‖W‖ := Real.sqrt_pos.mpr (by linarith)
        have := Real.log_le_sub_one_of_pos hpos
        rw [Real.log_sqrt (by linarith)] at this
        linarith
      have hsq : Real.sqrt ‖W‖ ≤ 4 * Real.sqrt ‖ζ‖ := by
        rw [show 4 * Real.sqrt ‖ζ‖ = Real.sqrt (16 * ‖ζ‖) by
          rw [Real.sqrt_mul (by norm_num), show (16 : ℝ) = 4 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt h4
      linarith
    refine ⟨hζ0, hS, hWe, ?_⟩
    have hu : u ζ - 1 = -Complex.log W / ζ := by
      have h' : W - ζ = -Complex.log W := by rw [← hg, lambertLogMap]; ring
      simp only [u]; rw [div_sub_one hζ0, h']
    rw [hu, norm_div, norm_neg, div_le_div_iff_of_pos_right (by linarith)]
    linarith
  -- `u → 1`
  have hB : Tendsto (fun ζ : ℂ => (8 * Real.sqrt ‖ζ‖ + π) / ‖ζ‖) l (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => 8 * (Real.sqrt t)⁻¹ + π * t⁻¹) atTop (𝓝 0) := by
      have a := (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul 8
      have b := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul π
      simpa using a.add b
    refine (h1.comp hnorm).congr' ?_
    filter_upwards [hnorm.eventually (eventually_gt_atTop 0)] with ζ hζ
    simp only [Function.comp]
    have hs : Real.sqrt ‖ζ‖ ≠ 0 := (Real.sqrt_pos.mpr hζ).ne'
    field_simp
    linear_combination (-8) * Real.mul_self_sqrt hζ.le
  have hu1 : Tendsto u l (𝓝 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hB
    filter_upwards [hre] with ζ hζ
    exact (key ζ hζ).2.2.2
  have hlogu : Tendsto (fun ζ => -Complex.log (u ζ)) l (𝓝 0) := by
    have := ((continuousAt_clog (by simp [mem_slitPlane_iff])).tendsto.comp hu1).neg
    simpa using this
  refine hlogu.congr' ?_
  have hure : ∀ᶠ ζ in l, 0 < (u ζ).re :=
    (Complex.continuous_re.tendsto 1).comp hu1 |>.eventually (eventually_gt_nhds (by simp))
  filter_upwards [hre, hure] with ζ hζ hu
  obtain ⟨hζ0, hS, -, -⟩ := key ζ hζ
  have hu0 : u ζ ≠ 0 := by rintro h; rw [h] at hu; simp at hu
  have hW : lambertLogMapInv ζ = ζ * u ζ := by simp only [u]; field_simp
  have ha1 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by linarith) : 0 < ζ.re ∨ ζ = 0)
  have ha2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hu : 0 < (u ζ).re ∨ u ζ = 0)
  rw [hW, log_mul hζ0 hu0]
  · ring
  · rw [abs_lt] at ha1 ha2
    constructor <;> linarith [Real.pi_pos]

/-- The distance between `ω(ζ)` and `ζ` grows at most like `√‖ζ‖`, once both have norm at
least `1`. -/
lemma norm_lambertLogMapInv_sub_le {ζ : ℂ} (hζ : ζ ∈ lambertOmegaDomain)
    (hW1 : 1 ≤ ‖lambertLogMapInv ζ‖) (hn1 : 1 ≤ ‖ζ‖) :
    ‖lambertLogMapInv ζ - ζ‖ ≤ 8 * Real.sqrt ‖ζ‖ + π := by
  obtain ⟨hS, hg⟩ := lambertLogMapInv_spec hζ
  set W := lambertLogMapInv ζ
  have h' : W - ζ = -Complex.log W := by rw [← hg, lambertLogMap]; ring
  have hWn := norm_le_of_lambertLogMap W
  rw [hg] at hWn
  have hlog : ‖Complex.log W‖ ≤ Real.log ‖W‖ + π := by
    refine (norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.log_re, Complex.log_im, abs_of_nonneg (Real.log_nonneg hW1)]
    gcongr; exact abs_arg_le_pi W
  have h4 : ‖W‖ ≤ 16 * ‖ζ‖ := by nlinarith [Real.pi_le_four]
  have hs : Real.log ‖W‖ ≤ 2 * Real.sqrt ‖W‖ := by
    have hpos : 0 < Real.sqrt ‖W‖ := Real.sqrt_pos.mpr (by linarith)
    have := Real.log_le_sub_one_of_pos hpos
    rw [Real.log_sqrt (by linarith)] at this
    linarith
  have hsq : Real.sqrt ‖W‖ ≤ 4 * Real.sqrt ‖ζ‖ := by
    rw [show 4 * Real.sqrt ‖ζ‖ = Real.sqrt (16 * ‖ζ‖) by
      rw [Real.sqrt_mul (by norm_num), show (16 : ℝ) = 4 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt h4
  rw [h', norm_neg]
  linarith

end DLMF.Elementary
