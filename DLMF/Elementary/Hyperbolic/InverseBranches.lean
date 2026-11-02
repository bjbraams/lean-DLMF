/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elementary.Hyperbolic.InverseCalculus
public import DLMFMathlib.Analysis.Complex.Sqrt

/-!
# Branches and cut values of inverse hyperbolic functions

This file proves the logarithmic forms and cut-side limits of the principal inverse hyperbolic
functions, the full inverse families, and the power series of the inverse sine and cosine
(DLMF §§4.37–4.38).

## Main definitions

* `hyperbolicCentral`: the central binomial coefficient divided by `4^n`.

## Main results

* `arccosh_neg`, `arcsech_neg`: the sign relations DLMF 4.37.11 and 4.37.14, corrected.
* `arcsinh_log`, `arccosh_log`, `arccosh_log_half`, `arctanh_log`: logarithmic forms
  (DLMF 4.37.16, 4.37.19, 4.37.21, 4.37.24).
* `arcsinh_upper_cut`, `arcsinh_lower_cut`, `arccosh_inner_cut`, `arccosh_outer_cut`,
  `arctanh_cut`: cut-side values (DLMF 4.37.17–4.37.25).
* `arccosh_imaginary`: `arccosh` on the imaginary axis (DLMF 4.37.20).
* `sinh_inverse_family`, `cosh_inverse_family`, `tanh_inverse_family`: all solutions of
  `sinh w = z`, `cosh w = z`, `tanh w = z` (DLMF 4.37.26–4.37.31).
* `arcsech_arccoth_interrelation`: the interrelation example of DLMF §4.37(vi).
* `hasSum_arcsinh`, `hasSum_arcsinh_large`: series for `arcsinh` (DLMF 4.38.1–4.38.2).
* `hasSum_arccosh_large`, `hasSum_arccosh_near_one`: series for `arccosh`
  (DLMF 4.38.3–4.38.4).

## Implementation notes

DLMF 4.37.11 with the printed sign pairing contradicts 4.37.20 at `z = ±i`; the principal-branch
sign relation is stated in corrected form.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory

open scoped Real Topology

namespace DLMF.Elementary

/-- Characterization of the principal square root by a root with positive real part. -/
private lemma complexSqrt_eq_of_sq_of_re_pos {a w : ℂ} (hw : w^2 = a) (hre : 0 < w.re) :
    Complex.sqrt a = w := by
  have h1 := Trigonometric.complexSqrt_sq a
  have h : (Complex.sqrt a - w)*(Complex.sqrt a + w) = 0 := by linear_combination h1 - hw
  rcases mul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have hr : 0 ≤ (Complex.sqrt a).re := by
      rw [Complex.sqrt, Complex.cpow_inv_two_re]; positivity
    have : (Complex.sqrt a).re = -w.re := by
      have := congrArg Complex.re h; simp at this; linarith
    linarith

/-- The principal square root of `-w` for `w` in the upper half-plane. -/
private lemma complexSqrt_neg_of_im_pos {w : ℂ} (h : 0 < w.im) :
    Complex.sqrt (-w) = -I*Complex.sqrt w := by
  apply complexSqrt_eq_of_sq_of_re_pos
  · rw [mul_pow, Trigonometric.complexSqrt_sq]; simp
  · have him : (Complex.sqrt w).im = Real.sqrt ((‖w‖ - w.re)/2) := by
      rw [Complex.sqrt]; exact Complex.cpow_inv_two_im_eq_sqrt h.le
    have hlt : w.re < ‖w‖ := lt_of_le_of_lt (le_abs_self _) (Complex.abs_re_lt_norm.mpr h.ne')
    simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul,
      one_mul, zero_sub, neg_neg, him]
    exact Real.sqrt_pos.mpr (by linarith)

/-- The principal square root of `-w` for `w` in the lower half-plane. -/
private lemma complexSqrt_neg_of_im_neg {w : ℂ} (h : w.im < 0) :
    Complex.sqrt (-w) = I*Complex.sqrt w := by
  apply complexSqrt_eq_of_sq_of_re_pos
  · rw [mul_pow, Trigonometric.complexSqrt_sq]; simp
  · have him : (Complex.sqrt w).im = -Real.sqrt ((‖w‖ - w.re)/2) := by
      rw [Complex.sqrt]; exact Complex.cpow_inv_two_im_eq_neg_sqrt h
    have hlt : w.re < ‖w‖ := lt_of_le_of_lt (le_abs_self _) (Complex.abs_re_lt_norm.mpr h.ne)
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
        zero_sub, him, neg_neg]
    exact Real.sqrt_pos.mpr (by linarith)

/-- The principal logarithm of `-u` for `u` in the upper half-plane. -/
private lemma complexLog_neg_of_im_pos {u : ℂ} (h : 0 < u.im) :
    Complex.log (-u) = Complex.log u - π*I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_sub_pi_of_im_pos h]

/-- The principal logarithm of `-u` for `u` in the lower half-plane. -/
private lemma complexLog_neg_of_im_neg {u : ℂ} (h : u.im < 0) :
    Complex.log (-u) = Complex.log u + π*I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_add_pi_of_im_neg h]

/-- Imaginary part of a principal square root has the sign of the imaginary part. -/
private lemma complexSqrt_im_nonneg {w : ℂ} (h : 0 ≤ w.im) : 0 ≤ (Complex.sqrt w).im := by
  rw [Complex.sqrt, Complex.cpow_inv_two_im_eq_sqrt h]; exact Real.sqrt_nonneg _

/-- Imaginary part of a principal square root in the lower half-plane. -/
private lemma complexSqrt_im_nonpos {w : ℂ} (h : w.im < 0) : (Complex.sqrt w).im ≤ 0 := by
  rw [Complex.sqrt, Complex.cpow_inv_two_im_eq_neg_sqrt h]
  exact neg_nonpos.mpr (Real.sqrt_nonneg _)

/-- Real part of a principal square root is nonnegative. -/
private lemma complexSqrt_re_nonneg (w : ℂ) : 0 ≤ (Complex.sqrt w).re := by
  rw [Complex.sqrt, Complex.cpow_inv_two_re]; exact Real.sqrt_nonneg _

/-- Corrected principal-branch sign: E20 at z=±i contradicts the printed E11 sign pairing. -/
@[dlmf 4.37.E11]
theorem arccosh_neg {z : ℂ} (hz : z.im≠0) :
    arccosh (-z)=arccosh z-(if 0<z.im then 1 else -1)*π*I := by
  have hI : (I:ℂ)^2 = -1 := by simp
  have e1 : -z-1 = -(z+1) := by ring
  have e2 : -z+1 = -(z-1) := by ring
  unfold arccosh
  rw [e1, e2]
  rcases lt_or_gt_of_ne hz with hn | hp
  · have h1 : (z+1).im < 0 := by simpa using hn
    have h2 : (z-1).im < 0 := by simpa using hn
    rw [complexSqrt_neg_of_im_neg h1, complexSqrt_neg_of_im_neg h2]
    simp only [not_lt.mpr hn.le, ↓reduceIte]
    have hu : (z + Complex.sqrt (z-1)*Complex.sqrt (z+1)).im < 0 := by
      have a1 := complexSqrt_re_nonneg (z-1)
      have a2 := complexSqrt_re_nonneg (z+1)
      have b1 := complexSqrt_im_nonpos h2
      have b2 := complexSqrt_im_nonpos h1
      simp only [Complex.add_im, Complex.mul_im]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos a1 b2, mul_nonpos_of_nonneg_of_nonpos a2 b1]
    have hx : -z + I*Complex.sqrt (z+1)*(I*Complex.sqrt (z-1)) =
        -(z + Complex.sqrt (z-1)*Complex.sqrt (z+1)) := by
      linear_combination Complex.sqrt (z+1)*Complex.sqrt (z-1)*hI
    rw [hx, complexLog_neg_of_im_neg hu]
    ring
  · have h1 : 0 < (z+1).im := by simpa using hp
    have h2 : 0 < (z-1).im := by simpa using hp
    rw [complexSqrt_neg_of_im_pos h1, complexSqrt_neg_of_im_pos h2]
    simp only [hp, ↓reduceIte]
    have hu : 0 < (z + Complex.sqrt (z-1)*Complex.sqrt (z+1)).im := by
      have a1 := complexSqrt_re_nonneg (z-1)
      have a2 := complexSqrt_re_nonneg (z+1)
      have b1 := complexSqrt_im_nonneg h2.le
      have b2 := complexSqrt_im_nonneg h1.le
      simp only [Complex.add_im, Complex.mul_im]
      nlinarith [mul_nonneg a1 b2, mul_nonneg a2 b1]
    have hx : -z + -I*Complex.sqrt (z+1)*(-I*Complex.sqrt (z-1)) =
        -(z + Complex.sqrt (z-1)*Complex.sqrt (z+1)) := by
      linear_combination Complex.sqrt (z+1)*Complex.sqrt (z-1)*hI
    rw [hx, complexLog_neg_of_im_pos hu]
    ring

/-- The reciprocal version of the corrected principal arccosh sign relation. -/
@[dlmf 4.37.E14]
theorem arcsech_neg {z : ℂ} (hz : z.im≠0) :
    arcsech (-z)=arcsech z+(if 0<z.im then 1 else -1)*π*I := by
  have hz0 : z ≠ 0 := fun h => hz (by simp [h])
  have hn : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz0
  have him : (z⁻¹).im = -z.im / Complex.normSq z := by rw [Complex.inv_im]
  have hi : (z⁻¹).im ≠ 0 := by rw [him]; exact div_ne_zero (neg_ne_zero.mpr hz) hn.ne'
  rw [arcsech, arcsech, inv_neg, arccosh_neg hi]
  rcases lt_or_gt_of_ne hz with h | h
  · have : 0 < (z⁻¹).im := by rw [him]; exact div_pos (by linarith) hn
    simp only [this, not_lt.mpr h.le, ↓reduceIte]; ring
  · have : ¬ 0 < (z⁻¹).im := by rw [him];
                                exact not_lt.mpr (div_nonpos_of_nonpos_of_nonneg
                                  (by linarith) hn.le)
    simp only [this, h, ↓reduceIte]; ring

/-- Identity under the stated parameter and domain assumptions: `arcsinh z=Complex.log
(Complex.sqrt (z^2+1)+z)`. -/
@[dlmf 4.37.E16]
theorem arcsinh_log {z : ℂ} : arcsinh z=Complex.log (Complex.sqrt (z^2+1)+z) := by
  rfl

/-- The principal square root is continuous off the open negative real axis. -/
private lemma continuousAt_complexSqrt {w : ℂ} (h : 0 ≤ w.re ∨ w.im ≠ 0) :
    ContinuousAt Complex.sqrt w := by
  have := Complex.continuousAt_cpow_const_of_re_pos (w := (2⁻¹:ℂ)) h (by norm_num)
  exact this

/-- One-sided limit of the principal square root at the cut, from the upper half-plane. -/
private lemma tendsto_complexSqrt_cut_upper {f : ℝ → ℂ} {l : Filter ℝ} {w₀ : ℂ}
    (hf : Tendsto f l (𝓝 w₀)) (hre : w₀.re ≤ 0) (him : ∀ᶠ ε in l, 0 < (f ε).im) :
    Tendsto (fun ε => Complex.sqrt (f ε)) l (𝓝 (I*Complex.sqrt (-w₀))) := by
  have hc := ((continuousAt_complexSqrt (w := -w₀) (Or.inl (by simp; linarith))).tendsto.comp
    hf.neg).const_mul I
  refine hc.congr' (him.mono fun ε hε => ?_)
  simp only [Function.comp_apply]
  rw [complexSqrt_neg_of_im_pos hε]
  linear_combination (-(Complex.sqrt (f ε))) * (by simp : (I:ℂ)^2 = -1)

/-- One-sided limit of the principal square root at the cut, from the lower half-plane. -/
private lemma tendsto_complexSqrt_cut_lower {f : ℝ → ℂ} {l : Filter ℝ} {w₀ : ℂ}
    (hf : Tendsto f l (𝓝 w₀)) (hre : w₀.re ≤ 0) (him : ∀ᶠ ε in l, (f ε).im < 0) :
    Tendsto (fun ε => Complex.sqrt (f ε)) l (𝓝 (-I*Complex.sqrt (-w₀))) := by
  have hc := ((continuousAt_complexSqrt (w := -w₀) (Or.inl (by simp; linarith))).tendsto.comp
    hf.neg).const_mul (-I)
  refine hc.congr' (him.mono fun ε hε => ?_)
  simp only [Function.comp_apply]
  rw [complexSqrt_neg_of_im_neg hε]
  linear_combination (-(Complex.sqrt (f ε))) * (by simp : (I:ℂ)^2 = -1)

/-- Limits of the principal logarithm at a point `i t` of the positive imaginary axis. -/
private lemma tendsto_complexLog_I_mul {g : ℝ → ℂ} {l : Filter ℝ} {t : ℝ} (ht : 0 < t)
    (hg : Tendsto g l (𝓝 (I*t))) :
    Tendsto (fun ε => Complex.log (g ε)) l (𝓝 (Real.log t + π/2*I)) := by
  have hs : I*(t:ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; right; simp [ht.ne']
  have h := (continuousAt_clog hs).tendsto.comp hg
  rw [Complex.log_mul_ofReal _ ht _ Complex.I_ne_zero, Complex.log_I] at h
  exact h

/-- Limits of the principal logarithm at a point `-i t` of the negative imaginary axis. -/
private lemma tendsto_complexLog_neg_I_mul {g : ℝ → ℂ} {l : Filter ℝ} {t : ℝ} (ht : 0 < t)
    (hg : Tendsto g l (𝓝 (-I*t))) :
    Tendsto (fun ε => Complex.log (g ε)) l (𝓝 (Real.log t - π/2*I)) := by
  have hs : -I*(t:ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; right; simp [ht.ne']
  have h := (continuousAt_clog hs).tendsto.comp hg
  rw [Complex.log_mul_ofReal _ ht _ (neg_ne_zero.mpr Complex.I_ne_zero), Complex.log_neg_I] at h
  have e : (Real.log t:ℂ) - π/2*I = Real.log t + -(π/2)*I := by ring
  rw [e]; exact h

/-- The quantity `ε + i y` tends to `i y` along any filter tending to zero. -/
private lemma tendsto_ofReal_add_const {l : Filter ℝ} (hl : l ≤ 𝓝 0) (c : ℂ) :
    Tendsto (fun ε : ℝ => (ε:ℂ)+c) l (𝓝 c) := by
  have : Tendsto (fun ε : ℝ => (ε:ℂ)+c) (𝓝 0) (𝓝 (((0:ℝ):ℂ)+c)) :=
    ((Complex.continuous_ofReal.add continuous_const).tendsto 0)
  simpa using this.mono_left hl

/-- Limit formula in the specified filter: `Tendsto (fun ε : ℝ => arcsinh ((ε:ℂ)+I*y)) (𝓝[>] 0) (𝓝
(π*I/2+(Real.log (Real.sqrt (y^2-1)+y):ℂ))) ∧ Tendsto (fun ε : ℝ => arcsinh ((ε:ℂ)+I*y)) (𝓝[<]
0) (𝓝 (π*I/2-(Real.log (Real.sqrt (y^2-1)+y):ℂ)))`. -/
@[dlmf 4.37.E17]
theorem arcsinh_upper_cut {y : ℝ} (hy : 1≤y) :
    Tendsto (fun ε : ℝ => arcsinh ((ε:ℂ)+I*y)) (𝓝[>] 0)
      (𝓝 (π*I/2+(Real.log (Real.sqrt (y^2-1)+y):ℂ))) ∧
    Tendsto (fun ε : ℝ => arcsinh ((ε:ℂ)+I*y)) (𝓝[<] 0)
      (𝓝 (π*I/2-(Real.log (Real.sqrt (y^2-1)+y):ℂ))) := by
  set r := Real.sqrt (y^2-1) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2 = y^2-1 := Real.sq_sqrt (by nlinarith)
  have hry : r < y := by nlinarith
  have hw : -((I*(y:ℂ))^2+1) = ((y^2-1:ℝ):ℂ) := by
    push_cast; linear_combination -(y:ℂ)^2*(by simp : (I:ℂ)^2 = -1)
  have hsq : Complex.sqrt (-((I*(y:ℂ))^2+1)) = r := by
      rw [hw, Hyperbolic.sqrt_ofReal _ (by nlinarith)]
  have hinv : y - r = (r+y)⁻¹ := eq_inv_of_mul_eq_one_left (by linear_combination -hr2)
  have hz : ∀ {l : Filter ℝ}, l ≤ 𝓝 0 →
      Tendsto (fun ε : ℝ => ((ε:ℂ)+I*y)^2+1) l (𝓝 ((I*(y:ℂ))^2+1)) := fun hl =>
    ((tendsto_ofReal_add_const hl (I*y)).pow 2).add_const 1
  have hw0 : ((I*(y:ℂ))^2+1).re ≤ 0 := by simp [pow_two]; nlinarith
  constructor
  · have him : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < (((ε:ℂ)+I*y)^2+1).im :=
      eventually_mem_nhdsWithin.mono fun ε (hε : 0 < ε) => by
        simp [pow_two]; nlinarith
    have hs := tendsto_complexSqrt_cut_upper (hz nhdsWithin_le_nhds) hw0 him
    rw [hsq] at hs
    have hg := hs.add (tendsto_ofReal_add_const nhdsWithin_le_nhds (I*y))
    have := tendsto_complexLog_I_mul (t := r+y) (by linarith)
        (by convert hg using 2; push_cast; ring)
    have e : (π*I/2+((Real.log (Real.sqrt (y^2-1)+y)):ℂ)) = (Real.log (r+y) + π/2*I) := by
      rw [← hr]; ring
    rw [e]; exact this
  · have him : ∀ᶠ ε in 𝓝[<] (0:ℝ), (((ε:ℂ)+I*y)^2+1).im < 0 :=
      eventually_mem_nhdsWithin.mono fun ε (hε : ε < 0) => by
        simp [pow_two]; nlinarith
    have hs := tendsto_complexSqrt_cut_lower (hz nhdsWithin_le_nhds) hw0 him
    rw [hsq] at hs
    have hg := hs.add (tendsto_ofReal_add_const nhdsWithin_le_nhds (I*y))
    have := tendsto_complexLog_I_mul (t := y-r) (by linarith)
        (by convert hg using 2; push_cast; ring)
    have e : (π*I/2-((Real.log (Real.sqrt (y^2-1)+y)):ℂ)) = (Real.log (y-r) + π/2*I) := by
      rw [← hr, hinv, Real.log_inv]; push_cast; ring
    rw [e]; exact this

/-- Limit formula in the specified filter: `Tendsto (fun ε : ℝ => arcsinh ((ε:ℂ)+I*y)) (𝓝[>] 0) (𝓝
(-π*I/2+(Real.log (Real.sqrt (y^2-1)-y):ℂ))) ∧ Tendsto (fun ε : ℝ => arcsinh ((ε:ℂ)+I*y))
(𝓝[<] 0) (𝓝 (-π*I/2-(Real.log (Real.sqrt (y^2-1)-y):ℂ)))`. -/
@[dlmf 4.37.E18]
theorem arcsinh_lower_cut {y : ℝ} (hy : y≤ -1) :
    Tendsto (fun ε : ℝ => arcsinh ((ε:ℂ)+I*y)) (𝓝[>] 0)
      (𝓝 (-π*I/2+(Real.log (Real.sqrt (y^2-1)-y):ℂ))) ∧
    Tendsto (fun ε : ℝ => arcsinh ((ε:ℂ)+I*y)) (𝓝[<] 0)
      (𝓝 (-π*I/2-(Real.log (Real.sqrt (y^2-1)-y):ℂ))) := by
  set r := Real.sqrt (y^2-1) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2 = y^2-1 := Real.sq_sqrt (by nlinarith)
  have hry : r < -y := by nlinarith
  have hw : -((I*(y:ℂ))^2+1) = ((y^2-1:ℝ):ℂ) := by
    push_cast; linear_combination -(y:ℂ)^2*(by simp : (I:ℂ)^2 = -1)
  have hsq : Complex.sqrt (-((I*(y:ℂ))^2+1)) = r := by
      rw [hw, Hyperbolic.sqrt_ofReal _ (by nlinarith)]
  have hinv : -y - r = (r-y)⁻¹ := eq_inv_of_mul_eq_one_left (by linear_combination -hr2)
  have hz : ∀ {l : Filter ℝ}, l ≤ 𝓝 0 →
      Tendsto (fun ε : ℝ => ((ε:ℂ)+I*y)^2+1) l (𝓝 ((I*(y:ℂ))^2+1)) := fun hl =>
    ((tendsto_ofReal_add_const hl (I*y)).pow 2).add_const 1
  have hw0 : ((I*(y:ℂ))^2+1).re ≤ 0 := by simp [pow_two]; nlinarith
  constructor
  · have him : ∀ᶠ ε in 𝓝[>] (0:ℝ), (((ε:ℂ)+I*y)^2+1).im < 0 :=
      eventually_mem_nhdsWithin.mono fun ε (hε : 0 < ε) => by
        simp [pow_two]; nlinarith
    have hs := tendsto_complexSqrt_cut_lower (hz nhdsWithin_le_nhds) hw0 him
    rw [hsq] at hs
    have hg := hs.add (tendsto_ofReal_add_const nhdsWithin_le_nhds (I*y))
    have := tendsto_complexLog_neg_I_mul (t := r-y) (by linarith)
        (by convert hg using 2; push_cast; ring)
    have e : (-π*I/2+((Real.log (Real.sqrt (y^2-1)-y)):ℂ)) = (Real.log (r-y) - π/2*I) := by
      rw [← hr]; ring
    rw [e]; exact this
  · have him : ∀ᶠ ε in 𝓝[<] (0:ℝ), 0 < (((ε:ℂ)+I*y)^2+1).im :=
      eventually_mem_nhdsWithin.mono fun ε (hε : ε < 0) => by
        simp [pow_two]; nlinarith
    have hs := tendsto_complexSqrt_cut_upper (hz nhdsWithin_le_nhds) hw0 him
    rw [hsq] at hs
    have hg := hs.add (tendsto_ofReal_add_const nhdsWithin_le_nhds (I*y))
    have := tendsto_complexLog_neg_I_mul (t := -y-r) (by linarith)
        (by convert hg using 2; push_cast; ring)
    have e : (-π*I/2-((Real.log (Real.sqrt (y^2-1)-y)):ℂ)) = (Real.log (-y-r) - π/2*I) := by
      rw [← hr, hinv, Real.log_inv]; push_cast; ring
    rw [e]; exact this

/-- The right half of the inverse-cosh domain is star-convex about `2`. -/
private lemma arccoshDomain_right_starConvex :
    StarConvex ℝ (2:ℂ) {z : ℂ | z ∈ arccoshDomain ∧ 0 < z.re} := by
  intro y hy a b ha hb hab
  obtain ⟨hyd, hyr⟩ := hy
  have hre : (a • (2:ℂ) + b • y).re = 2*a + b*y.re := by simp; ring
  have him : (a • (2:ℂ) + b • y).im = b*y.im := by simp
  have hpos : 0 < 2*a + b*y.re := by
    rcases eq_or_lt_of_le hb with hb0 | hb0
    · rw [← hb0]; linarith
    · nlinarith
  refine ⟨?_, by rw [hre]; exact hpos⟩
  rcases hyd with hi | hr
  · rcases eq_or_lt_of_le hb with hb0 | hb0
    · right; rw [hre, ← hb0]; linarith
    · left; rw [him]; exact mul_ne_zero hb0.ne' hi
  · right; rw [hre]
    rcases eq_or_lt_of_le hb with hb0 | hb0
    · rw [← hb0]; linarith
    · nlinarith [mul_pos hb0 (sub_pos.mpr hr)]

/-- On the right half of its domain the factored inverse-cosh root is the principal `√(z²-1)`. -/
private lemma sqrt_sub_one_mul_sqrt_add_one_of_re_pos {z : ℂ} (hz : z ∈ arccoshDomain)
    (hre : 0 < z.re) :
    Complex.sqrt (z-1)*Complex.sqrt (z+1) = Complex.sqrt (z^2-1) := by
  set V := {z : ℂ | z ∈ arccoshDomain ∧ 0 < z.re}
  have hVo : IsOpen V := by
    have : IsOpen arccoshDomain := by
      change IsOpen ({z:ℂ | z.im≠0}∪{z:ℂ | 1<z.re})
      exact (isOpen_ne.preimage Complex.continuous_im).union
        (isOpen_lt continuous_const Complex.continuous_re)
    exact this.inter (isOpen_lt continuous_const Complex.continuous_re)
  have h2V : (2:ℂ) ∈ V := ⟨Or.inr (by norm_num), by norm_num⟩
  have hVc : IsPreconnected V :=
    (arccoshDomain_right_starConvex.isPathConnected h2V).isConnected.isPreconnected
  have hslit : ∀ w ∈ V, w^2-1 ∈ Complex.slitPlane := by
    rintro w ⟨hw, hwr⟩
    rw [Complex.mem_slitPlane_iff]
    by_cases hy : w.im = 0
    · left
      have : 1 < w.re := hw.resolve_left (not_not.mpr hy)
      simp [pow_two, Complex.mul_re, hy]; nlinarith
    · right; simp [pow_two, Complex.mul_im]
      intro h; apply mul_ne_zero (mul_ne_zero two_ne_zero hwr.ne') hy; linear_combination h
  have hr : AnalyticOnNhd ℂ (fun w => Complex.sqrt (w-1)*Complex.sqrt (w+1)) V := by
    apply DifferentiableOn.analyticOnNhd _ hVo
    intro w hw
    obtain ⟨h1, h2⟩ := sub_one_add_one_mem_slitPlane_of_mem_arccoshDomain hw.1
    exact (((Complex.differentiableAt_sqrt h1).comp w (differentiableAt_id.sub_const 1)).mul
      ((Complex.differentiableAt_sqrt h2).comp w
          (differentiableAt_id.add_const 1))).differentiableWithinAt
  have hs : AnalyticOnNhd ℂ (fun w => Complex.sqrt (w^2-1)) V := by
    apply DifferentiableOn.analyticOnNhd _ hVo
    intro w hw
    exact ((Complex.differentiableAt_sqrt (hslit w hw)).comp w
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w^2-1) w)).differentiableWithinAt
  have h1 : Complex.sqrt 1 = 1 := by simp [Complex.sqrt]
  refine eqOn_of_sq_eq_of_analyticOnNhd hVo hVc hr hs ?_ h2V ?_ ?_ z ⟨hz, hre⟩
  · intro w _; rw [mul_pow, Trigonometric.complexSqrt_sq, Trigonometric.complexSqrt_sq,
        Trigonometric.complexSqrt_sq]; ring
  · norm_num [h1]
  · intro h
    have := Trigonometric.complexSqrt_sq ((2:ℂ)^2-1)
    rw [h] at this; norm_num at this

/-- The factored inverse-cosh root is `±√(z²-1)` according to the sign of `Re z`. -/
lemma sqrt_sub_one_mul_sqrt_add_one_eq_sign_mul_sqrt {z : ℂ} (hz : z ∈ arccoshDomain)
    (hre : z.re ≠ 0) :
    Complex.sqrt (z-1)*Complex.sqrt (z+1) = (if 0<z.re then 1 else -1)*Complex.sqrt (z^2-1) := by
  rcases lt_or_gt_of_ne hre with hneg | hpos
  · simp only [show ¬ (0 < z.re) from not_lt.mpr hneg.le, ↓reduceIte]
    have him : z.im ≠ 0 := by
      rcases hz with h | h
      · exact h
      · linarith
    have hz' : -z ∈ arccoshDomain := Or.inl (by simpa using him)
    have h := sqrt_sub_one_mul_sqrt_add_one_of_re_pos hz' (by simpa using hneg)
    rw [show (-z)^2-1 = z^2-1 by ring, show -z-1 = -(z+1) by ring,
      show -z+1 = -(z-1) by ring] at h
    rcases lt_or_gt_of_ne him with hi | hi
    · rw [complexSqrt_neg_of_im_neg (by simpa using hi),
          complexSqrt_neg_of_im_neg (by simpa using hi)] at h
      rw [← h]; linear_combination (Complex.sqrt (z-1)*Complex.sqrt (z+1))*Complex.I_sq
    · rw [complexSqrt_neg_of_im_pos (by simpa using hi),
          complexSqrt_neg_of_im_pos (by simpa using hi)] at h
      rw [← h]; linear_combination (Complex.sqrt (z-1)*Complex.sqrt (z+1))*Complex.I_sq
  · simp only [hpos, ↓reduceIte, one_mul]; exact sqrt_sub_one_mul_sqrt_add_one_of_re_pos hz hpos

/-- Identity under the stated parameter and domain assumptions: `arccosh z=Complex.log ((if 0<z.re
then 1 else -1)*Complex.sqrt (z^2-1)+z)`. -/
@[dlmf 4.37.E19]
theorem arccosh_log {z : ℂ} (hz : z ∈ arccoshDomain) (hre : z.re≠0) :
    arccosh z=Complex.log ((if 0<z.re then 1 else -1)*Complex.sqrt (z^2-1)+z) := by
  rw [arccosh, sqrt_sub_one_mul_sqrt_add_one_eq_sign_mul_sqrt hz hre, add_comm]

/-- Identity under the stated parameter and domain assumptions: `arccosh (I*y)=(if 0<y then 1 else
-1)*π*I/2+ (Real.log (Real.sqrt (y^2+1)+(if 0<y then y else -y)):ℂ)`. -/
@[dlmf 4.37.E20]
theorem arccosh_imaginary {y : ℝ} (hy : y≠0) :
    arccosh (I*y)=(if 0<y then 1 else -1)*π*I/2+
      (Real.log (Real.sqrt (y^2+1)+(if 0<y then y else -y)):ℂ) := by
  have hI : (I:ℂ)^2 = -1 := by simp
  set r := Real.sqrt (y^2+1) with hr
  have hr2 : r^2 = y^2+1 := Real.sq_sqrt (by positivity)
  have hrpos : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hry : |y| < r := by
    rw [hr, ← Real.sqrt_sq_eq_abs]; exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  set S := Complex.sqrt (I*y-1)*Complex.sqrt (I*y+1) with hSdef
  have hS2 : S^2 = -((r:ℂ)^2) := by
    rw [hSdef, mul_pow, Trigonometric.complexSqrt_sq, Trigonometric.complexSqrt_sq]
    have : ((r:ℂ))^2 = ((y^2+1:ℝ):ℂ) := by rw [← Complex.ofReal_pow, hr2]
    rw [this]; push_cast; linear_combination (y:ℂ)^2*hI
  have hfac : (S - I*r)*(S + I*r) = 0 := by linear_combination hS2 - (r:ℂ)^2*hI
  unfold arccosh
  rw [← hSdef]
  have a1 := complexSqrt_re_nonneg (I*y-1)
  have a2 := complexSqrt_re_nonneg (I*y+1)
  rcases lt_or_gt_of_ne hy with hn | hp
  · have h1 : (I*y+1).im < 0 := by simpa using hn
    have h2 : (I*y-1).im < 0 := by simpa using hn
    have b1 := complexSqrt_im_nonpos h2
    have b2 := complexSqrt_im_nonpos h1
    have hSim : S.im ≤ 0 := by
      rw [hSdef, Complex.mul_im]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos a1 b2, mul_nonpos_of_nonneg_of_nonpos a2 b1]
    have hS : S = -(I*r) := by
      rcases mul_eq_zero.mp hfac with h | h
      · have : S = I*r := by linear_combination h
        rw [this] at hSim; simp at hSim; linarith
      · linear_combination h
    simp only [not_lt.mpr hn.le, ↓reduceIte]
    rw [hS, show I*(y:ℂ) + -(I*r) = -I*((r-y:ℝ):ℂ) by push_cast; ring,
      Complex.log_mul_ofReal _ (by linarith [neg_abs_le y, le_abs_self y]) _ (by simp)]
    rw [Complex.log_neg_I]; ring
  · have h1 : 0 < (I*y+1).im := by simpa using hp
    have h2 : 0 < (I*y-1).im := by simpa using hp
    have b1 := complexSqrt_im_nonneg h2.le
    have b2 := complexSqrt_im_nonneg h1.le
    have hSim : 0 ≤ S.im := by
      rw [hSdef, Complex.mul_im]
      nlinarith [mul_nonneg a1 b2, mul_nonneg a2 b1]
    have hS : S = I*r := by
      rcases mul_eq_zero.mp hfac with h | h
      · linear_combination h
      · have : S = -(I*r) := by linear_combination h
        rw [this] at hSim; simp at hSim; linarith
    simp only [hp, ↓reduceIte]
    rw [hS, show I*(y:ℂ) + I*r = I*((r+y:ℝ):ℂ) by push_cast; ring,
      Complex.log_mul_ofReal _ (by linarith [neg_abs_le y]) _ (by simp)]
    rw [Complex.log_I]; ring

/-- The principal square root has positive real part off the closed negative real axis. -/
private lemma complexSqrt_re_pos {w : ℂ} (h : w.im ≠ 0 ∨ 0 < w.re) : 0 < (Complex.sqrt w).re := by
  rw [Complex.sqrt, Complex.cpow_inv_two_re]
  apply Real.sqrt_pos.mpr
  rcases h with h | h
  · have := Complex.abs_re_lt_norm.mpr h
    linarith [neg_abs_le w.re]
  · linarith [Complex.re_le_norm w]

/-- Halving under the principal square root. -/
private lemma complexSqrt_div_two {w : ℂ} :
    Complex.sqrt (w/2) = Complex.sqrt w*((Real.sqrt 2)⁻¹:ℝ) := by
  have hs := Complex.sqrt_ofReal_mul (by norm_num : (0:ℝ)≤1/2) w
  simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
    Real.sqrt_div, Real.sqrt_one, Real.sqrt_inv, one_div, one_mul, Complex.ofReal_inv, mul_comm,
    div_eq_mul_inv] using hs

/-- `log (u²) = 2 log u` in the open right half-plane. -/
private lemma complexLog_sq_of_re_pos {u : ℂ} (h : 0 < u.re) :
    Complex.log (u^2) = 2*Complex.log u := by
  have hu0 : u ≠ 0 := fun e => by rw [e] at h; simp at h
  have harg : |Complex.arg u| < π/2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl h)
  rw [show u^2 = Complex.exp (2*Complex.log u) by
    rw [two_mul, Complex.exp_add, Complex.exp_log hu0]; ring, Complex.log_exp]
  · rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, Complex.im_ofReal_mul, Complex.log_im]
    linarith [(abs_lt.mp harg).1]
  · rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, Complex.im_ofReal_mul, Complex.log_im]
    linarith [(abs_lt.mp harg).2]

/-- Identity under the stated parameter and domain assumptions: `arccosh z=2*Complex.log
(Complex.sqrt ((z+1)/2)+Complex.sqrt ((z-1)/2))`. -/
@[dlmf 4.37.E21]
theorem arccosh_log_half {z : ℂ} (hz : z ∈ arccoshDomain) :
    arccosh z=2*Complex.log (Complex.sqrt ((z+1)/2)+Complex.sqrt ((z-1)/2)) := by
  have hp : (z+1).im ≠ 0 ∨ 0 < (z+1).re := by
    rcases hz with h | h
    · left; simpa using h
    · right; simp; linarith
  have hm : (z-1).im ≠ 0 ∨ 0 < (z-1).re := by
    rcases hz with h | h
    · left; simpa using h
    · right; simp; linarith
  have h2 : ((Real.sqrt 2)⁻¹:ℝ)^2 = (1/2:ℂ) := by
    rw [← Complex.ofReal_pow, inv_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring
  have hsum : Complex.sqrt ((z+1)/2)+Complex.sqrt ((z-1)/2) =
      (Complex.sqrt (z+1)+Complex.sqrt (z-1))*((Real.sqrt 2)⁻¹:ℝ) := by
    rw [complexSqrt_div_two, complexSqrt_div_two]; ring
  have hre : 0 < (Complex.sqrt ((z+1)/2)+Complex.sqrt ((z-1)/2)).re := by
    rw [Complex.add_re]
    have := complexSqrt_re_pos (show ((z+1)/2).im ≠ 0 ∨ 0 < ((z+1)/2).re by
      rcases hp with h | h
      · left; simpa using h
      · right; simp; linarith [show 0 < (z+1).re from h, show (z+1).re = z.re+1 by simp])
    linarith [complexSqrt_re_nonneg ((z-1)/2)]
  rw [← complexLog_sq_of_re_pos hre, hsum, mul_pow, h2, add_sq, Trigonometric.complexSqrt_sq,
      Trigonometric.complexSqrt_sq]
  unfold arccosh
  congr 1
  ring

/-- Limit formula in the specified filter: `Tendsto (fun ε : ℝ => arccosh ((x:ℂ)+I*ε)) (𝓝[>] 0) (𝓝
(Complex.log (I*Real.sqrt (1-x^2)+x))) ∧ Tendsto (fun ε : ℝ => arccosh ((x:ℂ)+I*ε)) (𝓝[<] 0)
(𝓝 (-Complex.log (I*Real.sqrt (1-x^2)+x)))`. -/
@[dlmf 4.37.E22]
theorem arccosh_inner_cut {x : ℝ} (hx : -1<x ∧ x≤1) :
    Tendsto (fun ε : ℝ => arccosh ((x:ℂ)+I*ε)) (𝓝[>] 0)
      (𝓝 (Complex.log (I*Real.sqrt (1-x^2)+x))) ∧
    Tendsto (fun ε : ℝ => arccosh ((x:ℂ)+I*ε)) (𝓝[<] 0)
      (𝓝 (-Complex.log (I*Real.sqrt (1-x^2)+x))) := by
  obtain ⟨hx1, hx2⟩ := hx
  set s := Real.sqrt (1-x^2) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s^2 = 1-x^2 := Real.sq_sqrt (by nlinarith)
  have hprod : Real.sqrt (1-x)*Real.sqrt (x+1) = s := by
    rw [← Real.sqrt_mul (by linarith), hs]; congr 1; ring
  have hp : Tendsto (fun ε : ℝ => Complex.sqrt ((x:ℂ)+I*ε+1)) (𝓝 0) (𝓝 (Real.sqrt (x+1):ℂ)) := by
    have hc : Tendsto (fun ε : ℝ => (x:ℂ)+I*ε+1) (𝓝 0) (𝓝 ((x+1:ℝ):ℂ)) := by
      have : Continuous (fun ε : ℝ => (x:ℂ)+I*ε+1) := by fun_prop
      simpa using this.tendsto 0
    have := (continuousAt_complexSqrt (w := ((x+1:ℝ):ℂ))
        (Or.inl (by simp; linarith))).tendsto.comp hc
    rwa [Hyperbolic.sqrt_ofReal _ (by linarith)] at this
  have hm : Tendsto (fun ε : ℝ => (x:ℂ)+I*ε-1) (𝓝 0) (𝓝 ((x:ℂ)-1)) := by
    have : Continuous (fun ε : ℝ => (x:ℂ)+I*ε-1) := by fun_prop
    simpa using this.tendsto 0
  have hlin : Tendsto (fun ε : ℝ => (x:ℂ)+I*ε) (𝓝 0) (𝓝 (x:ℂ)) := by
    have : Continuous (fun ε : ℝ => (x:ℂ)+I*ε) := by fun_prop
    simpa using this.tendsto 0
  have hmre : ((x:ℂ)-1).re ≤ 0 := by simp; linarith
  have hneg : Complex.sqrt (-((x:ℂ)-1)) = (Real.sqrt (1-x):ℂ) := by
    rw [show -((x:ℂ)-1) = ((1-x:ℝ):ℂ) by push_cast; ring, Hyperbolic.sqrt_ofReal _ (by linarith)]
  have hslit : I*(s:ℂ)+x ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    by_cases h0 : s = 0
    · left
      have : x^2 = 1 := by nlinarith
      have : x = 1 := by nlinarith
      simp [h0, this]
    · right; simp; exact h0
  constructor
  · have him : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), 0 < ((x:ℂ)+I*(ε:ℂ)-1).im :=
      eventually_mem_nhdsWithin.mono fun ε (hε : 0 < ε) => by simpa using hε
    have h1 := tendsto_complexSqrt_cut_upper (hm.mono_left nhdsWithin_le_nhds) hmre him
    rw [hneg] at h1
    have hg := (hlin.mono_left nhdsWithin_le_nhds).add (h1.mul (hp.mono_left nhdsWithin_le_nhds))
    have := (continuousAt_clog hslit).tendsto.comp
      (show Tendsto _ _ (𝓝 (I*(s:ℂ)+x)) by
        convert hg using 2; rw [← hprod]; push_cast; ring)
    exact this
  · have him : ∀ᶠ ε : ℝ in 𝓝[<] (0:ℝ), ((x:ℂ)+I*(ε:ℂ)-1).im < 0 :=
      eventually_mem_nhdsWithin.mono fun ε (hε : ε < 0) => by simpa using hε
    have h1 := tendsto_complexSqrt_cut_lower (hm.mono_left nhdsWithin_le_nhds) hmre him
    rw [hneg] at h1
    have hg := (hlin.mono_left nhdsWithin_le_nhds).add (h1.mul (hp.mono_left nhdsWithin_le_nhds))
    have hconj : -I*(s:ℂ)+x = (I*(s:ℂ)+x)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      have : ((s:ℂ))^2 = 1-(x:ℂ)^2 := by rw [← Complex.ofReal_pow, hs2]; push_cast; ring
      linear_combination this - (s:ℂ)^2*(by simp : (I:ℂ)^2 = -1)
    have harg : Complex.arg (I*(s:ℂ)+x) ≠ π := by
      intro h
      rw [Complex.arg_eq_pi_iff] at h
      simp at h
      obtain ⟨h1, h2⟩ := h
      rw [h2] at hs2; nlinarith
    have hslit' : -I*(s:ℂ)+x ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      by_cases h0 : s = 0
      · left
        have : x^2 = 1 := by nlinarith
        have : x = 1 := by nlinarith
        simp [h0, this]
      · right; simp; exact h0
    have := (continuousAt_clog hslit').tendsto.comp
      (show Tendsto _ _ (𝓝 (-I*(s:ℂ)+x)) by
        convert hg using 2; rw [← hprod]; push_cast; ring)
    rw [hconj, Complex.log_inv _ harg] at this
    exact this

/-- One-sided limit of the principal logarithm at the negative real axis, from above. -/
private lemma tendsto_complexLog_cut_upper {g : ℝ → ℂ} {l : Filter ℝ} {t : ℝ} (ht : t < 0)
    (hg : Tendsto g l (𝓝 (t:ℂ))) (him : ∀ᶠ ε in l, 0 ≤ (g ε).im) :
    Tendsto (fun ε => Complex.log (g ε)) l (𝓝 (Real.log (-t) + π*I)) := by
  have h := (Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
    (z := (t:ℂ)) (by simpa using ht) (by simp)).comp (tendsto_nhdsWithin_iff.mpr ⟨hg, him⟩)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg ht] at h
  exact h

/-- One-sided limit of the principal logarithm at the negative real axis, from below. -/
private lemma tendsto_complexLog_cut_lower {g : ℝ → ℂ} {l : Filter ℝ} {t : ℝ} (ht : t < 0)
    (hg : Tendsto g l (𝓝 (t:ℂ))) (him : ∀ᶠ ε in l, (g ε).im < 0) :
    Tendsto (fun ε => Complex.log (g ε)) l (𝓝 (Real.log (-t) - π*I)) := by
  have h := (Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero
    (z := (t:ℂ)) (by simpa using ht) (by simp)).comp (tendsto_nhdsWithin_iff.mpr ⟨hg, him⟩)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg ht] at h
  exact h

/-- Limit formula in the specified filter: `Tendsto (fun ε : ℝ => arccosh ((x:ℂ)+I*ε)) (𝓝[>] 0) (𝓝
(π*I+(Real.log (Real.sqrt (x^2-1)-x):ℂ))) ∧ Tendsto (fun ε : ℝ => arccosh ((x:ℂ)+I*ε)) (𝓝[<]
0) (𝓝 (-π*I+(Real.log (Real.sqrt (x^2-1)-x):ℂ)))`. -/
@[dlmf 4.37.E23]
theorem arccosh_outer_cut {x : ℝ} (hx : x≤ -1) :
    Tendsto (fun ε : ℝ => arccosh ((x:ℂ)+I*ε)) (𝓝[>] 0)
      (𝓝 (π*I+(Real.log (Real.sqrt (x^2-1)-x):ℂ))) ∧
    Tendsto (fun ε : ℝ => arccosh ((x:ℂ)+I*ε)) (𝓝[<] 0)
      (𝓝 (-π*I+(Real.log (Real.sqrt (x^2-1)-x):ℂ))) := by
  set r := Real.sqrt (x^2-1) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2 = x^2-1 := Real.sq_sqrt (by nlinarith)
  have hprod : Real.sqrt (1-x)*Real.sqrt (-1-x) = r := by
    rw [← Real.sqrt_mul (by linarith), hr]; congr 1; ring
  have hcont : ∀ c : ℂ, Tendsto (fun ε : ℝ => (x:ℂ)+I*ε+c) (𝓝 0) (𝓝 ((x:ℂ)+c)) := fun c => by
    have : Continuous (fun ε : ℝ => (x:ℂ)+I*ε+c) := by fun_prop
    simpa using this.tendsto 0
  have hm := hcont (-1)
  have hp := hcont 1
  simp only [← sub_eq_add_neg] at hm
  have hlin : Tendsto (fun ε : ℝ => (x:ℂ)+I*ε) (𝓝 0) (𝓝 (x:ℂ)) := by
    have : Continuous (fun ε : ℝ => (x:ℂ)+I*ε) := by fun_prop
    simpa using this.tendsto 0
  have hmre : ((x:ℂ)-1).re ≤ 0 := by simp; linarith
  have hpre : ((x:ℂ)+1).re ≤ 0 := by simp; linarith
  have hneg1 : Complex.sqrt (-((x:ℂ)-1)) = (Real.sqrt (1-x):ℂ) := by
    rw [show -((x:ℂ)-1) = ((1-x:ℝ):ℂ) by push_cast; ring, Hyperbolic.sqrt_ofReal _ (by linarith)]
  have hneg2 : Complex.sqrt (-((x:ℂ)+1)) = (Real.sqrt (-1-x):ℂ) := by
    rw [show -((x:ℂ)+1) = ((-1-x:ℝ):ℂ) by push_cast; ring, Hyperbolic.sqrt_ofReal _ (by linarith)]
  have hxr : x - r < 0 := by linarith
  have hI : (I:ℂ)^2 = -1 := by simp
  constructor
  · have him1 : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), 0 < ((x:ℂ)+I*(ε:ℂ)-1).im :=
      eventually_mem_nhdsWithin.mono fun ε (hε : 0 < ε) => by simpa using hε
    have him2 : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), 0 < ((x:ℂ)+I*(ε:ℂ)+1).im :=
      eventually_mem_nhdsWithin.mono fun ε (hε : 0 < ε) => by simpa using hε
    have h1 := tendsto_complexSqrt_cut_upper (hm.mono_left nhdsWithin_le_nhds) hmre him1
    have h2 := tendsto_complexSqrt_cut_upper (hp.mono_left nhdsWithin_le_nhds) hpre him2
    rw [hneg1] at h1; rw [hneg2] at h2
    have hg := (hlin.mono_left nhdsWithin_le_nhds).add (h1.mul h2)
    have hgim : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), 0 ≤ ((x:ℂ)+I*(ε:ℂ) +
        Complex.sqrt ((x:ℂ)+I*(ε:ℂ)-1)*Complex.sqrt ((x:ℂ)+I*(ε:ℂ)+1)).im :=
      (him1.and him2).mono fun ε ⟨e1, e2⟩ => by
        have a1 := complexSqrt_re_nonneg ((x:ℂ)+I*(ε:ℂ)-1)
        have a2 := complexSqrt_re_nonneg ((x:ℂ)+I*(ε:ℂ)+1)
        have b1 := complexSqrt_im_nonneg e1.le
        have b2 := complexSqrt_im_nonneg e2.le
        have hε : 0 < ε := by
          simpa using e1
        simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im]
        nlinarith [mul_nonneg a1 b2, mul_nonneg a2 b1]
    have hg' : Tendsto (fun ε : ℝ => (x:ℂ)+I*(ε:ℂ) +
        Complex.sqrt ((x:ℂ)+I*(ε:ℂ)-1)*Complex.sqrt ((x:ℂ)+I*(ε:ℂ)+1)) (𝓝[>] (0:ℝ))
        (𝓝 ((x-r:ℝ):ℂ)) := by
      convert hg using 2
      rw [← hprod]; push_cast
      linear_combination (-(Real.sqrt (1-x):ℂ)*(Real.sqrt (-1-x):ℂ))*hI
    have := tendsto_complexLog_cut_upper hxr hg' hgim
    have e : (π*I+(Real.log (Real.sqrt (x^2-1)-x):ℂ)) = Real.log (-(x-r)) + π*I := by
      rw [← hr]; ring_nf
    rw [e]; exact this
  · have him1 : ∀ᶠ ε : ℝ in 𝓝[<] (0:ℝ), ((x:ℂ)+I*(ε:ℂ)-1).im < 0 :=
      eventually_mem_nhdsWithin.mono fun ε (hε : ε < 0) => by simpa using hε
    have him2 : ∀ᶠ ε : ℝ in 𝓝[<] (0:ℝ), ((x:ℂ)+I*(ε:ℂ)+1).im < 0 :=
      eventually_mem_nhdsWithin.mono fun ε (hε : ε < 0) => by simpa using hε
    have h1 := tendsto_complexSqrt_cut_lower (hm.mono_left nhdsWithin_le_nhds) hmre him1
    have h2 := tendsto_complexSqrt_cut_lower (hp.mono_left nhdsWithin_le_nhds) hpre him2
    rw [hneg1] at h1; rw [hneg2] at h2
    have hg := (hlin.mono_left nhdsWithin_le_nhds).add (h1.mul h2)
    have hgim : ∀ᶠ ε : ℝ in 𝓝[<] (0:ℝ), ((x:ℂ)+I*(ε:ℂ) +
        Complex.sqrt ((x:ℂ)+I*(ε:ℂ)-1)*Complex.sqrt ((x:ℂ)+I*(ε:ℂ)+1)).im < 0 :=
      (him1.and him2).mono fun ε ⟨e1, e2⟩ => by
        have a1 := complexSqrt_re_nonneg ((x:ℂ)+I*(ε:ℂ)-1)
        have a2 := complexSqrt_re_nonneg ((x:ℂ)+I*(ε:ℂ)+1)
        have b1 := complexSqrt_im_nonpos e1
        have b2 := complexSqrt_im_nonpos e2
        have hε : ε < 0 := by
          simpa using e1
        simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im]
        nlinarith [mul_nonpos_of_nonneg_of_nonpos a1 b2, mul_nonpos_of_nonneg_of_nonpos a2 b1]
    have hg' : Tendsto (fun ε : ℝ => (x:ℂ)+I*(ε:ℂ) +
        Complex.sqrt ((x:ℂ)+I*(ε:ℂ)-1)*Complex.sqrt ((x:ℂ)+I*(ε:ℂ)+1)) (𝓝[<] (0:ℝ))
        (𝓝 ((x-r:ℝ):ℂ)) := by
      convert hg using 2
      rw [← hprod]; push_cast
      linear_combination (-(Real.sqrt (1-x):ℂ)*(Real.sqrt (-1-x):ℂ))*hI
    have := tendsto_complexLog_cut_lower hxr hg' hgim
    have e : (-π*I+(Real.log (Real.sqrt (x^2-1)-x):ℂ)) = Real.log (-(x-r)) - π*I := by
      rw [← hr]; ring_nf
    rw [e]; exact this

/-- Identity under the stated parameter and domain assumptions: `arctanh z=Complex.log
((1+z)/(1-z))/2`. -/
@[dlmf 4.37.E24]
theorem arctanh_log {z : ℂ} : arctanh z=Complex.log ((1+z)/(1-z))/2 := by
  rfl

/-- Limit formula in the specified filter: `Tendsto (fun ε : ℝ => arctanh ((x:ℂ)+I*ε)) (𝓝[>] 0) (𝓝
(π*I/2+(Real.log ((x+1)/(x-1)):ℂ)/2)) ∧ Tendsto (fun ε : ℝ => arctanh ((x:ℂ)+I*ε)) (𝓝[<] 0) (𝓝
(-π*I/2+(Real.log ((x+1)/(x-1)):ℂ)/2))`. -/
@[dlmf 4.37.E25]
theorem arctanh_cut {x : ℝ} (hx : 1< |x|) :
    Tendsto (fun ε : ℝ => arctanh ((x:ℂ)+I*ε)) (𝓝[>] 0)
      (𝓝 (π*I/2+(Real.log ((x+1)/(x-1)):ℂ)/2)) ∧
    Tendsto (fun ε : ℝ => arctanh ((x:ℂ)+I*ε)) (𝓝[<] 0)
      (𝓝 (-π*I/2+(Real.log ((x+1)/(x-1)):ℂ)/2)) := by
  have hx1 : 1-x ≠ 0 := by
    intro h; have : x = 1 := by linarith
    rw [this] at hx; norm_num at hx
  have hx2 : x+1 ≠ 0 := by
    intro h; have : x = -1 := by linarith
    rw [this] at hx; norm_num at hx
  have ht : (1+x)/(1-x) < 0 := by
    rcases lt_abs.mp hx with h | h
    · exact div_neg_of_pos_of_neg (by linarith) (by linarith)
    · exact div_neg_of_neg_of_pos (by linarith) (by linarith)
  have hcont : Tendsto (fun ε : ℝ => (1+((x:ℂ)+I*ε))/(1-((x:ℂ)+I*ε))) (𝓝 0)
      (𝓝 (((1+x)/(1-x):ℝ):ℂ)) := by
    have hn : Tendsto (fun ε : ℝ => 1+((x:ℂ)+I*ε)) (𝓝 0) (𝓝 (1+(x:ℂ))) := by
      have : Continuous (fun ε : ℝ => 1+((x:ℂ)+I*ε)) := by fun_prop
      simpa using this.tendsto 0
    have hd : Tendsto (fun ε : ℝ => 1-((x:ℂ)+I*ε)) (𝓝 0) (𝓝 (1-(x:ℂ))) := by
      have : Continuous (fun ε : ℝ => 1-((x:ℂ)+I*ε)) := by fun_prop
      simpa using this.tendsto 0
    have := hn.div hd (by exact_mod_cast hx1)
    rw [show (((1+x)/(1-x):ℝ):ℂ) = (1+(x:ℂ))/(1-(x:ℂ)) by push_cast; ring]
    exact this
  have him : ∀ ε : ℝ, ((1+((x:ℂ)+I*ε))/(1-((x:ℂ)+I*ε))).im =
      2*ε/Complex.normSq (1-((x:ℂ)+I*ε)) := by
    intro ε
    rw [Complex.div_im]
    simp only [Complex.add_im, Complex.sub_im, Complex.add_re, Complex.sub_re, Complex.mul_im,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im]
    ring
  have hnsq : ∀ ε : ℝ, 0 < Complex.normSq (1-((x:ℂ)+I*ε)) := fun ε =>
    Complex.normSq_pos.mpr fun h => hx1 (by
      have := congrArg Complex.re h; simpa using this)
  have e : Real.log (-((1+x)/(1-x))) = Real.log ((x+1)/(x-1)) := by
    have hx1' : x-1 ≠ 0 := fun h => hx1 (by linarith)
    congr 1; rw [← neg_div, div_eq_div_iff hx1 hx1']; ring
  constructor
  · have hev : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), 0 ≤ ((1+((x:ℂ)+I*ε))/(1-((x:ℂ)+I*ε))).im :=
      eventually_mem_nhdsWithin.mono fun ε (hε : 0 < ε) => by
        rw [him]; exact (div_pos (by linarith) (hnsq ε)).le
    have h := tendsto_complexLog_cut_upper ht (hcont.mono_left nhdsWithin_le_nhds) hev
    have := h.div_const 2
    rw [e] at this
    have e2 : (π*I/2+(Real.log ((x+1)/(x-1)):ℂ)/2) = ((Real.log ((x+1)/(x-1)):ℂ) + π*I)/2 := by
      ring
    rw [e2]; exact this
  · have hev : ∀ᶠ ε : ℝ in 𝓝[<] (0:ℝ), ((1+((x:ℂ)+I*ε))/(1-((x:ℂ)+I*ε))).im < 0 :=
      eventually_mem_nhdsWithin.mono fun ε (hε : ε < 0) => by
        rw [him]; exact div_neg_of_neg_of_pos (by linarith) (hnsq ε)
    have h := tendsto_complexLog_cut_lower ht (hcont.mono_left nhdsWithin_le_nhds) hev
    have := h.div_const 2
    rw [e] at this
    have e2 : (-π*I/2+(Real.log ((x+1)/(x-1)):ℂ)/2) = ((Real.log ((x+1)/(x-1)):ℂ) - π*I)/2 := by
      ring
    rw [e2]; exact this

/-- Identity under the stated parameter and domain assumptions: `Complex.sinh w=z ↔ ∃ k : ℤ,
w=(-1:ℂ)^k*arcsinh z+(k:ℂ)*π*I`. -/
@[dlmf 4.37.E26, dlmf 4.37.E29]
theorem sinh_inverse_family (z w : ℂ) :
    Complex.sinh w=z ↔ ∃ k : ℤ, w=(-1:ℂ)^k*arcsinh z+(k:ℂ)*π*I := by
  simpa only [Hyperbolic.sinh_arcsinh] using Hyperbolic.sinh_fiber_forms (arcsinh z) w

/-- Identity under the stated parameter and domain assumptions: `Complex.cosh w=z ↔ ∃ k : ℤ,
w=arccosh z+2*(k:ℂ)*π*I ∨ w= -arccosh z+2*(k:ℂ)*π*I`. -/
@[dlmf 4.37.E27, dlmf 4.37.E30]
theorem cosh_inverse_family (z w : ℂ) :
    Complex.cosh w=z ↔ ∃ k : ℤ, w=arccosh z+2*(k:ℂ)*π*I ∨ w= -arccosh z+2*(k:ℂ)*π*I := by
  have hrot:Complex.cosh w=z ↔ Complex.cos (arccosh z*I)=Complex.cos (w*I) := by
    rw [Complex.cos_mul_I,Complex.cos_mul_I,Hyperbolic.cosh_arccosh]
    exact eq_comm
  rw [hrot,Complex.cos_eq_cos_iff]
  constructor
  · rintro ⟨k,hk|hk⟩
    · refine ⟨-k,Or.inl ?_⟩
      push_cast
      linear_combination -I*hk+(w-arccosh z)*Complex.I_sq
    · refine ⟨-k,Or.inr ?_⟩
      push_cast
      linear_combination -I*hk+(w+arccosh z)*Complex.I_sq
  · rintro ⟨k,hk|hk⟩
    · refine ⟨-k,Or.inl ?_⟩
      push_cast
      linear_combination I*hk+(2*k*π)*Complex.I_sq
    · refine ⟨-k,Or.inr ?_⟩
      push_cast
      linear_combination I*hk+(2*k*π)*Complex.I_sq

/-- `cosh` and `sinh` in terms of `exp (2w)`, after multiplying by `2 exp w`. -/
lemma two_mul_exp_mul_cosh_and_sinh (w : ℂ) :
    2*Complex.exp w*Complex.cosh w = Complex.exp (2*w)+1 ∧
      2*Complex.exp w*Complex.sinh w = Complex.exp (2*w)-1 := by
  have h2 : Complex.exp (2*w) = Complex.exp w*Complex.exp w := by
    rw [← Complex.exp_add]; ring_nf
  have h1 : Complex.exp w*Complex.exp (-w) = 1 := by rw [← Complex.exp_add]; simp
  rw [Complex.cosh, Complex.sinh, h2]
  constructor
  · linear_combination h1
  · linear_combination -h1

/-- Formula under the stated hypotheses: `w ∈ arctanhValues z ↔ ∃ k : ℤ, w=arctanh z+(k:ℂ)*π*I`. -/
@[dlmf 4.37.E28, dlmf 4.37.E31]
theorem tanh_inverse_family {z w : ℂ} (hz : z≠1 ∧ z≠ -1) :
    w ∈ arctanhValues z ↔ ∃ k : ℤ, w=arctanh z+(k:ℂ)*π*I := by
  have hm : 1-z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz.1)
  have hA := exp_two_mul_arctanh_mul_one_sub z hz.1 hz.2
  have key : w ∈ arctanhValues z ↔ Complex.exp (2*w) = Complex.exp (2*arctanh z) := by
    obtain ⟨hc, hs⟩ := two_mul_exp_mul_cosh_and_sinh w
    have hE : Complex.exp w ≠ 0 := Complex.exp_ne_zero w
    constructor
    · rintro ⟨hc0, ht⟩
      rw [Complex.tanh_eq_sinh_div_cosh, div_eq_iff hc0] at ht
      apply mul_right_cancel₀ hm
      rw [hA]
      linear_combination -hs + (z)*hc + 2*Complex.exp w*ht
    · intro h
      have h' : Complex.exp (2*w)*(1-z) = 1+z := by rw [h, hA]
      have hc0 : Complex.cosh w ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hc
        have : (2:ℂ) = 0 := by linear_combination -h' - (1-z)*hc
        norm_num at this
      refine ⟨hc0, ?_⟩
      rw [Complex.tanh_eq_sinh_div_cosh, div_eq_iff hc0]
      apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hE)
      linear_combination hs - z*hc + h'
  rw [key, Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by linear_combination hn/2⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by linear_combination 2*hn⟩

/-- The open inverse-cosh domain is star-convex about `2`. -/
private lemma arccoshDomain_starConvex : StarConvex ℝ (2:ℂ) arccoshDomain := by
  intro y hy a b ha hb hab
  have hre : (a • (2:ℂ) + b • y).re = 2*a + b*y.re := by simp; ring
  have him : (a • (2:ℂ) + b • y).im = b*y.im := by simp
  rcases hy with hi | hr
  · rcases eq_or_lt_of_le hb with hb0 | hb0
    · right; rw [hre, ← hb0]; linarith
    · left; rw [him]; exact mul_ne_zero hb0.ne' hi
  · right; rw [hre]
    rcases eq_or_lt_of_le hb with hb0 | hb0
    · rw [← hb0]; linarith
    · nlinarith [mul_pos hb0 (sub_pos.mpr hr)]

/-- A real point of the inverse-sech domain lies in `(0,1)`. -/
private lemma re_mem_Ioo_of_mem_arcsechDomain {z : ℂ} (hz : z ∈ arcsechDomain) (hy : z.im = 0) :
    0 < z.re ∧ z.re < 1 := by
  obtain ⟨hz0, hi⟩ := hz
  have he : z = (z.re:ℂ) := Complex.ext (by simp) (by simp [hy])
  have hx0 : z.re ≠ 0 := fun h => hz0 (by rw [he, h]; simp)
  rw [he, ← Complex.ofReal_inv] at hi
  rcases hi with hi | hi
  · simp at hi
  · rw [Complex.ofReal_re] at hi
    have hxpos : 0 < z.re := by
      by_contra hc; replace hc := not_lt.mp hc
      have : z.re⁻¹ ≤ 0 := inv_nonpos.mpr hc
      linarith
    exact ⟨hxpos, by rwa [one_lt_inv₀ hxpos] at hi⟩

/-- `z √(z⁻¹-1) √(z⁻¹+1)` is the principal `√(1-z²)` on the whole inverse-sech domain. -/
lemma mul_sqrt_inv_sub_one_mul_sqrt_inv_add_one {z : ℂ} (hz : z ∈ arcsechDomain) :
    z*(Complex.sqrt (z⁻¹-1)*Complex.sqrt (z⁻¹+1)) = Complex.sqrt (1-z^2) := by
  have hVo : IsOpen arcsechDomain := by
    have hA : IsOpen arccoshDomain := by
      change IsOpen ({z:ℂ | z.im≠0}∪{z:ℂ | 1<z.re})
      exact (isOpen_ne.preimage Complex.continuous_im).union
        (isOpen_lt continuous_const Complex.continuous_re)
    have : arcsechDomain = {z : ℂ | z ≠ 0} ∩ (fun z : ℂ => z⁻¹) ⁻¹' arccoshDomain := rfl
    rw [this]
    exact continuousOn_inv₀.isOpen_inter_preimage isOpen_ne hA
  have h0A : (0:ℂ) ∉ arccoshDomain := by
    rintro (h | h)
    · simp at h
    · norm_num at h
  have hVc : IsPreconnected arcsechDomain := by
    have h2 : (2:ℂ) ∈ arccoshDomain := Or.inr (by norm_num)
    have hc := (arccoshDomain_starConvex.isPathConnected h2).isConnected.isPreconnected
    have himg : arcsechDomain = (fun z : ℂ => z⁻¹) '' arccoshDomain := by
      ext z
      constructor
      · rintro ⟨hz0, hz⟩; exact ⟨z⁻¹, hz, inv_inv z⟩
      · rintro ⟨w, hw, rfl⟩
        have hw0 : w ≠ 0 := fun h => h0A (h ▸ hw)
        exact ⟨inv_ne_zero hw0, by rwa [inv_inv]⟩
    rw [himg]
    exact hc.image _ (continuousOn_inv₀.mono fun w hw => fun h => h0A (h ▸ hw))
  have hslit : ∀ w ∈ arcsechDomain, 1-w^2 ∈ Complex.slitPlane := by
    intro w hw
    rw [Complex.mem_slitPlane_iff]
    by_cases hy : w.im = 0
    · left
      obtain ⟨h1, h2⟩ := re_mem_Ioo_of_mem_arcsechDomain hw hy
      simp [pow_two, Complex.mul_re, hy]; nlinarith
    · by_cases hx : w.re = 0
      · left; simp [pow_two, Complex.mul_re, hx]; nlinarith [sq_nonneg w.im]
      · right; simp [pow_two, Complex.mul_im]
        intro h; apply mul_ne_zero (mul_ne_zero two_ne_zero hx) hy; linear_combination -h
  have hr : AnalyticOnNhd ℂ (fun w => w*(Complex.sqrt (w⁻¹-1)*Complex.sqrt (w⁻¹+1)))
      arcsechDomain := by
    apply DifferentiableOn.analyticOnNhd _ hVo
    intro w hw
    obtain ⟨h1, h2⟩ := sub_one_add_one_mem_slitPlane_of_mem_arccoshDomain hw.2
    have hw0 := hw.1
    exact (differentiableAt_id.mul
      (((Complex.differentiableAt_sqrt h1).comp w
        (by fun_prop (disch := exact hw0) : DifferentiableAt ℂ (fun w : ℂ => w⁻¹-1) w)).mul
      ((Complex.differentiableAt_sqrt h2).comp w
        (by fun_prop (disch := exact hw0) : DifferentiableAt ℂ (fun w : ℂ => w⁻¹+1)
              w)))).differentiableWithinAt
  have hs : AnalyticOnNhd ℂ (fun w => Complex.sqrt (1-w^2)) arcsechDomain := by
    apply DifferentiableOn.analyticOnNhd _ hVo
    intro w hw
    exact ((Complex.differentiableAt_sqrt (hslit w hw)).comp w
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => 1-w^2) w)).differentiableWithinAt
  have hhalf : (1/2:ℂ) ∈ arcsechDomain := ⟨by norm_num, Or.inr (by norm_num)⟩
  have h1 : Complex.sqrt 1 = 1 := by simp [Complex.sqrt]
  have hanchor : (1/2:ℂ)*(Complex.sqrt ((1/2:ℂ)⁻¹-1)*Complex.sqrt ((1/2:ℂ)⁻¹+1)) =
      Complex.sqrt (1-(1/2:ℂ)^2) := by
    rw [show (1/2:ℂ)⁻¹-1 = 1 by norm_num, show (1/2:ℂ)⁻¹+1 = 3 by norm_num, h1, one_mul]
    symm
    apply complexSqrt_eq_of_sq_of_re_pos
    · rw [mul_pow, Trigonometric.complexSqrt_sq]; norm_num
    · have : 0 < (Complex.sqrt 3).re := by
        rw [Complex.sqrt, Complex.cpow_inv_two_re]
        apply Real.sqrt_pos.mpr; norm_num
      simpa using this
  refine eqOn_of_sq_eq_of_analyticOnNhd hVo hVc hr hs ?_ hhalf hanchor ?_ z hz
  · intro w hw
    have hw0 := hw.1
    rw [mul_pow, mul_pow, Trigonometric.complexSqrt_sq, Trigonometric.complexSqrt_sq,
        Trigonometric.complexSqrt_sq]; field_simp; ring
  · intro h
    have := Trigonometric.complexSqrt_sq (1-(1/2:ℂ)^2)
    rw [h] at this; norm_num at this

/-- On the inverse-sech domain, `1-z²` lies in the slit plane. -/
lemma one_sub_sq_mem_slitPlane_of_mem_arcsechDomain {w : ℂ} (hw : w ∈ arcsechDomain) :
    1-w^2 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hy : w.im = 0
  · left
    obtain ⟨h1, h2⟩ := re_mem_Ioo_of_mem_arcsechDomain hw hy
    simp [pow_two, Complex.mul_re, hy]; nlinarith
  · by_cases hx : w.re = 0
    · left; simp [pow_two, Complex.mul_re, hx]; nlinarith [sq_nonneg w.im]
    · right; simp [pow_two, Complex.mul_im]
      intro h; apply mul_ne_zero (mul_ne_zero two_ne_zero hx) hy; linear_combination -h

/-- The interrelation example in §4.37(vi), with compatible principal branches. -/
theorem arcsech_arccoth_interrelation {a : ℂ} (hre : 0<a.re) (ha : a∈arcsechDomain) :
    arcsech a=arccoth ((Complex.sqrt (1-a^2))⁻¹) := by
  have ha0 : a ≠ 0 := ha.1
  set q := Complex.sqrt (1-a^2) with hqdef
  have hq2 : q^2 = 1-a^2 := Trigonometric.complexSqrt_sq _
  have hqre : 0 ≤ q.re := by
    rw [hqdef, Complex.sqrt, Complex.cpow_inv_two_re]; exact Real.sqrt_nonneg _
  have hq0 : q ≠ 0 := by
    intro h; rw [h] at hq2
    exact Complex.slitPlane_ne_zero (one_sub_sq_mem_slitPlane_of_mem_arcsechDomain ha)
        (by rw [← hq2]; ring)
  have hq1 : 1+q ≠ 0 := by
    intro h; have : q = -1 := by linear_combination h
    rw [this] at hqre; norm_num at hqre
  have hqm : 1-q ≠ 0 := by
    intro h; have : q = 1 := by linear_combination -h
    rw [this] at hq2
    exact ha0 (pow_eq_zero_iff two_ne_zero |>.mp (by linear_combination hq2))
  set u := (1+q)/a with hu
  have hu0 : u ≠ 0 := div_ne_zero hq1 ha0
  have huinv : u + u⁻¹ = 2/a := by
    rw [hu, inv_div]; field_simp; linear_combination hq2
  have hure : 0 < u.re := by
    by_contra hc; replace hc := not_lt.mp hc
    have h1 : u⁻¹.re ≤ 0 := by
      rw [Complex.inv_re]; exact div_nonpos_of_nonpos_of_nonneg hc (Complex.normSq_nonneg _)
    have h2 : 0 < (2/a).re := by
      rw [div_eq_mul_inv, Complex.mul_re, Complex.inv_re, Complex.inv_im]
      simp only [Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
      have : 0 < Complex.normSq a := Complex.normSq_pos.mpr ha0
      positivity
    rw [← huinv, Complex.add_re] at h2
    linarith
  have hS : a⁻¹ + Complex.sqrt (a⁻¹-1)*Complex.sqrt (a⁻¹+1) = u := by
    have e := mul_sqrt_inv_sub_one_mul_sqrt_inv_add_one ha
    rw [← hqdef] at e
    rw [hu, eq_div_iff ha0]
    linear_combination e + mul_inv_cancel₀ ha0
  have hL : arcsech a = Complex.log u := by
    rw [arcsech, arccosh, hS]
  have hR : arccoth q⁻¹ = Complex.log (u^2)/2 := by
    rw [arccoth_eq_inv (inv_ne_zero hq0), inv_inv, arctanh]
    congr 2
    rw [hu, div_pow]
    field_simp
    linear_combination hq2
  rw [hL, hR]
  have harg : |Complex.arg u| < π/2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hure)
  have hpow : u^2 = Complex.exp (2*Complex.log u) := by
    rw [two_mul, Complex.exp_add, Complex.exp_log hu0]; ring
  rw [hpow, Complex.log_exp]
  · ring
  · rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, Complex.im_ofReal_mul, Complex.log_im]
    linarith [(abs_lt.mp harg).1]
  · rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, Complex.im_ofReal_mul, Complex.log_im]
    linarith [(abs_lt.mp harg).2]

/-- The half-angle logarithm holds on the right half-plane, including the chosen real cut bank. -/
private lemma arccosh_half_right {z : ℂ} (hz : 0<z.re) :
    arccosh z = 2*arcsinh (Complex.sqrt ((z-1)/2)) := by
  let c : ℂ := (Real.sqrt (1/2):ℝ)
  have hc2 : c^2=(1/2:ℂ) := by
    dsimp [c]
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hs (w : ℂ) : Complex.sqrt (w/2) = c*Complex.sqrt w := by
    simpa only [c, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
      div_mul_eq_mul_div, one_mul] using
      Complex.sqrt_ofReal_mul (by norm_num : (0:ℝ)≤1/2) w
  have hp : 0<((z+1)/2).re := by simp; linarith
  have hre : 0<(Complex.sqrt ((z+1)/2)+Complex.sqrt ((z-1)/2)).re := by
    rw [Complex.add_re]
    linarith [complexSqrt_re_pos (Or.inr hp), complexSqrt_re_nonneg ((z-1)/2)]
  have hlog := complexLog_sq_of_re_pos hre
  rw [hs, hs, add_sq, mul_pow, mul_pow, hc2, Trigonometric.complexSqrt_sq,
      Trigonometric.complexSqrt_sq] at hlog
  unfold arccosh arcsinh
  rw [Trigonometric.complexSqrt_sq,show (z-1)/2+1=(z+1)/2 by ring]
  rw [hs,hs,← hlog]
  congr 1
  linear_combination -2*Complex.sqrt (z+1)*Complex.sqrt (z-1)*hc2

/-- Central-binomial coefficient divided by 4^n, used in the inverse expansions. -/
def hyperbolicCentral (n : ℕ) : ℂ := (Nat.choose (2*n) n:ℂ)/(4:ℂ)^n
/-- The central-binomial expansion of the principal inverse hyperbolic sine
converges on the closed unit disk, including its two branch points. -/
lemma hasSum_arcsinh_closed_disk {z : ℂ} (hz : ‖z‖≤1) :
    HasSum (fun n : ℕ => (-1:ℂ)^n*hyperbolicCentral n/(2*n+1:ℂ)*z^(2*n+1))
      (arcsinh z) := by
  have hn : ‖-I*z‖≤1 := by simpa using hz
  have h := (hasSum_arcsin_principal hn).mul_left I
  rw [← Hyperbolic.arcsinh_rotation] at h
  convert h using 1
  ext n
  rw [mul_pow, pow_add, pow_mul, pow_add, pow_mul, show (-I:ℂ)^2 = -1 by simp, pow_one]
  dsimp only [hyperbolicCentral]
  simp only [div_eq_mul_inv, mul_inv_rev]
  linear_combination ((2*n).choose n:ℂ)*(-1:ℂ)^n*z^(2*n)*z*(4^n:ℂ)⁻¹*(2*n+1:ℂ)⁻¹*Complex.I_sq

/-- The central-binomial power series of the principal inverse hyperbolic sine
on the open unit disk, obtained by rotating the principal arcsine expansion. -/
@[dlmf 4.38.E1]
theorem hasSum_arcsinh {z : ℂ} (hz : ‖z‖<1) : HasSum
    (fun n : ℕ => (-1:ℂ)^n*hyperbolicCentral n/(2*n+1:ℂ)*z^(2*n+1)) (arcsinh z) := by
  exact hasSum_arcsinh_closed_disk hz.le

/-- `(1/2)ₙ/n! = C(2n,n)/4ⁿ`. -/
private lemma ascPochhammer_half_div_factorial (n : ℕ) :
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

/-- The principal square root has positive real part in the open right half-plane. -/
private lemma re_sqrt_pos {w : ℂ} (hw : 0 < w.re) : 0 < (Complex.sqrt w).re := by
  rw [Complex.sqrt, Complex.cpow_inv_two_re]
  apply Real.sqrt_pos.mpr
  have := Complex.re_le_norm w
  linarith

/-- `(√w)² = w`. -/
private lemma sqrt_sq_self (w : ℂ) : Complex.sqrt w ^ 2 = w := by
  rw [Complex.sqrt]; exact Complex.cpow_ofNat_inv_pow w 2

/-- `-log((1 + √(1-v²))/2) = ∑ c_{n+1} v^{2n+2}/(2n+2)` on the unit disk. -/
theorem hasSum_hyperbolicCentral_neg_log {v : ℂ} (hv : ‖v‖ < 1) :
    HasSum (fun n : ℕ => hyperbolicCentral (n + 1) / (2 * n + 2 : ℂ) * v ^ (2 * n + 2))
      (-Complex.log ((1 + Complex.sqrt (1 - v ^ 2)) / 2)) := by
  set f : ℂ → ℂ := fun v => -Complex.log ((1 + Complex.sqrt (1 - v ^ 2)) / 2)
  have hre : ∀ w : ℂ, ‖w‖ < 1 → 0 < (1 - w ^ 2).re := by
    intro w hw
    have h1 : |(w ^ 2).re| < 1 := by
      calc |(w ^ 2).re| ≤ ‖w ^ 2‖ := Complex.abs_re_le_norm _
        _ = ‖w‖ ^ 2 := norm_pow _ _
        _ < 1 := by nlinarith [norm_nonneg w]
    rw [Complex.sub_re, Complex.one_re]; linarith [le_abs_self (w ^ 2).re]
  have hderiv : ∀ w : ℂ, ‖w‖ < 1 → HasDerivAt f
      (w / (Complex.sqrt (1 - w ^ 2) * (1 + Complex.sqrt (1 - w ^ 2)))) w := by
    intro w hw
    set q := Complex.sqrt (1 - w ^ 2)
    have hq : 0 < q.re := re_sqrt_pos (hre w hw)
    have hq0 : q ≠ 0 := fun h => by rw [h] at hq; simp at hq
    have hq1 : 1 + q ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have hslit : 1 - w ^ 2 ∈ slitPlane := Or.inl (hre w hw)
    have h1 : HasDerivAt (fun w : ℂ => 1 - w ^ 2) (-(2 * w)) w := by
      simpa using ((hasDerivAt_pow 2 w).const_sub 1)
    have h2 := h1.cpow_const (c := (2⁻¹ : ℂ)) hslit
    have hslit2 : (1 + q) / 2 ∈ slitPlane := Or.inl (by simp; linarith)
    have h3 := ((h2.const_add 1).div_const 2).clog hslit2
    have h4 := h3.neg
    convert h4 using 1
    · funext t; simp [f, Complex.sqrt]
    have hw2 : (1 - w ^ 2) ≠ 0 := fun h => by rw [h] at hslit; simp at hslit
    have e : (1 - w ^ 2) ^ ((2⁻¹ : ℂ) - 1) = q / (1 - w ^ 2) := by
      rw [Complex.cpow_sub _ _ hw2, Complex.cpow_one]; rfl
    have hq' : (1 - w ^ 2) ^ (2⁻¹ : ℂ) = q := rfl
    rw [e, hq']
    have hsq : q ^ 2 = 1 - w ^ 2 := sqrt_sq_self _
    rw [← hsq]
    field_simp
  have hdiff : DifferentiableOn ℂ f (Metric.ball 0 1) := fun w hw =>
    (hderiv w (by simpa using hw)).differentiableAt.differentiableWithinAt
  have hf0 : f 0 = 0 := by simp [f]
  refine Complex.hasSum_odd_primitive_on_ball (f := f) (b := fun n => hyperbolicCentral (n + 1))
    one_pos hdiff hf0 (fun w hw => ?_) hv
  rw [(hderiv w hw).deriv]
  set q := Complex.sqrt (1 - w ^ 2)
  have hq : 0 < q.re := re_sqrt_pos (hre w hw)
  have hq0 : q ≠ 0 := fun h => by rw [h] at hq; simp at hq
  have hq1 : 1 + q ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hsq : q ^ 2 = 1 - w ^ 2 := sqrt_sq_self _
  have hw2 : ‖w ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg w]
  have hbin := Complex.hasSum_ascPochhammer_mul_pow_div_factorial (1/2:ℂ) (w ^ 2) hw2
  simp_rw [ascPochhammer_half_div_factorial] at hbin
  have hval : 1 / (1 - w ^ 2) ^ (1 / 2 : ℂ) = 1 / q := by
    rw [show (1 / 2 : ℂ) = 2⁻¹ by norm_num]; rfl
  rw [hval] at hbin
  have hs := (hasSum_nat_add_iff' 1).mpr hbin
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.choose_zero_right,
    Nat.cast_one, mul_one, div_one] at hs
  -- hs : ∑ c_{n+1} (w²)^{n+1} = 1/q - 1
  rcases eq_or_ne w 0 with rfl | hw0
  · simp
  have h := hs.div_const w
  convert h using 1
  · funext n
    simp only [hyperbolicCentral]
    rw [← pow_mul, show 2 * (n + 1) = 2 * n + 1 + 1 by ring, pow_succ]
    field_simp
    ring
  · field_simp
    linear_combination hsq

/-- In the right half-plane, the imaginary part of the square root is nonpositive when that of
the radicand is. -/
private lemma im_sqrt_nonpos_of_re_pos {w : ℂ} (hre : 0 < w.re) (h : w.im ≤ 0) :
    (Complex.sqrt w).im ≤ 0 := by
  rcases h.lt_or_eq with h | h
  · exact complexSqrt_im_nonpos h
  · rw [Complex.sqrt, Complex.cpow_inv_two_im_eq_sqrt h.ge]
    have : ‖w‖ = w.re := by
      rw [← Complex.re_add_im w, h]; simp [abs_of_pos hre]
    rw [this, sub_self, zero_div, Real.sqrt_zero]

/-- `Re(1 - v²) > 0` on the unit disk. -/
private lemma re_one_sub_sq_pos {v : ℂ} (hv : ‖v‖ < 1) : 0 < (1 - v ^ 2).re := by
  have h1 : |(v ^ 2).re| < 1 := by
    calc |(v ^ 2).re| ≤ ‖v ^ 2‖ := Complex.abs_re_le_norm _
      _ = ‖v‖ ^ 2 := norm_pow _ _
      _ < 1 := by nlinarith [norm_nonneg v]
  rw [Complex.sub_re, Complex.one_re]; linarith [le_abs_self (v ^ 2).re]

/-- Large-argument form of the principal inverse cosh. -/
private lemma log_two_mul_sub_arccosh {z : ℂ} (hn : 1 < ‖z‖) :
    Complex.log (2 * z) - arccosh z =
      -Complex.log ((1 + Complex.sqrt (1 - (1 / z) ^ 2)) / 2) := by
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hn; linarith
  set u := 1 / z with hu_def
  have hu : ‖u‖ < 1 := by
    rw [hu_def, norm_div, norm_one]; exact (div_lt_one (by linarith)).mpr hn
  set w := 1 - u ^ 2 with hw_def
  have hwre : 0 < w.re := re_one_sub_sq_pos hu
  set q := Complex.sqrt w
  have hq : 0 < q.re := re_sqrt_pos hwre
  have hsq : q ^ 2 = w := sqrt_sq_self _
  set a := Complex.sqrt (z - 1)
  set b := Complex.sqrt (z + 1)
  have ha2 : a ^ 2 = z - 1 := sqrt_sq_self _
  have hb2 : b ^ 2 = z + 1 := sqrt_sq_self _
  have hzab : z = (a ^ 2 + b ^ 2) / 2 := by rw [ha2, hb2]; ring
  -- the product of the two square roots is `z q`
  have hab : 0 ≤ a.im * b.im := by
    rcases le_or_gt 0 z.im with h | h
    · exact mul_nonneg (complexSqrt_im_nonneg (by simpa using h))
        (complexSqrt_im_nonneg (by simpa using h))
    · exact mul_nonneg_of_nonpos_of_nonpos (complexSqrt_im_nonpos (by simpa using h))
        (complexSqrt_im_nonpos (by simpa using h))
  have hre1 : 0 ≤ (a * b * (starRingEnd ℂ) z).re := by
    have e : (a * b * (starRingEnd ℂ) z).re = ((a.re ^ 2 + a.im ^ 2) + (b.re ^ 2 + b.im ^ 2)) *
        (a.re * b.re + a.im * b.im) / 2 := by
      rw [hzab, map_div₀, map_add, map_pow, map_pow, map_ofNat]
      simp [Complex.mul_re, Complex.mul_im, pow_two, Complex.div_ofNat_re, Complex.conj_re,
        Complex.conj_im]
      ring
    rw [e]
    have := complexSqrt_re_nonneg (z - 1)
    have := complexSqrt_re_nonneg (z + 1)
    have : 0 ≤ a.re * b.re := mul_nonneg (by assumption) (by assumption)
    positivity
  have hre2 : 0 < (z * q * (starRingEnd ℂ) z).re := by
    rw [mul_right_comm, Complex.mul_conj, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos (Complex.normSq_pos.mpr hz0) hq
  have hp : a * b = z * q := by
    have h2 : (a * b) ^ 2 = (z * q) ^ 2 := by
      rw [mul_pow, mul_pow, ha2, hb2, hsq, hw_def, hu_def]; field_simp; ring
    have hne : a * b + z * q ≠ 0 := by
      intro h
      have := congrArg (fun x => (x * (starRingEnd ℂ) z).re) h
      simp only [add_mul, Complex.add_re, zero_mul, Complex.zero_re] at this
      linarith
    have : (a * b - z * q) * (a * b + z * q) = 0 := by linear_combination h2
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hne)
  have h1q : 1 + q ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have harc : arccosh z = Complex.log (z * (1 + q)) := by
    rw [arccosh]; congr 1; rw [hp]; ring
  -- argument bounds
  have hre1q : 0 < (1 + q).re := by simp; linarith
  have harg1q : |arg (1 + q)| < π / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre1q)
  have hwim : w.im = 2 * z.re * z.im / Complex.normSq z ^ 2 := by
    rw [hw_def, hu_def]
    simp [Complex.sub_im, pow_two, Complex.mul_im]
    ring
  have hN : 0 < Complex.normSq z ^ 2 := by positivity [Complex.normSq_pos.mpr hz0]
  have hqim : (1 + q).im = q.im := by simp
  have hlog : Complex.log (z * (1 + q)) = Complex.log z + Complex.log (1 + q) := by
    refine (Complex.log_mul_eq_add_log_iff hz0 h1q).mpr ⟨?_, ?_⟩
    · rcases le_or_gt 0 (arg (1 + q)) with h | h
      · linarith [Complex.neg_pi_lt_arg z]
      · have hqi : q.im < 0 := by rw [← hqim]; exact Complex.arg_neg_iff.mp h
        have hwi : w.im < 0 := by
          by_contra hc; push Not at hc; linarith [complexSqrt_im_nonneg hc]
        rw [hwim, div_neg_iff] at hwi
        rcases hwi with ⟨-, hc⟩ | ⟨hc, -⟩
        · exact absurd hN (not_lt.mpr hc.le)
        rcases le_or_gt 0 z.re with hx | hx
        · have := Complex.abs_arg_le_pi_div_two_iff.mpr hx
          linarith [abs_le.mp this, abs_lt.mp harg1q]
        · have hy : 0 ≤ z.im := by nlinarith
          have := Complex.arg_nonneg_iff.mpr hy
          linarith [abs_lt.mp harg1q, Real.pi_pos]
    · rcases le_or_gt (arg (1 + q)) 0 with h | h
      · linarith [Complex.arg_le_pi z]
      · have hqi : 0 < q.im := by
          rw [← hqim]; by_contra hc; push Not at hc
          rcases hc.lt_or_eq with hc | hc
          · linarith [Complex.arg_neg_iff.mpr hc]
          · have := Complex.arg_eq_zero_iff.mpr ⟨hre1q.le, hc⟩
            linarith
        have hwi : 0 < w.im := by
          by_contra hc; push Not at hc; linarith [im_sqrt_nonpos_of_re_pos hwre hc]
        rw [hwim] at hwi
        have hxy : 0 < z.re * z.im := by
          have := (div_pos_iff.mp hwi)
          rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
          · linarith
          · exact absurd hN (not_lt.mpr h2.le)
        rcases le_or_gt 0 z.re with hx | hx
        · have := Complex.abs_arg_le_pi_div_two_iff.mpr hx
          linarith [abs_le.mp this, abs_lt.mp harg1q]
        · have hy : z.im < 0 := by nlinarith
          have := Complex.arg_neg_iff.mpr hy
          linarith [abs_lt.mp harg1q, Real.pi_pos]
  have h2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  have hlog2z : Complex.log (2 * z) = Real.log 2 + Complex.log z := by
    rw [h2, Complex.log_ofReal_mul (by norm_num) hz0]
  have hlog1q : Complex.log (1 + q) = Real.log 2 + Complex.log ((1 + q) / 2) := by
    rw [← Complex.log_ofReal_mul (by norm_num) (div_ne_zero h1q two_ne_zero), ← h2]
    congr 1; ring
  rw [harc, hlog, hlog2z, hlog1q]; ring

/-- Large-argument form of the principal inverse sinh in the right half-plane. -/
private lemma arcsinh_sub_log_two_mul {z : ℂ} (hz : 0 < z.re) (hn : 1 < ‖z‖) :
    arcsinh z - Complex.log (2 * z) =
      Complex.log ((1 + Complex.sqrt (1 - (I / z) ^ 2)) / 2) := by
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hn; linarith
  set v := I / z with hv_def
  have hv : ‖v‖ < 1 := by
    rw [hv_def, norm_div, Complex.norm_I]; exact (div_lt_one (by linarith)).mpr hn
  set w := 1 - v ^ 2 with hw_def
  have hwre : 0 < w.re := re_one_sub_sq_pos hv
  set q := Complex.sqrt w
  have hq : 0 < q.re := re_sqrt_pos hwre
  have hsq : q ^ 2 = w := sqrt_sq_self _
  set p := Complex.sqrt (z ^ 2 + 1)
  have hp2 : p ^ 2 = z ^ 2 + 1 := sqrt_sq_self _
  have hN : 0 < Complex.normSq z ^ 2 := by positivity [Complex.normSq_pos.mpr hz0]
  have hwim : w.im = -(2 * z.re * z.im) / Complex.normSq z ^ 2 := by
    rw [hw_def, hv_def]
    simp [Complex.sub_im, pow_two, Complex.mul_im, Complex.div_re, Complex.div_im]
    ring
  have hzq : 0 < (z * q).re := by
    rw [Complex.mul_re]
    have h1 : 0 < z.re * q.re := mul_pos hz hq
    have h2 : 0 ≤ -(z.im * q.im) := by
      rcases le_or_gt 0 z.im with hy | hy
      · have : w.im ≤ 0 := by
          rw [hwim]; exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) hN.le
        have := im_sqrt_nonpos_of_re_pos hwre this
        nlinarith
      · have : 0 ≤ w.im := by
          rw [hwim]; exact div_nonneg (by nlinarith) hN.le
        have := complexSqrt_im_nonneg this
        nlinarith
    linarith
  have hp : p = z * q := by
    have h2 : p ^ 2 = (z * q) ^ 2 := by
      rw [hp2, mul_pow, hsq, hw_def, hv_def, div_pow, I_sq]; field_simp; ring
    have hne : p + z * q ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp only [Complex.add_re, Complex.zero_re] at this
      linarith [complexSqrt_re_nonneg (z ^ 2 + 1)]
    have : (p - z * q) * (p + z * q) = 0 := by linear_combination h2
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hne)
  have h1q : 1 + q ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hre1q : 0 < (1 + q).re := by simp; linarith
  have harc : arcsinh z = Complex.log z + Complex.log (1 + q) := by
    rw [arcsinh, show p + z = z * (1 + q) by rw [hp]; ring]
    refine (Complex.log_mul_eq_add_log_iff hz0 h1q).mpr ⟨?_, ?_⟩
    · have a := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz))
      have b := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre1q))
      linarith
    · have a := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz))
      have b := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre1q))
      linarith [Real.pi_pos]
  have h2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  have hlog2z : Complex.log (2 * z) = Real.log 2 + Complex.log z := by
    rw [h2, Complex.log_ofReal_mul (by norm_num) hz0]
  have hlog1q : Complex.log (1 + q) = Real.log 2 + Complex.log ((1 + q) / 2) := by
    rw [← Complex.log_ofReal_mul (by norm_num) (div_ne_zero h1q two_ne_zero), ← h2]
    congr 1; ring
  rw [harc, hlog2z, hlog1q]; ring

/-- The series with terms `(fun n : ℕ => (-1:ℂ)^n*hyperbolicCentral (n+1)/((2*n+2:ℂ)*z^(2*n+2)))`
converges to `(arcsinh z-Complex.log (2*z))`. -/
@[dlmf 4.38.E2]
theorem hasSum_arcsinh_large {z : ℂ} (hz : 0<z.re) (hn : 1<‖z‖) : HasSum
    (fun n : ℕ => (-1:ℂ)^n*hyperbolicCentral (n+1)/((2*n+2:ℂ)*z^(2*n+2)))
    (arcsinh z-Complex.log (2*z)) := by
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hn; linarith
  have hv : ‖I / z‖ < 1 := by
    rw [norm_div, Complex.norm_I]; exact (div_lt_one (by linarith)).mpr hn
  rw [arcsinh_sub_log_two_mul hz hn]
  have h := (hasSum_hyperbolicCentral_neg_log hv).neg
  rw [neg_neg] at h
  convert h using 1
  funext n
  have hI : I ^ (2 * n + 2) = -(-1 : ℂ) ^ n := by
    rw [show 2 * n + 2 = 2 * (n + 1) by ring, pow_mul, I_sq]; ring
  rw [div_pow, hI]
  field_simp

/-- The series with terms `(fun n : ℕ => hyperbolicCentral (n+1)/((2*n+2:ℂ)*z^(2*n+2)))` converges
to `(Complex.log (2*z)-arccosh z)`. -/
@[dlmf 4.38.E3]
theorem hasSum_arccosh_large {z : ℂ} (hn : 1<‖z‖) : HasSum
    (fun n : ℕ => hyperbolicCentral (n+1)/((2*n+2:ℂ)*z^(2*n+2))) (Complex.log (2*z)-arccosh z) := by
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hn; linarith
  have hu : ‖1 / z‖ < 1 := by
    rw [norm_div, norm_one]; exact (div_lt_one (by linarith)).mpr hn
  rw [log_two_mul_sub_arccosh hn]
  convert hasSum_hyperbolicCentral_neg_log hu using 1
  funext n
  rw [div_pow, one_pow]
  field_simp

/-- The principal inverse-cosh expansion about one after factoring the square root.
The series converges on the stated closed disk in the right half-plane, with
its removable value at one assigned explicitly. -/
@[dlmf 4.38.E4]
theorem hasSum_arccosh_near_one {z : ℂ} (hz : 0<z.re) (hn : ‖z-1‖≤2) : HasSum
    (fun n : ℕ => (-1:ℂ)^n*hyperbolicCentral n/((2:ℂ)^n*(2*n+1:ℂ))*(z-1)^n)
    (if z=1 then 1 else arccosh z/Complex.sqrt (2*(z-1))) := by
  by_cases hz1 : z=1
  · subst z
    convert hasSum_ite_eq (0:ℕ) (1:ℂ) using 1
    · funext n
      by_cases hn : n=0
      · simp [hn,hyperbolicCentral]
      · simp [hn]
    · simp
  let w := Complex.sqrt ((z-1)/2)
  have hw2 : w^2=(z-1)/2 := Trigonometric.complexSqrt_sq _
  have hw0 : w≠0 := by intro h; rw [h] at hw2; apply hz1; linear_combination -2*hw2
  have hwn : ‖w‖≤1 := by
    have he : ‖w‖^2=‖z-1‖/2 := by
      rw [← norm_pow,hw2,norm_div]; norm_num
    nlinarith [norm_nonneg w]
  have h := (hasSum_arcsinh_closed_disk hwn).mul_left w⁻¹
  have hs : Complex.sqrt (2*(z-1))=2*w := by
    have he := Complex.sqrt_ofReal_mul (by norm_num : (0:ℝ)≤4) ((z-1)/2)
    norm_num at he
    convert he using 1
    congr 1
    ring
  have hv : w⁻¹*arcsinh w=arccosh z/Complex.sqrt (2*(z-1)) := by
    rw [arccosh_half_right hz,hs]
    dsimp only [w]
    field_simp [hw0]
  rw [hv] at h
  rw [ite_eq_right_iff.mpr (fun h => (hz1 h).elim)]
  convert h using 1
  ext n
  rw [pow_add,pow_mul,hw2,pow_one,div_pow]
  field_simp [hw0]

end DLMF.Elementary
end
