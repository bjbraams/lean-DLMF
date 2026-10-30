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

Square-root branches, cut-side limits and the full inverse families of the hyperbolic functions.

Source references and common attribution are retained in
`DLMF.Elementary.Hyperbolic`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory

open scoped Real Topology

namespace DLMF.Elementary

/-- Characterization of the principal square root by a root with positive real part. -/
private lemma hypR4_sqrt_eq_of_sq {a w : ℂ} (hw : w^2 = a) (hre : 0 < w.re) :
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

/-- The principal square root of `-w` for `w` in the upper half-plane. -/
private lemma hypR4_sqrt_neg_of_im_pos {w : ℂ} (h : 0 < w.im) :
    Complex.sqrt (-w) = -I*Complex.sqrt w := by
  apply hypR4_sqrt_eq_of_sq
  · rw [mul_pow, trig_sqrt_sq]; simp
  · have him : (Complex.sqrt w).im = Real.sqrt ((‖w‖ - w.re)/2) := by
      rw [Complex.sqrt]; exact Complex.cpow_inv_two_im_eq_sqrt h.le
    have hlt : w.re < ‖w‖ := lt_of_le_of_lt (le_abs_self _) (Complex.abs_re_lt_norm.mpr h.ne')
    simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul,
      one_mul, zero_sub, neg_neg, him]
    exact Real.sqrt_pos.mpr (by linarith)

/-- The principal square root of `-w` for `w` in the lower half-plane. -/
private lemma hypR4_sqrt_neg_of_im_neg {w : ℂ} (h : w.im < 0) :
    Complex.sqrt (-w) = I*Complex.sqrt w := by
  apply hypR4_sqrt_eq_of_sq
  · rw [mul_pow, trig_sqrt_sq]; simp
  · have him : (Complex.sqrt w).im = -Real.sqrt ((‖w‖ - w.re)/2) := by
      rw [Complex.sqrt]; exact Complex.cpow_inv_two_im_eq_neg_sqrt h
    have hlt : w.re < ‖w‖ := lt_of_le_of_lt (le_abs_self _) (Complex.abs_re_lt_norm.mpr h.ne)
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, him, neg_neg]
    exact Real.sqrt_pos.mpr (by linarith)

/-- The principal logarithm of `-u` for `u` in the upper half-plane. -/
private lemma hypR4_log_neg_of_im_pos {u : ℂ} (h : 0 < u.im) :
    Complex.log (-u) = Complex.log u - π*I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_sub_pi_of_im_pos h]

/-- The principal logarithm of `-u` for `u` in the lower half-plane. -/
private lemma hypR4_log_neg_of_im_neg {u : ℂ} (h : u.im < 0) :
    Complex.log (-u) = Complex.log u + π*I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_add_pi_of_im_neg h]

/-- Imaginary part of a principal square root has the sign of the imaginary part. -/
private lemma hypR4_sqrt_im_nonneg {w : ℂ} (h : 0 ≤ w.im) : 0 ≤ (Complex.sqrt w).im := by
  rw [Complex.sqrt, Complex.cpow_inv_two_im_eq_sqrt h]; exact Real.sqrt_nonneg _

/-- Imaginary part of a principal square root in the lower half-plane. -/
private lemma hypR4_sqrt_im_nonpos {w : ℂ} (h : w.im < 0) : (Complex.sqrt w).im ≤ 0 := by
  rw [Complex.sqrt, Complex.cpow_inv_two_im_eq_neg_sqrt h]
  exact neg_nonpos.mpr (Real.sqrt_nonneg _)

/-- Real part of a principal square root is nonnegative. -/
private lemma hypR4_sqrt_re_nonneg (w : ℂ) : 0 ≤ (Complex.sqrt w).re := by
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
    rw [hypR4_sqrt_neg_of_im_neg h1, hypR4_sqrt_neg_of_im_neg h2]
    simp only [not_lt.mpr hn.le, ↓reduceIte]
    have hu : (z + Complex.sqrt (z-1)*Complex.sqrt (z+1)).im < 0 := by
      have a1 := hypR4_sqrt_re_nonneg (z-1)
      have a2 := hypR4_sqrt_re_nonneg (z+1)
      have b1 := hypR4_sqrt_im_nonpos h2
      have b2 := hypR4_sqrt_im_nonpos h1
      simp only [Complex.add_im, Complex.mul_im]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos a1 b2, mul_nonpos_of_nonneg_of_nonpos a2 b1]
    have hx : -z + I*Complex.sqrt (z+1)*(I*Complex.sqrt (z-1)) =
        -(z + Complex.sqrt (z-1)*Complex.sqrt (z+1)) := by
      linear_combination Complex.sqrt (z+1)*Complex.sqrt (z-1)*hI
    rw [hx, hypR4_log_neg_of_im_neg hu]
    ring
  · have h1 : 0 < (z+1).im := by simpa using hp
    have h2 : 0 < (z-1).im := by simpa using hp
    rw [hypR4_sqrt_neg_of_im_pos h1, hypR4_sqrt_neg_of_im_pos h2]
    simp only [hp, ↓reduceIte]
    have hu : 0 < (z + Complex.sqrt (z-1)*Complex.sqrt (z+1)).im := by
      have a1 := hypR4_sqrt_re_nonneg (z-1)
      have a2 := hypR4_sqrt_re_nonneg (z+1)
      have b1 := hypR4_sqrt_im_nonneg h2.le
      have b2 := hypR4_sqrt_im_nonneg h1.le
      simp only [Complex.add_im, Complex.mul_im]
      nlinarith [mul_nonneg a1 b2, mul_nonneg a2 b1]
    have hx : -z + -I*Complex.sqrt (z+1)*(-I*Complex.sqrt (z-1)) =
        -(z + Complex.sqrt (z-1)*Complex.sqrt (z+1)) := by
      linear_combination Complex.sqrt (z+1)*Complex.sqrt (z-1)*hI
    rw [hx, hypR4_log_neg_of_im_pos hu]
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
  · have : ¬ 0 < (z⁻¹).im := by rw [him]; exact not_lt.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith) hn.le)
    simp only [this, h, ↓reduceIte]; ring

/-- Identity under the stated parameter and domain assumptions: `arcsinh z=Complex.log
(Complex.sqrt (z^2+1)+z)`. -/
@[dlmf 4.37.E16]
theorem arcsinh_log {z : ℂ} (hz : z ∈ arcsinhDomain) : arcsinh z=Complex.log (Complex.sqrt (z^2+1)+z) := by
  rfl

/-- The principal square root is continuous off the open negative real axis. -/
private lemma hypR4_sqrt_continuousAt {w : ℂ} (h : 0 ≤ w.re ∨ w.im ≠ 0) :
    ContinuousAt Complex.sqrt w := by
  have := Complex.continuousAt_cpow_const_of_re_pos (w := (2⁻¹:ℂ)) h (by norm_num)
  exact this

/-- One-sided limit of the principal square root at the cut, from the upper half-plane. -/
private lemma hypR4_sqrt_tendsto_upper {f : ℝ → ℂ} {l : Filter ℝ} {w₀ : ℂ}
    (hf : Tendsto f l (𝓝 w₀)) (hre : w₀.re ≤ 0) (him : ∀ᶠ ε in l, 0 < (f ε).im) :
    Tendsto (fun ε => Complex.sqrt (f ε)) l (𝓝 (I*Complex.sqrt (-w₀))) := by
  have hc := ((hypR4_sqrt_continuousAt (w := -w₀) (Or.inl (by simp; linarith))).tendsto.comp
    hf.neg).const_mul I
  refine hc.congr' (him.mono fun ε hε => ?_)
  simp only [Function.comp_apply]
  rw [hypR4_sqrt_neg_of_im_pos hε]
  linear_combination (-(Complex.sqrt (f ε))) * (by simp : (I:ℂ)^2 = -1)

/-- One-sided limit of the principal square root at the cut, from the lower half-plane. -/
private lemma hypR4_sqrt_tendsto_lower {f : ℝ → ℂ} {l : Filter ℝ} {w₀ : ℂ}
    (hf : Tendsto f l (𝓝 w₀)) (hre : w₀.re ≤ 0) (him : ∀ᶠ ε in l, (f ε).im < 0) :
    Tendsto (fun ε => Complex.sqrt (f ε)) l (𝓝 (-I*Complex.sqrt (-w₀))) := by
  have hc := ((hypR4_sqrt_continuousAt (w := -w₀) (Or.inl (by simp; linarith))).tendsto.comp
    hf.neg).const_mul (-I)
  refine hc.congr' (him.mono fun ε hε => ?_)
  simp only [Function.comp_apply]
  rw [hypR4_sqrt_neg_of_im_neg hε]
  linear_combination (-(Complex.sqrt (f ε))) * (by simp : (I:ℂ)^2 = -1)

/-- Limits of the principal logarithm at a point `i t` of the positive imaginary axis. -/
private lemma hypR4_tendsto_log_I {g : ℝ → ℂ} {l : Filter ℝ} {t : ℝ} (ht : 0 < t)
    (hg : Tendsto g l (𝓝 (I*t))) :
    Tendsto (fun ε => Complex.log (g ε)) l (𝓝 (Real.log t + π/2*I)) := by
  have hs : I*(t:ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; right; simp [ht.ne']
  have h := (continuousAt_clog hs).tendsto.comp hg
  rw [Complex.log_mul_ofReal _ ht _ Complex.I_ne_zero, Complex.log_I] at h
  exact h

/-- Limits of the principal logarithm at a point `-i t` of the negative imaginary axis. -/
private lemma hypR4_tendsto_log_negI {g : ℝ → ℂ} {l : Filter ℝ} {t : ℝ} (ht : 0 < t)
    (hg : Tendsto g l (𝓝 (-I*t))) :
    Tendsto (fun ε => Complex.log (g ε)) l (𝓝 (Real.log t - π/2*I)) := by
  have hs : -I*(t:ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; right; simp [ht.ne']
  have h := (continuousAt_clog hs).tendsto.comp hg
  rw [Complex.log_mul_ofReal _ ht _ (neg_ne_zero.mpr Complex.I_ne_zero), Complex.log_neg_I] at h
  have e : (Real.log t:ℂ) - π/2*I = Real.log t + -(π/2)*I := by ring
  rw [e]; exact h

/-- The quantity `ε + i y` tends to `i y` along any filter tending to zero. -/
private lemma hypR4_tendsto_line {l : Filter ℝ} (hl : l ≤ 𝓝 0) (c : ℂ) :
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
  have hsq : Complex.sqrt (-((I*(y:ℂ))^2+1)) = r := by rw [hw, hyper_sqrt_ofReal _ (by nlinarith)]
  have hinv : y - r = (r+y)⁻¹ := eq_inv_of_mul_eq_one_left (by linear_combination -hr2)
  have hz : ∀ {l : Filter ℝ}, l ≤ 𝓝 0 →
      Tendsto (fun ε : ℝ => ((ε:ℂ)+I*y)^2+1) l (𝓝 ((I*(y:ℂ))^2+1)) := fun hl =>
    ((hypR4_tendsto_line hl (I*y)).pow 2).add_const 1
  have hw0 : ((I*(y:ℂ))^2+1).re ≤ 0 := by simp [pow_two]; nlinarith
  constructor
  · have him : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < (((ε:ℂ)+I*y)^2+1).im :=
      eventually_mem_nhdsWithin.mono fun ε (hε : 0 < ε) => by
        simp [pow_two]; nlinarith
    have hs := hypR4_sqrt_tendsto_upper (hz nhdsWithin_le_nhds) hw0 him
    rw [hsq] at hs
    have hg := hs.add (hypR4_tendsto_line nhdsWithin_le_nhds (I*y))
    have := hypR4_tendsto_log_I (t := r+y) (by linarith) (by convert hg using 2; push_cast; ring)
    have e : (π*I/2+((Real.log (Real.sqrt (y^2-1)+y)):ℂ)) = (Real.log (r+y) + π/2*I) := by
      rw [← hr]; ring
    rw [e]; exact this
  · have him : ∀ᶠ ε in 𝓝[<] (0:ℝ), (((ε:ℂ)+I*y)^2+1).im < 0 :=
      eventually_mem_nhdsWithin.mono fun ε (hε : ε < 0) => by
        simp [pow_two]; nlinarith
    have hs := hypR4_sqrt_tendsto_lower (hz nhdsWithin_le_nhds) hw0 him
    rw [hsq] at hs
    have hg := hs.add (hypR4_tendsto_line nhdsWithin_le_nhds (I*y))
    have := hypR4_tendsto_log_I (t := y-r) (by linarith) (by convert hg using 2; push_cast; ring)
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
  have hsq : Complex.sqrt (-((I*(y:ℂ))^2+1)) = r := by rw [hw, hyper_sqrt_ofReal _ (by nlinarith)]
  have hinv : -y - r = (r-y)⁻¹ := eq_inv_of_mul_eq_one_left (by linear_combination -hr2)
  have hz : ∀ {l : Filter ℝ}, l ≤ 𝓝 0 →
      Tendsto (fun ε : ℝ => ((ε:ℂ)+I*y)^2+1) l (𝓝 ((I*(y:ℂ))^2+1)) := fun hl =>
    ((hypR4_tendsto_line hl (I*y)).pow 2).add_const 1
  have hw0 : ((I*(y:ℂ))^2+1).re ≤ 0 := by simp [pow_two]; nlinarith
  constructor
  · have him : ∀ᶠ ε in 𝓝[>] (0:ℝ), (((ε:ℂ)+I*y)^2+1).im < 0 :=
      eventually_mem_nhdsWithin.mono fun ε (hε : 0 < ε) => by
        simp [pow_two]; nlinarith
    have hs := hypR4_sqrt_tendsto_lower (hz nhdsWithin_le_nhds) hw0 him
    rw [hsq] at hs
    have hg := hs.add (hypR4_tendsto_line nhdsWithin_le_nhds (I*y))
    have := hypR4_tendsto_log_negI (t := r-y) (by linarith) (by convert hg using 2; push_cast; ring)
    have e : (-π*I/2+((Real.log (Real.sqrt (y^2-1)-y)):ℂ)) = (Real.log (r-y) - π/2*I) := by
      rw [← hr]; ring
    rw [e]; exact this
  · have him : ∀ᶠ ε in 𝓝[<] (0:ℝ), 0 < (((ε:ℂ)+I*y)^2+1).im :=
      eventually_mem_nhdsWithin.mono fun ε (hε : ε < 0) => by
        simp [pow_two]; nlinarith
    have hs := hypR4_sqrt_tendsto_upper (hz nhdsWithin_le_nhds) hw0 him
    rw [hsq] at hs
    have hg := hs.add (hypR4_tendsto_line nhdsWithin_le_nhds (I*y))
    have := hypR4_tendsto_log_negI (t := -y-r) (by linarith) (by convert hg using 2; push_cast; ring)
    have e : (-π*I/2-((Real.log (Real.sqrt (y^2-1)-y)):ℂ)) = (Real.log (-y-r) - π/2*I) := by
      rw [← hr, hinv, Real.log_inv]; push_cast; ring
    rw [e]; exact this

/-- The right half of the inverse-cosh domain is star-convex about `2`. -/
private lemma hypR4_acosh_right_starConvex :
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
private lemma hypR4_acosh_root_pos {z : ℂ} (hz : z ∈ arccoshDomain) (hre : 0 < z.re) :
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
    (hypR4_acosh_right_starConvex.isPathConnected h2V).isConnected.isPreconnected
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
    obtain ⟨h1, h2⟩ := hypR4_acosh_slit hw.1
    exact (((Complex.differentiableAt_sqrt h1).comp w (differentiableAt_id.sub_const 1)).mul
      ((Complex.differentiableAt_sqrt h2).comp w (differentiableAt_id.add_const 1))).differentiableWithinAt
  have hs : AnalyticOnNhd ℂ (fun w => Complex.sqrt (w^2-1)) V := by
    apply DifferentiableOn.analyticOnNhd _ hVo
    intro w hw
    exact ((Complex.differentiableAt_sqrt (hslit w hw)).comp w
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w^2-1) w)).differentiableWithinAt
  have h1 : Complex.sqrt 1 = 1 := by simp [Complex.sqrt]
  refine hypR4_sq_eq_continuation hVo hVc hr hs ?_ h2V ?_ ?_ z ⟨hz, hre⟩
  · intro w _; rw [mul_pow, trig_sqrt_sq, trig_sqrt_sq, trig_sqrt_sq]; ring
  · norm_num [h1]
  · intro h
    have := trig_sqrt_sq ((2:ℂ)^2-1)
    rw [h] at this; norm_num at this

/-- The factored inverse-cosh root is `±√(z²-1)` according to the sign of `Re z`. -/
lemma hypR4_acosh_root_signed {z : ℂ} (hz : z ∈ arccoshDomain) (hre : z.re ≠ 0) :
    Complex.sqrt (z-1)*Complex.sqrt (z+1) = (if 0<z.re then 1 else -1)*Complex.sqrt (z^2-1) := by
  rcases lt_or_gt_of_ne hre with hneg | hpos
  · simp only [show ¬ (0 < z.re) from not_lt.mpr hneg.le, ↓reduceIte]
    have him : z.im ≠ 0 := by
      rcases hz with h | h
      · exact h
      · linarith
    have hz' : -z ∈ arccoshDomain := Or.inl (by simpa using him)
    have h := hypR4_acosh_root_pos hz' (by simpa using hneg)
    rw [show (-z)^2-1 = z^2-1 by ring, show -z-1 = -(z+1) by ring,
      show -z+1 = -(z-1) by ring] at h
    rcases lt_or_gt_of_ne him with hi | hi
    · rw [hypR4_sqrt_neg_of_im_neg (by simpa using hi), hypR4_sqrt_neg_of_im_neg (by simpa using hi)] at h
      rw [← h]; linear_combination (Complex.sqrt (z-1)*Complex.sqrt (z+1))*Complex.I_sq
    · rw [hypR4_sqrt_neg_of_im_pos (by simpa using hi), hypR4_sqrt_neg_of_im_pos (by simpa using hi)] at h
      rw [← h]; linear_combination (Complex.sqrt (z-1)*Complex.sqrt (z+1))*Complex.I_sq
  · simp only [hpos, ↓reduceIte, one_mul]; exact hypR4_acosh_root_pos hz hpos

/-- Identity under the stated parameter and domain assumptions: `arccosh z=Complex.log ((if 0<z.re
then 1 else -1)*Complex.sqrt (z^2-1)+z)`. -/
@[dlmf 4.37.E19]
theorem arccosh_log {z : ℂ} (hz : z ∈ arccoshDomain) (hre : z.re≠0) :
    arccosh z=Complex.log ((if 0<z.re then 1 else -1)*Complex.sqrt (z^2-1)+z) := by
  rw [arccosh, hypR4_acosh_root_signed hz hre, add_comm]

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
    rw [hSdef, mul_pow, trig_sqrt_sq, trig_sqrt_sq]
    have : ((r:ℂ))^2 = ((y^2+1:ℝ):ℂ) := by rw [← Complex.ofReal_pow, hr2]
    rw [this]; push_cast; linear_combination (y:ℂ)^2*hI
  have hfac : (S - I*r)*(S + I*r) = 0 := by linear_combination hS2 - (r:ℂ)^2*hI
  unfold arccosh
  rw [← hSdef]
  have a1 := hypR4_sqrt_re_nonneg (I*y-1)
  have a2 := hypR4_sqrt_re_nonneg (I*y+1)
  rcases lt_or_gt_of_ne hy with hn | hp
  · have h1 : (I*y+1).im < 0 := by simpa using hn
    have h2 : (I*y-1).im < 0 := by simpa using hn
    have b1 := hypR4_sqrt_im_nonpos h2
    have b2 := hypR4_sqrt_im_nonpos h1
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
    have b1 := hypR4_sqrt_im_nonneg h2.le
    have b2 := hypR4_sqrt_im_nonneg h1.le
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
private lemma hypR4_sqrt_re_pos {w : ℂ} (h : w.im ≠ 0 ∨ 0 < w.re) : 0 < (Complex.sqrt w).re := by
  rw [Complex.sqrt, Complex.cpow_inv_two_re]
  apply Real.sqrt_pos.mpr
  rcases h with h | h
  · have := Complex.abs_re_lt_norm.mpr h
    linarith [neg_abs_le w.re]
  · linarith [Complex.re_le_norm w]

/-- Halving under the principal square root. -/
private lemma hypR4_sqrt_half {w : ℂ} (_h : w.im ≠ 0 ∨ 0 < w.re) :
    Complex.sqrt (w/2) = Complex.sqrt w*((Real.sqrt 2)⁻¹:ℝ) := by
  have hs := Complex.sqrt_ofReal_mul (by norm_num : (0:ℝ)≤1/2) w
  simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
    Real.sqrt_div, Real.sqrt_one, Real.sqrt_inv, one_div, one_mul, Complex.ofReal_inv, mul_comm,
    div_eq_mul_inv] using hs

/-- `log (u²) = 2 log u` in the open right half-plane. -/
private lemma hypR4_log_sq_of_re_pos {u : ℂ} (h : 0 < u.re) :
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
    rw [hypR4_sqrt_half hp, hypR4_sqrt_half hm]; ring
  have hre : 0 < (Complex.sqrt ((z+1)/2)+Complex.sqrt ((z-1)/2)).re := by
    rw [Complex.add_re]
    have := hypR4_sqrt_re_pos (show ((z+1)/2).im ≠ 0 ∨ 0 < ((z+1)/2).re by
      rcases hp with h | h
      · left; simpa using h
      · right; simp; linarith [show 0 < (z+1).re from h, show (z+1).re = z.re+1 by simp])
    linarith [hypR4_sqrt_re_nonneg ((z-1)/2)]
  rw [← hypR4_log_sq_of_re_pos hre, hsum, mul_pow, h2, add_sq, trig_sqrt_sq, trig_sqrt_sq]
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
    have := (hypR4_sqrt_continuousAt (w := ((x+1:ℝ):ℂ)) (Or.inl (by simp; linarith))).tendsto.comp hc
    rwa [hyper_sqrt_ofReal _ (by linarith)] at this
  have hm : Tendsto (fun ε : ℝ => (x:ℂ)+I*ε-1) (𝓝 0) (𝓝 ((x:ℂ)-1)) := by
    have : Continuous (fun ε : ℝ => (x:ℂ)+I*ε-1) := by fun_prop
    simpa using this.tendsto 0
  have hlin : Tendsto (fun ε : ℝ => (x:ℂ)+I*ε) (𝓝 0) (𝓝 (x:ℂ)) := by
    have : Continuous (fun ε : ℝ => (x:ℂ)+I*ε) := by fun_prop
    simpa using this.tendsto 0
  have hmre : ((x:ℂ)-1).re ≤ 0 := by simp; linarith
  have hneg : Complex.sqrt (-((x:ℂ)-1)) = (Real.sqrt (1-x):ℂ) := by
    rw [show -((x:ℂ)-1) = ((1-x:ℝ):ℂ) by push_cast; ring, hyper_sqrt_ofReal _ (by linarith)]
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
    have h1 := hypR4_sqrt_tendsto_upper (hm.mono_left nhdsWithin_le_nhds) hmre him
    rw [hneg] at h1
    have hg := (hlin.mono_left nhdsWithin_le_nhds).add (h1.mul (hp.mono_left nhdsWithin_le_nhds))
    have := (continuousAt_clog hslit).tendsto.comp
      (show Tendsto _ _ (𝓝 (I*(s:ℂ)+x)) by
        convert hg using 2; rw [← hprod]; push_cast; ring)
    exact this
  · have him : ∀ᶠ ε : ℝ in 𝓝[<] (0:ℝ), ((x:ℂ)+I*(ε:ℂ)-1).im < 0 :=
      eventually_mem_nhdsWithin.mono fun ε (hε : ε < 0) => by simpa using hε
    have h1 := hypR4_sqrt_tendsto_lower (hm.mono_left nhdsWithin_le_nhds) hmre him
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
private lemma hypR4_tendsto_log_cut_upper {g : ℝ → ℂ} {l : Filter ℝ} {t : ℝ} (ht : t < 0)
    (hg : Tendsto g l (𝓝 (t:ℂ))) (him : ∀ᶠ ε in l, 0 ≤ (g ε).im) :
    Tendsto (fun ε => Complex.log (g ε)) l (𝓝 (Real.log (-t) + π*I)) := by
  have h := (Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
    (z := (t:ℂ)) (by simpa using ht) (by simp)).comp (tendsto_nhdsWithin_iff.mpr ⟨hg, him⟩)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg ht] at h
  exact h

/-- One-sided limit of the principal logarithm at the negative real axis, from below. -/
private lemma hypR4_tendsto_log_cut_lower {g : ℝ → ℂ} {l : Filter ℝ} {t : ℝ} (ht : t < 0)
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
    rw [show -((x:ℂ)-1) = ((1-x:ℝ):ℂ) by push_cast; ring, hyper_sqrt_ofReal _ (by linarith)]
  have hneg2 : Complex.sqrt (-((x:ℂ)+1)) = (Real.sqrt (-1-x):ℂ) := by
    rw [show -((x:ℂ)+1) = ((-1-x:ℝ):ℂ) by push_cast; ring, hyper_sqrt_ofReal _ (by linarith)]
  have hxr : x - r < 0 := by linarith
  have hI : (I:ℂ)^2 = -1 := by simp
  constructor
  · have him1 : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), 0 < ((x:ℂ)+I*(ε:ℂ)-1).im :=
      eventually_mem_nhdsWithin.mono fun ε (hε : 0 < ε) => by simpa using hε
    have him2 : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), 0 < ((x:ℂ)+I*(ε:ℂ)+1).im :=
      eventually_mem_nhdsWithin.mono fun ε (hε : 0 < ε) => by simpa using hε
    have h1 := hypR4_sqrt_tendsto_upper (hm.mono_left nhdsWithin_le_nhds) hmre him1
    have h2 := hypR4_sqrt_tendsto_upper (hp.mono_left nhdsWithin_le_nhds) hpre him2
    rw [hneg1] at h1; rw [hneg2] at h2
    have hg := (hlin.mono_left nhdsWithin_le_nhds).add (h1.mul h2)
    have hgim : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), 0 ≤ ((x:ℂ)+I*(ε:ℂ) +
        Complex.sqrt ((x:ℂ)+I*(ε:ℂ)-1)*Complex.sqrt ((x:ℂ)+I*(ε:ℂ)+1)).im :=
      (him1.and him2).mono fun ε ⟨e1, e2⟩ => by
        have a1 := hypR4_sqrt_re_nonneg ((x:ℂ)+I*(ε:ℂ)-1)
        have a2 := hypR4_sqrt_re_nonneg ((x:ℂ)+I*(ε:ℂ)+1)
        have b1 := hypR4_sqrt_im_nonneg e1.le
        have b2 := hypR4_sqrt_im_nonneg e2.le
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
    have := hypR4_tendsto_log_cut_upper hxr hg' hgim
    have e : (π*I+(Real.log (Real.sqrt (x^2-1)-x):ℂ)) = Real.log (-(x-r)) + π*I := by
      rw [← hr]; ring_nf
    rw [e]; exact this
  · have him1 : ∀ᶠ ε : ℝ in 𝓝[<] (0:ℝ), ((x:ℂ)+I*(ε:ℂ)-1).im < 0 :=
      eventually_mem_nhdsWithin.mono fun ε (hε : ε < 0) => by simpa using hε
    have him2 : ∀ᶠ ε : ℝ in 𝓝[<] (0:ℝ), ((x:ℂ)+I*(ε:ℂ)+1).im < 0 :=
      eventually_mem_nhdsWithin.mono fun ε (hε : ε < 0) => by simpa using hε
    have h1 := hypR4_sqrt_tendsto_lower (hm.mono_left nhdsWithin_le_nhds) hmre him1
    have h2 := hypR4_sqrt_tendsto_lower (hp.mono_left nhdsWithin_le_nhds) hpre him2
    rw [hneg1] at h1; rw [hneg2] at h2
    have hg := (hlin.mono_left nhdsWithin_le_nhds).add (h1.mul h2)
    have hgim : ∀ᶠ ε : ℝ in 𝓝[<] (0:ℝ), ((x:ℂ)+I*(ε:ℂ) +
        Complex.sqrt ((x:ℂ)+I*(ε:ℂ)-1)*Complex.sqrt ((x:ℂ)+I*(ε:ℂ)+1)).im < 0 :=
      (him1.and him2).mono fun ε ⟨e1, e2⟩ => by
        have a1 := hypR4_sqrt_re_nonneg ((x:ℂ)+I*(ε:ℂ)-1)
        have a2 := hypR4_sqrt_re_nonneg ((x:ℂ)+I*(ε:ℂ)+1)
        have b1 := hypR4_sqrt_im_nonpos e1
        have b2 := hypR4_sqrt_im_nonpos e2
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
    have := hypR4_tendsto_log_cut_lower hxr hg' hgim
    have e : (-π*I+(Real.log (Real.sqrt (x^2-1)-x):ℂ)) = Real.log (-(x-r)) - π*I := by
      rw [← hr]; ring_nf
    rw [e]; exact this

/-- Identity under the stated parameter and domain assumptions: `arctanh z=Complex.log
((1+z)/(1-z))/2`. -/
@[dlmf 4.37.E24]
theorem arctanh_log {z : ℂ} (hz : z ∈ arctanhDomain) : arctanh z=Complex.log ((1+z)/(1-z))/2 := by
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
    have h := hypR4_tendsto_log_cut_upper ht (hcont.mono_left nhdsWithin_le_nhds) hev
    have := h.div_const 2
    rw [e] at this
    have e2 : (π*I/2+(Real.log ((x+1)/(x-1)):ℂ)/2) = ((Real.log ((x+1)/(x-1)):ℂ) + π*I)/2 := by
      ring
    rw [e2]; exact this
  · have hev : ∀ᶠ ε : ℝ in 𝓝[<] (0:ℝ), ((1+((x:ℂ)+I*ε))/(1-((x:ℂ)+I*ε))).im < 0 :=
      eventually_mem_nhdsWithin.mono fun ε (hε : ε < 0) => by
        rw [him]; exact div_neg_of_neg_of_pos (by linarith) (hnsq ε)
    have h := hypR4_tendsto_log_cut_lower ht (hcont.mono_left nhdsWithin_le_nhds) hev
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
  simpa only [hyper_sinh_arcsinh] using hyper_sinh_fiber_forms (arcsinh z) w

/-- Identity under the stated parameter and domain assumptions: `Complex.cosh w=z ↔ ∃ k : ℤ,
w=arccosh z+2*(k:ℂ)*π*I ∨ w= -arccosh z+2*(k:ℂ)*π*I`. -/
@[dlmf 4.37.E27, dlmf 4.37.E30]
theorem cosh_inverse_family (z w : ℂ) :
    Complex.cosh w=z ↔ ∃ k : ℤ, w=arccosh z+2*(k:ℂ)*π*I ∨ w= -arccosh z+2*(k:ℂ)*π*I := by
  have hrot:Complex.cosh w=z ↔ Complex.cos (arccosh z*I)=Complex.cos (w*I) := by
    rw [Complex.cos_mul_I,Complex.cos_mul_I,hyper_cosh_arccosh]
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
lemma hypR4_cosh_sinh_exp (w : ℂ) :
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
  have hA := hypR4_arctanh_exp z hz.1 hz.2
  have key : w ∈ arctanhValues z ↔ Complex.exp (2*w) = Complex.exp (2*arctanh z) := by
    obtain ⟨hc, hs⟩ := hypR4_cosh_sinh_exp w
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
private lemma hypR4_acosh_starConvex : StarConvex ℝ (2:ℂ) arccoshDomain := by
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
private lemma hypR4_asech_real {z : ℂ} (hz : z ∈ arcsechDomain) (hy : z.im = 0) :
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
lemma hypR4_asech_root {z : ℂ} (hz : z ∈ arcsechDomain) :
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
    have hc := (hypR4_acosh_starConvex.isPathConnected h2).isConnected.isPreconnected
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
      obtain ⟨h1, h2⟩ := hypR4_asech_real hw hy
      simp [pow_two, Complex.mul_re, hy]; nlinarith
    · by_cases hx : w.re = 0
      · left; simp [pow_two, Complex.mul_re, hx]; nlinarith [sq_nonneg w.im]
      · right; simp [pow_two, Complex.mul_im]
        intro h; apply mul_ne_zero (mul_ne_zero two_ne_zero hx) hy; linear_combination -h
  have hr : AnalyticOnNhd ℂ (fun w => w*(Complex.sqrt (w⁻¹-1)*Complex.sqrt (w⁻¹+1))) arcsechDomain := by
    apply DifferentiableOn.analyticOnNhd _ hVo
    intro w hw
    obtain ⟨h1, h2⟩ := hypR4_acosh_slit hw.2
    have hw0 := hw.1
    exact (differentiableAt_id.mul
      (((Complex.differentiableAt_sqrt h1).comp w
        (by fun_prop (disch := exact hw0) : DifferentiableAt ℂ (fun w : ℂ => w⁻¹-1) w)).mul
      ((Complex.differentiableAt_sqrt h2).comp w
        (by fun_prop (disch := exact hw0) : DifferentiableAt ℂ (fun w : ℂ => w⁻¹+1) w)))).differentiableWithinAt
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
    apply hypR4_sqrt_eq_of_sq
    · rw [mul_pow, trig_sqrt_sq]; norm_num
    · have : 0 < (Complex.sqrt 3).re := by
        rw [Complex.sqrt, Complex.cpow_inv_two_re]
        apply Real.sqrt_pos.mpr; norm_num
      simpa using this
  refine hypR4_sq_eq_continuation hVo hVc hr hs ?_ hhalf hanchor ?_ z hz
  · intro w hw
    have hw0 := hw.1
    rw [mul_pow, mul_pow, trig_sqrt_sq, trig_sqrt_sq, trig_sqrt_sq]; field_simp; ring
  · intro h
    have := trig_sqrt_sq (1-(1/2:ℂ)^2)
    rw [h] at this; norm_num at this

/-- On the inverse-sech domain, `1-z²` lies in the slit plane. -/
lemma hypR4_asech_slit {w : ℂ} (hw : w ∈ arcsechDomain) :
    1-w^2 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hy : w.im = 0
  · left
    obtain ⟨h1, h2⟩ := hypR4_asech_real hw hy
    simp [pow_two, Complex.mul_re, hy]; nlinarith
  · by_cases hx : w.re = 0
    · left; simp [pow_two, Complex.mul_re, hx]; nlinarith [sq_nonneg w.im]
    · right; simp [pow_two, Complex.mul_im]
      intro h; apply mul_ne_zero (mul_ne_zero two_ne_zero hx) hy; linear_combination -h

/-- The interrelation example in §4.37(vi), with compatible principal branches. -/
theorem arcsech_arccoth_interrelation {a : ℂ} (hre : 0<a.re) (ha : a∈arcsechDomain)
    (hr : (Complex.sqrt (1-a^2))⁻¹∈arccothDomain) :
    arcsech a=arccoth ((Complex.sqrt (1-a^2))⁻¹) := by
  have ha0 : a ≠ 0 := ha.1
  set q := Complex.sqrt (1-a^2) with hqdef
  have hq2 : q^2 = 1-a^2 := trig_sqrt_sq _
  have hqre : 0 ≤ q.re := by
    rw [hqdef, Complex.sqrt, Complex.cpow_inv_two_re]; exact Real.sqrt_nonneg _
  have hq0 : q ≠ 0 := by
    intro h; rw [h] at hq2
    exact Complex.slitPlane_ne_zero (hypR4_asech_slit ha) (by rw [← hq2]; ring)
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
    have e := hypR4_asech_root ha
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
    linarith [hypR4_sqrt_re_pos (Or.inr hp), hypR4_sqrt_re_nonneg ((z-1)/2)]
  have hlog := hypR4_log_sq_of_re_pos hre
  rw [hs,hs,add_sq,mul_pow,mul_pow,hc2,trig_sqrt_sq,trig_sqrt_sq] at hlog
  unfold arccosh arcsinh
  rw [trig_sqrt_sq,show (z-1)/2+1=(z+1)/2 by ring]
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
  rw [← hyper_arcsinh_rotation] at h
  convert h using 1
  ext n
  rw [mul_pow, pow_add, pow_mul, pow_add, pow_mul, show (-I:ℂ)^2 = -1 by simp, pow_one]
  dsimp only [hyperbolicCentral]
  simp only [div_eq_mul_inv, mul_inv_rev]
  linear_combination ((2*n).choose n:ℂ)*(-1:ℂ)^n*z^(2*n)*z*(4^n:ℂ)⁻¹*(2*n+1:ℂ)⁻¹*Complex.I_sq

/-- The central-binomial power series of the principal inverse hyperbolic sine
on the open unit disk, obtained by rotating the principal arcsine expansion. -/
@[dlmf 4.38.E1]
theorem hasSum_arcsinh {z : ℂ} (hz : ‖z‖<1) : HasSum (fun n : ℕ => (-1:ℂ)^n*hyperbolicCentral n/(2*n+1:ℂ)*z^(2*n+1)) (arcsinh z) := by
  exact hasSum_arcsinh_closed_disk hz.le

/-- The series with terms `(fun n : ℕ => (-1:ℂ)^n*hyperbolicCentral (n+1)/((2*n+2:ℂ)*z^(2*n+2)))`
converges to `(arcsinh z-Complex.log (2*z))`. -/
@[dlmf 4.38.E2]
theorem hasSum_arcsinh_large {z : ℂ} (hz : 0<z.re) (hn : 1<‖z‖) : HasSum (fun n : ℕ => (-1:ℂ)^n*hyperbolicCentral (n+1)/((2*n+2:ℂ)*z^(2*n+2))) (arcsinh z-Complex.log (2*z)) := by
  sorry

/-- The series with terms `(fun n : ℕ => hyperbolicCentral (n+1)/((2*n+2:ℂ)*z^(2*n+2)))` converges
to `(Complex.log (2*z)-arccosh z)`. -/
@[dlmf 4.38.E3]
theorem hasSum_arccosh_large {z : ℂ} (hn : 1<‖z‖) : HasSum (fun n : ℕ => hyperbolicCentral (n+1)/((2*n+2:ℂ)*z^(2*n+2))) (Complex.log (2*z)-arccosh z) := by
  sorry

/-- The principal inverse-cosh expansion about one after factoring the square root.
The series converges on the stated closed disk in the right half-plane, with
its removable value at one assigned explicitly. -/
@[dlmf 4.38.E4]
theorem hasSum_arccosh_near_one {z : ℂ} (hz : 0<z.re) (hn : ‖z-1‖≤2) : HasSum (fun n : ℕ => (-1:ℂ)^n*hyperbolicCentral n/((2:ℂ)^n*(2*n+1:ℂ))*(z-1)^n) (if z=1 then 1 else arccosh z/Complex.sqrt (2*(z-1))) := by
  by_cases hz1 : z=1
  · subst z
    convert hasSum_ite_eq (0:ℕ) (1:ℂ) using 1
    · funext n
      by_cases hn : n=0
      · simp [hn,hyperbolicCentral]
      · simp [hn]
    · simp
  let w := Complex.sqrt ((z-1)/2)
  have hw2 : w^2=(z-1)/2 := trig_sqrt_sq _
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
