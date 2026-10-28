/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Continuation

/-!
# The loop integral for `₂F₁` (DLMF 15.6.2, Temme §5.2.2)

DLMF 15.6.2 represents `F(a,b;c;z)/Γ(c)` by an integral over a loop that starts at `t = 0`,
encircles `t = 1` once in the positive sense and returns to `0`, with `t^{b-1}` and `(t-1)^{c-b-1}`
taking their principal values where the loop crosses the positive real axis beyond `1`. We use the
explicit loop of radius `0 < ρ < 1` about `1`: the segment `[0, 1-ρ]` below the cut, where
`(t-1)^{c-b-1} = (1-t)^{c-b-1} e^{-πi(c-b-1)}`, the circle `t = 1 + ρ e^{iθ}`, `-π < θ < π`, and the
segment back above the cut, where `(t-1)^{c-b-1} = (1-t)^{c-b-1} e^{πi(c-b-1)}`
(`hypergeometricLoop`).

In the coordinate `w = log (t-1)` the loop becomes three sides of a rectangle, so Cauchy's theorem
for rectangles shows that the loop integral does not depend on `ρ`. For `re (c-b) > 0` the
circle contributes nothing as `ρ → 0`, and the two segments give `-2i sin(π(c-b-1))` times Euler's
integral 15.6.1. Analytic continuation in `c` removes the restriction.
-/

@[expose] public section

open Complex Filter Set MeasureTheory intervalIntegral
open scoped Topology Real Interval

noncomputable section

namespace DLMF.Hypergeometric

/-- The integrand on the segments of the loop: below the cut (`s = -1`) and above it (`s = 1`). -/
def loopSegIntegrand (a b c z s : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (b - 1) * ((1 - t : ℝ) : ℂ) ^ (c - b - 1) * exp (s * π * I * (c - b - 1)) *
    (1 - z * t) ^ (-a)

/-- The integrand on the circle `t = 1 + ρ e^{iθ}`, including `dt = iρ e^{iθ} dθ`. -/
def loopCircIntegrand (a b c z : ℂ) (ρ θ : ℝ) : ℂ :=
  (1 + ρ * exp (θ * I)) ^ (b - 1) * ((ρ : ℂ) ^ (c - b - 1) * exp (θ * I * (c - b - 1))) *
    (1 - z * (1 + ρ * exp (θ * I))) ^ (-a) * (I * ρ * exp (θ * I))

/-- **The loop integral** `∫₀^{(1+)} t^{b-1} (t-1)^{c-b-1} (1-zt)^{-a} dt` of DLMF 15.6.2 over the
loop of radius `ρ` about `1`. -/
def hypergeometricLoop (a b c z : ℂ) (ρ : ℝ) : ℂ :=
  (∫ t in (0 : ℝ)..(1 - ρ), loopSegIntegrand a b c z (-1) t) +
    (∫ θ in (-π)..π, loopCircIntegrand a b c z ρ θ) -
    ∫ t in (0 : ℝ)..(1 - ρ), loopSegIntegrand a b c z 1 t

/-- The integrand in the coordinate `w = log (t - 1)`. -/
def loopLogIntegrand (a b c z : ℂ) (w : ℂ) : ℂ :=
  (1 + exp w) ^ (b - 1) * exp ((c - b - 1) * w) * (1 - z * (1 + exp w)) ^ (-a) * exp w

/-- `(eˣ)^s = e^{s x}` for real `x`. -/
theorem ofReal_exp_cpow (x : ℝ) (s : ℂ) : ((Real.exp x : ℝ) : ℂ) ^ s = exp (s * x) := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'), ofReal_exp, log_exp]
  · ring
  · simp [Real.pi_pos]
  · simp [Real.pi_pos.le]

/-- `ρ^s = e^{s log ρ}` for real `ρ > 0`. -/
theorem ofReal_cpow_eq_exp_mul_log {ρ : ℝ} (hρ : 0 < ρ) (s : ℂ) :
    (ρ : ℂ) ^ s = exp (s * Real.log ρ) := by
  rw [← Real.exp_log hρ, ofReal_exp_cpow, Real.log_exp]

/-- The log-coordinate integrand is holomorphic where `|e^w| < 1` and `|z| (1 + |e^w|) < 1`. -/
theorem differentiableAt_loopLogIntegrand (a b c z : ℂ) {w : ℂ} (hw : w.re < 0)
    (hz : ‖z‖ * (1 + Real.exp w.re) < 1) : DifferentiableAt ℂ (loopLogIntegrand a b c z) w := by
  have he : ‖exp w‖ = Real.exp w.re := norm_exp w
  have he1 : Real.exp w.re < 1 := (Real.exp_lt_exp.mpr hw).trans_eq Real.exp_zero
  have h1 : 1 + exp w ∈ slitPlane := by
    rw [mem_slitPlane_iff]; left
    have := abs_re_le_norm (exp w)
    rw [add_re, one_re]; rw [he] at this; linarith [neg_abs_le (exp w).re]
  have h2 : 1 - z * (1 + exp w) ∈ slitPlane := by
    rw [mem_slitPlane_iff]; left
    have hn : ‖z * (1 + exp w)‖ < 1 := by
      rw [norm_mul]
      calc ‖z‖ * ‖1 + exp w‖ ≤ ‖z‖ * (1 + Real.exp w.re) := by
            gcongr; exact (norm_add_le _ _).trans (by rw [norm_one, he])
        _ < 1 := hz
    have := abs_re_le_norm (z * (1 + exp w))
    rw [sub_re, one_re]; linarith [le_abs_self (z * (1 + exp w)).re]
  have hA : DifferentiableAt ℂ (fun w : ℂ => 1 + exp w) w :=
    (differentiableAt_const 1).add differentiableAt_exp
  have hB : DifferentiableAt ℂ (fun w : ℂ => 1 - z * (1 + exp w)) w :=
    (differentiableAt_const 1).sub ((differentiableAt_const z).mul hA)
  have hC : DifferentiableAt ℂ (fun w : ℂ => exp ((c - b - 1) * w)) w :=
    ((differentiableAt_const _).mul differentiableAt_id).cexp
  unfold loopLogIntegrand
  exact (((hA.cpow (differentiableAt_const _) h1).mul hC).mul
    (hB.cpow (differentiableAt_const _) h2)).mul differentiableAt_exp

/-- If `‖z‖ |t| < 1`, then `1 - z t` lies in the slit plane. -/
theorem one_sub_mul_ofReal_mem_slitPlane {z : ℂ} {t : ℝ} (h : ‖z‖ * |t| < 1) :
    1 - z * t ∈ slitPlane := by
  rw [mem_slitPlane_iff]; left
  have h1 := abs_re_le_norm (z * t)
  rw [norm_mul, norm_real, Real.norm_eq_abs] at h1
  rw [sub_re, one_re]; linarith [le_abs_self (z * t).re]

/-- The factors of the segment integrand other than `t^{b-1}`. -/
theorem continuousOn_loopSeg_rest (a b c z s : ℂ) {T : ℝ} (hT : T < 1) (hz : ‖z‖ * |T| < 1)
    (hz1 : ‖z‖ < 1) :
    ContinuousOn (fun t : ℝ => ((1 - t : ℝ) : ℂ) ^ (c - b - 1) * exp (s * π * I * (c - b - 1)) *
      (1 - z * t) ^ (-a)) (uIcc 0 T) := by
  intro t ht
  have ht' : t ∈ Icc (min 0 T) (max 0 T) := ht
  have h1 : 0 < 1 - t := by
    have : t ≤ max 0 T := ht'.2
    rcases le_total 0 T with h | h
    · rw [max_eq_right h] at this; linarith
    · rw [max_eq_left h] at this; linarith
  have h2 : ‖z‖ * |t| < 1 := by
    have : |t| ≤ max |T| 1 := by
      rw [abs_le]; constructor
      · have : min 0 T ≤ t := ht'.1
        rcases le_total 0 T with h | h
        · rw [min_eq_left h] at this; linarith [le_max_right |T| 1]
        · rw [min_eq_right h] at this; linarith [neg_abs_le T, le_max_left |T| 1]
      · linarith [le_max_right |T| 1]
    rcases le_total |T| 1 with h | h
    · rw [max_eq_right h] at this
      calc ‖z‖ * |t| ≤ ‖z‖ * 1 := by gcongr
        _ < 1 := by linarith
    · rw [max_eq_left h] at this
      calc ‖z‖ * |t| ≤ ‖z‖ * |T| := by gcongr
        _ < 1 := hz
  refine ContinuousAt.continuousWithinAt ?_
  refine ContinuousAt.mul (ContinuousAt.mul ?_ continuousAt_const) ?_
  · exact ContinuousAt.cpow (by fun_prop) continuousAt_const (ofReal_mem_slitPlane.mpr h1)
  · exact ContinuousAt.cpow (by fun_prop) continuousAt_const (one_sub_mul_ofReal_mem_slitPlane h2)

/-- Regrouping of the segment integrand of the loop integral. -/
theorem loopSegIntegrand_eq (a b c z s : ℂ) (t : ℝ) :
    loopSegIntegrand a b c z s t = (t : ℂ) ^ (b - 1) *
      (((1 - t : ℝ) : ℂ) ^ (c - b - 1) * exp (s * π * I * (c - b - 1)) * (1 - z * t) ^ (-a)) := by
  unfold loopSegIntegrand; ring

/-- For `Re b > 0`, `T < 1` and `‖z‖ |T| < 1`, the segment integrand is integrable on `[0, T]`. -/
theorem intervalIntegrable_loopSegIntegrand (a b c z s : ℂ) (hb : 0 < b.re) {T : ℝ}
    (hT : T < 1) (hz : ‖z‖ * |T| < 1) (hz1 : ‖z‖ < 1) :
    IntervalIntegrable (loopSegIntegrand a b c z s) volume 0 T := by
  have h := (intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := T) (r := b - 1)
    (by simp; linarith)).mul_continuousOn (continuousOn_loopSeg_rest a b c z s hT hz hz1)
  have he : loopSegIntegrand a b c z s = fun t : ℝ => (t : ℂ) ^ (b - 1) *
      (((1 - t : ℝ) : ℂ) ^ (c - b - 1) * exp (s * π * I * (c - b - 1)) * (1 - z * t) ^ (-a)) :=
    funext (loopSegIntegrand_eq a b c z s)
  rw [he]; exact h

/-- The horizontal sides of the rectangle are the differences of the segment integrals. -/
theorem integral_loopLogIntegrand_horizontal (a b c z : ℂ) {s : ℂ} (hs : s = 1 ∨ s = -1)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) (hρ₁1 : ρ₁ < 1) (hρ₂1 : ρ₂ < 1)
    (hz1 : ‖z‖ < 1) :
    ∫ x in (Real.log ρ₁)..(Real.log ρ₂), loopLogIntegrand a b c z (x + (s.re * π : ℝ) * I) =
      ∫ t in (1 - ρ₁)..(1 - ρ₂), loopSegIntegrand a b c z s t := by
  have hexp : exp (((s.re * π : ℝ) : ℂ) * I) = -1 := by
    rcases hs with rfl | rfl
    · simp
    · rw [show (((-1 : ℂ).re * π : ℝ) : ℂ) * I = -(π * I) by simp, exp_neg, exp_pi_mul_I]
      norm_num
  have hcont : ContinuousOn (loopSegIntegrand a b c z s)
      ((fun u : ℝ => 1 - Real.exp u) '' uIcc (Real.log ρ₁) (Real.log ρ₂)) := by
    rintro _ ⟨u, hu, rfl⟩
    have hu' : u ≤ max (Real.log ρ₁) (Real.log ρ₂) := hu.2
    have hu0 : u < 0 := by
      have := Real.log_neg hρ₁ hρ₁1; have := Real.log_neg hρ₂ hρ₂1
      rcases le_total (Real.log ρ₁) (Real.log ρ₂) with h | h
      · rw [max_eq_right h] at hu'; linarith
      · rw [max_eq_left h] at hu'; linarith
    have he0 := Real.exp_pos u
    have he1 : Real.exp u < 1 := (Real.exp_lt_exp.mpr hu0).trans_eq Real.exp_zero
    have ht0 : 0 < 1 - Real.exp u := by linarith
    have ht1 : 0 < 1 - (1 - Real.exp u) := by linarith
    have hzt : ‖z‖ * |1 - Real.exp u| < 1 := by
      rw [abs_of_pos ht0]
      calc ‖z‖ * (1 - Real.exp u) ≤ ‖z‖ * 1 := by gcongr; linarith
        _ < 1 := by linarith
    refine ContinuousAt.continuousWithinAt ?_
    unfold loopSegIntegrand
    refine ContinuousAt.mul (ContinuousAt.mul (ContinuousAt.mul ?_ ?_) continuousAt_const) ?_
    · exact ContinuousAt.cpow (by fun_prop) continuousAt_const (ofReal_mem_slitPlane.mpr ht0)
    · exact ContinuousAt.cpow (by fun_prop) continuousAt_const (ofReal_mem_slitPlane.mpr ht1)
    · exact ContinuousAt.cpow (by fun_prop) continuousAt_const
        (one_sub_mul_ofReal_mem_slitPlane hzt)
  have h := intervalIntegral.integral_deriv_smul_comp' (f := fun u : ℝ => 1 - Real.exp u)
    (f' := fun u : ℝ => -Real.exp u) (g := loopSegIntegrand a b c z s)
    (a := Real.log ρ₁) (b := Real.log ρ₂)
    (fun x _ => by simpa using (Real.hasDerivAt_exp x).const_sub 1)
    (by fun_prop) hcont
  simp only [Real.exp_log hρ₁, Real.exp_log hρ₂] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [Function.comp_apply, Complex.real_smul]
  unfold loopLogIntegrand loopSegIntegrand
  rw [exp_add, hexp, show (1 : ℂ) + exp x * -1 = ((1 - Real.exp x : ℝ) : ℂ) by
      push_cast; ring,
    show ((1 - (1 - Real.exp x) : ℝ) : ℂ) = ((Real.exp x : ℝ) : ℂ) by push_cast; ring,
    ofReal_exp_cpow, ← ofReal_exp]
  have hsre : (s.re : ℂ) = s := by rcases hs with rfl | rfl <;> simp
  rw [show (c - b - 1) * ((x : ℂ) + ((s.re * π : ℝ) : ℂ) * I) =
      (c - b - 1) * x + s * π * I * (c - b - 1) by push_cast; rw [hsre]; ring, exp_add]
  push_cast
  ring

/-- The vertical sides of the rectangle are the circle integrals. -/
theorem I_mul_loopLogIntegrand_vertical (a b c z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) :
    I * loopLogIntegrand a b c z ((Real.log ρ : ℂ) + θ * I) = loopCircIntegrand a b c z ρ θ := by
  unfold loopLogIntegrand loopCircIntegrand
  have hexp : exp ((Real.log ρ : ℂ) + θ * I) = ρ * exp (θ * I) := by
    rw [exp_add, ← ofReal_exp, Real.exp_log hρ]
  rw [hexp, ofReal_cpow_eq_exp_mul_log hρ, mul_add, exp_add]
  ring_nf

/-- **The loop integral does not depend on the radius**, by Cauchy's theorem for the rectangle
`[log ρ₁, log ρ₂] × [-π, π]` in the coordinate `w = log (t - 1)`. -/
theorem hypergeometricLoop_eq (a b c z : ℂ) (hb : 0 < b.re) {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁)
    (hρ₂ : 0 < ρ₂) (hρ₁1 : ρ₁ < 1) (hρ₂1 : ρ₂ < 1) (hz₁ : ‖z‖ * (1 + ρ₁) < 1)
    (hz₂ : ‖z‖ * (1 + ρ₂) < 1) :
    hypergeometricLoop a b c z ρ₁ = hypergeometricLoop a b c z ρ₂ := by
  have hz1 : ‖z‖ < 1 := by nlinarith [norm_nonneg z]
  set G := loopLogIntegrand a b c z
  have hrect := integral_boundary_rect_eq_zero_of_differentiableOn G
    ((Real.log ρ₁ : ℂ) + ((-π : ℝ) : ℂ) * I) ((Real.log ρ₂ : ℂ) + ((π : ℝ) : ℂ) * I)
    (fun w hw => by
      rw [mem_reProdIm] at hw
      have h1 := hw.1
      simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, mul_one,
        sub_zero, add_zero] at h1
      have hwle : w.re ≤ max (Real.log ρ₁) (Real.log ρ₂) := h1.2
      have hl1 := Real.log_neg hρ₁ hρ₁1
      have hl2 := Real.log_neg hρ₂ hρ₂1
      have hw0 : w.re < 0 := lt_of_le_of_lt hwle (max_lt hl1 hl2)
      have hew : Real.exp w.re ≤ max ρ₁ ρ₂ := by
        rcases le_total (Real.log ρ₁) (Real.log ρ₂) with h | h
        · rw [max_eq_right h] at hwle
          exact (Real.exp_le_exp.mpr hwle).trans (by rw [Real.exp_log hρ₂]; exact le_max_right _ _)
        · rw [max_eq_left h] at hwle
          exact (Real.exp_le_exp.mpr hwle).trans (by rw [Real.exp_log hρ₁]; exact le_max_left _ _)
      have hzw : ‖z‖ * (1 + Real.exp w.re) < 1 := by
        rcases le_total ρ₁ ρ₂ with h | h
        · rw [max_eq_right h] at hew
          calc ‖z‖ * (1 + Real.exp w.re) ≤ ‖z‖ * (1 + ρ₂) := by gcongr
            _ < 1 := hz₂
        · rw [max_eq_left h] at hew
          calc ‖z‖ * (1 + Real.exp w.re) ≤ ‖z‖ * (1 + ρ₁) := by gcongr
            _ < 1 := hz₁
      exact (differentiableAt_loopLogIntegrand a b c z hw0 hzw).differentiableWithinAt)
  simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, mul_one, sub_zero,
    add_zero, add_im, mul_im, zero_add, smul_eq_mul] at hrect
  have hbot := integral_loopLogIntegrand_horizontal a b c z (s := -1) (Or.inr rfl) hρ₁ hρ₂
    hρ₁1 hρ₂1 hz1
  have htop := integral_loopLogIntegrand_horizontal a b c z (s := 1) (Or.inl rfl) hρ₁ hρ₂
    hρ₁1 hρ₂1 hz1
  simp only [neg_re, one_re, neg_mul, one_mul] at hbot htop
  rw [show ((-π : ℝ) : ℂ) = ((-π : ℝ) : ℂ) from rfl] at hrect
  push_cast at hbot htop hrect
  rw [hbot, htop] at hrect
  have hvert : ∀ ρ : ℝ, 0 < ρ → I * ∫ θ in (-π)..π, G ((Real.log ρ : ℂ) + θ * I) =
      ∫ θ in (-π)..π, loopCircIntegrand a b c z ρ θ := fun ρ hρ => by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun θ _ => I_mul_loopLogIntegrand_vertical a b c z hρ θ
  rw [hvert ρ₂ hρ₂, hvert ρ₁ hρ₁] at hrect
  -- the segment integrals
  have hT : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ‖z‖ * |1 - ρ| < 1 := fun ρ hρ hρ1 => by
    rw [abs_of_pos (by linarith)]
    calc ‖z‖ * (1 - ρ) ≤ ‖z‖ * 1 := by gcongr; linarith
      _ < 1 := by linarith
  have hsplit : ∀ s : ℂ, (∫ t in (0 : ℝ)..(1 - ρ₂), loopSegIntegrand a b c z s t) -
      (∫ t in (0 : ℝ)..(1 - ρ₁), loopSegIntegrand a b c z s t) =
      ∫ t in (1 - ρ₁)..(1 - ρ₂), loopSegIntegrand a b c z s t := fun s =>
    intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_loopSegIntegrand a b c z s hb (by linarith) (hT ρ₂ hρ₂ hρ₂1) hz1)
      (intervalIntegrable_loopSegIntegrand a b c z s hb (by linarith) (hT ρ₁ hρ₁ hρ₁1) hz1)
  have h1 := hsplit (-1)
  have h2 := hsplit 1
  unfold hypergeometricLoop
  linear_combination -h1 + h2 - hrect

/-- For `w ≠ 0`, `‖w^s‖ ≤ ‖w‖^{Re s} e^{π |Im s|}`. -/
theorem norm_cpow_le_rpow_mul_exp {w : ℂ} (hw : w ≠ 0) (s : ℂ) :
    ‖w ^ s‖ ≤ ‖w‖ ^ s.re * Real.exp (π * |s.im|) := by
  rw [norm_cpow_of_ne_zero hw, div_eq_mul_inv, ← Real.exp_neg]
  gcongr
  have h1 : |arg w| ≤ π := abs_le.mpr ⟨by linarith [neg_pi_lt_arg w], arg_le_pi w⟩
  have h2 : |arg w * s.im| ≤ π * |s.im| := by rw [abs_mul]; gcongr
  linarith [neg_abs_le (arg w * s.im)]

/-- For `0 < m ≤ r ≤ M`, `r^τ ≤ m^τ + M^τ` for every real `τ`. -/
theorem rpow_le_add_rpow {m M r : ℝ} (hm : 0 < m) (hr : m ≤ r) (hrM : r ≤ M) (τ : ℝ) :
    r ^ τ ≤ m ^ τ + M ^ τ := by
  have hr0 : 0 < r := by linarith
  rcases le_total 0 τ with hτ | hτ
  · have := Real.rpow_le_rpow hr0.le hrM hτ
    linarith [Real.rpow_nonneg hm.le τ]
  · have := Real.rpow_le_rpow_of_nonpos hm hr hτ
    linarith [Real.rpow_nonneg (show (0 : ℝ) ≤ M by linarith) τ]

/-- The circle integrand is `O(ρ'^{re(c-b)})` uniformly in `θ`. -/
theorem norm_loopCircIntegrand_le (a b c z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hz : ‖z‖ * (1 + ρ) < 1) :
    ∃ K : ℝ, ∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ ρ → ∀ θ ∈ Icc (-π) π,
      ‖loopCircIntegrand a b c z ρ' θ‖ ≤ K * ρ' ^ ((c - b - 1).re + 1) := by
  set q := ‖z‖ * (1 + ρ) with hq
  have hq0 : 0 ≤ q := by positivity
  set Kb := ((1 - ρ) ^ (b - 1).re + (1 + ρ) ^ (b - 1).re) * Real.exp (π * |(b - 1).im|)
  set Ka := ((1 - q) ^ (-a).re + (1 + q) ^ (-a).re) * Real.exp (π * |(-a).im|)
  refine ⟨Kb * Real.exp (π * |(c - b - 1).im|) * Ka, fun ρ' hρ' hρ'ρ θ hθ => ?_⟩
  have he : ‖exp (θ * I)‖ = 1 := norm_exp_ofReal_mul_I θ
  -- the factor `(1 + ρ' e^{iθ})^{b-1}`
  have hn1 : ‖(1 : ℂ) + ρ' * exp (θ * I)‖ ∈ Icc (1 - ρ) (1 + ρ) := by
    have hρn : ‖(ρ' : ℂ) * exp (θ * I)‖ = ρ' := by rw [norm_mul, he, mul_one, norm_real,
      Real.norm_of_nonneg hρ'.le]
    constructor
    · have := norm_sub_norm_le (1 : ℂ) (-(ρ' * exp (θ * I)))
      rw [norm_one, norm_neg, hρn, sub_neg_eq_add] at this; linarith
    · have := norm_add_le (1 : ℂ) (ρ' * exp (θ * I))
      rw [norm_one, hρn] at this; linarith
  have h1ne : (1 : ℂ) + ρ' * exp (θ * I) ≠ 0 := by
    intro h; rw [h, norm_zero] at hn1; linarith [hn1.1]
  have hB : ‖((1 : ℂ) + ρ' * exp (θ * I)) ^ (b - 1)‖ ≤ Kb :=
    (norm_cpow_le_rpow_mul_exp h1ne _).trans (mul_le_mul_of_nonneg_right
      (rpow_le_add_rpow (by linarith) hn1.1 hn1.2 _) (Real.exp_pos _).le)
  -- the factor `(1 - z(1 + ρ' e^{iθ}))^{-a}`
  have hzw : ‖z * (1 + ρ' * exp (θ * I))‖ ≤ q := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left hn1.2 (norm_nonneg z)
  have hn2 : ‖(1 : ℂ) - z * (1 + ρ' * exp (θ * I))‖ ∈ Icc (1 - q) (1 + q) := by
    constructor
    · have := norm_sub_norm_le (1 : ℂ) (z * (1 + ρ' * exp (θ * I)))
      rw [norm_one] at this; linarith
    · have := norm_sub_le (1 : ℂ) (z * (1 + ρ' * exp (θ * I)))
      rw [norm_one] at this; linarith
  have h2ne : (1 : ℂ) - z * (1 + ρ' * exp (θ * I)) ≠ 0 := by
    intro h; rw [h, norm_zero] at hn2; linarith [hn2.1]
  have hA : ‖((1 : ℂ) - z * (1 + ρ' * exp (θ * I))) ^ (-a)‖ ≤ Ka :=
    (norm_cpow_le_rpow_mul_exp h2ne _).trans (mul_le_mul_of_nonneg_right
      (rpow_le_add_rpow (by linarith) hn2.1 hn2.2 _) (Real.exp_pos _).le)
  -- the factor `ρ'^{c-b-1} e^{iθ(c-b-1)}`
  have hC : ‖(ρ' : ℂ) ^ (c - b - 1) * exp (θ * I * (c - b - 1))‖ ≤
      ρ' ^ (c - b - 1).re * Real.exp (π * |(c - b - 1).im|) := by
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hρ', norm_exp]
    gcongr
    have : (θ * I * (c - b - 1)).re = -(θ * (c - b - 1).im) := by simp
    rw [this]
    have h3 : |θ * (c - b - 1).im| ≤ π * |(c - b - 1).im| := by
      rw [abs_mul]; gcongr; exact abs_le.mpr hθ
    linarith [neg_abs_le (θ * (c - b - 1).im)]
  have hD : ‖I * (ρ' : ℂ) * exp (θ * I)‖ = ρ' := by
    rw [norm_mul, norm_mul, norm_I, one_mul, he, mul_one, norm_real, Real.norm_of_nonneg hρ'.le]
  unfold loopCircIntegrand
  rw [norm_mul, norm_mul, norm_mul, hD, Real.rpow_add hρ', Real.rpow_one]
  have hKb : 0 ≤ Kb := (norm_nonneg _).trans hB
  have hKa : 0 ≤ Ka := (norm_nonneg _).trans hA
  calc ‖((1 : ℂ) + ρ' * exp (θ * I)) ^ (b - 1)‖ *
        ‖(ρ' : ℂ) ^ (c - b - 1) * exp (θ * I * (c - b - 1))‖ *
        ‖((1 : ℂ) - z * (1 + ρ' * exp (θ * I))) ^ (-a)‖ * ρ'
      ≤ Kb * (ρ' ^ (c - b - 1).re * Real.exp (π * |(c - b - 1).im|)) * Ka * ρ' := by
        gcongr
    _ = _ := by ring

/-- For `re (c-b) > 0` the loop collapses onto the segment: the loop integral is
`(e^{-πi(c-b-1)} - e^{πi(c-b-1)})` times Euler's integral. -/
theorem hypergeometricLoop_eq_euler (a b c z : ℂ) (hb : 0 < b.re) (hcb : 0 < (c - b).re)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (hz : ‖z‖ * (1 + ρ) < 1) :
    hypergeometricLoop a b c z ρ =
      (exp (-1 * π * I * (c - b - 1)) - exp (1 * π * I * (c - b - 1))) *
        ∫ t : ℝ in (0 : ℝ)..1,
          (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a) := by
  have hz1 : ‖z‖ < 1 := by nlinarith [norm_nonneg z]
  set φ : ℝ → ℂ := fun t => (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)
    with hφ
  have hφi : IntervalIntegrable φ volume 0 1 := by
    have hcont : ContinuousOn (fun t : ℝ => (1 - z * t) ^ (-a)) (uIcc 0 1) := by
      intro t ht
      have ht' : t ∈ Icc 0 1 := by simpa [uIcc_of_le zero_le_one] using ht
      have hzt : ‖z‖ * |t| < 1 := by
        rw [abs_of_nonneg ht'.1]
        calc ‖z‖ * t ≤ ‖z‖ * 1 := by gcongr; exact ht'.2
          _ < 1 := by linarith
      exact (ContinuousAt.cpow (f := fun t : ℝ => 1 - z * (t : ℂ)) (g := fun _ => -a)
        (by fun_prop) continuousAt_const (one_sub_mul_ofReal_mem_slitPlane hzt)).continuousWithinAt
    have := (betaIntegral_convergent hb hcb).mul_continuousOn hcont
    simpa [hφ, show b + (c - b) - 1 = c - 1 by ring] using this
  set Φ : ℝ → ℂ := fun x => ∫ t in (0 : ℝ)..x, φ t with hΦ
  have hΦc : ContinuousOn Φ (uIcc 0 1) :=
    intervalIntegral.continuousOn_primitive_interval' hφi left_mem_uIcc
  -- the segment integrals in terms of `Φ`
  have hseg : ∀ s : ℂ, ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 →
      ∫ t in (0 : ℝ)..(1 - ρ'), loopSegIntegrand a b c z s t =
        exp (s * π * I * (c - b - 1)) * Φ (1 - ρ') := by
    intro s ρ' _ _
    rw [hΦ, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [loopSegIntegrand, hφ]
    push_cast; ring
  -- the circle integral tends to zero
  obtain ⟨K, hK⟩ := norm_loopCircIntegrand_le a b c z hρ hρ1 hz
  set p := (c - b - 1).re + 1 with hp
  have hp0 : 0 < p := by simp only [hp, sub_re, one_re] at hcb ⊢; linarith
  have hcirc : Tendsto (fun ρ' : ℝ => ∫ θ in (-π)..π, loopCircIntegrand a b c z ρ' θ)
      (𝓝[>] 0) (𝓝 0) := by
    have hbound : ∀ᶠ ρ' in 𝓝[>] (0 : ℝ),
        ‖∫ θ in (-π)..π, loopCircIntegrand a b c z ρ' θ‖ ≤ K * ρ' ^ p * (2 * π) := by
      filter_upwards [Ioo_mem_nhdsGT hρ] with ρ' hρ'
      refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := K * ρ' ^ p)
        fun θ hθ => ?_).trans_eq ?_
      · exact hK ρ' hρ'.1 hρ'.2.le θ ⟨by
          have := hθ.1; rw [min_eq_left (by linarith [Real.pi_pos])] at this; linarith,
          by have := hθ.2; rwa [max_eq_right (by linarith [Real.pi_pos])] at this⟩
      · rw [abs_of_pos (by linarith [Real.pi_pos])]; ring
    have h0 : Tendsto (fun ρ' : ℝ => K * ρ' ^ p * (2 * π)) (𝓝[>] 0) (𝓝 0) := by
      have := (((Real.continuousAt_rpow_const 0 p (Or.inr hp0.le)).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Ioi 0))).const_mul K).mul_const (2 * π)
      simpa [Real.zero_rpow hp0.ne'] using this
    exact squeeze_zero_norm' hbound h0
  -- the segment integrals tend to Euler's integral
  have hΦlim : Tendsto (fun ρ' : ℝ => Φ (1 - ρ')) (𝓝[>] 0) (𝓝 (Φ 1)) := by
    have h1 : ContinuousWithinAt Φ (uIcc 0 1) 1 := hΦc 1 right_mem_uIcc
    refine h1.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩)
    · have : Tendsto (fun ρ' : ℝ => 1 - ρ') (𝓝 0) (𝓝 1) := by
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_id (x := 𝓝 (0 : ℝ)))
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT one_pos] with ρ' hρ'
      rw [uIcc_of_le zero_le_one]; exact ⟨by linarith [hρ'.2], by linarith [hρ'.1]⟩
  have hlim : Tendsto (fun ρ' : ℝ => hypergeometricLoop a b c z ρ') (𝓝[>] 0)
      (𝓝 ((exp (-1 * π * I * (c - b - 1)) - exp (1 * π * I * (c - b - 1))) * Φ 1)) := by
    have h := ((hΦlim.const_mul (exp (-1 * π * I * (c - b - 1)))).add hcirc).sub
      (hΦlim.const_mul (exp (1 * π * I * (c - b - 1))))
    rw [add_zero, ← sub_mul] at h
    refine h.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT one_pos] with ρ' hρ'
    unfold hypergeometricLoop
    rw [hseg (-1) ρ' hρ'.1 hρ'.2, hseg 1 ρ' hρ'.1 hρ'.2]
  have hconst : Tendsto (fun ρ' : ℝ => hypergeometricLoop a b c z ρ') (𝓝[>] 0)
      (𝓝 (hypergeometricLoop a b c z ρ)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hρ] with ρ' hρ'
    exact hypergeometricLoop_eq a b c z hb hρ hρ'.1 hρ1 (by linarith [hρ'.2]) hz
      (by nlinarith [norm_nonneg z, hρ'.2])
  exact tendsto_nhds_unique hconst hlim

/-- `c ↦ ∫ₐᵇ h(t) e^{c L(t)} dt` is entire for integrable `h` and continuous `L`. -/
theorem differentiable_intervalIntegral_mul_exp {h L : ℝ → ℂ} {a b : ℝ}
    (hh : IntervalIntegrable h volume a b) (hL : ContinuousOn L (uIcc a b)) :
    Differentiable ℂ fun c : ℂ => ∫ t in a..b, h t * exp (c * L t) := by
  intro c₀
  obtain ⟨M, hM⟩ := isCompact_uIcc.exists_bound_of_continuousOn hL
  have hM0 : 0 ≤ M := by
    have := hM a left_mem_uIcc; exact (norm_nonneg _).trans this
  set B := M * Real.exp ((‖c₀‖ + 1) * M)
  have hexp : ∀ c ∈ Metric.ball c₀ 1, ∀ t ∈ uIcc a b,
      ‖exp (c * L t)‖ ≤ Real.exp ((‖c₀‖ + 1) * M) := by
    intro c hc t ht
    rw [norm_exp]
    apply Real.exp_le_exp.mpr
    have hc' : ‖c‖ ≤ ‖c₀‖ + 1 := by
      have := norm_le_norm_add_norm_sub' c c₀
      rw [Metric.mem_ball, dist_eq_norm] at hc; linarith
    calc (c * L t).re ≤ ‖c * L t‖ := re_le_norm _
      _ = ‖c‖ * ‖L t‖ := norm_mul _ _
      _ ≤ (‖c₀‖ + 1) * M := mul_le_mul hc' (hM t ht) (norm_nonneg _) (by positivity)
  have hcontE : ∀ c : ℂ, ContinuousOn (fun t => exp (c * L t)) (uIcc a b) := fun c =>
    (continuousOn_const.mul hL).cexp
  have hcontE' : ContinuousOn (fun t => L t * exp (c₀ * L t)) (uIcc a b) :=
    hL.mul (hcontE c₀)
  have hhm : AEStronglyMeasurable h (volume.restrict (Ι a b)) :=
    (intervalIntegrable_iff.mp hh).aestronglyMeasurable
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun c t => h t * exp (c * L t)) (F' := fun c t => h t * (L t * exp (c * L t)))
    (bound := fun t => ‖h t‖ * B) (x₀ := c₀) (s := Metric.ball c₀ 1)
    (Metric.ball_mem_nhds c₀ one_pos)
    (Eventually.of_forall fun c => hhm.mul ((hcontE c).mono uIoc_subset_uIcc
      |>.aestronglyMeasurable measurableSet_uIoc))
    (hh.mul_continuousOn (hcontE c₀))
    (hhm.mul (hcontE'.mono uIoc_subset_uIcc |>.aestronglyMeasurable measurableSet_uIoc))
    (Eventually.of_forall fun t ht c hc => by
      have htI : t ∈ uIcc a b := uIoc_subset_uIcc ht
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hM t htI) (hexp c hc t htI)
        (norm_nonneg _) hM0) (norm_nonneg _))
    (hh.norm.mul_const B)
    (Eventually.of_forall fun t _ c _ => by
      have := (((hasDerivAt_id c).mul_const (L t)).cexp).const_mul (h t)
      simpa [mul_comm, mul_left_comm, mul_assoc] using this)
  exact key.2.differentiableAt

/-- **The loop integral is entire in `c`.** -/
theorem differentiable_hypergeometricLoop (a b z : ℂ) (hb : 0 < b.re) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ < 1) (hz : ‖z‖ * (1 + ρ) < 1) :
    Differentiable ℂ fun c : ℂ => hypergeometricLoop a b c z ρ := by
  have hz1 : ‖z‖ < 1 := by nlinarith [norm_nonneg z]
  have hT : ‖z‖ * |1 - ρ| < 1 := by
    rw [abs_of_pos (by linarith)]
    calc ‖z‖ * (1 - ρ) ≤ ‖z‖ * 1 := by gcongr; linarith
      _ < 1 := by linarith
  -- the segments
  have hseg : ∀ s : ℂ, Differentiable ℂ fun c : ℂ =>
      ∫ t in (0 : ℝ)..(1 - ρ), loopSegIntegrand a b c z s t := by
    intro s
    set L : ℝ → ℂ := fun t => (Real.log (1 - t) : ℂ) + s * π * I
    set h : ℝ → ℂ := fun t => loopSegIntegrand a b 0 z s t
    have hL : ContinuousOn L (uIcc 0 (1 - ρ)) := by
      intro t ht
      have ht' : t ≤ 1 - ρ := by
        have := ht.2; rwa [max_eq_right (by linarith)] at this
      have hlog : ContinuousAt (fun t : ℝ => Real.log (1 - t)) t :=
        ContinuousAt.comp (g := Real.log) (f := fun t : ℝ => 1 - t)
          (Real.continuousAt_log (by linarith)) (by fun_prop)
      exact ((continuous_ofReal.continuousAt.comp hlog).add continuousAt_const).continuousWithinAt
    have hh : IntervalIntegrable h volume 0 (1 - ρ) :=
      intervalIntegrable_loopSegIntegrand a b 0 z s hb (by linarith) hT hz1
    have hd := differentiable_intervalIntegral_mul_exp hh hL
    have heq : ∀ c : ℂ, ∫ t in (0 : ℝ)..(1 - ρ), loopSegIntegrand a b c z s t =
        ∫ t in (0 : ℝ)..(1 - ρ), h t * exp (c * L t) := fun c => by
      refine intervalIntegral.integral_congr fun t ht => ?_
      have ht' : t ≤ 1 - ρ := by
        have := ht.2; rwa [max_eq_right (by linarith)] at this
      have h1t : 0 < 1 - t := by linarith
      simp only [h, L, loopSegIntegrand]
      rw [ofReal_cpow_eq_exp_mul_log h1t, ofReal_cpow_eq_exp_mul_log h1t]
      have e1 : exp ((c - b - 1) * Real.log (1 - t)) * exp (s * π * I * (c - b - 1)) =
          exp ((0 - b - 1) * Real.log (1 - t)) * exp (s * π * I * (0 - b - 1)) *
            exp (c * ((Real.log (1 - t) : ℂ) + s * π * I)) := by
        rw [← exp_add, ← exp_add, ← exp_add]; congr 1; ring
      linear_combination ((t : ℂ) ^ (b - 1) * (1 - z * t) ^ (-a)) * e1
    simpa only [heq] using hd
  -- the circle
  have hcirc : Differentiable ℂ fun c : ℂ => ∫ θ in (-π)..π, loopCircIntegrand a b c z ρ θ := by
    set L : ℝ → ℂ := fun θ => (Real.log ρ : ℂ) + θ * I
    set h : ℝ → ℂ := fun θ => loopCircIntegrand a b 0 z ρ θ
    have hL : ContinuousOn L (uIcc (-π) π) := by fun_prop
    have hh : IntervalIntegrable h volume (-π) π := by
      refine ContinuousOn.intervalIntegrable fun θ _ => ?_
      have he : ‖exp (θ * I)‖ = 1 := norm_exp_ofReal_mul_I θ
      have h1 : 1 + (ρ : ℂ) * exp (θ * I) ∈ slitPlane := by
        rw [mem_slitPlane_iff]; left
        have := abs_re_le_norm ((ρ : ℂ) * exp (θ * I))
        rw [norm_mul, he, mul_one, norm_real, Real.norm_of_nonneg hρ.le] at this
        rw [add_re, one_re]; linarith [neg_abs_le ((ρ : ℂ) * exp (θ * I)).re]
      have h2 : 1 - z * (1 + (ρ : ℂ) * exp (θ * I)) ∈ slitPlane := by
        rw [mem_slitPlane_iff]; left
        have hn : ‖z * (1 + (ρ : ℂ) * exp (θ * I))‖ < 1 := by
          rw [norm_mul]
          calc ‖z‖ * ‖1 + (ρ : ℂ) * exp (θ * I)‖ ≤ ‖z‖ * (1 + ρ) := by
                gcongr
                refine (norm_add_le _ _).trans ?_
                rw [norm_one, norm_mul, he, mul_one, norm_real, Real.norm_of_nonneg hρ.le]
            _ < 1 := hz
        have := abs_re_le_norm (z * (1 + (ρ : ℂ) * exp (θ * I)))
        rw [sub_re, one_re]; linarith [le_abs_self (z * (1 + (ρ : ℂ) * exp (θ * I))).re]
      refine ContinuousAt.continuousWithinAt ?_
      simp only [h, loopCircIntegrand]
      refine ContinuousAt.mul (ContinuousAt.mul (ContinuousAt.mul ?_ (by fun_prop)) ?_)
        (by fun_prop)
      · exact ContinuousAt.cpow (by fun_prop) continuousAt_const h1
      · exact ContinuousAt.cpow (by fun_prop) continuousAt_const h2
    have hd := differentiable_intervalIntegral_mul_exp hh hL
    have heq : ∀ c : ℂ, ∫ θ in (-π)..π, loopCircIntegrand a b c z ρ θ =
        ∫ θ in (-π)..π, h θ * exp (c * L θ) := fun c => by
      refine intervalIntegral.integral_congr fun θ _ => ?_
      simp only [h, L, loopCircIntegrand]
      rw [ofReal_cpow_eq_exp_mul_log hρ, ofReal_cpow_eq_exp_mul_log hρ]
      have e1 : exp ((c - b - 1) * Real.log ρ) * exp (θ * I * (c - b - 1)) =
          exp ((0 - b - 1) * Real.log ρ) * exp (θ * I * (0 - b - 1)) *
            exp (c * ((Real.log ρ : ℂ) + θ * I)) := by
        rw [← exp_add, ← exp_add, ← exp_add]; congr 1; ring
      linear_combination ((1 + (ρ : ℂ) * exp (θ * I)) ^ (b - 1) *
        (1 - z * (1 + (ρ : ℂ) * exp (θ * I))) ^ (-a) * (I * ρ * exp (θ * I))) * e1
    simpa only [heq] using hd
  unfold hypergeometricLoop
  exact ((hseg (-1)).add hcirc).sub (hseg 1)

/-- `e^{-πi(x - 1)} - e^{πi(x - 1)} = 2i sin(πx)`. -/
theorem exp_neg_sub_exp_loop (x : ℂ) :
    exp (-1 * π * I * (x - 1)) - exp (1 * π * I * (x - 1)) = 2 * I * sin (π * x) := by
  have h1 : exp (-1 * π * I * (x - 1)) = -exp (-(π * x * I)) := by
    rw [show -1 * (π : ℂ) * I * (x - 1) = -(π * x * I) + π * I by ring, exp_add, exp_pi_mul_I]
    ring
  have h2 : exp (1 * π * I * (x - 1)) = -exp (π * x * I) := by
    rw [show 1 * (π : ℂ) * I * (x - 1) = π * x * I + -(π * I) by ring, exp_add, exp_neg,
      exp_pi_mul_I]
    ring
  rw [h1, h2, Complex.sin]
  ring_nf
  rw [I_sq]
  ring

/-- **The loop integral for `₂F₁`** (DLMF 15.6.2, Temme §5.2.2): for `re b > 0`,
`c - b ∉ {1, 2, …}`, and the loop of radius `ρ` about `1` with `|z|(1+ρ) < 1`,
`F(a,b;c;z)/Γ(c) = Γ(1+b-c)/(2πi Γ(b)) ∫₀^{(1+)} t^{b-1} (t-1)^{c-b-1} (1-zt)^{-a} dt`. -/
@[dlmf 15.6.E2]
theorem regularizedGaussHGFun_eq_loop (a b c z : ℂ) (hb : 0 < b.re)
    (hcb : ∀ n : ℕ, c - b ≠ n + 1) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hz : ‖z‖ * (1 + ρ) < 1) :
    regularizedGaussHGFun a b c z =
      Gamma (1 + b - c) / (2 * π * I * Gamma b) * hypergeometricLoop a b c z ρ := by
  have hz1 : ‖z‖ < 1 := by nlinarith [norm_nonneg z]
  have hGb : Gamma b ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hb
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have hinvG : Differentiable ℂ fun s : ℂ => (Gamma s)⁻¹ := by
    simpa [one_div] using Complex.differentiable_one_div_Gamma
  have key := eq_of_analyticOnNhd_univ_of_eqOn
    (f := fun c => (Gamma (1 + b - c))⁻¹ * regularizedGaussHGFun a b c z)
    (g := fun c => (2 * π * I * Gamma b)⁻¹ * hypergeometricLoop a b c z ρ)
    (fun c _ => ((hinvG.comp (by fun_prop : Differentiable ℂ fun c : ℂ => 1 + b - c)).analyticAt
      c).mul (analyticOnNhd_regularizedGaussHGFun_c a b hz1 c trivial))
    (fun c _ => ((differentiable_hypergeometricLoop a b z hb hρ hρ1 hz).const_mul _).analyticAt c)
    (U := Metric.ball (b + 1 / 2) (1 / 4)) Metric.isOpen_ball ⟨b + 1 / 2, by simp⟩
    (fun c hc => by
      rw [Metric.mem_ball, dist_eq_norm] at hc
      have hre := abs_re_le_norm (c - (b + 1 / 2))
      rw [abs_le] at hre
      simp only [sub_re, add_re, div_re] at hre
      norm_num at hre
      have hcb' : 0 < (c - b).re := by simp only [sub_re]; linarith [hre.1]
      have hcb'' : (c - b).re < 1 := by simp only [sub_re]; linarith [hre.2]
      have hc0 : ∀ k : ℕ, c ≠ -k := fun k h => by
        have := congrArg re h; simp at this
        linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), show (c - b).re = c.re - b.re from sub_re c b]
      have hGc : Gamma c ≠ 0 := Gamma_ne_zero hc0
      have hGcb : Gamma (c - b) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hcb'
      have hsin : sin (π * (c - b)) ≠ 0 := by
        rw [Complex.sin_ne_zero_iff]
        intro k hk
        have := congrArg re hk
        simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, intCast_re, intCast_im,
          mul_zero] at this
        have hk' : (c - b).re = k := by
          have hπ' : (π : ℝ) ≠ 0 := Real.pi_ne_zero
          field_simp at this; linarith
        rw [hk'] at hcb' hcb''
        have h1 : (0 : ℤ) < k := by exact_mod_cast hcb'
        have h2 : k < (1 : ℤ) := by exact_mod_cast hcb''
        omega
      have hrefl := Complex.Gamma_mul_Gamma_one_sub (c - b)
      rw [show 1 - (c - b) = 1 + b - c by ring] at hrefl
      have hloop := hypergeometricLoop_eq_euler a b c z hb hcb' hρ hρ1 hz
      rw [show c - b - 1 = (c - b) - 1 by ring, exp_neg_sub_exp_loop] at hloop
      simp only
      rw [regularizedGaussHGFun_eq_div_Gamma hc0, ordinaryHypergeometric_eq_integral hb hcb' hz1,
        hloop]
      have hG1 : Gamma (1 + b - c) = π / (sin (π * (c - b)) * Gamma (c - b)) := by
        rw [eq_div_iff (mul_ne_zero hsin hGcb)]
        rw [show Gamma (1 + b - c) * (sin (π * (c - b)) * Gamma (c - b)) =
          Gamma (c - b) * Gamma (1 + b - c) * sin (π * (c - b)) by ring, hrefl]
        field_simp
      rw [hG1]
      generalize (∫ t : ℝ in (0 : ℝ)..1, (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
        (1 - z * t) ^ (-a)) = E
      field_simp)
  have hc := congrFun key c
  have hG : Gamma (1 + b - c) ≠ 0 := Gamma_ne_zero fun k h => hcb k (by linear_combination -h)
  rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hπ) hI)
    hGb)]
  field_simp at hc
  linear_combination hc

end DLMF.Hypergeometric
