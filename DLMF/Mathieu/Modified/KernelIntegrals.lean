/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Modified.Connection

/-!
# Integral equations with the kernel `e^{2ihw}` (DLMF 28.28.2–28.28.3)

Proofs of the integral equations DLMF 28.28.2–28.28.3 stated in
`DLMF.Mathieu.Modified.Integrals`, for all real `h`.

## Main results

* `hasDerivAt_integral_exp_mathieuKernelW`: differentiation in `α` under the integral sign
  for the kernel `e^{2ihw}`.
* `integral_exp_mathieuCe'`: DLMF 28.28.2.
* `integral_exp_mathieuSe'`: DLMF 28.28.3.

## Implementation notes

For `w = cosh z cos t cos α + sinh z sin t sin α` the kernel `K = e^{2ihw}` satisfies
`(∂_α² - 2q cos 2α) K = (∂_t² - 2q cos 2t) K`, `q = h²`, so `α ↦ ∫₀^{2π} e^{2ihw} f(t) dt`
solves Mathieu's equation whenever `f` is a `2π`-periodic solution. For `f = ce_n` (`se_n`)
the integral is even (odd) in `α`, hence a multiple of `ce_n(α)` (`se_n(α)`); the multiplier
is evaluated by the integral equations 28.10.1, 28.10.3, 28.10.6 and 28.10.7 at the point
`iz`, and compared with `Mc^{(1)}_n`, `Ms^{(1)}_n` by the connection formulas 28.22.1–28.22.2
(`h > 0`), the parity in `h` (`h < 0`) and the values at `h = 0`.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory intervalIntegral
open scoped Topology Real

namespace DLMF.Mathieu

/-- `∂w/∂α` for the kernel `w` of 28.28.1. -/
private lemma hasDerivAt_mathieuKernelW (z t α : ℂ) :
    HasDerivAt (fun β => mathieuKernelW z t β)
      (-(Complex.cosh z * Complex.cos t * Complex.sin α) +
        Complex.sinh z * Complex.sin t * Complex.cos α) α := by
  have h1 := ((Complex.hasDerivAt_cos α).const_mul (Complex.cosh z * Complex.cos t)).add
    ((Complex.hasDerivAt_sin α).const_mul (Complex.sinh z * Complex.sin t))
  convert h1 using 1
  · funext β; simp [mathieuKernelW]
  · ring

/-- Differentiation in `α` under the integral sign for the kernel `e^{2ihw}`. -/
theorem hasDerivAt_integral_exp_mathieuKernelW (h : ℝ) (z : ℂ) {g : ℝ → ℂ} (hg : Continuous g)
    (α : ℂ) :
    HasDerivAt (fun β => ∫ t in (0 : ℝ)..2 * π,
        Complex.exp (2 * I * h * mathieuKernelW z t β) * g t)
      (∫ t in (0 : ℝ)..2 * π, 2 * I * h * deriv (fun β => mathieuKernelW z t β) α *
        Complex.exp (2 * I * h * mathieuKernelW z t α) * g t) α := by
  set W' : ℂ → ℝ → ℂ := fun β t => -(Complex.cosh z * Complex.cos t * Complex.sin β) +
    Complex.sinh z * Complex.sin t * Complex.cos β
  set F' : ℂ → ℝ → ℂ := fun β t => 2 * I * h * W' β t *
    Complex.exp (2 * I * h * mathieuKernelW z t β) * g t
  have hcontW : Continuous (fun p : ℂ × ℝ => mathieuKernelW z p.2 p.1) := by
    unfold mathieuKernelW; fun_prop
  have hcont : Continuous (fun p : ℂ × ℝ => F' p.1 p.2) := by
    simp only [F', W']
    have := hg.comp (continuous_snd : Continuous (fun p : ℂ × ℝ => p.2))
    fun_prop
  have hFc : ∀ β : ℂ, Continuous (fun t : ℝ =>
      Complex.exp (2 * I * h * mathieuKernelW z t β) * g t) := fun β => by
    have : Continuous (fun t : ℝ => mathieuKernelW z t β) := by unfold mathieuKernelW; fun_prop
    fun_prop
  obtain ⟨C, hC⟩ := (isCompact_closedBall α 1 |>.prod (isCompact_Icc (a := (0 : ℝ))
    (b := 2 * π))).exists_bound_of_continuousOn hcont.continuousOn
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (a := 0) (b := 2 * π)
    (F := fun β t => Complex.exp (2 * I * h * mathieuKernelW z t β) * g t) (F' := F')
    (x₀ := α) (s := Metric.closedBall α 1) (bound := fun _ => C)
    (Metric.closedBall_mem_nhds α one_pos)
    (Eventually.of_forall fun β => (hFc β).aestronglyMeasurable)
    ((hFc α).intervalIntegrable _ _)
    ((hcont.comp (Continuous.prodMk_right α)).aestronglyMeasurable)
    (ae_of_all _ fun t ht β hβ => by
      have ht' : t ∈ Icc 0 (2 * π) := by
        rw [uIoc_of_le (by positivity)] at ht; exact ⟨ht.1.le, ht.2⟩
      exact hC (β, t) ⟨hβ, ht'⟩)
    intervalIntegrable_const
    (ae_of_all _ fun t _ β _ => by
      have := (((hasDerivAt_mathieuKernelW z t β).const_mul (2 * I * h)).cexp).mul_const (g t)
      convert this using 1
      simp only [F', W']; ring)
  convert key.2 using 1
  apply intervalIntegral.integral_congr
  intro t _
  simp only [F', W']
  rw [(hasDerivAt_mathieuKernelW z t α).deriv]

/-- The kernel `e^{2ihw}`, `w = cosh z cos t cos α + sinh z sin t sin α`, as a function of `α`
is carried by a `2π`-periodic solution of Mathieu's equation in `t` to a solution in `α`. -/
private lemma isMathieuSolution_integral_exp_mathieuKernelW {a : ℂ} (h : ℝ) (z : ℂ) {f f' : ℝ → ℂ}
    (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t : ℝ, HasDerivAt f' ((2 * ((h ^ 2 : ℝ) : ℂ) * Complex.cos (2 * (t : ℂ)) - a) *
      f t) t)
    (hfp : ∀ t, f (t + 2 * π) = f t) (hf'p : ∀ t, f' (t + 2 * π) = f' t) :
    IsMathieuSolution a ((h ^ 2 : ℝ) : ℂ)
      (fun α => ∫ t in (0 : ℝ)..2 * π,
        Complex.exp (2 * I * h * mathieuKernelW z t α) * f t) := by
  set H : ℂ := (h : ℂ) with hH
  have hQ : (((h ^ 2 : ℝ)) : ℂ) = H ^ 2 := by push_cast; rfl
  set C := Complex.cosh z
  set S := Complex.sinh z
  let W : ℂ → ℝ → ℂ := fun α t => C * Complex.cos t * Complex.cos α + S * Complex.sin t *
    Complex.sin α
  let Wa : ℂ → ℝ → ℂ := fun α t => -(C * Complex.cos t * Complex.sin α) + S * Complex.sin t *
    Complex.cos α
  let Wt : ℂ → ℝ → ℂ := fun α t => -(C * Complex.sin t * Complex.cos α) + S * Complex.cos t *
    Complex.sin α
  have hWe : ∀ (α : ℂ) (t : ℝ), mathieuKernelW z t α = W α t := fun α t => rfl
  have hWa : ∀ α t, HasDerivAt (fun α => W α t) (Wa α t) α := by
    intro α t
    have := ((Complex.hasDerivAt_cos α).const_mul (C * Complex.cos t)).add
      ((Complex.hasDerivAt_sin α).const_mul (S * Complex.sin t))
    convert this using 1; simp only [Wa]; ring
  have hWaa : ∀ α t, HasDerivAt (fun α => Wa α t) (-W α t) α := by
    intro α t
    have := ((Complex.hasDerivAt_sin α).const_mul (C * Complex.cos t)).neg.add
      ((Complex.hasDerivAt_cos α).const_mul (S * Complex.sin t))
    convert this using 1; simp only [W]; ring
  have hcos : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.cos (t : ℂ)) (-Complex.sin t) t :=
    fun t => (Complex.hasDerivAt_cos (t : ℂ)).comp_ofReal
  have hsin : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.sin (t : ℂ)) (Complex.cos t) t :=
    fun t => (Complex.hasDerivAt_sin (t : ℂ)).comp_ofReal
  have hWt : ∀ α t, HasDerivAt (fun t => W α t) (Wt α t) t := by
    intro α t
    have := (((hcos t).const_mul C).mul_const (Complex.cos α)).add
      (((hsin t).const_mul S).mul_const (Complex.sin α))
    convert this using 1; simp only [Wt]; ring
  have hWtt : ∀ α t, HasDerivAt (fun t => Wt α t) (-W α t) t := by
    intro α t
    have := (((hsin t).const_mul C).mul_const (Complex.cos α)).neg.add
      (((hcos t).const_mul S).mul_const (Complex.sin α))
    convert this using 1; simp only [W]; ring
  set k : ℂ := 2 * I * H
  have hG := isMathieuSolution_intervalIntegral_kernel (α := 0) (β := 2 * π) (a := a) (q := H ^ 2)
    (K := fun α t => Complex.exp (k * W α t))
    (K1 := fun α t => k * Wa α t * Complex.exp (k * W α t))
    (K2 := fun α t => (k * -W α t + (k * Wa α t) ^ 2) * Complex.exp (k * W α t))
    (Kt := fun α t => k * Wt α t * Complex.exp (k * W α t))
    (Ktt := fun α t => (k * -W α t + (k * Wt α t) ^ 2) * Complex.exp (k * W α t))
    (f := f) (f' := f')
    (fun α t => by
      have := ((hWa α t).const_mul k).cexp
      convert this using 1; ring)
    (fun α t => by
      have := ((hWaa α t).const_mul k).mul ((hWa α t).const_mul k).cexp
      convert this using 1; ring)
    (fun α t => by
      have := ((hWt α t).const_mul k).cexp
      convert this using 1; ring)
    (fun α t => by
      have := ((hWtt α t).const_mul k).mul ((hWt α t).const_mul k).cexp
      convert this using 1; ring)
    (by simp only [W]; fun_prop) (by simp only [W, Wa]; fun_prop)
    (by simp only [W, Wa]; fun_prop) (fun α => by simp only [W, Wt]; fun_prop)
    hf (by simpa [hQ] using hf')
    (fun α t => by
      simp only [k]
      rw [Complex.cos_two_mul, Complex.cos_two_mul]
      have e0 : C ^ 2 - S ^ 2 = 1 := Complex.cosh_sq_sub_sinh_sq z
      have e1 := Complex.sin_sq_add_cos_sq α
      have e2 := Complex.sin_sq_add_cos_sq (t : ℂ)
      simp only [W, Wa, Wt]
      set E := Complex.exp (2 * I * H * (C * Complex.cos t * Complex.cos α +
        S * Complex.sin t * Complex.sin α))
      set D := Complex.cos (t : ℂ) ^ 2 * Complex.sin α ^ 2 - Complex.sin (t : ℂ) ^ 2 *
        Complex.cos α ^ 2
      linear_combination E * 4 * I ^ 2 * H ^ 2 * D * e0 + E * 4 * H ^ 2 * D * I_sq -
        4 * H ^ 2 * E * Complex.cos (t : ℂ) ^ 2 * e1 + 4 * H ^ 2 * E * Complex.cos α ^ 2 * e2)
    (fun α => by
      have e := hfp 0
      have e' := hf'p 0
      rw [zero_add] at e e'
      rw [e, e']
      simp only [W, Wt]
      push_cast
      rw [Complex.cos_two_pi, Complex.sin_two_pi, Complex.cos_zero, Complex.sin_zero])
  simpa [hQ, hWe] using hG

/-- Reflection of the kernel integral: `G(-α) = s G(α)` when `f(-t) = s f(t)`. -/
private lemma integral_exp_mathieuKernelW_neg (h : ℝ) (z : ℂ) {f : ℝ → ℂ}
    (hfp : ∀ t, f (t + 2 * π) = f t) {s : ℂ} (hpar : ∀ t, f t = s * f (-t)) (α : ℂ) :
    ∫ t in (0 : ℝ)..2 * π, Complex.exp (2 * I * h * mathieuKernelW z t (-α)) * f t =
      s * ∫ t in (0 : ℝ)..2 * π, Complex.exp (2 * I * h * mathieuKernelW z t α) * f t := by
  set g : ℝ → ℂ := fun t => Complex.exp (2 * I * h * mathieuKernelW z t α) * f t
  have hg : Function.Periodic g (2 * π) := by
    intro t
    simp only [g, mathieuKernelW]
    push_cast
    rw [hfp, Complex.cos_add_two_pi, Complex.sin_add_two_pi]
  have e : ∀ t : ℝ, Complex.exp (2 * I * h * mathieuKernelW z t (-α)) * f t = s * g (-t) := by
    intro t
    simp only [g, mathieuKernelW]
    rw [hpar t]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg, Complex.cos_neg, Complex.sin_neg]
    ring_nf
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_neg]
  congr 1
  have := hg.intervalIntegral_add_eq (-(2 * π)) 0
  simp only [neg_add_cancel, zero_add] at this
  rw [neg_zero, this]

/-- `∫₀^{2π} g = 0` for `g(x + π) = -g(x)`. -/
private lemma integral_two_pi_eq_zero_of_antiperiodic {g : ℝ → ℂ} (hg : Continuous g)
    (hper : ∀ x, g (x + π) = -g x) : ∫ x in (0 : ℝ)..2 * π, g x = 0 := by
  have hi : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b => hg.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π) (hi _ _) (hi _ _)]
  have h1 := intervalIntegral.integral_comp_add_right (a := 0) (b := π) g π
  rw [zero_add, show π + π = 2 * π by ring] at h1
  rw [← h1]
  simp_rw [hper]
  rw [intervalIntegral.integral_neg]; ring

/-- `ce_n` is continuous on the real line. -/
private lemma continuous_mathieuCe_ofReal (n : ℕ) (q : ℝ) : Continuous fun t : ℝ =>
    mathieuCe n t q :=
  (isMathieuSolution_mathieuCe n q).differentiable.continuous.comp continuous_ofReal

/-- The kernel integral against `ce_n` is `G(z, 0)/ce_n(0) · ce_n(α)`. -/
private lemma integral_kernel_mathieuCe_eq_mul_mathieuCe (n : ℕ) (h : ℝ) (z α : ℂ) :
    ∫ t in (0 : ℝ)..2 * π, Complex.exp (2 * I * h * mathieuKernelW z t α) *
        mathieuCe n t (h ^ 2) =
      (∫ t in (0 : ℝ)..2 * π, Complex.exp (2 * I * h * (Complex.cosh z * Complex.cos t)) *
        mathieuCe n t (h ^ 2)) / mathieuCe n 0 (h ^ 2) * mathieuCe n α (h ^ 2) := by
  have hper : ∀ t : ℝ, mathieuCe n ((t + 2 * π : ℝ) : ℂ) (h ^ 2) = mathieuCe n t (h ^ 2) := by
    intro t
    push_cast
    rw [show (t : ℂ) + 2 * π = t + π + π by ring, mathieuCe_add_pi, mathieuCe_add_pi,
      ← mul_assoc, ← mul_pow]
    simp
  have hdper : ∀ t : ℝ, deriv (fun z => mathieuCe n z (h ^ 2)) ((t + 2 * π : ℝ) : ℂ) =
      deriv (fun z => mathieuCe n z (h ^ 2)) t := by
    intro t
    have e : (fun z => mathieuCe n z (h ^ 2)) =
        fun z => mathieuCe n (z + (2 * π : ℂ)) (h ^ 2) := by
      funext w
      have := hper 0
      rw [show mathieuCe n (w + (2 * π : ℂ)) (h ^ 2) = mathieuCe n (w + π + π) (h ^ 2) by ring_nf,
        mathieuCe_add_pi, mathieuCe_add_pi, ← mul_assoc, ← mul_pow]
      simp
    push_cast
    conv_rhs => rw [e]
    have := deriv_comp_add_const (f := fun w => mathieuCe n w (h ^ 2)) (a := (2 * π : ℂ))
      (x := (t : ℂ))
    rw [this]
  have hG := isMathieuSolution_integral_exp_mathieuKernelW (a := mathieuA n (h ^ 2)) h z
    (f := fun t : ℝ => mathieuCe n t (h ^ 2))
    (f' := fun t : ℝ => deriv (fun z => mathieuCe n z (h ^ 2)) t)
    (hasDerivAt_mathieuCe_ofReal _ _) (hasDerivAt_deriv_mathieuCe_ofReal _ _) hper hdper
  have hev : ∀ α, (fun α => ∫ t in (0 : ℝ)..2 * π,
      Complex.exp (2 * I * h * mathieuKernelW z t α) * mathieuCe n t (h ^ 2)) (-α) =
      (fun α => ∫ t in (0 : ℝ)..2 * π,
      Complex.exp (2 * I * h * mathieuKernelW z t α) * mathieuCe n t (h ^ 2)) α := by
    intro α
    have := integral_exp_mathieuKernelW_neg h z
        (f := fun t : ℝ => mathieuCe n t (h ^ 2)) hper (s := 1)
      (fun t => by push_cast; rw [mathieuCe_neg, one_mul]) α
    simpa using this
  have := eq_mul_mathieuCe_of_even hG hev α
  rw [this]
  congr 3
  funext t
  simp [mathieuKernelW]

/-- Splitting `e^{iθ} = cos θ + i sin θ` under the integral. -/
private lemma integral_exp_I_mul_eq_cos_add_sin {u g : ℝ → ℂ} (hu : Continuous u)
    (hg : Continuous g) :
    ∫ t in (0 : ℝ)..2 * π, Complex.exp (I * u t) * g t =
      (∫ t in (0 : ℝ)..2 * π, Complex.cos (u t) * g t) +
        I * ∫ t in (0 : ℝ)..2 * π, Complex.sin (u t) * g t := by
  have e : ∀ t, Complex.exp (I * u t) * g t =
      Complex.cos (u t) * g t + I * (Complex.sin (u t) * g t) := by
    intro t; rw [mul_comm I, Complex.exp_mul_I]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_add ((by fun_prop : Continuous fun t =>
      Complex.cos (u t) * g t).intervalIntegrable _ _)
    (((by fun_prop : Continuous fun t => Complex.sin (u t) * g t).const_mul I).intervalIntegrable
      _ _), intervalIntegral.integral_const_mul]

/-- `∫₀^{2π} e^{2ih cosh z cos t} ce_{2k}(t) dt = 2π A_0/ce_{2k}(π/2) · ce_{2k}(iz)` (28.10.1). -/
private lemma integral_exp_cosh_cos_mul_mathieuCe_even (k : ℕ) (h : ℝ) (z : ℂ) :
    ∫ t in (0 : ℝ)..2 * π, Complex.exp (2 * I * h * (Complex.cosh z * Complex.cos t)) *
        mathieuCe (2 * k) t (h ^ 2) =
      2 * π * (mathieuFourierA (2 * k) 0 (h ^ 2) / mathieuCe (2 * k) (π / 2) (h ^ 2)) *
        mathieuCe (2 * k) (I * z) (h ^ 2) := by
  set C := Complex.cosh z
  have hcI : Complex.cos (I * z) = C := by rw [mul_comm, Complex.cos_mul_I]
  set u : ℝ → ℂ := fun t => 2 * h * C * Real.cos t
  have hu : Continuous u := by simp only [u]; fun_prop
  have hcs : ∀ F : ℂ → ℂ, Continuous F →
      Continuous fun t => F (u t) * mathieuCe (2 * k) t (h ^ 2) :=
    fun F hF => (hF.comp hu).mul (continuous_mathieuCe_ofReal _ _)
  have e : ∀ t : ℝ, Complex.exp (2 * I * h * (C * Complex.cos t)) * mathieuCe (2 * k) t (h ^ 2) =
      Complex.exp (I * u t) * mathieuCe (2 * k) t (h ^ 2) := by
    intro t; simp only [u]; push_cast; ring_nf
  simp_rw [e]
  rw [integral_exp_I_mul_eq_cos_add_sin hu (continuous_mathieuCe_ofReal _ _)]
  have hsin : ∫ t in (0 : ℝ)..2 * π, Complex.sin (u t) * mathieuCe (2 * k) t (h ^ 2) = 0 := by
    refine integral_two_pi_eq_zero_of_antiperiodic (hcs _ Complex.continuous_sin) fun x => ?_
    simp only [u]
    push_cast
    rw [mathieuCe_even_add_pi, Complex.cos_add_pi]
    rw [show 2 * (h : ℂ) * C * -Complex.cos (x : ℂ) = -(2 * h * C * Complex.cos x) by ring,
      Complex.sin_neg]
    ring
  have hcos : ∫ t in (0 : ℝ)..2 * π, Complex.cos (u t) * mathieuCe (2 * k) t (h ^ 2) =
      4 * ∫ t in (0 : ℝ)..π / 2, Complex.cos (u t) * mathieuCe (2 * k) t (h ^ 2) := by
    refine integral_two_pi_eq_four_mul_integral_pi_div_two (hcs _ Complex.continuous_cos)
        (fun x => ?_) (fun x => ?_)
    · simp only [u]
      push_cast
      rw [mathieuCe_even_add_pi, Complex.cos_add_pi]
      rw [show 2 * (h : ℂ) * C * -Complex.cos (x : ℂ) = -(2 * h * C * Complex.cos x) by ring,
        Complex.cos_neg]
    · simp only [u]
      push_cast
      rw [mathieuCe_neg, Complex.cos_neg]
  have h10 := integral_cos_mathieuCe_even k h (I * z)
  rw [hcI] at h10
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [hsin, mul_zero, add_zero, hcos]
  have hI : ∫ t in (0 : ℝ)..π / 2, Complex.cos (u t) * mathieuCe (2 * k) t (h ^ 2) =
      π / 2 * (mathieuFourierA (2 * k) 0 (h ^ 2) / mathieuCe (2 * k) (π / 2) (h ^ 2) *
        mathieuCe (2 * k) (I * z) (h ^ 2)) := by
    rw [← h10]; field_simp; rfl
  rw [hI]; ring

/-- `∫₀^{2π} e^{2ih cosh z cos t} ce_{2k+1}(t) dt = -2πi h A_1/ce'_{2k+1}(π/2) · ce_{2k+1}(iz)`
(28.10.3). -/
private lemma integral_exp_cosh_cos_mul_mathieuCe_odd (k : ℕ) (h : ℝ) (z : ℂ) :
    ∫ t in (0 : ℝ)..2 * π, Complex.exp (2 * I * h * (Complex.cosh z * Complex.cos t)) *
        mathieuCe (2 * k + 1) t (h ^ 2) =
      2 * π * I * -(h * mathieuFourierA (2 * k + 1) 1 (h ^ 2) /
        deriv (fun w => mathieuCe (2 * k + 1) w (h ^ 2)) (π / 2)) *
        mathieuCe (2 * k + 1) (I * z) (h ^ 2) := by
  set C := Complex.cosh z
  have hcI : Complex.cos (I * z) = C := by rw [mul_comm, Complex.cos_mul_I]
  set u : ℝ → ℂ := fun t => 2 * h * C * Real.cos t
  have hu : Continuous u := by simp only [u]; fun_prop
  have hcs : ∀ F : ℂ → ℂ, Continuous F →
      Continuous fun t => F (u t) * mathieuCe (2 * k + 1) t (h ^ 2) :=
    fun F hF => (hF.comp hu).mul (continuous_mathieuCe_ofReal _ _)
  have e : ∀ t : ℝ, Complex.exp (2 * I * h * (C * Complex.cos t)) *
      mathieuCe (2 * k + 1) t (h ^ 2) =
      Complex.exp (I * u t) * mathieuCe (2 * k + 1) t (h ^ 2) := by
    intro t; simp only [u]; push_cast; ring_nf
  simp_rw [e]
  rw [integral_exp_I_mul_eq_cos_add_sin hu (continuous_mathieuCe_ofReal _ _)]
  have hc : ∫ t in (0 : ℝ)..2 * π, Complex.cos (u t) * mathieuCe (2 * k + 1) t (h ^ 2) = 0 := by
    refine integral_two_pi_eq_zero_of_antiperiodic (hcs _ Complex.continuous_cos) fun x => ?_
    simp only [u]
    push_cast
    rw [mathieuCe_odd_add_pi, Complex.cos_add_pi]
    rw [show 2 * (h : ℂ) * C * -Complex.cos (x : ℂ) = -(2 * h * C * Complex.cos x) by ring,
      Complex.cos_neg]
    ring
  have hs : ∫ t in (0 : ℝ)..2 * π, Complex.sin (u t) * mathieuCe (2 * k + 1) t (h ^ 2) =
      4 * ∫ t in (0 : ℝ)..π / 2, Complex.sin (u t) * mathieuCe (2 * k + 1) t (h ^ 2) := by
    refine integral_two_pi_eq_four_mul_integral_pi_div_two (hcs _ Complex.continuous_sin)
        (fun x => ?_) (fun x => ?_)
    · simp only [u]
      push_cast
      rw [mathieuCe_odd_add_pi, Complex.cos_add_pi]
      rw [show 2 * (h : ℂ) * C * -Complex.cos (x : ℂ) = -(2 * h * C * Complex.cos x) by ring,
        Complex.sin_neg]
      ring
    · simp only [u]
      push_cast
      rw [mathieuCe_neg, Complex.cos_neg]
  have h10 := integral_sin_mathieuCe_odd k h (I * z)
  rw [hcI] at h10
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [hc, zero_add, hs]
  have hI : ∫ t in (0 : ℝ)..π / 2, Complex.sin (u t) * mathieuCe (2 * k + 1) t (h ^ 2) =
      π / 2 * (-(h * mathieuFourierA (2 * k + 1) 1 (h ^ 2) /
        deriv (fun w => mathieuCe (2 * k + 1) w (h ^ 2)) (π / 2)) *
        mathieuCe (2 * k + 1) (I * z) (h ^ 2)) := by
    rw [← h10]; field_simp; rfl
  rw [hI]; ring

/-- `ce_n(0) ≠ 0`. -/
private lemma mathieuCe_zero_ne_zero (n : ℕ) (q : ℝ) : mathieuCe n 0 q ≠ 0 := by
  rw [mathieuCe_zero]; exact_mod_cast (mathieuCeZero_pos n q).ne'

/-- The left side of 28.28.2 in closed form, even `n = 2k`, all real `h`. -/
private lemma integral_kernel_mathieuCe_even_closedForm (k : ℕ) (h : ℝ) (z α : ℂ) :
    (2 * π : ℂ)⁻¹ * ∫ t in (0 : ℝ)..2 * π,
        Complex.exp (2 * I * h * mathieuKernelW z t α) * mathieuCe (2 * k) t (h ^ 2) =
      mathieuFourierA (2 * k) 0 (h ^ 2) / mathieuCe (2 * k) (π / 2) (h ^ 2) *
        mathieuCe (2 * k) (I * z) (h ^ 2) / mathieuCe (2 * k) 0 (h ^ 2) *
          mathieuCe (2 * k) α (h ^ 2) := by
  rw [integral_kernel_mathieuCe_eq_mul_mathieuCe, integral_exp_cosh_cos_mul_mathieuCe_even]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- The left side of 28.28.2 in closed form, odd `n = 2k + 1`, all real `h`. -/
private lemma integral_kernel_mathieuCe_odd_closedForm (k : ℕ) (h : ℝ) (z α : ℂ) :
    (2 * π : ℂ)⁻¹ * ∫ t in (0 : ℝ)..2 * π,
        Complex.exp (2 * I * h * mathieuKernelW z t α) * mathieuCe (2 * k + 1) t (h ^ 2) =
      I * -(h * mathieuFourierA (2 * k + 1) 1 (h ^ 2) /
        deriv (fun w => mathieuCe (2 * k + 1) w (h ^ 2)) (π / 2)) *
        mathieuCe (2 * k + 1) (I * z) (h ^ 2) / mathieuCe (2 * k + 1) 0 (h ^ 2) *
          mathieuCe (2 * k + 1) α (h ^ 2) := by
  rw [integral_kernel_mathieuCe_eq_mul_mathieuCe, integral_exp_cosh_cos_mul_mathieuCe_odd]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- 28.28.2 for `h > 0`. -/
private lemma integral_exp_mathieuCe_of_pos (n : ℕ) {h : ℝ} (hh : 0 < h) (z α : ℂ) :
    (2 * π : ℂ)⁻¹ * ∫ t in (0 : ℝ)..2 * π,
        Complex.exp (2 * I * h * mathieuKernelW z t α) * mathieuCe n t (h ^ 2) =
      I ^ n * mathieuCe n α (h ^ 2) * radialMathieuMc 1 n z h := by
  have hq : h ^ 2 ≠ 0 := by positivity
  have hs := ofReal_sqrt_two_div_pi_ne_zero
  rw [radialMathieuMc_one_eq n hh z, modMathieuCe_natCast]
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hA0 := mathieuFourierA_even_zero_ne_zero k hq
    have hc : mathieuCe (2 * k) (π / 2) (h ^ 2) ≠ 0 := by
      intro h0
      exact mathieuCe_deriv_not_both_zero (2 * k) (h ^ 2) ((π / 2 : ℝ) : ℂ) (by push_cast; exact h0)
        (deriv_mathieuCe_even_pi_div_two k (h ^ 2))
    have h0 := mathieuCe_zero_ne_zero (2 * k) (h ^ 2)
    rw [integral_kernel_mathieuCe_even_closedForm, mathieuJoinGe,
      ite_eq_left_of_eq_true _ _ (eq_true (even_two_mul k)), show 2 * k / 2 = k by omega,
      pow_mul, I_sq]
    field_simp
  · have hA1 := mathieuFourierA_odd_one_ne_zero k hq
    have hc : deriv (fun w => mathieuCe (2 * k + 1) w (h ^ 2)) (π / 2) ≠ 0 := by
      intro h0
      exact mathieuCe_deriv_not_both_zero (2 * k + 1) (h ^ 2) ((π / 2 : ℝ) : ℂ)
        (mathieuCe_odd_pi_div_two k (h ^ 2)) (by push_cast; exact h0)
    have h0 := mathieuCe_zero_ne_zero (2 * k + 1) (h ^ 2)
    have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    rw [integral_kernel_mathieuCe_odd_closedForm, mathieuJoinGe,
      ite_eq_right_of_eq_false _ _ (eq_false (Nat.not_even_two_mul_add_one k)),
      show (2 * k + 1) / 2 = k by omega,
      show I ^ (2 * k + 1) = (-1) ^ k * I by rw [pow_succ, pow_mul, I_sq],
      show ((-1 : ℂ)) ^ (k + 1) = (-1) ^ k * (-1) from pow_succ _ _]
    field_simp

/-- `Mc^{(1)}_n(z, -h) = (-1)^n Mc^{(1)}_n(z, h)`. -/
private lemma radialMathieuMc_one_neg_parameter (n : ℕ) (z H : ℂ) :
    radialMathieuMc 1 n z (-H) = (-1 : ℂ) ^ n * radialMathieuMc 1 n z H := by
  have hidx : modMathieuIndex (n : ℂ) (-H) = modMathieuIndex (n : ℂ) H := by
    unfold modMathieuIndex; rw [neg_sq]
  simp only [radialMathieuMc, modMathieuM, hidx, neg_sq]
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  congr 1
  funext ℓ
  set k := modMathieuIndex (n : ℂ) H
  simp only [modMathieuTerm, mathieuCylExp, neg_sq]
  rw [show (n : ℂ) + k + ℓ = ((n + k + ℓ : ℤ) : ℂ) by push_cast; ring,
    besselJExp_intCast_neg_parameter, besselJExp_intCast_neg_parameter]
  have e : (-1 : ℂ) ^ (ℓ - k) * (-1 : ℂ) ^ ((n : ℤ) + k + ℓ) = (-1 : ℂ) ^ n := by
    rw [← zpow_add₀ (by norm_num), show ℓ - k + ((n : ℤ) + k + ℓ) = n + 2 * ℓ by ring,
      zpow_add₀ (by norm_num), zpow_mul, zpow_natCast]
    norm_num
  linear_combination (mathieuMeCoeff (n : ℂ) (H ^ 2) k)⁻¹ *
    ((-1 : ℂ) ^ ℓ * mathieuMeCoeff (n : ℂ) (H ^ 2) ℓ *
    besselJExp ((ℓ - k : ℤ) : ℂ) H (-z) * besselJExp ((n + k + ℓ : ℤ) : ℂ) H z) * e

/-- `∫₀^{2π} cos(m x) dx = 0` for an integer `m ≠ 0`. -/
private lemma integral_cos_intCast_mul_eq_zero {m : ℤ} (hm : m ≠ 0) :
    ∫ x in (0 : ℝ)..2 * π, Complex.cos ((m : ℂ) * x) = 0 := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.sin ((m : ℂ) * x) / m)
      (Complex.cos ((m : ℂ) * x)) x := by
    intro x
    have := (((hasDerivAt_id (x : ℂ)).const_mul (m : ℂ)).csin).comp_ofReal.div_const (m : ℂ)
    convert this using 1
    · simp only [id]
    · simp only [id]; field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((by fun_prop : Continuous fun x : ℝ => Complex.cos ((m : ℂ) * x)).intervalIntegrable _ _)]
  have : Complex.sin ((m : ℂ) * (2 * (π : ℂ))) = 0 := by
    rw [show (m : ℂ) * (2 * (π : ℂ)) = ((2 * m : ℤ) : ℂ) * π by push_cast; ring]
    exact Complex.sin_int_mul_pi _
  simp [this]

/-- `J_k(0 · e^w) = δ_{k0}` for the continued Bessel function of integer order. -/
private lemma besselJExp_intCast_parameter_zero (k : ℤ) (w : ℂ) :
    besselJExp k 0 w = if k = 0 then 1 else 0 := by
  rw [besselJExp_intCast, zero_mul]
  split_ifs with hk
  · subst hk; simpa using DLMF.Bessel.besselJ_zero_zero
  · rw [DLMF.Bessel.besselJ_eq_regularized, zero_div,
      Complex.zero_cpow (by exact_mod_cast hk), zero_mul]

/-- The coefficients `c^N_{2m}(0)` vanish unless `N + 2m = ±N`. -/
private lemma mathieuMeCoeff_natCast_q_zero_of_add_eq_zero (N : ℕ) (m : ℤ)
    (hm : (N : ℤ) + 2 * m = 0) (hN : N ≠ 0) :
    mathieuMeCoeff (N : ℂ) ((0 : ℂ) ^ 2) m = 0 := by
  have := mathieuMeCoeff_natCast_eq_integral N 0 m
  push_cast at this
  rw [show (0 : ℂ) ^ 2 = 0 by ring, this]
  have e : ∀ x : ℝ, mathieuCe N x 0 * Complex.cos (((N : ℂ) + 2 * m) * x) =
      Complex.cos (((N : ℤ) : ℂ) * x) := by
    intro x
    rw [mathieuCe_q_zero hN, show ((N : ℂ) + 2 * m) = ((N + 2 * m : ℤ) : ℂ) by push_cast; ring,
      hm]
    simp
  simp_rw [e]
  rw [integral_cos_intCast_mul_eq_zero (by exact_mod_cast hN), mul_zero]

/-- The coefficients `c^0_{2m}(0) = δ_{m0}`. -/
private lemma mathieuMeCoeff_zero_q_zero (m : ℤ) :
    mathieuMeCoeff ((0 : ℕ) : ℂ) ((0 : ℂ) ^ 2) m = if m = 0 then 1 else 0 := by
  have := mathieuMeCoeff_natCast_eq_integral 0 0 m
  push_cast at this
  rw [show (0 : ℂ) ^ 2 = 0 by ring, Nat.cast_zero, this]
  simp only [mathieuCe_zero_zero, zero_add]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt 2 := by positivity
    exact_mod_cast this.ne'
  rw [intervalIntegral.integral_const_mul]
  split_ifs with hm
  · subst hm; simp; field_simp
  · rw [show ∫ x in (0 : ℝ)..2 * π, Complex.cos (2 * (m : ℂ) * x) =
        ∫ x in (0 : ℝ)..2 * π, Complex.cos (((2 * m : ℤ) : ℂ) * x) by push_cast; rfl,
      integral_cos_intCast_mul_eq_zero (by omega)]
    ring

/-- `Mc^{(1)}_n(z, 0) = δ_{n0}`. -/
private lemma radialMathieuMc_one_parameter_zero (n : ℕ) (z : ℂ) :
    radialMathieuMc 1 n z 0 = if n = 0 then 1 else 0 := by
  simp only [radialMathieuMc, modMathieuM]
  set K := modMathieuIndex (n : ℂ) 0
  have hterm : ∀ ℓ, ℓ ≠ K → modMathieuTerm 1 n z 0 K ℓ = 0 := by
    intro ℓ hℓ
    simp only [modMathieuTerm, mathieuCylExp, besselJExp_intCast_parameter_zero]
    simp only [sub_eq_zero, hℓ, ↓reduceIte]; ring
  rw [tsum_eq_single K hterm]
  simp only [modMathieuTerm, mathieuCylExp, sub_self, besselJExp_intCast_parameter_zero, ite_true]
  rw [show (n : ℂ) + K + K = ((n + K + K : ℤ) : ℂ) by push_cast; ring,
                                                        besselJExp_intCast_parameter_zero]
  by_cases hn : n = 0
  · subst hn
    have hK : K = 0 := by
      have hex : ∃ m : ℤ, mathieuMeCoeff ((0 : ℕ) : ℂ) ((0 : ℂ) ^ 2) m ≠ 0 :=
        ⟨0, by rw [mathieuMeCoeff_zero_q_zero]; simp⟩
      have : K = hex.choose := by simp only [K, modMathieuIndex, hex, ↓reduceDIte]
      have h1 := hex.choose_spec
      rw [← this, mathieuMeCoeff_zero_q_zero] at h1
      by_contra hK; simp [hK] at h1
    rw [hK, mathieuMeCoeff_zero_q_zero]; simp
  · simp only [hn, ↓reduceIte]
    by_cases h2 : (n : ℤ) + K + K = 0
    · rw [mathieuMeCoeff_natCast_q_zero_of_add_eq_zero n K (by linarith) hn]; simp
    · simp only [h2, ↓reduceIte]; ring

/-- **DLMF 28.28.2** (proof), all real `h`. -/
theorem integral_exp_mathieuCe' (n : ℕ) (h : ℝ) (z α : ℂ) :
    (2 * π : ℂ)⁻¹ * ∫ t in (0 : ℝ)..2 * π,
        Complex.exp (2 * I * h * mathieuKernelW z t α) * mathieuCe n t (h ^ 2) =
      I ^ n * mathieuCe n α (h ^ 2) * radialMathieuMc 1 n z h := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rcases lt_trichotomy h 0 with hneg | rfl | hpos
  · have hpos' : 0 < -h := neg_pos.2 hneg
    have P := integral_exp_mathieuCe_of_pos n hpos' z α
    rw [show (-h) ^ 2 = h ^ 2 by ring] at P
    have hM := radialMathieuMc_one_neg_parameter n z ((-h : ℝ) : ℂ)
    rw [show -((-h : ℝ) : ℂ) = (h : ℂ) by push_cast; ring] at hM
    rw [hM, show I ^ n * mathieuCe n α (h ^ 2) * ((-1 : ℂ) ^ n *
        radialMathieuMc 1 n z ((-h : ℝ) : ℂ)) = (-1 : ℂ) ^ n *
        (I ^ n * mathieuCe n α (h ^ 2) * radialMathieuMc 1 n z ((-h : ℝ) : ℂ)) by ring, ← P]
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · have L2 := integral_kernel_mathieuCe_even_closedForm k (-h) z α
      rw [show (-h) ^ 2 = h ^ 2 by ring] at L2
      rw [integral_kernel_mathieuCe_even_closedForm, L2, pow_mul]
      simp
    · have L2 := integral_kernel_mathieuCe_odd_closedForm k (-h) z α
      rw [show (-h) ^ 2 = h ^ 2 by ring] at L2
      rw [integral_kernel_mathieuCe_odd_closedForm, L2,
        show ((-1 : ℂ)) ^ (2 * k + 1) = -1 by rw [pow_succ, pow_mul]; simp]
      push_cast
      ring
  · rw [Complex.ofReal_zero, radialMathieuMc_one_parameter_zero]
    simp only [mul_zero, zero_mul, Complex.exp_zero, one_mul, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    by_cases hn : n = 0
    · subst hn
      simp only [mathieuCe_zero_zero, intervalIntegral.integral_const, sub_zero,
        Complex.real_smul, ↓reduceIte, pow_zero, one_mul, mul_one]
      push_cast
      field_simp
    · have e : ∀ t : ℝ, mathieuCe n t 0 = Complex.cos (((n : ℤ) : ℂ) * t) := fun t => by
        rw [mathieuCe_q_zero hn]; push_cast; rfl
      simp only [e, hn, ↓reduceIte, mul_zero]
      rw [integral_cos_intCast_mul_eq_zero (by exact_mod_cast hn), mul_zero]
  · exact integral_exp_mathieuCe_of_pos n hpos z α

/-- `se_n` is continuous on the real line. -/
private lemma continuous_mathieuSe_ofReal (n : ℕ) (q : ℝ) : Continuous fun t : ℝ =>
    mathieuSe n t q :=
  (isMathieuSolution_mathieuSe n q).differentiable.continuous.comp continuous_ofReal

/-- The kernel integral against `se_n` is `G'(0)/se_n'(0) · se_n(α)`, with
`G'(0) = ∫₀^{2π} 2ih sinh z sin t e^{2ih cosh z cos t} se_n(t) dt`. -/
private lemma integral_kernel_mathieuSe_eq_mul_mathieuSe {n : ℕ} (hn : n ≠ 0) (h : ℝ) (z α : ℂ) :
    ∫ t in (0 : ℝ)..2 * π, Complex.exp (2 * I * h * mathieuKernelW z t α) *
        mathieuSe n t (h ^ 2) =
      (∫ t in (0 : ℝ)..2 * π, 2 * I * h * (Complex.sinh z * Complex.sin t) *
        Complex.exp (2 * I * h * (Complex.cosh z * Complex.cos t)) * mathieuSe n t (h ^ 2)) /
        deriv (fun w => mathieuSe n w (h ^ 2)) 0 * mathieuSe n α (h ^ 2) := by
  have hper : ∀ t : ℝ, mathieuSe n ((t + 2 * π : ℝ) : ℂ) (h ^ 2) = mathieuSe n t (h ^ 2) := by
    intro t; push_cast; exact mathieuSe_add_two_pi hn _ _
  have hdper : ∀ t : ℝ, deriv (fun z => mathieuSe n z (h ^ 2)) ((t + 2 * π : ℝ) : ℂ) =
      deriv (fun z => mathieuSe n z (h ^ 2)) t := by
    intro t
    have e : (fun z => mathieuSe n z (h ^ 2)) =
        fun z => mathieuSe n (z + (2 * π : ℂ)) (h ^ 2) :=
      funext fun w => (mathieuSe_add_two_pi hn w _).symm
    push_cast
    conv_rhs => rw [e]
    have := deriv_comp_add_const (f := fun w => mathieuSe n w (h ^ 2)) (a := (2 * π : ℂ))
      (x := (t : ℂ))
    rw [this]
  have hG := isMathieuSolution_integral_exp_mathieuKernelW (a := mathieuB n (h ^ 2)) h z
    (f := fun t : ℝ => mathieuSe n t (h ^ 2))
    (f' := fun t : ℝ => deriv (fun z => mathieuSe n z (h ^ 2)) t)
    (hasDerivAt_mathieuSe_ofReal _ _) (hasDerivAt_deriv_mathieuSe_ofReal _ _) hper hdper
  have hodd : ∀ α, (fun α => ∫ t in (0 : ℝ)..2 * π,
      Complex.exp (2 * I * h * mathieuKernelW z t α) * mathieuSe n t (h ^ 2)) (-α) =
      -(fun α => ∫ t in (0 : ℝ)..2 * π,
      Complex.exp (2 * I * h * mathieuKernelW z t α) * mathieuSe n t (h ^ 2)) α := by
    intro α
    have := integral_exp_mathieuKernelW_neg h z
        (f := fun t : ℝ => mathieuSe n t (h ^ 2)) hper (s := -1)
      (fun t => by push_cast; rw [mathieuSe_neg]; ring) α
    simpa using this
  have := eq_mul_mathieuSe_of_odd hG hodd α
  rw [this]
  congr 2
  have hd := hasDerivAt_integral_exp_mathieuKernelW h z (continuous_mathieuSe_ofReal n (h ^ 2)) 0
  rw [hd.deriv]
  congr 1
  funext t
  rw [(hasDerivAt_mathieuKernelW z t 0).deriv]
  simp [mathieuKernelW]

/-- `∫₀^{2π} 2ih sinh z sin t e^{2ih cosh z cos t} se_{2k+1}(t) dt`, by 28.10.6. -/
private lemma integral_sinh_sin_exp_cosh_cos_mul_mathieuSe_odd (k : ℕ) (h : ℝ) (z : ℂ) :
    ∫ t in (0 : ℝ)..2 * π, 2 * I * h * (Complex.sinh z * Complex.sin t) *
        Complex.exp (2 * I * h * (Complex.cosh z * Complex.cos t)) *
          mathieuSe (2 * k + 1) t (h ^ 2) =
      2 * π * h * mathieuFourierB (2 * k + 1) 1 (h ^ 2) / mathieuSe (2 * k + 1) (π / 2) (h ^ 2) *
        mathieuSe (2 * k + 1) (I * z) (h ^ 2) := by
  set C := Complex.cosh z
  set Sh := Complex.sinh z
  have hcI : Complex.cos (I * z) = C := by rw [mul_comm, Complex.cos_mul_I]
  have hsI : Complex.sin (I * z) = Sh * I := by rw [mul_comm, Complex.sin_mul_I]
  set u : ℝ → ℂ := fun t => 2 * h * C * Real.cos t
  have hu : Continuous u := by simp only [u]; fun_prop
  set g : ℝ → ℂ := fun t => Sh * Real.sin t * mathieuSe (2 * k + 1) t (h ^ 2)
  have hg : Continuous g := by
    simp only [g]; exact (by fun_prop : Continuous fun t : ℝ => Sh * (Real.sin t : ℂ)).mul
      (continuous_mathieuSe_ofReal _ _)
  have hcs : ∀ F : ℂ → ℂ, Continuous F → Continuous fun t => F (u t) * g t :=
    fun F hF => (hF.comp hu).mul hg
  have e : ∀ t : ℝ, 2 * I * h * (Sh * Complex.sin t) * Complex.exp (2 * I * h * (C * Complex.cos t))
      * mathieuSe (2 * k + 1) t (h ^ 2) = 2 * I * h * (Complex.exp (I * u t) * g t) := by
    intro t; simp only [u, g]; push_cast; ring_nf
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, integral_exp_I_mul_eq_cos_add_sin hu hg]
  have hz : ∫ t in (0 : ℝ)..2 * π, Complex.sin (u t) * g t = 0 := by
    refine integral_two_pi_eq_zero_of_antiperiodic (hcs _ Complex.continuous_sin) fun x => ?_
    simp only [u, g]
    push_cast
    rw [mathieuSe_odd_add_pi, Complex.cos_add_pi, Complex.sin_add_pi]
    rw [show 2 * (h : ℂ) * C * -Complex.cos (x : ℂ) = -(2 * h * C * Complex.cos x) by ring,
      Complex.sin_neg]
    ring
  have hq : ∫ t in (0 : ℝ)..2 * π, Complex.cos (u t) * g t =
      4 * ∫ t in (0 : ℝ)..π / 2, Complex.cos (u t) * g t := by
    refine integral_two_pi_eq_four_mul_integral_pi_div_two (hcs _ Complex.continuous_cos)
        (fun x => ?_) (fun x => ?_)
    · simp only [u, g]
      push_cast
      rw [mathieuSe_odd_add_pi, Complex.cos_add_pi, Complex.sin_add_pi]
      rw [show 2 * (h : ℂ) * C * -Complex.cos (x : ℂ) = -(2 * h * C * Complex.cos x) by ring,
        Complex.cos_neg]
      ring
    · simp only [u, g]
      push_cast
      rw [mathieuSe_neg, Complex.cos_neg, Complex.sin_neg]
      ring
  have h10 := integral_sin_cos_mathieuSe_odd k h (I * z)
  rw [hcI, hsI] at h10
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : ∫ t in (0 : ℝ)..π / 2, Complex.cos (u t) * g t =
      π / 2 / I * ((mathieuFourierB (2 * k + 1) 1 (h ^ 2) /
        (2 * mathieuSe (2 * k + 1) (π / 2) (h ^ 2))) * mathieuSe (2 * k + 1) (I * z) (h ^ 2)) := by
    rw [← h10]
    have e2 : ∀ t : ℝ, Sh * I * (Real.sin t : ℂ) * Complex.cos (2 * h * C * Real.cos t) *
        mathieuSe (2 * k + 1) t (h ^ 2) = I * (Complex.cos (u t) * g t) := by
      intro t; simp only [u, g]; ring
    simp_rw [e2]
    rw [intervalIntegral.integral_const_mul]
    field_simp
  rw [hz, mul_zero, add_zero, hq, hI]
  field_simp
  ring_nf

/-- `∫₀^{2π} 2ih sinh z sin t e^{2ih cosh z cos t} se_{2k+2}(t) dt`, by 28.10.7. -/
private lemma integral_sinh_sin_exp_cosh_cos_mul_mathieuSe_even (k : ℕ) (h : ℝ) (z : ℂ) :
    ∫ t in (0 : ℝ)..2 * π, 2 * I * h * (Complex.sinh z * Complex.sin t) *
        Complex.exp (2 * I * h * (Complex.cosh z * Complex.cos t)) *
          mathieuSe (2 * k + 2) t (h ^ 2) =
      -(2 * π * I * h ^ 2 * mathieuFourierB (2 * k + 2) 2 (h ^ 2) /
        deriv (fun w => mathieuSe (2 * k + 2) w (h ^ 2)) (π / 2)) *
        mathieuSe (2 * k + 2) (I * z) (h ^ 2) := by
  set C := Complex.cosh z
  set Sh := Complex.sinh z
  have hcI : Complex.cos (I * z) = C := by rw [mul_comm, Complex.cos_mul_I]
  have hsI : Complex.sin (I * z) = Sh * I := by rw [mul_comm, Complex.sin_mul_I]
  set u : ℝ → ℂ := fun t => 2 * h * C * Real.cos t
  have hu : Continuous u := by simp only [u]; fun_prop
  set g : ℝ → ℂ := fun t => Sh * Real.sin t * mathieuSe (2 * k + 2) t (h ^ 2)
  have hg : Continuous g := by
    simp only [g]; exact (by fun_prop : Continuous fun t : ℝ => Sh * (Real.sin t : ℂ)).mul
      (continuous_mathieuSe_ofReal _ _)
  have hcs : ∀ F : ℂ → ℂ, Continuous F → Continuous fun t => F (u t) * g t :=
    fun F hF => (hF.comp hu).mul hg
  have e : ∀ t : ℝ, 2 * I * h * (Sh * Complex.sin t) * Complex.exp (2 * I * h * (C * Complex.cos t))
      * mathieuSe (2 * k + 2) t (h ^ 2) = 2 * I * h * (Complex.exp (I * u t) * g t) := by
    intro t; simp only [u, g]; push_cast; ring_nf
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, integral_exp_I_mul_eq_cos_add_sin hu hg]
  have hz : ∫ t in (0 : ℝ)..2 * π, Complex.cos (u t) * g t = 0 := by
    refine integral_two_pi_eq_zero_of_antiperiodic (hcs _ Complex.continuous_cos) fun x => ?_
    simp only [u, g]
    push_cast
    rw [mathieuSe_even_add_pi, Complex.cos_add_pi, Complex.sin_add_pi]
    rw [show 2 * (h : ℂ) * C * -Complex.cos (x : ℂ) = -(2 * h * C * Complex.cos x) by ring,
      Complex.cos_neg]
    ring
  have hq : ∫ t in (0 : ℝ)..2 * π, Complex.sin (u t) * g t =
      4 * ∫ t in (0 : ℝ)..π / 2, Complex.sin (u t) * g t := by
    refine integral_two_pi_eq_four_mul_integral_pi_div_two (hcs _ Complex.continuous_sin)
        (fun x => ?_) (fun x => ?_)
    · simp only [u, g]
      push_cast
      rw [mathieuSe_even_add_pi, Complex.cos_add_pi, Complex.sin_add_pi]
      rw [show 2 * (h : ℂ) * C * -Complex.cos (x : ℂ) = -(2 * h * C * Complex.cos x) by ring,
        Complex.sin_neg]
      ring
    · simp only [u, g]
      push_cast
      rw [mathieuSe_neg, Complex.cos_neg, Complex.sin_neg]
      ring
  have h10 := integral_sin_sin_mathieuSe_even k h (I * z)
  rw [hcI, hsI] at h10
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : ∫ t in (0 : ℝ)..π / 2, Complex.sin (u t) * g t =
      π / 2 / I * (-(h * mathieuFourierB (2 * k + 2) 2 (h ^ 2) /
        (2 * deriv (fun w => mathieuSe (2 * k + 2) w (h ^ 2)) (π / 2))) *
        mathieuSe (2 * k + 2) (I * z) (h ^ 2)) := by
    rw [← h10]
    have e2 : ∀ t : ℝ, Sh * I * (Real.sin t : ℂ) * Complex.sin (2 * h * C * Real.cos t) *
        mathieuSe (2 * k + 2) t (h ^ 2) = I * (Complex.sin (u t) * g t) := by
      intro t; simp only [u, g]; ring
    simp_rw [e2]
    rw [intervalIntegral.integral_const_mul]
    field_simp
  rw [hz, zero_add, hq, hI]
  field_simp
  ring_nf

/-- `M^{(1)}_m(z, -h) = (-1)^m M^{(1)}_m(z, h)` for integer `m`. -/
private lemma modMathieuM_one_intCast_neg_parameter (m : ℤ) (z H : ℂ) :
    modMathieuM 1 (m : ℂ) z (-H) = (-1 : ℂ) ^ m * modMathieuM 1 m z H := by
  have hidx : modMathieuIndex (m : ℂ) (-H) = modMathieuIndex (m : ℂ) H := by
    unfold modMathieuIndex; rw [neg_sq]
  simp only [modMathieuM, hidx, neg_sq]
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  congr 1
  funext ℓ
  set k := modMathieuIndex (m : ℂ) H
  simp only [modMathieuTerm, mathieuCylExp, neg_sq]
  rw [show (m : ℂ) + k + ℓ = ((m + k + ℓ : ℤ) : ℂ) by push_cast; ring,
    besselJExp_intCast_neg_parameter, besselJExp_intCast_neg_parameter]
  have e : (-1 : ℂ) ^ (ℓ - k) * (-1 : ℂ) ^ (m + k + ℓ) = (-1 : ℂ) ^ m := by
    rw [← zpow_add₀ (by norm_num), show ℓ - k + (m + k + ℓ) = m + 2 * ℓ by ring,
      zpow_add₀ (by norm_num), zpow_mul]
    norm_num
  linear_combination (mathieuMeCoeff (m : ℂ) (H ^ 2) k)⁻¹ *
    ((-1 : ℂ) ^ ℓ * mathieuMeCoeff (m : ℂ) (H ^ 2) ℓ *
    besselJExp ((ℓ - k : ℤ) : ℂ) H (-z) * besselJExp ((m + k + ℓ : ℤ) : ℂ) H z) * e

/-- `Ms^{(1)}_n(z, -h) = (-1)^n Ms^{(1)}_n(z, h)`. -/
private lemma radialMathieuMs_one_neg_parameter (n : ℕ) (z H : ℂ) :
    radialMathieuMs 1 n z (-H) = (-1 : ℂ) ^ n * radialMathieuMs 1 n z H := by
  simp only [radialMathieuMs]
  rw [show -(n : ℂ) = ((-(n : ℤ) : ℤ) : ℂ) by push_cast; ring,
                                                modMathieuM_one_intCast_neg_parameter,
    zpow_neg, zpow_natCast]
  have : ((-1 : ℂ) ^ n)⁻¹ = (-1) ^ n := by
    rw [← inv_pow, inv_neg, inv_one]
  rw [this]

/-- `Ms^{(1)}_n(z, 0) = 0`, `n ≥ 1`. -/
private lemma radialMathieuMs_one_parameter_zero {n : ℕ} (hn : n ≠ 0) (z : ℂ) :
    radialMathieuMs 1 n z 0 = 0 := by
  simp only [radialMathieuMs]
  rw [show -(n : ℂ) = ((-(n : ℤ) : ℤ) : ℂ) by push_cast; ring]
  simp only [modMathieuM]
  set K := modMathieuIndex ((-(n : ℤ) : ℤ) : ℂ) 0
  have hterm : ∀ ℓ, ℓ ≠ K → modMathieuTerm 1 ((-(n : ℤ) : ℤ) : ℂ) z 0 K ℓ = 0 := by
    intro ℓ hℓ
    simp only [modMathieuTerm, mathieuCylExp, besselJExp_intCast_parameter_zero]
    simp only [sub_eq_zero, hℓ, ↓reduceIte]; ring
  rw [tsum_eq_single K hterm]
  simp only [modMathieuTerm, mathieuCylExp, sub_self, besselJExp_intCast_parameter_zero, ↓reduceIte]
  rw [show ((-(n : ℤ) : ℤ) : ℂ) + K + K = ((-(n : ℤ) + K + K : ℤ) : ℂ) by push_cast; ring,
    besselJExp_intCast_parameter_zero]
  by_cases h2 : -(n : ℤ) + K + K = 0
  · have hc := mathieuMeCoeff_neg_natCast_eq_integral hn 0 K
    rw [show -(n : ℤ) + 2 * K = 0 by linarith] at hc
    simp only [Int.cast_zero, zero_mul, Complex.sin_zero, mul_zero,
      intervalIntegral.integral_zero] at hc
    push_cast at hc
    rw [show (0 : ℂ) ^ 2 = 0 by ring]
    push_cast
    rw [hc]; simp
  · simp only [h2, ↓reduceIte]; ring

/-- `∫₀^{2π} sin(m x) dx = 0` for an integer `m ≠ 0`. -/
private lemma integral_sin_intCast_mul_eq_zero {m : ℤ} (hm : m ≠ 0) :
    ∫ x in (0 : ℝ)..2 * π, Complex.sin ((m : ℂ) * x) = 0 := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => -Complex.cos ((m : ℂ) * x) / m)
      (Complex.sin ((m : ℂ) * x)) x := by
    intro x
    have := ((((hasDerivAt_id (x : ℂ)).const_mul (m : ℂ)).ccos).comp_ofReal.neg).div_const (m : ℂ)
    convert this using 1
    · funext y; simp only [id, Pi.neg_apply]
    · simp only [id]; field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((by fun_prop : Continuous fun x : ℝ => Complex.sin ((m : ℂ) * x)).intervalIntegrable _ _)]
  have : Complex.cos ((m : ℂ) * (2 * (π : ℂ))) = 1 := by
    rw [show (m : ℂ) * (2 * (π : ℂ)) = (m : ℂ) * (2 * π) by ring]
    exact_mod_cast Complex.cos_int_mul_two_pi m
  push_cast
  rw [this]; simp

/-- `se_n'(0) ≠ 0`. -/
private lemma deriv_mathieuSe_zero_ne_zero (n : ℕ) (q : ℝ) : deriv
    (fun w => mathieuSe n w q) 0 ≠ 0 := by
  rw [deriv_mathieuSe_zero]; exact_mod_cast (mathieuSeDerivZero_pos n q).ne'

/-- Closed form of the left side of 28.28.3, odd `n = 2k + 1`, all real `h`. -/
private lemma integral_kernel_mathieuSe_odd_closedForm (k : ℕ) (h : ℝ) (z α : ℂ) :
    (2 * π : ℂ)⁻¹ * ∫ t in (0 : ℝ)..2 * π,
        Complex.exp (2 * I * h * mathieuKernelW z t α) * mathieuSe (2 * k + 1) t (h ^ 2) =
      h * mathieuFourierB (2 * k + 1) 1 (h ^ 2) / mathieuSe (2 * k + 1) (π / 2) (h ^ 2) *
        mathieuSe (2 * k + 1) (I * z) (h ^ 2) / deriv (fun w => mathieuSe (2 * k + 1) w (h ^ 2)) 0 *
          mathieuSe (2 * k + 1) α (h ^ 2) := by
  rw [integral_kernel_mathieuSe_eq_mul_mathieuSe (by omega),
      integral_sinh_sin_exp_cosh_cos_mul_mathieuSe_odd]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- Closed form of the left side of 28.28.3, even `n = 2k + 2`, all real `h`. -/
private lemma integral_kernel_mathieuSe_even_closedForm (k : ℕ) (h : ℝ) (z α : ℂ) :
    (2 * π : ℂ)⁻¹ * ∫ t in (0 : ℝ)..2 * π,
        Complex.exp (2 * I * h * mathieuKernelW z t α) * mathieuSe (2 * k + 2) t (h ^ 2) =
      -(I * h ^ 2 * mathieuFourierB (2 * k + 2) 2 (h ^ 2) /
        deriv (fun w => mathieuSe (2 * k + 2) w (h ^ 2)) (π / 2)) *
        mathieuSe (2 * k + 2) (I * z) (h ^ 2) / deriv (fun w => mathieuSe (2 * k + 2) w (h ^ 2)) 0 *
          mathieuSe (2 * k + 2) α (h ^ 2) := by
  rw [integral_kernel_mathieuSe_eq_mul_mathieuSe (by omega),
      integral_sinh_sin_exp_cosh_cos_mul_mathieuSe_even]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- 28.28.3 for `h > 0`. -/
private lemma integral_exp_mathieuSe_of_pos {n : ℕ} (hn : n ≠ 0) {h : ℝ} (hh : 0 < h) (z α : ℂ) :
    (2 * π : ℂ)⁻¹ * ∫ t in (0 : ℝ)..2 * π,
        Complex.exp (2 * I * h * mathieuKernelW z t α) * mathieuSe n t (h ^ 2) =
      I ^ n * mathieuSe n α (h ^ 2) * radialMathieuMs 1 n z h := by
  have hq : h ^ 2 ≠ 0 := by positivity
  have hs := ofReal_sqrt_two_div_pi_ne_zero
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  rw [radialMathieuMs_one_eq hn hh z, modMathieuSe_natCast hn]
  have hd0 := deriv_mathieuSe_zero_ne_zero n (h ^ 2)
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [show 2 * (k + 1) = 2 * k + 2 by ring] at hd0 ⊢
    have hB2 := mathieuFourierB_even_two_ne_zero k hq
    have hc : deriv (fun w => mathieuSe (2 * k + 2) w (h ^ 2)) (π / 2) ≠ 0 := by
      intro h0
      exact mathieuSe_deriv_not_both_zero (2 * k + 2) (h ^ 2) ((π / 2 : ℝ) : ℂ)
        (mathieuSe_even_pi_div_two k (h ^ 2)) (by push_cast; exact h0)
    rw [integral_kernel_mathieuSe_even_closedForm, mathieuJoinGo,
      ite_eq_right_of_eq_false _ _ (eq_false (by
        rw [Nat.not_odd_iff_even]; exact ⟨k + 1, by ring⟩)),
      show (2 * k + 2 - 2) / 2 + 1 = k + 1 by omega,
      show I ^ (2 * k + 2) = (-1) ^ (k + 1) by rw [show 2 * k + 2 = 2 * (k + 1) by ring,
        pow_mul, I_sq]]
    field_simp
  · have hB1 := mathieuFourierB_odd_one_ne_zero k hq
    have hc : mathieuSe (2 * k + 1) (π / 2) (h ^ 2) ≠ 0 := by
      intro h0
      exact mathieuSe_deriv_not_both_zero (2 * k + 1) (h ^ 2) ((π / 2 : ℝ) : ℂ)
        (by push_cast; exact h0) (deriv_mathieuSe_odd_pi_div_two k (h ^ 2))
    rw [integral_kernel_mathieuSe_odd_closedForm, mathieuJoinGo,
      ite_eq_left_of_eq_true _ _ (eq_true (odd_two_mul_add_one k)),
      show (2 * k + 1) / 2 = k by omega,
      show I ^ (2 * k + 1) = (-1) ^ k * I by rw [pow_succ, pow_mul, I_sq]]
    field_simp
    ring_nf
    rw [I_sq]; ring

/-- **DLMF 28.28.3** (proof), all real `h`. -/
theorem integral_exp_mathieuSe' {n : ℕ} (hn : n ≠ 0) (h : ℝ) (z α : ℂ) :
    (2 * π : ℂ)⁻¹ * ∫ t in (0 : ℝ)..2 * π,
        Complex.exp (2 * I * h * mathieuKernelW z t α) * mathieuSe n t (h ^ 2) =
      I ^ n * mathieuSe n α (h ^ 2) * radialMathieuMs 1 n z h := by
  rcases lt_trichotomy h 0 with hneg | rfl | hpos
  · have hpos' : 0 < -h := neg_pos.2 hneg
    have P := integral_exp_mathieuSe_of_pos hn hpos' z α
    rw [show (-h) ^ 2 = h ^ 2 by ring] at P
    have hM := radialMathieuMs_one_neg_parameter n z ((-h : ℝ) : ℂ)
    rw [show -((-h : ℝ) : ℂ) = (h : ℂ) by push_cast; ring] at hM
    rw [hM, show I ^ n * mathieuSe n α (h ^ 2) * ((-1 : ℂ) ^ n *
        radialMathieuMs 1 n z ((-h : ℝ) : ℂ)) = (-1 : ℂ) ^ n *
        (I ^ n * mathieuSe n α (h ^ 2) * radialMathieuMs 1 n z ((-h : ℝ) : ℂ)) by ring, ← P]
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [show 2 * (k + 1) = 2 * k + 2 by ring]
      have L2 := integral_kernel_mathieuSe_even_closedForm k (-h) z α
      rw [show (-h) ^ 2 = h ^ 2 by ring] at L2
      have hp : ((-1 : ℂ)) ^ (2 * k + 2) = 1 := by
        rw [show 2 * k + 2 = 2 * (k + 1) by ring, pow_mul]; simp
      rw [integral_kernel_mathieuSe_even_closedForm, L2, hp]
      push_cast
      ring
    · have L2 := integral_kernel_mathieuSe_odd_closedForm k (-h) z α
      rw [show (-h) ^ 2 = h ^ 2 by ring] at L2
      have hp : ((-1 : ℂ)) ^ (2 * k + 1) = -1 := by rw [pow_succ, pow_mul]; simp
      rw [integral_kernel_mathieuSe_odd_closedForm, L2, hp]
      push_cast
      ring
  · rw [Complex.ofReal_zero, radialMathieuMs_one_parameter_zero hn]
    simp only [mul_zero, zero_mul, Complex.exp_zero, one_mul, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    have e : ∀ t : ℝ, mathieuSe n t 0 = Complex.sin (((n : ℤ) : ℂ) * t) := fun t => by
      rw [mathieuSe_q_zero hn]; push_cast; rfl
    simp only [e]
    rw [integral_sin_intCast_mul_eq_zero (by exact_mod_cast hn), mul_zero]
  · exact integral_exp_mathieuSe_of_pos hn hpos z α

end DLMF.Mathieu
