/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Scorer
public import DLMF.Struve.AsymptoticTools
public import DLMF.Struve.TurningTools
public import DLMF.Struve.LargeOrderTools
public import ToMathlib.Analysis.Integral.Laplace
public import DLMF.Struve.Representations

/-!
# Watson expansions of Struve functions

Laplace representations and Watson lemma give fixed-order asymptotic expansions of the Struve
functions.

Source references and common attribution are retained in
`DLMF.Struve.Asymptotics`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Struve

open DLMF.Bessel DLMF.Airy

/-- The `k`th large-argument Struve term `Γ(k+1/2) (z/2)^(ν-2k-1)/(π Γ(ν+1/2-k))`. -/
def struveAsymptoticTerm (ν z : ℂ) (k : ℕ) : ℂ :=
  Gamma (k+1/2)/Gamma (ν+1/2-k)*(z/2)^(ν-2*k-1)/π

section WatsonExpansions

open DLMF.Confluent
open scoped Interval

/-- `cos y · (1 + r²) ≤ ‖1 + (r e^{iy})²‖`. -/
theorem cos_mul_le_norm_one_add_sq (r y : ℝ) :
    Real.cos y * (1 + r ^ 2) ≤ ‖1 + ((r : ℂ) * exp (y * I)) ^ 2‖ := by
  set w := 1 + ((r : ℂ) * exp (y * I)) ^ 2 with hw
  have hexp : ((r : ℂ) * exp (y * I)) ^ 2 = ((r ^ 2 : ℝ) : ℂ) * exp (((2 * y : ℝ) : ℂ) * I) := by
    rw [mul_pow, ← exp_nat_mul]; push_cast; ring_nf
  have hre : w.re = 1 + r ^ 2 * Real.cos (2 * y) := by
    rw [hw, add_re, hexp, re_ofReal_mul, exp_ofReal_mul_I_re]; simp
  have him : w.im = r ^ 2 * Real.sin (2 * y) := by
    rw [hw, add_im, hexp, im_ofReal_mul, exp_ofReal_mul_I_im]; simp
  have hsq : ‖w‖ ^ 2 = (Real.cos y * (1 + r ^ 2)) ^ 2 + (Real.sin y * (1 - r ^ 2)) ^ 2 := by
    rw [Complex.sq_norm, normSq_apply, hre, him, Real.cos_two_mul, Real.sin_two_mul]
    linear_combination (4 * (r ^ 2) ^ 2 * Real.cos y ^ 2 - (1 - r ^ 2) ^ 2) *
      Real.sin_sq_add_cos_sq y
  calc Real.cos y * (1 + r ^ 2) ≤ |Real.cos y * (1 + r ^ 2)| := le_abs_self _
    _ = Real.sqrt ((Real.cos y * (1 + r ^ 2)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (‖w‖ ^ 2) := Real.sqrt_le_sqrt (by rw [hsq]; nlinarith [sq_nonneg (Real.sin y * (1 - r ^ 2))])
    _ = ‖w‖ := Real.sqrt_sq (norm_nonneg _)

/-- `1 + (r e^{iy})²` lies in the slit plane for `|y| < π/2`. -/
theorem one_add_sq_mem_slitPlane {r y : ℝ} (hy : |y| < π / 2) :
    1 + ((r : ℂ) * exp (y * I)) ^ 2 ∈ slitPlane := by
  have hexp : ((r : ℂ) * exp (y * I)) ^ 2 = ((r ^ 2 : ℝ) : ℂ) * exp (((2 * y : ℝ) : ℂ) * I) := by
    rw [mul_pow, ← exp_nat_mul]; push_cast; ring_nf
  rw [mem_slitPlane_iff, add_re, add_im, hexp, re_ofReal_mul, im_ofReal_mul,
    exp_ofReal_mul_I_re, exp_ofReal_mul_I_im]
  simp only [one_re, one_im, zero_add]
  by_cases hs : Real.sin (2 * y) = 0
  · left
    have h0 : 2 * y = 0 := by
      rw [Real.sin_eq_zero_iff_of_lt_of_lt] at hs
      · exact hs
      · linarith [neg_abs_le y]
      · linarith [le_abs_self y]
    rw [h0, Real.cos_zero]; positivity
  · rcases eq_or_ne r 0 with h | h
    · left; simp [h]
    · right; exact mul_ne_zero (by positivity) hs

/-- A point between `0` and `α` has modulus at most `|α|`. -/
theorem abs_le_abs_of_mem_uIcc_zero_left {α y : ℝ} (hy : y ∈ [[0, α]]) : |y| ≤ |α| := by
  rcases le_total 0 α with h | h
  · rw [uIcc_of_le h] at hy; rw [abs_of_nonneg hy.1, abs_of_nonneg h]; exact hy.2
  · rw [uIcc_of_ge h] at hy; rw [abs_of_nonpos hy.2, abs_of_nonpos h]; linarith [hy.1]

/-- A polynomial bound for `(1 + (r e^{iy})²)^a`, uniform in `|y| ≤ |α| < π/2`. -/
theorem norm_one_add_sq_mul_exp_cpow_le {a : ℂ} {α : ℝ} (hα : |α| < π / 2) {N : ℕ} (hN : |a.re| ≤ N)
    {r y : ℝ} (hr : 0 ≤ r) (hy : |y| ≤ |α|) :
    ‖(1 + ((r : ℂ) * exp (y * I)) ^ 2) ^ a‖ ≤
      Real.cos α ^ (-(N : ℝ)) * (1 + r) ^ (2 * N) * Real.exp (π * |a.im|) := by
  have hcα : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [neg_abs_le α], by linarith [le_abs_self α]⟩
  have hcα1 : Real.cos α ≤ 1 := Real.cos_le_one α
  have hcy : Real.cos α ≤ Real.cos y := by
    rw [← Real.cos_abs α, ← Real.cos_abs y]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hy
  set m := ‖1 + ((r : ℂ) * exp (y * I)) ^ 2‖ with hm
  have hm1 : m ≤ (1 + r) ^ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_pow, norm_mul_exp_I_eq r hr]; nlinarith
  have hm0 : Real.cos α ≤ m := by
    refine le_trans ?_ (cos_mul_le_norm_one_add_sq r y)
    nlinarith [sq_nonneg r]
  refine (norm_cpow_le_exp _ _).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  have hK : 1 ≤ Real.cos α ^ (-(N : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hcα hcα1 (by simp)
  have hP : 1 ≤ (1 + r) ^ (2 * N) := one_le_pow₀ (by linarith)
  rcases le_total 0 a.re with h | h
  · calc m ^ a.re ≤ ((1 + r) ^ 2) ^ a.re := Real.rpow_le_rpow (norm_nonneg _) hm1 h
      _ ≤ ((1 + r) ^ 2) ^ (N : ℝ) := Real.rpow_le_rpow_of_exponent_le (by nlinarith)
          (by linarith [le_abs_self a.re])
      _ = (1 + r) ^ (2 * N) := by rw [Real.rpow_natCast, ← pow_mul]
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hK
  · calc m ^ a.re ≤ Real.cos α ^ a.re := Real.rpow_le_rpow_of_nonpos hcα hm0 h
      _ ≤ Real.cos α ^ (-(N : ℝ)) := Real.rpow_le_rpow_of_exponent_ge hcα hcα1
          (by linarith [neg_abs_le a.re])
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hP

/-- The integrand `e^{-zt} (1+t²)^a` of the Laplace representation of `𝐊_ν`. -/
def struveKKernel (a z t : ℂ) : ℂ := exp (-z * t) * (1 + t ^ 2) ^ a

/-- Pointwise bound for the kernel on the ray `r e^{iy}`. -/
theorem norm_struveKKernel_le {a : ℂ} {α : ℝ} (hα : |α| < π / 2) {N : ℕ} (hN : |a.re| ≤ N)
    (z : ℂ) {r y : ℝ} (hr : 0 ≤ r) (hy : |y| ≤ |α|) :
    ‖struveKKernel a z (r * exp (y * I))‖ ≤ Real.exp (-(z * (r * exp (y * I))).re) *
      (Real.cos α ^ (-(N : ℝ)) * (1 + r) ^ (2 * N) * Real.exp (π * |a.im|)) := by
  rw [struveKKernel, norm_mul, Complex.norm_exp, neg_mul, neg_re]
  exact mul_le_mul_of_nonneg_left (norm_one_add_sq_mul_exp_cpow_le hα hN hr hy) (Real.exp_pos _).le

/-- The kernel is holomorphic on the rays `r e^{iy}`, `|y| < π/2`. -/
theorem differentiableAt_struveKKernel (a z : ℂ) {r y : ℝ} (hy : |y| < π / 2) :
    DifferentiableAt ℂ (struveKKernel a z) (r * exp (y * I)) := by
  unfold struveKKernel
  exact (by fun_prop : DifferentiableAt ℂ (fun t : ℂ => exp (-z * t)) _).mul
    ((by fun_prop : DifferentiableAt ℂ (fun t : ℂ => 1 + t ^ 2) _).cpow (differentiableAt_const _)
      (one_add_sq_mem_slitPlane hy))

/-- Rotation of the ray in the Laplace integral of `𝐊_ν`, on the common half-plane. -/
theorem integral_struveKKernel_rotate {a z : ℂ} {α : ℝ} (hα : |α| < π / 2) (hz0 : 0 < z.re)
    (hzα : 0 < (z * exp (α * I)).re) :
    ∫ r in Ioi (0 : ℝ), struveKKernel a z r =
      exp (α * I) * ∫ r in Ioi (0 : ℝ), struveKKernel a z (r * exp (α * I)) := by
  set κ0 := min z.re (z * exp (α * I)).re with hκ0
  have hκ0pos : 0 < κ0 := lt_min hz0 hzα
  obtain ⟨N, hN⟩ : ∃ N : ℕ, |a.re| ≤ N := ⟨⌈|a.re|⌉₊, Nat.le_ceil _⟩
  set B := Real.cos α ^ (-(N : ℝ)) * Real.exp (π * |a.im|) with hB
  have hcα : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [neg_abs_le α], by linarith [le_abs_self α]⟩
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨M, hM⟩ := exists_rpow_mul_exp_neg_le ((2 * N : ℕ) : ℝ) (b := κ0 / 2) (by positivity)
  have hM0 : 0 ≤ M := (by positivity : (0 : ℝ) ≤ 1 ^ ((2 * N : ℕ) : ℝ) *
    Real.exp (-(κ0 / 2) * 1)).trans (hM 1 le_rfl)
  set C := max (2 ^ (2 * N) * B) (2 ^ (2 * N) * B * M) with hC
  have hbound : ∀ r : ℝ, 0 < r → ∀ y ∈ [[0, α]], ‖struveKKernel a z (r * exp (y * I))‖ ≤
      Real.exp (-κ0 * r) * (1 + r) ^ (2 * N) * B := by
    intro r hr y hy
    have hb := norm_struveKKernel_le hα hN z hr.le (abs_le_abs_of_mem_uIcc_zero_left hy)
    refine hb.trans ?_
    have hre : κ0 * r ≤ (z * ((r : ℂ) * exp (y * I))).re := by
      rw [mul_left_comm, re_ofReal_mul]
      have := re_mul_exp_mul_I_ge hα hz0 hzα hy
      nlinarith
    have he : Real.exp (-(z * ((r : ℂ) * exp (y * I))).re) ≤ Real.exp (-κ0 * r) :=
      Real.exp_le_exp.mpr (by linarith)
    calc Real.exp (-(z * ((r : ℂ) * exp (y * I))).re) *
          (Real.cos α ^ (-(N : ℝ)) * (1 + r) ^ (2 * N) * Real.exp (π * |a.im|))
        ≤ Real.exp (-κ0 * r) *
          (Real.cos α ^ (-(N : ℝ)) * (1 + r) ^ (2 * N) * Real.exp (π * |a.im|)) := by gcongr
      _ = _ := by rw [hB]; ring
  refine Complex.integral_Ioi_eq_exp_mul_integral_Ioi_rotate (σ := 1) (κ := κ0 / 2) (C := C)
    one_pos (by positivity) ?_ ?_ ?_
  · intro r hr y hy
    exact differentiableAt_struveKKernel a z (abs_lt_of_mem_uIcc hα hy)
  · intro r hr hr1 y hy
    refine (hbound r hr y hy).trans ?_
    have h1 : Real.exp (-κ0 * r) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have h2 : (1 + r) ^ (2 * N) ≤ 2 ^ (2 * N) := pow_le_pow_left₀ (by linarith) (by linarith) _
    rw [sub_self, Real.rpow_zero, mul_one]
    calc Real.exp (-κ0 * r) * (1 + r) ^ (2 * N) * B ≤ 1 * 2 ^ (2 * N) * B := by gcongr
      _ = 2 ^ (2 * N) * B := by ring
      _ ≤ C := le_max_left _ _
  · intro r hr y hy
    have hr0 : 0 < r := by linarith
    refine (hbound r hr0 y hy).trans ?_
    have h2 : (1 + r) ^ (2 * N) ≤ 2 ^ (2 * N) * r ^ (2 * N) := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) _
    have hsplit : Real.exp (-κ0 * r) = Real.exp (-(κ0 / 2) * r) * Real.exp (-(κ0 / 2) * r) := by
      rw [← Real.exp_add]; ring_nf
    have hMr := hM r hr
    rw [Real.rpow_natCast] at hMr
    calc Real.exp (-κ0 * r) * (1 + r) ^ (2 * N) * B
        ≤ Real.exp (-κ0 * r) * (2 ^ (2 * N) * r ^ (2 * N)) * B := by gcongr
      _ = 2 ^ (2 * N) * B * (r ^ (2 * N) * Real.exp (-(κ0 / 2) * r)) *
            Real.exp (-(κ0 / 2) * r) := by rw [hsplit]; ring
      _ ≤ 2 ^ (2 * N) * B * M * Real.exp (-(κ0 / 2) * r) := by gcongr
      _ ≤ C * Real.exp (-(κ0 / 2) * r) := by gcongr; exact le_max_right _ _

/-- The rotated Laplace integral `∫₀^∞ e^{-z r e^{iα}} (1 + (r e^{iα})²)^a dr`. -/
def struveKRotIntegral (a : ℂ) (α : ℝ) (z : ℂ) : ℂ :=
  ∫ r in Ioi (0 : ℝ), struveKKernel a z (r * exp (α * I))

/-- The rotated integral is holomorphic on the half-plane `re (z e^{iα}) > 0`. -/
theorem differentiableOn_struveKRotIntegral (a : ℂ) {α : ℝ} (hα : |α| < π / 2) :
    DifferentiableOn ℂ (struveKRotIntegral a α) {z : ℂ | 0 < (z * exp (α * I)).re} := by
  intro z₀ hz₀
  change 0 < (z₀ * exp (α * I)).re at hz₀
  set ω := exp (α * I) with hω
  set δ : ℝ := (z₀ * ω).re / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hre : ∀ z ∈ Metric.ball z₀ δ, ∀ r : ℝ, 0 ≤ r → δ * r ≤ (z * ((r : ℂ) * ω)).re := by
    intro z hz r hr
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 : |((z - z₀) * ω).re| ≤ ‖z - z₀‖ := by
      refine (abs_re_le_norm _).trans ?_
      rw [norm_mul, hω, norm_exp_ofReal_mul_I, mul_one]
    have h2 : (z * ((r : ℂ) * ω)).re = r * (z * ω).re := by
      rw [mul_left_comm, re_ofReal_mul]
    have h3 : (z * ω).re = (z₀ * ω).re + ((z - z₀) * ω).re := by
      rw [← add_re]; ring_nf
    rw [h2, h3]
    have := (abs_le.mp h1).1
    nlinarith
  obtain ⟨N, hN⟩ : ∃ N : ℕ, |a.re| ≤ N := ⟨⌈|a.re|⌉₊, Nat.le_ceil _⟩
  set B := Real.cos α ^ (-(N : ℝ)) * Real.exp (π * |a.im|) with hB
  have hcα : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [neg_abs_le α], by linarith [le_abs_self α]⟩
  set F : ℂ → ℝ → ℂ := fun z r => struveKKernel a z (r * ω) with hF
  have hcontF : ∀ z : ℂ, ContinuousOn (F z) (Ioi 0) := fun z r _ =>
    (ContinuousAt.comp (g := struveKKernel a z) (f := fun r : ℝ => (r : ℂ) * ω) (x := r)
      (differentiableAt_struveKKernel a z hα).continuousAt
      (by fun_prop : Continuous fun r : ℝ => (r : ℂ) * ω).continuousAt).continuousWithinAt
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (F z) (volume.restrict (Ioi 0)) := fun z =>
    (hcontF z).aestronglyMeasurable measurableSet_Ioi
  have hbnd : ∀ z ∈ Metric.ball z₀ δ, ∀ r : ℝ, 0 < r →
      ‖F z r‖ ≤ Real.exp (-δ * r) * r ^ (0 : ℝ) * (1 + r) ^ (2 * N) * B := by
    intro z hz r hr
    have hb := norm_struveKKernel_le hα hN z hr.le le_rfl
    refine hb.trans ?_
    have := hre z hz r hr.le
    have he : Real.exp (-(z * ((r : ℂ) * ω)).re) ≤ Real.exp (-δ * r) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [Real.rpow_zero, mul_one, hB]
    calc Real.exp (-(z * ((r : ℂ) * ω)).re) *
          (Real.cos α ^ (-(N : ℝ)) * (1 + r) ^ (2 * N) * Real.exp (π * |a.im|))
        ≤ Real.exp (-δ * r) *
          (Real.cos α ^ (-(N : ℝ)) * (1 + r) ^ (2 * N) * Real.exp (π * |a.im|)) := by gcongr
      _ = _ := by ring
  set G : ℝ → ℝ := fun r => Real.exp (-δ * r) * r ^ (1 : ℝ) * (1 + r) ^ (2 * N) * B with hGdef
  have hG : IntegrableOn G (Ioi 0) :=
    (integrableOn_exp_mul_rpow_mul_one_add_pow (by norm_num) hδ0 (2 * N)).mul_const B
  have hint0 : Integrable (F z₀) (volume.restrict (Ioi 0)) := by
    refine Integrable.mono' ((integrableOn_exp_mul_rpow_mul_one_add_pow (s := 0)
      (by norm_num) hδ0 (2 * N)).mul_const B) (hmeas z₀) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
    exact hbnd z₀ (Metric.mem_ball_self hδ0) r hr
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0)) (F := F) (F' := fun z r => -((r : ℂ) * ω) * F z r)
    (bound := G) (Metric.ball_mem_nhds _ hδ0) (Eventually.of_forall hmeas) hint0
    ((((by fun_prop : Continuous fun r : ℝ => -((r : ℂ) * ω)).continuousOn).mul
      (hcontF z₀)).aestronglyMeasurable measurableSet_Ioi) ?_ hG ?_
  · exact hd.2.differentiableAt.differentiableWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr z hz => ?_)
    have hr : (0 : ℝ) < r := hr
    rw [norm_mul, norm_neg, norm_mul_exp_I_eq r hr.le]
    calc r * ‖F z r‖ ≤ r * (Real.exp (-δ * r) * r ^ (0 : ℝ) * (1 + r) ^ (2 * N) * B) :=
          mul_le_mul_of_nonneg_left (hbnd z hz r hr) hr.le
      _ = G r := by rw [hGdef]; simp only [Real.rpow_zero, Real.rpow_one]; ring
  · refine Eventually.of_forall fun r z _ => ?_
    have h := ((hasDerivAt_id z).neg.mul_const ((r : ℂ) * ω)).cexp.mul_const
      ((1 + ((r : ℂ) * ω) ^ 2) ^ a)
    simp only [hF, struveKKernel]
    convert h using 1
    · funext w; simp
    · simp; ring

/-- The rotated representation `𝐊_ν(z) = 2(z/2)^ν/(√π Γ(ν+1/2)) · e^{iα} ∫₀^∞ …`. -/
def struveKRotated (ν : ℂ) (α : ℝ) (z : ℂ) : ℂ :=
  2 * (z / 2) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2)) *
    (exp (α * I) * struveKRotIntegral (ν - 1 / 2) α z)

/-- **Rotated Laplace representation of `𝐊_ν`**: for `|α| < π/2` and `re (z e^{iα}) > 0`. -/
theorem struveK_eq_struveKRotated (ν : ℂ) {α : ℝ} (hα : |α| < π / 2) {z : ℂ}
    (hz : 0 < (z * exp (α * I)).re) : struveK ν z = struveKRotated ν α z := by
  set ω := exp (α * I) with hω
  set H : Set ℂ := {z : ℂ | 0 < (z * ω).re} with hH
  have hHo : IsOpen H := isOpen_lt continuous_const (by fun_prop)
  have hHc : Convex ℝ H := by
    intro z₁ hz₁ z₂ hz₂ s t hs ht hst
    change 0 < ((s • z₁ + t • z₂) * ω).re
    change 0 < (z₁ * ω).re at hz₁
    change 0 < (z₂ * ω).re at hz₂
    rw [add_mul, add_re, smul_mul_assoc, smul_mul_assoc, Complex.smul_re, Complex.smul_re,
      smul_eq_mul, smul_eq_mul]
    rcases eq_or_lt_of_le hs with h | h
    · subst h; simp at hst; subst hst; simpa using hz₂
    · nlinarith [mul_pos h hz₁, mul_nonneg ht hz₂.le]
  have hcosα : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [neg_abs_le α], by linarith [le_abs_self α]⟩
  have hHslit : H ⊆ slitPlane := by
    intro w hw
    change 0 < (w * ω).re at hw
    by_contra h
    rw [mem_slitPlane_iff, not_or] at h
    push Not at h
    have hw' : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [h.2])
    rw [hw', re_ofReal_mul, hω, exp_ofReal_mul_I_re] at hw
    nlinarith [h.1]
  have hU : AnalyticOnNhd ℂ (struveK ν) H :=
    (DLMF.Bessel.analyticOnNhd_struveK ν).mono hHslit
  have hpre : DifferentiableOn ℂ
      (fun z : ℂ => 2 * (z / 2) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2))) H := by
    intro w hw
    have h2 := div_two_mem_slitPlane (hHslit hw)
    exact ((((differentiableAt_id.div_const 2).cpow (differentiableAt_const ν) h2).const_mul
      2).div_const _).differentiableWithinAt
  have hV : AnalyticOnNhd ℂ (struveKRotated ν α) H :=
    (hpre.mul ((differentiableOn_struveKRotIntegral (ν - 1 / 2) hα).const_mul ω)).analyticOnNhd
      hHo
  set zs : ℂ := exp ((-(α / 2) : ℝ) * I) with hzs
  have hzs0 : 0 < zs.re := by
    rw [hzs, exp_ofReal_mul_I_re, Real.cos_neg]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le α, Real.pi_pos],
      by linarith [le_abs_self α, Real.pi_pos]⟩
  have hzsH : 0 < (zs * ω).re := by
    rw [hzs, hω, ← exp_add, show ((-(α / 2) : ℝ) : ℂ) * I + α * I = ((α / 2 : ℝ) : ℂ) * I by
      push_cast; ring, exp_ofReal_mul_I_re]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le α, Real.pi_pos],
      by linarith [le_abs_self α, Real.pi_pos]⟩
  have hev : struveK ν =ᶠ[𝓝 zs] struveKRotated ν α := by
    have hopen : IsOpen {w : ℂ | 0 < w.re ∧ 0 < (w * ω).re} :=
      (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_const
        (by fun_prop : Continuous fun w : ℂ => (w * ω).re))
    filter_upwards [hopen.mem_nhds ⟨hzs0, hzsH⟩] with w hw
    rw [DLMF.Bessel.struveK_eq_integral ν hw.1, struveKRotated, struveKRotIntegral,
      ← integral_struveKKernel_rotate hα hw.1 hw.2]
    rfl
  exact hU.eqOn_of_preconnected_of_eventuallyEq hV hHc.isPreconnected hzsH hev hz

/-- `(a)(a-1)⋯(a-k+1)/Γ(a+1) = 1/Γ(a+1-k)`. -/
theorem neg_one_pow_mul_poch_mul_recip_Gamma (a : ℂ) (k : ℕ) :
    (Gamma (a + 1))⁻¹ * ((-1) ^ k * poch (-a) k) = (Gamma (a + 1 - k))⁻¹ := by
  induction k with
  | zero => simp [poch]
  | succ k ih =>
    rw [poch_succ, pow_succ, show (Gamma (a + 1))⁻¹ * ((-1) ^ k * (-1) * (poch (-a) k * (-a + k)))
      = (Gamma (a + 1))⁻¹ * ((-1) ^ k * poch (-a) k) * (a - k) by ring, ih,
      DLMF.Hypergeometric.recip_Gamma_eq_mul_recip_Gamma_add_one (a + 1 - ((k + 1 : ℕ) : ℂ))]
    push_cast
    rw [show a + 1 - (k + 1) + 1 = a + 1 - k by ring]
    ring

/-- `Γ(k+1/2) k! 4^k = (2k)! √π`. -/
theorem Gamma_nat_add_half_mul (k : ℕ) :
    Gamma (k + 1 / 2) * (k ! : ℂ) * 4 ^ k = ((2 * k) ! : ℂ) * Real.sqrt π := by
  have h := Complex.Gamma_mul_Gamma_add_half ((k : ℂ) + 1 / 2)
  rw [show (k : ℂ) + 1 / 2 + 1 / 2 = (k : ℂ) + 1 by ring, Complex.Gamma_nat_eq_factorial,
    show 2 * ((k : ℂ) + 1 / 2) = ((2 * k : ℕ) : ℂ) + 1 by push_cast; ring,
    Complex.Gamma_nat_eq_factorial,
    show (1 : ℂ) - (((2 * k : ℕ) : ℂ) + 1) = -((2 * k : ℕ) : ℂ) by ring, cpow_neg,
    cpow_natCast] at h
  have h4 : (2 : ℂ) ^ (2 * k) = 4 ^ k := by rw [pow_mul]; norm_num
  rw [h4] at h
  have h40 : (4 : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [h]; field_simp

/-- The coefficient identity behind DLMF 11.6.1. -/
theorem struveK_coeff_eq (ν : ℂ) {z : ℂ} (hz : z ≠ 0) (k : ℕ) :
    2 * (z / 2) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2)) *
      ((z ^ (2 * k + 1))⁻¹ * (Gamma (((2 * k : ℕ) : ℂ) + 1) * Ring.choose (ν - 1 / 2) k)) =
      struveAsymptoticTerm ν z k := by
  have hz2 : z / 2 ≠ 0 := div_ne_zero hz two_ne_zero
  have hch : Ring.choose (ν - 1 / 2) k = (-1) ^ k * poch (-(ν - 1 / 2)) k / k ! := by
    rw [← ring_choose_neg_eq_poch, neg_neg]
  have hG := neg_one_pow_mul_poch_mul_recip_Gamma (ν - 1 / 2) k
  rw [show ν - 1 / 2 + 1 = ν + 1 / 2 by ring] at hG
  have hH := Gamma_nat_add_half_mul k
  have hpow : (z / 2) ^ (ν - 2 * k - 1) = (z / 2) ^ ν * 2 ^ (2 * k + 1) * (z ^ (2 * k + 1))⁻¹ := by
    rw [show ν - 2 * k - 1 = ν - ((2 * k + 1 : ℕ) : ℂ) by push_cast; ring, cpow_sub _ _ hz2,
      cpow_natCast, div_pow]
    field_simp
  rw [struveAsymptoticTerm, hpow, Complex.Gamma_nat_eq_factorial, hch, div_eq_mul_inv _ (Gamma (ν + 1 / 2 - k)), ← hG]
  have hs : (Real.sqrt π : ℂ) ≠ 0 := by
    rw [ofReal_ne_zero]; exact (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hpi : (π : ℂ) = Real.sqrt π * Real.sqrt π := by
    rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have h' : (((2 * k) ! : ℕ) : ℂ) = Gamma (k + 1 / 2) * k ! * 4 ^ k / Real.sqrt π := by
    rw [hH]; field_simp
  rw [hpi, h']
  rw [show (2 : ℂ) ^ (2 * k + 1) = 4 ^ k * 2 by rw [pow_succ, pow_mul]; norm_num]
  field_simp

/-- A sum over even indices below `N`, reindexed. -/
theorem sum_range_ite_even (g : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range N, (if Even n then g (n / 2) else 0) =
      ∑ k ∈ Finset.range ((N + 1) / 2), g k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd N with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · simp only [show Even (m + m) from ⟨m, rfl⟩, ↓reduceIte]
      rw [show (m + m + 1 + 1) / 2 = m + 1 by omega,
        show (m + m + 1) / 2 = m by omega, show (m + m) / 2 = m by omega, Finset.sum_range_succ]
    · simp only [show ¬Even (2 * m + 1) from Nat.not_even_iff_odd.mpr ⟨m, rfl⟩, ↓reduceIte]
      rw [add_zero,
        show (2 * m + 1 + 1 + 1) / 2 = m + 1 by omega, show (2 * m + 1 + 1) / 2 = m + 1 by omega]

/-- Coefficients of `(1 + (t e^{iα})²)^a = ∑ Aₙ tⁿ`. -/
def struveKCoeffA (a : ℂ) (α : ℝ) (n : ℕ) : ℂ :=
  if Even n then exp (α * I) ^ n * Ring.choose a (n / 2) else 0

/-- Watson's lemma for the rotated Laplace integral of `𝐊_ν`. -/
theorem hasAsymptoticExpansion_struveKRotIntegral (a : ℂ) {δ α : ℝ} (hδ : 0 < δ)
    (hα : |α| < π / 2) :
    HasAsymptoticExpansion (rotSectorAtTop δ α)
      (fun (n : ℕ) (z : ℂ) => (z * exp (α * I)) ^ (-((n : ℂ) + 1)))
      (fun n => Gamma ((n : ℂ) + 1) • struveKCoeffA a α n) (struveKRotIntegral a α) := by
  set ω := exp (α * I) with hω
  set F : ℝ → ℂ := fun r => (1 + ((r : ℂ) * ω) ^ 2) ^ a with hF
  obtain ⟨N0, hN0⟩ : ∃ N : ℕ, |a.re| ≤ N := ⟨⌈|a.re|⌉₊, Nat.le_ceil _⟩
  set B := Real.cos α ^ (-(N0 : ℝ)) * Real.exp (π * |a.im|) with hB
  have hFcont : Continuous F := continuous_iff_continuousAt.2 fun r =>
    (by fun_prop : Continuous fun r : ℝ => 1 + ((r : ℂ) * ω) ^ 2).continuousAt.cpow
      continuousAt_const (one_add_sq_mem_slitPlane hα)
  have hint : IntegrableOn (fun r => Real.exp (-1 * r) • F r) (Ioi 0) := by
    refine ((integrableOn_exp_mul_rpow_mul_one_add_pow (s := 0) (by norm_num) one_pos
      (2 * N0)).mul_const B).mono'
      (((by fun_prop : Continuous fun r : ℝ => Real.exp (-1 * r)).smul hFcont
        ).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
    have hr : (0 : ℝ) < r := hr
    have h := norm_one_add_sq_mul_exp_cpow_le hα hN0 hr.le le_rfl (a := a)
    rw [norm_smul, Real.norm_eq_abs, Real.abs_exp, Real.rpow_zero, mul_one]
    calc Real.exp (-1 * r) * ‖F r‖ ≤ Real.exp (-1 * r) *
          (Real.cos α ^ (-(N0 : ℝ)) * (1 + r) ^ (2 * N0) * Real.exp (π * |a.im|)) :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = _ := by rw [hB]; ring
  have ht2 : Tendsto (fun t : ℝ => t ^ 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_pow 2).tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact pow_pos (show (0 : ℝ) < t from ht) 2
  have hFexp : ∀ N : ℕ, (fun t => F t - ∑ n ∈ Finset.range N,
      ((t : ℂ) ^ ((n : ℂ) + 1 - 1)) • struveKCoeffA a α n) =O[𝓝[>] 0]
      fun t => t ^ ((N : ℝ) + (1 : ℂ).re - 1) := by
    intro N
    set M := (N + 1) / 2 with hM
    have hb := (one_add_mul_cpow_sub_sum_isBigO (ω ^ 2) a M).comp_tendsto ht2
    have hpow : (fun t : ℝ => (t ^ 2) ^ M) =O[𝓝[>] 0]
        fun t => t ^ ((N : ℝ) + (1 : ℂ).re - 1) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
      rw [one_re, add_sub_cancel_right, Real.rpow_natCast, one_mul, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (pow_nonneg ht.1.le _),
        ← pow_mul]
      exact pow_le_pow_of_le_one ht.1.le ht.2.le (by omega)
    refine (hb.trans hpow).congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
    simp only [Function.comp_apply, hF]
    congr 1
    · congr 1; push_cast; ring
    · rw [← sum_range_ite_even]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [add_sub_cancel_right, cpow_natCast, smul_eq_mul, struveKCoeffA]
      split_ifs with h
      · obtain ⟨m, rfl⟩ := h
        rw [show (m + m) / 2 = m by omega]
        push_cast
        ring
      · simp
  have hW := (hasAsymptoticExpansion_integral_cexp_smul_sector (μ := 1) (by simp) hδ hint
    hFexp).comp_tendsto (tendsto_rotSectorAtTop δ α)
  refine hW.congr' (Eventually.of_forall fun z => ?_)
  simp only [Function.comp_apply, struveKRotIntegral, struveKKernel, hF, smul_eq_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  rw [hω]; ring_nf

/-- `‖(z/2)^w‖ = 2^{-re w} ‖z^w‖`. -/
theorem norm_div_two_cpow (z w : ℂ) : ‖(z / 2) ^ w‖ = 2 ^ (-w.re) * ‖z ^ w‖ := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [zero_div]
    rcases eq_or_ne w 0 with rfl | hw
    · simp
    · rw [zero_cpow hw, norm_zero, mul_zero]
  · have hz2 : z / 2 ≠ 0 := div_ne_zero hz two_ne_zero
    have harg : arg (z / 2) = arg z := by
      rw [div_eq_mul_inv, show (2 : ℂ)⁻¹ = ((2⁻¹ : ℝ) : ℂ) by push_cast; rfl,
        arg_mul_real (by norm_num)]
    rw [norm_cpow_of_ne_zero hz2, norm_cpow_of_ne_zero hz, harg, norm_div, Complex.norm_ofNat,
      Real.div_rpow (norm_nonneg _) (by norm_num), Real.rpow_neg (by norm_num)]
    ring

/-- `(z/2)^w = O(z^w)` along any filter. -/
theorem isBigO_div_two_cpow (l : Filter ℂ) (w : ℂ) :
    (fun z : ℂ => (z / 2) ^ w) =O[l] fun z => z ^ w :=
  IsBigO.of_bound (2 ^ (-w.re)) (Eventually.of_forall fun z => (norm_div_two_cpow z w).le)

/-- DLMF 11.6.1 in a rotated sector `δ |z| ≤ re (z e^{iα})`. -/
theorem struveK_asymptotic_rotSector (ν : ℂ) {δ α : ℝ} (hδ : 0 < δ) (hα : |α| < π / 2)
    (N : ℕ) :
    (fun z : ℂ => struveK ν z - ∑ k ∈ Finset.range N, struveAsymptoticTerm ν z k)
      =O[rotSectorAtTop δ α] fun z : ℂ => z ^ (ν - 2 * N - 1) := by
  set ω := exp (α * I) with hω
  have hω0 : ω ≠ 0 := exp_ne_zero _
  set P : ℂ → ℂ := fun z => 2 * (z / 2) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2)) with hP
  have hE := hasAsymptoticExpansion_struveKRotIntegral (ν - 1 / 2) hδ hα (2 * N)
  have hev := eventually_rotSectorAtTop hδ hα
  have h1 := (isBigO_refl (fun z => P z * ω) (rotSectorAtTop δ α)).mul hE
  -- the scale
  have hscale : ∀ z : ℂ, z ≠ 0 → ∀ m : ℕ,
      (z * ω) ^ (-(((m : ℕ) : ℂ) + 1)) = (z ^ (m + 1))⁻¹ * (ω ^ (m + 1))⁻¹ := by
    intro z hz m
    rw [cpow_neg, show ((m : ℕ) : ℂ) + 1 = ((m + 1 : ℕ) : ℂ) by push_cast; ring, cpow_natCast,
      mul_pow, mul_inv]
  have h2 : (fun z => P z * ω * (z * ω) ^ (-(((2 * N : ℕ) : ℂ) + 1))) =O[rotSectorAtTop δ α]
      fun z : ℂ => z ^ (ν - 2 * N - 1) := by
    have hc : (fun z => P z * ω * (z * ω) ^ (-(((2 * N : ℕ) : ℂ) + 1))) =ᶠ[rotSectorAtTop δ α]
        fun z => (2 / (Real.sqrt π * Gamma (ν + 1 / 2)) / ω ^ (2 * N) / 2 ^ (2 * N + 1)) *
          (z / 2) ^ (ν - 2 * N - 1) := by
      filter_upwards [hev] with z hz
      have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; linarith [hz.1]
      have hz2 : z / 2 ≠ 0 := div_ne_zero hz0 two_ne_zero
      rw [hscale z hz0, show ν - 2 * N - 1 = ν - ((2 * N + 1 : ℕ) : ℂ) by push_cast; ring,
        cpow_sub _ _ hz2, cpow_natCast, div_pow, hP]
      simp only
      field_simp
      ring
    exact (hc.trans_isBigO ((isBigO_div_two_cpow _ _).const_mul_left _))
  refine (h1.congr' ?_ EventuallyEq.rfl).trans h2
  filter_upwards [hev] with z hz
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; linarith [hz.1]
  rw [struveK_eq_struveKRotated ν hα hz.2.1, struveKRotated, mul_sub]
  congr 1
  · simp only [hP]; ring
  · rw [Finset.mul_sum]
    have hsum : ∀ n ∈ Finset.range (2 * N), P z * ω * ((z * ω) ^ (-((n : ℂ) + 1)) •
        Gamma ((n : ℂ) + 1) • struveKCoeffA (ν - 1 / 2) α n) =
        if Even n then struveAsymptoticTerm ν z (n / 2) else 0 := by
      intro n _
      rw [struveKCoeffA]
      split_ifs with h
      · obtain ⟨m, rfl⟩ := h
        rw [show (m + m) / 2 = m by omega, ← struveK_coeff_eq ν hz0 m, smul_eq_mul, smul_eq_mul,
          show ((m + m : ℕ) : ℂ) = ((2 * m : ℕ) : ℂ) by push_cast; ring,
          hscale z hz0, show m + m = 2 * m by ring]
        simp only [hP]
        field_simp
        ring
      · simp
    rw [Finset.sum_congr rfl hsum, sum_range_ite_even, show (2 * N + 1) / 2 = N by omega]

/-- Unfolding an eventual statement in a rotated Watson sector. -/
theorem exists_of_eventually_rotSectorAtTop {δ α : ℝ} {p : ℂ → Prop}
    (h : ∀ᶠ z in rotSectorAtTop δ α, p z) :
    ∃ R, ∀ z : ℂ, R ≤ ‖z‖ → δ * ‖z‖ ≤ (z * exp (α * I)).re → p z := by
  rw [rotSectorAtTop, eventually_comap, sectorAtTop, eventually_inf_principal, eventually_comap,
    eventually_atTop] at h
  obtain ⟨R, hR⟩ := h
  refine ⟨R, fun z hz hzs => ?_⟩
  have hn : ‖z * exp (α * I)‖ = ‖z‖ := by rw [norm_mul, norm_exp_ofReal_mul_I, mul_one]
  exact hR ‖z‖ hz (z * exp (α * I)) hn (by show δ * ‖z * exp (α * I)‖ ≤ (z * exp (α * I)).re; rw [hn]; exact hzs) z rfl

/-- The closed sector `|arg z| ≤ π - δ` is covered by two rotated Watson sectors. -/
theorem sector_le_sup_rotSectorAtTop {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    DLMF.sector (π - δ) ≤ rotSectorAtTop (Real.sin (δ / 2)) (-((π - δ) / 2)) ⊔
      rotSectorAtTop (Real.sin (δ / 2)) ((π - δ) / 2) := by
  intro U hU
  rw [mem_sup] at hU
  obtain ⟨R1, h1⟩ := exists_of_eventually_rotSectorAtTop (p := (· ∈ U)) hU.1
  obtain ⟨R2, h2⟩ := exists_of_eventually_rotSectorAtTop (p := (· ∈ U)) hU.2
  have key : ∀ (z : ℂ) (β : ℝ), |arg z + β| ≤ (π - δ) / 2 →
      Real.sin (δ / 2) * ‖z‖ ≤ (z * exp (β * I)).re := by
    intro z β hb
    rw [re_mul_exp_mul_I, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [← Real.cos_abs, show δ / 2 = π / 2 - (π - δ) / 2 by ring, Real.sin_pi_div_two_sub]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) hb
  change ∀ᶠ z in DLMF.sector (π - δ), z ∈ U
  rw [DLMF.sector, eventually_inf_principal]
  refine (tendsto_comap.eventually (eventually_ge_atTop (max R1 R2))).mono fun z hzR hzS => ?_
  obtain ⟨-, hzarg⟩ := hzS
  rcases le_total 0 (arg z) with h | h
  · refine h1 z ((le_max_left _ _).trans hzR) (key z _ ?_)
    rw [abs_le]; constructor <;> linarith [abs_le.mp hzarg]
  · refine h2 z ((le_max_right _ _).trans hzR) (key z _ ?_)
    rw [abs_le]; constructor <;> linarith [abs_le.mp hzarg]

/-! ### The modified function `𝐌_ν` -/

/-- Coefficients of `(1 - t²)^a = ∑ Bₙ tⁿ`. -/
def struveMCoeffB (a : ℂ) (n : ℕ) : ℂ :=
  if Even n then (-1) ^ (n / 2) * Ring.choose a (n / 2) else 0

/-- The weight `(1 - t²)^a` on `t ≤ 1`, extended by zero. -/
def struveMWeight (a : ℂ) (t : ℝ) : ℂ :=
  (Iic (1 : ℝ)).indicator (fun t : ℝ => (1 - (t : ℂ) ^ 2) ^ a) t

/-- Identity under the stated parameter and domain assumptions: `HasAsymptoticExpansion
(sectorAtTop δ) (fun (n : ℕ) (z : ℂ) => z ^ (-((n : ℂ) + 1))) (fun n => Gamma ((n : ℂ) + 1) •
struveMCoeffB a n) (fun z => ∫ t in Ioi (0 : ℝ), exp (-(z * t)) • struveMWeight a t)`. -/
theorem hasAsymptoticExpansion_struveMIntegral {a : ℂ} (ha : 0 < a.re) {δ : ℝ} (hδ : 0 < δ) :
    HasAsymptoticExpansion (sectorAtTop δ) (fun (n : ℕ) (z : ℂ) => z ^ (-((n : ℂ) + 1)))
      (fun n => Gamma ((n : ℂ) + 1) • struveMCoeffB a n)
      (fun z => ∫ t in Ioi (0 : ℝ), exp (-(z * t)) • struveMWeight a t) := by
  have hmeas : Measurable (struveMWeight a) :=
    ((measurable_const.sub (Complex.measurable_ofReal.pow_const 2)).pow_const a).indicator
      measurableSet_Iic
  have hbd : ∀ t : ℝ, 0 < t → ‖struveMWeight a t‖ ≤ 1 := by
    intro t _
    unfold struveMWeight
    by_cases h : t ∈ Iic (1 : ℝ)
    · rw [indicator_of_mem h]
      have h1 : (1 - (t : ℂ) ^ 2) = ((1 - t ^ 2 : ℝ) : ℂ) := by push_cast; ring
      have ht1 : t ≤ 1 := h
      have h0 : 0 ≤ 1 - t ^ 2 := by nlinarith
      rw [h1, norm_cpow_eq_rpow_re_of_nonneg h0 ha.ne']
      exact Real.rpow_le_one h0 (by nlinarith) ha.le
    · rw [indicator_of_notMem h, norm_zero]; exact zero_le_one
  have hint : IntegrableOn (fun t => Real.exp (-1 * t) • struveMWeight a t) (Ioi 0) := by
    refine (integrableOn_exp_mul_rpow_mul_one_add_pow (s := 0) (by norm_num) one_pos 0).mono'
      (((by fun_prop : Continuous fun t : ℝ => Real.exp (-1 * t)).measurable.smul
        hmeas).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [norm_smul, Real.norm_eq_abs, Real.abs_exp, Real.rpow_zero, pow_zero, mul_one, mul_one]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (hbd t ht)
  have ht2 : Tendsto (fun t : ℝ => t ^ 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_pow 2).tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact pow_pos (show (0 : ℝ) < t from ht) 2
  have hFexp : ∀ N : ℕ, (fun t => struveMWeight a t - ∑ n ∈ Finset.range N,
      ((t : ℂ) ^ ((n : ℂ) + 1 - 1)) • struveMCoeffB a n) =O[𝓝[>] 0]
      fun t => t ^ ((N : ℝ) + (1 : ℂ).re - 1) := by
    intro N
    set M := (N + 1) / 2 with hM
    have hb := (one_add_mul_cpow_sub_sum_isBigO (-1) a M).comp_tendsto ht2
    have hpow : (fun t : ℝ => (t ^ 2) ^ M) =O[𝓝[>] 0]
        fun t => t ^ ((N : ℝ) + (1 : ℂ).re - 1) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
      rw [one_re, add_sub_cancel_right, Real.rpow_natCast, one_mul, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (pow_nonneg ht.1.le _),
        ← pow_mul]
      exact pow_le_pow_of_le_one ht.1.le ht.2.le (by omega)
    refine (hb.trans hpow).congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    simp only [Function.comp_apply, struveMWeight,
      indicator_of_mem (show t ∈ Iic (1 : ℝ) from ht.2.le)]
    congr 1
    · congr 1; push_cast; ring
    · rw [← sum_range_ite_even]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [add_sub_cancel_right, cpow_natCast, smul_eq_mul, struveMCoeffB]
      split_ifs with h
      · obtain ⟨m, rfl⟩ := h
        rw [show (m + m) / 2 = m by omega]
        push_cast
        ring
      · simp
  exact hasAsymptoticExpansion_integral_cexp_smul_sector (μ := 1) (by simp) hδ hint hFexp

/-- DLMF 11.5.4 written as a Laplace integral over `(0, ∞)`. -/
theorem struveM_eq_integral_weight {ν : ℂ} (hν : -1 / 2 < ν.re) {z : ℂ} (hz : 0 < z.re) :
    struveM ν z = -(2 * (z / 2) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2))) *
      ∫ t in Ioi (0 : ℝ), exp (-(z * t)) • struveMWeight (ν - 1 / 2) t := by
  rw [struveM_eq_poisson hν (Or.inl hz), intervalIntegral.integral_of_le zero_le_one,
    ← Ioi_inter_Iic, ← setIntegral_indicator (measurableSet_Iic (a := (1 : ℝ)))]
  have h : ∫ t in Ioi (0 : ℝ), (Iic (1 : ℝ)).indicator
      (fun t : ℝ => exp (-z * t) * (1 - (t : ℂ) ^ 2) ^ (ν - 1 / 2)) t =
      ∫ t in Ioi (0 : ℝ), exp (-(z * t)) • struveMWeight (ν - 1 / 2) t := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [struveMWeight]
    by_cases h : t ∈ Iic (1 : ℝ)
    · rw [indicator_of_mem h, indicator_of_mem h, smul_eq_mul, neg_mul]
    · rw [indicator_of_notMem h, indicator_of_notMem h, smul_zero]
  rw [h]; ring

/-- Points of a Watson sector eventually have `‖z‖ ≥ 1` and `re z > 0`. -/
theorem eventually_re_pos_sectorAtTop {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ z in sectorAtTop δ, 1 ≤ ‖z‖ ∧ 0 < z.re :=
  eventually_sectorAtTop (R := 1) fun z hz hzs => ⟨hz, by nlinarith⟩

/-- DLMF 11.6.2 for `re ν > 1/2`, in the Watson sector `δ |z| ≤ re z`. -/
theorem struveM_asymptotic_sectorAtTop_of_re {ν : ℂ} (hν : 1 / 2 < ν.re) {δ : ℝ} (hδ : 0 < δ)
    (N : ℕ) :
    (fun z : ℂ => struveM ν z -
      ∑ k ∈ Finset.range N, (-1) ^ (k + 1) * struveAsymptoticTerm ν z k)
      =O[sectorAtTop δ] fun z : ℂ => z ^ (ν - 2 * N - 1) := by
  set P : ℂ → ℂ := fun z => 2 * (z / 2) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2)) with hP
  have hE := hasAsymptoticExpansion_struveMIntegral (a := ν - 1 / 2) (by simp; linarith) hδ
    (2 * N)
  have hev := eventually_re_pos_sectorAtTop hδ
  have h1 := (isBigO_refl (fun z => -P z) (sectorAtTop δ)).mul hE
  have hscale : ∀ z : ℂ, ∀ m : ℕ, z ^ (-(((m : ℕ) : ℂ) + 1)) = (z ^ (m + 1))⁻¹ := by
    intro z m
    rw [cpow_neg, show ((m : ℕ) : ℂ) + 1 = ((m + 1 : ℕ) : ℂ) by push_cast; ring, cpow_natCast]
  have h2 : (fun z => -P z * z ^ (-(((2 * N : ℕ) : ℂ) + 1))) =O[sectorAtTop δ]
      fun z : ℂ => z ^ (ν - 2 * N - 1) := by
    have hc : (fun z => -P z * z ^ (-(((2 * N : ℕ) : ℂ) + 1))) =ᶠ[sectorAtTop δ]
        fun z => (-(2 / (Real.sqrt π * Gamma (ν + 1 / 2))) / 2 ^ (2 * N + 1)) *
          (z / 2) ^ (ν - 2 * N - 1) := by
      filter_upwards [hev] with z hz
      have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; linarith [hz.1]
      have hz2 : z / 2 ≠ 0 := div_ne_zero hz0 two_ne_zero
      rw [hscale z, show ν - 2 * N - 1 = ν - ((2 * N + 1 : ℕ) : ℂ) by push_cast; ring,
        cpow_sub _ _ hz2, cpow_natCast, div_pow, hP]
      simp only
      field_simp
    exact (hc.trans_isBigO ((isBigO_div_two_cpow _ _).const_mul_left _))
  refine (h1.congr' ?_ EventuallyEq.rfl).trans h2
  filter_upwards [hev] with z hz
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; linarith [hz.1]
  rw [struveM_eq_integral_weight (by linarith) hz.2, mul_sub]
  congr 1
  rw [Finset.mul_sum]
  have hsum : ∀ n ∈ Finset.range (2 * N), -P z * (z ^ (-((n : ℂ) + 1)) •
      Gamma ((n : ℂ) + 1) • struveMCoeffB (ν - 1 / 2) n) =
      if Even n then (-1) ^ (n / 2 + 1) * struveAsymptoticTerm ν z (n / 2) else 0 := by
    intro n _
    rw [struveMCoeffB]
    split_ifs with h
    · obtain ⟨m, rfl⟩ := h
      rw [show (m + m) / 2 = m by omega, ← struveK_coeff_eq ν hz0 m, smul_eq_mul, smul_eq_mul,
        show ((m + m : ℕ) : ℂ) = ((2 * m : ℕ) : ℂ) by push_cast; ring, hscale z]
      simp only [hP]
      ring
    · simp
  rw [Finset.sum_congr rfl hsum, sum_range_ite_even (fun k => (-1) ^ (k + 1) *
    struveAsymptoticTerm ν z k), show (2 * N + 1) / 2 = N by omega]

/-- The recurrence `𝐌_{ν-1} = 𝐌_{ν+1} + (2ν/z) 𝐌_ν + (z/2)^ν/(√π Γ(ν+3/2))`. -/
theorem struveM_sub_one (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    struveM (ν - 1) z = struveM (ν + 1) z + 2 * ν / z * struveM ν z +
      (z / 2) ^ ν / (Real.sqrt π * Gamma (ν + 3 / 2)) := by
  have hL := struveL_recurrence ν hz
  have hI := DLMF.Bessel.besselI_sub_add (ν := ν) (slitPlane_ne_zero hz)
  simp only [struveM]
  linear_combination hL + hI

/-- The asymptotic coefficients satisfy the same recurrence. -/
theorem struveAsymptoticTerm_sum_sub_one (ν : ℂ) {z : ℂ} (hz : z ≠ 0) (N : ℕ) :
    ∑ k ∈ Finset.range N, (-1) ^ (k + 1) * struveAsymptoticTerm (ν - 1) z k =
      ∑ k ∈ Finset.range (N + 1), (-1) ^ (k + 1) * struveAsymptoticTerm (ν + 1) z k +
      2 * ν / z * ∑ k ∈ Finset.range N, (-1) ^ (k + 1) * struveAsymptoticTerm ν z k +
      (z / 2) ^ ν / (Real.sqrt π * Gamma (ν + 3 / 2)) := by
  have hz2 : z / 2 ≠ 0 := div_ne_zero hz two_ne_zero
  have hs : (Real.sqrt π : ℂ) ≠ 0 := by
    rw [ofReal_ne_zero]; exact (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hpi : (π : ℂ) = Real.sqrt π * Real.sqrt π := by
    rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have hG12 : Gamma (1 / 2) = Real.sqrt π := by
    rw [Complex.Gamma_one_half_eq, Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]; push_cast; rfl
  rw [Finset.sum_range_succ', Finset.mul_sum]
  have h0 : (-1) ^ (0 + 1) * struveAsymptoticTerm (ν + 1) z 0 +
      (z / 2) ^ ν / (Real.sqrt π * Gamma (ν + 3 / 2)) = 0 := by
    simp only [struveAsymptoticTerm, Nat.cast_zero, zero_add, mul_zero, sub_zero]
    rw [show ν + 1 + 1 / 2 = ν + 3 / 2 by ring, show ν + 1 - 1 = ν by ring, hG12, hpi]
    field_simp
    ring
  rw [show ∀ A B C D : ℂ, A + B + C + D = (A + C) + (B + D) by intros; ring, h0, add_zero,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [struveAsymptoticTerm]
  push_cast
  have hk : (k : ℂ) + 1 / 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hΓ : Gamma ((k : ℂ) + 1 + 1 / 2) = ((k : ℂ) + 1 / 2) * Gamma ((k : ℂ) + 1 / 2) := by
    rw [show (k : ℂ) + 1 + 1 / 2 = (k : ℂ) + 1 / 2 + 1 by ring, Complex.Gamma_add_one _ hk]
  have hinv := DLMF.Hypergeometric.recip_Gamma_eq_mul_recip_Gamma_add_one (ν - 1 / 2 - k)
  rw [show ν - 1 / 2 - (k : ℂ) + 1 = ν + 1 / 2 - k by ring] at hinv
  have e1 : (z / 2) ^ (ν - 1 - 2 * (k : ℂ) - 1) = (z / 2) ^ (ν - 2 * k - 2) := by ring_nf
  have e2 : (z / 2) ^ (ν + 1 - 2 * ((k : ℂ) + 1) - 1) = (z / 2) ^ (ν - 2 * k - 2) := by ring_nf
  have e3 : (z / 2) ^ (ν - 2 * (k : ℂ) - 1) = (z / 2) ^ (ν - 2 * k - 2) * (z / 2) := by
    rw [show ν - 2 * (k : ℂ) - 1 = (ν - 2 * k - 2) + 1 by ring, cpow_add _ _ hz2, cpow_one]
  rw [e1, e2, e3, hΓ, show ν - 1 + 1 / 2 - (k : ℂ) = ν - 1 / 2 - k by ring,
    show ν + 1 + 1 / 2 - ((k : ℂ) + 1) = ν + 1 / 2 - k by ring,
    div_eq_mul_inv (Gamma ((k : ℂ) + 1 / 2)) (Gamma (ν - 1 / 2 - k)), hinv]
  field_simp
  ring

/-- One downward step of the recurrence for the expansion of `𝐌_ν`. -/
theorem struveM_asymptotic_step {l : Filter ℂ} (hl : ∀ᶠ z in l, z ∈ slitPlane) {μ : ℂ} (N : ℕ)
    (h1 : (fun z : ℂ => struveM (μ + 1) z -
      ∑ k ∈ Finset.range (N + 1), (-1) ^ (k + 1) * struveAsymptoticTerm (μ + 1) z k)
      =O[l] fun z : ℂ => z ^ (μ + 1 - 2 * ((N + 1 : ℕ) : ℂ) - 1))
    (h0 : (fun z : ℂ => struveM μ z -
      ∑ k ∈ Finset.range N, (-1) ^ (k + 1) * struveAsymptoticTerm μ z k)
      =O[l] fun z : ℂ => z ^ (μ - 2 * N - 1)) :
    (fun z : ℂ => struveM (μ - 1) z -
      ∑ k ∈ Finset.range N, (-1) ^ (k + 1) * struveAsymptoticTerm (μ - 1) z k)
      =O[l] fun z : ℂ => z ^ (μ - 1 - 2 * N - 1) := by
  have hinv : (fun z : ℂ => 2 * μ / z) =O[l] fun z : ℂ => z⁻¹ :=
    ((isBigO_refl (fun z : ℂ => z⁻¹) l).const_mul_left (2 * μ)).congr_left
      fun z => by rw [div_eq_mul_inv]
  have h0' := hinv.mul h0
  have hpow : (fun z : ℂ => z⁻¹ * z ^ (μ - 2 * N - 1)) =ᶠ[l]
      fun z : ℂ => z ^ (μ - 1 - 2 * N - 1) := by
    filter_upwards [hl] with z hz
    rw [show μ - 1 - 2 * (N : ℂ) - 1 = (μ - 2 * N - 1) - 1 by ring,
      cpow_sub (μ - 2 * N - 1) 1 (slitPlane_ne_zero hz), cpow_one, div_eq_mul_inv, mul_comm]
  have h1' : (fun z : ℂ => z ^ (μ + 1 - 2 * ((N + 1 : ℕ) : ℂ) - 1)) =
      fun z : ℂ => z ^ (μ - 1 - 2 * N - 1) := by
    funext z; congr 1; push_cast; ring
  rw [h1'] at h1
  refine (h1.add (h0'.trans_eventuallyEq hpow)).congr' ?_ EventuallyEq.rfl
  filter_upwards [hl] with z hz
  rw [struveM_sub_one μ hz, struveAsymptoticTerm_sum_sub_one μ (slitPlane_ne_zero hz) N]
  ring

/-- DLMF 11.6.2 for all orders, in the Watson sector `δ |z| ≤ re z`. -/
theorem struveM_asymptotic_sectorAtTop (ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    (fun z : ℂ => struveM ν z -
      ∑ k ∈ Finset.range N, (-1) ^ (k + 1) * struveAsymptoticTerm ν z k)
      =O[sectorAtTop δ] fun z : ℂ => z ^ (ν - 2 * N - 1) := by
  have hl : ∀ᶠ z in sectorAtTop δ, z ∈ slitPlane :=
    (eventually_re_pos_sectorAtTop hδ).mono fun z hz => Or.inl hz.2
  suffices h : ∀ m : ℕ, ∀ ν : ℂ, 1 / 2 - m < ν.re → ∀ N : ℕ,
      (fun z : ℂ => struveM ν z -
        ∑ k ∈ Finset.range N, (-1) ^ (k + 1) * struveAsymptoticTerm ν z k)
        =O[sectorAtTop δ] fun z : ℂ => z ^ (ν - 2 * N - 1) by
    obtain ⟨m, hm⟩ := exists_nat_gt (1 / 2 - ν.re)
    exact h m ν (by linarith) N
  intro m
  induction m with
  | zero =>
    intro ν hν N
    exact struveM_asymptotic_sectorAtTop_of_re (by simpa using hν) hδ N
  | succ m ih =>
    intro ν hν N
    have h1 := ih (ν + 1 + 1) (by simp at hν ⊢; linarith) (N + 1)
    have h0 := ih (ν + 1) (by simp at hν ⊢; linarith) N
    have h := struveM_asymptotic_step hl N h1 h0
    rw [show ν + 1 - 1 = ν by ring] at h
    exact h

/-- The sector `|arg z| ≤ π/2 - δ` lies in the Watson sector `sin δ · |z| ≤ re z`. -/
theorem sector_le_sectorAtTop {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π / 2) :
    DLMF.sector (π / 2 - δ) ≤ sectorAtTop (Real.sin δ) := by
  refine inf_le_inf_left _ (principal_mono.mpr fun z hz => ?_)
  obtain ⟨hz0, harg⟩ := hz
  change Real.sin δ * ‖z‖ ≤ z.re
  have hre : z.re = ‖z‖ * Real.cos (arg z) := by
    rw [Complex.cos_arg hz0]; field_simp [norm_ne_zero_iff.mpr hz0]
  rw [hre, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [← Real.cos_abs, show δ = π / 2 - (π / 2 - δ) by ring, Real.sin_pi_div_two_sub]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) harg

end WatsonExpansions

/-- Asymptotic bound with the indicated comparison function: `(fun z : ℂ => struveK ν z-∑ k ∈
Finset.range N, struveAsymptoticTerm ν z k) =O[sector (π-δ)] (fun z : ℂ => z^(ν-2*N-1))`. -/
@[dlmf 11.6.E1]
theorem struveK_asymptotic (ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun z : ℂ => struveK ν z-∑ k ∈ Finset.range N, struveAsymptoticTerm ν z k) =O[sector (π-δ)] (fun z : ℂ => z^(ν-2*N-1)) := by
  have hs : 0 < Real.sin (δ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hα : |(π - δ) / 2| < π / 2 := by rw [abs_lt]; constructor <;> linarith
  have hα' : |-((π - δ) / 2)| < π / 2 := by rwa [abs_neg]
  exact ((struveK_asymptotic_rotSector ν hs hα' N).sup
    (struveK_asymptotic_rotSector ν hs hα N)).mono (sector_le_sup_rotSectorAtTop hδ hδπ)

/-- Asymptotic bound with the indicated comparison function: `(fun z : ℂ => struveM ν z-∑ k ∈
Finset.range N, (-1)^(k+1)*struveAsymptoticTerm ν z k) =O[sector (π/2-δ)] (fun z : ℂ =>
z^(ν-2*N-1))`. -/
@[dlmf 11.6.E2]
theorem struveM_asymptotic (ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun z : ℂ => struveM ν z-∑ k ∈ Finset.range N, (-1)^(k+1)*struveAsymptoticTerm ν z k) =O[sector (π/2-δ)] (fun z : ℂ => z^(ν-2*N-1)) :=
  (struveM_asymptotic_sectorAtTop ν (Real.sin_pos_of_pos_of_lt_pi hδ (by linarith)) N).mono
    (sector_le_sectorAtTop hδ hδπ)

end DLMF.Struve
end
