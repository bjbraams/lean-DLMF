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
# Struve and Anger–Weber asymptotics

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.

The large-argument expansions 11.6.1 and 11.6.2 are proved by Watson's lemma
(`hasAsymptoticExpansion_integral_cexp_smul_sector`). For `𝐊_ν` the Laplace integral
11.5.2 (`DLMF.Bessel.struveK_eq_integral`) is rotated to the ray `arg t = α`, `|α| < π/2`
(`struveK_eq_struveKRotated`, by `Complex.integral_Ioi_eq_exp_mul_integral_Ioi_rotate`
and analytic continuation, following `DLMF.Confluent.kummerU_eq_tricomiRotated`); two
rotated sectors cover `|arg z| ≤ π - δ`. For `𝐌_ν` the integral 11.5.4 gives the case
`re ν > 1/2`, and the recurrence 11.4.25 with 10.29.1 extends it to all orders.

The large-order expansions 11.6.6–11.6.7 follow from 11.5.2 and 11.5.4 by a binomial expansion
of `(1 ± t²)^{ν-1/2}` with the uniform remainder bounds of `DLMF.Struve.LargeOrderTools`; the
binomial terms are regrouped into powers of `1/ν` through the reflected polynomials
`struveLO_Q` (`struveLO_poly_bound`). The removable singularity 11.11(iii) of the coefficient
recurrence follows from the Lagrange-inversion form `A_k(λ) = (2πi)⁻¹ ∮ (t + λ sinh t)^{-2k-1} dt`
(`struveLO_angerScaledA_eq`).
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Struve

open DLMF.Bessel DLMF.Airy

/-- struveAsymptoticTerm. -/
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

/-- struveK asymptotic. -/
@[dlmf 11.6.E1]
theorem struveK_asymptotic (ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun z : ℂ => struveK ν z-∑ k ∈ Finset.range N, struveAsymptoticTerm ν z k) =O[sector (π-δ)] (fun z : ℂ => z^(ν-2*N-1)) := by
  have hs : 0 < Real.sin (δ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hα : |(π - δ) / 2| < π / 2 := by rw [abs_lt]; constructor <;> linarith
  have hα' : |-((π - δ) / 2)| < π / 2 := by rwa [abs_neg]
  exact ((struveK_asymptotic_rotSector ν hs hα' N).sup
    (struveK_asymptotic_rotSector ν hs hα N)).mono (sector_le_sup_rotSectorAtTop hδ hδπ)

/-- struveM asymptotic. -/
@[dlmf 11.6.E2]
theorem struveM_asymptotic (ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun z : ℂ => struveM ν z-∑ k ∈ Finset.range N, (-1)^(k+1)*struveAsymptoticTerm ν z k) =O[sector (π/2-δ)] (fun z : ℂ => z^(ν-2*N-1)) :=
  (struveM_asymptotic_sectorAtTop ν (Real.sin_pos_of_pos_of_lt_pi hδ (by linarith)) N).mono
    (sector_le_sectorAtTop hδ hδπ)

section StruvePrimitive

open scoped Interval


/-- `‖𝐊₀(w)‖ ≤ M (cos α)^{-1/2} (re (w e^{iα}))^{-1/2}` from the rotated Laplace integral. -/
theorem struvePrim_norm_struveK_zero_le {α : ℝ} (hα : |α| < π / 2) {w : ℂ}
    (hw : 0 < (w * exp (α * I)).re) :
    ‖struveK 0 w‖ ≤ ‖(2 : ℂ) / (Real.sqrt π * Gamma (1 / 2))‖ *
      (Real.cos α ^ (-(1 / 2 : ℝ)) * ((1 / (w * exp (α * I)).re) ^ (1 / 2 : ℝ) *
        Real.Gamma (1 / 2))) := by
  set ω := exp (α * I) with hω
  set a := (w * ω).re with ha
  have hcα : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [neg_abs_le α], by linarith [le_abs_self α]⟩
  rw [struveK_eq_struveKRotated 0 hα hw, struveKRotated, struveKRotIntegral]
  simp only [cpow_zero, mul_one, zero_add, zero_sub]
  rw [norm_mul, norm_mul, ← hω, norm_exp_ofReal_mul_I, one_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hbound : ∀ r ∈ Ioi (0 : ℝ), ‖struveKKernel (-(1 / 2)) w (r * ω)‖ ≤
      Real.cos α ^ (-(1 / 2 : ℝ)) * (r ^ ((1 / 2 : ℝ) - 1) * Real.exp (-(a * r))) := by
    intro r hr
    have hr : (0 : ℝ) < r := hr
    rw [struveKKernel, norm_mul, norm_exp,
      show (-(1 / 2) : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring, norm_cpow_real]
    have hre : (-w * (r * ω)).re = -(a * r) := by
      rw [ha, show -w * (r * ω) = -((r : ℂ) * (w * ω)) by ring, neg_re, re_ofReal_mul]; ring
    rw [hre, ← mul_assoc, mul_comm (Real.exp _)]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    have hlow : Real.cos α * r ≤ ‖1 + ((r : ℂ) * ω) ^ 2‖ := by
      refine le_trans ?_ (cos_mul_le_norm_one_add_sq r α)
      have : r ≤ 1 + r ^ 2 := by nlinarith [sq_nonneg (r - 1)]
      exact mul_le_mul_of_nonneg_left this hcα.le
    calc ‖1 + ((r : ℂ) * ω) ^ 2‖ ^ (-(1 / 2) : ℝ) ≤ (Real.cos α * r) ^ (-(1 / 2) : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hlow (by norm_num)
      _ = _ := by rw [Real.mul_rpow hcα.le hr.le]; norm_num
  have hint : IntegrableOn (fun r : ℝ => Real.cos α ^ (-(1 / 2 : ℝ)) *
      (r ^ ((1 / 2 : ℝ) - 1) * Real.exp (-(a * r)))) (Ioi 0) := by
    have := (integrableOn_exp_neg_mul_mul_rpow_sub_one (s := 1 / 2) (by norm_num) hw).const_mul
      (Real.cos α ^ (-(1 / 2 : ℝ)))
    refine IntegrableOn.congr_fun this (fun r _ => ?_) measurableSet_Ioi
    simp only [neg_mul]; ring
  refine (norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall hbound))).trans (le_of_eq ?_)
  rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) hw]


/-- Positive real multiples stay in the slit plane. -/
theorem struvePrim_ofReal_mul_mem {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : z ∈ slitPlane) :
    (t : ℂ) * z ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hz ⊢
  rw [re_ofReal_mul, im_ofReal_mul]
  rcases hz with h | h
  · left; positivity
  · right; exact mul_ne_zero ht.ne' h

/-- A local bound `‖𝐊₀(t y)‖ ≤ C t^{-1/2}`, uniform for `y` near a point of the slit plane. -/
theorem struvePrim_local_bound {z₀ : ℂ} (hz₀ : z₀ ∈ slitPlane) :
    ∃ V ∈ 𝓝 z₀, ∃ C : ℝ, ∀ y ∈ V, ∀ t : ℝ, 0 < t → ‖struveK 0 ((t : ℂ) * y)‖ ≤ C * t ^ (-(1 / 2 : ℝ)) := by
  set α : ℝ := -(arg z₀ / 2) with hα
  have hz0 : z₀ ≠ 0 := slitPlane_ne_zero hz₀
  have harg : |arg z₀| < π := by
    rw [abs_lt]; refine ⟨neg_pi_lt_arg _, lt_of_le_of_ne (arg_le_pi _) ?_⟩
    intro h; rw [mem_slitPlane_iff_arg] at hz₀; exact hz₀.1 h
  have hαπ : |α| < π / 2 := by rw [hα, abs_neg, abs_div, abs_two]; linarith
  set ω := exp (α * I) with hω
  have hre0 : 0 < (z₀ * ω).re := by
    rw [hω, DLMF.Confluent.re_mul_exp_mul_I, hα]
    refine mul_pos (norm_pos_iff.mpr hz0) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩) <;>
      linarith [abs_lt.mp harg]
  set c := (z₀ * ω).re / 2 with hc
  have hc0 : 0 < c := by positivity
  refine ⟨{y | c < (y * ω).re}, (isOpen_lt continuous_const (by fun_prop)).mem_nhds
    (by show c < (z₀ * ω).re; linarith), ?_⟩
  set M := ‖(2 : ℂ) / (Real.sqrt π * Gamma (1 / 2))‖ * (Real.cos α ^ (-(1 / 2 : ℝ)) *
    Real.Gamma (1 / 2))
  refine ⟨M * (1 / c) ^ (1 / 2 : ℝ), fun y hy t ht => ?_⟩
  have hy' : c < (y * ω).re := hy
  have hty : 0 < ((t : ℂ) * y * ω).re := by
    rw [mul_assoc, re_ofReal_mul]; exact mul_pos ht (hc0.trans hy')
  refine (struvePrim_norm_struveK_zero_le hαπ hty).trans ?_
  rw [mul_assoc, re_ofReal_mul]
  have hM0 : 0 ≤ ‖(2 : ℂ) / (Real.sqrt π * Gamma (1 / 2))‖ * Real.cos α ^ (-(1 / 2 : ℝ)) * Real.Gamma (1 / 2) := by
    have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
    have hcα : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [neg_abs_le α], by linarith [le_abs_self α]⟩
    have := Real.rpow_pos_of_pos hcα (-(1 / 2 : ℝ))
    positivity
  have hb : 0 < (y * ω).re := hc0.trans hy'
  have hle : (1 / (t * (y * ω).re)) ^ (1 / 2 : ℝ) ≤ (1 / c) ^ (1 / 2 : ℝ) * t ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_neg ht.le, ← Real.inv_rpow ht.le, ← Real.mul_rpow (by positivity) (by positivity)]
    refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
    have := one_div_le_one_div_of_le (mul_pos ht hc0) (mul_le_mul_of_nonneg_left hy'.le ht.le)
    refine this.trans (le_of_eq ?_)
    field_simp
  calc ‖(2 : ℂ) / (Real.sqrt π * Gamma (1 / 2))‖ * (Real.cos α ^ (-(1 / 2 : ℝ)) *
        ((1 / (t * (y * ω).re)) ^ (1 / 2 : ℝ) * Real.Gamma (1 / 2)))
      = (‖(2 : ℂ) / (Real.sqrt π * Gamma (1 / 2))‖ * Real.cos α ^ (-(1 / 2 : ℝ)) *
          Real.Gamma (1 / 2)) * (1 / (t * (y * ω).re)) ^ (1 / 2 : ℝ) := by ring
    _ ≤ (‖(2 : ℂ) / (Real.sqrt π * Gamma (1 / 2))‖ * Real.cos α ^ (-(1 / 2 : ℝ)) *
          Real.Gamma (1 / 2)) * ((1 / c) ^ (1 / 2 : ℝ) * t ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hle hM0
    _ = _ := by simp only [M]; ring


/-- `𝐊₀` is continuous on the slit plane. -/
theorem struvePrim_continuousOn : ContinuousOn (struveK 0) slitPlane :=
  (DLMF.Bessel.analyticOnNhd_struveK 0).continuousOn

/-- `t ↦ 𝐊₀(t z)` is continuous on `(0, ∞)` for `z` in the slit plane. -/
theorem struvePrim_continuousOn_ray {z : ℂ} (hz : z ∈ slitPlane) :
    ContinuousOn (fun t : ℝ => struveK 0 ((t : ℂ) * z)) (Ioi 0) :=
  struvePrim_continuousOn.comp (by fun_prop) fun t ht => struvePrim_ofReal_mul_mem ht hz

/-- `t ↦ 𝐊₀(t z)` is interval integrable on `[0, 1]`. -/
theorem struvePrim_intervalIntegrable {z : ℂ} (hz : z ∈ slitPlane) :
    IntervalIntegrable (fun t : ℝ => struveK 0 ((t : ℂ) * z)) volume 0 1 := by
  obtain ⟨V, hV, C, hC⟩ := struvePrim_local_bound hz
  have hg : IntervalIntegrable (fun t : ℝ => C * t ^ (-(1 / 2 : ℝ))) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul C
  have hI : Ι (0 : ℝ) 1 = Ioc 0 1 := uIoc_of_le zero_le_one
  refine hg.mono_fun' ?_ ?_
  · rw [hI]
    exact ((struvePrim_continuousOn_ray hz).mono Ioc_subset_Ioi_self).aestronglyMeasurable
      measurableSet_Ioc
  · rw [hI]
    exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht =>
      hC z (mem_of_mem_nhds hV) t ht.1)

/-- The segment DLMF.primitive of `𝐊₀` is holomorphic on the slit plane. -/
theorem struvePrim_differentiableOn :
    DifferentiableOn ℂ (fun w : ℂ => ∫ t in (0 : ℝ)..1, struveK 0 ((t : ℂ) * w)) slitPlane := by
  have hI : Ι (0 : ℝ) 1 = Ioc 0 1 := uIoc_of_le zero_le_one
  refine Complex.differentiableOn_intervalIntegral_of_locally_dominated
    (Φ := fun w (t : ℝ) => struveK 0 ((t : ℂ) * w)) isOpen_slitPlane 0 1 ?_ ?_ ?_
  · intro x hx
    rw [hI]
    exact ((struvePrim_continuousOn_ray hx).mono Ioc_subset_Ioi_self).aestronglyMeasurable
      measurableSet_Ioc
  · rw [hI]
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
    exact (DLMF.Bessel.analyticOnNhd_struveK 0).differentiableOn.comp (by fun_prop)
      fun w hw => struvePrim_ofReal_mul_mem ht.1 hw
  · intro x hx
    obtain ⟨V, hV, C, hC⟩ := struvePrim_local_bound hx
    refine ⟨V, hV, fun t => C * t ^ (-(1 / 2 : ℝ)), ?_, ?_⟩
    · have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
        (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul C
      exact (intervalIntegrable_iff.mp this)
    · rw [hI]
      exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht y hy =>
        hC y hy t ht.1)

/-- The DLMF.primitive `∫₀^z 𝐊₀` is a holomorphic antiderivative of `𝐊₀` on the slit plane. -/
theorem struvePrim_hasDerivAt {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (DLMF.primitive (struveK 0)) (struveK 0 z) z := by
  have hP : DLMF.primitive (struveK 0) = fun w : ℂ => w * ∫ t in (0 : ℝ)..1, struveK 0 ((t : ℂ) * w) := by
    funext w; simp [DLMF.primitive, segmentIntegral]
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hPd : DifferentiableAt ℂ (DLMF.primitive (struveK 0)) z := by
    rw [hP]
    exact differentiableAt_id.mul (struvePrim_differentiableOn.differentiableAt
      (isOpen_slitPlane.mem_nhds hz))
  set F : ℝ → ℂ := fun u => struveK 0 ((u : ℂ) * z) * z with hF
  have hFc : ContinuousOn F (Ioi 0) := (struvePrim_continuousOn_ray hz).mul continuousOn_const
  have hFi : IntervalIntegrable F volume 0 1 := (struvePrim_intervalIntegrable hz).mul_const z
  have hd1 : HasDerivAt (fun s => ∫ u in (0 : ℝ)..s, F u) (F 1) 1 :=
    intervalIntegral.integral_hasDerivAt_right hFi
      (hFc.stronglyMeasurableAtFilter isOpen_Ioi 1 (by norm_num : (1 : ℝ) ∈ Ioi 0))
      (hFc.continuousAt (Ioi_mem_nhds one_pos))
  have heq : (fun s : ℝ => ∫ u in (0 : ℝ)..s, F u) =ᶠ[𝓝 1]
      fun s : ℝ => DLMF.primitive (struveK 0) ((s : ℂ) * z) := by
    filter_upwards [Ioi_mem_nhds one_pos] with s hs
    have hs0 : (s : ℝ) ≠ 0 := (show (0 : ℝ) < s from hs).ne'
    have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) F hs0
    rw [mul_zero, mul_one] at h
    rw [eq_inv_smul_iff₀ hs0] at h
    rw [← h, hP]
    simp only [hF, real_smul]
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    push_cast; ring_nf
  have hd2 : HasDerivAt (fun s : ℝ => DLMF.primitive (struveK 0) ((s : ℂ) * z))
      (deriv (DLMF.primitive (struveK 0)) z * z) 1 := by
    have h1 : HasDerivAt (fun w : ℂ => DLMF.primitive (struveK 0) (w * z))
        (deriv (DLMF.primitive (struveK 0)) z * z) ((1 : ℝ) : ℂ) := by
      have hPd' : HasDerivAt (DLMF.primitive (struveK 0)) (deriv (DLMF.primitive (struveK 0)) z)
          (((1 : ℝ) : ℂ) * z) := by rw [ofReal_one, one_mul]; exact hPd.hasDerivAt
      have := hPd'.comp ((1 : ℝ) : ℂ) (by
        simpa using (hasDerivAt_id ((1 : ℝ) : ℂ)).mul_const z :
          HasDerivAt (fun w : ℂ => w * z) z ((1 : ℝ) : ℂ))
      exact this
    exact h1.comp_ofReal
  have hu := (hd1.congr_of_eventuallyEq heq.symm).unique hd2
  simp only [hF, ofReal_one, one_mul] at hu
  have : deriv (DLMF.primitive (struveK 0)) z = struveK 0 z := mul_right_cancel₀ hz0 hu.symm
  rw [← this]
  exact hPd.hasDerivAt


/-- `∫₀^∞ ((1+τ²)^{-1/2} - (1+τ)⁻¹)/τ dτ = log 2`, with integrability. -/
theorem struvePrim_integral_log_two :
    IntegrableOn (fun τ : ℝ => (1 / Real.sqrt (1 + τ ^ 2) - 1 / (1 + τ)) / τ) (Ioi 0) ∧
    ∫ τ in Ioi (0 : ℝ), (1 / Real.sqrt (1 + τ ^ 2) - 1 / (1 + τ)) / τ = Real.log 2 := by
  set F : ℝ → ℝ := fun τ => Real.log (1 + τ) - Real.log (1 + Real.sqrt (1 + τ ^ 2)) with hF
  have hS : ∀ τ : ℝ, 0 < Real.sqrt (1 + τ ^ 2) := fun τ => Real.sqrt_pos.2 (by positivity)
  have hSS : ∀ τ : ℝ, Real.sqrt (1 + τ ^ 2) ^ 2 = 1 + τ ^ 2 := fun τ =>
    Real.sq_sqrt (by positivity)
  have hderiv : ∀ τ ∈ Ioi (0 : ℝ), HasDerivAt F
      ((1 / Real.sqrt (1 + τ ^ 2) - 1 / (1 + τ)) / τ) τ := by
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := hτ
    have h1 : HasDerivAt (fun τ : ℝ => Real.log (1 + τ)) (1 / (1 + τ)) τ := by
      have := ((hasDerivAt_id τ).const_add 1).log (by simp; linarith)
      simpa using this
    have hsq : HasDerivAt (fun τ : ℝ => Real.sqrt (1 + τ ^ 2))
        (τ / Real.sqrt (1 + τ ^ 2)) τ := by
      have := ((hasDerivAt_pow 2 τ).const_add 1).sqrt (by positivity)
      convert this using 1; push_cast; ring
    have h2 : HasDerivAt (fun τ : ℝ => Real.log (1 + Real.sqrt (1 + τ ^ 2)))
        (τ / Real.sqrt (1 + τ ^ 2) / (1 + Real.sqrt (1 + τ ^ 2))) τ := by
      have := (hsq.const_add 1).log (by have := hS τ; linarith)
      convert this using 1
    convert h1.sub h2 using 1
    have := hS τ
    have h3 := hSS τ
    field_simp
    linear_combination (-(1 + τ) * τ + τ ^ 2 - 1) * h3
  have hcont : ContinuousWithinAt F (Ici 0) 0 := by
    have : ContinuousAt F 0 := by
      refine ContinuousAt.sub ?_ ?_
      · exact (continuousAt_const.add continuousAt_id).log (by norm_num)
      · refine (continuousAt_const.add
          ((continuousAt_const.add (continuousAt_id.pow 2)).sqrt)).log ?_
        norm_num
    exact this.continuousWithinAt
  have hpos : ∀ τ ∈ Ioi (0 : ℝ), 0 ≤ (1 / Real.sqrt (1 + τ ^ 2) - 1 / (1 + τ)) / τ := by
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := hτ
    refine div_nonneg (sub_nonneg.2 ?_) hτ0.le
    refine one_div_le_one_div_of_le (hS τ) ?_
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hlim : Tendsto F atTop (𝓝 0) := by
    set h : ℝ → ℝ := fun u => Real.log ((u + 1) / (u + Real.sqrt (u ^ 2 + 1))) with hh
    have hhc : ContinuousAt h 0 := by
      refine ContinuousAt.log ?_ (by norm_num)
      refine (continuousAt_id.add continuousAt_const).div
        (continuousAt_id.add ((continuousAt_id.pow 2).add continuousAt_const).sqrt) (by norm_num)
    have h0 : h 0 = 0 := by simp [hh]
    have ht := (hhc.tendsto.comp tendsto_inv_atTop_zero)
    rw [h0] at ht
    refine ht.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with τ hτ
    simp only [Function.comp, hh, hF]
    have hS1 : 0 < 1 + Real.sqrt (1 + τ ^ 2) := by have := hS τ; linarith
    rw [← Real.log_div (by linarith) hS1.ne']
    congr 1
    have hq : Real.sqrt (τ⁻¹ ^ 2 + 1) = Real.sqrt (1 + τ ^ 2) / τ := by
      rw [show τ⁻¹ ^ 2 + 1 = (1 + τ ^ 2) / τ ^ 2 by field_simp,
        Real.sqrt_div (by positivity), Real.sqrt_sq hτ.le]
    rw [hq]
    field_simp
  have hF0 : F 0 = -Real.log 2 := by
    simp only [hF]; norm_num
  refine ⟨integrableOn_Ioi_deriv_of_nonneg hcont hderiv hpos hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hpos hlim, hF0]
  ring

/-- `∫₀^∞ ((1+τ)⁻¹ - (1+xτ)⁻¹)/τ dτ = log x` for `x > 0`, with integrability. -/
theorem struvePrim_integral_log {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun τ : ℝ => (1 / (1 + τ) - 1 / (1 + x * τ)) / τ) (Ioi 0) ∧
    ∫ τ in Ioi (0 : ℝ), (1 / (1 + τ) - 1 / (1 + x * τ)) / τ = Real.log x := by
  set G : ℝ → ℝ := fun τ => Real.log (1 + x * τ) - Real.log (1 + τ) with hG
  have hderiv : ∀ τ ∈ Ioi (0 : ℝ), HasDerivAt G ((1 / (1 + τ) - 1 / (1 + x * τ)) / τ) τ := by
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := hτ
    have h1 : HasDerivAt (fun τ : ℝ => Real.log (1 + x * τ)) (x / (1 + x * τ)) τ := by
      have hp : (1 : ℝ) + x * id τ ≠ 0 := by simp only [id_eq]; positivity
      have := (((hasDerivAt_id τ).const_mul x).const_add 1).log hp
      simpa using this
    have h2 : HasDerivAt (fun τ : ℝ => Real.log (1 + τ)) (1 / (1 + τ)) τ := by
      have := ((hasDerivAt_id τ).const_add 1).log (by simp; linarith)
      simpa using this
    convert h1.sub h2 using 1
    have : 0 < 1 + x * τ := by positivity
    field_simp
    ring
  have hcont : ContinuousWithinAt G (Ici 0) 0 := by
    have : ContinuousAt G 0 := by
      refine ContinuousAt.sub ?_ ?_
      · exact (continuousAt_const.add (continuousAt_id.const_mul x)).log (by norm_num)
      · exact (continuousAt_const.add continuousAt_id).log (by norm_num)
    exact this.continuousWithinAt
  have hlim : Tendsto G atTop (𝓝 (Real.log x)) := by
    set h : ℝ → ℝ := fun u => Real.log ((u + x) / (u + 1)) with hh
    have hhc : ContinuousAt h 0 := by
      refine ContinuousAt.log ?_ (by simp; exact hx.ne')
      exact (continuousAt_id.add continuousAt_const).div (continuousAt_id.add continuousAt_const)
        (by norm_num)
    have h0 : h 0 = Real.log x := by simp [hh]
    have ht := (hhc.tendsto.comp tendsto_inv_atTop_zero)
    rw [h0] at ht
    refine ht.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with τ hτ
    simp only [Function.comp, hh, hG]
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
  have hint : IntegrableOn (fun τ : ℝ => (1 / (1 + τ) - 1 / (1 + x * τ)) / τ) (Ioi 0) := by
    refine Integrable.mono' ((integrable_inv_one_add_sq.const_mul (|x - 1| * (1 + 1 / x))).integrableOn)
      ((ContinuousOn.div (ContinuousOn.sub
        (continuousOn_const.div (by fun_prop) fun τ (hτ : 0 < τ) => by positivity)
        (continuousOn_const.div (by fun_prop) fun τ (hτ : 0 < τ) => by positivity)) continuousOn_id
        fun τ hτ => (ne_of_gt (show (0 : ℝ) < τ from hτ))).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun τ hτ => ?_)
    have hτ0 : (0 : ℝ) < τ := hτ
    have e : (1 / (1 + τ) - 1 / (1 + x * τ)) / τ = (x - 1) / ((1 + τ) * (1 + x * τ)) := by
      have : 0 < 1 + x * τ := by positivity
      field_simp; ring
    rw [e, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < (1 + τ) * (1 + x * τ)),
      div_eq_mul_inv |x - 1|, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [← one_div, ← one_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 < 1 / x := by positivity
    have hx1 : (1 + 1 / x) * x = x + 1 := by field_simp
    nlinarith [mul_pos hτ0 hτ0, mul_pos this hτ0, mul_pos hx hτ0]
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim]
  simp [hG]

/-- `∫₀^∞ ((1+xτ)⁻¹ - e^{-xτ})/τ dτ = γ` for `x > 0`, with integrability. -/
theorem struvePrim_integral_euler {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun τ : ℝ => (1 / (1 + x * τ) - Real.exp (-(x * τ))) / τ) (Ioi 0) ∧
    ∫ τ in Ioi (0 : ℝ), (1 / (1 + x * τ) - Real.exp (-(x * τ))) / τ =
      Real.eulerMascheroniConstant := by
  set g : ℝ → ℝ := fun t => (1 / (1 + t) - Real.exp (-t)) / t with hg
  have hpt : ∀ τ : ℝ, (1 / (1 + x * τ) - Real.exp (-(x * τ))) / τ = x * g (x * τ) := by
    intro τ
    simp only [hg]
    rcases eq_or_ne τ 0 with h | h
    · simp [h]
    · field_simp
  have hgi : IntegrableOn (fun τ => g (x * τ)) (Ioi 0) := by
    rw [integrableOn_Ioi_comp_mul_left_iff g 0 hx, mul_zero]
    exact DLMF.Gamma.integrableOn_eulerIntegrand
  refine ⟨?_, ?_⟩
  · simp_rw [hpt]; exact hgi.const_mul x
  · simp_rw [hpt]
    rw [integral_const_mul, integral_comp_mul_left_Ioi g 0 hx, mul_zero, smul_eq_mul,
      ← mul_assoc, mul_inv_cancel₀ hx.ne', one_mul, DLMF.Gamma.eulerMascheroni_eq_integral_recip_one_add]

/-- The combined Frullani-type integral: `∫₀^∞ ((1+τ²)^{-1/2} - e^{-xτ})/τ dτ = log 2x + γ`. -/
theorem struvePrim_integral_log_two_mul {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun τ : ℝ => (1 / Real.sqrt (1 + τ ^ 2) - Real.exp (-(x * τ))) / τ) (Ioi 0) ∧
    ∫ τ in Ioi (0 : ℝ), (1 / Real.sqrt (1 + τ ^ 2) - Real.exp (-(x * τ))) / τ =
      Real.log (2 * x) + Real.eulerMascheroniConstant := by
  obtain ⟨i1, e1⟩ := struvePrim_integral_log_two
  obtain ⟨i2, e2⟩ := struvePrim_integral_log hx
  obtain ⟨i3, e3⟩ := struvePrim_integral_euler hx
  have hpt : (fun τ : ℝ => (1 / Real.sqrt (1 + τ ^ 2) - Real.exp (-(x * τ))) / τ) =
      fun τ => (1 / Real.sqrt (1 + τ ^ 2) - 1 / (1 + τ)) / τ +
        (1 / (1 + τ) - 1 / (1 + x * τ)) / τ + (1 / (1 + x * τ) - Real.exp (-(x * τ))) / τ := by
    funext τ; ring
  rw [hpt]
  refine ⟨(i1.add i2).add i3, ?_⟩
  have h12 := integral_add i1 i2
  have h123 := integral_add (i1.add i2) i3
  simp only [Pi.add_apply] at h12 h123
  rw [h123, h12, e1, e2, e3, Real.log_mul (by norm_num) hx.ne']


/-- The real Laplace form of `𝐊₀` on the positive axis (DLMF 11.5.2 with `ν = 0`). -/
theorem struvePrim_struveK_zero_ofReal {t : ℝ} (ht : 0 < t) :
    struveK 0 t = (((2 / π) * ∫ τ in Ioi (0 : ℝ),
      Real.exp (-(t * τ)) * (1 / Real.sqrt (1 + τ ^ 2)) : ℝ) : ℂ) := by
  rw [DLMF.Bessel.struveK_eq_integral 0 (by simpa using ht)]
  have hG : Gamma (0 + 1 / 2) = ((Real.sqrt π : ℝ) : ℂ) := by
    rw [zero_add, Complex.Gamma_one_half_eq, Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]
    push_cast; rfl
  have hint : ∫ τ in Ioi (0 : ℝ), exp (-(t : ℂ) * τ) * (1 + (τ : ℂ) ^ 2) ^ ((0 : ℂ) - 1 / 2) =
      ((∫ τ in Ioi (0 : ℝ), Real.exp (-(t * τ)) * (1 / Real.sqrt (1 + τ ^ 2)) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
    have h1 : (1 + (τ : ℂ) ^ 2) ^ ((0 : ℂ) - 1 / 2) = (((1 + τ ^ 2) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) := by
      rw [ofReal_cpow (by positivity)]; push_cast; ring_nf
    rw [h1, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, ofReal_mul, ofReal_exp]
    push_cast; ring_nf
  rw [hint, hG, cpow_zero]
  have hs : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hss : ((Real.sqrt π : ℝ) : ℂ) * (Real.sqrt π : ℝ) = (π : ℂ) := by
    rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  push_cast
  rw [mul_one, show (2 : ℂ) / (↑√π * ↑√π) = 2 / π from by rw [hss] ]

/-- `∫₀^x e^{-uτ} du = (1 - e^{-xτ})/τ` for `τ ≠ 0`. -/
theorem struvePrim_integral_exp {τ : ℝ} (hτ : τ ≠ 0) (x : ℝ) :
    ∫ u in (0 : ℝ)..x, Real.exp (-(u * τ)) = (1 - Real.exp (-(x * τ))) / τ := by
  have h : ∀ u ∈ [[(0 : ℝ), x]], HasDerivAt (fun u : ℝ => -Real.exp (-(u * τ)) / τ)
      (Real.exp (-(u * τ))) u := by
    intro u _
    have h0 : HasDerivAt (fun u : ℝ => -(u * τ)) (-τ) u := by
      exact (hasDerivAt_mul_const τ).neg
    have := (h0.exp.neg).div_const τ
    convert this using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h
    ((by fun_prop : Continuous fun u : ℝ => Real.exp (-(u * τ))).intervalIntegrable _ _)]
  simp only [zero_mul, neg_zero, Real.exp_zero]
  ring

/-- Fubini for the DLMF.primitive: `∫₀^x 𝐊₀ = (2/π) ∫₀^∞ (1+τ²)^{-1/2} (1 - e^{-xτ})/τ dτ`. -/
theorem struvePrim_primitive_ofReal {x : ℝ} (hx : 0 < x) :
    DLMF.primitive (struveK 0) x = (((2 / π) * ∫ τ in Ioi (0 : ℝ),
      (1 / Real.sqrt (1 + τ ^ 2)) * ((1 - Real.exp (-(x * τ))) / τ) : ℝ) : ℂ) := by
  set g : ℝ → ℝ := fun τ => 1 / Real.sqrt (1 + τ ^ 2) with hg
  set k : ℝ → ℝ := fun u => (2 / π) * ∫ τ in Ioi (0 : ℝ), Real.exp (-(u * τ)) * g τ with hk
  -- the DLMF.primitive as a real interval integral
  have hP : DLMF.primitive (struveK 0) x = ((∫ u in (0 : ℝ)..x, k u : ℝ) : ℂ) := by
    simp only [DLMF.primitive, segmentIntegral, sub_zero, zero_add]
    have h1 : ∫ t in (0 : ℝ)..1, struveK 0 (↑t * ↑x) = ∫ t in (0 : ℝ)..1, ((k (x * t) : ℝ) : ℂ) := by
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
      rw [uIoc_of_le zero_le_one] at ht
      rw [← ofReal_mul, mul_comm t x, struvePrim_struveK_zero_ofReal (by nlinarith [ht.1])]
    rw [h1, intervalIntegral.integral_ofReal]
    have h2 := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) k hx.ne'
    rw [mul_zero, mul_one, smul_eq_mul] at h2
    rw [h2, ← ofReal_mul, mul_inv_cancel_left₀ hx.ne']
  rw [hP]
  congr 1
  -- Fubini
  set f : ℝ → ℝ → ℝ := fun u τ => Real.exp (-(u * τ)) * g τ with hf
  have hg0 : ∀ τ, 0 ≤ g τ := fun τ => by simp only [hg]; positivity
  have hgle : ∀ τ, g τ ≤ 1 := fun τ => by
    simp only [hg]; rw [div_le_one (Real.sqrt_pos.2 (by positivity))]
    exact Real.one_le_sqrt.2 (by nlinarith)
  have hinner : ∀ τ ∈ Ioi (0 : ℝ), ∫ u in Ioc 0 x, f u τ = g τ * ((1 - Real.exp (-(x * τ))) / τ) := by
    intro τ hτ
    rw [← intervalIntegral.integral_of_le hx.le]
    simp only [hf]
    rw [intervalIntegral.integral_mul_const, struvePrim_integral_exp (ne_of_gt hτ), mul_comm]
  have hbd : ∀ τ ∈ Ioi (0 : ℝ), g τ * ((1 - Real.exp (-(x * τ))) / τ) ≤ 2 * (x + 1) * (1 + τ ^ 2)⁻¹ := by
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := hτ
    have he : 0 < Real.exp (-(x * τ)) := Real.exp_pos _
    have he1 : 1 - Real.exp (-(x * τ)) ≤ x * τ := by
      have := Real.add_one_le_exp (-(x * τ)); linarith
    rw [← div_eq_mul_inv]
    have hgτ := hgle τ
    have hg0τ := hg0 τ
    rcases le_or_gt τ 1 with h1 | h1
    · have hq : (1 - Real.exp (-(x * τ))) / τ ≤ x := by
        rw [div_le_iff₀ hτ0]; linarith
      have hq0 : 0 ≤ (1 - Real.exp (-(x * τ))) / τ := by
        have : Real.exp (-(x * τ)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
        exact div_nonneg (by linarith) hτ0.le
      calc g τ * ((1 - Real.exp (-(x * τ))) / τ) ≤ 1 * x := mul_le_mul hgτ hq hq0 zero_le_one
        _ ≤ 2 * (x + 1) / (1 + τ ^ 2) := by
          rw [le_div_iff₀ (by positivity)]
          nlinarith [mul_le_mul h1 h1 hτ0.le zero_le_one]
    · have hq : (1 - Real.exp (-(x * τ))) / τ ≤ 1 / τ := by
        gcongr; linarith
      have hgτ' : g τ ≤ 1 / τ := by
        simp only [hg]
        exact one_div_le_one_div_of_le hτ0 (Real.le_sqrt_of_sq_le (by nlinarith))
      have hq0 : 0 ≤ (1 - Real.exp (-(x * τ))) / τ := by
        have : Real.exp (-(x * τ)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
        exact div_nonneg (by linarith) hτ0.le
      calc g τ * ((1 - Real.exp (-(x * τ))) / τ) ≤ (1 / τ) * (1 / τ) :=
            mul_le_mul hgτ' hq hq0 (by positivity)
        _ ≤ 2 * (x + 1) / (1 + τ ^ 2) := by
          rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  have hgc : Continuous g := by
    simp only [hg]
    exact continuous_const.div (by fun_prop) fun τ => (Real.sqrt_pos.2 (by positivity)).ne'
  have hfc : Continuous (Function.uncurry f) := by
    simp only [hf]
    exact ((by fun_prop : Continuous fun p : ℝ × ℝ => Real.exp (-(p.1 * p.2)))).mul
      (hgc.comp continuous_snd)
  have hval : IntegrableOn (fun τ => g τ * ((1 - Real.exp (-(x * τ))) / τ)) (Ioi 0) := by
    refine Integrable.mono' ((integrable_inv_one_add_sq.const_mul (2 * (x + 1))).integrableOn)
      ((ContinuousOn.mul hgc.continuousOn (ContinuousOn.div (by fun_prop) continuousOn_id
        fun τ hτ => ne_of_gt (show (0 : ℝ) < τ from hτ))).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun τ hτ => ?_)
    have hτ0 : (0 : ℝ) < τ := hτ
    have : Real.exp (-(x * τ)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg0 τ) (div_nonneg (by linarith) hτ0.le))]
    exact hbd τ hτ
  have hint : Integrable (Function.uncurry f)
      ((volume.restrict (Ioc 0 x)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [integrable_prod_iff' hfc.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun τ => ?_, ?_⟩
    · exact (hfc.comp (by fun_prop : Continuous fun u : ℝ => (u, τ))).integrableOn_Ioc
    · refine hval.congr ((ae_restrict_iff' measurableSet_Ioi).mpr
        (Eventually.of_forall fun τ hτ => ?_))
      show g τ * ((1 - Real.exp (-(x * τ))) / τ) = ∫ u in Ioc 0 x, ‖Function.uncurry f (u, τ)‖
      rw [← hinner τ hτ]
      refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
      simp only [Function.uncurry_apply_pair, hf]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hg0 τ))]
  rw [intervalIntegral.integral_of_le hx.le]
  simp only [hk]
  rw [integral_const_mul]
  congr 1
  have hsw := integral_integral_swap hint
  simp only [hf] at hsw
  rw [hsw]
  refine setIntegral_congr_fun measurableSet_Ioi fun τ hτ => ?_
  have := hinner τ hτ
  simp only [hf] at this
  rw [this]


/-- For `τ > 0`, `0 ≤ (1 - (1+τ²)^{-1/2})/τ ≤ 1`. -/
theorem struvePrim_quot_bounds {τ : ℝ} (hτ0 : 0 < τ) :
    0 ≤ (1 - 1 / Real.sqrt (1 + τ ^ 2)) / τ ∧ (1 - 1 / Real.sqrt (1 + τ ^ 2)) / τ ≤ 1 := by
  have hS : 0 < Real.sqrt (1 + τ ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hg1 : 1 / Real.sqrt (1 + τ ^ 2) ≤ 1 := by
    rw [div_le_one hS]; exact Real.one_le_sqrt.2 (by nlinarith)
  refine ⟨div_nonneg (by linarith) hτ0.le, ?_⟩
  rw [div_le_one hτ0]
  have : 1 - τ ≤ 1 / Real.sqrt (1 + τ ^ 2) := by
    rcases le_or_gt τ 1 with h | h
    · rw [le_div_iff₀ hS]
      have hsq : Real.sqrt (1 + τ ^ 2) ≤ 1 + τ := by
        rw [Real.sqrt_le_left (by linarith)]; nlinarith
      nlinarith [hS]
    · have : 0 < 1 / Real.sqrt (1 + τ ^ 2) := by positivity
      linarith
  linarith

/-- Integrability of the remainder integrand `e^{-xτ}(1 - (1+τ²)^{-1/2})/τ` on `(0, ∞)`. -/
theorem struvePrim_rem_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun τ : ℝ => Real.exp (-(x * τ)) * ((1 - 1 / Real.sqrt (1 + τ ^ 2)) / τ))
      (Ioi 0) := by
  have hS : ∀ τ : ℝ, 0 < Real.sqrt (1 + τ ^ 2) := fun τ => Real.sqrt_pos.2 (by positivity)
  refine Integrable.mono' (exp_neg_integrableOn_Ioi 0 hx)
    ((ContinuousOn.mul (by fun_prop) (ContinuousOn.div (ContinuousOn.sub continuousOn_const
      (continuousOn_const.div (by fun_prop) fun τ _ => (hS τ).ne')) continuousOn_id
      fun τ hτ => ne_of_gt (show (0 : ℝ) < τ from hτ))).aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun τ hτ => ?_)
  obtain ⟨hq0, hq⟩ := struvePrim_quot_bounds (show (0 : ℝ) < τ from hτ)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hq0), neg_mul]
  calc Real.exp (-(x * τ)) * ((1 - 1 / Real.sqrt (1 + τ ^ 2)) / τ)
      ≤ Real.exp (-(x * τ)) * 1 := mul_le_mul_of_nonneg_left hq (Real.exp_pos _).le
    _ = _ := mul_one _

/-- On the positive axis, `∫₀^x 𝐊₀ - (2/π)(log 2x + γ) = (2/π) ∫₀^∞ e^{-xτ} (1 - (1+τ²)^{-1/2})/τ dτ`. -/
theorem struvePrim_remainder_ofReal {x : ℝ} (hx : 0 < x) :
    DLMF.primitive (struveK 0) x - 2 / π * (log (2 * x) + Real.eulerMascheroniConstant) =
      (((2 / π) * ∫ τ in Ioi (0 : ℝ),
        Real.exp (-(x * τ)) * ((1 - 1 / Real.sqrt (1 + τ ^ 2)) / τ) : ℝ) : ℂ) := by
  obtain ⟨i1, e1⟩ := struvePrim_integral_log_two_mul hx
  have hsplit : ∫ τ in Ioi (0 : ℝ), (1 / Real.sqrt (1 + τ ^ 2)) * ((1 - Real.exp (-(x * τ))) / τ) =
      (∫ τ in Ioi (0 : ℝ), (1 / Real.sqrt (1 + τ ^ 2) - Real.exp (-(x * τ))) / τ) +
        ∫ τ in Ioi (0 : ℝ), Real.exp (-(x * τ)) * ((1 - 1 / Real.sqrt (1 + τ ^ 2)) / τ) := by
    rw [← integral_add i1 (struvePrim_rem_integrable hx)]
    refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
    ring
  rw [struvePrim_primitive_ofReal hx, hsplit, e1,
    show (2 : ℂ) * x = ((2 * x : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_log (by positivity)]
  push_cast
  ring

/-- `∫₀^x 𝐊₀ - (2/π)(log 2x + γ) → 0` as `x → +∞` (the constant in DLMF 11.6.3). -/
theorem struvePrim_tendsto_ofReal :
    Tendsto (fun x : ℝ => DLMF.primitive (struveK 0) x -
      2 / π * (log (2 * x) + Real.eulerMascheroniConstant)) atTop (𝓝 0) := by
  have hb : ∀ᶠ x : ℝ in atTop, ‖DLMF.primitive (struveK 0) x -
      2 / π * (log (2 * x) + Real.eulerMascheroniConstant)‖ ≤ 2 / π * x⁻¹ := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [struvePrim_remainder_ofReal hx, norm_real, Real.norm_eq_abs]
    have hle : ∫ τ in Ioi (0 : ℝ), Real.exp (-(x * τ)) * ((1 - 1 / Real.sqrt (1 + τ ^ 2)) / τ) ≤
        ∫ τ in Ioi (0 : ℝ), Real.exp ((-x) * τ) := by
      refine setIntegral_mono_on (struvePrim_rem_integrable hx)
        (by simpa [neg_mul] using exp_neg_integrableOn_Ioi 0 hx) measurableSet_Ioi fun τ hτ => ?_
      obtain ⟨_, hq⟩ := struvePrim_quot_bounds (show (0 : ℝ) < τ from hτ)
      rw [neg_mul]
      calc Real.exp (-(x * τ)) * ((1 - 1 / Real.sqrt (1 + τ ^ 2)) / τ)
          ≤ Real.exp (-(x * τ)) * 1 := mul_le_mul_of_nonneg_left hq (Real.exp_pos _).le
        _ = _ := mul_one _
    have h0 : 0 ≤ ∫ τ in Ioi (0 : ℝ), Real.exp (-(x * τ)) * ((1 - 1 / Real.sqrt (1 + τ ^ 2)) / τ) :=
      setIntegral_nonneg measurableSet_Ioi fun τ hτ =>
        mul_nonneg (Real.exp_pos _).le (struvePrim_quot_bounds (show (0 : ℝ) < τ from hτ)).1
    rw [integral_exp_mul_Ioi (by linarith) 0, mul_zero, Real.exp_zero] at hle
    rw [abs_of_nonneg (mul_nonneg (by positivity) h0)]
    have : -1 / -x = x⁻¹ := by field_simp
    rw [this] at hle
    exact mul_le_mul_of_nonneg_left hle (by positivity)
  refine squeeze_zero_norm' hb ?_
  simpa using (tendsto_inv_atTop_zero.const_mul (2 / π))


/-- `arg (ρ e^{is}) = s` for `ρ > 0` and `s ∈ (-π, π]`. -/
theorem struvePrim_arg_ray {ρ s : ℝ} (hρ : 0 < ρ) (hs : s ∈ Ioc (-π) π) :
    arg ((ρ : ℂ) * exp (s * I)) = s := by
  rw [arg_real_mul _ hρ, exp_mul_I, arg_cos_add_sin_mul_I hs]

/-- Unpacking an eventual statement in `sector α`. -/
theorem struvePrim_exists_of_eventually_sector {α : ℝ} {p : ℂ → Prop}
    (h : ∀ᶠ z in sector α, p z) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → z ≠ 0 → |arg z| ≤ α → p z := by
  rw [sector, eventually_inf_principal] at h
  obtain ⟨t, ht, hsub⟩ := h
  obtain ⟨R, hR⟩ := mem_atTop_sets.1 ht
  exact ⟨R, fun z hz hz0 harg => hsub (hR _ hz) ⟨hz0, harg⟩⟩

/-- **Integration of a derivative bound in a sector.** If `G` is holomorphic on the slit plane,
`G(t) → 0` along the positive axis, and `‖G'(z)‖ ≤ C ‖z‖^{-(m+1)}` for large `z` with
`|arg z| ≤ α < π`, then `G(z) = O(z^{-m})` in `sector α`. -/
theorem struvePrim_isBigO_of_deriv {G G' : ℂ → ℂ} {α : ℝ} (hα0 : 0 ≤ α) (hα : α < π) {m : ℕ} (hm : 0 < m)
    (hG : ∀ z ∈ slitPlane, HasDerivAt G (G' z) z)
    (hlim : Tendsto (fun t : ℝ => G t) atTop (𝓝 0)) {R C : ℝ} (hR : 0 < R)
    (hC : ∀ z : ℂ, R ≤ ‖z‖ → |arg z| ≤ α → ‖G' z‖ ≤ C * ‖z‖ ^ (-((m : ℤ) + 1))) :
    G =O[sector α] (fun z : ℂ => z ^ (-(m : ℤ))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  -- the ray estimate
  have hray : ∀ ρ : ℝ, R ≤ ρ → ‖G ρ‖ ≤ C / m * ρ ^ (-(m : ℤ)) := by
    intro ρ hρ
    have hρ0 : 0 < ρ := hR.trans_le hρ
    have hstep : ∀ t : ℝ, ρ ≤ t → ‖G t - G ρ‖ ≤ C / m * (ρ ^ (-(m : ℤ)) - t ^ (-(m : ℤ))) := by
      intro t ht
      have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
        (f := fun u : ℝ => G u - G ρ) (f' := fun u : ℝ => G' u) (a := ρ) (b := t)
        (B := fun u : ℝ => C / m * (ρ ^ (-(m : ℤ)) - u ^ (-(m : ℤ))))
        (B' := fun u : ℝ => C * u ^ (-((m : ℤ) + 1))) ?_ ?_ ?_ ?_ ?_ ?_ (right_mem_Icc.2 ht)
      · exact key
      · intro u hu
        have hu0 : 0 < u := hρ0.trans_le hu.1
        exact ((hG u (ofReal_mem_slitPlane.2 hu0)).comp_ofReal.sub_const _).continuousAt
          |>.continuousWithinAt
      · intro u hu
        have hu0 : 0 < u := hρ0.trans_le hu.1
        exact ((hG u (ofReal_mem_slitPlane.2 hu0)).comp_ofReal.sub_const _).hasDerivWithinAt
      · simp
      · intro u hu
        have hu0 : 0 < u := hρ0.trans_le hu.1
        exact ((continuousAt_const.sub (continuousAt_zpow₀ u _ (Or.inl hu0.ne'))).const_mul _)
          |>.continuousWithinAt
      · intro u hu
        have hu0 : 0 < u := hρ0.trans_le hu.1
        have h1 := ((hasDerivAt_zpow (-(m : ℤ)) u (Or.inl hu0.ne')).const_sub
          (ρ ^ (-(m : ℤ)))).const_mul (C / m)
        convert h1.hasDerivWithinAt using 1
        rw [show -(m : ℤ) - 1 = -((m : ℤ) + 1) by ring]
        push_cast
        field_simp
      · intro u hu
        have hu0 : 0 < u := hρ0.trans_le hu.1
        have h := hC u (by rw [norm_real, Real.norm_of_nonneg hu0.le]; linarith [hu.1])
          (by rw [arg_ofReal_of_nonneg hu0.le, abs_zero]; exact hα0)
        rwa [norm_real, Real.norm_of_nonneg hu0.le] at h
    have hlim' : Tendsto (fun t : ℝ => ‖G t - G ρ‖) atTop (𝓝 ‖G ρ‖) := by
      simpa using (hlim.sub_const (G ρ)).norm
    have hB : Tendsto (fun t : ℝ => C / m * (ρ ^ (-(m : ℤ)) - t ^ (-(m : ℤ)))) atTop
        (𝓝 (C / m * ρ ^ (-(m : ℤ)))) := by
      have : Tendsto (fun t : ℝ => t ^ (-(m : ℤ))) atTop (𝓝 0) :=
        tendsto_zpow_atTop_zero (by omega)
      simpa using (tendsto_const_nhds.sub this).const_mul (C / m)
    exact le_of_tendsto_of_tendsto hlim' hB
      (eventually_atTop.2 ⟨ρ, fun t ht => hstep t ht⟩)
  have hC0 : 0 ≤ C := by
    have h := hC R (by rw [norm_real, Real.norm_of_nonneg hR.le])
      (by rw [arg_ofReal_of_nonneg hR.le, abs_zero]; exact hα0)
    rw [norm_real, Real.norm_of_nonneg hR.le] at h
    have hp : 0 < R ^ (-((m : ℤ) + 1)) := zpow_pos hR _
    by_contra hneg
    push Not at hneg
    nlinarith [norm_nonneg (G' R)]
  have hev : ∀ᶠ z in sector α, R ≤ ‖z‖ ∧ z ∈ {z : ℂ | z ≠ 0 ∧ |arg z| ≤ α} :=
    (((tendsto_comap.mono_left inf_le_left : Tendsto (fun z : ℂ => ‖z‖) (sector α) atTop)).eventually
      (eventually_ge_atTop R)).and
      (mem_inf_of_right (mem_principal_self _))
  refine IsBigO.of_bound (C / m + C * α) (hev.mono fun z ⟨hzR, hz0, hzα⟩ => ?_)
  set ρ := ‖z‖ with hρdef
  have hρ0 : 0 < ρ := hR.trans_le hzR
  set f : ℝ → ℂ := fun s => G ((ρ : ℂ) * exp (s * I)) with hf
  have hmem : ∀ s ∈ Icc (-α) α, s ∈ Ioc (-π) π := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hnormw : ∀ s : ℝ, ‖(ρ : ℂ) * exp (s * I)‖ = ρ := fun s => by
    rw [norm_mul, norm_real, Real.norm_of_nonneg hρ0.le, norm_exp_ofReal_mul_I, mul_one]
  have hderiv : ∀ s ∈ Icc (-α) α, HasDerivWithinAt f
      (G' ((ρ : ℂ) * exp (s * I)) * ((ρ : ℂ) * (exp (s * I) * I))) (Icc (-α) α) s := by
    intro s hs
    have harg := struvePrim_arg_ray hρ0 (hmem s hs)
    have hsl : (ρ : ℂ) * exp (s * I) ∈ slitPlane := by
      rw [mem_slitPlane_iff_arg, harg]
      refine ⟨by linarith [hs.2], mul_ne_zero (ofReal_ne_zero.2 hρ0.ne') (exp_ne_zero _)⟩
    have h1 : HasDerivAt (fun s : ℝ => (ρ : ℂ) * exp (s * I)) ((ρ : ℂ) * (exp (s * I) * I)) s := by
      have := (((hasDerivAt_id s).ofReal_comp).mul_const I).cexp.const_mul (ρ : ℂ)
      simpa using this
    exact ((hG _ hsl).comp s h1).hasDerivWithinAt
  have hbound : ∀ s ∈ Icc (-α) α,
      ‖G' ((ρ : ℂ) * exp (s * I)) * ((ρ : ℂ) * (exp (s * I) * I))‖ ≤ C * ρ ^ (-(m : ℤ)) := by
    intro s hs
    have harg := struvePrim_arg_ray hρ0 (hmem s hs)
    have h := hC ((ρ : ℂ) * exp (s * I)) (by rw [hnormw]; exact hzR)
      (by rw [harg, abs_le]; exact ⟨hs.1, hs.2⟩)
    rw [hnormw] at h
    rw [norm_mul, ← mul_assoc, norm_mul _ I, hnormw, norm_I, mul_one]
    calc ‖G' ((ρ : ℂ) * exp (s * I))‖ * ρ ≤ C * ρ ^ (-((m : ℤ) + 1)) * ρ :=
          mul_le_mul_of_nonneg_right h hρ0.le
      _ = C * ρ ^ (-(m : ℤ)) := by
          rw [mul_assoc, ← zpow_add_one₀ hρ0.ne']; congr 2; ring
  have hθ : arg z ∈ Icc (-α) α := abs_le.1 hzα
  have hmvt := (convex_Icc (-α) α).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (show (0 : ℝ) ∈ Icc (-α) α from ⟨by linarith, hα0⟩) hθ
  have hfz : f (arg z) = G z := by
    simp only [hf, hρdef]; rw [norm_mul_exp_arg_mul_I]
  have hf0 : f 0 = G ρ := by simp [hf]
  rw [hfz, hf0, sub_zero, Real.norm_eq_abs] at hmvt
  have hz' : ‖z ^ (-(m : ℤ))‖ = ρ ^ (-(m : ℤ)) := by rw [norm_zpow]
  rw [hz']
  have hp : 0 ≤ ρ ^ (-(m : ℤ)) := (zpow_pos hρ0 _).le
  have h1 := hray ρ hzR
  have h2 : C * ρ ^ (-(m : ℤ)) * |arg z| ≤ C * ρ ^ (-(m : ℤ)) * α :=
    mul_le_mul_of_nonneg_left hzα (mul_nonneg hC0 hp)
  calc ‖G z‖ ≤ ‖G ρ‖ + ‖G z - G ρ‖ := by
        have := norm_sub_norm_le (G z) (G ρ); linarith
    _ ≤ C / m * ρ ^ (-(m : ℤ)) + C * ρ ^ (-(m : ℤ)) * α := by linarith
    _ = (C / m + C * α) * ρ ^ (-(m : ℤ)) := by ring


/-- `Γ(1/2 - s) (2s)! = (-4)^s s! √π`. -/
theorem struvePrim_Gamma_half_sub_nat (s : ℕ) :
    Gamma (1 / 2 - s) * ((2 * s).factorial : ℂ) = (-4 : ℂ) ^ s * s.factorial * Real.sqrt π := by
  induction s with
  | zero =>
    simp only [Nat.cast_zero, sub_zero, mul_zero, Nat.factorial_zero, Nat.cast_one, mul_one,
      pow_zero, one_mul]
    rw [Complex.Gamma_one_half_eq, Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]
    push_cast; ring_nf
  | succ s ih =>
    have h1 : Gamma (1 / 2 - s) = (1 / 2 - ((s + 1 : ℕ) : ℂ)) * Gamma (1 / 2 - ((s + 1 : ℕ) : ℂ)) := by
      rw [← Gamma_add_one]
      · push_cast; ring_nf
      · intro h
        have := congrArg Complex.re h
        simp at this
        linarith
    rw [h1] at ih
    rw [show 2 * (s + 1) = 2 * s + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast at ih ⊢
    linear_combination (-2 * (2 * (s : ℂ) + 2)) * ih

/-- The `k = j+1` term of the expansion of `∫₀^z 𝐊₀` differentiates to the `k`-th term of the
expansion of `𝐊₀` (DLMF 11.6.1 with `ν = 0`). -/
theorem struvePrim_term_hasDerivAt (j : ℕ) {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (fun w : ℂ => 2 / π * ((-1) ^ (j + 1 + 1) * ((2 * (j + 1)).factorial : ℂ) *
      (2 * (j + 1) - 1).factorial / (((j + 1).factorial : ℂ) ^ 2 * (2 * w) ^ (2 * (j + 1)))))
      (struveAsymptoticTerm 0 z (j + 1)) z := by
  have hz2 : (2 : ℂ) * z ≠ 0 := mul_ne_zero two_ne_zero hz
  set n : ℕ := 2 * (j + 1) with hn
  set A : ℂ := 2 / π * ((-1) ^ (j + 1 + 1) * ((2 * (j + 1)).factorial : ℂ) *
      (2 * (j + 1) - 1).factorial / (((j + 1).factorial : ℂ) ^ 2)) with hA
  have hfun : (fun w : ℂ => 2 / π * ((-1) ^ (j + 1 + 1) * ((2 * (j + 1)).factorial : ℂ) *
      (2 * (j + 1) - 1).factorial / (((j + 1).factorial : ℂ) ^ 2 * (2 * w) ^ (2 * (j + 1))))) =
      fun w => A * (2 * w) ^ (-(n : ℤ)) := by
    funext w
    rw [hA, zpow_neg, zpow_natCast]
    field_simp
    rfl
  rw [hfun]
  have hd : HasDerivAt (fun w : ℂ => A * (2 * w) ^ (-(n : ℤ)))
      (A * ((-(n : ℤ) : ℂ) * (2 * z) ^ (-(n : ℤ) - 1) * 2)) z := by
    have h1 := (hasDerivAt_zpow (-(n : ℤ)) (2 * z) (Or.inl hz2)).comp z
      ((hasDerivAt_id z).const_mul 2)
    simpa using h1.const_mul A
  convert hd using 1
  -- identify the term
  have hG1 := Gamma_nat_add_half_mul (j + 1)
  have hG2 := struvePrim_Gamma_half_sub_nat (j + 1)
  have hsq : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_pos.ne'
  have hGa : Gamma (1 / 2 - ((j + 1 : ℕ) : ℂ)) ≠ 0 := by
    intro h; rw [h, zero_mul] at hG2
    exact (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))) hsq) hG2.symm
  have hpow : (z / 2) ^ ((0 : ℂ) - 2 * ((j + 1 : ℕ) : ℂ) - 1) = ((z / 2) ^ (n + 1))⁻¹ := by
    rw [show (0 : ℂ) - 2 * ((j + 1 : ℕ) : ℂ) - 1 = -((n + 1 : ℕ) : ℂ) by rw [hn]; push_cast; ring,
      cpow_neg, cpow_natCast]
  have hfac : ((2 * (j + 1)).factorial : ℂ) = (2 * (j + 1) : ℕ) * ((2 * (j + 1) - 1).factorial) := by
    rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, Nat.factorial_succ]; push_cast; simp
  rw [struveAsymptoticTerm, zero_add, hpow, hA,
    show (-(n : ℤ) - 1) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  have hk : ((j + 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have h2k : ((2 * (j + 1)).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have e1 : Gamma (((j + 1 : ℕ) : ℂ) + 1 / 2) =
      ((2 * (j + 1)).factorial : ℂ) * Real.sqrt π / (((j + 1).factorial : ℂ) * 4 ^ (j + 1)) := by
    rw [eq_div_iff (mul_ne_zero hk (pow_ne_zero _ (by norm_num))), ← hG1]; ring
  have e2 : Gamma (1 / 2 - ((j + 1 : ℕ) : ℂ)) =
      (-4 : ℂ) ^ (j + 1) * ((j + 1).factorial : ℂ) * Real.sqrt π / ((2 * (j + 1)).factorial : ℂ) := by
    rw [eq_div_iff h2k, ← hG2]
  rw [e1, e2, hfac, hn]
  have hz' : z / 2 ≠ 0 := div_ne_zero hz two_ne_zero
  have h2m1 : (((2 * (j + 1) - 1).factorial : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  field_simp
  push_cast
  ring_nf
  have key : (-4 : ℂ) ^ j * (-1) ^ j * (1 / 2) ^ (j * 2) * 4 ^ j = 2 ^ (j * 2) := by
    rw [mul_comm j 2, pow_mul, pow_mul, ← mul_pow, ← mul_pow, ← mul_pow]; norm_num
  linear_combination (-(↑j * z ^ 3 * z ^ (j * 2) * 16 + z ^ 3 * z ^ (j * 2) * 16)) * key


/-- The constant term `2/(πz)` of the expansion of `𝐊₀`. -/
theorem struvePrim_term_zero {z : ℂ} (hz : z ≠ 0) : struveAsymptoticTerm 0 z 0 = 2 / (π * z) := by
  have hG : Gamma (1 / 2) ≠ 0 := by
    rw [Complex.Gamma_one_half_eq]; exact (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).2
      (ofReal_ne_zero.2 Real.pi_pos.ne')
  rw [struveAsymptoticTerm]
  simp only [Nat.cast_zero, mul_zero, sub_zero, zero_add, zero_sub, div_self hG, one_mul]
  rw [cpow_neg_one]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_pos.ne'
  field_simp

/-- struveK primitive asymptotic. -/
@[dlmf 11.6.E3]
theorem struveK_primitive_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun z : ℂ => DLMF.primitive (struveK 0) z - 2/π*(log (2*z)+Real.eulerMascheroniConstant)-2/π*∑ j ∈ Finset.range N, let k:=j+1; (-1)^(k+1)*((2*k).factorial:ℂ)*(2*k-1).factorial/((k.factorial:ℂ)^2*(2*z)^(2*k))) =O[sector (π-δ)] (fun z : ℂ => z^(-(2*(N+1):ℤ))) := by
  set c : ℕ → ℂ → ℂ := fun j w => 2 / π * ((-1) ^ (j + 1 + 1) * ((2 * (j + 1)).factorial : ℂ) *
      (2 * (j + 1) - 1).factorial / (((j + 1).factorial : ℂ) ^ 2 * (2 * w) ^ (2 * (j + 1)))) with hc
  have hGeq : (fun z : ℂ => DLMF.primitive (struveK 0) z - 2/π*(log (2*z)+Real.eulerMascheroniConstant)-2/π*∑ j ∈ Finset.range N, let k:=j+1; (-1)^(k+1)*((2*k).factorial:ℂ)*(2*k-1).factorial/((k.factorial:ℂ)^2*(2*z)^(2*k))) =
      fun z => (DLMF.primitive (struveK 0) z - 2 / π * (log (2 * z) + Real.eulerMascheroniConstant)) -
        ∑ j ∈ Finset.range N, c j z := by
    funext z
    simp only [hc, Finset.mul_sum]
  rw [hGeq]
  have hα0 : 0 ≤ π - δ := by linarith
  have hα : π - δ < π := by linarith
  -- the derivative bound
  obtain ⟨C, hCb⟩ := (struveK_asymptotic 0 hδ hδπ (N + 1)).bound
  obtain ⟨R, hR⟩ := struvePrim_exists_of_eventually_sector hCb
  have hexp : ∀ z : ℂ, z ≠ 0 → ‖z ^ ((0 : ℂ) - 2 * ((N + 1 : ℕ) : ℂ) - 1)‖ =
      ‖z‖ ^ (-(((2 * (N + 1) : ℕ) : ℤ) + 1)) := by
    intro z hz
    rw [norm_cpow_of_ne_zero hz]
    have him : ((0 : ℂ) - 2 * ((N + 1 : ℕ) : ℂ) - 1).im = 0 := by simp
    rw [him, mul_zero, Real.exp_zero, div_one]
    have : ((0 : ℂ) - 2 * ((N + 1 : ℕ) : ℂ) - 1).re = ((-(((2 * (N + 1) : ℕ) : ℤ) + 1) : ℤ) : ℝ) := by
      simp; ring
    rw [this, Real.rpow_intCast]
  have hmain := struvePrim_isBigO_of_deriv (G := fun z => (DLMF.primitive (struveK 0) z -
      2 / π * (log (2 * z) + Real.eulerMascheroniConstant)) - ∑ j ∈ Finset.range N, c j z)
    (G' := fun z => struveK 0 z - ∑ k ∈ Finset.range (N + 1), struveAsymptoticTerm 0 z k) hα0 hα
    (m := 2 * (N + 1)) (by omega) ?_ ?_ (R := max R 1) (C := C) (by positivity) ?_
  · convert hmain using 3; push_cast; ring
  · -- derivative
    intro z hz
    have hz0 : z ≠ 0 := slitPlane_ne_zero hz
    have h2z : 2 * z ∈ slitPlane := by
      rw [mem_slitPlane_iff] at hz ⊢
      simp only [mul_re, mul_im, re_ofNat, im_ofNat, zero_mul, sub_zero, add_zero]
      rcases hz with h | h
      · left; linarith
      · right; simpa using h
    have hlog : HasDerivAt (fun w : ℂ => 2 / π * (log (2 * w) + Real.eulerMascheroniConstant))
        (2 / (π * z)) z := by
      have h1 := ((((hasDerivAt_id' z).const_mul 2).clog h2z).add_const
        (Real.eulerMascheroniConstant : ℂ)).const_mul (2 / (π : ℂ))
      have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_pos.ne'
      convert h1 using 1
      field_simp
    have hsum : HasDerivAt (fun w => ∑ j ∈ Finset.range N, c j w)
        (∑ j ∈ Finset.range N, struveAsymptoticTerm 0 z (j + 1)) z :=
      HasDerivAt.fun_sum fun j _ => struvePrim_term_hasDerivAt j hz0
    convert ((struvePrim_hasDerivAt hz).sub hlog).sub hsum using 1
    rw [Finset.sum_range_succ', struvePrim_term_zero hz0]
    ring
  · -- limit on the positive axis
    have hterm : ∀ j : ℕ, Tendsto (fun t : ℝ => c j t) atTop (𝓝 0) := by
      intro j
      have hpow : Tendsto (fun t : ℝ => ((2 * (t : ℂ)) ^ (2 * (j + 1)))⁻¹) atTop (𝓝 0) := by
        refine tendsto_inv₀_cobounded.comp (tendsto_norm_atTop_iff_cobounded.1 ?_)
        have h2 : Tendsto (fun t : ℝ => (2 * t) ^ (2 * (j + 1))) atTop atTop :=
          (tendsto_pow_atTop (by omega)).comp (tendsto_id.const_mul_atTop two_pos)
        refine h2.congr' ((eventually_ge_atTop 0).mono fun t ht => ?_)
        simp only [norm_pow, norm_mul, norm_real, Real.norm_of_nonneg ht,
          RCLike.norm_ofNat]
      have := hpow.const_mul (2 / π * ((-1) ^ (j + 1 + 1) * ((2 * (j + 1)).factorial : ℂ) *
        (2 * (j + 1) - 1).factorial / (((j + 1).factorial : ℂ) ^ 2)))
      rw [mul_zero] at this
      refine this.congr fun t => ?_
      simp only [hc]
      rw [mul_assoc, div_mul_eq_div_div, div_eq_mul_inv _ ((2 * (t : ℂ)) ^ (2 * (j + 1)))]
    have := struvePrim_tendsto_ofReal.sub (tendsto_finsetSum (Finset.range N) fun j _ => hterm j)
    simpa using this
  · intro z hz harg
    have hz1 : 1 ≤ ‖z‖ := (le_max_right _ _).trans hz
    have hz0 : z ≠ 0 := norm_pos_iff.1 (by linarith)
    have h := hR z ((le_max_left _ _).trans hz) hz0 harg
    rwa [hexp z hz0] at h

/-- `(1 - t²)^{-1/2}` is integrable on `(0, 1]`. -/
theorem struvePrim_integrableOn_w :
    IntegrableOn (fun t : ℝ => 1 / Real.sqrt (1 - t ^ 2)) (Ioc 0 1) := by
  refine intervalIntegral.integrableOn_deriv_of_nonneg (g := Real.arcsin) Real.continuous_arcsin.continuousOn
    (fun t ht => Real.hasDerivAt_arcsin (by linarith [ht.1]) (by linarith [ht.2]))
    (fun t _ => by positivity)

/-- `∫₀¹ ((1-t²)^{-1/2} - (1+t²)^{-1/2})/t dt = log(1+√2)`, with integrability. -/
theorem struvePrim_integral_w_sub_g :
    IntegrableOn (fun t : ℝ => (1 / Real.sqrt (1 - t ^ 2) - 1 / Real.sqrt (1 + t ^ 2)) / t)
      (Ioc 0 1) ∧
    ∫ t in Ioc (0 : ℝ) 1, (1 / Real.sqrt (1 - t ^ 2) - 1 / Real.sqrt (1 + t ^ 2)) / t =
      Real.log (1 + Real.sqrt 2) := by
  set F : ℝ → ℝ := fun t => Real.log (1 + Real.sqrt (1 + t ^ 2)) -
    Real.log (1 + Real.sqrt (1 - t ^ 2)) with hF
  have hFc : ContinuousOn F (Icc 0 1) := by
    refine ContinuousOn.sub ?_ ?_
    · exact (Real.continuousOn_log.comp (by fun_prop : Continuous fun t : ℝ =>
        1 + Real.sqrt (1 + t ^ 2)).continuousOn fun t _ => by
          have := Real.sqrt_nonneg (1 + t ^ 2); simp only [mem_compl_iff, mem_singleton_iff]
          linarith)
    · exact (Real.continuousOn_log.comp (by fun_prop : Continuous fun t : ℝ =>
        1 + Real.sqrt (1 - t ^ 2)).continuousOn fun t _ => by
          have := Real.sqrt_nonneg (1 - t ^ 2); simp only [mem_compl_iff, mem_singleton_iff]
          linarith)
  have hFd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt F
      ((1 / Real.sqrt (1 - t ^ 2) - 1 / Real.sqrt (1 + t ^ 2)) / t) t := by
    intro t ht
    have hS : 0 < 1 + t ^ 2 := by positivity
    have hQ : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    have hSs := Real.sqrt_pos.2 hS
    have hQs := Real.sqrt_pos.2 hQ
    have d1 : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
      simpa using ((hasDerivAt_pow 2 t).const_add 1)
    have d2 : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * t)) t := by
      simpa using ((hasDerivAt_pow 2 t).const_sub 1)
    have e1 := ((d1.sqrt hS.ne').const_add 1).log (by positivity)
    have e2 := ((d2.sqrt hQ.ne').const_add 1).log (by positivity)
    convert e1.sub e2 using 1
    have hS2 := Real.sq_sqrt hS.le
    have hQ2 := Real.sq_sqrt hQ.le
    have ht0 : t ≠ 0 := ht.1.ne'
    field_simp
    nlinarith [hS2, hQ2]
  have hnn : ∀ t ∈ Ioo (0 : ℝ) 1,
      0 ≤ (1 / Real.sqrt (1 - t ^ 2) - 1 / Real.sqrt (1 + t ^ 2)) / t := by
    intro t ht
    have hQ : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    refine div_nonneg (sub_nonneg.2 ?_) ht.1.le
    exact one_div_le_one_div_of_le (Real.sqrt_pos.2 hQ)
      (Real.sqrt_le_sqrt (by nlinarith))
  have hint := intervalIntegral.integrableOn_deriv_of_nonneg hFc hFd hnn
  refine ⟨hint, ?_⟩
  rw [← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hFc hFd
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 hint)]
  simp only [hF]
  norm_num

/-- `∫₁^∞ (1+τ²)^{-1/2}/τ dτ = log(1+√2)`, with integrability. -/
theorem struvePrim_integral_g_Ioi_one :
    IntegrableOn (fun t : ℝ => 1 / Real.sqrt (1 + t ^ 2) / t) (Ioi 1) ∧
    ∫ t in Ioi (1 : ℝ), 1 / Real.sqrt (1 + t ^ 2) / t = Real.log (1 + Real.sqrt 2) := by
  set H : ℝ → ℝ := fun t => Real.log t - Real.log (1 + Real.sqrt (1 + t ^ 2)) with hH
  have hHd : ∀ t ∈ Ici (1 : ℝ), HasDerivAt H (1 / Real.sqrt (1 + t ^ 2) / t) t := by
    intro t ht
    have ht0 : 0 < t := by linarith [mem_Ici.1 ht]
    have hS : 0 < 1 + t ^ 2 := by positivity
    have hSs := Real.sqrt_pos.2 hS
    have d1 : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
      simpa using ((hasDerivAt_pow 2 t).const_add 1)
    have e1 := ((d1.sqrt hS.ne').const_add 1).log (by positivity)
    convert (Real.hasDerivAt_log ht0.ne').sub e1 using 1
    have hS2 := Real.sq_sqrt hS.le
    field_simp
    nlinarith [hS2]
  have hnn : ∀ t ∈ Ioi (1 : ℝ), 0 ≤ 1 / Real.sqrt (1 + t ^ 2) / t := fun t ht => by
    have : (0 : ℝ) < t := by linarith [mem_Ioi.1 ht]
    positivity
  have hlim : Tendsto H atTop (𝓝 0) := by
    have heq : ∀ t : ℝ, 0 < t → H t = -Real.log ((1 + Real.sqrt (1 + t ^ 2)) / t) := by
      intro t ht
      simp only [hH]
      rw [Real.log_div (by positivity) ht.ne']; ring
    have h1 : Tendsto (fun t : ℝ => (1 + Real.sqrt (1 + t ^ 2)) / t) atTop (𝓝 1) := by
      have h2 : Tendsto (fun t : ℝ => 1 / t + Real.sqrt (1 / t ^ 2 + 1)) atTop (𝓝 (0 + Real.sqrt (0 + 1))) := by
        refine (tendsto_const_nhds.div_atTop tendsto_id).add ?_
        refine (Real.continuous_sqrt.tendsto _).comp ?_
        exact (tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)).add tendsto_const_nhds
      rw [zero_add, zero_add, Real.sqrt_one] at h2
      refine h2.congr' ((eventually_gt_atTop 0).mono fun t ht => ?_)
      show _ = (1 + Real.sqrt (1 + t ^ 2)) / t
      have e : 1 / t ^ 2 + 1 = (1 + t ^ 2) / t ^ 2 := by field_simp
      rw [add_div, e, Real.sqrt_div (by positivity), Real.sqrt_sq ht.le]
    have h3 := (Real.continuousAt_log one_ne_zero).tendsto.comp h1
    rw [Real.log_one] at h3
    have h4 := h3.neg
    rw [neg_zero] at h4
    exact h4.congr' ((eventually_gt_atTop 0).mono fun t ht => (heq t ht).symm)
  have hint := integrableOn_Ioi_deriv_of_nonneg' hHd hnn hlim
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hHd hnn hlim]
  simp only [hH]
  norm_num


/-- The real Laplace form of `𝐌₀` on the positive axis (DLMF 11.5.4 with `ν = 0`). -/
theorem struvePrim_struveM_zero_ofReal {u : ℝ} (hu : 0 < u) :
    struveM 0 u = ((-(2 / π) * ∫ t in Ioc (0 : ℝ) 1,
      Real.exp (-(u * t)) * (1 / Real.sqrt (1 - t ^ 2)) : ℝ) : ℂ) := by
  rw [struveM_integral (ν := 0) (by norm_num) (ofReal_mem_slitPlane.2 hu)]
  have hG : Gamma (0 + 1 / 2) = ((Real.sqrt π : ℝ) : ℂ) := by
    rw [zero_add, Complex.Gamma_one_half_eq, Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]
    push_cast; rfl
  have hint : ∫ t in (0 : ℝ)..1, exp (-(u : ℂ) * t) * (1 - (t : ℂ) ^ 2) ^ ((0 : ℂ) - 1 / 2) =
      ((∫ t in Ioc (0 : ℝ) 1, Real.exp (-(u * t)) * (1 / Real.sqrt (1 - t ^ 2)) : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have h0 : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    have h1 : (1 - (t : ℂ) ^ 2) ^ ((0 : ℂ) - 1 / 2) = (((1 - t ^ 2) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) := by
      rw [ofReal_cpow h0]; push_cast; ring_nf
    rw [h1, Real.rpow_neg h0, ← Real.sqrt_eq_rpow, ofReal_mul, ofReal_exp]
    push_cast; ring_nf
  rw [hint, hG, cpow_zero]
  have hss : ((Real.sqrt π : ℝ) : ℂ) * (Real.sqrt π : ℝ) = (π : ℂ) := by
    rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  push_cast
  rw [mul_one, hss, neg_div]

/-- Fubini for the DLMF.primitive of `𝐌₀`:
`∫₀^x 𝐌₀ = -(2/π) ∫₀¹ (1-t²)^{-1/2} (1 - e^{-xt})/t dt`. -/
theorem struvePrim_primitive_M_ofReal {x : ℝ} (hx : 0 < x) :
    DLMF.primitive (struveM 0) x = ((-(2 / π) * ∫ t in Ioc (0 : ℝ) 1,
      (1 / Real.sqrt (1 - t ^ 2)) * ((1 - Real.exp (-(x * t))) / t) : ℝ) : ℂ) := by
  set g : ℝ → ℝ := fun t => 1 / Real.sqrt (1 - t ^ 2) with hg
  set k : ℝ → ℝ := fun u => -(2 / π) * ∫ t in Ioc (0 : ℝ) 1, Real.exp (-(u * t)) * g t with hk
  have hP : DLMF.primitive (struveM 0) x = ((∫ u in (0 : ℝ)..x, k u : ℝ) : ℂ) := by
    simp only [DLMF.primitive, segmentIntegral, sub_zero, zero_add]
    have h1 : ∫ t in (0 : ℝ)..1, struveM 0 (↑t * ↑x) = ∫ t in (0 : ℝ)..1, ((k (x * t) : ℝ) : ℂ) := by
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
      rw [uIoc_of_le zero_le_one] at ht
      rw [← ofReal_mul, mul_comm t x, struvePrim_struveM_zero_ofReal (by nlinarith [ht.1])]
    rw [h1, intervalIntegral.integral_ofReal]
    have h2 := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) k hx.ne'
    rw [mul_zero, mul_one, smul_eq_mul] at h2
    rw [h2, ← ofReal_mul, mul_inv_cancel_left₀ hx.ne']
  rw [hP]
  congr 1
  set f : ℝ → ℝ → ℝ := fun u t => Real.exp (-(u * t)) * g t with hf
  have hg0 : ∀ t, 0 ≤ g t := fun t => by simp only [hg]; positivity
  have hinner : ∀ t ∈ Ioc (0 : ℝ) 1, ∫ u in Ioc 0 x, f u t = g t * ((1 - Real.exp (-(x * t))) / t) := by
    intro t ht
    rw [← intervalIntegral.integral_of_le hx.le]
    simp only [hf]
    rw [intervalIntegral.integral_mul_const, struvePrim_integral_exp (ne_of_gt ht.1), mul_comm]
  have hq : ∀ t ∈ Ioc (0 : ℝ) 1, 0 ≤ (1 - Real.exp (-(x * t))) / t ∧
      (1 - Real.exp (-(x * t))) / t ≤ x := by
    intro t ht
    have he1 : 1 - Real.exp (-(x * t)) ≤ x * t := by
      have := Real.add_one_le_exp (-(x * t)); linarith
    have : Real.exp (-(x * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [ht.1])
    exact ⟨div_nonneg (by linarith) ht.1.le, by rw [div_le_iff₀ ht.1]; linarith⟩
  have hgm : Measurable g := by simp only [hg]; fun_prop
  have hfm : Measurable (Function.uncurry f) := by
    simp only [hf]
    exact ((by fun_prop : Measurable fun p : ℝ × ℝ => Real.exp (-(p.1 * p.2)))).mul
      (hgm.comp measurable_snd)
  have hval : IntegrableOn (fun t => g t * ((1 - Real.exp (-(x * t))) / t)) (Ioc 0 1) := by
    refine Integrable.mono' (struvePrim_integrableOn_w.const_mul x)
      (((hgm.mul ((by fun_prop : Measurable fun t : ℝ => 1 - Real.exp (-(x * t))).div
        measurable_id))).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
    obtain ⟨h0, h1⟩ := hq t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg0 t) h0)]
    exact (mul_le_mul_of_nonneg_left h1 (hg0 t)).trans_eq (mul_comm _ _)
  have hint : Integrable (Function.uncurry f)
      ((volume.restrict (Ioc 0 x)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    rw [integrable_prod_iff' hfm.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun t => ?_, ?_⟩
    · exact ((by fun_prop : Continuous fun u : ℝ => Real.exp (-(u * t)) * g t)).integrableOn_Ioc
    · refine hval.congr ((ae_restrict_iff' measurableSet_Ioc).mpr
        (Eventually.of_forall fun t ht => ?_))
      show g t * ((1 - Real.exp (-(x * t))) / t) = ∫ u in Ioc 0 x, ‖Function.uncurry f (u, t)‖
      rw [← hinner t ht]
      refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
      simp only [Function.uncurry_apply_pair, hf]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hg0 t))]
  rw [intervalIntegral.integral_of_le hx.le]
  simp only [hk]
  rw [integral_const_mul]
  congr 1
  have hsw := integral_integral_swap hint
  simp only [hf] at hsw
  rw [hsw]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  have := hinner t ht
  simp only [hf] at this
  rw [this]


/-- Dominated convergence for `∫_s h(t) (1 - e^{-xt}) dt → ∫_s h` as `x → ∞`, `s ⊆ (0, ∞)`. -/
theorem struvePrim_tendsto_integral_one_sub_exp {s : Set ℝ} (hs : MeasurableSet s)
    (hpos : s ⊆ Ioi 0) {h : ℝ → ℝ} (hi : IntegrableOn h s) :
    Tendsto (fun x : ℝ => ∫ t in s, h t * (1 - Real.exp (-(x * t)))) atTop
      (𝓝 (∫ t in s, h t)) := by
  have hlim : ∀ t ∈ s, Tendsto (fun x : ℝ => h t * (1 - Real.exp (-(x * t)))) atTop (𝓝 (h t)) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := hpos ht
    have h1 : Tendsto (fun x : ℝ => Real.exp (-(x * t))) atTop (𝓝 0) := by
      refine Real.tendsto_exp_atBot.comp ?_
      exact tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const ht0)
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub h1).const_mul (h t)
  refine tendsto_integral_filter_of_dominated_convergence (fun t => ‖h t‖) ?_ ?_ hi.norm ?_
  · exact Eventually.of_forall fun x => hi.aestronglyMeasurable.mul
      ((by fun_prop : Continuous fun t : ℝ => 1 - Real.exp (-(x * t))).aestronglyMeasurable)
  · filter_upwards [eventually_ge_atTop 0] with x hx
    refine (ae_restrict_iff' hs).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := hpos ht
    have he : Real.exp (-(x * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have he0 := Real.exp_pos (-(x * t))
    rw [norm_mul, Real.norm_eq_abs (1 - _), abs_of_nonneg (by linarith)]
    nlinarith [norm_nonneg (h t)]
  · exact (ae_restrict_iff' hs).mpr (Eventually.of_forall hlim)

/-- `∫₀¹ (1-t²)^{-1/2}(1 - e^{-xt})/t dt - (log 2x + γ) → 0` as `x → ∞`. -/
theorem struvePrim_tendsto_Phi :
    Tendsto (fun x : ℝ => (∫ t in Ioc (0 : ℝ) 1,
      (1 / Real.sqrt (1 - t ^ 2)) * ((1 - Real.exp (-(x * t))) / t)) -
        (Real.log (2 * x) + Real.eulerMascheroniConstant)) atTop (𝓝 0) := by
  set w : ℝ → ℝ := fun t => 1 / Real.sqrt (1 - t ^ 2) with hw
  set g : ℝ → ℝ := fun t => 1 / Real.sqrt (1 + t ^ 2) with hg
  set E : ℝ → ℝ → ℝ := fun x t => 1 - Real.exp (-(x * t)) with hE
  set Ψ : ℝ → ℝ := fun x => ∫ τ in Ioi (0 : ℝ), g τ * (E x τ / τ) with hΨ
  -- the `𝐊₀` side
  have hK : Tendsto (fun x : ℝ => Ψ x - (Real.log (2 * x) + Real.eulerMascheroniConstant))
      atTop (𝓝 0) := by
    have h := (Complex.continuous_re.tendsto 0).comp struvePrim_tendsto_ofReal
    rw [zero_re] at h
    have h2 := h.const_mul (π / 2)
    rw [mul_zero] at h2
    refine h2.congr' ((eventually_gt_atTop 0).mono fun x hx => ?_)
    simp only [Function.comp]
    rw [struvePrim_primitive_ofReal hx, show (2 : ℂ) * x = ((2 * x : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_log (by positivity)]
    have hre : (((2 / π * ∫ τ in Ioi (0 : ℝ), 1 / Real.sqrt (1 + τ ^ 2) *
        ((1 - Real.exp (-(x * τ))) / τ) : ℝ) : ℂ) -
        2 / π * (((Real.log (2 * x)) : ℂ) + (Real.eulerMascheroniConstant : ℂ))).re =
        2 / π * (Ψ x - (Real.log (2 * x) + Real.eulerMascheroniConstant)) := by
      rw [show (2 : ℂ) / π = ((2 / π : ℝ) : ℂ) by push_cast; rfl, ← ofReal_add, ← ofReal_mul,
        ← ofReal_sub, ofReal_re]
      simp only [hΨ, hg, hE]; ring
    rw [hre]
    field_simp
  -- integrability facts
  have hI1 := struvePrim_integral_w_sub_g
  have hI2 := struvePrim_integral_g_Ioi_one
  have hmul : ∀ {s : Set ℝ}, MeasurableSet s → s ⊆ Ioi 0 → ∀ {h : ℝ → ℝ}, IntegrableOn h s →
      ∀ x : ℝ, 0 ≤ x → IntegrableOn (fun t => h t * E x t) s := by
    intro s hs hpos h hi x hx
    refine Integrable.mono' hi.norm (hi.aestronglyMeasurable.mul
      ((by fun_prop : Continuous fun t : ℝ => E x t).aestronglyMeasurable)) ?_
    refine (ae_restrict_iff' hs).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := hpos ht
    have he : Real.exp (-(x * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have he0 := Real.exp_pos (-(x * t))
    simp only [hE]
    rw [norm_mul, Real.norm_eq_abs (1 - _), abs_of_nonneg (by linarith)]
    nlinarith [norm_nonneg (h t)]
  have hgm : Measurable g := by simp only [hg]; fun_prop
  have hsmall : ∀ x : ℝ, 0 < x → IntegrableOn (fun t => g t * (E x t / t)) (Ioc 0 1) := by
    intro x hx
    refine Measure.integrableOn_of_bounded (M := x) (by simp)
      ((hgm.mul ((by fun_prop : Measurable fun t : ℝ => E x t).div measurable_id)).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
    have he1 : 1 - Real.exp (-(x * t)) ≤ x * t := by
      have := Real.add_one_le_exp (-(x * t)); linarith
    have he : Real.exp (-(x * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [ht.1])
    have hq0 : 0 ≤ E x t / t := div_nonneg (by simp only [hE]; linarith) ht.1.le
    have hq : E x t / t ≤ x := by rw [div_le_iff₀ ht.1]; simp only [hE]; linarith
    have hg0 : 0 ≤ g t := by simp only [hg]; positivity
    have hg1 : g t ≤ 1 := by
      simp only [hg]; rw [div_le_one (Real.sqrt_pos.2 (by positivity))]
      exact Real.one_le_sqrt.2 (by nlinarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hg0 hq0)]
    calc g t * (E x t / t) ≤ 1 * x := mul_le_mul hg1 hq hq0 zero_le_one
      _ = x := one_mul x
  -- the decomposition
  have hdec : ∀ x : ℝ, 0 < x →
      (∫ t in Ioc (0 : ℝ) 1, w t * (E x t / t)) - Ψ x =
        (∫ t in Ioc (0 : ℝ) 1, ((w t - g t) / t) * E x t) -
          ∫ t in Ioi (1 : ℝ), (g t / t) * E x t := by
    intro x hx
    have hA := hmul measurableSet_Ioc Ioc_subset_Ioi_self hI1.1 x hx.le
    have hB := hmul measurableSet_Ioi (Ioi_subset_Ioi zero_le_one) hI2.1 x hx.le
    have h1 : ∫ t in Ioc (0 : ℝ) 1, w t * (E x t / t) =
        (∫ t in Ioc (0 : ℝ) 1, ((w t - g t) / t) * E x t) +
          ∫ t in Ioc (0 : ℝ) 1, g t * (E x t / t) := by
      rw [← integral_add hA (hsmall x hx)]
      refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
      ring
    have h2 : Ψ x = (∫ t in Ioc (0 : ℝ) 1, g t * (E x t / t)) +
        ∫ t in Ioi (1 : ℝ), (g t / t) * E x t := by
      have hB' : IntegrableOn (fun t => g t * (E x t / t)) (Ioi 1) :=
        hB.congr_fun (fun t _ => by ring) measurableSet_Ioi
      simp only [hΨ]
      rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
        measurableSet_Ioi (hsmall x hx) hB']
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      ring
    rw [h1, h2]; ring
  have hL1 := struvePrim_tendsto_integral_one_sub_exp measurableSet_Ioc Ioc_subset_Ioi_self hI1.1
  have hL2 := struvePrim_tendsto_integral_one_sub_exp measurableSet_Ioi
    (Ioi_subset_Ioi zero_le_one) hI2.1
  rw [hI1.2] at hL1
  rw [hI2.2] at hL2
  have hfin := (hL1.sub hL2).add hK
  rw [sub_self, zero_add] at hfin
  refine hfin.congr' ((eventually_gt_atTop 0).mono fun x hx => ?_)
  have := hdec x hx
  simp only [hE, hw, hg] at this ⊢
  linarith


/-- `𝐌₀` is entire. -/
theorem struvePrim_differentiable_struveM_zero : Differentiable ℂ (struveM 0) := by
  have hL : Differentiable ℂ (struveL 0) := by simpa using struveL_nat_entire 0
  have hI : Differentiable ℂ (besselI 0) := by
    have he : besselI 0 = fun z => regularizedHGFun (∅ : Multiset ℂ) {0 + 1} (z ^ 2 / 4) := by
      funext z; simp [besselI]
    rw [he]
    exact fun z => ((analyticAt_regularized0F1 _ _).differentiableAt).comp z
      ((differentiableAt_pow 2).div_const 4)
  exact hL.sub hI

/-- The DLMF.primitive `∫₀^z 𝐌₀` differentiates to `𝐌₀`. -/
theorem struvePrim_hasDerivAt_M (z : ℂ) :
    HasDerivAt (DLMF.primitive (struveM 0)) (struveM 0 z) z := by
  have hP : DLMF.primitive (struveM 0) =
      fun w : ℂ => w * ∫ t in (0 : ℝ)..1, struveM 0 ((t : ℂ) * w) := by
    funext w; simp [DLMF.primitive, segmentIntegral]
  rw [hP]
  exact Complex.hasDerivAt_mul_integral_comp_mul struvePrim_differentiable_struveM_zero z

/-- `∫₀^x 𝐌₀ + (2/π)(log 2x + γ) → 0` as `x → +∞` (the constant in DLMF 11.6.4). -/
theorem struvePrim_tendsto_M_ofReal :
    Tendsto (fun x : ℝ => DLMF.primitive (struveM 0) x +
      2 / π * (log (2 * x) + Real.eulerMascheroniConstant)) atTop (𝓝 0) := by
  have h0 := struvePrim_tendsto_Phi.const_mul (-(2 / π))
  rw [mul_zero] at h0
  have h := (Complex.continuous_ofReal.tendsto 0).comp h0
  rw [ofReal_zero] at h
  refine h.congr' ((eventually_gt_atTop 0).mono fun x hx => ?_)
  simp only [Function.comp]
  rw [struvePrim_primitive_M_ofReal hx, show (2 : ℂ) * x = ((2 * x : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_log (by positivity)]
  push_cast
  ring

/-- struveM primitive asymptotic. -/
@[dlmf 11.6.E4]
theorem struveM_primitive_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun z : ℂ => DLMF.primitive (struveM 0) z + 2/π*(log (2*z)+Real.eulerMascheroniConstant)-2/π*∑ j ∈ Finset.range N, let k:=j+1; 1*((2*k).factorial:ℂ)*(2*k-1).factorial/((k.factorial:ℂ)^2*(2*z)^(2*k))) =O[sector (π/2-δ)] (fun z : ℂ => z^(-(2*(N+1):ℤ))) := by
  set c : ℕ → ℂ → ℂ := fun j w => 2 / π * ((-1) ^ (j + 1 + 1) * ((2 * (j + 1)).factorial : ℂ) *
      (2 * (j + 1) - 1).factorial / (((j + 1).factorial : ℂ) ^ 2 * (2 * w) ^ (2 * (j + 1)))) with hc
  have hsq : ∀ j : ℕ, ((-1 : ℂ) ^ (j + 1 + 1)) * (-1) ^ (j + 1 + 1) = 1 := fun j => by
    rw [← mul_pow]; norm_num
  have hGeq : (fun z : ℂ => DLMF.primitive (struveM 0) z + 2/π*(log (2*z)+Real.eulerMascheroniConstant)-2/π*∑ j ∈ Finset.range N, let k:=j+1; 1*((2*k).factorial:ℂ)*(2*k-1).factorial/((k.factorial:ℂ)^2*(2*z)^(2*k))) =
      fun z => (DLMF.primitive (struveM 0) z +
        2 / π * (log (2 * z) + Real.eulerMascheroniConstant)) -
        ∑ j ∈ Finset.range N, (-1) ^ (j + 1 + 1) * c j z := by
    funext z
    simp only [hc, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have := hsq j
    linear_combination (-(2 / (π : ℂ)) * (((2 * (j + 1)).factorial : ℂ) *
      (2 * (j + 1) - 1).factorial / (((j + 1).factorial : ℂ) ^ 2 * (2 * z) ^ (2 * (j + 1))))) * this
  rw [hGeq]
  have hα0 : 0 ≤ π / 2 - δ := by linarith
  have hα : π / 2 - δ < π := by linarith [Real.pi_pos]
  obtain ⟨C, hCb⟩ := (struveM_asymptotic 0 hδ hδπ (N + 1)).bound
  obtain ⟨R, hR⟩ := struvePrim_exists_of_eventually_sector hCb
  have hexp : ∀ z : ℂ, z ≠ 0 → ‖z ^ ((0 : ℂ) - 2 * ((N + 1 : ℕ) : ℂ) - 1)‖ =
      ‖z‖ ^ (-(((2 * (N + 1) : ℕ) : ℤ) + 1)) := by
    intro z hz
    rw [norm_cpow_of_ne_zero hz]
    have him : ((0 : ℂ) - 2 * ((N + 1 : ℕ) : ℂ) - 1).im = 0 := by simp
    rw [him, mul_zero, Real.exp_zero, div_one]
    have : ((0 : ℂ) - 2 * ((N + 1 : ℕ) : ℂ) - 1).re = ((-(((2 * (N + 1) : ℕ) : ℤ) + 1) : ℤ) : ℝ) := by
      simp; ring
    rw [this, Real.rpow_intCast]
  have hmain := struvePrim_isBigO_of_deriv (G := fun z => (DLMF.primitive (struveM 0) z +
      2 / π * (log (2 * z) + Real.eulerMascheroniConstant)) -
        ∑ j ∈ Finset.range N, (-1) ^ (j + 1 + 1) * c j z)
    (G' := fun z => struveM 0 z -
      ∑ k ∈ Finset.range (N + 1), (-1) ^ (k + 1) * struveAsymptoticTerm 0 z k) hα0 hα
    (m := 2 * (N + 1)) (by omega) ?_ ?_ (R := max R 1) (C := C) (by positivity) ?_
  · convert hmain using 3; push_cast; ring
  · intro z hz
    have hz0 : z ≠ 0 := slitPlane_ne_zero hz
    have h2z : 2 * z ∈ slitPlane := by
      rw [mem_slitPlane_iff] at hz ⊢
      simp only [mul_re, mul_im, re_ofNat, im_ofNat, zero_mul, sub_zero, add_zero]
      rcases hz with h | h
      · left; linarith
      · right; simpa using h
    have hlog : HasDerivAt (fun w : ℂ => 2 / π * (log (2 * w) + Real.eulerMascheroniConstant))
        (2 / (π * z)) z := by
      have h1 := ((((hasDerivAt_id' z).const_mul 2).clog h2z).add_const
        (Real.eulerMascheroniConstant : ℂ)).const_mul (2 / (π : ℂ))
      have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_pos.ne'
      convert h1 using 1
      field_simp
    have hsum : HasDerivAt (fun w => ∑ j ∈ Finset.range N, (-1) ^ (j + 1 + 1) * c j w)
        (∑ j ∈ Finset.range N, (-1) ^ (j + 1 + 1) * struveAsymptoticTerm 0 z (j + 1)) z :=
      HasDerivAt.fun_sum fun j _ => (struvePrim_term_hasDerivAt j hz0).const_mul _
    convert ((struvePrim_hasDerivAt_M z).add hlog).sub hsum using 1
    rw [Finset.sum_range_succ', struvePrim_term_zero hz0]
    ring
  · have hterm : ∀ j : ℕ, Tendsto (fun t : ℝ => (-1) ^ (j + 1 + 1) * c j t) atTop (𝓝 0) := by
      intro j
      have hpow : Tendsto (fun t : ℝ => ((2 * (t : ℂ)) ^ (2 * (j + 1)))⁻¹) atTop (𝓝 0) := by
        refine tendsto_inv₀_cobounded.comp (tendsto_norm_atTop_iff_cobounded.1 ?_)
        have h2 : Tendsto (fun t : ℝ => (2 * t) ^ (2 * (j + 1))) atTop atTop :=
          (tendsto_pow_atTop (by omega)).comp (tendsto_id.const_mul_atTop two_pos)
        refine h2.congr' ((eventually_ge_atTop 0).mono fun t ht => ?_)
        simp only [norm_pow, norm_mul, norm_real, Real.norm_of_nonneg ht, RCLike.norm_ofNat]
      have := hpow.const_mul ((-1) ^ (j + 1 + 1) * (2 / π * ((-1) ^ (j + 1 + 1) *
        ((2 * (j + 1)).factorial : ℂ) *
        (2 * (j + 1) - 1).factorial / (((j + 1).factorial : ℂ) ^ 2))))
      rw [mul_zero] at this
      refine this.congr fun t => ?_
      simp only [hc]
      rw [mul_assoc, mul_assoc, div_mul_eq_div_div, div_eq_mul_inv _ ((2 * (t : ℂ)) ^ (2 * (j + 1)))]
    have := struvePrim_tendsto_M_ofReal.sub
      (tendsto_finsetSum (Finset.range N) fun j _ => hterm j)
    simpa using this
  · intro z hz harg
    have hz1 : 1 ≤ ‖z‖ := (le_max_right _ _).trans hz
    have hz0 : z ≠ 0 := norm_pos_iff.1 (by linarith)
    have h := hR z ((le_max_left _ _).trans hz) hz0 harg
    rwa [hexp z hz0] at h

end StruvePrimitive

section LargeOrder

open scoped Interval

/-- In the sector `|arg ν| ≤ π - δ`, `‖ν + s‖ ≥ s sin δ` for `s > 0`. -/
theorem mul_sin_le_norm_add_ofReal {ν : ℂ} {δ : ℝ} (hδ : 0 < δ) (harg : |arg ν| ≤ π - δ) {s : ℝ}
    (hs : 0 < s) : s * Real.sin δ ≤ ‖ν + s‖ := by
  set θ := arg ν
  set r := ‖ν‖
  have hre : ν.re = r * Real.cos θ := (norm_mul_cos_arg ν).symm
  have him : ν.im = r * Real.sin θ := (norm_mul_sin_arg ν).symm
  have hr0 : 0 ≤ r := norm_nonneg _
  have hsq : ‖ν + s‖ ^ 2 = (r * Real.cos θ + s) ^ 2 + (r * Real.sin θ) ^ 2 := by
    rw [Complex.sq_norm, normSq_apply, add_re, add_im, ofReal_re, ofReal_im, add_zero, hre, him]
    ring
  have hcs := Real.sin_sq_add_cos_sq θ
  have hkey : (s * Real.sin δ) ^ 2 ≤ ‖ν + s‖ ^ 2 := by
    rw [hsq]
    have hsd := Real.sin_sq_le_one δ
    rcases le_or_gt 0 (Real.cos θ) with hc | hc
    · nlinarith [mul_nonneg (mul_nonneg hr0 hs.le) hc, sq_nonneg (r * Real.cos θ),
        sq_nonneg (r * Real.sin θ), mul_le_mul_of_nonneg_left hsd (sq_nonneg s)]
    · have hθ : π / 2 < |θ| := by
        by_contra h; push Not at h
        have := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (x := θ)
          (by linarith [neg_abs_le θ]) (by linarith [le_abs_self θ])
        linarith
      have h1 : Real.sin δ ≤ Real.sin (π - |θ|) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith)
          (by linarith)
      have hδ0 : 0 ≤ Real.sin δ :=
        Real.sin_nonneg_of_nonneg_of_le_pi hδ.le (by linarith [abs_nonneg θ])
      have h2 : Real.sin (π - |θ|) ^ 2 = Real.sin θ ^ 2 := by
        rw [Real.sin_pi_sub]
        rcases le_total 0 θ with h | h
        · rw [abs_of_nonneg h]
        · rw [abs_of_nonpos h, Real.sin_neg, neg_sq]
      have h3 : Real.sin δ ^ 2 ≤ Real.sin θ ^ 2 := by
        rw [← h2]
        have : 0 ≤ Real.sin (π - |θ|) := Real.sin_nonneg_of_nonneg_of_le_pi
          (by linarith [Complex.abs_arg_le_pi ν]) (by linarith [abs_nonneg θ])
        exact pow_le_pow_left₀ hδ0 h1 2
      have e : (r * Real.cos θ + s) ^ 2 + (r * Real.sin θ) ^ 2 =
          (r + s * Real.cos θ) ^ 2 + s ^ 2 * Real.sin θ ^ 2 := by
        linear_combination (r ^ 2 - s ^ 2) * hcs
      rw [e]
      nlinarith [sq_nonneg (r + s * Real.cos θ), mul_le_mul_of_nonneg_left h3 (sq_nonneg s)]
  calc s * Real.sin δ ≤ |s * Real.sin δ| := le_abs_self _
    _ = Real.sqrt ((s * Real.sin δ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (‖ν + s‖ ^ 2) := Real.sqrt_le_sqrt hkey
    _ = ‖ν + s‖ := Real.sqrt_sq (norm_nonneg _)

/-- `‖1/Γ(s₀ + k)‖ ≤ ‖1/Γ(s₀)‖ / ((3/2) sin δ)^k` for `s₀ = ν + N + 3/2` in the sector. -/
theorem norm_recip_Gamma_add_nat_le_of_arg {ν : ℂ} {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π)
    (harg : |arg ν| ≤ π - δ) (N k : ℕ) :
    ‖(Gamma (ν + N + 3 / 2 + k))⁻¹‖ ≤
      ‖(Gamma (ν + N + 3 / 2))⁻¹‖ / (3 / 2 * Real.sin δ) ^ k := by
  have hsin : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ hδπ
  have hρ : 0 < 3 / 2 * Real.sin δ := by positivity
  induction k with
  | zero => simp
  | succ k ih =>
    set s := ν + N + 3 / 2 + k with hs
    have hsn : (N + 3 / 2 + k : ℝ) * Real.sin δ ≤ ‖s‖ := by
      have := mul_sin_le_norm_add_ofReal hδ harg (s := N + 3 / 2 + k) (by positivity)
      rw [hs]; convert this using 2; push_cast; ring
    have hs1 : 3 / 2 * Real.sin δ ≤ ‖s‖ := le_trans (by
      have : (3 / 2 : ℝ) ≤ N + 3 / 2 + k := by
        have := (N.cast_nonneg : (0 : ℝ) ≤ N); have := (k.cast_nonneg : (0 : ℝ) ≤ k); linarith
      nlinarith) hsn
    have hs0 : s ≠ 0 := by
      intro h; rw [h, norm_zero] at hs1; linarith
    have hrec := DLMF.Hypergeometric.recip_Gamma_eq_mul_recip_Gamma_add_one s
    have h1 : (Gamma (s + 1))⁻¹ = (Gamma s)⁻¹ / s := by
      rw [hrec]; field_simp
    rw [show ν + N + 3 / 2 + ((k + 1 : ℕ) : ℂ) = s + 1 by rw [hs]; push_cast; ring, h1,
      norm_div, pow_succ, ← div_div]
    exact div_le_div₀ (by positivity) ih hρ hs1

/-- Tail bound for the Struve series in the order variable. -/
theorem struve_series_tail_isBigO {z : ℂ} (hz : z ≠ 0) {ε : ℂ} (hε : ‖ε‖ = 1) {δ : ℝ}
    (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) (S : ℂ → ℂ)
    (hS : ∀ ν, HasSum (fun n : ℕ => ε ^ n * (z / 2) ^ (2 * n) * struveCoeff ν n) (S ν)) :
    (fun ν : ℂ => (z / 2) ^ (ν + 1) * S ν - (z / 2) ^ (ν + 1) *
      ∑ n ∈ Finset.range N, ε ^ n * (z / 2) ^ (2 * n) * struveCoeff ν n) =O[sector (π - δ)]
      (fun ν : ℂ => (z / 2) ^ (ν + 1) / Gamma (ν + N + 3 / 2)) := by
  have hsin : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ hδπ
  set ρ := 3 / 2 * Real.sin δ with hρdef
  have hρ : 0 < ρ := by positivity
  set q := ‖z / 2‖ with hq
  have hq0 : 0 < q := norm_pos_iff.mpr (div_ne_zero hz two_ne_zero)
  set a : ℕ → ℝ := fun k => q ^ (2 * (k + N)) / (Real.Gamma ((k + N : ℕ) + 3 / 2) * ρ ^ k)
    with hadef
  have hΓpos : ∀ n : ℕ, 0 < Real.Gamma ((n : ℝ) + 3 / 2) := fun n =>
    Real.Gamma_pos_of_pos (by positivity)
  have hapos : ∀ k, 0 < a k := fun k => by rw [hadef]; have := hΓpos (k + N); positivity
  have hsum : Summable a := by
    refine summable_of_ratio_test_tendsto_lt_one (l := 0) zero_lt_one
      (Eventually.of_forall fun k => (hapos k).ne') ?_
    have hratio : ∀ k : ℕ, ‖a (k + 1)‖ / ‖a k‖ = q ^ 2 / ρ * ((k + N : ℝ) + 3 / 2)⁻¹ := by
      intro k
      rw [Real.norm_of_nonneg (hapos _).le, Real.norm_of_nonneg (hapos _).le, hadef]
      simp only
      have hG : Real.Gamma (((k + 1 + N : ℕ) : ℝ) + 3 / 2) =
          ((k + N : ℝ) + 3 / 2) * Real.Gamma (((k + N : ℕ) : ℝ) + 3 / 2) := by
        rw [show (((k + 1 + N : ℕ) : ℝ) + 3 / 2) = ((k + N : ℕ) : ℝ) + 3 / 2 + 1 by
          push_cast; ring, Real.Gamma_add_one (by positivity)]
        push_cast; ring
      rw [hG, show 2 * (k + 1 + N) = 2 * (k + N) + 2 by ring, pow_add, pow_succ]
      have := hΓpos (k + N)
      have : (0 : ℝ) < (k + N : ℝ) + 3 / 2 := by positivity
      field_simp
      ring
    simp_rw [hratio]
    rw [show (0 : ℝ) = q ^ 2 / ρ * 0 by ring]
    refine tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp ?_)
    exact tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.atTop_add
      tendsto_const_nhds)
  set A := ∑' k, a k
  refine IsBigO.of_bound A ?_
  rw [DLMF.sector, eventually_inf_principal]
  refine Eventually.of_forall fun ν hν => ?_
  obtain ⟨-, harg⟩ := hν
  have htail : S ν - ∑ n ∈ Finset.range N, ε ^ n * (z / 2) ^ (2 * n) * struveCoeff ν n =
      ∑' k, ε ^ (k + N) * (z / 2) ^ (2 * (k + N)) * struveCoeff ν (k + N) := by
    rw [← (hS ν).tsum_eq, ← (hS ν).summable.sum_add_tsum_nat_add N]; ring
  have hbd : ∀ k, ‖ε ^ (k + N) * (z / 2) ^ (2 * (k + N)) * struveCoeff ν (k + N)‖ ≤
      ‖(Gamma (ν + N + 3 / 2))⁻¹‖ * a k := by
    intro k
    have hG := norm_recip_Gamma_add_nat_le_of_arg hδ hδπ harg N k
    rw [norm_mul, norm_mul, norm_pow, norm_pow, hε, one_pow, one_mul, struveCoeff, one_div,
      mul_inv, norm_mul, show ((k + N : ℕ) : ℂ) + 3 / 2 = (((k + N : ℕ) + 3 / 2 : ℝ) : ℂ) by
        push_cast; ring, Complex.Gamma_ofReal, ← ofReal_inv, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr (hΓpos _).le),
      show ((k + N : ℕ) : ℂ) + ν + 3 / 2 = ν + N + 3 / 2 + k by push_cast; ring, hadef]
    simp only
    rw [← hq]
    calc q ^ (2 * (k + N)) * ((Real.Gamma ((k + N : ℕ) + 3 / 2))⁻¹ *
          ‖(Gamma (ν + N + 3 / 2 + k))⁻¹‖)
        ≤ q ^ (2 * (k + N)) * ((Real.Gamma ((k + N : ℕ) + 3 / 2))⁻¹ *
          (‖(Gamma (ν + N + 3 / 2))⁻¹‖ / ρ ^ k)) := by gcongr
      _ = _ := by field_simp
  have hT := tsum_of_norm_bounded ((hsum.hasSum).mul_left ‖(Gamma (ν + N + 3 / 2))⁻¹‖) hbd
  rw [← mul_sub, htail, norm_mul, norm_div]
  calc ‖(z / 2) ^ (ν + 1)‖ * ‖∑' k, ε ^ (k + N) * (z / 2) ^ (2 * (k + N)) *
        struveCoeff ν (k + N)‖
      ≤ ‖(z / 2) ^ (ν + 1)‖ * (‖(Gamma (ν + N + 3 / 2))⁻¹‖ * A) := by gcongr
    _ = _ := by rw [norm_inv]; ring

/-- In the sector `|arg ν| ≤ π - δ`, `‖ν + s‖ ≥ ‖ν‖ sin δ` for `s ≥ 0`. -/
theorem norm_mul_sin_le_norm_add_ofReal {ν : ℂ} {δ : ℝ} (hδ : 0 < δ) (harg : |arg ν| ≤ π - δ)
    {s : ℝ} (hs : 0 ≤ s) : ‖ν‖ * Real.sin δ ≤ ‖ν + s‖ := by
  set θ := arg ν
  set r := ‖ν‖
  have hre : ν.re = r * Real.cos θ := (norm_mul_cos_arg ν).symm
  have him : ν.im = r * Real.sin θ := (norm_mul_sin_arg ν).symm
  have hr0 : 0 ≤ r := norm_nonneg _
  have hsq : ‖ν + s‖ ^ 2 = (r * Real.cos θ + s) ^ 2 + (r * Real.sin θ) ^ 2 := by
    rw [Complex.sq_norm, normSq_apply, add_re, add_im, ofReal_re, ofReal_im, add_zero, hre, him]
    ring
  have hcs := Real.sin_sq_add_cos_sq θ
  have hkey : (r * Real.sin δ) ^ 2 ≤ ‖ν + s‖ ^ 2 := by
    rw [hsq]
    have hsd := Real.sin_sq_le_one δ
    rcases le_or_gt 0 (Real.cos θ) with hc | hc
    · nlinarith [mul_nonneg (mul_nonneg hr0 hs) hc, sq_nonneg s,
        mul_le_mul_of_nonneg_left hsd (sq_nonneg r)]
    · have hθ : π / 2 < |θ| := by
        by_contra h; push Not at h
        have := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (x := θ)
          (by linarith [neg_abs_le θ]) (by linarith [le_abs_self θ])
        linarith
      have h1 : Real.sin δ ≤ Real.sin (π - |θ|) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith)
          (by linarith)
      have hδ0 : 0 ≤ Real.sin δ :=
        Real.sin_nonneg_of_nonneg_of_le_pi hδ.le (by linarith [abs_nonneg θ])
      have h2 : Real.sin (π - |θ|) ^ 2 = Real.sin θ ^ 2 := by
        rw [Real.sin_pi_sub]
        rcases le_total 0 θ with h | h
        · rw [abs_of_nonneg h]
        · rw [abs_of_nonpos h, Real.sin_neg, neg_sq]
      have h3 : Real.sin δ ^ 2 ≤ Real.sin θ ^ 2 := by
        rw [← h2]; exact pow_le_pow_left₀ hδ0 h1 2
      have e : (r * Real.cos θ + s) ^ 2 + (r * Real.sin θ) ^ 2 =
          (s + r * Real.cos θ) ^ 2 + r ^ 2 * Real.sin θ ^ 2 := by ring
      rw [e]
      nlinarith [sq_nonneg (s + r * Real.cos θ), mul_le_mul_of_nonneg_left h3 (sq_nonneg r)]
  calc r * Real.sin δ ≤ |r * Real.sin δ| := le_abs_self _
    _ = Real.sqrt ((r * Real.sin δ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (‖ν + s‖ ^ 2) := Real.sqrt_le_sqrt hkey
    _ = ‖ν + s‖ := Real.sqrt_sq (norm_nonneg _)

/-- Shifting a point of the sector to the right keeps it in the slit plane. -/
theorem add_ofReal_mem_slitPlane_of_arg {ν : ℂ} (hν : ν ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (harg : |arg ν| ≤ π - δ) {s : ℝ} (hs : 0 ≤ s) : ν + s ∈ slitPlane := by
  have hslit : ν ∈ slitPlane := mem_slitPlane_iff_arg.mpr
    ⟨fun h => by rw [h, abs_of_pos Real.pi_pos] at harg; linarith, hν⟩
  rcases mem_slitPlane_iff.mp hslit with h | h
  · exact Or.inl (by simp; linarith)
  · exact Or.inr (by simpa using h)

/-- `log (ν + c) - log ν = ∫₀^c ds / (ν + s)` along a horizontal segment in the slit plane. -/
theorem log_add_ofReal_sub_log {ν : ℂ} (hν : ∀ s : ℝ, 0 ≤ s → ν + s ∈ slitPlane) {c : ℝ}
    (hc : 0 ≤ c) : log (ν + c) - log ν = ∫ s in (0 : ℝ)..c, (ν + s)⁻¹ := by
  have hd : ∀ s ∈ [[0, c]], HasDerivAt (fun s : ℝ => log (ν + s)) (ν + s)⁻¹ s := by
    intro s hs
    rw [uIcc_of_le hc] at hs
    have h1 : HasDerivAt (fun s : ℝ => ν + (s : ℂ)) 1 s := by
      simpa using ((hasDerivAt_id (s : ℂ)).const_add ν).comp_ofReal
    have h := h1.clog_real (hν s hs.1)
    simpa using h
  have hcont : ContinuousOn (fun s : ℝ => (ν + s)⁻¹) [[0, c]] := by
    intro s hs
    rw [uIcc_of_le hc] at hs
    exact ((continuous_const.add continuous_ofReal).continuousAt.inv₀
      (slitPlane_ne_zero (hν s hs.1))).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable]
  simp

/-- `log (z/2) = log z - log 2`. -/
theorem log_div_two_eq {z : ℂ} (hz : z ≠ 0) : log (z / 2) = log z - log 2 := by
  have h2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  apply Complex.ext
  · rw [log_re, sub_re, log_re, h2, ← ofReal_log (by norm_num), ofReal_re, ← h2, norm_div,
      Complex.norm_ofNat, Real.log_div (norm_ne_zero_iff.mpr hz) (by norm_num)]
  · rw [log_im, sub_im, log_im, h2, ← ofReal_log (by norm_num), ofReal_im, sub_zero, ← h2,
      div_eq_mul_inv, show (2 : ℂ)⁻¹ = ((2⁻¹ : ℝ) : ℂ) by push_cast; rfl,
      arg_mul_real (by norm_num)]

theorem tendsto_norm_sector (α : ℝ) : Tendsto (fun ν : ℂ => ‖ν‖) (sector α) atTop :=
  tendsto_comap.mono_left inf_le_left

/-- The Stirling correction in the leading large-order term tends to `0`. -/
theorem tendsto_struve_stirling_exponent {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    Tendsto (fun ν : ℂ => (ν + 1) * (log ν - log (ν + 3 / 2)) + 3 / 2 -
      DLMF.Gamma.binetMu (ν + 3 / 2)) (sector (π - δ)) (𝓝 0) := by
  have hsin : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ hδπ
  have hcos : 0 < 1 - Real.cos δ := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hδπ.le hδ
    rw [Real.cos_zero] at this; linarith
  set C := 3 / 2 / Real.sin δ + 1 / (6 * (1 - Real.cos δ)) with hC
  have hb : Tendsto (fun ν : ℂ => C * ‖ν‖⁻¹) (sector (π - δ)) (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp (tendsto_norm_sector (π - δ))).const_mul C
  refine squeeze_zero_norm' ?_ hb
  rw [DLMF.sector, eventually_inf_principal]
  filter_upwards [tendsto_comap.eventually (eventually_gt_atTop (0 : ℝ))]
    with ν hν0 hν
  obtain ⟨hν, harg⟩ := hν
  set r := ‖ν‖ with hr
  have hshift : ∀ s : ℝ, 0 ≤ s → ν + s ∈ slitPlane := fun s hs =>
    add_ofReal_mem_slitPlane_of_arg hν hδ harg hs
  -- the logarithmic part
  have hlog := log_add_ofReal_sub_log hshift (c := 3 / 2) (by norm_num)
  push_cast at hlog
  have hA : (ν + 1) * (log ν - log (ν + 3 / 2)) + 3 / 2 =
      ∫ s in (0 : ℝ)..(3 / 2), ((s : ℂ) - 1) / (ν + s) := by
    have hint : IntervalIntegrable (fun s : ℝ => (ν + s)⁻¹) volume 0 (3 / 2) := by
      refine ContinuousOn.intervalIntegrable fun s hs => ?_
      rw [uIcc_of_le (by norm_num)] at hs
      exact ((continuous_const.add continuous_ofReal).continuousAt.inv₀
        (slitPlane_ne_zero (hshift s hs.1))).continuousWithinAt
    have h1 : ∫ s in (0 : ℝ)..(3 / 2), ((s : ℂ) - 1) / (ν + s) =
        ∫ s in (0 : ℝ)..(3 / 2), (1 - (ν + 1) * (ν + s)⁻¹) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le (by norm_num)] at hs
      have := slitPlane_ne_zero (hshift s hs.1)
      field_simp
      ring
    rw [h1, intervalIntegral.integral_sub intervalIntegrable_const (hint.const_mul _),
      intervalIntegral.integral_const_mul, ← hlog]
    simp
    ring
  have hAb : ‖∫ s in (0 : ℝ)..(3 / 2), ((s : ℂ) - 1) / (ν + s)‖ ≤
      1 / (r * Real.sin δ) * |3 / 2 - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
    rw [uIoc_of_le (by norm_num)] at hs
    have h1 := norm_mul_sin_le_norm_add_ofReal hδ harg (s := s) hs.1.le
    have h2 : ‖(s : ℂ) - 1‖ ≤ 1 := by
      rw [show (s : ℂ) - 1 = ((s - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hs.1, hs.2]
    rw [norm_div]
    have hp : 0 < r * Real.sin δ := by positivity
    calc ‖(s : ℂ) - 1‖ / ‖ν + s‖ ≤ 1 / ‖ν + s‖ := by gcongr
      _ ≤ 1 / (r * Real.sin δ) := by gcongr
  -- the Binet part
  have hw : ν + 3 / 2 ∈ slitPlane := by simpa using hshift (3 / 2) (by norm_num)
  have hμ := DLMF.Gamma.norm_binetMu_le hw
  have hcosθ : -Real.cos δ ≤ Real.cos (arg ν) := by
    rw [← Real.cos_pi_sub, ← Real.cos_abs (arg ν)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) harg
  have hre : ν.re = r * Real.cos (arg ν) := (norm_mul_cos_arg ν).symm
  have hwre : r * (1 - Real.cos δ) ≤ ‖ν + 3 / 2‖ + (ν + 3 / 2).re := by
    have h1 : r ≤ ‖ν + 3 / 2‖ + 3 / 2 := by
      have := norm_add_le (ν + 3 / 2) (-(3 / 2 : ℂ))
      simp only [add_neg_cancel_right, norm_neg] at this
      norm_num at this ⊢; linarith
    have h2 : (ν + 3 / 2).re = ν.re + 3 / 2 := by simp
    rw [h2, hre]
    nlinarith
  have hμb : ‖DLMF.Gamma.binetMu (ν + 3 / 2)‖ ≤ 1 / (6 * (r * (1 - Real.cos δ))) :=
    hμ.trans (one_div_le_one_div_of_le (by positivity) (by linarith))
  rw [hA]
  refine (norm_sub_le _ _).trans ?_
  have e : C * r⁻¹ = 1 / (r * Real.sin δ) * |3 / 2 - 0| + 1 / (6 * (r * (1 - Real.cos δ))) := by
    rw [hC, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2 - 0)]
    field_simp
    ring
  rw [e]
  exact add_le_add hAb hμb

/-- The leading term of the Struve series written through Binet's formula. -/
theorem struve_lead_eq {z : ℂ} (hz : z ≠ 0) {ν : ℂ} (hν : ν ≠ 0) (hw : ν + 3 / 2 ∈ slitPlane) :
    (z / 2) ^ (ν + 1) * struveCoeff ν 0 =
      z / (π * ν * Real.sqrt 2) * exp (ν * (1 + log z - log 2 - log ν)) *
        exp ((ν + 1) * (log ν - log (ν + 3 / 2)) + 3 / 2 - DLMF.Gamma.binetMu (ν + 3 / 2)) := by
  have hz2 : z / 2 ≠ 0 := div_ne_zero hz two_ne_zero
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hG32 : Gamma (3 / 2) = exp (log π * (1 / 2)) / exp (log 2) := by
    rw [show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num, Complex.Gamma_add_one _ (by norm_num),
      Complex.Gamma_one_half_eq, cpow_def_of_ne_zero hπ, exp_log two_ne_zero]
    ring
  have hGw := DLMF.Gamma.Gamma_eq_exp_binetExponent hw
  have hl2π : log (2 * π : ℂ) = log 2 + log π := by
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, ← ofReal_log (by positivity),
      Real.log_mul (by norm_num) Real.pi_ne_zero, ofReal_add, ofReal_log (by norm_num),
      ofReal_log Real.pi_pos.le]
    norm_num
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) = exp (log 2 * (1 / 2)) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow (by norm_num), cpow_def_of_ne_zero (by norm_num)]
    push_cast; ring_nf
  have hpre : z / (π * ν * Real.sqrt 2) = exp (log z - log π - log ν - log 2 * (1 / 2)) := by
    rw [Complex.exp_sub, Complex.exp_sub, Complex.exp_sub, exp_log hz, exp_log hπ, exp_log hν,
      ← hs2]
    field_simp
  rw [hpre, struveCoeff, Nat.cast_zero, zero_add, zero_add, hG32, hGw, DLMF.Gamma.binetExponent,
    hl2π, cpow_def_of_ne_zero hz2, log_div_two_eq hz]
  simp only [div_eq_mul_inv, one_mul, ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  ring

/-- `(z/2)^{ν+1} / (Γ(3/2) Γ(ν+3/2))` has the leading behaviour of DLMF 11.6.5. -/
theorem struve_lead_isEquivalent {z : ℂ} (hz : z ≠ 0) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun ν : ℂ => (z / 2) ^ (ν + 1) * struveCoeff ν 0) ~[sector (π - δ)]
      fun ν => z / (π * ν * Real.sqrt 2) * exp (ν * (1 + log z - log 2 - log ν)) := by
  refine isEquivalent_of_tendsto_one ?_
  have h := (Complex.continuous_exp.tendsto 0).comp (tendsto_struve_stirling_exponent hδ hδπ)
  rw [Complex.exp_zero] at h
  refine h.congr' ?_
  rw [EventuallyEq, DLMF.sector, eventually_inf_principal]
  refine Eventually.of_forall fun ν hν => ?_
  obtain ⟨hν0, harg⟩ := hν
  have hw : ν + 3 / 2 ∈ slitPlane := by
    simpa using add_ofReal_mem_slitPlane_of_arg hν0 hδ harg (s := 3 / 2) (by norm_num)
  have hg : z / (π * ν * Real.sqrt 2) * exp (ν * (1 + log z - log 2 - log ν)) ≠ 0 := by
    refine mul_ne_zero (div_ne_zero hz (mul_ne_zero (mul_ne_zero ?_ hν0) ?_)) (exp_ne_zero _)
    · exact ofReal_ne_zero.mpr Real.pi_ne_zero
    · exact ofReal_ne_zero.mpr (by positivity)
  simp only [Function.comp_apply, Pi.div_apply]
  rw [struve_lead_eq hz hν0 hw, mul_div_cancel_left₀ _ hg]

/-- From the first term of the order expansion to the leading behaviour of DLMF 11.6.5. -/
theorem isEquivalent_of_struve_order_expansion {f : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0) {δ : ℝ}
    (hδ : 0 < δ) (hδπ : δ < π)
    (h : (fun ν : ℂ => f ν - (z / 2) ^ (ν + 1) * struveCoeff ν 0) =O[sector (π - δ)]
      fun ν : ℂ => (z / 2) ^ (ν + 1) / Gamma (ν + ((1 : ℕ) : ℂ) + 3 / 2)) :
    f ~[sector (π - δ)]
      fun ν => z / (π * ν * Real.sqrt 2) * exp (ν * (1 + log z - log 2 - log ν)) := by
  have hsin : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ hδπ
  set lead : ℂ → ℂ := fun ν => (z / 2) ^ (ν + 1) * struveCoeff ν 0 with hlead
  set k : ℂ → ℂ := fun ν => Gamma (3 / 2) / (ν + 3 / 2) with hk
  have hk0 : Tendsto k (sector (π - δ)) (𝓝 0) := by
    have hb : Tendsto (fun ν : ℂ => ‖Gamma (3 / 2)‖ / Real.sin δ * ‖ν‖⁻¹) (sector (π - δ))
        (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp (tendsto_norm_sector (π - δ))).const_mul
        (‖Gamma (3 / 2)‖ / Real.sin δ)
    refine squeeze_zero_norm' ?_ hb
    rw [DLMF.sector, eventually_inf_principal]
    filter_upwards [tendsto_comap.eventually (eventually_gt_atTop (0 : ℝ))] with ν hν0 hν
    obtain ⟨-, harg⟩ := hν
    have h1 := norm_mul_sin_le_norm_add_ofReal hδ harg (s := 3 / 2) (by norm_num)
    push_cast at h1
    rw [hk, norm_div]
    have hp : 0 < ‖ν‖ * Real.sin δ := by positivity
    calc ‖Gamma (3 / 2)‖ / ‖ν + 3 / 2‖ ≤ ‖Gamma (3 / 2)‖ / (‖ν‖ * Real.sin δ) := by gcongr
      _ = _ := by field_simp
  have hko : k =o[sector (π - δ)] fun _ => (1 : ℂ) := (isLittleO_one_iff ℂ).mpr hk0
  have hrem : (fun ν : ℂ => (z / 2) ^ (ν + 1) / Gamma (ν + ((1 : ℕ) : ℂ) + 3 / 2)) =ᶠ[sector (π - δ)]
      fun ν => lead ν * k ν := by
    rw [EventuallyEq, DLMF.sector, eventually_inf_principal]
    refine Eventually.of_forall fun ν hν => ?_
    obtain ⟨hν0, harg⟩ := hν
    have hw0 : ν + 3 / 2 ≠ 0 := slitPlane_ne_zero (by
      simpa using add_ofReal_mem_slitPlane_of_arg hν0 hδ harg (s := 3 / 2) (by norm_num))
    have hG32 : Gamma (3 / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by norm_num)
    have hrec := DLMF.Hypergeometric.recip_Gamma_eq_mul_recip_Gamma_add_one (ν + 3 / 2)
    have h5 : (Gamma (ν + ((1 : ℕ) : ℂ) + 3 / 2))⁻¹ = (Gamma (ν + 3 / 2))⁻¹ / (ν + 3 / 2) := by
      rw [show ν + ((1 : ℕ) : ℂ) + 3 / 2 = ν + 3 / 2 + 1 by push_cast; ring, eq_div_iff hw0,
        mul_comm, ← hrec]
    simp only [hlead, hk, struveCoeff, Nat.cast_zero, zero_add]
    rw [div_eq_mul_inv, h5]
    field_simp
  have hE : (fun ν => f ν - lead ν) =o[sector (π - δ)] lead := by
    have h1 := h.trans_eventuallyEq hrem
    have h2 : (fun ν => lead ν * k ν) =o[sector (π - δ)] fun ν => lead ν * 1 :=
      (isBigO_refl lead _).mul_isLittleO hko
    simpa using h1.trans_isLittleO h2
  have hE' : f ~[sector (π - δ)] lead := hE
  exact hE'.trans (struve_lead_isEquivalent hz hδ hδπ)

end LargeOrder

/-- struveH large order. -/
@[dlmf 11.6.E5]
theorem struveH_large_order {z : ℂ} (hz : z ∈ slitPlane) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun ν : ℂ => struveH ν z) ~[sector (π-δ)] (fun ν => z/(π*ν*Real.sqrt 2)*exp (ν*(1+log z-log 2-log ν))) := by
  refine isEquivalent_of_struve_order_expansion (slitPlane_ne_zero hz) hδ hδπ ?_
  simpa [struveH] using struve_series_tail_isBigO (slitPlane_ne_zero hz) (by simp) hδ hδπ 1
    (fun ν => struveHCore ν z) (fun ν => hasSum_struveHCore ν z)

/-- struveL large order. -/
@[dlmf 11.6.E5]
theorem struveL_large_order {z : ℂ} (hz : z ∈ slitPlane) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun ν : ℂ => struveL ν z) ~[sector (π-δ)] (fun ν => z/(π*ν*Real.sqrt 2)*exp (ν*(1+log z-log 2-log ν))) := by
  refine isEquivalent_of_struve_order_expansion (slitPlane_ne_zero hz) hδ hδπ ?_
  have h := struve_series_tail_isBigO (slitPlane_ne_zero hz) (ε := 1) (by simp) hδ hδπ 1
    (fun ν => struveLCore ν z) (fun ν => by simpa using hasSum_struveLCore ν z)
  simpa [struveL] using h

/-- Finite polynomial formula for the saddle-endpoint coefficients. -/
def struveScaledCoeff (lam : ℂ) (k : ℕ) : ℂ :=
  (∑ j ∈ Finset.range (k+1), if k ≤ 2*j then
    ((2*j).factorial:ℂ)/(j.factorial:ℂ) *
      (∏ r ∈ Finset.range j, (Polynomial.X-Polynomial.C (1/2+r:ℂ))).coeff (2*j-k) /
      lam^(2*j) else 0) / (k.factorial:ℂ)

section StruveLOScaled

open Polynomial Metric

/-- The polynomial `∏_{r<j} (X - (1/2 + r))` of `struveScaledCoeff`. -/
noncomputable def struveLO_P (j : ℕ) : ℂ[X] :=
  ∏ r ∈ Finset.range j, (Polynomial.X - Polynomial.C (1/2 + r : ℂ))

/-- `deg P_j ≤ j`. -/
theorem struveLO_natDegree_P (j : ℕ) : (struveLO_P j).natDegree ≤ j := by
  rw [struveLO_P, natDegree_prod_of_monic _ _ (fun r _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one, le_refl]

/-- `(ν - 1/2 choose j) = P_j(ν)/j!`. -/
theorem struveLO_b_eq_eval (ν : ℂ) (j : ℕ) :
    struveLO_b (ν - 1/2) j = (struveLO_P j).eval ν / (j.factorial : ℂ) := by
  unfold struveLO_b struveLO_P
  rw [eval_prod]
  congr 1
  refine Finset.prod_congr rfl fun r _ => ?_
  simp only [eval_sub, eval_X, eval_C]
  ring

/-- The polynomial in `w = 1/ν` collecting the binomial terms. -/
noncomputable def struveLO_Q (μ : ℂ) (N : ℕ) : ℂ[X] :=
  ∑ j ∈ Finset.range N, C (((2 * j).factorial : ℂ) / ((j.factorial : ℂ) * μ ^ (2 * j))) *
    reflect (2 * j) (struveLO_P j)

/-- At `w = 1/ν`, `Q` is the sum of the binomial terms `(ν-1/2 choose j) (2j)!/(μν)^{2j}`. -/
theorem struveLO_eval_Q (μ : ℂ) (N : ℕ) {ν : ℂ} (hν : ν ≠ 0) :
    (struveLO_Q μ N).eval ν⁻¹ = ∑ j ∈ Finset.range N,
      struveLO_b (ν - 1/2) j * ((2 * j).factorial : ℂ) / (μ * ν) ^ (2 * j) := by
  unfold struveLO_Q
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  let _ : Invertible ν := invertibleOfNonzero hν
  have h := eval₂_reflect_mul_pow (RingHom.id ℂ) ν (2 * j) (struveLO_P j)
    ((struveLO_natDegree_P j).trans (by omega))
  rw [invOf_eq_inv] at h
  have h' : (reflect (2 * j) (struveLO_P j)).eval ν⁻¹ = (struveLO_P j).eval ν / ν ^ (2 * j) := by
    rw [eq_div_iff (pow_ne_zero _ hν)]; exact h
  rw [eval_mul, eval_C, h', struveLO_b_eq_eval]
  have : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  rw [mul_pow]
  field_simp

/-- The coefficients of `Q` below degree `N` are `k! c_k(μ)` of DLMF 11.6.8. -/
theorem struveLO_coeff_Q (μ : ℂ) {N k : ℕ} (hk : k < N) :
    (struveLO_Q μ N).coeff k = (k.factorial : ℂ) * struveScaledCoeff μ k := by
  have hkf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  unfold struveLO_Q struveScaledCoeff
  rw [finsetSum_coeff, mul_div_cancel₀ _ hkf]
  set f : ℕ → ℂ := fun j => (C (((2 * j).factorial : ℂ) / ((j.factorial : ℂ) * μ ^ (2 * j))) *
    reflect (2 * j) (struveLO_P j)).coeff k with hf
  have hf0 : ∀ j, k < j → f j = 0 := by
    intro j hj
    simp only [hf, coeff_C_mul, coeff_reflect]
    rw [revAt_le (by omega)]
    rw [coeff_eq_zero_of_natDegree_lt ((struveLO_natDegree_P j).trans_lt (by omega)), mul_zero]
  have hfe : ∀ j, f j = if k ≤ 2 * j then ((2 * j).factorial : ℂ) / (j.factorial : ℂ) *
      (∏ r ∈ Finset.range j, (Polynomial.X - Polynomial.C (1/2 + r : ℂ))).coeff (2 * j - k) /
      μ ^ (2 * j) else 0 := by
    intro j
    simp only [hf, coeff_C_mul, coeff_reflect]
    split_ifs with h
    · rw [revAt_le h, struveLO_P]
      ring
    · have hr : (revAt (2 * j)) k = k := by
        rw [← revAtFun_eq]; simp [revAtFun, h]
      rw [hr, coeff_eq_zero_of_natDegree_lt ((struveLO_natDegree_P j).trans_lt (by omega)),
        mul_zero]
  calc ∑ j ∈ Finset.range N, f j = ∑ j ∈ Finset.range (k + 1), f j := by
        refine (Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun j _ hj => ?_).symm
        simp only [Finset.mem_range, not_lt] at hj
        exact hf0 j (by omega)
    _ = _ := Finset.sum_congr rfl fun j _ => hfe j

/-- The binomial terms reproduce the coefficients of DLMF 11.6.6–11.6.7 up to `O(ν^{-N})`. -/
theorem struveLO_poly_bound (μ : ℂ) (N : ℕ) : ∃ B : ℝ, ∀ ν : ℂ, 1 ≤ ‖ν‖ →
    ‖∑ j ∈ Finset.range N, struveLO_b (ν - 1/2) j * ((2 * j).factorial : ℂ) / (μ * ν) ^ (2 * j) -
      ∑ k ∈ Finset.range N, (k.factorial : ℂ) * struveScaledCoeff μ k / ν ^ k‖ ≤
      B * ‖ν‖⁻¹ ^ N := by
  set Q := struveLO_Q μ N
  set T : ℂ[X] := ∑ k ∈ Finset.range N, C (Q.coeff k) * X ^ k with hT
  have hdvd : X ^ N ∣ Q - T := by
    rw [X_pow_dvd_iff]
    intro d hd
    rw [coeff_sub, hT, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    simp [Finset.mem_range.2 hd]
  obtain ⟨S, hS⟩ := hdvd
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    S.continuous.continuousOn
  refine ⟨B, fun ν hν => ?_⟩
  have hν0 : ν ≠ 0 := by rintro rfl; norm_num at hν
  have hw : ν⁻¹ ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall, dist_zero_right, norm_inv]; exact inv_le_one_of_one_le₀ hν
  have h1 : ∑ k ∈ Finset.range N, (k.factorial : ℂ) * struveScaledCoeff μ k / ν ^ k = T.eval ν⁻¹ := by
    rw [hT, eval_finsetSum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [eval_mul, eval_C, eval_pow, eval_X, struveLO_coeff_Q μ (Finset.mem_range.1 hk), inv_pow,
      div_eq_mul_inv]
  rw [← struveLO_eval_Q μ N hν0, h1, ← eval_sub, hS, eval_mul, eval_pow, eval_X, norm_mul,
    norm_pow, norm_inv, mul_comm]
  exact mul_le_mul_of_nonneg_right (hB _ hw) (by positivity)

/-- In the closed sector `|arg ν| ≤ π/2 - δ`, `re ν ≥ sin δ · |ν|`. -/
theorem struveLO_re_ge {ν : ℂ} {δ : ℝ} (hν : ν ≠ 0) (h : |arg ν| ≤ π / 2 - δ) (hδ : 0 < δ) :
    Real.sin δ * ‖ν‖ ≤ ν.re := by
  have hc : Real.cos (π / 2 - δ) ≤ Real.cos (arg ν) := by
    rw [← Real.cos_abs (arg ν)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) h
  rw [Real.cos_pi_div_two_sub, cos_arg hν, le_div_iff₀ (norm_pos_iff.2 hν)] at hc
  exact hc

/-- `log (z/2) = log z - log 2` for `z ≠ 0`. -/
theorem struveLO_log_div_two {z : ℂ} (hz : z ≠ 0) : log (z / 2) = log z - log 2 := by
  have h := log_mul_ofReal (1 / 2) (by norm_num) z hz
  rw [show z * ((1 / 2 : ℝ) : ℂ) = z / 2 by push_cast; ring] at h
  rw [h, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← ofReal_log (by norm_num), one_div,
    Real.log_inv]
  push_cast; ring

/-- The normalization in DLMF 11.6.6–11.6.7: `e^{(1-ν)(log z - log 2)} · 2 (z/2)^ν = z`. -/
theorem struveLO_normalize {z : ℂ} (hz : z ≠ 0) (ν : ℂ) :
    exp ((1 - ν) * (log z - log 2)) * (2 * (z / 2) ^ ν) = z := by
  have hz2 : z / 2 ≠ 0 := div_ne_zero hz two_ne_zero
  rw [cpow_def_of_ne_zero hz2, struveLO_log_div_two hz]
  have : exp ((1 - ν) * (log z - log 2)) * exp ((log z - log 2) * ν) = exp (log z - log 2) := by
    rw [← exp_add]; ring_nf
  rw [show exp ((1 - ν) * (log z - log 2)) * (2 * exp ((log z - log 2) * ν)) =
    2 * (exp ((1 - ν) * (log z - log 2)) * exp ((log z - log 2) * ν)) by ring, this,
    ← struveLO_log_div_two hz, exp_log hz2]
  ring

/-- `‖(a choose j)‖ ≤ (2|ν|)^j` for `a = ν - 1/2`, `j ≤ N ≤ |ν|`. -/
theorem struveLO_norm_b_le {ν : ℂ} {N j : ℕ} (hj : j ≤ N) (hN : (N : ℝ) ≤ ‖ν‖) :
    ‖struveLO_b (ν - 1 / 2) j‖ ≤ (2 * ‖ν‖) ^ j := by
  unfold struveLO_b
  rw [norm_div, norm_prod, Complex.norm_natCast]
  have h1 : (1 : ℝ) ≤ j.factorial := by exact_mod_cast j.factorial_pos
  calc (∏ i ∈ Finset.range j, ‖ν - 1 / 2 - i‖) / j.factorial ≤ ∏ i ∈ Finset.range j, ‖ν - 1 / 2 - i‖ :=
        div_le_self (Finset.prod_nonneg fun _ _ => norm_nonneg _) h1
    _ ≤ ∏ _i ∈ Finset.range j, 2 * ‖ν‖ :=
        Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i hi => by
          have hi : (i : ℝ) + 1 ≤ N := by
            have := Finset.mem_range.1 hi; exact_mod_cast (by omega : i + 1 ≤ N)
          calc ‖ν - 1 / 2 - i‖ ≤ ‖ν‖ + ‖(1 / 2 : ℂ) + i‖ := by
                rw [sub_sub]; exact norm_sub_le _ _
            _ ≤ ‖ν‖ + (1 / 2 + i) := by
                gcongr
                calc ‖(1 / 2 : ℂ) + i‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖(i : ℂ)‖ := norm_add_le _ _
                  _ = 1 / 2 + i := by simp
            _ ≤ 2 * ‖ν‖ := by linarith)
    _ = (2 * ‖ν‖) ^ j := by rw [Finset.prod_const, Finset.card_range]

/-- The exponentially small tail terms are `O(|ν|^{-N})`. -/
theorem struveLO_tail_term_le {x κ L : ℝ} (hx : 1 ≤ x) (hκ : 0 < κ) (hL : 0 < L) {c : ℝ}
    (hc : 2 * κ * x ≤ c) (N j : ℕ) :
    L * x * ((2 * x) ^ j * (Real.exp (-(c / 2)) * ((2 * j).factorial * (2 / c) ^ (2 * j + 1)))) ≤
      (L * 2 ^ j * (2 * j).factorial * (1 / κ) ^ (2 * j + 1) * (N + j + 1).factorial /
        κ ^ (N + j + 1)) * x⁻¹ ^ N := by
  have hx0 : 0 < x := by linarith
  have hc0 : 0 < c := by nlinarith
  have he : Real.exp (-(c / 2)) ≤ (N + j + 1).factorial / (κ * x) ^ (N + j + 1) :=
    (Real.exp_le_exp.2 (by nlinarith)).trans (struveLO_exp_neg_le (by positivity) _)
  have h2c : 2 / c ≤ 1 / κ := by
    rw [div_le_div_iff₀ hc0 hκ]; nlinarith
  calc L * x * ((2 * x) ^ j * (Real.exp (-(c / 2)) * ((2 * j).factorial * (2 / c) ^ (2 * j + 1))))
      ≤ L * x * ((2 * x) ^ j * ((N + j + 1).factorial / (κ * x) ^ (N + j + 1) *
          ((2 * j).factorial * (1 / κ) ^ (2 * j + 1)))) := by gcongr
    _ = _ := by
        rw [mul_pow, mul_pow, inv_pow]
        have : x ^ (N + j + 1) = x * x ^ j * x ^ N := by ring
        rw [this]
        field_simp

end StruveLOScaled

/-- struveK scaled asymptotic. -/
@[dlmf 11.6.E6]
theorem struveK_scaled_asymptotic {lam : ℝ} (hlam : 1 < lam) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun ν : ℂ => Real.sqrt π*Gamma (ν+1/2)*exp ((1-ν)*(log (lam*ν)-log 2))*struveK ν (lam*ν)-∑ k ∈ Finset.range N, (k.factorial:ℂ)*struveScaledCoeff (lam) k/ν^k) =O[sector (π/2-δ)] (fun ν : ℂ => ν^(-(N:ℤ))) := by
  obtain ⟨B, hB⟩ := struveLO_poly_bound (lam : ℂ) N
  set s := Real.sin δ with hs_def
  have hs : 0 < s := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  have hl1 : 0 < lam - 1 := by linarith
  have hl0 : 0 < lam := by linarith
  set C' : ℝ := lam * 2 ^ N * (2 * N).factorial / ((lam - 1) * s) ^ (2 * N + 1) with hC'
  set R : ℝ := max (max 1 N) ((N + 1) / s) with hR
  refine IsBigO.of_bound (B + C') ?_
  rw [DLMF.sector, eventually_inf_principal]
  filter_upwards [tendsto_comap.eventually (eventually_ge_atTop R)] with ν hνR hν
  obtain ⟨hν0, harg⟩ := hν
  have hre := struveLO_re_ge hν0 harg hδ
  have hR1 : 1 ≤ ‖ν‖ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hνR
  have hRN : (N : ℝ) ≤ ‖ν‖ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hνR
  have hRs : (N : ℝ) + 1 ≤ s * ‖ν‖ := by
    have h := le_trans (le_max_right _ _) hνR
    rw [div_le_iff₀ hs] at h; linarith
  have hnorm0 : 0 < ‖ν‖ := by linarith
  set z : ℂ := (lam : ℂ) * ν with hz
  set a : ℂ := ν - 1 / 2 with ha_def
  have hzre : z.re = lam * ν.re := by simp [hz]
  have hare : a.re = ν.re - 1 / 2 := by simp [ha_def]
  have ha : (N : ℝ) ≤ a.re := by rw [hare]; linarith
  have hνre : 0 < ν.re := by linarith
  have hza : a.re < z.re := by rw [hare, hzre]; nlinarith
  have hz0 : z ≠ 0 := mul_ne_zero (ofReal_ne_zero.2 hl0.ne') hν0
  have hK := struveLO_K_integral_bound N ha hza
  have hrep := DLMF.Bessel.struveK_eq_integral ν (z := z) (by rw [hzre]; positivity)
  set J := ∫ t in Ioi (0 : ℝ), exp (-z * t) * (1 + (t : ℂ) ^ 2) ^ (ν - 1 / 2) with hJ
  have hG : Gamma (ν + 1 / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hsq : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hid : Real.sqrt π * Gamma (ν + 1 / 2) * exp ((1 - ν) * (log z - log 2)) * struveK ν z =
      z * J := by
    rw [hrep]
    have hc : (Real.sqrt π : ℂ) * Gamma (ν + 1 / 2) ≠ 0 := mul_ne_zero hsq hG
    calc _ = ((Real.sqrt π : ℂ) * Gamma (ν + 1 / 2) / ((Real.sqrt π : ℂ) * Gamma (ν + 1 / 2))) *
          ((exp ((1 - ν) * (log z - log 2)) * (2 * (z / 2) ^ ν)) * J) := by ring
      _ = z * J := by rw [div_self hc, one_mul, struveLO_normalize hz0 ν]
  have hsum : z * ∑ j ∈ Finset.range N, struveLO_b a j * ((2 * j).factorial : ℂ) / z ^ (2 * j + 1) =
      ∑ j ∈ Finset.range N, struveLO_b (ν - 1/2) j * ((2 * j).factorial : ℂ) / ((lam : ℂ) * ν) ^ (2 * j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← ha_def, ← hz, pow_succ]
    field_simp
  have hP : (∏ i ∈ Finset.range N, ‖a - i‖) ≤ (2 * ‖ν‖) ^ N := by
    calc (∏ i ∈ Finset.range N, ‖a - i‖) ≤ ∏ _i ∈ Finset.range N, 2 * ‖ν‖ :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i hi => by
            have hi : (i : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.1 hi
            calc ‖a - i‖ ≤ ‖ν‖ + ‖(1 / 2 : ℂ) + i‖ := by
                  rw [ha_def, sub_sub]; exact norm_sub_le _ _
              _ ≤ ‖ν‖ + (1 / 2 + i) := by
                  gcongr
                  calc ‖(1 / 2 : ℂ) + i‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖(i : ℂ)‖ := norm_add_le _ _
                    _ = 1 / 2 + i := by simp
              _ ≤ 2 * ‖ν‖ := by linarith)
      _ = (2 * ‖ν‖) ^ N := by rw [Finset.prod_const, Finset.card_range]
  have hden : (lam - 1) * s * ‖ν‖ ≤ z.re - a.re := by rw [hzre, hare]; nlinarith
  have hpos : 0 < (lam - 1) * s * ‖ν‖ := by positivity
  have hE : ‖z‖ * ‖J - ∑ j ∈ Finset.range N, struveLO_b a j * ((2 * j).factorial : ℂ) / z ^ (2 * j + 1)‖ ≤
      C' * ‖ν‖⁻¹ ^ N := by
    have hzn : ‖z‖ = lam * ‖ν‖ := by rw [hz, norm_mul, norm_real, Real.norm_of_nonneg hl0.le]
    rw [hzn]
    calc lam * ‖ν‖ * ‖J - _‖
        ≤ lam * ‖ν‖ * ((∏ i ∈ Finset.range N, ‖a - i‖) * (2 * N).factorial /
            (z.re - a.re) ^ (2 * N + 1)) := by gcongr
      _ ≤ lam * ‖ν‖ * ((2 * ‖ν‖) ^ N * (2 * N).factorial / ((lam - 1) * s * ‖ν‖) ^ (2 * N + 1)) := by
          gcongr
      _ = C' * ‖ν‖⁻¹ ^ N := by
          have hx : ‖ν‖ ^ (2 * N + 1) = ‖ν‖ * ‖ν‖ ^ N * ‖ν‖ ^ N := by ring
          have hn0 : ‖ν‖ ≠ 0 := hnorm0.ne'
          rw [hC', mul_pow ((lam - 1) * s) ‖ν‖, hx, mul_pow 2 ‖ν‖, inv_pow]
          field_simp
  rw [hid]
  have hsplit : z * J - ∑ k ∈ Finset.range N, (k.factorial : ℂ) * struveScaledCoeff lam k / ν ^ k =
      (∑ j ∈ Finset.range N, struveLO_b (ν - 1/2) j * ((2 * j).factorial : ℂ) / ((lam : ℂ) * ν) ^ (2 * j) -
        ∑ k ∈ Finset.range N, (k.factorial : ℂ) * struveScaledCoeff lam k / ν ^ k) +
      z * (J - ∑ j ∈ Finset.range N, struveLO_b a j * ((2 * j).factorial : ℂ) / z ^ (2 * j + 1)) := by
    rw [mul_sub, hsum]; ring
  rw [hsplit, norm_zpow, zpow_neg, zpow_natCast, ← inv_pow]
  calc _ ≤ ‖∑ j ∈ Finset.range N, struveLO_b (ν - 1/2) j * ((2 * j).factorial : ℂ) / ((lam : ℂ) * ν) ^ (2 * j) -
        ∑ k ∈ Finset.range N, (k.factorial : ℂ) * struveScaledCoeff lam k / ν ^ k‖ +
      ‖z‖ * ‖J - ∑ j ∈ Finset.range N, struveLO_b a j * ((2 * j).factorial : ℂ) / z ^ (2 * j + 1)‖ := by
        rw [← norm_mul]; exact norm_add_le _ _
    _ ≤ B * ‖ν‖⁻¹ ^ N + C' * ‖ν‖⁻¹ ^ N := add_le_add (hB ν hR1) hE
    _ = (B + C') * ‖ν‖⁻¹ ^ N := by ring

/-- struveM scaled asymptotic. -/
@[dlmf 11.6.E7]
theorem struveM_scaled_asymptotic {lam : ℝ} (hlam : 0 < lam) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun ν : ℂ => -Real.sqrt π*Gamma (ν+1/2)*exp ((1-ν)*(log (lam*ν)-log 2))*struveM ν (lam*ν)-∑ k ∈ Finset.range N, (k.factorial:ℂ)*struveScaledCoeff (I*lam) k/ν^k) =O[sector (π/2-δ)] (fun ν : ℂ => ν^(-(N:ℤ))) := by
  obtain ⟨B, hB⟩ := struveLO_poly_bound (I * lam : ℂ) N
  set s := Real.sin δ with hs_def
  have hs : 0 < s := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  set κ : ℝ := lam * s / 2 with hκ
  have hκ0 : 0 < κ := by positivity
  set C1 : ℝ := lam * 2 ^ N * (2 * N).factorial / (lam * s) ^ (2 * N + 1) with hC1
  set C2 : ℝ := ∑ j ∈ Finset.range N, (lam * 2 ^ j * (2 * j).factorial * (1 / κ) ^ (2 * j + 1) *
    (N + j + 1).factorial / κ ^ (N + j + 1)) with hC2
  set R : ℝ := max (max 1 N) ((N + 1) / s) with hR
  refine IsBigO.of_bound (B + C1 + C2) ?_
  rw [DLMF.sector, eventually_inf_principal]
  filter_upwards [tendsto_comap.eventually (eventually_ge_atTop R)] with ν hνR hν
  obtain ⟨hν0, harg⟩ := hν
  have hre := struveLO_re_ge hν0 harg hδ
  have hR1 : 1 ≤ ‖ν‖ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hνR
  have hRN : (N : ℝ) ≤ ‖ν‖ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hνR
  have hRs : (N : ℝ) + 1 ≤ s * ‖ν‖ := by
    have h := le_trans (le_max_right _ _) hνR
    rw [div_le_iff₀ hs] at h; linarith
  have hnorm0 : 0 < ‖ν‖ := by linarith
  set z : ℂ := (lam : ℂ) * ν with hz
  set a : ℂ := ν - 1 / 2 with ha_def
  have hzre : z.re = lam * ν.re := by simp [hz]
  have hare : a.re = ν.re - 1 / 2 := by simp [ha_def]
  have ha : (N : ℝ) ≤ a.re := by rw [hare]; linarith
  have hνre : 0 < ν.re := by linarith
  have hzpos : 0 < z.re := by rw [hzre]; positivity
  have hz0 : z ≠ 0 := mul_ne_zero (ofReal_ne_zero.2 hlam.ne') hν0
  have hK := struveLO_M_integral_bound N ha hzpos
  have hrep := struveM_integral (ν := ν) (by linarith) (z := z) (by
    rw [mem_slitPlane_iff]; left; exact hzpos)
  set J := ∫ t : ℝ in (0 : ℝ)..1, exp (-z * t) * (1 - (t : ℂ) ^ 2) ^ (ν - 1 / 2) with hJ
  have hG : Gamma (ν + 1 / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hsq : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hid : -Real.sqrt π * Gamma (ν + 1 / 2) * exp ((1 - ν) * (log z - log 2)) * struveM ν z =
      z * J := by
    rw [hrep]
    have hc : (Real.sqrt π : ℂ) * Gamma (ν + 1 / 2) ≠ 0 := mul_ne_zero hsq hG
    calc _ = ((Real.sqrt π : ℂ) * Gamma (ν + 1 / 2) / ((Real.sqrt π : ℂ) * Gamma (ν + 1 / 2))) *
          ((exp ((1 - ν) * (log z - log 2)) * (2 * (z / 2) ^ ν)) * J) := by ring
      _ = z * J := by rw [div_self hc, one_mul, struveLO_normalize hz0 ν]
  have hsum : z * ∑ j ∈ Finset.range N,
        struveLO_b a j * (-1) ^ j * ((2 * j).factorial : ℂ) / z ^ (2 * j + 1) =
      ∑ j ∈ Finset.range N, struveLO_b (ν - 1/2) j * ((2 * j).factorial : ℂ) /
        ((I * lam : ℂ) * ν) ^ (2 * j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hI : ((I * lam : ℂ) * ν) ^ (2 * j) = (-1) ^ j * z ^ (2 * j) := by
      rw [hz, mul_pow, mul_pow, mul_pow, pow_mul I, I_sq]; ring
    have hinv : ((-1 : ℂ) ^ j)⁻¹ = (-1) ^ j := by rw [← inv_pow, inv_neg, inv_one]
    rw [← ha_def, hI, div_eq_mul_inv, div_eq_mul_inv, mul_inv, hinv, pow_succ, mul_inv]
    linear_combination (struveLO_b a j * (-1) ^ j * ((2 * j).factorial : ℂ) * (z ^ (2 * j))⁻¹) *
      (mul_inv_cancel₀ hz0)
  have hcre : lam * s * ‖ν‖ ≤ z.re := by rw [hzre]; nlinarith
  have hE : ‖z‖ * ‖J - ∑ j ∈ Finset.range N,
        struveLO_b a j * (-1) ^ j * ((2 * j).factorial : ℂ) / z ^ (2 * j + 1)‖ ≤
      (C1 + C2) * ‖ν‖⁻¹ ^ N := by
    have hzn : ‖z‖ = lam * ‖ν‖ := by rw [hz, norm_mul, norm_real, Real.norm_of_nonneg hlam.le]
    rw [hzn]
    have hP : (∏ i ∈ Finset.range N, ‖a - i‖) ≤ (2 * ‖ν‖) ^ N := by
      calc (∏ i ∈ Finset.range N, ‖a - i‖) ≤ ∏ _i ∈ Finset.range N, 2 * ‖ν‖ :=
            Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i hi => by
              have hi : (i : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.1 hi
              calc ‖a - i‖ ≤ ‖ν‖ + ‖(1 / 2 : ℂ) + i‖ := by
                    rw [ha_def, sub_sub]; exact norm_sub_le _ _
                _ ≤ ‖ν‖ + (1 / 2 + i) := by
                    gcongr
                    calc ‖(1 / 2 : ℂ) + i‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖(i : ℂ)‖ := norm_add_le _ _
                      _ = 1 / 2 + i := by simp
                _ ≤ 2 * ‖ν‖ := by linarith)
        _ = (2 * ‖ν‖) ^ N := by rw [Finset.prod_const, Finset.card_range]
    have hpos : 0 < lam * s * ‖ν‖ := by positivity
    have h1 : lam * ‖ν‖ * ((∏ i ∈ Finset.range N, ‖a - i‖) * (2 * N).factorial /
        z.re ^ (2 * N + 1)) ≤ C1 * ‖ν‖⁻¹ ^ N := by
      calc lam * ‖ν‖ * ((∏ i ∈ Finset.range N, ‖a - i‖) * (2 * N).factorial / z.re ^ (2 * N + 1))
          ≤ lam * ‖ν‖ * ((2 * ‖ν‖) ^ N * (2 * N).factorial / (lam * s * ‖ν‖) ^ (2 * N + 1)) := by
            gcongr
        _ = C1 * ‖ν‖⁻¹ ^ N := by
            have hx : ‖ν‖ ^ (2 * N + 1) = ‖ν‖ * ‖ν‖ ^ N * ‖ν‖ ^ N := by ring
            have hn0 : ‖ν‖ ≠ 0 := hnorm0.ne'
            rw [hC1, mul_pow (lam * s) ‖ν‖, hx, mul_pow 2 ‖ν‖, inv_pow]
            field_simp
    have h2 : lam * ‖ν‖ * ∑ j ∈ Finset.range N, ‖struveLO_b a j‖ *
        (Real.exp (-(z.re / 2)) * ((2 * j).factorial * (2 / z.re) ^ (2 * j + 1))) ≤
        C2 * ‖ν‖⁻¹ ^ N := by
      rw [Finset.mul_sum, hC2, Finset.sum_mul]
      refine Finset.sum_le_sum fun j hj => ?_
      have hb := struveLO_norm_b_le (ν := ν) (j := j) (le_of_lt (Finset.mem_range.1 hj)) hRN
      calc lam * ‖ν‖ * (‖struveLO_b a j‖ *
            (Real.exp (-(z.re / 2)) * ((2 * j).factorial * (2 / z.re) ^ (2 * j + 1))))
          ≤ lam * ‖ν‖ * ((2 * ‖ν‖) ^ j *
            (Real.exp (-(z.re / 2)) * ((2 * j).factorial * (2 / z.re) ^ (2 * j + 1)))) := by
            gcongr
        _ ≤ _ := struveLO_tail_term_le hR1 hκ0 hlam (by rw [hκ]; linarith) N j
    calc lam * ‖ν‖ * ‖J - _‖ ≤ lam * ‖ν‖ * ((∏ i ∈ Finset.range N, ‖a - i‖) * (2 * N).factorial /
          z.re ^ (2 * N + 1) + ∑ j ∈ Finset.range N, ‖struveLO_b a j‖ *
          (Real.exp (-(z.re / 2)) * ((2 * j).factorial * (2 / z.re) ^ (2 * j + 1)))) := by gcongr
      _ ≤ C1 * ‖ν‖⁻¹ ^ N + C2 * ‖ν‖⁻¹ ^ N := by rw [mul_add]; exact add_le_add h1 h2
      _ = (C1 + C2) * ‖ν‖⁻¹ ^ N := by ring
  rw [hid]
  have hsplit : z * J - ∑ k ∈ Finset.range N, (k.factorial : ℂ) * struveScaledCoeff (I * lam) k / ν ^ k =
      (∑ j ∈ Finset.range N, struveLO_b (ν - 1/2) j * ((2 * j).factorial : ℂ) / ((I * lam : ℂ) * ν) ^ (2 * j) -
        ∑ k ∈ Finset.range N, (k.factorial : ℂ) * struveScaledCoeff (I * lam) k / ν ^ k) +
      z * (J - ∑ j ∈ Finset.range N,
        struveLO_b a j * (-1) ^ j * ((2 * j).factorial : ℂ) / z ^ (2 * j + 1)) := by
    rw [mul_sub, hsum]; ring
  rw [hsplit, norm_zpow, zpow_neg, zpow_natCast, ← inv_pow]
  calc _ ≤ _ + _ := norm_add_le _ _
    _ ≤ B * ‖ν‖⁻¹ ^ N + (C1 + C2) * ‖ν‖⁻¹ ^ N := add_le_add (hB ν hR1) (by rw [norm_mul]; exact hE)
    _ = (B + C1 + C2) * ‖ν‖⁻¹ ^ N := by ring

/-- struveScaledCoeff initial. -/
@[dlmf 11.6.E8]
theorem struveScaledCoeff_initial (lam : ℂ) (hlam : lam ≠ 0) :
    struveScaledCoeff lam 0=1 ∧ struveScaledCoeff lam 1=2/(lam:ℂ)^2 ∧ struveScaledCoeff lam 2=6/(lam:ℂ)^4-1/(2*(lam:ℂ)^2) ∧ struveScaledCoeff lam 3=20/(lam:ℂ)^6-4/(lam:ℂ)^4 ∧ struveScaledCoeff lam 4=70/(lam:ℂ)^8-45/(2*(lam:ℂ)^6)+3/(8*(lam:ℂ)^4) := by
  simp only [struveScaledCoeff, Finset.sum_range_succ, Finset.prod_range_succ,
    Finset.sum_range_zero, Finset.prod_range_zero, one_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [Nat.factorial, Polynomial.coeff_mul_X_sub_C, Polynomial.coeff_one,
      Polynomial.mul_coeff_zero, Polynomial.coeff_X] <;>
    field_simp <;> ring

/-- struveL scaled equiv. -/
@[dlmf 11.6.E9]
theorem struveL_scaled_equiv {lam : ℝ} (hlam : 0 < lam) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) :
    (fun ν : ℂ => struveL ν (lam*ν)) ~[sector (π/2-δ)] (fun ν => besselI ν (lam*ν)) := by
  sorry

section BinomialRemainder

open scoped Interval

/-- The binomial remainder `(1+u)^a - ∑_{k<m} (a choose k) u^k`. -/
def struveBinomRem (a : ℝ) (m : ℕ) (u : ℝ) : ℝ :=
  (1 + u) ^ a - ∑ k ∈ Finset.range m, Ring.choose a k * u ^ k

/-- `(k+1) (a choose k+1) = a (a-1 choose k)`. -/
theorem succ_mul_ring_choose_succ (a : ℝ) (k : ℕ) :
    ((k : ℝ) + 1) * Ring.choose a (k + 1) = a * Ring.choose (a - 1) k := by
  have h1 := DLMF.Confluent.ring_choose_neg_eq_poch (-(a : ℂ)) (k + 1)
  have h2 := DLMF.Confluent.ring_choose_neg_eq_poch (-(a : ℂ) + 1) k
  rw [neg_neg] at h1
  rw [show -(-(a : ℂ) + 1) = (a : ℂ) - 1 by ring] at h2
  apply Complex.ofReal_injective
  push_cast
  rw [h1, h2, poch_succ_left, Nat.factorial_succ]
  push_cast
  have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  field_simp
  ring

/-- `d/du` of the binomial remainder lowers `a` and `m` by one. -/
theorem hasDerivAt_struveBinomRem (a : ℝ) (m : ℕ) {u : ℝ} (hu : -1 < u) :
    HasDerivAt (struveBinomRem a (m + 1)) (a * struveBinomRem (a - 1) m u) u := by
  have h1 : HasDerivAt (fun u : ℝ => (1 + u) ^ a) (1 * a * (1 + u) ^ (a - 1)) u :=
    ((hasDerivAt_id u).const_add 1).rpow_const (Or.inl (by simp; linarith))
  have h2 : HasDerivAt (fun u : ℝ => ∑ k ∈ Finset.range (m + 1), Ring.choose a k * u ^ k)
      (∑ k ∈ Finset.range (m + 1), Ring.choose a k * (k * u ^ (k - 1))) u :=
    HasDerivAt.fun_sum fun k _ => (hasDerivAt_pow k u).const_mul _
  convert h1.sub h2 using 1
  · funext v; rfl
  unfold struveBinomRem
  rw [Finset.sum_range_succ', mul_sub, Finset.mul_sum]
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.add_sub_cancel, Nat.cast_succ]
  rw [one_mul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, ← mul_assoc, ← succ_mul_ring_choose_succ]
  ring

/-- The binomial remainder is continuous on `[0, ∞)`. -/
theorem continuousOn_struveBinomRem (a : ℝ) (m : ℕ) : ContinuousOn (struveBinomRem a m) (Ici 0) := by
  refine ((continuousOn_const.add continuousOn_id).rpow_const fun x hx => Or.inl ?_).sub
    (by fun_prop)
  have : (0 : ℝ) ≤ x := hx
  simp; linarith

/-- The remainder after at least one term vanishes at `0`. -/
theorem struveBinomRem_succ_zero (a : ℝ) (m : ℕ) : struveBinomRem a (m + 1) 0 = 0 := by
  simp [struveBinomRem, Finset.sum_range_succ']

/-- Integral form of the binomial remainder. -/
theorem struveBinomRem_succ_eq_integral (a : ℝ) (m : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    struveBinomRem a (m + 1) u = a * ∫ s in (0 : ℝ)..u, struveBinomRem (a - 1) m s := by
  rw [← intervalIntegral.integral_const_mul]
  have hint : IntervalIntegrable (fun s => a * struveBinomRem (a - 1) m s) volume 0 u :=
    ((continuousOn_struveBinomRem (a - 1) m).mono (by
      rw [uIcc_of_le hu]; exact Icc_subset_Ici_self)).intervalIntegrable.const_mul a
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := struveBinomRem a (m + 1)) (fun s hs => ?_)
    hint, struveBinomRem_succ_zero, sub_zero]
  rw [uIcc_of_le hu] at hs
  exact hasDerivAt_struveBinomRem a m (by linarith [hs.1])

/-- Sign and size of the binomial remainder for `a ≤ m` and `u ≥ 0`. -/
theorem struveBinomRem_bound (m : ℕ) : ∀ a : ℝ, a ≤ m → ∀ u : ℝ, 0 ≤ u →
    0 ≤ Ring.choose a m * struveBinomRem a m u ∧ |struveBinomRem a m u| ≤ |Ring.choose a m| * u ^ m := by
  induction m with
  | zero =>
    intro a ha u hu
    simp only [struveBinomRem, Finset.range_zero, Finset.sum_empty, sub_zero, Ring.choose_zero_right,
      one_mul, pow_zero, abs_one, mul_one]
    have h0 : 0 ≤ (1 + u) ^ a := Real.rpow_nonneg (by linarith) _
    refine ⟨h0, ?_⟩
    rw [abs_of_nonneg h0]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by simpa using ha)
  | succ m ih =>
    intro a ha u hu
    have ih' := ih (a - 1) (by push_cast at ha; linarith)
    have hc := succ_mul_ring_choose_succ a m
    have hm1 : (0 : ℝ) < m + 1 := by positivity
    have hc' : Ring.choose a (m + 1) = a * Ring.choose (a - 1) m / (m + 1) := by
      field_simp; linarith
    have hcont := (continuousOn_struveBinomRem (a - 1) m).mono (show Icc 0 u ⊆ Ici 0 from
      Icc_subset_Ici_self)
    have hint : IntervalIntegrable (struveBinomRem (a - 1) m) volume 0 u :=
      (hcont.mono (by rw [uIcc_of_le hu])).intervalIntegrable
    rw [struveBinomRem_succ_eq_integral a m hu, hc']
    constructor
    · have : a * Ring.choose (a - 1) m / (m + 1) * (a * ∫ s in (0 : ℝ)..u, struveBinomRem (a - 1) m s)
          = a ^ 2 / (m + 1) * ∫ s in (0 : ℝ)..u, Ring.choose (a - 1) m * struveBinomRem (a - 1) m s := by
        rw [intervalIntegral.integral_const_mul]; ring
      rw [this]
      refine mul_nonneg (by positivity) (intervalIntegral.integral_nonneg hu fun s hs => ?_)
      exact (ih' s hs.1).1
    · rw [abs_mul, abs_div, abs_mul, abs_of_pos hm1]
      have hb : |∫ s in (0 : ℝ)..u, struveBinomRem (a - 1) m s| ≤
          |Ring.choose (a - 1) m| * (u ^ (m + 1) / (m + 1)) := by
        refine (intervalIntegral.abs_integral_le_integral_abs hu).trans ?_
        have hmono : ∫ s in (0 : ℝ)..u, |struveBinomRem (a - 1) m s| ≤
            ∫ s in (0 : ℝ)..u, |Ring.choose (a - 1) m| * s ^ m :=
          intervalIntegral.integral_mono_on hu hint.abs ((by fun_prop : Continuous fun s : ℝ =>
            |Ring.choose (a - 1) m| * s ^ m).intervalIntegrable _ _) fun s hs => (ih' s hs.1).2
        refine hmono.trans (le_of_eq ?_)
        rw [intervalIntegral.integral_const_mul, integral_pow]
        simp
      calc |a| * |∫ s in (0 : ℝ)..u, struveBinomRem (a - 1) m s|
          ≤ |a| * (|Ring.choose (a - 1) m| * (u ^ (m + 1) / (m + 1))) := by gcongr
        _ = _ := by ring

end BinomialRemainder

/-- First omitted term bounds the real positive-argument remainder. -/
theorem struveK_remainder_sign {ν x : ℝ} (hx : 0 < x) (m : ℕ) (hm : ν ≤ m+1/2) :
    let R := struveK ν x-∑ k ∈ Finset.range m, struveAsymptoticTerm ν x k; R.im=0 ∧ R.re*(struveAsymptoticTerm ν x m).re ≥ 0 ∧ ‖R‖ ≤ ‖struveAsymptoticTerm ν x m‖ := by
  intro R
  set a : ℝ := ν - 1 / 2 with ha
  have hxC : 0 < ((x : ℂ)).re := by simpa using hx
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  set p : ℝ := 2 * (x / 2) ^ ν / (Real.sqrt π * Real.Gamma (ν + 1 / 2)) with hpdef
  have hp : 2 * ((x : ℂ) / 2) ^ (ν : ℂ) / (Real.sqrt π * Gamma ((ν : ℂ) + 1 / 2)) = (p : ℂ) := by
    rw [show (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow (by positivity), show (ν : ℂ) + 1 / 2 = ((ν + 1 / 2 : ℝ) : ℂ) by
        push_cast; ring, Complex.Gamma_ofReal, hpdef]
    push_cast; ring
  set e : ℝ → ℝ := fun t => Real.exp (-x * t) with he
  set L : ℕ → ℝ := fun k => ((2 * k) ! : ℝ) / x ^ (2 * k + 1) with hLdef
  have hpow : ∀ (k : ℕ) (t : ℝ), 0 < t → t ^ (((2 * k + 1 : ℕ) : ℝ) - 1) = (t ^ 2) ^ k := by
    intro k t ht
    rw [show ((2 * k + 1 : ℕ) : ℝ) - 1 = ((2 * k : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, pow_mul]
  have hLint : ∀ k : ℕ, IntegrableOn (fun t => e t * (t ^ 2) ^ k) (Ioi 0) := fun k =>
    (integrableOn_exp_neg_mul_mul_rpow_sub_one (s := ((2 * k + 1 : ℕ) : ℝ)) (by positivity)
      hx).congr_fun (fun t ht => by simp only [he, hpow k t ht]) measurableSet_Ioi
  have hL : ∀ k : ℕ, ∫ t in Ioi (0 : ℝ), e t * (t ^ 2) ^ k = L k := by
    intro k
    have h := integral_exp_neg_mul_mul_rpow_sub_one (s := ((2 * k + 1 : ℕ) : ℝ))
      (by positivity) hx
    rw [show (∫ t in Ioi (0 : ℝ), e t * (t ^ 2) ^ k) = ∫ t in Ioi (0 : ℝ),
      Real.exp (-x * t) * t ^ (((2 * k + 1 : ℕ) : ℝ) - 1) from
      setIntegral_congr_fun measurableSet_Ioi (fun t ht => by simp only [he, hpow k t ht]), h, show ((2 * k + 1 : ℕ) : ℝ) = ((2 * k : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial, Real.rpow_neg hx.le, show ((2 * k : ℕ) : ℝ) + 1 =
      ((2 * k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, hLdef]
    rfl
  have hpt : ∀ t : ℝ, ((e t * (1 + t ^ 2) ^ a : ℝ) : ℂ) =
      exp (-(x : ℂ) * t) * (1 + (t : ℂ) ^ 2) ^ ((ν : ℂ) - 1 / 2) := by
    intro t
    rw [show (1 + (t : ℂ) ^ 2) = ((1 + t ^ 2 : ℝ) : ℂ) by push_cast; ring,
      show (ν : ℂ) - 1 / 2 = ((ν - 1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow (by positivity)]
    simp only [he, ha]
    push_cast
    ring_nf
  have hI0int : IntegrableOn (fun t => e t * (1 + t ^ 2) ^ a) (Ioi 0) := by
    refine (DLMF.Bessel.integrableOn_yLaplaceKernel (ν : ℂ) hxC).norm.mono'
      ((by fun_prop : Continuous fun t : ℝ => Real.exp (-x * t)).aestronglyMeasurable.mul
        (Continuous.aestronglyMeasurable (by
          exact (continuous_const.add (continuous_pow 2)).rpow_const fun t =>
            Or.inl (by simp only [Pi.add_apply]; positivity)))) ?_
    refine Eventually.of_forall fun t => le_of_eq ?_
    rw [DLMF.Bessel.yLaplaceKernel, ← hpt, Complex.norm_real]
  have hK : struveK ν x = (p : ℂ) * ((∫ t in Ioi (0 : ℝ), e t * (1 + t ^ 2) ^ a : ℝ) : ℂ) := by
    rw [DLMF.Bessel.struveK_eq_integral _ hxC, hp]
    have h := integral_complex_ofReal (f := fun t => e t * (1 + t ^ 2) ^ a)
      (μ := volume.restrict (Ioi 0))
    rw [← h]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [hpt]
  have hT : ∀ k : ℕ, struveAsymptoticTerm ν x k = ((p * (Ring.choose a k * L k) : ℝ) : ℂ) := by
    intro k
    rw [← struveK_coeff_eq (ν : ℂ) hx0 k, hp, Complex.Gamma_nat_eq_factorial,
      show (ν : ℂ) - 1 / 2 = (a : ℂ) by rw [ha]; push_cast; ring,
      ← Complex.ofReal_choose, hLdef]
    push_cast
    field_simp
  have hsumint : IntegrableOn (fun t => ∑ k ∈ Finset.range m,
      Ring.choose a k * (e t * (t ^ 2) ^ k)) (Ioi 0) :=
    integrable_finsetSum _ fun k _ => (hLint k).const_mul _
  have hJ : (∫ t in Ioi (0 : ℝ), e t * (1 + t ^ 2) ^ a) -
      ∑ k ∈ Finset.range m, Ring.choose a k * L k =
      ∫ t in Ioi (0 : ℝ), e t * struveBinomRem a m (t ^ 2) := by
    have h1 : ∑ k ∈ Finset.range m, Ring.choose a k * L k =
        ∫ t in Ioi (0 : ℝ), ∑ k ∈ Finset.range m, Ring.choose a k * (e t * (t ^ 2) ^ k) := by
      rw [integral_finsetSum _ fun k _ => (hLint k).const_mul _]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_const_mul, hL]
    rw [h1, ← integral_sub hI0int hsumint]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [struveBinomRem, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  set J := ∫ t in Ioi (0 : ℝ), e t * struveBinomRem a m (t ^ 2) with hJdef
  have hJint : IntegrableOn (fun t => e t * struveBinomRem a m (t ^ 2)) (Ioi 0) := by
    refine (hI0int.sub hsumint).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, struveBinomRem, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hR : R = ((p * J : ℝ) : ℂ) := by
    simp only [R]
    rw [hK, Finset.sum_congr rfl fun k _ => hT k, ← hJ]
    push_cast
    rw [mul_sub, Finset.mul_sum]
  have ham : a ≤ m := by rw [ha]; linarith
  have hbd := struveBinomRem_bound m a ham
  have hL0 : 0 ≤ L m := by rw [hLdef]; positivity
  refine ⟨by rw [hR, ofReal_im], ?_, ?_⟩
  · rw [hR, hT m, ofReal_re, ofReal_re]
    have hcJ : 0 ≤ Ring.choose a m * J := by
      rw [hJdef, ← integral_const_mul]
      refine setIntegral_nonneg measurableSet_Ioi fun t _ => ?_
      have := (hbd (t ^ 2) (sq_nonneg t)).1
      have he0 : 0 ≤ e t := (Real.exp_pos _).le
      nlinarith
    have : p * J * (p * (Ring.choose a m * L m)) = p ^ 2 * L m * (Ring.choose a m * J) := by ring
    rw [this]; exact mul_nonneg (mul_nonneg (sq_nonneg _) hL0) hcJ
  · rw [hR, hT m, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_mul, abs_mul, abs_mul, abs_of_nonneg hL0]
    gcongr
    rw [hJdef, ← hL m, ← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans (setIntegral_mono_on hJint.abs
      ((hLint m).const_mul _) measurableSet_Ioi fun t _ => ?_)
    rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    have := (hbd (t ^ 2) (sq_nonneg t)).2
    have he0 : 0 ≤ e t := (Real.exp_pos _).le
    calc e t * |struveBinomRem a m (t ^ 2)| ≤ e t * (|Ring.choose a m| * (t ^ 2) ^ m) :=
          mul_le_mul_of_nonneg_left this he0
      _ = _ := by ring

/-- angerF. -/
@[dlmf 11.11.E1]
def angerF (ν : ℂ) (k : ℕ) : ℂ :=
  ∏ j ∈ Finset.range k, (ν^2-(2*j+1)^2)

/-- angerG. -/
@[dlmf 11.11.E1]
def angerG (ν : ℂ) (k : ℕ) : ℂ :=
  ∏ j ∈ Finset.range k, (ν^2-(2*j+2)^2)

/-- angerFG poch. -/
@[dlmf 11.11.E1]
theorem angerFG_poch (ν : ℂ) (k : ℕ) :
    angerF ν k = (-4)^k*poch (1/2-ν/2) k*poch (1/2+ν/2) k ∧ angerG ν k = (-4)^k*poch (1-ν/2) k*poch (1+ν/2) k := by
  induction k with
  | zero => simp [angerF, angerG, poch_zero]
  | succ k ih =>
    rcases ih with ⟨ihF, ihG⟩
    have hF : angerF ν (k+1)=angerF ν k*(ν^2-(2*k+1)^2) := by
      simp [angerF, Finset.prod_range_succ]
    have hG : angerG ν (k+1)=angerG ν k*(ν^2-(2*k+2)^2) := by
      simp [angerG, Finset.prod_range_succ]
    rw [hF,hG,ihF,ihG,poch_succ,poch_succ,poch_succ,poch_succ,pow_succ]
    push_cast
    constructor <;> ring

/-- The Taylor data of the Anger kernel in terms of `F_k`, `G_k`. -/
theorem struveAs_coeffD_even_odd (ν : ℂ) (k : ℕ) :
    struveAs_coeffD ν (2 * k) = angerF ν k ∧ struveAs_coeffD ν (2 * k + 1) = -ν * angerG ν k := by
  induction k with
  | zero => simp [struveAs_coeffD, angerF, angerG]
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, show 2 * k + 2 + 1 = (2 * k + 1) + 2 by ring,
      struveAs_coeffD, struveAs_coeffD, ih.1, ih.2]
    simp only [angerF, angerG, Finset.prod_range_succ]
    push_cast
    constructor <;> ring

/-- Points of a closed sector `|arg z| ≤ π - δ` near infinity are nonzero and in the slit plane. -/
theorem struveAs_eventually_sector {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ z in sector (π - δ), z ≠ 0 ∧ z ∈ slitPlane := by
  rw [sector, eventually_inf_principal]
  refine Eventually.of_forall fun z hz => ⟨hz.1, ?_⟩
  rw [mem_slitPlane_iff_arg]
  refine ⟨fun h => ?_, hz.1⟩
  have := hz.2
  rw [h, abs_of_pos Real.pi_pos] at this
  linarith

/-- DLMF 11.11.4 in the form of an asymptotic expansion in `z^{-n-1}`. -/
theorem struveAs_angerA_sector (ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    HasAsymptoticExpansion (sector (π - δ)) (fun (n : ℕ) (z : ℂ) => z ^ (-((n : ℂ) + 1)))
      (fun n => struveAs_coeffD ν n / π) (angerA ν) := by
  have hs : 0 < Real.sin (δ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hα : |(π - δ) / 2| < π / 2 := by rw [abs_lt]; constructor <;> linarith
  have hα' : |-((π - δ) / 2)| < π / 2 := by rwa [abs_neg]
  exact ((struveAs_angerA_hasAsymptoticExpansion ν hs hα').sup
    (struveAs_angerA_hasAsymptoticExpansion ν hs hα)).mono (sector_le_sup_rotSectorAtTop hδ hδπ)

/-- Pairing consecutive terms of a finite sum. -/
theorem struveAs_sum_range_two_mul (c : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range (2 * N), c n = ∑ k ∈ Finset.range N, (c (2 * k) + c (2 * k + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    ring

/-- The paired form of the `A_ν` expansion. -/
theorem struveAs_angerA_paired (ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun z : ℂ => angerA ν z-(∑ k ∈ Finset.range N, 1/π*(angerF ν k/z^(2*k+1)-ν*angerG ν k/z^(2*k+2)))) =O[sector (π-δ)] (fun z : ℂ => z^(-(2*N+1:ℤ))) := by
  have h := struveAs_angerA_sector ν hδ hδπ (2 * N)
  refine (h.congr' ?_ ?_)
  · filter_upwards [struveAs_eventually_sector hδ] with z hz
    congr 1
    have hterm : ∀ m : ℕ, z ^ (-((m : ℂ) + 1)) • (struveAs_coeffD ν m / π) =
        1 / π * (struveAs_coeffD ν m / z ^ (m + 1)) := by
      intro m
      rw [cpow_neg, show (m : ℂ) + 1 = ((m + 1 : ℕ) : ℂ) by push_cast; ring, cpow_natCast,
        smul_eq_mul]
      field_simp
    simp_rw [hterm]
    rw [struveAs_sum_range_two_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(struveAs_coeffD_even_odd ν k).1, (struveAs_coeffD_even_odd ν k).2,
      show 2 * k + 1 + 1 = 2 * k + 2 by ring]
    ring
  · filter_upwards [struveAs_eventually_sector hδ] with z hz
    rw [cpow_neg, show ((2 * N : ℕ) : ℂ) + 1 = ((2 * N + 1 : ℕ) : ℂ) by push_cast; ring,
      cpow_natCast, zpow_neg, show ((2 * N + 1 : ℤ)) = ((2 * N + 1 : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast]

/-- angerJ large argument. -/
@[dlmf 11.11.E2]
theorem angerJ_large_argument (ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun z : ℂ => angerJ ν z-besselJ ν z-(∑ k ∈ Finset.range N, sin (π*ν)/π*(angerF ν k/z^(2*k+1)-ν*angerG ν k/z^(2*k+2)))) =O[sector (π-δ)] (fun z : ℂ => z^(-(2*N+1:ℤ))) := by
  refine ((struveAs_angerA_paired ν hδ hδπ N).const_mul_left (sin (π * ν))).congr' ?_
    EventuallyEq.rfl
  filter_upwards [struveAs_eventually_sector hδ] with z hz
  rw [anger_bessel ν hz.2, mul_sub, Finset.mul_sum]
  have : ∀ k ∈ Finset.range N, sin (π * ν) * (1 / π * (angerF ν k / z ^ (2 * k + 1) -
      ν * angerG ν k / z ^ (2 * k + 2))) = sin (π * ν) / π * (angerF ν k / z ^ (2 * k + 1) -
      ν * angerG ν k / z ^ (2 * k + 2)) := fun k _ => by ring
  rw [Finset.sum_congr rfl this]
  ring

/-- weberE large argument, DLMF 11.11.3. The sum runs over both terms of the summand; an earlier
transcription bound only the `F_k` terms, leaving an auto-bound `k` in the `G_k` term. -/
@[dlmf 11.11.E3]
theorem weberE_large_argument (ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun z : ℂ => weberE ν z+besselY ν z-(∑ k ∈ Finset.range N, (-(1+cos (π*ν))/π*angerF ν k/z^(2*k+1)-ν*(1-cos (π*ν))/π*angerG ν k/z^(2*k+2)))) =O[sector (π-δ)] (fun z : ℂ => z^(-(2*N+1:ℤ))) := by
  have h1 := (struveAs_angerA_paired ν hδ hδπ N).const_mul_left (-cos (π * ν))
  have h2 := (struveAs_angerA_paired (-ν) hδ hδπ N).neg_left
  refine (h1.add h2).congr' ?_ EventuallyEq.rfl
  filter_upwards [struveAs_eventually_sector hδ] with z hz
  have hF : ∀ k, angerF (-ν) k = angerF ν k := fun k => by simp [angerF]
  have hG : ∀ k, angerG (-ν) k = angerG ν k := fun k => by simp [angerG]
  simp only [hF, hG]
  rw [weber_bessel ν hz.2]
  have : ∑ k ∈ Finset.range N, (-(1+cos (π*ν))/π*angerF ν k/z^(2*k+1) -
      ν*(1-cos (π*ν))/π*angerG ν k/z^(2*k+2)) =
      ∑ k ∈ Finset.range N, (-cos (π * ν) * (1 / π * (angerF ν k / z ^ (2 * k + 1) -
        ν * angerG ν k / z ^ (2 * k + 2))) - 1 / π * (angerF ν k / z ^ (2 * k + 1) -
        -ν * angerG ν k / z ^ (2 * k + 2))) :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [this, Finset.sum_sub_distrib, ← Finset.mul_sum (a := -cos (π * ν))]
  set S1 := ∑ k ∈ Finset.range N, 1 / (π : ℂ) * (angerF ν k / z ^ (2 * k + 1) -
    ν * angerG ν k / z ^ (2 * k + 2))
  set S2 := ∑ k ∈ Finset.range N, 1 / (π : ℂ) * (angerF ν k / z ^ (2 * k + 1) -
    -ν * angerG ν k / z ^ (2 * k + 2))
  ring

/-- angerA large argument. -/
@[dlmf 11.11.E4]
theorem angerA_large_argument (ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun z : ℂ => angerA ν z-(∑ k ∈ Finset.range N, 1/π*(angerF ν k/z^(2*k+1)-ν*angerG ν k/z^(2*k+2)))) =O[sector (π-δ)] (fun z : ℂ => z^(-(2*N+1:ℤ))) :=
  struveAs_angerA_paired ν hδ hδπ N

/-- Large orders separated from all integers. -/
def nonintegerOrderSector (ε : ℝ) : Filter ℂ :=
  sector π ⊓ 𝓟 {ν : ℂ | ∀ n : ℤ, ε ≤ ‖ν-n‖}

/-- `Γ(a+k)⁻¹ Γ(b+k)⁻¹ ∏_{j<k} (a+j)(b+j) = Γ(a)⁻¹ Γ(b)⁻¹`, valid for all `a`, `b`. -/
theorem struveAs_recipGamma_mul_prod (a b : ℂ) (k : ℕ) :
    (Gamma (a + k))⁻¹ * (Gamma (b + k))⁻¹ * ∏ j ∈ Finset.range k, ((a + j) * (b + j)) =
      (Gamma a)⁻¹ * (Gamma b)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ha := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a + k)
    have hb := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (b + k)
    rw [Finset.prod_range_succ, ← ih, ha, hb]
    push_cast
    rw [show a + k + 1 = a + (k + 1) by ring, show b + k + 1 = b + (k + 1) by ring]
    ring

/-- The product `∏_{j<k} ((j+1)² - (ν/2)²)`. -/
def struveAs_P1 (ν : ℂ) (k : ℕ) : ℂ := ∏ j ∈ Finset.range k, (((j : ℂ) + 1) ^ 2 - (ν / 2) ^ 2)

/-- The product `∏_{j≤k} ((j+1/2)² - (ν/2)²)`. -/
def struveAs_P2 (ν : ℂ) (k : ℕ) : ℂ :=
  ∏ j ∈ Finset.range (k + 1), (((j : ℂ) + 1 / 2) ^ 2 - (ν / 2) ^ 2)

/-- Reflection: `Γ(1+x)⁻¹ Γ(1-x)⁻¹ = sin(πx)/(πx)`. -/
theorem struveAs_recipGamma_one_add_mul {x : ℂ} (hx : x ≠ 0) :
    (Gamma (x + 1))⁻¹ * (Gamma (1 - x))⁻¹ = sin (π * x) / (π * x) := by
  have h := Complex.Gamma_mul_Gamma_one_sub x
  rw [Complex.Gamma_add_one x hx]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  by_cases hs : sin (π * x) = 0
  · rw [hs, div_zero] at h
    rcases mul_eq_zero.mp h with h | h <;> simp [h, hs]
  · have hG : Gamma x ≠ 0 := fun h0 => by rw [h0, zero_mul] at h; exact (div_ne_zero hπ hs) h.symm
    have hG' : Gamma (1 - x) ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at h; exact (div_ne_zero hπ hs) h.symm
    field_simp
    rw [h, mul_comm x (π : ℂ)]
    field_simp

/-- Reflection: `Γ(1/2+x)⁻¹ Γ(1/2-x)⁻¹ = cos(πx)/π`. -/
theorem struveAs_recipGamma_half_add_mul (x : ℂ) :
    (Gamma (x + 1 / 2))⁻¹ * (Gamma (1 / 2 - x))⁻¹ = cos (π * x) / π := by
  have h := Complex.Gamma_mul_Gamma_one_sub (x + 1 / 2)
  rw [show 1 - (x + 1 / 2) = 1 / 2 - x by ring,
    show (π : ℂ) * (x + 1 / 2) = π * x + π / 2 by ring, Complex.sin_add_pi_div_two] at h
  rw [← mul_inv, h, inv_div]


theorem struveAs_P1_ne_zero {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) (k : ℕ) : struveAs_P1 ν k ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun j _ h => ?_
  have h' : ((j : ℂ) + 1 - ν / 2) * ((j : ℂ) + 1 + ν / 2) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h | h
  · exact hν (2 * j + 2) (by push_cast; linear_combination -2 * h)
  · exact hν (-(2 * j + 2)) (by push_cast; linear_combination 2 * h)

theorem struveAs_P2_ne_zero {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) (k : ℕ) : struveAs_P2 ν k ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun j _ h => ?_
  have h' : ((j : ℂ) + 1 / 2 - ν / 2) * ((j : ℂ) + 1 / 2 + ν / 2) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h | h
  · exact hν (2 * j + 1) (by push_cast; linear_combination -2 * h)
  · exact hν (-(2 * j + 1)) (by push_cast; linear_combination 2 * h)

theorem struveAs_hasSum_S1 {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) (z : ℂ) :
    HasSum (fun k : ℕ => (-1) ^ k * (z / 2) ^ (2 * k) / struveAs_P1 ν k)
      (π * (ν / 2) / sin (π * (ν / 2)) * angerS1 ν z) := by
  have hx : ν / 2 ≠ 0 := fun h => hν 0 (by push_cast; linear_combination 2 * h)
  have hs : sin (π * (ν / 2)) ≠ 0 := sin_pi_mul_ne_zero_of_not_int (not_int_half hν)
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  refine ((hasSum_angerS1 ν z).mul_left _).congr_fun fun k => ?_
  have h := struveAs_recipGamma_mul_prod (ν / 2 + 1) (1 - ν / 2) k
  rw [struveAs_recipGamma_one_add_mul hx] at h
  have hP : ∏ j ∈ Finset.range k, ((ν / 2 + 1 + j) * (1 - ν / 2 + j)) = struveAs_P1 ν k :=
    Finset.prod_congr rfl fun j _ => by ring
  rw [hP] at h
  have hP0 := struveAs_P1_ne_zero hν k
  have e : (Gamma (k + ν / 2 + 1) * Gamma (k - ν / 2 + 1))⁻¹ =
      sin (π * (ν / 2)) / (π * (ν / 2)) / struveAs_P1 ν k := by
    rw [← h, mul_inv, show ν / 2 + 1 + (k : ℂ) = k + ν / 2 + 1 by ring,
      show 1 - ν / 2 + (k : ℂ) = k - ν / 2 + 1 by ring]
    field_simp
  have e' : (-1) ^ k * (z / 2) ^ (2 * k) / (Gamma (k + ν / 2 + 1) * Gamma (k - ν / 2 + 1)) =
      (-1) ^ k * (z / 2) ^ (2 * k) * (sin (π * (ν / 2)) / (π * (ν / 2)) / struveAs_P1 ν k) := by
    rw [div_eq_mul_inv, e]
  rw [e']
  have hs' : sin (π * ν / 2) ≠ 0 := by rwa [mul_div_assoc]
  have hν0 : ν ≠ 0 := fun h0 => hx (by rw [h0, zero_div])
  field_simp

theorem struveAs_hasSum_S2 {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) (z : ℂ) :
    HasSum (fun k : ℕ => (-1) ^ k * (z / 2) ^ (2 * k + 1) / struveAs_P2 ν k)
      (π / cos (π * (ν / 2)) * angerS2 ν z) := by
  have hs : sin (π * ν) ≠ 0 := sin_pi_mul_ne_zero_of_not_int hν
  have hc : cos (π * (ν / 2)) ≠ 0 := by
    intro h; apply hs
    rw [show (π : ℂ) * ν = 2 * (π * (ν / 2)) by ring, Complex.sin_two_mul, h, mul_zero]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  refine ((hasSum_angerS2 ν z).mul_left _).congr_fun fun k => ?_
  have h := struveAs_recipGamma_mul_prod (ν / 2 + 1 / 2) (1 / 2 - ν / 2) (k + 1)
  rw [struveAs_recipGamma_half_add_mul] at h
  have hP : ∏ j ∈ Finset.range (k + 1), ((ν / 2 + 1 / 2 + j) * (1 / 2 - ν / 2 + j)) =
      struveAs_P2 ν k := Finset.prod_congr rfl fun j _ => by ring
  rw [hP] at h
  have hP0 := struveAs_P2_ne_zero hν k
  have e : (Gamma (k + ν / 2 + 3 / 2) * Gamma (k - ν / 2 + 3 / 2))⁻¹ =
      cos (π * (ν / 2)) / π / struveAs_P2 ν k := by
    rw [← h, mul_inv]
    push_cast
    rw [show ν / 2 + 1 / 2 + ((k : ℂ) + 1) = k + ν / 2 + 3 / 2 by ring,
      show 1 / 2 - ν / 2 + ((k : ℂ) + 1) = k - ν / 2 + 3 / 2 by ring]
    field_simp
  have e' : (-1) ^ k * (z / 2) ^ (2 * k + 1) /
      (Gamma (k + ν / 2 + 3 / 2) * Gamma (k - ν / 2 + 3 / 2)) =
      (-1) ^ k * (z / 2) ^ (2 * k + 1) * (cos (π * (ν / 2)) / π / struveAs_P2 ν k) := by
    rw [div_eq_mul_inv, e]
  rw [e']
  have hc' : cos (π * ν / 2) ≠ 0 := by rwa [mul_div_assoc]
  field_simp

/-- `π ν / sin(π ν) · 𝐉_ν(z)` as a pair of series rational in `ν`. -/
theorem struveAs_angerJ_scaled_eq {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) (z : ℂ) :
    π * ν / sin (π * ν) * angerJ ν z =
      π * (ν / 2) / sin (π * (ν / 2)) * angerS1 ν z +
        ν / 2 * (π / cos (π * (ν / 2)) * angerS2 ν z) := by
  have hs : sin (π * ν) ≠ 0 := sin_pi_mul_ne_zero_of_not_int hν
  have h2 : sin (π * ν) = 2 * sin (π * (ν / 2)) * cos (π * (ν / 2)) := by
    rw [show (π : ℂ) * ν = 2 * (π * (ν / 2)) by ring, Complex.sin_two_mul]
  have hs2 : sin (π * (ν / 2)) ≠ 0 := fun h => hs (by rw [h2, h]; ring)
  have hc2 : cos (π * (ν / 2)) ≠ 0 := fun h => hs (by rw [h2, h]; ring)
  rw [angerJ_series, h2, show (π : ℂ) * ν / 2 = π * (ν / 2) by ring]
  set sn := sin (π * (ν / 2))
  set cs := cos (π * (ν / 2))
  field_simp


theorem struveAs_norm_mul_ge {u v : ℂ} {e m : ℝ} (he : 0 ≤ e) (hu : e ≤ ‖u‖)
    (hv : e ≤ ‖v‖) (huv : 2 * m ≤ ‖u‖ + ‖v‖) : e * m ≤ ‖u * v‖ := by
  rw [norm_mul]
  rcases le_total ‖u‖ ‖v‖ with h | h
  · have : m ≤ ‖v‖ := by linarith
    nlinarith [norm_nonneg u]
  · have : m ≤ ‖u‖ := by linarith
    nlinarith [norm_nonneg v]

theorem struveAs_factor_ge {ν : ℂ} {ε : ℝ} (hε : 0 < ε) (hν : ∀ n : ℤ, ε ≤ ‖ν - n‖) (a : ℤ) :
    ε / 2 * ((a : ℝ) / 2) ≤ ‖((a : ℂ) / 2) ^ 2 - (ν / 2) ^ 2‖ ∨ (a : ℝ) < 0 := by
  rcases lt_or_ge (a : ℝ) 0 with h | h
  · exact Or.inr h
  left
  have hu : ε / 2 ≤ ‖(a : ℂ) / 2 - ν / 2‖ := by
    rw [show (a : ℂ) / 2 - ν / 2 = -(ν - a) / 2 by ring, norm_div, norm_neg, Complex.norm_two]
    linarith [hν a]
  have hv : ε / 2 ≤ ‖(a : ℂ) / 2 + ν / 2‖ := by
    rw [show (a : ℂ) / 2 + ν / 2 = (ν - ((-a : ℤ) : ℂ)) / 2 by push_cast; ring, norm_div,
      Complex.norm_two]
    linarith [hν (-a)]
  have huv : 2 * ((a : ℝ) / 2) ≤ ‖(a : ℂ) / 2 - ν / 2‖ + ‖(a : ℂ) / 2 + ν / 2‖ := by
    have := norm_add_le ((a : ℂ) / 2 - ν / 2) ((a : ℂ) / 2 + ν / 2)
    rw [show (a : ℂ) / 2 - ν / 2 + ((a : ℂ) / 2 + ν / 2) = ((a : ℝ) : ℂ) by push_cast; ring,
      norm_real, Real.norm_eq_abs, abs_of_nonneg h] at this
    linarith
  have := struveAs_norm_mul_ge (by linarith) hu hv huv
  rw [show ((a : ℂ) / 2 - ν / 2) * ((a : ℂ) / 2 + ν / 2) = ((a : ℂ) / 2) ^ 2 - (ν / 2) ^ 2 by
    ring] at this
  exact this

theorem struveAs_factor_ge_sq (c x : ℂ) : ‖x‖ ^ 2 - ‖c‖ ^ 2 ≤ ‖c ^ 2 - x ^ 2‖ := by
  have := norm_sub_norm_le (x ^ 2) (c ^ 2)
  rw [norm_pow, norm_pow, norm_sub_rev] at this
  exact this

theorem struveAs_P1_tail_ge {ν : ℂ} {ε : ℝ} (hε : 0 < ε) (hν : ∀ n : ℤ, ε ≤ ‖ν - n‖)
    (hx : 2 ≤ ‖ν / 2‖) (k : ℕ) :
    ‖ν / 2‖ ^ 2 / 4 * ((ε / 2) ^ k * k !) ≤ ‖struveAs_P1 ν (k + 1)‖ := by
  rw [struveAs_P1, Finset.prod_range_succ', norm_mul, norm_prod, mul_comm (‖ν / 2‖ ^ 2 / 4)]
  refine mul_le_mul ?_ ?_ (by positivity) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  rotate_left
  · have := struveAs_factor_ge_sq (((0 : ℕ) : ℂ) + 1) (ν / 2)
    simp only [Nat.cast_zero, zero_add, norm_one, one_pow] at this ⊢
    nlinarith
  · rw [show (ε / 2) ^ k * (k ! : ℝ) = ∏ i ∈ Finset.range k, (ε / 2 * ((i : ℝ) + 1)) by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
      congr 1
      rw [← Finset.prod_range_add_one_eq_factorial]; push_cast; rfl]
    refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
    rcases struveAs_factor_ge hε hν (2 * ((i + 1 : ℕ) : ℤ) + 2) with h | h
    · push_cast at h ⊢
      rw [show (2 * ((i : ℂ) + 1) + 2) / 2 = (i : ℂ) + 1 + 1 by ring] at h
      refine le_trans ?_ h
      gcongr
      linarith
    · push_cast at h; linarith

theorem struveAs_P2_tail_ge {ν : ℂ} {ε : ℝ} (hε : 0 < ε) (hν : ∀ n : ℤ, ε ≤ ‖ν - n‖)
    (hx : 2 ≤ ‖ν / 2‖) (k : ℕ) :
    (‖ν / 2‖ ^ 2 / 4) ^ 2 * ((ε / 2) ^ k * k !) ≤ ‖struveAs_P2 ν (k + 1)‖ := by
  rw [struveAs_P2, Finset.prod_range_succ', Finset.prod_range_succ', norm_mul, norm_mul,
    norm_prod]
  have h0 := struveAs_factor_ge_sq (((0 : ℕ) : ℂ) + 1 / 2) (ν / 2)
  have h1 := struveAs_factor_ge_sq ((((0 + 1 : ℕ) : ℕ) : ℂ) + 1 / 2) (ν / 2)
  have hc0 : ‖(((0 : ℕ) : ℂ) + 1 / 2)‖ = 1 / 2 := by simp
  have hc1 : ‖((((0 + 1 : ℕ) : ℕ) : ℂ) + 1 / 2)‖ = 3 / 2 := by
    rw [show (((0 + 1 : ℕ) : ℕ) : ℂ) + 1 / 2 = ((3 / 2 : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_eq_abs, abs_of_pos (by norm_num)]
  rw [hc0] at h0; rw [hc1] at h1
  have hP : (ε / 2) ^ k * (k ! : ℝ) ≤
      ∏ i ∈ Finset.range k, ‖((((i + 1 + 1 : ℕ) : ℕ) : ℂ) + 1 / 2) ^ 2 - (ν / 2) ^ 2‖ := by
    rw [show (ε / 2) ^ k * (k ! : ℝ) = ∏ i ∈ Finset.range k, (ε / 2 * ((i : ℝ) + 1)) by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
      congr 1
      rw [← Finset.prod_range_add_one_eq_factorial]; push_cast; rfl]
    refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
    rcases struveAs_factor_ge hε hν (2 * ((i + 1 + 1 : ℕ) : ℤ) + 1) with h | h
    · push_cast at h ⊢
      rw [show (2 * ((i : ℂ) + 1 + 1) + 1) / 2 = (i : ℂ) + 1 + 1 + 1 / 2 by ring] at h
      refine le_trans ?_ h
      gcongr
      linarith
    · push_cast at h; linarith
  have hx2 : 4 ≤ ‖ν / 2‖ ^ 2 := by nlinarith
  have e0 : ‖ν / 2‖ ^ 2 / 4 ≤ ‖(((0 : ℕ) : ℂ) + 1 / 2) ^ 2 - (ν / 2) ^ 2‖ := by nlinarith
  have e1 : ‖ν / 2‖ ^ 2 / 4 ≤ ‖((((0 + 1 : ℕ) : ℕ) : ℂ) + 1 / 2) ^ 2 - (ν / 2) ^ 2‖ := by
    nlinarith
  calc (‖ν / 2‖ ^ 2 / 4) ^ 2 * ((ε / 2) ^ k * k !)
      = (((ε / 2) ^ k * k !) * (‖ν / 2‖ ^ 2 / 4)) * (‖ν / 2‖ ^ 2 / 4) := by ring
    _ ≤ _ := by
      refine mul_le_mul (mul_le_mul hP e1 (by positivity) (by positivity)) e0 (by positivity)
        (by positivity)


/-- The quantitative form of DLMF 11.11.5: for `|ν| ≥ 4` at distance `≥ ε` from the integers,
`|πν/sin(πν) 𝐉_ν(z) - 1 + νz/(ν²-1)| ≤ K/|ν/2|²`. -/
theorem struveAs_angerJ_large_order_bound (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K, ∀ ν : ℂ, (∀ n : ℤ, ε ≤ ‖ν - n‖) → 2 ≤ ‖ν / 2‖ →
      ‖π * ν / sin (π * ν) * angerJ ν z - 1 + ν * z / (ν ^ 2 - 1)‖ ≤ K / ‖ν / 2‖ ^ 2 := by
  set c := ‖z / 2‖ ^ 2 * (2 / ε)
  have hE := (Real.summable_pow_div_factorial c).hasSum
  set E := ∑' k : ℕ, c ^ k / (k ! : ℝ)
  refine ⟨4 * ‖z / 2‖ ^ 2 * E + 16 * ‖z / 2‖ ^ 3 * E, fun ν hν hx => ?_⟩
  have hν' : ∀ n : ℤ, ν ≠ n := fun n h => by
    have := hν n; rw [h, sub_self, norm_zero] at this; linarith
  have hx0 : 0 < ‖ν / 2‖ := by linarith
  have hε0 : ε ≠ 0 := hε.ne'
  have h1 := struveAs_hasSum_S1 hν' z
  have h2 := struveAs_hasSum_S2 hν' z
  rw [← hasSum_nat_add_iff' 1] at h1 h2
  have e1 : struveAs_P1 ν 0 = 1 := by simp [struveAs_P1]
  have e2 : struveAs_P2 ν 0 = (1 / 2 : ℂ) ^ 2 - (ν / 2) ^ 2 := by simp [struveAs_P2]
  simp only [Finset.range_one, Finset.sum_singleton, e1, e2, pow_zero, mul_zero, div_one,
    one_mul] at h1 h2
  -- the identity
  have hP20 : ((1 / 2 : ℂ)) ^ 2 - (ν / 2) ^ 2 ≠ 0 := by
    have := struveAs_P2_ne_zero hν' 0
    simpa [struveAs_P2] using this
  have hν2 : ν ^ 2 - 1 ≠ 0 := fun h => hP20 (by linear_combination (-1 / 4 : ℂ) * h)
  have hid : π * ν / sin (π * ν) * angerJ ν z - 1 + ν * z / (ν ^ 2 - 1) =
      (π * (ν / 2) / sin (π * (ν / 2)) * angerS1 ν z - 1) +
        ν / 2 * (π / cos (π * (ν / 2)) * angerS2 ν z - (z / 2) ^ (0 + 1) /
          ((1 / 2 : ℂ) ^ 2 - (ν / 2) ^ 2)) := by
    have h1ν : 1 - ν ^ 2 ≠ 0 := fun h => hν2 (by linear_combination -h)
    rw [struveAs_angerJ_scaled_eq hν' z]
    field_simp
    ring
  rw [hid]
  -- the bounds
  have hb1 : ∀ k : ℕ, ‖(-1) ^ (k + 1) * (z / 2) ^ (2 * (k + 1)) / struveAs_P1 ν (k + 1)‖ ≤
      4 * ‖z / 2‖ ^ 2 / ‖ν / 2‖ ^ 2 * (c ^ k / k !) := by
    intro k
    have hP := struveAs_P1_tail_ge hε hν hx k
    have hpos : 0 < ‖ν / 2‖ ^ 2 / 4 * ((ε / 2) ^ k * k !) := by positivity
    rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
    calc ‖z / 2‖ ^ (2 * (k + 1)) / ‖struveAs_P1 ν (k + 1)‖
        ≤ ‖z / 2‖ ^ (2 * (k + 1)) / (‖ν / 2‖ ^ 2 / 4 * ((ε / 2) ^ k * k !)) :=
          div_le_div_of_nonneg_left (by positivity) hpos hP
      _ = _ := by
          simp only [c]
          rw [mul_pow, div_pow, div_pow]
          field_simp
          ring
  have hb2 : ∀ k : ℕ, ‖ν / 2 * ((-1) ^ (k + 1) * (z / 2) ^ (2 * (k + 1) + 1) /
      struveAs_P2 ν (k + 1))‖ ≤ 16 * ‖z / 2‖ ^ 3 / ‖ν / 2‖ ^ 2 * (c ^ k / k !) := by
    intro k
    have hP := struveAs_P2_tail_ge hε hν hx k
    have hpos : 0 < (‖ν / 2‖ ^ 2 / 4) ^ 2 * ((ε / 2) ^ k * k !) := by positivity
    rw [norm_mul (ν / 2), norm_div ((-1 : ℂ) ^ (k + 1) * (z / 2) ^ (2 * (k + 1) + 1)),
      norm_mul ((-1 : ℂ) ^ (k + 1)), norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
    calc ‖ν / 2‖ * (‖z / 2‖ ^ (2 * (k + 1) + 1) / ‖struveAs_P2 ν (k + 1)‖)
        ≤ ‖ν / 2‖ * (‖z / 2‖ ^ (2 * (k + 1) + 1) /
            ((‖ν / 2‖ ^ 2 / 4) ^ 2 * ((ε / 2) ^ k * k !))) := by
          gcongr
      _ = 16 * ‖z / 2‖ ^ 3 / ‖ν / 2‖ ^ 3 * (c ^ k / k !) := by
          have hεk : ε ^ k * ε⁻¹ ^ k = 1 := by rw [← mul_pow, mul_inv_cancel₀ hε0, one_pow]
          simp only [c]
          rw [mul_pow, div_pow, div_pow]
          field_simp
          linear_combination (-(‖z / 2‖ ^ 3 * ‖z / 2‖ ^ (k * 2) * 2 ^ k * 16)) * hεk
      _ ≤ _ := by
          have : ‖ν / 2‖ ^ 2 ≤ ‖ν / 2‖ ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
          exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by positivity)
            (by positivity) this) (by positivity)
  have n1 := h1.norm_le_of_bounded (hE.mul_left (4 * ‖z / 2‖ ^ 2 / ‖ν / 2‖ ^ 2)) hb1
  have n2 := (h2.mul_left (ν / 2)).norm_le_of_bounded
    (hE.mul_left (16 * ‖z / 2‖ ^ 3 / ‖ν / 2‖ ^ 2)) hb2
  refine (norm_add_le _ _).trans ?_
  have : 4 * ‖z / 2‖ ^ 2 / ‖ν / 2‖ ^ 2 * E + 16 * ‖z / 2‖ ^ 3 / ‖ν / 2‖ ^ 2 * E =
      (4 * ‖z / 2‖ ^ 2 * E + 16 * ‖z / 2‖ ^ 3 * E) / ‖ν / 2‖ ^ 2 := by ring
  rw [← this]
  exact add_le_add n1 n2

/-- angerJ large order. -/
@[dlmf 11.11.E5]
theorem angerJ_large_order (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (fun ν : ℂ => π*ν/sin (π*ν)*angerJ ν z-1+ν*z/(ν^2-1)) =O[nonintegerOrderSector ε] (fun ν : ℂ => ν^(-2:ℤ)) := by
  obtain ⟨K, hK⟩ := struveAs_angerJ_large_order_bound z hε
  have hev : ∀ᶠ ν : ℂ in nonintegerOrderSector ε, 4 ≤ ‖ν‖ ∧ ∀ n : ℤ, ε ≤ ‖ν - n‖ := by
    rw [nonintegerOrderSector, sector, eventually_inf_principal, eventually_inf_principal]
    exact (tendsto_comap.eventually (eventually_ge_atTop 4)).mono fun ν h4 _ hn => ⟨h4, hn⟩
  refine IsBigO.of_bound (4 * K) ?_
  filter_upwards [hev] with ν hν
  have hx : 2 ≤ ‖ν / 2‖ := by rw [norm_div, Complex.norm_two]; linarith [hν.1]
  have hν0 : 0 < ‖ν‖ := by linarith [hν.1]
  refine (hK ν hν.2 hx).trans (le_of_eq ?_)
  rw [norm_zpow, norm_div, Complex.norm_two, zpow_neg, zpow_two]
  field_simp
  ring

/-- `‖sin w‖ ≤ e^{|Im w|}`. -/
theorem struveAs_norm_sin_le (w : ℂ) : ‖sin w‖ ≤ Real.exp |w.im| := by
  have e1 : ‖exp (-w * I)‖ ≤ Real.exp |w.im| := by
    rw [norm_exp]; exact Real.exp_le_exp.2 (by simp [le_abs_self])
  have e2 : ‖exp (w * I)‖ ≤ Real.exp |w.im| := by
    rw [norm_exp]; exact Real.exp_le_exp.2 (by simp [neg_le_abs])
  rw [Complex.sin, norm_div, norm_mul, norm_I, mul_one, Complex.norm_two]
  have := norm_sub_le (exp (-w * I)) (exp (w * I))
  linarith

/-- `‖cos w‖ ≤ e^{|Im w|}`. -/
theorem struveAs_norm_cos_le (w : ℂ) : ‖cos w‖ ≤ Real.exp |w.im| := by
  have e1 : ‖exp (-w * I)‖ ≤ Real.exp |w.im| := by
    rw [norm_exp]; exact Real.exp_le_exp.2 (by simp [le_abs_self])
  have e2 : ‖exp (w * I)‖ ≤ Real.exp |w.im| := by
    rw [norm_exp]; exact Real.exp_le_exp.2 (by simp [neg_le_abs])
  rw [Complex.cos, norm_div, Complex.norm_two]
  have := norm_add_le (exp (w * I)) (exp (-w * I))
  linarith

/-- The two tail bounds behind DLMF 11.11.5 and 11.11.6: for `|ν| ≥ 4` at distance `≥ ε`
from the integers, the normalized series `πν/(2 sin(πν/2)) 𝐒₁` and `π/cos(πν/2) 𝐒₂` agree
with their leading terms up to `K/|ν/2|²`. -/
theorem struveAs_S_tail_bound (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K, ∀ ν : ℂ, (∀ n : ℤ, ε ≤ ‖ν - n‖) → 2 ≤ ‖ν / 2‖ →
      ‖π * (ν / 2) / sin (π * (ν / 2)) * angerS1 ν z - 1‖ ≤ K / ‖ν / 2‖ ^ 2 ∧
      ‖ν / 2 * (π / cos (π * (ν / 2)) * angerS2 ν z - (z / 2) ^ (0 + 1) /
          ((1 / 2 : ℂ) ^ 2 - (ν / 2) ^ 2))‖ ≤ K / ‖ν / 2‖ ^ 2 := by
  set c := ‖z / 2‖ ^ 2 * (2 / ε)
  have hE := (Real.summable_pow_div_factorial c).hasSum
  set E := ∑' k : ℕ, c ^ k / (k ! : ℝ)
  have hE0 : 0 ≤ E := tsum_nonneg fun k => by positivity
  refine ⟨4 * ‖z / 2‖ ^ 2 * E + 16 * ‖z / 2‖ ^ 3 * E, fun ν hν hx => ?_⟩
  have hν' : ∀ n : ℤ, ν ≠ n := fun n h => by
    have := hν n; rw [h, sub_self, norm_zero] at this; linarith
  have hx0 : 0 < ‖ν / 2‖ := by linarith
  have hε0 : ε ≠ 0 := hε.ne'
  have h1 := struveAs_hasSum_S1 hν' z
  have h2 := struveAs_hasSum_S2 hν' z
  rw [← hasSum_nat_add_iff' 1] at h1 h2
  have e1 : struveAs_P1 ν 0 = 1 := by simp [struveAs_P1]
  have e2 : struveAs_P2 ν 0 = (1 / 2 : ℂ) ^ 2 - (ν / 2) ^ 2 := by simp [struveAs_P2]
  simp only [Finset.range_one, Finset.sum_singleton, e1, e2, pow_zero, mul_zero, div_one,
    one_mul] at h1 h2
  have hb1 : ∀ k : ℕ, ‖(-1) ^ (k + 1) * (z / 2) ^ (2 * (k + 1)) / struveAs_P1 ν (k + 1)‖ ≤
      4 * ‖z / 2‖ ^ 2 / ‖ν / 2‖ ^ 2 * (c ^ k / k !) := by
    intro k
    have hP := struveAs_P1_tail_ge hε hν hx k
    have hpos : 0 < ‖ν / 2‖ ^ 2 / 4 * ((ε / 2) ^ k * k !) := by positivity
    rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
    calc ‖z / 2‖ ^ (2 * (k + 1)) / ‖struveAs_P1 ν (k + 1)‖
        ≤ ‖z / 2‖ ^ (2 * (k + 1)) / (‖ν / 2‖ ^ 2 / 4 * ((ε / 2) ^ k * k !)) :=
          div_le_div_of_nonneg_left (by positivity) hpos hP
      _ = _ := by
          simp only [c]
          rw [mul_pow, div_pow, div_pow]
          field_simp
          ring
  have hb2 : ∀ k : ℕ, ‖ν / 2 * ((-1) ^ (k + 1) * (z / 2) ^ (2 * (k + 1) + 1) /
      struveAs_P2 ν (k + 1))‖ ≤ 16 * ‖z / 2‖ ^ 3 / ‖ν / 2‖ ^ 2 * (c ^ k / k !) := by
    intro k
    have hP := struveAs_P2_tail_ge hε hν hx k
    have hpos : 0 < (‖ν / 2‖ ^ 2 / 4) ^ 2 * ((ε / 2) ^ k * k !) := by positivity
    rw [norm_mul (ν / 2), norm_div ((-1 : ℂ) ^ (k + 1) * (z / 2) ^ (2 * (k + 1) + 1)),
      norm_mul ((-1 : ℂ) ^ (k + 1)), norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
    calc ‖ν / 2‖ * (‖z / 2‖ ^ (2 * (k + 1) + 1) / ‖struveAs_P2 ν (k + 1)‖)
        ≤ ‖ν / 2‖ * (‖z / 2‖ ^ (2 * (k + 1) + 1) /
            ((‖ν / 2‖ ^ 2 / 4) ^ 2 * ((ε / 2) ^ k * k !))) := by
          gcongr
      _ = 16 * ‖z / 2‖ ^ 3 / ‖ν / 2‖ ^ 3 * (c ^ k / k !) := by
          have hεk : ε ^ k * ε⁻¹ ^ k = 1 := by rw [← mul_pow, mul_inv_cancel₀ hε0, one_pow]
          simp only [c]
          rw [mul_pow, div_pow, div_pow]
          field_simp
          linear_combination (-(‖z / 2‖ ^ 3 * ‖z / 2‖ ^ (k * 2) * 2 ^ k * 16)) * hεk
      _ ≤ _ := by
          have : ‖ν / 2‖ ^ 2 ≤ ‖ν / 2‖ ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
          exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by positivity)
            (by positivity) this) (by positivity)
  have n1 := h1.norm_le_of_bounded (hE.mul_left (4 * ‖z / 2‖ ^ 2 / ‖ν / 2‖ ^ 2)) hb1
  have n2 := (h2.mul_left (ν / 2)).norm_le_of_bounded
    (hE.mul_left (16 * ‖z / 2‖ ^ 3 / ‖ν / 2‖ ^ 2)) hb2
  have hA : 0 ≤ 4 * ‖z / 2‖ ^ 2 * E := by positivity
  have hB : 0 ≤ 16 * ‖z / 2‖ ^ 3 * E := by positivity
  constructor
  · refine n1.trans ?_
    rw [div_mul_eq_mul_div]
    gcongr
    linarith
  · rw [mul_sub] at n2 ⊢
    refine n2.trans ?_
    rw [div_mul_eq_mul_div]
    gcongr
    linarith

/-- weberE large order, DLMF 11.11.6 with the error term corrected for complex `ν`.

DLMF prints the error as `O(ν⁻²)`, but the remainder inherits the size of `sin²(πν/2)` and
`cos²(πν/2)`, which grow like `e^{π|Im ν|}`: at `z = 1`, `|error|·|ν|²` is about `0.5` for real
`ν` but about `10⁵⁴` at `ν = 1/2 + 40i`. The bound here is `e^{π|Im ν|} ν⁻²`, which is DLMF's
form on the real axis. -/
@[dlmf 11.11.E6 "different convention: error term e^{π|Im ν|} ν⁻², DLMF erratum"]
theorem weberE_large_order (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (fun ν : ℂ => π*ν/2*weberE ν z-(sin (π*ν/2))^2-ν*z/(ν^2-1)*(cos (π*ν/2))^2) =O[nonintegerOrderSector ε] (fun ν : ℂ => (Real.exp (π*|ν.im|) : ℂ)*ν^(-2:ℤ)) := by
  obtain ⟨K, hK⟩ := struveAs_S_tail_bound z hε
  have hev : ∀ᶠ ν : ℂ in nonintegerOrderSector ε, 4 ≤ ‖ν‖ ∧ ∀ n : ℤ, ε ≤ ‖ν - n‖ := by
    rw [nonintegerOrderSector, sector, eventually_inf_principal, eventually_inf_principal]
    exact (tendsto_comap.eventually (eventually_ge_atTop 4)).mono fun ν h4 _ hn => ⟨h4, hn⟩
  refine IsBigO.of_bound (8 * K) ?_
  filter_upwards [hev] with ν hν
  have hx : 2 ≤ ‖ν / 2‖ := by rw [norm_div, Complex.norm_two]; linarith [hν.1]
  have hν0 : 0 < ‖ν‖ := by linarith [hν.1]
  have hν' : ∀ n : ℤ, ν ≠ n := fun n h => by
    have := hν.2 n; rw [h, sub_self, norm_zero] at this; linarith
  obtain ⟨b1, b2⟩ := hK ν hν.2 hx
  have hs : sin (π * ν) ≠ 0 := sin_pi_mul_ne_zero_of_not_int hν'
  have h2 : sin (π * ν) = 2 * sin (π * (ν / 2)) * cos (π * (ν / 2)) := by
    rw [show (π : ℂ) * ν = 2 * (π * (ν / 2)) by ring, Complex.sin_two_mul]
  have hs2 : sin (π * (ν / 2)) ≠ 0 := fun h => hs (by rw [h2, h]; ring)
  have hc2 : cos (π * (ν / 2)) ≠ 0 := fun h => hs (by rw [h2, h]; ring)
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hP20 : ((1 / 2 : ℂ)) ^ 2 - (ν / 2) ^ 2 ≠ 0 := by
    have := struveAs_P2_ne_zero hν' 0
    simpa [struveAs_P2] using this
  have hν2 : ν ^ 2 - 1 ≠ 0 := fun h => hP20 (by linear_combination (-1 / 4 : ℂ) * h)
  have hν0' : ν ≠ 0 := fun h => by rw [h] at hν0; simp at hν0
  set s := sin (π * (ν / 2)) with hsd
  set c := cos (π * (ν / 2)) with hcd
  set R1 := π * (ν / 2) / s * angerS1 ν z - 1
  set R2 := ν / 2 * (π / c * angerS2 ν z - (z / 2) ^ (0 + 1) / ((1 / 2 : ℂ) ^ 2 - (ν / 2) ^ 2))
  have hid : π*ν/2*weberE ν z-(sin (π*ν/2))^2-ν*z/(ν^2-1)*(cos (π*ν/2))^2 =
      s ^ 2 * R1 - c ^ 2 * R2 := by
    rw [weberE_series, show (π : ℂ) * ν / 2 = π * (ν / 2) by ring]
    rw [← hsd, ← hcd]
    simp only [R1, R2]
    have h1ν : 1 - ν ^ 2 ≠ 0 := fun h => hν2 (by linear_combination -h)
    clear_value s c
    field_simp
    ring
  rw [hid]
  have hsn : ‖s‖ ^ 2 ≤ Real.exp (π * |ν.im|) := by
    have := struveAs_norm_sin_le (π * (ν / 2))
    have him : |(π * (ν / 2) : ℂ).im| = π * |ν.im| / 2 := by
      simp [abs_mul, abs_of_pos Real.pi_pos, abs_div]; ring
    rw [him] at this
    calc ‖s‖ ^ 2 ≤ Real.exp (π * |ν.im| / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = _ := by rw [← Real.exp_nat_mul]; ring_nf
  have hcn : ‖c‖ ^ 2 ≤ Real.exp (π * |ν.im|) := by
    have := struveAs_norm_cos_le (π * (ν / 2))
    have him : |(π * (ν / 2) : ℂ).im| = π * |ν.im| / 2 := by
      simp [abs_mul, abs_of_pos Real.pi_pos, abs_div]; ring
    rw [him] at this
    calc ‖c‖ ^ 2 ≤ Real.exp (π * |ν.im| / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = _ := by rw [← Real.exp_nat_mul]; ring_nf
  have hK0 : 0 ≤ K := by
    have : 0 ≤ K / ‖ν / 2‖ ^ 2 := (norm_nonneg _).trans b1
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) fun h => by
      nlinarith [h.2, sq_nonneg ‖ν / 2‖]
  have hexp := Real.exp_pos (π * |ν.im|)
  calc ‖s ^ 2 * R1 - c ^ 2 * R2‖ ≤ ‖s‖ ^ 2 * ‖R1‖ + ‖c‖ ^ 2 * ‖R2‖ := by
        refine (norm_sub_le _ _).trans ?_; rw [norm_mul, norm_mul, norm_pow, norm_pow]
    _ ≤ Real.exp (π * |ν.im|) * (K / ‖ν / 2‖ ^ 2) + Real.exp (π * |ν.im|) * (K / ‖ν / 2‖ ^ 2) := by
        gcongr
    _ = 8 * K * ‖((Real.exp (π*|ν.im|) : ℝ) : ℂ) * ν ^ (-2:ℤ)‖ := by
        rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hexp, norm_zpow, norm_div,
          Complex.norm_two, zpow_neg, zpow_two]
        field_simp
        ring

/-- One integration by parts against `e^{ωθ}` on `[0, π]`. -/
theorem integral_exp_mul_ibp {ω : ℂ} (hω : ω ≠ 0) {H H' : ℝ → ℂ}
    (hd : ∀ θ, HasDerivAt H (H' θ) θ) (hc : Continuous H') :
    (∫ θ : ℝ in 0..π, exp (ω*θ) * H θ) =
      (exp (ω*π) * H π - H 0)/ω - (1/ω) * ∫ θ : ℝ in 0..π, exp (ω*θ) * H' θ := by
  have hv : ∀ θ ∈ uIcc (0:ℝ) π, HasDerivAt (fun θ : ℝ => exp (ω*θ)/ω) (exp (ω*θ)) θ := by
    intro θ _
    have := (((hasDerivAt_id (θ:ℝ)).ofReal_comp.const_mul ω).cexp).div_const ω
    refine this.congr_deriv ?_
    simp only [id, ofReal_one, mul_one]; field_simp
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun θ _ => hd θ) hv
    (hc.intervalIntegrable _ _) ((by fun_prop : Continuous fun θ : ℝ => exp (ω*θ)).intervalIntegrable _ _)
  have e1 : (∫ θ : ℝ in 0..π, exp (ω*θ) * H θ) = ∫ θ : ℝ in 0..π, H θ * exp (ω*θ) :=
    intervalIntegral.integral_congr fun θ _ => by ring
  have e2 : (∫ θ : ℝ in 0..π, H' θ * (exp (ω*θ)/ω)) =
      (1/ω) * ∫ θ : ℝ in 0..π, exp (ω*θ) * H' θ := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun θ _ => by ring
  rw [e1, hibp, e2]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  ring

/-- `|∫₀^π e^{itθ} k| ≤ ∫₀^π |k|`. -/
theorem norm_integral_exp_I_mul_le (t : ℝ) (k : ℝ → ℂ) :
    ‖∫ θ : ℝ in 0..π, exp ((I*t)*θ) * k θ‖ ≤ ∫ θ : ℝ in 0..π, ‖k θ‖ := by
  refine (intervalIntegral.norm_integral_le_integral_norm Real.pi_pos.le).trans ?_
  refine le_of_eq (intervalIntegral.integral_congr fun θ _ => ?_)
  simp only [norm_mul]
  rw [show (I*t)*(θ:ℂ) = ((t*θ:ℝ):ℂ)*I by push_cast; ring, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Derivatives of `θ ↦ exp (a sin θ)`. -/
theorem hasDerivAt_exp_mul_sin (a : ℂ) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => exp (a*Real.sin θ)) (a*Real.cos θ*exp (a*Real.sin θ)) θ := by
  have := ((Real.hasDerivAt_sin θ).ofReal_comp.const_mul a).cexp
  convert this using 1; ring

theorem hasDerivAt_exp_mul_sin_one (a : ℂ) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => a*Real.cos θ*exp (a*Real.sin θ))
      ((a^2*(Real.cos θ)^2 - a*Real.sin θ)*exp (a*Real.sin θ)) θ := by
  have h1 := ((Real.hasDerivAt_cos θ).ofReal_comp.const_mul a).mul (hasDerivAt_exp_mul_sin a θ)
  convert h1 using 1; push_cast; ring

theorem hasDerivAt_exp_mul_sin_two (a : ℂ) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => (a^2*(Real.cos θ)^2 - a*Real.sin θ)*exp (a*Real.sin θ))
      ((a^3*(Real.cos θ)^3 - 3*a^2*Real.sin θ*Real.cos θ - a*Real.cos θ)*exp (a*Real.sin θ)) θ := by
  have hc := (Real.hasDerivAt_cos θ).ofReal_comp
  have hs := (Real.hasDerivAt_sin θ).ofReal_comp
  have h1 := (((hc.pow 2).const_mul (a^2)).sub (hs.const_mul a)).mul (hasDerivAt_exp_mul_sin a θ)
  convert h1 using 1
  simp only [Pi.sub_apply, Pi.pow_apply]; push_cast; ring

theorem integral_exp_mul_exp_sin_odd {ω : ℂ} (hω : ω ≠ 0) (he : exp (ω*π) = -1) (a : ℂ) :
    (∫ θ : ℝ in 0..π, exp (ω*θ) * exp (a*Real.sin θ)) = -2/ω + (1/ω^2) *
      ∫ θ : ℝ in 0..π, exp (ω*θ) * ((a^2*(Real.cos θ)^2 - a*Real.sin θ)*exp (a*Real.sin θ)) := by
  rw [integral_exp_mul_ibp hω (hasDerivAt_exp_mul_sin a) (by fun_prop),
    integral_exp_mul_ibp hω (hasDerivAt_exp_mul_sin_one a) (by fun_prop), he]
  simp only [Real.sin_pi, Real.cos_pi, Real.sin_zero, Real.cos_zero, ofReal_zero, ofReal_one,
    ofReal_neg, mul_zero, Complex.exp_zero, mul_one]
  field_simp
  ring

theorem integral_exp_mul_exp_sin_even {ω : ℂ} (hω : ω ≠ 0) (he : exp (ω*π) = 1) (a : ℂ) :
    (∫ θ : ℝ in 0..π, exp (ω*θ) * exp (a*Real.sin θ)) = 2*a/ω^2 - (1/ω^3) *
      ∫ θ : ℝ in 0..π, exp (ω*θ) * ((a^3*(Real.cos θ)^3 - 3*a^2*Real.sin θ*Real.cos θ -
        a*Real.cos θ)*exp (a*Real.sin θ)) := by
  rw [integral_exp_mul_ibp hω (hasDerivAt_exp_mul_sin a) (by fun_prop),
    integral_exp_mul_ibp hω (hasDerivAt_exp_mul_sin_one a) (by fun_prop),
    integral_exp_mul_ibp hω (hasDerivAt_exp_mul_sin_two a) (by fun_prop), he]
  simp only [Real.sin_pi, Real.cos_pi, Real.sin_zero, Real.cos_zero, ofReal_zero, ofReal_one,
    ofReal_neg, mul_zero, Complex.exp_zero, mul_one]
  field_simp
  ring

/-- The Weber function as a combination of two exponential integrals. -/
theorem weberE_eq_exp_integrals (ν z : ℂ) :
    weberE ν z = 1/π * (I/2 * ((∫ θ : ℝ in 0..π, exp ((-I*ν)*θ) * exp ((I*z)*Real.sin θ)) -
      ∫ θ : ℝ in 0..π, exp ((I*ν)*θ) * exp ((-I*z)*Real.sin θ))) := by
  unfold weberE
  congr 1
  rw [← intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [Complex.sin, ← Complex.exp_add, ← Complex.exp_add]
  ring_nf

/-- A uniform bound for an integral against `e^{itθ}`. -/
theorem norm_integral_exp_I_mul_le_const (t : ℝ) {k : ℝ → ℂ} {C : ℝ}
    (hk : ∀ θ, ‖k θ‖ ≤ C) :
    ‖∫ θ : ℝ in 0..π, exp ((I*t)*θ) * k θ‖ ≤ C * π := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := π)
    (f := fun θ : ℝ => exp ((I*t)*θ) * k θ) (C := C) (fun θ _ => by
      rw [norm_mul, show (I*t)*(θ:ℂ) = ((t*θ:ℝ):ℂ)*I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, one_mul]; exact hk θ)
  rwa [sub_zero, abs_of_pos Real.pi_pos] at this

theorem exp_I_mul_odd_mul_pi (n : ℤ) : exp ((I*(2*n+1:ℂ))*π) = -1 := by
  rw [show (I*(2*n+1:ℂ))*π = n*(2*π*I) + π*I by ring, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I, one_mul]

theorem exp_I_mul_even_mul_pi (n : ℤ) : exp ((I*(2*n:ℂ))*π) = 1 := by
  rw [show (I*(2*n:ℂ))*π = n*(2*π*I) by ring, Complex.exp_int_mul_two_pi_mul_I]

theorem exp_neg_I_mul_odd_mul_pi (n : ℤ) : exp ((-I*(2*n+1:ℂ))*π) = -1 := by
  have := exp_I_mul_odd_mul_pi (-n-1)
  rw [← this]; congr 1; push_cast; ring

theorem exp_neg_I_mul_even_mul_pi (n : ℤ) : exp ((-I*(2*n:ℂ))*π) = 1 := by
  have := exp_I_mul_even_mul_pi (-n)
  rw [← this]; congr 1; push_cast; ring

/-- `E_{2n+1}(z) = 2/((2n+1)π) + O((2n+1)^{-2})`, uniformly in `n`. -/
theorem weberE_odd_bound (z : ℂ) : ∃ M : ℝ, ∀ n : ℤ,
    ‖weberE (2*n+1) z - 2/((2*n+1:ℂ)*π)‖ ≤ M / ((2*n+1:ℝ))^2 := by
  set K : ℝ := (‖z‖^2 + ‖z‖) * Real.exp ‖z‖
  have hH2 : ∀ a : ℂ, ‖a‖ = ‖z‖ → ∀ θ : ℝ,
      ‖(a^2*(Real.cos θ)^2 - a*Real.sin θ)*exp (a*Real.sin θ)‖ ≤ K := by
    intro a ha θ
    rw [norm_mul, Complex.norm_exp]
    have hc := Real.abs_cos_le_one θ
    have hs := Real.abs_sin_le_one θ
    have h1 : ‖a^2*(Real.cos θ:ℂ)^2 - a*Real.sin θ‖ ≤ ‖z‖^2 + ‖z‖ := by
      refine (norm_sub_le _ _).trans ?_
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, ha]
      have : |Real.cos θ|^2 ≤ 1 := by nlinarith [abs_nonneg (Real.cos θ)]
      have hz := norm_nonneg z
      nlinarith [abs_nonneg (Real.sin θ)]
    have h2 : Real.exp (a*Real.sin θ).re ≤ Real.exp ‖z‖ := by
      apply Real.exp_le_exp.2
      calc (a*Real.sin θ).re ≤ ‖a*Real.sin θ‖ := re_le_norm _
        _ = ‖a‖ * |Real.sin θ| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ ‖z‖ := by rw [ha]; nlinarith [norm_nonneg z, abs_nonneg (Real.sin θ)]
    exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
  refine ⟨K * π / π, fun n => ?_⟩
  set t : ℝ := 2*n+1
  have ht : (2*n+1:ℂ) = t := by simp [t]
  have ht0 : t ≠ 0 := by
    intro h
    have h' : ((2*n+1 : ℤ) : ℝ) = 0 := by push_cast; exact h
    have : (2*n+1 : ℤ) = 0 := by exact_mod_cast h'
    omega
  have htc : (t:ℂ) ≠ 0 := ofReal_ne_zero.2 ht0
  have hω1 : -I*(2*n+1:ℂ) ≠ 0 := by rw [ht]; simp [htc]
  have hω2 : I*(2*n+1:ℂ) ≠ 0 := by rw [ht]; simp [htc]
  rw [weberE_eq_exp_integrals,
    integral_exp_mul_exp_sin_odd hω1 (exp_neg_I_mul_odd_mul_pi n),
    integral_exp_mul_exp_sin_odd hω2 (exp_I_mul_odd_mul_pi n)]
  set R1 := ∫ θ : ℝ in 0..π, exp ((-I*(2*n+1:ℂ))*θ) *
    (((I*z)^2*(Real.cos θ)^2 - (I*z)*Real.sin θ)*exp ((I*z)*Real.sin θ))
  set R2 := ∫ θ : ℝ in 0..π, exp ((I*(2*n+1:ℂ))*θ) *
    (((-I*z)^2*(Real.cos θ)^2 - (-I*z)*Real.sin θ)*exp ((-I*z)*Real.sin θ))
  have hR1 : ‖R1‖ ≤ K * π := by
    have h := norm_integral_exp_I_mul_le_const (-t) (hH2 (I*z) (by simp))
    simp only [R1]; convert h using 4; push_cast [ht]; ring_nf
  have hR2 : ‖R2‖ ≤ K * π := by
    have h := norm_integral_exp_I_mul_le_const t (hH2 (-I*z) (by simp))
    simp only [R2]; convert h using 4; push_cast [ht]; ring_nf
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have key : 1/π * (I/2 * ((-2/(-I*(2*n+1:ℂ)) + 1/(-I*(2*n+1:ℂ))^2 * R1) -
      (-2/(I*(2*n+1:ℂ)) + 1/(I*(2*n+1:ℂ))^2 * R2))) - 2/((2*n+1:ℂ)*π) =
      (I/(2*π)) * (R2 - R1) / (t:ℂ)^2 := by
    rw [ht]
    field_simp
    ring_nf
    rw [I_sq]
    ring_nf
  rw [key, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hI : ‖I/(2*(π:ℂ))‖ = 1/(2*π) := by
    rw [norm_div, Complex.norm_I, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  rw [hI]
  have hsum : ‖R2 - R1‖ ≤ 2*(K*π) := (norm_sub_le _ _).trans (by linarith)
  have ht2 : 0 < t^2 := by positivity
  rw [div_le_div_iff_of_pos_right ht2]
  calc 1/(2*π) * ‖R2 - R1‖ ≤ 1/(2*π) * (2*(K*π)) := by gcongr
    _ = K * π / π := by field_simp

/-- `|2n+1| ≥ |n|` and `|2n| ≥ |n|` in real form. -/
theorem abs_two_mul_add_ge (n : ℤ) (e : ℝ) (he : e = 0 ∨ e = 1) :
    (|n| : ℝ) ≤ |2*(n:ℝ)+e| ∨ n = 0 := by
  rcases eq_or_ne n 0 with h | h
  · exact Or.inr h
  left
  have h1 : (1:ℝ) ≤ |(n:ℝ)| := by
    have : (1:ℤ) ≤ |n| := Int.one_le_abs h
    exact_mod_cast this
  rcases he with rfl | rfl
  · rw [add_zero, abs_mul]; norm_num; linarith [abs_nonneg (n:ℝ)]
  · have := abs_sub_abs_le_abs_sub (2*(n:ℝ)) (-1)
    rw [abs_mul, abs_two, abs_neg, abs_one, sub_neg_eq_add] at this
    linarith

theorem norm_sub_sub_le_add_add (A B C : ℂ) : ‖A - B - C‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ :=
  (norm_sub_le _ _).trans (by linarith [norm_sub_le A B])

/-- `E_{2n}(z) = 2z/(π(2n)²) + O(|z| (2n)^{-3})`, uniformly in `n ≠ 0`. -/
theorem weberE_even_bound (z : ℂ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℤ, n ≠ 0 →
    ‖weberE (2*n) z - 2*z/(π*(2*n:ℂ)^2)‖ ≤ ‖z‖ * K / |(2*n:ℝ)|^3 := by
  set K0 : ℝ := (‖z‖^2 + 3*‖z‖ + 1) * Real.exp ‖z‖
  have hK0 : 0 ≤ K0 := by positivity
  have hH3 : ∀ a : ℂ, ‖a‖ = ‖z‖ → ∀ θ : ℝ,
      ‖(a^3*(Real.cos θ)^3 - 3*a^2*Real.sin θ*Real.cos θ - a*Real.cos θ)*exp (a*Real.sin θ)‖ ≤
        ‖z‖ * K0 := by
    intro a ha θ
    rw [norm_mul, Complex.norm_exp]
    have hc := Real.abs_cos_le_one θ
    have hs := Real.abs_sin_le_one θ
    have hz := norm_nonneg z
    have h1 : ‖a^3*(Real.cos θ:ℂ)^3 - 3*a^2*Real.sin θ*Real.cos θ - a*Real.cos θ‖ ≤
        ‖z‖^3 + 3*‖z‖^2 + ‖z‖ := by
      refine (norm_sub_sub_le_add_add _ _ _).trans ?_
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, ha, Complex.norm_ofNat]
      have hc3 : |Real.cos θ|^3 ≤ 1 := pow_le_one₀ (abs_nonneg _) hc
      have hsc : |Real.sin θ| * |Real.cos θ| ≤ 1 := by
        nlinarith [abs_nonneg (Real.sin θ), abs_nonneg (Real.cos θ)]
      have e1 : ‖z‖^3 * |Real.cos θ|^3 ≤ ‖z‖^3 := by
        calc _ ≤ ‖z‖^3 * 1 := by gcongr
          _ = _ := mul_one _
      have e2 : 3 * ‖z‖^2 * |Real.sin θ| * |Real.cos θ| ≤ 3*‖z‖^2 := by
        calc _ = 3 * ‖z‖^2 * (|Real.sin θ| * |Real.cos θ|) := by ring
          _ ≤ 3 * ‖z‖^2 * 1 := by gcongr
          _ = _ := mul_one _
      have e3 : ‖z‖ * |Real.cos θ| ≤ ‖z‖ := by
        calc _ ≤ ‖z‖ * 1 := by gcongr
          _ = _ := mul_one _
      linarith
    have h2 : Real.exp (a*Real.sin θ).re ≤ Real.exp ‖z‖ := by
      apply Real.exp_le_exp.2
      calc (a*Real.sin θ).re ≤ ‖a*Real.sin θ‖ := re_le_norm _
        _ = ‖a‖ * |Real.sin θ| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ ‖z‖ := by rw [ha]; nlinarith [norm_nonneg z, abs_nonneg (Real.sin θ)]
    calc _ ≤ (‖z‖^3 + 3*‖z‖^2 + ‖z‖) * Real.exp ‖z‖ :=
          mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
      _ = ‖z‖ * K0 := by simp only [K0]; ring
  refine ⟨K0, hK0, fun n hn => ?_⟩
  set t : ℝ := 2*n
  have ht : (2*n:ℂ) = t := by simp [t]
  have ht0 : t ≠ 0 := by
    intro h
    have h' : ((2*n : ℤ) : ℝ) = 0 := by push_cast; exact h
    have : (2*n : ℤ) = 0 := by exact_mod_cast h'
    omega
  have htc : (t:ℂ) ≠ 0 := ofReal_ne_zero.2 ht0
  have hω1 : -I*(2*n:ℂ) ≠ 0 := by rw [ht]; simp [htc]
  have hω2 : I*(2*n:ℂ) ≠ 0 := by rw [ht]; simp [htc]
  rw [weberE_eq_exp_integrals,
    integral_exp_mul_exp_sin_even hω1 (exp_neg_I_mul_even_mul_pi n),
    integral_exp_mul_exp_sin_even hω2 (exp_I_mul_even_mul_pi n)]
  set R1 := ∫ θ : ℝ in 0..π, exp ((-I*(2*n:ℂ))*θ) *
    (((I*z)^3*(Real.cos θ)^3 - 3*(I*z)^2*Real.sin θ*Real.cos θ - (I*z)*Real.cos θ)*
      exp ((I*z)*Real.sin θ))
  set R2 := ∫ θ : ℝ in 0..π, exp ((I*(2*n:ℂ))*θ) *
    (((-I*z)^3*(Real.cos θ)^3 - 3*(-I*z)^2*Real.sin θ*Real.cos θ - (-I*z)*Real.cos θ)*
      exp ((-I*z)*Real.sin θ))
  have hR1 : ‖R1‖ ≤ ‖z‖ * K0 * π := by
    have h := norm_integral_exp_I_mul_le_const (-t) (hH3 (I*z) (by simp))
    simp only [R1]; convert h using 4; push_cast [ht]; ring_nf
  have hR2 : ‖R2‖ ≤ ‖z‖ * K0 * π := by
    have h := norm_integral_exp_I_mul_le_const t (hH3 (-I*z) (by simp))
    simp only [R2]; convert h using 4; push_cast [ht]; ring_nf
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have key : 1/π * (I/2 * ((2*(I*z)/(-I*(2*n:ℂ))^2 - 1/(-I*(2*n:ℂ))^3 * R1) -
      (2*(-I*z)/(I*(2*n:ℂ))^2 - 1/(I*(2*n:ℂ))^3 * R2))) - 2*z/(π*(2*n:ℂ)^2) =
      -(R1 + R2) / (2*π*(t:ℂ)^3) := by
    rw [ht]
    have e1 : (-I*(t:ℂ))^2 = -(t:ℂ)^2 := by linear_combination (t:ℂ)^2 * I_sq
    have e2 : (I*(t:ℂ))^2 = -(t:ℂ)^2 := by linear_combination (t:ℂ)^2 * I_sq
    have e3 : (-I*(t:ℂ))^3 = I*(t:ℂ)^3 := by linear_combination (-I*(t:ℂ)^3) * I_sq
    have e4 : (I*(t:ℂ))^3 = -(I*(t:ℂ)^3) := by linear_combination (I*(t:ℂ)^3) * I_sq
    rw [e1, e2, e3, e4]
    field_simp
    ring_nf
    simp only [I_sq]
    ring_nf
  rw [key]
  simp only [norm_div, norm_neg, norm_mul, norm_pow, Complex.norm_real, Complex.norm_ofNat,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hsum : ‖R1 + R2‖ ≤ 2*(‖z‖ * K0 * π) := (norm_add_le _ _).trans (by linarith)
  have ht3 : 0 < |t|^3 := by positivity
  rw [div_le_div_iff₀ (by positivity) ht3]
  nlinarith [Real.pi_pos]

/-- weberE large integer 0. -/
@[dlmf 11.11.E7]
theorem weberE_large_integer_0 (z : ℂ) :
    (fun n : ℤ => weberE (2*n+0) z) ~[comap (fun n : ℤ => |n|) atTop] (fun n => 2*z/((4*(n:ℂ)^2-1)*π)) := by
  obtain ⟨K, hK, hb⟩ := weberE_even_bound z
  unfold IsEquivalent
  rw [isLittleO_iff]
  intro c hc
  obtain ⟨N, hN⟩ := exists_nat_ge (2/c + K*π/c + 1)
  have hev : ∀ᶠ n : ℤ in comap (fun n : ℤ => |n|) atTop, (N:ℤ) ≤ |n| :=
    tendsto_comap.eventually (eventually_ge_atTop (N:ℤ))
  filter_upwards [hev] with n hn
  have hnR : (N:ℝ) ≤ |(n:ℝ)| := by
    have : ((N:ℤ):ℝ) ≤ ((|n|:ℤ):ℝ) := by exact_mod_cast hn
    simpa [Int.cast_abs] using this
  have h2c : 0 ≤ 2/c := by positivity
  have hKc : 0 ≤ K*π/c := by positivity
  have hn1 : (1:ℝ) ≤ |(n:ℝ)| := by linarith
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn1; linarith
  set t : ℝ := 2*n
  set x : ℝ := |t|
  have hx : x = 2*|(n:ℝ)| := by simp only [x, t, abs_mul, abs_two]
  have hx2 : 2 ≤ x := by linarith
  have hxN : (N:ℝ) ≤ x := by linarith
  have hxc : 2/c ≤ x := by linarith
  have hxK : K*π/c ≤ x := by linarith
  have ht : (2*n:ℂ) = t := by simp [t]
  have htx : t^2 = x^2 := (sq_abs t).symm
  have hx0 : 0 < x := by linarith
  have hx21 : 0 < x^2 - 1 := by nlinarith
  rw [Pi.sub_apply, add_zero]
  set u := weberE (2*n) z
  set w : ℂ := 2*z/(π*(2*n:ℂ)^2)
  set v : ℂ := 2*z/((4*(n:ℂ)^2-1)*π)
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have htc : (t:ℂ) ≠ 0 := ofReal_ne_zero.2 fun h => by
    have : x = 0 := by simp only [x, h, abs_zero]
    linarith
  have hn4 : (4*(n:ℂ)^2-1) = ((x^2-1:ℝ):ℂ) := by
    rw [← htx]; push_cast [t]; ring
  have hn4ne : (4*(n:ℂ)^2-1) ≠ 0 := by rw [hn4]; exact ofReal_ne_zero.2 hx21.ne'
  have hwv : w - v = -(2*z) / (π*(t:ℂ)^2*((x^2-1:ℝ):ℂ)) := by
    simp only [w, v]
    rw [ht, hn4]
    have : ((x^2-1:ℝ):ℂ) = (t:ℂ)^2 - 1 := by push_cast [← htx]; ring
    have h1 : ((x^2-1:ℝ):ℂ) ≠ 0 := ofReal_ne_zero.2 hx21.ne'
    rw [this] at h1 ⊢
    field_simp
    ring
  have hnv : ‖v‖ = 2*‖z‖/((x^2-1)*π) := by
    simp only [v]
    rw [hn4, norm_div, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg hx21.le, Real.norm_of_nonneg Real.pi_pos.le]
  have hnwv : ‖w - v‖ = 2*‖z‖/(π*x^2*(x^2-1)) := by
    rw [hwv, norm_div, norm_neg, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Complex.norm_real, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hx21.le, Real.norm_of_nonneg Real.pi_pos.le, Real.norm_eq_abs]
  have huw : ‖u - w‖ ≤ ‖z‖ * K / x^3 := hb n hn0
  have htri : ‖u - v‖ ≤ ‖u - w‖ + ‖w - v‖ := by
    have := norm_add_le (u - w) (w - v); rwa [sub_add_sub_cancel] at this
  rw [hnv]
  refine htri.trans ?_
  rw [hnwv]
  have hzn := norm_nonneg z
  have e1 : K / x^3 ≤ c/((x^2-1)*π) := by
    have ha : K / x^3 ≤ c/(x^2*π) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : K*π ≤ c*x := by rwa [div_le_iff₀ hc, mul_comm x] at hxK
      nlinarith [sq_nonneg x]
    refine ha.trans (div_le_div_of_nonneg_left hc.le (by positivity) ?_)
    nlinarith [Real.pi_pos]
  have e2 : 2/(π*x^2*(x^2-1)) ≤ c/((x^2-1)*π) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 2 ≤ c*x := by rwa [div_le_iff₀ hc, mul_comm x] at hxc
    have : 2 ≤ c*x^2 := by nlinarith
    have hp : 0 < (x^2-1)*π := by positivity
    nlinarith
  refine (add_le_add huw le_rfl).trans ?_
  calc ‖z‖ * K / x^3 + 2*‖z‖/(π*x^2*(x^2-1)) = ‖z‖ * (K/x^3 + 2/(π*x^2*(x^2-1))) := by ring
    _ ≤ ‖z‖ * (c/((x^2-1)*π) + c/((x^2-1)*π)) := by gcongr
    _ = c * (2*‖z‖/((x^2-1)*π)) := by ring

/-- weberE large integer 1. -/
@[dlmf 11.11.E7]
theorem weberE_large_integer_1 (z : ℂ) :
    (fun n : ℤ => weberE (2*n+1) z) ~[comap (fun n : ℤ => |n|) atTop] (fun n => 2/((2*n+1:ℂ)*π)) := by
  obtain ⟨M, hM⟩ := weberE_odd_bound z
  unfold IsEquivalent
  rw [isLittleO_iff]
  intro c hc
  obtain ⟨N, hN⟩ := exists_nat_ge (M * π / (2*c) + 1)
  have hev : ∀ᶠ n : ℤ in comap (fun n : ℤ => |n|) atTop, (N:ℤ) ≤ |n| :=
    tendsto_comap.eventually (eventually_ge_atTop (N:ℤ))
  filter_upwards [hev] with n hn
  have hnR : (N:ℝ) ≤ |(n:ℝ)| := by
    have : ((N:ℤ):ℝ) ≤ ((|n|:ℤ):ℝ) := by exact_mod_cast hn
    simpa [Int.cast_abs] using this
  set t : ℝ := 2*n+1
  have ht : (2*n+1:ℂ) = t := by simp [t]
  have ht0 : t ≠ 0 := by
    intro h
    have h' : ((2*n+1 : ℤ) : ℝ) = 0 := by push_cast; exact h
    have : (2*n+1 : ℤ) = 0 := by exact_mod_cast h'
    omega
  have htabs : M * π / (2*c) ≤ |t| := by
    rcases abs_two_mul_add_ge n 1 (Or.inr rfl) with h | h
    · linarith
    · subst h
      simp only [Int.cast_zero, abs_zero, mul_zero, zero_add, abs_one, t] at hnR ⊢
      have : (N:ℝ) ≤ 0 := hnR
      linarith
  have htpos : 0 < |t| := abs_pos.2 ht0
  have hv : ‖(2:ℂ)/((2*n+1:ℂ)*π)‖ = 2/(|t| * π) := by
    rw [ht, norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_ofNat,
      Real.norm_eq_abs, Real.norm_of_nonneg Real.pi_pos.le]
  rw [hv, Pi.sub_apply]
  refine (hM n).trans ?_
  have hMle : M * π ≤ 2*c*|t| := by
    have := (div_le_iff₀ (by positivity : (0:ℝ) < 2*c)).1 htabs
    linarith
  rw [← sq_abs t, div_le_iff₀ (by positivity)]
  have : c * (2 / (|t| * π)) * |t|^2 = 2*c*|t|/π := by field_simp
  rw [this, le_div_iff₀ Real.pi_pos]
  linarith

/-- Coefficients in the scaled Anger–Weber expansion. -/
def angerScaledA : ℕ → ℂ → ℂ
  | 0 => fun lam => 1/(1+lam)
  | k+1 => fun lam => limUnder (𝓝[≠] lam) (fun l : ℂ => l/(1-l^2)*(l*iteratedDeriv 2 (angerScaledA k) l+deriv (angerScaledA k) l)/((2*k+1:ℂ)*(2*k+2)))

/-- Derivative of a quadratic divided by a power of `1 + l`. -/
theorem hasDerivAt_quadratic_div_pow (a b c : ℂ) (n : ℕ) {l : ℂ} (hl : 1+l ≠ 0) :
    HasDerivAt (fun l => (a*l^2+b*l+c)/(1+l)^(n+1))
      (((2*a*l+b)*(1+l)-(n+1)*(a*l^2+b*l+c))/(1+l)^(n+2)) l := by
  have hp : HasDerivAt (fun l : ℂ => a*l^2+b*l+c) (2*a*l+b) l := by
    convert (((hasDerivAt_pow 2 l).const_mul a).add ((hasDerivAt_id' l).const_mul b)).add_const c
      using 1
    simp; ring
  have hq : HasDerivAt (fun l : ℂ => (1+l)^(n+1)) ((n+1)*(1+l)^n) l := by
    convert ((hasDerivAt_id' l).const_add 1).pow (n+1) using 1
    simp
  convert hp.div hq (pow_ne_zero _ hl) using 1
  field_simp
  ring

/-- One step of the recursion for `angerScaledA`: if the `k`-th coefficient agrees with `g`
off `l = -1`, with derivatives `d`, `e`, then the removable limit defining the next
coefficient is the continuous closed form `G`. -/
theorem angerScaledA_succ_eq (k : ℕ) {g d e G : ℂ → ℂ}
    (hA : ∀ l, 1+l ≠ 0 → angerScaledA k l = g l)
    (hd : ∀ l, 1+l ≠ 0 → HasDerivAt g (d l) l)
    (he : ∀ l, 1+l ≠ 0 → HasDerivAt d (e l) l)
    (halg : ∀ l, 1+l ≠ 0 → l ≠ 1 → l/(1-l^2)*(l*e l+d l)/((2*k+1:ℂ)*(2*k+2)) = G l)
    (hG : ∀ l, 1+l ≠ 0 → ContinuousAt G l) {lam : ℂ} (hlam : 1+lam ≠ 0) :
    angerScaledA (k+1) lam = G lam := by
  have hU : IsOpen {l : ℂ | 1+l ≠ 0} := isOpen_ne_fun (by fun_prop) continuous_const
  have hAd : ∀ l, 1+l ≠ 0 → HasDerivAt (angerScaledA k) (d l) l := fun l hl =>
    (hd l hl).congr_of_eventuallyEq (by
      filter_upwards [hU.mem_nhds hl] with x hx using hA x hx)
  have hAe : ∀ l, 1+l ≠ 0 → iteratedDeriv 2 (angerScaledA k) l = e l := by
    intro l hl
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    refine ((he l hl).congr_of_eventuallyEq ?_).deriv
    filter_upwards [hU.mem_nhds hl] with x hx using (hAd x hx).deriv
  have hev : ∀ᶠ l in 𝓝[≠] lam, 1+l ≠ 0 ∧ l ≠ 1 := by
    refine Filter.Eventually.and (nhdsWithin_le_nhds (hU.mem_nhds hlam) :
      ∀ᶠ l in 𝓝[≠] lam, 1+l ≠ 0) ?_
    by_cases h1 : lam = 1
    · subst h1; exact self_mem_nhdsWithin
    · exact nhdsWithin_le_nhds (eventually_ne_nhds h1)
  show limUnder _ _ = _
  refine (((hG lam hlam).tendsto.mono_left nhdsWithin_le_nhds).congr' ?_).limUnder_eq
  filter_upwards [hev] with l hl
  rw [hAe l hl.1, (hAd l hl.1).deriv, halg l hl.1 hl.2]

/-- angerScaledA initial. -/
@[dlmf 11.11.E9]
theorem angerScaledA_initial (lam : ℂ) (h : lam ≠ -1) :
    angerScaledA 1 lam = -lam/(2*(1+lam)^4) ∧ angerScaledA 2 lam = (9*lam^2-lam)/(24*(1+lam)^7) ∧ angerScaledA 3 lam = -(225*lam^3-54*lam^2+lam)/(720*(1+lam)^10) := by
  have hlam : 1+lam ≠ 0 := fun h0 => h (by linear_combination h0)
  have hc : ∀ (a b c : ℂ) (n : ℕ) l, 1+l ≠ 0 → ContinuousAt (fun l => (a*l^2+b*l+c)/(1+l)^(n+1)) l :=
    fun a b c n l hl => (hasDerivAt_quadratic_div_pow a b c n hl).continuousAt
  have h1m : ∀ l : ℂ, 1+l ≠ 0 → l ≠ 1 → 1-l^2 ≠ 0 := fun l hl h1 => by
    have : 1-l ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
    rw [show 1-l^2 = (1-l)*(1+l) by ring]; exact mul_ne_zero this hl
  have s1 : ∀ l, 1+l ≠ 0 → angerScaledA 1 l = (0*l^2+(-1/2)*l+0)/(1+l)^(3+1) := by
    intro l hl
    refine angerScaledA_succ_eq 0 (g := fun l => (0*l^2+0*l+1)/(1+l)^(0+1))
      (d := fun l => (0*l^2+0*l+(-1))/(1+l)^(1+1)) (e := fun l => (0*l^2+0*l+2)/(1+l)^(2+1))
      (fun l hl => by simp [angerScaledA]) (fun l hl => ?_) (fun l hl => ?_) (fun l hl h1 => ?_)
      (fun l hl => hc _ _ _ _ l hl) hl
    · convert hasDerivAt_quadratic_div_pow 0 0 1 0 hl using 1; field_simp; ring
    · convert hasDerivAt_quadratic_div_pow 0 0 (-1) 1 hl using 1; field_simp; ring
    · have := h1m l hl h1; field_simp; ring
  have s2 : ∀ l, 1+l ≠ 0 → angerScaledA 2 l = ((9/24)*l^2+(-1/24)*l+0)/(1+l)^(6+1) := by
    intro l hl
    refine angerScaledA_succ_eq 1 (g := fun l => (0*l^2+(-1/2)*l+0)/(1+l)^(3+1))
      (d := fun l => (0*l^2+(3/2)*l+(-1/2))/(1+l)^(4+1))
      (e := fun l => (0*l^2+(-6)*l+4)/(1+l)^(5+1))
      s1 (fun l hl => ?_) (fun l hl => ?_) (fun l hl h1 => ?_)
      (fun l hl => hc _ _ _ _ l hl) hl
    · convert hasDerivAt_quadratic_div_pow 0 (-1/2) 0 3 hl using 1; field_simp; ring
    · convert hasDerivAt_quadratic_div_pow 0 (3/2) (-1/2) 4 hl using 1; field_simp; ring
    · have := h1m l hl h1; push_cast; field_simp; ring
  have s3 : angerScaledA 3 lam = -(225*lam^3-54*lam^2+lam)/(720*(1+lam)^10) := by
    refine angerScaledA_succ_eq 2 (g := fun l => ((9/24)*l^2+(-1/24)*l+0)/(1+l)^(6+1))
      (d := fun l => ((-45/24)*l^2+1*l+(-1/24))/(1+l)^(7+1))
      (e := fun l => ((270/24)*l^2+(-258/24)*l+(32/24))/(1+l)^(8+1))
      (G := fun l => -(225*l^3-54*l^2+l)/(720*(1+l)^10))
      s2 (fun l hl => ?_) (fun l hl => ?_) (fun l hl h1 => ?_)
      (fun l hl => ?_) hlam
    · convert hasDerivAt_quadratic_div_pow (9/24) (-1/24) 0 6 hl using 1; field_simp; ring
    · convert hasDerivAt_quadratic_div_pow (-45/24) 1 (-1/24) 7 hl using 1; field_simp; ring
    · have := h1m l hl h1; push_cast; field_simp; ring
    · exact ((by fun_prop : Continuous fun l : ℂ => -(225*l^3-54*l^2+l)).continuousAt).div
        (by fun_prop) (mul_ne_zero (by norm_num) (pow_ne_zero _ hl))
  refine ⟨?_, ?_, s3⟩
  · rw [s1 lam hlam]; field_simp; ring
  · rw [s2 lam hlam]; field_simp; ring

/-- angerA scaled 8. -/
@[dlmf 11.11.E8]
theorem angerA_scaled_8 {lam : ℝ} (hlam : 0 < lam) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun ν : ℂ => angerA (1*ν) (lam*ν)-(1:ℂ)/π*∑ k ∈ Finset.range N, ((2*k).factorial:ℂ)*angerScaledA k (1*lam)/ν^(2*k+1)) =O[sector (π-δ)] (fun ν : ℂ => ν^(-(2*N+1:ℤ))) := by
  sorry

/-- angerA scaled 10. -/
@[dlmf 11.11.E10]
theorem angerA_scaled_10 {lam : ℝ} (hlam : 1 < lam) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun ν : ℂ => angerA (-1*ν) (lam*ν)-(-1:ℂ)/π*∑ k ∈ Finset.range N, ((2*k).factorial:ℂ)*angerScaledA k (-1*lam)/ν^(2*k+1)) =O[sector (π-δ)] (fun ν : ℂ => ν^(-(2*N+1:ℤ))) := by
  sorry

/-- angerMu. -/
@[dlmf 11.11.E12]
def angerMu (lam : ℂ) : ℂ :=
  (1-lam^2)^(1/2:ℂ)-log ((1+(1-lam^2)^(1/2:ℂ))/lam)

/-- Coefficients of the saddle expansion, with existence provided by the expansion theorem. -/
def angerScaledB (lam : ℝ) (k : ℕ) : ℂ :=
  asymptoticCoeff (fun v : ℝ => ((π*v/2:ℂ)^(1/2:ℂ))*exp (v*angerMu lam)*angerA (-v) (lam*v)) k / poch (1/2) k

/-- angerA scaled saddle. -/
@[dlmf 11.11.E11]
theorem angerA_scaled_saddle {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun ν : ℂ => (π*ν/2)^(1/2:ℂ)*exp (ν*angerMu lam)*angerA (-ν) (lam*ν)-∑ k ∈ Finset.range N, poch (1/2) k*angerScaledB lam k/ν^k) =O[sector (π/2-δ)] (fun ν : ℂ => ν^(-(N:ℤ))) := by
  sorry

/-- angerScaledB initial. -/
@[dlmf 11.11.E13]
theorem angerScaledB_initial {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    angerScaledB lam 0 = (1-lam^2:ℂ)^(-1/4:ℂ) ∧ angerScaledB lam 1 = (2+3*lam^2:ℂ)/(12*(1-lam^2:ℂ)^(7/4:ℂ)) ∧ angerScaledB lam 2 = (4+300*lam^2+81*lam^4:ℂ)/(864*(1-lam^2:ℂ)^(13/4:ℂ)) := by
  sorry

section StruveScaled

open scoped Interval

/-- `re z^{1/2} ≥ 0`. -/
theorem struveSc_re_cpow_half_nonneg (z : ℂ) : 0 ≤ (z ^ (1 / 2 : ℂ)).re := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  rw [cpow_def_of_ne_zero hz, exp_re]
  refine mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩)
  · have : (log z * (1 / 2)).im = arg z / 2 := by simp [log_im, div_eq_mul_inv]
    rw [this]; linarith [neg_pi_lt_arg z]
  · have : (log z * (1 / 2)).im = arg z / 2 := by simp [log_im, div_eq_mul_inv]
    rw [this]; linarith [arg_le_pi z]

/-- `im z^{1/2} ≤ 0` when `im z ≤ 0`. -/
theorem struveSc_im_cpow_half_nonpos {z : ℂ} (hz' : z ∈ slitPlane) (h : z.im ≤ 0) :
    (z ^ (1 / 2 : ℂ)).im ≤ 0 := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  rw [cpow_def_of_ne_zero hz, exp_im]
  have him : (log z * (1 / 2)).im = arg z / 2 := by simp [log_im, div_eq_mul_inv]
  rw [him]
  refine mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le ?_
  rcases eq_or_lt_of_le h with h0 | hneg
  · -- real axis
    have hre : 0 ≤ z.re := by
      rcases mem_slitPlane_iff.1 hz' with h1 | h1
      · exact h1.le
      · exact absurd h0 h1
    rw [arg_eq_zero_iff.2 ⟨hre, h0⟩]; simp
  · have := arg_neg_iff.2 hneg
    exact Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith [neg_pi_lt_arg z])

/-- `im z^{1/2} ≥ 0` when `im z ≥ 0`. -/
theorem struveSc_im_cpow_half_nonneg {z : ℂ} (h : 0 ≤ z.im) : 0 ≤ (z ^ (1 / 2 : ℂ)).im := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  rw [cpow_def_of_ne_zero hz, exp_im]
  have him : (log z * (1 / 2)).im = arg z / 2 := by simp [log_im, div_eq_mul_inv]
  rw [him]
  refine mul_nonneg (Real.exp_pos _).le (Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_)
  · linarith [arg_nonneg_iff.2 h]
  · linarith [arg_le_pi z, Real.pi_pos]

/-- The square of the rotated point. -/
theorem struveSc_sq (r a : ℝ) : ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2 =
    ((r ^ 2 * Real.cos (2 * a) : ℝ) : ℂ) - ((r ^ 2 * Real.sin (2 * a) : ℝ) : ℂ) * I := by
  rw [mul_pow, ← exp_nat_mul, show ((2 : ℕ) : ℂ) * (((-a : ℝ) : ℂ) * I) =
    ((-(2 * a) : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    Real.cos_neg, Real.sin_neg]
  push_cast; ring

/-- `1 + w²` lies in the slit plane on the rotated ray. -/
theorem struveSc_mem_slitPlane {a : ℝ} (ha : |a| < π / 2) {r : ℝ} :
    1 + ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2 ∈ slitPlane := by
  rw [struveSc_sq, mem_slitPlane_iff]
  simp only [add_re, one_re, sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
    sub_zero, mul_one, add_im, one_im, sub_im, zero_add, zero_sub]
  by_cases hs : Real.sin (2 * a) = 0
  · left
    have h2 : |2 * a| < π := by rw [abs_mul]; norm_num; linarith
    have ha0 : 2 * a = 0 := by
      rcases Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [neg_abs_le (2 * a)])
        (by linarith [le_abs_self (2 * a)]) |>.1 hs with h; exact h
    rw [ha0, Real.cos_zero]
    nlinarith [sq_nonneg r]
  · rcases eq_or_ne r 0 with hr | hr
    · left; simp [hr]
    · right
      intro h
      have : r ^ 2 * Real.sin (2 * a) = 0 := by
        rw [mul_I_im, ofReal_re, neg_eq_zero] at h; exact h
      rcases mul_eq_zero.1 this with h1 | h1
      · exact hr (pow_eq_zero_iff two_ne_zero |>.1 h1)
      · exact hs h1


theorem struveSc_cos_pos {a : ℝ} (ha : |a| < π / 2) : 0 < Real.cos a :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le a], by linarith [le_abs_self a]⟩

/-- `re (e^{ia} (1+w²)^{1/2}) ≥ 0` on the ray `w = r e^{-ia}`. -/
theorem struveSc_re_rot_P {a : ℝ} (ha : |a| < π / 2) (r : ℝ) :
    0 ≤ (exp ((a : ℂ) * I) *
      (1 + ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (1 / 2 : ℂ)).re := by
  set u := 1 + ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2 with hu
  have hmem : u ∈ slitPlane := struveSc_mem_slitPlane ha
  have hum : u.im = -(r ^ 2 * Real.sin (2 * a)) := by
    rw [hu, struveSc_sq, add_im, sub_im, one_im, ofReal_im, mul_I_im, ofReal_re]; ring
  have hc := struveSc_cos_pos ha
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  simp only [mul_re, add_re, ofReal_re, mul_im, ofReal_im, I_re, I_im, add_im, mul_zero,
    sub_zero, mul_one, zero_add]
  have hre := struveSc_re_cpow_half_nonneg u
  rcases le_or_gt 0 a with h0 | h0
  · have hs : 0 ≤ Real.sin a := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [le_abs_self a])
    have hs2 : 0 ≤ Real.sin (2 * a) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [le_abs_self a])
    have him := struveSc_im_cpow_half_nonpos hmem (by rw [hum]; nlinarith [sq_nonneg r])
    nlinarith [mul_nonneg hc.le hre]
  · have hs : Real.sin a < 0 := Real.sin_neg_of_neg_of_neg_pi_lt h0 (by linarith [neg_abs_le a])
    have hs2 : Real.sin (2 * a) ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith [neg_abs_le a])
    have him := struveSc_im_cpow_half_nonneg (z := u) (by rw [hum]; nlinarith [sq_nonneg r])
    nlinarith [mul_nonneg hc.le hre]

/-- `re (e^{ia} (1 - (1+w²)^{-1/2})) ≥ 0` on the ray `w = r e^{-ia}`. -/
theorem struveSc_re_one_sub_q {a : ℝ} (ha : |a| < π / 2) (r : ℝ) :
    0 ≤ (exp ((a : ℂ) * I) *
      (1 - (1 + ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ)))).re := by
  set w := (r : ℂ) * exp (((-a : ℝ) : ℂ) * I) with hw
  set u := 1 + w ^ 2 with hu
  set P := u ^ (1 / 2 : ℂ) with hP
  have hmem : u ∈ slitPlane := struveSc_mem_slitPlane ha
  have hu0 : u ≠ 0 := slitPlane_ne_zero hmem
  have hP0 : P ≠ 0 := by rw [hP]; exact (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).2 hu0
  have hP2 : P ^ 2 = u := by
    rw [hP, ← cpow_nat_mul]; norm_num
  have hq : u ^ (-(1 / 2 : ℂ)) = P⁻¹ := by rw [cpow_neg]
  set ea := exp ((a : ℂ) * I) with hea
  have hc := struveSc_cos_pos ha
  set Z := ea * u + ea * P with hZ
  have hZre : (1 + r ^ 2) * Real.cos a ≤ Z.re := by
    have h1 : (ea * u).re = (1 + r ^ 2) * Real.cos a := by
      rw [hea, hu, struveSc_sq, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
      simp only [mul_re, add_re, ofReal_re, mul_im, ofReal_im, I_re, I_im, add_im, mul_zero,
        sub_zero, mul_one, zero_add, one_re, one_im, sub_re, sub_im]
      rw [Real.cos_two_mul, Real.sin_two_mul]
      linear_combination (2 * r ^ 2 * Real.cos a) * Real.sin_sq_add_cos_sq a
    have h2 := struveSc_re_rot_P ha r
    simp only [hZ, add_re]
    rw [h1]; linarith
  have hZ0 : Z ≠ 0 := by
    intro h; rw [h, zero_re] at hZre; nlinarith [sq_nonneg r]
  have hkey : ea * (1 - u ^ (-(1 / 2 : ℂ))) * Z = (r : ℂ) ^ 2 := by
    have hee : ea * ea * w ^ 2 = (r : ℂ) ^ 2 := by
      rw [hw, hea, mul_pow, ← exp_nat_mul]
      have h1 : cexp (↑a * I) * cexp (↑a * I) * cexp (((2 : ℕ) : ℂ) * (((-a : ℝ) : ℂ) * I)) = 1 := by
        rw [← exp_add, ← exp_add]; push_cast; ring_nf; exact exp_zero
      linear_combination (r : ℂ) ^ 2 * h1
    rw [hq, hZ, ← hee, show w ^ 2 = P ^ 2 - 1 by rw [hP2, hu]; ring]
    field_simp
    linear_combination ea ^ 2 * (1 - P) * hP2
  have hX : ea * (1 - u ^ (-(1 / 2 : ℂ))) = ((r ^ 2 : ℝ) : ℂ) / Z := by
    rw [eq_div_iff hZ0, hkey]; push_cast; ring
  rw [hX, div_re, ofReal_re, ofReal_im, zero_mul, zero_div, add_zero]
  exact div_nonneg (mul_nonneg (sq_nonneg r) (by nlinarith [sq_nonneg r])) (normSq_nonneg _)


/-- The phase `Ψ(w) = λ w - log (w + (1+w²)^{1/2})` of the scaled `𝐀_{-ν}(λν)` integrand. -/
noncomputable def struveSc_phase (lam : ℝ) (w : ℂ) : ℂ :=
  (lam : ℂ) * w - log (w + (1 + w ^ 2) ^ (1 / 2 : ℂ))

/-- `Ψ'(w) = λ - (1+w²)^{-1/2}`. -/
theorem struveSc_hasDerivAt_phase (lam : ℝ) {w : ℂ} (hu : 1 + w ^ 2 ∈ slitPlane)
    (hx : w + (1 + w ^ 2) ^ (1 / 2 : ℂ) ∈ slitPlane) :
    HasDerivAt (struveSc_phase lam) ((lam : ℂ) - (1 + w ^ 2) ^ (-(1 / 2 : ℂ))) w := by
  have hu0 : 1 + w ^ 2 ≠ 0 := slitPlane_ne_zero hu
  have hP0 : (1 + w ^ 2) ^ (1 / 2 : ℂ) ≠ 0 :=
    (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).2 hu0
  have hx0 : w + (1 + w ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := slitPlane_ne_zero hx
  have hP2 : ((1 + w ^ 2) ^ (1 / 2 : ℂ)) ^ 2 = 1 + w ^ 2 := by
    rw [← cpow_nat_mul]; norm_num
  have h1 : HasDerivAt (fun w : ℂ => 1 + w ^ 2) (2 * w) w := by
    simpa using ((hasDerivAt_pow 2 w).const_add 1)
  have h2 := (h1.cpow_const (c := (1 / 2 : ℂ)) hu)
  have h3 := ((hasDerivAt_id' w).fun_add h2).clog hx
  have h4 := ((hasDerivAt_id' w).const_mul (lam : ℂ)).fun_sub h3
  convert h4 using 1
  · rfl
  rw [show (1 / 2 : ℂ) - 1 = -(1 / 2) by norm_num, cpow_neg]
  field_simp
  ring

theorem struveSc_re_x_pos {a : ℝ} (ha : |a| < π / 2) {r : ℝ} (hr : 0 ≤ r) :
    0 < ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I) +
      (1 + ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (1 / 2 : ℂ)).re := by
  have h1 := struveAs_re_cpow_half_pos (struveSc_mem_slitPlane (r := r) ha)
  rw [add_re, re_ofReal_mul, exp_ofReal_mul_I_re, Real.cos_neg]
  have := struveSc_cos_pos ha
  nlinarith

/-- The phase along the rotated ray. -/
theorem struveSc_hasDerivAt_phase_ray (lam : ℝ) {a : ℝ} (ha : |a| < π / 2) {r : ℝ} (hr : 0 ≤ r) :
    HasDerivAt (fun r : ℝ => struveSc_phase lam ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)))
      (exp (((-a : ℝ) : ℂ) * I) * ((lam : ℂ) -
        (1 + ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ)))) r := by
  have hd := struveSc_hasDerivAt_phase lam (struveSc_mem_slitPlane (r := r) ha)
    (mem_slitPlane_iff.2 (Or.inl (struveSc_re_x_pos ha hr)))
  have hl : HasDerivAt (fun r : ℝ => (r : ℂ) * exp (((-a : ℝ) : ℂ) * I))
      (exp (((-a : ℝ) : ℂ) * I)) r := by
    simpa using (hasDerivAt_id r).ofReal_comp.mul_const (exp (((-a : ℝ) : ℂ) * I))
  exact (hd.comp r hl).congr_deriv (mul_comm _ _)

theorem struveSc_phase_zero (lam : ℝ) : struveSc_phase lam 0 = 0 := by
  simp [struveSc_phase]


theorem struveSc_hasDerivAt_re {f : ℝ → ℂ} {f' : ℂ} {s : ℝ} (h : HasDerivAt f f' s) :
    HasDerivAt (fun s => (f s).re) f'.re s := by
  have := reCLM.hasFDerivAt.comp_hasDerivAt s h
  convert this using 1
  · funext y; simp
  · simp

/-- **Growth of the phase.** With `ν = ρ e^{2ia}`, `re (ν Ψ(r e^{-ia})) ≥ (λ-1) cos a · ρ r`. -/
theorem struveSc_re_phase_ge {lam : ℝ} {a : ℝ} (ha : |a| < π / 2) {ρ : ℝ}
    (hρ : 0 ≤ ρ) {r : ℝ} (hr : 0 ≤ r) :
    (lam - 1) * Real.cos a * ρ * r ≤
      ((ρ : ℂ) * exp ((2 * a : ℝ) * I) *
        struveSc_phase lam ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I))).re := by
  set ν : ℂ := (ρ : ℂ) * exp ((2 * a : ℝ) * I) with hν
  set g : ℝ → ℝ := fun s => (ν * struveSc_phase lam ((s : ℂ) * exp (((-a : ℝ) : ℂ) * I))).re -
    (lam - 1) * Real.cos a * ρ * s with hg
  have hνE : ν * exp (((-a : ℝ) : ℂ) * I) = (ρ : ℂ) * exp ((a : ℂ) * I) := by
    rw [hν, mul_assoc, ← exp_add]; congr 2; push_cast; ring
  have hderiv : ∀ s : ℝ, 0 ≤ s → HasDerivAt g
      ((ν * (exp (((-a : ℝ) : ℂ) * I) * ((lam : ℂ) -
        (1 + ((s : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ))))).re -
        (lam - 1) * Real.cos a * ρ) s := by
    intro s hs
    have h1 := struveSc_hasDerivAt_re ((struveSc_hasDerivAt_phase_ray lam ha hs).const_mul ν)
    have h2 := h1.sub ((hasDerivAt_id' s).const_mul ((lam - 1) * Real.cos a * ρ))
    rw [mul_one] at h2
    exact h2
  have hmono : MonotoneOn g (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) (f' := fun s =>
      (ν * (exp (((-a : ℝ) : ℂ) * I) * ((lam : ℂ) -
        (1 + ((s : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ))))).re -
        (lam - 1) * Real.cos a * ρ) ?_ ?_ ?_
    · exact fun s hs => (hderiv s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ici] at hs ⊢
      exact (hderiv s (le_of_lt hs)).hasDerivWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      have hpos := struveSc_re_one_sub_q ha s
      rw [← mul_assoc, hνE, sub_nonneg]
      set q := (1 + ((s : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ))
      have e1 : ((ρ : ℂ) * exp ((a : ℂ) * I) * ((lam : ℂ) - q)).re =
          ρ * ((lam - 1) * Real.cos a + (exp ((a : ℂ) * I) * (1 - q)).re) := by
        have : (ρ : ℂ) * exp ((a : ℂ) * I) * ((lam : ℂ) - q) =
            (ρ : ℂ) * (((lam - 1 : ℝ) : ℂ) * exp ((a : ℂ) * I) + exp ((a : ℂ) * I) * (1 - q)) := by
          push_cast; ring
        rw [this, re_ofReal_mul, add_re, re_ofReal_mul, exp_ofReal_mul_I_re]
      rw [e1]
      nlinarith [mul_nonneg hρ hpos]
  have h0 : g 0 = 0 := by simp [hg, struveSc_phase_zero]
  have := hmono (mem_Ici.2 le_rfl) (show r ∈ Ici (0 : ℝ) from hr) hr
  rw [h0] at this
  simp only [hg] at this
  linarith


/-- Uniform bounds for `q = (1+w²)^{-1/2}` on the rotated rays: `|q| ≤ K`, `|1 - q| ≤ K r`. -/
theorem struveSc_q_bounds {δ : ℝ} (hδ : 0 < δ) : ∃ K > 0, ∀ a : ℝ, |a| ≤ (π - δ) / 2 →
    ∀ r : ℝ, 0 ≤ r →
      ‖(1 + ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ))‖ ≤ K ∧
      ‖1 - (1 + ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ))‖ ≤ K * r := by
  obtain ⟨c0, hc0, hc⟩ := Complex.exists_pos_le_norm_one_add_ofReal_mul_exp
    (Φ := π - δ) (by linarith)
  set K : ℝ := 1 + 1 / Real.sqrt c0 with hK
  have hs0 : 0 < Real.sqrt c0 := Real.sqrt_pos.2 hc0
  refine ⟨K, by positivity, fun a ha r hr => ?_⟩
  have ha' : |a| < π / 2 := by linarith
  set w := (r : ℂ) * exp (((-a : ℝ) : ℂ) * I) with hw
  set u := 1 + w ^ 2 with hu
  set P := u ^ (1 / 2 : ℂ) with hP
  have hmem : u ∈ slitPlane := struveSc_mem_slitPlane ha'
  have hu0 : u ≠ 0 := slitPlane_ne_zero hmem
  have hP0 : P ≠ 0 := by rw [hP]; exact (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).2 hu0
  have hP2 : P ^ 2 = u := by rw [hP, ← cpow_nat_mul]; norm_num
  have hq : u ^ (-(1 / 2 : ℂ)) = P⁻¹ := by rw [cpow_neg]
  have hw2 : w ^ 2 = ((r ^ 2 : ℝ) : ℂ) * exp (((-(2 * a) : ℝ) : ℂ) * I) := by
    rw [hw, mul_pow, ← exp_nat_mul]; push_cast; ring_nf
  have hu_ge : c0 ≤ ‖u‖ := by
    rw [hu, hw2]; exact hc _ (sq_nonneg r) _ (by rw [abs_neg, abs_mul]; norm_num; linarith)
  have hPn : Real.sqrt c0 ≤ ‖P‖ := by
    have : ‖P‖ ^ 2 = ‖u‖ := by rw [← norm_pow, hP2]
    rw [show ‖P‖ = Real.sqrt (‖P‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm, this]
    exact Real.sqrt_le_sqrt hu_ge
  have hPpos : 0 < ‖P‖ := hs0.trans_le hPn
  have hqn : ‖u ^ (-(1 / 2 : ℂ))‖ ≤ 1 / Real.sqrt c0 := by
    rw [hq, norm_inv, inv_eq_one_div]
    exact one_div_le_one_div_of_le hs0 hPn
  have hP1 : 1 ≤ ‖P + 1‖ := by
    have := struveSc_re_cpow_half_nonneg u
    have h := Complex.re_le_norm (P + 1)
    rw [add_re, one_re] at h
    linarith
  have hiden : (1 - u ^ (-(1 / 2 : ℂ))) * (P * (P + 1)) = w ^ 2 := by
    rw [hq, show w ^ 2 = P ^ 2 - 1 by rw [hP2, hu]; ring]
    field_simp
    ring
  have h1q : ‖1 - u ^ (-(1 / 2 : ℂ))‖ ≤ r ^ 2 / Real.sqrt c0 := by
    have hn : ‖1 - u ^ (-(1 / 2 : ℂ))‖ * (‖P‖ * ‖P + 1‖) = r ^ 2 := by
      rw [← norm_mul, ← norm_mul, hiden, hw2, norm_mul, norm_exp_ofReal_mul_I, mul_one,
        norm_real, Real.norm_of_nonneg (sq_nonneg r)]
    rw [le_div_iff₀ hs0, ← hn]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    nlinarith
  refine ⟨hqn.trans (by rw [hK]; linarith), ?_⟩
  rcases le_or_gt r 1 with h | h
  · calc ‖1 - u ^ (-(1 / 2 : ℂ))‖ ≤ r ^ 2 / Real.sqrt c0 := h1q
      _ ≤ r / Real.sqrt c0 := by gcongr; nlinarith
      _ ≤ K * r := by
        rw [hK, div_eq_mul_one_div r, mul_comm r]; gcongr; linarith
  · calc ‖1 - u ^ (-(1 / 2 : ℂ))‖ ≤ ‖(1 : ℂ)‖ + ‖u ^ (-(1 / 2 : ℂ))‖ := norm_sub_le _ _
      _ ≤ K := by rw [norm_one, hK]; linarith
      _ ≤ K * r := le_mul_of_one_le_right (by positivity) h.le


/-- `‖e^A - e^B‖ ≤ ‖A - B‖ e^M` when `re A, re B ≤ M`. -/
theorem struveSc_norm_exp_sub_exp_le {A B : ℂ} {M : ℝ} (hA : A.re ≤ M) (hB : B.re ≤ M) :
    ‖exp A - exp B‖ ≤ ‖A - B‖ * Real.exp M := by
  set g : ℝ → ℂ := fun t => exp (B + t * (A - B)) with hg
  have hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g ((A - B) * g t) (Icc 0 1) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => B + (t : ℂ) * (A - B)) (A - B) t := by
      simpa using ((hasDerivAt_id t).ofReal_comp.mul_const (A - B)).const_add B
    have := h1.cexp
    rw [mul_comm] at this
    exact this.hasDerivWithinAt
  have hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖(A - B) * g t‖ ≤ ‖A - B‖ * Real.exp M := by
    intro t ht
    rw [norm_mul, hg, norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    simp only [add_re, re_ofReal_mul, sub_re]
    nlinarith [ht.1, ht.2]
  have := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
  simpa [hg] using this

/-- `‖Ψ(r e^{-ia}) - e^{-ia}(λ-1) r‖ ≤ K r²/2` from `|1 - q| ≤ K r`. -/
theorem struveSc_phase_sub_lin (lam : ℝ) {a : ℝ} (ha : |a| < π / 2) {K : ℝ}
    (hK : ∀ s : ℝ, 0 ≤ s →
      ‖1 - (1 + ((s : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ))‖ ≤ K * s)
    {r : ℝ} (hr : 0 ≤ r) :
    ‖struveSc_phase lam ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) -
      exp (((-a : ℝ) : ℂ) * I) * ((lam : ℂ) - 1) * r‖ ≤ K / 2 * r ^ 2 := by
  set E := exp (((-a : ℝ) : ℂ) * I) with hE
  set f : ℝ → ℂ := fun s => struveSc_phase lam ((s : ℂ) * E) - E * ((lam : ℂ) - 1) * s with hf
  have hfd : ∀ s : ℝ, 0 ≤ s → HasDerivAt f
      (E * (1 - (1 + ((s : ℂ) * E) ^ 2) ^ (-(1 / 2 : ℂ)))) s := by
    intro s hs
    have h1 := struveSc_hasDerivAt_phase_ray lam ha hs
    have h2 := (hasDerivAt_id s).ofReal_comp.const_mul (E * ((lam : ℂ) - 1))
    refine (h1.fun_sub h2).congr_deriv ?_
    rw [← hE, ofReal_one, mul_one]; ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := f) (a := 0) (b := r)
    (f' := fun s => E * (1 - (1 + ((s : ℂ) * E) ^ 2) ^ (-(1 / 2 : ℂ))))
    (B := fun s => K / 2 * s ^ 2) (B' := fun s => K * s)
    (fun s hs => (hfd s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hfd s hs.1).hasDerivWithinAt)
    (by simp [hf, struveSc_phase_zero])
    (fun s => by
      have := (hasDerivAt_pow 2 s).const_mul (K / 2)
      convert this using 1; push_cast; ring)
    (fun s hs => by
      rw [norm_mul, hE, norm_exp_ofReal_mul_I, one_mul]; exact hK s hs.1)
    (right_mem_Icc.2 hr)
  simpa [hf] using key


/-- The integrand of the rotated representation of `𝐀_{-ν}(λν)` in terms of the phase. -/
theorem struveSc_integrand_eq (lam : ℝ) {a : ℝ} (ha : |a| < π / 2) (ν : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    exp (-((lam : ℂ) * ν * exp (((-a : ℝ) : ℂ) * I) * r)) *
      struveAs_kernel (-ν) ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) =
    exp (-(ν * struveSc_phase lam ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)))) *
      (1 + ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ)) := by
  set w := (r : ℂ) * exp (((-a : ℝ) : ℂ) * I) with hw
  have hx : w + (1 + w ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := by
    intro h; have := struveSc_re_x_pos ha hr; rw [← hw, h, zero_re] at this; exact lt_irrefl _ this
  rw [struveAs_kernel, neg_neg, cpow_def_of_ne_zero hx, struveSc_phase, ← mul_assoc, ← exp_add]
  congr 2
  rw [hw]; ring


/-- `∫₀^∞ e^{-br} rⁿ dr = n!/b^{n+1}`, with integrability. -/
theorem struveSc_integral_pow_exp (n : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun r : ℝ => Real.exp (-(b * r)) * r ^ n) (Ioi 0) ∧
    ∫ r in Ioi (0 : ℝ), Real.exp (-(b * r)) * r ^ n = n ! / b ^ (n + 1) := by
  have hcongr : EqOn (fun r : ℝ => r ^ ((n + 1 : ℝ) - 1) * Real.exp (-(b * r)))
      (fun r : ℝ => Real.exp (-(b * r)) * r ^ n) (Ioi 0) := by
    intro r hr
    simp only
    rw [show (n + 1 : ℝ) - 1 = (n : ℝ) by ring, Real.rpow_natCast, mul_comm]
  refine ⟨?_, ?_⟩
  · have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := b)
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith) one_pos hb
    refine h.congr_fun (fun r hr => ?_) measurableSet_Ioi
    simp only [Real.rpow_one, Real.rpow_natCast, neg_mul]
    ring
  · rw [← setIntegral_congr_fun measurableSet_Ioi hcongr,
      Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) hb, Real.Gamma_nat_eq_factorial,
      show (n + 1 : ℝ) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, div_pow, one_pow]
    field_simp

/-- **The main estimate** behind DLMF 11.11.14. -/
theorem struveSc_integral_est {lam : ℝ} (hlam : 1 < lam) {a : ℝ} (ha : |a| < π / 2) {K : ℝ}
    (hK : ∀ s : ℝ, 0 ≤ s →
      ‖(1 + ((s : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ))‖ ≤ K ∧
      ‖1 - (1 + ((s : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ))‖ ≤ K * s)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ‖exp (((-a : ℝ) : ℂ) * I) * (∫ r in Ioi (0 : ℝ),
        exp (-((lam : ℂ) * ((ρ : ℂ) * exp ((2 * a : ℝ) * I)) * exp (((-a : ℝ) : ℂ) * I) * r)) *
        struveAs_kernel (-((ρ : ℂ) * exp ((2 * a : ℝ) * I))) ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I))) -
      1 / (((ρ : ℂ) * exp ((2 * a : ℝ) * I)) * ((lam : ℂ) - 1))‖ ≤
      (K / ((lam - 1) * Real.cos a) ^ 2 + K / ((lam - 1) * Real.cos a) ^ 3) / ρ ^ 2 := by
  set ν : ℂ := (ρ : ℂ) * exp ((2 * a : ℝ) * I) with hν
  set E : ℂ := exp (((-a : ℝ) : ℂ) * I) with hE
  set κ : ℝ := (lam - 1) * Real.cos a with hκ
  have hc := struveSc_cos_pos ha
  have hκ0 : 0 < κ := mul_pos (by linarith) hc
  set b : ℝ := κ * ρ with hb
  have hb0 : 0 < b := mul_pos hκ0 hρ
  set q : ℝ → ℂ := fun s => (1 + ((s : ℂ) * E) ^ 2) ^ (-(1 / 2 : ℂ)) with hq
  set Ψ : ℝ → ℂ := fun s => struveSc_phase lam ((s : ℂ) * E) with hΨ
  set F : ℝ → ℂ := fun r => exp (-(ν * Ψ r)) * q r with hF
  have hνE : ν * E = (ρ : ℂ) * exp ((a : ℂ) * I) := by
    rw [hν, hE, mul_assoc, ← exp_add]; congr 2; push_cast; ring
  set c : ℂ := -(ν * E * ((lam : ℂ) - 1)) with hcdef
  have hcre : c.re = -b := by
    rw [hcdef, hνE, hb, hκ, show (ρ : ℂ) * exp ((a : ℂ) * I) * ((lam : ℂ) - 1) =
      ((ρ * (lam - 1) : ℝ) : ℂ) * exp ((a : ℂ) * I) by push_cast; ring, neg_re, re_ofReal_mul,
      exp_ofReal_mul_I_re]
    ring
  set G : ℝ → ℂ := fun r => exp (c * r) with hG
  have hGi : IntegrableOn G (Ioi 0) := integrableOn_exp_mul_complex_Ioi (by rw [hcre]; linarith) 0
  have hc0 : c ≠ 0 := by intro h; rw [h, zero_re] at hcre; linarith
  have hGint : ∫ r in Ioi (0 : ℝ), G r = -1 / c := by
    rw [integral_exp_mul_complex_Ioi (by rw [hcre]; linarith) 0]; simp
  -- pointwise bound
  have hbound : ∀ r : ℝ, 0 < r → ‖F r - G r‖ ≤
      Real.exp (-(b * r)) * (K * r + ρ * (K / 2) * r ^ 2) := by
    intro r hr
    have hre := struveSc_re_phase_ge (lam := lam) ha hρ.le hr.le
    rw [← hν] at hre
    have hA : (-(ν * Ψ r)).re ≤ -(b * r) := by
      rw [neg_re, hb]; simp only [hΨ, hE]; nlinarith
    have hB : (c * r).re ≤ -(b * r) := by rw [re_mul_ofReal, hcre]; linarith
    have hsplit : F r - G r = exp (-(ν * Ψ r)) * (q r - 1) + (exp (-(ν * Ψ r)) - exp (c * r)) := by
      simp only [hF, hG]; ring
    have h1 : ‖exp (-(ν * Ψ r))‖ ≤ Real.exp (-(b * r)) := by
      rw [norm_exp]; exact Real.exp_le_exp.2 hA
    have h2 : ‖q r - 1‖ ≤ K * r := by rw [norm_sub_rev]; exact (hK r hr.le).2
    have hlin := struveSc_phase_sub_lin lam ha (fun s hs => (hK s hs).2) hr.le
    have h3 : ‖-(ν * Ψ r) - c * r‖ ≤ ρ * (K / 2 * r ^ 2) := by
      have : -(ν * Ψ r) - c * r = -(ν * (struveSc_phase lam ((r : ℂ) * E) -
          E * ((lam : ℂ) - 1) * r)) := by
        simp only [hΨ, hcdef]; ring
      rw [this, norm_neg, norm_mul, hν, norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real,
        Real.norm_of_nonneg hρ.le]
      exact mul_le_mul_of_nonneg_left hlin hρ.le
    have h4 := struveSc_norm_exp_sub_exp_le hA hB
    rw [hsplit]
    calc ‖exp (-(ν * Ψ r)) * (q r - 1) + (exp (-(ν * Ψ r)) - exp (c * r))‖
        ≤ ‖exp (-(ν * Ψ r))‖ * ‖q r - 1‖ + ‖-(ν * Ψ r) - c * r‖ * Real.exp (-(b * r)) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul]; gcongr
      _ ≤ Real.exp (-(b * r)) * (K * r) + ρ * (K / 2 * r ^ 2) * Real.exp (-(b * r)) := by
          gcongr
      _ = _ := by ring
  -- integrability
  obtain ⟨i1, e1⟩ := struveSc_integral_pow_exp 1 hb0
  obtain ⟨i2, e2⟩ := struveSc_integral_pow_exp 2 hb0
  have hbi : IntegrableOn (fun r : ℝ => Real.exp (-(b * r)) * (K * r + ρ * (K / 2) * r ^ 2))
      (Ioi 0) := by
    have : IntegrableOn (fun r : ℝ => K * (Real.exp (-(b * r)) * r ^ 1) +
        ρ * (K / 2) * (Real.exp (-(b * r)) * r ^ 2)) (Ioi 0) :=
      (i1.const_mul K).add (i2.const_mul (ρ * (K / 2)))
    refine this.congr_fun (fun r _ => ?_) measurableSet_Ioi
    simp only [pow_one]; ring
  have hFc : ContinuousOn F (Ioi 0) := by
    intro r hr
    have hr0 : (0 : ℝ) ≤ r := le_of_lt hr
    have hΨc : ContinuousAt Ψ r := (struveSc_hasDerivAt_phase_ray lam ha hr0).continuousAt
    have hqc : ContinuousAt q r :=
      ((by fun_prop : Continuous fun s : ℝ => 1 + ((s : ℂ) * E) ^ 2).continuousAt).cpow
        continuousAt_const (struveSc_mem_slitPlane ha)
    exact ((continuous_exp.continuousAt.comp (hΨc.const_mul ν).neg).mul hqc).continuousWithinAt
  have hdm : AEStronglyMeasurable (fun r => F r - G r) (volume.restrict (Ioi 0)) :=
    (hFc.sub (by fun_prop : Continuous G).continuousOn).aestronglyMeasurable measurableSet_Ioi
  have hdi : IntegrableOn (fun r => F r - G r) (Ioi 0) := by
    refine Integrable.mono' hbi hdm ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun r hr => hbound r hr))
  have hFi : IntegrableOn F (Ioi 0) := by
    have : IntegrableOn (fun r => (F r - G r) + G r) (Ioi 0) := hdi.add hGi
    refine this.congr_fun (fun r _ => ?_) measurableSet_Ioi
    simp
  -- assemble
  have hint_eq : (∫ r in Ioi (0 : ℝ),
      exp (-((lam : ℂ) * ν * E * r)) * struveAs_kernel (-ν) ((r : ℂ) * E)) =
      ∫ r in Ioi (0 : ℝ), F r := by
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    simp only [hF, hΨ, hq]
    exact struveSc_integrand_eq lam ha ν (le_of_lt hr)
  have hE1 : ‖E‖ = 1 := by rw [hE, norm_exp_ofReal_mul_I]
  have hE0 : E ≠ 0 := by rw [hE]; exact exp_ne_zero _
  have hν0 : ν ≠ 0 := by
    rw [hν]; exact mul_ne_zero (ofReal_ne_zero.2 hρ.ne') (exp_ne_zero _)
  have hl0 : (lam : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hlam.ne'
  have hlead : 1 / (ν * ((lam : ℂ) - 1)) = E * ∫ r in Ioi (0 : ℝ), G r := by
    rw [hGint, hcdef]; field_simp
  rw [hint_eq, hlead, ← mul_sub, norm_mul, hE1, one_mul, ← integral_sub hFi hGi]
  refine (norm_integral_le_of_norm_le hbi ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun r hr => hbound r hr))).trans (le_of_eq ?_)
  have hsum : ∫ r in Ioi (0 : ℝ), Real.exp (-(b * r)) * (K * r + ρ * (K / 2) * r ^ 2) =
      K * (1 / b ^ 2) + ρ * (K / 2) * (2 / b ^ 3) := by
    have h := integral_add (i1.const_mul K) (i2.const_mul (ρ * (K / 2)))
    rw [integral_const_mul, integral_const_mul, e1, e2] at h
    rw [← show (1 ! : ℝ) / b ^ (1 + 1) = 1 / b ^ 2 by norm_num,
      ← show (2 ! : ℝ) / b ^ (2 + 1) = 2 / b ^ 3 by norm_num, ← h]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    simp only [pow_one]; ring
  rw [hsum, hb]
  field_simp



/-- Quantitative form of `struveSc_re_one_sub_q`:
`re (e^{ia}(1 - q)) ≥ cos a · r²/(4(1+r²))`. -/
theorem struveSc_re_one_sub_q_ge {a : ℝ} (ha : |a| < π / 2) (r : ℝ) :
    Real.cos a * r ^ 2 / (4 * (1 + r ^ 2)) ≤ (exp ((a : ℂ) * I) *
      (1 - (1 + ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ)))).re := by
  set w := (r : ℂ) * exp (((-a : ℝ) : ℂ) * I) with hw
  set u := 1 + w ^ 2 with hu
  set P := u ^ (1 / 2 : ℂ) with hP
  have hmem : u ∈ slitPlane := struveSc_mem_slitPlane ha
  have hu0 : u ≠ 0 := slitPlane_ne_zero hmem
  have hP0 : P ≠ 0 := by rw [hP]; exact (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).2 hu0
  have hP2 : P ^ 2 = u := by
    rw [hP, ← cpow_nat_mul]; norm_num
  have hq : u ^ (-(1 / 2 : ℂ)) = P⁻¹ := by rw [cpow_neg]
  set ea := exp ((a : ℂ) * I) with hea
  have hc := struveSc_cos_pos ha
  set Z := ea * u + ea * P with hZ
  have hZre : (1 + r ^ 2) * Real.cos a ≤ Z.re := by
    have h1 : (ea * u).re = (1 + r ^ 2) * Real.cos a := by
      rw [hea, hu, struveSc_sq, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
      simp only [mul_re, add_re, ofReal_re, mul_im, ofReal_im, I_re, I_im, add_im, mul_zero,
        sub_zero, mul_one, zero_add, one_re, one_im, sub_re, sub_im]
      rw [Real.cos_two_mul, Real.sin_two_mul]
      linear_combination (2 * r ^ 2 * Real.cos a) * Real.sin_sq_add_cos_sq a
    have h2 := struveSc_re_rot_P ha r
    simp only [hZ, add_re]
    rw [h1]; linarith
  have hZ0 : Z ≠ 0 := by
    intro h; rw [h, zero_re] at hZre; nlinarith [sq_nonneg r]
  have hkey : ea * (1 - u ^ (-(1 / 2 : ℂ))) * Z = (r : ℂ) ^ 2 := by
    have hee : ea * ea * w ^ 2 = (r : ℂ) ^ 2 := by
      rw [hw, hea, mul_pow, ← exp_nat_mul]
      have h1 : cexp (↑a * I) * cexp (↑a * I) * cexp (((2 : ℕ) : ℂ) * (((-a : ℝ) : ℂ) * I)) = 1 := by
        rw [← exp_add, ← exp_add]; push_cast; ring_nf; exact exp_zero
      linear_combination (r : ℂ) ^ 2 * h1
    rw [hq, hZ, ← hee, show w ^ 2 = P ^ 2 - 1 by rw [hP2, hu]; ring]
    field_simp
    linear_combination ea ^ 2 * (1 - P) * hP2
  have hX : ea * (1 - u ^ (-(1 / 2 : ℂ))) = ((r ^ 2 : ℝ) : ℂ) / Z := by
    rw [eq_div_iff hZ0, hkey]; push_cast; ring
  have hwn : ‖w‖ = |r| := by
    rw [hw, norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real, Real.norm_eq_abs]
  have hun : ‖u‖ ≤ 1 + r ^ 2 := by
    rw [hu]; refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_pow, hwn, sq_abs]
  have hPn : ‖P‖ ≤ 1 + r ^ 2 := by
    have h2 : ‖P‖ ^ 2 = ‖u‖ := by rw [← norm_pow, hP2]
    nlinarith [norm_nonneg P, sq_nonneg r]
  have hZn : ‖Z‖ ≤ 2 * (1 + r ^ 2) := by
    rw [hZ]; refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, hea, norm_exp_ofReal_mul_I]; linarith
  rw [hX, div_re, ofReal_re, ofReal_im, zero_mul, zero_div, add_zero]
  have hnp : 0 < normSq Z := normSq_pos.2 hZ0
  have hns : normSq Z ≤ 4 * (1 + r ^ 2) ^ 2 := by
    rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg Z]
  rw [div_le_div_iff₀ (by positivity) hnp]
  have h1 := mul_le_mul_of_nonneg_left hns (mul_nonneg hc.le (sq_nonneg r))
  have h2 := mul_le_mul_of_nonneg_left hZre (by positivity : (0 : ℝ) ≤ 4 * r ^ 2 * (1 + r ^ 2))
  nlinarith

/-- Growth of the `λ = 1` phase: `re (ν Ψ₁(r e^{-ia})) ≥ cos a · ρ r³/(12(1+r²))`. -/
theorem struveSc_re_phase_one_ge {a : ℝ} (ha : |a| < π / 2) {ρ : ℝ}
    (hρ : 0 ≤ ρ) {r : ℝ} (hr : 0 ≤ r) :
    Real.cos a * ρ * (r ^ 3 / (12 * (1 + r ^ 2))) ≤
      ((ρ : ℂ) * exp ((2 * a : ℝ) * I) *
        struveSc_phase 1 ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I))).re := by
  set ν : ℂ := (ρ : ℂ) * exp ((2 * a : ℝ) * I) with hν
  set h : ℝ → ℝ := fun s => s ^ 3 / (12 * (1 + s ^ 2)) with hh
  have hhd : ∀ s, HasDerivAt h (s ^ 2 * (3 + s ^ 2) / (12 * (1 + s ^ 2) ^ 2)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * s ^ 2) s := by simpa using hasDerivAt_pow 3 s
    have h2 : HasDerivAt (fun s : ℝ => 12 * (1 + s ^ 2)) (12 * (2 * s)) s := by
      simpa using ((hasDerivAt_pow 2 s).const_add 1).const_mul 12
    have h3 := h1.div h2 (by positivity)
    convert h3 using 1
    field_simp; ring
  set g : ℝ → ℝ := fun s => (ν * struveSc_phase 1 ((s : ℂ) * exp (((-a : ℝ) : ℂ) * I))).re -
    Real.cos a * ρ * h s with hg
  have hνE : ν * exp (((-a : ℝ) : ℂ) * I) = (ρ : ℂ) * exp ((a : ℂ) * I) := by
    rw [hν, mul_assoc, ← exp_add]; congr 2; push_cast; ring
  have hderiv : ∀ s : ℝ, 0 ≤ s → HasDerivAt g
      ((ν * (exp (((-a : ℝ) : ℂ) * I) * (((1 : ℝ) : ℂ) -
        (1 + ((s : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ))))).re -
        Real.cos a * ρ * (s ^ 2 * (3 + s ^ 2) / (12 * (1 + s ^ 2) ^ 2))) s := by
    intro s hs
    exact (struveSc_hasDerivAt_re ((struveSc_hasDerivAt_phase_ray 1 ha hs).const_mul ν)).sub
      ((hhd s).const_mul _)
  have hc := struveSc_cos_pos ha
  have hmono : MonotoneOn g (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) (f' := fun s =>
      (ν * (exp (((-a : ℝ) : ℂ) * I) * (((1 : ℝ) : ℂ) -
        (1 + ((s : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ))))).re -
        Real.cos a * ρ * (s ^ 2 * (3 + s ^ 2) / (12 * (1 + s ^ 2) ^ 2))) ?_ ?_ ?_
    · exact fun s hs => (hderiv s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ici] at hs ⊢
      exact (hderiv s (le_of_lt hs)).hasDerivWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      have hpos := struveSc_re_one_sub_q_ge ha s
      rw [← mul_assoc, hνE, sub_nonneg, ofReal_one, mul_assoc (ρ : ℂ), re_ofReal_mul]
      have hs2 : s ^ 2 * (3 + s ^ 2) / (12 * (1 + s ^ 2) ^ 2) ≤ s ^ 2 / (4 * (1 + s ^ 2)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg s, pow_nonneg (sq_nonneg s) 2, mul_nonneg (sq_nonneg s) (sq_nonneg s)]
      calc Real.cos a * ρ * (s ^ 2 * (3 + s ^ 2) / (12 * (1 + s ^ 2) ^ 2))
          ≤ Real.cos a * ρ * (s ^ 2 / (4 * (1 + s ^ 2))) := by gcongr
        _ = ρ * (Real.cos a * s ^ 2 / (4 * (1 + s ^ 2))) := by ring
        _ ≤ _ := by gcongr
  have h0 : g 0 = 0 := by simp [hg, hh, struveSc_phase_zero]
  have := hmono (mem_Ici.2 le_rfl) (show r ∈ Ici (0 : ℝ) from hr) hr
  rw [h0] at this
  simp only [hg, hh] at this
  linarith

/-- `‖Ψ₁(w) - w³/6‖ ≤ (1/2 + K)/5 · r⁵` on the ray `w = r e^{-ia}`, given `‖q‖ ≤ K`. -/
theorem struveSc_phase_one_sub_cube {a : ℝ} (ha : |a| < π / 2) {K : ℝ}
    (hK : ∀ s : ℝ, 0 ≤ s →
      ‖(1 + ((s : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ))‖ ≤ K)
    {r : ℝ} (hr : 0 ≤ r) :
    ‖struveSc_phase 1 ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) -
      ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 3 / 6‖ ≤ (1 / 2 + K) / 5 * r ^ 5 := by
  set E := exp (((-a : ℝ) : ℂ) * I) with hE
  have hpt : ∀ s : ℝ, 0 ≤ s → ‖(1 - (1 + ((s : ℂ) * E) ^ 2) ^ (-(1 / 2 : ℂ))) -
      ((s : ℂ) * E) ^ 2 / 2‖ ≤ (1 / 2 + K) * s ^ 4 := by
    intro s hs
    have hqK := hK s hs
    set w := (s : ℂ) * E with hw
    set u := 1 + w ^ 2 with hu
    set P := u ^ (1 / 2 : ℂ) with hP
    have hmem : u ∈ slitPlane := struveSc_mem_slitPlane ha
    have hu0 : u ≠ 0 := slitPlane_ne_zero hmem
    have hP0 : P ≠ 0 := by
      rw [hP]; exact (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).2 hu0
    have hP2 : P ^ 2 = u := by rw [hP, ← cpow_nat_mul]; norm_num
    have hq : u ^ (-(1 / 2 : ℂ)) = P⁻¹ := by rw [cpow_neg]
    have hP1 : 1 ≤ ‖P + 1‖ := by
      have := struveSc_re_cpow_half_nonneg u
      have h := Complex.re_le_norm (P + 1)
      rw [add_re, one_re] at h
      linarith
    have hwn : ‖w‖ = s := by
      rw [hw, norm_mul, hE, norm_exp_ofReal_mul_I, mul_one, norm_real, Real.norm_of_nonneg hs]
    have hPm1 : (P - 1) * (P + 1) = w ^ 2 := by
      rw [show w ^ 2 = P ^ 2 - 1 by rw [hP2, hu]; ring]; ring
    have hPm1n : ‖P - 1‖ ≤ s ^ 2 := by
      have : ‖P - 1‖ * ‖P + 1‖ = s ^ 2 := by rw [← norm_mul, hPm1, norm_pow, hwn]
      nlinarith [norm_nonneg (P - 1)]
    have hid : (1 - u ^ (-(1 / 2 : ℂ))) - w ^ 2 / 2 = -((P - 1) ^ 2 * (P + 2)) / (2 * P) := by
      rw [hq, show w ^ 2 = P ^ 2 - 1 by rw [hP2, hu]; ring]; field_simp; ring
    rw [hq, norm_inv] at hqK
    have hPp : 0 < ‖P‖ := norm_pos_iff.2 hP0
    have hKP : 1 ≤ K * ‖P‖ := by
      rwa [inv_le_iff_one_le_mul₀ hPp] at hqK
    rw [hid, norm_div, norm_neg, norm_mul, norm_mul, norm_pow, div_le_iff₀ (mul_pos (by norm_num) hPp)]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]
    have hP2n : ‖P + 2‖ ≤ ‖P‖ + 2 := by
      refine (norm_add_le _ _).trans ?_; simp
    have hsq : ‖P - 1‖ ^ 2 ≤ s ^ 4 := by
      rw [show s ^ 4 = (s ^ 2) ^ 2 by ring]
      exact pow_le_pow_left₀ (norm_nonneg _) hPm1n 2
    calc ‖P - 1‖ ^ 2 * ‖P + 2‖ ≤ s ^ 4 * (‖P‖ + 2) := by
          gcongr
      _ ≤ (1 / 2 + K) * s ^ 4 * (2 * ‖P‖) := by
          nlinarith [pow_nonneg hs 4]
  set f : ℝ → ℂ := fun s => struveSc_phase 1 ((s : ℂ) * E) - ((s : ℂ) * E) ^ 3 / 6 with hf
  have hfd : ∀ s : ℝ, 0 ≤ s → HasDerivAt f
      (E * ((1 - (1 + ((s : ℂ) * E) ^ 2) ^ (-(1 / 2 : ℂ))) - ((s : ℂ) * E) ^ 2 / 2)) s := by
    intro s hs
    have h1 := struveSc_hasDerivAt_phase_ray 1 ha hs
    have h2 := (((hasDerivAt_id s).ofReal_comp.mul_const E).pow 3).div_const 6
    refine (h1.fun_sub h2).congr_deriv ?_
    rw [← hE]; simp only [id, ofReal_one, one_mul]; push_cast; ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := f) (a := 0) (b := r)
    (f' := fun s => E * ((1 - (1 + ((s : ℂ) * E) ^ 2) ^ (-(1 / 2 : ℂ))) - ((s : ℂ) * E) ^ 2 / 2))
    (B := fun s => (1 / 2 + K) / 5 * s ^ 5) (B' := fun s => (1 / 2 + K) * s ^ 4)
    (fun s hs => (hfd s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hfd s hs.1).hasDerivWithinAt)
    (by simp [hf, struveSc_phase_zero])
    (fun s => by
      have := (hasDerivAt_pow 5 s).const_mul ((1 / 2 + K) / 5)
      convert this using 1; push_cast; ring)
    (fun s hs => by
      rw [norm_mul, hE, norm_exp_ofReal_mul_I, one_mul]; exact hpt s hs.1)
    (right_mem_Icc.2 hr)
  simpa [hf] using key

/-- `∫₀^∞ e^{-b r³} rⁿ dr = b^{-(n+1)/3} Γ((n+1)/3)/3`, with integrability. -/
theorem struveSc_integral_pow_exp_cube (n : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun r : ℝ => Real.exp (-(b * r ^ 3)) * r ^ n) (Ioi 0) ∧
    ∫ r in Ioi (0 : ℝ), Real.exp (-(b * r ^ 3)) * r ^ n =
      b ^ (-((n : ℝ) + 1) / 3) * (1 / 3) * Real.Gamma (((n : ℝ) + 1) / 3) := by
  have hcongr : EqOn (fun r : ℝ => r ^ (n : ℝ) * Real.exp (-b * r ^ (3 : ℝ)))
      (fun r : ℝ => Real.exp (-(b * r ^ 3)) * r ^ n) (Ioi 0) := by
    intro r _
    simp only [Real.rpow_natCast, neg_mul]
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  have hn : (-1 : ℝ) < n := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  refine ⟨(integrableOn_rpow_mul_exp_neg_mul_rpow hn (by norm_num) hb).congr_fun hcongr
    measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_rpow_mul_exp_neg_mul_rpow (by norm_num) hn hb]

/-- `∫₀^∞ e^{-C r³} dr = Γ(4/3) C^{-1/3}` for `re C > 0`. -/
theorem struveSc_integral_exp_cube {C : ℂ} (hC : 0 < C.re) :
    ∫ r in Ioi (0 : ℝ), exp (-(C * (r : ℂ) ^ 3)) = Gamma (4 / 3) * C ^ (-(1 / 3 : ℂ)) := by
  have hsub := integral_comp_rpow_Ioi (fun y : ℝ => exp (-(C * (y : ℂ) ^ 3)))
    (p := 1 / 3) (by norm_num)
  rw [← hsub]
  have hG := integral_cpow_mul_cexp_neg_mul_Ioi (s := 1 / 3) (z := C) (by norm_num) hC
  have h43 : Gamma (4 / 3 : ℂ) = 1 / 3 * Gamma (1 / 3) := by
    rw [show (4 / 3 : ℂ) = 1 / 3 + 1 by norm_num, Gamma_add_one _ (by norm_num)]
  rw [h43, mul_assoc, show (-(1 / 3 : ℂ)) = -(1 / 3) from rfl, ← hG, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 < x := hx
  simp only [Complex.real_smul]
  have h3 : ((x ^ (1 / 3 : ℝ) : ℝ) : ℂ) ^ 3 = (x : ℂ) := by
    rw [← ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  rw [h3]
  have hc : ((|(1 / 3 : ℝ)| * x ^ ((1 / 3 : ℝ) - 1) : ℝ) : ℂ) =
      1 / 3 * (x : ℂ) ^ ((1 / 3 : ℂ) - 1) := by
    rw [abs_of_pos (by norm_num), ofReal_mul, ofReal_cpow hx0.le]; push_cast; ring
  rw [hc, mul_comm C]; ring

/-- Integrability of `e^{-C r³}` on `(0,∞)` for `re C > 0`. -/
theorem struveSc_integrableOn_exp_cube {C : ℂ} (hC : 0 < C.re) :
    IntegrableOn (fun r : ℝ => exp (-(C * (r : ℂ) ^ 3))) (Ioi 0) := by
  obtain ⟨hi, -⟩ := struveSc_integral_pow_exp_cube 0 hC
  refine Integrable.mono' hi ((by fun_prop : Continuous fun r : ℝ =>
    exp (-(C * (r : ℂ) ^ 3))).aestronglyMeasurable) ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun r _ => ?_))
  rw [norm_exp, pow_zero, mul_one, neg_re, ← ofReal_pow, mul_comm, re_ofReal_mul, mul_comm]

/-- `e^{-c ρ r³/(12(1+r²))} ≤ e^{-β r³} + e^{-β r}` with `β = cρ/24`. -/
theorem struveSc_exp_split {c ρ r : ℝ} (hc : 0 ≤ c) (hρ : 0 ≤ ρ) (hr : 0 ≤ r) :
    Real.exp (-(c * ρ * (r ^ 3 / (12 * (1 + r ^ 2))))) ≤
      Real.exp (-(c / 24 * ρ * r ^ 3)) + Real.exp (-(c / 24 * ρ * r)) := by
  have hcρ : 0 ≤ c * ρ := mul_nonneg hc hρ
  rcases le_total r 1 with h | h
  · have : c / 24 * ρ * r ^ 3 ≤ c * ρ * (r ^ 3 / (12 * (1 + r ^ 2))) := by
      rw [show c / 24 * ρ * r ^ 3 = c * ρ * (r ^ 3 / 24) by ring]
      refine mul_le_mul_of_nonneg_left ?_ hcρ
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [pow_nonneg hr 3, mul_nonneg (pow_nonneg hr 3) (sq_nonneg r), sq_nonneg r,
        mul_le_mul_of_nonneg_left (pow_le_one₀ hr h : r ^ 2 ≤ 1) (pow_nonneg hr 3)]
    linarith [Real.exp_le_exp.2 (neg_le_neg this), Real.exp_pos (-(c / 24 * ρ * r))]
  · have : c / 24 * ρ * r ≤ c * ρ * (r ^ 3 / (12 * (1 + r ^ 2))) := by
      rw [show c / 24 * ρ * r = c * ρ * (r / 24) by ring]
      refine mul_le_mul_of_nonneg_left ?_ hcρ
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [one_le_pow₀ h (n := 2), mul_le_mul_of_nonneg_left (one_le_pow₀ h (n := 2) : 1 ≤ r ^ 2) hr]
    linarith [Real.exp_le_exp.2 (neg_le_neg this), Real.exp_pos (-(c / 24 * ρ * r ^ 3))]

set_option maxHeartbeats 400000 in
/-- **The main estimate** behind DLMF 11.11.16. -/
theorem struveSc_turning_est {a : ℝ} (ha : |a| < π / 2) {K c0 : ℝ} (hK0 : 0 ≤ K) (hc0 : 0 < c0)
    (hc0a : c0 ≤ Real.cos a)
    (hK : ∀ s : ℝ, 0 ≤ s →
      ‖(1 + ((s : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ))‖ ≤ K ∧
      ‖1 - (1 + ((s : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ))‖ ≤ K * s)
    {ρ : ℝ} (hρ : 1 ≤ ρ) :
    ‖(∫ r in Ioi (0 : ℝ), exp (-((ρ : ℂ) * exp ((2 * a : ℝ) * I) *
          struveSc_phase 1 ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)))) *
          (1 + ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ))) -
      ∫ r in Ioi (0 : ℝ), exp (-(((ρ : ℂ) * exp ((2 * a : ℝ) * I) *
          exp (((-a : ℝ) : ℂ) * I) ^ 3 / 6) * (r : ℂ) ^ 3))‖ ≤
      (K * ((c0 / 24) ^ (-(2 / 3 : ℝ)) * (1 / 3) * Real.Gamma (2 / 3) + 1 / (c0 / 24) ^ 2) +
        (1 / 2 + K) / 5 * (1 / (3 * (c0 / 24) ^ 2) + 120 / (c0 / 24) ^ 6)) *
        ρ ^ (-(2 / 3 : ℝ)) := by
  have hρ0 : 0 < ρ := by linarith
  set ν : ℂ := (ρ : ℂ) * exp ((2 * a : ℝ) * I) with hν
  set E : ℂ := exp (((-a : ℝ) : ℂ) * I) with hE
  set κ : ℝ := c0 / 24 with hκ
  have hκ0 : 0 < κ := by positivity
  set K₅ : ℝ := (1 / 2 + K) / 5 with hK₅
  have hK₅0 : 0 ≤ K₅ := by positivity
  set β : ℝ := κ * ρ with hβ
  have hβ0 : 0 < β := mul_pos hκ0 hρ0
  have hc := struveSc_cos_pos ha
  set q : ℝ → ℂ := fun s => (1 + ((s : ℂ) * E) ^ 2) ^ (-(1 / 2 : ℂ)) with hq
  set Ψ : ℝ → ℂ := fun s => struveSc_phase 1 ((s : ℂ) * E) with hΨ
  set F : ℝ → ℂ := fun r => exp (-(ν * Ψ r)) * q r with hF
  set C : ℂ := ν * E ^ 3 / 6 with hC
  have hνE3 : ν * E ^ 3 = ((ρ : ℝ) : ℂ) * exp (((-a : ℝ) : ℂ) * I) := by
    rw [hν, hE, ← exp_nat_mul, mul_assoc, ← exp_add]; congr 2; push_cast; ring
  have hCre : C.re = ρ * Real.cos a / 6 := by
    rw [hC, hνE3, show ((ρ : ℝ) : ℂ) * exp (((-a : ℝ) : ℂ) * I) / 6 =
      ((ρ / 6 : ℝ) : ℂ) * exp (((-a : ℝ) : ℂ) * I) by push_cast; ring, re_ofReal_mul,
      exp_ofReal_mul_I_re, Real.cos_neg]
    ring
  have hCpos : 0 < C.re := by rw [hCre]; positivity
  set G : ℝ → ℂ := fun r => exp (-(C * (r : ℂ) ^ 3)) with hG
  have hGi : IntegrableOn G (Ioi 0) := struveSc_integrableOn_exp_cube hCpos
  set H : ℝ → ℝ := fun r => (Real.exp (-(β * r ^ 3)) + Real.exp (-(β * r))) *
    (K * r + ρ * K₅ * r ^ 5) with hH
  -- pointwise bound
  have hbound : ∀ r : ℝ, 0 < r → ‖F r - G r‖ ≤ H r := by
    intro r hr
    set X : ℝ := Real.exp (-(c0 * ρ * (r ^ 3 / (12 * (1 + r ^ 2))))) with hX
    have hhr : 0 ≤ r ^ 3 / (12 * (1 + r ^ 2)) := by positivity
    have hre := struveSc_re_phase_one_ge ha hρ0.le hr.le
    rw [← hν] at hre
    have hA : (-(ν * Ψ r)).re ≤ -(c0 * ρ * (r ^ 3 / (12 * (1 + r ^ 2)))) := by
      rw [neg_re]; simp only [hΨ, hE]
      have : c0 * ρ * (r ^ 3 / (12 * (1 + r ^ 2))) ≤
          Real.cos a * ρ * (r ^ 3 / (12 * (1 + r ^ 2))) := by gcongr
      linarith
    have hB : (-(C * (r : ℂ) ^ 3)).re ≤ -(c0 * ρ * (r ^ 3 / (12 * (1 + r ^ 2)))) := by
      rw [neg_re, ← ofReal_pow, re_mul_ofReal, hCre, neg_le_neg_iff]
      have h1 : r ^ 3 / (12 * (1 + r ^ 2)) ≤ r ^ 3 / 6 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [pow_nonneg hr.le 3, mul_nonneg (pow_nonneg hr.le 3) (sq_nonneg r)]
      calc c0 * ρ * (r ^ 3 / (12 * (1 + r ^ 2))) ≤ Real.cos a * ρ * (r ^ 3 / 6) := by gcongr
        _ = _ := by ring
    have hsplit : F r - G r = exp (-(ν * Ψ r)) * (q r - 1) +
        (exp (-(ν * Ψ r)) - exp (-(C * (r : ℂ) ^ 3))) := by
      simp only [hF, hG]; ring
    have h1 : ‖exp (-(ν * Ψ r))‖ ≤ X := by
      rw [norm_exp]; exact Real.exp_le_exp.2 hA
    have h2 : ‖q r - 1‖ ≤ K * r := by rw [norm_sub_rev]; exact (hK r hr.le).2
    have hcube := struveSc_phase_one_sub_cube ha (fun s hs => (hK s hs).1) hr.le
    have h3 : ‖-(ν * Ψ r) - -(C * (r : ℂ) ^ 3)‖ ≤ ρ * (K₅ * r ^ 5) := by
      have : -(ν * Ψ r) - -(C * (r : ℂ) ^ 3) = -(ν * (struveSc_phase 1 ((r : ℂ) * E) -
          ((r : ℂ) * E) ^ 3 / 6)) := by
        simp only [hΨ, hC]; ring
      rw [this, norm_neg, norm_mul, hν, norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real,
        Real.norm_of_nonneg hρ0.le]
      exact mul_le_mul_of_nonneg_left hcube hρ0.le
    have h4 := struveSc_norm_exp_sub_exp_le hA hB
    have hXs := struveSc_exp_split hc0.le hρ0.le hr.le
    rw [hsplit]
    calc ‖exp (-(ν * Ψ r)) * (q r - 1) + (exp (-(ν * Ψ r)) - exp (-(C * (r : ℂ) ^ 3)))‖
        ≤ ‖exp (-(ν * Ψ r))‖ * ‖q r - 1‖ + ‖-(ν * Ψ r) - -(C * (r : ℂ) ^ 3)‖ * X := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul]; gcongr
      _ ≤ X * (K * r) + ρ * (K₅ * r ^ 5) * X := by gcongr
      _ = X * (K * r + ρ * K₅ * r ^ 5) := by ring
      _ ≤ H r := by
          simp only [hH]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          simpa [hX, hβ, hκ, mul_assoc] using hXs
  -- integrability of the majorant
  obtain ⟨i31, e31⟩ := struveSc_integral_pow_exp_cube 1 hβ0
  obtain ⟨i35, e35⟩ := struveSc_integral_pow_exp_cube 5 hβ0
  obtain ⟨i11, e11⟩ := struveSc_integral_pow_exp 1 hβ0
  obtain ⟨i15, e15⟩ := struveSc_integral_pow_exp 5 hβ0
  have hsplitH : ∀ r : ℝ, H r = (K * (Real.exp (-(β * r ^ 3)) * r ^ 1) +
      ρ * K₅ * (Real.exp (-(β * r ^ 3)) * r ^ 5)) +
      (K * (Real.exp (-(β * r)) * r ^ 1) + ρ * K₅ * (Real.exp (-(β * r)) * r ^ 5)) := by
    intro r; simp only [hH, pow_one]; ring
  have j1 := (i31.const_mul K).add (i35.const_mul (ρ * K₅))
  have j2 := (i11.const_mul K).add (i15.const_mul (ρ * K₅))
  have hHi : IntegrableOn H (Ioi 0) := by
    refine IntegrableOn.congr_fun (j1.add j2) (fun r _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply]; exact (hsplitH r).symm
  have k1 := integral_add (i31.const_mul K) (i35.const_mul (ρ * K₅))
  have k2 := integral_add (i11.const_mul K) (i15.const_mul (ρ * K₅))
  have k3 := integral_add j1 j2
  simp only [Pi.add_apply] at k3
  have hHint : ∫ r in Ioi (0 : ℝ), H r =
      (K * (β ^ (-(2 / 3 : ℝ)) * (1 / 3) * Real.Gamma (2 / 3)) + ρ * K₅ * (1 / (3 * β ^ 2))) +
      (K * (1 / β ^ 2) + ρ * K₅ * (120 / β ^ 6)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun r _ => hsplitH r), k3, k1, k2,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
      e31, e35, e11, e15]
    have g2 : Real.Gamma ((((5 : ℕ) : ℝ) + 1) / 3) = 1 := by
      rw [show (((5 : ℕ) : ℝ) + 1) / 3 = 1 + 1 by norm_num, Real.Gamma_add_one one_ne_zero,
        Real.Gamma_one, mul_one]
    have b2 : β ^ (-(((5 : ℕ) : ℝ) + 1) / 3) = 1 / β ^ 2 := by
      rw [show (-(((5 : ℕ) : ℝ) + 1) / 3) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hβ0.le,
        Real.rpow_natCast, one_div]
    rw [g2, b2, show (-(((1 : ℕ) : ℝ) + 1) / 3) = -(2 / 3 : ℝ) by norm_num,
      show (((1 : ℕ) : ℝ) + 1) / 3 = 2 / 3 by norm_num]
    norm_num [Nat.factorial]
  -- continuity and integrability of `F`
  have hFc : ContinuousOn F (Ioi 0) := by
    intro r hr
    have hr0 : (0 : ℝ) ≤ r := le_of_lt hr
    have hΨc : ContinuousAt Ψ r := (struveSc_hasDerivAt_phase_ray 1 ha hr0).continuousAt
    have hqc : ContinuousAt q r :=
      ((by fun_prop : Continuous fun s : ℝ => 1 + ((s : ℂ) * E) ^ 2).continuousAt).cpow
        continuousAt_const (struveSc_mem_slitPlane ha)
    exact ((continuous_exp.continuousAt.comp (hΨc.const_mul ν).neg).mul hqc).continuousWithinAt
  have hdm : AEStronglyMeasurable (fun r => F r - G r) (volume.restrict (Ioi 0)) :=
    (hFc.sub (by fun_prop : Continuous G).continuousOn).aestronglyMeasurable measurableSet_Ioi
  have hdi : IntegrableOn (fun r => F r - G r) (Ioi 0) :=
    Integrable.mono' hHi hdm ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun r hr => hbound r hr))
  have hFi : IntegrableOn F (Ioi 0) := by
    have : IntegrableOn (fun r => (F r - G r) + G r) (Ioi 0) := hdi.add hGi
    refine this.congr_fun (fun r _ => ?_) measurableSet_Ioi
    simp
  -- assemble
  change ‖(∫ r in Ioi (0 : ℝ), F r) - ∫ r in Ioi (0 : ℝ), G r‖ ≤ _
  rw [← integral_sub hFi hGi]
  refine (norm_integral_le_of_norm_le hHi ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun r hr => hbound r hr))).trans ?_
  rw [hHint]
  -- comparison of powers of `ρ`
  have hm1 : ρ ^ (-(1 : ℝ)) ≤ ρ ^ (-(2 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hρ (by norm_num)
  rw [Real.rpow_neg_one] at hm1
  have hinv : 0 < ρ⁻¹ := inv_pos.2 hρ0
  have hinv1 : ρ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hρ
  have hp2 : 1 / β ^ 2 = 1 / κ ^ 2 * ρ⁻¹ * ρ⁻¹ := by rw [hβ]; field_simp
  have hp6 : 1 / β ^ 6 = 1 / κ ^ 6 * ρ⁻¹ ^ 6 := by rw [hβ]; field_simp
  have hp23 : β ^ (-(2 / 3 : ℝ)) = κ ^ (-(2 / 3 : ℝ)) * ρ ^ (-(2 / 3 : ℝ)) := by
    rw [hβ, Real.mul_rpow hκ0.le hρ0.le]
  have hρρ : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ0.ne'
  have hr5 : ρ⁻¹ ^ 5 ≤ ρ⁻¹ := by
    calc ρ⁻¹ ^ 5 ≤ ρ⁻¹ ^ 1 := pow_le_pow_of_le_one hinv.le hinv1 (by norm_num)
      _ = ρ⁻¹ := pow_one _
  have hr2 : ρ⁻¹ * ρ⁻¹ ≤ ρ⁻¹ := by nlinarith
  set t : ℝ := ρ ^ (-(2 / 3 : ℝ)) with ht
  have hG23 : 0 < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have hk23 : 0 < κ ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hκ0 _
  have e1 : ρ * K₅ * (1 / (3 * β ^ 2)) = K₅ * (1 / (3 * κ ^ 2)) * ρ⁻¹ := by
    rw [hβ]; field_simp
  have e2 : ρ * K₅ * (120 / β ^ 6) = K₅ * (120 / κ ^ 6) * ρ⁻¹ ^ 5 := by
    rw [hβ]; field_simp
  rw [hp23, e1, e2, hp2]
  have hk2 : 0 ≤ 1 / κ ^ 2 := by positivity
  have hk6 : 0 ≤ 120 / κ ^ 6 := by positivity
  have hk32 : 0 ≤ 1 / (3 * κ ^ 2) := by positivity
  have a1 : K * (1 / κ ^ 2 * ρ⁻¹ * ρ⁻¹) ≤ K * (1 / κ ^ 2) * t := by
    rw [mul_assoc (1 / κ ^ 2)]
    have := mul_le_mul_of_nonneg_left (hr2.trans hm1) (mul_nonneg hK0 hk2)
    linarith [this]
  have a2 : K₅ * (1 / (3 * κ ^ 2)) * ρ⁻¹ ≤ K₅ * (1 / (3 * κ ^ 2)) * t :=
    mul_le_mul_of_nonneg_left hm1 (mul_nonneg hK₅0 hk32)
  have a3 : K₅ * (120 / κ ^ 6) * ρ⁻¹ ^ 5 ≤ K₅ * (120 / κ ^ 6) * t :=
    mul_le_mul_of_nonneg_left (hr5.trans hm1) (mul_nonneg hK₅0 hk6)
  nlinarith [a1, a2, a3]

/-- `π⁻¹ Γ(4/3) 6^{1/3} = 2^{4/3}/(3^{7/6} Γ(2/3))`. -/
theorem struveSc_const_turn :
    1 / π * Real.Gamma (4 / 3) * (1 / 6 : ℝ) ^ (-(1 / 3 : ℝ)) =
      2 ^ (4 / 3 : ℝ) / (3 ^ (7 / 6 : ℝ) * Real.Gamma (2 / 3)) := by
  have h := struveTP_const_E
  rw [Real.sin_pi_div_six] at h
  have h2 : (2 : ℝ) ^ (4 / 3 : ℝ) = 2 * 2 ^ (1 / 3 : ℝ) := by
    rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one]
  rw [h2, mul_div_assoc, ← h]
  ring

/-- The DLMF 11.11.16 right-hand side as the Gamma-integral leading term. -/
theorem struveSc_turning_rhs {a : ℝ} (ha : |a| < π / 2) {ρ : ℝ} (hρ : 0 < ρ) :
    (2 : ℂ) ^ (4 / 3 : ℂ) / ((3 : ℂ) ^ (7 / 6 : ℂ) * Gamma (2 / 3) *
        ((ρ : ℂ) * exp ((2 * a : ℝ) * I)) ^ (1 / 3 : ℂ)) =
      1 / π * (exp (((-a : ℝ) : ℂ) * I) * (Gamma (4 / 3) *
        ((ρ : ℂ) * exp ((2 * a : ℝ) * I) * exp (((-a : ℝ) : ℂ) * I) ^ 3 / 6) ^
          (-(1 / 3 : ℂ)))) := by
  have hb1 : -π < a := by linarith [neg_abs_le a, Real.pi_pos]
  have hb2 : a < π := by linarith [le_abs_self a, Real.pi_pos]
  have hc1 : -π < 2 * a := by linarith [neg_abs_le a]
  have hc2 : 2 * a ≤ π := by linarith [le_abs_self a]
  have hνE3 : (ρ : ℂ) * exp ((2 * a : ℝ) * I) * exp (((-a : ℝ) : ℂ) * I) ^ 3 / 6 =
      ((ρ / 6 : ℝ) : ℂ) * exp (((-a : ℝ) : ℂ) * I) := by
    rw [← exp_nat_mul, mul_assoc, ← exp_add]; push_cast; ring_nf
  rw [hνE3, ofReal_mul_exp_cpow (r := ρ / 6) (by positivity) (θ := -a) (by linarith)
    (by linarith), ofReal_mul_exp_cpow hρ hc1 hc2]
  have e1 : ((ρ / 6 : ℝ) : ℂ) ^ (-(1 / 3 : ℂ)) = (((ρ / 6) ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) := by
    rw [ofReal_cpow (by positivity)]; push_cast; rfl
  have e2 : (ρ : ℂ) ^ (1 / 3 : ℂ) = ((ρ ^ (1 / 3 : ℝ) : ℝ) : ℂ) := by
    rw [ofReal_cpow hρ.le]; push_cast; rfl
  have e3 : (2 : ℂ) ^ (4 / 3 : ℂ) = ((2 ^ (4 / 3 : ℝ) : ℝ) : ℂ) := by
    rw [ofReal_cpow (by norm_num)]; push_cast; rfl
  have e4 : (3 : ℂ) ^ (7 / 6 : ℂ) = ((3 ^ (7 / 6 : ℝ) : ℝ) : ℂ) := by
    rw [ofReal_cpow (by norm_num)]; push_cast; rfl
  have e5 : Gamma (2 / 3 : ℂ) = ((Real.Gamma (2 / 3) : ℝ) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; rfl
  have e6 : Gamma (4 / 3 : ℂ) = ((Real.Gamma (4 / 3) : ℝ) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; rfl
  have hx1 : exp (((-a : ℝ) : ℂ) * I * -(1 / 3 : ℂ)) = exp (((a / 3 : ℝ) : ℂ) * I) := by
    congr 1; push_cast; ring
  have hx2 : exp (((2 * a : ℝ) : ℂ) * I * (1 / 3 : ℂ)) = exp (((2 * a / 3 : ℝ) : ℂ) * I) := by
    congr 1; push_cast; ring
  rw [e1, e2, e3, e4, e5, e6, hx1, hx2]
  have hρ6 : (ρ / 6) ^ (-(1 / 3 : ℝ)) * ρ ^ (1 / 3 : ℝ) = (1 / 6 : ℝ) ^ (-(1 / 3 : ℝ)) := by
    rw [show ρ / 6 = 1 / 6 * ρ by ring, Real.mul_rpow (by norm_num) hρ.le, mul_assoc,
      ← Real.rpow_add hρ, show -(1 / 3 : ℝ) + 1 / 3 = 0 by ring, Real.rpow_zero, mul_one]
  have hk := struveSc_const_turn
  have hexp : exp (((-a : ℝ) : ℂ) * I) * exp (((a / 3 : ℝ) : ℂ) * I) *
      exp (((2 * a / 3 : ℝ) : ℂ) * I) = 1 := by
    rw [← exp_add, ← exp_add]; push_cast; ring_nf; exact exp_zero
  have hG : 0 < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have h3 : 0 < (3 : ℝ) ^ (7 / 6 : ℝ) := by positivity
  have hr3 : 0 < ρ ^ (1 / 3 : ℝ) := by positivity
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_pos.ne'
  have hne : ((ρ ^ (1 / 3 : ℝ) : ℝ) : ℂ) * exp (((2 * a / 3 : ℝ) : ℂ) * I) ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.2 hr3.ne') (exp_ne_zero _)
  have h3c : ((3 ^ (7 / 6 : ℝ) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 h3.ne'
  have hGc : ((Real.Gamma (2 / 3) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 hG.ne'
  rw [div_eq_iff (mul_ne_zero (mul_ne_zero h3c hGc) hne)]
  have hk' : ((2 ^ (4 / 3 : ℝ) : ℝ) : ℂ) = 1 / π * ((Real.Gamma (4 / 3) : ℝ) : ℂ) *
      (((ρ / 6) ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * ((ρ ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
      (((3 ^ (7 / 6 : ℝ) : ℝ) : ℂ) * ((Real.Gamma (2 / 3) : ℝ) : ℂ)) := by
    have : 2 ^ (4 / 3 : ℝ) = 1 / π * Real.Gamma (4 / 3) * ((ρ / 6) ^ (-(1 / 3 : ℝ)) *
        ρ ^ (1 / 3 : ℝ)) * (3 ^ (7 / 6 : ℝ) * Real.Gamma (2 / 3)) := by
      rw [hρ6, hk]; field_simp
    rw [this]; push_cast; ring
  rw [hk']
  linear_combination (-1 / π * ((Real.Gamma (4 / 3) : ℝ) : ℂ) *
      (((ρ / 6) ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * ((ρ ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
      (((3 ^ (7 / 6 : ℝ) : ℝ) : ℂ) * ((Real.Gamma (2 / 3) : ℝ) : ℂ))) * hexp

/-- The norm of the DLMF 11.11.16 right-hand side. -/
theorem struveSc_norm_turning_rhs (ν : ℂ) :
    ‖(2 : ℂ) ^ (4 / 3 : ℂ) / ((3 : ℂ) ^ (7 / 6 : ℂ) * Gamma (2 / 3) * ν ^ (1 / 3 : ℂ))‖ =
      2 ^ (4 / 3 : ℝ) / (3 ^ (7 / 6 : ℝ) * Real.Gamma (2 / 3)) / ‖ν‖ ^ (1 / 3 : ℝ) := by
  have e5 : Gamma (2 / 3 : ℂ) = ((Real.Gamma (2 / 3) : ℝ) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; rfl
  have hG : 0 < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  rw [e5, norm_div, norm_mul, norm_mul, norm_real, Real.norm_of_nonneg hG.le,
    show (4 / 3 : ℂ) = ((4 / 3 : ℝ) : ℂ) by push_cast; rfl,
    show (7 / 6 : ℂ) = ((7 / 6 : ℝ) : ℂ) by push_cast; rfl,
    show (1 / 3 : ℂ) = ((1 / 3 : ℝ) : ℂ) by push_cast; rfl,
    norm_cpow_real, norm_cpow_real, norm_cpow_real]
  simp only [Complex.norm_ofNat]
  ring


/-- The real phase `φ(s) = λ s - arsinh s` of `𝐀_{-ν}(λν)` on the positive axis. -/
noncomputable def struveSc_phiR (lam s : ℝ) : ℝ := lam * s - Real.arsinh s

theorem struveSc_sqrt_pos (s : ℝ) : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.2 (by positivity)

theorem struveSc_sqrt_sq (s : ℝ) : Real.sqrt (1 + s ^ 2) ^ 2 = 1 + s ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem struveSc_one_le_sqrt (s : ℝ) : 1 ≤ Real.sqrt (1 + s ^ 2) := by
  have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + s ^ 2 by nlinarith)
  rwa [Real.sqrt_one] at this

theorem struveSc_abs_le_sqrt (s : ℝ) : |s| ≤ Real.sqrt (1 + s ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)

theorem struveSc_hasDerivAt_sqrt (s : ℝ) :
    HasDerivAt (fun s : ℝ => Real.sqrt (1 + s ^ 2)) (s / Real.sqrt (1 + s ^ 2)) s := by
  have h := ((hasDerivAt_pow 2 s).const_add 1).sqrt (by positivity)
  convert h using 1
  have := struveSc_sqrt_pos s
  field_simp
  push_cast; ring

theorem struveSc_hasDerivAt_phiR (lam s : ℝ) :
    HasDerivAt (struveSc_phiR lam) (lam - (Real.sqrt (1 + s ^ 2))⁻¹) s := by
  have h := ((hasDerivAt_id s).const_mul lam).sub (Real.hasDerivAt_arsinh s)
  exact h.congr_deriv (by simp)

theorem struveSc_hasDerivAt_phiR' (lam s : ℝ) :
    HasDerivAt (fun s : ℝ => lam - (Real.sqrt (1 + s ^ 2))⁻¹)
      (s / Real.sqrt (1 + s ^ 2) ^ 3) s := by
  have hS := struveSc_sqrt_pos s
  have h := ((struveSc_hasDerivAt_sqrt s).inv hS.ne').const_sub lam
  convert h using 1
  field_simp

theorem struveSc_hasDerivAt_phiR'' (s : ℝ) :
    HasDerivAt (fun s : ℝ => s / Real.sqrt (1 + s ^ 2) ^ 3)
      ((1 - 2 * s ^ 2) / Real.sqrt (1 + s ^ 2) ^ 5) s := by
  have hS := struveSc_sqrt_pos s
  have h := (hasDerivAt_id s).div ((struveSc_hasDerivAt_sqrt s).pow 3) (pow_pos hS 3).ne'
  refine h.congr_deriv ?_
  have h2 := struveSc_sqrt_sq s
  simp only [id, Pi.pow_apply]
  field_simp
  norm_num
  rw [show Real.sqrt (1 + s ^ 2) ^ 4 = (Real.sqrt (1 + s ^ 2) ^ 2) ^ 2 by ring, h2]
  ring

theorem struveSc_abs_phiR''' (s : ℝ) : |(1 - 2 * s ^ 2) / Real.sqrt (1 + s ^ 2) ^ 5| ≤ 1 := by
  have hS := struveSc_sqrt_pos s
  have h1 := struveSc_one_le_sqrt s
  have h2 := struveSc_sqrt_sq s
  rw [abs_div, abs_of_pos (pow_pos hS 5), div_le_one (pow_pos hS 5)]
  have h4 : Real.sqrt (1 + s ^ 2) ^ 4 ≤ Real.sqrt (1 + s ^ 2) ^ 5 :=
    pow_le_pow_right₀ h1 (by norm_num)
  have h5 : Real.sqrt (1 + s ^ 2) ^ 4 = (1 + s ^ 2) ^ 2 := by
    rw [show Real.sqrt (1 + s ^ 2) ^ 4 = (Real.sqrt (1 + s ^ 2) ^ 2) ^ 2 by ring, h2]
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg s, pow_nonneg (sq_nonneg s) 2]

/-- `φ''` is `1`-Lipschitz. -/
theorem struveSc_phiR''_lip (u v : ℝ) :
    |u / Real.sqrt (1 + u ^ 2) ^ 3 - v / Real.sqrt (1 + v ^ 2) ^ 3| ≤ |u - v| := by
  have := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s : ℝ => s / Real.sqrt (1 + s ^ 2) ^ 3)
    (f' := fun s => (1 - 2 * s ^ 2) / Real.sqrt (1 + s ^ 2) ^ 5) (C := 1)
    (fun x _ => (struveSc_hasDerivAt_phiR'' x).hasDerivWithinAt)
    (fun x _ => by rw [Real.norm_eq_abs]; exact struveSc_abs_phiR''' x)
    (mem_univ v) (mem_univ u)
  simpa [Real.norm_eq_abs] using this

/-- Quadratic Taylor bound for `φ` at a critical point. -/
theorem struveSc_phiR_taylor {lam s₀ : ℝ} (hcrit : lam = (Real.sqrt (1 + s₀ ^ 2))⁻¹) (t : ℝ) :
    |struveSc_phiR lam (s₀ + t) - struveSc_phiR lam s₀ -
      s₀ / Real.sqrt (1 + s₀ ^ 2) ^ 3 / 2 * t ^ 2| ≤ |t| ^ 3 := by
  set c₂ := s₀ / Real.sqrt (1 + s₀ ^ 2) ^ 3 with hc₂
  -- first derivative bound
  have h1 : ∀ x : ℝ, |lam - (Real.sqrt (1 + (s₀ + x) ^ 2))⁻¹ - c₂ * x| ≤ x ^ 2 := by
    intro x
    have := (convex_uIcc (0 : ℝ) x).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun y : ℝ => lam - (Real.sqrt (1 + (s₀ + y) ^ 2))⁻¹ - c₂ * y)
      (f' := fun y => (s₀ + y) / Real.sqrt (1 + (s₀ + y) ^ 2) ^ 3 - c₂) (C := |x|)
      (fun y _ => by
        have h := (struveSc_hasDerivAt_phiR' lam (s₀ + y)).comp y ((hasDerivAt_id y).const_add s₀)
        have h2 := h.sub ((hasDerivAt_id y).const_mul c₂)
        exact (h2.congr_deriv (by simp)).hasDerivWithinAt)
      (fun y hy => by
        rw [Real.norm_eq_abs]
        have := struveSc_phiR''_lip (s₀ + y) s₀
        rw [show s₀ + y - s₀ = y by ring] at this
        have hy' := abs_sub_left_of_mem_uIcc hy
        simp only [sub_zero] at hy'
        exact this.trans hy')
      (left_mem_uIcc) (right_mem_uIcc)
    simp only [add_zero, mul_zero, sub_zero, Real.norm_eq_abs] at this
    rw [← hcrit, sub_self, sub_zero] at this
    calc _ ≤ |x| * |x| := this
      _ = x ^ 2 := by rw [← abs_mul, ← sq, abs_of_nonneg (sq_nonneg x)]
  have := (convex_uIcc (0 : ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y : ℝ => struveSc_phiR lam (s₀ + y) - struveSc_phiR lam s₀ - c₂ / 2 * y ^ 2)
    (f' := fun y => lam - (Real.sqrt (1 + (s₀ + y) ^ 2))⁻¹ - c₂ * y) (C := t ^ 2)
    (fun y _ => by
      have h := (struveSc_hasDerivAt_phiR lam (s₀ + y)).comp y ((hasDerivAt_id y).const_add s₀)
      have h2 := (h.sub_const (struveSc_phiR lam s₀)).sub ((hasDerivAt_pow 2 y).const_mul (c₂ / 2))
      exact (h2.congr_deriv (by simp; ring)).hasDerivWithinAt)
    (fun y hy => by
      rw [Real.norm_eq_abs]
      have hy' := abs_sub_left_of_mem_uIcc hy
      simp only [sub_zero] at hy'
      refine (h1 y).trans ?_
      rw [← sq_abs y, ← sq_abs t]
      exact pow_le_pow_left₀ (abs_nonneg _) hy' 2)
    (left_mem_uIcc) (right_mem_uIcc)
  simp only [add_zero, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, sub_zero, Real.norm_eq_abs] at this
  calc _ ≤ t ^ 2 * |t| := this
    _ = |t| ^ 3 := by rw [← sq_abs t]; ring

/-- The saddle `s₀ = √(1-λ²)/λ` satisfies `√(1+s₀²) = 1/λ`. -/
theorem struveSc_sqrt_saddle {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    Real.sqrt (1 + (Real.sqrt (1 - lam ^ 2) / lam) ^ 2) = lam⁻¹ := by
  have hs : Real.sqrt (1 - lam ^ 2) ^ 2 = 1 - lam ^ 2 := Real.sq_sqrt (by nlinarith)
  rw [div_pow, hs, show 1 + (1 - lam ^ 2) / lam ^ 2 = lam⁻¹ ^ 2 by field_simp; ring,
    Real.sqrt_sq (inv_pos.2 h0).le]

/-- Monotonicity of `φ` on both sides of the critical point. -/
theorem struveSc_phiR_mono {lam s₀ : ℝ} (hs₀ : 0 ≤ s₀) (hcrit : lam = (Real.sqrt (1 + s₀ ^ 2))⁻¹) :
    MonotoneOn (struveSc_phiR lam) (Ici s₀) ∧ AntitoneOn (struveSc_phiR lam) (Icc 0 s₀) := by
  have hS : ∀ s, 0 < Real.sqrt (1 + s ^ 2) := struveSc_sqrt_pos
  constructor
  · refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici s₀)
      (f' := fun s => lam - (Real.sqrt (1 + s ^ 2))⁻¹)
      (fun s _ => (struveSc_hasDerivAt_phiR lam s).continuousAt.continuousWithinAt)
      (fun s _ => (struveSc_hasDerivAt_phiR lam s).hasDerivWithinAt) ?_
    intro s hs
    rw [interior_Ici] at hs
    have hss : s₀ ≤ s := le_of_lt hs
    have : Real.sqrt (1 + s₀ ^ 2) ≤ Real.sqrt (1 + s ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rw [hcrit, sub_nonneg]
    exact inv_anti₀ (hS s₀) this
  · refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 s₀)
      (f' := fun s => lam - (Real.sqrt (1 + s ^ 2))⁻¹)
      (fun s _ => (struveSc_hasDerivAt_phiR lam s).continuousAt.continuousWithinAt)
      (fun s _ => (struveSc_hasDerivAt_phiR lam s).hasDerivWithinAt) ?_
    intro s hs
    rw [interior_Icc] at hs
    have : Real.sqrt (1 + s ^ 2) ≤ Real.sqrt (1 + s₀ ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith [hs.1, hs.2])
    rw [hcrit, sub_nonpos]
    exact inv_anti₀ (hS s) this

theorem struveSc_cpow_half_ofReal (s : ℝ) :
    (1 + (s : ℂ) ^ 2) ^ (1 / 2 : ℂ) = ((Real.sqrt (1 + s ^ 2) : ℝ) : ℂ) := by
  rw [show 1 + (s : ℂ) ^ 2 = ((1 + s ^ 2 : ℝ) : ℂ) by push_cast; ring,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, ← ofReal_cpow (by positivity),
    Real.sqrt_eq_rpow]

theorem struveSc_q_ofReal (s : ℝ) :
    (1 + (s : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) = (((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ) := by
  rw [cpow_neg, struveSc_cpow_half_ofReal, ofReal_inv]

theorem struveSc_phase_ofReal (lam s : ℝ) :
    struveSc_phase lam (s : ℂ) = ((struveSc_phiR lam s : ℝ) : ℂ) := by
  have hpos : 0 < s + Real.sqrt (1 + s ^ 2) := by
    have := struveSc_abs_le_sqrt s
    have h2 : Real.sqrt (1 + s ^ 2) ≠ |s| := by
      intro h
      have := struveSc_sqrt_sq s
      rw [h, sq_abs] at this; linarith
    have := lt_of_le_of_ne this h2.symm
    linarith [neg_abs_le s]
  rw [struveSc_phase, struveSc_cpow_half_ofReal, ← ofReal_add, ← ofReal_log hpos.le,
    struveSc_phiR, Real.arsinh]
  push_cast; ring

/-- DLMF 11.10.4 on the real contour, written with the real phase. -/
theorem struveSc_angerA_real {lam : ℝ} (hlam : 0 < lam) {ν : ℂ} (hν : 0 < ν.re) :
    angerA (-ν) (lam * ν) = 1 / π * ∫ s in Ioi (0 : ℝ),
      exp (-(ν * ((struveSc_phiR lam s : ℝ) : ℂ))) * (((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ) := by
  have ha : |(0 : ℝ)| < π / 2 := by rw [abs_zero]; positivity
  have hθ : |(-(0 : ℝ))| < π / 2 := by rw [neg_zero, abs_zero]; positivity
  have hz : 0 < ((lam : ℂ) * ν * exp (((-(0 : ℝ) : ℝ) : ℂ) * I)).re := by
    simp only [neg_zero, ofReal_zero, zero_mul, exp_zero, mul_one]
    rw [re_ofReal_mul]; exact mul_pos hlam hν
  rw [struveAs_angerA_eq_rot (-ν) hθ hz, struveAs_rotInt]
  have hint : (∫ r in Ioi (0 : ℝ), exp (-((lam : ℂ) * ν * exp (((-(0 : ℝ) : ℝ) : ℂ) * I) * r)) *
      struveAs_kernel (-ν) ((r : ℂ) * exp (((-(0 : ℝ) : ℝ) : ℂ) * I))) =
      ∫ s in Ioi (0 : ℝ), exp (-(ν * ((struveSc_phiR lam s : ℝ) : ℂ))) *
        (((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    rw [struveSc_integrand_eq lam ha ν (le_of_lt hr)]
    simp only [neg_zero, ofReal_zero, zero_mul, exp_zero, mul_one]
    rw [struveSc_phase_ofReal, struveSc_q_ofReal]
  rw [hint]
  simp only [neg_zero, ofReal_zero, zero_mul, exp_zero, one_mul]

/-- The saddle point `s₀ = √(1-λ²)/λ` of the real phase. -/
noncomputable def struveSc_s0 (lam : ℝ) : ℝ := Real.sqrt (1 - lam ^ 2) / lam

/-- Half the second derivative of the phase at the saddle, `φ''(s₀)/2 = s₀ λ³/2`. -/
noncomputable def struveSc_Q0 (lam : ℝ) : ℝ := struveSc_s0 lam * lam ^ 3 / 2

/-- The quadratic phase coefficient `(φ(s₀+t) - φ(s₀))/t²`, extended by `Q₀` at `0`. -/
noncomputable def struveSc_Qf (lam t : ℝ) : ℝ :=
  if t = 0 then struveSc_Q0 lam else
    (struveSc_phiR lam (struveSc_s0 lam + t) - struveSc_phiR lam (struveSc_s0 lam)) / t ^ 2

theorem struveSc_s0_pos {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) : 0 < struveSc_s0 lam :=
  div_pos (Real.sqrt_pos.2 (by nlinarith)) h0

theorem struveSc_crit {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    lam = (Real.sqrt (1 + struveSc_s0 lam ^ 2))⁻¹ := by
  rw [struveSc_s0, struveSc_sqrt_saddle h0 h1, inv_inv]

theorem struveSc_c2 {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    struveSc_s0 lam / Real.sqrt (1 + struveSc_s0 lam ^ 2) ^ 3 / 2 = struveSc_Q0 lam := by
  rw [struveSc_Q0, struveSc_s0, struveSc_sqrt_saddle h0 h1]
  field_simp

theorem struveSc_Q0_pos {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) : 0 < struveSc_Q0 lam := by
  have := struveSc_s0_pos h0 h1
  rw [struveSc_Q0]; positivity

theorem struveSc_Q0_lt {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    struveSc_Q0 lam < struveSc_s0 lam := by
  have := struveSc_s0_pos h0 h1
  have h3 : lam ^ 3 < 1 := pow_lt_one₀ h0.le h1 (by norm_num)
  rw [struveSc_Q0]; nlinarith

theorem struveSc_D_eq {lam : ℝ} (t : ℝ) :
    struveSc_phiR lam (struveSc_s0 lam + t) - struveSc_phiR lam (struveSc_s0 lam) =
      t ^ 2 * struveSc_Qf lam t := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · simp only [struveSc_Qf, ht, ↓reduceIte]; field_simp

theorem struveSc_D_taylor {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) (t : ℝ) :
    |struveSc_phiR lam (struveSc_s0 lam + t) - struveSc_phiR lam (struveSc_s0 lam) -
      struveSc_Q0 lam * t ^ 2| ≤ |t| ^ 3 := by
  have := struveSc_phiR_taylor (struveSc_crit h0 h1) t
  rwa [struveSc_c2 h0 h1] at this

theorem struveSc_Qf_lip {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) (t : ℝ) :
    |struveSc_Qf lam t - struveSc_Q0 lam| ≤ |t| := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [struveSc_Qf]
  · have h := struveSc_D_taylor h0 h1 t
    rw [struveSc_D_eq] at h
    have ht2 : 0 < t ^ 2 := by positivity
    rw [show t ^ 2 * struveSc_Qf lam t - struveSc_Q0 lam * t ^ 2 =
      t ^ 2 * (struveSc_Qf lam t - struveSc_Q0 lam) by ring, abs_mul,
      abs_of_pos ht2, show |t| ^ 3 = t ^ 2 * |t| by rw [← sq_abs t]; ring] at h
    exact le_of_mul_le_mul_left h ht2

theorem struveSc_amp_lip {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) (t : ℝ) :
    |(Real.sqrt (1 + (struveSc_s0 lam + t) ^ 2))⁻¹ - lam| ≤ |t| := by
  have hcrit := struveSc_crit h0 h1
  have := (convex_uIcc (0 : ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y : ℝ => lam - (Real.sqrt (1 + (struveSc_s0 lam + y) ^ 2))⁻¹)
    (f' := fun y => (struveSc_s0 lam + y) / Real.sqrt (1 + (struveSc_s0 lam + y) ^ 2) ^ 3)
    (C := 1)
    (fun y _ => by
      have h := (struveSc_hasDerivAt_phiR' lam (struveSc_s0 lam + y)).comp y
        ((hasDerivAt_id y).const_add (struveSc_s0 lam))
      exact (h.congr_deriv (by simp)).hasDerivWithinAt)
    (fun y _ => by
      set u := struveSc_s0 lam + y
      have hS := struveSc_sqrt_pos u
      have hle := struveSc_abs_le_sqrt u
      have h1' := struveSc_one_le_sqrt u
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hS 3), div_le_one (pow_pos hS 3)]
      calc |u| ≤ Real.sqrt (1 + u ^ 2) := hle
        _ ≤ Real.sqrt (1 + u ^ 2) ^ 3 := by
          calc Real.sqrt (1 + u ^ 2) = Real.sqrt (1 + u ^ 2) ^ 1 := (pow_one _).symm
            _ ≤ _ := pow_le_pow_right₀ h1' (by norm_num))
    (left_mem_uIcc) (right_mem_uIcc)
  simp only [add_zero, sub_zero, Real.norm_eq_abs] at this
  rw [← hcrit, sub_self, sub_zero, abs_sub_comm] at this
  simpa [abs_sub_comm] using this

theorem struveSc_phiR_ge {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) {s : ℝ} (hs : 0 ≤ s) :
    struveSc_phiR lam (struveSc_s0 lam) ≤ struveSc_phiR lam s := by
  have hs0 := struveSc_s0_pos h0 h1
  obtain ⟨hm, ha⟩ := struveSc_phiR_mono hs0.le (struveSc_crit h0 h1)
  rcases le_total s (struveSc_s0 lam) with h | h
  · exact ha ⟨hs, h⟩ ⟨hs0.le, le_rfl⟩ h
  · exact hm (mem_Ici.2 le_rfl) (mem_Ici.2 h) h

/-- The phase gap away from the saddle. -/
theorem struveSc_phiR_gap {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) {s : ℝ} (hs : 0 ≤ s)
    (hout : s ∉ Icc (struveSc_s0 lam - struveSc_Q0 lam / 2) (struveSc_s0 lam + struveSc_Q0 lam / 2)) :
    struveSc_phiR lam (struveSc_s0 lam) + struveSc_Q0 lam * (struveSc_Q0 lam / 2) ^ 2 / 2 ≤
      struveSc_phiR lam s := by
  set s₀ := struveSc_s0 lam with hs₀
  set Q0 := struveSc_Q0 lam with hQ0
  have hs0 := struveSc_s0_pos h0 h1
  have hQ := struveSc_Q0_pos h0 h1
  have hQs := struveSc_Q0_lt h0 h1
  obtain ⟨hm, ha⟩ := struveSc_phiR_mono hs0.le (struveSc_crit h0 h1)
  have key : ∀ t : ℝ, |t| = Q0 / 2 → struveSc_phiR lam s₀ + Q0 * (Q0 / 2) ^ 2 / 2 ≤
      struveSc_phiR lam (s₀ + t) := by
    intro t ht
    have h := struveSc_D_taylor h0 h1 t
    rw [← hs₀, ← hQ0, ht] at h
    have ht2 : t ^ 2 = (Q0 / 2) ^ 2 := by rw [← sq_abs, ht]
    rw [ht2] at h
    have := (abs_le.1 h).1
    nlinarith
  rw [mem_Icc, not_and_or, not_le, not_le] at hout
  rcases hout with h | h
  · have hk := key (-(Q0 / 2)) (by rw [abs_neg, abs_of_pos (by positivity)])
    have := ha ⟨hs, by linarith⟩ ⟨by linarith, by linarith⟩ (show s ≤ s₀ + -(Q0 / 2) by linarith)
    linarith
  · have hk := key (Q0 / 2) (abs_of_pos (by positivity))
    have := hm (mem_Ici.2 (by linarith)) (mem_Ici.2 (by linarith))
      (show s₀ + Q0 / 2 ≤ s by linarith)
    linarith

/-- An integrable majorant for `e^{-(φ - φ₀)} (1+s²)^{-1/2}`. -/
theorem struveSc_W_le {lam : ℝ} {s : ℝ} (hs : 0 ≤ s) (c : ℝ) :
    Real.exp (-(struveSc_phiR lam s - c)) * (Real.sqrt (1 + s ^ 2))⁻¹ ≤
      Real.exp c * (Real.exp (-(lam * s)) * (1 + 2 * s)) := by
  have hS := struveSc_sqrt_pos s
  have h1 := struveSc_one_le_sqrt s
  have hS1 : Real.sqrt (1 + s ^ 2) ≤ 1 + s := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have he : Real.exp (-(struveSc_phiR lam s - c)) =
      Real.exp c * (Real.exp (-(lam * s)) * (s + Real.sqrt (1 + s ^ 2))) := by
    rw [struveSc_phiR, ← Real.exp_arsinh, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hk : (s + Real.sqrt (1 + s ^ 2)) * (Real.sqrt (1 + s ^ 2))⁻¹ ≤ 1 + 2 * s := by
    calc (s + Real.sqrt (1 + s ^ 2)) * (Real.sqrt (1 + s ^ 2))⁻¹ ≤
          (s + Real.sqrt (1 + s ^ 2)) * 1 := by
          gcongr; exact inv_le_one_of_one_le₀ h1
      _ ≤ 1 + 2 * s := by linarith
  rw [he]
  calc Real.exp c * (Real.exp (-(lam * s)) * (s + Real.sqrt (1 + s ^ 2))) *
        (Real.sqrt (1 + s ^ 2))⁻¹ = Real.exp c * (Real.exp (-(lam * s)) *
          ((s + Real.sqrt (1 + s ^ 2)) * (Real.sqrt (1 + s ^ 2))⁻¹)) := by ring
    _ ≤ _ := by gcongr

theorem struveSc_integrableOn_maj {lam : ℝ} (h0 : 0 < lam) (c : ℝ) :
    IntegrableOn (fun s : ℝ => Real.exp c * (Real.exp (-(lam * s)) * (1 + 2 * s))) (Ioi 0) := by
  obtain ⟨i0, -⟩ := struveSc_integral_pow_exp 0 h0
  obtain ⟨i1, -⟩ := struveSc_integral_pow_exp 1 h0
  refine IntegrableOn.congr_fun ((i0.add (i1.const_mul 2)).const_mul (Real.exp c))
    (fun s _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply, pow_zero, pow_one]; ring

theorem struveSc_continuous_phiR (lam : ℝ) : Continuous (struveSc_phiR lam) :=
  (continuous_const.mul continuous_id).sub Real.continuous_arsinh

theorem struveSc_exp_neg_le_recip {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ 1 / y := by
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le hy (by linarith [Real.add_one_le_exp y])

theorem struveSc_cos_ge {δ θ : ℝ} (hδ : 0 ≤ δ) (hδπ : δ < π / 2) (hθ : |θ| ≤ π / 2 - δ) :
    Real.sin δ ≤ Real.cos θ := by
  rw [← Real.cos_abs, ← Real.cos_pi_div_two_sub]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) (by linarith [Real.pi_pos]) hθ

/-- **The main Laplace estimate** behind DLMF 11.11.15, uniform in `ph ν`. -/
theorem struveSc_inner_est {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) {δ : ℝ} (hδ : 0 < δ)
    (hδπ : δ < π / 2) : ∃ C n₀ : ℝ, 0 < n₀ ∧ ∀ n θ : ℝ, n₀ ≤ n → |θ| ≤ π / 2 - δ →
      ‖(Real.sqrt n : ℂ) * (∫ s in Ioi (0 : ℝ), exp (-((n : ℂ) * exp ((θ : ℂ) * I) *
          ((struveSc_phiR lam s - struveSc_phiR lam (struveSc_s0 lam) : ℝ) : ℂ))) *
          (((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ)) -
        (lam : ℂ) * ((π : ℂ) / (exp ((θ : ℂ) * I) * (struveSc_Q0 lam : ℂ))) ^ (1 / 2 : ℂ)‖ ≤
        C / Real.sqrt n := by
  set s₀ := struveSc_s0 lam with hs₀
  set φ₀ := struveSc_phiR lam s₀ with hφ₀
  set Q0 := struveSc_Q0 lam with hQ0
  have hs0 := struveSc_s0_pos h0 h1
  have hQ := struveSc_Q0_pos h0 h1
  have hQs := struveSc_Q0_lt h0 h1
  set δ' := Q0 / 2 with hδ'
  have hδ'0 : 0 < δ' := by positivity
  set η := Q0 * δ' ^ 2 / 2 with hη
  have hη0 : 0 < η := by positivity
  have hsδ : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  set c := Real.sin δ * Q0 / 2 with hc
  have hc0 : 0 < c := by positivity
  set maj : ℝ → ℝ := fun s => Real.exp φ₀ * (Real.exp (-(lam * s)) * (1 + 2 * s)) with hmaj
  have hmi : IntegrableOn maj (Ioi 0) := struveSc_integrableOn_maj h0 φ₀
  set T0 := ∫ s in Ioi (0 : ℝ), maj s with hT0
  have hmaj0 : ∀ s : ℝ, 0 ≤ s → 0 ≤ maj s := fun s hs => by simp only [hmaj]; positivity
  have hT00 : 0 ≤ T0 := setIntegral_nonneg measurableSet_Ioi fun s hs => hmaj0 s (le_of_lt hs)
  refine ⟨((1 + 1 / δ') / c + 1 * 1 / c ^ 2) + 2 * T0 / (Real.sin δ * η), 2 / Real.sin δ,
    by positivity, fun n θ hn hθ => ?_⟩
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hcos := struveSc_cos_ge hδ.le hδπ hθ
  set x := n * Real.cos θ with hx
  have hx2 : 2 ≤ x := by
    have : 2 ≤ n * Real.sin δ := by rwa [div_le_iff₀ hsδ] at hn
    calc 2 ≤ n * Real.sin δ := this
      _ ≤ x := by rw [hx]; gcongr
  set ν : ℂ := (n : ℂ) * exp ((θ : ℂ) * I) with hν
  have hνre : ∀ d : ℝ, (-(ν * (d : ℂ))).re = -(x * d) := by
    intro d
    rw [hν, neg_re, show (n : ℂ) * exp ((θ : ℂ) * I) * (d : ℂ) = ((n * d : ℝ) : ℂ) *
      exp ((θ : ℂ) * I) by push_cast; ring, re_ofReal_mul, exp_ofReal_mul_I_re, hx]
    ring
  set f : ℝ → ℂ := fun s => exp (-(ν * ((struveSc_phiR lam s - φ₀ : ℝ) : ℂ))) *
    (((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ) with hf
  have hfn : ∀ s : ℝ, ‖f s‖ = Real.exp (-(x * (struveSc_phiR lam s - φ₀))) *
      (Real.sqrt (1 + s ^ 2))⁻¹ := by
    intro s
    rw [hf, norm_mul, norm_exp, hνre, norm_real, Real.norm_of_nonneg
      (inv_nonneg.2 (struveSc_sqrt_pos s).le)]
  have hSc : Continuous fun s : ℝ => (Real.sqrt (1 + s ^ 2))⁻¹ :=
    ((Real.continuous_sqrt.comp (by fun_prop : Continuous fun s : ℝ => 1 + s ^ 2)).inv₀
      fun s => (struveSc_sqrt_pos s).ne')
  have hfc : Continuous f := by
    have := struveSc_continuous_phiR lam
    simp only [hf]
    exact (continuous_exp.comp ((continuous_const.mul (continuous_ofReal.comp
      (this.sub continuous_const))).neg)).mul (continuous_ofReal.comp hSc)
  -- global bound
  have hb1 : ∀ s : ℝ, 0 ≤ s → ‖f s‖ ≤ maj s := by
    intro s hs
    have hd := struveSc_phiR_ge h0 h1 hs
    rw [hfn]
    refine le_trans ?_ (struveSc_W_le hs φ₀)
    gcongr
    nlinarith
  -- tail bound
  have hb2 : ∀ s : ℝ, 0 ≤ s → s ∉ Icc (s₀ - δ') (s₀ + δ') →
      ‖f s‖ ≤ Real.exp (-((x - 1) * η)) * maj s := by
    intro s hs hout
    have hd := struveSc_phiR_gap h0 h1 hs hout
    rw [← hs₀, ← hQ0, ← hφ₀] at hd
    have hd' : η ≤ struveSc_phiR lam s - φ₀ := by rw [hη, hδ']; linarith
    rw [hfn]
    have : Real.exp (-(x * (struveSc_phiR lam s - φ₀))) ≤
        Real.exp (-((x - 1) * η)) * Real.exp (-(struveSc_phiR lam s - φ₀)) := by
      rw [← Real.exp_add]; gcongr
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ x - 1 by linarith) (sub_nonneg.2 hd')]
    calc Real.exp (-(x * (struveSc_phiR lam s - φ₀))) * (Real.sqrt (1 + s ^ 2))⁻¹
        ≤ Real.exp (-((x - 1) * η)) * Real.exp (-(struveSc_phiR lam s - φ₀)) *
          (Real.sqrt (1 + s ^ 2))⁻¹ := by
          gcongr
      _ = Real.exp (-((x - 1) * η)) * (Real.exp (-(struveSc_phiR lam s - φ₀)) *
          (Real.sqrt (1 + s ^ 2))⁻¹) := by ring
      _ ≤ _ := by gcongr; exact struveSc_W_le hs φ₀
  have hfi : IntegrableOn f (Ioi 0) :=
    Integrable.mono' hmi hfc.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun s hs => hb1 s (le_of_lt hs)))
  -- split
  have hsplit := integral_inter_add_sdiff (f := f) (μ := volume) (s := Ioi 0)
    (t := Icc (s₀ - δ') (s₀ + δ')) measurableSet_Icc hfi
  have hinter : Ioi (0 : ℝ) ∩ Icc (s₀ - δ') (s₀ + δ') = Icc (s₀ - δ') (s₀ + δ') := by
    refine inter_eq_right.2 fun s hs => ?_
    exact mem_Ioi.2 (by linarith [hs.1])
  rw [hinter] at hsplit
  -- core via the Laplace estimate
  set A : ℝ → ℂ := fun t => (((Real.sqrt (1 + (s₀ + t) ^ 2))⁻¹ : ℝ) : ℂ) with hA
  set q : ℝ → ℂ := fun t => exp ((θ : ℂ) * I) * ((struveSc_Qf lam t : ℝ) : ℂ) with hq
  have hcore : ∫ s in Icc (s₀ - δ') (s₀ + δ'), f s =
      ∫ t in Icc (-δ') δ', A t * exp (-(n : ℂ) * (t : ℂ) ^ 2 * q t) := by
    have hpre := (measurePreserving_add_right volume s₀).setIntegral_preimage_emb
      (measurableEmbedding_addRight s₀) f (Icc (s₀ - δ') (s₀ + δ'))
    rw [Set.preimage_add_const_Icc, show s₀ - δ' - s₀ = -δ' by ring,
      show s₀ + δ' - s₀ = δ' by ring] at hpre
    rw [← hpre]
    refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
    have hD := struveSc_D_eq (lam := lam) t
    rw [← hs₀, ← hφ₀] at hD
    simp only [hf, hA, hq]
    rw [add_comm t s₀, hD, mul_comm]
    congr 2
    rw [hν]; push_cast; ring
  have hAc : Measurable A := by
    simp only [hA]; fun_prop
  have hQm : Measurable (struveSc_Qf lam) := by
    have hDc : Continuous fun t : ℝ => struveSc_phiR lam (struveSc_s0 lam + t) -
        struveSc_phiR lam (struveSc_s0 lam) :=
      ((struveSc_continuous_phiR lam).comp (continuous_const.add continuous_id)).sub
        continuous_const
    unfold struveSc_Qf
    exact Measurable.ite measurableSet_eq measurable_const
      (hDc.measurable.div (continuous_pow 2).measurable)
  have hqc : Measurable q := by
    simp only [hq]
    exact measurable_const.mul (Complex.measurable_ofReal.comp hQm)
  have hQ0f : struveSc_Qf lam 0 = Q0 := by simp [struveSc_Qf, hQ0]
  have hqre : ∀ t ∈ Icc (-δ') δ', c ≤ (q t).re := by
    intro t ht
    have hl := struveSc_Qf_lip h0 h1 t
    rw [← hQ0] at hl
    have hta : |t| ≤ δ' := abs_le.2 ⟨ht.1, ht.2⟩
    have hQt : Q0 / 2 ≤ struveSc_Qf lam t := by
      have := (abs_le.1 hl).1; linarith
    simp only [hq]
    rw [mul_comm, re_ofReal_mul, exp_ofReal_mul_I_re, hc]
    calc Real.sin δ * Q0 / 2 = Real.sin δ * (Q0 / 2) := by ring
      _ ≤ Real.cos θ * struveSc_Qf lam t := by
        have : 0 ≤ Real.cos θ := by linarith
        gcongr
      _ = struveSc_Qf lam t * Real.cos θ := by ring
  have hA0 : ‖A 0‖ ≤ 1 := by
    simp only [hA, add_zero]
    rw [← struveSc_crit h0 h1, norm_real, Real.norm_of_nonneg h0.le]; exact h1.le
  have hAl : ∀ t ∈ Icc (-δ') δ', ‖A t - A 0‖ ≤ 1 * |t| := by
    intro t _
    simp only [hA, add_zero]
    rw [← struveSc_crit h0 h1, ← ofReal_sub, norm_real, Real.norm_eq_abs, one_mul]
    exact struveSc_amp_lip h0 h1 t
  have hql : ∀ t ∈ Icc (-δ') δ', ‖q t - q 0‖ ≤ 1 * |t| := by
    intro t _
    simp only [hq]
    rw [← mul_sub, norm_mul, norm_exp_ofReal_mul_I, one_mul, one_mul, ← ofReal_sub, norm_real,
      Real.norm_eq_abs, hQ0f]
    exact struveSc_Qf_lip h0 h1 t
  have hlap := Complex.norm_sqrt_mul_integral_laplace_Icc_sub_le hc0 hδ'0 hn0 hAc hqc hqre hA0
    hAl hql
  have hA0' : A 0 = (lam : ℂ) := by
    simp only [hA, add_zero]; rw [← struveSc_crit h0 h1]
  have hq0' : q 0 = exp ((θ : ℂ) * I) * (Q0 : ℂ) := by simp only [hq]; rw [hQ0f]
  rw [hA0', hq0', ← hcore] at hlap
  -- tail
  set Tl := ∫ s in Ioi (0 : ℝ) \ Icc (s₀ - δ') (s₀ + δ'), f s with hTl
  have htail : ‖Tl‖ ≤ Real.exp (-((x - 1) * η)) * T0 := by
    have hmi' : IntegrableOn maj (Ioi 0 \ Icc (s₀ - δ') (s₀ + δ')) := hmi.mono_set sdiff_subset
    calc ‖Tl‖ ≤ ∫ s in Ioi (0 : ℝ) \ Icc (s₀ - δ') (s₀ + δ'), Real.exp (-((x - 1) * η)) * maj s :=
          norm_integral_le_of_norm_le (hmi'.const_mul _) ((ae_restrict_iff'
            (measurableSet_Ioi.diff measurableSet_Icc)).mpr (Eventually.of_forall fun s hs =>
              hb2 s (le_of_lt hs.1) hs.2))
      _ = Real.exp (-((x - 1) * η)) * ∫ s in Ioi (0 : ℝ) \ Icc (s₀ - δ') (s₀ + δ'), maj s :=
          integral_const_mul _ _
      _ ≤ Real.exp (-((x - 1) * η)) * T0 := by
          gcongr
          exact setIntegral_mono_set hmi ((ae_restrict_iff' measurableSet_Ioi).mpr
            (Eventually.of_forall fun s hs => hmaj0 s (le_of_lt hs)))
            (Eventually.of_forall fun s hs => hs.1)
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have htail' : Real.sqrt n * ‖Tl‖ ≤ 2 * T0 / (Real.sin δ * η) / Real.sqrt n := by
    have hy : 0 < (x - 1) * η := mul_pos (by linarith) hη0
    have he := struveSc_exp_neg_le_recip hy
    have hxs : n * Real.sin δ ≤ x := by rw [hx]; gcongr
    have hx1 : x ≤ 2 * (x - 1) := by linarith
    have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
    calc Real.sqrt n * ‖Tl‖ ≤ Real.sqrt n * (1 / ((x - 1) * η) * T0) := by
          gcongr; exact htail.trans (by gcongr)
      _ ≤ Real.sqrt n * (2 / (n * Real.sin δ * η) * T0) := by
          have key : 1 / ((x - 1) * η) ≤ 2 / (n * Real.sin δ * η) := by
            rw [div_le_div_iff₀ hy (by positivity)]
            nlinarith
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right key hT00) hsq.le
      _ = 2 * T0 / (Real.sin δ * η) / Real.sqrt n := by
          rw [eq_div_iff hsq.ne', mul_comm, ← mul_assoc, hsn]
          field_simp
  -- assemble
  rw [← hsplit, mul_add]
  calc ‖(Real.sqrt n : ℂ) * (∫ s in Icc (s₀ - δ') (s₀ + δ'), f s) + (Real.sqrt n : ℂ) * Tl -
        (lam : ℂ) * ((π : ℂ) / (exp ((θ : ℂ) * I) * (Q0 : ℂ))) ^ (1 / 2 : ℂ)‖
      ≤ ‖(Real.sqrt n : ℂ) * (∫ s in Icc (s₀ - δ') (s₀ + δ'), f s) -
        (lam : ℂ) * ((π : ℂ) / (exp ((θ : ℂ) * I) * (Q0 : ℂ))) ^ (1 / 2 : ℂ)‖ +
        ‖(Real.sqrt n : ℂ) * Tl‖ := by
        rw [show ∀ a b d : ℂ, a + b - d = (a - d) + b from fun a b d => by ring]
        exact norm_add_le _ _
    _ ≤ ((1 + 1 / δ') / c + 1 * 1 / c ^ 2) / Real.sqrt n +
        2 * T0 / (Real.sin δ * η) / Real.sqrt n := by
        gcongr
        rw [norm_mul, norm_real, Real.norm_of_nonneg hsq.le]; exact htail'
    _ = _ := by ring

/-- `μ(λ)` of DLMF 11.11.12 is the phase at the saddle. -/
theorem struveSc_angerMu_eq {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    DLMF.Struve.angerMu (lam : ℂ) = ((struveSc_phiR lam (struveSc_s0 lam) : ℝ) : ℂ) := by
  have hu : 0 < Real.sqrt (1 - lam ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have e1 : (1 - (lam : ℂ) ^ 2) ^ (1 / 2 : ℂ) = ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ) := by
    rw [show 1 - (lam : ℂ) ^ 2 = ((1 - lam ^ 2 : ℝ) : ℂ) by push_cast; ring,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, ← ofReal_cpow (by nlinarith),
      Real.sqrt_eq_rpow]
  have hpos : 0 < (1 + Real.sqrt (1 - lam ^ 2)) / lam := by positivity
  rw [DLMF.Struve.angerMu, e1, show (1 + ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ)) / (lam : ℂ) =
    (((1 + Real.sqrt (1 - lam ^ 2)) / lam : ℝ) : ℂ) by push_cast; ring, ← ofReal_log hpos.le,
    ← ofReal_sub]
  congr 1
  rw [struveSc_phiR, Real.arsinh, struveSc_s0, struveSc_sqrt_saddle h0 h1]
  congr 1
  · field_simp
  · congr 1; field_simp; ring

/-- The DLMF 11.11.15 right-hand side as the Laplace leading term. -/
theorem struveSc_inner_rhs {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) {n θ : ℝ} (hn : 0 < n)
    (hθ : |θ| < π) :
    (2 / (π * ((n : ℂ) * exp ((θ : ℂ) * I)))) ^ (1 / 2 : ℂ) *
        exp (-((n : ℂ) * exp ((θ : ℂ) * I)) * DLMF.Struve.angerMu (lam : ℂ)) /
        (1 - (lam : ℂ) ^ 2) ^ (1 / 4 : ℂ) =
      1 / π * (exp (-((n : ℂ) * exp ((θ : ℂ) * I) *
        ((struveSc_phiR lam (struveSc_s0 lam) : ℝ) : ℂ))) *
        ((lam : ℂ) * ((π : ℂ) / (exp ((θ : ℂ) * I) * (struveSc_Q0 lam : ℂ))) ^ (1 / 2 : ℂ) /
          (Real.sqrt n : ℂ))) := by
  have hQ := struveSc_Q0_pos h0 h1
  have hb1 : -π < -θ := by linarith [le_abs_self θ]
  have hb2 : -θ ≤ π := by linarith [neg_abs_le θ]
  rw [struveSc_angerMu_eq h0 h1]
  have e1 : 2 / (π * ((n : ℂ) * exp ((θ : ℂ) * I))) =
      ((2 / (π * n) : ℝ) : ℂ) * exp (((-θ : ℝ) : ℂ) * I) := by
    rw [show ((-θ : ℝ) : ℂ) * I = -((θ : ℂ) * I) by push_cast; ring, exp_neg]
    push_cast; field_simp
  have e2 : (π : ℂ) / (exp ((θ : ℂ) * I) * (struveSc_Q0 lam : ℂ)) =
      ((π / struveSc_Q0 lam : ℝ) : ℂ) * exp (((-θ : ℝ) : ℂ) * I) := by
    rw [show ((-θ : ℝ) : ℂ) * I = -((θ : ℂ) * I) by push_cast; ring, exp_neg]
    push_cast; field_simp
  rw [e1, e2, ofReal_mul_exp_cpow (by positivity) hb1 hb2,
    ofReal_mul_exp_cpow (by positivity) hb1 hb2]
  have r1 : ((2 / (π * n) : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt (2 / (π * n)) : ℝ) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, ← ofReal_cpow (by positivity),
      Real.sqrt_eq_rpow]
  have r2 : ((π / struveSc_Q0 lam : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
      ((Real.sqrt (π / struveSc_Q0 lam) : ℝ) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, ← ofReal_cpow (by positivity),
      Real.sqrt_eq_rpow]
  have hu : 0 < Real.sqrt (1 - lam ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have r3 : (1 - (lam : ℂ) ^ 2) ^ (1 / 4 : ℂ) = ((Real.sqrt (Real.sqrt (1 - lam ^ 2)) : ℝ) : ℂ) := by
    rw [show 1 - (lam : ℂ) ^ 2 = ((1 - lam ^ 2 : ℝ) : ℂ) by push_cast; ring,
      show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by push_cast; rfl, ← ofReal_cpow (by nlinarith),
      Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by nlinarith)]
    norm_num
  rw [r1, r2, r3]
  -- the real identity
  have hQ0 : struveSc_Q0 lam = lam ^ 2 * Real.sqrt (1 - lam ^ 2) / 2 := by
    rw [struveSc_Q0, struveSc_s0]; field_simp
  have key : Real.sqrt (2 / (π * n)) / Real.sqrt (Real.sqrt (1 - lam ^ 2)) =
      1 / π * (lam * Real.sqrt (π / struveSc_Q0 lam) / Real.sqrt n) := by
    have hL : 0 ≤ Real.sqrt (2 / (π * n)) / Real.sqrt (Real.sqrt (1 - lam ^ 2)) := by positivity
    have hR : 0 ≤ 1 / π * (lam * Real.sqrt (π / struveSc_Q0 lam) / Real.sqrt n) := by positivity
    rw [← sq_eq_sq₀ hL hR]
    simp only [div_pow, mul_pow]
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt hu.le, Real.sq_sqrt (by positivity),
      Real.sq_sqrt hn.le, hQ0]
    field_simp
  have hn' : (Real.sqrt n : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 hn).ne'
  have hs4 : ((Real.sqrt (Real.sqrt (1 - lam ^ 2)) : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.2 (Real.sqrt_pos.2 hu).ne'
  have keyC : ((Real.sqrt (2 / (π * n)) : ℝ) : ℂ) =
      1 / π * ((lam : ℂ) * ((Real.sqrt (π / struveSc_Q0 lam) : ℝ) : ℂ) / (Real.sqrt n : ℂ)) *
        ((Real.sqrt (Real.sqrt (1 - lam ^ 2)) : ℝ) : ℂ) := by
    rw [div_eq_iff (Real.sqrt_pos.2 hu).ne'] at key
    rw [key]; push_cast; ring
  rw [keyC]
  field_simp


theorem struveSc_one_sub_recip_sqrt (s : ℝ) : |1 - (Real.sqrt (1 + s ^ 2))⁻¹| ≤ s ^ 2 := by
  have hS := struveSc_sqrt_pos s
  have h1 := struveSc_one_le_sqrt s
  have h2 := struveSc_sqrt_sq s
  have hinv : (Real.sqrt (1 + s ^ 2))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
  rw [abs_of_nonneg (by linarith)]
  have : 1 - (Real.sqrt (1 + s ^ 2))⁻¹ = (Real.sqrt (1 + s ^ 2) - 1) / Real.sqrt (1 + s ^ 2) := by
    field_simp
  rw [this, div_le_iff₀ hS]
  nlinarith

theorem struveSc_phiR_one_sub_cube {s : ℝ} (hs : 0 ≤ s) :
    |struveSc_phiR 1 s - s ^ 3 / 6| ≤ 3 / 10 * s ^ 5 := by
  have ha : |(0 : ℝ)| < π / 2 := by rw [abs_zero]; positivity
  have h := struveSc_phase_one_sub_cube (a := 0) (K := 1) ha (fun t ht => by
    simp only [neg_zero, ofReal_zero, zero_mul, exp_zero, mul_one]
    rw [struveSc_q_ofReal, norm_real, Real.norm_of_nonneg (inv_nonneg.2 (struveSc_sqrt_pos t).le)]
    exact inv_le_one_of_one_le₀ (struveSc_one_le_sqrt t)) hs
  simp only [neg_zero, ofReal_zero, zero_mul, exp_zero, mul_one] at h
  rw [struveSc_phase_ofReal] at h
  have h' : ‖((struveSc_phiR 1 s - s ^ 3 / 6 : ℝ) : ℂ)‖ ≤ (1 / 2 + 1) / 5 * s ^ 5 := by
    push_cast; exact h
  rw [norm_real, Real.norm_eq_abs] at h'
  linarith

theorem struveSc_cubic_absorb {M u : ℝ} (hM : 0 ≤ M) (hu : 0 ≤ u) :
    M * u - u ^ 3 / 48 ≤ M * (48 * M + 1) / 2 := by
  rcases le_or_gt (48 * M) (u ^ 2) with h | h
  · have : M * u ≤ u ^ 3 / 48 := by nlinarith
    nlinarith [mul_nonneg hM (by positivity : (0 : ℝ) ≤ 48 * M + 1)]
  · have hu2 : u ≤ (48 * M + 1) / 2 := by nlinarith [sq_nonneg (u - 1)]
    have : M * u ≤ M * ((48 * M + 1) / 2) := mul_le_mul_of_nonneg_left hu2 hM
    nlinarith [pow_nonneg hu 3]

theorem struveSc_X_split {ν τ M s : ℝ} (hτ : 0 < τ) (hντ : ν = τ ^ 3) (hM : 0 ≤ M)
    (hτM : 48 * M ≤ τ ^ 2) (hs : 0 ≤ s) :
    Real.exp (-(ν * (s ^ 3 / (12 * (1 + s ^ 2)))) + M * τ * s) ≤
      Real.exp (M * (48 * M + 1) / 2) * Real.exp (-(ν / 48 * s ^ 3)) +
        Real.exp (-(ν / 48 * s)) := by
  have hν : 0 ≤ ν := by rw [hντ]; positivity
  rcases le_total s 1 with h | h
  · have h1 : ν * (s ^ 3 / 24) ≤ ν * (s ^ 3 / (12 * (1 + s ^ 2))) := by
      refine mul_le_mul_of_nonneg_left ?_ hν
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [pow_nonneg hs 3, mul_le_mul_of_nonneg_left (pow_le_one₀ hs h : s ^ 2 ≤ 1)
        (pow_nonneg hs 3)]
    have h2 := struveSc_cubic_absorb hM (mul_nonneg hτ.le hs)
    have h3 : -(ν * (s ^ 3 / (12 * (1 + s ^ 2)))) + M * τ * s ≤
        M * (48 * M + 1) / 2 + -(ν / 48 * s ^ 3) := by
      have : (τ * s) ^ 3 = ν * s ^ 3 := by rw [hντ]; ring
      nlinarith
    calc Real.exp (-(ν * (s ^ 3 / (12 * (1 + s ^ 2)))) + M * τ * s)
        ≤ Real.exp (M * (48 * M + 1) / 2 + -(ν / 48 * s ^ 3)) := Real.exp_le_exp.2 h3
      _ = Real.exp (M * (48 * M + 1) / 2) * Real.exp (-(ν / 48 * s ^ 3)) := Real.exp_add _ _
      _ ≤ _ := le_add_of_nonneg_right (Real.exp_pos _).le
  · have h1 : ν * (s / 24) ≤ ν * (s ^ 3 / (12 * (1 + s ^ 2))) := by
      refine mul_le_mul_of_nonneg_left ?_ hν
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [one_le_pow₀ h (n := 2), mul_le_mul_of_nonneg_left (one_le_pow₀ h (n := 2) :
        1 ≤ s ^ 2) hs]
    have h2 : M * τ * s ≤ ν / 48 * s := by
      have : M * τ ≤ ν / 48 := by
        rw [hντ]; nlinarith [mul_le_mul_of_nonneg_left hτM hτ.le]
      exact mul_le_mul_of_nonneg_right this hs
    have h3 : -(ν * (s ^ 3 / (12 * (1 + s ^ 2)))) + M * τ * s ≤ -(ν / 48 * s) := by
      nlinarith
    calc Real.exp (-(ν * (s ^ 3 / (12 * (1 + s ^ 2)))) + M * τ * s)
        ≤ Real.exp (-(ν / 48 * s)) := Real.exp_le_exp.2 h3
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

/-- DLMF 11.10.4 on the real contour for `𝐀_{-ν}(z)`, `ν` real, `re z > 0`. -/
theorem struveSc_angerA_shift (ν : ℝ) {z : ℂ} (hz : 0 < z.re) :
    angerA (-(ν : ℂ)) z = 1 / π * ∫ s in Ioi (0 : ℝ),
      exp (-((ν : ℂ) * ((struveSc_phiR 1 s : ℝ) : ℂ)) - (z - ν) * s) *
        (((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ) := by
  have ha : |(0 : ℝ)| < π / 2 := by rw [abs_zero]; positivity
  have hθ : |(-(0 : ℝ))| < π / 2 := by rw [neg_zero, abs_zero]; positivity
  have hz' : 0 < (z * exp (((-(0 : ℝ) : ℝ) : ℂ) * I)).re := by
    simp only [neg_zero, ofReal_zero, zero_mul, exp_zero, mul_one]; exact hz
  rw [struveAs_angerA_eq_rot (-(ν : ℂ)) hθ hz', struveAs_rotInt]
  simp only [neg_zero, ofReal_zero, zero_mul, exp_zero, mul_one, one_mul]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have h := struveSc_integrand_eq 1 ha (ν : ℂ) (le_of_lt hr)
  simp only [neg_zero, ofReal_zero, zero_mul, exp_zero, mul_one, ofReal_one, one_mul] at h
  rw [struveSc_phase_ofReal, struveSc_q_ofReal] at h
  have hsplit : exp (-(z * r)) = exp (-((z - ν) * r)) * exp (-((ν : ℂ) * r)) := by
    rw [← exp_add]; congr 1; ring
  rw [hsplit, mul_assoc, h, ← mul_assoc, ← exp_add]
  congr 2; ring

/-- Rescaling the cubic model integral to the Scorer integral. -/
theorem struveSc_lead_cube {τ : ℝ} (hτ : 0 < τ) (a : ℂ) :
    ∫ s in Ioi (0 : ℝ), exp (-(((τ ^ 3 : ℝ) : ℂ) * (s : ℂ) ^ 3 / 6) - a * τ * s) =
      (((2 : ℝ) ^ (1 / 3 : ℝ) / τ : ℝ) : ℂ) *
        ∫ t in Ioi (0 : ℝ), exp (-(t : ℂ) ^ 3 / 3 + (-(((2 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) * a) * t) := by
  set c : ℝ := (2 : ℝ) ^ (1 / 3 : ℝ) / τ with hc
  have hc0 : 0 < c := by positivity
  have h23 : ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have h := integral_comp_mul_left_Ioi (fun s : ℝ =>
    exp (-(((τ ^ 3 : ℝ) : ℂ) * (s : ℂ) ^ 3 / 6) - a * τ * s)) 0 hc0
  rw [mul_zero] at h
  have hL : (∫ s in Ioi (0 : ℝ), exp (-(((τ ^ 3 : ℝ) : ℂ) * (s : ℂ) ^ 3 / 6) - a * τ * s)) =
      (c : ℂ) * ∫ x in Ioi (0 : ℝ), exp (-(((τ ^ 3 : ℝ) : ℂ) * ((c * x : ℝ) : ℂ) ^ 3 / 6) -
        a * τ * ((c * x : ℝ) : ℂ)) := by
    rw [h, Complex.real_smul, ← mul_assoc, ← ofReal_mul, mul_inv_cancel₀ hc0.ne', ofReal_one,
      one_mul]
  rw [hL]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  congr 1
  have hτc : τ * c = (2 : ℝ) ^ (1 / 3 : ℝ) := by rw [hc]; field_simp
  have e1 : ((τ * c : ℝ) : ℂ) ^ 3 = 2 := by rw [hτc, ← ofReal_pow, h23]; norm_num
  have e2 : ((τ * c : ℝ) : ℂ) = (((2 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) := by rw [hτc]
  push_cast at e1 e2 ⊢
  linear_combination (-(x : ℂ) ^ 3 / 6) * e1 + (-(a * x)) * e2

theorem struveSc_phiR_one_ge {s : ℝ} (hs : 0 ≤ s) :
    s ^ 3 / (12 * (1 + s ^ 2)) ≤ struveSc_phiR 1 s := by
  have ha : |(0 : ℝ)| < π / 2 := by rw [abs_zero]; positivity
  have h := struveSc_re_phase_one_ge ha (ρ := 1) zero_le_one hs
  simp only [neg_zero, ofReal_zero, zero_mul, exp_zero, mul_one, mul_zero, Real.cos_zero,
    one_mul, ofReal_one] at h
  rwa [struveSc_phase_ofReal, ofReal_re] at h

/-- **The main estimate** behind DLMF 11.11.17. -/
theorem struveSc_turnU_est {M : ℝ} (hM : 0 ≤ M) {τ : ℝ} (hτ1 : 1 ≤ τ) (hτM : 48 * M ≤ τ ^ 2)
    {a : ℂ} (ha : ‖a‖ ≤ M) :
    ‖(∫ s in Ioi (0 : ℝ), exp (-(((τ ^ 3 : ℝ) : ℂ) * ((struveSc_phiR 1 s : ℝ) : ℂ)) - a * τ * s) *
        (((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ)) -
      ∫ s in Ioi (0 : ℝ), exp (-(((τ ^ 3 : ℝ) : ℂ) * (s : ℂ) ^ 3 / 6) - a * τ * s)‖ ≤
      (Real.exp (M * (48 * M + 1) / 2) * (16 + 3 / 10 * 768) + 2 * 48 ^ 3 +
        3 / 10 * 120 * 48 ^ 6) / τ ^ 3 := by
  have hτ0 : 0 < τ := by linarith
  set ν : ℝ := τ ^ 3 with hν
  have hν1 : 1 ≤ ν := one_le_pow₀ hτ1
  have hν0 : 0 < ν := by linarith
  set b : ℝ := ν / 48 with hb
  have hb0 : 0 < b := by positivity
  set Cm : ℝ := Real.exp (M * (48 * M + 1) / 2) with hCm
  have hCm0 : 0 < Cm := Real.exp_pos _
  set F : ℝ → ℂ := fun s => exp (-((ν : ℂ) * ((struveSc_phiR 1 s : ℝ) : ℂ)) - a * τ * s) *
    (((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ) with hF
  set G : ℝ → ℂ := fun s => exp (-((ν : ℂ) * (s : ℂ) ^ 3 / 6) - a * τ * s) with hG
  set H : ℝ → ℝ := fun s => (Cm * Real.exp (-(b * s ^ 3)) + Real.exp (-(b * s))) *
    (s ^ 2 + ν * (3 / 10) * s ^ 5) with hH
  have hare : ∀ s : ℝ, 0 ≤ s → (-(a * τ * s)).re ≤ M * τ * s := by
    intro s hs
    rw [neg_re, show a * (τ : ℂ) * (s : ℂ) = ((τ * s : ℝ) : ℂ) * a by push_cast; ring,
      re_ofReal_mul]
    have := neg_le_of_abs_le (abs_re_le_norm a)
    nlinarith [mul_nonneg hτ0.le hs]
  have hbound : ∀ s : ℝ, 0 < s → ‖F s - G s‖ ≤ H s := by
    intro s hs
    set X : ℝ := Real.exp (-(ν * (s ^ 3 / (12 * (1 + s ^ 2)))) + M * τ * s) with hX
    have hlow := struveSc_phiR_one_ge hs.le
    have hA : (-((ν : ℂ) * ((struveSc_phiR 1 s : ℝ) : ℂ)) - a * τ * s).re ≤
        -(ν * (s ^ 3 / (12 * (1 + s ^ 2)))) + M * τ * s := by
      rw [sub_eq_add_neg, add_re, neg_re, ← ofReal_mul, ofReal_re]
      have := hare s hs.le
      nlinarith
    have hB : (-((ν : ℂ) * (s : ℂ) ^ 3 / 6) - a * τ * s).re ≤
        -(ν * (s ^ 3 / (12 * (1 + s ^ 2)))) + M * τ * s := by
      rw [sub_eq_add_neg, add_re, show -((ν : ℂ) * (s : ℂ) ^ 3 / 6) = ((-(ν * s ^ 3 / 6) : ℝ) : ℂ) by
        push_cast; ring, ofReal_re]
      have := hare s hs.le
      have h1 : s ^ 3 / (12 * (1 + s ^ 2)) ≤ s ^ 3 / 6 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [pow_nonneg hs.le 3, mul_nonneg (pow_nonneg hs.le 3) (sq_nonneg s)]
      have : ν * (s ^ 3 / (12 * (1 + s ^ 2))) ≤ ν * (s ^ 3 / 6) := mul_le_mul_of_nonneg_left h1 hν0.le
      linarith
    have hsplit : F s - G s = exp (-((ν : ℂ) * ((struveSc_phiR 1 s : ℝ) : ℂ)) - a * τ * s) *
        ((((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ) - 1) +
        (exp (-((ν : ℂ) * ((struveSc_phiR 1 s : ℝ) : ℂ)) - a * τ * s) -
          exp (-((ν : ℂ) * (s : ℂ) ^ 3 / 6) - a * τ * s)) := by
      simp only [hF, hG]; ring
    have h1 : ‖exp (-((ν : ℂ) * ((struveSc_phiR 1 s : ℝ) : ℂ)) - a * τ * s)‖ ≤ X := by
      rw [norm_exp]; exact Real.exp_le_exp.2 hA
    have h2 : ‖(((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ) - 1‖ ≤ s ^ 2 := by
      rw [← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_sub_comm]
      exact struveSc_one_sub_recip_sqrt s
    have h3 : ‖(-((ν : ℂ) * ((struveSc_phiR 1 s : ℝ) : ℂ)) - a * τ * s) -
        (-((ν : ℂ) * (s : ℂ) ^ 3 / 6) - a * τ * s)‖ ≤ ν * (3 / 10 * s ^ 5) := by
      have : (-((ν : ℂ) * ((struveSc_phiR 1 s : ℝ) : ℂ)) - a * τ * s) -
          (-((ν : ℂ) * (s : ℂ) ^ 3 / 6) - a * τ * s) =
          ((-(ν * (struveSc_phiR 1 s - s ^ 3 / 6)) : ℝ) : ℂ) := by push_cast; ring
      rw [this, norm_real, Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos hν0]
      exact mul_le_mul_of_nonneg_left (struveSc_phiR_one_sub_cube hs.le) hν0.le
    have h4 := struveSc_norm_exp_sub_exp_le hA hB
    have hXs := struveSc_X_split hτ0 hν hM hτM hs.le
    rw [hsplit]
    calc _ ≤ ‖exp (-((ν : ℂ) * ((struveSc_phiR 1 s : ℝ) : ℂ)) - a * τ * s)‖ *
          ‖(((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ) - 1‖ +
          ‖(-((ν : ℂ) * ((struveSc_phiR 1 s : ℝ) : ℂ)) - a * τ * s) -
            (-((ν : ℂ) * (s : ℂ) ^ 3 / 6) - a * τ * s)‖ * X := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul]; gcongr
      _ ≤ X * s ^ 2 + ν * (3 / 10 * s ^ 5) * X := by gcongr
      _ = X * (s ^ 2 + ν * (3 / 10) * s ^ 5) := by ring
      _ ≤ H s := by
          simp only [hH]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          simpa [hX, hb, hCm] using hXs
  obtain ⟨i32, e32⟩ := struveSc_integral_pow_exp_cube 2 hb0
  obtain ⟨i35, e35⟩ := struveSc_integral_pow_exp_cube 5 hb0
  obtain ⟨i12, e12⟩ := struveSc_integral_pow_exp 2 hb0
  obtain ⟨i15, e15⟩ := struveSc_integral_pow_exp 5 hb0
  have hsplitH : ∀ s : ℝ, H s = (Cm * (Real.exp (-(b * s ^ 3)) * s ^ 2) +
      Cm * (ν * (3 / 10)) * (Real.exp (-(b * s ^ 3)) * s ^ 5)) +
      ((Real.exp (-(b * s)) * s ^ 2) + ν * (3 / 10) * (Real.exp (-(b * s)) * s ^ 5)) := by
    intro s; simp only [hH]; ring
  have j1 := (i32.const_mul Cm).add (i35.const_mul (Cm * (ν * (3 / 10))))
  have j2 := i12.add (i15.const_mul (ν * (3 / 10)))
  have hHi : IntegrableOn H (Ioi 0) := by
    refine IntegrableOn.congr_fun (j1.add j2) (fun r _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply]; exact (hsplitH r).symm
  have k1 := integral_add (i32.const_mul Cm) (i35.const_mul (Cm * (ν * (3 / 10))))
  have k2 := integral_add i12 (i15.const_mul (ν * (3 / 10)))
  have k3 := integral_add j1 j2
  simp only [Pi.add_apply] at k3
  have hHint : ∫ s in Ioi (0 : ℝ), H s =
      (Cm * (b⁻¹ * (1 / 3)) + Cm * (ν * (3 / 10)) * (1 / b ^ 2 * (1 / 3))) +
      (2 / b ^ 3 + ν * (3 / 10) * (120 / b ^ 6)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun r _ => hsplitH r), k3, k1, k2,
      integral_const_mul, integral_const_mul, integral_const_mul, e32, e35, e12, e15]
    have g1 : Real.Gamma ((((2 : ℕ) : ℝ) + 1) / 3) = 1 := by
      rw [show (((2 : ℕ) : ℝ) + 1) / 3 = 1 by norm_num, Real.Gamma_one]
    have g2 : Real.Gamma ((((5 : ℕ) : ℝ) + 1) / 3) = 1 := by
      rw [show (((5 : ℕ) : ℝ) + 1) / 3 = 1 + 1 by norm_num, Real.Gamma_add_one one_ne_zero,
        Real.Gamma_one, mul_one]
    have b1 : b ^ (-(((2 : ℕ) : ℝ) + 1) / 3) = b⁻¹ := by
      rw [show (-(((2 : ℕ) : ℝ) + 1) / 3) = -1 by norm_num, Real.rpow_neg_one]
    have b2 : b ^ (-(((5 : ℕ) : ℝ) + 1) / 3) = 1 / b ^ 2 := by
      rw [show (-(((5 : ℕ) : ℝ) + 1) / 3) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hb0.le,
        Real.rpow_natCast, one_div]
    rw [g1, g2, b1, b2]
    norm_num [Nat.factorial]
  -- integrability and assembly
  have hSc : Continuous fun s : ℝ => (Real.sqrt (1 + s ^ 2))⁻¹ :=
    ((Real.continuous_sqrt.comp (by fun_prop : Continuous fun s : ℝ => 1 + s ^ 2)).inv₀
      fun s => (struveSc_sqrt_pos s).ne')
  have hFc : Continuous F := by
    have := struveSc_continuous_phiR 1
    simp only [hF]
    exact (continuous_exp.comp ((continuous_const.mul (continuous_ofReal.comp this)).neg.sub
      (continuous_const.mul continuous_ofReal))).mul (continuous_ofReal.comp hSc)
  have hGc : Continuous G := by simp only [hG]; fun_prop
  have hGi : IntegrableOn G (Ioi 0) := by
    obtain ⟨i30, -⟩ := struveSc_integral_pow_exp_cube 0 hb0
    obtain ⟨i10, -⟩ := struveSc_integral_pow_exp 0 hb0
    refine Integrable.mono' ((i30.const_mul Cm).add i10) hGc.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_))
    have hs0 : (0 : ℝ) ≤ s := le_of_lt hs
    simp only [Pi.add_apply, pow_zero, mul_one]
    have hXs := struveSc_X_split hτ0 hν hM hτM hs0
    refine le_trans ?_ (by simpa [hb, hCm] using hXs)
    rw [hG, norm_exp, sub_eq_add_neg, add_re,
      show -((ν : ℂ) * (s : ℂ) ^ 3 / 6) = ((-(ν * s ^ 3 / 6) : ℝ) : ℂ) by push_cast; ring,
      ofReal_re]
    refine Real.exp_le_exp.2 ?_
    have := hare s hs0
    have h1 : s ^ 3 / (12 * (1 + s ^ 2)) ≤ s ^ 3 / 6 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [pow_nonneg hs0 3, mul_nonneg (pow_nonneg hs0 3) (sq_nonneg s)]
    have : ν * (s ^ 3 / (12 * (1 + s ^ 2))) ≤ ν * (s ^ 3 / 6) :=
      mul_le_mul_of_nonneg_left h1 hν0.le
    linarith
  have hdi : IntegrableOn (fun s => F s - G s) (Ioi 0) :=
    Integrable.mono' hHi ((hFc.sub hGc).aestronglyMeasurable) ((ae_restrict_iff'
      measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => hbound s hs))
  have hFi : IntegrableOn F (Ioi 0) := by
    have : IntegrableOn (fun s => (F s - G s) + G s) (Ioi 0) := hdi.add hGi
    refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
    simp
  change ‖(∫ s in Ioi (0 : ℝ), F s) - ∫ s in Ioi (0 : ℝ), G s‖ ≤ _
  rw [← integral_sub hFi hGi]
  refine (norm_integral_le_of_norm_le hHi ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun s hs => hbound s hs))).trans ?_
  rw [hHint, hb]
  have hν3 : ν ≤ ν ^ 3 := le_self_pow₀ hν1 (by norm_num)
  have hν6 : ν ≤ ν ^ 5 := le_self_pow₀ hν1 (by norm_num)
  rw [le_div_iff₀ hν0]
  have e1 : (Cm * ((ν / 48)⁻¹ * (1 / 3)) + Cm * (ν * (3 / 10)) * (1 / (ν / 48) ^ 2 * (1 / 3))) * ν
      = Cm * (16 + 3 / 10 * 768) := by field_simp; ring
  have e2 : (2 / (ν / 48) ^ 3 + ν * (3 / 10) * (120 / (ν / 48) ^ 6)) * ν =
      2 * 48 ^ 3 / ν ^ 2 + 3 / 10 * 120 * 48 ^ 6 / ν ^ 4 := by field_simp
  have f1 : 2 * 48 ^ 3 / ν ^ 2 ≤ 2 * 48 ^ 3 := div_le_self (by norm_num) (one_le_pow₀ hν1)
  have f2 : 3 / 10 * 120 * 48 ^ 6 / ν ^ 4 ≤ 3 / 10 * 120 * 48 ^ 6 :=
    div_le_self (by norm_num) (one_le_pow₀ hν1)
  rw [add_mul, e1, e2]
  linarith

end StruveScaled

/-- angerA scaled outer equiv. -/
@[dlmf 11.11.E14]
theorem angerA_scaled_outer_equiv {lam : ℝ} (hlam : 1 < lam) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun ν : ℂ => angerA (-ν) (lam*ν)) ~[sector (π-δ)] (fun ν => 1/(π*ν*(lam-1))) := by
  obtain ⟨K, hK0, hK⟩ := struveSc_q_bounds hδ
  set κ0 : ℝ := (lam - 1) * Real.sin (δ / 2) with hκ0
  have hs : 0 < Real.sin (δ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hκ0p : 0 < κ0 := mul_pos (by linarith) hs
  set C : ℝ := 1 / π * (K / κ0 ^ 2 + K / κ0 ^ 3) with hC
  have hmain : ∀ ν : ℂ, ν ≠ 0 → |arg ν| ≤ π - δ →
      ‖angerA (-ν) (lam * ν) - 1 / (π * ν * (lam - 1))‖ ≤ C / ‖ν‖ ^ 2 := by
    intro ν hν0 harg
    set a : ℝ := arg ν / 2 with ha
    have ha' : |a| ≤ (π - δ) / 2 := by rw [ha, abs_div, abs_two]; linarith
    have ha2 : |a| < π / 2 := by linarith
    set ρ : ℝ := ‖ν‖ with hρ
    have hρ0 : 0 < ρ := norm_pos_iff.2 hν0
    have hνe : ν = (ρ : ℂ) * exp ((2 * a : ℝ) * I) := by
      rw [ha, show 2 * (arg ν / 2) = arg ν by ring, hρ, norm_mul_exp_arg_mul_I]
    have hcos : Real.sin (δ / 2) ≤ Real.cos a := by
      rw [← Real.cos_abs, ← Real.cos_pi_div_two_sub]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg a) (by linarith) (by linarith)
    have hθ : |(-a)| < π / 2 := by rwa [abs_neg]
    have hz : 0 < ((lam : ℂ) * ν * exp (((-a : ℝ) : ℂ) * I)).re := by
      rw [hνe, show (lam : ℂ) * ((ρ : ℂ) * exp ((2 * a : ℝ) * I)) * exp (((-a : ℝ) : ℂ) * I) =
        ((lam * ρ : ℝ) : ℂ) * exp ((a : ℂ) * I) by
          rw [mul_assoc, mul_assoc, ← exp_add]; push_cast; ring_nf, re_ofReal_mul,
        exp_ofReal_mul_I_re]
      exact mul_pos (mul_pos (by linarith) hρ0) (struveSc_cos_pos ha2)
    have hrot := struveAs_angerA_eq_rot (-ν) hθ hz
    have hest := struveSc_integral_est hlam ha2 (fun s hs => hK a ha' s hs) hρ0
    rw [← hνe] at hest
    have hdiff : angerA (-ν) (lam * ν) - 1 / (π * ν * (lam - 1)) =
        1 / π * (exp (((-a : ℝ) : ℂ) * I) * (∫ r in Ioi (0 : ℝ),
          exp (-((lam : ℂ) * ν * exp (((-a : ℝ) : ℂ) * I) * r)) *
          struveAs_kernel (-ν) ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I))) -
          1 / (ν * ((lam : ℂ) - 1))) := by
      rw [hrot, struveAs_rotInt]
      have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_pos.ne'
      field_simp
    rw [hdiff, norm_mul, norm_div, norm_one, norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    have hκa : κ0 ≤ (lam - 1) * Real.cos a := mul_le_mul_of_nonneg_left hcos (by linarith)
    calc 1 / π * ‖_‖ ≤ 1 / π * ((K / ((lam - 1) * Real.cos a) ^ 2 +
          K / ((lam - 1) * Real.cos a) ^ 3) / ρ ^ 2) :=
          mul_le_mul_of_nonneg_left hest (by positivity)
      _ ≤ 1 / π * ((K / κ0 ^ 2 + K / κ0 ^ 3) / ρ ^ 2) := by
          gcongr
      _ = C / ρ ^ 2 := by rw [hC]; ring
  rw [IsEquivalent, isLittleO_iff]
  intro ε hε
  have hl0 : (0 : ℝ) < lam - 1 := by linarith
  set R : ℝ := max 1 (C * π * (lam - 1) / ε) with hR
  have hev : ∀ᶠ ν in sector (π - δ), R ≤ ‖ν‖ ∧ ν ∈ {z : ℂ | z ≠ 0 ∧ |arg z| ≤ π - δ} :=
    ((tendsto_norm_sector (π - δ)).eventually (eventually_ge_atTop R)).and
      (mem_inf_of_right (mem_principal_self _))
  filter_upwards [hev] with ν ⟨hνR, hν0, harg⟩
  have hρ1 : 1 ≤ ‖ν‖ := (le_max_left _ _).trans hνR
  have hρ0 : 0 < ‖ν‖ := by linarith
  have hv : ‖1 / (π * ν * (lam - 1))‖ = 1 / (π * ‖ν‖ * (lam - 1)) := by
    rw [norm_div, norm_one, norm_mul, norm_mul, norm_real, Real.norm_of_nonneg Real.pi_pos.le,
      show (lam : ℂ) - 1 = ((lam - 1 : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_of_nonneg hl0.le]
  simp only [Pi.sub_apply]
  rw [hv]
  refine (hmain ν hν0 harg).trans ?_
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have hRε : C * π * (lam - 1) / ε ≤ ‖ν‖ := (le_max_right _ _).trans hνR
  rw [div_le_iff₀ hε] at hRε
  rw [div_le_iff₀ (by positivity)]
  field_simp
  nlinarith [Real.pi_pos]

/-- angerA scaled inner equiv. -/
@[dlmf 11.11.E15]
theorem angerA_scaled_inner_equiv {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) :
    (fun ν : ℂ => angerA (-ν) (lam*ν)) ~[sector (π/2-δ)] (fun ν => (2/(π*ν))^(1/2:ℂ)*exp (-ν*angerMu lam)/(1-lam^2:ℂ)^(1/4:ℂ)) := by
  obtain ⟨C, n₀, hn₀, hC⟩ := struveSc_inner_est h0 h1 hδ hδπ
  set φ₀ := struveSc_phiR lam (struveSc_s0 lam) with hφ₀
  set Q0 := struveSc_Q0 lam with hQ0
  have hQ := struveSc_Q0_pos h0 h1
  set K1 : ℝ := lam * Real.sqrt (π / Q0) with hK1
  have hK1p : 0 < K1 := by rw [hK1]; positivity
  have hmain : ∀ ν : ℂ, ν ≠ 0 → |arg ν| ≤ π / 2 - δ → n₀ ≤ ‖ν‖ →
      ‖angerA (-ν) (lam * ν) - (2/(π*ν))^(1/2:ℂ)*exp (-ν*angerMu lam)/(1-lam^2:ℂ)^(1/4:ℂ)‖ ≤
        |C| / K1 / Real.sqrt ‖ν‖ *
          ‖(2/(π*ν))^(1/2:ℂ)*exp (-ν*angerMu lam)/(1-lam^2:ℂ)^(1/4:ℂ)‖ := by
    intro ν hν0 harg hn
    set n := ‖ν‖ with hn'
    set θ := arg ν with hθ'
    have hn0 : 0 < n := norm_pos_iff.2 hν0
    have hνe : ν = (n : ℂ) * exp ((θ : ℂ) * I) := (norm_mul_exp_arg_mul_I ν).symm
    have hθπ : |θ| < π := by linarith [Real.pi_pos]
    have hcos := struveSc_cos_ge hδ.le hδπ harg
    have hsδ : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
    have hre : 0 < ν.re := by
      rw [hνe, re_ofReal_mul, exp_ofReal_mul_I_re]; nlinarith
    have hrep := struveSc_angerA_real h0 hre
    have hfac : (∫ s in Ioi (0 : ℝ), exp (-(ν * ((struveSc_phiR lam s : ℝ) : ℂ))) *
        (((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ)) = exp (-(ν * (φ₀ : ℂ))) *
        ∫ s in Ioi (0 : ℝ), exp (-(ν * ((struveSc_phiR lam s - φ₀ : ℝ) : ℂ))) *
          (((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
      rw [← mul_assoc, ← exp_add]; congr 2; push_cast; ring
    have hrhs := struveSc_inner_rhs h0 h1 hn0 hθπ
    rw [← hνe] at hrhs
    rw [hrhs, hrep, hfac]
    set I0 := ∫ s in Ioi (0 : ℝ), exp (-(ν * ((struveSc_phiR lam s - φ₀ : ℝ) : ℂ))) *
          (((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ) with hI0
    set L := (lam : ℂ) * ((π : ℂ) / (exp ((θ : ℂ) * I) * (Q0 : ℂ))) ^ (1 / 2 : ℂ) with hL
    have hest := hC n θ hn harg
    rw [← hνe] at hest
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
    have hsqc : (Real.sqrt n : ℂ) ≠ 0 := ofReal_ne_zero.2 hsq.ne'
    have hLn : ‖L‖ = K1 := by
      rw [hL, norm_mul, norm_real, Real.norm_of_nonneg h0.le,
        show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, norm_cpow_real, norm_div,
        norm_mul, norm_exp_ofReal_mul_I, one_mul, norm_real, norm_real,
        Real.norm_of_nonneg Real.pi_pos.le, Real.norm_of_nonneg hQ.le, ← Real.sqrt_eq_rpow, hK1]
    have hdiff : 1 / π * (exp (-(ν * (φ₀ : ℂ))) * I0) - 1 / π * (exp (-(ν * (φ₀ : ℂ))) *
        (L / (Real.sqrt n : ℂ))) = 1 / π * exp (-(ν * (φ₀ : ℂ))) *
          (((Real.sqrt n : ℂ) * I0 - L) / (Real.sqrt n : ℂ)) := by
      field_simp
    rw [hdiff]
    have hE : 0 < ‖1 / (π : ℂ) * exp (-(ν * (φ₀ : ℂ)))‖ := by
      rw [norm_mul]; refine mul_pos ?_ (by rw [norm_exp]; exact Real.exp_pos _)
      rw [norm_div, norm_one, norm_real, Real.norm_of_nonneg Real.pi_pos.le]; positivity
    have hRn : ‖1 / (π : ℂ) * (exp (-(ν * (φ₀ : ℂ))) * (L / (Real.sqrt n : ℂ)))‖ =
        ‖1 / (π : ℂ) * exp (-(ν * (φ₀ : ℂ)))‖ * (K1 / Real.sqrt n) := by
      rw [← mul_assoc, norm_mul, norm_div, hLn, norm_real, Real.norm_of_nonneg hsq.le]
    have hLn' : ‖1 / (π : ℂ) * exp (-(ν * (φ₀ : ℂ))) *
        (((Real.sqrt n : ℂ) * I0 - L) / (Real.sqrt n : ℂ))‖ =
        ‖1 / (π : ℂ) * exp (-(ν * (φ₀ : ℂ)))‖ * (‖(Real.sqrt n : ℂ) * I0 - L‖ / Real.sqrt n) := by
      rw [norm_mul, norm_div, norm_real, Real.norm_of_nonneg hsq.le]
    rw [hRn, hLn']
    have h2 : ‖(Real.sqrt n : ℂ) * I0 - L‖ / Real.sqrt n ≤ |C| / K1 / Real.sqrt n *
        (K1 / Real.sqrt n) := by
      rw [div_le_iff₀ hsq]
      calc ‖(Real.sqrt n : ℂ) * I0 - L‖ ≤ C / Real.sqrt n := hest
        _ ≤ |C| / Real.sqrt n := by gcongr; exact le_abs_self C
        _ = |C| / K1 / Real.sqrt n * (K1 / Real.sqrt n) * Real.sqrt n := by
          field_simp
    calc ‖1 / (π : ℂ) * exp (-(ν * (φ₀ : ℂ)))‖ * (‖(Real.sqrt n : ℂ) * I0 - L‖ / Real.sqrt n)
        ≤ ‖1 / (π : ℂ) * exp (-(ν * (φ₀ : ℂ)))‖ * (|C| / K1 / Real.sqrt n *
          (K1 / Real.sqrt n)) := by gcongr
      _ = _ := by ring
  rw [IsEquivalent, isLittleO_iff]
  intro ε hε
  set R : ℝ := max n₀ ((|C| / K1 / ε) ^ 2 + 1) with hR
  have hev : ∀ᶠ ν in sector (π / 2 - δ), R ≤ ‖ν‖ ∧
      ν ∈ {z : ℂ | z ≠ 0 ∧ |arg z| ≤ π / 2 - δ} :=
    ((tendsto_norm_sector (π / 2 - δ)).eventually (eventually_ge_atTop R)).and
      (mem_inf_of_right (mem_principal_self _))
  filter_upwards [hev] with ν ⟨hνR, hν0, harg⟩
  have hn := (le_max_left _ _).trans hνR
  have hn2 : (|C| / K1 / ε) ^ 2 + 1 ≤ ‖ν‖ := (le_max_right _ _).trans hνR
  simp only [Pi.sub_apply]
  refine (hmain ν hν0 harg hn).trans ?_
  gcongr
  have hn0 : 0 < ‖ν‖ := norm_pos_iff.2 hν0
  have hsq : 0 < Real.sqrt ‖ν‖ := Real.sqrt_pos.2 hn0
  rw [div_le_iff₀ hsq]
  have : |C| / K1 / ε < Real.sqrt ‖ν‖ := by
    rw [show |C| / K1 / ε = Real.sqrt ((|C| / K1 / ε) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_lt_sqrt (by positivity) (by linarith)
  rw [div_lt_iff₀ hε] at this
  linarith

/-- angerA turning equiv. -/
@[dlmf 11.11.E16]
theorem angerA_turning_equiv {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun ν : ℂ => angerA (-ν) ν) ~[sector (π-δ)] (fun ν => 2^(4/3:ℂ)/(3^(7/6:ℂ)*Gamma (2/3)*ν^(1/3:ℂ))) := by
  obtain ⟨K, hK0, hK⟩ := struveSc_q_bounds hδ
  set s0 : ℝ := Real.sin (δ / 2) with hs0
  have hs : 0 < s0 := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  set Cst : ℝ := K * ((s0 / 24) ^ (-(2 / 3 : ℝ)) * (1 / 3) * Real.Gamma (2 / 3) +
      1 / (s0 / 24) ^ 2) + (1 / 2 + K) / 5 * (1 / (3 * (s0 / 24) ^ 2) + 120 / (s0 / 24) ^ 6)
    with hCst
  have hCst0 : 0 ≤ Cst := by
    have : 0 < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)
    rw [hCst]; positivity
  have hmain : ∀ ν : ℂ, ν ≠ 0 → |arg ν| ≤ π - δ → 1 ≤ ‖ν‖ →
      ‖angerA (-ν) ν - 2^(4/3:ℂ)/(3^(7/6:ℂ)*Gamma (2/3)*ν^(1/3:ℂ))‖ ≤
        1 / π * Cst * ‖ν‖ ^ (-(2 / 3 : ℝ)) := by
    intro ν hν0 harg hρ1
    set a : ℝ := arg ν / 2 with ha
    have ha' : |a| ≤ (π - δ) / 2 := by rw [ha, abs_div, abs_two]; linarith
    have ha2 : |a| < π / 2 := by linarith
    set ρ : ℝ := ‖ν‖ with hρ
    have hρ0 : 0 < ρ := norm_pos_iff.2 hν0
    have hνe : ν = (ρ : ℂ) * exp ((2 * a : ℝ) * I) := by
      rw [ha, show 2 * (arg ν / 2) = arg ν by ring, hρ, norm_mul_exp_arg_mul_I]
    have hcos : Real.sin (δ / 2) ≤ Real.cos a := by
      rw [← Real.cos_abs, ← Real.cos_pi_div_two_sub]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg a) (by linarith) (by linarith)
    have hθ : |(-a)| < π / 2 := by rwa [abs_neg]
    have hz : 0 < (ν * exp (((-a : ℝ) : ℂ) * I)).re := by
      rw [hνe, show (ρ : ℂ) * exp ((2 * a : ℝ) * I) * exp (((-a : ℝ) : ℂ) * I) =
        ((ρ : ℝ) : ℂ) * exp ((a : ℂ) * I) by
          rw [mul_assoc, ← exp_add]; push_cast; ring_nf, re_ofReal_mul,
        exp_ofReal_mul_I_re]
      exact mul_pos hρ0 (struveSc_cos_pos ha2)
    have hrot := struveAs_angerA_eq_rot (-ν) hθ hz
    have hest := struveSc_turning_est ha2 hK0.le hs hcos (fun s hs => hK a ha' s hs) hρ1
    have hrhs := struveSc_turning_rhs ha2 hρ0
    rw [← hνe] at hest hrhs
    set E : ℂ := exp (((-a : ℝ) : ℂ) * I) with hE
    have hint : (∫ r in Ioi (0 : ℝ), exp (-(ν * E * r)) * struveAs_kernel (-ν) ((r : ℂ) * E)) =
        ∫ r in Ioi (0 : ℝ), exp (-(ν * struveSc_phase 1 ((r : ℂ) * E))) *
          (1 + ((r : ℂ) * E) ^ 2) ^ (-(1 / 2 : ℂ)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
      have := struveSc_integrand_eq 1 ha2 ν (le_of_lt hr)
      rwa [ofReal_one, one_mul] at this
    have hCre : 0 < (ν * E ^ 3 / 6).re := by
      rw [hνe, hE, ← exp_nat_mul, show (ρ : ℂ) * exp ((2 * a : ℝ) * I) *
          exp (((3 : ℕ) : ℂ) * (((-a : ℝ) : ℂ) * I)) / 6 =
          ((ρ / 6 : ℝ) : ℂ) * exp (((-a : ℝ) : ℂ) * I) by
        rw [mul_assoc, ← exp_add]; push_cast; ring_nf, re_ofReal_mul, exp_ofReal_mul_I_re,
        Real.cos_neg]
      exact mul_pos (by positivity) (struveSc_cos_pos ha2)
    rw [hrot, struveAs_rotInt, hint, hrhs, ← struveSc_integral_exp_cube hCre, ← mul_sub,
      ← mul_sub, norm_mul, norm_mul, hE, norm_exp_ofReal_mul_I, one_mul, ← hE, norm_div,
      norm_one, norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hest (by positivity)
  set c1 : ℝ := 2 ^ (4 / 3 : ℝ) / (3 ^ (7 / 6 : ℝ) * Real.Gamma (2 / 3)) with hc1
  have hc10 : 0 < c1 := by
    have : 0 < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)
    rw [hc1]; positivity
  rw [IsEquivalent, isLittleO_iff]
  intro ε hε
  set M : ℝ := 1 / π * Cst / (ε * c1) + 1 with hM
  have hM0 : 0 < M := by rw [hM]; positivity
  set R : ℝ := max 1 (M ^ 3) with hR
  have hev : ∀ᶠ ν in sector (π - δ), R ≤ ‖ν‖ ∧ ν ∈ {z : ℂ | z ≠ 0 ∧ |arg z| ≤ π - δ} :=
    ((tendsto_norm_sector (π - δ)).eventually (eventually_ge_atTop R)).and
      (mem_inf_of_right (mem_principal_self _))
  filter_upwards [hev] with ν ⟨hνR, hν0, harg⟩
  have hρ1 : 1 ≤ ‖ν‖ := (le_max_left _ _).trans hνR
  have hρ0 : 0 < ‖ν‖ := by linarith
  simp only [Pi.sub_apply]
  rw [struveSc_norm_turning_rhs ν, ← hc1]
  refine (hmain ν hν0 harg hρ1).trans ?_
  have hM3 : M ≤ ‖ν‖ ^ (1 / 3 : ℝ) := by
    have h1 : M ^ 3 ≤ ‖ν‖ := (le_max_right _ _).trans hνR
    have h2 : (M ^ 3) ^ (1 / 3 : ℝ) = M := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hM0.le]; norm_num
    rw [← h2]
    exact Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  set t : ℝ := ‖ν‖ ^ (1 / 3 : ℝ) with ht
  have ht0 : 0 < t := by positivity
  have h23 : ‖ν‖ ^ (-(2 / 3 : ℝ)) = 1 / t * (1 / t) := by
    rw [ht, show (-(2 / 3 : ℝ)) = -(1 / 3) + -(1 / 3) by norm_num, Real.rpow_add hρ0,
      Real.rpow_neg hρ0.le]
    ring
  rw [h23]
  have hMε : 1 / π * Cst ≤ ε * c1 * (M - 1) := by
    rw [hM]; field_simp; linarith
  have key : 1 / π * Cst * (1 / t) ≤ ε * c1 := by
    rw [mul_one_div, div_le_iff₀ ht0]
    nlinarith [mul_pos hε hc10]
  calc 1 / π * Cst * (1 / t * (1 / t)) = 1 / π * Cst * (1 / t) * (1 / t) := by ring
    _ ≤ ε * c1 * (1 / t) := mul_le_mul_of_nonneg_right key (by positivity)
    _ = ε * (c1 / t) := by ring

/-- angerJ turning equiv, DLMF 11.11.18 for real `ν → +∞`.

DLMF 1.1.2 extended this to `ν → ∞` in `|ph ν| ≤ π - δ`; that extension fails. By 11.10.15,
`𝐉_ν(ν) = J_ν(ν) + sin(πν) 𝐀_ν(ν)` with `𝐀_ν(ν) ~ 1/(2πν)`, and off the real axis the second
term grows like `e^{π|Im ν|}/|ν|`: at `ph ν = 0.3` the ratio to the leading term is about `10⁶`,
`10¹⁴`, `10³⁰` for `|ν| = 20, 40, 80`. The original DLMF condition `ν → +∞` is kept. -/
@[dlmf 11.11.E18 "special case: ν → +∞ (the complex sector of DLMF 1.1.2 fails), DLMF erratum"]
theorem angerJ_turning_equiv :
    (fun ν : ℝ => angerJ ν ν) ~[atTop] (fun ν : ℝ => 2^(1/3:ℂ)/(3^(2/3:ℂ)*Gamma (2/3)*(ν:ℂ)^(1/3:ℂ))) := by
  have hK : (2 : ℝ) ^ (1 / 3 : ℝ) / (3 ^ (2 / 3 : ℝ) * Real.Gamma (2 / 3)) ≠ 0 := by
    have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 2 / 3); positivity
  have hlim : Tendsto (fun ν : ℝ => ν ^ (1 / 3 : ℝ) * ((1 / π) * (∫ x in (0 : ℝ)..π,
      exp (((ν * (x - Real.sin x) : ℝ) : ℂ) * I)).re)) atTop
      (𝓝 (2 ^ (1 / 3 : ℝ) / (3 ^ (2 / 3 : ℝ) * Real.Gamma (2 / 3)))) := by
    have h := ((continuous_re.tendsto _).comp struveTP_tendsto_integral).const_mul (1 / π)
    rw [← struveTP_const_J]
    convert h using 2
    · simp only [Function.comp, re_ofReal_mul]; ring
    · rw [re_ofReal_mul, re_ofReal_mul, exp_ofReal_mul_I_re]; ring
  have := struveTP_isEquivalent_of_tendsto hK hlim
  simp only [← struveTP_angerJ_eq] at this
  refine this.congr_right ?_
  filter_upwards [eventually_gt_atTop 0] with ν hν
  have := struveTP_rhs_eq (2 / 3) hν
  push_cast at this
  rw [this]
  push_cast; ring

/-- weberE turning equiv, DLMF 11.11.19 for real `ν → +∞`.

As for 11.11.18, the complex sector `|ph ν| ≤ π - δ` of DLMF 1.1.2 fails: by 11.10.16,
`𝐄_ν(ν) = -Y_ν(ν) - cos(πν) 𝐀_ν(ν) - 𝐀_{-ν}(ν)`, and `cos(πν) 𝐀_ν(ν)` grows like
`e^{π|Im ν|}/|ν|` off the real axis. The original DLMF condition `ν → +∞` is kept. -/
@[dlmf 11.11.E19 "special case: ν → +∞ (the complex sector of DLMF 1.1.2 fails), DLMF erratum"]
theorem weberE_turning_equiv :
    (fun ν : ℝ => weberE ν ν) ~[atTop] (fun ν : ℝ => 2^(1/3:ℂ)/(3^(7/6:ℂ)*Gamma (2/3)*(ν:ℂ)^(1/3:ℂ))) := by
  have hK : (2 : ℝ) ^ (1 / 3 : ℝ) / (3 ^ (7 / 6 : ℝ) * Real.Gamma (2 / 3)) ≠ 0 := by
    have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 2 / 3); positivity
  have hlim : Tendsto (fun ν : ℝ => ν ^ (1 / 3 : ℝ) * ((1 / π) * (∫ x in (0 : ℝ)..π,
      exp (((ν * (x - Real.sin x) : ℝ) : ℂ) * I)).im)) atTop
      (𝓝 (2 ^ (1 / 3 : ℝ) / (3 ^ (7 / 6 : ℝ) * Real.Gamma (2 / 3)))) := by
    have h := ((continuous_im.tendsto _).comp struveTP_tendsto_integral).const_mul (1 / π)
    rw [← struveTP_const_E]
    convert h using 2
    · simp only [Function.comp, im_ofReal_mul]; ring
    · rw [im_ofReal_mul, im_ofReal_mul, exp_ofReal_mul_I_im]; ring
  have := struveTP_isEquivalent_of_tendsto hK hlim
  simp only [← struveTP_weberE_eq] at this
  refine this.congr_right ?_
  filter_upwards [eventually_gt_atTop 0] with ν hν
  have := struveTP_rhs_eq (7 / 6) hν
  push_cast at this
  rw [this]
  push_cast; ring

/-- Turning-point approximation uniform on bounded complex transition parameters; positive real order. -/
@[dlmf 11.11.E17]
theorem angerA_turning_uniform (M : ℝ) (hM : 0 < M) :
    (fun p : ℝ × ℂ => angerA (-p.1) (p.1+p.2*(p.1:ℂ)^(1/3:ℂ))-2^(1/3:ℂ)*(p.1:ℂ)^(-1/3:ℂ)*scorerHi (-2^(1/3:ℂ)*p.2)) =O[comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℂ | ‖p.2‖ ≤ M}] (fun p : ℝ × ℂ => (p.1:ℂ)^(-1:ℤ)) := by
  set CU : ℝ := Real.exp (M * (48 * M + 1) / 2) * (16 + 3 / 10 * 768) + 2 * 48 ^ 3 +
    3 / 10 * 120 * 48 ^ 6 with hCU
  refine IsBigO.of_bound (CU / π) ?_
  set R : ℝ := max 1 ((48 * M + 1) ^ 3) with hR
  filter_upwards [mem_inf_of_left (preimage_mem_comap (Ici_mem_atTop R)),
    mem_inf_of_right (mem_principal_self _)] with p hp hpM
  obtain ⟨ν, a⟩ := p
  simp only [mem_preimage, mem_Ici] at hp
  simp only at hpM
  simp only
  have hν1 : 1 ≤ ν := (le_max_left _ _).trans hp
  have hν0 : 0 < ν := by linarith
  set τ : ℝ := ν ^ (1 / 3 : ℝ) with hτ
  have hτ0 : 0 < τ := by positivity
  have hντ : τ ^ 3 = ν := by
    rw [hτ, ← Real.rpow_natCast, ← Real.rpow_mul hν0.le]; norm_num
  have hτ1 : 48 * M + 1 ≤ τ := by
    have h1 : (48 * M + 1) ^ 3 ≤ ν := (le_max_right _ _).trans hp
    have h2 : ((48 * M + 1) ^ 3) ^ (1 / 3 : ℝ) = 48 * M + 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
    rw [← h2]; exact Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  have hτ1' : 1 ≤ τ := by linarith
  have hτM : 48 * M ≤ τ ^ 2 := by nlinarith
  have hcτ : (ν : ℂ) ^ (1 / 3 : ℂ) = (τ : ℂ) := by
    rw [hτ, ofReal_cpow hν0.le]; push_cast; rfl
  have hcτ' : (ν : ℂ) ^ (-1 / 3 : ℂ) = ((τ⁻¹ : ℝ) : ℂ) := by
    rw [hτ, ← Real.rpow_neg hν0.le, ofReal_cpow hν0.le]; push_cast; ring_nf
  have hc2 : (2 : ℂ) ^ (1 / 3 : ℂ) = (((2 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) := by
    rw [ofReal_cpow (by norm_num)]; push_cast; rfl
  rw [hcτ, hcτ', hc2]
  -- representation
  have hzre : 0 < ((ν : ℂ) + a * τ).re := by
    rw [add_re, ofReal_re, show a * (τ : ℂ) = (τ : ℂ) * a by ring, re_ofReal_mul]
    have := neg_le_of_abs_le (abs_re_le_norm a)
    have hMτ : M * τ < ν := by rw [← hντ]; nlinarith
    nlinarith
  rw [struveSc_angerA_shift ν hzre]
  have hsc := (scorerHi_exp_integral (-(((2 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) * a)).2
  rw [hsc]
  have hlead := struveSc_lead_cube hτ0 a
  have hest := struveSc_turnU_est hM.le hτ1' hτM hpM
  rw [hντ] at hlead hest
  set Fi := ∫ s in Ioi (0 : ℝ), exp (-((ν : ℂ) * ((struveSc_phiR 1 s : ℝ) : ℂ)) - a * τ * s) *
        (((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ) with hFi
  set Gi := ∫ s in Ioi (0 : ℝ), exp (-((ν : ℂ) * (s : ℂ) ^ 3 / 6) - a * τ * s) with hGi
  set Ti := ∫ t in Ioi (0 : ℝ), exp (-(t : ℂ) ^ 3 / 3 + (-(((2 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) * a) * t)
    with hTi
  have hint : ∫ s in Ioi (0 : ℝ), exp (-((ν : ℂ) * ((struveSc_phiR 1 s : ℝ) : ℂ)) -
      ((ν : ℂ) + a * τ - ν) * s) * (((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ) = Fi := by
    rw [hFi]; congr 1; funext s; congr 3; ring
  rw [hint]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_pos.ne'
  have hdiff : 1 / (π : ℂ) * Fi - (((2 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) * ((τ⁻¹ : ℝ) : ℂ) * (Ti / π) =
      1 / (π : ℂ) * (Fi - Gi) := by
    rw [hlead]; push_cast; field_simp
  rw [hdiff, norm_mul, norm_div, norm_one, norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    norm_zpow, norm_real, Real.norm_of_nonneg hν0.le]
  calc 1 / π * ‖Fi - Gi‖ ≤ 1 / π * (CU / τ ^ 3) := by
        gcongr; rw [hντ, hCU]; exact hest
    _ = CU / π * ν ^ (-1 : ℤ) := by
        rw [hντ, zpow_neg_one]; ring

/-- The recurrence quotient of DLMF 11.11(iii) evaluated on the circle-integral form:
if `A_k = c I_n` on the disc `|λ - λ₀| < ε` (`n = 2k+1`), the quotient defining `A_{k+1}` equals
`c I_{n+2}` at every point of the disc other than `λ = 1`. -/
theorem struveLO_quotient_eq {r ε : ℝ} {lam₀ : ℂ} (hr : 0 < r) (hG : struveLO_Good r ε lam₀)
    (k : ℕ) (c : ℂ)
    (hA : ∀ l ∈ Metric.ball lam₀ ε, angerScaledA k l = c * struveLO_I r (fun _ => 1) (2 * k + 1) l)
    {lam : ℂ} (hlam : lam ∈ Metric.ball lam₀ ε) (h1 : lam ≠ 1) :
    lam/(1-lam^2)*(lam*iteratedDeriv 2 (angerScaledA k) lam+deriv (angerScaledA k) lam)/
      ((2*k+1:ℂ)*(2*k+2)) = c * struveLO_I r (fun _ => 1) (2 * (k + 1) + 1) lam := by
  set n := 2 * k + 1 with hn
  have hU : IsOpen (Metric.ball lam₀ ε) := Metric.isOpen_ball
  have hd1 : ∀ l ∈ Metric.ball lam₀ ε, HasDerivAt (angerScaledA k)
      (c * (-(n : ℂ) * struveLO_I r (fun t => 1 * sinh t) (n + 1) l)) l := by
    intro l hl
    refine ((struveLO_hasDerivAt_I hr hG continuous_const n hl).const_mul c).congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hl] with x hx using hA x hx
  have hd2 : HasDerivAt (fun l => c * (-(n : ℂ) * struveLO_I r (fun t => 1 * sinh t) (n + 1) l))
      (c * (-(n : ℂ) * (-((n + 1 : ℕ) : ℂ) *
        struveLO_I r (fun t => 1 * sinh t * sinh t) (n + 1 + 1) lam))) lam :=
    (((struveLO_hasDerivAt_I hr hG (g := fun t => 1 * sinh t) (by fun_prop) (n + 1)
      hlam).const_mul _).const_mul c)
  have hD : deriv (angerScaledA k) lam =
      c * (-(n : ℂ) * struveLO_I r (fun t => 1 * sinh t) (n + 1) lam) := (hd1 lam hlam).deriv
  have hD2 : iteratedDeriv 2 (angerScaledA k) lam = c * (-(n : ℂ) * (-((n + 1 : ℕ) : ℂ) *
        struveLO_I r (fun t => 1 * sinh t * sinh t) (n + 1 + 1) lam)) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    refine (hd2.congr_of_eventuallyEq ?_).deriv
    filter_upwards [hU.mem_nhds hlam] with x hx using (hd1 x hx).deriv
  have hrec := struveLO_recurrence hr hG n (Metric.ball_subset_closedBall hlam)
  have hl1 : 1 + lam ≠ 0 := by
    have := hG lam (Metric.ball_subset_closedBall hlam) 0 (Metric.mem_closedBall_self hr.le)
    rwa [struveLO_dslope_zero, mul_one] at this
  have hsq : 1 - lam ^ 2 ≠ 0 := by
    rw [show 1 - lam ^ 2 = (1 - lam) * (1 + lam) by ring]
    exact mul_ne_zero (sub_ne_zero.2 (Ne.symm h1)) hl1
  have hk : ((2 * k + 1 : ℂ) * (2 * k + 2)) ≠ 0 := by
    have : ((2 * k + 1 : ℕ) : ℂ) * ((2 * k + 2 : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (by positivity : (2 * k + 1) * (2 * k + 2) ≠ 0)
    exact_mod_cast this
  rw [show 2 * (k + 1) + 1 = n + 2 by omega, hD, hD2]
  set X2 := struveLO_I r (fun t => 1 * sinh t * sinh t) (n + 1 + 1) lam
  set X1 := struveLO_I r (fun t => 1 * sinh t) (n + 1) lam
  set X0 := struveLO_I r (fun _ => 1) (n + 2) lam
  have hnc : (n : ℂ) = 2 * k + 1 := by rw [hn]; push_cast; ring
  push_cast
  rw [hnc] at hrec ⊢
  rw [div_eq_iff hk, div_mul_eq_mul_div, div_eq_iff hsq]
  linear_combination c * hrec

/-- Under the hypothesis of `struveLO_quotient_eq`, the recurrence quotient tends to
`c I_{2k+3}(λ)` along the punctured neighbourhood of every point `λ` of the disc. -/
theorem struveLO_tendsto_quotient {r ε : ℝ} {lam₀ : ℂ} (hr : 0 < r) (hG : struveLO_Good r ε lam₀)
    (k : ℕ) (c : ℂ)
    (hA : ∀ l ∈ Metric.ball lam₀ ε, angerScaledA k l = c * struveLO_I r (fun _ => 1) (2 * k + 1) l)
    {lam : ℂ} (hlam : lam ∈ Metric.ball lam₀ ε) :
    Tendsto (fun l : ℂ => l/(1-l^2)*(l*iteratedDeriv 2 (angerScaledA k) l+deriv (angerScaledA k) l)/
      ((2*k+1:ℂ)*(2*k+2))) (𝓝[≠] lam)
      (𝓝 (c * struveLO_I r (fun _ => 1) (2 * (k + 1) + 1) lam)) := by
  have hc : ContinuousAt (fun l => c * struveLO_I r (fun _ => 1) (2 * (k + 1) + 1) l) lam :=
    ((struveLO_hasDerivAt_I hr hG continuous_const _ hlam).continuousAt).const_mul c
  refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  have hev : ∀ᶠ l in 𝓝[≠] lam, l ∈ Metric.ball lam₀ ε ∧ l ≠ 1 := by
    refine Filter.Eventually.and (nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hlam)) ?_
    by_cases h1 : lam = 1
    · subst h1; exact self_mem_nhdsWithin
    · exact nhdsWithin_le_nhds (eventually_ne_nhds h1)
  filter_upwards [hev] with l hl
  exact (struveLO_quotient_eq hr hG k c hA hl.1 hl.2).symm

/-- On a good disc, `A_k(λ) = (2πi)⁻¹ ∮ (t + λ sinh t)^{-(2k+1)} dt` (Lagrange inversion form of
the coefficients of DLMF 11.11.8). -/
theorem struveLO_angerScaledA_eq {r ε : ℝ} {lam₀ : ℂ} (hr : 0 < r) (hG : struveLO_Good r ε lam₀)
    (k : ℕ) : ∀ l ∈ Metric.ball lam₀ ε,
      angerScaledA k l = (2 * π * I)⁻¹ * struveLO_I r (fun _ => 1) (2 * k + 1) l := by
  induction k with
  | zero =>
    intro l hl
    have hl1 : 1 + l ≠ 0 := by
      have := hG l (Metric.ball_subset_closedBall hl) 0 (Metric.mem_closedBall_self hr.le)
      rwa [struveLO_dslope_zero, mul_one] at this
    have hπ : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    simp only [Nat.mul_zero, Nat.zero_add]
    rw [struveLO_I_one hr hG (Metric.ball_subset_closedBall hl)]
    simp only [angerScaledA]
    field_simp
  | succ k ih =>
    intro l hl
    exact (struveLO_tendsto_quotient hr hG k _ ih hl).limUnder_eq

/-- The recurrence in DLMF 11.11(iii) has a removable singularity at lambda=1.
Proof: `A_k(λ) = (2πi)⁻¹ ∮ (t + λ sinh t)^{-(2k+1)} dt` near every `λ ≠ -1`
(`struveLO_angerScaledA_eq`), and the circle integrals are holomorphic in `λ`. -/
theorem angerScaledA_removable (k : ℕ) {lam : ℂ} (hlam : lam ≠ -1) :
    Tendsto (fun l : ℂ => l/(1-l^2)*(l*iteratedDeriv 2 (angerScaledA k) l+deriv (angerScaledA k) l)/((2*k+1:ℂ)*(2*k+2)))
      (𝓝[≠] lam) (𝓝 (angerScaledA (k+1) lam)) := by
  have h1 : 1 + lam ≠ 0 := fun h => hlam (by linear_combination h)
  obtain ⟨r, hr, ε, hε, hG⟩ := struveLO_good_exists h1
  have hm : lam ∈ Metric.ball lam ε := Metric.mem_ball_self hε
  rw [struveLO_angerScaledA_eq hr hG (k + 1) lam hm]
  exact struveLO_tendsto_quotient hr hG k _ (struveLO_angerScaledA_eq hr hG k) hm

/-- The convergent defining H series is also a generalized large-order expansion, DLMF 11.6(ii). -/
theorem struveH_large_order_expansion {z : ℂ} (hz : z ∈ slitPlane)
    {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun ν : ℂ => struveH ν z-(z/2)^(ν+1)*∑ n ∈ Finset.range N,
      (-1)^n*(z/2)^(2*n)*struveCoeff ν n) =O[sector (π-δ)]
      (fun ν : ℂ => (z/2)^(ν+1)/Gamma (ν+N+3/2)) :=
  struve_series_tail_isBigO (slitPlane_ne_zero hz) (by simp) hδ hδπ N (fun ν => struveHCore ν z)
    (fun ν => hasSum_struveHCore ν z)

/-- The corresponding generalized L expansion in DLMF 11.6(ii). -/
theorem struveL_large_order_expansion {z : ℂ} (hz : z ∈ slitPlane)
    {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun ν : ℂ => struveL ν z-(z/2)^(ν+1)*∑ n ∈ Finset.range N,
      (z/2)^(2*n)*struveCoeff ν n) =O[sector (π-δ)]
      (fun ν : ℂ => (z/2)^(ν+1)/Gamma (ν+N+3/2)) := by
  have h := struve_series_tail_isBigO (slitPlane_ne_zero hz) (ε := 1) (by simp) hδ hδπ N
    (fun ν => struveLCore ν z) (fun ν => by simpa using hasSum_struveLCore ν z)
  simpa [struveL] using h

end DLMF.Struve
