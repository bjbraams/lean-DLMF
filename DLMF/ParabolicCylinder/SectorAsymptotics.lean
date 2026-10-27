/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ParabolicCylinder.Basic
public import DLMFMathlib.Analysis.Asymptotics.WatsonRotated
public import DLMF.Core.Framework

/-!
# Sector asymptotics of `U(a,z)` past `|ph z| = π/2` (DLMF 12.9)

For `re a > -1/2` and `|θ| < π/4`, rotating the ray in the Laplace integral DLMF 12.5.1 gives

`Γ(1/2 + a) e^{z²/4} U(a,z) = e^{iθ} ∫₀^∞ e^{-z e^{iθ} r} (r e^{iθ})^{a-1/2} e^{-(r e^{iθ})²/2} dr`

for every complex `z` (`pcfSect_integral_rotate`). Watson's lemma along the rotated rays
(`hasAsymptoticExpansion_integral_cexp_smul_rotate_comap`) then gives the Poincaré expansion
DLMF 12.9.1 of `e^{z²/4} z^{a+1/2} U(a,z)` uniformly in `|ph z| ≤ 3π/4 - δ`; the recurrence
DLMF 12.8.1 removes the restriction on `a` (`pcfSect_U_sector`).

We also record the expansion along the logarithmic plane (`pcfSect_U_logWedge`), which is the
input for the two-exponential expansions DLMF 12.9.3–12.9.4 obtained from the connection
formulas 12.2.19–12.2.20, and DLMF 12.9.2 for `V(a,z)` from 12.2.20 (`pcfSect_V_sector`); there
the `U(a,z)` contribution is exponentially small (`pcfSect_exp_neg_sq_mul_cpow_isBigO`).
The expansion 12.9.1 holds for every `δ > 0` (no upper bound on `δ` is needed).
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat Interval
namespace DLMF.Confluent

/-! ### The Gaussian kernel -/

/-- Coefficients of `e^{-t²/2} = ∑ cₙ tⁿ`. -/
def pcfSect_gaussCoeff (n : ℕ) : ℂ :=
  if Even n then (-1 / 2 : ℂ) ^ (n / 2) / ((n / 2).factorial : ℂ) else 0

/-- Partial sums of `∑ cₙ tⁿ` are partial sums of the exponential series of `-t²/2`. -/
theorem pcfSect_sum_gaussCoeff (t : ℂ) (M : ℕ) :
    (∑ n ∈ Finset.range (2 * M), t ^ n * pcfSect_gaussCoeff n =
      ∑ k ∈ Finset.range M, (-(t ^ 2 / 2)) ^ k / (k.factorial : ℂ)) ∧
    (∑ n ∈ Finset.range (2 * M + 1), t ^ n * pcfSect_gaussCoeff n =
      ∑ k ∈ Finset.range (M + 1), (-(t ^ 2 / 2)) ^ k / (k.factorial : ℂ)) := by
  induction M with
  | zero => simp [pcfSect_gaussCoeff]
  | succ M ih =>
    have h1 : ∑ n ∈ Finset.range (2 * (M + 1)), t ^ n * pcfSect_gaussCoeff n =
        ∑ k ∈ Finset.range (M + 1), (-(t ^ 2 / 2)) ^ k / (k.factorial : ℂ) := by
      rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, Finset.sum_range_succ, ih.2]
      have : ¬ Even (2 * M + 1) := by simp
      simp [pcfSect_gaussCoeff]
    refine ⟨h1, ?_⟩
    rw [Finset.sum_range_succ, h1, Finset.sum_range_succ (n := M + 1)]
    congr 1
    have he : Even (2 * (M + 1)) := even_two_mul _
    have hd : 2 * (M + 1) / 2 = M + 1 := by omega
    simp only [pcfSect_gaussCoeff, he, ite_true, hd]
    rw [neg_pow, div_pow, div_pow, ← pow_mul]
    ring

/-- Taylor remainders of `e^{-t²/2}` along a ray. -/
theorem pcfSect_gauss_sub_sum_isBigO (θ : ℝ) (N : ℕ) :
    (fun r : ℝ => cexp (-(((r : ℂ) * exp (θ * I)) ^ 2 / 2)) - ∑ n ∈ Finset.range N,
      ((r : ℂ) * exp (θ * I)) ^ n * pcfSect_gaussCoeff n) =O[𝓝[>] 0] fun r => r ^ N := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, N ≤ 2 * M ∧
      ∀ t : ℂ, ∑ n ∈ Finset.range N, t ^ n * pcfSect_gaussCoeff n =
        ∑ k ∈ Finset.range M, (-(t ^ 2 / 2)) ^ k / (k.factorial : ℂ) := by
    obtain ⟨M, rfl | rfl⟩ := Nat.even_or_odd' N
    · exact ⟨M, le_rfl, fun t => (pcfSect_sum_gaussCoeff t M).1⟩
    · exact ⟨M + 1, by omega, fun t => (pcfSect_sum_gaussCoeff t M).2⟩
  refine IsBigO.of_bound 3 ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one' ℝ))]
    with r hr hr1
  have hr : (0 : ℝ) < r := hr
  have hr1 : r < 1 := hr1
  rw [hM.2]
  have hb := Complex.norm_exp_sub_sum_le_norm_mul_exp (-(((r : ℂ) * exp (θ * I)) ^ 2 / 2)) M
  have hn : ‖-(((r : ℂ) * exp (θ * I)) ^ 2 / 2)‖ = r ^ 2 / 2 := by
    rw [norm_neg, norm_div, norm_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le,
      norm_exp_ofReal_mul_I, mul_one]
    simp
  rw [hn] at hb
  rw [Real.norm_of_nonneg (pow_nonneg hr.le _)]
  refine hb.trans ?_
  have h1 : (r ^ 2 / 2) ^ M ≤ r ^ N := by
    calc (r ^ 2 / 2) ^ M ≤ (r ^ 2) ^ M := by
          gcongr; linarith [sq_nonneg r]
      _ = r ^ (2 * M) := by rw [← pow_mul]
      _ ≤ r ^ N := pow_le_pow_of_le_one hr.le hr1.le hM.1
  have h2 : Real.exp (r ^ 2 / 2) ≤ 3 := by
    have : r ^ 2 / 2 ≤ 1 := by nlinarith
    calc Real.exp (r ^ 2 / 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr this
      _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  calc (r ^ 2 / 2) ^ M * Real.exp (r ^ 2 / 2) ≤ r ^ N * 3 := by gcongr
    _ = 3 * r ^ N := by ring

/-- The Laplace kernel `t^{μ-1} e^{-t²/2}` of DLMF 12.5.1, with `μ = a + 1/2`. -/
def pcfSect_kernel (μ t : ℂ) : ℂ := t ^ (μ - 1) * cexp (-(t ^ 2 / 2))

/-- Modulus of the Gaussian factor along a ray. -/
theorem pcfSect_norm_gauss (r y : ℝ) :
    ‖cexp (-(((r : ℂ) * exp (y * I)) ^ 2 / 2))‖ = Real.exp (-(r ^ 2 * Real.cos (2 * y)) / 2) := by
  rw [Complex.norm_exp, Complex.ofReal_mul_exp_ofReal_mul_I_sq]
  congr 1
  rw [neg_re, div_ofNat_re, re_ofReal_mul, exp_ofReal_mul_I_re]
  ring

/-- Bound for the kernel along a ray `|arg t| ≤ π/4`. -/
theorem pcfSect_norm_kernel_le (μ : ℂ) {r : ℝ} (hr : 0 < r) {y : ℝ} (hy : |y| ≤ π / 4) :
    ‖pcfSect_kernel μ ((r : ℂ) * exp (y * I))‖ ≤
      Real.exp (π * |μ.im|) * r ^ (μ.re - 1) * Real.exp (-(r ^ 2 * Real.cos (2 * y)) / 2) := by
  have hy1 : -π < y := by linarith [neg_abs_le y, Real.pi_pos]
  have hy2 : y ≤ π := by linarith [le_abs_self y, Real.pi_pos]
  rw [pcfSect_kernel, norm_mul, pcfSect_norm_gauss, Complex.ofReal_mul_exp_cpow hr hy1 hy2,
    norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hr, Complex.norm_exp]
  have he : (y * I * (μ - 1)).re ≤ π * |μ.im| := by
    have : (y * I * (μ - 1)).re = -(y * μ.im) := by simp
    rw [this]
    calc -(y * μ.im) ≤ |y| * |μ.im| := by
          rw [← abs_mul]; exact neg_le_abs _
      _ ≤ π * |μ.im| := by gcongr; linarith
  have h1 := Real.exp_le_exp.mpr he
  simp only [sub_re, one_re]
  have h2 : 0 ≤ r ^ (μ.re - 1) := Real.rpow_nonneg hr.le _
  calc r ^ (μ.re - 1) * Real.exp (y * I * (μ - 1)).re * Real.exp (-(r ^ 2 * Real.cos (2 * y)) / 2)
      ≤ r ^ (μ.re - 1) * Real.exp (π * |μ.im|) * Real.exp (-(r ^ 2 * Real.cos (2 * y)) / 2) := by
        gcongr
    _ = _ := by ring

/-- `cos (2y) ≥ 0` for `|y| ≤ π/4`. -/
theorem pcfSect_cos_two_mul_nonneg {y : ℝ} (hy : |y| ≤ π / 4) : 0 ≤ Real.cos (2 * y) := by
  rw [← Real.cos_abs, abs_mul, abs_two]
  exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [abs_nonneg y, Real.pi_pos], by linarith⟩

/-- `cos (2y) > 0` for `|y| < π/4`. -/
theorem pcfSect_cos_two_mul_pos {y : ℝ} (hy : |y| < π / 4) : 0 < Real.cos (2 * y) := by
  rw [← Real.cos_abs, abs_mul, abs_two]
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [abs_nonneg y, Real.pi_pos], by linarith⟩

/-- A simpler kernel bound: `|K(r e^{iy})| ≤ C r^{re μ - 1}` for `|y| ≤ π/4`. -/
theorem pcfSect_norm_kernel_le' (μ : ℂ) {r : ℝ} (hr : 0 < r) {y : ℝ} (hy : |y| ≤ π / 4) :
    ‖pcfSect_kernel μ ((r : ℂ) * exp (y * I))‖ ≤ Real.exp (π * |μ.im|) * r ^ (μ.re - 1) := by
  refine (pcfSect_norm_kernel_le μ hr hy).trans ?_
  have : Real.exp (-(r ^ 2 * Real.cos (2 * y)) / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := mul_nonneg (sq_nonneg r) (pcfSect_cos_two_mul_nonneg hy)
    linarith
  have h0 : 0 ≤ Real.exp (π * |μ.im|) * r ^ (μ.re - 1) :=
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hr.le _)
  calc _ ≤ Real.exp (π * |μ.im|) * r ^ (μ.re - 1) * 1 := by gcongr
    _ = _ := mul_one _

/-- Points `r e^{iy}`, `r > 0`, `|y| < π/2`, lie in the slit plane. -/
theorem pcfSect_mem_slitPlane {r : ℝ} (hr : 0 < r) {y : ℝ} (hy : |y| < π / 2) :
    (r : ℂ) * exp (y * I) ∈ slitPlane := by
  refine Or.inl ?_
  rw [re_ofReal_mul, exp_ofReal_mul_I_re]
  exact mul_pos hr (Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le y], by
    linarith [le_abs_self y]⟩)

/-- Continuity of the kernel along a ray. -/
theorem pcfSect_continuousOn_kernel (μ : ℂ) {θ : ℝ} (hθ : |θ| < π / 2) :
    ContinuousOn (fun r : ℝ => pcfSect_kernel μ ((r : ℂ) * exp (θ * I))) (Ioi 0) := by
  intro r hr
  have hc : ContinuousAt (fun r : ℝ => (r : ℂ) * exp (θ * I)) r := by fun_prop
  refine ContinuousAt.continuousWithinAt ?_
  exact (hc.cpow continuousAt_const (pcfSect_mem_slitPlane hr hθ)).mul
    (by fun_prop)

/-- Integrability of the kernel along a ray `|arg t| < π/4`, against any exponential. -/
theorem pcfSect_integrableOn {μ : ℂ} (hμ : 0 < μ.re) (c : ℝ) {θ : ℝ} (hθ : |θ| < π / 4) :
    IntegrableOn (fun r : ℝ => Real.exp (-c * r) • pcfSect_kernel μ ((r : ℂ) * exp (θ * I)))
      (Ioi 0) := by
  set b := Real.cos (2 * θ) with hb
  have hb0 : 0 < b := pcfSect_cos_two_mul_pos hθ
  set K := Real.exp (π * |μ.im|) * Real.exp (c ^ 2 / b)
  have hθ2 : |θ| < π / 2 := by linarith [Real.pi_pos]
  have hg : IntegrableOn (fun r : ℝ => K * (r ^ (μ.re - 1) * Real.exp (-(b / 4) * r ^ 2)))
      (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_sq (by positivity) (by linarith)).const_mul K
  refine hg.mono' ((((by fun_prop : Continuous fun r : ℝ => Real.exp (-c * r)).continuousOn.smul
    (pcfSect_continuousOn_kernel μ hθ2))).aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
  have hr : (0 : ℝ) < r := hr
  rw [norm_smul, Real.norm_eq_abs, Real.abs_exp]
  have hk := pcfSect_norm_kernel_le μ hr hθ.le
  have hq : -c * r + -(r ^ 2 * b) / 2 ≤ c ^ 2 / b + -(b / 4) * r ^ 2 := by
    have : 0 ≤ (b / 2 * r + c) ^ 2 / b := div_nonneg (sq_nonneg _) hb0.le
    have e : (b / 2 * r + c) ^ 2 / b = b / 4 * r ^ 2 + c * r + c ^ 2 / b := by
      field_simp; ring
    nlinarith
  have hq' := Real.exp_le_exp.mpr hq
  rw [Real.exp_add, Real.exp_add] at hq'
  have h0 : 0 ≤ Real.exp (π * |μ.im|) * r ^ (μ.re - 1) :=
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hr.le _)
  calc Real.exp (-c * r) * ‖pcfSect_kernel μ ((r : ℂ) * exp (θ * I))‖
      ≤ Real.exp (-c * r) * (Real.exp (π * |μ.im|) * r ^ (μ.re - 1) *
          Real.exp (-(r ^ 2 * b) / 2)) := by gcongr
    _ = Real.exp (π * |μ.im|) * r ^ (μ.re - 1) *
          (Real.exp (-c * r) * Real.exp (-(r ^ 2 * b) / 2)) := by ring
    _ ≤ Real.exp (π * |μ.im|) * r ^ (μ.re - 1) *
          (Real.exp (c ^ 2 / b) * Real.exp (-(b / 4) * r ^ 2)) := by gcongr
    _ = _ := by ring

/-- The rotated Laplace transform of the kernel is entire. -/
theorem pcfSect_differentiable_laplace {μ : ℂ} (hμ : 0 < μ.re) {θ : ℝ} (hθ : |θ| < π / 4) :
    Differentiable ℂ (fun z : ℂ => exp (θ * I) * ∫ r in Ioi (0 : ℝ),
      cexp (-(z * exp (θ * I) * r)) * pcfSect_kernel μ ((r : ℂ) * exp (θ * I))) := by
  have hL : Differentiable ℂ (fun w : ℂ => ∫ r in Ioi (0 : ℝ), cexp (-(w * r)) •
      pcfSect_kernel μ ((r : ℂ) * exp (θ * I))) := fun w =>
    (differentiableOn_integral_cexp_neg_mul_smul (pcfSect_integrableOn hμ (w.re - 1) hθ)
      ).differentiableAt ((isOpen_lt continuous_const continuous_re).mem_nhds (by simp))
  simp only [smul_eq_mul] at hL
  exact (differentiable_const _).mul (hL.comp (differentiable_id.mul_const (exp (θ * I))))

/-- **Rotated Laplace representation of `U`** (DLMF 12.5.1 with a rotated ray): for
`re a > -1/2`, `|θ| < π/4` and every complex `z`,
`Γ(1/2 + a) e^{z²/4} U(a,z) = e^{iθ} ∫₀^∞ e^{-z e^{iθ} r} K(r e^{iθ}) dr`,
`K(t) = t^{a-1/2} e^{-t²/2}`. -/
theorem pcfSect_integral_rotate {a : ℂ} (ha : -1 / 2 < a.re) {θ : ℝ} (hθ : |θ| < π / 4)
    (z : ℂ) :
    Gamma (1 / 2 + a) * (exp (z ^ 2 / 4) * pcfU a z) = exp (θ * I) * ∫ r in Ioi (0 : ℝ),
      cexp (-(z * exp (θ * I) * r)) * pcfSect_kernel (a + 1 / 2) ((r : ℂ) * exp (θ * I)) := by
  set μ := a + 1 / 2 with hμd
  have hμ : 0 < μ.re := by simp [hμd]; linarith
  have hΓ : Gamma (1 / 2 + a) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hd1 : Differentiable ℂ (fun z : ℂ => Gamma (1 / 2 + a) * (exp (z ^ 2 / 4) * pcfU a z)) :=
    (differentiable_const _).mul ((by fun_prop : Differentiable ℂ fun z : ℂ => exp (z ^ 2 / 4)).mul
      (pcfU_entire a))
  have hd2 := pcfSect_differentiable_laplace hμ hθ
  have hy : ∀ y ∈ [[0, θ]], |y| ≤ π / 4 := fun y hy =>
    (abs_le_abs_of_mem_uIcc_zero hy).trans hθ.le
  have hreal : ∀ x : ℝ, 0 < x → Gamma (1 / 2 + a) * (exp ((x : ℂ) ^ 2 / 4) * pcfU a x) =
      exp (θ * I) * ∫ r in Ioi (0 : ℝ), cexp (-((x : ℂ) * exp (θ * I) * r)) *
        pcfSect_kernel μ ((r : ℂ) * exp (θ * I)) := by
    intro x hx
    have h0 : Gamma (1 / 2 + a) * (exp ((x : ℂ) ^ 2 / 4) * pcfU a x) =
        ∫ t in Ioi (0 : ℝ), cexp (-((x : ℂ) * t)) * pcfSect_kernel μ t := by
      rw [pcfU_eq_integral ha]
      have he : exp ((x : ℂ) ^ 2 / 4) * exp (-(x : ℂ) ^ 2 / 4) = 1 := by
        rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero
      rw [show Gamma (1 / 2 + a) * (exp ((x : ℂ) ^ 2 / 4) * (exp (-(x : ℂ) ^ 2 / 4) /
          Gamma (1 / 2 + a) * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (a - 1 / 2) *
            exp (-(t : ℂ) ^ 2 / 2 - x * t))) = ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (a - 1 / 2) *
            exp (-(t : ℂ) ^ 2 / 2 - x * t) by
          rw [show ∀ G e1 e2 J : ℂ, G ≠ 0 → G * (e1 * (e2 / G * J)) = (e1 * e2) * J from
            fun G e1 e2 J hG => by field_simp, he, one_mul]; exact hΓ]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      simp only [pcfSect_kernel, hμd]
      rw [show a + 1 / 2 - 1 = a - 1 / 2 by ring, show -(t : ℂ) ^ 2 / 2 - x * t =
        -((x : ℂ) * t) + -((t : ℂ) ^ 2 / 2) by ring, Complex.exp_add]
      ring
    rw [h0]
    refine integral_cexp_neg_mul_mul_eq_rotate (F := pcfSect_kernel μ) (σ := μ.re)
      (C := Real.exp (π * |μ.im|)) (k := μ.re - 1) hμ (fun r hr y hy' => ?_)
      (fun r hr _ y hy' => pcfSect_norm_kernel_le' μ hr (hy y hy'))
      (fun r hr y hy' => pcfSect_norm_kernel_le' μ (by linarith) (hy y hy')) (fun y hy' => ?_)
    · have hs := pcfSect_mem_slitPlane hr (y := y) (by linarith [hy y hy', Real.pi_pos])
      exact (differentiableAt_id.cpow (differentiableAt_const _) hs).mul (by fun_prop)
    · rw [re_ofReal_mul, exp_ofReal_mul_I_re]
      have := hy y hy'
      exact mul_pos hx (Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le y, Real.pi_pos],
        by linarith [le_abs_self y, Real.pi_pos]⟩)
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), Gamma (1 / 2 + a) * (exp (w ^ 2 / 4) * pcfU a w) =
      exp (θ * I) * ∫ r in Ioi (0 : ℝ), cexp (-(w * exp (θ * I) * r)) *
        pcfSect_kernel μ ((r : ℂ) * exp (θ * I)) := by
    have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have := (continuous_ofReal.tendsto (1 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := ({1}ᶜ : Set ℝ)))
        rwa [ofReal_one] at this
      · filter_upwards [self_mem_nhdsWithin] with r hr
        simpa using hr
    apply ht.frequently
    apply Eventually.frequently
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one' ℝ))] with r hr
    exact hreal r hr
  exact (hd1.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_frequently_eq
    (hd2.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (mem_univ _) hfreq
    (mem_univ z)

/-! ### Watson's lemma along rotated rays -/

/-- `|(r e^{iy})^w| ≤ e^{π |im w|} r^{re w}` for `r > 0`, `|y| ≤ π`. -/
theorem pcfSect_norm_cpow_le (w : ℂ) {r : ℝ} (hr : 0 < r) {y : ℝ} (hy1 : -π < y) (hy2 : y ≤ π) :
    ‖((r : ℂ) * exp (y * I)) ^ w‖ ≤ Real.exp (π * |w.im|) * r ^ w.re := by
  rw [Complex.ofReal_mul_exp_cpow hr hy1 hy2, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hr,
    Complex.norm_exp]
  have he : (y * I * w).re ≤ π * |w.im| := by
    have : (y * I * w).re = -(y * w.im) := by simp
    rw [this]
    calc -(y * w.im) ≤ |y| * |w.im| := by
          rw [← abs_mul]; exact neg_le_abs _
      _ ≤ π * |w.im| := by
          gcongr; rw [abs_le]; constructor <;> linarith
  have h1 := Real.exp_le_exp.mpr he
  have h2 : 0 ≤ r ^ w.re := Real.rpow_nonneg hr.le _
  calc r ^ w.re * Real.exp (y * I * w).re ≤ r ^ w.re * Real.exp (π * |w.im|) := by gcongr
    _ = _ := by ring

/-- Small-`r` expansion of the kernel along a ray, in the form required by Watson's lemma. -/
theorem pcfSect_kernel_sub_sum_isBigO (μ : ℂ) {θ : ℝ} (hθ1 : -π < θ) (hθ2 : θ ≤ π) (N : ℕ) :
    (fun r : ℝ => pcfSect_kernel μ ((r : ℂ) * exp (θ * I)) - ∑ n ∈ Finset.range N,
      (((r : ℂ) * exp (θ * I)) ^ ((n : ℂ) + μ - 1)) • pcfSect_gaussCoeff n)
      =O[𝓝[>] 0] fun r => r ^ ((N : ℝ) + μ.re - 1) := by
  have h1 : (fun r : ℝ => ((r : ℂ) * exp (θ * I)) ^ (μ - 1)) =O[𝓝[>] 0]
      fun r => r ^ (μ.re - 1) := by
    refine IsBigO.of_bound (Real.exp (π * |(μ - 1).im|)) ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr : (0 : ℝ) < r := hr
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hr.le _)]
    have := pcfSect_norm_cpow_le (μ - 1) hr hθ1 hθ2
    simpa using this
  refine ((h1.mul (pcfSect_gauss_sub_sum_isBigO θ N)).congr' ?_ ?_)
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have hr : (0 : ℝ) < r := hr
    have ht : (r : ℂ) * exp (θ * I) ≠ 0 :=
      mul_ne_zero (ofReal_ne_zero.mpr hr.ne') (exp_ne_zero _)
    simp only [pcfSect_kernel, smul_eq_mul, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show (n : ℂ) + μ - 1 = (μ - 1) + n by ring, Complex.cpow_add _ _ ht,
      Complex.cpow_natCast]
    ring
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have hr : (0 : ℝ) < r := hr
    rw [show (N : ℝ) + μ.re - 1 = (μ.re - 1) + N by ring, Real.rpow_add hr, Real.rpow_natCast]

/-- The term `(-1)^s (a + 1/2)_{2s} / (s! (2z²)^s)` of DLMF 12.9.1. -/
def pcfSect_uTerm (a z : ℂ) (s : ℕ) : ℂ :=
  (-1) ^ s * poch (1 / 2 + a) (2 * s) / ((s.factorial : ℂ) * (2 * z ^ 2) ^ s)

/-- The normalized function `e^{z²/4} z^{a+1/2} U(a,z)` of DLMF 12.9.1. -/
def pcfSect_G (a z : ℂ) : ℂ := exp (z ^ 2 / 4) * z ^ (a + 1 / 2) * pcfU a z

/-- The expansion DLMF 12.9.1 along a filter `l`, as a family of `O`-bounds. -/
def pcfSect_IsExp (a : ℂ) (l : Filter ℂ) : Prop :=
  ∀ N : ℕ, (fun z : ℂ => pcfSect_G a z - ∑ s ∈ Finset.range N, pcfSect_uTerm a z s) =O[l]
    (fun z : ℂ => z ^ (-(2 * N : ℤ)))

/-- Eventually `z ≠ 0` and `|z| ≥ 1` in a sector at infinity. -/
theorem pcfSect_eventually_sector (α : ℝ) : ∀ᶠ z in sector α, z ≠ 0 ∧ 1 ≤ ‖z‖ := by
  have h1 : ∀ᶠ z in sector α, 1 ≤ ‖z‖ :=
    (inf_le_left : sector α ≤ _) (tendsto_comap.eventually (eventually_ge_atTop 1))
  have h2 : ∀ᶠ z in sector α, z ≠ 0 :=
    (inf_le_right : sector α ≤ _) (mem_principal.mpr fun z hz => hz.1)
  exact h2.and h1

/-- Watson's lemma for `Γ(1/2 + a) e^{z²/4} U(a,z)` in a closed sector `|ph z| ≤ 3π/4 - δ`,
for `re a > -1/2`. -/
theorem pcfSect_hasAsymptoticExpansion {a : ℂ} (ha : -1 / 2 < a.re) {δ : ℝ} (hδ : 0 < δ) :
    HasAsymptoticExpansion (sector (3 * π / 4 - δ))
      (fun (n : ℕ) (z : ℂ) => z ^ (-(((2 * n : ℕ) : ℂ) + (a + 1 / 2))))
      (fun n => Complex.Gamma (((2 * n : ℕ) : ℂ) + (a + 1 / 2)) • pcfSect_gaussCoeff (2 * n))
      (fun z => Gamma (1 / 2 + a) * (exp (z ^ 2 / 4) * pcfU a z)) := by
  set μ := a + 1 / 2 with hμd
  have hμ : 0 < μ.re := by simp [hμd]; linarith
  set d := min δ (π / 4) with hd
  have hd0 : 0 < d := lt_min hδ (by positivity)
  have hdδ : d ≤ δ := min_le_left _ _
  have hdπ : d ≤ π / 4 := min_le_right _ _
  have hcov := le_sup_comap_rotate (α := 3 * π / 4 - δ) (β := π / 4 - d / 2) (γ := π / 2 - d / 2)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have hcos : 0 < Real.cos (π / 2 - d / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hrot : ∀ θ : ℝ, |θ| < π / 4 → HasAsymptoticExpansion
      (comap (fun z : ℂ => z * exp (θ * I)) (sectorAtTop (Real.cos (π / 2 - d / 2))))
      (fun (n : ℕ) (z : ℂ) => z ^ (-(((2 * n : ℕ) : ℂ) + μ)))
      (fun n => Complex.Gamma (((2 * n : ℕ) : ℂ) + μ) • pcfSect_gaussCoeff (2 * n))
      (fun z => Gamma (1 / 2 + a) * (exp (z ^ 2 / 4) * pcfU a z)) := by
    intro θ hθ
    have hθ' : |θ| < π / 2 := by linarith [Real.pi_pos]
    have hθ1 : -π < θ := by linarith [neg_abs_le θ, Real.pi_pos]
    have hθ2 : θ ≤ π := by linarith [le_abs_self θ, Real.pi_pos]
    have hW := hasAsymptoticExpansion_integral_cexp_smul_rotate_comap
      (F := pcfSect_kernel μ) (a := pcfSect_gaussCoeff) (μ := μ) (c := 0) hθ' hμ hcos
      (pcfSect_integrableOn hμ 0 hθ) (pcfSect_kernel_sub_sum_isBigO μ hθ1 hθ2)
    have hE := hW.even (fun n => by
      have : ¬ Even (2 * n + 1) := by simp
      simp [pcfSect_gaussCoeff, this])
    refine hE.congr' (Eventually.of_forall fun z => ?_)
    simp only [smul_eq_mul]
    rw [pcfSect_integral_rotate ha hθ z]
  have hβ : |π / 4 - d / 2| < π / 4 := by
    rw [abs_lt]; constructor <;> linarith
  exact ((hrot _ (by rwa [abs_neg])).sup (hrot _ hβ)).mono hcov

/-- **DLMF 12.9.1 for `re a > -1/2`** in the closed sector `|ph z| ≤ 3π/4 - δ`. -/
theorem pcfSect_isExp_of_re {a : ℂ} (ha : -1 / 2 < a.re) {δ : ℝ} (hδ : 0 < δ) :
    pcfSect_IsExp a (sector (3 * π / 4 - δ)) := by
  intro N
  set μ := a + 1 / 2 with hμd
  have hμ : 0 < μ.re := by simp [hμd]; linarith
  have hμk : ∀ k : ℕ, μ ≠ -k := fun k hk => by
    have := congrArg Complex.re hk
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), hμ]
  have hΓ : Gamma (1 / 2 + a) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hΓμ : Gamma (1 / 2 + a) = Gamma μ := by rw [hμd, add_comm]
  have h := ((pcfSect_hasAsymptoticExpansion ha hδ) N).mul
    (isBigO_refl (fun z : ℂ => z ^ μ / Gamma (1 / 2 + a)) (sector (3 * π / 4 - δ)))
  have hev := pcfSect_eventually_sector (3 * π / 4 - δ)
  refine IsBigO.trans (h.congr' (g₂ := fun z : ℂ => (Gamma (1 / 2 + a))⁻¹ * z ^ (-(2 * N : ℤ)))
    ?_ ?_) ?_
  · filter_upwards [hev] with z hz
    have hz0 := hz.1
    simp only [smul_eq_mul, sub_mul, Finset.sum_mul]
    congr 1
    · have key : ∀ G e u q : ℂ, G ≠ 0 → G * (e * u) * (q / G) = e * q * u :=
        fun G e u q hG => by field_simp
      simp only [pcfSect_G, hμd]
      exact key _ _ _ _ hΓ
    · refine Finset.sum_congr rfl fun n _ => ?_
      have hzp : z ^ (-(((2 * n : ℕ) : ℂ) + μ)) * z ^ μ = (z ^ (2 * n))⁻¹ := by
        rw [← Complex.cpow_add _ _ hz0, show -(((2 * n : ℕ) : ℂ) + μ) + μ = -((2 * n : ℕ) : ℂ)
          by ring, Complex.cpow_neg, Complex.cpow_natCast]
      have hG : Gamma (μ + ((2 * n : ℕ) : ℂ)) / Gamma μ = poch μ (2 * n) :=
        Complex.Gamma_add_nat_div_Gamma_eq μ hμk
      have hg : pcfSect_gaussCoeff (2 * n) = (-1 / 2 : ℂ) ^ n / (n.factorial : ℂ) := by
        simp [pcfSect_gaussCoeff, show 2 * n / 2 = n by omega]
      have hΓμ0 : Gamma μ ≠ 0 := hΓμ ▸ hΓ
      have hG' : Gamma (((2 * n : ℕ) : ℂ) + μ) = poch μ (2 * n) * Gamma μ := by
        rw [add_comm, ← hG]; field_simp
      rw [hg, hG', hΓμ, pcfSect_uTerm, show 1 / 2 + a = μ by rw [hμd]; ring]
      have hz2 : z ^ (2 * n) ≠ 0 := pow_ne_zero _ hz0
      have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
      calc z ^ (-(((2 * n : ℕ) : ℂ) + μ)) * (poch μ (2 * n) * Gamma μ *
            ((-1 / 2 : ℂ) ^ n / (n.factorial : ℂ))) * (z ^ μ / Gamma μ)
          = (z ^ (-(((2 * n : ℕ) : ℂ) + μ)) * z ^ μ) * poch μ (2 * n) *
            ((-1 / 2 : ℂ) ^ n / (n.factorial : ℂ)) := by field_simp
        _ = _ := by
          rw [hzp, mul_pow, pow_mul]
          field_simp
          rw [mul_assoc, ← mul_pow]
          norm_num
  · filter_upwards [hev] with z hz
    rw [show (-(((2 * N : ℕ) : ℂ) + μ)) = -((2 * N : ℕ) : ℂ) + -μ by ring,
      Complex.cpow_add _ _ hz.1, Complex.cpow_neg, Complex.cpow_neg, Complex.cpow_natCast,
      zpow_neg, show (2 * (N : ℤ)) = ((2 * N : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    have hzμ : z ^ μ ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff]; tauto
    field_simp
  · exact (isBigO_refl _ _).const_mul_left _

/-- Rewriting `(z^{a+1/2})` along the recurrence: `G(a-1) = G(a) + (a+1/2) z^{-2} G(a+1)`. -/
theorem pcfSect_G_recurrence (a : ℂ) {z : ℂ} (hz : z ≠ 0) :
    pcfSect_G (a - 1) z = pcfSect_G a z + (a + 1 / 2) * (z ^ 2)⁻¹ * pcfSect_G (a + 1) z := by
  have h3 := pcfU_three_term a z
  have h1 : z ^ (a + 1 / 2) = z ^ (a - 1 + 1 / 2) * z := by
    rw [show a + 1 / 2 = (a - 1 + 1 / 2) + 1 by ring, Complex.cpow_add _ _ hz, Complex.cpow_one]
  have h2 : z ^ (a + 1 + 1 / 2) = z ^ (a - 1 + 1 / 2) * z ^ 2 := by
    rw [show a + 1 + 1 / 2 = (a - 1 + 1 / 2) + (2 : ℕ) by push_cast; ring,
      Complex.cpow_add _ _ hz, Complex.cpow_natCast]
  have hz2 : (z ^ 2)⁻¹ * z ^ 2 = 1 := inv_mul_cancel₀ (pow_ne_zero _ hz)
  simp only [pcfSect_G]
  rw [h1, h2]
  linear_combination (-(exp (z ^ 2 / 4) * z ^ (a - 1 + 1 / 2))) * h3 -
    exp (z ^ 2 / 4) * z ^ (a - 1 + 1 / 2) * (a + 1 / 2) * pcfU (a + 1) z * hz2

/-- `poch x (1 + n) = x · poch (x + 1) n`. -/
theorem pcfSect_poch_succ_left (x : ℂ) (n : ℕ) : poch x (1 + n) = x * poch (x + 1) n := by
  rw [poch_add, poch_one]; push_cast; ring_nf

/-- The coefficient recurrence behind `pcfSect_G_recurrence`. -/
theorem pcfSect_uTerm_recurrence (a z : ℂ) (hz : z ≠ 0) (s : ℕ) :
    pcfSect_uTerm (a - 1) z (s + 1) =
      pcfSect_uTerm a z (s + 1) + (a + 1 / 2) * (z ^ 2)⁻¹ * pcfSect_uTerm (a + 1) z s := by
  set x := 1 / 2 + (a - 1) with hx
  have hA : poch x (2 * (s + 1)) = x * ((x + 1) * poch (x + 1 + 1) (2 * s)) := by
    rw [show 2 * (s + 1) = 1 + (1 + 2 * s) by ring, pcfSect_poch_succ_left,
      pcfSect_poch_succ_left]
  have hB : poch (x + 1) (2 * (s + 1)) = (x + 1) * poch (x + 1 + 1) (2 * s) *
      (x + 1 + ((1 + 2 * s : ℕ) : ℂ)) := by
    rw [show 2 * (s + 1) = (1 + 2 * s) + 1 by ring, poch_succ, pcfSect_poch_succ_left]
  have e1 : 1 / 2 + a = x + 1 := by rw [hx]; ring
  have e2 : 1 / 2 + (a + 1) = x + 1 + 1 := by rw [hx]; ring
  have e3 : a + 1 / 2 = x + 1 := by rw [hx]; ring
  simp only [pcfSect_uTerm]
  rw [← hx, hA, e1, hB, e2, e3]
  have hf : (s.factorial : ℂ) ≠ 0 := by exact_mod_cast s.factorial_ne_zero
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- The partial sums along the recurrence. -/
theorem pcfSect_sum_uTerm_recurrence (a z : ℂ) (hz : z ≠ 0) (N : ℕ) :
    ∑ s ∈ Finset.range N, pcfSect_uTerm (a - 1) z s = ∑ s ∈ Finset.range N, pcfSect_uTerm a z s +
      (a + 1 / 2) * (z ^ 2)⁻¹ * ∑ s ∈ Finset.range (N - 1), pcfSect_uTerm (a + 1) z s := by
  rcases N with _ | M
  · simp
  · rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun s => pcfSect_uTerm a z s),
      show M + 1 - 1 = M by omega, Finset.mul_sum]
    simp only [pcfSect_uTerm_recurrence a z hz, Finset.sum_add_distrib]
    have h0 : ∀ b : ℂ, pcfSect_uTerm b z 0 = 1 := fun b => by simp [pcfSect_uTerm, poch_zero]
    rw [h0, h0]
    ring

/-- **The recurrence step**: the expansion for `a` and `a + 1` gives the expansion for `a - 1`. -/
theorem pcfSect_isExp_sub_one {a : ℂ} {l : Filter ℂ} (hl : ∀ᶠ z in l, z ≠ 0 ∧ 1 ≤ ‖z‖)
    (h1 : pcfSect_IsExp a l) (h2 : pcfSect_IsExp (a + 1) l) : pcfSect_IsExp (a - 1) l := by
  intro N
  have hB : (fun z : ℂ => (a + 1 / 2) * (z ^ 2)⁻¹ * z ^ (-(2 * ((N - 1 : ℕ) : ℤ)))) =O[l]
      (fun z : ℂ => z ^ (-(2 * N : ℤ))) := by
    refine IsBigO.of_bound ‖a + 1 / 2‖ ?_
    filter_upwards [hl] with z hz
    have ht : 1 ≤ ‖z‖ := hz.2
    have ht0 : ‖z‖ ≠ 0 := by linarith
    rw [norm_mul, norm_mul, norm_inv, norm_pow, norm_zpow, norm_zpow, mul_assoc]
    gcongr
    rw [← zpow_natCast, ← zpow_neg, ← zpow_add₀ ht0]
    exact zpow_le_zpow_right₀ ht (by omega)
  have h := (h1 N).add (((isBigO_refl (fun z : ℂ => (a + 1 / 2) * (z ^ 2)⁻¹) l).mul
    (h2 (N - 1))).trans hB)
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [hl] with z hz
  rw [pcfSect_G_recurrence a hz.1, pcfSect_sum_uTerm_recurrence a z hz.1]
  ring

/-- **DLMF 12.9.1** for all complex `a`, uniformly in `|ph z| ≤ 3π/4 - δ`:
`e^{z²/4} z^{a+1/2} U(a,z) - ∑_{s<N} (-1)^s (a+1/2)_{2s}/(s! (2z²)^s) = O(z^{-2N})`. -/
theorem pcfSect_U_sector (a : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    pcfSect_IsExp a (sector (3 * π / 4 - δ)) := by
  have hl := pcfSect_eventually_sector (3 * π / 4 - δ)
  suffices h : ∀ m : ℕ, ∀ a : ℂ, -1 / 2 < (a + m).re → pcfSect_IsExp a (sector (3 * π / 4 - δ)) by
    obtain ⟨m, hm⟩ := exists_nat_gt (-1 / 2 - a.re)
    exact h m a (by simp; linarith)
  intro m
  induction m with
  | zero =>
    intro a ha
    exact pcfSect_isExp_of_re (by simpa using ha) hδ
  | succ m ih =>
    intro a ha
    have h1 := ih (a + 1) (by simp at ha ⊢; linarith)
    have h2 := ih (a + 1 + 1) (by simp at ha ⊢; linarith)
    simpa using pcfSect_isExp_sub_one hl h1 h2

/-! ### The expansion along the logarithmic plane -/

/-- `(e^v)^c = e^{cv}` for `-π < im v ≤ π`. -/
theorem pcfSect_exp_cpow {v : ℂ} (h1 : -π < v.im) (h2 : v.im ≤ π) (c : ℂ) :
    (exp v) ^ c = exp (c * v) := by
  rw [Complex.cpow_def_of_ne_zero (exp_ne_zero v), Complex.log_exp h1 h2, mul_comm]

/-- `arg (e^v) = im v` for `-π < im v ≤ π`. -/
theorem pcfSect_arg_exp {v : ℂ} (h1 : -π < v.im) (h2 : v.im ≤ π) : arg (exp v) = v.im := by
  rw [← Complex.log_im, Complex.log_exp h1 h2]

/-- The filter `re w → +∞` with `lo ≤ im w ≤ hi` on the logarithmic plane. -/
def pcfSect_logWedge (lo hi : ℝ) : Filter ℂ :=
  comap (fun w : ℂ => Real.exp w.re) atTop ⊓ 𝓟 {w : ℂ | lo ≤ w.im ∧ w.im ≤ hi}

/-- Eventually `lo ≤ im w ≤ hi` along the logarithmic wedge. -/
theorem pcfSect_eventually_logWedge (lo hi : ℝ) :
    ∀ᶠ w in pcfSect_logWedge lo hi, lo ≤ w.im ∧ w.im ≤ hi :=
  (inf_le_right : pcfSect_logWedge lo hi ≤ _) (mem_principal.mpr fun _ hw => hw)

/-- `w ↦ e^{w + iκ}` maps the logarithmic wedge into the sector `|ph z| ≤ 3π/4 - δ`. -/
theorem pcfSect_tendsto_exp_logWedge {δ : ℝ} (hδ : 0 < δ) (κ : ℝ) {lo hi : ℝ}
    (hlo : -(3 * π / 4 - δ) ≤ lo + κ) (hhi : hi + κ ≤ 3 * π / 4 - δ) :
    Tendsto (fun w : ℂ => exp (w + κ * I)) (pcfSect_logWedge lo hi) (sector (3 * π / 4 - δ)) := by
  refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr ?_⟩
  · have hn : (fun z : ℂ => ‖z‖) ∘ (fun w : ℂ => exp (w + κ * I)) = fun w => Real.exp w.re := by
      funext w; simp [Complex.norm_exp]
    rw [hn]
    exact (inf_le_left : pcfSect_logWedge lo hi ≤ _).trans_eq rfl |> tendsto_comap.mono_left
  · filter_upwards [pcfSect_eventually_logWedge lo hi] with w hw
    have him : (w + κ * I).im = w.im + κ := by simp
    have h1 : -π < (w + κ * I).im := by rw [him]; linarith [Real.pi_pos]
    have h2 : (w + κ * I).im ≤ π := by rw [him]; linarith [Real.pi_pos]
    refine ⟨exp_ne_zero _, ?_⟩
    rw [pcfSect_arg_exp h1 h2, him, abs_le]
    constructor <;> linarith

/-- `U(b, e^v) = e^{-e^{2v}/4 - (b+1/2) v} G(b, e^v)` for `-π < im v ≤ π`. -/
theorem pcfSect_pcfU_exp (b : ℂ) {v : ℂ} (h1 : -π < v.im) (h2 : v.im ≤ π) :
    pcfU b (exp v) = exp (-exp (2 * v) / 4 - (b + 1 / 2) * v) * pcfSect_G b (exp v) := by
  rw [pcfSect_G, pcfSect_exp_cpow h1 h2, ← Complex.exp_nat_mul, ← mul_assoc, ← mul_assoc,
    ← Complex.exp_add, ← Complex.exp_add]
  push_cast
  ring_nf
  rw [Complex.exp_zero, one_mul]

/-- **DLMF 12.9.1 on the logarithmic plane**: with `z = e^{w + iκ}`, uniformly for
`lo ≤ im w ≤ hi` and `|im w + κ| ≤ 3π/4 - δ`,
`U(b,z) - e^{-z²/4} z^{-b-1/2} ∑_{s<N} u_s(z) = O(|e^{-z²/4} z^{-b-1/2}| |z|^{-2N})`. -/
theorem pcfSect_U_logWedge (b : ℂ) {δ : ℝ} (hδ : 0 < δ) (κ : ℝ) {lo hi : ℝ}
    (hlo : -(3 * π / 4 - δ) ≤ lo + κ) (hhi : hi + κ ≤ 3 * π / 4 - δ) (N : ℕ) :
    (fun w : ℂ => pcfU b (exp (w + κ * I)) - exp (-exp (2 * (w + κ * I)) / 4 -
        (b + 1 / 2) * (w + κ * I)) * ∑ s ∈ Finset.range N, pcfSect_uTerm b (exp (w + κ * I)) s)
      =O[pcfSect_logWedge lo hi] (fun w : ℂ => ‖exp (-exp (2 * (w + κ * I)) / 4 -
        (b + 1 / 2) * (w + κ * I))‖ * Real.exp (-2 * N * w.re)) := by
  set E : ℂ → ℂ := fun w => exp (-exp (2 * (w + κ * I)) / 4 - (b + 1 / 2) * (w + κ * I))
  have h := ((pcfSect_U_sector b hδ N).comp_tendsto
    (pcfSect_tendsto_exp_logWedge hδ κ hlo hhi))
  have hm := (isBigO_refl E (pcfSect_logWedge lo hi)).mul h
  have hev := pcfSect_eventually_logWedge lo hi
  refine (hm.congr' ?_ EventuallyEq.rfl).trans ?_
  · filter_upwards [hev] with w hw
    have him : (w + κ * I).im = w.im + κ := by simp
    have h1 : -π < (w + κ * I).im := by rw [him]; linarith [Real.pi_pos]
    have h2 : (w + κ * I).im ≤ π := by rw [him]; linarith [Real.pi_pos]
    simp only [Function.comp_apply, E]
    rw [pcfSect_pcfU_exp b h1 h2]
    ring
  · refine IsBigO.of_bound 1 (Eventually.of_forall fun w => ?_)
    simp only [Function.comp_apply, norm_mul, norm_zpow, Complex.norm_exp, one_mul, E]
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le]
    refine le_of_eq ?_
    congr 1
    rw [show (w + κ * I).re = w.re by simp, zpow_neg, zpow_mul, zpow_ofNat, zpow_natCast,
      ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1
    push_cast
    ring

/-- Transferring an `O`-bound with exponential envelope through a constant factor. -/
theorem pcfSect_isBigO_const_mul_envelope {α : Type*} {l : Filter α} {f E : α → ℂ}
    {e T : α → ℝ} (C : ℂ) {K : ℝ} (hK : 0 ≤ K) (h : f =O[l] (fun w => ‖E w‖ * e w))
    (he : ∀ w, 0 ≤ e w) (hT : ∀ w, ‖C * E w‖ * e w ≤ K * T w) :
    (fun w => C * f w) =O[l] T := by
  obtain ⟨M, hM0, hM⟩ := h.exists_pos
  refine IsBigO.of_bound (M * K) ?_
  filter_upwards [hM.bound] with w hw
  rw [norm_mul]
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (he w))] at hw
  calc ‖C‖ * ‖f w‖ ≤ ‖C‖ * (M * (‖E w‖ * e w)) := by gcongr
    _ = M * (‖C * E w‖ * e w) := by rw [norm_mul]; ring
    _ ≤ M * (K * T w) := mul_le_mul_of_nonneg_left (hT w) hM0.le
    _ ≤ M * K * ‖T w‖ := by rw [← mul_assoc]; gcongr; exact Real.le_norm_self _

/-- Equality of exponentials whose exponents differ by `2πik`. -/
theorem pcfSect_exp_eq_of_eq_add {X Y : ℂ} (k : ℤ) (h : X = Y + k * (2 * π * I)) :
    exp X = exp Y := by
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The term `(1/2 - a)_{2s} / (s! (2z²)^s)` of DLMF 12.9.2. -/
def pcfSect_vTerm (a z : ℂ) (s : ℕ) : ℂ :=
  poch (1 / 2 - a) (2 * s) / ((s.factorial : ℂ) * (2 * z ^ 2) ^ s)

/-- `u_s(b, z)` depends only on `z²`. -/
theorem pcfSect_uTerm_congr_sq (b : ℂ) {z z' : ℂ} (h : z ^ 2 = z' ^ 2) (s : ℕ) :
    pcfSect_uTerm b z s = pcfSect_uTerm b z' s := by
  rw [pcfSect_uTerm, pcfSect_uTerm, h]

/-- `u_s(-a, z') = v_s(a, z)` when `z'² = -z²`. -/
theorem pcfSect_uTerm_neg_eq_vTerm (a : ℂ) {z z' : ℂ} (h : z' ^ 2 = -z ^ 2) (s : ℕ) :
    pcfSect_uTerm (-a) z' s = pcfSect_vTerm a z s := by
  rw [pcfSect_uTerm, pcfSect_vTerm, h, show 1 / 2 + -a = 1 / 2 - a by ring,
    show 2 * -z ^ 2 = -1 * (2 * z ^ 2) by ring, mul_pow]
  have hf : (s.factorial : ℂ) ≠ 0 := by exact_mod_cast s.factorial_ne_zero
  by_cases hz : (2 * z ^ 2) ^ s = 0
  · simp [hz]
  · field_simp

/-- `e^{2(w + iκ)}` for the four quarter turns used in DLMF 12.9.3–12.9.4. -/
theorem pcfSect_exp_two_mul_add (w : ℂ) (κ : ℝ) :
    exp (2 * (w + κ * I)) = exp (2 * w) * exp ((2 * κ : ℝ) * I) := by
  rw [← Complex.exp_add]; push_cast; ring_nf

/-! ### The expansion of `V(a,z)` (DLMF 12.9.2) -/

/-- Sectors at infinity are monotone in the opening. -/
theorem pcfSect_sector_mono {α β : ℝ} (h : α ≤ β) : sector α ≤ sector β :=
  inf_le_inf_left _ (principal_mono.mpr fun _ hz => ⟨hz.1, hz.2.trans h⟩)

/-- `re (z²) ≥ sin (2δ) |z|²` for `|ph z| ≤ π/4 - δ`. -/
theorem pcfSect_re_sq_ge {z : ℂ} (hz : z ≠ 0) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π / 4)
    (harg : |arg z| ≤ π / 4 - δ) : Real.sin (2 * δ) * ‖z‖ ^ 2 ≤ (z ^ 2).re := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hre : z.re = ‖z‖ * Real.cos (arg z) := by rw [Complex.cos_arg hz]; field_simp
  have him : z.im = ‖z‖ * Real.sin (arg z) := by rw [Complex.sin_arg]; field_simp
  have hsq : (z ^ 2).re = ‖z‖ ^ 2 * Real.cos (2 * arg z) := by
    rw [sq, Complex.mul_re, hre, him, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (arg z)]
  rw [hsq, mul_comm]
  gcongr
  rw [← Real.cos_pi_div_two_sub, ← Real.cos_abs (2 * arg z), abs_mul, abs_two]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
    (by linarith)

/-- `e^{-z²/2} z^w = O(z^{-2N})` in the sector `|ph z| ≤ π/4 - δ`. -/
theorem pcfSect_exp_neg_sq_mul_cpow_isBigO (w : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π / 4)
    (N : ℕ) : (fun z : ℂ => exp (-z ^ 2 / 2) * z ^ w) =O[sector (π / 4 - δ)]
      (fun z : ℂ => z ^ (-(2 * N : ℤ))) := by
  set c := Real.sin (2 * δ) with hc
  have hc0 : 0 < c := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (w.re + 2 * N) (c / 2)
    (by positivity)).eventually (ge_mem_nhds (zero_lt_one' ℝ))
  have h1 : ∀ᶠ z in sector (π / 4 - δ), ‖z‖ ^ (w.re + 2 * N) * Real.exp (-(c / 2) * ‖z‖) ≤ 1 :=
    (inf_le_left : sector (π / 4 - δ) ≤ _) (tendsto_comap.eventually ht)
  have h2 : ∀ᶠ z in sector (π / 4 - δ), 1 ≤ ‖z‖ :=
    (inf_le_left : sector (π / 4 - δ) ≤ _) (tendsto_comap.eventually (eventually_ge_atTop 1))
  have h3 : ∀ᶠ z in sector (π / 4 - δ), z ≠ 0 ∧ |arg z| ≤ π / 4 - δ :=
    (inf_le_right : sector (π / 4 - δ) ≤ _) (mem_principal.mpr fun _ hz => hz)
  refine IsBigO.of_bound (Real.exp (π * |w.im|)) ?_
  filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz3.1
  rw [norm_mul, Complex.norm_exp, norm_zpow, Complex.norm_cpow_of_ne_zero hz3.1]
  have hre := pcfSect_re_sq_ge hz3.1 hδ hδπ hz3.2
  have hexp : Real.exp (-z ^ 2 / 2).re ≤ Real.exp (-(c / 2) * ‖z‖) := by
    have hr2 : (-z ^ 2 / 2 : ℂ).re = -(z ^ 2).re / 2 := by simp
    rw [Real.exp_le_exp, hr2]
    rw [← hc] at hre
    have : ‖z‖ ≤ ‖z‖ ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hc0.le]
  have harg : (Real.exp (arg z * w.im))⁻¹ ≤ Real.exp (π * |w.im|) := by
    rw [← Real.exp_neg, Real.exp_le_exp]
    have := abs_arg_le_pi z
    calc -(arg z * w.im) ≤ |arg z| * |w.im| := by rw [← abs_mul]; exact neg_le_abs _
      _ ≤ π * |w.im| := by gcongr
  have hsplit : ‖z‖ ^ w.re = ‖z‖ ^ (w.re + 2 * N) * ‖z‖ ^ (-(2 * N : ℤ)) := by
    rw [← Real.rpow_intCast, ← Real.rpow_add hn]; push_cast; ring_nf
  rw [div_eq_mul_inv, hsplit]
  have hp : 0 ≤ ‖z‖ ^ (-(2 * N : ℤ)) := zpow_nonneg (norm_nonneg _) _
  calc Real.exp (-z ^ 2 / 2).re * (‖z‖ ^ (w.re + 2 * N) * ‖z‖ ^ (-(2 * N : ℤ)) *
        (Real.exp (arg z * w.im))⁻¹)
      ≤ Real.exp (-(c / 2) * ‖z‖) * (‖z‖ ^ (w.re + 2 * N) * ‖z‖ ^ (-(2 * N : ℤ)) *
        Real.exp (π * |w.im|)) := by gcongr
    _ = (‖z‖ ^ (w.re + 2 * N) * Real.exp (-(c / 2) * ‖z‖)) *
        (Real.exp (π * |w.im|) * ‖z‖ ^ (-(2 * N : ℤ))) := by ring
    _ ≤ 1 * (Real.exp (π * |w.im|) * ‖z‖ ^ (-(2 * N : ℤ))) := by gcongr
    _ = _ := one_mul _

/-- `z ↦ iz` maps `|ph z| ≤ π/4 - δ` into `|ph z| ≤ 3π/4 - δ`, with `arg (iz) = arg z + π/2`. -/
theorem pcfSect_arg_I_mul {z : ℂ} (hz : z ≠ 0) (h : |arg z| ≤ π / 2) :
    arg (I * z) = arg z + π / 2 := by
  have e1 : ((π / 2 : ℝ) : ℂ) * I = π / 2 * I := by push_cast; ring
  have : I * z = exp (log z + (π / 2 : ℝ) * I) := by
    rw [Complex.exp_add, Complex.exp_log hz, e1, Complex.exp_pi_div_two_mul_I]; ring
  have him : (log z + ((π / 2 : ℝ) : ℂ) * I).im = arg z + π / 2 := by simp [Complex.log_im]
  rw [this, pcfSect_arg_exp, him] <;> rw [him] <;>
    linarith [(abs_le.mp h).1, (abs_le.mp h).2, Real.pi_pos]

theorem pcfSect_tendsto_I_mul {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun z : ℂ => I * z) (sector (π / 4 - δ)) (sector (3 * π / 4 - δ)) := by
  refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr ?_⟩
  · have hn : (fun z : ℂ => ‖z‖) ∘ (fun z : ℂ => I * z) = fun z => ‖z‖ := by
      funext z; simp
    rw [hn]
    exact tendsto_comap.mono_left inf_le_left
  · filter_upwards [(inf_le_right : sector (π / 4 - δ) ≤ _) (mem_principal_self _)] with z hz
    refine ⟨mul_ne_zero I_ne_zero hz.1, ?_⟩
    rw [pcfSect_arg_I_mul hz.1 (by linarith [hz.2, Real.pi_pos]), abs_le]
    constructor <;> linarith [(abs_le.mp hz.2).1, (abs_le.mp hz.2).2]

/-- **DLMF 12.9.2**: uniformly in `|ph z| ≤ π/4 - δ`,
`√(π/2) e^{-z²/4} z^{-a+1/2} V(a,z) - ∑_{s<N} (1/2-a)_{2s}/(s! (2z²)^s) = O(z^{-2N})`. -/
theorem pcfSect_V_sector (a : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π / 4) (N : ℕ) :
    (fun z : ℂ => (Real.sqrt (π / 2) : ℂ) * exp (-z ^ 2 / 4) * z ^ (-a + 1 / 2) * pcfV a z -
      ∑ s ∈ Finset.range N, pcfSect_vTerm a z s) =O[sector (π / 4 - δ)]
      (fun z : ℂ => z ^ (-(2 * N : ℤ))) := by
  have hl := pcfSect_eventually_sector (π / 4 - δ)
  have hsec := pcfSect_sector_mono (show π / 4 - δ ≤ 3 * π / 4 - δ by linarith [Real.pi_pos])
  -- the main term, from `U(-a, iz)`
  have h1 : (fun z : ℂ => pcfSect_G (-a) (I * z) - ∑ s ∈ Finset.range N,
      pcfSect_uTerm (-a) (I * z) s) =O[sector (π / 4 - δ)] (fun z : ℂ => z ^ (-(2 * N : ℤ))) := by
    refine ((pcfSect_U_sector (-a) hδ N).comp_tendsto (pcfSect_tendsto_I_mul hδ)).trans ?_
    refine IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_)
    simp
  -- the recessive term, from `U(a, z)`
  set C : ℂ := (Real.sqrt (π / 2) : ℂ) * (-I / Gamma (1 / 2 - a))
  have h2 : (fun z : ℂ => C * (exp (-z ^ 2 / 2) * z ^ (-2 * a) * pcfSect_G a z))
      =O[sector (π / 4 - δ)] (fun z : ℂ => z ^ (-(2 * N : ℤ))) := by
    have hG : (fun z : ℂ => pcfSect_G a z) =O[sector (π / 4 - δ)] (fun _ : ℂ => (1 : ℂ)) := by
      have := ((pcfSect_U_sector a hδ 0).mono hsec)
      simpa using this
    have := ((pcfSect_exp_neg_sq_mul_cpow_isBigO (-2 * a) hδ hδπ N).mul hG).const_mul_left C
    simpa [mul_assoc] using this
  refine (h1.add h2).congr' ?_ EventuallyEq.rfl
  filter_upwards [hl, (inf_le_right : sector (π / 4 - δ) ≤ _) (mem_principal_self _)]
    with z hz hz'
  have hz0 := hz.1
  have hIz : I * z ≠ 0 := mul_ne_zero I_ne_zero hz0
  have hsum : ∑ s ∈ Finset.range N, pcfSect_uTerm (-a) (I * z) s =
      ∑ s ∈ Finset.range N, pcfSect_vTerm a z s :=
    Finset.sum_congr rfl fun s _ => pcfSect_uTerm_neg_eq_vTerm a (by ring_nf; rw [I_sq]; ring) s
  have hcp : (I * z) ^ (a - 1 / 2) = z ^ (a - 1 / 2) * exp (I * π * (a / 2 - 1 / 4)) := by
    have h := Complex.cpow_mul_exp_ofReal_mul_I hz0 (θ := π / 2)
      (by linarith [(abs_le.mp hz'.2).1, Real.pi_pos])
      (by linarith [(abs_le.mp hz'.2).2, Real.pi_pos]) (a - 1 / 2)
    rw [show ((π / 2 : ℝ) : ℂ) * I = π / 2 * I by push_cast; ring,
      Complex.exp_pi_div_two_mul_I, mul_comm z I] at h
    rw [h]; congr 2; ring
  have hU' : pcfU (-a) (I * z) = exp (z ^ 2 / 4) * (I * z) ^ (a - 1 / 2) *
      pcfSect_G (-a) (I * z) := by
    have h0 : (I * z) ^ (a - 1 / 2) * (I * z) ^ (-a + 1 / 2) = 1 := by
      rw [← Complex.cpow_add _ _ hIz, show a - 1 / 2 + (-a + 1 / 2) = 0 by ring,
        Complex.cpow_zero]
    have he : exp (z ^ 2 / 4) * exp ((I * z) ^ 2 / 4) = 1 := by
      rw [← Complex.exp_add, show z ^ 2 / 4 + (I * z) ^ 2 / 4 = z ^ 2 / 4 * (1 + I ^ 2) by ring,
        I_sq]; simp
    simp only [pcfSect_G]
    calc pcfU (-a) (I * z) = (exp (z ^ 2 / 4) * exp ((I * z) ^ 2 / 4)) *
          ((I * z) ^ (a - 1 / 2) * (I * z) ^ (-a + 1 / 2)) * pcfU (-a) (I * z) := by
          rw [he, h0]; ring
      _ = _ := by ring
  have hUa : pcfU a z = exp (-z ^ 2 / 4) * z ^ (-a - 1 / 2) * pcfSect_G a z := by
    have h0 : z ^ (-a - 1 / 2) * z ^ (a + 1 / 2) = 1 := by
      rw [← Complex.cpow_add _ _ hz0, show -a - 1 / 2 + (a + 1 / 2) = 0 by ring,
        Complex.cpow_zero]
    have he : exp (-z ^ 2 / 4) * exp (z ^ 2 / 4) = 1 := by
      rw [← Complex.exp_add]; ring_nf; simp
    simp only [pcfSect_G]
    calc pcfU a z = (exp (-z ^ 2 / 4) * exp (z ^ 2 / 4)) *
          (z ^ (-a - 1 / 2) * z ^ (a + 1 / 2)) * pcfU a z := by rw [he, h0]; ring
      _ = _ := by ring
  have k1 : (Real.sqrt (π / 2) : ℂ) * (Real.sqrt (2 / π) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by positivity),
      show π / 2 * (2 / π) = 1 by field_simp, Real.sqrt_one, Complex.ofReal_one]
  have k2 : exp (-z ^ 2 / 4) * exp (z ^ 2 / 4) = 1 := by
    rw [← Complex.exp_add]; ring_nf; simp
  have k3 : z ^ (-a + 1 / 2) * z ^ (a - 1 / 2) = 1 := by
    rw [← Complex.cpow_add _ _ hz0, show -a + 1 / 2 + (a - 1 / 2) = 0 by ring, Complex.cpow_zero]
  have k4 : exp (-I * π * (a / 2 - 1 / 4)) * exp (I * π * (a / 2 - 1 / 4)) = 1 := by
    rw [← Complex.exp_add]; ring_nf; simp
  have kk : ((Real.sqrt (π / 2) : ℂ) * (Real.sqrt (2 / π) : ℂ)) *
      (exp (-z ^ 2 / 4) * exp (z ^ 2 / 4)) * (z ^ (-a + 1 / 2) * z ^ (a - 1 / 2)) *
      (exp (-I * π * (a / 2 - 1 / 4)) * exp (I * π * (a / 2 - 1 / 4))) = 1 := by
    rw [k1, k2, k3, k4]; ring
  have k56 : (exp (-z ^ 2 / 4) * exp (-z ^ 2 / 4)) * (z ^ (-a + 1 / 2) * z ^ (-a - 1 / 2)) =
      exp (-z ^ 2 / 2) * z ^ (-2 * a) := by
    rw [← Complex.exp_add, ← Complex.cpow_add _ _ hz0]; ring_nf
  rw [pcfV_eq_mul_I, hU', hcp, hUa, ← hsum]
  simp only [C]
  linear_combination (-pcfSect_G (-a) (I * z)) * kk -
    (Real.sqrt (π / 2) : ℂ) * (-I / Gamma (1 / 2 - a)) * pcfSect_G a z * k56

end DLMF.Confluent
