/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Continuation

/-!
# Continuation of `₂F₁` in the argument to the cut plane (DLMF §15.2(i))

DLMF defines `F(a,b;c;z)` on the cut plane `ℂ ∖ [1, ∞)` as the analytic continuation of
the Gauss series. We construct this continuation for the regularized function
`𝐅(a,b;c;z) = F(a,b;c;z)/Γ(c)`, with no hypothesis on the parameters:

* `cutPlane := {z | 1 - z ∈ slitPlane}` is open and star-shaped about `0`, so the identity
  principle `eqOn_cutPlane_of_eqOn_disk` lifts every identity from the unit disk.
* `regularizedGaussHGIntegral a b c z = (Γ(b) Γ(c-b))⁻¹ ∫₀¹ t^(b-1) (1-t)^(c-b-1) (1 - z t)^(-a) dt`
  is analytic on the cut plane for `Re b > 0`, `Re (c - b) > 0` (differentiation under the
  integral sign), and equals `𝐅` on the disk (`ordinaryHypergeometric_eq_integral`).
* `regularizedGaussHG a b c z` is defined for all parameters by shifting `b` and `c` into the Euler
  region with the hypothesis-free contiguous relations `regularizedGaussHGFun_contiguous_c` and
  `regularizedGaussHGFun_contiguous_shift_b`, through a recursion with fuel
  `shiftMeasure b c`.
* `regularizedGaussHG_eq_regularizedGaussHGFun` (agreement with `𝐅` on the disk),
  `analyticOnNhd_regularizedGaussHG`
  (analyticity on the cut plane) and `regularizedGaussHG_unique` characterize the continuation.

The second half lifts the derivative formulas, the contiguous relations and the Euler and
Pfaff transformations to the cut plane.
-/

@[expose] public section

open Complex Filter Set MeasureTheory intervalIntegral
open scoped Real Nat Topology Interval ComplexOrder

noncomputable section

set_option autoImplicit false

namespace DLMF.Hypergeometric

/-! ### The cut plane -/

/-- The cut plane `ℂ ∖ [1, ∞)`, the natural domain of `₂F₁` in its argument. -/
def cutPlane : Set ℂ := {z | 1 - z ∈ slitPlane}

/-- `z` lies in the cut plane `ℂ \ [1, ∞)` iff `1 - z` lies in the slit plane. -/
theorem mem_cutPlane {z : ℂ} : z ∈ cutPlane ↔ 1 - z ∈ slitPlane := Iff.rfl

/-- The cut plane `ℂ \ [1, ∞)` is open. -/
theorem isOpen_cutPlane : IsOpen cutPlane :=
  isOpen_slitPlane.preimage (continuous_const.sub continuous_id)

/-- `0` lies in the cut plane. -/
theorem zero_mem_cutPlane : (0 : ℂ) ∈ cutPlane := by
  show (1 : ℂ) - 0 ∈ slitPlane
  simp

/-- On the cut plane, `1 - z ≠ 0`. -/
theorem one_sub_ne_zero_of_mem_cutPlane {z : ℂ} (hz : z ∈ cutPlane) : 1 - z ≠ 0 :=
  slitPlane_ne_zero hz

/-- The open unit disk lies in the cut plane. -/
theorem mem_cutPlane_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : z ∈ cutPlane := by
  show 1 - z ∈ slitPlane
  rw [mem_slitPlane_iff]
  left
  simp only [sub_re, one_re]
  linarith [re_le_norm z]

/-- The cut plane is star-convex about `0`. -/
theorem starConvex_zero_cutPlane : StarConvex ℝ 0 cutPlane := by
  intro y hy a b ha hb hab
  have h := starConvex_one_slitPlane (hy : 1 - y ∈ slitPlane) ha hb hab
  show 1 - (a • (0 : ℂ) + b • y) ∈ slitPlane
  convert h using 1
  simp only [smul_zero, zero_add, Complex.real_smul]
  have : (a : ℂ) + b = 1 := by exact_mod_cast hab
  linear_combination (-1 : ℂ) * this

/-- The cut plane is preconnected. -/
theorem isPreconnected_cutPlane : IsPreconnected cutPlane :=
  (starConvex_zero_cutPlane.isPathConnected zero_mem_cutPlane).isConnected.isPreconnected

/-- The identity principle on the cut plane: analytic functions agreeing near `0` agree on
the whole cut plane. -/
theorem eqOn_cutPlane_of_eventuallyEq {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f cutPlane)
    (hg : AnalyticOnNhd ℂ g cutPlane) (h : f =ᶠ[𝓝 0] g) : EqOn f g cutPlane :=
  hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_cutPlane zero_mem_cutPlane h

/-- The identity principle on the cut plane: analytic functions agreeing on a small disk
about `0` agree on the whole cut plane. -/
theorem eqOn_cutPlane_of_eqOn_ball {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f cutPlane)
    (hg : AnalyticOnNhd ℂ g cutPlane) {r : ℝ} (hr : 0 < r)
    (h : ∀ z : ℂ, ‖z‖ < r → f z = g z) : EqOn f g cutPlane :=
  eqOn_cutPlane_of_eventuallyEq hf hg (by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with z hz
    exact h z (by simpa using hz))

/-- The identity principle on the cut plane: analytic functions agreeing on the unit disk
agree on the whole cut plane. -/
theorem eqOn_cutPlane_of_eqOn_disk {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f cutPlane)
    (hg : AnalyticOnNhd ℂ g cutPlane) (h : ∀ z : ℂ, ‖z‖ < 1 → f z = g z) :
    EqOn f g cutPlane :=
  eqOn_cutPlane_of_eqOn_ball hf hg one_pos h

/-- For `z` in the cut plane and `t ∈ [0,1]`, `1 - z t` lies in the slit plane. -/
theorem one_sub_mul_mem_slitPlane {z : ℂ} (hz : z ∈ cutPlane) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    1 - z * t ∈ slitPlane := by
  have hz' : ¬ (1 - z ≤ 0) := mem_slitPlane_iff_not_le_zero.mp hz
  rw [mem_slitPlane_iff_not_le_zero]
  intro hle
  apply hz'
  rw [Complex.le_def] at hle ⊢
  simp only [sub_re, sub_im, one_re, one_im, mul_re, mul_im, ofReal_re, ofReal_im, mul_zero,
    sub_zero, zero_re, zero_im, zero_add] at hle ⊢
  obtain ⟨hre, him⟩ := hle
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · subst h0
    norm_num at hre
  · have him' : z.im = 0 := by
      have : z.im * t = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right h0.ne'
    refine ⟨?_, by simp [him']⟩
    nlinarith [ht.2]

/-! ### The Euler integral on the cut plane -/

/-- The integrand of Euler's integral 15.6.1. -/
def eulerKernel (a b c z : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)

/-- The `z`-derivative of the integrand. -/
def eulerKernelDeriv (a b c z : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
    (-a * (1 - z * t) ^ (-a - 1) * -(1 * (t : ℂ)))

/-- Euler's integral in the regularized normalization:
`𝐅(a,b;c;z) = (Γ(b) Γ(c-b))⁻¹ ∫₀¹ t^(b-1) (1-t)^(c-b-1) (1 - z t)^(-a) dt`. -/
def regularizedGaussHGIntegral (a b c z : ℂ) : ℂ :=
  (Gamma b * Gamma (c - b))⁻¹ * ∫ t : ℝ in (0 : ℝ)..1, eulerKernel a b c z t

/-- On the unit disk the Euler integral is the regularized Gauss function. -/
theorem regularizedGaussHGIntegral_eq_regularizedGaussHGFun {a b c : ℂ} (hb : 0 < b.re)
    (hcb : 0 < (c - b).re)
    {z : ℂ} (hz : ‖z‖ < 1) : regularizedGaussHGIntegral a b c z
        = regularizedGaussHGFun a b c z := by
  have hc := not_neg_nat_of_re_pos (re_c_pos_of hb hcb)
  have hΓc : Gamma c ≠ 0 := Gamma_ne_zero hc
  have hΓb : Gamma b ≠ 0 := Gamma_ne_zero (not_neg_nat_of_re_pos hb)
  have hΓcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero (not_neg_nat_of_re_pos hcb)
  rw [regularizedGaussHGFun_eq_div_Gamma hc, ordinaryHypergeometric_eq_integral hb hcb hz,
    regularizedGaussHGIntegral]
  simp only [eulerKernel]
  set I := ∫ t : ℝ in (0 : ℝ)..1,
    (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a) with hI
  field_simp

/-- For `z` in the cut plane, `t ↦ (1 - z t)^s` is continuous on `[0, 1]`. -/
theorem continuousOn_one_sub_mul_cpow {z : ℂ} (hz : z ∈ cutPlane) (s : ℂ) :
    ContinuousOn (fun t : ℝ => (1 - z * t) ^ s) (Icc (0 : ℝ) 1) :=
  (continuousOn_const.sub (continuousOn_const.mul continuous_ofReal.continuousOn)).cpow
    continuousOn_const (fun _ ht => one_sub_mul_mem_slitPlane hz ht)

/-- For `Re c > Re b > 0` and `z` in the cut plane, the Euler kernel is integrable on `[0, 1]`. -/
theorem intervalIntegrable_eulerKernel {a b c : ℂ} (hb : 0 < b.re) (hcb : 0 < (c - b).re)
    {z : ℂ} (hz : z ∈ cutPlane) : IntervalIntegrable (eulerKernel a b c z) volume 0 1 := by
  have h := (betaIntegral_convergent hb hcb).mul_continuousOn
    (by rw [uIcc_of_le zero_le_one]; exact continuousOn_one_sub_mul_cpow hz (-a))
  exact h

/-- For `z` in the cut plane and `t ∈ [0, 1]`, the Euler kernel is complex-differentiable in `z`,
  with derivative `eulerKernelDeriv`. -/
theorem hasDerivAt_eulerKernel {a b c z : ℂ} (hz : z ∈ cutPlane) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun w => eulerKernel a b c w t) (eulerKernelDeriv a b c z t) z := by
  have h1 : HasDerivAt (fun w : ℂ => 1 - w * (t : ℂ)) (-(1 * (t : ℂ))) z :=
    ((hasDerivAt_id' z).mul_const _).const_sub 1
  have h2 := h1.cpow_const (c := -a) (one_sub_mul_mem_slitPlane hz ht)
  exact h2.const_mul _

/-- Differentiation under the integral sign for Euler's integral. -/
theorem hasDerivAt_integral_eulerKernel {a b c : ℂ} (hb : 0 < b.re) (hcb : 0 < (c - b).re)
    {z₀ : ℂ} (hz₀ : z₀ ∈ cutPlane) :
    HasDerivAt (fun z => ∫ t : ℝ in (0 : ℝ)..1, eulerKernel a b c z t)
      (∫ t : ℝ in (0 : ℝ)..1, eulerKernelDeriv a b c z₀ t) z₀ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_cutPlane z₀ hz₀
  have hclosed : Metric.closedBall z₀ (ε / 2) ⊆ cutPlane :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  have hsub : Metric.ball z₀ (ε / 2) ⊆ cutPlane := Metric.ball_subset_closedBall.trans hclosed
  -- a uniform bound for the `z`-dependent factor of the derivative
  set G : ℝ × ℂ → ℂ := fun p => -a * (1 - p.2 * p.1) ^ (-a - 1) * -(1 * (p.1 : ℂ)) with hG
  have hGcont : ContinuousOn G (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall z₀ (ε / 2)) := by
    have hpow : ContinuousOn (fun p : ℝ × ℂ => (1 - p.2 * p.1) ^ (-a - 1))
        (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall z₀ (ε / 2)) := by
      refine (continuousOn_const.sub (continuous_snd.continuousOn.mul
        (continuous_ofReal.comp continuous_fst).continuousOn)).cpow continuousOn_const ?_
      intro p hp
      exact one_sub_mul_mem_slitPlane (hclosed hp.2) hp.1
    exact (continuousOn_const.mul hpow).mul
      (continuousOn_const.mul (continuous_ofReal.comp continuous_fst).continuousOn).neg
  obtain ⟨C, hC⟩
      := (isCompact_Icc.prod (isCompact_closedBall z₀ (ε / 2))).exists_bound_of_continuousOn
    hGcont
  have hbeta := betaIntegral_convergent hb hcb
  have hIoc : ∀ t ∈ Ι (0 : ℝ) 1, t ∈ Icc (0 : ℝ) 1 := fun t ht => by
    rw [uIoc_of_le zero_le_one] at ht
    exact Ioc_subset_Icc_self ht
  have hderiv_int : ∀ z ∈ Metric.closedBall z₀ (ε / 2),
      IntervalIntegrable (eulerKernelDeriv a b c z) volume 0 1 := by
    intro z hz
    refine hbeta.mul_continuousOn ?_
    rw [uIcc_of_le zero_le_one]
    have : ContinuousOn (fun t : ℝ => G (t, z)) (Icc (0 : ℝ) 1) :=
      hGcont.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun t ht => ⟨ht, hz⟩)
    exact this
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun z t => eulerKernel a b c z t)
    (F' := fun z t => eulerKernelDeriv a b c z t) (bound := fun t =>
      ‖(t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)‖ * C)
    (Metric.ball_mem_nhds z₀ (half_pos hε)) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [Metric.ball_mem_nhds z₀ (half_pos hε)] with z hz
    exact (intervalIntegrable_iff.mp (intervalIntegrable_eulerKernel hb hcb (hsub hz))).1
  · exact intervalIntegrable_eulerKernel hb hcb hz₀
  · exact (intervalIntegrable_iff.mp
      (hderiv_int z₀ (Metric.mem_closedBall_self (half_pos hε).le))).1
  · refine ae_of_all _ fun t ht z hz => ?_
    have ht' := hIoc t ht
    show ‖(t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * G (t, z)‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC (t, z) ⟨ht', Metric.ball_subset_closedBall hz⟩)
      (norm_nonneg _)
  · exact hbeta.norm.mul_const C
  · refine ae_of_all _ fun t ht z hz => ?_
    exact hasDerivAt_eulerKernel (hsub hz) (hIoc t ht)

/-- Euler's integral is analytic in `z` on the cut plane when `Re b > 0`, `Re (c - b) > 0`. -/
theorem analyticOnNhd_regularizedGaussHGIntegral (a : ℂ) {b c : ℂ} (hb : 0 < b.re)
    (hcb : 0 < (c - b).re) :
    AnalyticOnNhd ℂ (regularizedGaussHGIntegral a b c) cutPlane := by
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_cutPlane
  intro z hz
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold regularizedGaussHGIntegral
  exact (differentiableAt_const _).mul (hasDerivAt_integral_eulerKernel hb hcb hz).differentiableAt

/-! ### The continuation for all parameters -/

/-- Number of `b`-shifts needed to reach `Re b ≥ 1`. -/
def shiftB (b : ℂ) : ℕ := ⌈1 - b.re⌉₊

/-- Number of `c`-shifts needed so that `Re (c - b) ≥ 1` still holds after the `b`-shifts. -/
def shiftC (b c : ℂ) : ℕ := ⌈1 + shiftB b - (c - b).re⌉₊

/-- The recursion fuel. -/
def shiftMeasure (b c : ℂ) : ℕ := shiftB b + shiftC b c

/-- For `x > 0`, `⌈x - 1⌉₊ < ⌈x⌉₊`. -/
theorem ceil_sub_one_lt_ceil {x : ℝ} (hx : 0 < x) : ⌈x - 1⌉₊ < ⌈x⌉₊ := by
  have h1 : 0 < ⌈x⌉₊ := Nat.ceil_pos.mpr hx
  have : ⌈x - 1⌉₊ ≤ ⌈x⌉₊ - 1 :=
    Nat.ceil_le.mpr (by push_cast [Nat.cast_sub h1]; linarith [Nat.le_ceil x])
  omega

/-- Raising `c` by one decreases a positive `c`-shift count. -/
theorem shiftC_add_one_lt {b c : ℂ} (h : 0 < shiftC b c) : shiftC b (c + 1) < shiftC b c := by
  have hx : 0 < 1 + (shiftB b : ℝ) - (c - b).re := Nat.ceil_pos.mp h
  have : 1 + (shiftB b : ℝ) - (c + 1 - b).re = 1 + (shiftB b : ℝ) - (c - b).re - 1 := by
    simp only [sub_re, add_re, one_re]; ring
  unfold shiftC
  rw [this]
  exact ceil_sub_one_lt_ceil hx

/-- Raising `b` by one decreases a positive `b`-shift count. -/
theorem shiftB_add_one_lt {b : ℂ} (h : 0 < shiftB b) : shiftB (b + 1) < shiftB b := by
  have hx : 0 < 1 - b.re := Nat.ceil_pos.mp h
  have : 1 - (b + 1).re = 1 - b.re - 1 := by simp only [add_re, one_re]; ring
  unfold shiftB
  rw [this]
  exact ceil_sub_one_lt_ceil hx

/-- No `c`-shift is needed when `Re (c - b) ≥ 1 + shiftB b`. -/
theorem shiftC_eq_zero_of {b c : ℂ} (h : (c - b).re ≥ 1 + shiftB b) : shiftC b c = 0 := by
  unfold shiftC
  rw [Nat.ceil_eq_zero]
  linarith

/-- When both shift counts vanish, `Re b ≥ 1` and `Re (c - b) ≥ 1`, so Euler's integral applies. -/
theorem euler_region_of_shift_eq_zero {b c : ℂ} (hB : shiftB b = 0) (hC : shiftC b c = 0) :
    1 ≤ b.re ∧ 1 ≤ (c - b).re := by
  have hB' : 1 - b.re ≤ 0 := Nat.ceil_eq_zero.mp hB
  have hC' : 1 + (shiftB b : ℝ) - (c - b).re ≤ 0 := Nat.ceil_eq_zero.mp hC
  rw [hB, Nat.cast_zero] at hC'
  constructor <;> linarith

/-- The recursion with fuel: shift `c` while `shiftC > 0`, then shift `b` while `shiftB > 0`,
then use Euler's integral. -/
def regularizedGaussHGAux : ℕ → ℂ → ℂ → ℂ → ℂ → ℂ
  | 0, a, b, c, z => regularizedGaussHGIntegral a b c z
  | n + 1, a, b, c, z =>
    if 0 < shiftC b c then
      (c - a) * regularizedGaussHGAux n a b (c + 1) z + a
          * regularizedGaussHGAux n (a + 1) b (c + 1) z
    else if 0 < shiftB b then
      regularizedGaussHGAux n a (b + 1) c z - a * z
          * regularizedGaussHGAux n (a + 1) (b + 1) (c + 1) z
    else regularizedGaussHGIntegral a b c z

/-- The regularized Gauss function `𝐅(a,b;c;z) = ₂F₁(a,b;c;z)/Γ(c)` continued to the cut
plane `ℂ ∖ [1, ∞)`, for all parameters (DLMF §15.2(i)). Its domain is `cutPlane`; the series is
Mathlib's `regularizedGaussHGFun` and the Euler integral is `regularizedGaussHGIntegral`. -/
def regularizedGaussHG (a b c z : ℂ) : ℂ := regularizedGaussHGAux (shiftMeasure b c) a b c z

/-- Unfolding the recursion when a `c`-shift is needed: the contiguous relation in `c`. -/
theorem regularizedGaussHGAux_succ_of_pos_c {n : ℕ} {a b c z : ℂ} (h : 0 < shiftC b c) :
    regularizedGaussHGAux (n + 1) a b c z =
      (c - a) * regularizedGaussHGAux n a b (c + 1) z + a
          * regularizedGaussHGAux n (a + 1) b (c + 1) z := by
  simp only [regularizedGaussHGAux, h, ↓reduceIte]

/-- Unfolding the recursion when only a `b`-shift is needed: the contiguous relation in `b`. -/
lemma regularizedGaussHGAux_succ_of_pos_b {n : ℕ} {a b c z : ℂ} (hc : ¬ 0 < shiftC b c)
    (hb : 0 < shiftB b) :
    regularizedGaussHGAux (n + 1) a b c z =
      regularizedGaussHGAux n a (b + 1) c z - a * z
          * regularizedGaussHGAux n (a + 1) (b + 1) (c + 1) z := by
  simp only [regularizedGaussHGAux, hc, hb, ↓reduceIte]

/-- Unfolding the recursion when no shift is needed: Euler's integral. -/
theorem regularizedGaussHGAux_succ_of_zero {n : ℕ} {a b c z : ℂ} (hc : ¬ 0 < shiftC b c)
    (hb : ¬ 0 < shiftB b) : regularizedGaussHGAux (n + 1) a b c z
        = regularizedGaussHGIntegral a b c z := by
  simp only [regularizedGaussHGAux, hc, hb, ↓reduceIte]

/-- The measures of the recursive calls in the `b`-shift branch. -/
theorem shiftMeasure_b_step {b c : ℂ} (hc : ¬ 0 < shiftC b c) (hb : 0 < shiftB b) :
    shiftMeasure (b + 1) c < shiftMeasure b c ∧
      shiftMeasure (b + 1) (c + 1) < shiftMeasure b c := by
  have hC0 : shiftC b c = 0 := Nat.eq_zero_of_not_pos hc
  have hlt := shiftB_add_one_lt hb
  have hre : c.re - b.re ≥ 1 + shiftB b := by
    have := (Nat.ceil_eq_zero.mp hC0 : 1 + (shiftB b : ℝ) - (c - b).re ≤ 0)
    simp only [sub_re] at this
    linarith
  have hB' : (shiftB (b + 1) : ℝ) + 1 ≤ shiftB b := by exact_mod_cast hlt
  have h1 : shiftC (b + 1) c = 0 := by
    apply shiftC_eq_zero_of
    simp only [sub_re, add_re, one_re]
    linarith
  have h2 : shiftC (b + 1) (c + 1) = 0 := by
    apply shiftC_eq_zero_of
    simp only [sub_re, add_re, one_re]
    linarith
  unfold shiftMeasure
  rw [h1, h2, hC0]
  omega

/-- On the unit disk, every stage of the recursion agrees with `𝐅` once the fuel suffices. -/
lemma regularizedGaussHGAux_eq_regularized (n : ℕ) {a b c : ℂ} (hn : shiftMeasure b c ≤ n) {z : ℂ}
    (hz : ‖z‖ < 1) : regularizedGaussHGAux n a b c z = regularizedGaussHGFun a b c z := by
  induction n generalizing a b c with
  | zero =>
    have h0 : shiftB b = 0 ∧ shiftC b c = 0 := by unfold shiftMeasure at hn; omega
    obtain ⟨h1, h2⟩ := euler_region_of_shift_eq_zero h0.1 h0.2
    exact regularizedGaussHGIntegral_eq_regularizedGaussHGFun (by linarith) (by linarith) hz
  | succ n ih =>
    by_cases hc : 0 < shiftC b c
    · rw [regularizedGaussHGAux_succ_of_pos_c hc]
      have hlt := shiftC_add_one_lt hc
      have hn' : shiftMeasure b (c + 1) ≤ n := by unfold shiftMeasure at hn ⊢; omega
      rw [ih hn', ih hn', regularizedGaussHGFun_contiguous_c a b c hz]
    · by_cases hb : 0 < shiftB b
      · rw [regularizedGaussHGAux_succ_of_pos_b hc hb]
        obtain ⟨hm1, hm2⟩ := shiftMeasure_b_step hc hb
        rw [ih (a := a) (b := b + 1) (c := c) (by omega),
          ih (a := a + 1) (b := b + 1) (c := c + 1) (by omega)]
        linear_combination (-1 : ℂ) * regularizedGaussHGFun_contiguous_shift_b a b c hz
      · rw [regularizedGaussHGAux_succ_of_zero hc hb]
        obtain ⟨h1, h2⟩ := euler_region_of_shift_eq_zero (Nat.eq_zero_of_not_pos hb)
          (Nat.eq_zero_of_not_pos hc)
        exact regularizedGaussHGIntegral_eq_regularizedGaussHGFun (by linarith) (by linarith) hz

/-- Every stage of the recursion is analytic on the cut plane once the fuel suffices. -/
lemma analyticOnNhd_regularizedGaussHGAux (n : ℕ) {a b c : ℂ} (hn : shiftMeasure b c ≤ n) :
    AnalyticOnNhd ℂ (fun z => regularizedGaussHGAux n a b c z) cutPlane := by
  induction n generalizing a b c with
  | zero =>
    have h0 : shiftB b = 0 ∧ shiftC b c = 0 := by unfold shiftMeasure at hn; omega
    obtain ⟨h1, h2⟩ := euler_region_of_shift_eq_zero h0.1 h0.2
    exact analyticOnNhd_regularizedGaussHGIntegral a (by linarith) (by linarith)
  | succ n ih =>
    by_cases hc : 0 < shiftC b c
    · simp_rw [regularizedGaussHGAux_succ_of_pos_c hc]
      have hlt := shiftC_add_one_lt hc
      have hn' : shiftMeasure b (c + 1) ≤ n := by unfold shiftMeasure at hn ⊢; omega
      exact (analyticOnNhd_const.mul (ih hn')).add (analyticOnNhd_const.mul (ih hn'))
    · by_cases hb : 0 < shiftB b
      · simp_rw [regularizedGaussHGAux_succ_of_pos_b hc hb]
        obtain ⟨hm1, hm2⟩ := shiftMeasure_b_step hc hb
        exact (ih (a := a) (b := b + 1) (c := c) (by omega)).sub
          ((analyticOnNhd_const.mul analyticOnNhd_id).mul
            (ih (a := a + 1) (b := b + 1) (c := c + 1) (by omega)))
      · simp_rw [regularizedGaussHGAux_succ_of_zero hc hb]
        obtain ⟨h1, h2⟩ := euler_region_of_shift_eq_zero (Nat.eq_zero_of_not_pos hb)
          (Nat.eq_zero_of_not_pos hc)
        exact analyticOnNhd_regularizedGaussHGIntegral a (by linarith) (by linarith)

/-- On the unit disk the continuation is the regularized Gauss series. -/
theorem regularizedGaussHG_eq_regularizedGaussHGFun (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    regularizedGaussHG a b c z = regularizedGaussHGFun a b c z :=
  regularizedGaussHGAux_eq_regularized _ le_rfl hz

/-- The continuation is analytic on the cut plane. -/
theorem analyticOnNhd_regularizedGaussHG (a b c : ℂ) : AnalyticOnNhd ℂ (regularizedGaussHG a b c)
    cutPlane :=
  analyticOnNhd_regularizedGaussHGAux _ le_rfl

/-- The continued regularized function `𝐅(a, b; c; z)` is analytic on the cut plane. -/
@[fun_prop]
theorem analyticAt_regularizedGaussHG (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    AnalyticAt ℂ (regularizedGaussHG a b c) z :=
  analyticOnNhd_regularizedGaussHG a b c z hz

/-- The continued regularized function `𝐅(a, b; c; z)` is differentiable on the cut plane. -/
@[fun_prop]
theorem differentiableAt_regularizedGaussHG (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    DifferentiableAt ℂ (regularizedGaussHG a b c) z :=
  (analyticAt_regularizedGaussHG a b c hz).differentiableAt

/-- Uniqueness: any function analytic on the cut plane that agrees with `𝐅` on the unit disk
is the continuation. -/
theorem regularizedGaussHG_unique {a b c : ℂ} {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f cutPlane)
    (h : ∀ z : ℂ, ‖z‖ < 1 → f z = regularizedGaussHGFun a b c z) :
    EqOn f (regularizedGaussHG a b c) cutPlane :=
  eqOn_cutPlane_of_eqOn_disk hf (analyticOnNhd_regularizedGaussHG a b c) fun z hz =>
    (h z hz).trans (regularizedGaussHG_eq_regularizedGaussHGFun a b c hz).symm

/-- The continuation equals the Euler integral on the whole cut plane, for `Re b > 0` and
`Re (c - b) > 0`. -/
theorem regularizedGaussHG_eq_regularizedGaussHGIntegral {a b c : ℂ} (hb : 0 < b.re)
    (hcb : 0 < (c - b).re) {z : ℂ} (hz : z ∈ cutPlane) :
    regularizedGaussHG a b c z = regularizedGaussHGIntegral a b c z :=
  (regularizedGaussHG_unique (analyticOnNhd_regularizedGaussHGIntegral a hb hcb)
    (fun _ hw => regularizedGaussHGIntegral_eq_regularizedGaussHGFun hb hcb hw) hz).symm

/-- The classical `₂F₁` on the unit disk is `Γ(c)` times the continuation. -/
theorem ordinaryHypergeometric_eq_Gamma_mul_regularizedGaussHG {a b c : ℂ}
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    {z : ℂ} (hz : ‖z‖ < 1) : ₂F₁ a b c z = Gamma c * regularizedGaussHG a b c z := by
  rw [regularizedGaussHG_eq_regularizedGaussHGFun a b c hz, regularizedGaussHGFun_eq_div_Gamma hc,
    mul_div_cancel₀ _ (Gamma_ne_zero hc)]

/-- Symmetry `𝐅(a,b;c;z) = 𝐅(b,a;c;z)` on the cut plane. -/
theorem regularizedGaussHG_symm (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    regularizedGaussHG a b c z = regularizedGaussHG b a c z :=
  eqOn_cutPlane_of_eqOn_disk (analyticOnNhd_regularizedGaussHG a b c)
      (analyticOnNhd_regularizedGaussHG b a c)
    (fun z hz => by rw
        [regularizedGaussHG_eq_regularizedGaussHGFun a b c hz,
            regularizedGaussHG_eq_regularizedGaussHGFun b a c hz,
      regularizedGaussHGFun_symm]) hz

/-! ### Identities on the cut plane

Every identity between analytic expressions proved on the unit disk lifts to the cut plane by
`eqOn_cutPlane_of_eqOn_disk`. -/

/-- 15.5.1 on the cut plane: `𝐅'(a,b;c;z) = a b 𝐅(a+1,b+1;c+1;z)`. -/
theorem deriv_regularizedGaussHG (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    deriv (regularizedGaussHG a b c) z = a * b * regularizedGaussHG (a + 1) (b + 1) (c + 1) z :=
  eqOn_cutPlane_of_eqOn_disk (f := deriv (regularizedGaussHG a b c))
    (g := fun z => a * b * regularizedGaussHG (a + 1) (b + 1) (c + 1) z)
    (analyticOnNhd_regularizedGaussHG a b c).deriv (by intro z hz; fun_prop (disch := assumption))
    (fun z hz => by
      have heq : regularizedGaussHG a b c =ᶠ[𝓝 z] regularizedGaussHGFun a b c := by
        filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with w hw
        exact regularizedGaussHG_eq_regularizedGaussHGFun a b c hw
      rw [heq.deriv_eq, deriv_regularizedGaussHGFun a b c hz,
          regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz])
    hz

/-- 15.5.2 on the cut plane: `𝐅⁽ⁿ⁾(a,b;c;z) = (a)ₙ (b)ₙ 𝐅(a+n,b+n;c+n;z)`. -/
theorem iteratedDeriv_regularizedGaussHG (a b c : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ cutPlane) :
    iteratedDeriv n (regularizedGaussHG a b c) z =
      poch a n * poch b n * regularizedGaussHG (a + n) (b + n) (c + n) z := by
  induction n generalizing z with
  | zero => simp [iteratedDeriv_zero, poch_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv n (regularizedGaussHG a b c) =ᶠ[𝓝 z]
        fun w => poch a n * poch b n * regularizedGaussHG (a + n) (b + n) (c + n) w := by
      filter_upwards [isOpen_cutPlane.mem_nhds hz] with w hw
      exact ih hw
    rw [heq.deriv_eq, deriv_const_mul _ (differentiableAt_regularizedGaussHG _ _ _ hz),
      deriv_regularizedGaussHG _ _ _ hz, poch_succ, poch_succ,
      show a + ((n + 1 : ℕ) : ℂ) = a + n + 1 by push_cast; ring,
      show b + ((n + 1 : ℕ) : ℂ) = b + n + 1 by push_cast; ring,
      show c + ((n + 1 : ℕ) : ℂ) = c + n + 1 by push_cast; ring]
    ring

/-- `regularizedGaussHGFun_contiguous_c` on the cut plane. -/
theorem regularizedGaussHG_contiguous_c (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    regularizedGaussHG a b c z =
      (c - a) * regularizedGaussHG a b (c + 1) z + a * regularizedGaussHG (a + 1) b (c + 1) z :=
  eqOn_cutPlane_of_eqOn_disk (f := fun z => regularizedGaussHG a b c z)
    (g := fun z => (c - a) * regularizedGaussHG a b (c + 1) z + a
        * regularizedGaussHG (a + 1) b (c + 1) z)
    (by intro z hz; fun_prop (disch := assumption)) (by intro z hz; fun_prop (disch := assumption))
    (fun z hz => by
      simp only [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz]
      exact regularizedGaussHGFun_contiguous_c a b c hz) hz

/-- `regularizedGaussHGFun_contiguous_shift_b` on the cut plane. -/
theorem regularizedGaussHG_contiguous_shift_b (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    regularizedGaussHG a b c z - regularizedGaussHG a (b + 1) c z = -(a * z)
        * regularizedGaussHG (a + 1) (b + 1) (c + 1) z :=
  eqOn_cutPlane_of_eqOn_disk
      (f := fun z => regularizedGaussHG a b c z - regularizedGaussHG a (b + 1) c z)
    (g := fun z => -(a * z) * regularizedGaussHG (a + 1) (b + 1) (c + 1) z)
    (by intro z hz; fun_prop (disch := assumption)) (by intro z hz; fun_prop (disch := assumption))
    (fun z hz => by
      simp only [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz]
      exact regularizedGaussHGFun_contiguous_shift_b a b c hz) hz

/-- `regularizedGaussHGFun_contiguous_a` on the cut plane. -/
theorem regularizedGaussHG_contiguous_a (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    (c - a) * regularizedGaussHG (a - 1) b c z + (2 * a - c + (b - a) * z)
        * regularizedGaussHG a b c z + a * (z - 1) * regularizedGaussHG (a + 1) b c z = 0 :=
  eqOn_cutPlane_of_eqOn_disk
      (f := fun z => (c - a) * regularizedGaussHG (a - 1) b c z + (2 * a - c + (b - a) * z)
          * regularizedGaussHG a b c z + a * (z - 1) * regularizedGaussHG (a + 1) b c z)
    (g := fun z => 0)
    (by intro z hz; fun_prop (disch := assumption)) (by intro z hz; fun_prop (disch := assumption))
    (fun z hz => by
      simp only [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz]
      exact regularizedGaussHGFun_contiguous_a a b c hz) hz

/-- `regularizedGaussHGFun_contiguous_ab` on the cut plane. -/
theorem regularizedGaussHG_contiguous_ab (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    (b - a) * regularizedGaussHG a b c z + a * regularizedGaussHG (a + 1) b c z - b
        * regularizedGaussHG a (b + 1) c z = 0 :=
  eqOn_cutPlane_of_eqOn_disk
      (f := fun z => (b - a) * regularizedGaussHG a b c z + a * regularizedGaussHG (a + 1) b c z - b
          * regularizedGaussHG a (b + 1) c z)
    (g := fun z => 0)
    (by intro z hz; fun_prop (disch := assumption)) (by intro z hz; fun_prop (disch := assumption))
    (fun z hz => by
      simp only [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz]
      exact regularizedGaussHGFun_contiguous_ab a b c hz) hz

/-- `regularizedGaussHGFun_contiguous_a_b_pred` on the cut plane. -/
theorem regularizedGaussHG_contiguous_a_b_pred (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    (c - a - b) * regularizedGaussHG a b c z + a * (1 - z) * regularizedGaussHG (a + 1) b c z
        - (c - b) * regularizedGaussHG a (b - 1) c z = 0 :=
  eqOn_cutPlane_of_eqOn_disk
      (f := fun z => (c - a - b) * regularizedGaussHG a b c z + a * (1 - z)
          * regularizedGaussHG (a + 1) b c z - (c - b) * regularizedGaussHG a (b - 1) c z)
    (g := fun z => 0)
    (by intro z hz; fun_prop (disch := assumption)) (by intro z hz; fun_prop (disch := assumption))
    (fun z hz => by
      simp only [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz]
      exact regularizedGaussHGFun_contiguous_a_b_pred a b c hz) hz

/-- `regularizedGaussHGFun_contiguous_c_succ_deriv` on the cut plane. -/
theorem regularizedGaussHG_contiguous_c_succ_deriv (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    (1 - z) * (a * b) * regularizedGaussHG (a + 1) (b + 1) (c + 1) z = (c - a) * (c - b)
        * regularizedGaussHG a b (c + 1) z + (a + b - c) * regularizedGaussHG a b c z :=
  eqOn_cutPlane_of_eqOn_disk
      (f := fun z => (1 - z) * (a * b) * regularizedGaussHG (a + 1) (b + 1) (c + 1) z)
    (g := fun z => (c - a) * (c - b) * regularizedGaussHG a b (c + 1) z + (a + b - c)
        * regularizedGaussHG a b c z)
    (by intro z hz; fun_prop (disch := assumption)) (by intro z hz; fun_prop (disch := assumption))
    (fun z hz => by
      simp only [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz]
      exact regularizedGaussHGFun_contiguous_c_succ_deriv a b c hz) hz

/-- `regularizedGaussHGFun_contiguous_a_c_succ` on the cut plane. -/
theorem regularizedGaussHG_contiguous_a_c_succ (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    (a + (b - c) * z) * regularizedGaussHG a b c z - a * (1 - z) * regularizedGaussHG (a + 1) b c z
        + (c - a) * (c - b) * z * regularizedGaussHG a b (c + 1) z = 0 :=
  eqOn_cutPlane_of_eqOn_disk
      (f := fun z => (a + (b - c) * z) * regularizedGaussHG a b c z - a * (1 - z)
          * regularizedGaussHG (a + 1) b c z + (c - a) * (c - b) * z
              * regularizedGaussHG a b (c + 1) z)
    (g := fun z => 0)
    (by intro z hz; fun_prop (disch := assumption)) (by intro z hz; fun_prop (disch := assumption))
    (fun z hz => by
      simp only [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz]
      exact regularizedGaussHGFun_contiguous_a_c_succ a b c hz) hz

/-- `regularizedGaussHGFun_contiguous_a_succ_c_pred` on the cut plane. -/
theorem regularizedGaussHG_contiguous_a_succ_c_pred (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    (c - a - 1) * regularizedGaussHG a b c z + a * regularizedGaussHG (a + 1) b c z
        - regularizedGaussHG a b (c - 1) z = 0 :=
  eqOn_cutPlane_of_eqOn_disk
      (f := fun z => (c - a - 1) * regularizedGaussHG a b c z + a * regularizedGaussHG (a + 1) b c z
          - regularizedGaussHG a b (c - 1) z)
    (g := fun z => 0)
    (by intro z hz; fun_prop (disch := assumption)) (by intro z hz; fun_prop (disch := assumption))
    (fun z hz => by
      simp only [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz]
      exact regularizedGaussHGFun_contiguous_a_succ_c_pred a b c hz) hz

/-- `regularizedGaussHGFun_contiguous_a_pred_c_succ` on the cut plane. -/
theorem regularizedGaussHG_contiguous_a_pred_c_succ (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    (1 - z) * regularizedGaussHG a b c z - regularizedGaussHG (a - 1) b c z + (c - b) * z
        * regularizedGaussHG a b (c + 1) z = 0 :=
  eqOn_cutPlane_of_eqOn_disk
      (f := fun z => (1 - z) * regularizedGaussHG a b c z - regularizedGaussHG (a - 1) b c z
          + (c - b) * z * regularizedGaussHG a b (c + 1) z)
    (g := fun z => 0)
    (by intro z hz; fun_prop (disch := assumption)) (by intro z hz; fun_prop (disch := assumption))
    (fun z hz => by
      simp only [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz]
      exact regularizedGaussHGFun_contiguous_a_pred_c_succ a b c hz) hz

/-- `regularizedGaussHGFun_contiguous_a_pred_c_pred` on the cut plane. -/
theorem regularizedGaussHG_contiguous_a_pred_c_pred (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    (a - 1 + (b + 1 - c) * z) * regularizedGaussHG a b c z + (c - a)
        * regularizedGaussHG (a - 1) b c z - (1 - z) * regularizedGaussHG a b (c - 1) z = 0 :=
  eqOn_cutPlane_of_eqOn_disk
      (f := fun z => (a - 1 + (b + 1 - c) * z) * regularizedGaussHG a b c z + (c - a)
          * regularizedGaussHG (a - 1) b c z - (1 - z) * regularizedGaussHG a b (c - 1) z)
    (g := fun z => 0)
    (by intro z hz; fun_prop (disch := assumption)) (by intro z hz; fun_prop (disch := assumption))
    (fun z hz => by
      simp only [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz]
      exact regularizedGaussHGFun_contiguous_a_pred_c_pred a b c hz) hz

/-- `regularizedGaussHGFun_contiguous_c_three` on the cut plane. -/
theorem regularizedGaussHG_contiguous_c_three (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    (z - 1) * regularizedGaussHG a b (c - 1) z + (c - 1 - (2 * c - a - b - 1) * z)
        * regularizedGaussHG a b c z + (c - a) * (c - b) * z * regularizedGaussHG a b (c + 1) z
            = 0 :=
  eqOn_cutPlane_of_eqOn_disk
      (f := fun z => (z - 1) * regularizedGaussHG a b (c - 1) z + (c - 1 - (2 * c - a - b - 1) * z)
          * regularizedGaussHG a b c z + (c - a) * (c - b) * z * regularizedGaussHG a b (c + 1) z)
    (g := fun z => 0)
    (by intro z hz; fun_prop (disch := assumption)) (by intro z hz; fun_prop (disch := assumption))
    (fun z hz => by
      simp only [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz]
      exact regularizedGaussHGFun_contiguous_c_three a b c hz) hz

/-- `regularizedGaussHGFun_contiguous_diagonal` on the cut plane. -/
theorem regularizedGaussHG_contiguous_diagonal (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    z * (1 - z) * (a + 1) * (b + 1) * regularizedGaussHG (a + 2) (b + 2) (c + 2) z
        + (c - (a + b + 1) * z) * regularizedGaussHG (a + 1) (b + 1) (c + 1) z
            - regularizedGaussHG a b c z = 0 :=
  eqOn_cutPlane_of_eqOn_disk
      (f := fun z => z * (1 - z) * (a + 1) * (b + 1) * regularizedGaussHG (a + 2) (b + 2) (c + 2) z
          + (c - (a + b + 1) * z) * regularizedGaussHG (a + 1) (b + 1) (c + 1) z
              - regularizedGaussHG a b c z)
    (g := fun z => 0)
    (by intro z hz; fun_prop (disch := assumption)) (by intro z hz; fun_prop (disch := assumption))
    (fun z hz => by
      simp only [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz]
      exact regularizedGaussHGFun_contiguous_diagonal a b c hz) hz

/-- Euler's transformation 15.8.1 on the cut plane:
`𝐅(a,b;c;z) = (1-z)^(c-a-b) 𝐅(c-a,c-b;c;z)`. -/
theorem regularizedGaussHG_euler (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    regularizedGaussHG a b c z = (1 - z) ^ (c - a - b) * regularizedGaussHG (c - a) (c - b) c z :=
  eqOn_cutPlane_of_eqOn_disk (f := fun z => regularizedGaussHG a b c z)
    (g := fun z => (1 - z) ^ (c - a - b) * regularizedGaussHG (c - a) (c - b) c z)
    (by intro z hz; fun_prop (disch := assumption))
    (by
      intro z hz
      exact ((analyticAt_const.sub analyticAt_id).cpow analyticAt_const hz).mul
        (analyticAt_regularizedGaussHG _ _ _ hz))
    (fun z hz => by
      simp only [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz]
      exact regularizedGaussHGFun_euler a b c hz) hz

/-- The Pfaff map `z ↦ z/(z-1)` preserves the cut plane. -/
theorem div_sub_one_mem_cutPlane {z : ℂ} (hz : z ∈ cutPlane) : z / (z - 1) ∈ cutPlane := by
  have h0 : 1 - z ≠ 0 := one_sub_ne_zero_of_mem_cutPlane hz
  have h1 : z - 1 ≠ 0 := fun h => h0 (by linear_combination -h)
  show 1 - z / (z - 1) ∈ slitPlane
  have : 1 - z / (z - 1) = (1 - z)⁻¹ := by
    field_simp
    ring
  rw [this]
  have hz' : 1 - z ∈ slitPlane := hz
  rw [mem_slitPlane_iff] at hz' ⊢
  rw [inv_re, inv_im]
  have hn : 0 < normSq (1 - z) := normSq_pos.mpr h0
  rcases hz' with h | h
  · exact Or.inl (div_pos h hn)
  · right
    rw [neg_div, neg_ne_zero]
    exact div_ne_zero h hn.ne'

/-- Pfaff's transformation 15.8.1 on the cut plane:
`𝐅(a,b;c;z) = (1-z)^(-a) 𝐅(a,c-b;c;z/(z-1))`. -/
theorem regularizedGaussHG_pfaff (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    regularizedGaussHG a b c z = (1 - z) ^ (-a) * regularizedGaussHG a (c - b) c (z / (z - 1)) :=
  eqOn_cutPlane_of_eqOn_ball (f := fun z => regularizedGaussHG a b c z)
    (g := fun z => (1 - z) ^ (-a) * regularizedGaussHG a (c - b) c (z / (z - 1)))
    (by intro z hz; fun_prop (disch := assumption))
    (by
      intro z hz
      have h1 : z - 1 ≠ 0 := fun h => one_sub_ne_zero_of_mem_cutPlane hz (by linear_combination -h)
      have hmap : AnalyticAt ℂ (fun w : ℂ => w / (w - 1)) z :=
        AnalyticAt.fun_div (f := fun w : ℂ => w) (g := fun w : ℂ => w - 1) (x := z)
          analyticAt_id (analyticAt_id.sub analyticAt_const) h1
      exact ((analyticAt_const.sub analyticAt_id).cpow analyticAt_const hz).mul
        ((analyticAt_regularizedGaussHG a (c - b) c (div_sub_one_mem_cutPlane hz)).comp
          (f := fun w : ℂ => w / (w - 1)) hmap))
    (r := 1 / 2) (by norm_num)
    (fun z hz => by
      have hz1 : ‖z‖ < 1 := by linarith
      have hlow : 1 - ‖z‖ ≤ ‖z - 1‖ := by
        have := norm_sub_norm_le (1 : ℂ) z
        rwa [norm_one, norm_sub_rev] at this
      have hzt : ‖z / (z - 1)‖ < 1 := by
        rw [norm_div, div_lt_one (by linarith)]
        linarith
      simp only [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz1,
          regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hzt]
      exact regularizedGaussHGFun_pfaff a b c hz1 hzt) hz

end DLMF.Hypergeometric
