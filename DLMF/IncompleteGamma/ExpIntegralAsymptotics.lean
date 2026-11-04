/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.ExponentialIntegral
public import DLMFMathlib.Analysis.Asymptotics.WatsonRotated

/-!
# Generalized exponential integral asymptotics, DLMF §8.20

Asymptotic expansions of the generalized exponential integral `E_p(z)` for large `z`, on
sectors of the logarithmic plane, and for large order `p` (DLMF §8.20).

## Main definitions

* `logStripAtTop`: the strip filter `re w → ∞` with `|im w + θ| ≤ π/2 - δ`.
* `expIntLargeOrderPolynomial`: the polynomials `A_k(λ)` of DLMF 8.20.4, with `A₀ = 1`.

## Main results

* `expIntegralE_exact_remainder`: the expansion with exact remainder, DLMF 8.20.1.
* `expIntegralE_eq_exp_mul_integral`, `genExpIntEOnLog_eq_integral_rotate`: Laplace
  representations of `E_p`, the latter rotated on the logarithmic plane.
* `genExpIntEOnLog_strip_asymptotic`: Watson's expansion of `E_p` on a strip.
* `expIntegralE_log_sector_asymptotic`: the expansion on `|ph z| ≤ 3π/2 - δ`, DLMF 8.20.2.
* `expIntegralE_extended_sector_asymptotic`: the extended-sector expansion with connection
  terms, DLMF 8.20.3.
* `expIntLargeOrderPolynomial_initial`, `expIntLargeOrderPolynomial_degree`: DLMF 8.20.5 and
  the degree statement of DLMF §8.20(ii).
* `expIntegralE_large_order_uniform`: the uniform large-order expansion, DLMF 8.20.6.

## Implementation notes

The uniform expansion 8.20.6 follows by repeated integration by parts in
`e^{λp} E_p(λp) = ∫₁^∞ e^{-λp(t-1)} t^{-p} dt`. The `k`-th step produces
`g_k(t) = A_k(λt)/(1+λt)^{2k}`, which is bounded uniformly in `λ ≥ 0` and `t ≥ 0` since
`deg A_k ≤ k`, and the remainder is controlled by `(1+λ) ∫₁^∞ e^{-λp(t-1)} t^{-p} dt ≤ 1/(p-1)`.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat Interval
open DLMF.Core

namespace DLMF.Confluent

/-- Formula under the stated hypotheses: `expIntegralE p z=exp (-z)/z*(∑ k ∈ Finset.range N, (-1 :
ℂ)^k*pochhammer p k/z^k)+(-1 : ℂ)^N*pochhammer p N/z^N*expIntegralE (N+p) z`. -/
@[dlmf 8.20.E1]
theorem expIntegralE_exact_remainder (p : ℂ) {z : ℂ} (hz : z ≠ 0) (N : ℕ) :
    expIntegralE p z=exp
        (-z)/z*(∑ k ∈ Finset.range N, (-1 : ℂ)^k*pochhammer p k/z^k)+(-1 : ℂ)^N*pochhammer p
        N/z^N*expIntegralE (N+p) z := by
  induction N with
  | zero => simp [pochhammer]
  | succ N ih =>
    have h := expIntegralE_add_one ((N:ℂ)+p) hz
    rw [show (N:ℂ)+p+1 = ((N+1:ℕ):ℂ)+p by push_cast; ring] at h
    rw [ih, Finset.sum_range_succ, pochhammer_succ, pow_succ, pow_succ]
    have hzN : z^N ≠ 0 := pow_ne_zero _ hz
    set S := ∑ k ∈ Finset.range N, (-1 : ℂ)^k*pochhammer p k/z^k
    field_simp
    linear_combination (-1:ℂ)^N*pochhammer p N*h

/-- Polynomial bound for `(1+t)^{-p}` on the sector `|arg t| ≤ |θ| < π`. -/
theorem exists_norm_one_add_cpow_neg_le (p : ℂ) {θ : ℝ} (hθ : |θ| < π) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → ∀ y : ℝ, |y| ≤ |θ| →
      ‖(1 + (r : ℂ) * exp (y * I)) ^ (-p)‖ ≤ C * (1 + r) ^ |p.re| := by
  obtain ⟨c, hc0, hc⟩ := exists_pos_le_norm_one_add_ofReal_mul_exp (Φ := |θ|) hθ
  set c' := min c 1 with hc'
  have hc'0 : 0 < c' := lt_min hc0 one_pos
  have hc'1 : c' ≤ 1 := min_le_right _ _
  refine ⟨Real.exp (π * |p.im|) * c' ^ (-|p.re|), by positivity, fun r hr y hy => ?_⟩
  set t : ℂ := 1 + (r : ℂ) * exp (y * I)
  have hlo : c' ≤ ‖t‖ := (min_le_left _ _).trans (hc r hr y hy)
  have hhi : ‖t‖ ≤ 1 + r := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr, norm_exp_ofReal_mul_I,
      mul_one]
  have ht0 : 0 < ‖t‖ := hc'0.trans_le hlo
  have h1 : ‖t ^ (-p)‖ ≤ ‖t‖ ^ (-p).re * Real.exp (π * |p.im|) := by
    refine (norm_cpow_le t (-p)).trans ?_
    rw [div_eq_mul_inv, ← Real.exp_neg]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.rpow_nonneg (norm_nonneg _) _)
    have h1 := Complex.abs_arg_le_pi t
    have h2 : |arg t * (-p).im| ≤ π * |p.im| := by
      rw [abs_mul, neg_im, abs_neg]; exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    linarith [neg_abs_le (arg t * (-p).im)]
  have h2 : ‖t‖ ^ (-p).re ≤ c' ^ (-|p.re|) * (1 + r) ^ |p.re| := by
    rw [neg_re]
    have hA : 1 ≤ c' ^ (-|p.re|) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hc'0 hc'1
      (by linarith [abs_nonneg p.re])
    have hB : 1 ≤ (1 + r) ^ |p.re| := Real.one_le_rpow (by linarith) (abs_nonneg _)
    rcases le_total 0 (-p.re) with h | h
    · calc ‖t‖ ^ (-p.re) ≤ (1 + r) ^ (-p.re) := Real.rpow_le_rpow ht0.le hhi h
        _ ≤ (1 + r) ^ |p.re| := Real.rpow_le_rpow_of_exponent_le (by linarith)
            (by rw [← abs_neg]; exact le_abs_self _)
        _ ≤ _ := le_mul_of_one_le_left (by positivity) hA
    · calc ‖t‖ ^ (-p.re) ≤ c' ^ (-p.re) := Real.rpow_le_rpow_of_nonpos hc'0 hlo h
        _ = c' ^ (-|p.re|) := by
            rw [abs_of_nonneg (by linarith : 0 ≤ p.re)]
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hB
  calc ‖t ^ (-p)‖ ≤ ‖t‖ ^ (-p).re * Real.exp (π * |p.im|) := h1
    _ ≤ c' ^ (-|p.re|) * (1 + r) ^ |p.re| * Real.exp (π * |p.im|) := by gcongr
    _ = _ := by ring

/-- `E_p(z) = e^{-z} ∫₀^∞ e^{-zt} (1+t)^{-p} dt` for `re z > 0`. -/
theorem expIntegralE_eq_exp_mul_integral {p z : ℂ} (hz : 0 < z.re) :
    expIntegralE p z = cexp (-z) * ∫ t : ℝ in Ioi 0, cexp (-(z * t)) * (1 + (t : ℂ)) ^ (-p) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  rw [expIntegralE_eq_exp_mul_kummerU p hz0, kummerU_laplace (by norm_num) hz]
  simp only [Gamma_one, div_one, one_mul, sub_self, cpow_zero, mul_one,
    show (2 - p : ℂ) - 1 - 1 = -p by ring, neg_mul]

/-- On the principal strip the logarithmic-plane `E_p` is the principal one. -/
theorem genExpIntEOnLog_eq_expIntegralE (p : ℂ) {w : ℂ} (h1 : -π < w.im) (h2 : w.im ≤ π) :
    genExpIntEOnLog p w = expIntegralE p (cexp w) := by
  rw [genExpIntEOnLog, expIntegralE, upperIncompleteGammaOnLog_eq_upperIncompleteGamma _ h1 h2,
    cpow_def_of_ne_zero (Complex.exp_ne_zero w), Complex.log_exp h1 h2, mul_comm w]

/-- `1 + r e^{iy}` lies in the slit plane for `r ≥ 0` and `|y| < π`. -/
theorem one_add_ofReal_mul_exp_mem_slitPlane {r y : ℝ} (hr : 0 ≤ r) (hy : |y| < π) :
    1 + (r : ℂ) * exp (y * I) ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  simp only [add_re, one_re, re_ofReal_mul, exp_ofReal_mul_I_re, add_im, one_im, im_ofReal_mul,
    exp_ofReal_mul_I_im, zero_add]
  by_cases hs : Real.sin y = 0
  · left
    rw [Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [neg_abs_le y]) (by linarith [le_abs_self y])]
      at hs
    rw [hs, Real.cos_zero]; linarith
  · rcases hr.lt_or_eq with hr | hr
    · right; exact mul_ne_zero hr.ne' hs
    · left; rw [← hr]; simp

/-- `re (e^w e^{iy}) = e^{re w} cos (im w + y)`. -/
theorem re_cexp_mul_exp (w : ℂ) (y : ℝ) :
    (cexp w * exp (y * I)).re = Real.exp w.re * Real.cos (w.im + y) := by
  rw [← Complex.exp_add, Complex.exp_re]
  simp

/-- `(1 + r)^k ≤ 2^k (r^k + 1)` for `r, k ≥ 0`. -/
theorem one_add_rpow_le {r k : ℝ} (hr : 0 ≤ r) (hk : 0 ≤ k) :
    (1 + r) ^ k ≤ 2 ^ k * r ^ k + 2 ^ k := by
  rcases le_total r 1 with h | h
  · have : (1 + r) ^ k ≤ 2 ^ k := Real.rpow_le_rpow (by linarith) (by linarith) hk
    have : 0 ≤ 2 ^ k * r ^ k := by positivity
    linarith
  · have : (1 + r) ^ k ≤ (2 * r) ^ k := Real.rpow_le_rpow (by linarith) (by linarith) hk
    rw [Real.mul_rpow (by norm_num) hr] at this
    have : (0 : ℝ) ≤ 2 ^ k := by positivity
    linarith

/-- **Rotated Laplace representation of `E_p` on the logarithmic plane**: for `|θ| < π` and
`|im w + θ| < π/2`,
`E_p(e^w) = e^{-e^w} e^{iθ} ∫₀^∞ e^{-e^w e^{iθ} r} (1 + r e^{iθ})^{-p} dr`. -/
theorem genExpIntEOnLog_eq_integral_rotate (p : ℂ) {θ : ℝ} (hθ : |θ| < π) {w : ℂ}
    (hw : |w.im + θ| < π / 2) :
    genExpIntEOnLog p w = cexp (-cexp w) * (exp (θ * I) * ∫ r in Ioi (0 : ℝ),
      cexp (-(cexp w * exp (θ * I) * r)) * (1 + (r : ℂ) * exp (θ * I)) ^ (-p)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_one_add_cpow_neg_le p hθ
  set k := |p.re| with hk
  have hk0 : 0 ≤ k := abs_nonneg _
  set U : Set ℂ := {w : ℂ | |w.im + θ| < π / 2} with hU
  have hUo : IsOpen U := isOpen_lt (by fun_prop) continuous_const
  have hUc : Convex ℝ U := by
    intro x hx y hy a b ha hb hab
    have hx : |x.im + θ| < π / 2 := hx
    have hy : |y.im + θ| < π / 2 := hy
    show |(a • x + b • y).im + θ| < π / 2
    have he : (a • x + b • y).im + θ = a * (x.im + θ) + b * (y.im + θ) := by
      simp only [add_im, Complex.real_smul, im_ofReal_mul]
      linear_combination θ * hab.symm
    rw [he]
    refine (abs_add_le _ _).trans_lt ?_
    rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    rcases ha.lt_or_eq with ha' | ha'
    · have h1 := mul_lt_mul_of_pos_left hx ha'
      have h2 := mul_le_mul_of_nonneg_left hy.le hb
      have h3 : a * (π / 2) + b * (π / 2) = π / 2 := by rw [← add_mul, hab, one_mul]
      linarith
    · subst ha'; rw [zero_add] at hab; subst hab; simpa using hy
  set G : ℝ → ℂ := fun r => (1 + (r : ℂ) * exp (θ * I)) ^ (-p) with hG
  have hGc : ContinuousOn G (Ioi 0) := fun r hr =>
    (((by fun_prop : Continuous fun r : ℝ => 1 + (r : ℂ) * exp (θ * I)).continuousAt).cpow
      continuousAt_const (one_add_ofReal_mul_exp_mem_slitPlane (le_of_lt hr) hθ)
      ).continuousWithinAt
  have hLd := differentiableOn_integral_cexp_neg_mul_smul_of_le_rpow (G := G) (C := C * 2 ^ k)
    (D := C * 2 ^ k) (k := k) (by linarith) hGc (fun r hr => by
      refine (hC r hr.le θ le_rfl).trans ?_
      have := one_add_rpow_le hr.le hk0
      calc C * (1 + r) ^ k ≤ C * (2 ^ k * r ^ k + 2 ^ k) := mul_le_mul_of_nonneg_left this hC0
        _ = _ := by ring)
  simp only [smul_eq_mul] at hLd
  have hmaps : MapsTo (fun w : ℂ => cexp w * exp (θ * I)) U {w : ℂ | 0 < w.re} := by
    intro v hv
    have hv : |v.im + θ| < π / 2 := hv
    show 0 < (cexp v * exp (θ * I)).re
    rw [re_cexp_mul_exp]
    refine mul_pos (Real.exp_pos _) ?_
    rw [← Real.cos_abs]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [abs_nonneg (v.im + θ), Real.pi_pos], hv⟩
  have hR : DifferentiableOn ℂ (fun w : ℂ => cexp (-cexp w) * (exp (θ * I) * ∫ r in Ioi (0 : ℝ),
      cexp (-(cexp w * exp (θ * I) * r)) * G r)) U :=
    (by fun_prop : Differentiable ℂ fun w : ℂ => cexp (-cexp w)).differentiableOn.mul
      ((differentiableOn_const _).mul (hLd.comp
        ((by fun_prop : Differentiable ℂ fun w : ℂ => cexp w * exp (θ * I)).differentiableOn)
        hmaps))
  have hL : Differentiable ℂ (genExpIntEOnLog p) := fun v => by
    unfold genExpIntEOnLog
    exact (by fun_prop : Differentiable ℂ fun v : ℂ => cexp ((p - 1) * v)) v |>.mul
      (hasDerivAt_upperIncompleteGammaOnLog (1 - p) v).differentiableAt
  -- agreement on the principal strip
  have hagree : ∀ v : ℂ, |v.im| < π / 2 → v ∈ U → genExpIntEOnLog p v =
      cexp (-cexp v) * (exp (θ * I) * ∫ r in Ioi (0 : ℝ),
        cexp (-(cexp v * exp (θ * I) * r)) * G r) := by
    intro v hv hvU
    have hvU : |v.im + θ| < π / 2 := hvU
    have hre : 0 < (cexp v).re := by
      rw [Complex.exp_re]
      refine mul_pos (Real.exp_pos _) ?_
      rw [← Real.cos_abs]
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith [abs_nonneg v.im, Real.pi_pos], hv⟩
    rw [genExpIntEOnLog_eq_expIntegralE p (by linarith [neg_abs_le v.im, Real.pi_pos])
      (by linarith [le_abs_self v.im, Real.pi_pos]), expIntegralE_eq_exp_mul_integral hre]
    congr 1
    refine integral_cexp_neg_mul_mul_eq_rotate (F := fun t : ℂ => (1 + t) ^ (-p))
      (σ := 1) (C := C * 2 ^ k) (k := k) one_pos (fun r hr y hy => ?_) (fun r hr hr1 y hy => ?_)
      (fun r hr y hy => ?_) (fun y hy => ?_)
    · have hy' := (abs_le_abs_of_mem_uIcc_zero hy).trans_lt hθ
      exact (differentiableAt_id.const_add 1).cpow (differentiableAt_const _)
        (one_add_ofReal_mul_exp_mem_slitPlane hr.le hy')
    · refine (hC r hr.le y (abs_le_abs_of_mem_uIcc_zero hy)).trans ?_
      rw [sub_self, Real.rpow_zero, mul_one]
      have : (1 + r) ^ k ≤ 2 ^ k := Real.rpow_le_rpow (by linarith) (by linarith) hk0
      exact mul_le_mul_of_nonneg_left this hC0
    · refine (hC r (by linarith) y (abs_le_abs_of_mem_uIcc_zero hy)).trans ?_
      have : (1 + r) ^ k ≤ (2 * r) ^ k := Real.rpow_le_rpow (by linarith) (by linarith) hk0
      rw [Real.mul_rpow (by norm_num) (by linarith)] at this
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left this hC0
    · rw [re_cexp_mul_exp]
      refine mul_pos (Real.exp_pos _) ?_
      have h2 : |v.im + y| < π / 2 := by
        rcases le_total 0 θ with h | h
        · rw [uIcc_of_le h] at hy
          rw [abs_lt] at hv hvU ⊢; constructor <;> linarith [hy.1, hy.2]
        · rw [uIcc_of_ge h] at hy
          rw [abs_lt] at hv hvU ⊢; constructor <;> linarith [hy.1, hy.2]
      rw [← Real.cos_abs]
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith [abs_nonneg (v.im + y), Real.pi_pos], h2⟩
  -- the identity theorem
  set w₀ : ℂ := ((-(θ / 2) : ℝ) : ℂ) * I with hw₀
  have hw₀im : w₀.im = -(θ / 2) := by simp [hw₀]
  have hw₀P : |w₀.im| < π / 2 := by
    rw [hw₀im, abs_neg, abs_div, abs_two]; linarith
  have hw₀U : w₀ ∈ U := by
    show |w₀.im + θ| < π / 2
    rw [hw₀im, show -(θ / 2) + θ = θ / 2 by ring, abs_div, abs_two]; linarith
  have hev : genExpIntEOnLog p =ᶠ[𝓝 w₀] (fun w : ℂ => cexp (-cexp w) * (exp (θ * I) *
      ∫ r in Ioi (0 : ℝ), cexp (-(cexp w * exp (θ * I) * r)) * G r)) := by
    have hV : IsOpen {v : ℂ | |v.im| < π / 2} := isOpen_lt (by fun_prop) continuous_const
    filter_upwards [hV.mem_nhds hw₀P, hUo.mem_nhds hw₀U] with v hv hvU
    exact hagree v hv hvU
  exact (hL.differentiableOn.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
    (hR.analyticOnNhd hUo) hUc.isPreconnected hw₀U hev hw

/-- The strip filter `re w → ∞` with `|im w + θ| ≤ π/2 - δ`. -/
noncomputable def logStripAtTop (θ δ : ℝ) : Filter ℂ :=
  comap (fun w : ℂ => Real.exp w.re) atTop ⊓ 𝓟 {w : ℂ | |w.im + θ| ≤ π / 2 - δ}

/-- Along the strip filter, `e^w e^{iθ}` tends to infinity within
`sectorAtTop (sin (min δ (π/2)))`. -/
theorem tendsto_cexp_mul_logStripAtTop (θ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun w : ℂ => cexp w * exp (θ * I)) (logStripAtTop θ δ)
      (sectorAtTop (Real.sin (min δ (π / 2)))) := by
  have hnorm : ∀ w : ℂ, ‖cexp w * exp (θ * I)‖ = Real.exp w.re := fun w => by
    rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_exp]
  rw [sectorAtTop, tendsto_inf, tendsto_comap_iff, tendsto_principal]
  constructor
  · have : (fun z : ℂ => ‖z‖) ∘ (fun w : ℂ => cexp w * exp (θ * I)) =
        fun w : ℂ => Real.exp w.re := funext hnorm
    rw [this]
    exact tendsto_comap.mono_left inf_le_left
  · refine (eventually_principal.mpr fun w hw => ?_).filter_mono inf_le_right
    have hw : |w.im + θ| ≤ π / 2 - δ := hw
    show Real.sin (min δ (π / 2)) * ‖cexp w * exp (θ * I)‖ ≤ (cexp w * exp (θ * I)).re
    rw [hnorm, re_cexp_mul_exp, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    rw [← Real.cos_pi_div_two_sub, ← Real.cos_abs (w.im + θ)]
    have hm : min δ (π / 2) ≤ π / 2 := min_le_right _ _
    have hm' : min δ (π / 2) ≤ δ := min_le_left _ _
    have hm0 : 0 < min δ (π / 2) := lt_min hδ (by positivity)
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos])
      (by linarith)

/-- Watson's expansion of `E_p` on a strip of the logarithmic plane. -/
theorem genExpIntEOnLog_strip_asymptotic (p : ℂ) {θ δ : ℝ} (hθ : |θ| < π) (hδ : 0 < δ) :
    HasAsymptoticExpansion (logStripAtTop θ δ) (fun k w => exp (-exp w-(k+1 : ℂ)*w))
      (fun k => (-1 : ℂ)^k*pochhammer p k) (genExpIntEOnLog p) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_one_add_cpow_neg_le p hθ
  set k := |p.re| with hk
  have hk0 : 0 ≤ k := abs_nonneg _
  have hθ1 : -π < θ := by linarith [neg_abs_le θ]
  have hθ2 : θ ≤ π := by linarith [le_abs_self θ]
  have hδ'' : 0 < Real.sin (min δ (π / 2)) := Real.sin_pos_of_pos_of_lt_pi
    (lt_min hδ (by positivity)) (by linarith [min_le_right δ (π / 2), Real.pi_pos])
  have hGc : ContinuousOn (fun r : ℝ => (1 + (r : ℂ) * exp (θ * I)) ^ (-p)) (Ioi 0) :=
    fun r hr => (((by fun_prop : Continuous fun r : ℝ => 1 + (r : ℂ) * exp (θ * I)
      ).continuousAt).cpow continuousAt_const
      (one_add_ofReal_mul_exp_mem_slitPlane (le_of_lt hr) hθ)).continuousWithinAt
  have hint : IntegrableOn (fun r : ℝ => Real.exp (-1 * r) • (1 + (r : ℂ) * exp (θ * I)) ^ (-p))
      (Ioi 0) := by
    have hmaj := ((integrableOn_exp_neg_mul_mul_rpow_sub_one (s := k + 1) (by linarith)
      one_pos).const_mul (C * 2 ^ k)).add
      ((exp_neg_integrableOn_Ioi 0 one_pos).const_mul (C * 2 ^ k))
    refine hmaj.mono' (((by fun_prop : Continuous fun t : ℝ => Real.exp (-1 * t)
      ).continuousOn.smul hGc).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht : (0 : ℝ) < t := ht
    rw [norm_smul, Real.norm_eq_abs, Real.abs_exp, add_sub_cancel_right]
    have h1 := (hC t ht.le θ le_rfl).trans (mul_le_mul_of_nonneg_left
      (one_add_rpow_le ht.le hk0) hC0)
    calc Real.exp (-1 * t) * ‖(1 + (t : ℂ) * exp (θ * I)) ^ (-p)‖
        ≤ Real.exp (-1 * t) * (C * (2 ^ k * t ^ k + 2 ^ k)) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = _ := by simp only [Pi.add_apply]; ring
  have hF : ∀ N : ℕ, (fun r : ℝ => (1 + (r : ℂ) * exp (θ * I)) ^ (-p) -
      ∑ n ∈ Finset.range N, (((r : ℂ) * exp (θ * I)) ^ ((n : ℂ) + 1 - 1)) • Ring.choose (-p) n)
      =O[𝓝[>] 0] fun r => r ^ ((N : ℝ) + (1 : ℂ).re - 1) := by
    intro N
    refine (one_add_mul_cpow_sub_sum_isBigO (exp (θ * I)) (-p) N).congr' ?_ ?_
    · filter_upwards with r
      simp only [add_sub_cancel_right, cpow_natCast, smul_eq_mul, mul_comm (Ring.choose _ _)]
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simp only [one_re, add_sub_cancel_right, Real.rpow_natCast]
  have hW := (hasAsymptoticExpansion_integral_cexp_smul_rotate (F := fun t : ℂ => (1 + t) ^ (-p))
    (a := fun n => Ring.choose (-p) n) (μ := 1) (c := 1) hθ1 hθ2 (by norm_num) hδ'' hint
    hF).comp_tendsto (tendsto_cexp_mul_logStripAtTop θ hδ)
  have h3 := hW.mul_left (fun w : ℂ => cexp (-cexp w))
  refine ((h3.smul_scale (κ := fun n => exp (θ * I * (-((n : ℂ) + 1))))
    (ψ := fun (n : ℕ) (w : ℂ) => exp (-exp w - (n + 1 : ℂ) * w))
    fun n => Eventually.of_forall fun w => ?_).congr' ?_).congr_coeff ?_
  · simp only
    rw [show -((n : ℂ) + 1) = -((n + 1 : ℕ) : ℂ) by push_cast; ring, cpow_neg, cpow_natCast,
      mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_neg,
      ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · rw [logStripAtTop]
    refine (eventually_inf_principal.mpr (Eventually.of_forall fun w hw => ?_))
    have hw : |w.im + θ| ≤ π / 2 - δ := hw
    simp only [Function.comp_apply, smul_eq_mul]
    rw [genExpIntEOnLog_eq_integral_rotate p hθ (by linarith)]
  · funext n
    have hG : Gamma ((n : ℂ) + 1) = n.factorial := Complex.Gamma_nat_eq_factorial n
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    simp only [smul_eq_mul, hG, ring_choose_neg_eq_pochhammer, mul_neg, Complex.exp_neg]
    field_simp

/-- Three strips `|im w + θ| ≤ π/2 - d/4`, `θ ∈ {π - d/2, 0, -(π - d/2)}`, cover the closed
logarithmic sector `|im w| ≤ 3π/2 - δ`, where `d = min δ 1`. -/
theorem logSector_le_sup_logStripAtTop {δ : ℝ} (hδ : 0 < δ) :
    logSector (3 * π / 2 - δ) ≤
      logStripAtTop (π - min δ 1 / 2) (min δ 1 / 4) ⊔ logStripAtTop 0 (min δ 1 / 4) ⊔
        logStripAtTop (-(π - min δ 1 / 2)) (min δ 1 / 4) := by
  set d := min δ 1 with hd
  have hdδ : d ≤ δ := min_le_left _ _
  have hd0 : 0 < d := lt_min hδ one_pos
  set A : Set ℂ := {w : ℂ | |w.im| ≤ 3 * π / 2 - δ}
  have hsub : A ⊆ ({w : ℂ | |w.im + (π - d / 2)| ≤ π / 2 - d / 4} ∪
      {w : ℂ | |w.im + 0| ≤ π / 2 - d / 4}) ∪ {w : ℂ | |w.im + -(π - d / 2)| ≤ π / 2 - d / 4} := by
    intro w hw
    have hw : |w.im| ≤ 3 * π / 2 - δ := hw
    rw [abs_le] at hw
    by_cases h1 : w.im ≤ -(π / 2 - d / 4)
    · left; left
      show |w.im + (π - d / 2)| ≤ π / 2 - d / 4
      rw [abs_le]; constructor <;> linarith
    by_cases h2 : w.im ≤ π / 2 - d / 4
    · left; right
      show |w.im + 0| ≤ π / 2 - d / 4
      rw [add_zero, abs_le]; constructor <;> linarith
    · right
      show |w.im + -(π - d / 2)| ≤ π / 2 - d / 4
      rw [abs_le]; constructor <;> linarith
  rw [logSector]
  calc comap (fun w : ℂ => Real.exp w.re) atTop ⊓ 𝓟 A
      ≤ comap (fun w : ℂ => Real.exp w.re) atTop ⊓ 𝓟 (({w : ℂ | |w.im + (π - d / 2)| ≤
          π / 2 - d / 4} ∪ {w : ℂ | |w.im + 0| ≤ π / 2 - d / 4}) ∪
          {w : ℂ | |w.im + -(π - d / 2)| ≤ π / 2 - d / 4}) :=
        inf_le_inf_left _ (principal_mono.mpr hsub)
    _ = _ := by
        rw [← sup_principal, ← sup_principal, inf_sup_left, inf_sup_left]
        rfl

/-- Identity under the stated parameter and domain assumptions: `HasAsymptoticExpansion (logSector
(3*π/2-δ)) (fun k w => exp (-exp w-(k+1 : ℂ)*w)) (fun k => (-1 : ℂ)^k*pochhammer p k)
(genExpIntEOnLog p)`. -/
@[dlmf 8.20.E2]
theorem expIntegralE_log_sector_asymptotic (p : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 3*π/2) :
    HasAsymptoticExpansion (logSector (3*π/2-δ)) (fun k w => exp (-exp w-(k+1 : ℂ)*w))
        (fun k => (-1 : ℂ)^k*pochhammer p k) (genExpIntEOnLog p) := by
  have hd0 : 0 < min δ 1 / 4 := by have := lt_min hδ one_pos; positivity
  have hd1 : min δ 1 ≤ 1 := min_le_right _ _
  have hθ : |π - min δ 1 / 2| < π := by
    rw [abs_lt]; constructor <;> linarith [Real.pi_gt_three, lt_min hδ one_pos]
  have h1 := genExpIntEOnLog_strip_asymptotic p hθ hd0
  have h2 := genExpIntEOnLog_strip_asymptotic p (θ := 0) (by simpa using Real.pi_pos) hd0
  have h3 := genExpIntEOnLog_strip_asymptotic p (θ := -(π - min δ 1 / 2)) (by rwa [abs_neg]) hd0
  exact ((h1.sup h2).sup h3).mono (logSector_le_sup_logStripAtTop hδ)

/-- Crossing one sheet of the logarithmic covering: subtracting the connection term
`m·2πi/Γ(p)·exp(-m p π i + (p-1) w)` from `E_p` on the log-cover at `w` gives `E_p` at
`w - 2 m π i`, for `m = ±1`. -/
theorem genExpIntEOnLog_sub_connection (p w : ℂ) {m : ℤ} (hm : m = 1 ∨ m = -1) :
    genExpIntEOnLog p w - m*2*π*I/Gamma p*exp (-m*p*π*I+(p-1)*w) =
      genExpIntEOnLog p (w - 2*m*π*I) := by
  set w' := w - 2*m*π*I with hw'
  have hw : w = w' + 2*m*π*I := by rw [hw']; ring
  by_cases hp : ∀ n : ℤ, p ≠ n
  · have h := genExpIntEOnLog_monodromy hp w' m
    rw [← hw] at h
    have hs : Complex.sin (p*π) ≠ 0 := by
      rw [Complex.sin_ne_zero_iff]
      intro k hk
      exact hp k (by
        have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        exact mul_right_cancel₀ hπ hk)
    have hsin : Complex.sin (m*p*π) = m * Complex.sin (p*π) := by
      rcases hm with rfl | rfl
      · simp
      · push_cast; rw [show (-1:ℂ)*p*π = -(p*π) by ring, Complex.sin_neg]; ring
    have hexp : exp (m*p*π*I) * exp ((p-1)*w') = exp (-m*p*π*I+(p-1)*w) := by
      rw [← Complex.exp_add, hw]
      have := exp_add_two_pi_int_mul_I (-m*p*π*I+(p-1)*(w'+2*m*π*I)) m
      rw [← this]; congr 1; ring
    have hq : (m:ℂ) * Complex.sin (p*π) / Complex.sin (p*π) = m := by field_simp
    rw [h, hsin, mul_div_assoc (2*π*I*exp (m*p*π*I)/Gamma p), hq, ← hexp]
    ring
  · push Not at hp
    obtain ⟨n, rfl⟩ := hp
    rcases le_or_gt n 0 with hn | hn
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, n = -k := ⟨n.natAbs, by omega⟩
      subst hk
      have h := genExpIntEOnLog_nonpos_nat_monodromy k w' m
      rw [← hw] at h
      push_cast
      rw [Complex.Gamma_neg_nat_eq_zero, div_zero, zero_mul, sub_zero, h]
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k := ⟨n.natAbs, by omega⟩
      subst hk
      have hk1 : 1 ≤ k := by exact_mod_cast hn
      have h := genExpIntEOnLog_nat_monodromy hk1 w' m
      rw [← hw] at h
      push_cast
      have hG : Gamma (k : ℂ) = ((k-1).factorial : ℂ) := by
        obtain ⟨j, rfl⟩ : ∃ j, k = j+1 := ⟨k-1, by omega⟩
        rw [Nat.add_sub_cancel]; push_cast; exact Complex.Gamma_nat_eq_factorial j
      have hper : exp (((k:ℂ)-1)*w') = exp (((k:ℂ)-1)*w) := by
        rw [hw]
        have := exp_add_two_pi_int_mul_I (((k:ℂ)-1)*w') ((k-1:ℤ)*m)
        rw [← this]; congr 1; push_cast; ring
      have hsign : exp (-(m:ℂ)*k*π*I) = (-1:ℂ)^k := by
        rcases hm with rfl | rfl
        · push_cast
          rw [show -(1:ℂ)*k*π*I = k*(-(π*I)) by ring, Complex.exp_nat_mul,
            Complex.exp_neg_pi_mul_I]
        · push_cast
          rw [show -(-1:ℂ)*k*π*I = k*(π*I) by ring, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
      rw [Complex.exp_add, hsign, hG, h, hper]
      ring

/-- Estimate under the stated parameter and domain assumptions: `HasAsymptoticExpansion (comap
(fun w : ℂ => Real.exp w.re) atTop ⊓ 𝓟 {w : ℂ | π/2+δ ≤ ε*w.im ∧ ε*w.im ≤ 7*π/2-δ}) (fun k w
=> exp (-exp w-(k+1 : ℂ)*w)) (fun k => (-1 : ℂ)^k*pochhammer p k) (fun w => genExpIntEOnLog p
w-ε*2*π*I/Gamma p*exp (-ε*p*π*I+(p-1)*w))`. -/
@[dlmf 8.20.E3]
theorem expIntegralE_extended_sector_asymptotic (p : ℂ) {ε : ℝ} (hε : ε=1 ∨ ε = -1) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 3*π/2) :
    HasAsymptoticExpansion
        (comap (fun w : ℂ => Real.exp w.re) atTop ⊓ 𝓟 {w : ℂ | π/2+δ ≤ ε*w.im ∧ ε*w.im ≤ 7*π/2-δ})
        (fun k w => exp (-exp w-(k+1 : ℂ)*w)) (fun k => (-1 : ℂ)^k*pochhammer p k)
        (fun w => genExpIntEOnLog p w-ε*2*π*I/Gamma p*exp (-ε*p*π*I+(p-1)*w)) := by
  obtain ⟨m, hm, hεm⟩ : ∃ m : ℤ, (m = 1 ∨ m = -1) ∧ ε = m := by
    rcases hε with rfl | rfl
    · exact ⟨1, Or.inl rfl, by norm_num⟩
    · exact ⟨-1, Or.inr rfl, by norm_num⟩
  subst hεm
  set F := comap (fun w : ℂ => Real.exp w.re) atTop ⊓
    𝓟 {w : ℂ | π/2+δ ≤ (m:ℝ)*w.im ∧ (m:ℝ)*w.im ≤ 7*π/2-δ}
  have hg : Tendsto (fun w : ℂ => w - 2*m*π*I) F (logSector (3*π/2-δ)) := by
    unfold logSector
    refine tendsto_inf.mpr ⟨?_, tendsto_principal.mpr ?_⟩
    · refine tendsto_comap_iff.mpr ?_
      have : (fun w : ℂ => Real.exp w.re) ∘ (fun w => w - 2*m*π*I) =
          fun w => Real.exp w.re := by
        funext w; simp
      rw [this]; exact tendsto_comap.mono_left inf_le_left
    · filter_upwards [mem_inf_of_right (mem_principal_self _)] with w hw
      have hw : π/2+δ ≤ (m:ℝ)*w.im ∧ (m:ℝ)*w.im ≤ 7*π/2-δ := hw
      show |(w - 2*m*π*I).im| ≤ 3*π/2-δ
      have him : (w - 2*m*π*I).im = w.im - 2*m*π := by simp
      rw [him, abs_le]
      rcases hm with rfl | rfl
      · norm_num at hw ⊢; constructor <;> linarith
      · norm_num at hw ⊢; constructor <;> linarith
  have h := (expIntegralE_log_sector_asymptotic p hδ hδ1).comp_tendsto hg
  have hφ : (fun (k : ℕ) (w : ℂ) => exp (-exp (w - 2*m*π*I)-(k+1 : ℂ)*(w - 2*m*π*I))) =
      fun (k : ℕ) (w : ℂ) => exp (-exp w-(k+1 : ℂ)*w) := by
    funext k w
    have h1 : exp (w - 2*m*π*I) = exp w := by
      have := exp_add_two_pi_int_mul_I (w - 2*m*π*I) m
      rw [← this]; congr 1; ring
    rw [h1]
    have := exp_add_two_pi_int_mul_I (-exp w-(k+1 : ℂ)*(w - 2*m*π*I)) (-((k:ℤ)+1)*m)
    rw [← this]; congr 1; push_cast; ring
  have hf : genExpIntEOnLog p ∘ (fun w : ℂ => w - 2*m*π*I) =
      fun w => genExpIntEOnLog p w-((m:ℝ):ℂ)*2*π*I/Gamma p*exp (-((m:ℝ):ℂ)*p*π*I+(p-1)*w) := by
    funext w
    simp only [Function.comp, Complex.ofReal_intCast]
    exact (genExpIntEOnLog_sub_connection p w hm).symm
  rw [hφ, hf] at h
  exact h

/-- Large-order polynomials A_k(λ), including A₀=1. -/
@[dlmf 8.20.E4]
def expIntLargeOrderPolynomial : ℕ → Polynomial ℂ
  | 0 => 1
  | k+1 => (1-Polynomial.C (2*(k : ℂ))*Polynomial.X)*expIntLargeOrderPolynomial k+
      Polynomial.X*(Polynomial.X+1)*(expIntLargeOrderPolynomial k).derivative

/-- Identity under the stated parameter and domain assumptions: `expIntLargeOrderPolynomial 1=1 ∧
expIntLargeOrderPolynomial 2=1-2*Polynomial.X ∧ expIntLargeOrderPolynomial
3=1-8*Polynomial.X+6*Polynomial.X^2`. -/
@[dlmf 8.20.E5]
theorem expIntLargeOrderPolynomial_initial  :
    expIntLargeOrderPolynomial 1=1 ∧ expIntLargeOrderPolynomial 2=1-2*Polynomial.X ∧
        expIntLargeOrderPolynomial 3=1-8*Polynomial.X+6*Polynomial.X^2 := by
  norm_num [expIntLargeOrderPolynomial, Polynomial.derivative_mul, Polynomial.derivative_X,
      Polynomial.C_ofNat]
  ring

open Polynomial in
/-- Degree bound and leading coefficient of `A_{m+1}`. -/
theorem expIntLargeOrderPolynomial_succ_degree_coeff (m : ℕ) :
    (expIntLargeOrderPolynomial (m+1)).natDegree ≤ m ∧
      (expIntLargeOrderPolynomial (m+1)).coeff m = (-1 : ℂ)^m*(m+1).factorial := by
  induction m with
  | zero =>
    simp [expIntLargeOrderPolynomial]
  | succ m ih =>
    obtain ⟨hd, hc⟩ := ih
    set A := expIntLargeOrderPolynomial (m+1) with hA
    have hrec : expIntLargeOrderPolynomial (m+1+1) =
        (1-C (2*((m+1:ℕ) : ℂ))*X)*A + X*(X+1)*A.derivative := rfl
    have hAd : A.derivative.natDegree ≤ m - 1 := by
      have := natDegree_derivative_le A; omega
    have hA1 : A.coeff (m+1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hrec]
    constructor
    · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine (natDegree_mul_le).trans ?_
        have : (1-C (2*((m+1:ℕ) : ℂ))*X).natDegree ≤ 1 := by
          refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
          exact (natDegree_C_mul_le _ _).trans (by simp)
        omega
      · rcases Nat.eq_zero_or_pos m with h0 | h0
        · subst h0
          rw [derivative_of_natDegree_zero (by omega)]
          simp
        · refine (natDegree_mul_le).trans ?_
          have : (X*(X+1) : ℂ[X]).natDegree ≤ 2 := by
            refine (natDegree_mul_le).trans ?_
            have : (X+1 : ℂ[X]).natDegree ≤ 1 := (natDegree_add_le _ _).trans (by simp)
            have : (X : ℂ[X]).natDegree ≤ 1 := by simp
            omega
          omega
    · have he : (1-C (2*((m+1:ℕ) : ℂ))*X)*A + X*(X+1)*A.derivative =
          A - C (2*((m+1:ℕ) : ℂ))*(X*A) + X*(X*A.derivative) + X*A.derivative := by ring
      rw [he, coeff_add, coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul, coeff_X_mul,
        coeff_X_mul, coeff_derivative, hA1, hc]
      have hmid : (X*A.derivative).coeff m = (m : ℂ)*((-1 : ℂ)^m*(m+1).factorial) := by
        rcases m with _ | k
        · simp
        · rw [coeff_X_mul, coeff_derivative, hc]; push_cast; ring
      rw [hmid, Nat.factorial_succ (m+1)]
      push_cast
      ring

/-- The degree statement in the prose of DLMF §8.20(ii). -/
theorem expIntLargeOrderPolynomial_degree {k : ℕ} (hk : 1 ≤ k) :
    (expIntLargeOrderPolynomial k).natDegree=k-1 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k-1, by omega⟩
  obtain ⟨hd, hc⟩ := expIntLargeOrderPolynomial_succ_degree_coeff m
  rw [Nat.add_sub_cancel]
  refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hd ?_
  rw [hc]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

namespace ExpIntLargeOrder

/-- The functions `g_k(t) = A_k(λt)/(1+λt)^{2k}` of the repeated integration by parts in the
large-order expansion of `E_p(λp)`. -/
private noncomputable def coeffFn (l : ℝ) (k : ℕ) (t : ℝ) : ℂ :=
  (expIntLargeOrderPolynomial k).eval ((l : ℂ) * t) / (1 + (l : ℂ) * t) ^ (2 * k)

/-- The recurrence of DLMF 8.20.4 evaluated at a point. -/
private theorem eval_succ (k : ℕ) (x : ℂ) : (expIntLargeOrderPolynomial (k+1)).eval x =
    (1 - 2 * k * x) * (expIntLargeOrderPolynomial k).eval x +
      x * (x + 1) * (expIntLargeOrderPolynomial k).derivative.eval x := by
  simp [expIntLargeOrderPolynomial]

/-- `g_{k+1} = (t g_k/(1+λt))'`. -/
private theorem hasDerivAt_coeffFn {l : ℝ} (hl : 0 ≤ l) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => (t : ℂ) / (1 + (l : ℂ) * t) * coeffFn l k t) (coeffFn l (k+1) t)
      t := by
  set P := expIntLargeOrderPolynomial k
  have hne : (1 + (l : ℂ) * t) ≠ 0 := by
    have : (0 : ℝ) < 1 + l * t := by positivity
    exact_mod_cast this.ne'
  have hlin : HasDerivAt (fun t : ℝ => (l : ℂ) * t) (l : ℂ) t := by
    simpa using ((hasDerivAt_id (t : ℂ)).const_mul (l : ℂ)).comp_ofReal
  have hP : HasDerivAt (fun t : ℝ => P.eval ((l : ℂ) * t))
      (P.derivative.eval ((l : ℂ) * t) * l) t :=
    (P.hasDerivAt _).comp t hlin
  have hD : HasDerivAt (fun t : ℝ => 1 + (l : ℂ) * t) (l : ℂ) t := by
    simpa using hlin.const_add 1
  have hT : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := by
    simpa using (hasDerivAt_id (t : ℂ)).comp_ofReal
  have h := (hT.mul hP).div (hD.pow (2 * k + 1)) (pow_ne_zero _ hne)
  have heq : (fun t : ℝ => (t : ℂ) / (1 + (l : ℂ) * t) * coeffFn l k t) =
      fun t : ℝ => (t : ℂ) * P.eval ((l : ℂ) * t) / (1 + (l : ℂ) * t) ^ (2 * k + 1) := by
    funext s
    simp only [coeffFn, P]
    rw [pow_succ]
    by_cases hs : (1 + (l : ℂ) * s) = 0
    · simp [hs]
    · field_simp
  rw [heq]
  convert h using 1
  simp only [coeffFn, eval_succ, P, Pi.pow_apply, Pi.mul_apply]
  rw [show 2 * k + 1 - 1 = 2 * k by omega, pow_succ]
  field_simp
  push_cast
  ring

/-- `deg A_k ≤ k`. -/
private theorem natDegree_le (k : ℕ) : (expIntLargeOrderPolynomial k).natDegree ≤ k := by
  rcases k with _ | m
  · simp [expIntLargeOrderPolynomial]
  · exact (expIntLargeOrderPolynomial_succ_degree_coeff m).1.trans (Nat.le_succ m)

/-- A bound for `|g_k|` on `t ≥ 0`, uniform in `λ ≥ 0`. -/
private noncomputable def coeffBound (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), ‖(expIntLargeOrderPolynomial k).coeff i‖

/-- `|g_k(t)|` is bounded uniformly in `λ ≥ 0` and `t ≥ 0`. -/
private theorem norm_coeffFn_le {l : ℝ} (hl : 0 ≤ l) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖coeffFn l k t‖ ≤ coeffBound k := by
  set P := expIntLargeOrderPolynomial k
  set s : ℝ := l * t with hs
  have hs0 : 0 ≤ s := mul_nonneg hl ht
  have hx : (l : ℂ) * t = (s : ℂ) := by rw [hs]; push_cast; ring
  have h1 : (1 + (s : ℂ)) = ((1 + s : ℝ) : ℂ) := by push_cast; ring
  have hev : ‖P.eval (s : ℂ)‖ ≤ coeffBound k * (1 + s) ^ k := by
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (natDegree_le k)), coeffBound,
      Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hs0]
    gcongr
    calc s ^ i ≤ (1 + s) ^ i := by gcongr; linarith
      _ ≤ (1 + s) ^ k := pow_le_pow_right₀ (by linarith) (by
          simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi)
  have hpos : (0 : ℝ) < 1 + s := by linarith
  rw [coeffFn, hx, h1, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hpos.le,
    div_le_iff₀ (by positivity)]
  have hS : 0 ≤ coeffBound k := Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc ‖P.eval (s : ℂ)‖ ≤ coeffBound k * (1 + s) ^ k := hev
    _ ≤ coeffBound k * (1 + s) ^ (2 * k) := by
        gcongr
        · linarith
        · omega

/-- The Laplace kernel `e^{-λp(t-1)} t^{-p}` of `e^{λp} E_p(λp)`. -/
private noncomputable def laplaceKernel (p l t : ℝ) : ℂ :=
  ((Real.exp (-(l * p * (t - 1))) * t ^ (-p) : ℝ) : ℂ)

/-- The kernel is dominated by `t^{-p}` on `t ≥ 1`. -/
private theorem norm_laplaceKernel_le {p l : ℝ} (hp : 0 ≤ p) (hl : 0 ≤ l) {t : ℝ} (ht : 1 ≤ t) :
    ‖laplaceKernel p l t‖ ≤ t ^ (-p) := by
  rw [laplaceKernel, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have : Real.exp (-(l * p * (t - 1))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by
      have := mul_nonneg (mul_nonneg hl hp) (by linarith : 0 ≤ t - 1); linarith)
  calc _ ≤ 1 * t ^ (-p) := by gcongr
    _ = _ := one_mul _

/-- The derivative of the kernel, `-p (1+λt)/t` times the kernel. -/
private theorem hasDerivAt_laplaceKernel (p l : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (laplaceKernel p l) (-(p : ℂ) * ((1 + (l : ℂ) * t) / t) * laplaceKernel p l t)
      t := by
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (-(l * p * (t - 1)))) 
      (Real.exp (-(l * p * (t - 1))) * (-(l * p))) t := by
    have := ((((hasDerivAt_id t).sub_const 1).const_mul (l * p)).neg).exp
    simpa using this
  have h2 := Real.hasDerivAt_rpow_const (p := -p) (x := t) (Or.inl ht.ne')
  have h := (h1.mul h2).ofReal_comp
  unfold laplaceKernel
  convert h using 1
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  rw [Real.rpow_sub_one ht.ne']
  push_cast
  field_simp
  ring

/-- `g_k` is continuous on `t ≥ 0`. -/
private theorem continuousOn_coeffFn {l : ℝ} (hl : 0 ≤ l) (k : ℕ) :
    ContinuousOn (coeffFn l k) (Ici 0) := by
  intro t ht
  have hne : (1 + (l : ℂ) * t) ≠ 0 := by
    have : (0 : ℝ) < 1 + l * t := by have := mul_nonneg hl (show (0:ℝ) ≤ t from ht); linarith
    exact_mod_cast this.ne'
  refine ContinuousAt.continuousWithinAt ?_
  unfold coeffFn
  refine ContinuousAt.div ?_ ?_ (pow_ne_zero _ hne)
  · exact ((Polynomial.continuous _).comp (by fun_prop)).continuousAt
  · fun_prop

/-- The kernel is continuous on `t > 0`. -/
private theorem continuousOn_laplaceKernel (p l : ℝ) :
    ContinuousOn (laplaceKernel p l) (Ioi 0) := by
  intro t ht
  have ht : (0 : ℝ) < t := ht
  exact (hasDerivAt_laplaceKernel p l ht).continuousAt.continuousWithinAt

/-- The integrands `e^{-λp(t-1)} t^{-p} g_k(t)` are integrable on `(1, ∞)`. -/
private theorem integrableOn_laplaceKernel_mul {p l : ℝ} (hp : 1 < p) (hl : 0 ≤ l) (k : ℕ) :
    IntegrableOn (fun t => laplaceKernel p l t * coeffFn l k t) (Ioi 1) := by
  have hint : IntegrableOn (fun t : ℝ => coeffBound k * t ^ (-p)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
  refine hint.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact ((continuousOn_laplaceKernel p l).mono (Ioi_subset_Ioi zero_le_one)).mul
      ((continuousOn_coeffFn hl k).mono (fun t (ht : (1 : ℝ) < t) => show (0 : ℝ) ≤ t by linarith))
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht : (1 : ℝ) < t := ht
    rw [norm_mul, mul_comm]
    exact mul_le_mul (norm_coeffFn_le hl k (by linarith))
      (norm_laplaceKernel_le (by linarith) hl ht.le)
      (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)

/-- The integrals `I_k = ∫₁^∞ e^{-λp(t-1)} t^{-p} g_k(t) dt`. -/
private noncomputable def kernelIntegral (p l : ℝ) (k : ℕ) : ℂ :=
  ∫ t in Ioi 1, laplaceKernel p l t * coeffFn l k t

/-- Integration by parts: `p I_k = g_k(1)/(1+λ) + I_{k+1}`. -/
private theorem kernelIntegral_succ {p l : ℝ} (hp : 1 < p) (hl : 0 ≤ l) (k : ℕ) :
    (p : ℂ) * kernelIntegral p l k = coeffFn l k 1 / (1 + l) + kernelIntegral p l (k + 1) := by
  set F : ℝ → ℂ := fun t => laplaceKernel p l t * ((t : ℂ) / (1 + (l : ℂ) * t) * coeffFn l k t)
  have hderiv : ∀ t ∈ Ioi (1 : ℝ), HasDerivAt F
      (-(p : ℂ) * (laplaceKernel p l t * coeffFn l k t) +
        laplaceKernel p l t * coeffFn l (k + 1) t) t := by
    intro t ht
    have ht : (1 : ℝ) < t := ht
    have ht0 : (0 : ℝ) < t := by linarith
    have h := (hasDerivAt_laplaceKernel p l ht0).mul (hasDerivAt_coeffFn hl k ht0)
    convert h using 1
    have hne : (1 + (l : ℂ) * t) ≠ 0 := by
      have : (0 : ℝ) < 1 + l * t := by have := mul_nonneg hl ht0.le; linarith
      exact_mod_cast this.ne'
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    field_simp
  have hint := ((integrableOn_laplaceKernel_mul hp hl k).const_mul (-(p : ℂ))).add
    (integrableOn_laplaceKernel_mul hp hl (k + 1))
  have hlim : Tendsto F atTop (𝓝 0) := by
    have ht : Tendsto (fun t : ℝ => coeffBound k * t ^ (-(p - 1))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by linarith : 0 < p - 1)).const_mul (coeffBound k)
    refine squeeze_zero_norm' ?_ ht
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have ht0 : (0 : ℝ) < t := by linarith
    have hden : 1 ≤ ‖(1 + (l : ℂ) * t)‖ := by
      have : (1 + (l : ℂ) * t) = ((1 + l * t : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have := mul_nonneg hl ht0.le; linarith
    simp only [F, norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg ht0.le]
    have h1 := norm_laplaceKernel_le (p := p) (by linarith) hl ht.le
    have h2 := norm_coeffFn_le hl k ht0.le
    have h3 : t / ‖(1 + (l : ℂ) * t)‖ ≤ t := div_le_self ht0.le hden
    calc ‖laplaceKernel p l t‖ * (t / ‖(1 + (l : ℂ) * t)‖ * ‖coeffFn l k t‖)
        ≤ t ^ (-p) * (t * coeffBound k) := by gcongr
      _ = coeffBound k * t ^ (-(p - 1)) := by
        rw [show -(p - 1) = -p + 1 by ring, Real.rpow_add ht0, Real.rpow_one]; ring
  have hcont : ContinuousWithinAt F (Ici 1) 1 := by
    have h := (hasDerivAt_laplaceKernel p l one_pos).mul (hasDerivAt_coeffFn hl k one_pos)
    exact h.continuousAt.continuousWithinAt
  have hF := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  rw [integral_add ((integrableOn_laplaceKernel_mul hp hl k).const_mul _)
      (integrableOn_laplaceKernel_mul hp hl (k + 1)),
    integral_const_mul] at hF
  have hF1 : F 1 = coeffFn l k 1 / (1 + l) := by
    simp [F, laplaceKernel, div_eq_inv_mul]
  rw [hF1] at hF
  unfold kernelIntegral
  linear_combination -hF

/-- The expansion with exact remainder after `N` integrations by parts. -/
private theorem kernelIntegral_expand {p l : ℝ} (hp : 1 < p) (hl : 0 ≤ l) (N : ℕ) :
    (1 + (l : ℂ)) * p * kernelIntegral p l 0 = ∑ k ∈ Finset.range N, coeffFn l k 1 / (p : ℂ) ^ k +
      (1 + (l : ℂ)) * p * kernelIntegral p l N / (p : ℂ) ^ N := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0 : ℝ) < p).ne'
  have hl1 : (1 + (l : ℂ)) ≠ 0 := by
    have : (0 : ℝ) < 1 + l := by linarith
    exact_mod_cast this.ne'
  induction N with
  | zero => simp
  | succ N ih =>
    rw [ih, Finset.sum_range_succ, add_assoc]
    congr 1
    rw [mul_assoc, kernelIntegral_succ hp hl N]
    field_simp
    ring

/-- `g_0 = 1`. -/
private theorem coeffFn_zero (l : ℝ) (t : ℝ) : coeffFn l 0 t = 1 := by
  simp [coeffFn, expIntLargeOrderPolynomial]

/-- `g_1(t) = 1/(1+λt)²`. -/
private theorem coeffFn_one (l : ℝ) (t : ℝ) : coeffFn l 1 t = 1 / (1 + (l : ℂ) * t) ^ 2 := by
  simp [coeffFn, expIntLargeOrderPolynomial_initial.1]

/-- The real kernel is integrable on `(1, ∞)`. -/
private theorem integrableOn_realKernel {p l : ℝ} (hp : 1 < p) (hl : 0 ≤ l) :
    IntegrableOn (fun t : ℝ => Real.exp (-(l * p * (t - 1))) * t ^ (-p)) (Ioi 1) := by
  refine (integrableOn_Ioi_rpow_of_lt (by linarith : -p < -1) one_pos).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun t (ht : (1 : ℝ) < t) => ?_) measurableSet_Ioi
    exact ((by fun_prop : Continuous fun t : ℝ => Real.exp (-(l * p * (t - 1)))).continuousAt.mul
      (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith)))).continuousWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht : (1 : ℝ) < t := ht
    have h := norm_laplaceKernel_le (p := p) (by linarith) hl ht.le
    rwa [laplaceKernel, Complex.norm_real] at h

/-- `I_0` is the integral of the real kernel. -/
private theorem kernelIntegral_zero_eq {p l : ℝ} : kernelIntegral p l 0 =
    ((∫ t in Ioi (1 : ℝ), Real.exp (-(l * p * (t - 1))) * t ^ (-p) : ℝ) : ℂ) := by
  rw [kernelIntegral, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp [laplaceKernel, coeffFn_zero]

/-- `(1+λ) I_0 ≤ 1/(p-1)`. -/
private theorem realKernel_integral_le {p l : ℝ} (hp : 1 < p) (hl : 0 ≤ l) :
    (1 + l) * (∫ t in Ioi (1 : ℝ), Real.exp (-(l * p * (t - 1))) * t ^ (-p)) ≤ 1 / (p - 1) := by
  set J := ∫ t in Ioi (1 : ℝ), Real.exp (-(l * p * (t - 1))) * t ^ (-p)
  have hJ0 : 0 ≤ J := setIntegral_nonneg measurableSet_Ioi fun t ht => by
    have : (0 : ℝ) < t := lt_trans one_pos ht
    positivity
  have hl1 : (0 : ℝ) < 1 + l := by linarith
  -- bound on I_1
  have hI1 : ‖kernelIntegral p l 1‖ ≤ J / (1 + l) ^ 2 := by
    rw [kernelIntegral, div_eq_mul_inv, mul_comm, ← integral_const_mul]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine setIntegral_mono_on (integrableOn_laplaceKernel_mul hp hl 1).norm ?_ measurableSet_Ioi
      fun t ht => ?_
    · exact (integrableOn_realKernel hp hl).const_mul _
    · have ht : (1 : ℝ) < t := ht
      have ht0 : (0 : ℝ) < t := by linarith
      rw [norm_mul, laplaceKernel, Complex.norm_real, Real.norm_of_nonneg (by positivity),
        coeffFn_one,
        mul_comm ((1 + l) ^ 2)⁻¹]
      gcongr
      have : (1 + (l : ℂ) * t) = ((1 + l * t : ℝ) : ℂ) := by push_cast; ring
      rw [this, norm_div, norm_one, norm_pow, Complex.norm_real,
        Real.norm_of_nonneg (by positivity), one_div]
      gcongr
      nlinarith
  have hid := kernelIntegral_succ hp hl 0
  rw [kernelIntegral_zero_eq, coeffFn_zero] at hid
  have hnorm := congrArg norm hid
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hJ0,
    Real.norm_of_nonneg (by linarith)] at hnorm
  have htri : p * J ≤ 1 / (1 + l) + J / (1 + l) ^ 2 := by
    rw [hnorm]
    refine (norm_add_le _ _).trans ?_
    gcongr
    · have : (1 : ℂ) / (1 + (l : ℂ)) = ((1 / (1 + l) : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [le_div_iff₀ (by linarith)]
  have h2 : J / (1 + l) ^ 2 ≤ J := div_le_self hJ0 (by nlinarith)
  have h3 : p * J * (1 + l) ≤ 1 + J * (1 + l) := by
    have := mul_le_mul_of_nonneg_right htri hl1.le
    calc p * J * (1 + l) ≤ (1 / (1 + l) + J / (1 + l) ^ 2) * (1 + l) := this
      _ = 1 + J / (1 + l) := by field_simp
      _ ≤ 1 + J * (1 + l) := by
        gcongr
        exact div_le_self hJ0 (by linarith) |>.trans (le_mul_of_one_le_right hJ0 (by linarith))
  nlinarith

/-- `e^{λp} E_p(λp) = I_0`, with `E_p(0) = 1/(p-1)`. -/
private theorem exp_mul_genExpIntEExtended_eq {p l : ℝ} (hp : 1 < p) (hl : 0 ≤ l) :
    exp ((p : ℂ) * l) * genExpIntEExtended p (l * p) = kernelIntegral p l 0 := by
  rw [kernelIntegral_zero_eq]
  rcases hl.eq_or_lt with h0 | hpos
  · subst h0
    simp only [ofReal_zero, zero_mul, mul_zero, Complex.exp_zero, one_mul, genExpIntEExtended,
      ite_true, neg_zero, Real.exp_zero]
    rw [integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow]
    have : (1 : ℂ) - p ≠ 0 := by
      have : (1:ℝ) - p ≠ 0 := by linarith
      exact_mod_cast this
    have : (p : ℂ) - 1 ≠ 0 := by
      have : (0:ℝ) < p - 1 := by linarith
      exact_mod_cast this.ne'
    push_cast
    field_simp
    ring_nf
    rw [show -((p : ℂ) * (1 - (p : ℂ))⁻¹) + (1 - (p : ℂ))⁻¹ = (1 - (p : ℂ)) * (1 - (p : ℂ))⁻¹ by
      ring, mul_inv_cancel₀ (by assumption)]
  · have hz : ((l : ℂ) * p) ≠ 0 := by
      have : (0 : ℝ) < l * p := by nlinarith
      exact_mod_cast this.ne'
    have hre : 0 < ((l : ℂ) * p).re := by
      rw [← ofReal_mul, ofReal_re]; nlinarith
    simp only [genExpIntEExtended, hz, ↓reduceIte]
    rw [expIntegralE_laplace_complex _ hre, ← integral_const_mul,
      ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) ≤ t := le_of_lt (lt_trans one_pos ht)
    rw [ofReal_mul, ofReal_exp, ofReal_cpow ht0, ← mul_assoc, ← Complex.exp_add]
    push_cast
    congr 2
    ring

/-- `|I_N| ≤ S_N I_0`. -/
private theorem norm_kernelIntegral_le {p l : ℝ} (hp : 1 < p) (hl : 0 ≤ l) (N : ℕ) :
    ‖kernelIntegral p l N‖ ≤
      coeffBound N * ∫ t in Ioi (1 : ℝ), Real.exp (-(l * p * (t - 1))) * t ^ (-p) := by
  rw [kernelIntegral, ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((integrableOn_realKernel hp hl).const_mul _) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht : (1 : ℝ) < t := ht
  have ht0 : (0 : ℝ) < t := by linarith
  rw [norm_mul, laplaceKernel, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_coeffFn_le hl N ht0.le) (by positivity)

end ExpIntLargeOrder

open ExpIntLargeOrder in
/-- Estimate under the stated parameter and domain assumptions: `IsBigO (comap Prod.fst atTop ⊓ 𝓟
{p : ℝ × ℝ | 1 < p.1 ∧ 0 ≤ p.2}) (fun p => exp (p.1*p.2 : ℂ)*(p.2+1)*p.1*genExpIntEExtended
p.1 (p.2*p.1)-∑ k ∈ Finset.range N, (expIntLargeOrderPolynomial k).eval (p.2 : ℂ)/(((p.2+1 :
ℂ)^(2*k))*(p.1 : ℂ)^k)) (fun p => p.1^(-(N : ℤ)))`. -/
@[dlmf 8.20.E6]
theorem expIntegralE_large_order_uniform (N : ℕ) :
    IsBigO (comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 1 < p.1 ∧ 0 ≤ p.2})
        (fun p => exp (p.1*p.2 : ℂ)*(p.2+1)*p.1*genExpIntEExtended p.1 (p.2*p.1)-∑ k ∈
        Finset.range N, (expIntLargeOrderPolynomial k).eval
        (p.2 : ℂ)/(((p.2+1 : ℂ)^(2*k))*(p.1 : ℂ)^k)) (fun p => p.1^(-(N : ℤ))) := by
  have h2 : ∀ᶠ q : ℝ × ℝ in comap Prod.fst atTop, 2 ≤ q.1 :=
    tendsto_comap.eventually (eventually_ge_atTop 2)
  refine IsBigO.of_bound (2 * coeffBound N) ?_
  filter_upwards [h2.filter_mono inf_le_left,
    (eventually_principal.mpr fun q hq => hq).filter_mono inf_le_right] with q hq2 hqS
  obtain ⟨P, L⟩ := q
  obtain ⟨hP1, hL⟩ := hqS
  simp only at hq2 hP1 hL ⊢
  have hP0 : (0 : ℝ) < P := by linarith
  have hPc : (P : ℂ) ≠ 0 := by exact_mod_cast hP0.ne'
  have hE := exp_mul_genExpIntEExtended_eq hP1 hL
  have hexp := kernelIntegral_expand hP1 hL N
  have hsum : ∑ k ∈ Finset.range N, (expIntLargeOrderPolynomial k).eval (L : ℂ) /
      (((L + 1 : ℂ) ^ (2 * k)) * (P : ℂ) ^ k) =
        ∑ k ∈ Finset.range N, coeffFn L k 1 / (P : ℂ) ^ k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [coeffFn, ofReal_one, mul_one]
    rw [add_comm (1 : ℂ), div_div]
  have hlhs : exp ((P : ℂ) * L) * (L + 1) * P * genExpIntEExtended P (L * P) =
      (1 + (L : ℂ)) * P * kernelIntegral P L 0 := by
    rw [← hE]; ring
  rw [hsum, hlhs, hexp, add_sub_cancel_left]
  have hJ := realKernel_integral_le hP1 hL
  have hI := norm_kernelIntegral_le hP1 hL N
  set J := ∫ t in Ioi (1 : ℝ), Real.exp (-(L * P * (t - 1))) * t ^ (-P)
  have hS : 0 ≤ coeffBound N := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hn1 : ‖(1 + (L : ℂ))‖ = 1 + L := by
    rw [show (1 + (L : ℂ)) = ((1 + L : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  rw [norm_div, norm_mul, norm_mul, hn1, norm_pow, Complex.norm_real, Real.norm_of_nonneg hP0.le,
    Real.norm_of_nonneg (by positivity), zpow_neg, zpow_natCast]
  have hPN : 0 < P ^ N := by positivity
  rw [div_le_iff₀ hPN, mul_assoc (2 * coeffBound N), inv_mul_cancel₀ hPN.ne', mul_one]
  calc (1 + L) * P * ‖kernelIntegral P L N‖ ≤ (1 + L) * P * (coeffBound N * J) := by gcongr
    _ = P * coeffBound N * ((1 + L) * J) := by ring
    _ ≤ P * coeffBound N * (1 / (P - 1)) := by gcongr
    _ ≤ 2 * coeffBound N := by
        rw [mul_one_div, div_le_iff₀ (by linarith)]
        nlinarith

end DLMF.Confluent
