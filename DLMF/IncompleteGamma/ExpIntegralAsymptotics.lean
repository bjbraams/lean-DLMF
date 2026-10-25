/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.ExponentialIntegral
public import DLMF.Confluent.TricomiRotated
public import DLMFMathlib.Analysis.Asymptotics.WatsonRotated

/-!
# Generalized exponential integral asymptotics, DLMF §8.20

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat Interval
namespace DLMF.Confluent

/-- genExpIntE exact remainder. -/
@[dlmf 8.20.E1]
theorem genExpIntE_exact_remainder (p : ℂ) {z : ℂ} (hz : z ≠ 0) (N : ℕ) :
    genExpIntE p z=exp (-z)/z*(∑ k ∈ Finset.range N, (-1 : ℂ)^k*poch p k/z^k)+(-1 : ℂ)^N*poch p N/z^N*genExpIntE (N+p) z := by
  induction N with
  | zero => simp [poch]
  | succ N ih =>
    have h := genExpIntE_add_one ((N:ℂ)+p) hz
    rw [show (N:ℂ)+p+1 = ((N+1:ℕ):ℂ)+p by push_cast; ring] at h
    rw [ih, Finset.sum_range_succ, poch_succ, pow_succ, pow_succ]
    have hzN : z^N ≠ 0 := pow_ne_zero _ hz
    set S := ∑ k ∈ Finset.range N, (-1 : ℂ)^k*poch p k/z^k
    field_simp
    linear_combination (-1:ℂ)^N*poch p N*h

/-- Polynomial bound for `(1+t)^{-p}` on the sector `|arg t| ≤ |θ| < π`. -/
lemma exists_norm_one_add_cpow_neg_le (p : ℂ) {θ : ℝ} (hθ : |θ| < π) :
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
lemma genExpIntE_eq_exp_mul_integral {p z : ℂ} (hz : 0 < z.re) :
    genExpIntE p z = cexp (-z) * ∫ t : ℝ in Ioi 0, cexp (-(z * t)) * (1 + (t : ℂ)) ^ (-p) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  rw [genExpIntE_eq_exp_mul_kummerU p hz0, kummerU_laplace (by norm_num) hz]
  simp only [Gamma_one, div_one, one_mul, sub_self, cpow_zero, mul_one,
    show (2 - p : ℂ) - 1 - 1 = -p by ring, neg_mul]

/-- On the principal strip the logarithmic-plane `E_p` is the principal one. -/
lemma genExpIntEOnLog_eq_genExpIntE (p : ℂ) {w : ℂ} (h1 : -π < w.im) (h2 : w.im ≤ π) :
    genExpIntEOnLog p w = genExpIntE p (cexp w) := by
  rw [genExpIntEOnLog, genExpIntE, upperIncGammaOnLog_eq_upperIncGamma _ h1 h2,
    cpow_def_of_ne_zero (Complex.exp_ne_zero w), Complex.log_exp h1 h2, mul_comm w]

/-- `1 + r e^{iy}` lies in the slit plane for `r ≥ 0` and `|y| < π`. -/
lemma one_add_ofReal_mul_exp_mem_slitPlane {r y : ℝ} (hr : 0 ≤ r) (hy : |y| < π) :
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
lemma re_cexp_mul_exp (w : ℂ) (y : ℝ) :
    (cexp w * exp (y * I)).re = Real.exp w.re * Real.cos (w.im + y) := by
  rw [← Complex.exp_add, Complex.exp_re]
  simp

/-- `(1 + r)^k ≤ 2^k (r^k + 1)` for `r, k ≥ 0`. -/
lemma one_add_rpow_le {r k : ℝ} (hr : 0 ≤ r) (hk : 0 ≤ k) :
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
      (hasDerivAt_upperIncGammaOnLog (1 - p) v).differentiableAt
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
    rw [genExpIntEOnLog_eq_genExpIntE p (by linarith [neg_abs_le v.im, Real.pi_pos])
      (by linarith [le_abs_self v.im, Real.pi_pos]), genExpIntE_eq_exp_mul_integral hre]
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
lemma tendsto_cexp_mul_logStripAtTop (θ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
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
      (fun k => (-1 : ℂ)^k*poch p k) (genExpIntEOnLog p) := by
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
    simp only [smul_eq_mul, hG, ring_choose_neg_eq_poch, mul_neg, Complex.exp_neg]
    field_simp


/-- Three strips `|im w + θ| ≤ π/2 - d/4`, `θ ∈ {π - d/2, 0, -(π - d/2)}`, cover the closed
logarithmic sector `|im w| ≤ 3π/2 - δ`, where `d = min δ 1`. -/
lemma logSector_le_sup_logStripAtTop {δ : ℝ} (hδ : 0 < δ) :
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


/-- genExpIntE log sector asymptotic. -/
@[dlmf 8.20.E2]
theorem genExpIntE_log_sector_asymptotic (p : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 3*π/2) :
    HasAsymptoticExpansion (logSector (3*π/2-δ)) (fun k w => exp (-exp w-(k+1 : ℂ)*w)) (fun k => (-1 : ℂ)^k*poch p k) (genExpIntEOnLog p) := by
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
lemma genExpIntEOnLog_sub_connection (p w : ℂ) {m : ℤ} (hm : m = 1 ∨ m = -1) :
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

/-- genExpIntE extended sector asymptotic. -/
@[dlmf 8.20.E3]
theorem genExpIntE_extended_sector_asymptotic (p : ℂ) {ε : ℝ} (hε : ε=1 ∨ ε = -1) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 3*π/2) :
    HasAsymptoticExpansion (comap (fun w : ℂ => Real.exp w.re) atTop ⊓ 𝓟 {w : ℂ | π/2+δ ≤ ε*w.im ∧ ε*w.im ≤ 7*π/2-δ}) (fun k w => exp (-exp w-(k+1 : ℂ)*w)) (fun k => (-1 : ℂ)^k*poch p k) (fun w => genExpIntEOnLog p w-ε*2*π*I/Gamma p*exp (-ε*p*π*I+(p-1)*w)) := by
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
  have h := (genExpIntE_log_sector_asymptotic p hδ hδ1).comp_tendsto hg
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

/-- expIntLargeOrderPolynomial initial. -/
@[dlmf 8.20.E5]
theorem expIntLargeOrderPolynomial_initial  :
    expIntLargeOrderPolynomial 1=1 ∧ expIntLargeOrderPolynomial 2=1-2*Polynomial.X ∧ expIntLargeOrderPolynomial 3=1-8*Polynomial.X+6*Polynomial.X^2 := by
  norm_num [expIntLargeOrderPolynomial, Polynomial.derivative_mul, Polynomial.derivative_X, Polynomial.C_ofNat]
  ring

open Polynomial in
/-- Degree bound and leading coefficient of `A_{m+1}`. -/
lemma expIntLargeOrderPolynomial_succ_degree_coeff (m : ℕ) :
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

/-- genExpIntE large order uniform. -/
@[dlmf 8.20.E6]
theorem genExpIntE_large_order_uniform (N : ℕ) :
    IsBigO (comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 1 < p.1 ∧ 0 ≤ p.2}) (fun p => exp (p.1*p.2 : ℂ)*(p.2+1)*p.1*genExpIntEExtended p.1 (p.2*p.1)-∑ k ∈ Finset.range N, (expIntLargeOrderPolynomial k).eval (p.2 : ℂ)/(((p.2+1 : ℂ)^(2*k))*(p.1 : ℂ)^k)) (fun p => p.1^(-(N : ℤ))) := by
  sorry

end DLMF.Confluent
