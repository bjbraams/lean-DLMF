/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Integrals.Laplace

/-!
# Hankel kernels for confluent hypergeometric transforms

Bounds, continuity and Laplace transforms of the Hankel kernels used in the confluent integral
formulas.

Source references and common attribution are retained in
`DLMF.Confluent.Integrals`.
-/

@[expose] public section

open Complex Filter MeasureTheory FormalMultilinearSeries

open scoped Real Topology ENNReal

open DLMF.Hypergeometric

open DLMF.Bessel

noncomputable section

namespace DLMF.Confluent

section HankelKernel

/-! ### Hankel-kernel bounds and Laplace transform (used for 13.10.15, 13.23.11) -/

open Set Asymptotics

/-- `t^r e^{-st}` is integrable on `(0,∞)` for `r > -1`, `s > 0`. -/
theorem cfInt_integrableOn_rpow_exp {r s : ℝ} (hr : -1 < r) (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => t ^ r * Real.exp (-(s * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := r) (b := s) hr one_pos hs
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp [Real.rpow_one, neg_mul]

/-- `∫₀^∞ t^r e^{-st} dt = Γ(r+1) s^{-(r+1)}`. -/
theorem cfInt_integral_rpow_exp {r s : ℝ} (hr : -1 < r) (hs : 0 < s) :
    ∫ t : ℝ in Ioi 0, t ^ r * Real.exp (-(s * t)) = Real.Gamma (r + 1) * s ^ (-(r + 1)) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := r + 1) (r := s) (by linarith) hs
  rw [add_sub_cancel_right] at h
  rw [h, one_div, Real.inv_rpow hs.le, Real.rpow_neg hs.le]
  ring

/-- The Laplace integrand `t^r (1+t)^{-p} e^{-st}` is a.e. strongly measurable on `(0, ∞)`. -/
private lemma cfInt_aestronglyMeasurable_laplace_rpow (r p s : ℝ) :
    AEStronglyMeasurable (fun t : ℝ => t ^ r * (1 + t) ^ (-p) * Real.exp (-(s * t)))
      (volume.restrict (Ioi 0)) := by
  refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
  have ht0 : (0 : ℝ) < t := ht
  exact (((Real.continuousAt_rpow_const _ _ (Or.inl ht0.ne')).mul
    (Real.continuousAt_rpow_const _ _ (Or.inl (by simp only [Pi.add_apply, _root_.id]; linarith)) |>.comp
      (continuous_const.add continuous_id).continuousAt)).mul
    (Real.continuous_exp.comp (by fun_prop)).continuousAt).continuousWithinAt

/-- The case `p ≥ 0` of `cfInt_laplace_rpow_le`. -/
private lemma cfInt_laplace_rpow_le_of_nonneg {r p : ℝ} (hr : -1 < r) (hrp : -1 < r - p)
    (hp : 0 ≤ p) :
    ∃ C, ∀ s : ℝ, 0 < s →
      IntegrableOn (fun t : ℝ => t ^ r * (1 + t) ^ (-p) * Real.exp (-(s * t))) (Ioi 0) ∧
      ∫ t : ℝ in Ioi 0, t ^ r * (1 + t) ^ (-p) * Real.exp (-(s * t)) ≤
        C * (s ^ (p - r - 1) * (1 + s) ^ (-p)) := by
  have hmeas := cfInt_aestronglyMeasurable_laplace_rpow r p
  refine ⟨2 ^ p * max (Real.Gamma (r + 1)) (Real.Gamma (r - p + 1)), fun s hs => ?_⟩
  have hI1 := cfInt_integrableOn_rpow_exp hr hs
  have hI2 := cfInt_integrableOn_rpow_exp hrp hs
  have hle1 : ∀ t ∈ Ioi (0 : ℝ), t ^ r * (1 + t) ^ (-p) * Real.exp (-(s * t)) ≤
      t ^ r * Real.exp (-(s * t)) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have : (1 + t) ^ (-p) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    have h0 : 0 ≤ t ^ r * Real.exp (-(s * t)) := by positivity
    nlinarith [Real.rpow_nonneg (by linarith : (0:ℝ) ≤ 1 + t) (-p),
      mul_nonneg (Real.rpow_nonneg ht0.le r) (Real.exp_pos (-(s * t))).le]
  have hle2 : ∀ t ∈ Ioi (0 : ℝ), t ^ r * (1 + t) ^ (-p) * Real.exp (-(s * t)) ≤
      t ^ (r - p) * Real.exp (-(s * t)) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have h1 : (1 + t) ^ (-p) ≤ t ^ (-p) :=
      Real.rpow_le_rpow_of_nonpos ht0 (by linarith) (by linarith)
    rw [show r - p = r + -p by ring, Real.rpow_add ht0]
    have := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg ht0.le r)
    exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
  have hnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ t ^ r * (1 + t) ^ (-p) * Real.exp (-(s * t)) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have := Real.rpow_nonneg (by linarith : (0:ℝ) ≤ 1 + t) (-p)
    positivity
  have hInt : IntegrableOn (fun t : ℝ => t ^ r * (1 + t) ^ (-p) * Real.exp (-(s * t))) (Ioi 0) :=
    hI1.mono' (hmeas s) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_of_nonneg (hnn t ht)]; exact hle1 t ht)
  refine ⟨hInt, ?_⟩
  have hJ1 := setIntegral_mono_on hInt hI1 measurableSet_Ioi hle1
  have hJ2 := setIntegral_mono_on hInt hI2 measurableSet_Ioi hle2
  rw [cfInt_integral_rpow_exp hr hs] at hJ1
  rw [cfInt_integral_rpow_exp hrp hs] at hJ2
  have hG1 := Real.Gamma_pos_of_pos (by linarith : 0 < r + 1)
  have hG2 := Real.Gamma_pos_of_pos (by linarith : 0 < r - p + 1)
  have h2p : (1 : ℝ) ≤ 2 ^ p := Real.one_le_rpow (by norm_num) hp
  rcases le_or_gt 1 s with hs1 | hs1
  · -- `s ≥ 1`: use the first bound
    refine hJ1.trans ?_
    have e1 : s ^ (-(r + 1)) = s ^ (p - r - 1) * s ^ (-p) := by
      rw [← Real.rpow_add hs]; ring_nf
    have e2 : s ^ (-p) ≤ 2 ^ p * (1 + s) ^ (-p) := by
      have key : (1 + s) ^ p ≤ 2 ^ p * s ^ p :=
        (Real.rpow_le_rpow (by linarith) (by linarith) hp).trans_eq
          (Real.mul_rpow (by norm_num) hs.le)
      rw [Real.rpow_neg hs.le, Real.rpow_neg (by linarith), ← div_eq_mul_inv,
        le_div_iff₀ (by positivity)]
      calc (s ^ p)⁻¹ * (1 + s) ^ p ≤ (s ^ p)⁻¹ * (2 ^ p * s ^ p) := by gcongr
        _ = 2 ^ p := by field_simp
    rw [e1]
    calc Real.Gamma (r + 1) * (s ^ (p - r - 1) * s ^ (-p))
        ≤ max (Real.Gamma (r + 1)) (Real.Gamma (r - p + 1)) *
            (s ^ (p - r - 1) * (2 ^ p * (1 + s) ^ (-p))) := by
          gcongr
          · exact le_max_left _ _
      _ = _ := by ring
  · -- `s < 1`: use the second bound
    refine hJ2.trans ?_
    have e1 : s ^ (-(r - p + 1)) = s ^ (p - r - 1) := by ring_nf
    have e2 : 1 ≤ 2 ^ p * (1 + s) ^ (-p) := by
      rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
      exact Real.rpow_le_rpow (by linarith) (by linarith) hp
    rw [e1]
    calc Real.Gamma (r - p + 1) * s ^ (p - r - 1)
        ≤ max (Real.Gamma (r + 1)) (Real.Gamma (r - p + 1)) *
            (s ^ (p - r - 1) * (2 ^ p * (1 + s) ^ (-p))) := by
          have hs0 : 0 ≤ s ^ (p - r - 1) := by positivity
          calc Real.Gamma (r - p + 1) * s ^ (p - r - 1)
              ≤ max (Real.Gamma (r + 1)) (Real.Gamma (r - p + 1)) * (s ^ (p - r - 1) * 1) := by
                rw [mul_one]; gcongr; exact le_max_right _ _
            _ ≤ _ := by gcongr
      _ = _ := by ring

/-- The case `p < 0` of `cfInt_laplace_rpow_le`. -/
private lemma cfInt_laplace_rpow_le_of_neg {r p : ℝ} (hr : -1 < r) (hp : p < 0) :
    ∃ C, ∀ s : ℝ, 0 < s →
      IntegrableOn (fun t : ℝ => t ^ r * (1 + t) ^ (-p) * Real.exp (-(s * t))) (Ioi 0) ∧
      ∫ t : ℝ in Ioi 0, t ^ r * (1 + t) ^ (-p) * Real.exp (-(s * t)) ≤
        C * (s ^ (p - r - 1) * (1 + s) ^ (-p)) := by
  have hmeas := cfInt_aestronglyMeasurable_laplace_rpow r p
  set q := -p with hq
  have hq0 : 0 < q := by linarith
  refine ⟨2 ^ q * (Real.Gamma (r + 1) + Real.Gamma (r + q + 1)), fun s hs => ?_⟩
  have hI1 := cfInt_integrableOn_rpow_exp hr hs
  have hI2 := cfInt_integrableOn_rpow_exp (r := r + q) (by linarith) hs
  have hle : ∀ t ∈ Ioi (0 : ℝ), t ^ r * (1 + t) ^ (-p) * Real.exp (-(s * t)) ≤
      2 ^ q * (t ^ r * Real.exp (-(s * t)) + t ^ (r + q) * Real.exp (-(s * t))) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have h1 : (1 + t) ^ q ≤ 2 ^ q * (1 + t ^ q) := by
      rcases le_or_gt t 1 with ht1 | ht1
      · calc (1 + t) ^ q ≤ 2 ^ q := Real.rpow_le_rpow (by linarith) (by linarith) hq0.le
          _ ≤ 2 ^ q * (1 + t ^ q) := le_mul_of_one_le_right (by positivity)
              (by linarith [Real.rpow_nonneg ht0.le q])
      · calc (1 + t) ^ q ≤ (2 * t) ^ q := Real.rpow_le_rpow (by linarith) (by linarith) hq0.le
          _ = 2 ^ q * t ^ q := Real.mul_rpow (by norm_num) ht0.le
          _ ≤ 2 ^ q * (1 + t ^ q) := by gcongr; linarith
    rw [show -p = q by rw [hq]]
    rw [Real.rpow_add ht0]
    have he := (Real.exp_pos (-(s * t))).le
    have htr := Real.rpow_nonneg ht0.le r
    calc t ^ r * (1 + t) ^ q * Real.exp (-(s * t))
        ≤ t ^ r * (2 ^ q * (1 + t ^ q)) * Real.exp (-(s * t)) := by gcongr
      _ = _ := by ring
  have hnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ t ^ r * (1 + t) ^ (-p) * Real.exp (-(s * t)) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have := Real.rpow_nonneg (by linarith : (0:ℝ) ≤ 1 + t) (-p)
    positivity
  have hS : IntegrableOn (fun t : ℝ => 2 ^ q * (t ^ r * Real.exp (-(s * t)) +
      t ^ (r + q) * Real.exp (-(s * t)))) (Ioi 0) := (hI1.add hI2).const_mul (2 ^ q)
  have hInt : IntegrableOn (fun t : ℝ => t ^ r * (1 + t) ^ (-p) * Real.exp (-(s * t))) (Ioi 0) :=
    hS.mono' (hmeas s) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_of_nonneg (hnn t ht)]; exact hle t ht)
  refine ⟨hInt, ?_⟩
  have hJ := setIntegral_mono_on hInt hS measurableSet_Ioi hle
  rw [integral_const_mul, integral_add hI1 hI2, cfInt_integral_rpow_exp hr hs,
    cfInt_integral_rpow_exp (by linarith) hs] at hJ
  refine hJ.trans ?_
  have e1 : s ^ (-(r + 1)) ≤ s ^ (p - r - 1) * (1 + s) ^ (-p) := by
    rw [show p - r - 1 = -(r + 1) - q by rw [hq]; ring, ← hq, Real.rpow_sub hs, div_mul_eq_mul_div,
      le_div_iff₀ (by positivity)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs.le (by linarith) hq0.le) (by positivity)
  have e2 : s ^ (-(r + q + 1)) ≤ s ^ (p - r - 1) * (1 + s) ^ (-p) := by
    rw [show p - r - 1 = -(r + q + 1) by rw [hq]; ring, ← hq]
    exact le_mul_of_one_le_right (by positivity) (Real.one_le_rpow (by linarith) hq0.le)
  have hG1 := Real.Gamma_pos_of_pos (by linarith : 0 < r + 1)
  have hG2 := Real.Gamma_pos_of_pos (by linarith : 0 < r + q + 1)
  calc 2 ^ q * (Real.Gamma (r + 1) * s ^ (-(r + 1)) + Real.Gamma (r + q + 1) * s ^ (-(r + q + 1)))
      ≤ 2 ^ q * (Real.Gamma (r + 1) * (s ^ (p - r - 1) * (1 + s) ^ (-p)) +
          Real.Gamma (r + q + 1) * (s ^ (p - r - 1) * (1 + s) ^ (-p))) := by gcongr
    _ = _ := by ring

/-- `∫₀^∞ e^{-st} t^r (1+t)^{-p} dt ≤ C s^{p-r-1} (1+s)^{-p}` for `r > -1`, `r - p > -1`. -/
theorem cfInt_laplace_rpow_le {r p : ℝ} (hr : -1 < r) (hrp : -1 < r - p) :
    ∃ C, ∀ s : ℝ, 0 < s →
      IntegrableOn (fun t : ℝ => t ^ r * (1 + t) ^ (-p) * Real.exp (-(s * t))) (Ioi 0) ∧
      ∫ t : ℝ in Ioi 0, t ^ r * (1 + t) ^ (-p) * Real.exp (-(s * t)) ≤
        C * (s ^ (p - r - 1) * (1 + s) ^ (-p)) := by
  rcases le_or_gt 0 p with hp | hp
  · exact cfInt_laplace_rpow_le_of_nonneg hr hrp hp
  · exact cfInt_laplace_rpow_le_of_neg hr hp

/-- Two comparable positive quantities have comparable real powers. -/
theorem cfInt_rpow_le_of_le_mul {A B m M : ℝ} (hA : 0 < A) (hm : 0 < m) (h1 : m * A ≤ B)
    (h2 : B ≤ M * A) (u : ℝ) : B ^ u ≤ max (m ^ u) (M ^ u) * A ^ u := by
  have hB : 0 < B := lt_of_lt_of_le (by positivity) h1
  have hM : 0 < M := by
    by_contra h; push Not at h; nlinarith
  rcases le_or_gt 0 u with hu | hu
  · calc B ^ u ≤ (M * A) ^ u := Real.rpow_le_rpow hB.le h2 hu
      _ = M ^ u * A ^ u := Real.mul_rpow hM.le hA.le
      _ ≤ _ := by gcongr; exact le_max_right _ _
  · calc B ^ u ≤ (m * A) ^ u := Real.rpow_le_rpow_of_nonpos (by positivity) h1 hu.le
      _ = m ^ u * A ^ u := Real.mul_rpow hm.le hA.le
      _ ≤ _ := by gcongr; exact le_max_left _ _

/-- A function continuous on `[a₀,∞)` and `O(g)` at infinity, with `g` continuous and positive,
is bounded by a multiple of `g` on `[a₀,∞)`. -/
theorem cfInt_exists_bound_Ici {f : ℝ → ℂ} {g : ℝ → ℝ} (a₀ : ℝ) (hf : ContinuousOn f (Ici a₀))
    (hg : ContinuousOn g (Ici a₀)) (hgpos : ∀ t, a₀ ≤ t → 0 < g t) (h : f =O[atTop] g) :
    ∃ C, ∀ t, a₀ ≤ t → ‖f t‖ ≤ C * g t := by
  obtain ⟨C1, hC1⟩ := h.bound
  obtain ⟨T, hT⟩ := eventually_atTop.mp hC1
  have hq : ContinuousOn (fun t => ‖f t‖ / g t) (Icc a₀ (max T a₀)) :=
    (hf.norm.div hg fun t ht => (hgpos t ht).ne').mono (fun t ht => ht.1)
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hq
  refine ⟨max C1 K, fun t ht => ?_⟩
  have hg0 := hgpos t ht
  rcases le_or_gt t (max T a₀) with htT | htT
  · have h1 := hK t ⟨ht, htT⟩
    rw [Real.norm_of_nonneg (div_nonneg (norm_nonneg _) hg0.le), div_le_iff₀ hg0] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hg0.le)
  · have h1 := hT t (le_of_lt (lt_of_le_of_lt (le_max_left _ _) htT))
    rw [Real.norm_of_nonneg hg0.le] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hg0.le)

/-- `‖cos w‖ ≤ e^{|Im w|}`. -/
theorem cfInt_norm_cos_le (w : ℂ) : ‖Complex.cos w‖ ≤ Real.exp |w.im| := by
  rw [Complex.cos]
  have h1 : ‖exp (w * I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; simp only [mul_re, I_re, mul_zero, I_im, mul_one, zero_sub]
    exact Real.exp_le_exp.mpr (neg_le_abs _)
  have h2 : ‖exp (-w * I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; simp only [mul_re, neg_re, I_re, mul_zero, neg_im, I_im, mul_one,
      zero_sub, neg_neg]
    exact Real.exp_le_exp.mpr (le_abs_self _)
  rw [norm_div, Complex.norm_two]
  have := norm_add_le (exp (w * I)) (exp (-w * I))
  linarith

/-- **Global bound for `J_ν` on the positive axis**: `|J_ν(y)| ≤ C y^{re ν} (1+y)^{-re ν - 1/2}`. -/
theorem cfInt_exists_norm_besselJ_le (ν : ℂ) :
    ∃ C, ∀ y : ℝ, 0 < y → ‖besselJ ν y‖ ≤ C * (y ^ ν.re * (1 + y) ^ (-(ν.re + 1 / 2))) := by
  set σ := ν.re
  obtain ⟨M, hM⟩ := exists_norm_besselJ_mul_le ν (c := 1) one_pos
  -- large `y`
  have hO : (fun y : ℝ => besselJ ν y) =O[atTop] fun y : ℝ => y ^ (-(1 / 2 : ℝ)) := by
    have h1 := besselJ_sub_cos_isBigO ν
    have h2 : (fun y : ℝ => (Real.sqrt (2 / (π * y)) : ℂ) * Complex.cos (y - ν * π / 2 - π / 4))
        =O[atTop] fun y : ℝ => y ^ (-(1 / 2 : ℝ)) := by
      refine IsBigO.of_bound (Real.sqrt (2 / π) * Real.exp |(ν * π / 2).im|) ?_
      filter_upwards [eventually_gt_atTop 0] with y hy
      rw [norm_mul, norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
        Real.norm_of_nonneg (by positivity)]
      have hc := cfInt_norm_cos_le ((y : ℂ) - ν * π / 2 - π / 4)
      have him : (((y : ℂ) - ν * π / 2 - π / 4)).im = -((ν * π / 2).im) := by
        simp
      rw [him, abs_neg] at hc
      have hs : Real.sqrt (2 / (π * y)) = Real.sqrt (2 / π) * y ^ (-(1 / 2 : ℝ)) := by
        rw [Real.rpow_neg hy.le, ← Real.sqrt_eq_rpow, div_mul_eq_div_div, Real.sqrt_div' _ hy.le]
        · ring
      rw [hs]
      calc Real.sqrt (2 / π) * y ^ (-(1 / 2 : ℝ)) * ‖Complex.cos (y - ν * π / 2 - π / 4)‖
          ≤ Real.sqrt (2 / π) * y ^ (-(1 / 2 : ℝ)) * Real.exp |(ν * π / 2).im| := by gcongr
        _ = _ := by ring
    have h3 : (fun y : ℝ => y ^ (-(3 / 2) : ℝ)) =O[atTop] fun y : ℝ => y ^ (-(1 / 2 : ℝ)) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [eventually_ge_atTop 1] with y hy
      rw [one_mul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
      exact Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
    exact ((h1.trans h3).add h2).congr_left fun y => by ring
  have hcont : ContinuousOn (fun y : ℝ => besselJ ν y) (Ici 1) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := by simp only [mem_Ici] at hy; linarith
    have := continuousAt_besselJ_mul ν (c := 1) one_pos hy0
    simp only [ofReal_one, one_mul] at this
    exact this.continuousWithinAt
  obtain ⟨C2, hC2⟩ := cfInt_exists_bound_Ici 1 hcont
    (fun y hy => (Real.continuousAt_rpow_const _ _ (Or.inl (by
      simp only [mem_Ici] at hy; linarith))).continuousWithinAt)
    (fun y hy => by positivity) hO
  set u := -(σ + 1 / 2)
  refine ⟨max (M * 2 ^ |u|) (C2 * 2 ^ |u|), fun y hy => ?_⟩
  rcases le_or_gt y 1 with hy1 | hy1
  · have h1 := hM y ⟨hy, hy1⟩
    simp only [ofReal_one, one_mul] at h1
    have h2 : 1 ≤ 2 ^ |u| * (1 + y) ^ u := by
      rcases le_or_gt 0 u with hu | hu
      · exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (by norm_num) (abs_nonneg _))
          (Real.one_le_rpow (by linarith) hu)
      · rw [abs_of_neg hu]
        have : (2 : ℝ) ^ u ≤ (1 + y) ^ u := Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith)
          hu.le
        calc (1 : ℝ) = 2 ^ (-u) * 2 ^ u := by rw [← Real.rpow_add (by norm_num)]; simp
          _ ≤ _ := by gcongr
    have hM0 : 0 ≤ M := by
      have := (norm_nonneg _).trans h1
      exact nonneg_of_mul_nonneg_left this (by positivity)
    calc ‖besselJ ν y‖ ≤ M * y ^ σ := h1
      _ ≤ M * y ^ σ * (2 ^ |u| * (1 + y) ^ u) := le_mul_of_one_le_right (by positivity) h2
      _ = (M * 2 ^ |u|) * (y ^ σ * (1 + y) ^ u) := by ring
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · have h1 := hC2 y hy1.le
    have h2 : y ^ (-(1 / 2 : ℝ)) ≤ 2 ^ |u| * (y ^ σ * (1 + y) ^ u) := by
      have := kumDec_rpow_le_one_add hy1.le u
      calc y ^ (-(1 / 2 : ℝ)) = y ^ σ * y ^ u := by
            rw [← Real.rpow_add hy]; congr 1; simp only [u]; ring
        _ ≤ y ^ σ * (2 ^ |u| * (1 + y) ^ u) := by gcongr
        _ = _ := by ring
    have hC20 : 0 ≤ C2 := by
      have := (norm_nonneg _).trans h1
      exact nonneg_of_mul_nonneg_left this (by positivity)
    calc ‖besselJ ν y‖ ≤ C2 * y ^ (-(1 / 2 : ℝ)) := h1
      _ ≤ C2 * (2 ^ |u| * (y ^ σ * (1 + y) ^ u)) := by gcongr
      _ = (C2 * 2 ^ |u|) * (y ^ σ * (1 + y) ^ u) := by ring
      _ ≤ _ := by
          gcongr
          exact le_max_right _ _

/-- `‖Γ(w+k)‖ Γ(re w) ≥ ‖Γ(w)‖ Γ(re w + k)` for `re w > 0`. -/
theorem cfInt_norm_Gamma_add_nat_ge {w : ℂ} (hw : 0 < w.re) (k : ℕ) :
    ‖Gamma w‖ * Real.Gamma (w.re + k) ≤ ‖Gamma (w + k)‖ * Real.Gamma w.re := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : Gamma (w + (k + 1 : ℕ)) = (w + k) * Gamma (w + k) := by
      rw [show w + ((k + 1 : ℕ) : ℂ) = (w + k) + 1 by push_cast; ring, Gamma_add_one]
      intro h; have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    have h2 : Real.Gamma (w.re + (k + 1 : ℕ)) = (w.re + k) * Real.Gamma (w.re + k) := by
      rw [show w.re + ((k + 1 : ℕ) : ℝ) = (w.re + k) + 1 by push_cast; ring,
        Real.Gamma_add_one (by positivity)]
    have h3 : w.re + k ≤ ‖w + k‖ := by
      calc w.re + k = (w + k).re := by simp
        _ ≤ _ := re_le_norm _
    rw [h1, h2, norm_mul]
    have hG := (Real.Gamma_pos_of_pos (by positivity : 0 < w.re)).le
    calc ‖Gamma w‖ * ((w.re + k) * Real.Gamma (w.re + k))
        = (w.re + k) * (‖Gamma w‖ * Real.Gamma (w.re + k)) := by ring
      _ ≤ ‖w + k‖ * (‖Gamma (w + k)‖ * Real.Gamma w.re) := by
          gcongr
      _ = _ := by ring

/-- The kernel `t^{ν/2} J_ν(2√(xt))` in power-series form. -/
theorem cfInt_kernel_eq (ν : ℂ) {x : ℂ} (hx : x ≠ 0) {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ (ν / 2) * besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      x ^ (ν / 2) * ((t : ℂ) ^ ν * regularizedHGFun ∅ {ν + 1} (-x * t)) := by
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  rw [besselJ_two_sqrt hx ht]
  have hνt : (t : ℂ) ^ (ν / 2) * (t : ℂ) ^ (ν / 2) = (t : ℂ) ^ ν := by
    rw [← cpow_add _ _ htc]; ring_nf
  linear_combination (x ^ (ν / 2) * regularizedHGFun ∅ {ν + 1} (-x * t)) * hνt

/-- The Hankel kernel `t^{ν/2} J_ν(2√(xt))` is continuous on `(0,∞)`. -/
theorem cfInt_continuousOn_kernel (ν : ℂ) {x : ℂ} (hx : x ≠ 0) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ (ν / 2) * besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)))
      (Ioi 0) := by
  have h : ContinuousOn (fun t : ℝ => x ^ (ν / 2) * ((t : ℂ) ^ ν *
      regularizedHGFun ∅ {ν + 1} (-x * t))) (Ioi 0) := by
    refine continuousOn_const.mul (ContinuousOn.mul ?_ ?_)
    · exact ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
        fun t ht => ofReal_mem_slitPlane.mpr ht
    · exact (continuous_regularized0F1.comp (by fun_prop :
        Continuous fun t : ℝ => (ν + 1, -x * t))).continuousOn
  exact h.congr fun t ht => cfInt_kernel_eq ν hx ht

/-- **The Laplace transform of the Hankel kernel**:
`∫₀^∞ e^{-st} t^{ν/2} J_ν(2√(xt)) dt = x^{ν/2} s^{-ν-1} e^{-x/s}`, for `re ν > -1`, `s > 0`. -/
theorem cfInt_laplace_kernel {ν x : ℂ} (hν : -1 < ν.re) (hx : x ≠ 0) {s : ℝ} (hs : 0 < s) :
    ∫ t : ℝ in Ioi 0, exp (-(s * t : ℂ)) * ((t : ℂ) ^ (ν / 2) *
        besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ))) =
      x ^ (ν / 2) * ((s : ℂ) ^ (-(ν + 1)) * exp (-x / s)) := by
  set d := regularizedHGFunCoeff (∅ : Multiset ℂ) {ν + 1} with hd
  set F : ℕ → ℝ → ℂ := fun k t => x ^ (ν / 2) * (d k * (-x) ^ k) *
    ((t : ℂ) ^ (ν + k + 1 - 1) * exp (-(s * t : ℂ))) with hF
  have hνk : ∀ k : ℕ, 0 < (ν + k + 1).re := fun k => by
    simp; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hGk : ∀ k : ℕ, ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (ν + k + 1 - 1) * exp (-(s * t : ℂ)) =
      (1 / (s : ℂ)) ^ (ν + k + 1) * Gamma (ν + k + 1) := fun k => by
    have := integral_cpow_mul_exp_neg_mul_Ioi (a := ν + k + 1) (r := s) (hνk k) hs
    simpa using this
  have hIk : ∀ k : ℕ, IntegrableOn (fun t : ℝ => (t : ℂ) ^ (ν + k + 1 - 1) *
      exp (-(s * t : ℂ))) (Ioi 0) := fun k => by
    have h := cfInt_integrableOn_rpow_exp (r := (ν + k + 1).re - 1) (by linarith [hνk k]) hs
    refine h.mono' ?_ ?_
    · exact (ContinuousOn.mul (ContinuousOn.cpow continuous_ofReal.continuousOn
        continuousOn_const fun t ht => ofReal_mem_slitPlane.mpr ht)
        (by fun_prop : Continuous fun t : ℝ => exp (-(s * t : ℂ))).continuousOn)
        |>.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := ht
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_exp]
      apply le_of_eq; simp
  have hFi : ∀ k, IntegrableOn (F k) (Ioi 0) := fun k => (hIk k).const_mul _
  have hGpos : 0 < Real.Gamma (ν.re + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hG0 : Gamma (ν + 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hnormF : ∀ k : ℕ, ∫ t : ℝ in Ioi 0, ‖F k t‖ ≤
      ‖x ^ (ν / 2)‖ * (Real.Gamma (ν.re + 1) / ‖Gamma (ν + 1)‖) * s ^ (-(ν.re + 1)) *
        ((‖x‖ / s) ^ k / k.factorial) := by
    intro k
    have hint : ∫ t : ℝ in Ioi 0, ‖F k t‖ = ‖x ^ (ν / 2)‖ * ‖d k‖ * ‖x‖ ^ k *
        (Real.Gamma (ν.re + k + 1) * s ^ (-(ν.re + k + 1))) := by
      have : ∀ t ∈ Ioi (0 : ℝ), ‖F k t‖ = ‖x ^ (ν / 2)‖ * ‖d k‖ * ‖x‖ ^ k *
          (t ^ (ν.re + k) * Real.exp (-(s * t))) := by
        intro t ht
        have ht0 : (0 : ℝ) < t := ht
        simp only [hF, norm_mul, norm_pow, norm_neg]
        rw [norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_exp]
        simp only [add_re, natCast_re, add_sub_cancel_right]
        have : (-(↑s * ↑t : ℂ)).re = -(s * t) := by simp
        rw [this]; ring
      rw [setIntegral_congr_fun measurableSet_Ioi this, integral_const_mul,
        cfInt_integral_rpow_exp (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]) hs]
    rw [hint, hd, DLMF.Bessel.regularizedHGFunCoeff_empty]
    have hGk := cfInt_norm_Gamma_add_nat_ge (w := ν + 1) (by simp; linarith) k
    simp only [add_re, one_re] at hGk
    have hGnk : 0 < ‖Gamma (ν + 1 + k)‖ := by
      have := Gamma_ne_zero_of_re_pos (s := ν + 1 + k) (by simp; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])
      exact norm_pos_iff.mpr this
    have hG1 : 0 < ‖Gamma (ν + 1)‖ := norm_pos_iff.mpr hG0
    rw [show ν + 1 + (k : ℂ) = ν + 1 + k by rfl] at hGnk
    simp only [norm_div, norm_one, norm_mul, Complex.norm_natCast]
    rw [show ν.re + k + 1 = ν.re + 1 + k by ring, show -(ν.re + 1 + k) = -(ν.re + 1) + -(k : ℝ) by ring,
      Real.rpow_add hs, Real.rpow_neg hs.le (k : ℝ), Real.rpow_natCast, div_pow]
    have hfac : (0 : ℝ) < k.factorial := by positivity
    have hsk : (0 : ℝ) < s ^ k := by positivity
    have hkey : Real.Gamma (ν.re + 1 + k) / ‖Gamma (ν + 1 + k)‖ ≤
        Real.Gamma (ν.re + 1) / ‖Gamma (ν + 1)‖ := by
      rw [div_le_div_iff₀ hGnk hG1]; linarith
    have hpos : 0 ≤ ‖x ^ (ν / 2)‖ * ‖x‖ ^ k * s ^ (-(ν.re + 1)) / (k.factorial * s ^ k) := by
      positivity
    calc ‖x ^ (ν / 2)‖ * (1 / (k.factorial * ‖Gamma (ν + 1 + k)‖)) * ‖x‖ ^ k *
          (Real.Gamma (ν.re + 1 + k) * (s ^ (-(ν.re + 1)) * (s ^ k)⁻¹))
        = (Real.Gamma (ν.re + 1 + k) / ‖Gamma (ν + 1 + k)‖) *
            (‖x ^ (ν / 2)‖ * ‖x‖ ^ k * s ^ (-(ν.re + 1)) / (k.factorial * s ^ k)) := by
          field_simp
      _ ≤ (Real.Gamma (ν.re + 1) / ‖Gamma (ν + 1)‖) *
            (‖x ^ (ν / 2)‖ * ‖x‖ ^ k * s ^ (-(ν.re + 1)) / (k.factorial * s ^ k)) := by
          gcongr
      _ = _ := by field_simp
  have hsum : Summable fun k => ∫ t : ℝ in Ioi 0, ‖F k t‖ := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun t => norm_nonneg _) hnormF ?_
    exact (Real.summable_pow_div_factorial (‖x‖ / s)).mul_left _
  have hs' := hasSum_integral_of_summable_integral_norm hFi hsum
  have hterm : ∀ k : ℕ, ∫ t : ℝ in Ioi 0, F k t =
      x ^ (ν / 2) * ((s : ℂ) ^ (-(ν + 1)) * ((-x / s) ^ k / k.factorial)) := by
    intro k
    have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
    simp only [hF]
    rw [integral_const_mul, hGk k, hd, DLMF.Bessel.regularizedHGFunCoeff_empty]
    have hGk' : Gamma (ν + 1 + k) ≠ 0 := Gamma_ne_zero_of_re_pos (by
      simp; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])
    have hp : (1 / (s : ℂ)) ^ (ν + k + 1) = (s : ℂ) ^ (-(ν + 1)) * ((s : ℂ) ^ k)⁻¹ := by
      rw [one_div, inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hs.le]; exact Real.pi_ne_zero.symm),
        ← cpow_neg, show -(ν + k + 1) = -(ν + 1) + -(k : ℂ) by ring, cpow_add _ _ hs0, cpow_neg,
        cpow_neg (s : ℂ) (k : ℂ), cpow_natCast]
    rw [hp, show ν + k + 1 = ν + 1 + k by ring, div_pow]
    field_simp
  simp_rw [hterm] at hs'
  have hexp : HasSum (fun k : ℕ => (-x / s) ^ k / k.factorial) (exp (-x / s)) := by
    simpa only [exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp (-x / s)
  have hR := (hexp.mul_left ((s : ℂ) ^ (-(ν + 1)))).mul_left (x ^ (ν / 2))
  rw [← hs'.unique hR]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
  rw [cfInt_kernel_eq ν hx ht0]
  have h0 := ((DLMF.Bessel.hasFPowerSeriesOnBall_regularized0F1 (ν + 1)).hasSum_mul_pow
    (z := -x * t) (by simp)).mul_left (x ^ (ν / 2) * (exp (-(s * t : ℂ)) * (t : ℂ) ^ ν))
  refine Eq.trans ?_ (h0.tsum_eq.symm.trans (tsum_congr fun k => ?_))
  · ring
  · simp only [hF, ← hd]
    rw [show ν + k + 1 - 1 = ν + k by ring, cpow_add _ _ htc, cpow_natCast, mul_pow]
    ring

/-- `2 ((r t)^{1/2})` as a real number. -/
theorem cfInt_two_sqrt_eq {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) :
    2 * ((r : ℂ) * t) ^ (1 / 2 : ℂ) = ((2 * (Real.sqrt r * Real.sqrt t) : ℝ) : ℂ) := by
  rw [show ((r : ℂ) * t) = ((r * t : ℝ) : ℂ) by push_cast; ring,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow (by positivity),
    ← Real.sqrt_eq_rpow, Real.sqrt_mul hr]
  push_cast; ring

/-- The Hankel kernel bound `‖t^{ν/2} J_ν(2√(rt))‖ ≤ C t^{re ν} (1+t)^{-(re ν/2+1/4)}`. -/
theorem cfInt_exists_norm_kernel_le (ν : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ C, ∀ t : ℝ, 0 < t →
      ‖(t : ℂ) ^ (ν / 2) * besselJ ν (2 * ((r : ℂ) * t) ^ (1 / 2 : ℂ))‖ ≤
        C * (t ^ ν.re * (1 + t) ^ (-(ν.re / 2 + 1 / 4))) := by
  obtain ⟨C, hC⟩ := cfInt_exists_norm_besselJ_le ν
  set σ := ν.re with hσ
  set q := Real.sqrt r with hq
  have hq0 : 0 < q := Real.sqrt_pos.mpr hr
  set m := min 1 (2 * q) with hm
  set M := 1 + 2 * q with hM
  have hm0 : 0 < m := lt_min one_pos (by positivity)
  set u := -(σ + 1 / 2) with hu
  refine ⟨max C 0 * 2 ^ σ * q ^ σ * max (m ^ u) (M ^ u), fun t ht => ?_⟩
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  set y := 2 * (q * Real.sqrt t) with hy
  have hy0 : 0 < y := by positivity
  rw [cfInt_two_sqrt_eq hr.le ht.le, norm_mul, norm_cpow_eq_rpow_re_of_pos ht]
  have hre : (ν / 2).re = σ / 2 := by simp [hσ]
  rw [hre]
  set A := Real.sqrt (1 + t) with hA
  have hA0 : 0 < A := Real.sqrt_pos.mpr (by linarith)
  have hA1 : 1 ≤ A := by rw [hA, Real.one_le_sqrt]; linarith
  have hAt : Real.sqrt t ≤ A := Real.sqrt_le_sqrt (by linarith)
  have hA2 : A ≤ 1 + Real.sqrt t := by
    rw [hA, Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt ht.le, hst]
  have h1 : m * A ≤ 1 + y := by
    have hm1 : m ≤ 1 := min_le_left _ _
    have hm2 : m ≤ 2 * q := min_le_right _ _
    calc m * A ≤ m * (1 + Real.sqrt t) := by gcongr
      _ = m + m * Real.sqrt t := by ring
      _ ≤ 1 + 2 * q * Real.sqrt t := by gcongr
      _ = 1 + y := by rw [hy]; ring
  have h2 : 1 + y ≤ M * A := by
    rw [hy, hM]; nlinarith
  have hB := cfInt_rpow_le_of_le_mul hA0 hm0 h1 h2 u
  have hAu : A ^ u = (1 + t) ^ (-(σ / 2 + 1 / 4)) := by
    rw [hA, Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith), hu]; congr 1; ring
  have hyσ : y ^ σ = 2 ^ σ * q ^ σ * t ^ (σ / 2) := by
    rw [hy, Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow hq0.le hst.le,
      Real.sqrt_eq_rpow t, ← Real.rpow_mul ht.le]
    ring_nf
  have htt : t ^ (σ / 2) * t ^ (σ / 2) = t ^ σ := by
    rw [← Real.rpow_add ht]; ring_nf
  have hJ := hC y hy0
  have hJ' : ‖besselJ ν (y : ℂ)‖ ≤ max C 0 * (y ^ σ * (max (m ^ u) (M ^ u) * A ^ u)) := by
    calc ‖besselJ ν (y : ℂ)‖ ≤ C * (y ^ σ * (1 + y) ^ u) := hJ
      _ ≤ max C 0 * (y ^ σ * (1 + y) ^ u) := by gcongr; exact le_max_left _ _
      _ ≤ _ := by gcongr
  have htp : 0 ≤ t ^ (σ / 2) := by positivity
  calc t ^ (σ / 2) * ‖besselJ ν (y : ℂ)‖
      ≤ t ^ (σ / 2) * (max C 0 * (y ^ σ * (max (m ^ u) (M ^ u) * A ^ u))) := by gcongr
    _ = _ := by
      rw [hAu, hyσ, ← htt]; ring

/-- The substitution `s ↦ 1/s` turning the Hankel–Laplace integral into a Tricomi `U` integral. -/
theorem cfInt_recip_subst_U {a b ν x : ℂ} (hx : 0 < x.re) (hA : 0 < (ν - b + 2).re) :
    ∫ s : ℝ in Ioi 0, (s : ℂ) ^ (a - 1) * (1 + (s : ℂ)) ^ (b - a - 1) *
        ((s : ℂ) ^ (-(ν + 1)) * exp (-x / s)) =
      Gamma (ν - b + 2) * kummerU (ν - b + 2) (ν - a + 2) x := by
  have hU := kummerU_laplace (a := ν - b + 2) (b := ν - a + 2) (z := x) hA hx
  have hGA : Gamma (ν - b + 2) ≠ 0 := Gamma_ne_zero_of_re_pos hA
  rw [show ν - a + 2 - (ν - b + 2) - 1 = b - a - 1 by ring,
    show ν - b + 2 - 1 = ν - b + 1 by ring] at hU
  set g : ℝ → ℂ := fun u => exp (-x * u) * (u : ℂ) ^ (ν - b + 1) * (1 + (u : ℂ)) ^ (b - a - 1)
    with hg
  have hsub := integral_comp_rpow_Ioi g (p := -1) (by norm_num)
  rw [hU, ← hsub]
  field_simp
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs0 : (0 : ℝ) < s := hs
  have hsc : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs0.ne'
  have harg : (s : ℂ).arg ≠ π := by rw [arg_ofReal_of_nonneg hs0.le]; exact Real.pi_ne_zero.symm
  simp only [hg, Real.rpow_neg_one, abs_neg, abs_one, one_mul, real_smul]
  have h2 : ((s ^ (-1 - 1 : ℝ) : ℝ) : ℂ) = (s : ℂ) ^ (-2 : ℂ) := by
    rw [ofReal_cpow hs0.le]; norm_num
  have hinv : ∀ w : ℂ, ((s⁻¹ : ℝ) : ℂ) ^ w = (s : ℂ) ^ (-w) := fun w => by
    rw [ofReal_inv, inv_cpow _ _ harg, cpow_neg]
  have h1s : (1 : ℂ) + ((s⁻¹ : ℝ) : ℂ) = ((1 + s : ℝ) : ℂ) * ((s⁻¹ : ℝ) : ℂ) := by
    push_cast; field_simp; ring
  rw [h2, hinv, h1s, mul_cpow_ofReal_nonneg (by linarith) (by positivity), hinv]
  have e1 : (s : ℂ) ^ (-2 : ℂ) * (s : ℂ) ^ (-(ν - b + 1)) * (s : ℂ) ^ (-(b - a - 1)) =
      (s : ℂ) ^ (a - ν - 2) := by
    rw [← cpow_add _ _ hsc, ← cpow_add _ _ hsc]; ring_nf
  have e2 : (s : ℂ) ^ (a - 1) * (s : ℂ) ^ (-(ν + 1)) = (s : ℂ) ^ (a - ν - 2) := by
    rw [← cpow_add _ _ hsc]; ring_nf
  have hex : exp (-x * ((s⁻¹ : ℝ) : ℂ)) = exp (-x / s) := by
    rw [ofReal_inv, div_eq_mul_inv]
  rw [hex]
  push_cast
  simp only [neg_div] at *
  linear_combination (-(exp (-(x / s)) * (1 + (s : ℂ)) ^ (b - a - 1))) * (e1 - e2)

/-- Tricomi's `U(a,b,z)` is entire in its first parameter, for fixed `b` and `z ≠ 0`. -/
theorem cfInt_differentiable_kummerU_fst (b : ℂ) {z : ℂ} (hz : z ≠ 0) :
    Differentiable ℂ (fun a => kummerU a b z) := by
  have hmem : ∀ c ∈ integerComplement, Differentiable ℂ (fun a => kummerU a c z) := by
    intro c hc
    have hfun : (fun a => kummerU a c z) = fun a => π / sin (π * c) * tricomiD a c z := by
      funext a
      rw [kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc),
        kummerUConnection_eq_tricomiD hc]
    rw [hfun]
    refine Differentiable.const_mul ?_ _
    unfold tricomiD
    have h1 : Differentiable ℂ (fun a => regularizedHGFun {a} {c} z) :=
      differentiable_regularizedConfluent_comp differentiable_id (differentiable_const c) z
    have h2 : Differentiable ℂ (fun a => regularizedHGFun {a - c + 1} {2 - c} z) :=
      differentiable_regularizedConfluent_comp (by fun_prop) (differentiable_const _) z
    have h3 : Differentiable ℂ (fun a : ℂ => (Gamma (a - c + 1))⁻¹) :=
      differentiable_one_div_Gamma.comp (by fun_prop)
    have h4 : Differentiable ℂ (fun a : ℂ => (Gamma a)⁻¹) := differentiable_one_div_Gamma
    exact (h1.mul h3).sub ((h2.const_mul _).mul h4)
  have hT : TendstoLocallyUniformlyOn (fun c a => kummerU a c z) (fun a => kummerU a b z)
      (𝓝[integerComplement] b) univ := by
    rw [tendstoLocallyUniformlyOn_iff_filter]
    intro a _
    have hc : ContinuousAt (fun p : ℂ × ℂ => kummerU p.2 p.1 z) (b, a) := by
      have h := continuousAt_kummerU_param a b hz
      exact ContinuousAt.comp (g := fun q : ℂ × ℂ => kummerU q.1 q.2 z)
        (f := fun p : ℂ × ℂ => (p.2, p.1)) h (by fun_prop)
    exact (tendstoUniformlyOnFilter_of_continuousAt (F := fun c a => kummerU a c z) hc
      nhdsWithin_le_nhds).mono_right nhdsWithin_le_nhds
  have := integerComplement_nhdsWithin_neBot b
  have hd := hT.differentiableOn
    (eventually_nhdsWithin_of_forall fun c hc => (hmem c hc).differentiableOn) isOpen_univ
  exact differentiableOn_univ.mp hd

/-- The substitution `s = 1/(1+v)` turning an Euler-type integral on `(0,1)` into a
Tricomi `U` integral. -/
theorem cfInt_euler_subst_U {a c ν x : ℂ} (hx : 0 < x.re) (ha : 0 < a.re) :
    ∫ s in Ioo (0 : ℝ) 1, (s : ℂ) ^ (c - 1) * (1 - (s : ℂ)) ^ (a - 1) *
        ((s : ℂ) ^ (-(ν + 1)) * exp (-x / s)) =
      exp (-x) * (Gamma a * kummerU a (ν + 2 - c) x) := by
  have hU := kummerU_laplace (a := a) (b := ν + 2 - c) (z := x) ha hx
  rw [show ν + 2 - c - a - 1 = ν + 1 - c - a by ring] at hU
  have hGa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha
  set f : ℝ → ℝ := fun v => (1 + v)⁻¹ with hf
  have himg : f '' Ioi 0 = Ioo 0 1 := by
    ext y
    simp only [mem_image, mem_Ioi, mem_Ioo, hf]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨by positivity, inv_lt_one_of_one_lt₀ (by linarith)⟩
    · rintro ⟨h0, h1⟩
      refine ⟨y⁻¹ - 1, ?_, ?_⟩
      · have : 1 < y⁻¹ := (one_lt_inv₀ h0).mpr h1
        linarith
      · rw [show 1 + (y⁻¹ - 1) = y⁻¹ by ring, inv_inv]
  have hderiv : ∀ v ∈ Ioi (0 : ℝ), HasDerivWithinAt f (-((1 + v) ^ 2)⁻¹) (Ioi 0) v := by
    intro v hv
    have hv0 : (0 : ℝ) < v := hv
    have h : HasDerivAt f (-((1 + v) ^ 2)⁻¹) v := by
      have := (hasDerivAt_inv (show (1 + v) ≠ 0 by linarith)).comp v
        ((hasDerivAt_id v).const_add 1)
      simpa [hf, Function.comp_def] using this
    exact h.hasDerivWithinAt
  have hinj : InjOn f (Ioi 0) := fun u _ v _ h => by
    simp only [hf] at h
    have := inv_injective h
    linarith
  set g : ℝ → ℂ := fun s => (s : ℂ) ^ (c - 1) * (1 - (s : ℂ)) ^ (a - 1) *
    ((s : ℂ) ^ (-(ν + 1)) * exp (-x / s)) with hg
  have hsub := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj g
  rw [himg] at hsub
  rw [hsub, hU, show exp (-x) * (Gamma a * (1 / Gamma a * ∫ t : ℝ in Ioi 0,
      exp (-x * t) * (t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (ν + 1 - c - a))) =
      ∫ t : ℝ in Ioi 0, exp (-x) *
        (exp (-x * t) * (t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (ν + 1 - c - a)) by
    rw [integral_const_mul]; field_simp]
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  have hv0 : (0 : ℝ) < v := hv
  have hP0 : (0 : ℝ) < 1 + v := by linarith
  set P : ℂ := ((1 + v : ℝ) : ℂ) with hP
  have hPne : P ≠ 0 := ofReal_ne_zero.mpr hP0.ne'
  have harg : P.arg ≠ π := by rw [hP, arg_ofReal_of_nonneg hP0.le]; exact Real.pi_ne_zero.symm
  have hinv : ∀ w : ℂ, (((1 + v)⁻¹ : ℝ) : ℂ) ^ w = P ^ (-w) := fun w => by
    rw [ofReal_inv, inv_cpow _ _ harg, cpow_neg]
  have h1s : (1 : ℂ) - (((1 + v)⁻¹ : ℝ) : ℂ) = (v : ℂ) * (((1 + v)⁻¹ : ℝ) : ℂ) := by
    rw [ofReal_inv]
    have : (1 + (v : ℂ)) ≠ 0 := by
      have := hPne; rwa [hP, ofReal_add, ofReal_one] at this
    push_cast; field_simp; ring
  have hex : exp (-x / (((1 + v)⁻¹ : ℝ) : ℂ)) = exp (-x) * exp (-x * v) := by
    rw [ofReal_inv, div_inv_eq_mul, ← Complex.exp_add]; push_cast; ring_nf
  have hab : |(-((1 + v) ^ 2)⁻¹ : ℝ)| = ((1 + v) ^ 2)⁻¹ := by
    rw [abs_neg, abs_of_pos (by positivity)]
  have hP2 : ((((1 + v) ^ 2)⁻¹ : ℝ) : ℂ) = (P ^ 2)⁻¹ := by
    rw [hP]; push_cast; ring
  have e : (P ^ 2)⁻¹ * P ^ (-(c - 1)) * P ^ (-(a - 1)) * P ^ (-(-(ν + 1))) =
      P ^ (ν + 1 - c - a) := by
    rw [← cpow_natCast P 2, ← cpow_neg, ← cpow_add _ _ hPne, ← cpow_add _ _ hPne,
      ← cpow_add _ _ hPne]
    push_cast; ring_nf
  have hvP : (1 + (v : ℂ)) = P := by rw [hP]; push_cast; ring
  simp only [hg, hf]
  rw [hab, real_smul, hP2, hinv, h1s, mul_cpow_ofReal_nonneg hv0.le (by positivity), hinv, hinv,
    hex, hvP]
  linear_combination (exp (-x) * exp (-x * v) * (v : ℂ) ^ (a - 1)) * e

/-- 13.10.14 in the Euler region `0 < re a`, in the Kummer-transformed form. -/
theorem cfInt_bessel_M_euler {a b ν x : ℂ} (hx : 0 < x.re) (hxi : x.im = 0) (ha : 0 < a.re)
    (hν0 : -1 < ν.re) (hν1 : ν.re < 2 * (b - a).re - 3 / 2) :
    ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (ν / 2) * besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) *
        regularizedHGFun {b - a} {b} (-(t : ℂ)) =
      x ^ (ν / 2) * exp (-x) / Gamma (b - a) * kummerU a (a - b + ν + 2) x := by
  set r := x.re with hr
  have hxr : x = (r : ℂ) := Complex.ext (by simp [hr]) (by simp [hxi])
  have hx0 : x ≠ 0 := by rw [hxr]; exact ofReal_ne_zero.mpr hx.ne'
  set c := b - a with hc
  have hbc : b - c = a := by rw [hc]; ring
  set σ := ν.re with hσ
  set p := σ / 2 + 1 / 4 with hp
  have hcre : σ / 2 + 3 / 4 < c.re := by linarith
  have hc0 : 0 < c.re := by linarith
  have hGa := Gamma_ne_zero_of_re_pos ha
  have hGc := Gamma_ne_zero_of_re_pos hc0
  set K : ℝ → ℂ := fun t => (t : ℂ) ^ (ν / 2) * besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) with hK
  set E : ℝ → ℝ → ℂ := fun t s => kumDec_eulerKernel c b t s with hE
  set G : ℝ → ℝ → ℂ := fun t s => K t * E t s with hG
  have hKc : ContinuousOn K (Ioi 0) := cfInt_continuousOn_kernel ν hx0
  obtain ⟨CK, hCK⟩ := cfInt_exists_norm_kernel_le ν hx
  obtain ⟨CL, hCL⟩ := cfInt_laplace_rpow_le (r := σ) (p := p) hν0 (by rw [hp]; linarith)
  have hKb : ∀ t : ℝ, 0 < t → ‖K t‖ ≤ CK * (t ^ σ * (1 + t) ^ (-p)) := by
    intro t ht
    have := hCK t ht
    simp only [hK]; rw [hxr]; exact this
  have hEm : Measurable (Function.uncurry E) := by
    simp only [hE, kumDec_eulerKernel]
    fun_prop
  have hm : AEStronglyMeasurable (Function.uncurry G)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioo (0:ℝ) 1))) :=
    ((hKc.aestronglyMeasurable measurableSet_Ioi).comp_fst
      (ν := volume.restrict (Ioo (0:ℝ) 1))).mul hEm.aestronglyMeasurable
  set M2 := max 1 ((2:ℝ) ^ (-p)) with hM2
  have h1s : ∀ s ∈ Ioo (0:ℝ) 1, (1 + s) ^ (-p) ≤ M2 := by
    intro s hs
    rcases le_or_gt 0 (-p) with h | h
    · exact (Real.rpow_le_rpow (by linarith [hs.1]) (by linarith [hs.2]) h).trans
        (le_max_right _ _)
    · exact (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hs.1]) h.le).trans
        (le_max_left _ _)
  set w : ℝ → ℝ := fun s => s ^ (c.re - 1) * (1 - s) ^ (a.re - 1) with hw
  have hnE : ∀ s ∈ Ioo (0:ℝ) 1, ∀ t, ‖E t s‖ = Real.exp (-(t * s)) * w s := by
    intro s hs t
    simp only [hE, hw]; rw [kumDec_norm_eulerKernel c b hs, hbc]; ring
  have hinner : ∀ s ∈ Ioo (0:ℝ) 1, IntegrableOn (fun t => G t s) (Ioi 0) ∧
      ∫ t in Ioi 0, ‖G t s‖ ≤ CK * CL * M2 * (s ^ (p - σ - 1) * w s) := by
    intro s hs
    obtain ⟨hI, hle⟩ := hCL s hs.1
    have hw0 : 0 ≤ w s :=
      mul_nonneg (Real.rpow_nonneg hs.1.le _) (Real.rpow_nonneg (by linarith [hs.2]) _)
    have hCL0 : 0 ≤ CL := by
      have h0 : 0 ≤ ∫ t in Ioi 0, t ^ σ * (1 + t) ^ (-p) * Real.exp (-(s * t)) :=
        setIntegral_nonneg measurableSet_Ioi fun t ht => by
          have : (0:ℝ) < t := ht
          positivity
      have hpos : 0 < s ^ (p - σ - 1) * (1 + s) ^ (-p) := by
        have := hs.1; positivity
      exact (mul_nonneg_iff_of_pos_right hpos).mp (h0.trans hle)
    have hbd : ∀ t ∈ Ioi (0:ℝ), ‖G t s‖ ≤
        CK * w s * (t ^ σ * (1 + t) ^ (-p) * Real.exp (-(s * t))) := by
      intro t ht
      show ‖K t * E t s‖ ≤ _
      rw [norm_mul (K t), hnE s hs t]
      calc ‖K t‖ * (Real.exp (-(t * s)) * w s)
          ≤ (CK * (t ^ σ * (1 + t) ^ (-p))) * (Real.exp (-(t * s)) * w s) := by
            gcongr; exact hKb t ht
        _ = _ := by rw [mul_comm t s]; ring
    have hInt : IntegrableOn (fun t => G t s) (Ioi 0) := by
      refine (hI.const_mul (CK * w s)).mono' ?_ ?_
      · exact (hKc.aestronglyMeasurable measurableSet_Ioi).mul
          ((hEm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hbd t ht
    refine ⟨hInt, ?_⟩
    have hCK0 : 0 ≤ CK := by
      have h := (norm_nonneg _).trans (hKb 1 one_pos)
      exact (mul_nonneg_iff_of_pos_right (by positivity)).mp h
    calc ∫ t in Ioi 0, ‖G t s‖
        ≤ ∫ t in Ioi 0, CK * w s * (t ^ σ * (1 + t) ^ (-p) * Real.exp (-(s * t))) :=
          setIntegral_mono_on hInt.norm (hI.const_mul _) measurableSet_Ioi hbd
      _ = CK * w s * ∫ t in Ioi 0, t ^ σ * (1 + t) ^ (-p) * Real.exp (-(s * t)) :=
          integral_const_mul _ _
      _ ≤ CK * w s * (CL * (s ^ (p - σ - 1) * (1 + s) ^ (-p))) := by gcongr
      _ ≤ CK * w s * (CL * (s ^ (p - σ - 1) * M2)) := by
          have := hs.1
          gcongr; exact h1s s hs
      _ = _ := by ring
  have hmaj : IntegrableOn (fun s : ℝ => s ^ (p - σ - 1) * w s) (Ioo 0 1) := by
    have hB := Complex.betaIntegral_convergent (u := ((c.re + p - σ - 1 : ℝ) : ℂ))
      (v := ((a.re : ℝ) : ℂ)) (by simp; linarith) (by simpa using ha)
    have hB' := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hB.norm
    refine hB'.congr_fun (fun s hs => ?_) measurableSet_Ioo
    simp only [hw]
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hs.1,
      show (1 : ℂ) - s = ((1 - s : ℝ) : ℂ) by push_cast; ring,
      norm_cpow_eq_rpow_re_of_pos (by linarith [hs.2])]
    simp only [sub_re, ofReal_re, one_re]
    rw [show c.re + p - σ - 1 - 1 = (p - σ - 1) + (c.re - 1) by ring, Real.rpow_add hs.1]
    ring
  have hGi : Integrable (Function.uncurry G)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioo (0:ℝ) 1))) := by
    refine (integrable_prod_iff' hm).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact (hinner s hs).1
    · refine (hmaj.const_mul (CK * CL * M2)).mono' hm.norm.prod_swap.integral_prod_right' ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact (hinner s hs).2
  have hts : ∀ t ∈ Ioi (0:ℝ), ∫ s in Ioo 0 1, G t s =
      K t * (Gamma c * Gamma a * regularizedHGFun {c} {b} (-(t : ℂ))) := by
    intro t ht
    have h := kumDec_regularizedHGFun_neg_eq (a := c) (b := b) hc0 (by rw [hbc]; exact ha) t
    rw [hbc] at h
    simp only [hG]
    rw [integral_const_mul, h, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
    field_simp
    rfl
  have hst : ∀ s ∈ Ioo (0:ℝ) 1, ∫ t in Ioi 0, G t s =
      (s : ℂ) ^ (c - 1) * (1 - (s : ℂ)) ^ (a - 1) *
        (x ^ (ν / 2) * ((s : ℂ) ^ (-(ν + 1)) * exp (-x / s))) := by
    intro s hs
    have h := cfInt_laplace_kernel hν0 hx0 hs.1
    rw [← h, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [hG, hE, hK, kumDec_eulerKernel]
    rw [hbc, show -(t : ℂ) * s = -(s * t : ℂ) by ring]
    ring
  calc ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (ν / 2) * besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) *
        regularizedHGFun {c} {b} (-(t : ℂ))
      = ∫ t : ℝ in Ioi 0, (Gamma c * Gamma a)⁻¹ * ∫ s in Ioo 0 1, G t s := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
        rw [hts t ht]; simp only [hK]; field_simp
    _ = (Gamma c * Gamma a)⁻¹ * ∫ s in Ioo 0 1, ∫ t in Ioi 0, G t s := by
        rw [integral_const_mul, integral_integral_swap hGi]
    _ = (Gamma c * Gamma a)⁻¹ * (x ^ (ν / 2) * ∫ s in Ioo (0:ℝ) 1, (s : ℂ) ^ (c - 1) *
          (1 - (s : ℂ)) ^ (a - 1) * ((s : ℂ) ^ (-(ν + 1)) * exp (-x / s))) := by
        rw [setIntegral_congr_fun measurableSet_Ioo hst, ← integral_const_mul,
          ← integral_const_mul, ← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioo fun s _ => ?_
        ring
    _ = _ := by
        rw [cfInt_euler_subst_U hx ha, show ν + 2 - c = a - b + ν + 2 by rw [hc]; ring]
        field_simp

/-- The Gaussian cosine integral
`∫₀^∞ cos(2xt) e^{-st²} dt = (√π/2) s^{-1/2} e^{-x²/s}`, for `s > 0`. -/
theorem cfInt_integral_cos_gauss (x : ℝ) {s : ℝ} (hs : 0 < s) :
    ∫ t : ℝ in Ioi 0, Complex.cos (2 * x * t) * exp (-((t ^ 2 : ℝ) : ℂ) * s) =
      (Real.sqrt π : ℂ) / 2 * ((s : ℂ) ^ (-(1 / 2 : ℂ)) * exp (-(x : ℂ) ^ 2 / s)) := by
  set g : ℝ → ℝ := fun t => Real.cos (2 * x * t) * Real.exp (-(s * t ^ 2)) with hg
  have hfg : ∀ t : ℝ, Complex.cos (2 * x * t) * exp (-((t ^ 2 : ℝ) : ℂ) * s) = (g t : ℂ) := by
    intro t; simp only [hg]; push_cast; ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hfg t), integral_complex_ofReal]
  have habs : ∫ t, g |t| = 2 * ∫ t in Ioi 0, g t := integral_comp_abs
  have hgabs : (fun t => g |t|) = g := funext fun t => by
    simp only [hg]
    rcases abs_choice t with h | h <;> rw [h]
    simp [mul_neg, Real.cos_neg]
  rw [hgabs] at habs
  have hR : ∫ t in Ioi 0, g t = (∫ t, g t) / 2 := by linarith
  rw [hR]
  have hsplit : ∀ t : ℝ, (g t : ℂ) =
      (cexp (I * ((2 * x : ℝ) : ℂ) * t) * cexp (-(s : ℂ) * (t : ℂ) ^ 2) +
      cexp (I * ((-(2 * x) : ℝ) : ℂ) * t) * cexp (-(s : ℂ) * (t : ℂ) ^ 2)) / 2 := by
    intro t
    simp only [hg]
    push_cast
    rw [Complex.cos, show I * (2 * (x : ℂ)) * t = 2 * x * t * I by ring,
      show I * (-(2 * (x : ℂ))) * t = -(2 * x * t) * I by ring,
      show -((s : ℂ) * (t : ℂ) ^ 2) = -(s : ℂ) * (t : ℂ) ^ 2 by ring]
    ring
  have hI : ∀ T : ℝ, Integrable (fun t : ℝ => cexp (I * T * t) * cexp (-(s : ℂ) * (t : ℂ) ^ 2)) := by
    intro T
    refine (integrable_exp_neg_mul_sq hs).mono' (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun t => ?_)
    rw [norm_mul, Complex.norm_exp, Complex.norm_exp,
      show (-(s : ℂ) * (t : ℂ) ^ 2) = ((-s * t ^ 2 : ℝ) : ℂ) by push_cast; ring, ofReal_re,
      show I * (T : ℂ) * t = ((T * t : ℝ) : ℂ) * I by push_cast; ring]
    simp
  have hsc : 0 < (s : ℂ).re := by simpa using hs
  have h1 := fourierIntegral_gaussian hsc ((2 * x : ℝ) : ℂ)
  have h2 := fourierIntegral_gaussian hsc ((-(2 * x) : ℝ) : ℂ)
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have e1 : -((2 * x : ℝ) : ℂ) ^ 2 / (4 * (s : ℂ)) = -(x : ℂ) ^ 2 / s := by
    push_cast; field_simp; ring
  have e2 : -((-(2 * x) : ℝ) : ℂ) ^ 2 / (4 * (s : ℂ)) = -(x : ℂ) ^ 2 / s := by
    push_cast; field_simp; ring
  rw [e1] at h1
  rw [e2] at h2
  have hr : (π / s) ^ (1 / 2 : ℝ) = Real.sqrt π * s ^ (-(1 / 2) : ℝ) := by
    rw [Real.div_rpow (by positivity) hs.le, ← Real.sqrt_eq_rpow, Real.rpow_neg hs.le]; ring
  have hc := congrArg (fun r : ℝ => (r : ℂ)) hr
  rw [ofReal_cpow (by positivity), ofReal_mul, ofReal_cpow hs.le] at hc
  push_cast at hc
  rw [show (((∫ t, g t) / 2 : ℝ) : ℂ) = ((∫ t, g t : ℝ) : ℂ) / 2 by push_cast; ring,
    integral_complex_ofReal.symm, show (fun t : ℝ => (g t : ℂ)) = _ from funext hsplit, integral_div,
    integral_add (hI _) (hI _), h1, h2, hc]
  ring

/-- The cosine transform 13.10.12 in the Euler region `re (B - a) > 0`, before the Kummer
transformation of `U`. -/
theorem cfInt_cosine_euler {a x : ℝ} {B : ℂ} (hx : 0 < x) (ha : 1 / 2 < a) (hB : 0 < (B - a).re) :
    ∫ t : ℝ in Ioi 0, Complex.cos (2 * x * t) * regularizedHGFun {(a : ℂ)} {B} (-(t : ℂ) ^ 2) =
      (Real.sqrt π : ℂ) / (2 * Gamma (a : ℂ)) * exp (-(x : ℂ) ^ 2) *
        kummerU (B - a) (3 / 2 - a) ((x : ℂ) ^ 2) := by
  set A : ℂ := (a : ℂ) with hA
  have hA0 : 0 < A.re := by simp [hA]; linarith
  have hGA := Gamma_ne_zero_of_re_pos hA0
  have hGB := Gamma_ne_zero_of_re_pos hB
  have hBA : B - (B - A) = A := by ring
  set E : ℝ → ℝ → ℂ := fun t s => kumDec_eulerKernel A B (t ^ 2) s with hE
  set G : ℝ → ℝ → ℂ := fun t s => Complex.cos (2 * x * t) * E t s with hG
  have hEm : Measurable (Function.uncurry G) := by
    simp only [hG, hE, kumDec_eulerKernel]
    fun_prop
  have hm : AEStronglyMeasurable (Function.uncurry G)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioo (0:ℝ) 1))) :=
    hEm.aestronglyMeasurable
  set w : ℝ → ℝ := fun s => s ^ (a - 1) * (1 - s) ^ ((B - A).re - 1) with hw
  have hcos : ∀ t : ℝ, ‖Complex.cos (2 * x * t)‖ ≤ 1 := fun t => by
    rw [show (2 * (x : ℂ) * t) = ((2 * x * t : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos,
      norm_real, Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  have hnG : ∀ s ∈ Ioo (0:ℝ) 1, ∀ t : ℝ, ‖G t s‖ ≤ w s * Real.exp (-s * t ^ 2) := by
    intro s hs t
    simp only [hG, hE]
    rw [norm_mul, kumDec_norm_eulerKernel A B hs]
    have hw0 : 0 ≤ Real.exp (-(t ^ 2 * s)) * s ^ (A.re - 1) * (1 - s) ^ ((B - A).re - 1) := by
      have := hs.1; have : 0 < 1 - s := by linarith [hs.2]
      positivity
    calc ‖Complex.cos (2 * x * t)‖ * (Real.exp (-(t ^ 2 * s)) * s ^ (A.re - 1) *
          (1 - s) ^ ((B - A).re - 1))
        ≤ 1 * (Real.exp (-(t ^ 2 * s)) * s ^ (A.re - 1) * (1 - s) ^ ((B - A).re - 1)) := by
          gcongr; exact hcos t
      _ = _ := by simp only [hw, hA, ofReal_re]; ring_nf
  have hinner : ∀ s ∈ Ioo (0:ℝ) 1, IntegrableOn (fun t => G t s) (Ioi 0) ∧
      ∫ t in Ioi 0, ‖G t s‖ ≤ Real.sqrt π / 2 * (s ^ (-(1 / 2) : ℝ) * w s) := by
    intro s hs
    have hI := (integrable_exp_neg_mul_sq hs.1).integrableOn (s := Ioi (0:ℝ))
    have hInt : IntegrableOn (fun t => G t s) (Ioi 0) :=
      (hI.const_mul (w s)).mono' ((hEm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
        (Eventually.of_forall fun t => hnG s hs t)
    refine ⟨hInt, ?_⟩
    calc ∫ t in Ioi 0, ‖G t s‖ ≤ ∫ t in Ioi 0, w s * Real.exp (-s * t ^ 2) :=
          setIntegral_mono_on hInt.norm (hI.const_mul _) measurableSet_Ioi fun t _ => hnG s hs t
      _ = w s * (Real.sqrt (π / s) / 2) := by rw [integral_const_mul, integral_gaussian_Ioi]
      _ = _ := by
          rw [Real.sqrt_div' _ hs.1.le, Real.sqrt_eq_rpow s, Real.rpow_neg hs.1.le]; ring
  have hmaj : IntegrableOn (fun s : ℝ => s ^ (-(1 / 2) : ℝ) * w s) (Ioo 0 1) := by
    have hB' := Complex.betaIntegral_convergent (u := ((a - 1 / 2 : ℝ) : ℂ))
      (v := (((B - A).re : ℝ) : ℂ)) (by simp; linarith) (by simpa using hB)
    have hB'' := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hB'.norm
    refine hB''.congr_fun (fun s hs => ?_) measurableSet_Ioo
    simp only [hw]
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hs.1,
      show (1 : ℂ) - s = ((1 - s : ℝ) : ℂ) by push_cast; ring,
      norm_cpow_eq_rpow_re_of_pos (by linarith [hs.2])]
    simp only [sub_re, ofReal_re, one_re]
    rw [show a - 1 / 2 - 1 = -(1 / 2) + (a - 1) by ring, Real.rpow_add hs.1]
    ring
  have hGi : Integrable (Function.uncurry G)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioo (0:ℝ) 1))) := by
    refine (integrable_prod_iff' hm).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact (hinner s hs).1
    · refine (hmaj.const_mul (Real.sqrt π / 2)).mono' hm.norm.prod_swap.integral_prod_right' ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact (hinner s hs).2
  have hts : ∀ t : ℝ, ∫ s in Ioo 0 1, G t s =
      Complex.cos (2 * x * t) * (Gamma A * Gamma (B - A) *
        regularizedHGFun {A} {B} (-(t : ℂ) ^ 2)) := by
    intro t
    have h := kumDec_regularizedHGFun_neg_eq (a := A) (b := B) (t := t ^ 2) hA0 hB
    rw [show (((t ^ 2 : ℝ)) : ℂ) = (t : ℂ) ^ 2 by push_cast; ring] at h
    simp only [hG]
    rw [integral_const_mul, h, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
    field_simp
    rfl
  have hst : ∀ s ∈ Ioo (0:ℝ) 1, ∫ t in Ioi 0, G t s =
      (s : ℂ) ^ (A - 1) * (1 - (s : ℂ)) ^ ((B - A) - 1) *
        ((Real.sqrt π : ℂ) / 2 * ((s : ℂ) ^ (-(1 / 2 : ℂ)) * exp (-((x : ℂ) ^ 2) / s))) := by
    intro s hs
    have h := cfInt_integral_cos_gauss x hs.1
    rw [show -((x : ℂ) ^ 2) = -(x : ℂ) ^ 2 by ring, ← h, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [hG, hE, kumDec_eulerKernel]
    ring
  have hX : 0 < ((x : ℂ) ^ 2).re := by
    rw [← ofReal_pow, ofReal_re]; positivity
  have hsub := cfInt_euler_subst_U (a := B - A) (c := A) (ν := -(1 / 2)) hX hB
  rw [show -(-(1 / 2 : ℂ) + 1) = -(1 / 2) by ring,
    show -(1 / 2 : ℂ) + 2 - A = 3 / 2 - A by ring] at hsub
  calc ∫ t : ℝ in Ioi 0, Complex.cos (2 * x * t) * regularizedHGFun {A} {B} (-(t : ℂ) ^ 2)
      = ∫ t : ℝ in Ioi 0, (Gamma A * Gamma (B - A))⁻¹ * ∫ s in Ioo 0 1, G t s := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        rw [hts t]; field_simp
    _ = (Gamma A * Gamma (B - A))⁻¹ * ∫ s in Ioo 0 1, ∫ t in Ioi 0, G t s := by
        rw [integral_const_mul, integral_integral_swap hGi]
    _ = (Gamma A * Gamma (B - A))⁻¹ * ((Real.sqrt π : ℂ) / 2 * ∫ s in Ioo (0:ℝ) 1,
          (s : ℂ) ^ (A - 1) * (1 - (s : ℂ)) ^ ((B - A) - 1) *
            ((s : ℂ) ^ (-(1 / 2 : ℂ)) * exp (-((x : ℂ) ^ 2) / s))) := by
        rw [setIntegral_congr_fun measurableSet_Ioo hst, ← integral_const_mul,
          ← integral_const_mul, ← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioo fun s _ => ?_
        ring
    _ = _ := by
        rw [hsub]
        field_simp

end HankelKernel

open Set in
/-- A cosine transform of `𝐌`. For `a ≤ 1/2` the integral converges only conditionally,
which Lean's integral does not capture, so `1/2 < a` is required. -/
@[dlmf 13.10.E12]
theorem cosine_regularizedHGFun {a b x : ℝ} (hx : 0 < x) (ha : 1 / 2 < a) :
    ∫ t : ℝ in Set.Ioi 0,
        Complex.cos (2 * x * t) * regularizedHGFun {(a : ℂ)} {(b : ℂ)} (-(t : ℂ) ^ 2) =
      (Real.sqrt π : ℂ) / (2 * Gamma (a : ℂ)) * (x : ℂ) ^ (2 * (a : ℂ) - 1) *
        exp (-(x : ℂ) ^ 2) *
        kummerU (b - 1 / 2) (a + 1 / 2) (x ^ 2) := by
  set A : ℂ := (a : ℂ) with hA
  have hAre : A.re = a := by simp [hA]
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hX0 : (x : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ hx0
  set F : ℂ → ℂ := fun B => ∫ t : ℝ in Ioi 0,
    Complex.cos (2 * x * t) * regularizedHGFun {A} {B} (-(t : ℂ) ^ 2) with hF
  set H : ℂ → ℂ := fun B => (Real.sqrt π : ℂ) / (2 * Gamma A) * exp (-(x : ℂ) ^ 2) *
    kummerU (B - A) (3 / 2 - A) ((x : ℂ) ^ 2) with hH
  have hFH : ∀ B : ℂ, 0 < (B - A).re → F B = H B := fun B hB => cfInt_cosine_euler hx ha hB
  set ε := (a - 1 / 2) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hFd : Differentiable ℂ F := by
    refine differentiableOn_univ.mp (Complex.differentiableOn_integral_Ioi_of_locally_dominated
      (Φ := fun B t => Complex.cos (2 * x * t) * regularizedHGFun {A} {B} (-(t : ℂ) ^ 2))
      isOpen_univ 0 ?_ ?_ ?_)
    · intro B _
      exact ((by fun_prop : Continuous fun t : ℝ => Complex.cos (2 * x * t)).mul
        (continuous_regularizedConfluent.comp (by fun_prop :
          Continuous fun t : ℝ => (A, B, -(t : ℂ) ^ 2)))).aestronglyMeasurable
    · refine Eventually.of_forall fun t => ?_
      exact ((differentiable_regularizedConfluent_comp (A := fun _ => A) (B := fun w => w)
        (differentiable_const A) differentiable_id (-(t : ℂ) ^ 2)).const_mul _).differentiableOn
    · intro B₀ _
      obtain ⟨C, hC⟩ := exists_eventually_norm_regularizedHGFun_neg_le A B₀ hε0
      have htend : Tendsto (fun w : ℂ => (A, w)) (𝓝 B₀) (𝓝 (A, B₀)) :=
        ((continuous_const.prodMk continuous_id).tendsto B₀)
      refine ⟨_, htend.eventually hC, fun t => C * (1 + t ^ 2) ^ (-A.re + ε), ?_, ?_⟩
      · have hI := (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
          (r := 2 * (a - ε)) (by simp; rw [hε]; linarith)).integrableOn (s := Ioi (0:ℝ))
        refine IntegrableOn.congr_fun (Integrable.const_mul hI C) (fun t _ => ?_)
          measurableSet_Ioi
        simp only [Real.norm_eq_abs, sq_abs, hAre]
        congr 2; ring
      · refine Eventually.of_forall fun t y hy => ?_
        have h := hy (t ^ 2) (sq_nonneg t)
        rw [show (((t ^ 2 : ℝ)) : ℂ) = (t : ℂ) ^ 2 by push_cast; ring] at h
        have hc : ‖Complex.cos (2 * x * t)‖ ≤ 1 := by
          rw [show (2 * (x : ℂ) * t) = ((2 * x * t : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos,
            norm_real, Real.norm_eq_abs]
          exact Real.abs_cos_le_one _
        rw [norm_mul]
        calc ‖Complex.cos (2 * x * t)‖ * ‖regularizedHGFun {A} {y} (-(t : ℂ) ^ 2)‖
            ≤ 1 * (C * (1 + t ^ 2) ^ (-A.re + ε)) :=
              mul_le_mul hc h (norm_nonneg _) zero_le_one
          _ = _ := one_mul _
  have hHd : Differentiable ℂ H :=
    ((cfInt_differentiable_kummerU_fst (3 / 2 - A) hX0).comp
      (differentiable_id.sub_const A)).const_mul _
  have heq : F = H := by
    refine AnalyticOnNhd.eq_of_eventuallyEq (fun z _ => hFd.analyticAt z)
      (fun z _ => hHd.analyticAt z) (z₀ := A + 1) ?_
    have hopen : IsOpen {w : ℂ | 0 < (w - A).re} :=
      isOpen_lt continuous_const (continuous_re.comp (continuous_id.sub continuous_const))
    filter_upwards [hopen.mem_nhds (by simp : (0:ℝ) < (A + 1 - A).re)] with w hw
    exact hFH w hw
  have h := congrFun heq (b : ℂ)
  simp only [hF, hH] at h
  rw [h, kummerU_kummer_transform_all _ _ hX0,
    show (b : ℂ) - A - (3 / 2 - A) + 1 = b - 1 / 2 by ring,
    show (2 : ℂ) - (3 / 2 - A) = A + 1 / 2 by ring]
  have hp : ((x : ℂ) ^ 2) ^ (1 - (3 / 2 - A)) = (x : ℂ) ^ (2 * A - 1) := by
    rw [sq, mul_cpow_ofReal_nonneg hx.le hx.le, ← cpow_add _ _ hx0]; ring_nf
  rw [hp]
  ring

end DLMF.Confluent
end
end
