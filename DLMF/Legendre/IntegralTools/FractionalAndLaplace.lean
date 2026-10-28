/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.IntegralTools.Orthogonality

/-!
# Fractional and Laplace Legendre integral tools

Cut-plane fractional integration, segment substitutions and Laplace estimates used by Legendre
integral formulas.

Source references and common attribution are retained in
`DLMF.Legendre.IntegralTools`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Legendre

open DLMF.OrthogonalPolynomials

/-! ### A fractional integral on the cut plane -/

/-- `z s` lies in the cut plane for `z` in the cut plane and `s ∈ [0,1]`. -/
theorem legInt_mul_mem_cutPlane {z : ℂ} (hz : z ∈ cutPlane) {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    z * s ∈ cutPlane := by
  have h := starConvex_zero_cutPlane hz (by linarith [hs.2] : (0:ℝ) ≤ 1 - s) hs.1 (by ring)
  simpa [Complex.real_smul, mul_comm] using h

/-- `z ↦ ∫_0^1 w(s) F(z s) ds` is analytic on the cut plane when `F` is and `w` is integrable. -/
theorem legInt_analyticOnNhd_integral {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F cutPlane) {w : ℝ → ℂ}
    (hw : IntervalIntegrable w volume 0 1) :
    AnalyticOnNhd ℂ (fun z => ∫ s : ℝ in (0:ℝ)..1, w s * F (z * s)) cutPlane := by
  refine DifferentiableOn.analyticOnNhd (fun z0 hz0 => ?_) isOpen_cutPlane
  refine DifferentiableAt.differentiableWithinAt ?_
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_cutPlane z0 hz0
  set ε := r/2 with hε
  have hεpos : 0 < ε := by positivity
  have hcb : Metric.closedBall z0 ε ⊆ cutPlane := fun z hz =>
    hball (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith)))
  set K := (fun p : ℂ × ℝ => p.1 * p.2) '' (Metric.closedBall z0 ε ×ˢ Icc (0:ℝ) 1)
  have hK : IsCompact K := ((isCompact_closedBall z0 ε).prod isCompact_Icc).image (by fun_prop)
  have hKsub : K ⊆ cutPlane := by
    rintro _ ⟨⟨z, s⟩, ⟨hz, hs⟩, rfl⟩
    exact legInt_mul_mem_cutPlane (hcb hz) hs
  have hdF : ContinuousOn (deriv F) cutPlane := (hF.deriv).continuousOn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hdF.mono hKsub)
  have hIcc : ∀ s ∈ uIoc (0:ℝ) 1, s ∈ Icc (0:ℝ) 1 := fun s hs => by
    rw [uIoc_of_le zero_le_one] at hs; exact ⟨hs.1.le, hs.2⟩
  have hcont : ∀ z ∈ cutPlane, ContinuousOn (fun s : ℝ => F (z * s)) (uIcc 0 1) := by
    intro z hz s hs
    rw [uIcc_of_le zero_le_one] at hs
    exact (ContinuousAt.comp (g := F) (f := fun s : ℝ => z * (s:ℂ))
      (hF _ (legInt_mul_mem_cutPlane hz hs)).continuousAt (by fun_prop)).continuousWithinAt
  have hcont' : ContinuousOn (fun s : ℝ => deriv F (z0 * s) * s) (uIcc 0 1) := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    exact ((ContinuousAt.comp (g := deriv F) (f := fun s : ℝ => z0 * (s:ℂ))
      (hF.deriv _ (legInt_mul_mem_cutPlane hz0 hs)).continuousAt (by fun_prop)).mul
      (continuous_ofReal.continuousAt)).continuousWithinAt
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z s => w s * F (z * s)) (F' := fun z s => w s * (deriv F (z * s) * s))
    (x₀ := z0) (bound := fun s => ‖w s‖ * C) (μ := volume) (a := 0) (b := 1) (Metric.ball_mem_nhds z0 hεpos)
    (by
      filter_upwards [isOpen_cutPlane.mem_nhds hz0] with z hz
      exact (hw.mul_continuousOn (hcont z hz)).def'.aestronglyMeasurable)
    (hw.mul_continuousOn (hcont z0 hz0))
    ((hw.mul_continuousOn hcont').def'.aestronglyMeasurable)
    (Eventually.of_forall fun s hs z hz => by
      have hs' := hIcc s hs
      have hzK : z * s ∈ K := ⟨⟨z, s⟩, ⟨Metric.ball_subset_closedBall hz, hs'⟩, rfl⟩
      rw [norm_mul, norm_mul]
      gcongr
      calc ‖deriv F (z * s)‖ * ‖(s:ℂ)‖ ≤ C * 1 := by
            gcongr
            · exact le_trans (norm_nonneg _) (hC _ hzK)
            · exact hC _ hzK
            · rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hs'.1]; exact hs'.2
        _ = C := mul_one C)
    (hw.norm.mul_const C)
    (Eventually.of_forall fun s hs z hz => by
      have hs' := hIcc s hs
      have hzc : z * s ∈ cutPlane := legInt_mul_mem_cutPlane (hcb (Metric.ball_subset_closedBall hz)) hs'
      have hd := ((hF _ hzc).differentiableAt.hasDerivAt).comp z (hasDerivAt_mul_const (s:ℂ))
      exact hd.const_mul (w s))
  exact h.2.differentiableAt

/-- DLMF 15.6.8 with `d = 1` on the cut plane:
`Γ(μ) 𝐅(a,b;1+μ;z) = ∫_0^1 (1-s)^{μ-1} 𝐅(a,b;1;zs) ds`. -/
theorem legInt_fractional_cutPlane (a b : ℂ) {μ : ℂ} (hμ : 0 < μ.re) {z : ℂ} (hz : z ∈ cutPlane) :
    Gamma μ * regularizedGaussHG a b (1+μ) z =
      ∫ s : ℝ in (0:ℝ)..1, (1-(s:ℂ))^(μ-1) * regularizedGaussHG a b 1 (z * s) := by
  have hw : IntervalIntegrable (fun s : ℝ => (1-(s:ℂ))^(μ-1)) volume 0 1 := by
    simpa using betaIntegral_convergent (u := 1) (by norm_num) hμ
  refine eqOn_cutPlane_of_eqOn_disk (f := fun z => Gamma μ * regularizedGaussHG a b (1+μ) z)
    (fun z hz => analyticAt_const.mul (analyticOnNhd_regularizedGaussHG a b _ z hz))
    (legInt_analyticOnNhd_integral (analyticOnNhd_regularizedGaussHG a b 1) hw) (fun z hz => ?_) hz
  have hfr := fractional_integral (a := a) (b := b) (c := 1+μ) (d := 1) (by norm_num)
    (by simpa using hμ) hz
  rw [show 1+μ-1 = μ by ring] at hfr
  rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz, hfr, ← mul_assoc,
    mul_one_div_cancel (Gamma_ne_zero_of_re_pos hμ), one_mul]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le zero_le_one] at hs
  have hzs : ‖z*s‖ < 1 := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    calc ‖z‖*s ≤ ‖z‖*1 := by gcongr; exact hs.2
      _ < 1 := by rw [mul_one]; exact hz
  rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hzs, sub_self, cpow_zero, mul_one, mul_comm]

/-- Complex powers of a positive real as exponentials of the real logarithm. -/
theorem legInt_cpow_ofReal {r : ℝ} (hr : 0 < r) (c : ℂ) :
    ((r:ℝ):ℂ)^c = exp (Real.log r * c) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.2 hr.ne'), ofReal_log hr.le]

/-- Order-derivative relation `(1-z²) 𝑸' + μ z 𝑸^μ_ν = (ν+μ+1) (z²-1)^{1/2} 𝑸^{μ+1}_ν`. -/
theorem legInt_olverQ_order_deriv (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    (1-z^2)*deriv (olverQ ν μ) z + μ*z*olverQ ν μ z =
      (ν+μ+1)*legendreBranchPower 1 z*olverQ ν (μ+1) z := by
  have h7 := olverQ_recurrence_7 ν μ hz
  have h4 := olverQ_recurrence_4 ν μ hz
  linear_combination h4 + (ν+μ+1)*h7

/-- `g_k(z) = (z²-1)^{k/2} Q^{-k}_ν(z)`. -/
noncomputable def legInt_g (ν : ℂ) (k : ℕ) (z : ℂ) : ℂ :=
  legendreBranchPower k z * associatedQ ν (-k) z

/-- `g_0 = Q_ν`. -/
theorem legInt_g_zero (ν z : ℂ) : legInt_g ν 0 z = associatedQ ν 0 z := by
  simp [legInt_g, legendreBranchPower]

/-- `g_{k+1}' = g_k` on the principal sheet, for `ν ≠ k`. -/
theorem legInt_hasDerivAt_g (ν : ℂ) (k : ℕ) (hk : ν ≠ k) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    HasDerivAt (legInt_g ν (k+1)) (legInt_g ν k z) z := by
  set C : ℂ := exp (-((k+1:ℕ):ℂ)*π*I)*Gamma (ν+-((k+1:ℕ):ℂ)+1)
  have hQ := ((olverQ_analytic ν (-((k+1:ℕ):ℂ)) z hz).differentiableAt.hasDerivAt).const_mul C
  have h := (hasDerivAt_legendreBranchPower ((k+1:ℕ):ℂ) hz).mul hQ
  have e : legInt_g ν (k+1) = fun w => legendreBranchPower ((k+1:ℕ):ℂ) w *
      (C * olverQ ν (-((k+1:ℕ):ℂ)) w) := by
    funext w; simp only [legInt_g, associatedQ, C]
  rw [e]
  refine h.congr_deriv ?_
  have L := legInt_olverQ_order_deriv ν (-((k+1:ℕ):ℂ)) hz
  rw [show -((k+1:ℕ):ℂ)+1 = -(k:ℂ) by push_cast; ring] at L
  have hz2 := legendre_sq_sub_one_ne_zero hz
  have hb : legendreBranchPower ((k+1:ℕ):ℂ) z = legendreBranchPower k z * legendreBranchPower 1 z := by
    rw [legendreBranchPower_mul]; push_cast; ring_nf
  have hb2 : legendreBranchPower 1 z * legendreBranchPower 1 z = z^2-1 := by
    rw [legendreBranchPower_mul, show (1:ℂ)+1 = 2 by norm_num, legendreBranchPower_two hz]
  have hνk : ν - k ≠ 0 := sub_ne_zero.mpr hk
  have hG : Gamma (ν + -(k:ℂ) + 1) = (ν-k) * Gamma (ν-(k+1)+1) := by
    rw [show ν-(k+1)+1 = ν-k by ring, show ν + -(k:ℂ) + 1 = (ν-k)+1 by ring, Gamma_add_one _ hνk]
  have hE : exp (-((k+1:ℕ):ℂ)*π*I) = -exp (-(k:ℂ)*π*I) := by
    rw [show -((k+1:ℕ):ℂ)*π*I = -(k:ℂ)*π*I + (-(π*I)) by push_cast; ring, exp_add, exp_neg,
      exp_pi_mul_I]; ring
  simp only [legInt_g, associatedQ, C, hE, hb]
  push_cast at hG L ⊢
  have hD : deriv (olverQ ν (-((k:ℂ)+1))) z = -((ν-k)*legendreBranchPower 1 z*olverQ ν (-k) z
      + ((k:ℂ)+1)*z*olverQ ν (-((k:ℂ)+1)) z)/(z^2-1) := by
    field_simp; linear_combination -L
  rw [hG, hD]
  field_simp
  rw [show ν + -((k:ℂ)+1) + 1 = ν - (k+1) + 1 by ring]
  linear_combination (legendreBranchPower k z * (ν-k) * olverQ ν (-k) z * Gamma (ν-(k+1)+1)) * hb2

/-- Continuity of `g_k` on the principal sheet. -/
theorem legInt_continuousAt_g (ν : ℂ) (k : ℕ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    ContinuousAt (legInt_g ν k) z := by
  have h1 := (hasDerivAt_legendreBranchPower (k:ℂ) hz).continuousAt
  have h2 := ((olverQ_analytic ν (-(k:ℂ)) z hz).continuousAt).const_mul
    (exp (-(k:ℂ)*π*I)*Gamma (ν+-(k:ℂ)+1))
  have e : legInt_g ν k = fun w => legendreBranchPower (k:ℂ) w *
      (exp (-(k:ℂ)*π*I)*Gamma (ν+-(k:ℂ)+1) * olverQ ν (-(k:ℂ)) w) := by
    funext w; simp only [legInt_g, associatedQ]
  rw [e]; exact h1.mul h2

/-- `g_{k+1}(R) → 0` as `R → ∞` when `k < Re ν`. -/
theorem legInt_tendsto_g (ν : ℂ) (k : ℕ) (hk : (k:ℝ) < ν.re) :
    Tendsto (fun R : ℝ => legInt_g ν (k+1) R) atTop (𝓝 0) := by
  set w : ℂ := ν + -((k+1:ℕ):ℂ) + 1 with hw
  have hwre : 0 < w.re := by rw [hw]; simp; linarith
  set K : ℂ := exp (-((k+1:ℕ):ℂ)*π*I)*Gamma w*(Real.sqrt π/(2^(ν+1)))
  set A := (ν+-((k+1:ℕ):ℂ)+2)/2
  set B := (ν+-((k+1:ℕ):ℂ)+1)/2
  have e : ∀ R : ℝ, legInt_g ν (k+1) R =
      K * ((R:ℂ)^w)⁻¹ * regularizedGaussHG A B (ν+3/2) (1/(R:ℂ)^2) := by
    intro R
    have hb : legendreBranchPower ((k+1:ℕ):ℂ) R * legendreBranchPower (-((k+1:ℕ):ℂ)) R = 1 := by
      rw [legendreBranchPower_mul, add_neg_cancel]; simp [legendreBranchPower]
    simp only [legInt_g, associatedQ, olverQ, K, A, B, hw]
    rw [div_eq_mul_inv (Real.sqrt π * legendreBranchPower _ _), mul_inv]
    linear_combination (exp (-((k+1:ℕ):ℂ)*π*I)*Gamma (ν+-((k+1:ℕ):ℂ)+1)*Real.sqrt π *
      (2^(ν+1))⁻¹ * ((R:ℂ)^(ν+-((k+1:ℕ):ℂ)+1))⁻¹ *
      regularizedGaussHG ((ν+-((k+1:ℕ):ℂ)+2)/2) ((ν+-((k+1:ℕ):ℂ)+1)/2) (ν+3/2) (1/(R:ℂ)^2)) * hb
  simp_rw [e]
  have h1 : Tendsto (fun R : ℝ => ((R:ℂ)^w)⁻¹) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := (tendsto_rpow_atTop hwre).inv_tendsto_atTop
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    rw [norm_inv, norm_cpow_eq_rpow_re_of_pos hR]; rfl
  have h2 : Tendsto (fun R : ℝ => regularizedGaussHG A B (ν+3/2) (1/(R:ℂ)^2)) atTop
      (𝓝 (regularizedGaussHG A B (ν+3/2) 0)) := by
    have hc := (analyticAt_regularizedGaussHG A B (ν+3/2) zero_mem_cutPlane).continuousAt
    have ht : Tendsto (fun R : ℝ => 1/(R:ℂ)^2) atTop (𝓝 0) := by
      have := ((continuous_ofReal.tendsto 0).comp
        (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (two_ne_zero (α := ℕ)))))
      simp only [ofReal_zero] at this
      refine this.congr fun R => ?_
      simp [Function.comp]
    exact hc.tendsto.comp ht
  simpa using (tendsto_const_nhds (x := K)).mul h1 |>.mul h2

/-- Real points `t > 1` give `t - 1` in the slit plane. -/
theorem legInt_one_lt_mem {t : ℝ} (ht : 1 < t) : (t:ℂ)-1 ∈ slitPlane :=
  Or.inl (by simp; linarith)

/-- `∫_x^∞ g_j = -g_{j+1}(x)` for `x > 1` and `j < Re ν`. -/
theorem legInt_hasIntegralAtTop_g (ν : ℂ) (j : ℕ) (hj : (j:ℝ) < ν.re) {x : ℝ} (hx : 1 < x) :
    HasIntegralAtTop (fun t : ℝ => legInt_g ν j t) x (-legInt_g ν (j+1) x) := by
  have hne : ν ≠ j := fun h => by rw [h] at hj; simp at hj
  have hFTC : ∀ R, x ≤ R → ∫ t in x..R, legInt_g ν j t = legInt_g ν (j+1) R - legInt_g ν (j+1) x := by
    intro R hR
    have hsub : ∀ t ∈ uIcc x R, 1 < t := fun t ht => by
      rw [uIcc_of_le hR] at ht; linarith [ht.1]
    have hco : ContinuousOn (fun t : ℝ => legInt_g ν j t) (uIcc x R) := fun t ht =>
      ((legInt_continuousAt_g ν j (legInt_one_lt_mem (hsub t ht))).comp
        continuous_ofReal.continuousAt).continuousWithinAt
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => legInt_g ν (j+1) t)
      (fun t ht => (legInt_hasDerivAt_g ν j hne (legInt_one_lt_mem (hsub t ht))).comp_ofReal)
      (hco.intervalIntegrable)
  have h := (legInt_tendsto_g ν j hj).sub_const (legInt_g ν (j+1) x)
  rw [zero_sub] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop x] with R hR
  exact (hFTC R hR).symm

/-- Iterated tails of `Q_ν`. -/
theorem legInt_iterate_Q (ν : ℂ) (k : ℕ) (hk : (k:ℝ)-1 < ν.re) {x : ℝ} (hx : 1 < x) :
    ((fun f : ℝ → ℂ => fun x => improperAtTop f x)^[k]) (fun x : ℝ => associatedQ ν 0 x) x =
      (-1)^k * legInt_g ν k x := by
  induction k generalizing x with
  | zero => simp [legInt_g_zero]
  | succ k ih =>
    have hk' : (k:ℝ) < ν.re := by push_cast at hk; linarith
    rw [Function.iterate_succ_apply']
    show improperAtTop _ x = _
    have h := (legInt_hasIntegralAtTop_g ν k hk' hx).const_mul ((-1:ℂ)^k)
    have h' : HasIntegralAtTop (((fun f : ℝ → ℂ => fun x => improperAtTop f x)^[k])
        (fun x : ℝ => associatedQ ν 0 x)) x ((-1)^k * -legInt_g ν (k+1) x) := by
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop x] with R hR
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hR] at ht
      exact (ih (by linarith) (by linarith [ht.1])).symm
    rw [improperAtTop, h'.limUnder_eq]
    ring

/-- Points of the segment from `z` to `2` stay on the principal sheet. -/
theorem legInt_seg_two_mem {z : ℂ} (hz : z-1 ∈ slitPlane) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    (z + t*(2-z)) - 1 ∈ slitPlane := by
  have h := starConvex_one_slitPlane hz ht.1 (by linarith [ht.2] : (0:ℝ) ≤ 1 - t) (by ring)
  convert h using 1
  simp only [Complex.real_smul, mul_one, ofReal_sub, ofReal_one]
  ring

/-- Iterated segment-plus-tail integrals of `Q_ν`. -/
theorem legInt_iterate_Qc (ν : ℂ) (k : ℕ) (hk : (k:ℝ)-1 < ν.re) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    ((fun f : ℂ → ℂ => fun z => segmentIntegral f z 2+improperAtTop (fun t : ℝ => f t) 2)^[k])
      (associatedQ ν 0) z = (-1)^k * legInt_g ν k z := by
  induction k generalizing z with
  | zero => simp [legInt_g_zero]
  | succ k ih =>
    have hk' : (k:ℝ) < ν.re := by push_cast at hk; linarith
    have hne : ν ≠ k := fun h => by rw [h] at hk'; simp at hk'
    have ih' := fun {w : ℂ} (hw : w-1 ∈ slitPlane) => ih (by linarith) (z := w) hw
    rw [Function.iterate_succ_apply']
    show segmentIntegral _ z 2 + improperAtTop _ 2 = _
    -- the tail
    have htail : improperAtTop (fun t : ℝ => ((fun f : ℂ → ℂ => fun z =>
        segmentIntegral f z 2+improperAtTop (fun t : ℝ => f t) 2)^[k]) (associatedQ ν 0) t) 2 =
        (-1)^k * -legInt_g ν (k+1) 2 := by
      have h := (legInt_hasIntegralAtTop_g ν k hk' (by norm_num : (1:ℝ) < 2)).const_mul ((-1:ℂ)^k)
      refine (h.congr' ?_).limUnder_eq
      · filter_upwards [eventually_ge_atTop 2] with R hR
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [uIcc_of_le hR] at ht
        exact (ih' (legInt_one_lt_mem (by linarith [ht.1]))).symm
    -- the segment
    have hseg : segmentIntegral (((fun f : ℂ → ℂ => fun z =>
        segmentIntegral f z 2+improperAtTop (fun t : ℝ => f t) 2)^[k]) (associatedQ ν 0)) z 2 =
        (-1)^k * (legInt_g ν (k+1) 2 - legInt_g ν (k+1) z) := by
      rw [segmentIntegral]
      have hc : (∫ t : ℝ in (0:ℝ)..1, ((fun f : ℂ → ℂ => fun z =>
          segmentIntegral f z 2+improperAtTop (fun t : ℝ => f t) 2)^[k]) (associatedQ ν 0)
            (z + t*(2-z))) = ∫ t : ℝ in (0:ℝ)..1, (-1)^k * legInt_g ν k (z + t*(2-z)) := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [uIcc_of_le zero_le_one] at ht
        exact ih' (legInt_seg_two_mem hz ht)
      rw [hc, intervalIntegral.integral_const_mul, mul_left_comm]
      congr 1
      rw [← intervalIntegral.integral_const_mul]
      have hd : ∀ t ∈ uIcc (0:ℝ) 1, HasDerivAt (fun t : ℝ => legInt_g ν (k+1) (z + t*(2-z)))
          ((2-z) * legInt_g ν k (z + t*(2-z))) t := by
        intro t ht
        rw [uIcc_of_le zero_le_one] at ht
        have hl : HasDerivAt (fun t : ℝ => z + (t:ℂ)*(2-z)) (1*(2-z)) t :=
          ((hasDerivAt_id t).ofReal_comp.mul_const (2-z)).const_add z
        rw [one_mul] at hl
        exact ((legInt_hasDerivAt_g ν k hne (legInt_seg_two_mem hz ht)).comp t hl).congr_deriv
          (mul_comm _ _)
      have hco : ContinuousOn (fun t : ℝ => (2-z) * legInt_g ν k (z + t*(2-z))) (uIcc 0 1) :=
        fun t ht => by
          have ht' := ht; rw [uIcc_of_le zero_le_one] at ht'
          refine ContinuousAt.continuousWithinAt (ContinuousAt.mul continuousAt_const ?_)
          exact ContinuousAt.comp (g := legInt_g ν k)
            (legInt_continuousAt_g ν k (legInt_seg_two_mem hz ht')) (by fun_prop)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hco.intervalIntegrable]
      simp only [ofReal_one, one_mul, ofReal_zero, zero_mul, add_zero, add_sub_cancel]
    rw [htail, hseg]
    ring

/-- The Laplace kernel `w(θ) = x + √(x²-1) cos θ`, positive for `x > 1`. -/
theorem legInt_laplace_pos {x : ℝ} (hx : 1 < x) (θ : ℝ) :
    0 < x + Real.sqrt (x^2-1) * Real.cos θ := by
  have hs : Real.sqrt (x^2-1) < x := by
    rw [Real.sqrt_lt' (by linarith)]; linarith
  have hs0 := Real.sqrt_nonneg (x^2-1)
  nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]

/-- Fourier moments of powers of the Laplace kernel. -/
noncomputable def legInt_L (ν : ℂ) (x : ℝ) (m : ℕ) : ℂ :=
  ∫ θ : ℝ in (0:ℝ)..π, (((x + Real.sqrt (x^2-1) * Real.cos θ : ℝ)) : ℂ)^ν * Real.cos (m*θ)

/-- Continuity of the integrand of `legInt_L`. -/
theorem legInt_cont_L (ν : ℂ) {x : ℝ} (hx : 1 < x) (c : ℝ) :
    Continuous fun θ : ℝ => (((x + Real.sqrt (x^2-1) * Real.cos θ : ℝ)) : ℂ)^ν * Real.cos (c*θ) := by
  refine Continuous.mul ?_ (by fun_prop)
  refine continuous_iff_continuousAt.2 fun θ => ?_
  refine ContinuousAt.cpow (by fun_prop) continuousAt_const ( ?_)
  exact ofReal_mem_slitPlane.2 (legInt_laplace_pos hx θ)

/-- The integration-by-parts recurrence
`(ν+m+2) s L_{m+2} + 2(m+1) x L_{m+1} + (m-ν) s L_m = 0`, `s = √(x²-1)`. -/
theorem legInt_L_rec (ν : ℂ) {x : ℝ} (hx : 1 < x) (m : ℕ) :
    (ν+m+2) * Real.sqrt (x^2-1) * legInt_L ν x (m+2) + 2*(m+1)*x*legInt_L ν x (m+1) +
      (m-ν) * Real.sqrt (x^2-1) * legInt_L ν x m = 0 := by
  set s := Real.sqrt (x^2-1)
  set w : ℝ → ℝ := fun θ => x + s * Real.cos θ with hw
  have hwpos : ∀ θ, 0 < w θ := legInt_laplace_pos hx
  -- derivative of `w^{ν+1} sin((m+1)θ)`
  have hd : ∀ θ ∈ uIcc (0:ℝ) π, HasDerivAt (fun θ : ℝ => ((w θ : ℝ):ℂ)^(ν+1) * Real.sin ((m+1)*θ))
      ((ν+1) * ((w θ:ℝ):ℂ)^ν * (-(s * Real.sin θ)) * Real.sin ((m+1)*θ) +
        ((w θ:ℝ):ℂ)^(ν+1) * (((m:ℝ)+1) * Real.cos ((m+1)*θ))) θ := by
    intro θ _
    have h1 : HasDerivAt (fun θ : ℝ => ((w θ:ℝ):ℂ)) (((-(s * Real.sin θ)):ℝ):ℂ) θ := by
      have := ((Real.hasDerivAt_cos θ).const_mul s).const_add x
      simpa [hw] using this.ofReal_comp
    have h2 := (hasStrictDerivAt_cpow_const (c := ν+1)
      (ofReal_mem_slitPlane.2 (hwpos θ))).hasDerivAt.comp θ h1
    have h3 : HasDerivAt (fun θ : ℝ => ((Real.sin ((m+1)*θ) : ℝ):ℂ))
        ((((m:ℝ)+1) * Real.cos ((m+1)*θ) : ℝ):ℂ) θ := by
      have := (Real.hasDerivAt_sin ((m+1)*θ)).comp θ ((hasDerivAt_id θ).const_mul ((m:ℝ)+1))
      simpa [mul_comm] using this.ofReal_comp
    rw [add_sub_cancel_right] at h2
    exact (h2.mul h3).congr_deriv (by simp only [Function.comp_apply]; push_cast; ring)
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
    refine (Continuous.intervalIntegrable ?_ _ _)
    refine Continuous.add (Continuous.mul (Continuous.mul (Continuous.mul continuous_const ?_)
      (by fun_prop)) (by fun_prop)) (Continuous.mul ?_ (by fun_prop))
    · refine continuous_iff_continuousAt.2 fun θ => ?_
      exact ContinuousAt.cpow (by fun_prop) continuousAt_const ( (ofReal_mem_slitPlane.2 (hwpos θ)))
    · refine continuous_iff_continuousAt.2 fun θ => ?_
      exact ContinuousAt.cpow (by fun_prop) continuousAt_const ( (ofReal_mem_slitPlane.2 (hwpos θ))))
  have hsin0 : Real.sin ((m+1)*π) = 0 := by
    rw [show ((m:ℝ)+1)*π = ((m+1:ℕ):ℝ)*π by push_cast; ring]; exact Real.sin_nat_mul_pi _
  simp only [mul_zero, Real.sin_zero, ofReal_zero, hsin0, mul_zero, sub_zero] at hint
  -- pointwise identity
  have hpt : ∀ θ : ℝ, (ν+1) * ((w θ:ℝ):ℂ)^ν * (-(s * Real.sin θ)) * Real.sin ((m+1)*θ) +
        ((w θ:ℝ):ℂ)^(ν+1) * (((m:ℝ)+1) * Real.cos ((m+1)*θ)) =
      (1/2:ℂ) * ((ν+m+2) * s * (((w θ:ℝ):ℂ)^ν * Real.cos (((m+2:ℕ):ℝ)*θ)) +
        2*(m+1)*x*(((w θ:ℝ):ℂ)^ν * Real.cos (((m+1:ℕ):ℝ)*θ)) +
        (m-ν) * s * (((w θ:ℝ):ℂ)^ν * Real.cos (((m:ℕ):ℝ)*θ))) := by
    intro θ
    have hp : ((w θ:ℝ):ℂ)^(ν+1) = ((w θ:ℝ):ℂ)^ν * (x + s * Real.cos θ) := by
      rw [cpow_add _ _ (ofReal_ne_zero.2 (hwpos θ).ne'), cpow_one]; simp [hw]
    have e1 : Real.cos (((m+2:ℕ):ℝ)*θ) = Real.cos ((m+1)*θ) * Real.cos θ -
        Real.sin ((m+1)*θ) * Real.sin θ := by
      rw [← Real.cos_add]; push_cast; ring_nf
    have e2 : Real.cos (((m:ℕ):ℝ)*θ) = Real.cos ((m+1)*θ) * Real.cos θ +
        Real.sin ((m+1)*θ) * Real.sin θ := by
      rw [← Real.cos_sub]; ring_nf
    rw [hp, e1, e2]; push_cast; ring
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ), intervalIntegral.integral_const_mul] at hint
  have hc := fun k : ℕ => (legInt_cont_L ν hx (k:ℝ)).intervalIntegrable (μ := volume) 0 π
  rw [intervalIntegral.integral_add ((((hc _).const_mul _)).add ((hc _).const_mul _))
    ((hc _).const_mul _), intervalIntegral.integral_add ((hc _).const_mul _) ((hc _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hint
  simp only [legInt_L] at hint ⊢
  push_cast at hint ⊢
  linear_combination 2 * hint

/-- The Heine kernel `W(t) = x + √(x²-1) cosh t`. -/
noncomputable def legInt_W (x t : ℝ) : ℝ := x + Real.sqrt (x^2-1) * Real.cosh t

/-- Positivity of the Heine kernel. -/
theorem legInt_W_pos {x : ℝ} (hx : 1 < x) (t : ℝ) : 0 < legInt_W x t := by
  unfold legInt_W
  have := Real.sqrt_nonneg (x^2-1); have := Real.one_le_cosh t
  nlinarith

/-- Continuity of `1/W^n`. -/
theorem legInt_cont_W_pow {x : ℝ} (hx : 1 < x) (n : ℕ) :
    Continuous fun t => 1 / legInt_W x t ^ n := by
  unfold legInt_W
  exact Continuous.div continuous_const (by fun_prop)
    (fun t => pow_ne_zero _ (legInt_W_pos hx t).ne')

/-- `W(t) → ∞` as `t → ∞`. -/
theorem legInt_W_tendsto {x : ℝ} (hx : 1 < x) : Tendsto (legInt_W x) atTop atTop := by
  have hs : 0 < Real.sqrt (x^2-1) := Real.sqrt_pos.2 (by nlinarith)
  refine tendsto_atTop_mono (fun t => ?_)
    ((Real.tendsto_exp_atTop.const_mul_atTop (by positivity : 0 < Real.sqrt (x^2-1)/2)))
  unfold legInt_W
  rw [Real.cosh_eq]
  have := Real.exp_pos (-t)
  nlinarith

/-- The `n = 0` Heine integral: `∫_0^∞ dt/W = ½ log((x+1)/(x-1))`. -/
theorem legInt_heine_zero {x : ℝ} (hx : 1 < x) :
    Tendsto (fun R => ∫ t in (0:ℝ)..R, 1 / legInt_W x t ^ 1) atTop
      (𝓝 (Real.log ((x+1)/(x-1)) / 2)) := by
  set s := Real.sqrt (x^2-1) with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 (by nlinarith)
  have hss : s^2 = x^2-1 := Real.sq_sqrt (by nlinarith)
  set F : ℝ → ℝ := fun t => Real.log (s * Real.exp t + x - 1) - Real.log (s * Real.exp t + x + 1)
  have hA : ∀ t, 0 < s * Real.exp t + x - 1 := fun t => by
    have := Real.exp_pos t; nlinarith
  have hB : ∀ t, 0 < s * Real.exp t + x + 1 := fun t => by linarith [hA t]
  have hd : ∀ t, HasDerivAt F (1 / legInt_W x t ^ 1) t := by
    intro t
    have he := Real.hasDerivAt_exp t
    have h1 := ((((he.const_mul s).add_const x).sub_const 1).log (hA t).ne')
    have h2 := ((((he.const_mul s).add_const x).add_const 1).log (hB t).ne')
    refine (h1.sub h2).congr_deriv ?_
    have hW := legInt_W_pos hx t
    have hAt := hA t; have hBt := hB t
    unfold legInt_W at hW ⊢
    rw [Real.cosh_eq] at hW ⊢
    have hee : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
    field_simp
    nlinarith [hee, hss]
  have hint : ∀ R, ∫ t in (0:ℝ)..R, 1 / legInt_W x t ^ 1 = F R - F 0 := fun R =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      ((legInt_cont_W_pow hx 1).intervalIntegrable _ _)
  simp_rw [hint]
  have hF0 : -F 0 = Real.log ((x+1)/(x-1)) / 2 := by
    simp only [F, Real.exp_zero, mul_one]
    have hq : ((s+x+1)/(s+x-1))^2 = (x+1)/(x-1) := by
      have h1 : s + x - 1 ≠ 0 := by linarith [hA 0, Real.exp_zero]
      have h2 : x - 1 ≠ 0 := by linarith
      field_simp
      nlinarith [hss]
    rw [← hq, Real.log_pow, Real.log_div (by linarith [hB 0, Real.exp_zero])
      (by linarith [hA 0, Real.exp_zero])]
    push_cast; ring
  rw [← hF0, show -F 0 = 0 - F 0 by ring]
  refine Tendsto.sub_const ?_ _
  have hBt : Tendsto (fun R => s * Real.exp R + x + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _
      (Real.tendsto_exp_atTop.const_mul_atTop hs))
  have h2 : Tendsto (fun R => 1 - 2 / (s * Real.exp R + x + 1)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub (hBt.const_div_atTop (2:ℝ))
  have h3 := ((Real.continuousAt_log one_ne_zero).tendsto).comp h2
  rw [Real.log_one] at h3
  refine h3.congr fun R => ?_
  simp only [Function.comp_apply, F]
  rw [← Real.log_div (hA R).ne' (hB R).ne']
  congr 1
  field_simp
  ring

/-- Integration by parts for the Heine integrals:
`∫_0^R (-n/W^n + (2n+1)x/W^{n+1} - (n+1)/W^{n+2}) = s sinh R / W(R)^{n+1}`. -/
theorem legInt_heine_ibp {x : ℝ} (hx : 1 < x) (n : ℕ) (R : ℝ) :
    ∫ t in (0:ℝ)..R, (-(n:ℝ) * (1 / legInt_W x t ^ n) + (2*n+1)*x * (1 / legInt_W x t ^ (n+1)) -
      (n+1) * (1 / legInt_W x t ^ (n+2))) =
      Real.sqrt (x^2-1) * Real.sinh R / legInt_W x R ^ (n+1) := by
  set s := Real.sqrt (x^2-1) with hs_def
  have hss : s^2 = x^2-1 := Real.sq_sqrt (by nlinarith)
  have hd : ∀ t, HasDerivAt (fun t => s * Real.sinh t / legInt_W x t ^ (n+1))
      (-(n:ℝ) * (1 / legInt_W x t ^ n) + (2*n+1)*x * (1 / legInt_W x t ^ (n+1)) -
        (n+1) * (1 / legInt_W x t ^ (n+2))) t := by
    intro t
    have hW := legInt_W_pos hx t
    have hWd : HasDerivAt (legInt_W x) (s * Real.sinh t) t := by
      unfold legInt_W
      simpa using ((Real.hasDerivAt_cosh t).const_mul s).const_add x
    have h := ((Real.hasDerivAt_sinh t).const_mul s).div (hWd.pow (n+1)) (pow_ne_zero _ hW.ne')
    refine h.congr_deriv ?_
    have hc : Real.cosh t ^ 2 - Real.sinh t ^ 2 = 1 := by
      rw [Real.cosh_sq, Real.sinh_sq]; ring
    have hWe : legInt_W x t = x + s * Real.cosh t := rfl
    simp only [Pi.pow_apply, Nat.add_sub_cancel]
    generalize legInt_W x t = w at hW hWe ⊢
    have hw : w ≠ 0 := hW.ne'
    rw [show s * Real.cosh t * w^(n+1) - s * Real.sinh t * (((n+1:ℕ):ℝ) * w^n * (s * Real.sinh t)) =
        w^n * (s * Real.cosh t * w - (n+1) * s^2 * Real.sinh t^2) by push_cast; ring,
      show (w^(n+1))^2 = w^n * w^(n+2) by ring, mul_div_mul_left _ _ (pow_ne_zero _ hw)]
    rw [show -(n:ℝ) * (1 / w ^ n) + (2*n+1)*x * (1 / w ^ (n+1)) - (n+1) * (1 / w ^ (n+2)) =
        (-(n:ℝ) * w^2 + (2*n+1)*x*w - (n+1)) / w^(n+2) by field_simp; ring]
    congr 1
    rw [hWe]
    linear_combination (↑n + 1) * s ^ 2 * hc + (↑n + 1) * hss
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)]
  · simp
  · refine Continuous.intervalIntegrable ?_ _ _
    exact ((continuous_const.mul (legInt_cont_W_pow hx n)).add
      (continuous_const.mul (legInt_cont_W_pow hx (n+1)))).sub
      (continuous_const.mul (legInt_cont_W_pow hx (n+2)))

/-- The Heine recurrence for truncated integrals. -/
theorem legInt_heine_rec {x : ℝ} (hx : 1 < x) (n : ℕ) (R : ℝ) :
    (n+1) * (∫ t in (0:ℝ)..R, 1 / legInt_W x t ^ (n+2)) =
      -(n:ℝ) * (∫ t in (0:ℝ)..R, 1 / legInt_W x t ^ n) +
        (2*n+1)*x * (∫ t in (0:ℝ)..R, 1 / legInt_W x t ^ (n+1)) -
        Real.sqrt (x^2-1) * Real.sinh R / legInt_W x R ^ (n+1) := by
  rw [← legInt_heine_ibp hx n R]
  have hc := fun k : ℕ => (legInt_cont_W_pow hx k).intervalIntegrable (μ := volume) 0 R
  rw [intervalIntegral.integral_sub (((hc n).const_mul _).add ((hc _).const_mul _))
    ((hc _).const_mul _), intervalIntegral.integral_add ((hc n).const_mul _) ((hc _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  ring

/-- `s sinh R / W(R) → 1`. -/
theorem legInt_heine_bdry_one {x : ℝ} (hx : 1 < x) :
    Tendsto (fun R => Real.sqrt (x^2-1) * Real.sinh R / legInt_W x R ^ (0+1)) atTop (𝓝 1) := by
  set s := Real.sqrt (x^2-1)
  have h1 : Tendsto (fun R => x + s * Real.exp (-R)) atTop (𝓝 (x + s*0)) :=
    tendsto_const_nhds.add (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul s)
  have h2 := (h1.div_atTop (legInt_W_tendsto hx))
  have h3 := (tendsto_const_nhds (x := (1:ℝ))).sub h2
  rw [sub_zero] at h3
  refine h3.congr fun R => ?_
  have hW := (legInt_W_pos hx R).ne'
  simp only [zero_add, pow_one]
  field_simp
  unfold legInt_W
  rw [Real.cosh_eq, Real.sinh_eq]; ring

/-- `s sinh R / W(R)^{n+2} → 0`. -/
theorem legInt_heine_bdry {x : ℝ} (hx : 1 < x) (n : ℕ) :
    Tendsto (fun R => Real.sqrt (x^2-1) * Real.sinh R / legInt_W x R ^ (n+2)) atTop (𝓝 0) := by
  have h1 := legInt_heine_bdry_one hx
  have h2 : Tendsto (fun R => (legInt_W x R)⁻¹ ^ (n+1)) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp (legInt_W_tendsto hx)).pow (n+1)
  have h3 := h1.mul h2
  rw [mul_zero] at h3
  refine h3.congr fun R => ?_
  rw [inv_pow, zero_add, pow_one, ← div_eq_mul_inv, div_div, ← pow_succ']

/-- Heine's integral for `Q_n` on `(1,∞)`, unnormalized. -/
theorem legInt_heine (x : ℝ) (hx : 1 < x) (n : ℕ) :
    Tendsto (fun R => ((∫ t in (0:ℝ)..R, 1 / legInt_W x t ^ (n+1) : ℝ) : ℂ)) atTop
      (𝓝 (legendreQ n x)) := by
  have hx1 : (x:ℂ)-1 ∈ slitPlane := legInt_one_lt_mem hx
  have hc : Continuous (fun r : ℝ => (r:ℂ)) := continuous_ofReal
  have h0 : Tendsto (fun R => ((∫ t in (0:ℝ)..R, 1 / legInt_W x t ^ (0+1) : ℝ) : ℂ)) atTop
      (𝓝 (legendreQ (0:ℕ) x)) := by
    have h := (hc.tendsto _).comp (legInt_heine_zero hx)
    have hv : legendreQ (0:ℕ) x = ((Real.log ((x+1)/(x-1)) / 2 : ℝ) : ℂ) := by
      rw [Nat.cast_zero, legendreQ_zero hx1, ofReal_div,
        ofReal_log (div_pos (by linarith) (by linarith)).le]
      push_cast; ring
    rw [hv]; exact h
  have key : ∀ n : ℕ, Tendsto (fun R => ((∫ t in (0:ℝ)..R, 1 / legInt_W x t ^ (n+1) : ℝ) : ℂ))
      atTop (𝓝 (legendreQ n x)) ∧
      Tendsto (fun R => ((∫ t in (0:ℝ)..R, 1 / legInt_W x t ^ (n+1+1) : ℝ) : ℂ))
      atTop (𝓝 (legendreQ (n+1:ℕ) x)) := by
    intro n
    induction n with
    | zero =>
      refine ⟨h0, ?_⟩
      have hr := fun R => legInt_heine_rec hx 0 R
      have hb := (hc.tendsto _).comp (legInt_heine_bdry_one hx)
      have h := (h0.const_mul (x:ℂ)).sub hb
      have hQ1 : legendreQ ((0+1:ℕ):ℂ) x = x * legendreQ (0:ℕ) x - 1 := by
        rw [legendreQ_nat _ hx1]
        have := legendreP_nat 1 (one_add_mem_slitPlane_of_sub_one hx1)
        simp only [Nat.cast_zero, zero_add, Nat.cast_one] at this ⊢
        rw [this]
        simp [legendreQPoly, DLMF.OrthogonalPolynomials.legendrePolyP_one]
      rw [hQ1]
      convert h using 2 with R
      simp only [Function.comp_apply]
      have := hr R
      simp only [CharP.cast_eq_zero, zero_add, one_mul, neg_zero, zero_mul, mul_zero,
        pow_zero] at this ⊢
      rw [this]; push_cast; ring
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have hr := fun R => legInt_heine_rec hx (k+1) R
      have hb := (hc.tendsto _).comp (legInt_heine_bdry hx k)
      have h := ((((ih.1.const_mul (-((k:ℂ)+1))).add (ih.2.const_mul ((2*((k:ℂ)+1)+1)*x))).sub
        hb).div_const ((k:ℂ)+2))
      have hrec := olverQ_recurrence_3 (k:ℂ) 0 hx1
      rw [show (k:ℂ)+2 = ((k+1+1:ℕ):ℂ) by push_cast; ring,
        show (k:ℂ)+1 = ((k+1:ℕ):ℂ) by push_cast; ring, legInt_olverQ_nat_zero_order _ hx1,
        legInt_olverQ_nat_zero_order _ hx1, legInt_olverQ_nat_zero_order _ hx1] at hrec
      have hQ : legendreQ ((k+1+1:ℕ):ℂ) x = (-((k:ℂ)+1) * legendreQ k x +
          (2*((k:ℂ)+1)+1)*x * legendreQ ((k+1:ℕ):ℂ) x - 0) / ((k:ℂ)+2) := by
        have hf : (k.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
        simp only [Nat.factorial_succ] at hrec
        push_cast at hrec ⊢
        have hk2 : (k:ℂ)+2 ≠ 0 := by norm_cast
        have hk1 : (k:ℂ)+1 ≠ 0 := by norm_cast
        field_simp at hrec
        rw [show (k:ℂ)+1+1 = k+2 by ring] at hrec ⊢
        have e : ((k:ℂ)+0+2)*((k:ℂ)-0+2)*legendreQ ((k:ℂ)+2) x/((k:ℂ)+2) =
            ((k:ℂ)+2)*legendreQ ((k:ℂ)+2) x := by field_simp; ring
        rw [eq_div_iff hk2]
        linear_combination hrec - e
      rw [hQ]
      convert h using 2 with R
      simp only [Function.comp_apply]
      have := hr R
      have hk2 : (k:ℝ)+1+1 ≠ 0 := by positivity
      push_cast at this ⊢
      rw [eq_div_iff (by norm_cast)]
      rw [show k+1+1+1 = k+1+2 by ring]
      apply_fun ((↑) : ℝ → ℂ) at this
      push_cast at this
      linear_combination this
  exact (key n).1

/-- The endpoint `u = ½ log((x+1)/(x-1)) = arcoth x`. -/
noncomputable def legInt_u (x : ℝ) : ℝ := 1/2*Real.log ((x+1)/(x-1))

/-- `√(x²-1) e^u = x+1` at `u = arcoth x`. -/
theorem legInt_s_exp_u {x : ℝ} (hx : 1 < x) :
    Real.sqrt (x^2-1) * Real.exp (legInt_u x) = x+1 := by
  have hq : 0 < (x+1)/(x-1) := div_pos (by linarith) (by linarith)
  have hs := Real.sqrt_nonneg (x^2-1)
  have hss : Real.sqrt (x^2-1)^2 = x^2-1 := Real.sq_sqrt (by nlinarith)
  have he : Real.exp (legInt_u x)^2 = (x+1)/(x-1) := by
    rw [← Real.exp_nat_mul, legInt_u]; push_cast
    rw [show (2:ℝ) * (1/2*Real.log ((x+1)/(x-1))) = Real.log ((x+1)/(x-1)) by ring,
      Real.exp_log hq]
  have h2 : (Real.sqrt (x^2-1) * Real.exp (legInt_u x))^2 = (x+1)^2 := by
    rw [mul_pow, hss, he]; field_simp; ring
  exact (sq_eq_sq₀ (by positivity) (by linarith)).1 h2

/-- `√(x²-1) cosh u = x` and `√(x²-1) sinh u = 1` at `u = arcoth x`. -/
theorem legInt_s_cosh_sinh_u {x : ℝ} (hx : 1 < x) :
    Real.sqrt (x^2-1) * Real.cosh (legInt_u x) = x ∧
      Real.sqrt (x^2-1) * Real.sinh (legInt_u x) = 1 := by
  have h1 := legInt_s_exp_u hx
  have hss : Real.sqrt (x^2-1)^2 = x^2-1 := Real.sq_sqrt (by nlinarith)
  have hee : Real.exp (legInt_u x) * Real.exp (-legInt_u x) = 1 := by
    rw [← Real.exp_add]; simp
  have h2 : Real.sqrt (x^2-1) * Real.exp (-legInt_u x) = x-1 := by
    have hx1 : x+1 ≠ 0 := by linarith
    have : (Real.sqrt (x^2-1) * Real.exp (-legInt_u x)) * (x+1) = (x-1)*(x+1) := by
      linear_combination (-(Real.sqrt (x^2-1) * Real.exp (-legInt_u x))) * h1 +
        (Real.sqrt (x^2-1))^2 * hee + hss
    exact mul_right_cancel₀ hx1 this
  rw [Real.cosh_eq, Real.sinh_eq]
  constructor
  · linear_combination h1/2 + h2/2
  · linear_combination h1/2 - h2/2

/-- The kernel `V(t) = x - √(x²-1) cosh t` of DLMF 14.12.9. -/
noncomputable def legInt_V (x t : ℝ) : ℝ := x - Real.sqrt (x^2-1) * Real.cosh t

/-- The integrand `V^n cosh(m t)`. -/
noncomputable def legInt_f (x : ℝ) (n m : ℕ) (t : ℝ) : ℝ := legInt_V x t ^ n * Real.cosh (m*t)

/-- The integrals `M(n,m) = ∫_0^u V^n cosh(m t)`. -/
noncomputable def legInt_M (x : ℝ) (n m : ℕ) : ℝ := ∫ t in (0:ℝ)..legInt_u x, legInt_f x n m t

/-- Continuity of `V^n cosh(m t)`. -/
theorem legInt_cont_f (x : ℝ) (n m : ℕ) : Continuous (legInt_f x n m) := by
  unfold legInt_f legInt_V; fun_prop

/-- `V(u) = 0`. -/
theorem legInt_V_u {x : ℝ} (hx : 1 < x) : legInt_V x (legInt_u x) = 0 := by
  rw [legInt_V, (legInt_s_cosh_sinh_u hx).1, sub_self]

/-- The degree recurrence `(n+2) M(n+2,0) = (2n+3) x M(n+1,0) - (n+1) M(n,0)`. -/
theorem legInt_M_deg {x : ℝ} (hx : 1 < x) (n : ℕ) :
    (n+2) * legInt_M x (n+2) 0 = (2*n+3)*x*legInt_M x (n+1) 0 - (n+1) * legInt_M x n 0 := by
  set s := Real.sqrt (x^2-1) with hs_def
  have hss : s^2 = x^2-1 := Real.sq_sqrt (by nlinarith)
  have hd : ∀ t, HasDerivAt (fun t => s * (legInt_V x t ^ (n+1) * Real.sinh t))
      (-(n+2) * legInt_f x (n+2) 0 t + (2*n+3)*x*legInt_f x (n+1) 0 t - (n+1) * legInt_f x n 0 t)
      t := by
    intro t
    have hV : HasDerivAt (legInt_V x) (-(s * Real.sinh t)) t := by
      unfold legInt_V
      simpa using ((Real.hasDerivAt_cosh t).const_mul s).const_sub x
    have h := ((hV.pow (n+1)).mul (Real.hasDerivAt_sinh t)).const_mul s
    refine h.congr_deriv ?_
    have hc : Real.cosh t ^ 2 - Real.sinh t ^ 2 = 1 := by
      rw [Real.cosh_sq, Real.sinh_sq]; ring
    have hv : legInt_V x t = x - s * Real.cosh t := rfl
    simp only [legInt_f, CharP.cast_eq_zero, zero_mul, Real.cosh_zero, mul_one, Nat.add_sub_cancel,
      Pi.pow_apply]
    generalize legInt_V x t = v at hv ⊢
    push_cast
    linear_combination v^n*((v - (n+1)*(2*(x-v) + (v - x + s*Real.cosh t)))*hv + (n+1)*hss +
      (n+1)*s^2*hc)
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := legInt_u x)
    (fun t _ => hd t) (by
      refine Continuous.intervalIntegrable ?_ _ _
      exact ((continuous_const.mul (legInt_cont_f x _ _)).add
        (continuous_const.mul (legInt_cont_f x _ _))).sub
        (continuous_const.mul (legInt_cont_f x _ _)))
  have hc := fun k : ℕ => (legInt_cont_f x k 0).intervalIntegrable (μ := volume) 0 (legInt_u x)
  rw [intervalIntegral.integral_sub (((hc _).const_mul _).add ((hc _).const_mul _))
    ((hc _).const_mul _), intervalIntegral.integral_add ((hc _).const_mul _) ((hc _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, legInt_V_u hx] at hint
  simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow,
    zero_mul, mul_zero, Real.sinh_zero, sub_zero] at hint
  simp only [legInt_M]
  linarith

/-- The order recurrence
`(n+m+2) s M(n,m+2) = 2(m+1) x M(n,m+1) + (n-m) s M(n,m)`. -/
theorem legInt_M_ord {x : ℝ} (hx : 1 < x) (n m : ℕ) :
    (n+m+2) * Real.sqrt (x^2-1) * legInt_M x n (m+2) =
      2*(m+1)*x*legInt_M x n (m+1) + ((n:ℝ)-m) * Real.sqrt (x^2-1) * legInt_M x n m := by
  set s := Real.sqrt (x^2-1) with hs_def
  have hd : ∀ t, HasDerivAt (fun t => legInt_V x t ^ (n+1) * Real.sinh ((m+1)*t))
      ((1/2:ℝ) * (-(n+m+2) * s * legInt_f x n (m+2) t + 2*(m+1)*x*legInt_f x n (m+1) t +
        ((n:ℝ)-m) * s * legInt_f x n m t)) t := by
    intro t
    have hV : HasDerivAt (legInt_V x) (-(s * Real.sinh t)) t := by
      unfold legInt_V
      simpa using ((Real.hasDerivAt_cosh t).const_mul s).const_sub x
    have h3 : HasDerivAt (fun t : ℝ => Real.sinh ((m+1)*t)) (((m:ℝ)+1) * Real.cosh ((m+1)*t)) t := by
      have := (Real.hasDerivAt_sinh ((m+1)*t)).comp t ((hasDerivAt_id t).const_mul ((m:ℝ)+1))
      simpa [mul_comm, Function.comp_def] using this
    have h := (hV.pow (n+1)).mul h3
    refine h.congr_deriv ?_
    have hv : legInt_V x t = x - s * Real.cosh t := rfl
    have e1 : Real.cosh (((m+2:ℕ):ℝ)*t) = Real.cosh ((m+1)*t) * Real.cosh t +
        Real.sinh ((m+1)*t) * Real.sinh t := by
      rw [← Real.cosh_add]; push_cast; ring_nf
    have e2 : Real.cosh (((m:ℕ):ℝ)*t) = Real.cosh ((m+1)*t) * Real.cosh t -
        Real.sinh ((m+1)*t) * Real.sinh t := by
      rw [← Real.cosh_sub]; ring_nf
    simp only [legInt_f, e1, e2, Nat.add_sub_cancel, Pi.pow_apply]
    generalize legInt_V x t = v at hv ⊢
    push_cast
    linear_combination v^n*(m+1)*Real.cosh ((m+1)*t)*hv
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := legInt_u x)
    (fun t _ => hd t) (by
      refine Continuous.intervalIntegrable ?_ _ _
      exact continuous_const.mul (((continuous_const.mul (legInt_cont_f x _ _)).add
        (continuous_const.mul (legInt_cont_f x _ _))).add
        (continuous_const.mul (legInt_cont_f x _ _))))
  have hc := fun k : ℕ => (legInt_cont_f x n k).intervalIntegrable (μ := volume) 0 (legInt_u x)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    (((hc _).const_mul _).add ((hc _).const_mul _)) ((hc _).const_mul _),
    intervalIntegral.integral_add ((hc _).const_mul _) ((hc _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, legInt_V_u hx] at hint
  simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow,
    zero_mul, mul_zero, Real.sinh_zero, sub_zero] at hint
  simp only [legInt_M]
  linarith

/-- `M(0,0) = u` and `M(1,0) = x u - 1`. -/
theorem legInt_M_base {x : ℝ} (hx : 1 < x) :
    legInt_M x 0 0 = legInt_u x ∧ legInt_M x 1 0 = x * legInt_u x - 1 := by
  constructor
  · simp [legInt_M, legInt_f]
  · have hd : ∀ t, HasDerivAt (fun t => x*t - Real.sqrt (x^2-1) * Real.sinh t) (legInt_f x 1 0 t) t :=
      fun t => by
        have := ((hasDerivAt_id t).const_mul x).sub ((Real.hasDerivAt_sinh t).const_mul
          (Real.sqrt (x^2-1)))
        exact this.congr_deriv (by simp [legInt_f, legInt_V])
    rw [legInt_M, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      ((legInt_cont_f x 1 0).intervalIntegrable _ _), (legInt_s_cosh_sinh_u hx).2]
    simp

/-- `s M(n,1) = x M(n,0) - M(n+1,0)`. -/
theorem legInt_M_one (x : ℝ) (n : ℕ) :
    Real.sqrt (x^2-1) * legInt_M x n 1 = x * legInt_M x n 0 - legInt_M x (n+1) 0 := by
  have hc := fun k : ℕ => (legInt_cont_f x k 0).intervalIntegrable (μ := volume) 0 (legInt_u x)
  simp only [legInt_M]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub ((hc _).const_mul _) (hc _)]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [legInt_f, legInt_V, Nat.cast_one, one_mul, Nat.cast_zero, zero_mul, Real.cosh_zero]
  ring

/-- The Legendre recurrence `(k+2) Q_{k+2} = (2k+3) x Q_{k+1} - (k+1) Q_k` on the principal sheet. -/
theorem legInt_legendreQ_rec (k : ℕ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    ((k:ℂ)+2) * legendreQ ((k+2:ℕ):ℂ) z =
      (2*k+3)*z*legendreQ ((k+1:ℕ):ℂ) z - ((k:ℂ)+1) * legendreQ k z := by
  have hrec := olverQ_recurrence_3 (k:ℂ) 0 hz
  rw [show (k:ℂ)+2 = ((k+1+1:ℕ):ℂ) by push_cast; ring,
    show (k:ℂ)+1 = ((k+1:ℕ):ℂ) by push_cast; ring, legInt_olverQ_nat_zero_order _ hz,
    legInt_olverQ_nat_zero_order _ hz, legInt_olverQ_nat_zero_order _ hz] at hrec
  have hf : (k.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
  simp only [Nat.factorial_succ] at hrec
  push_cast at hrec ⊢
  have hk2 : (k:ℂ)+2 ≠ 0 := by norm_cast
  have hk1 : (k:ℂ)+1 ≠ 0 := by norm_cast
  field_simp at hrec
  rw [show (k:ℂ)+1+1 = k+2 by ring] at hrec
  have e : ((k:ℂ)+0+2)*((k:ℂ)-0+2)*legendreQ ((k:ℂ)+2) z/((k:ℂ)+2) =
      ((k:ℂ)+2)*legendreQ ((k:ℂ)+2) z := by field_simp; ring
  linear_combination hrec - e

/-- `Q_n(x) = M(n,0)` for `x > 1`. -/
theorem legInt_legendreQ_M {x : ℝ} (hx : 1 < x) (n : ℕ) : legendreQ n x = legInt_M x n 0 := by
  have hx1 : (x:ℂ)-1 ∈ slitPlane := legInt_one_lt_mem hx
  have key : ∀ n : ℕ, legendreQ n x = legInt_M x n 0 ∧ legendreQ (n+1:ℕ) x = legInt_M x (n+1) 0 := by
    intro n
    induction n with
    | zero =>
      have h0 : legendreQ (0:ℕ) x = legInt_M x 0 0 := by
        rw [(legInt_M_base hx).1, Nat.cast_zero, legendreQ_zero hx1, legInt_u, ofReal_mul,
          ofReal_log (div_pos (by linarith) (by linarith)).le]
        push_cast; ring
      refine ⟨h0, ?_⟩
      have hQ0 : legendreQ 0 x = legInt_u x := by
        rw [← (legInt_M_base hx).1, ← h0, Nat.cast_zero]
      rw [zero_add, (legInt_M_base hx).2, legendreQ_nat _ hx1]
      have := legendreP_nat 1 (one_add_mem_slitPlane_of_sub_one hx1)
      simp only [Nat.cast_one] at this ⊢
      rw [this, hQ0]
      simp [legendreQPoly, DLMF.OrthogonalPolynomials.legendrePolyP_one]
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have h := legInt_legendreQ_rec k hx1
      have hM := legInt_M_deg hx k
      have hk2 : (k:ℂ)+2 ≠ 0 := by norm_cast
      rw [ih.1, ih.2] at h
      apply mul_left_cancel₀ hk2
      rw [show k+1+1 = k+2 by ring, h]
      apply_fun ((↑) : ℝ → ℂ) at hM
      push_cast at hM
      linear_combination -hM
  exact (key n).1

/-- The integrals `A(n,p) = ∫_{-1}^1 (1-t²)^n/(x-t)^p`. -/
noncomputable def legInt_A (x : ℝ) (n p : ℕ) : ℝ := ∫ t in (-1:ℝ)..1, (1-t^2)^n / (x-t)^p

/-- Continuity of the integrand of `legInt_A` on `[-1,1]`. -/
theorem legInt_contOn_A {x : ℝ} (hx : 1 < x) (n p : ℕ) :
    ContinuousOn (fun t : ℝ => (1-t^2)^n / (x-t)^p) (uIcc (-1) 1) := by
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => ?_
  rw [uIcc_of_le (by norm_num)] at ht
  exact pow_ne_zero _ (by linarith [ht.2])

/-- Interval integrability of the integrand of `legInt_A`. -/
theorem legInt_intInt_A {x : ℝ} (hx : 1 < x) (n p : ℕ) :
    IntervalIntegrable (fun t : ℝ => (1-t^2)^n / (x-t)^p) volume (-1) 1 :=
  (legInt_contOn_A hx n p).intervalIntegrable

/-- The algebraic relation `A(n+1,p+2) = (1-x²) A(n,p+2) + 2x A(n,p+1) - A(n,p)`. -/
theorem legInt_A_R1 {x : ℝ} (hx : 1 < x) (n p : ℕ) :
    legInt_A x (n+1) (p+2) = (1-x^2) * legInt_A x n (p+2) + 2*x * legInt_A x n (p+1) -
      legInt_A x n p := by
  have hi := legInt_intInt_A hx
  simp only [legInt_A]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((hi _ _).const_mul _) ((hi _ _).const_mul _),
    ← intervalIntegral.integral_sub (((hi _ _).const_mul _).add ((hi _ _).const_mul _)) (hi _ _)]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le (by norm_num)] at ht
  have hw : x - t ≠ 0 := by linarith [ht.2]
  field_simp
  ring

/-- Integration by parts: `2(n+1)(x A(n,p+1) - A(n,p)) = (p+1) A(n+1,p+2)`. -/
theorem legInt_A_R2 {x : ℝ} (hx : 1 < x) (n p : ℕ) :
    2*(n+1)*(x * legInt_A x n (p+1) - legInt_A x n p) = (p+1) * legInt_A x (n+1) (p+2) := by
  have hi := legInt_intInt_A hx
  have hd : ∀ t ∈ uIcc (-1:ℝ) 1, HasDerivAt (fun t : ℝ => (1-t^2)^(n+1) / (x-t)^(p+1))
      ((p+1) * ((1-t^2)^(n+1) / (x-t)^(p+2)) -
        2*(n+1)*(x * ((1-t^2)^n / (x-t)^(p+1)) - (1-t^2)^n / (x-t)^p)) t := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    have hw : x - t ≠ 0 := by linarith [ht.2]
    have h1 : HasDerivAt (fun t : ℝ => (1-t^2)^(n+1)) ((n+1:ℕ) * (1-t^2)^n * (-(2*t))) t := by
      have := ((hasDerivAt_pow 2 t).const_sub 1).pow (n+1)
      exact this.congr_deriv (by push_cast; ring)
    have h2 : HasDerivAt (fun t : ℝ => (x-t)^(p+1)) ((p+1:ℕ) * (x-t)^p * (-1)) t := by
      have := ((hasDerivAt_id t).const_sub x).pow (p+1)
      exact this.congr_deriv (by simp)
    refine (h1.div h2 (pow_ne_zero _ hw)).congr_deriv ?_
    field_simp
    push_cast
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
    refine ((((hi _ _).const_mul _)).sub ((((hi _ _).const_mul _).sub (hi _ _)).const_mul _)))
  rw [intervalIntegral.integral_sub ((hi _ _).const_mul _)
    ((((hi _ _).const_mul _).sub (hi _ _)).const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_sub ((hi _ _).const_mul _) (hi _ _),
    intervalIntegral.integral_const_mul] at hint
  norm_num at hint
  simp only [legInt_A]
  linarith

/-- The order relation
`(p+1)(1-x²) A(n,p+2) + 2(p-n) x A(n,p+1) + (2n+1-p) A(n,p) = 0`. -/
theorem legInt_A_ord {x : ℝ} (hx : 1 < x) (n p : ℕ) :
    (p+1)*(1-x^2)*legInt_A x n (p+2) + 2*((p:ℝ)-n)*x*legInt_A x n (p+1) +
      (2*n+1-(p:ℝ))*legInt_A x n p = 0 := by
  linear_combination (-((p:ℝ)+1))*legInt_A_R1 hx n p - legInt_A_R2 hx n p

/-- `A(n+1,n+2) = 2x A(n,n+1) - 2(x²-1) A(n,n+2)`. -/
theorem legInt_A_b {x : ℝ} (hx : 1 < x) (n : ℕ) :
    legInt_A x (n+1) (n+2) = 2*x*legInt_A x n (n+1) - 2*(x^2-1)*legInt_A x n (n+2) := by
  have h1 := legInt_A_R1 hx n n
  have hn : (n:ℝ)+1 ≠ 0 := by positivity
  have h2 := mul_left_cancel₀ hn (by linear_combination legInt_A_R2 hx n n :
    ((n:ℝ)+1) * (2*(x*legInt_A x n (n+1) - legInt_A x n n)) = ((n:ℝ)+1) * legInt_A x (n+1) (n+2))
  linear_combination 2*h1 + h2

/-- The degree recurrence `(n+2) A(n+2,n+3) = 2(2n+3) x A(n+1,n+2) - 4(n+1) A(n,n+1)`. -/
theorem legInt_A_deg {x : ℝ} (hx : 1 < x) (n : ℕ) :
    (n+2)*legInt_A x (n+2) (n+3) = 2*(2*n+3)*x*legInt_A x (n+1) (n+2) -
      4*(n+1)*legInt_A x n (n+1) := by
  have B0 := legInt_A_b hx n
  have B1 := legInt_A_b hx (n+1)
  have R := legInt_A_R1 hx n (n+1)
  have O := legInt_A_ord hx n (n+1)
  simp only [show n+1+1 = n+2 by ring, show n+1+2 = n+3 by ring] at B1 R O
  push_cast at B1 R O ⊢
  linear_combination ((n:ℝ)+2)*B1 - 2*(x^2-1)*((n:ℝ)+2)*R - 2*(x^2-1)*O - 2*((n:ℝ)+1)*x*B0

/-- `A(0,1) = log((x+1)/(x-1))` and `A(0,2) = 2/(x²-1)`. -/
theorem legInt_A_base {x : ℝ} (hx : 1 < x) :
    legInt_A x 0 1 = Real.log ((x+1)/(x-1)) ∧ legInt_A x 0 2 = 2/(x^2-1) := by
  have hi := legInt_intInt_A hx
  constructor
  · have hd : ∀ t ∈ uIcc (-1:ℝ) 1, HasDerivAt (fun t => -Real.log (x-t)) ((1-t^2)^0/(x-t)^1) t := by
      intro t ht
      rw [uIcc_of_le (by norm_num)] at ht
      have hw : x - t ≠ 0 := by linarith [ht.2]
      have := (((hasDerivAt_id t).const_sub x).log hw).neg
      exact this.congr_deriv (by simp [neg_div])
    rw [legInt_A, intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hi 0 1),
      Real.log_div (by linarith) (by linarith)]
    ring_nf
  · have hd : ∀ t ∈ uIcc (-1:ℝ) 1, HasDerivAt (fun t => 1/(x-t)) ((1-t^2)^0/(x-t)^2) t := by
      intro t ht
      rw [uIcc_of_le (by norm_num)] at ht
      have hw : x - t ≠ 0 := by linarith [ht.2]
      have := (((hasDerivAt_id t).const_sub x)).inv hw
      exact (this.congr_deriv (by simp)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y => by simp)
    rw [legInt_A, intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hi 0 2)]
    have h1 : x - 1 ≠ 0 := by linarith
    have h2 : x + 1 ≠ 0 := by linarith
    have h3 : x^2 - 1 ≠ 0 := by nlinarith
    have h4 : 1 + x ≠ 0 := by linarith
    norm_num
    field_simp
    ring

/-- `Q_n(x) = A(n,n+1)/2^{n+1}` for `x > 1`. -/
theorem legInt_legendreQ_A {x : ℝ} (hx : 1 < x) (n : ℕ) :
    legendreQ n x = legInt_A x n (n+1) / 2^(n+1) := by
  have hx1 : (x:ℂ)-1 ∈ slitPlane := legInt_one_lt_mem hx
  have key : ∀ n : ℕ, legendreQ n x = legInt_A x n (n+1) / 2^(n+1) ∧
      legendreQ (n+1:ℕ) x = legInt_A x (n+1) (n+1+1) / 2^(n+1+1) := by
    intro n
    induction n with
    | zero =>
      have hQ0 : legendreQ 0 x = Real.log ((x+1)/(x-1)) / 2 := by
        rw [legendreQ_zero hx1, ofReal_log (div_pos (by linarith) (by linarith)).le]
        push_cast; ring
      refine ⟨by rw [Nat.cast_zero, hQ0, (legInt_A_base hx).1]; push_cast; ring, ?_⟩
      rw [zero_add, legendreQ_nat _ hx1]
      have := legendreP_nat 1 (one_add_mem_slitPlane_of_sub_one hx1)
      simp only [Nat.cast_one] at this ⊢
      rw [this, hQ0, legInt_A_b hx 0, (legInt_A_base hx).1, (legInt_A_base hx).2]
      have h3 : (x:ℂ)^2 - 1 ≠ 0 := by
        rw [show (x:ℂ)^2-1 = ((x^2-1:ℝ):ℂ) by push_cast; ring]
        exact ofReal_ne_zero.2 (by nlinarith)
      simp [legendreQPoly, DLMF.OrthogonalPolynomials.legendrePolyP_one]
      field_simp
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have h := legInt_legendreQ_rec k hx1
      have hA := legInt_A_deg hx k
      have hk2 : (k:ℂ)+2 ≠ 0 := by norm_cast
      rw [ih.1, ih.2] at h
      apply mul_left_cancel₀ hk2
      rw [show k+1+1 = k+2 by ring, h]
      apply_fun ((↑) : ℝ → ℂ) at hA
      push_cast at hA ⊢
      rw [show k+1+1 = k+2 by ring, show k+2+1 = k+3 by ring]
      linear_combination -hA / (2:ℂ)^(k+3)
  exact (key n).1

/-- The real Laplace kernel `w(θ) = x + √(x²-1) cos θ`. -/
noncomputable def legInt_w (x θ : ℝ) : ℝ := x + Real.sqrt (x^2-1) * Real.cos θ

/-- The moments `K(p,q) = ∫_0^π w^p sin^{2q}θ`. -/
noncomputable def legInt_Ks (x : ℝ) (p q : ℕ) : ℝ :=
  ∫ θ in (0:ℝ)..π, legInt_w x θ ^ p * Real.sin θ ^ (2*q)

/-- Continuity of the integrand of `legInt_Ks`. -/
theorem legInt_cont_Ks (x : ℝ) (p q : ℕ) :
    Continuous fun θ => legInt_w x θ ^ p * Real.sin θ ^ (2*q) := by
  unfold legInt_w; fun_prop

/-- Derivative of the real Laplace kernel. -/
theorem legInt_hasDerivAt_w (x θ : ℝ) :
    HasDerivAt (legInt_w x) (-(Real.sqrt (x^2-1) * Real.sin θ)) θ := by
  unfold legInt_w
  simpa using ((Real.hasDerivAt_cos θ).const_mul (Real.sqrt (x^2-1))).const_add x

/-- Integration by parts:
`(r+2q+3) K(r+1,q+1) = (r+1) x K(r,q+1) + (2q+1) K(r+1,q)`. -/
theorem legInt_Ks_star (x : ℝ) (r q : ℕ) :
    (r+2*q+3) * legInt_Ks x (r+1) (q+1) = (r+1)*x*legInt_Ks x r (q+1) +
      (2*q+1) * legInt_Ks x (r+1) q := by
  have hd : ∀ θ, HasDerivAt (fun θ => legInt_w x θ ^ (r+1) * (Real.sin θ ^ (2*q+1) * Real.cos θ))
      (-(r+2*q+3) * (legInt_w x θ ^ (r+1) * Real.sin θ ^ (2*(q+1))) +
        (r+1)*x*(legInt_w x θ ^ r * Real.sin θ ^ (2*(q+1))) +
        (2*q+1) * (legInt_w x θ ^ (r+1) * Real.sin θ ^ (2*q))) θ := by
    intro θ
    have h1 := (legInt_hasDerivAt_w x θ).pow (r+1)
    have h2 := ((Real.hasDerivAt_sin θ).pow (2*q+1)).mul (Real.hasDerivAt_cos θ)
    refine (h1.mul h2).congr_deriv ?_
    have hv : legInt_w x θ = x + Real.sqrt (x^2-1) * Real.cos θ := rfl
    have hsc := Real.sin_sq_add_cos_sq θ
    simp only [Pi.pow_apply, Pi.mul_apply, Nat.add_sub_cancel]
    generalize legInt_w x θ = v at hv ⊢
    push_cast
    linear_combination ((r:ℝ)+1)*v^r*Real.sin θ^(2*q+2)*hv +
      (2*(q:ℝ)+1)*v^(r+1)*Real.sin θ^(2*q)*hsc
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := π)
    (fun θ _ => hd θ) (by
      refine Continuous.intervalIntegrable ?_ _ _
      exact ((continuous_const.mul (legInt_cont_Ks x _ _)).add
        (continuous_const.mul (legInt_cont_Ks x _ _))).add
        (continuous_const.mul (legInt_cont_Ks x _ _)))
  have hc := fun p k : ℕ => (legInt_cont_Ks x p k).intervalIntegrable (μ := volume) 0 π
  rw [intervalIntegral.integral_add (((hc _ _).const_mul _).add ((hc _ _).const_mul _))
    ((hc _ _).const_mul _), intervalIntegral.integral_add ((hc _ _).const_mul _)
    ((hc _ _).const_mul _), intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hint
  simp only [Real.sin_pi, Real.sin_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    not_false_eq_true, zero_pow, zero_mul, mul_zero, sub_zero] at hint
  simp only [legInt_Ks]
  linarith

/-- Integration by parts:
`(p+1) s² K(p,q+1) = (2q+1) (K(p+2,q) - x K(p+1,q))`, `s = √(x²-1)`. -/
theorem legInt_Ks_ibp (x : ℝ) (p q : ℕ) :
    ((p:ℝ)+1) * Real.sqrt (x^2-1)^2 * legInt_Ks x p (q+1) =
      (2*q+1) * (legInt_Ks x (p+2) q - x * legInt_Ks x (p+1) q) := by
  have hd : ∀ θ, HasDerivAt (fun θ => Real.sqrt (x^2-1) * (legInt_w x θ ^ (p+1) * Real.sin θ ^ (2*q+1)))
      (-(((p:ℝ)+1) * Real.sqrt (x^2-1)^2) * (legInt_w x θ ^ p * Real.sin θ ^ (2*(q+1))) +
        (2*q+1) * (legInt_w x θ ^ (p+2) * Real.sin θ ^ (2*q)) -
        (2*q+1) * x * (legInt_w x θ ^ (p+1) * Real.sin θ ^ (2*q))) θ := by
    intro θ
    have h1 := (legInt_hasDerivAt_w x θ).pow (p+1)
    have h2 := (Real.hasDerivAt_sin θ).pow (2*q+1)
    refine ((h1.mul h2).const_mul (Real.sqrt (x^2-1))).congr_deriv ?_
    have hv : legInt_w x θ = x + Real.sqrt (x^2-1) * Real.cos θ := rfl
    simp only [Pi.pow_apply, Nat.add_sub_cancel]
    generalize legInt_w x θ = v at hv ⊢
    push_cast
    linear_combination (-(2*(q:ℝ)+1))*v^(p+1)*Real.sin θ^(2*q)*hv
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := π)
    (fun θ _ => hd θ) (by
      refine Continuous.intervalIntegrable ?_ _ _
      exact ((continuous_const.mul (legInt_cont_Ks x _ _)).add
        (continuous_const.mul (legInt_cont_Ks x _ _))).sub
        (continuous_const.mul (legInt_cont_Ks x _ _)))
  have hc := fun p k : ℕ => (legInt_cont_Ks x p k).intervalIntegrable (μ := volume) 0 π
  rw [intervalIntegral.integral_sub (((hc _ _).const_mul _).add ((hc _ _).const_mul _))
    ((hc _ _).const_mul _), intervalIntegral.integral_add ((hc _ _).const_mul _)
    ((hc _ _).const_mul _), intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hint
  simp only [Real.sin_pi, Real.sin_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    not_false_eq_true, zero_pow, mul_zero, sub_zero] at hint
  simp only [legInt_Ks]
  linarith

/-- `K(r+2,0) - x K(r+1,0) = (r+1) s² K(r,1)`. -/
theorem legInt_Ks_one (x : ℝ) (r : ℕ) :
    legInt_Ks x (r+2) 0 - x * legInt_Ks x (r+1) 0 = (r+1) * Real.sqrt (x^2-1)^2 * legInt_Ks x r 1 := by
  have := legInt_Ks_ibp x r 0
  simp only [CharP.cast_eq_zero, mul_zero, zero_add, one_mul] at this
  linarith

/-- The constant `2^m m! (2m+p)! / ((2m)! p! π)` of DLMF 14.12.8 with `n = m+p`. -/
noncomputable def legInt_cK (m p : ℕ) : ℂ :=
  2^m*(m.factorial:ℂ)*(2*m+p).factorial/(((2*m).factorial:ℂ)*p.factorial*π)

/-- Ratio of consecutive constants `legInt_cK`. -/
theorem legInt_cK_succ (m p : ℕ) :
    legInt_cK (m+1) (p+1) * (2*m+1) = legInt_cK m (p+2) * (2*m+p+3) * (p+2) := by
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  simp only [legInt_cK]
  rw [show 2*(m+1)+(p+1) = 2*m+p+2+1 by ring, show 2*(m+1) = 2*m+1+1 by ring,
    show 2*m+(p+2) = 2*m+p+2 by ring, show p+2 = p+1+1 by ring]
  simp only [Nat.factorial_succ]
  push_cast
  have n1 : (2*(m:ℂ)+1) ≠ 0 := by norm_cast
  have n2 : (2*(m:ℂ)+1+1) ≠ 0 := by norm_cast
  have n3 : (2*(m:ℂ)+1+1+1) ≠ 0 := by norm_cast
  have n4 : (2*(m:ℂ)+1+1+1+1) ≠ 0 := by norm_cast
  have n5 : ((p:ℂ)+1) ≠ 0 := by norm_cast
  have n6 : ((p:ℂ)+1+1) ≠ 0 := by norm_cast
  have n7 : ((m:ℂ)+1) ≠ 0 := by norm_cast
  have n8 : ((m:ℂ)+1+1) ≠ 0 := by norm_cast
  have f1 : ((2*m).factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have f2 : (p.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have f3 : ((m.factorial:ℂ)) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  simp only [div_mul_eq_mul_div]
  rw [div_eq_div_iff (by apply_rules [mul_ne_zero]) (by apply_rules [mul_ne_zero])]
  ring

/-- Ratio of consecutive constants `legInt_cK`. -/
theorem legInt_cK_succ' (m p : ℕ) :
    legInt_cK (m+2) p * (2*m+3) = legInt_cK (m+1) (p+1) * (2*m+p+4) * (p+1) := by
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  simp only [legInt_cK]
  rw [show 2*(m+2)+p = 2*m+p+3+1 by ring, show 2*(m+1)+(p+1) = 2*m+p+3 by ring,
    show 2*(m+2) = 2*m+1+1+1+1 by ring, show 2*(m+1) = 2*m+1+1 by ring, show m+2 = m+1+1 by ring]
  simp only [Nat.factorial_succ]
  push_cast
  have n1 : (2*(m:ℂ)+1) ≠ 0 := by norm_cast
  have n2 : (2*(m:ℂ)+1+1) ≠ 0 := by norm_cast
  have n3 : (2*(m:ℂ)+1+1+1) ≠ 0 := by norm_cast
  have n4 : (2*(m:ℂ)+1+1+1+1) ≠ 0 := by norm_cast
  have n5 : ((p:ℂ)+1) ≠ 0 := by norm_cast
  have n6 : ((p:ℂ)+1+1) ≠ 0 := by norm_cast
  have n7 : ((m:ℂ)+1) ≠ 0 := by norm_cast
  have n8 : ((m:ℂ)+1+1) ≠ 0 := by norm_cast
  have f1 : ((2*m).factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have f2 : (p.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have f3 : ((m.factorial:ℂ)) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  simp only [div_mul_eq_mul_div]
  rw [div_eq_div_iff (by apply_rules [mul_ne_zero] <;> norm_cast)
    (by apply_rules [mul_ne_zero])]
  ring

/-- DLMF 14.12.8 in the form `P^m_{m+p}(x) = c s^m K(p,m)`. -/
theorem legInt_associatedP_Ks {x : ℝ} (hx : 1 < x) (m p : ℕ) :
    associatedP ((m+p:ℕ):ℂ) m x = legInt_cK m p * (Real.sqrt (x^2-1):ℂ)^m * legInt_Ks x p m := by
  have hx1 : ((x:ℂ)-1) ∈ slitPlane := legInt_one_lt_mem hx
  set s := Real.sqrt (x^2-1) with hs_def
  have hs : (s:ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 (by nlinarith)).ne'
  have hb1 : legendreBranchPower 1 x = s := by
    rw [legInt_legendreBranchPower_real _ hx, show (x:ℂ)^2-1 = ((x^2-1:ℝ):ℂ) by push_cast; ring,
      hs_def, Real.sqrt_eq_rpow, ofReal_cpow (by nlinarith)]
    push_cast; ring_nf
  have hbm : legendreBranchPower (-1) x * s = 1 := by
    rw [← hb1, legendreBranchPower_mul, neg_add_cancel]; simp [legendreBranchPower]
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have h0 : ∀ k : ℕ, associatedP (k:ℂ) 0 x = legInt_Ks x k 0 / π := fun k => by
    rw [associatedP_zero_order _ hx1, legendreP_laplace _ hx.le, legInt_Ks,
      ← intervalIntegral.integral_ofReal]
    simp only [mul_zero, pow_zero, mul_one]
    rw [one_div_mul_eq_div]
    congr 1
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [legInt_w]
    rw [cpow_natCast, ofReal_pow]
  have hc0 : ∀ p : ℕ, legInt_cK 0 p = 1/π := fun p => by
    have := Nat.factorial_ne_zero p
    simp [legInt_cK]; field_simp
  have key : ∀ m : ℕ, (∀ p : ℕ, associatedP ((m+p:ℕ):ℂ) m x =
      legInt_cK m p * (s:ℂ)^m * legInt_Ks x p m) ∧ (∀ p : ℕ, associatedP ((m+1+p:ℕ):ℂ) (m+1:ℕ) x =
      legInt_cK (m+1) p * (s:ℂ)^(m+1) * legInt_Ks x p (m+1)) := by
    intro m
    induction m with
    | zero =>
      refine ⟨fun p => by rw [Nat.cast_zero, zero_add, h0, hc0]; simp; ring, fun p => ?_⟩
      have h7 := associatedP_recurrence_7 ((p+1:ℕ):ℂ) 0 hx1
      have hK := legInt_Ks_one x p
      rw [hb1, zero_add, show ((p+1:ℕ):ℂ)+1 = ((p+2:ℕ):ℂ) by push_cast; ring, h0, h0] at h7
      apply mul_left_cancel₀ hs
      apply_fun ((↑) : ℝ → ℂ) at hK
      have hc1 : legInt_cK 1 p = ((p:ℂ)+1)*((p:ℂ)+2)/π := by
        simp only [legInt_cK]
        rw [show 2*1+p = p+1+1 by ring]
        simp only [Nat.factorial_succ]
        push_cast
        have := Nat.factorial_ne_zero p
        field_simp
        ring
      rw [show 0+1+p = p+1 by ring, hc1]
      have hss : (s:ℂ)^2 = (x:ℂ)^2-1 := by
        rw [← ofReal_pow, hs_def, Real.sq_sqrt (by nlinarith)]; push_cast; ring
      push_cast at hK h7 ⊢
      rw [← hs_def] at hK
      linear_combination h7 + ((p:ℂ)+2)/π * hK
    | succ k ih =>
      refine ⟨ih.2, fun p => ?_⟩
      have h6 := associatedP_recurrence_6 ((k+1+1+p:ℕ):ℂ) (k:ℂ) hx1
      have e1 := ih.1 (p+2)
      have e2 := ih.2 (p+1)
      rw [show k+(p+2) = k+1+1+p by ring] at e1
      rw [show k+1+(p+1) = k+1+1+p by ring] at e2
      rw [show (k:ℂ)+1 = ((k+1:ℕ):ℂ) by push_cast; ring, e2,
        show (k:ℂ)+2 = ((k+1+1:ℕ):ℂ) by push_cast; ring, e1] at h6
      have hst := legInt_Ks_star x (p+1) k
      have hib := legInt_Ks_ibp x p (k+1)
      have hr1 := legInt_cK_succ k p
      have hr2 := legInt_cK_succ' k p
      have h23 : (2*(k:ℂ)+3) ≠ 0 := by norm_cast
      apply mul_left_cancel₀ (mul_ne_zero h23 hs)
      apply_fun ((↑) : ℝ → ℂ) at hst hib
      push_cast at hst hib h6 hr1 hr2 ⊢
      rw [← hs_def] at hib
      simp only [show k+1+1 = k+2 by ring] at h6 hib hst ⊢
      linear_combination (2*(k:ℂ)+3)*(s:ℂ)*h6
        - 2*((k:ℂ)+1)*(2*k+3)*x*legInt_cK (k+1) (p+1)*(s:ℂ)^(k+1)*(legInt_Ks x (p+1) (k+1):ℂ)*hbm
        - (2*(k:ℂ)+3)*(s:ℂ)^(k+1)*(legInt_Ks x (p+2) k:ℂ)*hr1
        - (s:ℂ)^(k+3)*(legInt_Ks x p (k+2):ℂ)*hr2
        - (2*(k:ℂ)+3)*legInt_cK (k+1) (p+1)*(s:ℂ)^(k+1)*hst
        - legInt_cK (k+1) (p+1)*(s:ℂ)^(k+1)*((p:ℂ)+2*k+4)*hib
  exact (key m).1 p

end DLMF.Legendre

end
