/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Integrals.FerrersGreen

/-!
# Diagonal Ferrers integrals and uniform parameter bounds

Parameter-uniform endpoint estimates justify the diagonal limits of Ferrers product integrals.

Source references and common attribution are retained in
`DLMF.Legendre.Integrals`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Legendre

/-! ### Parameter-uniform bounds and diagonal integrals

The zero-balanced expansion `legBd_zeroBalanced_eq` (DLMF 15.8.10 at `m = 0`) holds with a
remainder `legBdZbH` that is bounded uniformly in the parameters (Cauchy's estimate in the third
parameter, `legPIU_bound_H`). This gives `𝖯_λ, 𝖰_λ = O((1-x²)^{-1/4})` on `(-1,1)` uniformly for
`λ` near `ν`, and dominated convergence turns the off-diagonal integrals 14.17.10, 12, 14 into the
diagonal ones 14.17.11, 13, 15. Helper names carry the prefix `legPIU_`. -/

/-- Uniform bound for `𝐅(a,b;c;w)` on `‖a‖, ‖b‖, ‖c‖ ≤ R`, `‖w‖ ≤ 1/2`. -/
theorem legPIU_bound_F (R : ℝ) : ∃ M : ℝ, ∀ a b c w : ℂ, ‖a‖ ≤ R → ‖b‖ ≤ R → ‖c‖ ≤ R →
    ‖w‖ ≤ 1/2 → ‖regularizedGaussHGFun a b c w‖ ≤ M := by
  set S : Set (ℂ × ℂ × ℂ × ℂ) := Metric.closedBall 0 R ×ˢ (Metric.closedBall 0 R ×ˢ
    (Metric.closedBall 0 R ×ˢ Metric.closedBall 0 (1/2)))
  have hS : IsCompact S := (isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)))
  have hsub : S ⊆ {q : ℂ × ℂ × ℂ × ℂ | q.2.2.2 ∈ cutPlane} := by
    rintro ⟨a, b, c, w⟩ ⟨-, -, -, hw⟩
    simp only [Metric.mem_closedBall, dist_zero_right] at hw
    show 1 - w ∈ slitPlane
    refine Or.inl ?_
    have := Complex.re_le_norm w
    simp only [sub_re, one_re]; linarith
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn
    (differentiableOn_regularizedGaussHG_joint.continuousOn.mono hsub)
  refine ⟨M, fun a b c w ha hb hc hw => ?_⟩
  have hq : ((a, b, c, w) : ℂ × ℂ × ℂ × ℂ) ∈ S := by
    simp only [S, Set.mem_prod, Metric.mem_closedBall, dist_zero_right]
    exact ⟨ha, hb, hc, hw⟩
  have := hM _ hq
  rwa [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ (by linarith)] at this

/-- A continuous function is bounded on `‖a‖, ‖b‖ ≤ R`. -/
theorem legPIU_bound_two {f : ℂ × ℂ → ℂ} (hf : Continuous f) (R : ℝ) :
    ∃ M : ℝ, ∀ a b : ℂ, ‖a‖ ≤ R → ‖b‖ ≤ R → ‖f (a, b)‖ ≤ M := by
  obtain ⟨M, hM⟩ := ((isCompact_closedBall (0:ℂ) R).prod (isCompact_closedBall (0:ℂ) R)
    ).exists_bound_of_continuousOn hf.continuousOn
  exact ⟨M, fun a b ha hb => hM _ (by
    simp only [Set.mem_prod, Metric.mem_closedBall, dist_zero_right]; exact ⟨ha, hb⟩)⟩

/-- Uniform bound for the analytic part `H(a,b;w)` of DLMF 15.8.10 on `‖a‖, ‖b‖ ≤ R`,
`‖w‖ ≤ 1/2`, from Cauchy's estimate in the third parameter. -/
theorem legPIU_bound_H (R : ℝ) : ∃ M : ℝ, ∀ a b w : ℂ, ‖a‖ ≤ R → ‖b‖ ≤ R →
    ‖w‖ ≤ 1/2 → ‖legBdZbH a b w‖ ≤ M := by
  obtain ⟨MF, hMF⟩ := legPIU_bound_F (R+2)
  have cK : Continuous fun p : ℂ × ℂ => legBdK p.1 p.2 := by
    unfold legBdK
    exact (continuous_recip_Gamma.comp continuous_fst).mul (continuous_recip_Gamma.comp continuous_snd)
  have cK' : Continuous fun p : ℂ × ℂ => legBdK' p.1 p.2 := by
    unfold legBdK'
    have h1 := DLMF.Gamma.continuous_recipGammaDeriv 1
    exact ((h1.comp continuous_snd).mul (continuous_recip_Gamma.comp continuous_fst)).add
      ((continuous_recip_Gamma.comp continuous_snd).mul (h1.comp continuous_fst))
  obtain ⟨MK, hMK⟩ := legPIU_bound_two cK R
  obtain ⟨MK', hMK'⟩ := legPIU_bound_two cK' R
  refine ⟨MK * MF + MK' * MF + MK * MF, fun a b w ha hb hw => ?_⟩
  have hw1 : ‖w‖ < 1 := by linarith
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) ha
  have hMF0 : 0 ≤ MF := le_trans (norm_nonneg _) (hMF 0 0 0 0 (by simp; linarith)
    (by simp; linarith) (by simp; linarith) (by simp))
  have hK := hMK a b ha hb
  have hK' := hMK' a b ha hb
  -- first derivative
  have hd1 : ‖deriv (fun c => regularizedGaussHGFun a b (a+b-c+1) w) (a+b)‖ ≤ MF := by
    have hdiff : Differentiable ℂ (fun c => regularizedGaussHGFun a b (a+b-c+1) w) :=
      differentiable_regularizedGaussHGFun_of_differentiable (differentiable_const _)
        (differentiable_const _) ((differentiable_const _).sub differentiable_id |>.add_const 1) hw1
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := a+b) (R := 1) one_pos
      hdiff.diffContOnCl (C := MF) fun c hc => by
        rw [mem_sphere_iff_norm] at hc
        refine hMF _ _ _ _ (by linarith) (by linarith) ?_ hw
        calc ‖a+b-c+1‖ ≤ ‖a+b-c‖ + ‖(1:ℂ)‖ := norm_add_le _ _
          _ = 2 := by rw [← norm_neg, neg_sub, hc]; simp; norm_num
          _ ≤ R+2 := by linarith
    simpa using this
  have hd2 : ‖deriv (fun c => regularizedGaussHGFun (c-a) (c-b) (c-a-b+1) w) (a+b)‖ ≤ MF := by
    have hdiff : Differentiable ℂ (fun c => regularizedGaussHGFun (c-a) (c-b) (c-a-b+1) w) :=
      differentiable_regularizedGaussHGFun_of_differentiable (differentiable_id.sub_const _)
        (differentiable_id.sub_const _) ((differentiable_id.sub_const _).sub_const _ |>.add_const 1) hw1
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := a+b) (R := 1) one_pos
      hdiff.diffContOnCl (C := MF) fun c hc => by
        rw [mem_sphere_iff_norm] at hc
        refine hMF _ _ _ _ ?_ ?_ ?_ hw
        · calc ‖c-a‖ = ‖(c-(a+b)) + b‖ := by ring_nf
            _ ≤ ‖c-(a+b)‖ + ‖b‖ := norm_add_le _ _
            _ ≤ R+2 := by linarith
        · calc ‖c-b‖ = ‖(c-(a+b)) + a‖ := by ring_nf
            _ ≤ ‖c-(a+b)‖ + ‖a‖ := norm_add_le _ _
            _ ≤ R+2 := by linarith
        · calc ‖c-a-b+1‖ = ‖(c-(a+b)) + 1‖ := by ring_nf
            _ ≤ ‖c-(a+b)‖ + ‖(1:ℂ)‖ := norm_add_le _ _
            _ ≤ R+2 := by simp; linarith
    simpa using this
  have hF1 : ‖regularizedGaussHGFun a b 1 w‖ ≤ MF :=
    hMF _ _ _ _ (by linarith) (by linarith) (by simp; linarith) hw
  unfold legBdZbH
  calc _ ≤ ‖legBdK a b * deriv (fun c => regularizedGaussHGFun a b (a+b-c+1) w) (a+b)‖ +
        ‖legBdK' a b * regularizedGaussHGFun a b 1 w‖ +
        ‖legBdK a b * deriv (fun c => regularizedGaussHGFun (c-a) (c-b) (c-a-b+1) w) (a+b)‖ :=
        norm_sub_le_of_le (norm_add_le _ _) le_rfl
    _ ≤ MK * MF + MK' * MF + MK * MF := by
      rw [norm_mul, norm_mul, norm_mul]
      gcongr <;> first | exact le_trans (norm_nonneg _) hK | exact le_trans (norm_nonneg _) hK'

/-- `𝖯_α(x) = O((1-x²)^{-1/4})` on `(-1,1)` uniformly for `‖α‖ ≤ R`: the parameter-uniform form of
DLMF 15.8.10 at `m = 0` used for diagonal integrals. -/
theorem legPIU_bound_P (R : ℝ) : ∃ M : ℝ, ∀ α : ℂ, ‖α‖ ≤ R → ∀ x ∈ Ioo (-1:ℝ) 1,
    ‖ferrersP α 0 x‖ ≤ M * legPIw x := by
  set R1 := |R| + 1
  obtain ⟨MF, hMF⟩ := legPIU_bound_F R1
  obtain ⟨MH, hMH⟩ := legPIU_bound_H R1
  have cK : Continuous fun p : ℂ × ℂ => legBdK p.1 p.2 := by
    unfold legBdK
    exact (continuous_recip_Gamma.comp continuous_fst).mul (continuous_recip_Gamma.comp continuous_snd)
  obtain ⟨MK, hMK⟩ := legPIU_bound_two cK R1
  set A := max MF 0
  set B := 4 * max MK 0 * max MF 0 + max MH 0
  refine ⟨A + B, fun α hα x hx => ?_⟩
  have hR1 : R ≤ |R| := le_abs_self R
  have ha : ‖α+1‖ ≤ R1 := by
    calc ‖α+1‖ ≤ ‖α‖ + ‖(1:ℂ)‖ := norm_add_le _ _
      _ ≤ R1 := by simp only [norm_one, R1]; linarith
  have hb : ‖-α‖ ≤ R1 := by rw [norm_neg]; simp only [R1]; linarith
  have hone : ‖(1:ℂ)‖ ≤ R1 := by simp only [norm_one, R1]; linarith [abs_nonneg R]
  have hA0 : 0 ≤ A := le_max_right _ _
  have hB0 : 0 ≤ B := by positivity
  have hw1 := legPIw_one_le hx
  have hw0 := legPIw_pos hx
  rw [legPI_ferrersP_zero]
  by_cases hx0 : 0 ≤ x
  · have hn : ‖(1-(x:ℂ))/2‖ ≤ 1/2 := by
      rw [show (1-(x:ℂ))/2 = (((1-x)/2:ℝ):ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
        abs_le]
      constructor <;> linarith [hx.2]
    rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ (by linarith)]
    calc _ ≤ MF := hMF _ _ _ _ ha hb hone hn
      _ ≤ A := le_max_left _ _
      _ ≤ A + B := by linarith
      _ ≤ (A + B) * legPIw x := le_mul_of_one_le_right (by linarith) hw1
  · push Not at hx0
    set t : ℝ := (1+x)/2 with ht
    have ht0 : 0 < t := by simp only [t]; linarith [hx.1]
    have ht1 : t ≤ 1/2 := by simp only [t]; linarith
    have hz : (1-(x:ℂ))/2 = 1 - (t:ℂ) := by simp only [t]; push_cast; ring
    have hzn : ‖1 - (t:ℂ)‖ < 1 := by
      rw [show (1:ℂ) - t = ((1-t:ℝ):ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
        abs_lt]
      constructor <;> linarith
    have htn : ‖(1:ℂ) - (1 - (t:ℂ))‖ < 1 := by
      rw [sub_sub_cancel, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]; linarith
    rw [hz, regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hzn,
      show regularizedGaussHGFun (α+1) (-α) 1 (1 - (t:ℂ)) =
        regularizedGaussHGFun (α+1) (-α) ((α+1) + -α) (1 - (t:ℂ)) by
          rw [show (α+1) + -α = (1:ℂ) by ring],
      legBd_zeroBalanced_eq _ _ hzn htn, sub_sub_cancel, ← Complex.ofReal_log ht0.le]
    have htn' : ‖(t:ℂ)‖ ≤ 1/2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]; exact ht1
    have hF := hMF _ _ _ _ ha hb hone htn'
    have hH := hMH _ _ _ ha hb htn'
    have hK := hMK _ _ ha hb
    have hlog := legPI_abs_log_le ht0 (by linarith)
    have hp : 1 ≤ t^(-(1/4:ℝ)) := legPI_rpow_ge_one ht0 (by linarith)
    have hwt : t^(-(1/4:ℝ)) ≤ legPIw x := by
      rw [legPIw_eq hx]
      exact le_mul_of_one_le_right (Real.rpow_nonneg ht0.le _)
        (legPI_rpow_ge_one (by linarith [hx.2]) (by linarith [hx.1]))
    calc ‖-legBdK (α+1) (-α) * ((Real.log t : ℝ) : ℂ) * regularizedGaussHGFun (α+1) (-α) 1 (t:ℂ) +
          legBdZbH (α+1) (-α) (t:ℂ)‖
        ≤ ‖legBdK (α+1) (-α)‖ * |Real.log t| * ‖regularizedGaussHGFun (α+1) (-α) 1 (t:ℂ)‖ +
          ‖legBdZbH (α+1) (-α) (t:ℂ)‖ := by
          refine le_trans (norm_add_le _ _) ?_
          rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ max MK 0 * (4 * t^(-(1/4:ℝ))) * max MF 0 + max MH 0 := by
          gcongr
          · exact le_trans hK (le_max_left _ _)
          · exact le_trans hF (le_max_left _ _)
          · exact le_trans hH (le_max_left _ _)
      _ ≤ B * t^(-(1/4:ℝ)) := by
          simp only [B]
          nlinarith [le_max_right MK 0, le_max_right MF 0, le_max_right MH 0,
            mul_nonneg (le_max_right MK 0) (le_max_right MF 0)]
      _ ≤ (A + B) * legPIw x := by
          have := Real.rpow_nonneg ht0.le (-(1/4:ℝ))
          nlinarith

/-- `λ ↦ 𝖯_λ(x)` is entire for `x > -1`. -/
theorem legPIU_continuous_degree {x : ℝ} (hx : -1 < x) : Continuous fun α : ℂ => ferrersP α 0 x := by
  simp only [legPI_ferrersP_zero]
  exact (differentiable_regularizedGaussHG_comp (A := fun α : ℂ => α+1) (B := fun α : ℂ => -α)
    (C := fun _ => 1) (by fun_prop) (by fun_prop) (by fun_prop) (legInt_half_mem_cutPlane hx)).continuous

/-- Dominated convergence: `∫₋₁¹ 𝖯_ν 𝖯_λ → ∫₋₁¹ 𝖯_ν²` as `λ → ν`. -/
theorem legPIU_tendsto_PP (ν : ℂ) :
    Tendsto (fun lam : ℂ => ∫ x : ℝ in -1..1, ferrersP ν 0 x * ferrersP lam 0 x) (𝓝 ν)
      (𝓝 (∫ x : ℝ in -1..1, ferrersP ν 0 x * ferrersP ν 0 x)) := by
  obtain ⟨M, hM⟩ := legPIU_bound_P (‖ν‖ + 1)
  have hI := (legInt_intervalIntegrable_rpow (r := -1/2) (Or.inl rfl)).const_mul (M*M/4^(-1/2:ℝ))
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun x => M*M/4^(-1/2:ℝ) * (1-x^2)^(-1/2:ℝ)) ?_ ?_ hI ?_
  · refine Eventually.of_forall fun lam => ?_
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    intro x hx
    rw [Set.uIoc_of_le (by norm_num)] at hx
    exact ((legPI_continuousAt_ferrersP ν hx.1).mul
      (legPI_continuousAt_ferrersP lam hx.1)).continuousWithinAt
  · have hb : ∀ᶠ lam in 𝓝 ν, ‖lam‖ ≤ ‖ν‖ + 1 := by
      filter_upwards [Metric.ball_mem_nhds ν one_pos] with lam hl
      rw [Metric.mem_ball, dist_eq_norm] at hl
      calc ‖lam‖ = ‖ν + (lam - ν)‖ := by ring_nf
        _ ≤ ‖ν‖ + ‖lam - ν‖ := norm_add_le _ _
        _ ≤ ‖ν‖ + 1 := by linarith
    filter_upwards [hb] with lam hl
    filter_upwards [Measure.ae_ne volume (1:ℝ)] with x hx1 hx
    rw [Set.uIoc_of_le (by norm_num)] at hx
    have hx' : x ∈ Ioo (-1:ℝ) 1 := ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
    have h0 : 0 ≤ 1 - x^2 := by nlinarith [hx'.1, hx'.2]
    have hw : legPIw x * legPIw x = (1-x^2)^(-1/2:ℝ) / 4^(-1/2:ℝ) := by
      rw [legPIw, ← Real.rpow_add' (by positivity) (by norm_num), Real.div_rpow h0 (by norm_num)]
      norm_num
    have h1 := hM ν (by linarith) x hx'
    have h2 := hM lam hl x hx'
    rw [norm_mul]
    calc ‖ferrersP ν 0 x‖ * ‖ferrersP lam 0 x‖ ≤ (M * legPIw x) * (M * legPIw x) :=
          mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
      _ = M*M/4^(-1/2:ℝ)*(1-x^2)^(-1/2:ℝ) := by rw [mul_mul_mul_comm, hw]; ring
  · refine Eventually.of_forall fun x hx => ?_
    rw [Set.uIoc_of_le (by norm_num)] at hx
    exact tendsto_const_nhds.mul ((legPIU_continuous_degree hx.1).tendsto ν)

/-- Dominated convergence: `∫₋₁¹ 𝖯_λ² → ∫₋₁¹ 𝖯_ν²` as `λ → ν`. -/
theorem legPIU_tendsto_sq (ν : ℂ) :
    Tendsto (fun lam : ℂ => ∫ x : ℝ in -1..1, (ferrersP lam 0 x)^2) (𝓝 ν)
      (𝓝 (∫ x : ℝ in -1..1, (ferrersP ν 0 x)^2)) := by
  obtain ⟨M, hM⟩ := legPIU_bound_P (‖ν‖ + 1)
  have hI := (legInt_intervalIntegrable_rpow (r := -1/2) (Or.inl rfl)).const_mul (M*M/4^(-1/2:ℝ))
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun x => M*M/4^(-1/2:ℝ) * (1-x^2)^(-1/2:ℝ)) ?_ ?_ hI ?_
  · refine Eventually.of_forall fun lam => ?_
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    intro x hx
    rw [Set.uIoc_of_le (by norm_num)] at hx
    exact ((legPI_continuousAt_ferrersP lam hx.1).pow 2).continuousWithinAt
  · have hb : ∀ᶠ lam in 𝓝 ν, ‖lam‖ ≤ ‖ν‖ + 1 := by
      filter_upwards [Metric.ball_mem_nhds ν one_pos] with lam hl
      rw [Metric.mem_ball, dist_eq_norm] at hl
      calc ‖lam‖ = ‖ν + (lam - ν)‖ := by ring_nf
        _ ≤ ‖ν‖ + ‖lam - ν‖ := norm_add_le _ _
        _ ≤ ‖ν‖ + 1 := by linarith
    filter_upwards [hb] with lam hl
    filter_upwards [Measure.ae_ne volume (1:ℝ)] with x hx1 hx
    rw [Set.uIoc_of_le (by norm_num)] at hx
    have hx' : x ∈ Ioo (-1:ℝ) 1 := ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
    have h0 : 0 ≤ 1 - x^2 := by nlinarith [hx'.1, hx'.2]
    have hw : legPIw x * legPIw x = (1-x^2)^(-1/2:ℝ) / 4^(-1/2:ℝ) := by
      rw [legPIw, ← Real.rpow_add' (by positivity) (by norm_num), Real.div_rpow h0 (by norm_num)]
      norm_num
    have h2 := hM lam hl x hx'
    rw [norm_pow, pow_two]
    calc ‖ferrersP lam 0 x‖ * ‖ferrersP lam 0 x‖ ≤ (M * legPIw x) * (M * legPIw x) :=
          mul_le_mul h2 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h2)
      _ = M*M/4^(-1/2:ℝ)*(1-x^2)^(-1/2:ℝ) := by rw [mul_mul_mul_comm, hw]; ring
  · refine Eventually.of_forall fun x hx => ?_
    rw [Set.uIoc_of_le (by norm_num)] at hx
    exact ((legPIU_continuous_degree hx.1).tendsto ν).pow 2

/-- Uniform zero-balanced bound (DLMF 15.8.10 at `m = 0`):
`‖𝐅(a,b;a+b;1-t)‖ ≤ C t^{-1/4}` for `‖a‖, ‖b‖ ≤ R`, `0 < t ≤ 1/2`. -/
theorem legPIU_bound_zb (R : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℂ, ‖a‖ ≤ R → ‖b‖ ≤ R → ∀ t : ℝ, 0 < t →
    t ≤ 1/2 → ‖regularizedGaussHGFun a b (a+b) (1 - (t:ℂ))‖ ≤ C * t^(-(1/4:ℝ)) := by
  set R1 := |R| + 1
  obtain ⟨MF, hMF⟩ := legPIU_bound_F R1
  obtain ⟨MH, hMH⟩ := legPIU_bound_H R1
  have cK : Continuous fun p : ℂ × ℂ => legBdK p.1 p.2 := by
    unfold legBdK
    exact (continuous_recip_Gamma.comp continuous_fst).mul (continuous_recip_Gamma.comp continuous_snd)
  obtain ⟨MK, hMK⟩ := legPIU_bound_two cK R1
  refine ⟨4 * max MK 0 * max MF 0 + max MH 0, by positivity, fun a b ha hb t ht0 ht1 => ?_⟩
  have hR1 : R ≤ |R| := le_abs_self R
  have ha' : ‖a‖ ≤ R1 := by simp only [R1]; linarith
  have hb' : ‖b‖ ≤ R1 := by simp only [R1]; linarith
  have hone : ‖(1:ℂ)‖ ≤ R1 := by simp only [norm_one, R1]; linarith [abs_nonneg R]
  have hzn : ‖1 - (t:ℂ)‖ < 1 := by
    rw [show (1:ℂ) - t = ((1-t:ℝ):ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  have htn : ‖(1:ℂ) - (1 - (t:ℂ))‖ < 1 := by
    rw [sub_sub_cancel, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]; linarith
  rw [legBd_zeroBalanced_eq _ _ hzn htn, sub_sub_cancel, ← Complex.ofReal_log ht0.le]
  have htn' : ‖(t:ℂ)‖ ≤ 1/2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]; exact ht1
  have hF := hMF _ _ _ _ ha' hb' hone htn'
  have hH := hMH _ _ _ ha' hb' htn'
  have hK := hMK _ _ ha' hb'
  have hlog := legPI_abs_log_le ht0 (by linarith)
  have hp : 1 ≤ t^(-(1/4:ℝ)) := legPI_rpow_ge_one ht0 (by linarith)
  calc ‖-legBdK a b * ((Real.log t : ℝ) : ℂ) * regularizedGaussHGFun a b 1 (t:ℂ) + legBdZbH a b (t:ℂ)‖
      ≤ ‖legBdK a b‖ * |Real.log t| * ‖regularizedGaussHGFun a b 1 (t:ℂ)‖ + ‖legBdZbH a b (t:ℂ)‖ := by
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ max MK 0 * (4 * t^(-(1/4:ℝ))) * max MF 0 + max MH 0 := by
        gcongr
        · exact le_trans hK (le_max_left _ _)
        · exact le_trans hF (le_max_left _ _)
        · exact le_trans hH (le_max_left _ _)
    _ ≤ (4 * max MK 0 * max MF 0 + max MH 0) * t^(-(1/4:ℝ)) := by
        nlinarith [le_max_right MK 0, le_max_right MF 0, le_max_right MH 0,
          mul_nonneg (le_max_right MK 0) (le_max_right MF 0)]

/-- `‖𝐅(a,b;a+b;x²)‖ ≤ M (1-x²)^{-1/4}` on `(-1,1)`, uniformly for `‖a‖, ‖b‖ ≤ R`. -/
theorem legPIU_bound_sq (R : ℝ) : ∃ M : ℝ, ∀ a b : ℂ, ‖a‖ ≤ R → ‖b‖ ≤ R → ∀ x ∈ Ioo (-1:ℝ) 1,
    ‖regularizedGaussHG a b (a+b) ((x:ℂ)^2)‖ ≤ M * legPIw x := by
  obtain ⟨C, hC0, hC⟩ := legPIU_bound_zb R
  obtain ⟨MF, hMF⟩ := legPIU_bound_F (2*|R| + 1)
  refine ⟨max MF 0 + C, fun a b ha hb x hx => ?_⟩
  have hR1 : R ≤ |R| := le_abs_self R
  have hw1 := legPIw_one_le hx
  have hx2 : x^2 < 1 := by nlinarith [hx.1, hx.2]
  have hsq : ((x:ℂ))^2 = ((x^2:ℝ):ℂ) := by push_cast; ring
  have hn : ‖((x:ℂ))^2‖ < 1 := by
    rw [hsq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]; exact hx2
  rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hn]
  by_cases hx0 : x^2 ≤ 1/2
  · have hn' : ‖((x:ℂ))^2‖ ≤ 1/2 := by
      rw [hsq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]; exact hx0
    have hab : ‖a+b‖ ≤ 2*|R|+1 := by
      calc ‖a+b‖ ≤ ‖a‖+‖b‖ := norm_add_le _ _
        _ ≤ 2*|R|+1 := by linarith
    calc _ ≤ MF := hMF _ _ _ _ (by linarith [abs_nonneg R]) (by linarith [abs_nonneg R]) hab hn'
      _ ≤ max MF 0 + C := by linarith [le_max_left MF 0]
      _ ≤ (max MF 0 + C) * legPIw x :=
          le_mul_of_one_le_right (by linarith [le_max_right MF 0]) hw1
  · push Not at hx0
    set t : ℝ := 1 - x^2
    have ht0 : 0 < t := by simp only [t]; linarith
    have ht1 : t ≤ 1/2 := by simp only [t]; linarith
    rw [show ((x:ℂ))^2 = 1 - (t:ℂ) by simp only [t]; push_cast; ring]
    have hwt : t^(-(1/4:ℝ)) ≤ legPIw x := by
      rw [legPIw]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by simp only [t]; linarith) (by norm_num)
    calc _ ≤ C * t^(-(1/4:ℝ)) := hC a b ha hb t ht0 ht1
      _ ≤ (max MF 0 + C) * legPIw x := by
          have := Real.rpow_nonneg ht0.le (-(1/4:ℝ))
          nlinarith [le_max_right MF 0]

/-- A function continuous on a compact set is bounded there. -/
theorem legPIU_bound_on {f : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K) (hf : ContinuousOn f K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ K, ‖f y‖ ≤ B := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hf
  exact ⟨max B 0, le_max_right _ _, fun y hy => le_trans (hB y hy) (le_max_left _ _)⟩

/-- `𝖰_λ(x) = O((1-x²)^{-1/4})` on `(-1,1)` uniformly for `λ` near a regular `ν`. -/
theorem legPIU_bound_Q {ν : ℂ} (hν : LegendreQRegular ν 0) : ∃ r : ℝ, 0 < r ∧ ∃ M : ℝ,
    ∀ lam : ℂ, ‖lam - ν‖ ≤ r → LegendreQRegular lam 0 ∧
      ∀ x ∈ Ioo (-1:ℝ) 1, ‖ferrersQ lam 0 x‖ ≤ M * legPIw x := by
  have hν1 := legHyp_nu hν
  have o : IsOpen {lam : ℂ | (Gamma (lam+0+1))⁻¹ ≠ 0} :=
    isOpen_ne_fun (continuous_recip_Gamma.comp (by fun_prop)) continuous_const
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp o ν (by simpa using inv_ne_zero (Gamma_ne_zero hν1))
  set r := ε/2
  have hr : 0 < r := by positivity
  set K := Metric.closedBall ν r
  have hK : IsCompact K := isCompact_closedBall _ _
  have hreg : ∀ lam ∈ K, LegendreQRegular lam 0 := fun lam hl => legHyp_regular_of_recip (hball (by
    rw [Metric.mem_ball]; have := Metric.mem_closedBall.mp hl; simp only [r] at this; linarith))
  obtain ⟨B1, hB10, hB1⟩ := legPIU_bound_on (f := fun lam : ℂ => Gamma ((lam+0+1)/2)) hK
    (fun lam hl => (continuousAt_Gamma_ferrersQ (hreg lam hl)).1.continuousWithinAt)
  obtain ⟨B2, hB20, hB2⟩ := legPIU_bound_on (f := fun lam : ℂ => Gamma ((lam+0+2)/2)) hK
    (fun lam hl => (continuousAt_Gamma_ferrersQ (hreg lam hl)).2.continuousWithinAt)
  obtain ⟨B3, hB30, hB3⟩ := legPIU_bound_on (f := fun lam : ℂ => (Gamma ((lam-0+2)/2))⁻¹) hK
    (continuous_recip_Gamma.comp (by fun_prop)).continuousOn
  obtain ⟨B4, hB40, hB4⟩ := legPIU_bound_on (f := fun lam : ℂ => (Gamma ((lam-0+1)/2))⁻¹) hK
    (continuous_recip_Gamma.comp (by fun_prop)).continuousOn
  obtain ⟨B5, hB50, hB5⟩ := legPIU_bound_on (f := fun lam : ℂ => sin ((lam+0)*π/2)) hK
    (by fun_prop)
  obtain ⟨B6, hB60, hB6⟩ := legPIU_bound_on (f := fun lam : ℂ => cos ((lam+0)*π/2)) hK
    (by fun_prop)
  obtain ⟨MS, hMS⟩ := legPIU_bound_sq (‖ν‖ + r + 2)
  set MS' := max MS 0
  refine ⟨r, hr, (π/2) * (B5*B1*B3*MS' + B6*B2*B4*MS'), fun lam hl => ?_⟩
  have hlK : lam ∈ K := Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact hl)
  refine ⟨hreg lam hlK, fun x hx => ?_⟩
  have hlam : ‖lam‖ ≤ ‖ν‖ + r := by
    calc ‖lam‖ = ‖ν + (lam - ν)‖ := by ring_nf
      _ ≤ ‖ν‖ + ‖lam - ν‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hw0 := legPIw_pos hx
  have hxa : ‖(x:ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]; constructor <;> linarith [hx.1, hx.2]
  -- the two hypergeometric factors
  have hE : ‖ferrersEven lam 0 x‖ ≤ MS' * legPIw x := by
    unfold ferrersEven
    rw [show -(lam+0)/2 = -lam/2 by ring, show (lam-0+1)/2 = (lam+1)/2 by ring, neg_zero, zero_div,
      cpow_zero, one_mul, show (1/2:ℂ) = -lam/2 + (lam+1)/2 by ring]
    refine le_trans (hMS _ _ ?_ ?_ x hx) (mul_le_mul_of_nonneg_right (le_max_left _ _) hw0.le)
    · rw [norm_div, norm_neg]
      exact le_trans (div_le_self (norm_nonneg _) (by simp)) (by linarith)
    · calc ‖(lam+1)/2‖ ≤ ‖lam+1‖ := by rw [norm_div]; exact div_le_self (norm_nonneg _) (by simp)
        _ ≤ ‖lam‖ + 1 := by simpa using norm_add_le lam 1
        _ ≤ _ := by linarith
  have hO : ‖ferrersOdd lam 0 x‖ ≤ MS' * legPIw x := by
    unfold ferrersOdd
    rw [show (1-lam-0)/2 = (1-lam)/2 by ring, show (lam-0+2)/2 = (lam+2)/2 by ring, neg_zero, zero_div,
      cpow_zero, one_mul, show (3/2:ℂ) = (1-lam)/2 + (lam+2)/2 by ring, norm_mul]
    have h := hMS ((1-lam)/2) ((lam+2)/2) ?_ ?_ x hx
    · calc ‖(x:ℂ)‖ * _ ≤ 1 * (MS * legPIw x) := mul_le_mul hxa h (norm_nonneg _) zero_le_one
        _ ≤ MS' * legPIw x := by rw [one_mul]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hw0.le
    · calc ‖(1-lam)/2‖ ≤ ‖1-lam‖ := by rw [norm_div]; exact div_le_self (norm_nonneg _) (by simp)
        _ ≤ 1 + ‖lam‖ := by simpa using norm_sub_le (1:ℂ) lam
        _ ≤ _ := by linarith
    · calc ‖(lam+2)/2‖ ≤ ‖lam+2‖ := by rw [norm_div]; exact div_le_self (norm_nonneg _) (by simp)
        _ ≤ ‖lam‖ + 2 := by simpa using norm_add_le lam 2
        _ ≤ _ := by linarith
  rw [ferrersQ_even_odd, cpow_zero, one_mul]
  have hπ : ‖((π:ℂ))/2‖ = π/2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]; simp
  rw [norm_mul, hπ]
  have e1 := hB1 lam hlK; have e2 := hB2 lam hlK; have e3 := hB3 lam hlK
  have e4 := hB4 lam hlK; have e5 := hB5 lam hlK; have e6 := hB6 lam hlK
  have hMS0 : 0 ≤ MS' := le_max_right _ _
  calc π/2 * ‖-sin ((lam+0)*π/2)*Gamma ((lam+0+1)/2)*(Gamma ((lam-0+2)/2))⁻¹*ferrersEven lam 0 x +
        cos ((lam+0)*π/2)*Gamma ((lam+0+2)/2)*(Gamma ((lam-0+1)/2))⁻¹*ferrersOdd lam 0 x‖
      ≤ π/2 * (B5*B1*B3*(MS' * legPIw x) + B6*B2*B4*(MS' * legPIw x)) := by
        gcongr
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_mul, norm_mul, norm_mul, norm_neg, norm_mul, norm_mul, norm_mul]
        gcongr
    _ = _ := by ring

/-- Dominated convergence on `(-1,1)` with the weight `(1-x²)^{-1/4}`. -/
theorem legPIU_tendsto_int {F : ℂ → ℝ → ℂ} {f : ℝ → ℂ} {ν : ℂ} {M N : ℝ}
    (hf : ContinuousOn f (Ioo (-1) 1)) (hfN : ∀ x ∈ Ioo (-1:ℝ) 1, ‖f x‖ ≤ N * legPIw x)
    (hFc : ∀ lam, ContinuousOn (F lam) (Ioo (-1) 1))
    (hFM : ∀ᶠ lam in 𝓝 ν, ∀ x ∈ Ioo (-1:ℝ) 1, ‖F lam x‖ ≤ M * legPIw x)
    (hlim : ∀ x ∈ Ioo (-1:ℝ) 1, ContinuousAt (fun lam => F lam x) ν) :
    Tendsto (fun lam => ∫ x in (-1:ℝ)..1, f x * F lam x) (𝓝 ν)
      (𝓝 (∫ x in (-1:ℝ)..1, f x * F ν x)) := by
  have hI := (legInt_intervalIntegrable_rpow (r := -1/2) (Or.inl rfl)).const_mul (N*M/4^(-1/2:ℝ))
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun x => N*M/4^(-1/2:ℝ) * (1-x^2)^(-1/2:ℝ)) ?_ ?_ hI ?_
  · refine Eventually.of_forall fun lam => ?_
    rw [Set.uIoc_of_le (by norm_num : (-1:ℝ) ≤ 1), ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact (hf.mul (hFc lam)).aestronglyMeasurable measurableSet_Ioo
  · filter_upwards [hFM] with lam hl
    filter_upwards [Measure.ae_ne volume (1:ℝ)] with x hx1 hx
    rw [Set.uIoc_of_le (by norm_num)] at hx
    have hx' : x ∈ Ioo (-1:ℝ) 1 := ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
    have h0 : 0 ≤ 1 - x^2 := by nlinarith [hx'.1, hx'.2]
    have hw : legPIw x * legPIw x = (1-x^2)^(-1/2:ℝ) / 4^(-1/2:ℝ) := by
      rw [legPIw, ← Real.rpow_add' (by positivity) (by norm_num), Real.div_rpow h0 (by norm_num)]
      norm_num
    have h1 := hfN x hx'
    have h2 := hl x hx'
    rw [norm_mul]
    calc ‖f x‖ * ‖F lam x‖ ≤ (N * legPIw x) * (M * legPIw x) :=
          mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
      _ = N*M/4^(-1/2:ℝ)*(1-x^2)^(-1/2:ℝ) := by rw [mul_mul_mul_comm, hw]; ring
  · filter_upwards [Measure.ae_ne volume (1:ℝ)] with x hx1 hx
    rw [Set.uIoc_of_le (by norm_num)] at hx
    exact tendsto_const_nhds.mul (hlim x ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩).tendsto

/-- DLMF 14.17.10: for `λ ≠ ν`, `λ ≠ -ν-1` and `ν, λ ∉ {-1,-2,…}`, `∫_{-1}^{1} 𝖯_ν(x) 𝖯_λ(x) dx =
2(2 sin(νπ) sin(λπ)(ψ(ν+1) - ψ(λ+1)) + π sin((λ-ν)π))/(π² (λ-ν)(λ+ν+1))`. -/
@[dlmf 14.17.E10]
theorem ferrers_product_integral_10 (ν : ℂ) (lam : ℂ) (h0 : lam ≠ ν) (h1 : lam ≠ -ν-1) (hν : LegendreQRegular ν 0) (hlam : LegendreQRegular lam 0) :
    (∫ x : ℝ in -1..1, ferrersP ν 0 x*ferrersP lam 0 x)=2*(2*sin (ν*π)*sin (lam*π)*(digamma (ν+1)-digamma (lam+1))+π*sin ((lam-ν)*π))/(π^2*(lam-ν)*(lam+ν+1)) := by
  have hd1 : lam - ν ≠ 0 := sub_ne_zero.mpr h0
  have hd2 : lam + ν + 1 ≠ 0 := fun h => h1 (by linear_combination h)
  have hc : ν*(ν+1) - lam*(lam+1) ≠ 0 := by
    rw [show ν*(ν+1) - lam*(lam+1) = -((lam-ν)*(lam+ν+1)) by ring]
    exact neg_ne_zero.mpr (mul_ne_zero hd1 hd2)
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hB := legPI_boundary_const hν hlam
  rw [legPI_integral_PP ν lam hc, show 2*sin (ν*π)*sin (lam*π)*(digamma (ν+1)-digamma (lam+1))+
    π*sin ((lam-ν)*π) = (π:ℂ)^2 * (legPIK ν * legPIC lam - legPIK lam * legPIC ν) by
    rw [hB]; ring]
  field_simp
  ring

/-- DLMF 14.17.11: for `ν ≠ -1/2`, `ν ∉ {-1,-2,…}`, `∫_{-1}^{1} (𝖯_ν(x))² dx = (π² - 2 sin²(νπ)
ψ'(ν+1))/(π² (ν+1/2))`. -/
@[dlmf 14.17.E11]
theorem ferrers_product_integral_11 (ν : ℂ) (hν : ν ≠ -1/2) (hr : LegendreQRegular ν 0) :
    (∫ x : ℝ in -1..1, (ferrersP ν 0 x)^2)=(π^2-2*(sin (ν*π))^2*deriv digamma (ν+1))/(π^2*(ν+1/2)) := by
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2ν : 2*ν+1 ≠ 0 := fun h => hν (by linear_combination h/2)
  have hν1 := legHyp_nu hr
  -- the off-diagonal formula near `ν`
  set N : ℂ → ℂ := fun lam => 2*sin (ν*π)*sin (lam*π)*(digamma (ν+1)-digamma (lam+1))+π*sin ((lam-ν)*π)
  have hψ := (DLMF.Gamma.differentiableAt_digamma hν1).hasDerivAt
  have hψ' : HasDerivAt (fun lam : ℂ => digamma (lam+1)) (deriv digamma (ν+1)) ν := by
    have := hψ.comp ν ((hasDerivAt_id' ν).add_const 1)
    rw [mul_one] at this; exact this
  have hN : HasDerivAt N (2*sin (ν*π)*(cos (ν*π)*(1*π)*(digamma (ν+1)-digamma (ν+1)) +
      sin (ν*π)*(-deriv digamma (ν+1))) + π*(cos ((ν-ν)*π)*(1*π))) ν := by
    have hs := ((hasDerivAt_id' ν).mul_const (π:ℂ)).csin
    have hs2 := (((hasDerivAt_id' ν).sub_const ν).mul_const (π:ℂ)).csin
    have := ((hs.mul ((hasDerivAt_const ν (digamma (ν+1))).sub hψ')).const_mul (2*sin (ν*π))).add
      (hs2.const_mul (π:ℂ))
    simp only [Pi.mul_apply, Pi.sub_apply] at this
    convert this using 1
    · funext lam; simp only [N, Pi.add_apply]; ring
    · ring
  have hN0 : N ν = 0 := by simp [N]
  have hsl := hasDerivAt_iff_tendsto_slope.mp hN
  have hden : Tendsto (fun lam : ℂ => 2/(π^2*(lam+ν+1))) (𝓝[≠] ν) (𝓝 (2/(π^2*(ν+ν+1)))) := by
    refine ((continuousAt_const.div (continuousAt_const.mul ((continuousAt_id.add continuousAt_const).add
      continuousAt_const)) ?_).tendsto).mono_left nhdsWithin_le_nhds
    exact mul_ne_zero (pow_ne_zero 2 hπ) (by show ν + ν + 1 ≠ 0; rw [show ν+ν+1 = 2*ν+1 by ring]; exact h2ν)
  have hR := hsl.mul hden
  -- eventually the off-diagonal identity holds
  have hreg : ∀ᶠ lam in 𝓝 ν, LegendreQRegular lam 0 := by
    have o : IsOpen {lam : ℂ | (Gamma (lam+0+1))⁻¹ ≠ 0} :=
      isOpen_ne_fun (continuous_recip_Gamma.comp (by fun_prop)) continuous_const
    filter_upwards [o.mem_nhds (by simpa using inv_ne_zero (Gamma_ne_zero hν1))] with lam h
    exact legHyp_regular_of_recip h
  have hne : ∀ᶠ lam in 𝓝 ν, lam ≠ -ν-1 :=
    continuousAt_id.eventually_ne (show ν ≠ -ν-1 from fun h => h2ν (by linear_combination h))
  have heq : (fun lam : ℂ => ∫ x : ℝ in -1..1, ferrersP ν 0 x * ferrersP lam 0 x) =ᶠ[𝓝[≠] ν]
      fun lam => slope N ν lam * (2/(π^2*(lam+ν+1))) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hreg, nhdsWithin_le_nhds hne]
      with lam (h0 : lam ≠ ν) hl h1
    rw [ferrers_product_integral_10 ν lam h0 h1 hr hl, slope_def_field, hN0, sub_zero]
    have hd1 : lam - ν ≠ 0 := sub_ne_zero.mpr h0
    have hd2 : lam + ν + 1 ≠ 0 := fun h => h1 (by linear_combination h)
    simp only [N]
    field_simp
  have hu := tendsto_nhds_unique (((legPIU_tendsto_PP ν).mono_left nhdsWithin_le_nhds).congr' heq) hR
  simp only [pow_two]
  rw [hu]
  have h3 : ν + 1/2 ≠ 0 := fun h => h2ν (by linear_combination 2*h)
  rw [show ν+ν+1 = 2*(ν+1/2) by ring, sub_self, sub_self, zero_mul, Complex.cos_zero]
  generalize ν + 1/2 = u at h3 ⊢
  field_simp
  ring

/-- DLMF 14.17.12: for `λ ≠ ν`, `λ ≠ -ν-1` and `ν, λ ∉ {-1,-2,…}`, `∫_{-1}^{1} 𝖰_ν(x) 𝖰_λ(x) dx =
((ψ(ν+1) - ψ(λ+1))(1 + cos(νπ) cos(λπ)) + (π/2) sin((λ-ν)π))/((λ-ν)(λ+ν+1))`. -/
@[dlmf 14.17.E12]
theorem ferrers_product_integral_12 (ν : ℂ) (lam : ℂ) (h0 : lam ≠ ν) (h1 : lam ≠ -ν-1) (hν : LegendreQRegular ν 0) (hlam : LegendreQRegular lam 0) :
    (∫ x : ℝ in -1..1, ferrersQ ν 0 x*ferrersQ lam 0 x)=((digamma (ν+1)-digamma (lam+1))*(1+cos (ν*π)*cos (lam*π))+π/2*sin ((lam-ν)*π))/((lam-ν)*(lam+ν+1)) := by
  have hd1 : lam - ν ≠ 0 := sub_ne_zero.mpr h0
  have hd2 : lam + ν + 1 ≠ 0 := fun h => h1 (by linear_combination h)
  have hc : ν*(ν+1) - lam*(lam+1) ≠ 0 := by
    rw [show ν*(ν+1) - lam*(lam+1) = -((lam-ν)*(lam+ν+1)) by ring]
    exact neg_ne_zero.mpr (mul_ne_zero hd1 hd2)
  rw [legPI_integral_QQ hν hlam hc, show ν*(ν+1) - lam*(lam+1) = -((lam-ν)*(lam+ν+1)) by ring,
    show (lam-ν)*π = lam*π - ν*π by ring, sin_sub]
  unfold legPIcneg legPIcpos
  field_simp
  ring

/-- DLMF 14.17.13: for `ν ≠ -1/2`, `ν ∉ {-1,-2,…}`, `∫_{-1}^{1} (𝖰_ν(x))² dx = (π²/2 - (1 +
cos²(νπ)) ψ'(ν+1))/(2ν+1)`. -/
@[dlmf 14.17.E13]
theorem ferrers_product_integral_13 (ν : ℂ) (hν : ν ≠ -1/2) (hr : LegendreQRegular ν 0) :
    (∫ x : ℝ in -1..1, (ferrersQ ν 0 x)^2)=(π^2-2*(1+(cos (ν*π))^2)*deriv digamma (ν+1))/(2*(2*ν+1)) := by
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2ν : 2*ν+1 ≠ 0 := fun h => hν (by linear_combination h/2)
  have hν1 := legHyp_nu hr
  obtain ⟨r, hr0, M, hM⟩ := legPIU_bound_Q hr
  have hnear : ∀ᶠ lam in 𝓝 ν, ‖lam - ν‖ ≤ r := by
    filter_upwards [Metric.closedBall_mem_nhds ν hr0] with lam hl
    rwa [Metric.mem_closedBall, dist_eq_norm] at hl
  have hlimI := legPIU_tendsto_int (F := fun lam x => ferrersQ lam 0 x) (f := ferrersQ ν 0)
    (legPI_continuousOn_of_solution (legPI_ferrersQ_isFerrersSolution ν))
    ((hM ν (by simp; linarith)).2)
    (fun lam => legPI_continuousOn_of_solution (legPI_ferrersQ_isFerrersSolution lam))
    (by filter_upwards [hnear] with lam hl using (hM lam hl).2)
    (fun x hx => continuousAt_ferrersQ_degree hr hx)
  set N : ℂ → ℂ := fun lam => (digamma (ν+1)-digamma (lam+1))*(1+cos (ν*π)*cos (lam*π))+π/2*sin ((lam-ν)*π)
  have hψ := (DLMF.Gamma.differentiableAt_digamma hν1).hasDerivAt
  have hψ' : HasDerivAt (fun lam : ℂ => digamma (lam+1)) (deriv digamma (ν+1)) ν := by
    have := hψ.comp ν ((hasDerivAt_id' ν).add_const 1)
    rw [mul_one] at this; exact this
  have hN : HasDerivAt N ((0 - deriv digamma (ν+1)) * (1+cos (ν*π)*cos (ν*π)) +
      (digamma (ν+1)-digamma (ν+1)) * (cos (ν*π) * (-sin (ν*π) * (1*π))) +
      π/2*(cos ((ν-ν)*π)*(1*π))) ν := by
    have hc := ((hasDerivAt_id' ν).mul_const (π:ℂ)).ccos
    have hs2 := (((hasDerivAt_id' ν).sub_const ν).mul_const (π:ℂ)).csin
    have := (((hasDerivAt_const ν (digamma (ν+1))).sub hψ').mul
      ((hasDerivAt_const ν (1:ℂ)).add (hc.const_mul (cos (ν*π))))).add (hs2.const_mul ((π:ℂ)/2))
    simp only [Pi.sub_apply, zero_add] at this
    convert this using 1
  have hN0 : N ν = 0 := by simp [N]
  have hsl := hasDerivAt_iff_tendsto_slope.mp hN
  have hden : Tendsto (fun lam : ℂ => 1/(lam+ν+1)) (𝓝[≠] ν) (𝓝 (1/(ν+ν+1))) := by
    refine ((continuousAt_const.div ((continuousAt_id.add continuousAt_const).add
      continuousAt_const) ?_).tendsto).mono_left nhdsWithin_le_nhds
    show ν + ν + 1 ≠ 0; rw [show ν+ν+1 = 2*ν+1 by ring]; exact h2ν
  have hR := hsl.mul hden
  have hne : ∀ᶠ lam in 𝓝 ν, lam ≠ -ν-1 :=
    continuousAt_id.eventually_ne (show ν ≠ -ν-1 from fun h => h2ν (by linear_combination h))
  have heq : (fun lam : ℂ => ∫ x : ℝ in -1..1, ferrersQ ν 0 x * ferrersQ lam 0 x) =ᶠ[𝓝[≠] ν]
      fun lam => slope N ν lam * (1/(lam+ν+1)) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hnear, nhdsWithin_le_nhds hne]
      with lam (h0 : lam ≠ ν) hl h1
    rw [ferrers_product_integral_12 ν lam h0 h1 hr (hM lam hl).1, slope_def_field, hN0, sub_zero]
    have hd1 : lam - ν ≠ 0 := sub_ne_zero.mpr h0
    have hd2 : lam + ν + 1 ≠ 0 := fun h => h1 (by linear_combination h)
    simp only [N]
    field_simp
  have hu := tendsto_nhds_unique (((hlimI).mono_left nhdsWithin_le_nhds).congr' heq) hR
  simp only [pow_two]
  rw [hu]
  have h3 : ν + 1/2 ≠ 0 := fun h => h2ν (by linear_combination 2*h)
  rw [show ν+ν+1 = 2*(ν+1/2) by ring, show 2*ν+1 = 2*(ν+1/2) by ring]
  simp only [sub_self, zero_mul, Complex.cos_zero, add_zero, one_mul]
  generalize ν + 1/2 = u at h3 ⊢
  field_simp
  ring

/-- DLMF 14.17.14: for `Re ν > 0`, `Re λ > 0` and `λ ≠ ν`, `∫_{-1}^{1} 𝖯_ν(x) 𝖰_λ(x) dx = (2 sin(νπ)
cos(λπ)(ψ(ν+1) - ψ(λ+1)) + π cos((λ-ν)π) - π)/(π (λ-ν)(λ+ν+1))`. -/
@[dlmf 14.17.E14]
theorem ferrers_product_integral_14 (ν : ℂ) (lam : ℂ) (hν : 0 < ν.re) (hlam : 0 < lam.re) (hne : lam ≠ ν) :
    (∫ x : ℝ in -1..1, ferrersP ν 0 x*ferrersQ lam 0 x)=(2*sin (ν*π)*cos (lam*π)*(digamma (ν+1)-digamma (lam+1))+π*cos ((lam-ν)*π)-π)/(π*(lam-ν)*(lam+ν+1)) := by
  have hrν := legPI_regular_of_re_pos hν
  have hrl := legPI_regular_of_re_pos hlam
  have hd1 : lam - ν ≠ 0 := sub_ne_zero.mpr hne
  have hd2 : lam + ν + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hc : ν*(ν+1) - lam*(lam+1) ≠ 0 := by
    rw [show ν*(ν+1) - lam*(lam+1) = -((lam-ν)*(lam+ν+1)) by ring]
    exact neg_ne_zero.mpr (mul_ne_zero hd1 hd2)
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hK : legBdK (ν+1) (-ν) = -sin (ν*π)/π := by
    rw [eq_div_iff hpi, mul_comm, legPI_K_eq ν, mul_comm]
  rw [legPI_integral_PQ hrl hc, show ν*(ν+1) - lam*(lam+1) = -((lam-ν)*(lam+ν+1)) by ring,
    show (lam-ν)*π = lam*π - ν*π by ring, cos_sub]
  unfold legPIcneg legPIcpos legPIC legPIK
  rw [legPI_K'_eq (legHyp_nu hrν), hK, show (π:ℂ)*ν = ν*π by ring]
  field_simp
  ring

/-- DLMF 14.17.15: for `Re ν > 0`, `∫_{-1}^{1} 𝖯_ν(x) 𝖰_ν(x) dx = -sin(2νπ) ψ'(ν+1)/(π (2ν+1))`. -/
@[dlmf 14.17.E15]
theorem ferrers_product_integral_15 (ν : ℂ) (hν : 0 < ν.re) :
    (∫ x : ℝ in -1..1, ferrersP ν 0 x*ferrersQ ν 0 x)=-sin (2*ν*π)*deriv digamma (ν+1)/(π*(2*ν+1)) := by
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hr := legPI_regular_of_re_pos hν
  have h2ν : 2*ν+1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hν1 := legHyp_nu hr
  obtain ⟨r, hr0, M, hM⟩ := legPIU_bound_Q hr
  obtain ⟨MP, hMP⟩ := legPIU_bound_P ‖ν‖
  have hnear : ∀ᶠ lam in 𝓝 ν, ‖lam - ν‖ ≤ r := by
    filter_upwards [Metric.closedBall_mem_nhds ν hr0] with lam hl
    rwa [Metric.mem_closedBall, dist_eq_norm] at hl
  have hlimI := legPIU_tendsto_int (F := fun lam x => ferrersQ lam 0 x) (f := ferrersP ν 0)
    (legPI_continuousOn_ferrersP ν) (hMP ν le_rfl)
    (fun lam => legPI_continuousOn_of_solution (legPI_ferrersQ_isFerrersSolution lam))
    (by filter_upwards [hnear] with lam hl using (hM lam hl).2)
    (fun x hx => continuousAt_ferrersQ_degree hr hx)
  set N : ℂ → ℂ := fun lam => 2*sin (ν*π)*cos (lam*π)*(digamma (ν+1)-digamma (lam+1))+π*cos ((lam-ν)*π)-π
  have hψ := (DLMF.Gamma.differentiableAt_digamma hν1).hasDerivAt
  have hψ' : HasDerivAt (fun lam : ℂ => digamma (lam+1)) (deriv digamma (ν+1)) ν := by
    have := hψ.comp ν ((hasDerivAt_id' ν).add_const 1)
    rw [mul_one] at this; exact this
  have hN : HasDerivAt N (2*sin (ν*π)*(-sin (ν*π)*(1*π)*(digamma (ν+1)-digamma (ν+1)) +
      cos (ν*π)*(0-deriv digamma (ν+1))) + π*(-sin ((ν-ν)*π)*(1*π))) ν := by
    have hc := ((hasDerivAt_id' ν).mul_const (π:ℂ)).ccos
    have hc2 := (((hasDerivAt_id' ν).sub_const ν).mul_const (π:ℂ)).ccos
    have := (((hc.mul ((hasDerivAt_const ν (digamma (ν+1))).sub hψ')).const_mul (2*sin (ν*π))).add
      (hc2.const_mul (π:ℂ))).sub_const (π:ℂ)
    simp only [Pi.mul_apply, Pi.sub_apply] at this
    convert this using 1
    funext lam; simp only [N, Pi.add_apply]; ring
  have hN0 : N ν = 0 := by simp [N]
  have hsl := hasDerivAt_iff_tendsto_slope.mp hN
  have hden : Tendsto (fun lam : ℂ => 1/(π*(lam+ν+1))) (𝓝[≠] ν) (𝓝 (1/(π*(ν+ν+1)))) := by
    refine ((continuousAt_const.div (continuousAt_const.mul ((continuousAt_id.add continuousAt_const).add
      continuousAt_const)) ?_).tendsto).mono_left nhdsWithin_le_nhds
    exact mul_ne_zero hπ (by show ν + ν + 1 ≠ 0; rw [show ν+ν+1 = 2*ν+1 by ring]; exact h2ν)
  have hR := hsl.mul hden
  have hre : ∀ᶠ lam in 𝓝 ν, 0 < lam.re :=
    Complex.continuous_re.continuousAt.eventually (lt_mem_nhds hν)
  have heq : (fun lam : ℂ => ∫ x : ℝ in -1..1, ferrersP ν 0 x * ferrersQ lam 0 x) =ᶠ[𝓝[≠] ν]
      fun lam => slope N ν lam * (1/(π*(lam+ν+1))) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hre] with lam (h0 : lam ≠ ν) hl
    rw [ferrers_product_integral_14 ν lam hν hl h0, slope_def_field, hN0, sub_zero]
    have hd1 : lam - ν ≠ 0 := sub_ne_zero.mpr h0
    have hd2 : lam + ν + 1 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    simp only [N]
    field_simp
  have hu := tendsto_nhds_unique (((hlimI).mono_left nhdsWithin_le_nhds).congr' heq) hR
  rw [hu, show 2*ν*π = 2*(ν*π) by ring, Complex.sin_two_mul, sub_self, sub_self, zero_mul,
    Complex.sin_zero, neg_zero, zero_mul, mul_zero, zero_add, mul_zero, add_zero,
    show ν+ν+1 = 2*ν+1 by ring]
  field_simp
  ring

/-- Green's identity for two Legendre solutions of the same order `μ`. -/
theorem legPI_green_mu {ν lam μ : ℂ} {f g : ℝ → ℂ} (hf : IsFerrersSolution ν μ f)
    (hg : IsFerrersSolution lam μ g) {y : ℝ} (hy : y ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (fun y : ℝ => (1-(y:ℂ)^2)*(f y*deriv g y-g y*deriv f y))
      ((ν*(ν+1) - lam*(lam+1)) * (f y * g y)) y := by
  obtain ⟨hf1, f2, hf2, ef⟩ := hf y hy
  obtain ⟨hg1, g2, hg2, eg⟩ := hg y hy
  have hsq : HasDerivAt (fun y : ℝ => 1-(y:ℂ)^2) (-(2*(y:ℂ))) y := by
    have := ((hasDerivAt_id y).ofReal_comp.pow 2).const_sub 1
    simpa using this
  refine (hsq.mul ((hf1.hasDerivAt.mul hg2).sub (hg1.hasDerivAt.mul hf2))).congr_deriv ?_
  simp only [Pi.mul_apply, Pi.sub_apply]
  linear_combination (f y)*eg-(g y)*ef

/-- Green's identity on `[-1,1]` for two solutions of the same order, in terms of the limits of a
function `B` equal to the boundary form `(1-x²)(f g' - g f')` on `(-1,1)`. -/
theorem legPI_integral_green_B {f g B : ℝ → ℂ} {ν lam μ Bm Bp : ℂ}
    (hf : IsFerrersSolution ν μ f) (hg : IsFerrersSolution lam μ g)
    (hB : ∀ x ∈ Ioo (-1:ℝ) 1, (1-(x:ℂ)^2)*(f x*deriv g x - g x*deriv f x) = B x)
    (hint : IntervalIntegrable (fun x => f x * g x) volume (-1) 1)
    (hm : Tendsto B (𝓝[>] (-1)) (𝓝 Bm)) (hp : Tendsto B (𝓝[<] 1) (𝓝 Bp))
    (hc : ν*(ν+1) - lam*(lam+1) ≠ 0) :
    (∫ x : ℝ in -1..1, f x * g x) = (Bp - Bm) / (ν*(ν+1) - lam*(lam+1)) := by
  set F : ℝ → ℂ := fun y => (1-(y:ℂ)^2)*(f y*deriv g y - g y*deriv f y) with hF
  have hd : ∀ y ∈ Ioo (-1:ℝ) 1, HasDerivAt F ((ν*(ν+1) - lam*(lam+1)) * (f y * g y)) y :=
    fun y hy => legPI_green_mu hf hg hy
  have hint' := hint.const_mul (ν*(ν+1) - lam*(lam+1))
  have ha := hm.congr' (by
    filter_upwards [Ioo_mem_nhdsGT (show (-1:ℝ) < 1 by norm_num)] with y hy using (hB y hy).symm)
  have hb := hp.congr' (by
    filter_upwards [Ioo_mem_nhdsLT (show (-1:ℝ) < 1 by norm_num)] with y hy using (hB y hy).symm)
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (by norm_num) hd hint' ha hb
  rw [intervalIntegral.integral_const_mul] at hI
  rw [eq_div_iff hc, ← hI]; ring

/-- A solution of the associated Legendre equation is continuous on `(-1,1)`. -/
theorem legPI_continuousOn_of_solution' {α μ : ℂ} {f : ℝ → ℂ} (hf : IsFerrersSolution α μ f) :
    ContinuousOn f (Ioo (-1) 1) :=
  fun y hy => (hf y hy).1.continuousAt.continuousWithinAt

/-- `(k+1)_j · k! = (k+j)!`. -/
theorem legPI_poch_nat (k j : ℕ) : poch ((k:ℂ)+1) j * (k.factorial : ℂ) = ((k+j).factorial : ℂ) := by
  induction j with
  | zero => simp [poch_zero]
  | succ j ih =>
    rw [poch_succ, mul_right_comm, ih, show k + (j+1) = (k+j)+1 by ring, Nat.factorial_succ]
    push_cast; ring

/-- `𝖯^m_k 𝖰^m_j → (k+m)!/((k-m)! 2m)` as `x → 1⁻`, for `1 ≤ m ≤ k`. -/
theorem legPI_tendsto_PQ_one {k j m : ℕ} (hm : 0 < m) (hk : m ≤ k) :
    Tendsto (fun x : ℝ => ferrersP k m x * ferrersQ j m x) (𝓝[<] (1:ℝ))
      (𝓝 (((k+m).factorial : ℂ) / ((k-m).factorial * (2*m)))) := by
  have hp : poch ((k:ℂ)-m+1) (2*m) ≠ 0 := by
    have := legPI_poch_nat (k-m) (2*m)
    rw [show ((k-m:ℕ):ℂ) = (k:ℂ) - m by push_cast [hk]; ring] at this
    intro h; rw [h, zero_mul] at this
    exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) this.symm
  have h1 := legendre_singular_2 (k:ℂ) m hm hp
  have hreg : LegendreQRegular (j:ℂ) (m:ℂ) := fun n hn => by
    have := congrArg Complex.re hn; simp at this
    linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n), (Nat.cast_nonneg j : (0:ℝ) ≤ j),
      (Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  have hμ : 0 < ((m:ℂ)).re := by simp; exact_mod_cast hm
  have hh : ∀ n : ℕ, (m:ℂ) ≠ n+1/2 := fun n hn => by
    have := congrArg Complex.re hn; simp at this
    have h2 : (2:ℝ)*m = 2*n+1 := by linarith
    have h3 : (2*m : ℕ) = 2*n+1 := by exact_mod_cast h2
    omega
  have h2 := legendre_singular_4 (j:ℂ) (m:ℂ) hreg hμ hh
  have h3 := h1.mul h2
  set c : ℂ := (-1)^m*poch ((k:ℂ)-m+1) (2*m)/(m.factorial:ℂ) * (1/2*cos ((m:ℂ)*π)*Gamma m)
    with hc
  have h4 : (fun x : ℝ => (-1)^m*poch ((k:ℂ)-m+1) (2*m)/(m.factorial:ℂ)*((1-x)/2:ℂ)^((m:ℂ)/2) *
      (1/2*cos ((m:ℂ)*π)*Gamma m*(2/(1-x):ℂ)^((m:ℂ)/2))) =ᶠ[𝓝[<] (1:ℝ)] (fun _ => c) := by
    filter_upwards [self_mem_nhdsWithin] with x (hx : x < 1)
    have h1x : (0:ℝ) < 1 - x := by linarith
    have e : ((1-x)/2:ℂ)^((m:ℂ)/2) * (2/(1-x):ℂ)^((m:ℂ)/2) = 1 := by
      rw [show ((1-x)/2:ℂ) = (((1-x)/2:ℝ):ℂ) by push_cast; ring,
        show (2/(1-x):ℂ) = ((2/(1-x):ℝ):ℂ) by push_cast; ring,
        ← mul_cpow_ofReal_nonneg (by positivity) (by positivity), ← ofReal_mul,
        show (1-x)/2*(2/(1-x)) = 1 by field_simp]
      simp
    rw [hc]
    linear_combination ((-1)^m*poch ((k:ℂ)-m+1) (2*m)/(m.factorial:ℂ) *
      (1/2*cos ((m:ℂ)*π)*Gamma m)) * e
  have h5 := (h3.congr_right h4).symm.tendsto_nhds (tendsto_const_nhds (x := c))
  convert h5 using 2
  obtain ⟨m', rfl⟩ : ∃ m' : ℕ, m = m' + 1 := ⟨m - 1, by omega⟩
  have hpn := legPI_poch_nat (k-(m'+1)) (2*(m'+1))
  rw [show ((k-(m'+1):ℕ):ℂ) = (k:ℂ) - ((m'+1:ℕ):ℂ) by push_cast [hk]; ring,
    show k-(m'+1)+2*(m'+1) = k+(m'+1) by omega] at hpn
  have hcos : cos (((m'+1:ℕ):ℂ)*π) = (-1)^(m'+1) := by
    rw [show (((m'+1:ℕ):ℂ)*π) = ((((m'+1:ℕ):ℝ)*π : ℝ):ℂ) by push_cast; ring, ← ofReal_cos,
      Real.cos_nat_mul_pi]
    push_cast; ring
  have hG : Gamma ((m'+1:ℕ):ℂ) = (m'.factorial : ℂ) := by
    rw [show ((m'+1:ℕ):ℂ) = (m':ℂ)+1 by push_cast; ring, Complex.Gamma_nat_eq_factorial]
  have hsq : ((-1:ℂ)^(m'+1))^2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hf0 : ((k-(m'+1)).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hm0 : ((m':ℂ)+1) ≠ 0 := by norm_cast
  have hmf : (m'.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [hc, hcos, hG, ← hpn, Nat.factorial_succ]
  push_cast
  field_simp
  linear_combination (-poch ((k:ℂ)-((m':ℂ)+1)+1) (2*(m'+1))) * hsq

/-- `𝖯^m_k 𝖰^m_j → (-1)^{k+j+1} (k+m)!/((k-m)! 2m)` as `x → -1⁺`, for `1 ≤ m ≤ k`. -/
theorem legPI_tendsto_PQ_neg_one {k j m : ℕ} (hm : 0 < m) (hk : m ≤ k) :
    Tendsto (fun x : ℝ => ferrersP k m x * ferrersQ j m x) (𝓝[>] (-1:ℝ))
      (𝓝 ((-1)^(k+j+1) * (((k+m).factorial : ℂ) / ((k-m).factorial * (2*m))))) := by
  have h := ((legPI_tendsto_PQ_one (j := j) hm hk).comp legPI_tendsto_neg_left).const_mul
    ((-1:ℂ)^(k+j+1))
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (-1:ℝ) < 1 by norm_num)] with x hx
  have hx' : -x ∈ Ioo (-1:ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hP := ferrersP_neg_of_add_eq_nat (ν := (k:ℂ)) (μ := (m:ℂ)) (N := k+m) (by push_cast; ring) hx'
  have hQ := ferrersQ_neg_of_add_eq_nat (ν := (j:ℂ)) (μ := (m:ℂ)) (N := j+m) (by push_cast; ring) (-x)
  rw [neg_neg] at hP hQ
  simp only [Function.comp_apply]
  rw [hP, hQ]
  have : ((-1:ℂ)^(k+m) * (-1)^(j+m+1)) = (-1)^(k+j+1) := by
    rw [← pow_add, show k+m+(j+m+1) = (k+j+1) + 2*m by ring, pow_add, pow_mul]; norm_num
  linear_combination -(ferrersP (k:ℂ) (m:ℂ) (-x) * ferrersQ (j:ℂ) (m:ℂ) (-x)) * this

/-- A function continuous on `(-1,1)` with finite limits at both ends is integrable on `[-1,1]`. -/
theorem legPI_intervalIntegrable_of_tendsto {h : ℝ → ℂ} (hc : ContinuousOn h (Ioo (-1) 1)) {a b : ℂ}
    (ha : Tendsto h (𝓝[>] (-1:ℝ)) (𝓝 a)) (hb : Tendsto h (𝓝[<] (1:ℝ)) (𝓝 b)) :
    IntervalIntegrable h volume (-1) 1 := by
  obtain ⟨M, hM⟩ := legPI_bound hc ((ha.isBigO_one ℝ).trans legPI_one_isBigO_left)
    ((hb.isBigO_one ℝ).trans legPI_one_isBigO_right)
  have h1 : ∀ x ∈ Ioo (-1:ℝ) 1, ‖(fun _ : ℝ => (1:ℂ)) x‖ ≤ 1 * legPIw x := fun x hx => by
    simp only [norm_one, one_mul]; exact legPIw_one_le hx
  have := legPI_intervalIntegrable_mul hc continuousOn_const hM h1
  simpa using this

/-- DLMF 14.17.16 for positive order. -/
theorem legPI_PQ_nat_pos (l m n : ℕ) (hm : 0 < m) (h : l ≠ n) (hl : m ≤ l) :
    (∫ x : ℝ in -1..1, ferrersP l m x*ferrersQ n m x) =
      (1-(-1)^(l+n))*((l+m).factorial:ℂ)/(((l:ℂ)-n)*(l+n+1:ℂ)*(l-m).factorial) := by
  have hreg : ∀ j : ℕ, LegendreQRegular (j:ℂ) (m:ℂ) := fun j n hn => by
    have := congrArg Complex.re hn; simp at this
    linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n), (Nat.cast_nonneg j : (0:ℝ) ≤ j),
      (Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  set c : ℕ → ℂ := fun k => ((k+m).factorial : ℂ) / ((k-m).factorial * (2*m)) with hcdef
  set B : ℝ → ℂ := fun x => (m-n-1:ℂ)*(ferrersP l m x * ferrersQ (n+1:ℕ) m x) +
    (n+1:ℂ)*x*(ferrersP l m x * ferrersQ n m x) -
    (m-l-1:ℂ)*(ferrersP (l+1:ℕ) m x * ferrersQ n m x) -
    (l+1:ℂ)*x*(ferrersP l m x * ferrersQ n m x) with hB
  have hBeq : ∀ x ∈ Ioo (-1:ℝ) 1, (1-(x:ℂ)^2)*(ferrersP l m x*deriv (ferrersQ n m) x -
      ferrersQ n m x*deriv (ferrersP l m) x) = B x := by
    intro x hx
    have r1 := ferrersP_recurrence_4 (l:ℂ) (m:ℂ) hx
    have r2 := ferrersQ_recurrence_4 (n:ℂ) (m:ℂ) (hreg n) hx
    simp only [hB]
    push_cast
    linear_combination ferrersP (l:ℂ) (m:ℂ) x * r2 - ferrersQ (n:ℂ) (m:ℂ) x * r1
  have hx1 : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[<] (1:ℝ)) (𝓝 1) := by
    have := (continuous_ofReal.tendsto (1:ℝ)).mono_left (nhdsWithin_le_nhds (s := Iio (1:ℝ)))
    simpa using this
  have hxm : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[>] (-1:ℝ)) (𝓝 (-1)) := by
    have := (continuous_ofReal.tendsto (-1:ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (-1:ℝ)))
    simpa using this
  have hl1 : m ≤ l+1 := by omega
  have p1 := legPI_tendsto_PQ_one (j := n+1) hm hl
  have p2 := legPI_tendsto_PQ_one (j := n) hm hl
  have p3 := legPI_tendsto_PQ_one (j := n) hm hl1
  have q1 := legPI_tendsto_PQ_neg_one (j := n+1) hm hl
  have q2 := legPI_tendsto_PQ_neg_one (j := n) hm hl
  have q3 := legPI_tendsto_PQ_neg_one (j := n) hm hl1
  have hp := ((((tendsto_const_nhds (x := (m-n-1:ℂ))).mul p1).add
    (((tendsto_const_nhds (x := (n+1:ℂ))).mul hx1).mul p2)).sub
    ((tendsto_const_nhds (x := (m-l-1:ℂ))).mul p3)).sub
    (((tendsto_const_nhds (x := (l+1:ℂ))).mul hx1).mul p2)
  have hq := ((((tendsto_const_nhds (x := (m-n-1:ℂ))).mul q1).add
    (((tendsto_const_nhds (x := (n+1:ℂ))).mul hxm).mul q2)).sub
    ((tendsto_const_nhds (x := (m-l-1:ℂ))).mul q3)).sub
    (((tendsto_const_nhds (x := (l+1:ℂ))).mul hxm).mul q2)
  have hcont : ContinuousOn (fun x => ferrersP l m x * ferrersQ n m x) (Ioo (-1) 1) :=
    (legPI_continuousOn_of_solution' (ferrersP_isFerrersSolution _ _)).mul
      (legPI_continuousOn_of_solution' (ferrersQ_isFerrersSolution _ _))
  have hint := legPI_intervalIntegrable_of_tendsto hcont q2 p2
  have hc : (l:ℂ)*(l+1) - n*(n+1) ≠ 0 := by
    rw [show (l:ℂ)*(l+1) - n*(n+1) = ((l:ℂ)-n)*(l+n+1) by ring]
    refine mul_ne_zero (sub_ne_zero.mpr (by exact_mod_cast h)) ?_
    exact_mod_cast (Nat.succ_ne_zero (l+n))
  rw [legPI_integral_green_B (ferrersP_isFerrersSolution _ _)
    (ferrersQ_isFerrersSolution _ _) hBeq hint hq hp hc]
  have e1 : ((-1:ℂ))^(l+(n+1)+1) = (-1)^(l+n) := by
    rw [show l+(n+1)+1 = (l+n)+2 by ring, pow_add]; norm_num
  have e2 : (-1:ℂ)^(l+n+1) = -(-1)^(l+n) := by rw [pow_succ]; ring
  have e3 : (-1:ℂ)^(l+1+n+1) = (-1)^(l+n) := by
    rw [show l+1+n+1 = (l+n)+2 by ring, pow_add]; norm_num
  have f1 : (l+1+m).factorial = (l+m+1) * (l+m).factorial := by
    rw [show l+1+m = (l+m)+1 by ring, Nat.factorial_succ]
  have f2 : (l+1-m).factorial = (l-m+1) * (l-m).factorial := by
    rw [show l+1-m = (l-m)+1 by omega, Nat.factorial_succ]
  have hlm : ((l-m:ℕ):ℂ) = (l:ℂ) - m := by push_cast [hl]; ring
  have hlm1 : ((l-m).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hm0 : (m:ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hd1 : ((l:ℂ) - m + 1) ≠ 0 := by
    rw [← hlm]; exact_mod_cast Nat.succ_ne_zero (l-m)
  have hd2 : (l:ℂ) - n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
  have hd3 : (l:ℂ) + n + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (l+n)
  rw [e1, e2, e3, f1, f2]
  push_cast
  rw [hlm]
  field_simp
  ring

/-- DLMF 14.17.16: for natural numbers `l ≠ n` and `m ≤ l`, `∫_{-1}^{1} 𝖯^m_l(x) 𝖰^m_n(x) dx = (1 -
(-1)^{l+n}) (l+m)!/((l-n)(l+n+1)(l-m)!)`. -/
@[dlmf 14.17.E16]
theorem ferrersPQ_nat_integral (l m n : ℕ) (h : l ≠ n) (hl : m ≤ l) :
    (∫ x : ℝ in -1..1, ferrersP l m x*ferrersQ n m x)=(1-(-1)^(l+n))*((l+m).factorial:ℂ)/(((l:ℂ)-n)*(l+n+1:ℂ)*(l-m).factorial) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hreg : LegendreQRegular (n:ℂ) 0 := fun j hj => by
      have := congrArg Complex.re hj; simp at this
      linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n), (Nat.cast_nonneg j : (0:ℝ) ≤ j)]
    have hd2 : (l:ℂ) - n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
    have hd3 : (l:ℂ) + n + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (l+n)
    have hc : (l:ℂ)*(l+1) - n*(n+1) ≠ 0 := by
      rw [show (l:ℂ)*(l+1) - n*(n+1) = (l-n)*(l+n+1) by ring]; exact mul_ne_zero hd2 hd3
    have hG : (Gamma (-(l:ℂ)))⁻¹ = 0 := by
      rw [inv_eq_zero]; exact Complex.Gamma_neg_nat_eq_zero l
    have hK : legPIK (l:ℂ) = 0 := by unfold legPIK legBdK; rw [hG, mul_zero]
    have hC : legPIC (l:ℂ) = (-1)^l := by
      unfold legPIC; rw [legPI_K'_eq_all, hG]; unfold legBdK; rw [hG]
      simp only [mul_zero, add_zero, sub_zero]
      rw [mul_comm, show ((l:ℂ)*π) = ((l*π : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos,
        Real.cos_nat_mul_pi]; push_cast; ring
    have hcos : cos ((n:ℂ)*π) = (-1)^n := by
      rw [show ((n:ℂ)*π) = ((n*π : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos,
        Real.cos_nat_mul_pi]; push_cast; ring
    have e := legPI_integral_PQ (ν := (l:ℂ)) hreg hc
    simp only [Nat.cast_zero] at e ⊢
    rw [e, hK, hC, hcos]
    simp only [add_zero, Nat.sub_zero]
    have hlf : ((l.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [pow_add]
    field_simp
    ring
  · exact legPI_PQ_nat_pos l m n hm h hl

/-- DLMF 14.17.17: for positive integers `l, m, n` such that either `|m-n| < l < m+n` or `l+m+n` is
even, `∫₀^π 𝖰_l(cos θ) 𝖯_m(cos θ) 𝖯_n(cos θ) sin θ dθ = 0`. -/
@[dlmf 14.17.E17]
theorem ferrers_triple_integral (l m n : ℕ) (hl : 0 < l) (hm : 0 < m) (hn : 0 < n) (htri : (|((m:ℤ)-n)| < l ∧ l < m+n) ∨ Even (l+m+n)) :
    (∫ θ : ℝ in 0..π, ferrersQ l 0 (Real.cos θ)*ferrersP m 0 (Real.cos θ)*ferrersP n 0 (Real.cos θ)*Real.sin θ)=0 := by
  sorry

end DLMF.Legendre
end
