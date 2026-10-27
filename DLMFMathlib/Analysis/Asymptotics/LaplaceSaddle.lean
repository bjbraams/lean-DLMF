/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.Watson

/-!
# All-order Laplace expansions at a quadratic endpoint

Watson's lemma (`hasAsymptoticExpansion_integral_exp_smul`) treats Laplace transforms
`∫₀^∞ e^{-zt} F(t) dt`. After the saddle substitution `φ(u) = v²/2`, a Laplace integral with a
quadratic minimum of the phase becomes a Gaussian integral `∫₀^{v₀} e^{-z v²/2} G(v) dv`. This
file proves the all-order expansion of such Gaussian integrals and collects the tools used to
produce the substitution.

## Main results

* `Asymptotics.lapSad_hasAsymptoticExpansion_gauss_odd`: if `G(v) ~ ∑ bⱼ v^{2j+1}` as `v → 0⁺`,
  then `∫₀^{v₀} e^{-z v²/2} G(v) dv ~ ∑ j! 2ʲ bⱼ z^{-(j+1)}` as `z → +∞`.
* `Asymptotics.lapSad_hasAsymptoticExpansion_gauss_analytic`: the same for the odd amplitude
  `v (-U(-v) - U(v))` built from an analytic substitution `U`, with coefficients read off from
  the power series of `U` (`Asymptotics.lapSad_isBigO_odd_part`).
* `Asymptotics.lapSad_coeff_eq_zero_of_isBigO`: uniqueness of truncated power expansions, used
  to identify Taylor coefficients of implicitly defined substitutions.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Asymptotics
open scoped Topology

namespace Asymptotics

/-- The map `v ↦ v²/2` sends `(0, v₀]` onto `(0, v₀²/2]`. -/
theorem lapSad_image_half_sq {v₀ : ℝ} (hv₀ : 0 < v₀) :
    (fun v : ℝ => v^2/2) '' Ioc 0 v₀ = Ioc 0 (v₀^2/2) := by
  ext τ
  constructor
  · rintro ⟨v, ⟨hv0, hv1⟩, rfl⟩
    exact ⟨by positivity, show v^2/2 ≤ v₀^2/2 by gcongr⟩
  · rintro ⟨h0, h1⟩
    refine ⟨Real.sqrt (2*τ), ⟨by positivity, ?_⟩, ?_⟩
    · rw [Real.sqrt_le_left hv₀.le]; linarith
    · show Real.sqrt (2*τ)^2/2 = τ
      rw [Real.sq_sqrt (by linarith)]; ring

/-- Change of variables `τ = v²/2` on `(0, v₀]`. -/
theorem lapSad_integral_half_sq {v₀ : ℝ} (hv₀ : 0 < v₀) (g : ℝ → ℝ) :
    ∫ τ in Ioc 0 (v₀^2/2), g τ = ∫ v in Ioc 0 v₀, v * g (v^2/2) := by
  rw [← lapSad_image_half_sq hv₀, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc
    (f' := fun v => v)]
  · refine setIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
    simp [abs_of_pos hv.1]
  · intro v _
    have := ((hasDerivAt_pow 2 v).div_const 2).hasDerivWithinAt (s := Ioc 0 v₀)
    convert this using 1; push_cast; ring
  · intro x hx y hy hxy
    have := hx.1; have := hy.1
    have h2 : x^2 = y^2 := by simpa using hxy
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]

/-- **Watson's lemma in Gaussian form, odd amplitude.** If `G` is continuous on `[0, v₀]` and
`G(v) - ∑_{j<N} bⱼ v^{2j+1} = O(v^{2N+1})` as `v → 0⁺` for every `N`, then
`∫₀^{v₀} e^{-z v²/2} G(v) dv ~ ∑ Γ(j+1) 2ʲ bⱼ z^{-(j+1)}` as `z → +∞`. -/
theorem lapSad_hasAsymptoticExpansion_gauss_odd {G : ℝ → ℝ} {v₀ : ℝ} (hv₀ : 0 < v₀)
    (hG : ContinuousOn G (Icc 0 v₀)) {b : ℕ → ℝ}
    (hexp : ∀ N : ℕ, (fun v => G v - ∑ j ∈ Finset.range N, b j * v^(2*j+1)) =O[𝓝[>] 0]
      fun v => v^(2*N+1)) :
    HasAsymptoticExpansion atTop (fun (j : ℕ) (z : ℝ) => z ^ (-((j : ℝ) + 1)))
      (fun j => Real.Gamma ((j : ℝ) + 1) * (2^j * b j))
      (fun z => ∫ v in (0:ℝ)..v₀, Real.exp (-z * v^2/2) * G v) := by
  set T := v₀^2/2 with hT
  have hT0 : 0 < T := by positivity
  set F : ℝ → ℝ := indicator (Ioc 0 T) fun τ => G (Real.sqrt (2*τ)) / Real.sqrt (2*τ) with hF
  have hsq : ∀ v : ℝ, 0 < v → Real.sqrt (2*(v^2/2)) = v := fun v hv => by
    rw [show 2*(v^2/2) = v^2 by ring, Real.sqrt_sq hv.le]
  -- the integrals agree
  have hEq : ∀ z : ℝ, ∫ v in (0:ℝ)..v₀, Real.exp (-z * v^2/2) * G v =
      ∫ τ in Ioi (0:ℝ), Real.exp (-z * τ) • F τ := by
    intro z
    have h1 : ∫ τ in Ioi (0:ℝ), Real.exp (-z * τ) • F τ =
        ∫ τ in Ioc 0 T, Real.exp (-z * τ) * (G (Real.sqrt (2*τ)) / Real.sqrt (2*τ)) := by
      simp only [hF, smul_eq_mul]
      rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioc]
      congr 1; funext τ
      by_cases h : τ ∈ Ioc 0 T
      · simp [indicator_of_mem h, indicator_of_mem (show τ ∈ Ioi (0:ℝ) from h.1)]
      · simp only [indicator_of_notMem h]
        by_cases h' : τ ∈ Ioi (0:ℝ)
        · simp [indicator_of_mem h', indicator_of_notMem h]
        · simp [indicator_of_notMem h']
    rw [h1, lapSad_integral_half_sq hv₀, intervalIntegral.integral_of_le hv₀.le]
    refine setIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
    rw [hsq v hv.1]
    field_simp [hv.1.ne']
  -- integrability
  have hint : IntegrableOn (fun τ => Real.exp (-0 * τ) • F τ) (Ioi 0) := by
    have hGi : IntegrableOn G (Ioc 0 v₀) :=
      (hG.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
    have hI : IntegrableOn (fun τ => G (Real.sqrt (2*τ)) / Real.sqrt (2*τ)) (Ioc 0 T) := by
      rw [← lapSad_image_half_sq hv₀, integrableOn_image_iff_integrableOn_abs_deriv_smul
        measurableSet_Ioc (f' := fun v => v)]
      · refine hGi.congr_fun (fun v hv => ?_) measurableSet_Ioc
        simp only [smul_eq_mul]
        rw [hsq v hv.1, abs_of_pos hv.1]
        field_simp [hv.1.ne']
      · intro v _
        have := ((hasDerivAt_pow 2 v).div_const 2).hasDerivWithinAt (s := Ioc 0 v₀)
        convert this using 1; push_cast; ring
      · intro x hx y hy hxy
        have := hx.1; have := hy.1
        have h2 : x^2 = y^2 := by simpa using hxy
        nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]
    simp only [neg_zero, zero_mul, Real.exp_zero, one_smul]
    exact ((integrable_indicator_iff measurableSet_Ioc).mpr hI).integrableOn
  -- the expansion of `F` at `0⁺`
  have hFexp : ∀ N : ℕ, (fun τ => F τ - ∑ n ∈ Finset.range N, τ ^ ((n : ℝ) + 1 - 1) • (2^n * b n))
      =O[𝓝[>] 0] fun τ => τ ^ ((N : ℝ) + 1 - 1) := by
    intro N
    have hs : Tendsto (fun τ : ℝ => Real.sqrt (2*τ)) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun τ : ℝ => Real.sqrt (2*τ)) (𝓝 0) (𝓝 (Real.sqrt (2*0))) :=
          ((continuous_const.mul continuous_id).sqrt).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with τ hτ
        exact Real.sqrt_pos.mpr (by simpa using hτ)
    have h1 := ((hexp N).comp_tendsto hs).mul
      (isBigO_refl (fun τ : ℝ => (Real.sqrt (2*τ))⁻¹) (𝓝[>] 0))
    have h2 : (fun τ => F τ - ∑ n ∈ Finset.range N, τ ^ ((n : ℝ) + 1 - 1) • (2^n * b n))
        =O[𝓝[>] 0] fun x => ((fun v : ℝ => v^(2*N+1)) ∘ fun τ => Real.sqrt (2*τ)) x *
          (Real.sqrt (2*x))⁻¹ := by
      refine h1.congr' ?_ EventuallyEq.rfl
      filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hT0] with τ hτ hτT
      have hτ0 : (0:ℝ) < τ := hτ
      have hsp : 0 < Real.sqrt (2*τ) := Real.sqrt_pos.mpr (by linarith)
      have hss : Real.sqrt (2*τ)^2 = 2*τ := Real.sq_sqrt (by linarith)
      simp only [Function.comp_apply, hF, indicator_of_mem (show τ ∈ Ioc 0 T from
        ⟨hτ0, hτT.2.le⟩), smul_eq_mul]
      rw [sub_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [show (n:ℝ) + 1 - 1 = n by ring, Real.rpow_natCast, pow_succ, pow_mul, hss]
      field_simp
      ring
    refine h2.trans ?_
    · refine IsBigO.of_bound (2^N) ?_
      filter_upwards [self_mem_nhdsWithin] with τ hτ
      have hτ0 : (0:ℝ) < τ := hτ
      have hsp : 0 < Real.sqrt (2*τ) := Real.sqrt_pos.mpr (by linarith)
      have hss : Real.sqrt (2*τ)^2 = 2*τ := Real.sq_sqrt (by linarith)
      simp only [Function.comp_apply]
      rw [show (N:ℝ) + 1 - 1 = N by ring, Real.rpow_natCast, pow_succ, pow_mul, hss]
      rw [mul_assoc, mul_inv_cancel₀ hsp.ne', mul_one, mul_pow, norm_mul, norm_pow,
        Real.norm_two]
  have H := hasAsymptoticExpansion_integral_exp_smul (E := ℝ) (μ := 1) (c := 0) one_pos hint hFexp
  refine (H.congr' (Eventually.of_forall fun z => (hEq z).symm)).congr_coeff ?_
  funext j
  rw [smul_eq_mul]

/-- Uniqueness of truncated expansions: if `∑_{k<M} eₖ vᵏ = O(v^M)` as `v → 0`, `v ≠ 0`,
then `eₖ = 0` for every `k < M`. -/
theorem lapSad_coeff_eq_zero_of_isBigO : ∀ (M : ℕ) {e : ℕ → ℝ},
    (fun v : ℝ => ∑ k ∈ Finset.range M, e k * v^k) =O[𝓝[≠] 0] (fun v => v^M) →
    ∀ k < M, e k = 0
  | 0, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | M+1, e, h, k, hk => by
    have h1 : (fun v : ℝ => v^(M+1)) =O[𝓝[≠] 0] (fun v => v^M) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0:ℝ) one_pos)] with v hv
      have hv1 : |v| ≤ 1 := by simpa [Real.dist_eq] using (Metric.mem_ball.1 hv).le
      rw [norm_pow, norm_pow, Real.norm_eq_abs, pow_succ, one_mul]
      exact mul_le_of_le_one_right (by positivity) hv1
    have hM : (fun v : ℝ => ∑ k ∈ Finset.range M, e k * v^k) =O[𝓝[≠] 0] (fun v => v^M) := by
      have := (h.trans h1).sub ((isBigO_refl (fun v : ℝ => v^M) (𝓝[≠] 0)).const_mul_left (e M))
      exact this.congr' (Eventually.of_forall fun v => by simp [Finset.sum_range_succ])
        EventuallyEq.rfl
    have hlow := lapSad_coeff_eq_zero_of_isBigO M hM
    have hEM : e M = 0 := by
      have h3 : (fun v : ℝ => e M * v^M) =O[𝓝[≠] 0] (fun v => v^(M+1)) := by
        refine h.congr' (Eventually.of_forall fun v => ?_) EventuallyEq.rfl
        dsimp only
        rw [Finset.sum_range_succ, Finset.sum_eq_zero fun k hk => by
          rw [hlow k (Finset.mem_range.1 hk), zero_mul], zero_add]
      have h4 : (fun _ : ℝ => e M) =O[𝓝[≠] 0] (fun v => v) := by
        refine (h3.mul (isBigO_refl (fun v : ℝ => (v^M)⁻¹) _)).congr' ?_ ?_
        · filter_upwards [self_mem_nhdsWithin] with v hv
          have hv : v ≠ 0 := hv
          field_simp
        · filter_upwards [self_mem_nhdsWithin] with v hv
          have hv : v ≠ 0 := hv
          field_simp
          ring
      have h5 : Tendsto (fun _ : ℝ => e M) (𝓝[≠] 0) (𝓝 0) :=
        h4.trans_tendsto (tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto' 0 0 rfl))
      exact tendsto_nhds_unique tendsto_const_nhds h5
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact hlow k hk
    · exact hEM

/-- Pairing the terms of degree `2j` and `2j+1`: `-T(-v) - T(v) = ∑_{j<N} -2 c_{2j} v^{2j}` for
the polynomial `T(v) = ∑_{k<2N} c_k vᵏ`. -/
theorem lapSad_sum_even_part (c : ℕ → ℝ) (v : ℝ) (N : ℕ) :
    -(∑ k ∈ Finset.range (2*N), c k * (-v)^k) - ∑ k ∈ Finset.range (2*N), c k * v^k =
      ∑ j ∈ Finset.range N, (-2 * c (2*j)) * v^(2*j) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2*(N+1) = 2*N+1+1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ (fun k => c k * v^k), Finset.sum_range_succ,
      ← ih]
    have e1 : (-v)^(2*N) = v^(2*N) := by rw [pow_mul, neg_sq, ← pow_mul]
    have e2 : (-v)^(2*N+1) = -v^(2*N+1) := by rw [pow_succ, e1, pow_succ]; ring
    rw [e1, e2]
    ring

/-- Odd part of an analytic function: if `U` has the power series `p` at `0`, then
`v (-U(-v) - U(v)) = ∑_{j<N} (-2 p_{2j}) v^{2j+1} + O(v^{2N+1})` as `v → 0`. -/
theorem lapSad_isBigO_odd_part {U : ℝ → ℝ} {p : FormalMultilinearSeries ℝ ℝ ℝ}
    (hU : HasFPowerSeriesAt U p 0) (N : ℕ) :
    (fun v => v * (-U (-v) - U v) - ∑ j ∈ Finset.range N, (-2 * p.coeff (2*j)) * v^(2*j+1))
      =O[𝓝 0] fun v => v^(2*N+1) := by
  have h := hU.isBigO_sub_partialSum_pow (2*N)
  simp only [zero_add, FormalMultilinearSeries.partialSum,
    FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul] at h
  have hneg : Tendsto (fun v : ℝ => -v) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg (G := ℝ)).tendsto (0:ℝ)
  have h' : (fun v : ℝ => U (-v) - ∑ k ∈ Finset.range (2*N), (-v)^k * p.coeff k)
      =O[𝓝 0] fun v => ‖v‖^(2*N) :=
    (h.comp_tendsto hneg).congr' EventuallyEq.rfl (Eventually.of_forall fun v => by simp)
  have hW : (fun v : ℝ => (-U (-v) - U v) - ∑ j ∈ Finset.range N, (-2 * p.coeff (2*j)) * v^(2*j))
      =O[𝓝 0] fun v => ‖v‖^(2*N) := by
    refine (h'.neg_left.sub h).congr' (Eventually.of_forall fun v => ?_) EventuallyEq.rfl
    dsimp only
    rw [← lapSad_sum_even_part]
    simp only [mul_comm (p.coeff _)]
    ring
  refine ((isBigO_refl (fun v : ℝ => v) (𝓝 0)).mul hW).congr' (Eventually.of_forall fun v => ?_)
    EventuallyEq.rfl |>.trans ?_
  · simp only [mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  · refine IsBigO.of_bound 1 (Eventually.of_forall fun v => ?_)
    rw [one_mul, norm_mul, norm_pow, norm_norm, norm_pow, pow_succ, mul_comm]

/-- **Gaussian Laplace integrals with an analytic substitution.** If `U` has the power series
`p` at `0` and is continuous on `[-v₀, v₀]`, then
`∫₀^{v₀} e^{-z v²/2} v (-U(-v) - U(v)) dv ~ ∑ Γ(j+1) 2ʲ (-2 p_{2j}) z^{-(j+1)}` as `z → +∞`.
This is the form taken by `∫ e^{-z ψ}` across a quadratic minimum of `ψ` after the substitution
`ψ = v²/2` and an integration by parts. -/
theorem lapSad_hasAsymptoticExpansion_gauss_analytic {U : ℝ → ℝ}
    {p : FormalMultilinearSeries ℝ ℝ ℝ} (hU : HasFPowerSeriesAt U p 0) {v₀ : ℝ} (hv₀ : 0 < v₀)
    (hc : ContinuousOn U (Icc (-v₀) v₀)) :
    HasAsymptoticExpansion atTop (fun (j : ℕ) (z : ℝ) => z ^ (-((j : ℝ) + 1)))
      (fun j => Real.Gamma ((j : ℝ) + 1) * (2^j * (-2 * p.coeff (2*j))))
      (fun z => ∫ v in (0:ℝ)..v₀, Real.exp (-z * v^2/2) * (v * (-U (-v) - U v))) := by
  refine lapSad_hasAsymptoticExpansion_gauss_odd hv₀ ?_ fun N =>
    (lapSad_isBigO_odd_part hU N).mono nhdsWithin_le_nhds
  have h1 : ContinuousOn U (Icc 0 v₀) := hc.mono (Icc_subset_Icc (by linarith) le_rfl)
  have h2 : ContinuousOn (fun v => U (-v)) (Icc 0 v₀) :=
    hc.comp continuousOn_neg fun v hv => ⟨by linarith [hv.2], by linarith [hv.1]⟩
  exact continuousOn_id.mul (h2.neg.sub h1)

end Asymptotics
