/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.ArgumentContinuation
public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy

/-!
# Joint holomorphy of the Gauss function in its parameters (DLMF §15.2(ii))

DLMF §15.2(ii): `𝐅(a,b;c;z)` is an entire function of `a`, `b`, `c` for each fixed `z` in the
cut plane. This file proves the joint form, on the whole cut plane:

* `differentiable_regularizedGaussHGFun_of_differentiable`: on the unit disk, Mathlib's series
  `regularizedGaussHGFun` composed with holomorphic maps `A B C : E → ℂ` on any complex normed
  space is holomorphic. With projections this gives `entire_regularized_parameters`.
* `differentiableOn_regularizedGaussHG_joint`: `(a, b, c, z) ↦ regularizedGaussHG a b c z` is
  holomorphic on `ℂ³ × cutPlane`, with the corollaries `DifferentiableOn.regularizedGaussHG`,
  `differentiable_regularizedGaussHG_params`, `differentiable_regularizedGaussHG_comp` and
  `analyticOnNhd_regularizedGaussHG_comp`.

The definition `regularizedGaussHG` chooses its numbers of contiguous shifts from the parameters,
so its recursion is not locally uniform in them. Here the counts `p`, `q` are fixed instead
(`regularizedGaussHGShift`): on the open set `Re b + p > 0`, `Re (c - b) + q > p` the fixed-shift
recursion reaches Euler integrals only inside the Euler region, agrees with the series on the disk,
and is therefore the continuation. Euler's integral is jointly holomorphic in `(a, b, c, z)` by
`Complex.differentiableOn_intervalIntegral_of_locally_dominated`.
-/

@[expose] public section

open Complex Filter Set MeasureTheory intervalIntegral FormalMultilinearSeries
open scoped Topology Interval

noncomputable section

namespace DLMF.Hypergeometric

/-! ### The series on the unit disk -/

/-- On the unit disk, the regularized Gauss series composed with holomorphic parameter maps on a
complex normed space is holomorphic: the joint form of
`analyticOnNhd_regularizedGaussHGFun_comp`. -/
theorem differentiable_regularizedGaussHGFun_of_differentiable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {A B C : E → ℂ} (hA : Differentiable ℂ A)
    (hB : Differentiable ℂ B) (hC : Differentiable ℂ C) {z : ℂ} (hz : ‖z‖ < 1) :
    Differentiable ℂ (fun w => regularizedGaussHGFun (A w) (B w) (C w) z) := by
  simp_rw [regularizedGaussHGFun_eq_tsum]
  rw [← differentiableOn_univ]
  refine Complex.differentiableOn_tsum_of_eventually_dominated isOpen_univ ?_ ?_
  · intro n
    have h1 : Differentiable ℂ fun w => (ascPochhammer ℂ n).eval (A w) :=
      (Polynomial.differentiable (ascPochhammer ℂ n)).comp hA
    have h2 : Differentiable ℂ fun w => (ascPochhammer ℂ n).eval (B w) :=
      (Polynomial.differentiable (ascPochhammer ℂ n)).comp hB
    have h3 : Differentiable ℂ fun w => (ascPochhammer ℂ n).eval (A w) *
        (ascPochhammer ℂ n).eval (B w) * z ^ n / n.factorial := by
      fun_prop
    have h4 : Differentiable ℂ fun w => (Gamma (C w + n))⁻¹ := by
      simpa only [one_div, Function.comp_def] using
        differentiable_one_div_Gamma.comp (hC.add_const (n : ℂ))
    exact (h3.mul h4).differentiableOn
  · intro w₀ _
    obtain ⟨N, hN⟩ : ∃ N : ℕ, 3 - (C w₀).re ≤ N := exists_nat_ge _
    have hre0 : 2 ≤ (C w₀ + N).re := by
      simp only [Complex.add_re, Complex.natCast_re]
      linarith
    obtain ⟨V, hVopen, hc₀V, hV⟩ := exists_open_norm_Gamma_add_nat_gt hre0
    have hevA : ∀ᶠ w in 𝓝 w₀, ‖A w‖ < ‖A w₀‖ + 1 :=
      hA.continuous.continuousAt.norm.eventually (gt_mem_nhds (by linarith))
    have hevB : ∀ᶠ w in 𝓝 w₀, ‖B w‖ < ‖B w₀‖ + 1 :=
      hB.continuous.continuousAt.norm.eventually (gt_mem_nhds (by linarith))
    have hevC : ∀ᶠ w in 𝓝 w₀, (C w₀).re - 1 < (C w).re :=
      (Complex.continuous_re.comp hC.continuous).continuousAt.eventually
        (lt_mem_nhds (by show (C w₀).re - 1 < (C w₀).re; linarith))
    have hevV : ∀ᶠ w in 𝓝 w₀, C w ∈ V := hC.continuous.continuousAt (hVopen.mem_nhds hc₀V)
    refine ⟨_, hevA.and (hevB.and (hevC.and hevV)), N, ?_⟩
    set p := regularizedGaussHGFunSeries ((‖A w₀‖ + 1 : ℝ) : ℂ) ((‖B w₀‖ + 1 : ℝ) : ℂ) (1 - N)
      with hp
    have hz' : (‖z‖₊ : ENNReal) < p.radius := by
      refine lt_of_lt_of_le ?_ (radius_regularizedGaussHGFunSeries_ge_one _ _ _)
      rw [← ENNReal.coe_one, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]
      exact hz
    have hm : 0 < ‖Gamma (C w₀ + N)‖ / 2 := by
      have hpole : ∀ k : ℕ, C w₀ + N ≠ -k := fun k h => by
        have := congrArg Complex.re h
        simp only [Complex.neg_re, Complex.natCast_re] at this
        linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      have := norm_pos_iff.mpr (Gamma_ne_zero hpole)
      positivity
    refine ⟨fun n => (‖Gamma (C w₀ + N)‖ / 2)⁻¹ * (‖p n‖ * (‖z‖₊ : ℝ) ^ n),
      (p.summable_norm_mul_pow hz').mul_left _, ?_⟩
    intro n hn w hw
    obtain ⟨hAw, hBw, hCw, hVw⟩ := hw
    have hre : 1 ≤ (C w + N).re := by
      simp only [Complex.add_re, Complex.natCast_re] at hre0 ⊢
      linarith
    simpa only [coe_nnnorm] using
      norm_term_le_majorant hAw.le hBw.le hre hm (hV _ hVw).le hn

/-! ### Euler's integral and the fixed-shift recursion -/

/-- The Euler region in `(a, b, c, z)`. -/
def eulerRegion : Set (ℂ × ℂ × ℂ × ℂ) :=
  {q | 0 < q.2.1.re ∧ 0 < (q.2.2.1 - q.2.1).re ∧ q.2.2.2 ∈ cutPlane}

/-- The Euler region is open. -/
theorem isOpen_eulerRegion : IsOpen eulerRegion := by
  have h1 : Continuous fun q : ℂ × ℂ × ℂ × ℂ => q.2.1.re := by fun_prop
  have h2 : Continuous fun q : ℂ × ℂ × ℂ × ℂ => (q.2.2.1 - q.2.1).re := by fun_prop
  have h3 : Continuous fun q : ℂ × ℂ × ℂ × ℂ => q.2.2.2 := by fun_prop
  exact (isOpen_lt continuous_const h1).inter ((isOpen_lt continuous_const h2).inter
    (isOpen_cutPlane.preimage h3))

/-- Real powers bound complex powers of `t ∈ (0, 1)`. -/
theorem norm_ofReal_cpow_le {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) {w : ℂ} {β : ℝ} (hw : β ≤ w.re) :
    ‖(t : ℂ) ^ (w - 1)‖ ≤ ‖(t : ℂ) ^ ((β : ℂ) - 1)‖ := by
  rw [norm_cpow_eq_rpow_re_of_pos ht0, norm_cpow_eq_rpow_re_of_pos ht0]
  simp only [sub_re, ofReal_re, one_re]
  exact Real.rpow_le_rpow_of_exponent_ge ht0 ht1 (by linarith)

/-- Euler's integral `∫₀¹ t^(b-1) (1-t)^(c-b-1) (1-zt)^(-a) dt` is jointly holomorphic in
`(a, b, c, z)` on the Euler region. -/
theorem differentiableOn_regularizedGaussHGIntegral_joint :
    DifferentiableOn ℂ (fun q : ℂ × ℂ × ℂ × ℂ =>
      ∫ t : ℝ in (0 : ℝ)..1, eulerKernel q.1 q.2.1 q.2.2.1 q.2.2.2 t) eulerRegion := by
  have hI : Ι (0 : ℝ) 1 = Ioc 0 1 := uIoc_of_le zero_le_one
  refine Complex.differentiableOn_intervalIntegral_of_locally_dominated isOpen_eulerRegion 0 1
    ?_ ?_ ?_
  · intro q hq
    have := intervalIntegrable_eulerKernel (a := q.1) hq.1 hq.2.1 hq.2.2
    rw [hI]
    exact this.1.aestronglyMeasurable
  · rw [hI]
    have hne : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)), t ≠ 1 :=
      ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton (1 : ℝ)))
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hne] with t ht ht1 q hq
    have ht1' : t < 1 := lt_of_le_of_ne ht.2 ht1
    have h0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
    have h1 : (1 - (t : ℂ)) ≠ 0 := by
      rw [← ofReal_one, ← ofReal_sub, ofReal_ne_zero]; linarith
    have hslit := one_sub_mul_mem_slitPlane hq.2.2 ⟨ht.1.le, ht.2⟩
    refine DifferentiableAt.differentiableWithinAt ?_
    unfold eulerKernel
    refine ((DifferentiableAt.const_cpow (by fun_prop) (Or.inl h0)).mul
      (DifferentiableAt.const_cpow (by fun_prop) (Or.inl h1))).mul
      (DifferentiableAt.cpow (by fun_prop) (by fun_prop) hslit)
  · rintro ⟨a₀, b₀, c₀, z₀⟩ ⟨hb₀, hcb₀, hz₀⟩
    simp only at hb₀ hcb₀ hz₀
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_cutPlane z₀ hz₀
    have hclosed : Metric.closedBall z₀ (ε / 2) ⊆ cutPlane :=
      (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
    set K : Set (ℝ × ℂ × ℂ) := Icc (0 : ℝ) 1 ×ˢ Metric.closedBall a₀ 1 ×ˢ
      Metric.closedBall z₀ (ε / 2) with hK
    have hcont : ContinuousOn (fun p : ℝ × ℂ × ℂ => (1 - p.2.2 * p.1) ^ (-p.2.1)) K := by
      refine ContinuousOn.cpow (by fun_prop) (by fun_prop) ?_
      intro p hp
      exact one_sub_mul_mem_slitPlane (hclosed hp.2.2) hp.1
    obtain ⟨C, hC⟩ := (isCompact_Icc.prod ((isCompact_closedBall a₀ 1).prod
      (isCompact_closedBall z₀ (ε / 2)))).exists_bound_of_continuousOn hcont
    set β := b₀.re / 2 with hβ
    set γ := (c₀ - b₀).re / 2 with hγ
    have hβ0 : 0 < β := by rw [hβ]; linarith
    have hγ0 : 0 < γ := by rw [hγ]; linarith
    set V : Set (ℂ × ℂ × ℂ × ℂ) := {q | β < q.2.1.re ∧ γ < (q.2.2.1 - q.2.1).re ∧
      q.1 ∈ Metric.ball a₀ 1 ∧ q.2.2.2 ∈ Metric.ball z₀ (ε / 2)} with hV
    have hVo : IsOpen V := by
      have h1 : Continuous fun q : ℂ × ℂ × ℂ × ℂ => q.2.1.re := by fun_prop
      have h2 : Continuous fun q : ℂ × ℂ × ℂ × ℂ => (q.2.2.1 - q.2.1).re := by fun_prop
      have h3 : Continuous fun q : ℂ × ℂ × ℂ × ℂ => q.2.2.2 := by fun_prop
      have h4 : Continuous fun q : ℂ × ℂ × ℂ × ℂ => q.1 := by fun_prop
      exact (isOpen_lt continuous_const h1).inter ((isOpen_lt continuous_const h2).inter
        ((Metric.isOpen_ball.preimage h4).inter (Metric.isOpen_ball.preimage h3)))
    have hq₀V : ((a₀, b₀, c₀, z₀) : ℂ × ℂ × ℂ × ℂ) ∈ V :=
      ⟨by simp only; linarith, by simp only; linarith, Metric.mem_ball_self one_pos,
        Metric.mem_ball_self (half_pos hε)⟩
    have hbeta := betaIntegral_convergent (u := (β : ℂ)) (v := (γ : ℂ)) (by simpa using hβ0)
      (by simpa using hγ0)
    refine ⟨V, hVo.mem_nhds hq₀V, fun t => ‖(t : ℂ) ^ ((β : ℂ) - 1) *
      (1 - (t : ℂ)) ^ ((γ : ℂ) - 1)‖ * C, ?_, ?_⟩
    · have := (intervalIntegrable_iff.mp (hbeta.norm.mul_const C))
      exact this
    · rw [hI]
      have hne : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)), t ≠ 1 :=
        ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton (1 : ℝ)))
      filter_upwards [ae_restrict_mem measurableSet_Ioc, hne] with t ht ht1 q hq
      obtain ⟨hqb, hqc, hqa, hqz⟩ := hq
      have ht1' : t < 1 := lt_of_le_of_ne ht.2 ht1
      have hone : (1 - (t : ℂ)) = ((1 - t : ℝ) : ℂ) := by push_cast; ring
      unfold eulerKernel
      rw [norm_mul, norm_mul, norm_mul]
      have hA : ‖(t : ℂ) ^ (q.2.1 - 1)‖ ≤ ‖(t : ℂ) ^ ((β : ℂ) - 1)‖ :=
        norm_ofReal_cpow_le ht.1 ht.2 hqb.le
      have hB : ‖(1 - (t : ℂ)) ^ (q.2.2.1 - q.2.1 - 1)‖ ≤ ‖(1 - (t : ℂ)) ^ ((γ : ℂ) - 1)‖ := by
        rw [hone]
        exact norm_ofReal_cpow_le (by linarith) (by linarith [ht.1]) hqc.le
      have hCq : ‖(1 - q.2.2.2 * t) ^ (-q.1)‖ ≤ C :=
        hC (t, q.1, q.2.2.2) ⟨⟨ht.1.le, ht.2⟩, Metric.ball_subset_closedBall hqa,
          Metric.ball_subset_closedBall hqz⟩
      gcongr

/-- Euler's integral in the regularized normalization, `regularizedGaussHGIntegral`, is jointly
holomorphic in `(a, b, c, z)` on the Euler region. -/
theorem differentiableOn_regularizedGaussHGIntegral_eulerRegion :
    DifferentiableOn ℂ (fun q : ℂ × ℂ × ℂ × ℂ =>
      regularizedGaussHGIntegral q.1 q.2.1 q.2.2.1 q.2.2.2) eulerRegion := by
  unfold regularizedGaussHGIntegral
  refine DifferentiableOn.mul ?_ differentiableOn_regularizedGaussHGIntegral_joint
  have hG : Differentiable ℂ fun s : ℂ => (Gamma s)⁻¹ := by
    simpa only [one_div] using differentiable_one_div_Gamma
  have h1 : Differentiable ℂ fun q : ℂ × ℂ × ℂ × ℂ => (Gamma q.2.1)⁻¹ :=
    hG.comp (by fun_prop)
  have h2 : Differentiable ℂ fun q : ℂ × ℂ × ℂ × ℂ => (Gamma (q.2.2.1 - q.2.1))⁻¹ :=
    hG.comp (by fun_prop)
  simp only [mul_inv]
  exact fun q _ => ((h1 q).mul (h2 q)).differentiableWithinAt

/-- The continuation recursion with a fixed number `p` of `b`-shifts, ending in Euler's
integral. -/
def regularizedGaussHGShiftB : ℕ → ℂ → ℂ → ℂ → ℂ → ℂ
  | 0, a, b, c, z => regularizedGaussHGIntegral a b c z
  | p + 1, a, b, c, z => regularizedGaussHGShiftB p a (b + 1) c z -
      a * z * regularizedGaussHGShiftB p (a + 1) (b + 1) (c + 1) z

/-- The continuation recursion with a fixed number `q` of `c`-shifts followed by `p` `b`-shifts. -/
def regularizedGaussHGShift (p : ℕ) : ℕ → ℂ → ℂ → ℂ → ℂ → ℂ
  | 0, a, b, c, z => regularizedGaussHGShiftB p a b c z
  | q + 1, a, b, c, z => (c - a) * regularizedGaussHGShift p q a b (c + 1) z +
      a * regularizedGaussHGShift p q (a + 1) b (c + 1) z

/-- On the disk the `b`-shift recursion is the series, when its Euler integrals are convergent. -/
theorem regularizedGaussHGShiftB_eq (p : ℕ) {a b c z : ℂ} (hb : 0 < b.re + p)
    (hc : (p : ℝ) < (c - b).re) (hz : ‖z‖ < 1) :
    regularizedGaussHGShiftB p a b c z = regularizedGaussHGFun a b c z := by
  induction p generalizing a b c with
  | zero =>
    simp only [CharP.cast_eq_zero, add_zero] at hb hc
    exact regularizedGaussHGIntegral_eq_regularizedGaussHGFun hb hc hz
  | succ p ih =>
    simp only [Nat.cast_succ] at hb hc
    rw [regularizedGaussHGShiftB, ih (by simp only [add_re, one_re]; linarith)
        (by simp only [sub_re, add_re, one_re] at hc ⊢; linarith),
      ih (by simp only [add_re, one_re]; linarith)
        (by simp only [sub_re, add_re, one_re] at hc ⊢; linarith)]
    linear_combination (-1 : ℂ) * regularizedGaussHGFun_contiguous_shift_b a b c hz

/-- On the disk the fixed-shift recursion is the series, when its Euler integrals are
convergent. -/
theorem regularizedGaussHGShift_eq (p q : ℕ) {a b c z : ℂ} (hb : 0 < b.re + p)
    (hc : (p : ℝ) < (c - b).re + q) (hz : ‖z‖ < 1) :
    regularizedGaussHGShift p q a b c z = regularizedGaussHGFun a b c z := by
  induction q generalizing a b c with
  | zero =>
    simp only [CharP.cast_eq_zero, add_zero] at hc
    exact regularizedGaussHGShiftB_eq p hb hc hz
  | succ q ih =>
    simp only [Nat.cast_succ] at hc
    rw [regularizedGaussHGShift, ih hb (by simp only [sub_re, add_re, one_re] at hc ⊢; linarith),
      ih hb (by simp only [sub_re, add_re, one_re] at hc ⊢; linarith),
      regularizedGaussHGFun_contiguous_c a b c hz]

/-- The base case of the `b`-shift recursion. -/
theorem regularizedGaussHGShiftB_zero (a b c z : ℂ) :
    regularizedGaussHGShiftB 0 a b c z = regularizedGaussHGIntegral a b c z := rfl

/-- The step of the `b`-shift recursion. -/
theorem regularizedGaussHGShiftB_succ (p : ℕ) (a b c z : ℂ) :
    regularizedGaussHGShiftB (p + 1) a b c z = regularizedGaussHGShiftB p a (b + 1) c z -
      a * z * regularizedGaussHGShiftB p (a + 1) (b + 1) (c + 1) z := rfl

section Comp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The `b`-shift recursion along holomorphic maps is holomorphic where its Euler integrals
converge. -/
theorem differentiableOn_regularizedGaussHGShiftB (p : ℕ) {A B C Z : E → ℂ}
    (hA : Differentiable ℂ A) (hB : Differentiable ℂ B) (hC : Differentiable ℂ C)
    (hZ : Differentiable ℂ Z) {W : Set E}
    (hW : ∀ w ∈ W, 0 < (B w).re + p ∧ (p : ℝ) < (C w - B w).re ∧ Z w ∈ cutPlane) :
    DifferentiableOn ℂ (fun w => regularizedGaussHGShiftB p (A w) (B w) (C w) (Z w)) W := by
  induction p generalizing A B C with
  | zero =>
    have hmap : MapsTo (fun w => ((A w, B w, C w, Z w) : ℂ × ℂ × ℂ × ℂ)) W eulerRegion := by
      intro w hw
      obtain ⟨h1, h2, h3⟩ := hW w hw
      simp only [CharP.cast_eq_zero, add_zero] at h1 h2
      exact ⟨h1, h2, h3⟩
    have hg : DifferentiableOn ℂ (fun w => ((A w, B w, C w, Z w) : ℂ × ℂ × ℂ × ℂ)) W :=
      (hA.prodMk (hB.prodMk (hC.prodMk hZ))).differentiableOn
    have hc := differentiableOn_regularizedGaussHGIntegral_eulerRegion.comp hg hmap
    simp only [regularizedGaussHGShiftB_zero]
    exact hc
  | succ p ih =>
    have h1 := ih hA (hB.add_const 1) hC (fun w hw => by
      obtain ⟨h1, h2, h3⟩ := hW w hw
      simp only [Nat.cast_succ, sub_re, add_re, one_re] at h1 h2 ⊢
      exact ⟨by linarith, by linarith, h3⟩)
    have h2 := ih (hA.add_const 1) (hB.add_const 1) (hC.add_const 1) (fun w hw => by
      obtain ⟨h1, h2, h3⟩ := hW w hw
      simp only [Nat.cast_succ, sub_re, add_re, one_re] at h1 h2 ⊢
      exact ⟨by linarith, by linarith, h3⟩)
    simp only [regularizedGaussHGShiftB_succ]
    exact h1.sub ((hA.differentiableOn.mul hZ.differentiableOn).mul h2)

/-- The fixed-shift recursion along holomorphic maps is holomorphic where its Euler integrals
converge. -/
theorem differentiableOn_regularizedGaussHGShift (p q : ℕ) {A B C Z : E → ℂ}
    (hA : Differentiable ℂ A) (hB : Differentiable ℂ B) (hC : Differentiable ℂ C)
    (hZ : Differentiable ℂ Z) {W : Set E}
    (hW : ∀ w ∈ W, 0 < (B w).re + p ∧ (p : ℝ) < (C w - B w).re + q ∧ Z w ∈ cutPlane) :
    DifferentiableOn ℂ (fun w => regularizedGaussHGShift p q (A w) (B w) (C w) (Z w)) W := by
  induction q generalizing A B C with
  | zero =>
    refine differentiableOn_regularizedGaussHGShiftB p hA hB hC hZ fun w hw => ?_
    obtain ⟨h1, h2, h3⟩ := hW w hw
    simp only [CharP.cast_eq_zero, add_zero] at h2
    exact ⟨h1, h2, h3⟩
  | succ q ih =>
    have hW' : ∀ w ∈ W, 0 < (B w).re + p ∧ (p : ℝ) < (C w + 1 - B w).re + q ∧ Z w ∈ cutPlane :=
      fun w hw => by
        obtain ⟨h1, h2, h3⟩ := hW w hw
        simp only [Nat.cast_succ, sub_re, add_re, one_re] at h2 ⊢
        exact ⟨h1, by linarith, h3⟩
    have h1 := ih hA hB (hC.add_const 1) hW'
    have h2 := ih (hA.add_const 1) hB (hC.add_const 1) hW'
    simp only [regularizedGaussHGShift]
    exact ((hC.differentiableOn.sub hA.differentiableOn).mul h1).add
      (hA.differentiableOn.mul h2)

end Comp

/-- In the region where the fixed shift counts suffice, the fixed-shift recursion is the
continuation. -/
theorem regularizedGaussHG_eq_regularizedGaussHGShift (p q : ℕ) {a b c z : ℂ}
    (hb : 0 < b.re + p) (hc : (p : ℝ) < (c - b).re + q) (hz : z ∈ cutPlane) :
    regularizedGaussHG a b c z = regularizedGaussHGShift p q a b c z := by
  have han : AnalyticOnNhd ℂ (fun z => regularizedGaussHGShift p q a b c z) cutPlane := by
    refine DifferentiableOn.analyticOnNhd ?_ isOpen_cutPlane
    exact differentiableOn_regularizedGaussHGShift p q (differentiable_const a)
      (differentiable_const b) (differentiable_const c) differentiable_id
      fun w hw => ⟨hb, hc, hw⟩
  exact (regularizedGaussHG_unique han
    (fun w hw => regularizedGaussHGShift_eq p q hb hc hw) hz).symm

/-- **Joint holomorphy of the continued Gauss function.** `(a, b, c, z) ↦ 𝐅(a, b; c; z)` is
holomorphic on `ℂ³ × cutPlane`, for all parameters. -/
theorem differentiableOn_regularizedGaussHG_joint :
    DifferentiableOn ℂ (fun q : ℂ × ℂ × ℂ × ℂ => regularizedGaussHG q.1 q.2.1 q.2.2.1 q.2.2.2)
      {q | q.2.2.2 ∈ cutPlane} := by
  rintro ⟨a₀, b₀, c₀, z₀⟩ hz₀
  obtain ⟨P, hP⟩ : ∃ P : ℕ, 1 - b₀.re ≤ P := exists_nat_ge _
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, P + 1 - (c₀ - b₀).re ≤ Q := exists_nat_ge _
  set W : Set (ℂ × ℂ × ℂ × ℂ) := {q | 0 < q.2.1.re + P ∧ (P : ℝ) < (q.2.2.1 - q.2.1).re + Q ∧
    q.2.2.2 ∈ cutPlane} with hWdef
  have hWo : IsOpen W := by
    have h1 : Continuous fun q : ℂ × ℂ × ℂ × ℂ => q.2.1.re + P := by fun_prop
    have h2 : Continuous fun q : ℂ × ℂ × ℂ × ℂ => (q.2.2.1 - q.2.1).re + Q := by fun_prop
    have h3 : Continuous fun q : ℂ × ℂ × ℂ × ℂ => q.2.2.2 := by fun_prop
    exact (isOpen_lt continuous_const h1).inter ((isOpen_lt continuous_const h2).inter
      (isOpen_cutPlane.preimage h3))
  have hq₀ : ((a₀, b₀, c₀, z₀) : ℂ × ℂ × ℂ × ℂ) ∈ W :=
    ⟨by simp only; linarith, by simp only; linarith, hz₀⟩
  have hd := differentiableOn_regularizedGaussHGShift P Q (E := ℂ × ℂ × ℂ × ℂ)
    (A := fun q => q.1) (B := fun q => q.2.1) (C := fun q => q.2.2.1) (Z := fun q => q.2.2.2)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (W := W) fun w hw => hw
  refine (hd.differentiableAt (hWo.mem_nhds hq₀)).congr_of_eventuallyEq ?_
    |>.differentiableWithinAt
  filter_upwards [hWo.mem_nhds hq₀] with q hq
  exact regularizedGaussHG_eq_regularizedGaussHGShift P Q hq.1 hq.2.1 hq.2.2

/-- The continued Gauss function composed with holomorphic parameter and argument maps is
holomorphic wherever the argument stays in the cut plane. -/
theorem _root_.DifferentiableOn.regularizedGaussHG {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {A B C Z : E → ℂ} {s : Set E} (hA : DifferentiableOn ℂ A s)
    (hB : DifferentiableOn ℂ B s) (hC : DifferentiableOn ℂ C s) (hZ : DifferentiableOn ℂ Z s)
    (hs : ∀ w ∈ s, Z w ∈ cutPlane) :
    DifferentiableOn ℂ (fun w => regularizedGaussHG (A w) (B w) (C w) (Z w)) s :=
  differentiableOn_regularizedGaussHG_joint.comp (hA.prodMk (hB.prodMk (hC.prodMk hZ)))
    fun w hw => hs w hw

/-- For `z` in the cut plane, `(a, b, c) ↦ 𝐅(a, b; c; z)` is entire (DLMF §15.2(ii), on the
whole cut plane). -/
theorem differentiable_regularizedGaussHG_params {z : ℂ} (hz : z ∈ cutPlane) :
    Differentiable ℂ (fun p : ℂ × ℂ × ℂ => regularizedGaussHG p.1 p.2.1 p.2.2 z) := by
  rw [← differentiableOn_univ]
  exact DifferentiableOn.regularizedGaussHG (by fun_prop) (by fun_prop) (by fun_prop)
    (differentiableOn_const z) fun _ _ => hz

/-- Along holomorphic parameter maps, the continued Gauss function is holomorphic for every `z`
in the cut plane. -/
theorem differentiable_regularizedGaussHG_comp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {A B C : E → ℂ} (hA : Differentiable ℂ A) (hB : Differentiable ℂ B)
    (hC : Differentiable ℂ C) {z : ℂ} (hz : z ∈ cutPlane) :
    Differentiable ℂ (fun w => regularizedGaussHG (A w) (B w) (C w) z) := by
  rw [← differentiableOn_univ]
  exact DifferentiableOn.regularizedGaussHG hA.differentiableOn hB.differentiableOn
    hC.differentiableOn (differentiableOn_const z) fun _ _ => hz

/-- Along entire parameter curves, the continued Gauss function is entire for every `z` in the
cut plane; the cut-plane form of `analyticOnNhd_regularizedGaussHGFun_comp`. -/
theorem analyticOnNhd_regularizedGaussHG_comp {A B C : ℂ → ℂ} (hA : Differentiable ℂ A)
    (hB : Differentiable ℂ B) (hC : Differentiable ℂ C) {z : ℂ} (hz : z ∈ cutPlane) :
    AnalyticOnNhd ℂ (fun w => regularizedGaussHG (A w) (B w) (C w) z) univ := by
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_univ
  exact (differentiable_regularizedGaussHG_comp hA hB hC hz).differentiableOn

end DLMF.Hypergeometric
