/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.AlgebraicAnalytic.Complex.Functions

/-!
# Infinite products, partial fractions and generating functions (DLMF §1.10(ix)–(xi))

## Main results

* `prodConvergesDLMF_iff_log`, `prodConvergesDLMF_norm_iff`, `prod_mtest_log`, `prod_mtest`,
  `differentiableOn_of_tendstoUniformlyOn_prod`, `tendsto_logDeriv_prod`: infinite products
  (§1.10(ix), 1.10.20–1.10.24).
* `weierstrass_product`, `mittag_leffler`: DLMF 1.10.22, 1.10.25.
* `coeff_eq_circleIntegral`: DLMF 1.10.26–1.10.27.

## Implementation notes

* Products indexed by `n ≥ 1` in DLMF are indexed by `ℕ` here where the index is a dummy
  (Weierstrass products, Mittag-Leffler series); DLMF's convergence of infinite products is
  `ProdConvergesDLMF` of `DLMF.AlgebraicAnalytic.Complex.Basic`.
-/

@[expose] public noncomputable section

open Complex Filter Set Metric MeasureTheory
open scoped Topology

namespace DLMF.AlgebraicAnalytic

/-! ## §1.10(ix) Infinite products -/

/-- DLMF §1.10(ix): the product `∏_{n ≥ 1} (1 + aₙ)` with `aₙ ≠ -1` for all `n` converges iff
`∑_{n ≥ 1} ln(1 + aₙ)` converges (principal logarithms, partial sums). -/
@[dlmf 1.10.ix]
theorem prodConvergesDLMF_iff_log {a : ℕ → ℂ} (ha : ∀ n ≥ 1, a n ≠ -1) :
    ProdConvergesDLMF a ↔
      ∃ s, Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, log (1 + a n)) atTop (𝓝 s) := by
  have hne : ∀ n ≥ 1, 1 + a n ≠ 0 := fun n hn h => ha n hn (by linear_combination h)
  set S : ℕ → ℂ := fun N => ∑ n ∈ Finset.Icc 1 N, log (1 + a n)
  set P : ℕ → ℂ := fun N => ∏ n ∈ Finset.Icc 1 N, (1 + a n)
  have hSP : ∀ N, exp (S N) = P N := fun N => by
    simp only [S, P, Complex.exp_sum]
    refine Finset.prod_congr rfl fun n hn => exp_log (hne n (Finset.mem_Icc.mp hn).1)
  have hP0 : ∀ N, P N ≠ 0 := fun N => by rw [← hSP]; exact exp_ne_zero _
  constructor
  · rintro ⟨k, hk, p, hp, hlim⟩
    -- the full partial products converge to a nonzero limit
    set C := ∏ n ∈ Finset.Ico 1 k, (1 + a n)
    have hC : C ≠ 0 := Finset.prod_ne_zero_iff.mpr fun n hn =>
      hne n (Finset.mem_Ico.mp hn).1
    have hPl : Tendsto P atTop (𝓝 (C * p)) := by
      refine (hlim.const_mul C).congr' ?_
      filter_upwards [eventually_ge_atTop k] with m hm
      simp only [P, C]
      rw [← Finset.Ico_add_one_right_eq_Icc, ← Finset.Ico_add_one_right_eq_Icc,
        Finset.prod_Ico_consecutive _ hk (by omega)]
    set L := C * p
    have hL : L ≠ 0 := mul_ne_zero hC hp
    have hint : ∀ N, ∃ k : ℤ, S N - log (P N / L) - log L = k * (2 * Real.pi * I) := by
      intro N
      rw [← Complex.exp_eq_one_iff, exp_sub, exp_sub, hSP, exp_log (div_ne_zero (hP0 N) hL),
        exp_log hL]
      field_simp [hP0 N]
    choose kk hkk using hint
    have hlog : Tendsto (fun N => log (P N / L)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun N => P N / L) atTop (𝓝 1) := by
        simpa [div_self hL] using hPl.div_const L
      have h2 := (continuousAt_clog (by simp : (1 : ℂ) ∈ slitPlane)).tendsto.comp h1
      rw [log_one] at h2
      exact h2
    have hstep : Tendsto (fun N => S (N + 1) - S N) atTop (𝓝 0) := by
      have h1 : Tendsto (fun N => P (N + 1) / P N) atTop (𝓝 1) := by
        have := ((tendsto_add_atTop_iff_nat 1).mpr hPl).div hPl hL
        rw [div_self hL] at this
        exact this
      have h2 := (continuousAt_clog (by simp : (1 : ℂ) ∈ slitPlane)).tendsto.comp h1
      rw [log_one] at h2
      refine h2.congr fun N => ?_
      simp only [Function.comp_apply, S, P]
      rw [Finset.sum_Icc_succ_top (by omega), Finset.prod_Icc_succ_top (by omega),
        mul_div_cancel_left₀ _ (hP0 N)]
      ring
    have hd : Tendsto (fun N => (((kk (N + 1) - kk N : ℤ) : ℂ))) atTop (𝓝 0) := by
      have h := (hstep.sub (((tendsto_add_atTop_iff_nat 1).mpr hlog).sub hlog)).div_const
        (2 * Real.pi * I)
      simp only [sub_zero, zero_div] at h
      refine h.congr fun N => ?_
      have e1 := hkk (N + 1)
      have e2 := hkk N
      have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
      rw [div_eq_iff hpi]
      push_cast
      linear_combination e1 - e2
    have hev : ∀ᶠ N in atTop, kk (N + 1) = kk N := by
      have hd' := hd.norm
      rw [norm_zero] at hd'
      filter_upwards [hd'.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with N hN
      rw [Complex.norm_intCast] at hN
      have : kk (N + 1) - kk N = 0 := by
        have h' : |((kk (N + 1) - kk N : ℤ) : ℝ)| < 1 := by exact_mod_cast hN
        exact_mod_cast Int.abs_lt_one_iff.mp (by exact_mod_cast h')
      omega
    obtain ⟨M, hM⟩ := eventually_atTop.mp hev
    have hconst : ∀ N ≥ M, kk N = kk M := by
      intro N hN
      induction N, hN using Nat.le_induction with
      | base => rfl
      | succ N hN ih => rw [hM N hN, ih]
    refine ⟨kk M * (2 * Real.pi * I) + log L, ?_⟩
    have h := (hlog.const_add (kk M * (2 * Real.pi * I) + log L))
    rw [add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop M] with N hN
    have := hkk N
    rw [hconst N hN] at this
    linear_combination -this
  · rintro ⟨s, hs⟩
    refine ⟨1, le_rfl, exp s, exp_ne_zero s, ?_⟩
    exact ((continuous_exp.tendsto s).comp hs).congr fun N => hSP N

/-- DLMF §1.10(ix): the product `∏_{n ≥ 1} (1 + aₙ)` converges absolutely (that is,
`∏ (1 + |aₙ|)` converges) iff `∑_{n ≥ 1} |aₙ|` converges. -/
@[dlmf 1.10.ix]
theorem prodConvergesDLMF_norm_iff {a : ℕ → ℂ} :
    ProdConvergesDLMF (fun n => (‖a n‖ : ℂ)) ↔ Summable (fun n => ‖a (n + 1)‖) := by
  have hnorm (n : ℕ) : ‖1 + (‖a n‖ : ℂ)‖ = 1 + ‖a n‖ := by
    rw [← ofReal_one, ← ofReal_add, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  have hshift (k n : ℕ) :
      (∏ i ∈ Finset.range (n + 1), (1 + (‖a (i + k)‖ : ℂ))) =
        ∏ i ∈ Finset.Icc k (n + k), (1 + (‖a i‖ : ℂ)) := by
    rw [← Nat.Ico_zero_eq_range,
      Finset.prod_Ico_add' (fun i => (1 + (‖a i‖ : ℂ))) 0 (n + 1) k, zero_add,
      show n + 1 + k = (n + k) + 1 by omega, Finset.Ico_add_one_right_eq_Icc]
  constructor
  · rintro ⟨k, hk, p, hp, hconv⟩
    obtain ⟨B, hB⟩ := hconv.norm.bddAbove_range
    have hsum : Summable (fun n : ℕ => ‖a (n + k)‖) := by
      refine summable_of_sum_range_le (fun n => norm_nonneg _) (c := B) fun n => ?_
      have hprod (m : ℕ) :
          (∑ i ∈ Finset.range m, ‖a (i + k)‖) ≤
            ∏ i ∈ Finset.range m, (1 + ‖a (i + k)‖) := by
        have hstrong (m : ℕ) :
            1 + (∑ i ∈ Finset.range m, ‖a (i + k)‖) ≤
              ∏ i ∈ Finset.range m, (1 + ‖a (i + k)‖) := by
          induction m with
          | zero => simp
          | succ m ih =>
            rw [Finset.sum_range_succ, Finset.prod_range_succ]
            have hs0 : 0 ≤ ∑ i ∈ Finset.range m, ‖a (i + k)‖ :=
              Finset.sum_nonneg fun i _ => norm_nonneg _
            nlinarith [norm_nonneg (a (m + k))]
        linarith [hstrong m]
      have hbound := hB ⟨n + k, rfl⟩
      change ‖∏ i ∈ Finset.Icc k (n + k), (1 + (‖a i‖ : ℂ))‖ ≤ B at hbound
      rw [← hshift k n, norm_prod] at hbound
      simp_rw [hnorm] at hbound
      refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun i _ _ => norm_nonneg (a (i + k)))).trans ((hprod (n + 1)).trans hbound)
    exact (summable_nat_add_iff (f := fun n => ‖a n‖) 1).mpr
      ((summable_nat_add_iff (f := fun n => ‖a n‖) k).mp hsum)
  · intro hs
    have hsc : Summable (fun n : ℕ => ‖(‖a (n + 1)‖ : ℂ)‖) := by simpa using hs
    have hprod := multipliable_one_add_of_summable hsc
    refine ⟨1, le_rfl, ∏' n : ℕ, (1 + (‖a (n + 1)‖ : ℂ)),
      tprod_one_add_ne_zero_of_summable (fun n => ?_) hsc, ?_⟩
    · intro hn
      have hn0 := hnorm (n + 1)
      rw [hn, norm_zero] at hn0
      have : 0 ≤ ‖a (n + 1)‖ := norm_nonneg _
      linarith
    · have hlim := hprod.hasProd.tendsto_prod_nat
      refine hlim.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
      simpa only [add_comm 1 m] using hshift 1 m

/-- DLMF §1.10(ix) (`M`-test for products, second form): the conclusion of 1.10.20–1.10.21 holds
if instead `|aₙ(z)| ≤ Mₙ` for all `n` and `z ∈ D`, with `∑ Mₙ < ∞`. -/
@[dlmf 1.10.E21]
theorem prod_mtest {a : ℕ → ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (ha : ∀ n, DifferentiableOn ℂ (a n) D) {M : ℕ → ℝ}
    (hM : ∀ n, ∀ z ∈ D, ‖a n z‖ ≤ M n) (hs : Summable M) :
    ∃ p : ℂ → ℂ, DifferentiableOn ℂ p D ∧
      TendstoUniformlyOn (fun m z => ∏ n ∈ Finset.Icc 1 m, (1 + a n z)) p atTop D ∧
      ∀ z ∈ D, p z = 0 → ∃ n ≥ 1, 1 + a n z = 0 := by
  classical
  let p : ℂ → ℂ := fun z => ∏' n : ℕ, (1 + a (n + 1) z)
  by_cases hne : D.Nonempty
  · letI : Nonempty D := hne.to_subtype
    have hM0 (n : ℕ) : 0 ≤ M n := by
      obtain ⟨z, hz⟩ := hne
      exact (norm_nonneg (a n z)).trans (hM n z hz)
    let A (n : ℕ) : BoundedContinuousFunction D ℂ :=
      BoundedContinuousFunction.ofNormedAddCommGroup (fun z => a (n + 1) z)
        (continuousOn_iff_continuous_domRestrict.mp (ha (n + 1)).continuousOn)
        (M (n + 1)) (fun z => hM (n + 1) z z.2)
    have hAapply (n : ℕ) (z : D) : A n z = a (n + 1) z := rfl
    have hAnorm : Summable (fun n => ‖A n‖) := by
      apply ((summable_nat_add_iff 1).mpr hs).of_nonneg_of_le (fun n => norm_nonneg _)
      intro n
      exact (BoundedContinuousFunction.norm_le (hM0 (n + 1))).mpr
        (fun z => hM (n + 1) z z.2)
    have hAP := multipliable_one_add_of_summable hAnorm
    have hAu := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
      hAP.hasProd.tendsto_prod_nat
    have hprod (n : ℕ) (z : ℂ) :
        (∏ i ∈ Finset.range n, (1 + a (i + 1) z)) =
          ∏ i ∈ Finset.Icc 1 n, (1 + a i z) := by
      rw [← Nat.Ico_zero_eq_range,
        Finset.prod_Ico_add' (fun i => (1 + a i z)) 0 n 1, zero_add,
        Finset.Ico_add_one_right_eq_Icc]
    have hpoint (z : ℂ) (hz : z ∈ D) :
        Tendsto (fun n => ∏ i ∈ Finset.range n, (1 + a (i + 1) z)) atTop (𝓝 (p z)) := by
      apply (multipliable_one_add_of_summable ?_).hasProd.tendsto_prod_nat
      exact ((summable_nat_add_iff 1).mpr hs).of_nonneg_of_le (fun n => norm_nonneg _)
        (fun n => hM (n + 1) z hz)
    have hPeq (z : D) : (∏' n : ℕ, (1 + A n)) z = p z := by
      apply tendsto_nhds_unique (hAu.tendsto_at z)
      simpa only [BoundedContinuousFunction.prod_apply, BoundedContinuousFunction.add_apply,
        BoundedContinuousFunction.coe_one, Pi.one_apply, hAapply] using hpoint z z.2
    have hu : TendstoUniformlyOn (fun n z => ∏ i ∈ Finset.Icc 1 n, (1 + a i z)) p atTop D := by
      rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
      convert hAu using 1
      · ext n z
        simp only [BoundedContinuousFunction.prod_apply, BoundedContinuousFunction.add_apply,
          BoundedContinuousFunction.coe_one, Pi.one_apply, hAapply]
        exact (hprod n z).symm
      · ext z
        exact (hPeq z).symm
    refine ⟨p, ?_, hu, ?_⟩
    · refine hu.tendstoLocallyUniformlyOn.differentiableOn
        (Eventually.of_forall fun n => ?_) hD
      exact DifferentiableOn.fun_finsetProd fun i _ => (ha i).const_add 1
    · intro z hz hp
      by_contra! hnone
      have hnonzero := tprod_one_add_ne_zero_of_summable
        (fun n => hnone (n + 1) (by omega))
        (((summable_nat_add_iff 1).mpr hs).of_nonneg_of_le (fun n => norm_nonneg _)
          (fun n => hM (n + 1) z hz))
      exact hnonzero hp
  · have hD0 : D = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst D
    exact ⟨p, differentiableOn_empty, tendstoUniformlyOn_empty, by simp⟩

/-- DLMF 1.10.20–1.10.21 (`M`-test for products): let `aₙ` be analytic in the domain `D`; if
`|ln(1 + aₙ(z))| ≤ Mₙ` for `n ≥ N` and `z ∈ D` and `∑ Mₙ < ∞`, then `∏_{n ≥ 1} (1 + aₙ(z))`
converges locally uniformly to a function `p` analytic in `D`, and `p(z) = 0` only where some factor
`1 + aₙ(z)` vanishes. Bounds on the tail give local uniform convergence; global uniform
convergence would additionally need control of the finite prefix. -/
@[dlmf 1.10.E20]
theorem prod_mtest_log {a : ℕ → ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (ha : ∀ n, DifferentiableOn ℂ (a n) D) {M : ℕ → ℝ} {N : ℕ}
    (hM : ∀ n ≥ N, ∀ z ∈ D, ‖log (1 + a n z)‖ ≤ M n) (hs : Summable M) :
    ∃ p : ℂ → ℂ, DifferentiableOn ℂ p D ∧
      TendstoLocallyUniformlyOn (fun m z => ∏ n ∈ Finset.Icc 1 m, (1 + a n z)) p atTop D ∧
      ∀ z ∈ D, p z = 0 → ∃ n ≥ 1, 1 + a n z = 0 := by
  classical
  set F : ℕ → ℂ → ℂ := fun m z => ∏ n ∈ Finset.Icc 1 m, (1 + a n z) with hFdef
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (hs.tendsto_atTop_zero.eventually (eventually_le_nhds one_pos))
  set N' := max (max N 1) N₀ with hN'
  have hN'N : N ≤ N' := le_trans (le_max_left _ _) (le_max_left _ _)
  have hN'1 : 1 ≤ N' := le_trans (le_max_right _ _) (le_max_left _ _)
  have hN'0 : N₀ ≤ N' := le_max_right _ _
  -- a nonvanishing tail factor is close to `1` and bounded away from `0`
  have hfac : ∀ n ≥ N', ∀ z ∈ D, 1 + a n z ≠ 0 →
      Real.exp (-1) ≤ ‖1 + a n z‖ ∧ ‖a n z‖ ≤ 2 * M n := by
    intro n hn z hz hne
    have hL := hM n (hN'N.trans hn) z hz
    have hM1 : M n ≤ 1 := hN₀ n (hN'0.trans hn)
    have hexp := Complex.exp_log hne
    refine ⟨?_, ?_⟩
    · rw [← hexp, Complex.norm_exp]
      refine Real.exp_le_exp.mpr ?_
      have := Complex.abs_re_le_norm (log (1 + a n z))
      have := neg_abs_le (log (1 + a n z)).re
      linarith
    · have h1 := Complex.norm_exp_sub_one_le (hL.trans hM1)
      rw [hexp, add_sub_cancel_left] at h1
      linarith
  -- the prefix product
  set P : ℂ → ℂ := fun z => ∏ n ∈ Finset.Ico 1 N', (1 + a n z) with hPdef
  have hPc : ContinuousOn P D :=
    (DifferentiableOn.fun_finsetProd fun i _ => (ha i).const_add 1).continuousOn
  have hloc : ∀ z₀ ∈ D, ∃ B ∈ 𝓝 z₀, ∃ q : ℂ → ℂ, TendstoUniformlyOn F q atTop B ∧
      ((∀ n ≥ 1, 1 + a n z₀ ≠ 0) → q z₀ ≠ 0) := by
    intro z₀ hz₀
    obtain ⟨r₁, hr₁, hr₁D⟩ := Metric.isOpen_iff.mp hD z₀ hz₀
    obtain ⟨r₂, hr₂, hr₂P⟩ := Metric.continuousOn_iff.mp hPc z₀ hz₀ 1 one_pos
    set r := min r₁ r₂
    have hr : 0 < r := lt_min hr₁ hr₂
    have hBD : ball z₀ r ⊆ D := (ball_subset_ball (min_le_left _ _)).trans hr₁D
    have hPb : ∀ z ∈ ball z₀ r, ‖P z‖ ≤ ‖P z₀‖ + 1 := by
      intro z hz
      have := hr₂P z (hBD hz) (lt_of_lt_of_le (mem_ball.mp hz) (min_le_right _ _))
      rw [dist_eq_norm] at this
      have := norm_le_norm_add_norm_sub' (P z) (P z₀)
      linarith
    -- each tail factor vanishes identically or nowhere on the ball
    have hdich : ∀ n ≥ N', (∀ z ∈ ball z₀ r, 1 + a n z = 0) ∨
        ∀ z ∈ ball z₀ r, 1 + a n z ≠ 0 := by
      intro n hn
      by_contra! h
      obtain ⟨⟨z₁, hz₁, h₁⟩, ⟨z₂, hz₂, h₂⟩⟩ := h
      have hc : ContinuousOn (fun z => ‖1 + a n z‖) (ball z₀ r) :=
        (((ha n).const_add 1).continuousOn.mono hBD).norm
      have hiv := (convex_ball z₀ r).isPreconnected.intermediate_value hz₂ hz₁ hc
      have hlow := (hfac n hn z₁ (hBD hz₁) h₁).1
      obtain ⟨w, hw, hw'⟩ := (hiv (show Real.exp (-1) / 2 ∈ Icc ‖1 + a n z₂‖ ‖1 + a n z₁‖ from
        ⟨by simp only [h₂, norm_zero]; positivity, by linarith [Real.exp_pos (-1)]⟩))
      have hwne : 1 + a n w ≠ 0 := by
        intro h0
        simp only [h0, norm_zero] at hw'
        linarith [Real.exp_pos (-1)]
      have := (hfac n hn w (hBD hw) hwne).1
      linarith [Real.exp_pos (-1)]
    by_cases hA : ∃ n ≥ N', ∀ z ∈ ball z₀ r, 1 + a n z = 0
    · obtain ⟨n₀, hn₀, hz⟩ := hA
      refine ⟨ball z₀ r, ball_mem_nhds z₀ hr, 0, ?_, fun h => absurd (hz z₀ (mem_ball_self hr))
        (h n₀ (hN'1.trans hn₀))⟩
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [eventually_ge_atTop n₀] with m hm z hzB
      simp only [hFdef, Pi.zero_apply]
      rw [Finset.prod_eq_zero (i := n₀) (Finset.mem_Icc.mpr ⟨hN'1.trans hn₀, hm⟩) (hz z hzB)]
      simpa using hε
    · push Not at hA
      have hB : ∀ n ≥ N', ∀ z ∈ ball z₀ r, 1 + a n z ≠ 0 := by
        intro n hn
        rcases hdich n hn with h | h
        · obtain ⟨z, hz, hne⟩ := hA n hn
          exact absurd (h z hz) hne
        · exact h
      set b : ℕ → ℂ → ℂ := fun n z => if N' ≤ n then a n z else 0 with hbdef
      have hbd : ∀ n, DifferentiableOn ℂ (b n) (ball z₀ r) := by
        intro n
        by_cases hn : N' ≤ n
        · simpa only [hbdef, hn, ite_true] using (ha n).mono hBD
        · simp only [hbdef, hn, ite_false]
          exact differentiableOn_const 0
      have hbM : ∀ n, ∀ z ∈ ball z₀ r, ‖b n z‖ ≤ 2 * |M n| := by
        intro n z hz
        by_cases hn : N' ≤ n
        · simp only [hbdef, hn, ite_true]
          exact (hfac n hn z (hBD hz) (hB n hn z hz)).2.trans (by
            have := le_abs_self (M n); linarith)
        · simp only [hbdef, hn, ite_false, norm_zero]
          positivity
      obtain ⟨pB, -, hpBu, hpB0⟩ := prod_mtest isOpen_ball hbd hbM (hs.abs.mul_left 2)
      have hsplit : ∀ m ≥ N', ∀ z, F m z = P z * ∏ n ∈ Finset.Icc 1 m, (1 + b n z) := by
        intro m hm z
        have hfac' : ∀ n, 1 + a n z = (if N' ≤ n then 1 else 1 + a n z) * (1 + b n z) := by
          intro n
          by_cases hn : N' ≤ n <;> simp [hbdef, hn]
        simp only [hFdef]
        rw [Finset.prod_congr rfl fun n _ => hfac' n, Finset.prod_mul_distrib]
        congr 1
        have h1 : ∏ n ∈ Finset.Ico 1 N', (if N' ≤ n then (1 : ℂ) else 1 + a n z) = P z :=
          Finset.prod_congr rfl fun n hn => by simp [not_le.mpr (Finset.mem_Ico.mp hn).2]
        rw [← h1]
        refine (Finset.prod_subset (fun n hn => ?_) (fun n hn hn' => ?_)).symm
        · exact (Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hn).1,
            ((Finset.mem_Ico.mp hn).2.le.trans hm)⟩)
        · have : N' ≤ n := by
            by_contra h
            exact hn' (Finset.mem_Ico.mpr ⟨(Finset.mem_Icc.mp hn).1, not_le.mp h⟩)
          simp [this]
      refine ⟨ball z₀ r, ball_mem_nhds z₀ hr, fun z => P z * pB z, ?_, ?_⟩
      · rw [Metric.tendstoUniformlyOn_iff] at hpBu ⊢
        intro ε hε
        have hK : 0 < ‖P z₀‖ + 1 := by positivity
        filter_upwards [hpBu (ε / (‖P z₀‖ + 1)) (div_pos hε hK), eventually_ge_atTop N']
          with m hm hmN z hz
        rw [hsplit m hmN z, dist_eq_norm, ← mul_sub, norm_mul]
        have h1 := hm z hz
        rw [dist_eq_norm] at h1
        calc ‖P z‖ * ‖pB z - ∏ n ∈ Finset.Icc 1 m, (1 + b n z)‖
            ≤ (‖P z₀‖ + 1) * ‖pB z - ∏ n ∈ Finset.Icc 1 m, (1 + b n z)‖ :=
              mul_le_mul_of_nonneg_right (hPb z hz) (norm_nonneg _)
          _ < (‖P z₀‖ + 1) * (ε / (‖P z₀‖ + 1)) := mul_lt_mul_of_pos_left h1 hK
          _ = ε := by field_simp
      · intro hne
        refine mul_ne_zero ?_ ?_
        · exact Finset.prod_ne_zero_iff.mpr fun n hn => hne n (Finset.mem_Ico.mp hn).1
        · intro h0
          obtain ⟨n, hn1, hn⟩ := hpB0 z₀ (mem_ball_self hr) h0
          by_cases hnN : N' ≤ n
          · simp only [hbdef, hnN, ite_true] at hn
            exact hne n hn1 hn
          · simp [hbdef, hnN] at hn
  set p : ℂ → ℂ := fun z => limUnder atTop fun m => F m z with hpdef
  have hpq : ∀ B q, TendstoUniformlyOn F q atTop B → EqOn q p B := fun B q h z hz =>
    ((h.tendsto_at hz).limUnder_eq).symm
  have hU : TendstoLocallyUniformlyOn F p atTop D := by
    refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun x hx => ?_
    obtain ⟨B, hB, q, hq, -⟩ := hloc x hx
    exact ⟨B, mem_nhdsWithin_of_mem_nhds hB, hq.congr_right (hpq B q hq)⟩
  refine ⟨p, hU.differentiableOn (Eventually.of_forall fun m =>
    DifferentiableOn.fun_finsetProd fun i _ => (ha i).const_add 1) hD, hU, ?_⟩
  intro z hz hp
  by_contra! hnone
  obtain ⟨B, hB, q, hq, hq0⟩ := hloc z hz
  exact hq0 hnone ((hpq B q hq (mem_of_mem_nhds hB)).trans hp)

/-- The Weierstrass elementary factor: `|(1 - u) eᵘ - 1| ≤ 3 |u|²` for `|u| ≤ 1`. -/
private theorem norm_one_sub_mul_exp_sub_one_le {u : ℂ} (hu : ‖u‖ ≤ 1) :
    ‖(1 - u) * exp u - 1‖ ≤ 3 * ‖u‖ ^ 2 := by
  have hR := norm_exp_sub_one_sub_id_le hu
  have heq : (1 - u) * exp u - 1 = -u ^ 2 + (1 - u) * (exp u - 1 - u) := by ring
  rw [heq]
  calc ‖-u ^ 2 + (1 - u) * (exp u - 1 - u)‖ ≤ ‖u‖ ^ 2 + 2 * ‖u‖ ^ 2 := by
        refine (norm_add_le _ _).trans (add_le_add (by simp) ?_)
        rw [norm_mul]
        have h1 : ‖1 - u‖ ≤ 2 := (norm_sub_le _ _).trans (by simp; linarith)
        exact mul_le_mul h1 hR (norm_nonneg _) (by norm_num)
    _ = 3 * ‖u‖ ^ 2 := by ring

/-- DLMF 1.10.22 (Weierstrass product): if `zₙ ≠ 0` and `∑ |zₙ|⁻²` converges, then
`P(z) = ∏ (1 - z/zₙ) e^{z/zₙ}` (an absolutely convergent product) is an entire function whose
zeros are exactly the points `zₙ`. -/
@[dlmf 1.10.E22]
theorem weierstrass_product {zs : ℕ → ℂ} (hz : ∀ n, zs n ≠ 0)
    (hs : Summable (fun n => ‖zs n‖⁻¹ ^ 2)) :
    (∀ z, Multipliable (fun n => (1 - z / zs n) * exp (z / zs n))) ∧
      Differentiable ℂ (fun z => ∏' n, (1 - z / zs n) * exp (z / zs n)) ∧
      ∀ z, (∏' n, (1 - z / zs n) * exp (z / zs n)) = 0 ↔ ∃ n, z = zs n := by
  set f : ℕ → ℂ → ℂ := fun n z => (1 - z / zs n) * exp (z / zs n) - 1 with hfdef
  have hf1 : ∀ n z, 1 + f n z = (1 - z / zs n) * exp (z / zs n) := fun n z => by
    simp only [hfdef]; ring
  have hinv : Tendsto (fun n => ‖zs n‖⁻¹) atTop (𝓝 0) := by
    have h2 := hs.tendsto_atTop_zero
    have h3 := h2.sqrt
    simp only [Real.sqrt_zero] at h3
    refine h3.congr fun n => ?_
    rw [Real.sqrt_sq (inv_nonneg.2 (norm_nonneg _))]
  have hbound : ∀ R : ℝ, 0 < R → ∀ᶠ n in atTop, ∀ z ∈ ball (0 : ℂ) R,
      ‖f n z‖ ≤ 3 * R ^ 2 * ‖zs n‖⁻¹ ^ 2 := by
    intro R hR
    filter_upwards [hinv.eventually (gt_mem_nhds (inv_pos.2 hR))] with n hn z hzR
    have hzR' : ‖z‖ < R := by simpa using hzR
    have hu : ‖z / zs n‖ ≤ R * ‖zs n‖⁻¹ := by
      rw [norm_div, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hzR'.le (inv_nonneg.2 (norm_nonneg _))
    have hu1 : ‖z / zs n‖ ≤ 1 := hu.trans (by
      have := mul_lt_mul_of_pos_left hn hR
      rw [mul_inv_cancel₀ hR.ne'] at this
      exact this.le)
    calc ‖f n z‖ ≤ 3 * ‖z / zs n‖ ^ 2 := norm_one_sub_mul_exp_sub_one_le hu1
      _ ≤ 3 * (R * ‖zs n‖⁻¹) ^ 2 := by gcongr
      _ = 3 * R ^ 2 * ‖zs n‖⁻¹ ^ 2 := by ring
  have hsumm : ∀ z, Summable fun n => ‖f n z‖ := by
    intro z
    have hR : (0 : ℝ) < ‖z‖ + 1 := by positivity
    refine (hs.mul_left (3 * (‖z‖ + 1) ^ 2)).of_norm_bounded_eventually_nat ?_
    filter_upwards [hbound _ hR] with n hn
    rw [norm_norm]
    exact hn z (by simp)
  have hcont : ∀ n, Continuous (f n) := fun n => by simp only [hfdef]; fun_prop
  have hloc : ∀ R : ℝ, 0 < R → HasProdLocallyUniformlyOn (fun n z => 1 + f n z)
      (fun z => ∏' n, (1 + f n z)) (ball (0 : ℂ) R) := fun R hR =>
    (hs.mul_left (3 * R ^ 2)).hasProdLocallyUniformlyOn_nat_one_add isOpen_ball (hbound R hR)
      fun n => (hcont n).continuousOn
  refine ⟨fun z => ?_, fun z => ?_, fun z => ⟨fun h0 => ?_, ?_⟩⟩
  · simpa only [hf1] using multipliable_one_add_of_summable (hsumm z)
  · have hR : (0 : ℝ) < ‖z‖ + 1 := by positivity
    have hd := (hloc _ hR).differentiableOn (.of_forall fun s => by
      simpa [Finset.prod_fn] using DifferentiableOn.finsetProd (fun i _ =>
        ((differentiable_const _).add (by simp only [hfdef]; fun_prop)).differentiableOn))
      isOpen_ball
    have := hd.differentiableAt (isOpen_ball.mem_nhds (by simp : z ∈ ball (0 : ℂ) (‖z‖ + 1)))
    simpa only [hf1] using this
  · by_contra hne
    push Not at hne
    have hne' : ∀ n, 1 + f n z ≠ 0 := by
      intro n
      rw [hf1]
      refine mul_ne_zero ?_ (exp_ne_zero _)
      rw [sub_ne_zero, ne_comm, Ne, div_eq_one_iff_eq (hz n)]
      exact hne n
    exact tprod_one_add_ne_zero_of_summable hne' (hsumm z) (by simpa only [hf1] using h0)
  · rintro ⟨n, rfl⟩
    exact tprod_of_exists_eq_zero ⟨n, by simp [hz n]⟩

/-! ## §1.10(x) Infinite partial fractions -/

/-- DLMF 1.10.23: if the `aₙ` are analytic in the domain `D` and the partial products of
`F(z) = ∏ aₙ(z)` converge uniformly on compact subsets of `D`, then `F` is analytic in `D`. From
Mathlib's `TendstoLocallyUniformlyOn.differentiableOn`. -/
@[dlmf 1.10.E23]
theorem differentiableOn_of_tendstoUniformlyOn_prod {a : ℕ → ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (ha : ∀ n, DifferentiableOn ℂ (a n) D) {F : ℂ → ℂ}
    (hu : ∀ K ⊆ D, IsCompact K →
      TendstoUniformlyOn (fun m z => ∏ n ∈ Finset.range m, a n z) F atTop K) :
    DifferentiableOn ℂ F D := by
  have hl : TendstoLocallyUniformlyOn (fun m z => ∏ n ∈ Finset.range m, a n z) F atTop D :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hD).mpr hu
  refine hl.differentiableOn (Eventually.of_forall fun m => ?_) hD
  exact DifferentiableOn.fun_finsetProd fun n _ => ha n

/-- DLMF 1.10.24: if, in addition to the hypotheses of 1.10.23, `aₙ(z) ≠ 0` on `D` and the
product converges in the sense of DLMF (nonzero limit, `F(z) ≠ 0` on `D`; this hypothesis is
part of DLMF's notion of convergence and cannot be dropped: `aₙ = ½` gives the uniform limit
`0`), then `F'/F = ∑ aₙ'/aₙ` on `D`, the series converging as partial sums. -/
@[dlmf 1.10.E24]
theorem tendsto_logDeriv_prod {a : ℕ → ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (ha : ∀ n, DifferentiableOn ℂ (a n) D) (ha0 : ∀ n, ∀ z ∈ D, a n z ≠ 0) {F : ℂ → ℂ}
    (hu : ∀ K ⊆ D, IsCompact K →
      TendstoUniformlyOn (fun m z => ∏ n ∈ Finset.range m, a n z) F atTop K)
    (hF : ∀ z ∈ D, F z ≠ 0) {z : ℂ} (hz : z ∈ D) :
    Tendsto (fun m => ∑ n ∈ Finset.range m, logDeriv (a n) z) atTop (𝓝 (logDeriv F z)) := by
  let P : ℕ → ℂ → ℂ := fun m z => ∏ n ∈ Finset.range m, a n z
  have hP : ∀ m, DifferentiableOn ℂ (P m) D :=
    fun _ => DifferentiableOn.fun_finsetProd fun n _ => ha n
  have hl : TendstoLocallyUniformlyOn P F atTop D :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hD).mpr hu
  have hd := (hl.deriv (Eventually.of_forall hP) hD).tendsto_at hz
  have hv := hl.tendsto_at hz
  have hlim := hd.div hv (hF z hz)
  change Tendsto (fun m => deriv (P m) z / P m z) atTop (𝓝 (logDeriv F z)) at hlim
  refine hlim.congr' (Eventually.of_forall fun m => ?_)
  change logDeriv (fun w => ∏ n ∈ Finset.range m, a n w) z = _
  exact (logDeriv_fun_prod (fun n _ => ha0 n z hz)
    (fun n _ => (ha n).differentiableAt (hD.mem_nhds hz)))

/-- DLMF 1.10.25 (Mittag-Leffler expansion): if the `zₙ` are distinct and nonzero, `|zₙ| → ∞`,
and `∑ |aₙ zₙ⁻²|` converges, then `f(z) = ∑ aₙ (1/(z - zₙ) + 1/zₙ)` is analytic in `ℂ` except
for simple poles at the `zₙ` of residue `aₙ` (removable when `aₙ = 0`). The hypotheses
`zₙ ≠ 0` and `|zₙ| → ∞` are implicit in DLMF: without the latter the `zₙ` may accumulate at a
finite point, which is then a non-isolated singularity. -/
@[dlmf 1.10.E25]
theorem mittag_leffler {a zs : ℕ → ℂ} (hinj : Function.Injective zs) (hz : ∀ n, zs n ≠ 0)
    (hlim : Tendsto (fun n => ‖zs n‖) atTop atTop) (hs : Summable (fun n => ‖a n / zs n ^ 2‖)) :
    DifferentiableOn ℂ (fun z => ∑' n, a n * (1 / (z - zs n) + 1 / zs n)) (range zs)ᶜ ∧
      ∀ n, residueAt (fun z => ∑' k, a k * (1 / (z - zs k) + 1 / zs k)) (zs n) = a n ∧
        ∃ g : ℂ → ℂ, AnalyticAt ℂ g (zs n) ∧
          ∀ᶠ z in 𝓝[≠] (zs n),
            ∑' k, a k * (1 / (z - zs k) + 1 / zs k) = a n / (z - zs n) + g z := by
  refine ⟨Complex.differentiableOn_tsum_mittagLeffler hz hlim hs, fun n => ?_⟩
  obtain ⟨g, hg, hev⟩ := Complex.exists_analyticAt_tsum_mittagLeffler_eq hinj hz hlim hs n
  refine ⟨?_, g, hg, hev⟩
  have hH : AnalyticAt ℂ (fun z => a n + (z - zs n) * g z) (zs n) :=
    analyticAt_const.add ((analyticAt_id.sub analyticAt_const).mul hg)
  rw [residueAt_div_sub_pow (n := 0) hH (by
    filter_upwards [hev, self_mem_nhdsWithin] with z hz hne
    have hne' : z - zs n ≠ 0 := sub_ne_zero.2 hne
    rw [hz, zero_add, pow_one]
    field_simp)]
  simp

/-! ## §1.10(xi) Generating functions -/

/-- DLMF 1.10.26–1.10.27: if `F(z) = ∑ pₙ zⁿ` for `|z| < R` (the generating function of the
`pₙ`; for a family `F(x; z)` apply this for each fixed `x`), then
`pₙ = (2πi)⁻¹ ∮_{|z| = r} F(z) z^{-n-1} dz` for `0 < r < R`. -/
@[dlmf 1.10.E26, dlmf 1.10.E27]
theorem coeff_eq_circleIntegral {p : ℕ → ℂ} {F : ℂ → ℂ} {R : ℝ}
    (hF : ∀ z ∈ ball (0 : ℂ) R, HasSum (fun n => p n * z ^ n) (F z)) {r : ℝ} (hr : r ∈ Ioo 0 R)
    (n : ℕ) : p n = (2 * Real.pi * I)⁻¹ * ∮ z in C(0, r), F z / z ^ (n + 1) := by
  obtain ⟨ρ, hrρ, hρR⟩ := exists_between hr.2
  have hρ : 0 < ρ := hr.1.trans hrρ
  let s : NNReal := ⟨ρ, hρ.le⟩
  have hp := Complex.hasFPowerSeriesOnBall_of_hasSum_ball (ρ := s)
    (by exact_mod_cast hρ) hρR (fun z hz => hF z (by simpa using hz))
  have hsball : Metric.eball (0 : ℂ) (s : ENNReal) = ball (0 : ℂ) ρ := Metric.eball_coe
  have hd : DifferentiableOn ℂ F (closedBall 0 r) := by
    apply hp.differentiableOn.mono
    rw [hsball]
    exact closedBall_subset_ball hrρ
  let r₀ : NNReal := ⟨r, hr.1.le⟩
  have hr₀ : (r₀ : ℝ) = r := rfl
  have hc := hd.hasFPowerSeriesOnBall (R := r₀) (by exact_mod_cast hr.1)
  have heq := hp.hasFPowerSeriesAt.eq_formalMultilinearSeries hc.hasFPowerSeriesAt
  have h := congrArg (fun q : FormalMultilinearSeries ℂ ℂ ℂ => q n (fun _ => 1)) heq
  simpa [FormalMultilinearSeries.ofScalars_apply_eq, cauchyPowerSeries, cauchyPowerSeries_apply,
    smul_eq_mul, sub_zero, div_eq_mul_inv, pow_succ, mul_inv, inv_pow, hr₀,
    mul_comm, mul_left_comm, mul_assoc] using h

end DLMF.AlgebraicAnalytic
