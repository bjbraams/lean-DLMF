/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Basic.Hurwitz
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Complex.Liouville

/-!
# Sector bounds for the Hurwitz Euler–Maclaurin remainder

Uniform bounds for the Euler–Maclaurin increments on closed sectors separated from the
negative real axis. Taking enough correction terms gives summable product majorants in
the argument and in the increment index. Compact uniformity in the order parameter and
Cauchy’s estimate give the corresponding bounds for the order derivative.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics
open scoped Nat Real Topology

namespace DLMF.Zeta.HurwitzSectorRemainder

/-- Uniform increment constants can be chosen continuously in the order parameter. -/
lemma exists_continuous_increment_bound (M : ℕ) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < π) :
    ∃ F : ℂ → ℝ, Continuous F ∧ (∀ s, 0 ≤ F s) ∧ ∀ s : ℂ, s ≠ 1 →
      0 ≤ s.re + (2 * M + 1) → ∀ a : ℂ, |arg a| ≤ π - δ → 1 ≤ ‖a‖ → ∀ n : ℕ,
      ‖eulerMaclaurinIncrement M s (a + n)‖ ≤
        F s * ‖a‖ ^ (-(s.re + (2 * M + 1)) / 2) *
          ((n : ℝ) + 1) ^ (-(s.re + (2 * M + 1)) / 2) := by
  obtain ⟨c, hc, hcle⟩ := Complex.sector_norm_add_ofReal_bound hδ0 hδ
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(bernoulliFun (2 * M + 1) t : ℂ)‖ ≤ B :=
    isCompact_Icc.exists_bound_of_continuousOn (by fun_prop)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, zero_le_one⟩)
  let F : ℂ → ℝ := fun s =>
    ‖DLMF.Hypergeometric.pochhammer s (2 * M + 1) / ((2 * M + 1 : ℕ)! : ℂ)‖ * B *
      Real.exp (π * |s.im|) * c ^ (-(s.re + (2 * M + 1)))
  have hpoch : Continuous (fun s : ℂ => DLMF.Hypergeometric.pochhammer s (2 * M + 1)) :=
    continuous_iff_continuousAt.mpr fun s => (differentiableAt_pochhammer _ s).continuousAt
  have hFc : Continuous F := by
    dsimp [F]
    fun_prop
  have hF0 : ∀ s, 0 ≤ F s := by intro s; dsimp [F]; positivity
  refine ⟨F, hFc, hF0, fun s hs hM => ?_⟩
  let p : ℝ := s.re + (2 * M + 1)
  let A : ℝ := ‖DLMF.Hypergeometric.pochhammer s (2 * M + 1) /
    ((2 * M + 1 : ℕ)! : ℂ)‖
  let C : ℝ := A * B * Real.exp (π * |s.im|) * c ^ (-p)
  have hC : 0 ≤ C := by dsimp [C, A]; positivity
  intro a ha hr n
  have ha0 : a ≠ 0 := by intro h; norm_num [h] at hr
  have haslit : a ∈ slitPlane := by
    refine mem_slitPlane_iff_arg.mpr ⟨?_, ha0⟩
    intro h
    rw [h, abs_of_pos Real.pi_pos] at ha
    linarith
  have hnaslit : a + (n : ℂ) ∈ slitPlane := by
    simpa only [Complex.ofReal_natCast] using
      Complex.add_ofReal_mem_slitPlane_of_nonneg haslit (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hnp : 0 < c * (‖a‖ + n) := by positivity
  have hI : ‖∫ t in (0 : ℝ)..1,
        (a + n + t) ^ (-s - (2 * M + 1 : ℕ)) * (bernoulliFun (2 * M + 1) t : ℂ)‖ ≤
      (c * (‖a‖ + n)) ^ (-p) * Real.exp (π * |s.im|) * B := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (f := fun t : ℝ => (a + n + t) ^ (-s - (2 * M + 1 : ℕ)) *
        (bernoulliFun (2 * M + 1) t : ℂ))
      (C := (c * (‖a‖ + n)) ^ (-p) * Real.exp (π * |s.im|) * B) (fun t ht => ?_)
    · simpa using h
    rw [uIoc_of_le zero_le_one] at ht
    have ht0 : 0 ≤ t := ht.1.le
    have hnorm : c * (‖a‖ + n) ≤ ‖a + (n : ℂ) + t‖ := by
      have h := hcle a ha ((n : ℝ) + t) (by positivity)
      have heq : a + (((n : ℝ) + t : ℝ) : ℂ) = a + (n : ℂ) + t := by push_cast; ring
      rw [heq] at h
      nlinarith
    have hpow := Complex.norm_cpow_le_of_norm_lower_bound hnp hnorm
      (s := -s - (2 * M + 1 : ℕ)) (by simp; linarith)
    have hbound : ‖(a + n + t) ^ (-s - (2 * M + 1 : ℕ))‖ ≤
        (c * (‖a‖ + n)) ^ (-p) * Real.exp (π * |s.im|) := by
      have hre : (-s - (2 * M + 1 : ℕ) : ℂ).re = -p := by
        simp only [sub_re, neg_re, natCast_re, p]
        push_cast
        ring
      have him : |(-s - (2 * M + 1 : ℕ) : ℂ).im| = |s.im| := by simp
      simpa only [hre, him] using hpow
    rw [norm_mul]
    exact mul_le_mul hbound (hB t ⟨ht0, ht.2⟩) (norm_nonneg _) (by positivity)
  have hstep : ‖eulerMaclaurinIncrement M s (a + n)‖ ≤
      C * (‖a‖ + n) ^ (-p) := by
    unfold eulerMaclaurinIncrement
    rw [cpow_add_eulerMaclaurinTail_sub_eq_integral_of_mem_slitPlane hs hnaslit M,
      norm_mul, norm_neg]
    calc ‖DLMF.Hypergeometric.pochhammer s (2 * M + 1) /
          ((2 * M + 1 : ℕ)! : ℂ)‖ * ‖∫ t in (0 : ℝ)..1,
            (a + n + t) ^ (-s - (2 * M + 1 : ℕ)) *
              (bernoulliFun (2 * M + 1) t : ℂ)‖ ≤
        A * ((c * (‖a‖ + n)) ^ (-p) * Real.exp (π * |s.im|) * B) := by
          exact mul_le_mul_of_nonneg_left hI (norm_nonneg _)
      _ = _ := by rw [Real.mul_rpow hc.le (by positivity)]; dsimp only [C]; ring
  have hdecay := Real.add_rpow_le_mul_rpow_half hr (Nat.cast_nonneg n) hM
  calc ‖eulerMaclaurinIncrement M s (a + n)‖ ≤ C * (‖a‖ + n) ^ (-p) := hstep
    _ ≤ _ := by
      dsimp only [p] at hstep ⊢
      nlinarith [mul_le_mul_of_nonneg_left hdecay hC]

/-- A summable product bound for the Euler–Maclaurin increments on a closed sector. -/
lemma exists_increment_bound {s : ℂ} (hs : s ≠ 1) (M : ℕ)
    (hM : 0 ≤ s.re + (2 * M + 1)) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < π) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℂ, |arg a| ≤ π - δ → 1 ≤ ‖a‖ → ∀ n : ℕ,
      ‖eulerMaclaurinIncrement M s (a + n)‖ ≤
        C * ‖a‖ ^ (-(s.re + (2 * M + 1)) / 2) *
          ((n : ℝ) + 1) ^ (-(s.re + (2 * M + 1)) / 2) := by
  obtain ⟨F, -, hF0, hF⟩ := exists_continuous_increment_bound M hδ0 hδ
  exact ⟨F s, hF0 s, hF s hs hM⟩

/-- A summable majorant for the increments bounds the full Euler–Maclaurin remainder. -/
lemma norm_sub_tail_le_of_summable_bound {s a : ℂ} (hs : s ≠ 1) (M : ℕ)
    (hM : 0 < s.re + 2 * M) {u : ℕ → ℝ} (hu : Summable u)
    (hinc : ∀ n : ℕ, ‖eulerMaclaurinIncrement M s (a + n)‖ ≤ u n) :
    ‖hurwitzZetaComplex s a - eulerMaclaurinTail M s a‖ ≤ ∑' n, u n := by
  have hsum : Summable (fun n : ℕ => eulerMaclaurinIncrement M s (a + n)) :=
    Summable.of_norm_bounded hu hinc
  have hzero : eulerMaclaurinSeq M s a 0 = eulerMaclaurinTail M s a := by
    simp [eulerMaclaurinSeq]
  have he (N : ℕ) : eulerMaclaurinSeq M s a N = eulerMaclaurinTail M s a +
      ∑ n ∈ Finset.range N, eulerMaclaurinIncrement M s (a + n) := by
    simpa only [Nat.zero_add, hzero] using eulerMaclaurinSeq_add M s a 0 N
  have ht := (hsum.hasSum.tendsto_sum_nat.const_add (eulerMaclaurinTail M s a)).congr
    (fun N => (he N).symm)
  have hζ : hurwitzZetaComplex s a - eulerMaclaurinTail M s a =
      ∑' n : ℕ, eulerMaclaurinIncrement M s (a + n) := by
    have h := tendsto_nhds_unique (tendsto_eulerMaclaurinSeq_hurwitzZetaComplex hs hM) ht
    linear_combination h
  rw [hζ]
  exact tsum_of_norm_bounded hu.hasSum hinc

/-- With enough correction terms, the full Euler–Maclaurin remainder has uniform power decay
on each closed sector away from the cut. -/
lemma exists_remainder_bound {s : ℂ} (hs : s ≠ 1) (M : ℕ)
    (hM : 1 < (s.re + (2 * M + 1)) / 2) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < π) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℂ, |arg a| ≤ π - δ → 1 ≤ ‖a‖ →
      ‖hurwitzZetaComplex s a - eulerMaclaurinTail M s a‖ ≤
        C * ‖a‖ ^ (-(s.re + (2 * M + 1)) / 2) := by
  obtain ⟨C, hC, hbound⟩ := exists_increment_bound hs M (by linarith) hδ0 hδ
  let q : ℝ := (s.re + (2 * M + 1)) / 2
  let w : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (-q)
  have hw : Summable w := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow.mpr (show -q < -1 by dsimp [q]; linarith))
    simpa only [w, Nat.cast_add, Nat.cast_one] using h
  have hW : 0 ≤ ∑' n, w n := tsum_nonneg fun n => by dsimp [w]; positivity
  refine ⟨C * ∑' n, w n, mul_nonneg hC hW, fun a ha hr => ?_⟩
  have hmaj : Summable (fun n => (C * ‖a‖ ^ (-q)) * w n) :=
    hw.mul_left (C * ‖a‖ ^ (-q))
  have hinc (n : ℕ) : ‖eulerMaclaurinIncrement M s (a + n)‖ ≤
      (C * ‖a‖ ^ (-q)) * w n := by
    simpa only [w, q, neg_div] using hbound a ha hr n
  calc ‖hurwitzZetaComplex s a - eulerMaclaurinTail M s a‖ ≤
      ∑' n, (C * ‖a‖ ^ (-q)) * w n :=
        norm_sub_tail_le_of_summable_bound hs M (by linarith) hmaj hinc
    _ = _ := by rw [tsum_mul_left]; dsimp only [q]; rw [neg_div]; ring

/-- The remainder bound is uniform over compact sets of order parameters. -/
lemma exists_uniform_remainder_bound {S : Set ℂ} (hS : IsCompact S) {σ : ℝ}
    (hσ : ∀ s ∈ S, σ ≤ s.re) (M : ℕ) (hM : 1 < (σ + (2 * M + 1)) / 2)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < π) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ S, s ≠ 1 → ∀ a : ℂ,
      |arg a| ≤ π - δ → 1 ≤ ‖a‖ →
      ‖hurwitzZetaComplex s a - eulerMaclaurinTail M s a‖ ≤
        C * ‖a‖ ^ (-(σ + (2 * M + 1)) / 2) := by
  obtain ⟨F, hFc, hF0, hF⟩ := exists_continuous_increment_bound M hδ0 hδ
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hFc.continuousOn
  let D : ℝ := max B 0
  have hD : 0 ≤ D := le_max_right _ _
  have hFs : ∀ s ∈ S, F s ≤ D := by
    intro s hs
    have hb : |F s| ≤ B := by simpa only [Real.norm_eq_abs] using hB s hs
    exact (le_abs_self (F s)).trans (hb.trans (le_max_left B 0))
  let q : ℝ := (σ + (2 * M + 1)) / 2
  let w : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (-q)
  have hw : Summable w := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow.mpr (show -q < -1 by dsimp [q]; linarith))
    simpa only [w, Nat.cast_add, Nat.cast_one] using h
  have hW : 0 ≤ ∑' n, w n := tsum_nonneg fun n => by dsimp [w]; positivity
  refine ⟨D * ∑' n, w n, mul_nonneg hD hW, fun s hs hs1 a ha hr => ?_⟩
  have hσs := hσ s hs
  have hinc (n : ℕ) : ‖eulerMaclaurinIncrement M s (a + n)‖ ≤
      (D * ‖a‖ ^ (-q)) * w n := by
    have hb := hF s hs1 (by linarith) a ha hr n
    have he : -(s.re + (2 * M + 1)) / 2 ≤ -q := by dsimp [q]; linarith
    calc ‖eulerMaclaurinIncrement M s (a + n)‖ ≤
        F s * ‖a‖ ^ (-(s.re + (2 * M + 1)) / 2) *
          ((n : ℝ) + 1) ^ (-(s.re + (2 * M + 1)) / 2) := hb
      _ ≤ D * ‖a‖ ^ (-q) * ((n : ℝ) + 1) ^ (-q) := by
        have hpa := Real.rpow_le_rpow_of_exponent_le hr he
        have hpn := Real.rpow_le_rpow_of_exponent_le
          (by linarith [Nat.cast_nonneg (α := ℝ) n] : 1 ≤ (n : ℝ) + 1) he
        exact mul_le_mul (mul_le_mul (hFs s hs) hpa (by positivity) hD) hpn
          (by positivity) (by positivity)
      _ = _ := rfl
  have hmaj := hw.mul_left (D * ‖a‖ ^ (-q))
  calc ‖hurwitzZetaComplex s a - eulerMaclaurinTail M s a‖ ≤
      ∑' n, (D * ‖a‖ ^ (-q)) * w n :=
        norm_sub_tail_le_of_summable_bound hs1 M (by linarith) hmaj hinc
    _ = _ := by rw [tsum_mul_left]; dsimp only [q]; rw [neg_div]; ring

/-- Holomorphy in the order of a finite Euler–Maclaurin tail. -/
lemma differentiableAt_tail_order (M : ℕ) {s a : ℂ} (hs : s ≠ 1) (ha : a ≠ 0) :
    DifferentiableAt ℂ (fun z => eulerMaclaurinTail M z a) s := by
  unfold eulerMaclaurinTail eulerMaclaurinCoeff
  refine DifferentiableAt.add (DifferentiableAt.add ?_ ?_)
    (DifferentiableAt.fun_sum fun k _ => ?_)
  · exact ((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl ha) |>.div
      (differentiableAt_id.sub (differentiableAt_const _)) (sub_ne_zero.mpr hs)
  · exact (differentiableAt_id.neg.const_cpow (Or.inl ha)).div_const _
  · exact ((differentiableAt_pochhammer _ s).const_mul _).mul
      ((differentiableAt_id.neg.sub (differentiableAt_const _)).const_cpow (Or.inl ha))

/-- Cauchy's estimate gives a sector bound for the order derivative of the remainder. -/
lemma exists_deriv_remainder_bound {s₀ : ℂ} (hs₀ : s₀.re ≤ 0) (M : ℕ)
    (hM : 1 < (s₀.re - 1 / 4 + (2 * M + 1)) / 2)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < π) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℂ, |arg a| ≤ π - δ → 1 ≤ ‖a‖ →
      ‖deriv (fun s => hurwitzZetaComplex s a - eulerMaclaurinTail M s a) s₀‖ ≤
        C * ‖a‖ ^ (-(s₀.re - 1 / 4 + (2 * M + 1)) / 2) := by
  have hsRe (s : ℂ) (hs : s ∈ Metric.closedBall s₀ (1 / 4 : ℝ)) :
      s₀.re - 1 / 4 ≤ s.re ∧ s.re ≤ s₀.re + 1 / 4 := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hs
    have h := (abs_re_le_norm (s - s₀)).trans hs
    simp only [sub_re] at h
    constructor <;> linarith [neg_abs_le (s.re - s₀.re), le_abs_self (s.re - s₀.re)]
  have hs1 (s : ℂ) (hs : s ∈ Metric.closedBall s₀ (1 / 4 : ℝ)) : s ≠ 1 := by
    have h := (hsRe s hs).2
    intro he
    rw [he, one_re] at h
    linarith
  obtain ⟨C, hC, hb⟩ := exists_uniform_remainder_bound (M := M)
    (isCompact_closedBall s₀ (1 / 4 : ℝ)) (σ := s₀.re - 1 / 4)
    (fun s hs => (hsRe s hs).1) hM hδ0 hδ
  refine ⟨4 * C, by positivity, fun a ha hr => ?_⟩
  have ha0 : a ≠ 0 := by intro h; norm_num [h] at hr
  have haslit : a ∈ slitPlane := by
    refine mem_slitPlane_iff_arg.mpr ⟨?_, ha0⟩
    intro h
    rw [h, abs_of_pos Real.pi_pos] at ha
    linarith
  have hnat : ∀ n : ℕ, a + n ≠ 0 := by
    intro n
    have h : a + (n : ℂ) ∈ slitPlane := by
      simpa only [Complex.ofReal_natCast] using
        Complex.add_ofReal_mem_slitPlane_of_nonneg haslit (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    exact slitPlane_ne_zero h
  have hd : DifferentiableOn ℂ
      (fun s => hurwitzZetaComplex s a - eulerMaclaurinTail M s a)
      (Metric.closedBall s₀ (1 / 4 : ℝ)) := by
    intro s hs
    exact ((differentiableAt_hurwitzZetaComplex_of_add_ne_zero (hs1 s hs) hnat).sub
      (differentiableAt_tail_order M (hs1 s hs) ha0)).differentiableWithinAt
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0 : ℝ) < 1 / 4) (hd.diffContOnCl_ball Subset.rfl)
    (fun s hs => hb s (Metric.sphere_subset_closedBall hs)
      (hs1 s (Metric.sphere_subset_closedBall hs)) a ha hr)
  calc ‖deriv (fun s => hurwitzZetaComplex s a - eulerMaclaurinTail M s a) s₀‖ ≤
      (C * ‖a‖ ^ (-(s₀.re - 1 / 4 + (2 * M + 1)) / 2)) / (1 / 4) := h
    _ = _ := by ring

/-- A sufficiently deep Euler–Maclaurin tail approximates the order derivative to any prescribed
integral power on a closed sector. -/
lemma isBigO_deriv_sub_tail {s₀ : ℂ} (hs₀ : s₀.re ≤ 0) (M L : ℕ)
    (hM : 1 < (s₀.re - 1 / 4 + (2 * M + 1)) / 2)
    (hL : L ≤ (s₀.re - 1 / 4 + (2 * M + 1)) / 2)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < π) :
    (fun a => deriv (fun s => hurwitzZetaComplex s a) s₀ -
      deriv (fun s => eulerMaclaurinTail M s a) s₀)
      =O[Bornology.cobounded ℂ ⊓ 𝓟 {a : ℂ | |arg a| ≤ π - δ}]
        (fun a => a ^ (-(L : ℤ))) := by
  obtain ⟨C, hC, hbound⟩ := exists_deriv_remainder_bound hs₀ M hM hδ0 hδ
  refine IsBigO.of_bound C ?_
  have hr : ∀ᶠ a : ℂ in Bornology.cobounded ℂ ⊓ 𝓟 {a : ℂ | |arg a| ≤ π - δ},
      1 ≤ ‖a‖ := Filter.Eventually.filter_mono inf_le_left (eventually_cobounded_le_norm 1)
  have ha : ∀ᶠ a : ℂ in Bornology.cobounded ℂ ⊓ 𝓟 {a : ℂ | |arg a| ≤ π - δ},
      |arg a| ≤ π - δ :=
    Filter.Eventually.filter_mono inf_le_right (Filter.eventually_principal.mpr fun _ h => h)
  filter_upwards [hr, ha] with a hr ha
  have ha0 : a ≠ 0 := by intro h; norm_num [h] at hr
  have hs1 : s₀ ≠ 1 := by intro h; rw [h, one_re] at hs₀; linarith
  have haslit : a ∈ slitPlane := by
    refine mem_slitPlane_iff_arg.mpr ⟨?_, ha0⟩
    intro h
    rw [h, abs_of_pos Real.pi_pos] at ha
    linarith
  have hnat : ∀ n : ℕ, a + n ≠ 0 := by
    intro n
    have h : a + (n : ℂ) ∈ slitPlane := by
      simpa only [Complex.ofReal_natCast] using
        Complex.add_ofReal_mem_slitPlane_of_nonneg haslit (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    exact slitPlane_ne_zero h
  rw [← deriv_sub (differentiableAt_hurwitzZetaComplex_of_add_ne_zero hs1 hnat)
    (differentiableAt_tail_order M hs1 ha0)]
  have h := (hbound a ha hr).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hr
      (show -(s₀.re - 1 / 4 + (2 * M + 1)) / 2 ≤ -(L : ℝ) by linarith)) hC)
  have h' : ‖deriv (fun s => hurwitzZetaComplex s a - eulerMaclaurinTail M s a) s₀‖ ≤
      C * ‖a‖ ^ (-(L : ℤ)) := by
    convert h using 1
    rw [← Real.rpow_intCast]
    simp only [Int.cast_neg, Int.cast_natCast]
  have hfun : ((fun s => hurwitzZetaComplex s a) -
      fun s => eulerMaclaurinTail M s a) =
      (fun s => hurwitzZetaComplex s a - eulerMaclaurinTail M s a) := by
    funext s
    rfl
  rw [hfun]
  simpa only [norm_zpow] using h'

/-- The Euler–Maclaurin remainder is bounded by its first omitted power on closed sectors. -/
lemma isBigO_sub_tail {s : ℂ} (hs : s ≠ 1) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < π)
    (K : ℕ) :
    (fun a => hurwitzZetaComplex s a - eulerMaclaurinTail K s a)
      =O[Bornology.cobounded ℂ ⊓ 𝓟 {a : ℂ | |arg a| ≤ π - δ}]
        (fun a => a ^ (-s - (2 * K + 1 : ℕ))) := by
  let l : Filter ℂ := Bornology.cobounded ℂ ⊓ 𝓟 {a : ℂ | |arg a| ≤ π - δ}
  let M : ℕ := ⌈|s.re|⌉₊ + 2 * K + 2
  let v : ℂ := -s - (2 * K + 1 : ℕ)
  have hKM : K ≤ M := by dsimp [M]; omega
  have hM : 1 < (s.re + (2 * M + 1)) / 2 := by
    have := Nat.le_ceil |s.re|
    have := neg_abs_le s.re
    dsimp [M]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) K, abs_nonneg s.re]
  have hMv : -(s.re + (2 * M + 1)) / 2 ≤ v.re := by
    have := Nat.le_ceil |s.re|
    have := le_abs_self s.re
    simp only [M, v, sub_re, neg_re, natCast_re]
    push_cast
    linarith
  have hr : ∀ᶠ a : ℂ in l, 1 ≤ ‖a‖ :=
    Filter.Eventually.filter_mono inf_le_left (eventually_cobounded_le_norm 1)
  have ha : ∀ᶠ a : ℂ in l, |arg a| ≤ π - δ :=
    Filter.Eventually.filter_mono inf_le_right (Filter.eventually_principal.mpr fun _ h => h)
  obtain ⟨C, hC, hbound⟩ := exists_remainder_bound hs M hM hδ0 hδ
  have hrem : (fun a => hurwitzZetaComplex s a - eulerMaclaurinTail M s a)
      =O[l] (fun a => a ^ v) := by
    refine IsBigO.of_bound (C * Real.exp (π * |v.im|)) ?_
    filter_upwards [hr, ha] with a hr ha
    have ha0 : a ≠ 0 := by intro h; norm_num [h] at hr
    calc ‖hurwitzZetaComplex s a - eulerMaclaurinTail M s a‖ ≤
        C * ‖a‖ ^ (-(s.re + (2 * M + 1)) / 2) := hbound a ha hr
      _ ≤ C * ‖a‖ ^ v.re :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hr hMv) hC
      _ ≤ C * (‖a ^ v‖ * Real.exp (π * |v.im|)) :=
        mul_le_mul_of_nonneg_left (Complex.rpow_norm_le_norm_cpow_mul_exp ha0 v) hC
      _ = _ := by ring
  have hterm (k : ℕ) (hk : k ∈ Finset.Ico K M) :
      (fun a : ℂ => eulerMaclaurinCoeff s k * a ^ (-s - (2 * k + 1 : ℕ)))
        =O[l] (fun a => a ^ v) := by
    let u : ℂ := -s - (2 * k + 1 : ℕ)
    have huv : u.re ≤ v.re := by
      simp only [u, v, sub_re, neg_re, natCast_re]
      have := (Nat.cast_le (α := ℝ)).mpr (Finset.mem_Ico.mp hk).1
      push_cast
      linarith
    refine IsBigO.of_bound (‖eulerMaclaurinCoeff s k‖ *
      Real.exp (π * |u.im|) * Real.exp (π * |v.im|)) ?_
    filter_upwards [hr] with a hr
    have ha0 : a ≠ 0 := by intro h; norm_num [h] at hr
    have hpow : ‖a ^ u‖ ≤ ‖a‖ ^ u.re * Real.exp (π * |u.im|) := by
      apply (Complex.norm_cpow_le a u).trans
      rw [div_eq_mul_inv, ← Real.exp_neg]
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (norm_nonneg a) _)
      apply Real.exp_le_exp.mpr
      calc -(arg a * u.im) ≤ |arg a| * |u.im| := by rw [← abs_mul]; exact neg_le_abs _
        _ ≤ π * |u.im| := mul_le_mul_of_nonneg_right (abs_arg_le_pi a) (abs_nonneg _)
    change ‖eulerMaclaurinCoeff s k * a ^ u‖ ≤ _
    rw [norm_mul]
    calc ‖eulerMaclaurinCoeff s k‖ * ‖a ^ u‖ ≤
        ‖eulerMaclaurinCoeff s k‖ * (‖a‖ ^ u.re * Real.exp (π * |u.im|)) := by gcongr
      _ ≤ ‖eulerMaclaurinCoeff s k‖ * (‖a‖ ^ v.re * Real.exp (π * |u.im|)) := by
        gcongr
      _ ≤ ‖eulerMaclaurinCoeff s k‖ *
          ((‖a ^ v‖ * Real.exp (π * |v.im|)) * Real.exp (π * |u.im|)) := by
        gcongr
        exact Complex.rpow_norm_le_norm_cpow_mul_exp ha0 v
      _ = _ := by ring
  have hsum := Asymptotics.IsBigO.sum (s := Finset.Ico K M) hterm
  have h := hrem.add hsum
  apply h.congr_left
  intro a
  rw [Finset.sum_apply, Finset.sum_Ico_eq_sub _ hKM]
  unfold eulerMaclaurinTail
  push_cast
  ring

end DLMF.Zeta.HurwitzSectorRemainder
