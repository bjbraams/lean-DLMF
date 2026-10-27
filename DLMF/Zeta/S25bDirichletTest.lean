/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.NumberTheory.LSeries.HurwitzZeta

/-!
# Dirichlet's test for Dirichlet series with bounded partial sums

If the partial sums of `c : ℕ → ℂ` are bounded and `a > 0`, the series `∑ c n (n + a)^{-s}`
converges for `Re s > 0`, as a limit of partial sums, to a function holomorphic on `Re s > 0`
(`DLMF.Zeta.s25b_dirichlet_test`). The proof is summation by parts together with the mean-value
bound `|(x+1)^{-s} - x^{-s}| ≤ |s| x^{-Re s - 1}`, which makes the transformed series locally
uniformly absolutely convergent. Used for the conditionally convergent series of DLMF §25.11 and
§25.13 (25.11.8, 25.11.9, 25.13.1); in particular the partial sums of `∑_{n≥1} e^{2πinx}/n^s` tend
to Mathlib's `expZeta x s` for `x ∉ ℤ`, `Re s > 0` (`DLMF.Zeta.s25b_tendsto_expZeta`).
-/

@[expose] public section

open Complex Filter Set Finset HurwitzZeta
open scoped Real Topology

noncomputable section

namespace DLMF.Zeta

/-- Summation by parts with partial sums `A N = ∑_{n<N} c n`. -/
lemma s25b_sum_by_parts (c f : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ range N, c n * f n = (∑ n ∈ range N, c n) * f N -
      ∑ n ∈ range N, (∑ k ∈ range (n + 1), c k) * (f (n + 1) - f n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun n => (∑ k ∈ range (n + 1), c k) * _),
      sum_range_succ c]
    ring

/-- Mean-value bound `|(x+1)^{-s} - x^{-s}| ≤ |s| x^{-Re s - 1}` for `x > 0`. -/
lemma s25b_norm_cpow_succ_sub_le {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : -1 ≤ s.re) :
    ‖(((x + 1 : ℝ)) : ℂ) ^ (-s) - (x : ℂ) ^ (-s)‖ ≤ ‖s‖ * x ^ (-s.re - 1) := by
  have hd : ∀ t ∈ Icc x (x + 1), HasDerivWithinAt (fun t : ℝ => (t : ℂ) ^ (-s))
      (-s * (t : ℂ) ^ (-s - 1)) (Icc x (x + 1)) t := by
    intro t ht
    have ht0 : 0 < t := hx.trans_le ht.1
    have h := ((hasDerivAt_id (t : ℂ)).cpow_const (c := -s)
      (Or.inl (by simpa using ht0))).comp_ofReal
    simpa using h.hasDerivWithinAt
  have hb : ∀ t ∈ Ico x (x + 1), ‖-s * (t : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * x ^ (-s.re - 1) := by
    intro t ht
    have ht0 : 0 < t := hx.trans_le ht.1
    rw [norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos ht0]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    simp only [sub_re, neg_re, one_re]
    exact Real.rpow_le_rpow_of_nonpos hx ht.1 (by linarith)
  have := norm_image_sub_le_of_norm_deriv_le_segment' hd hb (x + 1) ⟨by linarith, le_rfl⟩
  simpa using this


/-- `∑ (n + a)^p` converges for `a > 0`, `p < -1`. -/
lemma s25b_summable_nat_add_rpow {a : ℝ} (ha : 0 < a) {p : ℝ} (hp : p < -1) :
    Summable (fun n : ℕ => ((n : ℝ) + a) ^ p) := by
  have h := (Real.summable_one_div_nat_add_rpow a (-p)).mpr (by linarith)
  refine h.congr fun n => ?_
  have hpos : 0 < (n : ℝ) + a := by positivity
  rw [abs_of_pos hpos, Real.rpow_neg hpos.le, one_div, inv_inv]

/-- `x^{-σ-1} ≤ x^{-σ₀-1} + x^{-R-1}` for `x > 0` and `σ₀ ≤ σ ≤ R`. -/
theorem s25b_rpow_le_add {x σ σ₀ R : ℝ} (hx : 0 < x) (h0 : σ₀ ≤ σ) (h1 : σ ≤ R) :
    x ^ (-σ - 1) ≤ x ^ (-σ₀ - 1) + x ^ (-R - 1) := by
  rcases le_or_gt 1 x with hx1 | hx1
  · have := Real.rpow_le_rpow_of_exponent_le hx1 (show -σ - 1 ≤ -σ₀ - 1 by linarith)
    linarith [Real.rpow_nonneg hx.le (-R - 1)]
  · have := Real.rpow_le_rpow_of_exponent_ge hx hx1.le (show -R - 1 ≤ -σ - 1 by linarith)
    linarith [Real.rpow_nonneg hx.le (-σ₀ - 1)]

/-- **Dirichlet's test, holomorphic form**: if the partial sums of `c` are bounded and `a > 0`,
then `∑ c n (n + a)^{-s}` converges for `Re s > 0` (as a limit of partial sums) to a function
holomorphic on `Re s > 0`. -/
theorem s25b_dirichlet_test {c : ℕ → ℂ} {C : ℝ} (hC : ∀ N, ‖∑ n ∈ range N, c n‖ ≤ C)
    {a : ℝ} (ha : 0 < a) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s | 0 < s.re} ∧ ∀ s : ℂ, 0 < s.re →
      Tendsto (fun N => ∑ n ∈ range N, c n * (((n + a : ℝ)) : ℂ) ^ (-s)) atTop (𝓝 (G s)) := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  set A : ℕ → ℂ := fun N => ∑ n ∈ range N, c n
  set f : ℕ → ℂ → ℂ := fun n s => (((n + a : ℝ)) : ℂ) ^ (-s)
  set T : ℕ → ℂ → ℂ := fun n s => A (n + 1) * (f (n + 1) s - f n s)
  have hpos : ∀ n : ℕ, 0 < (n : ℝ) + a := fun n => by positivity
  have hT : ∀ n s, -1 ≤ s.re → ‖T n s‖ ≤ C * (‖s‖ * ((n : ℝ) + a) ^ (-s.re - 1)) := by
    intro n s hs
    simp only [T, f, norm_mul]
    refine mul_le_mul (hC _) ?_ (norm_nonneg _) hC0
    have := s25b_norm_cpow_succ_sub_le (hpos n) hs
    convert this using 4
    push_cast; ring
  refine ⟨fun s => -∑' n, T n s, ?_, fun s hs => ?_⟩
  · intro s₀ hs₀
    have hs₀' : 0 < s₀.re := hs₀
    set σ₀ := s₀.re / 2
    set R := ‖s₀‖ + 1
    set U : Set ℂ := {s | σ₀ < s.re ∧ ‖s‖ < R}
    have hU : IsOpen U := (isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)
    have hmem : s₀ ∈ U := ⟨by simp only [σ₀]; linarith, by simp only [R]; linarith⟩
    have hσ₀ : 0 < σ₀ := by simp only [σ₀]; linarith
    have hR : σ₀ < R := by
      simp only [σ₀, R]; linarith [re_le_norm s₀]
    have hu : Summable fun n : ℕ => C * (R * (((n : ℝ) + a) ^ (-σ₀ - 1) +
        ((n : ℝ) + a) ^ (-R - 1))) :=
      (((s25b_summable_nat_add_rpow ha (by linarith)).add
        (s25b_summable_nat_add_rpow ha (by linarith))).mul_left R).mul_left C
    have hdiff : DifferentiableOn ℂ (fun s => ∑' n, T n s) U := by
      refine differentiableOn_tsum_of_summable_norm hu (fun n s _ => ?_) hU (fun n s hs => ?_)
      · refine (DifferentiableAt.const_mul (DifferentiableAt.sub ?_ ?_) _).differentiableWithinAt
        · exact (differentiableAt_id.neg).const_cpow (Or.inl (by exact_mod_cast (hpos (n + 1)).ne'))
        · exact (differentiableAt_id.neg).const_cpow (Or.inl (by exact_mod_cast (hpos n).ne'))
      · obtain ⟨h1, h2⟩ := hs
        refine (hT n s (by linarith)).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ hC0
        refine mul_le_mul h2.le (s25b_rpow_le_add (hpos n) h1.le ?_) (by positivity)
          (by linarith)
        exact (re_le_norm s).trans h2.le
    exact ((hdiff.differentiableAt (hU.mem_nhds hmem)).neg).differentiableWithinAt
  · have hsum : Summable fun n => T n s := by
      refine Summable.of_norm_bounded
        (((s25b_summable_nat_add_rpow ha (p := -s.re - 1) (by linarith)).mul_left ‖s‖).mul_left
          C) ?_
      exact fun n => hT n s (by linarith)
    have h1 := hsum.hasSum.tendsto_sum_nat
    have h2 : Tendsto (fun N => A N * f N s) atTop (𝓝 0) := by
      have h0 := (tendsto_rpow_neg_atTop hs).comp
        (tendsto_atTop_add_const_right _ a tendsto_natCast_atTop_atTop) |>.const_mul C
      rw [mul_zero] at h0
      refine squeeze_zero_norm (fun N => ?_) h0
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (hpos N)]
      simp only [neg_re, Function.comp_apply]
      exact mul_le_mul (hC N) le_rfl (by positivity) hC0
    have := h2.sub h1
    rw [zero_sub] at this
    refine this.congr fun N => ?_
    exact (s25b_sum_by_parts c (fun n => f n s) N).symm

/-- `{Re s > 0} \ {1}` is preconnected. -/
theorem s25b_isPreconnected_re_pos_diff_one :
    IsPreconnected ({s : ℂ | 0 < s.re} \ {1}) := by
  set Q1 : Set ℂ := {s | 0 < s.re ∧ 0 < s.im}
  set Q2 : Set ℂ := {s | 0 < s.re ∧ s.im < 0}
  set Q3 : Set ℂ := {s | 0 < s.re ∧ s.re < 1}
  set Q4 : Set ℂ := {s | 1 < s.re}
  have c1 : Convex ℝ Q1 := (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)
  have c2 : Convex ℝ Q2 := (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0)
  have c3 : Convex ℝ Q3 := (convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)
  have c4 : Convex ℝ Q4 := convex_halfSpace_re_gt 1
  have h13 := c1.isPreconnected.union (1 / 2 + I) (by norm_num [Q1])
    (by norm_num [Q3]) c3.isPreconnected
  have h132 := h13.union (1 / 2 - I) (by norm_num [Q3]) (by norm_num [Q2])
    c2.isPreconnected
  have h := h132.union (2 + I) (by norm_num [Q1]) (by norm_num [Q4])
    c4.isPreconnected
  convert h using 1
  ext s
  simp only [Set.mem_sdiff, mem_ofPred_eq, Set.mem_singleton_iff, mem_union, Q1, Q2, Q3, Q4]
  constructor
  · rintro ⟨h0, h1⟩
    rcases lt_trichotomy s.im 0 with hi | hi | hi
    · exact Or.inl (Or.inr ⟨h0, hi⟩)
    · rcases lt_trichotomy s.re 1 with hr | hr | hr
      · exact Or.inl (Or.inl (Or.inr ⟨h0, hr⟩))
      · exact absurd (Complex.ext (by simpa using hr) (by simpa using hi)) h1
      · exact Or.inr hr
    · exact Or.inl (Or.inl (Or.inl ⟨h0, hi⟩))
  · rintro (((⟨h0, h1⟩ | ⟨h0, h1⟩) | ⟨h0, h1⟩) | h0)
    · exact ⟨h0, fun h => by subst h; simp at h1⟩
    · exact ⟨h0, fun h => by subst h; simp at h1⟩
    · exact ⟨h0, fun h => by subst h; simp at h1⟩
    · exact ⟨by linarith, fun h => by subst h; simp at h0⟩

/-- Bounded partial sums of `∑_{n≥1} wⁿ` for `|w| = 1`, `w ≠ 1`. -/
lemma s25b_norm_geom_sum_le {w : ℂ} (hw : ‖w‖ = 1) (hw1 : w ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, w ^ (n + 1)‖ ≤ 2 / ‖w - 1‖ := by
  have hw1' : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
  have hpos : 0 < ‖w - 1‖ := norm_pos_iff.mpr hw1'
  have h : ∑ n ∈ Finset.range N, w ^ (n + 1) = w * ((w ^ N - 1) / (w - 1)) := by
    rw [← geom_sum_eq hw1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [h, norm_mul, hw, one_mul, norm_div, div_le_div_iff_of_pos_right hpos]
  calc ‖w ^ N - 1‖ ≤ ‖w ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hw, one_pow, norm_one]; norm_num

/-- Identity theorem on the half-plane `Re s > 0` from agreement on `Re s > 1`. -/
lemma s25b_eqOn_re_pos {F G : ℂ → ℂ} (hF : DifferentiableOn ℂ F {s | 0 < s.re})
    (hG : DifferentiableOn ℂ G {s | 0 < s.re}) (h : ∀ s : ℂ, 1 < s.re → F s = G s) :
    EqOn F G {s | 0 < s.re} := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
  have hc : IsPreconnected {s : ℂ | 0 < s.re} :=
    (convex_halfSpace_re_gt 0).isPreconnected
  refine (hF.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hG.analyticOnNhd hU) hc
    (show (2 : ℂ) ∈ {s : ℂ | 0 < s.re} by norm_num) ?_
  have hopen : IsOpen {t : ℂ | 1 < t.re} := isOpen_lt continuous_const continuous_re
  filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with t ht
  exact h t ht

/-- Partial sums of `∑_{n≥1} e^{2πinx}/n^s` tend to `F(x, s)` for `Re s > 1`. -/
lemma s25b_tendsto_expZeta_of_one_lt_re (x : ℝ) {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
        cexp (2 * π * I * (n + 1) * x) / ((n : ℂ) + 1) ^ s) atTop
      (𝓝 (expZeta (x : UnitAddCircle) s)) := by
  have h1 := (hasSum_nat_add_iff' 1).mpr (hasSum_expZeta_of_one_lt_re x hs)
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs; linarith
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_cpow hs0,
    div_zero, sub_zero] at h1
  refine h1.tendsto_sum_nat.congr fun N => Finset.sum_congr rfl fun n _ => ?_
  push_cast; ring_nf

/-- **DLMF 25.13.1 in both ranges**: the partial sums of `∑_{n≥1} e^{2πinx}/n^s` tend to
`F(x, s) = expZeta x s` if `x ∉ ℤ` and `Re s > 0`, or if `Re s > 1`. -/
theorem s25b_tendsto_expZeta {x : ℝ} {s : ℂ} (h : ((∀ m : ℤ, x ≠ m) ∧ 0 < s.re) ∨ 1 < s.re) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
        cexp (2 * π * I * (n + 1) * x) / ((n : ℂ) + 1) ^ s) atTop
      (𝓝 (expZeta (x : UnitAddCircle) s)) := by
  rcases h with ⟨hx, hs⟩ | hs
  swap
  · exact s25b_tendsto_expZeta_of_one_lt_re x hs
  set w := cexp (2 * π * I * x)
  have hw : ‖w‖ = 1 := by
    simp only [w]
    rw [show 2 * π * I * x = ((2 * π * x : ℝ) : ℂ) * I by push_cast; ring]
    exact norm_exp_ofReal_mul_I _
  have hw1 : w ≠ 1 := by
    intro h
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp h
    apply hx m
    have hpi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    have : (x : ℂ) = m := by
      apply mul_left_cancel₀ hpi; linear_combination hm
    exact_mod_cast this
  have hterm : ∀ (n : ℕ) (t : ℂ), cexp (2 * π * I * (n + 1) * x) / ((n : ℂ) + 1) ^ t =
      w ^ (n + 1) * (((n + 1 : ℝ)) : ℂ) ^ (-t) := by
    intro n t
    rw [← Complex.exp_nat_mul, cpow_neg, div_eq_mul_inv]
    push_cast; ring_nf
  obtain ⟨G, hG, hT⟩ := s25b_dirichlet_test (c := fun n => w ^ (n + 1))
    (s25b_norm_geom_sum_le hw hw1) one_pos
  have hx0 : (x : UnitAddCircle) ≠ 0 := by
    rw [Ne, AddCircle.coe_eq_zero_iff]
    rintro ⟨m, hm⟩
    exact hx m (by simpa using hm.symm)
  have heq : EqOn G (expZeta (x : UnitAddCircle)) {s | 0 < s.re} := by
    refine s25b_eqOn_re_pos hG (differentiable_expZeta_of_ne_zero hx0).differentiableOn
      fun t ht => ?_
    refine tendsto_nhds_unique (hT t (by linarith)) ?_
    exact (s25b_tendsto_expZeta_of_one_lt_re x ht).congr fun N =>
      Finset.sum_congr rfl fun n _ => hterm n t
  rw [← heq hs]
  refine (hT s hs).congr fun N => Finset.sum_congr rfl fun n _ => (hterm n s).symm

end DLMF.Zeta

end
