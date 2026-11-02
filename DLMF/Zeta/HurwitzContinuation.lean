/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Basic.Hurwitz
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

/-!
# Continuation of the Hurwitz zeta function by Euler–Maclaurin summation

Holomorphy of the Hurwitz zeta function `ζ(s, z)` in `s` and in `z`, its `z`-derivative and the
pole at `s = 1` (DLMF §25.11(i), 25.11.17).

## Main definitions

* `subOneMulEulerMaclaurinSeq`: `(s - 1) E_N(s, a)`, written without division so that it is
  entire in `s`.

## Main results

* `differentiableAt_hurwitzZetaComplex_of_add_natCast_ne_zero'`: holomorphy in `s ≠ 1` for
  `z ≠ 0, -1, -2, …`.
* `differentiableOn_hurwitzZetaComplex_param'`: holomorphy in `a` on `Re a > 0`.
* `hasDerivAt_hurwitzZetaComplex_param'`: `∂ζ(s, a)/∂a = -s ζ(s+1, a)` (DLMF 25.11.17).
* `tendsto_sub_one_mul_hurwitzZetaComplex`: `(s - 1) ζ(s, a) → 1` as `s → 1`.

## Implementation notes

The project's `DLMF.Zeta.hurwitzZetaComplex s z` is defined as the limit of the
Euler–Maclaurin sequence
`E_N(s, z) = ∑_{n<N} (z+n)^{-s} + (z+N)^{1-s}/(s-1) + (z+N)^{-s}/2
  + ∑_{k<M} B_{2k+2}/(2k+2)! (s)_{2k+1} (z+N)^{-s-2k-1}`.
The limit exists for every `s ≠ 1` and every `z`, and is the same for every admissible number
`M` of correction terms (`Re s > -2M`). The engine is the one-interval Euler–Maclaurin identity
for `t ↦ (w+t)^{-s}` on `[0, 1]` (`cpow_add_eulerMaclaurinTail_sub_eq_integral`), which gives
`E_{N+1} - E_N = O(N^{-Re s - 2M - 1})` locally uniformly in `(s, z)`.

The general parts, and the definition of `DLMF.Zeta.hurwitzZetaComplex` itself, live in
`DLMF.Zeta.Basic.Hurwitz`; this file restates some of them in primed form and derives
the consequences above.
-/

@[expose] public section

open Complex Filter Set MeasureTheory intervalIntegral
open scoped Nat Real Topology

noncomputable section

namespace DLMF.Zeta

open DLMF.Hypergeometric (poch poch_succ poch_zero)

/-- The project's `hurwitzZetaComplex` is the Euler–Maclaurin limit for any admissible `M`. -/
private lemma hurwitzZetaComplex_eq_limUnder_eulerMaclaurinSeq' {M : ℕ} {s z : ℂ} (hs : s ≠ 1)
    (hM : 0 < s.re + 2 * M) :
    DLMF.Zeta.hurwitzZetaComplex s z = limUnder atTop (eulerMaclaurinSeq M s z) :=
  hurwitzZetaComplex_eq_limUnder_eulerMaclaurinSeq hs hM

/-- **Uniform convergence to `hurwitzZetaComplex`** on bounded sets with `Re s ≥ σ > -2M`,
`s ≠ 1`. -/
private lemma tendstoUniformlyOn_eulerMaclaurinSeq_hurwitzZetaComplex' {M : ℕ} {K : Set (ℂ × ℂ)}
    {R σ : ℝ} (hR : 0 ≤ R)
    (hσ : 0 < σ + 2 * M) (hK : ∀ q ∈ K, ‖q.1‖ ≤ R ∧ ‖q.2‖ ≤ R ∧ σ ≤ q.1.re ∧ q.1 ≠ 1) :
    TendstoUniformlyOn (fun N (q : ℂ × ℂ) => eulerMaclaurinSeq M q.1 q.2 (⌈R⌉₊ + 1 + N))
      (fun q => DLMF.Zeta.hurwitzZetaComplex q.1 q.2) atTop K :=
  tendstoUniformlyOn_eulerMaclaurinSeq_hurwitzZetaComplex hR hσ hK

/-- **Holomorphy of `ζ(s, z)` in `s ≠ 1`** for `z ≠ 0, -1, -2, …`. -/
theorem differentiableAt_hurwitzZetaComplex_of_add_natCast_ne_zero' {s₀ z : ℂ} (hs₀ : s₀ ≠ 1)
    (hz : ∀ n : ℕ, z + n ≠ 0) :
    DifferentiableAt ℂ (fun s => DLMF.Zeta.hurwitzZetaComplex s z) s₀ :=
  differentiableAt_hurwitzZetaComplex_of_add_ne_zero hs₀ hz

/-- At `w`, the function `(fun x => (x + n) ^ c)` has derivative `(c * (w + n) ^ (c - 1))`. -/
private lemma hasDerivAt_add_cpow {w c : ℂ} (n : ℂ) (h : w + n ∈ slitPlane) :
    HasDerivAt (fun x => (x + n) ^ c) (c * (w + n) ^ (c - 1)) w := by
  simpa using ((hasDerivAt_id w).add_const n).cpow_const (c := c) h

/-- Identity under the stated parameter and domain assumptions:
`eulerMaclaurinCoeff s k * (-s - (2 * k + 1)) = -s * eulerMaclaurinCoeff (s + 1) k`. -/
private lemma eulerMaclaurinCoeff_mul_eq (s : ℂ) (k : ℕ) :
    eulerMaclaurinCoeff s k * (-s - (2 * k + 1)) = -s * eulerMaclaurinCoeff (s + 1) k := by
  have h : poch s (2 * k + 1 + 1) = s * poch (s + 1) (2 * k + 1) := by
    simp [poch, ascPochhammer_succ_left, Polynomial.eval_comp]
  rw [poch_succ] at h
  simp only [eulerMaclaurinCoeff]
  push_cast at h ⊢
  linear_combination (-(bernoulli (2 * k + 2) : ℂ) / ((2 * k + 2)! : ℂ)) * h

/-- The `z`-derivative of the Euler–Maclaurin sequence: `∂_z E_N(s, z) = -s E_N(s+1, z)`. -/
private lemma hasDerivAt_eulerMaclaurinSeq_param (M : ℕ) {s w : ℂ} (hs : s ≠ 0) (hs1' : s ≠ 1)
    (hw : 0 < w.re)
    (N : ℕ) :
    HasDerivAt (fun x => eulerMaclaurinSeq M s x N) (-s * eulerMaclaurinSeq M (s + 1) w N) w := by
  have hsl : ∀ n : ℕ, w + n ∈ slitPlane := fun n =>
    Complex.mem_slitPlane_iff.mpr (Or.inl (by simp; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]))
  have h1 := HasDerivAt.fun_sum (u := Finset.range N)
    (fun n _ => hasDerivAt_add_cpow (c := -s) (n : ℂ) (hsl n))
  have h2 := (hasDerivAt_add_cpow (c := 1 - s) (N : ℂ) (hsl N)).div_const (s - 1)
  have h3 := (hasDerivAt_add_cpow (c := -s) (N : ℂ) (hsl N)).div_const 2
  have h4 := HasDerivAt.fun_sum (u := Finset.range M)
    (fun k _ => (hasDerivAt_add_cpow (c := -s - (2 * k + 1)) (N : ℂ) (hsl N)).const_mul
      (eulerMaclaurinCoeff s k))
  have := h1.add ((h2.add h3).add h4)
  unfold eulerMaclaurinSeq eulerMaclaurinTail
  convert this using 1
  have hs1 : (s + 1 - 1) = s := by ring
  rw [hs1, show 1 - (s + 1) = -s by ring]
  simp only [mul_add, Finset.mul_sum]
  have hs2 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1'
  congr 1
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [show -(s + 1) = -s - 1 by ring]
  congr 1
  · rw [show -(s + 1) = -s - 1 by ring, show 1 - s - 1 = -s by ring]
    field_simp
    ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [show -(s + 1) - (2 * (k : ℂ) + 1) = -s - (2 * k + 1) - 1 by ring,
      ← mul_assoc (eulerMaclaurinCoeff s k), eulerMaclaurinCoeff_mul_eq]
    ring

/-- Each term of the Euler–Maclaurin sequence is holomorphic in `z` on `Re z > 0`. -/
private lemma differentiableAt_eulerMaclaurinSeq_param (M : ℕ) (s : ℂ) {w : ℂ}
    (hw : 0 < w.re) (N : ℕ) :
    DifferentiableAt ℂ (fun x => eulerMaclaurinSeq M s x N) w := by
  have hsl : ∀ n : ℕ, w + n ∈ slitPlane := fun n =>
    Complex.mem_slitPlane_iff.mpr (Or.inl (by simp; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]))
  unfold eulerMaclaurinSeq eulerMaclaurinTail
  refine DifferentiableAt.add (DifferentiableAt.fun_sum fun n _ =>
    (hasDerivAt_add_cpow (n : ℂ) (hsl n)).differentiableAt) ?_
  refine DifferentiableAt.add (DifferentiableAt.add ?_ ?_) (DifferentiableAt.fun_sum fun k _ => ?_)
  · exact (hasDerivAt_add_cpow (N : ℂ) (hsl N)).differentiableAt.div_const _
  · exact (hasDerivAt_add_cpow (N : ℂ) (hsl N)).differentiableAt.div_const _
  · exact (hasDerivAt_add_cpow (N : ℂ) (hsl N)).differentiableAt.const_mul _

/-- Uniform convergence in `z` on a closed disk inside `Re z > 0`, for fixed `s ≠ 1`. -/
private lemma tendstoUniformlyOn_eulerMaclaurinSeq_param {s : ℂ} (a₀ : ℂ) (hs : s ≠ 1) :
    TendstoUniformlyOn (fun N (a : ℂ) => eulerMaclaurinSeq (⌈|s.re|⌉₊ + 1) s a
        (⌈max (‖s‖ + 1) (‖a₀‖ + a₀.re / 2)⌉₊ + 1 + N))
      (DLMF.Zeta.hurwitzZetaComplex s) atTop (Metric.closedBall a₀ (a₀.re / 2)) := by
  set r := a₀.re / 2
  set R : ℝ := max (‖s‖ + 1) (‖a₀‖ + r)
  have hR : 0 ≤ R := le_max_of_le_left (by positivity)
  have hσ : 0 < s.re + 2 * ((⌈|s.re|⌉₊ + 1 : ℕ) : ℝ) := by
    have := Nat.le_ceil |s.re|
    have := neg_abs_le s.re
    push_cast; linarith
  have hK : ∀ q ∈ (({s} : Set ℂ) ×ˢ Metric.closedBall a₀ r), ‖q.1‖ ≤ R ∧ ‖q.2‖ ≤ R ∧
      s.re ≤ q.1.re ∧ q.1 ≠ 1 := by
    rintro ⟨t, a⟩ ⟨ht, ha⟩
    simp only [Set.mem_singleton_iff] at ht
    subst ht
    rw [Metric.mem_closedBall, dist_eq_norm] at ha
    refine ⟨by simp only [R]; exact le_max_of_le_left (by linarith), ?_, le_rfl, hs⟩
    calc ‖a‖ = ‖(a - a₀) + a₀‖ := by ring_nf
      _ ≤ ‖a - a₀‖ + ‖a₀‖ := norm_add_le _ _
      _ ≤ R := by simp only [R]; exact le_max_of_le_right (by linarith)
  have hU := (tendstoUniformlyOn_eulerMaclaurinSeq_hurwitzZetaComplex' hR hσ hK).comp
      (fun a : ℂ => (s, a))
  have hpre : (fun a : ℂ => (s, a)) ⁻¹' (({s} : Set ℂ) ×ˢ Metric.closedBall a₀ r) =
      Metric.closedBall a₀ r := by
    ext a; simp
  rw [hpre] at hU
  exact hU

/-- Estimate under the stated parameter and domain assumptions: `0 < a.re`. -/
private lemma re_pos_of_mem_ball_half_re {a₀ a : ℂ} (ha₀ : 0 < a₀.re)
    (ha : a ∈ Metric.ball a₀ (a₀.re / 2)) :
    0 < a.re := by
  rw [Metric.mem_ball, dist_eq_norm] at ha
  have := abs_re_le_norm (a - a₀)
  simp only [sub_re] at this
  linarith [neg_abs_le (a.re - a₀.re)]

/-- **Holomorphy of `ζ(s, a)` in `a`** on `Re a > 0`, for fixed `s ≠ 1`. -/
theorem differentiableOn_hurwitzZetaComplex_param' {s : ℂ} (hs : s ≠ 1) :
    DifferentiableOn ℂ (DLMF.Zeta.hurwitzZetaComplex s) {a | 0 < a.re} := by
  intro a₀ ha₀
  have ha₀' : 0 < a₀.re := ha₀
  have hr : 0 < a₀.re / 2 := by linarith
  have hU := ((tendstoUniformlyOn_eulerMaclaurinSeq_param a₀ hs).mono
    Metric.ball_subset_closedBall).tendstoLocallyUniformlyOn
  have hdiff := hU.differentiableOn (Eventually.of_forall fun N a ha =>
    (differentiableAt_eulerMaclaurinSeq_param _ s (re_pos_of_mem_ball_half_re ha₀' ha)
        _).differentiableWithinAt)
    Metric.isOpen_ball
  exact (hdiff.differentiableAt (Metric.ball_mem_nhds _ hr)).differentiableWithinAt

/-- **`∂ζ(s, a)/∂a = -s ζ(s+1, a)`** (DLMF 25.11.17) for `s ≠ 0, 1`, `Re a > 0`. -/
theorem hasDerivAt_hurwitzZetaComplex_param' {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) {a₀ : ℂ}
    (ha₀ : 0 < a₀.re) :
    HasDerivAt (DLMF.Zeta.hurwitzZetaComplex s)
      (-s * DLMF.Zeta.hurwitzZetaComplex (s + 1) a₀) a₀ := by
  have hr : 0 < a₀.re / 2 := by linarith
  have hU := ((tendstoUniformlyOn_eulerMaclaurinSeq_param a₀ hs1).mono
    Metric.ball_subset_closedBall).tendstoLocallyUniformlyOn
  have hF : ∀ᶠ N in atTop, DifferentiableOn ℂ (fun a => eulerMaclaurinSeq (⌈|s.re|⌉₊ + 1) s a
      (⌈max (‖s‖ + 1) (‖a₀‖ + a₀.re / 2)⌉₊ + 1 + N)) (Metric.ball a₀ (a₀.re / 2)) :=
    Eventually.of_forall fun N a ha =>
      (differentiableAt_eulerMaclaurinSeq_param _ s (re_pos_of_mem_ball_half_re ha₀ ha)
          _).differentiableWithinAt
  have hdiff := hU.differentiableOn hF Metric.isOpen_ball
  have hD := (hU.deriv hF Metric.isOpen_ball).tendsto_at (Metric.mem_ball_self hr)
  have hD' : Tendsto (fun N => -s * eulerMaclaurinSeq (⌈|s.re|⌉₊ + 1) (s + 1) a₀
      (⌈max (‖s‖ + 1) (‖a₀‖ + a₀.re / 2)⌉₊ + 1 + N)) atTop
      (𝓝 (-s * DLMF.Zeta.hurwitzZetaComplex (s + 1) a₀)) := by
    have hs1' : s + 1 ≠ 1 := by intro h; exact hs0 (by linear_combination h)
    have hM : 0 < (s + 1).re + 2 * ((⌈|s.re|⌉₊ + 1 : ℕ) : ℝ) := by
      have := Nat.le_ceil |s.re|
      have := neg_abs_le s.re
      simp; linarith
    have hT : Tendsto (fun N : ℕ => ⌈max (‖s‖ + 1) (‖a₀‖ + a₀.re / 2)⌉₊ + 1 + N) atTop atTop :=
      tendsto_atTop_mono (fun N => Nat.le_add_left N _) tendsto_id
    exact ((tendsto_eulerMaclaurinSeq_hurwitzZetaComplex (z := a₀) hs1' hM).comp hT).const_mul (-s)
  have heq : (fun N => (deriv ∘ fun N a => eulerMaclaurinSeq (⌈|s.re|⌉₊ + 1) s a
      (⌈max (‖s‖ + 1) (‖a₀‖ + a₀.re / 2)⌉₊ + 1 + N)) N a₀) =
      fun N => -s * eulerMaclaurinSeq (⌈|s.re|⌉₊ + 1) (s + 1) a₀
        (⌈max (‖s‖ + 1) (‖a₀‖ + a₀.re / 2)⌉₊ + 1 + N) := by
    funext N
    exact (hasDerivAt_eulerMaclaurinSeq_param _ hs0 hs1 ha₀ _).deriv
  have hval : deriv (DLMF.Zeta.hurwitzZetaComplex s) a₀ =
      -s * DLMF.Zeta.hurwitzZetaComplex (s + 1) a₀ := by
    refine tendsto_nhds_unique ?_ hD'
    rw [← heq]
    exact hD
  rw [← hval]
  exact (hdiff.differentiableAt (Metric.ball_mem_nhds _ hr)).hasDerivAt

/-- `(s - 1) E_N(s, a)`, written without division so that it is entire in `s`. -/
def subOneMulEulerMaclaurinSeq (M : ℕ) (s a : ℂ) (N : ℕ) : ℂ :=
  (s - 1) * ((∑ n ∈ Finset.range N, (a + n) ^ (-s)) + (a + N) ^ (-s) / 2 +
    ∑ k ∈ Finset.range M, eulerMaclaurinCoeff s k * (a + N) ^ (-s - (2 * k + 1))) +
        (a + N) ^ (1 - s)

/-- Identity under the stated parameter and domain assumptions:
`subOneMulEulerMaclaurinSeq M s a N = (s - 1) * eulerMaclaurinSeq M s a N`. -/
private lemma subOneMulEulerMaclaurinSeq_eq {M : ℕ} {s : ℂ} (hs : s ≠ 1) (a : ℂ) (N : ℕ) :
    subOneMulEulerMaclaurinSeq M s a N = (s - 1) * eulerMaclaurinSeq M s a N := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  unfold subOneMulEulerMaclaurinSeq eulerMaclaurinSeq eulerMaclaurinTail
  field_simp
  ring

/-- Formula under the stated hypotheses:
`subOneMulEulerMaclaurinSeq M s a (N₀ + N) = subOneMulEulerMaclaurinSeq M s a N₀ + ∑ n ∈
Finset.range N, (s - 1) * eulerMaclaurinIncrement M s (a + (N₀ + n : ℕ))`. -/
private lemma subOneMulEulerMaclaurinSeq_add (M : ℕ) (s a : ℂ) (N₀ N : ℕ) :
    subOneMulEulerMaclaurinSeq M s a (N₀ + N) =
      subOneMulEulerMaclaurinSeq M s a N₀ + ∑ n ∈ Finset.range N, (s - 1) *
          eulerMaclaurinIncrement M s (a + (N₀ + n : ℕ)) := by
  rcases eq_or_ne s 1 with rfl | hs
  · simp [subOneMulEulerMaclaurinSeq]
  · rw [subOneMulEulerMaclaurinSeq_eq hs, subOneMulEulerMaclaurinSeq_eq hs, eulerMaclaurinSeq_add,
        mul_add, Finset.mul_sum]

/-- Continuity of the indicated function: `Continuous fun s => subOneMulEulerMaclaurinSeq M s a N`.
-/
private lemma continuous_subOneMulEulerMaclaurinSeq (M : ℕ) {a : ℂ}
    (ha : ∀ n : ℕ, a + n ≠ 0) (N : ℕ) :
    Continuous fun s => subOneMulEulerMaclaurinSeq M s a N := by
  refine continuous_iff_continuousAt.mpr fun s => DifferentiableAt.continuousAt (𝕜 := ℂ) ?_
  unfold subOneMulEulerMaclaurinSeq eulerMaclaurinCoeff
  refine DifferentiableAt.add (DifferentiableAt.mul
    ((differentiableAt_id (x := s)).sub_const (1 : ℂ)) ?_) ?_
  · refine DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.fun_sum fun n _ =>
      (differentiableAt_id.neg).const_cpow (Or.inl (ha n))) ?_)
      (DifferentiableAt.fun_sum fun k _ => ?_)
    · exact (differentiableAt_id.neg.const_cpow (Or.inl (ha N))).div_const _
    · exact ((differentiableAt_poch _ s).const_mul _).mul
        ((differentiableAt_id.neg.sub (differentiableAt_const _)).const_cpow (Or.inl (ha N)))
  · exact ((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl (ha N))

/-- **The pole at `s = 1`**: `(s - 1) ζ(s, a) → 1` as `s → 1`, for `a ≠ 0, -1, -2, …`. -/
theorem tendsto_sub_one_mul_hurwitzZetaComplex {a : ℂ} (ha : ∀ n : ℕ, a + n ≠ 0) :
    Tendsto (fun s => (s - 1) * DLMF.Zeta.hurwitzZetaComplex s a) (𝓝[≠] 1) (𝓝 1) := by
  set B := Metric.closedBall (1 : ℂ) (1 / 2)
  set R : ℝ := max 2 ‖a‖
  have hR : 0 ≤ R := le_max_of_le_left (by norm_num)
  set K : Set (ℂ × ℂ) := {q | q.1 ∈ B ∧ q.1 ≠ 1 ∧ q.2 = a}
  have hB : ∀ s ∈ B, ‖s‖ ≤ 2 ∧ 1 / 2 ≤ s.re ∧ ‖s - 1‖ ≤ 1 / 2 := by
    intro s hs
    rw [Metric.mem_closedBall, dist_eq_norm] at hs
    refine ⟨?_, ?_, hs⟩
    · calc ‖s‖ = ‖(s - 1) + 1‖ := by ring_nf
        _ ≤ ‖s - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ ≤ 2 := by simp; linarith
    · have := abs_re_le_norm (s - 1)
      simp only [sub_re, one_re] at this
      linarith [neg_abs_le (s.re - 1)]
  have hK : ∀ q ∈ K, ‖q.1‖ ≤ R ∧ ‖q.2‖ ≤ R ∧ (1 / 2 : ℝ) ≤ q.1.re ∧ q.1 ≠ 1 := by
    rintro ⟨s, w⟩ ⟨hs, hs1, rfl⟩
    exact ⟨(hB s hs).1.trans (le_max_left _ _), le_max_right _ _, (hB s hs).2.1, hs1⟩
  obtain ⟨u, hu, hu0, hb⟩ :=
      exists_summable_bound_eulerMaclaurinIncrement (M := 0) hR (by norm_num) hK
  set N₀ := ⌈R⌉₊ + 1
  have hbound : ∀ n : ℕ, ∀ s ∈ B, ‖(s - 1) *
      eulerMaclaurinIncrement 0 s (a + (N₀ + n : ℕ))‖ ≤ u n := by
    intro n s hs
    rcases eq_or_ne s 1 with rfl | hs1
    · simpa using hu0 n
    · rw [norm_mul]
      have := hb n (s, a) ⟨hs, hs1, rfl⟩
      have h2 := (hB s hs).2.2
      calc ‖s - 1‖ * ‖eulerMaclaurinIncrement 0 s (a + (N₀ + n : ℕ))‖ ≤ 1 * u n :=
            mul_le_mul (by linarith) this (norm_nonneg _) zero_le_one
        _ = u n := one_mul _
  have hT := tendstoUniformlyOn_tsum_nat hu hbound
  set H : ℂ → ℂ := fun s => subOneMulEulerMaclaurinSeq 0 s a N₀ +
    ∑' n : ℕ, (s - 1) * eulerMaclaurinIncrement 0 s (a + (N₀ + n : ℕ))
  have hU : TendstoUniformlyOn (fun N s => subOneMulEulerMaclaurinSeq 0 s a (N₀ + N))
      H atTop B := by
    rw [Metric.tendstoUniformlyOn_iff] at hT ⊢
    intro ε hε
    filter_upwards [hT ε hε] with N hN s hs
    rw [subOneMulEulerMaclaurinSeq_add 0 s a N₀ N, dist_add_left]
    exact hN s hs
  have hHc : ContinuousOn H B :=
    hU.continuousOn (Frequently.of_forall fun N =>
        (continuous_subOneMulEulerMaclaurinSeq 0 ha _).continuousOn)
  have hH1 : H 1 = 1 := by simp [H, subOneMulEulerMaclaurinSeq]
  have hHeq : ∀ s ∈ B, s ≠ 1 → (s - 1) * DLMF.Zeta.hurwitzZetaComplex s a = H s := by
    intro s hs hs1
    have hT1 := hU.tendsto_at hs
    have hM : 0 < s.re + 2 * ((0 : ℕ) : ℝ) := by simp; linarith [(hB s hs).2.1]
    have hT0 : Tendsto (fun N : ℕ => N₀ + N) atTop atTop :=
      tendsto_atTop_mono (fun N => Nat.le_add_left N _) tendsto_id
    have hT2 := (((tendsto_eulerMaclaurinSeq_hurwitzZetaComplex (z := a) hs1 hM).comp
        hT0).const_mul (s - 1))
    refine tendsto_nhds_unique hT2 ?_
    refine hT1.congr fun N => ?_
    simp only [Function.comp_apply]
    rw [subOneMulEulerMaclaurinSeq_eq hs1]
  have hBn : B ∈ 𝓝 (1 : ℂ) := Metric.closedBall_mem_nhds _ (by norm_num)
  have hcont : Tendsto H (𝓝 1) (𝓝 1) := by
    have := (hHc.continuousAt hBn).tendsto
    rwa [hH1] at this
  refine (hcont.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [nhdsWithin_le_nhds hBn, self_mem_nhdsWithin] with s hs hs1
  exact (hHeq s hs hs1).symm

end DLMF.Zeta

end
