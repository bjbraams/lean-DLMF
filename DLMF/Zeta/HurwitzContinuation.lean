/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Basic.HurwitzProperties
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
`DLMF.Zeta.Basic.Hurwitz` and `DLMF.Zeta.Basic.HurwitzProperties`; this file derives
the pole behaviour from those foundational results.
-/

@[expose] public section

open Complex Filter Set MeasureTheory intervalIntegral
open scoped Nat Real Topology

noncomputable section

namespace DLMF.Zeta

open DLMF.Hypergeometric (pochhammer pochhammer_succ pochhammer_zero)

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
    · exact ((differentiableAt_pochhammer _ s).const_mul _).mul
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
