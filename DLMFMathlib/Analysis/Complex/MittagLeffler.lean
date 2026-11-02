/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Mittag-Leffler series with simple poles

Let `zₙ` be distinct nonzero points with `|zₙ| → ∞` and let `aₙ` be complex numbers with
`∑ |aₙ / zₙ²| < ∞`. Then the Mittag-Leffler series
`f(z) = ∑ₙ aₙ (1 / (z - zₙ) + 1 / zₙ)`
converges, is holomorphic off the points `zₙ`, and has a simple pole with principal part
`aₙ / (z - zₙ)` at each `zₙ`.

## Main results

* `Complex.differentiableOn_tsum_mittagLeffler`: `f` is holomorphic on the complement of
  `{zₙ}`.
* `Complex.exists_analyticAt_tsum_mittagLeffler_eq`: near `zₙ`, `f(z) = aₙ / (z - zₙ) + g(z)` with
  `g` analytic at `zₙ`.

## Implementation notes

On a disc `|z| < R` only the finitely many indices with `|zₙ| < 2R` can produce poles; the
remaining terms satisfy `|aₙ (1 / (z - zₙ) + 1 / zₙ)| ≤ 2R |aₙ / zₙ²|`, so their sum is
holomorphic on the disc by the Weierstrass M-test (`differentiableOn_tsum_of_summable_norm`).
-/

@[expose] public noncomputable section

open Filter Set Metric
open scoped Topology

namespace Complex

variable {a zs : ℕ → ℂ}

/-- On the disc `|z| < R`, the Mittag-Leffler series is a finite sum of its terms plus a
function holomorphic on the disc. -/
private theorem exists_mittagLeffler_split (hz : ∀ n, zs n ≠ 0)
    (hlim : Tendsto (fun n => ‖zs n‖) atTop atTop) (hs : Summable (fun n => ‖a n / zs n ^ 2‖))
    {R : ℝ} (hR : 0 < R) :
    ∃ N : ℕ, (∀ k, N ≤ k → 2 * R ≤ ‖zs k‖) ∧ ∃ T : ℂ → ℂ, DifferentiableOn ℂ T (ball 0 R) ∧
      ∀ z ∈ ball (0 : ℂ) R, ∑' k, a k * (1 / (z - zs k) + 1 / zs k) =
        ∑ k ∈ Finset.range N, a k * (1 / (z - zs k) + 1 / zs k) + T z := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually_ge_atTop (2 * R))
  refine ⟨N, hN, ?_⟩
  set t : ℕ → ℂ → ℂ := fun k z => a k * (1 / (z - zs k) + 1 / zs k) with htdef
  set F : ℕ → ℂ → ℂ := fun k z => if k < N then 0 else t k z with hFdef
  have hne : ∀ k, N ≤ k → ∀ z ∈ ball (0 : ℂ) R, z - zs k ≠ 0 := by
    intro k hk z hzR h
    have hzR' : ‖z‖ < R := by simpa using hzR
    rw [sub_eq_zero] at h
    have := hN k hk
    rw [← h] at this
    linarith
  have hbound : ∀ k, ∀ z ∈ ball (0 : ℂ) R, ‖F k z‖ ≤ 2 * R * ‖a k / zs k ^ 2‖ := by
    intro k z hzR
    by_cases hk : k < N
    · simp only [hFdef, hk, ite_true, norm_zero]; positivity
    · push Not at hk
      simp only [hFdef, show ¬ k < N by omega, ite_false, htdef]
      have hzR' : ‖z‖ < R := by simpa using hzR
      have hw := hN k hk
      have hzk := hne k hk z hzR
      have heq : a k * (1 / (z - zs k) + 1 / zs k) = a k / zs k ^ 2 * (z * zs k / (z - zs k)) := by
        field_simp [hz k, hzk]
        ring
      rw [heq, norm_mul]
      refine mul_comm (2 * R) _ ▸ mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have hdist : ‖zs k‖ / 2 ≤ ‖z - zs k‖ := by
        have := norm_sub_norm_le (zs k) z
        rw [norm_sub_rev] at this
        linarith
      have hwpos : 0 < ‖zs k‖ := norm_pos_iff.2 (hz k)
      rw [norm_div, norm_mul, div_le_iff₀ (norm_pos_iff.2 hzk)]
      calc ‖z‖ * ‖zs k‖ ≤ R * ‖zs k‖ := by gcongr
        _ = 2 * R * (‖zs k‖ / 2) := by ring
        _ ≤ 2 * R * ‖z - zs k‖ := by gcongr
  have hFd : ∀ k, DifferentiableOn ℂ (F k) (ball 0 R) := by
    intro k
    by_cases hk : k < N
    · simp only [hFdef, hk, ite_true]; exact differentiableOn_const 0
    · push Not at hk
      simp only [hFdef, show ¬ k < N by omega, ite_false, htdef]
      intro z hzR
      have h1 : DifferentiableAt ℂ (fun y => 1 / (y - zs k)) z :=
        (differentiableAt_const _).div (differentiableAt_id.sub_const _) (hne k hk z hzR)
      exact ((h1.add_const _).const_mul _).differentiableWithinAt
  refine ⟨fun z => ∑' k, F k z, differentiableOn_tsum_of_summable_norm (hs.mul_left (2 * R))
    hFd isOpen_ball hbound, fun z hzR => ?_⟩
  have hFs : Summable fun k => F k z :=
    (hs.mul_left (2 * R)).of_norm_bounded fun k => hbound k z hzR
  have hfin : Summable fun k => if k < N then t k z else 0 :=
    summable_of_ne_finset_zero (s := Finset.range N) fun k hk => by
      simp only [Finset.mem_range] at hk; simp [hk]
  have hsplit : (fun k => t k z) = fun k => (if k < N then t k z else 0) + F k z := by
    funext k
    by_cases hk : k < N <;> simp [hFdef, hk]
  change ∑' k, t k z = _
  conv_lhs => rw [hsplit]
  rw [hfin.tsum_add hFs, tsum_eq_sum (f := fun k => if k < N then t k z else 0)
    (s := Finset.range N) (fun k hk => by
    simp only [Finset.mem_range] at hk; simp [hk])]
  congr 1
  exact Finset.sum_congr rfl fun k hk => by simp only [Finset.mem_range.1 hk, ite_true, htdef]

/-- The Mittag-Leffler series `∑ aₙ (1/(z - zₙ) + 1/zₙ)` with `zₙ ≠ 0`, `|zₙ| → ∞` and
`∑ |aₙ / zₙ²| < ∞` is holomorphic off the points `zₙ`. -/
theorem differentiableOn_tsum_mittagLeffler (hz : ∀ n, zs n ≠ 0)
    (hlim : Tendsto (fun n => ‖zs n‖) atTop atTop) (hs : Summable (fun n => ‖a n / zs n ^ 2‖)) :
    DifferentiableOn ℂ (fun z => ∑' n, a n * (1 / (z - zs n) + 1 / zs n)) (range zs)ᶜ := by
  intro z hzr
  have hR : (0 : ℝ) < ‖z‖ + 1 := by positivity
  obtain ⟨N, -, T, hT, hsplit⟩ := exists_mittagLeffler_split hz hlim hs hR
  have hzB : z ∈ ball (0 : ℂ) (‖z‖ + 1) := by simp
  have hfin : DifferentiableAt ℂ
      (fun y => ∑ k ∈ Finset.range N, a k * (1 / (y - zs k) + 1 / zs k)) z := by
    refine DifferentiableAt.fun_sum fun k _ => ?_
    have hne : z - zs k ≠ 0 := sub_ne_zero.2 fun h => hzr ⟨k, h.symm⟩
    have h1 : DifferentiableAt ℂ (fun y => 1 / (y - zs k)) z :=
      (differentiableAt_const _).div (differentiableAt_id.sub_const _) hne
    exact (h1.add_const _).const_mul _
  have hd := hfin.add (hT.differentiableAt (isOpen_ball.mem_nhds hzB))
  refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [isOpen_ball.mem_nhds hzB] with y hy using hsplit y hy

/-- Under the hypotheses of `differentiableOn_tsum_mittagLeffler`, if moreover the `zₙ` are
distinct, then near `zₙ` the Mittag-Leffler series is `aₙ / (z - zₙ) + g(z)` with `g` analytic
at `zₙ`. -/
theorem exists_analyticAt_tsum_mittagLeffler_eq (hinj : Function.Injective zs)
    (hz : ∀ n, zs n ≠ 0) (hlim : Tendsto (fun n => ‖zs n‖) atTop atTop)
    (hs : Summable (fun n => ‖a n / zs n ^ 2‖)) (n : ℕ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (zs n) ∧ ∀ᶠ z in 𝓝[≠] (zs n),
      ∑' k, a k * (1 / (z - zs k) + 1 / zs k) = a n / (z - zs n) + g z := by
  have hR : (0 : ℝ) < ‖zs n‖ + 1 := by positivity
  obtain ⟨N, hN, T, hT, hsplit⟩ := exists_mittagLeffler_split hz hlim hs hR
  have hnN : n ∈ Finset.range N := by
    rw [Finset.mem_range]
    by_contra h
    have := hN n (by omega)
    linarith [norm_nonneg (zs n)]
  have hB : zs n ∈ ball (0 : ℂ) (‖zs n‖ + 1) := by simp
  refine ⟨fun z => a n / zs n +
    ∑ k ∈ (Finset.range N).erase n, a k * (1 / (z - zs k) + 1 / zs k) + T z, ?_, ?_⟩
  · refine (analyticAt_const.add (Finset.analyticAt_fun_sum _ fun k hk => ?_)).add
      (hT.analyticAt (isOpen_ball.mem_nhds hB))
    have hne : zs n - zs k ≠ 0 := sub_ne_zero.2 fun h => (Finset.ne_of_mem_erase hk) (hinj h).symm
    have : AnalyticAt ℂ (fun z => a k * ((z - zs k)⁻¹ + (zs k)⁻¹)) (zs n) :=
      analyticAt_const.mul (((analyticAt_id.sub analyticAt_const).inv hne).add analyticAt_const)
    simpa [one_div] using this
  · filter_upwards [nhdsWithin_le_nhds (isOpen_ball.mem_nhds hB)] with z hz
    rw [hsplit z hz, ← Finset.add_sum_erase _ _ hnN]
    ring

end Complex
