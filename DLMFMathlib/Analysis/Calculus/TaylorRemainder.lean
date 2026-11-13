/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Norm estimates for multivariable Taylor remainders

For a `C^(n+1)` map between real normed spaces with complete target, the order-`n`
Taylor remainder is `O(‖h‖^(n+1))` and hence `o(‖h‖^n)` at its center.

The proof applies Mathlib's `map_add_eq_sum_add_integral_iteratedFDeriv` on short line
segments. Continuity bounds the next derivative uniformly near the center, and the
operator norm bounds the integral remainder. No finite-dimensional assumption is needed.

## Main results

* `ContDiffAt.isBigO_sub_sum_iteratedFDeriv`: bound the next-order remainder.
* `ContDiffAt.isLittleO_sub_sum_iteratedFDeriv`: the resulting Peano estimate.
-/

public noncomputable section

open Filter Asymptotics Set MeasureTheory
open scoped Topology

namespace ContDiffAt
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
/-- A `C^(n+1)` map has Taylor remainder `O(‖h‖^(n+1))` at its center. -/
theorem isBigO_sub_sum_iteratedFDeriv {f : E → F} {p : E} (n : ℕ)
    (hf : ContDiffAt ℝ (n + 1) f p) :
    (fun h : E => f (p + h) - ∑ k ∈ Finset.range (n + 1),
      (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f p (fun _ => h)) =O[𝓝 0]
        (fun h : E => ‖h‖ ^ (n + 1)) := by
  let K := ‖iteratedFDeriv ℝ (n + 1) f p‖ + 1
  have hb : ∀ᶠ z in 𝓝 p, ‖iteratedFDeriv ℝ (n + 1) f z‖ < K :=
    (hf.continuousAt_iteratedFDeriv (k := n + 1) (by norm_cast)).norm.eventually
      (gt_mem_nhds (by dsimp only [K]; linarith))
  obtain ⟨δ, hδ, hδprop⟩ := Metric.eventually_nhds_iff.mp
    ((hf.eventually (by simp)).and hb)
  refine IsBigO.of_bound (‖((n.factorial : ℝ)⁻¹)‖ * K) ?_
  filter_upwards [Metric.ball_mem_nhds (0 : E) hδ] with h hh
  have hh' : ‖h‖ < δ := by simpa only [Metric.mem_ball, dist_zero_right] using hh
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℝ (n + 1) f (p + t • h) ∧ ‖iteratedFDeriv ℝ (n + 1) f (p + t • h)‖ < K := by
    apply hδprop
    calc
      dist (p + t • h) p = ‖t • h‖ := by rw [dist_eq_norm, add_sub_cancel_left]
      _ = |t| * ‖h‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖h‖ :=
        mul_le_of_le_one_left (norm_nonneg _) (by simpa only [abs_of_nonneg ht.1] using ht.2)
      _ < δ := hh'
  have hformula := map_add_eq_sum_add_integral_iteratedFDeriv
    (n := n) (fun t ht => (hseg t ht).1)
  have hint : ‖∫ t in (0 : ℝ)..1, (1 - t) ^ n •
      iteratedFDeriv ℝ (n + 1) f (p + t • h) (fun _ => h)‖ ≤ K * ‖h‖ ^ (n + 1) := by
    calc
      _ ≤ (K * ‖h‖ ^ (n + 1)) * |(1 : ℝ) - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro t ht
        rw [uIoc_of_le zero_le_one] at ht
        have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
        have hpow : |(1 - t) ^ n| ≤ 1 := by
          rw [abs_pow, abs_of_nonneg (by linarith [ht'.2])]
          exact pow_le_one₀ (by linarith [ht'.2]) (by linarith [ht'.1])
        have hD : ‖iteratedFDeriv ℝ (n + 1) f (p + t • h) (fun _ => h)‖ ≤
            K * ‖h‖ ^ (n + 1) := by
          calc
            _ ≤ ‖iteratedFDeriv ℝ (n + 1) f (p + t • h)‖ * ‖h‖ ^ (n + 1) := by
              simpa using (iteratedFDeriv ℝ (n + 1) f (p + t • h)).le_opNorm (fun _ => h)
            _ ≤ _ := mul_le_mul_of_nonneg_right (hseg t ht').2.le (by positivity)
        rw [norm_smul, Real.norm_eq_abs]
        calc
          _ ≤ 1 * (K * ‖h‖ ^ (n + 1)) := mul_le_mul hpow hD (norm_nonneg _) zero_le_one
          _ = _ := one_mul _
      _ = _ := by norm_num
  rw [hformula, add_sub_cancel_left, norm_smul]
  simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg h) _)]
  calc
    _ ≤ |(n.factorial : ℝ)⁻¹| * (K * ‖h‖ ^ (n + 1)) :=
      mul_le_mul_of_nonneg_left hint (abs_nonneg _)
    _ = _ := by ring
/-- A `C^(n+1)` map has Taylor remainder `o(‖h‖^n)` at its center. -/
theorem isLittleO_sub_sum_iteratedFDeriv {f : E → F} {p : E} (n : ℕ)
    (hf : ContDiffAt ℝ (n + 1) f p) :
    (fun h : E => f (p + h) - ∑ k ∈ Finset.range (n + 1),
      (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f p (fun _ => h)) =o[𝓝 0]
        (fun h : E => ‖h‖ ^ n) :=
  (hf.isBigO_sub_sum_iteratedFDeriv n).trans_isLittleO
    (isLittleO_norm_pow_norm_pow n.lt_succ_self)
end ContDiffAt
