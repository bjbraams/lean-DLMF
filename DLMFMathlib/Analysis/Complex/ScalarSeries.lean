/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Positivity.Finset

/-!
# Uniqueness and multiplication of scalar power series

Shared helpers formerly proved independently in the hypergeometric and orthogonal-polynomial
libraries. The proofs use Mathlib's uniqueness of formal multilinear series and its absolutely
summable Cauchy product. They do not depend on any special-function definitions.
-/

@[expose] public noncomputable section
open Filter
open scoped Nat Topology
namespace Complex

/-- Recover a scalar power series from its sums on the unit disk. -/
theorem powerSeries_coefficients_unique {c d : ℕ → ℂ} {f : ℂ → ℂ}
    (hc : ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun n => c n * z ^ n) (f z))
    (hd : ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun n => d n * z ^ n) (f z)) : c = d := by
  have series {e : ℕ → ℂ}
      (he : ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun n => e n * z ^ n) (f z)) :
      HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ e) 0
        ((1 / 2 : NNReal) : ENNReal) := by
    refine ⟨?_, by norm_num, ?_⟩
    · apply FormalMultilinearSeries.le_radius_of_summable_norm
      simpa [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow] using
        (he (1 / 2) (by norm_num)).summable.norm
    · intro z hz
      have hzNN : ‖z‖₊ < (1 / 2 : NNReal) := by
        simpa only [Metric.mem_eball, edist_zero_right, enorm_lt_coe] using hz
      have hz' : ‖z‖ < (1 / 2 : ℝ) := by exact_mod_cast hzNN
      simpa [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using
        he z (by linarith)
  exact FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ
    ((series hc).hasFPowerSeriesAt.eq_formalMultilinearSeries (series hd).hasFPowerSeriesAt)

/-- Cauchy product of scalar series, written as a coefficient convolution. -/
theorem hasSum_powerSeries_convolution {c d : ℕ → ℂ} {z u v : ℂ}
    (hc : HasSum (fun n => c n * z ^ n) u)
    (hd : HasSum (fun n => d n * z ^ n) v) :
    HasSum (fun n => (∑ k ∈ Finset.range (n + 1), c k * d (n - k)) * z ^ n) (u * v) := by
  have h := hasSum_sum_range_mul_of_summable_norm hc.summable.norm hd.summable.norm
  rw [hc.tsum_eq, hd.tsum_eq] at h
  refine h.congr_fun fun n => ?_
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by simpa using Finset.mem_range.mp hk
  have hp : z ^ n = z ^ k * z ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hk']
  rw [hp]
  ring

end Complex
