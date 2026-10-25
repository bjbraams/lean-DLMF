/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Analytic.OfScalars

/-!
# Extending the disk of convergence of a scalar power series

If a power series `∑ cₙ zⁿ` sums to `f z` on a small disk and `f` is complex differentiable
on a larger disk `‖z‖ < R`, then the same series sums to `f z` on the whole larger disk.
The proof compares the coefficients with Mathlib's Cauchy–Taylor expansion
(`Complex.hasSum_taylorSeries_on_ball`) through uniqueness of formal multilinear series;
the uniqueness argument follows `DLMF.Hypergeometric.scalarSeries_unique_ball`.
A reindexing lemma handles even series `∑ aₙ z^{2n}`.
-/

@[expose] public noncomputable section
open Filter
open scoped Nat Topology
namespace Complex

/-- Coefficients of a scalar power series are determined by its sums on a small disk. -/
theorem trigR4_coeff_unique_ball {c d : ℕ → ℂ} {g : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hc : ∀ z : ℂ, ‖z‖ < ρ → HasSum (fun n => c n * z ^ n) (g z))
    (hd : ∀ z : ℂ, ‖z‖ < ρ → HasSum (fun n => d n * z ^ n) (g z)) : c = d := by
  set ρ' : NNReal := ⟨ρ / 2, by positivity⟩
  have series {e : ℕ → ℂ}
      (he : ∀ z : ℂ, ‖z‖ < ρ → HasSum (fun n => e n * z ^ n) (g z)) :
      HasFPowerSeriesOnBall g (FormalMultilinearSeries.ofScalars ℂ e) 0 (ρ' : ENNReal) := by
    refine ⟨?_, ?_, ?_⟩
    · apply FormalMultilinearSeries.le_radius_of_summable_norm
      have hz0 : ‖((ρ / 2 : ℝ) : ℂ)‖ < ρ := by
        rw [norm_real, Real.norm_of_nonneg (by positivity)]; linarith
      have := (he _ hz0).summable.norm
      simp only [norm_mul, norm_pow, norm_real, Real.norm_of_nonneg
        (by positivity : (0 : ℝ) ≤ ρ / 2)] at this
      simp only [FormalMultilinearSeries.ofScalars_norm]
      exact this
    · exact ENNReal.coe_pos.mpr (by rw [← NNReal.coe_pos]; show (0 : ℝ) < ρ / 2; positivity)
    · intro z hz
      have hzNN : ‖z‖₊ < ρ' := by
        simpa only [Metric.mem_eball, edist_zero_right, enorm_lt_coe] using hz
      have hz' : ‖z‖ < ρ / 2 := by exact_mod_cast hzNN
      simpa [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using
        he z (by linarith)
  exact FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ
    ((series hc).hasFPowerSeriesAt.eq_formalMultilinearSeries (series hd).hasFPowerSeriesAt)

/-- A power series that represents `f` near the origin represents it on every centered disk
on which `f` is complex differentiable. -/
theorem trigR4_hasSum_of_differentiableOn_ball {f : ℂ → ℂ} {c : ℕ → ℂ} {R ρ : ℝ}
    (hρ : 0 < ρ) (hf : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hc : ∀ z : ℂ, ‖z‖ < ρ → HasSum (fun n => c n * z ^ n) (f z))
    {z : ℂ} (hz : ‖z‖ < R) : HasSum (fun n => c n * z ^ n) (f z) := by
  have hT : ∀ w : ℂ, ‖w‖ < R →
      HasSum (fun n => (iteratedDeriv n f 0 / n !) * w ^ n) (f w) := by
    intro w hw
    convert Complex.hasSum_taylorSeries_on_ball hf (z := w) (by simpa using hw) using 1
    funext n
    simp only [sub_zero, smul_eq_mul]
    ring
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg z) hz
  have hcd : c = fun n => iteratedDeriv n f 0 / n ! :=
    trigR4_coeff_unique_ball (lt_min hρ hR)
      (fun w hw => hc w (lt_of_lt_of_le hw (min_le_left _ _)))
      (fun w hw => hT w (lt_of_lt_of_le hw (min_le_right _ _)))
  rw [hcd]
  exact hT z hz

/-- A series supported on even indices is a reindexed series. -/
theorem trigR4_hasSum_even_iff {a : ℕ → ℂ} {s : ℂ} :
    HasSum (fun m : ℕ => if Even m then a (m / 2) else 0) s ↔ HasSum a s := by
  have hinj : Function.Injective (fun n : ℕ => 2 * n) := fun x y h => by simpa using h
  rw [← hinj.hasSum_iff]
  · apply Iff.of_eq
    congr 1
    funext n
    simp
  · intro m hm
    have : ¬ Even m := by
      rintro ⟨k, hk⟩; exact hm ⟨k, by simp only; omega⟩
    simp [this]

/-- A series supported on odd indices is a reindexed series. -/
theorem trigR4_hasSum_odd_iff {a : ℕ → ℂ} {s : ℂ} :
    HasSum (fun m : ℕ => if Even m then 0 else a (m / 2)) s ↔ HasSum a s := by
  have hinj : Function.Injective (fun n : ℕ => 2 * n + 1) := fun x y h => by simpa using h
  rw [← hinj.hasSum_iff]
  · apply Iff.of_eq
    congr 1
    funext n
    have h1 : ¬ Even (2 * n + 1) := by simp
    have h2 : (2 * n + 1) / 2 = n := by omega
    simp [h1, h2]
  · intro m hm
    have : Even m := by
      rcases Nat.even_or_odd m with h | ⟨k, hk⟩
      · exact h
      · exact absurd ⟨k, hk.symm⟩ hm
    simp [this]

end Complex
