/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Extending the disk of convergence of a scalar power series

If a power series `∑ cₙ zⁿ` sums to `f z` on a small disk and `f` is complex differentiable
on a larger disk `‖z‖ < R`, then the same series sums to `f z` on the whole larger disk.
The proof compares the coefficients with Mathlib's Cauchy–Taylor expansion
(`Complex.hasSum_taylorSeries_on_ball`) through uniqueness of formal multilinear series;
the uniqueness argument follows `DLMF.Hypergeometric.scalarSeries_unique_ball`.
A reindexing lemma handles even series `∑ aₙ z^{2n}`.
The scalar-to-multilinear adapter and the Cauchy product lemma also support algebraic
operations on convergent power series; these specialize Mathlib’s analytic and sum APIs.
-/

@[expose] public noncomputable section
open Filter
open scoped Nat Topology
namespace Complex

/-- A scalar power series represents its sum analytically on every strictly smaller disk. -/
theorem hasFPowerSeriesOnBall_of_hasSum_ball {a : ℕ → ℂ} {f : ℂ → ℂ} {R : ℝ}
    {ρ : NNReal} (hρ : 0 < ρ) (hρR : (ρ : ℝ) < R)
    (hf : ∀ z : ℂ, ‖z‖ < R → HasSum (fun n => a n * z ^ n) (f z)) :
    HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ a) 0
      (ρ : ENNReal) := by
  refine ⟨?_, by exact_mod_cast hρ, ?_⟩
  · apply FormalMultilinearSeries.le_radius_of_summable_norm
    have h := (hf ((ρ : ℝ) : ℂ) (by simpa [Real.norm_of_nonneg ρ.coe_nonneg] using hρR)).summable.norm
    simpa [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_of_nonneg ρ.coe_nonneg] using h
  · intro w hw
    have hw' : ‖w‖ < (ρ : ℝ) := by
      simpa [Metric.eball_coe, dist_eq_norm] using hw
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using
      hf w (hw'.trans hρR)

/-- Multiply two convergent complex power series by convolution of their coefficients. -/
theorem hasSum_mul_powerSeries {a b : ℕ → ℂ} {x A B : ℂ}
    (ha : HasSum (fun n => a n * x ^ n) A) (hb : HasSum (fun n => b n * x ^ n) B) :
    HasSum (fun n => (∑ k ∈ Finset.range (n + 1), a k * b (n - k)) * x ^ n) (A * B) := by
  have h := hasSum_sum_range_mul_of_summable_norm ha.summable.norm hb.summable.norm
  rw [ha.tsum_eq, hb.tsum_eq] at h
  convert h using 1
  ext n
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  rw [show x ^ n = x ^ k * x ^ (n - k) by rw [← pow_add, Nat.add_sub_of_le hkn]]
  ring

/-- Coefficients of a scalar power series are determined by its sums on a small disk. -/
lemma trigR4_coeff_unique_ball {c d : ℕ → ℂ} {g : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hc : ∀ z : ℂ, ‖z‖ < ρ → HasSum (fun n => c n * z ^ n) (g z))
    (hd : ∀ z : ℂ, ‖z‖ < ρ → HasSum (fun n => d n * z ^ n) (g z)) : c = d := by
  set ρ' : NNReal := ⟨ρ / 2, by positivity⟩
  have series {e : ℕ → ℂ}
      (he : ∀ z : ℂ, ‖z‖ < ρ → HasSum (fun n => e n * z ^ n) (g z)) :
      HasFPowerSeriesOnBall g (FormalMultilinearSeries.ofScalars ℂ e) 0 (ρ' : ENNReal) := by
    exact hasFPowerSeriesOnBall_of_hasSum_ball
      (by rw [← NNReal.coe_pos]; exact half_pos hρ) (half_lt_self hρ) he
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
lemma trigR4_hasSum_odd_iff {a : ℕ → ℂ} {s : ℂ} :
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

/-- Integrating a scalar power series termwise recovers its normalized holomorphic primitive
on the same centered disk. Coefficients are identified through the Cauchy–Taylor expansion. -/
theorem hasSum_primitive_on_ball {f : ℂ → ℂ} {a : ℕ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 R)) (hf0 : f 0 = 0)
    (ha : ∀ z : ℂ, ‖z‖ < R → HasSum (fun n => a n * z ^ n) (deriv f z))
    {z : ℂ} (hz : ‖z‖ < R) :
    HasSum (fun n => a n / (n + 1) * z ^ (n + 1)) (f z) := by
  have hd := hf.deriv Metric.isOpen_ball
  have hcoeff : a = fun n => iteratedDeriv n (deriv f) 0 / n ! := by
    apply Complex.trigR4_coeff_unique_ball hR ha
    intro w hw
    convert Complex.hasSum_taylorSeries_on_ball hd (z := w) (by simpa using hw) using 1
    funext n
    simp only [sub_zero, smul_eq_mul]
    ring
  have hs := Complex.hasSum_taylorSeries_on_ball hf (z := z) (by simpa using hz)
  have ht := (hasSum_nat_add_iff' 1).mpr hs
  convert ht using 1
  · funext n
    simp only [hcoeff, sub_zero, smul_eq_mul, ← iteratedDeriv_succ']
    rw [Nat.factorial_succ, Nat.cast_mul]
    push_cast
    field_simp
  · simp [hf0]


/-- An odd power series integrates to an even power series with zero constant term. -/
theorem hasSum_odd_primitive_on_ball {f : ℂ → ℂ} {b : ℕ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 R)) (hf0 : f 0 = 0)
    (hb : ∀ z : ℂ, ‖z‖ < R → HasSum (fun n => b n * z ^ (2 * n + 1)) (deriv f z))
    {z : ℂ} (hz : ‖z‖ < R) :
    HasSum (fun n => b n / (2 * n + 2 : ℂ) * z ^ (2 * n + 2)) (f z) := by
  let c : ℕ → ℂ := fun m => if Even m then 0 else b (m / 2)
  have hc : ∀ w : ℂ, ‖w‖ < R → HasSum (fun m => c m * w ^ m) (deriv f w) := by
    intro w hw
    have he : (fun m => c m * w ^ m) =
        fun m => if Even m then 0 else b (m / 2) * w ^ (2 * (m / 2) + 1) := by
      funext m
      by_cases hm : Even m
      · simp [c, hm]
      · have hmod : m % 2 ≠ 0 := by simpa only [Nat.even_iff] using hm
        have hme : 2 * (m / 2) + 1 = m := by omega
        simp [c, hm, hme]
    rw [he]
    exact Complex.trigR4_hasSum_odd_iff.mpr (hb w hw)
  have hs := Complex.hasSum_primitive_on_ball hR hf hf0 hc hz
  have he : (fun m => c m / (m + 1) * z ^ (m + 1)) =
      fun m => if Even m then 0 else
        b (m / 2) / (2 * ((m / 2 : ℕ) : ℂ) + 2) * z ^ (2 * (m / 2) + 2) := by
    funext m
    by_cases hm : Even m
    · simp [c, hm]
    · have hmod : m % 2 ≠ 0 := by simpa only [Nat.even_iff] using hm
      have hme : m = 2 * (m / 2) + 1 := by omega
      simp only [c, hm, ite_false]
      generalize hn : m / 2 = n
      have hmn : m = 2 * n + 1 := by omega
      rw [hmn]
      push_cast
      rw [show 2 * n + 1 + 1 = 2 * n + 2 by omega]
      ring
  rw [he] at hs
  exact Complex.trigR4_hasSum_odd_iff.mp hs

/-- Integrating an even power series gives the odd series of its primitive normalized at zero. -/
theorem hasSum_even_primitive_on_ball {f : ℂ → ℂ} {b : ℕ → ℂ} {R : ℝ} (hR : 0<R)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 R)) (hf0 : f 0=0)
    (hb : ∀ z : ℂ, ‖z‖<R → HasSum (fun n => b n*z^(2*n)) (deriv f z))
    {z : ℂ} (hz : ‖z‖<R) :
    HasSum (fun n => b n/(2*n+1:ℂ)*z^(2*n+1)) (f z) := by
  let c : ℕ → ℂ := fun m => if Even m then b (m/2) else 0
  have hc : ∀ w : ℂ, ‖w‖<R → HasSum (fun m => c m*w^m) (deriv f w) := by
    intro w hw
    have he : (fun m => c m*w^m) =
        fun m => if Even m then b (m/2)*w^(2*(m/2)) else 0 := by
      funext m
      by_cases hm : Even m
      · have hmod : m%2=0 := by simpa only [Nat.even_iff] using hm
        have hme : 2*(m/2)=m := by omega
        simp [c,hm,hme]
      · simp [c,hm]
    rw [he]
    exact Complex.trigR4_hasSum_even_iff.mpr (hb w hw)
  have hs := Complex.hasSum_primitive_on_ball hR hf hf0 hc hz
  have he : (fun m => c m/(m+1)*z^(m+1)) =
      fun m => if Even m then b (m/2)/(2*((m/2:ℕ):ℂ)+1)*z^(2*(m/2)+1) else 0 := by
    funext m
    by_cases hm : Even m
    · have hmod : m%2=0 := by simpa only [Nat.even_iff] using hm
      have hme : m=2*(m/2) := by omega
      simp only [c,hm,ite_true]
      generalize hn : m/2=n
      have hmn : m=2*n := by omega
      rw [hmn]
      push_cast
      rfl
    · simp [c,hm]
  rw [he] at hs
  exact Complex.trigR4_hasSum_even_iff.mp hs

end Complex
