/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Group.Prod
public import TauCeti.MeasureTheory.Function.Lp.Translation

/-!
# Approximate identities on the line in `L¹`

Let `k ≥ 0` be integrable on `ℝ` with `∫ k = 1`. For an integrable `f`, the averages
`∫ k(u) f(x - εu) du` converge to `f` in `L¹` as `ε → 0`. The proof bounds the `L¹` distance by
`∫ k(u) ‖f(· - εu) - f‖₁ du` (Fubini) and uses the continuity of translation in `L¹`
(TauCeti's `Integrable.continuous_integral_norm_translate_sub`) with dominated convergence.
This covers the Poisson kernel `1/(π(1 + u²))` and the Fejér kernel `(1 - cos u)/(πu²)` of the
line.

## Main results

* `MeasureTheory.Integrable.tendsto_integral_norm_integral_smul_comp_sub_mul_sub`: the `L¹`
  convergence of the scaled averages.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Approximate identity in `L¹(ℝ)`.** For `f` integrable and `k ≥ 0` integrable with
`∫ k = 1`, `∫ ‖∫ k(u) f(x - εu) du - f(x)‖ dx → 0` as `ε → 0`. -/
theorem Integrable.tendsto_integral_norm_integral_smul_comp_sub_mul_sub {f : ℝ → E}
    (hf : Integrable f) {k : ℝ → ℝ} (hk : Integrable k) (hk0 : ∀ u, 0 ≤ k u)
    (hk1 : ∫ u, k u = 1) :
    Tendsto (fun ε : ℝ => ∫ x, ‖(∫ u, k u • f (x - ε * u)) - f x‖) (𝓝 0) (𝓝 0) := by
  set g : ℝ → ℝ := fun c => ∫ x, ‖f (x - c) - f (x - 0)‖ with hg
  have hgc : Continuous g := hf.continuous_integral_norm_translate_sub 0
  have hg0 : g 0 = 0 := by simp [hg]
  have hgle : ∀ c, g c ≤ 2 * ∫ x, ‖f x‖ := by
    intro c
    calc g c ≤ ∫ x, (‖f (x - c)‖ + ‖f x‖) := by
          refine integral_mono ((hf.comp_sub_right c).sub hf |>.norm |>.congr ?_)
            ((hf.comp_sub_right c).norm.add hf.norm) fun x => by
              simpa only [sub_zero] using norm_sub_le (f (x - c)) (f x)
          exact Eventually.of_forall fun x => by simp
      _ = 2 * ∫ x, ‖f x‖ := by
          rw [integral_add (hf.comp_sub_right c).norm hf.norm,
            integral_sub_right_eq_self (fun x => ‖f x‖) c]
          ring
  have key : ∀ ε : ℝ, ∫ x, ‖(∫ u, k u • f (x - ε * u)) - f x‖ ≤ ∫ u, k u * g (ε * u) := by
    intro ε
    set G : ℝ × ℝ → E := fun p => k p.2 • (f (p.1 - ε * p.2) - f p.1) with hG
    have hQ : QuasiMeasurePreserving (fun p : ℝ × ℝ => p.1 - ε * p.2)
        (volume.prod volume) volume :=
      QuasiMeasurePreserving.prod_of_left (by fun_prop)
        (Eventually.of_forall fun u =>
          (measurePreserving_sub_right volume (ε * u)).quasiMeasurePreserving)
    have hGm : AEStronglyMeasurable G (volume.prod volume) := by
      refine (hk.aestronglyMeasurable.comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_snd).smul ?_
      exact (hf.aestronglyMeasurable.comp_quasiMeasurePreserving hQ).sub
        (hf.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst)
    have hGu : ∀ u, ∫ x, ‖G (x, u)‖ = k u * g (ε * u) := by
      intro u
      simp only [hG, hg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hk0 u), sub_zero]
      rw [integral_const_mul]
    have hGi : Integrable G (volume.prod volume) := by
      rw [integrable_prod_iff' hGm]
      refine ⟨Eventually.of_forall fun u => ((hf.comp_sub_right (ε * u)).sub hf).smul (k u), ?_⟩
      simp_rw [hGu]
      refine (hk.mul_const (2 * ∫ x, ‖f x‖)).mono'
        (hk.aestronglyMeasurable.mul (hgc.comp (continuous_const.mul continuous_id)
          |>.aestronglyMeasurable)) (Eventually.of_forall fun u => ?_)
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (hk0 u) (integral_nonneg fun _ => norm_nonneg _))]
      exact mul_le_mul_of_nonneg_left (hgle _) (hk0 u)
    calc ∫ x, ‖(∫ u, k u • f (x - ε * u)) - f x‖ ≤ ∫ x, ∫ u, ‖G (x, u)‖ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
            hGi.norm.integral_prod_left ?_
          filter_upwards [hGi.prod_right_ae] with x hx
          have hkx : Integrable fun u => k u • f x := hk.smul_const (f x)
          have hsum : Integrable fun u => k u • f (x - ε * u) :=
            (hx.add hkx).congr (Eventually.of_forall fun u => by simp [hG, smul_sub])
          have : (∫ u, k u • f (x - ε * u)) - f x = ∫ u, G (x, u) := by
            rw [show f x = ∫ u, k u • f x by rw [integral_smul_const, hk1, one_smul],
              ← integral_sub hsum hkx]
            congr 1; funext u; simp [hG, smul_sub]
          rw [this]
          exact norm_integral_le_integral_norm _
      _ = ∫ u, ∫ x, ‖G (x, u)‖ := integral_integral_swap hGi.norm
      _ = ∫ u, k u * g (ε * u) := by simp_rw [hGu]
  have hJ : Tendsto (fun ε : ℝ => ∫ u, k u * g (ε * u)) (𝓝 0) (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (l := 𝓝 (0 : ℝ))
      (F := fun ε u => k u * g (ε * u)) (f := fun u => k u * g (0 * u))
      (fun u => k u * (2 * ∫ x, ‖f x‖))
      (Eventually.of_forall fun ε => (hk.aestronglyMeasurable.mul
        (hgc.comp (continuous_const.mul continuous_id)).aestronglyMeasurable))
      (Eventually.of_forall fun ε => Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hk0 u)
          (integral_nonneg fun _ => norm_nonneg _))]
        exact mul_le_mul_of_nonneg_left (hgle _) (hk0 u))
      (hk.mul_const _)
      (Eventually.of_forall fun u => ((continuous_const.mul
        (hgc.comp (continuous_id.mul continuous_const))).tendsto 0))
    simpa [hg0] using h
  exact squeeze_zero (fun ε => integral_nonneg fun _ => norm_nonneg _) key hJ

end MeasureTheory
