/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Complex.ZeroLocalization
public import TauCeti.Analysis.Complex.Conformal.Rouche

/-!
# Zero localization by comparison with an exponential model

Asymptotic zeros of special functions (erf and Fresnel zeros, DLMF §7.13; large zeros of Kummer's
function, DLMF 13.9.9; Airy `Bi` zeros) are located by comparing the function on a small circle
with the model `A (exp (z - w) - 1)`, whose only zero in a disc of radius `ρ ≤ 1/2` about `w` is
the simple zero `w`. Rouché's theorem (`TauCeti.rouche`, Tau Ceti) then transfers existence and
the count, with multiplicity, to the function.

## Main results

* `DLMF.erfZ_count_eq_one_of_expModel`: exactly one zero, counted with multiplicity.
* `DLMF.erfZ_exists_zero_of_expModel`: a zero in the open disc.
* `DLMF.erfZ_existsUnique_zero_of_expModel`: exactly one zero in the open disc, and it is simple.

The single-point count lemma follows the private `TauCeti.count_eq_single` of
`TauCeti.Analysis.Complex.Conformal.LocalDegree`.
-/

@[expose] public noncomputable section

open Complex Metric Set Filter
open scoped Topology

namespace DLMF

/-- If `z₀` is the only zero of `f` in the open disc, the zero count is the order at `z₀`
(after the private `TauCeti.count_eq_single`). -/
theorem erfZ_count_eq_single {f : ℂ → ℂ} {c z₀ : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hz₀ : z₀ ∈ ball c R)
    (hone : ∀ z ∈ ball c R, z ≠ z₀ → f z ≠ 0) :
    (∑ᶠ z ∈ ball c R, analyticOrderNatAt f z) = analyticOrderNatAt f z₀ := by
  classical
  have hsub : (({z₀} : Finset ℂ) : Set ℂ) ⊆ ball c R := by simpa using hz₀
  have h1 : ball c R ∩ Function.support (fun z => analyticOrderNatAt f z)
      ⊆ (({z₀} : Finset ℂ) : Set ℂ) := by
    rintro z ⟨hzb, hzs⟩
    simp only [Function.mem_support, ne_eq] at hzs
    by_contra hne
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hne
    exact hzs (by
      simp [analyticOrderNatAt,
        (hf z (ball_subset_closedBall hzb)).analyticOrderAt_eq_zero.2 (hone z hzb hne)])
  rw [finsum_mem_eq_sum_of_subset _ h1 hsub, Finset.sum_singleton]

/-- The exponential model `A (exp (z - w) - 1)` has exactly one zero, of order one, in the open
disc of radius `ρ ≤ 1/2` about `w`. -/
theorem erfZ_expModel_count {w A : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 1 / 2) (hA : A ≠ 0) :
    (∑ᶠ z ∈ ball w ρ, analyticOrderNatAt (fun z => A * (exp (z - w) - 1)) z) = 1 := by
  have han : AnalyticOnNhd ℂ (fun z => A * (exp (z - w) - 1)) (closedBall w ρ) := by
    intro z _
    fun_prop
  rw [erfZ_count_eq_single han (mem_ball_self hρ)]
  · have hd : HasDerivAt (fun z => A * (exp (z - w) - 1)) (A * (exp (w - w) * 1)) w := by
      have := (((hasDerivAt_id w).sub_const w).cexp.sub_const 1).const_mul A
      simpa using this
    have h1 := (han w (mem_closedBall_self hρ.le)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
      (by simp) (by rw [hd.deriv]; simpa using hA)
    simp [analyticOrderNatAt, h1]
  · intro z hz hne
    have hz' : ‖z - w‖ < ρ := mem_ball_iff_norm.mp hz
    have hpos : 0 < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have := Complex.zloc_norm_exp_sub_one_ge (ζ := z - w) (by linarith)
    refine mul_ne_zero hA fun h0 => ?_
    rw [h0, norm_zero] at this
    linarith

/-- **Exponential-model Rouché criterion**, count form. If `f` is analytic on `closedBall w ρ`
with `0 < ρ ≤ 1/2`, `A ≠ 0`, and `‖f z - A (exp (z - w) - 1)‖ < ‖A‖ ρ / 2` on the circle
`‖z - w‖ = ρ`, then `f` has exactly one zero in the open disc, counted with multiplicity. -/
theorem erfZ_count_eq_one_of_expModel {f : ℂ → ℂ} {w A : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hρ2 : ρ ≤ 1 / 2) (hA : A ≠ 0) (hf : AnalyticOnNhd ℂ f (closedBall w ρ))
    (hs : ∀ z ∈ sphere w ρ, ‖f z - A * (exp (z - w) - 1)‖ < ‖A‖ * ρ / 2) :
    (∑ᶠ z ∈ ball w ρ, analyticOrderNatAt f z) = 1 := by
  have han : AnalyticOnNhd ℂ (fun z => A * (exp (z - w) - 1)) (closedBall w ρ) := by
    intro z _
    fun_prop
  rw [← TauCeti.rouche hρ han hf (fun z hz => ?_), erfZ_expModel_count hρ hρ2 hA]
  have hzw : ‖z - w‖ = ρ := mem_sphere_iff_norm.mp hz
  have hlow := Complex.zloc_norm_exp_sub_one_ge (ζ := z - w) (by linarith)
  rw [norm_sub_rev, norm_mul]
  calc ‖f z - A * (exp (z - w) - 1)‖ < ‖A‖ * ρ / 2 := hs z hz
    _ = ‖A‖ * (‖z - w‖ / 2) := by rw [hzw]; ring
    _ ≤ ‖A‖ * ‖exp (z - w) - 1‖ := by gcongr

/-- Under the exponential-model hypothesis, `f` has no zero on the circle. -/
theorem erfZ_expModel_ne_zero_sphere {f : ℂ → ℂ} {w A : ℂ} {ρ : ℝ}
    (hρ2 : ρ ≤ 1 / 2)
    (hs : ∀ z ∈ sphere w ρ, ‖f z - A * (exp (z - w) - 1)‖ < ‖A‖ * ρ / 2) :
    ∀ z ∈ sphere w ρ, f z ≠ 0 := by
  intro z hz h0
  have h := hs z hz
  have hzw : ‖z - w‖ = ρ := mem_sphere_iff_norm.mp hz
  have hlow := Complex.zloc_norm_exp_sub_one_ge (ζ := z - w) (by linarith)
  rw [h0, zero_sub, norm_neg, norm_mul] at h
  have : ‖A‖ * (ρ / 2) ≤ ‖A‖ * ‖exp (z - w) - 1‖ := by
    gcongr; linarith
  linarith

/-- **Exponential-model Rouché criterion**, existence form: under the hypotheses of
`erfZ_count_eq_one_of_expModel`, `f` has a zero in the open disc `ball w ρ`. -/
theorem erfZ_exists_zero_of_expModel {f : ℂ → ℂ} {w A : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hρ2 : ρ ≤ 1 / 2) (hA : A ≠ 0) (hf : AnalyticOnNhd ℂ f (closedBall w ρ))
    (hs : ∀ z ∈ sphere w ρ, ‖f z - A * (exp (z - w) - 1)‖ < ‖A‖ * ρ / 2) :
    ∃ z ∈ ball w ρ, f z = 0 := by
  have hcount := erfZ_count_eq_one_of_expModel hρ hρ2 hA hf hs
  have hne : ∃ z ∈ closedBall w ρ, f z ≠ 0 :=
    TauCeti.exists_mem_closedBall_ne_zero_of_forall_mem_sphere_ne_zero hρ.le
      (erfZ_expModel_ne_zero_sphere hρ2 hs)
  by_contra hno
  push Not at hno
  have := (TauCeti.finsum_analyticOrderNatAt_ball_eq_zero_iff hf hne).2 hno
  omega

/-- **Exponential-model Rouché criterion**, uniqueness form: under the hypotheses of
`erfZ_count_eq_one_of_expModel`, `f` has exactly one zero in the open disc, and that zero has
order one. -/
theorem erfZ_existsUnique_zero_of_expModel {f : ℂ → ℂ} {w A : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hρ2 : ρ ≤ 1 / 2) (hA : A ≠ 0) (hf : AnalyticOnNhd ℂ f (closedBall w ρ))
    (hs : ∀ z ∈ sphere w ρ, ‖f z - A * (exp (z - w) - 1)‖ < ‖A‖ * ρ / 2) :
    ∃! z, z ∈ ball w ρ ∧ f z = 0 ∧ analyticOrderNatAt f z = 1 := by
  classical
  have hcount := erfZ_count_eq_one_of_expModel hρ hρ2 hA hf hs
  obtain ⟨z, hz, hz0⟩ := erfZ_exists_zero_of_expModel hρ hρ2 hA hf hs
  have hne : ∃ x ∈ closedBall w ρ, f x ≠ 0 :=
    TauCeti.exists_mem_closedBall_ne_zero_of_forall_mem_sphere_ne_zero hρ.le
      (erfZ_expModel_ne_zero_sphere hρ2 hs)
  have hnetop : ∀ y ∈ ball w ρ, f y = 0 → 1 ≤ analyticOrderNatAt f y := by
    intro y hy hy0
    have h1 : analyticOrderAt f y ≠ 0 :=
      (hf y (ball_subset_closedBall hy)).analyticOrderAt_ne_zero.2 hy0
    obtain ⟨x, hx, hxne⟩ := hne
    have h2 : analyticOrderAt f y ≠ ⊤ :=
      hf.analyticOrderAt_ne_top_of_isPreconnected (convex_closedBall w ρ).isPreconnected hx
        (ball_subset_closedBall hy) (by simp [(hf x hx).analyticOrderAt_eq_zero.2 hxne])
    have : analyticOrderNatAt f y ≠ 0 := by
      simp [analyticOrderNatAt, ENat.toNat_eq_zero, h1, h2]
    omega
  have hle : ∀ y ∈ ball w ρ, analyticOrderNatAt f y ≤ 1 := fun y hy =>
    hcount ▸ TauCeti.analyticOrderNatAt_le_finsum_ball hf hy
  have hord : analyticOrderNatAt f z = 1 := le_antisymm (hle z hz) (hnetop z hz hz0)
  refine ⟨z, ⟨hz, hz0, hord⟩, ?_⟩
  rintro y ⟨hy, hy0, hyord⟩
  by_contra hyz
  -- two distinct zeros would give count at least two
  have hfin : (ball w ρ ∩ Function.support (fun x => analyticOrderNatAt f x)).Finite := by
    by_contra hinf
    have : (∑ᶠ x ∈ ball w ρ, analyticOrderNatAt f x) = 0 := by
      rw [finsum_mem_def]
      apply finsum_of_infinite_support
      intro hfin'
      apply hinf
      refine hfin'.subset ?_
      rintro x ⟨hxb, hxs⟩
      simp only [Function.mem_support, ne_eq] at hxs ⊢
      simpa [hxb] using hxs
    omega
  have hsub : (({y, z} : Finset ℂ) : Set ℂ) ⊆ ball w ρ := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hy
    · exact hz
  have h2 : ∑ i ∈ ({y, z} : Finset ℂ), analyticOrderNatAt f i ≤
      ∑ᶠ x ∈ ball w ρ, analyticOrderNatAt f x := by
    rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ hfin]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Set.Finite.mem_toFinset]
      rcases hx with rfl | rfl
      · exact ⟨hy, by simp [Function.mem_support, hyord]⟩
      · exact ⟨hz, by simp [Function.mem_support, hord]⟩
    · intros; exact Nat.zero_le _
  rw [Finset.sum_pair hyz, hyord, hord, hcount] at h2
  omega

end DLMF
