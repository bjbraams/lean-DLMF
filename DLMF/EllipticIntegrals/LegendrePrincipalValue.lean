/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.LegendreSymmetricForms
public import DLMF.EllipticIntegrals.SymmetricPrincipalValue
public import DLMFMathlib.Analysis.Integral.PrincipalValueLevelSets

/-!
# Principal values of Legendre's integral of the third kind

The substitution `t = csc² θ - csc² φ` expresses the defining principal value of `Π`
in terms of `R_F` and `R_J`. A level cutoff of `1 - α² sin² θ` becomes an asymmetric
interval excision about `t = α² - csc² φ`, symmetric to first order.

## Main results

* `incompleteEllipticPi_eq_symmetricEllipticRF_add_RJ`: the symmetric representation for
  real characteristic away from an endpoint pole, including Cauchy principal values.
* `completeEllipticPi_eq_symmetricEllipticRF_add_RJ`: the corresponding complete formula.
* `symmetricEllipticRC_mul_ofReal`: positive real homogeneity including principal values.
* `mul_symmetricEllipticRJ_self_right_ofReal`: partial fractions at repeated real nodes,
  allowing a negative third-kind parameter.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Real Topology

namespace DLMF.EllipticIntegrals

open DLMF.JacobiElliptic

/-- On a real segment, the defining principal value uses ordinary real interval integrals. -/
theorem principalValueSegmentIntegral_ofReal (g f : ℂ → ℂ) (φ : ℝ) :
    principalValueSegmentIntegral g f φ = limUnder (𝓝[>] (0 : ℝ)) fun ε : ℝ =>
      ∫ θ in (0 : ℝ)..φ, if ε ≤ ‖g θ‖ then f θ else 0 := by
  unfold principalValueSegmentIntegral
  congr 1
  funext ε
  have H := primitive_ofReal (fun θ : ℂ => if ε ≤ ‖g θ‖ then f θ else 0) φ
  rw [primitive_eq_integral] at H
  simpa only [mul_ite, mul_zero] using H

/-- The real-amplitude third integral is the limit of its level-truncated angular integrals. -/
lemma incompleteEllipticPi_eq_limUnder_cutoff (φ α : ℝ) (k : ℂ) :
    incompleteEllipticPi φ α k = limUnder (𝓝[>] (0 : ℝ)) fun ε : ℝ =>
      ∫ θ in (0 : ℝ)..φ, if ε ≤ |1 - α * Real.sin θ ^ 2| then
        (1 - (α : ℂ) * (Real.sin θ : ℂ) ^ 2)⁻¹ *
          (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) else 0 := by
  rw [incompleteEllipticPi, principalValueSegmentIntegral_ofReal]
  congr 1
  funext ε
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  rw [← ofReal_sin]
  have hn : ‖1 - (α : ℂ) * (Real.sin θ : ℂ) ^ 2‖ = |1 - α * Real.sin θ ^ 2| := by
    rw [← ofReal_pow, ← ofReal_mul, ← ofReal_one, ← ofReal_sub, norm_real,
      Real.norm_eq_abs]
  rw [hn]

namespace LegendrePrincipalValue

/-- The reciprocal characteristic becomes the angular characteristic under `csc²`. -/
lemma one_sub_div_csc_sq {θ : ℝ} (hs : Real.sin θ ≠ 0) (α c : ℝ) :
    1 - α / (1 / Real.sin θ ^ 2 - c + c) = 1 - α * Real.sin θ ^ 2 := by
  field_simp
  ring

/-- The level-truncated angular integral after the `csc²` substitution. -/
lemma integral_cutoff_csc_sq {φ : ℝ} (hφ : 0 < φ) (hφ1 : φ ≤ π / 2)
    (k : ℂ) (α : ℝ) {ε : ℝ} (hε : 0 < ε) :
    let c : ℝ := 1 / Real.sin φ ^ 2
    let S : ℝ → ℂ := carlsonRootProduct ((c : ℂ) - 1) ((c : ℂ) - k ^ 2) c
    (∫ θ in (0 : ℝ)..φ, if ε ≤ |1 - α * Real.sin θ ^ 2| then
      (1 - (α : ℂ) * (Real.sin θ : ℂ) ^ 2)⁻¹ *
        (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) else 0) =
      ∫ t in Ioi (0 : ℝ), if ε ≤ |1 - α / (t + c)| then
        (1 / 2 : ℂ) * (S t)⁻¹ + (α : ℂ) / 2 * (S t * ((t : ℂ) + ((c - α : ℝ) : ℂ)))⁻¹ else 0 := by
  intro c S
  rw [integral_Ioi_eq_integral_Ioo_csc_sq_subst hφ hφ1,
    intervalIntegral.integral_of_le hφ.le, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have hs : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  rw [one_sub_div_csc_sq hs.ne' α c]
  by_cases hcut : ε ≤ |1 - α * Real.sin θ ^ 2|
  · simp only [ite_eq_left hcut]
    have hreal : 1 - α * Real.sin θ ^ 2 ≠ 0 := by
      intro h
      rw [h, abs_zero] at hcut
      linarith
    have hW : 1 - (α : ℂ) * (Real.sin θ : ℂ) ^ 2 ≠ 0 := by
      rw [← ofReal_pow, ← ofReal_mul, ← ofReal_one, ← ofReal_sub]
      exact ofReal_ne_zero.mpr hreal
    have hS : S (1 / Real.sin θ ^ 2 - c) = (Real.cos θ : ℂ) *
        (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (1 / 2 : ℂ) *
          ((1 / Real.sin θ ^ 3 : ℝ) : ℂ) := by
      exact carlsonRootProduct_csc_sq_subst hs hc k
    have hs0 : Complex.sin (θ : ℂ) ≠ 0 := by
      rw [← ofReal_sin]; exact ofReal_ne_zero.mpr hs.ne'
    have hP : ((1 / Real.sin θ ^ 2 - c : ℝ) : ℂ) + ((c - α : ℝ) : ℂ) =
        (1 - (α : ℂ) * (Real.sin θ : ℂ) ^ 2) / (Real.sin θ : ℂ) ^ 2 := by
      push_cast
      field_simp [hs0]
      ring
    rw [hS, hP, cpow_neg]
    generalize (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (1 / 2 : ℂ) = V
    by_cases hV : V = 0
    · simp [hV]
    have hsC : (Real.sin θ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
    have hcC : (Real.cos θ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
    push_cast at hW hsC hcC ⊢
    field_simp [hW, hsC, hcC, hV]
    ring
  · simp only [ite_eq_right hcut, mul_zero]

end LegendrePrincipalValue

/-- The truncated third-kind integrals converge through an interior pole. -/
theorem LegendrePrincipalValue.tendsto_integral_cutoff_of_lt_characteristic {φ : ℝ}
    (hφ : 0 < φ) (hφ1 : φ ≤ π / 2) {k : ℂ}
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) {α : ℝ}
    (hα : 1 / Real.sin φ ^ 2 < α) :
    let c : ℝ := 1 / Real.sin φ ^ 2
    Tendsto (fun ε : ℝ => ∫ θ in (0 : ℝ)..φ,
      if ε ≤ |1 - α * Real.sin θ ^ 2| then
        (1 - (α : ℂ) * (Real.sin θ : ℂ) ^ 2)⁻¹ *
          (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) else 0)
      (𝓝[>] 0) (𝓝 (symmetricEllipticRF ((c : ℂ) - 1) ((c : ℂ) - k ^ 2) c +
        (α : ℂ) / 3 * symmetricEllipticRJ ((c : ℂ) - 1) ((c : ℂ) - k ^ 2) c (c - α : ℝ))) := by
  intro c
  change c < α at hα
  let p : ℝ := c - α
  let a : ℝ := -p
  let S : ℝ → ℂ := carlsonRootProduct ((c : ℂ) - 1) ((c : ℂ) - k ^ 2) c
  let J : ℝ → ℂ := fun t => (S t * ((t : ℂ) + p))⁻¹
  let leftGap : ℝ → ℝ := fun ε => α * ε / (1 + ε)
  let rightGap : ℝ → ℝ := fun ε => α * ε / (1 - ε)
  have hsφ : 0 < Real.sin φ :=
    Real.sin_pos_of_pos_of_lt_pi hφ (by linarith [Real.pi_pos])
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : 1 ≤ c := by
    dsimp [c]
    rw [le_div_iff₀ (sq_pos_of_pos hsφ)]
    simpa only [one_mul] using Real.sin_sq_le_one φ
  have hα0 : 0 < α := hc.trans hα
  have hp : p < 0 := by dsimp [p]; linarith
  have ha : 0 < a := neg_pos.mpr hp
  have hac : a + c = α := by dsimp [a, p]; ring
  have hx : (c : ℂ) - 1 ∈ slitPlane ∨ (c : ℂ) - 1 = 0 := by
    rcases hc1.eq_or_lt with h | h
    · right; rw [← h]; simp
    · left
      rw [← ofReal_one, ← ofReal_sub]
      exact ofReal_mem_slitPlane.mpr (sub_pos.mpr h)
  have hy : (c : ℂ) - k ^ 2 ∈ slitPlane := csc_sq_sub_mem_slitPlane hφ hφ1 hk
  have hz : (c : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hc
  have hiF := integrableOn_symmetricEllipticRF_integrand hx hy hz
  change IntegrableOn (fun t => (S t)⁻¹) (Ioi 0) at hiF
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < 1 := Ioo_mem_nhdsGT zero_lt_one
  have hleft : Tendsto leftGap (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have H : Tendsto leftGap (𝓝 0) (𝓝 (leftGap 0)) := by
        apply ContinuousAt.tendsto
        dsimp [leftGap]
        fun_prop (disch := norm_num)
      simpa [leftGap] using H.mono_left nhdsWithin_le_nhds
    · filter_upwards [hsmall] with ε hε
      dsimp [leftGap]
      exact div_pos (mul_pos hα0 hε.1) (by linarith)
  have hright : Tendsto rightGap (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have H : Tendsto rightGap (𝓝 0) (𝓝 (rightGap 0)) := by
        apply ContinuousAt.tendsto
        dsimp [rightGap]
        fun_prop (disch := norm_num)
      simpa [rightGap] using H.mono_left nhdsWithin_le_nhds
    · filter_upwards [hsmall] with ε hε
      dsimp [rightGap]
      exact div_pos (mul_pos hα0 hε.1) (by linarith)
  have hratio : Tendsto (fun ε => leftGap ε / rightGap ε) (𝓝[>] 0) (𝓝 1) := by
    have H : Tendsto (fun ε : ℝ => (1 - ε) / (1 + ε)) (𝓝 0) (𝓝 1) := by
      have hc : ContinuousAt (fun ε : ℝ => (1 - ε) / (1 + ε)) 0 := by
        fun_prop (disch := norm_num)
      simpa using hc.tendsto
    refine (H.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [hsmall] with ε hε
    dsimp [leftGap, rightGap]
    field_simp [hα0.ne', hε.1.ne', show 1 - ε ≠ 0 by linarith,
      show 1 + ε ≠ 0 by linarith]
  have hF : Tendsto (fun ε => ∫ t in Ioi (0 : ℝ) \
        Icc (a - leftGap ε) (a + rightGap ε), (S t)⁻¹)
      (𝓝[>] 0) (𝓝 (∫ t in Ioi (0 : ℝ), (S t)⁻¹)) := by
    have hi0 : IntegrableOn (fun t : ℝ => (S t)⁻¹ -
        (Icc (a / 2) (3 * a / 2)).indicator (fun t => (0 : ℂ) / ((t : ℂ) - a)) t)
        (Ioi 0) := by simpa using hiF
    have H := tendsto_setIntegral_diff_Icc_of_integrableOn_sub (0 : ℂ)
      (by linarith : a / 2 < a) (by linarith : a < 3 * a / 2) measurableSet_Ioi
      (fun t ht => by change 0 < t; linarith [ht.1]) hi0 hleft hright hratio
    simpa using H
  have hJ := tendsto_integral_symmetricEllipticRJ_of_neg hx hy hz hp hleft hright hratio
  change Tendsto (fun ε => ∫ t in Ioi (0 : ℝ) \
      Icc (a - leftGap ε) (a + rightGap ε), J t) (𝓝[>] 0)
        (𝓝 ((2 / 3 : ℂ) * symmetricEllipticRJ ((c : ℂ) - 1) ((c : ℂ) - k ^ 2) c p)) at hJ
  have hkey : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫ θ in (0 : ℝ)..φ, if ε ≤ |1 - α * Real.sin θ ^ 2| then
        (1 - (α : ℂ) * (Real.sin θ : ℂ) ^ 2)⁻¹ *
          (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) else 0) =
        (1 / 2 : ℂ) * (∫ t in Ioi (0 : ℝ) \ Icc (a - leftGap ε) (a + rightGap ε), (S t)⁻¹) +
          (α : ℂ) / 2 * (∫ t in Ioi (0 : ℝ) \
            Icc (a - leftGap ε) (a + rightGap ε), J t) := by
    filter_upwards [hsmall] with ε hε
    rw [LegendrePrincipalValue.integral_cutoff_csc_sq hφ hφ1 k α hε.1]
    have Hlevel := integral_indicator_one_sub_div_eq_diff_Icc
      (fun t => (1 / 2 : ℂ) * (S t)⁻¹ + (α : ℂ) / 2 * J t) (a := a) hc hε.1 hε.2
    rw [hac] at Hlevel
    rw [Hlevel]
    have hiFc := hiF.mono_set
      (show Ioi (0 : ℝ) \ Icc (a - leftGap ε) (a + rightGap ε) ⊆ Ioi 0 from sdiff_subset)
    have hL : 0 < leftGap ε := div_pos (mul_pos hα0 hε.1) (by linarith)
    have hR : 0 < rightGap ε := div_pos (mul_pos hα0 hε.1) (by linarith)
    have hiJ0 := integrableOn_carlsonRootProduct_mul_sub_inv_diff_Ioo hx hy hz
      (c := a) (by linarith : a - leftGap ε < a) (by linarith : a < a + rightGap ε)
    have hiJc : IntegrableOn J
        (Ioi (0 : ℝ) \ Icc (a - leftGap ε) (a + rightGap ε)) := by
      have H := hiJ0.mono_set (show Ioi (0 : ℝ) \ Icc (a - leftGap ε) (a + rightGap ε) ⊆
          Ioi 0 \ Ioo (a - leftGap ε) (a + rightGap ε) from
        fun t ht => ⟨ht.1, fun h => ht.2 (Ioo_subset_Icc_self h)⟩)
      simpa only [J, S, a, ofReal_neg, sub_neg_eq_add] using H
    have H := integral_add (hiFc.const_mul (1 / 2 : ℂ)) (hiJc.const_mul ((α : ℂ) / 2))
    simpa only [Pi.add_apply, integral_const_mul] using H
  have H := ((hF.const_mul (1 / 2 : ℂ)).add (hJ.const_mul ((α : ℂ) / 2))).congr'
    (hkey.mono fun ε h => h.symm)
  have hend : (1 / 2 : ℂ) * (∫ t in Ioi (0 : ℝ), (S t)⁻¹) +
        (α : ℂ) / 2 * ((2 / 3 : ℂ) *
          symmetricEllipticRJ ((c : ℂ) - 1) ((c : ℂ) - k ^ 2) c p) =
      symmetricEllipticRF ((c : ℂ) - 1) ((c : ℂ) - k ^ 2) c + (α : ℂ) / 3 *
        symmetricEllipticRJ ((c : ℂ) - 1) ((c : ℂ) - k ^ 2) c p := by
    change _ = (1 / 2 : ℂ) * (∫ t in Ioi (0 : ℝ), (S t)⁻¹) + _
    ring
  rw [hend] at H
  exact H

/-- The `R_F,R_J` representation of `Π` when its real characteristic crosses the path. -/
theorem incompleteEllipticPi_eq_symmetricEllipticRF_add_RJ_of_lt_characteristic {φ : ℝ}
    (hφ : 0 < φ) (hφ1 : φ ≤ π / 2) {k : ℂ}
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) {α : ℝ}
    (hα : 1 / Real.sin φ ^ 2 < α) :
    let c : ℝ := 1 / Real.sin φ ^ 2
    incompleteEllipticPi φ α k =
      symmetricEllipticRF ((c : ℂ) - 1) ((c : ℂ) - k ^ 2) c + (α : ℂ) / 3 *
        symmetricEllipticRJ ((c : ℂ) - 1) ((c : ℂ) - k ^ 2) c (c - α : ℝ) := by
  intro c
  rw [incompleteEllipticPi_eq_limUnder_cutoff]
  exact (LegendrePrincipalValue.tendsto_integral_cutoff_of_lt_characteristic
    hφ hφ1 hk hα).limUnder_eq

/-- The symmetric representation of `Π` for real characteristic, including principal values. -/
theorem incompleteEllipticPi_eq_symmetricEllipticRF_add_RJ {φ : ℝ}
    (hφ : 0 < φ) (hφ1 : φ ≤ π / 2) {k : ℂ}
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) {α : ℝ}
    (hα : α ≠ 1 / Real.sin φ ^ 2) :
    let c : ℝ := 1 / Real.sin φ ^ 2
    incompleteEllipticPi φ α k =
      symmetricEllipticRF ((c : ℂ) - 1) ((c : ℂ) - k ^ 2) c + (α : ℂ) / 3 *
        symmetricEllipticRJ ((c : ℂ) - 1) ((c : ℂ) - k ^ 2) c (c - α : ℝ) := by
  intro c
  rcases lt_or_gt_of_ne hα with hlt | hgt
  · have hsφ : 0 < Real.sin φ :=
      Real.sin_pos_of_pos_of_lt_pi hφ (by linarith [Real.pi_pos])
    have hc : c * Real.sin φ ^ 2 = 1 := by dsimp [c]; field_simp
    have hpos : 0 < 1 - α * Real.sin φ ^ 2 := by
      have H := mul_pos (sub_pos.mpr hlt) (sq_pos_of_pos hsφ)
      nlinarith
    have hαs : 1 - (α : ℂ) * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane := by
      rw [← ofReal_pow, ← ofReal_mul, ← ofReal_one, ← ofReal_sub]
      exact ofReal_mem_slitPlane.mpr hpos
    have hps : (c : ℂ) - α ∈ slitPlane := by
      rw [← ofReal_sub]
      exact ofReal_mem_slitPlane.mpr (sub_pos.mpr hlt)
    have hP := incompleteEllipticPi_sub_incompleteEllipticF_eq_integral hφ.le hφ1 hk hαs
    have hJ := symmetricEllipticRJ_csc_sq_eq_integral hφ hφ1 k (α : ℂ)
      (not_isNegReal_of_mem_slitPlane hps)
    have hF : incompleteEllipticF φ k =
        symmetricEllipticRF ((c : ℂ) - 1) ((c : ℂ) - k ^ 2) c := by
      rw [incompleteEllipticF_ofReal_eq_integral, symmetricEllipticRF_csc_sq_eq_integral hφ hφ1]
    rw [hF] at hP
    push_cast
    linear_combination hP - (α : ℂ) / 3 * hJ
  · exact incompleteEllipticPi_eq_symmetricEllipticRF_add_RJ_of_lt_characteristic hφ hφ1 hk hgt

/-- The complete third integral as `R_F + (α²/3)R_J`, including principal values. -/
theorem completeEllipticPi_eq_symmetricEllipticRF_add_RJ {k : ℂ}
    (hk : 1 - k ^ 2 ∈ slitPlane) {α : ℝ} (hα : α ≠ 1) :
    completeEllipticPi α k = symmetricEllipticRF 0 (1 - k ^ 2) 1 +
      (α : ℂ) / 3 * symmetricEllipticRJ 0 (1 - k ^ 2) 1 (1 - α : ℝ) := by
  have hφ : 0 < π / 2 := by positivity
  have hks : 1 - k ^ 2 * (Real.sin (π / 2) : ℂ) ^ 2 ∈ slitPlane := by simpa using hk
  have hαs : α ≠ 1 / Real.sin (π / 2) ^ 2 := by simpa using hα
  have H := incompleteEllipticPi_eq_symmetricEllipticRF_add_RJ hφ le_rfl hks hαs
  simpa only [Real.sin_pi_div_two, one_pow, one_div, inv_one, ofReal_one, sub_self,
    completeEllipticPi,
    show ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) by push_cast; ring] using H

/-- The complementary characteristic relation for the complete third symmetric integral. -/
theorem symmetricEllipticRJ_complete_reciprocal_parameter {k α : ℝ}
    (hk : k ^ 2 < 1) (hα : 1 < α) :
    (α : ℂ) * symmetricEllipticRJ 0 (1 - k ^ 2 : ℝ) 1 (1 - α : ℝ) +
      (k ^ 2 / α : ℝ) *
        symmetricEllipticRJ 0 (1 - k ^ 2 : ℝ) 1 (1 - k ^ 2 / α : ℝ) =
      -3 * symmetricEllipticRF 0 (1 - k ^ 2 : ℝ) 1 := by
  have hα0 : 0 < α := by linarith
  have hω : k ^ 2 / α < 1 := (div_lt_one hα0).mpr (by linarith)
  have hp : 1 - α ≠ 0 := by linarith
  have hq : 1 - k ^ 2 / α ≠ 0 := by linarith
  have hrel : (1 - α - 1) * (1 - k ^ 2 / α - 1) =
      (0 - 1) * (1 - k ^ 2 - 1) := by field_simp; ring
  have hneg : (1 - α) * (1 - k ^ 2 / α) / 1 - 0 * (1 - k ^ 2) / 1 < 0 := by
    simpa using mul_neg_of_neg_of_pos (by linarith : 1 - α < 0)
      (by linarith : 0 < 1 - k ^ 2 / α)
  have H := symmetricEllipticRJ_change_parameter_of_neg_difference
    zero_lt_one (le_refl (0 : ℝ)) (by linarith : 0 ≤ 1 - k ^ 2)
    (fun _ => by linarith : (0 : ℝ) = 0 → 1 - k ^ 2 ≠ 0) hp hq hrel hneg
  have hRC : symmetricEllipticRC 0 ((1 - α) * (1 - k ^ 2 / α) : ℝ) = 0 := by
    have H := (symmetricEllipticRC_of_neg
      (by simpa using hneg : (1 - α) * (1 - k ^ 2 / α) < 0) le_rfl).1
    simpa using H
  simp only [zero_mul, div_one, ofReal_zero, ofReal_one] at H
  rw [hRC] at H
  simp only [symmetricEllipticRJ_comm_left 0 1,
    symmetricEllipticRJ_comm_right 0 ((1 - k ^ 2 : ℝ) : ℂ) 1,
    symmetricEllipticRF_comm_left 0 1,
    symmetricEllipticRF_comm_right 0 ((1 - k ^ 2 : ℝ) : ℂ) 1] at H
  push_cast at H ⊢
  linear_combination -H

/-- Positive real homogeneity of `R_C` on positive arguments. -/
theorem symmetricEllipticRC_mul_ofReal_pos {l x y : ℝ} (hl : 0 < l)
    (hx : 0 < x) (hy : 0 < y) :
    symmetricEllipticRC (l * x : ℝ) (l * y : ℝ) =
      (Real.sqrt l : ℂ)⁻¹ * symmetricEllipticRC x y := by
  have hxs := ofReal_mem_slitPlane.mpr hx
  have hys := ofReal_mem_slitPlane.mpr hy
  have hz : (![x, y] : Fin 2 → ℂ) ∈ Carlson.carlsonRSlitDomain := by
    intro i
    fin_cases i <;> simp [hxs, hys]
  have H := symmetricEllipticR_mul (1 / 2) (![1 / 2, 1] : Fin 2 → ℂ) hz
    (ofReal_mem_slitPlane.mpr hl) (by
      intro i
      rw [arg_ofReal_of_nonneg hl.le, zero_add]
      exact ⟨neg_pi_lt_arg _, lt_of_le_of_ne (arg_le_pi _)
        (mem_slitPlane_iff_arg.mp (hz i)).1⟩)
  have hv : (fun i : Fin 2 => (l : ℂ) * (![x, y] : Fin 2 → ℂ) i) =
      ![((l * x : ℝ) : ℂ), ((l * y : ℝ) : ℂ)] := by
    funext i; fin_cases i <;> simp
  rw [hv] at H
  rw [symmetricEllipticRC_eq_symmetricEllipticR (ofReal_mem_slitPlane.mpr (mul_pos hl hx))
    (ofReal_mem_slitPlane.mpr (mul_pos hl hy)),
    symmetricEllipticRC_eq_symmetricEllipticR hxs hys]
  rw [H, cpow_neg, Carlson.ofReal_cpow_half hl.le]

/-- Positive real homogeneity of `R_C`, including principal values at negative second argument. -/
theorem symmetricEllipticRC_mul_ofReal {l x y : ℝ} (hl : 0 < l)
    (hx : 0 < x) (hy : y ≠ 0) :
    symmetricEllipticRC (l * x : ℝ) (l * y : ℝ) =
      (Real.sqrt l : ℂ)⁻¹ * symmetricEllipticRC x y := by
  rcases lt_or_gt_of_ne hy with hy | hy
  · have hxy : 0 < x - y := by linarith
    rw [(symmetricEllipticRC_of_neg (mul_neg_of_pos_of_neg hl hy) (mul_pos hl hx).le).1,
      (symmetricEllipticRC_of_neg hy hx.le).1]
    simp only [← ofReal_sub, ← ofReal_neg]
    rw [show l * x - l * y = l * (x - y) by ring,
      show -(l * y) = l * (-y) by ring,
      symmetricEllipticRC_mul_ofReal_pos hl hxy (neg_pos.mpr hy)]
    have he : l * x / (l * (x - y)) = x / (x - y) := by field_simp
    rw [he]
    ring
  · exact symmetricEllipticRC_mul_ofReal_pos hl hx hy

/-- Homogeneity under division by a positive real number, with the principal-value branch. -/
theorem symmetricEllipticRC_div_ofReal {l x y : ℝ} (hl : 0 < l)
    (hx : 0 < x) (hy : y ≠ 0) :
    symmetricEllipticRC (x / l : ℝ) (y / l : ℝ) =
      (Real.sqrt l : ℂ) * symmetricEllipticRC x y := by
  have H := symmetricEllipticRC_mul_ofReal (inv_pos.mpr hl) hx hy
  simpa only [mul_comm l⁻¹, ← div_eq_mul_inv, Real.sqrt_inv, ofReal_inv, inv_inv] using H

/-- Partial fractions for two repeated nodes of `R_J`, including a negative parameter. -/
theorem mul_symmetricEllipticRJ_self_right_ofReal {x y p : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hp : p ≠ 0) :
    ((p - y : ℝ) : ℂ) * symmetricEllipticRJ x y y p =
      3 * symmetricEllipticRC x y - 3 * symmetricEllipticRC x p := by
  have H := symmetricEllipticRJ_change_parameter' hy hx.le hy.le
    (fun _ => hy.ne') hp hy.ne' (by ring : (p - y) * (y - y) = (x - y) * (y - y))
  have hxy : x * y / y = x := by field_simp
  have hpy : p * y / y = p := by field_simp
  simp only [sub_self, ofReal_zero, zero_mul, add_zero, hxy, hpy] at H
  rw [symmetricEllipticRJ_comm_left, symmetricEllipticRF_comm_left,
    ← symmetricEllipticRC_eq_symmetricEllipticRF x
      (not_isNegReal_of_mem_slitPlane (ofReal_mem_slitPlane.mpr hy))] at H
  exact H

/-- Carlson's symmetric integral is continuous at every vector of slit-plane nodes. -/
theorem continuousAt_symmetricEllipticR {ι : Type*} [Fintype ι] (a : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ Carlson.carlsonRSlitDomain) :
    ContinuousAt (symmetricEllipticR a b) z := by
  have H : ContinuousAt (Carlson.carlsonR (-a) b) z := by
    unfold Carlson.carlsonR
    exact continuousAt_const.mul (Carlson.analyticOnNhd_regCarlsonR (-a) b z hz).continuousAt
  apply H.congr
  filter_upwards [Carlson.isOpen_carlsonRSlitDomain.mem_nhds hz] with w hw
  exact (symmetricEllipticR_of_mem a b hw).symm

/-- The third symmetric integral is continuous in its parameter on the slit plane. -/
theorem continuousAt_symmetricEllipticRJ_parameter {x y z p : ℂ}
    (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane)
    (hp : p ∈ slitPlane) : ContinuousAt (symmetricEllipticRJ x y z) p := by
  let b : Fin 4 → ℂ := ![1 / 2, 1 / 2, 1 / 2, 1]
  have hvec : ContinuousAt (fun q : ℂ => (![x, y, z, q] : Fin 4 → ℂ)) p := by
    apply continuousAt_pi.mpr
    intro i
    fin_cases i <;> simp <;> fun_prop
  have hReg : ContinuousAt (Carlson.regCarlsonR (-(3 / 2)) b) ![x, y, z, p] :=
    (Carlson.analyticOnNhd_regCarlsonR (-(3 / 2)) b _
      (vec4_mem_carlsonRSlitDomain hx hy hz hp)).continuousAt
  have hComp : ContinuousAt
      (fun q : ℂ => Carlson.regCarlsonR (-(3 / 2)) b ![x, y, z, q]) p := by
    exact hReg.tendsto.comp hvec.tendsto
  have H : ContinuousAt (fun q : ℂ => Carlson.carlsonR (-(3 / 2)) b ![x, y, z, q]) p := by
    unfold Carlson.carlsonR
    exact continuousAt_const.mul hComp
  apply H.congr
  filter_upwards [isOpen_slitPlane.mem_nhds hp] with q hq
  rw [symmetricEllipticRJ_eq_symmetricEllipticR hx hy hz hq,
    symmetricEllipticR_of_mem _ _ (vec4_mem_carlsonRSlitDomain hx hy hz hq)]

/-- Continuity in the parameter when the first node vanishes and the other nodes are admissible. -/
theorem continuousAt_symmetricEllipticRJ_zero_parameter {y z p : ℂ}
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) (hp : p ∈ slitPlane) :
    ContinuousAt (symmetricEllipticRJ 0 y z) p := by
  have hvec : ContinuousAt (fun q : ℂ => (![y, z, q] : Fin 3 → ℂ)) p := by
    apply continuousAt_pi.mpr
    intro i
    fin_cases i <;> simp <;> fun_prop
  have hComp : ContinuousAt (fun q : ℂ =>
      symmetricEllipticR (3 / 2) (![1 / 2, 1 / 2, 1] : Fin 3 → ℂ) ![y, z, q]) p :=
    (continuousAt_symmetricEllipticR _ _ (vec3_mem_carlsonRSlitDomain hy hz hp)).tendsto.comp
      hvec.tendsto
  have H := (continuousAt_const (y := 3 * (π : ℂ) / 4)).mul hComp
  apply H.congr
  filter_upwards [isOpen_slitPlane.mem_nhds hp] with q hq
  exact (symmetricEllipticRJ_zero_left hy hz hq).symm


/-- Continuity of the complete third integral in a real characteristic less than one. -/
theorem continuousAt_completeEllipticPi_characteristic {k : ℂ}
    (hk : 1 - k ^ 2 ∈ slitPlane) {α : ℝ} (hα : α < 1) :
    ContinuousAt (fun a : ℝ => completeEllipticPi a k) α := by
  have hJ := continuousAt_symmetricEllipticRJ_zero_parameter hk one_mem_slitPlane
    (ofReal_mem_slitPlane.mpr (sub_pos.mpr hα))
  have hComp : ContinuousAt (fun a : ℝ =>
      symmetricEllipticRJ 0 (1 - k ^ 2) 1 (1 - a : ℝ)) α :=
    hJ.tendsto.comp
      (show ContinuousAt (fun a : ℝ => ((1 - a : ℝ) : ℂ)) α by fun_prop).tendsto
  have H : ContinuousAt (fun a : ℝ => symmetricEllipticRF 0 (1 - k ^ 2) 1 +
      (a : ℂ) / 3 * symmetricEllipticRJ 0 (1 - k ^ 2) 1 (1 - a : ℝ)) α :=
    continuousAt_const.add (((by fun_prop : ContinuousAt (fun a : ℝ => (a : ℂ) / 3) α)).mul
      hComp)
  apply H.congr
  filter_upwards [eventually_lt_nhds hα] with a ha
  exact (completeEllipticPi_eq_symmetricEllipticRF_add_RJ hk ha.ne).symm

namespace LegendrePrincipalValue

/-- Integrability of the regular complete elliptic kernel on the angular interval. -/
theorem integrableOn_completeEllipticKernel {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) :
    IntegrableOn (fun θ : ℝ => (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)))
      (Ioc 0 (π / 2)) := by
  have hks : 1 - k ^ 2 * (Real.sin (π / 2) : ℂ) ^ 2 ∈ slitPlane := by simpa using hk
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mp
    (continuousOn_one_sub_mul_sin_sq_cpow (by positivity) le_rfl hks _).intervalIntegrable

/-- A characteristic cutoff preserves the regular complete elliptic integral. -/
theorem tendsto_integral_cutoff_completeEllipticK {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) (α : ℝ) :
    Tendsto (fun ε : ℝ => ∫ θ in (0 : ℝ)..(π / 2), if ε ≤ |1 - α * Real.sin θ ^ 2| then
      (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) else 0)
      (𝓝[>] 0) (𝓝 (completeEllipticK k)) := by
  have H := tendsto_integral_indicator_abs_ge (integrableOn_completeEllipticKernel hk)
    (show Measurable (fun θ : ℝ => 1 - α * Real.sin θ ^ 2) by fun_prop)
    (Real.ae_one_sub_mul_sin_sq_ne_zero_Ioc α)
  have hvalue : completeEllipticK k = ∫ θ in (0 : ℝ)..(π / 2),
      (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) := by
    rw [completeEllipticK_eq_incompleteEllipticF,
      show ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) by push_cast; ring,
      incompleteEllipticF_ofReal_eq_integral]
  rw [hvalue]
  simpa only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ π / 2 by positivity)] using H

/-- The complete third-kind cutoff converges to the defining principal value. -/
theorem tendsto_integral_cutoff_completeEllipticPi {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane)
    {α : ℝ} (hα : α ≠ 1) :
    Tendsto (fun ε : ℝ => ∫ θ in (0 : ℝ)..(π / 2), if ε ≤ |1 - α * Real.sin θ ^ 2| then
      (1 - (α : ℂ) * (Real.sin θ : ℂ) ^ 2)⁻¹ *
        (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) else 0)
      (𝓝[>] 0) (𝓝 (completeEllipticPi α k)) := by
  have hpi : (0 : ℝ) < π / 2 := by positivity
  have hpiC : ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) := by push_cast; ring
  rcases lt_or_gt_of_ne hα with hα | hα
  · have hchar : Continuous (fun θ : ℝ => (1 - (α : ℂ) * (Real.sin θ : ℂ) ^ 2)⁻¹) := by
      refine continuous_iff_continuousAt.mpr fun θ => ?_
      refine (show ContinuousAt (fun θ : ℝ => 1 - (α : ℂ) * (Real.sin θ : ℂ) ^ 2) θ
        by fun_prop).inv₀ ?_
      rw [← ofReal_pow, ← ofReal_mul, ← ofReal_one, ← ofReal_sub]
      exact ofReal_ne_zero.mpr (DLMF.Elliptic.one_sub_mul_sin_sq_pos hα θ).ne'
    have hks : 1 - k ^ 2 * (Real.sin (π / 2) : ℂ) ^ 2 ∈ slitPlane := by simpa using hk
    have hroot := continuousOn_one_sub_mul_sin_sq_cpow hpi.le le_rfl hks (-(1 / 2 : ℂ))
    have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume) hpi.le).mp
      (hchar.continuousOn.mul hroot).intervalIntegrable
    have H := tendsto_integral_indicator_abs_ge hi
      (show Measurable (fun θ : ℝ => 1 - α * Real.sin θ ^ 2) by fun_prop)
      (Real.ae_one_sub_mul_sin_sq_ne_zero_Ioc α)
    simp only [← intervalIntegral.integral_of_le hpi.le, Pi.mul_apply] at H
    have hvalue : completeEllipticPi α k = ∫ θ in (0 : ℝ)..(π / 2),
        (1 - (α : ℂ) * (Real.sin θ : ℂ) ^ 2)⁻¹ *
          (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) := by
      rw [completeEllipticPi, hpiC, incompleteEllipticPi_eq_limUnder_cutoff]
      exact H.limUnder_eq
    rwa [← hvalue] at H
  · have hks : 1 - k ^ 2 * (Real.sin (π / 2) : ℂ) ^ 2 ∈ slitPlane := by simpa using hk
    have hαs : 1 / Real.sin (π / 2) ^ 2 < α := by simpa using hα
    have H := tendsto_integral_cutoff_of_lt_characteristic hpi le_rfl hks hαs
    simp only [Real.sin_pi_div_two, one_pow, div_one, ofReal_one, sub_self] at H
    rw [completeEllipticPi_eq_symmetricEllipticRF_add_RJ hk hα.ne']
    exact H

end LegendrePrincipalValue

/-- Bulirsch's complete integral uses the same real level cutoff as Legendre's third integral. -/
theorem bulirschCel_eq_limUnder_cutoff (kc : ℂ) (p a b : ℝ) :
    bulirschCel kc p a b = limUnder (𝓝[>] (0 : ℝ)) fun ε : ℝ =>
      ∫ θ in (0 : ℝ)..(π / 2), if ε ≤ |1 - (1 - p) * Real.sin θ ^ 2| then
        ((a : ℂ) + (b - a : ℝ) * (Real.sin θ : ℂ) ^ 2) /
          (1 - ((1 - p : ℝ) : ℂ) * (Real.sin θ : ℂ) ^ 2) *
            (1 - jacobiComodulus kc ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) else 0 := by
  rw [bulirschCel, show ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) by push_cast; ring,
    principalValueSegmentIntegral_ofReal]
  congr 1
  funext ε
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [← ofReal_sin, ← ofReal_cos]
  have hcs : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  push_cast at hcs
  have hg : (Real.cos θ : ℂ) ^ 2 + (p : ℂ) * (Real.sin θ : ℂ) ^ 2 =
      1 - ((1 - p : ℝ) : ℂ) * (Real.sin θ : ℂ) ^ 2 := by
    push_cast
    linear_combination hcs
  have hn : (a : ℂ) * (Real.cos θ : ℂ) ^ 2 + b * (Real.sin θ : ℂ) ^ 2 =
      (a : ℂ) + (b - a : ℝ) * (Real.sin θ : ℂ) ^ 2 := by
    push_cast
    linear_combination (a : ℂ) * hcs
  have hk : (Real.cos θ : ℂ) ^ 2 + kc ^ 2 * (Real.sin θ : ℂ) ^ 2 =
      1 - jacobiComodulus kc ^ 2 * (Real.sin θ : ℂ) ^ 2 := by
    rw [jacobiComodulus_sq_eq_one_sub_sq]
    push_cast
    linear_combination hcs
  rw [hg, hn, hk]
  have hnorm : ‖1 - ((1 - p : ℝ) : ℂ) * (Real.sin θ : ℂ) ^ 2‖ =
      |1 - (1 - p) * Real.sin θ ^ 2| := by
    rw [← ofReal_pow, ← ofReal_mul, ← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs]
  rw [hnorm]

namespace ThirdKindBounds

/-- A lower bound for the increment in `Π` at a positive characteristic. -/
theorem completeEllipticPiOfParameter_ge_add {m α : ℝ} (hm0 : 0 ≤ m) (hm : m < 1)
    (hα : 1 < α) :
    DLMF.Elliptic.Real.completeEllipticKOfParameter m + (1 / α) *
      (DLMF.Elliptic.Real.completeEllipticKOfParameter m -
        DLMF.Elliptic.Real.completeEllipticEOfParameter m) ≤
      DLMF.Elliptic.Real.completeEllipticPiOfParameter (m / α) m := by
  have hα0 : 0 < α := by linarith
  have hn : m / α < 1 := (div_lt_one hα0).mpr (by linarith)
  have hn0 : 0 ≤ m / α := div_nonneg hm0 hα0.le
  have hK := (DLMF.Elliptic.continuous_one_sub_mul_sin_sq_rpow hm (-(1 / 2 : ℝ))).intervalIntegrable
    (μ := volume) 0 (π / 2)
  have hE := (DLMF.Elliptic.continuous_one_sub_mul_sin_sq_rpow hm (1 / 2 : ℝ)).intervalIntegrable
    (μ := volume) 0 (π / 2)
  rw [DLMF.Elliptic.Real.completeEllipticKOfParameter,
    DLMF.Elliptic.Real.completeEllipticEOfParameter,
    DLMF.Elliptic.Real.completeEllipticPiOfParameter,
    DLMF.Elliptic.Real.incompleteEllipticPiOfParameter,
    ← intervalIntegral.integral_sub hK hE, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add hK ((hK.sub hE).const_mul (1 / α))]
  apply intervalIntegral.integral_mono_on (by positivity)
    (hK.add ((hK.sub hE).const_mul (1 / α)))
    ((DLMF.Elliptic.continuous_piIntegrand hn hm).intervalIntegrable _ _) fun θ _ => ?_
  have hU := DLMF.Elliptic.one_sub_mul_sin_sq_pos hm θ
  have hV := DLMF.Elliptic.one_sub_mul_sin_sq_pos hn θ
  have hp : (1 - m * Real.sin θ ^ 2) ^ (1 / 2 : ℝ) =
      (1 - m * Real.sin θ ^ 2) * (1 - m * Real.sin θ ^ 2) ^ (-(1 / 2) : ℝ) := by
    rw [show (1 / 2 : ℝ) = 1 + (-(1 / 2)) by norm_num, Real.rpow_add hU, Real.rpow_one]
    norm_num
  have hInv : 1 + m / α * Real.sin θ ^ 2 ≤ (1 - m / α * Real.sin θ ^ 2)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hV]
    nlinarith [sq_nonneg (m / α * Real.sin θ ^ 2)]
  have H := mul_le_mul_of_nonneg_right hInv
    (Real.rpow_nonneg hU.le (-(1 / 2 : ℝ)))
  simp only [DLMF.Elliptic.piIntegrand, hp]
  have hEq : m / α = (1 / α) * m := by ring
  rw [hEq] at H
  linear_combination H

/-- The second complete real integral is at most `π/2` for `0 ≤ m < 1`. -/
theorem completeEllipticEOfParameter_le_pi_div_two {m : ℝ} (hm0 : 0 ≤ m) (hm : m < 1) :
    DLMF.Elliptic.Real.completeEllipticEOfParameter m ≤ π / 2 := by
  have hE := (DLMF.Elliptic.continuous_one_sub_mul_sin_sq_rpow hm (1 / 2 : ℝ)).intervalIntegrable
    (μ := volume) 0 (π / 2)
  calc DLMF.Elliptic.Real.completeEllipticEOfParameter m ≤
      ∫ θ in (0 : ℝ)..(π / 2), (1 : ℝ) := by
        apply intervalIntegral.integral_mono_on (by positivity) hE intervalIntegrable_const
        intro θ _
        exact Real.rpow_le_one (DLMF.Elliptic.one_sub_mul_sin_sq_pos hm θ).le
          (by nlinarith [sq_nonneg (Real.sin θ)]) (by norm_num)
    _ = π / 2 := by simp

end ThirdKindBounds

end DLMF.EllipticIntegrals
