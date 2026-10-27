/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
public import Mathlib.Analysis.Complex.OpenMapping

/-!
# Surjectivity of the modular invariant

The quotient `E₄³/(E₄³ - E₆²)` of Mathlib's normalised Eisenstein series (`j/1728`) takes every
complex value on the upper half-plane. Proof: the function is holomorphic and `SL(2, ℤ)`-invariant
on `ℍ` and tends to `∞` at `i∞`; its image is open (open mapping theorem) and closed (reduction to
the fundamental domain `𝒟`, whose part below any horizontal line is compact).

## Main results

* `ModularForm.p3w_exists_E₄_cube_div_eq`: every `w : ℂ` equals `E₄(τ)³/(E₄(τ)³ - E₆(τ)²)` for
  some `τ ∈ ℍ`.
-/

@[expose] public noncomputable section

open UpperHalfPlane Filter Topology EisensteinSeries
open scoped MatrixGroups Modular

namespace ModularForm

/-- The modular invariant `J = E₄³/(E₄³ - E₆²)` (`j/1728`). -/
def p3wJ (τ : ℍ) : ℂ := E₄ τ ^ 3 / (E₄ τ ^ 3 - E₆ τ ^ 2)

theorem p3w_E₄_cube_sub_E₆_sq_ne_zero (τ : ℍ) : E₄ τ ^ 3 - E₆ τ ^ 2 ≠ 0 := by
  have h := discriminant_ne_zero τ
  rw [discriminant_eq_E₄_cube_sub_E₆_sq] at h
  intro h'
  rw [h'] at h
  simp at h

theorem p3wJ_smul (g : SL(2, ℤ)) (τ : ℍ) : p3wJ (g • τ) = p3wJ τ := by
  have hg : (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) ∈ 𝒮ℒ :=
    MonoidHom.mem_range.mpr ⟨g, rfl⟩
  have h4 := SlashInvariantForm.slash_action_eqn'' E₄ hg τ
  have h6 := SlashInvariantForm.slash_action_eqn'' E₆ hg τ
  have hs : (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) • τ = g • τ := rfl
  rw [hs] at h4 h6
  have hd : denom (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ τ
  have hD := p3w_E₄_cube_sub_E₆_sq_ne_zero τ
  simp only [p3wJ, h4, h6]
  rw [div_eq_div_iff (by
    have : (denom (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) τ ^ (4 : ℤ) * E₄ τ) ^ 3 -
        (denom (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) τ ^ (6 : ℤ) * E₆ τ) ^ 2 =
        denom (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) τ ^ 12 *
          (E₄ τ ^ 3 - E₆ τ ^ 2) := by
      simp only [zpow_ofNat]; ring
    rw [this]; exact mul_ne_zero (pow_ne_zero _ hd) hD) hD]
  simp only [zpow_ofNat]
  ring

/-- `J` tends to `∞` at `i∞`. -/
lemma p3wJ_large (R : ℝ) : ∃ A : ℝ, ∀ τ : ℍ, A ≤ τ.im → R < ‖p3wJ τ‖ := by
  have h4 : Tendsto (fun τ : ℍ => E₄ τ ^ 3) atImInfty (𝓝 1) := by
    simpa using (tendsto_E_atImInfty (k := 4)).pow 3
  have hD : Tendsto (fun τ : ℍ => E₄ τ ^ 3 - E₆ τ ^ 2) atImInfty (𝓝 0) := by
    simpa using ((tendsto_E_atImInfty (k := 4)).pow 3).sub ((tendsto_E_atImInfty (k := 6)).pow 2)
  set ε : ℝ := 1 / (2 * (|R| + 1)) with hε
  have hεpos : 0 < ε := by positivity
  have e1 : ∀ᶠ τ in atImInfty, (1 / 2 : ℝ) < ‖E₄ τ ^ 3‖ := by
    have := (continuous_norm.tendsto _).comp h4
    simp only [norm_one] at this
    exact this.eventually (lt_mem_nhds (by norm_num))
  have e2 : ∀ᶠ τ in atImInfty, ‖E₄ τ ^ 3 - E₆ τ ^ 2‖ < ε := by
    have := (continuous_norm.tendsto _).comp hD
    simp only [norm_zero] at this
    exact this.eventually (gt_mem_nhds hεpos)
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp (e1.and e2)
  refine ⟨A, fun τ hτ => ?_⟩
  obtain ⟨a1, a2⟩ := hA τ hτ
  have hpos : 0 < ‖E₄ τ ^ 3 - E₆ τ ^ 2‖ := norm_pos_iff.mpr (p3w_E₄_cube_sub_E₆_sq_ne_zero τ)
  rw [p3wJ, norm_div, lt_div_iff₀ hpos]
  calc R * ‖E₄ τ ^ 3 - E₆ τ ^ 2‖ ≤ |R| * ‖E₄ τ ^ 3 - E₆ τ ^ 2‖ := by
        gcongr; exact le_abs_self R
    _ ≤ |R| * ε := by gcongr
    _ < 1 / 2 := by
        rw [hε]; field_simp; linarith [abs_nonneg R]
    _ < _ := a1

/-- `J ∘ ofComplex` is analytic on the upper half-plane. -/
theorem p3wJ_analyticOnNhd :
    AnalyticOnNhd ℂ (p3wJ ∘ ofComplex) {z : ℂ | 0 < z.im} := by
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_upperHalfPlaneSet
  refine DifferentiableOn.analyticOnNhd ?_ hU
  have d4 := UpperHalfPlane.mdifferentiable_iff.mp (E₄.holo')
  have d6 := UpperHalfPlane.mdifferentiable_iff.mp (E₆.holo')
  intro z hz
  have : (p3wJ ∘ ofComplex) = fun z => ((⇑E₄ ∘ ofComplex) z) ^ 3 /
      (((⇑E₄ ∘ ofComplex) z) ^ 3 - ((⇑E₆ ∘ ofComplex) z) ^ 2) := rfl
  rw [this]
  refine DifferentiableWithinAt.div (((d4 z hz).pow 3)) (((d4 z hz).pow 3).sub ((d6 z hz).pow 2))
    ?_
  simpa [Function.comp_apply, ofComplex_apply_of_im_pos hz] using
    p3w_E₄_cube_sub_E₆_sq_ne_zero ⟨z, hz⟩

/-- **Surjectivity of the modular invariant**: every complex `w` is `E₄³/(E₄³ - E₆²)` at some
point of `ℍ`. -/
theorem p3w_exists_E₄_cube_div_eq (w : ℂ) : ∃ τ : ℍ, p3wJ τ = w := by
  set U : Set ℂ := {z : ℂ | 0 < z.im} with hUdef
  set F : ℂ → ℂ := p3wJ ∘ ofComplex with hF
  have hFa : AnalyticOnNhd ℂ F U := p3wJ_analyticOnNhd
  have hFτ : ∀ τ : ℍ, F τ = p3wJ τ := fun τ => by simp [hF]
  have hUo : IsOpen U := isOpen_upperHalfPlaneSet
  have hUc : IsPreconnected U := (convex_halfSpace_im_gt 0).isPreconnected
  set S : Set ℂ := F '' U with hS
  have hSrange : ∀ y ∈ S, ∃ τ : ℍ, p3wJ τ = y := by
    rintro y ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, by rw [← hFτ]⟩
  -- open
  have hSo : IsOpen S := by
    rcases hFa.is_constant_or_isOpen hUc with ⟨c, hc⟩ | h
    · exfalso
      obtain ⟨A, hA⟩ := p3wJ_large ‖c‖
      have := hA (UpperHalfPlane.mk (Complex.I * (max A 1)) (by simp))
        (by simp)
      rw [← hFτ, hc _ (UpperHalfPlane.im_pos _)] at this
      exact lt_irrefl _ this
    · exact h U subset_rfl hUo
  -- closed
  have hScl : IsClosed S := by
    refine closure_subset_iff_isClosed.mp fun w hw => ?_
    obtain ⟨A, hA⟩ := p3wJ_large (‖w‖ + 1)
    set K : Set ℂ := Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ℂ Set.Icc (1 / 2 : ℝ) A with hK
    have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
    have hKU : K ⊆ U := fun z hz => by
      have := hz.2.1; simp only [hUdef, Set.mem_ofPred_eq]; linarith
    have hFK : IsCompact (F '' K) :=
      hKc.image_of_continuousOn (hFa.continuousOn.mono hKU)
    have hsub : S ∩ Metric.ball w 1 ⊆ F '' K := by
      rintro y ⟨hyS, hyb⟩
      obtain ⟨τ, rfl⟩ := hSrange y hyS
      obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
      have him := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hg
      have hre := hg.2
      have hlt : (g • τ).im < A := by
        by_contra hge
        have := hA (g • τ) (not_lt.mp hge)
        rw [p3wJ_smul] at this
        have := norm_le_norm_add_norm_sub' (p3wJ τ) w
        rw [Metric.mem_ball, dist_eq_norm] at hyb
        linarith
      refine ⟨(g • τ : ℍ), ?_, by rw [hFτ, p3wJ_smul]⟩
      have hpos := (g • τ).im_pos
      refine ⟨⟨?_, ?_⟩, ⟨?_, hlt.le⟩⟩
      · have := (abs_le.mp hre).1; simpa using this
      · have := (abs_le.mp hre).2; simpa using this
      · simp only [coe_im]; nlinarith
    have hw' : w ∈ closure (F '' K) := by
      refine closure_mono hsub ?_
      rw [Metric.mem_closure_iff] at hw ⊢
      intro ε hε
      obtain ⟨b, hb, hbd⟩ := hw (min ε 1) (lt_min hε one_pos)
      refine ⟨b, ⟨hb, ?_⟩, lt_of_lt_of_le hbd (min_le_left _ _)⟩
      rw [Metric.mem_ball, dist_comm]
      exact lt_of_lt_of_le hbd (min_le_right _ _)
    rw [hFK.isClosed.closure_eq] at hw'
    exact Set.image_mono hKU hw'
  have hSne : S.Nonempty := ⟨F UpperHalfPlane.I, UpperHalfPlane.I, UpperHalfPlane.I.im_pos, rfl⟩
  have huniv : S = Set.univ := (IsClopen.eq_univ ⟨hScl, hSo⟩ hSne)
  exact hSrange w (huniv ▸ Set.mem_univ w)

end ModularForm
