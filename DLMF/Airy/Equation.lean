/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Framework
public import DLMF.Airy.ErrorBoundTools
public import DLMFMathlib.Analysis.SpecialFunctions.Gamma.Values

/-!
# Numerically satisfactory pairs of Airy solutions (DLMF §9.2(v))

## Main results

* `airy_pair_wellConditioned_real`, `airy_pair_wellConditioned_sector`,
  `airy_rotated_pair_wellConditioned`, `airy_two_rotations_wellConditioned`: the numerically
  satisfactory pairs of DLMF Table 9.2.1.

## Implementation notes

The other §9.2 results (rotated solutions, the general solution, Wronskians and connection
formulas) are in `DLMF.Airy.Basic.Connections`, and the Maclaurin series of DLMF §9.4 in
`DLMF.Airy.Basic.Maclaurin`.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF.Confluent
open scoped Real Topology Nat
namespace DLMF.Airy

/-- `Ai'` is continuous. -/
private lemma continuous_deriv_airyAi : Continuous (deriv airyAi) := by
  rw [deriv_airyAi]
  exact Differentiable.continuous (𝕜 := ℂ) fun z => (hasDerivAt_airyAiDeriv z).differentiableAt

/-- `Bi'` is continuous. -/
private lemma continuous_deriv_airyBi : Continuous (deriv airyBi) := by
  rw [deriv_airyBi]
  exact Differentiable.continuous (𝕜 := ℂ) fun z => (hasDerivAt_airyBiDeriv z).differentiableAt

/-- The real-axis pair in DLMF Table 9.2.1 is numerically independent. -/
theorem airy_pair_wellConditioned_real  :
    IsWellConditionedPairOn airyAi airyBi {z : ℂ | z.im = 0} := by
  obtain ⟨R, B, h⟩ := airyErr_far_real
  have hπ : (1 / π : ℂ) ≠ 0 := one_div_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  refine airyErr_wellConditioned_of_far differentiable_airyAi.continuous
    differentiable_airyBi.continuous continuous_deriv_airyAi continuous_deriv_airyBi hπ ?_
    (R := R) (B := B) ?_
  · intro z; rw [deriv_airyAi, deriv_airyBi]; exact wronskian_airyAi_airyBi z
  · intro z hz hR
    rw [deriv_airyAi, deriv_airyBi]
    exact h z hz hR

/-- The first complex-sector pair in DLMF Table 9.2.1. -/
theorem airy_pair_wellConditioned_sector  :
    IsWellConditionedPairOn airyAi airyBi {z : ℂ | |arg z| ≤ π / 3 ∨ (z.im = 0 ∧ z.re ≤ 0)} := by
  obtain ⟨R, B, h⟩ := airyErr_far_real
  obtain ⟨R', B', h'⟩ := airyErr_far_sector
  have hπ : (1 / π : ℂ) ≠ 0 := one_div_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  refine airyErr_wellConditioned_of_far differentiable_airyAi.continuous
    differentiable_airyBi.continuous continuous_deriv_airyAi continuous_deriv_airyBi hπ ?_
    (R := max (max R R') 1) (B := max B B') ?_
  · intro z; rw [deriv_airyAi, deriv_airyBi]; exact wronskian_airyAi_airyBi z
  · intro z hz hR
    rw [deriv_airyAi, deriv_airyBi]
    have hz0 : z ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hR; linarith [le_max_right (max R R') 1]
    rcases hz with hz | hz
    · exact (h' z ((le_max_right _ _).trans ((le_max_left _ _).trans hR)) hz0 hz).trans
        (le_max_right _ _)
    · exact (h z hz.1 ((le_max_left _ _).trans ((le_max_left _ _).trans hR))).trans
        (le_max_left _ _)

/-- On the sector `-π/3 ≤ ε ph z ≤ π`, `ℜζ(z) + ℜζ(z e^{-2επi/3}) ≥ 0`, where
`ζ = (2/3) z^{3/2}`. -/
private lemma airy_rotated_pair_re_nonneg {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {z : ℂ} (hz0 : z ≠ 0)
    (hz : -π / 3 ≤ ε * arg z ∧ ε * arg z ≤ π) :
    0 ≤ (airyZetaComplex z).re + (airyZetaComplex (z * exp (-ε * (2 * π * I / 3)))).re := by
  have hπ := Real.pi_pos
  set c := exp (-ε * (2 * π * I / 3))
  have hlt := Complex.neg_pi_lt_arg z
  have hle := Complex.arg_le_pi z
  obtain ⟨hz1, hz2⟩ := hz
  rcases hε with rfl | rfl
  · simp only [one_mul] at hz1 hz2
    rcases eq_or_lt_of_le hz1 with h | h
    · have hcc : c = exp (((4 * π / 3 : ℝ) : ℂ) * I) := by
        simp only [c]
        rw [show (((4 * π / 3 : ℝ) : ℂ) * I) = -((1 : ℝ) : ℂ) * (2 * π * I / 3) + 2 * π * I by
          push_cast; ring, exp_add, exp_two_pi_mul_I, mul_one]
      rw [hcc, airyErr_zeta_rot hz0 (α := 4 * π / 3) (by linarith) (by linarith)
        (κ := 1) (by rw [show (((4 * π / 3 : ℝ) : ℂ) * I * (3 / 2)) = 2 * π * I by push_cast; ring,
          exp_two_pi_mul_I]), mul_one]
      have := airyErr_re_zeta_nonneg hz0 (abs_le.mpr ⟨by linarith, by linarith⟩)
      linarith
    · have hcc : c = exp (((-(2 * π / 3)) : ℝ) * I) := by
        simp only [c]; congr 1; push_cast; ring
      rw [hcc, airyErr_zeta_rot hz0 (α := -(2 * π / 3)) (by linarith) (by linarith)
        (κ := -1) (by rw [show ((((-(2 * π / 3)) : ℝ) : ℂ) * I * (3 / 2)) = -(π * I) by
          push_cast; ring, exp_neg, exp_pi_mul_I]; norm_num)]
      simp
  · have hcc : c = exp (((2 * π / 3 : ℝ)) * I) := by
      simp only [c]; congr 1; push_cast; ring
    have : arg z ≤ π / 3 := by linarith
    rw [hcc, airyErr_zeta_rot hz0 (α := 2 * π / 3) (by linarith) (by linarith)
      (κ := -1) (by rw [show (((2 * π / 3 : ℝ) : ℂ) * I * (3 / 2)) = π * I by
        push_cast; ring, exp_pi_mul_I])]
    simp

/-- The mixed pairs in DLMF Table 9.2.1. -/
theorem airy_rotated_pair_wellConditioned {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    IsWellConditionedPairOn airyAi (fun z => airyAi (z * exp (-ε * (2 * π * I / 3))))
      {z : ℂ | -π / 3 ≤ ε * arg z ∧ ε * arg z ≤ π} := by
  have hπ := Real.pi_pos
  obtain ⟨C, R, hC, hU⟩ := airyErr_ai_uniform
  set c := exp (-ε * (2 * π * I / 3))
  have hc : ‖c‖ = 1 := by
    rw [show c = exp (((-ε * (2 * π / 3) : ℝ) : ℂ) * I) by simp only [c]; congr 1; push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hW := wronskian_airyAi_rotated (z := 0) hε
  have hW0 : exp (ε * (π * I / 6)) / (2 * π) ≠ 0 :=
    div_ne_zero (exp_ne_zero _) (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero))
  refine airyErr_wellConditioned_of_far differentiable_airyAi.continuous (airyErr_continuous_rot c)
    continuous_deriv_airyAi
    (by rw [airyErr_deriv_rot]; exact airyErr_continuous_deriv_rot c) hW0
    (fun z => by rw [deriv_airyAi, airyErr_deriv_rot]
                 have := wronskian_airyAi_rotated z hε
                 simp only at this ⊢
                 linear_combination this) (R := max R 1) (B := 2 * (C ^ 2 / (4 * π))) ?_
  intro z hz hR
  have hz0 : z ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hR; linarith [le_max_right R 1]
  have hRz : R ≤ ‖z‖ := (le_max_left _ _).trans hR
  have hzc0 : z * c ≠ 0 := mul_ne_zero hz0 (exp_ne_zero _)
  have hzcn : ‖z‖ = ‖z * c‖ := by rw [norm_mul, hc, mul_one]
  have hre := airy_rotated_pair_re_nonneg hε hz0 hz
  rw [deriv_airyAi, airyErr_deriv_rot]
  simp only
  rw [norm_mul, hc, mul_one]
  have k1 := airyErr_cross_le hC hU hz0 hzc0 hzcn hRz hre
  have k2 := airyErr_cross_le hC hU hzc0 hz0 hzcn.symm (hzcn ▸ hRz) (by linarith)
  linarith [mul_comm ‖airyAiDeriv z‖ ‖airyAi (z * c)‖]

/-- For `|ph u| ≤ 2π/3`, `ℜζ(u e^{πi/3}) + ℜζ(u e^{-πi/3}) ≥ 0`, where `ζ = (2/3) z^{3/2}`. -/
private lemma airy_two_rotations_re_nonneg {u : ℂ} (hu0 : u ≠ 0) (hz' : |arg u| ≤ 2 * π / 3) :
    0 ≤ (airyZetaComplex (u * exp (((π / 3 : ℝ) : ℂ) * I))).re +
      (airyZetaComplex (u * exp (((-(π / 3)) : ℝ) * I))).re := by
  have hπ := Real.pi_pos
  have hlt := Complex.neg_pi_lt_arg u
  have hb := abs_le.mp hz'
  have hζ₁ : airyZetaComplex (u * exp (((π / 3 : ℝ) : ℂ) * I)) = airyZetaComplex u * I := by
    rw [airyErr_zeta_rot hu0 (by linarith) (by linarith)
      (by rw [show (((π / 3 : ℝ) : ℂ) * I * (3 / 2)) = π / 2 * I by push_cast; ring,
        exp_pi_div_two_mul_I])]
  rw [hζ₁]
  rcases eq_or_lt_of_le hb.1 with h | h
  · -- boundary ray `arg u = -2π/3`: rotate by `5π/3` instead
    have e₂' : u * exp (((-(π / 3)) : ℝ) * I) = u * exp (((5 * π / 3 : ℝ) : ℂ) * I) := by
      rw [show (((5 * π / 3 : ℝ) : ℂ) * I) = (((-(π / 3)) : ℝ) : ℂ) * I + 2 * π * I by
        push_cast; ring, exp_add, exp_two_pi_mul_I, mul_one]
    rw [e₂', airyErr_zeta_rot hu0 (α := 5 * π / 3) (by linarith) (by linarith) (κ := I)
      (by rw [show (((5 * π / 3 : ℝ) : ℂ) * I * (3 / 2)) = π / 2 * I + 2 * π * I by
        push_cast; ring, exp_add, exp_two_pi_mul_I, mul_one, exp_pi_div_two_mul_I])]
    have him := airyErr_im_two_zeta hu0
    rw [← h, show 3 / 2 * (-(2 * π / 3)) = -π by ring, Real.sin_neg, Real.sin_pi, neg_zero,
      mul_zero] at him
    have : (airyZetaComplex u).im = 0 := by simpa using him
    simp [this]
  · rw [airyErr_zeta_rot hu0 (α := -(π / 3)) (by linarith) (by linarith) (κ := -I)
      (by rw [show ((((-(π / 3)) : ℝ) : ℂ) * I * (3 / 2)) = -(π / 2 * I) by push_cast; ring,
        exp_neg, exp_pi_div_two_mul_I, inv_I])]
    simp

/-- The two rotated solutions in DLMF Table 9.2.1. -/
theorem airy_two_rotations_wellConditioned  :
    IsWellConditionedPairOn (fun z => airyAi (z * exp (-2 * π * I / 3)))
      (fun z => airyAi (z * exp (2 * π * I / 3))) {z : ℂ | |arg (-z)| ≤ 2 * π / 3} := by
  have hπ := Real.pi_pos
  obtain ⟨C, R, hC, hU⟩ := airyErr_ai_uniform
  set c₁ := exp (-2 * π * I / 3)
  set c₂ := exp (2 * π * I / 3)
  have hc₁ : c₁ = -exp (((π / 3 : ℝ) : ℂ) * I) := by
    simp only [c₁]
    rw [show (-2 * π * I / 3 : ℂ) = ((π / 3 : ℝ) : ℂ) * I + π * I - 2 * π * I by push_cast; ring,
      exp_sub, exp_add, exp_two_pi_mul_I, exp_pi_mul_I]; ring
  have hc₂ : c₂ = -exp (((-(π / 3)) : ℝ) * I) := by
    simp only [c₂]
    rw [show (2 * π * I / 3 : ℂ) = (((-(π / 3)) : ℝ) : ℂ) * I + π * I by push_cast; ring,
      exp_add, exp_pi_mul_I]; ring
  have hn₁ : ‖c₁‖ = 1 := by rw [hc₁, norm_neg]; exact Complex.norm_exp_ofReal_mul_I _
  have hn₂ : ‖c₂‖ = 1 := by rw [hc₂, norm_neg]; exact Complex.norm_exp_ofReal_mul_I _
  have hW0 : (1 / (2 * π * I) : ℂ) ≠ 0 := one_div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero
    (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero)
  refine airyErr_wellConditioned_of_far (airyErr_continuous_rot c₁) (airyErr_continuous_rot c₂)
    (by rw [airyErr_deriv_rot]; exact airyErr_continuous_deriv_rot c₁)
    (by rw [airyErr_deriv_rot]; exact airyErr_continuous_deriv_rot c₂) hW0
    (fun z => by rw [airyErr_deriv_rot, airyErr_deriv_rot]
                 have := wronskian_airyAi_rotations z
                 simp only at this ⊢
                 linear_combination this) (R := max R 1) (B := 2 * (C ^ 2 / (4 * π))) ?_
  intro z hz hR
  have hz0 : z ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hR; linarith [le_max_right R 1]
  have hRz : R ≤ ‖z‖ := (le_max_left _ _).trans hR
  set u := -z
  have hu0 : u ≠ 0 := neg_ne_zero.mpr hz0
  have e₁ : z * c₁ = u * exp (((π / 3 : ℝ) : ℂ) * I) := by rw [hc₁]; simp only [u]; ring
  have e₂ : z * c₂ = u * exp (((-(π / 3)) : ℝ) * I) := by rw [hc₂]; simp only [u]; ring
  have h₁0 : z * c₁ ≠ 0 := mul_ne_zero hz0 (exp_ne_zero _)
  have h₂0 : z * c₂ ≠ 0 := mul_ne_zero hz0 (exp_ne_zero _)
  have hn : ‖z * c₁‖ = ‖z * c₂‖ := by rw [norm_mul, norm_mul, hn₁, hn₂]
  have hR₁ : R ≤ ‖z * c₁‖ := by rw [norm_mul, hn₁, mul_one]; exact hRz
  have hre : 0 ≤ (airyZetaComplex (z * c₁)).re + (airyZetaComplex (z * c₂)).re := by
    rw [e₁, e₂]; exact airy_two_rotations_re_nonneg hu0 hz
  rw [airyErr_deriv_rot, airyErr_deriv_rot]
  simp only
  rw [norm_mul, norm_mul, hn₁, hn₂, mul_one, mul_one]
  have k1 := airyErr_cross_le hC hU h₁0 h₂0 hn hR₁ hre
  have k2 := airyErr_cross_le hC hU h₂0 h₁0 hn.symm (hn ▸ hR₁) (by linarith)
  linarith [mul_comm ‖airyAiDeriv (z * c₁)‖ ‖airyAi (z * c₂)‖]

end DLMF.Airy
