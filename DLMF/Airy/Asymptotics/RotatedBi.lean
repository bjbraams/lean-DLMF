/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Asymptotics.OscillatoryForms

/-!
# Rotated expansions of the Airy Bi function

The Bi connection formulas transfer the sector expansions to rotated arguments, with absolute
error envelopes.

Source references and common attribution are retained in
`DLMF.Airy.Asymptotics`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF.Confluent

open scoped Real Topology Interval

namespace DLMF.Airy

/-- At `z` with `|arg z| < 2π/3`, `Bi(z e^{±iπ/3})` is the rotated prefactor times the
cosine/sine combination of the even and odd parts of the normalized `Ai` (via 9.2.11). -/
private lemma airyRot_bi_rot_eq {z : ℂ} (hz0 : z ≠ 0) (hz3 : |arg z| < 2 * π / 3) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) :
    airyBi (z * exp (ε * (π * I / 3))) =
      (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (ε * (π * I / 6)) * z ^ (-1 / 4 : ℂ) *
        (((exp (π * I / 4) * exp (-((ε : ℂ) * Real.log 2 / 2)) / 2) *
              exp (-(airyZetaComplex z * I)) +
            (exp (-(π * I / 4)) * exp ((ε : ℂ) * Real.log 2 / 2) / 2) *
              exp (airyZetaComplex z * I)) *
            airyRot_even (fun w => airyAi w / airyPrefactor .ai w) z +
          I * ((exp (π * I / 4) * exp (-((ε : ℂ) * Real.log 2 / 2)) / 2) *
              exp (-(airyZetaComplex z * I)) -
            (exp (-(π * I / 4)) * exp ((ε : ℂ) * Real.log 2 / 2) / 2) *
              exp (airyZetaComplex z * I)) *
            airyRot_odd (fun w => airyAi w / airyPrefactor .ai w) z) := by
  obtain ⟨u4, um4, u3, um3, u2, um2, u12⟩ := airyRot_u_powers
  have hu6 := airyRot_u_six
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hs0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hl : exp (-((Real.log 2 : ℂ) / 2)) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
    rw [exp_neg, airyRot_exp_half_log_two]
  obtain ⟨d1, d2, d3, d4⟩ := airyRot_third_data hz0 hz3
  have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
  have hp1 := airyRot_prefactor_ne_zero .ai (mul_ne_zero hz0 (exp_ne_zero ((π / 3 : ℝ) * I)))
  have hp2 := airyRot_prefactor_ne_zero .ai
    (mul_ne_zero hz0 (exp_ne_zero ((-(π / 3) : ℝ) * I)))
  have split1 : airyAi (z * exp ((π / 3 : ℝ) * I)) =
      airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I)) *
      (airyAi (z * exp ((π / 3 : ℝ) * I)) / airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I))) := by
    field_simp
  have split2 : airyAi (z * exp ((-(π / 3) : ℝ) * I)) =
      airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I)) *
      (airyAi (z * exp ((-(π / 3) : ℝ) * I)) /
        airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I))) := by field_simp
  have hneg : z ^ (-1 / 4 : ℂ) = (z ^ (1 / 4 : ℂ))⁻¹ := by
    rw [show (-1 / 4 : ℂ) = -(1 / 4) by ring, cpow_neg]
  rcases hε with rfl | rfl
  · simp only [ofReal_one, one_mul]
    rw [airyRot_airyBi_rot_pos z, split1, split2, ← mul_assoc, ← mul_assoc,
      airyRot_decomp (fun w => airyAi w / airyPrefactor .ai w)]
    have ep : I * airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I)) =
        (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (π * I / 6) * z ^ (-1 / 4 : ℂ) *
          (exp (π * I / 4) * exp (-((Real.log 2 : ℂ) / 2)) / 2 *
            exp (-(airyZetaComplex z * I))) := by
      simp only [airyPrefactor]
      rw [d1, d3, airyRot_two_div_pi_cpow, hl, hneg, u2, u3]
      set u := exp (π * I / 12)
      have hu0 : u ≠ 0 := exp_ne_zero _
      rw [← hu6]
      field_simp
    have em : 2 * exp (-π * I / 6) * airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I)) =
        (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (π * I / 6) * z ^ (-1 / 4 : ℂ) *
          (exp (-(π * I / 4)) * exp ((Real.log 2 : ℂ) / 2) / 2 * exp (airyZetaComplex z * I)) := by
      simp only [airyPrefactor]
      rw [d2, d4, airyRot_two_div_pi_cpow, airyRot_exp_half_log_two, hneg, u2, um2, um3, neg_neg]
      set u := exp (π * I / 12)
      have hu0 : u ≠ 0 := exp_ne_zero _
      field_simp
      linear_combination -hs
    rw [ep, em]
    ring_nf
  · simp only [ofReal_neg, ofReal_one, neg_one_mul]
    rw [airyRot_airyBi_rot_neg z, split1, split2, sub_eq_add_neg, ← neg_mul, ← mul_assoc,
      ← mul_assoc, airyRot_decomp (fun w => airyAi w / airyPrefactor .ai w)]
    have ep : 2 * exp (π * I / 6) * airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I)) =
        (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (-(π * I / 6)) * z ^ (-1 / 4 : ℂ) *
          (exp (π * I / 4) * exp ((Real.log 2 : ℂ) / 2) / 2 *
            exp (-(airyZetaComplex z * I))) := by
      simp only [airyPrefactor]
      rw [d1, d3, airyRot_two_div_pi_cpow, airyRot_exp_half_log_two, hneg, u2, u3,
        show -(π * I / 6) = -π * I / 6 by ring, um2]
      set u := exp (π * I / 12)
      have hu0 : u ≠ 0 := exp_ne_zero _
      field_simp
      linear_combination -hs
    have em : -I * airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I)) =
        (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (-(π * I / 6)) * z ^ (-1 / 4 : ℂ) *
          (exp (-(π * I / 4)) * exp (-((Real.log 2 : ℂ) / 2)) / 2 *
            exp (airyZetaComplex z * I)) := by
      simp only [airyPrefactor]
      rw [d2, d4, airyRot_two_div_pi_cpow, hl, hneg, um3,
        show -(π * I / 6) = -π * I / 6 by ring, um2, neg_neg]
      set u := exp (π * I / 12)
      have hu0 : u ≠ 0 := exp_ne_zero _
      rw [← hu6]
      field_simp
      linear_combination -u12
    rw [ep, em]
    ring_nf

/-- `airyRotatedBiApprox false ε N M z` in the cosine/sine form used by `airyRot_osc_bound`. -/
private lemma airyRot_bi_approx_eq (ε : ℝ) (N M : ℕ) (z : ℂ) :
    airyRotatedBiApprox false ε N M z =
      (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (ε * (π * I / 6)) * z ^ (-1 / 4 : ℂ) *
        (((exp (π * I / 4) * exp (-((ε : ℂ) * Real.log 2 / 2)) / 2) *
              exp (-(airyZetaComplex z * I)) +
            (exp (-(π * I / 4)) * exp ((ε : ℂ) * Real.log 2 / 2) / 2) *
              exp (airyZetaComplex z * I)) * airyOscSum false 0 N z +
          I * ((exp (π * I / 4) * exp (-((ε : ℂ) * Real.log 2 / 2)) / 2) *
              exp (-(airyZetaComplex z * I)) -
            (exp (-(π * I / 4)) * exp ((ε : ℂ) * Real.log 2 / 2) / 2) *
              exp (airyZetaComplex z * I)) * airyOscSum false 1 M z) := by
  simp only [airyRotatedBiApprox, Bool.false_eq_true, ite_false, Complex.cos, Complex.sin]
  have e1 : exp ((airyZetaComplex z - π / 4 - ε * I * Real.log 2 / 2) * I) =
      exp (-(π * I / 4)) * exp ((ε : ℂ) * Real.log 2 / 2) * exp (airyZetaComplex z * I) := by
    rw [← exp_add, ← exp_add]; congr 1
    linear_combination (-(ε : ℂ) * Real.log 2 / 2) * I_sq
  have e2 : exp (-(airyZetaComplex z - π / 4 - ε * I * Real.log 2 / 2) * I) =
      exp (π * I / 4) * exp (-((ε : ℂ) * Real.log 2 / 2)) * exp (-(airyZetaComplex z * I)) := by
    rw [← exp_add, ← exp_add]; congr 1
    linear_combination ((ε : ℂ) * Real.log 2 / 2) * I_sq
  rw [e1, e2]
  ring

/-- The expansion of `Bi(z e^{±πi/3})` in `|arg z| ≤ 2π/3 - δ` by the rotated oscillatory
series `airyRotatedBiApprox` (DLMF 9.7.13). -/
@[dlmf 9.7.E13]
theorem airyBi_rotated_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (N M : ℕ) :
    IsBigO (airySector (2 * π / 3 - δ))
      (fun z => airyBi (z * exp (ε * (π * I / 3))) -
        airyRotatedBiApprox false ε N M z) (airyOscError .bi N M) := by
  obtain ⟨hE', hO'⟩ := airyRot_ai_parts hδ hδ' N M
  refine (airyRot_osc_bound (X := fun z => airyBi (z * exp (ε * (π * I / 3))))
    (Y := airyRotatedBiApprox false ε N M)
    (pref := fun z => (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (ε * (π * I / 6)) * z ^ (-1 / 4 : ℂ))
    (exp (π * I / 4) * exp (-((ε : ℂ) * Real.log 2 / 2)) / 2)
    (exp (-(π * I / 4)) * exp ((ε : ℂ) * Real.log 2 / 2) / 2) hE' hO' ?_ ?_).trans
    (airyRot_envelope .bi _ N M (airyRot_norm_rot_pref ε))
  · filter_upwards [airyRot_eventually_arg (2 * π / 3 - δ)] with z hz
    exact airyRot_bi_rot_eq hz.1 (hz.2.trans_lt (by linarith)) hε
  · exact Eventually.of_forall (airyRot_bi_approx_eq ε N M)

/-- Chain rule for `z ↦ f (z c)`: the derivative is `c f'(z c)`. -/
theorem airyRot_hasDerivAt_comp_mul {f f' : ℂ → ℂ} (hf : ∀ z, HasDerivAt f (f' z) z) (c z : ℂ) :
    HasDerivAt (fun z => f (z * c)) (c * f' (z * c)) z := by
  have := (hf (z * c)).comp z ((hasDerivAt_id' z).mul_const c)
  rw [show c * f' (z * c) = f' (z * c) * (1 * c) by ring]
  exact this

/-- `Bi'(z e^{iπ/3}) = i Ai'(z e^{iπ/3}) - 2 e^{iπ/6} Ai'(z e^{-iπ/3})`. -/
theorem airyRot_airyBiDeriv_rot_pos (z : ℂ) :
    airyBiDeriv (z * exp (π * I / 3)) = I * airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) +
      -2 * exp (π * I / 6) * airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) := by
  have h := airyRot_deriv_of_eq (airyRot_hasDerivAt_comp_mul hasDerivAt_airyBi (exp (π * I / 3)))
    hasDerivAt_airyAi _ _ _ _ airyRot_airyBi_rot_pos z
  obtain ⟨u4, um4, -, -, u2, um2, u12⟩ := airyRot_u_powers
  obtain ⟨k1, k2⟩ := airyRot_exp_third_ofReal
  have hu6 := airyRot_u_six
  rw [k1, k2] at h ⊢
  simp only [u4, um4, u2, um2] at h ⊢
  set u := exp (π * I / 12)
  set A := airyAiDeriv (z * u ^ 4)
  set B := airyAiDeriv (z * (u ^ 4)⁻¹)
  set X := airyBiDeriv (z * u ^ 4)
  have hu0 : u ≠ 0 := exp_ne_zero _
  apply mul_left_cancel₀ (pow_ne_zero 4 hu0)
  rw [h, ← hu6]
  field_simp
  linear_combination 2 * B * u12

/-- `Bi'(z e^{-iπ/3}) = -2 e^{-iπ/6} Ai'(z e^{iπ/3}) - i Ai'(z e^{-iπ/3})`. -/
theorem airyRot_airyBiDeriv_rot_neg (z : ℂ) :
    airyBiDeriv (z * exp (-(π * I / 3))) = -2 * exp (-π * I / 6) *
      airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) + -I * airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) := by
  have hc : ∀ z, airyBi (z * exp (-(π * I / 3))) = 2 * exp (π * I / 6) *
      airyAi (z * exp ((π / 3 : ℝ) * I)) + -I * airyAi (z * exp ((-(π / 3) : ℝ) * I)) := fun z => by
    rw [airyRot_airyBi_rot_neg]; ring
  have h := airyRot_deriv_of_eq
    (airyRot_hasDerivAt_comp_mul hasDerivAt_airyBi (exp (-(π * I / 3))))
    hasDerivAt_airyAi _ _ _ _ hc z
  obtain ⟨u4, um4, -, -, u2, um2, u12⟩ := airyRot_u_powers
  obtain ⟨k1, k2⟩ := airyRot_exp_third_ofReal
  have hu6 := airyRot_u_six
  have k3 : exp (-(π * I / 3)) = exp (-π * I / 3) := by congr 1; ring
  rw [k1, k2, k3] at h ⊢
  simp only [u4, um4, u2, um2] at h ⊢
  set u := exp (π * I / 12)
  set A := airyAiDeriv (z * u ^ 4)
  set B := airyAiDeriv (z * (u ^ 4)⁻¹)
  set X := airyBiDeriv (z * (u ^ 4)⁻¹)
  have hu0 : u ≠ 0 := exp_ne_zero _
  apply mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 4 hu0))
  rw [h, ← hu6]
  field_simp
  linear_combination 2 * A * u12

/-- At `z` with `|arg z| < 2π/3`, `Bi'(z e^{±iπ/3})` is the rotated prefactor times the
cosine/sine combination of the even and odd parts of the normalized `Ai'` (via 9.2.11). -/
private lemma airyRot_biDeriv_rot_eq {z : ℂ} (hz0 : z ≠ 0) (hz3 : |arg z| < 2 * π / 3) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) :
    airyBiDeriv (z * exp (ε * (π * I / 3))) =
      (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (-ε * (π * I / 6)) * z ^ (1 / 4 : ℂ) *
        (((exp (-(π * I / 4)) * exp (-((ε : ℂ) * Real.log 2 / 2)) / 2) *
              exp (-(airyZetaComplex z * I)) +
            (exp (π * I / 4) * exp ((ε : ℂ) * Real.log 2 / 2) / 2) *
              exp (airyZetaComplex z * I)) *
            airyRot_even (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w) z +
          I * ((exp (-(π * I / 4)) * exp (-((ε : ℂ) * Real.log 2 / 2)) / 2) *
              exp (-(airyZetaComplex z * I)) -
            (exp (π * I / 4) * exp ((ε : ℂ) * Real.log 2 / 2) / 2) *
              exp (airyZetaComplex z * I)) *
            airyRot_odd (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w) z) := by
  obtain ⟨u4, um4, u3, um3, u2, um2, u12⟩ := airyRot_u_powers
  have hu6 := airyRot_u_six
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hs0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hl : exp (-((Real.log 2 : ℂ) / 2)) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
    rw [exp_neg, airyRot_exp_half_log_two]
  obtain ⟨d1, d2, d3, d4⟩ := airyRot_third_data hz0 hz3
  have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
  have hp1 := airyRot_prefactor_ne_zero .aiDeriv
    (mul_ne_zero hz0 (exp_ne_zero ((π / 3 : ℝ) * I)))
  have hp2 := airyRot_prefactor_ne_zero .aiDeriv
    (mul_ne_zero hz0 (exp_ne_zero ((-(π / 3) : ℝ) * I)))
  have split1 : airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) =
      airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I)) *
      (airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) /
        airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I))) := by
    field_simp
  have split2 : airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) =
      airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I)) *
      (airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) /
        airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I))) := by field_simp
  rcases hε with rfl | rfl
  · simp only [ofReal_one, one_mul, neg_one_mul]
    rw [airyRot_airyBiDeriv_rot_pos z, split1, split2, ← mul_assoc, ← mul_assoc,
      airyRot_decomp (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w)]
    have ep : I * airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I)) =
        (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (-(π * I / 6)) * z ^ (1 / 4 : ℂ) *
          (exp (-(π * I / 4)) * exp (-((Real.log 2 : ℂ) / 2)) / 2 *
            exp (-(airyZetaComplex z * I))) := by
      simp only [airyPrefactor]
      rw [d1, d3, airyRot_two_div_pi_cpow, hl, show -(π * I / 6) = -π * I / 6 by ring,
        um2, um3]
      set u := exp (π * I / 12)
      have hu0 : u ≠ 0 := exp_ne_zero _
      rw [← hu6]
      field_simp
      linear_combination -u12
    have em : -2 * exp (π * I / 6) * airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I)) =
        (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (-(π * I / 6)) * z ^ (1 / 4 : ℂ) *
          (exp (π * I / 4) * exp ((Real.log 2 : ℂ) / 2) / 2 * exp (airyZetaComplex z * I)) := by
      simp only [airyPrefactor]
      rw [d2, d4, airyRot_two_div_pi_cpow, airyRot_exp_half_log_two,
        show -(π * I / 6) = -π * I / 6 by ring, u2, um2, u3, neg_neg]
      set u := exp (π * I / 12)
      have hu0 : u ≠ 0 := exp_ne_zero _
      field_simp
      linear_combination -hs
    rw [ep, em]
    ring_nf
  · simp only [ofReal_neg, ofReal_one, neg_one_mul, neg_neg, one_mul]
    rw [airyRot_airyBiDeriv_rot_neg z, split1, split2, ← mul_assoc,
      ← mul_assoc, airyRot_decomp (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w)]
    have ep : -2 * exp (-π * I / 6) * airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I)) =
        (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (π * I / 6) * z ^ (1 / 4 : ℂ) *
          (exp (-(π * I / 4)) * exp ((Real.log 2 : ℂ) / 2) / 2 *
            exp (-(airyZetaComplex z * I))) := by
      simp only [airyPrefactor]
      rw [d1, d3, airyRot_two_div_pi_cpow, airyRot_exp_half_log_two, u2, um2, um3]
      set u := exp (π * I / 12)
      have hu0 : u ≠ 0 := exp_ne_zero _
      field_simp
      linear_combination -hs
    have em : -I * airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I)) =
        (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (π * I / 6) * z ^ (1 / 4 : ℂ) *
          (exp (π * I / 4) * exp (-((Real.log 2 : ℂ) / 2)) / 2 *
            exp (airyZetaComplex z * I)) := by
      simp only [airyPrefactor]
      rw [d2, d4, airyRot_two_div_pi_cpow, hl, u3, u2, neg_neg]
      set u := exp (π * I / 12)
      have hu0 : u ≠ 0 := exp_ne_zero _
      rw [← hu6]
      field_simp
    rw [ep, em]
    ring_nf

/-- `airyRotatedBiApprox true ε N M z` in the cosine/sine form used by `airyRot_osc_bound`. -/
private lemma airyRot_biDeriv_approx_eq (ε : ℝ) (N M : ℕ) (z : ℂ) :
    airyRotatedBiApprox true ε N M z =
      (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (-ε * (π * I / 6)) * z ^ (1 / 4 : ℂ) *
        (((exp (-(π * I / 4)) * exp (-((ε : ℂ) * Real.log 2 / 2)) / 2) *
              exp (-(airyZetaComplex z * I)) +
            (exp (π * I / 4) * exp ((ε : ℂ) * Real.log 2 / 2) / 2) *
              exp (airyZetaComplex z * I)) * airyOscSum true 0 N z +
          I * ((exp (-(π * I / 4)) * exp (-((ε : ℂ) * Real.log 2 / 2)) / 2) *
              exp (-(airyZetaComplex z * I)) -
            (exp (π * I / 4) * exp ((ε : ℂ) * Real.log 2 / 2) / 2) *
              exp (airyZetaComplex z * I)) * airyOscSum true 1 M z) := by
  simp only [airyRotatedBiApprox, ↓reduceIte]
  rw [show cos (airyZetaComplex z - π / 4 - ε * I * Real.log 2 / 2) =
        sin (airyZetaComplex z - π / 4 - ε * I * Real.log 2 / 2 + π / 2) from
      (Complex.sin_add_pi_div_two _).symm,
    show sin (airyZetaComplex z - π / 4 - ε * I * Real.log 2 / 2) =
        -cos (airyZetaComplex z - π / 4 - ε * I * Real.log 2 / 2 + π / 2) by
      rw [Complex.cos_add_pi_div_two]; ring]
  simp only [Complex.cos, Complex.sin]
  have e1 : exp ((airyZetaComplex z - π / 4 - ε * I * Real.log 2 / 2 + π / 2) * I) =
      exp (π * I / 4) * exp ((ε : ℂ) * Real.log 2 / 2) * exp (airyZetaComplex z * I) := by
    rw [← exp_add, ← exp_add]; congr 1
    linear_combination (-(ε : ℂ) * Real.log 2 / 2) * I_sq
  have e2 : exp (-(airyZetaComplex z - π / 4 - ε * I * Real.log 2 / 2 + π / 2) * I) =
      exp (-(π * I / 4)) * exp (-((ε : ℂ) * Real.log 2 / 2)) *
        exp (-(airyZetaComplex z * I)) := by
    rw [← exp_add, ← exp_add]; congr 1
    linear_combination ((ε : ℂ) * Real.log 2 / 2) * I_sq
  rw [e1, e2]
  ring

/-- The expansion of `Bi'(z e^{±πi/3})` in `|arg z| ≤ 2π/3 - δ` by the rotated oscillatory
series `airyRotatedBiApprox` (DLMF 9.7.14). -/
@[dlmf 9.7.E14]
theorem airyBiDeriv_rotated_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (N M : ℕ) :
    IsBigO (airySector (2 * π / 3 - δ))
      (fun z => airyBiDeriv (z * exp (ε * (π * I / 3))) -
        airyRotatedBiApprox true ε N M z) (airyOscError .biDeriv N M) := by
  obtain ⟨hE', hO'⟩ := airyRot_aiDeriv_parts hδ hδ' N M
  refine (airyRot_osc_bound (X := fun z => airyBiDeriv (z * exp (ε * (π * I / 3))))
    (Y := airyRotatedBiApprox true ε N M)
    (pref := fun z => (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (-ε * (π * I / 6)) * z ^ (1 / 4 : ℂ))
    (exp (-(π * I / 4)) * exp (-((ε : ℂ) * Real.log 2 / 2)) / 2)
    (exp (π * I / 4) * exp ((ε : ℂ) * Real.log 2 / 2) / 2) hE' hO' ?_ ?_).trans
    (airyRot_envelope .biDeriv _ N M (airyRot_norm_rot_pref' ε))
  · filter_upwards [airyRot_eventually_arg (2 * π / 3 - δ)] with z hz
    exact airyRot_biDeriv_rot_eq hz.1 (hz.2.trans_lt (by linarith)) hε
  · exact Eventually.of_forall (airyRot_biDeriv_approx_eq ε N M)

/-- Eventually in `airySector α`, the Airy prefactor is nonzero. -/
theorem airyRot_eventually_prefactor_ne_zero (kind : AiryKind) (α : ℝ) :
    ∀ᶠ z in airySector α, airyPrefactor kind z ≠ 0 :=
  (airyRot_eventually_ne_zero α).mono fun _ hz => airyRot_prefactor_ne_zero kind hz

/-- `Ai(z) = e^{-ζ}/(2√π z^{1/4}) (∑_{k<N} (-1)^k u_k ζ^{-k} + O(ζ^{-N}))` in
`|arg z| ≤ π - δ` (DLMF 9.7.5). -/
@[dlmf 9.7.E5]
theorem airy_ai_poincare {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π) (N : ℕ) :
    IsBigO (airySector (π - δ)) (fun z => airyFunction .ai z -
      airyPrefactor .ai z * airyExponentialSum .ai N z)
      (fun z => airyPrefactor .ai z / airyZetaComplex z ^ N) :=
  airyRot_isBigO_of_expansion (airyRot_airyAi_expansion hδ hδ')
    (airyRot_eventually_prefactor_ne_zero .ai _) N

/-- `Ai'(z) = -z^{1/4} e^{-ζ}/(2√π) (∑_{k<N} (-1)^k v_k ζ^{-k} + O(ζ^{-N}))` in
`|arg z| ≤ π - δ` (DLMF 9.7.6). -/
@[dlmf 9.7.E6]
theorem airy_aiDeriv_poincare {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π) (N : ℕ) :
    IsBigO (airySector (π - δ)) (fun z => airyFunction .aiDeriv z -
      airyPrefactor .aiDeriv z * airyExponentialSum .aiDeriv N z)
      (fun z => airyPrefactor .aiDeriv z / airyZetaComplex z ^ N) :=
  airyRot_isBigO_of_expansion (airyRot_airyAiDeriv_expansion hδ hδ')
    (airyRot_eventually_prefactor_ne_zero .aiDeriv _) N

/-- `Bi(z) = e^{ζ}/(√π z^{1/4}) (∑_{k<N} u_k ζ^{-k} + O(ζ^{-N}))` in `|arg z| ≤ π/3 - δ`
(DLMF 9.7.7). -/
@[dlmf 9.7.E7]
theorem airy_bi_poincare {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π / 3) (N : ℕ) :
    IsBigO (airySector (π / 3 - δ)) (fun z => airyFunction .bi z -
      airyPrefactor .bi z * airyExponentialSum .bi N z)
      (fun z => airyPrefactor .bi z / airyZetaComplex z ^ N) :=
  airyRot_isBigO_of_expansion (airyRot_airyBi_expansion hδ hδ')
    (airyRot_eventually_prefactor_ne_zero .bi _) N

/-- `Bi'(z) = z^{1/4} e^{ζ}/√π (∑_{k<N} v_k ζ^{-k} + O(ζ^{-N}))` in `|arg z| ≤ π/3 - δ`
(DLMF 9.7.8). -/
@[dlmf 9.7.E8]
theorem airy_biDeriv_poincare {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π / 3) (N : ℕ) :
    IsBigO (airySector (π / 3 - δ)) (fun z => airyFunction .biDeriv z -
      airyPrefactor .biDeriv z * airyExponentialSum .biDeriv N z)
      (fun z => airyPrefactor .biDeriv z / airyZetaComplex z ^ N) :=
  airyRot_isBigO_of_expansion (airyRot_airyBiDeriv_expansion hδ hδ')
    (airyRot_eventually_prefactor_ne_zero .biDeriv _) N

end DLMF.Airy
end
