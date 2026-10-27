/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Asymptotics

/-!
# Uniform Airy bounds and numerically satisfactory pairs

Tools behind DLMF Table 9.2.1 (numerically satisfactory pairs of Airy solutions).

* `airyErr_bound_of_isBigO`: a big-O relation on `airySector α` with an explicit radius.
* `airyErr_wellConditioned_of_far`: for a pair with constant nonzero Wronskian it suffices to
  bound `|f g'| + |f' g|` outside a ball (compactness handles the rest).
* `airyErr_ai_uniform`: `|Ai w| ≤ C |e^{-ζ}| |w|^{-1/4}` and `|Ai' w| ≤ C |e^{-ζ}| |w|^{1/4}`
  uniformly in the closed plane `|arg w| ≤ π` for large `|w|`, including the negative axis,
  from the Poincaré expansions 9.7.5–9.7.6 and the oscillatory expansions 9.7.9–9.7.10.
* `airyErr_cross_le`: cross products `|Ai w₁| |Ai' w₂|` are bounded when `|w₁| = |w₂|` and
  `re ζ(w₁) + re ζ(w₂) ≥ 0`.
* `airyErr_far_real`, `airyErr_far_sector`: boundedness of `|Ai Bi'| + |Ai' Bi|` on the real line
  and in the closed sector `|arg z| ≤ π/3`.

The pairs themselves are proved in `DLMF.Airy.Equation`.
-/

@[expose] public noncomputable section
open Complex Filter Set Asymptotics
open scoped Real Topology
namespace DLMF.Airy

/-- A big-O relation on `airySector α` gives an explicit radius beyond which the bound holds. -/
theorem airyErr_bound_of_isBigO {α : ℝ} {E F : Type*} [Norm E] [SeminormedAddCommGroup F] {f : ℂ → E} {g : ℂ → F}
    (h : f =O[airySector α] g) :
    ∃ C R : ℝ, 0 ≤ C ∧ ∀ z : ℂ, R ≤ ‖z‖ → z ≠ 0 → |arg z| ≤ α → ‖f z‖ ≤ C * ‖g z‖ := by
  obtain ⟨C, hC0, hC⟩ := h.exists_nonneg
  have hb := hC.bound
  unfold airySector at hb
  rw [Filter.Eventually, Filter.mem_inf_principal] at hb
  obtain ⟨t, ht, hsub⟩ := Filter.mem_comap.1 hb
  obtain ⟨R, hR⟩ := Filter.mem_atTop_sets.1 ht
  exact ⟨C, R, hC0, fun z hz hz0 harg => hsub (hR _ hz) ⟨hz0, harg⟩⟩

/-- A pair with constant nonzero Wronskian is well conditioned on `s` as soon as the
products `|f g'| + |f' g|` are bounded on the part of `s` outside some ball. -/
theorem airyErr_wellConditioned_of_far {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hf' : Continuous (deriv f)) (hg' : Continuous (deriv g)) {W : ℂ} (hW : W ≠ 0)
    (hWr : ∀ z, f z * deriv g z - deriv f z * g z = W) {s : Set ℂ} {R B : ℝ}
    (hfar : ∀ z ∈ s, R ≤ ‖z‖ → ‖f z‖ * ‖deriv g z‖ + ‖deriv f z‖ * ‖g z‖ ≤ B) :
    IsWellConditionedPairOn f g s := by
  have hc : Continuous fun z => ‖f z‖ * ‖deriv g z‖ + ‖deriv f z‖ * ‖g z‖ := by fun_prop
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hc.continuousOn
  have hW' : 0 < ‖W‖ := norm_pos_iff.2 hW
  set K : ℝ := max (max B M) 0 + 1
  have hK : 0 < K := by positivity
  refine ⟨K / ‖W‖, by positivity, fun z hz => ?_⟩
  rw [hWr z, div_mul_cancel₀ _ hW'.ne']
  have h1 := le_max_left B M
  have h2 := le_max_right B M
  have h3 := le_max_left (max B M) 0
  by_cases hzR : R ≤ ‖z‖
  · have := hfar z hz hzR
    linarith
  · have hz' : z ∈ Metric.closedBall (0 : ℂ) R := by
      rw [Metric.mem_closedBall, dist_zero_right]; linarith
    have := hM z hz'
    rw [Real.norm_of_nonneg (by positivity)] at this
    linarith

/-- The `Ai` and `Bi'` prefactors of 9.7.5 and 9.7.8 multiply to `1/(2π)`. -/
theorem airyErr_pref_ai_mul_biDeriv {z : ℂ} (hz : z ≠ 0) :
    airyPrefactor .ai z * airyPrefactor .biDeriv z = 1 / (2 * π) := by
  have hπs : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz)
  have hs : (Real.sqrt π : ℂ) ^ 2 = π := by
    rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have he := airyRot_exp_mul_exp_neg (airyZetaComplex z)
  simp only [airyPrefactor]
  field_simp
  linear_combination (π : ℂ) * he - hs

/-- The `Ai'` and `Bi` prefactors of 9.7.6 and 9.7.7 multiply to `-1/(2π)`. -/
theorem airyErr_pref_aiDeriv_mul_bi {z : ℂ} (hz : z ≠ 0) :
    airyPrefactor .aiDeriv z * airyPrefactor .bi z = -1 / (2 * π) := by
  have hπs : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz)
  have hs : (Real.sqrt π : ℂ) ^ 2 = π := by
    rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have he := airyRot_exp_mul_exp_neg (airyZetaComplex z)
  simp only [airyPrefactor]
  field_simp
  linear_combination -(π : ℂ) * he + hs

/-- The oscillatory `Ai` and `Bi'` prefactors multiply to `1/π`. -/
theorem airyErr_oscPref_ai_mul_biDeriv {z : ℂ} (hz : z ≠ 0) :
    airyOscPrefactor .ai z * airyOscPrefactor .biDeriv z = 1 / π := by
  have hπs : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz)
  have hs : (Real.sqrt π : ℂ) ^ 2 = π := by
    rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  simp only [airyOscPrefactor]
  field_simp
  linear_combination -hs

/-- The oscillatory `Ai'` and `Bi` prefactors multiply to `1/π`. -/
theorem airyErr_oscPref_aiDeriv_mul_bi {z : ℂ} (hz : z ≠ 0) :
    airyOscPrefactor .aiDeriv z * airyOscPrefactor .bi z = 1 / π := by
  have hπs : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz)
  have hs : (Real.sqrt π : ℂ) ^ 2 = π := by
    rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  simp only [airyOscPrefactor]
  field_simp
  linear_combination -hs

/-- `ζ(x) ≥ 1` for `x ≥ 2`. -/
theorem airyErr_one_le_zeta {x : ℝ} (hx : 2 ≤ x) : 1 ≤ airyZeta x := by
  have h1 : x ^ (1 : ℝ) ≤ x ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  rw [Real.rpow_one] at h1
  unfold airyZeta
  linarith

/-- On the positive axis the zeroth oscillatory envelope is at most twice the prefactor. -/
theorem airyErr_oscError_le (kind : AiryKind) {x : ℝ} (hx : 2 ≤ x) :
    ‖airyOscError kind 0 0 x‖ ≤ 2 * ‖airyOscPrefactor kind x‖ := by
  have hx0 : 0 < x := by linarith
  have hz := airyErr_one_le_zeta hx
  unfold airyOscError
  have hzn : ‖((airyZeta x : ℝ) : ℂ)‖ = airyZeta x := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  rw [airyReal_zeta_ofReal hx0, ofReal_im, abs_zero, Real.exp_zero, mul_one, hzn]
  have he : airyZeta x ^ (-(2 * ((0 : ℕ) : ℤ))) + airyZeta x ^ (-(2 * ((0 : ℕ) : ℤ) + 1)) ≤ 2 := by
    simp only [Nat.cast_zero, mul_zero, neg_zero, zpow_zero, zero_add, zpow_neg_one]
    have hi : (airyZeta x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hz
    linarith
  have hp : 0 ≤ airyZeta x ^ (-(2 * ((0 : ℕ) : ℤ))) + airyZeta x ^ (-(2 * ((0 : ℕ) : ℤ) + 1)) := by
    have : 0 < airyZeta x := by linarith
    positivity
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hp)]
  nlinarith [norm_nonneg (airyOscPrefactor kind x)]

/-- Elementary data of a positive real point. -/
theorem airyErr_ofReal_data {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ≠ 0 ∧ ‖(x : ℂ)‖ = x ∧ arg (x : ℂ) = 0 :=
  ⟨ofReal_ne_zero.mpr hx.ne', by rw [Complex.norm_real, Real.norm_of_nonneg hx.le],
    Complex.arg_ofReal_of_nonneg hx.le⟩

/-- The Airy products `|Ai Bi'| + |Ai' Bi|` stay bounded as `x → +∞`. -/
theorem airyErr_far_pos : ∃ R B : ℝ, ∀ x : ℝ, R ≤ x →
    ‖airyAi x‖ * ‖airyBiDeriv x‖ + ‖airyAiDeriv x‖ * ‖airyBi x‖ ≤ B := by
  have hπ := Real.pi_pos
  have h1 := airy_ai_poincare (δ := π / 2) (by positivity) (by linarith) 0
  have h2 := airy_aiDeriv_poincare (δ := π / 2) (by positivity) (by linarith) 0
  have h3 := airy_bi_poincare (δ := π / 6) (by positivity) (by linarith) 0
  have h4 := airy_biDeriv_poincare (δ := π / 6) (by positivity) (by linarith) 0
  simp only [airyExponentialSum, Finset.range_zero, Finset.sum_empty, mul_zero, sub_zero,
    pow_zero, div_one, airyFunction] at h1 h2 h3 h4
  obtain ⟨C1, R1, hC1, hb1⟩ := airyErr_bound_of_isBigO h1
  obtain ⟨C2, R2, hC2, hb2⟩ := airyErr_bound_of_isBigO h2
  obtain ⟨C3, R3, hC3, hb3⟩ := airyErr_bound_of_isBigO h3
  obtain ⟨C4, R4, hC4, hb4⟩ := airyErr_bound_of_isBigO h4
  refine ⟨max (max R1 R2) (max (max R3 R4) 1), C1 * C4 * (1 / (2 * π)) + C2 * C3 * (1 / (2 * π)),
    fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨hz0, hzn, hza⟩ := airyErr_ofReal_data (by linarith : 0 < x)
  have hR : ∀ R, (R = R1 ∨ R = R2 ∨ R = R3 ∨ R = R4) → R ≤ ‖(x : ℂ)‖ := by
    intro R hR
    rw [hzn]
    rcases hR with rfl | rfl | rfl | rfl
    · exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
    · exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
    · exact le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hx
    · exact le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hx
  have ha : |arg (x : ℂ)| ≤ π - π / 2 := by rw [hza, abs_zero]; linarith
  have hb : |arg (x : ℂ)| ≤ π / 3 - π / 6 := by rw [hza, abs_zero]; linarith
  have e1 := hb1 x (hR _ (by tauto)) hz0 ha
  have e2 := hb2 x (hR _ (by tauto)) hz0 ha
  have e3 := hb3 x (hR _ (by tauto)) hz0 hb
  have e4 := hb4 x (hR _ (by tauto)) hz0 hb
  have p1 : ‖airyPrefactor .ai x‖ * ‖airyPrefactor .biDeriv x‖ = 1 / (2 * π) := by
    rw [← norm_mul, airyErr_pref_ai_mul_biDeriv hz0, norm_div, norm_one, norm_mul,
      Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg hπ.le]
  have p2 : ‖airyPrefactor .aiDeriv x‖ * ‖airyPrefactor .bi x‖ = 1 / (2 * π) := by
    rw [← norm_mul, airyErr_pref_aiDeriv_mul_bi hz0, norm_div, norm_neg, norm_one, norm_mul,
      Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg hπ.le]
  calc ‖airyAi x‖ * ‖airyBiDeriv x‖ + ‖airyAiDeriv x‖ * ‖airyBi x‖
      ≤ (C1 * ‖airyPrefactor .ai x‖) * (C4 * ‖airyPrefactor .biDeriv x‖) +
        (C2 * ‖airyPrefactor .aiDeriv x‖) * (C3 * ‖airyPrefactor .bi x‖) := by
        gcongr
    _ = C1 * C4 * (‖airyPrefactor .ai x‖ * ‖airyPrefactor .biDeriv x‖) +
        C2 * C3 * (‖airyPrefactor .aiDeriv x‖ * ‖airyPrefactor .bi x‖) := by ring
    _ = _ := by rw [p1, p2]

/-- The Airy products `|Ai Bi'| + |Ai' Bi|` stay bounded as `x → -∞`. -/
theorem airyErr_far_neg : ∃ R B : ℝ, ∀ x : ℝ, R ≤ x →
    ‖airyAi (-x)‖ * ‖airyBiDeriv (-x)‖ + ‖airyAiDeriv (-x)‖ * ‖airyBi (-x)‖ ≤ B := by
  have hπ := Real.pi_pos
  have h1 := airy_ai_oscillatory_expansion (δ := π / 3) (by positivity) (by linarith) 0 0
  have h2 := airy_aiDeriv_oscillatory_expansion (δ := π / 3) (by positivity) (by linarith) 0 0
  have h3 := airy_bi_oscillatory_expansion (δ := π / 3) (by positivity) (by linarith) 0 0
  have h4 := airy_biDeriv_oscillatory_expansion (δ := π / 3) (by positivity) (by linarith) 0 0
  simp only [airyOscApprox, airyOscSum, Finset.range_zero, Finset.sum_empty, mul_zero,
    add_zero, sub_zero, neg_mul, neg_zero, airyFunction] at h1 h2 h3 h4
  obtain ⟨C1, R1, hC1, hb1⟩ := airyErr_bound_of_isBigO h1
  obtain ⟨C2, R2, hC2, hb2⟩ := airyErr_bound_of_isBigO h2
  obtain ⟨C3, R3, hC3, hb3⟩ := airyErr_bound_of_isBigO h3
  obtain ⟨C4, R4, hC4, hb4⟩ := airyErr_bound_of_isBigO h4
  refine ⟨max (max R1 R2) (max (max R3 R4) 2), 4 * (C1 * C4 * (1 / π) + C2 * C3 * (1 / π)),
    fun x hx => ?_⟩
  have hx2 : 2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨hz0, hzn, hza⟩ := airyErr_ofReal_data (by linarith : 0 < x)
  have hR : ∀ R, (R = R1 ∨ R = R2 ∨ R = R3 ∨ R = R4) → R ≤ ‖(x : ℂ)‖ := by
    intro R hR
    rw [hzn]
    rcases hR with rfl | rfl | rfl | rfl
    · exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
    · exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
    · exact le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hx
    · exact le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hx
  have ha : |arg (x : ℂ)| ≤ 2 * π / 3 - π / 3 := by rw [hza, abs_zero]; linarith
  have e1 := (hb1 x (hR _ (by tauto)) hz0 ha).trans
    (mul_le_mul_of_nonneg_left (airyErr_oscError_le .ai hx2) hC1)
  have e2 := (hb2 x (hR _ (by tauto)) hz0 ha).trans
    (mul_le_mul_of_nonneg_left (airyErr_oscError_le .aiDeriv hx2) hC2)
  have e3 := (hb3 x (hR _ (by tauto)) hz0 ha).trans
    (mul_le_mul_of_nonneg_left (airyErr_oscError_le .bi hx2) hC3)
  have e4 := (hb4 x (hR _ (by tauto)) hz0 ha).trans
    (mul_le_mul_of_nonneg_left (airyErr_oscError_le .biDeriv hx2) hC4)
  have p1 : ‖airyOscPrefactor .ai x‖ * ‖airyOscPrefactor .biDeriv x‖ = 1 / π := by
    rw [← norm_mul, airyErr_oscPref_ai_mul_biDeriv hz0, norm_div, norm_one,
      Complex.norm_real, Real.norm_of_nonneg hπ.le]
  have p2 : ‖airyOscPrefactor .aiDeriv x‖ * ‖airyOscPrefactor .bi x‖ = 1 / π := by
    rw [← norm_mul, airyErr_oscPref_aiDeriv_mul_bi hz0, norm_div, norm_one,
      Complex.norm_real, Real.norm_of_nonneg hπ.le]
  have hneg : -((x : ℝ) : ℂ) = ((-x : ℝ) : ℂ) := by push_cast; ring
  rw [hneg] at e1 e2 e3 e4 ⊢
  calc ‖airyAi ((-x : ℝ) : ℂ)‖ * ‖airyBiDeriv ((-x : ℝ) : ℂ)‖ +
        ‖airyAiDeriv ((-x : ℝ) : ℂ)‖ * ‖airyBi ((-x : ℝ) : ℂ)‖
      ≤ (C1 * (2 * ‖airyOscPrefactor .ai x‖)) * (C4 * (2 * ‖airyOscPrefactor .biDeriv x‖)) +
        (C2 * (2 * ‖airyOscPrefactor .aiDeriv x‖)) * (C3 * (2 * ‖airyOscPrefactor .bi x‖)) := by
        gcongr
    _ = 4 * (C1 * C4 * (‖airyOscPrefactor .ai x‖ * ‖airyOscPrefactor .biDeriv x‖) +
        C2 * C3 * (‖airyOscPrefactor .aiDeriv x‖ * ‖airyOscPrefactor .bi x‖)) := by ring
    _ = _ := by rw [p1, p2]

/-- The products `|Ai Bi'| + |Ai' Bi|` are bounded on the real line, away from a ball. -/
theorem airyErr_far_real : ∃ R B : ℝ, ∀ z : ℂ, z.im = 0 → R ≤ ‖z‖ →
    ‖airyAi z‖ * ‖airyBiDeriv z‖ + ‖airyAiDeriv z‖ * ‖airyBi z‖ ≤ B := by
  obtain ⟨R1, B1, h1⟩ := airyErr_far_pos
  obtain ⟨R2, B2, h2⟩ := airyErr_far_neg
  refine ⟨max R1 R2, max B1 B2, fun z hz hR => ?_⟩
  have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz])
  have hn : ‖z‖ = |z.re| := by rw [hzr, Complex.norm_real, Real.norm_eq_abs]; simp
  rcases le_or_gt 0 z.re with h | h
  · rw [hn, abs_of_nonneg h] at hR
    rw [hzr]
    exact (h1 _ ((le_max_left _ _).trans hR)).trans (le_max_left _ _)
  · rw [hn, abs_of_neg h] at hR
    have hz' : z = -(((-z.re : ℝ)) : ℂ) := by rw [ofReal_neg, neg_neg]; exact hzr
    rw [hz']
    exact (h2 _ ((le_max_right _ _).trans hR)).trans (le_max_right _ _)

/-- `|w^{1/4}| = |w|^{1/4}`. -/
theorem airyErr_norm_quarter (w : ℂ) : ‖w ^ (1 / 4 : ℂ)‖ = ‖w‖ ^ (1 / 4 : ℝ) := by
  rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by push_cast; ring, norm_cpow_real]

/-- The norm of the `Ai` prefactor. -/
theorem airyErr_norm_pref_ai (w : ℂ) :
    ‖airyPrefactor .ai w‖ = ‖exp (-airyZetaComplex w)‖ / (2 * Real.sqrt π * ‖w‖ ^ (1 / 4 : ℝ)) := by
  rw [airyPrefactor, norm_div, norm_mul, norm_mul, airyErr_norm_quarter, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]

/-- The norm of the `Ai'` prefactor. -/
theorem airyErr_norm_pref_aiDeriv (w : ℂ) :
    ‖airyPrefactor .aiDeriv w‖ = ‖w‖ ^ (1 / 4 : ℝ) * ‖exp (-airyZetaComplex w)‖ / (2 * Real.sqrt π) := by
  rw [airyPrefactor, norm_div, norm_mul, norm_neg, norm_mul, airyErr_norm_quarter,
    Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]

/-- `re ζ ≥ 0` in the closed sector `|arg z| ≤ π/3`. -/
theorem airyErr_re_zeta_nonneg {z : ℂ} (hz : z ≠ 0) (harg : |arg z| ≤ π / 3) :
    0 ≤ (airyZetaComplex z).re := by
  have hπ := Real.pi_pos
  have h := airyRot_re_W z 0
  rw [← airyRot_two_zeta_mul_exp hz 0, ofReal_zero, zero_mul, exp_zero, mul_one, add_zero] at h
  have hc : 0 ≤ Real.cos (3 / 2 * arg z) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [(abs_le.mp harg).1], by linarith [(abs_le.mp harg).2]⟩
  have : 0 ≤ (2 * airyZetaComplex z).re := by rw [h]; positivity
  simpa using this

/-- `|e^{-ζ}| ≤ 1` in the closed sector `|arg z| ≤ π/3`. -/
theorem airyErr_norm_exp_neg_zeta_le {z : ℂ} (hz : z ≠ 0) (harg : |arg z| ≤ π / 3) :
    ‖exp (-airyZetaComplex z)‖ ≤ 1 := by
  rw [Complex.norm_exp, neg_re, Real.exp_le_one_iff, neg_nonpos]
  exact airyErr_re_zeta_nonneg hz harg

/-- Bounds for `Bi`, `Bi'` from a rotation identity `Ai(zc) = a (Ai z + b Bi z)`. -/
theorem airyErr_bi_le_of_rot {a b c : ℂ} (ha : ‖a‖ = 1 / 2) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (h : ∀ z, airyAi (z * c) = a * (airyAi z + b * airyBi z)) (z : ℂ) :
    ‖airyBi z‖ ≤ 2 * ‖airyAi (z * c)‖ + ‖airyAi z‖ ∧
      ‖airyBiDeriv z‖ ≤ 2 * ‖airyAiDeriv (z * c)‖ + ‖airyAiDeriv z‖ := by
  have ha0 : a ≠ 0 := by intro h0; rw [h0, norm_zero] at ha; norm_num at ha
  have hb0 : b ≠ 0 := by intro h0; rw [h0, norm_zero] at hb; norm_num at hb
  have hd : c * airyAiDeriv (z * c) = a * (airyAiDeriv z + b * airyBiDeriv z) := by
    have h1 : HasDerivAt (fun z => airyAi (z * c)) (airyAiDeriv (z * c) * c) z := by
      exact (hasDerivAt_airyAi (z * c)).comp z (hasDerivAt_mul_const c)
    have h2 : HasDerivAt (fun z => a * (airyAi z + b * airyBi z))
        (a * (airyAiDeriv z + b * airyBiDeriv z)) z :=
      ((hasDerivAt_airyAi z).add ((hasDerivAt_airyBi z).const_mul b)).const_mul a
    rw [funext h] at h1
    rw [mul_comm]; exact h1.unique h2
  have e1 : airyBi z = (airyAi (z * c) / a - airyAi z) / b := by
    rw [h]; field_simp; ring
  have e2 : airyBiDeriv z = (c * airyAiDeriv (z * c) / a - airyAiDeriv z) / b := by
    rw [hd]; field_simp; ring
  constructor
  · rw [e1, norm_div, hb, div_one]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_div, ha]; linarith [show ‖airyAi (z * c)‖ / (1 / 2) = 2 * ‖airyAi (z * c)‖ by ring]
  · rw [e2, norm_div, hb, div_one]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_div, norm_mul, ha, hc]
    linarith [show 1 * ‖airyAiDeriv (z * c)‖ / (1 / 2) = 2 * ‖airyAiDeriv (z * c)‖ by ring]

/-- `|e^{iθ}| = 1`. -/
theorem airyErr_norm_exp_I (θ : ℝ) : ‖exp ((θ : ℂ) * I)‖ = 1 := norm_exp_ofReal_mul_I θ

/-- The rotation identities 9.2.11 in the form `Ai(z c) = a (Ai z + b Bi z)`. -/
theorem airyErr_rot_identity {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ a b : ℂ, ‖a‖ = 1 / 2 ∧ ‖b‖ = 1 ∧ ∀ w, airyAi (w * exp (((ε * (2 * π / 3)) : ℝ) * I)) =
      a * (airyAi w + b * airyBi w) := by
  rcases hε with rfl | rfl
  · refine ⟨1 / 2 * exp (((π / 3 : ℝ) : ℂ) * I), -I, ?_, by simp, fun w => ?_⟩
    · rw [norm_mul, airyErr_norm_exp_I]; norm_num
    · rw [show (((1 * (2 * π / 3)) : ℝ) : ℂ) * I = 2 * π * I / 3 by push_cast; ring,
        airyAi_mul_omega, show (((π / 3 : ℝ) : ℂ) * I) = π * I / 3 by push_cast; ring]
      ring
  · refine ⟨1 / 2 * exp (((-(π / 3) : ℝ) : ℂ) * I), I, ?_, by simp, fun w => ?_⟩
    · rw [norm_mul, airyErr_norm_exp_I]; norm_num
    · rw [show ((((-1) * (2 * π / 3)) : ℝ) : ℂ) * I = -(2 * π * I / 3) by push_cast; ring,
        airyAi_mul_omega_recip, show ((((-(π / 3)) : ℝ) : ℂ) * I) = -(π * I / 3) by push_cast; ring]

/-- The products `|Ai Bi'| + |Ai' Bi|` stay bounded in the closed sector `|arg z| ≤ π/3`. -/
theorem airyErr_far_sector : ∃ R B : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → z ≠ 0 → |arg z| ≤ π / 3 →
    ‖airyAi z‖ * ‖airyBiDeriv z‖ + ‖airyAiDeriv z‖ * ‖airyBi z‖ ≤ B := by
  have hπ := Real.pi_pos
  have h1 := airy_ai_poincare (δ := π / 3) (by positivity) (by linarith) 0
  have h2 := airy_aiDeriv_poincare (δ := π / 3) (by positivity) (by linarith) 0
  simp only [airyExponentialSum, Finset.range_zero, Finset.sum_empty, mul_zero, sub_zero,
    pow_zero, div_one, airyFunction] at h1 h2
  obtain ⟨C1, R1, hC1, hb1⟩ := airyErr_bound_of_isBigO h1
  obtain ⟨C2, R2, hC2, hb2⟩ := airyErr_bound_of_isBigO h2
  refine ⟨max R1 R2, C1 * C2 * (6 / (4 * π)), fun z hR hz0 harg => ?_⟩
  have hR1 : R1 ≤ ‖z‖ := (le_max_left _ _).trans hR
  have hR2 : R2 ≤ ‖z‖ := (le_max_right _ _).trans hR
  obtain ⟨ε, hε, hlo, hhi, hsec⟩ : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ -π < arg z + ε * (2 * π / 3) ∧
      arg z + ε * (2 * π / 3) ≤ π ∧ |arg z + ε * (2 * π / 3)| ≤ π - π / 3 := by
    have := abs_le.mp harg
    rcases le_or_gt 0 (arg z) with h | h
    · exact ⟨-1, Or.inr rfl, by linarith, by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩
    · exact ⟨1, Or.inl rfl, by linarith, by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  set c := exp (((ε * (2 * π / 3)) : ℝ) * I)
  obtain ⟨a, b, ha, hb, hrot⟩ := airyErr_rot_identity hε
  have hc : ‖c‖ = 1 := airyErr_norm_exp_I _
  obtain ⟨hBi, hBi'⟩ := airyErr_bi_le_of_rot ha hb hc hrot z
  have hzc0 : z * c ≠ 0 := mul_ne_zero hz0 (exp_ne_zero _)
  have hzcn : ‖z * c‖ = ‖z‖ := by rw [norm_mul, hc, mul_one]
  have hzca : |arg (z * c)| ≤ π - π / 3 := by rw [airyRot_arg_mul_exp hz0 hlo hhi]; exact hsec
  have hzeta : airyZetaComplex (z * c) = -airyZetaComplex z := by
    rw [airyRot_zeta_mul_exp hz0 hlo hhi, airyRot_exp_rot_three_halves hε, mul_neg_one]
  have ha1 : |arg z| ≤ π - π / 3 := harg.trans (by linarith)
  have e1 := hb1 z hR1 hz0 ha1
  have e2 := hb2 z hR2 hz0 ha1
  have e3 := hb1 (z * c) (by rw [hzcn]; exact hR1) hzc0 hzca
  have e4 := hb2 (z * c) (by rw [hzcn]; exact hR2) hzc0 hzca
  -- explicit prefactor products
  set E := ‖exp (-airyZetaComplex z)‖
  set F := ‖exp (airyZetaComplex z)‖
  set q := ‖z‖ ^ (1 / 4 : ℝ)
  set sπ := Real.sqrt π
  have hEF : E * F = 1 := by
    simp only [E, F]; rw [← norm_mul, ← exp_add, neg_add_cancel, exp_zero, norm_one]
  have hE1 : E ≤ 1 := airyErr_norm_exp_neg_zeta_le hz0 harg
  have hE0 : 0 ≤ E := norm_nonneg _
  have hq : 0 < q := Real.rpow_pos_of_pos (norm_pos_iff.mpr hz0) _
  have hs : 0 < sπ := Real.sqrt_pos.mpr hπ
  have hs2 : sπ ^ 2 = π := Real.sq_sqrt hπ.le
  have pa : ‖airyPrefactor .ai z‖ = E / (2 * sπ * q) := airyErr_norm_pref_ai z
  have pd : ‖airyPrefactor .aiDeriv z‖ = q * E / (2 * sπ) := airyErr_norm_pref_aiDeriv z
  have pa' : ‖airyPrefactor .ai (z * c)‖ = F / (2 * sπ * q) := by
    rw [airyErr_norm_pref_ai, hzeta, neg_neg, hzcn]
  have pd' : ‖airyPrefactor .aiDeriv (z * c)‖ = q * F / (2 * sπ) := by
    rw [airyErr_norm_pref_aiDeriv, hzeta, neg_neg, hzcn]
  have k1 : ‖airyPrefactor .ai z‖ * ‖airyPrefactor .aiDeriv (z * c)‖ = 1 / (4 * π) := by
    rw [pa, pd', ← hs2]; field_simp; linear_combination 4 * hEF
  have k2 : ‖airyPrefactor .aiDeriv z‖ * ‖airyPrefactor .ai (z * c)‖ = 1 / (4 * π) := by
    rw [pd, pa', ← hs2]; field_simp; linear_combination 4 * hEF
  have k3 : ‖airyPrefactor .ai z‖ * ‖airyPrefactor .aiDeriv z‖ ≤ 1 / (4 * π) := by
    rw [pa, pd, ← hs2, show E / (2 * sπ * q) * (q * E / (2 * sπ)) = E * E / (4 * sπ ^ 2) by
      field_simp; ring]
    gcongr
    nlinarith
  calc ‖airyAi z‖ * ‖airyBiDeriv z‖ + ‖airyAiDeriv z‖ * ‖airyBi z‖
      ≤ ‖airyAi z‖ * (2 * ‖airyAiDeriv (z * c)‖ + ‖airyAiDeriv z‖) +
        ‖airyAiDeriv z‖ * (2 * ‖airyAi (z * c)‖ + ‖airyAi z‖) := by gcongr
    _ ≤ (C1 * ‖airyPrefactor .ai z‖) * (2 * (C2 * ‖airyPrefactor .aiDeriv (z * c)‖) +
          C2 * ‖airyPrefactor .aiDeriv z‖) +
        (C2 * ‖airyPrefactor .aiDeriv z‖) * (2 * (C1 * ‖airyPrefactor .ai (z * c)‖) +
          C1 * ‖airyPrefactor .ai z‖) := by gcongr
    _ = C1 * C2 * (2 * (‖airyPrefactor .ai z‖ * ‖airyPrefactor .aiDeriv (z * c)‖) +
          2 * (‖airyPrefactor .aiDeriv z‖ * ‖airyPrefactor .ai (z * c)‖) +
          2 * (‖airyPrefactor .ai z‖ * ‖airyPrefactor .aiDeriv z‖)) := by ring
    _ ≤ C1 * C2 * (2 * (1 / (4 * π)) + 2 * (1 / (4 * π)) + 2 * (1 / (4 * π))) := by
        rw [k1, k2]; gcongr
    _ = _ := by ring

/-- The imaginary part of `2ζ`. -/
theorem airyErr_im_two_zeta {z : ℂ} (hz : z ≠ 0) :
    (2 * airyZetaComplex z).im = Real.exp (log 2 + airyLogZeta z).re * Real.sin (3 / 2 * arg z) := by
  rw [← exp_log_two_add_airyLogZeta hz, Complex.exp_im, im_log_two_add_airyLogZeta]

/-- `|ζ(z)| = (2/3)|z|^{3/2}`. -/
theorem airyErr_norm_zeta (z : ℂ) : ‖airyZetaComplex z‖ = 2 / 3 * ‖z‖ ^ (3 / 2 : ℝ) := by
  have h := airyRot_norm_two_zeta z
  rw [norm_mul, Complex.norm_ofNat] at h
  linarith

/-- `|ζ(z)| ≥ 1` for `|z| ≥ 2`. -/
theorem airyErr_one_le_norm_zeta {z : ℂ} (hz : 2 ≤ ‖z‖) : 1 ≤ ‖airyZetaComplex z‖ := by
  have h1 : ‖z‖ ^ (1 : ℝ) ≤ ‖z‖ ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  rw [Real.rpow_one] at h1
  rw [airyErr_norm_zeta]
  linarith

/-- For `|u| ≥ 2` the zeroth oscillatory envelope is at most `2 |prefactor| e^{|im ζ|}`. -/
theorem airyErr_oscError_le' (kind : AiryKind) {u : ℂ} (hu : 2 ≤ ‖u‖) :
    ‖airyOscError kind 0 0 u‖ ≤
      2 * ‖airyOscPrefactor kind u‖ * Real.exp |(airyZetaComplex u).im| := by
  have hz := airyErr_one_le_norm_zeta hu
  unfold airyOscError
  have he : ‖airyZetaComplex u‖ ^ (-(2 * ((0 : ℕ) : ℤ))) +
      ‖airyZetaComplex u‖ ^ (-(2 * ((0 : ℕ) : ℤ) + 1)) ≤ 2 := by
    simp only [Nat.cast_zero, mul_zero, neg_zero, zpow_zero, zero_add, zpow_neg_one]
    have hi : ‖airyZetaComplex u‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hz
    linarith
  have hp : 0 ≤ ‖airyZetaComplex u‖ ^ (-(2 * ((0 : ℕ) : ℤ))) +
      ‖airyZetaComplex u‖ ^ (-(2 * ((0 : ℕ) : ℤ) + 1)) := by
    have : 0 < ‖airyZetaComplex u‖ := by linarith
    positivity
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) hp)]
  have h0 := norm_nonneg (airyOscPrefactor kind u)
  have h1 := Real.exp_pos |(airyZetaComplex u).im|
  nlinarith [mul_nonneg h0 h1.le]

/-- The norm of the oscillatory `Ai` prefactor. -/
theorem airyErr_norm_oscPref_ai (u : ℂ) :
    ‖airyOscPrefactor .ai u‖ = 1 / (Real.sqrt π * ‖u‖ ^ (1 / 4 : ℝ)) := by
  rw [airyOscPrefactor, norm_div, norm_one, norm_mul, airyErr_norm_quarter, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]

/-- The norm of the oscillatory `Ai'` prefactor. -/
theorem airyErr_norm_oscPref_aiDeriv (u : ℂ) :
    ‖airyOscPrefactor .aiDeriv u‖ = ‖u‖ ^ (1 / 4 : ℝ) / Real.sqrt π := by
  rw [airyOscPrefactor, norm_div, airyErr_norm_quarter, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]

/-- Near the negative axis, `|e^{-ζ(w)}| = e^{|im ζ(-w)|}`. -/
theorem airyErr_negative_axis {w : ℂ} (hw : w ≠ 0) (harg : 5 * π / 6 < |arg w|) :
    ‖-w‖ = ‖w‖ ∧ -w ≠ 0 ∧ |arg (-w)| ≤ 2 * π / 3 - π / 2 ∧
      ‖exp (-airyZetaComplex w)‖ = Real.exp |(airyZetaComplex (-w)).im| := by
  have hπ := Real.pi_pos
  have hb := abs_le.mp (abs_arg_le_pi w)
  have hlt := Complex.neg_pi_lt_arg w
  refine ⟨norm_neg w, neg_ne_zero.mpr hw, ?_⟩
  have key : ∀ α : ℝ, (α = π ∨ α = -π) → -π < arg w + α → arg w + α ≤ π →
      |arg w + α| ≤ π / 6 → ((α = π → 0 ≤ arg w + α) ∧ (α = -π → arg w + α ≤ 0)) →
      |arg (-w)| ≤ 2 * π / 3 - π / 2 ∧
        ‖exp (-airyZetaComplex w)‖ = Real.exp |(airyZetaComplex (-w)).im| := by
    intro α hα h1 h2 h3 hsgn
    have hneg : -w = w * exp (α * I) := by
      rcases hα with rfl | rfl
      · rw [exp_pi_mul_I]; ring
      · rw [ofReal_neg, neg_mul, exp_neg, exp_pi_mul_I]; ring
    have ha : arg (-w) = arg w + α := by rw [hneg]; exact airyRot_arg_mul_exp hw h1 h2
    refine ⟨by rw [ha]; linarith [abs_le.mp h3], ?_⟩
    -- w = (-w) * exp (-α I)
    have hw' : w = -w * exp (((-α : ℝ) : ℂ) * I) := by
      rw [hneg, mul_assoc, ← exp_add, ofReal_neg, neg_mul, add_neg_cancel, exp_zero, mul_one]
    have hz := airyRot_zeta_mul_exp (neg_ne_zero.mpr hw) (α := -α) (by rw [ha]; linarith)
      (by rw [ha]; linarith)
    rw [← hw'] at hz
    have him := airyErr_im_two_zeta (neg_ne_zero.mpr hw)
    rw [ha] at him
    rcases hα with rfl | rfl
    · -- arg (-w) ≥ 0, im ζ(-w) ≥ 0, ζ(w) = i ζ(-w)
      have he : exp (((-π : ℝ) : ℂ) * I * (3 / 2)) = I := by
        rw [show (((-π : ℝ) : ℂ) * I * (3 / 2)) = -(π * I) + -(π / 2 * I) by push_cast; ring,
          exp_add, exp_neg, exp_neg, exp_pi_mul_I, exp_pi_div_two_mul_I]
        field_simp; norm_num [I_sq]
      rw [hz, he, Complex.norm_exp]
      have hs : 0 ≤ (airyZetaComplex (-w)).im := by
        have h0 : 0 ≤ arg w + π := hsgn.1 rfl
        have : 0 ≤ Real.sin (3 / 2 * (arg w + π)) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [abs_le.mp h3])
        have : 0 ≤ (2 * airyZetaComplex (-w)).im := by rw [him]; positivity
        simpa using this
      rw [abs_of_nonneg hs]
      congr 1
      simp
    · have he : exp (((-(-π) : ℝ) : ℂ) * I * (3 / 2)) = -I := by
        rw [show (((-(-π) : ℝ) : ℂ) * I * (3 / 2)) = π * I + π / 2 * I by push_cast; ring,
          exp_add, exp_pi_mul_I, exp_pi_div_two_mul_I]
        ring
      rw [hz, he, Complex.norm_exp]
      have hs : (airyZetaComplex (-w)).im ≤ 0 := by
        have h0 : arg w + -π ≤ 0 := hsgn.2 rfl
        have : Real.sin (3 / 2 * (arg w + -π)) ≤ 0 :=
          Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith [abs_le.mp h3])
        have : (2 * airyZetaComplex (-w)).im ≤ 0 := by
          rw [him]; exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le this
        simp at this; linarith
      rw [abs_of_nonpos hs]
      congr 1
      simp
  rcases le_or_gt 0 (arg w) with h | h
  · rw [abs_of_nonneg h] at harg
    exact key (-π) (Or.inr rfl) (by linarith) (by linarith)
      (abs_le.mpr ⟨by linarith, by linarith⟩) ⟨fun h' => by linarith, fun _ => by linarith⟩
  · rw [abs_of_neg h] at harg
    exact key π (Or.inl rfl) (by linarith) (by linarith)
      (abs_le.mpr ⟨by linarith, by linarith⟩) ⟨fun _ => by linarith, fun h' => by linarith⟩

/-- **Uniform bounds for `Ai` and `Ai'` in the closed plane** `|arg w| ≤ π`:
`|Ai w| ≤ C |e^{-ζ}| |w|^{-1/4}` and `|Ai' w| ≤ C |e^{-ζ}| |w|^{1/4}` for large `|w|`,
including the negative real axis. -/
theorem airyErr_ai_uniform : ∃ C R : ℝ, 0 ≤ C ∧ ∀ w : ℂ, R ≤ ‖w‖ → w ≠ 0 →
    ‖airyAi w‖ ≤ C * ‖airyPrefactor .ai w‖ ∧ ‖airyAiDeriv w‖ ≤ C * ‖airyPrefactor .aiDeriv w‖ := by
  have hπ := Real.pi_pos
  have h1 := airy_ai_poincare (δ := π / 6) (by positivity) (by linarith) 0
  have h2 := airy_aiDeriv_poincare (δ := π / 6) (by positivity) (by linarith) 0
  simp only [airyExponentialSum, Finset.range_zero, Finset.sum_empty, mul_zero, sub_zero,
    pow_zero, div_one, airyFunction] at h1 h2
  have h3 := airy_ai_oscillatory_expansion (δ := π / 2) (by positivity) (by linarith) 0 0
  have h4 := airy_aiDeriv_oscillatory_expansion (δ := π / 2) (by positivity) (by linarith) 0 0
  simp only [airyOscApprox, airyOscSum, Finset.range_zero, Finset.sum_empty, mul_zero,
    add_zero, sub_zero, airyFunction] at h3 h4
  obtain ⟨C1, R1, hC1, hb1⟩ := airyErr_bound_of_isBigO h1
  obtain ⟨C2, R2, hC2, hb2⟩ := airyErr_bound_of_isBigO h2
  obtain ⟨C3, R3, hC3, hb3⟩ := airyErr_bound_of_isBigO h3
  obtain ⟨C4, R4, hC4, hb4⟩ := airyErr_bound_of_isBigO h4
  refine ⟨C1 + C2 + 4 * (C3 + C4), max (max R1 R2) (max (max R3 R4) 2), by positivity,
    fun w hR hw0 => ?_⟩
  have hR1 : R1 ≤ ‖w‖ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hR2 : R2 ≤ ‖w‖ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hR3 : R3 ≤ ‖w‖ :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hR
  have hR4 : R4 ≤ ‖w‖ :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hR
  have h2w : 2 ≤ ‖w‖ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hR
  have hn1 := norm_nonneg (airyPrefactor .ai w)
  have hn2 := norm_nonneg (airyPrefactor .aiDeriv w)
  rcases le_or_gt |arg w| (π - π / 6) with harg | harg
  · have e1 := hb1 w hR1 hw0 harg
    have e2 := hb2 w hR2 hw0 harg
    constructor
    · nlinarith [mul_nonneg hC2 hn1, mul_nonneg hC3 hn1, mul_nonneg hC4 hn1]
    · nlinarith [mul_nonneg hC1 hn2, mul_nonneg hC3 hn2, mul_nonneg hC4 hn2]
  · obtain ⟨hun, hu0, hua, hexp⟩ := airyErr_negative_axis hw0 (by linarith)
    have e3 := hb3 (-w) (by rw [hun]; exact hR3) hu0 hua
    have e4 := hb4 (-w) (by rw [hun]; exact hR4) hu0 hua
    rw [neg_neg] at e3 e4
    have o3 := airyErr_oscError_le' .ai (u := -w) (by rw [hun]; exact h2w)
    have o4 := airyErr_oscError_le' .aiDeriv (u := -w) (by rw [hun]; exact h2w)
    rw [airyErr_norm_oscPref_ai, hun, ← hexp] at o3
    rw [airyErr_norm_oscPref_aiDeriv, hun, ← hexp] at o4
    have pa := airyErr_norm_pref_ai w
    have pd := airyErr_norm_pref_aiDeriv w
    have q3 : 2 * (1 / (Real.sqrt π * ‖w‖ ^ (1 / 4 : ℝ))) * ‖exp (-airyZetaComplex w)‖ =
        4 * ‖airyPrefactor .ai w‖ := by rw [pa]; ring
    have q4 : 2 * (‖w‖ ^ (1 / 4 : ℝ) / Real.sqrt π) * ‖exp (-airyZetaComplex w)‖ =
        4 * ‖airyPrefactor .aiDeriv w‖ := by rw [pd]; ring
    rw [q3] at o3
    rw [q4] at o4
    have f3 := e3.trans (mul_le_mul_of_nonneg_left o3 hC3)
    have f4 := e4.trans (mul_le_mul_of_nonneg_left o4 hC4)
    constructor
    · nlinarith [mul_nonneg hC1 hn1, mul_nonneg hC2 hn1, mul_nonneg hC4 hn1]
    · nlinarith [mul_nonneg hC1 hn2, mul_nonneg hC2 hn2, mul_nonneg hC3 hn2]

/-- Cross products of `Ai` and `Ai'` at two points of equal modulus whose `ζ` have
nonnegative total real part are bounded. -/
theorem airyErr_cross_le {C R : ℝ} (hC : 0 ≤ C)
    (hU : ∀ w : ℂ, R ≤ ‖w‖ → w ≠ 0 →
      ‖airyAi w‖ ≤ C * ‖airyPrefactor .ai w‖ ∧ ‖airyAiDeriv w‖ ≤ C * ‖airyPrefactor .aiDeriv w‖)
    {w₁ w₂ : ℂ} (h₁ : w₁ ≠ 0) (h₂ : w₂ ≠ 0) (hn : ‖w₁‖ = ‖w₂‖) (hR : R ≤ ‖w₁‖)
    (hre : 0 ≤ (airyZetaComplex w₁).re + (airyZetaComplex w₂).re) :
    ‖airyAi w₁‖ * ‖airyAiDeriv w₂‖ ≤ C ^ 2 / (4 * π) := by
  have hπ := Real.pi_pos
  have e1 := (hU w₁ hR h₁).1
  have e2 := (hU w₂ (hn ▸ hR) h₂).2
  have hq : 0 < ‖w₁‖ ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (norm_pos_iff.mpr h₁) _
  have hs : 0 < Real.sqrt π := Real.sqrt_pos.mpr hπ
  have hs2 : Real.sqrt π ^ 2 = π := Real.sq_sqrt hπ.le
  have hE : ‖exp (-airyZetaComplex w₁)‖ * ‖exp (-airyZetaComplex w₂)‖ ≤ 1 := by
    rw [← norm_mul, ← exp_add, Complex.norm_exp, Real.exp_le_one_iff]
    simp only [add_re, neg_re]; linarith
  have hP : ‖airyPrefactor .ai w₁‖ * ‖airyPrefactor .aiDeriv w₂‖ ≤ 1 / (4 * π) := by
    rw [airyErr_norm_pref_ai, airyErr_norm_pref_aiDeriv, ← hn,
      show ‖exp (-airyZetaComplex w₁)‖ / (2 * Real.sqrt π * ‖w₁‖ ^ (1 / 4 : ℝ)) *
        (‖w₁‖ ^ (1 / 4 : ℝ) * ‖exp (-airyZetaComplex w₂)‖ / (2 * Real.sqrt π)) =
        (‖exp (-airyZetaComplex w₁)‖ * ‖exp (-airyZetaComplex w₂)‖) / (4 * Real.sqrt π ^ 2) by
        field_simp; ring, hs2]
    gcongr
  calc ‖airyAi w₁‖ * ‖airyAiDeriv w₂‖
      ≤ (C * ‖airyPrefactor .ai w₁‖) * (C * ‖airyPrefactor .aiDeriv w₂‖) := by gcongr
    _ = C ^ 2 * (‖airyPrefactor .ai w₁‖ * ‖airyPrefactor .aiDeriv w₂‖) := by ring
    _ ≤ C ^ 2 * (1 / (4 * π)) := by gcongr
    _ = _ := by ring

/-- `ζ(z e^{iα}) = ζ(z) e^{3iα/2}` when no branch cut is crossed. -/
theorem airyErr_zeta_rot {z : ℂ} (hz : z ≠ 0) {α : ℝ} (h1 : -π < arg z + α) (h2 : arg z + α ≤ π)
    {κ : ℂ} (hκ : exp (α * I * (3 / 2)) = κ) :
    airyZetaComplex (z * exp (α * I)) = airyZetaComplex z * κ := by
  rw [airyRot_zeta_mul_exp hz h1 h2, hκ]

/-- Derivative of `z ↦ Ai(z c)`. -/
theorem airyErr_hasDerivAt_rot (c z : ℂ) :
    HasDerivAt (fun z => airyAi (z * c)) (airyAiDeriv (z * c) * c) z := by
  exact (hasDerivAt_airyAi (z * c)).comp z (hasDerivAt_mul_const c)

/-- `deriv` of `z ↦ Ai(z c)`. -/
theorem airyErr_deriv_rot (c : ℂ) :
    deriv (fun z => airyAi (z * c)) = fun z => airyAiDeriv (z * c) * c :=
  funext fun z => (airyErr_hasDerivAt_rot c z).deriv

/-- Continuity of `z ↦ Ai(z c)`. -/
theorem airyErr_continuous_rot (c : ℂ) : Continuous fun z => airyAi (z * c) :=
  differentiable_airyAi.continuous.comp (by fun_prop : Continuous fun z : ℂ => z * c)

/-- Continuity of `z ↦ Ai'(z c) c`. -/
theorem airyErr_continuous_deriv_rot (c : ℂ) : Continuous fun z => airyAiDeriv (z * c) * c :=
  ((Differentiable.continuous (𝕜 := ℂ) fun z => (hasDerivAt_airyAiDeriv z).differentiableAt).comp
    (by fun_prop : Continuous fun z : ℂ => z * c)).mul continuous_const

end DLMF.Airy
