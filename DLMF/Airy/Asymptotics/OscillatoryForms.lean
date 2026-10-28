/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Asymptotics.LaplaceSectors

/-!
# Rotations and oscillatory forms of Airy expansions

Rotation formulas, branch powers and the even and odd parts of Airy expansions on the negative
axis.

Source references and common attribution are retained in
`DLMF.Airy.Asymptotics`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF.Confluent

open scoped Real Topology Interval

namespace DLMF.Airy

/-! ### Rotations of the variable -/

/-- `ζ(z e^{iα}) = ζ(z) e^{3iα/2}` when `arg z + α ∈ (-π, π]`. -/
theorem airyRot_zeta_mul_exp {z : ℂ} (hz : z ≠ 0) {α : ℝ} (h1 : -π < arg z + α)
    (h2 : arg z + α ≤ π) :
    airyZetaComplex (z * exp (α * I)) = airyZetaComplex z * exp (α * I * (3 / 2)) := by
  unfold airyZetaComplex
  rw [Complex.cpow_mul_exp_ofReal_mul_I hz h1 h2]
  ring

/-- Rotation by `c` maps the sector `|arg z| ≤ α` into `|arg z| ≤ β` when `|c| + α ≤ β < π`. -/
theorem airyRot_tendsto_rotate {α β c : ℝ} (hc : |c| + α ≤ β) (hβ : β < π) :
    Tendsto (fun z : ℂ => z * exp (c * I)) (airySector α) (airySector β) := by
  refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr ?_⟩
  · refine (tendsto_comap.mono_left inf_le_left).congr fun z => ?_
    simp only [Function.comp_apply, norm_mul, norm_exp_ofReal_mul_I, mul_one]
  · filter_upwards [airyRot_eventually_arg α] with z hz
    refine ⟨mul_ne_zero hz.1 (exp_ne_zero _), ?_⟩
    have h1 := abs_le.mp hz.2
    have h2 := le_abs_self c
    have h3 := neg_abs_le c
    rw [Complex.arg_mul_exp_ofReal_mul_I hz.1 (by linarith) (by linarith)]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The exponents `e^{±2πi/3}` in the form `e^{iα}`. -/
theorem airyRot_exp_two_pi_div_three :
    exp (2 * π * I / 3) = exp (((2 * π / 3 : ℝ) : ℂ) * I) ∧
      exp (-(2 * π * I / 3)) = exp (((-(2 * π / 3)) : ℝ) * I) := by
  constructor <;> congr 1 <;> push_cast <;> ring

/-- An expansion on `|arg z| ≤ π - δ` gives, at the two rotated points `z e^{±2πi/3}`,
expansions on `|arg z| ≤ π/3 - δ` with alternating coefficients. -/
theorem airyRot_rotated_expansion {F : ℂ → ℂ} {c : ℕ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hF : HasAsymptoticExpansion (airySector (π - δ))
      (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) c F) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    HasAsymptoticExpansion (airySector (π / 3 - δ))
      (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) (fun n => (-1) ^ n * c n)
      (fun z => F (z * exp (((ε * (2 * π / 3)) : ℝ) * I))) := by
  have hπ := Real.pi_pos
  have habs : |ε * (2 * π / 3)| = 2 * π / 3 := by
    rcases hε with h | h <;> subst h <;> simp [abs_of_pos (by positivity : (0:ℝ) < 2 * π / 3)]
  have h := hF.comp_tendsto (airyRot_tendsto_rotate (α := π / 3 - δ) (β := π - δ)
    (c := ε * (2 * π / 3)) (by rw [habs]; linarith) (by linarith))
  refine (h.smul_scale (κ := fun n => (-1 : ℂ) ^ n)
    (ψ := fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) fun n => ?_).congr_coeff ?_
  · filter_upwards [airyRot_eventually_arg (π / 3 - δ)] with z hz
    have h1 := abs_le.mp hz.2
    have h2 : -π < arg z + ε * (2 * π / 3) ∧ arg z + ε * (2 * π / 3) ≤ π := by
      rcases hε with h | h <;> subst h <;> constructor <;> linarith
    rw [airyRot_zeta_mul_exp hz.1 h2.1 h2.2]
    have he : exp (((ε * (2 * π / 3) : ℝ) : ℂ) * I * (3 / 2)) = -1 := by
      rcases hε with h | h <;> subst h
      · rw [show (((1 * (2 * π / 3) : ℝ) : ℂ) * I * (3 / 2)) = π * I by push_cast; ring,
          exp_pi_mul_I]
      · rw [show ((((-1) * (2 * π / 3) : ℝ) : ℂ) * I * (3 / 2)) = -(π * I) by push_cast; ring,
          exp_neg, exp_pi_mul_I]; norm_num
    rw [he, mul_neg_one, neg_pow, mul_inv, ← inv_pow, inv_neg, inv_one]
  · funext n
    simp only [smul_eq_mul]

/-- `exp ((±2π/3) · i · 3/2) = -1`. -/
theorem airyRot_exp_rot_three_halves {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    exp (((ε * (2 * π / 3) : ℝ) : ℂ) * I * (3 / 2)) = -1 := by
  rcases hε with h | h <;> subst h
  · rw [show (((1 * (2 * π / 3) : ℝ) : ℂ) * I * (3 / 2)) = π * I by push_cast; ring,
      exp_pi_mul_I]
  · rw [show ((((-1) * (2 * π / 3) : ℝ) : ℂ) * I * (3 / 2)) = -(π * I) by push_cast; ring,
      exp_neg, exp_pi_mul_I]; norm_num

/-- For `|arg z| < π/3`, `arg z ± 2π/3` lies in `(-π, π]`. -/
theorem airyRot_arg_rot_bounds {z : ℂ} (hz : |arg z| < π / 3) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    -π < arg z + ε * (2 * π / 3) ∧ arg z + ε * (2 * π / 3) ≤ π := by
  have h1 := abs_lt.mp hz
  have hπ := Real.pi_pos
  rcases hε with h | h <;> subst h <;> constructor <;> linarith

/-- `ζ(z e^{±2πi/3}) = -ζ(z)` for `|arg z| ≤ π/3`. -/
theorem airyRot_zeta_rot {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π / 3) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) :
    airyZetaComplex (z * exp (((ε * (2 * π / 3)) : ℝ) * I)) = -airyZetaComplex z := by
  obtain ⟨h1, h2⟩ := airyRot_arg_rot_bounds hz hε
  rw [airyRot_zeta_mul_exp hz0 h1 h2, airyRot_exp_rot_three_halves hε, mul_neg_one]

/-- `(z e^{±2πi/3})^{1/4} = z^{1/4} e^{±πi/6}`. -/
theorem airyRot_quarter_rot {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π / 3) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) :
    (z * exp (((ε * (2 * π / 3)) : ℝ) * I)) ^ (1 / 4 : ℂ) =
      z ^ (1 / 4 : ℂ) * exp (((ε * (π / 6)) : ℝ) * I) := by
  obtain ⟨h1, h2⟩ := airyRot_arg_rot_bounds hz hε
  rw [Complex.cpow_mul_exp_ofReal_mul_I hz0 h1 h2]
  congr 2
  push_cast; ring

/-- `e^w e^{-w} = 1`. -/
theorem airyRot_exp_mul_exp_neg (w : ℂ) : exp w * exp (-w) = 1 := by
  rw [← exp_add]; simp

/-- **Poincaré expansion of the normalized `Bi`** in `|arg z| ≤ π/3 - δ` (DLMF 9.7.7). -/
theorem airyRot_airyBi_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π / 3) :
    HasAsymptoticExpansion (airySector (π / 3 - δ)) (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹)
      (airyExpansionCoeff .bi) (fun z => airyBi z / airyPrefactor .bi z) := by
  have hπ := Real.pi_pos
  have hA := airyRot_airyAi_expansion hδ (by linarith)
  have hp := airyRot_rotated_expansion hδ hA (Or.inl rfl)
  have hm := airyRot_rotated_expansion hδ hA (Or.inr rfl)
  refine ((hp.const_smul (1 / 2 : ℂ)).add (hm.const_smul (1 / 2 : ℂ))).congr_coeff ?_ |>.congr' ?_
  · funext n
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, airyExpansionCoeff]
    have h1 : ((-1 : ℂ) ^ n) * ((-1) ^ n) = 1 := by rw [← mul_pow]; norm_num
    linear_combination (airyU n : ℂ) * h1
  · filter_upwards [airyRot_eventually_arg (π / 3 - δ)] with z hz
    have hz0 := hz.1
    have hz3 : |arg z| < π / 3 := hz.2.trans_lt (by linarith)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
    rw [airyBi_eq_airyAi_omega z, airyRot_exp_two_pi_div_three.1, airyRot_exp_two_pi_div_three.2]
    simp only [airyPrefactor]
    rw [airyRot_zeta_rot hz0 hz3 (Or.inl rfl), airyRot_zeta_rot hz0 hz3 (Or.inr rfl),
      airyRot_quarter_rot hz0 hz3 (Or.inl rfl), airyRot_quarter_rot hz0 hz3 (Or.inr rfl)]
    rw [show (((1 : ℝ) * (2 * π / 3) : ℝ) : ℂ) = ((2 * π / 3 : ℝ) : ℂ) by push_cast; ring,
      show (((-1 : ℝ) * (2 * π / 3) : ℝ) : ℂ) = ((-(2 * π / 3) : ℝ) : ℂ) by push_cast; ring]
    have e1 : exp ((((1 : ℝ) * (π / 6) : ℝ) : ℂ) * I) = exp (π * I / 6) := by
      congr 1; push_cast; ring
    have e2 : exp ((((-1 : ℝ) * (π / 6) : ℝ) : ℂ) * I) = exp (-(π * I / 6)) := by
      congr 1; push_cast; ring
    rw [e1, e2]
    have h6 := airyRot_exp_mul_exp_neg (π * I / 6)
    have hz2 := airyRot_exp_mul_exp_neg (airyZetaComplex z)
    rw [neg_neg]
    field_simp
    ring_nf

/-- Differentiating an identity `f(z) = c₁ g(z w₁) + c₂ g(z w₂)`. -/
theorem airyRot_deriv_of_eq {f g f' g' : ℂ → ℂ} (hf : ∀ z, HasDerivAt f (f' z) z)
    (hg : ∀ z, HasDerivAt g (g' z) z) (c₁ c₂ w₁ w₂ : ℂ)
    (h : ∀ z, f z = c₁ * g (z * w₁) + c₂ * g (z * w₂)) (z : ℂ) :
    f' z = c₁ * w₁ * g' (z * w₁) + c₂ * w₂ * g' (z * w₂) := by
  have h1 : HasDerivAt (fun z => c₁ * g (z * w₁) + c₂ * g (z * w₂))
      (c₁ * (g' (z * w₁) * w₁) + c₂ * (g' (z * w₂) * w₂)) z :=
    (((hg (z * w₁)).comp z ((hasDerivAt_id z).mul_const w₁)).const_mul c₁).add
      (((hg (z * w₂)).comp z ((hasDerivAt_id z).mul_const w₂)).const_mul c₂) |>.congr_deriv
      (by simp)
  rw [← funext h] at h1
  rw [(hf z).unique h1]
  ring

/-- `Bi'(z) = e^{-5πi/6} Ai'(z e^{-2πi/3}) + e^{5πi/6} Ai'(z e^{2πi/3})`. -/
theorem airyRot_airyBiDeriv_eq (z : ℂ) :
    airyBiDeriv z = exp (-(π * I / 6)) * exp (-(2 * π * I / 3)) *
        airyAiDeriv (z * exp (-(2 * π * I / 3))) +
      exp (π * I / 6) * exp (2 * π * I / 3) * airyAiDeriv (z * exp (2 * π * I / 3)) :=
  airyRot_deriv_of_eq hasDerivAt_airyBi hasDerivAt_airyAi _ _ _ _ airyBi_eq_airyAi_omega z

/-- **Poincaré expansion of the normalized `Bi'`** in `|arg z| ≤ π/3 - δ` (DLMF 9.7.8). -/
theorem airyRot_airyBiDeriv_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π / 3) :
    HasAsymptoticExpansion (airySector (π / 3 - δ)) (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹)
      (airyExpansionCoeff .biDeriv) (fun z => airyBiDeriv z / airyPrefactor .biDeriv z) := by
  have hπ := Real.pi_pos
  have hA := airyRot_airyAiDeriv_expansion hδ (by linarith)
  have hp := airyRot_rotated_expansion hδ hA (Or.inl rfl)
  have hm := airyRot_rotated_expansion hδ hA (Or.inr rfl)
  refine ((hp.const_smul (1 / 2 : ℂ)).add (hm.const_smul (1 / 2 : ℂ))).congr_coeff ?_ |>.congr' ?_
  · funext n
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, airyExpansionCoeff]
    have h1 : ((-1 : ℂ) ^ n) * ((-1) ^ n) = 1 := by rw [← mul_pow]; norm_num
    linear_combination (airyV n : ℂ) * h1
  · filter_upwards [airyRot_eventually_arg (π / 3 - δ)] with z hz
    have hz0 := hz.1
    have hz3 : |arg z| < π / 3 := hz.2.trans_lt (by linarith)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
    rw [airyRot_airyBiDeriv_eq z, airyRot_exp_two_pi_div_three.1,
      airyRot_exp_two_pi_div_three.2]
    simp only [airyPrefactor]
    rw [airyRot_zeta_rot hz0 hz3 (Or.inl rfl), airyRot_zeta_rot hz0 hz3 (Or.inr rfl),
      airyRot_quarter_rot hz0 hz3 (Or.inl rfl), airyRot_quarter_rot hz0 hz3 (Or.inr rfl)]
    rw [show (((1 : ℝ) * (2 * π / 3) : ℝ) : ℂ) = ((2 * π / 3 : ℝ) : ℂ) by push_cast; ring,
      show (((-1 : ℝ) * (2 * π / 3) : ℝ) : ℂ) = ((-(2 * π / 3)) : ℝ) by push_cast; ring]
    set u := exp (π * I / 6) with hu
    have e1 : exp ((((1 : ℝ) * (π / 6) : ℝ) : ℂ) * I) = u := by
      rw [hu]; congr 1; push_cast; ring
    have e2 : exp ((((-1 : ℝ) * (π / 6) : ℝ) : ℂ) * I) = u⁻¹ := by
      rw [hu, ← exp_neg]; congr 1; push_cast; ring
    have e3 : exp (((2 * π / 3 : ℝ) : ℂ) * I) = u ^ 4 := by
      rw [hu, ← exp_nat_mul]; congr 1; push_cast; ring
    have e4 : exp (((-(2 * π / 3) : ℝ) : ℂ) * I) = (u ^ 4)⁻¹ := by
      rw [hu, ← exp_nat_mul, ← exp_neg]; congr 1; push_cast; ring
    have e5 : exp (-(π * I / 6)) = u⁻¹ := by rw [hu, exp_neg]
    have hu6 : u ^ 6 = -1 := by
      rw [hu, ← exp_nat_mul, show ((6 : ℕ) : ℂ) * (π * I / 6) = π * I by push_cast; ring,
        exp_pi_mul_I]
    have hu0 : u ≠ 0 := exp_ne_zero _
    rw [e1, e2, e3, e4, e5]
    have hz2 := airyRot_exp_mul_exp_neg (airyZetaComplex z)
    rw [neg_neg]
    field_simp
    linear_combination (-(airyAiDeriv (z / u ^ 4) + u ^ 4 * airyAiDeriv (z * u ^ 4))) * hu6

/-! ### Even and odd parts on the negative axis -/

/-- An expansion on `|arg z| ≤ π - δ` restricts along the rotation `z ↦ z e^{iα}` to the sector
`|arg z| ≤ β`, for `|α| + β ≤ π - δ`. -/
theorem airyRot_rot_expansion {F : ℂ → ℂ} {c : ℕ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hF : HasAsymptoticExpansion (airySector (π - δ))
      (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) c F) {α β : ℝ} (hαβ : |α| + β ≤ π - δ) :
    HasAsymptoticExpansion (airySector β)
      (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹)
      (fun n => ((exp (α * I * (3 / 2))) ^ n)⁻¹ * c n)
      (fun z => F (z * exp (α * I))) := by
  have hπ := Real.pi_pos
  have h := hF.comp_tendsto (airyRot_tendsto_rotate (α := β) (β := π - δ) (c := α) hαβ
    (by linarith))
  refine (h.smul_scale (κ := fun n => ((exp (α * I * (3 / 2))) ^ n)⁻¹)
    (ψ := fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) fun n => ?_).congr_coeff ?_
  · filter_upwards [airyRot_eventually_arg β] with z hz
    have h1 := abs_le.mp hz.2
    have h2 := le_abs_self α
    have h3 := neg_abs_le α
    rw [airyRot_zeta_mul_exp hz.1 (by linarith) (by linarith), mul_pow, mul_inv, mul_comm]
  · funext n
    simp only [smul_eq_mul]

/-- The even part `(F(z e^{iπ/3}) + F(z e^{-iπ/3}))/2`. -/
def airyRot_even (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (F (z * exp ((π / 3 : ℝ) * I)) + F (z * exp ((-(π / 3) : ℝ) * I))) / 2

/-- The odd part `(F(z e^{iπ/3}) - F(z e^{-iπ/3}))/(2i)`. -/
def airyRot_odd (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (F (z * exp ((π / 3 : ℝ) * I)) - F (z * exp ((-(π / 3) : ℝ) * I))) / (2 * I)

/-- `exp ((π/3) · i · 3/2) = i` and `exp ((-π/3) · i · 3/2) = -i`. -/
theorem airyRot_exp_third_three_halves :
    exp (((π / 3 : ℝ) : ℂ) * I * (3 / 2)) = I ∧ exp (((-(π / 3)) : ℝ) * I * (3 / 2)) = -I := by
  constructor
  · rw [show (((π / 3 : ℝ) : ℂ) * I * (3 / 2)) = ((π / 2 : ℝ) : ℂ) * I by push_cast; ring,
      exp_mul_I]
    simp
  · rw [show ((((-(π / 3)) : ℝ) : ℂ) * I * (3 / 2)) = ((-(π / 2)) : ℝ) * I by push_cast; ring,
      exp_mul_I]
    simp

/-- Even powers: `(i^{-2j} + (-i)^{-2j})/2 = (-1)^j` and the odd combination vanishes. -/
theorem airyRot_I_pow_recip_even (j : ℕ) :
    ((I ^ (2 * j))⁻¹ + ((-I) ^ (2 * j))⁻¹) / 2 = (-1) ^ j ∧
      ((I ^ (2 * j))⁻¹ - ((-I) ^ (2 * j))⁻¹) / (2 * I) = 0 := by
  have h1 : I ^ (2 * j) = (-1) ^ j := by rw [pow_mul, I_sq]
  have h2 : (-I) ^ (2 * j) = (-1) ^ j := by rw [pow_mul, neg_sq, I_sq]
  rw [h1, h2]
  constructor
  · rw [← inv_pow, inv_neg, inv_one]; ring
  · simp

/-- Odd powers: `(i^{-(2j+1)} + (-i)^{-(2j+1)})/2 = 0` and the odd combination is `-(-1)^j`. -/
theorem airyRot_I_pow_recip_odd (j : ℕ) :
    ((I ^ (2 * j + 1))⁻¹ + ((-I) ^ (2 * j + 1))⁻¹) / 2 = 0 ∧
      ((I ^ (2 * j + 1))⁻¹ - ((-I) ^ (2 * j + 1))⁻¹) / (2 * I) = -(-1) ^ j := by
  have h1 : I ^ (2 * j + 1) = (-1) ^ j * I := by rw [pow_succ, pow_mul, I_sq]
  have h2 : (-I) ^ (2 * j + 1) = -((-1) ^ j * I) := by rw [pow_succ, pow_mul, neg_sq, I_sq]; ring
  rw [h1, h2]
  have hI : I ≠ 0 := I_ne_zero
  have hm : ((-1 : ℂ) ^ j) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hm2 : ((-1 : ℂ) ^ j) * (-1) ^ j = 1 := by rw [← mul_pow]; norm_num
  constructor
  · rw [inv_neg]; ring
  · field_simp
    linear_combination (2 : ℂ) * I_sq + (2 * I ^ 2) * hm2

/-- An expansion in `ζ^{-n}` on `|arg z| ≤ π - δ` gives expansions of `F(z e^{±iπ/3})` with
coefficients `(±i)^{-n} c_n` on `|arg z| ≤ 2π/3 - δ`. -/
theorem airyRot_pm_expansions {F : ℂ → ℂ} {c : ℕ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hF : HasAsymptoticExpansion (airySector (π - δ))
      (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) c F) :
    HasAsymptoticExpansion (airySector (2 * π / 3 - δ))
        (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) (fun n => (I ^ n)⁻¹ * c n)
        (fun z => F (z * exp ((π / 3 : ℝ) * I))) ∧
      HasAsymptoticExpansion (airySector (2 * π / 3 - δ))
        (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) (fun n => ((-I) ^ n)⁻¹ * c n)
        (fun z => F (z * exp ((-(π / 3) : ℝ) * I))) := by
  have hπ := Real.pi_pos
  constructor
  · have h := airyRot_rot_expansion hδ hF (α := π / 3) (β := 2 * π / 3 - δ)
      (by rw [abs_of_pos (by positivity)]; linarith)
    rwa [airyRot_exp_third_three_halves.1] at h
  · have h := airyRot_rot_expansion hδ hF (α := -(π / 3)) (β := 2 * π / 3 - δ)
      (by rw [abs_neg, abs_of_pos (by positivity)]; linarith)
    rwa [airyRot_exp_third_three_halves.2] at h

/-- The even part has the even subseries `∑ (-1)^j c_{2j} ζ^{-2j}`. -/
theorem airyRot_even_expansion {F : ℂ → ℂ} {c : ℕ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hF : HasAsymptoticExpansion (airySector (π - δ))
      (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) c F) :
    HasAsymptoticExpansion (airySector (2 * π / 3 - δ))
      (fun (j : ℕ) z => ((airyZetaComplex z) ^ (2 * j))⁻¹) (fun j => (-1) ^ j * c (2 * j))
      (airyRot_even F) := by
  obtain ⟨hp, hm⟩ := airyRot_pm_expansions hδ hF
  have h := ((hp.add hm).const_smul (1 / 2 : ℂ)).congr' (g := airyRot_even F)
    (Eventually.of_forall fun z => by
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, airyRot_even]; ring)
  have h' := h.even (fun j => by
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    have := (airyRot_I_pow_recip_odd j).1
    linear_combination (c (2 * j + 1)) * this)
  refine h'.congr_coeff (funext fun j => ?_)
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  have := (airyRot_I_pow_recip_even j).1
  linear_combination (c (2 * j)) * this

/-- The odd part has the odd subseries `-∑ (-1)^j c_{2j+1} ζ^{-2j-1}`. -/
theorem airyRot_odd_expansion {F : ℂ → ℂ} {c : ℕ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hF : HasAsymptoticExpansion (airySector (π - δ))
      (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) c F) :
    HasAsymptoticExpansion (airySector (2 * π / 3 - δ))
      (fun (j : ℕ) z => ((airyZetaComplex z) ^ (2 * j + 1))⁻¹)
      (fun j => -((-1) ^ j * c (2 * j + 1))) (airyRot_odd F) := by
  obtain ⟨hp, hm⟩ := airyRot_pm_expansions hδ hF
  have h := ((hp.sub hm).const_smul (1 / (2 * I) : ℂ)).congr' (g := airyRot_odd F)
    (Eventually.of_forall fun z => by
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, airyRot_odd]; ring)
  have h' := h.odd (fun j => by
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    have := (airyRot_I_pow_recip_even j).2
    linear_combination (c (2 * j)) * this)
  refine h'.congr_coeff (funext fun j => ?_)
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  have := (airyRot_I_pow_recip_odd j).2
  linear_combination (c (2 * j + 1)) * this

/-! ### The oscillatory error envelope -/

/-- `‖e^{∓iw}‖ ≤ e^{|Im w|}`. -/
theorem airyRot_norm_exp_mul_I_le (w : ℂ) :
    ‖exp (-(w * I))‖ ≤ Real.exp |w.im| ∧ ‖exp (w * I)‖ ≤ Real.exp |w.im| := by
  constructor <;> rw [Complex.norm_exp] <;> apply Real.exp_le_exp.mpr <;> simp <;>
    [exact le_abs_self _; exact neg_le_abs _]

/-- `‖(w^k)⁻¹‖ = ‖w‖^{-k}`. -/
theorem airyRot_norm_recip_pow (w : ℂ) (k : ℕ) : ‖(w ^ k)⁻¹‖ = ‖w‖ ^ (-(k : ℤ)) := by
  rw [norm_inv, norm_pow, zpow_neg, zpow_natCast]

/-- **The oscillatory envelope.** If `X = pref (a E + b O)` and `Y = pref (a P + b Q)` with
`a, b` combinations of `e^{∓iζ}`, then `X - Y` is bounded by the envelope
`|pref| e^{|im ζ|} (|ζ|^{-2N} + |ζ|^{-2M-1})`. -/
theorem airyRot_osc_bound {l : Filter ℂ} {E O P Q pref X Y : ℂ → ℂ} {N M : ℕ} (κp κm : ℂ)
    (hE : (fun z => E z - P z) =O[l] (fun z => ((airyZetaComplex z) ^ (2 * N))⁻¹))
    (hO : (fun z => O z - Q z) =O[l] (fun z => ((airyZetaComplex z) ^ (2 * M + 1))⁻¹))
    (hX : ∀ᶠ z in l, X z = pref z *
      ((κp * exp (-(airyZetaComplex z * I)) + κm * exp (airyZetaComplex z * I)) * E z +
        I * (κp * exp (-(airyZetaComplex z * I)) - κm * exp (airyZetaComplex z * I)) * O z))
    (hY : ∀ᶠ z in l, Y z = pref z *
      ((κp * exp (-(airyZetaComplex z * I)) + κm * exp (airyZetaComplex z * I)) * P z +
        I * (κp * exp (-(airyZetaComplex z * I)) - κm * exp (airyZetaComplex z * I)) * Q z)) :
    IsBigO l (fun z => X z - Y z) (fun z => ‖pref z‖ * Real.exp |(airyZetaComplex z).im| *
      (‖airyZetaComplex z‖ ^ (-(2 * N : ℤ)) + ‖airyZetaComplex z‖ ^ (-(2 * M + 1 : ℤ)))) := by
  obtain ⟨C1, hC1, h1⟩ := hE.exists_pos
  obtain ⟨C2, hC2, h2⟩ := hO.exists_pos
  set K := ‖κp‖ + ‖κm‖
  refine IsBigO.of_bound (K * (C1 + C2)) ?_
  filter_upwards [h1.bound, h2.bound, hX, hY] with z hz1 hz2 hzX hzY
  rw [hzX, hzY]
  set ζ := airyZetaComplex z
  obtain ⟨he1, he2⟩ := airyRot_norm_exp_mul_I_le ζ
  set A := κp * exp (-(ζ * I)) + κm * exp (ζ * I)
  set B := I * (κp * exp (-(ζ * I)) - κm * exp (ζ * I))
  have hA : ‖A‖ ≤ K * Real.exp |ζ.im| := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have := norm_nonneg κp; have := norm_nonneg κm
    nlinarith
  have hB : ‖B‖ ≤ K * Real.exp |ζ.im| := by
    rw [norm_mul, norm_I, one_mul]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have := norm_nonneg κp; have := norm_nonneg κm
    nlinarith
  have heq : pref z * (A * E z + B * O z) - pref z * (A * P z + B * Q z) =
      pref z * (A * (E z - P z) + B * (O z - Q z)) := by ring
  rw [heq]
  rw [airyRot_norm_recip_pow] at hz1 hz2
  have hr1 : (0 : ℝ) ≤ ‖ζ‖ ^ (-(2 * N : ℤ)) := by positivity
  have hr2 : (0 : ℝ) ≤ ‖ζ‖ ^ (-(2 * M + 1 : ℤ)) := by positivity
  have hex := Real.exp_pos |ζ.im|
  have hK : 0 ≤ K := by positivity
  rw [Real.norm_of_nonneg (by positivity)]
  rw [norm_mul]
  push_cast at hz1 hz2 ⊢
  calc ‖pref z‖ * ‖A * (E z - P z) + B * (O z - Q z)‖
      ≤ ‖pref z‖ * (‖A‖ * ‖E z - P z‖ + ‖B‖ * ‖O z - Q z‖) := by
        gcongr
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
    _ ≤ ‖pref z‖ * (K * Real.exp |ζ.im| * (C1 * ‖ζ‖ ^ (-(2 * (N : ℤ)))) +
          K * Real.exp |ζ.im| * (C2 * ‖ζ‖ ^ (-(2 * (M : ℤ) + 1)))) := by
        gcongr
    _ ≤ K * (C1 + C2) * (‖pref z‖ * Real.exp |ζ.im| *
          (‖ζ‖ ^ (-(2 * (N : ℤ))) + ‖ζ‖ ^ (-(2 * (M : ℤ) + 1)))) := by
        have := norm_nonneg (pref z)
        have hp1 : 0 ≤ ‖pref z‖ * Real.exp |ζ.im| := by positivity
        nlinarith [mul_nonneg hp1 hr1, mul_nonneg hp1 hr2, mul_nonneg hK hC1.le,
          mul_nonneg hK hC2.le, mul_nonneg (mul_nonneg hp1 hr1) (mul_nonneg hK hC2.le),
          mul_nonneg (mul_nonneg hp1 hr2) (mul_nonneg hK hC1.le)]

/-! ### The oscillatory expansions on the negative axis -/

/-- Rewriting `α₊ F(z e^{iπ/3}) + α₋ F(z e^{-iπ/3})` through the even and odd parts. -/
theorem airyRot_decomp (F : ℂ → ℂ) (z αp αm : ℂ) :
    αp * F (z * exp ((π / 3 : ℝ) * I)) + αm * F (z * exp ((-(π / 3) : ℝ) * I)) =
      (αp + αm) * airyRot_even F z + I * (αp - αm) * airyRot_odd F z := by
  simp only [airyRot_even, airyRot_odd]
  field_simp
  ring

/-- For `|arg z| < 2π/3`, `arg z ± π/3` lies in `(-π, π]`. -/
theorem airyRot_arg_third_bounds {z : ℂ} (hz : |arg z| < 2 * π / 3) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) : -π < arg z + ε * (π / 3) ∧ arg z + ε * (π / 3) ≤ π := by
  have h1 := abs_lt.mp hz
  have hπ := Real.pi_pos
  rcases hε with h | h <;> subst h <;> constructor <;> linarith

/-- The data of `ζ` and `z^{1/4}` at the points `z e^{±iπ/3}`. -/
theorem airyRot_third_data {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 2 * π / 3) :
    airyZetaComplex (z * exp ((π / 3 : ℝ) * I)) = airyZetaComplex z * I ∧
    airyZetaComplex (z * exp ((-(π / 3) : ℝ) * I)) = -(airyZetaComplex z * I) ∧
    (z * exp ((π / 3 : ℝ) * I)) ^ (1 / 4 : ℂ) = z ^ (1 / 4 : ℂ) * exp (π * I / 12) ∧
    (z * exp ((-(π / 3) : ℝ) * I)) ^ (1 / 4 : ℂ) = z ^ (1 / 4 : ℂ) * (exp (π * I / 12))⁻¹ := by
  obtain ⟨a1, a2⟩ := airyRot_arg_third_bounds hz (Or.inl rfl)
  obtain ⟨b1, b2⟩ := airyRot_arg_third_bounds hz (Or.inr rfl)
  simp only [one_mul, neg_one_mul] at a1 a2 b1 b2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [airyRot_zeta_mul_exp hz0 a1 a2, airyRot_exp_third_three_halves.1]
  · rw [airyRot_zeta_mul_exp hz0 b1 b2, airyRot_exp_third_three_halves.2]; ring
  · rw [Complex.cpow_mul_exp_ofReal_mul_I hz0 a1 a2]; congr 2; push_cast; ring
  · rw [Complex.cpow_mul_exp_ofReal_mul_I hz0 b1 b2, ← exp_neg]; congr 2; push_cast; ring

/-- DLMF 9.2.14, shared with `DLMF.Airy.Equation` from this earlier module.
The equation module uses the asymptotics here for its numerically satisfactory pairs. -/
theorem airyRot_neg_connection_ai (z : ℂ) :
    airyAi (-z) = exp (π * I / 3) * airyAi (z * exp (π * I / 3)) +
      exp (-π * I / 3) * airyAi (z * exp (-π * I / 3)) := by
  have h := airyAi_add_omega (-z)
  have e1 : -exp (-(2 * π * I / 3)) = exp (π * I / 3) := by
    rw [exp_neg_two_pi_I_div_three, exp_pi_I_div_three]
    push_cast; ring
  have e2 : -exp (2 * π * I / 3) = exp (-π * I / 3) := by
    rw [show -π * I / 3 = -(π * I / 3) by ring, exp_two_pi_I_div_three, exp_neg_pi_I_div_three]
    push_cast; ring
  rw [show -z * exp (-(2 * π * I / 3)) = z * exp (π * I / 3) by rw [← e1]; ring,
    show -z * exp (2 * π * I / 3) = z * exp (-π * I / 3) by rw [← e2]; ring] at h
  linear_combination h + airyAi (z * exp (π * I / 3)) * e1 +
    airyAi (z * exp (-π * I / 3)) * e2

/-- DLMF 9.2.15, shared with the equation module for the same reason. -/
theorem airyRot_neg_connection_bi (z : ℂ) :
    airyBi (-z) = exp (-π * I / 6) * airyAi (z * exp (π * I / 3)) +
      exp (π * I / 6) * airyAi (z * exp (-π * I / 3)) := by
  have h := airyBi_eq_airyAi_omega (-z)
  have e1 : -exp (-(2 * π * I / 3)) = exp (π * I / 3) := by
    rw [exp_neg_two_pi_I_div_three, exp_pi_I_div_three]
    push_cast; ring
  have e2 : -exp (2 * π * I / 3) = exp (-π * I / 3) := by
    rw [show -π * I / 3 = -(π * I / 3) by ring, exp_two_pi_I_div_three, exp_neg_pi_I_div_three]
    push_cast; ring
  simpa only [neg_mul, neg_div, show -z * exp (-(2 * π * I / 3)) = z * exp (π * I / 3) by
    rw [← e1]; ring, show -z * exp (2 * π * I / 3) = z * exp (-π * I / 3) by rw [← e2]; ring] using h

/-- The connection formula for `Ai(-z)` with the rotations written as `e^{iα}`. -/
theorem airyRot_airyAi_neg (z : ℂ) :
    airyAi (-z) = exp (π * I / 3) * airyAi (z * exp ((π / 3 : ℝ) * I)) +
      exp (-π * I / 3) * airyAi (z * exp ((-(π / 3) : ℝ) * I)) := by
  rw [airyRot_neg_connection_ai z]
  congr 4 <;> push_cast <;> ring_nf

/-- `Bi(-z)` with the rotations written as `e^{iα}`. -/
theorem airyRot_airyBi_neg (z : ℂ) :
    airyBi (-z) = exp (-π * I / 6) * airyAi (z * exp ((π / 3 : ℝ) * I)) +
      exp (π * I / 6) * airyAi (z * exp ((-(π / 3) : ℝ) * I)) := by
  rw [airyRot_neg_connection_bi z]
  congr 4 <;> push_cast <;> ring_nf

/-- The twelfth root of `-1`, `u = e^{iπ/12}`, and the exponentials used below. -/
theorem airyRot_u_powers :
    exp (π * I / 3) = exp (π * I / 12) ^ 4 ∧ exp (-π * I / 3) = (exp (π * I / 12) ^ 4)⁻¹ ∧
    exp (π * I / 4) = exp (π * I / 12) ^ 3 ∧ exp (-(π * I / 4)) = (exp (π * I / 12) ^ 3)⁻¹ ∧
    exp (π * I / 6) = exp (π * I / 12) ^ 2 ∧ exp (-π * I / 6) = (exp (π * I / 12) ^ 2)⁻¹ ∧
    exp (π * I / 12) ^ 12 = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [← exp_nat_mul, ← exp_neg]
  · congr 1; push_cast; ring
  · congr 1; push_cast; ring
  · congr 1; push_cast; ring
  · congr 1; push_cast; ring
  · congr 1; push_cast; ring
  · congr 1; push_cast; ring
  · rw [show ((12 : ℕ) : ℂ) * (π * I / 12) = π * I by push_cast; ring, exp_pi_mul_I]

/-- The sum identity behind the even subseries. -/
theorem airyRot_sum_even {d : ℕ → ℂ} (c : ℕ → ℂ) (hc : ∀ j, c (2 * j) = d (2 * j)) (N : ℕ) (z : ℂ) :
    ∑ j ∈ Finset.range N, ((airyZetaComplex z) ^ (2 * j))⁻¹ • ((-1) ^ j * c (2 * j)) =
      ∑ k ∈ Finset.range N, (-1 : ℂ) ^ k * d (2 * k) / airyZetaComplex z ^ (2 * k) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hc, smul_eq_mul]; ring

/-- The odd part of a series with sign-flipped coefficients is
`∑ (-1)^k d_{2k+1} ζ^{-(2k+1)}`. -/
theorem airyRot_sum_odd {d : ℕ → ℂ} (c : ℕ → ℂ) (hc : ∀ j, c (2 * j + 1) = -d (2 * j + 1)) (M : ℕ) (z : ℂ) :
    ∑ j ∈ Finset.range M, ((airyZetaComplex z) ^ (2 * j + 1))⁻¹ • (-((-1) ^ j * c (2 * j + 1))) =
      ∑ k ∈ Finset.range M, (-1 : ℂ) ^ k * d (2 * k + 1) / airyZetaComplex z ^ (2 * k + 1) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hc, smul_eq_mul]; ring

/-- For `Ai` and `Ai'`, the even coefficients are `u_{2j}` (resp. `v_{2j}`) and the odd ones
their negatives. -/
theorem airyRot_coeff_parity (kind : AiryKind) (hk : kind = .ai ∨ kind = .aiDeriv) (j : ℕ) :
    airyExpansionCoeff kind (2 * j) =
      ((if kind = .aiDeriv then airyV (2 * j) else airyU (2 * j) : ℝ) : ℂ) ∧
    airyExpansionCoeff kind (2 * j + 1) =
      -((if kind = .aiDeriv then airyV (2 * j + 1) else airyU (2 * j + 1) : ℝ) : ℂ) := by
  have h1 : (-1 : ℂ) ^ (2 * j) = 1 := by rw [pow_mul]; norm_num
  have h2 : (-1 : ℂ) ^ (2 * j + 1) = -1 := by rw [pow_succ, h1]; norm_num
  rcases hk with h | h <;> subst h <;> simp [airyExpansionCoeff, h1, h2]

/-- The even and odd parts of the normalized `Ai` at `z e^{±iπ/3}` are approximated by the
oscillatory subseries (used for `Ai(-z)`, `Bi(-z)`, `Bi(z e^{±iπ/3})`) in `|arg z| ≤ 2π/3 - δ`. -/
lemma airyRot_ai_parts {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) (N M : ℕ) :
    (fun z => airyRot_even (fun w => airyAi w / airyPrefactor .ai w) z -
      airyOscSum false 0 N z) =O[airySector (2 * π / 3 - δ)]
      (fun z => ((airyZetaComplex z) ^ (2 * N))⁻¹) ∧
    (fun z => airyRot_odd (fun w => airyAi w / airyPrefactor .ai w) z -
      airyOscSum false 1 M z) =O[airySector (2 * π / 3 - δ)]
      (fun z => ((airyZetaComplex z) ^ (2 * M + 1))⁻¹) := by
  have hF := airyRot_airyAi_expansion hδ (by linarith [Real.pi_pos])
  have hE := (airyRot_even_expansion hδ hF) N
  have hO := (airyRot_odd_expansion hδ hF) M
  refine ⟨?_, ?_⟩
  · refine hE.congr_left fun z => ?_
    dsimp only
    rw [airyRot_sum_even (d := fun k => ((airyU k : ℝ) : ℂ)) _
      (fun j => by simpa using (airyRot_coeff_parity .ai (Or.inl rfl) j).1) N z]
    simp [airyOscSum]
  · refine hO.congr_left fun z => ?_
    dsimp only
    rw [airyRot_sum_odd (d := fun k => ((airyU k : ℝ) : ℂ)) _
      (fun j => by simpa using (airyRot_coeff_parity .ai (Or.inl rfl) j).2) M z]
    simp [airyOscSum]

/-- The oscillatory expansion of `Ai(-z)` in `|arg z| ≤ 2π/3 - δ`: the cosine/sine-weighted
even and odd truncations differ from `Ai(-z)` by `O` of the error envelope (DLMF 9.7.9). -/
@[dlmf 9.7.E9]
theorem airy_ai_oscillatory_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) (N M : ℕ) :
    IsBigO (airySector (2 * π / 3 - δ))
      (fun z => airyFunction .ai (-z) - airyOscApprox .ai N M z)
      (airyOscError .ai N M) := by
  have hπ := Real.pi_pos
  obtain ⟨u4, um4, u3, um3, u2, um2, u12⟩ := airyRot_u_powers
  set u := exp (π * I / 12) with hu
  have hu0 : u ≠ 0 := exp_ne_zero _
  refine airyRot_osc_bound (E := airyRot_even fun w => airyAi w / airyPrefactor .ai w)
    (O := airyRot_odd fun w => airyAi w / airyPrefactor .ai w)
    (P := airyOscSum false 0 N) (Q := airyOscSum false 1 M)
    (exp (π * I / 4) / 2) (exp (-(π * I / 4)) / 2) ?_ ?_ ?_ ?_
  · exact (airyRot_ai_parts hδ hδ' N M).1
  · exact (airyRot_ai_parts hδ hδ' N M).2
  · filter_upwards [airyRot_eventually_arg (2 * π / 3 - δ)] with z hz
    have hz0 := hz.1
    have hz3 : |arg z| < 2 * π / 3 := hz.2.trans_lt (by linarith)
    obtain ⟨d1, d2, d3, d4⟩ := airyRot_third_data hz0 hz3
    have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
    have hp1 := airyRot_prefactor_ne_zero .ai (mul_ne_zero hz0 (exp_ne_zero ((π / 3 : ℝ) * I)))
    have hp2 := airyRot_prefactor_ne_zero .ai
      (mul_ne_zero hz0 (exp_ne_zero ((-(π / 3) : ℝ) * I)))
    simp only [airyFunction]
    rw [airyRot_airyAi_neg z]
    rw [show airyAi (z * exp ((π / 3 : ℝ) * I)) = airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I)) *
        (airyAi (z * exp ((π / 3 : ℝ) * I)) / airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I))) by
        field_simp,
      show airyAi (z * exp ((-(π / 3) : ℝ) * I)) =
        airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I)) *
        (airyAi (z * exp ((-(π / 3) : ℝ) * I)) /
          airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I))) by field_simp]
    rw [← mul_assoc, ← mul_assoc]
    rw [airyRot_decomp (fun w => airyAi w / airyPrefactor .ai w)]
    have ep : exp (π * I / 3) * airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I)) =
        airyOscPrefactor .ai z * (exp (π * I / 4) / 2 * exp (-(airyZetaComplex z * I))) := by
      simp only [airyPrefactor, airyOscPrefactor]
      rw [d1, d3, u4, u3]
      field_simp
      rw [hu]; ring_nf
    have em : exp (-π * I / 3) * airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I)) =
        airyOscPrefactor .ai z * (exp (-(π * I / 4)) / 2 * exp (airyZetaComplex z * I)) := by
      simp only [airyPrefactor, airyOscPrefactor]
      rw [d2, d4, um4, um3, neg_neg]
      field_simp
      rw [hu]; ring_nf
    rw [ep, em]
    ring
  · filter_upwards with z
    simp only [airyOscApprox, Complex.cos, Complex.sin]
    have e1 : exp ((airyZetaComplex z - π / 4) * I) =
        exp (-(π * I / 4)) * exp (airyZetaComplex z * I) := by
      rw [← exp_add]; congr 1; ring
    have e2 : exp (-(airyZetaComplex z - π / 4) * I) =
        exp (π * I / 4) * exp (-(airyZetaComplex z * I)) := by
      rw [← exp_add]; congr 1; ring
    rw [e1, e2]
    ring

/-- `exp ((±π/3 : ℝ) i) = exp (±πi/3)` (cast normalization). -/
theorem airyRot_exp_third_ofReal :
    exp ((π / 3 : ℝ) * I) = exp (π * I / 3) ∧ exp ((-(π / 3) : ℝ) * I) = exp (-π * I / 3) := by
  constructor <;> (congr 1; push_cast; ring)

/-- `Ai'(-z) = e^{-iπ/3} Ai'(z e^{iπ/3}) + e^{iπ/3} Ai'(z e^{-iπ/3})`. -/
theorem airyRot_airyAiDeriv_neg (z : ℂ) :
    airyAiDeriv (-z) = exp (-π * I / 3) * airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) +
      exp (π * I / 3) * airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) := by
  have h := airyRot_deriv_of_eq (f := fun z => airyAi (-z)) (f' := fun z => -airyAiDeriv (-z))
    (fun z => by simpa [Function.comp_def] using
      (hasDerivAt_airyAi (-z)).comp z (hasDerivAt_id z).neg)
    hasDerivAt_airyAi _ _ _ _ airyRot_airyAi_neg z
  obtain ⟨u4, um4, -, -, -, -, u12⟩ := airyRot_u_powers
  obtain ⟨k1, k2⟩ := airyRot_exp_third_ofReal
  rw [k1, k2] at h ⊢
  rw [u4, um4] at h ⊢
  have hu0 : exp (π * I / 12) ≠ 0 := exp_ne_zero _
  have h' : airyAiDeriv (-z) = (-(exp (π * I / 12) ^ 4 * exp (π * I / 12) ^ 4)) *
      airyAiDeriv (z * exp (π * I / 12) ^ 4) + (-((exp (π * I / 12) ^ 4)⁻¹ *
      (exp (π * I / 12) ^ 4)⁻¹)) * airyAiDeriv (z * (exp (π * I / 12) ^ 4)⁻¹) := by
    linear_combination -h
  have e1 : -(exp (π * I / 12) ^ 4 * exp (π * I / 12) ^ 4) = (exp (π * I / 12) ^ 4)⁻¹ := by
    field_simp; linear_combination -u12
  have e2 : -((exp (π * I / 12) ^ 4)⁻¹ * (exp (π * I / 12) ^ 4)⁻¹) = exp (π * I / 12) ^ 4 := by
    field_simp; linear_combination -u12
  rw [h', e1, e2]

/-- `Bi'(-z) = -e^{iπ/6} Ai'(z e^{iπ/3}) - e^{-iπ/6} Ai'(z e^{-iπ/3})`. -/
theorem airyRot_airyBiDeriv_neg (z : ℂ) :
    airyBiDeriv (-z) = -exp (π * I / 6) * airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) +
      -exp (-π * I / 6) * airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) := by
  have h := airyRot_deriv_of_eq (f := fun z => airyBi (-z)) (f' := fun z => -airyBiDeriv (-z))
    (fun z => by simpa [Function.comp_def] using
      (hasDerivAt_airyBi (-z)).comp z (hasDerivAt_id z).neg)
    hasDerivAt_airyAi _ _ _ _ airyRot_airyBi_neg z
  obtain ⟨u4, um4, -, -, u2, um2, u12⟩ := airyRot_u_powers
  obtain ⟨k1, k2⟩ := airyRot_exp_third_ofReal
  rw [k1, k2] at h ⊢
  rw [u4, um4, u2, um2] at h ⊢
  have hu0 : exp (π * I / 12) ≠ 0 := exp_ne_zero _
  have e1 : (exp (π * I / 12) ^ 2)⁻¹ * exp (π * I / 12) ^ 4 = exp (π * I / 12) ^ 2 := by
    field_simp
  have e2 : exp (π * I / 12) ^ 2 * (exp (π * I / 12) ^ 4)⁻¹ = (exp (π * I / 12) ^ 2)⁻¹ := by
    field_simp
  rw [e1, e2] at h
  linear_combination -h

/-- The even and odd parts of the normalized `Ai'` at `z e^{±iπ/3}` are approximated by the
oscillatory subseries (used for the derivatives) in `|arg z| ≤ 2π/3 - δ`. -/
lemma airyRot_aiDeriv_parts {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) (N M : ℕ) :
    (fun z => airyRot_even (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w) z -
      airyOscSum true 0 N z) =O[airySector (2 * π / 3 - δ)]
      (fun z => ((airyZetaComplex z) ^ (2 * N))⁻¹) ∧
    (fun z => airyRot_odd (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w) z -
      airyOscSum true 1 M z) =O[airySector (2 * π / 3 - δ)]
      (fun z => ((airyZetaComplex z) ^ (2 * M + 1))⁻¹) := by
  have hF := airyRot_airyAiDeriv_expansion hδ (by linarith [Real.pi_pos])
  have hE := (airyRot_even_expansion hδ hF) N
  have hO := (airyRot_odd_expansion hδ hF) M
  refine ⟨?_, ?_⟩
  · refine hE.congr_left fun z => ?_
    dsimp only
    rw [airyRot_sum_even (d := fun k => ((airyV k : ℝ) : ℂ)) _
      (fun j => by simpa using (airyRot_coeff_parity .aiDeriv (Or.inr rfl) j).1) N z]
    simp [airyOscSum]
  · refine hO.congr_left fun z => ?_
    dsimp only
    rw [airyRot_sum_odd (d := fun k => ((airyV k : ℝ) : ℂ)) _
      (fun j => by simpa using (airyRot_coeff_parity .aiDeriv (Or.inr rfl) j).2) M z]
    simp [airyOscSum]

/-- The oscillatory expansion of `Ai'(-z)` in `|arg z| ≤ 2π/3 - δ`, with error `O` of the
envelope `airyOscError` (DLMF 9.7.10). -/
@[dlmf 9.7.E10]
theorem airy_aiDeriv_oscillatory_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) (N M : ℕ) :
    IsBigO (airySector (2 * π / 3 - δ))
      (fun z => airyFunction .aiDeriv (-z) - airyOscApprox .aiDeriv N M z)
      (airyOscError .aiDeriv N M) := by
  have hπ := Real.pi_pos
  obtain ⟨u4, um4, u3, um3, u2, um2, u12⟩ := airyRot_u_powers
  set u := exp (π * I / 12) with hu
  have hu0 : u ≠ 0 := exp_ne_zero _
  refine airyRot_osc_bound (E := airyRot_even fun w => airyAiDeriv w / airyPrefactor .aiDeriv w)
    (O := airyRot_odd fun w => airyAiDeriv w / airyPrefactor .aiDeriv w)
    (P := airyOscSum true 0 N) (Q := airyOscSum true 1 M)
    (-(exp (-(π * I / 4)) / 2)) (-(exp (π * I / 4) / 2)) ?_ ?_ ?_ ?_
  · exact (airyRot_aiDeriv_parts hδ hδ' N M).1
  · exact (airyRot_aiDeriv_parts hδ hδ' N M).2
  · filter_upwards [airyRot_eventually_arg (2 * π / 3 - δ)] with z hz
    have hz0 := hz.1
    have hz3 : |arg z| < 2 * π / 3 := hz.2.trans_lt (by linarith)
    obtain ⟨d1, d2, d3, d4⟩ := airyRot_third_data hz0 hz3
    have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
    have hp1 := airyRot_prefactor_ne_zero .aiDeriv
      (mul_ne_zero hz0 (exp_ne_zero ((π / 3 : ℝ) * I)))
    have hp2 := airyRot_prefactor_ne_zero .aiDeriv
      (mul_ne_zero hz0 (exp_ne_zero ((-(π / 3) : ℝ) * I)))
    simp only [airyFunction]
    rw [airyRot_airyAiDeriv_neg z]
    rw [show airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) =
        airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I)) *
        (airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) /
          airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I))) by field_simp,
      show airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) =
        airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I)) *
        (airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) /
          airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I))) by field_simp]
    rw [← mul_assoc, ← mul_assoc]
    rw [airyRot_decomp (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w)]
    have ep : exp (-π * I / 3) * airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I)) =
        airyOscPrefactor .aiDeriv z *
          (-(exp (-(π * I / 4)) / 2) * exp (-(airyZetaComplex z * I))) := by
      simp only [airyPrefactor, airyOscPrefactor]
      rw [d1, d3, ← hu, um4, um3]
      field_simp
    have em : exp (π * I / 3) * airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I)) =
        airyOscPrefactor .aiDeriv z * (-(exp (π * I / 4) / 2) * exp (airyZetaComplex z * I)) := by
      simp only [airyPrefactor, airyOscPrefactor]
      rw [d2, d4, ← hu, u4, u3, neg_neg]
      field_simp
    rw [ep, em]
    ring
  · filter_upwards with z
    simp only [airyOscApprox]
    rw [show cos (airyZetaComplex z - π / 4) = sin (airyZetaComplex z - π / 4 + π / 2) from
        (Complex.sin_add_pi_div_two _).symm,
      show sin (airyZetaComplex z - π / 4) = -cos (airyZetaComplex z - π / 4 + π / 2) by
        rw [Complex.cos_add_pi_div_two]; ring]
    simp only [Complex.cos, Complex.sin]
    have e1 : exp ((airyZetaComplex z - π / 4 + π / 2) * I) =
        exp (π * I / 4) * exp (airyZetaComplex z * I) := by
      rw [← exp_add]; congr 1; ring
    have e2 : exp (-(airyZetaComplex z - π / 4 + π / 2) * I) =
        exp (-(π * I / 4)) * exp (-(airyZetaComplex z * I)) := by
      rw [← exp_add]; congr 1; ring
    rw [e1, e2]
    ring

/-- The oscillatory expansion of `Bi(-z)` in `|arg z| ≤ 2π/3 - δ`, with error `O` of the
envelope `airyOscError` (DLMF 9.7.11). -/
@[dlmf 9.7.E11]
theorem airy_bi_oscillatory_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) (N M : ℕ) :
    IsBigO (airySector (2 * π / 3 - δ))
      (fun z => airyFunction .bi (-z) - airyOscApprox .bi N M z)
      (airyOscError .bi N M) := by
  have hπ := Real.pi_pos
  obtain ⟨u4, um4, u3, um3, u2, um2, u12⟩ := airyRot_u_powers
  set u := exp (π * I / 12) with hu
  have hu0 : u ≠ 0 := exp_ne_zero _
  refine airyRot_osc_bound (E := airyRot_even fun w => airyAi w / airyPrefactor .ai w)
    (O := airyRot_odd fun w => airyAi w / airyPrefactor .ai w)
    (P := airyOscSum false 0 N) (Q := airyOscSum false 1 M)
    (exp (-(π * I / 4)) / 2) (exp (π * I / 4) / 2) ?_ ?_ ?_ ?_
  · exact (airyRot_ai_parts hδ hδ' N M).1
  · exact (airyRot_ai_parts hδ hδ' N M).2
  · filter_upwards [airyRot_eventually_arg (2 * π / 3 - δ)] with z hz
    have hz0 := hz.1
    have hz3 : |arg z| < 2 * π / 3 := hz.2.trans_lt (by linarith)
    obtain ⟨d1, d2, d3, d4⟩ := airyRot_third_data hz0 hz3
    have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
    have hp1 := airyRot_prefactor_ne_zero .ai
      (mul_ne_zero hz0 (exp_ne_zero ((π / 3 : ℝ) * I)))
    have hp2 := airyRot_prefactor_ne_zero .ai
      (mul_ne_zero hz0 (exp_ne_zero ((-(π / 3) : ℝ) * I)))
    simp only [airyFunction]
    rw [airyRot_airyBi_neg z]
    rw [show airyAi (z * exp ((π / 3 : ℝ) * I)) =
        airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I)) *
        (airyAi (z * exp ((π / 3 : ℝ) * I)) /
          airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I))) by field_simp,
      show airyAi (z * exp ((-(π / 3) : ℝ) * I)) =
        airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I)) *
        (airyAi (z * exp ((-(π / 3) : ℝ) * I)) /
          airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I))) by field_simp]
    rw [← mul_assoc, ← mul_assoc]
    rw [airyRot_decomp (fun w => airyAi w / airyPrefactor .ai w)]
    have ep : exp (-π * I / 6) * airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I)) =
        airyOscPrefactor .bi z *
          (exp (-(π * I / 4)) / 2 * exp (-(airyZetaComplex z * I))) := by
      simp only [airyPrefactor, airyOscPrefactor]
      rw [d1, d3, ← hu, um2, um3]
      field_simp
    have em : exp (π * I / 6) * airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I)) =
        airyOscPrefactor .bi z * (exp (π * I / 4) / 2 * exp (airyZetaComplex z * I)) := by
      simp only [airyPrefactor, airyOscPrefactor]
      rw [d2, d4, ← hu, u2, u3, neg_neg]
      field_simp
    rw [ep, em]
    ring
  · filter_upwards with z
    simp only [airyOscApprox]
    rw [show cos (airyZetaComplex z - π / 4) = sin (airyZetaComplex z - π / 4 + π / 2) from
        (Complex.sin_add_pi_div_two _).symm,
      show sin (airyZetaComplex z - π / 4) = -cos (airyZetaComplex z - π / 4 + π / 2) by
        rw [Complex.cos_add_pi_div_two]; ring]
    simp only [Complex.cos, Complex.sin]
    have e1 : exp ((airyZetaComplex z - π / 4 + π / 2) * I) =
        exp (π * I / 4) * exp (airyZetaComplex z * I) := by
      rw [← exp_add]; congr 1; ring
    have e2 : exp (-(airyZetaComplex z - π / 4 + π / 2) * I) =
        exp (-(π * I / 4)) * exp (-(airyZetaComplex z * I)) := by
      rw [← exp_add]; congr 1; ring
    rw [e1, e2]
    ring

/-- The oscillatory expansion of `Bi'(-z)` in `|arg z| ≤ 2π/3 - δ`, with error `O` of the
envelope `airyOscError` (DLMF 9.7.12). -/
@[dlmf 9.7.E12]
theorem airy_biDeriv_oscillatory_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) (N M : ℕ) :
    IsBigO (airySector (2 * π / 3 - δ))
      (fun z => airyFunction .biDeriv (-z) - airyOscApprox .biDeriv N M z)
      (airyOscError .biDeriv N M) := by
  have hπ := Real.pi_pos
  obtain ⟨u4, um4, u3, um3, u2, um2, u12⟩ := airyRot_u_powers
  set u := exp (π * I / 12) with hu
  have hu0 : u ≠ 0 := exp_ne_zero _
  refine airyRot_osc_bound (E := airyRot_even fun w => airyAiDeriv w / airyPrefactor .aiDeriv w)
    (O := airyRot_odd fun w => airyAiDeriv w / airyPrefactor .aiDeriv w)
    (P := airyOscSum true 0 N) (Q := airyOscSum true 1 M)
    (exp (π * I / 4) / 2) (exp (-(π * I / 4)) / 2) ?_ ?_ ?_ ?_
  · exact (airyRot_aiDeriv_parts hδ hδ' N M).1
  · exact (airyRot_aiDeriv_parts hδ hδ' N M).2
  · filter_upwards [airyRot_eventually_arg (2 * π / 3 - δ)] with z hz
    have hz0 := hz.1
    have hz3 : |arg z| < 2 * π / 3 := hz.2.trans_lt (by linarith)
    obtain ⟨d1, d2, d3, d4⟩ := airyRot_third_data hz0 hz3
    have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
    have hp1 := airyRot_prefactor_ne_zero .aiDeriv
      (mul_ne_zero hz0 (exp_ne_zero ((π / 3 : ℝ) * I)))
    have hp2 := airyRot_prefactor_ne_zero .aiDeriv
      (mul_ne_zero hz0 (exp_ne_zero ((-(π / 3) : ℝ) * I)))
    simp only [airyFunction]
    rw [airyRot_airyBiDeriv_neg z]
    rw [show airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) =
        airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I)) *
        (airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) /
          airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I))) by field_simp,
      show airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) =
        airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I)) *
        (airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) /
          airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I))) by field_simp]
    rw [← mul_assoc, ← mul_assoc]
    rw [airyRot_decomp (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w)]
    have ep : -exp (π * I / 6) * airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I)) =
        airyOscPrefactor .biDeriv z *
          (exp (π * I / 4) / 2 * exp (-(airyZetaComplex z * I))) := by
      simp only [airyPrefactor, airyOscPrefactor]
      rw [d1, d3, ← hu, u2, u3]
      field_simp
    have em : -exp (-π * I / 6) * airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I)) =
        airyOscPrefactor .biDeriv z * (exp (-(π * I / 4)) / 2 * exp (airyZetaComplex z * I)) := by
      simp only [airyPrefactor, airyOscPrefactor]
      rw [d2, d4, ← hu, um2, um3, neg_neg]
      field_simp
    rw [ep, em]
    ring
  · filter_upwards with z
    simp only [airyOscApprox, Complex.cos, Complex.sin]
    have e1 : exp ((airyZetaComplex z - π / 4) * I) =
        exp (-(π * I / 4)) * exp (airyZetaComplex z * I) := by
      rw [← exp_add]; congr 1; ring
    have e2 : exp (-(airyZetaComplex z - π / 4) * I) =
        exp (π * I / 4) * exp (-(airyZetaComplex z * I)) := by
      rw [← exp_add]; congr 1; ring
    rw [e1, e2]
    ring

/-- `(e^{πi/12})^6 = i`. -/
theorem airyRot_u_six : exp (π * I / 12) ^ 6 = I := by
  rw [← exp_nat_mul, show ((6 : ℕ) : ℂ) * (π * I / 12) = (π / 2 : ℂ) * I by push_cast; ring,
    exp_pi_div_two_mul_I]

/-- `Bi(z e^{iπ/3}) = i Ai(z e^{iπ/3}) + 2 e^{-iπ/6} Ai(z e^{-iπ/3})`. -/
theorem airyRot_airyBi_rot_pos (z : ℂ) :
    airyBi (z * exp (π * I / 3)) = I * airyAi (z * exp ((π / 3 : ℝ) * I)) +
      2 * exp (-π * I / 6) * airyAi (z * exp ((-(π / 3) : ℝ) * I)) := by
  rw [airyBi_eq_airyAi_omega,
    show z * exp (π * I / 3) * exp (-(2 * π * I / 3)) = z * exp ((-(π / 3) : ℝ) * I) by
      rw [mul_assoc, ← exp_add]; congr 2; push_cast; ring,
    show z * exp (π * I / 3) * exp (2 * π * I / 3) = -z by
      rw [mul_assoc, ← exp_add, show π * I / 3 + 2 * π * I / 3 = π * I by ring, exp_pi_mul_I]
      ring,
    airyRot_airyAi_neg z]
  obtain ⟨u4, um4, -, -, u2, um2, u12⟩ := airyRot_u_powers
  have k : exp (-(π * I / 6)) = exp (-π * I / 6) := by congr 1; ring
  have hu6 := airyRot_u_six
  rw [k, u4, um4, u2, um2]
  set u := exp (π * I / 12)
  set A := airyAi (z * exp ((π / 3 : ℝ) * I))
  set B := airyAi (z * exp ((-(π / 3) : ℝ) * I))
  have hu0 : u ≠ 0 := exp_ne_zero _
  rw [← hu6]
  field_simp
  ring

/-- `Bi(z e^{-iπ/3}) = 2 e^{iπ/6} Ai(z e^{iπ/3}) - i Ai(z e^{-iπ/3})`. -/
theorem airyRot_airyBi_rot_neg (z : ℂ) :
    airyBi (z * exp (-(π * I / 3))) = 2 * exp (π * I / 6) * airyAi (z * exp ((π / 3 : ℝ) * I)) -
      I * airyAi (z * exp ((-(π / 3) : ℝ) * I)) := by
  rw [airyBi_eq_airyAi_omega,
    show z * exp (-(π * I / 3)) * exp (2 * π * I / 3) = z * exp ((π / 3 : ℝ) * I) by
      rw [mul_assoc, ← exp_add]; congr 2; push_cast; ring,
    show z * exp (-(π * I / 3)) * exp (-(2 * π * I / 3)) = -z by
      rw [mul_assoc, ← exp_add, show -(π * I / 3) + -(2 * π * I / 3) = -(π * I) by ring,
        exp_neg, exp_pi_mul_I]
      ring,
    airyRot_airyAi_neg z]
  obtain ⟨u4, um4, -, -, u2, um2, u12⟩ := airyRot_u_powers
  have k : exp (-(π * I / 6)) = exp (-π * I / 6) := by congr 1; ring
  have hu6 := airyRot_u_six
  rw [k, u4, um4, u2, um2]
  set u := exp (π * I / 12)
  set A := airyAi (z * exp ((π / 3 : ℝ) * I))
  set B := airyAi (z * exp ((-(π / 3) : ℝ) * I))
  have hu0 : u ≠ 0 := exp_ne_zero _
  rw [← hu6]
  field_simp
  linear_combination B * u12

/-- `exp (log 2 / 2) = √2`. -/
theorem airyRot_exp_half_log_two : exp ((Real.log 2 : ℂ) / 2) = (Real.sqrt 2 : ℂ) := by
  rw [show (Real.log 2 : ℂ) / 2 = ((Real.log 2 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_exp]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos two_pos]; ring_nf

/-- `(2/π)^{1/2} = √2/√π` in `ℂ`. -/
theorem airyRot_two_div_pi_cpow :
    (2 / π : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt 2 : ℂ) / (Real.sqrt π : ℂ) := by
  rw [show (2 / π : ℂ) = ((2 / π : ℝ) : ℂ) by push_cast; ring,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_div' _ Real.pi_pos.le]
  push_cast; ring

/-- `‖exp (ε c i)‖ = 1` for real `ε, c`. -/
theorem airyRot_norm_exp_real_mul (ε : ℝ) (c : ℝ) : ‖exp (ε * (c * I))‖ = 1 := by
  rw [show (ε : ℂ) * (c * I) = ((ε * c : ℝ) : ℂ) * I by push_cast; ring, norm_exp_ofReal_mul_I]

/-- `‖(2/π)^{1/2}‖ = √2/√π`. -/
theorem airyRot_norm_two_div_pi_cpow :
    ‖(2 / π : ℂ) ^ (1 / 2 : ℂ)‖ = Real.sqrt 2 / Real.sqrt π := by
  rw [airyRot_two_div_pi_cpow, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (Real.sqrt_nonneg _)]

/-- The prefactor of 9.7.13 is `√2` times that of 9.7.11 in norm. -/
theorem airyRot_norm_rot_pref (ε : ℝ) (z : ℂ) :
    ‖(2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (ε * (π * I / 6)) * z ^ (-1 / 4 : ℂ)‖ =
      Real.sqrt 2 * ‖airyOscPrefactor .bi z‖ := by
  rw [show (ε : ℂ) * (π * I / 6) = ε * (((π / 6 : ℝ) : ℂ) * I) by push_cast; ring,
    norm_mul, norm_mul, airyRot_norm_exp_real_mul, airyRot_norm_two_div_pi_cpow,
    show (-1 / 4 : ℂ) = -(1 / 4) by ring, cpow_neg, airyOscPrefactor, norm_div, norm_mul,
    norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  simp only [norm_one]
  ring

/-- The prefactor of 9.7.14 is `√2` times that of 9.7.12 in norm. -/
theorem airyRot_norm_rot_pref' (ε : ℝ) (z : ℂ) :
    ‖(2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (-ε * (π * I / 6)) * z ^ (1 / 4 : ℂ)‖ =
      Real.sqrt 2 * ‖airyOscPrefactor .biDeriv z‖ := by
  rw [show (-ε : ℂ) * (π * I / 6) = ((-ε : ℝ) : ℂ) * (((π / 6 : ℝ) : ℂ) * I) by push_cast; ring,
    norm_mul, norm_mul, airyRot_norm_exp_real_mul, airyRot_norm_two_div_pi_cpow,
    airyOscPrefactor, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  ring

/-- Passing from the `√2`-scaled envelope to `airyOscError`. -/
theorem airyRot_envelope {l : Filter ℂ} (kind : AiryKind) (pref : ℂ → ℂ) (N M : ℕ)
    (h : ∀ z, ‖pref z‖ = Real.sqrt 2 * ‖airyOscPrefactor kind z‖) :
    (fun z => ‖pref z‖ * Real.exp |(airyZetaComplex z).im| *
      (‖airyZetaComplex z‖ ^ (-(2 * N : ℤ)) + ‖airyZetaComplex z‖ ^ (-(2 * M + 1 : ℤ))))
      =O[l] airyOscError kind N M := by
  refine ((isBigO_refl (airyOscError kind N M) l).const_mul_left (Real.sqrt 2)).congr_left
    fun z => ?_
  rw [h, airyOscError]; ring

end DLMF.Airy
end
