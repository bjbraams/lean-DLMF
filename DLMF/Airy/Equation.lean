/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Framework
public import DLMF.Airy.ErrorBoundTools

/-!
# Airy equations, connection formulas and explicit Maclaurin series

Statements acquired from the NIST DLMF, checked 2026-10-19.
New statements are initially admitted; existing proved Airy results are retained.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF.Confluent
open scoped Real Topology Nat
namespace DLMF.Airy

/-- isAirySol rotated (DLMF 9.2.2). -/
@[dlmf 9.2.E2]
theorem isAirySol_rotated {ω : ℂ} (hω : ω ^ 3 = 1) :
    IsAirySol (fun z => airyAi (ω * z)) (fun z => ω * airyAiDeriv (ω * z)) := by
  intro z
  have h1 := (hasDerivAt_airyAi (ω * z)).comp z ((hasDerivAt_id z).const_mul ω)
  have h2 := ((hasDerivAt_airyAiDeriv (ω * z)).comp z ((hasDerivAt_id z).const_mul ω)).const_mul ω
  change HasDerivAt (fun z => airyAi (ω * z)) _ z at h1
  change HasDerivAt (fun z => ω * airyAiDeriv (ω * z)) _ z at h2
  constructor
  · exact h1.congr_deriv (by ring)
  · exact h2.congr_deriv (by linear_combination z * airyAi (ω * z) * hω)

/-- Every entire Airy solution is a linear combination of Ai and Bi. -/
theorem airy_general_solution {w w' : ℂ → ℂ} (hw : IsAirySol w w') :
    ∃ a b : ℂ, ∀ z, w z = a * airyAi z + b * airyBi z := by
  let a : ℂ := π * (w 0 * airyBiDeriv 0 - w' 0 * airyBi 0)
  let b : ℂ := π * (airyAi 0 * w' 0 - airyAiDeriv 0 * w 0)
  refine ⟨a, b, ?_⟩
  have hs : IsAirySol (fun z => a * airyAi z + b * airyBi z)
      (fun z => a * airyAiDeriv z + b * airyBiDeriv z) := fun z => ⟨
    ((hasDerivAt_airyAi z).const_mul a).add ((hasDerivAt_airyBi z).const_mul b),
    (((hasDerivAt_airyAiDeriv z).const_mul a).add
      ((hasDerivAt_airyBiDeriv z).const_mul b)).congr_deriv (by ring)⟩
  have hW := wronskian_airyAi_airyBi 0
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have h0 : w 0 = a * airyAi 0 + b * airyBi 0 := by
    dsimp only [a, b]
    field_simp at hW
    linear_combination -(w 0) * hW
  have h1 : w' 0 = a * airyAiDeriv 0 + b * airyBiDeriv 0 := by
    dsimp only [a, b]
    field_simp at hW
    linear_combination -(w' 0) * hW
  exact hw.eq_of_initial hs h0 h1

/-- The initial-value product, normalized using the already proved Airy Wronskian. -/
theorem airyAi_zero_mul_airyAiDeriv_zero :
    airyAi 0 * airyAiDeriv 0 = -1 / (2 * π * Real.sqrt 3) := by
  have hB : airyBi 0 = (Real.sqrt 3 : ℂ) * airyAi 0 := by
    simp only [airyBi, airyAi, airyG_zero, mul_zero, add_zero, sub_zero]
  have hB' : airyBiDeriv 0 = -(Real.sqrt 3 : ℂ) * airyAiDeriv 0 := by
    simp only [airyBiDeriv, airyAiDeriv, airyFDeriv_zero, mul_zero, zero_add, zero_sub]
    ring
  have hW := wronskian_airyAi_airyBi 0
  rw [hB, hB'] at hW
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  field_simp at hW ⊢
  linear_combination -hW

/-- wronskian airyAi rotated (DLMF 9.2.8). -/
@[dlmf 9.2.E8]
theorem wronskian_airyAi_rotated (z : ℂ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    airyAi z * (-ε * (2 * π * I / 3) |>.exp) * airyAiDeriv (z * exp (-ε * (2 * π * I / 3))) -
      airyAiDeriv z * airyAi (z * exp (-ε * (2 * π * I / 3))) =
      exp (ε * (π * I / 6)) / (2 * π) := by
  let ω : ℂ := exp (-ε * (2 * π * I / 3))
  have hω : ω ^ 3 = 1 := by
    rcases hε with rfl | rfl
    · simpa [ω] using omega_recip_cube
    · simpa [ω] using omega_cube
  have hr := isAirySol_airyAi.wronskian_eq (isAirySol_rotated hω) z
  simp only [mul_zero] at hr
  have he : ω - 1 = -(Real.sqrt 3 : ℂ) * exp (ε * (π * I / 6)) := by
    rcases hε with rfl | rfl
    · simp only [ω, ofReal_one, one_mul, neg_mul]
      rw [exp_neg_two_pi_I_div_three, exp_pi_I_div_six]
      push_cast
      linear_combination sqrt_three_sq / 2
    · simp only [ω, ofReal_neg, ofReal_one, neg_mul, one_mul, neg_neg]
      rw [exp_two_pi_I_div_three, exp_neg_pi_I_div_six]
      push_cast
      linear_combination sqrt_three_sq / 2
  change airyAi z * ω * airyAiDeriv (z * ω) - airyAiDeriv z * airyAi (z * ω) = _
  calc
    _ = (ω - 1) * (airyAi 0 * airyAiDeriv 0) := by
      rw [mul_comm z ω]
      linear_combination hr
    _ = _ := by
      rw [he, airyAi_zero_mul_airyAiDeriv_zero]
      have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
      field_simp

/-- wronskian airyAi rotations (DLMF 9.2.9). -/
@[dlmf 9.2.E9]
theorem wronskian_airyAi_rotations (z : ℂ) :
    airyAi (z * exp (-2 * π * I / 3)) * exp (2 * π * I / 3) *
        airyAiDeriv (z * exp (2 * π * I / 3)) -
      exp (-2 * π * I / 3) * airyAiDeriv (z * exp (-2 * π * I / 3)) *
        airyAi (z * exp (2 * π * I / 3)) = 1 / (2 * π * I) := by
  have hr := (isAirySol_rotated omega_recip_cube).wronskian_eq (isAirySol_rotated omega_cube) z
  simp only [mul_zero] at hr
  have he : exp (2 * π * I / 3) - exp (-(2 * π * I / 3)) = (Real.sqrt 3 : ℂ) * I := by
    rw [exp_two_pi_I_div_three, exp_neg_two_pi_I_div_three]
    push_cast
    ring
  calc
    _ = (exp (2 * π * I / 3) - exp (-(2 * π * I / 3))) * (airyAi 0 * airyAiDeriv 0) := by
      simp only [neg_mul, neg_div] at hr ⊢
      rw [mul_comm z (exp (2 * π * I / 3)), mul_comm z (exp (-(2 * π * I / 3)))]
      linear_combination hr
    _ = _ := by
      rw [he, airyAi_zero_mul_airyAiDeriv_zero]
      have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
      have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
      field_simp
      norm_num [I_sq]

/-- airyAi neg connection (DLMF 9.2.14). -/
@[dlmf 9.2.E14]
theorem airyAi_neg_connection (z : ℂ) :
    airyAi (-z) = exp (π * I / 3) * airyAi (z * exp (π * I / 3)) +
      exp (-π * I / 3) * airyAi (z * exp (-π * I / 3)) := by
  exact airyRot_neg_connection_ai z

/-- airyBi neg connection (DLMF 9.2.15). -/
@[dlmf 9.2.E15]
theorem airyBi_neg_connection (z : ℂ) :
    airyBi (-z) = exp (-π * I / 6) * airyAi (z * exp (π * I / 3)) +
      exp (π * I / 6) * airyAi (z * exp (-π * I / 3)) := by
  exact airyRot_neg_connection_bi z

/-- airy log derivative riccati (DLMF 9.2.16). -/
@[dlmf 9.2.E16]
theorem airy_log_derivative_riccati {w w' : ℂ → ℂ} (hw : IsAirySol w w') {z : ℂ} (hz : w z ≠ 0) :
    HasDerivAt (fun t => w' t / w t) (z - (w' z / w z) ^ 2) z := by
  have h := (hw z).2.div (hw z).1 hz
  exact h.congr_deriv (by field_simp)

/-- The regularized `₀F₁` series as a `HasSum`. -/
theorem hasSum_reg0F1 (c w : ℂ) :
    HasSum (fun k : ℕ => w ^ k / (k ! * Gamma (c + k))) (regularizedHGFun ∅ {c} w) := by
  have hr : (regularizedHGFunSeries (∅ : Multiset ℂ) {c}).radius = ⊤ :=
    radius_regularizedHGFunSeries_eq_top (by simp)
  have hp : HasFPowerSeriesOnBall (regularizedHGFun ∅ {c})
      (regularizedHGFunSeries (∅ : Multiset ℂ) {c}) 0 ⊤ := by
    rw [← hr]
    exact (regularizedHGFunSeries (∅ : Multiset ℂ) {c}).hasFPowerSeriesOnBall (by rw [hr]; simp)
  refine (hp.hasSum_mul_pow (by simp)).congr_fun fun k => ?_
  simp only [DLMF.Bessel.regularizedHGFunCoeff_empty]
  ring

/-- Triplication: `(3k)! = 27^k k! (1/3)_k (2/3)_k`. -/
theorem factorial_three_mul (k : ℕ) :
    (((3 * k) ! : ℕ) : ℂ) = 27 ^ k * k ! * poch (1 / 3) k * poch (2 / 3) k := by
  induction k with
  | zero => simp [poch]
  | succ k ih =>
    rw [show 3 * (k + 1) = 3 * k + 2 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast
    rw [ih]
    simp only [poch, ascPochhammer_succ_eval, Nat.factorial_succ]
    push_cast
    ring

/-- `(3k+1)! = 27^k k! (2/3)_k (4/3)_k`. -/
theorem factorial_three_mul_add_one (k : ℕ) :
    (((3 * k + 1) ! : ℕ) : ℂ) = 27 ^ k * k ! * poch (2 / 3) k * poch (4 / 3) k := by
  induction k with
  | zero => simp [poch]
  | succ k ih =>
    rw [show 3 * (k + 1) + 1 = 3 * k + 1 + 2 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast
    rw [ih]
    simp only [poch, ascPochhammer_succ_eval, Nat.factorial_succ]
    push_cast
    ring

/-- `(3k+2)! = 2 · 27^k k! (4/3)_k (5/3)_k`. -/
theorem factorial_three_mul_add_two (k : ℕ) :
    (((3 * k + 2) ! : ℕ) : ℂ) = 2 * 27 ^ k * k ! * poch (4 / 3) k * poch (5 / 3) k := by
  induction k with
  | zero => simp [poch]
  | succ k ih =>
    rw [show 3 * (k + 1) + 2 = 3 * k + 2 + 2 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast
    rw [ih]
    simp only [poch, ascPochhammer_succ_eval, Nat.factorial_succ]
    push_cast
    ring

/-- `(c)_k ≠ 0` for `0 < re c`. -/
theorem poch_ne_zero_of_re_pos {c : ℂ} (hc : 0 < c.re) (k : ℕ) : poch c k ≠ 0 := by
  intro h
  have h2 := DLMF.Gamma.Gamma_add_nat_eq_poch_mul_Gamma hc k
  rw [h, zero_mul] at h2
  exact Gamma_ne_zero_of_re_pos (by simp; linarith [k.cast_nonneg (α := ℝ)]) h2

/-- `Γ(4/3) = Γ(1/3)/3`. -/
theorem Gamma_four_thirds : Gamma (4 / 3) = 1 / 3 * Gamma (1 / 3) := by
  rw [show (4 / 3 : ℂ) = 1 / 3 + 1 by norm_num, Complex.Gamma_add_one _ (by norm_num)]

/-- `Γ(5/3) = (2/3) Γ(2/3)`. -/
theorem Gamma_five_thirds : Gamma (5 / 3) = 2 / 3 * Gamma (2 / 3) := by
  rw [show (5 / 3 : ℂ) = 2 / 3 + 1 by norm_num, Complex.Gamma_add_one _ (by norm_num)]

/-- Maclaurin series of `airyF`. -/
theorem hasSum_airyF_maclaurin (z : ℂ) :
    HasSum (fun k : ℕ => (Gamma (2 / 3))⁻¹ * (3 : ℂ) ^ k * poch (1 / 3) k / (3 * k)! *
      z ^ (3 * k)) (airyF z) := by
  refine (hasSum_reg0F1 (2 / 3) (z ^ 3 / 9)).congr_fun fun k => ?_
  rw [factorial_three_mul, DLMF.Gamma.Gamma_add_nat_eq_poch_mul_Gamma (by norm_num)]
  have h1 := poch_ne_zero_of_re_pos (c := 1 / 3) (by norm_num) k
  have h2 := poch_ne_zero_of_re_pos (c := 2 / 3) (by norm_num) k
  have h3 : Gamma (2 / 3) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [pow_mul, show (27 : ℂ) = 3 * 9 by norm_num, mul_pow, div_pow]
  field_simp

/-- Maclaurin series of `airyG`. -/
theorem hasSum_airyG_maclaurin (z : ℂ) :
    HasSum (fun k : ℕ => (Gamma (4 / 3))⁻¹ * (3 : ℂ) ^ k * poch (2 / 3) k / (3 * k + 1)! *
      z ^ (3 * k + 1)) (airyG z) := by
  refine ((hasSum_reg0F1 (4 / 3) (z ^ 3 / 9)).mul_left z).congr_fun fun k => ?_
  rw [factorial_three_mul_add_one, DLMF.Gamma.Gamma_add_nat_eq_poch_mul_Gamma (by norm_num)]
  have h1 := poch_ne_zero_of_re_pos (c := 4 / 3) (by norm_num) k
  have h2 := poch_ne_zero_of_re_pos (c := 2 / 3) (by norm_num) k
  have h3 : Gamma (4 / 3) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [pow_succ, pow_mul, show (27 : ℂ) = 3 * 9 by norm_num, mul_pow, div_pow]
  field_simp

/-- Maclaurin series of `airyFDeriv`. -/
theorem hasSum_airyFDeriv_maclaurin (z : ℂ) :
    HasSum (fun k : ℕ => (Gamma (2 / 3))⁻¹ * (3 : ℂ) ^ k * poch (4 / 3) k / (3 * k + 2)! *
      z ^ (3 * k + 2)) (airyFDeriv z) := by
  refine ((hasSum_reg0F1 (5 / 3) (z ^ 3 / 9)).mul_left (z ^ 2 / 3)).congr_fun fun k => ?_
  rw [factorial_three_mul_add_two, DLMF.Gamma.Gamma_add_nat_eq_poch_mul_Gamma (by norm_num), Gamma_five_thirds]
  have h1 := poch_ne_zero_of_re_pos (c := 4 / 3) (by norm_num) k
  have h2 := poch_ne_zero_of_re_pos (c := 5 / 3) (by norm_num) k
  have h3 : Gamma (2 / 3) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [pow_add, pow_mul, show (27 : ℂ) = 3 * 9 by norm_num, mul_pow, div_pow]
  field_simp

/-- `G′(z) = 3 ₀F̃₁(;1/3;z³/9)`. -/
theorem airyGDeriv_eq (z : ℂ) :
    airyGDeriv z = 3 * regularizedHGFun (∅ : Multiset ℂ) {1 / 3} (z ^ 3 / 9) := by
  rw [airyGDeriv, reg0F1_contiguous' (c := 1 / 3) (c₁ := 4 / 3) (c₂ := 7 / 3) (by norm_num)
    (by norm_num)]
  ring

/-- Maclaurin series of `airyGDeriv`. -/
theorem hasSum_airyGDeriv_maclaurin (z : ℂ) :
    HasSum (fun k : ℕ => (Gamma (4 / 3))⁻¹ * (3 : ℂ) ^ k * poch (2 / 3) k / (3 * k)! *
      z ^ (3 * k)) (airyGDeriv z) := by
  rw [airyGDeriv_eq]
  refine ((hasSum_reg0F1 (1 / 3) (z ^ 3 / 9)).mul_left 3).congr_fun fun k => ?_
  rw [factorial_three_mul, DLMF.Gamma.Gamma_add_nat_eq_poch_mul_Gamma (by norm_num), Gamma_four_thirds]
  have h1 := poch_ne_zero_of_re_pos (c := 1 / 3) (by norm_num) k
  have h2 := poch_ne_zero_of_re_pos (c := 2 / 3) (by norm_num) k
  have h3 : Gamma (1 / 3) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [pow_mul, show (27 : ℂ) = 3 * 9 by norm_num, mul_pow, div_pow]
  field_simp

/-- `G′(0) = 1/Γ(4/3)`. -/
theorem airyGDeriv_zero' : airyGDeriv 0 = (Gamma (4 / 3))⁻¹ := by
  rw [airyGDeriv_zero, Gamma_four_thirds]
  have h3 : Gamma (1 / 3) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  field_simp

/-- hasSum airyAi maclaurin (DLMF 9.4.1). -/
@[dlmf 9.4.E1]
theorem hasSum_airyAi_maclaurin (z : ℂ) :
    HasSum (fun k : ℕ => airyAi 0 * (3 : ℂ) ^ k * poch (1 / 3) k / (3 * k).factorial * z ^ (3 * k) +
      airyAiDeriv 0 * (3 : ℂ) ^ k * poch (2 / 3) k / (3 * k + 1).factorial * z ^ (3 * k + 1))
      (airyAi z) := by
  convert ((hasSum_airyF_maclaurin z).mul_left (((3 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)).add
    ((hasSum_airyG_maclaurin z).mul_left (-(((3 : ℝ) ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ))) using 1
  · funext k
    simp only [airyAi, airyAiDeriv, airyF_zero, airyG_zero, airyFDeriv_zero, airyGDeriv_zero']
    ring
  · simp only [airyAi]; ring

/-- hasSum airyAiDeriv maclaurin (DLMF 9.4.2). -/
@[dlmf 9.4.E2]
theorem hasSum_airyAiDeriv_maclaurin (z : ℂ) :
    HasSum (fun k : ℕ => airyAiDeriv 0 * (3 : ℂ) ^ k * poch (2 / 3) k / (3 * k).factorial * z ^ (3 * k) +
      airyAi 0 * (3 : ℂ) ^ k * poch (4 / 3) k / (3 * k + 2).factorial * z ^ (3 * k + 2))
      (airyAiDeriv z) := by
  convert ((hasSum_airyGDeriv_maclaurin z).mul_left (-(((3 : ℝ) ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ))).add
    ((hasSum_airyFDeriv_maclaurin z).mul_left (((3 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)) using 1
  · funext k
    simp only [airyAi, airyAiDeriv, airyF_zero, airyG_zero, airyFDeriv_zero, airyGDeriv_zero']
    ring
  · simp only [airyAiDeriv]; ring

/-- hasSum airyBi maclaurin (DLMF 9.4.3). -/
@[dlmf 9.4.E3]
theorem hasSum_airyBi_maclaurin (z : ℂ) :
    HasSum (fun k : ℕ => airyBi 0 * (3 : ℂ) ^ k * poch (1 / 3) k / (3 * k).factorial * z ^ (3 * k) +
      airyBiDeriv 0 * (3 : ℂ) ^ k * poch (2 / 3) k / (3 * k + 1).factorial * z ^ (3 * k + 1))
      (airyBi z) := by
  convert ((hasSum_airyF_maclaurin z).mul_left
      ((Real.sqrt 3 : ℂ) * (((3 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ))).add
    ((hasSum_airyG_maclaurin z).mul_left
      ((Real.sqrt 3 : ℂ) * (((3 : ℝ) ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ))) using 1
  · funext k
    simp only [airyBi, airyBiDeriv, airyF_zero, airyG_zero, airyFDeriv_zero, airyGDeriv_zero']
    ring
  · simp only [airyBi]; ring

/-- hasSum airyBiDeriv maclaurin (DLMF 9.4.4). -/
@[dlmf 9.4.E4]
theorem hasSum_airyBiDeriv_maclaurin (z : ℂ) :
    HasSum (fun k : ℕ => airyBiDeriv 0 * (3 : ℂ) ^ k * poch (2 / 3) k / (3 * k).factorial * z ^ (3 * k) +
      airyBi 0 * (3 : ℂ) ^ k * poch (4 / 3) k / (3 * k + 2).factorial * z ^ (3 * k + 2))
      (airyBiDeriv z) := by
  convert ((hasSum_airyGDeriv_maclaurin z).mul_left
      ((Real.sqrt 3 : ℂ) * (((3 : ℝ) ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ))).add
    ((hasSum_airyFDeriv_maclaurin z).mul_left
      ((Real.sqrt 3 : ℂ) * (((3 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ))) using 1
  · funext k
    simp only [airyBi, airyBiDeriv, airyF_zero, airyG_zero, airyFDeriv_zero, airyGDeriv_zero']
    ring
  · simp only [airyBiDeriv]; ring

/-- The real-axis pair in DLMF Table 9.2.1 is numerically independent. -/
theorem airy_pair_wellConditioned_real  :
    IsWellConditionedPairOn airyAi airyBi {z : ℂ | z.im = 0} := by
  obtain ⟨R, B, h⟩ := airyErr_far_real
  have hπ : (1 / π : ℂ) ≠ 0 := one_div_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  refine airyErr_wellConditioned_of_far differentiable_airyAi.continuous
    differentiable_airyBi.continuous ?_ ?_ hπ ?_ (R := R) (B := B) ?_
  · rw [deriv_airyAi]
    exact Differentiable.continuous (𝕜 := ℂ) fun z => (hasDerivAt_airyAiDeriv z).differentiableAt
  · rw [deriv_airyBi]
    exact Differentiable.continuous (𝕜 := ℂ) fun z => (hasDerivAt_airyBiDeriv z).differentiableAt
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
    differentiable_airyBi.continuous ?_ ?_ hπ ?_ (R := max (max R R') 1) (B := max B B') ?_
  · rw [deriv_airyAi]
    exact Differentiable.continuous (𝕜 := ℂ) fun z => (hasDerivAt_airyAiDeriv z).differentiableAt
  · rw [deriv_airyBi]
    exact Differentiable.continuous (𝕜 := ℂ) fun z => (hasDerivAt_airyBiDeriv z).differentiableAt
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

/-- The mixed pairs in DLMF Table 9.2.1. -/
theorem airy_rotated_pair_wellConditioned {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    IsWellConditionedPairOn airyAi (fun z => airyAi (z * exp (-ε * (2 * π * I / 3))))
      {z : ℂ | -π / 3 ≤ ε * arg z ∧ ε * arg z ≤ π} := by
  have hπ := Real.pi_pos
  obtain ⟨C, R, hC, hU⟩ := airyErr_ai_uniform
  set c := exp (-ε * (2 * π * I / 3))
  have hc : ‖c‖ = 1 := by
    rw [show c = exp (((-ε * (2 * π / 3) : ℝ) : ℂ) * I) by simp only [c]; congr 1; push_cast; ring]
    exact airyErr_norm_exp_I _
  have hW := wronskian_airyAi_rotated (z := 0) hε
  have hW0 : exp (ε * (π * I / 6)) / (2 * π) ≠ 0 :=
    div_ne_zero (exp_ne_zero _) (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero))
  refine airyErr_wellConditioned_of_far differentiable_airyAi.continuous (airyErr_continuous_rot c)
    (by rw [deriv_airyAi]
        exact Differentiable.continuous (𝕜 := ℂ) fun z => (hasDerivAt_airyAiDeriv z).differentiableAt)
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
  have hlt := Complex.neg_pi_lt_arg z
  have hle := Complex.arg_le_pi z
  -- the key real-part inequality
  have hre : 0 ≤ (airyZetaComplex z).re + (airyZetaComplex (z * c)).re := by
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
  rw [deriv_airyAi, airyErr_deriv_rot]
  simp only
  rw [norm_mul, hc, mul_one]
  have k1 := airyErr_cross_le hC hU hz0 hzc0 hzcn hRz hre
  have k2 := airyErr_cross_le hC hU hzc0 hz0 hzcn.symm (hzcn ▸ hRz) (by linarith)
  linarith [mul_comm ‖airyAiDeriv z‖ ‖airyAi (z * c)‖]

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
  have hn₁ : ‖c₁‖ = 1 := by rw [hc₁, norm_neg]; exact airyErr_norm_exp_I _
  have hn₂ : ‖c₂‖ = 1 := by rw [hc₂, norm_neg]; exact airyErr_norm_exp_I _
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
  have hz' : |arg u| ≤ 2 * π / 3 := hz
  have hlt := Complex.neg_pi_lt_arg u
  have hb := abs_le.mp hz'
  have e₁ : z * c₁ = u * exp (((π / 3 : ℝ) : ℂ) * I) := by rw [hc₁]; simp only [u]; ring
  have e₂ : z * c₂ = u * exp (((-(π / 3)) : ℝ) * I) := by rw [hc₂]; simp only [u]; ring
  have h₁0 : z * c₁ ≠ 0 := mul_ne_zero hz0 (exp_ne_zero _)
  have h₂0 : z * c₂ ≠ 0 := mul_ne_zero hz0 (exp_ne_zero _)
  have hn : ‖z * c₁‖ = ‖z * c₂‖ := by rw [norm_mul, norm_mul, hn₁, hn₂]
  have hR₁ : R ≤ ‖z * c₁‖ := by rw [norm_mul, hn₁, mul_one]; exact hRz
  have hζ₁ : airyZetaComplex (z * c₁) = airyZetaComplex u * I := by
    rw [e₁, airyErr_zeta_rot hu0 (by linarith) (by linarith)
      (by rw [show (((π / 3 : ℝ) : ℂ) * I * (3 / 2)) = π / 2 * I by push_cast; ring,
        exp_pi_div_two_mul_I])]
  have hre : 0 ≤ (airyZetaComplex (z * c₁)).re + (airyZetaComplex (z * c₂)).re := by
    rw [hζ₁]
    rcases eq_or_lt_of_le hb.1 with h | h
    · -- boundary ray `arg u = -2π/3`: rotate by `5π/3` instead
      have e₂' : z * c₂ = u * exp (((5 * π / 3 : ℝ) : ℂ) * I) := by
        rw [e₂, show (((5 * π / 3 : ℝ) : ℂ) * I) = (((-(π / 3)) : ℝ) : ℂ) * I + 2 * π * I by
          push_cast; ring, exp_add, exp_two_pi_mul_I, mul_one]
      rw [e₂', airyErr_zeta_rot hu0 (α := 5 * π / 3) (by linarith) (by linarith) (κ := I)
        (by rw [show (((5 * π / 3 : ℝ) : ℂ) * I * (3 / 2)) = π / 2 * I + 2 * π * I by
          push_cast; ring, exp_add, exp_two_pi_mul_I, mul_one, exp_pi_div_two_mul_I])]
      have him := airyErr_im_two_zeta hu0
      rw [← h, show 3 / 2 * (-(2 * π / 3)) = -π by ring, Real.sin_neg, Real.sin_pi, neg_zero,
        mul_zero] at him
      have : (airyZetaComplex u).im = 0 := by simpa using him
      simp [this]
    · rw [e₂, airyErr_zeta_rot hu0 (α := -(π / 3)) (by linarith) (by linarith) (κ := -I)
        (by rw [show ((((-(π / 3)) : ℝ) : ℂ) * I * (3 / 2)) = -(π / 2 * I) by push_cast; ring,
          exp_neg, exp_pi_div_two_mul_I, inv_I])]
      simp
  rw [airyErr_deriv_rot, airyErr_deriv_rot]
  simp only
  rw [norm_mul, norm_mul, hn₁, hn₂, mul_one, mul_one]
  have k1 := airyErr_cross_le hC hU h₁0 h₂0 hn hR₁ hre
  have k2 := airyErr_cross_le hC hU h₂0 h₁0 hn.symm (hn ▸ hR₁) (by linarith)
  linarith [mul_comm ‖airyAiDeriv (z * c₁)‖ ‖airyAi (z * c₂)‖]

end DLMF.Airy
