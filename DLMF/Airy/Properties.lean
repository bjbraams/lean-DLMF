/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Basic
public import DLMF.Bessel.SturmZeros

/-!
# Differential and connection properties of Airy functions (DLMF §§9.2, 9.4)

The Airy functions are defined through their Maclaurin series, written with Mathlib's regularized
`₀F̃₁`. With `f(z) = ₀F̃₁(;2/3;z³/9)` and `g(z) = z ₀F̃₁(;4/3;z³/9)` (`airyF`, `airyG`),

$$
\operatorname{Ai}(z) = 3^{-2/3} f(z) - 3^{-4/3} g(z),\qquad
\operatorname{Bi}(z) = \sqrt3\,\bigl(3^{-2/3} f(z) + 3^{-4/3} g(z)\bigr),
$$

which is DLMF 9.4.1 and 9.4.3 with the Gamma factors of the Maclaurin coefficients absorbed into
the regularized series. Both functions are entire, with derivatives `airyAiDeriv`, `airyBiDeriv`
given by explicit series.

## Main results

* `hasDerivAt_airyAi`, `hasDerivAt_airyAiDeriv` and the Bi analogues: Airy's equation
  `w'' = z w` (9.2.1), packaged as `isAirySol_airyAi`, `isAirySol_airyBi`;
* `airyAi_zero`, `airyAiDeriv_zero`, `airyBi_zero`, `airyBiDeriv_zero` (9.2.3–9.2.6);
* `wronskian_airyAi_airyBi`: `𝒲{Ai, Bi} = 1/π` (9.2.7);
* `IsAirySol.eq_of_initial`: solutions of Airy's equation are determined by `w(0), w'(0)`;
* rotations by `e^{±2πi/3}`: `airyBi_eq_airyAi_omega` (9.2.10), `airyAi_mul_omega`,
  `airyAi_mul_omega_recip` (9.2.11), `airyAi_add_omega` (9.2.12), `airyBi_add_omega` (9.2.13);
* `airyAi_conj`, `airyBi_conj`: both functions are real on the real line.
-/

@[expose] public section

open Complex
open scoped Real ComplexConjugate

noncomputable section

namespace DLMF.Airy

open DLMF.Bessel

/-! ### The two even/odd series -/

/-- The chain rule for `z ↦ ₀F̃₁(;c;z³/9)`: its derivative is `(z²/3) ₀F̃₁(;c+1;z³/9)`. -/
theorem hasDerivAt_reg0F1_cube {c c' : ℂ} (hc : c + 1 = c') (z : ℂ) :
    HasDerivAt (fun z : ℂ => regularizedHGFun (∅ : Multiset ℂ) {c} (z ^ 3 / 9))
      (z ^ 2 / 3 * regularizedHGFun (∅ : Multiset ℂ) {c'} (z ^ 3 / 9)) z := by
  subst hc
  have h := (hasDerivAt_regularized0F1 c (z ^ 3 / 9)).comp z ((hasDerivAt_pow 3 z).div_const 9)
  refine h.congr_deriv ?_
  norm_num
  ring

/-- The contiguous relation `₀F̃₁(;c;w) = c ₀F̃₁(;c+1;w) + w ₀F̃₁(;c+2;w)`, with the shifted
parameters given as equations. -/
theorem reg0F1_contiguous' {c c₁ c₂ : ℂ} (h₁ : c + 1 = c₁) (h₂ : c + 1 + 1 = c₂) (w : ℂ) :
    regularizedHGFun (∅ : Multiset ℂ) {c} w =
      c * regularizedHGFun ∅ {c₁} w + w * regularizedHGFun ∅ {c₂} w := by
  subst h₁ h₂
  exact regularized0F1_contiguous c w

/-- `airyF` has derivative `airyFDeriv`. -/
theorem hasDerivAt_airyF (z : ℂ) : HasDerivAt airyF (airyFDeriv z) z :=
  hasDerivAt_reg0F1_cube (by norm_num) z

/-- `airyFDeriv` has derivative `z · airyF z`, so `f'' = z f`. -/
theorem hasDerivAt_airyFDeriv (z : ℂ) : HasDerivAt airyFDeriv (z * airyF z) z := by
  have h := ((hasDerivAt_pow 2 z).div_const 3).mul (hasDerivAt_reg0F1_cube
    (c := 5 / 3) (c' := 8 / 3) (by norm_num) z)
  have e : z * airyF z = z * regularizedHGFun (∅ : Multiset ℂ) {2 / 3} (z ^ 3 / 9) := rfl
  rw [e, reg0F1_contiguous' (c := 2 / 3) (c₁ := 5 / 3) (c₂ := 8 / 3) (by norm_num)
    (by norm_num)]
  refine h.congr_deriv ?_
  norm_num
  ring

/-- `airyG` has derivative `airyGDeriv`. -/
theorem hasDerivAt_airyG (z : ℂ) : HasDerivAt airyG (airyGDeriv z) z := by
  have h := (hasDerivAt_id z).mul (hasDerivAt_reg0F1_cube (c := 4 / 3) (c' := 7 / 3)
    (by norm_num) z)
  refine h.congr_deriv ?_
  simp only [airyGDeriv, id]
  ring

/-- `airyGDeriv` has derivative `z · airyG z`, so `g'' = z g`. -/
theorem hasDerivAt_airyGDeriv (z : ℂ) : HasDerivAt airyGDeriv (z * airyG z) z := by
  have h := (hasDerivAt_reg0F1_cube (c := 4 / 3) (c' := 7 / 3) (by norm_num) z).add
    (((hasDerivAt_pow 3 z).div_const 3).mul (hasDerivAt_reg0F1_cube
      (c := 7 / 3) (c' := 10 / 3) (by norm_num) z))
  have e : z * airyG z = z * (z * regularizedHGFun (∅ : Multiset ℂ) {4 / 3} (z ^ 3 / 9)) := rfl
  rw [e, reg0F1_contiguous' (c := 4 / 3) (c₁ := 7 / 3) (c₂ := 10 / 3) (by norm_num)
    (by norm_num)]
  refine h.congr_deriv ?_
  norm_num
  ring

/-- The regularized `₀F̃₁(;c;·)` takes the value `1/Γ(c)` at the origin. -/
theorem reg0F1_zero (c : ℂ) : regularizedHGFun (∅ : Multiset ℂ) {c} 0 = (Gamma c)⁻¹ := by
  rw [regularizedHGFun_zero]
  exact (regularizedHGFunCoeff_empty c 0).trans (by simp)

/-- `f(0) = 1/Γ(2/3)`. -/
theorem airyF_zero : airyF 0 = (Gamma (2 / 3))⁻¹ := by
  rw [airyF, show (0 : ℂ) ^ 3 / 9 = 0 by norm_num, reg0F1_zero]

/-- `g(0) = 0`. -/
theorem airyG_zero : airyG 0 = 0 := by simp [airyG]

/-- `f'(0) = 0`. -/
theorem airyFDeriv_zero : airyFDeriv 0 = 0 := by simp [airyFDeriv]

/-- `g'(0) = 3/Γ(1/3)`, i.e. `1/Γ(4/3)`. -/
theorem airyGDeriv_zero : airyGDeriv 0 = 3 * (Gamma (1 / 3))⁻¹ := by
  have h : Gamma (4 / 3) = 1 / 3 * Gamma (1 / 3) := by
    rw [show (4 / 3 : ℂ) = 1 / 3 + 1 by norm_num, Complex.Gamma_add_one _ (by norm_num)]
  rw [airyGDeriv, show (0 : ℂ) ^ 3 / 9 = 0 by norm_num, reg0F1_zero, reg0F1_zero, h]
  ring

/-! ### Definitions of `Ai`, `Bi` and their derivatives -/

/-- `Ai` has derivative `Ai'` (`airyAiDeriv`) at every point. -/
theorem hasDerivAt_airyAi (z : ℂ) : HasDerivAt airyAi (airyAiDeriv z) z :=
  ((hasDerivAt_airyF z).const_mul _).sub ((hasDerivAt_airyG z).const_mul _)

/-- `Ai'` has derivative `z Ai(z)` (Airy's equation). -/
theorem hasDerivAt_airyAiDeriv (z : ℂ) : HasDerivAt airyAiDeriv (z * airyAi z) z :=
  (((hasDerivAt_airyFDeriv z).const_mul _).sub
    ((hasDerivAt_airyGDeriv z).const_mul _)).congr_deriv (by simp only [airyAi]; ring)

/-- `Bi` has derivative `Bi'` (`airyBiDeriv`) at every point. -/
theorem hasDerivAt_airyBi (z : ℂ) : HasDerivAt airyBi (airyBiDeriv z) z :=
  (((hasDerivAt_airyF z).const_mul _).add ((hasDerivAt_airyG z).const_mul _)).const_mul _

/-- `Bi'` has derivative `z Bi(z)` (Airy's equation). -/
theorem hasDerivAt_airyBiDeriv (z : ℂ) : HasDerivAt airyBiDeriv (z * airyBi z) z :=
  ((((hasDerivAt_airyFDeriv z).const_mul _).add
    ((hasDerivAt_airyGDeriv z).const_mul _)).const_mul _).congr_deriv
      (by simp only [airyBi]; ring)

/-- `Ai` is entire. -/
theorem differentiable_airyAi : Differentiable ℂ airyAi :=
  fun z => (hasDerivAt_airyAi z).differentiableAt

/-- `Bi` is entire. -/
theorem differentiable_airyBi : Differentiable ℂ airyBi :=
  fun z => (hasDerivAt_airyBi z).differentiableAt

/-- The derivative of `Ai` is `airyAiDeriv`. -/
theorem deriv_airyAi : deriv airyAi = airyAiDeriv :=
  funext fun z => (hasDerivAt_airyAi z).deriv

/-- The derivative of `Bi` is `airyBiDeriv`. -/
theorem deriv_airyBi : deriv airyBi = airyBiDeriv :=
  funext fun z => (hasDerivAt_airyBi z).deriv

/-- Airy's equation for `Ai` (DLMF 9.2.1). -/
@[dlmf 9.2.E1]
theorem airyAi_ode (z : ℂ) : deriv (deriv airyAi) z = z * airyAi z := by
  rw [deriv_airyAi, (hasDerivAt_airyAiDeriv z).deriv]

/-- Airy's equation for `Bi` (DLMF 9.2.1). -/
@[dlmf 9.2.E1]
theorem airyBi_ode (z : ℂ) : deriv (deriv airyBi) z = z * airyBi z := by
  rw [deriv_airyBi, (hasDerivAt_airyBiDeriv z).deriv]

/-! ### Values at the origin -/

/-- `3^a 3^b = 3^{a+b}` for real exponents. -/
theorem three_rpow_add (a b : ℝ) : (3 : ℝ) ^ a * (3 : ℝ) ^ b = (3 : ℝ) ^ (a + b) :=
  (Real.rpow_add (by norm_num) a b).symm

/-- `√3 = 3^{1/2}`. -/
theorem sqrt_three_eq_rpow : Real.sqrt 3 = (3 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow 3

/-- `3^{-a} = (3^a)⁻¹` for real `a`. -/
theorem three_rpow_neg (a : ℝ) : (3 : ℝ) ^ (-a) = ((3 : ℝ) ^ a)⁻¹ :=
  Real.rpow_neg (by norm_num) a

/-- `Ai(0) = 1/(3^{2/3} Γ(2/3))` (DLMF 9.2.3). -/
@[dlmf 9.2.E3]
theorem airyAi_zero : airyAi 0 = 1 / (((3 : ℝ) ^ (2 / 3 : ℝ) : ℝ) * Gamma (2 / 3)) := by
  rw [airyAi, airyF_zero, airyG_zero, mul_zero, sub_zero, three_rpow_neg]
  push_cast
  ring

/-- `Ai'(0) = -1/(3^{1/3} Γ(1/3))` (DLMF 9.2.4). -/
@[dlmf 9.2.E4]
theorem airyAiDeriv_zero :
    airyAiDeriv 0 = -1 / (((3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) * Gamma (1 / 3)) := by
  rw [airyAiDeriv, airyFDeriv_zero, airyGDeriv_zero]
  have h : (3 : ℝ) ^ (-(4 / 3 : ℝ)) * 3 = ((3 : ℝ) ^ (1 / 3 : ℝ))⁻¹ := by
    rw [← three_rpow_neg]
    conv_lhs => rw [show (3 : ℝ) ^ (-(4 / 3 : ℝ)) * 3 = 3 ^ (-(4 / 3 : ℝ)) * 3 ^ (1 : ℝ) by simp]
    rw [three_rpow_add]
    norm_num
  have h' : (((3 : ℝ) ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) * 3 = (((3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ)⁻¹ := by
    exact_mod_cast h
  rw [mul_zero, zero_sub, ← mul_assoc, h']
  ring

/-- `Bi(0) = 1/(3^{1/6} Γ(2/3))` (DLMF 9.2.5). -/
@[dlmf 9.2.E5]
theorem airyBi_zero : airyBi 0 = 1 / (((3 : ℝ) ^ (1 / 6 : ℝ) : ℝ) * Gamma (2 / 3)) := by
  rw [airyBi, airyF_zero, airyG_zero]
  have h : Real.sqrt 3 * (3 : ℝ) ^ (-(2 / 3 : ℝ)) = ((3 : ℝ) ^ (1 / 6 : ℝ))⁻¹ := by
    rw [sqrt_three_eq_rpow, three_rpow_add, ← three_rpow_neg]
    norm_num
  have h' : (Real.sqrt 3 : ℂ) * (((3 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) =
      (((3 : ℝ) ^ (1 / 6 : ℝ) : ℝ) : ℂ)⁻¹ := by
    exact_mod_cast h
  rw [mul_zero, add_zero, ← mul_assoc, h']
  ring

/-- `Bi'(0) = 3^{1/6}/Γ(1/3)` (DLMF 9.2.6). -/
@[dlmf 9.2.E6]
theorem airyBiDeriv_zero :
    airyBiDeriv 0 = ((3 : ℝ) ^ (1 / 6 : ℝ) : ℝ) / Gamma (1 / 3) := by
  rw [airyBiDeriv, airyFDeriv_zero, airyGDeriv_zero]
  have h : Real.sqrt 3 * ((3 : ℝ) ^ (-(4 / 3 : ℝ)) * 3) = (3 : ℝ) ^ (1 / 6 : ℝ) := by
    conv_lhs => rw [show (3 : ℝ) ^ (-(4 / 3 : ℝ)) * 3 = 3 ^ (-(4 / 3 : ℝ)) * 3 ^ (1 : ℝ) by simp]
    rw [sqrt_three_eq_rpow, three_rpow_add, three_rpow_add]
    norm_num
  have h' : (Real.sqrt 3 : ℂ) * ((((3 : ℝ) ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) * 3) =
      (((3 : ℝ) ^ (1 / 6 : ℝ) : ℝ) : ℂ) := by
    exact_mod_cast h
  rw [mul_zero, zero_add, ← h']
  ring

/-! ### Solutions of Airy's equation -/

/-- `(Ai, Ai')` solves Airy's equation. -/
theorem isAirySol_airyAi : IsAirySol airyAi airyAiDeriv :=
  fun z => ⟨hasDerivAt_airyAi z, hasDerivAt_airyAiDeriv z⟩

/-- `(Bi, Bi')` solves Airy's equation. -/
theorem isAirySol_airyBi : IsAirySol airyBi airyBiDeriv :=
  fun z => ⟨hasDerivAt_airyBi z, hasDerivAt_airyBiDeriv z⟩

/-- The Wronskian of two solutions of Airy's equation is constant (DLMF 9.2(iii)). -/
theorem IsAirySol.wronskian_eq {f f' g g' : ℂ → ℂ} (hf : IsAirySol f f') (hg : IsAirySol g g')
    (z : ℂ) : f z * g' z - f' z * g z = f 0 * g' 0 - f' 0 * g 0 := by
  have hd : ∀ w, HasDerivAt (fun w => f w * g' w - f' w * g w) 0 w := fun w =>
    (((hf w).1.mul (hg w).2).sub ((hf w).2.mul (hg w).1)).congr_deriv (by ring)
  exact is_const_of_deriv_eq_zero (fun w => (hd w).differentiableAt)
    (fun w => (hd w).deriv) z 0

/-- `Γ(1/3) Γ(2/3) = 2π/√3` (reflection formula at `1/3`). -/
theorem Gamma_one_third_mul_Gamma_two_thirds :
    Gamma (1 / 3) * Gamma (2 / 3) = 2 * π / Real.sqrt 3 := by
  have h := Complex.Gamma_mul_Gamma_one_sub (1 / 3)
  rw [show (1 : ℂ) - 1 / 3 = 2 / 3 by norm_num] at h
  rw [h]
  have hs : Complex.sin (π * (1 / 3)) = ((Real.sqrt 3 / 2 : ℝ) : ℂ) := by
    rw [show (π : ℂ) * (1 / 3) = ((π / 3 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_sin,
      Real.sin_pi_div_three]
  rw [hs]
  have h3 : (Real.sqrt 3 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num)).ne'
  push_cast
  field_simp

/-- The Wronskian `𝒲{Ai, Bi} = 1/π` (DLMF 9.2.7). -/
@[dlmf 9.2.E7]
theorem wronskian_airyAi_airyBi (z : ℂ) :
    airyAi z * airyBiDeriv z - airyAiDeriv z * airyBi z = 1 / π := by
  rw [isAirySol_airyAi.wronskian_eq isAirySol_airyBi z, airyAi_zero, airyAiDeriv_zero,
    airyBi_zero, airyBiDeriv_zero]
  have hG : Gamma (1 / 3) * Gamma (2 / 3) ≠ 0 := by
    rw [Gamma_one_third_mul_Gamma_two_thirds]
    have : (Real.sqrt 3 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num)).ne'
    exact div_ne_zero (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)) this
  have h1 : Gamma (1 / 3) ≠ 0 := left_ne_zero_of_mul hG
  have h2 : Gamma (2 / 3) ≠ 0 := right_ne_zero_of_mul hG
  have e1 : (3 : ℝ) ^ (1 / 6 : ℝ) / ((3 : ℝ) ^ (2 / 3 : ℝ)) = ((Real.sqrt 3)⁻¹) := by
    rw [div_eq_mul_inv, ← three_rpow_neg, three_rpow_add, sqrt_three_eq_rpow,
      ← three_rpow_neg]
    norm_num
  have e2 : 1 / ((3 : ℝ) ^ (1 / 3 : ℝ) * (3 : ℝ) ^ (1 / 6 : ℝ)) = ((Real.sqrt 3)⁻¹) := by
    rw [three_rpow_add, sqrt_three_eq_rpow, one_div]
    norm_num
  have e1' : (((3 : ℝ) ^ (1 / 6 : ℝ) : ℝ) : ℂ) / (((3 : ℝ) ^ (2 / 3 : ℝ) : ℝ) : ℂ) =
      ((Real.sqrt 3 : ℝ) : ℂ)⁻¹ := by exact_mod_cast e1
  have e2' : 1 / ((((3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (((3 : ℝ) ^ (1 / 6 : ℝ) : ℝ) : ℂ)) =
      ((Real.sqrt 3 : ℝ) : ℂ)⁻¹ := by exact_mod_cast e2
  have hπ := Gamma_one_third_mul_Gamma_two_thirds
  have h3 : (Real.sqrt 3 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hr1 : (((3 : ℝ) ^ (2 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).ne'
  have hr2 : (((3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).ne'
  have hr3 : (((3 : ℝ) ^ (1 / 6 : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).ne'
  calc 1 / ((((3 : ℝ) ^ (2 / 3 : ℝ) : ℝ) : ℂ) * Gamma (2 / 3)) *
        ((((3 : ℝ) ^ (1 / 6 : ℝ) : ℝ) : ℂ) / Gamma (1 / 3)) -
        -1 / ((((3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) * Gamma (1 / 3)) *
          (1 / ((((3 : ℝ) ^ (1 / 6 : ℝ) : ℝ) : ℂ) * Gamma (2 / 3)))
      = ((((3 : ℝ) ^ (1 / 6 : ℝ) : ℝ) : ℂ) / (((3 : ℝ) ^ (2 / 3 : ℝ) : ℝ) : ℂ) +
          1 / ((((3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (((3 : ℝ) ^ (1 / 6 : ℝ) : ℝ) : ℂ))) /
          (Gamma (1 / 3) * Gamma (2 / 3)) := by
        field_simp
        ring
    _ = 1 / π := by
        rw [e1', e2', hπ]
        field_simp
        ring

/-- A solution of Airy's equation with vanishing initial data vanishes identically. -/
theorem IsAirySol.eq_zero {f f' : ℂ → ℂ} (hf : IsAirySol f f') (h0 : f 0 = 0) (h1 : f' 0 = 0)
    (z : ℂ) : f z = 0 := by
  have h₁ := hf.wronskian_eq isAirySol_airyAi z
  have h₂ := hf.wronskian_eq isAirySol_airyBi z
  have h₃ := wronskian_airyAi_airyBi z
  simp only [h0, h1, zero_mul, sub_zero] at h₁ h₂
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have : f z * (1 / π) = 0 := by
    linear_combination airyAi z * h₂ - airyBi z * h₁ - f z * h₃
  simpa [hp] using this

/-- Solutions of Airy's equation are determined by their initial data. -/
theorem IsAirySol.eq_of_initial {f f' g g' : ℂ → ℂ} (hf : IsAirySol f f') (hg : IsAirySol g g')
    (h0 : f 0 = g 0) (h1 : f' 0 = g' 0) (z : ℂ) : f z = g z := by
  have hd : IsAirySol (fun w => f w - g w) (fun w => f' w - g' w) := fun w =>
    ⟨(hf w).1.sub (hg w).1, ((hf w).2.sub (hg w).2).congr_deriv (by ring)⟩
  exact sub_eq_zero.mp (hd.eq_zero (by simp [h0]) (by simp [h1]) z)

/-! ### Rotations by cube roots of unity (DLMF 9.2(iv)) -/

/-- `e^{2πi/3} = -1/2 + (√3/2) i`. -/
theorem exp_two_pi_I_div_three :
    exp (2 * π * I / 3) = -1 / 2 + (Real.sqrt 3 / 2 : ℝ) * I := by
  have h : (2 * π * I / 3 : ℂ) = ((2 * π / 3 : ℝ) : ℂ) * I := by push_cast; ring
  rw [h, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    show 2 * π / 3 = π - π / 3 by ring, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three,
    Real.sin_pi_div_three]
  push_cast
  ring

/-- `ω = e^{2πi/3}` is a cube root of unity: `ω³ = 1`. -/
theorem omega_cube : exp (2 * π * I / 3) ^ 3 = 1 := by
  rw [← Complex.exp_nat_mul, show ((3 : ℕ) : ℂ) * (2 * π * I / 3) = 2 * π * I by push_cast; ring,
    exp_two_pi_mul_I]

/-- `₀F̃₁(;c;(ωz)³/9) = ₀F̃₁(;c;z³/9)` when `ω³ = 1`. -/
lemma reg0F1_cube_mul {c ω : ℂ} (hω : ω ^ 3 = 1) (z : ℂ) :
    regularizedHGFun (∅ : Multiset ℂ) {c} ((ω * z) ^ 3 / 9) =
      regularizedHGFun (∅ : Multiset ℂ) {c} (z ^ 3 / 9) := by
  rw [mul_pow, hω, one_mul]

/-- `f(ωz) = f(z)` when `ω³ = 1`. -/
theorem airyF_mul {ω : ℂ} (hω : ω ^ 3 = 1) (z : ℂ) : airyF (ω * z) = airyF z :=
  reg0F1_cube_mul hω z

/-- `g(ωz) = ω g(z)` when `ω³ = 1`. -/
theorem airyG_mul {ω : ℂ} (hω : ω ^ 3 = 1) (z : ℂ) : airyG (ω * z) = ω * airyG z := by
  simp only [airyG, reg0F1_cube_mul hω z]; ring

/-- `(√3)² = 3` in `ℂ`. -/
theorem sqrt_three_sq : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
  rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring

/-- `e^{-2πi/3} = -1/2 - (√3/2) i`. -/
theorem exp_neg_two_pi_I_div_three :
    exp (-(2 * π * I / 3)) = -1 / 2 - (Real.sqrt 3 / 2 : ℝ) * I := by
  have h : (-(2 * π * I / 3) : ℂ) = ((-(2 * π / 3) : ℝ) : ℂ) * I := by push_cast; ring
  rw [h, exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_neg, Real.sin_neg,
    show 2 * π / 3 = π - π / 3 by ring, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three,
    Real.sin_pi_div_three]
  push_cast
  ring

/-- `e^{πi/6} = √3/2 + i/2`. -/
theorem exp_pi_I_div_six : exp (π * I / 6) = (Real.sqrt 3 / 2 : ℝ) + (1 / 2 : ℂ) * I := by
  have h : (π * I / 6 : ℂ) = ((π / 6 : ℝ) : ℂ) * I := by push_cast; ring
  rw [h, exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_six, Real.sin_pi_div_six]
  push_cast
  ring

/-- `e^{-πi/6} = √3/2 - i/2`. -/
theorem exp_neg_pi_I_div_six : exp (-(π * I / 6)) = (Real.sqrt 3 / 2 : ℝ) - (1 / 2 : ℂ) * I := by
  have h : (-(π * I / 6) : ℂ) = ((-(π / 6) : ℝ) : ℂ) * I := by push_cast; ring
  rw [h, exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_six,
    Real.sin_pi_div_six]
  push_cast
  ring

/-- `e^{πi/3} = 1/2 + (√3/2) i`. -/
theorem exp_pi_I_div_three : exp (π * I / 3) = (1 / 2 : ℂ) + (Real.sqrt 3 / 2 : ℝ) * I := by
  have h : (π * I / 3 : ℂ) = ((π / 3 : ℝ) : ℂ) * I := by push_cast; ring
  rw [h, exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast
  ring

/-- `e^{-πi/3} = 1/2 - (√3/2) i`. -/
theorem exp_neg_pi_I_div_three :
    exp (-(π * I / 3)) = (1 / 2 : ℂ) - (Real.sqrt 3 / 2 : ℝ) * I := by
  have h : (-(π * I / 3) : ℂ) = ((-(π / 3) : ℝ) : ℂ) * I := by push_cast; ring
  rw [h, exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast
  ring

/-- `(e^{-2πi/3})³ = 1`. -/
theorem omega_recip_cube : exp (-(2 * π * I / 3)) ^ 3 = 1 := by
  rw [← Complex.exp_nat_mul, show ((3 : ℕ) : ℂ) * (-(2 * π * I / 3)) = -(2 * π * I) by
    push_cast; ring, exp_neg, exp_two_pi_mul_I, inv_one]

/-- `Bi(z) = e^{-πi/6} Ai(z e^{-2πi/3}) + e^{πi/6} Ai(z e^{2πi/3})` (DLMF 9.2.10). -/
@[dlmf 9.2.E10]
theorem airyBi_eq_airyAi_omega (z : ℂ) :
    airyBi z = exp (-(π * I / 6)) * airyAi (z * exp (-(2 * π * I / 3))) +
      exp (π * I / 6) * airyAi (z * exp (2 * π * I / 3)) := by
  rw [mul_comm z, mul_comm z]
  simp only [airyAi, airyBi, airyF_mul omega_cube, airyF_mul omega_recip_cube,
    airyG_mul omega_cube, airyG_mul omega_recip_cube]
  rw [exp_pi_I_div_six, exp_neg_pi_I_div_six, exp_two_pi_I_div_three,
    exp_neg_two_pi_I_div_three]
  push_cast
  linear_combination ((((3 : ℝ) ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) * airyG z * Real.sqrt 3 / 2) * I_sq

/-- `Ai(z e^{-2πi/3}) = ½ e^{-πi/3} (Ai(z) + i Bi(z))` (DLMF 9.2.11, upper signs). -/
@[dlmf 9.2.E11]
theorem airyAi_mul_omega_recip (z : ℂ) :
    airyAi (z * exp (-(2 * π * I / 3))) =
      1 / 2 * exp (-(π * I / 3)) * (airyAi z + I * airyBi z) := by
  rw [mul_comm z]
  simp only [airyAi, airyBi, airyF_mul omega_recip_cube, airyG_mul omega_recip_cube]
  rw [exp_neg_pi_I_div_three, exp_neg_two_pi_I_div_three]
  have h3 := sqrt_three_sq
  push_cast at h3 ⊢
  linear_combination ((((((3 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) * airyF z +
    (((3 : ℝ) ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) * airyG z)) / 4) * (I ^ 2 * h3 + 3 * I_sq)

/-- `Ai(z e^{2πi/3}) = ½ e^{πi/3} (Ai(z) - i Bi(z))` (DLMF 9.2.11, lower signs). -/
@[dlmf 9.2.E11]
theorem airyAi_mul_omega (z : ℂ) :
    airyAi (z * exp (2 * π * I / 3)) = 1 / 2 * exp (π * I / 3) * (airyAi z - I * airyBi z) := by
  rw [mul_comm z]
  simp only [airyAi, airyBi, airyF_mul omega_cube, airyG_mul omega_cube]
  rw [exp_pi_I_div_three, exp_two_pi_I_div_three]
  have h3 := sqrt_three_sq
  push_cast at h3 ⊢
  linear_combination ((((((3 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) * airyF z +
    (((3 : ℝ) ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) * airyG z)) / 4) * (I ^ 2 * h3 + 3 * I_sq)

/-- `Ai(z) + e^{-2πi/3} Ai(z e^{-2πi/3}) + e^{2πi/3} Ai(z e^{2πi/3}) = 0` (DLMF 9.2.12). -/
@[dlmf 9.2.E12]
theorem airyAi_add_omega (z : ℂ) :
    airyAi z + exp (-(2 * π * I / 3)) * airyAi (z * exp (-(2 * π * I / 3))) +
      exp (2 * π * I / 3) * airyAi (z * exp (2 * π * I / 3)) = 0 := by
  rw [mul_comm z, mul_comm z]
  simp only [airyAi, airyF_mul omega_cube, airyF_mul omega_recip_cube, airyG_mul omega_cube,
    airyG_mul omega_recip_cube]
  rw [exp_two_pi_I_div_three, exp_neg_two_pi_I_div_three]
  have h3 := sqrt_three_sq
  push_cast at h3 ⊢
  linear_combination (-((((3 : ℝ) ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) * airyG z)) *
    ((I ^ 2 / 2) * h3 + (3 / 2 : ℂ) * I_sq)

/-- `Bi(z) + e^{-2πi/3} Bi(z e^{-2πi/3}) + e^{2πi/3} Bi(z e^{2πi/3}) = 0` (DLMF 9.2.13). -/
@[dlmf 9.2.E13]
theorem airyBi_add_omega (z : ℂ) :
    airyBi z + exp (-(2 * π * I / 3)) * airyBi (z * exp (-(2 * π * I / 3))) +
      exp (2 * π * I / 3) * airyBi (z * exp (2 * π * I / 3)) = 0 := by
  rw [mul_comm z, mul_comm z]
  simp only [airyBi, airyF_mul omega_cube, airyF_mul omega_recip_cube, airyG_mul omega_cube,
    airyG_mul omega_recip_cube]
  rw [exp_two_pi_I_div_three, exp_neg_two_pi_I_div_three]
  have h3 := sqrt_three_sq
  push_cast at h3 ⊢
  linear_combination ((Real.sqrt 3 : ℂ) * (((3 : ℝ) ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) * airyG z) *
    ((I ^ 2 / 2) * h3 + (3 / 2 : ℂ) * I_sq)

/-! ### Real values on the real line -/

/-- For real `c`, `₀F̃₁(;c;(z̄)³/9)` is the conjugate of `₀F̃₁(;c;z³/9)`. -/
lemma reg0F1_conj_rat (c : ℝ) (z : ℂ) :
    regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ)} (conj z ^ 3 / 9) =
      conj (regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ)} (z ^ 3 / 9)) := by
  rw [← regularized0F1_conj, map_div₀, map_pow, map_ofNat]

/-- `f(z̄) = conj (f z)`. -/
theorem airyF_conj (z : ℂ) : airyF (conj z) = conj (airyF z) := by
  have h := reg0F1_conj_rat (2 / 3) z
  push_cast at h
  exact h

/-- `g(z̄) = conj (g z)`. -/
theorem airyG_conj (z : ℂ) : airyG (conj z) = conj (airyG z) := by
  have h := reg0F1_conj_rat (4 / 3) z
  push_cast at h
  simp only [airyG, map_mul, h]

/-- `Ai` commutes with complex conjugation; in particular it is real on `ℝ`. -/
theorem airyAi_conj (z : ℂ) : airyAi (conj z) = conj (airyAi z) := by
  simp only [airyAi, airyF_conj, airyG_conj, map_sub, map_mul, conj_ofReal]

/-- `Bi` commutes with complex conjugation; in particular it is real on `ℝ`. -/
theorem airyBi_conj (z : ℂ) : airyBi (conj z) = conj (airyBi z) := by
  simp only [airyBi, airyF_conj, airyG_conj, map_add, map_mul, conj_ofReal]

/-- `Ai(x)` is real for real `x`. -/
theorem airyAi_ofReal_im (x : ℝ) : (airyAi x).im = 0 := by
  have h := airyAi_conj (x : ℂ)
  rw [conj_ofReal] at h
  exact conj_eq_iff_im.mp h.symm

/-- `Bi(x)` is real for real `x`. -/
theorem airyBi_ofReal_im (x : ℝ) : (airyBi x).im = 0 := by
  have h := airyBi_conj (x : ℂ)
  rw [conj_ofReal] at h
  exact conj_eq_iff_im.mp h.symm

end DLMF.Airy
