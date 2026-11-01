/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Basic.Properties
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Floquet's theorem for Mathieu's equation

Floquet's theorem, the characteristic equation, the connection formula and the Floquet dichotomy
for Mathieu's equation (DLMF §§28.2(iii)–(iv)).

## Main results

* `exists_isFloquetSolution_iff`: Floquet's theorem (DLMF 28.2.14–28.2.15).
* `exists_isFloquetSolution_iff_charExp`, `mathieuWI_pi_neg_q`: the characteristic equation
  `cos πν = w_I(π; a, q) = w_I(π; a, -q)` (DLMF 28.2.16).
* `IsMathieuSolution.add_pi_add_sub_pi`: the connection formula 28.2.17.
* `IsMathieuSolution.isFloquet_or`: the Floquet dichotomy (DLMF §28.2(iv)).

## Implementation notes

The principal characteristic exponent, Ince's uniqueness theorem and the Fourier series of
Floquet solutions are in `DLMF.Mathieu.Properties.Floquet`.
-/

@[expose] public noncomputable section

open Complex Set Filter

open scoped Topology Real

namespace DLMF.Mathieu

/-! ### Floquet theory (§28.2(iii)–(iv)) -/

/-- **Floquet's theorem** (DLMF 28.2.14–28.2.15): Mathieu's equation has a nontrivial solution
with `w(z + π) = e^{πiν} w(z)` iff `e^{πiν}` is an eigenvalue of the monodromy matrix 28.2.15. -/
@[dlmf 28.2.E14, dlmf 28.2.E15]
theorem exists_isFloquetSolution_iff (a q ν : ℂ) :
    (∃ w, IsFloquetSolution a q ν w) ↔
      ∃ v : Fin 2 → ℂ, v ≠ 0 ∧
        (mathieuMonodromy a q).mulVec v = Complex.exp (π * I * ν) • v := by
  set μ := Complex.exp (π * I * ν)
  obtain ⟨h1, h10, h11⟩ := mathieuWI_spec a q
  obtain ⟨h2, h20, h21⟩ := mathieuWII_spec a q
  constructor
  · rintro ⟨w, hw, hne, hper⟩
    refine ⟨![w 0, deriv w 0], ?_, ?_⟩
    · intro hv
      have e0 : w 0 = 0 := by simpa using congrFun hv 0
      have e1 : deriv w 0 = 0 := by simpa using congrFun hv 1
      apply hne
      rw [hw.eq_combination]; funext z; simp [e0, e1]
    · have hf : (fun z => w (z + π)) = fun z => μ * w z := funext hper
      have d1 : deriv w π = μ * deriv w 0 := by
        have := congrArg (fun f => deriv f 0) hf
        rw [deriv_comp_add_const, zero_add,
          deriv_const_mul _ (hw.differentiable 0)] at this
        exact this
      have v0 : w π = μ * w 0 := by simpa using hper 0
      have c0 := congrFun hw.eq_combination π
      have c1 := hw.deriv_eq_mathieuWI_mathieuWII π
      ext i; fin_cases i
      · simp [mathieuMonodromy, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        rw [← v0, c0]; ring
      · simp [mathieuMonodromy, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        rw [← d1, c1]; ring
  · rintro ⟨v, hv, hM⟩
    have m0 := congrFun hM 0
    have m1 := congrFun hM 1
    simp [mathieuMonodromy, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at m0 m1
    set w := fun z => v 0 * mathieuWI a q z + v 1 * mathieuWII a q z with hwdef
    have hw : IsMathieuSolution a q w := (h1.const_mul _).add (h2.const_mul _)
    have hw0 : w 0 = v 0 := by simp [w, h10, h20]
    have hw1 : deriv w 0 = v 1 := by
      rw [hwdef, deriv_const_mul_add_const_mul (h1.differentiable 0) (h2.differentiable 0), h11,
          h21]
      ring
    refine ⟨w, hw, ?_, fun z => ?_⟩
    · intro hz
      apply hv
      have e0 : v 0 = 0 := by rw [← hw0, hz]; rfl
      have e1 : v 1 = 0 := by rw [← hw1, hz]; simp
      ext i; fin_cases i <;> simp [e0, e1]
    · have key := hw.comp_add_pi.eq_of_initial (hw.const_mul μ) (z₀ := 0)
        (by simp only [zero_add, w, h10, h20]; linear_combination m0)
        (by
          rw [deriv_comp_add_const, zero_add, deriv_const_mul _ (hw.differentiable 0), hw1,
            hwdef, deriv_const_mul_add_const_mul (h1.differentiable _) (h2.differentiable _)]
          linear_combination m1)
      exact congrFun key z

/-- **Characteristic equation** (DLMF 28.2.16): a Floquet solution with respect to `ν` exists iff
`cos πν = w_I(π; a, q)`. -/
@[dlmf 28.2.E16]
theorem exists_isFloquetSolution_iff_charExp (a q ν : ℂ) :
    (∃ w, IsFloquetSolution a q ν w) ↔ IsMathieuCharExp a q ν := by
  rw [exists_isFloquetSolution_iff]
  set μ := Complex.exp (π * I * ν)
  have hμ : μ ≠ 0 := Complex.exp_ne_zero _
  set M := mathieuMonodromy a q
  have e1 : (∃ v : Fin 2 → ℂ, v ≠ 0 ∧ M.mulVec v = μ • v) ↔
      ∃ v ≠ 0, (M - μ • (1 : Matrix (Fin 2) (Fin 2) ℂ)).mulVec v = 0 := by
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]
  rw [e1, Matrix.exists_mulVec_eq_zero_iff, Matrix.det_fin_two]
  have hW := mathieuWI_wronskian a q π
  have h9 := mathieuWI_pi_eq_deriv_mathieuWII_pi a q
  have hcos : Complex.cos (π * ν) = (μ + μ⁻¹) / 2 := by
    rw [Complex.cos, show (π : ℂ) * ν * I = π * I * ν by ring,
      show -((π : ℂ) * ν) * I = -(π * I * ν) by ring, Complex.exp_neg]
  simp only [M, mathieuMonodromy, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul]
  simp only [Fin.isValue, ↓reduceIte, mul_one, mul_zero, sub_zero, zero_ne_one, one_ne_zero]
  rw [IsMathieuCharExp, hcos]
  rw [← h9] at hW ⊢
  constructor
  · intro h
    field_simp
    linear_combination h - hW
  · intro h
    field_simp at h
    linear_combination h + hW

/-- **DLMF 28.2.16** (second equality): `w_I(π; a, q) = w_I(π; a, -q)`. -/
@[dlmf 28.2.E16]
theorem mathieuWI_pi_neg_q (a q : ℂ) : mathieuWI a q π = mathieuWI a (-q) π := by
  rw [mathieuWI_pi, mathieuWI_pi a (-q), mathieuWI_half_pi_neg_q,
    mathieuWII_half_pi_neg_q, deriv_mathieuWI_half_pi_neg_q,
    deriv_mathieuWII_half_pi_neg_q]
  ring

/-- **Connection formula** (DLMF 28.2.17): every solution satisfies
`w(z + π) + w(z - π) = 2 cos(πν) w(z)` for a characteristic exponent `ν`. -/
@[dlmf 28.2.E17]
theorem IsMathieuSolution.add_pi_add_sub_pi {a q ν : ℂ} {w : ℂ → ℂ}
    (h : IsMathieuSolution a q w) (hν : IsMathieuCharExp a q ν) (z : ℂ) :
    w (z + π) + w (z - π) = 2 * Complex.cos (π * ν) * w z := by
  have e := h.eq_combination
  rw [hν, e]
  simp only
  rw [mathieuWI_add_pi, mathieuWI_sub_pi, mathieuWII_add_pi, mathieuWII_sub_pi,
    ← mathieuWI_pi_eq_deriv_mathieuWII_pi]
  ring

/-- **Floquet dichotomy** (DLMF §28.2(iv)): a nontrivial solution `w` is either a Floquet solution
with respect to `ν`, or `w(z + π) - e^{iνπ} w(z)` is a Floquet solution with respect to `-ν`. -/
@[dlmf 28.2.iv]
theorem IsMathieuSolution.isFloquet_or {a q ν : ℂ} {w : ℂ → ℂ}
    (h : IsMathieuSolution a q w) (hw : w ≠ 0) (hν : IsMathieuCharExp a q ν) :
    IsFloquetSolution a q ν w ∨
      IsFloquetSolution a q (-ν) (fun z => w (z + π) - Complex.exp (I * ν * π) * w z) := by
  by_cases hu : (fun z => w (z + π) - Complex.exp (I * ν * π) * w z) = 0
  · left
    refine ⟨h, hw, fun z => ?_⟩
    have := congrFun hu z
    simp only [Pi.zero_apply] at this
    rw [show (π : ℂ) * I * ν = I * ν * π by ring]
    linear_combination this
  · right
    refine ⟨by simpa [sub_eq_add_neg] using
      h.comp_add_pi.add (h.const_mul (-Complex.exp (I * ν * π))), hu, fun z => ?_⟩
    · have h2 := h.add_pi_add_sub_pi hν (z + π)
      rw [show z + π - π = z by ring, show z + π + π = z + 2 * π by ring] at h2
      have hc : 2 * Complex.cos (π * ν) =
          Complex.exp (I * ν * π) + (Complex.exp (I * ν * π))⁻¹ := by
        rw [Complex.cos, show (π : ℂ) * ν * I = I * ν * π by ring,
          show -((π : ℂ) * ν) * I = -(I * ν * π) by ring, Complex.exp_neg]; ring
      rw [hc] at h2
      rw [show (π : ℂ) * I * -ν = -(I * ν * π) by ring, Complex.exp_neg]
      beta_reduce
      rw [show z + π + π = z + 2 * π by ring]
      have he : (Complex.exp (I * ν * π))⁻¹ * Complex.exp (I * ν * π) = 1 :=
        inv_mul_cancel₀ (Complex.exp_ne_zero _)
      linear_combination h2 + w z * he

end DLMF.Mathieu
