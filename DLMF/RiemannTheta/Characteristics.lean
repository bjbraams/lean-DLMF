/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.RiemannTheta.Basic.Characteristics
public import DLMF.RiemannTheta.Scaled

/-!
# Examples of Riemann theta functions (DLMF 21.2.3–21.2.4, 21.4.2–21.4.3)

The example of DLMF 21.2.3–21.2.4 and the Riemann matrices of DLMF 21.4.2–21.4.3. The
characteristics and the genus-one reduction of DLMF §21.2 are in
`DLMF.RiemannTheta.Basic.Characteristics`.

## Main results

* `riemannMatrixExample_mem`, `riemannTheta_example`, `riemannThetaScaled_example`: the
  example DLMF 21.2.3–21.2.4.
* `riemannMatrixExample_eq_omegaOne`, `riemannMatrixOmegaTwo_mem`: the Riemann matrices of
  DLMF 21.4.2–21.4.3.
-/

@[expose] public noncomputable section

open Complex Matrix Finset Filter Topology
open scoped Real

variable {ι : Type*} [Fintype ι]

namespace DLMF.RiemannTheta

/-! ## The example of DLMF 21.2.3–21.2.4 and the Riemann matrices of §21.4 -/

/-- `Ω₁ = [[i, -1/2], [-1/2, i]]` of DLMF 21.4.2 (graphics section; exact matrix retained). -/
@[dlmf 21.4.E2]
theorem riemannMatrixExample_eq_omegaOne :
    riemannMatrixExample = !![I, -1 / 2; -1 / 2, I] := rfl

/-- Identity under the stated parameter and domain assumptions: `riemannMatrixExample.map
Complex.im = 1`. -/
theorem riemannMatrixExample_map_im : riemannMatrixExample.map Complex.im = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [riemannMatrixExample]

/-- The example matrix is a Riemann matrix. -/
@[dlmf 21.2.E3 "the example matrix lies in the Siegel upper half-space"]
theorem riemannMatrixExample_mem : riemannMatrixExample ∈ siegelUpperHalfSpace (Fin 2) := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [riemannMatrixExample]
  · rw [riemannMatrixExample_map_im]
    exact Matrix.PosDef.one

/-- Identity under the stated parameter and domain assumptions: `riemannThetaTerm z
riemannMatrixExample n = cexp (-π * ((n 0 : ℂ) ^ 2 + (n 1 : ℂ) ^ 2)) * cexp (-I * π * (n 0 * n
1 : ℂ)) * cexp (2 * π * I * (n 0 * z 0 + n 1 * z 1))`. -/
private lemma riemannThetaTerm_riemannMatrixExample (z : Fin 2 → ℂ) (n : Fin 2 → ℤ) :
    riemannThetaTerm z riemannMatrixExample n =
      cexp (-π * ((n 0 : ℂ) ^ 2 + (n 1 : ℂ) ^ 2)) * cexp (-I * π * (n 0 * n 1 : ℂ)) *
        cexp (2 * π * I * (n 0 * z 0 + n 1 * z 1)) := by
  rw [riemannThetaTerm, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp [riemannMatrixExample, dotProduct, mulVec, Fin.sum_univ_two]
  ring_nf
  rw [I_sq]
  ring

/-- The double series for the example (DLMF 21.2.3). -/
@[dlmf 21.2.E3]
theorem riemannTheta_example (z₁ z₂ : ℂ) :
    riemannTheta ![z₁, z₂] riemannMatrixExample =
      ∑' n₁ : ℤ, ∑' n₂ : ℤ, cexp (-π * ((n₁ : ℂ) ^ 2 + (n₂ : ℂ) ^ 2)) *
        cexp (-I * π * (n₁ * n₂ : ℂ)) * cexp (2 * π * I * (n₁ * z₁ + n₂ * z₂)) := by
  have hs := (summable_norm_riemannThetaTerm ![z₁, z₂] riemannMatrixExample_mem).of_norm
  rw [riemannTheta, ← (finTwoArrowEquiv ℤ).symm.tsum_eq]
  have hs' := (finTwoArrowEquiv ℤ).symm.summable_iff.mpr hs
  refine (hs'.tsum_prod).trans ?_
  refine tsum_congr fun n₁ => tsum_congr fun n₂ => ?_
  rw [Function.comp_apply, riemannThetaTerm_riemannMatrixExample]
  simp

/-- The scaled double series for the example (DLMF 21.2.4), `z_j = x_j + i y_j`. -/
@[dlmf 21.2.E4]
theorem riemannThetaScaled_example (x₁ y₁ x₂ y₂ : ℝ) :
    riemannThetaScaled ![x₁ + y₁ * I, x₂ + y₂ * I] riemannMatrixExample =
      ∑' n₁ : ℤ, ∑' n₂ : ℤ, cexp (-π * ((n₁ + y₁ : ℂ) ^ 2) - π * ((n₂ + y₂ : ℂ) ^ 2)) *
        cexp (π * I * (2 * n₁ * x₁ + 2 * n₂ * x₂ - n₁ * n₂)) := by
  rw [riemannThetaScaled, riemannTheta_example, riemannMatrixExample_map_im, inv_one,
    one_mulVec, ← tsum_mul_left]
  refine tsum_congr fun n₁ => ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun n₂ => ?_
  have hy : ((fun i => ((![x₁ + y₁ * I, x₂ + y₂ * I] : Fin 2 → ℂ) i).im) ⬝ᵥ
      fun i => ((![x₁ + y₁ * I, x₂ + y₂ * I] : Fin 2 → ℂ) i).im) = y₁ ^ 2 + y₂ ^ 2 := by
    simp [dotProduct, Fin.sum_univ_two, sq]
  rw [hy, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- `Ω₂` of DLMF 21.4.3 is a Riemann matrix. -/
@[dlmf 21.4.E3 "Ω₂ lies in the Siegel upper half-space"]
theorem riemannMatrixOmegaTwo_mem : riemannMatrixOmegaTwo ∈ siegelUpperHalfSpace (Fin 3) := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [riemannMatrixOmegaTwo]
  · refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [riemannMatrixOmegaTwo]
    · have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 ∨ x 2 ≠ 0 := by
        by_contra h
        push Not at h
        exact hx (by ext i; fin_cases i <;> simp [h.1, h.2.1, h.2.2])
      simp [riemannMatrixOmegaTwo, dotProduct, mulVec, Fin.sum_univ_three]
      rcases hx' with h | h | h
      · have := pow_pos (abs_pos.mpr h) 2
        nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 - x 2), sq_nonneg (x 1),
          sq_nonneg (x 2), sq_abs (x 0)]
      · have := pow_pos (abs_pos.mpr h) 2
        nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 - x 2), sq_nonneg (x 1),
          sq_nonneg (x 2), sq_abs (x 1)]
      · have := pow_pos (abs_pos.mpr h) 2
        nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 - x 2), sq_nonneg (x 1),
          sq_nonneg (x 2), sq_abs (x 2)]

end DLMF.RiemannTheta
