/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.MatrixArgument.Basic
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Inv

/-!
# Helpers for integrals over the positive-definite cone (DLMF Chapter 35)

General facts used by the integral formulas of §§35.5–35.6:

* `q2m_det_le_trace_pow`: `|Y| ≤ (tr Y)^m` for positive-definite `Y`;
* `q2m_measurable_inv`: measurability of `X ↦ X⁻¹` on `𝓢` (from Tau Ceti's `symmetricInv`);
* `q2m_setIntegral_posDef_inv`: the inversion change of variables
  `∫_Ω g(X) dX = ∫_Ω |X|^{-(m+1)} g(X⁻¹) dX`, from Tau Ceti's
  `TauCeti.map_symmetricInv_symmetricLebesgue`;
* `q2m_det_one_add`: `|I + X| = ∏ (1 + λ_i)` for symmetric `X`;
* `q2m_exists_posDef_sub_smul`: `T - εI ∈ Ω` for `T ∈ Ω` and small `ε > 0`.
-/

@[expose] public noncomputable section

open MeasureTheory Matrix Finset
open scoped ENNReal

namespace DLMF.MatrixArgument

/-- For positive-definite `Y`, `|Y| ≤ (tr Y)^m`. -/
theorem q2m_det_le_trace_pow {m : ℕ} {Y : Matrix (Fin m) (Fin m) ℝ} (hY : Y.PosDef) :
    Y.det ≤ Y.trace ^ m := by
  rw [hY.isHermitian.det_eq_prod_eigenvalues, hY.isHermitian.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id]
  have hnn : ∀ i, 0 ≤ hY.isHermitian.eigenvalues i := fun i => (hY.eigenvalues_pos i).le
  calc ∏ i, hY.isHermitian.eigenvalues i ≤ ∏ _i : Fin m, ∑ j, hY.isHermitian.eigenvalues j :=
        Finset.prod_le_prod₀ (fun i _ => hnn i)
          (fun i _ => Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i))
    _ = _ := by simp

/-- Measurability of `X ↦ X⁻¹` on `𝓢`. -/
theorem q2m_measurable_inv (m : ℕ) :
    Measurable (fun X : SymMatrix m => (X : Matrix (Fin m) (Fin m) ℝ)⁻¹) := by
  have h : (fun X : SymMatrix m => (X : Matrix (Fin m) (Fin m) ℝ)⁻¹) =
      fun X => ((TauCeti.symmetricInv X : SymMatrix m) : Matrix (Fin m) (Fin m) ℝ) :=
    funext fun X => (TauCeti.coe_symmetricInv X).symm
  rw [h]
  exact measurable_subtype_coe.comp TauCeti.measurable_symmetricInv

/-- The inversion change of variables on `Ω`: `∫_Ω g(X) dX = ∫_Ω |X|^{-(m+1)} g(X⁻¹) dX`. -/
theorem q2m_setIntegral_posDef_inv {m : ℕ} {g : SymMatrix m → ℂ} (hg : Measurable g) :
    ∫ X in posDefCone m, g X ∂TauCeti.symmetricLebesgue m =
      ∫ X in posDefCone m, (((X : Matrix (Fin m) (Fin m) ℝ).det ^ (-((m : ℝ) + 1)) : ℝ) : ℂ) *
        g (TauCeti.symmetricInv X) ∂TauCeti.symmetricLebesgue m := by
  have hset : posDefCone m = {A : SymMatrix m | (A : Matrix (Fin m) (Fin m) ℝ).PosDef} := rfl
  have hmeas := TauCeti.measurableSet_posDefMatrix m
  rw [hset]
  calc ∫ X in {A : SymMatrix m | (A : Matrix (Fin m) (Fin m) ℝ).PosDef}, g X
        ∂TauCeti.symmetricLebesgue m
      = ∫ X in {A : SymMatrix m | (A : Matrix (Fin m) (Fin m) ℝ).PosDef},
          (g ∘ TauCeti.symmetricInv) (TauCeti.symmetricInv X) ∂TauCeti.symmetricLebesgue m := by
        refine setIntegral_congr_fun hmeas fun X hX => ?_
        simp only [Function.comp_apply]
        rw [TauCeti.symmetricInv_symmetricInv (show (X : Matrix (Fin m)
          (Fin m) ℝ).PosDef from hX).det_pos.ne']
    _ = ∫ Y, (g ∘ TauCeti.symmetricInv) Y ∂(((TauCeti.symmetricLebesgue m).restrict
          {A : SymMatrix m | (A : Matrix (Fin m) (Fin m) ℝ).PosDef}).map
            TauCeti.symmetricInv) := by
        rw [integral_map TauCeti.measurable_symmetricInv.aemeasurable
          (hg.comp TauCeti.measurable_symmetricInv).aestronglyMeasurable]
    _ = _ := by
        rw [TauCeti.map_symmetricInv_symmetricLebesgue,
          integral_withDensity_eq_integral_toReal_smul (by fun_prop)
            (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
        refine setIntegral_congr_fun hmeas fun X hX => ?_
        rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (show (X : Matrix (Fin m)
          (Fin m) ℝ).PosDef from hX).det_pos.le _), Complex.real_smul]
        rfl

/-- `|I + X| = ∏ (1 + λ_i)` for real symmetric `X`. -/
theorem q2m_det_one_add {m : ℕ} {X : Matrix (Fin m) (Fin m) ℝ} (hX : X.IsHermitian) :
    (1 + X).det = ∏ i, (1 + hX.eigenvalues i) := by
  set U := hX.eigenvectorUnitary
  have h := hX.spectral_theorem
  have h1 : 1 + X = (U : Matrix (Fin m) (Fin m) ℝ) *
      diagonal (fun i => 1 + hX.eigenvalues i) * star (U : Matrix (Fin m) (Fin m) ℝ) := by
    conv_lhs => rw [h]
    rw [Unitary.conjStarAlgAut_apply]
    have hu : (U : Matrix (Fin m) (Fin m) ℝ) * star (U : Matrix (Fin m) (Fin m) ℝ) = 1 :=
      Unitary.mul_star_self_of_mem U.2
    have hd : diagonal (fun i => 1 + hX.eigenvalues i) =
        1 + diagonal (RCLike.ofReal ∘ hX.eigenvalues) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [hd, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hu]
  rw [h1, det_mul, det_mul, det_diagonal, mul_comm, ← mul_assoc, ← det_mul,
    Unitary.star_mul_self_of_mem U.2, det_one, one_mul]




/-- A positive-definite `T` stays positive definite after subtracting a small multiple of `I`. -/
theorem q2m_exists_posDef_sub_smul {m : ℕ} {T : Matrix (Fin m) (Fin m) ℝ} (hT : T.PosDef) :
    ∃ ε : ℝ, 0 < ε ∧ (T - ε • (1 : Matrix (Fin m) (Fin m) ℝ)).PosDef := by
  set T' : SymMatrix m := ⟨T, Matrix.isHermitian_iff_isSelfAdjoint.mp hT.isHermitian⟩
  set I' : SymMatrix m := ⟨1, Matrix.isHermitian_iff_isSelfAdjoint.mp Matrix.isHermitian_one⟩
  have hU := TauCeti.isOpen_setOfPred_posDefMatrix m
  have hγ : Continuous fun ε : ℝ => T' - ε • I' :=
    continuous_const.sub (continuous_id.smul continuous_const)
  have h0 : (fun ε : ℝ => T' - ε • I') 0 ∈
      {A : SymMatrix m | (A : Matrix (Fin m) (Fin m) ℝ).PosDef} := by
    simpa [T'] using hT
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hU.preimage hγ) 0 h0
  refine ⟨r / 2, by positivity, ?_⟩
  have hmem := hball (show r / 2 ∈ Metric.ball (0 : ℝ) r by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith)
  simpa [T', I'] using hmem

end DLMF.MatrixArgument
