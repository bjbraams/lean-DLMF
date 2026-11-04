/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.MatrixArgument.Basic
public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy
public import TauCeti.Analysis.Matrix.Sqrt
public import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
public import TauCeti.Analysis.SpecialFunctions.MultivariateGamma.Basic
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Cholesky
public import TauCeti.LinearAlgebra.Matrix.Triangular
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Congruence
public import TauCeti.Analysis.SpecialFunctions.MultivariateGamma.Integral
public import DLMF.MatrixArgument.GammaBeta.GammaIntegrals

/-!
# Integrals for the multivariate beta function (DLMF §35.3)

Congruence by a Cholesky factor scales the beta integrand on the matrix interval `0 < X < T`
to the one on `0 < X < I`; Fubini and the translation `T = X + Y` give
`Γ_m(a) Γ_m(b) = Γ_m(a + b) B_m(a, b)`.

## Main results

* `multivariateBeta_eq_integral`: the beta integral 35.3.3.
* `multivariateGammaVec_const`, `multivariateBeta_one`: 35.3.6 and the case `m = 1` (35.3.7).
* `multivariateBeta_eq_integral_posDefCone`: the integral over `Ω` (35.3.8).
-/

@[expose] public noncomputable section

open MeasureTheory Matrix Finset Set
open scoped ENNReal

namespace DLMF.MatrixArgument

/-! ### The beta integral 35.3.3

Congruence by a Cholesky factor of `T` scales the beta integrand on `0 < X < T` to the one on
`0 < X < I`; Fubini applied to `∫∫ expTrace(-X)|X|^{a-(m+1)/2} expTrace(-Y)|Y|^{b-(m+1)/2}` with the
translation `T = X + Y` then gives `Γ_m(a) Γ_m(b) = Γ_m(a + b) B_m(a, b)`. -/

/-- Integrability of the indicated kernel: `Integrable (fun A => f
(Matrix.GeneralLinearGroup.symmetricCongruence C A)) (TauCeti.symmetricLebesgue m) ↔
Integrable f (TauCeti.symmetricLebesgue m)`. -/
private lemma integrable_symmetricCongruence_iff {m : ℕ} (C : Matrix.GeneralLinearGroup (Fin m) ℝ)
    (f : SymMatrix m → ℂ) :
    Integrable (fun A => f (Matrix.GeneralLinearGroup.symmetricCongruence C A))
      (TauCeti.symmetricLebesgue m) ↔ Integrable f (TauCeti.symmetricLebesgue m) := by
  have hC : (0 : ℝ) < |Matrix.det (C : Matrix (Fin m) (Fin m) ℝ)| :=
    abs_pos.2 (Matrix.GeneralLinearGroup.det_ne_zero C)
  have h := integrable_map_equiv (μ := TauCeti.symmetricLebesgue m)
    (Matrix.GeneralLinearGroup.symmetricCongruence C).toHomeomorph.toMeasurableEquiv f
  rw [Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph,
    Matrix.GeneralLinearGroup.map_symmetricCongruence_symmetricLebesgue,
    integrable_smul_measure] at h
  · exact h.symm
  · exact ENNReal.inv_ne_zero.mpr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  · exact ENNReal.inv_ne_top.mpr (pow_ne_zero _ (ENNReal.ofReal_pos.mpr hC).ne')

/-- Identity under the stated parameter and domain assumptions: `∫ A, f
(Matrix.GeneralLinearGroup.symmetricCongruence C A) ∂TauCeti.symmetricLebesgue m =
(|Matrix.det (C : Matrix (Fin m) (Fin m) ℝ)| ^ (m + 1))⁻¹ • ∫ A, f A
∂TauCeti.symmetricLebesgue m`. -/
private lemma integral_symmetricCongruence {m : ℕ} (C : Matrix.GeneralLinearGroup (Fin m) ℝ)
    (f : SymMatrix m → ℂ) :
    ∫ A, f (Matrix.GeneralLinearGroup.symmetricCongruence C A) ∂TauCeti.symmetricLebesgue m =
      (|Matrix.det (C : Matrix (Fin m) (Fin m) ℝ)| ^ (m + 1))⁻¹ •
        ∫ A, f A ∂TauCeti.symmetricLebesgue m := by
  have hJ : (0 : ℝ) < |Matrix.det (C : Matrix (Fin m) (Fin m) ℝ)| ^ (m + 1) :=
    pow_pos (abs_pos.2 (Matrix.GeneralLinearGroup.det_ne_zero C)) _
  have h := integral_map_equiv (μ := TauCeti.symmetricLebesgue m)
    (Matrix.GeneralLinearGroup.symmetricCongruence C).toHomeomorph.toMeasurableEquiv f
  rw [Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph] at h
  rw [← h, Matrix.GeneralLinearGroup.map_symmetricCongruence_symmetricLebesgue,
    integral_smul_measure, ENNReal.toReal_inv, ← ENNReal.ofReal_pow (abs_nonneg _),
    ENNReal.toReal_ofReal hJ.le]

/-- The stated relation follows from the given hypotheses: `((C : Matrix (Fin m) (Fin m) ℝ) * M *
(C : Matrix (Fin m) (Fin m) ℝ)ᵀ).PosDef ↔ M.PosDef`. -/
private lemma posDef_mul_mul_transpose_iff {m : ℕ} (C : Matrix.GeneralLinearGroup (Fin m) ℝ)
    (M : Matrix (Fin m) (Fin m) ℝ) :
    ((C : Matrix (Fin m) (Fin m) ℝ) * M * (C : Matrix (Fin m) (Fin m) ℝ)ᵀ).PosDef ↔ M.PosDef := by
  rw [← conjTranspose_eq_transpose_of_trivial, ← star_eq_conjTranspose,
    IsUnit.posDef_star_right_conjugate_iff (Units.isUnit C)]

/-- The beta integrand on `0 < X < T`, extended by zero. -/
private lemma integrable_indicator_matrixInterval_beta_iff {m : ℕ} {T : Matrix (Fin m) (Fin m) ℝ}
    (hT : T.PosDef) (a b : ℂ) :
    (Integrable (fun X : SymMatrix m => (matrixInterval 0 T).indicator (fun X : SymMatrix m =>
        (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (a - ((m : ℂ) + 1) / 2)) *
        (((T - (X : Matrix (Fin m) (Fin m) ℝ)).det : ℂ) ^ (b - ((m : ℂ) + 1) / 2))) X)
        (TauCeti.symmetricLebesgue m) ↔
      Integrable (fun X : SymMatrix m => (matrixInterval 0 1).indicator (fun X : SymMatrix m =>
        (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (a - ((m : ℂ) + 1) / 2)) *
        (((1 - (X : Matrix (Fin m) (Fin m) ℝ)).det : ℂ) ^ (b - ((m : ℂ) + 1) / 2))) X)
        (TauCeti.symmetricLebesgue m)) ∧
    ∫ X : SymMatrix m, (matrixInterval 0 T).indicator (fun X : SymMatrix m =>
        (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (a - ((m : ℂ) + 1) / 2)) *
        (((T - (X : Matrix (Fin m) (Fin m) ℝ)).det : ℂ) ^ (b - ((m : ℂ) + 1) / 2))) X
        ∂TauCeti.symmetricLebesgue m =
      (T.det : ℂ) ^ (a + b - ((m : ℂ) + 1) / 2) *
      ∫ X : SymMatrix m, (matrixInterval 0 1).indicator (fun X : SymMatrix m =>
        (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (a - ((m : ℂ) + 1) / 2)) *
        (((1 - (X : Matrix (Fin m) (Fin m) ℝ)).det : ℂ) ^ (b - ((m : ℂ) + 1) / 2))) X
        ∂TauCeti.symmetricLebesgue m := by
  set P : ℂ := ((m : ℂ) + 1) / 2 with hP
  set A : TauCeti.PosDefMatrix m :=
    ⟨⟨T, Matrix.isHermitian_iff_isSelfAdjoint.mp hT.isHermitian⟩, hT⟩
  set L := (TauCeti.cholesky A).1
  have hLL : L * Lᵀ = T := TauCeti.cholesky_mul_transpose A
  have hTd := hT.det_pos
  have hdetLL : L.det ^ 2 = T.det := by
    have h := congrArg Matrix.det hLL
    rw [Matrix.det_mul, Matrix.det_transpose] at h
    rw [sq, h]
  have hdetL : L.det ≠ 0 := fun h => by
    rw [h] at hdetLL; simp at hdetLL; exact hTd.ne' hdetLL.symm
  set C := Matrix.GeneralLinearGroup.mkOfDetNeZero L hdetL
  have hC : (C : Matrix (Fin m) (Fin m) ℝ) = L := rfl
  set βT : SymMatrix m → ℂ := fun X => (matrixInterval 0 T).indicator (fun X : SymMatrix m =>
    (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (a - P)) *
    (((T - (X : Matrix (Fin m) (Fin m) ℝ)).det : ℂ) ^ (b - P))) X with hβT
  set β1 : SymMatrix m → ℂ := fun X => (matrixInterval 0 1).indicator (fun X : SymMatrix m =>
    (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (a - P)) *
    (((1 - (X : Matrix (Fin m) (Fin m) ℝ)).det : ℂ) ^ (b - P))) X with hβ1
  set k : ℂ := (T.det : ℂ) ^ (a - P) * (T.det : ℂ) ^ (b - P)
  have hk : k ≠ 0 := by
    have hne : (T.det : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hTd.ne'
    refine mul_ne_zero ?_ ?_ <;>
    · rw [Complex.cpow_def_of_ne_zero hne]; exact Complex.exp_ne_zero _
  have hpt : ∀ U : SymMatrix m,
      βT (Matrix.GeneralLinearGroup.symmetricCongruence C U) = k * β1 U := by
    intro U
    have hsub : T - L * (U : Matrix (Fin m) (Fin m) ℝ) * Lᵀ =
        L * (1 - (U : Matrix (Fin m) (Fin m) ℝ)) * Lᵀ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hLL]
    have hmemiff : Matrix.GeneralLinearGroup.symmetricCongruence C U ∈ matrixInterval 0 T ↔
        U ∈ matrixInterval 0 1 := by
      simp only [matrixInterval, Set.mem_ofPred_eq, sub_zero,
        Matrix.GeneralLinearGroup.coe_symmetricCongruence_apply, hC]
      rw [hsub, ← hC, posDef_mul_mul_transpose_iff, posDef_mul_mul_transpose_iff]
    simp only [hβT, hβ1]
    by_cases hU : U ∈ matrixInterval 0 1
    · rw [Set.indicator_of_mem (hmemiff.mpr hU), Set.indicator_of_mem hU]
      have hU1 : (U : Matrix (Fin m) (Fin m) ℝ).PosDef := by simpa [matrixInterval] using hU.1
      have hU2 : (1 - (U : Matrix (Fin m) (Fin m) ℝ)).PosDef := hU.2
      simp only [Matrix.GeneralLinearGroup.coe_symmetricCongruence_apply, hC]
      rw [hsub]
      have hd1 : (L * (U : Matrix (Fin m) (Fin m) ℝ) * Lᵀ).det =
          T.det * (U : Matrix (Fin m) (Fin m) ℝ).det := by
        rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← hdetLL]; ring
      have hd2 : (L * (1 - (U : Matrix (Fin m) (Fin m) ℝ)) * Lᵀ).det =
          T.det * (1 - (U : Matrix (Fin m) (Fin m) ℝ)).det := by
        rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← hdetLL]; ring
      rw [hd1, hd2, Complex.ofReal_mul, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg hTd.le hU1.det_pos.le,
        Complex.mul_cpow_ofReal_nonneg hTd.le hU2.det_pos.le]
      ring
    · rw [Set.indicator_of_notMem (fun h => hU (hmemiff.mp h)), Set.indicator_of_notMem hU,
        mul_zero]
  have hcomp : (fun U => βT (Matrix.GeneralLinearGroup.symmetricCongruence C U)) =
      fun U => k * β1 U := funext hpt
  refine ⟨?_, ?_⟩
  · rw [← integrable_symmetricCongruence_iff C βT, hcomp]
    exact ⟨fun h => by simpa [← mul_assoc, inv_mul_cancel₀ hk] using h.const_mul k⁻¹,
      fun h => h.const_mul k⟩
  · have h := integral_symmetricCongruence C βT
    rw [hcomp, integral_const_mul] at h
    have hJ : (0 : ℝ) < |Matrix.det (C : Matrix (Fin m) (Fin m) ℝ)| ^ (m + 1) :=
      pow_pos (abs_pos.2 (Matrix.GeneralLinearGroup.det_ne_zero C)) _
    have h2 : ∫ X, βT X ∂TauCeti.symmetricLebesgue m =
        ((|Matrix.det (C : Matrix (Fin m) (Fin m) ℝ)| ^ (m + 1) : ℝ) : ℂ) * (k * ∫ X, β1 X
          ∂TauCeti.symmetricLebesgue m) := by
      rw [h, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hJ.ne',
        Complex.ofReal_one, one_mul]
    rw [h2, hC]
    have habs : |L.det| ^ (m + 1) = T.det ^ (((m : ℝ) + 1) / 2) := by
      rw [← hdetLL, ← sq_abs, ← Real.rpow_natCast, ← Real.rpow_natCast _ 2,
        ← Real.rpow_mul (abs_nonneg _)]
      congr 1
      push_cast; ring
    have hne : (T.det : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hTd.ne'
    rw [habs, Complex.ofReal_cpow hTd.le, ← mul_assoc]
    congr 1
    simp only [k]
    rw [← Complex.cpow_add _ _ hne, ← Complex.cpow_add _ _ hne]
    congr 1
    simp only [P]; push_cast; ring

/-- The stated relation follows from the given hypotheses: `M.PosDef`. -/
private lemma posDef_fin_zero (M : Matrix (Fin 0) (Fin 0) ℝ) : M.PosDef :=
  Matrix.PosDef.of_dotProduct_mulVec_pos (by ext i; exact i.elim0)
    (fun x hx => absurd (Subsingleton.elim x 0) hx)

/-- Formula under the stated hypotheses: `X ∈ matrixInterval 0 T ↔ X ∈ posDefCone m ∧ (T - (X :
Matrix (Fin m) (Fin m) ℝ)).PosDef`. -/
private lemma mem_matrixInterval_zero_iff {m : ℕ} (T : Matrix (Fin m) (Fin m) ℝ) (X : SymMatrix m) :
    X ∈ matrixInterval 0 T ↔ X ∈ posDefCone m ∧ (T - (X : Matrix (Fin m) (Fin m) ℝ)).PosDef := by
  simp [matrixInterval, posDefCone]

/-- The stated relation follows from the given hypotheses: `MeasurableSet (matrixInterval 0 (T :
Matrix (Fin m) (Fin m) ℝ))`. -/
private lemma measurableSet_matrixInterval_zero {m : ℕ} (T : SymMatrix m) :
    MeasurableSet (matrixInterval 0 (T : Matrix (Fin m) (Fin m) ℝ)) := by
  have hmc : MeasurableSet (posDefCone m) := TauCeti.measurableSet_posDefMatrix m
  have : matrixInterval 0 (T : Matrix (Fin m) (Fin m) ℝ) =
      posDefCone m ∩ (fun X => T - X) ⁻¹' posDefCone m := by
    ext X; rw [mem_matrixInterval_zero_iff]; rfl
  rw [this]
  exact hmc.inter (hmc.preimage (measurable_const.sub measurable_id))

/-- Identity under the stated parameter and domain assumptions: `matrixInterval (m := m) 0 T = ∅`.
-/
private lemma matrixInterval_zero_eq_empty_of_not_posDef {m : ℕ} {T : Matrix (Fin m) (Fin m) ℝ}
    (hT : ¬ T.PosDef) :
    matrixInterval (m := m) 0 T = ∅ := by
  ext X
  simp only [Set.mem_empty_iff_false, iff_false]
  intro h
  obtain ⟨hX, hTX⟩ := (mem_matrixInterval_zero_iff T X).mp h
  apply hT
  have := (show ((X : Matrix (Fin m) (Fin m) ℝ)).PosDef from hX).add hTX
  rwa [add_sub_cancel] at this

/-- DLMF 35.3.3 for `m ≥ 1`. -/
private lemma hasIntegralOn_matrixInterval_multivariateBeta {m : ℕ} (hm : 1 ≤ m) {a b : ℂ}
    (ha : ((m : ℝ) - 1) / 2 < a.re)
    (hb : ((m : ℝ) - 1) / 2 < b.re) :
    HasIntegralOn (m := m) (matrixInterval 0 1)
      (fun X => ((X.det : ℂ) ^ (a - ((m : ℂ) + 1) / 2)) *
        (((1 - X).det : ℂ) ^ (b - ((m : ℂ) + 1) / 2)))
      (multivariateBeta m a b) := by
  set Λ := TauCeti.symmetricLebesgue m
  have hmc : MeasurableSet (posDefCone m) := TauCeti.measurableSet_posDefMatrix m
  set P : ℂ := ((m : ℂ) + 1) / 2 with hP
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hab : ((m : ℝ) - 1) / 2 < (a + b).re := by rw [Complex.add_re]; linarith
  set g : ℂ → SymMatrix m → ℂ := fun s => (posDefCone m).indicator (fun X : SymMatrix m =>
    (expTrace (-(X : Matrix (Fin m) (Fin m) ℝ)) : ℂ) *
      (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (s - P))) with hg
  have hgint : ∀ s : ℂ, ((m : ℝ) - 1) / 2 < s.re → Integrable (g s) Λ :=
    fun s hs => (integrable_indicator_iff hmc).mpr (multivariateGamma_eq_integral hs).1
  have hgval : ∀ s : ℂ, ((m : ℝ) - 1) / 2 < s.re → ∫ X, g s X ∂Λ = multivariateGamma m s := by
    intro s hs
    rw [integral_indicator hmc]
    exact (multivariateGamma_eq_integral hs).2
  have hgm : ∀ s : ℂ, Measurable (g s) := by
    intro s
    refine Measurable.indicator ?_ hmc
    unfold expTrace
    exact (Complex.measurable_ofReal.comp (Real.measurable_exp.comp
      continuous_subtype_val.neg.matrix_trace.measurable)).mul (measurable_det_cpow _)
  set K : SymMatrix m → SymMatrix m → ℂ := fun X T => g a X * g b (T - X) with hKdef
  have hK : Integrable (Function.uncurry K) (Λ.prod Λ) := by
    have hKm : Measurable (Function.uncurry K) :=
      ((hgm a).comp measurable_fst).mul ((hgm b).comp (measurable_snd.sub measurable_fst))
    rw [integrable_prod_iff hKm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun X => ?_, ?_⟩
    · exact ((hgint b hb).comp_sub_right X).const_mul (g a X)
    · refine ((hgint a ha).norm.mul_const (∫ Y, ‖g b Y‖ ∂Λ)).congr
        (Filter.Eventually.of_forall fun X => ?_)
      simp only [Function.uncurry_apply_pair, hKdef, norm_mul]
      rw [integral_const_mul, integral_sub_right_eq_self (fun Y => ‖g b Y‖) X]
  set β : Matrix (Fin m) (Fin m) ℝ → SymMatrix m → ℂ := fun T X =>
    (matrixInterval 0 T).indicator (fun X : SymMatrix m =>
      (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (a - P)) *
      (((T - (X : Matrix (Fin m) (Fin m) ℝ)).det : ℂ) ^ (b - P))) X with hβ
  have hKβ : ∀ X T : SymMatrix m,
      K X T = (expTrace (-(T : Matrix (Fin m) (Fin m) ℝ)) : ℂ) * β T X := by
    intro X T
    simp only [hKdef, hg, hβ]
    by_cases hX : X ∈ posDefCone m
    · by_cases hTX : T - X ∈ posDefCone m
      · have hXI : X ∈ matrixInterval 0 (T : Matrix (Fin m) (Fin m) ℝ) :=
          (mem_matrixInterval_zero_iff _ X).mpr ⟨hX, hTX⟩
        rw [Set.indicator_of_mem hX, Set.indicator_of_mem hTX, Set.indicator_of_mem hXI,
          Submodule.coe_sub]
        have he : (expTrace (-(X : Matrix (Fin m) (Fin m) ℝ)) : ℂ) *
            (expTrace (-((T : Matrix (Fin m) (Fin m) ℝ) - (X : Matrix (Fin m) (Fin m) ℝ))) : ℂ) =
            (expTrace (-(T : Matrix (Fin m) (Fin m) ℝ)) : ℂ) := by
          unfold expTrace
          rw [← Complex.ofReal_mul, ← Real.exp_add, Matrix.trace_neg, Matrix.trace_neg,
            Matrix.trace_neg, Matrix.trace_sub]
          ring_nf
        rw [← he]
        ring
      · have hXI : X ∉ matrixInterval 0 (T : Matrix (Fin m) (Fin m) ℝ) := fun h =>
          hTX ((mem_matrixInterval_zero_iff _ X).mp h).2
        rw [Set.indicator_of_notMem hTX, Set.indicator_of_notMem hXI]
        simp
    · have hXI : X ∉ matrixInterval 0 (T : Matrix (Fin m) (Fin m) ℝ) :=
        fun h => hX ((mem_matrixInterval_zero_iff _ X).mp h).1
      rw [Set.indicator_of_notMem hX, Set.indicator_of_notMem hXI]
      simp
  -- integrability of the beta integrand
  have hΩ : Λ.restrict (posDefCone m) ≠ 0 := by
    intro h0
    have h := (multivariateGamma_eq_integral ha).2
    rw [h0, integral_zero_measure] at h
    exact multivariateGamma_ne_zero_of_re_gt ha h.symm
  have : (ae (Λ.restrict (posDefCone m))).NeBot := ae_neBot.mpr hΩ
  obtain ⟨T, hTint, hTΩ⟩ := ((ae_restrict_of_ae hK.prod_left_ae).and
    (ae_restrict_mem hmc)).exists
  have hTpos : (T : Matrix (Fin m) (Fin m) ℝ).PosDef := hTΩ
  have hβT : Integrable (β T) Λ := by
    have he : (expTrace (-(T : Matrix (Fin m) (Fin m) ℝ)) : ℂ) ≠ 0 := by
      unfold expTrace; exact Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
    have := hTint.const_mul (expTrace (-(T : Matrix (Fin m) (Fin m) ℝ)) : ℂ)⁻¹
    refine this.congr (Filter.Eventually.of_forall fun X => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [hKβ, ← mul_assoc, inv_mul_cancel₀ he, one_mul]
  have hβ1 : Integrable (β 1) Λ :=
      ((integrable_indicator_matrixInterval_beta_iff hTpos a b).1).mp hβT
  -- the value
  set J := ∫ X, β 1 X ∂Λ
  have hleft : ∫ X, ∫ T, K X T ∂Λ ∂Λ = multivariateGamma m a * multivariateGamma m b := by
    have : ∀ X, ∫ T, K X T ∂Λ = g a X * multivariateGamma m b := by
      intro X
      simp only [hKdef]
      rw [integral_const_mul, integral_sub_right_eq_self (g b) X, hgval b hb]
    simp_rw [this]
    rw [integral_mul_const, hgval a ha]
  have hright : ∫ T, ∫ X, K X T ∂Λ ∂Λ = J * multivariateGamma m (a + b) := by
    have : ∀ T : SymMatrix m, ∫ X, K X T ∂Λ = (posDefCone m).indicator (fun T : SymMatrix m =>
        (expTrace (-(T : Matrix (Fin m) (Fin m) ℝ)) : ℂ) *
          (((T : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (a + b - P)) * J) T := by
      intro T
      simp_rw [hKβ]
      rw [integral_const_mul]
      by_cases hT : T ∈ posDefCone m
      · rw [Set.indicator_of_mem hT, (integrable_indicator_matrixInterval_beta_iff hT a b).2]
        ring
      · rw [Set.indicator_of_notMem hT]
        have h0 : ∀ X, β T X = 0 := fun X => by
          simp only [hβ]
          rw [matrixInterval_zero_eq_empty_of_not_posDef hT, Set.indicator_empty]
        simp [h0]
    simp_rw [this]
    rw [integral_indicator hmc, integral_mul_const, (multivariateGamma_eq_integral hab).2]
    ring
  have hmI1 : MeasurableSet (matrixInterval (m := m) 0 1) :=
    measurableSet_matrixInterval_zero ⟨1, IsSelfAdjoint.one _⟩
  have hβ1eq : β 1 = (matrixInterval 0 1).indicator (fun X : SymMatrix m =>
      (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (a - P)) *
      (((1 - (X : Matrix (Fin m) (Fin m) ℝ)).det : ℂ) ^ (b - P))) := rfl
  refine ⟨(integrable_indicator_iff hmI1).mp (hβ1eq ▸ hβ1), ?_⟩
  rw [← integral_indicator hmI1, ← hβ1eq]
  change J = _
  have hΓ := multivariateGamma_ne_zero_of_re_gt hab
  have key : J * multivariateGamma m (a + b) =
      multivariateGamma m a * multivariateGamma m b := by
    rw [← hright, ← hleft, integral_integral_swap hK]
  unfold multivariateBeta
  rw [← key]
  field_simp

/-- DLMF 35.3.3: `B_m(a, b) = ∫_{0<X<I} |X|^{a-(m+1)/2} |I - X|^{b-(m+1)/2} dX` for
`ℜa, ℜb > (m-1)/2`. -/
@[dlmf 35.3.E3]
theorem multivariateBeta_eq_integral {m : ℕ} {a b : ℂ} (ha : ((m : ℝ) - 1) / 2 < a.re)
    (hb : ((m : ℝ) - 1) / 2 < b.re) :
    HasIntegralOn (m := m) (matrixInterval 0 1)
      (fun X => ((X.det : ℂ) ^ (a - ((m : ℂ) + 1) / 2)) *
        (((1 - X).det : ℂ) ^ (b - ((m : ℂ) + 1) / 2)))
      (multivariateBeta m a b) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hset : matrixInterval (m := 0) 0 1 = posDefCone 0 := by
      ext X
      simp only [matrixInterval, posDefCone, Set.mem_ofPred_eq]
      exact ⟨fun _ => posDef_fin_zero _, fun _ => ⟨posDef_fin_zero _,
        posDef_fin_zero _⟩⟩
    have h := multivariateGamma_eq_integral (m := 0) (a := 1) (by norm_num)
    have hv : multivariateBeta 0 a b = multivariateGamma 0 1 := by
      simp [multivariateBeta, multivariateGamma]
    rw [hv, hset]
    refine hasIntegralOn_posDefCone_congr h fun X _ => ?_
    simp [expTrace, Matrix.det_isEmpty, Matrix.trace]
  · exact hasIntegralOn_matrixInterval_multivariateBeta hm ha hb

/-- DLMF 35.3.6: `Γ_m(a, …, a) = Γ_m(a)`. -/
@[dlmf 35.3.E6]
theorem multivariateGammaVec_const (m : ℕ) (a : ℂ) :
    multivariateGammaVec m (fun _ => a) = multivariateGamma m a := rfl

/-- DLMF 35.3.7 for `m = 1`: `B₁(a, b) = Γ(a) Γ(b) / Γ(a + b)`. -/
@[dlmf 35.3.E7]
theorem multivariateBeta_one (a b : ℂ) :
    multivariateBeta 1 a b = Complex.Gamma a * Complex.Gamma b / Complex.Gamma (a + b) := by
  simp [multivariateBeta, multivariateGamma_one]

/-- DLMF 35.3.8: `B_m(a, b) = ∫_Ω |X|^{a-(m+1)/2} |I + X|^{-(a+b)} dX` for
`ℜa, ℜb > (m-1)/2`. -/
@[dlmf 35.3.E8]
theorem multivariateBeta_eq_integral_posDefCone {m : ℕ} {a b : ℂ}
    (ha : ((m : ℝ) - 1) / 2 < a.re) (hb : ((m : ℝ) - 1) / 2 < b.re) :
    HasIntegralOn (posDefCone m)
      (fun X => ((X.det : ℂ) ^ (a - ((m : ℂ) + 1) / 2)) * (((1 + X).det : ℂ) ^ (-(a + b))))
      (multivariateBeta m a b) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using hasIntegralOn_posDefCone_multivariateBeta_zero (a := a) (b := b)
  · exact hasIntegralOn_posDefCone_multivariateBeta hm ha hb

end DLMF.MatrixArgument
