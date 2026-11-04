/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.MatrixArgument.Generalized
public import DLMF.MatrixArgument.MatrixIntegrals

/-!
# Bessel functions of matrix argument (DLMF §35.5)

Properties of the Bessel functions `A_ν` and `B_ν` of a real symmetric matrix argument. The
functions `matrixBesselA ν T` (DLMF 35.5.1–35.5.2) and `matrixBesselB ν T` (DLMF 35.5.3) are defined
in `DLMF.MatrixArgument.Basic`; here `Ω` is the cone of positive definite matrices and `𝓢` the
space of real symmetric matrices.

## Main results

* `matrixBesselA_zero`: `A_ν(0) = 1 / Γ_m(ν + (m+1)/2)` (DLMF 35.5.1), from 35.8.4 and 35.8.8.
* `integrableOn_matrixBesselB`: absolute convergence of the integral defining `B_ν(T)`
  (DLMF 35.5.3).
* `hasIntegralOn_matrixBesselA_laplace`: the Laplace transform of `|X|^ν A_ν(SX)` (DLMF 35.5.4).
* `hasIntegralOn_matrixBesselA_convolution`: the convolution formula DLMF 35.5.5.
* `matrixBesselB_neg`: the reflection `B_ν(T) = |T|^{-ν} B_{-ν}(T)` (DLMF 35.5.6), by the inversion
  `X ↦ X⁻¹` and congruence by `T^{1/2}`.
* `hasIntegralOn_matrixBesselA_mul_matrixBesselB`: the integral of `A_{ν₁} B_{-ν₂}` (DLMF 35.5.7).
* `integral_expTrace_orthogonal`: the integral of `expTrace(SH)` over the orthogonal group `O(m)`
  (DLMF 35.5.8).

## Implementation notes

Where DLMF evaluates a function of matrix argument at a product such as `SX` with `X ∈ Ω`, the
statements use `X^{1/2} S X^{1/2}`, which has the same eigenvalues. DLMF §35.5(iii) cites
references only.
-/

@[expose] public noncomputable section

open MeasureTheory Matrix Finset
open scoped Nat MatrixOrder ENNReal

namespace DLMF.MatrixArgument

/-- DLMF 35.5.1: `A_ν(0) = 1 / Γ_m(ν + (m+1)/2)` for `ν ∈ ℂ`. -/
@[dlmf 35.5.E1]
theorem matrixBesselA_zero {m : ℕ} (ν : ℂ) :
    matrixBesselA ν (0 : Matrix (Fin m) (Fin m) ℝ) = 1 /
        multivariateGamma m (ν + ((m : ℂ) + 1) / 2) := by
  rw [matrixBesselA_eq_matrixHypergeometric0F1, neg_zero, matrixHypergeometric0F1,
      matrixHypergeometricPFQ_zero, mul_one]

/-- Measurability of the integrand of `B_ν(T)` (35.5.3). -/
private lemma measurable_matrixBesselB_integrand {m : ℕ} (ν : ℂ) (T : Matrix (Fin m) (Fin m) ℝ) :
    Measurable (fun X : SymMatrix m =>
      (expTrace (-(T * (X : Matrix (Fin m) (Fin m) ℝ) + (X : Matrix (Fin m) (Fin m) ℝ)⁻¹)) : ℂ) *
        (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (ν - ((m : ℂ) + 1) / 2))) := by
  have hi := measurable_symMatrix_inv m
  have ht : (fun X : SymMatrix m => expTrace (-(T * (X : Matrix (Fin m) (Fin m) ℝ) +
      (X : Matrix (Fin m) (Fin m) ℝ)⁻¹))) = fun X : SymMatrix m => Real.exp
        (-(T * (X : Matrix (Fin m) (Fin m) ℝ)).trace -
          ((X : Matrix (Fin m) (Fin m) ℝ)⁻¹).trace) := by
    funext X; simp only [expTrace, Matrix.trace_neg, Matrix.trace_add]; ring_nf
  have h1 : Measurable fun X : SymMatrix m => expTrace (-(T * (X : Matrix (Fin m) (Fin m) ℝ) +
      (X : Matrix (Fin m) (Fin m) ℝ)⁻¹)) := by
    rw [ht]
    exact Real.measurable_exp.comp
      ((continuous_const.matrix_mul continuous_subtype_val).matrix_trace.measurable.neg.sub
        (continuous_id.matrix_trace.measurable.comp hi))
  exact (Complex.measurable_ofReal.comp h1).mul
    ((Complex.measurable_ofReal.comp continuous_subtype_val.matrix_det.measurable).pow_const _)

/-- DLMF 35.5.3: the integral defining `B_ν(T)` converges absolutely for `ν ∈ ℂ` and `T ∈ Ω`. -/
@[dlmf 35.5.E3]
theorem integrableOn_matrixBesselB {m : ℕ} (ν : ℂ) {T : Matrix (Fin m) (Fin m) ℝ} (hT : T.PosDef) :
    IntegrableOn (fun X : SymMatrix m =>
        (expTrace (-(T * (X : Matrix (Fin m) (Fin m) ℝ) + (X : Matrix (Fin m) (Fin m) ℝ)⁻¹)) : ℂ) *
          (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (ν - ((m : ℂ) + 1) / 2)))
      (posDefCone m) (TauCeti.symmetricLebesgue m) := by
  set K : ℕ := ⌈((m : ℝ) - 1) / 2 - ν.re⌉₊ + 1 with hK
  have hK' : ((m : ℝ) - 1) / 2 < ν.re + K := by
    have := Nat.le_ceil (((m : ℝ) - 1) / 2 - ν.re)
    rw [hK]; push_cast; linarith
  have hint := Matrix.PosDef.integrableOn_posDef_det_rpow_mul_exp_neg_trace_mul hT hK'
  have hmeas := measurable_matrixBesselB_integrand ν T
  refine (hint.const_mul ((m * K)! : ℝ)).mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (TauCeti.measurableSet_posDefMatrix m)] with X hX
  have hX : (X : Matrix (Fin m) (Fin m) ℝ).PosDef := hX
  set A : Matrix (Fin m) (Fin m) ℝ := (X : Matrix (Fin m) (Fin m) ℝ)
  have hdet := hX.det_pos
  have hYi : A⁻¹.PosDef := hX.inv
  have hdetinv : A⁻¹.det = A.det⁻¹ := by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  rw [norm_mul, Complex.norm_real]
  unfold expTrace
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Complex.norm_cpow_eq_rpow_re_of_pos hdet]
  have hre : (ν - ((m : ℂ) + 1) / 2).re = (ν.re + K - ((m : ℝ) + 1) / 2) - K := by
    simp; ring
  rw [hre, Real.rpow_sub hdet, Real.rpow_natCast, neg_add, Matrix.trace_add, Real.exp_add,
    Matrix.trace_neg, Matrix.trace_neg]
  -- `|X|^{-K} e^{-tr X⁻¹} ≤ (mK)!`
  have hbound : Real.exp (-A⁻¹.trace) / A.det ^ K ≤ ((m * K)! : ℝ) := by
    have htr : 0 ≤ A⁻¹.trace := by
      rw [hYi.isHermitian.trace_eq_sum_eigenvalues]
      exact Finset.sum_nonneg fun i _ => by simpa using (hYi.eigenvalues_pos i).le
    have h1 : (A.det ^ K)⁻¹ ≤ A⁻¹.trace ^ (m * K) := by
      rw [← inv_pow, ← hdetinv, pow_mul]
      exact pow_le_pow_left₀ hYi.det_pos.le (det_le_trace_pow_of_posDef hYi) K
    have h2 := Real.pow_div_factorial_le_exp _ htr (m * K)
    rw [div_le_iff₀ (by positivity)] at h2
    rw [div_eq_mul_inv]
    calc Real.exp (-A⁻¹.trace) * (A.det ^ K)⁻¹
        ≤ Real.exp (-A⁻¹.trace) * (Real.exp A⁻¹.trace * (m * K)!) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (Real.exp_pos _).le
      _ = _ := by rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  calc Real.exp (-(T * A).trace) * Real.exp (-A⁻¹.trace) *
        (A.det ^ (ν.re + K - ((m : ℝ) + 1) / 2) / A.det ^ K)
      = (Real.exp (-A⁻¹.trace) / A.det ^ K) *
          (A.det ^ (ν.re + K - ((m : ℝ) + 1) / 2) * Real.exp (-(T * A).trace)) := by ring
    _ ≤ ((m * K)! : ℝ) *
          (A.det ^ (ν.re + K - ((m : ℝ) + 1) / 2) * Real.exp (-(T * A).trace)) :=
        mul_le_mul_of_nonneg_right hbound (by positivity)


/-- DLMF 35.5.4: for `S ∈ 𝓢`, `T ∈ Ω` and `ℜν > -1`,
`∫_Ω expTrace(-TX) |X|^ν A_ν(SX) dX = expTrace(-ST⁻¹) |T|^{-ν-(m+1)/2}`. -/
@[dlmf 35.5.E4]
theorem hasIntegralOn_matrixBesselA_laplace {m : ℕ} {ν : ℂ} (hν : -1 < ν.re)
    {S T : Matrix (Fin m) (Fin m) ℝ} (hS : S.IsHermitian) (hT : T.PosDef) :
    HasIntegralOn (posDefCone m)
      (fun X => (expTrace (-(T * X)) : ℂ) * ((X.det : ℂ) ^ ν) *
          matrixBesselA ν (CFC.sqrt X * S * CFC.sqrt X))
      ((expTrace (-(S * T⁻¹)) : ℂ) * (T.det : ℂ) ^ (-ν - ((m : ℂ) + 1) / 2)) := by
  sorry

/-- DLMF 35.5.5: for `ℜν₁, ℜν₂ > -1`, `S₁, S₂ ∈ 𝓢` and `T ∈ Ω`,
`∫_{0<X<T} A_{ν₁}(S₁X) |X|^{ν₁} A_{ν₂}(S₂(T - X)) |T - X|^{ν₂} dX
  = |T|^{ν₁+ν₂+(m+1)/2} A_{ν₁+ν₂+(m+1)/2}((S₁ + S₂)T)`. -/
@[dlmf 35.5.E5]
theorem hasIntegralOn_matrixBesselA_convolution {m : ℕ} {ν₁ ν₂ : ℂ} (hν₁ : -1 < ν₁.re)
    (hν₂ : -1 < ν₂.re) {S₁ S₂ T : Matrix (Fin m) (Fin m) ℝ} (hS₁ : S₁.IsHermitian)
    (hS₂ : S₂.IsHermitian) (hT : T.PosDef) :
    HasIntegralOn (matrixInterval 0 T)
      (fun X => matrixBesselA ν₁ (CFC.sqrt X * S₁ * CFC.sqrt X) * ((X.det : ℂ) ^ ν₁) *
        matrixBesselA ν₂ (CFC.sqrt (T - X) * S₂ * CFC.sqrt (T - X)) * (((T - X).det : ℂ) ^ ν₂))
      ((T.det : ℂ) ^ (ν₁ + ν₂ + ((m : ℂ) + 1) / 2) *
        matrixBesselA (ν₁ + ν₂ + ((m : ℂ) + 1) / 2) (CFC.sqrt T * (S₁ + S₂) * CFC.sqrt T)) := by
  sorry

/-- DLMF 35.5.6: `B_ν(T) = |T|^{-ν} B_{-ν}(T)` for `ν ∈ ℂ` and `T ∈ Ω`. -/
@[dlmf 35.5.E6]
theorem matrixBesselB_neg {m : ℕ} (ν : ℂ) {T : Matrix (Fin m) (Fin m) ℝ} (hT : T.PosDef) :
    matrixBesselB ν T = (T.det : ℂ) ^ (-ν) * matrixBesselB (-ν) T := by
  have hsq : CFC.sqrt T * CFC.sqrt T = T := CFC.sqrt_mul_sqrt_self T hT.posSemidef.nonneg
  have htr : (CFC.sqrt T)ᵀ = CFC.sqrt T := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial,
      (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg T)).isHermitian.eq]
  have hdet : (CFC.sqrt T).det ≠ 0 := fun h => by
    have hpos := hT.det_pos
    rw [← hsq, Matrix.det_mul, h, mul_zero] at hpos
    exact lt_irrefl 0 hpos
  set C := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet with hCdef
  have hC : (C : Matrix (Fin m) (Fin m) ℝ) = CFC.sqrt T := rfl
  set R := CFC.sqrt T with hR
  have hRu : IsUnit R.det := isUnit_iff_ne_zero.mpr hdet
  have hTdet := hT.det_pos
  have hmc : MeasurableSet (posDefCone m) := TauCeti.measurableSet_posDefMatrix m
  unfold matrixBesselB
  -- inversion
  rw [show posDefCone m = posDefCone m from rfl,
    setIntegral_posDefCone_inv (measurable_matrixBesselB_integrand ν T)]
  have step2 : ∀ X ∈ posDefCone m,
      (((X : Matrix (Fin m) (Fin m) ℝ).det ^ (-((m : ℝ) + 1)) : ℝ) : ℂ) *
        ((expTrace (-(T * ((TauCeti.symmetricInv X : SymMatrix m) : Matrix (Fin m) (Fin m) ℝ) +
          ((TauCeti.symmetricInv X : SymMatrix m) : Matrix (Fin m) (Fin m) ℝ)⁻¹)) : ℂ) *
        ((((TauCeti.symmetricInv X : SymMatrix m) : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^
          (ν - ((m : ℂ) + 1) / 2))) =
      (expTrace (-(T * (X : Matrix (Fin m) (Fin m) ℝ)⁻¹ + (X : Matrix (Fin m) (Fin m) ℝ))) : ℂ) *
        (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (-ν - ((m : ℂ) + 1) / 2)) := by
    intro X hX
    have hX : (X : Matrix (Fin m) (Fin m) ℝ).PosDef := hX
    have hd := hX.det_pos
    rw [TauCeti.coe_symmetricInv, Matrix.nonsing_inv_nonsing_inv _ hd.ne'.isUnit,
      Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Complex.ofReal_inv,
      Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hd.le]; exact Real.pi_ne_zero.symm),
      Complex.ofReal_cpow hd.le, ← Complex.cpow_neg]
    have hne : ((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
    rw [mul_comm, mul_assoc, ← Complex.cpow_add _ _ hne]
    congr 2
    push_cast
    ring
  rw [setIntegral_congr_fun hmc step2]
  set F : SymMatrix m → ℂ := fun X =>
    (expTrace (-(T * (X : Matrix (Fin m) (Fin m) ℝ)⁻¹ + (X : Matrix (Fin m) (Fin m) ℝ))) : ℂ) *
      (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (-ν - ((m : ℂ) + 1) / 2)) with hF
  have hcong := Matrix.GeneralLinearGroup.integral_posDef_symmetricCongruence C F
  have hJ : (0 : ℝ) < |Matrix.det (C : Matrix (Fin m) (Fin m) ℝ)| ^ (m + 1) :=
    pow_pos (abs_pos.2 (Matrix.GeneralLinearGroup.det_ne_zero C)) _
  have hLHS : ∫ X in posDefCone m, F X ∂TauCeti.symmetricLebesgue m =
      (|Matrix.det (C : Matrix (Fin m) (Fin m) ℝ)| ^ (m + 1)) •
        ∫ A in posDefCone m, F (Matrix.GeneralLinearGroup.symmetricCongruence C A)
          ∂TauCeti.symmetricLebesgue m := by
    change _ = _ • ∫ A in {A : SymMatrix m | (A : Matrix (Fin m) (Fin m) ℝ).PosDef}, _ ∂_
    rw [hcong, smul_smul, mul_inv_cancel₀ hJ.ne', one_smul]
    rfl
  have step4 : ∀ A ∈ posDefCone m, F (Matrix.GeneralLinearGroup.symmetricCongruence C A) =
      (T.det : ℂ) ^ (-ν - ((m : ℂ) + 1) / 2) *
        ((expTrace (-(T * (A : Matrix (Fin m) (Fin m) ℝ) + (A : Matrix (Fin m) (Fin m) ℝ)⁻¹)) : ℂ) *
          (((A : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (-ν - ((m : ℂ) + 1) / 2))) := by
    intro A hA
    have hA : (A : Matrix (Fin m) (Fin m) ℝ).PosDef := hA
    rw [hF]
    simp only
    rw [Matrix.GeneralLinearGroup.coe_symmetricCongruence_apply, hC, htr]
    have hinv : (R * (A : Matrix (Fin m) (Fin m) ℝ) * R)⁻¹ =
        R⁻¹ * (A : Matrix (Fin m) (Fin m) ℝ)⁻¹ * R⁻¹ := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]
    have htr1 : (T * (R * (A : Matrix (Fin m) (Fin m) ℝ) * R)⁻¹).trace =
        ((A : Matrix (Fin m) (Fin m) ℝ)⁻¹).trace := by
      rw [hinv, ← hsq, Matrix.mul_assoc, Matrix.mul_assoc R⁻¹,
        Matrix.mul_nonsing_inv_cancel_left _ _ hRu, Matrix.trace_mul_comm, Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hRu, Matrix.mul_one]
    have htr2 : (R * (A : Matrix (Fin m) (Fin m) ℝ) * R).trace =
        (T * (A : Matrix (Fin m) (Fin m) ℝ)).trace := by
      rw [Matrix.trace_mul_cycle, hsq]
    have hdet2 : (R * (A : Matrix (Fin m) (Fin m) ℝ) * R).det =
        T.det * (A : Matrix (Fin m) (Fin m) ℝ).det := by
      rw [← hsq, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]; ring
    unfold expTrace
    rw [Matrix.trace_neg, Matrix.trace_add, htr1, htr2, hdet2, Matrix.trace_neg, Matrix.trace_add,
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hTdet.le hA.det_pos.le]
    ring_nf
  rw [hLHS, setIntegral_congr_fun hmc step4, integral_const_mul, Complex.real_smul, ← mul_assoc]
  congr 1
  have hd2 : |(C : Matrix (Fin m) (Fin m) ℝ).det| ^ 2 = T.det := by
    rw [sq_abs, hC, sq, ← Matrix.det_mul, hsq]
  have hpow : |(C : Matrix (Fin m) (Fin m) ℝ).det| ^ (m + 1) =
      T.det ^ (((m : ℝ) + 1) / 2) := by
    rw [← hd2, ← Real.rpow_natCast, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    push_cast; ring
  rw [hpow, Complex.ofReal_cpow hTdet.le, ← Complex.cpow_add _ _
    (Complex.ofReal_ne_zero.mpr hTdet.ne')]
  congr 1
  push_cast
  ring


/-- DLMF 35.5.7: for `ℜ(ν₁ + ν₂) > -1` and `S, T ∈ Ω`,
`∫_Ω A_{ν₁}(TX) B_{-ν₂}(SX) |X|^{ν₁} dX
  = |S|^{ν₂} |T + S|^{-(ν₁+ν₂+(m+1)/2)} / A_{ν₁+ν₂}(0)`. -/
@[dlmf 35.5.E7]
theorem hasIntegralOn_matrixBesselA_mul_matrixBesselB {m : ℕ} {ν₁ ν₂ : ℂ} (hν : -1 < (ν₁ + ν₂).re)
    {S T : Matrix (Fin m) (Fin m) ℝ} (hS : S.PosDef) (hT : T.PosDef) :
    HasIntegralOn (posDefCone m)
      (fun X => matrixBesselA ν₁ (CFC.sqrt X * T * CFC.sqrt X) *
        matrixBesselB (-ν₂) (CFC.sqrt X * S * CFC.sqrt X) * ((X.det : ℂ) ^ ν₁))
      (1 / matrixBesselA (ν₁ + ν₂) (0 : Matrix (Fin m) (Fin m) ℝ) * (S.det : ℂ) ^ ν₂ *
        ((T + S).det : ℂ) ^ (-(ν₁ + ν₂ + ((m : ℂ) + 1) / 2))) := by
  sorry

/-- DLMF 35.5.8: `∫_{O(m)} expTrace(SH) dH = A_{-1/2}(-¼ S Sᵀ) / A_{-1/2}(0)` for every real
`m × m` matrix `S`. -/
@[dlmf 35.5.E8]
theorem integral_expTrace_orthogonal {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) :
    ∫ H, (expTrace (S * (H : Matrix (Fin m) (Fin m) ℝ)) : ℂ) ∂orthogonalHaar m =
      matrixBesselA (-1 / 2) (-(1 / 4 : ℝ) • (S * Sᵀ)) /
        matrixBesselA (-1 / 2) (0 : Matrix (Fin m) (Fin m) ℝ) := by
  sorry

end DLMF.MatrixArgument
