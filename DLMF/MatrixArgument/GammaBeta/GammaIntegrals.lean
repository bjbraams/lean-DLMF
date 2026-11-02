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
public import DLMF.MatrixArgument.GammaBeta.CholeskyCoordinates

/-!
# Integrals for the multivariate gamma function (DLMF §35.3)

The integral representations of `Γ_m(a)` and `Γ_m(s₁, …, s_m)` for complex parameters, and
the scaled Laplace integrals over `Ω` used for 35.3.8 and 35.4.8. The bridge to Tau Ceti's real
`Γ_m` and the case `m = 1` (35.3.4) are in `DLMF.MatrixArgument.Basic`.

## Main results

* `multivariateGamma_eq_integral`, `multivariateGammaVec_eq_integral`: 35.3.1 and 35.3.2.
* `hasIntegralOn_laplace_leadingMinorPowProd`:
  `∫_Ω etr(-SY) |Y|^{a-(m+1)/2} φ_κ(Y) dY = Γ_m(a + κ) |S|^{-a} φ_κ(S⁻¹)` for the leading-minor
  product `φ_κ`.
* `hasIntegralOn_posDefCone_multivariateBeta`: the double integral over `Ω × Ω` behind 35.3.8.
-/

@[expose] public noncomputable section

open MeasureTheory Matrix Finset Set
open scoped ENNReal

namespace DLMF.MatrixArgument

/-! ## §35.3 Multivariate gamma and beta functions -/

/-- DLMF 35.3.1: `Γ_m(a) = ∫_Ω etr(-X) |X|^{a-(m+1)/2} dX` for `ℜa > (m-1)/2`, the integral
converging absolutely. For real `a` this is Tau Ceti's `TauCeti.integral_posDef_multivariateGamma`
(see `DLMF.MatrixArgument.multivariateGamma_ofReal`). -/
@[dlmf 35.3.E1]
theorem multivariateGamma_eq_integral {m : ℕ} {a : ℂ} (ha : ((m : ℝ) - 1) / 2 < a.re) :
    HasIntegralOn (posDefCone m)
      (fun X => (etr (-X) : ℂ) * ((X.det : ℂ) ^ (a - ((m : ℂ) + 1) / 2)))
      (multivariateGamma m a) := by
  have hs : ∀ j : Fin m, (j : ℝ) / 2 < ((fun _ : Fin m => a) j).re := by
    intro j
    have : (j : ℝ) + 1 ≤ m := by exact_mod_cast j.2
    simp only
    linarith
  have h := hasIntegralOn_multivariateGammaVecIntegrand hs
  change HasIntegralOn _ _ (multivariateGammaVec m fun _ => a)
  convert h using 2 with X
  unfold multivariateGammaVecIntegrand
  congr 1
  rcases m with _ | k
  · simp
  · rw [Fin.prod_univ_castSucc]
    have h1 : ∀ j : Fin k, ((leadingMinor X (j.castSucc.1 + 1) : ℝ) : ℂ) ^
        (multivariateGammaVecExponent (fun _ : Fin (k + 1) => a) j.castSucc) = 1 := by
      intro j
      rw [multivariateGammaVecExponent, dite_eq_left (by simp), sub_self, Complex.cpow_zero]
    simp_rw [h1, Finset.prod_const_one, one_mul]
    rw [multivariateGammaVecExponent, dite_eq_right (by simp), leadingMinor, dite_eq_left (by simp)]
    simp

/-- DLMF 35.3.2: `Γ_m(s₁, …, s_m) = ∫_Ω etr(-X) |X|^{s_m-(m+1)/2} ∏_{j=1}^{m-1}
|(X)_j|^{s_j - s_{j+1}} dX` for `ℜs_j > (j-1)/2`. In Lean the indices are zero-based and the
factors are combined as `∏_{j=1}^{m} |(X)_j|^{s_j - s_{j+1}}` with `s_{m+1} = (m+1)/2`
(the factor `j = m` is `|X|^{s_m - (m+1)/2}`). -/
@[dlmf 35.3.E2]
theorem multivariateGammaVec_eq_integral {m : ℕ} {s : Fin m → ℂ}
    (hs : ∀ j : Fin m, (j : ℝ) / 2 < (s j).re) :
    HasIntegralOn (posDefCone m)
      (fun X => (etr (-X) : ℂ) * ∏ j : Fin m, ((leadingMinor X (j.1 + 1) : ℝ) : ℂ) ^
        (s j - if h : j.1 + 1 < m then s ⟨j.1 + 1, h⟩ else ((m : ℂ) + 1) / 2))
      (multivariateGammaVec m s) := by
  exact hasIntegralOn_multivariateGammaVecIntegrand hs

/-! ### Laplace integrals over `Ω` and the beta integral 35.3.8

The Cholesky substitution turns 35.3.2 into the scaled form
`∫_Ω etr(-SY) |Y|^{a-(m+1)/2} φ_κ(Y) dY = Γ_m(a + κ) |S|^{-a} φ_κ(S⁻¹)` for the leading-minor
product `φ_κ` (used for 35.4.8), and the case `κ = 0` gives
`∫_Ω etr(-SY) |Y|^{a-(m+1)/2} dY = Γ_m(a) |S|^{-a}`. Fubini then gives 35.3.8. -/

section LaplaceTransform
/-- The stated relation follows from the given hypotheses: `HasIntegralOn (posDefCone m) g I`. -/
theorem hasIntegralOn_posDefCone_congr {m : ℕ} {f g : Matrix (Fin m) (Fin m) ℝ → ℂ} {I : ℂ}
    (h : HasIntegralOn (posDefCone m) f I) (hfg : ∀ X : SymMatrix m, X ∈ posDefCone m →
      f X = g X) : HasIntegralOn (posDefCone m) g I := by
  have hmc : MeasurableSet (posDefCone m) := TauCeti.measurableSet_posDefMatrix m
  refine ⟨h.1.congr_fun (fun X hX => hfg X hX) hmc, ?_⟩
  rw [← h.2]
  exact (setIntegral_congr_fun hmc fun X hX => hfg X hX).symm

/-- Identity under the stated parameter and domain assumptions: `HasIntegralOn (posDefCone m) (fun
X => c * f X) (c * I)`. -/
theorem hasIntegralOn_posDefCone_const_mul {m : ℕ} {f : Matrix (Fin m) (Fin m) ℝ → ℂ} {I : ℂ}
    (h : HasIntegralOn (posDefCone m) f I) (c : ℂ) :
    HasIntegralOn (posDefCone m) (fun X => c * f X) (c * I) :=
  ⟨h.1.const_mul c, by rw [integral_const_mul, h.2]⟩

/-- Congruence change of variables for `HasIntegralOn` over `Ω`. -/
theorem hasIntegralOn_posDefCone_of_congruence {m : ℕ} (C : Matrix.GeneralLinearGroup (Fin m) ℝ)
    {F : Matrix (Fin m) (Fin m) ℝ → ℂ} (hF : Measurable fun X : SymMatrix m => F X) {I : ℂ}
    (h : HasIntegralOn (posDefCone m) (fun A => F ((C : Matrix (Fin m) (Fin m) ℝ) * A *
      (C : Matrix (Fin m) (Fin m) ℝ)ᵀ)) I) :
    HasIntegralOn (posDefCone m) F
      (((|(C : Matrix (Fin m) (Fin m) ℝ).det| ^ (m + 1) : ℝ) : ℂ) * I) := by
  have hJ : (0 : ℝ) < |Matrix.det (C : Matrix (Fin m) (Fin m) ℝ)| ^ (m + 1) :=
    pow_pos (abs_pos.2 (Matrix.GeneralLinearGroup.det_ne_zero C)) _
  have hcomp : ∀ A : SymMatrix m, F ((C : Matrix (Fin m) (Fin m) ℝ) * A *
      (C : Matrix (Fin m) (Fin m) ℝ)ᵀ) =
      F (Matrix.GeneralLinearGroup.symmetricCongruence C A) := fun A => by
    rw [Matrix.GeneralLinearGroup.coe_symmetricCongruence_apply]
  refine ⟨⟨hF.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_enorm]
    have hl := Matrix.GeneralLinearGroup.lintegral_posDef_symmetricCongruence C
      (fun X : SymMatrix m => ‖F X‖ₑ)
    have hfin := h.1.2
    rw [hasFiniteIntegral_iff_enorm] at hfin
    simp_rw [hcomp] at hfin
    change ∫⁻ A in {A : SymMatrix m | (A : Matrix (Fin m) (Fin m) ℝ).PosDef},
      ‖F (Matrix.GeneralLinearGroup.symmetricCongruence C A)‖ₑ ∂_ < ∞ at hfin
    rw [hl] at hfin
    change ∫⁻ A in {A : SymMatrix m | (A : Matrix (Fin m) (Fin m) ℝ).PosDef}, ‖F A‖ₑ ∂_ < ∞
    have hne : (ENNReal.ofReal |Matrix.det (C : Matrix (Fin m) (Fin m) ℝ)| ^ (m + 1))⁻¹ ≠ 0 :=
      ENNReal.inv_ne_zero.mpr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    exact (ENNReal.mul_lt_top_iff.mp hfin).elim (fun h => h.2)
      (fun h => h.elim (fun h0 => absurd h0 hne) (fun h0 => h0 ▸ ENNReal.zero_lt_top))
  · have hi := Matrix.GeneralLinearGroup.integral_posDef_symmetricCongruence C
      (fun X : SymMatrix m => F X)
    have h2 := h.2
    simp_rw [hcomp] at h2
    change ∫ A in {A : SymMatrix m | (A : Matrix (Fin m) (Fin m) ℝ).PosDef},
      F (Matrix.GeneralLinearGroup.symmetricCongruence C A) ∂_ = I at h2
    rw [hi] at h2
    change ∫ A in {A : SymMatrix m | (A : Matrix (Fin m) (Fin m) ℝ).PosDef}, F A ∂_ = _
    rw [← h2, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hJ.ne',
      Complex.ofReal_one, one_mul]

/-- The product `∏_j |(Y)_j|^{k_j - k_{j+1}}` of leading minors in 35.4.3. -/
def leadingMinorPowProd {m : ℕ} (κ : Fin m → ℕ) (Y : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ∏ j : Fin m, leadingMinor Y (j.1 + 1) ^ (κ j - nextPart κ j)

/-- Estimate under the stated parameter and domain assumptions: `0 < leadingMinor X (j.1 + 1)`. -/
private lemma leadingMinor_pos_of_posDef {m : ℕ} {X : Matrix (Fin m) (Fin m) ℝ}
    (hX : X.PosDef) (j : Fin m) :
    0 < leadingMinor X (j.1 + 1) := by
  have hj : j.1 + 1 ≤ m := j.2
  rw [leadingMinor, dite_eq_left hj]
  exact (hX.submatrix (Fin.castLE_injective hj)).det_pos

/-- Estimate under the stated parameter and domain assumptions: `0 < leadingMinorPowProd κ X`. -/
theorem leadingMinorPowProd_pos {m : ℕ} (κ : Fin m → ℕ) {X : Matrix (Fin m) (Fin m) ℝ}
    (hX : X.PosDef) :
    0 < leadingMinorPowProd κ X :=
  Finset.prod_pos fun j _ => pow_pos (leadingMinor_pos_of_posDef hX j) _

/-- 35.3.2 with `s_j = a + k_j`: `∫_Ω etr(-X) |X|^{a-(m+1)/2} φ_κ(X) dX = Γ_m(a + κ)`. -/
private lemma hasIntegralOn_etr_neg_mul_leadingMinorPowProd {m : ℕ} (κ : Fin m → ℕ)
    (hκ : Antitone κ) {a : ℂ}
    (ha : ((m : ℝ) - 1) / 2 < a.re) :
    HasIntegralOn (posDefCone m) (fun Z => (etr (-Z) : ℂ) * ((Z.det : ℂ) ^ (a - ((m : ℂ) + 1) / 2))
      * (leadingMinorPowProd κ Z : ℂ)) (multivariateGammaVec m (fun j => a + κ j)) := by
  have hs : ∀ j : Fin m, (j : ℝ) / 2 < ((fun j => a + (κ j : ℂ)) j).re := by
    intro j
    have : (j : ℝ) + 1 ≤ m := by exact_mod_cast j.2
    simp only [Complex.add_re, Complex.natCast_re]
    have := (κ j).cast_nonneg (α := ℝ)
    linarith
  refine hasIntegralOn_posDefCone_congr
      (hasIntegralOn_multivariateGammaVecIntegrand hs) fun Z hZ => ?_
  have hZ : (Z : Matrix (Fin m) (Fin m) ℝ).PosDef := hZ
  unfold multivariateGammaVecIntegrand leadingMinorPowProd
  rw [mul_assoc]
  congr 1
  push_cast
  have hterm : ∀ j : Fin m, ((leadingMinor (Z : Matrix (Fin m) (Fin m) ℝ) (j.1 + 1) : ℝ) : ℂ) ^
      (multivariateGammaVecExponent (fun j => a + (κ j : ℂ)) j) =
      ((leadingMinor (Z : Matrix (Fin m) (Fin m) ℝ) (j.1 + 1) : ℝ) : ℂ) ^ (κ j - nextPart κ j) *
        (if j.1 + 1 = m then ((Z : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^
          (a - ((m : ℂ) + 1) / 2) else 1) := by
    intro j
    have hpos := leadingMinor_pos_of_posDef hZ j
    have hne : ((leadingMinor (Z : Matrix (Fin m) (Fin m) ℝ) (j.1 + 1) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hpos.ne'
    unfold multivariateGammaVecExponent
    split_ifs with h1 h2 h2
    · omega
    · have hn : nextPart κ j = κ ⟨j.1 + 1, h1⟩ := by rw [nextPart, dite_eq_left h1]
      have hle : κ ⟨j.1 + 1, h1⟩ ≤ κ j := hκ (Fin.mk_le_mk.mpr (by omega))
      rw [mul_one, hn, ← Complex.cpow_natCast, Nat.cast_sub hle]
      congr 1; ring
    · have hn : nextPart κ j = 0 := by rw [nextPart, dite_eq_right h1]
      have hdet : leadingMinor (Z : Matrix (Fin m) (Fin m) ℝ) (j.1 + 1) =
          (Z : Matrix (Fin m) (Fin m) ℝ).det := by
        rw [leadingMinor, dite_eq_left (show j.1 + 1 ≤ m from j.2)]
        have hce : (Fin.castLE (show j.1 + 1 ≤ m from j.2) : Fin (j.1 + 1) → Fin m) =
            ⇑(finCongr h2) := by
          funext i; ext; simp
        rw [hce, Matrix.det_submatrix_equiv_self]
      rw [hn, Nat.sub_zero, ← hdet, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hne]
      congr 1; ring
    · omega
  simp_rw [hterm]
  rw [Finset.prod_mul_distrib, mul_comm]
  congr 1
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  · rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
    have hfilt : (Finset.univ.filter fun j : Fin m => j.1 + 1 = m) = {⟨m - 1, by omega⟩} := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h; ext; simp; omega
      · rintro rfl; simp; omega
    rw [hfilt, Finset.prod_singleton]

/-- Estimate under the stated parameter and domain assumptions: `leadingMinor (L * Lᵀ) (j.1 + 1) =
∏ i ∈ Finset.univ.filter (· ≤ j), L i i ^ 2`. -/
private lemma leadingMinor_mul_transpose_of_isLowerTriangular {m : ℕ} {L : Matrix (Fin m) (Fin m) ℝ}
    (hL : L.IsLowerTriangular)
    (j : Fin m) : leadingMinor (L * Lᵀ) (j.1 + 1) =
      ∏ i ∈ Finset.univ.filter (· ≤ j), L i i ^ 2 := by
  have h := leadingMinor_lowerTriangleMatrix_mul_transpose
      (fun ij : TauCeti.lowerTriangle m => L ij.1.1 ij.1.2) j
  rw [TauCeti.lowerTriangleMatrix_entries hL] at h
  rw [h, Finset.prod_ite, Finset.prod_const_one, mul_one]

/-- `φ_κ(L Z Lᵀ) = φ_κ(L Lᵀ) φ_κ(Z)` for lower-triangular `L` and `Z ∈ Ω`. -/
private lemma leadingMinorPowProd_lower_conj {m : ℕ} (κ : Fin m → ℕ) {L : Matrix (Fin m) (Fin m) ℝ}
    (hL : L.IsLowerTriangular) {Z : Matrix (Fin m) (Fin m) ℝ} (hZ : Z.PosDef) :
    leadingMinorPowProd κ (L * Z * Lᵀ) = leadingMinorPowProd κ (L * Lᵀ) *
        leadingMinorPowProd κ Z := by
  set A : TauCeti.PosDefMatrix m :=
    ⟨⟨Z, Matrix.isHermitian_iff_isSelfAdjoint.mp hZ.isHermitian⟩, hZ⟩
  set M := (TauCeti.cholesky A).1
  have hM : M.IsLowerTriangular := (TauCeti.cholesky A).2.1
  have hMM : M * Mᵀ = Z := TauCeti.cholesky_mul_transpose A
  have hLM : (L * M).IsLowerTriangular := hL.mul hM
  have hconj : L * Z * Lᵀ = (L * M) * (L * M)ᵀ := by
    rw [← hMM, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  unfold leadingMinorPowProd
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← mul_pow, hconj, leadingMinor_mul_transpose_of_isLowerTriangular hLM,
      leadingMinor_mul_transpose_of_isLowerTriangular hL, ← hMM,
    leadingMinor_mul_transpose_of_isLowerTriangular hM, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply_diag_of_isLowerTriangular hL hM, mul_pow]

/-- Continuity of the indicated function:
`Continuous fun Y : Matrix (Fin m) (Fin m) ℝ => leadingMinorPowProd κ Y`. -/
theorem continuous_leadingMinorPowProd {m : ℕ} (κ : Fin m → ℕ) :
    Continuous fun Y : Matrix (Fin m) (Fin m) ℝ => leadingMinorPowProd κ Y := by
  unfold leadingMinorPowProd
  refine continuous_finsetProd _ fun j _ => (Continuous.pow ?_ _)
  have hj : j.1 + 1 ≤ m := j.2
  simp only [leadingMinor, hj, dite_true]
  exact (continuous_id.matrix_submatrix _ _).matrix_det

/-- The Laplace integral of `φ_κ`: for `S ∈ Ω`,
`∫_Ω etr(-SY) |Y|^{a-(m+1)/2} φ_κ(Y) dY = Γ_m(a + κ) |S|^{-a} φ_κ(S⁻¹)`. -/
theorem hasIntegralOn_laplace_leadingMinorPowProd {m : ℕ} (κ : Fin m → ℕ) (hκ : Antitone κ)
    {S : Matrix (Fin m) (Fin m) ℝ} (hS : S.PosDef) {a : ℂ} (ha : ((m : ℝ) - 1) / 2 < a.re) :
    HasIntegralOn (posDefCone m) (fun Y => (etr (-(S * Y)) : ℂ) *
      ((Y.det : ℂ) ^ (a - ((m : ℂ) + 1) / 2)) * (leadingMinorPowProd κ Y : ℂ))
      (multivariateGammaVec m (fun j => a + κ j) * (S.det : ℂ) ^ (-a) *
        (leadingMinorPowProd κ S⁻¹ : ℂ)) := by
  set A : TauCeti.PosDefMatrix m :=
    ⟨⟨S⁻¹, Matrix.isHermitian_iff_isSelfAdjoint.mp hS.inv.isHermitian⟩, hS.inv⟩
  set L := (TauCeti.cholesky A).1
  have hL : L.IsLowerTriangular := (TauCeti.cholesky A).2.1
  have hLL : L * Lᵀ = S⁻¹ := TauCeti.cholesky_mul_transpose A
  have hSd := hS.det_pos
  have hSu : IsUnit S.det := hSd.ne'.isUnit
  have hdetLL : L.det ^ 2 = S.det⁻¹ := by
    have h := congrArg Matrix.det hLL
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv] at h
    rw [sq, h]
  have hdetL : L.det ≠ 0 := fun h => by
    rw [h] at hdetLL; simp at hdetLL; exact hSd.ne' hdetLL.symm
  set C := Matrix.GeneralLinearGroup.mkOfDetNeZero L hdetL
  have hC : (C : Matrix (Fin m) (Fin m) ℝ) = L := rfl
  have hLSL : Lᵀ * (S * L) = 1 := by
    have : S * L * Lᵀ = 1 := by rw [Matrix.mul_assoc, hLL, Matrix.mul_nonsing_inv _ hSu]
    exact mul_eq_one_comm.mp this
  have hF : Measurable fun Y : SymMatrix m => (etr (-(S * (Y : Matrix (Fin m) (Fin m) ℝ))) : ℂ) *
      (((Y : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (a - ((m : ℂ) + 1) / 2)) *
      (leadingMinorPowProd κ (Y : Matrix (Fin m) (Fin m) ℝ) : ℂ) := by
    unfold etr
    refine ((Complex.measurable_ofReal.comp ?_).mul
      ((Complex.measurable_ofReal.comp continuous_subtype_val.matrix_det.measurable).pow_const
        _)).mul (Complex.measurable_ofReal.comp
          ((continuous_leadingMinorPowProd κ).comp continuous_subtype_val).measurable)
    exact Real.measurable_exp.comp
      (continuous_const.matrix_mul continuous_subtype_val).neg.matrix_trace.measurable
  set c : ℂ := ((S.det⁻¹ : ℝ) : ℂ) ^ (a - ((m : ℂ) + 1) / 2) * (leadingMinorPowProd κ S⁻¹ : ℂ)
  have h1 := hasIntegralOn_posDefCone_const_mul
      (hasIntegralOn_etr_neg_mul_leadingMinorPowProd κ hκ ha) c
  have h2 : HasIntegralOn (posDefCone m) (fun Z => (etr (-(S * ((C : Matrix (Fin m) (Fin m) ℝ) *
      Z * (C : Matrix (Fin m) (Fin m) ℝ)ᵀ))) : ℂ) * ((((C : Matrix (Fin m) (Fin m) ℝ) * Z *
        (C : Matrix (Fin m) (Fin m) ℝ)ᵀ).det : ℂ) ^ (a - ((m : ℂ) + 1) / 2)) *
      (leadingMinorPowProd κ
          ((C : Matrix (Fin m) (Fin m) ℝ) * Z * (C : Matrix (Fin m) (Fin m) ℝ)ᵀ) : ℂ))
      (c * multivariateGammaVec m (fun j => a + κ j)) := by
    refine hasIntegralOn_posDefCone_congr h1 fun Z hZ => ?_
    have hZ : (Z : Matrix (Fin m) (Fin m) ℝ).PosDef := hZ
    rw [hC, leadingMinorPowProd_lower_conj κ hL hZ, hLL]
    have htr : (S * (L * (Z : Matrix (Fin m) (Fin m) ℝ) * Lᵀ)).trace =
        (Z : Matrix (Fin m) (Fin m) ℝ).trace := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
        hLSL, Matrix.one_mul]
    have hdet : (L * (Z : Matrix (Fin m) (Fin m) ℝ) * Lᵀ).det =
        S.det⁻¹ * (Z : Matrix (Fin m) (Fin m) ℝ).det := by
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← hdetLL]; ring
    unfold etr
    rw [Matrix.trace_neg, Matrix.trace_neg, htr, hdet, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (inv_pos.mpr hSd).le hZ.det_pos.le, Complex.ofReal_mul]
    ring
  have h3 := hasIntegralOn_posDefCone_of_congruence (F := fun Y => (etr (-(S * Y)) : ℂ) *
    ((Y.det : ℂ) ^ (a - ((m : ℂ) + 1) / 2)) * (leadingMinorPowProd κ Y : ℂ)) C hF h2
  convert h3 using 1
  -- the scalar
  rw [hC]
  have habs : |L.det| ^ (m + 1) = S.det⁻¹ ^ (((m : ℝ) + 1) / 2) := by
    rw [← hdetLL, ← sq_abs, ← Real.rpow_natCast, ← Real.rpow_natCast _ 2,
      ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    push_cast; ring
  have hinvpos : 0 < S.det⁻¹ := inv_pos.mpr hSd
  rw [habs, Complex.ofReal_cpow hinvpos.le]
  have hne : ((S.det⁻¹ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hinvpos.ne'
  have hpow : ((S.det⁻¹ : ℝ) : ℂ) ^ ((((m : ℝ) + 1) / 2 : ℝ) : ℂ) *
      ((S.det⁻¹ : ℝ) : ℂ) ^ (a - ((m : ℂ) + 1) / 2) = (S.det : ℂ) ^ (-a) := by
    have harg : ((S.det : ℝ) : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hSd.le]; exact Real.pi_ne_zero.symm
    rw [← Complex.cpow_add _ _ hne, Complex.ofReal_inv, Complex.inv_cpow _ _ harg,
      ← Complex.cpow_neg]
    congr 1
    push_cast; ring
  rw [← hpow]
  ring

/-- Identity under the stated parameter and domain assumptions: `HasIntegralOn (posDefCone m) (fun
Y => (etr (-(S * Y)) : ℂ) * ((Y.det : ℂ) ^ (a - ((m : ℂ) + 1) / 2))) (multivariateGamma m a *
(S.det : ℂ) ^ (-a))`. -/
theorem hasIntegralOn_laplace_det_cpow {m : ℕ} {S : Matrix (Fin m) (Fin m) ℝ} (hS : S.PosDef)
    {a : ℂ} (ha : ((m : ℝ) - 1) / 2 < a.re) :
    HasIntegralOn (posDefCone m) (fun Y => (etr (-(S * Y)) : ℂ) *
      ((Y.det : ℂ) ^ (a - ((m : ℂ) + 1) / 2))) (multivariateGamma m a * (S.det : ℂ) ^ (-a)) := by
  have h := hasIntegralOn_laplace_leadingMinorPowProd (fun _ : Fin m => 0)
      (fun _ _ _ => le_rfl) hS ha
  have h1 : ∀ Y, leadingMinorPowProd (fun _ : Fin m => 0) Y = 1 := fun Y =>
      by simp [leadingMinorPowProd]
  simp only [h1, Complex.ofReal_one, mul_one, Nat.cast_zero, add_zero] at h
  exact h

/-- Nonvanishing under the stated hypotheses: `multivariateGamma m a ≠ 0`. -/
lemma multivariateGamma_ne_zero_of_re_gt {m : ℕ} {a : ℂ} (ha : ((m : ℝ) - 1) / 2 < a.re) :
    multivariateGamma m a ≠ 0 := by
  unfold multivariateGamma
  refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.mpr fun j _ => Complex.Gamma_ne_zero_of_re_pos ?_)
  · rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
    exact Complex.exp_ne_zero _
  · have hj : (j : ℝ) ≤ (m : ℝ) - 1 := by
      have := j.2; rw [le_sub_iff_add_le]; exact_mod_cast this
    simp only [Complex.sub_re, Complex.div_re, Complex.natCast_re, Complex.natCast_im]
    norm_num
    linarith

/-- Measurability of the indicated function: `Measurable fun X : SymMatrix m => (((X : Matrix (Fin
m) (Fin m) ℝ).det : ℂ) ^ q)`. -/
theorem measurable_det_cpow {m : ℕ} (q : ℂ) :
    Measurable fun X : SymMatrix m => (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ q) :=
  (Complex.measurable_ofReal.comp continuous_subtype_val.matrix_det.measurable).pow_const _

/-- DLMF 35.3.8 for `m ≥ 1`, by Fubini from the Laplace transform of `|Y|^{a+b-(m+1)/2}`. -/
lemma hasIntegralOn_posDefCone_multivariateBeta {m : ℕ} (hm : 1 ≤ m) {a b : ℂ}
    (ha : ((m : ℝ) - 1) / 2 < a.re) (hb : ((m : ℝ) - 1) / 2 < b.re) :
    HasIntegralOn (posDefCone m)
      (fun X => ((X.det : ℂ) ^ (a - ((m : ℂ) + 1) / 2)) * (((1 + X).det : ℂ) ^ (-(a + b))))
      (multivariateBeta m a b) := by
  set ν := (TauCeti.symmetricLebesgue m).restrict (posDefCone m)
  have hmc : MeasurableSet (posDefCone m) := TauCeti.measurableSet_posDefMatrix m
  set p : ℂ := ((m : ℂ) + 1) / 2
  set c := a + b
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hc : ((m : ℝ) - 1) / 2 < c.re := by simp only [c, Complex.add_re]; linarith
  -- the double integrand, `Y` first
  set f : SymMatrix m → SymMatrix m → ℂ := fun Y X =>
    ((etr (-(Y : Matrix (Fin m) (Fin m) ℝ)) : ℂ) *
      (((Y : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (c - p))) *
    ((etr (-((Y : Matrix (Fin m) (Fin m) ℝ) * (X : Matrix (Fin m) (Fin m) ℝ))) : ℂ) *
      (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (a - p))) with hfdef
  have hetr : ∀ Y X : Matrix (Fin m) (Fin m) ℝ, (etr (-Y) : ℂ) * (etr (-(Y * X)) : ℂ) =
      (etr (-((1 + X) * Y)) : ℂ) := by
    intro Y X
    unfold etr
    rw [← Complex.ofReal_mul, ← Real.exp_add, Matrix.add_mul, Matrix.one_mul, neg_add,
      Matrix.trace_add, Matrix.trace_neg, Matrix.trace_neg, Matrix.trace_neg,
      Matrix.trace_mul_comm X Y]
  have hfm : Measurable (Function.uncurry f) := by
    have hY : Measurable fun Y : SymMatrix m => (etr (-(Y : Matrix (Fin m) (Fin m) ℝ)) : ℂ) := by
      unfold etr
      exact Complex.measurable_ofReal.comp (Real.measurable_exp.comp
        continuous_subtype_val.neg.matrix_trace.measurable)
    have hYX : Measurable fun q : SymMatrix m × SymMatrix m =>
        (etr (-((q.1 : Matrix (Fin m) (Fin m) ℝ) * (q.2 : Matrix (Fin m) (Fin m) ℝ))) : ℂ) := by
      unfold etr
      exact Complex.measurable_ofReal.comp (Real.measurable_exp.comp
        ((continuous_subtype_val.comp continuous_fst).matrix_mul
          (continuous_subtype_val.comp continuous_snd)).neg.matrix_trace.measurable)
    exact ((hY.mul (measurable_det_cpow _)).comp measurable_fst).mul
      (hYX.mul ((measurable_det_cpow _).comp measurable_snd))
  -- inner integrals over `X`
  have hinX : ∀ Y ∈ posDefCone m, HasIntegralOn (posDefCone m)
      (fun X => (etr (-((Y : Matrix (Fin m) (Fin m) ℝ) * X)) : ℂ) * ((X.det : ℂ) ^ (a - p)))
      (multivariateGamma m a * ((Y : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (-a)) :=
    fun Y hY => hasIntegralOn_laplace_det_cpow hY ha
  set a' : ℂ := (a.re : ℂ)
  have ha' : ((m : ℝ) - 1) / 2 < a'.re := by simpa [a'] using ha
  set b' : ℂ := (b.re : ℂ)
  have hb' : ((m : ℝ) - 1) / 2 < b'.re := by simpa [b'] using hb
  have hcpow_re : ∀ (x : ℝ), 0 < x → ∀ q : ℂ, (((‖(x : ℂ) ^ q‖ : ℝ)) : ℂ) =
      (x : ℂ) ^ ((q.re : ℝ) : ℂ) := by
    intro x hx q
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.ofReal_cpow hx.le]
  set r : SymMatrix m → ℝ := fun Y => etr (-(Y : Matrix (Fin m) (Fin m) ℝ)) *
    (Y : Matrix (Fin m) (Fin m) ℝ).det ^ ((c - p).re) with hr
  have hnormX : ∀ Y X : SymMatrix m, Y ∈ posDefCone m → X ∈ posDefCone m →
      ((‖f Y X‖ : ℝ) : ℂ) = (r Y : ℂ) *
        ((etr (-((Y : Matrix (Fin m) (Fin m) ℝ) * (X : Matrix (Fin m) (Fin m) ℝ))) : ℂ) *
          (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (a' - p))) := by
    intro Y X hY hX
    have hY : (Y : Matrix (Fin m) (Fin m) ℝ).PosDef := hY
    have hX : (X : Matrix (Fin m) (Fin m) ℝ).PosDef := hX
    have hre : a' - p = (((a - p).re : ℝ) : ℂ) := by
      simp [a', p]
    rw [hre]
    simp only [hfdef, hr, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_pos _).le, etr, Complex.ofReal_mul]
    rw [hcpow_re _ hY.det_pos, hcpow_re _ hX.det_pos, Complex.ofReal_cpow hY.det_pos.le]
  have hnormInt : ∀ Y ∈ posDefCone m, ∫ X, ‖f Y X‖ ∂ν =
      ((r Y : ℂ) *
        (multivariateGamma m a' * ((Y : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (-a'))).re := by
    intro Y hY
    have h := hasIntegralOn_posDefCone_const_mul (hasIntegralOn_laplace_det_cpow hY ha') (r Y : ℂ)
    have h2 := h.2
    rw [← setIntegral_congr_fun hmc (fun X hX => hnormX Y X hY hX),
      integral_complex_ofReal] at h2
    rw [← h2, Complex.ofReal_re]
  have hfi : Integrable (Function.uncurry f) (ν.prod ν) := by
    rw [integrable_prod_iff hfm.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem hmc] with Y hY
      refine (((hinX Y hY).1).const_mul ((etr (-(Y : Matrix (Fin m) (Fin m) ℝ)) : ℂ) *
        (((Y : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (c - p)))).congr ?_
      exact Filter.Eventually.of_forall fun X => rfl
    · simp only [Function.uncurry_apply_pair]
      have hG := ((multivariateGamma_eq_integral hb').1.const_mul (multivariateGamma m a')).re
      refine hG.congr ?_
      filter_upwards [ae_restrict_mem hmc] with Y hY
      rw [hnormInt Y hY]
      have hY' : (Y : Matrix (Fin m) (Fin m) ℝ).PosDef := hY
      have hd := hY'.det_pos
      have hne : ((Y : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr hd.ne'
      change Complex.re _ = Complex.re _
      congr 1
      simp only [hr]
      rw [Complex.ofReal_mul, Complex.ofReal_cpow hd.le]
      have key : ((Y : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ ((((c - p).re : ℝ)) : ℂ) *
          ((Y : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (-a') =
          ((Y : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (b' - ((m : ℂ) + 1) / 2) := by
        rw [← Complex.cpow_add _ _ hne]
        congr 1
        simp [c, a', b', p, Complex.ext_iff]
        ring
      rw [← key]
      ring
  -- `Y`-integrals
  have hΓc := multivariateGamma_ne_zero_of_re_gt hc
  have hinY : ∀ X ∈ posDefCone m, ∫ Y, f Y X ∂ν = multivariateGamma m c *
      (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (a - p) *
        (((1 + (X : Matrix (Fin m) (Fin m) ℝ)).det : ℂ) ^ (-c))) := by
    intro X hX
    have hX' : (X : Matrix (Fin m) (Fin m) ℝ).PosDef := hX
    have h1X : (1 + (X : Matrix (Fin m) (Fin m) ℝ)).PosDef := Matrix.PosDef.one.add hX'
    have h := (hasIntegralOn_posDefCone_const_mul (hasIntegralOn_laplace_det_cpow h1X hc)
      (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (a - p))).2
    rw [show ∀ u v w : ℂ, u * (v * w) = v * (u * w) from fun u v w => by ring, ← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
    simp only [hfdef]
    rw [← hetr]
    ring
  refine ⟨?_, ?_⟩
  · have := (hfi.integral_prod_right).const_mul (multivariateGamma m c)⁻¹
    refine Integrable.congr this ?_
    filter_upwards [ae_restrict_mem hmc] with X hX
    simp only [Function.uncurry_apply_pair]
    rw [hinY X hX, ← mul_assoc, inv_mul_cancel₀ hΓc, one_mul]
  · have h1 : ∫ X in posDefCone m, ((((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (a - p)) *
        (((1 + (X : Matrix (Fin m) (Fin m) ℝ)).det : ℂ) ^ (-(a + b))))
          ∂TauCeti.symmetricLebesgue m =
        ∫ X, (multivariateGamma m c)⁻¹ * ∫ Y, f Y X ∂ν ∂ν := by
      refine setIntegral_congr_fun hmc fun X hX => ?_
      rw [hinY X hX, ← mul_assoc, inv_mul_cancel₀ hΓc, one_mul]
    rw [h1, integral_const_mul, ← integral_integral_swap hfi]
    have h2 : ∫ Y, ∫ X, f Y X ∂ν ∂ν = ∫ Y, multivariateGamma m a *
        ((etr (-(Y : Matrix (Fin m) (Fin m) ℝ)) : ℂ) *
          (((Y : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (b - p))) ∂ν := by
      refine setIntegral_congr_fun hmc fun Y hY => ?_
      have hY' : (Y : Matrix (Fin m) (Fin m) ℝ).PosDef := hY
      have hne : ((Y : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr hY'.det_pos.ne'
      simp only [hfdef]
      rw [integral_const_mul, (hinX Y hY).2]
      have : c - p + -a = b - p := by simp only [c]; ring
      rw [← this, Complex.cpow_add _ _ hne]
      ring
    rw [h2, integral_const_mul, (multivariateGamma_eq_integral hb).2]
    unfold multivariateBeta
    rw [show a + b = c from rfl]
    field_simp

/-- DLMF 35.3.8 for `m = 0`, where `𝓢` is a point and every factor is `1`. -/
lemma hasIntegralOn_posDefCone_multivariateBeta_zero {a b : ℂ} :
    HasIntegralOn (posDefCone 0)
      (fun X => ((X.det : ℂ) ^ (a - ((0 : ℂ) + 1) / 2)) * (((1 + X).det : ℂ) ^ (-(a + b))))
      (multivariateBeta 0 a b) := by
  have h := multivariateGamma_eq_integral (m := 0) (a := 1) (by norm_num)
  have hv : multivariateBeta 0 a b = multivariateGamma 0 1 := by
    simp [multivariateBeta, multivariateGamma]
  rw [hv]
  refine hasIntegralOn_posDefCone_congr h fun X _ => ?_
  simp [etr, Matrix.det_isEmpty, Matrix.trace]

end LaplaceTransform
end DLMF.MatrixArgument
