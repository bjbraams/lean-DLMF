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
public import ToMathlib.Analysis.SpecialFunctions.Pow

/-!
# Cholesky coordinates for integrals over positive definite matrices

Tau Ceti's Cholesky substitution `X = L Lᵀ` transports integrals over `Ω` to integrals over
lower-triangular matrices with positive diagonal, with Jacobian `2^m ∏ L_ii^{m-i}`. The
integrand of `Γ_m(s₁, …, s_m)` then factors into one-dimensional Gamma and Gaussian integrals.

## Main results

* `hasIntegralOn_of_cholesky`: change of variables to Cholesky coordinates.
* `hasIntegralOn_multivariateGammaVecIntegrand`: the factorized evaluation behind 35.3.1–35.3.2.
-/

@[expose] public noncomputable section

open MeasureTheory Matrix Finset Set
open scoped ENNReal

namespace DLMF.MatrixArgument

/-! ## Cholesky coordinates (helpers for 35.3.1–35.3.2) -/

/-- The Cholesky Jacobian `2^m ∏ L_ii^{m-i}`. -/
def choleskyJacobian {m : ℕ} (x : TauCeti.lowerTriangle m → ℝ) : ℝ :=
  2 ^ m * ∏ i : Fin m, x ⟨(i, i), le_rfl⟩ ^ (m - i.1)

/-- Transfer of an integral over `Ω` to Cholesky coordinates. -/
private lemma hasIntegralOn_of_cholesky {m : ℕ} {F : Matrix (Fin m) (Fin m) ℝ → ℂ}
    (hF : Measurable (fun X : SymMatrix m => F X)) {I : ℂ}
    (hG : IntegrableOn (fun x : TauCeti.lowerTriangle m → ℝ =>
      ((choleskyJacobian x : ℝ) : ℂ) * F (TauCeti.lowerTriangleMatrix m x *
        (TauCeti.lowerTriangleMatrix m x)ᵀ)) (TauCeti.posDiagLowerRegion m))
    (hI : ∫ x in TauCeti.posDiagLowerRegion m, ((choleskyJacobian x : ℝ) : ℂ) *
      F (TauCeti.lowerTriangleMatrix m x * (TauCeti.lowerTriangleMatrix m x)ᵀ) = I) :
    HasIntegralOn (posDefCone m) F I := by
  refine ⟨⟨hF.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_enorm]
    have h := TauCeti.setLIntegral_posDef_symmetricLebesgue m
      (fun X : SymMatrix m => ‖F X‖ₑ)
    change ∫⁻ X in {A : SymMatrix m | (A : Matrix (Fin m) (Fin m) ℝ).PosDef}, ‖F X‖ₑ
      ∂TauCeti.symmetricLebesgue m < ∞
    rw [h]
    refine lt_of_eq_of_lt ?_ hG.hasFiniteIntegral
    refine setLIntegral_congr_fun (TauCeti.measurableSet_posDiagLowerRegion m) fun x hx => ?_
    have hj : 0 ≤ choleskyJacobian x := by
      unfold choleskyJacobian
      exact mul_nonneg (by positivity)
        (Finset.prod_nonneg fun i _ =>
          pow_nonneg ((TauCeti.mem_posDiagLowerRegion m).mp hx i).le _)
    rw [enorm_mul, TauCeti.choleskyJacobianDensity_def,
        ← enorm_norm (((choleskyJacobian x : ℝ) : ℂ)),
      Complex.norm_real, enorm_norm, Real.enorm_of_nonneg hj, TauCeti.coe_lowerTriangleGram,
      choleskyJacobian]
  · rw [← hI]
    change ∫ X in {A : SymMatrix m | (A : Matrix (Fin m) (Fin m) ℝ).PosDef}, F X
      ∂TauCeti.symmetricLebesgue m = _
    rw [TauCeti.integral_posDef_symmetricLebesgue m (fun X : SymMatrix m => F X)]
    refine setIntegral_congr_fun (TauCeti.measurableSet_posDiagLowerRegion m) fun x _ => ?_
    simp [choleskyJacobian, Complex.real_smul]

/-- Leading minors of a Gram matrix `L Lᵀ` of a lower-triangular `L`. -/
lemma leadingMinor_lowerTriangleMatrix_mul_transpose {m : ℕ}
    (x : TauCeti.lowerTriangle m → ℝ) (j : Fin m) :
    leadingMinor (TauCeti.lowerTriangleMatrix m x * (TauCeti.lowerTriangleMatrix m x)ᵀ)
      (j.1 + 1) = ∏ i : Fin m, if i ≤ j then x ⟨(i, i), le_rfl⟩ ^ 2 else 1 := by
  have hj : j.1 + 1 ≤ m := j.2
  have hL := TauCeti.isLowerTriangular_lowerTriangleMatrix x
  rw [leadingMinor, dite_eq_left hj, hL.submatrix_castLE_mul_transpose hj, det_mul, det_transpose]
  have hsub : (TauCeti.lowerTriangleMatrix m x).submatrix (Fin.castLE hj)
      (Fin.castLE hj) |>.IsLowerTriangular := by
    intro a b hab
    exact hL (show Fin.castLE hj a < Fin.castLE hj b from hab)
  rw [det_of_isLowerTriangular _ hsub, ← sq, ← Finset.prod_pow, Finset.prod_ite,
    Finset.prod_const_one, mul_one]
  have himg : (Finset.univ : Finset (Fin (j.1 + 1))).map (Fin.castLEEmb hj) =
      Finset.univ.filter fun i : Fin m => i ≤ j := by
    ext i
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Fin.castLEEmb_apply,
      Finset.mem_filter]
    constructor
    · rintro ⟨a, rfl⟩
      exact Fin.le_def.mpr (by simp; omega)
    · intro h
      exact ⟨⟨i.1, by have := Fin.le_def.mp h; omega⟩, rfl⟩
  rw [← himg, Finset.prod_map]
  refine Finset.prod_congr rfl fun a _ => ?_
  simp [TauCeti.lowerTriangleMatrix_apply_of_le]

/-- The positive-diagonal factor in Cholesky coordinates: the Jacobian `2t` times the Gamma
density in `t²`, extended by zero to `t ≤ 0`. -/
def choleskyDiagFactor (c : ℂ) (t : ℝ) : ℂ :=
  (Ioi (0 : ℝ)).indicator
    (fun t : ℝ => ((2 * t : ℝ) : ℂ) * ((Real.exp (-t ^ 2) : ℂ) * ((t ^ 2 : ℝ) : ℂ) ^ (c - 1))) t

/-- Integrability of the indicated kernel:
`Integrable (choleskyDiagFactor c) ∧ ∫ t, choleskyDiagFactor c t = Complex.Gamma c`. -/
private lemma integrable_and_integral_choleskyDiagFactor {c : ℂ} (hc : 0 < c.re) :
    Integrable (choleskyDiagFactor c) ∧ ∫ t, choleskyDiagFactor c t = Complex.Gamma c := by
  have hcongr : EqOn (fun t : ℝ => ((2 * t : ℝ) : ℂ) * ((Real.exp (-t ^ 2) : ℂ) *
      ((t ^ 2 : ℝ) : ℂ) ^ (c - 1)))
      (fun x : ℝ => ((|(2:ℝ)| * x ^ ((2:ℝ) - 1)) • (fun y : ℝ =>
        ((Real.exp (-y) : ℝ) : ℂ) * (y : ℂ) ^ (c - 1)) (x ^ (2:ℝ)))) (Ioi 0) := by
    intro x hx
    simp only [Real.rpow_two, abs_two, Complex.real_smul]
    norm_num
  constructor
  · unfold choleskyDiagFactor
    rw [integrable_indicator_iff measurableSet_Ioi, integrableOn_congr_fun hcongr measurableSet_Ioi,
]
    exact (integrableOn_Ioi_comp_rpow_iff (fun y : ℝ =>
        ((Real.exp (-y) : ℝ) : ℂ) * (y : ℂ) ^ (c - 1)) two_ne_zero).mpr
      (Complex.GammaIntegral_convergent hc)
  · unfold choleskyDiagFactor
    rw [integral_indicator measurableSet_Ioi, setIntegral_congr_fun measurableSet_Ioi hcongr,
      Complex.Gamma_eq_integral hc]
    exact integral_comp_rpow_Ioi (fun y : ℝ =>
        ((Real.exp (-y) : ℝ) : ℂ) * (y : ℂ) ^ (c - 1)) two_ne_zero

/-- The off-diagonal one-dimensional factor. -/
private lemma integrable_and_integral_exp_neg_sq :
    Integrable (fun t : ℝ => ((Real.exp (-t ^ 2) : ℝ) : ℂ)) ∧
      ∫ t : ℝ, ((Real.exp (-t ^ 2) : ℝ) : ℂ) = (Real.sqrt Real.pi : ℂ) := by
  have h1 := integrable_exp_neg_mul_sq (b := 1) one_pos
  have h2 := integral_gaussian 1
  simp only [neg_mul, one_mul, div_one] at h1 h2
  exact ⟨h1.ofReal, by rw [integral_complex_ofReal, h2]⟩

/-- Estimate under the stated parameter and domain assumptions: `∑ j : Fin m, (if i ≤ j then s j -
(if h : j.1 + 1 < m then s ⟨j.1 + 1, h⟩ else p) else 0) = s i - p`. -/
private lemma sum_ite_sub_succ_eq_sub {m : ℕ} (s : Fin m → ℂ) (p : ℂ) (i : Fin m) :
    ∑ j : Fin m, (if i ≤ j then s j - (if h : j.1 + 1 < m then s ⟨j.1 + 1, h⟩ else p) else 0)
      = s i - p := by
  set S : ℕ → ℂ := fun n => if h : n < m then s ⟨n, h⟩ else p with hS
  have hterm : ∀ j : Fin m, (if i ≤ j then s j - (if h : j.1 + 1 < m then s ⟨j.1 + 1, h⟩
      else p) else 0) = if i.1 ≤ j.1 then S j.1 - S (j.1 + 1) else 0 := by
    intro j
    simp only [hS, dite_eq_left j.2, Fin.le_def]
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun n => if i.1 ≤ n then S n - S (n + 1) else 0)]
  have key : ∀ N, i.1 ≤ N → ∑ n ∈ Finset.range N, (if i.1 ≤ n then S n - S (n + 1) else 0)
      = S i.1 - S N := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      rw [sub_self]
      exact Finset.sum_eq_zero fun n hn => ite_eq_right (by simp at hn; omega)
    | succ N hN ih =>
      rw [Finset.sum_range_succ, ih, ite_eq_left hN]
      ring
  rw [key m i.2.le]
  simp [hS, i.2]

/-- The exponent `s_j - s_{j+1}` (with `s_{m+1} = (m+1)/2`) in 35.3.2. -/
def multivariateGammaVecExponent {m : ℕ} (s : Fin m → ℂ) (j : Fin m) : ℂ :=
  s j - if h : j.1 + 1 < m then s ⟨j.1 + 1, h⟩ else ((m : ℂ) + 1) / 2

/-- The integrand of 35.3.2. -/
def multivariateGammaVecIntegrand {m : ℕ} (s : Fin m → ℂ) (X : Matrix (Fin m) (Fin m) ℝ) : ℂ :=
  (expTrace (-X) : ℂ) * ∏ j : Fin m,
      ((leadingMinor X (j.1 + 1) : ℝ) : ℂ) ^ (multivariateGammaVecExponent s j)

/-- The one-dimensional factors of 35.3.2 in Cholesky coordinates. -/
def multivariateGammaVecCholeskyFactor {m : ℕ} (s : Fin m → ℂ)
    (ij : TauCeti.lowerTriangle m) (t : ℝ) : ℂ :=
  if ij.1.1 = ij.1.2 then choleskyDiagFactor (s ij.1.1 - (ij.1.1 : ℂ) / 2) t
  else ((Real.exp (-t ^ 2) : ℝ) : ℂ)

/-- Identity under the stated parameter and domain assumptions: `(TauCeti.posDiagLowerRegion
m).indicator (fun x => ((choleskyJacobian x : ℝ) : ℂ) * multivariateGammaVecIntegrand s
(TauCeti.lowerTriangleMatrix m x * (TauCeti.lowerTriangleMatrix m x)ᵀ)) x = ∏ ij,
multivariateGammaVecCholeskyFactor s ij (x ij)`. -/
private lemma indicator_choleskyJacobian_mul_integrand_eq_prod {m : ℕ} (s : Fin m → ℂ)
    (x : TauCeti.lowerTriangle m → ℝ) :
    (TauCeti.posDiagLowerRegion m).indicator (fun x => ((choleskyJacobian x : ℝ) : ℂ) *
      multivariateGammaVecIntegrand s
          (TauCeti.lowerTriangleMatrix m x * (TauCeti.lowerTriangleMatrix m x)ᵀ)) x
      = ∏ ij, multivariateGammaVecCholeskyFactor s ij (x ij) := by
  by_cases hx : x ∈ TauCeti.posDiagLowerRegion m
  · rw [Set.indicator_of_mem hx]
    have hpos : ∀ i : Fin m, 0 < x ⟨(i, i), le_rfl⟩ := (TauCeti.mem_posDiagLowerRegion m).mp hx
    set d : Fin m → ℝ := fun i => x ⟨(i, i), le_rfl⟩ with hd
    set ℓ : Fin m → ℝ := fun i => Real.log (d i) with hℓ
    have hdexp : ∀ i, d i = Real.exp (ℓ i) := fun i => (Real.exp_log (hpos i)).symm
    -- the factors
    have hfac : ∀ ij : TauCeti.lowerTriangle m, multivariateGammaVecCholeskyFactor s ij (x ij) =
        (if ij.1.1 = ij.1.2 then 2 * Complex.exp ((ℓ ij.1.1 : ℂ) *
          (2 * s ij.1.1 - ij.1.1 - 1)) else 1) * ((Real.exp (-x ij ^ 2) : ℝ) : ℂ) := by
      intro ij
      unfold multivariateGammaVecCholeskyFactor
      split_ifs with h
      · have hij : ij = ⟨(ij.1.1, ij.1.1), le_rfl⟩ := Subtype.ext (Prod.ext rfl h.symm)
        have hxij : x ij = d ij.1.1 := by rw [hd]; exact congrArg x hij
        rw [choleskyDiagFactor,
            Set.indicator_of_mem (show x ij ∈ Set.Ioi 0 by rw [hxij]; exact hpos _),
          Complex.ofReal_cpow_eq_exp (by rw [hxij]; exact pow_pos (hpos _) 2), hxij,
              Real.log_pow, hdexp]
        push_cast
        rw [Real.log_exp]
        have : Complex.exp (ℓ ij.1.1) * Complex.exp (2 * ℓ ij.1.1 * (s ij.1.1 - ij.1.1 / 2 - 1))
            = Complex.exp (ℓ ij.1.1 * (2 * s ij.1.1 - ij.1.1 - 1)) := by
          rw [← Complex.exp_add]; ring_nf
        rw [← this]
        ring
      · ring
    rw [Finset.prod_congr rfl fun ij _ => hfac ij, Finset.prod_mul_distrib,
      TauCeti.prod_lowerTriangle_ite (fun i => 2 * Complex.exp ((ℓ i : ℂ) *
        (2 * s i - i - 1))) fun _ => 1]
    simp only [one_pow, mul_one]
    -- the left side
    have hminor : ∀ j : Fin m, ((leadingMinor (TauCeti.lowerTriangleMatrix m x *
        (TauCeti.lowerTriangleMatrix m x)ᵀ) (j.1 + 1) : ℝ) : ℂ) ^
            (multivariateGammaVecExponent s j) =
        Complex.exp ((∑ i : Fin m, if i ≤ j then 2 * (ℓ i : ℂ) else 0) *
            multivariateGammaVecExponent s j) := by
      intro j
      rw [leadingMinor_lowerTriangleMatrix_mul_transpose,
          Complex.ofReal_cpow_eq_exp (Finset.prod_pos fun i _ => by
        split_ifs <;> [exact pow_pos (hpos i) 2; exact one_pos]), Real.log_prod (fun i _ => by
        split_ifs <;> [exact (pow_pos (hpos i) 2).ne'; exact one_ne_zero])]
      push_cast
      congr 2
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp [Real.log_pow, hℓ, hd]
    have hsum : (∑ j : Fin m, (∑ i : Fin m, if i ≤ j then 2 * (ℓ i : ℂ) else 0) *
        multivariateGammaVecExponent s j) = ∑ i : Fin m, 2 * (ℓ i : ℂ) *
            (s i - ((m : ℂ) + 1) / 2) := by
      simp_rw [Finset.sum_mul, ite_mul, zero_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sum_ite_sub_succ_eq_sub s (((m : ℂ) + 1) / 2) i, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : i ≤ j
      · rw [ite_eq_left h, ite_eq_left h]; rfl
      · rw [ite_eq_right h, ite_eq_right h, mul_zero]
    have hexp : (Real.exp (-(TauCeti.lowerTriangleMatrix m x *
        (TauCeti.lowerTriangleMatrix m x)ᵀ).trace) : ℂ) =
        ∏ ij : TauCeti.lowerTriangle m, ((Real.exp (-x ij ^ 2) : ℝ) : ℂ) := by
      rw [TauCeti.trace_lowerTriangleMatrix_mul_transpose, ← Finset.sum_neg_distrib,
        Real.exp_sum]
      push_cast; rfl
    unfold multivariateGammaVecIntegrand expTrace
    rw [Matrix.trace_neg, hexp]
    simp_rw [hminor]
    rw [← Complex.exp_sum, hsum, choleskyJacobian]
    push_cast
    have hdc : ∀ i : Fin m, ((x ⟨(i, i), le_rfl⟩ : ℝ) : ℂ) ^ (m - i.1) =
        Complex.exp (((m - i.1 : ℕ) : ℂ) * (ℓ i : ℂ)) := by
      intro i
      rw [Complex.exp_nat_mul, ← Complex.ofReal_exp, ← hdexp i]
    simp_rw [hdc, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Complex.exp_sum]
    rw [mul_comm (Complex.exp _) (Complex.exp _), ← mul_assoc, mul_assoc (2 ^ m),
      ← Complex.exp_add, ← Finset.sum_add_distrib]
    congr 3
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.cast_sub i.2.le]
    ring
  · rw [Set.indicator_of_notMem hx]
    obtain ⟨i, hi⟩ := not_forall.1 ((TauCeti.mem_posDiagLowerRegion m).not.1 hx)
    refine (Finset.prod_eq_zero (Finset.mem_univ (⟨(i, i), le_rfl⟩ : TauCeti.lowerTriangle m))
      ?_).symm
    simp only [multivariateGammaVecCholeskyFactor, ite_true, choleskyDiagFactor]
    exact Set.indicator_of_notMem (show
      x (⟨(i, i), le_rfl⟩ : TauCeti.lowerTriangle m) ∉ Set.Ioi 0 by simpa using hi) _

/-- Identity under the stated parameter and domain assumptions: `∏ i : Fin m, ((Real.sqrt Real.pi
: ℝ) : ℂ) ^ (i : ℕ) = (Real.pi : ℂ) ^ (((m : ℂ) * ((m : ℂ) - 1)) / 4)`. -/
private lemma prod_sqrt_pi_pow (m : ℕ) :
    ∏ i : Fin m, ((Real.sqrt Real.pi : ℝ) : ℂ) ^ (i : ℕ) =
      (Real.pi : ℂ) ^ (((m : ℂ) * ((m : ℂ) - 1)) / 4) := by
  have hreal : ∏ i : Fin m, Real.sqrt Real.pi ^ (i : ℕ) =
      Real.pi ^ (((m : ℝ) * ((m : ℝ) - 1)) / 4) := by
    have h1 := TauCeti.multivariateGamma_eq_prod m m
    rw [TauCeti.multivariateGamma_def, Finset.prod_mul_distrib] at h1
    have hpos : 0 < ∏ i : Fin m, Real.Gamma ((m : ℝ) - (i.1 : ℝ) / 2) :=
      Finset.prod_pos fun i _ => Real.Gamma_pos_of_pos (by
        have : (i.1 : ℝ) + 1 ≤ m := by exact_mod_cast i.2
        linarith)
    have h2 := mul_right_cancel₀ hpos.ne' h1
    rw [h2]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    ring_nf
  have h3 : ((∏ i : Fin m, Real.sqrt Real.pi ^ (i : ℕ) : ℝ) : ℂ) =
      ∏ i : Fin m, ((Real.sqrt Real.pi : ℝ) : ℂ) ^ (i : ℕ) := by push_cast; rfl
  rw [← h3, hreal, Complex.ofReal_cpow Real.pi_pos.le]
  push_cast
  rfl

/-- The stated relation follows from the given hypotheses: `HasIntegralOn (posDefCone m)
(multivariateGammaVecIntegrand s) (multivariateGammaVec m s)`. -/
lemma hasIntegralOn_multivariateGammaVecIntegrand {m : ℕ} {s : Fin m → ℂ}
    (hs : ∀ j : Fin m, (j : ℝ) / 2 < (s j).re) :
    HasIntegralOn (posDefCone m) (multivariateGammaVecIntegrand s) (multivariateGammaVec m s) := by
  have hc : ∀ i : Fin m, 0 < (s i - (i : ℂ) / 2).re := by
    intro i
    have := hs i
    simp only [Complex.sub_re, Complex.div_re, Complex.natCast_re, Complex.natCast_im]
    norm_num
    linarith
  have hind : (TauCeti.posDiagLowerRegion m).indicator (fun x => ((choleskyJacobian x : ℝ) : ℂ) *
      multivariateGammaVecIntegrand s
          (TauCeti.lowerTriangleMatrix m x * (TauCeti.lowerTriangleMatrix m x)ᵀ))
      = fun x => ∏ ij, multivariateGammaVecCholeskyFactor s ij (x ij) :=
          funext (indicator_choleskyJacobian_mul_integrand_eq_prod s)
  have hfacint : ∀ ij : TauCeti.lowerTriangle m,
      Integrable (multivariateGammaVecCholeskyFactor s ij) := by
    intro ij
    unfold multivariateGammaVecCholeskyFactor
    split_ifs
    · exact (integrable_and_integral_choleskyDiagFactor (hc _)).1
    · exact integrable_and_integral_exp_neg_sq.1
  refine hasIntegralOn_of_cholesky ?_ ?_ ?_
  · unfold multivariateGammaVecIntegrand expTrace leadingMinor
    fun_prop
  · rw [← integrable_indicator_iff (TauCeti.measurableSet_posDiagLowerRegion m), hind]
    exact Integrable.fintype_prod hfacint
  · rw [← integral_indicator (TauCeti.measurableSet_posDiagLowerRegion m), hind,
      integral_fintype_prod_volume_eq_prod]
    have hval : ∀ ij : TauCeti.lowerTriangle m, ∫ t, multivariateGammaVecCholeskyFactor s ij t =
        if ij.1.1 = ij.1.2 then Complex.Gamma (s ij.1.1 - (ij.1.1 : ℂ) / 2)
        else ((Real.sqrt Real.pi : ℝ) : ℂ) := by
      intro ij
      unfold multivariateGammaVecCholeskyFactor
      split_ifs
      · exact (integrable_and_integral_choleskyDiagFactor (hc _)).2
      · exact integrable_and_integral_exp_neg_sq.2
    rw [Finset.prod_congr rfl fun ij _ => hval ij, TauCeti.prod_lowerTriangle_ite
      (fun i => Complex.Gamma (s i - (i : ℂ) / 2)) fun _ => ((Real.sqrt Real.pi : ℝ) : ℂ),
      Finset.prod_mul_distrib, prod_sqrt_pi_pow, multivariateGammaVec, mul_comm]

end DLMF.MatrixArgument
