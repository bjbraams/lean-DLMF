/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.MatrixArgument.Generalized
public import DLMF.MatrixArgument.Q2mMatrixIntegrals

/-!
# Confluent hypergeometric functions of matrix argument (DLMF §35.6)

`hyp1F1 a b T` (35.6.1), `kummerPsi a b T` (35.6.2) and the Laguerre form `laguerreL γ ν T`
(35.6.3) are defined in `DLMF.MatrixArgument.Basic`. This file proves the series form 35.6.1
and the case `m = 1` (`hyp1F1_fin_one`), the convergence 35.6.2 of the integral defining `Ψ`
(`integrableOn_kummerPsi`) and the Mellin transform 35.6.8 (`hasIntegralOn_kummerPsi_mellin`,
by Fubini from 35.3.8), and states 35.6.4–35.6.7, 35.6.9 and 35.6.10 (admitted). Where DLMF
evaluates `₁F₁` at a product `SX` with `X ∈ Ω`, the statements use `X^{1/2} S X^{1/2}`.
§35.6(iv) cites references only.
-/

@[expose] public noncomputable section

open MeasureTheory Matrix Finset Filter
open scoped Nat MatrixOrder Topology

namespace DLMF.MatrixArgument

/-- DLMF 35.6.1: `₁F₁(a; b; T) = ∑_{k=0}^∞ (1/k!) ∑_{|κ|=k} [a]_κ / [b]_κ Z_κ(T)`. -/
@[dlmf 35.6.E1]
theorem hyp1F1_eq_tsum {m : ℕ} (a b : ℂ) (T : Matrix (Fin m) (Fin m) ℝ) :
    hyp1F1 a b T = ∑' k : ℕ, (1 / (k ! : ℂ)) * ∑ κ ∈ partitions m k,
      partitionalShiftedFactorial a κ / partitionalShiftedFactorial b κ *
        (zonalPolynomial κ T : ℂ) := by
  simp [hyp1F1, hypergeometricPFQ]

/-- For `m = 1`, `₁F₁(a; b; t) = ∑_k (a)_k / (b)_k t^k / k!`, Kummer's series (DLMF 13.2.2). -/
lemma hyp1F1_fin_one (a b : ℂ) (T : Matrix (Fin 1) (Fin 1) ℝ) :
    hyp1F1 a b T = ∑' k : ℕ, (1 / (k ! : ℂ)) *
      ((ascPochhammer ℂ k).eval a / (ascPochhammer ℂ k).eval b * ((T 0 0 : ℂ) ^ k)) := by
  rw [hyp1F1, hypergeometricPFQ_fin_one]
  simp

/-- DLMF 35.6.2: the integral defining `Ψ(a; b; T)` converges absolutely for `ℜa > (m-1)/2`
and `T ∈ Ω`. -/
@[dlmf 35.6.E2]
theorem integrableOn_kummerPsi {m : ℕ} {a : ℂ} (b : ℂ) (ha : ((m : ℝ) - 1) / 2 < a.re)
    {T : Matrix (Fin m) (Fin m) ℝ} (hT : T.PosDef) :
    IntegrableOn (fun X : SymMatrix m =>
        (etr (-(T * (X : Matrix (Fin m) (Fin m) ℝ))) : ℂ) *
          (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (a - ((m : ℂ) + 1) / 2)) *
          (((1 + (X : Matrix (Fin m) (Fin m) ℝ)).det : ℂ) ^ (b - a - ((m : ℂ) + 1) / 2)))
      (posDefCone m) (TauCeti.symmetricLebesgue m) := by
  have hmeas : Measurable (fun X : SymMatrix m =>
        (etr (-(T * (X : Matrix (Fin m) (Fin m) ℝ))) : ℂ) *
          (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (a - ((m : ℂ) + 1) / 2)) *
          (((1 + (X : Matrix (Fin m) (Fin m) ℝ)).det : ℂ) ^ (b - a - ((m : ℂ) + 1) / 2))) := by
    unfold etr
    refine ((Complex.measurable_ofReal.comp ?_).mul
      ((Complex.measurable_ofReal.comp continuous_subtype_val.matrix_det.measurable).pow_const
        _)).mul ((Complex.measurable_ofReal.comp
          (continuous_const.add continuous_subtype_val).matrix_det.measurable).pow_const _)
    exact Real.measurable_exp.comp
      (continuous_const.matrix_mul continuous_subtype_val).neg.matrix_trace.measurable
  obtain ⟨ε, hε, hTε⟩ := q2m_exists_posDef_sub_smul hT
  set c : ℝ := (b - a - ((m : ℂ) + 1) / 2).re with hc
  have hre : (a - ((m : ℂ) + 1) / 2).re = a.re - ((m : ℝ) + 1) / 2 := by simp
  -- pointwise facts on the cone
  have hfacts : ∀ X : SymMatrix m, (X : Matrix (Fin m) (Fin m) ℝ).PosDef →
      ‖(etr (-(T * (X : Matrix (Fin m) (Fin m) ℝ))) : ℂ) *
          (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (a - ((m : ℂ) + 1) / 2)) *
          (((1 + (X : Matrix (Fin m) (Fin m) ℝ)).det : ℂ) ^ (b - a - ((m : ℂ) + 1) / 2))‖ =
        (X : Matrix (Fin m) (Fin m) ℝ).det ^ (a.re - ((m : ℝ) + 1) / 2) *
          Real.exp (-(T * (X : Matrix (Fin m) (Fin m) ℝ)).trace) *
          (1 + (X : Matrix (Fin m) (Fin m) ℝ)).det ^ c := by
    intro X hX
    have hX1 : (1 + (X : Matrix (Fin m) (Fin m) ℝ)).PosDef := Matrix.PosDef.one.add hX
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_cpow_eq_rpow_re_of_pos hX.det_pos,
      Complex.norm_cpow_eq_rpow_re_of_pos hX1.det_pos, hre, ← hc]
    unfold etr
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Matrix.trace_neg]
    ring
  have hone : ∀ X : SymMatrix m, (X : Matrix (Fin m) (Fin m) ℝ).PosDef →
      1 ≤ (1 + (X : Matrix (Fin m) (Fin m) ℝ)).det := by
    intro X hX
    rw [q2m_det_one_add hX.isHermitian]
    exact Finset.one_le_prod₀ fun i _ => by
      have := (hX.eigenvalues_pos i).le; linarith
  by_cases hc0 : c ≤ 0
  · have hint := Matrix.PosDef.integrableOn_posDef_det_rpow_mul_exp_neg_trace_mul hT ha
    refine hint.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (TauCeti.measurableSet_posDefMatrix m)] with X hX
    have hX : (X : Matrix (Fin m) (Fin m) ℝ).PosDef := hX
    rw [hfacts X hX]
    have h1 : (1 + (X : Matrix (Fin m) (Fin m) ℝ)).det ^ c ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (hone X hX) hc0
    calc _ ≤ (X : Matrix (Fin m) (Fin m) ℝ).det ^ (a.re - ((m : ℝ) + 1) / 2) *
          Real.exp (-(T * (X : Matrix (Fin m) (Fin m) ℝ)).trace) * 1 :=
          mul_le_mul_of_nonneg_left h1
            (mul_nonneg (Real.rpow_nonneg hX.det_pos.le _) (Real.exp_pos _).le)
      _ = _ := mul_one _
  · push Not at hc0
    set δ : ℝ := min 1 (ε / c) with hδ
    have hδpos : 0 < δ := lt_min one_pos (div_pos hε hc0)
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hcδ : c * δ ≤ ε := by
      have := min_le_right 1 (ε / c)
      rw [← hδ] at this
      calc c * δ ≤ c * (ε / c) := mul_le_mul_of_nonneg_left this hc0.le
        _ = ε := by field_simp
    have hint := Matrix.PosDef.integrableOn_posDef_det_rpow_mul_exp_neg_trace_mul hTε ha
    refine (hint.const_mul (δ ^ (-((m : ℝ) * c)))).mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (TauCeti.measurableSet_posDefMatrix m)] with X hX
    have hX : (X : Matrix (Fin m) (Fin m) ℝ).PosDef := hX
    rw [hfacts X hX]
    set A : Matrix (Fin m) (Fin m) ℝ := (X : Matrix (Fin m) (Fin m) ℝ)
    have htrX : 0 ≤ A.trace := by
      rw [hX.isHermitian.trace_eq_sum_eigenvalues]
      exact Finset.sum_nonneg fun i _ => by simpa using (hX.eigenvalues_pos i).le
    have hdet1 : (1 + A).det ≤ (δ⁻¹) ^ m * Real.exp (δ * A.trace) := by
      rw [q2m_det_one_add hX.isHermitian, hX.isHermitian.trace_eq_sum_eigenvalues]
      simp only [RCLike.ofReal_real_eq_id, id, Finset.mul_sum, Real.exp_sum]
      have hc' : (δ⁻¹) ^ m = ∏ _i : Fin m, δ⁻¹ := by simp
      rw [hc', ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod₀ (fun i _ => by have := (hX.eigenvalues_pos i).le; linarith)
        fun i _ => ?_
      have h1 := Real.add_one_le_exp (δ * hX.isHermitian.eigenvalues i)
      have h2 := (hX.eigenvalues_pos i).le
      rw [le_inv_mul_iff₀ hδpos]
      nlinarith
    have hpow : (1 + A).det ^ c ≤ δ ^ (-((m : ℝ) * c)) * Real.exp (ε * A.trace) := by
      calc (1 + A).det ^ c ≤ ((δ⁻¹) ^ m * Real.exp (δ * A.trace)) ^ c :=
            Real.rpow_le_rpow (by linarith [hone X hX]) hdet1 hc0.le
        _ = δ ^ (-((m : ℝ) * c)) * Real.exp (c * δ * A.trace) := by
            rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul,
              inv_pow, Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul
              hδpos.le, Real.rpow_neg hδpos.le]
            ring_nf
        _ ≤ _ := by
            gcongr
    have htr : -((T - ε • (1 : Matrix (Fin m) (Fin m) ℝ)) * A).trace =
        -(T * A).trace + ε * A.trace := by
      rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
        smul_eq_mul]
      ring
    rw [htr, Real.exp_add]
    calc A.det ^ (a.re - ((m : ℝ) + 1) / 2) * Real.exp (-(T * A).trace) * (1 + A).det ^ c
        ≤ A.det ^ (a.re - ((m : ℝ) + 1) / 2) * Real.exp (-(T * A).trace) *
            (δ ^ (-((m : ℝ) * c)) * Real.exp (ε * A.trace)) :=
          mul_le_mul_of_nonneg_left hpow
            (mul_nonneg (Real.rpow_nonneg hX.det_pos.le _) (Real.exp_pos _).le)
      _ = _ := by ring


/-- DLMF 35.6.4: for `ℜa, ℜ(b - a) > (m-1)/2` and `T ∈ 𝓢`,
`₁F₁(a; b; T) = B_m(a, b - a)⁻¹ ∫_{0<X<I} etr(TX) |X|^{a-(m+1)/2} |I - X|^{b-a-(m+1)/2} dX`,
stated as: the integral converges and equals `B_m(a, b - a) ₁F₁(a; b; T)`. -/
@[dlmf 35.6.E4]
theorem hasIntegralOn_hyp1F1 {m : ℕ} {a b : ℂ} (ha : ((m : ℝ) - 1) / 2 < a.re)
    (hba : ((m : ℝ) - 1) / 2 < (b - a).re) {T : Matrix (Fin m) (Fin m) ℝ}
    (hT : T.IsHermitian) :
    HasIntegralOn (m := m) (matrixInterval 0 1)
      (fun X => (etr (T * X) : ℂ) * ((X.det : ℂ) ^ (a - ((m : ℂ) + 1) / 2)) *
        (((1 - X).det : ℂ) ^ (b - a - ((m : ℂ) + 1) / 2)))
      (multivariateBeta m a (b - a) * hyp1F1 a b T) := by
  sorry

/-- DLMF 35.6.5: for `T > S`, `ℜb > (m-1)/2`,
`∫_Ω etr(-TX) |X|^{b-(m+1)/2} ₁F₁(a; b; SX) dX = Γ_m(b) |I - ST⁻¹|^{-a} |T|^{-b}`.
`S ∈ 𝓢` and `T ∈ Ω` (needed for `|T|^{-b}`) are made explicit. -/
@[dlmf 35.6.E5]
theorem hasIntegralOn_hyp1F1_laplace {m : ℕ} (a : ℂ) {b : ℂ} (hb : ((m : ℝ) - 1) / 2 < b.re)
    {S T : Matrix (Fin m) (Fin m) ℝ} (hS : S.IsHermitian) (hT : T.PosDef) (hTS : (T - S).PosDef) :
    HasIntegralOn (posDefCone m)
      (fun X => (etr (-(T * X)) : ℂ) * ((X.det : ℂ) ^ (b - ((m : ℂ) + 1) / 2)) *
        hyp1F1 a b (CFC.sqrt X * S * CFC.sqrt X))
      (multivariateGamma m b * ((1 - S * T⁻¹).det : ℂ) ^ (-a) * (T.det : ℂ) ^ (-b)) := by
  sorry

/-- DLMF 35.6.6: for `ℜb₁, ℜb₂ > (m-1)/2` and `T ∈ Ω`,
`B_m(b₁, b₂) |T|^{b₁+b₂-(m+1)/2} ₁F₁(a₁ + a₂; b₁ + b₂; T) = ∫_{0<X<T} |X|^{b₁-(m+1)/2}
  ₁F₁(a₁; b₁; X) |T - X|^{b₂-(m+1)/2} ₁F₁(a₂; b₂; T - X) dX`. -/
@[dlmf 35.6.E6]
theorem hasIntegralOn_hyp1F1_convolution {m : ℕ} (a₁ a₂ : ℂ) {b₁ b₂ : ℂ}
    (hb₁ : ((m : ℝ) - 1) / 2 < b₁.re) (hb₂ : ((m : ℝ) - 1) / 2 < b₂.re)
    {T : Matrix (Fin m) (Fin m) ℝ} (hT : T.PosDef) :
    HasIntegralOn (matrixInterval 0 T)
      (fun X => ((X.det : ℂ) ^ (b₁ - ((m : ℂ) + 1) / 2)) * hyp1F1 a₁ b₁ X *
        (((T - X).det : ℂ) ^ (b₂ - ((m : ℂ) + 1) / 2)) * hyp1F1 a₂ b₂ (T - X))
      (multivariateBeta m b₁ b₂ * (T.det : ℂ) ^ (b₁ + b₂ - ((m : ℂ) + 1) / 2) *
        hyp1F1 (a₁ + a₂) (b₁ + b₂) T) := by
  sorry

/-- DLMF 35.6.7 (Kummer transformation): `₁F₁(a; b; T) = etr(T) ₁F₁(b - a; b; -T)` for
`T ∈ 𝓢`, when `Γ_m(b) ≠ 0`. -/
@[dlmf 35.6.E7]
theorem hyp1F1_kummer {m : ℕ} (a : ℂ) {b : ℂ} (hb : multivariateGamma m b ≠ 0)
    {T : Matrix (Fin m) (Fin m) ℝ} (hT : T.IsHermitian) :
    hyp1F1 a b T = (etr T : ℂ) * hyp1F1 (b - a) b (-T) := by
  sorry

lemma q2m_cpow_norm_ofReal {x : ℝ} (hx : 0 < x) (q : ℂ) :
    (((‖(x : ℂ) ^ q‖ : ℝ)) : ℂ) = (x : ℂ) ^ ((q.re : ℝ) : ℂ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.ofReal_cpow hx.le]

/-- DLMF 35.6.8: for `ℜa > ℜc + (m-1)/2 > m-1` and `ℜ(c - b) > -1`,
`∫_Ω |T|^{c-(m+1)/2} Ψ(a; b; T) dT
  = Γ_m(c) Γ_m(a - c) Γ_m(c - b + (m+1)/2) / (Γ_m(a) Γ_m(a - b + (m+1)/2))`. -/
@[dlmf 35.6.E8]
theorem hasIntegralOn_kummerPsi_mellin {m : ℕ} {a b c : ℂ}
    (hac : c.re + ((m : ℝ) - 1) / 2 < a.re) (hc : (m : ℝ) - 1 < c.re + ((m : ℝ) - 1) / 2)
    (hcb : -1 < (c - b).re) :
    HasIntegralOn (posDefCone m)
      (fun T => ((T.det : ℂ) ^ (c - ((m : ℂ) + 1) / 2)) * kummerPsi a b T)
      (multivariateGamma m c * multivariateGamma m (a - c) *
          multivariateGamma m (c - b + ((m : ℂ) + 1) / 2) /
        (multivariateGamma m a * multivariateGamma m (a - b + ((m : ℂ) + 1) / 2))) := by
  set ν := (TauCeti.symmetricLebesgue m).restrict (posDefCone m)
  have hmc : MeasurableSet (posDefCone m) := TauCeti.measurableSet_posDefMatrix m
  set p : ℂ := ((m : ℂ) + 1) / 2 with hp
  set α := a - c
  set β := c - b + p
  have hc' : ((m : ℝ) - 1) / 2 < c.re := by linarith
  have hα : ((m : ℝ) - 1) / 2 < α.re := by simp only [α, Complex.sub_re]; linarith
  have hpre : p.re = ((m : ℝ) + 1) / 2 := by simp [p]
  have hβ : ((m : ℝ) - 1) / 2 < β.re := by
    simp only [β, Complex.add_re, hpre]; linarith
  have hαβ : α + β = a - b + p := by simp only [α, β]; ring
  -- the double integrand, `X` first
  set w : SymMatrix m → ℂ := fun X => (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (a - p)) *
    (((1 + (X : Matrix (Fin m) (Fin m) ℝ)).det : ℂ) ^ (b - a - p)) with hw
  set f : SymMatrix m → SymMatrix m → ℂ := fun X T => w X *
    ((etr (-((X : Matrix (Fin m) (Fin m) ℝ) * (T : Matrix (Fin m) (Fin m) ℝ))) : ℂ) *
      (((T : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (c - p))) with hfdef
  have hfm : Measurable (Function.uncurry f) := by
    have hwm : Measurable w :=
      (q2m_measurable_detcpow _).mul ((Complex.measurable_ofReal.comp
        (continuous_const.add continuous_subtype_val).matrix_det.measurable).pow_const _)
    have hXT : Measurable fun q : SymMatrix m × SymMatrix m =>
        (etr (-((q.1 : Matrix (Fin m) (Fin m) ℝ) * (q.2 : Matrix (Fin m) (Fin m) ℝ))) : ℂ) := by
      unfold etr
      exact Complex.measurable_ofReal.comp (Real.measurable_exp.comp
        ((continuous_subtype_val.comp continuous_fst).matrix_mul
          (continuous_subtype_val.comp continuous_snd)).neg.matrix_trace.measurable)
    exact (hwm.comp measurable_fst).mul (hXT.mul ((q2m_measurable_detcpow _).comp measurable_snd))
  have hinT : ∀ X ∈ posDefCone m, HasIntegralOn (posDefCone m)
      (fun T => (etr (-((X : Matrix (Fin m) (Fin m) ℝ) * T)) : ℂ) * ((T.det : ℂ) ^ (c - p)))
      (multivariateGamma m c * ((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (-c)) :=
    fun X hX => q2m_hasIntegralOn_gamma_scaled hX hc'
  set c' : ℂ := (c.re : ℂ)
  have hc'' : ((m : ℝ) - 1) / 2 < c'.re := by simpa [c'] using hc'
  have hnormT : ∀ X T : SymMatrix m, T ∈ posDefCone m →
      ((‖f X T‖ : ℝ) : ℂ) = ((‖w X‖ : ℝ) : ℂ) *
        ((etr (-((X : Matrix (Fin m) (Fin m) ℝ) * (T : Matrix (Fin m) (Fin m) ℝ))) : ℂ) *
          (((T : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (c' - p))) := by
    intro X T hT
    have hT : (T : Matrix (Fin m) (Fin m) ℝ).PosDef := hT
    have hre : c' - p = (((c - p).re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [c', p]
    rw [hre]
    simp only [hfdef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_pos _).le, etr, Complex.ofReal_mul]
    rw [q2m_cpow_norm_ofReal hT.det_pos]
  have hnormInt : ∀ X, X ∈ posDefCone m → ∫ T, ‖f X T‖ ∂ν =
      (((‖w X‖ : ℝ) : ℂ) *
        (multivariateGamma m c' * ((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (-c'))).re := by
    intro X hX
    have h := (q2m_hasIntegralOn_const_mul (q2m_hasIntegralOn_gamma_scaled hX hc'')
      ((‖w X‖ : ℝ) : ℂ)).2
    rw [← setIntegral_congr_fun hmc (fun T hT => hnormT X T hT),
      integral_complex_ofReal] at h
    rw [← h, Complex.ofReal_re]
  set α' : ℂ := (α.re : ℂ)
  set β' : ℂ := (β.re : ℂ)
  have hα' : ((m : ℝ) - 1) / 2 < α'.re := by simpa [α'] using hα
  have hβ' : ((m : ℝ) - 1) / 2 < β'.re := by simpa [β'] using hβ
  have hfi : Integrable (Function.uncurry f) (ν.prod ν) := by
    rw [integrable_prod_iff hfm.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem hmc] with X hX
      refine (((hinT X hX).1).const_mul (w X)).congr ?_
      exact Filter.Eventually.of_forall fun T => rfl
    · simp only [Function.uncurry_apply_pair]
      have hB := ((multivariateBeta_eq_integral_posDefCone hα' hβ').1.const_mul
        (multivariateGamma m c')).re
      refine hB.congr ?_
      filter_upwards [ae_restrict_mem hmc] with X hX
      rw [hnormInt X hX]
      have hX' : (X : Matrix (Fin m) (Fin m) ℝ).PosDef := hX
      have hd := hX'.det_pos
      have he := (Matrix.PosDef.one.add hX').det_pos
      have hne : ((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr hd.ne'
      change Complex.re _ = Complex.re _
      congr 1
      have hwn : ((‖w X‖ : ℝ) : ℂ) =
          ((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ ((((a - p).re : ℝ)) : ℂ) *
          ((1 + (X : Matrix (Fin m) (Fin m) ℝ)).det : ℂ) ^ ((((b - a - p).re : ℝ)) : ℂ) := by
        simp only [hw, norm_mul, Complex.ofReal_mul]
        rw [q2m_cpow_norm_ofReal hd, q2m_cpow_norm_ofReal he]
      rw [hwn]
      have k1 : ((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ ((((a - p).re : ℝ)) : ℂ) *
          ((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (-c') =
          ((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (α' - ((m : ℂ) + 1) / 2) := by
        rw [← Complex.cpow_add _ _ hne]
        congr 1
        apply Complex.ext
        · simp [α', α, c', p]; ring
        · simp [α', α, c', p]
      have k2 : (((b - a - p).re : ℝ) : ℂ) = -(α' + β') := by
        apply Complex.ext
        · simp [α', β', α, β, p]; ring
        · simp [α', β', α, β, p]
      rw [k2, ← k1]
      ring
  -- the `T`-integrals and the `X`-integrand
  have hinX : ∀ T : SymMatrix m, ((((T : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (c - p)) *
      kummerPsi a b (T : Matrix (Fin m) (Fin m) ℝ)) =
      (multivariateGamma m a)⁻¹ * ∫ X, f X T ∂ν := by
    intro T
    unfold kummerPsi
    rw [← integral_const_mul, ← integral_const_mul, one_div, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only [hfdef, hw, etr]
    rw [Matrix.trace_neg, Matrix.trace_neg, Matrix.trace_mul_comm]
    ring
  refine ⟨?_, ?_⟩
  · have := (hfi.integral_prod_right).const_mul (multivariateGamma m a)⁻¹
    refine Integrable.congr this (Filter.Eventually.of_forall fun T => ?_)
    exact (hinX T).symm
  · rw [show (∫ T in posDefCone m, (((T : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (c - p)) *
        kummerPsi a b (T : Matrix (Fin m) (Fin m) ℝ) ∂TauCeti.symmetricLebesgue m) =
        ∫ T, (multivariateGamma m a)⁻¹ * ∫ X, f X T ∂ν ∂ν from
          integral_congr_ae (Filter.Eventually.of_forall hinX)]
    rw [integral_const_mul, (integral_integral_swap hfi).symm]
    have h2 : ∫ X, ∫ T, f X T ∂ν ∂ν = ∫ X, multivariateGamma m c *
        ((((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (α - ((m : ℂ) + 1) / 2)) *
          (((1 + (X : Matrix (Fin m) (Fin m) ℝ)).det : ℂ) ^ (-(α + β)))) ∂ν := by
      refine setIntegral_congr_fun hmc fun X hX => ?_
      have hX' : (X : Matrix (Fin m) (Fin m) ℝ).PosDef := hX
      have hne : ((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr hX'.det_pos.ne'
      simp only [hfdef]
      rw [integral_const_mul, (hinT X hX).2, hw]
      simp only
      have e1 : a - p + -c = α - ((m : ℂ) + 1) / 2 := by simp only [α, p]; ring
      have e2 : b - a - p = -(α + β) := by simp only [α, β]; ring
      rw [e2, ← e1, Complex.cpow_add _ _ hne]
      ring
    rw [h2, integral_const_mul, (multivariateBeta_eq_integral_posDefCone hα hβ).2]
    unfold multivariateBeta
    rw [hαβ]
    simp only [α, β]
    ring

/-- DLMF 35.6.9: `lim_{a→∞} ₁F₁(a; ν + (m+1)/2; -a⁻¹T) = A_ν(T) / A_ν(0)` (real `a → +∞`),
for `T ∈ 𝓢` and `Γ_m(ν + (m+1)/2) ≠ 0`. -/
@[dlmf 35.6.E9]
theorem tendsto_hyp1F1_besselA {m : ℕ} {ν : ℂ}
    (hν : multivariateGamma m (ν + ((m : ℂ) + 1) / 2) ≠ 0)
    {T : Matrix (Fin m) (Fin m) ℝ} (hT : T.IsHermitian) :
    Tendsto (fun a : ℝ => hyp1F1 a (ν + ((m : ℂ) + 1) / 2) (-(a⁻¹ • T))) atTop
      (𝓝 (besselA ν T / besselA ν (0 : Matrix (Fin m) (Fin m) ℝ))) := by
  sorry

/-- DLMF 35.6.10: `lim_{a→∞} Γ_m(a) Ψ(a + ν; ν + (m+1)/2; a⁻¹T) = B_ν(T)` (real `a → +∞`),
for `T ∈ Ω`. -/
@[dlmf 35.6.E10]
theorem tendsto_kummerPsi_besselB {m : ℕ} (ν : ℂ) {T : Matrix (Fin m) (Fin m) ℝ}
    (hT : T.PosDef) :
    Tendsto (fun a : ℝ => multivariateGamma m a *
        kummerPsi (a + ν) (ν + ((m : ℂ) + 1) / 2) (a⁻¹ • T)) atTop (𝓝 (besselB ν T)) := by
  sorry

end DLMF.MatrixArgument
