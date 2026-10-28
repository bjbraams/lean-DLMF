/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.MatrixArgument.Basic
public import TauCeti.Analysis.SpecialFunctions.MultivariateGamma.Basic
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Cholesky
public import TauCeti.LinearAlgebra.Matrix.Triangular
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Congruence
public import TauCeti.Analysis.SpecialFunctions.MultivariateGamma.Integral

/-!
# Laplace transform, multivariate gamma and beta functions (DLMF §§35.2–35.3)

* §35.2: absolute convergence and analyticity of the Laplace transform 35.2.1
  (`laplaceTransform_integrableOn_analyticOnNhd`), the inversion formula 35.2.2
  (`laplaceTransform_inversion`, **corrected** by the factor `2^{m(m-1)/2}`, see below), both
  admitted, and the convolution theorem 35.2.3 (`laplaceTransform_matrixConvolution`, proved by
  Fubini and translation invariance of `dX`).
* §35.3: the integrals 35.3.1–35.3.3 and 35.3.8 for `Γ_m`, `Γ_m(s₁, …, s_m)` and `B_m` for
  complex parameters (proved by the Cholesky substitution of Tau Ceti and Fubini; for real `a`
  the integral 35.3.1 is Tau Ceti's `TauCeti.integral_posDef_multivariateGamma`, recorded as an
  upstream pointer in `DLMF.MatrixArgument.MathlibCoverage`), the bridge
  `multivariateGamma_ofReal` to Tau Ceti's real
  `Γ_m`, the case `m = 1`, and 35.3.6.

**Correction of 35.2.2.** With DLMF's `dX = ∏_{j≤k} dx_{j,k}` (and `d𝐙 = ∏_{j≤k} dz_{j,k}`) the
pairing `tr(VX) = ∑_j v_{jj}x_{jj} + 2∑_{j<k} v_{jk}x_{jk}` doubles the off-diagonal
frequencies, so Fourier inversion on `𝓢` carries the factor `2^{m(m-1)/2}`:
`f(X) = 2^{m(m-1)/2} (2πi)^{-m(m+1)/2} ∫ etr(𝐙X) g(𝐙) d𝐙`. (Check with the Gaussian
`exp(-½ tr X²)`, whose Fourier transform on `𝓢` integrates to `(2π)^m π^{m(m-1)/2}`.)
DLMF prints the formula without it; the two agree for `m = 1`.
-/

@[expose] public noncomputable section

open MeasureTheory Matrix Finset Set
open scoped ENNReal

namespace DLMF.MatrixArgument

/-! ## §35.2 Laplace transform -/

/-! ### Helpers: the Laplace kernel and absolute convergence -/

/-- Identity under the stated parameter and domain assumptions: `(Z * X.map (fun x : ℝ => (x :
ℂ))).trace.re = (Z.map Complex.re * X).trace`. -/
lemma q2m_re_trace_mul_map {m : ℕ} (Z : Matrix (Fin m) (Fin m) ℂ)
    (X : Matrix (Fin m) (Fin m) ℝ) :
    (Z * X.map (fun x : ℝ => (x : ℂ))).trace.re = (Z.map Complex.re * X).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- Identity under the stated parameter and domain assumptions: `Complex.exp (-(Z * ((X + Y :
SymMatrix m) : Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ))).trace) = Complex.exp (-(Z
* (X : Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ))).trace) * Complex.exp (-(Z * (Y :
Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ))).trace)`. -/
lemma q2m_lapKernel_add {m : ℕ} (Z : Matrix (Fin m) (Fin m) ℂ) (X Y : SymMatrix m) :
    Complex.exp (-(Z * ((X + Y : SymMatrix m) : Matrix (Fin m) (Fin m) ℝ).map
        (fun x : ℝ => (x : ℂ))).trace) =
      Complex.exp (-(Z * (X : Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ))).trace) *
        Complex.exp (-(Z * (Y : Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ))).trace) := by
  rw [← Complex.exp_add, Submodule.coe_add,
    Matrix.map_add (fun x : ℝ => (x : ℂ)) Complex.ofReal_add, Matrix.mul_add, Matrix.trace_add,
    neg_add]

/-- Identity under the stated parameter and domain assumptions: `‖Complex.exp (-(Z * (X : Matrix
(Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ))).trace)‖ = etr (-(Z.map Complex.re * (X : Matrix
(Fin m) (Fin m) ℝ)))`. -/
lemma q2m_norm_lapKernel {m : ℕ} (Z : Matrix (Fin m) (Fin m) ℂ) (X : SymMatrix m) :
    ‖Complex.exp (-(Z * (X : Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ))).trace)‖ =
      etr (-(Z.map Complex.re * (X : Matrix (Fin m) (Fin m) ℝ))) := by
  unfold etr
  rw [Complex.norm_exp, Complex.neg_re, q2m_re_trace_mul_map, Matrix.trace_neg]

/-- Continuity of the indicated function: `Continuous fun X : SymMatrix m => Complex.exp (-(Z * (X
: Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ))).trace)`. -/
lemma q2m_continuous_lapKernel {m : ℕ} (Z : Matrix (Fin m) (Fin m) ℂ) :
    Continuous fun X : SymMatrix m =>
      Complex.exp (-(Z * (X : Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ))).trace) := by
  exact Complex.continuous_exp.comp ((continuous_const.matrix_mul
    (continuous_subtype_val.matrix_map Complex.continuous_ofReal)).matrix_trace.neg)

/-- Under the bound of 35.2, `etr(-𝐙X) f(X)` is integrable on `Ω` for `ℜ𝐙 > X₀`. -/
lemma q2m_integrable_lap {m : ℕ} {f : Matrix (Fin m) (Fin m) ℝ → ℂ}
    (hf : AEStronglyMeasurable (fun X : SymMatrix m => f X)
      ((TauCeti.symmetricLebesgue m).restrict (posDefCone m)))
    {X₀ : Matrix (Fin m) (Fin m) ℝ} (hX₀ : X₀.PosDef)
    (hbound : ∀ X ∈ posDefCone m, ‖f X‖ < etr (-(X₀ * (X : Matrix (Fin m) (Fin m) ℝ))))
    {Z : Matrix (Fin m) (Fin m) ℂ} (hZX : (Z.map Complex.re - X₀).PosDef) :
    IntegrableOn (fun X : SymMatrix m =>
        Complex.exp (-(Z * (X : Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ))).trace) * f X)
      (posDefCone m)
      (TauCeti.symmetricLebesgue m) := by
  have hmc : MeasurableSet (posDefCone m) := TauCeti.measurableSet_posDefMatrix m
  set R := Z.map Complex.re + X₀
  have hR : R.PosDef := by
    have : R = (Z.map Complex.re - X₀) + (X₀ + X₀) := by simp only [R]; abel
    rw [this]; exact hZX.add (hX₀.add hX₀)
  have hRint := Matrix.PosDef.integrableOn_posDef_det_rpow_mul_exp_neg_trace_mul hR
    (a := ((m : ℝ) + 1) / 2) (by linarith)
  refine Integrable.mono' (g := fun X : SymMatrix m => etr (-(R * (X : Matrix (Fin m) (Fin m) ℝ))))
    ?_ (((q2m_continuous_lapKernel Z).aestronglyMeasurable).mul hf) ?_
  · refine hRint.congr (Filter.Eventually.of_forall fun X => ?_)
    simp only [sub_self, Real.rpow_zero, one_mul]
    unfold etr
    rw [Matrix.trace_neg]
  · filter_upwards [ae_restrict_mem hmc] with X hX
    rw [norm_mul, q2m_norm_lapKernel]
    calc etr (-(Z.map Complex.re * (X : Matrix (Fin m) (Fin m) ℝ))) * ‖f X‖
        ≤ etr (-(Z.map Complex.re * (X : Matrix (Fin m) (Fin m) ℝ))) *
          etr (-(X₀ * (X : Matrix (Fin m) (Fin m) ℝ))) :=
          mul_le_mul_of_nonneg_left (hbound X hX).le (Real.exp_pos _).le
      _ = etr (-(R * (X : Matrix (Fin m) (Fin m) ℝ))) := by
          unfold etr
          rw [← Real.exp_add, Matrix.add_mul, Matrix.trace_neg, Matrix.trace_neg,
            Matrix.trace_neg, Matrix.trace_add]
          ring_nf

/-- DLMF 35.2 (paragraph after 35.2.1): if `|f(X)| < etr(-X₀X)` on `Ω` for some `X₀ ∈ Ω`, the
Laplace transform 35.2.1 converges absolutely for every complex symmetric `𝐙` with
`ℜ𝐙 > X₀`, and `g(𝐙)` is a holomorphic function of the independent entries `z_{j,k}`
(`j ≤ k`) on that region. Measurability of `f` is an added (implicit) hypothesis. -/
@[dlmf 35.2]
theorem laplaceTransform_integrableOn_analyticOnNhd {m : ℕ} (f : Matrix (Fin m) (Fin m) ℝ → ℂ)
    (hf : AEStronglyMeasurable (fun X : SymMatrix m => f X)
      ((TauCeti.symmetricLebesgue m).restrict (posDefCone m)))
    {X₀ : Matrix (Fin m) (Fin m) ℝ} (hX₀ : X₀.PosDef)
    (hbound : ∀ X ∈ posDefCone m, ‖f X‖ < etr (-(X₀ * (X : Matrix (Fin m) (Fin m) ℝ)))) :
    (∀ Z : Matrix (Fin m) (Fin m) ℂ, Zᵀ = Z → (Z.map Complex.re - X₀).PosDef →
      IntegrableOn (fun X : SymMatrix m =>
          Complex.exp (-(Z * (X : Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ))).trace) *
            f X)
        (posDefCone m) (TauCeti.symmetricLebesgue m)) ∧
    AnalyticOnNhd ℂ (fun z => laplaceTransform f (complexSymmetricOfCoords z))
      {z | ((complexSymmetricOfCoords z).map Complex.re - X₀).PosDef} := by
  sorry

/-- DLMF 35.2.2 (**corrected**): the inversion formula. Let `f` satisfy the bound of
35.2 with `X₀ ∈ Ω`, let `U ∈ 𝓢` with `U > X₀`, and suppose `V ↦ g(U + iV)` is integrable over
`𝓢`. Then for every `X ∈ Ω` at which `f` is continuous,
`f(X) = 2^{m(m-1)/2} (2π)^{-m(m+1)/2} ∫_𝓢 etr((U + iV)X) g(U + iV) dV`,
which is DLMF's `(2πi)^{-m(m+1)/2} ∫ etr(𝐙X) g(𝐙) d𝐙` (with `d𝐙 = i^{m(m+1)/2} dV`) multiplied by
the missing factor `2^{m(m-1)/2}` (see the module docstring). Continuity of `f` on `Ω` is an
added hypothesis (pointwise inversion); DLMF's condition that the `V`-integral tends to `0` as
`U → ∞` is not needed for the formula and is omitted. -/
@[dlmf 35.2.E2 "corrected: missing factor 2^(m(m-1)/2) restored"]
theorem laplaceTransform_inversion {m : ℕ} (f : Matrix (Fin m) (Fin m) ℝ → ℂ)
    (hf : AEStronglyMeasurable (fun X : SymMatrix m => f X)
      ((TauCeti.symmetricLebesgue m).restrict (posDefCone m)))
    (hfc : ContinuousOn f {X | X.PosDef})
    {X₀ : Matrix (Fin m) (Fin m) ℝ} (hX₀ : X₀.PosDef)
    (hbound : ∀ X ∈ posDefCone m, ‖f X‖ < etr (-(X₀ * (X : Matrix (Fin m) (Fin m) ℝ))))
    (U : SymMatrix m) (hU : ((U : Matrix (Fin m) (Fin m) ℝ) - X₀).PosDef)
    (hint : Integrable (fun V : SymMatrix m =>
      laplaceTransform f ((U : Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ)) +
        Complex.I • (V : Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ))))
      (TauCeti.symmetricLebesgue m))
    (X : Matrix (Fin m) (Fin m) ℝ) (hX : X.PosDef) :
    f X = (2 : ℂ) ^ (m * (m - 1) / 2) / (2 * (Real.pi : ℂ)) ^ (m * (m + 1) / 2) *
      ∫ V : SymMatrix m,
        Complex.exp (((U : Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ)) +
            Complex.I • (V : Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ))) *
              X.map (fun x : ℝ => (x : ℂ))).trace *
          laplaceTransform f ((U : Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ)) +
            Complex.I • (V : Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ)))
        ∂TauCeti.symmetricLebesgue m := by
  sorry

/-- DLMF 35.2.3 (convolution theorem): if `f₁, f₂` satisfy the bound of 35.2 with `X₀ ∈ Ω`,
then for complex symmetric `𝐙` with `ℜ𝐙 > X₀` the Laplace transform of the convolution
`f₁ * f₂` is the product of the Laplace transforms. -/
@[dlmf 35.2.E3]
theorem laplaceTransform_matrixConvolution {m : ℕ} (f₁ f₂ : Matrix (Fin m) (Fin m) ℝ → ℂ)
    (hf₁ : Measurable f₁) (hf₂ : Measurable f₂)
    {X₀ : Matrix (Fin m) (Fin m) ℝ} (hX₀ : X₀.PosDef)
    (hb₁ : ∀ X ∈ posDefCone m, ‖f₁ X‖ < etr (-(X₀ * (X : Matrix (Fin m) (Fin m) ℝ))))
    (hb₂ : ∀ X ∈ posDefCone m, ‖f₂ X‖ < etr (-(X₀ * (X : Matrix (Fin m) (Fin m) ℝ))))
    (Z : Matrix (Fin m) (Fin m) ℂ) (hZ : Zᵀ = Z) (hZX : (Z.map Complex.re - X₀).PosDef) :
    laplaceTransform (matrixConvolution f₁ f₂) Z =
      laplaceTransform f₁ Z * laplaceTransform f₂ Z := by
  set Λ := TauCeti.symmetricLebesgue m
  have hmc : MeasurableSet (posDefCone m) := TauCeti.measurableSet_posDefMatrix m
  set e := fun X : SymMatrix m =>
    Complex.exp (-(Z * (X : Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ))).trace) with hedef
  have hem : Measurable e := (q2m_continuous_lapKernel Z).measurable
  set g₁ := (posDefCone m).indicator (fun X : SymMatrix m => e X * f₁ X)
  set g₂ := (posDefCone m).indicator (fun X : SymMatrix m => e X * f₂ X)
  have hg₁m : Measurable g₁ := (hem.mul (hf₁.comp measurable_subtype_coe)).indicator hmc
  have hg₂m : Measurable g₂ := (hem.mul (hf₂.comp measurable_subtype_coe)).indicator hmc
  have hg₁ : Integrable g₁ Λ := (integrable_indicator_iff hmc).mpr
    (q2m_integrable_lap (hf₁.comp measurable_subtype_coe).aestronglyMeasurable hX₀ hb₁ hZX)
  have hg₂ : Integrable g₂ Λ := (integrable_indicator_iff hmc).mpr
    (q2m_integrable_lap (hf₂.comp measurable_subtype_coe).aestronglyMeasurable hX₀ hb₂ hZX)
  have hL : ∀ f : Matrix (Fin m) (Fin m) ℝ → ℂ, laplaceTransform f Z =
      ∫ X, (posDefCone m).indicator (fun X : SymMatrix m => e X * f X) X ∂Λ :=
    fun f => (integral_indicator hmc).symm
  set K : SymMatrix m → SymMatrix m → ℂ := fun X T => g₂ X * g₁ (T - X) with hKdef
  have hK : Integrable (Function.uncurry K) (Λ.prod Λ) := by
    have hKm : Measurable (Function.uncurry K) :=
      (hg₂m.comp measurable_fst).mul (hg₁m.comp (measurable_snd.sub measurable_fst))
    rw [integrable_prod_iff hKm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun X => ?_, ?_⟩
    · exact (hg₁.comp_sub_right X).const_mul (g₂ X)
    · refine (hg₂.norm.mul_const (∫ Y, ‖g₁ Y‖ ∂Λ)).congr
        (Filter.Eventually.of_forall fun X => ?_)
      simp only [Function.uncurry_apply_pair, hKdef, norm_mul]
      rw [integral_const_mul, integral_sub_right_eq_self (fun Y => ‖g₁ Y‖) X]
  -- the convolution as an integral over all of `𝓢`
  have hmem : ∀ T X : SymMatrix m, X ∈ matrixInterval 0 (T : Matrix (Fin m) (Fin m) ℝ) ↔
      X ∈ posDefCone m ∧ T - X ∈ posDefCone m := by
    intro T X
    simp [matrixInterval, posDefCone]
  have hmI : ∀ T : SymMatrix m,
      MeasurableSet (matrixInterval 0 (T : Matrix (Fin m) (Fin m) ℝ)) := by
    intro T
    have : matrixInterval 0 (T : Matrix (Fin m) (Fin m) ℝ) =
        posDefCone m ∩ (fun X => T - X) ⁻¹' posDefCone m := by
      ext X; rw [hmem]; rfl
    rw [this]
    exact hmc.inter (hmc.preimage (measurable_const.sub measurable_id))
  have hA : ∀ T : SymMatrix m, ∫ X, K X T ∂Λ =
      e T * matrixConvolution f₁ f₂ (T : Matrix (Fin m) (Fin m) ℝ) := by
    intro T
    unfold matrixConvolution
    rw [← integral_indicator (hmI T), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only [hKdef, g₁, g₂]
    by_cases hX : X ∈ posDefCone m
    · by_cases hTX : T - X ∈ posDefCone m
      · have hXI : X ∈ matrixInterval 0 (T : Matrix (Fin m) (Fin m) ℝ) := (hmem T X).mpr ⟨hX, hTX⟩
        rw [Set.indicator_of_mem hX, Set.indicator_of_mem hTX, Set.indicator_of_mem hXI]
        have heT : e T = e X * e (T - X) := by
          simp only [hedef]; rw [← q2m_lapKernel_add]; congr 2; abel_nf
        rw [heT, Submodule.coe_sub]
        ring
      · have hXI : X ∉ matrixInterval 0 (T : Matrix (Fin m) (Fin m) ℝ) :=
          fun h => hTX ((hmem T X).mp h).2
        rw [Set.indicator_of_notMem hTX, Set.indicator_of_notMem hXI]
        simp
    · have hXI : X ∉ matrixInterval 0 (T : Matrix (Fin m) (Fin m) ℝ) :=
        fun h => hX ((hmem T X).mp h).1
      rw [Set.indicator_of_notMem hX, Set.indicator_of_notMem hXI]
      simp
  have hconv0 : ∀ T : SymMatrix m, T ∉ posDefCone m →
      e T * matrixConvolution f₁ f₂ (T : Matrix (Fin m) (Fin m) ℝ) = 0 := by
    intro T hT
    have hempty : matrixInterval 0 (T : Matrix (Fin m) (Fin m) ℝ) = ∅ := by
      ext X
      simp only [Set.mem_empty_iff_false, iff_false]
      intro h
      obtain ⟨hX, hTX⟩ := (hmem T X).mp h
      apply hT
      have := (show ((X : Matrix (Fin m) (Fin m) ℝ)).PosDef from hX).add
        (show (((T - X : SymMatrix m)) : Matrix (Fin m) (Fin m) ℝ).PosDef from hTX)
      rw [Submodule.coe_sub, add_sub_cancel] at this
      exact this
    unfold matrixConvolution
    rw [hempty, Measure.restrict_empty, integral_zero_measure, mul_zero]
  calc laplaceTransform (matrixConvolution f₁ f₂) Z
      = ∫ T, e T * matrixConvolution f₁ f₂ (T : Matrix (Fin m) (Fin m) ℝ) ∂Λ :=
        setIntegral_eq_integral_of_forall_compl_eq_zero hconv0
    _ = ∫ T, ∫ X, K X T ∂Λ ∂Λ := by simp_rw [hA]
    _ = ∫ X, ∫ T, K X T ∂Λ ∂Λ := (integral_integral_swap hK).symm
    _ = ∫ X, g₂ X * ∫ T, g₁ T ∂Λ ∂Λ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
        simp only [hKdef]
        rw [integral_const_mul, integral_sub_right_eq_self g₁ X]
    _ = laplaceTransform f₁ Z * laplaceTransform f₂ Z := by
        rw [integral_mul_const, hL, hL, mul_comm]

/-! ## Cholesky coordinates (helpers for 35.3.1–35.3.2) -/

/-- The Cholesky Jacobian `2^m ∏ L_ii^{m-i}`. -/
def q2m_jac {m : ℕ} (x : TauCeti.lowerTriangle m → ℝ) : ℝ :=
  2 ^ m * ∏ i : Fin m, x ⟨(i, i), le_rfl⟩ ^ (m - i.1)

/-- Transfer of an integral over `Ω` to Cholesky coordinates. -/
lemma q2m_hasIntegralOn_of_cholesky {m : ℕ} {F : Matrix (Fin m) (Fin m) ℝ → ℂ}
    (hF : Measurable (fun X : SymMatrix m => F X)) {I : ℂ}
    (hG : IntegrableOn (fun x : TauCeti.lowerTriangle m → ℝ =>
      ((q2m_jac x : ℝ) : ℂ) * F (TauCeti.lowerTriangleMatrix m x *
        (TauCeti.lowerTriangleMatrix m x)ᵀ)) (TauCeti.posDiagLowerRegion m))
    (hI : ∫ x in TauCeti.posDiagLowerRegion m, ((q2m_jac x : ℝ) : ℂ) *
      F (TauCeti.lowerTriangleMatrix m x * (TauCeti.lowerTriangleMatrix m x)ᵀ) = I) :
    HasIntegralOn (posDefCone m) F I := by
  refine ⟨⟨hF.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_enorm]
    have h := TauCeti.setLIntegral_posDef_symmetricLebesgue m
      (f := fun X : SymMatrix m => ‖F X‖ₑ) hF.enorm
    change ∫⁻ X in {A : SymMatrix m | (A : Matrix (Fin m) (Fin m) ℝ).PosDef}, ‖F X‖ₑ
      ∂TauCeti.symmetricLebesgue m < ∞
    rw [h]
    refine lt_of_eq_of_lt ?_ hG.hasFiniteIntegral
    refine setLIntegral_congr_fun (TauCeti.measurableSet_posDiagLowerRegion m) fun x hx => ?_
    have hj : 0 ≤ q2m_jac x := by
      unfold q2m_jac
      exact mul_nonneg (by positivity)
        (Finset.prod_nonneg fun i _ =>
          pow_nonneg ((TauCeti.mem_posDiagLowerRegion m).mp hx i).le _)
    rw [enorm_mul, TauCeti.choleskyJacobianDensity_def, ← enorm_norm (((q2m_jac x : ℝ) : ℂ)),
      Complex.norm_real, enorm_norm, Real.enorm_of_nonneg hj, TauCeti.coe_lowerTriangleGram,
      q2m_jac]
  · rw [← hI]
    change ∫ X in {A : SymMatrix m | (A : Matrix (Fin m) (Fin m) ℝ).PosDef}, F X
      ∂TauCeti.symmetricLebesgue m = _
    rw [TauCeti.integral_posDef_symmetricLebesgue m hF.aestronglyMeasurable]
    refine setIntegral_congr_fun (TauCeti.measurableSet_posDiagLowerRegion m) fun x _ => ?_
    simp [q2m_jac, Complex.real_smul]

/-- Leading minors of a Gram matrix `L Lᵀ` of a lower-triangular `L`. -/
lemma q2m_leadingMinor_gram {m : ℕ} (x : TauCeti.lowerTriangle m → ℝ) (j : Fin m) :
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
def q2m_diagFactor (c : ℂ) (t : ℝ) : ℂ :=
  (Ioi (0 : ℝ)).indicator
    (fun t : ℝ => ((2 * t : ℝ) : ℂ) * ((Real.exp (-t ^ 2) : ℂ) * ((t ^ 2 : ℝ) : ℂ) ^ (c - 1))) t

/-- Integrability of the indicated kernel: `Integrable (q2m_diagFactor c) ∧ ∫ t, q2m_diagFactor c
t = Complex.Gamma c`. -/
lemma q2m_diagFactor_integral {c : ℂ} (hc : 0 < c.re) :
    Integrable (q2m_diagFactor c) ∧ ∫ t, q2m_diagFactor c t = Complex.Gamma c := by
  have hcongr : EqOn (fun t : ℝ => ((2 * t : ℝ) : ℂ) * ((Real.exp (-t ^ 2) : ℂ) *
      ((t ^ 2 : ℝ) : ℂ) ^ (c - 1)))
      (fun x : ℝ => ((|(2:ℝ)| * x ^ ((2:ℝ) - 1)) • (fun y : ℝ =>
        ((Real.exp (-y) : ℝ) : ℂ) * (y : ℂ) ^ (c - 1)) (x ^ (2:ℝ)))) (Ioi 0) := by
    intro x hx
    simp only [Real.rpow_two, abs_two, Complex.real_smul]
    norm_num
  constructor
  · unfold q2m_diagFactor
    rw [integrable_indicator_iff measurableSet_Ioi, integrableOn_congr_fun hcongr measurableSet_Ioi,
]
    exact (integrableOn_Ioi_comp_rpow_iff (fun y : ℝ =>
        ((Real.exp (-y) : ℝ) : ℂ) * (y : ℂ) ^ (c - 1)) two_ne_zero).mpr
      (Complex.GammaIntegral_convergent hc)
  · unfold q2m_diagFactor
    rw [integral_indicator measurableSet_Ioi, setIntegral_congr_fun measurableSet_Ioi hcongr,
      Complex.Gamma_eq_integral hc]
    exact integral_comp_rpow_Ioi (fun y : ℝ =>
        ((Real.exp (-y) : ℝ) : ℂ) * (y : ℂ) ^ (c - 1)) two_ne_zero

/-- The off-diagonal one-dimensional factor. -/
lemma q2m_offFactor_integral :
    Integrable (fun t : ℝ => ((Real.exp (-t ^ 2) : ℝ) : ℂ)) ∧
      ∫ t : ℝ, ((Real.exp (-t ^ 2) : ℝ) : ℂ) = (Real.sqrt Real.pi : ℂ) := by
  have h1 := integrable_exp_neg_mul_sq (b := 1) one_pos
  have h2 := integral_gaussian 1
  simp only [neg_mul, one_mul, div_one] at h1 h2
  exact ⟨h1.ofReal, by rw [integral_complex_ofReal, h2]⟩

/-- Estimate under the stated parameter and domain assumptions: `∑ j : Fin m, (if i ≤ j then s j -
(if h : j.1 + 1 < m then s ⟨j.1 + 1, h⟩ else p) else 0) = s i - p`. -/
lemma q2m_telescope {m : ℕ} (s : Fin m → ℂ) (p : ℂ) (i : Fin m) :
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

/-- Identity under the stated parameter and domain assumptions: `((r : ℝ) : ℂ) ^ e = Complex.exp
((Real.log r : ℂ) * e)`. -/
lemma q2m_cpow_eq_exp {r : ℝ} (hr : 0 < r) (e : ℂ) :
    ((r : ℝ) : ℂ) ^ e = Complex.exp ((Real.log r : ℂ) * e) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
    Complex.ofReal_log hr.le]

/-- The exponent `s_j - s_{j+1}` (with `s_{m+1} = (m+1)/2`) in 35.3.2. -/
def q2m_gexp {m : ℕ} (s : Fin m → ℂ) (j : Fin m) : ℂ :=
  s j - if h : j.1 + 1 < m then s ⟨j.1 + 1, h⟩ else ((m : ℂ) + 1) / 2

/-- The integrand of 35.3.2. -/
def q2m_gIntegrand {m : ℕ} (s : Fin m → ℂ) (X : Matrix (Fin m) (Fin m) ℝ) : ℂ :=
  (etr (-X) : ℂ) * ∏ j : Fin m, ((leadingMinor X (j.1 + 1) : ℝ) : ℂ) ^ (q2m_gexp s j)

/-- The one-dimensional factors of 35.3.2 in Cholesky coordinates. -/
def q2m_gFactor {m : ℕ} (s : Fin m → ℂ) (ij : TauCeti.lowerTriangle m) (t : ℝ) : ℂ :=
  if ij.1.1 = ij.1.2 then q2m_diagFactor (s ij.1.1 - (ij.1.1 : ℂ) / 2) t
  else ((Real.exp (-t ^ 2) : ℝ) : ℂ)

/-- Identity under the stated parameter and domain assumptions: `(TauCeti.posDiagLowerRegion
m).indicator (fun x => ((q2m_jac x : ℝ) : ℂ) * q2m_gIntegrand s (TauCeti.lowerTriangleMatrix m
x * (TauCeti.lowerTriangleMatrix m x)ᵀ)) x = ∏ ij, q2m_gFactor s ij (x ij)`. -/
lemma q2m_indicator_eq_prod {m : ℕ} (s : Fin m → ℂ) (x : TauCeti.lowerTriangle m → ℝ) :
    (TauCeti.posDiagLowerRegion m).indicator (fun x => ((q2m_jac x : ℝ) : ℂ) *
      q2m_gIntegrand s (TauCeti.lowerTriangleMatrix m x * (TauCeti.lowerTriangleMatrix m x)ᵀ)) x
      = ∏ ij, q2m_gFactor s ij (x ij) := by
  by_cases hx : x ∈ TauCeti.posDiagLowerRegion m
  · rw [Set.indicator_of_mem hx]
    have hpos : ∀ i : Fin m, 0 < x ⟨(i, i), le_rfl⟩ := (TauCeti.mem_posDiagLowerRegion m).mp hx
    set d : Fin m → ℝ := fun i => x ⟨(i, i), le_rfl⟩ with hd
    set ℓ : Fin m → ℝ := fun i => Real.log (d i) with hℓ
    have hdexp : ∀ i, d i = Real.exp (ℓ i) := fun i => (Real.exp_log (hpos i)).symm
    -- the factors
    have hfac : ∀ ij : TauCeti.lowerTriangle m, q2m_gFactor s ij (x ij) =
        (if ij.1.1 = ij.1.2 then 2 * Complex.exp ((ℓ ij.1.1 : ℂ) *
          (2 * s ij.1.1 - ij.1.1 - 1)) else 1) * ((Real.exp (-x ij ^ 2) : ℝ) : ℂ) := by
      intro ij
      unfold q2m_gFactor
      split_ifs with h
      · have hij : ij = ⟨(ij.1.1, ij.1.1), le_rfl⟩ := Subtype.ext (Prod.ext rfl h.symm)
        have hxij : x ij = d ij.1.1 := by rw [hd]; exact congrArg x hij
        rw [q2m_diagFactor, Set.indicator_of_mem (show x ij ∈ Set.Ioi 0 by rw [hxij]; exact hpos _),
          q2m_cpow_eq_exp (by rw [hxij]; exact pow_pos (hpos _) 2), hxij, Real.log_pow, hdexp]
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
        (TauCeti.lowerTriangleMatrix m x)ᵀ) (j.1 + 1) : ℝ) : ℂ) ^ (q2m_gexp s j) =
        Complex.exp ((∑ i : Fin m, if i ≤ j then 2 * (ℓ i : ℂ) else 0) * q2m_gexp s j) := by
      intro j
      rw [q2m_leadingMinor_gram, q2m_cpow_eq_exp (Finset.prod_pos fun i _ => by
        split_ifs <;> [exact pow_pos (hpos i) 2; exact one_pos]), Real.log_prod (fun i _ => by
        split_ifs <;> [exact (pow_pos (hpos i) 2).ne'; exact one_ne_zero])]
      push_cast
      congr 2
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp [Real.log_pow, hℓ, hd]
    have hsum : (∑ j : Fin m, (∑ i : Fin m, if i ≤ j then 2 * (ℓ i : ℂ) else 0) *
        q2m_gexp s j) = ∑ i : Fin m, 2 * (ℓ i : ℂ) * (s i - ((m : ℂ) + 1) / 2) := by
      simp_rw [Finset.sum_mul, ite_mul, zero_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← q2m_telescope s (((m : ℂ) + 1) / 2) i, Finset.mul_sum]
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
    unfold q2m_gIntegrand etr
    rw [Matrix.trace_neg, hexp]
    simp_rw [hminor]
    rw [← Complex.exp_sum, hsum, q2m_jac]
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
    simp only [q2m_gFactor, ite_true, q2m_diagFactor]
    exact Set.indicator_of_notMem (show
      x (⟨(i, i), le_rfl⟩ : TauCeti.lowerTriangle m) ∉ Set.Ioi 0 by simpa using hi) _

/-- Identity under the stated parameter and domain assumptions: `∏ i : Fin m, ((Real.sqrt Real.pi
: ℝ) : ℂ) ^ (i : ℕ) = (Real.pi : ℂ) ^ (((m : ℂ) * ((m : ℂ) - 1)) / 4)`. -/
lemma q2m_prod_sqrt_pi (m : ℕ) :
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
(q2m_gIntegrand s) (multivariateGammaVec m s)`. -/
lemma q2m_multivariateGammaVec_eq_integral {m : ℕ} {s : Fin m → ℂ}
    (hs : ∀ j : Fin m, (j : ℝ) / 2 < (s j).re) :
    HasIntegralOn (posDefCone m) (q2m_gIntegrand s) (multivariateGammaVec m s) := by
  have hc : ∀ i : Fin m, 0 < (s i - (i : ℂ) / 2).re := by
    intro i
    have := hs i
    simp only [Complex.sub_re, Complex.div_re, Complex.natCast_re, Complex.natCast_im]
    norm_num
    linarith
  have hind : (TauCeti.posDiagLowerRegion m).indicator (fun x => ((q2m_jac x : ℝ) : ℂ) *
      q2m_gIntegrand s (TauCeti.lowerTriangleMatrix m x * (TauCeti.lowerTriangleMatrix m x)ᵀ))
      = fun x => ∏ ij, q2m_gFactor s ij (x ij) := funext (q2m_indicator_eq_prod s)
  have hfacint : ∀ ij : TauCeti.lowerTriangle m, Integrable (q2m_gFactor s ij) := by
    intro ij
    unfold q2m_gFactor
    split_ifs
    · exact (q2m_diagFactor_integral (hc _)).1
    · exact q2m_offFactor_integral.1
  refine q2m_hasIntegralOn_of_cholesky ?_ ?_ ?_
  · unfold q2m_gIntegrand etr leadingMinor
    fun_prop
  · rw [← integrable_indicator_iff (TauCeti.measurableSet_posDiagLowerRegion m), hind]
    exact Integrable.fintype_prod hfacint
  · rw [← integral_indicator (TauCeti.measurableSet_posDiagLowerRegion m), hind,
      integral_fintype_prod_volume_eq_prod]
    have hval : ∀ ij : TauCeti.lowerTriangle m, ∫ t, q2m_gFactor s ij t =
        if ij.1.1 = ij.1.2 then Complex.Gamma (s ij.1.1 - (ij.1.1 : ℂ) / 2)
        else ((Real.sqrt Real.pi : ℝ) : ℂ) := by
      intro ij
      unfold q2m_gFactor
      split_ifs
      · exact (q2m_diagFactor_integral (hc _)).2
      · exact q2m_offFactor_integral.2
    rw [Finset.prod_congr rfl fun ij _ => hval ij, TauCeti.prod_lowerTriangle_ite
      (fun i => Complex.Gamma (s i - (i : ℂ) / 2)) fun _ => ((Real.sqrt Real.pi : ℝ) : ℂ),
      Finset.prod_mul_distrib, q2m_prod_sqrt_pi, multivariateGammaVec, mul_comm]

/-! ## §35.3 Multivariate gamma and beta functions -/

/-- DLMF 35.3.4: on real arguments `Γ_m` is Tau Ceti's real multivariate gamma function. -/
@[dlmf 35.3.E4]
theorem multivariateGamma_ofReal (m : ℕ) (x : ℝ) :
    ((TauCeti.multivariateGamma m x : ℝ) : ℂ) = multivariateGamma m x := by
  rw [TauCeti.multivariateGamma_def, multivariateGamma, Complex.ofReal_mul,
    Complex.ofReal_cpow Real.pi_pos.le, Complex.ofReal_prod]
  push_cast
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Complex.Gamma_ofReal]
  push_cast
  rfl

/-- DLMF 35.3.4 for `m = 1`: `Γ₁(a) = Γ(a)`. -/
@[dlmf 35.3.E4]
theorem multivariateGamma_one (a : ℂ) : multivariateGamma 1 a = Complex.Gamma a := by
  simp [multivariateGamma]

/-- DLMF 35.3.1: `Γ_m(a) = ∫_Ω etr(-X) |X|^{a-(m+1)/2} dX` for `ℜa > (m-1)/2`, the integral
converging absolutely. For real `a` this is Tau Ceti's `TauCeti.integral_posDef_multivariateGamma`
(see `multivariateGamma_ofReal`). -/
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
  have h := q2m_multivariateGammaVec_eq_integral hs
  change HasIntegralOn _ _ (multivariateGammaVec m fun _ => a)
  convert h using 2 with X
  unfold q2m_gIntegrand
  congr 1
  rcases m with _ | k
  · simp
  · rw [Fin.prod_univ_castSucc]
    have h1 : ∀ j : Fin k, ((leadingMinor X (j.castSucc.1 + 1) : ℝ) : ℂ) ^
        (q2m_gexp (fun _ : Fin (k + 1) => a) j.castSucc) = 1 := by
      intro j
      rw [q2m_gexp, dite_eq_left (by simp), sub_self, Complex.cpow_zero]
    simp_rw [h1, Finset.prod_const_one, one_mul]
    rw [q2m_gexp, dite_eq_right (by simp), leadingMinor, dite_eq_left (by simp)]
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
  exact q2m_multivariateGammaVec_eq_integral hs

/-! ### Laplace integrals over `Ω` and the beta integral 35.3.8

The Cholesky substitution turns 35.3.2 into the scaled form
`∫_Ω etr(-SY) |Y|^{a-(m+1)/2} φ_κ(Y) dY = Γ_m(a + κ) |S|^{-a} φ_κ(S⁻¹)` for the leading-minor
product `φ_κ` (used for 35.4.8), and the case `κ = 0` gives
`∫_Ω etr(-SY) |Y|^{a-(m+1)/2} dY = Γ_m(a) |S|^{-a}`. Fubini then gives 35.3.8. -/

section q2mLaplace

/-- The stated relation follows from the given hypotheses: `HasIntegralOn (posDefCone m) g I`. -/
theorem q2m_hasIntegralOn_congr {m : ℕ} {f g : Matrix (Fin m) (Fin m) ℝ → ℂ} {I : ℂ}
    (h : HasIntegralOn (posDefCone m) f I) (hfg : ∀ X : SymMatrix m, X ∈ posDefCone m →
      f X = g X) : HasIntegralOn (posDefCone m) g I := by
  have hmc : MeasurableSet (posDefCone m) := TauCeti.measurableSet_posDefMatrix m
  refine ⟨h.1.congr_fun (fun X hX => hfg X hX) hmc, ?_⟩
  rw [← h.2]
  exact (setIntegral_congr_fun hmc fun X hX => hfg X hX).symm

/-- Identity under the stated parameter and domain assumptions: `HasIntegralOn (posDefCone m) (fun
X => c * f X) (c * I)`. -/
theorem q2m_hasIntegralOn_const_mul {m : ℕ} {f : Matrix (Fin m) (Fin m) ℝ → ℂ} {I : ℂ}
    (h : HasIntegralOn (posDefCone m) f I) (c : ℂ) :
    HasIntegralOn (posDefCone m) (fun X => c * f X) (c * I) :=
  ⟨h.1.const_mul c, by rw [integral_const_mul, h.2]⟩

/-- Congruence change of variables for `HasIntegralOn` over `Ω`. -/
theorem q2m_hasIntegralOn_of_congruence {m : ℕ} (C : Matrix.GeneralLinearGroup (Fin m) ℝ)
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
def q2m_phi {m : ℕ} (κ : Fin m → ℕ) (Y : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ∏ j : Fin m, leadingMinor Y (j.1 + 1) ^ (κ j - nextPart κ j)

/-- Estimate under the stated parameter and domain assumptions: `0 < leadingMinor X (j.1 + 1)`. -/
lemma q2m_leadingMinor_pos {m : ℕ} {X : Matrix (Fin m) (Fin m) ℝ} (hX : X.PosDef) (j : Fin m) :
    0 < leadingMinor X (j.1 + 1) := by
  have hj : j.1 + 1 ≤ m := j.2
  rw [leadingMinor, dite_eq_left hj]
  exact (hX.submatrix (Fin.castLE_injective hj)).det_pos

/-- Estimate under the stated parameter and domain assumptions: `0 < q2m_phi κ X`. -/
theorem q2m_phi_pos {m : ℕ} (κ : Fin m → ℕ) {X : Matrix (Fin m) (Fin m) ℝ} (hX : X.PosDef) :
    0 < q2m_phi κ X :=
  Finset.prod_pos fun j _ => pow_pos (q2m_leadingMinor_pos hX j) _

/-- 35.3.2 with `s_j = a + k_j`: `∫_Ω etr(-X) |X|^{a-(m+1)/2} φ_κ(X) dX = Γ_m(a + κ)`. -/
lemma q2m_hasIntegralOn_phi_one {m : ℕ} (κ : Fin m → ℕ) (hκ : Antitone κ) {a : ℂ}
    (ha : ((m : ℝ) - 1) / 2 < a.re) :
    HasIntegralOn (posDefCone m) (fun Z => (etr (-Z) : ℂ) * ((Z.det : ℂ) ^ (a - ((m : ℂ) + 1) / 2))
      * (q2m_phi κ Z : ℂ)) (multivariateGammaVec m (fun j => a + κ j)) := by
  have hs : ∀ j : Fin m, (j : ℝ) / 2 < ((fun j => a + (κ j : ℂ)) j).re := by
    intro j
    have : (j : ℝ) + 1 ≤ m := by exact_mod_cast j.2
    simp only [Complex.add_re, Complex.natCast_re]
    have := (κ j).cast_nonneg (α := ℝ)
    linarith
  refine q2m_hasIntegralOn_congr (q2m_multivariateGammaVec_eq_integral hs) fun Z hZ => ?_
  have hZ : (Z : Matrix (Fin m) (Fin m) ℝ).PosDef := hZ
  unfold q2m_gIntegrand q2m_phi
  rw [mul_assoc]
  congr 1
  push_cast
  have hterm : ∀ j : Fin m, ((leadingMinor (Z : Matrix (Fin m) (Fin m) ℝ) (j.1 + 1) : ℝ) : ℂ) ^
      (q2m_gexp (fun j => a + (κ j : ℂ)) j) =
      ((leadingMinor (Z : Matrix (Fin m) (Fin m) ℝ) (j.1 + 1) : ℝ) : ℂ) ^ (κ j - nextPart κ j) *
        (if j.1 + 1 = m then ((Z : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^
          (a - ((m : ℂ) + 1) / 2) else 1) := by
    intro j
    have hpos := q2m_leadingMinor_pos hZ j
    have hne : ((leadingMinor (Z : Matrix (Fin m) (Fin m) ℝ) (j.1 + 1) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hpos.ne'
    unfold q2m_gexp
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
lemma q2m_leadingMinor_lower {m : ℕ} {L : Matrix (Fin m) (Fin m) ℝ} (hL : L.IsLowerTriangular)
    (j : Fin m) : leadingMinor (L * Lᵀ) (j.1 + 1) =
      ∏ i ∈ Finset.univ.filter (· ≤ j), L i i ^ 2 := by
  have h := q2m_leadingMinor_gram (fun ij : TauCeti.lowerTriangle m => L ij.1.1 ij.1.2) j
  rw [TauCeti.lowerTriangleMatrix_entries hL] at h
  rw [h, Finset.prod_ite, Finset.prod_const_one, mul_one]

/-- `φ_κ(L Z Lᵀ) = φ_κ(L Lᵀ) φ_κ(Z)` for lower-triangular `L` and `Z ∈ Ω`. -/
lemma q2m_phi_lower_conj {m : ℕ} (κ : Fin m → ℕ) {L : Matrix (Fin m) (Fin m) ℝ}
    (hL : L.IsLowerTriangular) {Z : Matrix (Fin m) (Fin m) ℝ} (hZ : Z.PosDef) :
    q2m_phi κ (L * Z * Lᵀ) = q2m_phi κ (L * Lᵀ) * q2m_phi κ Z := by
  set A : TauCeti.PosDefMatrix m :=
    ⟨⟨Z, Matrix.isHermitian_iff_isSelfAdjoint.mp hZ.isHermitian⟩, hZ⟩
  set M := (TauCeti.cholesky A).1
  have hM : M.IsLowerTriangular := (TauCeti.cholesky A).2.1
  have hMM : M * Mᵀ = Z := TauCeti.cholesky_mul_transpose A
  have hLM : (L * M).IsLowerTriangular := hL.mul hM
  have hconj : L * Z * Lᵀ = (L * M) * (L * M)ᵀ := by
    rw [← hMM, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  unfold q2m_phi
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← mul_pow, hconj, q2m_leadingMinor_lower hLM, q2m_leadingMinor_lower hL, ← hMM,
    q2m_leadingMinor_lower hM, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply_diag_of_isLowerTriangular hL hM, mul_pow]

/-- Continuity of the indicated function: `Continuous fun Y : Matrix (Fin m) (Fin m) ℝ => q2m_phi
κ Y`. -/
theorem q2m_continuous_phi {m : ℕ} (κ : Fin m → ℕ) :
    Continuous fun Y : Matrix (Fin m) (Fin m) ℝ => q2m_phi κ Y := by
  unfold q2m_phi
  refine continuous_finsetProd _ fun j _ => (Continuous.pow ?_ _)
  have hj : j.1 + 1 ≤ m := j.2
  simp only [leadingMinor, hj, dite_true]
  exact (continuous_id.matrix_submatrix _ _).matrix_det

/-- The Laplace integral of `φ_κ`: for `S ∈ Ω`,
`∫_Ω etr(-SY) |Y|^{a-(m+1)/2} φ_κ(Y) dY = Γ_m(a + κ) |S|^{-a} φ_κ(S⁻¹)`. -/
theorem q2m_hasIntegralOn_phi {m : ℕ} (κ : Fin m → ℕ) (hκ : Antitone κ)
    {S : Matrix (Fin m) (Fin m) ℝ} (hS : S.PosDef) {a : ℂ} (ha : ((m : ℝ) - 1) / 2 < a.re) :
    HasIntegralOn (posDefCone m) (fun Y => (etr (-(S * Y)) : ℂ) *
      ((Y.det : ℂ) ^ (a - ((m : ℂ) + 1) / 2)) * (q2m_phi κ Y : ℂ))
      (multivariateGammaVec m (fun j => a + κ j) * (S.det : ℂ) ^ (-a) *
        (q2m_phi κ S⁻¹ : ℂ)) := by
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
      (q2m_phi κ (Y : Matrix (Fin m) (Fin m) ℝ) : ℂ) := by
    unfold etr
    refine ((Complex.measurable_ofReal.comp ?_).mul
      ((Complex.measurable_ofReal.comp continuous_subtype_val.matrix_det.measurable).pow_const
        _)).mul (Complex.measurable_ofReal.comp
          ((q2m_continuous_phi κ).comp continuous_subtype_val).measurable)
    exact Real.measurable_exp.comp
      (continuous_const.matrix_mul continuous_subtype_val).neg.matrix_trace.measurable
  set c : ℂ := ((S.det⁻¹ : ℝ) : ℂ) ^ (a - ((m : ℂ) + 1) / 2) * (q2m_phi κ S⁻¹ : ℂ)
  have h1 := q2m_hasIntegralOn_const_mul (q2m_hasIntegralOn_phi_one κ hκ ha) c
  have h2 : HasIntegralOn (posDefCone m) (fun Z => (etr (-(S * ((C : Matrix (Fin m) (Fin m) ℝ) *
      Z * (C : Matrix (Fin m) (Fin m) ℝ)ᵀ))) : ℂ) * ((((C : Matrix (Fin m) (Fin m) ℝ) * Z *
        (C : Matrix (Fin m) (Fin m) ℝ)ᵀ).det : ℂ) ^ (a - ((m : ℂ) + 1) / 2)) *
      (q2m_phi κ ((C : Matrix (Fin m) (Fin m) ℝ) * Z * (C : Matrix (Fin m) (Fin m) ℝ)ᵀ) : ℂ))
      (c * multivariateGammaVec m (fun j => a + κ j)) := by
    refine q2m_hasIntegralOn_congr h1 fun Z hZ => ?_
    have hZ : (Z : Matrix (Fin m) (Fin m) ℝ).PosDef := hZ
    rw [hC, q2m_phi_lower_conj κ hL hZ, hLL]
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
  have h3 := q2m_hasIntegralOn_of_congruence (F := fun Y => (etr (-(S * Y)) : ℂ) *
    ((Y.det : ℂ) ^ (a - ((m : ℂ) + 1) / 2)) * (q2m_phi κ Y : ℂ)) C hF h2
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
theorem q2m_hasIntegralOn_gamma_scaled {m : ℕ} {S : Matrix (Fin m) (Fin m) ℝ} (hS : S.PosDef)
    {a : ℂ} (ha : ((m : ℝ) - 1) / 2 < a.re) :
    HasIntegralOn (posDefCone m) (fun Y => (etr (-(S * Y)) : ℂ) *
      ((Y.det : ℂ) ^ (a - ((m : ℂ) + 1) / 2))) (multivariateGamma m a * (S.det : ℂ) ^ (-a)) := by
  have h := q2m_hasIntegralOn_phi (fun _ : Fin m => 0) (fun _ _ _ => le_rfl) hS ha
  have h1 : ∀ Y, q2m_phi (fun _ : Fin m => 0) Y = 1 := fun Y => by simp [q2m_phi]
  simp only [h1, Complex.ofReal_one, mul_one, Nat.cast_zero, add_zero] at h
  exact h

/-- Nonvanishing under the stated hypotheses: `multivariateGamma m a ≠ 0`. -/
lemma q2m_multivariateGamma_ne_zero {m : ℕ} {a : ℂ} (ha : ((m : ℝ) - 1) / 2 < a.re) :
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
theorem q2m_measurable_detcpow {m : ℕ} (q : ℂ) :
    Measurable fun X : SymMatrix m => (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ q) :=
  (Complex.measurable_ofReal.comp continuous_subtype_val.matrix_det.measurable).pow_const _

/-- DLMF 35.3.8 for `m ≥ 1`, by Fubini from the Laplace transform of `|Y|^{a+b-(m+1)/2}`. -/
lemma q2m_beta_posDefCone {m : ℕ} (hm : 1 ≤ m) {a b : ℂ}
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
    exact ((hY.mul (q2m_measurable_detcpow _)).comp measurable_fst).mul
      (hYX.mul ((q2m_measurable_detcpow _).comp measurable_snd))
  -- inner integrals over `X`
  have hinX : ∀ Y ∈ posDefCone m, HasIntegralOn (posDefCone m)
      (fun X => (etr (-((Y : Matrix (Fin m) (Fin m) ℝ) * X)) : ℂ) * ((X.det : ℂ) ^ (a - p)))
      (multivariateGamma m a * ((Y : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (-a)) :=
    fun Y hY => q2m_hasIntegralOn_gamma_scaled hY ha
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
    have h := q2m_hasIntegralOn_const_mul (q2m_hasIntegralOn_gamma_scaled hY ha') (r Y : ℂ)
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
  have hΓc := q2m_multivariateGamma_ne_zero hc
  have hinY : ∀ X ∈ posDefCone m, ∫ Y, f Y X ∂ν = multivariateGamma m c *
      (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (a - p) *
        (((1 + (X : Matrix (Fin m) (Fin m) ℝ)).det : ℂ) ^ (-c))) := by
    intro X hX
    have hX' : (X : Matrix (Fin m) (Fin m) ℝ).PosDef := hX
    have h1X : (1 + (X : Matrix (Fin m) (Fin m) ℝ)).PosDef := Matrix.PosDef.one.add hX'
    have h := (q2m_hasIntegralOn_const_mul (q2m_hasIntegralOn_gamma_scaled h1X hc)
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
lemma q2m_beta_posDefCone_zero {a b : ℂ} :
    HasIntegralOn (posDefCone 0)
      (fun X => ((X.det : ℂ) ^ (a - ((0 : ℂ) + 1) / 2)) * (((1 + X).det : ℂ) ^ (-(a + b))))
      (multivariateBeta 0 a b) := by
  have h := multivariateGamma_eq_integral (m := 0) (a := 1) (by norm_num)
  have hv : multivariateBeta 0 a b = multivariateGamma 0 1 := by
    simp [multivariateBeta, multivariateGamma]
  rw [hv]
  refine q2m_hasIntegralOn_congr h fun X _ => ?_
  simp [etr, Matrix.det_isEmpty, Matrix.trace]

end q2mLaplace

/-! ### The beta integral 35.3.3

Congruence by a Cholesky factor of `T` scales the beta integrand on `0 < X < T` to the one on
`0 < X < I`; Fubini applied to `∫∫ etr(-X)|X|^{a-(m+1)/2} etr(-Y)|Y|^{b-(m+1)/2}` with the
translation `T = X + Y` then gives `Γ_m(a) Γ_m(b) = Γ_m(a + b) B_m(a, b)`. -/

/-- Integrability of the indicated kernel: `Integrable (fun A => f
(Matrix.GeneralLinearGroup.symmetricCongruence C A)) (TauCeti.symmetricLebesgue m) ↔
Integrable f (TauCeti.symmetricLebesgue m)`. -/
lemma q2m_integrable_congruence_iff {m : ℕ} (C : Matrix.GeneralLinearGroup (Fin m) ℝ)
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
lemma q2m_integral_congruence {m : ℕ} (C : Matrix.GeneralLinearGroup (Fin m) ℝ)
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
lemma q2m_posDef_conj_iff {m : ℕ} (C : Matrix.GeneralLinearGroup (Fin m) ℝ)
    (M : Matrix (Fin m) (Fin m) ℝ) :
    ((C : Matrix (Fin m) (Fin m) ℝ) * M * (C : Matrix (Fin m) (Fin m) ℝ)ᵀ).PosDef ↔ M.PosDef := by
  rw [← conjTranspose_eq_transpose_of_trivial, ← star_eq_conjTranspose,
    IsUnit.posDef_star_right_conjugate_iff (Units.isUnit C)]

/-- The beta integrand on `0 < X < T`, extended by zero. -/
lemma q2m_beta_scale {m : ℕ} {T : Matrix (Fin m) (Fin m) ℝ} (hT : T.PosDef) (a b : ℂ) :
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
      rw [hsub, ← hC, q2m_posDef_conj_iff, q2m_posDef_conj_iff]
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
  · rw [← q2m_integrable_congruence_iff C βT, hcomp]
    exact ⟨fun h => by simpa [← mul_assoc, inv_mul_cancel₀ hk] using h.const_mul k⁻¹,
      fun h => h.const_mul k⟩
  · have h := q2m_integral_congruence C βT
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
lemma q2m_posDef_fin_zero (M : Matrix (Fin 0) (Fin 0) ℝ) : M.PosDef :=
  Matrix.PosDef.of_dotProduct_mulVec_pos (by ext i; exact i.elim0)
    (fun x hx => absurd (Subsingleton.elim x 0) hx)

/-- Formula under the stated hypotheses: `X ∈ matrixInterval 0 T ↔ X ∈ posDefCone m ∧ (T - (X :
Matrix (Fin m) (Fin m) ℝ)).PosDef`. -/
lemma q2m_mem_matrixInterval {m : ℕ} (T : Matrix (Fin m) (Fin m) ℝ) (X : SymMatrix m) :
    X ∈ matrixInterval 0 T ↔ X ∈ posDefCone m ∧ (T - (X : Matrix (Fin m) (Fin m) ℝ)).PosDef := by
  simp [matrixInterval, posDefCone]

/-- The stated relation follows from the given hypotheses: `MeasurableSet (matrixInterval 0 (T :
Matrix (Fin m) (Fin m) ℝ))`. -/
lemma q2m_measurableSet_matrixInterval {m : ℕ} (T : SymMatrix m) :
    MeasurableSet (matrixInterval 0 (T : Matrix (Fin m) (Fin m) ℝ)) := by
  have hmc : MeasurableSet (posDefCone m) := TauCeti.measurableSet_posDefMatrix m
  have : matrixInterval 0 (T : Matrix (Fin m) (Fin m) ℝ) =
      posDefCone m ∩ (fun X => T - X) ⁻¹' posDefCone m := by
    ext X; rw [q2m_mem_matrixInterval]; rfl
  rw [this]
  exact hmc.inter (hmc.preimage (measurable_const.sub measurable_id))

/-- Identity under the stated parameter and domain assumptions: `matrixInterval (m := m) 0 T = ∅`. -/
lemma q2m_matrixInterval_eq_empty {m : ℕ} {T : Matrix (Fin m) (Fin m) ℝ} (hT : ¬ T.PosDef) :
    matrixInterval (m := m) 0 T = ∅ := by
  ext X
  simp only [Set.mem_empty_iff_false, iff_false]
  intro h
  obtain ⟨hX, hTX⟩ := (q2m_mem_matrixInterval T X).mp h
  apply hT
  have := (show ((X : Matrix (Fin m) (Fin m) ℝ)).PosDef from hX).add hTX
  rwa [add_sub_cancel] at this

/-- DLMF 35.3.3 for `m ≥ 1`. -/
lemma q2m_beta_interval {m : ℕ} (hm : 1 ≤ m) {a b : ℂ} (ha : ((m : ℝ) - 1) / 2 < a.re)
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
    (etr (-(X : Matrix (Fin m) (Fin m) ℝ)) : ℂ) *
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
    unfold etr
    exact (Complex.measurable_ofReal.comp (Real.measurable_exp.comp
      continuous_subtype_val.neg.matrix_trace.measurable)).mul (q2m_measurable_detcpow _)
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
      K X T = (etr (-(T : Matrix (Fin m) (Fin m) ℝ)) : ℂ) * β T X := by
    intro X T
    simp only [hKdef, hg, hβ]
    by_cases hX : X ∈ posDefCone m
    · by_cases hTX : T - X ∈ posDefCone m
      · have hXI : X ∈ matrixInterval 0 (T : Matrix (Fin m) (Fin m) ℝ) :=
          (q2m_mem_matrixInterval _ X).mpr ⟨hX, hTX⟩
        rw [Set.indicator_of_mem hX, Set.indicator_of_mem hTX, Set.indicator_of_mem hXI,
          Submodule.coe_sub]
        have he : (etr (-(X : Matrix (Fin m) (Fin m) ℝ)) : ℂ) *
            (etr (-((T : Matrix (Fin m) (Fin m) ℝ) - (X : Matrix (Fin m) (Fin m) ℝ))) : ℂ) =
            (etr (-(T : Matrix (Fin m) (Fin m) ℝ)) : ℂ) := by
          unfold etr
          rw [← Complex.ofReal_mul, ← Real.exp_add, Matrix.trace_neg, Matrix.trace_neg,
            Matrix.trace_neg, Matrix.trace_sub]
          ring_nf
        rw [← he]
        ring
      · have hXI : X ∉ matrixInterval 0 (T : Matrix (Fin m) (Fin m) ℝ) := fun h =>
          hTX ((q2m_mem_matrixInterval _ X).mp h).2
        rw [Set.indicator_of_notMem hTX, Set.indicator_of_notMem hXI]
        simp
    · have hXI : X ∉ matrixInterval 0 (T : Matrix (Fin m) (Fin m) ℝ) :=
        fun h => hX ((q2m_mem_matrixInterval _ X).mp h).1
      rw [Set.indicator_of_notMem hX, Set.indicator_of_notMem hXI]
      simp
  -- integrability of the beta integrand
  have hΩ : Λ.restrict (posDefCone m) ≠ 0 := by
    intro h0
    have h := (multivariateGamma_eq_integral ha).2
    rw [h0, integral_zero_measure] at h
    exact q2m_multivariateGamma_ne_zero ha h.symm
  have : (ae (Λ.restrict (posDefCone m))).NeBot := ae_neBot.mpr hΩ
  obtain ⟨T, hTint, hTΩ⟩ := ((ae_restrict_of_ae hK.prod_left_ae).and
    (ae_restrict_mem hmc)).exists
  have hTpos : (T : Matrix (Fin m) (Fin m) ℝ).PosDef := hTΩ
  have hβT : Integrable (β T) Λ := by
    have he : (etr (-(T : Matrix (Fin m) (Fin m) ℝ)) : ℂ) ≠ 0 := by
      unfold etr; exact Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
    have := hTint.const_mul (etr (-(T : Matrix (Fin m) (Fin m) ℝ)) : ℂ)⁻¹
    refine this.congr (Filter.Eventually.of_forall fun X => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [hKβ, ← mul_assoc, inv_mul_cancel₀ he, one_mul]
  have hβ1 : Integrable (β 1) Λ := ((q2m_beta_scale hTpos a b).1).mp hβT
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
        (etr (-(T : Matrix (Fin m) (Fin m) ℝ)) : ℂ) *
          (((T : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (a + b - P)) * J) T := by
      intro T
      simp_rw [hKβ]
      rw [integral_const_mul]
      by_cases hT : T ∈ posDefCone m
      · rw [Set.indicator_of_mem hT, (q2m_beta_scale hT a b).2]
        ring
      · rw [Set.indicator_of_notMem hT]
        have h0 : ∀ X, β T X = 0 := fun X => by
          simp only [hβ]
          rw [q2m_matrixInterval_eq_empty hT, Set.indicator_empty]
        simp [h0]
    simp_rw [this]
    rw [integral_indicator hmc, integral_mul_const, (multivariateGamma_eq_integral hab).2]
    ring
  have hmI1 : MeasurableSet (matrixInterval (m := m) 0 1) :=
    q2m_measurableSet_matrixInterval ⟨1, IsSelfAdjoint.one _⟩
  have hβ1eq : β 1 = (matrixInterval 0 1).indicator (fun X : SymMatrix m =>
      (((X : Matrix (Fin m) (Fin m) ℝ).det : ℂ) ^ (a - P)) *
      (((1 - (X : Matrix (Fin m) (Fin m) ℝ)).det : ℂ) ^ (b - P))) := rfl
  refine ⟨(integrable_indicator_iff hmI1).mp (hβ1eq ▸ hβ1), ?_⟩
  rw [← integral_indicator hmI1, ← hβ1eq]
  change J = _
  have hΓ := q2m_multivariateGamma_ne_zero hab
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
      exact ⟨fun _ => q2m_posDef_fin_zero _, fun _ => ⟨q2m_posDef_fin_zero _,
        q2m_posDef_fin_zero _⟩⟩
    have h := multivariateGamma_eq_integral (m := 0) (a := 1) (by norm_num)
    have hv : multivariateBeta 0 a b = multivariateGamma 0 1 := by
      simp [multivariateBeta, multivariateGamma]
    rw [hv, hset]
    refine q2m_hasIntegralOn_congr h fun X _ => ?_
    simp [etr, Matrix.det_isEmpty, Matrix.trace]
  · exact q2m_beta_interval hm ha hb

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
  · simpa using q2m_beta_posDefCone_zero (a := a) (b := b)
  · exact q2m_beta_posDefCone hm ha hb

end DLMF.MatrixArgument
