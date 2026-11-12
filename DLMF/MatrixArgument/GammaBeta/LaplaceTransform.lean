/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.MatrixArgument.Basic
public import DLMFMathlib.Analysis.Fourier.RadianInversion
import DLMFMathlib.LinearAlgebra.Matrix.Complexification
import Mathlib.Data.Nat.Choose.Cast
public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy
public import TauCeti.Analysis.Matrix.Sqrt
public import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
public import TauCeti.Analysis.SpecialFunctions.MultivariateGamma.Basic
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Cholesky
public import TauCeti.LinearAlgebra.Matrix.Triangular
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Congruence
public import TauCeti.Analysis.SpecialFunctions.MultivariateGamma.Integral

/-!
# The matrix Laplace transform (DLMF §35.2)

The Laplace kernel `expTrace(-ZX)` on the cone `Ω` of positive definite matrices and the
absolute convergence of the Laplace transform 35.2.1 for `ℜZ > X₀`.

## Main results

* `matrixLaplaceTransform_integrableOn_analyticOnNhd`: absolute convergence and analyticity of
  35.2.1, via locally dominated integration and Tau Ceti's finite-dimensional analyticity.
* `matrixLaplaceTransform_inversion`: the inversion formula 35.2.2, with the corrected
  factor `2^{m(m-1)/2}` explained in `DLMF.MatrixArgument.GammaBeta`.
* `matrixLaplaceTransform_matrixConvolution`: the convolution theorem 35.2.3, by Fubini and
  translation invariance of `dX`.

The inversion proof uses Mathlib's Fourier inversion through the radian-frequency API.
TauCeti supplies the Frobenius trace pairing and its volume comparison with `dX`.
-/

@[expose] public noncomputable section

open MeasureTheory Matrix Finset Set
open scoped ENNReal

namespace DLMF.MatrixArgument

/-! ## §35.2 Laplace transform -/

/-! ### Helpers: the Laplace kernel and absolute convergence -/

/-- Identity under the stated parameter and domain assumptions: `(Z * X.map (fun x : ℝ => (x :
ℂ))).trace.re = (Z.map Complex.re * X).trace`. -/
private lemma re_trace_mul_map_ofReal {m : ℕ} (Z : Matrix (Fin m) (Fin m) ℂ)
    (X : Matrix (Fin m) (Fin m) ℝ) :
    (Z * X.map (fun x : ℝ => (x : ℂ))).trace.re = (Z.map Complex.re * X).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- Identity under the stated parameter and domain assumptions: `Complex.exp (-(Z * ((X + Y :
SymMatrix m) : Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ))).trace) = Complex.exp (-(Z
* (X : Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ))).trace) * Complex.exp (-(Z * (Y :
Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ))).trace)`. -/
private lemma exp_neg_trace_mul_add {m : ℕ} (Z : Matrix (Fin m) (Fin m) ℂ) (X Y : SymMatrix m) :
    Complex.exp (-(Z * ((X + Y : SymMatrix m) : Matrix (Fin m) (Fin m) ℝ).map
        (fun x : ℝ => (x : ℂ))).trace) =
      Complex.exp (-(Z * (X : Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ))).trace) *
        Complex.exp (-(Z * (Y : Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ))).trace) := by
  rw [← Complex.exp_add, Submodule.coe_add,
    Matrix.map_add (fun x : ℝ => (x : ℂ)) Complex.ofReal_add, Matrix.mul_add, Matrix.trace_add,
    neg_add]

/-- Identity under the stated parameter and domain assumptions: `‖Complex.exp (-(Z * (X : Matrix
(Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ))).trace)‖ = expTrace (-(Z.map Complex.re * (X : Matrix
(Fin m) (Fin m) ℝ)))`. -/
private lemma norm_exp_neg_trace_mul {m : ℕ} (Z : Matrix (Fin m) (Fin m) ℂ) (X : SymMatrix m) :
    ‖Complex.exp (-(Z * (X : Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ))).trace)‖ =
      expTrace (-(Z.map Complex.re * (X : Matrix (Fin m) (Fin m) ℝ))) := by
  unfold expTrace
  rw [Complex.norm_exp, Complex.neg_re, re_trace_mul_map_ofReal, Matrix.trace_neg]

/-- Continuity of the indicated function: `Continuous fun X : SymMatrix m => Complex.exp (-(Z * (X
: Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ))).trace)`. -/
private lemma continuous_exp_neg_trace_mul {m : ℕ} (Z : Matrix (Fin m) (Fin m) ℂ) :
    Continuous fun X : SymMatrix m =>
      Complex.exp (-(Z * (X : Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ))).trace) := by
  exact Complex.continuous_exp.comp ((continuous_const.matrix_mul
    (continuous_subtype_val.matrix_map Complex.continuous_ofReal)).matrix_trace.neg)

/-- Under the bound of 35.2, `expTrace(-𝐙X) f(X)` is integrable on `Ω` for `ℜ𝐙 > X₀`. -/
private lemma integrableOn_exp_neg_trace_mul_of_lt_expTrace {m : ℕ}
    {f : Matrix (Fin m) (Fin m) ℝ → ℂ}
    (hf : AEStronglyMeasurable (fun X : SymMatrix m => f X)
      ((TauCeti.symmetricLebesgue m).restrict (posDefCone m)))
    {X₀ : Matrix (Fin m) (Fin m) ℝ} (hX₀ : X₀.PosDef)
    (hbound : ∀ X ∈ posDefCone m, ‖f X‖ < expTrace (-(X₀ * (X : Matrix (Fin m) (Fin m) ℝ))))
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
  refine Integrable.mono'
      (g := fun X : SymMatrix m => expTrace (-(R * (X : Matrix (Fin m) (Fin m) ℝ))))
    ?_ (((continuous_exp_neg_trace_mul Z).aestronglyMeasurable).mul hf) ?_
  · refine hRint.congr (Filter.Eventually.of_forall fun X => ?_)
    simp only [sub_self, Real.rpow_zero, one_mul]
    unfold expTrace
    rw [Matrix.trace_neg]
  · filter_upwards [ae_restrict_mem hmc] with X hX
    rw [norm_mul, norm_exp_neg_trace_mul]
    calc expTrace (-(Z.map Complex.re * (X : Matrix (Fin m) (Fin m) ℝ))) * ‖f X‖
        ≤ expTrace (-(Z.map Complex.re * (X : Matrix (Fin m) (Fin m) ℝ))) *
          expTrace (-(X₀ * (X : Matrix (Fin m) (Fin m) ℝ))) :=
          mul_le_mul_of_nonneg_left (hbound X hX).le (Real.exp_pos _).le
      _ = expTrace (-(R * (X : Matrix (Fin m) (Fin m) ℝ))) := by
          unfold expTrace
          rw [← Real.exp_add, Matrix.add_mul, Matrix.trace_neg, Matrix.trace_neg,
            Matrix.trace_neg, Matrix.trace_add]
          ring_nf

open scoped MatrixOrder in
/-- DLMF 35.2 (paragraph after 35.2.1): if `|f(X)| < expTrace(-X₀X)` on `Ω` for some `X₀ ∈ Ω`, the
Laplace transform 35.2.1 converges absolutely for every complex symmetric `𝐙` with
`ℜ𝐙 > X₀`, and `g(𝐙)` is a holomorphic function of the independent entries `z_{j,k}`
(`j ≤ k`) on that region. Measurability of `f` is an added (implicit) hypothesis. -/
@[dlmf 35.2]
theorem matrixLaplaceTransform_integrableOn_analyticOnNhd {m : ℕ} (f : Matrix (Fin m) (Fin m) ℝ → ℂ)
    (hf : AEStronglyMeasurable (fun X : SymMatrix m => f X)
      ((TauCeti.symmetricLebesgue m).restrict (posDefCone m)))
    {X₀ : Matrix (Fin m) (Fin m) ℝ} (hX₀ : X₀.PosDef)
    (hbound : ∀ X ∈ posDefCone m, ‖f X‖ < expTrace (-(X₀ * (X : Matrix (Fin m) (Fin m) ℝ)))) :
    (∀ Z : Matrix (Fin m) (Fin m) ℂ, Zᵀ = Z → (Z.map Complex.re - X₀).PosDef →
      IntegrableOn (fun X : SymMatrix m =>
          Complex.exp (-(Z * (X : Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ))).trace) *
            f X)
        (posDefCone m) (TauCeti.symmetricLebesgue m)) ∧
    AnalyticOnNhd ℂ (fun z => matrixLaplaceTransform f (complexSymmetricOfCoords z))
      {z | ((complexSymmetricOfCoords z).map Complex.re - X₀).PosDef} := by
  constructor
  · intro Z _ hZ; exact integrableOn_exp_neg_trace_mul_of_lt_expTrace hf hX₀ hbound hZ
  · let R := fun z : TauCeti.upperTriangle m → ℂ =>
      (TauCeti.symmetricCoordinates m).symm (fun ij => (z ij).re) - ⟨X₀, hX₀.isHermitian⟩
    have hR z : (R z : Matrix (Fin m) (Fin m) ℝ) =
        (complexSymmetricOfCoords z).map Complex.re - X₀ := by
      ext i j; by_cases hij : i ≤ j
      · simp [R, complexSymmetricOfCoords, hij,
            TauCeti.coe_symmetricCoordinates_symm_apply_of_le m _ hij]
      · simp [R, complexSymmetricOfCoords, hij,
          TauCeti.coe_symmetricCoordinates_symm_apply_of_ge m _ (le_of_not_ge hij)]
    have hC : Continuous R := ((TauCeti.symmetricCoordinates m).symm.continuous.comp
      (continuous_pi fun ij => Complex.continuous_re.comp (continuous_apply ij))).sub
          continuous_const
    have hU : IsOpen {z | ((complexSymmetricOfCoords z).map Complex.re - X₀).PosDef} := by
      have h := (TauCeti.isOpen_posDefMatrix m).preimage hC
      change IsOpen {z | (R z : Matrix (Fin m) (Fin m) ℝ).PosDef} at h
      simpa only [hR] using h
    refine DifferentiableOn.analyticOnNhd_of_finiteDimensional ?_ hU
    change DifferentiableOn ℂ (fun z => ∫ X : SymMatrix m,
      Complex.exp (-(complexSymmetricOfCoords z * (X : Matrix (Fin m) (Fin m) ℝ).map
        (fun x : ℝ => (x : ℂ))).trace) *
            f X ∂((TauCeti.symmetricLebesgue m).restrict (posDefCone m))) _
    apply Complex.differentiableOn_integral_of_locally_dominated hU
    · intro z _; exact (continuous_exp_neg_trace_mul _).aestronglyMeasurable.mul hf
    · refine Filter.Eventually.of_forall fun X => Differentiable.differentiableOn ?_
      dsimp [complexSymmetricOfCoords, Matrix.trace, Matrix.diag, Matrix.mul_apply]
      apply Differentiable.mul_const; apply Differentiable.cexp; apply Differentiable.neg
      apply Differentiable.fun_sum; intro i _; apply Differentiable.fun_sum; intro j _
      split_ifs <;> fun_prop
    · intro z hz
      have hg := hX₀.integrableOn_posDef_det_rpow_mul_exp_neg_trace_mul
        (a := ((m : ℝ) + 1) / 2) (by linarith)
      simp only [sub_self, Real.rpow_zero, one_mul] at hg
      refine ⟨_, hU.mem_nhds hz, _, hg, ?_⟩
      filter_upwards [ae_restrict_mem (TauCeti.measurableSet_posDefMatrix m)] with X hX y hy
      have hY : ((complexSymmetricOfCoords y).map Complex.re).PosDef := by
        have h := hy.add hX₀; convert h using 1; abel
      have htrace : 0 ≤ ((complexSymmetricOfCoords y).map Complex.re *
          (X : Matrix (Fin m) (Fin m) ℝ)).trace := by
        rw [← hX.posSemidef.trace_sqrt_mul_mul_sqrt]
        have hsq := (Matrix.LE.le.posSemidef
            (CFC.sqrt_nonneg (X : Matrix (Fin m) (Fin m) ℝ))).isHermitian
        simpa only [hsq.eq] using (hY.posSemidef.mul_mul_conjTranspose_same
          (CFC.sqrt (X : Matrix (Fin m) (Fin m) ℝ))).trace_nonneg
      rw [norm_mul, norm_exp_neg_trace_mul, expTrace, Matrix.trace_neg]
      apply (mul_le_of_le_one_left (norm_nonneg _)
          (Real.exp_le_one_iff.mpr (neg_nonpos.mpr htrace))).trans
      simpa only [expTrace, Matrix.trace_neg] using (hbound X hX).le

namespace MatrixLaplaceInversion
/-- The Laplace damping factor times `f` on the positive cone, extended by zero. -/
def damped {m : ℕ} (f : Matrix (Fin m) (Fin m) ℝ → ℂ) (U : SymMatrix m) :
    SymMatrix m → ℂ :=
  (posDefCone m).indicator (fun Y => Complex.exp (-(((U : Matrix (Fin m) (Fin m) ℝ) *
    (Y : Matrix (Fin m) (Fin m) ℝ)).trace : ℂ)) * f Y)
/-- The defining equation of the damped cone extension. -/
lemma damped_def {m : ℕ} (f : Matrix (Fin m) (Fin m) ℝ → ℂ) (U : SymMatrix m) :
    damped f U = (posDefCone m).indicator (fun Y =>
      Complex.exp (-(((U : Matrix (Fin m) (Fin m) ℝ) *
        (Y : Matrix (Fin m) (Fin m) ℝ)).trace : ℂ)) * f Y) := rfl

/-- On the positive cone the damped extension equals the weighted original function. -/
lemma damped_of_mem {m : ℕ} (f : Matrix (Fin m) (Fin m) ℝ → ℂ) (U Y : SymMatrix m)
    (hY : Y ∈ posDefCone m) :
    damped f U Y = Complex.exp (-(((U : Matrix (Fin m) (Fin m) ℝ) *
      (Y : Matrix (Fin m) (Fin m) ℝ)).trace : ℂ)) * f Y :=
  Set.indicator_of_mem hY _

/-- Outside the positive cone the damped extension vanishes. -/
lemma damped_of_notMem {m : ℕ} (f : Matrix (Fin m) (Fin m) ℝ → ℂ) (U Y : SymMatrix m)
    (hY : Y ∉ posDefCone m) : damped f U Y = 0 :=
  Set.indicator_of_notMem hY _

/-- The radian Fourier transform of the damped cone extension is the vertical Laplace transform. -/
lemma radianFourierIntegral_damped {m : ℕ} (f : Matrix (Fin m) (Fin m) ℝ → ℂ) (U V : SymMatrix m) :
    Real.radianFourierIntegral (TauCeti.symmetricLebesgue m) (damped f U) V =
      matrixLaplaceTransform f ((U : Matrix (Fin m) (Fin m) ℝ).map Complex.ofReal +
        Complex.I • (V : Matrix (Fin m) (Fin m) ℝ).map Complex.ofReal) := by
  rw [Real.radianFourierIntegral_def]
  unfold damped matrixLaplaceTransform
  simp only [smul_eq_mul]
  have hmc : MeasurableSet (posDefCone m) := TauCeti.measurableSet_posDefMatrix m
  rw [← integral_indicator hmc]
  apply integral_congr_ae
  filter_upwards [] with Y
  by_cases hY : Y ∈ posDefCone m
  · rw [Set.indicator_of_mem hY, Set.indicator_of_mem hY]
    rw [← mul_assoc, ← Complex.exp_add, Matrix.trace_map_ofReal_add_I_smul_mul_map_ofReal]
    congr 2
    rw [selfAdjoint.inner_eq_trace_mul]
    ring
  · simp [hY]

/-- The damped cone extension is continuous at interior continuity points of `f`. -/
lemma continuousAt_damped {m : ℕ} (f : Matrix (Fin m) (Fin m) ℝ → ℂ) (U : SymMatrix m)
    (hfc : ContinuousOn f {X | X.PosDef}) (X : SymMatrix m) (hX : X ∈ posDefCone m) :
    ContinuousAt (damped f U) X := by
  have hco : IsOpen (posDefCone m) := TauCeti.isOpen_posDefMatrix m
  have hfw : ContinuousWithinAt (fun Y : SymMatrix m => f Y) (posDefCone m) X :=
    (hfc _ hX).comp continuous_subtype_val.continuousAt.continuousWithinAt
      (fun Y hY => hY)
  have hf := hfw.continuousAt (hco.mem_nhds hX)
  have hc : ContinuousAt (fun Y : SymMatrix m => Complex.exp (-(((U : Matrix (Fin m) (Fin m) ℝ) *
    (Y : Matrix (Fin m) (Fin m) ℝ)).trace : ℂ)) * f Y) X := by
    exact ((Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_const.matrix_mul
        continuous_subtype_val).matrix_trace).neg)).continuousAt).mul hf
  apply hc.congr_of_eventuallyEq
  filter_upwards [hco.mem_nhds hX] with Y hY
  exact Set.indicator_of_mem hY _
end MatrixLaplaceInversion

/-- DLMF 35.2.2 (**corrected**): the inversion formula. Let `f` satisfy the bound of
35.2 with `X₀ ∈ Ω`, let `U ∈ 𝓢` with `U > X₀`, and suppose `V ↦ g(U + iV)` is integrable over
`𝓢`. Then for every `X ∈ Ω` at which `f` is continuous,
`f(X) = 2^{m(m-1)/2} (2π)^{-m(m+1)/2} ∫_𝓢 expTrace((U + iV)X) g(U + iV) dV`,
which is DLMF's `(2πi)^{-m(m+1)/2} ∫ expTrace(𝐙X) g(𝐙) d𝐙` (with `d𝐙 = i^{m(m+1)/2} dV`) multiplied
by the missing factor `2^{m(m-1)/2}` (see the module docstring). Continuity of `f` on `Ω` is an
added hypothesis (pointwise inversion); DLMF's condition that the `V`-integral tends to `0` as
`U → ∞` is not needed for the formula and is omitted. -/
@[dlmf 35.2.E2 "corrected: missing factor 2^(m(m-1)/2) restored"]
theorem matrixLaplaceTransform_inversion {m : ℕ} (f : Matrix (Fin m) (Fin m) ℝ → ℂ)
    (hf : AEStronglyMeasurable (fun X : SymMatrix m => f X)
      ((TauCeti.symmetricLebesgue m).restrict (posDefCone m)))
    (hfc : ContinuousOn f {X | X.PosDef})
    {X₀ : Matrix (Fin m) (Fin m) ℝ} (hX₀ : X₀.PosDef)
    (hbound : ∀ X ∈ posDefCone m, ‖f X‖ < expTrace (-(X₀ * (X : Matrix (Fin m) (Fin m) ℝ))))
    (U : SymMatrix m) (hU : ((U : Matrix (Fin m) (Fin m) ℝ) - X₀).PosDef)
    (hint : Integrable (fun V : SymMatrix m =>
      matrixLaplaceTransform f ((U : Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ)) +
        Complex.I • (V : Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ))))
      (TauCeti.symmetricLebesgue m))
    (X : Matrix (Fin m) (Fin m) ℝ) (hX : X.PosDef) :
    f X = (2 : ℂ) ^ (m * (m - 1) / 2) / (2 * (Real.pi : ℂ)) ^ (m * (m + 1) / 2) *
      ∫ V : SymMatrix m,
        Complex.exp (((U : Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ)) +
            Complex.I • (V : Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ))) *
              X.map (fun x : ℝ => (x : ℂ))).trace *
          matrixLaplaceTransform f ((U : Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ)) +
            Complex.I • (V : Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ)))
        ∂TauCeti.symmetricLebesgue m := by
  let Xs : SymMatrix m := ⟨X, hX.isHermitian⟩
  let Z : Matrix (Fin m) (Fin m) ℂ := (U : Matrix (Fin m) (Fin m) ℝ).map Complex.ofReal
  have hmc : MeasurableSet (posDefCone m) := TauCeti.measurableSet_posDefMatrix m
  have hmap : Z.map Complex.re = (U : Matrix (Fin m) (Fin m) ℝ) := by
    ext i j
    simp [Z, Matrix.map_apply]
  have hZi : (Z.map Complex.re - X₀).PosDef := by
    rw [hmap]
    exact hU
  have hZT : Zᵀ = Z := by
    ext i j
    simp only [Z, Matrix.transpose_apply, Matrix.map_apply]
    exact congrArg Complex.ofReal (congrFun (congrFun (selfAdjoint.transpose_coe U) i) j)
  have hi := (matrixLaplaceTransform_integrableOn_analyticOnNhd f hf hX₀ hbound).1 Z hZT hZi
  have hzero (Y : SymMatrix m) :
      (Z * (Y : Matrix (Fin m) (Fin m) ℝ).map Complex.ofReal).trace =
        (((U : Matrix (Fin m) (Fin m) ℝ) * (Y : Matrix (Fin m) (Fin m) ℝ)).trace : ℂ) := by
    simpa only [Matrix.map_zero, zero_smul, add_zero, Matrix.zero_mul, Matrix.trace_zero,
      Complex.ofReal_zero, mul_zero, smul_zero, Z] using
      Matrix.trace_map_ofReal_add_I_smul_mul_map_ofReal (U : Matrix (Fin m) (Fin m) ℝ) 0 Y
  have hg : Integrable (MatrixLaplaceInversion.damped f U) (TauCeti.symmetricLebesgue m) := by
    rw [MatrixLaplaceInversion.damped]
    apply (integrable_indicator_iff hmc).mpr
    simpa only [hzero] using hi
  have hFfun : Real.radianFourierIntegral (TauCeti.symmetricLebesgue m)
      (MatrixLaplaceInversion.damped f U) = fun V : SymMatrix m =>
        matrixLaplaceTransform f ((U : Matrix (Fin m) (Fin m) ℝ).map Complex.ofReal +
          Complex.I • (V : Matrix (Fin m) (Fin m) ℝ).map Complex.ofReal) :=
    funext (MatrixLaplaceInversion.radianFourierIntegral_damped f U)
  have hG : Integrable (Real.radianFourierIntegral (TauCeti.symmetricLebesgue m)
      (MatrixLaplaceInversion.damped f U)) (TauCeti.symmetricLebesgue m) := by
    rw [hFfun]
    exact hint
  let s : ℝ := (2 : ℝ) ^ (((m : ℝ) * (m - 1)) / 4)
  have hs : 0 < s := by dsimp [s]; positivity
  have hvol : (volume : Measure (SymMatrix m)) = ENNReal.ofReal s • TauCeti.symmetricLebesgue m :=
    TauCeti.volume_symmetricMatrix_eq_smul_symmetricLebesgue m
  have hc := MatrixLaplaceInversion.continuousAt_damped f U hfc Xs hX
  have heq := Real.radianFourierIntegral_inversion_of_volume_eq_smul
    (TauCeti.symmetricLebesgue m) hs hvol hg hG hc
  rw [hFfun, MatrixLaplaceInversion.damped,
    Set.indicator_of_mem (show Xs ∈ posDefCone m from hX)] at heq
  simp only [smul_eq_mul] at heq
  have hfactor : s ^ 2 / (2 * Real.pi) ^ (Module.finrank ℝ (SymMatrix m)) =
      (2 : ℝ) ^ (m * (m - 1) / 2) / (2 * Real.pi) ^ (m * (m + 1) / 2) := by

    rw [TauCeti.finrank_symmetricMatrix, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    have hn : ((m * (m - 1) / 2 : ℕ) : ℝ) = (m : ℝ) * (m - 1) / 2 := by
      rw [← Nat.choose_two_right, Nat.cast_choose_two]
    rw [show ((m : ℝ) * (m - 1) / 4) * (2 : ℕ) = (m : ℝ) * (m - 1) / 2 by push_cast; ring, ← hn,
      Real.rpow_natCast]
  have hex : Complex.exp (((U : Matrix (Fin m) (Fin m) ℝ) * X).trace : ℂ) *
      Complex.exp (-(((U : Matrix (Fin m) (Fin m) ℝ) * X).trace : ℂ)) = 1 := by
    rw [← Complex.exp_add]; simp only [add_neg_cancel, Complex.exp_zero]
  calc f X = Complex.exp (((U : Matrix (Fin m) (Fin m) ℝ) * X).trace : ℂ) *
        (Complex.exp (-(((U : Matrix (Fin m) (Fin m) ℝ) * X).trace : ℂ)) * f X) := by
          rw [← mul_assoc, hex, one_mul]
    _ = Complex.exp (((U : Matrix (Fin m) (Fin m) ℝ) * X).trace : ℂ) *
        ((s ^ 2 / (2 * Real.pi) ^ (Module.finrank ℝ (SymMatrix m))) •
          ∫ V : SymMatrix m, Complex.exp (Complex.I * (inner ℝ V Xs : ℝ)) *
            matrixLaplaceTransform f ((U : Matrix (Fin m) (Fin m) ℝ).map Complex.ofReal +
              Complex.I • (V : Matrix (Fin m) (Fin m) ℝ).map Complex.ofReal)
            ∂TauCeti.symmetricLebesgue m) := by rw [heq]
    _ = (s ^ 2 / (2 * Real.pi) ^ (Module.finrank ℝ (SymMatrix m))) •
        ∫ V : SymMatrix m,
          Complex.exp (((U : Matrix (Fin m) (Fin m) ℝ) * X).trace : ℂ) *
            (Complex.exp (Complex.I * (inner ℝ V Xs : ℝ)) *
              matrixLaplaceTransform f ((U : Matrix (Fin m) (Fin m) ℝ).map Complex.ofReal +
                Complex.I • (V : Matrix (Fin m) (Fin m) ℝ).map Complex.ofReal))
          ∂TauCeti.symmetricLebesgue m := by
      rw [integral_const_mul]
      simp only [Complex.real_smul]
      ring
    _ = _ := by
      rw [show s ^ 2 / (2 * Real.pi) ^ (Module.finrank ℝ (SymMatrix m)) =
        (2 : ℝ) ^ (m * (m - 1) / 2) / (2 * Real.pi) ^ (m * (m + 1) / 2) from hfactor]
      simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_pow,
        Complex.ofReal_mul, Complex.ofReal_ofNat]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with V
      rw [← mul_assoc, ← Complex.exp_add, Matrix.trace_map_ofReal_add_I_smul_mul_map_ofReal,
        selfAdjoint.inner_eq_trace_mul]
      congr 2
      simp only [Xs]
      rw [Matrix.trace_mul_comm X (V : Matrix (Fin m) (Fin m) ℝ)]

/-- DLMF 35.2.3 (convolution theorem): if `f₁, f₂` satisfy the bound of 35.2 with `X₀ ∈ Ω`,
then for complex `𝐙` (DLMF: symmetric) with `ℜ𝐙 > X₀` the Laplace transform of the convolution
`f₁ * f₂` is the product of the Laplace transforms. -/
@[dlmf 35.2.E3]
theorem matrixLaplaceTransform_matrixConvolution {m : ℕ} (f₁ f₂ : Matrix (Fin m) (Fin m) ℝ → ℂ)
    (hf₁ : Measurable f₁) (hf₂ : Measurable f₂)
    {X₀ : Matrix (Fin m) (Fin m) ℝ} (hX₀ : X₀.PosDef)
    (hb₁ : ∀ X ∈ posDefCone m, ‖f₁ X‖ < expTrace (-(X₀ * (X : Matrix (Fin m) (Fin m) ℝ))))
    (hb₂ : ∀ X ∈ posDefCone m, ‖f₂ X‖ < expTrace (-(X₀ * (X : Matrix (Fin m) (Fin m) ℝ))))
    (Z : Matrix (Fin m) (Fin m) ℂ) (hZX : (Z.map Complex.re - X₀).PosDef) :
    matrixLaplaceTransform (matrixConvolution f₁ f₂) Z =
      matrixLaplaceTransform f₁ Z * matrixLaplaceTransform f₂ Z := by
  set Λ := TauCeti.symmetricLebesgue m
  have hmc : MeasurableSet (posDefCone m) := TauCeti.measurableSet_posDefMatrix m
  set e := fun X : SymMatrix m =>
    Complex.exp (-(Z * (X : Matrix (Fin m) (Fin m) ℝ).map (fun x : ℝ => (x : ℂ))).trace) with hedef
  have hem : Measurable e := (continuous_exp_neg_trace_mul Z).measurable
  set g₁ := (posDefCone m).indicator (fun X : SymMatrix m => e X * f₁ X)
  set g₂ := (posDefCone m).indicator (fun X : SymMatrix m => e X * f₂ X)
  have hg₁m : Measurable g₁ := (hem.mul (hf₁.comp measurable_subtype_coe)).indicator hmc
  have hg₂m : Measurable g₂ := (hem.mul (hf₂.comp measurable_subtype_coe)).indicator hmc
  have hg₁ : Integrable g₁ Λ := (integrable_indicator_iff hmc).mpr
    (integrableOn_exp_neg_trace_mul_of_lt_expTrace
        (hf₁.comp measurable_subtype_coe).aestronglyMeasurable hX₀ hb₁ hZX)
  have hg₂ : Integrable g₂ Λ := (integrable_indicator_iff hmc).mpr
    (integrableOn_exp_neg_trace_mul_of_lt_expTrace
        (hf₂.comp measurable_subtype_coe).aestronglyMeasurable hX₀ hb₂ hZX)
  have hL : ∀ f : Matrix (Fin m) (Fin m) ℝ → ℂ, matrixLaplaceTransform f Z =
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
          simp only [hedef]; rw [← exp_neg_trace_mul_add]; congr 2; abel_nf
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
  calc matrixLaplaceTransform (matrixConvolution f₁ f₂) Z
      = ∫ T, e T * matrixConvolution f₁ f₂ (T : Matrix (Fin m) (Fin m) ℝ) ∂Λ :=
        setIntegral_eq_integral_of_forall_compl_eq_zero hconv0
    _ = ∫ T, ∫ X, K X T ∂Λ ∂Λ := by simp_rw [hA]
    _ = ∫ X, ∫ T, K X T ∂Λ ∂Λ := (integral_integral_swap hK).symm
    _ = ∫ X, g₂ X * ∫ T, g₁ T ∂Λ ∂Λ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
        simp only [hKdef]
        rw [integral_const_mul, integral_sub_right_eq_self g₁ X]
    _ = matrixLaplaceTransform f₁ Z * matrixLaplaceTransform f₂ Z := by
        rw [integral_mul_const, hL, hL, mul_comm]

end DLMF.MatrixArgument
