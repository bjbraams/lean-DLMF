/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Distributions.Basic
import DLMFMathlib.Analysis.Distribution.Barrelled
import DLMFMathlib.Analysis.LocallyConvex.CompactConvergence
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import DLMFMathlib.Analysis.Distribution.IteratedLineDeriv
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import DLMFMathlib.Analysis.Distribution.Stieltjes
import DLMFMathlib.Analysis.Distribution.JumpDerivatives
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import DLMFMathlib.Analysis.Fourier.Sign
import DLMFMathlib.Analysis.Integral.HilbertRegularization
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Distributions (DLMF §1.16)

Theorems of DLMF §1.16 that are not already in Mathlib (the upstream pointers are in
`DLMF.AlgebraicAnalytic.Distributions.MathlibCoverage`). Sequential distribution convergence
uses TauCeti's Fréchet fixed-support spaces and Mathlib's native test-function topology,
Banach–Steinhaus theorem and Ascoli theorem, through the generic support modules.
Test-function derivatives use TauCeti's
`TestFunction.lineDerivOp_one_apply_eq_deriv` and `coe_iterate_lineDerivOp_one`.

## Main results

* `distribIterDeriv_apply` (1.16.9) and `distribIterDeriv_delta_apply` (1.16.12).
* `smoothMul_apply` (1.16.6), `distrib_tendsto_iff` (1.16.7).
* `deriv_heaviside` (1.16.15), `deriv_heaviside_shift` (1.16.16), `stieltjes_eq_deriv`
  (1.16.9_5), `delta_not_regular` (§1.16(iii)).
* `iterDeriv_piecewise`: the jump formula (1.16.17–1.16.18).
* `deriv_xPlusRpow` (1.16.20) and its iterate `distribIterDeriv_xPlusRpow`,
  `xPlusDistrib_eq_iterDeriv` (1.16.21),
  `factorial_smul_xPlusDistrib` (1.16.23).
* `sign_eq_two_mul_heaviside_sub_one` (1.16.44), `deriv_sign` (1.16.45).
* `fourierTransformSchwartz_apply` (1.16.29),
  `fourierTransformSchwartz_polynomialDifferentialOperator`, `fourierTransformSchwartz_polyMul`
  (1.16.33–1.16.34), `fourierTransformTempered_polynomialDifferentialOperator`,
  `fourierTransformTempered_polyMul` (1.16.36–1.16.37).
* `fourierTransformTempered_delta`, `fourierTransformTempered_one`,
  `fourierTransformTempered_deriv_sign`, `fourierTransformTempered_sign`,
  `fourierTransformTempered_heaviside`: the transforms of `δ`, `1`, `sign'`, `sign` and `H`
  (1.16.38–1.16.51).

## Implementation notes

Distributions on the line are Mathlib's `𝓓'(Ω, ℝ)` (real test functions); `lineDistrib f`
is the regular distribution of `f`. Tempered distributions are Mathlib's `𝓢'(E, ℂ)`.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory Complex
open scoped Topology Distributions SchwartzMap FourierTransform LineDeriv

namespace DLMF.AlgebraicAnalytic

/-! ## §1.16(ii): derivatives of distributions -/

section Deriv

variable {Ω : TopologicalSpace.Opens ℝ} {F : Type*} [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

/-- DLMF 1.16.9: `⟨Λ^{(k)}, φ⟩ = (-1)^k ⟨Λ, φ^{(k)}⟩`, with `φ^{(k)}` the `k`-fold
derivative of the test function (as an element of `𝓓(Ω, ℝ)`; its values are
`iteratedDeriv k φ`, `TestFunction.coe_iterate_lineDerivOp_one`). The case `k = 1` is 1.16.8,
Mathlib's `Distribution.lineDerivOp_apply_apply`. -/
@[dlmf 1.16.E9]
theorem distribIterDeriv_apply (k : ℕ) (T : 𝓓'(Ω, F)) (φ : 𝓓(Ω, ℝ)) :
    distribIterDeriv k T φ =
      ((-1 : ℝ) ^ k) • T ((fun ψ : 𝓓(Ω, ℝ) => ∂_{(1 : ℝ)} ψ)^[k] φ) := by
  induction k generalizing T with
  | zero => simp [distribIterDeriv]
  | succ k ih =>
    have h : distribIterDeriv (k + 1) T = distribIterDeriv k (∂_{(1 : ℝ)} T) := by
      simp only [distribIterDeriv, Function.iterate_succ_apply]
    rw [h, ih, Distribution.lineDerivOp_apply_apply, map_neg, smul_neg,
      Function.iterate_succ_apply' (fun ψ : 𝓓(Ω, ℝ) => ∂_{(1 : ℝ)} ψ) k φ, pow_succ,
      mul_neg_one, neg_smul]

/-- DLMF 1.16.12: `⟨δ_{x₀}^{(n)}, φ⟩ = (-1)^n φ^{(n)}(x₀)` (Mathlib's real `Distribution.delta`
on an open set `Ω` of the line, 1.16.11). -/
@[dlmf 1.16.E12]
theorem distribIterDeriv_delta_apply (n : ℕ) (x₀ : ℝ) (φ : 𝓓(Ω, ℝ)) :
    distribIterDeriv n (Distribution.delta x₀ : 𝓓'(Ω, ℝ)) φ =
      (-1 : ℝ) ^ n * iteratedDeriv n ⇑φ x₀ := by
  rw [distribIterDeriv_apply, Distribution.delta_apply,
    TestFunction.coe_iterate_lineDerivOp_one, ← iteratedDeriv_eq_iterate,
    smul_eq_mul]

end Deriv

/-! ## §1.16(iv): the Heaviside function -/

/-- Identity under the stated parameter and domain assumptions: `(fun x => heaviside (x - x₀)) =
(Ioi x₀).indicator (fun _ => (1 : ℝ))`. -/
private lemma heaviside_sub_eq_indicator (x₀ : ℝ) :
    (fun x => heaviside (x - x₀)) = (Ioi x₀).indicator (fun _ => (1 : ℝ)) := by
  ext x
  simp [heaviside, Set.indicator, sub_pos]

/-- Identity under the stated parameter and domain assumptions: `LocallyIntegrable (fun x =>
heaviside (x - x₀)) volume`. -/
private lemma locallyIntegrable_heaviside_sub (x₀ : ℝ) :
    LocallyIntegrable (fun x => heaviside (x - x₀)) volume := by
  rw [heaviside_sub_eq_indicator]
  exact (locallyIntegrable_const 1).indicator measurableSet_Ioi

/-- `∫ φ'(x) H(x - x₀) dx = -φ(x₀)` for a test function `φ` on the line. -/
private lemma integral_deriv_mul_heaviside_sub (x₀ : ℝ) (φ : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)) :
    ∫ x, deriv ⇑φ x * heaviside (x - x₀) = -φ x₀ := by
  have hd : ContDiff ℝ 1 ⇑φ := φ.contDiff.of_le (by simp)
  have hφ' : Continuous (deriv ⇑φ) := hd.continuous_deriv le_rfl
  have hcs : HasCompactSupport (deriv ⇑φ) := φ.hasCompactSupport.deriv
  have h1 : (fun x => deriv ⇑φ x * heaviside (x - x₀)) =
      (Ioi x₀).indicator (deriv ⇑φ) := by
    ext x; simp [heaviside, Set.indicator, sub_pos]
  rw [h1, integral_indicator measurableSet_Ioi,
    integral_Ioi_of_hasDerivAt_of_tendsto (f := ⇑φ) (m := 0)
      φ.continuous.continuousWithinAt
      (fun x _ => (hd.differentiable (by norm_num) x).hasDerivAt)
      (hφ'.integrable_of_hasCompactSupport hcs).integrableOn
      ((φ.hasCompactSupport.is_zero_at_infty).mono_left atTop_le_cocompact)]
  ring

/-- DLMF 1.16.16: `D H(x - x₀) = δ_{x₀}` as distributions on the line. -/
@[dlmf 1.16.E16]
theorem deriv_heaviside_shift (x₀ : ℝ) :
    ∂_{(1 : ℝ)} (lineDistrib fun x => heaviside (x - x₀)) = Distribution.delta x₀ := by
  ext φ
  rw [Distribution.lineDerivOp_apply_apply, lineDistrib,
    Distribution.ofFun_apply ((locallyIntegrable_heaviside_sub x₀).locallyIntegrableOn _),
    Distribution.delta_apply]
  simp only [FunLike.coe_neg, Pi.neg_apply, funext (TestFunction.lineDerivOp_one_apply_eq_deriv φ),
    smul_eq_mul, neg_mul,
    integral_neg, integral_deriv_mul_heaviside_sub, neg_neg]

/-- DLMF 1.16.15: `D H = δ` as distributions on the line. -/
@[dlmf 1.16.E15]
theorem deriv_heaviside :
    ∂_{(1 : ℝ)} (lineDistrib heaviside) = Distribution.delta 0 := by
  simpa using deriv_heaviside_shift 0

/-! ## §1.16(viii): the sign function -/

/-- DLMF 1.16.44: `sign x = 2H(x) - 1` for `x ≠ 0` (`Real.sign`). -/
@[dlmf 1.16.E44]
theorem sign_eq_two_mul_heaviside_sub_one {x : ℝ} (hx : x ≠ 0) :
    Real.sign x = 2 * heaviside x - 1 := by
  rcases hx.lt_or_gt with h | h
  · simp [Real.sign_of_neg h, heaviside, not_lt.mpr h.le]
  · simp [Real.sign_of_pos h, heaviside, h]; norm_num

/-- The distributional derivative of a constant vanishes. -/
private lemma lineDerivOp_lineDistrib_const (c : ℝ) : ∂_{(1 : ℝ)} (lineDistrib fun _ => c) = 0 := by
  ext φ
  have hd : ContDiff ℝ 1 ⇑φ := φ.contDiff.of_le (by simp)
  rw [Distribution.lineDerivOp_apply_apply, lineDistrib,
    Distribution.ofFun_apply ((locallyIntegrable_const c).locallyIntegrableOn _)]
  simp only [FunLike.coe_neg, Pi.neg_apply, funext (TestFunction.lineDerivOp_one_apply_eq_deriv φ),
    smul_eq_mul, neg_mul,
    integral_neg, integral_mul_const, zero_apply, neg_eq_zero,
    mul_eq_zero]
  left
  exact integral_eq_zero_of_hasDerivAt_of_integrable
    (fun x => (hd.differentiable (by norm_num) x).hasDerivAt)
    ((hd.continuous_deriv le_rfl).integrable_of_hasCompactSupport φ.hasCompactSupport.deriv)
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport)

/-- DLMF 1.16.45: `sign' = 2H' = 2δ` in the sense of distributions on the line. -/
@[dlmf 1.16.E45]
theorem deriv_sign : ∂_{(1 : ℝ)} (lineDistrib Real.sign) = (2 : ℝ) • Distribution.delta 0 := by
  have hae : Real.sign =ᵐ[volume] fun x => (2 : ℝ) * heaviside (x - 0) - 1 := by
    filter_upwards [(compl_mem_ae_iff.mpr (measure_singleton 0) : ({0}ᶜ : Set ℝ) ∈ ae volume)]
      with x hx
    simpa using sign_eq_two_mul_heaviside_sub_one (x := x) hx
  have h2 : lineDistrib Real.sign =
      (2 : ℝ) • lineDistrib (fun x => heaviside (x - 0)) - lineDistrib (fun _ => (1 : ℝ)) := by
    have e : (fun x => (2 : ℝ) * heaviside (x - 0) - 1) =
        (2 : ℝ) • (fun x => heaviside (x - 0)) + -(fun _ => (1 : ℝ)) := by
      ext; simp [sub_eq_add_neg]
    rw [lineDistrib, Distribution.ofFun_congr_ae (ae_restrict_of_ae hae), e,
      Distribution.ofFun_add
        (((locallyIntegrable_heaviside_sub 0).smul (2 : ℝ)).locallyIntegrableOn _)
        ((locallyIntegrable_const (1 : ℝ)).neg.locallyIntegrableOn _),
      Distribution.ofFun_smul, Distribution.ofFun_neg, sub_eq_add_neg]
    rfl
  rw [h2, sub_eq_add_neg, LineDeriv.lineDerivOp_add, LineDeriv.lineDerivOp_neg,
    LineDeriv.lineDerivOp_smul, deriv_heaviside_shift, lineDerivOp_lineDistrib_const,
        neg_zero, add_zero]

/-! ## §1.16(i): products, convergence, Stieltjes measures -/

/-- DLMF 1.16.6: `⟨αΛ, φ⟩ = ⟨Λ, αφ⟩` for a smooth `α`. -/
@[dlmf 1.16.E6]
theorem smoothMul_apply {Ω : TopologicalSpace.Opens ℝ} {α : ℝ → ℝ}
    (hα : ContDiff ℝ (⊤ : ℕ∞) α) (T : 𝓓'(Ω, ℝ)) (φ : 𝓓(Ω, ℝ)) :
    smoothMul hα T φ =
      T (TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) hα φ) := rfl

/-- DLMF 1.16.7: a sequence of distributions converges in `𝓓'` (Mathlib's topology of
compact convergence on `𝓓(Ω, ℝ)`) if and only if `⟨Λₙ, φ⟩ → ⟨Λ, φ⟩` for every test
function (L. Schwartz, *Théorie des distributions*, Ch. III, Thm. XIII; the direction `→` is
continuity of evaluation, the converse uses the Banach–Steinhaus theorem on the barrelled
space `𝓓(Ω)`). -/
@[dlmf 1.16.E7]
theorem distrib_tendsto_iff {Ω : TopologicalSpace.Opens ℝ} (T : ℕ → 𝓓'(Ω, ℝ))
    (T₀ : 𝓓'(Ω, ℝ)) :
    Tendsto T atTop (𝓝 T₀) ↔ ∀ φ : 𝓓(Ω, ℝ), Tendsto (fun n => T n φ) atTop (𝓝 (T₀ φ)) := by
  exact CompactConvergenceCLM.tendsto_atTop_iff_forall_apply T T₀

/-- DLMF 1.16.9_5: `μ_α = Dα`: the distributional derivative of a Stieltjes function `α`
(nondecreasing, right continuous, hence locally integrable) is its Lebesgue–Stieltjes
measure (1.16.3_5). With `α = H(· - x₀)` this is 1.16.16 (`deriv_heaviside_shift`). -/
@[dlmf 1.16.E9_5]
theorem stieltjes_eq_deriv (α : StieltjesFunction ℝ) :
    stieltjesDistribution ⊤ α = ∂_{(1 : ℝ)} (lineDistrib ⇑α) := by
  ext φ
  rw [stieltjesDistribution, Distribution.ofFun_apply
    ((locallyIntegrable_const (1 : ℝ)).locallyIntegrableOn _),
    Distribution.lineDerivOp_apply_apply, lineDistrib,
    Distribution.ofFun_apply (α.mono.locallyIntegrable.locallyIntegrableOn _)]
  simp only [FunLike.coe_neg, Pi.neg_apply, funext (TestFunction.lineDerivOp_one_apply_eq_deriv φ),
    smul_eq_mul, neg_mul,
    integral_neg, mul_one]
  simpa only [mul_comm, neg_neg] using
    (congrArg Neg.neg (α.integral_mul_deriv_eq_neg
      (φ.contDiff.of_le (by simp)) φ.hasCompactSupport)).symm

/-- §1.16(ii): if the Lebesgue–Stieltjes measure of `α` is absolutely continuous with density
`w` (`dα = w dx`), then `Dα = Λ_w`. -/
@[dlmf 1.16.ii]
theorem deriv_stieltjes_of_density (α : StieltjesFunction ℝ) {w : ℝ → ℝ}
    (hw : α.measure = volume.withDensity fun x => ENNReal.ofReal (w x))
    (hw0 : ∀ x, 0 ≤ w x) (hwi : LocallyIntegrable w volume) :
    ∂_{(1 : ℝ)} (lineDistrib ⇑α) = lineDistrib w := by
  rw [← stieltjes_eq_deriv]
  ext φ
  rw [stieltjesDistribution, Distribution.ofFun_apply
    ((locallyIntegrable_const (1 : ℝ)).locallyIntegrableOn _), lineDistrib,
    Distribution.ofFun_apply (hwi.locallyIntegrableOn _)]
  simp only [smul_eq_mul, mul_one]
  rw [hw, integral_withDensity_eq_integral_toReal_smul₀
    hwi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hw0 _), smul_eq_mul, mul_comm]

/-- §1.16(iii): the Dirac delta distribution is singular: it is not `Λ_f` for any locally
integrable `f`. -/
@[dlmf 1.16.iii]
theorem delta_not_regular :
    ¬ ∃ f : ℝ → ℝ, LocallyIntegrable f volume ∧ lineDistrib f = Distribution.delta 0 := by
  rintro ⟨f, hf, he⟩
  have hz : ∀ᵐ x : ℝ, x ∈ ({0}ᶜ : Set ℝ) → f x = 0 := by
    refine isClosed_singleton.isOpen_compl.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hf.locallyIntegrableOn _) ?_
    intro g hgd hgc hgs
    let φ : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ) :=
      ⟨g, hgd, hgc, subset_univ _⟩
    have hg0 : g 0 = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hgs h (mem_singleton 0))
    have hh := congrArg (fun T : 𝓓'((⊤ : TopologicalSpace.Opens ℝ), ℝ) => T φ) he
    rw [lineDistrib, Distribution.ofFun_apply (hf.locallyIntegrableOn _),
      Distribution.delta_apply] at hh
    simpa [φ, hg0] using hh
  have hfae : f =ᵐ[volume] 0 := by
    have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by simp [ae_iff]
    filter_upwards [hz, hne] with x hx hx0
    exact hx hx0
  have hzdis : lineDistrib f = 0 := by
    rw [lineDistrib, Distribution.ofFun_congr_ae (by simpa using hfae), Distribution.ofFun_zero]
  obtain ⟨g, hgs, hgc, hgd, -, hg0⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞))
      (s := (univ : Set ℝ)) (x := 0) (Filter.univ_mem)
  let φ : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ) := ⟨g, hgd, hgc, hgs⟩
  have hh := congrArg (fun T : 𝓓'((⊤ : TopologicalSpace.Opens ℝ), ℝ) => T φ)
    (he.symm.trans hzdis)
  simp [Distribution.delta_apply, φ, hg0] at hh

/-! ## §1.16(iv): jumps and the distributions `x₊^α` -/

/-- DLMF 1.16.17–1.16.18 (jump formula): let `f` agree with the smooth function `g` on
`(x₀, ∞)` and with the smooth function `h` on `(-∞, x₀)` (so that `f` is smooth except at
`x₀` with one-sided derivatives of all orders, `f^{(n)}(x₀±)` being `g^{(n)}(x₀)` and
`h^{(n)}(x₀)`), and let `σₙ = f^{(n)}(x₀+) - f^{(n)}(x₀-)` (1.16.17). Then
`D^m f = f^{(m)} + σ₀ δ_{x₀}^{(m-1)} + ⋯ + σ_{m-1} δ_{x₀}` (1.16.18), where `f^{(m)}` is the
classical derivative off `x₀`. -/
@[dlmf 1.16.E17, dlmf 1.16.E18]
theorem iterDeriv_piecewise {f g h : ℝ → ℝ} {x₀ : ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hfg : ∀ x, x₀ < x → f x = g x)
    (hfh : ∀ x, x < x₀ → f x = h x) (m : ℕ) (hm : 1 ≤ m) :
    distribIterDeriv m (lineDistrib f) =
      lineDistrib (fun x => if x₀ < x then iteratedDeriv m g x else iteratedDeriv m h x) +
      ∑ k ∈ Finset.range m, (iteratedDeriv k g x₀ - iteratedDeriv k h x₀) •
        distribIterDeriv (m - 1 - k) (Distribution.delta x₀) := by
  let p (n : ℕ) : ℝ → ℝ :=
    fun x => if x₀ < x then iteratedDeriv n g x else iteratedDeriv n h x
  have he : lineDistrib f = lineDistrib (p 0) := by
    apply Distribution.ofFun_congr_ae
    -- Identify the top open set with the whole line before removing the singleton.
    change f =ᵐ[volume.restrict Set.univ] p 0
    rw [Measure.restrict_univ]
    have hne : ∀ᵐ x : ℝ ∂volume, x ≠ x₀ := by simp [ae_iff]
    filter_upwards [hne] with x hx
    dsimp [p]
    split_ifs with hlt
    · exact hfg x hlt
    · exact hfh x (lt_of_le_of_ne (le_of_not_gt hlt) hx)
  have hd (n : ℕ) : ∂_{(1 : ℝ)} (lineDistrib (p n)) =
      lineDistrib (p (n + 1)) + (iteratedDeriv n g x₀ - iteratedDeriv n h x₀) •
        Distribution.delta x₀ := by
    have hg' : ContDiff ℝ 1 (iteratedDeriv n g) :=
      (contDiff_nat_succ_iff_contDiff_one_iteratedDeriv.mp (hg.of_le (by simp))).2
    have hh' : ContDiff ℝ 1 (iteratedDeriv n h) :=
      (contDiff_nat_succ_iff_contDiff_one_iteratedDeriv.mp (hh.of_le (by simp))).2
    simpa only [p, lineDistrib, iteratedDeriv_succ] using
      Distribution.lineDerivOp_ofFun_piecewise hg' hh' x₀
  have hall (n : ℕ) :
      distribIterDeriv n (lineDistrib (p 0)) = lineDistrib (p n) +
        ∑ k ∈ Finset.range n, (iteratedDeriv k g x₀ - iteratedDeriv k h x₀) •
          distribIterDeriv (n - 1 - k) (Distribution.delta x₀) := by
    induction n with
    | zero => simp [distribIterDeriv]
    | succ n ih =>
      rw [show distribIterDeriv (n + 1) (lineDistrib (p 0)) =
        ∂_{(1 : ℝ)} (distribIterDeriv n (lineDistrib (p 0))) by
          simp only [distribIterDeriv, Function.iterate_succ_apply']]
      rw [ih, LineDeriv.lineDerivOp_add, hd]
      rw [Finset.sum_range_succ]
      simp only [Nat.add_sub_cancel, Nat.sub_self, distribIterDeriv,
        Function.iterate_zero, id_eq]
      have hs : ∂_{(1 : ℝ)}
          (∑ k ∈ Finset.range n, (iteratedDeriv k g x₀ - iteratedDeriv k h x₀) •
            (fun S : 𝓓'((⊤ : TopologicalSpace.Opens ℝ), ℝ) => ∂_{(1 : ℝ)} S)^[n - 1 - k]
              (Distribution.delta x₀)) =
          ∑ k ∈ Finset.range n, (iteratedDeriv k g x₀ - iteratedDeriv k h x₀) •
            (fun S : 𝓓'((⊤ : TopologicalSpace.Opens ℝ), ℝ) => ∂_{(1 : ℝ)} S)^[n - k]
              (Distribution.delta x₀) := by
        rw [LineDeriv.lineDerivOp_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [LineDeriv.lineDerivOp_smul]
        congr 1
        rw [← Function.iterate_succ_apply'
          (fun S : 𝓓'((⊤ : TopologicalSpace.Opens ℝ), ℝ) => ∂_{(1 : ℝ)} S)]
        congr 2
        have hk' := Finset.mem_range.mp hk
        omega
      rw [hs]
      abel
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [he]
  exact hall (n + 1)

/-- `x₊^β` is locally integrable for `β > -1`. -/
private lemma locallyIntegrable_xPlusRpow {β : ℝ} (hβ : -1 < β) :
    LocallyIntegrable (xPlusRpow β) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨b, hb⟩ := hK.bddAbove
  have hsub : K ⊆ Iic 0 ∪ Ioc 0 (max b 0) := by
    intro x hx
    rcases le_or_gt x 0 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, (hb hx).trans (le_max_left _ _)⟩
  refine IntegrableOn.mono_set (integrableOn_union.mpr ⟨?_, ?_⟩) hsub
  · refine (integrableOn_zero).congr_fun (fun x hx => ?_) measurableSet_Iic
    simp [xPlusRpow, not_lt.mpr (show x ≤ 0 from hx)]
  · have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := max b 0) hβ)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (le_max_right _ _)] at h
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ioc
    simp [xPlusRpow, hx.1]

/-- DLMF 1.16.20: `D x₊^α = α x₊^{α-1}` for `α > 0`, as distributions on the line. -/
@[dlmf 1.16.E20]
theorem deriv_xPlusRpow {α : ℝ} (hα : 0 < α) :
    ∂_{(1 : ℝ)} (lineDistrib (xPlusRpow α)) = α • lineDistrib (xPlusRpow (α - 1)) := by
  ext φ
  have hli := locallyIntegrable_xPlusRpow (show -1 < α by linarith)
  have hli' := locallyIntegrable_xPlusRpow (show -1 < α - 1 by linarith)
  have hd : ContDiff ℝ 1 ⇑φ := φ.contDiff.of_le (by simp)
  rw [Distribution.lineDerivOp_apply_apply, lineDistrib,
    Distribution.ofFun_apply (hli.locallyIntegrableOn _)]
  rw [_root_.smul_apply, lineDistrib,
    Distribution.ofFun_apply (hli'.locallyIntegrableOn _)]
  simp only [FunLike.coe_neg, Pi.neg_apply, funext (TestFunction.lineDerivOp_one_apply_eq_deriv φ),
    smul_eq_mul, neg_mul,
    integral_neg]
  have h1 : (fun x => deriv ⇑φ x * xPlusRpow α x) =
      (Ioi 0).indicator (fun x => x ^ α * deriv ⇑φ x) := by
    ext x; by_cases hx : 0 < x <;> simp [xPlusRpow, Set.indicator, hx, mul_comm]
  have h2 : (fun x => φ x * xPlusRpow (α - 1) x) =
      (Ioi 0).indicator (fun x => x ^ (α - 1) * φ x) := by
    ext x; by_cases hx : 0 < x <;> simp [xPlusRpow, Set.indicator, hx, mul_comm]
  rw [h1, h2, integral_indicator measurableSet_Ioi, integral_indicator measurableSet_Ioi]
  have hcs : HasCompactSupport (fun x => x ^ α * φ x) := φ.hasCompactSupport.mul_left
  have hcont : Continuous (fun x => x ^ α * φ x) :=
    (Real.continuous_rpow_const hα.le).mul φ.continuous
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := 0) (b' := 0)
    (u := fun x => x ^ α) (u' := fun x => α * x ^ (α - 1)) (v := ⇑φ) (v' := deriv ⇑φ)
    (fun x hx => Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx)))
    (fun x _ => (hd.differentiable (by norm_num) x).hasDerivAt)
    (((Real.continuous_rpow_const hα.le).mul
      (hd.continuous_deriv le_rfl)).integrable_of_hasCompactSupport
        φ.hasCompactSupport.deriv.mul_left).integrableOn
    (by
      have hI := hli'.integrable_smul_left_of_hasCompactSupport φ.continuous φ.hasCompactSupport
      refine ((hI.const_mul α).integrableOn).congr_fun (fun x hx => ?_) measurableSet_Ioi
      simp [xPlusRpow, show (0 : ℝ) < x from hx]; ring)
    (by
      have := hcont.tendsto 0
      simp only [Real.zero_rpow hα.ne', zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds)
    ((hcs.is_zero_at_infty).mono_left atTop_le_cocompact)
  simp only [sub_zero, zero_sub] at hibp
  rw [hibp, neg_neg, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  ring

/-- `D^k` commutes with scalar multiplication. -/
private lemma distribIterDeriv_smul (k : ℕ) (c : ℝ)
    (T : 𝓓'((⊤ : TopologicalSpace.Opens ℝ), ℝ)) :
    distribIterDeriv k (c • T) = c • distribIterDeriv k T := by
  induction k generalizing T with
  | zero => rfl
  | succ k ih =>
    simp only [distribIterDeriv, Function.iterate_succ_apply] at ih ⊢
    rw [LineDeriv.lineDerivOp_smul, ih]

/-- Iterated form of DLMF 1.16.20: `D^k x₊^{γ+k} = (γ+1)_k x₊^γ` for `γ > -1`. -/
theorem distribIterDeriv_xPlusRpow {γ : ℝ} (hγ : -1 < γ) (k : ℕ) :
    distribIterDeriv k (lineDistrib (xPlusRpow (γ + k))) =
      (ascPochhammer ℝ k).eval (γ + 1) • lineDistrib (xPlusRpow γ) := by
  induction k with
  | zero => simp [distribIterDeriv]
  | succ k ih =>
    have h : distribIterDeriv (k + 1) (lineDistrib (xPlusRpow (γ + ↑(k + 1)))) =
        distribIterDeriv k (∂_{(1 : ℝ)} (lineDistrib (xPlusRpow (γ + ↑(k + 1))))) := by
      simp only [distribIterDeriv, Function.iterate_succ_apply]
    rw [h, deriv_xPlusRpow (by push_cast; linarith), distribIterDeriv_smul,
      show γ + ↑(k + 1) - 1 = γ + k by push_cast; ring, ih, smul_smul, ascPochhammer_succ_eval]
    congr 1
    push_cast
    ring

/-- DLMF 1.16.21: for `α < -1` not an integer, `x₊^α = D^n x₊^{α+n} / (α+1)_n` for every
integer `n` with `α + n > -1` (the definition `xPlusDistrib` uses the least such `n`). -/
@[dlmf 1.16.E21]
theorem xPlusDistrib_eq_iterDeriv {α : ℝ} (hα : α < -1) (hαZ : ∀ m : ℤ, α ≠ m) (n : ℕ)
    (hn : -1 < α + n) :
    xPlusDistrib α = ((ascPochhammer ℝ n).eval (α + 1))⁻¹ •
      distribIterDeriv n (lineDistrib (xPlusRpow (α + n))) := by
  set n₀ := ⌊-α⌋₊ with hn₀
  have hfl : (n₀ : ℝ) ≤ -α := Nat.floor_le (by linarith)
  have hfl' : -α < n₀ + 1 := Nat.lt_floor_add_one _
  have hne : (n₀ : ℝ) ≠ -α := by
    intro h
    exact hαZ (-(n₀ : ℤ)) (by push_cast; linarith)
  have hγ : -1 < α + n₀ := by linarith
  have hnn : n₀ ≤ n := by
    have : (n₀ : ℝ) < n + 1 := by linarith [lt_of_le_of_ne hfl hne]
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnn
  have hnotint : ¬ ∃ m : ℕ, α = -1 - m := by
    rintro ⟨m, hm⟩
    exact hαZ (-1 - m) (by rw [hm]; push_cast; ring)
  rw [xPlusDistrib, ite_eq_right (by linarith), ite_eq_right hnotint, ← hn₀]
  have hsplit : distribIterDeriv (n₀ + k) (lineDistrib (xPlusRpow (α + ↑(n₀ + k)))) =
      distribIterDeriv n₀ (distribIterDeriv k (lineDistrib (xPlusRpow (α + n₀ + k)))) := by
    simp only [distribIterDeriv, Function.iterate_add_apply]
    push_cast
    rw [add_assoc]
  rw [hsplit, distribIterDeriv_xPlusRpow hγ k, distribIterDeriv_smul, smul_smul]
  congr 1
  have hmul := congrArg (Polynomial.eval (α + 1)) (ascPochhammer_mul (S := ℝ) n₀ k)
  rw [Polynomial.eval_mul, Polynomial.eval_comp] at hmul
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_natCast] at hmul
  rw [← hmul, show α + n₀ + 1 = α + 1 + n₀ by ring]
  have h0 : (ascPochhammer ℝ k).eval (α + 1 + n₀) ≠ 0 := by
    rw [Ne, ascPochhammer_eval_eq_zero_iff]
    rintro ⟨j, -, hj⟩
    exact hαZ (-1 - n₀ - j) (by push_cast; linarith)
  field_simp

/-- DLMF 1.16.23: `(-1)^n n! x₊^{-1-n} = D^{n+1} ln₊ x`, `n = 0, 1, 2, …`. -/
@[dlmf 1.16.E23]
theorem factorial_smul_xPlusDistrib (n : ℕ) :
    ((-1 : ℝ) ^ n * n.factorial) • xPlusDistrib (-1 - n) =
      distribIterDeriv (n + 1) (lineDistrib logPlus) := by
  have h1 : ¬ (-1 : ℝ) < -1 - n := by
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have h2 : ⌊(-1 : ℝ) - (-1 - n)⌋₊ = n := by simp
  have h3 : ∃ m : ℕ, (-1 - n : ℝ) = -1 - m := ⟨n, rfl⟩
  rw [xPlusDistrib, ite_eq_right_of_eq_false _ _ (eq_false h1),
    ite_eq_left_of_eq_true _ _ (eq_true h3), h2, smul_smul]
  have h4 : (n.factorial : ℝ) ≠ 0 := by positivity
  have h5 : ((-1 : ℝ) ^ n * n.factorial) * ((-1) ^ n / n.factorial) = 1 := by
    field_simp
    rw [← pow_mul, mul_comm n 2, pow_mul]
    norm_num
  rw [h5, one_smul]

/-! ## §1.16(vi): several variables -/

/-- DLMF 1.16.27: the distributional derivative `D^k f` of a locally integrable function on
`ℝⁿ` acts by `⟨D^k f, φ⟩ = (-1)^{|k|} ∫ f(x) φ^{(k)}(x) dx`. Here the multi-index `k` is
given as the list `m : Fin r → ℝⁿ` of its `r = |k|` coordinate directions, `D^k` is Mathlib's
iterated directional derivative `∂^{m}` on `𝓓'` and `φ^{(k)} = ∂^{m} φ`. -/
@[dlmf 1.16.E27]
theorem iteratedLineDerivOp_ofFun_apply {n r : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : LocallyIntegrable f volume) (m : Fin r → EuclideanSpace ℝ (Fin n))
    (φ : 𝓓((⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∂^{m} (Distribution.ofFun ⊤ f volume ⊤ :
        𝓓'((⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))), ℝ))) φ =
      (-1 : ℝ) ^ r * ∫ x, f x * (∂^{m} φ) x := by
  rw [Distribution.iteratedLineDerivOp_apply,
    Distribution.ofFun_apply (hf.locallyIntegrableOn _)]
  simp only [smul_eq_mul, mul_comm]

/-! ## §1.16(vii): the DLMF Fourier transform -/

section Fourier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- DLMF 1.16.29: `𝓕φ(x) = (2π)^{-n/2} ∫ φ(t) e^{i x·t} dt` for `φ ∈ 𝓢(E, ℂ)`,
`n = dim E`. -/
@[dlmf 1.16.E29]
theorem fourierTransformSchwartz_apply (φ : 𝓢(E, ℂ)) (x : E) :
    fourierTransformSchwartz φ x =
      (((2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) : ℝ) : ℂ) *
        ∫ t, φ t * exp (I * (inner ℝ x t : ℝ)) := by
  simp only [fourierTransformSchwartz, smul_apply, ContinuousLinearMap.comp_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, FourierTransform.fourierInvCLM_apply, SchwartzMap.fourierInv_coe,
    Real.fourierInv_eq', smul_eq_mul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [scaleEquiv, ContinuousLinearEquiv.equivOfInverse_apply,
    smul_apply, ContinuousLinearMap.id_apply, inner_smul_right,
    real_inner_comm x t]
  rw [mul_comm (φ t)]
  congr 2
  push_cast
  field_simp

end Fourier

/-- A linear functional on which each operator acts by a scalar evaluates the polynomial in
those operators by substituting the same scalars. -/
lemma polynomialOperator_apply_eigenfunctional {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (L : V →ₗ[ℂ] ℂ) (D : Fin n → Module.End ℂ V) (g : Fin n → ℂ)
    (hL : ∀ j φ, L (D j φ) = g j * L φ) (P : MvPolynomial (Fin n) ℂ) (φ : V) :
    L (polynomialOperator P D φ) = MvPolynomial.eval g P * L φ := by
  have hp (j : Fin n) (k : ℕ) (φ : V) : L ((D j ^ k) φ) = g j ^ k * L φ := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', mul_apply_eq_comp, hL, pow_succ]
      rw [ih]
      ring
  have hl (α : Fin n → ℕ) (l : List (Fin n)) (φ : V) :
      L ((l.map (fun j => D j ^ α j)).prod φ) =
        (l.map (fun j => g j ^ α j)).prod * L φ := by
    induction l generalizing φ with
    | nil => simp
    | cons j l ih =>
      simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp]
      rw [hp, ih]
      ring
  have hmono (α : Fin n →₀ ℕ) :
      L ((List.ofFn (fun j => D j ^ α j)).prod φ) = (∏ j, g j ^ α j) * L φ := by
    simpa only [List.map_ofFn, Function.comp_def, List.prod_ofFn, id_eq] using
      hl α (List.ofFn id) φ
  rw [polynomialOperator, LinearMap.sum_apply, map_sum, MvPolynomial.eval_eq', Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro α _
  rw [LinearMap.smul_apply, map_smul, smul_eq_mul, hmono]
  ring

section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
/-- The DLMF Fourier transform sends a directional derivative to multiplication by
`-I * inner x v`. This specializes Mathlib’s `SchwartzMap.fourierInv_lineDerivOp_eq`. -/
lemma fourierTransformSchwartz_lineDeriv (φ : 𝓢(E, ℂ)) (v : E) :
    fourierTransformSchwartz (∂_{v} φ) =
      SchwartzMap.smulLeftCLM ℂ (fun x : E => -I * (inner ℝ x v : ℂ))
        (fourierTransformSchwartz φ) := by
  have hg : (fun x : E => -I * (inner ℝ x v : ℂ)).HasTemperateGrowth := by fun_prop
  have hi : (fun x : E => inner ℝ x v).HasTemperateGrowth := by fun_prop
  simp only [fourierTransformSchwartz, smul_apply, ContinuousLinearMap.comp_apply,
    FourierTransform.fourierInvCLM_apply, SchwartzMap.fourierInv_lineDerivOp_eq,
    map_smul]
  ext x
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    SchwartzMap.smulLeftCLM_apply hg, SchwartzMap.smulLeftCLM_apply hi,
    smul_apply, Complex.real_smul, smul_eq_mul]
  simp only [scaleEquiv, ContinuousLinearEquiv.equivOfInverse_apply,
    smul_apply, ContinuousLinearMap.id_apply, inner_smul_left]
  simp only [starRingEnd_apply, star_trivial]
  push_cast
  field_simp
end General

/-- The DLMF differential operator `D_j = (1 / I) ∂_j` transforms to multiplication by `-x_j`. -/
lemma fourierTransformSchwartz_normalizedPartialDeriv {n : ℕ} (j : Fin n)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (x : EuclideanSpace ℝ (Fin n)) :
    fourierTransformSchwartz (normalizedPartialDeriv j φ) x = -(x j : ℂ) *
        fourierTransformSchwartz φ x := by
  have hg : (fun x : EuclideanSpace ℝ (Fin n) =>
      -I * (inner ℝ x (EuclideanSpace.single j (1 : ℝ)) : ℂ)).HasTemperateGrowth := by fun_prop
  simp only [normalizedPartialDeriv, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
    LineDeriv.lineDerivOpCLM_apply, map_smul, smul_apply]
  rw [fourierTransformSchwartz_lineDeriv]
  rw [SchwartzMap.smulLeftCLM_apply hg]
  simp only [smul_eq_mul, EuclideanSpace.inner_single_right, one_mul]
  simp only [starRingEnd_apply, star_trivial]
  linear_combination ((x j : ℂ) * fourierTransformSchwartz φ x) * I_sq


/-- A complex polynomial in the real coordinate functions has temperate growth. -/
lemma polyEval_hasTemperateGrowth {n : ℕ} (P : MvPolynomial (Fin n) ℂ) :
    (polyEval P).HasTemperateGrowth := by
  have hall (Q : MvPolynomial (Fin n) ℂ) : (polyEval Q).HasTemperateGrowth := by
    induction Q using MvPolynomial.induction_on with
    | C c =>
      convert Function.HasTemperateGrowth.const (E := EuclideanSpace ℝ (Fin n)) c using 1
      ext y
      simp [polyEval]
    | add p q hp hq =>
      convert hp.add hq using 1
      ext y
      simp [polyEval]
    | mul_X p j hp =>
      have hx : (fun x : EuclideanSpace ℝ (Fin n) => (x j : ℂ)).HasTemperateGrowth := by
        have hi : (fun x : EuclideanSpace ℝ (Fin n) =>
            (inner ℝ x (EuclideanSpace.single j (1 : ℝ)) : ℂ)).HasTemperateGrowth := by fun_prop
        convert hi using 1
        ext y
        simp [EuclideanSpace.inner_single_right]
      convert hp.mul hx using 1
      ext y
      simp [polyEval]
  exact hall P


/-- A linear map intertwining two families of operators also intertwines every polynomial
in those families, preserving the fixed order in `polynomialOperator`. -/
lemma polynomialOperator_intertwine {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (L : V →ₗ[ℂ] W) (D : Fin n → Module.End ℂ V) (T : Fin n → Module.End ℂ W)
    (hL : ∀ j φ, L (D j φ) = T j (L φ)) (P : MvPolynomial (Fin n) ℂ) (φ : V) :
    L (polynomialOperator P D φ) = polynomialOperator P T (L φ) := by
  have hp (j : Fin n) (k : ℕ) (φ : V) : L ((D j ^ k) φ) = (T j ^ k) (L φ) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', mul_apply_eq_comp, hL, ih, pow_succ', mul_apply_eq_comp]
  have hl (α : Fin n → ℕ) (l : List (Fin n)) (φ : V) :
      L ((l.map (fun j => D j ^ α j)).prod φ) =
        (l.map (fun j => T j ^ α j)).prod (L φ) := by
    induction l generalizing φ with
    | nil => simp
    | cons j l ih =>
      simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp]
      rw [hp, ih]
  have hmono (α : Fin n →₀ ℕ) :
      L ((List.ofFn (fun j => D j ^ α j)).prod φ) =
        (List.ofFn (fun j => T j ^ α j)).prod (L φ) := by
    simpa only [List.map_ofFn, Function.comp_def, id_eq] using hl α (List.ofFn id) φ
  simp only [polynomialOperator, LinearMap.sum_apply, map_sum, LinearMap.smul_apply,
      map_smul, hmono]


section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
/-- A directional derivative of the DLMF Fourier transform corresponds to multiplying the
original Schwartz function by `I * inner x v`, including DLMF’s frequency normalization. -/
lemma lineDeriv_fourierTransformSchwartz (φ : 𝓢(E, ℂ)) (v : E) :
    ∂_{v} (fourierTransformSchwartz φ) =
      fourierTransformSchwartz (SchwartzMap.smulLeftCLM ℂ
        (fun x : E => I * (inner ℝ x v : ℂ)) φ) := by
  simp only [fourierTransformSchwartz, smul_apply, ContinuousLinearMap.comp_apply,
    FourierTransform.fourierInvCLM_apply]
  rw [LineDeriv.lineDerivOp_smul, SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv,
    SchwartzMap.lineDerivOp_fourierInv_eq]
  congr 3
  ext x
  have h₁ : (fun y : E =>
      inner ℝ y ((scaleEquiv (2 * Real.pi)⁻¹ (by positivity)) v)).HasTemperateGrowth := by fun_prop
  have h₂ : (fun x : E => I * (inner ℝ x v : ℂ)).HasTemperateGrowth := by fun_prop
  simp only [smul_apply]
  rw [SchwartzMap.smulLeftCLM_apply h₁, SchwartzMap.smulLeftCLM_apply h₂]
  simp only [Complex.real_smul, smul_eq_mul]
  simp only [scaleEquiv, ContinuousLinearEquiv.equivOfInverse_apply,
    smul_apply, ContinuousLinearMap.id_apply, inner_smul_right]
  push_cast
  field_simp
end General

/-- A bilinear pairing transposes a polynomial in operators to the corresponding polynomial
in their adjoints, provided the latter commute. -/
lemma polynomialOperator_pairing {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (D : Fin n → Module.End ℂ V)
    (T : Fin n → Module.End ℂ W) (hT : ∀ i j, Commute (T i) (T j))
    (hB : ∀ j v w, B (D j v) w = B v (T j w)) (P : MvPolynomial (Fin n) ℂ)
    (v : V) (w : W) : B (polynomialOperator P D v) w = B v (polynomialOperator P T w) := by
  have hp (j : Fin n) (k : ℕ) (v : V) (w : W) :
      B ((D j ^ k) v) w = B v ((T j ^ k) w) := by
    induction k generalizing v with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, mul_apply_eq_comp, ih, hB, pow_succ', mul_apply_eq_comp]
  have hl (α : Fin n → ℕ) (l : List (Fin n)) (v : V) (w : W) :
      B ((l.map (fun j => D j ^ α j)).prod v) w =
        B v ((l.map (fun j => T j ^ α j)).prod w) := by
    induction l generalizing v w with
    | nil => simp
    | cons j l ih =>
      simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp]
      rw [hp, ih]
      have hc : Commute (T j ^ α j) (l.map (fun k => T k ^ α k)).prod := by
        apply Commute.list_prod_right
        intro t ht
        obtain ⟨k, _, rfl⟩ := List.mem_map.mp ht
        exact (hT j k).pow_pow _ _
      exact congrArg (fun A : Module.End ℂ W => B v (A w)) hc.eq.symm
  have hmono (α : Fin n →₀ ℕ) :
      B ((List.ofFn (fun j => D j ^ α j)).prod v) w =
        B v ((List.ofFn (fun j => T j ^ α j)).prod w) := by
    simpa only [List.map_ofFn, Function.comp_def, id_eq] using hl α (List.ofFn id) v w
  simp only [polynomialOperator, LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul,
    smul_eq_mul, hmono]

/-- Directional derivatives of smooth Schwartz functions commute. The proof adapts
Tau Ceti’s `TestFunction.lineDerivOp_comm`, using Mathlib’s symmetric second derivative. -/
lemma schwartz_lineDeriv_comm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : 𝓢(E, ℂ)) (v w : E) : ∂_{v} (∂_{w} φ) = ∂_{w} (∂_{v} φ) := by
  ext x
  have hd : DifferentiableAt ℝ (fderiv ℝ (φ : E → ℂ)) x :=
    (φ.smooth ⊤ |>.fderiv_right (m := 1) (by simp)).differentiable one_ne_zero x
  change fderiv ℝ (fun y => fderiv ℝ (φ : E → ℂ) y w) x v =
    fderiv ℝ (fun y => fderiv ℝ (φ : E → ℂ) y v) x w
  simpa [fderiv_clm_apply hd (differentiableAt_const _)] using
    ((φ.smooth ⊤ |>.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)).eq v w
/-- The coordinate differential operators `D_i` and `D_j` commute on Schwartz space. -/
lemma normalizedPartialDeriv_commute {n : ℕ} (i j : Fin n) : Commute (normalizedPartialDeriv i)
    (normalizedPartialDeriv j) := by
  ext φ
  simp only [mul_apply_eq_comp, normalizedPartialDeriv, LinearMap.smul_apply,
    ContinuousLinearMap.coe_coe, LineDeriv.lineDerivOpCLM_apply,
    LineDeriv.lineDerivOp_smul]
  rw [schwartz_lineDeriv_comm]

/-- Applying a polynomial differential operator to a tempered distribution transfers the
operators to the test function with a minus sign on each coordinate derivative. -/
lemma temperedPolynomialDifferentialOperator_apply {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    temperedPolynomialDifferentialOperator P u φ =
        u (polynomialOperator P (fun j => -normalizedPartialDeriv j) φ) := by
  let B : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) →ₗ[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun v => v.toLinearMap
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hB (j : Fin n) (v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
      (ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
      B (temperedD j v) ψ = B v ((-normalizedPartialDeriv j) ψ) := by
    change (-I) * v (-∂_{EuclideanSpace.single j (1 : ℝ)} ψ) =
      v (-((-I) • ∂_{EuclideanSpace.single j (1 : ℝ)} ψ))
    simp only [map_neg, map_smul, smul_eq_mul]
    ring
  exact polynomialOperator_pairing B temperedD (fun j => -normalizedPartialDeriv j)
    (fun i j => by
      change (-normalizedPartialDeriv i) * (-normalizedPartialDeriv j) =
          (-normalizedPartialDeriv j) * (-normalizedPartialDeriv i)
      simpa only [neg_mul_neg] using (normalizedPartialDeriv_commute i j).eq) hB P u φ
/-- A real coordinate function, viewed as complex valued, has temperate growth. -/
lemma coordinate_hasTemperateGrowth {n : ℕ} (j : Fin n) :
    (fun x : EuclideanSpace ℝ (Fin n) => (x j : ℂ)).HasTemperateGrowth := by
  have hi : (fun x : EuclideanSpace ℝ (Fin n) =>
      (inner ℝ x (EuclideanSpace.single j (1 : ℝ)) : ℂ)).HasTemperateGrowth := by fun_prop
  convert hi using 1
  ext y
  simp [EuclideanSpace.inner_single_right]
/-- A polynomial in coordinate multiplication operators acts pointwise as the corresponding
polynomial function, with a common complex scale factor on the coordinates. -/
lemma polynomialOperator_coordinateMul_apply {n : ℕ} (c : ℂ) (P : MvPolynomial (Fin n) ℂ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (x : EuclideanSpace ℝ (Fin n)) :
    polynomialOperator P (fun j => (SchwartzMap.smulLeftCLM ℂ
      (fun y : EuclideanSpace ℝ (Fin n) => c * (y j : ℂ))).toLinearMap) φ x =
      MvPolynomial.eval (fun j => c * (x j : ℂ)) P * φ x := by
  exact polynomialOperator_apply_eigenfunctional (TemperedDistribution.delta x).toLinearMap
    _ (fun j => c * (x j : ℂ)) (fun j ψ => by
      have hg : (fun y : EuclideanSpace ℝ (Fin n) => c * (y j : ℂ)).HasTemperateGrowth :=
        (Function.HasTemperateGrowth.const (E := EuclideanSpace ℝ (Fin n)) c).mul
          (coordinate_hasTemperateGrowth j)
      change (SchwartzMap.smulLeftCLM ℂ _ ψ) x = _
      rw [SchwartzMap.smulLeftCLM_apply hg]
      rfl) P φ
/-- The DLMF operator `D_j` applied to a Fourier transform is the transform of multiplication
by the original coordinate `x_j`. -/
lemma normalizedPartialDeriv_fourierTransformSchwartz {n : ℕ} (j : Fin n)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    normalizedPartialDeriv j (fourierTransformSchwartz φ) =
      fourierTransformSchwartz (SchwartzMap.smulLeftCLM ℂ
        (fun x : EuclideanSpace ℝ (Fin n) => (x j : ℂ)) φ) := by
  change (-I) • (∂_{EuclideanSpace.single j (1 : ℝ)} (fourierTransformSchwartz φ)) = _
  rw [lineDeriv_fourierTransformSchwartz]
  have hg : (fun x : EuclideanSpace ℝ (Fin n) =>
      I * (inner ℝ x (EuclideanSpace.single j (1 : ℝ)) : ℂ)).HasTemperateGrowth := by fun_prop
  have he : SchwartzMap.smulLeftCLM ℂ
      (fun x : EuclideanSpace ℝ (Fin n) => I *
          (inner ℝ x (EuclideanSpace.single j (1 : ℝ)) : ℂ)) φ =
      I • SchwartzMap.smulLeftCLM ℂ (fun x : EuclideanSpace ℝ (Fin n) => (x j : ℂ)) φ := by
    ext x
    rw [SchwartzMap.smulLeftCLM_apply hg]
    simp only [smul_apply]
    rw [SchwartzMap.smulLeftCLM_apply (coordinate_hasTemperateGrowth j)]
    simp [EuclideanSpace.inner_single_right, smul_eq_mul, mul_assoc]
  rw [he, map_smul, smul_smul]
  simp


/-- DLMF 1.16.33: `𝓕(P(𝐃)φ)(𝐱) = P(-𝐱) 𝓕φ(𝐱)` on Schwartz space. -/
@[dlmf 1.16.E33]
theorem fourierTransformSchwartz_polynomialDifferentialOperator {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    fourierTransformSchwartz (polynomialDifferentialOperator P φ) =
        polyMul (polyNeg P) (fourierTransformSchwartz φ) := by
  ext x
  let L : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) →ₗ[ℂ] ℂ :=
    (TemperedDistribution.delta x).toLinearMap.comp fourierTransformSchwartz.toLinearMap
  have h := polynomialOperator_apply_eigenfunctional L normalizedPartialDeriv (fun j => -(x j : ℂ))
    (fun j φ => fourierTransformSchwartz_normalizedPartialDeriv j φ x) P φ
  have hg := polyEval_hasTemperateGrowth (polyNeg P)
  rw [polyMul, SchwartzMap.smulLeftCLM_apply hg]
  change L (polynomialOperator P normalizedPartialDeriv φ) = polyEval (polyNeg P) x *
      fourierTransformSchwartz φ x
  rw [h]
  congr 1
  have he : (MvPolynomial.eval (fun j => (x j : ℂ))).comp MvPolynomial.C =
      RingHom.id ℂ := by
    ext c
    simp
  simp [polyEval, polyNeg, he]

/-- DLMF 1.16.34: `𝓕(Pφ)(𝐱) = P(𝐃) 𝓕φ(𝐱)` on Schwartz space. -/
@[dlmf 1.16.E34]
theorem fourierTransformSchwartz_polyMul {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    fourierTransformSchwartz (polyMul P φ) =
        polynomialDifferentialOperator P (fourierTransformSchwartz φ) := by
  let X (j : Fin n) : Module.End ℂ 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
    (SchwartzMap.smulLeftCLM ℂ (fun x : EuclideanSpace ℝ (Fin n) => (x j : ℂ))).toLinearMap
  have hxg (j : Fin n) : (fun x : EuclideanSpace ℝ (Fin n) => (x j : ℂ)).HasTemperateGrowth := by
    have hi : (fun x : EuclideanSpace ℝ (Fin n) =>
        (inner ℝ x (EuclideanSpace.single j (1 : ℝ)) : ℂ)).HasTemperateGrowth := by fun_prop
    convert hi using 1
    ext y
    simp [EuclideanSpace.inner_single_right]
  have hX (j : Fin n) (ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
      fourierTransformSchwartz (X j ψ) = normalizedPartialDeriv j (fourierTransformSchwartz ψ) := by
    change _ = (-I) • (∂_{EuclideanSpace.single j (1 : ℝ)} (fourierTransformSchwartz ψ))
    rw [lineDeriv_fourierTransformSchwartz]
    have hg : (fun x : EuclideanSpace ℝ (Fin n) =>
        I * (inner ℝ x (EuclideanSpace.single j (1 : ℝ)) : ℂ)).HasTemperateGrowth := by fun_prop
    have he : SchwartzMap.smulLeftCLM ℂ
        (fun x : EuclideanSpace ℝ (Fin n) => I *
            (inner ℝ x (EuclideanSpace.single j (1 : ℝ)) : ℂ)) ψ =
        I • X j ψ := by
      ext x
      rw [SchwartzMap.smulLeftCLM_apply hg]
      change _ = I * (SchwartzMap.smulLeftCLM ℂ
        (fun x : EuclideanSpace ℝ (Fin n) => (x j : ℂ)) ψ) x
      rw [SchwartzMap.smulLeftCLM_apply (hxg j)]
      simp [EuclideanSpace.inner_single_right, smul_eq_mul, mul_assoc]
    rw [he, map_smul, smul_smul]
    simp
  have hpX : polynomialOperator P X φ = polyMul P φ := by
    ext x
    let L : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) →ₗ[ℂ] ℂ := (TemperedDistribution.delta x).toLinearMap
    have h := polynomialOperator_apply_eigenfunctional L X (fun j => (x j : ℂ)) (fun j ψ => by
      change (SchwartzMap.smulLeftCLM ℂ (fun x : EuclideanSpace ℝ (Fin n) => (x j : ℂ)) ψ) x = _
      rw [SchwartzMap.smulLeftCLM_apply (hxg j)]
      rfl) P φ
    have hpg := polyEval_hasTemperateGrowth P
    rw [polyMul, SchwartzMap.smulLeftCLM_apply hpg]
    exact h
  rw [← hpX]
  exact polynomialOperator_intertwine fourierTransformSchwartz.toLinearMap X
      normalizedPartialDeriv hX P φ

/-- DLMF 1.16.36: `⟨𝓕(P(𝐃)u), φ⟩ = ⟨P₋ 𝓕(u), φ⟩ = ⟨𝓕(u), P₋φ⟩` for a tempered
distribution `u`, `P₋(𝐱) = P(-𝐱)`, derivatives in the sense of distributions. -/
@[dlmf 1.16.E36]
theorem fourierTransformTempered_polynomialDifferentialOperator {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    fourierTransformTempered (temperedPolynomialDifferentialOperator P u) φ =
        temperedPolyMul (polyNeg P) (fourierTransformTempered u) φ ∧
      temperedPolyMul (polyNeg P) (fourierTransformTempered u) φ =
        fourierTransformTempered u (polyMul (polyNeg P) φ) := by
  let X (j : Fin n) : Module.End ℂ 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
    (SchwartzMap.smulLeftCLM ℂ (fun x : EuclideanSpace ℝ (Fin n) => -(x j : ℂ))).toLinearMap
  have hX (j : Fin n) (ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
      fourierTransformSchwartz (X j ψ) =
          (-normalizedPartialDeriv j) (fourierTransformSchwartz ψ) := by
    have hg := coordinate_hasTemperateGrowth j
    have he : X j ψ = -(SchwartzMap.smulLeftCLM ℂ
        (fun x : EuclideanSpace ℝ (Fin n) => (x j : ℂ)) ψ) := by
      change SchwartzMap.smulLeftCLM ℂ
        (fun x : EuclideanSpace ℝ (Fin n) => -(x j : ℂ)) ψ = _
      rw [SchwartzMap.smulLeftCLM_fun_neg hg]
      rfl
    rw [he, map_neg]
    exact congrArg Neg.neg (normalizedPartialDeriv_fourierTransformSchwartz j ψ).symm
  have hpoly : polynomialOperator P X φ = polyMul (polyNeg P) φ := by
    ext x
    have h := polynomialOperator_coordinateMul_apply (-1) P φ x
    have hg := polyEval_hasTemperateGrowth (polyNeg P)
    rw [polyMul, SchwartzMap.smulLeftCLM_apply hg]
    change polynomialOperator P X φ x = polyEval (polyNeg P) x * φ x
    have he : (MvPolynomial.eval (fun j => (x j : ℂ))).comp MvPolynomial.C =
        RingHom.id ℂ := by ext c; simp
    have heval : MvPolynomial.eval (fun j => -(x j : ℂ)) P = polyEval (polyNeg P) x := by
      simp [polyEval, polyNeg, he]
    simpa only [X, neg_one_mul, heval] using h
  have hi := polynomialOperator_intertwine fourierTransformSchwartz.toLinearMap X
      (fun j => -normalizedPartialDeriv j) hX P φ
  change fourierTransformSchwartz (polynomialOperator P X φ) =
    polynomialOperator P (fun j => -normalizedPartialDeriv j) (fourierTransformSchwartz φ) at hi
  constructor
  · change temperedPolynomialDifferentialOperator P u (fourierTransformSchwartz φ) =
      u (fourierTransformSchwartz (polyMul (polyNeg P) φ))
    rw [temperedPolynomialDifferentialOperator_apply, ← hi, hpoly]
  · rfl

/-- DLMF 1.16.37: `⟨𝓕(Pu), φ⟩ = ⟨P(𝐃) 𝓕(u), φ⟩` for a tempered distribution `u`. -/
@[dlmf 1.16.E37]
theorem fourierTransformTempered_polyMul {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    fourierTransformTempered (temperedPolyMul P u) =
      temperedPolynomialDifferentialOperator P (fourierTransformTempered u) := by
  let X (j : Fin n) : Module.End ℂ 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
    (SchwartzMap.smulLeftCLM ℂ (fun x : EuclideanSpace ℝ (Fin n) => (x j : ℂ))).toLinearMap
  have hX (j : Fin n) (ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
      fourierTransformSchwartz ((-normalizedPartialDeriv j) ψ) =
          X j (fourierTransformSchwartz ψ) := by
    ext x
    change fourierTransformSchwartz (-(normalizedPartialDeriv j ψ)) x =
      (SchwartzMap.smulLeftCLM ℂ (fun x : EuclideanSpace ℝ (Fin n) => (x j : ℂ))
        (fourierTransformSchwartz ψ)) x
    rw [map_neg, neg_apply, fourierTransformSchwartz_normalizedPartialDeriv,
      SchwartzMap.smulLeftCLM_apply (coordinate_hasTemperateGrowth j)]
    simp [smul_eq_mul]
  have hpoly (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) : polynomialOperator P X φ = polyMul P φ := by
    ext x
    have h := polynomialOperator_coordinateMul_apply 1 P φ x
    rw [polyMul, SchwartzMap.smulLeftCLM_apply (polyEval_hasTemperateGrowth P)]
    simpa only [X, one_mul, polyEval, smul_eq_mul] using h
  ext φ
  change u (polyMul P (fourierTransformSchwartz φ)) =
    temperedPolynomialDifferentialOperator P (fourierTransformTempered u) φ
  rw [temperedPolynomialDifferentialOperator_apply]
  change u (polyMul P (fourierTransformSchwartz φ)) =
    u (fourierTransformSchwartz (polynomialOperator P (fun j => -normalizedPartialDeriv j) φ))
  have hi := polynomialOperator_intertwine fourierTransformSchwartz.toLinearMap
      (fun j => -normalizedPartialDeriv j) X hX P φ
  change fourierTransformSchwartz (polynomialOperator P (fun j => -normalizedPartialDeriv j) φ) =
    polynomialOperator P X (fourierTransformSchwartz φ) at hi
  rw [hi, hpoly]

/-! ## §1.16(viii): Fourier transforms of special distributions -/

/-- DLMF 1.16.38–1.16.40: `⟨𝓕(δ), φ⟩ = (2π)^{-1/2} ∫ φ(t) dt = (2π)^{-1/2} ⟨1, φ⟩`, that is
`𝓕(δ) = 1/√(2π)` (1.16.39), conventionally `∫ δ(t) e^{ixt} dt = 1` (1.16.40). -/
@[dlmf 1.16.E38, dlmf 1.16.E39, dlmf 1.16.E40]
theorem fourierTransformTempered_delta :
    fourierTransformTempered (TemperedDistribution.delta (0 : ℝ)) =
      (((2 * Real.pi) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) • volume.toTemperedDistribution := by
  ext φ
  change fourierTransformSchwartz φ 0 = _
  rw [fourierTransformSchwartz_apply]
  simp

/-- DLMF 1.16.41–1.16.43: `⟨𝓕(1), φ⟩ = √(2π) φ(0)`, that is `𝓕(1) = √(2π) δ` (1.16.42),
conventionally `(2π)^{-1} ∫ e^{ixt} dt = δ(x)` (1.16.43). -/
@[dlmf 1.16.E41, dlmf 1.16.E42, dlmf 1.16.E43]
theorem fourierTransformTempered_one :
    fourierTransformTempered (volume.toTemperedDistribution : 𝓢'(ℝ, ℂ)) =
      (Real.sqrt (2 * Real.pi) : ℂ) • TemperedDistribution.delta 0 := by
  ext φ
  have hF : ∫ t : ℝ, (𝓕⁻ φ) t = φ 0 := by
    have h := congrArg (fun ψ : 𝓢(ℝ, ℂ) => ψ 0)
      (FourierTransform.fourier_fourierInv_eq (F := 𝓢(ℝ, ℂ)) φ)
    change (𝓕 (𝓕⁻ φ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ)) 0 = φ 0 at h
    rw [SchwartzMap.fourier_coe, Real.fourier_eq] at h
    simpa using h
  change (∫ t : ℝ, fourierTransformSchwartz φ t) =
    (Real.sqrt (2 * Real.pi) : ℂ) * φ 0
  simp only [fourierTransformSchwartz, smul_apply, ContinuousLinearMap.comp_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    FourierTransform.fourierInvCLM_apply, scaleEquiv,
    ContinuousLinearEquiv.equivOfInverse_apply, smul_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, Module.finrank_self, Nat.cast_one]
  rw [integral_const_mul, Measure.integral_comp_mul_left, hF]
  simp only [inv_inv, abs_of_pos (by positivity : 0 < 2 * Real.pi), Complex.real_smul]
  have hc : (2 * Real.pi) ^ (-(1 : ℝ) / 2) * (2 * Real.pi) =
      Real.sqrt (2 * Real.pi) := by
    rw [show -(1 : ℝ) / 2 = -(1 / 2) by ring, Real.rpow_neg (by positivity),
      ← Real.sqrt_eq_rpow]
    have hs := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
    have hn : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
    field_simp
    nlinarith
  rw [← mul_assoc, ← ofReal_mul, hc]

/-- The tempered form of DLMF 1.16.45: `sign' = 2δ`. -/
@[dlmf 1.16.E45]
theorem deriv_signTempered :
    TemperedDistribution.derivCLM ℂ signTempered = (2 : ℂ) • TemperedDistribution.delta 0 := by
  have hmeas : Measurable (fun x : ℝ => (Real.sign x : ℂ)) := by
    have hs : Measurable Real.sign := by
      unfold Real.sign
      exact (measurable_const.ite measurableSet_Iio
        (measurable_const.ite measurableSet_Ioi measurable_const))
    exact Complex.continuous_ofReal.measurable.comp hs
  have hmem : MemLp (fun x : ℝ => (Real.sign x : ℂ)) ⊤ volume :=
    memLp_top_of_bound hmeas.aestronglyMeasurable 1 (Eventually.of_forall fun x => by
      rcases Real.sign_apply_eq x with h | h | h <;> rw [h] <;> norm_num)
  have happ (ψ : 𝓢(ℝ, ℂ)) : signTempered ψ = ∫ x, ψ x * (Real.sign x : ℂ) := by
    simpa only [signTempered] using boundedTempered_apply hmem ψ
  ext φ
  rw [TemperedDistribution.derivCLM_apply_apply, happ]
  simp only [neg_apply, SchwartzMap.derivCLM_apply,
    smul_apply, TemperedDistribution.delta_apply, smul_eq_mul]
  have hderiv : Integrable (deriv ⇑φ) := by
    have h := (SchwartzMap.derivCLM ℂ ℂ φ).integrable (μ := (volume : Measure ℝ))
    exact h.congr (Eventually.of_forall fun x => SchwartzMap.derivCLM_apply ℂ φ x)
  have hIoi : ∫ x in Ioi (0 : ℝ), deriv ⇑φ x = -φ 0 := by
    simpa only [zero_sub] using integral_Ioi_of_hasDerivAt_of_tendsto
      φ.continuous.continuousWithinAt (fun x _ => φ.differentiableAt.hasDerivAt)
      hderiv.integrableOn (φ.tendsto_cocompact.mono_left atTop_le_cocompact)
  have hfull : ∫ x, deriv ⇑φ x = 0 :=
    integral_eq_zero_of_hasDerivAt_of_integrable
      (fun x => φ.differentiableAt.hasDerivAt) hderiv φ.integrable
  have he : (fun x : ℝ => -deriv ⇑φ x * (Real.sign x : ℂ)) =ᵐ[volume]
      fun x => -(2 : ℂ) * ((Ioi 0).indicator (deriv ⇑φ) x) + deriv ⇑φ x := by
    filter_upwards [(compl_mem_ae_iff.mpr (measure_singleton 0) : ({0}ᶜ : Set ℝ) ∈ ae volume)]
      with x hx
    have hx0 : x ≠ 0 := hx
    rcases hx0.lt_or_gt with hn | hp
    · have hxmem : x ∉ Ioi (0 : ℝ) := not_lt.mpr hn.le
      simp [Real.sign_of_neg hn, hxmem]
    · have hxmem : x ∈ Ioi (0 : ℝ) := hp
      simp [Real.sign_of_pos hp, hxmem]
      ring
  rw [integral_congr_ae he, integral_add
      ((hderiv.indicator measurableSet_Ioi).const_mul _) hderiv,
    integral_const_mul, integral_indicator measurableSet_Ioi, hIoi, hfull]
  ring

/-- DLMF 1.16.46: `𝓕(sign') = 𝓕(2H') = 2𝓕(δ) = √(2/π)`. -/
@[dlmf 1.16.E46]
theorem fourierTransformTempered_deriv_sign :
    fourierTransformTempered (TemperedDistribution.derivCLM ℂ signTempered) =
      (Real.sqrt (2 / Real.pi) : ℂ) • volume.toTemperedDistribution := by
  rw [deriv_signTempered, map_smul, fourierTransformTempered_delta, smul_smul]
  congr 1
  have hπ : 0 < Real.pi := Real.pi_pos
  have h : (2 : ℝ) * (2 * Real.pi) ^ (-(1 : ℝ) / 2) = Real.sqrt (2 / Real.pi) := by
    rw [show -(1 : ℝ) / 2 = -(1 / 2) by ring, Real.rpow_neg (by positivity),
      ← Real.sqrt_eq_rpow, Real.sqrt_mul' _ hπ.le, Real.sqrt_div' _ hπ.le]
    have h2 : Real.sqrt 2 ≠ 0 := by positivity
    have hp : Real.sqrt Real.pi ≠ 0 := by positivity
    have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    field_simp
    linear_combination -hs
  rw [← h]
  push_cast
  ring

/-- In DLMF's normalization, differentiating a Schwartz Fourier transform corresponds to
multiplication of the original function by `I * x`. This specializes Mathlib's
`SchwartzMap.lineDerivOp_fourierInv_eq` and accounts for the frequency rescaling. -/
lemma fourierTransformSchwartz_deriv (φ : 𝓢(ℝ, ℂ)) :
    SchwartzMap.derivCLM ℂ ℂ (fourierTransformSchwartz φ) =
      fourierTransformSchwartz (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => I * x) φ) := by
  have hd : SchwartzMap.derivCLM ℂ ℂ (fourierTransformSchwartz φ) =
      ∂_{(1 : ℝ)} (fourierTransformSchwartz φ) := by ext x; rfl
  rw [hd]
  simpa only [Real.inner_apply, mul_one] using lineDeriv_fourierTransformSchwartz φ (1 : ℝ)

/-- The one-variable case of DLMF 1.16.36 with `P(𝐃) = d/dx`, `P₋(x) = -ix`:
`𝓕(u') = (x/i) 𝓕(u)` for a tempered distribution `u` on the line. -/
theorem fourierTransformTempered_deriv (u : 𝓢'(ℝ, ℂ)) :
    fourierTransformTempered (TemperedDistribution.derivCLM ℂ u) =
      TemperedDistribution.smulLeftCLM ℂ (fun x : ℝ => -I * x) (fourierTransformTempered u) := by
  ext φ
  change u (-SchwartzMap.derivCLM ℂ ℂ (fourierTransformSchwartz φ)) =
    u (fourierTransformSchwartz (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => -I * x) φ))
  rw [fourierTransformSchwartz_deriv]
  have hg : (fun x : ℝ => I * (x : ℂ)).HasTemperateGrowth := by fun_prop
  have he : (fun x : ℝ => -I * (x : ℂ)) = fun x : ℝ => -(I * (x : ℂ)) := by
    funext x
    ring
  rw [he, SchwartzMap.smulLeftCLM_fun_neg hg]
  simp only [neg_apply, map_neg]

/-- DLMF 1.16.47: `𝓕(sign') = (x/i) 𝓕(sign)`. -/
@[dlmf 1.16.E47]
theorem fourierTransformTempered_deriv_sign' :
    fourierTransformTempered (TemperedDistribution.derivCLM ℂ signTempered) =
      TemperedDistribution.smulLeftCLM ℂ (fun x : ℝ => -I * x)
        (fourierTransformTempered signTempered) :=
  fourierTransformTempered_deriv signTempered

/-- DLMF 1.16.48–1.16.49: `𝓕(sign) = √(2/π) i/x`, that is
`⟨𝓕(sign), φ⟩ = i √(2/π) ⨍ φ(x)/x dx` (Cauchy principal value, the limit of the integrals over
`|x| > ε` as `ε → 0+`). -/
@[dlmf 1.16.E48, dlmf 1.16.E49]
theorem fourierTransformTempered_sign (φ : 𝓢(ℝ, ℂ)) :
    Tendsto (fun ε : ℝ => I * Real.sqrt (2 / Real.pi) * ∫ x in {x : ℝ | ε < |x|}, φ x / x)
      (𝓝[>] 0) (𝓝 (fourierTransformTempered signTempered φ)) := by
  have hmeas : Measurable (fun x : ℝ => (Real.sign x : ℂ)) := by
    have hs : Measurable Real.sign := by
      unfold Real.sign
      exact measurable_const.ite measurableSet_Iio
        (measurable_const.ite measurableSet_Ioi measurable_const)
    exact Complex.continuous_ofReal.measurable.comp hs
  have hmem : MemLp (fun x : ℝ => (Real.sign x : ℂ)) ⊤ volume :=
    memLp_top_of_bound hmeas.aestronglyMeasurable 1 (Eventually.of_forall fun x => by
      rcases Real.sign_apply_eq x with h | h | h <;> rw [h] <;> norm_num)
  have happ (ψ : 𝓢(ℝ, ℂ)) : signTempered ψ = ∫ x, ψ x * (Real.sign x : ℂ) := by
    simpa only [signTempered] using boundedTempered_apply hmem ψ
  have hsign (c : ℝ) (hc : 0 < c) (x : ℝ) : Real.sign (c * x) = Real.sign x := by
    rcases lt_trichotomy x 0 with hx | rfl | hx
    · rw [Real.sign_of_neg (mul_neg_of_pos_of_neg hc hx), Real.sign_of_neg hx]
    · simp
    · rw [Real.sign_of_pos (mul_pos hc hx), Real.sign_of_pos hx]
  have he : fourierTransformTempered signTempered φ =
      (((2 * Real.pi) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) * (2 * Real.pi) *
        ∫ x, (Real.sign x : ℂ) * (𝓕⁻ φ) x := by
    change signTempered (fourierTransformSchwartz φ) = _
    rw [happ]
    simp only [fourierTransformSchwartz, smul_apply, ContinuousLinearMap.comp_apply,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      FourierTransform.fourierInvCLM_apply, scaleEquiv,
      ContinuousLinearEquiv.equivOfInverse_apply, smul_apply, ContinuousLinearMap.id_apply,
      smul_eq_mul, Module.finrank_self, Nat.cast_one]
    have hi : (∫ x : ℝ, (((2 * Real.pi) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
        (𝓕⁻ φ : 𝓢(ℝ, ℂ)) ((2 * Real.pi)⁻¹ * x) * (Real.sign x : ℂ)) =
        (((2 * Real.pi) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
          ∫ x : ℝ, (Real.sign ((2 * Real.pi)⁻¹ * x) : ℂ) *
            (𝓕⁻ φ : 𝓢(ℝ, ℂ)) ((2 * Real.pi)⁻¹ * x) := by
      rw [← integral_const_mul]
      congr 1
      funext x
      rw [hsign _ (by positivity)]
      ring
    rw [hi, Measure.integral_comp_mul_left
      (fun x : ℝ => (Real.sign x : ℂ) * (𝓕⁻ φ : 𝓢(ℝ, ℂ)) x) ((2 * Real.pi)⁻¹)]
    simp only [inv_inv, abs_of_pos (by positivity : 0 < 2 * Real.pi), Complex.real_smul]
    push_cast
    ring
  have hFi : Integrable (𝓕⁻ (φ : ℝ → ℂ)) := by
    rw [← SchwartzMap.fourierInv_coe]
    exact (𝓕⁻ φ : 𝓢(ℝ, ℂ)).integrable
  have hF := Real.integral_sign_mul_fourierInv_eq_integral_symmetric_div
    φ.continuous (φ.differentiable 0) φ.integrable hFi
  rw [← SchwartzMap.fourierInv_coe] at hF
  have hc :
      (((2 * Real.pi) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) * (2 * Real.pi) * (I / Real.pi) =
        I * Real.sqrt (2 / Real.pi) := by
    have hr : (2 * Real.pi) ^ (-(1 : ℝ) / 2) * (2 * Real.pi) / Real.pi =
        Real.sqrt (2 / Real.pi) := by
      rw [show -(1 : ℝ) / 2 = -(1 / 2) by ring, Real.rpow_neg (by positivity),
        ← Real.sqrt_eq_rpow]
      have he : Real.sqrt (2 / Real.pi) * Real.sqrt (2 * Real.pi) = 2 := by
        rw [← Real.sqrt_mul (by positivity)]
        have hh : 2 / Real.pi * (2 * Real.pi) = 4 := by field_simp; ring
        rw [hh]
        exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
      field_simp
      nlinarith [he]
    calc
      _ = I * (((2 * Real.pi) ^ (-(1 : ℝ) / 2) * (2 * Real.pi) / Real.pi : ℝ) : ℂ) := by
        push_cast
        ring
      _ = _ := by rw [hr]
  rw [he, hF, ← mul_assoc, hc]
  exact (tendsto_integral_cut_div_eq_integral_symmetric_div φ.continuous
    (φ.differentiable 0) φ.integrable).const_mul _

/-- DLMF 1.16.50–1.16.51: `𝓕(H) = √(π/2) (δ + i/(πx))`, that is
`⟨𝓕(H), φ⟩ = √(π/2) φ(0) + (i/√(2π)) ⨍ φ(x)/x dx` (principal value). -/
@[dlmf 1.16.E50, dlmf 1.16.E51]
theorem fourierTransformTempered_heaviside (φ : 𝓢(ℝ, ℂ)) :
    Tendsto (fun ε : ℝ => Real.sqrt (Real.pi / 2) * φ 0 +
        I / Real.sqrt (2 * Real.pi) * ∫ x in {x : ℝ | ε < |x|}, φ x / x)
      (𝓝[>] 0) (𝓝 (fourierTransformTempered heavisideTempered φ)) := by
  have hmeas : Measurable (fun x : ℝ => (Real.sign x : ℂ)) := by
    have hs : Measurable Real.sign := by
      unfold Real.sign
      exact measurable_const.ite measurableSet_Iio
        (measurable_const.ite measurableSet_Ioi measurable_const)
    exact Complex.continuous_ofReal.measurable.comp hs
  have hb : ∀ᵐ x : ℝ ∂volume, ‖(Real.sign x : ℂ)‖ ≤ 1 := Eventually.of_forall fun x => by
    rcases Real.sign_apply_eq x with h | h | h <;> rw [h] <;> norm_num
  have hmem : MemLp (fun x : ℝ => (Real.sign x : ℂ)) ⊤ volume :=
    memLp_top_of_bound hmeas.aestronglyMeasurable 1 hb
  have hHmeas : Measurable (fun x : ℝ => (heaviside x : ℂ)) := by
    have hs : Measurable heaviside := by
      unfold heaviside
      exact measurable_const.ite measurableSet_Ioi measurable_const
    exact Complex.continuous_ofReal.measurable.comp hs
  have hHmem : MemLp (fun x : ℝ => (heaviside x : ℂ)) ⊤ volume :=
    memLp_top_of_bound hHmeas.aestronglyMeasurable 1 (Eventually.of_forall fun x => by
      simp only [heaviside]
      split_ifs <;> norm_num)
  have hH (ψ : 𝓢(ℝ, ℂ)) : heavisideTempered ψ = (signTempered ψ + ∫ x, ψ x) / 2 := by
    rw [heavisideTempered, boundedTempered_apply hHmem, signTempered,
      boundedTempered_apply hmem, ← integral_add (ψ.integrable.mul_bdd
        hmeas.aestronglyMeasurable hb) ψ.integrable, ← integral_div]
    apply integral_congr_ae
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with x hx
    have hs : (Real.sign x : ℂ) = 2 * (heaviside x : ℂ) - 1 := by
      exact_mod_cast sign_eq_two_mul_heaviside_sub_one hx
    rw [hs]
    ring
  have hone : (∫ t : ℝ, fourierTransformSchwartz φ t) =
      (Real.sqrt (2 * Real.pi) : ℂ) * φ 0 := by
    have h := congrArg (fun T : 𝓢'(ℝ, ℂ) => T φ) fourierTransformTempered_one
    exact h
  have hvalue : fourierTransformTempered heavisideTempered φ =
      (fourierTransformTempered signTempered φ + (Real.sqrt (2 * Real.pi) : ℂ) * φ 0) / 2 := by
    change heavisideTempered (fourierTransformSchwartz φ) = _
    rw [hH, hone]
    rfl
  have hc : (Real.sqrt (2 / Real.pi) : ℂ) / 2 =
      1 / (Real.sqrt (2 * Real.pi) : ℂ) := by
    have he : Real.sqrt (2 / Real.pi) * Real.sqrt (2 * Real.pi) = 2 := by
      rw [← Real.sqrt_mul (by positivity)]
      have hh : 2 / Real.pi * (2 * Real.pi) = 4 := by field_simp; ring
      rw [hh]
      exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
    have hr : Real.sqrt (2 / Real.pi) / 2 = 1 / Real.sqrt (2 * Real.pi) := by
      apply (div_eq_div_iff (by norm_num) (Real.sqrt_pos.mpr (by positivity)).ne').mpr
      nlinarith [he]
    exact_mod_cast hr
  have hd : (Real.sqrt (2 * Real.pi) : ℂ) / 2 =
      (Real.sqrt (Real.pi / 2) : ℂ) := by
    have hr : Real.sqrt (2 * Real.pi) / 2 = Real.sqrt (Real.pi / 2) := by
      apply Eq.symm
      apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
      have hs := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
      nlinarith [hs]
    exact_mod_cast hr
  have ht := ((fourierTransformTempered_sign φ).add_const
    ((Real.sqrt (2 * Real.pi) : ℂ) * φ 0)).div_const (2 : ℂ)
  rw [← hvalue] at ht
  convert ht using 1
  funext ε
  rw [add_div,
    ← div_mul_eq_mul_div (I * (Real.sqrt (2 / Real.pi) : ℂ)) (2 : ℂ),
    mul_div_assoc I, hc,
    ← div_mul_eq_mul_div (Real.sqrt (2 * Real.pi) : ℂ) (2 : ℂ), hd]
  ring

end DLMF.AlgebraicAnalytic
