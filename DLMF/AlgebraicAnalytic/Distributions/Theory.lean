/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Distributions.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import DLMFMathlib.Analysis.Distribution.IteratedLineDeriv
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Distributions (DLMF §1.16)

Theorems of DLMF §1.16 that are not already in Mathlib (the upstream pointers are in
`DLMF.AlgebraicAnalytic.Distributions.MathlibCoverage`).

## Main results

* `distribIterDeriv_apply` (1.16.9) and `distribIterDeriv_delta_apply` (1.16.12).
* `smoothMul_apply` (1.16.6), `distrib_tendsto_iff` (1.16.7).
* `deriv_heaviside` (1.16.15), `deriv_heaviside_shift` (1.16.16), `stieltjes_eq_deriv`
  (1.16.9_5), `delta_not_regular` (§1.16(iii)).
* `iterDeriv_piecewise`: the jump formula (1.16.17–1.16.18).
* `deriv_xPlusRpow` (1.16.20), `xPlusDistrib_eq_iterDeriv` (1.16.21),
  `factorial_smul_xPlusDistrib` (1.16.23).
* `sign_eq_two_mul_heaviside_sub_one` (1.16.44), `deriv_sign` (1.16.45).
* `dlmfFourierSchwartz_apply` (1.16.29), `dlmfFourierSchwartz_polyDiffOp`,
  `dlmfFourierSchwartz_polyMul` (1.16.33–1.16.34), `dlmfFourierTempered_polyDiffOp`,
  `dlmfFourierTempered_polyMul` (1.16.36–1.16.37).
* `dlmfFourierTempered_delta`, `dlmfFourierTempered_one`, `dlmfFourierTempered_deriv_sign`,
  `dlmfFourierTempered_sign`, `dlmfFourierTempered_heaviside`: the transforms of `δ`, `1`,
  `sign'`, `sign` and `H` (1.16.38–1.16.51).

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

/-- The derivative of a test function on the line as a function: `∂_{1} φ = φ'`. -/
private lemma coe_lineDerivOp_one (φ : 𝓓(Ω, ℝ)) : ⇑(∂_{(1 : ℝ)} φ : 𝓓(Ω, ℝ)) = deriv ⇑φ := by
  ext x
  rw [TestFunction.lineDerivOp_eq_lineDerivCLM ℝ, TestFunction.lineDerivCLM_apply_of_le le_top,
    (φ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv]
  rfl

/-- The `k`-fold derivative of a test function on the line: `(∂_{1})^[k] φ = φ^{(k)}`. -/
private lemma coe_iterate_lineDerivOp_one (k : ℕ) (φ : 𝓓(Ω, ℝ)) :
    ⇑((fun ψ : 𝓓(Ω, ℝ) => ∂_{(1 : ℝ)} ψ)^[k] φ) = iteratedDeriv k ⇑φ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', coe_lineDerivOp_one, ih, iteratedDeriv_succ]

/-- DLMF 1.16.9: `⟨Λ^{(k)}, φ⟩ = (-1)^k ⟨Λ, φ^{(k)}⟩`, with `φ^{(k)}` the `k`-fold
derivative of the test function (as an element of `𝓓(Ω, ℝ)`; its values are
`iteratedDeriv k φ`, `coe_iterate_lineDerivOp_one`). The case `k = 1` is 1.16.8,
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
  rw [distribIterDeriv_apply, Distribution.delta_apply, coe_iterate_lineDerivOp_one,
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
  simp only [FunLike.coe_neg, Pi.neg_apply, coe_lineDerivOp_one, smul_eq_mul, neg_mul,
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
  simp only [FunLike.coe_neg, Pi.neg_apply, coe_lineDerivOp_one, smul_eq_mul, neg_mul,
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
    LineDeriv.lineDerivOp_smul, deriv_heaviside_shift, lineDerivOp_lineDistrib_const, neg_zero, add_zero]

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
  sorry

/-- DLMF 1.16.9_5: `μ_α = Dα`: the distributional derivative of a Stieltjes function `α`
(nondecreasing, right continuous, hence locally integrable) is its Lebesgue–Stieltjes
measure (1.16.3_5). With `α = H(· - x₀)` this is 1.16.16 (`deriv_heaviside_shift`). -/
@[dlmf 1.16.E9_5]
theorem stieltjes_eq_deriv (α : StieltjesFunction ℝ) :
    stieltjesDistribution ⊤ α = ∂_{(1 : ℝ)} (lineDistrib ⇑α) := by
  sorry

/-- §1.16(ii): if the Lebesgue–Stieltjes measure of `α` is absolutely continuous with density
`w` (`dα = w dx`), then `Dα = Λ_w`. -/
@[dlmf 1.16.ii]
theorem deriv_stieltjes_of_density (α : StieltjesFunction ℝ) {w : ℝ → ℝ}
    (hw : α.measure = volume.withDensity fun x => ENNReal.ofReal (w x))
    (hw0 : ∀ x, 0 ≤ w x) (hwi : LocallyIntegrable w volume) :
    ∂_{(1 : ℝ)} (lineDistrib ⇑α) = lineDistrib w := by
  sorry

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
  simpa [Distribution.delta_apply, φ, hg0] using hh

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
  sorry

/-- DLMF 1.16.20: `D x₊^α = α x₊^{α-1}` for `α > 0`, as distributions on the line. -/
@[dlmf 1.16.E20]
theorem deriv_xPlusRpow {α : ℝ} (hα : 0 < α) :
    ∂_{(1 : ℝ)} (lineDistrib (xPlusRpow α)) = α • lineDistrib (xPlusRpow (α - 1)) := by
  sorry

/-- DLMF 1.16.21: for `α < -1` not an integer, `x₊^α = D^n x₊^{α+n} / (α+1)_n` for every
integer `n` with `α + n > -1` (the definition `xPlusDistrib` uses the least such `n`). -/
@[dlmf 1.16.E21]
theorem xPlusDistrib_eq_iterDeriv {α : ℝ} (hα : α < -1) (hαZ : ∀ m : ℤ, α ≠ m) (n : ℕ)
    (hn : -1 < α + n) :
    xPlusDistrib α = (ascPochhammer ℝ n).eval (α + 1) ⁻¹ •
      distribIterDeriv n (lineDistrib (xPlusRpow (α + n))) := by
  sorry

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
theorem dlmfFourierSchwartz_apply (φ : 𝓢(E, ℂ)) (x : E) :
    dlmfFourierSchwartz φ x =
      (((2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) : ℝ) : ℂ) *
        ∫ t, φ t * exp (I * (inner ℝ x t : ℝ)) := by
  simp only [dlmfFourierSchwartz, smul_apply, ContinuousLinearMap.comp_apply,
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
lemma polyOp_apply_eigenfunctional {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (L : V →ₗ[ℂ] ℂ) (D : Fin n → Module.End ℂ V) (g : Fin n → ℂ)
    (hL : ∀ j φ, L (D j φ) = g j * L φ) (P : MvPolynomial (Fin n) ℂ) (φ : V) :
    L (polyOp P D φ) = MvPolynomial.eval g P * L φ := by
  have hp (j : Fin n) (k : ℕ) (φ : V) : L ((D j ^ k) φ) = g j ^ k * L φ := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, hL, pow_succ]
      rw [ih]
      ring
  have hl (α : Fin n → ℕ) (l : List (Fin n)) (φ : V) :
      L ((l.map (fun j => D j ^ α j)).prod φ) =
        (l.map (fun j => g j ^ α j)).prod * L φ := by
    induction l generalizing φ with
    | nil => simp
    | cons j l ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      rw [hp, ih]
      ring
  have hmono (α : Fin n →₀ ℕ) :
      L ((List.ofFn (fun j => D j ^ α j)).prod φ) = (∏ j, g j ^ α j) * L φ := by
    simpa only [List.map_ofFn, Function.comp_def, List.prod_ofFn, id_eq] using
      hl α (List.ofFn id) φ
  rw [polyOp, LinearMap.sum_apply, map_sum, MvPolynomial.eval_eq', Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro α hα
  rw [LinearMap.smul_apply, map_smul, smul_eq_mul, hmono]
  ring

section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
/-- The DLMF Fourier transform sends a directional derivative to multiplication by
`-I * inner x v`. This specializes Mathlib’s `SchwartzMap.fourierInv_lineDerivOp_eq`. -/
lemma dlmfFourierSchwartz_lineDeriv (φ : 𝓢(E, ℂ)) (v : E) :
    dlmfFourierSchwartz (∂_{v} φ) =
      SchwartzMap.smulLeftCLM ℂ (fun x : E => -I * (inner ℝ x v : ℂ))
        (dlmfFourierSchwartz φ) := by
  have hg : (fun x : E => -I * (inner ℝ x v : ℂ)).HasTemperateGrowth := by fun_prop
  have hi : (fun x : E => inner ℝ x v).HasTemperateGrowth := by fun_prop
  simp only [dlmfFourierSchwartz, smul_apply, ContinuousLinearMap.comp_apply,
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
lemma dlmfFourierSchwartz_dlmfD {n : ℕ} (j : Fin n)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (x : EuclideanSpace ℝ (Fin n)) :
    dlmfFourierSchwartz (dlmfD j φ) x = -(x j : ℂ) * dlmfFourierSchwartz φ x := by
  have hg : (fun x : EuclideanSpace ℝ (Fin n) =>
      -I * (inner ℝ x (EuclideanSpace.single j (1 : ℝ)) : ℂ)).HasTemperateGrowth := by fun_prop
  simp only [dlmfD, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
    LineDeriv.lineDerivOpCLM_apply, map_smul, smul_apply]
  rw [dlmfFourierSchwartz_lineDeriv]
  rw [SchwartzMap.smulLeftCLM_apply hg]
  simp only [smul_eq_mul, EuclideanSpace.inner_single_right, one_mul]
  simp only [starRingEnd_apply, star_trivial]
  linear_combination ((x j : ℂ) * dlmfFourierSchwartz φ x) * I_sq


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
in those families, preserving the fixed order in `polyOp`. -/
lemma polyOp_intertwine {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (L : V →ₗ[ℂ] W) (D : Fin n → Module.End ℂ V) (T : Fin n → Module.End ℂ W)
    (hL : ∀ j φ, L (D j φ) = T j (L φ)) (P : MvPolynomial (Fin n) ℂ) (φ : V) :
    L (polyOp P D φ) = polyOp P T (L φ) := by
  have hp (j : Fin n) (k : ℕ) (φ : V) : L ((D j ^ k) φ) = (T j ^ k) (L φ) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, hL, ih, pow_succ', Module.End.mul_apply]
  have hl (α : Fin n → ℕ) (l : List (Fin n)) (φ : V) :
      L ((l.map (fun j => D j ^ α j)).prod φ) =
        (l.map (fun j => T j ^ α j)).prod (L φ) := by
    induction l generalizing φ with
    | nil => simp
    | cons j l ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      rw [hp, ih]
  have hmono (α : Fin n →₀ ℕ) :
      L ((List.ofFn (fun j => D j ^ α j)).prod φ) =
        (List.ofFn (fun j => T j ^ α j)).prod (L φ) := by
    simpa only [List.map_ofFn, Function.comp_def, id_eq] using hl α (List.ofFn id) φ
  simp only [polyOp, LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul, hmono]


section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
/-- A directional derivative of the DLMF Fourier transform corresponds to multiplying the
original Schwartz function by `I * inner x v`, including DLMF’s frequency normalization. -/
lemma lineDeriv_dlmfFourierSchwartz (φ : 𝓢(E, ℂ)) (v : E) :
    ∂_{v} (dlmfFourierSchwartz φ) =
      dlmfFourierSchwartz (SchwartzMap.smulLeftCLM ℂ
        (fun x : E => I * (inner ℝ x v : ℂ)) φ) := by
  simp only [dlmfFourierSchwartz, smul_apply, ContinuousLinearMap.comp_apply,
    FourierTransform.fourierInvCLM_apply]
  rw [LineDeriv.lineDerivOp_smul, SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv,
    SchwartzMap.lineDerivOp_fourierInv_eq]
  congr 3
  ext x
  have h₁ : (fun y : E => inner ℝ y ((scaleEquiv (2 * Real.pi)⁻¹ (by positivity)) v)).HasTemperateGrowth := by fun_prop
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
lemma polyOp_pairing {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (D : Fin n → Module.End ℂ V)
    (T : Fin n → Module.End ℂ W) (hT : ∀ i j, Commute (T i) (T j))
    (hB : ∀ j v w, B (D j v) w = B v (T j w)) (P : MvPolynomial (Fin n) ℂ)
    (v : V) (w : W) : B (polyOp P D v) w = B v (polyOp P T w) := by
  have hp (j : Fin n) (k : ℕ) (v : V) (w : W) :
      B ((D j ^ k) v) w = B v ((T j ^ k) w) := by
    induction k generalizing v with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, ih, hB, pow_succ', Module.End.mul_apply]
  have hl (α : Fin n → ℕ) (l : List (Fin n)) (v : V) (w : W) :
      B ((l.map (fun j => D j ^ α j)).prod v) w =
        B v ((l.map (fun j => T j ^ α j)).prod w) := by
    induction l generalizing v w with
    | nil => simp
    | cons j l ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      rw [hp, ih]
      have hc : Commute (T j ^ α j) (l.map (fun k => T k ^ α k)).prod := by
        apply Commute.list_prod_right
        intro t ht
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht
        exact (hT j k).pow_pow _ _
      exact congrArg (fun A : Module.End ℂ W => B v (A w)) hc.eq.symm
  have hmono (α : Fin n →₀ ℕ) :
      B ((List.ofFn (fun j => D j ^ α j)).prod v) w =
        B v ((List.ofFn (fun j => T j ^ α j)).prod w) := by
    simpa only [List.map_ofFn, Function.comp_def, id_eq] using hl α (List.ofFn id) v w
  simp only [polyOp, LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul,
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
lemma dlmfD_commute {n : ℕ} (i j : Fin n) : Commute (dlmfD i) (dlmfD j) := by
  ext φ
  simp only [Module.End.mul_apply, dlmfD, LinearMap.smul_apply,
    ContinuousLinearMap.coe_coe, LineDeriv.lineDerivOpCLM_apply,
    LineDeriv.lineDerivOp_smul]
  rw [schwartz_lineDeriv_comm]

/-- Applying a polynomial differential operator to a tempered distribution transfers the
operators to the test function with a minus sign on each coordinate derivative. -/
lemma temperedPolyDiffOp_apply {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    temperedPolyDiffOp P u φ = u (polyOp P (fun j => -dlmfD j) φ) := by
  let B : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) →ₗ[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun v => v.toLinearMap
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hB (j : Fin n) (v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
      (ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
      B (temperedD j v) ψ = B v ((-dlmfD j) ψ) := by
    change (-I) * v (-∂_{EuclideanSpace.single j (1 : ℝ)} ψ) =
      v (-((-I) • ∂_{EuclideanSpace.single j (1 : ℝ)} ψ))
    simp only [map_neg, map_smul, smul_eq_mul]
    ring
  exact polyOp_pairing B temperedD (fun j => -dlmfD j)
    (fun i j => by
      change (-dlmfD i) * (-dlmfD j) = (-dlmfD j) * (-dlmfD i)
      simpa only [neg_mul_neg] using (dlmfD_commute i j).eq) hB P u φ
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
lemma polyOp_coordinateMul_apply {n : ℕ} (c : ℂ) (P : MvPolynomial (Fin n) ℂ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (x : EuclideanSpace ℝ (Fin n)) :
    polyOp P (fun j => (SchwartzMap.smulLeftCLM ℂ
      (fun y : EuclideanSpace ℝ (Fin n) => c * (y j : ℂ))).toLinearMap) φ x =
      MvPolynomial.eval (fun j => c * (x j : ℂ)) P * φ x := by
  exact polyOp_apply_eigenfunctional (TemperedDistribution.delta x).toLinearMap
    _ (fun j => c * (x j : ℂ)) (fun j ψ => by
      have hg : (fun y : EuclideanSpace ℝ (Fin n) => c * (y j : ℂ)).HasTemperateGrowth :=
        (Function.HasTemperateGrowth.const (E := EuclideanSpace ℝ (Fin n)) c).mul
          (coordinate_hasTemperateGrowth j)
      change (SchwartzMap.smulLeftCLM ℂ _ ψ) x = _
      rw [SchwartzMap.smulLeftCLM_apply hg]
      rfl) P φ
/-- The DLMF operator `D_j` applied to a Fourier transform is the transform of multiplication
by the original coordinate `x_j`. -/
lemma dlmfD_dlmfFourierSchwartz {n : ℕ} (j : Fin n)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    dlmfD j (dlmfFourierSchwartz φ) =
      dlmfFourierSchwartz (SchwartzMap.smulLeftCLM ℂ
        (fun x : EuclideanSpace ℝ (Fin n) => (x j : ℂ)) φ) := by
  change (-I) • (∂_{EuclideanSpace.single j (1 : ℝ)} (dlmfFourierSchwartz φ)) = _
  rw [lineDeriv_dlmfFourierSchwartz]
  have hg : (fun x : EuclideanSpace ℝ (Fin n) =>
      I * (inner ℝ x (EuclideanSpace.single j (1 : ℝ)) : ℂ)).HasTemperateGrowth := by fun_prop
  have he : SchwartzMap.smulLeftCLM ℂ
      (fun x : EuclideanSpace ℝ (Fin n) => I * (inner ℝ x (EuclideanSpace.single j (1 : ℝ)) : ℂ)) φ =
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
theorem dlmfFourierSchwartz_polyDiffOp {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    dlmfFourierSchwartz (polyDiffOp P φ) = polyMul (polyNeg P) (dlmfFourierSchwartz φ) := by
  ext x
  let L : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) →ₗ[ℂ] ℂ :=
    (TemperedDistribution.delta x).toLinearMap.comp dlmfFourierSchwartz.toLinearMap
  have h := polyOp_apply_eigenfunctional L dlmfD (fun j => -(x j : ℂ))
    (fun j φ => dlmfFourierSchwartz_dlmfD j φ x) P φ
  have hg := polyEval_hasTemperateGrowth (polyNeg P)
  rw [polyMul, SchwartzMap.smulLeftCLM_apply hg]
  change L (polyOp P dlmfD φ) = polyEval (polyNeg P) x * dlmfFourierSchwartz φ x
  rw [h]
  congr 1
  have he : (MvPolynomial.eval (fun j => (x j : ℂ))).comp MvPolynomial.C =
      RingHom.id ℂ := by
    ext c
    simp
  simp [polyEval, polyNeg, he]

/-- DLMF 1.16.34: `𝓕(Pφ)(𝐱) = P(𝐃) 𝓕φ(𝐱)` on Schwartz space. -/
@[dlmf 1.16.E34]
theorem dlmfFourierSchwartz_polyMul {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    dlmfFourierSchwartz (polyMul P φ) = polyDiffOp P (dlmfFourierSchwartz φ) := by
  let X (j : Fin n) : Module.End ℂ 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
    (SchwartzMap.smulLeftCLM ℂ (fun x : EuclideanSpace ℝ (Fin n) => (x j : ℂ))).toLinearMap
  have hxg (j : Fin n) : (fun x : EuclideanSpace ℝ (Fin n) => (x j : ℂ)).HasTemperateGrowth := by
    have hi : (fun x : EuclideanSpace ℝ (Fin n) =>
        (inner ℝ x (EuclideanSpace.single j (1 : ℝ)) : ℂ)).HasTemperateGrowth := by fun_prop
    convert hi using 1
    ext y
    simp [EuclideanSpace.inner_single_right]
  have hX (j : Fin n) (ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
      dlmfFourierSchwartz (X j ψ) = dlmfD j (dlmfFourierSchwartz ψ) := by
    change _ = (-I) • (∂_{EuclideanSpace.single j (1 : ℝ)} (dlmfFourierSchwartz ψ))
    rw [lineDeriv_dlmfFourierSchwartz]
    have hg : (fun x : EuclideanSpace ℝ (Fin n) =>
        I * (inner ℝ x (EuclideanSpace.single j (1 : ℝ)) : ℂ)).HasTemperateGrowth := by fun_prop
    have he : SchwartzMap.smulLeftCLM ℂ
        (fun x : EuclideanSpace ℝ (Fin n) => I * (inner ℝ x (EuclideanSpace.single j (1 : ℝ)) : ℂ)) ψ =
        I • X j ψ := by
      ext x
      rw [SchwartzMap.smulLeftCLM_apply hg]
      change _ = I * (SchwartzMap.smulLeftCLM ℂ
        (fun x : EuclideanSpace ℝ (Fin n) => (x j : ℂ)) ψ) x
      rw [SchwartzMap.smulLeftCLM_apply (hxg j)]
      simp [EuclideanSpace.inner_single_right, smul_eq_mul, mul_assoc]
    rw [he, map_smul, smul_smul]
    simp
  have hpX : polyOp P X φ = polyMul P φ := by
    ext x
    let L : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) →ₗ[ℂ] ℂ := (TemperedDistribution.delta x).toLinearMap
    have h := polyOp_apply_eigenfunctional L X (fun j => (x j : ℂ)) (fun j ψ => by
      change (SchwartzMap.smulLeftCLM ℂ (fun x : EuclideanSpace ℝ (Fin n) => (x j : ℂ)) ψ) x = _
      rw [SchwartzMap.smulLeftCLM_apply (hxg j)]
      rfl) P φ
    have hpg := polyEval_hasTemperateGrowth P
    rw [polyMul, SchwartzMap.smulLeftCLM_apply hpg]
    exact h
  rw [← hpX]
  exact polyOp_intertwine dlmfFourierSchwartz.toLinearMap X dlmfD hX P φ

/-- DLMF 1.16.36: `⟨𝓕(P(𝐃)u), φ⟩ = ⟨P₋ 𝓕(u), φ⟩ = ⟨𝓕(u), P₋φ⟩` for a tempered
distribution `u`, `P₋(𝐱) = P(-𝐱)`, derivatives in the sense of distributions. -/
@[dlmf 1.16.E36]
theorem dlmfFourierTempered_polyDiffOp {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    dlmfFourierTempered (temperedPolyDiffOp P u) φ =
        temperedPolyMul (polyNeg P) (dlmfFourierTempered u) φ ∧
      temperedPolyMul (polyNeg P) (dlmfFourierTempered u) φ =
        dlmfFourierTempered u (polyMul (polyNeg P) φ) := by
  let X (j : Fin n) : Module.End ℂ 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
    (SchwartzMap.smulLeftCLM ℂ (fun x : EuclideanSpace ℝ (Fin n) => -(x j : ℂ))).toLinearMap
  have hX (j : Fin n) (ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
      dlmfFourierSchwartz (X j ψ) = (-dlmfD j) (dlmfFourierSchwartz ψ) := by
    have hg := coordinate_hasTemperateGrowth j
    have he : X j ψ = -(SchwartzMap.smulLeftCLM ℂ
        (fun x : EuclideanSpace ℝ (Fin n) => (x j : ℂ)) ψ) := by
      change SchwartzMap.smulLeftCLM ℂ
        (fun x : EuclideanSpace ℝ (Fin n) => -(x j : ℂ)) ψ = _
      rw [SchwartzMap.smulLeftCLM_fun_neg hg]
      rfl
    rw [he, map_neg]
    exact congrArg Neg.neg (dlmfD_dlmfFourierSchwartz j ψ).symm
  have hpoly : polyOp P X φ = polyMul (polyNeg P) φ := by
    ext x
    have h := polyOp_coordinateMul_apply (-1) P φ x
    have hg := polyEval_hasTemperateGrowth (polyNeg P)
    rw [polyMul, SchwartzMap.smulLeftCLM_apply hg]
    change polyOp P X φ x = polyEval (polyNeg P) x * φ x
    have he : (MvPolynomial.eval (fun j => (x j : ℂ))).comp MvPolynomial.C =
        RingHom.id ℂ := by ext c; simp
    have heval : MvPolynomial.eval (fun j => -(x j : ℂ)) P = polyEval (polyNeg P) x := by
      simp [polyEval, polyNeg, he]
    simpa only [X, neg_one_mul, heval] using h
  have hi := polyOp_intertwine dlmfFourierSchwartz.toLinearMap X (fun j => -dlmfD j) hX P φ
  change dlmfFourierSchwartz (polyOp P X φ) =
    polyOp P (fun j => -dlmfD j) (dlmfFourierSchwartz φ) at hi
  constructor
  · change temperedPolyDiffOp P u (dlmfFourierSchwartz φ) =
      u (dlmfFourierSchwartz (polyMul (polyNeg P) φ))
    rw [temperedPolyDiffOp_apply, ← hi, hpoly]
  · rfl

/-- DLMF 1.16.37: `⟨𝓕(Pu), φ⟩ = ⟨P(𝐃) 𝓕(u), φ⟩` for a tempered distribution `u`. -/
@[dlmf 1.16.E37]
theorem dlmfFourierTempered_polyMul {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    dlmfFourierTempered (temperedPolyMul P u) =
      temperedPolyDiffOp P (dlmfFourierTempered u) := by
  let X (j : Fin n) : Module.End ℂ 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
    (SchwartzMap.smulLeftCLM ℂ (fun x : EuclideanSpace ℝ (Fin n) => (x j : ℂ))).toLinearMap
  have hX (j : Fin n) (ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
      dlmfFourierSchwartz ((-dlmfD j) ψ) = X j (dlmfFourierSchwartz ψ) := by
    ext x
    change dlmfFourierSchwartz (-(dlmfD j ψ)) x =
      (SchwartzMap.smulLeftCLM ℂ (fun x : EuclideanSpace ℝ (Fin n) => (x j : ℂ))
        (dlmfFourierSchwartz ψ)) x
    rw [map_neg, neg_apply, dlmfFourierSchwartz_dlmfD,
      SchwartzMap.smulLeftCLM_apply (coordinate_hasTemperateGrowth j)]
    simp [smul_eq_mul]
  have hpoly (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) : polyOp P X φ = polyMul P φ := by
    ext x
    have h := polyOp_coordinateMul_apply 1 P φ x
    rw [polyMul, SchwartzMap.smulLeftCLM_apply (polyEval_hasTemperateGrowth P)]
    simpa only [X, one_mul, polyEval, smul_eq_mul] using h
  ext φ
  change u (polyMul P (dlmfFourierSchwartz φ)) =
    temperedPolyDiffOp P (dlmfFourierTempered u) φ
  rw [temperedPolyDiffOp_apply]
  change u (polyMul P (dlmfFourierSchwartz φ)) =
    u (dlmfFourierSchwartz (polyOp P (fun j => -dlmfD j) φ))
  have hi := polyOp_intertwine dlmfFourierSchwartz.toLinearMap (fun j => -dlmfD j) X hX P φ
  change dlmfFourierSchwartz (polyOp P (fun j => -dlmfD j) φ) =
    polyOp P X (dlmfFourierSchwartz φ) at hi
  rw [hi, hpoly]

/-! ## §1.16(viii): Fourier transforms of special distributions -/

/-- DLMF 1.16.38–1.16.40: `⟨𝓕(δ), φ⟩ = (2π)^{-1/2} ∫ φ(t) dt = (2π)^{-1/2} ⟨1, φ⟩`, that is
`𝓕(δ) = 1/√(2π)` (1.16.39), conventionally `∫ δ(t) e^{ixt} dt = 1` (1.16.40). -/
@[dlmf 1.16.E38, dlmf 1.16.E39, dlmf 1.16.E40]
theorem dlmfFourierTempered_delta :
    dlmfFourierTempered (TemperedDistribution.delta (0 : ℝ)) =
      (((2 * Real.pi) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) • volume.toTemperedDistribution := by
  ext φ
  change dlmfFourierSchwartz φ 0 = _
  rw [dlmfFourierSchwartz_apply]
  simp

/-- DLMF 1.16.41–1.16.43: `⟨𝓕(1), φ⟩ = √(2π) φ(0)`, that is `𝓕(1) = √(2π) δ` (1.16.42),
conventionally `(2π)^{-1} ∫ e^{ixt} dt = δ(x)` (1.16.43). -/
@[dlmf 1.16.E41, dlmf 1.16.E42, dlmf 1.16.E43]
theorem dlmfFourierTempered_one :
    dlmfFourierTempered (volume.toTemperedDistribution : 𝓢'(ℝ, ℂ)) =
      (Real.sqrt (2 * Real.pi) : ℂ) • TemperedDistribution.delta 0 := by
  ext φ
  have hF : ∫ t : ℝ, (𝓕⁻ φ) t = φ 0 := by
    have h := congrArg (fun ψ : 𝓢(ℝ, ℂ) => ψ 0)
      (FourierTransform.fourier_fourierInv_eq (F := 𝓢(ℝ, ℂ)) φ)
    change (𝓕 (𝓕⁻ φ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ)) 0 = φ 0 at h
    rw [SchwartzMap.fourier_coe, Real.fourier_eq] at h
    simpa using h
  change (∫ t : ℝ, dlmfFourierSchwartz φ t) =
    (Real.sqrt (2 * Real.pi) : ℂ) * φ 0
  simp only [dlmfFourierSchwartz, smul_apply, ContinuousLinearMap.comp_apply,
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
    rw [signTempered, boundedTempered, dite_eq_left hmem, Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    filter_upwards [hmem.coeFn_toLp] with x hx
    simp only [hx, smul_eq_mul]
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
theorem dlmfFourierTempered_deriv_sign :
    dlmfFourierTempered (TemperedDistribution.derivCLM ℂ signTempered) =
      (Real.sqrt (2 / Real.pi) : ℂ) • volume.toTemperedDistribution := by
  rw [deriv_signTempered, map_smul, dlmfFourierTempered_delta, smul_smul]
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
lemma dlmfFourierSchwartz_deriv (φ : 𝓢(ℝ, ℂ)) :
    SchwartzMap.derivCLM ℂ ℂ (dlmfFourierSchwartz φ) =
      dlmfFourierSchwartz (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => I * x) φ) := by
  have hd : SchwartzMap.derivCLM ℂ ℂ (dlmfFourierSchwartz φ) =
      ∂_{(1 : ℝ)} (dlmfFourierSchwartz φ) := by ext x; rfl
  rw [hd]
  simpa only [Real.inner_apply, mul_one] using lineDeriv_dlmfFourierSchwartz φ (1 : ℝ)

/-- The one-variable case of DLMF 1.16.36 with `P(𝐃) = d/dx`, `P₋(x) = -ix`:
`𝓕(u') = (x/i) 𝓕(u)` for a tempered distribution `u` on the line. -/
theorem dlmfFourierTempered_deriv (u : 𝓢'(ℝ, ℂ)) :
    dlmfFourierTempered (TemperedDistribution.derivCLM ℂ u) =
      TemperedDistribution.smulLeftCLM ℂ (fun x : ℝ => -I * x) (dlmfFourierTempered u) := by
  ext φ
  change u (-SchwartzMap.derivCLM ℂ ℂ (dlmfFourierSchwartz φ)) =
    u (dlmfFourierSchwartz (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => -I * x) φ))
  rw [dlmfFourierSchwartz_deriv]
  have hg : (fun x : ℝ => I * (x : ℂ)).HasTemperateGrowth := by fun_prop
  have he : (fun x : ℝ => -I * (x : ℂ)) = fun x : ℝ => -(I * (x : ℂ)) := by
    funext x
    ring
  rw [he, SchwartzMap.smulLeftCLM_fun_neg hg]
  simp only [neg_apply, map_neg]

/-- DLMF 1.16.47: `𝓕(sign') = (x/i) 𝓕(sign)`. -/
@[dlmf 1.16.E47]
theorem dlmfFourierTempered_deriv_sign' :
    dlmfFourierTempered (TemperedDistribution.derivCLM ℂ signTempered) =
      TemperedDistribution.smulLeftCLM ℂ (fun x : ℝ => -I * x)
        (dlmfFourierTempered signTempered) :=
  dlmfFourierTempered_deriv signTempered

/-- DLMF 1.16.48–1.16.49: `𝓕(sign) = √(2/π) i/x`, that is
`⟨𝓕(sign), φ⟩ = i √(2/π) ⨍ φ(x)/x dx` (Cauchy principal value, the limit of the integrals over
`|x| > ε` as `ε → 0+`). -/
@[dlmf 1.16.E48, dlmf 1.16.E49]
theorem dlmfFourierTempered_sign (φ : 𝓢(ℝ, ℂ)) :
    Tendsto (fun ε : ℝ => I * Real.sqrt (2 / Real.pi) * ∫ x in {x : ℝ | ε < |x|}, φ x / x)
      (𝓝[>] 0) (𝓝 (dlmfFourierTempered signTempered φ)) := by
  sorry

/-- DLMF 1.16.50–1.16.51: `𝓕(H) = √(π/2) (δ + i/(πx))`, that is
`⟨𝓕(H), φ⟩ = √(π/2) φ(0) + (i/√(2π)) ⨍ φ(x)/x dx` (principal value). -/
@[dlmf 1.16.E50, dlmf 1.16.E51]
theorem dlmfFourierTempered_heaviside (φ : 𝓢(ℝ, ℂ)) :
    Tendsto (fun ε : ℝ => Real.sqrt (Real.pi / 2) * φ 0 +
        I / Real.sqrt (2 * Real.pi) * ∫ x in {x : ℝ | ε < |x|}, φ x / x)
      (𝓝[>] 0) (𝓝 (dlmfFourierTempered heavisideTempered φ)) := by
  sorry

end DLMF.AlgebraicAnalytic
