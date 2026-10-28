/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Distributions.Defs

/-!
# Distributions (DLMF §1.16)

Theorems of DLMF §1.16 that are not already in Mathlib (the upstream pointers are in
`DLMF.AlgebraicAnalytic.Distributions.MathlibCoverage`):

* `distribIterDeriv_apply` (1.16.9) and `distribIterDeriv_delta_apply` (1.16.12);
* `deriv_heaviside_shift` (1.16.16), `deriv_heaviside` (1.16.15), `stieltjes_eq_deriv`
  (1.16.9_5), the jump formula `iterDeriv_piecewise` (1.16.17–1.16.18), `deriv_xPlusRpow`
  (1.16.20) and the consistency of `xPlusDistrib` (1.16.21);
* `sign_eq_two_mul_heaviside_sub_one` (1.16.44), `deriv_sign` (1.16.45);
* the DLMF Fourier transform: `dlmfFourierSchwartz_apply` (1.16.29), the operator identities
  1.16.33–1.16.34 and 1.16.36–1.16.37, and the transforms of `δ`, `1`, `sign` and `H`
  (1.16.38–1.16.51).

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
lemma g1f_coe_lineDeriv_one (φ : 𝓓(Ω, ℝ)) : ⇑(∂_{(1 : ℝ)} φ : 𝓓(Ω, ℝ)) = deriv ⇑φ := by
  ext x
  rw [TestFunction.lineDerivOp_eq_lineDerivCLM ℝ, TestFunction.lineDerivCLM_apply_of_le le_top,
    (φ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv]
  rfl

/-- The `k`-fold derivative of a test function on the line: `(∂_{1})^[k] φ = φ^{(k)}`. -/
lemma g1f_coe_iterate_lineDeriv_one (k : ℕ) (φ : 𝓓(Ω, ℝ)) :
    ⇑((fun ψ : 𝓓(Ω, ℝ) => ∂_{(1 : ℝ)} ψ)^[k] φ) = iteratedDeriv k ⇑φ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', g1f_coe_lineDeriv_one, ih, iteratedDeriv_succ]

/-- DLMF 1.16.9: `⟨Λ^{(k)}, φ⟩ = (-1)^k ⟨Λ, φ^{(k)}⟩`, with `φ^{(k)}` the `k`-fold
derivative of the test function (as an element of `𝓓(Ω, ℝ)`; its values are
`iteratedDeriv k φ`, `g1f_coe_iterate_lineDeriv_one`). The case `k = 1` is 1.16.8,
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
  rw [distribIterDeriv_apply, Distribution.delta_apply, g1f_coe_iterate_lineDeriv_one,
    smul_eq_mul]

end Deriv

/-! ## §1.16(iv): the Heaviside function -/

/-- Identity under the stated parameter and domain assumptions: `(fun x => heaviside (x - x₀)) =
(Ioi x₀).indicator (fun _ => (1 : ℝ))`. -/
lemma g1f_heaviside_shift_eq_indicator (x₀ : ℝ) :
    (fun x => heaviside (x - x₀)) = (Ioi x₀).indicator (fun _ => (1 : ℝ)) := by
  ext x
  simp [heaviside, Set.indicator, sub_pos]

/-- Identity under the stated parameter and domain assumptions: `LocallyIntegrable (fun x =>
heaviside (x - x₀)) volume`. -/
lemma g1f_locallyIntegrable_heaviside_shift (x₀ : ℝ) :
    LocallyIntegrable (fun x => heaviside (x - x₀)) volume := by
  rw [g1f_heaviside_shift_eq_indicator]
  exact (locallyIntegrable_const 1).indicator measurableSet_Ioi

/-- `∫ φ'(x) H(x - x₀) dx = -φ(x₀)` for a test function `φ` on the line. -/
lemma g1f_integral_deriv_mul_heaviside (x₀ : ℝ) (φ : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)) :
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
    Distribution.ofFun_apply ((g1f_locallyIntegrable_heaviside_shift x₀).locallyIntegrableOn _),
    Distribution.delta_apply]
  simp only [FunLike.coe_neg, Pi.neg_apply, g1f_coe_lineDeriv_one, smul_eq_mul, neg_mul,
    integral_neg, g1f_integral_deriv_mul_heaviside, neg_neg]

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
lemma g1f_deriv_const (c : ℝ) : ∂_{(1 : ℝ)} (lineDistrib fun _ => c) = 0 := by
  ext φ
  have hd : ContDiff ℝ 1 ⇑φ := φ.contDiff.of_le (by simp)
  rw [Distribution.lineDerivOp_apply_apply, lineDistrib,
    Distribution.ofFun_apply ((locallyIntegrable_const c).locallyIntegrableOn _)]
  simp only [FunLike.coe_neg, Pi.neg_apply, g1f_coe_lineDeriv_one, smul_eq_mul, neg_mul,
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
        (((g1f_locallyIntegrable_heaviside_shift 0).smul (2 : ℝ)).locallyIntegrableOn _)
        ((locallyIntegrable_const (1 : ℝ)).neg.locallyIntegrableOn _),
      Distribution.ofFun_smul, Distribution.ofFun_neg, sub_eq_add_neg]
    rfl
  rw [h2, sub_eq_add_neg, LineDeriv.lineDerivOp_add, LineDeriv.lineDerivOp_neg,
    LineDeriv.lineDerivOp_smul, deriv_heaviside_shift, g1f_deriv_const, neg_zero, add_zero]

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
  sorry

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
  sorry

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

/-- DLMF 1.16.33: `𝓕(P(𝐃)φ)(𝐱) = P(-𝐱) 𝓕φ(𝐱)` on Schwartz space. -/
@[dlmf 1.16.E33]
theorem dlmfFourierSchwartz_polyDiffOp {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    dlmfFourierSchwartz (polyDiffOp P φ) = polyMul (polyNeg P) (dlmfFourierSchwartz φ) := by
  sorry

/-- DLMF 1.16.34: `𝓕(Pφ)(𝐱) = P(𝐃) 𝓕φ(𝐱)` on Schwartz space. -/
@[dlmf 1.16.E34]
theorem dlmfFourierSchwartz_polyMul {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    dlmfFourierSchwartz (polyMul P φ) = polyDiffOp P (dlmfFourierSchwartz φ) := by
  sorry

/-- DLMF 1.16.36: `⟨𝓕(P(𝐃)u), φ⟩ = ⟨P₋ 𝓕(u), φ⟩ = ⟨𝓕(u), P₋φ⟩` for a tempered
distribution `u`, `P₋(𝐱) = P(-𝐱)`, derivatives in the sense of distributions. -/
@[dlmf 1.16.E36]
theorem dlmfFourierTempered_polyDiffOp {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    dlmfFourierTempered (temperedPolyDiffOp P u) φ =
        temperedPolyMul (polyNeg P) (dlmfFourierTempered u) φ ∧
      temperedPolyMul (polyNeg P) (dlmfFourierTempered u) φ =
        dlmfFourierTempered u (polyMul (polyNeg P) φ) := by
  sorry

/-- DLMF 1.16.37: `⟨𝓕(Pu), φ⟩ = ⟨P(𝐃) 𝓕(u), φ⟩` for a tempered distribution `u`. -/
@[dlmf 1.16.E37]
theorem dlmfFourierTempered_polyMul {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    dlmfFourierTempered (temperedPolyMul P u) =
      temperedPolyDiffOp P (dlmfFourierTempered u) := by
  sorry

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
  sorry

/-- The tempered form of DLMF 1.16.45: `sign' = 2δ`. -/
@[dlmf 1.16.E45]
theorem deriv_signTempered :
    TemperedDistribution.derivCLM ℂ signTempered = (2 : ℂ) • TemperedDistribution.delta 0 := by
  sorry

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

/-- The one-variable case of DLMF 1.16.36 with `P(𝐃) = d/dx`, `P₋(x) = -ix`:
`𝓕(u') = (x/i) 𝓕(u)` for a tempered distribution `u` on the line. -/
theorem dlmfFourierTempered_deriv (u : 𝓢'(ℝ, ℂ)) :
    dlmfFourierTempered (TemperedDistribution.derivCLM ℂ u) =
      TemperedDistribution.smulLeftCLM ℂ (fun x : ℝ => -I * x) (dlmfFourierTempered u) := by
  sorry

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
