/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.BernoulliEuler.Basic
public import DLMF.Zeta.Basic.RiemannProperties
public import DLMF.Constants.Dirichlet
public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.LSeries.Deriv
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import DLMFMathlib.RingTheory.Binomial

/-!
# The Riemann zeta function: definition and expansions (DLMF §§25.1–25.2)

The Riemann zeta function `ζ(s)` of DLMF Chapter 25 is Mathlib's `riemannZeta`, defined on all
of `ℂ` by analytic continuation (via the Hurwitz zeta function), with the junk value
`riemannZeta 1 = (γ - log (4π))/2` at the pole. The Dirichlet series 25.2.1, the residue at
`s = 1`, the constant term of the Laurent expansion and the Euler product 25.2.11 are Mathlib
theorems; their `dlmf_upstream` pointers are in `DLMF.Core.UpstreamElementary`. The Stieltjes
constants (25.2.5), the Laurent expansion (25.2.4) and the Dirichlet series of the derivatives
(25.2.6–25.2.7) are in the foundational module `DLMF.Zeta.Basic.RiemannProperties`. This file
covers the remaining items of §25.2.

## Main results

* `riemannZeta_eq_odd_series`: the odd-term series (DLMF 25.2.2).
* `tendsto_alternating_partial_sums`, `riemannZeta_eq_alternating`: the alternating series
  (DLMF 25.2.3).
* `riemannZeta_eq_sum_add_integral_fract`, `riemannZeta_eq_eulerMaclaurin`,
  `riemannZeta_eq_eulerMaclaurin_one`: the Euler–Maclaurin representations
  (DLMF 25.2.8–25.2.10).
* `riemannZeta_hadamard_product`: the Hadamard product (DLMF 25.2.12).

## Implementation notes

25.2.3 converges only conditionally for `0 < Re s ≤ 1`; it is stated with natural-order partial
sums. Where DLMF divides by `1 - 2^{1-s}`, which vanishes at `s = 1 + 2πik/ln 2`, the statement
is also given in the multiplied form, valid for every `s ≠ 1` with `Re s > 0`.

In 25.2.8–25.2.10, `x - ⌊x⌋` is `Int.fract x`, the periodic Bernoulli function
`B̃ₙ(x) = Bₙ(x - ⌊x⌋)` of §25.1 / §24.2(iii) is the project's `periodicBernoulli`, and the
generalized binomial coefficient is `Ring.choose`. The Hadamard product runs
over the zeros `ρ` with `Re ρ > 0`, counted with multiplicity (`analyticOrderNatAt`).

§25.1 (notation) has no formulas: `γ` is `Real.eulerMascheroniConstant`, `ψ` is
`Complex.digamma`, `Bₙ` is Mathlib's `bernoulli` (with `B₁ = -1/2`, DLMF's convention) and
`Bₙ(x)` is `bernoulliFun n x` / `Polynomial.bernoulli n`.
-/

@[expose] public noncomputable section

open Complex Filter Topology MeasureTheory Set Finset
open scoped Real Nat

namespace DLMF.Zeta

open DLMF.BernoulliEuler

/-! ### §25.2(ii) Other infinite series -/

/-- DLMF 25.2.2: `ζ(s) = (1 - 2^{-s})⁻¹ ∑_{n≥0} (2n+1)^{-s}` for `Re s > 1`, where the factor
`1 - 2^{-s}` does not vanish. Proved from `DLMF.Constants.dirichletLambda_eq`. -/
@[dlmf 25.2.E2]
theorem riemannZeta_eq_odd_series {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => 1 / (2 * n + 1 : ℂ) ^ s) ∧
      riemannZeta s = 1 / (1 - 2 ^ (-s)) * ∑' n : ℕ, 1 / (2 * n + 1 : ℂ) ^ s := by
  refine ⟨DLMF.Constants.summable_odd_terms hs, ?_⟩
  have h := DLMF.Constants.dirichletLambda_eq hs
  rw [DLMF.Constants.dirichletLambda] at h
  have hne : (1 : ℂ) - 2 ^ (-s) ≠ 0 := by
    have h2 : ‖(2 : ℂ) ^ (-s)‖ < 1 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, norm_cpow_eq_rpow_re_of_pos (by norm_num)]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by simp; linarith)
    intro h0
    rw [sub_eq_zero] at h0
    rw [← h0] at h2
    simp at h2
  rw [h]
  field_simp

/-! ### §25.2(iii) Representations by the Euler–Maclaurin formula -/

/-! #### Helpers for 25.2.8–25.2.9: integration by parts against `B̃ₚ` -/

/-- `B̃_q` is bounded. -/
theorem exists_abs_periodicBernoulli_le (q : ℕ) : ∃ C : ℝ, ∀ x, |periodicBernoulli q x| ≤ C := by
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn (isCompact_Icc (a := (0 : ℝ)) (b := 1))
    (continuous_bernoulliFun q).continuousOn
  exact ⟨C, fun x => by
    simpa [Real.norm_eq_abs, periodicBernoulli] using
      hC _ ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩⟩

/-- `B̃_q` is continuous for `q ≠ 1`. -/
private lemma continuous_periodicBernoulli {q : ℕ} (hq : q ≠ 1) :
    Continuous (periodicBernoulli q) := by
  have : periodicBernoulli q = periodizedBernoulli q ∘ ((↑) : ℝ → UnitAddCircle) := by
    funext x; exact periodicBernoulliB_eq_periodizedBernoulli q x
  rw [this]; exact (periodizedBernoulli.continuous hq).comp continuous_quotient_mk'

/-- `B̃_{p+1}' = (p+1) B̃_p` off the integers. -/
private lemma hasDerivAt_periodicBernoulli_succ (p : ℕ) {x : ℝ} (hx : x ∉ range (Int.cast : ℤ → ℝ)) :
    HasDerivAt (periodicBernoulli (p + 1)) ((p + 1) * periodicBernoulli p x) x := by
  set m := ⌊x⌋
  have hlt : (m : ℝ) < x := lt_of_le_of_ne (Int.floor_le x) (fun h => hx ⟨m, h⟩)
  have hlt2 : x < m + 1 := Int.lt_floor_add_one x
  have heq : periodicBernoulli (p + 1) =ᶠ[𝓝 x] (fun y => bernoulliFun (p + 1) (y - m)) := by
    filter_upwards [Ioo_mem_nhds hlt hlt2] with y hy
    rw [periodicBernoulli, Int.fract, Int.floor_eq_iff.mpr ⟨hy.1.le, hy.2⟩]
  have hd := (hasDerivAt_bernoulliFun (p + 1) (x - m)).comp x
    ((hasDerivAt_id x).sub_const (m : ℝ))
  have hP : periodicBernoulli p x = bernoulliFun p (x - m) := by
    rw [periodicBernoulli, Int.fract]
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  convert hd using 1
  · funext y; simp
  · rw [hP]; push_cast; simp

/-- A bounded measurable function divided by `x^w`, `Re w > 1`, is integrable on `(a, ∞)`. -/
theorem integrableOn_bdd_div_cpow {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) {w : ℂ} (hw : 1 < w.re) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => (f x : ℂ) / (x : ℂ) ^ w) (Ioi a) := by
  have hi := integrableOn_Ioi_cpow_of_lt (a := -w) (by simp; linarith) ha
  have : IntegrableOn (fun x : ℝ => (f x : ℂ) * (x : ℂ) ^ (-w)) (Ioi a) :=
    Integrable.bdd_mul (f := fun x => (f x : ℂ)) (c := C) hi
    ((Complex.measurable_ofReal.comp hf).aestronglyMeasurable)
    (ae_of_all _ fun x => by simpa using hC x)
  refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp [div_eq_mul_inv, cpow_neg]

/-- Interval integrability of a bounded measurable function divided by `x^w` on `[a, b]`,
`0 < a`. -/
theorem intervalIntegrable_bdd_div_cpow {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) (w : ℂ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun x : ℝ => (f x : ℂ) / (x : ℂ) ^ w) volume a b := by
  have hc : ContinuousOn (fun x : ℝ => ((x : ℂ) ^ w)⁻¹) (uIcc a b) := by
    refine ContinuousOn.inv₀ ?_ ?_
    · refine ContinuousOn.cpow_const (Complex.continuous_ofReal.continuousOn) fun x hx => ?_
      rw [uIcc_of_le hab] at hx
      exact ofReal_mem_slitPlane.mpr (by linarith [hx.1])
    · intro x hx
      rw [uIcc_of_le hab] at hx
      exact cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast (by linarith [hx.1] : x ≠ 0)))
  have hi := hc.intervalIntegrable (μ := volume)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab] at hi ⊢
  have : IntegrableOn (fun x : ℝ => (f x : ℂ) * ((x : ℂ) ^ w)⁻¹) (Ioc a b) :=
    Integrable.bdd_mul (f := fun x => (f x : ℂ)) (c := C) hi
    ((Complex.measurable_ofReal.comp hf).aestronglyMeasurable)
    (ae_of_all _ fun x => by simpa using hC x)
  refine this.congr_fun (fun x _ => ?_) measurableSet_Ioc
  simp [div_eq_mul_inv]

/-- The derivative of `B̃_{p+1}(x) / x^w` off the integers, `x > 0`. -/
private lemma hasDerivAt_periodicBernoulli_div_cpow (p : ℕ) (w : ℂ) {x : ℝ} (hx0 : 0 < x)
    (hx : x ∉ range (Int.cast : ℤ → ℝ)) :
    HasDerivAt (fun y : ℝ => (periodicBernoulli (p + 1) y : ℂ) / (y : ℂ) ^ w)
      ((p + 1) * ((periodicBernoulli p x : ℂ) / (x : ℂ) ^ w) -
        w * ((periodicBernoulli (p + 1) x : ℂ) / (x : ℂ) ^ (w + 1))) x := by
  have h1 := (hasDerivAt_periodicBernoulli_succ p hx).ofReal_comp
  have h2 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-w)) (-w * (x : ℂ) ^ (-w - 1)) x :=
    (Complex.hasStrictDerivAt_cpow_const (c := -w)
      (ofReal_mem_slitPlane.mpr hx0)).hasDerivAt.comp_ofReal
  have h := h1.mul h2
  convert h using 1
  · funext y; simp [div_eq_mul_inv, cpow_neg]
  · rw [show -w - 1 = -(w + 1) by ring, cpow_neg, cpow_neg]; push_cast; ring

/-- Integration by parts against `B̃_{p+1}` on `[a, b]`, `0 < a ≤ b`, `p ≥ 1`. -/
theorem integral_periodicBernoulli_div_cpow_by_parts {p : ℕ} (hp : 1 ≤ p) (w : ℂ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, ((p + 1) * ((periodicBernoulli p x : ℂ) / (x : ℂ) ^ w) -
        w * ((periodicBernoulli (p + 1) x : ℂ) / (x : ℂ) ^ (w + 1))) =
      (periodicBernoulli (p + 1) b : ℂ) / (b : ℂ) ^ w -
        (periodicBernoulli (p + 1) a : ℂ) / (a : ℂ) ^ w := by
  obtain ⟨C, hC⟩ := exists_abs_periodicBernoulli_le p
  obtain ⟨D, hD⟩ := exists_abs_periodicBernoulli_le (p + 1)
  refine integral_eq_of_hasDerivAt_off_countable_of_le
    (fun y : ℝ => (periodicBernoulli (p + 1) y : ℂ) / (y : ℂ) ^ w) _ hab
    (countable_range (Int.cast : ℤ → ℝ)) ?_ ?_ ?_
  · have hc := continuous_periodicBernoulli (q := p + 1) (by omega)
    refine (Complex.continuous_ofReal.comp hc).continuousOn.div ?_ ?_
    · exact ContinuousOn.cpow_const (Complex.continuous_ofReal.continuousOn) fun x hx =>
        ofReal_mem_slitPlane.mpr (by linarith [hx.1])
    · intro x hx
      exact cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast (by linarith [hx.1] : x ≠ 0)))
  · exact fun x hx => hasDerivAt_periodicBernoulli_div_cpow p w (by linarith [hx.1.1]) hx.2
  · refine IntervalIntegrable.sub ?_ ?_
    · exact (intervalIntegrable_bdd_div_cpow (measurable_periodicBernoulli p) hC w
        ha hab).const_mul _
    · exact (intervalIntegrable_bdd_div_cpow (measurable_periodicBernoulli (p + 1))
        hD (w + 1) ha hab).const_mul _

/-- `B̃_q(b) / b^w → 0` as `b → ∞` for `Re w > 0`. -/
theorem tendsto_periodicBernoulli_div_cpow (q : ℕ) {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun b : ℝ => (periodicBernoulli q b : ℂ) / (b : ℂ) ^ w) atTop (𝓝 0) := by
  obtain ⟨D, hD⟩ := exists_abs_periodicBernoulli_le q
  have hg : Tendsto (fun b : ℝ => D * b ^ (-w.re)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop hw).const_mul D
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [eventually_gt_atTop 0] with b hb
  rw [norm_div, norm_cpow_eq_rpow_re_of_pos hb, Complex.norm_real, Real.norm_eq_abs,
    Real.rpow_neg hb.le, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (hD b) (by positivity)

/-- The recursion for `∫_a^∞ B̃_p(x) x^{-w} dx`, `p ≥ 1`, `Re w > 1`, `a > 0`:
`(p+1) ∫ B̃_p x^{-w} = -B̃_{p+1}(a) a^{-w} + w ∫ B̃_{p+1} x^{-w-1}`. -/
theorem integral_Ioi_periodicBernoulli_div_cpow_recursion {p : ℕ} (hp : 1 ≤ p) {w : ℂ} (hw : 1 < w.re) {a : ℝ} (ha : 0 < a) :
    (p + 1) * ∫ x in Ioi a, (periodicBernoulli p x : ℂ) / (x : ℂ) ^ w =
      -((periodicBernoulli (p + 1) a : ℂ) / (a : ℂ) ^ w) +
        w * ∫ x in Ioi a, (periodicBernoulli (p + 1) x : ℂ) / (x : ℂ) ^ (w + 1) := by
  obtain ⟨C, hC⟩ := exists_abs_periodicBernoulli_le p
  obtain ⟨D, hD⟩ := exists_abs_periodicBernoulli_le (p + 1)
  have hI1 := integrableOn_bdd_div_cpow (measurable_periodicBernoulli p) hC hw ha
  have hI2 := integrableOn_bdd_div_cpow (measurable_periodicBernoulli (p + 1)) hD
    (w := w + 1) (by simp; linarith) ha
  have hlim1 := intervalIntegral_tendsto_integral_Ioi a hI1 tendsto_id
  have hlim2 := intervalIntegral_tendsto_integral_Ioi a hI2 tendsto_id
  have hlim := (hlim1.const_mul ((p : ℂ) + 1)).sub (hlim2.const_mul w)
  have heq : ∀ᶠ b in atTop, ((p : ℂ) + 1) * (∫ x in a..id b,
        (periodicBernoulli p x : ℂ) / (x : ℂ) ^ w) -
      w * (∫ x in a..id b, (periodicBernoulli (p + 1) x : ℂ) / (x : ℂ) ^ (w + 1)) =
      (periodicBernoulli (p + 1) b : ℂ) / (b : ℂ) ^ w -
        (periodicBernoulli (p + 1) a : ℂ) / (a : ℂ) ^ w := by
    filter_upwards [eventually_ge_atTop a] with b hb
    rw [← integral_periodicBernoulli_div_cpow_by_parts hp w ha hb, intervalIntegral.integral_sub, id,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    · exact (intervalIntegrable_bdd_div_cpow (measurable_periodicBernoulli p) hC w
        ha hb).const_mul _
    · exact (intervalIntegrable_bdd_div_cpow (measurable_periodicBernoulli (p + 1))
        hD (w + 1) ha hb).const_mul _
  have := tendsto_nhds_unique (hlim.congr' heq)
    ((tendsto_periodicBernoulli_div_cpow (p + 1) (by linarith : 0 < w.re)).sub_const _)
  linear_combination this

/-- `b^z → 0` as `b → ∞` for `Re z < 0`. -/
theorem tendsto_ofReal_cpow_atTop_of_re_neg {z : ℂ} (hz : z.re < 0) :
    Tendsto (fun b : ℝ => (b : ℂ) ^ z) atTop (𝓝 0) := by
  have hg : Tendsto (fun b : ℝ => b ^ (-(-z.re))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [eventually_gt_atTop 0] with b hb
  rw [norm_cpow_eq_rpow_re_of_pos hb, neg_neg]

/-- The partial sums `∑_{k=1}^{M} k^{-s}` tend to `ζ(s)` for `Re s > 1`. -/
private lemma tendsto_sum_Icc_one_div_cpow {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun M : ℕ => ∑ k ∈ Finset.Icc (1 : ℕ) M, 1 / (k : ℂ) ^ s) atTop
      (𝓝 (riemannZeta s)) := by
  have hsum : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ s) :=
    (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs)
  have h := hsum.hasSum.tendsto_sum_nat
  rw [show (∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℂ) ^ s) = riemannZeta s by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]; push_cast; rfl] at h
  refine h.congr fun M => ?_
  induction M with
  | zero => simp
  | succ M ih => rw [sum_range_succ, ih, sum_Icc_succ_top (by omega)]

/-- One unit interval of the base identity: for `k ≥ 1`, `s ≠ 0, 1`,
`(k+1)^{-s} = -((k+1)^{1-s} - k^{1-s})/(s-1) + ((k+1)^{-s} - k^{-s})/2
  - s ∫_k^{k+1} B̃₁(x) x^{-s-1} dx`. -/
private lemma one_div_natCast_succ_cpow_eq_integral_step {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) {k : ℕ} (hk : 1 ≤ k) :
    1 / ((k + 1 : ℕ) : ℂ) ^ s = -(((k + 1 : ℕ) : ℂ) ^ (1 - s) - (k : ℂ) ^ (1 - s)) / (s - 1) +
      1 / 2 * (((k + 1 : ℕ) : ℂ) ^ (-s) - (k : ℂ) ^ (-s)) -
      s * ∫ x in (k : ℝ)..(k + 1 : ℕ), (periodicBernoulli 1 x : ℂ) / (x : ℂ) ^ (s + 1) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set G : ℝ → ℂ := fun x => (x : ℂ) ^ (-s + 1) / (-s + 1) -
    ((k : ℂ) + 1 / 2) * ((x : ℂ) ^ (-s) / (-s)) with hG
  have hns : -s ≠ 0 := neg_ne_zero.mpr hs0
  have hint : ∫ x in (k : ℝ)..(k + 1 : ℕ), (periodicBernoulli 1 x : ℂ) / (x : ℂ) ^ (s + 1) =
      G ((k + 1 : ℕ) : ℝ) - G k := by
    obtain ⟨C, hC⟩ := exists_abs_periodicBernoulli_le 1
    refine integral_eq_of_hasDerivAt_off_countable_of_le G _ (by push_cast; linarith)
      (countable_singleton ((k + 1 : ℕ) : ℝ)) ?_ ?_ ?_
    · refine ContinuousOn.sub ?_ ?_
      · refine ContinuousOn.div_const ?_ _
        exact ContinuousOn.cpow_const (Complex.continuous_ofReal.continuousOn) fun x hx =>
          ofReal_mem_slitPlane.mpr (by linarith [hx.1])
      · refine ContinuousOn.mul continuousOn_const (ContinuousOn.div_const ?_ _)
        exact ContinuousOn.cpow_const (Complex.continuous_ofReal.continuousOn) fun x hx =>
          ofReal_mem_slitPlane.mpr (by linarith [hx.1])
    · intro x hx
      have hx0 : 0 < x := by linarith [hx.1.1]
      have hxne : x ≠ 0 := hx0.ne'
      have h1 := hasDerivAt_ofReal_cpow_const' hxne (r := -s) (by
        intro h; apply hs1; linear_combination -h)
      have h2 := (hasDerivAt_ofReal_cpow_const hxne hns).div_const (-s)
      have h := h1.sub (h2.const_mul ((k : ℂ) + 1 / 2))
      convert h using 1
      have hx2 : x < (k : ℝ) + 1 := by
        have := hx.1.2; push_cast at this; exact this
      have hP : (periodicBernoulli 1 x : ℂ) = x - k - 1 / 2 := by
        rw [periodicBernoulli, bernoulliFun_one, Int.fract,
          Int.floor_eq_iff.mpr ⟨by exact_mod_cast hx.1.1.le, by exact_mod_cast hx2⟩]
        push_cast; ring
      have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hxne
      have e : (x : ℂ) ^ (-s) = x * (x : ℂ) ^ (-(s + 1)) := by
        rw [show -s = 1 + -(s + 1) by ring, cpow_add _ _ hx', cpow_one]
      rw [hP, show -s - 1 = -(s + 1) by ring, e, div_eq_mul_inv, ← cpow_neg]
      field_simp
      ring
    · exact intervalIntegrable_bdd_div_cpow (measurable_periodicBernoulli 1) hC _
        hk0 (by push_cast; linarith)
  rw [hint, hG]
  have hK : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : k + 1 ≠ 0)
  have hK' : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have e1 : ((k + 1 : ℕ) : ℂ) ^ (1 - s) = ((k + 1 : ℕ) : ℂ) * ((k + 1 : ℕ) : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, cpow_add _ _ hK, cpow_one]
  have e0 : (k : ℂ) ^ (1 - s) = (k : ℂ) * (k : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, cpow_add _ _ hK', cpow_one]
  simp only [ofReal_natCast]
  rw [show -s + 1 = 1 - s by ring, e1, e0, one_div, ← cpow_neg]
  have hs1'' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hs1''' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  push_cast
  field_simp
  ring

/-- The finite form of the base identity, `N ≤ M`, `s ≠ 0, 1`. -/
private lemma sum_Icc_one_div_cpow_eq_finite_identity {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) (M : ℕ)
    (hM : N ≤ M) :
    ∑ k ∈ Finset.Icc (1 : ℕ) M, 1 / (k : ℂ) ^ s =
      ∑ k ∈ Finset.Icc (1 : ℕ) N, 1 / (k : ℂ) ^ s + (N : ℂ) ^ (1 - s) / (s - 1) -
        (M : ℂ) ^ (1 - s) / (s - 1) + 1 / 2 * (M : ℂ) ^ (-s) - 1 / 2 * (N : ℂ) ^ (-s) -
        s * ∫ x in (N : ℝ)..M, (periodicBernoulli 1 x : ℂ) / (x : ℂ) ^ (s + 1) := by
  obtain ⟨C, hC⟩ := exists_abs_periodicBernoulli_le 1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
    have hM1 : 1 ≤ M := le_trans hN hNM
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_bdd_div_cpow (measurable_periodicBernoulli 1) hC (s + 1)
        hN0 (by exact_mod_cast hNM : (N : ℝ) ≤ M))
      (intervalIntegrable_bdd_div_cpow (measurable_periodicBernoulli 1) hC (s + 1)
        (by exact_mod_cast hM1 : (0 : ℝ) < M) (by push_cast; linarith : (M : ℝ) ≤ (M + 1 : ℕ)))
    rw [sum_Icc_succ_top (by omega), ih, one_div_natCast_succ_cpow_eq_integral_step hs0 hs1 hM1, ← hsplit]
    ring

/-- The base identity (25.2.8 with `B̃₁`) for `Re s > 1`:
`ζ(s) = ∑_{k=1}^{N} k^{-s} + N^{1-s}/(s-1) - N^{-s}/2 - s ∫_N^∞ B̃₁(x) x^{-s-1} dx`. -/
private lemma riemannZeta_eq_sum_add_integral_periodicBernoulli_one {s : ℂ} (hs : 1 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    riemannZeta s = ∑ k ∈ Finset.Icc (1 : ℕ) N, 1 / (k : ℂ) ^ s + (N : ℂ) ^ (1 - s) / (s - 1) -
      1 / 2 * (N : ℂ) ^ (-s) -
      s * ∫ x in Ioi (N : ℝ), (periodicBernoulli 1 x : ℂ) / (x : ℂ) ^ (s + 1) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs; linarith
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs
  obtain ⟨C, hC⟩ := exists_abs_periodicBernoulli_le 1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hI := integrableOn_bdd_div_cpow (measurable_periodicBernoulli 1) hC
    (w := s + 1) (by simp; linarith) hN0
  have hlimI := intervalIntegral_tendsto_integral_Ioi (N : ℝ) hI tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun M : ℕ => (M : ℂ) ^ (1 - s)) atTop (𝓝 0) := by
    have := (tendsto_ofReal_cpow_atTop_of_re_neg (z := 1 - s) (by simp; linarith)).comp
      tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using this
  have h2 : Tendsto (fun M : ℕ => (M : ℂ) ^ (-s)) atTop (𝓝 0) := by
    have := (tendsto_ofReal_cpow_atTop_of_re_neg (z := -s) (by simp; linarith)).comp
      tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using this
  have hR := ((((tendsto_const_nhds (x := ∑ k ∈ Finset.Icc (1 : ℕ) N, 1 / (k : ℂ) ^ s +
      (N : ℂ) ^ (1 - s) / (s - 1))).sub (h1.div_const (s - 1))).add
      (h2.const_mul (1 / 2))).sub (tendsto_const_nhds (x := 1 / 2 * (N : ℂ) ^ (-s)))).sub
      (hlimI.const_mul s)
  have heq : ∀ᶠ M : ℕ in atTop, ∑ k ∈ Finset.Icc (1 : ℕ) M, 1 / (k : ℂ) ^ s =
      ∑ k ∈ Finset.Icc (1 : ℕ) N, 1 / (k : ℂ) ^ s + (N : ℂ) ^ (1 - s) / (s - 1) -
        (M : ℂ) ^ (1 - s) / (s - 1) + 1 / 2 * (M : ℂ) ^ (-s) - 1 / 2 * (N : ℂ) ^ (-s) -
        s * ∫ x in (N : ℝ)..M, (periodicBernoulli 1 x : ℂ) / (x : ℂ) ^ (s + 1) := by
    filter_upwards [eventually_ge_atTop N] with M hM
    exact sum_Icc_one_div_cpow_eq_finite_identity hs0 hs1 hN M hM
  have := tendsto_nhds_unique (tendsto_sum_Icc_one_div_cpow hs) (hR.congr' (heq.mono fun M h => h.symm))
  rw [this]
  ring

/-- `binom(z+1, m+1) = binom(z, m) (z+1)/(m+1)`. -/
private lemma choose_add_one_succ (z : ℂ) (m : ℕ) :
    Ring.choose (z + 1) (m + 1) = Ring.choose z m * (z + 1) / (m + 1) := by
  rw [Ring.choose_eq_descPochhammer_div, Ring.choose_eq_descPochhammer_div, descPochhammer_succ_left, Polynomial.eval_mul,
    Polynomial.eval_comp, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_one, add_sub_cancel_right, Nat.factorial_succ]
  have h1 : ((m ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  have h2 : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero m)
  push_cast
  field_simp

/-- `B̃_q(N) = B_q` at an integer `N`. -/
private lemma periodicBernoulli_natCast (q N : ℕ) :
    periodicBernoulli q N = bernoulli q := by
  rw [periodicBernoulli, Int.fract_natCast, bernoulliFun_eval_zero]

/-- The double integration-by-parts step from `B̃_{2n+1}` to `B̃_{2n+3}`, `Re s > -2n`. -/
private lemma choose_mul_integral_periodicBernoulli_double_step {s : ℂ} {n N : ℕ} (hN : 1 ≤ N) (hs : -(2 * n : ℝ) < s.re) :
    Ring.choose (s + 2 * n) (2 * n + 1) * ∫ x in Ioi (N : ℝ),
        (periodicBernoulli (2 * n + 1) x : ℂ) / (x : ℂ) ^ (s + 2 * n + 1) =
      -(Ring.choose (s + 2 * n) (2 * n + 1) * ((bernoulli (2 * n + 2) : ℂ) / (2 * n + 2)) *
          (N : ℂ) ^ (-(s + 2 * n + 1))) +
        Ring.choose (s + 2 * n + 2) (2 * n + 3) * ∫ x in Ioi (N : ℝ),
          (periodicBernoulli (2 * n + 3) x : ℂ) / (x : ℂ) ^ (s + 2 * n + 3) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := integral_Ioi_periodicBernoulli_div_cpow_recursion (p := 2 * n + 1) (by omega) (w := s + 2 * n + 1)
    (by simp; linarith) hN0
  have h2 := integral_Ioi_periodicBernoulli_div_cpow_recursion (p := 2 * n + 2) (by omega) (w := s + 2 * n + 2)
    (by simp; linarith) hN0
  rw [periodicBernoulli_natCast] at h1 h2
  rw [show 2 * n + 2 + 1 = 2 * n + 3 by ring, bernoulli_eq_zero_of_odd ⟨n + 1, by ring⟩
    (by omega)] at h2
  rw [show 2 * n + 1 + 1 = 2 * n + 2 by ring] at h1
  have e1 : s + 2 * (n : ℂ) + 1 + 1 = s + 2 * n + 2 := by ring
  have e2 : s + 2 * (n : ℂ) + 2 + 1 = s + 2 * n + 3 := by ring
  rw [e1] at h1
  rw [e2] at h2
  push_cast at h1 h2
  have hb1 : Ring.choose (s + 2 * n + 1) (2 * n + 2) =
      Ring.choose (s + 2 * n) (2 * n + 1) * (s + 2 * n + 1) / (2 * n + 2) := by
    rw [choose_add_one_succ]; push_cast; ring
  have hb2 : Ring.choose (s + 2 * n + 2) (2 * n + 3) =
      Ring.choose (s + 2 * n + 1) (2 * n + 2) * (s + 2 * n + 2) / (2 * n + 3) := by
    rw [show s + 2 * (n : ℂ) + 2 = s + 2 * n + 1 + 1 by ring, choose_add_one_succ]; push_cast; ring
  have hn2 : (2 * (n : ℂ) + 2) ≠ 0 := by
    have : (0 : ℝ) < 2 * n + 2 := by positivity
    exact_mod_cast this.ne'
  have hn3 : (2 * (n : ℂ) + 3) ≠ 0 := by
    have : (0 : ℝ) < 2 * n + 3 := by positivity
    exact_mod_cast this.ne'
  have hNp : (N : ℂ) ^ (-(s + 2 * n + 1)) = 1 / (N : ℂ) ^ (s + 2 * n + 1) := by
    rw [cpow_neg, one_div]
  rw [hb2, hb1, hNp]
  set A := ∫ x in Ioi (N : ℝ), (periodicBernoulli (2 * n + 1) x : ℂ) / (x : ℂ) ^ (s + 2 * n + 1)
  set B := ∫ x in Ioi (N : ℝ), (periodicBernoulli (2 * n + 2) x : ℂ) / (x : ℂ) ^ (s + 2 * n + 2)
  set C := ∫ x in Ioi (N : ℝ), (periodicBernoulli (2 * n + 3) x : ℂ) / (x : ℂ) ^ (s + 2 * n + 3)
  set g := Ring.choose (s + 2 * n) (2 * n + 1)
  have hA : A = (-((bernoulli (2 * n + 2) : ℂ) / (N : ℂ) ^ (s + 2 * n + 1)) +
      (s + 2 * n + 1) * B) / (2 * n + 2) := by
    rw [eq_div_iff hn2, mul_comm]; linear_combination h1
  have hB : B = (s + 2 * n + 2) * C / (2 * n + 3) := by
    rw [eq_div_iff hn3, mul_comm]; linear_combination h2
  rw [hA, hB]
  field_simp

/-- The right side of DLMF 25.2.9. -/
noncomputable def eulerMaclaurinZetaRHS (N n : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.Icc (1 : ℕ) N, 1 / (k : ℂ) ^ s + (N : ℂ) ^ (1 - s) / (s - 1) -
    1 / 2 * (N : ℂ) ^ (-s) +
    ∑ k ∈ Finset.Icc (1 : ℕ) n, Ring.choose (s + 2 * k - 2) (2 * k - 1) *
      ((bernoulli (2 * k) : ℂ) / (2 * k)) * (N : ℂ) ^ (1 - s - 2 * k) -
    Ring.choose (s + 2 * n) (2 * n + 1) *
      ∫ x in Ioi (N : ℝ), (periodicBernoulli (2 * n + 1) x : ℂ) / (x : ℂ) ^ (s + 2 * n + 1)

/-- Identity under the stated parameter and domain assumptions: `eulerMaclaurinZetaRHS N (n + 1) s =
eulerMaclaurinZetaRHS N n s`. -/
private lemma eulerMaclaurinZetaRHS_succ {s : ℂ} {n N : ℕ} (hN : 1 ≤ N) (hs : -(2 * n : ℝ) < s.re) :
    eulerMaclaurinZetaRHS N (n + 1) s = eulerMaclaurinZetaRHS N n s := by
  have h := choose_mul_integral_periodicBernoulli_double_step hN hs
  unfold eulerMaclaurinZetaRHS
  rw [sum_Icc_succ_top (by omega), show 2 * (n + 1) - 1 = 2 * n + 1 by omega,
    show 2 * (n + 1) = 2 * n + 2 by ring, show 2 * n + 2 + 1 = 2 * n + 3 by ring, h]
  have e1 : s + 2 * ((n + 1 : ℕ) : ℂ) - 2 = s + 2 * n := by push_cast; ring
  have e2 : s + 2 * ((n + 1 : ℕ) : ℂ) = s + 2 * n + 2 := by push_cast; ring
  have e3 : s + 2 * ((n + 1 : ℕ) : ℂ) + 1 = s + 2 * n + 3 := by push_cast; ring
  have e4 : (1 : ℂ) - s - 2 * ((n + 1 : ℕ) : ℂ) = -(s + 2 * n + 1) := by push_cast; ring
  have e5 : (2 * ((n + 1 : ℕ) : ℂ)) = 2 * n + 2 := by push_cast; ring
  rw [e1, e3, e2, e4, e5]
  ring

/-- Identity under the stated parameter and domain assumptions: `riemannZeta s = eulerMaclaurinZetaRHS N n
s`. -/
private lemma riemannZeta_eq_eulerMaclaurinZetaRHS_of_one_lt_re {s : ℂ} (hs : 1 < s.re) {N : ℕ} (hN : 1 ≤ N) (n : ℕ) :
    riemannZeta s = eulerMaclaurinZetaRHS N n s := by
  induction n with
  | zero =>
    rw [riemannZeta_eq_sum_add_integral_periodicBernoulli_one hs hN, eulerMaclaurinZetaRHS]
    simp [Ring.choose_one_right]
  | succ n ih =>
    rw [eulerMaclaurinZetaRHS_succ hN (by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith), ih]

/-- `s ↦ ∫_a^∞ f(x) x^{-(s+c)} dx` is holomorphic on `Re(s+c) > 1` for bounded measurable `f`,
`a ≥ 1`. -/
private lemma differentiableOn_integral_bdd_div_cpow {f : ℝ → ℝ} (hf : Measurable f) {D : ℝ}
    (hD : ∀ x, |f x| ≤ D) (c : ℂ) {a : ℝ} (ha : 1 ≤ a) :
    DifferentiableOn ℂ (fun s : ℂ => ∫ x in Ioi a, (f x : ℂ) / (x : ℂ) ^ (s + c))
      {s | 1 < (s + c).re} := by
  have ha0 : 0 < a := by linarith
  have hcont : Continuous fun s : ℂ => (s + c).re :=
    continuous_re.comp (continuous_id.add continuous_const)
  refine Complex.differentiableOn_integral_Ioi_of_locally_dominated
    (isOpen_lt continuous_const hcont) a ?_ ?_ ?_
  · intro s hs
    exact (integrableOn_bdd_div_cpow hf hD hs ha0).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (by linarith [mem_Ioi.mp ht] : t ≠ 0)
    intro s _
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (differentiableAt_const _).div ?_ (cpow_ne_zero_iff.mpr (Or.inl ht0))
    exact (differentiableAt_id.add_const c).const_cpow (Or.inl ht0)
  · intro s0 hs0
    set σ := (1 + (s0 + c).re) / 2 with hσ
    have hs0' : 1 < (s0 + c).re := hs0
    have hσ1 : 1 < σ := by rw [hσ]; linarith
    refine ⟨{s | σ < (s + c).re}, (isOpen_lt continuous_const hcont).mem_nhds (by
      show σ < (s0 + c).re; rw [hσ]; linarith), fun t => D * t ^ (-σ),
      (integrableOn_Ioi_rpow_of_lt (by linarith) ha0).const_mul D, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht s hs
    have ht1 : 1 ≤ t := by linarith [mem_Ioi.mp ht]
    have ht0 : 0 < t := by linarith
    change σ < (s + c).re at hs
    rw [norm_div, norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real, Real.norm_eq_abs,
      div_eq_mul_inv, ← Real.rpow_neg ht0.le]
    exact mul_le_mul (hD t) (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith))
      (by positivity) ((abs_nonneg _).trans (hD t))

/-- The right side of 25.2.9 is holomorphic on `Re s > -2n`, `s ≠ 1`. -/
private lemma differentiableOn_eulerMaclaurinZetaRHS {N : ℕ} (hN : 1 ≤ N) (n : ℕ) :
    DifferentiableOn ℂ (eulerMaclaurinZetaRHS N n) ({s : ℂ | -(2 * n : ℝ) < s.re} \ {1}) := by
  obtain ⟨D, hD⟩ := exists_abs_periodicBernoulli_le (2 * n + 1)
  have hJ := differentiableOn_integral_bdd_div_cpow (measurable_periodicBernoulli (2 * n + 1)) hD
    (2 * n + 1) (a := N) (by exact_mod_cast hN)
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hpow : ∀ (k : ℕ), 1 ≤ k → Differentiable ℂ fun s : ℂ => (k : ℂ) ^ s := by
    intro k hk s
    exact differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast (by omega : k ≠ 0)))
  have hpoly : ∀ m : ℕ, Differentiable ℂ fun z : ℂ => (descPochhammer ℂ m).eval z :=
    fun m => Polynomial.differentiable _
  intro s hs
  obtain ⟨hs1, hs2⟩ := hs
  change -(2 * n : ℝ) < s.re at hs1
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs2
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold eulerMaclaurinZetaRHS
  refine DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub
    (DifferentiableAt.add ?_ ?_) ?_) ?_) (DifferentiableAt.mul ?_ ?_)
  · refine DifferentiableAt.fun_sum fun k hk => ?_
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    exact (differentiableAt_const _).div (hpow k hk1 s)
      (cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast (by omega : k ≠ 0))))
  · exact ((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl hN0) |>.div
      (differentiableAt_id.sub_const 1) hs1'
  · exact (differentiableAt_id.neg.const_cpow (Or.inl hN0)).const_mul _
  · refine DifferentiableAt.fun_sum fun k _ => ?_
    refine DifferentiableAt.mul (DifferentiableAt.mul ?_ (differentiableAt_const _)) ?_
    · simp_rw [Ring.choose_eq_descPochhammer_div]
      exact (((hpoly _) _).comp s ((differentiableAt_id.add_const _).sub_const _)).div_const _
    · exact (((differentiableAt_const _).sub differentiableAt_id).sub_const _).const_cpow
        (Or.inl hN0)
  · simp_rw [Ring.choose_eq_descPochhammer_div]
    exact (((hpoly _) _).comp s (differentiableAt_id.add_const _)).div_const _
  · have hmem : s ∈ {s : ℂ | 1 < (s + (2 * n + 1)).re} := by
      simp only [mem_ofPred_eq, add_re]; simp; linarith
    have := (hJ s hmem).differentiableAt ((isOpen_lt continuous_const
      (continuous_re.comp (continuous_id.add continuous_const))).mem_nhds hmem)
    convert this using 2 with z
    simp only [add_assoc]

/-- The domain `Re s > -2n` minus the ray `[1, ∞)`, star-shaped about `0`. -/
private lemma isPreconnected_re_gt_neg_two_mul_diff_ray {n : ℕ} (hn1 : 1 ≤ n) :
    IsPreconnected ({s : ℂ | -(2 * n : ℝ) < s.re} \ {s : ℂ | s.im = 0 ∧ 1 ≤ s.re}) := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  refine (StarConvex.isPathConnected (a := 0) ?_ ?_).isConnected.isPreconnected
  · intro z hz a b ha hb hab
    have hz1 : -(2 * n : ℝ) < z.re := hz.1
    have hz2 : ¬ (z.im = 0 ∧ 1 ≤ z.re) := hz.2
    rw [smul_zero, zero_add, Complex.real_smul]
    refine ⟨?_, ?_⟩
    · show -(2 * n : ℝ) < ((b : ℂ) * z).re
      rw [re_ofReal_mul]
      rcases eq_or_lt_of_le hb with rfl | hb'
      · simp; linarith
      · nlinarith
    · rintro ⟨him, hre⟩
      rw [im_ofReal_mul] at him
      rw [re_ofReal_mul] at hre
      rcases eq_or_lt_of_le hb with rfl | hb'
      · simp at hre; linarith
      · have hzi : z.im = 0 := by
          rcases mul_eq_zero.mp him with h | h
          · linarith
          · exact h
        have hb1 : b ≤ 1 := by linarith
        have : z.re < 1 := by
          by_contra h; exact hz2 ⟨hzi, not_lt.mp h⟩
        nlinarith
  · refine ⟨?_, ?_⟩
    · show -(2 * n : ℝ) < (0 : ℂ).re
      simp; linarith
    · rintro ⟨-, h⟩; simp at h; linarith

/-- 25.2.9 as an identity with `eulerMaclaurinZetaRHS`. -/
theorem riemannZeta_eq_eulerMaclaurinZetaRHS {s : ℂ} {n N : ℕ} (hn : 1 ≤ n) (hN : 1 ≤ N)
    (hs : -(2 * n : ℝ) < s.re) (hs1 : s ≠ 1) : riemannZeta s = eulerMaclaurinZetaRHS N n s := by
  set V : Set ℂ := {s : ℂ | -(2 * n : ℝ) < s.re} \ {s : ℂ | s.im = 0 ∧ 1 ≤ s.re} with hV
  have hVo : IsOpen V := (isOpen_lt continuous_const continuous_re).sdiff
    ((isClosed_eq continuous_im continuous_const).inter
      (isClosed_le continuous_const continuous_re))
  have hsub : V ⊆ {s : ℂ | -(2 * n : ℝ) < s.re} \ {1} := by
    rintro z ⟨hz1, hz2⟩
    refine ⟨hz1, fun h => hz2 ?_⟩
    rw [mem_singleton_iff.mp h]; simp
  have hζ : DifferentiableOn ℂ riemannZeta V := fun z hz =>
    (differentiableAt_riemannZeta (hsub hz).2).differentiableWithinAt
  have hR := (differentiableOn_eulerMaclaurinZetaRHS hN n).mono hsub
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hz0 : (2 + I : ℂ) ∈ V := by
    refine ⟨?_, ?_⟩
    · show -(2 * n : ℝ) < (2 + I : ℂ).re
      simp; linarith
    · rintro ⟨h, -⟩; simp at h
  have hev : riemannZeta =ᶠ[𝓝 (2 + I : ℂ)] eulerMaclaurinZetaRHS N n := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show (1 : ℝ) < (2 + I : ℂ).re by simp)] with z hz
    exact riemannZeta_eq_eulerMaclaurinZetaRHS_of_one_lt_re hz hN n
  have heq := (hζ.analyticOnNhd hVo).eqOn_of_preconnected_of_eventuallyEq
    (hR.analyticOnNhd hVo) (isPreconnected_re_gt_neg_two_mul_diff_ray hn) hz0 hev
  by_cases hsV : s ∈ V
  · exact heq hsV
  · have hray : s.im = 0 ∧ 1 ≤ s.re := by
      by_contra h; exact hsV ⟨hs, h⟩
    have hre : 1 < s.re := by
      rcases eq_or_lt_of_le hray.2 with h | h
      · exfalso; apply hs1; apply Complex.ext <;> simp [hray.1, ← h]
      · exact h
    exact riemannZeta_eq_eulerMaclaurinZetaRHS_of_one_lt_re hre hN n

/-- DLMF 25.2.8: for `Re s > 0`, `s ≠ 1` and `N ≥ 1`,
`ζ(s) = ∑_{k=1}^{N} k^{-s} + N^{1-s}/(s-1) - s ∫_N^∞ (x - ⌊x⌋) x^{-s-1} dx`; the integral
converges absolutely. -/
@[dlmf 25.2.E8]
theorem riemannZeta_eq_sum_add_integral_fract {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {N : ℕ}
    (hN : 1 ≤ N) :
    IntegrableOn (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) / (x : ℂ) ^ (s + 1)) (Ioi (N : ℝ)) ∧
      riemannZeta s = ∑ k ∈ Finset.Icc (1 : ℕ) N, 1 / (k : ℂ) ^ s + (N : ℂ) ^ (1 - s) / (s - 1) -
        s * ∫ x in Ioi (N : ℝ), ((Int.fract x : ℝ) : ℂ) / (x : ℂ) ^ (s + 1) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hfr : ∀ x : ℝ, |Int.fract x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (Int.fract_nonneg x)]; exact (Int.fract_lt_one x).le
  have hw : 1 < (s + 1).re := by simp; linarith
  have hI := integrableOn_bdd_div_cpow measurable_fract hfr hw hN0
  refine ⟨hI, ?_⟩
  obtain ⟨D, hD⟩ := exists_abs_periodicBernoulli_le 1
  have hJ := integrableOn_bdd_div_cpow (measurable_periodicBernoulli 1) hD hw hN0
  have hP := integrableOn_Ioi_cpow_of_lt (a := -(s + 1)) (by simp; linarith) hN0
  have h1 := riemannZeta_eq_eulerMaclaurinZetaRHS (n := 1) le_rfl hN (by simp; linarith) hs1
  have h0 : eulerMaclaurinZetaRHS N 1 s = eulerMaclaurinZetaRHS N 0 s := eulerMaclaurinZetaRHS_succ hN (by simpa using hs)
  rw [h0, eulerMaclaurinZetaRHS] at h1
  simp at h1
  have hsplit : ∫ x in Ioi (N : ℝ), ((Int.fract x : ℝ) : ℂ) / (x : ℂ) ^ (s + 1) =
      (∫ x in Ioi (N : ℝ), (periodicBernoulli 1 x : ℂ) / (x : ℂ) ^ (s + 1)) +
        1 / 2 * ∫ x in Ioi (N : ℝ), (x : ℂ) ^ (-(s + 1)) := by
    rw [← integral_const_mul, ← integral_add hJ (hP.const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [periodicBernoulli, bernoulliFun_one, cpow_neg]
    push_cast
    ring
  rw [hsplit, integral_Ioi_cpow_of_lt (by simp; linarith) hN0, h1]
  rw [show -(s + 1) + 1 = -s by ring, ofReal_natCast]
  field_simp
  ring

/-! ### §25.2(ii) The alternating series (DLMF 25.2.3), from 25.2.8 -/

/-- A sequence converging along the even and along the odd indices converges. -/
private lemma tendsto_of_tendsto_two_mul_of_tendsto_two_mul_add_one {f : ℕ → ℂ} {L : ℂ}
    (h0 : Tendsto (fun M => f (2 * M)) atTop (𝓝 L))
    (h1 : Tendsto (fun M => f (2 * M + 1)) atTop (𝓝 L)) : Tendsto f atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop] at *
  intro ε hε
  obtain ⟨A, hA⟩ := h0 ε hε
  obtain ⟨B, hB⟩ := h1 ε hε
  refine ⟨2 * A + 2 * B + 1, fun n hn => ?_⟩
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · exact hA m (by omega)
  · exact hB m (by omega)

/-- The tail `∫_N^∞ (x - ⌊x⌋) x^{-s-1} dx` tends to `0` for `Re s > 0`. -/
private lemma tendsto_integral_Ioi_fract_div_cpow {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ => ∫ x in Ioi (N : ℝ), ((Int.fract x : ℝ) : ℂ) / (x : ℂ) ^ (s + 1))
      atTop (𝓝 0) := by
  have hfr : ∀ x : ℝ, |Int.fract x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (Int.fract_nonneg x)]; exact (Int.fract_lt_one x).le
  have hI := integrableOn_bdd_div_cpow measurable_fract hfr (w := s + 1)
    (by simp; linarith) (a := 1) one_pos
  have h := tendsto_setIntegral_of_antitone (μ := volume)
    (f := fun x : ℝ => ((Int.fract x : ℝ) : ℂ) / (x : ℂ) ^ (s + 1))
    (s := fun N : ℕ => Ioi (N : ℝ)) (fun _ => measurableSet_Ioi)
    (fun a b hab => Ioi_subset_Ioi (by exact_mod_cast hab)) ⟨1, by simpa using hI⟩
  have he : (⋂ N : ℕ, Ioi (N : ℝ)) = ∅ := by
    ext x
    simp only [mem_iInter, Set.mem_Ioi, mem_empty_iff_false, iff_false, not_forall, not_lt]
    obtain ⟨N, hN⟩ := exists_nat_gt x
    exact ⟨N, hN.le⟩
  rwa [he, setIntegral_empty] at h

/-- `∑_{n<N} (-1)ⁿ (n+1)^{-s} = ∑_{k=1}^{2M} k^{-s} - 2^{1-s} ∑_{k=1}^{M} k^{-s}` for `N = 2M`. -/
private lemma sum_range_two_mul_alternating_eq (s : ℂ) (M : ℕ) :
    ∑ n ∈ range (2 * M), (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s =
      ∑ k ∈ Finset.Icc (1 : ℕ) (2 * M), 1 / (k : ℂ) ^ s -
        2 ^ (1 - s) * ∑ k ∈ Finset.Icc (1 : ℕ) M, 1 / (k : ℂ) ^ s := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega)]
    have hp : ((2 * M + 1 + 1 : ℕ) : ℂ) ^ s = 2 ^ s * ((M + 1 : ℕ) : ℂ) ^ s := by
      rw [show ((2 * M + 1 + 1 : ℕ) : ℂ) = ((2 : ℝ) : ℂ) * (((M + 1 : ℕ) : ℝ) : ℂ) by
        push_cast; ring, mul_cpow_ofReal_nonneg (by norm_num) (by positivity)]
      push_cast; rfl
    have h2 : (2 : ℂ) ^ (1 - s) = 2 / 2 ^ s := by
      rw [cpow_sub _ _ two_ne_zero, cpow_one]
    have hne : (2 : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
    have hne' : ((M + 1 : ℕ) : ℂ) ^ s ≠ 0 :=
      cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast (by omega : M + 1 ≠ 0)))
    have e1 : (-1 : ℂ) ^ (2 * M) = 1 := by rw [pow_mul]; norm_num
    have e2 : (-1 : ℂ) ^ (2 * M + 1) = -1 := by rw [pow_succ, e1]; ring
    rw [e1, e2, h2, hp]
    have c1 : (((2 * M : ℕ) : ℂ) + 1) = ((2 * M + 1 : ℕ) : ℂ) := by push_cast; ring
    have c2 : (((2 * M + 1 : ℕ) : ℂ) + 1) = ((2 * M + 1 + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [c1, c2, hp]
    field_simp
    ring

/-- DLMF 25.2.3 in multiplied form: for `Re s > 0`, `s ≠ 1`, the partial sums of the alternating
series `∑_{n≥1} (-1)^{n-1} n^{-s}` converge to `(1 - 2^{1-s}) ζ(s)`. The series converges only
conditionally for `Re s ≤ 1`, so natural-order partial sums are used. This form also covers the
points `s = 1 + 2πik/ln 2`, `k ≠ 0`, where DLMF's factor `1/(1 - 2^{1-s})` is undefined. -/
@[dlmf 25.2.E3]
theorem tendsto_alternating_partial_sums {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s) atTop
      (𝓝 ((1 - 2 ^ (1 - s)) * riemannZeta s)) := by
  set I : ℕ → ℂ := fun N => ∫ x in Ioi (N : ℝ), ((Int.fract x : ℝ) : ℂ) / (x : ℂ) ^ (s + 1)
    with hIdef
  have hA : ∀ N : ℕ, 1 ≤ N → ∑ k ∈ Finset.Icc (1 : ℕ) N, 1 / (k : ℂ) ^ s =
      riemannZeta s - (N : ℂ) ^ (1 - s) / (s - 1) + s * I N := fun N hN => by
    rw [(riemannZeta_eq_sum_add_integral_fract hs hs1 hN).2]; ring
  have hev : ∀ M : ℕ, 1 ≤ M → ∑ n ∈ range (2 * M), (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s =
      (1 - 2 ^ (1 - s)) * riemannZeta s + s * (I (2 * M) - 2 ^ (1 - s) * I M) := by
    intro M hM
    rw [sum_range_two_mul_alternating_eq, hA _ (by omega), hA _ hM]
    have hp : ((2 * M : ℕ) : ℂ) ^ (1 - s) = 2 ^ (1 - s) * (M : ℂ) ^ (1 - s) := by
      rw [show ((2 * M : ℕ) : ℂ) = ((2 : ℝ) : ℂ) * ((M : ℝ) : ℂ) by push_cast; ring,
        mul_cpow_ofReal_nonneg (by norm_num) (by positivity)]
      push_cast; rfl
    rw [hp]
    ring
  have hT := tendsto_integral_Ioi_fract_div_cpow hs
  have h2M : Tendsto (fun M : ℕ => 2 * M) atTop atTop :=
    tendsto_atTop_mono (fun M => by simp; omega) tendsto_id
  have hlim0 : Tendsto (fun M : ℕ => (1 - 2 ^ (1 - s)) * riemannZeta s +
      s * (I (2 * M) - 2 ^ (1 - s) * I M)) atTop
      (𝓝 ((1 - 2 ^ (1 - s)) * riemannZeta s)) := by
    have := tendsto_const_nhds (x := (1 - 2 ^ (1 - s)) * riemannZeta s) (f := (atTop : Filter ℕ))
      |>.add (((hT.comp h2M).sub (hT.const_mul (2 ^ (1 - s)))).const_mul s)
    simp only [mul_zero, sub_zero, add_zero] at this
    exact this
  have hE : Tendsto (fun M : ℕ => ∑ n ∈ range (2 * M), (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s) atTop
      (𝓝 ((1 - 2 ^ (1 - s)) * riemannZeta s)) :=
    hlim0.congr' (eventually_atTop.mpr ⟨1, fun M hM => (hev M hM).symm⟩)
  refine tendsto_of_tendsto_two_mul_of_tendsto_two_mul_add_one hE ?_
  have hterm : Tendsto (fun M : ℕ => (-1 : ℂ) ^ (2 * M) / ((2 * M : ℕ) + 1 : ℂ) ^ s) atTop
      (𝓝 0) := by
    have hc := (tendsto_ofReal_cpow_atTop_of_re_neg (z := -s) (by simp; linarith)).comp
      (tendsto_atTop_mono (fun M : ℕ => (by
        have : (0 : ℝ) ≤ M := M.cast_nonneg
        linarith : (M : ℝ) ≤ 2 * M + 1)) tendsto_natCast_atTop_atTop)
    refine hc.congr fun M => ?_
    simp only [Function.comp_apply, pow_mul, neg_one_sq, one_pow, cpow_neg, one_div]
    push_cast; ring_nf
  simpa [sum_range_succ] using hE.add hterm

/-- DLMF 25.2.3 as printed, `ζ(s) = (1 - 2^{1-s})⁻¹ ∑_{n≥1} (-1)^{n-1} n^{-s}`, where the
series is the limit of its partial sums; for `Re s > 0` with `2^{1-s} ≠ 1` (this excludes
`s = 1` and the zeros of the factor). -/
@[dlmf 25.2.E3]
theorem riemannZeta_eq_alternating {s : ℂ} (hs : 0 < s.re) (h2 : (2 : ℂ) ^ (1 - s) ≠ 1) :
    riemannZeta s = 1 / (1 - 2 ^ (1 - s)) *
      limUnder atTop (fun N : ℕ => ∑ n ∈ range N, (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s) := by
  have hs1 : s ≠ 1 := by rintro rfl; simp at h2
  rw [(tendsto_alternating_partial_sums hs hs1).limUnder_eq]
  have : (1 : ℂ) - 2 ^ (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm h2)
  field_simp

/-- DLMF 25.2.9: for `n, N ≥ 1`, `Re s > -2n`, `s ≠ 1`,
`ζ(s) = ∑_{k=1}^{N} k^{-s} + N^{1-s}/(s-1) - N^{-s}/2
  + ∑_{k=1}^{n} binom(s+2k-2, 2k-1) (B_{2k}/2k) N^{1-s-2k}
  - binom(s+2n, 2n+1) ∫_N^∞ B̃_{2n+1}(x) x^{-s-2n-1} dx`,
with `B̃_{2n+1}(x) = B_{2n+1}(x - ⌊x⌋)`; the integral converges absolutely. -/
@[dlmf 25.2.E9]
theorem riemannZeta_eq_eulerMaclaurin {s : ℂ} {n N : ℕ} (hn : 1 ≤ n) (hN : 1 ≤ N)
    (hs : -(2 * n : ℝ) < s.re) (hs1 : s ≠ 1) :
    IntegrableOn (fun x : ℝ => (periodicBernoulli (2 * n + 1) x : ℂ) /
        (x : ℂ) ^ (s + 2 * n + 1)) (Ioi (N : ℝ)) ∧
      riemannZeta s = ∑ k ∈ Finset.Icc (1 : ℕ) N, 1 / (k : ℂ) ^ s + (N : ℂ) ^ (1 - s) / (s - 1) -
        1 / 2 * (N : ℂ) ^ (-s) +
        ∑ k ∈ Finset.Icc (1 : ℕ) n, Ring.choose (s + 2 * k - 2) (2 * k - 1) *
          ((bernoulli (2 * k) : ℂ) / (2 * k)) * (N : ℂ) ^ (1 - s - 2 * k) -
        Ring.choose (s + 2 * n) (2 * n + 1) *
          ∫ x in Ioi (N : ℝ), (periodicBernoulli (2 * n + 1) x : ℂ) /
            (x : ℂ) ^ (s + 2 * n + 1) := by
  obtain ⟨D, hD⟩ := exists_abs_periodicBernoulli_le (2 * n + 1)
  refine ⟨integrableOn_bdd_div_cpow (measurable_periodicBernoulli _) hD
    (by simp; linarith) (by exact_mod_cast hN), ?_⟩
  exact riemannZeta_eq_eulerMaclaurinZetaRHS hn hN hs hs1

/-- DLMF 25.2.10: for `n ≥ 1`, `Re s > -2n`, `s ≠ 1`,
`ζ(s) = 1/(s-1) + 1/2 + ∑_{k=1}^{n} binom(s+2k-2, 2k-1) B_{2k}/(2k)
  - binom(s+2n, 2n+1) ∫_1^∞ B̃_{2n+1}(x) x^{-s-2n-1} dx` (the case `N = 1` of 25.2.9). -/
@[dlmf 25.2.E10]
theorem riemannZeta_eq_eulerMaclaurin_one {s : ℂ} {n : ℕ} (hn : 1 ≤ n)
    (hs : -(2 * n : ℝ) < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = 1 / (s - 1) + 1 / 2 +
        ∑ k ∈ Finset.Icc (1 : ℕ) n, Ring.choose (s + 2 * k - 2) (2 * k - 1) *
          ((bernoulli (2 * k) : ℂ) / (2 * k)) -
        Ring.choose (s + 2 * n) (2 * n + 1) *
          ∫ x in Ioi (1 : ℝ), (periodicBernoulli (2 * n + 1) x : ℂ) /
            (x : ℂ) ^ (s + 2 * n + 1) := by
  have h := (riemannZeta_eq_eulerMaclaurin hn le_rfl hs hs1).2
  rw [h]
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  simp only [Nat.cast_one, one_cpow, Finset.Icc_self, sum_singleton, mul_one]
  ring

/-! ### §25.2(iv) Infinite products -/

/-- DLMF 25.2.12 (Hadamard product): for `s ≠ 1`,
`ζ(s) = (2π)^s e^{-s-γs/2} / (2(s-1) Γ(s/2+1)) ∏_ρ (1 - s/ρ) e^{s/ρ}`, the product over the zeros
`ρ` of `ζ` with `Re ρ > 0`, each repeated according to its multiplicity. The product converges
absolutely (unconditionally). `1/Γ(s/2+1)` is written `(Γ(s/2+1))⁻¹`, which is Lean's value `0`
at the poles `s = -2, -4, …`, matching the trivial zeros. -/
@[dlmf 25.2.E12]
theorem riemannZeta_hadamard_product {s : ℂ} (hs : s ≠ 1) :
    ∃ P : ℂ, HasProd (fun ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re} =>
        ((1 - s / ρ) * exp (s / ρ)) ^ analyticOrderNatAt riemannZeta (ρ : ℂ)) P ∧
      riemannZeta s = (2 * π) ^ s * exp (-s - Real.eulerMascheroniConstant * s / 2) /
        (2 * (s - 1)) * (Gamma (s / 2 + 1))⁻¹ * P := by
  sorry

end DLMF.Zeta
