/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Calculus.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Calculus of one variable (DLMF §1.4)

Most of DLMF §1.4 is in Mathlib; the pointers are in
`DLMF.AlgebraicAnalytic.Calculus.MathlibCoverage`. This file states the remaining items:

* the ε–δ form 1.4.2 of right continuity;
* the antiderivatives 1.4.17 and the linear combination 1.4.19;
* improper integrals at a finite endpoint 1.4.23 and absolute convergence (§1.4(v));
* absolutely continuous and discrete Stieltjes measures 1.4.23_1–1.4.23_3;
* principal values of integrable functions (1.4.24–1.4.25);
* the first and second mean value theorems for integrals 1.4.29–1.4.30, repeated integrals
  1.4.31, the total variation formula 1.4.34;
* L'Hôpital's rule for `∞/∞` (1.4.14–1.4.15) and Faà di Bruno's formula 1.4.13;
* extrema on a closed interval (§1.4(vii)) and the derivative criteria for convexity
  (§1.4(viii)).
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal Nat

namespace DLMF.AlgebraicAnalytic

/-! ### §1.4(ii) Continuity -/

/-- DLMF 1.4.1–1.4.2: `f` is continuous on the right at `c` iff for every `ε > 0` there is
`δ > 0` with `|f(c + α) - f(c)| < ε` for all `0 ≤ α < δ`. -/
@[dlmf 1.4.E1, dlmf 1.4.E2]
theorem continuousWithinAt_Ici_iff_eps_delta {f : ℝ → ℝ} {c : ℝ} :
    ContinuousWithinAt f (Ici c) c ↔
      ∀ ε > 0, ∃ δ > 0, ∀ α, 0 ≤ α → α < δ → |f (c + α) - f c| < ε := by
  rw [Metric.continuousWithinAt_iff]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, h⟩ := h ε hε
    refine ⟨δ, hδ, fun α hα hαδ => ?_⟩
    have := h (x := c + α) (by simpa using hα)
      (by simpa [Real.dist_eq, abs_of_nonneg hα] using hαδ)
    simpa [Real.dist_eq] using this
  · intro h ε hε
    obtain ⟨δ, hδ, h⟩ := h ε hε
    refine ⟨δ, hδ, fun {x} hx hxδ => ?_⟩
    have hx' : 0 ≤ x - c := sub_nonneg.mpr hx
    have := h (x - c) hx' (by rwa [Real.dist_eq, abs_of_nonneg hx'] at hxδ)
    simpa [Real.dist_eq] using this

/-! ### §1.4(iii) Derivatives -/

/-- DLMF 1.4.13 (Faà di Bruno's formula): for `f`, `g` of class `Cⁿ`,
`dⁿ/dxⁿ f(g(x)) = ∑ n!/(m₁! ⋯ mₙ!) f^{(k)}(g(x)) ∏ⱼ (g^{(j)}(x)/j!)^{mⱼ}`, the sum over
`m₁ + 2m₂ + ⋯ + nmₙ = n` (here `m : Fin n → Fin (n + 1)`, `mⱼ ≤ n` being automatic) and
`k = m₁ + ⋯ + mₙ`. -/
@[dlmf 1.4.E13]
theorem iteratedDeriv_comp_faaDiBruno {f g : ℝ → ℝ} (n : ℕ) (hf : ContDiff ℝ n f)
    (hg : ContDiff ℝ n g) (x : ℝ) :
    iteratedDeriv n (f ∘ g) x =
      ∑ m ∈ (Finset.univ : Finset (Fin n → Fin (n + 1))).filter
          (fun m => ∑ j : Fin n, (j.val + 1) * (m j).val = n),
        ((n ! : ℝ) / ∏ j : Fin n, ((m j).val ! : ℝ)) *
          iteratedDeriv (∑ j : Fin n, (m j).val) f (g x) *
          ∏ j : Fin n, (iteratedDeriv (j.val + 1) g x / ((j.val + 1) ! : ℝ)) ^ (m j).val := by
  sorry

/-- DLMF 1.4.14–1.4.15 (L'Hôpital's rule, case `∞/∞`): if `f` and `g` are differentiable in a
punctured neighbourhood of `a`, `g' ≠ 0` there, `|g(x)| → ∞` as `x → a`, and
`f'(x)/g'(x) → l`, then `f(x)/g(x) → l`. (No hypothesis on `f` is needed beyond
differentiability; the case `0/0` is Mathlib's `deriv.lhopital_zero_nhdsNE`.) -/
@[dlmf 1.4.E14, dlmf 1.4.E15]
theorem lhopital_atTop_nhdsNE {f g : ℝ → ℝ} {a l : ℝ}
    (hf : ∀ᶠ x in 𝓝[≠] a, DifferentiableAt ℝ f x)
    (hg : ∀ᶠ x in 𝓝[≠] a, DifferentiableAt ℝ g x)
    (hg' : ∀ᶠ x in 𝓝[≠] a, deriv g x ≠ 0)
    (hgtop : Tendsto (fun x => |g x|) (𝓝[≠] a) atTop)
    (hdiv : Tendsto (fun x => deriv f x / deriv g x) (𝓝[≠] a) (𝓝 l)) :
    Tendsto (fun x => f x / g x) (𝓝[≠] a) (𝓝 l) := by
  sorry

/-! ### §1.4(iv) Indefinite integrals -/

/-- DLMF 1.4.17, case `n ≠ -1`: `x^{n+1}/(n+1)` is an antiderivative of `xⁿ` for an integer
`n ≠ -1` (at `x ≠ 0`; for `n ≥ 0` at every `x`, `hasDerivAt_pow_succ_div`). -/
@[dlmf 1.4.E17]
theorem hasDerivAt_zpow_succ_div {n : ℤ} (hn : n ≠ -1) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun x : ℝ => x ^ (n + 1) / (n + 1)) (x ^ n) x := by
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by
    intro h
    apply hn
    exact_mod_cast (eq_neg_of_add_eq_zero_left h)
  have := (hasDerivAt_zpow (n + 1) x (Or.inl hx)).div_const ((n : ℝ) + 1)
  convert this using 1
  rw [add_sub_cancel_right]
  field_simp
  push_cast
  ring

/-- DLMF 1.4.17, case `n ≥ 0`: `x^{n+1}/(n+1)` is an antiderivative of `xⁿ` on `ℝ`. -/
@[dlmf 1.4.E17]
theorem hasDerivAt_pow_succ_div (n : ℕ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => x ^ (n + 1) / (n + 1)) (x ^ n) x := by
  have := (hasDerivAt_pow (n + 1) x).div_const ((n : ℝ) + 1)
  convert this using 1
  field_simp
  push_cast
  ring

/-- DLMF 1.4.17, case `n = -1`: `ln |x|` is an antiderivative of `1/x` on `x ≠ 0`. -/
@[dlmf 1.4.E17]
theorem hasDerivAt_log_abs {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.log |x|) x⁻¹ x := by
  simpa [Real.log_abs] using Real.hasDerivAt_log hx

/-! ### §1.4(v) Definite integrals -/

/-- DLMF 1.4.19: linearity of the integral, `∫ₐᵇ (c f + d g) = c ∫ₐᵇ f + d ∫ₐᵇ g`. -/
@[dlmf 1.4.E19]
theorem integral_const_mul_add_const_mul {f g : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b) (c d : ℝ) :
    ∫ x in a..b, (c * f x + d * g x) = c * (∫ x in a..b, f x) + d * ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_add (hf.const_mul c) (hg.const_mul d),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- DLMF 1.4.23: an integral that is improper at the upper endpoint `b` (for instance
`f(b) = ±∞`) is the limit `lim_{c → b-} ∫ₐᶜ f`. Stated for `f` Lebesgue integrable on
`(a, b)`, whose integral is then this limit. -/
@[dlmf 1.4.E23]
theorem tendsto_integral_nhdsLT_of_integrableOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {a b : ℝ} (hab : a < b) (hf : IntegrableOn f (Ioo a b)) :
    Tendsto (fun c => ∫ x in a..c, f x) (𝓝[<] b) (𝓝 (∫ x in a..b, f x)) := by
  have hf' : IntegrableOn f (uIcc a b) := by
    rw [uIcc_of_le hab.le]
    exact (integrableOn_Icc_iff_integrableOn_Ioo' (by simp) (by simp) (by simp) (by simp)).mpr hf
  have hc := intervalIntegral.continuousOn_primitive_interval hf'
  rw [uIcc_of_le hab.le] at hc
  exact (hc b (right_mem_Icc.mpr hab.le)).mono_of_mem_nhdsWithin (Icc_mem_nhdsLT hab)

/-- DLMF §1.4(v): absolute convergence of `∫ₐ^∞ f` implies its convergence: if `f` is
integrable on every `(a, b]` and `∫ₐᵇ |f|` converges as `b → ∞`, then so does `∫ₐᵇ f`, to the
Lebesgue integral over `(a, ∞)`. -/
@[dlmf 1.4.v]
theorem tendsto_integral_of_tendsto_integral_abs {f : ℝ → ℝ} {a L : ℝ}
    (hf : ∀ b, IntegrableOn f (Ioc a b))
    (h : Tendsto (fun b => ∫ x in a..b, |f x|) atTop (𝓝 L)) :
    Tendsto (fun b => ∫ x in a..b, f x) atTop (𝓝 (∫ x in Ioi a, f x)) := by
  have hI : IntegrableOn f (Ioi a) :=
    integrableOn_Ioi_of_intervalIntegral_norm_tendsto L a hf tendsto_id
      (by simpa [Real.norm_eq_abs] using h)
  exact intervalIntegral_tendsto_integral_Ioi a hI tendsto_id

/-- DLMF 1.4.23_1: a nondecreasing (right-continuous) `α` with `α(d) - α(c) = ∫_c^d w` for a
weight `w ≥ 0` defines the absolutely continuous Stieltjes measure `dα = w dx`. -/
@[dlmf 1.4.E23_1]
theorem stieltjes_measure_eq_withDensity (α : StieltjesFunction ℝ) {w : ℝ → ℝ≥0}
    (hwi : ∀ c d, IntervalIntegrable (fun x => (w x : ℝ)) volume c d)
    (h : ∀ c d, c ≤ d → α d - α c = ∫ x in c..d, (w x : ℝ)) :
    α.measure = volume.withDensity (fun x => (w x : ℝ≥0∞)) := by
  refine Measure.ext_of_Ioc' _ _ (fun a b _ => by simp [α.measure_Ioc]) fun a b hab => ?_
  rw [α.measure_Ioc, withDensity_apply _ measurableSet_Ioc, h a b hab.le,
    intervalIntegral.integral_of_le hab.le,
    ofReal_integral_eq_lintegral_ofReal ((hwi a b).1) (Eventually.of_forall fun x => by simp)]
  simp

/-- DLMF 1.4.23_2: for an absolutely continuous Stieltjes measure `dα = w dx` (1.4.23_1),
`∫ f dα = ∫ f w dx` over any measurable set. -/
@[dlmf 1.4.E23_2]
theorem setIntegral_stieltjes_eq_integral_mul (α : StieltjesFunction ℝ) {w : ℝ → ℝ≥0}
    (hw : Measurable w) (hwi : ∀ c d, IntervalIntegrable (fun x => (w x : ℝ)) volume c d)
    (h : ∀ c d, c ≤ d → α d - α c = ∫ x in c..d, (w x : ℝ)) (f : ℝ → ℝ) {s : Set ℝ}
    (hs : MeasurableSet s) :
    ∫ x in s, f x ∂α.measure = ∫ x in s, f x * (w x : ℝ) := by
  rw [stieltjes_measure_eq_withDensity α hwi h,
    setIntegral_withDensity_eq_setIntegral_smul hw f hs]
  simp [NNReal.smul_def, mul_comm]

/-- DLMF 1.4.23_3: for the mixed measure `dα = w dx + ∑ₙ wₙ δ(x - xₙ) dx` with mass points
`xₙ ∈ (a, b)`, `∫ₐᵇ f dα = ∫ₐᵇ w f dx + ∑ₙ wₙ f(xₙ)`; `f w` is assumed integrable on `(a, b)`
(`f` continuous on `[a, b]` and `w` integrable suffice). -/
@[dlmf 1.4.E23_3]
theorem setIntegral_withDensity_add_dirac {w : ℝ → ℝ≥0} (hw : Measurable w) {N : ℕ}
    (wn : Fin N → ℝ≥0) (xn : Fin N → ℝ) {a b : ℝ} (hxn : ∀ n, xn n ∈ Ioo a b) {f : ℝ → ℝ}
    (hfm : Measurable f) (hfw : IntegrableOn (fun x => (w x : ℝ) * f x) (Ioo a b)) :
    ∫ x in Ioo a b, f x ∂(volume.withDensity (fun x => (w x : ℝ≥0∞)) +
        ∑ n, (wn n : ℝ≥0∞) • Measure.dirac (xn n)) =
      ∫ x in Ioo a b, (w x : ℝ) * f x + ∑ n, (wn n : ℝ) * f (xn n) := by
  sorry

/-- DLMF 1.4.24: for `f` integrable on `[a, b]` the principal value at `c ∈ (a, b)` exists and
equals the integral `∫ₐᵇ f`. -/
@[dlmf 1.4.E24]
theorem hasCauchyPrincipalValue_of_intervalIntegrable {f : ℝ → ℂ} {a b c : ℝ} (hac : a < c)
    (hcb : c < b) (hf : IntervalIntegrable f volume a b) :
    HasCauchyPrincipalValue f a b c (∫ x in a..b, f x) := by
  have hab : a ≤ b := (hac.trans hcb).le
  have hsub : ∀ t, a ≤ t → t ≤ b → uIcc a t ⊆ uIcc a b := fun t h1 h2 =>
    uIcc_subset_uIcc left_mem_uIcc (by rw [uIcc_of_le hab]; exact ⟨h1, h2⟩)
  have hsub' : ∀ t, a ≤ t → t ≤ b → uIcc t b ⊆ uIcc a b := fun t h1 h2 =>
    uIcc_subset_uIcc (by rw [uIcc_of_le hab]; exact ⟨h1, h2⟩) right_mem_uIcc
  refine ⟨hac, hcb, fun ε hε hε' => ?_, ?_⟩
  · have h1 := min_le_left (c - a) (b - c)
    have h2 := min_le_right (c - a) (b - c)
    exact ⟨hf.mono_set (hsub _ (by linarith) (by linarith)),
      hf.mono_set (hsub' _ (by linarith) (by linarith))⟩
  set F : ℝ → ℂ := fun t => ∫ x in a..t, f x with hFdef
  have hcont : ContinuousOn F (uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval' hf left_mem_uIcc
  have hcA : ContinuousAt F c := by
    refine hcont.continuousAt ?_
    rw [uIcc_of_le hab]
    exact Icc_mem_nhds hac hcb
  have t1 : Tendsto (fun ε : ℝ => c - ε) (𝓝[>] 0) (𝓝 c) := by
    have : Tendsto (fun ε : ℝ => c - ε) (𝓝 0) (𝓝 (c - 0)) := tendsto_const_nhds.sub tendsto_id
    simpa using this.mono_left nhdsWithin_le_nhds
  have t2 : Tendsto (fun ε : ℝ => c + ε) (𝓝[>] 0) (𝓝 c) := by
    have : Tendsto (fun ε : ℝ => c + ε) (𝓝 0) (𝓝 (c + 0)) := tendsto_const_nhds.add tendsto_id
    simpa using this.mono_left nhdsWithin_le_nhds
  have hlim := (hcA.tendsto.comp t1).add (tendsto_const_nhds (x := F b) |>.sub
    (hcA.tendsto.comp t2))
  simp only [add_sub_cancel] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min (sub_pos.2 hac) (sub_pos.2 hcb))] with ε hε
  have h1 := min_le_left (c - a) (b - c)
  have h2 := min_le_right (c - a) (b - c)
  have hε2 := hε.2
  have hε1 := hε.1
  simp only [Function.comp, hFdef]
  congr 1
  exact intervalIntegral.integral_interval_sub_left hf
    (hf.mono_set (hsub _ (by linarith) (by linarith)))

/-- DLMF 1.4.25: for `f` integrable on `ℝ` the principal value `lim_{b→∞} ∫_{-b}^{b} f` exists
and equals `∫_ℝ f`. -/
@[dlmf 1.4.E25]
theorem hasPrincipalValueAtInfinity_of_integrable {f : ℝ → ℂ} (hf : Integrable f) :
    HasPrincipalValueAtInfinity f (∫ x, f x) := by
  refine ⟨fun b _ => hf.intervalIntegrable, ?_⟩
  exact intervalIntegral_tendsto_integral hf tendsto_neg_atTop_atBot tendsto_id

/-- DLMF 1.4.29 (first mean value theorem for integrals): for `f` continuous and `ψ ≥ 0`
integrable on `[a, b]` there is `c ∈ [a, b]` with `∫ₐᵇ f ψ = f(c) ∫ₐᵇ ψ`. -/
@[dlmf 1.4.E29]
theorem exists_integral_mul_eq_mul_integral {f ψ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hψ : ∀ x ∈ Icc a b, 0 ≤ ψ x)
    (hψi : IntervalIntegrable ψ volume a b) :
    ∃ c ∈ Icc a b, ∫ x in a..b, f x * ψ x = f c * ∫ x in a..b, ψ x := by
  sorry

/-- DLMF 1.4.30 (second mean value theorem for integrals, Bonnet–du Bois-Reymond): for `f`
monotonic and `ψ` integrable on `[a, b]` there is `c ∈ [a, b]` with
`∫ₐᵇ f ψ = f(a) ∫ₐᶜ ψ + f(b) ∫_c^b ψ`. -/
@[dlmf 1.4.E30]
theorem exists_integral_mul_eq_secondMeanValue {f ψ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : MonotoneOn f (Icc a b) ∨ AntitoneOn f (Icc a b))
    (hψ : IntervalIntegrable ψ volume a b) :
    ∃ c ∈ Icc a b, ∫ x in a..b, f x * ψ x =
      f a * (∫ x in a..c, ψ x) + f b * ∫ x in c..b, ψ x := by
  sorry

/-- DLMF 1.4.31 (repeated integrals): applying `g ↦ (x ↦ ∫ₐˣ g)` `n + 1` times to `f` gives
`(1/n!) ∫ₐᵇ (b - x)ⁿ f(x) dx` at `b`. Stated for `f` continuous (DLMF: continuous or piecewise
continuous). -/
@[dlmf 1.4.E31]
theorem iterate_primitive_eq_integral {f : ℝ → ℝ} (hf : Continuous f) (a b : ℝ) (n : ℕ) :
    (fun g : ℝ → ℝ => fun x => ∫ t in a..x, g t)^[n + 1] f b =
      (1 / (n ! : ℝ)) * ∫ x in a..b, (b - x) ^ n * f x := by
  sorry

/-- DLMF 1.4.34: if `f` is continuous on `[a, b]` and continuously differentiable on `(a, b)`
with `∫ₐᵇ ‖f'‖ < ∞`, then its total variation on `[a, b]` is `∫ₐᵇ ‖f'(x)‖ dx`. Stated for
functions with values in any real normed space, which covers the complex case of §1.4(v). -/
@[dlmf 1.4.E34]
theorem eVariationOn_eq_integral_norm_deriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : DifferentiableOn ℝ f (Ioo a b)) (hd' : ContinuousOn (deriv f) (Ioo a b))
    (hi : IntegrableOn (fun x => ‖deriv f x‖) (Ioo a b)) :
    eVariationOn f (Icc a b) = ENNReal.ofReal (∫ x in a..b, ‖deriv f x‖) := by
  sorry

/-! ### §1.4(vii) Maxima and minima -/

/-- DLMF §1.4(vii): the maximum of a continuous `f` on `[a, b]` is attained either at a local
maximum of `f` or at one of the end points. -/
@[dlmf 1.4.vii]
theorem exists_isMaxOn_Icc_endpoint_or_isLocalMax {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) :
    ∃ c ∈ Icc a b, IsMaxOn f (Icc a b) c ∧ (c = a ∨ c = b ∨ IsLocalMax f c) := by
  obtain ⟨c, hc, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hf
  refine ⟨c, hc, hmax, ?_⟩
  rcases eq_or_lt_of_le hc.1 with h | h
  · exact Or.inl h.symm
  rcases eq_or_lt_of_le hc.2 with h' | h'
  · exact Or.inr (Or.inl h')
  exact Or.inr (Or.inr (hmax.isLocalMax (Icc_mem_nhds h h')))

/-- DLMF §1.4(vii): the minimum of a continuous `f` on `[a, b]` is attained either at a local
minimum of `f` or at one of the end points. -/
@[dlmf 1.4.vii]
theorem exists_isMinOn_Icc_endpoint_or_isLocalMin {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) :
    ∃ c ∈ Icc a b, IsMinOn f (Icc a b) c ∧ (c = a ∨ c = b ∨ IsLocalMin f c) := by
  obtain ⟨c, hc, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hf
  refine ⟨c, hc, hmin, ?_⟩
  rcases eq_or_lt_of_le hc.1 with h | h
  · exact Or.inl h.symm
  rcases eq_or_lt_of_le hc.2 with h' | h'
  · exact Or.inr (Or.inl h')
  exact Or.inr (Or.inr (hmin.isLocalMin (Icc_mem_nhds h h')))

/-! ### §1.4(viii) Convex functions -/

/-- DLMF §1.4(viii): a twice differentiable `f` is convex on `(a, b)` iff `f'' ≥ 0` there. -/
@[dlmf 1.4.viii]
theorem convexOn_Ioo_iff_deriv2_nonneg {f : ℝ → ℝ} {a b : ℝ}
    (hf : DifferentiableOn ℝ f (Ioo a b)) (hf' : DifferentiableOn ℝ (deriv f) (Ioo a b)) :
    ConvexOn ℝ (Ioo a b) f ↔ ∀ x ∈ Ioo a b, 0 ≤ deriv (deriv f) x := by
  constructor
  · intro hc x hx
    have hmono : MonotoneOn (deriv f) (Ioo a b) :=
      hc.monotoneOn_deriv fun y hy => hf.differentiableAt (isOpen_Ioo.mem_nhds hy)
    have := hmono.derivWithin_nonneg (x := x)
    rwa [derivWithin_of_isOpen isOpen_Ioo hx] at this
  · intro h
    refine convexOn_of_deriv2_nonneg (convex_Ioo a b) hf.continuousOn ?_ ?_ ?_
    · simpa [interior_Ioo] using hf
    · simpa [interior_Ioo] using hf'
    · simpa [interior_Ioo] using h

/-- DLMF §1.4(viii): a continuously differentiable `f` is convex on `(a, b)` iff its graph
does not lie below any of its tangents: `f(y) ≥ f(x) + f'(x)(y - x)` for `x, y ∈ (a, b)`. -/
@[dlmf 1.4.viii]
theorem convexOn_Ioo_iff_tangent_le {f : ℝ → ℝ} {a b : ℝ}
    (hf : DifferentiableOn ℝ f (Ioo a b)) :
    ConvexOn ℝ (Ioo a b) f ↔
      ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, f x + deriv f x * (y - x) ≤ f y := by
  have hdiff : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x :=
    fun x hx => hf.differentiableAt (isOpen_Ioo.mem_nhds hx)
  constructor
  · intro hc x hx y hy
    rcases lt_trichotomy x y with hxy | rfl | hxy
    · have := hc.deriv_le_slope hx hy hxy (hdiff x hx)
      rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hxy)] at this
      linarith
    · simp
    · have := hc.slope_le_deriv hy hx hxy (hdiff x hx)
      rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hxy)] at this
      linarith
  · intro h
    refine MonotoneOn.convexOn_of_deriv (convex_Ioo a b) hf.continuousOn
      (by simpa [interior_Ioo] using hf) ?_
    rw [interior_Ioo]
    intro x hx y hy hxy
    rcases eq_or_lt_of_le hxy with rfl | hlt
    · exact le_rfl
    have h1 := h x hx y hy
    have h2 := h y hy x hx
    have : (deriv f x - deriv f y) * (y - x) ≤ 0 := by nlinarith
    nlinarith [sub_pos.mpr hlt]

end DLMF.AlgebraicAnalytic
