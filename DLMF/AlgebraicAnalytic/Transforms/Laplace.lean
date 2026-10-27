/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Transforms.Defs
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# The Laplace transform (DLMF §1.14(iii))

Statements of DLMF §1.14(iii) for `laplaceTransform f s = ∫₀^∞ e^{-st} f(t) dt` (1.14.17).

DLMF assumes throughout that `f` is piecewise continuous on `[0, ∞)` and of exponential growth
(1.14.18) with exponent `α`, and `ℜs > α`. Here "piecewise continuous" is replaced by the weaker
`LocallyIntegrableOn f (Ici 0)` wherever that suffices (stronger than DLMF), and the exponential
growth is the predicate `IsOfExponentialGrowth f α`.

Proved: absolute convergence for `ℜs > α` (`integrableOn_laplace_integrand`), the translation
rules 1.14.21 and 1.14.22. Admitted: analyticity and decay (§1.14(iii), 1.14.19), inversion
1.14.20, differentiation and integration 1.14.23–1.14.24, periodic functions 1.14.25–1.14.26,
derivatives 1.14.27–1.14.29, the convolution theorem 1.14.31 and uniqueness.
-/

@[expose] public noncomputable section

open MeasureTheory Complex Set Filter Topology

namespace DLMF.AlgebraicAnalytic

/-- DLMF §1.14(iii) (convergence): if `f` is locally integrable on `[0, ∞)` and of exponential
growth `α` (1.14.18), then `e^{-st} f(t)` is integrable on `(0, ∞)` for `ℜs > α`. -/
@[dlmf 1.14.iii]
theorem integrableOn_laplace_integrand {f : ℝ → ℂ} {α : ℝ} (hf : LocallyIntegrableOn f (Ici 0))
    (hg : IsOfExponentialGrowth f α) {s : ℂ} (hs : α < s.re) :
    IntegrableOn (fun t : ℝ => cexp (-s * t) * f t) (Ioi 0) := by
  obtain ⟨M, hM⟩ := hg
  have hmeas : AEStronglyMeasurable f (volume.restrict (Ioi 0)) :=
    (hf.aestronglyMeasurable).mono_set Ioi_subset_Ici_self
  have hb : IntegrableOn (fun t : ℝ => M * Real.exp (-(s.re - α) * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (by linarith)).const_mul M
  refine hb.mono' ((by fun_prop : Continuous fun t : ℝ => cexp (-s * t)).aestronglyMeasurable.mul
    hmeas) ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  rw [norm_mul, Complex.norm_exp]
  have hre : (-s * (t : ℂ)).re = -s.re * t := by simp
  rw [hre]
  calc Real.exp (-s.re * t) * ‖f t‖ ≤ Real.exp (-s.re * t) * (M * Real.exp (α * t)) :=
        mul_le_mul_of_nonneg_left (hM t ht0) (Real.exp_pos _).le
    _ = M * Real.exp (-(s.re - α) * t) := by
        rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

/-- DLMF §1.14(iii) (analyticity): under 1.14.18, `𝓛(f)(s)` is analytic in `ℜs > α`. -/
@[dlmf 1.14.iii]
theorem differentiableOn_laplaceTransform {f : ℝ → ℂ} {α : ℝ}
    (hf : LocallyIntegrableOn f (Ici 0)) (hg : IsOfExponentialGrowth f α) :
    DifferentiableOn ℂ (laplaceTransform f) {s : ℂ | α < s.re} := by
  sorry

/-- DLMF 1.14.19: under 1.14.18, `𝓛(f)(s) → 0` as `ℜs → ∞`, uniformly in `ℑs`. -/
@[dlmf 1.14.E19]
theorem tendsto_laplaceTransform_re_atTop {f : ℝ → ℂ} {α : ℝ}
    (hf : LocallyIntegrableOn f (Ici 0)) (hg : IsOfExponentialGrowth f α) :
    Tendsto (laplaceTransform f) (comap Complex.re atTop) (𝓝 0) := by
  sorry

/-- DLMF 1.14.20 (Bromwich inversion): if `f` is continuous on `[0, ∞)`, of exponential growth
`α`, and of locally bounded variation (as when `f'` is piecewise continuous), then for `t > 0`
and `σ > α`,
`f(t) = (1/2πi) lim_{T→∞} ∫_{σ-iT}^{σ+iT} e^{ts} 𝓛(f)(s) ds`, the path parametrized by
`s = σ + iy` (`ds = i dy`). -/
@[dlmf 1.14.E20]
theorem tendsto_laplaceTransform_inversion {f : ℝ → ℂ} {α : ℝ} (hf : ContinuousOn f (Ici 0))
    (hbv : LocallyBoundedVariationOn f (Ici 0)) (hg : IsOfExponentialGrowth f α) {σ : ℝ}
    (hσ : α < σ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun T : ℝ => (1 / (2 * Real.pi) : ℂ) *
        ∫ y in -T..T, cexp (t * (σ + y * I)) * laplaceTransform f (σ + y * I)) atTop
      (𝓝 (f t)) := by
  sorry

/-- DLMF §1.14(iii), after 1.14.20: if moreover `𝓛(f)(s) = O(s^{-K})` with `K > 1` in a
half-plane `ℜs ≥ γ` (here `γ > α`), then for every `σ > γ` and `t > 0` the inversion integral
converges absolutely and `f(t) = (1/2π) ∫ e^{t(σ+iy)} 𝓛(f)(σ + iy) dy`; continuity of `f`
suffices. -/
@[dlmf 1.14.E20]
theorem laplaceTransform_inversion_of_isBigO {f : ℝ → ℂ} {α γ K C : ℝ}
    (hf : ContinuousOn f (Ici 0)) (hg : IsOfExponentialGrowth f α) (hγ : α < γ) (hK : 1 < K)
    (hbound : ∀ s : ℂ, γ ≤ s.re → ‖laplaceTransform f s‖ ≤ C * ‖s‖ ^ (-K)) {σ : ℝ}
    (hσ : γ < σ) {t : ℝ} (ht : 0 < t) :
    f t = (1 / (2 * Real.pi) : ℂ) *
      ∫ y : ℝ, cexp (t * (σ + y * I)) * laplaceTransform f (σ + y * I) := by
  sorry

/-- DLMF 1.14.21 (translation): `𝓛(f)(s - a) = 𝓛(f_a)(s)` with `f_a(t) = e^{at} f(t)`. This holds
identically (also when the integrals diverge, both sides being `0`). -/
@[dlmf 1.14.E21]
theorem laplaceTransform_sub (f : ℝ → ℂ) (s a : ℂ) :
    laplaceTransform f (s - a) = laplaceTransform (fun t => cexp (a * t) * f t) s := by
  unfold laplaceTransform
  congr 1
  funext t
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- DLMF 1.14.22 (translation): for `a ≥ 0`, `𝓛(f_a⁺)(s) = e^{-as} 𝓛(f)(s)` with
`f_a⁺(t) = H(t - a) f(t - a)` (`H` the Heaviside function; its value at `0` is irrelevant). -/
@[dlmf 1.14.E22]
theorem laplaceTransform_heaviside_shift (f : ℝ → ℂ) {a : ℝ} (ha : 0 ≤ a) (s : ℂ) :
    laplaceTransform (fun t => (Ioi a).indicator (fun t => f (t - a)) t) s =
      cexp (-a * s) * laplaceTransform f s := by
  unfold laplaceTransform
  have h1 : (∫ t in Ioi (0 : ℝ), cexp (-s * t) * (Ioi a).indicator (fun t => f (t - a)) t) =
      ∫ t : ℝ, (Ioi a).indicator (fun t => cexp (-s * t) * f (t - a)) t := by
    rw [← integral_indicator measurableSet_Ioi]
    congr 1
    funext t
    by_cases hta : a < t
    · have ht0 : 0 < t := lt_of_le_of_lt ha hta
      simp [indicator_of_mem, hta, ht0]
    · simp [indicator_of_notMem, hta]
  have h2 : (∫ t : ℝ, (Ioi a).indicator (fun t => cexp (-s * t) * f (t - a)) t) =
      ∫ u : ℝ, (Ioi (0 : ℝ)).indicator (fun u : ℝ => cexp (-s * ((u : ℂ) + a)) * f u) u := by
    rw [← integral_add_right_eq_self (fun t => (Ioi a).indicator
      (fun t => cexp (-s * t) * f (t - a)) t) a]
    congr 1
    funext u
    by_cases hu : 0 < u
    · have : a < u + a := by linarith
      simp [indicator_of_mem, hu, this]
    · have : ¬ a < u + a := by linarith
      simp [indicator_of_notMem, hu, this]
  rw [h1, h2, integral_indicator measurableSet_Ioi, ← integral_const_mul]
  congr 1
  funext u
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- DLMF 1.14.23: `(-1)ⁿ (dⁿ/dsⁿ) 𝓛(f)(s) = 𝓛(f_n)(s)` with `f_n(t) = tⁿ f(t)`, for `ℜs > α`. -/
@[dlmf 1.14.E23]
theorem iteratedDeriv_laplaceTransform {f : ℝ → ℂ} {α : ℝ} (hf : LocallyIntegrableOn f (Ici 0))
    (hg : IsOfExponentialGrowth f α) (n : ℕ) {s : ℂ} (hs : α < s.re) :
    (-1) ^ n * iteratedDeriv n (laplaceTransform f) s =
      laplaceTransform (fun t => (t : ℂ) ^ n * f t) s := by
  sorry

/-- DLMF 1.14.24: if moreover `lim_{t→0+} f(t)/t` exists, then
`∫_s^∞ 𝓛(f)(u) du = 𝓛(f_{-1})(s)` with `f_{-1}(t) = f(t)/t`, the integral along the horizontal ray
`u = s + v`, `v ≥ 0`. -/
@[dlmf 1.14.E24]
theorem integral_laplaceTransform_ray {f : ℝ → ℂ} {α : ℝ} (hf : LocallyIntegrableOn f (Ici 0))
    (hg : IsOfExponentialGrowth f α) {l : ℂ}
    (hl : Tendsto (fun t : ℝ => f t / t) (𝓝[>] 0) (𝓝 l)) {s : ℂ} (hs : α < s.re) :
    ∫ v in Ioi (0 : ℝ), laplaceTransform f (s + v) = laplaceTransform (fun t => f t / t) s := by
  sorry

/-- DLMF 1.14.25: if `a > 0` and `f(t + a) = f(t)` for `t > 0`, then
`𝓛(f)(s) = (1 - e^{-as})⁻¹ ∫₀^a e^{-st} f(t) dt`. -/
@[dlmf 1.14.E25]
theorem laplaceTransform_of_periodic {f : ℝ → ℂ} {α a : ℝ} (ha : 0 < a)
    (hf : LocallyIntegrableOn f (Ici 0)) (hg : IsOfExponentialGrowth f α)
    (hper : ∀ t, 0 < t → f (t + a) = f t) {s : ℂ} (hs : α < s.re) (hs0 : 0 < s.re) :
    laplaceTransform f s =
      (1 - cexp (-a * s))⁻¹ * ∫ t in (0 : ℝ)..a, cexp (-s * t) * f t := by
  sorry

/-- DLMF 1.14.26: if `a > 0` and `f(t + a) = -f(t)` for `t > 0`, then
`𝓛(f)(s) = (1 + e^{-as})⁻¹ ∫₀^a e^{-st} f(t) dt`. -/
@[dlmf 1.14.E26]
theorem laplaceTransform_of_antiperiodic {f : ℝ → ℂ} {α a : ℝ} (ha : 0 < a)
    (hf : LocallyIntegrableOn f (Ici 0)) (hg : IsOfExponentialGrowth f α)
    (hper : ∀ t, 0 < t → f (t + a) = -f t) {s : ℂ} (hs : α < s.re) (hs0 : 0 < s.re) :
    laplaceTransform f s =
      (1 + cexp (-a * s))⁻¹ * ∫ t in (0 : ℝ)..a, cexp (-s * t) * f t := by
  sorry

/-- DLMF 1.14.27: if `f` is continuous on `[0, ∞)`, differentiable on `(0, ∞)` with locally
integrable derivative `f'`, and `f`, `f'` are of exponential growth `α`, then
`𝓛(f')(s) = s 𝓛(f)(s) - f(0+)` for `ℜs > α`. -/
@[dlmf 1.14.E27]
theorem laplaceTransform_deriv {f f' : ℝ → ℂ} {α : ℝ} (hf : ContinuousOn f (Ici 0))
    (hderiv : ∀ t, 0 < t → HasDerivAt f (f' t) t) (hf' : LocallyIntegrableOn f' (Ici 0))
    (hg : IsOfExponentialGrowth f α) (hg' : IsOfExponentialGrowth f' α) {s : ℂ}
    (hs : α < s.re) :
    laplaceTransform f' s = s * laplaceTransform f s - f 0 := by
  sorry

/-- DLMF 1.14.28: if `f` has jump discontinuities at `0 = t₀ < t₁ < ⋯ < tₙ` and is differentiable
elsewhere on `(0, ∞)` with locally integrable derivative `f'`, then
`𝓛(f')(s) = s 𝓛(f)(s) - f(0+) - ∑_{k=1}^{n} e^{-s t_k}(f(t_k+) - f(t_k-))`. -/
@[dlmf 1.14.E28]
theorem laplaceTransform_deriv_of_jumps {f f' : ℝ → ℂ} {α : ℝ} {n : ℕ} {τ : ℕ → ℝ}
    (hτ0 : τ 0 = 0) (hτ : ∀ k < n, τ k < τ (k + 1))
    (hderiv : ∀ t, 0 < t → t ∉ τ '' (Finset.range (n + 1) : Set ℕ) → HasDerivAt f (f' t) t)
    (hf : LocallyIntegrableOn f (Ici 0)) (hf' : LocallyIntegrableOn f' (Ici 0))
    (hg : IsOfExponentialGrowth f α) (hg' : IsOfExponentialGrowth f' α) {fp fm : ℕ → ℂ}
    (hp : ∀ k ≤ n, Tendsto f (𝓝[>] (τ k)) (𝓝 (fp k)))
    (hm : ∀ k ≤ n, 0 < k → Tendsto f (𝓝[<] (τ k)) (𝓝 (fm k))) {s : ℂ} (hs : α < s.re) :
    laplaceTransform f' s = s * laplaceTransform f s - fp 0 -
      ∑ k ∈ Finset.Icc 1 n, cexp (-s * τ k) * (fp k - fm k) := by
  sorry

/-- DLMF 1.14.29: if `f, f', …, f^{(n-1)}` are continuous on `[0, ∞)` and of exponential growth,
and `f^{(n)}` is locally integrable (and of exponential growth), then
`𝓛(f^{(n)})(s) = sⁿ 𝓛(f)(s) - s^{n-1} f(0+) - ⋯ - f^{(n-1)}(0+)`. The derivatives are given as a
family `g k` with `g 0 = f` and `(g k)' = g (k + 1)` on `(0, ∞)`. -/
@[dlmf 1.14.E29]
theorem laplaceTransform_iteratedDeriv {g : ℕ → ℝ → ℂ} {α : ℝ} {n : ℕ}
    (hcont : ∀ k < n, ContinuousOn (g k) (Ici 0))
    (hderiv : ∀ k < n, ∀ t, 0 < t → HasDerivAt (g k) (g (k + 1) t) t)
    (hloc : LocallyIntegrableOn (g n) (Ici 0)) (hg : ∀ k ≤ n, IsOfExponentialGrowth (g k) α)
    {s : ℂ} (hs : α < s.re) :
    laplaceTransform (g n) s =
      s ^ n * laplaceTransform (g 0) s - ∑ k ∈ Finset.range n, s ^ (n - 1 - k) * g k 0 := by
  sorry

/-- DLMF 1.14.31 (convolution theorem): `𝓛(f * g) = 𝓛(f) 𝓛(g)` for the Laplace convolution
1.14.30, for `ℜs > α`. -/
@[dlmf 1.14.E31]
theorem laplaceTransform_laplaceConvolution {f g : ℝ → ℂ} {α : ℝ}
    (hf : LocallyIntegrableOn f (Ici 0)) (hg : LocallyIntegrableOn g (Ici 0))
    (hfe : IsOfExponentialGrowth f α) (hge : IsOfExponentialGrowth g α) {s : ℂ}
    (hs : α < s.re) :
    laplaceTransform (laplaceConvolution f g) s = laplaceTransform f s * laplaceTransform g s := by
  sorry

/-- DLMF §1.14(iii) (uniqueness, Lerch): if `f`, `g` are continuous on `[0, ∞)`, of exponential
growth `α`, and `𝓛(f)(s) = 𝓛(g)(s)` for all real `s > α`, then `f = g` on `[0, ∞)`. -/
@[dlmf 1.14.iii]
theorem eqOn_of_laplaceTransform_eq {f g : ℝ → ℂ} {α : ℝ} (hf : ContinuousOn f (Ici 0))
    (hg : ContinuousOn g (Ici 0)) (hfe : IsOfExponentialGrowth f α)
    (hge : IsOfExponentialGrowth g α)
    (h : ∀ s : ℝ, α < s → laplaceTransform f s = laplaceTransform g s) :
    EqOn f g (Ici 0) := by
  sorry

end DLMF.AlgebraicAnalytic
