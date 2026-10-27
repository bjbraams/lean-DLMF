/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Transforms.Defs
public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Basic.Real.Sign

/-!
# Mellin, Hilbert and Stieltjes transforms (DLMF §1.14(iv)–(vi))

The Mellin transform 1.14.32 is Mathlib's `mellin f s = ∫₀^∞ x^{s-1} f(x) dx` (the same
normalization, principal powers of the positive real `x`); its inversion theorem 1.14.35 is
Mathlib's `mellinInv_mellin_eq` (pointer in `MathlibCoverage`). The Hilbert transform
`hilbertTransform` (1.14.41) and the Stieltjes transform `stieltjesTransform` (1.14.47) are
defined in `Transforms/Defs`.

Proved: the Riemann–Lebesgue property 1.14.33 of the Mellin transform on vertical lines (from
Mathlib's `mellin_eq_fourier`), the integrability criterion of §1.14(iv) (from
`mellinConvergent_of_isBigO_rpow`) and 1.14.37 from 1.14.36. The other statements are admitted.

**Correction (1.14.45).** DLMF prints `∫ |ℋf|^p ≤ A_p ∫ |f|^p` with the Pichorides constants
`A_p = tan(π/(2p))` (`1 < p ≤ 2`) and `cot(π/(2p))` (`p ≥ 2`), "sharp". These constants are the
sharp bounds of the `L^p` operator norm, `‖ℋf‖_p ≤ A_p ‖f‖_p`; for the integrals of `p`-th powers
the sharp constant is `A_p^p`. The printed form fails: for `p = 4/3` (`A_p = 1 + √2 ≈ 2.414`) the
boundary values `u + iv` of `G(z) = (-iz)^{-0.745} (1 - iz)^{-1/2}` (analytic in the upper
half-plane, `v = -ℋu` in DLMF's sign) give `∫|v|^p / ∫|u|^p ≈ 3.19 > 2.414`. The corrected form
with `A_p^p` is acquired.

**Sign remark.** DLMF's Hilbert transform has `t - x` in the denominator (1.14.41), so its
Fourier multiplier in DLMF's Fourier normalization is `-i sign x` (1.14.46, checked numerically
for `f(t) = 1/(1 + t²)`, `ℋf(x) = -x/(1 + x²)`).
-/

@[expose] public noncomputable section

open MeasureTheory Complex Set Filter Topology Asymptotics
open scoped FourierTransform ENNReal Nat

namespace DLMF.AlgebraicAnalytic

/-! ### Mellin transform (§1.14(iv)) -/

/-- DLMF §1.14(iv): if `x^{σ-1} f(x)` is integrable on `(0, ∞)` for all `σ ∈ (a, b)`, then
`𝓜(f)(s)` is analytic in the strip `a < ℜs < b`. -/
@[dlmf 1.14.iv]
theorem differentiableOn_mellin {f : ℝ → ℂ} {a b : ℝ}
    (hf : ∀ σ : ℝ, a < σ → σ < b → MellinConvergent f σ) :
    DifferentiableOn ℂ (mellin f) {s : ℂ | a < s.re ∧ s.re < b} := by
  sorry

/-- DLMF 1.14.33: `𝓜(f)(σ + it) → 0` as `t → ±∞`. Proved from Mathlib's `mellin_eq_fourier`
and the Riemann–Lebesgue lemma; it holds for every `σ` (for non-convergent integrals the value
is `0`), stronger than DLMF. -/
@[dlmf 1.14.E33]
theorem tendsto_mellin_vertical (f : ℝ → ℂ) (σ : ℝ) :
    Tendsto (fun t : ℝ => mellin f (σ + t * I)) (cocompact ℝ) (𝓝 0) := by
  have hlin : Tendsto (fun t : ℝ => t / (2 * Real.pi)) (cocompact ℝ) (cocompact ℝ) := by
    have h2 : (1 / (2 * Real.pi) : ℝ) ≠ 0 := by positivity
    refine (Filter.tendsto_cocompact_mul_left₀ (K := ℝ) h2).congr fun t => ?_
    ring
  refine ((Real.zero_at_infty_fourier (fun u : ℝ => (Real.exp (-σ * u) • f (Real.exp (-u)) :
    ℂ))).comp hlin).congr fun t => ?_
  simp [mellin_eq_fourier, Function.comp]

/-- DLMF §1.14(iv) (note): if `f` is continuous on `(0, ∞)`, `f(x) = O(x^α)` as `x → 0+` and
`f(x) = O(x^β)` as `x → ∞`, then `x^{σ-1} f(x)` is integrable on `(0, ∞)` for
`σ ∈ (-α, -β)`. From Mathlib's `mellinConvergent_of_isBigO_rpow`. -/
@[dlmf 1.14.iv]
theorem mellinConvergent_of_isBigO {f : ℝ → ℂ} {α β σ : ℝ} (hf : ContinuousOn f (Ioi 0))
    (h0 : f =O[𝓝[>] 0] fun x => x ^ α) (hinf : f =O[atTop] fun x => x ^ β)
    (hσ1 : -α < σ) (hσ2 : σ < -β) : MellinConvergent f σ := by
  refine mellinConvergent_of_isBigO_rpow (a := -β) (b := -α)
    (hf.locallyIntegrableOn measurableSet_Ioi) ?_ (by simpa using hσ2) ?_ (by simpa using hσ1)
  · simpa using hinf
  · simpa using h0

/-- DLMF 1.14.34 (Mellin inversion at a point of bounded variation): if the Mellin integral
converges absolutely on `ℜs = σ` and `f` is of bounded variation near `u > 0`, then
`½(f(u+) + f(u-)) = (1/2πi) lim_{T→∞} ∫_{σ-iT}^{σ+iT} u^{-s} 𝓜(f)(s) ds` (with `s = σ + iy`,
`ds = i dy`). -/
@[dlmf 1.14.E34]
theorem tendsto_mellin_inversion_pv {f : ℝ → ℂ} {σ u δ : ℝ} (hf : MellinConvergent f σ)
    (hu : 0 < u) (hδ : 0 < δ) (hδu : δ < u) (hbv : BoundedVariationOn f (Icc (u - δ) (u + δ)))
    {fp fm : ℂ} (hp : Tendsto f (𝓝[>] u) (𝓝 fp)) (hm : Tendsto f (𝓝[<] u) (𝓝 fm)) :
    Tendsto (fun T : ℝ => (1 / (2 * Real.pi) : ℂ) *
        ∫ y in -T..T, (u : ℂ) ^ (-(σ + y * I)) * mellin f (σ + y * I)) atTop
      (𝓝 ((fp + fm) / 2)) := by
  sorry

/-- DLMF 1.14.36 (Parseval-type formula): if `x^{-σ} f(x)` and `x^{σ-1} g(x)` are absolutely
integrable on `(0, ∞)` and `𝓜(g)(σ + it)` or `𝓜(f)(1 - σ - it)` is absolutely integrable, then
for `y > 0`, `∫₀^∞ f(x) g(yx) dx = (1/2πi) ∫_{σ-i∞}^{σ+i∞} y^{-s} 𝓜(f)(1 - s) 𝓜(g)(s) ds`. -/
@[dlmf 1.14.E36]
theorem integral_mul_comp_mul_eq_mellin {f g : ℝ → ℂ} {σ : ℝ} (hf : MellinConvergent f (1 - σ))
    (hg : MellinConvergent g σ)
    (hint : VerticalIntegrable (mellin g) σ ∨
      Integrable fun t : ℝ => mellin f (1 - (σ + t * I))) {y : ℝ} (hy : 0 < y) :
    ∫ x in Ioi (0 : ℝ), f x * g (y * x) = (1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ, (y : ℂ) ^ (-(σ + t * I)) * mellin f (1 - (σ + t * I)) * mellin g (σ + t * I) := by
  sorry

/-- DLMF 1.14.37: the case `y = 1` of 1.14.36,
`∫₀^∞ f(x) g(x) dx = (1/2πi) ∫_{σ-i∞}^{σ+i∞} 𝓜(f)(1 - s) 𝓜(g)(s) ds`. -/
@[dlmf 1.14.E37]
theorem integral_mul_eq_mellin {f g : ℝ → ℂ} {σ : ℝ} (hf : MellinConvergent f (1 - σ))
    (hg : MellinConvergent g σ)
    (hint : VerticalIntegrable (mellin g) σ ∨
      Integrable fun t : ℝ => mellin f (1 - (σ + t * I))) :
    ∫ x in Ioi (0 : ℝ), f x * g x = (1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ, mellin f (1 - (σ + t * I)) * mellin g (σ + t * I) := by
  have h := integral_mul_comp_mul_eq_mellin hf hg hint one_pos
  simp only [one_mul, ofReal_one, one_cpow] at h
  exact h

/-- DLMF 1.14.38 (Mellin–Parseval): for real `f` with `x^{-1/2} f(x)` absolutely integrable on
`(0, ∞)` and `𝓜(f)(½ + it)` absolutely integrable,
`∫₀^∞ (f(x))² dx = (1/2π) ∫ |𝓜(f)(½ + it)|² dt`. -/
@[dlmf 1.14.E38]
theorem integral_sq_eq_mellin {f : ℝ → ℝ} (hf : MellinConvergent (fun x => (f x : ℂ)) (1 / 2))
    (hint : VerticalIntegrable (mellin fun x => (f x : ℂ)) (1 / 2)) :
    ∫ x in Ioi (0 : ℝ), f x ^ 2 =
      1 / (2 * Real.pi) * ∫ t : ℝ, ‖mellin (fun x => (f x : ℂ)) (1 / 2 + t * I)‖ ^ 2 := by
  sorry

/-- DLMF 1.14.40 (Mellin convolution theorem): if `x^{σ-1} f(x)` and `x^{σ-1} g(x)` are
absolutely integrable on `(0, ∞)`, then for `s = σ + it`,
`∫₀^∞ x^{s-1} (f * g)(x) dx = 𝓜(f)(s) 𝓜(g)(s)` with the Mellin convolution 1.14.39. -/
@[dlmf 1.14.E40]
theorem mellin_mellinConvolution {f g : ℝ → ℂ} {σ : ℝ} (hf : MellinConvergent f σ)
    (hg : MellinConvergent g σ) (t : ℝ) :
    mellin (mellinConvolution f g) (σ + t * I) =
      mellin f (σ + t * I) * mellin g (σ + t * I) := by
  sorry

/-! ### Hilbert transform (§1.14(v)) -/

/-- DLMF §1.14(v), 1.14.41: for `f ∈ L^p`, `1 ≤ p < ∞`, the principal value 1.14.41 exists for
almost every `x`, i.e. `hilbertTruncated f x ε → ℋ(f)(x)` as `ε → 0⁺`. -/
@[dlmf 1.14.E41]
theorem ae_tendsto_hilbertTruncated {f : ℝ → ℂ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (hf : MemLp f p) :
    ∀ᵐ x, Tendsto (hilbertTruncated f x) (𝓝[>] 0) (𝓝 (hilbertTransform f x)) := by
  sorry

/-- DLMF 1.14.42: for `f ∈ L^p`, `1 ≤ p < ∞`, and almost every `x`,
`ℋ(f)(x) = lim_{y→0+} (1/π) ∫ (t - x)/((t - x)² + y²) f(t) dt` (conjugate Poisson integral). -/
@[dlmf 1.14.E42]
theorem ae_tendsto_conjugatePoisson_hilbertTransform {f : ℝ → ℂ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hpt : p ≠ ∞) (hf : MemLp f p) :
    ∀ᵐ x, Tendsto (fun y : ℝ => (Real.pi⁻¹ : ℂ) *
        ∫ t, (((t - x) / ((t - x) ^ 2 + y ^ 2) : ℝ) : ℂ) * f t) (𝓝[>] 0)
      (𝓝 (hilbertTransform f x)) := by
  sorry

/-- DLMF 1.14.43: for `f ∈ L^p`, `1 ≤ p < ∞`, and every `x`, the truncated integrals of 1.14.41
equal `(1/π) ∫_ε^∞ (f(x + t) - f(x - t))/t dt`; hence
`ℋ(f)(x) = lim_{ε→0+} (1/π) ∫_ε^∞ (f(x + t) - f(x - t))/t dt` whenever either limit exists. -/
@[dlmf 1.14.E43]
theorem hilbertTruncated_eq_integral_Ioi {f : ℝ → ℂ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (hf : MemLp f p) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    hilbertTruncated f x ε = (Real.pi⁻¹ : ℂ) * ∫ t in Ioi ε, (f (x + t) - f (x - t)) / t := by
  sorry

/-- DLMF 1.14.44 (Hilbert inversion): if `f` is continuously differentiable with compact
support, then `f(x) = -(1/π) P.V.∫ ℋ(f)(u)/(u - x) du`, i.e. `f = -ℋ(ℋ(f))`. -/
@[dlmf 1.14.E44]
theorem hilbertTransform_hilbertTransform {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (x : ℝ) :
    f x = -hilbertTransform (hilbertTransform f) x := by
  sorry

/-- The Pichorides constant `A_p` of DLMF 1.14.45: `tan(π/(2p))` for `1 < p ≤ 2`,
`cot(π/(2p))` for `p ≥ 2` (the two agree at `p = 2`). -/
def pichoridesConstant (p : ℝ) : ℝ :=
  if p ≤ 2 then Real.tan (Real.pi / (2 * p)) else Real.cot (Real.pi / (2 * p))

/-- DLMF 1.14.45 (M. Riesz inequality with Pichorides' sharp constant), **corrected**: if
`|f|^p` is integrable, `1 < p < ∞`, then so is `|ℋ(f)|^p` and
`∫ |ℋ(f)(x)|^p dx ≤ A_p^p ∫ |f(t)|^p dt`. DLMF prints `A_p` instead of `A_p^p`, which is
false for `p ≠ 2` (see the module docstring); equality of norms holds for `p = 2`. -/
@[dlmf 1.14.E45]
theorem hilbertTransform_lp_bound {f : ℝ → ℂ} {p : ℝ} (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p)) :
    MemLp (hilbertTransform f) (ENNReal.ofReal p) ∧
      ∫ x, ‖hilbertTransform f x‖ ^ p ≤ pichoridesConstant p ^ p * ∫ t, ‖f t‖ ^ p := by
  sorry

/-- DLMF §1.14(v): for `p = 2` the Hilbert transform is an isometry of `L²`. -/
@[dlmf 1.14.E45]
theorem integral_norm_hilbertTransform_sq {f : ℝ → ℂ} (hf : MemLp f 2) :
    ∫ x, ‖hilbertTransform f x‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 := by
  sorry

/-- DLMF 1.14.46: for `f` continuously differentiable with compact support,
`(2π)^{-1/2} ∫ ℋ(f)(u) e^{iux} du = -i (sign x) 𝓕(f)(x)`, with `𝓕` as in 1.14.1 (the integral
taken as `lim_{R→∞} ∫_{-R}^{R}`, since `ℋf` decays only like `1/u`). -/
@[dlmf 1.14.E46]
theorem tendsto_fourier_hilbertTransform {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (x : ℝ) :
    Tendsto (fun R : ℝ => ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) *
        ∫ u in -R..R, hilbertTransform f u * cexp (I * u * x)) atTop
      (𝓝 (-I * (Real.sign x : ℂ) * fourierTransform f x)) := by
  sorry

/-! ### Stieltjes transform (§1.14(vi)) -/

/-- DLMF §1.14(vi): if `f` is locally integrable on `[0, ∞)` and `f(t) = O(t^{-δ})` as `t → ∞`
with `δ > 0`, then the integral 1.14.47 converges absolutely for every real `s > 0`. -/
@[dlmf 1.14.vi]
theorem integrableOn_stieltjes_integrand {f : ℝ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hf : LocallyIntegrableOn f (Ici 0)) (hO : f =O[atTop] fun t => t ^ (-δ)) {s : ℝ}
    (hs : 0 < s) : IntegrableOn (fun t : ℝ => f t / ((s : ℂ) + t)) (Ioi 0) := by
  sorry

/-- DLMF §1.14(vi): if the integral 1.14.47 converges absolutely at one point `s₀ > 0`, then
`𝒮(f)(s)` is analytic in the `s`-plane cut along the negative real axis (Mathlib's
`Complex.slitPlane`). (Absolute convergence makes DLMF's uniform convergence on compact sets
automatic.) -/
@[dlmf 1.14.vi]
theorem differentiableOn_stieltjesTransform {f : ℝ → ℂ} {s₀ : ℝ} (hs₀ : 0 < s₀)
    (hf : IntegrableOn (fun t : ℝ => f t / ((s₀ : ℂ) + t)) (Ioi 0)) :
    DifferentiableOn ℂ (stieltjesTransform f) slitPlane := by
  sorry

/-- DLMF 1.14.48: under the hypotheses of `differentiableOn_stieltjesTransform`,
`(dᵐ/dsᵐ) 𝒮(f)(s) = (-1)ᵐ m! ∫₀^∞ f(t)/(s + t)^{m+1} dt` on the cut plane. -/
@[dlmf 1.14.E48]
theorem iteratedDeriv_stieltjesTransform {f : ℝ → ℂ} {s₀ : ℝ} (hs₀ : 0 < s₀)
    (hf : IntegrableOn (fun t : ℝ => f t / ((s₀ : ℂ) + t)) (Ioi 0)) (m : ℕ) {s : ℂ}
    (hs : s ∈ slitPlane) :
    iteratedDeriv m (stieltjesTransform f) s =
      (-1) ^ m * (m ! : ℂ) * ∫ t in Ioi (0 : ℝ), f t / (s + t) ^ (m + 1) := by
  sorry

/-- DLMF 1.14.49 (Stieltjes inversion): if `f` is absolutely integrable on every `[0, R]` and the
integral 1.14.47 converges (absolutely, at `s = 1`), then for every `σ > 0` at which the one-sided
limits exist, `(𝒮(f)(-σ - it) - 𝒮(f)(-σ + it))/(2πi) → ½(f(σ+) + f(σ-))` as `t → 0+`. -/
@[dlmf 1.14.E49]
theorem tendsto_stieltjesTransform_jump {f : ℝ → ℂ} (hf : LocallyIntegrableOn f (Ici 0))
    (hconv : IntegrableOn (fun t : ℝ => f t / (1 + t)) (Ioi 0)) {σ : ℝ} (hσ : 0 < σ)
    {fp fm : ℂ} (hp : Tendsto f (𝓝[>] σ) (𝓝 fp)) (hm : Tendsto f (𝓝[<] σ) (𝓝 fm)) :
    Tendsto (fun t : ℝ => (stieltjesTransform f (-σ - t * I) -
        stieltjesTransform f (-σ + t * I)) / (2 * Real.pi * I)) (𝓝[>] 0)
      (𝓝 ((fp + fm) / 2)) := by
  sorry

/-- DLMF 1.14.50: if `f` is locally integrable on `[0, ∞)` and the integral 1.14.47 converges
(absolutely, at `s = 1`), then `𝒮(f)(s) = 𝓛(𝓛(f))(s)` for `ℜs > 0`, where the inner transform
is evaluated at real arguments. -/
@[dlmf 1.14.E50]
theorem stieltjesTransform_eq_laplace_laplace {f : ℝ → ℂ} (hf : LocallyIntegrableOn f (Ici 0))
    (hconv : IntegrableOn (fun t : ℝ => f t / (1 + t)) (Ioi 0)) {s : ℂ} (hs : 0 < s.re) :
    stieltjesTransform f s = laplaceTransform (fun u : ℝ => laplaceTransform f u) s := by
  sorry

end DLMF.AlgebraicAnalytic
