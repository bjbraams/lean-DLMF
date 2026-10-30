/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Transforms.Basic
public import DLMFMathlib.Analysis.MellinConvolution
public import DLMFMathlib.Analysis.MellinParseval
public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Basic.Real.Sign
public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy
public import TauCeti.Analysis.Complex.SlitPlane
public import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
public import Mathlib.MeasureTheory.Integral.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Mellin, Hilbert and Stieltjes transforms (DLMF §1.14(iv)–(vi))

The Mellin transform 1.14.32 is Mathlib's `mellin f s = ∫₀^∞ x^{s-1} f(x) dx` (the same
normalization, principal powers of the positive real `x`); its inversion theorem 1.14.35 is
Mathlib's `mellinInv_mellin_eq` (pointer in `MathlibCoverage`). The Hilbert transform
`hilbertTransform` (1.14.41) and the Stieltjes transform `stieltjesTransform` (1.14.47) are
defined in `Transforms/Basic`.

Proved: Mellin holomorphy in its strip of absolute convergence, the Riemann–Lebesgue
property 1.14.33 on vertical lines, the integrability criterion of §1.14(iv), Mellin
convolution 1.14.40, the bilinear Mellin pairings 1.14.36–1.14.37 and the real
Mellin–Parseval identity 1.14.38. These pairings use Fourier inversion almost everywhere
with weighted `L¹` hypotheses. The Stieltjes results
include convergence from power decay, slit-plane holomorphy, differentiation of every
order and the iterated-Laplace identity 1.14.50. The Hilbert-transform statements and
Stieltjes inversion remain admitted. Slit-plane bounds reuse TauCeti's denominator estimate.

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
The Mellin convolution theorem uses `hasMellin_integral_mul_div` from the project’s
logarithmic-coordinate adapter to Mathlib’s convolution API.
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
  let U : Set ℂ := {s | a < s.re ∧ s.re < b}
  let Φ : ℂ → ℝ → ℂ := fun s t => (t : ℂ) ^ (s - 1) * f t
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_re continuous_const)
  apply Complex.differentiableOn_integral_Ioi_of_locally_dominated
    (Φ := Φ) hU 0
  · intro s hs
    exact ((hf s.re hs.1 hs.2).of_re_eq (by simp)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro s _
    exact (((differentiableAt_id.sub_const 1).const_cpow
      (Or.inl (ofReal_ne_zero.mpr ht.ne'))).mul_const (f t)).differentiableWithinAt
  · intro s hs
    obtain ⟨c, hac, hcs⟩ := exists_between hs.1
    obtain ⟨d, hsd, hdb⟩ := exists_between hs.2
    let V : Set ℂ := {y | c < y.re ∧ y.re < d}
    have hV : IsOpen V := (isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_re continuous_const)
    refine ⟨V, hV.mem_nhds ⟨hcs, hsd⟩, fun t => ‖Φ c t‖ + ‖Φ d t‖,
      ((hf c hac (by linarith)).norm).add ((hf d (by linarith) hdb).norm), ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht y hy
    dsimp only [Φ]
    simp only [norm_mul, norm_cpow_eq_rpow_re_of_pos ht, sub_re, one_re, ofReal_re]
    have hle : t ^ (y.re - 1) ≤ t ^ (c - 1) + t ^ (d - 1) := by
      rcases le_total 1 t with ht1 | ht1
      · exact le_add_of_nonneg_of_le (by positivity)
          (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith [hy.2]))
      · exact le_add_of_le_of_nonneg
          (Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith [hy.1])) (Real.rpow_nonneg ht.le _)
    calc _ ≤ (t ^ (c - 1) + t ^ (d - 1)) * ‖f t‖ :=
        mul_le_mul_of_nonneg_right hle (norm_nonneg _)
      _ = _ := by ring

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
  have hgy : MellinConvergent (fun x => g (y * x)) σ :=
    (MellinConvergent.comp_mul_left hy).mpr hg
  have h := integral_mul_eq_mellin_parseval hf hgy
    (hint.imp (fun hg' => hg'.mellin_comp_mul_left hy) id)
  rw [h]
  congr 1
  apply integral_congr_ae (Eventually.of_forall fun t => ?_)
  rw [mellin_comp_mul_left g _ hy, smul_eq_mul]
  ring

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
  have h := integral_mul_eq_mellin_parseval
    (f := fun x => (f x : ℂ)) (g := fun x => (f x : ℂ)) (σ := 1 / 2)
    (by convert hf using 1 <;> norm_num) (by simpa using hf) (Or.inl hint)
  have hm (t : ℝ) :
      mellin (fun x => (f x : ℂ)) (1 - ((1 / 2 : ℝ) + t * I)) =
        starRingEnd ℂ (mellin (fun x => (f x : ℂ)) ((1 / 2 : ℝ) + t * I)) := by
    have hc := mellin_conj (fun x => (f x : ℂ)) ((1 / 2 : ℝ) + t * I)
    convert hc using 1 <;> simp only [conj_ofReal, map_add, map_mul, map_div₀,
      map_one, map_ofNat, conj_I]
    congr 1
    push_cast
    ring
  simp_rw [hm, Complex.conj_mul', ← ofReal_pow] at h
  have hleft : (∫ x in Ioi (0 : ℝ), (f x : ℂ) * (f x : ℂ)) =
      ((∫ x in Ioi (0 : ℝ), f x ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    ext x
    push_cast
    ring
  rw [hleft, integral_complex_ofReal] at h
  simp only [ofReal_div, ofReal_one, ofReal_ofNat] at h
  exact_mod_cast h

/-- DLMF 1.14.40 (Mellin convolution theorem): if `x^{σ-1} f(x)` and `x^{σ-1} g(x)` are
absolutely integrable on `(0, ∞)`, then for `s = σ + it`,
`∫₀^∞ x^{s-1} (f * g)(x) dx = 𝓜(f)(s) 𝓜(g)(s)` with the Mellin convolution 1.14.39. -/
@[dlmf 1.14.E40]
theorem mellin_mellinConvolution {f g : ℝ → ℂ} {σ : ℝ} (hf : MellinConvergent f σ)
    (hg : MellinConvergent g σ) (t : ℝ) :
    mellin (mellinConvolution f g) (σ + t * I) =
      mellin f (σ + t * I) * mellin g (σ + t * I) := by
  exact (hasMellin_integral_mul_div (hf.of_re_eq (by simp)) (hg.of_re_eq (by simp))).2

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

/-- The Stieltjes denominator has no zeros on the slit plane for nonnegative integration
variables. -/
private lemma stieltjes_denominator_ne_zero {z : ℂ} (hz : z ∈ slitPlane) {t : ℝ}
    (ht : 0 ≤ t) : z + (t : ℂ) ≠ 0 := by
  obtain ⟨c, hc, hb⟩ := TauCeti.exists_pos_forall_mem_ball_mul_one_add_le_norm_add hz
  have h := hb z (Metric.mem_ball_self hc) ⟨t, ht⟩
  change c * (1 + t) ≤ ‖z + (t : ℂ)‖ at h
  exact norm_pos_iff.mp (lt_of_lt_of_le (by positivity) h)

/-- Convergence at a positive real point supplies measurability of all Stieltjes kernels. -/
private lemma stieltjesKernel_aestronglyMeasurable {f : ℝ → ℂ} {s₀ : ℝ} (hs₀ : 0 < s₀)
    (hf : IntegrableOn (fun t : ℝ => f t / ((s₀ : ℂ) + t)) (Ioi 0)) (z : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => f t / (z + t)) (volume.restrict (Ioi 0)) := by
  have hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0)) := by
    refine (hf.aestronglyMeasurable.mul (by fun_prop : Continuous fun t : ℝ =>
      (s₀ : ℂ) + t).aestronglyMeasurable).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    exact div_mul_cancel₀ _ (by rw [← ofReal_add]; exact ofReal_ne_zero.mpr (by linarith))
  refine (hfm.mul
    (by fun_prop : Measurable fun t : ℝ => (z + t)⁻¹).aestronglyMeasurable).congr
      (Eventually.of_forall fun t => ?_)
  exact (div_eq_mul_inv (f t) (z + t)).symm

/-- A local slit-plane denominator bound dominates the Stieltjes kernel by its integrable
norm at one positive real point. -/
private lemma stieltjesKernel_locally_dominated {f : ℝ → ℂ} {s₀ : ℝ} (hs₀ : 0 < s₀)
    (hf : IntegrableOn (fun t : ℝ => f t / ((s₀ : ℂ) + t)) (Ioi 0)) :
    ∀ z ∈ slitPlane, ∃ V ∈ 𝓝 z, ∃ g : ℝ → ℝ, Integrable g (volume.restrict (Ioi 0)) ∧
      ∀ᵐ t ∂(volume.restrict (Ioi 0)), ∀ w ∈ V, ‖f t / (w + t)‖ ≤ g t := by
  intro z hz
  obtain ⟨c, hc, hb⟩ := TauCeti.exists_pos_forall_mem_ball_mul_one_add_le_norm_add hz
  let D := max s₀ 1
  refine ⟨Metric.ball z c, Metric.ball_mem_nhds z hc,
    fun t => (D / c) * ‖f t / ((s₀ : ℂ) + t)‖, hf.norm.const_mul _, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
  change 0 < t at ht
  have hbound := hb w hw ⟨t, ht.le⟩
  change c * (1 + t) ≤ ‖w + (t : ℂ)‖ at hbound
  have hnorm : 0 < ‖w + (t : ℂ)‖ := lt_of_lt_of_le (by positivity) hbound
  have hst : 0 < s₀ + t := by linarith
  have hD : s₀ + t ≤ D * (1 + t) := by
    have hd0 : s₀ ≤ D := le_max_left _ _
    have hd1 : 1 ≤ D := le_max_right _ _
    nlinarith [mul_nonneg (sub_nonneg.mpr hd1) ht.le]
  have hr : (s₀ + t) / ‖w + (t : ℂ)‖ ≤ D / c := by
    apply (div_le_div_iff₀ hnorm hc).mpr
    have hdpos : 0 ≤ D := (zero_le_one.trans (le_max_right _ _))
    nlinarith [mul_le_mul_of_nonneg_left hbound hdpos]
  calc ‖f t / (w + t)‖ = ‖f t / ((s₀ : ℂ) + t)‖ * ((s₀ + t) / ‖w + (t : ℂ)‖) := by
        rw [norm_div, norm_div, ← ofReal_add, Complex.norm_real, Real.norm_of_nonneg hst.le]
        field_simp
      _ ≤ ‖f t / ((s₀ : ℂ) + t)‖ * (D / c) := mul_le_mul_of_nonneg_left hr (norm_nonneg _)
      _ = (D / c) * ‖f t / ((s₀ : ℂ) + t)‖ := mul_comm _ _

/-- Absolute convergence at one positive point implies convergence at every slit-plane point. -/
private theorem integrable_stieltjesKernel {f : ℝ → ℂ} {s₀ : ℝ} (hs₀ : 0 < s₀)
    (hf : IntegrableOn (fun t : ℝ => f t / ((s₀ : ℂ) + t)) (Ioi 0)) {z : ℂ}
    (hz : z ∈ slitPlane) : IntegrableOn (fun t : ℝ => f t / (z + t)) (Ioi 0) := by
  obtain ⟨V, hV, g, hg, hb⟩ := stieltjesKernel_locally_dominated hs₀ hf z hz
  exact hg.mono' (stieltjesKernel_aestronglyMeasurable hs₀ hf z)
    (hb.mono fun t ht => ht z (mem_of_mem_nhds hV))

/-- Repeated differentiation of the rational Stieltjes kernel. -/
private lemma iteratedDeriv_stieltjesKernel (a t z : ℂ) (m : ℕ) :
    iteratedDeriv m (fun w : ℂ => a / (w + t)) z =
      (-1) ^ m * (m ! : ℂ) * a / (z + t) ^ (m + 1) := by
  have hi := iteratedDerivWithin_one_div (𝕜 := ℂ) m isOpen_univ (mem_univ (z + t))
  rw [iteratedDerivWithin_univ] at hi
  simp only [one_div, show (-1 - (m : ℤ)) = -((m + 1 : ℕ) : ℤ) by push_cast; ring,
    zpow_neg, zpow_natCast] at hi
  simp only [div_eq_mul_inv]
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_comp_add_const]
  dsimp only
  rw [hi]
  ring

/-- DLMF §1.14(vi): if `f` is locally integrable on `[0, ∞)` and `f(t) = O(t^{-δ})` as `t → ∞`
with `δ > 0`, then the integral 1.14.47 converges absolutely for every real `s > 0`. -/
@[dlmf 1.14.vi]
theorem integrableOn_stieltjes_integrand {f : ℝ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hf : LocallyIntegrableOn f (Ici 0)) (hO : f =O[atTop] fun t => t ^ (-δ)) {s : ℝ}
    (hs : 0 < s) : IntegrableOn (fun t : ℝ => f t / ((s : ℂ) + t)) (Ioi 0) := by
  have hloc : LocallyIntegrableOn (fun t : ℝ => f t / ((s : ℂ) + t)) (Ici 0) := by
    have hk : ContinuousOn (fun t : ℝ => ((s : ℂ) + t)⁻¹) (Ici 0) := by
      intro t ht
      have hc : ContinuousAt (fun u : ℝ => (s : ℂ) + u) t := by fun_prop
      have hn : (s : ℂ) + t ≠ 0 := by
        rw [← ofReal_add]
        exact ofReal_ne_zero.mpr (add_pos_of_pos_of_nonneg hs ht).ne'
      exact (hc.inv₀ hn).continuousWithinAt
    simpa only [div_eq_mul_inv] using hf.mul_continuousOn hk isClosed_Ici.isLocallyClosed
  obtain ⟨C, hCpos, hC⟩ := hO.exists_pos
  have hbound : (fun t : ℝ => f t / ((s : ℂ) + t)) =O[atTop]
      fun t => t ^ (-δ - 1) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [hC.bound, eventually_ge_atTop (1 : ℝ)] with t ht ht1
    have ht0 : 0 < t := zero_lt_one.trans_le ht1
    rw [norm_div, ← ofReal_add, Complex.norm_real, Real.norm_of_nonneg (by linarith),
      Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _)]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _)] at ht
    calc ‖f t‖ / (s + t) ≤ (C * t ^ (-δ)) / (s + t) :=
          div_le_div_of_nonneg_right ht (by linarith)
      _ ≤ (C * t ^ (-δ)) / t := div_le_div_of_nonneg_left (by positivity) ht0 (by linarith)
      _ = C * t ^ (-δ - 1) := by rw [Real.rpow_sub ht0, Real.rpow_one]; ring
  have hi : IntegrableAtFilter (fun t : ℝ => t ^ (-δ - 1)) atTop volume :=
    ⟨Ioi (1 : ℝ), Ioi_mem_atTop 1, integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one⟩
  exact (hloc.integrableOn_of_isBigO_atTop hbound hi).mono_set Ioi_subset_Ici_self

/-- DLMF §1.14(vi): if the integral 1.14.47 converges absolutely at one point `s₀ > 0`, then
`𝒮(f)(s)` is analytic in the `s`-plane cut along the negative real axis (Mathlib's
`Complex.slitPlane`). (Absolute convergence makes DLMF's uniform convergence on compact sets
automatic.) -/
@[dlmf 1.14.vi]
theorem differentiableOn_stieltjesTransform {f : ℝ → ℂ} {s₀ : ℝ} (hs₀ : 0 < s₀)
    (hf : IntegrableOn (fun t : ℝ => f t / ((s₀ : ℂ) + t)) (Ioi 0)) :
    DifferentiableOn ℂ (stieltjesTransform f) slitPlane := by
  refine Complex.differentiableOn_integral_of_locally_dominated isOpen_slitPlane
    (fun z _ => stieltjesKernel_aestronglyMeasurable hs₀ hf z) ?_
    (stieltjesKernel_locally_dominated hs₀ hf)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
  exact (differentiableAt_const (f t)).div (differentiableAt_id.add_const (t : ℂ))
    (stieltjes_denominator_ne_zero hz ht.le) |>.differentiableWithinAt

/-- DLMF 1.14.48: under the hypotheses of `differentiableOn_stieltjesTransform`,
`(dᵐ/dsᵐ) 𝒮(f)(s) = (-1)ᵐ m! ∫₀^∞ f(t)/(s + t)^{m+1} dt` on the cut plane. -/
@[dlmf 1.14.E48]
theorem iteratedDeriv_stieltjesTransform {f : ℝ → ℂ} {s₀ : ℝ} (hs₀ : 0 < s₀)
    (hf : IntegrableOn (fun t : ℝ => f t / ((s₀ : ℂ) + t)) (Ioi 0)) (m : ℕ) {s : ℂ}
    (hs : s ∈ slitPlane) :
    iteratedDeriv m (stieltjesTransform f) s =
      (-1) ^ m * (m ! : ℂ) * ∫ t in Ioi (0 : ℝ), f t / (s + t) ^ (m + 1) := by
  have hd : ∀ᵐ t ∂(volume.restrict (Ioi 0)),
      DifferentiableOn ℂ (fun z : ℂ => f t / (z + t)) slitPlane := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
    exact ((differentiableAt_const (f t)).div (differentiableAt_id.add_const (t : ℂ))
      (stieltjes_denominator_ne_zero hz ht.le)).differentiableWithinAt
  change iteratedDeriv m (fun z : ℂ => ∫ t in Ioi (0 : ℝ), f t / (z + t)) s = _
  rw [Complex.iteratedDeriv_integral_of_locally_dominated
    isOpen_slitPlane (fun z _ => stieltjesKernel_aestronglyMeasurable hs₀ hf z) hd
    (stieltjesKernel_locally_dominated hs₀ hf) m hs]
  simp_rw [iteratedDeriv_stieltjesKernel]
  simp only [mul_assoc, mul_div_assoc, integral_const_mul]

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
  let μ := volume.restrict (Ioi (0 : ℝ))
  let Φ : ℝ × ℝ → ℂ := fun p => cexp (-(s + p.1) * p.2) * f p.1
  have hfm : AEStronglyMeasurable f μ :=
    (hf.mono_set Ioi_subset_Ici_self).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable Φ (μ.prod μ) :=
    (by fun_prop : Continuous fun p : ℝ × ℝ => cexp (-(s + p.1) * p.2)).aestronglyMeasurable.mul
      hfm.comp_fst
  have hinner (t : ℝ) (ht : 0 < t) : Integrable (fun u => Φ (t, u)) μ := by
    exact (integrableOn_exp_mul_complex_Ioi (a := -(s + t)) (by simp; linarith) 0).mul_const (f t)
  have hnorm (t : ℝ) (ht : 0 < t) : (∫ u, ‖Φ (t, u)‖ ∂μ) = ‖f t‖ / (s.re + t) := by
    simp only [Φ, norm_mul, Complex.norm_exp, neg_mul, neg_re, mul_re,
      add_re, ofReal_re, ofReal_im, mul_zero, sub_zero, μ]
    simp only [← neg_mul]
    rw [integral_mul_const, integral_exp_mul_Ioi (by linarith : -(s.re + t) < 0) 0]
    simp only [mul_zero, Real.exp_zero, div_neg, neg_neg, one_div]
    ring
  have hk : Integrable (fun t : ℝ => f t / ((s.re : ℂ) + t)) μ :=
    integrable_stieltjesKernel zero_lt_one (by simpa using hconv)
      (by exact Or.inl hs : (s.re : ℂ) ∈ slitPlane)
  have hi : Integrable Φ (μ.prod μ) := by
    apply (integrable_prod_iff hmeas).mpr
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hinner t ht
    · refine hk.norm.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change 0 < t at ht
      rw [hnorm t ht, norm_div, ← ofReal_add, norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith : 0 < s.re + t)]
  change (∫ t, f t / (s + t) ∂μ) = _
  calc _ = ∫ t, ∫ u, Φ (t, u) ∂μ ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        change 0 < t at ht
        dsimp [Φ, μ]
        rw [integral_mul_const, integral_exp_mul_complex_Ioi (by simp; linarith) 0]
        simp only [ofReal_zero, mul_zero, Complex.exp_zero, div_neg, neg_neg]
        ring
    _ = ∫ u, ∫ t, Φ (t, u) ∂μ ∂μ := integral_integral_swap hi
    _ = _ := by
        unfold laplaceTransform
        apply integral_congr_ae
        filter_upwards [] with u
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with t
        dsimp [Φ]
        rw [← mul_assoc, ← Complex.exp_add]
        congr 2
        ring

end DLMF.AlgebraicAnalytic
