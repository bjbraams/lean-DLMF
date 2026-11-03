/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Mellin.Transforms
public import DLMF.AsymptoticApproximations.Mellin.Residues
public import DLMF.AlgebraicAnalytic.Transforms.Basic
public import DLMF.ExpIntegrals.Expansions
public import DLMF.IncompleteGamma.ExponentialIntegral
public import DLMF.Hypergeometric.Solutions.Logarithmic
public import DLMF.Gamma.VerticalBounds
public import DLMFMathlib.Analysis.Complex.BarnesResidue

/-!
# Laplace transforms with small parameters (DLMF §2.5(iii))

For `h` satisfying 2.5.18 and 2.5.20 with `c > -1`, the Laplace transform
`𝓛h(ζ) = ∫₀^∞ h(t) e^{-ζt} dt` (2.5.37; `DLMF.AlgebraicAnalytic.laplaceTransform`) is expanded
as `ζ → 0⁺` by writing `ζ𝓛h(ζ) = I₁(1/ζ) + I₂(1/ζ)` (2.5.38–2.5.39) and applying the Mellin
method with `𝓜(e^{-t})(z) = Γ(z)`.

## Main results

* `laplace_eq_trunc_add`, `laplace_trunc_eq_mellinInv`: DLMF 2.5.37–2.5.40.
* `laplace_truncLow_shift`, `laplace_truncHigh_shift`, `laplace_truncHigh_shift'`: contour shifts
  (DLMF 2.5.41–2.5.42).
* `laplace_remainder_isBigO`, `laplace_expansion_residues`: the remainder estimate
  `O(ζ^{l-δ-1})` and the expansion 2.5.43.
* `laplace_small_parameter`: the expansion 2.5.44.
* `residueAt_laplace_inv_one_add`, `residueAt_laplace_inv_one_add_truncHigh`,
  `laplace_inv_one_add_eq`, `laplace_inv_one_add_eq_complex`, `hasSum_laplace_inv_one_add`,
  `laplace_inv_one_add_isBigO`: the example `h(t) = 1/(1 + t)` (DLMF 2.5.45–2.5.49), the
  convergent form of 2.5.48 from DLMF 6.2.2 and 6.6.3.

## Implementation notes

Parameters: `ζ` is real and positive except in `laplace_inv_one_add_eq_complex` (`ℜζ > 0`).
The extended transform `𝓜h(z)` for `ℜz > 1` in 2.5.43–2.5.44 is `𝓜h₁(z) + H(z)`, `H` the
continuation of `𝓜h₂` (2.5.27–2.5.28).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Finset Asymptotics Complex Metric
open scoped Topology Real Nat

namespace DLMF.AsymptoticApproximations

open DLMF.AlgebraicAnalytic (laplaceTransform)

/-- DLMF 2.5.37–2.5.39: for `ζ > 0` and `x = 1/ζ`, `ζ𝓛h(ζ) = I₁(x) + I₂(x)` with
`I_j(x) = ∫₀^∞ e^{-t} h_j(xt) dt`, provided both integrals converge. -/
@[dlmf 2.5.E37, dlmf 2.5.E38, dlmf 2.5.E39]
theorem laplace_eq_trunc_add {h : ℝ → ℂ} {ζ : ℝ} (hζ : 0 < ζ)
    (h1 : IntegrableOn (fun t => (Real.exp (-t) : ℂ) * mellinTruncLow h (ζ⁻¹ * t)) (Ioi 0))
    (h2 : IntegrableOn (fun t => (Real.exp (-t) : ℂ) * mellinTruncHigh h (ζ⁻¹ * t)) (Ioi 0)) :
    (ζ : ℂ) * laplaceTransform h ζ =
      (∫ t in Ioi 0, (Real.exp (-t) : ℂ) * mellinTruncLow h (ζ⁻¹ * t)) +
        ∫ t in Ioi 0, (Real.exp (-t) : ℂ) * mellinTruncHigh h (ζ⁻¹ * t) := by
  rw [← integral_add h1 h2]
  have hsplit : (fun t => (Real.exp (-t) : ℂ) * mellinTruncLow h (ζ⁻¹ * t) +
      (Real.exp (-t) : ℂ) * mellinTruncHigh h (ζ⁻¹ * t)) =
      fun t => (fun u : ℝ => Complex.exp (-(ζ : ℂ) * u) * h u) (ζ⁻¹ * t) := by
    funext t
    simp only [mellinTruncHigh, Pi.sub_apply, ofReal_exp]
    have hζ0 : (ζ : ℂ) ≠ 0 := by exact_mod_cast hζ.ne'
    rw [show -(ζ : ℂ) * ((ζ⁻¹ * t : ℝ) : ℂ) = ((-t : ℝ) : ℂ) by
      push_cast; field_simp]
    ring
  rw [hsplit, integral_comp_mul_left_Ioi (fun u : ℝ => Complex.exp (-(ζ : ℂ) * u) * h u) 0
    (inv_pos.2 hζ), mul_zero, inv_inv,
    laplaceTransform, Complex.real_smul]

/-- `𝓜(e^{-t})(s) = Γ(s)` for `ℜs > 0` (DLMF 5.2.1), used in 2.5.40. -/
theorem mellin_exp_neg {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t : ℝ => (Real.exp (-t) : ℂ)) s = Complex.Gamma s := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral_eq_mellin]

/-- DLMF 2.5.40: if `𝓜h(z)` converges absolutely on the line `ℜz = p < 1`,
`Γ(1 - z)𝓜h(z)` is integrable along it, and `I(x) = ∫₀^∞ e^{-t} h(xt) dt` is continuous at
`x > 0`, then `I(x) = (2πi)⁻¹ ∫_{p-i∞}^{p+i∞} x^{-z} Γ(1 - z) 𝓜h(z) dz` (applied to `h = h_j`). -/
@[dlmf 2.5.E40]
theorem laplace_trunc_eq_mellinInv {h : ℝ → ℂ} {p x : ℝ} (hp : p < 1) (hx : 0 < x)
    (hconv : ∀ z : ℂ, z.re = p → MellinConvergent h z)
    (hint : VerticalIntegrable (fun z => Complex.Gamma (1 - z) * mellin h z) p)
    (hcont : ContinuousAt (fun x => ∫ t in Ioi 0, (Real.exp (-t) : ℂ) * h (x * t)) x) :
    (∫ t in Ioi 0, (Real.exp (-t) : ℂ) * h (x * t)) =
      mellinInv p (fun z => Complex.Gamma (1 - z) * mellin h z) x := by
  have hre : ∀ y : ℝ, 0 < (1 - ((p : ℂ) + y * I)).re := fun y => by simp; linarith
  have hline : ∀ y : ℝ, mellin (fun t : ℝ => (Real.exp (-t) : ℂ)) (1 - ((p : ℂ) + y * I)) =
      Complex.Gamma (1 - ((p : ℂ) + y * I)) := fun y => mellin_exp_neg (hre y)
  have hconv' : ∀ z : ℂ, z.re = p →
      MellinConvergent (fun t : ℝ => (Real.exp (-t) : ℂ)) (1 - z) ∧ MellinConvergent h z := by
    intro z hz
    refine ⟨?_, hconv z hz⟩
    have hs : 0 < (1 - z).re := by simp; linarith
    refine (Complex.GammaIntegral_convergent hs).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [smul_eq_mul, mul_comm, ofReal_exp]
  have hint' : VerticalIntegrable
      (fun z => mellin (fun t : ℝ => (Real.exp (-t) : ℂ)) (1 - z) * mellin h z) p := by
    unfold VerticalIntegrable at hint ⊢
    simp only [hline]
    exact hint
  rw [mellin_convolution_eq_mellinInv hx hconv' hint' hcont]
  unfold mellinInv
  simp only [hline]

/-- `Γ` is holomorphic at points of positive real part. -/
private lemma differentiableAt_Gamma_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Gamma s :=
  Complex.differentiableAt_Gamma s fun m h => by
    rw [h] at hs; simp at hs; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]

/-- Uniform vertical bound for `Γ` on a strip. -/
private lemma norm_Gamma_le_of_mem_Icc {a b x : ℝ} (ha : 0 < a) (hx : x ∈ Icc a b) (y : ℝ) :
    ‖Complex.Gamma (x + I * y)‖ ≤
      max (Real.Gamma a) (Real.Gamma b) / Real.Gamma b * ‖Complex.Gamma (b + I * y)‖ := by
  have hx0 : 0 < x := ha.trans_le hx.1
  have hb0 : 0 < b := hx0.trans_le hx.2
  have hM : Real.Gamma x ≤ max (Real.Gamma a) (Real.Gamma b) :=
    Real.convexOn_Gamma.le_max_of_mem_Icc (mem_Ioi.2 ha) (mem_Ioi.2 hb0) hx
  have hGx := Real.Gamma_pos_of_pos hx0
  have hGb := Real.Gamma_pos_of_pos hb0
  have hP := DLMF.Gamma.gammaVertProd_anti hx0 hx.2 y
  have hP1 := DLMF.Gamma.one_le_gammaVertProd b y
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, DLMF.Gamma.norm_Gamma_sq_eq hx0, DLMF.Gamma.norm_Gamma_sq_eq hb0, div_pow]
  rw [show max (Real.Gamma a) (Real.Gamma b) ^ 2 / Real.Gamma b ^ 2 *
      (Real.Gamma b ^ 2 / DLMF.Gamma.gammaVertProd b y) =
      max (Real.Gamma a) (Real.Gamma b) ^ 2 / DLMF.Gamma.gammaVertProd b y by
    field_simp]
  exact div_le_div₀ (by positivity) (pow_le_pow_left₀ hGx.le hM 2) (by linarith) hP

/-- `|Γ(b - iy)| → 0` as `|y| → ∞`, for `b > 0`. -/
private lemma tendsto_norm_Gamma_vertical {b : ℝ} (hb : 0 < b) :
    Tendsto (fun y : ℝ => ‖Complex.Gamma (b + I * ((-y : ℝ) : ℂ))‖) (cocompact ℝ) (𝓝 0) := by
  obtain ⟨C, K, hC⟩ := DLMF.Gamma.exists_norm_Gamma_le hb
  have hlim : Tendsto (fun t : ℝ => (1 + t) ^ K * Real.exp (-(π * t) / 2)) atTop (𝓝 0) := by
    have hu : Tendsto (fun t : ℝ => π / 2 * (1 + t)) atTop atTop :=
      (tendsto_atTop_add_const_left _ 1 tendsto_id).const_mul_atTop (by positivity)
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero K).comp hu
    have h' := h.const_mul ((2 / π) ^ K * Real.exp (π / 2))
    rw [mul_zero] at h'
    refine h'.congr' (Eventually.of_forall fun t => ?_)
    simp only [Function.comp_apply]
    rw [show -(π / 2 * (1 + t)) = -(π * t) / 2 + -(π / 2) by ring, Real.exp_add, mul_pow]
    have h1 : Real.exp (π / 2) * Real.exp (-(π / 2)) = 1 := by rw [← Real.exp_add]; simp
    have h2 : (2 / π) ^ K * (π / 2) ^ K = 1 := by rw [← mul_pow]; field_simp; simp
    linear_combination ((1 + t) ^ K * Real.exp (-(π * t) / 2)) *
      ((2 / π) ^ K * (π / 2) ^ K * h1 + h2)
  have h2 := (hlim.comp (tendsto_norm_cocompact_atTop (E := ℝ))).const_mul C
  rw [mul_zero] at h2
  refine squeeze_zero (fun y => norm_nonneg _) (fun y => ?_) h2
  simpa [Real.norm_eq_abs, mul_assoc] using hC (-y)

/-- `y ↦ |Γ(b + iy)|` is integrable for `b > 0`. -/
private lemma integrable_norm_Gamma_vertical {b : ℝ} (hb : 0 < b) :
    Integrable (fun y : ℝ => ‖Complex.Gamma (b + I * y)‖) := by
  obtain ⟨C, K, hC⟩ := DLMF.Gamma.exists_norm_Gamma_le hb
  have hi := (DLMF.Gamma.integrable_one_add_abs_pow_mul_exp_neg
    (c := π / 2) (by positivity) K).const_mul C
  refine hi.mono' ?_ (Eventually.of_forall fun y => ?_)
  · refine Continuous.aestronglyMeasurable (continuous_norm.comp ?_)
    refine continuous_iff_continuousAt.2 fun y => ?_
    refine (Complex.differentiableAt_Gamma _ fun m hm => ?_).continuousAt.comp (by fun_prop)
    have := congrArg re hm; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  · rw [norm_norm]
    refine (hC y).trans (le_of_eq ?_)
    rw [show -(π * |y|) / 2 = -(π / 2 * |y|) by ring]; ring
/-- `𝓜h₁` is holomorphic on `ℜz > -c` when `h(t) = O(t^c)` as `t → 0⁺`. -/
private lemma mellin_truncLow_differentiableAt {h : ℝ → ℂ} {c : ℝ}
    (hhc : LocallyIntegrableOn h (Ioi 0)) (h0 : h =O[𝓝[>] 0] fun t => t ^ c) {z : ℂ}
    (hz : -c < z.re) : DifferentiableAt ℂ (mellin (mellinTruncLow h)) z := by
  have hc : LocallyIntegrableOn (mellinTruncLow h) (Ioi 0) := by
    intro x hx
    obtain ⟨U, hU, h'U⟩ := hhc x hx
    exact ⟨U, hU, h'U.indicator measurableSet_Iic⟩
  refine mellin_differentiableAt_of_isBigO_rpow hc (a := z.re + 1) ?_ (by linarith) ?_ hz
  · refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop 1] with t ht
    rw [mellinTruncLow, indicator_of_notMem (show t ∉ Set.Iic 1 from not_le.2 ht)]
  · simp only [neg_neg]
    refine IsBigO.trans ?_ h0
    refine (isBigO_refl _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    rw [mellinTruncLow, indicator_of_mem (show t ∈ Set.Iic 1 from ht.2.le)]

/-- `|𝓜h₁(z)| ≤ ∫₀¹ t^{p-1} |h(t)| dt` for `ℜz ≥ p`. -/
private lemma norm_mellin_truncLow_le {h : ℝ → ℂ} {p : ℝ}
    (hconv : MellinConvergent (mellinTruncLow h) p) {z : ℂ} (hz : p ≤ z.re) :
    ‖mellin (mellinTruncLow h) z‖ ≤ ∫ t in Ioi 0, t ^ (p - 1) * ‖mellinTruncLow h t‖ := by
  refine (norm_integral_le_integral_norm _).trans ?_
  have hint : IntegrableOn (fun t : ℝ => t ^ (p - 1) * ‖mellinTruncLow h t‖) (Ioi 0) := by
    refine IntegrableOn.congr_fun (Integrable.norm hconv) (fun t ht => ?_) measurableSet_Ioi
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos ht]
    simp
  refine integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _) hint ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
  dsimp only
  rw [norm_smul, norm_cpow_eq_rpow_re_of_pos ht]
  by_cases h1 : t ≤ 1
  · refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge ht h1 ?_)
      (norm_nonneg _)
    simp only [sub_re, one_re]; linarith
  · simp [mellinTruncLow, indicator_of_notMem (show t ∉ Set.Iic (1 : ℝ) from h1)]


/-- `I₁(x) = ∫₀^∞ e^{-t} h₁(xt) dt` is continuous at `x > 0` when `∫₀¹ |h| < ∞`. -/
private lemma continuousAt_laplace_truncLow {h : ℝ → ℂ}
    (hconv1 : MellinConvergent (mellinTruncLow h) 1) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (fun x => ∫ t in Ioi 0, (Real.exp (-t) : ℂ) * mellinTruncLow h (x * t)) x := by
  set g := mellinTruncLow h
  have hg : IntegrableOn g (Ioi 0) := by
    refine IntegrableOn.congr_fun hconv1 (fun t _ => ?_) measurableSet_Ioi
    simp
  have heq : ∀ y : ℝ, 0 < y → (∫ t in Ioi 0, (Real.exp (-t) : ℂ) * g (y * t)) =
      (y : ℂ)⁻¹ * ∫ u in Ioi 0, (Real.exp (-(u / y)) : ℂ) * g u := by
    intro y hy
    have h := integral_comp_mul_left_Ioi (fun u => (Real.exp (-(u / y)) : ℂ) * g u) 0 hy
    rw [mul_zero] at h
    rw [← Complex.ofReal_inv, ← Complex.real_smul, ← h]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [mul_div_cancel_left₀ t hy.ne']
  have hI : ContinuousAt (fun y : ℝ => ∫ u in Ioi 0, (Real.exp (-(u / y)) : ℂ) * g u) x := by
    refine continuousAt_of_dominated (bound := fun u => ‖g u‖) ?_ ?_ hg.norm ?_
    · refine Eventually.of_forall fun y => ?_
      exact ((by fun_prop : Continuous fun u : ℝ => (Real.exp (-(u / y)) : ℂ))
        |>.aestronglyMeasurable).mul hg.aestronglyMeasurable
    · filter_upwards [lt_mem_nhds hx] with y hy
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      have : Real.exp (-(u / y)) ≤ 1 := Real.exp_le_one_iff.2 (by
        have := div_pos (show (0 : ℝ) < u from hu) hy; linarith)
      nlinarith [norm_nonneg (g u)]
    · refine Eventually.of_forall fun u => ?_
      have : ContinuousAt (fun y : ℝ => -(u / y)) x :=
        (continuousAt_const.div continuousAt_id hx.ne').neg
      exact ((continuous_ofReal.comp Real.continuous_exp).continuousAt.comp this).mul
        continuousAt_const
  have hinv : ContinuousAt (fun y : ℝ => (y : ℂ)⁻¹) x :=
    (continuous_ofReal.continuousAt).inv₀ (ofReal_ne_zero.2 hx.ne')
  refine (hinv.mul hI).congr ?_
  filter_upwards [lt_mem_nhds hx] with y hy
  exact (heq y hy).symm


/-- DLMF 2.5.41: let `h` be locally integrable on `(0, ∞)` with `h(t) = O(t^c)` as `t → 0⁺`,
`c > -1` (2.5.20). Then for `1 < ρ < 2` and `x > 0`,
`I₁(x) = 𝓜h₁(1) x^{-1} + (2πi)⁻¹ ∫_{ρ-i∞}^{ρ+i∞} x^{-z} Γ(1 - z) 𝓜h₁(z) dz`. -/
@[dlmf 2.5.E41, dlmf 2.5.iii]
theorem laplace_truncLow_shift {h : ℝ → ℂ} {c ρ x : ℝ} (hc : -1 < c) (hρ1 : 1 < ρ)
    (hρ2 : ρ < 2) (hx : 0 < x) (hhc : LocallyIntegrableOn h (Ioi 0))
    (h0 : h =O[𝓝[>] 0] fun t => t ^ c) :
    (∫ t in Ioi 0, (Real.exp (-t) : ℂ) * mellinTruncLow h (x * t)) =
      mellin (mellinTruncLow h) 1 * (x : ℂ)⁻¹ +
        mellinInv ρ (fun z => Complex.Gamma (1 - z) * mellin (mellinTruncLow h) z) x := by
  set g := mellinTruncLow h with hg
  set p : ℝ := (1 - c) / 2 with hpdef
  have hp1 : p < 1 := by rw [hpdef]; linarith
  have hpc : -c < p := by rw [hpdef]; linarith
  have hpρ : p < ρ := by linarith
  have hconv : ∀ z : ℂ, p ≤ z.re → MellinConvergent g z := fun z hz =>
    mellinConvergent_truncLow hhc h0 (by linarith)
  have hconv1 : MellinConvergent g 1 := hconv 1 (by simp; linarith)
  set B : ℝ := ∫ t in Ioi 0, t ^ (p - 1) * ‖g t‖
  have hB : ∀ z : ℂ, p ≤ z.re → ‖mellin g z‖ ≤ B := fun z hz =>
    norm_mellin_truncLow_le (hconv p (by simp)) hz
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB p (by simp))
  have hdiff : ∀ z : ℂ, p ≤ z.re → DifferentiableAt ℂ (mellin g) z := fun z hz =>
    mellin_truncLow_differentiableAt hhc h0 (by linarith)
  set F : ℂ → ℂ := fun z => Complex.Gamma (1 - z) * mellin g z with hF
  -- line integrability at `p`
  have hint : VerticalIntegrable F p := by
    have hb : 0 < 1 - p := by linarith
    have hi := (integrable_norm_Gamma_vertical hb).comp_neg.const_mul B
    refine hi.mono' ?_ (Eventually.of_forall fun y => ?_)
    · refine Continuous.aestronglyMeasurable (continuous_iff_continuousAt.2 fun y => ?_)
      have hz : ((p : ℂ) + y * I).re = p := by simp
      refine ContinuousAt.comp (g := F) ?_ (by fun_prop)
      refine ContinuousAt.mul ?_ (hdiff _ hz.ge).continuousAt
      refine (differentiableAt_Gamma_of_re_pos ?_).continuousAt.comp (by fun_prop)
      simp; linarith
    · simp only [hF]
      rw [norm_mul, mul_comm]
      have e : 1 - ((p : ℂ) + y * I) = ((1 - p : ℝ) : ℂ) + I * ((-y : ℝ) : ℂ) := by
        push_cast; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right (hB _ (by simp)) (norm_nonneg _)
  rw [laplace_trunc_eq_mellinInv hp1 hx (fun z hz => hconv z hz.ge) hint
    (continuousAt_laplace_truncLow hconv1 hx)]
  set Φ : ℂ → ℂ := fun z => -((x : ℂ) ^ (-z) * Complex.Gamma (2 - z) * mellin g z) with hΦ
  have hΦF : ∀ z : ℂ, z ≠ 1 → Φ z / (z - 1) = (x : ℂ) ^ (-z) • F z := by
    intro z hz
    have h1 : 1 - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
    have h2 : z - 1 ≠ 0 := sub_ne_zero.2 hz
    have hG : Complex.Gamma (2 - z) = (1 - z) * Complex.Gamma (1 - z) := by
      rw [show 2 - z = (1 - z) + 1 by ring, Complex.Gamma_add_one _ h1]
    simp only [hΦ, hF, hG, smul_eq_mul]
    field_simp
    ring
  have hline : ∀ σ : ℝ, σ ≠ 1 → (fun y : ℝ => Φ (σ + y * I) / (σ + y * I - 1)) =
      fun y : ℝ => (x : ℂ) ^ (-((σ : ℂ) + y * I)) • F (σ + y * I) := by
    intro σ hσ
    funext y
    refine hΦF _ fun he => hσ ?_
    have := congrArg re he; simpa using this
  have hxpos : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
  have hΦd : DifferentiableOn ℂ Φ (re ⁻¹' Icc p ρ) := by
    intro z hz
    have hz' : z.re ∈ Icc p ρ := hz
    refine DifferentiableAt.differentiableWithinAt ?_
    refine ((DifferentiableAt.mul ?_ ?_).mul (hdiff z hz'.1)).neg
    · exact (differentiableAt_id.neg).const_cpow (Or.inl hxpos)
    · refine (differentiableAt_Gamma_of_re_pos ?_).comp z (by fun_prop)
      simp; linarith [hz'.2]
  set X : ℝ := x ^ (-p) + x ^ (-ρ)
  set M : ℝ := max (Real.Gamma (2 - ρ)) (Real.Gamma (2 - p)) / Real.Gamma (2 - p)
  have hM0 : 0 ≤ M := div_nonneg ((Real.Gamma_pos_of_pos (by linarith)).le.trans
    (le_max_left _ _)) (Real.Gamma_pos_of_pos (by linarith)).le
  have hbound : ∀ σ : ℝ, σ ∈ Icc p ρ → ∀ y : ℝ, ‖Φ (σ + y * I)‖ ≤
      X * B * M * ‖Complex.Gamma (((2 - p : ℝ) : ℂ) + I * ((-y : ℝ) : ℂ))‖ := by
    intro σ hσ y
    have hre : ((σ : ℂ) + y * I).re = σ := by simp
    simp only [hΦ, norm_neg, norm_mul]
    have hX : ‖(x : ℂ) ^ (-((σ : ℂ) + y * I))‖ ≤ X := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp only [neg_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero]
      rcases le_total 1 x with h1 | h1
      · have := Real.rpow_le_rpow_of_exponent_le h1 (show -σ ≤ -p by linarith [hσ.1])
        have := Real.rpow_nonneg hx.le (-ρ)
        linarith
      · have := Real.rpow_le_rpow_of_exponent_ge hx h1 (show -ρ ≤ -σ by linarith [hσ.2])
        have := Real.rpow_nonneg hx.le (-p)
        linarith
    have hGam : ‖Complex.Gamma (2 - ((σ : ℂ) + y * I))‖ ≤
        M * ‖Complex.Gamma (((2 - p : ℝ) : ℂ) + I * ((-y : ℝ) : ℂ))‖ := by
      have e : 2 - ((σ : ℂ) + y * I) = ((2 - σ : ℝ) : ℂ) + I * ((-y : ℝ) : ℂ) := by
        push_cast; ring
      rw [e]
      exact norm_Gamma_le_of_mem_Icc (by linarith) ⟨by linarith [hσ.2], by linarith [hσ.1]⟩ _
    have hBz := hB _ (show p ≤ ((σ : ℂ) + y * I).re by rw [hre]; exact hσ.1)
    calc ‖(x : ℂ) ^ (-((σ : ℂ) + y * I))‖ * ‖Complex.Gamma (2 - ((σ : ℂ) + y * I))‖ *
          ‖mellin g (σ + y * I)‖
        ≤ X * (M * ‖Complex.Gamma (((2 - p : ℝ) : ℂ) + I * ((-y : ℝ) : ℂ))‖) * B := by
          gcongr
      _ = _ := by ring
  have hcontΦ : ∀ σ : ℝ, σ ∈ Icc p ρ → Continuous fun y : ℝ => Φ (σ + y * I) := by
    intro σ hσ
    refine hΦd.continuousOn.comp_continuous (by fun_prop) fun y => ?_
    show ((σ : ℂ) + y * I).re ∈ Icc p ρ
    simpa using hσ
  have hli : ∀ σ : ℝ, σ ∈ Icc p ρ → σ ≠ 1 →
      Integrable fun y : ℝ => Φ (σ + y * I) / (σ + y * I - 1) := by
    intro σ hσ hσ1
    have hne : ∀ y : ℝ, (σ : ℂ) + y * I - 1 ≠ 0 := fun y he => hσ1 (by
      have := congrArg re he; simp at this; linarith)
    have hσ1' : 0 < |σ - 1| := abs_pos.2 (sub_ne_zero.2 hσ1)
    have hi := (integrable_norm_Gamma_vertical (b := 2 - p) (by linarith)).comp_neg.const_mul
      (X * B * M / |σ - 1|)
    refine hi.mono' ((hcontΦ σ hσ).div (by fun_prop) hne).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    have hden : |σ - 1| ≤ ‖(σ : ℂ) + y * I - 1‖ := by
      refine le_trans (le_of_eq ?_) (Complex.abs_re_le_norm _)
      simp
    rw [norm_div, div_eq_mul_inv]
    calc ‖Φ (σ + y * I)‖ * ‖(σ : ℂ) + y * I - 1‖⁻¹
        ≤ (X * B * M * ‖Complex.Gamma (((2 - p : ℝ) : ℂ) + I * ((-y : ℝ) : ℂ))‖) *
          |σ - 1|⁻¹ :=
          mul_le_mul (hbound σ hσ y) (inv_anti₀ hσ1' hden) (by positivity)
            (by have := hB0; positivity)
      _ = _ := by ring
  have hhor : Tendsto (fun T : ℝ => ∫ t in p..ρ, Φ (t + T * I) / (t + T * I - 1))
      (cocompact ℝ) (𝓝 0) := by
    have hG := (tendsto_norm_Gamma_vertical (b := 2 - p) (by linarith)).const_mul
      (X * B * M * |ρ - p|)
    rw [mul_zero] at hG
    refine squeeze_zero_norm' ?_ hG
    filter_upwards [(tendsto_norm_cocompact_atTop (E := ℝ)).eventually
      (eventually_ge_atTop 1)] with T hT
    rw [show X * B * M * |ρ - p| * ‖Complex.Gamma (((2 - p : ℝ) : ℂ) + I * ((-T : ℝ) : ℂ))‖ =
        X * B * M * ‖Complex.Gamma (((2 - p : ℝ) : ℂ) + I * ((-T : ℝ) : ℂ))‖ * |ρ - p| by
      ring]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    have ht' : t ∈ Icc p ρ := by
      rw [uIoc_of_le hpρ.le] at ht; exact ⟨ht.1.le, ht.2⟩
    have hden : 1 ≤ ‖(t : ℂ) + T * I - 1‖ := by
      refine le_trans ?_ (Complex.abs_im_le_norm _)
      simpa [Real.norm_eq_abs] using hT
    rw [norm_div]
    exact (div_le_self (norm_nonneg _) hden).trans (hbound t ht' T)
  have hs := Complex.BarnesResidue.vertical_shift (c₁ := p) (c₂ := ρ) (p := 1)
    (by simpa using hp1) (by simpa using hρ1) hΦd (hli p ⟨le_rfl, hpρ.le⟩ hp1.ne)
    (hli ρ ⟨hpρ.le, le_rfl⟩ (by linarith)) (hhor.mono_left atTop_le_cocompact)
    (hhor.mono_left atBot_le_cocompact)
  rw [hline p hp1.ne, hline ρ (by linarith)] at hs
  have hΦ1 : Φ 1 = -((x : ℂ)⁻¹ * mellin g 1) := by
    simp only [hΦ]
    norm_num [Complex.cpow_neg_one]
  rw [hΦ1] at hs
  show mellinInv p F x = _
  unfold mellinInv
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  generalize (∫ y : ℝ, (x : ℂ) ^ (-((ρ : ℂ) + y * I)) • F (ρ + y * I)) = Iρ at hs ⊢
  generalize (∫ y : ℝ, (x : ℂ) ^ (-((p : ℂ) + y * I)) • F (p + y * I)) = Ip at hs ⊢
  rw [Complex.real_smul, Complex.real_smul]
  push_cast
  field_simp
  linear_combination (-x : ℂ) * hs + 2 * (π : ℂ) * mellin g 1 * mul_inv_cancel₀ hxpos

/-- DLMF 2.5.42, stronger than DLMF, which assumes `ρ < 2`: let `h` satisfy 2.5.18 and 2.5.20,
`p₂ < min(1, ℜβ₀)` as in 2.5.40, and let `H` be the continuation of `𝓜h₂` (2.5.27, or entire if
`κ ≠ 0`), so that `Γ(1 - z)H(z)` is analytic in `p₂ ≤ ℜz ≤ ρ` (`1 < ρ`) except
at the finite set `P` of poles with `ℜβ₀ ≤ ℜz ≤ 1`, and decays as `ℑz → ±∞` uniformly in
the strip. Then
`I₂(x) = ∑_{q ∈ P} Res_{z=q}[-x^{-z} Γ(1 - z) H(z)] + (2πi)⁻¹ ∫_{(ρ)} x^{-z} Γ(1 - z) H(z) dz`. -/
@[dlmf 2.5.E42, dlmf 2.5.iii]
theorem laplace_truncHigh_shift' {h : ℝ → ℂ} {H : ℂ → ℂ} {p ρ x : ℝ} (P : Finset ℂ)
    (hρ1 : 1 < ρ) (hp : p < 1) (hx : 0 < x)
    (hconv : ∀ z : ℂ, z.re = p → MellinConvergent (mellinTruncHigh h) z)
    (hH : ∀ z : ℂ, z.re ≤ p → H z = mellin (mellinTruncHigh h) z)
    (hP : ∀ q ∈ P, p < q.re ∧ q.re ≤ 1)
    (hHd : DifferentiableOn ℂ (fun z => Complex.Gamma (1 - z) * H z)
      ({z : ℂ | p ≤ z.re ∧ z.re ≤ ρ} \ (P : Set ℂ)))
    (hdecay : Tendsto (fun y : ℝ => ⨆ σ : Icc p ρ, ‖Complex.Gamma (1 - (σ + y * I)) *
      H (σ + y * I)‖) (cocompact ℝ) (𝓝 0))
    (hp_int : VerticalIntegrable (fun z => Complex.Gamma (1 - z) * H z) p)
    (hρ_int : VerticalIntegrable (fun z => Complex.Gamma (1 - z) * H z) ρ)
    (hcont : ContinuousAt (fun x => ∫ t in Ioi 0,
      (Real.exp (-t) : ℂ) * mellinTruncHigh h (x * t)) x) :
    (∫ t in Ioi 0, (Real.exp (-t) : ℂ) * mellinTruncHigh h (x * t)) =
      ∑ q ∈ P, DLMF.AlgebraicAnalytic.residueAt
        (fun z => -((x : ℂ) ^ (-z) * Complex.Gamma (1 - z) * H z)) q +
        mellinInv ρ (fun z => Complex.Gamma (1 - z) * H z) x := by
  set G : ℂ → ℂ := fun z => Complex.Gamma (1 - z) * H z with hGdef
  have hpρ : p < ρ := by linarith
  have hHp : ∀ y : ℝ, mellin (mellinTruncHigh h) (p + y * I) = H (p + y * I) := fun y =>
    (hH _ (by simp)).symm
  have hint : VerticalIntegrable
      (fun z => Complex.Gamma (1 - z) * mellin (mellinTruncHigh h) z) p := by
    unfold VerticalIntegrable at hp_int ⊢
    simpa only [hHp] using hp_int
  rw [laplace_trunc_eq_mellinInv hp hx hconv hint hcont]
  have hlineq : mellinInv p (fun z => Complex.Gamma (1 - z) * mellin (mellinTruncHigh h) z) x =
      mellinInv p G x := by
    unfold mellinInv
    simp only [hHp, hGdef]
  have hP' : ∀ q ∈ P, p < q.re ∧ q.re < ρ := fun q hq => ⟨(hP q hq).1, by linarith [(hP q hq).2]⟩
  rw [hlineq, mellinInv_shift (G := G) hpρ hx P hP' hHd hdecay hρ_int hp_int]
  have hxpos : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
  have hneg : ∀ q ∈ P, DLMF.AlgebraicAnalytic.residueAt
      (fun z => -((x : ℂ) ^ (-z) * Complex.Gamma (1 - z) * H z)) q =
        -DLMF.AlgebraicAnalytic.residueAt (fun z => (x : ℂ) ^ (-z) * G z) q := by
    intro q hq
    have hF : DifferentiableOn ℂ (fun z => (x : ℂ) ^ (-z) * G z)
        (re ⁻¹' Icc p ρ \ (P : Set ℂ)) := fun z hz =>
      (((differentiableAt_id.neg).const_cpow (Or.inl hxpos)).differentiableWithinAt).mul
        (hHd z hz)
    obtain ⟨ε, hε, hball⟩ := exists_punctured_differentiableAt hP' hF hq
    rw [← residueAt_neg_of_differentiableAt hε hball]
    congr 1
    funext z
    simp only [hGdef]
    ring
  rw [Finset.sum_congr rfl hneg, Finset.sum_neg_distrib]
  ring

/-- DLMF 2.5.42: let `h` satisfy 2.5.18 and 2.5.20, `p₂ < min(1, ℜβ₀)` as in 2.5.40, and let `H`
be the continuation of `𝓜h₂` (2.5.27, or entire if `κ ≠ 0`), so that `Γ(1 - z)H(z)` is
analytic in `p₂ ≤ ℜz ≤ ρ` (`1 < ρ < 2`) except at the finite set `P` of poles with
`ℜβ₀ ≤ ℜz ≤ 1`, and decays as `ℑz → ±∞` uniformly in the strip. Then
`I₂(x) = ∑_{q ∈ P} Res_{z=q}[-x^{-z} Γ(1 - z) H(z)] + (2πi)⁻¹ ∫_{(ρ)} x^{-z} Γ(1 - z) H(z) dz`. -/
@[dlmf 2.5.E42, dlmf 2.5.iii]
theorem laplace_truncHigh_shift {h : ℝ → ℂ} {H : ℂ → ℂ} {p ρ x : ℝ} (P : Finset ℂ)
    (hρ1 : 1 < ρ) (_hρ2 : ρ < 2) (hp : p < 1) (hx : 0 < x)
    (hconv : ∀ z : ℂ, z.re = p → MellinConvergent (mellinTruncHigh h) z)
    (hH : ∀ z : ℂ, z.re ≤ p → H z = mellin (mellinTruncHigh h) z)
    (hP : ∀ q ∈ P, p < q.re ∧ q.re ≤ 1)
    (hHd : DifferentiableOn ℂ (fun z => Complex.Gamma (1 - z) * H z)
      ({z : ℂ | p ≤ z.re ∧ z.re ≤ ρ} \ (P : Set ℂ)))
    (hdecay : Tendsto (fun y : ℝ => ⨆ σ : Icc p ρ, ‖Complex.Gamma (1 - (σ + y * I)) *
      H (σ + y * I)‖) (cocompact ℝ) (𝓝 0))
    (hp_int : VerticalIntegrable (fun z => Complex.Gamma (1 - z) * H z) p)
    (hρ_int : VerticalIntegrable (fun z => Complex.Gamma (1 - z) * H z) ρ)
    (hcont : ContinuousAt (fun x => ∫ t in Ioi 0,
      (Real.exp (-t) : ℂ) * mellinTruncHigh h (x * t)) x) :
    (∫ t in Ioi 0, (Real.exp (-t) : ℂ) * mellinTruncHigh h (x * t)) =
      ∑ q ∈ P, DLMF.AlgebraicAnalytic.residueAt
        (fun z => -((x : ℂ) ^ (-z) * Complex.Gamma (1 - z) * H z)) q +
        mellinInv ρ (fun z => Complex.Gamma (1 - z) * H z) x :=
  laplace_truncHigh_shift' P hρ1 hp hx hconv hH hP hHd hdecay hp_int hρ_int hcont

/-- Bound for the inverse Mellin integral: `|(2πi)⁻¹ ∫_{(σ)} x^{-z} G(z) dz| ≤ x^{-σ} C` with
`C = (2π)⁻¹ ∫ |G(σ + iy)| dy`, for `x > 0`. -/
theorem norm_mellinInv_le (σ : ℝ) (G : ℂ → ℂ) {x : ℝ} (hx : 0 < x) :
    ‖mellinInv σ G x‖ ≤ x ^ (-σ) * ((1 / (2 * π)) * ∫ y : ℝ, ‖G (σ + y * I)‖) := by
  unfold mellinInv
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  have h1 : ‖∫ y : ℝ, (x : ℂ) ^ (-((σ : ℂ) + y * I)) • G (σ + y * I)‖ ≤
      x ^ (-σ) * ∫ y : ℝ, ‖G (σ + y * I)‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp
  calc 1 / (2 * π) * ‖∫ y : ℝ, (x : ℂ) ^ (-((σ : ℂ) + y * I)) • G (σ + y * I)‖
      ≤ 1 / (2 * π) * (x ^ (-σ) * ∫ y : ℝ, ‖G (σ + y * I)‖) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

/-- DLMF §2.5(iii), after 2.5.43: the last term of 2.5.43,
`(2πi)⁻¹ ∫_{l-δ-i∞}^{l-δ+i∞} ζ^{z-1} G(z) dz = ζ⁻¹ · (2πi)⁻¹ ∫ (1/ζ)^{-z} G(z) dz`, is
`O(ζ^{l-δ-1})` as `ζ → 0⁺` (here `σ = l - δ`). Stronger than DLMF: no hypothesis on `G`. -/
@[dlmf 2.5.E43, dlmf 2.5.iii]
theorem laplace_remainder_isBigO (σ : ℝ) (G : ℂ → ℂ) :
    (fun ζ : ℝ => (ζ : ℂ)⁻¹ * mellinInv σ G ζ⁻¹) =O[𝓝[>] 0] fun ζ => ζ ^ (σ - 1) := by
  set C : ℝ := (1 / (2 * π)) * ∫ y : ℝ, ‖G (σ + y * I)‖
  refine IsBigO.of_bound C ?_
  filter_upwards [self_mem_nhdsWithin] with ζ (hζ : 0 < ζ)
  have hb := norm_mellinInv_le σ G (inv_pos.2 hζ)
  rw [Real.inv_rpow hζ.le, Real.rpow_neg hζ.le, inv_inv] at hb
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hζ.le,
    Real.norm_of_nonneg (Real.rpow_nonneg hζ.le _), Real.rpow_sub_one hζ.ne']
  calc ζ⁻¹ * ‖mellinInv σ G ζ⁻¹‖ ≤ ζ⁻¹ * (ζ ^ σ * C) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.2 hζ.le)
    _ = C * (ζ ^ σ / ζ) := by ring

/-- DLMF 2.5.43: under the hypotheses of 2.5.41–2.5.42, with `H` the continuation of `𝓜h₂`,
`P₂` the poles of `Γ(1 - z)H(z)` in `ℜβ₀ ≤ ℜz ≤ 1`, always including `z = 1` (the pole of
`Γ(1 - z)`, whose residue `H(1)` the formula needs), `P` the poles of `Γ(1 - z)𝓜h(z)`
(`𝓜h = 𝓜h₁ + H`) in `1 < ℜz < l` (`l ≥ 2` an integer, `0 < δ` small, no poles on
`ℜz = l - δ`), decay of these products along vertical lines uniformly in strips, and
integrability of `Γ(1 - z)𝓜h(z)` on the line `ℜz = l - δ` (which DLMF assumes implicitly),
`𝓛h(ζ) = 𝓜h₁(1) + ∑_{P₂} Res[-ζ^{z-1}Γ(1 - z)H(z)] + ∑_{P} Res[-ζ^{z-1}Γ(1 - z)𝓜h(z)]
+ (2πi)⁻¹ ∫_{(l-δ)} ζ^{z-1}Γ(1 - z)𝓜h(z) dz` for `ζ > 0`. -/
@[dlmf 2.5.E43]
theorem laplace_expansion_residues {h : ℝ → ℂ} {H : ℂ → ℂ} {c p : ℝ} {l : ℕ} {δ ζ : ℝ}
    (P₂ P : Finset ℂ) (hc : -1 < c) (hl : 2 ≤ l) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hζ : 0 < ζ)
    (hp : p < 1) (hhc : LocallyIntegrableOn h (Ioi 0)) (h0 : h =O[𝓝[>] 0] fun t => t ^ c)
    (hconv : ∀ z : ℂ, z.re = p → MellinConvergent (mellinTruncHigh h) z)
    (hH : ∀ z : ℂ, z.re ≤ p → H z = mellin (mellinTruncHigh h) z)
    (hP₂ : ∀ q ∈ P₂, p < q.re ∧ q.re ≤ 1) (h1P₂ : (1 : ℂ) ∈ P₂)
    (hP : ∀ q ∈ P, 1 < q.re ∧ q.re < l - δ)
    (hHd : DifferentiableOn ℂ (fun z => Complex.Gamma (1 - z) *
        (mellin (mellinTruncLow h) z + H z))
      ({z : ℂ | p ≤ z.re ∧ z.re ≤ l - δ} \ ((P₂ : Set ℂ) ∪ P ∪ {1})))
    (hdecay : Tendsto (fun y : ℝ => ⨆ σ : Icc p (l - δ), ‖Complex.Gamma (1 - (σ + y * I)) *
      (mellin (mellinTruncLow h) (σ + y * I) + H (σ + y * I))‖) (cocompact ℝ) (𝓝 0))
    (hl_int : VerticalIntegrable (fun z => Complex.Gamma (1 - z) *
        (mellin (mellinTruncLow h) z + H z)) (l - δ)) :
    laplaceTransform h ζ = mellin (mellinTruncLow h) 1 +
      ∑ q ∈ P₂, DLMF.AlgebraicAnalytic.residueAt
        (fun z => -((ζ : ℂ) ^ (z - 1) * Complex.Gamma (1 - z) * H z)) q +
      ∑ q ∈ P, DLMF.AlgebraicAnalytic.residueAt
        (fun z => -((ζ : ℂ) ^ (z - 1) * Complex.Gamma (1 - z) *
          (mellin (mellinTruncLow h) z + H z))) q +
      (ζ : ℂ)⁻¹ * mellinInv (l - δ) (fun z => Complex.Gamma (1 - z) *
        (mellin (mellinTruncLow h) z + H z)) ζ⁻¹ := by
  sorry

/-- DLMF 2.5.44: let `h` be locally integrable on `(0, ∞)` with `h(t) = O(t^c)` as `t → 0⁺`,
`c > -1`, and `h(t) ∼ ∑ bₙ t^{-βₙ}` as `t → ∞` (2.5.18 with `κ = 0`), `ℜβₙ` strictly
increasing to `∞` and no `βₙ` a positive integer. Let `H` be the continuation of `𝓜h₂`
(2.5.27) and `𝓜h(z) = 𝓜h₁(z) + H(z)` (2.5.28). Then as `ζ → 0⁺`
`𝓛h(ζ) ∼ ∑ bₙ Γ(1 - βₙ) ζ^{βₙ-1} + ∑ (-ζ)ⁿ/n! 𝓜h(n + 1)`, the two series interpreted
separately: the remainder after `N` and `M` terms is `O(ζ^{ℜβ_N - 1}) + O(ζ^M)`. -/
@[dlmf 2.5.E44, dlmf 2.5.iii]
theorem laplace_small_parameter {h : ℝ → ℂ} {b β : ℕ → ℂ} {c : ℝ} {H : ℂ → ℂ} (hc : -1 < c)
    (hhc : LocallyIntegrableOn h (Ioi 0)) (h0 : h =O[𝓝[>] 0] fun t => t ^ c)
    (hβ : StrictMono fun s => (β s).re) (hβinf : Tendsto (fun s => (β s).re) atTop atTop)
    (hβint : ∀ s (n : ℕ), β s ≠ n + 1)
    (hh : HasAsymptoticExpansion atTop (fun s (t : ℝ) => (t : ℂ) ^ (-β s)) b h)
    (hH : ∀ z : ℂ, z.re < (β 0).re → H z = mellin (mellinTruncHigh h) z)
    (hHd : ∀ N : ℕ, DifferentiableOn ℂ (fun z => H z + ∑ s ∈ range N, b s / (z - β s))
      {z : ℂ | z.re < (β N).re}) (N M : ℕ) :
    (fun ζ : ℝ => laplaceTransform h ζ -
        ∑ n ∈ range N, b n * Complex.Gamma (1 - β n) * (ζ : ℂ) ^ (β n - 1) -
        ∑ n ∈ range M, (-(ζ : ℂ)) ^ n / n ! *
          (mellin (mellinTruncLow h) (n + 1) + H (n + 1)))
      =O[𝓝[>] 0] fun ζ => ζ ^ ((β N).re - 1) + ζ ^ M := by
  sorry

/-- The factor `u(z) = -ζ^{z-1}/Γ(z)` of the Laplace residues 2.5.46–2.5.47. -/
private lemma hasDerivAt_neg_cpow_div_Gamma {ζ : ℝ} (hζ : 0 < ζ) (m : ℕ) :
    HasDerivAt (fun z : ℂ => -((ζ : ℂ) ^ (z - 1) * (Gamma z)⁻¹))
      ((-Real.log ζ + digamma (m + 1)) * (ζ : ℂ) ^ m / m !) (m + 1) := by
  have hζ0 : (ζ : ℂ) ≠ 0 := ofReal_ne_zero.2 hζ.ne'
  have hpos : 0 < ((m : ℂ) + 1).re := by simp; positivity
  have hG := (differentiableAt_Gamma_of_re_pos hpos).hasDerivAt
  have hΓ : Gamma ((m : ℂ) + 1) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hpos
  have hd := ((((hasDerivAt_id' ((m : ℂ) + 1)).sub_const 1).const_cpow (c := (ζ : ℂ))
    (Or.inl hζ0)).mul (hG.inv hΓ)).neg
  convert hd using 1
  simp only [Pi.inv_apply]
  rw [digamma_def, logDeriv_apply, Complex.Gamma_nat_eq_factorial, ← ofReal_log hζ.le,
    add_sub_cancel_right, cpow_natCast]
  rw [Complex.Gamma_nat_eq_factorial] at hΓ
  field_simp
  ring

/-- The truncated kernel `𝓜h₁` of `h(t) = 1/(1 + t)` is holomorphic on `ℜz > 0`. -/
private lemma mellin_truncLow_inv_one_add_differentiableAt {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ (mellin (mellinTruncLow fun t : ℝ => (((1 + t : ℝ)) : ℂ)⁻¹)) z := by
  set h : ℝ → ℂ := mellinTruncLow fun t : ℝ => (((1 + t : ℝ)) : ℂ)⁻¹
  have hbound : ∀ t : ℝ, 0 < t → ‖h t‖ ≤ 1 := by
    intro t ht
    simp only [h, mellinTruncLow, indicator]
    split_ifs
    · rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      exact inv_le_one_of_one_le₀ (by linarith)
    · simp
  have hcont : ContinuousOn (fun t : ℝ => (((1 + t : ℝ)) : ℂ)⁻¹) (Icc 0 1) := by
    intro t ht
    have : ((1 + t : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (by linarith [ht.1])
    exact ((continuous_ofReal.comp (continuous_const.add continuous_id)).continuousAt.inv₀
      this).continuousWithinAt
  have hli : LocallyIntegrableOn h (Ioi 0) := by
    refine IntegrableOn.locallyIntegrableOn ?_
    rw [IntegrableOn, show h = (Iic (1 : ℝ)).indicator _ from rfl,
      integrable_indicator_iff measurableSet_Iic, IntegrableOn,
      Measure.restrict_restrict measurableSet_Iic]
    exact hcont.integrableOn_Icc.mono_set fun t ht => ⟨le_of_lt ht.2, ht.1⟩
  refine mellin_differentiableAt_of_isBigO_rpow (a := z.re + 1) (b := 0) hli ?_
    (by linarith) ?_ hz
  · refine Asymptotics.IsBigO.of_bound 0 ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    simp [h, mellinTruncLow, not_le.2 ht]
  · refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simpa using hbound t ht

/-- DLMF 2.5.46: for `ζ > 0` and `k ≥ 1`,
`Res_{z=k}[-ζ^{z-1} Γ(1 - z) π csc(πz)] = (-ln ζ + ψ(k)) ζ^{k-1}/(k-1)!`; here
`h(t) = 1/(1 + t)` (2.5.45), `𝓜h(z) = π csc(πz)`, `κ = 0`, `βₛ = s + 1`, `c = 0`. -/
@[dlmf 2.5.E45, dlmf 2.5.E46]
theorem residueAt_laplace_inv_one_add {ζ : ℝ} (hζ : 0 < ζ) {k : ℕ} (hk : 1 ≤ k) :
    DLMF.AlgebraicAnalytic.residueAt (fun z => -((ζ : ℂ) ^ (z - 1) * Complex.Gamma (1 - z) *
        (π / Complex.sin (π * z)))) k =
      (-Real.log ζ + digamma k) * (ζ : ℂ) ^ (k - 1) / (k - 1)! := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hζ0 : (ζ : ℂ) ≠ 0 := ofReal_ne_zero.2 hζ.ne'
  have hball : ∀ z ∈ ball (((m + 1 : ℕ) : ℤ) : ℂ) (1 / 2), 0 < z.re := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have hre := (abs_re_le_norm _).trans_lt hz
    simp only [sub_re, Int.cast_natCast, natCast_re, abs_lt] at hre
    push_cast at hre
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hu : DifferentiableOn ℂ (fun z : ℂ => -((ζ : ℂ) ^ (z - 1) * (Gamma z)⁻¹))
      (ball (((m + 1 : ℕ) : ℤ) : ℂ) (1 / 2)) := fun z _ =>
    (((differentiableAt_id.sub_const 1).const_cpow (Or.inl hζ0)).mul
      (differentiable_one_div_Gamma z |>.congr_of_eventuallyEq
        (Eventually.of_forall fun _ => by simp))).neg.differentiableWithinAt
  have h := residueAt_mul_pi_div_sin_sq_add
    (f := fun z => -((ζ : ℂ) ^ (z - 1) * Complex.Gamma (1 - z) * (π / Complex.sin (π * z))))
    (v := fun _ => 0) (by norm_num) hu
    (differentiableOn_const 0) fun z hz _ => by
      have hΓ := Complex.Gamma_ne_zero_of_re_pos (hball z hz)
      have hr := Complex.Gamma_mul_Gamma_one_sub z
      have : Gamma (1 - z) = π / Complex.sin (π * z) / Gamma z := by
        rw [← hr]; field_simp
      rw [this]; simp only [zero_div, add_zero]; field_simp
  simp only [Int.cast_natCast, add_zero] at h
  rw [h, show (((m + 1 : ℕ)) : ℂ) = (m : ℂ) + 1 by push_cast; ring,
    (hasDerivAt_neg_cpow_div_Gamma hζ m).deriv]
  simp

/-- DLMF 2.5.47: for `ζ > 0`, with `h(t) = 1/(1 + t)` and the continuation
`𝓜h₂(z) = π csc(πz) - 𝓜h₁(z)` (2.5.28),
`Res_{z=1}[-ζ^{z-1} Γ(1 - z) 𝓜h₂(z)] = (-ln ζ - γ) - 𝓜h₁(1)`. -/
@[dlmf 2.5.E47]
theorem residueAt_laplace_inv_one_add_truncHigh {ζ : ℝ} (hζ : 0 < ζ) :
    DLMF.AlgebraicAnalytic.residueAt (fun z => -((ζ : ℂ) ^ (z - 1) * Complex.Gamma (1 - z) *
        (π / Complex.sin (π * z) -
          mellin (mellinTruncLow fun t : ℝ => (((1 + t : ℝ)) : ℂ)⁻¹) z))) 1 =
      (-Real.log ζ - Real.eulerMascheroniConstant) -
        mellin (mellinTruncLow fun t : ℝ => (((1 + t : ℝ)) : ℂ)⁻¹) 1 := by
  set M := mellin (mellinTruncLow fun t : ℝ => (((1 + t : ℝ)) : ℂ)⁻¹)
  have hζ0 : (ζ : ℂ) ≠ 0 := ofReal_ne_zero.2 hζ.ne'
  have hball : ∀ z ∈ ball ((1 : ℤ) : ℂ) (1 / 2), 0 < z.re ∧ 0 < (2 - z).re := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have hre := (abs_re_le_norm _).trans_lt hz
    simp only [sub_re, Int.cast_one, one_re, abs_lt] at hre
    simp only [sub_re, re_ofNat]
    constructor <;> linarith
  have hu : DifferentiableOn ℂ (fun z : ℂ => -((ζ : ℂ) ^ (z - 1) * (Gamma z)⁻¹))
      (ball ((1 : ℤ) : ℂ) (1 / 2)) := fun z _ =>
    (((differentiableAt_id.sub_const 1).const_cpow (Or.inl hζ0)).mul
      (differentiable_one_div_Gamma z |>.congr_of_eventuallyEq
        (Eventually.of_forall fun _ => by simp))).neg.differentiableWithinAt
  have hv : DifferentiableOn ℂ (fun z : ℂ => -((ζ : ℂ) ^ (z - 1) * Gamma (2 - z) * M z))
      (ball ((1 : ℤ) : ℂ) (1 / 2)) := fun z hz =>
    ((((differentiableAt_id.sub_const 1).const_cpow (Or.inl hζ0)).mul
      ((differentiableAt_Gamma_of_re_pos (hball z hz).2).comp z
        (differentiableAt_const _ |>.sub differentiableAt_id))).mul
      (mellin_truncLow_inv_one_add_differentiableAt (hball z hz).1)).neg.differentiableWithinAt
  have h := residueAt_mul_pi_div_sin_sq_add
    (f := fun z => -((ζ : ℂ) ^ (z - 1) * Complex.Gamma (1 - z) *
        (π / Complex.sin (π * z) - M z))) (by norm_num) hu hv fun z hz hz1 => by
      have hΓ := Complex.Gamma_ne_zero_of_re_pos (hball z hz).1
      have hr := Complex.Gamma_mul_Gamma_one_sub z
      have h1 : Gamma (1 - z) = π / Complex.sin (π * z) / Gamma z := by
        rw [← hr]; field_simp
      have hz1' : z - 1 ≠ 0 := sub_ne_zero.2 (by simpa using hz1)
      have h2 : Gamma (1 - z) = -(Gamma (2 - z) / (z - 1)) := by
        have := Complex.Gamma_add_one (1 - z) (by intro h; apply hz1'; linear_combination -h)
        rw [show 1 - z + 1 = 2 - z by ring] at this
        rw [this]; field_simp; ring
      simp only [Int.cast_one]
      linear_combination (-((ζ : ℂ) ^ (z - 1) * (π / Complex.sin (π * z)))) * h1 +
        ((ζ : ℂ) ^ (z - 1) * M z) * h2
  simp only [Int.cast_one] at h
  have hd := (hasDerivAt_neg_cpow_div_Gamma hζ 0).deriv
  simp only [Nat.cast_zero, zero_add] at hd
  rw [h, hd, show (2 : ℂ) - 1 = 1 by norm_num, Complex.Gamma_one]
  simp [digamma_one]
  ring

/-- DLMF 2.5.45 and 2.5.49 for real `ζ > 0`: `𝓛h(ζ) = ∫₀^∞ e^{-ζt}/(1 + t) dt = e^ζ E₁(ζ)`,
from the Stieltjes form 6.2.2 of `E₁` (`DLMF.Confluent.expIntE1_stieltjes`). -/
@[dlmf 2.5.E45, dlmf 2.5.E49]
theorem laplace_inv_one_add_eq {ζ : ℝ} (hζ : 0 < ζ) :
    laplaceTransform (fun t : ℝ => (((1 + t : ℝ)) : ℂ)⁻¹) ζ =
      Complex.exp ζ * DLMF.Confluent.genExpIntE 1 ζ := by
  have hS : (ζ : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.2 hζ
  rw [DLMF.Confluent.expIntE1_stieltjes hS, ← mul_assoc, ← Complex.exp_add, add_neg_cancel,
    Complex.exp_zero, one_mul]
  have h := integral_comp_mul_left_Ioi
    (fun t : ℝ => Complex.exp (-(t : ℂ)) / ((t : ℂ) + ζ)) 0 hζ
  rw [mul_zero] at h
  have h' : (∫ t in Ioi (0 : ℝ), Complex.exp (-(t : ℂ)) / ((t : ℂ) + ζ)) =
      ζ • ∫ x in Ioi (0 : ℝ), Complex.exp (-((ζ * x : ℝ) : ℂ)) / (((ζ * x : ℝ) : ℂ) + ζ) := by
    rw [h, smul_inv_smul₀ hζ.ne']
  rw [h', ← integral_smul, laplaceTransform]
  refine setIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) => ?_
  have hx1 : ((1 + x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (1 + x : ℝ) ≠ 0)
  have hζ0 : (ζ : ℂ) ≠ 0 := by exact_mod_cast hζ.ne'
  have hd : ((ζ * x : ℝ) : ℂ) + ζ = ζ * ((1 + x : ℝ) : ℂ) := by push_cast; ring
  simp only [Complex.real_smul, hd]
  rw [show -((ζ * x : ℝ) : ℂ) = -(ζ : ℂ) * x by push_cast; ring]
  field_simp

/-- DLMF 2.5.49: `𝓛h(ζ) = e^ζ E₁(ζ)` for `ℜζ > 0`, `h(t) = 1/(1 + t)`. -/
@[dlmf 2.5.E49]
theorem laplace_inv_one_add_eq_complex {ζ : ℂ} (hζ : 0 < ζ.re) :
    laplaceTransform (fun t : ℝ => (((1 + t : ℝ)) : ℂ)⁻¹) ζ =
      Complex.exp ζ * DLMF.Confluent.genExpIntE 1 ζ := by
  rw [DLMF.Confluent.genExpIntE_stieltjes (by norm_num) hζ]
  simp only [sub_self, cpow_zero, Complex.Gamma_one, div_one, one_mul, laplaceTransform]
  rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  push_cast; ring

/-- DLMF 2.5.48 (convergent form, stronger than DLMF): for `ζ > 0`,
`𝓛h(ζ) = (-ln ζ) ∑ ζᵏ/k! + ∑ ψ(k + 1) ζᵏ/k!` with both series convergent, for
`h(t) = 1/(1 + t)`; from 2.5.49 and DLMF 6.6.3. -/
@[dlmf 2.5.E48]
theorem hasSum_laplace_inv_one_add {ζ : ℝ} (hζ : 0 < ζ) :
    HasSum (fun k : ℕ => (-(Real.log ζ : ℂ) + digamma (k + 1)) * (ζ : ℂ) ^ k / k !)
      (laplaceTransform (fun t : ℝ => (((1 + t : ℝ)) : ℂ)⁻¹) ζ) := by
  have hζ0 : (ζ : ℂ) ≠ 0 := by exact_mod_cast hζ.ne'
  have h1 := DLMF.Confluent.expIntE1_digamma_series hζ0
  have h2 : HasSum (fun k : ℕ => (ζ : ℂ) ^ k / k !) (Complex.exp ζ) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp (ζ : ℂ)
  have h3 := (h2.mul_left (-(Real.log ζ : ℂ))).add h1
  rw [laplace_inv_one_add_eq hζ]
  convert h3 using 1
  · funext k
    ring
  · rw [← ofReal_log hζ.le]
    ring

/-- DLMF 2.5.48 (asymptotic form): for `h(t) = 1/(1 + t)`, as `ζ → 0⁺`,
`𝓛h(ζ) - ∑_{k<N} (-ln ζ + ψ(k + 1)) ζᵏ/k! = O(ζᴺ ln(1/ζ))` for every `N`. -/
@[dlmf 2.5.E48]
theorem laplace_inv_one_add_isBigO (N : ℕ) :
    (fun ζ : ℝ => laplaceTransform (fun t : ℝ => (((1 + t : ℝ)) : ℂ)⁻¹) ζ -
        ∑ k ∈ range N, (-(Real.log ζ : ℂ) + digamma (k + 1)) * (ζ : ℂ) ^ k / k !)
      =O[𝓝[>] 0] fun ζ => ζ ^ N * (1 + |Real.log ζ|) := by
  obtain ⟨C, hC⟩ := DLMF.Hypergeometric.exists_norm_digamma_add_nat_le (x := 1)
    (fun m h => by
      have : ((1 : ℝ) : ℂ) = ((-(m : ℝ) : ℝ) : ℂ) := by push_cast; exact h
      have h' := Complex.ofReal_injective this
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  set D : ℝ := max C 1 with hD
  set g : ℕ → ℝ := fun k => (N + 1) * 2 ^ k / k ! with hg
  have hgs : Summable g := by
    have := (Real.summable_pow_div_factorial 2).mul_left ((N : ℝ) + 1)
    refine this.congr fun k => ?_
    simp only [hg]; ring
  refine IsBigO.of_bound (D * ∑' k, g k) ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ζ hζ
  have hζ0 : 0 < ζ := hζ.1
  set term : ℕ → ℂ := fun k => (-(Real.log ζ : ℂ) + digamma (k + 1)) * (ζ : ℂ) ^ k / k !
    with hterm
  have hS : HasSum (fun k => term (k + N))
      (laplaceTransform (fun t : ℝ => (((1 + t : ℝ)) : ℂ)⁻¹) ζ - ∑ k ∈ range N, term k) :=
    (hasSum_nat_add_iff' N).mpr (hasSum_laplace_inv_one_add hζ0)
  have hbound : ∀ k : ℕ, ‖term (k + N)‖ ≤ ζ ^ N * (1 + |Real.log ζ|) * (D * g k) := by
    intro k
    have hdig : ‖digamma (((k + N : ℕ) : ℂ) + 1)‖ ≤ C * ((k + N : ℕ) + 1) := by
      rw [add_comm]; exact hC (k + N)
    have hk1 : (1 : ℝ) ≤ ((k + N : ℕ) : ℝ) + 1 := by
      linarith [(Nat.cast_nonneg (k + N) : (0:ℝ) ≤ _)]
    have hkN : ((k + N : ℕ) : ℝ) + 1 ≤ (N + 1) * 2 ^ k := by
      have h2 : (k : ℝ) + 1 ≤ 2 ^ k := by
        have := Nat.lt_two_pow_self (n := k)
        exact_mod_cast this
      push_cast
      nlinarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k), (Nat.cast_nonneg N : (0:ℝ) ≤ N)]
    have h1 : ‖-(Real.log ζ : ℂ) + digamma (((k + N : ℕ) : ℂ) + 1)‖ ≤
        (1 + |Real.log ζ|) * (D * (((k + N : ℕ) : ℝ) + 1)) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]
      have hC' : C * (((k + N : ℕ) : ℝ) + 1) ≤ D * (((k + N : ℕ) : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
      have hD1 : 1 ≤ D := le_max_right _ _
      have hDm : 1 ≤ D * (((k + N : ℕ) : ℝ) + 1) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hDm (abs_nonneg (Real.log ζ))]
    have h2 : ‖(ζ : ℂ) ^ (k + N) / ((k + N)! : ℂ)‖ ≤ ζ ^ N / k ! := by
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hζ0,
        Complex.norm_natCast, pow_add]
      have hk : (k ! : ℝ) ≤ (k + N)! := by exact_mod_cast Nat.factorial_le (by omega)
      have hk0 : (0 : ℝ) < k ! := by positivity
      have hζk : ζ ^ k ≤ 1 := pow_le_one₀ hζ0.le hζ.2.le
      rw [div_le_div_iff₀ (by positivity) hk0]
      calc ζ ^ k * ζ ^ N * k ! ≤ 1 * ζ ^ N * (k + N)! := by gcongr
        _ = ζ ^ N * (k + N)! := by ring
    have heq : term (k + N) = (-(Real.log ζ : ℂ) + digamma (((k + N : ℕ) : ℂ) + 1)) *
        ((ζ : ℂ) ^ (k + N) / ((k + N)! : ℂ)) := by
      simp only [hterm]; ring
    rw [heq, norm_mul]
    calc _ ≤ (1 + |Real.log ζ|) * (D * (((k + N : ℕ) : ℝ) + 1)) * (ζ ^ N / k !) := by
          gcongr
      _ ≤ (1 + |Real.log ζ|) * (D * ((N + 1) * 2 ^ k)) * (ζ ^ N / k !) := by
          have hD0 : 0 ≤ D := le_trans zero_le_one (le_max_right _ _)
          gcongr
      _ = _ := by simp only [hg]; ring
  have hsum := hgs.mul_left (ζ ^ N * (1 + |Real.log ζ|) * D)
  have hle := norm_tsum_le_tsum_norm ?_ |>.trans (hS.summable.norm.tsum_le_tsum hbound ?_)
  · rw [hS.tsum_eq] at hle
    have hpos : 0 ≤ ζ ^ N * (1 + |Real.log ζ|) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hpos]
    calc _ ≤ _ := hle
      _ = ζ ^ N * (1 + |Real.log ζ|) * D * ∑' k, g k := by
          rw [← tsum_mul_left]; congr 1; funext k; ring
      _ = _ := by ring
  · exact hS.summable.norm
  · exact (hgs.mul_left D).mul_left (ζ ^ N * (1 + |Real.log ζ|))

end DLMF.AsymptoticApproximations
