/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.MellinConvolution
public import DLMF.AlgebraicAnalytic.Transforms.Basic
public import DLMF.AsymptoticApproximations.Mellin.Basic
public import DLMF.AlgebraicAnalytic.Complex.Basic
public import DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion
public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# Mellin transform methods (DLMF §2.5(i)–(ii))

The Mellin transform 2.5.1 is Mathlib's `mellin`, the inversion integral 2.5.2 along
`ℜz = c` is `mellinInv c` (`(2πi)⁻¹ ∫_{c-i∞}^{c+i∞} x^{-z} F(z) dz = mellinInv c F x`), and the
inversion theorem is `mellinInv_mellin_eq` (see `MathlibCoverage`). Residues are
`DLMF.AlgebraicAnalytic.residueAt` (§1.10(iii)), the circle integral `(2πi)⁻¹ ∮ F` around a small
circle.

* 2.5.3–2.5.5: the Mellin convolution `I(x) = ∫₀^∞ f(t) h(xt) dt` and the Parseval formula;
* 2.5.6–2.5.7, 2.5.34–2.5.36: shifting the line of integration past finitely many poles, and
  `E(x) = o(x^{-q})` by the Riemann–Lebesgue lemma (proved);
* §2.5(ii): the truncations `f₁, f₂, h₁, h₂` (2.5.21–2.5.24), the domains of convergence of
  Tables 2.5.1–2.5.2 (proved), the continuations 2.5.25–2.5.28, and the splitting 2.5.29–2.5.31
  (proved).

Mellin convergence `MellinConvergent f z` is absolute convergence of `∫₀^∞ t^{z-1} f(t) dt`.
In the convolution theorems the transforms are required to converge absolutely on the line of
integration; then the double integral converges absolutely (Tonelli).
The convolution theorem reuses the logarithmic-coordinate convolution API in
`DLMFMathlib.Analysis.MellinConvolution`, together with Mathlib’s `mellin_comp_inv`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Finset Asymptotics Complex
open scoped Topology Real

namespace DLMF.AsymptoticApproximations

/-! ## §2.5(i) Convolution and Parseval formula -/

/-- The kernel `f(1/y)/y` has Mellin convergence at `s` when `f` converges at `1-s`. -/
private lemma reciprocal_mellinConvergent {f : ℝ → ℂ} {s : ℂ}
    (hf : MellinConvergent f (1 - s)) :
    MellinConvergent (fun y => f y⁻¹ / y) s := by
  have hi : MellinConvergent (fun y => f y⁻¹) (s - 1) := by
    have hs : (s - 1) / ((-1 : ℝ) : ℂ) = 1 - s := by push_cast; ring
    have h := (MellinConvergent.comp_rpow (f := f) (s := s - 1) (a := -1)
      (by norm_num)).mpr (by simpa only [hs] using hf)
    simpa only [Real.rpow_neg_one] using h
  have h := (MellinConvergent.cpow_smul (f := fun y => f y⁻¹) (s := s) (a := -1)).mpr
    (by simpa only [sub_eq_add_neg] using hi)
  simpa only [cpow_neg_one, smul_eq_mul, div_eq_mul_inv, mul_comm] using h

/-- Inverting the convolution variable relates the two Mellin convolution conventions. -/
private lemma reciprocal_mellinConvolution (f h : ℝ → ℂ) (x : ℝ) :
    DLMF.AlgebraicAnalytic.mellinConvolution (fun y => f y⁻¹ / y) h x =
      ∫ t in Ioi 0, f t * h (x * t) := by
  have he := mellin_comp_inv (fun y => f y * h (x * y)) (-1 : ℂ)
  have hleft : mellin (fun y => f y⁻¹ * h (x * y⁻¹)) (-1) =
      DLMF.AlgebraicAnalytic.mellinConvolution (fun y => f y⁻¹ / y) h x := by
    unfold mellin DLMF.AlgebraicAnalytic.mellinConvolution
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    dsimp only
    rw [show (-1 : ℂ) - 1 = -(2 : ℂ) by norm_num, cpow_neg, cpow_two]
    simp only [smul_eq_mul]
    rw [div_eq_mul_inv x y]
    field_simp
  rw [hleft] at he
  simpa only [neg_neg, mellin, sub_self, cpow_zero, one_smul] using he


/-- DLMF 2.5.3–2.5.4: if `𝓜f(1 - z)` and `𝓜h(z)` converge absolutely, then the Mellin
convolution `I(x) = ∫₀^∞ f(t) h(xt) dt` has Mellin transform `𝓜I(z) = 𝓜f(1 - z) 𝓜h(z)`. -/
@[dlmf 2.5.E3, dlmf 2.5.E4]
theorem mellin_convolution {f h : ℝ → ℂ} {z : ℂ} (hf : MellinConvergent f (1 - z))
    (hh : MellinConvergent h z) :
    MellinConvergent (fun x => ∫ t in Ioi 0, f t * h (x * t)) z ∧
      mellin (fun x => ∫ t in Ioi 0, f t * h (x * t)) z = mellin f (1 - z) * mellin h z := by
  have hfi := reciprocal_mellinConvergent hf
  have he : HasMellin (DLMF.AlgebraicAnalytic.mellinConvolution (fun y => f y⁻¹ / y) h)
      z (mellin (fun y => f y⁻¹ / y) z * mellin h z) := hasMellin_integral_mul_div hfi hh
  change MellinConvergent (DLMF.AlgebraicAnalytic.mellinConvolution (fun y => f y⁻¹ / y) h) z ∧
    mellin (DLMF.AlgebraicAnalytic.mellinConvolution (fun y => f y⁻¹ / y) h) z =
      mellin (fun y => f y⁻¹ / y) z * mellin h z at he
  have hfun := funext (reciprocal_mellinConvolution f h)
  rw [hfun] at he
  have hmel : mellin (fun y => f y⁻¹ / y) z = mellin f (1 - z) := by
    have h := mellin_cpow_smul (fun y => f y⁻¹) z (-1)
    simp only [cpow_neg_one, smul_eq_mul] at h
    rw [mellin_comp_inv] at h
    convert h using 1
    · congr 1; funext y; ring
    · congr 1; ring
  rwa [hmel] at he

/-- DLMF 2.5.5 (Parseval formula; also 2.5.33 and 2.5.40): if `𝓜f(1 - z)` and `𝓜h(z)` converge
absolutely on the line `ℜz = c`, their product is integrable along that line and `I` is
continuous at `x > 0`, then `I(x) = (2πi)⁻¹ ∫_{c-i∞}^{c+i∞} x^{-z} 𝓜f(1 - z) 𝓜h(z) dz`. The case
`x = 1` is a Parseval-type formula (§1.14(iv)). -/
@[dlmf 2.5.E5, dlmf 2.5.E33, dlmf 2.5.i]
theorem mellin_convolution_eq_mellinInv {f h : ℝ → ℂ} {c x : ℝ} (hx : 0 < x)
    (hconv : ∀ z : ℂ, z.re = c → MellinConvergent f (1 - z) ∧ MellinConvergent h z)
    (hint : VerticalIntegrable (fun z => mellin f (1 - z) * mellin h z) c)
    (hcont : ContinuousAt (fun x => ∫ t in Ioi 0, f t * h (x * t)) x) :
    (∫ t in Ioi 0, f t * h (x * t)) =
      mellinInv c (fun z => mellin f (1 - z) * mellin h z) x := by
  set Iv : ℝ → ℂ := fun x => ∫ t in Ioi 0, f t * h (x * t) with hIv
  have hline : ∀ y : ℝ, mellin Iv ((c : ℂ) + y * I) =
      mellin f (1 - ((c : ℂ) + y * I)) * mellin h ((c : ℂ) + y * I) := fun y => by
    have hz := hconv ((c : ℂ) + y * I) (by simp)
    exact (mellin_convolution hz.1 hz.2).2
  have hIc : MellinConvergent Iv (c : ℂ) := by
    have hz := hconv (c : ℂ) (by simp)
    exact (mellin_convolution hz.1 hz.2).1
  have hV : VerticalIntegrable (mellin Iv) c := by
    unfold VerticalIntegrable at hint ⊢
    simp only [hline]
    exact hint
  have h1 := mellinInv_mellin_eq c Iv hx hIc hV hcont
  change Iv x = _
  rw [← h1]
  unfold mellinInv
  simp only [hline]

/-- DLMF 2.5.6–2.5.7 and 2.5.34–2.5.35 (shifting the line of integration): let `d < c`, let `G`
be differentiable on the closed strip `d ≤ ℜz ≤ c` except at the points of a finite set `P` of
poles in the open strip `d < ℜz < c`, let `G(σ + iy) → 0` as `y → ±∞` uniformly for
`d ≤ σ ≤ c` (2.5.34), and let `G` be integrable along both lines. Then for `x > 0`,
`(2πi)⁻¹ ∫_{(c)} x^{-z} G(z) dz = ∑_{p ∈ P} Res_{z=p}[x^{-z} G(z)] + E(x)`, with
`E(x) = (2πi)⁻¹ ∫_{(d)} x^{-z} G(z) dz` (2.5.7). Read from left to right this is 2.5.6; read
with `(p_{jk}, q_{jk}) = (d, c)` it is 2.5.35, `I_{jk} = ∑ Res[-x^{-z} G_{jk}] + E_{jk}`. -/
@[dlmf 2.5.E6, dlmf 2.5.E7, dlmf 2.5.E34, dlmf 2.5.E35]
theorem mellinInv_shift {G : ℂ → ℂ} {c d x : ℝ} (hdc : d < c) (hx : 0 < x) (P : Finset ℂ)
    (hP : ∀ p ∈ P, d < p.re ∧ p.re < c)
    (hG : DifferentiableOn ℂ G ({z : ℂ | d ≤ z.re ∧ z.re ≤ c} \ (P : Set ℂ)))
    (hdecay : Tendsto (fun y : ℝ => ⨆ σ : Icc d c, ‖G (σ + y * I)‖) (cocompact ℝ) (𝓝 0))
    (hc : VerticalIntegrable G c) (hd : VerticalIntegrable G d) :
    mellinInv c G x = ∑ p ∈ P, DLMF.AlgebraicAnalytic.residueAt
      (fun z => (x : ℂ) ^ (-z) * G z) p + mellinInv d G x := by
  sorry

/-- Helper for `mellinInv_isLittleO`: the integrand of `mellinInv q G x` as a Fourier
integrand. -/
private lemma g2a_mellinInv_integrand {q x : ℝ} (hx : 0 < x) (G : ℂ → ℂ) (y : ℝ) :
    (x : ℂ) ^ (-((q : ℂ) + y * I)) • G (q + y * I) =
      ((x ^ (-q) : ℝ) : ℂ) * ((Real.fourierChar (-(y * (Real.log x / (2 * π)))) : ℂ) *
        G (q + y * I)) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [smul_eq_mul, cpow_def_of_ne_zero hx0, Real.rpow_def_of_pos hx, Real.fourierChar_apply,
    ← ofReal_log hx.le]
  push_cast
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  field_simp
  ring

/-- DLMF 2.5.36: the remainder integral `E(x) = (2πi)⁻¹ ∫_{q-i∞}^{q+i∞} x^{-z} G(z) dz` is
`o(x^{-q})` as `x → +∞`, by the Riemann–Lebesgue lemma (§1.8(i)). Stronger than DLMF: no
hypothesis on `G` is needed (for `G` not integrable along `ℜz = q` both sides are `0` in Mathlib's
convention). -/
@[dlmf 2.5.E36]
theorem mellinInv_isLittleO (G : ℂ → ℂ) (q : ℝ) :
    (fun x => mellinInv q G x) =o[atTop] fun x => ((x ^ (-q) : ℝ) : ℂ) := by
  set u : ℝ → ℂ := fun x => (1 / (2 * π) : ℝ) •
    ∫ y : ℝ, Real.fourierChar (-(y * (Real.log x / (2 * π)))) • G (q + y * I)
  have hu : Tendsto u atTop (𝓝 0) := by
    have hRL := Real.tendsto_integral_exp_smul_cocompact (fun y : ℝ => G (q + y * I))
    have hlog : Tendsto (fun x : ℝ => Real.log x / (2 * π)) atTop (cocompact ℝ) :=
      (Real.tendsto_log_atTop.atTop_div_const (by positivity)).mono_right
        atTop_le_cocompact
    have := (hRL.comp hlog).const_smul (1 / (2 * π) : ℝ)
    simpa [u] using this
  have heq : (fun x => mellinInv q G x) =ᶠ[atTop] fun x => ((x ^ (-q) : ℝ) : ℂ) * u x := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [mellinInv, u, g2a_mellinInv_integrand hx, Circle.smul_def, smul_eq_mul]
    rw [integral_const_mul]
    simp only [Complex.real_smul]
    push_cast
    ring
  refine IsLittleO.congr' ?_ heq.symm EventuallyEq.rfl
  simpa using (isBigO_refl (fun x : ℝ => ((x ^ (-q) : ℝ) : ℂ)) atTop).mul_isLittleO
    ((isLittleO_one_iff ℂ).2 hu)

/-! ## §2.5(ii) Truncated functions and domains of convergence -/

/-- Helper: the restriction of a locally integrable function by an indicator. -/
private lemma g2a_locallyIntegrableOn_indicator {f : ℝ → ℂ} {s t : Set ℝ}
    (hf : LocallyIntegrableOn f s) (ht : MeasurableSet t) :
    LocallyIntegrableOn (t.indicator f) s := by
  intro x hx
  obtain ⟨U, hU, h'U⟩ := hf x hx
  exact ⟨U, hU, h'U.indicator ht⟩

/-- DLMF Table 2.5.1, row 1: if `f` is locally integrable on `(0, ∞)` and `f(t) = O(t^{α})` as
`t → 0⁺` (implied by 2.5.17 with `α = ℜα₀`), then `𝓜f₁(z)` converges absolutely for
`ℜz > -α`. -/
@[dlmf 2.5.T1, dlmf 2.5.ii]
theorem mellinConvergent_truncLow {f : ℝ → ℂ} {α : ℝ} (hfc : LocallyIntegrableOn f (Ioi 0))
    (hf0 : f =O[𝓝[>] 0] fun t => t ^ α) {z : ℂ} (hz : -α < z.re) :
    MellinConvergent (mellinTruncLow f) z := by
  have hc : LocallyIntegrableOn (mellinTruncLow f) (Ioi 0) := by
    unfold mellinTruncLow
    exact g2a_locallyIntegrableOn_indicator hfc measurableSet_Iic
  refine mellinConvergent_of_isBigO_rpow hc (a := z.re + 1) ?_ (by linarith) ?_ hz
  · refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop 1] with t ht
    rw [mellinTruncLow, indicator_of_notMem (show t ∉ Set.Iic 1 from not_le.2 ht)]
  · simp only [neg_neg]
    refine IsBigO.trans ?_ hf0
    refine (isBigO_refl _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    rw [mellinTruncLow, indicator_of_mem (show t ∈ Set.Iic 1 from ht.2.le)]

/-- DLMF Table 2.5.1, row 2: if `f` is locally integrable on `(0, ∞)` and `f(t) = O(t^{-b})` as
`t → ∞` (2.5.19), then `𝓜f₂(z)` converges absolutely for `ℜz < b`. -/
@[dlmf 2.5.T1, dlmf 2.5.E19]
theorem mellinConvergent_truncHigh {f : ℝ → ℂ} {b : ℝ} (hfc : LocallyIntegrableOn f (Ioi 0))
    (hf : f =O[atTop] fun t => t ^ (-b)) {z : ℂ} (hz : z.re < b) :
    MellinConvergent (mellinTruncHigh f) z := by
  have h2 : mellinTruncHigh f = (Ioi (1 : ℝ)).indicator f := by
    funext t
    by_cases ht : t ≤ 1
    · simp [mellinTruncHigh, mellinTruncLow, ht]
    · simp [mellinTruncHigh, mellinTruncLow, ht, not_le.1 ht]
  have hc : LocallyIntegrableOn (mellinTruncHigh f) (Ioi 0) := by
    rw [h2]
    exact g2a_locallyIntegrableOn_indicator hfc measurableSet_Ioi
  refine mellinConvergent_of_isBigO_rpow hc ?_ hz (b := z.re - 1) ?_ (by linarith)
  · refine IsBigO.trans ?_ hf
    refine (isBigO_refl _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop 1] with t ht
    rw [h2, indicator_of_mem (show t ∈ Set.Ioi 1 from ht)]
  · refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    rw [h2, indicator_of_notMem (show t ∉ Set.Ioi 1 from not_lt.2 ht.2.le)]

/-- DLMF Table 2.5.1, rows 3–4: if `h` is locally integrable on `(0, ∞)`, `h(t) = O(t^c)` as
`t → 0⁺` (2.5.20) and `h(t) = O(t^{-β})` as `t → ∞` (implied by 2.5.18 with `β = ℜβ₀`, since
`|exp(iκt^p)| = 1` for real `κ`, `p`), then `𝓜h₁(z)` converges absolutely for `ℜz > -c` and
`𝓜h₂(z)` for `ℜz < β`. -/
@[dlmf 2.5.T1, dlmf 2.5.E20]
theorem mellinConvergent_trunc_h {h : ℝ → ℂ} {c β : ℝ} (hhc : LocallyIntegrableOn h (Ioi 0))
    (h0 : h =O[𝓝[>] 0] fun t => t ^ c) (hinf : h =O[atTop] fun t => t ^ (-β)) :
    (∀ z : ℂ, -c < z.re → MellinConvergent (mellinTruncLow h) z) ∧
      ∀ z : ℂ, z.re < β → MellinConvergent (mellinTruncHigh h) z :=
  ⟨fun _ hz => mellinConvergent_truncLow hhc h0 hz,
    fun _ hz => mellinConvergent_truncHigh hhc hinf hz⟩

/-- DLMF Table 2.5.2: under the hypotheses of Table 2.5.1 (`f = O(t^α)` at `0⁺`,
`f = O(t^{-b})` at `∞`, `h = O(t^c)` at `0⁺`, `h = O(t^{-β})` at `∞`), the transform pairs
`𝓜f_j(1 - z)`, `𝓜h_k(z)` converge absolutely in the domains
`D₁₁ : -c < ℜz < 1 + α`, `D₁₂ : ℜz < min(1 + α, β)`, `D₂₁ : max(-c, 1 - b) < ℜz`,
`D₂₂ : 1 - b < ℜz < β`. -/
@[dlmf 2.5.T2]
theorem mellinConvergent_pairs {f h : ℝ → ℂ} {α b c β : ℝ}
    (hfc : LocallyIntegrableOn f (Ioi 0)) (hf0 : f =O[𝓝[>] 0] fun t => t ^ α)
    (hf : f =O[atTop] fun t => t ^ (-b)) (hhc : LocallyIntegrableOn h (Ioi 0))
    (h0 : h =O[𝓝[>] 0] fun t => t ^ c) (hinf : h =O[atTop] fun t => t ^ (-β)) (z : ℂ) :
    (-c < z.re → z.re < 1 + α →
      MellinConvergent (mellinTruncLow f) (1 - z) ∧ MellinConvergent (mellinTruncLow h) z) ∧
    (z.re < 1 + α → z.re < β →
      MellinConvergent (mellinTruncLow f) (1 - z) ∧ MellinConvergent (mellinTruncHigh h) z) ∧
    (-c < z.re → 1 - b < z.re →
      MellinConvergent (mellinTruncHigh f) (1 - z) ∧ MellinConvergent (mellinTruncLow h) z) ∧
    (1 - b < z.re → z.re < β →
      MellinConvergent (mellinTruncHigh f) (1 - z) ∧ MellinConvergent (mellinTruncHigh h) z) := by
  have hre : (1 - z).re = 1 - z.re := by simp
  have hL : z.re < 1 + α → MellinConvergent (mellinTruncLow f) (1 - z) := fun h1 =>
    mellinConvergent_truncLow hfc hf0 (by rw [hre]; linarith)
  have hH : 1 - b < z.re → MellinConvergent (mellinTruncHigh f) (1 - z) := fun h1 =>
    mellinConvergent_truncHigh hfc hf (by rw [hre]; linarith)
  have hh := mellinConvergent_trunc_h hhc h0 hinf
  exact ⟨fun h1 h2 => ⟨hL h2, hh.1 z h1⟩, fun h1 h2 => ⟨hL h1, hh.2 z h2⟩,
    fun h1 h2 => ⟨hH h2, hh.1 z h1⟩, fun h1 h2 => ⟨hH h1, hh.2 z h2⟩⟩

/-- DLMF 2.5.25 and §2.5(ii): let `f` be locally integrable on `(0, ∞)` with
`f(t) ∼ ∑ aₛ t^{αₛ}` as `t → 0⁺` (2.5.17), `ℜαₛ` strictly increasing and `ℜαₛ → ∞`. Then
`𝓜f₁` continues analytically from `ℜz > -ℜα₀` to a meromorphic function `F` on `ℂ` whose
singularities are simple poles at `-αₛ` with principal parts `aₛ/(z + αₛ)`: for every `N`,
`F(z) - ∑_{s<N} aₛ/(z + αₛ)` is analytic in `ℜz > -ℜα_N`. -/
@[dlmf 2.5.E17, dlmf 2.5.E25, dlmf 2.5.ii]
theorem mellin_truncLow_continuation {f : ℝ → ℂ} {a : ℕ → ℂ} {α : ℕ → ℂ}
    (hfc : LocallyIntegrableOn f (Ioi 0)) (hα : StrictMono fun s => (α s).re)
    (hαinf : Tendsto (fun s => (α s).re) atTop atTop)
    (hf : HasAsymptoticExpansion (𝓝[>] 0) (fun s (t : ℝ) => (t : ℂ) ^ α s) a f) :
    ∃ F : ℂ → ℂ, (∀ z : ℂ, -(α 0).re < z.re → F z = mellin (mellinTruncLow f) z) ∧
      ∀ N : ℕ, DifferentiableOn ℂ (fun z => F z - ∑ s ∈ range N, a s / (z + α s))
        {z : ℂ | -(α N).re < z.re} := by
  sorry

/-- DLMF 2.5.26 (and 2.5.28 for `h`): where `𝓜f₁(z)` and `𝓜f₂(z)` both converge,
`𝓜f(z) = 𝓜f₁(z) + 𝓜f₂(z)`; DLMF uses the right side to extend `𝓜f` to `ℜz < b`. -/
@[dlmf 2.5.E26, dlmf 2.5.E28, dlmf 2.5.E22, dlmf 2.5.E24]
theorem mellin_eq_truncLow_add_truncHigh {f : ℝ → ℂ} {z : ℂ}
    (h1 : MellinConvergent (mellinTruncLow f) z) (h2 : MellinConvergent (mellinTruncHigh f) z) :
    mellin f z = mellin (mellinTruncLow f) z + mellin (mellinTruncHigh f) z := by
  unfold mellin
  rw [← integral_add h1 h2]
  congr 1
  funext t
  simp only [mellinTruncHigh, Pi.sub_apply, smul_eq_mul]
  ring

/-- DLMF 2.5.27 and §2.5(ii), case `κ = 0`: let `h` be locally integrable on `(0, ∞)` with
`h(t) ∼ ∑ bₛ t^{-βₛ}` as `t → ∞` (2.5.18 with `κ = 0`), `ℜβₛ` strictly increasing and
`ℜβₛ → ∞`. Then `𝓜h₂` continues analytically from `ℜz < ℜβ₀` to a meromorphic function `H` on
`ℂ` with simple poles at `βₛ` and principal parts `-bₛ/(z - βₛ)`: for every `N`,
`H(z) + ∑_{s<N} bₛ/(z - βₛ)` is analytic in `ℜz < ℜβ_N`. -/
@[dlmf 2.5.E18, dlmf 2.5.E27, dlmf 2.5.ii]
theorem mellin_truncHigh_continuation {h : ℝ → ℂ} {b : ℕ → ℂ} {β : ℕ → ℂ}
    (hhc : LocallyIntegrableOn h (Ioi 0)) (hβ : StrictMono fun s => (β s).re)
    (hβinf : Tendsto (fun s => (β s).re) atTop atTop)
    (hh : HasAsymptoticExpansion atTop (fun s (t : ℝ) => (t : ℂ) ^ (-β s)) b h) :
    ∃ H : ℂ → ℂ, (∀ z : ℂ, z.re < (β 0).re → H z = mellin (mellinTruncHigh h) z) ∧
      ∀ N : ℕ, DifferentiableOn ℂ (fun z => H z + ∑ s ∈ range N, b s / (z - β s))
        {z : ℂ | z.re < (β N).re} := by
  sorry

/-- DLMF §2.5(ii), case `κ ≠ 0`: if `h(t) ∼ exp(iκt^p) ∑ bₛ t^{-βₛ}` as `t → ∞` (2.5.18) with
real `κ ≠ 0`, `p > 0`, and `ℜβₛ → ∞`, then `𝓜h₂` continues analytically from `ℜz < ℜβ₀` to an
entire function. -/
@[dlmf 2.5.E18, dlmf 2.5.ii]
theorem mellin_truncHigh_continuation_osc {h : ℝ → ℂ} {b : ℕ → ℂ} {β : ℕ → ℂ} {κ p : ℝ}
    (hκ : κ ≠ 0) (hp : 0 < p) (hhc : LocallyIntegrableOn h (Ioi 0))
    (hβinf : Tendsto (fun s => (β s).re) atTop atTop)
    (hh : HasAsymptoticExpansion atTop
      (fun s (t : ℝ) => Complex.exp (I * κ * ((t ^ p : ℝ) : ℂ)) * (t : ℂ) ^ (-β s)) b h) :
    ∃ H : ℂ → ℂ, (∀ z : ℂ, z.re < (β 0).re → H z = mellin (mellinTruncHigh h) z) ∧
      Differentiable ℂ H := by
  sorry

/-- DLMF 2.5.29–2.5.30: `I(x) = ∑_{j,k=1}^{2} I_{jk}(x)` with
`I_{jk}(x) = ∫₀^∞ f_j(t) h_k(xt) dt`, provided the four integrals converge. -/
@[dlmf 2.5.E29, dlmf 2.5.E30]
theorem convolution_eq_sum_trunc {f h : ℝ → ℂ} {x : ℝ}
    (h11 : IntegrableOn (fun t => mellinTruncLow f t * mellinTruncLow h (x * t)) (Ioi 0))
    (h12 : IntegrableOn (fun t => mellinTruncLow f t * mellinTruncHigh h (x * t)) (Ioi 0))
    (h21 : IntegrableOn (fun t => mellinTruncHigh f t * mellinTruncLow h (x * t)) (Ioi 0))
    (h22 : IntegrableOn (fun t => mellinTruncHigh f t * mellinTruncHigh h (x * t)) (Ioi 0)) :
    (∫ t in Ioi 0, f t * h (x * t)) =
      ((∫ t in Ioi 0, mellinTruncLow f t * mellinTruncLow h (x * t)) +
        ∫ t in Ioi 0, mellinTruncLow f t * mellinTruncHigh h (x * t)) +
      ((∫ t in Ioi 0, mellinTruncHigh f t * mellinTruncLow h (x * t)) +
        ∫ t in Ioi 0, mellinTruncHigh f t * mellinTruncHigh h (x * t)) := by
  rw [← integral_add h11 h12, ← integral_add h21 h22, ← integral_add]
  · congr 1
    funext t
    simp only [mellinTruncHigh, Pi.sub_apply]
    ring
  · exact h11.add h12
  · exact h21.add h22

/-- DLMF 2.5.31: `I₂₁(x) = ∫₀^∞ f₂(t) h₁(xt) dt = 0` for `x ≥ 1` (the integrand vanishes). -/
@[dlmf 2.5.E31]
theorem integral_truncHigh_mul_truncLow (f h : ℝ → ℂ) {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in Ioi 0, mellinTruncHigh f t * mellinTruncLow h (x * t)) = 0 := by
  refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
  by_cases ht1 : t ≤ 1
  · simp [mellinTruncHigh, mellinTruncLow, ht1]
  · have : ¬ x * t ≤ 1 := not_le.2 (by
      have : 1 < t := not_le.1 ht1
      nlinarith)
    simp [mellinTruncLow, this]

end DLMF.AsymptoticApproximations
