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
public import DLMFMathlib.Analysis.Complex.VerticalLineShift

/-!
# Mellin transform methods (DLMF §2.5(i)–(ii))

The Mellin transform 2.5.1 is Mathlib's `mellin`, the inversion integral 2.5.2 along
`ℜz = c` is `mellinInv c` (`(2πi)⁻¹ ∫_{c-i∞}^{c+i∞} x^{-z} F(z) dz = mellinInv c F x`), and the
inversion theorem is `mellinInv_mellin_eq` (see `Basics.MathlibCoverage`). Residues are
`DLMF.AlgebraicAnalytic.residueAt` (§1.10(iii)), the circle integral `(2πi)⁻¹ ∮ F` around a small
circle.

## Main results

* `mellin_convolution`, `mellin_convolution_eq_mellinInv`: the Mellin convolution
  `I(x) = ∫₀^∞ f(t) h(xt) dt` and the Parseval formula (DLMF 2.5.3–2.5.5).
* `mellinInv_shift`, `mellinInv_isLittleO`: shifting the line of integration past finitely
  many poles, and `E(x) = o(x^{-q})` by the Riemann–Lebesgue lemma (DLMF 2.5.6–2.5.7,
  2.5.34–2.5.36).
* `mellinConvergent_truncLow`, `mellinConvergent_truncHigh`, `mellinConvergent_trunc_h`,
  `mellinConvergent_pairs`: the domains of convergence of Tables 2.5.1–2.5.2.
* `mellin_truncLow_continuation`, `mellin_eq_truncLow_add_truncHigh`,
  `mellin_truncHigh_continuation`, `mellin_truncHigh_continuation_osc`: the continuations
  2.5.25–2.5.28.
* `convolution_eq_sum_trunc`, `integral_truncHigh_mul_truncLow`: the splitting 2.5.29–2.5.31.

## Implementation notes

Mellin convergence `MellinConvergent f z` is absolute convergence of `∫₀^∞ t^{z-1} f(t) dt`.
In the convolution theorems the transforms are required to converge absolutely on the line of
integration; then the double integral converges absolutely (Tonelli). The convolution theorem
uses the logarithmic-coordinate convolution API in `DLMFMathlib.Analysis.MellinConvolution`.
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

/-- Near an isolated singularity the Laurent coefficient `a_{-1}` on small circles is the
residue. -/
private lemma eventually_laurentCoeff_eq_residueAt {f : ℂ → ℂ} {p : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : ∀ z : ℂ, z ≠ p → ‖z - p‖ < ε → DifferentiableAt ℂ f z) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), DLMF.AlgebraicAnalytic.laurentCoeff f p r (-1) =
      DLMF.AlgebraicAnalytic.residueAt f p := by
  have hconst : ∀ r ∈ Ioo 0 ε, DLMF.AlgebraicAnalytic.laurentCoeff f p r (-1) =
      DLMF.AlgebraicAnalytic.laurentCoeff f p (ε / 2) (-1) := by
    have key : ∀ r₁ r₂ : ℝ, 0 < r₁ → r₁ ≤ r₂ → r₂ < ε →
        DLMF.AlgebraicAnalytic.laurentCoeff f p r₂ (-1) =
          DLMF.AlgebraicAnalytic.laurentCoeff f p r₁ (-1) := by
      intro r₁ r₂ h0 h12 h2
      unfold DLMF.AlgebraicAnalytic.laurentCoeff
      congr 1
      refine circleIntegral_eq_of_differentiable_on_annulus_off_countable h0 h12
        countable_empty (fun z hz => ?_) (fun z hz => ?_)
      · have h1 : ‖z - p‖ ≤ r₂ := by simpa [dist_eq_norm] using hz.1
        have h2' : r₁ ≤ ‖z - p‖ := by simpa [dist_eq_norm] using hz.2
        refine ((hf z (fun h => ?_) (by linarith)).continuousAt.mul
          (continuousAt_const)).continuousWithinAt
        rw [h, sub_self, norm_zero] at h2'; linarith
      · have h1 : ‖z - p‖ < r₂ := by simpa [dist_eq_norm] using hz.1.1
        have h2' : r₁ < ‖z - p‖ := by simpa [dist_eq_norm] using hz.1.2
        refine (hf z (fun h => ?_) (by linarith)).mul (differentiableAt_const _)
        rw [h, sub_self, norm_zero] at h2'; linarith
    intro r hr
    rcases le_total r (ε / 2) with h | h
    · exact (key r (ε / 2) hr.1 h (by linarith)).symm
    · exact key (ε / 2) r (by linarith) h hr.2
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), DLMF.AlgebraicAnalytic.laurentCoeff f p r (-1) =
      DLMF.AlgebraicAnalytic.laurentCoeff f p (ε / 2) (-1) := by
    filter_upwards [Ioo_mem_nhdsGT hε] with r hr using hconst r hr
  have hres : DLMF.AlgebraicAnalytic.residueAt f p =
      DLMF.AlgebraicAnalytic.laurentCoeff f p (ε / 2) (-1) :=
    Tendsto.limUnder_eq (tendsto_nhds_of_eventually_eq hev)
  rw [hres]
  exact hev

/-- A function holomorphic on a closed strip minus a finite set `P` of interior points is
holomorphic in a punctured disc around each point of `P`. -/
theorem exists_punctured_differentiableAt {F : ℂ → ℂ} {c d : ℝ} {P : Finset ℂ}
    (hP : ∀ p ∈ P, d < p.re ∧ p.re < c)
    (hF : DifferentiableOn ℂ F (re ⁻¹' Icc d c \ (P : Set ℂ))) {q : ℂ} (hq : q ∈ P) :
    ∃ ε > 0, ∀ z : ℂ, z ≠ q → ‖z - q‖ < ε → DifferentiableAt ℂ F z := by
  classical
  have hU : IsOpen (re ⁻¹' Ioo d c ∩ ((P.erase q : Finset ℂ) : Set ℂ)ᶜ) :=
    ((isOpen_Ioo).preimage continuous_re).inter
      (P.erase q).finite_toSet.isClosed.isOpen_compl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU q ⟨hP q hq, by simp⟩
  refine ⟨ε, hε, fun z hzq hz => ?_⟩
  have hzU := hball (by rwa [Metric.mem_ball, dist_eq_norm])
  have hzP : z ∉ P := fun hzP => hzU.2 (by simp [hzq, hzP])
  refine hF.differentiableAt (Filter.mem_of_superset ((((isOpen_Ioo (a := d) (b := c)).preimage
    continuous_re).inter P.finite_toSet.isClosed.isOpen_compl).mem_nhds ⟨hzU.1, hzP⟩) ?_)
  rintro v ⟨hv, hvP⟩
  exact ⟨Ioo_subset_Icc_self hv, hvP⟩

/-- At an isolated singularity, `Res_{z=p}[-f(z)] = -Res_{z=p} f(z)`. -/
theorem residueAt_neg_of_differentiableAt {f : ℂ → ℂ} {p : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : ∀ z : ℂ, z ≠ p → ‖z - p‖ < ε → DifferentiableAt ℂ f z) :
    DLMF.AlgebraicAnalytic.residueAt (fun z => -f z) p =
      -DLMF.AlgebraicAnalytic.residueAt f p := by
  have hev := eventually_laurentCoeff_eq_residueAt hε hf
  have hneg : ∀ r : ℝ, DLMF.AlgebraicAnalytic.laurentCoeff (fun z => -f z) p r (-1) =
      -DLMF.AlgebraicAnalytic.laurentCoeff f p r (-1) := fun r => by
    unfold DLMF.AlgebraicAnalytic.laurentCoeff circleIntegral
    simp only [neg_mul, smul_neg, intervalIntegral.integral_neg, mul_neg]
  unfold DLMF.AlgebraicAnalytic.residueAt
  simp only [hneg]
  refine Tendsto.limUnder_eq (tendsto_nhds_of_eventually_eq ?_)
  filter_upwards [hev] with r hr
  rw [hr, DLMF.AlgebraicAnalytic.residueAt]

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
  classical
  set f : ℂ → ℂ := fun z => (x : ℂ) ^ (-z) * G z with hfdef
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hpow : ∀ z : ℂ, DifferentiableAt ℂ (fun z : ℂ => (x : ℂ) ^ (-z)) z := fun z =>
    differentiableAt_id.neg.const_cpow (Or.inl hx0)
  have hnormpow : ∀ z : ℂ, ‖(x : ℂ) ^ (-z)‖ = x ^ (-z.re) := fun z => by
    rw [norm_cpow_eq_rpow_re_of_pos hx, neg_re]
  have hf : DifferentiableOn ℂ f (re ⁻¹' Icc d c \ P) := fun z hz =>
    ((hpow z).differentiableWithinAt).mul (hG z hz)
  have hline : ∀ σ : ℝ, VerticalIntegrable G σ → Integrable fun y : ℝ => f (σ + y * I) := by
    intro σ hσ
    refine (hσ.norm.const_mul (x ^ (-σ))).mono' ?_ (Eventually.of_forall fun y => ?_)
    · have hcp : Continuous fun y : ℝ => (x : ℂ) ^ (-((σ : ℂ) + y * I)) :=
        continuous_iff_continuousAt.2 fun y => (hpow _).continuousAt.comp
          (f := fun y : ℝ => (σ : ℂ) + y * I) (by fun_prop)
      exact hcp.aestronglyMeasurable.mul hσ.aestronglyMeasurable
    · rw [norm_mul, hnormpow]; simp
  -- horizontal cross-sections
  set X : ℝ := max (x ^ (-d)) (x ^ (-c)) with hX
  have hXσ : ∀ σ ∈ Icc d c, x ^ (-σ) ≤ X := by
    intro σ hσ
    rcases le_total 1 x with h1 | h1
    · exact (Real.rpow_le_rpow_of_exponent_le h1 (by linarith [hσ.1])).trans (le_max_left _ _)
    · exact (Real.rpow_le_rpow_of_exponent_ge hx h1 (by linarith [hσ.2])).trans
        (le_max_right _ _)
  have hhor : ∀ l : Filter ℝ, l ≤ cocompact ℝ →
      Tendsto (fun T : ℝ => ∫ σ in d..c, f (σ + T * I)) l (𝓝 0) := by
    intro l hl
    have hlim : Tendsto (fun T : ℝ => X * (⨆ σ : Icc d c, ‖G (σ + T * I)‖) * |c - d|) l
        (𝓝 0) := by
      simpa using ((hdecay.mono_left hl).const_mul X).mul_const |c - d|
    refine squeeze_zero_norm' ?_ hlim
    have hev : ∀ᶠ T : ℝ in l, ∀ p ∈ P, T ≠ p.im :=
      hl ((Filter.eventually_all_finset P).mpr fun p _ =>
        (isCompact_singleton : IsCompact ({p.im} : Set ℝ)).compl_mem_cocompact)
    filter_upwards [hev] with T hT
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ => ?_
    rw [uIoc_of_le hdc.le] at hσ
    have hσ' : σ ∈ Icc d c := Ioc_subset_Icc_self hσ
    have hseg : ∀ τ ∈ Icc d c, ((τ : ℂ) + T * I) ∈ re ⁻¹' Icc d c \ (P : Set ℂ) := by
      intro τ hτ
      refine ⟨by simpa using hτ, fun hP' => hT _ hP' ?_⟩
      simp
    have hcont : ContinuousOn (fun τ : ℝ => ‖G (τ + T * I)‖) (Icc d c) :=
      (hG.continuousOn.comp (Continuous.continuousOn (by fun_prop)) hseg).norm
    have hbdd : BddAbove (Set.range fun τ : Icc d c => ‖G (τ + T * I)‖) := by
      have := (isCompact_Icc.image_of_continuousOn hcont).bddAbove
      rwa [Set.image_eq_range] at this
    have hle : ‖G (σ + T * I)‖ ≤ ⨆ τ : Icc d c, ‖G (τ + T * I)‖ :=
      le_ciSup (f := fun τ : Icc d c => ‖G (τ + T * I)‖) hbdd ⟨σ, hσ'⟩
    simp only [hfdef]
    have hre : ((σ : ℂ) + T * I).re = σ := by simp
    rw [norm_mul, hnormpow, hre]
    exact mul_le_mul (hXσ σ hσ') hle (norm_nonneg _) ((Real.rpow_nonneg hx.le _).trans
      (hXσ σ hσ'))
  obtain ⟨ρ, hρ, hmain⟩ := Complex.integral_vertical_sub_eq_sum_circleIntegral hdc P hP hf
    (hline d hd) (hline c hc) (hhor atTop atTop_le_cocompact) (hhor atBot atBot_le_cocompact)
  -- residues as Laurent coefficients on a common small circle
  have hres : ∀ p ∈ P, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      DLMF.AlgebraicAnalytic.laurentCoeff f p r (-1) =
        DLMF.AlgebraicAnalytic.residueAt f p := by
    intro p hp
    obtain ⟨ε, hε, hball⟩ := exists_punctured_differentiableAt hP hf hp
    exact eventually_laurentCoeff_eq_residueAt hε hball
  obtain ⟨r, hr, hr0⟩ := (((Filter.eventually_all_finset P).mpr hres).and
    (Ioo_mem_nhdsGT hρ)).exists
  have hsum := hmain r hr0.1 hr0.2
  have hres' : ∑ p ∈ P, DLMF.AlgebraicAnalytic.residueAt f p =
      (2 * π * I)⁻¹ * ∑ p ∈ P, ∮ z in C(p, r), f z := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← hr p hp, DLMF.AlgebraicAnalytic.laurentCoeff]
    simp
  change mellinInv c G x = ∑ p ∈ P, DLMF.AlgebraicAnalytic.residueAt f p + mellinInv d G x
  rw [hres', ← hsum]
  unfold mellinInv
  simp only [smul_eq_mul]
  change (1 / (2 * π) : ℝ) • (∫ y : ℝ, f (c + y * I)) = _ +
    (1 / (2 * π) : ℝ) • ∫ y : ℝ, f (d + y * I)
  rw [real_smul, real_smul]
  generalize (∫ y : ℝ, f (c + y * I)) = A
  generalize (∫ y : ℝ, f (d + y * I)) = B
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  ring

/-- Helper for `mellinInv_isLittleO`: the integrand of `mellinInv q G x` as a Fourier
integrand. -/
private lemma mellinInv_integrand_eq_fourier {q x : ℝ} (hx : 0 < x) (G : ℂ → ℂ) (y : ℝ) :
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
    simp only [mellinInv, u, mellinInv_integrand_eq_fourier hx, Circle.smul_def, smul_eq_mul]
    rw [integral_const_mul]
    simp only [Complex.real_smul]
    push_cast
    ring
  refine IsLittleO.congr' ?_ heq.symm EventuallyEq.rfl
  simpa using (isBigO_refl (fun x : ℝ => ((x ^ (-q) : ℝ) : ℂ)) atTop).mul_isLittleO
    ((isLittleO_one_iff ℂ).2 hu)

/-! ## §2.5(ii) Truncated functions and domains of convergence -/

/-- Helper: the restriction of a locally integrable function by an indicator. -/
private lemma locallyIntegrableOn_indicator_of_measurableSet {f : ℝ → ℂ} {s t : Set ℝ}
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
    exact locallyIntegrableOn_indicator_of_measurableSet hfc measurableSet_Iic
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
    exact locallyIntegrableOn_indicator_of_measurableSet hfc measurableSet_Ioi
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

/-- The truncated remainder `(f - ∑_{s<N} aₛ t^{αₛ})₁` of the expansion 2.5.17. -/
private noncomputable def truncLowRemainder (f : ℝ → ℂ) (a α : ℕ → ℂ) (N : ℕ) : ℝ → ℂ :=
  mellinTruncLow fun t => f t - ∑ s ∈ range N, (t : ℂ) ^ α s • a s

/-- Peeling off one term of the remainder 2.5.17. -/
private lemma truncLowRemainder_succ (f : ℝ → ℂ) (a α : ℕ → ℂ) (N : ℕ) :
    truncLowRemainder f a α N = truncLowRemainder f a α (N + 1) +
      mellinTruncLow (fun t => (t : ℂ) ^ α N • a N) := by
  funext t
  simp only [truncLowRemainder, mellinTruncLow, Pi.add_apply, sum_range_succ]
  by_cases ht : t ∈ Iic (1 : ℝ)
  · simp only [indicator_of_mem ht]; ring
  · simp [indicator_of_notMem ht]

/-- `𝓜[(t^α a)₁](z) = a/(z + α)` for `ℜ(z + α) > 0`. -/
private lemma hasMellin_truncLow_cpow_smul (α c : ℂ) {z : ℂ} (hz : 0 < z.re + α.re) :
    HasMellin (mellinTruncLow fun t => (t : ℂ) ^ α • c) z (c / (z + α)) := by
  have h := hasMellin_cpow_Ioc α hz
  have heq : EqOn (mellinTruncLow fun t => (t : ℂ) ^ α • c)
      (fun t => (indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ α) t) * c) (Ioi 0) := by
    intro t ht
    by_cases h1 : t ≤ 1
    · simp [mellinTruncLow, indicator_of_mem (show t ∈ Iic (1 : ℝ) from h1),
        indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht, h1⟩)]
    · simp [mellinTruncLow, indicator_of_notMem (show t ∉ Iic (1 : ℝ) from h1),
        indicator_of_notMem (show t ∉ Ioc (0 : ℝ) 1 from fun h' => h1 h'.2)]
  have hc : MellinConvergent (fun t => (indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ α) t) * c)
      z := by
    have := h.1.const_smul c
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [smul_eq_mul]; ring
  refine ⟨hc.congr_fun (fun t ht => by simp only [heq ht]) measurableSet_Ioi, ?_⟩
  unfold mellin
  rw [setIntegral_congr_fun measurableSet_Ioi fun t ht => by rw [heq ht]]
  simp only [smul_eq_mul]
  have h2 := h.2
  unfold mellin at h2
  simp only [smul_eq_mul] at h2
  calc ∫ t in Ioi (0 : ℝ),
        (t : ℂ) ^ (z - 1) * (indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ α) t * c)
      = (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (z - 1) * indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ α) t)
        * c := by
        rw [← integral_mul_const]; congr 1; funext t; ring
    _ = c / (z + α) := by rw [h2]; ring

/-- Mellin convergence and holomorphy of the remainder in `ℜz > -ℜα_N`. -/
private lemma truncLowRemainder_mellin {f : ℝ → ℂ} {a α : ℕ → ℂ}
    (hfc : LocallyIntegrableOn f (Ioi 0))
    (hf : HasAsymptoticExpansion (𝓝[>] 0) (fun s (t : ℝ) => (t : ℂ) ^ α s) a f) (N : ℕ)
    {z : ℂ} (hz : -(α N).re < z.re) :
    MellinConvergent (truncLowRemainder f a α N) z ∧
      DifferentiableAt ℂ (mellin (truncLowRemainder f a α N)) z := by
  have hloc : LocallyIntegrableOn (fun t => f t - ∑ s ∈ range N, (t : ℂ) ^ α s • a s)
      (Ioi 0) := by
    refine hfc.sub ?_
    refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ioi
    refine continuousOn_finsetSum _ fun s _ => ?_
    intro t ht
    have h1 : ContinuousAt (fun t : ℝ => (t : ℂ) ^ α s) t :=
      (continuousAt_cpow_const (ofReal_mem_slitPlane.2 ht)).comp continuous_ofReal.continuousAt
    exact (h1.smul (continuousAt_const (y := a s))).continuousWithinAt
  have hc : LocallyIntegrableOn (truncLowRemainder f a α N) (Ioi 0) :=
    locallyIntegrableOn_indicator_of_measurableSet hloc measurableSet_Iic
  have htop : truncLowRemainder f a α N =O[atTop] (· ^ (-(z.re + 1))) := by
    refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop 1] with t ht
    rw [truncLowRemainder, mellinTruncLow,
      indicator_of_notMem (show t ∉ Set.Iic 1 from not_le.2 ht)]
  have hbot : truncLowRemainder f a α N =O[𝓝[>] 0] (· ^ (-(-(α N).re))) := by
    simp only [neg_neg]
    have h1 := hf N
    have h2 : (fun t : ℝ => (t : ℂ) ^ α N) =O[𝓝[>] 0] fun t : ℝ => t ^ (α N).re := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [norm_cpow_eq_rpow_re_of_pos ht, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _),
        one_mul]
    refine IsBigO.trans ?_ (h1.trans h2)
    refine (isBigO_refl _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    rw [truncLowRemainder, mellinTruncLow, indicator_of_mem (show t ∈ Set.Iic 1 from ht.2.le)]
  exact ⟨mellinConvergent_of_isBigO_rpow hc htop (by linarith) hbot hz,
    mellin_differentiableAt_of_isBigO_rpow hc htop (by linarith) hbot hz⟩


/-- Additivity of the Mellin transform where both transforms converge. -/
private lemma mellin_add_of_mellinConvergent {f g : ℝ → ℂ} {z : ℂ} (hf : MellinConvergent f z)
    (hg : MellinConvergent g z) : mellin (f + g) z = mellin f z + mellin g z := by
  unfold mellin
  rw [← integral_add hf hg]
  congr 1; funext t
  simp only [Pi.add_apply, smul_add]

/-- Comparing the remainders after `K ≤ M` terms. -/
private lemma mellin_truncLowRemainder_eq {f : ℝ → ℂ} {a α : ℕ → ℂ}
    (hfc : LocallyIntegrableOn f (Ioi 0)) (hα : StrictMono fun s => (α s).re)
    (hf : HasAsymptoticExpansion (𝓝[>] 0) (fun s (t : ℝ) => (t : ℂ) ^ α s) a f) {K M : ℕ}
    (hKM : K ≤ M) {z : ℂ} (hz : -(α K).re < z.re) :
    mellin (truncLowRemainder f a α K) z =
      mellin (truncLowRemainder f a α M) z + ∑ s ∈ Ico K M, a s / (z + α s) := by
  induction M, hKM using Nat.le_induction with
  | base => simp
  | succ M hKM ih =>
    have hM : -(α M).re < z.re := lt_of_le_of_lt (neg_le_neg (hα.monotone hKM)) hz
    have hM1 : -(α (M + 1)).re < z.re :=
      lt_trans (neg_lt_neg (hα (Nat.lt_succ_self M))) hM
    have h1 := (truncLowRemainder_mellin hfc hf (M + 1) hM1).1
    have h2 := hasMellin_truncLow_cpow_smul (α M) (a M) (z := z) (by linarith)
    rw [ih, truncLowRemainder_succ f a α M, mellin_add_of_mellinConvergent h1 h2.1, h2.2,
      sum_Ico_succ_top hKM]
    ring

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
  classical
  have hex : ∀ z : ℂ, ∃ N, -(α N).re < z.re := fun z => by
    obtain ⟨N, hN⟩ := (hαinf.eventually_gt_atTop (-z.re)).exists
    exact ⟨N, by linarith⟩
  set F : ℂ → ℂ := fun z => mellin (truncLowRemainder f a α (Nat.find (hex z))) z +
    ∑ s ∈ range (Nat.find (hex z)), a s / (z + α s) with hF
  have key : ∀ z : ℂ, ∀ N, -(α N).re < z.re →
      F z = mellin (truncLowRemainder f a α N) z + ∑ s ∈ range N, a s / (z + α s) := by
    intro z N hN
    have hK := Nat.find_min' (hex z) hN
    rw [hF]; dsimp only
    rw [mellin_truncLowRemainder_eq hfc hα hf hK (Nat.find_spec (hex z)), add_assoc,
      add_comm (∑ s ∈ Ico _ N, _), sum_range_add_sum_Ico _ hK]
  refine ⟨F, fun z hz => ?_, fun N => ?_⟩
  · rw [key z 0 hz]
    simp [truncLowRemainder]
  · have hopen : IsOpen {z : ℂ | -(α N).re < z.re} := isOpen_lt continuous_const continuous_re
    intro z hz
    refine ((truncLowRemainder_mellin hfc hf N hz).2.congr_of_eventuallyEq ?_)
      |>.differentiableWithinAt
    filter_upwards [hopen.mem_nhds hz] with w hw
    rw [key w N hw]; ring

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

/-- The truncated remainder `(h - ∑_{s<N} bₛ t^{-βₛ})₂` of the expansion 2.5.18 (`κ = 0`). -/
private noncomputable def truncHighRemainder (h : ℝ → ℂ) (b β : ℕ → ℂ) (N : ℕ) : ℝ → ℂ :=
  mellinTruncHigh fun t => h t - ∑ s ∈ range N, (t : ℂ) ^ (-β s) • b s

/-- `f₂` is the restriction of `f` to `(1, ∞)`. -/
private lemma mellinTruncHigh_eq_indicator (g : ℝ → ℂ) :
    mellinTruncHigh g = (Ioi (1 : ℝ)).indicator g := by
  funext t
  by_cases ht : t ≤ 1
  · simp [mellinTruncHigh, mellinTruncLow, ht]
  · simp [mellinTruncHigh, mellinTruncLow, ht, not_le.1 ht]

/-- Peeling off one term of the remainder 2.5.18. -/
private lemma truncHighRemainder_succ (h : ℝ → ℂ) (b β : ℕ → ℂ) (N : ℕ) :
    truncHighRemainder h b β N = truncHighRemainder h b β (N + 1) +
      mellinTruncHigh (fun t => (t : ℂ) ^ (-β N) • b N) := by
  simp only [truncHighRemainder, mellinTruncHigh_eq_indicator]
  funext t
  simp only [Pi.add_apply, sum_range_succ]
  by_cases ht : t ∈ Ioi (1 : ℝ)
  · simp only [indicator_of_mem ht]; ring
  · simp [indicator_of_notMem ht]

/-- `𝓜[(t^{-β} c)₂](z) = -c/(z - β)` for `ℜz < ℜβ`. -/
private lemma hasMellin_truncHigh_cpow_smul (β c : ℂ) {z : ℂ} (hz : z.re < β.re) :
    HasMellin (mellinTruncHigh fun t => (t : ℂ) ^ (-β) • c) z (-(c / (z - β))) := by
  have ha : (z - 1 - β).re < -1 := by simp; linarith
  have hpt : ∀ t ∈ Ioi (0 : ℝ), (t : ℂ) ^ (z - 1) • (Ioi (1 : ℝ)).indicator
      (fun t => (t : ℂ) ^ (-β) • c) t = (Ioi (1 : ℝ)).indicator
      (fun t => (t : ℂ) ^ (z - 1 - β) * c) t := by
    intro t ht
    by_cases h1 : t ∈ Ioi (1 : ℝ)
    · have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 (ne_of_gt ht)
      simp only [indicator_of_mem h1, smul_eq_mul]
      rw [show z - 1 - β = (z - 1) + -β by ring, cpow_add _ _ ht0]; ring
    · simp [indicator_of_notMem h1]
  have hint : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 1 - β) * c) (Ioi 1) :=
    (integrableOn_Ioi_cpow_of_lt ha one_pos).mul_const c
  rw [mellinTruncHigh_eq_indicator]
  refine ⟨?_, ?_⟩
  · refine IntegrableOn.congr_fun ?_ (fun t ht => (hpt t ht).symm) measurableSet_Ioi
    exact (hint.integrable_indicator measurableSet_Ioi).integrableOn
  · unfold mellin
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_indicator measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi,
      show Set.Ioi (1 : ℝ) ∩ Set.Ioi 0 = Set.Ioi 1 from
        inter_eq_left.2 (Ioi_subset_Ioi zero_le_one),
      integral_mul_const, integral_Ioi_cpow_of_lt ha one_pos]
    have hzb : z - β ≠ 0 := fun h0 => by
      have := congrArg re h0; simp at this; linarith
    rw [show z - 1 - β + 1 = z - β by ring, ofReal_one, one_cpow]
    field_simp


/-- Mellin convergence and holomorphy of the remainder in `ℜz < ℜβ_N`. -/
private lemma truncHighRemainder_mellin {h : ℝ → ℂ} {b β : ℕ → ℂ}
    (hhc : LocallyIntegrableOn h (Ioi 0))
    (hh : HasAsymptoticExpansion atTop (fun s (t : ℝ) => (t : ℂ) ^ (-β s)) b h) (N : ℕ)
    {z : ℂ} (hz : z.re < (β N).re) :
    MellinConvergent (truncHighRemainder h b β N) z ∧
      DifferentiableAt ℂ (mellin (truncHighRemainder h b β N)) z := by
  have hloc : LocallyIntegrableOn (fun t => h t - ∑ s ∈ range N, (t : ℂ) ^ (-β s) • b s)
      (Ioi 0) := by
    refine hhc.sub ?_
    refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ioi
    refine continuousOn_finsetSum _ fun s _ => ?_
    intro t ht
    have h1 : ContinuousAt (fun t : ℝ => (t : ℂ) ^ (-β s)) t :=
      (continuousAt_cpow_const (ofReal_mem_slitPlane.2 ht)).comp continuous_ofReal.continuousAt
    exact (h1.smul (continuousAt_const (y := b s))).continuousWithinAt
  have hc : LocallyIntegrableOn (truncHighRemainder h b β N) (Ioi 0) := by
    rw [truncHighRemainder, mellinTruncHigh_eq_indicator]
    exact locallyIntegrableOn_indicator_of_measurableSet hloc measurableSet_Ioi
  have hbot : truncHighRemainder h b β N =O[𝓝[>] 0] (· ^ (-(z.re - 1))) := by
    refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    rw [truncHighRemainder, mellinTruncHigh_eq_indicator,
      indicator_of_notMem (show t ∉ Set.Ioi 1 from not_lt.2 ht.2.le)]
  have htop : truncHighRemainder h b β N =O[atTop] (· ^ (-(β N).re)) := by
    have h2 : (fun t : ℝ => (t : ℂ) ^ (-β N)) =O[atTop] fun t : ℝ => t ^ (-(β N).re) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      rw [norm_cpow_eq_rpow_re_of_pos ht, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _),
        one_mul, neg_re]
    refine IsBigO.trans ?_ ((hh N).trans h2)
    refine (isBigO_refl _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop 1] with t ht
    rw [truncHighRemainder, mellinTruncHigh_eq_indicator,
      indicator_of_mem (show t ∈ Set.Ioi 1 from ht)]
  exact ⟨mellinConvergent_of_isBigO_rpow hc htop hz hbot (by linarith),
    mellin_differentiableAt_of_isBigO_rpow hc htop hz hbot (by linarith)⟩

/-- Comparing the remainders after `K ≤ M` terms of 2.5.18. -/
private lemma mellin_truncHighRemainder_eq {h : ℝ → ℂ} {b β : ℕ → ℂ}
    (hhc : LocallyIntegrableOn h (Ioi 0)) (hβ : StrictMono fun s => (β s).re)
    (hh : HasAsymptoticExpansion atTop (fun s (t : ℝ) => (t : ℂ) ^ (-β s)) b h) {K M : ℕ}
    (hKM : K ≤ M) {z : ℂ} (hz : z.re < (β K).re) :
    mellin (truncHighRemainder h b β K) z =
      mellin (truncHighRemainder h b β M) z - ∑ s ∈ Ico K M, b s / (z - β s) := by
  induction M, hKM using Nat.le_induction with
  | base => simp
  | succ M hKM ih =>
    have hM : z.re < (β M).re := lt_of_lt_of_le hz (hβ.monotone hKM)
    have hM1 : z.re < (β (M + 1)).re := lt_trans hM (hβ (Nat.lt_succ_self M))
    have h1 := (truncHighRemainder_mellin hhc hh (M + 1) hM1).1
    have h2 := hasMellin_truncHigh_cpow_smul (β M) (b M) hM
    rw [ih, truncHighRemainder_succ h b β M, mellin_add_of_mellinConvergent h1 h2.1, h2.2,
      sum_Ico_succ_top hKM]
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
  classical
  have hex : ∀ z : ℂ, ∃ N, z.re < (β N).re := fun z =>
    (hβinf.eventually_gt_atTop z.re).exists
  set H : ℂ → ℂ := fun z => mellin (truncHighRemainder h b β (Nat.find (hex z))) z -
    ∑ s ∈ range (Nat.find (hex z)), b s / (z - β s) with hH
  have key : ∀ z : ℂ, ∀ N, z.re < (β N).re →
      H z = mellin (truncHighRemainder h b β N) z - ∑ s ∈ range N, b s / (z - β s) := by
    intro z N hN
    have hK := Nat.find_min' (hex z) hN
    rw [hH]; dsimp only
    rw [mellin_truncHighRemainder_eq hhc hβ hh hK (Nat.find_spec (hex z)), sub_sub,
      add_comm (∑ s ∈ Ico _ N, _), sum_range_add_sum_Ico _ hK]
  refine ⟨H, fun z hz => ?_, fun N => ?_⟩
  · rw [key z 0 hz]
    simp [truncHighRemainder]
  · have hopen : IsOpen {z : ℂ | z.re < (β N).re} := isOpen_lt continuous_re continuous_const
    intro z hz
    refine ((truncHighRemainder_mellin hhc hh N hz).2.congr_of_eventuallyEq ?_)
      |>.differentiableWithinAt
    filter_upwards [hopen.mem_nhds hz] with w hw
    rw [key w N hw]; ring

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
