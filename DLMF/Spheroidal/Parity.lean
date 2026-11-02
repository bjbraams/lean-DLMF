/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Spheroidal.Spectrum

/-!
# Parity and simplicity of the spheroidal eigenvalues (DLMF §30.3(i), §30.4(i))

Continuing `DLMF.Spheroidal.Spectrum`, let `p(λ) = Y(0)` and `q(λ) = Y'(0)` for the Frobenius
solution `Y` at `z = 1` of the factor equation. This file proves that the eigenfunctions
alternate in parity and that the normalized eigenfunction is unique; together these give
`existsUnique_isSpheroidalPsFactor` in `DLMF.Spheroidal.Existence`.

## Main definitions

* `frobeniusValueAtZero`, `frobeniusDerivAtZero`: `Y(0)` and `Y'(0)` as entire functions of `λ`.

## Main results

* `frobeniusRealDeriv_zero_eq_zero_iff_even`: the element of the spectrum with `k` smaller
  elements has an even eigenfunction iff `k` is even.
* `exists_real_factorSolution_unit_data`: an entire solution at an eigenvalue is a multiple of
  a real solution with data `(1, 0)` or `(0, 1)` at `0`.
* `factorSolution_unique`: two real normalized solutions with the same sign agree.

## Implementation notes

Green's identity in `λ`, `p(λ₁) q(λ₂) - p(λ₂) q(λ₁) = (λ₂ - λ₁) ∫₀¹ (1-x²)^m y₁ y₂ dx`, shows that
the Wronskian `p q' - q p'` in `λ` is positive. Hence the zeros of `p` and `q` interlace
(`ODE.sturmCount_existsUnique_zero_between`), and the lowest element of the spectrum is a zero
of `q`.
-/

@[expose] public noncomputable section

open Complex Set Filter FormalMultilinearSeries MeasureTheory ComplexConjugate
open scoped Topology ENNReal ContDiff

namespace DLMF.Spheroidal

/-- The value `Y(0)` as an entire function of `λ`. -/
def frobeniusValueAtZero (m : ℕ) (γr : ℝ) (w : ℂ) : ℂ :=
    frobeniusSeries m (γr : ℂ) (w - (m : ℂ) * ((m : ℂ) + 1)) (-1)

/-- The derivative `Y'(0)` as an entire function of `λ`. -/
def frobeniusDerivAtZero (m : ℕ) (γr : ℝ) (w : ℂ) : ℂ :=
    frobeniusSeriesDeriv m (γr : ℂ) (w - (m : ℂ) * ((m : ℂ) + 1)) (-1)

/-- `λ ↦ Y(0)` is entire. -/
private lemma differentiable_frobeniusValueAtZero (m : ℕ) (γr : ℝ) : Differentiable ℂ
    (frobeniusValueAtZero m γr) :=
  (differentiable_frobeniusSeries_and_deriv_param m (γr : ℂ) (u := -1) (by simp)).1.comp
      (differentiable_id.sub_const _)

/-- `λ ↦ Y'(0)` is entire. -/
private lemma differentiable_frobeniusDerivAtZero (m : ℕ) (γr : ℝ) : Differentiable ℂ
    (frobeniusDerivAtZero m γr) :=
  (differentiable_frobeniusSeries_and_deriv_param m (γr : ℂ) (u := -1) (by simp)).2.comp
      (differentiable_id.sub_const _)

/-- `y(0)` for real `λ` is the real part of `frobeniusValueAtZero`. -/
private lemma frobeniusReal_zero_eq_re (m : ℕ) (γr lam : ℝ) :
    p3lyR m γr lam 0 = (frobeniusValueAtZero m γr lam).re := by
  simp only [p3lyR, frobeniusSolution, frobeniusValueAtZero, shiftedEigenvalue]; push_cast; ring_nf

/-- `y'(0)` for real `λ` is the real part of `frobeniusDerivAtZero`. -/
lemma p3lyR'_zero_eq (m : ℕ) (γr lam : ℝ) :
    p3lyR' m γr lam 0 = (frobeniusDerivAtZero m γr lam).re := by
  simp only [p3lyR']
  rw [deriv_frobeniusSolution _ _ _ (by norm_num)]
  simp only [frobeniusDerivAtZero, shiftedEigenvalue]; push_cast; ring_nf

/-- `λ ↦ Y(0)` is differentiable. -/
private lemma hasDerivAt_frobeniusReal_zero_param (m : ℕ) (γr lam : ℝ) :
    HasDerivAt (fun t => p3lyR m γr t 0) (deriv (frobeniusValueAtZero m γr) lam).re lam := by
  have h := ((differentiable_frobeniusValueAtZero m γr) lam).hasDerivAt.real_of_complex
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun t => frobeniusReal_zero_eq_re m γr t)

/-- `λ ↦ Y'(0)` is differentiable. -/
private lemma hasDerivAt_frobeniusRealDeriv_zero_param (m : ℕ) (γr lam : ℝ) :
    HasDerivAt (fun t => p3lyR' m γr t 0) (deriv (frobeniusDerivAtZero m γr) lam).re lam := by
  have h := ((differentiable_frobeniusDerivAtZero m γr) lam).hasDerivAt.real_of_complex
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun t => p3lyR'_zero_eq m γr t)

/-- Points of `[0, 1]` lie within `5/3` of `1`. -/
private lemma abs_sub_one_lt_five_thirds_of_mem_Icc {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : |x -
    1| < 5 / 3 := by
  rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]

/-- **Green's identity in the parameter**:
`Y₁(0) Y₂'(0) - Y₂(0) Y₁'(0) = (λ₂ - λ₁) ∫₀¹ (1-x²)^m y₁ y₂ dx`. -/
private lemma frobeniusReal_green_identity (m : ℕ) (γr l₁ l₂ : ℝ) :
    p3lyR m γr l₁ 0 * p3lyR' m γr l₂ 0 - p3lyR m γr l₂ 0 * p3lyR' m γr l₁ 0 =
      (l₂ - l₁) * ∫ x in (0 : ℝ)..1, (1 - x ^ 2) ^ m * p3lyR m γr l₁ x * p3lyR m γr l₂ x := by
  set y₁ := p3lyR m γr l₁
  set y₂ := p3lyR m γr l₂
  set W : ℝ → ℝ := fun x => y₁ x * ((1 - x ^ 2) ^ (m + 1) * p3lyR' m γr l₂ x) -
    y₂ x * ((1 - x ^ 2) ^ (m + 1) * p3lyR' m γr l₁ x)
  have hW : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt W ((l₁ - l₂) * ((1 - x ^ 2) ^ m * y₁ x * y₂ x)) x := by
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    have h := ((hasDerivAt_frobeniusReal m γr l₁ (abs_sub_one_lt_five_thirds_of_mem_Icc hx)).mul
      (hasDerivAt_frobeniusReal_flux m γr l₂ (abs_sub_one_lt_five_thirds_of_mem_Icc hx))).sub
      ((hasDerivAt_frobeniusReal m γr l₂ (abs_sub_one_lt_five_thirds_of_mem_Icc hx)).mul
      (hasDerivAt_frobeniusReal_flux m γr l₁ (abs_sub_one_lt_five_thirds_of_mem_Icc hx)))
    exact h.congr_deriv (by simp only [y₁, y₂]; ring)
  have hc : ContinuousOn (fun x => (l₁ - l₂) * ((1 - x ^ 2) ^ m * y₁ x * y₂ x)) (uIcc 0 1) := by
    have c1 : ContinuousOn y₁ (uIcc 0 1) := fun x hx => by
      rw [uIcc_of_le zero_le_one] at hx
      exact (hasDerivAt_frobeniusReal m γr l₁
          (abs_sub_one_lt_five_thirds_of_mem_Icc hx)).continuousAt.continuousWithinAt
    have c2 : ContinuousOn y₂ (uIcc 0 1) := fun x hx => by
      rw [uIcc_of_le zero_le_one] at hx
      exact (hasDerivAt_frobeniusReal m γr l₂
          (abs_sub_one_lt_five_thirds_of_mem_Icc hx)).continuousAt.continuousWithinAt
    exact continuousOn_const.mul (((by fun_prop : Continuous fun x : ℝ =>
      (1 - x ^ 2) ^ m).continuousOn.mul c1).mul c2)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hW hc.intervalIntegrable
  rw [intervalIntegral.integral_const_mul] at hftc
  simp only [W] at hftc
  norm_num at hftc
  linear_combination hftc

/-- Clamping to `[0, 1]`. -/
def unitIntervalClamp (x : ℝ) : ℝ := max 0 (min x 1)

/-- The clamp is continuous. -/
private lemma continuous_unitIntervalClamp : Continuous unitIntervalClamp :=
  continuous_const.max (continuous_id.min continuous_const)

/-- The clamp takes values in `(-1/2, 3/2)`. -/
private lemma unitIntervalClamp_mem_Ioo (x : ℝ) : unitIntervalClamp x ∈
    Ioo (-1 / 2 : ℝ) (3 / 2) := by
  simp only [unitIntervalClamp, mem_Ioo]
  constructor
  · exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  · exact lt_of_le_of_lt (max_le (by norm_num) (min_le_right _ _)) (by norm_num)

/-- The clamp is the identity on `[0, 1]`. -/
private lemma unitIntervalClamp_eq_self {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    unitIntervalClamp x = x := by
  simp [unitIntervalClamp, hx.1, hx.2]

/-- The Green integral is continuous in the second parameter. -/
private lemma continuous_frobeniusReal_greenIntegral (m : ℕ) (γr l₁ : ℝ) :
    Continuous fun l₂ =>
      ∫ x in (0 : ℝ)..1, (1 - x ^ 2) ^ m * p3lyR m γr l₁ x * p3lyR m γr l₂ x := by
  have hY : Continuous fun p : ℝ × ℝ => p3lyR m γr p.1 (unitIntervalClamp p.2) :=
    (continuousOn_frobeniusReal_and_deriv m γr).1.comp_continuous
      (continuous_fst.prodMk (continuous_unitIntervalClamp.comp continuous_snd))
      (fun p => ⟨mem_univ _, unitIntervalClamp_mem_Ioo _⟩)
  set F : ℝ → ℝ → ℝ := fun l x => (1 - unitIntervalClamp x ^ 2) ^ m *
      p3lyR m γr l₁ (unitIntervalClamp x) *
    p3lyR m γr l (unitIntervalClamp x)
  have hF : Continuous (Function.uncurry F) := by
    have h1 : Continuous fun p : ℝ × ℝ => p3lyR m γr l₁ (unitIntervalClamp p.2) :=
      hY.comp (continuous_const.prodMk continuous_snd)
    exact ((continuous_const.sub ((continuous_unitIntervalClamp.comp continuous_snd).pow 2)).pow m
      |>.mul h1).mul hY
  refine (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
    hF 0 1).congr fun l => ?_
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le zero_le_one] at hx
  simp only [F, unitIntervalClamp_eq_self hx]

/-- Positivity of the integral of a continuous nonnegative function that is nonzero at an
interior point. -/
private lemma intervalIntegral_pos_of_nonneg_of_ne_zero {f : ℝ → ℝ} {a b x₀ : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (h0 : ∀ x ∈ Icc a b, 0 ≤ f x) (hx₀ : x₀ ∈ Ioo a b) (hne : f x₀ ≠ 0) :
    0 < ∫ x in a..b, f x := by
  have hfi : IntervalIntegrable f volume a b :=
    (hf.mono (by rw [uIcc_of_le hab.le])).intervalIntegrable
  have hae : 0 ≤ᵐ[volume.restrict (uIoc a b)] f := by
    rw [uIoc_of_le hab.le, EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun x hx => h0 x (Ioc_subset_Icc_self hx)
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae' hae hfi]
  refine ⟨hab, ?_⟩
  set U := Ioo a b ∩ f ⁻¹' {0}ᶜ
  have hU : IsOpen U := (hf.mono Ioo_subset_Icc_self).isOpen_inter_preimage isOpen_Ioo
    isOpen_compl_singleton
  have hsub : U ⊆ Function.support f ∩ Ioc a b := fun x hx =>
    ⟨hx.2, Ioo_subset_Ioc_self hx.1⟩
  exact (hU.measure_pos volume ⟨x₀, hx₀, hne⟩).trans_le (measure_mono hsub)

/-- The diagonal Green integral is positive. -/
private lemma frobeniusReal_greenIntegral_self_pos (m : ℕ) (γr lam : ℝ) :
    0 < ∫ x in (0 : ℝ)..1, (1 - x ^ 2) ^ m * p3lyR m γr lam x * p3lyR m γr lam x := by
  have hy1 : ContinuousAt (p3lyR m γr lam) 1 :=
    (hasDerivAt_frobeniusReal m γr lam (by norm_num)).continuousAt
  have hev : ∀ᶠ x in 𝓝[<] (1 : ℝ), p3lyR m γr lam x ≠ 0 ∧ x ∈ Ioo (0 : ℝ) 1 :=
    ((hy1.eventually_ne (by rw [frobeniusReal_one]; norm_num)).filter_mono nhdsWithin_le_nhds).and
      (Ioo_mem_nhdsLT (by norm_num))
  obtain ⟨x₀, hx₀, hx₀'⟩ := hev.exists
  have hc : ContinuousOn (p3lyR m γr lam) (Icc 0 1) := fun x hx =>
    (hasDerivAt_frobeniusReal m γr lam
        (abs_sub_one_lt_five_thirds_of_mem_Icc hx)).continuousAt.continuousWithinAt
  refine intervalIntegral_pos_of_nonneg_of_ne_zero zero_lt_one
    (((by fun_prop : Continuous fun x : ℝ => (1 - x ^ 2) ^ m).continuousOn.mul hc).mul hc)
    (fun x hx => ?_) hx₀' ?_
  · have : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    rw [mul_assoc]; exact mul_nonneg (pow_nonneg this m) (mul_self_nonneg _)
  · have : 0 < 1 - x₀ ^ 2 := by nlinarith [hx₀'.1, hx₀'.2]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ this.ne') hx₀) hx₀

/-- **The Wronskian in `λ` is positive**: `Y(0) ∂_λY'(0) - Y'(0) ∂_λY(0) > 0`. -/
private lemma frobeniusReal_paramWronskian_pos (m : ℕ) (γr lam : ℝ) :
    0 < p3lyR m γr lam 0 * (deriv (frobeniusDerivAtZero m γr) lam).re -
      p3lyR' m γr lam 0 * (deriv (frobeniusValueAtZero m γr) lam).re := by
  set Φ := fun l₂ =>
    ∫ x in (0 : ℝ)..1, (1 - x ^ 2) ^ m * p3lyR m γr lam x * p3lyR m γr l₂ x
  set f : ℝ → ℝ := fun μ => p3lyR m γr lam 0 * p3lyR' m γr μ 0 -
    p3lyR m γr μ 0 * p3lyR' m γr lam 0
  have hfe : ∀ μ, f μ = (μ - lam) * Φ μ := fun μ => frobeniusReal_green_identity m γr lam μ
  have hf : HasDerivAt f (p3lyR m γr lam 0 * (deriv (frobeniusDerivAtZero m γr) lam).re -
      (deriv (frobeniusValueAtZero m γr) lam).re * p3lyR' m γr lam 0) lam :=
    ((hasDerivAt_frobeniusRealDeriv_zero_param m γr lam).const_mul _).sub
        ((hasDerivAt_frobeniusReal_zero_param m γr lam).mul_const _)
  have hg : HasDerivAt f (Φ lam) lam := by
    rw [hasDerivAt_iff_tendsto_slope]
    have : Tendsto Φ (𝓝[≠] lam) (𝓝 (Φ lam)) :=
      (continuous_frobeniusReal_greenIntegral m γr lam).continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with μ hμ
    rw [slope_def_field, hfe, hfe, sub_self, zero_mul, sub_zero]
    field_simp [sub_ne_zero.2 hμ]
  have e := hf.unique hg
  have hpos := frobeniusReal_greenIntegral_self_pos m γr lam
  linarith

/-- For `λ - m(m+1) < -|γ²|`, `Y(0) Y'(0) < 0`. -/
private lemma frobeniusReal_mul_deriv_zero_neg (m : ℕ) (γr lam : ℝ)
    (hc : lam - (m : ℝ) * (m + 1) < -|γr|) :
    p3lyR m γr lam 0 * p3lyR' m γr lam 0 < 0 := by
  refine lt_of_le_of_ne ?_ (frobeniusReal_mul_deriv_zero_ne_zero m γr lam hc)
  set y := p3lyR m γr lam
  set y' := p3lyR' m γr lam
  set q : ℝ → ℝ := fun t => (lam - (m : ℝ) * (m + 1) + γr * (1 - t ^ 2)) * (1 - t ^ 2) ^ m
  set ψ : ℝ → ℝ := fun t => y t * ((1 - t ^ 2) ^ (m + 1) * y' t)
  have hψ : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt ψ ((1 - t ^ 2) ^ (m + 1) * y' t ^ 2 - q t * y t ^ 2) t := by
    intro t ht
    have := (hasDerivAt_frobeniusReal m γr lam (abs_sub_one_lt_five_thirds_of_mem_Icc ht)).mul
      (hasDerivAt_frobeniusReal_flux m γr lam (abs_sub_one_lt_five_thirds_of_mem_Icc ht))
    exact this.congr_deriv (by simp only [q, y, y']; ring)
  have hq : ∀ t ∈ Icc (0 : ℝ) 1, q t ≤ 0 := by
    intro t ht
    have h1 : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    have h2 : 1 - t ^ 2 ≤ 1 := by nlinarith
    have h3 : lam - (m : ℝ) * (m + 1) + γr * (1 - t ^ 2) < 0 := by
      have : γr * (1 - t ^ 2) ≤ |γr| := by
        calc γr * (1 - t ^ 2) ≤ |γr| * (1 - t ^ 2) := by gcongr; exact le_abs_self γr
          _ ≤ |γr| * 1 := by gcongr
          _ = |γr| := mul_one _
      linarith
    exact mul_nonpos_of_nonpos_of_nonneg h3.le (pow_nonneg h1 m)
  have hmono : MonotoneOn ψ (Icc 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
      (fun t ht => (hψ t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hψ t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => ?_)
    rw [(hψ t (interior_subset ht)).deriv]
    have ht' := interior_subset ht
    have h1 : 0 ≤ 1 - t ^ 2 := by nlinarith [ht'.1, ht'.2]
    have := hq t ht'
    have : 0 ≤ (1 - t ^ 2) ^ (m + 1) * y' t ^ 2 := by positivity
    nlinarith [sq_nonneg (y t)]
  have := hmono ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  simpa [ψ] using this

/-- Membership in the spectrum: `λ ∈ spec ↔ Y(0) Y'(0) = 0`. -/
private lemma mem_factorSpectrum_iff (m : ℕ) (γr lam : ℝ) :
    lam ∈ factorSpectrum m γr ↔ p3lyR m γr lam 0 * p3lyR' m γr lam 0 = 0 := by
  constructor
  · rintro ⟨g, hg, hs, hne⟩
    have h := frobeniusSolution_mul_deriv_zero_eq_zero hg hs hne
    rwa [frobeniusSolution_mul_deriv_zero_eq_ofReal, Complex.ofReal_eq_zero] at h
  · intro h
    refine exists_entire_factorSolution ?_
    rw [frobeniusSolution_mul_deriv_zero_eq_ofReal, h, Complex.ofReal_zero]

/-- **The lowest eigenvalue is even**: at the smallest element of the spectrum, `Y'(0) = 0`. -/
private lemma frobeniusRealDeriv_zero_eq_zero_of_lowest (m : ℕ) (γr lam : ℝ)
    (hS : lam ∈ factorSpectrum m γr)
    (hmin : factorSpectrum m γr ∩ Iio lam = ∅) : p3lyR' m γr lam 0 = 0 := by
  set f : ℝ → ℝ := fun l => p3lyR m γr l 0 * p3lyR' m γr l 0
  have hfd : ∀ l : ℝ, HasDerivAt f ((deriv (frobeniusValueAtZero m γr) l).re * p3lyR' m γr l 0 +
      p3lyR m γr l 0 * (deriv (frobeniusDerivAtZero m γr) l).re) l := fun l =>
    (hasDerivAt_frobeniusReal_zero_param m γr l).mul
        (hasDerivAt_frobeniusRealDeriv_zero_param m γr l)
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun l => (hfd l).continuousAt
  have hnz : ∀ l < lam, f l ≠ 0 := fun l hl h0 =>
    (Set.eq_empty_iff_forall_notMem.1 hmin) l ⟨(mem_factorSpectrum_iff m γr l).2 h0, hl⟩
  by_contra hq
  have hp : p3lyR m γr lam 0 = 0 :=
    (mul_eq_zero.1 ((mem_factorSpectrum_iff m γr lam).1 hS)).resolve_right hq
  set L := min lam ((m : ℝ) * (m + 1) - |γr|) - 1
  have hL : L < lam := by simp only [L]; linarith [min_le_left lam ((m : ℝ) * (m + 1) - |γr|)]
  have hfL : f L < 0 := frobeniusReal_mul_deriv_zero_neg m γr L (by
    simp only [L]; linarith [min_le_right lam ((m : ℝ) * (m + 1) - |γr|)])
  have hneg : ∀ x ∈ Ioo L lam, 0 ≤ -f x := by
    intro x hx
    by_contra h
    push Not at h
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hx.1.le hfc.continuousOn
      ⟨hfL.le, (by linarith : (0 : ℝ) ≤ f x)⟩
    exact hnz c (lt_of_le_of_lt hc.2 hx.2) hc0
  have hd := ODE.nonpos_of_hasDerivAt_of_eq_zero_right hL (hfd lam).neg (by simp [f, hp]) hneg
  have hw := frobeniusReal_paramWronskian_pos m γr lam
  rw [hp] at hd hw
  linarith

/-- **Alternation**: consecutive elements of the spectrum have opposite parity. -/
private lemma frobeniusRealDeriv_zero_alternate (m : ℕ) (γr : ℝ) {μ lam : ℝ}
    (hμ : μ ∈ factorSpectrum m γr)
    (hl : lam ∈ factorSpectrum m γr) (hlt : μ < lam)
        (hgap : ∀ x ∈ Ioo μ lam, x ∉ factorSpectrum m γr) :
    ¬ (p3lyR' m γr μ 0 = 0 ↔ p3lyR' m γr lam 0 = 0) := by
  have hw : ∀ x ∈ Icc μ lam, 0 < p3lyR m γr x 0 * (deriv (frobeniusDerivAtZero m γr) x).re -
      p3lyR' m γr x 0 * (deriv (frobeniusValueAtZero m γr) x).re := fun x _ =>
          frobeniusReal_paramWronskian_pos m γr x
  intro hiff
  by_cases hq : p3lyR' m γr μ 0 = 0
  · have hq' := hiff.1 hq
    obtain ⟨e, he, he0⟩ := (ODE.sturmCount_existsUnique_zero_between
      (p := fun l => p3lyR' m γr l 0) (q := fun l => -p3lyR m γr l 0) hlt
      (fun x _ => hasDerivAt_frobeniusRealDeriv_zero_param m γr x)
          (fun x _ => (hasDerivAt_frobeniusReal_zero_param m γr x).neg)
      (fun x hx => by have := hw x hx; linarith) hq hq'
      (fun x hx h0 => hgap x hx ((mem_factorSpectrum_iff m γr x).2 (by rw [h0, mul_zero])))).exists
    exact hgap e he ((mem_factorSpectrum_iff m γr e).2 (by rw [neg_eq_zero.1 he0, zero_mul]))
  · have hq' : p3lyR' m γr lam 0 ≠ 0 := fun h => hq (hiff.2 h)
    have hp := (mul_eq_zero.1 ((mem_factorSpectrum_iff m γr μ).1 hμ)).resolve_right hq
    have hp' := (mul_eq_zero.1 ((mem_factorSpectrum_iff m γr lam).1 hl)).resolve_right hq'
    obtain ⟨e, he, he0⟩ := (ODE.sturmCount_existsUnique_zero_between
      (p := fun l => p3lyR m γr l 0) (q := fun l => p3lyR' m γr l 0) hlt
      (fun x _ => hasDerivAt_frobeniusReal_zero_param m γr x)
          (fun x _ => hasDerivAt_frobeniusRealDeriv_zero_param m γr x) hw hp hp'
      (fun x hx h0 => hgap x hx ((mem_factorSpectrum_iff m γr x).2 (by rw [h0, zero_mul])))).exists
    exact hgap e he ((mem_factorSpectrum_iff m γr e).2 (by rw [he0, mul_zero]))

/-- **Parity of the eigenfunctions**: the element of the spectrum with exactly `k` smaller
elements has `Y'(0) = 0` (even eigenfunction) iff `k` is even. -/
theorem frobeniusRealDeriv_zero_eq_zero_iff_even (m : ℕ) (γr : ℝ) : ∀ k : ℕ, ∀ lam ∈
    factorSpectrum m γr,
    (factorSpectrum m γr ∩ Iio lam).encard = k → (p3lyR' m γr lam 0 = 0 ↔ Even k) := by
  intro k
  induction k with
  | zero =>
    intro lam hl hk
    simp only [Nat.cast_zero, Set.encard_eq_zero] at hk
    simp [frobeniusRealDeriv_zero_eq_zero_of_lowest m γr lam hl hk]
  | succ k ih =>
    intro lam hl hk
    set T := factorSpectrum m γr ∩ Iio lam
    have hTf : T.Finite := factorSpectrum_inter_Iio_finite m γr lam
    have hTne : T.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      rw [h, Set.encard_empty] at hk
      norm_cast at hk
    obtain ⟨μ, hμT, hμmax⟩ := Set.exists_max_image T id hTf hTne
    have hTeq : T = insert μ (factorSpectrum m γr ∩ Iio μ) := by
      ext x
      simp only [T, mem_inter_iff, mem_Iio, mem_insert_iff]
      constructor
      · rintro ⟨hx, hxl⟩
        rcases (show x ≤ μ from hμmax x ⟨hx, hxl⟩).lt_or_eq with h | h
        · exact Or.inr ⟨hx, h⟩
        · exact Or.inl h
      · rintro (rfl | ⟨hx, hxμ⟩)
        · exact hμT
        · exact ⟨hx, hxμ.trans hμT.2⟩
    have hk' : (factorSpectrum m γr ∩ Iio μ).encard = k := by
      rw [hTeq, Set.encard_insert_of_notMem
        (fun h : μ ∈ factorSpectrum m γr ∩ Iio μ => lt_irrefl μ h.2)] at hk
      push_cast at hk
      exact (ENat.add_left_injective_of_ne_top ENat.one_ne_top) hk
    have hgap : ∀ x ∈ Ioo μ lam, x ∉ factorSpectrum m γr := fun x hx hxS =>
      not_le.2 hx.1 (show x ≤ μ from hμmax x ⟨hxS, hx.2⟩)
    have halt := frobeniusRealDeriv_zero_alternate m γr hμT.1 hl hμT.2 hgap
    have := ih μ hμT.1 hk'
    rw [Nat.even_add_one]
    tauto

/-! ### Real normalized eigenfunctions -/

/-- Linear combinations of entire solutions are entire solutions. -/
theorem isFactorSolution_linear_combination {m : ℕ} {γ2 c : ℂ} {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hfs : IsFactorSolution m γ2 c univ f)
        (hgs : IsFactorSolution m γ2 c univ g)
    (a b : ℂ) :
    Differentiable ℂ (fun z => a * f z + b * g z) ∧
      IsFactorSolution m γ2 c univ (fun z => a * f z + b * g z) ∧
      deriv (fun z => a * f z + b * g z) = fun z => a * deriv f z + b * deriv g z := by
  have hf' : Differentiable ℂ (deriv f) := fun z => (hf.analyticAt z).deriv.differentiableAt
  have hg' : Differentiable ℂ (deriv g) := fun z => (hg.analyticAt z).deriv.differentiableAt
  have e1 : deriv (fun z => a * f z + b * g z) = fun z => a * deriv f z + b * deriv g z :=
    funext fun z => (((hf z).hasDerivAt.const_mul a).add ((hg z).hasDerivAt.const_mul b)).deriv
  have e2 : deriv (fun z => a * deriv f z + b * deriv g z) =
      fun z => a * deriv (deriv f) z + b * deriv (deriv g) z :=
    funext fun z => (((hf' z).hasDerivAt.const_mul a).add ((hg' z).hasDerivAt.const_mul b)).deriv
  refine ⟨(hf.const_mul a).add (hg.const_mul b), fun z _ => ?_, e1⟩
  rw [e1, e2]
  beta_reduce
  linear_combination a * hfs z trivial + b * hgs z trivial

/-- Reflection in the real axis preserves the factor equation with real parameters. -/
private lemma isFactorSolution_conj_comp_conj {m : ℕ} {γr cr : ℝ} {g : ℂ → ℂ}
    (hg : Differentiable ℂ g)
    (hs : IsFactorSolution m (γr : ℂ) (cr : ℂ) univ g) :
    Differentiable ℂ (conj ∘ g ∘ conj) ∧
        IsFactorSolution m (γr : ℂ) (cr : ℂ) univ (conj ∘ g ∘ conj) := by
  refine ⟨fun z => by simpa using (hg (conj z)).conj_conj, fun z _ => ?_⟩
  rw [deriv_conj_conj, deriv_conj_conj]
  have := congrArg conj (hs (conj z) trivial)
  simp only [map_add, map_sub, map_mul, map_pow, map_one, map_zero, conj_conj,
    Complex.conj_ofReal, map_natCast, map_ofNat, Function.comp_apply] at this ⊢
  linear_combination this

/-- An entire solution with real data at `0` is real on the real axis. -/
private lemma im_eq_zero_of_isFactorSolution_real_data {m : ℕ} {γr cr : ℝ} {g : ℂ → ℂ}
    (hg : Differentiable ℂ g)
    (hs : IsFactorSolution m (γr : ℂ) (cr : ℂ) univ g) (h0 : (g 0).im = 0)
        (h1 : (deriv g 0).im = 0) :
    ∀ x : ℝ, (g x).im = 0 := by
  obtain ⟨hcd, hcs⟩ := isFactorSolution_conj_comp_conj hg hs
  obtain ⟨hdd, hds, hde⟩ := isFactorSolution_linear_combination hg hcd hs hcs 1 (-1)
  have hz := isFactorSolution_eq_zero_of_data_zero hdd hds
    (by simp only [Function.comp_apply, map_zero]; rw [Complex.conj_eq_iff_im.2 h0]; ring)
    (by rw [hde, deriv_conj_conj]; simp only [Function.comp_apply, map_zero]
        rw [Complex.conj_eq_iff_im.2 h1]; ring)
  intro x
  have := congrFun hz (x : ℂ)
  simp only [Function.comp_apply, Complex.conj_ofReal, Pi.zero_apply] at this
  rw [← Complex.conj_eq_iff_im]
  linear_combination -this

/-- The derivative of an entire function real on the real axis is real there. -/
private lemma im_deriv_eq_zero_of_im_eq_zero {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hr : ∀ x : ℝ, (g x).im = 0)
    (x : ℝ) : (deriv g x).im = 0 := by
  have h := ((hg x).hasDerivAt.const_mul (-I)).real_of_complex
  have hev : (fun t : ℝ => (-I * g t).re) = fun _ => 0 := funext fun t => by simp [hr t]
  rw [hev] at h
  have := h.unique (hasDerivAt_const x (0 : ℝ))
  simpa using this

/-- The Wronskian with the Frobenius solution, in real form. -/
private lemma isFactorSolution_wronskian_frobeniusReal {m : ℕ} {γr lam : ℝ} {g : ℂ → ℂ}
    (hg : Differentiable ℂ g)
    (hs : IsFactorSolution m (γr : ℂ) (shiftedEigenvalue m lam) univ g) :
    g 0 * (p3lyR' m γr lam 0 : ℂ) = deriv g 0 * (p3lyR m γr lam 0 : ℂ) := by
  have h := isFactorSolution_wronskian_frobeniusSolution_zero hg hs
  have h1 := frobeniusSolution_ofReal m γr lam 0
  have h2 := deriv_frobeniusSolution_ofReal m γr lam (x := 0) (by norm_num)
  push_cast at h1 h2
  rwa [h1, h2] at h

/-- Entire solutions at an even eigenvalue (`Y'(0) = 0`) have `g'(0) = 0`; at an odd one,
`g(0) = 0`. -/
theorem isFactorSolution_data_of_parity {m : ℕ} {γr lam : ℝ} {g : ℂ → ℂ}
    (hl : lam ∈ factorSpectrum m γr)
    (hg : Differentiable ℂ g) (hs : IsFactorSolution m (γr : ℂ) (shiftedEigenvalue m lam) univ g) :
    (p3lyR' m γr lam 0 = 0 → deriv g 0 = 0) ∧ (p3lyR' m γr lam 0 ≠ 0 → g 0 = 0) := by
  have hW := isFactorSolution_wronskian_frobeniusReal hg hs
  constructor
  · intro hq
    have hp : p3lyR m γr lam 0 ≠ 0 := fun hp =>
        frobeniusRealDeriv_ne_zero_of_frobeniusReal_eq_zero m γr lam (by norm_num) hp hq
    rw [hq, Complex.ofReal_zero, mul_zero] at hW
    exact (mul_eq_zero.1 hW.symm).resolve_right (by exact_mod_cast hp)
  · intro hq
    have hp := (mul_eq_zero.1 ((mem_factorSpectrum_iff m γr lam).1 hl)).resolve_right hq
    rw [hp, Complex.ofReal_zero, mul_zero] at hW
    exact (mul_eq_zero.1 hW).resolve_right (by exact_mod_cast hq)

/-- **A real eigenfunction with unit data**: for `λ` in the spectrum there is an entire solution,
real on `ℝ`, with `(g(0), g'(0)) = (1, 0)` (even case) or `(0, 1)` (odd case). -/
theorem exists_real_factorSolution_unit_data {m : ℕ} {γr lam : ℝ} (hl : lam ∈ factorSpectrum m γr) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ IsFactorSolution m (γr : ℂ) (shiftedEigenvalue m lam) univ g ∧
      (∀ x : ℝ, (g x).im = 0) ∧ (p3lyR' m γr lam 0 = 0 → g 0 = 1 ∧ deriv g 0 = 0) ∧
      (p3lyR' m γr lam 0 ≠ 0 → g 0 = 0 ∧ deriv g 0 = 1) := by
  obtain ⟨h, hd, hs, hne⟩ := hl
  have hpar := isFactorSolution_data_of_parity ⟨h, hd, hs, hne⟩ hd hs
  have hC : shiftedEigenvalue m lam = ((lam - (m : ℝ) * (m + 1) : ℝ) : ℂ) := rfl
  by_cases hq : p3lyR' m γr lam 0 = 0
  · have h1 := hpar.1 hq
    have h0 : h 0 ≠ 0 := fun h0 => hne (isFactorSolution_eq_zero_of_data_zero hd hs h0 h1)
    obtain ⟨gd, gs, ge⟩ := isFactorSolution_linear_combination hd hd hs hs (h 0)⁻¹ 0
    have g0 : (fun z => (h 0)⁻¹ * h z + 0 * h z) 0 = 1 := by simp [h0]
    have g1 : deriv (fun z => (h 0)⁻¹ * h z + 0 * h z) 0 = 0 := by rw [ge]; simp [h1]
    refine ⟨_, gd, gs, ?_, fun _ => ⟨g0, g1⟩, fun h' => absurd hq h'⟩
    rw [hC] at gs
    exact im_eq_zero_of_isFactorSolution_real_data gd gs (by simp [h0]) (by rw [g1]; simp)
  · have h0 := hpar.2 hq
    have h1 : deriv h 0 ≠ 0 := fun h1 => hne (isFactorSolution_eq_zero_of_data_zero hd hs h0 h1)
    obtain ⟨gd, gs, ge⟩ := isFactorSolution_linear_combination hd hd hs hs (deriv h 0)⁻¹ 0
    have g0 : (fun z => (deriv h 0)⁻¹ * h z + 0 * h z) 0 = 0 := by simp [h0]
    have g1 : deriv (fun z => (deriv h 0)⁻¹ * h z + 0 * h z) 0 = 1 := by rw [ge]; simp [h1]
    refine ⟨_, gd, gs, ?_, fun h' => absurd h' hq, fun _ => ⟨g0, g1⟩⟩
    rw [hC] at gs
    exact im_eq_zero_of_isFactorSolution_real_data gd gs (by simp [h0]) (by rw [g1]; simp)

/-- The weighted `L²` norm of a nondegenerate entire function on `[-1, 1]` is positive. -/
theorem integral_weight_mul_re_sq_pos (m : ℕ) {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (h : (g 0).re ≠ 0 ∨ (deriv g 0).re ≠ 0) :
    0 < ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * (g x).re ^ 2 := by
  have hr : Continuous fun x : ℝ => (g x).re :=
    Complex.continuous_re.comp (hg.continuous.comp Complex.continuous_ofReal)
  obtain ⟨x₀, hx₀, hne⟩ : ∃ x₀ ∈ Ioo (-1 : ℝ) 1, (g x₀).re ≠ 0 := by
    rcases h with h | h
    · exact ⟨0, by norm_num, by simpa using h⟩
    · by_contra hc
      push Not at hc
      have hd : HasDerivAt (fun x : ℝ => (g x).re) (deriv g 0).re 0 := by
        have := (hg ((0 : ℝ) : ℂ)).hasDerivAt.real_of_complex
        simpa using this
      have hev : (fun x : ℝ => (g x).re) =ᶠ[𝓝 0] fun _ => 0 := by
        filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)]
          with x hx using hc x hx
      exact h (hd.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hev))
  refine intervalIntegral_pos_of_nonneg_of_ne_zero (by norm_num)
    ((by fun_prop : Continuous fun x : ℝ => (1 - x ^ 2) ^ m).mul (hr.pow 2)).continuousOn
    (fun x hx => ?_) hx₀ ?_
  · have : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    exact mul_nonneg (pow_nonneg this m) (sq_nonneg _)
  · have : 0 < 1 - x₀ ^ 2 := by nlinarith [hx₀.1, hx₀.2]
    exact mul_ne_zero (pow_ne_zero _ this.ne') (pow_ne_zero _ hne)

/-- **Uniqueness of the normalized eigenfunction**: two entire solutions, real on `ℝ`, with
vanishing Wronskian at `0`, equal weighted norms and the same sign of the leading datum agree. -/
theorem factorSolution_unique {m : ℕ} {γ2 c : ℂ} {g₁ g₂ : ℂ → ℂ} (hd₁ : Differentiable ℂ g₁)
    (hs₁ : IsFactorSolution m γ2 c univ g₁) (hd₂ : Differentiable ℂ g₂)
        (hs₂ : IsFactorSolution m γ2 c univ g₂)
    (hr₁ : ∀ x : ℝ, (g₁ x).im = 0) (hr₂ : ∀ x : ℝ, (g₂ x).im = 0)
    (hW : g₁ 0 * deriv g₂ 0 = g₂ 0 * deriv g₁ 0)
    (hint : ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * (g₁ x).re ^ 2 =
      ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * (g₂ x).re ^ 2)
    (hsg : 0 < (g₁ 0).re * (g₂ 0).re ∨ 0 < (deriv g₁ 0).re * (deriv g₂ 0).re) : g₁ = g₂ := by
  have hre : ∀ {w : ℂ}, w.im = 0 → (w.re : ℂ) = w := fun h => Complex.ext rfl
    (by simp [h])
  have e₁ : ((g₁ 0).re : ℂ) = g₁ 0 := hre (by simpa using hr₁ 0)
  have e₂ : ((g₂ 0).re : ℂ) = g₂ 0 := hre (by simpa using hr₂ 0)
  have f₁ : ((deriv g₁ 0).re : ℂ) = deriv g₁ 0 :=
      hre (by simpa using im_deriv_eq_zero_of_im_eq_zero hd₁ hr₁ 0)
  have f₂ : ((deriv g₂ 0).re : ℂ) = deriv g₂ 0 :=
      hre (by simpa using im_deriv_eq_zero_of_im_eq_zero hd₂ hr₂ 0)
  obtain ⟨a, b, hab, hprop⟩ : ∃ a b : ℝ, 0 < a * b ∧ ∀ z, (a : ℂ) * g₂ z = b * g₁ z := by
    rcases hsg with h | h
    · refine ⟨(g₁ 0).re, (g₂ 0).re, h, fun z => ?_⟩
      obtain ⟨dd, ds, de⟩ := isFactorSolution_linear_combination hd₂ hd₁ hs₂ hs₁ (g₁ 0) (-g₂ 0)
      have hz := isFactorSolution_eq_zero_of_data_zero dd ds (by ring)
          (by rw [de]; linear_combination hW)
      have := congrFun hz z
      simp only [Pi.zero_apply] at this
      rw [e₁, e₂]; linear_combination this
    · refine ⟨(deriv g₁ 0).re, (deriv g₂ 0).re, h, fun z => ?_⟩
      obtain ⟨dd, ds, de⟩ :=
          isFactorSolution_linear_combination hd₂ hd₁ hs₂ hs₁ (deriv g₁ 0) (-deriv g₂ 0)
      have hz := isFactorSolution_eq_zero_of_data_zero dd ds (by linear_combination -hW)
          (by rw [de]; ring)
      have := congrFun hz z
      simp only [Pi.zero_apply] at this
      rw [f₁, f₂]; linear_combination this
  have ha : a ≠ 0 := by rintro rfl; simp at hab
  have hpt : ∀ x : ℝ, (g₂ x).re = b / a * (g₁ x).re := by
    intro x
    have := congrArg Complex.re (hprop x)
    rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul] at this
    field_simp
    linarith
  have hnd : (g₁ 0).re ≠ 0 ∨ (deriv g₁ 0).re ≠ 0 := by
    rcases hsg with h | h
    · left; rintro h0; rw [h0, zero_mul] at h; exact lt_irrefl _ h
    · right; rintro h0; rw [h0, zero_mul] at h; exact lt_irrefl _ h
  have hpos := integral_weight_mul_re_sq_pos m hd₁ hnd
  have hint' : ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * (g₂ x).re ^ 2 =
      (b / a) ^ 2 * ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * (g₁ x).re ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hpt]; ring
  rw [hint'] at hint
  have hk2 : (b / a) ^ 2 = 1 := by
    have := hint
    field_simp at this ⊢
    nlinarith
  have hk0 : 0 < b / a := by
    have : b / a = a * b / a ^ 2 := by field_simp
    rw [this]; positivity
  have hk : b / a = 1 := by nlinarith
  have hba : b = a := by field_simp at hk; linarith
  funext z
  have := hprop z
  rw [hba] at this
  exact (mul_left_cancel₀ (by exact_mod_cast ha) this).symm

end DLMF.Spheroidal
