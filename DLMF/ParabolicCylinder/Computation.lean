/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.SpecialFunctions.ChebyshevSeries
public import DLMF.ParabolicCylinder.ElementaryProperties
public import DLMF.ParabolicCylinder.AsymptoticsZeros
public import DLMFMathlib.Analysis.SpecialFunctions.ChebyshevSeriesDecay

/-!
# Chebyshev-series expansions of parabolic cylinder functions (DLMF §12.20)

DLMF §12.20 asserts that `U(a,x)` and `V(a,x)` can be computed from Chebyshev expansions on
compact intervals and, for the recessive solution, on a compactified half-line. This file
proves the existence of such expansions; the coefficients and the degree are not supplied by
the source.

## Main results

* `pcfU_chebyshev_compact`, `pcfV_chebyshev_compact`: summable Chebyshev expansions of
  `U(a,x)` and `V(a,x)` on `[0, λ]`.
* `pcfU_chebyshev_infinite`: a summable Chebyshev expansion of `U(a,x)` in `1 - 2λ/x` on
  `[λ, ∞)`.

## Implementation notes

On the half-line, `θ ↦ U(a, 2λ/(1 - cos θ))` is twice differentiable on `(0, π]` and, by the
large-argument behaviour DLMF 12.9.1, its first two derivatives tend to `0` at `θ = 0`; two
integrations by parts then give Chebyshev coefficients of order `n⁻²`.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
open DLMF.Core

namespace DLMF.Confluent

/-- DLMF 12.20: Chebyshev expansion on a compact interval; coefficients and degree are not supplied
by the source. -/
theorem pcfU_chebyshev_compact (a : ℂ) {lam : ℝ} (hlam : 0 < lam) :
    ∃ c : ℕ → ℂ, Summable c ∧ ∀ x ∈ Icc (0:ℝ) lam,
        HasSum (fun k : ℕ => c k*(Polynomial.Chebyshev.T ℂ (k:ℤ)).eval (2*(x:ℂ)/lam-1))
        (pcfU a x) := by
  have hF : Differentiable ℂ (fun z : ℂ => pcfU a ((lam : ℂ) * (z + 1) / 2)) :=
    (pcfU_entire a).comp (by fun_prop)
  obtain ⟨c, hc, hs⟩ := Polynomial.Chebyshev.exists_summable_series_of_entire hF
  refine ⟨c, hc, fun x hx => ?_⟩
  have h0 : 0 ≤ 2 * x / lam := div_nonneg (by linarith [hx.1]) hlam.le
  have h2 : 2 * x / lam ≤ 2 := (div_le_iff₀ hlam).mpr (by linarith [hx.2])
  have hy : 2 * x / lam - 1 ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have h := hs (2 * x / lam - 1) hy
  have hlam0 : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam.ne'
  have he : (lam : ℂ) * (((2 * x / lam - 1 : ℝ) : ℂ) + 1) / 2 = (x : ℂ) := by
    push_cast
    field_simp
    ring
  rw [he] at h
  convert h using 1
  funext k
  push_cast
  rfl

/-- DLMF 12.20: Chebyshev expansion on a compact interval; coefficients and degree are not supplied
by the source. -/
theorem pcfV_chebyshev_compact (a : ℂ) {lam : ℝ} (hlam : 0 < lam) :
    ∃ c : ℕ → ℂ, Summable c ∧ ∀ x ∈ Icc (0:ℝ) lam,
        HasSum (fun k : ℕ => c k*(Polynomial.Chebyshev.T ℂ (k:ℤ)).eval (2*(x:ℂ)/lam-1))
        (pcfV a x) := by
  have hF : Differentiable ℂ (fun z : ℂ => pcfV a ((lam : ℂ) * (z + 1) / 2)) :=
    (pcfV_entire a).comp (by fun_prop)
  obtain ⟨c, hc, hs⟩ := Polynomial.Chebyshev.exists_summable_series_of_entire hF
  refine ⟨c, hc, fun x hx => ?_⟩
  have h0 : 0 ≤ 2 * x / lam := div_nonneg (by linarith [hx.1]) hlam.le
  have h2 : 2 * x / lam ≤ 2 := (div_le_iff₀ hlam).mpr (by linarith [hx.2])
  have hy : 2 * x / lam - 1 ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have h := hs (2 * x / lam - 1) hy
  have hlam0 : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam.ne'
  have he : (lam : ℂ) * (((2 * x / lam - 1 : ℝ) : ℂ) + 1) / 2 = (x : ℂ) := by
    push_cast
    field_simp
    ring
  rw [he] at h
  convert h using 1
  funext k
  push_cast
  rfl

/-- Real positive arguments tend to infinity in every closed sector. -/
private lemma tendsto_ofReal_sector {α : ℝ} (hα : 0 ≤ α) :
    Tendsto (fun x : ℝ => (x : ℂ)) atTop (sector α) := by
  refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr ?_⟩
  · simpa [Function.comp_def] using tendsto_abs_atTop_atTop
  · filter_upwards [eventually_gt_atTop 0] with x hx
    refine ⟨ofReal_ne_zero.mpr hx.ne', ?_⟩
    rw [arg_ofReal_of_nonneg hx.le, abs_zero]; exact hα

/-- `x^k U(b,x) → 0` as `x → +∞`, from DLMF 12.9.1. -/
private lemma pcfU_real_decay (b : ℂ) (k : ℕ) :
    Tendsto (fun x : ℝ => x ^ k * ‖pcfU b x‖) atTop (𝓝 0) := by
  have h := pcfU_sector_asymptotic b (δ := π / 4) (by positivity) 0
  simp only [Finset.range_zero, Finset.sum_empty, sub_zero, CharP.cast_eq_zero, mul_zero,
    neg_zero, zpow_zero] at h
  have h2 := h.comp_tendsto (tendsto_ofReal_sector (by nlinarith [Real.pi_pos]))
  obtain ⟨C, hC⟩ := h2.bound
  set s : ℝ := (k : ℝ) - (b.re + 1 / 2)
  have hlim : Tendsto (fun x : ℝ => C * (x ^ s * Real.exp (-(1 / 4) * x))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s (1 / 4) (by norm_num)).const_mul C
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop 0] with x hx; positivity
  filter_upwards [hC, eventually_ge_atTop 1] with x hx hx1
  have hx0 : (0 : ℝ) < x := by linarith
  simp only [Function.comp_apply, norm_mul, norm_one, mul_one, Complex.norm_exp] at hx
  rw [norm_cpow_eq_rpow_re_of_pos hx0] at hx
  have hre : ((x : ℂ) ^ 2 / 4).re = x ^ 2 / 4 := by
    rw [← ofReal_pow, ← ofReal_ofNat, ← ofReal_div, ofReal_re]
  rw [hre] at hx
  simp only [add_re, one_div, inv_re, re_ofNat, normSq_ofNat] at hx
  set r : ℝ := b.re + 2 / (2 * 2) with hr
  have hC0 : 0 ≤ C := le_trans (by positivity) hx
  have hs : x ^ k = x ^ s * x ^ r := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hx0]; congr 1; simp only [s, hr]; ring
  have hxr : x ^ r * ‖pcfU b x‖ ≤ C * Real.exp (-(x ^ 2 / 4)) := by
    have h1 := mul_le_mul_of_nonneg_left hx (Real.exp_pos (-(x ^ 2 / 4))).le
    rw [← mul_assoc, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul] at h1
    linarith
  have hexp : Real.exp (-(x ^ 2 / 4)) ≤ Real.exp (-(1 / 4) * x) :=
    Real.exp_le_exp.mpr (by nlinarith)
  calc x ^ k * ‖pcfU b x‖ = x ^ s * (x ^ r * ‖pcfU b x‖) := by rw [hs]; ring
    _ ≤ x ^ s * (C * Real.exp (-(x ^ 2 / 4))) := by gcongr
    _ ≤ x ^ s * (C * Real.exp (-(1 / 4) * x)) := by gcongr
    _ = C * (x ^ s * Real.exp (-(1 / 4) * x)) := by ring

/-- DLMF 12.8.2 solved for `U'(a,z)`. -/
private lemma pcfUDeriv_eq (a z : ℂ) :
    pcfUDeriv a z = -(z / 2 * pcfU a z) - (a + 1 / 2) * pcfU (a + 1) z := by
  have h := pcfU_recurrence_add a z
  rw [deriv_pcfU] at h
  linear_combination h

/-- `x^k U'(a,x) → 0` as `x → +∞`. -/
private lemma pcfUDeriv_real_decay (a : ℂ) (k : ℕ) :
    Tendsto (fun x : ℝ => x ^ k * ‖pcfUDeriv a x‖) atTop (𝓝 0) := by
  have h := ((pcfU_real_decay a (k + 1)).const_mul (1 / 2)).add
    ((pcfU_real_decay (a + 1) k).const_mul ‖a + 1 / 2‖)
  rw [mul_zero, mul_zero, add_zero] at h
  refine squeeze_zero' ?_ ?_ h
  · filter_upwards [eventually_ge_atTop 0] with x hx; positivity
  filter_upwards [eventually_ge_atTop 0] with x hx
  rw [pcfUDeriv_eq]
  calc x ^ k * ‖-((x : ℂ) / 2 * pcfU a x) - (a + 1 / 2) * pcfU (a + 1) x‖
      ≤ x ^ k * (x / 2 * ‖pcfU a x‖ + ‖a + 1 / 2‖ * ‖pcfU (a + 1) x‖) := by
        gcongr
        refine (norm_sub_le _ _).trans (le_of_eq ?_)
        rw [norm_neg, norm_mul, norm_mul, norm_div, Complex.norm_real, Complex.norm_two,
          Real.norm_of_nonneg hx]
    _ = 1 / 2 * (x ^ (k + 1) * ‖pcfU a x‖) + ‖a + 1 / 2‖ * (x ^ k * ‖pcfU (a + 1) x‖) := by
        ring


/-- DLMF 12.20: compactification of the half-line for the recessive solution. -/
theorem pcfU_chebyshev_infinite (a : ℂ) {lam : ℝ} (hlam : 0 < lam) :
    ∃ c : ℕ → ℂ, Summable c ∧ ∀ x : ℝ, lam ≤ x →
        HasSum (fun k : ℕ => c k*(Polynomial.Chebyshev.T ℂ (k:ℤ)).eval (1-2*(lam:ℂ)/x))
        (pcfU a x) := by
  obtain ⟨X, hX⟩ : ∃ X : ℝ → ℝ, X = fun θ => 2 * lam / (1 - Real.cos θ) := ⟨_, rfl⟩
  have hUc : Continuous (pcfU a) := (pcfU_entire a).continuous
  have hU'c : Continuous (pcfUDeriv a) := continuous_iff_continuousAt.mpr fun z =>
    (hasDerivAt_pcfUDeriv a z).continuousAt
  have hcos : ∀ θ ∈ Ioc 0 π, Real.cos θ < 1 := fun θ hθ => by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hθ.2 hθ.1; rwa [Real.cos_zero] at this
  have hXd : ∀ θ, Real.cos θ < 1 →
      HasDerivAt X (-(Real.sin θ) * X θ ^ 2 / (2 * lam)) θ := by
    intro θ hθ
    have hD : 1 - Real.cos θ ≠ 0 := by linarith
    have h := (hasDerivAt_const θ (2 * lam)).div
      ((hasDerivAt_const θ (1 : ℝ)).sub (Real.hasDerivAt_cos θ)) hD
    simp only [Pi.sub_apply] at h
    rw [hX]
    convert h using 1
    field_simp
    ring
  have hXge : ∀ θ, Real.cos θ < 1 → lam ≤ X θ := by
    intro θ hθ
    rw [hX]; dsimp only
    rw [le_div_iff₀ (by linarith)]
    nlinarith [Real.neg_one_le_cos θ]
  obtain ⟨Y1, hY1⟩ : ∃ Y : ℝ → ℝ, Y = fun θ => -(Real.sin θ) * X θ ^ 2 / (2 * lam) := ⟨_, rfl⟩
  obtain ⟨Y2, hY2⟩ : ∃ Y : ℝ → ℝ, Y = fun θ => -(Real.cos θ) * X θ ^ 2 / (2 * lam) +
      Real.sin θ ^ 2 * X θ ^ 3 / (2 * lam ^ 2) := ⟨_, rfl⟩
  have hXd' : ∀ θ, Real.cos θ < 1 → HasDerivAt X (Y1 θ) θ := by
    intro θ hθ; rw [hY1]; exact hXd θ hθ
  have hY1d : ∀ θ, Real.cos θ < 1 → HasDerivAt Y1 (Y2 θ) θ := by
    intro θ hθ
    have h := (((Real.hasDerivAt_sin θ).neg.mul ((hXd θ hθ).pow 2)).div_const (2 * lam))
    simp only [Pi.mul_apply, Pi.neg_apply, Pi.pow_apply] at h
    rw [hY1, hY2]
    convert h using 1
    field_simp
    ring
  have hUd : ∀ θ, Real.cos θ < 1 →
      HasDerivAt (fun θ => pcfU a (X θ)) (pcfUDeriv a (X θ) * Y1 θ) θ := by
    intro θ hθ
    have h := (hasDerivAt_pcfU a (X θ)).comp_ofReal.scomp θ (hXd' θ hθ)
    refine h.congr_deriv ?_
    rw [real_smul, mul_comm]
  have hU'd : ∀ θ, Real.cos θ < 1 →
      HasDerivAt (fun θ => pcfUDeriv a (X θ) * Y1 θ)
        (((X θ : ℂ) ^ 2 / 4 + a) * pcfU a (X θ) * Y1 θ * Y1 θ + pcfUDeriv a (X θ) * Y2 θ) θ := by
    intro θ hθ
    have h1 := (hasDerivAt_pcfUDeriv a (X θ)).comp_ofReal.scomp θ (hXd' θ hθ)
    have h2 := (hY1d θ hθ).ofReal_comp
    have h := h1.mul h2
    refine h.congr_deriv ?_
    rw [real_smul, Function.comp_apply]
    ring
  -- growth of the coordinate and decay of the data at `θ = 0`
  have hXlim : Tendsto X (𝓝[>] 0) atTop := by
    have h1 : Tendsto (fun θ : ℝ => 1 - Real.cos θ) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have : Tendsto (fun θ : ℝ => 1 - Real.cos θ) (𝓝 0) (𝓝 (1 - Real.cos 0)) :=
          (continuous_const.sub Real.continuous_cos).tendsto 0
        rw [Real.cos_zero, sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsGT Real.pi_pos] with θ hθ
        simpa using hcos θ ⟨hθ.1, hθ.2.le⟩
    have h2 := (tendsto_inv_nhdsGT_zero.comp h1).const_mul_atTop (show 0 < 2 * lam by positivity)
    rw [hX]
    refine h2.congr fun θ => ?_
    simp [div_eq_mul_inv]
  have hA : Tendsto (fun x : ℝ => ‖pcfUDeriv a x‖ * (x ^ 2 / (2 * lam))) atTop (𝓝 0) := by
    have h := (pcfUDeriv_real_decay a 2).const_mul (1 / (2 * lam))
    rw [mul_zero] at h
    refine h.congr fun x => ?_
    ring
  have hB : Tendsto (fun x : ℝ => (x ^ 2 / 4 + ‖a‖) * ‖pcfU a x‖ * (x ^ 2 / (2 * lam)) ^ 2 +
      ‖pcfUDeriv a x‖ * (x ^ 2 / (2 * lam) + x ^ 3 / (2 * lam ^ 2))) atTop (𝓝 0) := by
    have h := ((((pcfU_real_decay a 6).const_mul (1 / (16 * lam ^ 2))).add
      ((pcfU_real_decay a 4).const_mul (‖a‖ / (4 * lam ^ 2)))).add
      ((pcfUDeriv_real_decay a 2).const_mul (1 / (2 * lam)))).add
      ((pcfUDeriv_real_decay a 3).const_mul (1 / (2 * lam ^ 2)))
    simp only [mul_zero, add_zero] at h
    refine h.congr fun x => ?_
    field_simp
    ring
  have hbd1 : ∀ θ, Real.cos θ < 1 →
      ‖pcfUDeriv a (X θ) * Y1 θ‖ ≤ ‖pcfUDeriv a (X θ)‖ * (X θ ^ 2 / (2 * lam)) := by
    intro θ hθ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hY1]
    gcongr
    rw [abs_div, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 2 * lam),
      abs_of_nonneg (by positivity : 0 ≤ X θ ^ 2)]
    gcongr
    exact mul_le_of_le_one_left (by positivity) (Real.abs_sin_le_one θ)
  have hbd2 : ∀ θ, Real.cos θ < 1 →
      ‖((X θ : ℂ) ^ 2 / 4 + a) * pcfU a (X θ) * Y1 θ * Y1 θ + pcfUDeriv a (X θ) * Y2 θ‖ ≤
        (X θ ^ 2 / 4 + ‖a‖) * ‖pcfU a (X θ)‖ * (X θ ^ 2 / (2 * lam)) ^ 2 +
          ‖pcfUDeriv a (X θ)‖ * (X θ ^ 2 / (2 * lam) + X θ ^ 3 / (2 * lam ^ 2)) := by
    intro θ hθ
    have hX0 : 0 ≤ X θ := hlam.le.trans (hXge θ hθ)
    have hY1b : |Y1 θ| ≤ X θ ^ 2 / (2 * lam) := by
      rw [hY1]; dsimp only
      rw [abs_div, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 2 * lam),
        abs_of_nonneg (by positivity : 0 ≤ X θ ^ 2)]
      gcongr
      exact mul_le_of_le_one_left (by positivity) (Real.abs_sin_le_one θ)
    have hY2b : |Y2 θ| ≤ X θ ^ 2 / (2 * lam) + X θ ^ 3 / (2 * lam ^ 2) := by
      rw [hY2]; dsimp only
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_div, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 2 * lam),
          abs_of_nonneg (by positivity : 0 ≤ X θ ^ 2)]
        gcongr
        exact mul_le_of_le_one_left (by positivity) (Real.abs_cos_le_one θ)
      · rw [abs_div, abs_mul, abs_of_pos (by positivity : 0 < 2 * lam ^ 2),
          abs_of_nonneg (by positivity : 0 ≤ X θ ^ 3), abs_of_nonneg (sq_nonneg _)]
        gcongr
        refine mul_le_of_le_one_left (by positivity) ?_
        nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.cos θ)]
    have ha : ‖((X θ : ℂ) ^ 2 / 4 + a)‖ ≤ X θ ^ 2 / 4 + ‖a‖ := by
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hX0]
      norm_num
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc _ ≤ (X θ ^ 2 / 4 + ‖a‖) * ‖pcfU a (X θ)‖ * (X θ ^ 2 / (2 * lam)) *
            (X θ ^ 2 / (2 * lam)) := by gcongr
        _ = _ := by ring
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      gcongr
  -- the function, its derivatives in `θ`, and the expansion
  set f : ℝ → ℂ := fun s => if s < 1 then pcfU a ((2 * lam / (1 - s) : ℝ)) else 0 with hf
  set g₁ : ℝ → ℂ := fun θ => if θ = 0 then 0 else pcfUDeriv a (X θ) * Y1 θ with hg₁
  set g₂ : ℝ → ℂ := fun θ => if θ = 0 then 0 else
    ((X θ : ℂ) ^ 2 / 4 + a) * pcfU a (X θ) * Y1 θ * Y1 θ + pcfUDeriv a (X θ) * Y2 θ with hg₂
  have hfX : ∀ θ, Real.cos θ < 1 → f (Real.cos θ) = pcfU a (X θ) := by
    intro θ hθ; simp only [hf, hθ, ↓reduceIte, hX]
  have hev : ∀ θ, Real.cos θ < 1 → ∀ᶠ t in 𝓝 θ, Real.cos t < 1 := fun θ hθ =>
    Real.continuous_cos.continuousAt.eventually_lt continuousAt_const hθ
  have hne : ∀ θ ∈ Ioc 0 π, ∀ᶠ t in 𝓝 θ, t ≠ 0 := fun θ hθ => eventually_ne_nhds hθ.1.ne'
  have hg₁e : ∀ θ ∈ Ioc 0 π, g₁ =ᶠ[𝓝 θ] fun t => pcfUDeriv a (X t) * Y1 t := fun θ hθ =>
    (hne θ hθ).mono fun t ht => by simp only [hg₁, ht, ↓reduceIte]
  have hg₂e : ∀ θ ∈ Ioc 0 π, g₂ =ᶠ[𝓝 θ] fun t =>
      ((X t : ℂ) ^ 2 / 4 + a) * pcfU a (X t) * Y1 t * Y1 t + pcfUDeriv a (X t) * Y2 t :=
    fun θ hθ => (hne θ hθ).mono fun t ht => by simp only [hg₂, ht, ↓reduceIte]
  have hzero : ∀ g : ℝ → ℂ, g 0 = 0 →
      Tendsto g (𝓝[>] 0) (𝓝 0) → ContinuousWithinAt g (Icc 0 π) 0 := by
    intro g hg0 ht
    refine (continuousWithinAt_Ioi_iff_Ici.mp ?_).mono Icc_subset_Ici_self
    rw [ContinuousWithinAt, hg0]; exact ht
  have hfc : ContinuousOn f (Icc (-1) 1) := by
    intro s hs
    rcases hs.2.lt_or_eq with h1 | rfl
    · refine ContinuousAt.continuousWithinAt ?_
      have hD : 1 - s ≠ 0 := by linarith
      have hc : ContinuousAt (fun s : ℝ => pcfU a ((2 * lam / (1 - s) : ℝ))) s :=
        hUc.continuousAt.comp (continuous_ofReal.continuousAt.comp
          (continuousAt_const.div (continuousAt_const.sub continuousAt_id) hD))
      refine hc.congr ?_
      filter_upwards [eventually_lt_nhds h1] with t ht
      simp only [hf, ht, ↓reduceIte]
    · refine (continuousWithinAt_Iio_iff_Iic.mp ?_).mono fun t ht => ht.2
      have h1 : Tendsto (fun s : ℝ => 1 - s) (𝓝[<] 1) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · have : Tendsto (fun s : ℝ => 1 - s) (𝓝 1) (𝓝 (1 - 1)) :=
            (continuous_const.sub continuous_id).tendsto 1
          rw [sub_self] at this
          exact this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with s hs
          simpa using hs
      have h2 : Tendsto (fun s : ℝ => 2 * lam / (1 - s)) (𝓝[<] 1) atTop := by
        refine ((tendsto_inv_nhdsGT_zero.comp h1).const_mul_atTop
          (show 0 < 2 * lam by positivity)).congr fun s => ?_
        simp [div_eq_mul_inv]
      have h3 : Tendsto (fun x : ℝ => pcfU a x) atTop (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        simpa using pcfU_real_decay a 0
      rw [ContinuousWithinAt, show f 1 = 0 by simp [hf]]
      refine (h3.comp h2).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Function.comp_apply, hf, show s < 1 from hs, ↓reduceIte]
  have hsmall : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ ∈ Ioc 0 π := by
    filter_upwards [Ioo_mem_nhdsGT Real.pi_pos] with θ hθ
    exact ⟨hθ.1, hθ.2.le⟩
  have hg₁c : ContinuousOn g₁ (Icc 0 π) := by
    intro θ hθ
    rcases hθ.1.lt_or_eq with h0 | rfl
    · have hθ' : θ ∈ Ioc 0 π := ⟨h0, hθ.2⟩
      exact ((hU'd θ (hcos θ hθ')).continuousAt.congr (hg₁e θ hθ').symm).continuousWithinAt
    · refine hzero g₁ (by simp [hg₁]) (squeeze_zero_norm' ?_ (hA.comp hXlim))
      filter_upwards [hsmall] with θ hθ
      simp only [hg₁, hθ.1.ne', ↓reduceIte, Function.comp_apply]
      exact hbd1 θ (hcos θ hθ)
  have hY2c : ∀ θ, Real.cos θ < 1 → ContinuousAt Y2 θ := by
    intro θ hθ
    have hXc := (hXd' θ hθ).continuousAt
    rw [hY2]
    exact ((Real.continuous_cos.continuousAt.neg.mul (hXc.pow 2)).div_const _).add
      (((Real.continuous_sin.continuousAt.pow 2).mul (hXc.pow 3)).div_const _)
  have hg₂c : ContinuousOn g₂ (Icc 0 π) := by
    intro θ hθ
    rcases hθ.1.lt_or_eq with h0 | rfl
    · have hθ' : θ ∈ Ioc 0 π := ⟨h0, hθ.2⟩
      have hc := hcos θ hθ'
      have hXc : ContinuousAt (fun t => (X t : ℂ)) θ :=
        continuous_ofReal.continuousAt.comp (hXd' θ hc).continuousAt
      have hY1c : ContinuousAt (fun t => (Y1 t : ℂ)) θ :=
        continuous_ofReal.continuousAt.comp (hY1d θ hc).continuousAt
      have hY2c' : ContinuousAt (fun t => (Y2 t : ℂ)) θ :=
        continuous_ofReal.continuousAt.comp (hY2c θ hc)
      have hUx : ContinuousAt (fun t => pcfU a (X t)) θ := hUc.continuousAt.comp hXc
      have hU'x : ContinuousAt (fun t => pcfUDeriv a (X t)) θ := hU'c.continuousAt.comp hXc
      refine ContinuousAt.continuousWithinAt (ContinuousAt.congr ?_ (hg₂e θ hθ').symm)
      exact (((((hXc.pow 2).div_const 4).add continuousAt_const).mul hUx).mul hY1c).mul hY1c
        |>.add (hU'x.mul hY2c')
    · refine hzero g₂ (by simp [hg₂]) (squeeze_zero_norm' ?_ (hB.comp hXlim))
      filter_upwards [hsmall] with θ hθ
      simp only [hg₂, hθ.1.ne', ↓reduceIte, Function.comp_apply]
      exact hbd2 θ (hcos θ hθ)
  have hf' : ∀ θ ∈ Ioo 0 π, HasDerivAt (fun θ => f (Real.cos θ)) (g₁ θ) θ := by
    intro θ hθ
    have hc := hcos θ ⟨hθ.1, hθ.2.le⟩
    have h := (hUd θ hc).congr_of_eventuallyEq ((hev θ hc).mono fun t ht => hfX t ht)
    simpa only [hg₁, hθ.1.ne', ↓reduceIte] using h
  have hg₁' : ∀ θ ∈ Ioo 0 π, HasDerivAt g₁ (g₂ θ) θ := by
    intro θ hθ
    have hθ' : θ ∈ Ioc 0 π := ⟨hθ.1, hθ.2.le⟩
    have h := (hU'd θ (hcos θ hθ')).congr_of_eventuallyEq (hg₁e θ hθ')
    simpa only [hg₂, hθ.1.ne', ↓reduceIte] using h
  have hg₁π : g₁ π = 0 := by
    simp [hg₁, Real.pi_ne_zero, hY1]
  obtain ⟨c, hc, hs⟩ := Polynomial.Chebyshev.exists_summable_series_of_hasDerivAt hfc hf' hg₁c
    (by simp [hg₁]) hg₁π hg₁' hg₂c
  refine ⟨c, hc, fun x hx => ?_⟩
  have hx0 : 0 < x := hlam.trans_le hx
  have hmem : 1 - 2 * lam / x ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · rw [le_sub_comm, sub_neg_eq_add, div_le_iff₀ hx0]; linarith
    · have : 0 ≤ 2 * lam / x := by positivity
      linarith
  have h := hs _ hmem
  have hlt : 1 - 2 * lam / x < 1 := by
    have : 0 < 2 * lam / x := by positivity
    linarith
  have hval : f (1 - 2 * lam / x) = pcfU a x := by
    simp only [hf, hlt, ↓reduceIte]
    congr 2
    field_simp
    ring
  rw [hval] at h
  convert h using 3
  push_cast
  ring

/- DLMF 12.6 points to a continued-fraction reference without specifying
coefficients; it adds no displayed fraction to acquire. Sections 12.18–21
contain computational references, a bibliography of external tables, the above
Chebyshev existence claims, and software listings. -/

end DLMF.Confluent
