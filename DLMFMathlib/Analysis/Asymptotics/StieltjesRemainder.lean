/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.WatsonRotated

/-!
# Remainders of Stieltjes transforms

For a nonnegative density `φ` on `(0, ∞)` with finite moments `m_k = ∫ τ^k φ(τ) dτ`, the
Stieltjes-type transform

  `F(S) = ∫₀^∞ φ(τ) / (1 + τ/S) dτ`,   `S ∉ (-∞, 0]`,

has the asymptotic expansion `Σ (-1)^k m_k S^{-k}`, and its remainder after `N` terms is exactly
`(-1)^N S^{-N} ∫ τ^N φ(τ) / (1 + τ/S) dτ`. Since `|1 + τ/S| ≥ 1` for `re S ≥ 0` and
`|1 + τ/S| ≥ |sin (arg S)|` in general, the remainder is bounded by the first neglected term
times `1`, respectively `|csc (arg S)|` (Olver, *Asymptotics and Special Functions*, Ch. 3 §9;
the bounds of DLMF 9.7.17, 6.12(i) and 2.4 are of this type). On the imaginary axis the real
and imaginary parts are Stieltjes transforms in `S²` and their even and odd remainders are
enclosed by the first neglected term with its sign.

## Main results

* `stRem_remainder_eq`: the exact remainder.
* `stRem_remainder_le`: the bound by the first neglected term divided by `stRem_c S`, where
  `stRem_c S = 1` for `re S ≥ 0` and `|sin (arg S)|` otherwise.
* `stRem_remainder_le_of_re_nonneg`, `stRem_remainder_le_csc`: the two sector cases.
* `stRem_transform_I_mul`: `F(iX) = E(X) + i O(X)` with the even and odd real transforms.
* `stRem_even_remainder`, `stRem_odd_remainder`: signed first-neglected-term enclosures.

All helper names carry the prefix `stRem_`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset Complex
open scoped Real

/-- The Stieltjes-type transform `∫₀^∞ φ(τ) / (1 + τ/S) dτ`. -/
def stRem_transform (φ : ℝ → ℝ) (S : ℂ) : ℂ :=
  ∫ τ in Ioi (0 : ℝ), (φ τ : ℂ) / (1 + τ / S)

/-- The moment `∫₀^∞ τ^k φ(τ) dτ`. -/
def stRem_moment (φ : ℝ → ℝ) (k : ℕ) : ℝ :=
  ∫ τ in Ioi (0 : ℝ), τ ^ k * φ τ

/-- The lower bound for `‖1 + τ/S‖` on `τ ≥ 0`: `1` if `re S ≥ 0`, else `|sin (arg S)|`. -/
def stRem_c (S : ℂ) : ℝ := if 0 ≤ S.re then 1 else |Real.sin (arg S)|

/-- The finite geometric expansion `1/(1+x) = Σ_{k<N} (-x)^k + (-x)^N/(1+x)`. -/
theorem stRem_geom {𝕜 : Type*} [Field 𝕜] (x : 𝕜) (hx : 1 + x ≠ 0) (N : ℕ) :
    1 / (1 + x) = ∑ k ∈ range N, (-x) ^ k + (-x) ^ N / (1 + x) := by
  have h := geom_sum_mul_neg (-x) N
  rw [sub_neg_eq_add] at h
  field_simp
  linear_combination -h

/-- `‖1 + τ/S‖ = ‖S + τ‖ / ‖S‖`. -/
theorem stRem_norm_one_add_div {S : ℂ} (hS : S ≠ 0) (τ : ℝ) :
    ‖1 + (τ : ℂ) / S‖ = ‖S + τ‖ / ‖S‖ := by
  rw [show 1 + (τ : ℂ) / S = (S + τ) / S by field_simp, norm_div]

theorem stRem_c_pos {S : ℂ} (hS : S ∈ slitPlane) : 0 < stRem_c S := by
  unfold stRem_c
  split_ifs with h
  · exact one_pos
  · have him : S.im ≠ 0 := by
      rcases hS with h' | h'
      · exact absurd h'.le h
      · exact h'
    rw [sin_arg]
    have : 0 < ‖S‖ := norm_pos_iff.mpr (slitPlane_ne_zero hS)
    exact abs_pos.mpr (div_ne_zero him this.ne')

theorem stRem_c_le_one (S : ℂ) : stRem_c S ≤ 1 := by
  unfold stRem_c
  split_ifs
  · exact le_rfl
  · exact Real.abs_sin_le_one _

/-- The basic lower bound `stRem_c S ≤ ‖1 + τ/S‖` for `τ ≥ 0`. -/
theorem stRem_c_le_norm {S : ℂ} (hS : S ∈ slitPlane) {τ : ℝ} (hτ : 0 ≤ τ) :
    stRem_c S ≤ ‖1 + (τ : ℂ) / S‖ := by
  have hS0 := slitPlane_ne_zero hS
  have hn : 0 < ‖S‖ := norm_pos_iff.mpr hS0
  rw [stRem_norm_one_add_div hS0, le_div_iff₀ hn]
  unfold stRem_c
  split_ifs with h
  · rw [one_mul]
    have h1 : ‖S‖ ^ 2 ≤ ‖S + τ‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp only [add_re, ofReal_re, add_im, ofReal_im, add_zero]
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1
  · rw [sin_arg, abs_div, abs_norm, div_mul_cancel₀ _ hn.ne']
    calc |S.im| = |(S + τ).im| := by simp
      _ ≤ ‖S + τ‖ := Complex.abs_im_le_norm _

theorem stRem_one_add_ne_zero {S : ℂ} (hS : S ∈ slitPlane) {τ : ℝ} (hτ : 0 ≤ τ) :
    1 + (τ : ℂ) / S ≠ 0 := by
  intro h
  have := stRem_c_le_norm hS hτ
  rw [h, norm_zero] at this
  exact (stRem_c_pos hS).not_ge this

/-- `‖1/(1+τ/S)‖ ≤ 1/stRem_c S`. -/
theorem stRem_norm_recip_le {S : ℂ} (hS : S ∈ slitPlane) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖1 / (1 + (τ : ℂ) / S)‖ ≤ 1 / stRem_c S := by
  rw [norm_div, norm_one]
  exact one_div_le_one_div_of_le (stRem_c_pos hS) (stRem_c_le_norm hS hτ)

/-- Integrability of `ψ(τ)/(1+τ/S)` for integrable `ψ`. -/
theorem stRem_integrableOn {ψ : ℝ → ℂ} (hψ : IntegrableOn ψ (Ioi 0)) {S : ℂ} (hS : S ∈ slitPlane) :
    IntegrableOn (fun τ : ℝ => ψ τ / (1 + τ / S)) (Ioi 0) := by
  have hm : Measurable fun τ : ℝ => (1 + (τ : ℂ) / S)⁻¹ := by fun_prop
  refine Integrable.mono' (hψ.norm.const_mul (1 / stRem_c S))
    (hψ.aestronglyMeasurable.mul hm.aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun τ hτ => ?_)
  have h := stRem_norm_recip_le hS (le_of_lt (show (0:ℝ) < τ from hτ))
  rw [div_eq_mul_one_div, norm_mul]
  calc ‖ψ τ‖ * ‖1 / (1 + (τ : ℂ) / S)‖ ≤ ‖ψ τ‖ * (1 / stRem_c S) :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = _ := mul_comm _ _

/-- **Exact remainder** of the Stieltjes expansion after `N` terms. -/
theorem stRem_remainder_eq {φ : ℝ → ℝ} {N : ℕ}
    (hφ : ∀ k ≤ N, IntegrableOn (fun τ : ℝ => τ ^ k * φ τ) (Ioi 0)) {S : ℂ} (hS : S ∈ slitPlane) :
    stRem_transform φ S - ∑ k ∈ range N, (-1 : ℂ) ^ k * stRem_moment φ k / S ^ k =
      (-1 : ℂ) ^ N / S ^ N * ∫ τ in Ioi (0 : ℝ), ((τ ^ N * φ τ : ℝ) : ℂ) / (1 + τ / S) := by
  have hS0 := slitPlane_ne_zero hS
  have hint : ∀ k ≤ N, IntegrableOn (fun τ : ℝ => ((τ ^ k * φ τ : ℝ) : ℂ)) (Ioi 0) :=
    fun k hk => (hφ k hk).ofReal
  have hpt : ∀ τ ∈ Ioi (0 : ℝ), (φ τ : ℂ) / (1 + τ / S) =
      ∑ k ∈ range N, ((τ ^ k * φ τ : ℝ) : ℂ) * ((-1 : ℂ) ^ k / S ^ k) +
        (-1 : ℂ) ^ N / S ^ N * (((τ ^ N * φ τ : ℝ) : ℂ) / (1 + τ / S)) := by
    intro τ hτ
    have hne := stRem_one_add_ne_zero hS (le_of_lt (show (0:ℝ) < τ from hτ))
    have hg := stRem_geom ((τ : ℂ) / S) hne N
    rw [div_eq_mul_one_div, hg, mul_add, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      rw [neg_pow, div_pow]
      ring
    · push_cast
      rw [neg_pow, div_pow]
      ring
  have hsum : IntegrableOn (fun τ : ℝ => ∑ k ∈ range N, ((τ ^ k * φ τ : ℝ) : ℂ) *
      ((-1 : ℂ) ^ k / S ^ k)) (Ioi 0) :=
    integrable_finsetSum _ fun k hk =>
      (hint k (le_of_lt (Finset.mem_range.mp hk))).mul_const _
  have hrem : IntegrableOn (fun τ : ℝ => (-1 : ℂ) ^ N / S ^ N *
      (((τ ^ N * φ τ : ℝ) : ℂ) / (1 + τ / S))) (Ioi 0) :=
    (stRem_integrableOn (hint N le_rfl) hS).const_mul _
  unfold stRem_transform
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add hsum hrem,
    integral_finsetSum _ fun k hk => (hint k (le_of_lt (Finset.mem_range.mp hk))).mul_const _,
    integral_const_mul]
  have : ∀ k ∈ range N, ∫ τ in Ioi (0 : ℝ), ((τ ^ k * φ τ : ℝ) : ℂ) * ((-1 : ℂ) ^ k / S ^ k) =
      (-1 : ℂ) ^ k * stRem_moment φ k / S ^ k := by
    intro k _
    rw [integral_mul_const, integral_complex_ofReal, stRem_moment]
    ring
  rw [Finset.sum_congr rfl this]
  ring

/-- **Remainder bound**: the remainder is at most the first neglected term divided by
`stRem_c S`. -/
theorem stRem_remainder_le {φ : ℝ → ℝ} {N : ℕ} (hφ0 : ∀ τ ∈ Ioi (0 : ℝ), 0 ≤ φ τ)
    (hφ : ∀ k ≤ N, IntegrableOn (fun τ : ℝ => τ ^ k * φ τ) (Ioi 0)) {S : ℂ} (hS : S ∈ slitPlane) :
    ‖stRem_transform φ S - ∑ k ∈ range N, (-1 : ℂ) ^ k * stRem_moment φ k / S ^ k‖ ≤
      stRem_moment φ N / (stRem_c S * ‖S‖ ^ N) := by
  have hS0 := slitPlane_ne_zero hS
  have hc := stRem_c_pos hS
  have hn : 0 < ‖S‖ ^ N := pow_pos (norm_pos_iff.mpr hS0) N
  rw [stRem_remainder_eq hφ hS, norm_mul, norm_div, norm_pow, norm_pow, norm_neg, norm_one,
    one_pow]
  have hI : ‖∫ τ in Ioi (0 : ℝ), ((τ ^ N * φ τ : ℝ) : ℂ) / (1 + τ / S)‖ ≤
      ∫ τ in Ioi (0 : ℝ), τ ^ N * φ τ * (1 / stRem_c S) := by
    refine norm_integral_le_of_norm_le ((hφ N le_rfl).mul_const _) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun τ hτ => ?_)
    have hτ' : (0 : ℝ) < τ := hτ
    rw [div_eq_mul_one_div, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg (pow_nonneg hτ'.le _) (hφ0 τ hτ))]
    exact mul_le_mul_of_nonneg_left (stRem_norm_recip_le hS hτ'.le)
      (mul_nonneg (pow_nonneg hτ'.le _) (hφ0 τ hτ))
  rw [integral_mul_const] at hI
  calc 1 / ‖S‖ ^ N * ‖∫ τ in Ioi (0 : ℝ), ((τ ^ N * φ τ : ℝ) : ℂ) / (1 + τ / S)‖
      ≤ 1 / ‖S‖ ^ N * ((∫ τ in Ioi (0 : ℝ), τ ^ N * φ τ) * (1 / stRem_c S)) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ = _ := by rw [stRem_moment]; field_simp

/-- The case `re S ≥ 0`: the remainder is bounded by the first neglected term. -/
theorem stRem_remainder_le_of_re_nonneg {φ : ℝ → ℝ} {N : ℕ} (hφ0 : ∀ τ ∈ Ioi (0 : ℝ), 0 ≤ φ τ)
    (hφ : ∀ k ≤ N, IntegrableOn (fun τ : ℝ => τ ^ k * φ τ) (Ioi 0)) {S : ℂ} (hS : S ≠ 0)
    (hre : 0 ≤ S.re) :
    ‖stRem_transform φ S - ∑ k ∈ range N, (-1 : ℂ) ^ k * stRem_moment φ k / S ^ k‖ ≤
      stRem_moment φ N / ‖S‖ ^ N := by
  have hS' : S ∈ slitPlane := by
    rcases hre.lt_or_eq with h | h
    · exact Or.inl h
    · refine Or.inr fun him => hS ?_
      exact Complex.ext h.symm him
  have h := stRem_remainder_le hφ0 hφ hS'
  simpa only [stRem_c, hre, ↓reduceIte, one_mul] using h

/-- The `|csc (arg S)|` bound, valid on the whole slit plane. -/
theorem stRem_remainder_le_csc {φ : ℝ → ℝ} {N : ℕ} (hφ0 : ∀ τ ∈ Ioi (0 : ℝ), 0 ≤ φ τ)
    (hφ : ∀ k ≤ N, IntegrableOn (fun τ : ℝ => τ ^ k * φ τ) (Ioi 0)) {S : ℂ} (hS : S ∈ slitPlane)
    (hsin : Real.sin (arg S) ≠ 0) :
    ‖stRem_transform φ S - ∑ k ∈ range N, (-1 : ℂ) ^ k * stRem_moment φ k / S ^ k‖ ≤
      |(Real.sin (arg S))⁻¹| * (stRem_moment φ N / ‖S‖ ^ N) := by
  have hmom : 0 ≤ stRem_moment φ N :=
    setIntegral_nonneg measurableSet_Ioi fun τ hτ =>
      mul_nonneg (pow_nonneg (le_of_lt (show (0:ℝ) < τ from hτ)) _) (hφ0 τ hτ)
  have hn : 0 < ‖S‖ ^ N := pow_pos (norm_pos_iff.mpr (slitPlane_ne_zero hS)) N
  refine (stRem_remainder_le hφ0 hφ hS).trans ?_
  have hc : |Real.sin (arg S)| ≤ stRem_c S := by
    unfold stRem_c; split_ifs
    · exact Real.abs_sin_le_one _
    · exact le_rfl
  have hs : 0 < |Real.sin (arg S)| := abs_pos.mpr hsin
  rw [abs_inv, show |Real.sin (arg S)|⁻¹ * (stRem_moment φ N / ‖S‖ ^ N) =
    stRem_moment φ N / (|Real.sin (arg S)| * ‖S‖ ^ N) by field_simp]
  exact div_le_div_of_nonneg_left hmom (mul_pos hs hn) (mul_le_mul_of_nonneg_right hc hn.le)

/-! ### The imaginary axis: even and odd parts -/

/-- The even real transform `∫₀^∞ φ(τ) / (1 + (τ/X)²) dτ`. -/
def stRem_even (φ : ℝ → ℝ) (X : ℝ) : ℝ :=
  ∫ τ in Ioi (0 : ℝ), φ τ / (1 + (τ / X) ^ 2)

/-- The odd real transform `∫₀^∞ φ(τ) (τ/X) / (1 + (τ/X)²) dτ`. -/
def stRem_odd (φ : ℝ → ℝ) (X : ℝ) : ℝ :=
  ∫ τ in Ioi (0 : ℝ), φ τ * (τ / X) / (1 + (τ / X) ^ 2)

/-- Integrability of `ψ(τ)/(1+(τ/X)²)` for integrable `ψ`. -/
theorem stRem_integrableOn_real {ψ : ℝ → ℝ} (hψ : IntegrableOn ψ (Ioi 0)) (X : ℝ) :
    IntegrableOn (fun τ : ℝ => ψ τ / (1 + (τ / X) ^ 2)) (Ioi 0) := by
  have hm : AEStronglyMeasurable (fun τ : ℝ => ψ τ / (1 + (τ / X) ^ 2))
      (volume.restrict (Ioi 0)) := by
    simp_rw [div_eq_mul_inv]
    exact hψ.aestronglyMeasurable.mul
      (by fun_prop : Measurable fun τ : ℝ => (1 + (τ / X) ^ 2)⁻¹).aestronglyMeasurable
  refine Integrable.mono' hψ.norm hm (Filter.Eventually.of_forall fun τ => ?_)
  rw [norm_div, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + (τ / X) ^ 2)]
  rw [div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (τ / X), norm_nonneg (ψ τ), mul_nonneg (norm_nonneg (ψ τ)) (sq_nonneg (τ / X))]

/-- **Exact signed remainder of the even transform.** For `ψ ≥ 0` with finite even moments,
`∫ψ/(1+(τ/X)²) - Σ_{k<N} (-1)^k X^{-2k} ∫τ^{2k}ψ = (-1)^N X^{-2N} J` with
`0 ≤ J ≤ ∫ τ^{2N} ψ`. -/
theorem stRem_even_core {ψ : ℝ → ℝ} {N : ℕ} (hψ0 : ∀ τ ∈ Ioi (0 : ℝ), 0 ≤ ψ τ)
    (hψ : ∀ k ≤ N, IntegrableOn (fun τ : ℝ => τ ^ (2 * k) * ψ τ) (Ioi 0)) {X : ℝ} (hX : 0 < X) :
    ∃ J : ℝ, 0 ≤ J ∧ J ≤ ∫ τ in Ioi (0 : ℝ), τ ^ (2 * N) * ψ τ ∧
      (∫ τ in Ioi (0 : ℝ), ψ τ / (1 + (τ / X) ^ 2)) -
        ∑ k ∈ range N, (-1 : ℝ) ^ k * (∫ τ in Ioi (0 : ℝ), τ ^ (2 * k) * ψ τ) / X ^ (2 * k) =
      (-1 : ℝ) ^ N / X ^ (2 * N) * J := by
  have hX0 := hX.ne'
  refine ⟨∫ τ in Ioi (0 : ℝ), τ ^ (2 * N) * ψ τ / (1 + (τ / X) ^ 2), ?_, ?_, ?_⟩
  · refine setIntegral_nonneg measurableSet_Ioi fun τ hτ => ?_
    have := hψ0 τ hτ
    have : (0 : ℝ) ≤ τ ^ (2 * N) := pow_nonneg (le_of_lt (show (0:ℝ) < τ from hτ)) _
    positivity
  · refine setIntegral_mono_on (stRem_integrableOn_real (hψ N le_rfl) X) (hψ N le_rfl)
      measurableSet_Ioi fun τ hτ => ?_
    have h1 : (0 : ℝ) ≤ τ ^ (2 * N) * ψ τ :=
      mul_nonneg (pow_nonneg (le_of_lt (show (0:ℝ) < τ from hτ)) _) (hψ0 τ hτ)
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (τ / X), mul_nonneg h1 (sq_nonneg (τ / X))]
  · have hpt : ∀ τ ∈ Ioi (0 : ℝ), ψ τ / (1 + (τ / X) ^ 2) =
        ∑ k ∈ range N, τ ^ (2 * k) * ψ τ * ((-1 : ℝ) ^ k / X ^ (2 * k)) +
          (-1 : ℝ) ^ N / X ^ (2 * N) * (τ ^ (2 * N) * ψ τ / (1 + (τ / X) ^ 2)) := by
      intro τ _
      have hu : (1 : ℝ) + (τ / X) ^ 2 ≠ 0 := by positivity
      have hpow : ∀ k : ℕ, (-(τ / X) ^ 2) ^ k = (-1 : ℝ) ^ k * τ ^ (2 * k) / X ^ (2 * k) := by
        intro k; rw [neg_pow, ← pow_mul, div_pow]; ring
      rw [div_eq_mul_one_div, stRem_geom _ hu N, mul_add, Finset.mul_sum, hpow]
      congr 1
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [hpow]; ring
      · ring
    have hsum : IntegrableOn (fun τ : ℝ => ∑ k ∈ range N, τ ^ (2 * k) * ψ τ *
        ((-1 : ℝ) ^ k / X ^ (2 * k))) (Ioi 0) :=
      integrable_finsetSum _ fun k hk =>
        (hψ k (le_of_lt (Finset.mem_range.mp hk))).mul_const _
    have hrem : IntegrableOn (fun τ : ℝ => (-1 : ℝ) ^ N / X ^ (2 * N) *
        (τ ^ (2 * N) * ψ τ / (1 + (τ / X) ^ 2))) (Ioi 0) :=
      (stRem_integrableOn_real (hψ N le_rfl) X).const_mul _
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add hsum hrem,
      integral_finsetSum _ fun k hk => (hψ k (le_of_lt (Finset.mem_range.mp hk))).mul_const _,
      integral_const_mul]
    have : ∀ k ∈ range N, ∫ τ in Ioi (0 : ℝ), τ ^ (2 * k) * ψ τ * ((-1 : ℝ) ^ k / X ^ (2 * k)) =
        (-1 : ℝ) ^ k * (∫ τ in Ioi (0 : ℝ), τ ^ (2 * k) * ψ τ) / X ^ (2 * k) := by
      intro k _
      rw [integral_mul_const]
      ring
    rw [Finset.sum_congr rfl this]
    ring

/-- From the exact signed form: the remainder is bounded by the first neglected term and has
its sign. -/
theorem stRem_signed_of_core {R m : ℝ} {N : ℕ} {Y : ℝ} (hY : 0 < Y) {J : ℝ} (hJ0 : 0 ≤ J)
    (hJm : J ≤ m) (hR : R = (-1 : ℝ) ^ N / Y * J) :
    |R| ≤ m / Y ∧ 0 ≤ R * ((-1 : ℝ) ^ N * m) := by
  have hs : ((-1 : ℝ) ^ N) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have ha : |(-1 : ℝ) ^ N| = 1 := by simp
  subst hR
  refine ⟨?_, ?_⟩
  · rw [abs_mul, abs_div, ha, abs_of_pos hY, abs_of_nonneg hJ0]
    rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right hJm hY.le
  · have : (-1 : ℝ) ^ N / Y * J * ((-1 : ℝ) ^ N * m) = ((-1 : ℝ) ^ N) ^ 2 * (J * m / Y) := by
      ring
    rw [this, hs, one_mul]
    exact div_nonneg (mul_nonneg hJ0 (hJ0.trans hJm)) hY.le

/-- **Even part on the imaginary axis**: signed first-neglected-term enclosure. -/
theorem stRem_even_remainder {φ : ℝ → ℝ} {N : ℕ} (hφ0 : ∀ τ ∈ Ioi (0 : ℝ), 0 ≤ φ τ)
    (hφ : ∀ k ≤ 2 * N, IntegrableOn (fun τ : ℝ => τ ^ k * φ τ) (Ioi 0)) {X : ℝ} (hX : 0 < X) :
    |stRem_even φ X - ∑ k ∈ range N, (-1 : ℝ) ^ k * stRem_moment φ (2 * k) / X ^ (2 * k)| ≤
        stRem_moment φ (2 * N) / X ^ (2 * N) ∧
      0 ≤ (stRem_even φ X - ∑ k ∈ range N, (-1 : ℝ) ^ k * stRem_moment φ (2 * k) / X ^ (2 * k)) *
        ((-1 : ℝ) ^ N * stRem_moment φ (2 * N)) := by
  obtain ⟨J, hJ0, hJm, hR⟩ := stRem_even_core (ψ := φ) (N := N) hφ0
    (fun k hk => hφ (2 * k) (by omega)) hX
  exact stRem_signed_of_core (pow_pos hX _) hJ0 hJm hR

/-- **Odd part on the imaginary axis**: signed first-neglected-term enclosure. -/
theorem stRem_odd_remainder {φ : ℝ → ℝ} {N : ℕ} (hφ0 : ∀ τ ∈ Ioi (0 : ℝ), 0 ≤ φ τ)
    (hφ : ∀ k ≤ 2 * N + 1, IntegrableOn (fun τ : ℝ => τ ^ k * φ τ) (Ioi 0)) {X : ℝ}
    (hX : 0 < X) :
    |stRem_odd φ X - ∑ k ∈ range N, (-1 : ℝ) ^ k * stRem_moment φ (2 * k + 1) / X ^ (2 * k + 1)| ≤
        stRem_moment φ (2 * N + 1) / X ^ (2 * N + 1) ∧
      0 ≤ (stRem_odd φ X -
          ∑ k ∈ range N, (-1 : ℝ) ^ k * stRem_moment φ (2 * k + 1) / X ^ (2 * k + 1)) *
        ((-1 : ℝ) ^ N * stRem_moment φ (2 * N + 1)) := by
  have hX0 := hX.ne'
  obtain ⟨J, hJ0, hJm, hR⟩ := stRem_even_core (ψ := fun τ => τ * φ τ) (N := N)
    (fun τ hτ => mul_nonneg (le_of_lt (show (0:ℝ) < τ from hτ)) (hφ0 τ hτ))
    (fun k hk => by
      simpa [pow_succ, mul_assoc] using hφ (2 * k + 1) (by omega)) hX
  have hmom : ∀ k, (∫ τ in Ioi (0 : ℝ), τ ^ (2 * k) * (τ * φ τ)) = stRem_moment φ (2 * k + 1) := by
    intro k; rw [stRem_moment]; congr 1; ext τ; ring
  have hodd : stRem_odd φ X = (∫ τ in Ioi (0 : ℝ), τ * φ τ / (1 + (τ / X) ^ 2)) / X := by
    rw [stRem_odd, ← integral_div]; congr 1; ext τ; field_simp
  rw [hmom] at hJm
  simp only [hmom] at hR
  refine stRem_signed_of_core (pow_pos hX _) hJ0 hJm ?_
  rw [hodd]
  have : ∑ k ∈ range N, (-1 : ℝ) ^ k * stRem_moment φ (2 * k + 1) / X ^ (2 * k + 1) =
      (∑ k ∈ range N, (-1 : ℝ) ^ k * stRem_moment φ (2 * k + 1) / X ^ (2 * k)) / X := by
    rw [Finset.sum_div]; refine Finset.sum_congr rfl fun k _ => ?_; rw [pow_succ]; field_simp
  rw [this, ← sub_div, hR, pow_succ]
  field_simp

/-- On the imaginary axis, `F(iX) = E(X) + i O(X)`. -/
theorem stRem_transform_I_mul {φ : ℝ → ℝ} (hφ : IntegrableOn φ (Ioi 0))
    (hφ1 : IntegrableOn (fun τ : ℝ => τ * φ τ) (Ioi 0)) {X : ℝ} (hX : 0 < X) :
    stRem_transform φ (X * I) = stRem_even φ X + stRem_odd φ X * I := by
  have hX0 : (X : ℂ) ≠ 0 := ofReal_ne_zero.mpr hX.ne'
  have hE := stRem_integrableOn_real hφ X
  have hO : IntegrableOn (fun τ : ℝ => φ τ * (τ / X) / (1 + (τ / X) ^ 2)) (Ioi 0) := by
    have := stRem_integrableOn_real (hφ1.div_const X) X
    refine this.congr_fun (fun τ _ => ?_) measurableSet_Ioi
    simp only; ring
  have hpt : ∀ τ ∈ Ioi (0 : ℝ), (φ τ : ℂ) / (1 + τ / (X * I)) =
      ((φ τ / (1 + (τ / X) ^ 2) : ℝ) : ℂ) + ((φ τ * (τ / X) / (1 + (τ / X) ^ 2) : ℝ) : ℂ) * I := by
    intro τ _
    have hu : (1 : ℂ) + ((τ : ℂ) / X) ^ 2 ≠ 0 := by
      rw [show (1 : ℂ) + ((τ : ℂ) / X) ^ 2 = ((1 + (τ / X) ^ 2 : ℝ) : ℂ) by push_cast; ring]
      exact ofReal_ne_zero.mpr (by positivity)
    have hw : (1 : ℂ) + τ / (X * I) = 1 - (τ / X) * I := by
      field_simp; linear_combination (τ : ℂ) * I_sq
    have hv : (1 : ℂ) - (τ / X) * I ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
    rw [hw, div_eq_iff hv]
    push_cast
    generalize (τ : ℂ) / X = t at hu ⊢
    field_simp
    linear_combination ((φ τ : ℂ) * t ^ 2) * I_sq
  have hE' : IntegrableOn (fun τ : ℝ => ((φ τ / (1 + (τ / X) ^ 2) : ℝ) : ℂ)) (Ioi 0) := hE.ofReal
  have hO' : IntegrableOn (fun τ : ℝ => ((φ τ * (τ / X) / (1 + (τ / X) ^ 2) : ℝ) : ℂ) * I)
      (Ioi 0) := hO.ofReal.mul_const _
  unfold stRem_transform stRem_even stRem_odd
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add hE' hO',
    integral_mul_const, integral_complex_ofReal, integral_complex_ofReal]

/-! ### The χ-bound along a ray (Olver's `1 + χ(m)` multiplier)

Writing `1/(X + t) = ∫₀^∞ e^{-(X+t)ρ e^{iβ}} e^{iβ} dρ` on a ray where `(X+t)e^{iβ}` has positive
real part and integrating first in `t`, the Laplace integral `∫₀^∞ r^m e^{-Wr}/(X + r e^{iθ}) dr`
is bounded by `Γ(m+1) ∫₀^∞ (W² + ρ²)^{-(m+1)/2} dρ = Γ(m) χ(m) W^{-m}` whenever
`θ + β = ±π/2` with `|β| < π/2`, i.e. for `π/2 ≤ |θ| < π`.
-/

theorem stRem_recip_eq_integral {c : ℂ} (hc : 0 < c.re) :
    1 / c = ∫ ρ in Ioi (0 : ℝ), Complex.exp (-(c * ρ)) := by
  have h := integral_exp_mul_complex_Ioi (a := -c) (by simp; linarith) 0
  simp only [ofReal_zero, mul_zero, Complex.exp_zero] at h
  rw [show (fun x : ℝ => Complex.exp (-(c * x))) = fun x : ℝ => Complex.exp (-c * x) by
    funext x; ring_nf, h]
  rw [neg_div, div_neg, neg_neg]

theorem stRem_norm_add_exp {W ρ σ : ℝ} (hσ : Real.cos σ = 0) :
    ‖(W : ℂ) + ρ * exp (σ * I)‖ = Real.sqrt (W ^ 2 + ρ ^ 2) := by
  rw [norm_eq_sqrt_sq_add_sq]
  congr 1
  have h1 : ((W : ℂ) + ρ * exp (σ * I)).re = W + ρ * Real.cos σ := by
    simp [exp_ofReal_mul_I_re]
  have h2 : ((W : ℂ) + ρ * exp (σ * I)).im = ρ * Real.sin σ := by
    simp [exp_ofReal_mul_I_im]
  rw [h1, h2, hσ]
  have := Real.sin_sq_add_cos_sq σ
  rw [hσ] at this
  nlinarith [this]

/-- The Laplace kernel `r^m e^{-Wr}` is integrable on `(0, ∞)`. -/
theorem stRem_integrableOn_rpow_exp {m W : ℝ} (hm : -1 < m) (hW : 0 < W) :
    IntegrableOn (fun r : ℝ => r ^ m * Real.exp (-(W * r))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := m) (p := 1) hm one_pos hW
  refine this.congr_fun (fun r hr => ?_) measurableSet_Ioi
  simp [Real.rpow_one]

/-- **The χ-kernel bound along a ray.** If `cos β > 0` and `cos (θ + β) = 0`, then
`‖∫₀^∞ r^m e^{-Wr} / (X + r e^{iθ}) dr‖ ≤ Γ(m+1) ∫₀^∞ (W² + ρ²)^{-(m+1)/2} dρ`. -/
theorem stRem_chi_ray {m W X θ β : ℝ} (hm : 0 < m) (hW : 0 < W) (hX : 0 < X)
    (hβ : 0 < Real.cos β) (hσ : Real.cos (θ + β) = 0) :
    ‖∫ r in Ioi (0 : ℝ), (r : ℂ) ^ (m : ℂ) * Complex.exp (-(W * r)) / (X + r * exp (θ * I))‖ ≤
      Real.Gamma (m + 1) * ∫ ρ in Ioi (0 : ℝ), (W ^ 2 + ρ ^ 2) ^ (-(m + 1) / 2) := by
  set σ := θ + β with hσdef
  set c : ℝ → ℂ := fun r => (X + r * exp (θ * I)) * exp (β * I) with hc
  have hcre : ∀ r : ℝ, (c r).re = X * Real.cos β := by
    intro r
    have : c r = X * exp (β * I) + r * exp (σ * I) := by
      simp only [hc, hσdef, ofReal_add, add_mul, mul_assoc, ← Complex.exp_add]
    rw [this]
    simp [exp_ofReal_mul_I_re, hσ]
  have hcpos : ∀ r : ℝ, 0 < (c r).re := fun r => by rw [hcre]; positivity
  set f : ℝ → ℝ → ℂ := fun r ρ => (r : ℂ) ^ (m : ℂ) * Complex.exp (-(W * r)) *
    (exp (β * I) * Complex.exp (-(c r * ρ))) with hf
  -- pointwise representation
  have hpt : ∀ r : ℝ, (r : ℂ) ^ (m : ℂ) * Complex.exp (-(W * r)) / (X + r * exp (θ * I)) =
      ∫ ρ in Ioi (0 : ℝ), f r ρ := by
    intro r
    have hne : (X : ℂ) + r * exp (θ * I) ≠ 0 := by
      intro h; have := hcpos r; simp [hc, h] at this
    simp only [hf]
    rw [integral_const_mul, integral_const_mul, ← stRem_recip_eq_integral (hcpos r)]
    simp only [hc]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi (fun r _ => hpt r)]
  have hp : 0 < (m + 1) / 2 := by linarith
  -- integrability on the product
  have hint : Integrable (Function.uncurry f)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have h1 := stRem_integrableOn_rpow_exp (m := m) (by linarith) hW
    have h2 : IntegrableOn (fun ρ : ℝ => Real.exp (-(X * Real.cos β) * ρ)) (Ioi 0) :=
      exp_neg_integrableOn_Ioi 0 (by positivity)
    refine (h1.mul_prod h2).mono' ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      simp only [hf, hc, Function.uncurry_def]
      have h3 : Continuous fun p : ℝ × ℝ => ((p.1 : ℂ)) ^ (m : ℂ) :=
        (continuous_ofReal_cpow_const (y := (m : ℂ)) (by simpa using hm)).comp continuous_fst
      fun_prop
    · rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioi)]
      refine Filter.Eventually.of_forall fun q hq => ?_
      obtain ⟨hr, hρ⟩ := hq
      have hr : (0 : ℝ) < q.1 := hr
      simp only [hf, Function.uncurry_def, norm_mul, norm_cpow_eq_rpow_re_of_pos hr, ofReal_re,
        norm_exp_ofReal_mul_I, one_mul]
      simp only [Complex.norm_exp]
      have e1 : (-((W : ℂ) * q.1)).re = -(W * q.1) := by simp
      have e2 : (-(c q.1 * q.2)).re = -(X * Real.cos β) * q.2 := by
        rw [neg_re, show c q.1 * q.2 = c q.1 * ((q.2 : ℝ) : ℂ) by rfl, mul_re, ofReal_re,
          ofReal_im, mul_zero, sub_zero, hcre]; ring
      rw [e1, e2]
  rw [integral_integral_swap hint]
  have hinner : ∀ ρ : ℝ, ∫ r in Ioi (0 : ℝ), f r ρ =
      exp (β * I) * Complex.exp (-(X * exp (β * I) * ρ)) *
        (Complex.Gamma ((m : ℂ) + 1) * ((W : ℂ) + ρ * exp (σ * I)) ^ (-((m : ℂ) + 1))) := by
    intro ρ
    have hz : 0 < ((W : ℂ) + ρ * exp (σ * I)).re := by
      simp [exp_ofReal_mul_I_re, hσ, hW]
    have hG := integral_cpow_mul_cexp_neg_mul_Ioi (s := (m : ℂ) + 1) (z := (W : ℂ) + ρ * exp (σ * I))
      (by simp; linarith) hz
    rw [show (m : ℂ) + 1 - 1 = m by ring] at hG
    rw [← hG, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    simp only [hf, hc]
    have : Complex.exp (-(W * r)) * Complex.exp (-((X + r * exp (θ * I)) * exp (β * I) * ρ)) =
        Complex.exp (-(X * exp (β * I) * ρ)) * Complex.exp (-(((W : ℂ) + ρ * exp (σ * I)) * r)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1
      simp only [hσdef, ofReal_add, add_mul, Complex.exp_add]; ring
    linear_combination ((r : ℂ) ^ (m : ℂ) * exp (β * I)) * this
  simp_rw [hinner]
  have hgi : IntegrableOn (fun ρ : ℝ => (W ^ 2 + ρ ^ 2) ^ (-(m + 1) / 2)) (Ioi 0) := by
    have h := (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := m + 1)
      (by simp; linarith)).integrableOn (s := Ioi (0 : ℝ))
    set K := (min (W ^ 2) 1) ^ (-(m + 1) / 2)
    refine (h.const_mul K).mono' ?_ ?_
    · exact (by fun_prop : Measurable fun ρ : ℝ => (W ^ 2 + ρ ^ 2) ^ (-(m + 1) / 2)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ρ => ?_
      have hk : 0 < min (W ^ 2) 1 := lt_min (by positivity) one_pos
      have hle : min (W ^ 2) 1 * (1 + ‖ρ‖ ^ 2) ≤ W ^ 2 + ρ ^ 2 := by
        rw [Real.norm_eq_abs, sq_abs]
        have := min_le_left (W ^ 2) 1; have := min_le_right (W ^ 2) 1
        nlinarith [sq_nonneg ρ]
      rw [Real.norm_of_nonneg (by positivity)]
      calc (W ^ 2 + ρ ^ 2) ^ (-(m + 1) / 2) ≤ (min (W ^ 2) 1 * (1 + ‖ρ‖ ^ 2)) ^ (-(m + 1) / 2) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith)
        _ = K * (1 + ‖ρ‖ ^ 2) ^ (-(m + 1) / 2) := by
            rw [Real.mul_rpow hk.le (by positivity)]
        _ = _ := by ring_nf
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hgi.const_mul _) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun ρ hρ => ?_)
  have hρ : (0 : ℝ) < ρ := hρ
  rw [norm_mul, norm_mul, norm_mul, norm_exp_ofReal_mul_I, one_mul, Complex.norm_exp,
    show ((m : ℂ) + 1) = ((m + 1 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal,
    Complex.norm_real, Real.norm_of_nonneg (Real.Gamma_pos_of_pos (by linarith)).le,
    show (-(((m + 1 : ℝ)) : ℂ)) = ((-(m + 1) : ℝ) : ℂ) by push_cast; ring, norm_cpow_real,
    stRem_norm_add_exp hσ]
  have hexp : Real.exp (-((X : ℂ) * exp (β * I) * ρ)).re ≤ 1 := by
    rw [Real.exp_le_one_iff]
    simp [exp_ofReal_mul_I_re]
    positivity
  have hsq : Real.sqrt (W ^ 2 + ρ ^ 2) ^ (-(m + 1)) = (W ^ 2 + ρ ^ 2) ^ (-(m + 1) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]; ring_nf
  rw [hsq]
  have h0 : 0 ≤ Real.Gamma (m + 1) * (W ^ 2 + ρ ^ 2) ^ (-(m + 1) / 2) :=
    mul_nonneg (Real.Gamma_pos_of_pos (by linarith)).le (by positivity)
  calc Real.exp (-((X : ℂ) * exp (β * I) * ρ)).re *
        (Real.Gamma (m + 1) * (W ^ 2 + ρ ^ 2) ^ (-(m + 1) / 2))
      ≤ 1 * (Real.Gamma (m + 1) * (W ^ 2 + ρ ^ 2) ^ (-(m + 1) / 2)) :=
        mul_le_mul_of_nonneg_right hexp h0
    _ = _ := one_mul _

/-- **χ-bound for a Stieltjes mixture along a ray.** -/
theorem stRem_mix_chi {m W θ β : ℝ} (hm : 0 < m) (hW : 0 < W) (hβ : 0 < Real.cos β)
    (hσ : Real.cos (θ + β) = 0) (hsin : Real.sin θ ≠ 0) {g : ℝ → ℝ}
    (hg0 : ∀ τ ∈ Ioo (0 : ℝ) 1, 0 ≤ g τ) (hgi' : IntegrableOn g (Ioo 0 1))
    (hgi : IntegrableOn (fun τ => g τ / τ) (Ioo 0 1)) :
    ‖∫ r in Ioi (0 : ℝ), (r : ℂ) ^ (m : ℂ) * Complex.exp (-(W * r)) *
        ∫ τ in Ioo (0 : ℝ) 1, (g τ : ℂ) / (1 + τ * (r * exp (θ * I)))‖ ≤
      Real.Gamma (m + 1) * (∫ ρ in Ioi (0 : ℝ), (W ^ 2 + ρ ^ 2) ^ (-(m + 1) / 2)) *
        ∫ τ in Ioo (0 : ℝ) 1, g τ / τ := by
  have hs : 0 < |Real.sin θ| := abs_pos.mpr hsin
  have hden : ∀ x : ℝ, |Real.sin θ| ≤ ‖1 + (x : ℂ) * exp (θ * I)‖ := fun x =>
    Complex.abs_sin_le_norm_one_add_ofReal_mul_exp x θ
  set F : ℝ → ℝ → ℂ := fun r τ => (r : ℂ) ^ (m : ℂ) * Complex.exp (-(W * r)) *
    ((g τ : ℂ) / (1 + τ * (r * exp (θ * I)))) with hF
  have hpt : ∀ r : ℝ, (r : ℂ) ^ (m : ℂ) * Complex.exp (-(W * r)) *
      ∫ τ in Ioo (0 : ℝ) 1, (g τ : ℂ) / (1 + τ * (r * exp (θ * I))) =
        ∫ τ in Ioo (0 : ℝ) 1, F r τ := fun r => (integral_const_mul _ _).symm
  simp_rw [hpt]
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
    have h1 := stRem_integrableOn_rpow_exp (m := m) (by linarith) hW
    refine (h1.mul_prod (hgi'.div_const |Real.sin θ|)).mono' ?_ ?_
    · have hcont : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) ^ (m : ℂ) * Complex.exp (-(W * p.1)) *
          (1 + p.2 * (p.1 * exp (θ * I)))⁻¹ := by
        have h3 : Continuous fun p : ℝ × ℝ => ((p.1 : ℂ)) ^ (m : ℂ) :=
          (continuous_ofReal_cpow_const (y := (m : ℂ)) (by simpa using hm)).comp continuous_fst
        refine (h3.mul (by fun_prop)).mul (Continuous.inv₀ (by fun_prop) fun p => ?_)
        intro h0
        have := hden (p.2 * p.1)
        rw [show (1 : ℂ) + ((p.2 * p.1 : ℝ) : ℂ) * exp (θ * I) =
          1 + p.2 * (p.1 * exp (θ * I)) by push_cast; ring, h0, norm_zero] at this
        exact hs.not_ge this
      have hg2 : AEStronglyMeasurable (fun p : ℝ × ℝ => ((g p.2 : ℝ) : ℂ))
          ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (0 : ℝ) 1))) :=
        (Complex.continuous_ofReal.comp_aestronglyMeasurable hgi'.aestronglyMeasurable).comp_snd
      refine (hcont.aestronglyMeasurable.mul hg2).congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [hF, Function.uncurry_def, div_eq_mul_inv, Pi.mul_apply]; ring
    · rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioo)]
      refine Filter.Eventually.of_forall fun q hq => ?_
      obtain ⟨hr, hτ⟩ := hq
      have hr : (0 : ℝ) < q.1 := hr
      have hg := hg0 q.2 hτ
      simp only [hF, Function.uncurry_def, norm_mul, norm_div, norm_cpow_eq_rpow_re_of_pos hr,
        ofReal_re, Complex.norm_real, Real.norm_of_nonneg hg]
      simp only [Complex.norm_exp]
      have e1 : (-((W : ℂ) * q.1)).re = -(W * q.1) := by simp
      rw [e1]
      have hd := hden (q.2 * q.1)
      rw [show (1 : ℂ) + ((q.2 * q.1 : ℝ) : ℂ) * exp (θ * I) =
          1 + q.2 * (q.1 * exp (θ * I)) by push_cast; ring] at hd
      have hA : 0 ≤ q.1 ^ m * Real.exp (-(W * q.1)) := by positivity
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hg hs hd) hA
  rw [integral_integral_swap hint]
  set C := Real.Gamma (m + 1) * ∫ ρ in Ioi (0 : ℝ), (W ^ 2 + ρ ^ 2) ^ (-(m + 1) / 2)
  have hbound : ∀ τ ∈ Ioo (0 : ℝ) 1, ‖∫ r in Ioi (0 : ℝ), F r τ‖ ≤ g τ / τ * C := by
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := hτ.1
    have hτc : (τ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hτ0.ne'
    have heq : ∫ r in Ioi (0 : ℝ), F r τ = ((g τ / τ : ℝ) : ℂ) * ∫ r in Ioi (0 : ℝ),
        (r : ℂ) ^ (m : ℂ) * Complex.exp (-(W * r)) / (((1 / τ : ℝ) : ℂ) + r * exp (θ * I)) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
      simp only [hF]
      have h1 : (1 : ℂ) + τ * (r * exp (θ * I)) = τ * (((1 / τ : ℝ) : ℂ) + r * exp (θ * I)) := by
        push_cast; field_simp
      rw [h1]
      push_cast
      field_simp
    rw [heq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_nonneg (hg0 τ hτ) hτ0.le)]
    exact mul_le_mul_of_nonneg_left (stRem_chi_ray hm hW (by positivity) hβ hσ)
      (div_nonneg (hg0 τ hτ) hτ0.le)
  calc ‖∫ τ in Ioo (0 : ℝ) 1, ∫ r in Ioi (0 : ℝ), F r τ‖
      ≤ ∫ τ in Ioo (0 : ℝ) 1, g τ / τ * C :=
        norm_integral_le_of_norm_le (hgi.mul_const C)
          ((ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall hbound))
    _ = _ := by rw [integral_mul_const]; ring

end
