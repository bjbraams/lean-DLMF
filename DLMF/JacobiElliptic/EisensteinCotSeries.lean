/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.EisensteinSeries
public import Mathlib.Order.Filter.AtTopBot.Interval

/-!
# Eisenstein-type cotangent series for `cs`

The cotangent analogue of `DLMF.JacobiElliptic.EisensteinSeries`: the series
`∑ₙ εⁿ π cot(π(t - nτ))` (`ε = ±1`, `Im τ > 0`) converges in symmetric partial sums, and for
`ε = -1` it equals `2K cs(2Kt)`. This gives the four cotangent forms of DLMF §22.12, the
Fourier series of `cs`, `dn`, `sc`, `nd` (DLMF §22.11) and, for `ε = 1`, the cotangent and
cosecant-square series of the Weierstrass functions (DLMF 23.8.3–23.8.4).

## Main definitions

* `eisensteinCotTerm`: the regularized terms `εⁿ (π cot(π(t - nτ)) - iπ sgn n)`.
* `eisensteinCotSeries`: their (absolutely convergent) sum.

## Main results

* `eisensteinCotSeries_add_one`, `eisensteinCotSeries_add`, `eisensteinCotSeries_neg`: the
  period `1`, the quasi-period `τ` and the oddness.
* `tendsto_sum_Icc_neg_one_zpow_pi_mul_cot`: the symmetric partial sums of
  `∑ₙ εⁿ π cot(π(t - nτ))` tend to `eisensteinCotSeries ε τ t`.
* `eq_eisensteinCotSeries_of_quasiPeriodic`,
  `eq_eisensteinCotSeries_of_quasiPeriodic_off_lattice`: the Liouville identification of a
  meromorphic function with the same periods, oddness and principal parts.
* `jacobiCs_eq_eisensteinCotSeries`: `2K cs(2Kt) = ∑ₙ (-1)ⁿ π cot(π(t - nτ))` (regularized).
* `tendsto_sum_Icc_one_div_sub`: `∑_{|m| ≤ M} 1/(w - m) → π cot(πw)`.
* `hasSum_fourier_eisensteinCotSeries`, `hasSum_fourier_eisensteinCotSeries_sub_half`: the
  Fourier expansions of `C(t)` and `C(t - τ/2)` (used for DLMF 22.11.3, 22.11.9).
* `hasSum_pi_sq_div_sin_sq`: `∑ₙ εⁿ π²/sin²(π(t - nτ)) = -C'(t)` (used for DLMF 23.8.3).

## Implementation notes

Since `cot w → ∓i` as `Im w → ±∞`, the terms are regularized by `-iπ sgn n`; the corrections
cancel in symmetric partial sums. The regularized terms are bounded by the cosecant terms of
`eisensteinSinTerm`, because `cot w ∓ i = e^{∓iw}/sin w`. The identification with `cs` is the
same Liouville argument as for `ns` and `ds`, on the lattice `⟨2, 2τ⟩`.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace DLMF.JacobiElliptic

open DLMF.EllipticIntegrals (completeEllipticK completeEllipticKPrime)

/-- The regularized terms `εⁿ (π cot(π(t - nτ)) - iπ sgn n)` of the cotangent series. -/
def eisensteinCotTerm (ε τ : ℂ) (n : ℤ) (t : ℂ) : ℂ :=
  ε ^ n * (π * cot (π * (t - n * τ)) - I * π * (Int.sign n : ℂ))

/-- The regularized cotangent series `∑ₙ εⁿ (π cot(π(t - nτ)) - iπ sgn n)`. -/
def eisensteinCotSeries (ε τ t : ℂ) : ℂ := ∑' n : ℤ, eisensteinCotTerm ε τ n t

/-- The cotangent series without its `n = 0` term. -/
def eisensteinCotRegularPart (ε τ t : ℂ) : ℂ := ∑' n : ℤ, if n = 0 then 0 else
    eisensteinCotTerm ε τ n t

/-- `cot w - i = e^{-iw}/sin w`. -/
private lemma cot_sub_I {w : ℂ} (hw : sin w ≠ 0) : cot w - I = cexp (-(I * w)) / sin w := by
  rw [Complex.cot_eq_cos_div_sin, eq_div_iff hw, sub_mul, div_mul_cancel₀ _ hw,
    show -(I * w) = (-w) * I by ring, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  ring

/-- `cot w + i = e^{iw}/sin w`. -/
private lemma cot_add_I {w : ℂ} (hw : sin w ≠ 0) : cot w + I = cexp (I * w) / sin w := by
  rw [Complex.cot_eq_cos_div_sin, eq_div_iff hw, add_mul, div_mul_cancel₀ _ hw,
    show I * w = w * I by ring, Complex.exp_mul_I]
  ring

/-- On the strip, the regularized cotangent terms are bounded by the cosecant terms. -/
private lemma norm_eisensteinCotTerm_le {ε τ : ℂ} (hε : ε = 1 ∨ ε = -1) (hτ : 0 < τ.im)
    {n : ℤ} (hn : n ≠ 0) {t : ℂ} (ht : |t.im| ≤ 3 / 4 * τ.im) :
    ‖eisensteinCotTerm ε τ n t‖ ≤ π * (2 / (1 - Real.exp (-(2 * (π * τ.im / 4))))) *
      Real.exp (-(π * τ.im / 4)) ^ n.natAbs := by
  refine le_trans ?_ (norm_eisensteinSinTerm_le (ε := 1) (Or.inl rfl) hτ hn ht)
  have hsin := sin_pi_mul_sub_ne_zero_of_strip hτ hn ht
  set w := π * (t - n * τ) with hw
  have hwim : w.im = π * (t.im - n * τ.im) := by simp [hw]
  have habs := abs_le.mp ht
  have hpi := Real.pi_pos
  simp only [eisensteinCotTerm, eisensteinSinTerm, one_zpow, one_mul, ← hw]
  rw [norm_mul, norm_sign_zpow hε, one_mul]
  rcases lt_or_gt_of_ne hn with h | h
  · rw [Int.sign_eq_neg_one_of_neg h, show (π : ℂ) * cot w - I * π * ((-1 : ℤ) : ℂ) =
      π * (cot w + I) by push_cast; ring, cot_add_I hsin, norm_mul, norm_div, norm_div,
      Complex.norm_exp]
    have hre : (I * w).re = -w.im := by simp
    rw [hre]
    have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.mpr h
    have : 0 ≤ w.im := by
      rw [hwim]; exact mul_nonneg hpi.le (by nlinarith [habs.1, habs.2])
    have he : Real.exp (-w.im) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [mul_div_assoc']
    gcongr
    calc ‖(π : ℂ)‖ * Real.exp (-w.im) ≤ ‖(π : ℂ)‖ * 1 := by gcongr
      _ = ‖(π : ℂ)‖ := mul_one _
  · rw [Int.sign_eq_one_of_pos h, show (π : ℂ) * cot w - I * π * ((1 : ℤ) : ℂ) =
      π * (cot w - I) by push_cast; ring, cot_sub_I hsin, norm_mul, norm_div, norm_div,
      Complex.norm_exp]
    have hre : (-(I * w)).re = w.im := by simp
    rw [hre]
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast h
    have : w.im ≤ 0 := by
      rw [hwim]; exact mul_nonpos_of_nonneg_of_nonpos hpi.le (by nlinarith [habs.1, habs.2])
    have he : Real.exp w.im ≤ 1 := Real.exp_le_one_iff.mpr this
    rw [mul_div_assoc']
    gcongr
    calc ‖(π : ℂ)‖ * Real.exp w.im ≤ ‖(π : ℂ)‖ * 1 := by gcongr
      _ = ‖(π : ℂ)‖ := mul_one _

/-- Geometric bound for the regularized terms with `n ≠ 0` on the strip. -/
private lemma norm_ite_eisensteinCotTerm_le {ε τ : ℂ} (hε : ε = 1 ∨ ε = -1) (hτ : 0 < τ.im)
    (n : ℤ) {t : ℂ} (ht : |t.im| ≤ 3 / 4 * τ.im) :
    ‖(if n = 0 then 0 else eisensteinCotTerm ε τ n t)‖ ≤ π *
        (2 / (1 - Real.exp (-(2 * (π * τ.im / 4))))) *
      Real.exp (-(π * τ.im / 4)) ^ n.natAbs := by
  split_ifs with hn
  · rw [norm_zero]
    have : Real.exp (-(2 * (π * τ.im / 4))) < 1 := by
      have := Real.exp_lt_exp.mpr (show -(2 * (π * τ.im / 4)) < 0 by
        have := Real.pi_pos; nlinarith); simpa using this
    have : 0 < 1 - Real.exp (-(2 * (π * τ.im / 4))) := by linarith
    have := (exp_neg_pi_im_div_four_mem_Ico hτ).1
    positivity
  · exact norm_eisensteinCotTerm_le hε hτ hn ht

/-- The regularized terms with `n ≠ 0` are summable on the strip. -/
private lemma summable_eisensteinCotTerm_ne_zero {ε τ : ℂ} (hε : ε = 1 ∨ ε = -1)
    (hτ : 0 < τ.im) {t : ℂ} (ht : |t.im| ≤ 3 / 4 * τ.im) :
    Summable fun n : ℤ => if n = 0 then 0 else eisensteinCotTerm ε τ n t :=
  Summable.of_norm_bounded
      (((summable_pow_natAbs (exp_neg_pi_im_div_four_mem_Ico hτ).1
      (exp_neg_pi_im_div_four_mem_Ico hτ).2).mul_left _))
    fun n => norm_ite_eisensteinCotTerm_le hε hτ n ht

/-- On the strip the series is `π cot(πt)` plus the regular part. -/
private lemma hasSum_eisensteinCotTerm_of_strip {ε τ : ℂ} (hε : ε = 1 ∨ ε = -1)
    (hτ : 0 < τ.im) {t : ℂ} (ht : |t.im| ≤ 3 / 4 * τ.im) :
    HasSum (fun n => eisensteinCotTerm ε τ n t)
        (π * cot (π * t) + eisensteinCotRegularPart ε τ t) := by
  have h1 := (summable_eisensteinCotTerm_ne_zero hε hτ ht).hasSum
  have h2 := hasSum_ite_eq (0 : ℤ) (eisensteinCotTerm ε τ 0 t)
  have := h2.add h1
  convert this using 1
  · funext n; split_ifs with hn <;> simp [hn]
  · simp [eisensteinCotTerm, eisensteinCotRegularPart]

/-- The correction produced by shifting `t` by `jτ`. -/
private def cotShiftCorrection (ε : ℂ) (j n : ℤ) : ℂ :=
  ε ^ n * (I * π * ((Int.sign (n - j) : ℂ) - (Int.sign n : ℂ)))

/-- Shifting `t` by `jτ` reindexes the regularized terms up to a correction. -/
private lemma eisensteinCotTerm_add_intCast_mul (ε τ : ℂ) (hε : ε ≠ 0) (n j : ℤ) (t : ℂ) :
    eisensteinCotTerm ε τ n (t + j * τ) =
      ε ^ j * eisensteinCotTerm ε τ (n - j) t + cotShiftCorrection ε j n := by
  simp only [eisensteinCotTerm, cotShiftCorrection]
  rw [show t + j * τ - n * τ = t - ((n - j : ℤ) : ℂ) * τ by push_cast; ring,
    show ε ^ n = ε ^ j * ε ^ (n - j) by rw [← zpow_add₀ hε]; ring_nf]
  ring

/-- The correction vanishes outside `[-|j|, |j|]`. -/
private lemma cotShiftCorrection_eq_zero (ε : ℂ) (j n : ℤ)
    (hn : n ∉ Finset.Icc (-|j|) |j|) : cotShiftCorrection ε j n = 0 := by
  have h1 := le_abs_self j
  have h2 := neg_abs_le j
  simp only [Finset.mem_Icc, not_and_or, not_le] at hn
  have : Int.sign (n - j) = Int.sign n := by
    rcases hn with hn | hn
    · rw [Int.sign_eq_neg_one_of_neg (by omega), Int.sign_eq_neg_one_of_neg (by omega)]
    · rw [Int.sign_eq_one_of_pos (by omega), Int.sign_eq_one_of_pos (by omega)]
  simp [cotShiftCorrection, this]

/-- The correction is summable. -/
private lemma summable_cotShiftCorrection (ε : ℂ) (j : ℤ) :
    Summable (cotShiftCorrection ε j) :=
  summable_of_ne_finset_zero (s := Finset.Icc (-|j|) |j|) fun n hn =>
    cotShiftCorrection_eq_zero ε j n hn

/-- The regularized series converges for every `t`. -/
lemma summable_eisensteinCotTerm {ε τ : ℂ} (hε : ε = 1 ∨ ε = -1) (hτ : 0 < τ.im) (t : ℂ) :
    Summable fun n => eisensteinCotTerm ε τ n t := by
  obtain ⟨j, hj⟩ := exists_abs_im_sub_intCast_mul_le hτ t
  have hs := (hasSum_eisensteinCotTerm_of_strip hε hτ (t := t - j * τ) (by linarith)).summable
  have e : ∀ n, eisensteinCotTerm ε τ n t =
      ε ^ j * eisensteinCotTerm ε τ (n - j) (t - j * τ) + cotShiftCorrection ε j n := by
    intro n
    rw [← eisensteinCotTerm_add_intCast_mul ε τ (sign_ne_zero_of_eq_one_or_eq_neg_one hε),
        sub_add_cancel]
  simp_rw [e]
  exact (((Equiv.subRight j).summable_iff.mpr hs).mul_left _).add
    (summable_cotShiftCorrection ε j)

/-- `C(t + jτ) = εʲ C(t) + c_j` with a constant `c_j`. -/
private lemma eisensteinCotSeries_add_intCast_mul {ε τ : ℂ} (hε : ε = 1 ∨ ε = -1)
    (hτ : 0 < τ.im) (j : ℤ) (t : ℂ) :
    eisensteinCotSeries ε τ (t + j * τ) =
      ε ^ j * eisensteinCotSeries ε τ t + ∑' n, cotShiftCorrection ε j n := by
  have hε0 := sign_ne_zero_of_eq_one_or_eq_neg_one hε
  simp only [eisensteinCotSeries, eisensteinCotTerm_add_intCast_mul ε τ hε0]
  have hs : Summable fun n => ε ^ j * eisensteinCotTerm ε τ (n - j) t :=
    ((Equiv.subRight j).summable_iff.mpr (summable_eisensteinCotTerm hε hτ t)).mul_left _
  rw [Summable.tsum_add hs (summable_cotShiftCorrection ε j), tsum_mul_left]
  congr 2
  exact (Equiv.subRight j).tsum_eq fun n => eisensteinCotTerm ε τ n t

/-- The shift constant for `j = 1`. -/
private lemma tsum_cotShiftCorrection_one (ε : ℂ) :
    ∑' n, cotShiftCorrection ε 1 n = -(I * π * (1 + ε)) := by
  rw [tsum_eq_sum (s := {0, 1}) fun n hn => ?_]
  · rw [Finset.sum_pair (by norm_num)]
    simp [cotShiftCorrection]
    ring
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    have : Int.sign (n - 1) = Int.sign n := by
      rcases lt_or_gt_of_ne hn.1 with h | h
      · rw [Int.sign_eq_neg_one_of_neg (by omega), Int.sign_eq_neg_one_of_neg h]
      · rw [Int.sign_eq_one_of_pos (by omega), Int.sign_eq_one_of_pos h]
    simp [cotShiftCorrection, this]

/-- DLMF §22.12: `C(t + τ) = ε C(t) - iπ(1 + ε)`. -/
theorem eisensteinCotSeries_add {ε τ : ℂ} (hε : ε = 1 ∨ ε = -1) (hτ : 0 < τ.im) (t : ℂ) :
    eisensteinCotSeries ε τ (t + τ) = ε * eisensteinCotSeries ε τ t - I * π * (1 + ε) := by
  have := eisensteinCotSeries_add_intCast_mul hε hτ 1 t
  rw [Int.cast_one, one_mul, zpow_one, tsum_cotShiftCorrection_one] at this
  rw [this]; ring

/-- `cot` has period `π`. -/
private lemma cot_add_pi (w : ℂ) : cot (w + π) = cot w := by
  rw [Complex.cot_eq_cos_div_sin, Complex.cot_eq_cos_div_sin, Complex.cos_add_pi,
    Complex.sin_add_pi, neg_div_neg_eq]

/-- `cot` is odd. -/
private lemma cot_neg' (w : ℂ) : cot (-w) = -cot w := by
  rw [Complex.cot_eq_cos_div_sin, Complex.cot_eq_cos_div_sin, Complex.cos_neg,
    Complex.sin_neg, div_neg]

/-- `C(t + 1) = C(t)`. -/
theorem eisensteinCotSeries_add_one (ε τ t : ℂ) :
    eisensteinCotSeries ε τ (t + 1) = eisensteinCotSeries ε τ t := by
  simp only [eisensteinCotSeries, eisensteinCotTerm]
  congr 1; funext n
  rw [show (π : ℂ) * (t + 1 - n * τ) = π * (t - n * τ) + π by ring, cot_add_pi]

/-- `C` is odd. -/
theorem eisensteinCotSeries_neg {ε : ℂ} (hε : ε = 1 ∨ ε = -1) (τ t : ℂ) :
    eisensteinCotSeries ε τ (-t) = -eisensteinCotSeries ε τ t := by
  have e : ∀ n, eisensteinCotTerm ε τ n (-t) = -eisensteinCotTerm ε τ (-n) t := by
    intro n
    simp only [eisensteinCotTerm, sign_zpow_neg hε, Int.sign_neg]
    rw [show (π : ℂ) * (-t - n * τ) = -(π * (t - ((-n : ℤ) : ℂ) * τ)) by push_cast; ring,
      cot_neg']
    push_cast; ring
  simp only [eisensteinCotSeries, e, tsum_neg]
  congr 1
  exact (Equiv.neg ℤ).tsum_eq fun n => eisensteinCotTerm ε τ n t

/-- The regular part is holomorphic on the strip. -/
private lemma differentiableOn_eisensteinCotRegularPart {ε τ : ℂ} (hε : ε = 1 ∨ ε = -1)
    (hτ : 0 < τ.im) :
    DifferentiableOn ℂ (eisensteinCotRegularPart ε τ) (eisensteinSinStrip τ) := by
  refine differentiableOn_tsum_of_summable_norm
    ((summable_pow_natAbs (exp_neg_pi_im_div_four_mem_Ico hτ).1
        (exp_neg_pi_im_div_four_mem_Ico hτ).2).mul_left _) (fun n => ?_)
    (isOpen_eisensteinSinStrip τ)
        (fun n w hw => norm_ite_eisensteinCotTerm_le hε hτ n (le_of_lt hw))
  by_cases hn : n = 0
  · simp only [hn, ite_true]; exact differentiableOn_const _
  · simp only [hn, ite_false, eisensteinCotTerm, Complex.cot_eq_cos_div_sin]
    refine DifferentiableOn.mul (differentiableOn_const _) (DifferentiableOn.sub
      (DifferentiableOn.mul (differentiableOn_const _) (DifferentiableOn.div (by fun_prop)
        (by fun_prop) fun w hw => ?_)) (differentiableOn_const _))
    exact sin_pi_mul_sub_ne_zero_of_strip hτ hn (le_of_lt hw)

/-- The regular part is analytic at the points of the strip. -/
private lemma analyticAt_eisensteinCotRegularPart {ε τ : ℂ} (hε : ε = 1 ∨ ε = -1)
    (hτ : 0 < τ.im) {t : ℂ} (ht : |t.im| < 3 / 4 * τ.im) :
    AnalyticAt ℂ (eisensteinCotRegularPart ε τ) t :=
  (differentiableOn_eisensteinCotRegularPart hε hτ).analyticAt
    ((isOpen_eisensteinSinStrip τ).mem_nhds ht)

/-- Local form of the series near a point, after translating into the strip. -/
private lemma eisensteinCotSeries_eventuallyEq_translate {ε τ : ℂ} (hε : ε = 1 ∨ ε = -1)
    (hτ : 0 < τ.im) (t₀ : ℂ) :
    ∃ j : ℤ, ∃ c : ℂ, |(t₀ - j * τ).im| ≤ 1 / 2 * τ.im ∧ eisensteinCotSeries ε τ =ᶠ[𝓝 t₀]
      fun s => ε ^ j * (π * cot (π * (s - j * τ)) +
        eisensteinCotRegularPart ε τ (s - j * τ)) + c := by
  obtain ⟨j, hj⟩ := exists_abs_im_sub_intCast_mul_le hτ t₀
  refine ⟨j, ∑' n, cotShiftCorrection ε j n, hj, ?_⟩
  have hU : (fun s => s - j * τ) ⁻¹' eisensteinSinStrip τ ∈ 𝓝 t₀ := by
    refine (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
      ((isOpen_eisensteinSinStrip τ).mem_nhds ?_)
    show |(t₀ - j * τ).im| < 3 / 4 * τ.im
    linarith
  filter_upwards [hU] with s hs
  have e := eisensteinCotSeries_add_intCast_mul (τ := τ) hε hτ j (s - j * τ)
  rw [sub_add_cancel] at e
  rw [e, eisensteinCotSeries,
      (hasSum_eisensteinCotTerm_of_strip hε hτ (t := s - j * τ) (le_of_lt hs)).tsum_eq]

/-- The function `s ↦ π cot(π(s - a))` is meromorphic. -/
private lemma meromorphicAt_pi_mul_cot (a t₀ : ℂ) :
    MeromorphicAt (fun s => (π : ℂ) * cot (π * (s - a))) t₀ := by
  simp only [Complex.cot_eq_cos_div_sin]
  exact (MeromorphicAt.const _ _).mul ((by fun_prop : AnalyticAt ℂ (fun s =>
    cos (π * (s - a))) t₀).meromorphicAt.div (by fun_prop : AnalyticAt ℂ (fun s =>
    sin (π * (s - a))) t₀).meromorphicAt)

/-- `C` is meromorphic. -/
private lemma meromorphicAt_eisensteinCotSeries {ε τ : ℂ} (hε : ε = 1 ∨ ε = -1)
    (hτ : 0 < τ.im) (t₀ : ℂ) :
    MeromorphicAt (eisensteinCotSeries ε τ) t₀ := by
  obtain ⟨j, c, hj, he⟩ := eisensteinCotSeries_eventuallyEq_translate hε hτ t₀
  have hR : AnalyticAt ℂ (fun s => eisensteinCotRegularPart ε τ (s - j * τ)) t₀ :=
    (analyticAt_eisensteinCotRegularPart hε hτ (t := t₀ - j * τ) (by linarith)).comp_of_eq
      (by fun_prop) rfl
  have hm : MeromorphicAt (fun s => ε ^ j * (π * cot (π * (s - j * τ)) +
      eisensteinCotRegularPart ε τ (s - j * τ)) + c) t₀ :=
    ((MeromorphicAt.const _ _).mul ((meromorphicAt_pi_mul_cot _ t₀).add
      hR.meromorphicAt)).add (MeromorphicAt.const _ _)
  exact hm.congr (he.symm.filter_mono nhdsWithin_le_nhds)

/-- `C` is analytic off the lattice. -/
private lemma analyticAt_eisensteinCotSeries {ε τ : ℂ} (hε : ε = 1 ∨ ε = -1)
    (hτ : 0 < τ.im) {t₀ : ℂ} (ht : t₀ ∉ eisensteinSinLattice τ) :
    AnalyticAt ℂ (eisensteinCotSeries ε τ) t₀ := by
  obtain ⟨j, c, hj, he⟩ := eisensteinCotSeries_eventuallyEq_translate hε hτ t₀
  have hR : AnalyticAt ℂ (fun s => eisensteinCotRegularPart ε τ (s - j * τ)) t₀ :=
    (analyticAt_eisensteinCotRegularPart hε hτ (t := t₀ - j * τ) (by linarith)).comp_of_eq
      (by fun_prop) rfl
  have hsin : sin (π * (t₀ - j * τ)) ≠ 0 := by
    intro h0
    obtain ⟨m, hm⟩ := Complex.sin_eq_zero_iff.mp h0
    apply ht
    refine ⟨m, j, ?_⟩
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have : t₀ - j * τ = m := by
      apply mul_left_cancel₀ hpi; rw [hm]; ring
    linear_combination this
  have hm : AnalyticAt ℂ (fun s => ε ^ j * (π * cot (π * (s - j * τ)) +
      eisensteinCotRegularPart ε τ (s - j * τ)) + c) t₀ := by
    refine (analyticAt_const.mul (AnalyticAt.add ?_ hR)).add analyticAt_const
    simp only [Complex.cot_eq_cos_div_sin]
    exact analyticAt_const.mul ((by fun_prop : AnalyticAt ℂ (fun s =>
      cos (π * (s - j * τ))) t₀).div (by fun_prop) hsin)
  exact hm.congr he.symm

/-- Liouville core for the cotangent series: a meromorphic function with the same periods,
oddness, poles and principal part at `0` as `eisensteinCotSeries ε τ` equals it off the
lattice. -/
theorem eq_eisensteinCotSeries_of_quasiPeriodic {ε τ : ℂ} (hε : ε = 1 ∨ ε = -1)
    (hτ : 0 < τ.im) {f : ℂ → ℂ} (hf : ∀ t, MeromorphicAt f t) (hf1 : ∀ t, f (t + 1) = f t)
    (hfτ : ∀ t, f (t + τ) = ε * f t - I * π * (1 + ε))
    (hfodd : ∀ t, f (-t) = -f t) (hfan : ∀ t ∉ eisensteinSinLattice τ, AnalyticAt ℂ f t)
    (hf0 : ∃ A : ℂ → ℂ, AnalyticAt ℂ A 0 ∧
      (fun t => f t - π * cot (π * t)) =ᶠ[𝓝[≠] 0] A) :
    ∀ t ∉ eisensteinSinLattice τ, f t = eisensteinCotSeries ε τ t := by
  set H := fun t => f t - eisensteinCotSeries ε τ t with hH
  have hε0 := sign_ne_zero_of_eq_one_or_eq_neg_one hε
  have hHm : Meromorphic H := fun t =>
    (hf t).sub (meromorphicAt_eisensteinCotSeries hε hτ t)
  have hH1 : ∀ t, H (t + 1) = 1 * H t := by
    intro t; simp only [hH, hf1, eisensteinCotSeries_add_one]; ring
  have hHτ : ∀ t, H (t + τ) = ε * H t := by
    intro t
    simp only [hH, hfτ, eisensteinCotSeries_add hε hτ]; ring
  have hHmn : ∀ (m n : ℤ) t, H (t + (m + n * τ)) = ε ^ n * H t := by
    intro m n t
    rw [← add_assoc, add_intCast_mul_eq_zpow_mul_of_quasiPeriodic hε0 hHτ n, show (t + (m : ℂ)) =
        t + m * 1 by ring,
      add_intCast_mul_eq_zpow_mul_of_quasiPeriodic (by norm_num) hH1 m]
    simp
  -- the lattice `⟨2, 2τ⟩`
  have hind : LinearIndependent ℝ ![(2 : ℂ), 2 * τ] := by
    refine LinearIndependent.pair_iff.mpr fun s u h => ?_
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    simp at him hre
    have hu : u = 0 := by
      rcases him with h | h
      · exact h
      · exact absurd h hτ.ne'
    subst hu
    simp at hre
    exact ⟨hre, rfl⟩
  let L : PeriodPair := ⟨2, 2 * τ, hind⟩
  have hper : ∀ z, ∀ l ∈ L.lattice, H (z + l) = H z := by
    intro z l hl
    obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hl
    have := hHmn (2 * m) (2 * n) z
    simp only [L] at this ⊢
    rw [show (m : ℂ) * 2 + n * (2 * τ) = ((2 * m : ℤ) : ℂ) + ((2 * n : ℤ) : ℂ) * τ by
      push_cast; ring, this]
    rw [zpow_mul]
    rcases hε with rfl | rfl <;> norm_num
  -- orders
  have hord0 : 0 ≤ meromorphicOrderAt H 0 := by
    obtain ⟨A, hA, hfA⟩ := hf0
    have h0 : |(0 : ℂ).im| < 3 / 4 * τ.im := by simp; linarith
    have hR := analyticAt_eisensteinCotRegularPart hε hτ h0
    have hG0 : eisensteinCotSeries ε τ =ᶠ[𝓝 0] fun s => π * cot (π * s) +
        eisensteinCotRegularPart ε τ s := by
      have hU : eisensteinSinStrip τ ∈ 𝓝 (0 : ℂ) := (isOpen_eisensteinSinStrip τ).mem_nhds h0
      filter_upwards [hU] with s hs
      exact (hasSum_eisensteinCotTerm_of_strip hε hτ (le_of_lt hs)).tsum_eq
    have hev : H =ᶠ[𝓝[≠] 0] fun s => A s - eisensteinCotRegularPart ε τ s := by
      filter_upwards [hfA, nhdsWithin_le_nhds hG0] with s h1 h2
      simp only [hH, h2]
      rw [← h1]; ring
    rw [meromorphicOrderAt_congr hev]
    exact (hA.sub hR).meromorphicOrderAt_nonneg
  have hord : ∀ x, 0 ≤ meromorphicOrderAt H x := by
    intro x
    by_cases hx : x ∈ eisensteinSinLattice τ
    · obtain ⟨m, n, rfl⟩ := hx
      have e : H ∘ (· + ((m : ℂ) + n * τ)) = (ε ^ n) • H := by
        funext t; simp [hHmn]
      have h1 := meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt (x := (0 : ℂ))
        (c := (m : ℂ) + n * τ) (f := H)
      rw [zero_add, e, meromorphicOrderAt_const_smul_eq_meromorphicOrderAt
        (zpow_ne_zero _ hε0)] at h1
      rw [← h1]; exact hord0
    · exact ((hfan x hx).sub (analyticAt_eisensteinCotSeries hε hτ hx)).meromorphicOrderAt_nonneg
  obtain ⟨c, hc⟩ := DLMF.Weierstrass.exists_eq_const_of_periodic_of_order_nonneg L hHm hper hord
  have hhalf : ∀ s : ℂ, s = 1 / 2 ∨ s = -(1 / 2) → s ∉ eisensteinSinLattice τ := by
    rintro s hs ⟨m, n, hmn⟩
    have him := congrArg Complex.im hmn
    have hre := congrArg Complex.re hmn
    rcases hs with rfl | rfl <;> simp at him hre
    all_goals
      rcases him with h | h
      · subst h; simp at hre
        have h2 : (2 * m : ℝ) = 1 ∨ (2 * m : ℝ) = -1 := by
          first | (left; linarith) | (right; linarith)
        rcases h2 with h2 | h2
        · have : (2 * m : ℤ) = 1 := by exact_mod_cast h2
          omega
        · have : (2 * m : ℤ) = -1 := by exact_mod_cast h2
          omega
      · exact absurd h hτ.ne'
  have hp := hhalf (1 / 2) (Or.inl rfl)
  have hn := hhalf (-(1 / 2)) (Or.inr rfl)
  have hHodd : H (-(1 / 2)) = -H (1 / 2) := by
    simp only [hH, hfodd, eisensteinCotSeries_neg hε]; ring
  have hc0 : c = 0 := by
    have e1 := hc _ ((hfan _ hp).sub (analyticAt_eisensteinCotSeries hε hτ hp))
    have e2 := hc _ ((hfan _ hn).sub (analyticAt_eisensteinCotSeries hε hτ hn))
    rw [hHodd, e1] at e2
    linear_combination -e2 / 2
  intro t ht
  have := hc t ((hfan t ht).sub (analyticAt_eisensteinCotSeries hε hτ ht))
  rw [hc0] at this
  exact sub_eq_zero.mp this

/-- The lattice `m + nτ` as the lattice of the period pair `⟨1, τ⟩`. -/
private lemma exists_periodPair_lattice_eq {τ : ℂ} (hτ : 0 < τ.im) :
    ∃ L : PeriodPair, ∀ t, t ∈ L.lattice ↔ t ∈ eisensteinSinLattice τ := by
  have hind : LinearIndependent ℝ ![(1 : ℂ), τ] := by
    refine LinearIndependent.pair_iff.mpr fun s u h => ?_
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    simp at him hre
    have hu : u = 0 := by
      rcases him with h | h
      · exact h
      · exact absurd h hτ.ne'
    subst hu
    simp at hre
    exact ⟨hre, rfl⟩
  refine ⟨⟨1, τ, hind⟩, fun t => ?_⟩
  rw [PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, h⟩; exact ⟨m, n, by rw [← h]; simp⟩
  · rintro ⟨m, n, h⟩; exact ⟨m, n, by rw [h]; simp⟩

/-- Liouville identification with the functional equations required only off the lattice
(the values at the poles are irrelevant). -/
theorem eq_eisensteinCotSeries_of_quasiPeriodic_off_lattice {ε τ : ℂ} (hε : ε = 1 ∨ ε = -1)
    (hτ : 0 < τ.im) {f : ℂ → ℂ} (hf : ∀ t, MeromorphicAt f t)
    (hf1 : ∀ t ∉ eisensteinSinLattice τ, f (t + 1) = f t)
    (hfτ : ∀ t ∉ eisensteinSinLattice τ, f (t + τ) = ε * f t - I * π * (1 + ε))
    (hfodd : ∀ t ∉ eisensteinSinLattice τ, f (-t) = -f t)
    (hfan : ∀ t ∉ eisensteinSinLattice τ, AnalyticAt ℂ f t)
    (hf0 : ∃ A : ℂ → ℂ, AnalyticAt ℂ A 0 ∧
      (fun t => f t - π * cot (π * t)) =ᶠ[𝓝[≠] 0] A) :
    ∀ t ∉ eisensteinSinLattice τ, f t = eisensteinCotSeries ε τ t := by
  classical
  obtain ⟨L, hL⟩ := exists_periodPair_lattice_eq hτ
  set Λ := eisensteinSinLattice τ
  have hev : ∀ a : ℂ, ∀ᶠ w in 𝓝[≠] a, w ∉ Λ := by
    intro a
    have hU : IsOpen ((L.lattice : Set ℂ) \ {a})ᶜ := L.isOpen_compl_lattice_sdiff
    have ha : a ∈ ((L.lattice : Set ℂ) \ {a})ᶜ := by simp
    filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds ha), self_mem_nhdsWithin] with w hw hwa
    intro hwL; exact hw ⟨(hL w).mpr hwL, hwa⟩
  have hopen : IsOpen Λᶜ := by
    have : Λᶜ = ((L.lattice : Set ℂ))ᶜ := by
      ext w; simp only [Set.mem_compl_iff, SetLike.mem_coe, hL w, Λ]
    rw [this]; exact L.isClosed_lattice.isOpen_compl
  have hΛ1 : ∀ t, t + 1 ∈ Λ ↔ t ∈ Λ := by
    intro t; constructor
    · rintro ⟨m, n, h⟩; exact ⟨m - 1, n, by push_cast; linear_combination h⟩
    · rintro ⟨m, n, h⟩; exact ⟨m + 1, n, by push_cast; linear_combination h⟩
  have hΛτ : ∀ t, t + τ ∈ Λ ↔ t ∈ Λ := by
    intro t; constructor
    · rintro ⟨m, n, h⟩; exact ⟨m, n - 1, by push_cast; linear_combination h⟩
    · rintro ⟨m, n, h⟩; exact ⟨m, n + 1, by push_cast; linear_combination h⟩
  have hΛneg : ∀ t, -t ∈ Λ ↔ t ∈ Λ := by
    intro t; constructor
    · rintro ⟨m, n, h⟩; exact ⟨-m, -n, by push_cast; linear_combination -h⟩
    · rintro ⟨m, n, h⟩; exact ⟨-m, -n, by push_cast; linear_combination -h⟩
  set g : ℂ → ℂ := fun t => if t ∈ Λ then eisensteinCotSeries ε τ t else f t with hg
  have hgf : ∀ a, g =ᶠ[𝓝[≠] a] f := by
    intro a
    filter_upwards [hev a] with w hw
    simp [hg, hw]
  have key := eq_eisensteinCotSeries_of_quasiPeriodic hε hτ (f := g)
    (fun t => (hf t).congr (hgf t).symm)
    (fun t => by
      by_cases ht : t ∈ Λ
      · simp only [hg, ht, (hΛ1 t).mpr ht, ite_true, eisensteinCotSeries_add_one]
      · simp only [hg, ht, mt (hΛ1 t).mp ht, ite_false]; exact hf1 t ht)
    (fun t => by
      by_cases ht : t ∈ Λ
      · simp only [hg, ht, (hΛτ t).mpr ht, ite_true, eisensteinCotSeries_add hε hτ]
      · simp only [hg, ht, mt (hΛτ t).mp ht, ite_false]; exact hfτ t ht)
    (fun t => by
      by_cases ht : t ∈ Λ
      · simp only [hg, ht, (hΛneg t).mpr ht, ite_true, eisensteinCotSeries_neg hε]
      · simp only [hg, ht, mt (hΛneg t).mp ht, ite_false]; exact hfodd t ht)
    (fun t ht => by
      have : g =ᶠ[𝓝 t] f := by
        filter_upwards [hopen.mem_nhds ht] with w hw
        simp only [hg, show w ∉ Λ from hw, ite_false]
      exact (hfan t ht).congr this.symm)
    (by
      obtain ⟨A, hA, hfA⟩ := hf0
      refine ⟨A, hA, ?_⟩
      filter_upwards [hfA, hgf 0] with t h1 h2
      rw [← h1, h2])
  intro t ht
  have := key t ht
  simp only [hg, ht, ite_false] at this
  exact this

/-- `π cot(πt) - 1/t` has a removable singularity at `0`. -/
lemma exists_analyticAt_pi_mul_cot_sub_one_div :
    ∃ B : ℂ → ℂ, AnalyticAt ℂ B 0 ∧
      (fun t : ℂ => π * cot (π * t) - 1 / t) =ᶠ[𝓝[≠] 0] B := by
  have hd : HasDerivAt (fun t : ℂ => sin (π * t)) (π : ℂ) 0 := by
    have := ((hasDerivAt_id (0 : ℂ)).const_mul (π : ℂ)).csin
    simpa using this
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  obtain ⟨B, hB, hev⟩ := exists_analyticAt_eq_div_sub_div_of_residue_eq (a := π) (b := 1)
    (N₁ := fun t => cos (π * t)) (S₁ := fun t => sin (π * t)) (N₂ := fun _ => 1)
    (S₂ := fun t => t) (by fun_prop) analyticAt_const (by fun_prop) analyticAt_id
    (by simp) rfl (by simp) rfl hd (hasDerivAt_id 0) hπ one_ne_zero (by ring)
  refine ⟨B, hB, ?_⟩
  filter_upwards [hev] with t h
  rw [← h, Complex.cot_eq_cos_div_sin]; ring

/-- The cotangent series identity for `cs`: `2K cs(2Kt) = ∑ₙ (-1)ⁿ π cot(π(t - nτ))`
(regularized) off the lattice. -/
theorem jacobiCs_eq_eisensteinCotSeries {k : ℂ} (hk : k ∈ jacobiModulusDomain) {t : ℂ}
    (ht : t ∉ eisensteinSinLattice (jacobiTau k)) :
    2 * completeEllipticK k * jacobiCs (2 * completeEllipticK k * t) k =
        eisensteinCotSeries (-1) (jacobiTau k) t := by
  have hτ := jacobiTau_im_pos hk
  have hK := completeEllipticK_ne_zero_of_mem_jacobiModulusDomain hk
  have hK2 : 2 * completeEllipticK k ≠ 0 := mul_ne_zero two_ne_zero hK
  set K := completeEllipticK k
  set f : ℂ → ℂ := fun t => 2 * K * jacobiPQ .c .s (2 * K * t) k with hfdef
  have hlat : ∀ t, t ∉ eisensteinSinLattice (jacobiTau k) → 2 * K * t ∉ jacobiCongruentk 0 k := by
    rintro t ht ⟨m, n, hmn⟩
    apply ht
    refine ⟨m, n, ?_⟩
    have h2 := two_mul_completeEllipticK_mul_jacobiTau hk
    apply mul_left_cancel₀ hK2
    rw [hmn]; linear_combination (-(n : ℂ)) * h2
  have hdich : HasPoleDichotomy f := by
    have := (poleDichotomy_jacobiPQ hk (p := .c) (q := .s) (by decide)).comp
      (a := (2 * K)⁻¹) (inv_ne_zero hK2) hK2
    convert this using 2 with w
    rw [div_inv_eq_mul, mul_comm w]
  have hf1 : ∀ t, f (t + 1) = f t := by
    intro t
    simp only [hfdef, show 2 * K * (t + 1) = 2 * K * t + 2 * K by ring]
    have hs : jacobiPQ .c .s (2 * K * t + 2 * K) k = jacobiPQ .c .s (2 * K * t) k :=
      (jacobiCs_shift hk _).2.2.2.1
    rw [hs]
  have hfτ : ∀ t, f (t + jacobiTau k) = -1 * f t - I * π * (1 + -1) := by
    intro t
    have h2 : 2 * K * jacobiTau k = 2 * (I * completeEllipticKPrime k) :=
        two_mul_completeEllipticK_mul_jacobiTau hk
    simp only [hfdef, show 2 * K * (t + jacobiTau k) = 2 * K * t + 2 * K * jacobiTau k by ring,
      h2]
    have hs : jacobiPQ .c .s (2 * K * t + 2 * (I * completeEllipticKPrime k)) k =
        -jacobiPQ .c .s (2 * K * t) k := (jacobiCs_shift hk _).2.2.2.2.2
    rw [hs]; ring
  have hfodd : ∀ t, f (-t) = -f t := by
    intro t
    simp only [hfdef, show 2 * K * -t = -(2 * K * t) by ring, jacobiPQ_neg]
    simp
  have hfan : ∀ t ∉ eisensteinSinLattice (jacobiTau k), AnalyticAt ℂ f t := by
    intro t ht
    have h := analyticAt_jacobiPQ_s hk (p := .c) (by decide) (hlat t ht)
    have hl : AnalyticAt ℂ (fun t : ℂ => 2 * K * t) t := by fun_prop
    exact analyticAt_const.mul (h.comp hl)
  have hf0 : ∃ A : ℂ → ℂ, AnalyticAt ℂ A 0 ∧
      (fun t => f t - π * cot (π * t)) =ᶠ[𝓝[≠] 0] A := by
    obtain ⟨A, hA, hev⟩ := exists_analyticAt_jacobiPQ_s_sub_one_div hk (p := .c) (by decide)
    obtain ⟨B, hB, hevB⟩ := exists_analyticAt_pi_mul_cot_sub_one_div
    have hlin : AnalyticAt ℂ (fun t : ℂ => 2 * K * t) 0 := by fun_prop
    refine ⟨fun t => 2 * K * A (2 * K * t) - B t,
      (analyticAt_const.mul (hA.comp_of_eq hlin (by simp))).sub hB, ?_⟩
    have htend : Tendsto (fun t : ℂ => 2 * K * t) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have := hlin.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact mul_ne_zero hK2 ht
    filter_upwards [htend.eventually hev, hevB, self_mem_nhdsWithin] with t h1 h2 h3
    have h3' : t ≠ 0 := h3
    simp only [hfdef] at h1 ⊢
    rw [← h1, ← h2]
    field_simp
    ring
  exact eq_eisensteinCotSeries_of_quasiPeriodic (Or.inr rfl) hτ hdich.meromorphicAt hf1 hfτ
    hfodd hfan hf0 t ht

/-- The regularizing constants cancel in symmetric partial sums. -/
private lemma sum_Icc_zpow_mul_sign {ε : ℂ} (hε : ε = 1 ∨ ε = -1) (N : ℕ) :
    ∑ n ∈ Finset.Icc (-(N : ℤ)) N, ε ^ n * (I * π * (Int.sign n : ℂ)) = 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hI : Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
        insert (-((N : ℤ) + 1)) (insert ((N : ℤ) + 1) (Finset.Icc (-(N : ℤ)) N)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    rw [hI, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp), ih,
      sign_zpow_neg hε, Int.sign_neg]
    push_cast; ring

/-- The symmetric partial sums of `∑ₙ εⁿ π cot(π(t - nτ))` tend to `eisensteinCotSeries ε τ t`. -/
theorem tendsto_sum_Icc_zpow_pi_mul_cot {ε τ : ℂ} (hε : ε = 1 ∨ ε = -1) (hτ : 0 < τ.im)
    (t : ℂ) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, ε ^ n * (π * cot (π * (t - n * τ))))
      atTop (𝓝 (eisensteinCotSeries ε τ t)) := by
  have h := (summable_eisensteinCotTerm hε hτ t).hasSum
  have h2 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, eisensteinCotTerm ε τ n t)
      atTop (𝓝 (eisensteinCotSeries ε τ t)) := h.comp (Finset.tendsto_Icc_neg (R := ℤ))
  refine h2.congr fun N => ?_
  have := sum_Icc_zpow_mul_sign hε N
  simp only [eisensteinCotTerm, mul_sub, Finset.sum_sub_distrib, this, sub_zero]

/-- The symmetric partial sums of `∑ 1/(w - m)`. -/
private lemma sum_Icc_one_div_sub (w : ℂ) (M : ℕ) :
    ∑ m ∈ Finset.Icc (-(M : ℤ)) M, 1 / (w - m) =
      1 / w + ∑ n ∈ Finset.range M, cotTerm w n := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hI : Finset.Icc (-((M + 1 : ℕ) : ℤ)) ((M + 1 : ℕ) : ℤ) =
        insert (-((M : ℤ) + 1)) (insert ((M : ℤ) + 1) (Finset.Icc (-(M : ℤ)) M)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    rw [hI, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp), ih,
      Finset.sum_range_succ, cotTerm]
    push_cast
    ring

/-- The cotangent Mittag-Leffler expansion `π cot(πw) = lim ∑_{|m| ≤ M} 1/(w - m)`. -/
theorem tendsto_sum_Icc_one_div_sub {w : ℂ} (hw : ∀ m : ℤ, w - m ≠ 0) :
    Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc (-(M : ℤ)) M, 1 / (w - m)) atTop
      (𝓝 (π * cot (π * w))) := by
  have hx := mem_integerComplement_of_sub_intCast_ne_zero hw
  have hlim := ((hasSum_cotTerm' hx).tendsto_sum_nat).const_add (1 / w)
  simp_rw [← sum_Icc_one_div_sub] at hlim
  convert hlim using 2
  ring

/-- `a / tan x = a cot x`. -/
lemma div_tan_eq_mul_cot (a x : ℂ) : a / tan x = a * cot x := by
  rw [Complex.tan_eq_sin_div_cos, Complex.cot_eq_cos_div_sin, div_div_eq_mul_div, mul_div_assoc]

/-! ### Fourier expansion of the cotangent series -/

/-- `π cot(πx) - iπ = ∑_{j ≥ 0} 2πi e^{-2πi(j+1)x}` for `Im x < 0`. -/
private lemma hasSum_pi_mul_cot_sub_of_im_neg {x : ℂ} (hx : x.im < 0) :
    HasSum (fun j : ℕ => 2 * π * I * cexp (-(2 * π * I * (j + 1) * x)))
      (π * cot (π * x) - I * π) := by
  set b := cexp (-(π * I * x)) with hbdef
  have hb0 : b ≠ 0 := Complex.exp_ne_zero _
  have hb : ‖b‖ < 1 := by
    rw [Complex.norm_exp]
    have : (-(π * I * x)).re = π * x.im := by simp [Complex.mul_re, Complex.mul_im]
    rw [this, Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  have ha : ‖b ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg b]
  have h1 : b ^ 2 ≠ 1 := fun h => by rw [h] at ha; simp at ha
  have h2 : 1 - b ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hg := (hasSum_geometric_of_norm_lt_one ha).mul_left (2 * π * I * b ^ 2)
  have hsin : sin (π * x) = (b - b⁻¹) * I / 2 := by
    rw [Complex.sin, show b⁻¹ = cexp (π * x * I) by rw [hbdef, ← Complex.exp_neg]; ring_nf]
    simp only [b]; ring_nf
  have hcos : cos (π * x) = (b + b⁻¹) / 2 := by
    rw [Complex.cos, show b⁻¹ = cexp (π * x * I) by rw [hbdef, ← Complex.exp_neg]; ring_nf]
    simp only [b]; ring_nf
  have hbb : b - b⁻¹ ≠ 0 := by
    intro h
    have : b ^ 2 = 1 := by field_simp at h; linear_combination h
    exact h1 this
  convert hg using 1
  · funext j
    rw [show -(2 * π * I * ((j : ℂ) + 1) * x) = ((2 * (j + 1) : ℕ) : ℂ) * (-(π * I * x)) by
      push_cast; ring, Complex.exp_nat_mul, ← hbdef, pow_mul, pow_succ]
    ring
  · rw [Complex.cot_eq_cos_div_sin, hsin, hcos]
    field_simp
    ring_nf
    rw [Complex.I_sq]; ring

/-- The one-sided double-series interchange: for `Im t < c Im τ`, the series
`∑_{n ≥ 0} εⁿ (π cot(π(t - (n+c)τ)) - iπ)` and
`∑_{j ≥ 0} 2πi e^{-2πimt} e^{2πiτmc}/(1 - εQ)`, `m = j + 1`, `Q = e^{2πiτm}`, have the same
sum. -/
private lemma exists_hasSum_cot_fourier_one_side {ε τ t : ℂ} {c : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hτ : 0 < τ.im) (ht : t.im < c * τ.im) :
    ∃ V : ℂ, HasSum (fun n : ℕ => ε ^ n * (π * cot (π * (t - (n + c) * τ)) - I * π)) V ∧
      HasSum (fun j : ℕ => 2 * π * I * cexp (-(2 * π * I * (j + 1) * t)) *
        (cexp (2 * π * I * τ * (j + 1) * c) / (1 - ε * cexp (2 * π * I * τ * (j + 1))))) V := by
  have hεn : ∀ n : ℕ, ‖ε ^ n‖ = 1 := fun n => by
    rcases hε with rfl | rfl <;> simp
  set f : ℕ × ℕ → ℂ := fun p => ε ^ p.1 *
    (2 * π * I * cexp (-(2 * π * I * (p.2 + 1) * (t - (p.1 + c) * τ)))) with hf
  set α : ℝ := 2 * π * (t.im - c * τ.im)
  set β : ℝ := 2 * π * τ.im
  have hα : α < 0 := by simp only [α]; nlinarith [Real.pi_pos]
  have hβ : 0 < β := by simp only [β]; nlinarith [Real.pi_pos]
  have hbound : ∀ p : ℕ × ℕ, ‖f p‖ ≤ 2 * π * (Real.exp α ^ p.2 * Real.exp (-β) ^ p.1) := by
    rintro ⟨n, j⟩
    have e1 : ‖cexp (-(2 * π * I * (j + 1) * (t - (n + c) * τ)))‖ =
        Real.exp (2 * π * (j + 1) * (t.im - (n + c) * τ.im)) := by
      rw [Complex.norm_exp]; congr 1
      simp [Complex.mul_re, Complex.mul_im]
    simp only [hf, norm_mul, hεn, one_mul, e1, Complex.norm_ofNat, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    gcongr
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [α, β]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hp := Real.pi_pos
    have h1 : 0 ≤ π * τ.im := by positivity
    have h2 : 0 ≤ π * (c * τ.im - t.im) := by nlinarith
    nlinarith [mul_nonneg (mul_nonneg h1 hn) hj]
  have hsum : Summable fun p : ℕ × ℕ => 2 * π * (Real.exp α ^ p.2 * Real.exp (-β) ^ p.1) := by
    refine Summable.mul_left _ ?_
    have h1 : Summable fun j : ℕ => Real.exp α ^ j :=
      summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr hα)
    have h2 : Summable fun n : ℕ => Real.exp (-β) ^ n :=
      summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by linarith))
    have := summable_mul_of_summable_norm (f := fun n : ℕ => Real.exp (-β) ^ n)
      (g := fun j : ℕ => Real.exp α ^ j) (by simpa using h2) (by simpa using h1)
    convert this using 2 with p; ring
  have hfs : Summable f := Summable.of_norm_bounded hsum hbound
  have hfn : ∀ n : ℕ, HasSum (fun j => f (n, j))
      (ε ^ n * (π * cot (π * (t - (n + c) * τ)) - I * π)) := by
    intro n
    have hm : (t - (n + c) * τ).im < 0 := by
      have : (t - ((n : ℂ) + c) * τ).im = t.im - (n + c) * τ.im := by simp
      rw [this]; nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) hτ.le]
    exact (hasSum_pi_mul_cot_sub_of_im_neg hm).mul_left _
  have hfj : ∀ j : ℕ, HasSum (fun n => f (n, j)) (2 * π * I * cexp (-(2 * π * I * (j + 1) * t)) *
      (cexp (2 * π * I * τ * (j + 1) * c) / (1 - ε * cexp (2 * π * I * τ * (j + 1))))) := by
    intro j
    set Q := cexp (2 * π * I * τ * (j + 1))
    have hQ : ‖ε * Q‖ < 1 := by
      rw [norm_mul, show ‖ε‖ = 1 by simpa using hεn 1, one_mul, Complex.norm_exp]
      have : (2 * π * I * τ * (j + 1)).re = -(2 * π * τ.im * (j + 1)) := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [this, Real.exp_lt_one_iff]
      have : 0 < 2 * π * τ.im * (j + 1) := by positivity
      linarith
    have hg := (hasSum_geometric_of_norm_lt_one hQ).mul_left
      (2 * π * I * cexp (-(2 * π * I * (j + 1) * t)) * cexp (2 * π * I * τ * (j + 1) * c))
    convert hg using 1
    · funext n
      simp only [hf, Q]
      have : cexp (-(2 * π * I * (j + 1) * (t - (n + c) * τ))) =
          cexp (-(2 * π * I * (j + 1) * t)) * cexp (2 * π * I * τ * (j + 1) * c) *
            cexp (2 * π * I * τ * (j + 1)) ^ n := by
        rw [← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add]; push_cast; ring_nf
      rw [this, mul_pow]; ring
    · rw [div_eq_mul_inv]; ring
  have h1 := hfs.hasSum.prod_fiberwise hfn
  have h2 := ((Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hfs.hasSum).prod_fiberwise
    (g := fun j : ℕ => _) fun j => hfj j
  exact ⟨_, h1, h2⟩

/-- Fourier expansion of the cotangent series: for `|Im t| < Im τ`,
`C(t) - π cot(πt) = ∑_{j ≥ 0} 2πi (e^{-2πimt} - e^{2πimt}) εQ/(1 - εQ)`, `m = j + 1`,
`Q = e^{2πiτm}`. -/
theorem hasSum_fourier_eisensteinCotSeries {ε τ t : ℂ} (hε : ε = 1 ∨ ε = -1)
    (hτ : 0 < τ.im) (ht : |t.im| < τ.im) :
    HasSum (fun j : ℕ => 2 * π * I * (cexp (-(2 * π * I * (j + 1) * t)) -
        cexp (2 * π * I * (j + 1) * t)) *
        (ε * cexp (2 * π * I * τ * (j + 1)) / (1 - ε * cexp (2 * π * I * τ * (j + 1)))))
      (eisensteinCotSeries ε τ t - π * cot (π * t)) := by
  have hab := abs_lt.mp ht
  obtain ⟨V₁, hn₁, hj₁⟩ := exists_hasSum_cot_fourier_one_side hε hτ (t := t) (c := 1)
    (by linarith)
  obtain ⟨V₂, hn₂, hj₂⟩ := exists_hasSum_cot_fourier_one_side hε hτ (t := -t) (c := 1)
    (by simp; linarith)
  simp only [Complex.ofReal_one, mul_one] at hn₁ hn₂ hj₁ hj₂
  replace hn₁ := hn₁.mul_left ε
  replace hn₂ := hn₂.mul_left ε
  replace hj₁ := hj₁.mul_left ε
  replace hj₂ := hj₂.mul_left ε
  have hN := hasSum_nat_add_neg_succ_of_hasSum (summable_eisensteinCotTerm hε hτ t).hasSum
  have e0 : eisensteinCotTerm ε τ 0 t = π * cot (π * t) := by simp [eisensteinCotTerm]
  rw [e0] at hN
  have hval : eisensteinCotSeries ε τ t - π * cot (π * t) = ε * V₁ - ε * V₂ := by
    refine hN.unique ((hn₁.sub hn₂).congr_fun fun n => ?_)
    have hs1 : Int.sign ((n : ℤ) + 1) = 1 := Int.sign_eq_one_of_pos (by omega)
    have hs2 : Int.sign (-((n : ℤ) + 1)) = -1 := Int.sign_eq_neg_one_of_neg (by omega)
    have hz1 : ε ^ ((n : ℤ) + 1) = ε ^ (n + 1) := by
      rw [show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    have hz2 : ε ^ (-((n : ℤ) + 1)) = ε ^ (n + 1) := by rw [sign_zpow_neg hε, hz1]
    simp only [eisensteinCotTerm, hs1, hs2, hz1, hz2]
    rw [show (π : ℂ) * (-t - ((n : ℂ) + 1) * τ) = -(π * (t - ((-((n : ℤ) + 1) : ℤ) : ℂ) * τ)) by
      push_cast; ring, cot_neg']
    push_cast; ring
  rw [hval]
  refine (hj₁.sub hj₂).congr_fun fun j => ?_
  simp only [mul_neg, neg_neg]
  ring

/-- Fourier expansion of the half-shifted cotangent series: for `|Im t| < Im τ/2`,
`C(t - τ/2) - iπ = ∑_{j ≥ 0} 2πi (e^{-2πimt} - ε e^{2πimt}) qᵐ/(1 - εq^{2m})`, `m = j + 1`,
`q = e^{πiτ}`. -/
theorem hasSum_fourier_eisensteinCotSeries_sub_half {ε τ t : ℂ} (hε : ε = 1 ∨ ε = -1)
    (hτ : 0 < τ.im) (ht : |t.im| < τ.im / 2) :
    HasSum (fun j : ℕ => 2 * π * I * (cexp (-(2 * π * I * (j + 1) * t)) -
        ε * cexp (2 * π * I * (j + 1) * t)) *
        (cexp (π * I * τ * (j + 1)) / (1 - ε * cexp (2 * π * I * τ * (j + 1)))))
      (eisensteinCotSeries ε τ (t - τ / 2) - I * π) := by
  have hab := abs_lt.mp ht
  obtain ⟨V₁, hn₁, hj₁⟩ := exists_hasSum_cot_fourier_one_side hε hτ (t := t) (c := 1 / 2)
    (by linarith)
  obtain ⟨V₂, hn₂, hj₂⟩ := exists_hasSum_cot_fourier_one_side hε hτ (t := -t) (c := 1 / 2)
    (by simp; linarith)
  have hN := (summable_eisensteinCotTerm hε hτ (t - τ / 2)).hasSum.nat_add_neg_add_one
  have hval : eisensteinCotSeries ε τ (t - τ / 2) - I * π = V₁ - ε * V₂ := by
    have h3 := ((hn₁.add (hasSum_ite_eq (0 : ℕ) (I * π))).sub (hn₂.mul_left ε))
    refine sub_eq_of_eq_add (hN.unique (h3.congr_fun fun n => ?_) |>.trans (by ring))
    have hs2 : Int.sign (-((n : ℤ) + 1)) = -1 := Int.sign_eq_neg_one_of_neg (by omega)
    have hz2 : ε ^ (-((n : ℤ) + 1)) = ε ^ (n + 1) := by
      rw [sign_zpow_neg hε, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring,
        zpow_natCast]
    have e2 : eisensteinCotTerm ε τ (-((n : ℤ) + 1)) (t - τ / 2) =
        -(ε * (ε ^ n * (π * cot (π * (-t - (n + ((1 / 2 : ℝ) : ℂ)) * τ)) - I * π))) := by
      simp only [eisensteinCotTerm, hs2, hz2]
      rw [show (π : ℂ) * (-t - (n + ((1 / 2 : ℝ) : ℂ)) * τ) =
        -(π * (t - τ / 2 - ((-((n : ℤ) + 1) : ℤ) : ℂ) * τ)) by push_cast; ring, cot_neg']
      push_cast; ring
    have e1 : eisensteinCotTerm ε τ (n : ℤ) (t - τ / 2) =
        ε ^ n * (π * cot (π * (t - (n + ((1 / 2 : ℝ) : ℂ)) * τ)) - I * π) +
          (if n = 0 then I * π else 0) := by
      simp only [eisensteinCotTerm, zpow_natCast]
      rw [show t - τ / 2 - ((n : ℤ) : ℂ) * τ = t - (n + ((1 / 2 : ℝ) : ℂ)) * τ by
        push_cast; ring]
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · rw [Int.sign_eq_one_of_pos (by omega)]
        simp only [show n ≠ 0 by omega, ↓reduceIte]; push_cast; ring
    rw [e1, e2]; ring
  rw [hval]
  refine (hj₁.sub (hj₂.mul_left ε)).congr_fun fun j => ?_
  rw [show 2 * π * I * τ * ((j : ℂ) + 1) * ((1 / 2 : ℝ) : ℂ) = π * I * τ * (j + 1) by
    push_cast; ring]
  simp only [mul_neg, neg_neg]
  ring

/-! ### The derivative: the cosecant-square series -/

/-- `d/dw π cot(π(w - a)) = -π²/sin²(π(w - a))`. -/
private lemma hasDerivAt_pi_mul_cot (a x : ℂ) (h : sin (π * (x - a)) ≠ 0) :
    HasDerivAt (fun w => (π : ℂ) * cot (π * (w - a))) (-(π ^ 2 / sin (π * (x - a)) ^ 2)) x := by
  have hl : HasDerivAt (fun w : ℂ => π * (w - a)) π x := by
    simpa using ((hasDerivAt_id x).sub_const a).const_mul (π : ℂ)
  have := ((hl.ccos).div (hl.csin) h).const_mul (π : ℂ)
  simp only [Complex.cot_eq_cos_div_sin]
  convert this using 1
  have h2 := Complex.sin_sq_add_cos_sq (π * (x - a))
  field_simp
  linear_combination h2

/-- The sine of `π(t - nτ)` vanishes only on the lattice. -/
private lemma sin_pi_mul_sub_ne_zero_of_not_mem {τ t : ℂ} (ht : t ∉ eisensteinSinLattice τ)
    (n : ℤ) : sin (π * (t - n * τ)) ≠ 0 := by
  intro h0
  obtain ⟨m, hm⟩ := Complex.sin_eq_zero_iff.mp h0
  apply ht
  refine ⟨m, n, ?_⟩
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have : t - n * τ = m := by
    apply mul_left_cancel₀ hpi; rw [hm]; ring
  linear_combination this

/-- The cosecant-square series on the strip. -/
private lemma hasSum_pi_sq_div_sin_sq_of_strip {ε τ : ℂ} (hε : ε = 1 ∨ ε = -1)
    (hτ : 0 < τ.im) {t : ℂ} (hts : |t.im| < 3 / 4 * τ.im) (ht : t ∉ eisensteinSinLattice τ) :
    HasSum (fun n : ℤ => ε ^ n * (π ^ 2 / sin (π * (t - n * τ)) ^ 2))
      (-deriv (eisensteinCotSeries ε τ) t) := by
  have hU := isOpen_eisensteinSinStrip τ
  have htU : t ∈ eisensteinSinStrip τ := hts
  have hG : eisensteinCotSeries ε τ =ᶠ[𝓝 t] fun s => π * cot (π * s) +
      eisensteinCotRegularPart ε τ s := by
    filter_upwards [hU.mem_nhds htU] with s hs
    exact (hasSum_eisensteinCotTerm_of_strip hε hτ (le_of_lt hs)).tsum_eq
  have hs0 : sin (π * (t - 0)) ≠ 0 := by
    simpa using sin_pi_mul_sub_ne_zero_of_not_mem (τ := τ) ht 0
  have hd0 := hasDerivAt_pi_mul_cot 0 t hs0
  simp only [sub_zero] at hd0
  set F : ℤ → ℂ → ℂ := fun n w => if n = 0 then 0 else eisensteinCotTerm ε τ n w with hF
  have hFd : ∀ n, DifferentiableOn ℂ (F n) (eisensteinSinStrip τ) := by
    intro n
    by_cases hn : n = 0
    · simp only [hF, hn, ite_true]; exact differentiableOn_const _
    · simp only [hF, hn, ite_false, eisensteinCotTerm, Complex.cot_eq_cos_div_sin]
      refine DifferentiableOn.mul (differentiableOn_const _) (DifferentiableOn.sub
        (DifferentiableOn.mul (differentiableOn_const _) (DifferentiableOn.div (by fun_prop)
          (by fun_prop) fun w hw => ?_)) (differentiableOn_const _))
      exact sin_pi_mul_sub_ne_zero_of_strip hτ hn (le_of_lt hw)
  have hR := hasSum_deriv_of_summable_norm
    ((summable_pow_natAbs (exp_neg_pi_im_div_four_mem_Ico hτ).1
        (exp_neg_pi_im_div_four_mem_Ico hτ).2).mul_left _) hFd hU
    (fun n w hw => norm_ite_eisensteinCotTerm_le hε hτ n (le_of_lt hw)) htU
  have hRd : DifferentiableAt ℂ (eisensteinCotRegularPart ε τ) t :=
    (analyticAt_eisensteinCotRegularPart hε hτ hts).differentiableAt
  have hderiv : deriv (eisensteinCotSeries ε τ) t =
      -(π ^ 2 / sin (π * t) ^ 2) + deriv (eisensteinCotRegularPart ε τ) t := by
    rw [hG.deriv_eq, deriv_fun_add hd0.differentiableAt hRd, hd0.deriv]
  have hFn : ∀ n, deriv (F n) t =
      if n = 0 then 0 else -(ε ^ n * (π ^ 2 / sin (π * (t - n * τ)) ^ 2)) := by
    intro n
    by_cases hn : n = 0
    · simp [hF, hn]
    · simp only [hF, hn, ite_false, eisensteinCotTerm]
      have hsn := sin_pi_mul_sub_ne_zero_of_not_mem ht n
      have := ((hasDerivAt_pi_mul_cot (n * τ) t hsn).sub_const
        (I * π * (Int.sign n : ℂ))).const_mul (ε ^ n)
      rw [this.deriv]; ring
  simp only [hFn] at hR
  rw [hderiv]
  have h2 := (hasSum_ite_eq (0 : ℤ) (π ^ 2 / sin (π * t) ^ 2)).add hR.neg
  convert h2 using 1
  · funext n
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn]
  · rw [show eisensteinCotRegularPart ε τ = fun w => ∑' n, F n w from rfl]; ring

/-- The cosecant-square series `∑ₙ εⁿ π²/sin²(π(t - nτ)) = -C'(t)` off the lattice. -/
theorem hasSum_pi_sq_div_sin_sq {ε τ : ℂ} (hε : ε = 1 ∨ ε = -1) (hτ : 0 < τ.im) {t : ℂ}
    (ht : t ∉ eisensteinSinLattice τ) :
    HasSum (fun n : ℤ => ε ^ n * (π ^ 2 / sin (π * (t - n * τ)) ^ 2))
      (-deriv (eisensteinCotSeries ε τ) t) := by
  obtain ⟨j, hj⟩ := exists_abs_im_sub_intCast_mul_le hτ t
  have hε0 := sign_ne_zero_of_eq_one_or_eq_neg_one hε
  have ht' : t - j * τ ∉ eisensteinSinLattice τ := by
    rintro ⟨m, n, h⟩; exact ht ⟨m, n + j, by push_cast; linear_combination h⟩
  have h1 := hasSum_pi_sq_div_sin_sq_of_strip hε hτ (t := t - j * τ) (by linarith) ht'
  have hC : eisensteinCotSeries ε τ = fun s => ε ^ j * eisensteinCotSeries ε τ (s - j * τ) +
      ∑' n, cotShiftCorrection ε j n := by
    funext s
    have := eisensteinCotSeries_add_intCast_mul hε hτ j (s - j * τ)
    rwa [sub_add_cancel] at this
  have hd : DifferentiableAt ℂ (eisensteinCotSeries ε τ) (t - j * τ) :=
    (analyticAt_eisensteinCotSeries hε hτ ht').differentiableAt
  have hderiv : deriv (eisensteinCotSeries ε τ) t =
      ε ^ j * deriv (eisensteinCotSeries ε τ) (t - j * τ) := by
    conv_lhs => rw [hC]
    rw [deriv_add_const, deriv_const_mul _ (by
      exact hd.comp t ((differentiableAt_id).sub_const _)), deriv_comp_sub_const]
  rw [hderiv]
  have h2 := h1.mul_left (ε ^ j)
  rw [← (Equiv.subRight j).hasSum_iff] at h2
  convert h2 using 1
  · funext n
    simp only [Function.comp_apply, Equiv.subRight_apply]
    rw [show t - j * τ - ((n - j : ℤ) : ℂ) * τ = t - n * τ by push_cast; ring,
      show ε ^ n = ε ^ j * ε ^ (n - j) by rw [← zpow_add₀ hε0]; ring_nf]
    ring
  · ring

end DLMF.JacobiElliptic
