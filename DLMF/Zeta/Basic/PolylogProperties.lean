/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Basic.LerchContinuation
public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Basic analytic properties of the principal polylogarithm

For every complex order the polylogarithm series extends holomorphically to the principal
cut plane `ℂ \ [1, ∞)`. Its derivative lowers the order by one. Orders zero and one give
`z/(1-z)` and `-log(1-z)`, respectively. For `Re s > 1` the series converges on the unit
circle, agrees there with Mathlib's periodic zeta function, and at `z = 1` gives `ζ(s)`.
These are the basic properties used in DLMF §§25.12–25.14.
-/

@[expose] public section

open Complex Filter Set MeasureTheory
open scoped Nat Real Topology

noncomputable section

namespace DLMF.Zeta

/-- The series 25.12.10 converges absolutely in the open unit disk, for every complex `s`. -/
theorem summable_polylogSeries_of_norm_lt_one (s : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => z ^ (n + 1) / ((n : ℂ) + 1) ^ s := by
  obtain ⟨K, hK⟩ := exists_nat_ge (-s.re)
  have hg : Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ K * ‖z‖ ^ (n + 1) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one K (r := ‖z‖) (by simpa using hz)
    exact (summable_nat_add_iff 1).mpr h
  refine Summable.of_norm_bounded hg fun n => ?_
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [norm_div, norm_pow, show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
    norm_cpow_eq_rpow_re_of_pos hn, div_eq_mul_inv, mul_comm, ← Real.rpow_neg hn.le]
  gcongr
  rw [← Real.rpow_natCast]
  push_cast
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]) hK

/-- The series 25.12.10 converges absolutely on the closed unit disk when `Re s > 1`
(DLMF §25.12(ii)). -/
@[dlmf 25.12.ii]
theorem summable_polylogSeries_of_norm_le_one {s : ℂ} (hs : 1 < s.re) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Summable fun n : ℕ => z ^ (n + 1) / ((n : ℂ) + 1) ^ s := by
  have h := (Real.summable_one_div_nat_add_rpow 1 s.re).mpr hs
  refine Summable.of_norm_bounded h fun n => ?_
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [norm_div, norm_pow, show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
    norm_cpow_eq_rpow_re_of_pos hn, abs_of_pos hn]
  gcongr
  exact pow_le_one₀ (norm_nonneg _) hz

/-- The polylogarithm series from Lerch's series with `a = 1`. -/
private lemma hasSum_polylogSeries_of_hasSum_lerch {s z w : ℂ}
    (h : HasSum (fun n : ℕ => z ^ n / (1 + n) ^ s) w) :
    HasSum (fun n : ℕ => z ^ (n + 1) / ((n : ℂ) + 1) ^ s) (z * w) :=
  (h.mul_left z).congr_fun fun n => by rw [pow_succ, add_comm (1 : ℂ)]; ring

/-- **Continuation of `Li_s`** (DLMF §25.12(ii)): for every complex `s` the series 25.12.10 extends
analytically from the unit disk to `ℂ \ [1, ∞)`. -/
@[dlmf 25.12.ii]
theorem exists_polylog_continuation (s : ℂ) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F slitOne ∧ ∀ z, ‖z‖ < 1 → F z = polylogSeries s z := by
  obtain ⟨F, hF⟩ := exists_isLerchContinuation s 1
  exact ⟨fun z => z * F z, analyticOnNhd_id.mul hF.1, fun z hz =>
    (hasSum_polylogSeries_of_hasSum_lerch (hF.2 z hz)).tsum_eq.symm⟩

/-- Analyticity on a neighborhood of the specified domain: `AnalyticOnNhd ℂ (slitContinuation
(polylogSeries s)) slitOne ∧ ∀ z, ‖z‖ < 1 → slitContinuation (polylogSeries s) z =
polylogSeries s z`. -/
private lemma polylog_slitContinuation_spec (s : ℂ) :
    AnalyticOnNhd ℂ (slitContinuation (polylogSeries s)) slitOne ∧
      ∀ z, ‖z‖ < 1 → slitContinuation (polylogSeries s) z = polylogSeries s z := by
  have h := exists_polylog_continuation s
  unfold slitContinuation
  simp only [h, ↓reduceDIte]
  exact h.choose_spec

/-- On the cut plane, `Li_s(z) = z Φ(z, s, 1)` for any continuation `Φ(·, s, 1)` of Lerch's
series. -/
private lemma polylog_eq_mul_of_isLerchContinuation {s : ℂ} {F : ℂ → ℂ}
    (hF : IsLerchContinuation s 1 F) {z : ℂ}
    (hz : z ∈ slitOne) : polylog s z = z * F z := by
  simp only [polylog, hz, ↓reduceIte]
  refine eqOn_slitOne_of_eq_on_ball (polylog_slitContinuation_spec s).1 (analyticOnNhd_id.mul hF.1)
      (fun w hw => ?_) hz
  rw [(polylog_slitContinuation_spec s).2 w hw]
  exact (hasSum_polylogSeries_of_hasSum_lerch (hF.2 w hw)).tsum_eq

/-- `z ∈ ℂ \ [1, ∞)` for `|z| ≤ 1`, `z ≠ 1`. -/
theorem mem_slitOne_of_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) (h1 : z ≠ 1) : z ∈ slitOne := by
  by_contra h
  simp only [slitOne, mem_ofPred_eq, not_or, not_lt, ne_eq, not_not] at h
  have hre : z.re ≤ 1 := (re_le_norm z).trans hz
  exact h1 (Complex.ext (by simp; linarith [h.2]) (by simp [h.1]))

/-- `Li_s(z) = (z/Γ(s)) ∫_0^∞ x^{s-1}e^{-x}/(1 - z e^{-x}) dx` (the form 25.14.5 of 25.12.11). -/
theorem polylog_eq_mul_lerchIntegral {s z : ℂ}
    (h : (0 < s.re ∧ z ∈ slitOne) ∨ (1 < s.re ∧ z = 1)) :
    polylog s z = z * ((Gamma s)⁻¹ * lerchIntegral s 1 z) := by
  obtain ⟨F, hF⟩ := exists_isLerchContinuation s 1
  rcases h with ⟨hs, hz⟩ | ⟨hs, rfl⟩
  · rw [polylog_eq_mul_of_isLerchContinuation hF hz, hF.eq_lerchInt hs one_pos hz]
  · have h1 : (1 : ℂ) ∉ slitOne := by simp [slitOne]
    simp only [polylog, h1, ↓reduceIte]
    exact (hasSum_polylogSeries_of_hasSum_lerch
      (hasSum_lerch_lerchIntegral (z := 1) (by linarith) one_pos (Or.inr ⟨by simp, hs⟩))).tsum_eq

/-- **The series in the unit disk** (DLMF 25.12.10, 25.12.1 for `s = 2`): for `|z| < 1`,
`Li_s(z) = ∑_{n≥1} zⁿ/n^s`. -/
@[dlmf 25.12.E10]
theorem hasSum_polylog {s z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => z ^ (n + 1) / ((n : ℂ) + 1) ^ s) (polylog s z) := by
  simp only [polylog, mem_slitOne_of_norm_lt_one hz, ↓reduceIte]
  rw [(polylog_slitContinuation_spec s).2 z hz]
  exact (summable_polylogSeries_of_norm_lt_one s hz).hasSum

/-- **Analyticity** (DLMF §25.12(i)–(ii)): `Li_s` is analytic on `ℂ \ [1, ∞)`. -/
@[dlmf 25.12.ii]
theorem analyticOnNhd_polylog (s : ℂ) : AnalyticOnNhd ℂ (polylog s) slitOne := by
  refine (polylog_slitContinuation_spec s).1.congr isOpen_slitOne fun z hz => ?_
  simp only [polylog, hz, ↓reduceIte]

/-- `Li_s` is differentiable on the cut plane; in terms of `Φ(z, s, 1) = F z`,
`Li_s'(z) = F z + z F'(z)`. -/
private lemma exists_hasDerivAt_polylog (s : ℂ) {z : ℂ} (hz : z ∈ slitOne) :
    ∃ F : ℂ → ℂ, IsLerchContinuation s 1 F ∧ HasDerivAt (polylog s) (F z + z * deriv F z) z := by
  obtain ⟨F, hF⟩ := exists_isLerchContinuation s 1
  refine ⟨F, hF, ?_⟩
  have hev : polylog s =ᶠ[𝓝 z] fun w => w * F w := by
    filter_upwards [isOpen_slitOne.mem_nhds hz] with w hw
    exact polylog_eq_mul_of_isLerchContinuation hF hw
  have hd : HasDerivAt (fun w => w * F w) (1 * F z + z * deriv F z) z :=
    (hasDerivAt_id z).mul ((hF.1 z hz).differentiableAt.hasDerivAt)
  rw [one_mul] at hd
  exact hd.congr_of_eventuallyEq hev

/-- `z Li_s'(z) = Li_{s-1}(z)` on the cut plane. -/
private lemma mul_deriv_polylog (s : ℂ) {z : ℂ} (hz : z ∈ slitOne) :
    z * deriv (polylog s) z = polylog (s - 1) z := by
  obtain ⟨F, hF, hd⟩ := exists_hasDerivAt_polylog s hz
  have h1 : ∀ n : ℕ, (1 : ℂ) + n ≠ 0 := fun n => by
    have : (0 : ℝ) < 1 + n := by positivity
    exact_mod_cast this.ne'
  rw [hd.deriv, polylog_eq_mul_of_isLerchContinuation (isLerchContinuation_sub_one h1 hF) hz]
  ring

/-- The derivative recurrence `Li_s'(z) = Li_{s-1}(z)/z` on the principal cut plane,
away from the origin. -/
theorem hasDerivAt_polylog (s : ℂ) {z : ℂ} (hz : z ∈ slitOne) (hz0 : z ≠ 0) :
    HasDerivAt (polylog s) (polylog (s - 1) z / z) z := by
  have hd := (analyticOnNhd_polylog s z hz).differentiableAt.hasDerivAt
  convert hd using 1
  rw [← mul_deriv_polylog s hz, mul_div_cancel_left₀ _ hz0]

/-- The order-zero principal polylogarithm is the rational function `z/(1-z)`. -/
theorem polylog_zero_order {z : ℂ} (hz : z ∈ slitOne) :
    polylog 0 z = z / (1 - z) := by
  have hn : ∀ w ∈ slitOne, (1 : ℂ) - w ≠ 0 := by
    intro w hw he
    have he' : w = 1 := by linear_combination -he
    simpa [he', slitOne] using hw
  refine eqOn_slitOne_of_eq_on_ball (analyticOnNhd_polylog 0)
    (analyticOnNhd_id.div (analyticOnNhd_const.sub analyticOnNhd_id) hn) ?_ hz
  intro w hw
  have h := (hasSum_geometric_of_norm_lt_one hw).mul_left w
  have h' : HasSum (fun n : ℕ => w ^ (n + 1) / ((n : ℂ) + 1) ^ (0 : ℂ))
      (w / (1 - w)) := by
    simpa only [cpow_zero, div_one, div_eq_mul_inv, pow_succ, mul_comm, inv_one, mul_one] using h
  exact (hasSum_polylog hw).unique h'

/-- `Li_1(z) = -ln(1 - z)` on the cut plane. -/
theorem polylog_one_eq_neg_log {z : ℂ} (hz : z ∈ slitOne) :
    polylog 1 z = -Complex.log (1 - z) := by
  have hmem : ∀ w ∈ slitOne, 1 - w ∈ slitPlane := fun w hw => by
    rcases hw with h | h
    · right; simpa using h
    · left; simp; linarith
  refine eqOn_slitOne_of_eq_on_ball (F := polylog 1) (G := fun z => -Complex.log (1 - z))
    (analyticOnNhd_polylog 1) (fun w hw => ((analyticAt_clog (hmem w hw)).comp
      (analyticAt_const.sub analyticAt_id)).neg) (fun w hw => ?_) hz
  have h := hasSum_polylog (s := 1) hw
  simp only [cpow_one] at h
  exact h.unique (Complex.hasSum_taylorSeries_neg_log' hw)

/-- `Li₂'(z) = -ln(1 - z)/z` on the cut plane, `z ≠ 0`. -/
theorem hasDerivAt_polylog_two {z : ℂ} (hz : z ∈ slitOne) (hz0 : z ≠ 0) :
    HasDerivAt (polylog 2) (-Complex.log (1 - z) / z) z := by
  obtain ⟨F, hF, hd⟩ := exists_hasDerivAt_polylog 2 hz
  have h := mul_deriv_polylog 2 hz
  rw [hd.deriv, show (2 : ℂ) - 1 = 1 by norm_num, polylog_one_eq_neg_log hz] at h
  rw [← h, mul_div_cancel_left₀ _ hz0]
  exact hd

/-- `Li₂'(0) = 1`. -/
theorem hasDerivAt_polylog_two_zero : HasDerivAt (polylog 2) 1 0 := by
  obtain ⟨F, hF, hd⟩ :=
    exists_hasDerivAt_polylog 2 (mem_slitOne_of_norm_lt_one (z := 0) (by simp))
  have h0 : HasSum (fun n : ℕ => (0 : ℂ) ^ n / (1 + n) ^ (2 : ℂ)) 1 := by
    convert hasSum_ite_eq 0 (1 : ℂ) using 1
    funext n
    rcases n with _ | n <;> simp
  rw [zero_mul, add_zero, (hF.2 0 (by simp)).unique h0] at hd
  exact hd

/-- **The series on the unit circle** (DLMF §25.12(ii), 25.12.1 for `s = 2`): for `Re s > 1` and
`|z| = 1`, `Li_s(z) = ∑ zⁿ/n^s` (Abel's theorem; at `z = 1` this is the definition). -/
@[dlmf 25.12.E10]
theorem hasSum_polylog_of_norm_eq_one {s z : ℂ} (hs : 1 < s.re) (hz : ‖z‖ = 1) :
    HasSum (fun n : ℕ => z ^ (n + 1) / ((n : ℂ) + 1) ^ s) (polylog s z) := by
  by_cases h1 : z = 1
  · subst h1
    have h1' : (1 : ℂ) ∉ slitOne := by simp [slitOne]
    simp only [polylog, h1', ↓reduceIte]
    exact (summable_polylogSeries_of_norm_le_one hs (by simp)).hasSum
  · obtain ⟨F, hF⟩ := exists_isLerchContinuation s 1
    have hzs := mem_slitOne_of_norm_le_one hz.le h1
    rw [polylog_eq_mul_of_isLerchContinuation hF hzs]
    exact hasSum_polylogSeries_of_hasSum_lerch (hF.hasSum_of_norm_le_one hs hz.le hzs)

/-- **`Li_s(1) = ζ(s)`** (DLMF §25.12(ii)) for `Re s > 1`. -/
@[dlmf 25.12.ii]
theorem polylog_one {s : ℂ} (hs : 1 < s.re) : polylog s 1 = riemannZeta s := by
  have h1 : (1 : ℂ) ∉ slitOne := by simp [slitOne]
  simp only [polylog, h1, ↓reduceIte]
  rw [polylogSeries, zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  simp

/-- On the closed unit disk, `Li_n(z)` for natural `n ≥ 2` is the value of the series
25.12.10. -/
theorem polylog_natCast_eq_polylogSeries {n : ℕ} (hn : 2 ≤ n) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    polylog n z = polylogSeries n z := by
  rw [polylogSeries]
  rcases hz.lt_or_eq with h | h
  · exact (hasSum_polylog h).tsum_eq.symm
  · exact (hasSum_polylog_of_norm_eq_one (by simp; exact_mod_cast hn) h).tsum_eq.symm

open HurwitzZeta in
/-- **`F(x, s)` is the polylogarithm on the unit circle** (DLMF §25.13): `F(x, s) = Li_s(e^{2πix})`
for real `x` and `Re s > 1`. -/
@[dlmf 25.13]
theorem polylog_exp_eq_expZeta (x : ℝ) {s : ℂ} (hs : 1 < s.re) :
    polylog s (cexp (2 * π * I * x)) = expZeta (x : UnitAddCircle) s := by
  have hz : ‖cexp (2 * π * I * x)‖ = 1 := by
    rw [show 2 * π * I * x = ((2 * π * x : ℝ) : ℂ) * I by push_cast; ring]
    exact norm_exp_ofReal_mul_I _
  have h1 := hasSum_polylog_of_norm_eq_one hs hz
  have h2 := (hasSum_nat_add_iff' 1).mpr (hasSum_expZeta_of_one_lt_re x hs)
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, Complex.exp_zero,
    zero_cpow (ne_zero_of_one_lt_re hs), div_zero, sub_zero] at h2
  refine h1.unique (h2.congr_fun fun n => ?_)
  rw [← Complex.exp_nat_mul]
  push_cast
  ring_nf

end DLMF.Zeta

end
