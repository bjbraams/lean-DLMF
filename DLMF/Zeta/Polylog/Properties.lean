/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Polylog.Dilog
public import DLMF.Zeta.Basic.PolylogProperties
public import DLMF.Zeta.Polylog.LogarithmicExpansion
public import DLMF.Zeta.Basic.Hurwitz
public import DLMF.Zeta.Basic.Polylog
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Log
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

/-!
# Polylogarithms of complex order (DLMF §25.12)

The polylogarithm `Li_s(z)` of complex order `s` (DLMF §25.12): the series 25.12.10, its
analytic continuation to the cut plane `ℂ \ [1, ∞)` (principal branch), the dilogarithm
identities of §25.12(i), and the Fermi–Dirac and Bose–Einstein integrals. The real dilogarithm
`DLMF.Polylog.Real.dilog` and its identities are in `DLMF/Polylog/Dilog.lean`.

The definitions (`polylogSeries`, `slitContinuation`, `polylog`, `fermiDiracF`,
`boseEinsteinG`) are in the foundational module `DLMF.Zeta.Basic.Polylog`.

## Main results

* `exists_polylog_continuation`, `analyticOnNhd_polylog`: `Li_s` is defined by analytic
  continuation and is analytic on `ℂ \ [1, ∞)`.
* `hasSum_polylog`, `hasSum_polylog_of_norm_eq_one`, `polylog_one`: the series in the unit disk
  and on the unit circle for `Re s > 1`, and `Li_s(1) = ζ(s)`.
* `polylog_natCast_eq_polylogSeries`: for natural order `n ≥ 2`, `Li_n(z)` is the series on
  the closed unit disk.
* `polylog_two_ofReal_eq_dilog`: `Li₂(x)` is the real dilogarithm for `x < 1`.
* `hasSum_dilog`, `polylog_two_eq_integral`: the dilogarithm series and integral
  (DLMF 25.12.1–25.12.2).
* `polylog_two_add_polylog_two_div_sub_one`, `polylog_two_add_polylog_two_inv`,
  `polylog_two_pow`, `polylog_two_add_polylog_two_one_sub`: the dilogarithm identities
  DLMF 25.12.3–25.12.6.
* `polylog_two_exp_mul_I`, `hasSum_cos_div_sq`, `hasSum_sin_div_sq`: `Li₂` on the unit circle
  (DLMF 25.12.7–25.12.9).
* `polylog_eq_integral`: the integral representation (DLMF 25.12.11).
* `hasSum_polylog_log`: the expansion about `z = 1` (DLMF 25.12.12).
* `fermiDiracF_eq_polylog`, `boseEinsteinG_eq_polylog`: both integrals as polylogarithms
  (DLMF 25.12.16).

## Implementation notes

`polylog s z` is the analytic continuation on `ℂ \ [1, ∞)` and the value of the series on the
cut `[1, ∞)` (meaningful at `z = 1` for `Re s > 1`). It is defined by choosing the continuation
when one exists (`slitContinuation`); since `ℂ \ [1, ∞)` is connected, the continuation is
unique.

**Correction (branch).** 25.12.13 as printed (`ln z` principal) holds for `Im z ≥ 0` only; for
`Im z < 0` it fails (mpmath: `s = 2.5 + 0.2i`, `z = 0.5 - 0.9i`; `s = 0.7 + 0.3i`,
`z = -0.3 - 0.4i`; `s = 2`, `z = -2 - 0.5i`). It holds for all `z ∈ ℂ \ [0, ∞)` with
`ln z` taken with `0 < ph z < 2π` (the branch cut along `[0, ∞)` named by DLMF's domain), i.e.
`ln z/(2πi) = 1/2 + ln(-z)/(2πi)` with principal `ln(-z)`; this form is the one stated. We also
exclude `s = 0`, where `1/Γ(s)` vanishes and `ζ(1 - s, ·)` has its pole.
-/

@[expose] public section

open Complex Filter Set MeasureTheory
open scoped Nat Real Topology

noncomputable section

namespace DLMF.Zeta


open DLMF.Polylog in
/-- `Li₂(x)` is the real dilogarithm `DLMF.Polylog.Real.dilog x` for real `x < 1`. -/
theorem polylog_two_ofReal_eq_dilog {x : ℝ} (hx : x < 1) :
    polylog 2 x = (Real.dilog x : ℂ) := by
  have hmem : ∀ y : ℝ, y < 1 → (y : ℂ) ∈ slitOne := fun y hy => Or.inr (by simpa using hy)
  have hder : ∀ y : ℝ, y < 1 → HasDerivAt (fun t : ℝ => polylog 2 t - (Real.dilog t : ℂ)) 0 y := by
    intro y hy
    have h2 : HasDerivAt (fun t : ℝ => (Real.dilog t : ℂ)) (dilogKernel y : ℂ) y :=
      (Real.hasDerivAt_dilog hy).ofReal_comp
    have h1 : HasDerivAt (fun t : ℝ => polylog 2 t) (dilogKernel y : ℂ) y := by
      rcases eq_or_ne y 0 with rfl | hy0
      · rw [dilogKernel_zero, ofReal_one]
        have := hasDerivAt_polylog_two_zero.comp_ofReal (z := (0 : ℝ))
        exact this
      · have hc := (hasDerivAt_polylog_two (hmem y hy)
          (by exact_mod_cast hy0)).comp_ofReal (z := y)
        rw [dilogKernel_of_ne hy0]
        convert hc using 1
        rw [← ofReal_one, ← ofReal_sub, ← ofReal_log (by linarith)]
        push_cast; ring
    have := h1.fun_sub h2
    rwa [sub_self] at this
  have hc := (isOpen_Iio (a := (1 : ℝ))).is_const_of_deriv_eq_zero isPreconnected_Iio
    (f := fun t : ℝ => polylog 2 t - (Real.dilog t : ℂ))
    (fun y hy => (hder y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hder y hy).deriv) (show x ∈ Iio (1 : ℝ) from hx)
    (show (0 : ℝ) ∈ Iio (1 : ℝ) by norm_num)
  have hp0 : polylog 2 0 = 0 := by
    have := hasSum_polylog (s := 2) (z := 0) (by simp)
    simpa using this.tsum_eq.symm
  simp only [ofReal_zero, hp0, Real.dilog_zero] at hc
  exact sub_eq_zero.mp (hc.trans (sub_self 0))

/-- Real points accumulate: a property holding near `x₀` on `ℝ` holds frequently near `x₀`
in `ℂ`. -/
private lemma frequently_ofReal_of_eventually {P : ℂ → Prop} {x₀ : ℝ}
    (h : ∀ᶠ x : ℝ in 𝓝 x₀, P (x : ℂ)) :
    ∃ᶠ z in 𝓝[≠] (x₀ : ℂ), P z := by
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] x₀) (𝓝[≠] (x₀ : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨(continuous_ofReal.tendsto x₀).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun x hx => ofReal_injective.ne hx⟩
  exact ht.frequently (h.filter_mono nhdsWithin_le_nhds).frequently

/-- The function `(fun w => polylog 2 (f w))` is analytic over `ℂ` at `z`. -/
private lemma analyticAt_polylog_two_comp {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (hz : f z ∈ slitOne) : AnalyticAt ℂ (fun w => polylog 2 (f w)) z :=
  (analyticOnNhd_polylog 2 _ hz).comp hf

/-! ### §25.12(i) Dilogarithms -/

/-- **The dilogarithm series** (DLMF 25.12.1): `Li₂(z) = ∑_{n≥1} zⁿ/n²` for `|z| ≤ 1`. -/
@[dlmf 25.12.E1]
theorem hasSum_dilog {z : ℂ} (hz : ‖z‖ ≤ 1) :
    HasSum (fun n : ℕ => z ^ (n + 1) / ((n : ℂ) + 1) ^ 2) (polylog 2 z) := by
  have h2 : ∀ w : ℂ, w ^ (2 : ℂ) = w ^ (2 : ℕ) := fun w => by
    rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, cpow_natCast]
  rcases hz.lt_or_eq with h | h
  · simpa only [h2] using hasSum_polylog (s := 2) h
  · simpa only [h2] using hasSum_polylog_of_norm_eq_one (s := 2) (by norm_num) h

/-- **Integral representation of `Li₂`** (DLMF 25.12.2): `Li₂(z) = -∫_0^z t^{-1} ln(1-t) dt` for
`z ∈ ℂ \ (1, ∞)`, along the segment `[0, z]` (`t = uz`), principal logarithm. (The real case
`x ≤ 1` is `DLMF.Polylog.Real.dilog`.) -/
@[dlmf 25.12.E2]
theorem polylog_two_eq_integral {z : ℂ} (hz : z.im ≠ 0 ∨ z.re ≤ 1) :
    polylog 2 z = -∫ u in (0 : ℝ)..1, Complex.log (1 - u * z) / u := by
  by_cases hzs : z ∈ slitOne
  · have hmem : ∀ u ∈ Icc (0 : ℝ) 1, (u : ℂ) * z ∈ slitOne := fun u hu => by
      have := starConvex_slitOne hzs (a := 1 - u) (b := u) (by linarith [hu.2]) hu.1
        (by ring)
      have h2 : (u : ℂ) * z ∈ slitOne := by simpa [Complex.real_smul] using this
      exact h2
    have hd : ∀ u ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun u : ℝ => polylog 2 (u * z))
        (deriv (polylog 2) (u * z) * z) u := by
      intro u hu
      rw [uIcc_of_le zero_le_one] at hu
      have hg := ((analyticOnNhd_polylog 2 _ (hmem u hu)).differentiableAt).hasDerivAt
      have hh : HasDerivAt (fun u : ℝ => (u : ℂ) * z) z u := by
        simpa using ((hasDerivAt_id u).ofReal_comp).mul_const z
      exact hg.comp u hh
    have hc : ContinuousOn (fun u : ℝ => deriv (polylog 2) (u * z) * z) (uIcc 0 1) := by
      intro u hu
      rw [uIcc_of_le zero_le_one] at hu
      refine ContinuousAt.continuousWithinAt ?_
      refine ContinuousAt.mul ?_ continuousAt_const
      exact ((analyticOnNhd_polylog 2).deriv _ (hmem u hu)).continuousAt.comp
        (f := fun u : ℝ => (u : ℂ) * z) (by fun_prop)
    have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)
    have hp0 : polylog 2 0 = 0 := by
      have := hasSum_polylog (s := 2) (z := 0) (by simp)
      simpa using this.tsum_eq.symm
    simp only [ofReal_one, one_mul, ofReal_zero, zero_mul, hp0, sub_zero] at hF
    rw [← hF, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun u hu => ?_)
    rw [uIoc_of_le zero_le_one] at hu
    rcases eq_or_ne z 0 with rfl | hz0
    · simp
    have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu.1.ne'
    rw [(hasDerivAt_polylog_two (hmem u ⟨hu.1.le, hu.2⟩) (mul_ne_zero hu0 hz0)).deriv]
    field_simp
  · have hz1 : z = 1 := by
      simp only [slitOne, Set.mem_ofPred_eq, not_or, not_lt, ne_eq, not_not] at hzs
      rcases hz with h | h
      · exact absurd hzs.1 h
      · exact Complex.ext (by simp; linarith [hzs.2]) (by simp [hzs.1])
    subst hz1
    rw [polylog_one (by norm_num), riemannZeta_two,
      show (π : ℂ) ^ 2 / 6 = ((π ^ 2 / 6 : ℝ) : ℂ) by push_cast; ring,
      ← DLMF.Polylog.Real.dilog_one, DLMF.Polylog.Real.dilog, ← intervalIntegral.integral_ofReal,
      ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun u hu => ?_)
    rw [uIoc_of_le zero_le_one] at hu
    rw [DLMF.Polylog.dilogKernel_of_ne hu.1.ne', mul_one,
      show (1 : ℂ) - u = ((1 - u : ℝ) : ℂ) by push_cast; ring, ← ofReal_log (by linarith [hu.2])]
    push_cast
    ring

/-- **Landen-type identity** (DLMF 25.12.3): `Li₂(z) + Li₂(z/(z-1)) = -½ (ln(1-z))²` for
`z ∈ ℂ \ [1, ∞)`. (Real case: `DLMF.Polylog.Real.dilog_add_dilog_div_sub_one`.) -/
@[dlmf 25.12.E3]
theorem polylog_two_add_polylog_two_div_sub_one {z : ℂ} (hz : z ∈ slitOne) :
    polylog 2 z + polylog 2 (z / (z - 1)) = -(1 / 2) * Complex.log (1 - z) ^ 2 := by
  have hne : ∀ w ∈ slitOne, w - 1 ≠ 0 := fun w hw h => by
    rw [sub_eq_zero] at h; subst h; rcases hw with h | h <;> simp at h
  have hmem : ∀ w ∈ slitOne, w / (w - 1) ∈ slitOne := by
    intro w hw
    by_contra hc
    simp only [slitOne, Set.mem_ofPred_eq, not_or, not_lt, ne_eq, not_not] at hc
    set r := (w / (w - 1)).re
    have hr : w / (w - 1) = r := Complex.ext (by simp [r]) (by simp [hc.1])
    have hr1 : r ≠ 1 := fun h => by
      rw [h, ofReal_one, div_eq_one_iff_eq (hne w hw)] at hr
      simpa using congrArg (· - w) hr
    have hwr : w = r / (r - 1) := by
      have hr1' : (r : ℂ) - 1 ≠ 0 := by rw [sub_ne_zero]; exact_mod_cast hr1
      field_simp
      rw [div_eq_iff (hne w hw)] at hr
      linear_combination -hr
    have hgt : 1 < r := lt_of_le_of_ne hc.2 (Ne.symm hr1)
    rw [hwr] at hw
    rcases hw with h | h
    · apply h; rw [show (r : ℂ) / (r - 1) = ((r / (r - 1) : ℝ) : ℂ) by push_cast; ring]
      exact ofReal_im _
    · rw [show (r : ℂ) / (r - 1) = ((r / (r - 1) : ℝ) : ℂ) by push_cast; ring, ofReal_re] at h
      rw [div_lt_one (by linarith)] at h
      linarith
  have hlog : ∀ w ∈ slitOne, 1 - w ∈ slitPlane := fun w hw => by
    rcases hw with h | h
    · right; simpa using h
    · left; simp; linarith
  have hf : AnalyticOnNhd ℂ (fun w => polylog 2 w + polylog 2 (w / (w - 1))) slitOne :=
    fun w hw => (analyticOnNhd_polylog 2 w hw).add (analyticAt_polylog_two_comp
      (analyticAt_id.div (analyticAt_id.sub analyticAt_const) (hne w hw)) (hmem w hw))
  have hg : AnalyticOnNhd ℂ (fun w => -(1 / 2) * Complex.log (1 - w) ^ 2) slitOne :=
    fun w hw => analyticAt_const.mul
      (((analyticAt_clog (hlog w hw)).comp (analyticAt_const.sub analyticAt_id)).pow 2)
  refine hf.eqOn_of_preconnected_of_frequently_eq hg isPreconnected_slitOne
    (z₀ := ((0 : ℝ) : ℂ)) (Or.inr (by simp)) (frequently_ofReal_of_eventually (x₀ := 0) ?_) hz
  filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)] with x hx
  have hx' : x < 1 := hx
  have h := DLMF.Polylog.Real.dilog_add_dilog_div_sub_one hx'
  have hd : x / (x - 1) < 1 := by
    rw [div_lt_one_of_neg (by linarith)]; linarith
  rw [show (x : ℂ) / (x - 1) = ((x / (x - 1) : ℝ) : ℂ) by push_cast; ring,
    polylog_two_ofReal_eq_dilog hx', polylog_two_ofReal_eq_dilog hd,
    show (1 : ℂ) - x = ((1 - x : ℝ) : ℂ) by push_cast; ring, ← ofReal_log (by linarith)]
  have hC := congrArg (fun t : ℝ => (t : ℂ)) h
  push_cast at hC ⊢
  linear_combination hC

/-- **Inversion** (DLMF 25.12.4): `Li₂(z) + Li₂(1/z) = -π²/6 - ½ (ln(-z))²` for `z ∈ ℂ \ [0, ∞)`.
(Real case: `DLMF.Polylog.Real.dilog_add_dilog_recip`.) -/
@[dlmf 25.12.E4]
theorem polylog_two_add_polylog_two_inv {z : ℂ} (hz : z.im ≠ 0 ∨ z.re < 0) :
    polylog 2 z + polylog 2 (1 / z) = -(π : ℂ) ^ 2 / 6 - (1 / 2) * Complex.log (-z) ^ 2 := by
  set U : Set ℂ := {z | z.im ≠ 0 ∨ z.re < 0}
  have hU0 : ∀ w ∈ U, w ≠ 0 := fun w hw h => by subst h; rcases hw with h | h <;> simp at h
  have hU1 : ∀ w ∈ U, w ∈ slitOne := fun w hw => by
    rcases hw with h | h; exacts [Or.inl h, Or.inr (by linarith)]
  have hU2 : ∀ w ∈ U, 1 / w ∈ slitOne := fun w hw => by
    have hw0 := hU0 w hw
    rcases hw with h | h
    · left
      rw [one_div, inv_im]
      exact div_ne_zero (neg_ne_zero.mpr h) (by simpa using hw0)
    · right
      rw [one_div, inv_re]
      have : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw0
      have : w.re / Complex.normSq w < 0 := div_neg_of_neg_of_pos h this
      linarith
  have hU3 : ∀ w ∈ U, -w ∈ slitPlane := fun w hw => by
    rcases hw with h | h
    · right; simpa using h
    · left; simpa using h
  have hUo : IsOpen U :=
    (isOpen_ne_fun continuous_im continuous_const).union (isOpen_lt continuous_re continuous_const)
  have hUc : IsPreconnected U := by
    refine (StarConvex.isPathConnected (a := ((-1 : ℝ) : ℂ)) ?_ ?_).isConnected.isPreconnected
    · intro y hy p q hp hq hpq
      rcases eq_or_lt_of_le hq with hq0 | hq0
      · subst hq0; right; simp at hpq; subst hpq; norm_num
      rcases hy with h | h
      · left; simp only [Complex.real_smul, add_im, mul_im, ofReal_re, ofReal_im, zero_mul,
          add_zero, mul_zero, zero_add]; exact mul_ne_zero hq0.ne' h
      · right
        simp only [Complex.real_smul, add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
          mul_zero]
        nlinarith
    · right; norm_num
  have hf : AnalyticOnNhd ℂ (fun w => polylog 2 w + polylog 2 (1 / w)) U := fun w hw =>
    (analyticOnNhd_polylog 2 w (hU1 w hw)).add (analyticAt_polylog_two_comp
      (analyticAt_const.div analyticAt_id (hU0 w hw)) (hU2 w hw))
  have hg : AnalyticOnNhd ℂ (fun w => -(π : ℂ) ^ 2 / 6 - (1 / 2) * Complex.log (-w) ^ 2) U :=
    fun w hw => analyticAt_const.sub (analyticAt_const.mul
      (((analyticAt_clog (hU3 w hw)).comp analyticAt_id.neg).pow 2))
  refine hf.eqOn_of_preconnected_of_frequently_eq hg hUc (z₀ := ((-1 : ℝ) : ℂ))
    (Or.inr (by norm_num)) (frequently_ofReal_of_eventually (x₀ := -1) ?_) hz
  filter_upwards [Iio_mem_nhds (by norm_num : (-1 : ℝ) < 0)] with x hx
  have hx' : x < 0 := hx
  have h := DLMF.Polylog.Real.dilog_add_dilog_recip hx'
  rw [show (1 : ℂ) / x = ((x⁻¹ : ℝ) : ℂ) by push_cast; ring,
    polylog_two_ofReal_eq_dilog (by linarith), polylog_two_ofReal_eq_dilog (by
      have := inv_lt_zero.mpr hx'; linarith),
    show -(x : ℂ) = ((-x : ℝ) : ℂ) by push_cast; ring, ← ofReal_log (by linarith)]
  have hC := congrArg (fun t : ℝ => (t : ℂ)) h
  push_cast at hC ⊢
  linear_combination hC

/-- **Multiplication formula** (DLMF 25.12.5): `Li₂(z^m) = m ∑_{k=0}^{m-1} Li₂(z e^{2πik/m})` for
`m = 1, 2, 3, …`, `|z| < 1`. -/
@[dlmf 25.12.E5]
theorem polylog_two_pow {m : ℕ} (hm : 1 ≤ m) {z : ℂ} (hz : ‖z‖ < 1) :
    polylog 2 (z ^ m) =
      m * ∑ k ∈ Finset.range m, polylog 2 (z * cexp (2 * π * I * k / m)) := by
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h2 : ∀ w : ℂ, w ^ (2 : ℂ) = w ^ (2 : ℕ) := fun w => by
    rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, cpow_natCast]
  -- the root-of-unity sum
  have hroot : ∀ j : ℕ, ∑ k ∈ Finset.range m, cexp (2 * π * I * k / m) ^ j =
      if m ∣ j then (m : ℂ) else 0 := by
    intro j
    have hζ : ∀ k : ℕ, cexp (2 * π * I * k / m) ^ j = cexp (2 * π * I * j / m) ^ k := by
      intro k; rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]; congr 1; ring
    simp_rw [hζ]
    split_ifs with hd
    · obtain ⟨q, rfl⟩ := hd
      have : cexp (2 * π * I * ((m * q : ℕ) : ℂ) / m) = 1 := by
        rw [show 2 * π * I * ((m * q : ℕ) : ℂ) / m = q * (2 * π * I) by push_cast; field_simp,
          Complex.exp_nat_mul_two_pi_mul_I]
      rw [this]; simp
    · have hne : cexp (2 * π * I * j / m) ≠ 1 := by
        intro h
        obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
        have hjn : (j : ℂ) = n * m := by
          field_simp at hn
          linear_combination hn
        apply hd
        have : (j : ℤ) = n * m := by exact_mod_cast hjn
        exact Int.natCast_dvd_natCast.mp ⟨n, by rw [this]; ring⟩
      rw [geom_sum_eq hne, ← Complex.exp_nat_mul,
        show (m : ℂ) * (2 * π * I * j / m) = j * (2 * π * I) by field_simp,
        Complex.exp_nat_mul_two_pi_mul_I, sub_self, zero_div]
  have hk : ∀ k ∈ Finset.range m, HasSum (fun n : ℕ =>
      (z * cexp (2 * π * I * k / m)) ^ (n + 1) / ((n : ℂ) + 1) ^ (2 : ℂ))
      (polylog 2 (z * cexp (2 * π * I * k / m))) := by
    intro k _
    refine hasSum_polylog ?_
    rw [norm_mul, show (2 * π * I * k / m : ℂ) = ((2 * π * k / m : ℝ) : ℂ) * I by
      push_cast; ring, norm_exp_ofReal_mul_I, mul_one]
    exact hz
  have hS := (hasSum_sum hk).mul_left (m : ℂ)
  have hzm : ‖z ^ m‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hz (by omega)
  have hT := hasSum_polylog (s := 2) hzm
  set f : ℕ → ℂ := fun n => if m ∣ n + 1 then (m : ℂ) ^ 2 * z ^ (n + 1) / ((n : ℂ) + 1) ^ 2
    else 0
  have hf1 : HasSum f (m * ∑ k ∈ Finset.range m, polylog 2 (z * cexp (2 * π * I * k / m))) := by
    refine hS.congr_fun fun n => ?_
    simp only [f, h2, mul_pow, ← Finset.sum_div, ← Finset.mul_sum, hroot (n + 1)]
    split_ifs <;> ring
  have he : ∀ j : ℕ, m * j + (m - 1) + 1 = m * (j + 1) := fun j => by
    rw [Nat.mul_succ]; omega
  have hg : Function.Injective fun j : ℕ => m * j + (m - 1) := fun a b h => by
    simp only at h
    exact Nat.eq_of_mul_eq_mul_left (by omega) (Nat.add_right_cancel h)
  have hf2 : HasSum f (polylog 2 (z ^ m)) := by
    refine (hg.hasSum_iff fun n hn => ?_).mp ?_
    · simp only [f]
      rw [ite_eq_right_iff]
      rintro ⟨q, hq⟩
      exfalso
      apply hn
      rcases q with _ | q
      · simp at hq
      · refine ⟨q, ?_⟩
        simp only
        rw [Nat.mul_succ] at hq
        omega
    · refine hT.congr_fun fun j => ?_
      simp only [Function.comp, f, h2]
      have hd : m ∣ m * j + (m - 1) + 1 := ⟨j + 1, he j⟩
      simp only [hd, ↓reduceIte]
      have hc : ((m * j + (m - 1) : ℕ) : ℂ) + 1 = m * ((j : ℂ) + 1) := by
        exact_mod_cast he j
      rw [hc, he j, pow_mul]
      have hj : (j : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
      field_simp
  exact hf2.unique hf1

/-- **Euler's reflection formula** (DLMF 25.12.6): `Li₂(z) + Li₂(1-z) = π²/6 - ln z ln(1-z)` for
`z ∈ ℂ \ ((-∞, 0] ∪ [1, ∞))`, principal logarithms (both sides are analytic there and agree on
`(0, 1)`). (Real case `0 < x < 1`: `DLMF.Polylog.Real.dilog_add_dilog_one_sub`.) -/
@[dlmf 25.12.E6]
theorem polylog_two_add_polylog_two_one_sub {z : ℂ} (hz : z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1)) :
    polylog 2 z + polylog 2 (1 - z) =
      (π : ℂ) ^ 2 / 6 - Complex.log z * Complex.log (1 - z) := by
  set U : Set ℂ := {z | z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1)}
  have hU1 : ∀ w ∈ U, w ∈ slitOne := fun w hw => by
    rcases hw with h | h; exacts [Or.inl h, Or.inr h.2]
  have hU2 : ∀ w ∈ U, 1 - w ∈ slitOne := fun w hw => by
    rcases hw with h | h
    · left; simpa using h
    · right; simp; linarith [h.1]
  have hU3 : ∀ w ∈ U, w ∈ slitPlane := fun w hw => by
    rcases hw with h | h; exacts [Or.inr h, Or.inl h.1]
  have hU4 : ∀ w ∈ U, 1 - w ∈ slitPlane := fun w hw => by
    rcases hw with h | h
    · right; simpa using h
    · left; simp; linarith [h.2]
  have hUo : IsOpen U :=
    (isOpen_ne_fun continuous_im continuous_const).union
      ((isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const))
  have hUc : IsPreconnected U := by
    refine (StarConvex.isPathConnected (a := ((1 / 2 : ℝ) : ℂ)) ?_ ?_).isConnected.isPreconnected
    · intro y hy p q hp hq hpq
      rcases eq_or_lt_of_le hq with hq0 | hq0
      · subst hq0; right; simp at hpq; subst hpq; norm_num
      rcases hy with h | h
      · left; simp only [Complex.real_smul, add_im, mul_im, ofReal_re, ofReal_im, zero_mul,
          add_zero, mul_zero, zero_add]; exact mul_ne_zero hq0.ne' h
      · right
        simp only [Complex.real_smul, add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
          mul_zero]
        constructor <;> nlinarith [h.1, h.2]
    · right; norm_num
  have hf : AnalyticOnNhd ℂ (fun w => polylog 2 w + polylog 2 (1 - w)) U := fun w hw =>
    (analyticOnNhd_polylog 2 w (hU1 w hw)).add
      (analyticAt_polylog_two_comp (analyticAt_const.sub analyticAt_id) (hU2 w hw))
  have hg : AnalyticOnNhd ℂ (fun w => (π : ℂ) ^ 2 / 6 - Complex.log w * Complex.log (1 - w)) U :=
    fun w hw => analyticAt_const.sub ((analyticAt_clog (hU3 w hw)).mul
      ((analyticAt_clog (hU4 w hw)).comp (analyticAt_const.sub analyticAt_id)))
  refine hf.eqOn_of_preconnected_of_frequently_eq hg hUc (z₀ := ((1 / 2 : ℝ) : ℂ))
    (Or.inr (by norm_num)) (frequently_ofReal_of_eventually (x₀ := 1 / 2) ?_) hz
  filter_upwards [Ioo_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)]
    with x hx
  have h := DLMF.Polylog.Real.dilog_add_dilog_one_sub hx
  rw [show (1 : ℂ) - x = ((1 - x : ℝ) : ℂ) by push_cast; ring,
    polylog_two_ofReal_eq_dilog hx.2, polylog_two_ofReal_eq_dilog (by linarith [hx.1]),
    ← ofReal_log hx.1.le, ← ofReal_log (by linarith [hx.2])]
  exact_mod_cast h

/-- **`Li₂` on the unit circle** (DLMF 25.12.7): for `0 ≤ θ ≤ 2π`,
`Li₂(e^{iθ}) = ∑ cos(nθ)/n² + i ∑ sin(nθ)/n²` (in fact for all real `θ`). -/
@[dlmf 25.12.E7]
theorem polylog_two_exp_mul_I (θ : ℝ) :
    polylog 2 (cexp (θ * I)) =
      ((∑' n : ℕ, Real.cos ((n + 1) * θ) / ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) +
        I * ((∑' n : ℕ, Real.sin ((n + 1) * θ) / ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) := by
  have hz : ‖cexp (θ * I)‖ = 1 := norm_exp_ofReal_mul_I θ
  have h := hasSum_dilog hz.le
  have hterm (n : ℕ) : cexp (θ * I) ^ (n + 1) / ((n : ℂ) + 1) ^ 2 =
      ((Real.cos ((n + 1) * θ) / ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) +
        I * ((Real.sin ((n + 1) * θ) / ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.exp_nat_mul, show ((n + 1 : ℕ) : ℂ) * (θ * I) = (((n + 1) * θ : ℝ) : ℂ) * I by
      push_cast; ring, Complex.exp_mul_I]
    push_cast
    ring
  simp_rw [hterm] at h
  have hre := (Complex.hasSum_re h)
  have him := (Complex.hasSum_im h)
  simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, mul_im, I_im, zero_mul, one_mul,
    sub_zero, zero_add, add_im, mul_zero, add_zero] at hre him
  rw [hre.tsum_eq, him.tsum_eq]
  apply Complex.ext <;> simp

/-- **The cosine series** (DLMF 25.12.8): `∑_{n≥1} cos(nθ)/n² = π²/6 - πθ/2 + θ²/4` for
`0 ≤ θ ≤ 2π`. -/
@[dlmf 25.12.E8]
theorem hasSum_cos_div_sq {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 2 * π) :
    HasSum (fun n : ℕ => Real.cos ((n + 1) * θ) / ((n : ℝ) + 1) ^ 2)
      (π ^ 2 / 6 - π * θ / 2 + θ ^ 2 / 4) := by
  have hx : θ / (2 * π) ∈ Icc (0 : ℝ) 1 := ⟨by positivity, by
    rw [div_le_one (by positivity)]; exact h1⟩
  have h := hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero hx
  have h' := (hasSum_nat_add_iff' 1).mpr h
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_pow (by norm_num :
    2 * 1 ≠ 0), div_zero, zero_mul, sub_zero] at h'
  have hB : (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * 1))).eval (θ / (2 * π)) =
      (θ / (2 * π)) ^ 2 - θ / (2 * π) + 1 / 6 := by
    simp [Polynomial.bernoulli, Finset.sum_range_succ, bernoulli, bernoulli'_one, bernoulli'_two]
    ring
  rw [hB] at h'
  convert h' using 1
  · funext n
    push_cast
    rw [show 2 * π * (n + 1) * (θ / (2 * π)) = (n + 1) * θ by field_simp]
    ring
  · field_simp
    ring

/-- `|1 - e^{ix}| = 2 sin(x/2)` for `0 < x < 2π`. -/
private lemma norm_one_sub_exp_mul_I {x : ℝ} (hx0 : 0 < x) (hx1 : x < 2 * π) :
    ‖1 - cexp (x * I)‖ = 2 * Real.sin (x / 2) := by
  have hs : 0 < Real.sin (x / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have h2 : ‖1 - cexp (x * I)‖ ^ 2 = (2 * Real.sin (x / 2)) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hc : Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
      rw [show x = 2 * (x / 2) by ring, Real.cos_two_mul, Real.cos_sq']; ring_nf
    have hsn : Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
      rw [show x = 2 * (x / 2) by ring, Real.sin_two_mul]; ring_nf
    simp only [sub_re, one_re, exp_ofReal_mul_I_re, sub_im, one_im, exp_ofReal_mul_I_im]
    rw [hc, hsn]
    have := Real.sin_sq_add_cos_sq (x / 2)
    linear_combination (4 * Real.sin (x / 2) ^ 2) * this
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp h2

/-- `d/dx Im Li₂(e^{ix}) = -ln(2 sin(x/2))` for `0 < x < 2π`. -/
private lemma hasDerivAt_im_polylog_two_exp {x : ℝ} (hx0 : 0 < x) (hx1 : x < 2 * π) :
    HasDerivAt (fun y : ℝ => (polylog 2 (cexp (y * I))).im)
      (-Real.log (2 * Real.sin (x / 2))) x := by
  set z := cexp (x * I)
  have hz1 : ‖z‖ = 1 := norm_exp_ofReal_mul_I x
  have hzne : z ≠ 1 := by
    intro h
    have := norm_one_sub_exp_mul_I hx0 hx1
    rw [show cexp (x * I) = z from rfl, h, sub_self, norm_zero] at this
    have hs : 0 < Real.sin (x / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    linarith
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have hmem := mem_slitOne_of_norm_le_one hz1.le hzne
  have he : HasDerivAt (fun y : ℝ => cexp (y * I)) (z * I) x := by
    have := ((hasDerivAt_id x).ofReal_comp.mul_const I).cexp
    simpa using this
  have hg := (hasDerivAt_polylog_two hmem hz0).comp x he
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hg
  convert him using 1
  · rfl
  show _ = (-Complex.log (1 - z) / z * (z * I)).im
  rw [show -Complex.log (1 - z) / z * (z * I) = -Complex.log (1 - z) * I by field_simp]
  simp [Complex.log_re, z, norm_one_sub_exp_mul_I hx0 hx1]

/-- **Clausen's integral** (DLMF 25.12.9): `∑_{n≥1} sin(nθ)/n² = -∫_0^θ ln(2 sin(x/2)) dx` for
`0 ≤ θ ≤ 2π`. -/
@[dlmf 25.12.E9]
theorem hasSum_sin_div_sq {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 2 * π) :
    HasSum (fun n : ℕ => Real.sin ((n + 1) * θ) / ((n : ℝ) + 1) ^ 2)
      (-∫ x in (0 : ℝ)..θ, Real.log (2 * Real.sin (x / 2))) := by
  have hb : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    exact_mod_cast (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  have hbd : ∀ (n : ℕ) (x : ℝ), ‖Real.sin ((n + 1) * x) / ((n : ℝ) + 1) ^ 2‖ ≤
      1 / ((n : ℝ) + 1) ^ 2 := fun n x => by
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 1) ^ 2)]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)
  set F : ℝ → ℝ := fun x => ∑' n : ℕ, Real.sin ((n + 1) * x) / ((n : ℝ) + 1) ^ 2
  have hsum : ∀ x, HasSum (fun n : ℕ => Real.sin ((n + 1) * x) / ((n : ℝ) + 1) ^ 2) (F x) :=
    fun x => (hb.of_norm_bounded (fun n => hbd n x)).hasSum
  have hFeq : F = fun y : ℝ => (polylog 2 (cexp (y * I))).im := by
    funext y
    rw [polylog_two_exp_mul_I]
    simp [F]
  have hcont : Continuous F :=
    continuous_tsum (fun n => by fun_prop) hb hbd
  have hint : IntervalIntegrable (fun x => -Real.log (2 * Real.sin (x / 2))) volume 0 θ := by
    refine IntervalIntegrable.neg ?_
    have hm : MeromorphicOn (fun x : ℝ => 2 * Real.sin (x / 2)) (uIcc 0 θ) := by
      refine AnalyticOnNhd.meromorphicOn ?_
      intro x _
      exact analyticAt_const.mul (Real.analyticAt_sin.comp (analyticAt_id.div_const (c := 2)))
    exact hm.intervalIntegrable_log
  rcases h0.eq_or_lt with rfl | hθ
  · simp
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hθ.le hcont.continuousOn
    (fun x hx => hFeq ▸ hasDerivAt_im_polylog_two_exp hx.1 (hx.2.trans_le h1)) hint
  have hF0 : F 0 = 0 := by simp [F]
  rw [hF0, sub_zero, intervalIntegral.integral_neg] at hI
  rw [hI]
  exact hsum θ

/-! ### §25.12(ii) Polylogarithms: further properties -/

/-- **Integral representation** (DLMF 25.12.11): `Li_s(z) = (z/Γ(s)) ∫_0^∞ x^{s-1}/(e^x - z) dx`,
valid for `Re s > 0` and `|ph(1-z)| < π` (i.e. `z ∈ ℂ \ [1, ∞)`), or `Re s > 1` and `z = 1`. -/
@[dlmf 25.12.E11]
theorem polylog_eq_integral {s z : ℂ}
    (h : (0 < s.re ∧ z ∈ slitOne) ∨ (1 < s.re ∧ z = 1)) :
    polylog s z = z / Gamma s * ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) / (Real.exp x - z) := by
  rw [polylog_eq_mul_lerchIntegral h, lerchIntegral, div_eq_mul_inv, mul_assoc]
  congr 2
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  have he : (Real.exp x : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos x).ne'
  rw [one_mul, Complex.ofReal_exp] at *
  rw [Complex.exp_neg]
  have he' : cexp x ≠ 0 := Complex.exp_ne_zero _
  by_cases hd : cexp x - z = 0
  · have : 1 - z * (cexp x)⁻¹ = 0 := by
      rw [show z = cexp x by linear_combination -hd]; field_simp; ring
    rw [hd, this]; simp
  · have hd' : 1 - z * (cexp x)⁻¹ ≠ 0 := by
      intro h0; apply hd; field_simp at h0; linear_combination h0
    field_simp

/-- **Expansion about `z = 1`** (DLMF 25.12.12): for `s ≠ 1, 2, 3, …` and `|ln z| < 2π`,
`Li_s(z) = Γ(1-s)(-ln z)^{s-1} + ∑_{n≥0} ζ(s-n)(ln z)ⁿ/n!`. We take `z ∈ ℂ \ [1, ∞)`, `z ≠ 0`
(domain qualification: on the cut `(1, e^{2π})` the principal branch of `Li_s` is not defined, and
at `z = 1` with `Re s ≤ 1` the left side is infinite). The singular term uses `-ln z`
also on the negative real axis, with principal logarithms throughout. -/
@[dlmf 25.12.E12]
theorem hasSum_polylog_log {s z : ℂ} (hs : ∀ n : ℕ, s ≠ n + 1) (hz : z ∈ slitOne)
    (hz0 : z ≠ 0) (hlog : ‖Complex.log z‖ < 2 * π) :
    HasSum (fun n : ℕ => riemannZeta (s - n) * Complex.log z ^ n / n !)
      (polylog s z - Gamma (1 - s) * (-Complex.log z) ^ (s - 1)) := by
  exact PolylogLogarithmic.hasSum_regularized hs hz hz0 hlog

/-! ### §25.12(iii) Fermi–Dirac and Bose–Einstein integrals -/

/-- **`F_s` as a polylogarithm** (DLMF 25.12.16): `F_s(x) = -Li_{s+1}(-e^x)` for `s > -1`. -/
@[dlmf 25.12.E16]
theorem fermiDiracF_eq_polylog {s : ℝ} (hs : -1 < s) (x : ℝ) :
    (fermiDiracF s x : ℂ) = -polylog (s + 1) (-Real.exp x) := by
  have hz : (-(Real.exp x : ℂ)) ∈ slitOne := Or.inr (by
    show (-(Real.exp x : ℂ)).re < 1
    rw [neg_re, ofReal_re]; linarith [Real.exp_pos x])
  rw [polylog_eq_integral (Or.inl ⟨by simp; linarith, hz⟩)]
  have hint : ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ ((s : ℂ) + 1 - 1) / (Real.exp t - -(Real.exp x : ℂ)) =
      (∫ t in Ioi (0 : ℝ), ((t ^ s / (Real.exp (t - x) + 1) : ℝ) : ℂ)) / Real.exp x := by
    rw [← integral_div]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have he : (0 : ℝ) < Real.exp t + Real.exp x := by positivity
    have he' : ((Real.exp t : ℂ) + Real.exp x) ≠ 0 := by exact_mod_cast he.ne'
    rw [add_sub_cancel_right, ← ofReal_cpow (le_of_lt ht), Real.exp_sub]
    simp only [ofReal_div, ofReal_one, ofReal_add, sub_neg_eq_add]
    have hx : (Real.exp x : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos x).ne'
    field_simp
  have hG : Gamma ((s : ℂ) + 1) = (Real.Gamma (s + 1) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; rfl
  have hx : (Real.exp x : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos x).ne'
  rw [hint, integral_complex_ofReal, fermiDiracF, hG]
  push_cast
  field_simp

/-- **`G_s` as a polylogarithm** (DLMF 25.12.16): `G_s(x) = Li_{s+1}(e^x)` for `s > -1`, `x < 0`, or
`s > 0`, `x ≤ 0`. -/
@[dlmf 25.12.E16]
theorem boseEinsteinG_eq_polylog {s x : ℝ} (h : (-1 < s ∧ x < 0) ∨ (0 < s ∧ x ≤ 0)) :
    (boseEinsteinG s x : ℂ) = polylog (s + 1) (Real.exp x) := by
  have h' : (0 < ((s : ℂ) + 1).re ∧ (Real.exp x : ℂ) ∈ slitOne) ∨
      (1 < ((s : ℂ) + 1).re ∧ (Real.exp x : ℂ) = 1) := by
    rcases lt_or_eq_of_le (show x ≤ 0 by rcases h with h | h; exacts [h.2.le, h.2]) with hx | hx
    · refine Or.inl ⟨?_, Or.inr ?_⟩
      · rcases h with h | h <;> simp <;> linarith [h.1]
      · show (Real.exp x : ℂ).re < 1
        rw [ofReal_re]; exact Real.exp_lt_one_iff.mpr hx
    · subst hx
      rcases h with h | h
      · exact absurd h.2 (lt_irrefl 0)
      · exact Or.inr ⟨by simp; linarith [h.1], by simp⟩
  rw [polylog_eq_integral h']
  have hint : ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ ((s : ℂ) + 1 - 1) / (Real.exp t - (Real.exp x : ℂ)) =
      (∫ t in Ioi (0 : ℝ), ((t ^ s / (Real.exp (t - x) - 1) : ℝ) : ℂ)) / Real.exp x := by
    rw [← integral_div]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have hx : (Real.exp x : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos x).ne'
    rw [add_sub_cancel_right, ← ofReal_cpow (le_of_lt ht), Real.exp_sub]
    simp only [ofReal_div, ofReal_sub, ofReal_one]
    by_cases hd : (Real.exp t : ℂ) - Real.exp x = 0
    · have hd' : (Real.exp t : ℂ) / Real.exp x - 1 = 0 := by
        rw [div_sub_one hx, hd, zero_div]
      rw [hd, hd']; simp
    · have hd' : (Real.exp t : ℂ) / Real.exp x - 1 ≠ 0 := by
        rw [div_sub_one hx]; exact div_ne_zero hd hx
      field_simp
  have hG : Gamma ((s : ℂ) + 1) = (Real.Gamma (s + 1) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; rfl
  have hx : (Real.exp x : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos x).ne'
  rw [hint, integral_complex_ofReal, boseEinsteinG, hG]
  push_cast
  field_simp

end DLMF.Zeta

end
