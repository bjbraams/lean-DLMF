/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Hurwitz
public import DLMF.Zeta.Q25bLerchContinuation
public import DLMF.Polylog.Dilog
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.SpecialFunctions.Integrability.Log

/-!
# Polylogarithms of complex order (DLMF §25.12)

* `polylogSeriesC s z = ∑_{n≥1} zⁿ/n^s` (DLMF 25.12.10) for complex order `s`, as a `tsum`; for
  natural `s = n` it is the project's `DLMF.Polylog.polylogSeries n z`
  (`polylogSeriesC_natCast`).
* `polylog s z` is DLMF's `Li_s(z)`: the analytic continuation of the series from the unit disk to
  the cut plane `ℂ \ [1, ∞)` (principal branch, §25.12(i)–(ii)), and the value of the series on the
  cut `[1, ∞)` (meaningful at `z = 1` for `Re s > 1`, where `Li_s(1) = ζ(s)`). It is defined by
  choosing the continuation when one exists (`z25b_slitContinuation`); the existence, i.e. DLMF's
  statement that `Li_s` is defined by analytic continuation, is the admitted
  `exists_polylog_continuation`. Since `ℂ \ [1, ∞)` is connected, the continuation is unique.
* The Fermi–Dirac and Bose–Einstein integrals `fermiDiracF`, `boseEinsteinG` (25.12.14–25.12.15).

The real dilogarithm `DLMF.Polylog.Real.dilog` and its identities are in `DLMF/Polylog/Dilog.lean`.

**Correction (branch).** 25.12.13 as printed (`ln z` principal) holds for `Im z ≥ 0` only; for
`Im z < 0` it fails (mpmath: `s = 2.5 + 0.2i`, `z = 0.5 - 0.9i`; `s = 0.7 + 0.3i`,
`z = -0.3 - 0.4i`; `s = 2`, `z = -2 - 0.5i`). It holds for all `z ∈ ℂ \ [0, ∞)` with
`ln z` taken with `0 < ph z < 2π` (the branch cut along `[0, ∞)` named by DLMF's domain), i.e.
`ln z/(2πi) = 1/2 + ln(-z)/(2πi)` with principal `ln(-z)`; this form is acquired. We also exclude
`s = 0`, where `1/Γ(s)` vanishes and `ζ(1 - s, ·)` has its pole.
-/

@[expose] public section

open Complex Filter Set MeasureTheory
open scoped Nat Real Topology

noncomputable section

namespace DLMF.Zeta

open DLMF.Confluent (hurwitzZetaComplex)

/-! ### Definitions -/

/-- The cut plane `ℂ \ [1, ∞)`. -/
def z25b_slitOne : Set ℂ := {z | z.im ≠ 0 ∨ z.re < 1}

open scoped Classical in
/-- The analytic continuation of `f` from the open unit disk to `ℂ \ [1, ∞)`, if one exists
(unique, the cut plane being connected); otherwise `f` itself. -/
def z25b_slitContinuation (f : ℂ → ℂ) : ℂ → ℂ :=
  if h : ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F z25b_slitOne ∧ ∀ z, ‖z‖ < 1 → F z = f z then h.choose
  else f

/-- **The polylogarithm series of complex order** `∑_{n≥1} zⁿ/n^s` (DLMF 25.12.10), as a `tsum`
(principal powers `n^s = e^{s ln n}`). Convergent for `|z| < 1`, and for `|z| = 1` when
`Re s > 1`. -/
@[dlmf 25.12.E10]
def polylogSeriesC (s z : ℂ) : ℂ := ∑' n : ℕ, z ^ (n + 1) / ((n : ℂ) + 1) ^ s

open scoped Classical in
/-- **The polylogarithm** `Li_s(z)` (DLMF §25.12(ii), and `Li₂` of §25.12(i)): the analytic
continuation of 25.12.10 to `ℂ \ [1, ∞)` (principal branch); on `[1, ∞)` the value of the series
(so `Li_s(1) = ζ(s)` for `Re s > 1`, and junk on `(1, ∞)`). -/
@[dlmf 25.12.ii]
def polylog (s z : ℂ) : ℂ :=
  if z ∈ z25b_slitOne then z25b_slitContinuation (polylogSeriesC s) z else polylogSeriesC s z

/-! ### Basic properties -/

lemma z25b_mem_slitOne_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : z ∈ z25b_slitOne :=
  Or.inr (lt_of_le_of_lt (re_le_norm z) hz)

lemma z25b_isOpen_slitOne : IsOpen z25b_slitOne :=
  (isOpen_ne_fun continuous_im continuous_const).union
    (isOpen_lt continuous_re continuous_const)

/-- The series 25.12.10 converges absolutely in the open unit disk, for every complex `s`. -/
lemma summable_polylogSeriesC_of_norm_lt_one (s : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
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
theorem summable_polylogSeriesC_of_norm_le_one {s : ℂ} (hs : 1 < s.re) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Summable fun n : ℕ => z ^ (n + 1) / ((n : ℂ) + 1) ^ s := by
  have h := (Real.summable_one_div_nat_add_rpow 1 s.re).mpr hs
  refine Summable.of_norm_bounded h fun n => ?_
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [norm_div, norm_pow, show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
    norm_cpow_eq_rpow_re_of_pos hn, abs_of_pos hn]
  gcongr
  exact pow_le_one₀ (norm_nonneg _) hz

/-- The polylogarithm series from Lerch's series with `a = 1`. -/
lemma q25b_hasSum_polylogSeriesC {s z w : ℂ}
    (h : HasSum (fun n : ℕ => z ^ n / (1 + n) ^ s) w) :
    HasSum (fun n : ℕ => z ^ (n + 1) / ((n : ℂ) + 1) ^ s) (z * w) :=
  (h.mul_left z).congr_fun fun n => by rw [pow_succ, add_comm (1 : ℂ)]; ring

/-- **Continuation of `Li_s`** (DLMF §25.12(ii)): for every complex `s` the series 25.12.10 extends
analytically from the unit disk to `ℂ \ [1, ∞)`. -/
@[dlmf 25.12.ii]
theorem exists_polylog_continuation (s : ℂ) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F z25b_slitOne ∧ ∀ z, ‖z‖ < 1 → F z = polylogSeriesC s z := by
  obtain ⟨F, hF⟩ := q25b_exists_isLerchCont s 1
  exact ⟨fun z => z * F z, analyticOnNhd_id.mul hF.1, fun z hz =>
    (q25b_hasSum_polylogSeriesC (hF.2 z hz)).tsum_eq.symm⟩

lemma z25b_polylog_spec (s : ℂ) :
    AnalyticOnNhd ℂ (z25b_slitContinuation (polylogSeriesC s)) z25b_slitOne ∧
      ∀ z, ‖z‖ < 1 → z25b_slitContinuation (polylogSeriesC s) z = polylogSeriesC s z := by
  have h := exists_polylog_continuation s
  unfold z25b_slitContinuation
  simp only [h, ↓reduceDIte]
  exact h.choose_spec

/-- On the cut plane, `Li_s(z) = z Φ(z, s, 1)` for any continuation `Φ(·, s, 1)` of Lerch's
series. -/
lemma q25b_polylog_eq_mul {s : ℂ} {F : ℂ → ℂ} (hF : q25b_IsLerchCont s 1 F) {z : ℂ}
    (hz : z ∈ z25b_slitOne) : polylog s z = z * F z := by
  simp only [polylog, hz, ↓reduceIte]
  refine q25b_eqOn_slit (z25b_polylog_spec s).1 (analyticOnNhd_id.mul hF.1) (fun w hw => ?_) hz
  rw [(z25b_polylog_spec s).2 w hw]
  exact (q25b_hasSum_polylogSeriesC (hF.2 w hw)).tsum_eq

/-- `z ∈ ℂ \ [1, ∞)` for `|z| ≤ 1`, `z ≠ 1`. -/
lemma q25b_mem_slitOne_of_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) (h1 : z ≠ 1) : z ∈ z25b_slitOne := by
  by_contra h
  simp only [z25b_slitOne, mem_ofPred_eq, not_or, not_lt, ne_eq, not_not] at h
  have hre : z.re ≤ 1 := (re_le_norm z).trans hz
  exact h1 (Complex.ext (by simp; linarith [h.2]) (by simp [h.1]))

/-- `Li_s(z) = (z/Γ(s)) ∫_0^∞ x^{s-1}e^{-x}/(1 - z e^{-x}) dx` (the form 25.14.5 of 25.12.11). -/
lemma q25b_polylog_eq_lerchInt {s z : ℂ}
    (h : (0 < s.re ∧ z ∈ z25b_slitOne) ∨ (1 < s.re ∧ z = 1)) :
    polylog s z = z * ((Gamma s)⁻¹ * q25b_lerchInt s 1 z) := by
  obtain ⟨F, hF⟩ := q25b_exists_isLerchCont s 1
  rcases h with ⟨hs, hz⟩ | ⟨hs, rfl⟩
  · rw [q25b_polylog_eq_mul hF hz, hF.eq_lerchInt hs one_pos hz]
  · have h1 : (1 : ℂ) ∉ z25b_slitOne := by simp [z25b_slitOne]
    simp only [polylog, h1, ↓reduceIte]
    exact (q25b_hasSum_polylogSeriesC
      (q25b_hasSum_lerchInt (z := 1) (by linarith) one_pos (Or.inr ⟨by simp, hs⟩))).tsum_eq

/-- **The series in the unit disk** (DLMF 25.12.10, 25.12.1 for `s = 2`): for `|z| < 1`,
`Li_s(z) = ∑_{n≥1} zⁿ/n^s`. -/
@[dlmf 25.12.E10]
theorem hasSum_polylog {s z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => z ^ (n + 1) / ((n : ℂ) + 1) ^ s) (polylog s z) := by
  simp only [polylog, z25b_mem_slitOne_of_norm_lt_one hz, ↓reduceIte]
  rw [(z25b_polylog_spec s).2 z hz]
  exact (summable_polylogSeriesC_of_norm_lt_one s hz).hasSum

/-- **Analyticity** (DLMF §25.12(i)–(ii)): `Li_s` is analytic on `ℂ \ [1, ∞)`. -/
@[dlmf 25.12.ii]
theorem analyticOnNhd_polylog (s : ℂ) : AnalyticOnNhd ℂ (polylog s) z25b_slitOne := by
  refine (z25b_polylog_spec s).1.congr z25b_isOpen_slitOne fun z hz => ?_
  simp only [polylog, hz, ↓reduceIte]

/-- `Li_s` is differentiable on the cut plane; in terms of `Φ(z, s, 1) = F z`,
`Li_s'(z) = F z + z F'(z)`. -/
lemma q25b_hasDerivAt_polylog (s : ℂ) {z : ℂ} (hz : z ∈ z25b_slitOne) :
    ∃ F : ℂ → ℂ, q25b_IsLerchCont s 1 F ∧ HasDerivAt (polylog s) (F z + z * deriv F z) z := by
  obtain ⟨F, hF⟩ := q25b_exists_isLerchCont s 1
  refine ⟨F, hF, ?_⟩
  have hev : polylog s =ᶠ[𝓝 z] fun w => w * F w := by
    filter_upwards [z25b_isOpen_slitOne.mem_nhds hz] with w hw
    exact q25b_polylog_eq_mul hF hw
  have hd : HasDerivAt (fun w => w * F w) (1 * F z + z * deriv F z) z :=
    (hasDerivAt_id z).mul ((hF.1 z hz).differentiableAt.hasDerivAt)
  rw [one_mul] at hd
  exact hd.congr_of_eventuallyEq hev

/-- `z Li_s'(z) = Li_{s-1}(z)` on the cut plane. -/
lemma q25b_mul_deriv_polylog (s : ℂ) {z : ℂ} (hz : z ∈ z25b_slitOne) :
    z * deriv (polylog s) z = polylog (s - 1) z := by
  obtain ⟨F, hF, hd⟩ := q25b_hasDerivAt_polylog s hz
  have h1 : ∀ n : ℕ, (1 : ℂ) + n ≠ 0 := fun n => by
    have : (0 : ℝ) < 1 + n := by positivity
    exact_mod_cast this.ne'
  rw [hd.deriv, q25b_polylog_eq_mul (q25b_isLerchCont_sub_one h1 hF) hz]
  ring

/-- `Li_1(z) = -ln(1 - z)` on the cut plane. -/
lemma q25b_polylog_one_eq {z : ℂ} (hz : z ∈ z25b_slitOne) :
    polylog 1 z = -Complex.log (1 - z) := by
  have hmem : ∀ w ∈ z25b_slitOne, 1 - w ∈ slitPlane := fun w hw => by
    rcases hw with h | h
    · right; simpa using h
    · left; simp; linarith
  refine q25b_eqOn_slit (F := polylog 1) (G := fun z => -Complex.log (1 - z))
    (analyticOnNhd_polylog 1) (fun w hw => ((analyticAt_clog (hmem w hw)).comp
      (analyticAt_const.sub analyticAt_id)).neg) (fun w hw => ?_) hz
  have h := hasSum_polylog (s := 1) hw
  simp only [cpow_one] at h
  exact h.unique (Complex.hasSum_taylorSeries_neg_log' hw)

/-- `Li₂'(z) = -ln(1 - z)/z` on the cut plane, `z ≠ 0`. -/
lemma q25b_hasDerivAt_polylog_two {z : ℂ} (hz : z ∈ z25b_slitOne) (hz0 : z ≠ 0) :
    HasDerivAt (polylog 2) (-Complex.log (1 - z) / z) z := by
  obtain ⟨F, hF, hd⟩ := q25b_hasDerivAt_polylog 2 hz
  have h := q25b_mul_deriv_polylog 2 hz
  rw [hd.deriv, show (2 : ℂ) - 1 = 1 by norm_num, q25b_polylog_one_eq hz] at h
  rw [← h, mul_div_cancel_left₀ _ hz0]
  exact hd

/-- `Li₂'(0) = 1`. -/
lemma q25b_hasDerivAt_polylog_two_zero : HasDerivAt (polylog 2) 1 0 := by
  obtain ⟨F, hF, hd⟩ :=
    q25b_hasDerivAt_polylog 2 (z25b_mem_slitOne_of_norm_lt_one (z := 0) (by simp))
  have h0 : HasSum (fun n : ℕ => (0 : ℂ) ^ n / (1 + n) ^ (2 : ℂ)) 1 := by
    convert hasSum_ite_eq 0 (1 : ℂ) using 1
    funext n
    rcases n with _ | n <;> simp
  rw [zero_mul, add_zero, (hF.2 0 (by simp)).unique h0] at hd
  exact hd

open DLMF.Polylog in
/-- **Bridge to the real dilogarithm**: `Li₂(x) = DLMF.Polylog.Real.dilog x` for real `x < 1`. -/
theorem q25b_polylog_two_ofReal {x : ℝ} (hx : x < 1) :
    polylog 2 x = (Real.dilog x : ℂ) := by
  have hmem : ∀ y : ℝ, y < 1 → (y : ℂ) ∈ z25b_slitOne := fun y hy => Or.inr (by simpa using hy)
  have hder : ∀ y : ℝ, y < 1 → HasDerivAt (fun t : ℝ => polylog 2 t - (Real.dilog t : ℂ)) 0 y := by
    intro y hy
    have h2 : HasDerivAt (fun t : ℝ => (Real.dilog t : ℂ)) (dilogKernel y : ℂ) y :=
      (Real.hasDerivAt_dilog hy).ofReal_comp
    have h1 : HasDerivAt (fun t : ℝ => polylog 2 t) (dilogKernel y : ℂ) y := by
      rcases eq_or_ne y 0 with rfl | hy0
      · rw [dilogKernel_zero, ofReal_one]
        have := q25b_hasDerivAt_polylog_two_zero.comp_ofReal (z := (0 : ℝ))
        exact this
      · have hc := (q25b_hasDerivAt_polylog_two (hmem y hy)
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

/-- **The series on the unit circle** (DLMF §25.12(ii), 25.12.1 for `s = 2`): for `Re s > 1` and
`|z| = 1`, `Li_s(z) = ∑ zⁿ/n^s` (Abel's theorem; at `z = 1` this is the definition). -/
@[dlmf 25.12.E10]
theorem hasSum_polylog_of_norm_eq_one {s z : ℂ} (hs : 1 < s.re) (hz : ‖z‖ = 1) :
    HasSum (fun n : ℕ => z ^ (n + 1) / ((n : ℂ) + 1) ^ s) (polylog s z) := by
  by_cases h1 : z = 1
  · subst h1
    have h1' : (1 : ℂ) ∉ z25b_slitOne := by simp [z25b_slitOne]
    simp only [polylog, h1', ↓reduceIte]
    exact (summable_polylogSeriesC_of_norm_le_one hs (by simp)).hasSum
  · obtain ⟨F, hF⟩ := q25b_exists_isLerchCont s 1
    have hzs := q25b_mem_slitOne_of_norm_le_one hz.le h1
    rw [q25b_polylog_eq_mul hF hzs]
    exact q25b_hasSum_polylogSeriesC (hF.hasSum_of_norm_le_one hs hz.le hzs)

/-- **`Li_s(1) = ζ(s)`** (DLMF §25.12(ii)) for `Re s > 1`. -/
@[dlmf 25.12.ii]
theorem polylog_one {s : ℂ} (hs : 1 < s.re) : polylog s 1 = riemannZeta s := by
  have h1 : (1 : ℂ) ∉ z25b_slitOne := by simp [z25b_slitOne]
  simp only [polylog, h1, ↓reduceIte]
  rw [polylogSeriesC, zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  simp

/-- For natural order the series is the project's `DLMF.Polylog.polylogSeries`. -/
theorem polylogSeriesC_natCast (n : ℕ) (z : ℂ) :
    polylogSeriesC n z = DLMF.Polylog.polylogSeries n z := by
  simp only [polylogSeriesC, DLMF.Polylog.polylogSeries, cpow_natCast]

/-- Bridge: on the closed unit disk, `Li_n(z)` for natural `n ≥ 2` is
`DLMF.Polylog.polylogSeries n z`. -/
theorem polylog_natCast_eq_polylogSeries {n : ℕ} (hn : 2 ≤ n) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    polylog n z = DLMF.Polylog.polylogSeries n z := by
  rw [← polylogSeriesC_natCast, polylogSeriesC]
  rcases hz.lt_or_eq with h | h
  · exact (hasSum_polylog h).tsum_eq.symm
  · exact (hasSum_polylog_of_norm_eq_one (by simp; exact_mod_cast hn) h).tsum_eq.symm

/-- Real points accumulate: a property holding near `x₀` on `ℝ` holds frequently near `x₀`
in `ℂ`. -/
lemma q25b_frequently_ofReal {P : ℂ → Prop} {x₀ : ℝ} (h : ∀ᶠ x : ℝ in 𝓝 x₀, P (x : ℂ)) :
    ∃ᶠ z in 𝓝[≠] (x₀ : ℂ), P z := by
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] x₀) (𝓝[≠] (x₀ : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨(continuous_ofReal.tendsto x₀).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun x hx => ofReal_injective.ne hx⟩
  exact ht.frequently (h.filter_mono nhdsWithin_le_nhds).frequently

lemma q25b_analyticAt_polylog_two_comp {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (hz : f z ∈ z25b_slitOne) : AnalyticAt ℂ (fun w => polylog 2 (f w)) z :=
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
  by_cases hzs : z ∈ z25b_slitOne
  · have hmem : ∀ u ∈ Icc (0 : ℝ) 1, (u : ℂ) * z ∈ z25b_slitOne := fun u hu => by
      have := q25b_starConvex_slit hzs (a := 1 - u) (b := u) (by linarith [hu.2]) hu.1
        (by ring)
      have h2 : (u : ℂ) * z ∈ q25b_slit := by simpa [Complex.real_smul] using this
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
    rw [(q25b_hasDerivAt_polylog_two (hmem u ⟨hu.1.le, hu.2⟩) (mul_ne_zero hu0 hz0)).deriv]
    field_simp
  · have hz1 : z = 1 := by
      simp only [z25b_slitOne, Set.mem_ofPred_eq, not_or, not_lt, ne_eq, not_not] at hzs
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
theorem polylog_two_add_polylog_two_div_sub_one {z : ℂ} (hz : z ∈ z25b_slitOne) :
    polylog 2 z + polylog 2 (z / (z - 1)) = -(1 / 2) * Complex.log (1 - z) ^ 2 := by
  have hne : ∀ w ∈ z25b_slitOne, w - 1 ≠ 0 := fun w hw h => by
    rw [sub_eq_zero] at h; subst h; rcases hw with h | h <;> simp at h
  have hmem : ∀ w ∈ z25b_slitOne, w / (w - 1) ∈ z25b_slitOne := by
    intro w hw
    by_contra hc
    simp only [z25b_slitOne, Set.mem_ofPred_eq, not_or, not_lt, ne_eq, not_not] at hc
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
  have hlog : ∀ w ∈ z25b_slitOne, 1 - w ∈ slitPlane := fun w hw => by
    rcases hw with h | h
    · right; simpa using h
    · left; simp; linarith
  have hf : AnalyticOnNhd ℂ (fun w => polylog 2 w + polylog 2 (w / (w - 1))) z25b_slitOne :=
    fun w hw => (analyticOnNhd_polylog 2 w hw).add (q25b_analyticAt_polylog_two_comp
      (analyticAt_id.div (analyticAt_id.sub analyticAt_const) (hne w hw)) (hmem w hw))
  have hg : AnalyticOnNhd ℂ (fun w => -(1 / 2) * Complex.log (1 - w) ^ 2) z25b_slitOne :=
    fun w hw => analyticAt_const.mul
      (((analyticAt_clog (hlog w hw)).comp (analyticAt_const.sub analyticAt_id)).pow 2)
  refine hf.eqOn_of_preconnected_of_frequently_eq hg q25b_isPreconnected_slit
    (z₀ := ((0 : ℝ) : ℂ)) (Or.inr (by simp)) (q25b_frequently_ofReal (x₀ := 0) ?_) hz
  filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)] with x hx
  have hx' : x < 1 := hx
  have h := DLMF.Polylog.Real.dilog_add_dilog_div_sub_one hx'
  have hd : x / (x - 1) < 1 := by
    rw [div_lt_one_of_neg (by linarith)]; linarith
  rw [show (x : ℂ) / (x - 1) = ((x / (x - 1) : ℝ) : ℂ) by push_cast; ring,
    q25b_polylog_two_ofReal hx', q25b_polylog_two_ofReal hd,
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
  have hU1 : ∀ w ∈ U, w ∈ z25b_slitOne := fun w hw => by
    rcases hw with h | h; exacts [Or.inl h, Or.inr (by linarith)]
  have hU2 : ∀ w ∈ U, 1 / w ∈ z25b_slitOne := fun w hw => by
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
    (analyticOnNhd_polylog 2 w (hU1 w hw)).add (q25b_analyticAt_polylog_two_comp
      (analyticAt_const.div analyticAt_id (hU0 w hw)) (hU2 w hw))
  have hg : AnalyticOnNhd ℂ (fun w => -(π : ℂ) ^ 2 / 6 - (1 / 2) * Complex.log (-w) ^ 2) U :=
    fun w hw => analyticAt_const.sub (analyticAt_const.mul
      (((analyticAt_clog (hU3 w hw)).comp analyticAt_id.neg).pow 2))
  refine hf.eqOn_of_preconnected_of_frequently_eq hg hUc (z₀ := ((-1 : ℝ) : ℂ))
    (Or.inr (by norm_num)) (q25b_frequently_ofReal (x₀ := -1) ?_) hz
  filter_upwards [Iio_mem_nhds (by norm_num : (-1 : ℝ) < 0)] with x hx
  have hx' : x < 0 := hx
  have h := DLMF.Polylog.Real.dilog_add_dilog_recip hx'
  rw [show (1 : ℂ) / x = ((x⁻¹ : ℝ) : ℂ) by push_cast; ring,
    q25b_polylog_two_ofReal (by linarith), q25b_polylog_two_ofReal (by
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
  have hU1 : ∀ w ∈ U, w ∈ z25b_slitOne := fun w hw => by
    rcases hw with h | h; exacts [Or.inl h, Or.inr h.2]
  have hU2 : ∀ w ∈ U, 1 - w ∈ z25b_slitOne := fun w hw => by
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
      (q25b_analyticAt_polylog_two_comp (analyticAt_const.sub analyticAt_id) (hU2 w hw))
  have hg : AnalyticOnNhd ℂ (fun w => (π : ℂ) ^ 2 / 6 - Complex.log w * Complex.log (1 - w)) U :=
    fun w hw => analyticAt_const.sub ((analyticAt_clog (hU3 w hw)).mul
      ((analyticAt_clog (hU4 w hw)).comp (analyticAt_const.sub analyticAt_id)))
  refine hf.eqOn_of_preconnected_of_frequently_eq hg hUc (z₀ := ((1 / 2 : ℝ) : ℂ))
    (Or.inr (by norm_num)) (q25b_frequently_ofReal (x₀ := 1 / 2) ?_) hz
  filter_upwards [Ioo_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)]
    with x hx
  have h := DLMF.Polylog.Real.dilog_add_dilog_one_sub hx
  rw [show (1 : ℂ) - x = ((1 - x : ℝ) : ℂ) by push_cast; ring,
    q25b_polylog_two_ofReal hx.2, q25b_polylog_two_ofReal (by linarith [hx.1]),
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
lemma s25b_norm_one_sub_exp {x : ℝ} (hx0 : 0 < x) (hx1 : x < 2 * π) :
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
lemma s25b_hasDerivAt_im_polylog_two_exp {x : ℝ} (hx0 : 0 < x) (hx1 : x < 2 * π) :
    HasDerivAt (fun y : ℝ => (polylog 2 (cexp (y * I))).im)
      (-Real.log (2 * Real.sin (x / 2))) x := by
  set z := cexp (x * I)
  have hz1 : ‖z‖ = 1 := norm_exp_ofReal_mul_I x
  have hzne : z ≠ 1 := by
    intro h
    have := s25b_norm_one_sub_exp hx0 hx1
    rw [show cexp (x * I) = z from rfl, h, sub_self, norm_zero] at this
    have hs : 0 < Real.sin (x / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    linarith
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have hmem := q25b_mem_slitOne_of_norm_le_one hz1.le hzne
  have he : HasDerivAt (fun y : ℝ => cexp (y * I)) (z * I) x := by
    have := ((hasDerivAt_id x).ofReal_comp.mul_const I).cexp
    simpa using this
  have hg := (q25b_hasDerivAt_polylog_two hmem hz0).comp x he
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hg
  convert him using 1
  · rfl
  show _ = (-Complex.log (1 - z) / z * (z * I)).im
  rw [show -Complex.log (1 - z) / z * (z * I) = -Complex.log (1 - z) * I by field_simp]
  simp [Complex.log_re, z, s25b_norm_one_sub_exp hx0 hx1]

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
    (fun x hx => hFeq ▸ s25b_hasDerivAt_im_polylog_two_exp hx.1 (hx.2.trans_le h1)) hint
  have hF0 : F 0 = 0 := by simp [F]
  rw [hF0, sub_zero, intervalIntegral.integral_neg] at hI
  rw [hI]
  exact hsum θ

/-! ### §25.12(ii) Polylogarithms: further properties -/

/-- **Integral representation** (DLMF 25.12.11): `Li_s(z) = (z/Γ(s)) ∫_0^∞ x^{s-1}/(e^x - z) dx`,
valid for `Re s > 0` and `|ph(1-z)| < π` (i.e. `z ∈ ℂ \ [1, ∞)`), or `Re s > 1` and `z = 1`. -/
@[dlmf 25.12.E11]
theorem polylog_eq_integral {s z : ℂ}
    (h : (0 < s.re ∧ z ∈ z25b_slitOne) ∨ (1 < s.re ∧ z = 1)) :
    polylog s z = z / Gamma s * ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) / (Real.exp x - z) := by
  rw [q25b_polylog_eq_lerchInt h, q25b_lerchInt, div_eq_mul_inv, mul_assoc]
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
`Li_s(z) = Γ(1-s)(ln(1/z))^{s-1} + ∑_{n≥0} ζ(s-n)(ln z)ⁿ/n!`. We take `z ∈ ℂ \ [1, ∞)`, `z ≠ 0`
(domain qualification: on the cut `(1, e^{2π})` the principal branch of `Li_s` is not defined, and
at `z = 1` with `Re s ≤ 1` the left side is infinite). -/
@[dlmf 25.12.E12]
theorem hasSum_polylog_log {s z : ℂ} (hs : ∀ n : ℕ, s ≠ n + 1) (hz : z ∈ z25b_slitOne)
    (hz0 : z ≠ 0) (hlog : ‖Complex.log z‖ < 2 * π) :
    HasSum (fun n : ℕ => riemannZeta (s - n) * Complex.log z ^ n / n !)
      (polylog s z - Gamma (1 - s) * Complex.log (1 / z) ^ (s - 1)) := by
  sorry

/-- **Inversion formula** (DLMF 25.12.13, **branch corrected**): for `z ∈ ℂ \ [0, ∞)` and `s ≠ 0`,
`Li_s(z) + e^{πis} Li_s(1/z) = ((2π)^s e^{πis/2}/Γ(s)) ζ(1-s, ln z/(2πi))` with `0 < ph z < 2π`,
i.e. `ln z/(2πi) = 1/2 + ln(-z)/(2πi)`, `ln(-z)` principal. (With principal `ln z` the printed
identity fails for `Im z < 0`; see the module docstring.) -/
@[dlmf 25.12.E13]
theorem polylog_add_exp_mul_polylog_inv {s z : ℂ} (hs : s ≠ 0) (hz : z.im ≠ 0 ∨ z.re < 0) :
    polylog s z + cexp (π * I * s) * polylog s (1 / z) =
      (2 * π) ^ s * cexp (π * I * s / 2) / Gamma s *
        hurwitzZetaComplex (1 - s) (1 / 2 + Complex.log (-z) / (2 * π * I)) := by
  sorry

/-! ### §25.12(iii) Fermi–Dirac and Bose–Einstein integrals -/

/-- **Fermi–Dirac integral** (DLMF 25.12.14): `F_s(x) = (1/Γ(s+1)) ∫_0^∞ t^s/(e^{t-x} + 1) dt`,
`s > -1`. -/
@[dlmf 25.12.E14]
def fermiDiracF (s x : ℝ) : ℝ :=
  1 / Real.Gamma (s + 1) * ∫ t in Ioi (0 : ℝ), t ^ s / (Real.exp (t - x) + 1)

/-- **Bose–Einstein integral** (DLMF 25.12.15): `G_s(x) = (1/Γ(s+1)) ∫_0^∞ t^s/(e^{t-x} - 1) dt`,
for `s > -1`, `x < 0`, or `s > 0`, `x ≤ 0`. -/
@[dlmf 25.12.E15]
def boseEinsteinG (s x : ℝ) : ℝ :=
  1 / Real.Gamma (s + 1) * ∫ t in Ioi (0 : ℝ), t ^ s / (Real.exp (t - x) - 1)

/-- **`F_s` as a polylogarithm** (DLMF 25.12.16): `F_s(x) = -Li_{s+1}(-e^x)` for `s > -1`. -/
@[dlmf 25.12.E16]
theorem fermiDiracF_eq_polylog {s : ℝ} (hs : -1 < s) (x : ℝ) :
    (fermiDiracF s x : ℂ) = -polylog (s + 1) (-Real.exp x) := by
  have hz : (-(Real.exp x : ℂ)) ∈ z25b_slitOne := Or.inr (by
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
  have h' : (0 < ((s : ℂ) + 1).re ∧ (Real.exp x : ℂ) ∈ z25b_slitOne) ∨
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
