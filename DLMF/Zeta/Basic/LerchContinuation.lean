/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Basic.Polylog
public import DLMFMathlib.Analysis.Asymptotics.WatsonSector
public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Analytic continuation of Lerch's series

For all complex `s` and `a`, the power series `∑_{n≥0} zⁿ/(a+n)^s` (principal powers) extends
from the open unit disk to an analytic function on the cut plane `ℂ \ [1, ∞)` (DLMF §25.14(i),
§25.12(ii)). These continuations underlie `DLMF.Zeta.polylog` and `DLMF.Zeta.lerchPhi`.

## Main definitions

The cut plane `slitOne` is defined in `DLMF.Zeta.Basic.Polylog`.

* `lerchIntegral`: the integral `∫_0^∞ x^{s-1} e^{-ax}/(1 - z e^{-x}) dx` of DLMF 25.14.5
  (without the factor `1/Γ(s)`).
* `IsLerchContinuation`: `F` is analytic on the cut plane and sums `∑ zⁿ/(a+n)^s` on the open
  unit disk.

## Main results

* `isPreconnected_slitOne`, `eqOn_slitOne_of_eq_on_ball`: the cut plane is connected (star-shaped
  about `0`), so continuations from the unit disk are unique.
* `hasSum_lerch_lerchIntegral`: for `Re a > 0`, `Re s > 0` the integral 25.14.5 sums the series.
* `isLerchContinuation_sub_one`: lowering the order, `Φ(z, s-1, a) = (z ∂_z + a) Φ(z, s, a)`.
* `hasSum_lerch_of_hasSum_add_natCast`: shifting the parameter `a` (DLMF 25.14.4).
* `exists_isLerchContinuation`: the continuation exists for all complex `s` and `a`.
* `IsLerchContinuation.eqOn`, `IsLerchContinuation.eq_lerchInt`: uniqueness, and the continuation
  is the integral 25.14.5 for `Re s > 0`, `Re a > 0`.
* `IsLerchContinuation.hasSum_of_norm_le_one`: for `Re s > 1` the continuation is the sum of the
  series on the closed unit disk (Abel's theorem).
-/

@[expose] public section

open Complex Filter Set MeasureTheory Metric
open scoped Topology Real

noncomputable section

namespace DLMF.Zeta

/-- The indicated domain is open: `IsOpen slitOne`. -/
private lemma isOpen_slitOne' : IsOpen slitOne :=
  (isOpen_ne_fun continuous_im continuous_const).union
    (isOpen_lt continuous_re continuous_const)

/-- Formula under the stated hypotheses: `z ∈ slitOne`. -/
private lemma mem_slitOne_of_norm_lt_one' {z : ℂ} (hz : ‖z‖ < 1) : z ∈ slitOne :=
  Or.inr (lt_of_le_of_lt (re_le_norm z) hz)

/-- The stated relation follows from the given hypotheses: `ball (0 : ℂ) 1 ⊆ slitOne`. -/
private lemma ball_subset_slitOne : ball (0 : ℂ) 1 ⊆ slitOne := fun z hz =>
  mem_slitOne_of_norm_lt_one' (by simpa using hz)

/-- The cut plane is star-shaped about `0`. -/
theorem starConvex_slitOne : StarConvex ℝ 0 slitOne := by
  intro y hy p q hp hq hpq
  simp only [smul_zero, zero_add]
  rcases eq_or_lt_of_le hq with hq0 | hq0
  · subst hq0; right; simp
  rcases hy with h | h
  · left
    simp only [Complex.real_smul, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
    exact mul_ne_zero hq0.ne' h
  · right
    simp only [Complex.real_smul, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    have hq1 : q ≤ 1 := by linarith
    rcases le_or_gt y.re 0 with h0 | h0
    · nlinarith
    · nlinarith

/-- The stated relation follows from the given hypotheses: `IsPreconnected slitOne`. -/
theorem isPreconnected_slitOne : IsPreconnected slitOne :=
  (starConvex_slitOne.isPathConnected (Or.inr (by simp))).isConnected.isPreconnected

/-- **Uniqueness of the continuation**: two analytic functions on the cut plane that agree on the
unit disk agree on the cut plane. -/
theorem eqOn_slitOne_of_eq_on_ball {F G : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F slitOne)
    (hG : AnalyticOnNhd ℂ G slitOne) (h : ∀ z, ‖z‖ < 1 → F z = G z) :
    EqOn F G slitOne := by
  refine hF.eqOn_of_preconnected_of_eventuallyEq hG isPreconnected_slitOne
    (mem_slitOne_of_norm_lt_one' (z := 0) (by simp)) ?_
  filter_upwards [ball_mem_nhds (0 : ℂ) one_pos] with z hz
  exact h z (by simpa using hz)

/-- `1 - z t ≠ 0` for `z` in the cut plane and `0 ≤ t ≤ 1`. -/
private lemma one_sub_mul_ofReal_ne_zero {z : ℂ} (hz : z ∈ slitOne) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    1 - z * t ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [sub_re, one_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, zero_re, sub_im,
    one_im, mul_im, zero_add, zero_im, zero_sub, neg_eq_zero] at hre him
  have ht0 : t ≠ 0 := by rintro rfl; simp at hre
  rcases hz with h1 | h1
  · exact h1 ((mul_eq_zero.mp him).resolve_right ht0)
  · rcases le_or_gt z.re 0 with h2 | h2
    · nlinarith [mul_nonneg (neg_nonneg.mpr h2) ht.1]
    · nlinarith [mul_nonneg h2.le (sub_nonneg.mpr ht.2)]

/-- A uniform lower bound for `‖1 - z t‖`, `0 ≤ t ≤ 1`, near a point of the cut plane. -/
private lemma exists_le_norm_one_sub_mul_ofReal {z₀ : ℂ} (hz₀ : z₀ ∈ slitOne) :
    ∃ ε > 0, closedBall z₀ ε ⊆ slitOne ∧ ∃ c > 0, ∀ z ∈ closedBall z₀ ε,
      ∀ t ∈ Icc (0 : ℝ) 1, c ≤ ‖1 - z * t‖ := by
  obtain ⟨ε, hε, hεs⟩ := Metric.isOpen_iff.mp isOpen_slitOne' z₀ hz₀
  have hsub : closedBall z₀ (ε / 2) ⊆ slitOne :=
    (closedBall_subset_ball (by linarith)).trans hεs
  refine ⟨ε / 2, by positivity, hsub, ?_⟩
  have hK : IsCompact (closedBall z₀ (ε / 2) ×ˢ Icc (0 : ℝ) 1) :=
    (isCompact_closedBall z₀ _).prod isCompact_Icc
  have hne : (closedBall z₀ (ε / 2) ×ˢ Icc (0 : ℝ) 1).Nonempty :=
    ⟨(z₀, 0), mem_closedBall_self (by positivity), by simp⟩
  have hc : ContinuousOn (fun p : ℂ × ℝ => ‖1 - p.1 * p.2‖) (closedBall z₀ (ε / 2) ×ˢ
      Icc (0 : ℝ) 1) := by fun_prop
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hne hc
  refine ⟨‖1 - p.1 * p.2‖, norm_pos_iff.mpr (one_sub_mul_ofReal_ne_zero (hsub hp.1) hp.2),
    fun z hz t ht => ?_⟩
  exact hmin (show (z, t) ∈ closedBall z₀ (ε / 2) ×ˢ Icc (0 : ℝ) 1 from ⟨hz, ht⟩)

/-! ### The integral 25.14.5 -/

/-- The integral `∫_0^∞ x^{s-1} e^{-ax}/(1 - z e^{-x}) dx` of DLMF 25.14.5 (without `1/Γ(s)`). -/
def lerchIntegral (s a z : ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * cexp (-(a * x)) / (1 - z * cexp (-(x : ℂ)))

/-- Identity under the stated parameter and domain assumptions: `cexp (-(x : ℂ)) = ((Real.exp (-x)
: ℝ) : ℂ)`. -/
private lemma exp_neg_ofReal_eq_ofReal (x : ℝ) : cexp (-(x : ℂ)) = ((Real.exp (-x) : ℝ) : ℂ) := by
  rw [ofReal_exp, ofReal_neg]

/-- Identity under the stated parameter and domain assumptions: `‖(x : ℂ) ^ (s - 1) * cexp (-(b *
x))‖ = x ^ (s.re - 1) * Real.exp (-(b.re * x))`. -/
theorem norm_cpow_mul_exp_neg {s b : ℂ} {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ (s - 1) * cexp (-(b * x))‖ = x ^ (s.re - 1) * Real.exp (-(b.re * x)) := by
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx, norm_exp]
  simp

/-- The kernel `(fun x : ℝ => x ^ (σ - 1) * Real.exp (-(β * x)))` is integrable on `(Ioi 0)`. -/
theorem integrableOn_rpow_mul_exp_neg {σ β : ℝ} (hσ : 0 < σ) (hβ : 0 < β) :
    IntegrableOn (fun x : ℝ => x ^ (σ - 1) * Real.exp (-(β * x))) (Ioi 0) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hσ hβ]
  exact mul_ne_zero (by positivity) (Real.Gamma_pos_of_pos hσ).ne'

/-- Identity under the stated parameter and domain assumptions: `AEStronglyMeasurable (fun x : ℝ
=> (x : ℂ) ^ (s - 1) * cexp (-(b * x))) (volume.restrict (Ioi 0))`. -/
theorem aestronglyMeasurable_cpow_mul_exp_neg (s b : ℂ) :
    AEStronglyMeasurable (fun x : ℝ => (x : ℂ) ^ (s - 1) * cexp (-(b * x)))
      (volume.restrict (Ioi 0)) := by
  refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
  intro x hx
  refine ContinuousAt.continuousWithinAt ?_
  refine ContinuousAt.mul ?_ (by fun_prop)
  exact (continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt hx)))

/-- The kernel `(fun x : ℝ => (x : ℂ) ^ (s - 1) * cexp (-(b * x)))` is integrable on `(Ioi 0)`. -/
theorem integrableOn_cpow_mul_exp_neg {s b : ℂ} (hs : 0 < s.re) (hb : 0 < b.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * cexp (-(b * x))) (Ioi 0) := by
  refine (integrableOn_rpow_mul_exp_neg hs hb).mono'
    (aestronglyMeasurable_cpow_mul_exp_neg s b) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_cpow_mul_exp_neg hx]

/-- The integral 25.14.5 is analytic in `z` on the cut plane, for `Re s > 0`, `Re a > 0`. -/
private lemma analyticOnNhd_lerchIntegral {s a : ℂ} (hs : 0 < s.re) (ha : 0 < a.re) :
    AnalyticOnNhd ℂ (lerchIntegral s a) slitOne := by
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_slitOne'
  have hx01 : ∀ x : ℝ, 0 < x → Real.exp (-x) ∈ Icc (0 : ℝ) 1 := fun x hx =>
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩
  refine Complex.differentiableOn_integral_Ioi_of_locally_dominated isOpen_slitOne' 0
    (fun z hz => ?_) ?_ fun z₀ hz₀ => ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro x hx
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.div (ContinuousAt.mul ?_ (by fun_prop)) (by fun_prop) ?_
    · exact continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt hx))
    · rw [exp_neg_ofReal_eq_ofReal]; exact one_sub_mul_ofReal_ne_zero hz (hx01 x hx)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (differentiableAt_const _).div (by fun_prop) ?_
    rw [exp_neg_ofReal_eq_ofReal]; exact one_sub_mul_ofReal_ne_zero hz (hx01 x hx)
  · obtain ⟨ε, hε, -, c, hc, hcb⟩ := exists_le_norm_one_sub_mul_ofReal hz₀
    refine ⟨closedBall z₀ ε, closedBall_mem_nhds z₀ hε,
      fun x => x ^ (s.re - 1) * Real.exp (-(a.re * x)) / c,
      (integrableOn_rpow_mul_exp_neg hs ha).div_const c, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro z hz
    have hb := hcb z hz _ (hx01 x hx)
    rw [norm_div, norm_cpow_mul_exp_neg hx, exp_neg_ofReal_eq_ofReal]
    exact div_le_div_of_nonneg_left
      (mul_nonneg (Real.rpow_nonneg (le_of_lt hx) _) (Real.exp_pos _).le) hc hb

/-- **The series by the integral** (DLMF 25.14.5 read backwards): for `Re a > 0`, `Re s > 0` and
`|z| < 1` (or `|z| ≤ 1` when `Re s > 1`), `∑ zⁿ/(a+n)^s = (1/Γ(s)) ∫_0^∞ …`. -/
theorem hasSum_lerch_lerchIntegral {s a z : ℂ} (hs : 0 < s.re) (ha : 0 < a.re)
    (hz : ‖z‖ < 1 ∨ (‖z‖ ≤ 1 ∧ 1 < s.re)) :
    HasSum (fun n : ℕ => z ^ n / (a + n) ^ s) ((Gamma s)⁻¹ * lerchIntegral s a z) := by
  have hz1 : ‖z‖ ≤ 1 := by rcases hz with h | h; exacts [h.le, h.1]
  have han : ∀ n : ℕ, 0 < (a + n).re := fun n => by simp; positivity
  set F : ℕ → ℝ → ℂ := fun n x => z ^ n * ((x : ℂ) ^ (s - 1) * cexp (-((a + n) * x)))
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioi 0)) := fun n =>
    (integrableOn_cpow_mul_exp_neg hs (han n)).const_mul _
  have hnorm : ∀ n, ∫ x in Ioi (0 : ℝ), ‖F n x‖ =
      ‖z‖ ^ n * ((1 / (a.re + n)) ^ s.re * Real.Gamma s.re) := by
    intro n
    rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi hs (by positivity : 0 < a.re + n),
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    simp only [F, norm_mul, norm_pow]
    rw [← norm_mul, norm_cpow_mul_exp_neg hx]
    simp
  have hsum : Summable fun n => ∫ x in Ioi (0 : ℝ), ‖F n x‖ := by
    simp_rw [hnorm]
    rcases hz with h | ⟨-, h⟩
    · refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
        ((summable_geometric_of_lt_one (norm_nonneg z) h).mul_right
          ((1 / a.re) ^ s.re * Real.Gamma s.re))
      gcongr
      simp
    · refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
        (((Real.summable_one_div_nat_add_rpow a.re s.re).mpr h).mul_right (Real.Gamma s.re))
      rw [abs_of_pos (by positivity : 0 < (n : ℝ) + a.re),
        Real.div_rpow zero_le_one (by positivity), Real.one_rpow, add_comm (n : ℝ)]
      calc ‖z‖ ^ n * (1 / (a.re + n) ^ s.re * Real.Gamma s.re)
          ≤ 1 * (1 / (a.re + n) ^ s.re * Real.Gamma s.re) := by
            gcongr
            exact pow_le_one₀ (norm_nonneg _) hz1
        _ = _ := one_mul _
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have hval : ∀ n, ∫ x in Ioi (0 : ℝ), F n x = z ^ n * (Gamma s * (a + n) ^ (-s)) := by
    intro n
    simp only [F]
    rw [integral_const_mul, integral_cpow_mul_cexp_neg_mul_Ioi hs (han n)]
  have htsum : ∫ x in Ioi (0 : ℝ), (∑' n, F n x) = lerchIntegral s a z := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hξ : ‖z * cexp (-(x : ℂ))‖ < 1 := by
      rw [norm_mul, exp_neg_ofReal_eq_ofReal, norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      calc ‖z‖ * Real.exp (-x) ≤ 1 * Real.exp (-x) := by gcongr
        _ < 1 := by rw [one_mul, Real.exp_lt_one_iff]; simpa using hx
    have hF : ∀ n, F n x = (x : ℂ) ^ (s - 1) * cexp (-(a * x)) * (z * cexp (-(x : ℂ))) ^ n := by
      intro n
      simp only [F, mul_pow, ← Complex.exp_nat_mul]
      rw [show -((a + n) * (x : ℂ)) = -(a * x) + n * -(x : ℂ) by ring, Complex.exp_add]
      ring
    simp_rw [hF]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hξ, div_eq_mul_inv]
  rw [htsum] at h
  simp_rw [hval] at h
  have hG : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos hs
  refine (h.mul_left (Gamma s)⁻¹).congr_fun fun n => ?_
  rw [cpow_neg]
  field_simp

/-! ### Lowering the order and shifting the parameter -/

/-- Absolute convergence of a power series inside its disk of convergence, from convergence on
the open unit disk. -/
private lemma summable_norm_mul_pow_of_summable_mul_pow {c : ℕ → ℂ}
    (hc : ∀ z : ℂ, ‖z‖ < 1 → Summable fun n => c n * z ^ n)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) : Summable fun n => ‖c n‖ * r ^ n := by
  set r' := (1 + r) / 2 with hr'
  have hr'0 : 0 < r' := by rw [hr']; linarith
  have hrr' : r < r' := by rw [hr']; linarith
  have hr'1 : r' < 1 := by rw [hr']; linarith
  have h := (hc (r' : ℂ) (by rw [norm_real, Real.norm_eq_abs, abs_of_pos hr'0]; exact hr'1))
  have hev : ∀ᶠ n in atTop, ‖c n * (r' : ℂ) ^ n‖ ≤ 1 :=
    (h.tendsto_atTop_zero.norm.eventually (ge_mem_nhds (by norm_num : ‖(0 : ℂ)‖ < 1)))
  refine Summable.of_norm_bounded_eventually_nat
    (summable_geometric_of_lt_one (by positivity) ((div_lt_one hr'0).mpr hrr')) ?_
  filter_upwards [hev] with n hn
  rw [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hr'0] at hn
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_pow]
  rw [le_div_iff₀ (by positivity)]
  calc ‖c n‖ * r ^ n * r' ^ n = (‖c n‖ * r' ^ n) * r ^ n := by ring
    _ ≤ 1 * r ^ n := by gcongr
    _ = r ^ n := one_mul _

/-- The continuation property: `F` is analytic on the cut plane and sums `∑ zⁿ/(a+n)^s` on the
open unit disk. -/
def IsLerchContinuation (s a : ℂ) (F : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ F slitOne ∧ ∀ z, ‖z‖ < 1 → HasSum (fun n : ℕ => z ^ n / (a + n) ^ s) (F z)

/-- **Lowering the order**: `Φ(z, s-1, a) = z ∂_z Φ(z, s, a) + a Φ(z, s, a)`, for
`a ≠ 0, -1, -2, …`. -/
theorem isLerchContinuation_sub_one {s a : ℂ} (ha : ∀ n : ℕ, a + n ≠ 0) {F : ℂ → ℂ}
    (hF : IsLerchContinuation s a F) :
    IsLerchContinuation (s - 1) a (fun z => z * deriv F z + a * F z) := by
  refine ⟨(analyticOnNhd_id.mul hF.1.deriv).add (analyticOnNhd_const.mul hF.1), fun z hz => ?_⟩
  set c : ℕ → ℂ := fun n => 1 / (a + n) ^ s
  have hc : ∀ w : ℂ, ‖w‖ < 1 → Summable fun n => c n * w ^ n := fun w hw =>
    (hF.2 w hw).summable.congr fun n => by simp only [c]; ring
  set r := (1 + ‖z‖) / 2 with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hzr : ‖z‖ < r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  have hu := summable_norm_mul_pow_of_summable_mul_pow hc hr0 hr1
  have hD := Complex.hasSum_deriv_of_summable_norm (F := fun n w => c n * w ^ n) hu
    (fun n => by fun_prop) isOpen_ball
    (fun n w hw => by
      rw [norm_mul, norm_pow]
      gcongr
      simpa using (mem_ball.mp hw).le)
    (mem_ball_zero_iff.mpr hzr)
  have hFeq : F =ᶠ[𝓝 z] fun w => ∑' n, c n * w ^ n := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hz)] with w hw
    rw [(hF.2 w (mem_ball_zero_iff.mp hw)).tsum_eq.symm]
    congr 1; funext n; simp only [c]; ring
  rw [← hFeq.deriv_eq] at hD
  have hd : ∀ n : ℕ, deriv (fun w => c n * w ^ n) z = c n * (n * z ^ (n - 1)) := fun n =>
    ((hasDerivAt_pow n z).const_mul (c n)).deriv
  simp_rw [hd] at hD
  refine ((hD.mul_left z).add ((hF.2 z hz).mul_left a)).congr_fun fun n => ?_
  have hn := ha n
  simp only [c]
  rw [cpow_sub _ _ hn, cpow_one]
  rcases n with _ | n
  · simp [div_eq_mul_inv]
  · simp only [Nat.add_sub_cancel, pow_succ]
    push_cast
    field_simp
    ring

/-- For `Re a > 0` the continuation exists for every order `s`. -/
private lemma exists_isLerchContinuation_of_re_pos {a : ℂ} (ha : 0 < a.re) (s : ℂ) :
    ∃ F, IsLerchContinuation s a F := by
  have han : ∀ n : ℕ, a + n ≠ 0 := fun n h => by
    have := congrArg Complex.re h; simp at this; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  suffices ∀ k : ℕ, ∀ s : ℂ, 0 < s.re + k → ∃ F, IsLerchContinuation s a F by
    obtain ⟨k, hk⟩ := exists_nat_gt (-s.re)
    exact this k s (by linarith)
  intro k
  induction k with
  | zero =>
    intro s hs
    simp only [Nat.cast_zero, add_zero] at hs
    exact ⟨fun z => (Gamma s)⁻¹ * lerchIntegral s a z,
      analyticOnNhd_const.mul (analyticOnNhd_lerchIntegral hs ha),
      fun z hz => hasSum_lerch_lerchIntegral hs ha (Or.inl hz)⟩
  | succ k ih =>
    intro s hs
    obtain ⟨F, hF⟩ := ih (s + 1) (by simp; push_cast at hs; linarith)
    have := isLerchContinuation_sub_one han hF
    rw [add_sub_cancel_right] at this
    exact ⟨_, this⟩

/-- Shifting the parameter in the series: if `∑ zⁿ/(a+m+n)^s = w` then
`∑ zⁿ/(a+n)^s = z^m w + ∑_{n<m} zⁿ/(a+n)^s` (DLMF 25.14.4). -/
theorem hasSum_lerch_of_hasSum_add_natCast {s a z w : ℂ} (m : ℕ)
    (h : HasSum (fun n : ℕ => z ^ n / (a + m + n) ^ s) w) :
    HasSum (fun n : ℕ => z ^ n / (a + n) ^ s)
      (z ^ m * w + ∑ n ∈ Finset.range m, z ^ n / (a + n) ^ s) := by
  refine (hasSum_nat_add_iff' m).mp ?_
  simp only [add_sub_cancel_right]
  refine (h.mul_left (z ^ m)).congr_fun fun n => ?_
  rw [pow_add]; push_cast; ring_nf

/-- **Continuation of Lerch's series** (DLMF §25.14(i)): for all complex `s` and `a` (principal
powers), `∑_{n≥0} zⁿ/(a+n)^s` extends analytically from the unit disk to `ℂ \ [1, ∞)`. -/
theorem exists_isLerchContinuation (s a : ℂ) : ∃ F, IsLerchContinuation s a F := by
  obtain ⟨m, hm⟩ := exists_nat_gt (-a.re)
  obtain ⟨F, hF, hFs⟩ := exists_isLerchContinuation_of_re_pos (a := a + m) (by simp; linarith) s
  refine ⟨fun z => z ^ m * F z + ∑ n ∈ Finset.range m, z ^ n / (a + n) ^ s,
    (analyticOnNhd_id.pow m |>.mul hF).add ?_, fun z hz => ?_⟩
  · exact Finset.analyticOnNhd_fun_sum _ fun n _ => (analyticOnNhd_id.pow n).div_const
  · exact hasSum_lerch_of_hasSum_add_natCast m (hFs z hz)

/-- Two continuations agree on the cut plane. -/
theorem IsLerchContinuation.eqOn {s a : ℂ} {F G : ℂ → ℂ} (hF : IsLerchContinuation s a F)
    (hG : IsLerchContinuation s a G) : EqOn F G slitOne :=
  eqOn_slitOne_of_eq_on_ball hF.1 hG.1 fun z hz => (hF.2 z hz).unique (hG.2 z hz)

/-- **The continuation is the integral 25.14.5** on the cut plane, for `Re s > 0`, `Re a > 0`. -/
theorem IsLerchContinuation.eq_lerchInt {s a : ℂ} {F : ℂ → ℂ} (hF : IsLerchContinuation s a F)
    (hs : 0 < s.re) (ha : 0 < a.re) {z : ℂ} (hz : z ∈ slitOne) :
    F z = (Gamma s)⁻¹ * lerchIntegral s a z :=
  hF.eqOn (G := fun z => (Gamma s)⁻¹ * lerchIntegral s a z)
    ⟨analyticOnNhd_const.mul (analyticOnNhd_lerchIntegral hs ha),
      fun _ hw => hasSum_lerch_lerchIntegral hs ha (Or.inl hw)⟩ hz

/-- **The series on the closed disk** (Abel's theorem for 25.14.1): for `Re s > 1`, `|z| ≤ 1`,
`z ∈ ℂ \ [1, ∞)`, the continuation is the sum of the series. -/
theorem IsLerchContinuation.hasSum_of_norm_le_one {s a : ℂ} {F : ℂ → ℂ}
    (hF : IsLerchContinuation s a F) (hs : 1 < s.re) {z : ℂ} (hz : ‖z‖ ≤ 1)
    (hzs : z ∈ slitOne) : HasSum (fun n : ℕ => z ^ n / (a + n) ^ s) (F z) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (-a.re)
  have ham : 0 < (a + m).re := by simp; linarith
  have hs0 : 0 < s.re := by linarith
  set G : ℂ → ℂ := fun z => (Gamma s)⁻¹ * lerchIntegral s (a + m) z
  have hG : ∀ z, ‖z‖ < 1 ∨ (‖z‖ ≤ 1 ∧ 1 < s.re) →
      HasSum (fun n : ℕ => z ^ n / (a + n) ^ s)
        (z ^ m * G z + ∑ n ∈ Finset.range m, z ^ n / (a + n) ^ s) := fun z hz =>
    hasSum_lerch_of_hasSum_add_natCast m (hasSum_lerch_lerchIntegral hs0 ham hz)
  have hH : IsLerchContinuation s a
      (fun z => z ^ m * G z + ∑ n ∈ Finset.range m, z ^ n / (a + n) ^ s) :=
    ⟨(analyticOnNhd_id.pow m |>.mul
        (analyticOnNhd_const.mul (analyticOnNhd_lerchIntegral hs0 ham))).add
      (Finset.analyticOnNhd_fun_sum _ fun n _ => (analyticOnNhd_id.pow n).div_const),
      fun z hz => hG z (Or.inl hz)⟩
  rw [hF.eqOn hH hzs]
  exact hG z (Or.inr ⟨hz, hs⟩)

/-- For `Re s > 1` the series `∑ 1/(a+n)^s` converges, for every complex `a` (principal powers,
Lean's conventions at `a + n = 0`). -/
theorem summable_one_div_add_natCast_cpow {s : ℂ} (hs : 1 < s.re) (a : ℂ) :
    Summable fun n : ℕ => 1 / (a + n) ^ s := by
  obtain ⟨m, hm⟩ := exists_nat_gt (-a.re)
  have h := (hasSum_lerch_of_hasSum_add_natCast m
      (hasSum_lerch_lerchIntegral (z := 1) (a := a + m) (by linarith)
    (by simp; linarith) (Or.inr ⟨by simp, hs⟩))).summable
  simpa using h

end DLMF.Zeta

end
