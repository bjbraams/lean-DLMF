/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Basic.LerchContinuation
public import Mathlib.Analysis.Normed.Group.Tannery
public import DLMF.Zeta.Basic.PolylogProperties
public import DLMFMathlib.Analysis.SpecialFunctions.Pow.Decay

/-!
# Basic analytic properties of the principal Lerch transcendent

The principal continuation of Lerch's series is holomorphic on `ℂ \ [1, ∞)`. Its defining
series converges in the open unit disk for every order, and on the unit circle when
`Re s > 1`. The parameter predicate records the branch and exceptional-parameter conditions
of DLMF §25.14(i).
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory
open scoped Nat Real Topology

namespace DLMF.Zeta

/-- DLMF's conditions on `a` in 25.14.1: `|ph a| < π` if `s` is not an integer, and
`a ≠ 0, -1, -2, …` if `s` is a positive integer (no condition if `s = 0, -1, -2, …`). -/
def LerchParamAdmissible (s a : ℂ) : Prop :=
  ((∀ n : ℤ, s ≠ n) → a ∈ slitPlane) ∧ ((∃ n : ℕ, s = n + 1) → ∀ m : ℕ, a ≠ -m)

/-- The stated relation follows from the given hypotheses: `LerchParamAdmissible s (a + m)`. -/
theorem lerchParamAdmissible_add_natCast {s a : ℂ} (h : LerchParamAdmissible s a) (m : ℕ) :
    LerchParamAdmissible s (a + m) := by
  refine ⟨fun hs => ?_, fun hs j hj => h.2 hs (j + m) (by push_cast; linear_combination hj)⟩
  rcases h.1 hs with h1 | h1
  · left; simp only [add_re, natCast_re]; positivity
  · right; simpa using h1

/-- **Convergence and continuation** (DLMF §25.14(i)): under the conditions of 25.14.1, the series
converges in the unit disk and extends analytically in `z` to `ℂ \ [1, ∞)`. This is stronger than
DLMF, which assumes the conditions of 25.14.1 on `s` and `a` (`LerchParamAdmissible s a`). -/
@[dlmf 25.14.i]
theorem exists_lerchPhi_continuation' {s a : ℂ} :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F slitOne ∧
      ∀ z, ‖z‖ < 1 → HasSum (fun n : ℕ => z ^ n / (a + n) ^ s) (F z) := by
  exact exists_isLerchContinuation s a

/-- **Convergence and continuation** (DLMF §25.14(i)): under the conditions of 25.14.1, the series
converges in the unit disk and extends analytically in `z` to `ℂ \ [1, ∞)`. -/
@[dlmf 25.14.i]
theorem exists_lerchPhi_continuation {s a : ℂ} (_h : LerchParamAdmissible s a) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F slitOne ∧
      ∀ z, ‖z‖ < 1 → HasSum (fun n : ℕ => z ^ n / (a + n) ^ s) (F z) :=
  exists_lerchPhi_continuation'

/-- Analyticity on a neighborhood of the specified domain: `AnalyticOnNhd ℂ (slitContinuation
(fun w => lerchPhiSeries w s a)) slitOne ∧ ∀ z, ‖z‖ < 1 → HasSum (fun n : ℕ => z ^ n / (a
+ n) ^ s) (slitContinuation (fun w => lerchPhiSeries w s a) z)`. -/
private lemma lerchPhi_slitContinuation_spec {s a : ℂ} (h : LerchParamAdmissible s a) :
    AnalyticOnNhd ℂ (slitContinuation (fun w => lerchPhiSeries w s a)) slitOne ∧
      ∀ z, ‖z‖ < 1 → HasSum (fun n : ℕ => z ^ n / (a + n) ^ s)
        (slitContinuation (fun w => lerchPhiSeries w s a) z) := by
  obtain ⟨F, hF, hFz⟩ := exists_lerchPhi_continuation h
  have he : ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F slitOne ∧
      ∀ z, ‖z‖ < 1 → F z = lerchPhiSeries z s a :=
    ⟨F, hF, fun z hz => (hFz z hz).tsum_eq.symm⟩
  unfold slitContinuation
  simp only [he, ↓reduceDIte]
  refine ⟨he.choose_spec.1, fun z hz => ?_⟩
  rw [he.choose_spec.2 z hz, lerchPhiSeries]
  exact (hFz z hz).summable.hasSum

/-- On the cut plane, `Φ(z, s, a)` is the value of any continuation of Lerch's series (no
conditions on `s`, `a`). -/
theorem lerchPhi_eq_of_isLerchContinuation {s a : ℂ} {F : ℂ → ℂ}
    (hF : IsLerchContinuation s a F) {z : ℂ}
    (hz : z ∈ slitOne) : lerchPhi z s a = F z := by
  obtain ⟨G, hG⟩ := exists_isLerchContinuation s a
  have he : ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F slitOne ∧
      ∀ z, ‖z‖ < 1 → F z = lerchPhiSeries z s a :=
    ⟨G, hG.1, fun z hz => (hG.2 z hz).tsum_eq.symm⟩
  simp only [lerchPhi, hz, ↓reduceIte, slitContinuation, he, ↓reduceDIte]
  refine eqOn_slitOne_of_eq_on_ball he.choose_spec.1 hF.1 (fun w hw => ?_) hz
  rw [he.choose_spec.2 w hw, lerchPhiSeries]
  exact (hF.2 w hw).tsum_eq

/-- For `Re s > 1` and `|z| ≤ 1`, Lerch's series converges (any `a`, Lean's conventions). -/
private lemma summable_lerch_of_norm_le_one {s a z : ℂ} (hs : 1 < s.re) (hz : ‖z‖ ≤ 1) :
    Summable fun n : ℕ => z ^ n / (a + n) ^ s := by
  obtain ⟨m, hm⟩ := exists_nat_gt (-a.re)
  exact (hasSum_lerch_of_hasSum_add_natCast m
      (hasSum_lerch_lerchIntegral (a := a + m) (by linarith) (by simp; linarith)
    (Or.inr ⟨hz, hs⟩))).summable

/-- **The series in the unit disk** (DLMF 25.14.1): `Φ(z, s, a) = ∑ zⁿ/(a+n)^s` for `|z| < 1`
under the conditions on `a`. -/
@[dlmf 25.14.E1]
theorem hasSum_lerchPhi {z s a : ℂ} (h : LerchParamAdmissible s a) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => z ^ n / (a + n) ^ s) (lerchPhi z s a) := by
  simp only [lerchPhi, mem_slitOne_of_norm_lt_one hz, ↓reduceIte]
  exact (lerchPhi_slitContinuation_spec h).2 z hz

/-- **The series on the unit circle** (DLMF 25.14.1): for `|z| = 1` and `Re s > 1` (at `z = 1` by
definition; otherwise by Abel's theorem). This is stronger than DLMF, which assumes the conditions
of 25.14.1 on `s` and `a` (`LerchParamAdmissible s a`). -/
@[dlmf 25.14.E1]
theorem hasSum_lerchPhi_of_norm_eq_one' {z s a : ℂ} (hs : 1 < s.re) (hz : ‖z‖ = 1) :
    HasSum (fun n : ℕ => z ^ n / (a + n) ^ s) (lerchPhi z s a) := by
  by_cases h1 : z = 1
  · subst h1
    have h1' : (1 : ℂ) ∉ slitOne := by simp [slitOne]
    simp only [lerchPhi, h1', ↓reduceIte, lerchPhiSeries]
    exact (summable_lerch_of_norm_le_one hs hz.le).hasSum
  · obtain ⟨F, hF⟩ := exists_isLerchContinuation s a
    have hzs := mem_slitOne_of_norm_le_one hz.le h1
    rw [lerchPhi_eq_of_isLerchContinuation hF hzs]
    exact hF.hasSum_of_norm_le_one hs hz.le hzs

/-- **The series on the unit circle** (DLMF 25.14.1): for `|z| = 1` and `Re s > 1` (at `z = 1` by
definition; otherwise by Abel's theorem). -/
@[dlmf 25.14.E1]
theorem hasSum_lerchPhi_of_norm_eq_one {z s a : ℂ} (_h : LerchParamAdmissible s a)
    (hs : 1 < s.re) (hz : ‖z‖ = 1) :
    HasSum (fun n : ℕ => z ^ n / (a + n) ^ s) (lerchPhi z s a) :=
  hasSum_lerchPhi_of_norm_eq_one' hs hz

/-- **Analyticity in `z`** (DLMF §25.14(i)). -/
@[dlmf 25.14.i]
theorem analyticOnNhd_lerchPhi {s a : ℂ} (h : LerchParamAdmissible s a) :
    AnalyticOnNhd ℂ (fun z => lerchPhi z s a) slitOne := by
  refine (lerchPhi_slitContinuation_spec h).1.congr isOpen_slitOne fun z hz => ?_
  simp only [lerchPhi, hz, ↓reduceIte]

/-- The series with terms `(fun n : ℕ => z ^ n / (a + n) ^ s)` converges to `(lerchPhi z s a)`. -/
theorem hasSum_lerchPhi_of_lerchParamAdmissible {z s a : ℂ} (h : LerchParamAdmissible s a)
    (hz : ‖z‖ < 1 ∨ (‖z‖ = 1 ∧ 1 < s.re)) :
    HasSum (fun n : ℕ => z ^ n / (a + n) ^ s) (lerchPhi z s a) := by
  rcases hz with hz | ⟨hz, hs⟩
  · exact hasSum_lerchPhi h hz
  · exact hasSum_lerchPhi_of_norm_eq_one h hs hz

/-- A parameter in the right half-plane satisfies Lerch's parameter conditions at every order. -/
theorem lerchParamAdmissible_of_re_pos {a : ℂ} (ha : 0 < a.re) (s : ℂ) :
    LerchParamAdmissible s a := by
  refine ⟨fun _ => Or.inl ha, fun _ m hm => ?_⟩
  have h := congrArg Complex.re hm
  simp only [neg_re, natCast_re] at h
  linarith [Nat.cast_nonneg (α := ℝ) m]

/-- Inside the unit disk, Lerch's transcendent is entire in its order when the parameter
is in the right half-plane. -/
theorem differentiable_lerchPhi_order_of_norm_lt_one {a z : ℂ} (ha : 0 < a.re)
    (hz : ‖z‖ < 1) : Differentiable ℂ (fun s => lerchPhi z s a) := by
  have hn0 : ∀ n : ℕ, a + n ≠ 0 := by
    intro n h
    have h' := congrArg Complex.re h
    simp only [add_re, natCast_re, zero_re] at h'
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have heq : (fun s => lerchPhi z s a) = fun s => ∑' n : ℕ, z ^ n * (a + n) ^ (-s) := by
    funext s
    rw [← (hasSum_lerchPhi (lerchParamAdmissible_of_re_pos ha s) hz).tsum_eq]
    exact tsum_congr fun n => by rw [cpow_neg, div_eq_mul_inv]
  rw [heq]
  refine differentiable_tsum_of_locally_dominated (fun n =>
    (differentiable_id.neg.const_cpow (Or.inl (hn0 n))).const_mul (z ^ n)) ?_
  intro s
  obtain ⟨C, hC, N, hb⟩ := exists_bound_cpow_of_norm_bounds ha (norm_nonneg a)
    (M := ‖s‖ + 1) (by positivity)
  refine ⟨Metric.ball s 1, Metric.ball_mem_nhds s one_pos,
    fun n => C * (((n : ℝ) + 1) ^ N * ‖z‖ ^ n),
    (Real.summable_natCast_add_one_pow_mul_geometric N (norm_nonneg z) hz).mul_left C, ?_⟩
  intro n t ht
  have ht' : ‖-t‖ ≤ ‖s‖ + 1 := by
    rw [norm_neg]
    have hdist : ‖t - s‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using ht
    have htri := norm_add_le (t - s) s
    rw [sub_add_cancel] at htri
    linarith
  have hn : a.re ≤ ‖a + (n : ℂ)‖ := by
    have h := re_le_norm (a + (n : ℂ))
    simp only [add_re, natCast_re] at h
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hnorm : ‖a + (n : ℂ)‖ ≤ ‖a‖ + n := by
    simpa only [Complex.norm_natCast] using norm_add_le a (n : ℂ)
  have h := hb (-t) ht' (a + n) n (Nat.cast_nonneg n) hn hnorm
  rw [norm_mul, norm_pow]
  calc
    _ ≤ ‖z‖ ^ n * (C * (1 + (n : ℝ)) ^ N) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by rw [add_comm (1 : ℝ)]; ring

/-- **Recurrence in `a`** (DLMF 25.14.4): under the conditions of 25.14.1 (`|z| < 1`, or `|z| = 1`
and `Re s > 1`) and `m = 1, 2, 3, …`,
`Φ(z, s, a) = z^m Φ(z, s, a+m) + ∑_{n=0}^{m-1} zⁿ/(a+n)^s` (valid also for `m = 0`). -/
@[dlmf 25.14.E4]
theorem lerchPhi_eq_add_nat {z s a : ℂ} (h : LerchParamAdmissible s a)
    (hz : ‖z‖ < 1 ∨ (‖z‖ = 1 ∧ 1 < s.re)) (m : ℕ) :
    lerchPhi z s a = z ^ m * lerchPhi z s (a + m) +
      ∑ n ∈ Finset.range m, z ^ n / (a + n) ^ s := by
  have h1 := (hasSum_nat_add_iff' m).mpr (hasSum_lerchPhi_of_lerchParamAdmissible h hz)
  have h2 := (hasSum_lerchPhi_of_lerchParamAdmissible (lerchParamAdmissible_add_natCast h m)
      hz).mul_left (z ^ m)
  have h3 : HasSum (fun n : ℕ => z ^ (n + m) / (a + ↑(n + m)) ^ s)
      (z ^ m * lerchPhi z s (a + m)) := by
    refine h2.congr_fun fun n => ?_
    rw [pow_add]; push_cast; ring_nf
  rw [← h1.unique h3]
  ring

/-- The parameter recurrence continues throughout the principal Lerch cut plane. -/
theorem lerchPhi_eq_add_nat_of_mem_slitOne {z s a : ℂ} (ha : LerchParamAdmissible s a)
    (hz : z ∈ slitOne) (m : ℕ) :
    lerchPhi z s a = z ^ m * lerchPhi z s (a + m) +
      ∑ n ∈ Finset.range m, z ^ n / (a + n) ^ s := by
  have hF := analyticOnNhd_lerchPhi ha
  have hG : AnalyticOnNhd ℂ (fun z => z ^ m * lerchPhi z s (a + m) +
      ∑ n ∈ Finset.range m, z ^ n / (a + n) ^ s) slitOne :=
    ((analyticOnNhd_id.pow m).mul
      (analyticOnNhd_lerchPhi (lerchParamAdmissible_add_natCast ha m))).add
      (Finset.analyticOnNhd_fun_sum _ fun n _ => (analyticOnNhd_id.pow n).div_const)
  exact eqOn_slitOne_of_eq_on_ball hF hG
    (fun v hv => lerchPhi_eq_add_nat ha (Or.inl hv) m) hz

/-- The principal polylogarithm is the parameter-one Lerch transcendent throughout its cut plane. -/
theorem polylog_eq_mul_lerchPhi_of_mem_slitOne (s : ℂ) {z : ℂ} (hz : z ∈ slitOne) :
    polylog s z = z * lerchPhi z s 1 := by
  have hp : LerchParamAdmissible s 1 := lerchParamAdmissible_of_re_pos (by norm_num) s
  apply eqOn_slitOne_of_eq_on_ball (analyticOnNhd_polylog s)
    (analyticOnNhd_id.mul (analyticOnNhd_lerchPhi hp)) ?_ hz
  intro v hv
  have hL := (hasSum_lerchPhi (z := v) hp hv).mul_left v
  apply (hasSum_polylog (s := s) hv).unique
  refine hL.congr_fun fun n => ?_
  rw [pow_succ, add_comm (1 : ℂ)]
  ring

/-- Differentiating the exponentially weighted Lerch function lowers its order. -/
theorem hasDerivAt_exp_mul_lerchPhi {a w : ℂ} (ha : ∀ n : ℕ, a + n ≠ 0) (s : ℂ)
    (hw : exp w ∈ slitOne) :
    HasDerivAt (fun v => exp (a * v) * lerchPhi (exp v) s a)
      (exp (a * w) * lerchPhi (exp w) (s - 1) a) w := by
  obtain ⟨F, hF⟩ := exists_isLerchContinuation s a
  have hG := isLerchContinuation_sub_one ha hF
  have heq : (fun v => exp (a * v) * lerchPhi (exp v) s a) =ᶠ[𝓝 w]
      fun v => exp (a * v) * F (exp v) := by
    filter_upwards [continuous_exp.continuousAt.eventually
      (isOpen_slitOne.mem_nhds hw)] with v hv
    rw [lerchPhi_eq_of_isLerchContinuation hF hv]
  have hd := (((hasDerivAt_id w).const_mul a).cexp).mul
    (((hF.1 (exp w) hw).differentiableAt.hasDerivAt).comp w (Complex.hasDerivAt_exp w))
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  convert hd using 1
  · funext v; rfl
  rw [lerchPhi_eq_of_isLerchContinuation hG hw]
  simp only [id_eq, mul_one, Function.comp_apply]
  ring

/-- Absolute convergence gives Lerch's unit-circle value along negative real logarithms. -/
theorem tendsto_lerchPhi_exp_zero {a s : ℂ} (ha : 0 < a.re) (hs : 1 < s.re) :
    Tendsto (fun r : ℝ => lerchPhi (exp (r : ℂ)) s a) (𝓝[<] 0)
      (𝓝 (lerchPhi 1 s a)) := by
  have hsum := (summable_one_div_add_natCast_cpow hs a).norm
  have hr : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[<] 0) (𝓝 0) :=
    (continuous_ofReal.continuousAt.tendsto (x := (0 : ℝ))).mono_left nhdsWithin_le_nhds
  have he : Tendsto (fun r : ℝ => exp (r : ℂ)) (𝓝[<] 0) (𝓝 1) := by
    have hc : ContinuousAt (fun r : ℝ => exp (r : ℂ)) 0 := by fun_prop
    simpa only [ofReal_zero, exp_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have h := tendsto_tsum_of_dominated_convergence hsum
    (f := fun (r : ℝ) (k : ℕ) => exp (r : ℂ) ^ k / (a + k) ^ s)
    (g := fun k : ℕ => 1 / (a + k) ^ s)
    (fun k => by simpa using (he.pow k).div_const ((a + k) ^ s)) ?_
  · have hZ : HasSum (fun k : ℕ => 1 / (a + k) ^ s) (lerchPhi 1 s a) := by
      simpa only [one_pow] using
        (hasSum_lerchPhi_of_norm_eq_one' (z := 1) hs (by norm_num))
    rw [hZ.tsum_eq] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hasSum_lerchPhi (lerchParamAdmissible_of_re_pos ha s)
      (by simpa only [norm_exp, ofReal_re] using Real.exp_lt_one_iff.mpr hr)).tsum_eq
  · filter_upwards [self_mem_nhdsWithin] with r hr k
    rw [norm_div, norm_pow, norm_div, norm_one]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    apply pow_le_one₀ (norm_nonneg _)
    rw [norm_exp, ofReal_re]
    exact Real.exp_le_one_iff.mpr hr.le

end DLMF.Zeta
