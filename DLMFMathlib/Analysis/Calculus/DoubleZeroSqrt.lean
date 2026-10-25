/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Square roots at double zeros and Airy-type turning-point coordinates

Change-of-variable coordinates used by uniform (turning-point and Temme-type) asymptotic
expansions, as real analysis on `ℝ`.

* `AnalyticAt.dblZero_integral_smul_comp_mul`, `AnalyticAt.dblZero_integral_smul_comp_sub`:
  for `q` analytic at `x₀` and any weight `w` integrable on `[0, 1]`, the weighted average
  `x ↦ ∫₀¹ w(τ) q(x₀ + (x - x₀) τ) dτ` is analytic at `x₀` (termwise integration of the power
  series).
* `AnalyticAt.dblZero_rpow_const`: real powers of positive analytic functions are analytic.
* `dblZero_integral_rpow_mul_right`, `dblZero_integral_rpow_mul_left`: the substitution
  `s = x₀ + (x - x₀) τ` in `∫ |s - x₀|^α q(s) ds`.
* `dblZero_airyCoord`: for `f(x) = (x - x₀) p(x)` with `p` analytic and positive at `x₀`, the
  Langer coordinate `ζ` with `(2/3) ζ^{3/2} = ∫_{x₀}^x √f` for `x > x₀` and
  `(2/3) (-ζ)^{3/2} = ∫_x^{x₀} √(-f)` for `x < x₀` (`dblZero_airyCoord_of_lt`,
  `dblZero_airyCoord_of_gt`), analytic at `x₀` (`dblZero_analyticAt_airyCoord`) with
  `ζ'(x₀) = p(x₀)^{1/3} = f'(x₀)^{1/3}` (`dblZero_hasDerivAt_airyCoord`), and with an analytic
  inverse (`dblZero_exists_analytic_inverse_airyCoord`); it is continuous on `ℝ` when `p` is
  (`dblZero_continuous_airyCoord`).
* `dblZero_eq_sq_mul_dslope`, `dblZero_signedSqrt`: at a double zero `g = (x - x₀)² Q` and the
  signed square root `sign(x - x₀) √(2 g)` is the analytic function `(x - x₀) √(2 Q)`.
* `dblZero_strictMonoOn_signedSqrt`: the global monotone version on an interval;
  `dblZero_exists_eq_of_tendsto`: range of a continuous map of `(0, ∞)` with infinite limits.
* `dblZero_exists_analytic_inverse`: analytic local inverse with its first Taylor coefficient
  (a wrapper around Mathlib's `AnalyticAt.analyticAt_localInverse`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral
open scoped NNReal ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Termwise integration: if `q` is analytic at `0` and `w` is integrable on `[0, 1]`, then
`y ↦ ∫₀¹ w(τ) • q(y τ) dτ` is analytic at `0`. -/
theorem AnalyticAt.dblZero_integral_smul_comp_mul {q : ℝ → E} (hq : AnalyticAt ℝ q 0)
    {w : ℝ → ℝ} (hw : IntervalIntegrable w volume 0 1) :
    AnalyticAt ℝ (fun y => ∫ τ in (0:ℝ)..1, w τ • q (y * τ)) 0 := by
  obtain ⟨p, r, hp⟩ := hq
  set c : ℕ → ℝ := fun n => ∫ τ in (0:ℝ)..1, w τ * τ ^ n with hc
  set M : ℝ := ∫ τ in (0:ℝ)..1, |w τ|
  have hcM : ∀ n, ‖c n‖ ≤ M := by
    intro n
    refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one ?_ hw.abs
    refine Filter.Eventually.of_forall fun τ hτ => ?_
    rw [norm_mul, Real.norm_eq_abs, norm_pow, Real.norm_eq_abs]
    have h1 : |τ| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg _) (by
      rw [abs_of_pos hτ.1]; exact hτ.2)
    nlinarith [abs_nonneg (w τ), abs_nonneg τ, pow_nonneg (abs_nonneg τ) n]
  have hM : 0 ≤ M := (norm_nonneg _).trans (hcM 0)
  let P : FormalMultilinearSeries ℝ ℝ E := fun n => c n • p n
  refine ⟨P, r, ?_, hp.r_pos, ?_⟩
  · refine ENNReal.le_of_forall_nnreal_lt fun t ht => ?_
    obtain ⟨C, -, hC⟩ := p.norm_mul_pow_le_of_lt_radius (ht.trans_le hp.r_le)
    refine P.le_radius_of_bound (M * C) fun n => ?_
    calc ‖P n‖ * (t:ℝ) ^ n ≤ (‖c n‖ * ‖p n‖) * (t:ℝ) ^ n := by
          gcongr; exact norm_smul_le (c n) (p n)
      _ = ‖c n‖ * (‖p n‖ * (t:ℝ) ^ n) := by ring
      _ ≤ M * C := mul_le_mul (hcM n) (hC n) (by positivity) hM
  · intro y hy
    rw [zero_add]
    have hyr : (‖y‖₊ : ℝ≥0∞) < p.radius := by
      have : (‖y‖₊ : ℝ≥0∞) < r := by
        rw [Metric.mem_eball, edist_zero_right] at hy; simpa [enorm_eq_nnnorm] using hy
      exact this.trans_le hp.r_le
    have hsum := p.summable_norm_mul_pow hyr
    have hPn : ∀ n, P n (fun _ => y) = ∫ τ in (0:ℝ)..1, (w τ * τ ^ n) • p n (fun _ => y) := by
      intro n
      rw [intervalIntegral.integral_smul_const]
      rfl
    simp_rw [hPn]
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n τ => |w τ| * (‖p n‖ * ‖y‖ ^ n)) (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
    · exact ((hw.mul_continuousOn (continuousOn_pow n)).def'.aestronglyMeasurable).smul_const _
    · refine Filter.Eventually.of_forall fun τ hτ => ?_
      rw [uIoc_of_le zero_le_one] at hτ
      rw [norm_smul, norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hτ.1]
      have h1 : τ ^ n ≤ 1 := pow_le_one₀ hτ.1.le hτ.2
      have h2 : ‖p n (fun _ => y)‖ ≤ ‖p n‖ * ‖y‖ ^ n := by
        simpa using (p n).le_opNorm (fun _ => y)
      have h3 : 0 ≤ ‖p n (fun _ => y)‖ := norm_nonneg _
      have h4 : 0 ≤ τ ^ n := pow_nonneg hτ.1.le n
      calc |w τ| * τ ^ n * ‖p n (fun _ => y)‖ ≤ |w τ| * 1 * ‖p n (fun _ => y)‖ := by gcongr
        _ ≤ |w τ| * (‖p n‖ * ‖y‖ ^ n) := by rw [mul_one]; gcongr
    · exact Filter.Eventually.of_forall fun τ _ => hsum.mul_left _
    · simp_rw [tsum_mul_left]
      exact hw.abs.mul_const _
    · refine Filter.Eventually.of_forall fun τ hτ => ?_
      rw [uIoc_of_le zero_le_one] at hτ
      have hmem : y * τ ∈ Metric.eball (0:ℝ) r := by
        rw [Metric.mem_eball, edist_zero_right] at hy ⊢
        refine lt_of_le_of_lt ?_ hy
        rw [enorm_mul]
        have : ‖τ‖ₑ ≤ 1 := by
          rw [← ofReal_norm, Real.norm_eq_abs, abs_of_pos hτ.1]
          exact ENNReal.ofReal_le_one.2 hτ.2
        exact mul_le_of_le_one_right (zero_le) this
      have h := (hp.hasSum hmem).const_smul (w τ)
      rw [zero_add] at h
      convert h using 1
      funext n
      rw [mul_smul]
      congr 1
      have := (p n).map_smul_univ (fun _ => τ) (fun _ => y)
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
      rw [← this, mul_comm y τ]
      rfl

/-- Recentered form: `x ↦ ∫₀¹ w τ • q (x₀ + (x - x₀) τ) dτ` is analytic at `x₀`. -/
theorem AnalyticAt.dblZero_integral_smul_comp_sub {q : ℝ → E} {x₀ : ℝ} (hq : AnalyticAt ℝ q x₀)
    {w : ℝ → ℝ} (hw : IntervalIntegrable w volume 0 1) :
    AnalyticAt ℝ (fun x => ∫ τ in (0:ℝ)..1, w τ • q (x₀ + (x - x₀) * τ)) x₀ := by
  have h0 : AnalyticAt ℝ (fun y => q (x₀ + y)) 0 :=
    hq.comp_of_eq (analyticAt_const.add analyticAt_id) (by simp)
  have h1 := h0.dblZero_integral_smul_comp_mul hw
  exact h1.comp_of_eq (analyticAt_id.sub analyticAt_const) (by simp)

/-- A real power of a positive analytic function is analytic. -/
theorem AnalyticAt.dblZero_rpow_const {f : ℝ → ℝ} {x : ℝ} (hf : AnalyticAt ℝ f x) (hx : 0 < f x)
    (a : ℝ) : AnalyticAt ℝ (fun y => f y ^ a) x := by
  have h : AnalyticAt ℝ (fun y => Real.exp (Real.log (f y) * a)) x :=
    ((hf.log hx).mul analyticAt_const).rexp'
  refine h.congr ?_
  filter_upwards [hf.continuousAt.eventually (lt_mem_nhds hx)] with y hy
  rw [Real.rpow_def_of_pos hy]

/-- Substitution `s = x₀ + (x - x₀) τ` on the right of `x₀`. -/
theorem dblZero_integral_rpow_mul_right (q : ℝ → ℝ) (α : ℝ) {x₀ x : ℝ} (hx : x₀ < x) :
    ∫ s in x₀..x, (s - x₀) ^ α * q s
      = (x - x₀) ^ (α + 1) * ∫ τ in (0:ℝ)..1, τ ^ α * q (x₀ + (x - x₀) * τ) := by
  have hc : 0 < x - x₀ := sub_pos.2 hx
  have h1 : ∫ τ in (0:ℝ)..1, τ ^ α * q (x₀ + (x - x₀) * τ)
      = ∫ τ in (0:ℝ)..1,
          (x - x₀) ^ (-α) * (((x₀ + (x - x₀) * τ) - x₀) ^ α * q (x₀ + (x - x₀) * τ)) := by
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [uIcc_of_le zero_le_one] at hτ
    simp only [add_sub_cancel_left]
    rw [Real.mul_rpow hc.le hτ.1, ← mul_assoc, ← mul_assoc, ← Real.rpow_add hc]
    simp
  rw [h1, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_add_mul (fun s => (s - x₀) ^ α * q s) hc.ne']
  simp only [mul_zero, add_zero, mul_one, add_sub_cancel, smul_eq_mul]
  rw [← mul_assoc, ← mul_assoc, ← Real.rpow_neg_one, ← Real.rpow_add hc, ← Real.rpow_add hc]
  simp

/-- Substitution `s = x₀ + (x - x₀) τ` on the left of `x₀`. -/
theorem dblZero_integral_rpow_mul_left (q : ℝ → ℝ) (α : ℝ) {x₀ x : ℝ} (hx : x < x₀) :
    ∫ s in x..x₀, (x₀ - s) ^ α * q s
      = (x₀ - x) ^ (α + 1) * ∫ τ in (0:ℝ)..1, τ ^ α * q (x₀ + (x - x₀) * τ) := by
  have hc : 0 < x₀ - x := sub_pos.2 hx
  have h1 : ∫ τ in (0:ℝ)..1, τ ^ α * q (x₀ + (x - x₀) * τ)
      = ∫ τ in (0:ℝ)..1,
          (x₀ - x) ^ (-α) * ((x₀ - (x₀ + (x - x₀) * τ)) ^ α * q (x₀ + (x - x₀) * τ)) := by
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [uIcc_of_le zero_le_one] at hτ
    have : x₀ - (x₀ + (x - x₀) * τ) = (x₀ - x) * τ := by ring
    rw [this, Real.mul_rpow hc.le hτ.1, ← mul_assoc, ← mul_assoc, ← Real.rpow_add hc]
    simp
  rw [h1, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_add_mul (fun s => (x₀ - s) ^ α * q s) (sub_ne_zero.2 hx.ne),
    intervalIntegral.integral_symm]
  simp only [mul_zero, add_zero, mul_one, add_sub_cancel, smul_eq_mul]
  have : (x - x₀)⁻¹ = -(x₀ - x)⁻¹ := by rw [← inv_neg, neg_sub]
  have key : (x₀ - x) ^ (α + 1) * ((x₀ - x) ^ (-α) * (x₀ - x)⁻¹) = 1 := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hc, ← Real.rpow_add hc,
      show α + 1 + (-α + -1) = 0 by ring, Real.rpow_zero]
  rw [this]
  linear_combination (∫ s in x₀..x, (x₀ - s) ^ α * q s) * key

/-- The weighted average `K(x) = ∫₀¹ τ^{1/2} √(p(x₀ + (x - x₀)τ)) dτ` behind the Airy coordinate. -/
def dblZero_airyAvg (p : ℝ → ℝ) (x₀ x : ℝ) : ℝ :=
  ∫ τ in (0:ℝ)..1, τ ^ (1/2:ℝ) * Real.sqrt (p (x₀ + (x - x₀) * τ))

/-- The Airy-type (Langer) coordinate `ζ(x) = (x - x₀) ((3/2) K(x))^{2/3}` attached to
`f(x) = (x - x₀) p(x)`. -/
def dblZero_airyCoord (p : ℝ → ℝ) (x₀ x : ℝ) : ℝ :=
  (x - x₀) * ((3/2) * dblZero_airyAvg p x₀ x) ^ (2/3:ℝ)

/-- The weighted average is nonnegative. -/
lemma dblZero_airyAvg_nonneg (p : ℝ → ℝ) (x₀ x : ℝ) : 0 ≤ dblZero_airyAvg p x₀ x :=
  intervalIntegral.integral_nonneg zero_le_one fun _ hτ =>
    mul_nonneg (Real.rpow_nonneg hτ.1 _) (Real.sqrt_nonneg _)

/-- To the right of `x₀`: `(2/3) ζ^{3/2} = ∫_{x₀}^x √f`. -/
theorem dblZero_airyCoord_of_lt (p : ℝ → ℝ) {x₀ x : ℝ} (hx : x₀ < x) :
    dblZero_airyCoord p x₀ x
      = ((3/2) * ∫ s in x₀..x, Real.sqrt ((s - x₀) * p s)) ^ (2/3:ℝ) := by
  have hc : 0 < x - x₀ := sub_pos.2 hx
  have h1 : ∫ s in x₀..x, Real.sqrt ((s - x₀) * p s)
      = ∫ s in x₀..x, (s - x₀) ^ (1/2:ℝ) * Real.sqrt (p s) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hx.le] at hs
    rw [Real.sqrt_mul (sub_nonneg.2 hs.1), Real.sqrt_eq_rpow]
  have hK := dblZero_airyAvg_nonneg p x₀ x
  rw [h1, dblZero_integral_rpow_mul_right _ _ hx, dblZero_airyCoord]
  rw [dblZero_airyAvg] at hK ⊢
  generalize (∫ τ in (0:ℝ)..1, τ ^ (1/2:ℝ) * Real.sqrt (p (x₀ + (x - x₀) * τ))) = K at hK ⊢
  rw [show 3/2 * ((x - x₀) ^ (1/2+1:ℝ) * K) = (x - x₀) ^ (1/2+1:ℝ) * (3/2 * K) by ring,
    Real.mul_rpow (x := (x - x₀) ^ (1/2+1:ℝ)) (by positivity) (by positivity),
    ← Real.rpow_mul hc.le]
  norm_num

/-- To the left of `x₀`: `(2/3) (-ζ)^{3/2} = ∫_x^{x₀} √(-f)`. -/
theorem dblZero_airyCoord_of_gt (p : ℝ → ℝ) {x₀ x : ℝ} (hx : x < x₀) :
    dblZero_airyCoord p x₀ x
      = -((3/2) * ∫ s in x..x₀, Real.sqrt ((x₀ - s) * p s)) ^ (2/3:ℝ) := by
  have hc : 0 < x₀ - x := sub_pos.2 hx
  have h1 : ∫ s in x..x₀, Real.sqrt ((x₀ - s) * p s)
      = ∫ s in x..x₀, (x₀ - s) ^ (1/2:ℝ) * Real.sqrt (p s) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hx.le] at hs
    rw [Real.sqrt_mul (sub_nonneg.2 hs.2), Real.sqrt_eq_rpow]
  have hK := dblZero_airyAvg_nonneg p x₀ x
  rw [h1, dblZero_integral_rpow_mul_left _ _ hx, dblZero_airyCoord]
  rw [dblZero_airyAvg] at hK ⊢
  generalize (∫ τ in (0:ℝ)..1, τ ^ (1/2:ℝ) * Real.sqrt (p (x₀ + (x - x₀) * τ))) = K at hK ⊢
  rw [show 3/2 * ((x₀ - x) ^ (1/2+1:ℝ) * K) = (x₀ - x) ^ (1/2+1:ℝ) * (3/2 * K) by ring,
    Real.mul_rpow (x := (x₀ - x) ^ (1/2+1:ℝ)) (by positivity) (by positivity),
    ← Real.rpow_mul hc.le]
  norm_num
  ring

/-- At the turning point, `K(x₀) = (2/3) √(p x₀)`. -/
lemma dblZero_airyAvg_self (p : ℝ → ℝ) (x₀ : ℝ) :
    dblZero_airyAvg p x₀ x₀ = (2/3) * Real.sqrt (p x₀) := by
  simp only [dblZero_airyAvg, sub_self, zero_mul, add_zero]
  rw [intervalIntegral.integral_mul_const, integral_rpow (Or.inl (by norm_num))]
  norm_num

/-- The weighted average `K` is analytic at the turning point `x₀`. -/
theorem dblZero_analyticAt_airyAvg {p : ℝ → ℝ} {x₀ : ℝ} (hp : AnalyticAt ℝ p x₀) (hp0 : 0 < p x₀) :
    AnalyticAt ℝ (dblZero_airyAvg p x₀) x₀ := by
  have hs : AnalyticAt ℝ (fun s => Real.sqrt (p s)) x₀ := by
    exact (hp.dblZero_rpow_const hp0 (1/2)).congr
      (Filter.Eventually.of_forall fun s => (Real.sqrt_eq_rpow _).symm)
  have hw : IntervalIntegrable (fun τ : ℝ => τ ^ (1/2:ℝ)) volume 0 1 :=
    (Real.continuous_rpow_const (by norm_num)).intervalIntegrable _ _
  exact hs.dblZero_integral_smul_comp_sub hw

/-- The Airy coordinate is analytic at the turning point `x₀`. -/
theorem dblZero_analyticAt_airyCoord {p : ℝ → ℝ} {x₀ : ℝ} (hp : AnalyticAt ℝ p x₀)
    (hp0 : 0 < p x₀) : AnalyticAt ℝ (dblZero_airyCoord p x₀) x₀ := by
  have hK := dblZero_analyticAt_airyAvg hp hp0
  have hK0 : 0 < (3/2) * dblZero_airyAvg p x₀ x₀ := by
    rw [dblZero_airyAvg_self]; have := Real.sqrt_pos.2 hp0; positivity
  exact (analyticAt_id.sub analyticAt_const).mul
    ((analyticAt_const.mul hK).dblZero_rpow_const hK0 _)

/-- The derivative of the Airy coordinate at the turning point is `p(x₀)^{1/3}`. -/
theorem dblZero_hasDerivAt_airyCoord {p : ℝ → ℝ} {x₀ : ℝ} (hp : AnalyticAt ℝ p x₀)
    (hp0 : 0 < p x₀) : HasDerivAt (dblZero_airyCoord p x₀) (p x₀ ^ (1/3:ℝ)) x₀ := by
  have hK := dblZero_analyticAt_airyAvg hp hp0
  have hK0 : 0 < (3/2) * dblZero_airyAvg p x₀ x₀ := by
    rw [dblZero_airyAvg_self]; have := Real.sqrt_pos.2 hp0; positivity
  have hG : DifferentiableAt ℝ (fun y => ((3/2) * dblZero_airyAvg p x₀ y) ^ (2/3:ℝ)) x₀ :=
    ((analyticAt_const.mul hK).dblZero_rpow_const hK0 (2/3:ℝ)).differentiableAt
  have h := ((hasDerivAt_id' x₀).sub_const x₀).mul hG.hasDerivAt
  convert h using 1
  · funext y; rfl
  rw [sub_self, zero_mul, add_zero, one_mul]
  rw [dblZero_airyAvg_self, ← mul_assoc, show (3/2:ℝ) * (2/3) = 1 by norm_num, one_mul,
    Real.sqrt_eq_rpow, ← Real.rpow_mul hp0.le]
  norm_num

/-- The Airy coordinate is continuous on `ℝ` when `p` is continuous. -/
theorem dblZero_continuous_airyCoord {p : ℝ → ℝ} (hp : Continuous p) (x₀ : ℝ) :
    Continuous (dblZero_airyCoord p x₀) := by
  have hK : Continuous (dblZero_airyAvg p x₀) := by
    unfold dblZero_airyAvg
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun x τ => τ ^ (1/2:ℝ) * Real.sqrt (p (x₀ + (x - x₀) * τ))) ?_ 0 1
    exact ((Real.continuous_rpow_const (by norm_num)).comp continuous_snd).mul
      (Real.continuous_sqrt.comp (hp.comp (continuous_const.add
        ((continuous_fst.sub continuous_const).mul continuous_snd))))
  exact (continuous_id.sub continuous_const).mul
    ((continuous_const.mul hK).rpow_const fun _ => Or.inr (by norm_num))

/-- A function with a double zero at `x₀` factors as `(x - x₀)² Q(x)` with `Q` analytic. -/
theorem dblZero_eq_sq_mul_dslope {g : ℝ → ℝ} {x₀ : ℝ} (hg0 : g x₀ = 0) (hg1 : deriv g x₀ = 0)
    (x : ℝ) : g x = (x - x₀) ^ 2 * dslope (dslope g x₀) x₀ x := by
  have h1 := sub_smul_dslope g x₀ x
  have h2 := sub_smul_dslope (dslope g x₀) x₀ x
  rw [dslope_same, hg1, sub_zero, smul_eq_mul] at h2
  rw [hg0, sub_zero, smul_eq_mul] at h1
  rw [← h1, ← h2]; ring

/-- Signed square root at a double zero: if `g = (x - x₀)² Q` with `Q` analytic and positive at
`x₀`, then `h(x) = (x - x₀) √(2 Q(x))` is analytic at `x₀`, `h' (x₀) = √(2 Q(x₀))`, and near `x₀`
`g = h²/2` and `h = sign(x - x₀) √(2 g)`. -/
theorem dblZero_signedSqrt {g Q : ℝ → ℝ} {x₀ : ℝ} (hQ : AnalyticAt ℝ Q x₀) (hQ0 : 0 < Q x₀)
    (hg : ∀ᶠ x in 𝓝 x₀, g x = (x - x₀) ^ 2 * Q x) :
    AnalyticAt ℝ (fun x => (x - x₀) * Real.sqrt (2 * Q x)) x₀ ∧
      HasDerivAt (fun x => (x - x₀) * Real.sqrt (2 * Q x)) (Real.sqrt (2 * Q x₀)) x₀ ∧
      ∀ᶠ x in 𝓝 x₀, g x = ((x - x₀) * Real.sqrt (2 * Q x)) ^ 2 / 2 ∧
        (x - x₀) * Real.sqrt (2 * Q x) = (if x < x₀ then -1 else 1) * Real.sqrt (2 * g x) := by
  have hs : AnalyticAt ℝ (fun x => Real.sqrt (2 * Q x)) x₀ :=
    ((analyticAt_const.mul hQ).dblZero_rpow_const (show (0:ℝ) < 2 * Q x₀ by linarith) (1/2)).congr
      (Filter.Eventually.of_forall fun s => (Real.sqrt_eq_rpow _).symm)
  have ha : AnalyticAt ℝ (fun x => (x - x₀) * Real.sqrt (2 * Q x)) x₀ :=
    (analyticAt_id.sub analyticAt_const).mul hs
  refine ⟨ha, ?_, ?_⟩
  · have h := ((hasDerivAt_id' x₀).sub_const x₀).mul hs.differentiableAt.hasDerivAt
    convert h using 1
    rw [sub_self, zero_mul, add_zero, one_mul]
  · filter_upwards [hg, hQ.continuousAt.eventually (lt_mem_nhds hQ0)] with x hx hQx
    have h2 : 0 ≤ 2 * Q x := by positivity
    refine ⟨?_, ?_⟩
    · rw [hx, mul_pow, Real.sq_sqrt h2]; ring
    · rw [hx, show 2 * ((x - x₀) ^ 2 * Q x) = (x - x₀) ^ 2 * (2 * Q x) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
      split_ifs with h
      · rw [abs_of_neg (sub_neg.2 h)]; ring
      · rw [abs_of_nonneg (sub_nonneg.2 (not_lt.1 h))]; ring

/-- Global monotonicity of the signed square root: if `g` vanishes at `x₀ ∈ I`, decreases strictly
on `I ∩ (-∞, x₀]` and increases strictly on `I ∩ [x₀, ∞)`, then
`x ↦ sign(x - x₀) √(2 g x)` is strictly increasing on `I`. -/
theorem dblZero_strictMonoOn_signedSqrt {g : ℝ → ℝ} {I : Set ℝ} {x₀ : ℝ} (hx₀ : x₀ ∈ I)
    (hg0 : g x₀ = 0) (hl : StrictAntiOn g (I ∩ Iic x₀)) (hr : StrictMonoOn g (I ∩ Ici x₀)) :
    StrictMonoOn (fun x => (if x < x₀ then -1 else 1) * Real.sqrt (2 * g x)) I := by
  have pos_l : ∀ x ∈ I, x < x₀ → 0 < g x := fun x hx h =>
    hg0 ▸ hl ⟨hx, h.le⟩ ⟨hx₀, le_refl x₀⟩ h
  have pos_r : ∀ x ∈ I, x₀ ≤ x → 0 ≤ g x := fun x hx h => by
    rcases h.lt_or_eq with h | h
    · exact (hg0 ▸ hr ⟨hx₀, le_refl x₀⟩ ⟨hx, h.le⟩ h).le
    · rw [← h, hg0]
  intro a ha b hb hab
  simp only
  by_cases hb0 : b < x₀
  · have ha0 : a < x₀ := hab.trans hb0
    simp only [ha0, hb0, ↓reduceIte, neg_one_mul, neg_lt_neg_iff]
    exact Real.sqrt_lt_sqrt (by linarith [pos_l b hb hb0])
      (by linarith [hl ⟨ha, ha0.le⟩ ⟨hb, hb0.le⟩ hab])
  · simp only [hb0, ↓reduceIte, one_mul]
    by_cases ha0 : a < x₀
    · simp only [ha0, ↓reduceIte, neg_one_mul]
      have := Real.sqrt_pos.2 (by linarith [pos_l a ha ha0] : 0 < 2 * g a)
      linarith [Real.sqrt_nonneg (2 * g b)]
    · simp only [ha0, ↓reduceIte, one_mul]
      have ha' : x₀ ≤ a := not_lt.1 ha0
      exact Real.sqrt_lt_sqrt (by linarith [pos_r a ha ha'])
        (by linarith [hr ⟨ha, ha'⟩ ⟨hb, not_lt.1 hb0⟩ hab])

/-- A function continuous on `(0, ∞)` with limit `-∞` at `0⁺` and `+∞` at `+∞` takes every real
value on `(0, ∞)`. -/
theorem dblZero_exists_eq_of_tendsto {f : ℝ → ℝ} (hc : ContinuousOn f (Ioi 0))
    (h0 : Tendsto f (𝓝[>] 0) atBot) (h1 : Tendsto f atTop atTop) (y : ℝ) :
    ∃ x, 0 < x ∧ f x = y := by
  obtain ⟨a, ha, ha0⟩ := ((h0.eventually (eventually_lt_atBot y)).and
    self_mem_nhdsWithin).exists
  obtain ⟨b, hb, hab⟩ := ((h1.eventually (eventually_gt_atTop y)).and
    (eventually_ge_atTop a)).exists
  have ha0 : (0:ℝ) < a := ha0
  have hsub : Icc a b ⊆ Ioi 0 := fun x hx => lt_of_lt_of_le ha0 hx.1
  obtain ⟨c, hc', hcy⟩ := intermediate_value_Icc hab (hc.mono hsub) ⟨ha.le, hb.le⟩
  exact ⟨c, hsub hc', hcy⟩

/-- Analytic inverse with explicit first Taylor coefficient: an analytic `f` with
`f'(x₀) ≠ 0` has an analytic local inverse `g` at `f x₀` with `g'(f x₀) = 1 / f'(x₀)`. -/
theorem dblZero_exists_analytic_inverse {f : ℝ → ℝ} {x₀ f' : ℝ} (hf : AnalyticAt ℝ f x₀)
    (hd : HasDerivAt f f' x₀) (hf' : f' ≠ 0) :
    ∃ g : ℝ → ℝ, AnalyticAt ℝ g (f x₀) ∧ HasDerivAt g f'⁻¹ (f x₀) ∧ g (f x₀) = x₀ ∧
      (∀ᶠ x in 𝓝 x₀, g (f x) = x) ∧ ∀ᶠ y in 𝓝 (f x₀), f (g y) = y := by
  have hne : deriv f x₀ ≠ 0 := by rw [hd.deriv]; exact hf'
  have hs := hf.hasStrictDerivAt
  have hl := hs.eventually_left_inverse hne
  refine ⟨hs.localInverse f (deriv f x₀) x₀ hne, hf.analyticAt_localInverse hne, ?_,
    hl.self_of_nhds, hl, hs.eventually_right_inverse hne⟩
  rw [← hd.deriv]
  exact (hs.to_localInverse hne).hasDerivAt

/-- The Airy coordinate has an analytic local inverse at `0` with derivative `p(x₀)^{-1/3}`. -/
theorem dblZero_exists_analytic_inverse_airyCoord {p : ℝ → ℝ} {x₀ : ℝ} (hp : AnalyticAt ℝ p x₀)
    (hp0 : 0 < p x₀) :
    ∃ g : ℝ → ℝ, AnalyticAt ℝ g 0 ∧ HasDerivAt g (p x₀ ^ (-(1/3:ℝ))) 0 ∧ g 0 = x₀ ∧
      (∀ᶠ x in 𝓝 x₀, g (dblZero_airyCoord p x₀ x) = x) ∧
      ∀ᶠ ζ in 𝓝 0, dblZero_airyCoord p x₀ (g ζ) = ζ := by
  have h0 : dblZero_airyCoord p x₀ x₀ = 0 := by simp [dblZero_airyCoord]
  obtain ⟨g, h1, h2, h3, h4, h5⟩ := dblZero_exists_analytic_inverse
    (dblZero_analyticAt_airyCoord hp hp0) (dblZero_hasDerivAt_airyCoord hp hp0)
    (Real.rpow_pos_of_pos hp0 _).ne'
  rw [h0, ← Real.rpow_neg hp0.le] at *
  exact ⟨g, h1, h2, h3, h4, h5⟩

end
