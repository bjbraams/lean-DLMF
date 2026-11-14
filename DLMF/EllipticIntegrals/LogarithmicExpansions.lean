/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import DLMF.EllipticIntegrals.LegendreIdentities
public import DLMF.EllipticIntegrals.SymmetricRelations
public import DLMFMathlib.Analysis.Analytic.ScalarSeries
import DLMF.EllipticIntegrals.SymmetricConnection
import DLMF.Hypergeometric.ConnectionFormulas
import Pochhammer.Estimates
import Mathlib.Analysis.Complex.Convex
import DLMFMathlib.Analysis.Integral.SquareRootPairRegularization
import Mathlib.Tactic

/-!
# Logarithmic expansions of complete elliptic integrals

The coefficients `d(n) = ψ(n+1) - ψ(n+1/2)` occur in the logarithmic expansions around
unit modulus. Their recurrence gives a linear norm bound, sufficient for analyticity of
the coefficient series throughout the unit disk. The resonant hypergeometric connection
formula `DLMF.Hypergeometric.logarithmic_connection_one_sub` gives the identity on a real
interval; the identity principle extends it across the slit unit disk.

## Main results

* `compEllIntLogCoeff_zero`, `compEllIntLogCoeff_succ`: the coefficient values (DLMF 19.12.3).
* `symmetricEllipticRF_zero_hasSum_log`: the logarithmic series of `R_F(0,w,1)`.
* `completeEllipticK_hasSum_log`, `completeEllipticE_hasSum_log`: the logarithmic series of
  `K(k)` and `E(k)` (DLMF 19.12.1–19.12.2).
-/

open Complex Set Filter Asymptotics
open scoped Real Topology
namespace DLMF.EllipticIntegrals
/-- DLMF 19.12.3: `d(m) = ψ(1 + m) - ψ(½ + m)`, `ψ` the digamma function
(`Complex.digamma`). -/
@[dlmf 19.12.E3, expose]
public noncomputable def compEllIntLogCoeff (m : ℕ) : ℂ :=
  digamma (1 + m) - digamma (1 / 2 + m)

/-- DLMF 19.12.3: `d(0) = 2 ln 2`. -/
@[dlmf 19.12.E3]
public theorem compEllIntLogCoeff_zero : compEllIntLogCoeff 0 = 2 * Complex.log 2 := by
  simp only [compEllIntLogCoeff, Nat.cast_zero, add_zero]
  rw [digamma_one, digamma_one_half]
  ring

/-- DLMF 19.12.3: `d(m + 1) = d(m) - 2/((2m + 1)(2m + 2))`. -/
@[dlmf 19.12.E3]
public theorem compEllIntLogCoeff_succ (m : ℕ) :
    compEllIntLogCoeff (m + 1) =
      compEllIntLogCoeff m - 2 / ((2 * m + 1) * (2 * m + 2)) := by
  have h1 : ∀ n : ℕ, (1 + (m : ℂ)) ≠ -n := by
    intro n h
    have := congrArg Complex.re h
    simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m), (n.cast_nonneg : (0 : ℝ) ≤ n)]
  have h2 : ∀ n : ℕ, (1 / 2 + (m : ℂ)) ≠ -n := by
    intro n h
    have := congrArg Complex.re h
    simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m), (n.cast_nonneg : (0 : ℝ) ≤ n)]
  simp only [compEllIntLogCoeff]
  push_cast
  rw [show (1 : ℂ) + (m + 1) = 1 + m + 1 by ring,
    show (1 / 2 : ℂ) + (m + 1) = 1 / 2 + m + 1 by ring,
    digamma_apply_add_one _ h1, digamma_apply_add_one _ h2]
  have hm1 : (1 + (m : ℂ)) ≠ 0 := by simpa using h1 0
  have hm2 : (1 / 2 + (m : ℂ)) ≠ 0 := by simpa using h2 0
  rw [show (2 * (m : ℂ) + 1) * (2 * m + 2) = 4 * ((1 / 2 + m) * (1 + m)) by ring]
  have hm3 : (1 + (m : ℂ) * 2) ≠ 0 := by
    rw [show 1 + (m : ℂ) * 2 = 2 * (1 / 2 + m) by ring]; exact mul_ne_zero two_ne_zero hm2
  field_simp
  ring

/-- A linear norm bound for the coefficients in the logarithmic elliptic expansions. -/
public theorem norm_compEllIntLogCoeff_le (n : ℕ) :
    ‖compEllIntLogCoeff n‖ ≤ ‖compEllIntLogCoeff 0‖ + 2 * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have he : (2 / ((2 * (n : ℂ) + 1) * (2 * n + 2)) : ℂ) =
        ((2 / ((2 * (n : ℝ) + 1) * (2 * n + 2)) : ℝ) : ℂ) := by push_cast; rfl
    have hb : ‖(2 / ((2 * (n : ℂ) + 1) * (2 * n + 2)) : ℂ)‖ ≤ 2 := by
      rw [he, norm_real, Real.norm_of_nonneg (by positivity)]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 * n + 1) * (2 * n + 2))).mpr
      nlinarith [hn]
    rw [compEllIntLogCoeff_succ]
    have H := norm_sub_le (compEllIntLogCoeff n) (2 / ((2 * (n : ℂ) + 1) * (2 * n + 2)))
    push_cast
    linarith only [H, ih, hb]

private noncomputable def ellipticLogSeriesCoeff (n : ℕ) : ℂ :=
  ((ascPochhammer ℂ n).eval (1 / 2 : ℂ)) ^ 2 / (n.factorial : ℂ) ^ 2

private theorem norm_ellipticLogSeriesCoeff_le (n : ℕ) :
    ‖ellipticLogSeriesCoeff n‖ ≤ 1 := by
  dsimp only [ellipticLogSeriesCoeff]
  have H := Complex.norm_ascPochhammer_eval_le_ascPochhammer (1 / 2 : ℂ) n
    (B := 1) (by norm_num)
  simp only [ascPochhammer_eval_one] at H
  rw [norm_div, norm_pow, norm_pow, Complex.norm_natCast]
  apply (div_le_one (by positivity : (0 : ℝ) < (n.factorial : ℝ) ^ 2)).mpr
  exact pow_le_pow_left₀ (norm_nonneg _) H 2
end DLMF.EllipticIntegrals
namespace DLMF.EllipticIntegrals
open DLMF.JacobiElliptic DLMF.Hypergeometric

private theorem summable_norm_ellipticLogSeriesCoeff {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n => ‖ellipticLogSeriesCoeff n‖ * r ^ n) :=
  (summable_geometric_of_lt_one hr0 hr1).of_nonneg_of_le (fun n => by positivity) fun n => by
    exact mul_le_of_le_one_left (pow_nonneg hr0 n)
      (norm_ellipticLogSeriesCoeff_le n)

private theorem summable_norm_ellipticLogSeriesCoeff_mul_logCoeff {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n => ‖ellipticLogSeriesCoeff n * compEllIntLogCoeff n‖ * r ^ n) := by
  have hn := summable_pow_mul_geometric_of_norm_lt_one 1 (r := r)
    (by simpa only [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1)
  have hmaj : Summable (fun n : ℕ => (‖compEllIntLogCoeff 0‖ + 2 * n) * r ^ n) := by
    convert ((summable_geometric_of_lt_one hr0 hr1).mul_left ‖compEllIntLogCoeff 0‖).add
      (hn.mul_left 2) using 1
    funext n
    simp only [pow_one]
    ring
  refine hmaj.of_nonneg_of_le (fun n => by positivity) fun n => ?_
  rw [norm_mul]
  gcongr
  exact (mul_le_of_le_one_left (norm_nonneg _) (norm_ellipticLogSeriesCoeff_le n)).trans
    (norm_compEllIntLogCoeff_le n)

private theorem ellipticLogSeries_hasSum {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun n => ellipticLogSeriesCoeff n * w ^ n *
        (-(1 / 2 : ℂ) * log w + compEllIntLogCoeff n))
      (-(1 / 2 : ℂ) * log w * (∑' n, ellipticLogSeriesCoeff n * w ^ n) +
        ∑' n, (ellipticLogSeriesCoeff n * compEllIntLogCoeff n) * w ^ n) := by
  have hs := (summable_norm_ellipticLogSeriesCoeff (norm_nonneg w) hw).of_norm_bounded
    (f := fun n => ellipticLogSeriesCoeff n * w ^ n)
      (by intro n; simp only [norm_mul, norm_pow]; rfl)
  have ht := (summable_norm_ellipticLogSeriesCoeff_mul_logCoeff (norm_nonneg w) hw).of_norm_bounded
    (f := fun n => (ellipticLogSeriesCoeff n * compEllIntLogCoeff n) * w ^ n)
      (by intro n; simp only [norm_mul, norm_pow]; rfl)
  exact ((hs.hasSum.mul_left (-(1 / 2 : ℂ) * log w)).add ht.hasSum).congr_fun fun n => by ring
/-- The logarithmic expansion of `R_F(0,w,1)` on the slit unit disk. -/
public theorem symmetricEllipticRF_zero_hasSum_log {w : ℂ}
    (hw : w ∈ slitPlane) (hwn : ‖w‖ < 1) :
    HasSum (fun n => ((ascPochhammer ℂ n).eval (1 / 2 : ℂ)) ^ 2 /
        (n.factorial : ℂ) ^ 2 * w ^ n * (-(1 / 2 : ℂ) * log w + compEllIntLogCoeff n))
      (symmetricEllipticRF 0 w 1) := by
  let U : Set ℂ := slitPlane ∩ Metric.ball 0 1
  let F : ℂ → ℂ := fun w => symmetricEllipticRF 0 w 1
  let G : ℂ → ℂ := fun w =>
    -(1 / 2 : ℂ) * log w * (∑' n, ellipticLogSeriesCoeff n * w ^ n) +
        ∑' n, (ellipticLogSeriesCoeff n * compEllIntLogCoeff n) * w ^ n
  have hF : AnalyticOnNhd ℂ F U := fun w hw =>
    analyticAt_symmetricEllipticRF_zero_comp analyticAt_id analyticAt_const hw.1 one_mem_slitPlane
  have hA := FormalMultilinearSeries.analyticOnNhd_tsum_mul_pow_of_summable_norm
    ellipticLogSeriesCoeff (fun _ hr0 hr1 => summable_norm_ellipticLogSeriesCoeff hr0 hr1)
  have hB := FormalMultilinearSeries.analyticOnNhd_tsum_mul_pow_of_summable_norm
    (fun n => ellipticLogSeriesCoeff n * compEllIntLogCoeff n)
    (fun _ hr0 hr1 => summable_norm_ellipticLogSeriesCoeff_mul_logCoeff hr0 hr1)
  have hG : AnalyticOnNhd ℂ G U := fun w hw =>
    ((analyticAt_const.mul (analyticAt_id.clog hw.1)).mul (hA w hw.2)).add (hB w hw.2)
  have h0 : ((1 / 2 : ℝ) : ℂ) ∈ U := by
    constructor
    · exact ofReal_mem_slitPlane.mpr (by norm_num)
    · norm_num
  have hU : IsPreconnected U := by
    exact ((starConvex_ofReal_slitPlane (by norm_num : (0 : ℝ) < 1 / 2)).inter
      ((convex_ball (0 : ℂ) 1).starConvex h0.2)).isPathConnected h0 |>.isConnected.isPreconnected
  have heq : EqOn F G U := by
    refine hF.eqOn_of_preconnected_of_frequently_eq hG hU h0 ?_
    refine Carlson.TwoVariable.frequently_ofReal_Ioo (a := 1 / 2) (ε := 1 / 4)
      (by norm_num) (fun x hx0 hx1 => ?_)
    have hx : 0 < x ∧ x < 1 := by constructor <;> linarith
    have hz : ‖(1 : ℂ) - (x : ℂ)‖ < 1 := by
      rw [← ofReal_one, ← ofReal_sub, norm_real, Real.norm_of_nonneg (by linarith)]
      linarith
    have hxnorm : ‖(x : ℂ)‖ < 1 := by rw [norm_real, Real.norm_of_nonneg hx.1.le]; exact hx.2
    have hpole : ∀ j : ℕ, (1 / 2 : ℂ) ≠ -(j : ℂ) := by
      intro j hj
      have H := congrArg Complex.re hj
      norm_num at H
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have H := logarithmic_connection_one_sub (a := (1 / 2 : ℂ)) (b := 1 / 2)
      (z := 1 - (x : ℂ)) 0 hpole hpole hz (by simpa using hxnorm)
    have hc : (1 / 2 : ℂ) + 1 / 2 + (0 : ℕ) = 1 := by norm_num
    rw [hc, ← ordinaryHypergeometric_div_Gamma_eq (by
      intro j hj
      have H := congrArg Complex.re hj
      norm_num at H
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]),
      Gamma_one, div_one] at H
    simp only [Nat.cast_zero, add_zero, Finset.sum_range_zero, mul_zero, pow_zero,
      Gamma_one_half_mul_self, sub_sub_cancel] at H
    have HK := DLMF.Elliptic.Real.completeEllipticKOfParameter_eq_ordinaryHypergeometric
      (m := 1 - x) (by rw [abs_of_pos (by linarith : (0 : ℝ) < 1 - x)]; linarith)
    have hsqrt : (Real.sqrt (1 - x) : ℂ) ^ 2 = 1 - x := by
      rw [← ofReal_pow, Real.sq_sqrt (by linarith)]; push_cast; ring
    have HKRF := completeEllipticK_eq_symmetricEllipticRF'
      (k := (Real.sqrt (1 - x) : ℂ))
    rw [hsqrt, sub_sub_cancel] at HKRF
    have HKr := completeEllipticK_eq_ofReal (k := (Real.sqrt (1 - x) : ℂ))
      (m := 1 - x) (by simpa only [ofReal_sub, ofReal_one] using hsqrt) (by linarith)
    rw [HKr, HK] at HKRF
    have HS := (ellipticLogSeries_hasSum hxnorm).tsum_eq
    dsimp only [F, G]
    rw [← HS]
    push_cast at HKRF
    rw [← HKRF, H]
    have hscalar (S : ℂ) : (π / 2 : ℂ) * (0 - 1 / π * S) = -(1 / 2 : ℂ) * S := by
      field_simp
      ring
    rw [hscalar, ← tsum_mul_left]
    congr 1
    funext n
    simp only [ellipticLogSeriesCoeff, compEllIntLogCoeff, pochhammer]
    rw [show (n : ℂ) + 1 = 1 + n by ring]
    field_simp
    ring
  have HS := ellipticLogSeries_hasSum hwn
  have H := heq ⟨hw, by simpa only [Metric.mem_ball, dist_zero_right] using hwn⟩
  dsimp only [F, G] at H
  rw [← H] at HS
  exact HS

private theorem log_one_div_jacobiComodulus {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) :
    log (1 / jacobiComodulus k) = -(1 / 2 : ℂ) * log (1 - k ^ 2) := by
  rw [one_div, jacobiComodulus, cpow_def_of_ne_zero (slitPlane_ne_zero hk), ← Complex.exp_neg,
    Complex.log_exp]
  · ring
  · norm_num [mul_im, log_im]
    linarith [neg_pi_lt_arg (1 - k ^ 2), arg_le_pi (1 - k ^ 2), Real.pi_pos]
  · norm_num [mul_im, log_im]
    linarith [neg_pi_lt_arg (1 - k ^ 2), arg_le_pi (1 - k ^ 2), Real.pi_pos]

/-- DLMF 19.12.1: `K(k) = Σ_{m ≥ 0} ((½)_m)²/(m!)² k'^{2m} (ln(1/k') + d(m))`, for complex
`k` with `0 < |k'| < 1`, `k' = (1 - k²)^{1/2}` principal, and `1 - k² ∉ (-∞, 0]`. -/
@[dlmf 19.12.E1]
public theorem completeEllipticK_hasSum_log {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane)
    (h1 : ‖jacobiComodulus k‖ < 1) :
    HasSum (fun m : ℕ => ((ascPochhammer ℂ m).eval (1 / 2 : ℂ)) ^ 2 / (m.factorial : ℂ) ^ 2 *
        jacobiComodulus k ^ (2 * m) *
          (Complex.log (1 / jacobiComodulus k) + compEllIntLogCoeff m))
      (completeEllipticK k) := by
  have hn : ‖1 - k ^ 2‖ < 1 := by
    rw [← jacobiComodulus_sq_eq_one_sub_sq, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) h1 (by decide : (2 : ℕ) ≠ 0)
  have hs := symmetricEllipticRF_zero_hasSum_log hk hn
  have hl := log_one_div_jacobiComodulus hk
  rw [← completeEllipticK_eq_symmetricEllipticRF hk] at hs
  exact hs.congr_fun fun m => by
    rw [hl, pow_mul, jacobiComodulus_sq_eq_one_sub_sq]
end DLMF.EllipticIntegrals

namespace DLMF.EllipticIntegrals
open DLMF.Hypergeometric DLMF.JacobiElliptic

private noncomputable def ellipticSecondLogSeriesCoeff (n : ℕ) : ℂ :=
  ((2 * n + 1 : ℂ) / (n + 1)) * ellipticLogSeriesCoeff n

private theorem ellipticSecondLogSeriesCoeff_eq (n : ℕ) :
    ellipticSecondLogSeriesCoeff n =
      (ascPochhammer ℂ n).eval (1 / 2) * (ascPochhammer ℂ n).eval (3 / 2) /
        ((ascPochhammer ℂ n).eval 2 * (n.factorial : ℂ)) := by
  have hh := congrArg (Polynomial.eval (1 / 2 : ℂ)) (ascPochhammer_succ_left (S := ℂ) n)
  have h2 := congrArg (Polynomial.eval (1 : ℂ)) (ascPochhammer_succ_left (S := ℂ) n)
  simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_one] at hh h2
  norm_num only [show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num] at hh
  norm_num only [show (1 : ℂ) + 1 = 2 by norm_num] at h2
  rw [ascPochhammer_eval_one, one_mul] at h2
  have hh' : (ascPochhammer ℂ n).eval (3 / 2) =
      (2 * n + 1) * (ascPochhammer ℂ n).eval (1 / 2) := by
    rw [ascPochhammer_succ_eval] at hh
    linear_combination -2 * hh
  rw [← h2, hh', Nat.factorial_succ]
  dsimp only [ellipticSecondLogSeriesCoeff, ellipticLogSeriesCoeff]
  push_cast
  field_simp

private theorem norm_ellipticSecondLogSeriesRatio_le (n : ℕ) :
    ‖((2 * n + 1 : ℂ) / (n + 1))‖ ≤ 2 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hr : ‖((2 * n + 1 : ℂ) / (n + 1))‖ =
      ‖(((2 * n + 1 : ℝ) / (n + 1) : ℝ) : ℂ)‖ := by congr 1 ; push_cast ; rfl
  rw [hr, norm_real, Real.norm_of_nonneg (by positivity)]
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr (by linarith [hn])

private noncomputable def ellipticSecondLogCorrection (n : ℕ) : ℂ :=
  1 / ((2 * n + 1) * (2 * n + 2))

private theorem norm_ellipticSecondLogCorrection_le (n : ℕ) :
    ‖ellipticSecondLogCorrection n‖ ≤ 1 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  dsimp only [ellipticSecondLogCorrection]
  rw [show (1 / ((2 * n + 1) * (2 * n + 2)) : ℂ) =
    ((1 / ((2 * n + 1) * (2 * n + 2)) : ℝ) : ℂ) by push_cast; rfl, norm_real,
    Real.norm_of_nonneg (by positivity)]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 * n + 1) * (2 * n + 2))).mpr
  nlinarith [hn]

private theorem summable_norm_ellipticSecondLogSeriesCoeff {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n => ‖ellipticSecondLogSeriesCoeff n‖ * r ^ n) := by
  refine ((summable_norm_ellipticLogSeriesCoeff hr0 hr1).mul_left 2).of_nonneg_of_le
    (fun n => by positivity) fun n => ?_
  dsimp only [ellipticSecondLogSeriesCoeff]
  rw [norm_mul]
  have H := norm_ellipticSecondLogSeriesRatio_le n
  nlinarith [mul_nonneg (norm_nonneg (ellipticLogSeriesCoeff n)) (pow_nonneg hr0 n)]

private theorem summable_norm_ellipticSecondLogSeriesCoeff_mul_logCoeff {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n => ‖ellipticSecondLogSeriesCoeff n *
      (compEllIntLogCoeff n - ellipticSecondLogCorrection n)‖ * r ^ n) := by
  have hmaj := ((summable_norm_ellipticLogSeriesCoeff_mul_logCoeff hr0 hr1).add
    (summable_norm_ellipticLogSeriesCoeff hr0 hr1)).mul_left 2
  refine hmaj.of_nonneg_of_le (fun n => by positivity) fun n => ?_
  dsimp only [ellipticSecondLogSeriesCoeff]
  have h1 := norm_ellipticSecondLogSeriesRatio_le n
  have h2 := norm_ellipticSecondLogCorrection_le n
  have H := norm_sub_le (compEllIntLogCoeff n) (ellipticSecondLogCorrection n)
  rw [norm_mul, norm_mul]
  calc _ ≤ 2 * ‖ellipticLogSeriesCoeff n‖ *
        (‖compEllIntLogCoeff n‖ + 1) * r ^ n := by
          gcongr
          exact H.trans (by linarith [h2])
       _ = _ := by rw [norm_mul]; ring

private theorem ellipticSecondLogSeries_hasSum {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun n => (1 / 2 : ℂ) * ellipticSecondLogSeriesCoeff n * w ^ (n + 1) *
        (-(1 / 2 : ℂ) * log w + compEllIntLogCoeff n - ellipticSecondLogCorrection n))
      (w / 2 * (-(1 / 2 : ℂ) * log w * (∑' n, ellipticSecondLogSeriesCoeff n * w ^ n) +
        ∑' n, (ellipticSecondLogSeriesCoeff n *
          (compEllIntLogCoeff n - ellipticSecondLogCorrection n)) * w ^ n)) := by
  have hs := (summable_norm_ellipticSecondLogSeriesCoeff (norm_nonneg w) hw).of_norm_bounded
    (f := fun n => ellipticSecondLogSeriesCoeff n * w ^ n)
      (by intro n; simp only [norm_mul, norm_pow]; rfl)
  have ht := (summable_norm_ellipticSecondLogSeriesCoeff_mul_logCoeff
    (norm_nonneg w) hw).of_norm_bounded
    (f := fun n => (ellipticSecondLogSeriesCoeff n *
      (compEllIntLogCoeff n - ellipticSecondLogCorrection n)) * w ^ n)
      (by intro n; simp only [norm_mul, norm_pow]; rfl)
  exact (((hs.hasSum.mul_left (-(1 / 2 : ℂ) * log w)).add ht.hasSum).mul_left
    (w / 2)).congr_fun fun n => by rw [pow_succ]; ring

private theorem symmetricEllipticRF_sub_RD_hasSum_log {w : ℂ}
    (hw : w ∈ slitPlane) (hwn : ‖w‖ < 1) :
    HasSum (fun n => (1 / 2 : ℂ) * ellipticSecondLogSeriesCoeff n * w ^ (n + 1) *
        (-(1 / 2 : ℂ) * log w + compEllIntLogCoeff n - ellipticSecondLogCorrection n))
      (symmetricEllipticRF 0 w 1 - (1 - w) / 3 * symmetricEllipticRD 0 w 1 - 1) := by
  let U : Set ℂ := slitPlane ∩ Metric.ball 0 1
  let F : ℂ → ℂ := fun w =>
    symmetricEllipticRF 0 w 1 - (1 - w) / 3 * symmetricEllipticRD 0 w 1 - 1
  let G : ℂ → ℂ := fun w => w / 2 *
    (-(1 / 2 : ℂ) * log w * (∑' n, ellipticSecondLogSeriesCoeff n * w ^ n) +
      ∑' n, (ellipticSecondLogSeriesCoeff n *
        (compEllIntLogCoeff n - ellipticSecondLogCorrection n)) * w ^ n)
  have hF : AnalyticOnNhd ℂ F U := fun w hw =>
    ((analyticAt_symmetricEllipticRF_zero_comp analyticAt_id analyticAt_const
      hw.1 one_mem_slitPlane).sub
      (((analyticAt_const.sub analyticAt_id).div_const (c := (3 : ℂ))).mul
      (analyticAt_symmetricEllipticRD_zero_comp analyticAt_id analyticAt_const
        hw.1 one_mem_slitPlane))).sub analyticAt_const
  have hA := FormalMultilinearSeries.analyticOnNhd_tsum_mul_pow_of_summable_norm
    ellipticSecondLogSeriesCoeff
    (fun _ hr0 hr1 => summable_norm_ellipticSecondLogSeriesCoeff hr0 hr1)
  have hB := FormalMultilinearSeries.analyticOnNhd_tsum_mul_pow_of_summable_norm
    (fun n => ellipticSecondLogSeriesCoeff n *
      (compEllIntLogCoeff n - ellipticSecondLogCorrection n))
    (fun _ hr0 hr1 => summable_norm_ellipticSecondLogSeriesCoeff_mul_logCoeff hr0 hr1)
  have hG : AnalyticOnNhd ℂ G U := fun w hw =>
    (analyticAt_id.div_const (c := (2 : ℂ))).mul
      (((analyticAt_const.mul (analyticAt_id.clog hw.1)).mul (hA w hw.2)).add (hB w hw.2))
  have h0 : ((1 / 2 : ℝ) : ℂ) ∈ U := by
    constructor
    · exact ofReal_mem_slitPlane.mpr (by norm_num)
    · norm_num
  have hU : IsPreconnected U := by
    exact ((starConvex_ofReal_slitPlane (by norm_num : (0 : ℝ) < 1 / 2)).inter
      ((convex_ball (0 : ℂ) 1).starConvex h0.2)).isPathConnected h0 |>.isConnected.isPreconnected
  have heq : EqOn F G U := by
    refine hF.eqOn_of_preconnected_of_frequently_eq hG hU h0 ?_
    refine Carlson.TwoVariable.frequently_ofReal_Ioo (a := 1 / 2) (ε := 1 / 4)
      (by norm_num) (fun x hx0 hx1 => ?_)
    have hx : 0 < x ∧ x < 1 := by constructor <;> linarith
    have hz : ‖(1 : ℂ) - (x : ℂ)‖ < 1 := by
      rw [← ofReal_one, ← ofReal_sub, norm_real, Real.norm_of_nonneg (by linarith)]
      linarith
    have hxnorm : ‖(x : ℂ)‖ < 1 := by rw [norm_real, Real.norm_of_nonneg hx.1.le]; exact hx.2
    have hpole : ∀ j : ℕ, (1 / 2 : ℂ) ≠ -(j : ℂ) := by
      intro j hj
      have H := congrArg Complex.re hj
      norm_num at H
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have hnpole : ∀ j : ℕ, (-(1 / 2) : ℂ) ≠ -(j : ℂ) := by
      intro j hj
      have H := congrArg Complex.re hj
      norm_num at H
      rcases Nat.eq_zero_or_pos j with h | h
      · subst j; norm_num at H
      · have H1 : (1 : ℝ) ≤ j := by exact_mod_cast h
        linarith
    have H := DLMF.Hypergeometric.logarithmic_connection_one_sub (a := (-(1 / 2) : ℂ))
      (b := 1 / 2) (z := 1 - (x : ℂ)) 1 hnpole hpole hz (by simpa using hxnorm)
    have hg3 : Gamma (3 / 2 : ℂ) = (1 / 2) * Gamma (1 / 2) := by
      convert Gamma_add_one (1 / 2 : ℂ) (by norm_num) using 1 ; norm_num
    have hgn : Gamma (-(1 / 2) : ℂ) = -2 * Gamma (1 / 2) := by
      have H := Gamma_add_one (-(1 / 2) : ℂ) (by norm_num)
      norm_num only [show (-(1 / 2) : ℂ) + 1 = 1 / 2 by norm_num] at H
      linear_combination 2 * H
    have hgP : Gamma (1 / 2 : ℂ) * Gamma (3 / 2) = π / 2 := by
      rw [hg3, mul_left_comm, Gamma_one_half_mul_self]
      ring
    have hgN : Gamma (-(1 / 2) : ℂ) * Gamma (1 / 2) = -2 * π := by
      rw [hgn, mul_assoc, Gamma_one_half_mul_self]
    have hc : (-(1 / 2) : ℂ) + 1 / 2 + (1 : ℕ) = 1 := by norm_num
    rw [hc, ← ordinaryHypergeometric_div_Gamma_eq (by
      intro j hj
      have H := congrArg Complex.re hj
      norm_num at H
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]), Gamma_one, div_one] at H
    norm_num only [Nat.cast_one, Finset.sum_range_one, pochhammer_zero, Nat.factorial_zero,
      Nat.cast_zero, mul_one, one_mul, div_one, pow_zero, pow_one, mul_zero, zero_mul,
      sub_zero, Nat.sub_zero, Nat.sub_self, add_zero, sub_sub_cancel,
      show (-(1 / 2) : ℂ) + 1 = 1 / 2 by norm_num,
      show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num, hgP, hgN] at H
    have HE := DLMF.Elliptic.Real.completeEllipticEOfParameter_eq_ordinaryHypergeometric
      (m := 1 - x) (by rw [abs_of_pos (by linarith : (0 : ℝ) < 1 - x)]; linarith)
    have hsqrt : (Real.sqrt (1 - x) : ℂ) ^ 2 = 1 - x := by
      rw [← ofReal_pow, Real.sq_sqrt (by linarith)]; push_cast; ring
    have hslit : 1 - (Real.sqrt (1 - x) : ℂ) ^ 2 ∈ slitPlane := by
      rw [hsqrt, sub_sub_cancel]; exact ofReal_mem_slitPlane.mpr hx.1
    have HEfull := completeEllipticE_eq_symmetricElliptic hslit
    have HKRF := completeEllipticK_eq_symmetricEllipticRF hslit
    have HEeq : completeEllipticE (Real.sqrt (1 - x) : ℂ) =
        symmetricEllipticRF 0 x 1 - (1 - x) / 3 * symmetricEllipticRD 0 x 1 := by
      rw [hsqrt, sub_sub_cancel] at HEfull HKRF
      linear_combination -HEfull.2.2.1 - HEfull.2.2.2.1 + HKRF
    have HEr := completeEllipticE_eq_ofReal (k := (Real.sqrt (1 - x) : ℂ))
      (m := 1 - x) (by simpa only [ofReal_sub, ofReal_one] using hsqrt) (by linarith)
    rw [HEr, HE] at HEeq
    push_cast at HEeq
    have HS := (ellipticSecondLogSeries_hasSum hxnorm).tsum_eq
    dsimp only [F, G]
    rw [← HS, ← HEeq, H]
    have hscalar (S : ℂ) : (π / 2 : ℂ) * (1 / (π / 2) -
        (1 - (x : ℂ) - 1) / (-2 * π) * S) - 1 = -(x : ℂ) / 4 * S := by
      field_simp
      ring
    rw [hscalar, ← tsum_mul_left]
    congr 1
    funext n
    rw [ellipticSecondLogSeriesCoeff_eq]
    have h1 : ∀ j : ℕ, (n : ℂ) + 1 ≠ -(j : ℂ) := by
      intro j hj; have H := congrArg Complex.re hj; norm_num at H
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h2 : ∀ j : ℕ, (n : ℂ) + 1 / 2 ≠ -(j : ℂ) := by
      intro j hj; have H := congrArg Complex.re hj; norm_num at H
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hd1 := digamma_apply_add_one ((n : ℂ) + 1) h1
    have hd2 := digamma_apply_add_one ((n : ℂ) + 1 / 2) h2
    have hn1 : (1 + (n : ℂ)) ≠ 0 := by
      intro h; have H := congrArg Complex.re h; norm_num at H
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hnh : (1 / 2 + (n : ℂ)) ≠ 0 := by
      intro h; have H := congrArg Complex.re h; norm_num at H
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hna : (2 * (n : ℂ) + 1) ≠ 0 := by
      intro h; have H := congrArg Complex.re h; norm_num at H
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hnb : (2 * (n : ℂ) + 2) ≠ 0 := by
      intro h; have H := congrArg Complex.re h; norm_num at H
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hpsi : log (x : ℂ) - digamma ((n : ℂ) + 1) - digamma ((n : ℂ) + 1 + 1) +
        digamma (-(1 / 2 : ℂ) + n + 1) + digamma ((1 / 2 : ℂ) + n + 1) =
        -2 * (-(1 / 2 : ℂ) * log x + compEllIntLogCoeff n - ellipticSecondLogCorrection n) := by
      rw [hd1, show (-(1 / 2) : ℂ) + n + 1 = (n : ℂ) + 1 / 2 by ring,
        show (1 / 2 : ℂ) + n + 1 = (n : ℂ) + 1 / 2 + 1 by ring, hd2]
      dsimp only [compEllIntLogCoeff, ellipticSecondLogCorrection]
      rw [show (n : ℂ) + 1 = 1 + n by ring, show (n : ℂ) + 1 / 2 = 1 / 2 + n by ring]
      have hInv : (1 + (n : ℂ) * 2) * (1 + (n : ℂ) * 2)⁻¹ = 1 :=
        mul_inv_cancel₀ (by simpa only [add_comm, mul_comm] using hna)
      field_simp [hn1, hnh, hna, hnb]
      linear_combination ((n : ℂ) + 1) * hInv
    rw [hpsi]
    have h2fac := congrArg (Polynomial.eval (1 : ℂ)) (ascPochhammer_succ_left (S := ℂ) n)
    simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_one, one_mul, ascPochhammer_eval_one] at h2fac
    norm_num only [show (1 : ℂ) + 1 = 2 by norm_num] at h2fac
    simp only [pochhammer]
    rw [← h2fac, Nat.factorial_succ, pow_succ]
    push_cast
    ring
  have HS := ellipticSecondLogSeries_hasSum hwn
  have H := heq ⟨hw, by simpa only [Metric.mem_ball, dist_zero_right] using hwn⟩
  dsimp only [F, G] at H
  rw [← H] at HS
  exact HS
/-- DLMF 19.12.2:
`E(k) = 1 + ½ Σ_{m ≥ 0} (½)_m (3/2)_m/((2)_m m!) k'^{2m+2} (ln(1/k') + d(m) - 1/((2m+1)(2m+2)))`,
for complex `k` with `|k'| < 1`, `k' = (1 - k²)^{1/2}` principal, and `1 - k² ∉ (-∞, 0)`. -/
@[dlmf 19.12.E2]
public theorem completeEllipticE_hasSum_log {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane ∨ k ^ 2 = 1)
    (h1 : ‖jacobiComodulus k‖ < 1) :
    HasSum (fun m : ℕ => (1 / 2 : ℂ) * ((ascPochhammer ℂ m).eval (1 / 2 : ℂ) *
        (ascPochhammer ℂ m).eval (3 / 2 : ℂ) /
          ((ascPochhammer ℂ m).eval (2 : ℂ) * (m.factorial : ℂ)) *
        jacobiComodulus k ^ (2 * m + 2) *
          (Complex.log (1 / jacobiComodulus k) + compEllIntLogCoeff m -
            1 / ((2 * m + 1) * (2 * m + 2)))))
      (completeEllipticE k - 1) := by
  rcases hk with hk | hk
  · have hn : ‖1 - k ^ 2‖ < 1 := by
      rw [← jacobiComodulus_sq_eq_one_sub_sq, norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) h1 (by decide : (2 : ℕ) ≠ 0)
    have hs := symmetricEllipticRF_sub_RD_hasSum_log hk hn
    have HEfull := completeEllipticE_eq_symmetricElliptic hk
    have HKRF := completeEllipticK_eq_symmetricEllipticRF hk
    have HEeq : symmetricEllipticRF 0 (1 - k ^ 2) 1 -
        (1 - (1 - k ^ 2)) / 3 * symmetricEllipticRD 0 (1 - k ^ 2) 1 - 1 =
        completeEllipticE k - 1 := by
      linear_combination HEfull.2.2.1 + HEfull.2.2.2.1 - HKRF
    rw [HEeq] at hs
    exact hs.congr_fun fun m => by
      rw [ellipticSecondLogSeriesCoeff_eq, log_one_div_jacobiComodulus hk,
        show 2 * m + 2 = 2 * (m + 1) by omega, pow_mul,
        jacobiComodulus_sq_eq_one_sub_sq]
      dsimp only [ellipticSecondLogCorrection]
      ring
  · have HE := completeEllipticE_eq_ofReal (m := 1) hk (by norm_num)
    rw [DLMF.Elliptic.Real.completeEllipticEOfParameter_one, ofReal_one] at HE
    have hkp : jacobiComodulus k = 0 := by
      norm_num [jacobiComodulus, hk]
    rw [HE, sub_self]
    convert (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0) using 1
    funext m
    rw [hkp, zero_pow (by omega : 2 * m + 2 ≠ 0)]
    simp
end DLMF.EllipticIntegrals

namespace DLMF.EllipticIntegrals
open DLMF.JacobiElliptic
/-- The first logarithmic correction to `R_G(0,x,1)` has remainder `O(x² log x)` as `x → 0+`. -/
public theorem symmetricEllipticRG_zero_one_isBigO_log :
    (fun x : ℝ => symmetricEllipticRG 0 x 1 -
      ((1 / 2 + x / 8 * (Real.log (16 / x) - 1) : ℝ) : ℂ)) =O[𝓝[>] 0]
        fun x : ℝ => x ^ 2 * Real.log x := by
  let A : ℂ → ℂ := fun w => ∑' n, ellipticSecondLogSeriesCoeff n * w ^ n
  let B : ℂ → ℂ := fun w => ∑' n, (ellipticSecondLogSeriesCoeff n *
    (compEllIntLogCoeff n - ellipticSecondLogCorrection n)) * w ^ n
  have hAa : AnalyticAt ℂ A 0 :=
    FormalMultilinearSeries.analyticOnNhd_tsum_mul_pow_of_summable_norm
      ellipticSecondLogSeriesCoeff (fun _ hr0 hr1 =>
        summable_norm_ellipticSecondLogSeriesCoeff hr0 hr1) 0 (by simp)
  have hBa : AnalyticAt ℂ B 0 :=
    FormalMultilinearSeries.analyticOnNhd_tsum_mul_pow_of_summable_norm
      (fun n => ellipticSecondLogSeriesCoeff n *
        (compEllIntLogCoeff n - ellipticSecondLogCorrection n)) (fun _ hr0 hr1 =>
        summable_norm_ellipticSecondLogSeriesCoeff_mul_logCoeff hr0 hr1) 0 (by simp)
  have hAz : A 0 = 1 := by
    dsimp only [A]
    rw [tsum_eq_single 0 (fun n hn => by rw [zero_pow hn, mul_zero])]
    norm_num [ellipticSecondLogSeriesCoeff, ellipticLogSeriesCoeff]
  have hBz : B 0 = compEllIntLogCoeff 0 - 1 / 2 := by
    dsimp only [B]
    rw [tsum_eq_single 0 (fun n hn => by rw [zero_pow hn, mul_zero])]
    norm_num [ellipticSecondLogSeriesCoeff, ellipticLogSeriesCoeff, ellipticSecondLogCorrection]
  have hc : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (continuous_ofReal.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hA : (fun x : ℝ => A x - 1) =O[𝓝[>] 0] fun x : ℝ => x := by
    apply IsBigO.of_norm_right
    simpa only [hAz, sub_zero, Function.comp_def, norm_real] using
      (hAa.differentiableAt.hasDerivAt.isBigO_sub.comp_tendsto hc).norm_right
  have hB : (fun x : ℝ => B x - (compEllIntLogCoeff 0 - 1 / 2)) =O[𝓝[>] 0]
      fun x : ℝ => x := by
    apply IsBigO.of_norm_right
    simpa only [hBz, sub_zero, Function.comp_def, norm_real] using
      (hBa.differentiableAt.hasDerivAt.isBigO_sub.comp_tendsto hc).norm_right
  have hlog : (fun x : ℝ => log (x : ℂ)) =O[𝓝[>] 0] Real.log := by
    apply IsBigO.of_bound 1
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [← ofReal_log hx.le, norm_real, one_mul]
  have hx : (fun x : ℝ => (x : ℂ)) =O[𝓝[>] 0] fun x : ℝ => x := by
    apply IsBigO.of_bound 1
    exact Eventually.of_forall fun x => by rw [norm_real, one_mul]
  have hsum : (fun x : ℝ => -(1 / 2 : ℂ) * log (x : ℂ) * (A x - 1) +
      (B x - (compEllIntLogCoeff 0 - 1 / 2))) =O[𝓝[>] 0]
        fun x : ℝ => x * Real.log x := by
    have H1 := (hlog.mul hA).const_mul_left (-(1 / 2 : ℂ))
    have H2 := hB.trans Real.isBigO_id_mul_log_nhdsGT_zero
    apply (H1.add (by simpa only [mul_comm] using H2)).congr'
    · exact Eventually.of_forall fun _ => by ring
    · exact Eventually.of_forall fun x => mul_comm _ _
  have H := (hx.mul hsum).const_mul_left (1 / 4 : ℂ)
  apply H.congr'
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx
    have hslit : (x : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hx.1
    have hn : ‖(x : ℂ)‖ < 1 := by rw [norm_real, Real.norm_of_nonneg hx.1.le]; exact hx.2
    have HS := (symmetricEllipticRF_sub_RD_hasSum_log hslit hn).unique
      (ellipticSecondLogSeries_hasSum hn)
    have HRG := (symmetricEllipticRG_zero_eq hslit one_mem_slitPlane).2
    have HG : 2 * symmetricEllipticRG 0 x 1 - 1 =
        (x : ℂ) / 2 * (-(1 / 2 : ℂ) * log x * A x + B x) := by
      dsimp only [A, B]
      linear_combination HS + (1 / 3 : ℂ) * HRG
    have hlog2 : log (2 : ℂ) = (Real.log 2 : ℂ) :=
      (ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
    rw [compEllIntLogCoeff_zero, ← ofReal_log hx.1.le, hlog2]
    have hlog16 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [Real.log_div (by norm_num : (16 : ℝ) ≠ 0) hx.1.ne', hlog16]
    push_cast
    rw [← ofReal_log hx.1.le] at HG
    linear_combination -(1 / 2 : ℂ) * HG
  · exact Eventually.of_forall fun x => by ring
end DLMF.EllipticIntegrals
