/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Integer
public import DLMF.OrthogonalPolynomials.Integrals

/-!
# Neumann's integral for `Q_n` (Temme §8.5)

For `z ∉ (-∞, 1]`, `½ ∫₋₁¹ dt/(z - t) = Q₀(z)`. The polynomials `R_n` of `Q_n = P_n Q₀ - R_n`
are `½ ∫₋₁¹ (P_n(z) - P_n(t))/(z - t) dt`: both satisfy the Legendre recurrence, by the
recurrence for `P_n` and `∫₋₁¹ P_{n+1} = 0`. Together these give Neumann's integral
`Q_n(z) = ½ ∫₋₁¹ P_n(t)/(z - t) dt`.
-/

@[expose] public section

open Complex Filter Set DLMF.Hypergeometric
open scoped Topology Real
open DLMF.OrthogonalPolynomials

noncomputable section

namespace DLMF.Legendre

/-- For `z ∉ (-∞, 1]` and real `t ≤ 1`, `z - t` lies in the slit plane. -/
theorem sub_ofReal_mem_slitPlane {z : ℂ} (hz : z - 1 ∈ slitPlane) {t : ℝ} (ht : t ≤ 1) :
    z - t ∈ slitPlane := by
  rw [show z - (t : ℂ) = (z - 1) + ((1 - t : ℝ) : ℂ) by push_cast; ring]
  rw [mem_slitPlane_iff] at hz ⊢
  rcases hz with h | h
  · left; simp at h ⊢; linarith
  · right; simpa using h

/-- `log(z+1) - log(z-1) = log((z+1)/(z-1))` off `(-∞, 1]`. -/
theorem log_add_one_sub_log_sub_one {z : ℂ} (hz : z - 1 ∈ slitPlane) :
    log (z + 1) - log (z - 1) = log ((z + 1) / (z - 1)) := by
  set D : Set ℂ := {w | w - 1 ∈ slitPlane}
  have h1 (w : ℂ) (hw : w ∈ D) : w + 1 ∈ slitPlane := by
    have := one_add_mem_slitPlane_of_sub_one hw; rwa [add_comm] at this
  have hf : AnalyticOnNhd ℂ (fun w : ℂ => log (w + 1) - log (w - 1)) D := by
    intro w hw
    exact ((analyticAt_clog (h1 w hw)).comp_of_eq (f := fun w : ℂ => w + 1) (by fun_prop)
      rfl).sub ((analyticAt_clog hw).comp_of_eq (f := fun w : ℂ => w - 1) (by fun_prop) rfl)
  have hg : AnalyticOnNhd ℂ (fun w : ℂ => log ((w + 1) / (w - 1))) D := by
    intro w hw
    have hw1 : w - 1 ≠ 0 := slitPlane_ne_zero hw
    exact (analyticAt_clog (div_mem_slitPlane hw)).comp_of_eq
      (by fun_prop (disch := exact hw1)) rfl
  have h2 : ((2 : ℝ) : ℂ) ∈ D := by show ((2 : ℝ) : ℂ) - 1 ∈ slitPlane; norm_num
  refine hf.eqOn_of_preconnected_of_frequently_eq hg isPreconnected_sub_one_mem_slitPlane h2 ?_ hz
  have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] (2 : ℝ)) (𝓝[≠] ((2 : ℝ) : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, ofReal_inj] using hr
  apply ht.frequently
  apply Eventually.frequently
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (show (1 : ℝ) < 2 by norm_num))] with r hr
  have hr1 : (0 : ℝ) < r - 1 := by linarith [show (1 : ℝ) < r from hr]
  have hr2 : (0 : ℝ) < r + 1 := by linarith [show (1 : ℝ) < r from hr]
  rw [show (r : ℂ) + 1 = ((r + 1 : ℝ) : ℂ) by push_cast; ring,
    show (r : ℂ) - 1 = ((r - 1 : ℝ) : ℂ) by push_cast; ring, ← ofReal_div,
    ← ofReal_log hr2.le, ← ofReal_log hr1.le, ← ofReal_log (by positivity),
    Real.log_div hr2.ne' hr1.ne']
  push_cast; ring

/-- `½ ∫₋₁¹ dt/(z - t) = Q₀(z)`. -/
theorem integral_recip_sub {z : ℂ} (hz : z - 1 ∈ slitPlane) :
    1 / 2 * ∫ t in (-1 : ℝ)..1, 1 / (z - t) = legendreQ 0 z := by
  have hd (t : ℝ) (ht : t ∈ uIcc (-1 : ℝ) 1) : HasDerivAt (fun t : ℝ => -log (z - t))
      (1 / (z - t)) t := by
    have ht1 : t ≤ 1 := by rw [uIcc_of_le (by norm_num)] at ht; exact ht.2
    have h := ((hasDerivAt_id t).ofReal_comp.const_sub z).clog_real
      (sub_ofReal_mem_slitPlane hz ht1)
    refine h.neg.congr_deriv ?_
    simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
    refine ContinuousOn.intervalIntegrable fun t ht => ?_
    have ht1 : t ≤ 1 := by rw [uIcc_of_le (by norm_num)] at ht; exact ht.2
    exact ((continuousAt_const.div (continuousAt_const.sub
      continuous_ofReal.continuousAt) (slitPlane_ne_zero (sub_ofReal_mem_slitPlane hz ht1)))
      ).continuousWithinAt), legendreQ_zero hz, ← log_add_one_sub_log_sub_one hz]
  push_cast
  ring_nf

/-- The difference quotient `(P_n(z) - P_n(t))/(z - t)` is continuous in `t ∈ [-1, 1]`. -/
theorem continuousOn_legendre_dq (n : ℕ) {z : ℂ} (hz : z - 1 ∈ slitPlane) :
    ContinuousOn (fun t : ℝ => (legendrePolyP n z - legendrePolyP n t) / (z - t))
        (uIcc (-1 : ℝ) 1) := by
  intro t ht
  have ht1 : t ≤ 1 := by rw [uIcc_of_le (by norm_num)] at ht; exact ht.2
  exact ((continuousAt_const.sub ((differentiable_legendrePolyP n).continuous.continuousAt.comp
    continuous_ofReal.continuousAt)).div (continuousAt_const.sub continuous_ofReal.continuousAt)
    (slitPlane_ne_zero (sub_ofReal_mem_slitPlane hz ht1))).continuousWithinAt

/-- `∫₋₁¹ P_{n+1} = 0`, by orthogonality to `P₀`. -/
theorem integral_legendrePolyP_succ (n : ℕ) :
    ∫ t in (-1 : ℝ)..1, legendrePolyP (n + 1) (t : ℂ) = 0 := by
  have h := DLMF.OrthogonalPolynomials.legendre_orthogonality 0 (n + 1)
  simpa [legendrePolyP_zero] using h

/-- `R_n(z) = ½ ∫₋₁¹ (P_n(z) - P_n(t))/(z - t) dt` (Temme, proof of (8.33)). -/
theorem legendreQPoly_eq_integral (n : ℕ) {z : ℂ} (hz : z - 1 ∈ slitPlane) :
    (legendreQPoly n).eval z =
      1 / 2 * ∫ t in (-1 : ℝ)..1, (legendrePolyP n z - legendrePolyP n t) / (z - t) := by
  have hne (t : ℝ) (ht : t ∈ uIcc (-1 : ℝ) 1) : z - t ≠ 0 := by
    have ht1 : t ≤ 1 := by rw [uIcc_of_le (by norm_num)] at ht; exact ht.2
    exact slitPlane_ne_zero (sub_ofReal_mem_slitPlane hz ht1)
  have hI (k : ℕ) := (continuousOn_legendre_dq k hz).intervalIntegrable (μ := MeasureTheory.volume)
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [legendreQPoly, legendrePolyP_zero]
    | 1, _ =>
      rw [legendreQPoly, Polynomial.eval_one,
        intervalIntegral.integral_congr (g := fun _ => (1 : ℂ)) (fun t ht => by
          simp only [legendrePolyP_one]; exact div_self (hne t ht))]
      simp; norm_num
    | n + 2, ih =>
      have h1 := ih (n + 1) (by omega)
      have h0 := ih n (by omega)
      have hLc : Continuous fun t : ℝ => legendrePolyP (n + 1) (t : ℂ) :=
        (differentiable_legendrePolyP _).continuous.comp continuous_ofReal
      have hrec : ∀ t ∈ uIcc (-1 : ℝ) 1,
          (legendrePolyP (n + 2) z - legendrePolyP (n + 2) t) / (z - t) =
            ((2 * n + 3) * (z * ((legendrePolyP (n + 1) z - legendrePolyP (n + 1) t) / (z - t)) +
              legendrePolyP (n + 1) t) - (n + 1)
                  * ((legendrePolyP n z - legendrePolyP n t) / (z - t))) /
              (n + 2) := by
        intro t ht
        have hn : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
        have rz := legendrePolyP_recurrence n z
        have rt := legendrePolyP_recurrence n (t : ℂ)
        have := hne t ht
        field_simp
        linear_combination rz - rt
      rw [intervalIntegral.integral_congr hrec, intervalIntegral.integral_div,
        intervalIntegral.integral_sub ((((hI (n + 1)).const_mul z).add
          (hLc.intervalIntegrable _ _)
            ).const_mul _) ((hI n).const_mul _),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add ((hI (n + 1)).const_mul z)
          (hLc.intervalIntegrable _ _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        integral_legendrePolyP_succ]
      simp only [legendreQPoly, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
        Polynomial.eval_X]
      rw [h1, h0]
      have hn : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
      field_simp
      ring

/-- **Neumann's integral** `Q_n(z) = ½ ∫₋₁¹ P_n(t)/(z - t) dt` for `z ∉ (-∞, 1]`
(Temme (8.33)). -/
theorem legendreQ_nat_eq_integral (n : ℕ) {z : ℂ} (hz : z - 1 ∈ slitPlane) :
    legendreQ n z = 1 / 2 * ∫ t in (-1 : ℝ)..1, legendrePolyP n t / (z - t) := by
  have hne (t : ℝ) (ht : t ∈ uIcc (-1 : ℝ) 1) : z - t ≠ 0 := by
    have ht1 : t ≤ 1 := by rw [uIcc_of_le (by norm_num)] at ht; exact ht.2
    exact slitPlane_ne_zero (sub_ofReal_mem_slitPlane hz ht1)
  have hsplit : ∀ t ∈ uIcc (-1 : ℝ) 1, legendrePolyP n t / (z - t) =
      legendrePolyP n z * (1 / (z - t)) - (legendrePolyP n z - legendrePolyP n t) / (z - t) := by
    intro t ht; have := hne t ht; field_simp; ring
  have hinv : IntervalIntegrable (fun t : ℝ => 1 / (z - t)) MeasureTheory.volume (-1) 1 := by
    refine ContinuousOn.intervalIntegrable fun t ht => ?_
    exact (continuousAt_const.div (continuousAt_const.sub continuous_ofReal.continuousAt)
      (hne t ht)).continuousWithinAt
  rw [intervalIntegral.integral_congr hsplit, intervalIntegral.integral_sub (hinv.const_mul _)
    ((continuousOn_legendre_dq n hz).intervalIntegrable), intervalIntegral.integral_const_mul,
    mul_sub, ← mul_assoc, mul_comm (1 / 2 : ℂ), mul_assoc, integral_recip_sub hz,
    ← legendreQPoly_eq_integral n hz, legendreQ_nat n hz,
    legendreP_nat n (one_add_mem_slitPlane_of_sub_one hz)]

end DLMF.Legendre

end
