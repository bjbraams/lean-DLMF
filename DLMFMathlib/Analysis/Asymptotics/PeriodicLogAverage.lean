/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.ContinuousMap.Compact
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic
/-!
# Logarithmic averages of periodic functions

For an integrable periodic real function, integration against `1/t` equals the period mean
times `log R`, up to a bounded error. The mean-zero primitive is continuous and periodic,
hence bounded; integration by parts controls the error. Mathlib supplies periodic interval
integration and descent to the compact circle, while TauCeti supplies almost-everywhere
integration by parts for the absolutely continuous primitive.

## Main results

* `Function.Periodic.isBigO_integral_div_sub_mean_mul_log`: the logarithmic averaging formula.
-/

public noncomputable section
open Filter Set MeasureTheory Asymptotics
open scoped Topology
namespace Real
/-- Integrating an integrable periodic function against `1/t` gives its period mean times
`log R`, with a bounded error as `R` tends to infinity. -/
lemma _root_.Function.Periodic.isBigO_integral_div_sub_mean_mul_log
    {p : ℝ → ℝ} {T : ℝ} (hp : Function.Periodic p T) (hT : 0 < T)
    (hi : IntervalIntegrable p volume 0 T) :
    (fun R : ℝ => (∫ t in (1 : ℝ)..R, p t / t) -
      ((∫ t in (0 : ℝ)..T, p t) / T) * log R) =O[atTop] (fun _ => (1 : ℝ)) := by
  let m : ℝ := (∫ t in (0 : ℝ)..T, p t) / T
  let q : ℝ → ℝ := fun t => p t - m
  let P : ℝ → ℝ := fun t => ∫ u in (0 : ℝ)..t, q u
  have hpi (a b : ℝ) : IntervalIntegrable p volume a b :=
    hp.intervalIntegrable hT.ne' (t := 0) (by simpa only [zero_add] using hi) a b
  have hqi (a b : ℝ) : IntervalIntegrable q volume a b :=
    (hpi a b).sub intervalIntegrable_const
  have hqper : Function.Periodic q T := by
    intro t
    dsimp only [q]
    rw [hp]
  have hqzero : (∫ t in (0 : ℝ)..T, q t) = 0 := by
    dsimp only [q, m]
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    field_simp [hT.ne']
    ring
  have hPper : Function.Periodic P T := by
    intro t
    dsimp only [P]
    rw [hqper.intervalIntegral_add_eq_add 0 t hqi, zero_add, hqzero, add_zero]
  have hPc : Continuous P := intervalIntegral.continuous_primitive hqi 0
  have : Fact (0 < T) := ⟨hT⟩
  let F : C(AddCircle T, ℝ) := ⟨hPper.lift, continuous_coinduced_dom.mpr hPc⟩
  let C : ℝ := ‖F‖
  have hC (t : ℝ) : |P t| ≤ C := by
    exact F.norm_coe_le_norm (t : AddCircle T)
  have hC0 : 0 ≤ C := norm_nonneg F
  have hbound : ∀ R : ℝ, 1 ≤ R → |(∫ t in (1 : ℝ)..R, p t / t) - m * log R| ≤ 3 * C := by
    intro R hR
    have hne (t : ℝ) (ht : t ∈ uIcc 1 R) : t ≠ 0 := by
      rw [uIcc_of_le hR] at ht
      linarith [ht.1]
    have hInv : ContDiffOn ℝ 1 (fun t : ℝ => t⁻¹) (uIcc 1 R) :=
      contDiffOn_id.inv hne
    have hPin : AbsolutelyContinuousOnInterval P 1 R := by
      have h : AbsolutelyContinuousOnInterval (fun t => ∫ u in (1 : ℝ)..t, q u) 1 R :=
        (hqi 1 R).absolutelyContinuousOnInterval_intervalIntegral' left_mem_uIcc
      have he (t : ℝ) : (∫ u in (1 : ℝ)..t, q u) = P t - P 1 :=
        (intervalIntegral.integral_interval_sub_left (hqi 0 t) (hqi 0 1)).symm
      have hconst := (LipschitzWith.const (P 1)).lipschitzOnWith.absolutelyContinuousOnInterval
        (a := 1) (b := R)
      exact (h.fun_add hconst).congr fun t _ => by dsimp only; rw [he]; simp
    have hpd : ∀ᵐ t, t ∈ uIoc 1 R → HasDerivAt P (q t) t := by
      filter_upwards [(hqi 0 R).ae_hasDerivAt_integral] with t ht htI
      exact ht (by rw [uIcc_of_le (by linarith : (0 : ℝ) ≤ R)];
                   exact ⟨by have hleft := htI.1
                             rw [min_eq_left hR] at hleft
                             linarith,
                     by simpa only [max_eq_right hR] using htI.2⟩)
        0 left_mem_uIcc
    have hid : ∀ᵐ t, t ∈ uIoc 1 R → HasDerivAt (fun t : ℝ => t⁻¹) (-(t ^ 2)⁻¹) t := by
      filter_upwards with t ht
      exact hasDerivAt_inv (hne t (uIoc_subset_uIcc ht))
    have hparts :=
      hInv.absolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul_of_ae_hasDerivAt
        hPin hid hpd
    have hpdiv : IntervalIntegrable (fun t => p t / t) volume 1 R :=
      (hpi 1 R).mul_continuousOn (by fun_prop : ContinuousOn (fun t : ℝ => t⁻¹) (uIcc 1 R))
    have hPdiv : IntervalIntegrable (fun t => P t / t ^ 2) volume 1 R :=
      hPc.continuousOn.div (continuous_id.pow 2).continuousOn (fun t ht => pow_ne_zero 2 (hne t ht))
        |>.intervalIntegrable
    have hinv2 : (∫ t in (1 : ℝ)..R, (t ^ 2)⁻¹) = 1 - R⁻¹ := by
      have hder (t : ℝ) (ht : t ∈ uIcc 1 R) :
          HasDerivAt (fun t : ℝ => -t⁻¹) ((t ^ 2)⁻¹) t := by
        simpa only [neg_neg] using (hasDerivAt_inv (hne t ht)).fun_neg
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder]
      · simp only [inv_one]
        ring
      · exact ((continuousOn_id.pow 2).inv₀
          (fun t ht => pow_ne_zero 2 (hne t ht))).intervalIntegrable
    have htail : |∫ t in (1 : ℝ)..R, P t / t ^ 2| ≤ C := by
      calc
        _ ≤ ∫ t in (1 : ℝ)..R, |P t / t ^ 2| :=
          intervalIntegral.abs_integral_le_integral_abs hR
        _ ≤ ∫ t in (1 : ℝ)..R, C * (t ^ 2)⁻¹ := by
          apply intervalIntegral.integral_mono_on hR hPdiv.abs
            (((continuousOn_id.pow 2).inv₀
              (fun t ht => pow_ne_zero 2 (hne t ht))).intervalIntegrable.const_mul C)
          intro t _
          rw [abs_div, abs_sq, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (hC t) (inv_nonneg.mpr (sq_nonneg t))
        _ = C * (1 - R⁻¹) := by rw [intervalIntegral.integral_const_mul, hinv2]
        _ ≤ C := by have hRi : 0 ≤ R⁻¹ := inv_nonneg.mpr (by linarith); nlinarith
    have hPover : |P R / R| ≤ C := by
      rw [abs_div, abs_of_pos (by linarith : 0 < R)]
      apply (div_le_iff₀ (by linarith : 0 < R)).mpr
      nlinarith [hC R]
    have hidentity : (∫ t in (1 : ℝ)..R, p t / t) - m * log R =
        P R / R - P 1 + ∫ t in (1 : ℝ)..R, P t / t ^ 2 := by
      have hqi' : (∫ t in (1 : ℝ)..R, t⁻¹ * q t) =
          (∫ t in (1 : ℝ)..R, p t / t) - m * log R := by
        have heq : (fun t : ℝ => t⁻¹ * q t) =
            (fun t : ℝ => p t / t - m * t⁻¹) := by
          funext t
          dsimp only [q]
          ring_nf
        rw [heq, intervalIntegral.integral_sub hpdiv
          (hInv.continuousOn.intervalIntegrable.const_mul m),
          intervalIntegral.integral_const_mul,
          integral_inv (fun hz => hne 0 hz rfl), div_one]
      have hnint : (∫ t in (1 : ℝ)..R, -(t ^ 2)⁻¹ * P t) =
          -(∫ t in (1 : ℝ)..R, P t / t ^ 2) := by
        rw [← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr
        intro t _
        ring_nf
      rw [hqi', hnint, inv_one, one_mul, sub_neg_eq_add] at hparts
      simpa only [div_eq_mul_inv, mul_comm] using hparts
    rw [hidentity]
    calc
      _ ≤ |P R / R| + |P 1| + |∫ t in (1 : ℝ)..R, P t / t ^ 2| :=
        (abs_add_le _ _).trans (add_le_add (_root_.abs_sub _ _) le_rfl)
      _ ≤ 3 * C := by linarith [hC 1]
  exact Asymptotics.IsBigO.of_bound (3 * C) (eventually_atTop.2 ⟨1, fun R hR => by
    simpa only [Real.norm_eq_abs, abs_one, mul_one] using hbound R hR⟩)
end Real
