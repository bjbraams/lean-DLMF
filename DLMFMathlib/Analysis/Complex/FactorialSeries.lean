/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt

/-!
# Entire sparse factorial series

Mathlib's summable exponential series and locally uniform holomorphic convergence
supply convergence and differentiability for bounded coefficients and injective exponents.
-/

@[expose] public noncomputable section
open Complex Set
namespace Complex

/-- A sparse factorial series with bounded coefficients is absolutely summable. -/
theorem summable_factorial_div_nat {c : ℕ → ℂ} {d : ℕ → ℕ}
    (hc : ∀ n, ‖c n‖ ≤ 1) (hd : Function.Injective d) (hpos : ∀ n, 0 < d n) (z : ℂ) :
    Summable (fun n => c n*z^(d n)/((d n).factorial*(d n : ℂ))) := by
  apply Summable.of_norm_bounded ((Real.summable_pow_div_factorial ‖z‖).comp_injective hd)
  intro n
  rw [norm_div, norm_mul, norm_mul, norm_pow, norm_natCast, norm_natCast]
  have hn : (1:ℝ) ≤ d n := by exact_mod_cast hpos n
  calc
    ‖c n‖*‖z‖^(d n)/((d n).factorial*(d n : ℝ))
        ≤ 1*‖z‖^(d n)/((d n).factorial*1) := by gcongr; exact hc n
    _ = ‖z‖^(d n)/(d n).factorial := by ring

/-- The same sparse series defines an entire function. -/
theorem differentiable_tsum_factorial_div_nat {c : ℕ → ℂ} {d : ℕ → ℕ}
    (hc : ∀ n, ‖c n‖ ≤ 1) (hd : Function.Injective d) (hpos : ∀ n, 0 < d n) :
    Differentiable ℂ (fun z => ∑' n, c n*z^(d n)/((d n).factorial*(d n : ℂ))) := by
  intro z
  have hbound : ∀ w ∈ Metric.ball (0:ℂ) (‖z‖+1), ∀ n,
      ‖c n*w^(d n)/((d n).factorial*(d n : ℂ))‖ ≤ (‖z‖+1)^(d n)/(d n).factorial := by
    intro w hw n
    rw [Metric.mem_ball, dist_zero_right] at hw
    rw [norm_div, norm_mul, norm_mul, norm_pow, norm_natCast, norm_natCast]
    have hn : (1:ℝ) ≤ d n := by exact_mod_cast hpos n
    calc
      ‖c n‖*‖w‖^(d n)/((d n).factorial*(d n : ℝ))
          ≤ 1*(‖z‖+1)^(d n)/((d n).factorial*1) := by gcongr; exact hc n
      _ = (‖z‖+1)^(d n)/(d n).factorial := by ring
  exact (differentiableOn_tsum_of_summable_norm
    ((Real.summable_pow_div_factorial (‖z‖+1)).comp_injective hd)
    (fun n => (by fun_prop : Differentiable ℂ
      (fun w => c n*w^(d n)/((d n).factorial*(d n : ℂ)))).differentiableOn)
    Metric.isOpen_ball (fun n w hw => hbound w hw n)).differentiableAt
      (Metric.isOpen_ball.mem_nhds (by simp : z ∈ Metric.ball (0:ℂ) (‖z‖+1)))

end Complex
