/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Integrals.Watson
public import DLMFMathlib.Analysis.Asymptotics.ElementaryPowerSeries

/-!
# Elementary Watson expansions

The reciprocal-linear kernel gives the factorial asymptotic series, while a single
power gives the exact Gamma integral, including the half-power case.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Finset Asymptotics Complex
open scoped Topology

namespace DLMF.AsymptoticApproximations

/-- The Laplace transform of `1/(1+t)` has the factorial expansion at positive infinity. -/
theorem hasAsymptoticExpansion_laplace_inv_one_add :
    HasAsymptoticExpansion atTop
      (fun (n : ℕ) (x : ℝ) => (x : ℂ) ^ (-((n : ℂ) + 1)))
      (fun n => (-1 : ℂ) ^ n * (n.factorial : ℂ))
      (fun x : ℝ => ∫ t : ℝ in Ioi 0, exp (-((x : ℂ) * t)) * (1 + (t : ℂ))⁻¹) := by
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-1 * t) • (1 + (t : ℂ))⁻¹)
      (Ioi 0) := by
    refine (integrableOn_exp_neg_Ioi 0).mono'
      ((by fun_prop : Measurable (fun t : ℝ => Real.exp (-1 * t) •
        (1 + (t : ℂ))⁻¹)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hn : ‖(1 + (t : ℂ))⁻¹‖ ≤ 1 := by
      rw [norm_inv, ← ofReal_one, ← ofReal_add, norm_real,
        Real.norm_of_nonneg (by linarith [show 0 < t from ht] : 0 ≤ 1 + t)]
      exact inv_le_one_of_one_le₀ (by linarith [show 0 < t from ht])
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, neg_one_mul]
    exact mul_le_of_le_one_right (Real.exp_pos _).le hn
  have hF (N : ℕ) : (fun t : ℝ => (1 + (t : ℂ))⁻¹ -
      ∑ n ∈ range N, (t : ℂ) ^ ((n : ℂ) + 1 - 1) • (-1 : ℂ) ^ n)
        =O[𝓝[>] 0] fun t => t ^ ((N : ℝ) + (1 : ℂ).re - 1) := by
    have h := Asymptotics.hasAsymptoticExpansion_inv_one_add_atZero N
    rw [← isBigO_norm_right] at h ⊢
    simpa only [add_sub_cancel_right, one_re, cpow_natCast,
      add_sub_cancel_right, Real.rpow_natCast, norm_pow, norm_real] using h
  have h := hasAsymptoticExpansion_integral_exp_smul_cpow (μ := (1 : ℂ))
    (by norm_num) hint hF
  simpa only [Gamma_nat_eq_factorial, smul_eq_mul, Complex.real_smul,
    ofReal_exp, ofReal_mul, ofReal_neg, mul_neg, neg_mul, mul_comm] using h

/-- The complex Gamma integral at order one and Laplace parameter `1+i`. -/
theorem integral_exp_neg_one_add_I :
    (∫ t : ℝ in Ioi 0, exp (-((1 + I) * t))) = (1 + I)⁻¹ := by
  simpa only [sub_self, cpow_zero, one_mul, Gamma_one, cpow_neg_one] using
    integral_cpow_mul_cexp_neg_mul_Ioi
    (s := 1) (z := 1 + I) (by norm_num) (by norm_num)

/-- The half-power kernel has the exact transform `√π z^(-1/2)` on the right half-plane. -/
theorem integral_exp_neg_mul_cpow_neg_half {z : ℂ} (hz : 0 < z.re) :
    (∫ t : ℝ in Ioi 0, exp (-(z * t)) * (t : ℂ) ^ (-(1 / 2 : ℂ))) =
      (Real.sqrt Real.pi : ℂ) * z ^ (-(1 / 2 : ℂ)) := by
  have h := integral_cpow_mul_cexp_neg_mul_Ioi (s := (1 / 2 : ℂ)) (by norm_num) hz
  have hhalf : Gamma (1 / 2) = (Real.sqrt Real.pi : ℂ) := by
    rw [Gamma_one_half_eq, Real.sqrt_eq_rpow, ofReal_cpow Real.pi_nonneg]
    norm_num
  simpa only [hhalf, show (1 / 2 : ℂ) - 1 = -(1 / 2 : ℂ) by ring,
    mul_comm] using h

end DLMF.AsymptoticApproximations
