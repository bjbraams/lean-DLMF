/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Basic.Properties
public import DLMF.Legendre.FirstKindProperties
public import DLMF.Hypergeometric.Elementary

/-!
# Legendre functions of the second kind (Temme §§8.2, 8.5; DLMF §14.3)

`Q_ν(z) = √π Γ(ν+1) (2z)^{-ν-1} 𝐅((ν+2)/2, (ν+1)/2; ν+3/2; 1/z²)` is analytic on
`ℂ ∖ (-∞, 1]`, where `1/z²` lies in the cut plane of `𝐅`. It satisfies Legendre's equation for
every complex `ν`, and `Q₀(z) = ½ log((z+1)/(z-1))`; the latter is proved near `z = 2` from
DLMF 15.4.2 and extended by the identity principle. The definition `legendreQ` (DLMF 14.3.7
with `μ = 0`) is in `DLMF.Legendre.Basic.Functions`.

Legendre's equation `legendreQ_ode`, the analyticity `analyticAt_legendreQ` and the topology of
the domain `ℂ ∖ (-∞, 1]` are in `DLMF.Legendre.Basic.Properties`.

## Main results

* `legendreQ_zero`: `Q₀(z) = ½ log((z+1)/(z-1))` (Temme (8.24)).
-/

@[expose] public section

open Complex Filter Set DLMF.Hypergeometric
open scoped Topology Real

noncomputable section

namespace DLMF.Legendre

/-- `Q₀(z) = ½ log((z+1)/(z-1))` (Temme (8.24)). -/
theorem legendreQ_zero {z : ℂ} (hz : z - 1 ∈ slitPlane) :
    legendreQ 0 z = 1 / 2 * log ((z + 1) / (z - 1)) := by
  have hQ : AnalyticOnNhd ℂ (legendreQ 0) {z | z - 1 ∈ slitPlane} :=
    fun w hw => analyticAt_legendreQ 0 hw
  have hL : AnalyticOnNhd ℂ (fun z : ℂ => 1 / 2 * log ((z + 1) / (z - 1)))
      {z | z - 1 ∈ slitPlane} := by
    intro w hw
    have hw1 : w - 1 ≠ 0 := slitPlane_ne_zero hw
    exact analyticAt_const.mul ((analyticAt_clog (div_mem_slitPlane hw)).comp_of_eq
      (by fun_prop (disch := exact hw1)) rfl)
  have h2 : (2 : ℂ) ∈ {z : ℂ | z - 1 ∈ slitPlane} := by
    show (2 : ℂ) - 1 ∈ slitPlane; norm_num
  refine hQ.eqOn_of_preconnected_of_eventuallyEq hL isPreconnected_sub_one_mem_slitPlane h2 ?_ hz
  have hball : Metric.ball (2 : ℂ) (1 / 2) ∈ 𝓝 (2 : ℂ) := Metric.ball_mem_nhds _ (by norm_num)
  filter_upwards [hball] with w hw
  have hw' : w - 1 ∈ slitPlane := by
    rw [Metric.mem_ball, dist_eq_norm] at hw
    left
    have := abs_re_le_norm (w - 2)
    simp at this ⊢
    rw [abs_le] at this
    linarith [this.1]
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have hw1 : 3 / 2 < ‖w‖ := by
    have := norm_sub_norm_le (2 : ℂ) w
    rw [norm_sub_rev] at hw; norm_num at this; linarith
  have hw0 : w ≠ 0 := by rintro rfl; norm_num at hw1
  have hu : ‖w⁻¹‖ < 1 := by
    rw [norm_inv]; exact inv_lt_one_of_one_lt₀ (by linarith)
  have hu2 : ‖w⁻¹ ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg w⁻¹]
  have hc : ∀ k : ℕ, (3 / 2 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hΓ : Gamma (3 / 2) = (Real.sqrt π : ℂ) / 2 := by
    rw [show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num, Gamma_add_one _ (by norm_num),
      Gamma_one_half_eq, show ((1 / 2 : ℂ)) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow Real.pi_pos.le, ← Real.sqrt_eq_rpow]
    push_cast; ring
  have hsq : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hlog := log_ratio hu
  have hratio : (1 + w⁻¹) / (1 - w⁻¹) = (w + 1) / (w - 1) := by
    have hw1 : w - 1 ≠ 0 := slitPlane_ne_zero hw'
    field_simp
  have hQ0 : legendreQ 0 w = (Real.sqrt π : ℂ) * 2⁻¹ *
      (w⁻¹ * regularizedGaussHypergeometric (1 / 2) 1 (3 / 2) (w⁻¹ ^ 2)) := by
    rw [legendreQ, regularizedGaussHypergeometric_symm _ _ _ (by
      rw [show 1 / w ^ 2 = w⁻¹ ^ 2 by rw [inv_pow, one_div]]
      exact mem_cutPlane_of_norm_lt_one hu2)]
    norm_num [cpow_neg_one]
  rw [hQ0, regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricFun _ _ _ hu2,
      regularizedGaussHypergeometricFun_eq_div_Gamma hc, hΓ,
    ← hratio, ← hlog]
  field_simp

end DLMF.Legendre

end
