/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import DLMF.EllipticIntegrals.LegendreIdentities
import DLMF.EllipticIntegrals.SymmetricRelations
import DLMF.EllipticIntegrals.SymmetricThirdKindAsymptotics
import Mathlib.Tactic

/-!
# Logarithmic asymptotics of the complete third-kind elliptic integral

The regularized combination `p R_J(0,y,1,p) - 3 R_F(0,y,1) + 3 R_C(1,p)` has remainder
`O(y log y)`. The symmetric representation of the complete third-kind integral gives
DLMF 19.12.4. The negative-parameter companion for `R_C` and the same endpoint estimate give
the principal-value formula DLMF 19.12.5. The proof reuses the endpoint bounds in
`DLMF.EllipticIntegrals.SymmetricThirdKindAsymptotics`.

## Main results

* `completeEllipticPi_isBigO_log`: the logarithmic approximation for `α² < 1` (DLMF 19.12.4).
* `completeEllipticPi_isBigO_log'`: the extension to every real `α² ≠ 1`.
* `completeEllipticPi_isBigO_log_of_one_lt`: the principal-value form (DLMF 19.12.5).
-/

open Complex Set Filter Asymptotics
open scoped Real Topology

namespace DLMF.EllipticIntegrals
open DLMF.JacobiElliptic

/-- The logarithmic approximation to `Π` holds for every real characteristic other than one.
Stronger than DLMF, which assumes `α² < 1`; for `α² > 1` the symmetric integrals encode their
Cauchy principal values. -/
@[dlmf 19.12.E4 "stronger than DLMF: every real characteristic α² ≠ 1"]
public theorem completeEllipticPi_isBigO_log' {α2 : ℝ} (hα : α2 ≠ 1) :
    (fun k : ℝ => (1 - α2) * completeEllipticPi α2 k + α2 *
        symmetricEllipticRC 1 ((1 - α2 : ℝ) : ℂ) -
        (Real.log (4 / Real.sqrt (1 - k ^ 2)) : ℂ)) =O[𝓝[<] 1]
      fun k : ℝ => (1 - k ^ 2) * Real.log (4 / Real.sqrt (1 - k ^ 2)) := by
  have log_four_div_sqrt_eq {y : ℝ} (hy : 0 < y) :
      Real.log (4 / Real.sqrt y) = Real.log (16 / y) / 2 := by
    rw [Real.log_div (by norm_num) (Real.sqrt_pos.mpr hy).ne', Real.log_sqrt hy.le,
      Real.log_div (by norm_num) hy.ne',
      show (16 : ℝ) = 4 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
    ring
  have endpoint_log_isBigO :
      (fun y : ℝ => ((y * Real.log y : ℝ) : ℂ)) =O[𝓝[>] 0]
        fun y : ℝ => y * Real.log (4 / Real.sqrt y) := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with y hy
    have hl : Real.log y < 0 := Real.log_neg hy.1 hy.2
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hL : Real.log (4 / Real.sqrt y) = Real.log 4 - 1 / 2 * Real.log y := by
      rw [Real.log_div (by norm_num) (Real.sqrt_pos.mpr hy.1).ne', Real.log_sqrt hy.1.le]
      ring
    have hLp : 0 < Real.log (4 / Real.sqrt y) := by rw [hL]; linarith
    rw [norm_real, Real.norm_eq_abs, abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hy.1.le hl.le),
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hy.1.le hLp.le), hL]
    nlinarith [mul_nonneg hy.1.le h4]
  have tendsto_complementaryParameter_zero :
      Tendsto (fun k : ℝ => 1 - k ^ 2) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Continuous (fun k : ℝ => 1 - k ^ 2) := by fun_prop
      simpa using (hc.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with k hk
      exact show 0 < 1 - k ^ 2 from by nlinarith [hk.1, hk.2]

  have hreg := SymmetricThirdKindEndpoint.regularizedThirdKind_zero_isBigO
    (z := 1) (p := 1 - α2) (by norm_num) (sub_ne_zero.mpr hα.symm)
  have hRF := SymmetricThirdKindEndpoint.symmetricEllipticRF_zero_sub_log_isBigO
    (z := 1) (by norm_num)
  have H := (((hreg.const_mul_left ((α2 : ℂ) / 3)).add hRF).trans endpoint_log_isBigO).comp_tendsto
    tendsto_complementaryParameter_zero
  apply H.congr'
  · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with k hk
    have hy : 0 < 1 - k ^ 2 := by nlinarith [hk.1, hk.2]
    have hslit : 1 - (k : ℂ) ^ 2 ∈ slitPlane := by
      rw [← ofReal_pow, ← ofReal_one, ← ofReal_sub]
      exact ofReal_mem_slitPlane.mpr hy
    have HP := completeEllipticPi_eq_symmetricEllipticRF_add_RJ hslit hα
    dsimp only [Function.comp_def, SymmetricThirdKindEndpoint.regularizedThirdKind]
    rw [log_four_div_sqrt_eq hy]
    norm_num only [Real.sqrt_one, mul_one]
    push_cast
    push_cast at HP
    linear_combination -(1 - (α2 : ℂ)) * HP
  · exact Eventually.of_forall fun _ => rfl
/-- DLMF 19.12.4: as `k² → 1-` (real `k → 1-`), for real `α² < 1`,
`(1 - α²) Π(α², k) = (ln(4/k'))(1 + O(k'²)) - α² R_C(1, 1 - α²)`, stated as
`(1 - α²) Π(α², k) + α² R_C(1, 1 - α²) - ln(4/k') = O(k'² ln(4/k'))`. -/
@[dlmf 19.12.E4]
public theorem completeEllipticPi_isBigO_log {α2 : ℝ} (hα : α2 < 1) :
    (fun k : ℝ => (1 - α2) * completeEllipticPi α2 k + α2 *
        symmetricEllipticRC 1 ((1 - α2 : ℝ) : ℂ) -
        (Real.log (4 / Real.sqrt (1 - k ^ 2)) : ℂ)) =O[𝓝[<] 1]
      fun k : ℝ => (1 - k ^ 2) * Real.log (4 / Real.sqrt (1 - k ^ 2)) := by
  exact completeEllipticPi_isBigO_log' hα.ne


end DLMF.EllipticIntegrals

namespace DLMF.EllipticIntegrals
/-- DLMF 19.12.5: as `k² → 1-` (real `k → 1-`), for real `α² > 1` (Cauchy principal value
`Π`), `(1 - α²) Π(α², k) = (ln(4/k') - R_C(1, 1 - α⁻²))(1 + O(k'²))`, stated as
`(1 - α²) Π(α², k) - (ln(4/k') - R_C(1, 1 - α⁻²)) = O(k'² (ln(4/k') - R_C(1, 1 - α⁻²)))`. -/
@[dlmf 19.12.E5]
public theorem completeEllipticPi_isBigO_log_of_one_lt {α2 : ℝ} (hα : 1 < α2) :
    (fun k : ℝ => (1 - α2) * completeEllipticPi α2 k -
        ((Real.log (4 / Real.sqrt (1 - k ^ 2)) : ℂ) -
          symmetricEllipticRC 1 ((1 - α2⁻¹ : ℝ) : ℂ))) =O[𝓝[<] 1]
      fun k : ℝ => ((1 - k ^ 2 : ℝ) : ℂ) *
        ((Real.log (4 / Real.sqrt (1 - k ^ 2)) : ℂ) -
            symmetricEllipticRC 1 ((1 - α2⁻¹ : ℝ) : ℂ)) := by
  have tendsto_complementaryParameter_zero :
      Tendsto (fun k : ℝ => 1 - k ^ 2) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Continuous (fun k : ℝ => 1 - k ^ 2) := by fun_prop
      simpa using (hc.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with k hk
      exact show 0 < 1 - k ^ 2 from by nlinarith [hk.1, hk.2]

  let C : ℂ := symmetricEllipticRC 1 ((1 - α2⁻¹ : ℝ) : ℂ)
  let L : ℝ → ℝ := fun k => Real.log (4 / Real.sqrt (1 - k ^ 2))
  have hα0 : α2 ≠ 0 := (lt_trans zero_lt_one hα).ne'
  have hcomp : SymmetricThirdKindEndpoint.negativeParameterCompanion 1 (1 - α2) 0 =
      1 - α2⁻¹ := by
    dsimp only [SymmetricThirdKindEndpoint.negativeParameterCompanion]
    field_simp [hα0]
    ring
  have hRC := SymmetricThirdKindEndpoint.symmetricEllipticRC_negativeParameterCompanion
    (z := 1) (p := 1 - α2) (by norm_num) (by linarith)
  rw [hcomp, show (1 : ℝ) - (1 - α2) = α2 by ring] at hRC
  norm_num only [ofReal_one] at hRC
  have hRC' : (α2 : ℂ) * symmetricEllipticRC 1 ((1 - α2 : ℝ) : ℂ) = C := by
    rw [hRC]
    dsimp only [C]
    push_cast
    field_simp [ofReal_ne_zero.mpr hα0]
  have hlog := Real.tendsto_log_nhdsGT_zero.comp tendsto_complementaryParameter_zero
  have hb : ∀ᶠ k : ℝ in 𝓝[<] 1, Real.log (1 - k ^ 2) ≤ -4 * (‖C‖ + 1) :=
    hlog.eventually (eventually_le_atBot _)
  have hcompare : (fun k : ℝ => (1 - k ^ 2) * L k) =O[𝓝[<] 1]
      fun k : ℝ => ((1 - k ^ 2 : ℝ) : ℂ) * ((L k : ℂ) - C) := by
    apply IsBigO.of_bound 2
    filter_upwards [hb, Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with k hk hk0
    have hy : 0 < 1 - k ^ 2 := by nlinarith [hk0.1, hk0.2]
    have hL : L k = Real.log 4 - 1 / 2 * Real.log (1 - k ^ 2) := by
      dsimp only [L]
      rw [Real.log_div (by norm_num) (Real.sqrt_pos.mpr hy).ne', Real.log_sqrt hy.le]
      ring
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hLp : 0 < L k := by rw [hL]; linarith [norm_nonneg C]
    have hLn : 2 * ‖C‖ ≤ L k := by rw [hL]; linarith
    have hn := norm_sub_norm_le ((L k : ℝ) : ℂ) C
    rw [norm_real, Real.norm_of_nonneg hLp.le] at hn
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hy.le hLp.le), norm_mul,
      norm_real, Real.norm_of_nonneg hy.le]
    nlinarith [mul_le_mul_of_nonneg_left hn hy.le,
      mul_le_mul_of_nonneg_left hLn hy.le]
  have H := (completeEllipticPi_isBigO_log' (ne_of_gt hα)).trans hcompare
  apply H.congr'
  · exact Eventually.of_forall fun k => by dsimp only [L, C]; rw [hRC']; ring
  · exact Eventually.of_forall fun _ => rfl
end DLMF.EllipticIntegrals
