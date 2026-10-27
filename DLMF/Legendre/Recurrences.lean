/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Basic
public import DLMF.Hypergeometric.Elementary

/-!
# Recurrences and special values of `P_ν` (Temme §8.4, Exercise 8.3; DLMF §§14.5, 14.10)

The three-term recurrence and the derivative relation for `P_ν` are linear combinations of
Gauss's contiguous relations for `𝐅(-ν, ν+1; 1; (1-z)/2)` on the cut plane. The value `P_ν(0)`
follows from Gauss's second summation theorem, and the higher derivatives of `P_ν` from 15.5.2.
-/

@[expose] public section

open Complex Filter Set DLMF.Hypergeometric
open scoped Topology Real

noncomputable section

namespace DLMF.Legendre

/-- The three-term recurrence `(ν+1) P_{ν+1} - (2ν+1) z P_ν + ν P_{ν-1} = 0`
(DLMF 14.10.3 with `μ = 0`). -/
@[dlmf 14.10.E3]
theorem legendreP_recurrence (ν : ℂ) {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    (ν + 1) * legendreP (ν + 1) z - (2 * ν + 1) * z * legendreP ν z +
      ν * legendreP (ν - 1) z = 0 := by
  have hw := mem_cutPlane_of_one_add hz
  set w := (1 - z) / 2 with hwdef
  have E1 := regularizedGaussHG_contiguous_ab (-ν - 1) (ν + 1) 1 hw
  have E2 := regularizedGaussHG_contiguous_ab (-ν) ν 1 hw
  have E3 := regularizedGaussHG_contiguous_a (-ν) (ν + 1) 1 hw
  have E4 := regularizedGaussHG_contiguous_a_b_pred (-ν) (ν + 1) 1 hw
  rw [show -ν - 1 + 1 = -ν by ring, show ν + 1 + 1 = ν + 2 by ring] at E1
  rw [show ν + 1 - 1 = ν by ring] at E4
  simp only [legendreP]
  rw [show -(ν + 1) = -ν - 1 by ring, show ν + 1 + 1 = ν + 2 by ring,
    show -(ν - 1) = -ν + 1 by ring, show ν - 1 + 1 = ν by ring, ← hwdef]
  rw [show z = 1 - 2 * w by rw [hwdef]; ring]
  linear_combination -E1 - E2 + 2 * E3 + 2 * E4

/-- `(1 - z²) P_ν'(z) = ν (P_{ν-1}(z) - z P_ν(z))` (Temme, Exercise 8.3; DLMF 14.10.5 with
`μ = 0`). -/
theorem legendreP_deriv_recurrence (ν : ℂ) {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    (1 - z ^ 2) * deriv (legendreP ν) z =
      ν * (legendreP (ν - 1) z - z * legendreP ν z) := by
  have hw := mem_cutPlane_of_one_add hz
  rw [deriv_legendreP ν hz]
  set w := (1 - z) / 2 with hwdef
  have R1 := regularizedGaussHG_contiguous_c_succ_deriv (-ν) (ν + 1) 1 hw
  have R2 := regularizedGaussHG_contiguous_a_c_succ (-ν) (ν + 1) 1 hw
  have E2 := regularizedGaussHG_contiguous_ab (-ν) ν 1 hw
  have E4 := regularizedGaussHG_contiguous_a_b_pred (-ν) (ν + 1) 1 hw
  rw [show ν + 1 - 1 = ν by ring] at E4
  rw [show (1 : ℂ) + 1 = 2 by norm_num] at R1 R2
  simp only [legendreP]
  rw [show -(ν - 1) = -ν + 1 by ring, show ν - 1 + 1 = ν by ring, ← hwdef]
  rw [show z = 1 - 2 * w by rw [hwdef]; ring]
  linear_combination (-2 * w) * R1 - 2 * R2 + E2 - 2 * E4

/-- `P_ν⁽ᵐ⁾(z) = (-1/2)ᵐ (-ν)ₘ (ν+1)ₘ 𝐅(m-ν, ν+1+m; 1+m; (1-z)/2)`. -/
theorem iteratedDeriv_legendreP (ν : ℂ) (m : ℕ) {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    iteratedDeriv m (legendreP ν) z = (-1 / 2) ^ m * poch (-ν) m * poch (ν + 1) m *
      regularizedGaussHG (-ν + m) (ν + 1 + m) (1 + m) ((1 - z) / 2) := by
  induction m generalizing z with
  | zero => simp [legendreP, poch_zero]
  | succ m ih =>
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv m (legendreP ν) =ᶠ[𝓝 z] fun w => (-1 / 2) ^ m * poch (-ν) m *
        poch (ν + 1) m * regularizedGaussHG (-ν + m) (ν + 1 + m) (1 + m) ((1 - w) / 2) := by
      filter_upwards [isOpen_one_add_mem_slitPlane.mem_nhds hz] with w hw
      exact ih hw
    rw [hev.deriv_eq, ((hasDerivAt_regularizedGaussHG_half _ _ _ hz).const_mul _).deriv, poch_succ,
      poch_succ]
    push_cast
    rw [show -ν + m + 1 = -ν + (m + 1) by ring, show ν + 1 + m + 1 = ν + 1 + (m + 1) by ring,
      show (1 : ℂ) + m + 1 = 1 + (m + 1) by ring]
    ring

/-- `P_ν(0) = √π / (Γ(ν/2 + 1) Γ((1-ν)/2))` (DLMF 14.5.1 with `μ = 0`, Temme (8.17)), by Gauss's
second summation theorem. -/
@[dlmf 14.5.E1]
theorem legendreP_zero_arg (ν : ℂ) :
    legendreP ν 0 = Real.sqrt π / (Gamma (ν / 2 + 1) * Gamma ((1 - ν) / 2)) := by
  have h1 : ∀ k : ℕ, (1 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hg := gauss_second_summation (a := -ν) (b := ν + 1)
    (by rw [show (-ν + (ν + 1) + 1) / 2 = 1 by ring]; exact h1)
  rw [show (-ν + (ν + 1) + 1) / 2 = 1 by ring, Gamma_one] at hg
  rw [legendreP, sub_zero, regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ (by norm_num),
    regularizedGaussHGFun_eq_div_Gamma h1, Gamma_one, div_one, hg,
    show (-ν + 1) / 2 = (1 - ν) / 2 by ring, show (ν + 1 + 1) / 2 = ν / 2 + 1 by ring]
  ring

end DLMF.Legendre

end
