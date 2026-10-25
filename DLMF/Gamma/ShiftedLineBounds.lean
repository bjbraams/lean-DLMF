/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.VerticalBounds
public import DLMFMathlib.Analysis.Complex.BarnesResidue

/-!
# Bounds for `Γ` on vertical lines, uniform under shifts of the line

Contour shifts in Mellin–Barnes integrals move a vertical line `Re s = c` to `Re s = c ± N`
and need bounds for `Γ` that are uniform in `N`. Writing `s = x + iy`:

* `shiftB_norm_Gamma_le`: `|Γ(x+iy)| ≤ Γ(x)` for `x > 0`;
* `shiftB_norm_recip_Gamma_le`: `|1/Γ(x+iy)| ≤ e^{π|y|/2} / Γ(x)` for `x ≥ 1/2`, uniformly in
  `x` (from `|Γ(x)/Γ(x+iy)|² = ∏ (1 + y²/(x+k)²) ≤ cosh πy`, DLMF 5.8.3);
* `shiftB_norm_Gamma_le_of_le_half`: `|Γ(x+iy)| ≤ 2π e^{-π|y|/2} / (|sin πx| Γ(1-x))` for
  `x ≤ 1/2`, uniformly in `x` (reflection formula);
* `shiftB_norm_Gamma_sub_nat_le`: hence on the shifted lines `x = x₀ - N`,
  `|Γ(x₀ - N + iy)| ≤ 2π e^{-π|y|/2} / (|sin πx₀| Γ(1 - x₀ + N))`, uniformly in `N`;
* `shiftB_norm_recip_Gamma_add_nat_le`: on `x = x₀ + N` with `x₀ ≥ 1/2`,
  `|1/Γ(x₀ + N + iy)| ≤ e^{π|y|/2} / Γ(x₀ + N)`.

The factorial growth of `Γ(1 - x₀ + N)` and `Γ(x₀ + N)` makes the shifted-line integrals of
Mellin–Barnes integrands tend to `0`.
-/

@[expose] public section

open Complex Filter Set
open scoped Topology Real

noncomputable section

namespace DLMF.Gamma

/-- `|Γ(x+iy)| ≤ Γ(x)` for `x > 0`. -/
theorem shiftB_norm_Gamma_le {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖Complex.Gamma (x + y * I)‖ ≤ Real.Gamma x := by
  have h := norm_Gamma_sq_eq hx y
  rw [mul_comm I] at h
  have hP := one_le_gammaVertProd x y
  have hG := Real.Gamma_pos_of_pos hx
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) hG.le two_ne_zero).mp ?_
  rw [h]
  exact div_le_self (by positivity) hP

/-- `|1/Γ(x+iy)| ≤ e^{π|y|/2} / Γ(x)` for `x ≥ 1/2`, uniformly in `x`. -/
theorem shiftB_norm_recip_Gamma_le {x : ℝ} (hx : 1 / 2 ≤ x) (y : ℝ) :
    ‖(Complex.Gamma (x + y * I))⁻¹‖ ≤ Real.exp (π * |y| / 2) / Real.Gamma x := by
  have h := norm_recip_Gamma_sq_le hx y
  rw [mul_comm I] at h
  have hG := Real.Gamma_pos_of_pos (by linarith : (0 : ℝ) < x)
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp (h.trans ?_)
  rw [div_pow, ← Real.exp_nat_mul]
  ring_nf
  rfl

/-- `|Γ(x+iy)| ≤ 2π e^{-π|y|/2} / (|sin πx| Γ(1-x))` for `x ≤ 1/2` with `sin πx ≠ 0`,
uniformly in `x`. -/
theorem shiftB_norm_Gamma_le_of_le_half {x : ℝ} (hx : x ≤ 1 / 2) (hs : Real.sin (π * x) ≠ 0)
    (y : ℝ) :
    ‖Complex.Gamma (x + y * I)‖ ≤
      2 * π * Real.exp (-(π * |y|) / 2) / (|Real.sin (π * x)| * Real.Gamma (1 - x)) := by
  set s : ℂ := x + y * I with hsdef
  have h1 := barnesRes_norm_Gamma_mul_sin_le s
  have h2 := barnesRes_sin_lower_line x y
  have h1s : (1 : ℂ) - s = ((1 - x : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I := by
    rw [hsdef]; push_cast; ring
  have h3 := shiftB_norm_recip_Gamma_le (x := 1 - x) (by linarith) (-y)
  rw [← h1s, abs_neg] at h3
  have hG := Real.Gamma_pos_of_pos (by linarith : (0 : ℝ) < 1 - x)
  have hsa : 0 < |Real.sin (π * x)| := abs_pos.mpr hs
  have he : Real.exp (π * |y|) = Real.exp (π * |y| / 2) * Real.exp (π * |y| / 2) := by
    rw [← Real.exp_add]; ring_nf
  have he2 : Real.exp (-(π * |y|) / 2) * Real.exp (π * |y| / 2) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hE := Real.exp_pos (π * |y| / 2)
  -- ‖Γ s‖ * (|sin πx|/2 e^{π|y|}) ≤ π e^{π|y|/2} / Γ(1-x)
  have key : ‖Complex.Gamma s‖ * (|Real.sin (π * x)| / 2 * Real.exp (π * |y|)) ≤
      π * (Real.exp (π * |y| / 2) / Real.Gamma (1 - x)) :=
    calc _ ≤ ‖Complex.Gamma s‖ * ‖Complex.sin (π * s)‖ :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ ≤ π * ‖(Complex.Gamma (1 - s))⁻¹‖ := h1
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 Real.pi_pos.le
  rw [le_div_iff₀ (by positivity)]
  rw [he] at key
  have : ‖Complex.Gamma s‖ * (|Real.sin (π * x)| * Real.Gamma (1 - x)) * Real.exp (π * |y| / 2)
      ≤ 2 * π := by
    have := mul_le_mul_of_nonneg_right key (by positivity : 0 ≤ 2 * Real.Gamma (1 - x) /
      Real.exp (π * |y| / 2))
    field_simp at this
    nlinarith [this]
  calc ‖Complex.Gamma s‖ * (|Real.sin (π * x)| * Real.Gamma (1 - x))
      = ‖Complex.Gamma s‖ * (|Real.sin (π * x)| * Real.Gamma (1 - x)) *
          Real.exp (π * |y| / 2) * Real.exp (-(π * |y|) / 2) := by
        rw [mul_assoc _ (Real.exp _), mul_comm (Real.exp (π * |y| / 2)), he2, mul_one]
    _ ≤ 2 * π * Real.exp (-(π * |y|) / 2) :=
        mul_le_mul_of_nonneg_right this (Real.exp_pos _).le

/-- **Uniform bound on left-shifted lines**: for `x₀ ≤ 1/2` with `sin πx₀ ≠ 0` and every
`N : ℕ`, `|Γ(x₀ - N + iy)| ≤ 2π e^{-π|y|/2} / (|sin πx₀| Γ(1 - x₀ + N))`. -/
theorem shiftB_norm_Gamma_sub_nat_le {x₀ : ℝ} (hx : x₀ ≤ 1 / 2) (hs : Real.sin (π * x₀) ≠ 0)
    (N : ℕ) (y : ℝ) :
    ‖Complex.Gamma (((x₀ - N : ℝ) : ℂ) + y * I)‖ ≤
      2 * π * Real.exp (-(π * |y|) / 2) / (|Real.sin (π * x₀)| * Real.Gamma (1 - x₀ + N)) := by
  have hsN : |Real.sin (π * (x₀ - N))| = |Real.sin (π * x₀)| := by
    rw [mul_sub, mul_comm π (N : ℝ), Real.sin_sub_nat_mul_pi]
    rcases neg_one_pow_eq_or ℝ N with h | h <;> simp [h]
  have hsN0 : Real.sin (π * (x₀ - N)) ≠ 0 := by
    intro h; apply hs; rw [← abs_eq_zero, ← hsN, h, abs_zero]
  have h := shiftB_norm_Gamma_le_of_le_half (x := x₀ - N)
    (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]) hsN0 y
  rw [hsN, show 1 - (x₀ - N) = 1 - x₀ + N by ring] at h
  exact h

/-- **Uniform bound on right-shifted lines**: for `x₀ ≥ 1/2` and every `N : ℕ`,
`|1/Γ(x₀ + N + iy)| ≤ e^{π|y|/2} / Γ(x₀ + N)`. -/
theorem shiftB_norm_recip_Gamma_add_nat_le {x₀ : ℝ} (hx : 1 / 2 ≤ x₀) (N : ℕ) (y : ℝ) :
    ‖(Complex.Gamma (((x₀ + N : ℝ) : ℂ) + y * I))⁻¹‖ ≤
      Real.exp (π * |y| / 2) / Real.Gamma (x₀ + N) :=
  shiftB_norm_recip_Gamma_le (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]) y

/-- **Growth of `Γ`**: `Γ(t) ≥ A^{t-1} e^{-(A+1)}` for `t ≥ 1` and every `A > 0` (the Euler
integral over `[A, A+1]`). With `A` large this beats every geometric sequence, so that
`r^x / Γ(x + a) → 0` exponentially fast. -/
theorem shiftB_Gamma_ge {t A : ℝ} (ht : 1 ≤ t) (hA : 0 < A) :
    A ^ (t - 1) * Real.exp (-(A + 1)) ≤ Real.Gamma t := by
  have ht0 : 0 < t := by linarith
  rw [Real.Gamma_eq_integral ht0]
  have hint := Real.GammaIntegral_convergent ht0
  have hsub : Icc A (A + 1) ⊆ Ioi 0 := fun x hx => lt_of_lt_of_le hA hx.1
  calc A ^ (t - 1) * Real.exp (-(A + 1))
      = ∫ _ in Icc A (A + 1), A ^ (t - 1) * Real.exp (-(A + 1)) := by
        rw [MeasureTheory.setIntegral_const, Real.volume_real_Icc_of_le (by linarith)]
        simp
    _ ≤ ∫ x in Icc A (A + 1), Real.exp (-x) * x ^ (t - 1) := by
        refine MeasureTheory.setIntegral_mono_on (MeasureTheory.integrableOn_const
          (by simp [Real.volume_Icc])) (hint.mono_set hsub) measurableSet_Icc fun x hx => ?_
        rw [mul_comm (Real.exp (-x))]
        refine mul_le_mul (Real.rpow_le_rpow hA.le hx.1 (by linarith))
          (Real.exp_le_exp.mpr (by linarith [hx.2])) (Real.exp_pos _).le
          (Real.rpow_nonneg (by linarith [hx.1]) _)
    _ ≤ ∫ x in Ioi 0, Real.exp (-x) * x ^ (t - 1) := by
        refine MeasureTheory.setIntegral_mono_set hint ?_ (Eventually.of_forall hsub)
        refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
          (Eventually.of_forall fun x hx => ?_)
        exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt hx) _)

end DLMF.Gamma
