/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic

/-!
# Gamma-ratio bounds for natural shifts

The Gamma recurrence and the finite Pochhammer product prove the natural-shift
case of DLMF 5.6.8. This does not assume the admitted fractional-shift inequality.
The norm and real-power manipulations use the Mathlib contributors' APIs.
-/

@[expose] public section
open Complex
open DLMF.Hypergeometric
noncomputable section
namespace DLMF.Gamma

/-- Adding a nonnegative real number cannot decrease the norm in the right half-plane. -/
theorem norm_le_norm_add_ofReal {z : ℂ} (hz : 0 ≤ z.re) {t : ℝ} (ht : 0 ≤ t) :
    ‖z‖ ≤ ‖z + t‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq]
  simp only [normSq_apply, add_re, add_im, ofReal_re, ofReal_im, add_zero]
  nlinarith [mul_nonneg hz ht, sq_nonneg t]

/-- A sharp Gamma-ratio bound for every natural difference of the real shifts. -/
theorem Gamma_ratio_norm_le_nat {a : ℝ} {z : ℂ} (hz : 0 < z.re) (ha : 0 ≤ a) (n : ℕ) :
    ‖Complex.Gamma (z + a) / Complex.Gamma (z + a + n)‖ ≤ ‖z‖ ^ (-(n : ℝ)) := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero (Or.inl hz)
  have hp : ∀ k : ℕ, z + a ≠ -k := by
    intro k hk
    have he := congrArg re hk
    simp only [add_re, ofReal_re, neg_re, natCast_re] at he
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hP : ‖z‖ ^ n ≤ ‖poch (z + a) n‖ := by
    induction n with
    | zero => simp [poch_zero]
    | succ n ih =>
      rw [pow_succ, DLMF.Hypergeometric.poch_succ, norm_mul]
      have hn : ‖z‖ ≤ ‖z + a + n‖ := by
        have h := norm_le_norm_add_ofReal hz.le (add_nonneg ha (Nat.cast_nonneg n))
        simpa only [ofReal_add, ofReal_natCast, add_assoc] using h
      exact mul_le_mul ih hn (norm_nonneg _) (norm_nonneg _)
  have hg := (div_eq_iff (Gamma_ne_zero hp)).mp (Gamma_add_nat_div_Gamma_eq (n := n) (z + a) hp)
  have hratio : ‖Complex.Gamma (z + a) / Complex.Gamma (z + a + n)‖ =
      ‖poch (z + a) n‖⁻¹ := by
    rw [hg, norm_div, norm_mul]
    field_simp [norm_ne_zero_iff.mpr (Gamma_ne_zero hp)]
  rw [hratio, Real.rpow_neg (norm_nonneg z), Real.rpow_natCast]
  simpa only [one_div] using
    (one_div_le_one_div_of_le (pow_pos (norm_pos_iff.mpr hz0) n) hP)

end DLMF.Gamma
