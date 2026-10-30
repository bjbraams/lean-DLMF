/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Framework

/-!
# Lattice coefficients and convergence radii for theta power series

The coefficients `thetaDelta`, `thetaAlpha`, `thetaBeta` and `thetaGamma` are the iterated
lattice sums of DLMF 20.6.6–20.6.9, with the inner sum over the real lattice index.
`thetaLatticeMinNorm` excludes the origin from the unshifted lattice; the shifted-lattice
radii for `θ₂`, `θ₃` and `θ₄` use `thetaShiftedLatticeMinNorm`.
The lemmas `thetaShiftedLatticeMinNorm_half_pos` and
`thetaShiftedLatticeMinNorm_half_zero_pos` prove that these radii are positive in the
upper half-plane; `thetaShiftedLatticeMinNorm_le` bounds them by any shifted lattice point.
-/

@[expose] public noncomputable section
open Complex
open scoped Real
namespace DLMF.Theta

/-- DLMF 20.6.6: `δ_k(τ) = ∑_n ∑'_m (m + nτ)^{-k}` (`(m,n) ≠ (0,0)`; DLMF writes `δ_{2j}`,
`k = 2j`).
Iterated sum, inner over `m`. -/
@[dlmf 20.6.E6]
def thetaDelta (k : ℕ) (τ : ℂ) : ℂ :=
  ∑' n : ℤ, ∑' m : ℤ, if m = 0 ∧ n = 0 then 0 else ((m : ℂ) + n * τ) ^ (-(k : ℤ))

/-- DLMF 20.6.7: `α_k(τ) = ∑_n ∑_m (m - 1/2 + nτ)^{-k}` (`k = 2j`). -/
@[dlmf 20.6.E7]
def thetaAlpha (k : ℕ) (τ : ℂ) : ℂ :=
  ∑' n : ℤ, ∑' m : ℤ, ((m : ℂ) - 1 / 2 + n * τ) ^ (-(k : ℤ))

/-- DLMF 20.6.8: `β_k(τ) = ∑_n ∑_m (m - 1/2 + (n - 1/2)τ)^{-k}` (`k = 2j`). -/
@[dlmf 20.6.E8]
def thetaBeta (k : ℕ) (τ : ℂ) : ℂ :=
  ∑' n : ℤ, ∑' m : ℤ, ((m : ℂ) - 1 / 2 + (n - 1 / 2) * τ) ^ (-(k : ℤ))

/-- DLMF 20.6.9: `γ_k(τ) = ∑_n ∑_m (m + (n - 1/2)τ)^{-k}` (`k = 2j`). -/
@[dlmf 20.6.E9]
def thetaGamma (k : ℕ) (τ : ℂ) : ℂ :=
  ∑' n : ℤ, ∑' m : ℤ, ((m : ℂ) + (n - 1 / 2) * τ) ^ (-(k : ℤ))

/-- Infimum of the norms of the points `π(m + nτ)` with `(m,n) ≠ (0,0)`. In the upper
half-plane this is the distance to the nearest nonzero lattice point, and is the
radius for the logarithmic expansion of `θ₁(πz|τ)/z` in DLMF 20.6.2; the other theta
functions require the distances to their shifted zero lattices. -/
@[dlmf 20.6.E1]
def thetaLatticeMinNorm (τ : ℂ) : ℝ :=
  ⨅ p : {p : ℤ × ℤ // p ≠ 0}, ‖((p.1.1 : ℂ) + p.1.2 * τ) * π‖

/-- Infimum of the distances from zero to the points of the shifted lattice
`π(m - u + (n - v)τ)`. The shifts `(1/2,0)`, `(1/2,1/2)` and `(0,1/2)` give the
logarithmic power-series radii for `θ₂`, `θ₃` and `θ₄`, respectively. -/
def thetaShiftedLatticeMinNorm (u v : ℝ) (τ : ℂ) : ℝ :=
  ⨅ p : ℤ × ℤ, ‖(((p.1 : ℂ) - u) + ((p.2 : ℂ) - v) * τ) * π‖

/-- The shifted-lattice distance is nonnegative. -/
lemma thetaShiftedLatticeMinNorm_nonneg (u v : ℝ) (τ : ℂ) :
    0 ≤ thetaShiftedLatticeMinNorm u v τ := by
  exact le_ciInf fun _ => norm_nonneg _

/-- Every shifted lattice point bounds the distance from the origin above. -/
lemma thetaShiftedLatticeMinNorm_le (u v : ℝ) (τ : ℂ) (p : ℤ × ℤ) :
    thetaShiftedLatticeMinNorm u v τ ≤
      ‖(((p.1 : ℂ) - u) + ((p.2 : ℂ) - v) * τ) * π‖ := by
  exact ciInf_le ⟨0, by rintro _ ⟨q, rfl⟩; exact norm_nonneg _⟩ p

/-- A half-integer is separated from every integer by at least one half. -/
private lemma half_le_abs_intCast_sub_half (n : ℤ) : (1 / 2 : ℝ) ≤ |(n : ℝ) - 1 / 2| := by
  by_cases hn : n ≤ 0
  · have hn' : (n : ℝ) ≤ 0 := by exact_mod_cast hn
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show (1 : ℤ) ≤ n by omega)
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- A half-period shift in the imaginary lattice direction has positive distance from zero
in the upper half-plane, independently of the real shift. -/
lemma thetaShiftedLatticeMinNorm_half_pos (u : ℝ) {τ : ℂ} (hτ : 0 < τ.im) :
    0 < thetaShiftedLatticeMinNorm u (1 / 2) τ := by
  refine lt_of_lt_of_le (mul_pos Real.pi_pos (half_pos hτ)) (le_ciInf fun p => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have h : τ.im / 2 ≤ ‖((p.1 : ℂ) - u) + ((p.2 : ℂ) - (1 / 2 : ℝ)) * τ‖ := by
    calc τ.im / 2 ≤ |(p.2 : ℝ) - 1 / 2| * τ.im := by
           nlinarith [half_le_abs_intCast_sub_half p.2]
      _ = |(((p.1 : ℂ) - u) + ((p.2 : ℂ) - (1 / 2 : ℝ)) * τ).im| := by
           simp [Complex.mul_im, Complex.sub_re, abs_mul, abs_of_pos hτ]
      _ ≤ _ := abs_im_le_norm _
  nlinarith [Real.pi_pos]

/-- The real half-period shifted lattice also has positive distance from zero in the
upper half-plane. This is the convergence radius for the logarithm of `θ₂`. -/
lemma thetaShiftedLatticeMinNorm_half_zero_pos {τ : ℂ} (hτ : 0 < τ.im) :
    0 < thetaShiftedLatticeMinNorm (1 / 2) 0 τ := by
  have hδ : 0 < min (1 / 2 : ℝ) τ.im := lt_min (by norm_num) hτ
  refine lt_of_lt_of_le (mul_pos Real.pi_pos hδ) (le_ciInf fun p => ?_)
  simp only [Complex.ofReal_zero, sub_zero, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  have h : min (1 / 2 : ℝ) τ.im ≤ ‖((p.1 : ℂ) - (1 / 2 : ℝ)) + (p.2 : ℂ) * τ‖ := by
    by_cases hn : p.2 = 0
    · simp only [hn, Int.cast_zero, zero_mul, add_zero]
      have he : ((p.1 : ℂ) - (1 / 2 : ℝ)) = (((p.1 : ℝ) - 1 / 2 : ℝ) : ℂ) := by
        push_cast; rfl
      rw [he, Complex.norm_real, Real.norm_eq_abs]
      exact (min_le_left _ _).trans (half_le_abs_intCast_sub_half p.1)
    · have hn' : (1 : ℝ) ≤ |(p.2 : ℝ)| := by exact_mod_cast (Int.one_le_abs hn)
      calc min (1 / 2 : ℝ) τ.im ≤ τ.im := min_le_right _ _
        _ ≤ |(p.2 : ℝ)| * τ.im := by nlinarith
        _ = |(((p.1 : ℂ) - (1 / 2 : ℝ)) + (p.2 : ℂ) * τ).im| := by
              simp [Complex.mul_im, abs_mul, abs_of_pos hτ]
        _ ≤ _ := abs_im_le_norm _
  nlinarith [Real.pi_pos]
end DLMF.Theta
