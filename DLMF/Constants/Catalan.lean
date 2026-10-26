/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Constants.Dirichlet
public import DLMF.Gamma.Polygamma
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# Catalan's constant (Duverney Remark 2.9, Exercise 2.12)

Catalan's constant `G = ∑ (-1)^k/(2k+1)² = β(2)` is not in Mathlib. With `λ(2) = (3/4) ζ(2) = π²/8`
from `DLMF.Constants.Dirichlet`, splitting the odd squares by residue mod 4 gives
`∑ 1/(4k+1)² = (π²/8 + G)/2` and `∑ 1/(4k+3)² = (π²/8 - G)/2`, hence, by the trigamma series,
`ψ'(1/4) = π² + 8G` and `ψ'(3/4) = π² - 8G`.
-/

@[expose] public section

open Complex Filter
open scoped Real

noncomputable section

namespace DLMF.Constants

/-- **Catalan's constant** `G = ∑ (-1)^k/(2k+1)² = β(2)` (Duverney Remark 2.9). -/
@[dlmf 25.11.E40]
def catalanConstant : ℝ := ∑' k : ℕ, (-1 : ℝ) ^ k / (2 * k + 1) ^ 2

/-- `∑ 1/(2k+1)²` converges. -/
lemma summable_one_div_odd_sq : Summable fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 2 := by
  have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (h.comp_injective (add_left_injective 1))
  simp only [Function.comp]
  push_cast
  gcongr
  linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]

/-- The series of Catalan's constant converges absolutely. -/
lemma hasSum_catalanConstant :
    HasSum (fun k : ℕ => (-1 : ℝ) ^ k / (2 * k + 1) ^ 2) catalanConstant := by
  refine (Summable.of_norm ?_).hasSum
  refine summable_one_div_odd_sq.congr fun k => ?_
  rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_of_nonneg (by positivity)]

/-- `∑ 1/(2k+1)² = π²/8`, from `λ(2) = (3/4) ζ(2)`. -/
lemma hasSum_one_div_odd_sq_complex :
    HasSum (fun k : ℕ => 1 / (2 * (k : ℂ) + 1) ^ 2) ((π : ℂ) ^ 2 / 8) := by
  have hs : (1 : ℝ) < (2 : ℂ).re := by norm_num
  have h := (summable_odd_terms hs).hasSum
  rw [← dirichletLambda, dirichletLambda_eq hs, riemannZeta_two] at h
  have h4 : (2 : ℂ) ^ (-(2 : ℂ)) = 1 / 4 := by
    rw [cpow_neg, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, cpow_natCast]; norm_num
  rw [h4] at h
  convert h using 1
  · funext k; rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, cpow_natCast]
  · ring

/-- `∑ 1/(4k+1)² = (π²/8 + G)/2` and `∑ 1/(4k+3)² = (π²/8 - G)/2`. -/
lemma hasSum_quarter_sq :
    HasSum (fun k : ℕ => 1 / (4 * (k : ℂ) + 1) ^ 2) (((π : ℂ) ^ 2 / 8 + catalanConstant) / 2) ∧
      HasSum (fun k : ℕ => 1 / (4 * (k : ℂ) + 3) ^ 2)
        (((π : ℂ) ^ 2 / 8 - catalanConstant) / 2) := by
  set f : ℕ → ℂ := fun k => 1 / (2 * (k : ℂ) + 1) ^ 2 with hf
  have hfs := hasSum_one_div_odd_sq_complex.summable
  have hA : HasSum (fun j => f (2 * j)) (∑' j, f (2 * j)) :=
    (hfs.comp_injective (mul_right_injective₀ (two_ne_zero' ℕ))).hasSum
  have hB : HasSum (fun j => f (2 * j + 1)) (∑' j, f (2 * j + 1)) :=
    (hfs.comp_injective (fun a b h => by simpa using h :
      Function.Injective fun j : ℕ => 2 * j + 1)).hasSum
  have hsum := (HasSum.even_add_odd hA hB).unique hasSum_one_div_odd_sq_complex
  have hG := (Complex.hasSum_ofReal.mpr hasSum_catalanConstant)
  set g : ℕ → ℂ := fun k => (((-1 : ℝ) ^ k / (2 * k + 1) ^ 2 : ℝ) : ℂ) with hg
  have hgA : HasSum (fun j => g (2 * j)) (∑' j, f (2 * j)) :=
    hA.congr_fun fun j => by simp only [hf, hg, pow_mul]; push_cast; norm_num
  have hgB : HasSum (fun j => g (2 * j + 1)) (-∑' j, f (2 * j + 1)) :=
    hB.neg.congr_fun fun j => by
      simp only [hf, hg, pow_succ, pow_mul]; push_cast; norm_num
      rw [neg_div, one_div, mul_inv]
  have hdiff := (HasSum.even_add_odd hgA hgB).unique hG
  have hA' : HasSum (fun k : ℕ => 1 / (4 * (k : ℂ) + 1) ^ 2) (∑' j, f (2 * j)) :=
    hA.congr_fun fun j => by simp only [hf]; push_cast; ring_nf
  have hB' : HasSum (fun k : ℕ => 1 / (4 * (k : ℂ) + 3) ^ 2) (∑' j, f (2 * j + 1)) :=
    hB.congr_fun fun j => by simp only [hf]; push_cast; ring_nf
  constructor
  · convert hA' using 1; linear_combination -(hsum + hdiff) / 2
  · convert hB' using 1; linear_combination -(hsum - hdiff) / 2

/-- Points with positive real part are not poles of `Γ`. -/
lemma mem_notNegNat_of_re_pos {z : ℂ} (hz : 0 < z.re) : z ∈ DLMF.Gamma.notNegNat := fun m h => by
  have := congrArg re h
  simp at this
  linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]

/-- `ψ'(1/4) = π² + 8G` (Duverney Remark 2.9, Exercise 2.12). -/
theorem trigamma_one_quarter :
    DLMF.Gamma.polygamma 1 (1 / 4) = (π : ℂ) ^ 2 + 8 * catalanConstant := by
  rw [DLMF.Gamma.polygamma_eq_tsum one_pos (mem_notNegNat_of_re_pos (by norm_num))]
  have h := hasSum_quarter_sq.1.mul_left 16
  have he : (fun k : ℕ => (1 / 4 + (k : ℂ)) ^ (-1 - (1 : ℕ) : ℤ)) =
      fun k : ℕ => 16 * (1 / (4 * (k : ℂ) + 1) ^ 2) := by
    funext k
    have hk : (4 * (k : ℂ) + 1) ≠ 0 := by
      have : (0 : ℝ) < 4 * k + 1 := by positivity
      exact_mod_cast this.ne'
    rw [show (-1 - ((1 : ℕ) : ℤ)) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast,
      show (1 / 4 + (k : ℂ)) = (4 * k + 1) / 4 by ring, div_pow]
    field_simp
    norm_num
  rw [he, h.tsum_eq]
  norm_num
  ring

/-- `ψ'(3/4) = π² - 8G` (Duverney Remark 2.9, Exercise 2.12). -/
theorem trigamma_three_quarters :
    DLMF.Gamma.polygamma 1 (3 / 4) = (π : ℂ) ^ 2 - 8 * catalanConstant := by
  rw [DLMF.Gamma.polygamma_eq_tsum one_pos (mem_notNegNat_of_re_pos (by norm_num))]
  have h := hasSum_quarter_sq.2.mul_left 16
  have he : (fun k : ℕ => (3 / 4 + (k : ℂ)) ^ (-1 - (1 : ℕ) : ℤ)) =
      fun k : ℕ => 16 * (1 / (4 * (k : ℂ) + 3) ^ 2) := by
    funext k
    have hk : (4 * (k : ℂ) + 3) ≠ 0 := by
      have : (0 : ℝ) < 4 * k + 3 := by positivity
      exact_mod_cast this.ne'
    rw [show (-1 - ((1 : ℕ) : ℤ)) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast,
      show (3 / 4 + (k : ℂ)) = (4 * k + 3) / 4 by ring, div_pow]
    field_simp
    norm_num
  rw [he, h.tsum_eq]
  norm_num
  ring

end DLMF.Constants

end
