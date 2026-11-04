/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import DLMF.Struve.SeriesAndEquations
/-!
# Relative-error bound for the Struve function

The normalized power series for `struveH` is compared with an exponential series using
lower bounds for its Pochhammer factors. The comparison is strict at the quadratic
coefficient.

## Main results

* `struveCoeff_normalized`: the Struve coefficients as Pochhammer quotients.
* `struveH_relative_bound`: the relative-error bound of DLMF 11.4.14–11.4.15.

## Implementation notes

The exponential subtraction in DLMF 11.4.14–11.4.15 is corrected. The estimate applies to
any positive lower bound for the distance to reciprocal-Gamma zeros; the lower bound need
not be attained.
-/

@[expose] public noncomputable section
open Complex Filter Set Finset MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Struve
/-- A lower bound on each linear factor bounds the norm of a Pochhammer product. -/
private lemma pow_le_norm_pochhammer_of_forall {v : ℂ} {d : ℝ} (hd : 0 ≤ d)
    (hv : ∀ n : ℕ, d ≤ ‖v + n‖) (n : ℕ) : d ^ n ≤ ‖pochhammer v n‖ := by
  induction n with
  | zero => simp [pochhammer_zero]
  | succ n ih =>
    rw [pochhammer_succ, norm_mul, pow_succ]
    exact mul_le_mul ih (hv n) hd (norm_nonneg _)
/-- The rising half-integer product exceeds three halves times the factorial. -/
private lemma factorial_le_norm_pochhammer_three_halves (n : ℕ) :
    (3 / 2 : ℝ) * ((n + 1).factorial : ℝ) ≤ ‖pochhammer (3 / 2) (n + 1)‖ := by
  induction n with
  | zero => norm_num [pochhammer_succ, pochhammer_zero]
  | succ n ih =>
    rw [pochhammer_succ, norm_mul, Nat.factorial_succ, Nat.cast_mul]
    have he : ‖(3 / 2 : ℂ) + (n + 1 : ℕ)‖ = (3 / 2 : ℝ) + (n + 1 : ℕ) := by
      rw [show (3 / 2 : ℂ) + (n + 1 : ℕ) = (((3 / 2 : ℝ) + (n + 1 : ℕ) : ℝ) : ℂ) by push_cast; ring]
      exact Complex.norm_of_nonneg (by positivity)
    rw [he]
    calc (3 / 2 : ℝ) * (((n + 1 + 1 : ℕ) : ℝ) * ((n + 1).factorial : ℝ))
        ≤ (3 / 2 : ℝ) * ((n + 1).factorial : ℝ) * (3 / 2 + (n + 1 : ℕ)) := by
          push_cast
          nlinarith [Nat.cast_nonneg (α := ℝ) ((n + 1).factorial)]
      _ ≤ _ := mul_le_mul_of_nonneg_right ih (by positivity)
/-- Gamma normalization expresses the ordinary Struve coefficients as Pochhammer quotients. -/
lemma struveCoeff_normalized {ν : ℂ} (hν : ∀ n : ℕ, ν + 3 / 2 ≠ -n) (n : ℕ) :
    Gamma (3 / 2) * Gamma (ν + 3 / 2) * struveCoeff ν n =
      1 / (pochhammer (3 / 2) n * pochhammer (ν + 3 / 2) n) := by
  have hhalf : ∀ k : ℕ, (3 / 2 : ℂ) ≠ -k := fun k h => by
    have hh := congrArg Complex.re h
    simp at hh
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hg (a : ℂ) (ha : ∀ k : ℕ, a ≠ -k) : Gamma (a + n) = pochhammer a n * Gamma a := by
    have h := Gamma_add_nat_div_Gamma_eq a ha (n := n)
    change Gamma (a + n) / Gamma a = pochhammer a n at h
    exact (div_eq_iff (Gamma_ne_zero ha)).mp h
  rw [struveCoeff, show (n : ℂ) + 3 / 2 = 3 / 2 + n by ring,
    show (n : ℂ) + ν + 3 / 2 = (ν + 3 / 2) + n by ring, hg _ hhalf, hg _ hν]
  convert mul_div_mul_left (1 : ℂ) (pochhammer (3 / 2) n * pochhammer (ν + 3 / 2) n)
    (mul_ne_zero (Gamma_ne_zero hhalf) (Gamma_ne_zero hν)) using 1
  ring
/-- Each nonconstant normalized Struve-series term is bounded by an exponential term. -/
private lemma norm_struve_term_le {ν w : ℂ} (hν : ∀ n : ℕ, ν + 3 / 2 ≠ -n)
    {d : ℝ} (hd : 0 < d) (hmin : ∀ n : ℕ, d ≤ ‖ν + 3 / 2 + n‖) (n : ℕ) :
    ‖w ^ (n + 1) * (Gamma (3 / 2) * Gamma (ν + 3 / 2) * struveCoeff ν (n + 1))‖ ≤
      (2 / 3 : ℝ) * (‖w‖ / d) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  rw [struveCoeff_normalized hν, norm_mul, norm_pow, norm_div, norm_one, norm_mul]
  have hprod := mul_le_mul (factorial_le_norm_pochhammer_three_halves n)
    (pow_le_norm_pochhammer_of_forall hd.le hmin (n + 1)) (by positivity)
    (norm_nonneg (pochhammer (3 / 2) (n + 1)))
  calc ‖w‖ ^ (n + 1) * (1 / (‖pochhammer (3 / 2) (n + 1)‖ * ‖pochhammer (ν + 3 / 2) (n + 1)‖))
      ≤ ‖w‖ ^ (n + 1) * (1 / ((3 / 2 : ℝ) * ((n + 1).factorial : ℝ) * d ^ (n + 1))) := by
        gcongr
    _ = _ := by rw [div_pow]; field_simp
/-- The quadratic normalized coefficient gives a strict comparison with the exponential majorant. -/
private lemma norm_struve_term_two_lt {ν w : ℂ} (hν : ∀ n : ℕ, ν + 3 / 2 ≠ -n) (hw : w ≠ 0)
    {d : ℝ} (hd : 0 < d) (hmin : ∀ n : ℕ, d ≤ ‖ν + 3 / 2 + n‖) :
    ‖w ^ 2 * (Gamma (3 / 2) * Gamma (ν + 3 / 2) * struveCoeff ν 2)‖ <
      (2 / 3 : ℝ) * (‖w‖ / d) ^ 2 / (2 : ℕ).factorial := by
  rw [struveCoeff_normalized hν, norm_mul, norm_pow, norm_div, norm_one, norm_mul]
  have hh : ‖pochhammer (3 / 2 : ℂ) 2‖ = (15 / 4 : ℝ) := by
    norm_num [pochhammer_succ, pochhammer_zero]
  rw [hh]
  have hp := pow_le_norm_pochhammer_of_forall hd.le hmin 2
  calc ‖w‖ ^ 2 * (1 / ((15 / 4 : ℝ) * ‖pochhammer (ν + 3 / 2) 2‖))
      ≤ ‖w‖ ^ 2 * (1 / ((15 / 4 : ℝ) * d ^ 2)) := by gcongr
    _ < _ := by
      have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr hw
      norm_num [Nat.factorial]
      rw [div_pow]
      field_simp
      nlinarith [sq_pos_of_pos hw0]
/-- DLMF 11.4.14–11.4.15, with the exponential subtraction corrected: the relative error of
`H_ν(z)` is bounded by `(2/3) * (exp (‖z‖² / (4d)) - 1)`. Any positive lower bound `d` for
`‖ν + 3/2 + n‖` suffices; it need not be the attained minimum. -/
@[dlmf 11.4.E14, dlmf 11.4.E15]
theorem struveH_relative_bound {ν z : ℂ} (hz : z ≠ 0) (d : ℝ) (hd : 0 < d)
    (hmin : ∀ n : ℕ, d ≤ ‖ν + 3 / 2 + n‖) :
    ∃ θ : ℂ, struveH ν z = 2 * (z / 2) ^ (ν + 1) /
      (Real.sqrt π * Gamma (ν + 3 / 2)) * (1 + θ) ∧
      ‖θ‖ < 2 / 3 * (Real.exp (‖z‖ ^ 2 / (4 * d)) - 1) := by
  have hν : ∀ n : ℕ, ν + 3 / 2 ≠ -n := by
    intro n hn
    have h := hmin n
    rw [hn, neg_add_cancel, norm_zero] at h
    linarith
  let G := Gamma (3 / 2) * Gamma (ν + 3 / 2)
  let w := -(z / 2) ^ 2
  let θ := G * struveHCore ν z - 1
  let T := fun n : ℕ => w ^ n * (G * struveCoeff ν n)
  have hfull : HasSum T (G * struveHCore ν z) := by
    convert (hasSum_struveHCore ν z).mul_left G using 1
    funext n
    dsimp [T, w]
    rw [neg_pow, ← pow_mul]
    ring
  have hT0 : T 0 = 1 := by
    dsimp only [T, G]
    rw [struveCoeff_normalized hν]
    simp [pochhammer_zero]
  have ht : HasSum (fun n => T (n + 1)) θ := by
    simpa only [sum_range_one, hT0] using (hasSum_nat_add_iff' 1).mpr hfull
  have hm : HasSum (fun n : ℕ => (2 / 3 : ℝ) * (‖w‖ / d) ^ (n + 1) / ((n + 1).factorial : ℝ))
      ((2 / 3 : ℝ) * (Real.exp (‖w‖ / d) - 1)) := by
    have hE : HasSum (fun n : ℕ => (‖w‖ / d) ^ n / (n.factorial : ℝ))
        (Real.exp (‖w‖ / d)) := by
      simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (‖w‖ / d)
    simpa only [sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
      mul_div_assoc] using ((hasSum_nat_add_iff' 1).mpr hE).mul_left (2 / 3 : ℝ)
  have hbound (n : ℕ) : ‖T (n + 1)‖ ≤
      (2 / 3 : ℝ) * (‖w‖ / d) ^ (n + 1) / ((n + 1).factorial : ℝ) :=
    norm_struve_term_le hν hd hmin n
  have hs : Summable (fun n => ‖T (n + 1)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hm.summable
  have hstrict : ‖T (1 + 1)‖ <
      (2 / 3 : ℝ) * (‖w‖ / d) ^ (1 + 1) / ((1 + 1).factorial : ℝ) :=
    norm_struve_term_two_lt hν
        (neg_ne_zero.mpr (pow_ne_zero _ (div_ne_zero hz two_ne_zero))) hd hmin
  have herr : ‖θ‖ < (2 / 3 : ℝ) * (Real.exp (‖w‖ / d) - 1) := by
    calc ‖θ‖ = ‖∑' n, T (n + 1)‖ := by rw [ht.tsum_eq]
      _ ≤ ∑' n, ‖T (n + 1)‖ := norm_tsum_le_tsum_norm hs
      _ < _ := (hs.tsum_lt_tsum hbound hstrict hm.summable).trans_eq hm.tsum_eq
  refine ⟨θ, ?_, ?_⟩
  · have hΓ : Gamma (3 / 2 : ℂ) = (Real.sqrt π : ℂ) / 2 := by
      rw [show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num, Gamma_add_one _ (by norm_num),
        Complex.Gamma_one_half_eq_sqrt]
      ring
    have hΓv : Gamma (ν + 3 / 2) ≠ 0 := Gamma_ne_zero hν
    have hsqrt : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    dsimp [θ, G, struveH]
    rw [hΓ]
    generalize Gamma (ν + 3 / 2) = C at hΓv ⊢
    field_simp [hΓv]
    ring
  · have hw : ‖w‖ / d = ‖z‖ ^ 2 / (4 * d) := by
      simp only [w, norm_neg, norm_pow, norm_div]
      norm_num
      ring
    rwa [hw] at herr
end DLMF.Struve
