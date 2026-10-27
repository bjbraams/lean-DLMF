/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.Polygamma

/-!
# Series of rational functions summed by the digamma function (Duverney §2.2)

If `∑ₖ Aₖ = 0`, the series `∑ₙ ∑ₖ Aₖ/(n - aₖ)` converges and equals `-∑ₖ Aₖ ψ(-aₖ)`
(Duverney (2.34)). This follows from the complex digamma series 5.7.6. Example 2.8 gives
`∑ 1/(2n²+3n+1) = 2 ln 2`.

The alternating series `∑ (-1)ⁿ/(z+n)` converges only conditionally, so it is stated through
partial sums: they tend to `½(ψ((z+1)/2) - ψ(z/2))` (Duverney (2.36)). The rational version
(Duverney (2.37)) follows by linearity.
-/

@[expose] public section

open Complex Filter
open scoped Nat Real Topology

noncomputable section

namespace DLMF.Gamma

/-- The digamma series as a `HasSum`: `∑ (1/(n+1) - 1/(z+n)) = ψ(z) + γ`. -/
theorem hasSum_cDigammaTerm {z : ℂ} (hz : z ∈ notNegNat) :
    HasSum (fun n => cDigammaTerm n z) (Complex.digamma z + Real.eulerMascheroniConstant) := by
  have h := (summable_cDigammaTerm hz).hasSum
  rw [digamma_eq_cDigammaSeries hz, cDigammaSeries]
  convert h using 1
  ring

/-- **Sums of rational functions by the digamma function** (Duverney (2.34)): if
`∑ₖ Aₖ = 0` and no `aₖ` is a nonnegative integer, then
`∑ₙ ∑ₖ Aₖ/(n - aₖ) = -∑ₖ Aₖ ψ(-aₖ)`. -/
theorem hasSum_sum_div_sub {ι : Type*} (s : Finset ι) (A a : ι → ℂ)
    (hA : ∑ k ∈ s, A k = 0) (ha : ∀ k ∈ s, ∀ m : ℕ, a k ≠ m) :
    HasSum (fun n : ℕ => ∑ k ∈ s, A k / (n - a k))
      (-∑ k ∈ s, A k * Complex.digamma (-a k)) := by
  have hmem (k : ι) (hk : k ∈ s) : -a k ∈ notNegNat := fun m h => ha k hk m (by
    rw [← neg_neg (a k), h, neg_neg])
  have h := hasSum_sum (s := s) fun k hk => (hasSum_cDigammaTerm (hmem k hk)).mul_left (A k)
  have hval : ∑ k ∈ s, A k * (Complex.digamma (-a k) + Real.eulerMascheroniConstant) =
      ∑ k ∈ s, A k * Complex.digamma (-a k) := by
    simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hA, zero_mul, add_zero]
  rw [hval] at h
  refine (h.neg).congr_fun fun n => ?_
  simp only [cDigammaTerm, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hA, zero_mul,
    zero_sub, neg_neg]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_one_div, neg_add_eq_sub]


/-- Duverney, Example 2.8: `∑ 1/(2n²+3n+1) = 2 ln 2`. -/
theorem hasSum_one_div_two_mul_sq_add : HasSum (fun n : ℕ => 1 / (2 * (n : ℝ) ^ 2 + 3 * n + 1))
    (2 * Real.log 2) := by
  have h := hasSum_sum_div_sub (Finset.univ : Finset (Fin 2)) ![1, -1] ![-1 / 2, -1]
    (by simp) (fun k _ m hm => by
      fin_cases k
      · have := congrArg re hm; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
      · have := congrArg re hm; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    neg_neg, one_mul, neg_one_mul] at h
  rw [show -(-1 / 2 : ℂ) = 1 / 2 by ring, Complex.digamma_one_half, Complex.digamma_one] at h
  have hfun : (fun n : ℕ => (1 : ℂ) / (n - -1 / 2) + -1 / (n - -1)) =
      fun n : ℕ => ((1 / (2 * (n : ℝ) ^ 2 + 3 * n + 1) : ℝ) : ℂ) := by
    funext n
    have h1 : (2 * (n : ℂ) + 1) ≠ 0 := by exact_mod_cast (by positivity : (2 * (n : ℝ) + 1) ≠ 0)
    have h2 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast (by positivity : ((n : ℝ) + 1) ≠ 0)
    have h3 : (2 * (n : ℂ) ^ 2 + 3 * n + 1) ≠ 0 := by
      rw [show (2 * (n : ℂ) ^ 2 + 3 * n + 1) = (2 * n + 1) * (n + 1) by ring]
      exact mul_ne_zero h1 h2
    push_cast
    rw [show (n : ℂ) - -1 / 2 = (2 * n + 1) / 2 by ring, eq_div_iff h3]
    field_simp
    ring
  rw [hfun, show -(-2 * log 2 - (Real.eulerMascheroniConstant : ℂ) +
      - -(Real.eulerMascheroniConstant : ℂ)) = ((2 * Real.log 2 : ℝ) : ℂ) by
    push_cast; rw [ofReal_log (by norm_num)]; push_cast; ring] at h
  exact Complex.hasSum_ofReal.mp h

/-- A sequence converges if its even and odd subsequences converge to the same limit. -/
theorem tendsto_of_tendsto_even_odd {f : ℕ → ℂ} {L : ℂ}
    (h0 : Tendsto (fun m => f (2 * m)) atTop (𝓝 L))
    (h1 : Tendsto (fun m => f (2 * m + 1)) atTop (𝓝 L)) : Tendsto f atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop] at h0 h1 ⊢
  intro ε hε
  obtain ⟨N0, hN0⟩ := h0 ε hε
  obtain ⟨N1, hN1⟩ := h1 ε hε
  refine ⟨2 * (N0 + N1), fun n hn => ?_⟩
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · exact hN0 k (by omega)
  · exact hN1 k (by omega)

/-- Pairing consecutive terms of a finite sum. -/
theorem sum_range_two_mul (f : ℕ → ℂ) (M : ℕ) :
    ∑ n ∈ Finset.range (2 * M), f n = ∑ m ∈ Finset.range M, (f (2 * m) + f (2 * m + 1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    ring

/-- The alternating series `∑ₙ (-1)ⁿ/(z+n) = ½(ψ((z+1)/2) - ψ(z/2))` (Duverney (2.36)), as a limit
of partial sums, for `z` off the poles. -/
theorem tendsto_sum_neg_one_pow_div_add {z : ℂ} (hz : z ∈ notNegNat) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, (-1 : ℂ) ^ n / (z + n)) atTop
      (𝓝 ((Complex.digamma ((z + 1) / 2) - Complex.digamma (z / 2)) / 2)) := by
  have h1 : (z + 1) / 2 ∈ notNegNat := fun m h => hz (2 * m + 1) (by
    push_cast; linear_combination 2 * h)
  have h0 : z / 2 ∈ notNegNat := fun m h => hz (2 * m) (by push_cast; linear_combination 2 * h)
  have hpair := ((hasSum_cDigammaTerm h1).sub (hasSum_cDigammaTerm h0)).div_const 2
  have hpair' : HasSum (fun m : ℕ => (-1 : ℂ) ^ (2 * m) / (z + (2 * m : ℕ)) +
      (-1 : ℂ) ^ (2 * m + 1) / (z + (2 * m + 1 : ℕ)))
      ((Complex.digamma ((z + 1) / 2) - Complex.digamma (z / 2)) / 2) := by
    convert hpair using 1
    · funext m
      have ha := add_nat_ne_zero_of_not_neg_nat hz (2 * m)
      have hb := add_nat_ne_zero_of_not_neg_nat hz (2 * m + 1)
      push_cast at ha hb ⊢
      simp only [cDigammaTerm, pow_succ, pow_mul]
      rw [show (z + 1) / 2 + m = (z + (2 * m + 1)) / 2 by ring,
        show z / 2 + m = (z + 2 * m) / 2 by ring]
      field_simp
      ring
    · ring
  apply tendsto_of_tendsto_even_odd
  · refine hpair'.tendsto_sum_nat.congr fun M => ?_
    rw [sum_range_two_mul]
  · have hev := hpair'.tendsto_sum_nat
    have hlast : Tendsto (fun M : ℕ => (-1 : ℂ) ^ (2 * M) / (z + (2 * M : ℕ))) atTop (𝓝 0) := by
      have hn : Tendsto (fun M : ℕ => z + ((2 * M : ℕ) : ℂ)) atTop (Bornology.cobounded ℂ) := by
        rw [← tendsto_norm_atTop_iff_cobounded]
        refine tendsto_atTop_mono (fun M => ?_) (tendsto_atTop_add_const_right _ (-‖z‖)
          (tendsto_natCast_atTop_atTop.comp (tendsto_id.const_mul_atTop' two_pos)))
        have := norm_sub_norm_le ((2 * M : ℕ) : ℂ) (-z)
        simp only [sub_neg_eq_add, norm_neg, Complex.norm_natCast] at this
        simp only [Function.comp, id]
        rw [add_comm z]; push_cast at this ⊢; linarith
      have := (tendsto_inv₀_cobounded.comp hn)
      refine this.congr fun M => ?_
      simp [pow_mul]
    refine ((hev.add hlast).congr fun M => ?_).trans (by rw [add_zero])
    rw [Finset.sum_range_succ, sum_range_two_mul]

/-- Alternating sums of rational functions (Duverney (2.37)): for `aₖ` not nonnegative integers,
`∑ₙ (-1)ⁿ ∑ₖ Aₖ/(n - aₖ) = ½ ∑ₖ Aₖ (ψ((1-aₖ)/2) - ψ(-aₖ/2))`, as a limit of partial sums. -/
theorem tendsto_sum_neg_one_pow_sum_div_sub {ι : Type*} (s : Finset ι) (A a : ι → ℂ)
    (ha : ∀ k ∈ s, ∀ m : ℕ, a k ≠ m) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, (-1 : ℂ) ^ n * ∑ k ∈ s, A k / (n - a k)) atTop
      (𝓝 (∑ k ∈ s, A k *
        ((Complex.digamma ((1 - a k) / 2) - Complex.digamma (-a k / 2)) / 2))) := by
  have hmem (k : ι) (hk : k ∈ s) : -a k ∈ notNegNat := fun m h => ha k hk m (by
    rw [← neg_neg (a k), h, neg_neg])
  have h := tendsto_finsetSum s fun k hk =>
    (tendsto_sum_neg_one_pow_div_add (hmem k hk)).const_mul (A k)
  simp_rw [neg_add_eq_sub (a _) 1] at h
  refine h.congr fun N => ?_
  simp_rw [Finset.mul_sum, Finset.sum_comm (s := Finset.range N)]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun n _ => ?_
  rw [neg_add_eq_sub]; ring

end DLMF.Gamma

end
