/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.ContinuedFractionTails
public import DLMF.Mathieu.FourierSeries
public import DLMF.Mathieu.Properties.Spectra

/-!
# The continued-fraction equations of Mathieu's eigenvalues

The continued-fraction equations DLMF 28.6.16–28.6.19 for `a_{2n}(q)`, `a_{2n+1}(q)`,
`b_{2n+1}(q)`, `b_{2n+2}(q)`. The Fourier coefficients of `ce_n`, `se_n` solve the recurrences
28.4.5–28.4.8 and decay, so `tendsto_neg_mathieuContinuedFractionTail_mathieuContinuedFractionHead`
of `DLMF.Mathieu.ContinuedFractionTails` applies; for `q = 0` both sides vanish.

## Main results

* `mathieuA_even_contFrac`, `mathieuA_zero_contFrac`: DLMF 28.6.16.
* `mathieuA_odd_contFrac`: DLMF 28.6.17.
* `mathieuB_odd_contFrac`: DLMF 28.6.18.
* `mathieuB_even_contFrac`: DLMF 28.6.19.

## Implementation notes

For `n = 0` the left side of 28.6.16 reduces to `a`, and the relation needs a factor 2:
`a₀ = -2q²/(4 - a₀ - q²/(16 - a₀ - ⋯))`; it is stated separately as `mathieuA_zero_contFrac`.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Topology Real

namespace DLMF.Mathieu

/-- `‖(2k + b)²‖ → ∞`. -/
private lemma tendsto_norm_two_mul_add_sq (b : ℕ) :
    Tendsto (fun k : ℕ => ‖(2 * (k : ℂ) + b) ^ 2‖) atTop atTop := by
  refine tendsto_atTop_mono (fun k => ?_) tendsto_natCast_atTop_atTop
  rw [show (2 * (k : ℂ) + b) ^ 2 = (((2 * k + b) ^ 2 : ℕ) : ℂ) by push_cast; ring,
    Complex.norm_natCast]
  have : k ≤ (2 * k + b) ^ 2 :=
    calc k ≤ 2 * k + b := by omega
      _ ≤ (2 * k + b) ^ 2 := Nat.le_self_pow two_ne_zero _
  exact_mod_cast this

/-- **DLMF 28.6.16** (`n ≥ 1`): for `a = a_{2n}(q)`,
`a - (2n)² - q²/(a - (2n-2)² - ⋯ q²/(a - 2² - 2q²/a)) = -q²/((2n+2)² - a - q²/((2n+4)² - a - ⋯))`;
the right side is the limit of the truncations `mathieuContinuedFractionTail`. The left-side partial
denominators are assumed nonzero. -/
@[dlmf 28.6.E16]
theorem mathieuA_even_contFrac {n : ℕ} (hn : 1 ≤ n) {q : ℝ}
    (hE : ∀ k < n, mathieuContinuedFractionHead q (mathieuA (2 * n) q) (mathieuA (2 * n) q)
      (fun k => if k = 0 then 2 else 1) (fun k => (2 * k + 2) ^ 2) k ≠ 0) :
    Tendsto (fun N => -mathieuContinuedFractionTail q (mathieuA (2 * n) q)
        (fun k => (2 * n + 2 * k + 2) ^ 2) N)
      atTop (𝓝 (mathieuContinuedFractionHead q (mathieuA (2 * n) q) (mathieuA (2 * n) q)
        (fun k => if k = 0 then 2 else 1) (fun k => (2 * k + 2) ^ 2) n)) := by
  rcases eq_or_ne q 0 with rfl | hq
  · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have h0 : mathieuContinuedFractionHead ((0 : ℝ) : ℂ) (mathieuA (2 * (n' + 1)) 0)
        (mathieuA (2 * (n' + 1)) 0)
        (fun k => if k = 0 then 2 else 1) (fun k => (2 * k + 2) ^ 2) (n' + 1) = 0 := by
      rw [mathieuContinuedFractionHead]
      simp only [Complex.ofReal_zero, zero_pow two_ne_zero, mul_zero, zero_div, sub_zero]
      rw [mathieuA_zero]
      push_cast
      ring
    rw [h0]
    simp only [Complex.ofReal_zero, mathieuContinuedFractionTail_zero_left, neg_zero]
    exact tendsto_const_nhds
  set A : ℕ → ℂ := fun k => mathieuFourierA (2 * n) (2 * k) q
  have hlim := tendsto_neg_mathieuContinuedFractionTail_mathieuContinuedFractionHead (A := A)
    (s := fun k : ℕ => ((2 * k + 2) ^ 2 : ℂ)) (c := fun k : ℕ => if k = 0 then (2 : ℂ) else 1)
    (e₀ := (mathieuA (2 * n) q : ℂ)) (a := (mathieuA (2 * n) q : ℂ)) (n := n)
    (Complex.ofReal_ne_zero.2 hq) ?_ ?_ ?_ ?_ ?_ ?_ hE
  · refine hlim.congr fun N => ?_
    congr 2
    funext k
    push_cast
    ring
  · have := mathieuFourierA_even_rec_zero n q
    simp only [A]; norm_num; linear_combination this
  · intro k
    rcases k with _ | k
    · have := mathieuFourierA_even_rec_one n q
      simp only [A]; norm_num; linear_combination -this
    · have := mathieuFourierA_even_rec n q (m := k + 2) (by omega)
      simp only [A, show 2 * (k + 2) - 2 = 2 * (k + 1) by omega,
        show 2 * (k + 2) + 2 = 2 * (k + 1 + 2) by ring] at this ⊢
      simp only [show k + 1 + 1 = k + 2 by ring, add_eq_zero, one_ne_zero, and_false,
        ite_false, one_mul]
      push_cast at this ⊢
      linear_combination -this
  · intro k hk; simp only [show k ≠ 0 by omega, ite_false]
  · intro h0
    have hs := hasSum_mathieuFourierA_even_sq n q
    simp only [A] at h0
    simp only [h0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at hs
    exact zero_ne_one (hasSum_zero.unique hs)
  · exact tendsto_mathieuFourierA_comp_atTop _ q
      (tendsto_atTop_atTop_of_monotone (fun _ _ h => by omega) fun b => ⟨b, by omega⟩)
  · simpa using tendsto_norm_two_mul_add_sq 2

/-- **DLMF 28.6.16, case `n = 0`**: `a₀(q) = -2q²/(4 - a₀ - q²/(16 - a₀ - ⋯))` (the printed
pattern degenerates at `n = 0`; the factor 2 comes from 28.4.5). -/
@[dlmf 28.6.E16]
theorem mathieuA_zero_contFrac (q : ℝ) :
    Tendsto (fun N => -2 *
        mathieuContinuedFractionTail q (mathieuA 0 q) (fun k => (2 * k + 2) ^ 2) N)
      atTop (𝓝 (mathieuA 0 q : ℂ)) := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp only [Complex.ofReal_zero, mathieuContinuedFractionTail_zero_left, mul_zero, mathieuA_zero]
    simp
  set A : ℕ → ℂ := fun k => (if k = 0 then 2 else 1) * mathieuFourierA 0 (2 * k) q
  have hlim := tendsto_neg_mathieuContinuedFractionTail_mathieuContinuedFractionHead (A := A)
    (s := fun k : ℕ => ((2 * k + 2) ^ 2 : ℂ)) (c := fun _ => 1)
    (e₀ := (mathieuA 0 q : ℂ) / 2) (a := (mathieuA 0 q : ℂ)) (n := 0)
    (Complex.ofReal_ne_zero.2 hq) ?_ ?_ (fun _ _ => rfl) ?_ ?_ ?_ (fun k hk => absurd hk (by omega))
  · simp only [mathieuContinuedFractionHead, zero_add] at hlim
    have := hlim.const_mul 2
    simp only [mul_div_cancel₀ _ (two_ne_zero' ℂ)] at this
    refine this.congr fun N => ?_
    ring
  · have := mathieuFourierA_even_rec_zero 0 q
    simp only [A]; norm_num at this ⊢; linear_combination this
  · intro k
    rcases k with _ | k
    · have := mathieuFourierA_even_rec_one 0 q
      simp only [A]; norm_num at this ⊢; linear_combination -this
    · have := mathieuFourierA_even_rec 0 q (m := k + 2) (by omega)
      simp only [A, show 2 * (k + 2) - 2 = 2 * (k + 1) by omega,
        show 2 * (k + 2) + 2 = 2 * (k + 1 + 2) by ring] at this ⊢
      simp only [show k + 1 + 1 = k + 2 by ring, add_eq_zero, one_ne_zero, and_false,
        ite_false, one_mul]
      push_cast at this ⊢
      simp only [and_false, ite_false, mul_one]
      linear_combination -this
  · intro h0
    have hs := hasSum_mathieuFourierA_even_sq 0 q
    have h0' : ∀ k, mathieuFourierA 0 (2 * k) q = 0 := fun k => by
      have := h0 k
      simp only [A] at this
      rcases mul_eq_zero.1 this with h | h
      · split_ifs at h <;> norm_num at h
      · exact h
    simp only [mul_zero, h0', ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hs
    exact zero_ne_one (hasSum_zero.unique hs)
  · have h := tendsto_mathieuFourierA_comp_atTop 0 q (g := fun k => 2 * k)
      (tendsto_atTop_atTop_of_monotone (fun _ _ h => by omega) fun b => ⟨b, by omega⟩)
    refine (h.congr' ?_)
    filter_upwards [eventually_ge_atTop 1] with k hk
    simp [A, show k ≠ 0 by omega]
  · simpa using tendsto_norm_two_mul_add_sq 2

/-- **DLMF 28.6.17**: for `a = a_{2n+1}(q)`,
`a - (2n+1)² - q²/(a - (2n-1)² - ⋯ q²/(a - 3² - q²/(a - 1² - q)))
= -q²/((2n+3)² - a - q²/((2n+5)² - a - ⋯))`. -/
@[dlmf 28.6.E17]
theorem mathieuA_odd_contFrac (n : ℕ) {q : ℝ}
    (hE : ∀ k < n, mathieuContinuedFractionHead q (mathieuA (2 * n + 1) q)
        (mathieuA (2 * n + 1) q - 1 - q)
      (fun _ => 1) (fun k => (2 * k + 3) ^ 2) k ≠ 0) :
    Tendsto (fun N => -mathieuContinuedFractionTail q (mathieuA (2 * n + 1) q)
        (fun k => (2 * n + 2 * k + 3) ^ 2) N)
      atTop (𝓝 (mathieuContinuedFractionHead q (mathieuA (2 * n + 1) q)
          (mathieuA (2 * n + 1) q - 1 - q)
        (fun _ => 1) (fun k => (2 * k + 3) ^ 2) n)) := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp only [Complex.ofReal_zero, mathieuContinuedFractionTail_zero_left, neg_zero]
    convert tendsto_const_nhds using 2
    rcases n with _ | n'
    · rw [mathieuContinuedFractionHead, mathieuA_zero]; push_cast; ring
    · rw [mathieuContinuedFractionHead]
      simp only [zero_pow two_ne_zero, mul_zero, zero_div, sub_zero]
      rw [mathieuA_zero]; push_cast; ring
  set A : ℕ → ℂ := fun k => mathieuFourierA (2 * n + 1) (2 * k + 1) q
  have hlim := tendsto_neg_mathieuContinuedFractionTail_mathieuContinuedFractionHead (A := A)
    (s := fun k : ℕ => ((2 * k + 3) ^ 2 : ℂ)) (c := fun _ => 1)
    (e₀ := (mathieuA (2 * n + 1) q : ℂ) - 1 - q) (a := (mathieuA (2 * n + 1) q : ℂ)) (n := n)
    (Complex.ofReal_ne_zero.2 hq) ?_ ?_ (fun _ _ => rfl) ?_ ?_ ?_ hE
  · refine hlim.congr fun N => ?_
    congr 2
    funext k
    push_cast
    ring
  · have := mathieuFourierA_odd_rec_zero n q
    simp only [A]; norm_num; linear_combination this
  · intro k
    have := mathieuFourierA_odd_rec n q (m := k + 1) (by omega)
    simp only [A, show 2 * (k + 1) - 1 = 2 * k + 1 by omega,
      show 2 * (k + 1) + 3 = 2 * (k + 2) + 1 by ring] at this ⊢
    push_cast at this ⊢
    linear_combination -this
  · intro h0
    have hs := hasSum_mathieuFourierA_odd_sq n q
    simp only [A] at h0
    simp only [h0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hs
    exact zero_ne_one (hasSum_zero.unique hs)
  · exact tendsto_mathieuFourierA_comp_atTop _ q
      (tendsto_atTop_atTop_of_monotone (fun _ _ h => by omega) fun b => ⟨b, by omega⟩)
  · simpa using tendsto_norm_two_mul_add_sq 3

/-- **DLMF 28.6.18**: for `a = b_{2n+1}(q)`,
`a - (2n+1)² - q²/(a - (2n-1)² - ⋯ q²/(a - 3² - q²/(a - 1² + q)))
= -q²/((2n+3)² - a - q²/((2n+5)² - a - ⋯))`. -/
@[dlmf 28.6.E18]
theorem mathieuB_odd_contFrac (n : ℕ) {q : ℝ}
    (hE : ∀ k < n, mathieuContinuedFractionHead q (mathieuB (2 * n + 1) q)
        (mathieuB (2 * n + 1) q - 1 + q)
      (fun _ => 1) (fun k => (2 * k + 3) ^ 2) k ≠ 0) :
    Tendsto (fun N => -mathieuContinuedFractionTail q (mathieuB (2 * n + 1) q)
        (fun k => (2 * n + 2 * k + 3) ^ 2) N)
      atTop (𝓝 (mathieuContinuedFractionHead q (mathieuB (2 * n + 1) q)
          (mathieuB (2 * n + 1) q - 1 + q)
        (fun _ => 1) (fun k => (2 * k + 3) ^ 2) n)) := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp only [Complex.ofReal_zero, mathieuContinuedFractionTail_zero_left, neg_zero]
    convert tendsto_const_nhds using 2
    rcases n with _ | n'
    · rw [mathieuContinuedFractionHead, mathieuB_zero (by omega)]; push_cast; ring
    · rw [mathieuContinuedFractionHead]
      simp only [zero_pow two_ne_zero, mul_zero, zero_div, sub_zero]
      rw [mathieuB_zero (by omega)]; push_cast; ring
  set A : ℕ → ℂ := fun k => mathieuFourierB (2 * n + 1) (2 * k + 1) q
  have hlim := tendsto_neg_mathieuContinuedFractionTail_mathieuContinuedFractionHead (A := A)
    (s := fun k : ℕ => ((2 * k + 3) ^ 2 : ℂ)) (c := fun _ => 1)
    (e₀ := (mathieuB (2 * n + 1) q : ℂ) - 1 + q) (a := (mathieuB (2 * n + 1) q : ℂ)) (n := n)
    (Complex.ofReal_ne_zero.2 hq) ?_ ?_ (fun _ _ => rfl) ?_ ?_ ?_ hE
  · refine hlim.congr fun N => ?_
    congr 2
    funext k
    push_cast
    ring
  · have := mathieuFourierB_odd_rec_zero n q
    simp only [A]; norm_num; linear_combination this
  · intro k
    have := mathieuFourierB_odd_rec n q (m := k + 1) (by omega)
    simp only [A, show 2 * (k + 1) - 1 = 2 * k + 1 by omega,
      show 2 * (k + 1) + 3 = 2 * (k + 2) + 1 by ring] at this ⊢
    push_cast at this ⊢
    linear_combination -this
  · intro h0
    have hs := hasSum_mathieuFourierB_odd_sq n q
    simp only [A] at h0
    simp only [h0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hs
    exact zero_ne_one (hasSum_zero.unique hs)
  · exact tendsto_mathieuFourierB_comp_atTop (by omega) q
      (tendsto_atTop_atTop_of_monotone (fun _ _ h => by omega) fun b => ⟨b, by omega⟩)
  · simpa using tendsto_norm_two_mul_add_sq 3

/-- **DLMF 28.6.19**: for `a = b_{2n+2}(q)`,
`a - (2n+2)² - q²/(a - (2n)² - ⋯ q²/(a - 2²)) = -q²/((2n+4)² - a - q²/((2n+6)² - a - ⋯))`. -/
@[dlmf 28.6.E19]
theorem mathieuB_even_contFrac (n : ℕ) {q : ℝ}
    (hE : ∀ k < n, mathieuContinuedFractionHead q (mathieuB (2 * n + 2) q)
        (mathieuB (2 * n + 2) q - 4)
      (fun _ => 1) (fun k => (2 * k + 4) ^ 2) k ≠ 0) :
    Tendsto (fun N => -mathieuContinuedFractionTail q (mathieuB (2 * n + 2) q)
        (fun k => (2 * n + 2 * k + 4) ^ 2) N)
      atTop (𝓝 (mathieuContinuedFractionHead q (mathieuB (2 * n + 2) q) (mathieuB (2 * n + 2) q - 4)
        (fun _ => 1) (fun k => (2 * k + 4) ^ 2) n)) := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp only [Complex.ofReal_zero, mathieuContinuedFractionTail_zero_left, neg_zero]
    convert tendsto_const_nhds using 2
    rcases n with _ | n'
    · rw [mathieuContinuedFractionHead, mathieuB_zero (by omega)]; push_cast; ring
    · rw [mathieuContinuedFractionHead]
      simp only [zero_pow two_ne_zero, mul_zero, zero_div, sub_zero]
      rw [mathieuB_zero (by omega)]; push_cast; ring
  set A : ℕ → ℂ := fun k => mathieuFourierB (2 * n + 2) (2 * k + 2) q
  have hlim := tendsto_neg_mathieuContinuedFractionTail_mathieuContinuedFractionHead (A := A)
    (s := fun k : ℕ => ((2 * k + 4) ^ 2 : ℂ)) (c := fun _ => 1)
    (e₀ := (mathieuB (2 * n + 2) q : ℂ) - 4) (a := (mathieuB (2 * n + 2) q : ℂ)) (n := n)
    (Complex.ofReal_ne_zero.2 hq) ?_ ?_ (fun _ _ => rfl) ?_ ?_ ?_ hE
  · refine hlim.congr fun N => ?_
    congr 2
    funext k
    push_cast
    ring
  · have := mathieuFourierB_even_rec_zero n q
    simp only [A]; norm_num; linear_combination this
  · intro k
    have := mathieuFourierB_even_rec n q (m := k + 2) (by omega)
    simp only [A, show 2 * (k + 2) - 2 = 2 * k + 2 by omega,
      ] at this ⊢
    simp only [show 2 * (k + 1) + 2 = 2 * (k + 2) by ring]
    push_cast at this ⊢
    linear_combination -this
  · intro h0
    have hs := hasSum_mathieuFourierB_even_sq n q
    simp only [A] at h0
    simp only [h0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hs
    exact zero_ne_one (hasSum_zero.unique hs)
  · exact tendsto_mathieuFourierB_comp_atTop (by omega) q
      (tendsto_atTop_atTop_of_monotone (fun _ _ h => by omega) fun b => ⟨b, by omega⟩)
  · simpa using tendsto_norm_two_mul_add_sq 4

end DLMF.Mathieu
