/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.WignerSymbols.SixJ

/-!
# The `9j` symbol: DLMF §§34.6–34.7

Statements of DLMF §34.6 (the definition 34.6.1 as a sum of products of six `3j` symbols)
and §34.7 (special case, symmetry, orthogonality and sums) for `wigner9j`, which is defined by
the sum 34.6.2 of products of three `6j` symbols. The `9j` symbol vanishes unless every row
and every column is a triad (each of them is a triad of one of the three `6j` factors).

Summations over angular momenta run over `halfIntegersUpTo x` for a bound `x` beyond which
the summands vanish, and summations over projections over `projections j`. The relations are
stated for all rational arguments where both sides vanish outside the admissible range
(checked numerically with exact arithmetic, see the ledger).
-/

@[expose] public noncomputable section

open Finset

namespace DLMF.WignerSymbols

/-- DLMF 34.6.1: the `9j` symbol as the sum over all projections `m_{rs}` of the product of
the six `3j` symbols of its rows and columns. -/
@[dlmf 34.6.E1]
theorem wigner9j_eq_sum_threeJ (j₁₁ j₁₂ j₁₃ j₂₁ j₂₂ j₂₃ j₃₁ j₃₂ j₃₃ : ℚ) :
    wigner9j j₁₁ j₁₂ j₁₃ j₂₁ j₂₂ j₂₃ j₃₁ j₃₂ j₃₃ =
      ∑ m₁₁ ∈ projections j₁₁, ∑ m₁₂ ∈ projections j₁₂, ∑ m₁₃ ∈ projections j₁₃,
      ∑ m₂₁ ∈ projections j₂₁, ∑ m₂₂ ∈ projections j₂₂, ∑ m₂₃ ∈ projections j₂₃,
      ∑ m₃₁ ∈ projections j₃₁, ∑ m₃₂ ∈ projections j₃₂, ∑ m₃₃ ∈ projections j₃₃,
        wigner3j j₁₁ j₁₂ j₁₃ m₁₁ m₁₂ m₁₃ * wigner3j j₂₁ j₂₂ j₂₃ m₂₁ m₂₂ m₂₃ *
          wigner3j j₃₁ j₃₂ j₃₃ m₃₁ m₃₂ m₃₃ * wigner3j j₁₁ j₂₁ j₃₁ m₁₁ m₂₁ m₃₁ *
          wigner3j j₁₂ j₂₂ j₃₂ m₁₂ m₂₂ m₃₂ * wigner3j j₁₃ j₂₃ j₃₃ m₁₃ m₂₃ m₃₃ := by
  sorry

/-! ## §34.7(i) Special case -/

/-- The sum `j₁ + j₂ + j₃` of a triad is a natural number. -/
lemma q2w_triad_sum {a b c : ℚ} (h : IsTriad a b c) : IsNatQ (a + b + c) :=
  ((h.1.add h.2.1).add h.2.2).of_eq (by ring)

/-- `2a` is a natural number for the first entry of a triad. -/
lemma q2w_triad_two_mul {a b c : ℚ} (h : IsTriad a b c) : IsNatQ (2 * a) :=
  (h.1.add h.2.1).of_eq (by ring)

/-- DLMF 34.7.1: `{j₁₁ j₁₂ j₁₃; j₂₁ j₂₂ j₁₃; j₃₁ j₃₁ 0}`
`= (-1)^{j₁₂+j₂₁+j₁₃+j₃₁} ((2j₁₃+1)(2j₃₁+1))^{-1/2} {j₁₁ j₁₂ j₁₃; j₂₂ j₂₁ j₃₁}`. -/
@[dlmf 34.7.E1]
theorem wigner9j_zero (j₁₁ j₁₂ j₁₃ j₂₁ j₂₂ j₃₁ : ℚ) :
    wigner9j j₁₁ j₁₂ j₁₃ j₂₁ j₂₂ j₁₃ j₃₁ j₃₁ 0 =
      signPow (j₁₂ + j₂₁ + j₁₃ + j₃₁) / Real.sqrt ((2 * (j₁₃ : ℝ) + 1) * (2 * j₃₁ + 1)) *
        wigner6j j₁₁ j₁₂ j₁₃ j₂₂ j₂₁ j₃₁ := by
  have hM : ∀ x : ℚ, wigner6j j₁₂ j₂₂ j₃₁ j₂₁ x j₁₃ = wigner6j x j₁₂ j₁₃ j₂₂ j₂₁ j₃₁ := by
    intro x
    rw [wigner6j_flip, wigner6j_swap_columns]
  have h3 : ∀ x : ℚ, x ≠ j₁₁ → wigner6j j₁₃ j₁₃ 0 x j₁₁ j₁₂ = 0 := by
    intro x hx
    apply wigner6j_of_not
    rintro ⟨-, -, -, ⟨-, ⟨b, hb⟩, ⟨c, hc⟩⟩⟩
    apply hx
    have h1 : (0 : ℚ) ≤ b := b.cast_nonneg
    have h2 : (0 : ℚ) ≤ c := c.cast_nonneg
    linarith
  have hF3 : wigner6j j₁₃ j₁₃ 0 j₁₁ j₁₁ j₁₂ = wigner6j j₁₂ j₁₁ j₁₃ 0 j₁₃ j₁₁ := by
    rw [wigner6j_flip j₁₃ j₁₃ 0 j₁₁ j₁₁ j₁₂, wigner6j_swap_columns j₁₃ j₁₁ j₁₂ j₁₁ j₁₃ 0,
      q2w_wigner6j_swap23 j₁₁ j₁₃ j₁₂ j₁₃ j₁₁ 0, wigner6j_swap_columns j₁₁ j₁₂ j₁₃ j₁₃ 0 j₁₁]
  have hF1 : wigner6j j₁₁ j₂₁ j₃₁ j₃₁ 0 j₁₁ = wigner6j j₂₁ j₁₁ j₃₁ 0 j₃₁ j₁₁ :=
    wigner6j_swap_columns _ _ _ _ _ _
  unfold wigner9j
  by_cases hk : IsNatQ (2 * j₁₁)
  · obtain ⟨k, hk⟩ := hk
    have hj : ((k : ℚ) / 2) = j₁₁ := by linarith
    rw [Finset.sum_eq_single k]
    · rw [hj, hM, hF1, hF3]
      by_cases t1 : IsTriad j₂₁ j₁₁ j₃₁
      · by_cases t3 : IsTriad j₁₂ j₁₁ j₁₃
        · rw [wigner6j_zero t1, wigner6j_zero t3]
          obtain ⟨n₁, hn₁⟩ := q2w_triad_sum t1
          obtain ⟨n₂, hn₂⟩ := q2w_triad_sum t3
          obtain ⟨e₁, he₁⟩ := (t1.symm23.cycle.cycle).2.1.add t1.symm23.cycle.cycle.2.2
          obtain ⟨e₃, he₃⟩ := (t3.symm23.cycle.cycle).2.1.add t3.symm23.cycle.cycle.2.2
          rw [signPow_of_eq (n := (n₁ : ℤ)) (by rw [hn₁]; push_cast; ring),
            signPow_of_eq (n := (n₂ : ℤ)) (by rw [hn₂]; push_cast; ring),
            signPow_of_eq (n := (n₁ : ℤ) + n₂ - k) (by push_cast; linarith)]
          have hx : (2 * (j₁₁ : ℝ) + 1) = (k : ℝ) + 1 := by
            have := congrArg (fun q : ℚ => (q : ℝ)) hk
            push_cast at this; linarith
          have h31 : (2 * (j₃₁ : ℝ) + 1) = (e₁ : ℝ) + 1 := by
            have := congrArg (fun q : ℚ => (q : ℝ)) he₁
            push_cast at this; linarith
          have h13 : (2 * (j₁₃ : ℝ) + 1) = (e₃ : ℝ) + 1 := by
            have := congrArg (fun q : ℚ => (q : ℝ)) he₃
            push_cast at this; linarith
          rw [hx, h31, h13, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
            Real.sqrt_mul (by positivity), zpow_sub₀ (by norm_num), zpow_add₀ (by norm_num)]
          have hs : Real.sqrt ((k : ℝ) + 1) ^ 2 = (k : ℝ) + 1 := Real.sq_sqrt (by positivity)
          have hs0 : Real.sqrt ((k : ℝ) + 1) ≠ 0 := by positivity
          have hs1 : Real.sqrt ((e₁ : ℝ) + 1) ≠ 0 := by positivity
          have hs3 : Real.sqrt ((e₃ : ℝ) + 1) ≠ 0 := by positivity
          simp only [zpow_natCast]
          field_simp
          rw [hs]
          have : ((-1 : ℝ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
          rw [this, one_mul]
        · rw [wigner6j_of_not (fun h => t3 h.1), wigner6j_of_not (fun h => t3 h.1.symm12)]
          ring
      · rw [wigner6j_of_not (fun h => t1 h.1), wigner6j_of_not (fun h => t1 h.2.1.symm12)]
        ring
    · intro t _ ht
      rw [h3 _ (fun h => ht (by
        have : (t : ℚ) = k := by linarith
        exact_mod_cast this))]
      ring
    · intro hk'
      exfalso; apply hk'
      rw [mem_range, add_zero, hk, Int.floor_natCast, Int.toNat_natCast]
      omega
  · rw [Finset.sum_eq_zero, wigner6j_of_not (fun h => hk (q2w_triad_two_mul h.1))]
    · ring
    · intro t _
      rw [h3 _ (fun h => hk ⟨t, by linarith⟩)]
      ring

/-! ## §34.7(ii) Symmetry

Even (cyclic) permutations of rows or columns and the transposition leave the `9j` symbol
unchanged; odd permutations of rows or columns give the phase `(-1)^R`, `R` the sum of all
nine arguments. Together these generate the 72 symmetries of DLMF §34.7(ii). -/

/-- DLMF §34.7(ii): invariance under transposition. -/
@[dlmf 34.7.ii]
theorem wigner9j_transpose (j₁₁ j₁₂ j₁₃ j₂₁ j₂₂ j₂₃ j₃₁ j₃₂ j₃₃ : ℚ) :
    wigner9j j₁₁ j₁₂ j₁₃ j₂₁ j₂₂ j₂₃ j₃₁ j₃₂ j₃₃ =
      wigner9j j₁₁ j₂₁ j₃₁ j₁₂ j₂₂ j₃₂ j₁₃ j₂₃ j₃₃ := by
  unfold wigner9j
  refine Finset.sum_congr rfl fun t _ => ?_
  set x : ℚ := (t : ℚ) / 2
  have e1 : wigner6j j₁₁ j₂₁ j₃₁ j₃₂ j₃₃ x = wigner6j j₃₁ j₃₂ j₃₃ x j₁₁ j₂₁ := by
    rw [q2w_wigner6j_flip12 j₁₁ j₂₁ j₃₁ j₃₂ j₃₃ x, q2w_wigner6j_swap23 j₃₂ j₃₃ j₃₁ j₁₁ j₂₁ x,
      wigner6j_swap_columns j₃₂ j₃₁ j₃₃ j₁₁ x j₂₁]
  have e3 : wigner6j j₁₃ j₂₃ j₃₃ x j₁₁ j₁₂ = wigner6j j₁₁ j₁₂ j₁₃ j₂₃ j₃₃ x := by
    rw [wigner6j_flip j₁₃ j₂₃ j₃₃ x j₁₁ j₁₂, wigner6j_swap_columns j₁₃ j₁₁ j₁₂ x j₂₃ j₃₃,
      q2w_wigner6j_swap23 j₁₁ j₁₃ j₁₂ j₂₃ x j₃₃]
  have e2 : wigner6j j₁₂ j₂₂ j₃₂ j₂₁ x j₂₃ = wigner6j j₂₁ j₂₂ j₂₃ j₁₂ x j₃₂ := by
    rw [wigner6j_swap_columns j₁₂ j₂₂ j₃₂ j₂₁ x j₂₃, wigner6j_flip j₂₂ j₁₂ j₃₂ x j₂₁ j₂₃,
      wigner6j_swap_columns j₂₂ j₂₁ j₂₃ x j₁₂ j₃₂]
  rw [e1, e2, e3]
  ring

/-- DLMF §34.7(ii): invariance under the cyclic permutation of the rows. -/
@[dlmf 34.7.ii]
theorem wigner9j_cycle_rows (j₁₁ j₁₂ j₁₃ j₂₁ j₂₂ j₂₃ j₃₁ j₃₂ j₃₃ : ℚ) :
    wigner9j j₁₁ j₁₂ j₁₃ j₂₁ j₂₂ j₂₃ j₃₁ j₃₂ j₃₃ =
      wigner9j j₂₁ j₂₂ j₂₃ j₃₁ j₃₂ j₃₃ j₁₁ j₁₂ j₁₃ := by
  sorry

/-- DLMF §34.7(ii): invariance under the cyclic permutation of the columns. -/
@[dlmf 34.7.ii]
theorem wigner9j_cycle_columns (j₁₁ j₁₂ j₁₃ j₂₁ j₂₂ j₂₃ j₃₁ j₃₂ j₃₃ : ℚ) :
    wigner9j j₁₁ j₁₂ j₁₃ j₂₁ j₂₂ j₂₃ j₃₁ j₃₂ j₃₃ =
      wigner9j j₁₂ j₁₃ j₁₁ j₂₂ j₂₃ j₂₁ j₃₂ j₃₃ j₃₁ := by
  sorry

/-- DLMF §34.7(ii): interchanging two rows gives the phase `(-1)^R`. -/
@[dlmf 34.7.ii]
theorem wigner9j_swap_rows (j₁₁ j₁₂ j₁₃ j₂₁ j₂₂ j₂₃ j₃₁ j₃₂ j₃₃ : ℚ) :
    wigner9j j₁₁ j₁₂ j₁₃ j₂₁ j₂₂ j₂₃ j₃₁ j₃₂ j₃₃ =
      signPow (j₁₁ + j₁₂ + j₁₃ + j₂₁ + j₂₂ + j₂₃ + j₃₁ + j₃₂ + j₃₃) *
        wigner9j j₂₁ j₂₂ j₂₃ j₁₁ j₁₂ j₁₃ j₃₁ j₃₂ j₃₃ := by
  sorry

/-- DLMF §34.7(ii): interchanging two columns gives the phase `(-1)^R`. -/
@[dlmf 34.7.ii]
theorem wigner9j_swap_columns (j₁₁ j₁₂ j₁₃ j₂₁ j₂₂ j₂₃ j₃₁ j₃₂ j₃₃ : ℚ) :
    wigner9j j₁₁ j₁₂ j₁₃ j₂₁ j₂₂ j₂₃ j₃₁ j₃₂ j₃₃ =
      signPow (j₁₁ + j₁₂ + j₁₃ + j₂₁ + j₂₂ + j₂₃ + j₃₁ + j₃₂ + j₃₃) *
        wigner9j j₁₂ j₁₁ j₁₃ j₂₂ j₂₁ j₂₃ j₃₂ j₃₁ j₃₃ := by
  sorry

/-! ## §34.7(iv) Orthogonality -/

/-- DLMF 34.7.2: `∑_{j₁₂, j₃₄} (2j₁₂+1)(2j₃₄+1)(2j₁₃+1)(2j₂₄+1)`
`{j₁ j₂ j₁₂; j₃ j₄ j₃₄; j₁₃ j₂₄ j}{j₁ j₂ j₁₂; j₃ j₄ j₃₄; j₁₃' j₂₄' j} = δ_{j₁₃,j₁₃'} δ_{j₂₄,j₂₄'}`,
for `(j₁ j₃ j₁₃)`, `(j₂ j₄ j₂₄)` and `(j₁₃ j₂₄ j)` triads. -/
@[dlmf 34.7.E2]
theorem wigner9j_orthogonality {j₁ j₂ j₃ j₄ j₁₃ j₂₄ j : ℚ} (h₁ : IsTriad j₁ j₃ j₁₃)
    (h₂ : IsTriad j₂ j₄ j₂₄) (h₃ : IsTriad j₁₃ j₂₄ j) (j₁₃' j₂₄' : ℚ) :
    ∑ j₁₂ ∈ halfIntegersUpTo (j₁ + j₂), ∑ j₃₄ ∈ halfIntegersUpTo (j₃ + j₄),
        (2 * (j₁₂ : ℝ) + 1) * (2 * (j₃₄ : ℝ) + 1) * (2 * (j₁₃ : ℝ) + 1) * (2 * (j₂₄ : ℝ) + 1) *
          wigner9j j₁ j₂ j₁₂ j₃ j₄ j₃₄ j₁₃ j₂₄ j * wigner9j j₁ j₂ j₁₂ j₃ j₄ j₃₄ j₁₃' j₂₄' j =
      if j₁₃ = j₁₃' ∧ j₂₄ = j₂₄' then 1 else 0 := by
  sorry

/-! ## §34.7(vi) Sums -/

/-- DLMF 34.7.3: the sum rule
`∑_{j₁₃, j₂₄} (-1)^{2j₂+j₂₄+j₂₃-j₃₄} (2j₁₃+1)(2j₂₄+1)`
`{j₁ j₂ j₁₂; j₃ j₄ j₃₄; j₁₃ j₂₄ j}{j₁ j₃ j₁₃; j₄ j₂ j₂₄; j₁₄ j₂₃ j}`
`= {j₁ j₂ j₁₂; j₄ j₃ j₃₄; j₁₄ j₂₃ j}`. -/
@[dlmf 34.7.E3]
theorem wigner9j_sum_rule (j₁ j₂ j₃ j₄ j₁₂ j₃₄ j₁₄ j₂₃ j : ℚ) :
    ∑ j₁₃ ∈ halfIntegersUpTo (j₁ + j₃), ∑ j₂₄ ∈ halfIntegersUpTo (j₂ + j₄),
        signPow (2 * j₂ + j₂₄ + j₂₃ - j₃₄) * (2 * (j₁₃ : ℝ) + 1) * (2 * (j₂₄ : ℝ) + 1) *
          wigner9j j₁ j₂ j₁₂ j₃ j₄ j₃₄ j₁₃ j₂₄ j * wigner9j j₁ j₃ j₁₃ j₄ j₂ j₂₄ j₁₄ j₂₃ j =
      wigner9j j₁ j₂ j₁₂ j₄ j₃ j₃₄ j₁₄ j₂₃ j := by
  sorry

/-- DLMF 34.7.4: `(j₁₃ j₂₃ j₃₃; m₁₃ m₂₃ m₃₃) {9j}` equals the sum over `m_{r1}, m_{r2}`
(`r = 1, 2, 3`) of the product of the five `3j` symbols of the three rows and of the first two
columns. -/
@[dlmf 34.7.E4]
theorem wigner3j_mul_wigner9j (j₁₁ j₁₂ j₁₃ j₂₁ j₂₂ j₂₃ j₃₁ j₃₂ j₃₃ m₁₃ m₂₃ m₃₃ : ℚ) :
    wigner3j j₁₃ j₂₃ j₃₃ m₁₃ m₂₃ m₃₃ * wigner9j j₁₁ j₁₂ j₁₃ j₂₁ j₂₂ j₂₃ j₃₁ j₃₂ j₃₃ =
      ∑ m₁₁ ∈ projections j₁₁, ∑ m₁₂ ∈ projections j₁₂, ∑ m₂₁ ∈ projections j₂₁,
      ∑ m₂₂ ∈ projections j₂₂, ∑ m₃₁ ∈ projections j₃₁, ∑ m₃₂ ∈ projections j₃₂,
        wigner3j j₁₁ j₁₂ j₁₃ m₁₁ m₁₂ m₁₃ * wigner3j j₂₁ j₂₂ j₂₃ m₂₁ m₂₂ m₂₃ *
          wigner3j j₃₁ j₃₂ j₃₃ m₃₁ m₃₂ m₃₃ * wigner3j j₁₁ j₂₁ j₃₁ m₁₁ m₂₁ m₃₁ *
          wigner3j j₁₂ j₂₂ j₃₂ m₁₂ m₂₂ m₃₂ := by
  sorry

/-- DLMF 34.7.5: `∑_{j'} (2j'+1) {j₁₁ j₁₂ j'; j₂₁ j₂₂ j₂₃; j₃₁ j₃₂ j₃₃}{j₁₁ j₁₂ j'; j₂₃ j₃₃ j}`
`= (-1)^{2j} {j₂₁ j₂₂ j₂₃; j₁₂ j j₃₂}{j₃₁ j₃₂ j₃₃; j j₁₁ j₂₁}`. -/
@[dlmf 34.7.E5]
theorem wigner9j_sum_wigner6j (j₁₁ j₁₂ j₂₁ j₂₂ j₂₃ j₃₁ j₃₂ j₃₃ j : ℚ) :
    ∑ j' ∈ halfIntegersUpTo (j₁₁ + j₁₂),
        (2 * (j' : ℝ) + 1) * wigner9j j₁₁ j₁₂ j' j₂₁ j₂₂ j₂₃ j₃₁ j₃₂ j₃₃ *
          wigner6j j₁₁ j₁₂ j' j₂₃ j₃₃ j =
      signPow (2 * j) * wigner6j j₂₁ j₂₂ j₂₃ j₁₂ j j₃₂ * wigner6j j₃₁ j₃₂ j₃₃ j j₁₁ j₂₁ := by
  sorry

end DLMF.WignerSymbols
