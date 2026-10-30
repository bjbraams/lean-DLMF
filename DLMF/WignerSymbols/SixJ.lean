/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.WignerSymbols.Basic
public import DLMF.WignerSymbols.Q2wHelpers
public import DLMF.GeneralizedHypergeometric.ParameterAndSeriesProperties

/-!
# The `6j` symbol: DLMF §§34.4–34.5 and §34.10

Statements of DLMF §34.4 (the definition 34.4.1 as a sum of products of four `3j` symbols,
the `₄F₃` form 34.4.3, the tetrahedron of §34.4) and §34.5 (special cases, symmetry,
recursion, orthogonality and sums) for `wigner6j`, which is defined by the single sum 34.4.2,
and the trivial zeros of §34.10.

Summations over angular momenta run over `halfIntegersUpTo x` (the values `0, 1/2, …, x`)
for a bound `x` beyond which every summand vanishes, and summations over projections run over
`projections j`; the summands vanish outside the admissible range, so these are DLMF's sums
over all admissible values. Signs `(-1)^x` are `signPow x`; in every nonzero summand `x` is an
integer.

The tetrahedron statement of §34.4 is acquired in its correct direction: the four triangle
conditions are necessary for the existence of a tetrahedron with the six edge lengths. DLMF's
converse ("except in degenerate cases … equivalent to the existence of a tetrahedron") fails:
for `{3 2 2; 3 2 2}` the four triads satisfy the triangle conditions and the symbol is `1/14`,
but the Cayley–Menger determinant is `-324 < 0`, so no Euclidean tetrahedron has these edges.
-/

@[expose] public noncomputable section

open Finset

namespace DLMF.WignerSymbols

/-! ## Helpers -/

/-- Product of four square roots. -/
lemma w34_sqrt4 {x y z w : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (_hw : 0 ≤ w) :
    Real.sqrt x * Real.sqrt y * Real.sqrt z * Real.sqrt w = Real.sqrt (x * y * z * w) := by
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul hx]

/-- The product of the four triangle coefficients of a `6j` symbol as one square root. -/
lemma w34_delta_prod (a b c d e f g h i k l m : ℚ) :
    triangleDelta a b c * triangleDelta d e f * triangleDelta g h i * triangleDelta k l m =
      Real.sqrt ((factQ (a + b - c) * factQ (a - b + c) * factQ (-a + b + c) /
          factQ (a + b + c + 1)) *
        (factQ (d + e - f) * factQ (d - e + f) * factQ (-d + e + f) / factQ (d + e + f + 1)) *
        (factQ (g + h - i) * factQ (g - h + i) * factQ (-g + h + i) / factQ (g + h + i + 1)) *
        (factQ (k + l - m) * factQ (k - l + m) * factQ (-k + l + m) /
          factQ (k + l + m + 1))) := by
  unfold triangleDelta
  exact w34_sqrt4 (by unfold factQ; positivity) (by unfold factQ; positivity)
    (by unfold factQ; positivity) (by unfold factQ; positivity)

/-- The four triads of a `6j` symbol, as twelve nonnegative integers. -/
lemma w34_admissible6j_iff {j₁ j₂ j₃ l₁ l₂ l₃ : ℚ} :
    IsAdmissible6j j₁ j₂ j₃ l₁ l₂ l₃ ↔
      IsNatQ (j₁ + j₂ - j₃) ∧ IsNatQ (j₁ - j₂ + j₃) ∧ IsNatQ (-j₁ + j₂ + j₃) ∧
      IsNatQ (j₁ + l₂ - l₃) ∧ IsNatQ (j₁ - l₂ + l₃) ∧ IsNatQ (-j₁ + l₂ + l₃) ∧
      IsNatQ (l₁ + j₂ - l₃) ∧ IsNatQ (l₁ - j₂ + l₃) ∧ IsNatQ (-l₁ + j₂ + l₃) ∧
      IsNatQ (l₁ + l₂ - j₃) ∧ IsNatQ (l₁ - l₂ + j₃) ∧ IsNatQ (-l₁ + l₂ + j₃) := by
  unfold IsAdmissible6j IsTriad
  tauto

set_option hygiene false in
/-- Close `IsNatQ e` by one of the hypotheses `h1`, …, `h12` up to `ring`. -/
macro "w34_pick" : tactic => `(tactic| first
  | (apply IsNatQ.of_eq h1; ring1)
  | (apply IsNatQ.of_eq h2; ring1)
  | (apply IsNatQ.of_eq h3; ring1)
  | (apply IsNatQ.of_eq h4; ring1)
  | (apply IsNatQ.of_eq h5; ring1)
  | (apply IsNatQ.of_eq h6; ring1)
  | (apply IsNatQ.of_eq h7; ring1)
  | (apply IsNatQ.of_eq h8; ring1)
  | (apply IsNatQ.of_eq h9; ring1)
  | (apply IsNatQ.of_eq h10; ring1)
  | (apply IsNatQ.of_eq h11; ring1)
  | (apply IsNatQ.of_eq h12; ring1))


/-- The sum of 34.4.2 may be extended beyond `s = j₁ + j₂ + l₁ + l₂`. -/
lemma w34_sum6j_extend {j₁ j₂ j₃ l₁ l₂ l₃ : ℚ} (h : IsAdmissible6j j₁ j₂ j₃ l₁ l₂ l₃) (N : ℕ)
    (hN : ⌊j₁ + j₂ + l₁ + l₂⌋.toNat ≤ N) :
    ∑ s ∈ range (⌊j₁ + j₂ + l₁ + l₂⌋.toNat + 1), racahTerm6j j₁ j₂ j₃ l₁ l₂ l₃ s =
      ∑ s ∈ range (N + 1), racahTerm6j j₁ j₂ j₃ l₁ l₂ l₃ s := by
  have hβ : IsNatQ (j₁ + j₂ + l₁ + l₂) :=
    (((h.1.1.add h.2.2.2.1).add h.1.2.1).add h.1.2.2).of_eq (by ring)
  apply Finset.sum_subset (range_subset_range.mpr (by omega))
  intro s _ hs'
  simp only [mem_range, not_lt] at hs'
  have hlt : (j₁ + j₂ + l₁ + l₂ : ℚ) < s := by
    rw [← hβ.floor_toNat]; exact_mod_cast (by omega : ⌊j₁ + j₂ + l₁ + l₂⌋.toNat < s)
  unfold racahTerm6j
  rw [invFactQ_of_neg (x := j₁ + j₂ + l₁ + l₂ - s) (by linarith)]
  ring

/-! ## §34.4 Definition -/

/-- DLMF 34.4.1: the `6j` symbol as the double sum over all projections of products of four
`3j` symbols, `∑ (-1)^{l₁+m₁'+l₂+m₂'+l₃+m₃'} (j₁ j₂ j₃; m₁ m₂ m₃)(j₁ l₂ l₃; m₁ m₂' -m₃')`
`(l₁ j₂ l₃; -m₁' m₂ m₃')(l₁ l₂ j₃; m₁' -m₂' m₃)`. (DLMF takes 34.4.1 as the definition and
34.4.2 as a consequence; here `wigner6j` is defined by 34.4.2.) -/
@[dlmf 34.4.E1]
theorem wigner6j_eq_sum_threeJ (j₁ j₂ j₃ l₁ l₂ l₃ : ℚ) :
    wigner6j j₁ j₂ j₃ l₁ l₂ l₃ =
      ∑ m₁ ∈ projections j₁, ∑ m₂ ∈ projections j₂, ∑ m₃ ∈ projections j₃,
        ∑ m₁' ∈ projections l₁, ∑ m₂' ∈ projections l₂, ∑ m₃' ∈ projections l₃,
          signPow (l₁ + m₁' + l₂ + m₂' + l₃ + m₃') * wigner3j j₁ j₂ j₃ m₁ m₂ m₃ *
            wigner3j j₁ l₂ l₃ m₁ m₂' (-m₃') * wigner3j l₁ j₂ l₃ (-m₁') m₂ m₃' *
            wigner3j l₁ l₂ j₃ m₁' (-m₂') m₃ := by
  sorry

/-- DLMF §34.4: the triangle conditions of the four triads of a `6j` symbol are necessary for
the existence of a tetrahedron with edges `j₁, j₂, j₃, l₁, l₂, l₃` (edges `jᵣ` and `lᵣ`
opposite). With vertices `A, B, C, D`, `AB = j₁`, `BC = j₂`, `CA = j₃`, `CD = l₁`, `AD = l₂`,
`BD = l₃`, the faces are the triads `(j₁ j₂ j₃)`, `(j₁ l₂ l₃)`, `(l₁ j₂ l₃)`, `(l₁ l₂ j₃)`.
The converse stated by DLMF fails in general (see the module docstring). -/
@[dlmf 34.4]
theorem triangle_conditions_of_tetrahedron {X : Type*} [PseudoMetricSpace X] {A B C D : X}
    {j₁ j₂ j₃ l₁ l₂ l₃ : ℝ} (h₁ : dist A B = j₁) (h₂ : dist B C = j₂) (h₃ : dist C A = j₃)
    (h₄ : dist C D = l₁) (h₅ : dist A D = l₂) (h₆ : dist B D = l₃) :
    (|j₁ - j₂| ≤ j₃ ∧ j₃ ≤ j₁ + j₂) ∧ (|j₁ - l₂| ≤ l₃ ∧ l₃ ≤ j₁ + l₂) ∧
      (|l₁ - j₂| ≤ l₃ ∧ l₃ ≤ l₁ + j₂) ∧ (|l₁ - l₂| ≤ j₃ ∧ j₃ ≤ l₁ + l₂) := by
  subst h₁ h₂ h₃ h₄ h₅ h₆
  have t1 := dist_triangle A B C
  have t2 := dist_triangle B C A
  have t3 := dist_triangle C A B
  have t4 := dist_triangle A B D
  have t5 := dist_triangle B D A
  have t6 := dist_triangle D A B
  have t7 := dist_triangle B C D
  have t8 := dist_triangle C D B
  have t9 := dist_triangle D B C
  have t10 := dist_triangle A C D
  have t11 := dist_triangle C D A
  have t12 := dist_triangle D A C
  simp only [dist_comm] at *
  refine ⟨⟨abs_le.mpr ⟨?_, ?_⟩, ?_⟩, ⟨abs_le.mpr ⟨?_, ?_⟩, ?_⟩, ⟨abs_le.mpr ⟨?_, ?_⟩, ?_⟩,
    ⟨abs_le.mpr ⟨?_, ?_⟩, ?_⟩⟩ <;> linarith

/-- DLMF 34.4.3: the `6j` symbol as a terminating `₄F₃` of unit argument,
`(-1)^{j₁+j₃+l₁+l₃} Δ(j₁j₂j₃)Δ(j₂l₁l₃)(j₁-j₂+l₁+l₂)!(-j₂+j₃+l₂+l₃)!(j₁+j₃+l₁+l₃+1)!`
`/ (Δ(j₁l₂l₃)Δ(j₃l₁l₂)(j₁-j₂+j₃)!(-j₂+l₁+l₃)!(j₁+l₂+l₃+1)!(j₃+l₁+l₂+1)!)`
`× ₄F₃(-j₁+j₂-j₃, j₂-l₁-l₃, -j₁-l₂-l₃-1, -j₃-l₁-l₂-1;`
`-j₁+j₂-l₁-l₂, j₂-j₃-l₂-l₃, -j₁-j₃-l₁-l₃-1; 1)`.
The series terminates after `n = min(j₁-j₂+j₃, -j₂+l₁+l₃)` terms (`genFiniteHG`); assumes
the four triangle conditions. -/
@[dlmf 34.4.E3]
theorem wigner6j_eq_hyp4F3 {j₁ j₂ j₃ l₁ l₂ l₃ : ℚ} (h : IsAdmissible6j j₁ j₂ j₃ l₁ l₂ l₃) :
    (wigner6j j₁ j₂ j₃ l₁ l₂ l₃ : ℂ) =
      ((signPow (j₁ + j₃ + l₁ + l₃) * triangleDelta j₁ j₂ j₃ * triangleDelta j₂ l₁ l₃ *
          factQ (j₁ - j₂ + l₁ + l₂) * factQ (-j₂ + j₃ + l₂ + l₃) *
          factQ (j₁ + j₃ + l₁ + l₃ + 1) /
          (triangleDelta j₁ l₂ l₃ * triangleDelta j₃ l₁ l₂ * factQ (j₁ - j₂ + j₃) *
            factQ (-j₂ + l₁ + l₃) * factQ (j₁ + l₂ + l₃ + 1) * factQ (j₃ + l₁ + l₂ + 1)) :
          ℝ) : ℂ) *
        DLMF.Hypergeometric.genFiniteHG (min ⌊j₁ - j₂ + j₃⌋.toNat ⌊-j₂ + l₁ + l₃⌋.toNat)
          {((-j₁ + j₂ - j₃ : ℚ) : ℂ), ((j₂ - l₁ - l₃ : ℚ) : ℂ), ((-j₁ - l₂ - l₃ - 1 : ℚ) : ℂ),
            ((-j₃ - l₁ - l₂ - 1 : ℚ) : ℂ)}
          {((-j₁ + j₂ - l₁ - l₂ : ℚ) : ℂ), ((j₂ - j₃ - l₂ - l₃ : ℚ) : ℂ),
            ((-j₁ - j₃ - l₁ - l₃ - 1 : ℚ) : ℂ)} 1 := by
  sorry

/-! ### Single-term evaluations -/

/-- A Racah term of 34.4.2 vanishes below the summation range. -/
lemma w34_term6j_zero_of_lt {j₁ j₂ j₃ l₁ l₂ l₃ : ℚ} {s : ℕ} (h : (s : ℚ) < j₁ + j₂ + j₃) :
    racahTerm6j j₁ j₂ j₃ l₁ l₂ l₃ s = 0 := by
  unfold racahTerm6j
  rw [invFactQ_of_neg (x := (s : ℚ) - j₁ - j₂ - j₃) (by linarith)]
  ring

/-- A Racah term of 34.4.2 vanishes above the summation range. -/
lemma w34_term6j_zero_of_gt {j₁ j₂ j₃ l₁ l₂ l₃ : ℚ} {s : ℕ} (h : j₁ + j₂ + l₁ + l₂ < s) :
    racahTerm6j j₁ j₂ j₃ l₁ l₂ l₃ s = 0 := by
  unfold racahTerm6j
  rw [invFactQ_of_neg (x := j₁ + j₂ + l₁ + l₂ - s) (by linarith)]
  ring

/-- Single-term evaluation of 34.4.2 when `j₁ + j₂ + j₃ = j₁ + j₂ + l₁ + l₂ = n`. -/
lemma w34_wigner6j_single {j₁ j₂ j₃ l₁ l₂ l₃ : ℚ} (h : IsAdmissible6j j₁ j₂ j₃ l₁ l₂ l₃) (n : ℕ)
    (h₁ : j₁ + j₂ + j₃ = n) (h₂ : j₁ + j₂ + l₁ + l₂ = n) :
    wigner6j j₁ j₂ j₃ l₁ l₂ l₃ = (-1 : ℝ) ^ n *
      (triangleDelta j₁ j₂ j₃ * triangleDelta j₁ l₂ l₃ * triangleDelta l₁ j₂ l₃ *
        triangleDelta l₁ l₂ j₃ * ((n + 1).factorial : ℝ) * invFactQ (n - j₁ - l₂ - l₃) *
        invFactQ (n - l₁ - j₂ - l₃) * invFactQ (n - l₁ - l₂ - j₃) *
        invFactQ (j₂ + j₃ + l₂ + l₃ - n) * invFactQ (j₃ + j₁ + l₃ + l₁ - n)) := by
  unfold wigner6j
  simp only [h, ↓reduceIte]
  rw [h₂, Int.floor_natCast, Int.toNat_natCast, Finset.sum_eq_single n]
  · unfold racahTerm6j
    have e₁ : invFactQ ((n : ℚ) - j₁ - j₂ - j₃) = 1 := by
      rw [invFactQ_of_eq (n := 0) (by rw [← h₁]; simp; ring)]; simp
    have e₂ : invFactQ (j₁ + j₂ + l₁ + l₂ - (n : ℚ)) = 1 := by
      rw [invFactQ_of_eq (n := 0) (by rw [h₂]; simp)]; simp
    rw [e₁, e₂]
    ring
  · intro s _ hs
    rcases lt_or_gt_of_ne hs with hlt | hgt
    · exact w34_term6j_zero_of_lt (by rw [h₁]; exact_mod_cast hlt)
    · exact w34_term6j_zero_of_gt (by rw [h₂]; exact_mod_cast hgt)
  · intro hn; simp at hn

/-- `(1 + n)! = (1 + n) n!`. -/
lemma w34_factorial_one_add (n : ℕ) :
    ((1 + n).factorial : ℝ) = ((1 + n : ℕ) : ℝ) * (n.factorial : ℝ) := by
  rw [Nat.add_comm, Nat.factorial_succ]; push_cast; ring

/-- Close a cast equation. -/
macro "w34_nq6" : tactic => `(tactic| first | ring1 | (push_cast; ring1))

/-- Nonnegativity of products of factorials and reciprocal factorials. -/
macro "w34_nonneg" : tactic => `(tactic|
  repeat (first | apply mul_nonneg | exact w34_invFactQ_nonneg _ | positivity |
    (unfold factQ; positivity)))

/-- Rewrite the factorials of natural-number arguments. -/
macro "w34_casts" : tactic => `(tactic| (push_cast; ring_nf; simp only [w34_one_add_natCast,
  ← Nat.cast_add, factQ_natCast, invFactQ_natCast, w34_factQ_zero, w34_invFactQ_zero, mul_one,
  one_mul]))

/-- Replace the argument of a square root of a rational cast. -/
lemma q2w_sqrt_cast_eq {y : ℚ} {Y : ℝ} (h : (y : ℝ) = Y) : Real.sqrt (y : ℝ) = Real.sqrt Y := by
  rw [h]

/-- Two-term evaluation of 34.4.2 when `j₁ + j₂ + j₃ = n` and `j₁ + j₂ + l₁ + l₂ = n + 1`. -/
lemma q2w_wigner6j_two {j₁ j₂ j₃ l₁ l₂ l₃ : ℚ} (h : IsAdmissible6j j₁ j₂ j₃ l₁ l₂ l₃) (n : ℕ)
    (h₁ : j₁ + j₂ + j₃ = n) (h₂ : j₁ + j₂ + l₁ + l₂ = n + 1) :
    wigner6j j₁ j₂ j₃ l₁ l₂ l₃ =
      triangleDelta j₁ j₂ j₃ * triangleDelta j₁ l₂ l₃ * triangleDelta l₁ j₂ l₃ *
        triangleDelta l₁ l₂ j₃ *
        (racahTerm6j j₁ j₂ j₃ l₁ l₂ l₃ n + racahTerm6j j₁ j₂ j₃ l₁ l₂ l₃ (n + 1)) := by
  unfold wigner6j
  simp only [h, ↓reduceIte]
  rw [h₂, show ((n : ℚ) + 1) = ((n + 1 : ℕ) : ℚ) by push_cast; ring, Int.floor_natCast,
    Int.toNat_natCast, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_eq_zero (s := range n), zero_add]
  intro s hs
  simp only [mem_range] at hs
  exact w34_term6j_zero_of_lt (by rw [h₁]; exact_mod_cast hs)

/-! ## §34.5(i) Special cases

`J = j₁ + j₂ + j₃` (34.3.4); each formula assumes the triangle conditions of the symbol. -/

/-- DLMF 34.5.1: `{j₁ j₂ j₃; 0 j₃ j₂} = (-1)^J / ((2j₂+1)(2j₃+1))^{1/2}`. -/
@[dlmf 34.5.E1]
theorem wigner6j_zero {j₁ j₂ j₃ : ℚ} (h : IsTriad j₁ j₂ j₃) :
    wigner6j j₁ j₂ j₃ 0 j₃ j₂ =
      signPow (j₁ + j₂ + j₃) / Real.sqrt ((2 * (j₂ : ℝ) + 1) * (2 * j₃ + 1)) := by
  obtain ⟨⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩, ⟨a₃, ha₃⟩⟩ := h
  obtain rfl : j₁ = ((a₁ : ℚ) + a₂) / 2 := by linarith
  obtain rfl : j₂ = ((a₁ : ℚ) + a₃) / 2 := by linarith
  obtain rfl : j₃ = ((a₂ : ℚ) + a₃) / 2 := by linarith
  have hadm : IsAdmissible6j (((a₁ : ℚ) + a₂) / 2) (((a₁ : ℚ) + a₃) / 2) (((a₂ : ℚ) + a₃) / 2) 0
      (((a₂ : ℚ) + a₃) / 2) (((a₁ : ℚ) + a₃) / 2) :=
    ⟨⟨⟨a₁, by w34_nq6⟩, ⟨a₂, by w34_nq6⟩, ⟨a₃, by w34_nq6⟩⟩,
      ⟨⟨a₂, by w34_nq6⟩, ⟨a₁, by w34_nq6⟩, ⟨a₃, by w34_nq6⟩⟩,
      ⟨⟨0, by w34_nq6⟩, ⟨0, by w34_nq6⟩, ⟨a₁ + a₃, by w34_nq6⟩⟩,
      ⟨⟨0, by w34_nq6⟩, ⟨0, by w34_nq6⟩, ⟨a₂ + a₃, by w34_nq6⟩⟩⟩
  rw [w34_wigner6j_single hadm (a₁ + a₂ + a₃) (by push_cast; ring) (by push_cast; ring),
    signPow_of_eq (n := ((a₁ + a₂ + a₃ : ℕ) : ℤ)) (by push_cast; ring), zpow_natCast,
    div_eq_mul_inv ((-1 : ℝ) ^ (a₁ + a₂ + a₃)), ← Real.sqrt_inv, w34_delta_prod]
  congr 1
  simp only [mul_assoc]
  apply w34_sqrt_mul_eq
  · w34_nonneg
  · w34_nonneg
  · w34_casts
    simp only [Nat.add_assoc, w34_factorial_one_add]
    push_cast
    field_simp
    ring

/-- DLMF 34.5.2. -/
@[dlmf 34.5.E2]
theorem wigner6j_half_plus {j₁ j₂ j₃ : ℚ}
    (h : IsAdmissible6j j₁ j₂ j₃ (1 / 2) (j₃ - 1 / 2) (j₂ + 1 / 2)) :
    wigner6j j₁ j₂ j₃ (1 / 2) (j₃ - 1 / 2) (j₂ + 1 / 2) =
      signPow (j₁ + j₂ + j₃) * Real.sqrt (((j₁ + j₃ - j₂) * (j₁ + j₂ - j₃ + 1) /
        ((2 * j₂ + 1) * (2 * j₂ + 2) * (2 * j₃) * (2 * j₃ + 1)) : ℚ) : ℝ) := by
  have h0 := h
  obtain ⟨⟨⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩, ⟨a₃, ha₃⟩⟩, ⟨⟨b₁, hb₁⟩, ⟨b₂, hb₂⟩, ⟨b₃, hb₃⟩⟩, -, -⟩ := h0
  obtain rfl : j₁ = ((a₁ : ℚ) + a₂) / 2 := by linarith
  obtain rfl : j₂ = ((a₁ : ℚ) + a₃) / 2 := by linarith
  obtain rfl : j₃ = ((a₂ : ℚ) + a₃) / 2 := by linarith
  obtain ⟨c₂, rfl⟩ : ∃ c, a₂ = c + 1 := ⟨b₁, by
    have : (a₂ : ℚ) = b₁ + 1 := by linarith
    exact_mod_cast this⟩
  rw [w34_wigner6j_single h (a₁ + c₂ + a₃ + 1) (by push_cast; ring) (by push_cast; ring),
    signPow_of_eq (n := ((a₁ + c₂ + a₃ + 1 : ℕ) : ℤ)) (by push_cast; ring), zpow_natCast,
    w34_delta_prod]
  congr 1
  simp only [mul_assoc]
  apply w34_sqrt_mul_eq
  · w34_nonneg
  · w34_nonneg
  · q2w_casts
    q2w_fin

/-- DLMF 34.5.3. -/
@[dlmf 34.5.E3]
theorem wigner6j_half_minus {j₁ j₂ j₃ : ℚ}
    (h : IsAdmissible6j j₁ j₂ j₃ (1 / 2) (j₃ - 1 / 2) (j₂ - 1 / 2)) :
    wigner6j j₁ j₂ j₃ (1 / 2) (j₃ - 1 / 2) (j₂ - 1 / 2) =
      signPow (j₁ + j₂ + j₃) * Real.sqrt (((j₂ + j₃ - j₁) * (j₁ + j₂ + j₃ + 1) /
        ((2 * j₂) * (2 * j₂ + 1) * (2 * j₃) * (2 * j₃ + 1)) : ℚ) : ℝ) := by
  have h0 := h
  obtain ⟨⟨⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩, ⟨a₃, ha₃⟩⟩, ⟨⟨b₁, hb₁⟩, ⟨b₂, hb₂⟩, ⟨b₃, hb₃⟩⟩, -, -⟩ := h0
  obtain rfl : j₁ = ((a₁ : ℚ) + a₂) / 2 := by linarith
  obtain rfl : j₂ = ((a₁ : ℚ) + a₃) / 2 := by linarith
  obtain rfl : j₃ = ((a₂ : ℚ) + a₃) / 2 := by linarith
  obtain ⟨c₃, rfl⟩ : ∃ c, a₃ = c + 1 := ⟨b₃, by
    have : (a₃ : ℚ) = b₃ + 1 := by linarith
    exact_mod_cast this⟩
  rw [w34_wigner6j_single h (a₁ + a₂ + c₃ + 1) (by push_cast; ring) (by push_cast; ring),
    signPow_of_eq (n := ((a₁ + a₂ + c₃ + 1 : ℕ) : ℤ)) (by push_cast; ring), zpow_natCast,
    w34_delta_prod]
  congr 1
  simp only [mul_assoc]
  apply w34_sqrt_mul_eq
  · w34_nonneg
  · w34_nonneg
  · q2w_casts
    q2w_fin

/-- DLMF 34.5.4. -/
@[dlmf 34.5.E4]
theorem wigner6j_one_minus_minus {j₁ j₂ j₃ : ℚ}
    (h : IsAdmissible6j j₁ j₂ j₃ 1 (j₃ - 1) (j₂ - 1)) :
    wigner6j j₁ j₂ j₃ 1 (j₃ - 1) (j₂ - 1) =
      signPow (j₁ + j₂ + j₃) * Real.sqrt ((((j₁ + j₂ + j₃) * (j₁ + j₂ + j₃ + 1) *
        (j₁ + j₂ + j₃ - 2 * j₁) * (j₁ + j₂ + j₃ - 2 * j₁ - 1)) /
        ((2 * j₂ - 1) * (2 * j₂) * (2 * j₂ + 1) * (2 * j₃ - 1) * (2 * j₃) * (2 * j₃ + 1)) :
          ℚ) : ℝ) := by
  have h0 := h
  obtain ⟨⟨⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩, ⟨a₃, ha₃⟩⟩, ⟨⟨b₁, hb₁⟩, ⟨b₂, hb₂⟩, ⟨b₃, hb₃⟩⟩, -, -⟩ := h0
  obtain rfl : j₁ = ((a₁ : ℚ) + a₂) / 2 := by linarith
  obtain rfl : j₂ = ((a₁ : ℚ) + a₃) / 2 := by linarith
  obtain rfl : j₃ = ((a₂ : ℚ) + a₃) / 2 := by linarith
  obtain ⟨c₃, rfl⟩ : ∃ c, a₃ = c + 2 := ⟨b₃, by
    have : (a₃ : ℚ) = b₃ + 2 := by linarith
    exact_mod_cast this⟩
  rw [w34_wigner6j_single h (a₁ + a₂ + c₃ + 2) (by push_cast; ring) (by push_cast; ring),
    signPow_of_eq (n := ((a₁ + a₂ + c₃ + 2 : ℕ) : ℤ)) (by push_cast; ring), zpow_natCast,
    w34_delta_prod]
  congr 1
  simp only [mul_assoc]
  apply w34_sqrt_mul_eq
  · w34_nonneg
  · w34_nonneg
  · q2w_casts
    q2w_fin

/-- DLMF 34.5.5. -/
@[dlmf 34.5.E5]
theorem wigner6j_one_minus_zero {j₁ j₂ j₃ : ℚ}
    (h : IsAdmissible6j j₁ j₂ j₃ 1 (j₃ - 1) j₂) :
    wigner6j j₁ j₂ j₃ 1 (j₃ - 1) j₂ =
      signPow (j₁ + j₂ + j₃) * Real.sqrt (((2 * (j₁ + j₂ + j₃ + 1) * (j₁ + j₂ + j₃ - 2 * j₁) *
        (j₁ + j₂ + j₃ - 2 * j₂) * (j₁ + j₂ + j₃ - 2 * j₃ + 1)) /
        ((2 * j₂) * (2 * j₂ + 1) * (2 * j₂ + 2) * (2 * j₃ - 1) * (2 * j₃) * (2 * j₃ + 1)) :
          ℚ) : ℝ) := by
  have h0 := h
  obtain ⟨⟨⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩, ⟨a₃, ha₃⟩⟩, ⟨⟨b₁, hb₁⟩, ⟨b₂, hb₂⟩, ⟨b₃, hb₃⟩⟩, -, -⟩ := h0
  obtain rfl : j₁ = ((a₁ : ℚ) + a₂) / 2 := by linarith
  obtain rfl : j₂ = ((a₁ : ℚ) + a₃) / 2 := by linarith
  obtain rfl : j₃ = ((a₂ : ℚ) + a₃) / 2 := by linarith
  obtain ⟨c₂, rfl⟩ : ∃ c, a₂ = c + 1 := ⟨b₁, by
    have : (a₂ : ℚ) = b₁ + 1 := by linarith
    exact_mod_cast this⟩
  obtain ⟨c₃, rfl⟩ : ∃ c, a₃ = c + 1 := ⟨b₃, by
    have : (a₃ : ℚ) = b₃ + 1 := by linarith
    exact_mod_cast this⟩
  rw [w34_wigner6j_single h (a₁ + c₂ + c₃ + 2) (by push_cast; ring) (by push_cast; ring),
    signPow_of_eq (n := ((a₁ + c₂ + c₃ + 2 : ℕ) : ℤ)) (by push_cast; ring), zpow_natCast,
    w34_delta_prod]
  congr 1
  simp only [mul_assoc]
  apply w34_sqrt_mul_eq
  · w34_nonneg
  · w34_nonneg
  · q2w_casts
    q2w_fin

/-- DLMF 34.5.6. -/
@[dlmf 34.5.E6]
theorem wigner6j_one_minus_plus {j₁ j₂ j₃ : ℚ}
    (h : IsAdmissible6j j₁ j₂ j₃ 1 (j₃ - 1) (j₂ + 1)) :
    wigner6j j₁ j₂ j₃ 1 (j₃ - 1) (j₂ + 1) =
      signPow (j₁ + j₂ + j₃) * Real.sqrt ((((j₁ + j₂ + j₃ - 2 * j₂ - 1) *
        (j₁ + j₂ + j₃ - 2 * j₂) * (j₁ + j₂ + j₃ - 2 * j₃ + 1) * (j₁ + j₂ + j₃ - 2 * j₃ + 2)) /
        ((2 * j₂ + 1) * (2 * j₂ + 2) * (2 * j₂ + 3) * (2 * j₃ - 1) * (2 * j₃) * (2 * j₃ + 1)) :
          ℚ) : ℝ) := by
  have h0 := h
  obtain ⟨⟨⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩, ⟨a₃, ha₃⟩⟩, ⟨⟨b₁, hb₁⟩, ⟨b₂, hb₂⟩, ⟨b₃, hb₃⟩⟩, -, -⟩ := h0
  obtain rfl : j₁ = ((a₁ : ℚ) + a₂) / 2 := by linarith
  obtain rfl : j₂ = ((a₁ : ℚ) + a₃) / 2 := by linarith
  obtain rfl : j₃ = ((a₂ : ℚ) + a₃) / 2 := by linarith
  obtain ⟨c₂, rfl⟩ : ∃ c, a₂ = c + 2 := ⟨b₁, by
    have : (a₂ : ℚ) = b₁ + 2 := by linarith
    exact_mod_cast this⟩
  rw [w34_wigner6j_single h (a₁ + c₂ + a₃ + 2) (by push_cast; ring) (by push_cast; ring),
    signPow_of_eq (n := ((a₁ + c₂ + a₃ + 2 : ℕ) : ℤ)) (by push_cast; ring), zpow_natCast,
    w34_delta_prod]
  congr 1
  simp only [mul_assoc]
  apply w34_sqrt_mul_eq
  · w34_nonneg
  · w34_nonneg
  · q2w_casts
    q2w_fin

/-- DLMF 34.5.7. -/
@[dlmf 34.5.E7]
theorem wigner6j_one_zero_zero {j₁ j₂ j₃ : ℚ} (h : IsAdmissible6j j₁ j₂ j₃ 1 j₃ j₂) :
    wigner6j j₁ j₂ j₃ 1 j₃ j₂ =
      signPow (j₁ + j₂ + j₃ + 1) *
        (2 * ((j₂ * (j₂ + 1) + j₃ * (j₃ + 1) - j₁ * (j₁ + 1) : ℚ) : ℝ)) /
        Real.sqrt (((2 * j₂) * (2 * j₂ + 1) * (2 * j₂ + 2) * (2 * j₃) * (2 * j₃ + 1) *
          (2 * j₃ + 2) : ℚ) : ℝ) := by
  have h0 := h
  obtain ⟨⟨⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩, ⟨a₃, ha₃⟩⟩, -, ⟨-, -, ⟨p, hp⟩⟩, ⟨-, -, ⟨q, hq⟩⟩⟩ := h0
  obtain rfl : j₁ = ((a₁ : ℚ) + a₂) / 2 := by linarith
  obtain rfl : j₂ = ((a₁ : ℚ) + a₃) / 2 := by linarith
  obtain rfl : j₃ = ((a₂ : ℚ) + a₃) / 2 := by linarith
  rw [q2w_wigner6j_two h (a₁ + a₂ + a₃) (by push_cast; ring) (by push_cast; ring),
    signPow_of_eq (n := ((a₁ + a₂ + a₃ + 1 : ℕ) : ℤ)) (by push_cast; ring), zpow_natCast,
    w34_delta_prod]
  rcases Nat.eq_zero_or_eq_succ_pred a₃ with h3 | h3
  · subst h3
    obtain ⟨d, rfl⟩ : ∃ d, a₁ = d + 1 := ⟨p, by
      have : (a₁ : ℚ) = p + 1 := by push_cast at hp; linarith
      exact_mod_cast this⟩
    obtain ⟨e, rfl⟩ : ∃ e, a₂ = e + 1 := ⟨q, by
      have : (a₂ : ℚ) = q + 1 := by push_cast at hq; linarith
      exact_mod_cast this⟩
    have hR : (0 : ℝ) ≤ ((1 + d).factorial * (1 + e).factorial / (3 + d + e).factorial : ℝ) :=
      by positivity
    have hY : (0 : ℝ) ≤ ((d + 1 : ℝ)) * (d + 2) * (d + 3) * (e + 1) * (e + 2) * (e + 3) :=
      by positivity
    rw [q2w_sqrt_eq_div hR hY, q2w_sqrt_cast_eq]
    · rw [div_mul_eq_mul_div]
      congr 1
      unfold racahTerm6j
      q2w_casts
      q2w_fin
    · push_cast; ring
    · q2w_casts
      q2w_fin
  · obtain ⟨c, rfl⟩ : ∃ c, a₃ = c + 1 := ⟨_, h3⟩
    have hR : (0 : ℝ) ≤ (a₁.factorial * a₂.factorial * (1 + c).factorial /
        (2 + a₁ + a₂ + c).factorial : ℝ) := by positivity
    have hY : (0 : ℝ) ≤ ((a₁ + c + 1 : ℝ)) * (a₁ + c + 2) * (a₁ + c + 3) *
        (a₂ + c + 1) * (a₂ + c + 2) * (a₂ + c + 3) := by positivity
    rw [q2w_sqrt_eq_div hR hY, q2w_sqrt_cast_eq]
    · rw [div_mul_eq_mul_div]
      congr 1
      unfold racahTerm6j
      q2w_casts
      q2w_fin
    · push_cast; ring
    · q2w_casts
      q2w_fin

/-! ## §34.5(ii) Symmetry -/

/-- DLMF 34.5.8, first equality: interchange of two columns. -/
@[dlmf 34.5.E8]
theorem wigner6j_swap_columns (j₁ j₂ j₃ l₁ l₂ l₃ : ℚ) :
    wigner6j j₁ j₂ j₃ l₁ l₂ l₃ = wigner6j j₂ j₁ j₃ l₂ l₁ l₃ := by
  have hiff : IsAdmissible6j j₁ j₂ j₃ l₁ l₂ l₃ ↔
      IsAdmissible6j j₂ j₁ j₃ l₂ l₁ l₃ := by
    rw [w34_admissible6j_iff, w34_admissible6j_iff]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> w34_pick
    · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> w34_pick
  by_cases h : IsAdmissible6j j₁ j₂ j₃ l₁ l₂ l₃
  · have h' := hiff.mp h
    unfold wigner6j
    simp only [h, h', ↓reduceIte]
    rw [w34_delta_prod, w34_delta_prod]
    unfold racahTerm6j
    ring_nf
    congr 1
    exact Finset.sum_congr rfl fun x _ => by ring
  · rw [wigner6j_of_not h, wigner6j_of_not (mt hiff.mpr h)]

/-- DLMF 34.5.8, second equality: interchange of the upper and lower arguments in two
columns. -/
@[dlmf 34.5.E8]
theorem wigner6j_flip (j₁ j₂ j₃ l₁ l₂ l₃ : ℚ) :
    wigner6j j₁ j₂ j₃ l₁ l₂ l₃ = wigner6j j₁ l₂ l₃ l₁ j₂ j₃ := by
  have hiff : IsAdmissible6j j₁ j₂ j₃ l₁ l₂ l₃ ↔
      IsAdmissible6j j₁ l₂ l₃ l₁ j₂ j₃ := by
    rw [w34_admissible6j_iff, w34_admissible6j_iff]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> w34_pick
    · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> w34_pick
  by_cases h : IsAdmissible6j j₁ j₂ j₃ l₁ l₂ l₃
  · have h' := hiff.mp h
    unfold wigner6j
    simp only [h, h', ↓reduceIte]
    rw [w34_delta_prod, w34_delta_prod]
    unfold racahTerm6j
    ring_nf
    congr 1
    exact Finset.sum_congr rfl fun x _ => by ring
  · rw [wigner6j_of_not h, wigner6j_of_not (mt hiff.mpr h)]

/-- DLMF 34.5.9: a Regge symmetry. -/
@[dlmf 34.5.E9]
theorem wigner6j_regge₁ (j₁ j₂ j₃ l₁ l₂ l₃ : ℚ) :
    wigner6j j₁ j₂ j₃ l₁ l₂ l₃ =
      wigner6j j₁ ((j₂ + l₂ + j₃ - l₃) / 2) ((j₂ - l₂ + j₃ + l₃) / 2)
        l₁ ((j₂ + l₂ - j₃ + l₃) / 2) ((-j₂ + l₂ + j₃ + l₃) / 2) := by
  have hiff : IsAdmissible6j j₁ j₂ j₃ l₁ l₂ l₃ ↔
      IsAdmissible6j j₁ ((j₂ + l₂ + j₃ - l₃) / 2) ((j₂ - l₂ + j₃ + l₃) / 2)
        l₁ ((j₂ + l₂ - j₃ + l₃) / 2) ((-j₂ + l₂ + j₃ + l₃) / 2) := by
    rw [w34_admissible6j_iff, w34_admissible6j_iff]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> w34_pick
    · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> w34_pick
  by_cases h : IsAdmissible6j j₁ j₂ j₃ l₁ l₂ l₃
  · have h' := hiff.mp h
    unfold wigner6j
    simp only [h, h', ↓reduceIte]
    rw [w34_delta_prod, w34_delta_prod]
    unfold racahTerm6j
    ring_nf
    congr 1
    exact Finset.sum_congr rfl fun x _ => by ring
  · rw [wigner6j_of_not h, wigner6j_of_not (mt hiff.mpr h)]

/-- DLMF 34.5.10: a Regge symmetry. -/
@[dlmf 34.5.E10]
theorem wigner6j_regge₂ (j₁ j₂ j₃ l₁ l₂ l₃ : ℚ) :
    wigner6j j₁ j₂ j₃ l₁ l₂ l₃ =
      wigner6j ((j₂ + l₂ + j₃ - l₃) / 2) ((j₁ - l₁ + j₃ + l₃) / 2) ((j₁ + l₁ + j₂ - l₂) / 2)
        ((j₂ + l₂ - j₃ + l₃) / 2) ((-j₁ + l₁ + j₃ + l₃) / 2) ((j₁ + l₁ - j₂ + l₂) / 2) := by
  have hiff : IsAdmissible6j j₁ j₂ j₃ l₁ l₂ l₃ ↔
      IsAdmissible6j ((j₂ + l₂ + j₃ - l₃) / 2) ((j₁ - l₁ + j₃ + l₃) / 2) ((j₁ + l₁ + j₂ - l₂) / 2)
        ((j₂ + l₂ - j₃ + l₃) / 2) ((-j₁ + l₁ + j₃ + l₃) / 2) ((j₁ + l₁ - j₂ + l₂) / 2) := by
    rw [w34_admissible6j_iff, w34_admissible6j_iff]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> w34_pick
    · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> w34_pick
  by_cases h : IsAdmissible6j j₁ j₂ j₃ l₁ l₂ l₃
  · have h' := hiff.mp h
    unfold wigner6j
    simp only [h, h', ↓reduceIte]
    rw [w34_delta_prod, w34_delta_prod,
      w34_sum6j_extend h (⌊j₁ + j₂ + l₁ + l₂⌋.toNat + ⌊j₂ + j₃ + l₂ + l₃⌋.toNat) (by omega),
      w34_sum6j_extend h' (⌊j₁ + j₂ + l₁ + l₂⌋.toNat + ⌊j₂ + j₃ + l₂ + l₃⌋.toNat) ?_]
    · unfold racahTerm6j
      ring_nf
      congr 1
      exact Finset.sum_congr rfl fun x _ => by ring
    · rw [show (j₂ + l₂ + j₃ - l₃) / 2 + (j₁ - l₁ + j₃ + l₃) / 2 + (j₂ + l₂ - j₃ + l₃) / 2 +
          (-j₁ + l₁ + j₃ + l₃) / 2 = j₂ + j₃ + l₂ + l₃ by ring]
      omega
  · rw [wigner6j_of_not h, wigner6j_of_not (mt hiff.mpr h)]

/-- DLMF 34.5.8: interchange of the second and third columns of a `6j` symbol (a helper; with
`wigner6j_swap_columns` it gives all column permutations). -/
theorem q2w_wigner6j_swap23 (j₁ j₂ j₃ l₁ l₂ l₃ : ℚ) :
    wigner6j j₁ j₂ j₃ l₁ l₂ l₃ = wigner6j j₁ j₃ j₂ l₁ l₃ l₂ := by
  have hiff : IsAdmissible6j j₁ j₂ j₃ l₁ l₂ l₃ ↔ IsAdmissible6j j₁ j₃ j₂ l₁ l₃ l₂ := by
    rw [w34_admissible6j_iff, w34_admissible6j_iff]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> w34_pick
    · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> w34_pick
  by_cases h : IsAdmissible6j j₁ j₂ j₃ l₁ l₂ l₃
  · have h' := hiff.mp h
    unfold wigner6j
    simp only [h, h', ↓reduceIte]
    rw [w34_delta_prod, w34_delta_prod,
      w34_sum6j_extend h (⌊j₁ + j₂ + l₁ + l₂⌋.toNat + ⌊j₁ + j₃ + l₁ + l₃⌋.toNat) (by omega),
      w34_sum6j_extend h' (⌊j₁ + j₂ + l₁ + l₂⌋.toNat + ⌊j₁ + j₃ + l₁ + l₃⌋.toNat) (by omega)]
    unfold racahTerm6j
    ring_nf
    congr 1
    exact Finset.sum_congr rfl fun x _ => by ring
  · rw [wigner6j_of_not h, wigner6j_of_not (mt hiff.mpr h)]

/-- DLMF 34.5.8: interchange of the upper and lower arguments in the first two columns. -/
theorem q2w_wigner6j_flip12 (j₁ j₂ j₃ l₁ l₂ l₃ : ℚ) :
    wigner6j j₁ j₂ j₃ l₁ l₂ l₃ = wigner6j l₁ l₂ j₃ j₁ j₂ l₃ := by
  rw [q2w_wigner6j_swap23 j₁ j₂ j₃ l₁ l₂ l₃, wigner6j_swap_columns j₁ j₃ j₂ l₁ l₃ l₂,
    wigner6j_flip j₃ j₁ j₂ l₃ l₁ l₂, wigner6j_swap_columns j₃ l₁ l₂ l₃ j₁ j₂,
    q2w_wigner6j_swap23 l₁ j₃ l₂ j₁ l₃ j₂]

/-! ## §34.5(iii) Recursion relations -/

/-- DLMF 34.5.11–34.5.13: with `Jᵣ = jᵣ(jᵣ+1)`, `Lᵣ = lᵣ(lᵣ+1)` (34.5.12) and `E(j)` of
34.5.13 (`sixJRecursionE`),
`(2j₁+1)((J₃+J₂-J₁)(L₃+L₂-J₁) - 2(J₃L₃+J₂L₂-J₁L₁)) {j₁ j₂ j₃; l₁ l₂ l₃}`
`= j₁ E(j₁+1) {j₁+1 j₂ j₃; l₁ l₂ l₃} + (j₁+1) E(j₁) {j₁-1 j₂ j₃; l₁ l₂ l₃}`,
assuming the triangle conditions of `{j₁ j₂ j₃; l₁ l₂ l₃}`. -/
@[dlmf 34.5.E11, dlmf 34.5.E12]
theorem wigner6j_recursion {j₁ j₂ j₃ l₁ l₂ l₃ : ℚ} (h : IsAdmissible6j j₁ j₂ j₃ l₁ l₂ l₃) :
    (((2 * j₁ + 1) * ((j₃ * (j₃ + 1) + j₂ * (j₂ + 1) - j₁ * (j₁ + 1)) *
        (l₃ * (l₃ + 1) + l₂ * (l₂ + 1) - j₁ * (j₁ + 1)) -
        2 * (j₃ * (j₃ + 1) * (l₃ * (l₃ + 1)) + j₂ * (j₂ + 1) * (l₂ * (l₂ + 1)) -
          j₁ * (j₁ + 1) * (l₁ * (l₁ + 1)))) : ℚ) : ℝ) * wigner6j j₁ j₂ j₃ l₁ l₂ l₃ =
      (j₁ : ℝ) * sixJRecursionE j₂ j₃ l₂ l₃ (j₁ + 1) * wigner6j (j₁ + 1) j₂ j₃ l₁ l₂ l₃ +
        ((j₁ + 1 : ℚ) : ℝ) * sixJRecursionE j₂ j₃ l₂ l₃ j₁ * wigner6j (j₁ - 1) j₂ j₃ l₁ l₂ l₃ := by
  sorry

/-! ## §34.5(iv) Orthogonality -/

/-- DLMF 34.5.14: `∑_{j₃} (2j₃+1)(2l₃+1) {j₁ j₂ j₃; l₁ l₂ l₃}{j₁ j₂ j₃; l₁ l₂ l₃'} = δ_{l₃,l₃'}`,
for `l₃` admissible (the triads `(j₁ l₂ l₃)` and `(l₁ j₂ l₃)` satisfy the triangle
conditions). -/
@[dlmf 34.5.E14]
theorem wigner6j_orthogonality {j₁ j₂ l₁ l₂ l₃ : ℚ} (h₁ : IsTriad j₁ l₂ l₃)
    (h₂ : IsTriad l₁ j₂ l₃) (l₃' : ℚ) :
    ∑ j₃ ∈ halfIntegersUpTo (j₁ + j₂),
        (2 * (j₃ : ℝ) + 1) * (2 * (l₃ : ℝ) + 1) * wigner6j j₁ j₂ j₃ l₁ l₂ l₃ *
          wigner6j j₁ j₂ j₃ l₁ l₂ l₃' =
      if l₃ = l₃' then 1 else 0 := by
  sorry

/-! ## §34.5(vi) Sums -/

/-- DLMF 34.5.15: the sum rule
`∑_j (-1)^{j+j'+j''} (2j+1) {j₁ j₂ j; j₃ j₄ j'}{j₁ j₂ j; j₄ j₃ j''} = {j₁ j₄ j'; j₂ j₃ j''}`. -/
@[dlmf 34.5.E15]
theorem wigner6j_sum_rule (j₁ j₂ j₃ j₄ j' j'' : ℚ) :
    ∑ j ∈ halfIntegersUpTo (j₁ + j₂),
        signPow (j + j' + j'') * (2 * (j : ℝ) + 1) * wigner6j j₁ j₂ j j₃ j₄ j' *
          wigner6j j₁ j₂ j j₄ j₃ j'' =
      wigner6j j₁ j₄ j' j₂ j₃ j'' := by
  sorry

/-- DLMF 34.5.16: the Biedenharn–Elliott sum rule
`(-1)^{j₁+j₂+j₃+j₁'+j₂'+l₁+l₂} {j₁ j₂ j₃; l₁ l₂ l₃}{j₁' j₂' j₃; l₁ l₂ l₃'}`
`= ∑_j (-1)^{l₃+l₃'+j} (2j+1) {j₁ j₁' j; j₂' j₂ j₃}{l₃ l₃' j; j₁' j₁ l₂}{l₃ l₃' j; j₂' j₂ l₁}`. -/
@[dlmf 34.5.E16]
theorem wigner6j_biedenharn_elliott (j₁ j₂ j₃ l₁ l₂ l₃ j₁' j₂' l₃' : ℚ) :
    signPow (j₁ + j₂ + j₃ + j₁' + j₂' + l₁ + l₂) * wigner6j j₁ j₂ j₃ l₁ l₂ l₃ *
        wigner6j j₁' j₂' j₃ l₁ l₂ l₃' =
      ∑ j ∈ halfIntegersUpTo (j₁ + j₁'),
        signPow (l₃ + l₃' + j) * (2 * (j : ℝ) + 1) * wigner6j j₁ j₁' j j₂' j₂ j₃ *
          wigner6j l₃ l₃' j j₁' j₁ l₂ * wigner6j l₃ l₃' j j₂' j₂ l₁ := by
  sorry

/-- DLMF 34.5.17: `∑_j (2j+1) {j₁ j₂ j; j₁ j₂ j'} = (-1)^{2(j₁+j₂)}`, for `(j₁ j₂ j')` a
triad. -/
@[dlmf 34.5.E17]
theorem wigner6j_sum_17 {j₁ j₂ j' : ℚ} (h : IsTriad j₁ j₂ j') :
    ∑ j ∈ halfIntegersUpTo (j₁ + j₂), (2 * (j : ℝ) + 1) * wigner6j j₁ j₂ j j₁ j₂ j' =
      signPow (2 * (j₁ + j₂)) := by
  sorry

/-- DLMF 34.5.18: `∑_j (-1)^{j₁+j₂+j} (2j+1) {j₁ j₂ j; j₂ j₁ j'}`
`= ((2j₁+1)(2j₂+1))^{1/2} δ_{j',0}`, for `(j₁ j₁ j')` and `(j₂ j₂ j')` triads. -/
@[dlmf 34.5.E18]
theorem wigner6j_sum_18 {j₁ j₂ j' : ℚ} (h₁ : IsTriad j₁ j₁ j') (h₂ : IsTriad j₂ j₂ j') :
    ∑ j ∈ halfIntegersUpTo (j₁ + j₂),
        signPow (j₁ + j₂ + j) * (2 * (j : ℝ) + 1) * wigner6j j₁ j₂ j j₂ j₁ j' =
      if j' = 0 then Real.sqrt ((2 * (j₁ : ℝ) + 1) * (2 * j₂ + 1)) else 0 := by
  sorry

/-- DLMF 34.5.19: `∑_l {j₁ j₂ l; j₂ j₁ j} = 0` when `2μ - j` is odd, `μ = min(j₁, j₂)`. -/
@[dlmf 34.5.E19]
theorem wigner6j_sum_19 {j₁ j₂ j : ℚ} (h₁ : IsTriad j₁ j₁ j) (h₂ : IsTriad j₂ j₂ j) (k : ℕ)
    (hodd : 2 * min j₁ j₂ - j = 2 * k + 1) :
    ∑ l ∈ halfIntegersUpTo (j₁ + j₂), wigner6j j₁ j₂ l j₂ j₁ j = 0 := by
  sorry

/-- DLMF 34.5.20: `∑_l (-1)^{l+j} {j₁ j₂ l; j₁ j₂ j} = (-1)^{2μ} / (2j+1)`,
`μ = min(j₁, j₂)`, for `(j₁ j₂ j)` a triad. -/
@[dlmf 34.5.E20]
theorem wigner6j_sum_20 {j₁ j₂ j : ℚ} (h : IsTriad j₁ j₂ j) :
    ∑ l ∈ halfIntegersUpTo (j₁ + j₂), signPow (l + j) * wigner6j j₁ j₂ l j₁ j₂ j =
      signPow (2 * min j₁ j₂) / (2 * (j : ℝ) + 1) := by
  sorry

/-- DLMF 34.5.21: for `j₂ ≤ j₁`, `∑_l (-1)^{l+j+j₁+j₂} {j₁ j₂ l; j₂ j₁ j}`
`= (2j+1)⁻¹ ((2j₁-j)!(2j₂+j+1)! / ((2j₂-j)!(2j₁+j+1)!))^{1/2}`. -/
@[dlmf 34.5.E21]
theorem wigner6j_sum_21 {j₁ j₂ j : ℚ} (h₁ : IsTriad j₁ j₁ j) (h₂ : IsTriad j₂ j₂ j)
    (h : j₂ ≤ j₁) :
    ∑ l ∈ halfIntegersUpTo (j₁ + j₂), signPow (l + j + j₁ + j₂) * wigner6j j₁ j₂ l j₂ j₁ j =
      Real.sqrt (factQ (2 * j₁ - j) * factQ (2 * j₂ + j + 1) /
        (factQ (2 * j₂ - j) * factQ (2 * j₁ + j + 1))) / (2 * (j : ℝ) + 1) := by
  sorry

/-- DLMF 34.5.22: for `j₂ < j₁`, `∑_l (-1)^{l+j+j₁+j₂} (l(l+1))⁻¹ {j₁ j₂ l; j₂ j₁ j}`
`= (j₁(j₁+1) - j₂(j₂+1))⁻¹ ((2j₁-j)!(2j₂+j+1)! / ((2j₂-j)!(2j₁+j+1)!))^{1/2}`
(the summands have `l ≥ j₁ - j₂ > 0`). -/
@[dlmf 34.5.E22]
theorem wigner6j_sum_22 {j₁ j₂ j : ℚ} (h₁ : IsTriad j₁ j₁ j) (h₂ : IsTriad j₂ j₂ j)
    (h : j₂ < j₁) :
    ∑ l ∈ halfIntegersUpTo (j₁ + j₂),
        signPow (l + j + j₁ + j₂) / ((l : ℝ) * (l + 1)) * wigner6j j₁ j₂ l j₂ j₁ j =
      Real.sqrt (factQ (2 * j₁ - j) * factQ (2 * j₂ + j + 1) /
        (factQ (2 * j₂ - j) * factQ (2 * j₁ + j + 1))) /
        ((j₁ : ℝ) * (j₁ + 1) - j₂ * (j₂ + 1)) := by
  sorry

/-- DLMF 34.5.23: `(j₁ j₂ j₃; m₁ m₂ m₃){j₁ j₂ j₃; l₁ l₂ l₃}`
`= ∑_{m'} (-1)^{l₁+l₂+l₃+m₁'+m₂'+m₃'} (j₁ l₂ l₃; m₁ m₂' -m₃')(l₁ j₂ l₃; -m₁' m₂ m₃')`
`(l₁ l₂ j₃; m₁' -m₂' m₃)`, an alternative definition of the `6j` symbol. -/
@[dlmf 34.5.E23]
theorem wigner3j_mul_wigner6j (j₁ j₂ j₃ l₁ l₂ l₃ m₁ m₂ m₃ : ℚ) :
    wigner3j j₁ j₂ j₃ m₁ m₂ m₃ * wigner6j j₁ j₂ j₃ l₁ l₂ l₃ =
      ∑ m₁' ∈ projections l₁, ∑ m₂' ∈ projections l₂, ∑ m₃' ∈ projections l₃,
        signPow (l₁ + l₂ + l₃ + m₁' + m₂' + m₃') * wigner3j j₁ l₂ l₃ m₁ m₂' (-m₃') *
          wigner3j l₁ j₂ l₃ (-m₁') m₂ m₃' * wigner3j l₁ l₂ j₃ m₁' (-m₂') m₃ := by
  sorry

/-! ## §34.10 Zeros -/

/-- DLMF §34.10: the `6j` symbol vanishes when one of the four triads violates the triangle
conditions (trivial zeros). -/
@[dlmf 34.10]
theorem wigner6j_eq_zero_of_not {j₁ j₂ j₃ l₁ l₂ l₃ : ℚ}
    (h : ¬ (IsTriad j₁ j₂ j₃ ∧ IsTriad j₁ l₂ l₃ ∧ IsTriad l₁ j₂ l₃ ∧ IsTriad l₁ l₂ j₃)) :
    wigner6j j₁ j₂ j₃ l₁ l₂ l₃ = 0 :=
  wigner6j_of_not h

end DLMF.WignerSymbols
