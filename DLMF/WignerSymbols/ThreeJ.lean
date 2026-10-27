/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.WignerSymbols.Basic
public import DLMF.WignerSymbols.Q2wHelpers
public import DLMF.GeneralizedHypergeometric.Basic
public import Mathlib.Algebra.Order.Ring.Star

/-!
# The `3j` symbol: DLMF §§34.2–34.3 and §34.10

Statements of DLMF §34.2 (the triangle conditions and the `₃F₂` form 34.2.6) and §34.3
(special cases, symmetry, recursion relations and orthogonality) for `wigner3j`, and the
trivial zeros of §34.10. The relations to Legendre polynomials and spherical harmonics
(§34.3(vii)) are in `DLMF.WignerSymbols.ThreeJLegendre`.

Since `wigner3j` is `0` outside the admissible range (34.2.1–34.2.3), the symmetry relations
34.3.8–34.3.12 and the recursion relations 34.3.13–34.3.15 are stated for all rational
arguments; for the recursions this is stronger than DLMF, which assumes the triangle
conditions for every symbol (checked numerically with exact arithmetic, see the ledger).
Square roots are `Real.sqrt`, which is `0` at negative arguments; the coefficients of the
recursions vanish exactly where a symbol leaves the admissible range.
-/

@[expose] public noncomputable section

open Finset

namespace DLMF.WignerSymbols

/-! ## Helpers: Racah's sum in symmetric form -/

/-- Shifting all arguments of `w34_S` by an integer `t` gives the sign `(-1)^t`. -/
lemma w34_S_shift (x₁ x₂ x₃ y₁ y₂ y₃ t : ℚ) (n : ℤ) (ht : t = n) :
    w34_S (x₁ + t) (x₂ + t) (x₃ + t) (y₁ + t) (y₂ + t) (y₃ + t) =
      (-1 : ℝ) ^ n * w34_S x₁ x₂ x₃ y₁ y₂ y₃ := by
  unfold w34_S
  rw [← finsum_comp_equiv (Equiv.addRight n), mul_finsum]
  refine finsum_congr fun s => ?_
  simp only [Equiv.coe_addRight, Int.cast_add, ← ht]
  rw [zpow_add₀ (by norm_num)]
  ring_nf

/-- `w34_S` is invariant under `(x, y) ↦ (-y, -x)` (substitute `s ↦ -s`). -/
lemma w34_S_neg (x₁ x₂ x₃ y₁ y₂ y₃ : ℚ) :
    w34_S x₁ x₂ x₃ y₁ y₂ y₃ = w34_S (-y₁) (-y₂) (-y₃) (-x₁) (-x₂) (-x₃) := by
  unfold w34_S
  rw [← finsum_comp_equiv (Equiv.neg ℤ)]
  refine finsum_congr fun s => ?_
  simp only [Equiv.neg_apply, Int.cast_neg, zpow_neg, ← inv_zpow, inv_neg, inv_one]
  ring_nf

/-- `w34_S` is symmetric in the `x` and in the `y` arguments. -/
lemma w34_S_swap_x12 (x₁ x₂ x₃ y₁ y₂ y₃ : ℚ) :
    w34_S x₁ x₂ x₃ y₁ y₂ y₃ = w34_S x₂ x₁ x₃ y₁ y₂ y₃ :=
  finsum_congr fun _ => by ring
/-- Symmetry of the symmetric Racah sum in `x₂ ↔ x₃`. -/
lemma w34_S_swap_x23 (x₁ x₂ x₃ y₁ y₂ y₃ : ℚ) :
    w34_S x₁ x₂ x₃ y₁ y₂ y₃ = w34_S x₁ x₃ x₂ y₁ y₂ y₃ :=
  finsum_congr fun _ => by ring
/-- Symmetry of the symmetric Racah sum in `y₁ ↔ y₂`. -/
lemma w34_S_swap_y12 (x₁ x₂ x₃ y₁ y₂ y₃ : ℚ) :
    w34_S x₁ x₂ x₃ y₁ y₂ y₃ = w34_S x₁ x₂ x₃ y₂ y₁ y₃ :=
  finsum_congr fun _ => by ring
/-- Symmetry of the symmetric Racah sum in `y₂ ↔ y₃`. -/
lemma w34_S_swap_y23 (x₁ x₂ x₃ y₁ y₂ y₃ : ℚ) :
    w34_S x₁ x₂ x₃ y₁ y₂ y₃ = w34_S x₁ x₂ x₃ y₁ y₃ y₂ :=
  finsum_congr fun _ => by ring

/-- The finite sum of 34.2.4 as `w34_S`. -/
lemma w34_sum3j_eq_S {j₁ j₂ j₃ m₁ m₂ : ℚ} (hA : IsNatQ (j₁ + j₂ - j₃)) :
    ∑ s ∈ range (⌊j₁ + j₂ - j₃⌋.toNat + 1), racahTerm3j j₁ j₂ j₃ m₁ m₂ s =
      w34_S (j₁ + j₂ - j₃) (j₁ - m₁) (j₂ + m₂) 0 (j₂ - j₃ - m₁) (j₁ - j₃ + m₂) := by
  unfold w34_S
  rw [finsum_eq_sum_of_support_subset _
    (s := (range (⌊j₁ + j₂ - j₃⌋.toNat + 1)).map Nat.castEmbedding) ?_, Finset.sum_map]
  · refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Nat.castEmbedding_apply, Int.cast_natCast, zpow_natCast, sub_zero]
    unfold racahTerm3j
    ring_nf
  · intro s hs
    simp only [Function.mem_support] at hs
    have h1 : invFactQ ((s : ℚ) - 0) ≠ 0 := fun h0 => hs (by rw [h0]; ring)
    have h2 : invFactQ (j₁ + j₂ - j₃ - s) ≠ 0 := fun h0 => hs (by rw [h0]; ring)
    rw [Ne, invFactQ_eq_zero_iff_neg, not_lt] at h1 h2
    simp only [coe_map, Nat.castEmbedding_apply, coe_range, Set.mem_image, Set.mem_Iio]
    refine ⟨s.toNat, ?_, Int.toNat_of_nonneg (by exact_mod_cast (by linarith : (0 : ℚ) ≤ s))⟩
    have : (s : ℚ) ≤ ((⌊j₁ + j₂ - j₃⌋.toNat : ℕ) : ℚ) := by rw [hA.floor_toNat]; linarith
    have h3 : s ≤ (⌊j₁ + j₂ - j₃⌋.toNat : ℤ) := by exact_mod_cast this
    omega

/-- Cyclic permutations of the `x` and of the `y` arguments of `w34_S`. -/
lemma w34_S_cycle_x (x₁ x₂ x₃ y₁ y₂ y₃ : ℚ) :
    w34_S x₁ x₂ x₃ y₁ y₂ y₃ = w34_S x₂ x₃ x₁ y₁ y₂ y₃ :=
  finsum_congr fun _ => by ring
/-- Cyclic symmetry of the symmetric Racah sum in the `y` arguments. -/
lemma w34_S_cycle_y (x₁ x₂ x₃ y₁ y₂ y₃ : ℚ) :
    w34_S x₁ x₂ x₃ y₁ y₂ y₃ = w34_S x₁ x₂ x₃ y₂ y₃ y₁ :=
  finsum_congr fun _ => by ring

/-- Integer powers of `-1` with exponents of the same parity. -/
lemma w34_neg_one_zpow_eq {A B : ℤ} (k : ℤ) (h : A = B + 2 * k) :
    (-1 : ℝ) ^ A = (-1 : ℝ) ^ B := by
  rw [h, zpow_add₀ (by norm_num), zpow_mul]
  norm_num

set_option hygiene false in
/-- Close `IsNatQ e` by one of the hypotheses `h1`, …, `h9` up to `ring`. -/
macro "w34_pick9" : tactic => `(tactic| first
  | (apply IsNatQ.of_eq h1; ring1) | (apply IsNatQ.of_eq h2; ring1)
  | (apply IsNatQ.of_eq h3; ring1) | (apply IsNatQ.of_eq h4; ring1)
  | (apply IsNatQ.of_eq h5; ring1) | (apply IsNatQ.of_eq h6; ring1)
  | (apply IsNatQ.of_eq h7; ring1) | (apply IsNatQ.of_eq h8; ring1)
  | (apply IsNatQ.of_eq h9; ring1))

/-- Racah's formula with the prefactor as one square root and the sum in symmetric form. -/
lemma w34_wigner3j_eq {j₁ j₂ j₃ m₁ m₂ m₃ : ℚ} (h : IsAdmissible3j j₁ j₂ j₃ m₁ m₂ m₃) :
    wigner3j j₁ j₂ j₃ m₁ m₂ m₃ =
      signPow (j₁ - j₂ - m₃) *
        Real.sqrt (factQ (j₁ + j₂ - j₃) * factQ (j₁ - j₂ + j₃) * factQ (-j₁ + j₂ + j₃) /
          factQ (j₁ + j₂ + j₃ + 1) * (factQ (j₁ + m₁) * factQ (j₁ - m₁) * factQ (j₂ + m₂) *
          factQ (j₂ - m₂) * factQ (j₃ + m₃) * factQ (j₃ - m₃))) *
        w34_S (j₁ + j₂ - j₃) (j₁ - m₁) (j₂ + m₂) 0 (j₂ - j₃ - m₁) (j₁ - j₃ + m₂) := by
  unfold wigner3j
  simp only [h, ↓reduceIte]
  rw [w34_sum3j_eq_S h.1.1, triangleDelta, Real.sqrt_mul (x := factQ (j₁ + j₂ - j₃) *
    factQ (j₁ - j₂ + j₃) * factQ (-j₁ + j₂ + j₃) / factQ (j₁ + j₂ + j₃ + 1))
    (by unfold factQ; positivity)]
  ring

/-- The `3j` symbol vanishes unless `m₁ + m₂ + m₃ = 0`. -/
lemma w34_wigner3j_sum_ne {j₁ j₂ j₃ m₁ m₂ m₃ : ℚ} (h : m₁ + m₂ + m₃ ≠ 0) :
    wigner3j j₁ j₂ j₃ m₁ m₂ m₃ = 0 := wigner3j_of_not fun h' => h h'.2.2.2.2

/-! ## §34.2 The triangle conditions -/

/-- DLMF 34.2.1 and §34.2: `IsTriad j₁ j₂ j₃` holds iff each `jᵣ` is a nonnegative integer or
half-odd integer, `j₁ + j₂ + j₃` is an integer (all three integers, or one integer and two
half-odd integers), and the triangle conditions `|jᵣ - jₛ| ≤ jₜ ≤ jᵣ + jₛ` hold for every
permutation `r, s, t` of `1, 2, 3`. -/
@[dlmf 34.2.E1]
theorem isTriad_iff {j₁ j₂ j₃ : ℚ} :
    IsTriad j₁ j₂ j₃ ↔
      IsAngularMomentum j₁ ∧ IsAngularMomentum j₂ ∧ IsAngularMomentum j₃ ∧
        (∃ n : ℤ, j₁ + j₂ + j₃ = n) ∧
        (|j₁ - j₂| ≤ j₃ ∧ j₃ ≤ j₁ + j₂) ∧ (|j₂ - j₃| ≤ j₁ ∧ j₁ ≤ j₂ + j₃) ∧
        (|j₃ - j₁| ≤ j₂ ∧ j₂ ≤ j₃ + j₁) := by
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩
    refine ⟨⟨a + b, by push_cast; linarith⟩, ⟨a + c, by push_cast; linarith⟩,
      ⟨b + c, by push_cast; linarith⟩, ⟨a + b + c, by push_cast; linarith⟩, ?_, ?_, ?_⟩ <;>
    · have := (Nat.cast_nonneg a : (0 : ℚ) ≤ a)
      have := (Nat.cast_nonneg b : (0 : ℚ) ≤ b)
      have := (Nat.cast_nonneg c : (0 : ℚ) ≤ c)
      refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, by linarith⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨n, hn⟩, ⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩⟩
    have e1 : j₁ + j₂ - j₃ = ((n - c : ℤ) : ℚ) := by push_cast; linarith
    have e2 : j₁ - j₂ + j₃ = ((n - b : ℤ) : ℚ) := by push_cast; linarith
    have e3 : -j₁ + j₂ + j₃ = ((n - a : ℤ) : ℚ) := by push_cast; linarith
    have q1 : (0 : ℚ) ≤ ((n - c : ℤ) : ℚ) := by rw [← e1]; linarith
    have q2 : (0 : ℚ) ≤ ((n - b : ℤ) : ℚ) := by rw [← e2]; linarith [(abs_le.mp h5).2]
    have q3 : (0 : ℚ) ≤ ((n - a : ℤ) : ℚ) := by rw [← e3]; linarith [(abs_le.mp h3).2]
    exact ⟨isNatQ_of_int _ e1 (by exact_mod_cast q1), isNatQ_of_int _ e2 (by exact_mod_cast q2),
      isNatQ_of_int _ e3 (by exact_mod_cast q3)⟩

/-- DLMF §34.2 (34.2.1 and 34.2.3): the `3j` symbol vanishes when the triangle conditions fail.
-/
@[dlmf 34.2.E1, dlmf 34.10]
theorem wigner3j_eq_zero_of_not_isTriad {j₁ j₂ j₃ : ℚ} (h : ¬ IsTriad j₁ j₂ j₃)
    (m₁ m₂ m₃ : ℚ) : wigner3j j₁ j₂ j₃ m₁ m₂ m₃ = 0 :=
  wigner3j_of_not fun h' => h h'.1

/-- DLMF §34.2 (34.2.3): the `3j` symbol vanishes unless `m₁ + m₂ + m₃ = 0`. -/
@[dlmf 34.2.E3, dlmf 34.10]
theorem wigner3j_eq_zero_of_sum_ne_zero (j₁ j₂ j₃ : ℚ) {m₁ m₂ m₃ : ℚ}
    (h : m₁ + m₂ + m₃ ≠ 0) : wigner3j j₁ j₂ j₃ m₁ m₂ m₃ = 0 :=
  wigner3j_of_not fun h' => h h'.2.2.2.2

/-- DLMF 34.2.2: the `3j` symbol vanishes unless each `mᵣ` is one of `-jᵣ, …, jᵣ` (the value
outside the range of definition; all summations of the chapter use this convention). -/
@[dlmf 34.2.E2]
theorem wigner3j_eq_zero_of_not_isProjection {j₁ j₂ j₃ m₁ m₂ m₃ : ℚ}
    (h : ¬ (IsProjection j₁ m₁ ∧ IsProjection j₂ m₂ ∧ IsProjection j₃ m₃)) :
    wigner3j j₁ j₂ j₃ m₁ m₂ m₃ = 0 :=
  wigner3j_of_not fun h' => h ⟨h'.2.1, h'.2.2.1, h'.2.2.2.1⟩

/-- DLMF 34.2.6: the `3j` symbol as a terminating `₃F₂` of unit argument,
`(-1)^{j₂-m₁+m₃} (j₁+j₂+m₃)! (j₂+j₃-m₁)! / (Δ(j₁j₂j₃) (j₁+j₂+j₃+1)!)`
`× ((j₁+m₁)!(j₃-m₃)! / ((j₁-m₁)!(j₂+m₂)!(j₂-m₂)!(j₃+m₃)!))^{1/2}`
`× ₃F₂(-j₁-j₂-j₃-1, -j₁+m₁, -j₃-m₃; -j₁-j₂-m₃, -j₂-j₃+m₁; 1)`.
The series terminates after `n = min(j₁-m₁, j₃+m₃)` terms; the lower parameters are
nonpositive integers `≤ -n`, so every retained Pochhammer denominator is nonzero
(`genFiniteHG`, the convention of §16.2). Assumes 34.2.1–34.2.3. -/
@[dlmf 34.2.E6]
theorem wigner3j_eq_hyp3F2 {j₁ j₂ j₃ m₁ m₂ m₃ : ℚ} (h : IsAdmissible3j j₁ j₂ j₃ m₁ m₂ m₃) :
    (wigner3j j₁ j₂ j₃ m₁ m₂ m₃ : ℂ) =
      ((signPow (j₂ - m₁ + m₃) * factQ (j₁ + j₂ + m₃) * factQ (j₂ + j₃ - m₁) /
          (triangleDelta j₁ j₂ j₃ * factQ (j₁ + j₂ + j₃ + 1)) *
          Real.sqrt (factQ (j₁ + m₁) * factQ (j₃ - m₃) /
            (factQ (j₁ - m₁) * factQ (j₂ + m₂) * factQ (j₂ - m₂) * factQ (j₃ + m₃))) : ℝ) : ℂ) *
        DLMF.Hypergeometric.genFiniteHG (min ⌊j₁ - m₁⌋.toNat ⌊j₃ + m₃⌋.toNat)
          {((-j₁ - j₂ - j₃ - 1 : ℚ) : ℂ), ((-j₁ + m₁ : ℚ) : ℂ), ((-j₃ - m₃ : ℚ) : ℂ)}
          {((-j₁ - j₂ - m₃ : ℚ) : ℂ), ((-j₂ - j₃ + m₁ : ℚ) : ℂ)} 1 := by
  sorry

/-! ## §34.3(i) Special cases -/

/-- DLMF 34.3.1: `(j j 0; m -m 0) = (-1)^{j-m} / (2j+1)^{1/2}`, for every projection `m`
of `j`. -/
@[dlmf 34.3.E1]
theorem wigner3j_j_j_zero {j m : ℚ} (h : IsProjection j m) :
    wigner3j j j 0 m (-m) 0 = signPow (j - m) / Real.sqrt (2 * (j : ℝ) + 1) := by
  obtain ⟨a, ha⟩ := h.1
  obtain ⟨b, hb⟩ := h.2
  have hj : j = ((a : ℚ) + b) / 2 := by linarith
  have hm : m = ((b : ℚ) - a) / 2 := by linarith
  subst hj hm
  have hadm : IsAdmissible3j (((a : ℚ) + b) / 2) (((a : ℚ) + b) / 2) 0 (((b : ℚ) - a) / 2)
      (-(((b : ℚ) - a) / 2)) 0 :=
    ⟨⟨⟨a + b, by push_cast; ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩,
      ⟨⟨a, by ring⟩, ⟨b, by ring⟩⟩,
      ⟨⟨b, by ring⟩, ⟨a, by ring⟩⟩,
      ⟨⟨0, by ring⟩, ⟨0, by ring⟩⟩, by ring⟩
  rw [wigner3j]
  simp only [hadm, ↓reduceIte]
  have hrange : ⌊((a : ℚ) + b) / 2 + ((a : ℚ) + b) / 2 - 0⌋.toNat = a + b := by
    rw [show ((a : ℚ) + b) / 2 + ((a : ℚ) + b) / 2 - 0 = ((a + b : ℕ) : ℚ) by push_cast; ring,
      Int.floor_natCast, Int.toNat_natCast]
  rw [hrange, Finset.sum_eq_single a]
  · unfold triangleDelta racahTerm3j
    ring_nf
    rw [show (1 : ℚ) + a + b = ((a + b + 1 : ℕ) : ℚ) by push_cast; ring,
      show (0 : ℚ) = ((0 : ℕ) : ℚ) by simp]
    simp only [← Nat.cast_add, factQ_natCast, invFactQ_natCast, signPow_natCast]
    have hf : ((a + b + 1).factorial : ℝ) = ((a : ℝ) + b + 1) * (a + b).factorial := by
      push_cast [Nat.factorial_succ]; ring
    have hpos : (0 : ℝ) < (a : ℝ) + b + 1 := by positivity
    have hA : (0 : ℝ) < (a.factorial : ℝ) := by positivity
    have hB : (0 : ℝ) < (b.factorial : ℝ) := by positivity
    have hAB : (0 : ℝ) < ((a + b).factorial : ℝ) := by positivity
    rw [hf, show ((0 : ℕ).factorial : ℝ) = 1 by simp,
      show (1 : ℝ) ^ 2 * (b.factorial : ℝ) ^ 2 * (a.factorial : ℝ) ^ 2 =
        ((a.factorial : ℝ) * b.factorial) ^ 2 by ring,
      Real.sqrt_sq (by positivity),
      show ((a + b).factorial : ℝ) * 1 ^ 2 * ((((a : ℝ) + b + 1) * (a + b).factorial))⁻¹ =
        ((a : ℝ) + b + 1)⁻¹ by field_simp,
      Real.sqrt_inv]
    push_cast
    rw [show (1 : ℝ) + ((a : ℝ) * (1 / 2) + b * (1 / 2)) * 2 = a + b + 1 by ring]
    field_simp
  · intro s _ hs
    unfold racahTerm3j
    rcases lt_or_gt_of_ne hs with hlt | hgt
    · rw [invFactQ_of_neg (x := 0 - ((a + b : ℚ)) / 2 + ((b : ℚ) - a) / 2 + s)]
      · ring
      · have : (s : ℚ) < a := by exact_mod_cast hlt
        linarith
    · rw [invFactQ_of_neg (x := ((a + b : ℚ)) / 2 + -(((b : ℚ) - a) / 2) - s)]
      · ring
      · have : (a : ℚ) < s := by exact_mod_cast hgt
        linarith
  · intro ha'
    simp at ha'


/-- Close a cast equation. -/
macro "w34_nq" : tactic => `(tactic| first | ring1 | (push_cast; ring1))

/-- The symmetric Racah sum with `x₁ = y₁ = n` reduces to its single term `s = n`. -/
lemma w34_S_single (n : ℤ) (x₂ x₃ y₂ y₃ : ℚ) :
    w34_S n x₂ x₃ n y₂ y₃ =
      (-1 : ℝ) ^ n * (invFactQ (x₂ - n) * invFactQ (x₃ - n) * (invFactQ (n - y₂) *
        invFactQ (n - y₃))) := by
  unfold w34_S
  rw [finsum_eq_single _ n]
  · simp only [sub_self]
    rw [show (0 : ℚ) = ((0 : ℕ) : ℚ) by simp, invFactQ_natCast]
    simp
  · intro s hs
    rcases lt_or_gt_of_ne hs with h | h
    · rw [invFactQ_of_neg (x := (s : ℚ) - n) (by
        have : (s : ℚ) < n := by exact_mod_cast h
        linarith)]
      ring
    · rw [invFactQ_of_neg (x := (n : ℚ) - s) (by
        have : (n : ℚ) < s := by exact_mod_cast h
        linarith)]
      ring

/-- `w34_S_single` with the coinciding arguments given by equations. -/
lemma q2w_S_single_of_eq {x₁ x₂ x₃ y₁ y₂ y₃ : ℚ} (n : ℤ) (hx : x₁ = n) (hy : y₁ = n) :
    w34_S x₁ x₂ x₃ y₁ y₂ y₃ =
      (-1 : ℝ) ^ n * (invFactQ (x₂ - n) * invFactQ (x₃ - n) * (invFactQ (n - y₂) *
        invFactQ (n - y₃))) := by
  subst hx hy; exact w34_S_single n x₂ x₃ y₂ y₃

/-- The symmetric Racah sum with `x₁ = n + 1`, `y₁ = n` has the two terms `s = n, n + 1`. -/
lemma q2w_S_pair_of_eq {x₁ x₂ x₃ y₁ y₂ y₃ : ℚ} (n : ℤ) (hx : x₁ = n + 1) (hy : y₁ = n) :
    w34_S x₁ x₂ x₃ y₁ y₂ y₃ =
      (-1 : ℝ) ^ n * (invFactQ (x₂ - n) * invFactQ (x₃ - n) * (invFactQ (n - y₂) *
        invFactQ (n - y₃)) - invFactQ (x₂ - n - 1) * invFactQ (x₃ - n - 1) *
        (invFactQ (n + 1 - y₂) * invFactQ (n + 1 - y₃))) := by
  subst hx hy
  unfold w34_S
  rw [finsum_eq_sum_of_support_subset _ (s := {n, n + 1}) ?_,
    Finset.sum_pair (by omega)]
  · rw [zpow_add₀ (by norm_num)]
    push_cast
    simp only [sub_self, show ((n : ℚ) + 1 - n) = 1 by ring, w34_invFactQ_zero,
      q2w_invFactQ_one]
    ring_nf
  · intro s hs
    simp only [Function.mem_support] at hs
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra hne
    simp only [not_or] at hne
    rcases lt_or_gt_of_ne hne.1 with h | h
    · apply hs
      rw [invFactQ_of_neg (x := (s : ℚ) - n) (by
        have : (s : ℚ) < n := by exact_mod_cast h
        linarith)]
      ring
    · have h' : n + 1 < s := by omega
      apply hs
      rw [invFactQ_of_neg (x := (n : ℚ) + 1 - s) (by
        have : (n : ℚ) + 1 < s := by exact_mod_cast h'
        linarith)]
      ring

/-- DLMF 34.3.2: `(j j 1; m -m 0) = (-1)^{j-m} 2m / (2j(2j+1)(2j+2))^{1/2}`, `j ≥ 1/2`. -/
@[dlmf 34.3.E2]
theorem wigner3j_j_j_one_zero {j m : ℚ} (h : IsProjection j m) (hj : 1 / 2 ≤ j) :
    wigner3j j j 1 m (-m) 0 =
      signPow (j - m) * (2 * (m : ℝ)) /
        Real.sqrt (2 * (j : ℝ) * (2 * j + 1) * (2 * j + 2)) := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := h
  obtain rfl : j = ((p : ℚ) + q) / 2 := by linarith
  obtain rfl : m = ((q : ℚ) - p) / 2 := by linarith
  rw [show (2 * ((((p : ℚ) + q) / 2 : ℚ) : ℝ) * (2 * (((p : ℚ) + q) / 2 : ℚ) + 1) *
      (2 * (((p : ℚ) + q) / 2 : ℚ) + 2)) = (((p : ℚ) + q : ℚ) : ℝ) * (((p : ℚ) + q : ℚ) + 1) *
      (((p : ℚ) + q : ℚ) + 2) by push_cast; ring]
  rcases p with _ | r
  · obtain ⟨c, rfl⟩ : ∃ c, q = c + 1 := ⟨q - 1, by
      have : (1 : ℚ) ≤ q := by push_cast at hj; linarith
      have : 1 ≤ q := by exact_mod_cast this
      omega⟩
    have hadm : IsAdmissible3j ((((0 : ℕ) : ℚ) + ((c + 1 : ℕ) : ℚ)) / 2)
        ((((0 : ℕ) : ℚ) + ((c + 1 : ℕ) : ℚ)) / 2) 1
        (((((c + 1 : ℕ) : ℚ) : ℚ) - (0 : ℕ)) / 2) (-(((((c + 1 : ℕ) : ℚ) : ℚ) - (0 : ℕ)) / 2)) 0 :=
      ⟨⟨⟨c, by w34_nq⟩, ⟨1, by w34_nq⟩, ⟨1, by w34_nq⟩⟩, ⟨⟨0, by w34_nq⟩, ⟨c + 1, by w34_nq⟩⟩,
        ⟨⟨c + 1, by w34_nq⟩, ⟨0, by w34_nq⟩⟩, ⟨⟨1, by w34_nq⟩, ⟨1, by w34_nq⟩⟩, by ring⟩
    have hR : (0 : ℝ) ≤ ((1 + c).factorial : ℝ) := by positivity
    have hY : (0 : ℝ) ≤ ((c + 1 : ℝ)) * (c + 2) * (c + 3) := by positivity
    rw [show ((((0 : ℕ) : ℚ) + ((c + 1 : ℕ) : ℚ) : ℚ) : ℝ) *
        ((((0 : ℕ) : ℚ) + ((c + 1 : ℕ) : ℚ) : ℚ) + 1) *
        ((((0 : ℕ) : ℚ) + ((c + 1 : ℕ) : ℚ) : ℚ) + 2) =
      ((c + 1 : ℝ)) * (c + 2) * (c + 3) by push_cast; ring]
    rw [w34_wigner3j_eq hadm, w34_S_swap_x12, w34_S_swap_y12,
      q2w_S_pair_of_eq ((((0 : ℕ) : ℕ) : ℤ) - 1) (by push_cast; ring) (by push_cast; ring),
      signPow_of_eq (n := 0) (by push_cast; ring),
      signPow_of_eq (n := (((0 : ℕ) : ℕ) : ℤ)) (by push_cast; ring), zpow_natCast,
      zpow_sub_one₀ (by norm_num), zpow_natCast, zpow_zero, one_mul,
      q2w_sqrt_eq_div hR hY, div_mul_eq_mul_div]
    · congr 1
      q2w_casts
      q2w_fin
    · q2w_casts
      q2w_fin
  · have hadm : IsAdmissible3j ((((r + 1 : ℕ) : ℚ) + (q : ℚ)) / 2)
        ((((r + 1 : ℕ) : ℚ) + (q : ℚ)) / 2) 1
        ((((q : ℚ) : ℚ) - (r + 1 : ℕ)) / 2) (-((((q : ℚ) : ℚ) - (r + 1 : ℕ)) / 2)) 0 :=
      ⟨⟨⟨r + q, by w34_nq⟩, ⟨1, by w34_nq⟩, ⟨1, by w34_nq⟩⟩, ⟨⟨r + 1, by w34_nq⟩, ⟨q, by w34_nq⟩⟩,
        ⟨⟨q, by w34_nq⟩, ⟨r + 1, by w34_nq⟩⟩, ⟨⟨1, by w34_nq⟩, ⟨1, by w34_nq⟩⟩, by ring⟩
    have hR : (0 : ℝ) ≤ ((1 + r).factorial * q.factorial : ℝ) := by positivity
    have hY : (0 : ℝ) ≤ ((r + q + 1 : ℝ)) * (r + q + 2) * (r + q + 3) := by positivity
    rw [show ((((r + 1 : ℕ) : ℚ) + (q : ℚ) : ℚ) : ℝ) *
        ((((r + 1 : ℕ) : ℚ) + (q : ℚ) : ℚ) + 1) * ((((r + 1 : ℕ) : ℚ) + (q : ℚ) : ℚ) + 2) =
      ((r + q + 1 : ℝ)) * (r + q + 2) * (r + q + 3) by push_cast; ring]
    rw [w34_wigner3j_eq hadm, w34_S_swap_x12, w34_S_swap_y12,
      q2w_S_pair_of_eq ((((r + 1 : ℕ) : ℕ) : ℤ) - 1) (by push_cast; ring) (by push_cast; ring),
      signPow_of_eq (n := 0) (by push_cast; ring),
      signPow_of_eq (n := (((r + 1 : ℕ) : ℕ) : ℤ)) (by push_cast; ring), zpow_natCast,
      zpow_sub_one₀ (by norm_num), zpow_natCast, zpow_zero, one_mul,
      q2w_sqrt_eq_div hR hY, div_mul_eq_mul_div]
    · congr 1
      q2w_casts
      q2w_fin
    · q2w_casts
      q2w_fin

/-- DLMF 34.3.3: `(j j 1; m -m-1 1) = (-1)^{j-m} (2(j-m)(j+m+1) / (2j(2j+1)(2j+2)))^{1/2}`,
`j ≥ 1/2`. -/
@[dlmf 34.3.E3]
theorem wigner3j_j_j_one_one {j m : ℚ} (h : IsProjection j m) (hj : 1 / 2 ≤ j) :
    wigner3j j j 1 m (-m - 1) 1 =
      signPow (j - m) * Real.sqrt (2 * ((j : ℝ) - m) * (j + m + 1) /
        (2 * (j : ℝ) * (2 * j + 1) * (2 * j + 2))) := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := h
  obtain rfl : j = ((p : ℚ) + q) / 2 := by linarith
  obtain rfl : m = ((q : ℚ) - p) / 2 := by linarith
  rcases Nat.eq_zero_or_eq_succ_pred p with h0 | h0
  · subst h0
    rw [wigner3j_of_not]
    · push_cast; simp
    · rintro ⟨-, -, ⟨-, ⟨k, hk⟩⟩, -⟩
      push_cast at hk
      have := (Nat.cast_nonneg (α := ℚ) k); linarith
  obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨_, h0⟩
  have hadm : IsAdmissible3j ((((r + 1 : ℕ) : ℚ) + q) / 2) ((((r + 1 : ℕ) : ℚ) + q) / 2) 1
      (((q : ℚ) - ((r + 1 : ℕ) : ℚ)) / 2) (-(((q : ℚ) - ((r + 1 : ℕ) : ℚ)) / 2) - 1) 1 :=
    ⟨⟨⟨r + q, by w34_nq⟩, ⟨1, by w34_nq⟩, ⟨1, by w34_nq⟩⟩, ⟨⟨r + 1, by w34_nq⟩, ⟨q, by w34_nq⟩⟩,
      ⟨⟨q + 1, by w34_nq⟩, ⟨r, by w34_nq⟩⟩, ⟨⟨0, by w34_nq⟩, ⟨2, by w34_nq⟩⟩, by ring⟩
  rw [w34_wigner3j_eq hadm, w34_S_swap_x23, w34_S_swap_x12, w34_S_swap_y12,
    q2w_S_single_of_eq (r : ℤ) (by push_cast; ring) (by push_cast; ring),
    signPow_of_eq (n := -1) (by push_cast; ring),
    signPow_of_eq (n := ((r + 1 : ℕ) : ℤ)) (by push_cast; ring), zpow_natCast, zpow_natCast,
    show (-1 : ℝ) ^ (-1 : ℤ) = -1 by norm_num]
  rw [show ∀ A X : ℝ, -1 * A * ((-1) ^ r * X) = (-1) ^ (r + 1) * (A * X) from
    fun A X => by ring]
  congr 1
  apply w34_sqrt_mul_eq
  · q2w_nonneg
  · q2w_nonneg
  · q2w_casts
    q2w_fin

/-- DLMF 34.3.4–34.3.5, `J = j₁ + j₂ + j₃ = 2n` even:
`(j₁ j₂ j₃; 0 0 0) = (-1)^{J/2} ((J-2j₁)!(J-2j₂)!(J-2j₃)!/(J+1)!)^{1/2}`
`× (J/2)! / ((J/2-j₁)!(J/2-j₂)!(J/2-j₃)!)`, for integers `jᵣ` satisfying the triangle
conditions. -/
@[dlmf 34.3.E4, dlmf 34.3.E5]
theorem wigner3j_zero_zero_zero_of_even {j₁ j₂ j₃ : ℚ} (h : IsTriad j₁ j₂ j₃)
    (h₁ : IsNatQ j₁) (h₂ : IsNatQ j₂) (h₃ : IsNatQ j₃) (n : ℕ) (hJ : j₁ + j₂ + j₃ = 2 * n) :
    wigner3j j₁ j₂ j₃ 0 0 0 =
      (-1 : ℝ) ^ n * Real.sqrt (factQ (2 * n - 2 * j₁) * factQ (2 * n - 2 * j₂) *
        factQ (2 * n - 2 * j₃) / factQ (2 * n + 1)) *
        (n.factorial / (factQ (n - j₁) * factQ (n - j₂) * factQ (n - j₃))) := by
  sorry

/-! ### Single-term evaluations -/

/-- Finish `s * √A * B = s * √C` from `A * B² = C`. -/
macro "w34_finish" : tactic => `(tactic|
  (simp only [mul_assoc]
   congr 1
   apply w34_sqrt_mul_eq (by positivity) (by positivity)
   first | (field_simp; done) | (field_simp; ring1)))

/-- The symmetric Racah sum with `x₁ = y₁ = 0`. -/
lemma w34_S_zero₁ (x₂ x₃ y₂ y₃ : ℚ) :
    w34_S 0 x₂ x₃ 0 y₂ y₃ = invFactQ x₂ * invFactQ x₃ * (invFactQ (-y₂) * invFactQ (-y₃)) := by
  have := w34_S_single 0 x₂ x₃ y₂ y₃
  simp only [Int.cast_zero, sub_zero, zero_sub, zpow_zero, one_mul] at this
  exact this

/-- The symmetric Racah sum with `x₂ = y₁ = 0`. -/
lemma w34_S_zero₂ (x₁ x₃ y₂ y₃ : ℚ) :
    w34_S x₁ 0 x₃ 0 y₂ y₃ = invFactQ x₁ * invFactQ x₃ * (invFactQ (-y₂) * invFactQ (-y₃)) := by
  rw [w34_S_swap_x12, w34_S_zero₁]

/-- The symmetric Racah sum with `x₃ = y₁ = 0`. -/
lemma w34_S_zero₃ (x₁ x₂ y₂ y₃ : ℚ) :
    w34_S x₁ x₂ 0 0 y₂ y₃ = invFactQ x₁ * invFactQ x₂ * (invFactQ (-y₂) * invFactQ (-y₃)) := by
  rw [← w34_S_cycle_x, w34_S_zero₁]

/-- DLMF 34.3.6: the stretched case `j₃ = j₁ + j₂`,
`(j₁ j₂ j₁+j₂; m₁ m₂ -m₁-m₂) = (-1)^{j₁-j₂+m₁+m₂}`
`× ((2j₁)!(2j₂)!(j₁+j₂+m₁+m₂)!(j₁+j₂-m₁-m₂)!`
`/ ((2j₁+2j₂+1)!(j₁+m₁)!(j₁-m₁)!(j₂+m₂)!(j₂-m₂)!))^{1/2}`.
-/
@[dlmf 34.3.E6]
theorem wigner3j_stretched {j₁ j₂ m₁ m₂ : ℚ} (h₁ : IsProjection j₁ m₁)
    (h₂ : IsProjection j₂ m₂) :
    wigner3j j₁ j₂ (j₁ + j₂) m₁ m₂ (-m₁ - m₂) =
      signPow (j₁ - j₂ + m₁ + m₂) * Real.sqrt (factQ (2 * j₁) * factQ (2 * j₂) *
        factQ (j₁ + j₂ + m₁ + m₂) * factQ (j₁ + j₂ - m₁ - m₂) /
        (factQ (2 * j₁ + 2 * j₂ + 1) * factQ (j₁ + m₁) * factQ (j₁ - m₁) * factQ (j₂ + m₂) *
          factQ (j₂ - m₂))) := by
  obtain ⟨⟨p₁, hp₁⟩, ⟨q₁, hq₁⟩⟩ := h₁
  obtain ⟨⟨p₂, hp₂⟩, ⟨q₂, hq₂⟩⟩ := h₂
  obtain rfl : j₁ = ((p₁ : ℚ) + q₁) / 2 := by linarith
  obtain rfl : m₁ = ((q₁ : ℚ) - p₁) / 2 := by linarith
  obtain rfl : j₂ = ((p₂ : ℚ) + q₂) / 2 := by linarith
  obtain rfl : m₂ = ((q₂ : ℚ) - p₂) / 2 := by linarith
  have hadm : IsAdmissible3j (((p₁ : ℚ) + q₁) / 2) (((p₂ : ℚ) + q₂) / 2)
      (((p₁ : ℚ) + q₁) / 2 + ((p₂ : ℚ) + q₂) / 2) (((q₁ : ℚ) - p₁) / 2)
      (((q₂ : ℚ) - p₂) / 2) (-(((q₁ : ℚ) - p₁) / 2) - ((q₂ : ℚ) - p₂) / 2) :=
    ⟨⟨⟨0, by w34_nq⟩, ⟨p₁ + q₁, by w34_nq⟩, ⟨p₂ + q₂, by w34_nq⟩⟩,
      ⟨⟨p₁, by w34_nq⟩, ⟨q₁, by w34_nq⟩⟩,
      ⟨⟨p₂, by w34_nq⟩, ⟨q₂, by w34_nq⟩⟩,
      ⟨⟨q₁ + q₂, by w34_nq⟩, ⟨p₁ + p₂, by w34_nq⟩⟩, by ring⟩
  rw [w34_wigner3j_eq hadm, sub_self, w34_S_zero₁]
  ring_nf
  simp only [w34_one_add_natCast, ← Nat.cast_add, factQ_natCast, invFactQ_natCast,
    w34_factQ_zero, one_mul]
  w34_finish

/-- DLMF 34.3.7: `(j₁ j₂ j₃; j₁ -j₁-m₃ m₃) = (-1)^{j₁-j₂-m₃}`
`× ((2j₁)!(-j₁+j₂+j₃)!(j₁+j₂+m₃)!(j₃-m₃)!`
`/ ((j₁+j₂+j₃+1)!(j₁-j₂+j₃)!(j₁+j₂-j₃)!(-j₁+j₂-m₃)!(j₃+m₃)!))^{1/2}`,
assuming the triangle conditions and that `m₃` and `-j₁-m₃` are projections of `j₃` and `j₂`.
-/
@[dlmf 34.3.E7]
theorem wigner3j_top {j₁ j₂ j₃ m₃ : ℚ} (h : IsTriad j₁ j₂ j₃) (h₂ : IsProjection j₂ (-j₁ - m₃))
    (h₃ : IsProjection j₃ m₃) :
    wigner3j j₁ j₂ j₃ j₁ (-j₁ - m₃) m₃ =
      signPow (j₁ - j₂ - m₃) * Real.sqrt (factQ (2 * j₁) * factQ (-j₁ + j₂ + j₃) *
        factQ (j₁ + j₂ + m₃) * factQ (j₃ - m₃) /
        (factQ (j₁ + j₂ + j₃ + 1) * factQ (j₁ - j₂ + j₃) * factQ (j₁ + j₂ - j₃) *
          factQ (-j₁ + j₂ - m₃) * factQ (j₃ + m₃))) := by
  obtain ⟨⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩, ⟨a₃, ha₃⟩⟩ := h
  obtain ⟨⟨b, hb⟩, ⟨c, hc⟩⟩ := h₂
  obtain ⟨⟨d, hd⟩, ⟨e, he⟩⟩ := h₃
  obtain rfl : j₁ = ((a₁ : ℚ) + a₂) / 2 := by linarith
  obtain rfl : j₂ = ((a₁ : ℚ) + c + e) / 2 := by linarith
  obtain rfl : j₃ = ((a₂ : ℚ) + c + e) / 2 := by linarith
  obtain rfl : m₃ = ((e : ℚ) - a₂ - c) / 2 := by linarith
  have hadm : IsAdmissible3j (((a₁ : ℚ) + a₂) / 2) (((a₁ : ℚ) + c + e) / 2)
      (((a₂ : ℚ) + c + e) / 2) (((a₁ : ℚ) + a₂) / 2)
      (-(((a₁ : ℚ) + a₂) / 2) - ((e : ℚ) - a₂ - c) / 2) (((e : ℚ) - a₂ - c) / 2) :=
    ⟨⟨⟨a₁, by w34_nq⟩, ⟨a₂, by w34_nq⟩, ⟨c + e, by w34_nq⟩⟩,
      ⟨⟨0, by w34_nq⟩, ⟨a₁ + a₂, by w34_nq⟩⟩,
      ⟨⟨a₁ + e, by w34_nq⟩, ⟨c, by w34_nq⟩⟩,
      ⟨⟨a₂ + c, by w34_nq⟩, ⟨e, by w34_nq⟩⟩, by ring⟩
  rw [w34_wigner3j_eq hadm]
  ring_nf
  simp only [w34_S_zero₂, neg_neg, w34_one_add_natCast, ← Nat.cast_add, factQ_natCast,
    invFactQ_natCast, w34_factQ_zero, mul_one]
  w34_finish

/-! ## §34.3(ii) Symmetry -/

/-- DLMF 34.3.8, first equality: invariance under the cyclic permutation of the columns. -/
@[dlmf 34.3.E8]
theorem wigner3j_cycle (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ) :
    wigner3j j₁ j₂ j₃ m₁ m₂ m₃ = wigner3j j₂ j₃ j₁ m₂ m₃ m₁ := by
  by_cases hm : m₁ + m₂ + m₃ = 0
  swap
  · rw [w34_wigner3j_sum_ne hm, w34_wigner3j_sum_ne (fun h => hm (by linarith))]
  obtain rfl : m₃ = -m₁ - m₂ := by linarith
  have hiff : IsAdmissible3j j₁ j₂ j₃ m₁ m₂ (-m₁ - m₂) ↔
      IsAdmissible3j j₂ j₃ j₁ m₂ (-m₁ - m₂) m₁ := by
    unfold IsAdmissible3j IsTriad IsProjection
    constructor <;> rintro ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, ⟨h6, h7⟩, ⟨h8, h9⟩, -⟩ <;>
      exact ⟨⟨by w34_pick9, by w34_pick9, by w34_pick9⟩, ⟨by w34_pick9, by w34_pick9⟩,
        ⟨by w34_pick9, by w34_pick9⟩, ⟨by w34_pick9, by w34_pick9⟩, by ring⟩
  by_cases h : IsAdmissible3j j₁ j₂ j₃ m₁ m₂ (-m₁ - m₂)
  · have h' := hiff.mp h
    rw [w34_wigner3j_eq h, w34_wigner3j_eq h']
    obtain ⟨-, ⟨⟨p₁, hp₁⟩, ⟨q₁, hq₁⟩⟩, ⟨⟨p₂, hp₂⟩, ⟨q₂, hq₂⟩⟩, ⟨⟨p₃, hp₃⟩, ⟨q₃, hq₃⟩⟩, -⟩ := h
    have hpq : q₁ + q₂ + q₃ = p₁ + p₂ + p₃ := by
      exact_mod_cast (by linarith : (q₁ : ℚ) + q₂ + q₃ = p₁ + p₂ + p₃)
    have e : w34_S (j₂ + j₃ - j₁) (j₂ - m₂) (j₃ + (-m₁ - m₂)) 0 (j₃ - j₁ - m₂)
        (j₂ - j₁ + (-m₁ - m₂)) =
        w34_S ((j₂ + m₂) + (j₃ - j₁ - m₂)) ((j₁ + j₂ - j₃) + (j₃ - j₁ - m₂))
          ((j₁ - m₁) + (j₃ - j₁ - m₂)) ((j₁ - j₃ + m₂) + (j₃ - j₁ - m₂))
          (0 + (j₃ - j₁ - m₂)) ((j₂ - j₃ - m₁) + (j₃ - j₁ - m₂)) := by
      congr 1 <;> ring
    rw [e, w34_S_shift _ _ _ _ _ _ _ ((q₃ : ℤ) - p₁) (by push_cast; linarith),
      ← w34_S_cycle_x, ← w34_S_cycle_y, ← w34_S_cycle_x, ← w34_S_cycle_y,
      signPow_of_eq (x := j₁ - j₂ - (-m₁ - m₂)) (n := (q₁ : ℤ) - p₂) (by push_cast; linarith),
      signPow_of_eq (x := j₂ - j₃ - m₁) (n := (q₂ : ℤ) - p₃) (by push_cast; linarith)]
    have hs : (-1 : ℝ) ^ ((q₂ : ℤ) - p₃) * (-1) ^ ((q₃ : ℤ) - p₁) = (-1) ^ ((q₁ : ℤ) - p₂) := by
      rw [← zpow_add₀ (by norm_num)]
      exact w34_neg_one_zpow_eq ((p₂ : ℤ) - q₁) (by omega)
    rw [← hs]
    ring_nf
  · rw [wigner3j_of_not h, wigner3j_of_not (mt hiff.mpr h)]

/-- DLMF 34.3.8, second equality. -/
@[dlmf 34.3.E8]
theorem wigner3j_cycle₂ (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ) :
    wigner3j j₁ j₂ j₃ m₁ m₂ m₃ = wigner3j j₃ j₁ j₂ m₃ m₁ m₂ := by
  rw [wigner3j_cycle, wigner3j_cycle]

/-- DLMF 34.3.9: an odd permutation of the columns gives the phase `(-1)^{j₁+j₂+j₃}`. -/
@[dlmf 34.3.E9]
theorem wigner3j_swap (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ) :
    wigner3j j₁ j₂ j₃ m₁ m₂ m₃ = signPow (j₁ + j₂ + j₃) * wigner3j j₂ j₁ j₃ m₂ m₁ m₃ := by
  by_cases hm : m₁ + m₂ + m₃ = 0
  swap
  · rw [w34_wigner3j_sum_ne hm, w34_wigner3j_sum_ne (fun h => hm (by linarith)), mul_zero]
  obtain rfl : m₃ = -m₁ - m₂ := by linarith
  have hiff : IsAdmissible3j j₁ j₂ j₃ m₁ m₂ (-m₁ - m₂) ↔
      IsAdmissible3j j₂ j₁ j₃ m₂ m₁ (-m₁ - m₂) := by
    unfold IsAdmissible3j IsTriad IsProjection
    constructor <;> rintro ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, ⟨h6, h7⟩, ⟨h8, h9⟩, -⟩ <;>
      exact ⟨⟨by w34_pick9, by w34_pick9, by w34_pick9⟩, ⟨by w34_pick9, by w34_pick9⟩,
        ⟨by w34_pick9, by w34_pick9⟩, ⟨by w34_pick9, by w34_pick9⟩, by ring⟩
  by_cases h : IsAdmissible3j j₁ j₂ j₃ m₁ m₂ (-m₁ - m₂)
  · have h' := hiff.mp h
    rw [w34_wigner3j_eq h, w34_wigner3j_eq h']
    obtain ⟨⟨⟨a₁, ha₁⟩, -, -⟩, ⟨⟨p₁, hp₁⟩, ⟨q₁, hq₁⟩⟩, ⟨⟨p₂, hp₂⟩, ⟨q₂, hq₂⟩⟩,
      ⟨⟨p₃, hp₃⟩, ⟨q₃, hq₃⟩⟩, -⟩ := h
    have ha : 2 * a₁ + p₃ + q₃ = p₁ + q₁ + p₂ + q₂ := by
      exact_mod_cast (by linarith : 2 * (a₁ : ℚ) + p₃ + q₃ = p₁ + q₁ + p₂ + q₂)
    have e : w34_S (j₂ + j₁ - j₃) (j₂ - m₂) (j₁ + m₁) 0 (j₁ - j₃ - m₂) (j₂ - j₃ + m₁) =
        w34_S (-0 + (j₁ + j₂ - j₃)) (-(j₁ - j₃ + m₂) + (j₁ + j₂ - j₃))
          (-(j₂ - j₃ - m₁) + (j₁ + j₂ - j₃)) (-(j₁ + j₂ - j₃) + (j₁ + j₂ - j₃))
          (-(j₂ + m₂) + (j₁ + j₂ - j₃)) (-(j₁ - m₁) + (j₁ + j₂ - j₃)) := by
      congr 1 <;> ring
    rw [e, w34_S_shift _ _ _ _ _ _ _ (a₁ : ℤ) (by push_cast; linarith),
      ← w34_S_swap_x23, ← w34_S_swap_y23, ← w34_S_neg,
      signPow_of_eq (x := j₁ - j₂ - (-m₁ - m₂)) (n := (q₁ : ℤ) - p₂) (by push_cast; linarith),
      signPow_of_eq (x := j₂ - j₁ - (-m₁ - m₂)) (n := (q₂ : ℤ) - p₁) (by push_cast; linarith),
      signPow_of_eq (x := j₁ + j₂ + j₃) (n := (a₁ : ℤ) + p₃ + q₃) (by push_cast; linarith)]
    have hs : (-1 : ℝ) ^ ((a₁ : ℤ) + p₃ + q₃) * ((-1) ^ ((q₂ : ℤ) - p₁) * (-1) ^ (a₁ : ℤ)) =
        (-1) ^ ((q₁ : ℤ) - p₂) := by
      rw [← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num)]
      exact w34_neg_one_zpow_eq ((p₂ : ℤ) + q₂) (by omega)
    rw [← hs]
    ring_nf
  · rw [wigner3j_of_not h, wigner3j_of_not (mt hiff.mpr h), mul_zero]

/-- DLMF 34.3.10: reversing the signs of the projections gives the phase `(-1)^{j₁+j₂+j₃}`. -/
@[dlmf 34.3.E10]
theorem wigner3j_neg (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ) :
    wigner3j j₁ j₂ j₃ m₁ m₂ m₃ = signPow (j₁ + j₂ + j₃) * wigner3j j₁ j₂ j₃ (-m₁) (-m₂) (-m₃) := by
  by_cases hm : m₁ + m₂ + m₃ = 0
  swap
  · rw [w34_wigner3j_sum_ne hm, w34_wigner3j_sum_ne (fun h => hm (by linarith)), mul_zero]
  obtain rfl : m₃ = -m₁ - m₂ := by linarith
  have hiff : IsAdmissible3j j₁ j₂ j₃ m₁ m₂ (-m₁ - m₂) ↔
      IsAdmissible3j j₁ j₂ j₃ (-m₁) (-m₂) (-(-m₁ - m₂)) := by
    unfold IsAdmissible3j IsTriad IsProjection
    constructor <;> rintro ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, ⟨h6, h7⟩, ⟨h8, h9⟩, -⟩ <;>
      exact ⟨⟨by w34_pick9, by w34_pick9, by w34_pick9⟩, ⟨by w34_pick9, by w34_pick9⟩,
        ⟨by w34_pick9, by w34_pick9⟩, ⟨by w34_pick9, by w34_pick9⟩, by ring⟩
  by_cases h : IsAdmissible3j j₁ j₂ j₃ m₁ m₂ (-m₁ - m₂)
  · have h' := hiff.mp h
    rw [w34_wigner3j_eq h, w34_wigner3j_eq h']
    obtain ⟨⟨⟨a₁, ha₁⟩, -, -⟩, ⟨⟨p₁, hp₁⟩, ⟨q₁, hq₁⟩⟩, ⟨⟨p₂, hp₂⟩, ⟨q₂, hq₂⟩⟩,
      ⟨⟨p₃, hp₃⟩, ⟨q₃, hq₃⟩⟩, -⟩ := h
    have ha : 2 * a₁ + p₃ + q₃ = p₁ + q₁ + p₂ + q₂ := by
      exact_mod_cast (by linarith : 2 * (a₁ : ℚ) + p₃ + q₃ = p₁ + q₁ + p₂ + q₂)
    have e : w34_S (j₁ + j₂ - j₃) (j₁ - -m₁) (j₂ + -m₂) 0 (j₂ - j₃ - -m₁) (j₁ - j₃ + -m₂) =
        w34_S (-0 + (j₁ + j₂ - j₃)) (-(j₂ - j₃ - m₁) + (j₁ + j₂ - j₃))
          (-(j₁ - j₃ + m₂) + (j₁ + j₂ - j₃)) (-(j₁ + j₂ - j₃) + (j₁ + j₂ - j₃))
          (-(j₁ - m₁) + (j₁ + j₂ - j₃)) (-(j₂ + m₂) + (j₁ + j₂ - j₃)) := by
      congr 1 <;> ring
    rw [e, w34_S_shift _ _ _ _ _ _ _ (a₁ : ℤ) (by push_cast; linarith), ← w34_S_neg,
      signPow_of_eq (x := j₁ - j₂ - (-m₁ - m₂)) (n := (q₁ : ℤ) - p₂) (by push_cast; linarith),
      signPow_of_eq (x := j₁ - j₂ - -(-m₁ - m₂)) (n := (p₁ : ℤ) - q₂) (by push_cast; linarith),
      signPow_of_eq (x := j₁ + j₂ + j₃) (n := (a₁ : ℤ) + p₃ + q₃) (by push_cast; linarith)]
    have hs : (-1 : ℝ) ^ ((a₁ : ℤ) + p₃ + q₃) * ((-1) ^ ((p₁ : ℤ) - q₂) * (-1) ^ (a₁ : ℤ)) =
        (-1) ^ ((q₁ : ℤ) - p₂) := by
      rw [← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num)]
      exact w34_neg_one_zpow_eq ((p₁ : ℤ) + p₂) (by omega)
    rw [← hs]
    ring_nf
  · rw [wigner3j_of_not h, wigner3j_of_not (mt hiff.mpr h), mul_zero]

/-- DLMF 34.3.4–34.3.5, `J = j₁ + j₂ + j₃` odd: `(j₁ j₂ j₃; 0 0 0) = 0`. The projections
`m = 0` require integer `jᵣ`. -/
@[dlmf 34.3.E4, dlmf 34.3.E5]
theorem wigner3j_zero_zero_zero_of_odd {j₁ j₂ j₃ : ℚ} (n : ℕ)
    (hJ : j₁ + j₂ + j₃ = 2 * n + 1) : wigner3j j₁ j₂ j₃ 0 0 0 = 0 := by
  have h := wigner3j_neg j₁ j₂ j₃ 0 0 0
  rw [neg_zero, signPow_of_eq (n := 2 * (n : ℤ) + 1) (by rw [hJ]; push_cast; ring),
    zpow_add₀ (by norm_num), zpow_mul] at h
  norm_num at h
  linarith

/-- DLMF 34.3.11: a Regge symmetry. -/
@[dlmf 34.3.E11]
theorem wigner3j_regge₁ (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ) :
    wigner3j j₁ j₂ j₃ m₁ m₂ m₃ =
      wigner3j j₁ ((j₂ + j₃ + m₁) / 2) ((j₂ + j₃ - m₁) / 2) (j₂ - j₃)
        ((j₃ - j₂ + m₁) / 2 + m₂) ((j₃ - j₂ + m₁) / 2 + m₃) := by
  by_cases hm : m₁ + m₂ + m₃ = 0
  swap
  · rw [w34_wigner3j_sum_ne hm, w34_wigner3j_sum_ne (fun h => hm (by linarith))]
  obtain rfl : m₃ = -m₁ - m₂ := by linarith
  have hiff : IsAdmissible3j j₁ j₂ j₃ m₁ m₂ (-m₁ - m₂) ↔
      IsAdmissible3j j₁ ((j₂ + j₃ + m₁) / 2) ((j₂ + j₃ - m₁) / 2) (j₂ - j₃)
        ((j₃ - j₂ + m₁) / 2 + m₂) ((j₃ - j₂ + m₁) / 2 + (-m₁ - m₂)) := by
    unfold IsAdmissible3j IsTriad IsProjection
    constructor <;> rintro ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, ⟨h6, h7⟩, ⟨h8, h9⟩, -⟩ <;>
      exact ⟨⟨by w34_pick9, by w34_pick9, by w34_pick9⟩, ⟨by w34_pick9, by w34_pick9⟩,
        ⟨by w34_pick9, by w34_pick9⟩, ⟨by w34_pick9, by w34_pick9⟩, by ring⟩
  by_cases h : IsAdmissible3j j₁ j₂ j₃ m₁ m₂ (-m₁ - m₂)
  · have h' := hiff.mp h
    rw [w34_wigner3j_eq h, w34_wigner3j_eq h']
    obtain ⟨-, ⟨⟨p₁, hp₁⟩, ⟨q₁, hq₁⟩⟩, ⟨⟨p₂, hp₂⟩, ⟨q₂, hq₂⟩⟩, ⟨⟨p₃, hp₃⟩, ⟨q₃, hq₃⟩⟩, -⟩ := h
    have hpq : q₁ + q₂ + q₃ = p₁ + p₂ + p₃ := by
      exact_mod_cast (by linarith : (q₁ : ℚ) + q₂ + q₃ = p₁ + p₂ + p₃)
    have e : w34_S (j₁ + (j₂ + j₃ + m₁) / 2 - (j₂ + j₃ - m₁) / 2) (j₁ - (j₂ - j₃))
        ((j₂ + j₃ + m₁) / 2 + ((j₃ - j₂ + m₁) / 2 + m₂)) 0
        ((j₂ + j₃ + m₁) / 2 - (j₂ + j₃ - m₁) / 2 - (j₂ - j₃))
        (j₁ - (j₂ + j₃ - m₁) / 2 + ((j₃ - j₂ + m₁) / 2 + m₂)) =
        w34_S ((j₁ + j₂ - j₃) + (j₃ - j₂ + m₁)) ((j₁ - m₁) + (j₃ - j₂ + m₁))
          ((j₂ + m₂) + (j₃ - j₂ + m₁)) ((j₂ - j₃ - m₁) + (j₃ - j₂ + m₁))
          (0 + (j₃ - j₂ + m₁)) ((j₁ - j₃ + m₂) + (j₃ - j₂ + m₁)) := by
      congr 1 <;> ring
    rw [e, w34_S_shift _ _ _ _ _ _ _ ((p₃ : ℤ) - q₂) (by push_cast; linarith), ← w34_S_swap_y12,
      signPow_of_eq (x := j₁ - j₂ - (-m₁ - m₂)) (n := (q₁ : ℤ) - p₂) (by push_cast; linarith),
      signPow_of_eq (x := j₁ - (j₂ + j₃ + m₁) / 2 - ((j₃ - j₂ + m₁) / 2 + (-m₁ - m₂)))
        (n := (p₁ : ℤ) - q₃) (by push_cast; linarith)]
    have hs : (-1 : ℝ) ^ ((p₁ : ℤ) - q₃) * (-1) ^ ((p₃ : ℤ) - q₂) = (-1) ^ ((q₁ : ℤ) - p₂) := by
      rw [← zpow_add₀ (by norm_num)]
      exact w34_neg_one_zpow_eq 0 (by omega)
    rw [← hs]
    ring_nf
  · rw [wigner3j_of_not h, wigner3j_of_not (mt hiff.mpr h)]

/-- DLMF 34.3.12: a Regge symmetry. -/
@[dlmf 34.3.E12]
theorem wigner3j_regge₂ (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ) :
    wigner3j j₁ j₂ j₃ m₁ m₂ m₃ =
      wigner3j ((j₁ + j₂ - m₃) / 2) ((j₂ + j₃ - m₁) / 2) ((j₁ + j₃ - m₂) / 2)
        (j₃ - (j₁ + j₂ + m₃) / 2) (j₁ - (j₂ + j₃ + m₁) / 2) (j₂ - (j₁ + j₃ + m₂) / 2) := by
  by_cases hm : m₁ + m₂ + m₃ = 0
  swap
  · rw [w34_wigner3j_sum_ne hm, w34_wigner3j_sum_ne (fun h => hm (by linarith))]
  obtain rfl : m₃ = -m₁ - m₂ := by linarith
  have hiff : IsAdmissible3j j₁ j₂ j₃ m₁ m₂ (-m₁ - m₂) ↔
      IsAdmissible3j ((j₁ + j₂ - (-m₁ - m₂)) / 2) ((j₂ + j₃ - m₁) / 2) ((j₁ + j₃ - m₂) / 2)
        (j₃ - (j₁ + j₂ + (-m₁ - m₂)) / 2) (j₁ - (j₂ + j₃ + m₁) / 2)
        (j₂ - (j₁ + j₃ + m₂) / 2) := by
    unfold IsAdmissible3j IsTriad IsProjection
    constructor <;> rintro ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, ⟨h6, h7⟩, ⟨h8, h9⟩, -⟩ <;>
      exact ⟨⟨by w34_pick9, by w34_pick9, by w34_pick9⟩, ⟨by w34_pick9, by w34_pick9⟩,
        ⟨by w34_pick9, by w34_pick9⟩, ⟨by w34_pick9, by w34_pick9⟩, by ring⟩
  by_cases h : IsAdmissible3j j₁ j₂ j₃ m₁ m₂ (-m₁ - m₂)
  · have h' := hiff.mp h
    rw [w34_wigner3j_eq h, w34_wigner3j_eq h', w34_S_cycle_x, w34_S_cycle_x]
    ring_nf
  · rw [wigner3j_of_not h, wigner3j_of_not (mt hiff.mpr h)]

/-! ## §34.3(iii) Recursion relations -/

/-- `1/(t-1)! = t/t!` for an integer `t` (both sides vanish for `t ≤ 0`). -/
lemma q2w_invFactQ_sub_one {t : ℚ} {n : ℤ} (h : t = n) :
    invFactQ (t - 1) = (t : ℝ) * invFactQ t := by
  subst h
  rcases lt_or_ge n 1 with hn | hn
  · have hn1 : (n : ℚ) < 1 := by exact_mod_cast hn
    rw [invFactQ_of_neg (by linarith)]
    rcases lt_or_ge n 0 with hn' | hn'
    · rw [invFactQ_of_neg (by exact_mod_cast hn'), mul_zero]
    · have : n = 0 := by omega
      subst this; simp
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨(n - 1).toNat, by omega⟩
    rw [invFactQ_of_eq (n := k) (by push_cast; ring),
      invFactQ_of_eq (n := k + 1) (by push_cast; ring), Nat.factorial_succ]
    push_cast
    field_simp

/-- The summand of `w34_S` has finite support. -/
lemma q2w_S_support_finite (x₁ x₂ x₃ y₁ y₂ y₃ : ℚ) :
    (Function.support fun s : ℤ => (-1 : ℝ) ^ s * (invFactQ (x₁ - s) * invFactQ (x₂ - s) *
      invFactQ (x₃ - s) * (invFactQ (s - y₁) * invFactQ (s - y₂) * invFactQ (s - y₃)))).Finite := by
  apply (Set.finite_Icc (⌈y₁⌉) (⌊x₁⌋)).subset
  intro s hs
  simp only [Function.mem_support] at hs
  simp only [Set.mem_Icc]
  constructor
  · by_contra h
    apply hs
    rw [invFactQ_of_neg (x := (s : ℚ) - y₁) (by
      have : (s : ℚ) < y₁ := by
        rw [not_le, Int.lt_ceil] at h; exact h
      linarith)]
    ring
  · by_contra h
    apply hs
    rw [invFactQ_of_neg (x := x₁ - s) (by
      have : x₁ < (s : ℚ) := by
        rw [not_le, Int.floor_lt] at h; exact h
      linarith)]
    ring

/-- Contiguity of the symmetric Racah sum: lowering `x₃` and raising `y₃` by one. -/
lemma q2w_S_contiguous (x₁ x₂ y₁ y₂ : ℚ) {x₃ y₃ : ℚ} {n k : ℤ} (hx : x₃ = n) (hy : y₃ = k) :
    w34_S x₁ x₂ (x₃ - 1) y₁ y₂ y₃ + w34_S x₁ x₂ x₃ y₁ y₂ (y₃ + 1) =
      ((x₃ - y₃ : ℚ) : ℝ) * w34_S x₁ x₂ x₃ y₁ y₂ y₃ := by
  unfold w34_S
  rw [← finsum_add_distrib (q2w_S_support_finite _ _ _ _ _ _) (q2w_S_support_finite _ _ _ _ _ _),
    mul_finsum]
  refine finsum_congr fun s => ?_
  rw [show x₃ - 1 - s = (x₃ - s) - 1 by ring, show (s : ℚ) - (y₃ + 1) = (s - y₃) - 1 by ring,
    q2w_invFactQ_sub_one (n := n - s) (by rw [hx]; push_cast; ring),
    q2w_invFactQ_sub_one (n := s - k) (by rw [hy]; push_cast; ring)]
  push_cast
  ring

/-- The symmetric Racah sum vanishes when `x₃ < y₂`. -/
lemma q2w_S_eq_zero_of_lt (x₁ x₂ y₁ y₃ : ℚ) {x₃ y₂ : ℚ} (h : x₃ < y₂) :
    w34_S x₁ x₂ x₃ y₁ y₂ y₃ = 0 := by
  unfold w34_S
  convert finsum_zero with s
  rcases lt_or_ge (x₃ - s) 0 with h' | h'
  · rw [invFactQ_of_neg h']; ring
  · rw [invFactQ_of_neg (x := (s : ℚ) - y₂) (by linarith)]; ring


/-- DLMF 34.3.13. Stated for all arguments (stronger than DLMF, which assumes the triangle
conditions for each symbol). -/
@[dlmf 34.3.E13]
theorem wigner3j_recursion_half (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ) :
    Real.sqrt ((j₁ + j₂ + j₃ + 1) * (-j₁ + j₂ + j₃)) * wigner3j j₁ j₂ j₃ m₁ m₂ m₃ =
      Real.sqrt ((j₂ + m₂) * (j₃ - m₃)) *
          wigner3j j₁ (j₂ - 1 / 2) (j₃ - 1 / 2) m₁ (m₂ - 1 / 2) (m₃ + 1 / 2) -
        Real.sqrt ((j₂ - m₂) * (j₃ + m₃)) *
          wigner3j j₁ (j₂ - 1 / 2) (j₃ - 1 / 2) m₁ (m₂ + 1 / 2) (m₃ - 1 / 2) := by
  have one : IsNatQ 1 := ⟨1, by simp⟩
  by_cases hL : IsAdmissible3j j₁ j₂ j₃ m₁ m₂ m₃
  swap
  · have h1 : ¬ IsAdmissible3j j₁ (j₂ - 1 / 2) (j₃ - 1 / 2) m₁ (m₂ - 1 / 2) (m₃ + 1 / 2) := by
      rintro ⟨⟨t1, t2, t3⟩, p1, ⟨p2a, p2b⟩, ⟨p3a, p3b⟩, hs⟩
      exact hL ⟨⟨t1.of_eq (by ring), t2.of_eq (by ring), (t3.add one).of_eq (by ring)⟩, p1,
        ⟨p2a.of_eq (by ring), (p2b.add one).of_eq (by ring)⟩,
        ⟨(p3a.add one).of_eq (by ring), p3b.of_eq (by ring)⟩, by linarith⟩
    have h2 : ¬ IsAdmissible3j j₁ (j₂ - 1 / 2) (j₃ - 1 / 2) m₁ (m₂ + 1 / 2) (m₃ - 1 / 2) := by
      rintro ⟨⟨t1, t2, t3⟩, p1, ⟨p2a, p2b⟩, ⟨p3a, p3b⟩, hs⟩
      exact hL ⟨⟨t1.of_eq (by ring), t2.of_eq (by ring), (t3.add one).of_eq (by ring)⟩, p1,
        ⟨(p2a.add one).of_eq (by ring), p2b.of_eq (by ring)⟩,
        ⟨p3a.of_eq (by ring), (p3b.add one).of_eq (by ring)⟩, by linarith⟩
    rw [wigner3j_of_not hL, wigner3j_of_not h1, wigner3j_of_not h2]; ring
  have hL' := hL
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩, ⟨⟨p₁, hp₁⟩, ⟨q₁, hq₁⟩⟩, ⟨⟨p₂, hp₂⟩, ⟨q₂, hq₂⟩⟩,
    ⟨⟨p₃, hp₃⟩, ⟨q₃, hq₃⟩⟩, hm⟩ := hL'
  rcases c with _ | w
  · have h1 : ¬ IsAdmissible3j j₁ (j₂ - 1 / 2) (j₃ - 1 / 2) m₁ (m₂ - 1 / 2) (m₃ + 1 / 2) := by
      rintro ⟨⟨-, -, t3⟩, -⟩
      have := t3.nonneg; push_cast at hc; linarith
    have h2 : ¬ IsAdmissible3j j₁ (j₂ - 1 / 2) (j₃ - 1 / 2) m₁ (m₂ + 1 / 2) (m₃ - 1 / 2) := by
      rintro ⟨⟨-, -, t3⟩, -⟩
      have := t3.nonneg; push_cast at hc; linarith
    rw [wigner3j_of_not h1, wigner3j_of_not h2,
      show (-(j₁ : ℝ) + j₂ + j₃) = 0 by
        have := congrArg (Rat.cast : ℚ → ℝ) hc; push_cast at this; linarith]
    simp
  have hR : ∀ {x : ℚ} {n : ℕ}, x = n → (x : ℝ) = n := fun h => by rw [h]; simp
  have hJ : j₁ + j₂ + j₃ + 1 = ((a + b + w + 2 : ℕ) : ℚ) := by push_cast at hc ⊢; linarith
  set PL : ℝ := factQ (j₁ + j₂ - j₃) * factQ (j₁ - j₂ + j₃) * factQ (-j₁ + j₂ + j₃) /
          factQ (j₁ + j₂ + j₃ + 1) * (factQ (j₁ + m₁) * factQ (j₁ - m₁) * factQ (j₂ + m₂) *
          factQ (j₂ - m₂) * factQ (j₃ + m₃) * factQ (j₃ - m₃)) with hPL
  set K : ℝ := signPow (j₁ - j₂ - m₃) * Real.sqrt PL *
    Real.sqrt (((a + b + w + 2 : ℕ) : ℝ) / ((w + 1 : ℕ) : ℝ)) with hK
  have e1 : Real.sqrt ((j₂ + m₂) * (j₃ - m₃)) *
      wigner3j j₁ (j₂ - 1 / 2) (j₃ - 1 / 2) m₁ (m₂ - 1 / 2) (m₃ + 1 / 2) =
      K * w34_S (j₁ + j₂ - j₃) (j₁ - m₁) ((j₂ + m₂) - 1) 0 (j₂ - j₃ - m₁) (j₁ - j₃ + m₂) := by
    rcases q₂ with _ | u
    · rw [w34_S_swap_y12, q2w_S_eq_zero_of_lt _ _ _ _ (by push_cast at hq₂; linarith),
        show ((j₂ : ℝ) + m₂) = 0 by have := hR hq₂; push_cast at this; linarith]
      simp
    rcases p₃ with _ | v
    · rw [q2w_S_eq_zero_of_lt _ _ _ _ (by push_cast at hq₂ hp₃; linarith),
        show ((j₃ : ℝ) - m₃) = 0 by have := hR hp₃; push_cast at this; linarith]
      simp
    have hR1 : IsAdmissible3j j₁ (j₂ - 1 / 2) (j₃ - 1 / 2) m₁ (m₂ - 1 / 2) (m₃ + 1 / 2) :=
      ⟨⟨⟨a, by linarith⟩, ⟨b, by linarith⟩, ⟨w, by push_cast at hc ⊢; linarith⟩⟩,
        ⟨⟨p₁, hp₁⟩, ⟨q₁, hq₁⟩⟩, ⟨⟨p₂, by linarith⟩, ⟨u, by push_cast at hq₂ ⊢; linarith⟩⟩,
        ⟨⟨v, by push_cast at hp₃ ⊢; linarith⟩, ⟨q₃, by linarith⟩⟩, by linarith⟩
    rw [w34_wigner3j_eq hR1, show j₁ - (j₂ - 1 / 2) - (m₃ + 1 / 2) = j₁ - j₂ - m₃ by ring,
      show w34_S (j₁ + (j₂ - 1 / 2) - (j₃ - 1 / 2)) (j₁ - m₁) (j₂ - 1 / 2 + (m₂ - 1 / 2)) 0
        (j₂ - 1 / 2 - (j₃ - 1 / 2) - m₁) (j₁ - (j₃ - 1 / 2) + (m₂ - 1 / 2)) =
        w34_S (j₁ + j₂ - j₃) (j₁ - m₁) ((j₂ + m₂) - 1) 0 (j₂ - j₃ - m₁) (j₁ - j₃ + m₂) by
          congr 1 <;> ring, hK,
      show ∀ c s Q S : ℝ, c * (s * Q * S) = s * (c * Q) * S from fun _ _ _ _ => by ring]
    congr 1
    rw [mul_assoc (signPow (j₁ - j₂ - m₃))]
    congr 1
    have hu : (j₂ : ℝ) + m₂ = (u : ℝ) + 1 := by have := hR hq₂; push_cast at this; linarith
    have hv : (j₃ : ℝ) - m₃ = (v : ℝ) + 1 := by have := hR hp₃; push_cast at this; linarith
    have hPL0 : 0 ≤ PL := by rw [hPL]; q2w_nonneg
    rw [hu, hv, ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul hPL0, hPL]
    congr 1
    rw [factQ_of_eq (n := a) (show j₁ + (j₂ - 1 / 2) - (j₃ - 1 / 2) = (a : ℚ) by linarith),
      factQ_of_eq (n := b) (show j₁ - (j₂ - 1 / 2) + (j₃ - 1 / 2) = (b : ℚ) by linarith),
      factQ_of_eq (n := w) (show -j₁ + (j₂ - 1 / 2) + (j₃ - 1 / 2) = (w : ℚ) by
        push_cast at hc; linarith),
      factQ_of_eq (n := a + b + w + 1) (show j₁ + (j₂ - 1 / 2) + (j₃ - 1 / 2) + 1 =
        ((a + b + w + 1 : ℕ) : ℚ) by push_cast at hJ ⊢; linarith),
      factQ_of_eq (n := u) (show j₂ - 1 / 2 + (m₂ - 1 / 2) = (u : ℚ) by
        push_cast at hq₂; linarith),
      factQ_of_eq (n := p₂) (show j₂ - 1 / 2 - (m₂ - 1 / 2) = (p₂ : ℚ) by linarith),
      factQ_of_eq (n := q₃) (show j₃ - 1 / 2 + (m₃ + 1 / 2) = (q₃ : ℚ) by linarith),
      factQ_of_eq (n := v) (show j₃ - 1 / 2 - (m₃ + 1 / 2) = (v : ℚ) by
        push_cast at hp₃; linarith),
      ha, hb, hc, hJ, hq₁, hp₁, hq₂, hp₂, hq₃, hp₃]
    simp only [factQ_natCast, Nat.factorial_succ, show a + b + w + 2 = (a + b + w + 1) + 1 from rfl]
    push_cast
    field_simp
  have e2 : Real.sqrt ((j₂ - m₂) * (j₃ + m₃)) *
      wigner3j j₁ (j₂ - 1 / 2) (j₃ - 1 / 2) m₁ (m₂ + 1 / 2) (m₃ - 1 / 2) =
      -K * w34_S (j₁ + j₂ - j₃) (j₁ - m₁) (j₂ + m₂) 0 (j₂ - j₃ - m₁) ((j₁ - j₃ + m₂) + 1) := by
    rcases p₂ with _ | u
    · rw [w34_S_swap_x12, w34_S_swap_x23, w34_S_swap_y23,
        q2w_S_eq_zero_of_lt _ _ _ _ (by push_cast at hp₂; linarith),
        show ((j₂ : ℝ) - m₂) = 0 by have := hR hp₂; push_cast at this; linarith]
      simp
    rcases q₃ with _ | v
    · rw [w34_S_swap_x23, w34_S_swap_y23,
        q2w_S_eq_zero_of_lt _ _ _ _ (by push_cast at hq₃; linarith),
        show ((j₃ : ℝ) + m₃) = 0 by have := hR hq₃; push_cast at this; linarith]
      simp
    have hR2 : IsAdmissible3j j₁ (j₂ - 1 / 2) (j₃ - 1 / 2) m₁ (m₂ + 1 / 2) (m₃ - 1 / 2) :=
      ⟨⟨⟨a, by linarith⟩, ⟨b, by linarith⟩, ⟨w, by push_cast at hc ⊢; linarith⟩⟩,
        ⟨⟨p₁, hp₁⟩, ⟨q₁, hq₁⟩⟩, ⟨⟨u, by push_cast at hp₂ ⊢; linarith⟩, ⟨q₂, by linarith⟩⟩,
        ⟨⟨p₃, by linarith⟩, ⟨v, by push_cast at hq₃ ⊢; linarith⟩⟩, by linarith⟩
    rw [w34_wigner3j_eq hR2,
      show j₁ - (j₂ - 1 / 2) - (m₃ - 1 / 2) = j₁ - j₂ - m₃ + ((1 : ℤ) : ℚ) by push_cast; ring,
      signPow_add_intCast, zpow_one,
      show w34_S (j₁ + (j₂ - 1 / 2) - (j₃ - 1 / 2)) (j₁ - m₁) (j₂ - 1 / 2 + (m₂ + 1 / 2)) 0
        (j₂ - 1 / 2 - (j₃ - 1 / 2) - m₁) (j₁ - (j₃ - 1 / 2) + (m₂ + 1 / 2)) =
        w34_S (j₁ + j₂ - j₃) (j₁ - m₁) (j₂ + m₂) 0 (j₂ - j₃ - m₁) ((j₁ - j₃ + m₂) + 1) by
          congr 1 <;> ring, hK, neg_mul,
      show ∀ c s Q S : ℝ, c * (s * (-1) * Q * S) = -(s * (c * Q) * S) from
        fun _ _ _ _ => by ring]
    congr 2
    rw [mul_assoc (signPow (j₁ - j₂ - m₃))]
    congr 1
    have hu : (j₂ : ℝ) - m₂ = (u : ℝ) + 1 := by have := hR hp₂; push_cast at this; linarith
    have hv : (j₃ : ℝ) + m₃ = (v : ℝ) + 1 := by have := hR hq₃; push_cast at this; linarith
    have hPL0 : 0 ≤ PL := by rw [hPL]; q2w_nonneg
    rw [hu, hv, ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul hPL0, hPL]
    congr 1
    rw [factQ_of_eq (n := a) (show j₁ + (j₂ - 1 / 2) - (j₃ - 1 / 2) = (a : ℚ) by linarith),
      factQ_of_eq (n := b) (show j₁ - (j₂ - 1 / 2) + (j₃ - 1 / 2) = (b : ℚ) by linarith),
      factQ_of_eq (n := w) (show -j₁ + (j₂ - 1 / 2) + (j₃ - 1 / 2) = (w : ℚ) by
        push_cast at hc; linarith),
      factQ_of_eq (n := a + b + w + 1) (show j₁ + (j₂ - 1 / 2) + (j₃ - 1 / 2) + 1 =
        ((a + b + w + 1 : ℕ) : ℚ) by push_cast at hJ ⊢; linarith),
      factQ_of_eq (n := q₂) (show j₂ - 1 / 2 + (m₂ + 1 / 2) = (q₂ : ℚ) by linarith),
      factQ_of_eq (n := u) (show j₂ - 1 / 2 - (m₂ + 1 / 2) = (u : ℚ) by
        push_cast at hp₂; linarith),
      factQ_of_eq (n := v) (show j₃ - 1 / 2 + (m₃ - 1 / 2) = (v : ℚ) by
        push_cast at hq₃; linarith),
      factQ_of_eq (n := p₃) (show j₃ - 1 / 2 - (m₃ - 1 / 2) = (p₃ : ℚ) by linarith),
      ha, hb, hc, hJ, hq₁, hp₁, hq₂, hp₂, hq₃, hp₃]
    simp only [factQ_natCast, Nat.factorial_succ, show a + b + w + 2 = (a + b + w + 1) + 1 from rfl]
    push_cast
    field_simp
  rw [e1, e2, w34_wigner3j_eq hL, ← hPL, show ∀ x y : ℝ, K * x - -K * y = K * (x + y) from
    fun x y => by ring, q2w_S_contiguous _ _ _ _ hq₂ (n := q₂) (k := (a : ℤ) - p₂) (by
      push_cast; linarith), hK]
  have hcR : (-(j₁ : ℝ) + j₂ + j₃) = ((w + 1 : ℕ) : ℝ) := by
    have := hR hc; push_cast at this ⊢; linarith
  have hJR : ((j₁ : ℝ) + j₂ + j₃ + 1) = ((a + b + w + 2 : ℕ) : ℝ) := by
    have := hR hJ; push_cast at this ⊢; linarith
  rw [hcR, hJR, show (((j₂ + m₂) - (j₁ - j₃ + m₂) : ℚ) : ℝ) = ((w + 1 : ℕ) : ℝ) by
    rw [show (j₂ + m₂) - (j₁ - j₃ + m₂) = -j₁ + j₂ + j₃ by ring, hR hc]]
  have hw : (0 : ℝ) < ((w + 1 : ℕ) : ℝ) := by positivity
  rw [Real.sqrt_mul (by positivity), Real.sqrt_div (by positivity)]
  have hs : Real.sqrt ((w + 1 : ℕ) : ℝ) ^ 2 = ((w + 1 : ℕ) : ℝ) := Real.sq_sqrt hw.le
  have hs0 : Real.sqrt ((w + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  rw [hs]
  ring

/-- DLMF 34.3.14. Stated for all arguments (stronger than DLMF). -/
@[dlmf 34.3.E14]
theorem wigner3j_recursion_m (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ) :
    ((j₁ * (j₁ + 1) - j₂ * (j₂ + 1) - j₃ * (j₃ + 1) - 2 * m₂ * m₃ : ℚ) : ℝ) *
        wigner3j j₁ j₂ j₃ m₁ m₂ m₃ =
      Real.sqrt ((j₂ - m₂) * (j₂ + m₂ + 1) * (j₃ - m₃ + 1) * (j₃ + m₃)) *
          wigner3j j₁ j₂ j₃ m₁ (m₂ + 1) (m₃ - 1) +
        Real.sqrt ((j₂ - m₂ + 1) * (j₂ + m₂) * (j₃ - m₃) * (j₃ + m₃ + 1)) *
          wigner3j j₁ j₂ j₃ m₁ (m₂ - 1) (m₃ + 1) := by
  sorry

/-- DLMF 34.3.15. Stated for all arguments (stronger than DLMF). -/
@[dlmf 34.3.E15]
theorem wigner3j_recursion_j (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ) :
    ((2 * j₁ + 1) * ((j₂ * (j₂ + 1) - j₃ * (j₃ + 1)) * m₁ - j₁ * (j₁ + 1) * (m₃ - m₂)) : ℚ) *
        wigner3j j₁ j₂ j₃ m₁ m₂ m₃ =
      ((j₁ + 1 : ℚ) : ℝ) * Real.sqrt (j₁ ^ 2 - (j₂ - j₃) ^ 2) *
          Real.sqrt ((j₂ + j₃ + 1) ^ 2 - j₁ ^ 2) * Real.sqrt (j₁ ^ 2 - m₁ ^ 2) *
          wigner3j (j₁ - 1) j₂ j₃ m₁ m₂ m₃ +
        (j₁ : ℝ) * Real.sqrt ((j₁ + 1) ^ 2 - (j₂ - j₃) ^ 2) *
          Real.sqrt ((j₂ + j₃ + 1) ^ 2 - (j₁ + 1) ^ 2) * Real.sqrt ((j₁ + 1) ^ 2 - m₁ ^ 2) *
          wigner3j (j₁ + 1) j₂ j₃ m₁ m₂ m₃ := by
  sorry

/-! ## §34.3(iv) Orthogonality

The summations run over the admissible values (34.2.1–34.2.3): `mᵣ ∈ projections jᵣ`, and
`j₃` over the half-integers `0, 1/2, …, j₁ + j₂` (`halfIntegersUpTo`); the summands vanish
outside the admissible range. -/

/-- DLMF 34.3.16. -/
@[dlmf 34.3.E16]
theorem wigner3j_orthogonality_m {j₁ j₂ j₃ m₃ : ℚ} (h : IsTriad j₁ j₂ j₃)
    (hm : IsProjection j₃ m₃) (j₃' m₃' : ℚ) :
    ∑ m₁ ∈ projections j₁, ∑ m₂ ∈ projections j₂,
        (2 * (j₃ : ℝ) + 1) * wigner3j j₁ j₂ j₃ m₁ m₂ m₃ * wigner3j j₁ j₂ j₃' m₁ m₂ m₃' =
      if j₃ = j₃' ∧ m₃ = m₃' then 1 else 0 := by
  sorry

/-- DLMF 34.3.17. -/
@[dlmf 34.3.E17]
theorem wigner3j_orthogonality_j {j₁ j₂ m₁ m₂ : ℚ} (h₁ : IsProjection j₁ m₁)
    (h₂ : IsProjection j₂ m₂) (m₁' m₂' : ℚ) :
    ∑ j₃ ∈ halfIntegersUpTo (j₁ + j₂), ∑ m₃ ∈ projections j₃,
        (2 * (j₃ : ℝ) + 1) * wigner3j j₁ j₂ j₃ m₁ m₂ m₃ * wigner3j j₁ j₂ j₃ m₁' m₂' m₃ =
      if m₁ = m₁' ∧ m₂ = m₂' then 1 else 0 := by
  sorry

/-- DLMF 34.3.18. -/
@[dlmf 34.3.E18]
theorem wigner3j_sum_sq {j₁ j₂ j₃ : ℚ} (h : IsTriad j₁ j₂ j₃) :
    ∑ m₁ ∈ projections j₁, ∑ m₂ ∈ projections j₂, ∑ m₃ ∈ projections j₃,
        wigner3j j₁ j₂ j₃ m₁ m₂ m₃ * wigner3j j₁ j₂ j₃ m₁ m₂ m₃ = 1 := by
  sorry

/-! ## §34.10 Zeros -/

/-- DLMF §34.10: a nontrivial zero. The triangle conditions hold for `(1, 1, 1)` and
`0 + 0 + 0 = 0`, but `(1 1 1; 0 0 0) = 0`. -/
@[dlmf 34.10]
theorem wigner3j_one_one_one_zero : IsAdmissible3j 1 1 1 0 0 0 ∧ wigner3j 1 1 1 0 0 0 = 0 := by
  refine ⟨⟨⟨⟨1, by norm_num⟩, ⟨1, by norm_num⟩, ⟨1, by norm_num⟩⟩, ⟨⟨1, by norm_num⟩,
    ⟨1, by norm_num⟩⟩, ⟨⟨1, by norm_num⟩, ⟨1, by norm_num⟩⟩, ⟨⟨1, by norm_num⟩,
    ⟨1, by norm_num⟩⟩, by norm_num⟩, ?_⟩
  exact wigner3j_zero_zero_zero_of_odd 1 (by norm_num)

end DLMF.WignerSymbols
