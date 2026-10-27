/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Wigner `3j`, `6j` and `9j` symbols: definitions (DLMF Chapter 34)

This file holds the definitions of DLMF Chapter 34 (namespace `DLMF.WignerSymbols`).

## Representation

Angular momenta `j` and projective quantum numbers `m` are rational numbers. DLMF's
standing conditions are predicates:

* `IsNatQ x`: `x` is a nonnegative integer; `IsAngularMomentum j`: `2j ∈ ℕ`;
* `IsProjection j m` (34.2.2): `j - m ∈ ℕ` and `j + m ∈ ℕ`, i.e. `m ∈ {-j, -j+1, …, j}`;
* `IsTriad j₁ j₂ j₃` (34.2.1 with the parity condition of §34.2): the three numbers
  `j₁ + j₂ - j₃`, `j₁ - j₂ + j₃`, `-j₁ + j₂ + j₃` are nonnegative integers. This is
  equivalent to: each `jᵣ` is a nonnegative integer or half-odd integer, the triangle
  conditions hold, and `j₁ + j₂ + j₃` is an integer (`isTriad_iff` in
  `DLMF.WignerSymbols.ThreeJ`).

Factorials, reciprocal factorials and signs of rational arguments are `factQ`, `invFactQ`
and `signPow`; they are only used at integer arguments, where they are `n!`, `1/n!`
(`0` for negative `n`) and `(-1)ⁿ`.

## Definitions

* `wigner3j j₁ j₂ j₃ m₁ m₂ m₃` (34.2.4, Racah's formula with `triangleDelta` of 34.2.5). It is
  `0` unless `IsAdmissible3j` holds: the triangle conditions (34.2.1), the projection
  conditions (34.2.2) and `m₁ + m₂ + m₃ = 0` (34.2.3). DLMF: "If either of the conditions
  (34.2.1) or (34.2.3) is not satisfied, then the 3j symbol is zero"; outside the
  projection ranges 34.2.2 DLMF defines nothing and the value `0` is the convention used by
  all summation formulas of the chapter.
* `clebschGordan` (34.1.1).
* `wigner6j` (34.4.2, the single-sum formula), zero unless the four triads of 34.4.1 satisfy
  the triangle conditions (DLMF §34.10).
* `wigner9j` (34.6.2, the sum of products of three `6j` symbols).
* `projections j`, `halfIntegersUpTo x`: the finite ranges of summation used in the
  orthogonality relations and sum rules.
* `largeParameterAngle` (34.8.2).
* `sixJRecursionE` (34.5.13), the coefficient of the three-term `6j` recursion 34.5.12.
* `w34_S`: an internal helper, the Racah sum of 34.2.4 written symmetrically as a `finsum`
  over `ℤ`; it is used to prove the symmetries of the `3j` symbol.
-/

@[expose] public noncomputable section

open Finset

namespace DLMF.WignerSymbols

/-! ## Integrality predicates -/

/-- The rational number `x` is a nonnegative integer. -/
def IsNatQ (x : ℚ) : Prop := ∃ n : ℕ, x = n

/-- An angular momentum (DLMF §34.1): `j` is a nonnegative integer or a nonnegative integer
plus one half, that is `2j ∈ ℕ`. -/
def IsAngularMomentum (j : ℚ) : Prop := IsNatQ (2 * j)

/-- DLMF 34.2.2: `m` is one of the projective quantum numbers `-j, -j + 1, …, j - 1, j`
of the angular momentum `j`; equivalently `j - m` and `j + m` are nonnegative integers. -/
@[dlmf 34.2.E2]
def IsProjection (j m : ℚ) : Prop := IsNatQ (j - m) ∧ IsNatQ (j + m)

/-- DLMF 34.2.1 together with the parity condition of §34.2: `j₁, j₂, j₃` are angular momenta
(all integers, or one integer and two half-odd integers) forming the sides of a possibly
degenerate triangle. Encoded as: `j₁ + j₂ - j₃`, `j₁ - j₂ + j₃` and `-j₁ + j₂ + j₃` are
nonnegative integers (see `isTriad_iff` for the equivalence with DLMF's wording). -/
@[dlmf 34.2.E1]
def IsTriad (j₁ j₂ j₃ : ℚ) : Prop :=
  IsNatQ (j₁ + j₂ - j₃) ∧ IsNatQ (j₁ - j₂ + j₃) ∧ IsNatQ (-j₁ + j₂ + j₃)

/-- The conditions 34.2.1–34.2.3 under which the `3j` symbol is given by 34.2.4. -/
def IsAdmissible3j (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ) : Prop :=
  IsTriad j₁ j₂ j₃ ∧ IsProjection j₁ m₁ ∧ IsProjection j₂ m₂ ∧ IsProjection j₃ m₃ ∧
    m₁ + m₂ + m₃ = 0

/-- The four triangle conditions of the `6j` symbol (the triads of the four `3j` symbols in
34.4.1). -/
def IsAdmissible6j (j₁ j₂ j₃ l₁ l₂ l₃ : ℚ) : Prop :=
  IsTriad j₁ j₂ j₃ ∧ IsTriad j₁ l₂ l₃ ∧ IsTriad l₁ j₂ l₃ ∧ IsTriad l₁ l₂ j₃

/-! ## Factorials and signs of rational arguments -/

/-- The factorial `x!` of a rational argument, `⌊x⌋.toNat !`. Only used where `x` is a
nonnegative integer. -/
def factQ (x : ℚ) : ℝ := ((⌊x⌋).toNat.factorial : ℝ)

/-- The reciprocal factorial `1/x!` of a rational argument, `0` for `x < 0` (the convention
`1/Γ(1 + x) = 0` at negative integers). It implements DLMF's "summation over all
nonnegative integers `s` such that the arguments in the factorials are nonnegative". -/
def invFactQ (x : ℚ) : ℝ := if 0 ≤ x then (factQ x)⁻¹ else 0

/-- The sign `(-1)^x`, as `(-1)^⌊x⌋`. Only used where `x` is an integer. -/
def signPow (x : ℚ) : ℝ := (-1 : ℝ) ^ ⌊x⌋

/-! ## The `3j` symbol -/

/-- DLMF 34.2.5: the triangle coefficient
`Δ(j₁ j₂ j₃) = ((j₁+j₂-j₃)! (j₁-j₂+j₃)! (-j₁+j₂+j₃)! / (j₁+j₂+j₃+1)!)^{1/2}`. -/
@[dlmf 34.2.E5]
def triangleDelta (j₁ j₂ j₃ : ℚ) : ℝ :=
  Real.sqrt (factQ (j₁ + j₂ - j₃) * factQ (j₁ - j₂ + j₃) * factQ (-j₁ + j₂ + j₃) /
    factQ (j₁ + j₂ + j₃ + 1))

/-- The summand of Racah's formula 34.2.4 at the summation index `s`. -/
def racahTerm3j (j₁ j₂ j₃ m₁ m₂ : ℚ) (s : ℕ) : ℝ :=
  (-1 : ℝ) ^ s * invFactQ s * invFactQ (j₁ + j₂ - j₃ - s) * invFactQ (j₁ - m₁ - s) *
    invFactQ (j₂ + m₂ - s) * invFactQ (j₃ - j₂ + m₁ + s) * invFactQ (j₃ - j₁ - m₂ + s)

/-- DLMF 34.2.4: the Wigner `3j` symbol
`(j₁ j₂ j₃; m₁ m₂ m₃)`, by Racah's finite sum. The summation index `s` runs over the
nonnegative integers with `s ≤ j₁ + j₂ - j₃`; the reciprocal factorials `invFactQ` vanish
where an argument is negative, so this is DLMF's sum over all `s` with nonnegative factorial
arguments. The symbol is `0` unless `IsAdmissible3j` (34.2.1–34.2.3) holds. -/
@[dlmf 34.2.E4]
def wigner3j (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ) : ℝ := by
  classical
  exact if IsAdmissible3j j₁ j₂ j₃ m₁ m₂ m₃ then
    signPow (j₁ - j₂ - m₃) * triangleDelta j₁ j₂ j₃ *
      Real.sqrt (factQ (j₁ + m₁) * factQ (j₁ - m₁) * factQ (j₂ + m₂) * factQ (j₂ - m₂) *
        factQ (j₃ + m₃) * factQ (j₃ - m₃)) *
      ∑ s ∈ range (⌊j₁ + j₂ - j₃⌋.toNat + 1), racahTerm3j j₁ j₂ j₃ m₁ m₂ s
  else 0

/-- DLMF 34.1.1: the Clebsch–Gordan coefficient
`(j₁ m₁ j₂ m₂ | j₁ j₂ j₃ m₃) = (-1)^{j₁-j₂+m₃} (2j₃+1)^{1/2} (j₁ j₂ j₃; m₁ m₂ -m₃)`. -/
@[dlmf 34.1.E1]
def clebschGordan (j₁ m₁ j₂ m₂ j₃ m₃ : ℚ) : ℝ :=
  signPow (j₁ - j₂ + m₃) * Real.sqrt (2 * (j₃ : ℝ) + 1) * wigner3j j₁ j₂ j₃ m₁ m₂ (-m₃)

/-- Racah's sum 34.2.4 in symmetric form: `∑_s (-1)^s / ∏ᵢ (xᵢ - s)! ∏ₖ (s - yₖ)!` over all
integers `s` (finitely many nonzero terms; `invFactQ` vanishes at negative arguments). A helper
for the symmetry relations of the `3j` symbol. -/
def w34_S (x₁ x₂ x₃ y₁ y₂ y₃ : ℚ) : ℝ :=
  ∑ᶠ s : ℤ, (-1 : ℝ) ^ s * (invFactQ (x₁ - s) * invFactQ (x₂ - s) * invFactQ (x₃ - s) *
    (invFactQ (s - y₁) * invFactQ (s - y₂) * invFactQ (s - y₃)))

/-! ## The `6j` symbol -/

/-- The summand of the single-sum formula 34.4.2 at the summation index `s`. -/
def racahTerm6j (j₁ j₂ j₃ l₁ l₂ l₃ : ℚ) (s : ℕ) : ℝ :=
  (-1 : ℝ) ^ s * ((s + 1).factorial : ℝ) *
    invFactQ (s - j₁ - j₂ - j₃) * invFactQ (s - j₁ - l₂ - l₃) * invFactQ (s - l₁ - j₂ - l₃) *
    invFactQ (s - l₁ - l₂ - j₃) * invFactQ (j₁ + j₂ + l₁ + l₂ - s) *
    invFactQ (j₂ + j₃ + l₂ + l₃ - s) * invFactQ (j₃ + j₁ + l₃ + l₁ - s)

/-- DLMF 34.4.2: the Wigner `6j` symbol `{j₁ j₂ j₃; l₁ l₂ l₃}`, by the single finite sum
(Racah). The index `s` runs over `0 ≤ s ≤ j₁ + j₂ + l₁ + l₂`, and the reciprocal factorials
vanish at negative arguments. The symbol is `0` unless the four triads of 34.4.1 satisfy the
triangle conditions (`IsAdmissible6j`; DLMF §34.10). DLMF 34.4.1 (the sum of products of four
`3j` symbols) is the theorem `wigner6j_eq_sum_threeJ`. -/
@[dlmf 34.4.E2]
def wigner6j (j₁ j₂ j₃ l₁ l₂ l₃ : ℚ) : ℝ := by
  classical
  exact if IsAdmissible6j j₁ j₂ j₃ l₁ l₂ l₃ then
    triangleDelta j₁ j₂ j₃ * triangleDelta j₁ l₂ l₃ * triangleDelta l₁ j₂ l₃ *
      triangleDelta l₁ l₂ j₃ *
      ∑ s ∈ range (⌊j₁ + j₂ + l₁ + l₂⌋.toNat + 1), racahTerm6j j₁ j₂ j₃ l₁ l₂ l₃ s
  else 0

/-- DLMF 34.5.13: the coefficient of the recursion relation 34.5.11,
`E(j) = ((j² - (j₂-j₃)²)((j₂+j₃+1)² - j²)(j² - (l₂-l₃)²)((l₂+l₃+1)² - j²))^{1/2}`. -/
@[dlmf 34.5.E13]
def sixJRecursionE (j₂ j₃ l₂ l₃ j : ℚ) : ℝ :=
  Real.sqrt (((j ^ 2 - (j₂ - j₃) ^ 2) * ((j₂ + j₃ + 1) ^ 2 - j ^ 2) * (j ^ 2 - (l₂ - l₃) ^ 2) *
    ((l₂ + l₃ + 1) ^ 2 - j ^ 2) : ℚ) : ℝ)

/-! ## The `9j` symbol -/

/-- DLMF 34.6.2: the Wigner `9j` symbol
`{j₁₁ j₁₂ j₁₃; j₂₁ j₂₂ j₂₃; j₃₁ j₃₂ j₃₃}`
`= ∑_j (-1)^{2j} (2j+1) {j₁₁ j₂₁ j₃₁; j₃₂ j₃₃ j} {j₁₂ j₂₂ j₃₂; j₂₁ j j₂₃} {j₁₃ j₂₃ j₃₃; j j₁₁ j₁₂}`.
The summation runs over `j = t/2`, `t = 0, 1, …, 2(j₁₁ + j₃₃)`; the first `6j` factor
vanishes unless `(j₁₁, j₃₃, j)` is a triad, so this is the sum over all admissible `j`.
DLMF 34.6.1 (the sum of products of six `3j` symbols) is `wigner9j_eq_sum_threeJ`. -/
@[dlmf 34.6.E2]
def wigner9j (j₁₁ j₁₂ j₁₃ j₂₁ j₂₂ j₂₃ j₃₁ j₃₂ j₃₃ : ℚ) : ℝ :=
  ∑ t ∈ range (⌊2 * (j₁₁ + j₃₃)⌋.toNat + 1),
    (-1 : ℝ) ^ t * ((t : ℝ) + 1) *
      wigner6j j₁₁ j₂₁ j₃₁ j₃₂ j₃₃ ((t : ℚ) / 2) *
      wigner6j j₁₂ j₂₂ j₃₂ j₂₁ ((t : ℚ) / 2) j₂₃ *
      wigner6j j₁₃ j₂₃ j₃₃ ((t : ℚ) / 2) j₁₁ j₁₂

/-! ## Summation ranges -/

/-- The projective quantum numbers `m = -j, -j + 1, …, j` of 34.2.2, as a finite set (empty
when `j < 0`). -/
def projections (j : ℚ) : Finset ℚ :=
  (range (⌊2 * j⌋.toNat + 1)).image fun k : ℕ => -j + k

/-- The nonnegative integers and half-odd integers `0, 1/2, 1, …` up to `x`, as a finite
set: the range of an angular momentum summation bounded by `x`. -/
def halfIntegersUpTo (x : ℚ) : Finset ℚ :=
  (range (⌊2 * x⌋.toNat + 1)).image fun t : ℕ => (t : ℚ) / 2

/-! ## Large parameters -/

/-- DLMF 34.8.2: the angle `θ ∈ [0, π]` of the approximation 34.8.1,
`cos θ = (j₁(j₁+1) + j₂(j₂+1) - j₃(j₃+1)) / (2 √(j₁(j₁+1) j₂(j₂+1)))`. -/
@[dlmf 34.8.E2]
def largeParameterAngle (j₁ j₂ j₃ : ℝ) : ℝ :=
  Real.arccos ((j₁ * (j₁ + 1) + j₂ * (j₂ + 1) - j₃ * (j₃ + 1)) /
    (2 * Real.sqrt (j₁ * (j₁ + 1) * j₂ * (j₂ + 1))))

/-! ## API for the rational factorials and signs -/

/-- `factQ` at a natural number is the factorial. -/
@[simp] theorem factQ_natCast (n : ℕ) : factQ n = (n.factorial : ℝ) := by
  simp [factQ]

/-- `factQ x = n!` when `x = n`. -/
theorem factQ_of_eq {x : ℚ} {n : ℕ} (h : x = n) : factQ x = (n.factorial : ℝ) := by
  rw [h, factQ_natCast]

/-- `invFactQ` at a natural number is the reciprocal factorial. -/
@[simp] theorem invFactQ_natCast (n : ℕ) : invFactQ n = ((n.factorial : ℝ))⁻¹ := by
  simp [invFactQ]

/-- `invFactQ x = 1/n!` when `x = n`. -/
theorem invFactQ_of_eq {x : ℚ} {n : ℕ} (h : x = n) : invFactQ x = ((n.factorial : ℝ))⁻¹ := by
  rw [h, invFactQ_natCast]

/-- `invFactQ` vanishes at negative arguments. -/
theorem invFactQ_of_neg {x : ℚ} (h : x < 0) : invFactQ x = 0 := by
  simp [invFactQ, not_le.mpr h]

/-- `invFactQ x = 0` exactly when `x < 0`. -/
theorem invFactQ_eq_zero_iff_neg {x : ℚ} : invFactQ x = 0 ↔ x < 0 := by
  unfold invFactQ factQ
  split_ifs with h
  · simp only [inv_eq_zero, Nat.cast_eq_zero]
    exact ⟨fun h' => absurd h' (Nat.factorial_ne_zero _), fun h' => absurd h' (not_lt.mpr h)⟩
  · simpa using h

/-- `signPow` at an integer is `(-1)ⁿ`. -/
@[simp] theorem signPow_intCast (n : ℤ) : signPow n = (-1 : ℝ) ^ n := by
  simp [signPow]

/-- `signPow` at a natural number is `(-1)ⁿ`. -/
@[simp] theorem signPow_natCast (n : ℕ) : signPow n = (-1 : ℝ) ^ n := by
  simp [signPow]

/-- `signPow x = (-1)ⁿ` when `x = n`. -/
theorem signPow_of_eq {x : ℚ} {n : ℤ} (h : x = n) : signPow x = (-1 : ℝ) ^ n := by
  rw [h, signPow_intCast]

/-- Shifting the argument of `signPow` by an integer `n` multiplies by `(-1)ⁿ`. -/
theorem signPow_add_intCast (x : ℚ) (n : ℤ) : signPow (x + n) = signPow x * (-1 : ℝ) ^ n := by
  rw [signPow, signPow, Int.floor_add_intCast, zpow_add₀ (by norm_num)]

/-- `signPow x` squares to `1`. -/
theorem signPow_sq (x : ℚ) : signPow x * signPow x = 1 := by
  rw [signPow, ← zpow_add₀ (by norm_num), ← two_mul, zpow_mul]
  norm_num

/-- Sign of an integer `x` given through `2x ∈ ℕ`. -/
theorem signPow_of_isNatQ_two_mul {x : ℚ} (h : IsNatQ (2 * x)) (hx : ∃ n : ℤ, x = n) :
    signPow (2 * x) = 1 := by
  obtain ⟨n, rfl⟩ := hx
  rw [show (2 : ℚ) * n = ((2 * n : ℤ) : ℚ) by push_cast; ring, signPow_intCast, zpow_mul]
  norm_num

/-- Natural-number rationals are nonnegative. -/
theorem IsNatQ.nonneg {x : ℚ} (h : IsNatQ x) : 0 ≤ x := by
  obtain ⟨n, rfl⟩ := h
  exact Nat.cast_nonneg n

/-- Natural-number casts satisfy `IsNatQ`. -/
theorem isNatQ_natCast (n : ℕ) : IsNatQ n := ⟨n, rfl⟩

/-- `IsNatQ` is closed under addition. -/
theorem IsNatQ.add {x y : ℚ} (hx : IsNatQ x) (hy : IsNatQ y) : IsNatQ (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, by push_cast; ring⟩

/-- Transport `IsNatQ` along an equality. -/
theorem IsNatQ.of_eq {x y : ℚ} (hx : IsNatQ x) (h : x = y) : IsNatQ y := h ▸ hx

/-- A rational with integer value `n ≥ 0` is a natural number. -/
theorem isNatQ_of_int {x : ℚ} (n : ℤ) (h : x = n) (hn : 0 ≤ n) : IsNatQ x :=
  ⟨n.toNat, by rw [h]; exact_mod_cast (Int.toNat_of_nonneg hn).symm⟩

/-- For `x ∈ ℕ`, `⌊x⌋.toNat` recovers `x`. -/
theorem IsNatQ.floor_toNat {x : ℚ} (h : IsNatQ x) : ((⌊x⌋.toNat : ℕ) : ℚ) = x := by
  obtain ⟨n, rfl⟩ := h
  simp

/-- Triads are symmetric in the first two entries. -/
theorem IsTriad.symm12 {a b c : ℚ} (h : IsTriad a b c) : IsTriad b a c :=
  ⟨h.1.of_eq (by ring), h.2.2.of_eq (by ring), h.2.1.of_eq (by ring)⟩

/-- Triads are invariant under cyclic permutation. -/
theorem IsTriad.cycle {a b c : ℚ} (h : IsTriad a b c) : IsTriad b c a :=
  ⟨h.2.2.of_eq (by ring), h.1.of_eq (by ring), h.2.1.of_eq (by ring)⟩

/-- Triads are symmetric in the last two entries. -/
theorem IsTriad.symm23 {a b c : ℚ} (h : IsTriad a b c) : IsTriad a c b :=
  ⟨h.2.1.of_eq (by ring), h.1.of_eq (by ring), h.2.2.of_eq (by ring)⟩

/-- Swapping the first two entries of a triad. -/
theorem isTriad_comm12 {a b c : ℚ} : IsTriad a b c ↔ IsTriad b a c := ⟨IsTriad.symm12, IsTriad.symm12⟩

/-- Swapping the last two entries of a triad. -/
theorem isTriad_comm23 {a b c : ℚ} : IsTriad a b c ↔ IsTriad a c b := ⟨IsTriad.symm23, IsTriad.symm23⟩

/-- `triangleDelta` is symmetric in its first two arguments. -/
theorem triangleDelta_comm12 (a b c : ℚ) : triangleDelta a b c = triangleDelta b a c := by
  unfold triangleDelta
  rw [show b + a - c = a + b - c by ring, show b - a + c = -a + b + c by ring,
    show -b + a + c = a - b + c by ring, show b + a + c + 1 = a + b + c + 1 by ring]
  ring_nf

/-- `triangleDelta` is symmetric in its last two arguments. -/
theorem triangleDelta_comm23 (a b c : ℚ) : triangleDelta a b c = triangleDelta a c b := by
  unfold triangleDelta
  rw [show a + c - b = a - b + c by ring, show a - c + b = a + b - c by ring,
    show -a + c + b = -a + b + c by ring, show a + c + b + 1 = a + b + c + 1 by ring]
  ring_nf

/-- The `3j` symbol vanishes outside the admissible range. -/
theorem wigner3j_of_not {j₁ j₂ j₃ m₁ m₂ m₃ : ℚ} (h : ¬ IsAdmissible3j j₁ j₂ j₃ m₁ m₂ m₃) :
    wigner3j j₁ j₂ j₃ m₁ m₂ m₃ = 0 := by
  simp [wigner3j, h]

/-- The `6j` symbol vanishes unless all four triads are admissible. -/
theorem wigner6j_of_not {j₁ j₂ j₃ l₁ l₂ l₃ : ℚ} (h : ¬ IsAdmissible6j j₁ j₂ j₃ l₁ l₂ l₃) :
    wigner6j j₁ j₂ j₃ l₁ l₂ l₃ = 0 := by
  simp [wigner6j, h]

/-- `√A · B = √(A B²)` for nonnegative `A`, `B`. -/
theorem w34_sqrt_mul_eq {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (h : A * B ^ 2 = C) :
    Real.sqrt A * B = Real.sqrt C := by
  rw [← h, Real.sqrt_mul hA, Real.sqrt_sq hB]

/-- Normalize `1 + n` to a natural-number cast. -/
theorem w34_one_add_natCast (n : ℕ) : (1 : ℚ) + n = ((1 + n : ℕ) : ℚ) := by push_cast; ring

/-- `0! = 1`. -/
@[simp] theorem w34_factQ_zero : factQ 0 = 1 := by simp [factQ]
/-- `1/0! = 1`. -/
@[simp] theorem w34_invFactQ_zero : invFactQ 0 = 1 := by simp [invFactQ, factQ]

/-- Reciprocal factorials are nonnegative. -/
theorem w34_invFactQ_nonneg (x : ℚ) : 0 ≤ invFactQ x := by
  unfold invFactQ factQ; split_ifs <;> positivity

end DLMF.WignerSymbols
