/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.WignerSymbols.Basic

/-!
# The triangle conditions for the `3j` symbol

The results of DLMF §34.2 that follow directly from the definition of `wigner3j` in
`DLMF.WignerSymbols.Basic`: the characterization of triads and the vanishing of the `3j`
symbol outside its admissible range.

## Main results

* `isTriad_iff`: the characterization of triads (DLMF 34.2.1 and §34.2).
* `wigner3j_eq_zero_of_not_isTriad`, `wigner3j_eq_zero_of_sum_ne_zero`,
  `wigner3j_eq_zero_of_not_isProjection`: vanishing outside the admissible range
  (DLMF 34.2.1–34.2.3).

## Implementation notes

The `₃F₂` form DLMF 34.2.6 and the properties of §34.3 are in `DLMF.WignerSymbols.ThreeJ`.
-/

@[expose] public noncomputable section

namespace DLMF.WignerSymbols

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

end DLMF.WignerSymbols
