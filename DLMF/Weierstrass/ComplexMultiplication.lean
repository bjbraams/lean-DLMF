/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.LatticeClassification
public import DLMFMathlib.Analysis.Complex.LatticeMultipliers
import Mathlib.Tactic

/-!
# Automorphisms of complex lattices

The origin-preserving scalar automorphisms of a complex torus are the square roots
of unity in the general case, the fourth roots when `g₃ = 0`, and the sixth roots
when `g₂ = 0`. In particular all have absolute value one and are twelfth roots of unity.
This supplements the imaginary quadratic multiplier theory of
`DLMFMathlib.Analysis.Complex.LatticeMultipliers`.

Sources: Lang, *Elliptic Functions*, Chapter 1, §5, pp. 19–21;
Koecher–Krieg, *Elliptic Functions and Modular Forms*, Chapter I, §7.
The proof reuses TauCeti's lattice classification by `g₂, g₃` and its homogeneity
formulas; it does not introduce another Weierstrass function or another lattice model.
-/

@[expose] public noncomputable section

namespace DLMF.Weierstrass

/-- A scalar preserves a lattice exactly when it fixes both weighted invariants. -/
theorem lattice_smul_eq_self_iff_invariant_weights (L : PeriodPair) (c : ℂˣ) :
    (c • L).lattice = L.lattice ↔
      ((c : ℂ) ^ 4 = 1 ∨ L.g₂ = 0) ∧ ((c : ℂ) ^ 6 = 1 ∨ L.g₃ = 0) := by
  rw [PeriodPair.lattice_eq_iff_g₂_eq_and_g₃_eq, L.g₂_smul, L.g₃_smul,
    div_eq_iff (pow_ne_zero 4 c.ne_zero), div_eq_iff (pow_ne_zero 6 c.ne_zero)]
  constructor
  · rintro ⟨h₂, h₃⟩
    constructor
    · rcases mul_eq_zero.mp (show ((c : ℂ) ^ 4 - 1) * L.g₂ = 0 by
        linear_combination -h₂) with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr h
    · rcases mul_eq_zero.mp (show ((c : ℂ) ^ 6 - 1) * L.g₃ = 0 by
        linear_combination -h₃) with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr h
  · rintro ⟨h₂, h₃⟩
    constructor
    · rcases h₂ with h | h <;> simp [h]
    · rcases h₃ with h | h <;> simp [h]

/-- Outside the square and hexagonal cases a scalar automorphism is `1` or `-1`. -/
theorem lattice_smul_eq_self_iff_of_invariants_ne_zero (L : PeriodPair)
    (h₂ : L.g₂ ≠ 0) (h₃ : L.g₃ ≠ 0) (c : ℂˣ) :
    (c • L).lattice = L.lattice ↔ (c : ℂ) = 1 ∨ (c : ℂ) = -1 := by
  rw [lattice_smul_eq_self_iff_invariant_weights]
  constructor
  · rintro ⟨h4, h6⟩
    have h4' := h4.resolve_right h₂
    have h6' := h6.resolve_right h₃
    apply mul_self_eq_one_iff.mp
    linear_combination h6' - (c : ℂ) ^ 2 * h4'
  · rintro (h | h) <;> norm_num [h]

/-- The square case has exactly the fourth roots of unity as scalar automorphisms. -/
theorem lattice_smul_eq_self_iff_of_g₃_eq_zero (L : PeriodPair)
    (h₃ : L.g₃ = 0) (c : ℂˣ) :
    (c • L).lattice = L.lattice ↔ (c : ℂ) ^ 4 = 1 := by
  have h₂ : L.g₂ ≠ 0 := by
    intro h₂
    apply L.weierstrassCurve_Δ_ne_zero
    rw [L.weierstrassCurve_Δ, h₂, h₃]
    norm_num
  simp [lattice_smul_eq_self_iff_invariant_weights, h₂, h₃]

/-- The hexagonal case has exactly the sixth roots of unity as scalar automorphisms. -/
theorem lattice_smul_eq_self_iff_of_g₂_eq_zero (L : PeriodPair)
    (h₂ : L.g₂ = 0) (c : ℂˣ) :
    (c • L).lattice = L.lattice ↔ (c : ℂ) ^ 6 = 1 := by
  have h₃ : L.g₃ ≠ 0 := by
    intro h₃
    apply L.weierstrassCurve_Δ_ne_zero
    rw [L.weierstrassCurve_Δ, h₂, h₃]
    norm_num
  simp [lattice_smul_eq_self_iff_invariant_weights, h₂, h₃]

/-- Every scalar automorphism of a complex lattice is a twelfth root of unity. -/
theorem pow_twelve_eq_one_of_lattice_smul_eq_self (L : PeriodPair) (c : ℂˣ)
    (h : (c • L).lattice = L.lattice) : (c : ℂ) ^ 12 = 1 := by
  obtain ⟨h4, _⟩ := (lattice_smul_eq_self_iff_invariant_weights L c).mp h
  rcases h4 with h4 | h₂
  · calc
      (c : ℂ) ^ 12 = ((c : ℂ) ^ 4) ^ 3 := by ring
      _ = 1 := by rw [h4]; norm_num
  · have h6' := (lattice_smul_eq_self_iff_of_g₂_eq_zero L h₂ c).mp h
    calc
      (c : ℂ) ^ 12 = ((c : ℂ) ^ 6) ^ 2 := by ring
      _ = 1 := by rw [h6']; norm_num

/-- Scalar automorphisms preserve the Euclidean absolute value. -/
theorem norm_eq_one_of_lattice_smul_eq_self (L : PeriodPair) (c : ℂˣ)
    (h : (c • L).lattice = L.lattice) : ‖(c : ℂ)‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one (pow_twelve_eq_one_of_lattice_smul_eq_self L c h)
    (by norm_num)

end DLMF.Weierstrass
