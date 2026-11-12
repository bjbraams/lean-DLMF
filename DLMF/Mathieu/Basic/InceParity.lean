/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Hill.Basic

/-!
# Parity and periodicity of the Ince polynomials

The Ince polynomials of DLMF §28.31(ii) belong to their defining finite cosine and sine
polynomial families. Consequently they are even and odd, respectively, and have period `2π`.
The same parity and periodicity hold for the paraboloidal wave functions (28.31.16–28.31.17).
These properties hold for every index, including the zero fallback outside the choice domain.

## Main results

* `isInceCosPoly_inceC`, `isInceSinPoly_inceS`: membership in the finite polynomial families.
* `IsInceCosPoly.neg_eq`, `IsInceSinPoly.neg_eq`: parity of the polynomial families.
* `IsInceCosPoly.periodic`, `IsInceSinPoly.periodic`: period `2π` of the families.
* `paraboloidalHc_neg`, `paraboloidalHs_neg`: parity of the paraboloidal wave functions.
* `periodic_paraboloidalHc`, `periodic_paraboloidalHs`: their period `2π`.
-/

public noncomputable section

open Complex

namespace DLMF.Mathieu

/-- The canonical Ince cosine polynomial belongs to its defining finite cosine family. -/
lemma isInceCosPoly_inceC (p m : ℕ) (ξ : ℝ) :
    IsInceCosPoly p (fun z => inceC p m z ξ) := by
  classical
  unfold inceC
  split_ifs with h
  · exact h.choose_spec.1.1
  · exact ⟨fun _ => 0, by simp⟩

/-- The canonical Ince sine polynomial belongs to its defining finite sine family. -/
lemma isInceSinPoly_inceS (p m : ℕ) (ξ : ℝ) :
    IsInceSinPoly p (fun z => inceS p m z ξ) := by
  classical
  unfold inceS
  split_ifs with h
  · exact h.choose_spec.1.1
  · exact ⟨fun _ => 0, by simp⟩

/-- A finite Ince cosine polynomial is even. -/
lemma IsInceCosPoly.neg_eq {p : ℕ} {f : ℂ → ℂ} (hf : IsInceCosPoly p f) (z : ℂ) :
    f (-z) = f z := by
  obtain ⟨A, hA⟩ := hf
  rw [hA, hA]
  simp only [mul_neg, Complex.cos_neg]

/-- A finite Ince sine polynomial is odd. -/
lemma IsInceSinPoly.neg_eq {p : ℕ} {f : ℂ → ℂ} (hf : IsInceSinPoly p f) (z : ℂ) :
    f (-z) = -f z := by
  obtain ⟨A, hA⟩ := hf
  rw [hA, hA]
  simp only [mul_neg, Complex.sin_neg, mul_neg, Finset.sum_neg_distrib]

/-- A finite Ince cosine polynomial has period `2π`. -/
lemma IsInceCosPoly.periodic {p : ℕ} {f : ℂ → ℂ} (hf : IsInceCosPoly p f) :
    Function.Periodic f (2 * Real.pi) := by
  obtain ⟨A, hA⟩ := hf
  intro z
  rw [hA, hA]
  apply Finset.sum_congr rfl
  intro k hk
  have harg : (k : ℂ) * (z + 2 * Real.pi) = k * z + k * (2 * Real.pi) := by ring
  rw [harg, Complex.cos_add_nat_mul_two_pi]

/-- A finite Ince sine polynomial has period `2π`. -/
lemma IsInceSinPoly.periodic {p : ℕ} {f : ℂ → ℂ} (hf : IsInceSinPoly p f) :
    Function.Periodic f (2 * Real.pi) := by
  obtain ⟨A, hA⟩ := hf
  intro z
  rw [hA, hA]
  apply Finset.sum_congr rfl
  intro k hk
  have harg : (k : ℂ) * (z + 2 * Real.pi) = k * z + k * (2 * Real.pi) := by ring
  rw [harg, Complex.sin_add_nat_mul_two_pi]

/-- The cosine paraboloidal wave function is even in its complex argument. -/
lemma paraboloidalHc_neg (p m : ℕ) (z : ℂ) (ξ : ℝ) :
    paraboloidalHc p m (-z) ξ = paraboloidalHc p m z ξ := by
  rw [paraboloidalHc, paraboloidalHc, mul_neg, Complex.cos_neg,
    (isInceCosPoly_inceC p m ξ).neg_eq z]

/-- The sine paraboloidal wave function is odd in its complex argument. -/
lemma paraboloidalHs_neg (p m : ℕ) (z : ℂ) (ξ : ℝ) :
    paraboloidalHs p m (-z) ξ = -paraboloidalHs p m z ξ := by
  rw [paraboloidalHs, paraboloidalHs, mul_neg, Complex.cos_neg,
    (isInceSinPoly_inceS p m ξ).neg_eq z, mul_neg]

/-- The cosine paraboloidal wave function has period `2π`. -/
lemma periodic_paraboloidalHc (p m : ℕ) (ξ : ℝ) :
    Function.Periodic (fun z => paraboloidalHc p m z ξ) (2 * Real.pi) := by
  intro z
  simp only [paraboloidalHc]
  have hp := (isInceCosPoly_inceC p m ξ).periodic z
  rw [hp]
  have harg : (2 : ℂ) * (z + 2 * Real.pi) = 2 * z + 2 * (2 * Real.pi) := by ring
  have hcos : Complex.cos (2 * z + 2 * (2 * Real.pi)) = Complex.cos (2 * z) := by
    simpa using Complex.cos_add_nat_mul_two_pi (2 * z) 2
  rw [harg, hcos]

/-- The sine paraboloidal wave function has period `2π`. -/
lemma periodic_paraboloidalHs (p m : ℕ) (ξ : ℝ) :
    Function.Periodic (fun z => paraboloidalHs p m z ξ) (2 * Real.pi) := by
  intro z
  simp only [paraboloidalHs]
  have hp := (isInceSinPoly_inceS p m ξ).periodic z
  rw [hp]
  have harg : (2 : ℂ) * (z + 2 * Real.pi) = 2 * z + 2 * (2 * Real.pi) := by ring
  have hcos : Complex.cos (2 * z + 2 * (2 * Real.pi)) = Complex.cos (2 * z) := by
    simpa using Complex.cos_add_nat_mul_two_pi (2 * z) 2
  rw [harg, hcos]

end DLMF.Mathieu
