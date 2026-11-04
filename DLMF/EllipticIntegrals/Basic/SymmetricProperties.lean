/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Basic.Symmetric
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Symmetric elliptic integrals: elementary properties

Elementary properties of Carlson's symmetric integrals `R_F`, `R_J`, `R_G`, `R_D`, `R_C` that
follow directly from their defining integrals (DLMF §§19.15–19.16), without Carlson's
`R`-function.

## Main results

* `symmetricEllipticRD_eq_integral`, `symmetricEllipticRC_eq_symmetricEllipticRF`,
  `symmetricEllipticRJ_eq_hyperelliptic`: DLMF 19.16.5–19.16.7.
* `symmetricEllipticRF_comm_left`, `symmetricEllipticRF_comm_right`,
  `symmetricEllipticRJ_comm_left`, `symmetricEllipticRJ_comm_right`, `symmetricEllipticRD_comm`,
  `symmetricEllipticRG_comm_left`, `symmetricEllipticRG_comm_right`: permutation symmetry (§19.15).
* `cpow_half_mul_cpow_half`, `inv_cpow_half_eq_cpow_neg_half`, `cpow_neg_three_halves_eq`,
  `not_isNegReal_of_mem_slitPlane`, `ofReal_add_ne_zero_of_isCarlsonArgument`: elementary facts on
  principal powers and admissible arguments.
-/

@[expose] public noncomputable section
open Complex Set Filter MeasureTheory
open scoped Real Topology
namespace DLMF.EllipticIntegrals

/-- Identity under the stated parameter and domain assumptions: `(w ^ (1 / 2 : ℂ))⁻¹ = w ^ (-1 / 2
: ℂ)`. -/
theorem inv_cpow_half_eq_cpow_neg_half (w : ℂ) : (w ^ (1 / 2 : ℂ))⁻¹ = w ^ (-1 / 2 : ℂ) := by
  rw [show (-1 / 2 : ℂ) = -(1 / 2) by ring, cpow_neg]

/-- Identity under the stated parameter and domain assumptions: `w ^ (1 / 2 : ℂ) * w ^ (1 / 2 : ℂ)
= w`. -/
theorem cpow_half_mul_cpow_half (w : ℂ) : w ^ (1 / 2 : ℂ) * w ^ (1 / 2 : ℂ) = w := by
  rw [← sq, show (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ by norm_num, cpow_nat_inv_pow _ two_ne_zero]

/-- The stated relation follows from the given hypotheses: `¬ IsNegReal p`. -/
theorem not_isNegReal_of_mem_slitPlane {p : ℂ} (hp : p ∈ slitPlane) : ¬ IsNegReal p := by
  rintro ⟨h1, h2⟩
  rcases mem_slitPlane_iff.mp hp with h | h
  · linarith
  · exact h h1

/-- Formula under the stated hypotheses: `(t : ℂ) + z ∈ slitPlane`. -/
private lemma ofReal_add_mem_slitPlane_of_isCarlsonArgument {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : IsCarlsonArgument z) :
    (t : ℂ) + z ∈ slitPlane := by
  rcases hz with hz | rfl
  · rcases mem_slitPlane_iff.mp hz with h | h
    · exact mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))
    · exact mem_slitPlane_iff.mpr (Or.inr (by simpa using h))
  · simpa using ofReal_mem_slitPlane.mpr ht

/-- Identity under the stated parameter and domain assumptions: `w ^ (-(3 / 2) : ℂ) = w ^ (-(1 /
2) : ℂ) * w⁻¹`. -/
theorem cpow_neg_three_halves_eq {w : ℂ} (hw : w ≠ 0) :
    w ^ (-(3 / 2) : ℂ) = w ^ (-(1 / 2) : ℂ) * w⁻¹ := by
  rw [show -(3 / 2 : ℂ) = -(1 / 2) + -1 by norm_num, cpow_add _ _ hw, cpow_neg_one]

/-- Nonvanishing under the stated hypotheses: `(t : ℂ) + z ≠ 0`. -/
theorem ofReal_add_ne_zero_of_isCarlsonArgument {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : IsCarlsonArgument z) :
    (t : ℂ) + z ≠ 0 := slitPlane_ne_zero (ofReal_add_mem_slitPlane_of_isCarlsonArgument ht hz)

/-- DLMF 19.16.5: `R_D(x, y, z) = (3/2) ∫₀^∞ dt / (s(t) (t + z))` (for `z` not a negative real;
DLMF: `z ≠ 0`, `z ∈ ℂ \ (-∞, 0]`). -/
@[dlmf 19.16.E5]
theorem symmetricEllipticRD_eq_integral {x y z : ℂ} (hz : ¬ IsNegReal z) :
    symmetricEllipticRD x y z = (3 / 2) * ∫ t in Ioi (0 : ℝ),
        (carlsonRootProduct x y z t * ((t : ℂ) + z))⁻¹ := by
  simp [symmetricEllipticRD, symmetricEllipticRJ, hz]

/-- DLMF 19.16.6: `R_C(x, y) = R_F(x, y, y)`, **stronger than DLMF**: for every `x` and every
`y` that is not a negative real (for `y < 0` DLMF's `R_C` is a principal value and `R_F(x, y, y)`
is outside DLMF's domain). The integrands agree pointwise. -/
@[dlmf 19.16.E6]
theorem symmetricEllipticRC_eq_symmetricEllipticRF (x : ℂ) {y : ℂ} (hy : ¬ IsNegReal y) :
    symmetricEllipticRC x y = symmetricEllipticRF x y y := by
  simp only [symmetricEllipticRC, symmetricEllipticRF, hy, ↓reduceIte,
      carlsonRootProduct, mul_assoc,
    cpow_half_mul_cpow_half]

/-- DLMF 19.16.7: `R_J` is the degenerate case `x₄ = x₅ = p` of the hyperelliptic integral
`(3/2) ∫₀^∞ dt / ∏_{j=1}^5 √(t + xⱼ)`; for `p` not a negative real (no principal value). -/
@[dlmf 19.16.E7]
theorem symmetricEllipticRJ_eq_hyperelliptic (x y z : ℂ) {p : ℂ} (hp : ¬ IsNegReal p) :
    symmetricEllipticRJ x y z p =
      (3 / 2) * ∫ t in Ioi (0 : ℝ),
          (∏ j : Fin 5, ((t : ℂ) + ![x, y, z, p, p] j) ^ (1 / 2 : ℂ))⁻¹ := by
  simp only [symmetricEllipticRJ, hp, ↓reduceIte, Fin.prod_univ_five, Matrix.cons_val_zero,
    Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons, carlsonRootProduct, mul_assoc, cpow_half_mul_cpow_half]

/-- DLMF 19.15.p2 / 19.16.8: `R_F` is symmetric in its first two arguments (all arguments). -/
@[dlmf 19.15]
theorem symmetricEllipticRF_comm_left (x y z : ℂ) : symmetricEllipticRF y x z =
    symmetricEllipticRF x y z := by
  simp only [symmetricEllipticRF, carlsonRootProduct, mul_comm (((_ : ℂ) + y) ^ (1 / 2 : ℂ))]

/-- `R_F` is symmetric in its last two arguments (all arguments). -/
@[dlmf 19.15]
theorem symmetricEllipticRF_comm_right (x y z : ℂ) : symmetricEllipticRF x z y =
    symmetricEllipticRF x y z := by
  simp only [symmetricEllipticRF, carlsonRootProduct, mul_assoc,
      mul_comm (((_ : ℂ) + z) ^ (1 / 2 : ℂ))]

/-- `R_J(x, y, z, p)` is symmetric in its first two arguments (all arguments). -/
@[dlmf 19.15]
theorem symmetricEllipticRJ_comm_left (x y z p : ℂ) : symmetricEllipticRJ y x z p =
    symmetricEllipticRJ x y z p := by
  simp only [symmetricEllipticRJ, carlsonRootProduct, mul_comm (((_ : ℂ) + y) ^ (1 / 2 : ℂ))]

/-- `R_J(x, y, z, p)` is symmetric in `y, z` (all arguments). -/
@[dlmf 19.15]
theorem symmetricEllipticRJ_comm_right (x y z p : ℂ) : symmetricEllipticRJ x z y p =
    symmetricEllipticRJ x y z p := by
  simp only [symmetricEllipticRJ, carlsonRootProduct, mul_assoc,
      mul_comm (((_ : ℂ) + z) ^ (1 / 2 : ℂ))]

/-- `R_D(x, y, z)` is symmetric in `x, y` (DLMF 19.16.5; all arguments). -/
theorem symmetricEllipticRD_comm (x y z : ℂ) : symmetricEllipticRD y x z =
    symmetricEllipticRD x y z :=
  symmetricEllipticRJ_comm_left x y z z

/-- `R_G` is symmetric in its first two arguments (all arguments). -/
@[dlmf 19.15]
theorem symmetricEllipticRG_comm_left (x y z : ℂ) : symmetricEllipticRG y x z =
    symmetricEllipticRG x y z := by
  unfold symmetricEllipticRG carlsonRootProduct
  congr 2; funext t; ring

/-- `R_G` is symmetric in its last two arguments (all arguments). -/
@[dlmf 19.15]
theorem symmetricEllipticRG_comm_right (x y z : ℂ) : symmetricEllipticRG x z y =
    symmetricEllipticRG x y z := by
  unfold symmetricEllipticRG carlsonRootProduct
  congr 2; funext t; ring

end DLMF.EllipticIntegrals
