/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The first two weighted moments of a finite coefficient family

The moment map `f -> (sum f, sum a*f)` has rank two whenever two weights differ.
Its fibers are nonempty translates of a kernel of dimension `card iota - 2`.
Applied to partial-fraction residues, this is the accessory-parameter count in
Kristensson, *Second Order Differential Equations*, Chapter 3, §§3.1–3.3 and
Chapter 4, §4.4, and Olver, *Asymptotics and Special Functions*, Chapter 5, §8.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace LinearMap

/-- The zeroth and first weighted moments of a finite family of coefficients. -/
def weightedMomentPair {ι R : Type*} [Fintype ι] [CommSemiring R] (a : ι → R) :
    (ι → R) →ₗ[R] R × R where
  toFun f := (∑ i, f i, ∑ i, a i * f i)
  map_add' f g := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, Prod.mk_add_mk]
  map_smul' c f := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Prod.smul_mk,
      ← Finset.mul_sum, mul_left_comm]

/-- Evaluation of the weighted moment map. -/
@[simp] theorem weightedMomentPair_apply {ι R : Type*} [Fintype ι] [CommSemiring R]
    (a f : ι → R) : weightedMomentPair a f = (∑ i, f i, ∑ i, a i * f i) := rfl

/-- The kernel consists exactly of families whose zeroth and first moments vanish. -/
theorem mem_ker_weightedMomentPair {ι R : Type*} [Fintype ι] [CommSemiring R]
    (a f : ι → R) :
    f ∈ (weightedMomentPair a).ker ↔ (∑ i, f i) = 0 ∧ (∑ i, a i * f i) = 0 := by
  simp [LinearMap.mem_ker, Prod.ext_iff]

/-- A pair of distinct weights makes the two-moment map surjective.
Kristensson, Chapter 3, §§3.1–3.3: the corresponding two-column minor is the
nonzero difference of the two marked points. -/
theorem weightedMomentPair_surjective {ι K : Type*} [Fintype ι] [Field K]
    (a : ι → K) {i j : ι} (hij : a i ≠ a j) :
    Function.Surjective (weightedMomentPair a) := by
  sorry

/-- The space of homogeneous residue corrections has exactly `card iota - 2`
parameters when two marked points differ. Kristensson, Chapter 3, §§3.1–3.3;
the one-accessory-parameter Heun case is Chapter 4, §4.4. -/
theorem finrank_ker_weightedMomentPair {ι K : Type*} [Fintype ι] [Field K]
    (a : ι → K) {i j : ι} (hij : a i ≠ a j) :
    Module.finrank K (weightedMomentPair a).ker = Fintype.card ι - 2 := by
  sorry

/-- Every prescribed pair of moments is attained once two weights differ. -/
theorem exists_weightedMomentPair_eq {ι K : Type*} [Fintype ι] [Field K]
    (a : ι → K) {i j : ι} (hij : a i ≠ a j) (u v : K) :
    ∃ f : ι → K, (∑ k, f k) = u ∧ (∑ k, a k * f k) = v := by
  obtain ⟨f, hf⟩ := weightedMomentPair_surjective a hij (u, v)
  exact ⟨f, congrArg Prod.fst hf, congrArg Prod.snd hf⟩

/-- A fiber of the two-moment map is the translate by any one of its elements of
the homogeneous kernel. This identifies the affine accessory-parameter freedom. -/
theorem weightedMomentPair_eq_iff_sub_mem_ker {ι K : Type*} [Fintype ι] [Field K]
    (a f g : ι → K) :
    weightedMomentPair a f = weightedMomentPair a g ↔
      f - g ∈ (weightedMomentPair a).ker := by
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero]

end LinearMap
