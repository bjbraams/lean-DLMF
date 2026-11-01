/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.NumberTheory.DirichletCharacter.GaussSum
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# Dirichlet characters, Ramanujan sums and Gauss sums (DLMF §§27.8, 27.10)

DLMF's definitions of Dirichlet characters (§27.8) and of the periodic functions, Ramanujan
sums and Gauss sums of §27.10, with their bridges to Mathlib's `DirichletCharacter` and
`gaussSum`.

## Main definitions

* `IsDirichletCharacterFn`: DLMF's definition of a Dirichlet character mod `k` by the
  properties DLMF 27.8.1–27.8.4.
* `IsPrimitiveDLMF`, `IsInducedModulus`: DLMF's primitive characters and induced moduli
  (DLMF 27.8.7).
* `IsPeriodicFn`: periodic functions mod `k` (DLMF 27.10.1).
* `expFrac`: the exponential `e^{2πimn/k}`.
* `ramanujanSum`: Ramanujan's sum `c_k(n)` (DLMF 27.10.4).
* `gaussSumDLMF`, `GaussSumSeparable`: the Gauss sum `G(n, χ)` (DLMF 27.10.9) and its
  separability (DLMF 27.10.10).

## Main results

* `DirichletCharacter.isDirichletCharacterFn`: Mathlib's Dirichlet characters satisfy
  DLMF 27.8.1–27.8.4.
* `principalCharacter_apply`: the principal character (DLMF 27.8.5).
* `isPeriodicFn_examples`: characters and `n ↦ (n, k)` are periodic mod `k`.
* `gaussSumDLMF_one`: `G(n, χ₁) = c_k(n)`.
* `gaussSumDLMF_eq_gaussSum`: DLMF's `G(n, χ)` is Mathlib's `gaussSum`.

## Implementation notes

Mathlib's `DirichletCharacter ℂ k` (a multiplicative character of `ZMod k`) is DLMF's object;
the converse of `DirichletCharacter.isDirichletCharacterFn`
(`IsDirichletCharacterFn.exists_dirichletCharacter`) and the further properties are in
`DLMF.NumberTheory.Characters`. `gaussSumDLMF χ n` is DLMF's sum over `m = 1, …, k`; Mathlib's
`gaussSum χ ψ` sums over `ZMod k` with an additive character `ψ`.
-/

@[expose] public noncomputable section

open Finset Complex
open scoped Real

namespace DLMF.NumberTheory

/-! ### §27.8 Dirichlet characters -/

/-- DLMF 27.8.1–27.8.4: `χ` is a Dirichlet character mod `k` if `χ(1) = 1`,
`χ(mn) = χ(m)χ(n)`, `χ(n + k) = χ(n)` (`m, n = 1, 2, …`) and `χ(n) = 0` when `(n, k) > 1`. -/
@[dlmf 27.8.E1, dlmf 27.8.E2, dlmf 27.8.E3, dlmf 27.8.E4]
def IsDirichletCharacterFn (k : ℕ) (χ : ℕ → ℂ) : Prop :=
  χ 1 = 1 ∧ (∀ m n : ℕ, 0 < m → 0 < n → χ (m * n) = χ m * χ n) ∧
    (∀ n : ℕ, 0 < n → χ (n + k) = χ n) ∧ ∀ n : ℕ, 0 < n → n.gcd k ≠ 1 → χ n = 0

/-- Every Mathlib Dirichlet character `χ : DirichletCharacter ℂ k` satisfies 27.8.1–27.8.4. -/
@[dlmf 27.8.E1, dlmf 27.8.E2, dlmf 27.8.E3, dlmf 27.8.E4]
theorem _root_.DirichletCharacter.isDirichletCharacterFn {k : ℕ} (χ : DirichletCharacter ℂ k) :
    IsDirichletCharacterFn k fun n ↦ χ n := by
  refine ⟨by simp, fun m n _ _ ↦ by simp, fun n _ ↦ by simp, fun n _ hn ↦ ?_⟩
  apply MulChar.map_nonunit
  rw [ZMod.isUnit_iff_coprime]
  exact hn

/-- DLMF 27.8.5: the principal character `χ₁ (mod k)` is `1` for `(n, k) = 1` and `0`
otherwise; it is Mathlib's `1 : DirichletCharacter ℂ k`. -/
@[dlmf 27.8.E5]
theorem principalCharacter_apply (k n : ℕ) :
    (1 : DirichletCharacter ℂ k) n = if n.Coprime k then 1 else 0 := by
  split_ifs with h
  · exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n k).mpr h)
  · exact MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])

/-- §27.8 after 27.8.6: DLMF's definition of a primitive character mod `k`: for every divisor
`d < k` of `k` there is `a ≡ 1 (mod d)` with `(a, k) = 1` and `χ(a) ≠ 1`. -/
@[dlmf 27.8]
def IsPrimitiveDLMF {k : ℕ} (χ : DirichletCharacter ℂ k) : Prop :=
  ∀ d, d ∣ k → d < k → ∃ a : ℕ, a ≡ 1 [MOD d] ∧ a.Coprime k ∧ χ a ≠ 1

/-- DLMF 27.8.7: a divisor `d` of `k` is an induced modulus for `χ` if `χ(a) = 1` for all
`a ≡ 1 (mod d)` with `(a, k) = 1`. -/
@[dlmf 27.8.E7]
def IsInducedModulus {k : ℕ} (χ : DirichletCharacter ℂ k) (d : ℕ) : Prop :=
  d ∣ k ∧ ∀ a : ℕ, a.Coprime k → a ≡ 1 [MOD d] → χ a = 1

/-! ### §27.10 Periodic number-theoretic functions -/

/-- DLMF 27.10.1: `f` is periodic mod `k` if `f(n + k) = f(n)`, `n = 1, 2, …`. -/
@[dlmf 27.10.E1]
def IsPeriodicFn {α : Type*} (k : ℕ) (f : ℕ → α) : Prop :=
  ∀ n : ℕ, 0 < n → f (n + k) = f n

/-- §27.10 after 27.10.1: the Dirichlet characters mod `k` and `n ↦ (n, k)` are periodic
mod `k`. -/
@[dlmf 27.10.E1]
theorem isPeriodicFn_examples {k : ℕ} (χ : DirichletCharacter ℂ k) :
    IsPeriodicFn k (fun n ↦ χ n) ∧ IsPeriodicFn k (fun n ↦ n.gcd k) :=
  ⟨χ.isDirichletCharacterFn.2.2.1, fun n _ ↦ Nat.gcd_add_self_left k n⟩

/-- The exponential `e^{2πi m n/k}` of §27.10. -/
def expFrac (m n k : ℕ) : ℂ := Complex.exp (2 * π * I * m * n / k)

/-- `∑_{m=1}^k g(m) = ∑_{a ∈ ℤ/k} g(a)`. -/
private lemma sum_Icc_one_eq_sum_zmod {M : Type*} [AddCommMonoid M] {k : ℕ} [NeZero k]
    (g : ZMod k → M) : ∑ m ∈ Icc 1 k, g m = ∑ a : ZMod k, g a := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  refine sum_nbij' (fun m ↦ (m : ZMod k)) (fun a ↦ if a = 0 then k else a.val) ?_ ?_ ?_ ?_ ?_
  · intro m _; exact mem_univ _
  · intro a _
    rw [mem_Icc]
    split_ifs with h
    · exact ⟨hk, le_rfl⟩
    · exact ⟨Nat.pos_of_ne_zero ((ZMod.val_ne_zero a).mpr h), (ZMod.val_lt a).le⟩
  · intro m hm
    rw [mem_Icc] at hm
    split_ifs with h
    · rw [ZMod.natCast_eq_zero_iff] at h
      exact le_antisymm (Nat.le_of_dvd (by omega) h) hm.2
    · rw [ZMod.val_natCast]
      apply Nat.mod_eq_of_lt
      rcases hm.2.lt_or_eq with h' | h'
      · exact h'
      · exact absurd (by rw [h', ZMod.natCast_self]) h
  · intro a _
    split_ifs with h
    · rw [h, ZMod.natCast_self]
    · exact ZMod.natCast_zmod_val a
  · intro m _; rfl

/-- DLMF 27.10.4: Ramanujan's sum `c_k(n) = ∑_{m=1}^k χ₁(m) e^{2πimn/k}`, the sum over
`1 ≤ m ≤ k` with `(m, k) = 1`. -/
@[dlmf 27.10.E4]
def ramanujanSum (k n : ℕ) : ℂ :=
  ∑ m ∈ (Finset.Icc 1 k).filter (fun m ↦ m.Coprime k), expFrac m n k

/-- DLMF 27.10.9: the Gauss sum `G(n, χ) = ∑_{m=1}^k χ(m) e^{2πimn/k}`. -/
@[dlmf 27.10.E9]
def gaussSumDLMF {k : ℕ} (χ : DirichletCharacter ℂ k) (n : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 k, χ m * expFrac m n k

/-- §27.10 after 27.10.9: `G(n, χ₁) = c_k(n)`. -/
@[dlmf 27.10.E9]
theorem gaussSumDLMF_one (k n : ℕ) : gaussSumDLMF (1 : DirichletCharacter ℂ k) n =
    ramanujanSum k n := by
  rw [gaussSumDLMF, ramanujanSum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [principalCharacter_apply]
  split_ifs <;> simp

/-- DLMF 27.10.9 bridge to Mathlib (proof). -/
private lemma gaussSumDLMF_eq_gaussSum_mulShift {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k)
    (n : ℕ) :
    gaussSumDLMF χ n = gaussSum χ ((ZMod.stdAddChar (N := k)).mulShift (n : ZMod k)) := by
  rw [gaussSumDLMF, gaussSum, ← sum_Icc_one_eq_sum_zmod]
  refine sum_congr rfl fun m _ ↦ ?_
  have h := ZMod.stdAddChar_coe (N := k) ((n * m : ℕ) : ℤ)
  rw [Int.cast_natCast] at h
  rw [AddChar.mulShift_apply, ← Nat.cast_mul, h, expFrac]
  congr 2
  push_cast
  ring

/-- DLMF's `G(n, χ)` is Mathlib's `gaussSum χ (ψ.mulShift n)` with the standard additive
character `ψ = ZMod.stdAddChar` of `ZMod k`. -/
@[dlmf 27.10.E9]
theorem gaussSumDLMF_eq_gaussSum {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) (n : ℕ) :
    gaussSumDLMF χ n = gaussSum χ ((ZMod.stdAddChar (N := k)).mulShift (n : ZMod k)) := by
  exact gaussSumDLMF_eq_gaussSum_mulShift χ n

/-- DLMF 27.10.10: `G(n, χ)` is separable for `n` if `G(n, χ) = χ̄(n) G(1, χ)`. -/
@[dlmf 27.10.E10]
def GaussSumSeparable {k : ℕ} (χ : DirichletCharacter ℂ k) (n : ℕ) : Prop :=
  gaussSumDLMF χ n = starRingEnd ℂ (χ n) * gaussSumDLMF χ 1

end DLMF.NumberTheory
