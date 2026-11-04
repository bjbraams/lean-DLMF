/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.WignerSymbols.Basic.TriangleConditions
public import DLMF.WignerSymbols.FactorialHelpers
public import DLMF.GeneralizedHypergeometric.Basic.PrincipalContinuationExistence
public import DLMF.GeneralizedHypergeometric.Basic
public import DLMF.Hypergeometric.Basic.GeneralizedCalculus
public import Mathlib.RingTheory.PowerSeries.Basic
public import DLMF.Hypergeometric.ArgumentContinuation
public import DLMF.Hypergeometric.Solutions
public import Mathlib.Algebra.Order.Ring.Star
public import DLMF.GeneralizedHypergeometric.UnitArgument
public import DLMF.GeneralizedHypergeometric.ClearedTerminating
public import DLMF.WignerSymbols.RacahPochhammer

/-!
# The `3j` symbol

Statements of DLMF §34.2 (the `₃F₂` form 34.2.6) and §34.3
(special cases, symmetry and orthogonality) for `wigner3j`, and the zeros of §34.10. The
recursion relations (§34.3(iii)) are in `DLMF.WignerSymbols.ThreeJRecursion`, the relations to
Legendre polynomials and spherical harmonics (§34.3(vii)) in
`DLMF.WignerSymbols.ThreeJLegendre`.

## Main results

* `wigner3j_eq_matrixHypergeometric3F2`: DLMF 34.2.6.
* `wigner3j_j_j_zero`, `wigner3j_j_j_one_zero`, `wigner3j_j_j_one_one`: DLMF 34.3.1–34.3.3.
* `wigner3j_zero_zero_zero_of_even`, `wigner3j_zero_zero_zero_of_odd`: DLMF 34.3.4–34.3.5.
* `wigner3j_stretched`, `wigner3j_top`: DLMF 34.3.6–34.3.7.
* `wigner3j_cycle`, `wigner3j_cycle₂`, `wigner3j_swap`, `wigner3j_neg`: the symmetries DLMF
  34.3.8–34.3.10.
* `wigner3j_regge₁`, `wigner3j_regge₂`: the Regge symmetries DLMF 34.3.11–34.3.12.
* `wigner3j_orthogonality_m`, `wigner3j_orthogonality_j`, `wigner3j_sum_sq`: DLMF
  34.3.16–34.3.18.
* `wigner3j_one_one_one_zero`: a nontrivial zero (DLMF §34.10).

## Implementation notes

The triangle conditions of §34.2 are in `DLMF.WignerSymbols.Basic.TriangleConditions`. Since
`wigner3j` is `0` outside the admissible range (34.2.1–34.2.3), the symmetry relations
34.3.8–34.3.12 are stated for all rational arguments.

The `₃F₂` form 34.2.6 follows from Racah's sum, reflected about `s = j₁ - m₁` and written as a
terminating `₃F₂(1)` with cleared denominators (`DLMF.Hypergeometric.genClearedFiniteHG`, which
keeps the vanishing terms of negative factorial arguments), by two steps of Sheppard's
transformation (`DLMF.Hypergeometric.genClearedFiniteHG_sheppard`).

The even case 34.3.4 of `wigner3j_zero_zero_zero_of_even` reduces the symmetric Racah sum
with zero magnetic numbers to Dixon's terminating sum 16.4.5
(`generalizedHypergeometric_dixon_terminating_even` in
`DLMF.GeneralizedHypergeometric.UnitArgument`).
-/

@[expose] public noncomputable section

open Finset

namespace DLMF.WignerSymbols

/-! ## Helpers: Racah's sum in symmetric form -/

/-- Shifting all arguments of `symmetricRacahSum` by an integer `t` gives the sign `(-1)^t`. -/
private lemma symmetricRacahSum_add_intCast (x₁ x₂ x₃ y₁ y₂ y₃ t : ℚ) (n : ℤ) (ht : t = n) :
    symmetricRacahSum (x₁ + t) (x₂ + t) (x₃ + t) (y₁ + t) (y₂ + t) (y₃ + t) =
      (-1 : ℝ) ^ n * symmetricRacahSum x₁ x₂ x₃ y₁ y₂ y₃ := by
  unfold symmetricRacahSum
  rw [← finsum_comp_equiv (Equiv.addRight n), mul_finsum]
  refine finsum_congr fun s => ?_
  simp only [Equiv.coe_addRight, Int.cast_add, ← ht]
  rw [zpow_add₀ (by norm_num)]
  ring_nf

/-- `symmetricRacahSum` is invariant under `(x, y) ↦ (-y, -x)` (substitute `s ↦ -s`). -/
private lemma symmetricRacahSum_neg (x₁ x₂ x₃ y₁ y₂ y₃ : ℚ) :
    symmetricRacahSum x₁ x₂ x₃ y₁ y₂ y₃ =
        symmetricRacahSum (-y₁) (-y₂) (-y₃) (-x₁) (-x₂) (-x₃) := by
  unfold symmetricRacahSum
  rw [← finsum_comp_equiv (Equiv.neg ℤ)]
  refine finsum_congr fun s => ?_
  simp only [Equiv.neg_apply, Int.cast_neg, zpow_neg, ← inv_zpow, inv_neg, inv_one]
  ring_nf

/-- `symmetricRacahSum` is symmetric in the `x` and in the `y` arguments. -/
theorem symmetricRacahSum_swap_x12 (x₁ x₂ x₃ y₁ y₂ y₃ : ℚ) :
    symmetricRacahSum x₁ x₂ x₃ y₁ y₂ y₃ = symmetricRacahSum x₂ x₁ x₃ y₁ y₂ y₃ :=
  finsum_congr fun _ => by ring
/-- Symmetry of the symmetric Racah sum in `x₂ ↔ x₃`. -/
theorem symmetricRacahSum_swap_x23 (x₁ x₂ x₃ y₁ y₂ y₃ : ℚ) :
    symmetricRacahSum x₁ x₂ x₃ y₁ y₂ y₃ = symmetricRacahSum x₁ x₃ x₂ y₁ y₂ y₃ :=
  finsum_congr fun _ => by ring
/-- Symmetry of the symmetric Racah sum in `y₁ ↔ y₂`. -/
theorem symmetricRacahSum_swap_y12 (x₁ x₂ x₃ y₁ y₂ y₃ : ℚ) :
    symmetricRacahSum x₁ x₂ x₃ y₁ y₂ y₃ = symmetricRacahSum x₁ x₂ x₃ y₂ y₁ y₃ :=
  finsum_congr fun _ => by ring
/-- Symmetry of the symmetric Racah sum in `y₂ ↔ y₃`. -/
theorem symmetricRacahSum_swap_y23 (x₁ x₂ x₃ y₁ y₂ y₃ : ℚ) :
    symmetricRacahSum x₁ x₂ x₃ y₁ y₂ y₃ = symmetricRacahSum x₁ x₂ x₃ y₁ y₃ y₂ :=
  finsum_congr fun _ => by ring

/-- The finite sum of 34.2.4 as `symmetricRacahSum`. -/
private lemma sum_racahTerm3j_eq_symmetricRacahSum {j₁ j₂ j₃ m₁ m₂ : ℚ}
    (hA : IsNatQ (j₁ + j₂ - j₃)) :
    ∑ s ∈ range (⌊j₁ + j₂ - j₃⌋.toNat + 1), racahTerm3j j₁ j₂ j₃ m₁ m₂ s =
      symmetricRacahSum (j₁ + j₂ - j₃) (j₁ - m₁) (j₂ + m₂) 0 (j₂ - j₃ - m₁) (j₁ - j₃ + m₂) := by
  unfold symmetricRacahSum
  rw [finsum_eq_sum_of_support_subset _
    (s := (range (⌊j₁ + j₂ - j₃⌋.toNat + 1)).map Nat.castEmbedding) ?_, Finset.sum_map]
  · refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Nat.castEmbedding_apply, Int.cast_natCast, zpow_natCast, sub_zero]
    unfold racahTerm3j
    ring_nf
  · intro s hs
    simp only [Function.mem_support] at hs
    have h1 : ratInvFactorial ((s : ℚ) - 0) ≠ 0 := fun h0 => hs (by rw [h0]; ring)
    have h2 : ratInvFactorial (j₁ + j₂ - j₃ - s) ≠ 0 := fun h0 => hs (by rw [h0]; ring)
    rw [Ne, ratInvFactorial_eq_zero_iff_neg, not_lt] at h1 h2
    simp only [coe_map, Nat.castEmbedding_apply, coe_range, Set.mem_image, Set.mem_Iio]
    refine ⟨s.toNat, ?_, Int.toNat_of_nonneg (by exact_mod_cast (by linarith : (0 : ℚ) ≤ s))⟩
    have : (s : ℚ) ≤ ((⌊j₁ + j₂ - j₃⌋.toNat : ℕ) : ℚ) := by rw [hA.floor_toNat]; linarith
    have h3 : s ≤ (⌊j₁ + j₂ - j₃⌋.toNat : ℤ) := by exact_mod_cast this
    omega

/-- Cyclic permutations of the `x` and of the `y` arguments of `symmetricRacahSum`. -/
private lemma symmetricRacahSum_cycle_x (x₁ x₂ x₃ y₁ y₂ y₃ : ℚ) :
    symmetricRacahSum x₁ x₂ x₃ y₁ y₂ y₃ = symmetricRacahSum x₂ x₃ x₁ y₁ y₂ y₃ :=
  finsum_congr fun _ => by ring
/-- Cyclic symmetry of the symmetric Racah sum in the `y` arguments. -/
private lemma symmetricRacahSum_cycle_y (x₁ x₂ x₃ y₁ y₂ y₃ : ℚ) :
    symmetricRacahSum x₁ x₂ x₃ y₁ y₂ y₃ = symmetricRacahSum x₁ x₂ x₃ y₂ y₃ y₁ :=
  finsum_congr fun _ => by ring

/-- Integer powers of `-1` with exponents of the same parity. -/
private lemma neg_one_zpow_eq_of_eq_add_two_mul {A B : ℤ} (k : ℤ) (h : A = B + 2 * k) :
    (-1 : ℝ) ^ A = (-1 : ℝ) ^ B := by
  rw [h, zpow_add₀ (by norm_num), zpow_mul]
  norm_num

set_option hygiene false in
/-- Close `IsNatQ e` by one of the hypotheses `h1`, …, `h9` up to `ring`. -/
macro "wigner_pick9" : tactic => `(tactic| first
  | (apply IsNatQ.of_eq h1; ring1) | (apply IsNatQ.of_eq h2; ring1)
  | (apply IsNatQ.of_eq h3; ring1) | (apply IsNatQ.of_eq h4; ring1)
  | (apply IsNatQ.of_eq h5; ring1) | (apply IsNatQ.of_eq h6; ring1)
  | (apply IsNatQ.of_eq h7; ring1) | (apply IsNatQ.of_eq h8; ring1)
  | (apply IsNatQ.of_eq h9; ring1))

/-- Racah's formula with the prefactor as one square root and the sum in symmetric form. -/
theorem wigner3j_eq_sqrt_mul_symmetricRacahSum {j₁ j₂ j₃ m₁ m₂ m₃ : ℚ}
    (h : IsAdmissible3j j₁ j₂ j₃ m₁ m₂ m₃) :
    wigner3j j₁ j₂ j₃ m₁ m₂ m₃ =
      signPow (j₁ - j₂ - m₃) *
        Real.sqrt (ratFactorial (j₁ + j₂ - j₃) * ratFactorial (j₁ - j₂ + j₃) *
            ratFactorial (-j₁ + j₂ + j₃) /
          ratFactorial (j₁ + j₂ + j₃ + 1) *
              (ratFactorial (j₁ + m₁) * ratFactorial (j₁ - m₁) * ratFactorial (j₂ + m₂) *
          ratFactorial (j₂ - m₂) * ratFactorial (j₃ + m₃) * ratFactorial (j₃ - m₃))) *
        symmetricRacahSum (j₁ + j₂ - j₃) (j₁ - m₁) (j₂ + m₂) 0 (j₂ - j₃ - m₁) (j₁ - j₃ + m₂) := by
  unfold wigner3j
  simp only [h, ↓reduceIte]
  rw [sum_racahTerm3j_eq_symmetricRacahSum h.1.1, triangleDelta,
      Real.sqrt_mul (x := ratFactorial (j₁ + j₂ - j₃) *
    ratFactorial (j₁ - j₂ + j₃) * ratFactorial (-j₁ + j₂ + j₃) / ratFactorial (j₁ + j₂ + j₃ + 1))
    (by unfold ratFactorial; positivity)]
  ring

/-- The `3j` symbol vanishes unless `m₁ + m₂ + m₃ = 0`. -/
private lemma wigner3j_eq_zero_of_add_add_ne_zero {j₁ j₂ j₃ m₁ m₂ m₃ : ℚ} (h : m₁ + m₂ + m₃ ≠ 0) :
    wigner3j j₁ j₂ j₃ m₁ m₂ m₃ = 0 := wigner3j_of_not fun h' => h h'.2.2.2.2

open DLMF.Hypergeometric in
/-- Racah's sum 34.2.4 reflected (`s = α - k`, `α = j₁ - m₁`) is a terminating `₃F₂(1)` with
cleared denominators, `(-1)^α / (α! A₂! γ! A₁! β!) ×`
`∑ₖ (-α)ₖ(-γ)ₖ(-A₂)ₖ/k! (β-α+1+k)_{α-k}(A₁-α+1+k)_{α-k}`. -/
private lemma sum_reflected_racahTerm3j_eq_cleared (A1 A2 α β γ : ℕ) :
    ∑ k ∈ range (α + 1), ((-1 : ℂ) ^ (α - k) * (ratInvFactorial ((α : ℚ) - k) : ℂ) *
      (ratInvFactorial ((((A1 : ℤ) - α : ℤ) : ℚ) + k) : ℂ) * (ratInvFactorial (k : ℚ) : ℂ) *
      (ratInvFactorial ((((β : ℤ) - α : ℤ) : ℚ) + k) : ℂ) * (ratInvFactorial ((A2 : ℚ) - k) : ℂ) *
      (ratInvFactorial ((γ : ℚ) - k) : ℂ)) =
    (-1) ^ α / (α.factorial * A2.factorial * γ.factorial * A1.factorial * β.factorial) *
      genClearedFiniteHG α {-(α : ℂ), -(γ : ℂ), -(A2 : ℂ)}
        {(β : ℂ) - α + 1, (A1 : ℂ) - α + 1} := by
  rw [genClearedFiniteHG, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ α := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [ratInvFactorial_natCast_sub_natCast, ratInvFactorial_natCast_sub_natCast,
    ratInvFactorial_natCast_sub_natCast, ratInvFactorial_of_eq (x := (k : ℚ)) rfl,
    ratInvFactorial_intCast_add_natCast _ hk' (by omega),
        ratInvFactorial_intCast_add_natCast _ hk' (by omega),
    show ((A1 : ℤ) - α + α).toNat = A1 by omega, show ((β : ℤ) - α + α).toNat = β by omega]
  have hsg : (-1 : ℂ) ^ α = (-1) ^ (α - k) * (-1) ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk']
  simp only [pochhammerProduct, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.prod_cons, Multiset.prod_singleton, hsg]
  push_cast
  have h1 : (α.factorial : ℂ) ≠ 0 := by exact_mod_cast α.factorial_ne_zero
  have h2 : (A2.factorial : ℂ) ≠ 0 := by exact_mod_cast A2.factorial_ne_zero
  have h3 : (γ.factorial : ℂ) ≠ 0 := by exact_mod_cast γ.factorial_ne_zero
  have h4 : (A1.factorial : ℂ) ≠ 0 := by exact_mod_cast A1.factorial_ne_zero
  have h5 : (β.factorial : ℂ) ≠ 0 := by exact_mod_cast β.factorial_ne_zero
  have h6 : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  field_simp
  have e : ((-1 : ℂ) ^ k) ^ 2 = 1 := by rw [← pow_mul, pow_mul']; norm_num
  linear_combination (norm := ring_nf) (pochhammer (-(α : ℂ)) k * pochhammer (-(A2 : ℂ)) k *
    pochhammer (-(γ : ℂ)) k * pochhammer ((A1 : ℂ) - α + 1 + k) (α - k) *
    pochhammer ((β : ℂ) - α + 1 + k) (α - k)) * e

/-! ## §34.2 The triangle conditions -/

open DLMF.Hypergeometric in
/-- DLMF 34.2.6: the `3j` symbol as a terminating `₃F₂` of unit argument,
`(-1)^{j₂-m₁+m₃} (j₁+j₂+m₃)! (j₂+j₃-m₁)! / (Δ(j₁j₂j₃) (j₁+j₂+j₃+1)!)`
`× ((j₁+m₁)!(j₃-m₃)! / ((j₁-m₁)!(j₂+m₂)!(j₂-m₂)!(j₃+m₃)!))^{1/2}`
`× ₃F₂(-j₁-j₂-j₃-1, -j₁+m₁, -j₃-m₃; -j₁-j₂-m₃, -j₂-j₃+m₁; 1)`.
The series terminates after `n = min(j₁-m₁, j₃+m₃)` terms; the lower parameters are
nonpositive integers `≤ -n`, so every retained Pochhammer denominator is nonzero
(`generalizedHypergeometricTruncated`, the convention of §16.2). Assumes 34.2.1–34.2.3. -/
@[dlmf 34.2.E6]
theorem wigner3j_eq_matrixHypergeometric3F2 {j₁ j₂ j₃ m₁ m₂ m₃ : ℚ}
    (h : IsAdmissible3j j₁ j₂ j₃ m₁ m₂ m₃) :
    (wigner3j j₁ j₂ j₃ m₁ m₂ m₃ : ℂ) =
      ((signPow (j₂ - m₁ + m₃) * ratFactorial (j₁ + j₂ + m₃) * ratFactorial (j₂ + j₃ - m₁) /
          (triangleDelta j₁ j₂ j₃ * ratFactorial (j₁ + j₂ + j₃ + 1)) *
          Real.sqrt (ratFactorial (j₁ + m₁) * ratFactorial (j₃ - m₃) /
            (ratFactorial (j₁ - m₁) * ratFactorial (j₂ + m₂) * ratFactorial (j₂ - m₂) *
                ratFactorial (j₃ + m₃))) : ℝ) : ℂ) *
        DLMF.Hypergeometric.generalizedHypergeometricTruncated (min ⌊j₁ - m₁⌋.toNat ⌊j₃ + m₃⌋.toNat)
          {((-j₁ - j₂ - j₃ - 1 : ℚ) : ℂ), ((-j₁ + m₁ : ℚ) : ℂ), ((-j₃ - m₃ : ℚ) : ℂ)}
          {((-j₁ - j₂ - m₃ : ℚ) : ℂ), ((-j₂ - j₃ + m₁ : ℚ) : ℂ)} 1 := by
  have h' := h
  obtain ⟨⟨⟨A1, hA1⟩, ⟨A2, hA2⟩, ⟨A3, hA3⟩⟩, ⟨⟨α, hα⟩, ⟨α', hα'⟩⟩, ⟨⟨β', hβ'⟩, ⟨β, hβ⟩⟩,
    ⟨⟨γ', hγ'⟩, ⟨γ, hγ⟩⟩, hm⟩ := h'
  have r1 : A1 + γ = α + β' := by
    have : ((A1 + γ : ℕ) : ℚ) = ((α + β' : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  have r2 : A3 + α = β + γ := by
    have : ((A3 + α : ℕ) : ℚ) = ((β + γ : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  -- Racah's sum, reflected
  have hz1 : ∀ s : ℕ, A1 < s → racahTerm3j j₁ j₂ j₃ m₁ m₂ s = 0 := by
    intro s hs
    have : (A1 : ℚ) < s := by exact_mod_cast hs
    unfold racahTerm3j
    rw [ratInvFactorial_of_neg (x := j₁ + j₂ - j₃ - s) (by linarith)]
    ring
  have hz2 : ∀ s : ℕ, α < s → racahTerm3j j₁ j₂ j₃ m₁ m₂ s = 0 := by
    intro s hs
    have : (α : ℚ) < s := by exact_mod_cast hs
    unfold racahTerm3j
    rw [ratInvFactorial_of_neg (x := j₁ - m₁ - s) (by linarith)]
    ring
  have hsum : ∑ s ∈ range (A1 + 1), racahTerm3j j₁ j₂ j₃ m₁ m₂ s =
      ∑ s ∈ range (α + 1), racahTerm3j j₁ j₂ j₃ m₁ m₂ s := by
    rw [Finset.sum_subset (s₂ := range (A1 + α + 1)) (range_subset_range.2 (by omega))
        (fun s _ hs => hz1 s (by simp only [mem_range, not_lt] at hs; omega)),
      Finset.sum_subset (s₁ := range (α + 1)) (s₂ := range (A1 + α + 1))
        (range_subset_range.2 (by omega))
        (fun s _ hs => hz2 s (by simp only [mem_range, not_lt] at hs; omega))]
  have hS : ((∑ s ∈ range (α + 1), racahTerm3j j₁ j₂ j₃ m₁ m₂ s : ℝ) : ℂ) =
      (-1) ^ α / (α.factorial * A2.factorial * γ.factorial * A1.factorial * β.factorial) *
        genClearedFiniteHG α {-(α : ℂ), -(γ : ℂ), -(A2 : ℂ)}
          {(β : ℂ) - α + 1, (A1 : ℂ) - α + 1} := by
    rw [← sum_reflected_racahTerm3j_eq_cleared, ← Finset.sum_range_reflect, Complex.ofReal_sum]
    refine sum_congr rfl fun k hk => ?_
    have hk' : k ≤ α := Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [show α + 1 - 1 - k = α - k by omega]
    unfold racahTerm3j
    have hs : ((α - k : ℕ) : ℚ) = α - k := by rw [Nat.cast_sub hk']
    rw [hs, show j₁ + j₂ - j₃ - ((α : ℚ) - k) = (((A1 : ℤ) - α : ℤ) : ℚ) + k by
        push_cast; linarith,
      show j₁ - m₁ - ((α : ℚ) - k) = (k : ℚ) by linarith,
      show j₂ + m₂ - ((α : ℚ) - k) = (((β : ℤ) - α : ℤ) : ℚ) + k by push_cast; linarith,
      show j₃ - j₂ + m₁ + ((α : ℚ) - k) = (A2 : ℚ) - k by linarith,
      show j₃ - j₁ - m₂ + ((α : ℚ) - k) = (γ : ℚ) - k by linarith]
    push_cast
    ring
  -- two Sheppard steps
  have hB : genClearedFiniteHG α {-(α : ℂ), -(γ : ℂ), -(A2 : ℂ)}
      {(β : ℂ) - α + 1, (A1 : ℂ) - α + 1} =
      genClearedFiniteHG α {-(α : ℂ), -((A1 : ℂ) + A2 + A3 + 1), -(γ : ℂ)}
        {-((A1 : ℂ) + γ), -((A3 : ℂ) + α)} := by
    rw [genClearedFiniteHG_sheppard α (-(γ : ℂ)) _ (-((A1 : ℂ) + γ)) (-((A3 : ℂ) + α))]
    conv_rhs => rw [Multiset.pair_comm (-(γ : ℂ)), Multiset.pair_comm (-((A1 : ℂ) + γ)),
      genClearedFiniteHG_sheppard α (-(γ : ℂ)) (-((A1 : ℂ) + γ) - -((A1 : ℂ) + A2 + A3 + 1))
        (1 + -(γ : ℂ) - -((A3 : ℂ) + α) - α) (-((A1 : ℂ) + γ))]
    rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
    have r2' : (A3 : ℂ) + α = β + γ := by exact_mod_cast r2
    rw [show (1 + -(γ : ℂ) - -((A3 : ℂ) + α) - α) - (-((A1 : ℂ) + γ) -
        -((A1 : ℂ) + A2 + A3 + 1)) = -(A2 : ℂ) by ring,
      show 1 + -(γ : ℂ) - -((A1 : ℂ) + γ) - α = (A1 : ℂ) - α + 1 by ring,
      show 1 + -(γ : ℂ) - -((A3 : ℂ) + α) - α = (β : ℂ) - α + 1 by linear_combination r2']
  -- the Wigner series
  have hW : genClearedFiniteHG α {-(α : ℂ), -((A1 : ℂ) + A2 + A3 + 1), -(γ : ℂ)}
        {-((A1 : ℂ) + γ), -((A3 : ℂ) + α)} =
      pochhammer (-((A1 + γ : ℕ) : ℂ)) α * pochhammer (-((A3 + α : ℕ) : ℂ)) α *
        generalizedHypergeometricTruncated α {-(α : ℂ), -((A1 : ℂ) + A2 + A3 + 1), -(γ : ℂ)}
          {-((A1 : ℂ) + γ), -((A3 : ℂ) + α)} 1 := by
    have n1 := pochhammer_neg_natCast_ne_zero (N := A1 + γ) (k := α) (by omega)
    have n2 := pochhammer_neg_natCast_ne_zero (N := A3 + α) (k := α) (by omega)
    push_cast at n1 n2 ⊢
    rw [genClearedFiniteHG_eq_mul]
    · simp only [pochhammerProduct, Multiset.insert_eq_cons, Multiset.map_cons,
          Multiset.map_singleton,
        Multiset.prod_cons, Multiset.prod_singleton]
    · simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
      rintro y (rfl | rfl)
      exacts [n1, n2]
  have hfloorA : ⌊j₁ + j₂ - j₃⌋.toNat = A1 := by rw [hA1, Int.floor_natCast, Int.toNat_natCast]
  have hfloor1 : ⌊j₁ - m₁⌋.toNat = α := by rw [hα, Int.floor_natCast, Int.toNat_natCast]
  have hfloor3 : ⌊j₃ + m₃⌋.toNat = γ := by rw [hγ, Int.floor_natCast, Int.toNat_natCast]
  have c1 : ((-j₁ - j₂ - j₃ - 1 : ℚ) : ℂ) = -((A1 : ℂ) + A2 + A3 + 1) := by
    rw [show (-j₁ - j₂ - j₃ - 1 : ℚ) = -((A1 : ℚ) + A2 + A3 + 1) by linarith]; push_cast; ring
  have c2 : ((-j₁ + m₁ : ℚ) : ℂ) = -(α : ℂ) := by
    rw [show (-j₁ + m₁ : ℚ) = -(α : ℚ) by linarith]; push_cast; ring
  have c3 : ((-j₃ - m₃ : ℚ) : ℂ) = -(γ : ℂ) := by
    rw [show (-j₃ - m₃ : ℚ) = -(γ : ℚ) by linarith]; push_cast; ring
  have c4 : ((-j₁ - j₂ - m₃ : ℚ) : ℂ) = -((A1 : ℂ) + γ) := by
    rw [show (-j₁ - j₂ - m₃ : ℚ) = -((A1 : ℚ) + γ) by linarith]; push_cast; ring
  have c5 : ((-j₂ - j₃ + m₁ : ℚ) : ℂ) = -((A3 : ℂ) + α) := by
    rw [show (-j₂ - j₃ + m₁ : ℚ) = -((A3 : ℚ) + α) by linarith]; push_cast; ring
  have hD : generalizedHypergeometricTruncated (min α γ)
      {-((A1 : ℂ) + A2 + A3 + 1), -(α : ℂ), -(γ : ℂ)}
      {-((A1 : ℂ) + γ), -((A3 : ℂ) + α)} 1 =
      generalizedHypergeometricTruncated α {-(α : ℂ), -((A1 : ℂ) + A2 + A3 + 1), -(γ : ℂ)}
        {-((A1 : ℂ) + γ), -((A3 : ℂ) + α)} 1 := by
    rw [show ({-((A1 : ℂ) + A2 + A3 + 1), -(α : ℂ), -(γ : ℂ)} : Multiset ℂ) =
      {-(α : ℂ), -((A1 : ℂ) + A2 + A3 + 1), -(γ : ℂ)} by
        simp only [Multiset.insert_eq_cons]; exact Multiset.cons_swap _ _ _]
    rcases le_total α γ with hle | hle
    · rw [min_eq_left hle]
    · rw [min_eq_right hle,
          generalizedHypergeometricTruncated_eq_of_neg_natCast_mem _ _ (N := γ) (by simp) hle]
  rw [hfloor1, hfloor3, c1, c2, c3, c4, c5, hD]
  unfold wigner3j
  simp only [h, ↓reduceIte]
  rw [hfloorA, hsum, Complex.ofReal_mul, hS, hB, hW, pochhammer_neg_coe_nat, pochhammer_neg_coe_nat]
  -- the real prefactors
  have hsign : signPow (j₁ - j₂ - m₃) = signPow (j₂ - m₁ + m₃) * (-1) ^ α := by
    rw [signPow_of_eq (n := (α' : ℤ) - β') (by push_cast; linarith),
      signPow_of_eq (n := (β' : ℤ) - α' + α) (by push_cast; linarith),
      show (α' : ℤ) - β' = ((β' : ℤ) - α' + α) + α + 2 * ((α' : ℤ) - β' - α) by ring,
      zpow_add₀ (by norm_num), zpow_add₀ (by norm_num), zpow_mul]
    norm_num
  have d1 : ((A1 + γ).descFactorial α : ℝ) * β'.factorial = (A1 + γ).factorial := by
    have := Nat.factorial_mul_descFactorial (n := A1 + γ) (k := α) (by omega)
    rw [show A1 + γ - α = β' by omega] at this
    exact_mod_cast (by linarith : (A1 + γ).descFactorial α * β'.factorial = (A1 + γ).factorial)
  have d2 : ((A3 + α).descFactorial α : ℝ) * A3.factorial = (A3 + α).factorial := by
    have := Nat.factorial_mul_descFactorial (n := A3 + α) (k := α) (by omega)
    rw [show A3 + α - α = A3 by omega] at this
    exact_mod_cast (by linarith : (A3 + α).descFactorial α * A3.factorial = (A3 + α).factorial)
  have hT : 0 ≤ (A1.factorial : ℝ) * A2.factorial * A3.factorial / (A1 + A2 + A3 + 1).factorial :=
    by positivity
  have hQ : 0 ≤ (α'.factorial : ℝ) * γ'.factorial / (α.factorial * β.factorial * β'.factorial *
      γ.factorial) := by positivity
  have hP6 : Real.sqrt (α'.factorial * α.factorial * β.factorial * β'.factorial * γ.factorial *
      γ'.factorial) = α.factorial * β.factorial * β'.factorial * γ.factorial *
        Real.sqrt ((α'.factorial : ℝ) * γ'.factorial / (α.factorial * β.factorial *
          β'.factorial * γ.factorial)) := by
    rw [show (α'.factorial : ℝ) * α.factorial * β.factorial * β'.factorial * γ.factorial *
      γ'.factorial = ((α.factorial : ℝ) * β.factorial * β'.factorial * γ.factorial) ^ 2 *
        ((α'.factorial : ℝ) * γ'.factorial / (α.factorial * β.factorial * β'.factorial *
          γ.factorial)) by field_simp,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have key : signPow (j₁ - j₂ - m₃) * triangleDelta j₁ j₂ j₃ *
      Real.sqrt (ratFactorial (j₁ + m₁) * ratFactorial (j₁ - m₁) * ratFactorial (j₂ + m₂) *
          ratFactorial (j₂ - m₂) *
        ratFactorial (j₃ + m₃) * ratFactorial (j₃ - m₃)) *
      ((-1) ^ α / (α.factorial * A2.factorial * γ.factorial * A1.factorial * β.factorial) *
        ((-1) ^ α * (A1 + γ).descFactorial α * ((-1) ^ α * (A3 + α).descFactorial α))) =
      signPow (j₂ - m₁ + m₃) * ratFactorial (j₁ + j₂ + m₃) * ratFactorial (j₂ + j₃ - m₁) /
          (triangleDelta j₁ j₂ j₃ * ratFactorial (j₁ + j₂ + j₃ + 1)) *
          Real.sqrt (ratFactorial (j₁ + m₁) * ratFactorial (j₃ - m₃) /
            (ratFactorial (j₁ - m₁) * ratFactorial (j₂ + m₂) * ratFactorial (j₂ - m₂) *
                ratFactorial (j₃ + m₃))) := by
    unfold triangleDelta
    rw [ratFactorial_of_eq hα', ratFactorial_of_eq hα, ratFactorial_of_eq hβ,
        ratFactorial_of_eq hβ', ratFactorial_of_eq hγ,
      ratFactorial_of_eq hγ', ratFactorial_of_eq hA1, ratFactorial_of_eq hA2,
          ratFactorial_of_eq hA3,
      ratFactorial_of_eq (x := j₁ + j₂ + j₃ + 1) (n := A1 + A2 + A3 + 1) (by push_cast; linarith),
      ratFactorial_of_eq (x := j₁ + j₂ + m₃) (n := A1 + γ) (by push_cast; linarith),
      ratFactorial_of_eq (x := j₂ + j₃ - m₁) (n := A3 + α) (by push_cast; linarith), hP6, hsign,
      ← d1, ← d2]
    have hΔ := Real.sq_sqrt hT
    have hΔ0 : Real.sqrt ((A1.factorial : ℝ) * A2.factorial * A3.factorial /
        (A1 + A2 + A3 + 1).factorial) ≠ 0 := by positivity
    have hs : ((-1 : ℝ) ^ α) ^ 2 = 1 := by rw [← pow_mul, pow_mul']; norm_num
    field_simp
    rw [hΔ, show ((-1 : ℝ) ^ α) ^ 4 = 1 by rw [← pow_mul, pow_mul']; norm_num]
    field_simp
  rw [← key]
  push_cast
  ring

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
    simp only [← Nat.cast_add, ratFactorial_natCast, ratInvFactorial_natCast, signPow_natCast]
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
    · rw [ratInvFactorial_of_neg (x := 0 - ((a + b : ℚ)) / 2 + ((b : ℚ) - a) / 2 + s)]
      · ring
      · have : (s : ℚ) < a := by exact_mod_cast hlt
        linarith
    · rw [ratInvFactorial_of_neg (x := ((a + b : ℚ)) / 2 + -(((b : ℚ) - a) / 2) - s)]
      · ring
      · have : (a : ℚ) < s := by exact_mod_cast hgt
        linarith
  · intro ha'
    simp at ha'


/-- Close a cast equation. -/
macro "wigner_ring_cast" : tactic => `(tactic| first | ring1 | (push_cast; ring1))

/-- The symmetric Racah sum with `x₁ = y₁ = n` reduces to its single term `s = n`. -/
private lemma symmetricRacahSum_intCast_intCast (n : ℤ) (x₂ x₃ y₂ y₃ : ℚ) :
    symmetricRacahSum n x₂ x₃ n y₂ y₃ =
      (-1 : ℝ) ^ n * (ratInvFactorial (x₂ - n) * ratInvFactorial (x₃ - n) *
          (ratInvFactorial (n - y₂) *
        ratInvFactorial (n - y₃))) := by
  unfold symmetricRacahSum
  rw [finsum_eq_single _ n]
  · simp only [sub_self]
    rw [show (0 : ℚ) = ((0 : ℕ) : ℚ) by simp, ratInvFactorial_natCast]
    simp
  · intro s hs
    rcases lt_or_gt_of_ne hs with h | h
    · rw [ratInvFactorial_of_neg (x := (s : ℚ) - n) (by
        have : (s : ℚ) < n := by exact_mod_cast h
        linarith)]
      ring
    · rw [ratInvFactorial_of_neg (x := (n : ℚ) - s) (by
        have : (n : ℚ) < s := by exact_mod_cast h
        linarith)]
      ring

/-- `symmetricRacahSum_intCast_intCast` with the coinciding arguments given by equations. -/
private lemma symmetricRacahSum_of_eq_intCast {x₁ x₂ x₃ y₁ y₂ y₃ : ℚ} (n : ℤ) (hx : x₁ = n)
    (hy : y₁ = n) :
    symmetricRacahSum x₁ x₂ x₃ y₁ y₂ y₃ =
      (-1 : ℝ) ^ n * (ratInvFactorial (x₂ - n) * ratInvFactorial (x₃ - n) *
          (ratInvFactorial (n - y₂) *
        ratInvFactorial (n - y₃))) := by
  subst hx hy; exact symmetricRacahSum_intCast_intCast n x₂ x₃ y₂ y₃

/-- The symmetric Racah sum with `x₁ = n + 1`, `y₁ = n` has the two terms `s = n, n + 1`. -/
private lemma symmetricRacahSum_of_eq_add_one {x₁ x₂ x₃ y₁ y₂ y₃ : ℚ} (n : ℤ) (hx : x₁ = n + 1)
    (hy : y₁ = n) :
    symmetricRacahSum x₁ x₂ x₃ y₁ y₂ y₃ =
      (-1 : ℝ) ^ n * (ratInvFactorial (x₂ - n) * ratInvFactorial (x₃ - n) *
          (ratInvFactorial (n - y₂) *
        ratInvFactorial (n - y₃)) - ratInvFactorial (x₂ - n - 1) * ratInvFactorial (x₃ - n - 1) *
        (ratInvFactorial (n + 1 - y₂) * ratInvFactorial (n + 1 - y₃))) := by
  subst hx hy
  unfold symmetricRacahSum
  rw [finsum_eq_sum_of_support_subset _ (s := {n, n + 1}) ?_,
    Finset.sum_pair (by omega)]
  · rw [zpow_add₀ (by norm_num)]
    push_cast
    simp only [sub_self, show ((n : ℚ) + 1 - n) = 1 by ring, ratInvFactorial_zero,
      ratInvFactorial_one]
    ring_nf
  · intro s hs
    simp only [Function.mem_support] at hs
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra hne
    simp only [not_or] at hne
    rcases lt_or_gt_of_ne hne.1 with h | h
    · apply hs
      rw [ratInvFactorial_of_neg (x := (s : ℚ) - n) (by
        have : (s : ℚ) < n := by exact_mod_cast h
        linarith)]
      ring
    · have h' : n + 1 < s := by omega
      apply hs
      rw [ratInvFactorial_of_neg (x := (n : ℚ) + 1 - s) (by
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
      ⟨⟨⟨c, by wigner_ring_cast⟩, ⟨1, by wigner_ring_cast⟩, ⟨1, by wigner_ring_cast⟩⟩,
          ⟨⟨0, by wigner_ring_cast⟩, ⟨c + 1, by wigner_ring_cast⟩⟩,
        ⟨⟨c + 1, by wigner_ring_cast⟩, ⟨0, by wigner_ring_cast⟩⟩,
            ⟨⟨1, by wigner_ring_cast⟩, ⟨1, by wigner_ring_cast⟩⟩, by ring⟩
    have hR : (0 : ℝ) ≤ ((1 + c).factorial : ℝ) := by positivity
    have hY : (0 : ℝ) ≤ ((c + 1 : ℝ)) * (c + 2) * (c + 3) := by positivity
    rw [show ((((0 : ℕ) : ℚ) + ((c + 1 : ℕ) : ℚ) : ℚ) : ℝ) *
        ((((0 : ℕ) : ℚ) + ((c + 1 : ℕ) : ℚ) : ℚ) + 1) *
        ((((0 : ℕ) : ℚ) + ((c + 1 : ℕ) : ℚ) : ℚ) + 2) =
      ((c + 1 : ℝ)) * (c + 2) * (c + 3) by push_cast; ring]
    rw [wigner3j_eq_sqrt_mul_symmetricRacahSum hadm, symmetricRacahSum_swap_x12,
        symmetricRacahSum_swap_y12,
      symmetricRacahSum_of_eq_add_one ((((0 : ℕ) : ℕ) : ℤ) - 1) (by push_cast; ring)
          (by push_cast; ring),
      signPow_of_eq (n := 0) (by push_cast; ring),
      signPow_of_eq (n := (((0 : ℕ) : ℕ) : ℤ)) (by push_cast; ring), zpow_natCast,
      zpow_sub_one₀ (by norm_num), zpow_natCast, zpow_zero, one_mul,
      sqrt_eq_div_sqrt_of_eq hR hY, div_mul_eq_mul_div]
    · congr 1
      wigner_cast_ring
      wigner_fin_simp
    · wigner_cast_ring
      wigner_fin_simp
  · have hadm : IsAdmissible3j ((((r + 1 : ℕ) : ℚ) + (q : ℚ)) / 2)
        ((((r + 1 : ℕ) : ℚ) + (q : ℚ)) / 2) 1
        ((((q : ℚ) : ℚ) - (r + 1 : ℕ)) / 2) (-((((q : ℚ) : ℚ) - (r + 1 : ℕ)) / 2)) 0 :=
      ⟨⟨⟨r + q, by wigner_ring_cast⟩, ⟨1, by wigner_ring_cast⟩, ⟨1, by wigner_ring_cast⟩⟩,
          ⟨⟨r + 1, by wigner_ring_cast⟩, ⟨q, by wigner_ring_cast⟩⟩,
        ⟨⟨q, by wigner_ring_cast⟩, ⟨r + 1, by wigner_ring_cast⟩⟩,
            ⟨⟨1, by wigner_ring_cast⟩, ⟨1, by wigner_ring_cast⟩⟩, by ring⟩
    have hR : (0 : ℝ) ≤ ((1 + r).factorial * q.factorial : ℝ) := by positivity
    have hY : (0 : ℝ) ≤ ((r + q + 1 : ℝ)) * (r + q + 2) * (r + q + 3) := by positivity
    rw [show ((((r + 1 : ℕ) : ℚ) + (q : ℚ) : ℚ) : ℝ) *
        ((((r + 1 : ℕ) : ℚ) + (q : ℚ) : ℚ) + 1) * ((((r + 1 : ℕ) : ℚ) + (q : ℚ) : ℚ) + 2) =
      ((r + q + 1 : ℝ)) * (r + q + 2) * (r + q + 3) by push_cast; ring]
    rw [wigner3j_eq_sqrt_mul_symmetricRacahSum hadm, symmetricRacahSum_swap_x12,
        symmetricRacahSum_swap_y12,
      symmetricRacahSum_of_eq_add_one ((((r + 1 : ℕ) : ℕ) : ℤ) - 1) (by push_cast; ring)
          (by push_cast; ring),
      signPow_of_eq (n := 0) (by push_cast; ring),
      signPow_of_eq (n := (((r + 1 : ℕ) : ℕ) : ℤ)) (by push_cast; ring), zpow_natCast,
      zpow_sub_one₀ (by norm_num), zpow_natCast, zpow_zero, one_mul,
      sqrt_eq_div_sqrt_of_eq hR hY, div_mul_eq_mul_div]
    · congr 1
      wigner_cast_ring
      wigner_fin_simp
    · wigner_cast_ring
      wigner_fin_simp

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
    ⟨⟨⟨r + q, by wigner_ring_cast⟩, ⟨1, by wigner_ring_cast⟩, ⟨1, by wigner_ring_cast⟩⟩,
        ⟨⟨r + 1, by wigner_ring_cast⟩, ⟨q, by wigner_ring_cast⟩⟩,
      ⟨⟨q + 1, by wigner_ring_cast⟩, ⟨r, by wigner_ring_cast⟩⟩,
          ⟨⟨0, by wigner_ring_cast⟩, ⟨2, by wigner_ring_cast⟩⟩, by ring⟩
  rw [wigner3j_eq_sqrt_mul_symmetricRacahSum hadm, symmetricRacahSum_swap_x23,
      symmetricRacahSum_swap_x12, symmetricRacahSum_swap_y12,
    symmetricRacahSum_of_eq_intCast (r : ℤ) (by push_cast; ring) (by push_cast; ring),
    signPow_of_eq (n := -1) (by push_cast; ring),
    signPow_of_eq (n := ((r + 1 : ℕ) : ℤ)) (by push_cast; ring), zpow_natCast, zpow_natCast,
    show (-1 : ℝ) ^ (-1 : ℤ) = -1 by norm_num]
  rw [show ∀ A X : ℝ, -1 * A * ((-1) ^ r * X) = (-1) ^ (r + 1) * (A * X) from
    fun A X => by ring]
  congr 1
  apply sqrt_mul_eq_sqrt_of_eq
  · wigner_cast_nonneg
  · wigner_cast_nonneg
  · wigner_cast_ring
    wigner_fin_simp

/-! ### Dixon's identity for the symmetric Racah sum -/

section Dixon

open DLMF.Hypergeometric

/-- `(m+1)_t = (m+t)!/m!`. -/
private lemma pochhammer_natCast_add_one (m t : ℕ) :
    pochhammer ((m : ℂ) + 1) t = ((m + t).factorial : ℂ) / m.factorial := by
  have h := Nat.factorial_mul_ascFactorial m t
  have hm : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  rw [eq_div_iff hm, pochhammer, show (m : ℂ) + 1 = ((m + 1 : ℕ) : ℂ) by push_cast; ring,
    ← ascPochhammer_eval_cast, ascPochhammer_nat_eq_ascFactorial, ← h]
  push_cast; ring

/-- `(-M)_t = (-1)^t M!/(M-t)!` for `t ≤ M`. -/
private lemma pochhammer_neg_natCast (M t : ℕ) (ht : t ≤ M) :
    pochhammer (-(M : ℂ)) t = (-1) ^ t * ((M.factorial : ℂ) / (M - t).factorial) := by
  have h := pochhammer_reflect (((M - t : ℕ) : ℂ) + 1) t
  rw [show (1 : ℂ) - (((M - t : ℕ) : ℂ) + 1) - t = -(M : ℂ) by push_cast [ht]; ring,
    pochhammer_natCast_add_one, Nat.sub_add_cancel ht] at h
  exact h

/-- Dixon's identity in factorial form, from the even terminating Dixon sum. -/
private lemma dixon_factorial_sum (A B C : ℕ) (hB : A ≤ B) (hC : A ≤ C) :
    ∑ t ∈ range (2 * A + 1), (-1 : ℂ) ^ t / ((2 * A - t).factorial * (A + B - t).factorial *
      (A + C - t).factorial * t.factorial * (B - A + t).factorial * (C - A + t).factorial) =
      (-1) ^ A * ((A + B + C).factorial / (A.factorial * B.factorial * C.factorial *
        (A + B).factorial * (B + C).factorial * (A + C).factorial)) := by
  have hb : LowerParametersRegular
      {1 - (-((A : ℂ) + B)) - 2 * A, 1 - (-((A : ℂ) + C)) - 2 * A} := by
    intro x hx n hn
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · have : ((B - A + 1 + n : ℕ) : ℂ) = 0 := by push_cast [hB]; linear_combination hn
      exact absurd (by exact_mod_cast this : B - A + 1 + n = 0) (by omega)
    · have : ((C - A + 1 + n : ℕ) : ℂ) = 0 := by push_cast [hC]; linear_combination hn
      exact absurd (by exact_mod_cast this : C - A + 1 + n = 0) (by omega)
  have hD := generalizedHypergeometric_dixon_terminating_even A (-((A : ℂ) + B)) (-((A : ℂ) + C)) hb
  have hf : ∀ m : ℕ, (m.factorial : ℂ) ≠ 0 := fun m => by exact_mod_cast m.factorial_ne_zero
  have hterm : ∀ t ∈ range (2 * A + 1),
      generalizedHypergeometricCoeff {(-(2 * A) : ℂ), -((A : ℂ) + B),
      -((A : ℂ) + C)} {1 - (-((A : ℂ) + B)) - 2 * A, 1 - (-((A : ℂ) + C)) - 2 * A} t * 1 ^ t =
      ((2 * A).factorial * (A + B).factorial * (A + C).factorial * (B - A).factorial *
        (C - A).factorial : ℂ) * ((-1 : ℂ) ^ t / ((2 * A - t).factorial *
          (A + B - t).factorial * (A + C - t).factorial * t.factorial *
            (B - A + t).factorial * (C - A + t).factorial)) := by
    intro t ht
    have ht' : t ≤ 2 * A := Nat.lt_succ_iff.mp (mem_range.mp ht)
    have h1 := pochhammer_neg_natCast (2 * A) t ht'
    have h2 := pochhammer_neg_natCast (A + B) t (by omega)
    have h3 := pochhammer_neg_natCast (A + C) t (by omega)
    have h4 := pochhammer_natCast_add_one (B - A) t
    have h5 := pochhammer_natCast_add_one (C - A) t
    push_cast at h1 h2 h3
    rw [show ((B - A : ℕ) : ℂ) + 1 = 1 - (-((A : ℂ) + B)) - 2 * A by push_cast [hB]; ring] at h4
    rw [show ((C - A : ℕ) : ℂ) + 1 = 1 - (-((A : ℂ) + C)) - 2 * A by push_cast [hC]; ring] at h5
    simp only [generalizedHypergeometricCoeff, pochhammerProduct, Multiset.insert_eq_cons,
        Multiset.map_cons,
      Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, one_pow, mul_one]
    rw [h1, h2, h3, h4, h5]
    have := hf (2 * A - t); have := hf (A + B - t); have := hf (A + C - t); have := hf t
    have := hf (B - A + t); have := hf (C - A + t); have := hf (B - A); have := hf (C - A)
    have hs2 : (-1 : ℂ) ^ (t * 2) = 1 := by rw [mul_comm, pow_mul]; simp
    field_simp
    linear_combination ((2 * A).factorial * (A + B).factorial * (A + C).factorial : ℂ) * hs2
  unfold generalizedHypergeometricTruncated at hD
  rw [sum_congr rfl hterm, ← mul_sum] at hD
  have hP1 := pochhammer_neg_natCast (A + B + C) A (by omega)
  have hP2 := pochhammer_neg_natCast B A hB
  have hP3 := pochhammer_neg_natCast C A hC
  rw [show -((A + B + C : ℕ) : ℂ) = -((A : ℂ) + B) + -((A : ℂ) + C) + A by push_cast; ring,
    show A + B + C - A = B + C by omega] at hP1
  rw [show -(B : ℂ) = -((A : ℂ) + B) + A by ring] at hP2
  rw [show -(C : ℂ) = -((A : ℂ) + C) + A by ring] at hP3
  rw [hP1, hP2, hP3] at hD
  have hM : ((2 * A).factorial * (A + B).factorial * (A + C).factorial * (B - A).factorial *
      (C - A).factorial : ℂ) ≠ 0 := by
    have := hf (2 * A); have := hf (A + B); have := hf (A + C); have := hf (B - A)
    have := hf (C - A)
    positivity
  apply mul_left_cancel₀ hM
  rw [hD]
  have hs2 : (-1 : ℂ) ^ (A * 2) = 1 := by rw [mul_comm, pow_mul]; simp
  have := hf A; have := hf B; have := hf C; have := hf (B + C); have := hf (A + B + C)
  have := hf (2 * A); have := hf (A + B); have := hf (A + C); have := hf (B - A)
  have := hf (C - A)
  field_simp
  linear_combination -hs2

/-- Dixon's identity for the symmetric Racah sum, when `A` is the smallest parameter. -/
private lemma symmetricRacahSum_dixon_of_le (A B C : ℕ) (hB : A ≤ B) (hC : A ≤ C) :
    symmetricRacahSum ((2 * A : ℕ) : ℚ) ((A + B : ℕ) : ℚ) ((A + C : ℕ) : ℚ) 0
      ((A : ℚ) - B) ((A : ℚ) - C) =
      (-1) ^ A * ((A + B + C).factorial / (A.factorial * B.factorial * C.factorial *
        (A + B).factorial * (B + C).factorial * (A + C).factorial)) := by
  unfold symmetricRacahSum
  rw [finsum_eq_sum_of_support_subset _
    (s := (range (2 * A + 1)).map Nat.castEmbedding) ?_, Finset.sum_map]
  · apply Complex.ofReal_injective
    have hD := dixon_factorial_sum A B C hB hC
    push_cast
    rw [← hD]
    refine sum_congr rfl fun t ht => ?_
    have ht' : t ≤ 2 * A := Nat.lt_succ_iff.mp (mem_range.mp ht)
    simp only [Nat.castEmbedding_apply, Int.cast_natCast, zpow_natCast]
    rw [ratInvFactorial_of_eq (n := 2 * A - t) (by push_cast [ht']; ring),
      ratInvFactorial_of_eq (n := A + B - t) (by push_cast [show t ≤ A + B by omega]; ring),
      ratInvFactorial_of_eq (n := A + C - t) (by push_cast [show t ≤ A + C by omega]; ring),
      ratInvFactorial_of_eq (n := t) (by ring),
      ratInvFactorial_of_eq (n := B - A + t) (by push_cast [hB]; ring),
      ratInvFactorial_of_eq (n := C - A + t) (by push_cast [hC]; ring)]
    push_cast
    field_simp
  · intro s hs
    simp only [Function.mem_support] at hs
    have h1 : ratInvFactorial (((2 * A : ℕ) : ℚ) - s) ≠ 0 := fun h0 => hs (by rw [h0]; ring)
    have h2 : ratInvFactorial ((s : ℚ) - 0) ≠ 0 := fun h0 => hs (by rw [h0]; ring)
    rw [Ne, ratInvFactorial_eq_zero_iff_neg, not_lt] at h1 h2
    simp only [coe_map, Nat.castEmbedding_apply, coe_range, Set.mem_image, Set.mem_Iio]
    refine ⟨s.toNat, ?_, Int.toNat_of_nonneg (by exact_mod_cast (by linarith : (0 : ℚ) ≤ s))⟩
    have : (s : ℚ) ≤ ((2 * A : ℕ) : ℚ) := by linarith
    have h3 : s ≤ ((2 * A : ℕ) : ℤ) := by exact_mod_cast this
    omega

/-- Dixon's identity for the symmetric Racah sum with parameters `a, b, c`. -/
private lemma symmetricRacahSum_dixon (a b c : ℕ) :
    symmetricRacahSum ((2 * a : ℕ) : ℚ) ((a + b : ℕ) : ℚ) ((a + c : ℕ) : ℚ) 0
      ((a : ℚ) - b) ((a : ℚ) - c) =
      (-1) ^ a * ((a + b + c).factorial / (a.factorial * b.factorial * c.factorial *
        (a + b).factorial * (b + c).factorial * (a + c).factorial)) := by
  have hswap : ∀ a b c : ℕ, symmetricRacahSum ((2 * a : ℕ) : ℚ) ((a + b : ℕ) : ℚ)
      ((a + c : ℕ) : ℚ) 0 ((a : ℚ) - b) ((a : ℚ) - c) = symmetricRacahSum ((2 * a : ℕ) : ℚ)
        ((a + c : ℕ) : ℚ) ((a + b : ℕ) : ℚ) 0 ((a : ℚ) - c) ((a : ℚ) - b) := fun a b c => by
    rw [symmetricRacahSum_swap_x23, symmetricRacahSum_swap_y23]
  have hshift : ∀ a b c : ℕ, symmetricRacahSum ((2 * a : ℕ) : ℚ) ((a + b : ℕ) : ℚ)
      ((a + c : ℕ) : ℚ) 0 ((a : ℚ) - b) ((a : ℚ) - c) = (-1 : ℝ) ^ ((a : ℤ) - b) *
        symmetricRacahSum ((2 * b : ℕ) : ℚ) ((b + a : ℕ) : ℚ) ((b + c : ℕ) : ℚ) 0
          ((b : ℚ) - a) ((b : ℚ) - c) := fun a b c => by
    rw [← symmetricRacahSum_add_intCast _ _ _ _ _ _ ((a : ℚ) - b) ((a : ℤ) - b)
        (by push_cast; ring),
      symmetricRacahSum_swap_x12, symmetricRacahSum_swap_y12]
    congr 1 <;> push_cast <;> ring
  have hK : ∀ a b c : ℕ, ((a + b + c).factorial / (a.factorial * b.factorial * c.factorial *
      (a + b).factorial * (b + c).factorial * (a + c).factorial) : ℝ) =
      (b + a + c).factorial / (b.factorial * a.factorial * c.factorial *
        (b + a).factorial * (a + c).factorial * (b + c).factorial) := fun a b c => by
    rw [Nat.add_comm b a]; ring
  have hK' : ∀ a b c : ℕ, ((a + b + c).factorial / (a.factorial * b.factorial * c.factorial *
      (a + b).factorial * (b + c).factorial * (a + c).factorial) : ℝ) =
      (a + c + b).factorial / (a.factorial * c.factorial * b.factorial *
        (a + c).factorial * (c + b).factorial * (a + b).factorial) := fun a b c => by
    rw [Nat.add_comm c b, Nat.add_right_comm a c b]; ring
  have hcase2 : ∀ a b c : ℕ, b ≤ a → b ≤ c → symmetricRacahSum ((2 * a : ℕ) : ℚ)
      ((a + b : ℕ) : ℚ) ((a + c : ℕ) : ℚ) 0 ((a : ℚ) - b) ((a : ℚ) - c) =
      (-1) ^ a * ((a + b + c).factorial / (a.factorial * b.factorial * c.factorial *
        (a + b).factorial * (b + c).factorial * (a + c).factorial)) := fun a b c hba hbc => by
    rw [hshift, symmetricRacahSum_dixon_of_le b a c hba hbc, ← hK, ← mul_assoc]
    congr 1
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
    congr 1; ring
  rcases le_total a b with hab | hab
  · rcases le_total a c with hac | hac
    · exact symmetricRacahSum_dixon_of_le a b c hab hac
    · rw [hswap, hcase2 a c b hac (by omega), hK']
  · rcases le_total b c with hbc | hbc
    · exact hcase2 a b c hab hbc
    · rw [hswap, hcase2 a c b (by omega) (by omega), hK']

end Dixon

/-- DLMF 34.3.4–34.3.5, `J = j₁ + j₂ + j₃ = 2n` even:
`(j₁ j₂ j₃; 0 0 0) = (-1)^{J/2} ((J-2j₁)!(J-2j₂)!(J-2j₃)!/(J+1)!)^{1/2}`
`× (J/2)! / ((J/2-j₁)!(J/2-j₂)!(J/2-j₃)!)`, for integers `jᵣ` satisfying the triangle
conditions. -/
@[dlmf 34.3.E4, dlmf 34.3.E5]
theorem wigner3j_zero_zero_zero_of_even {j₁ j₂ j₃ : ℚ} (h : IsTriad j₁ j₂ j₃)
    (h₁ : IsNatQ j₁) (h₂ : IsNatQ j₂) (h₃ : IsNatQ j₃) (n : ℕ) (hJ : j₁ + j₂ + j₃ = 2 * n) :
    wigner3j j₁ j₂ j₃ 0 0 0 =
      (-1 : ℝ) ^ n * Real.sqrt (ratFactorial (2 * n - 2 * j₁) * ratFactorial (2 * n - 2 * j₂) *
        ratFactorial (2 * n - 2 * j₃) / ratFactorial (2 * n + 1)) *
        (n.factorial / (ratFactorial (n - j₁) * ratFactorial (n - j₂) *
            ratFactorial (n - j₃))) := by
  obtain ⟨p₁, rfl⟩ := h₁
  obtain ⟨p₂, rfl⟩ := h₂
  obtain ⟨p₃, rfl⟩ := h₃
  obtain ⟨⟨x₃, hx₃⟩, ⟨x₂, hx₂⟩, ⟨x₁, hx₁⟩⟩ := h
  have hJ' : p₁ + p₂ + p₃ = 2 * n := by exact_mod_cast hJ
  have e₃ : p₁ + p₂ = p₃ + x₃ := by exact_mod_cast (by linarith : (p₁ : ℚ) + p₂ = p₃ + x₃)
  have e₂ : p₁ + p₃ = p₂ + x₂ := by exact_mod_cast (by linarith : (p₁ : ℚ) + p₃ = p₂ + x₂)
  have e₁ : p₂ + p₃ = p₁ + x₁ := by exact_mod_cast (by linarith : (p₂ : ℚ) + p₃ = p₁ + x₁)
  -- the Dixon parameters `a = n - j₃`, `b = n - j₂`, `c = n - j₁`
  obtain ⟨a, b, c, rfl, rfl, rfl, rfl⟩ : ∃ a b c : ℕ, p₁ = a + b ∧ p₂ = a + c ∧ p₃ = b + c ∧
      n = a + b + c := ⟨n - p₃, n - p₂, n - p₁, by omega, by omega, by omega, by omega⟩
  have hadm : IsAdmissible3j ((a + b : ℕ) : ℚ) ((a + c : ℕ) : ℚ) ((b + c : ℕ) : ℚ) 0 0 0 :=
    ⟨⟨⟨x₃, hx₃⟩, ⟨x₂, hx₂⟩, ⟨x₁, hx₁⟩⟩, ⟨⟨a + b, by simp⟩, ⟨a + b, by simp⟩⟩,
      ⟨⟨a + c, by simp⟩, ⟨a + c, by simp⟩⟩, ⟨⟨b + c, by simp⟩, ⟨b + c, by simp⟩⟩, by ring⟩
  rw [wigner3j_eq_sqrt_mul_symmetricRacahSum hadm]
  have hS := symmetricRacahSum_dixon a b c
  rw [show symmetricRacahSum (((a + b : ℕ) : ℚ) + ((a + c : ℕ) : ℚ) - ((b + c : ℕ) : ℚ))
      (((a + b : ℕ) : ℚ) - 0) (((a + c : ℕ) : ℚ) + 0) 0 (((a + c : ℕ) : ℚ) -
        ((b + c : ℕ) : ℚ) - 0) (((a + b : ℕ) : ℚ) - ((b + c : ℕ) : ℚ) + 0) =
      symmetricRacahSum ((2 * a : ℕ) : ℚ) ((a + b : ℕ) : ℚ) ((a + c : ℕ) : ℚ) 0
        ((a : ℚ) - b) ((a : ℚ) - c) by congr 1 <;> push_cast <;> ring, hS,
    signPow_of_eq (n := (b : ℤ) - c) (by push_cast; ring)]
  have hf : ∀ m : ℕ, (m.factorial : ℝ) ≠ 0 := fun m => by exact_mod_cast m.factorial_ne_zero
  set P : ℕ := a + b with hP
  set Q : ℕ := a + c with hQ
  set R : ℕ := b + c with hR
  set N : ℕ := a + b + c with hN
  rw [ratFactorial_of_eq (x := (P : ℚ) + Q - R) (n := 2 * a) (by push_cast [hP, hQ, hR]; ring),
    ratFactorial_of_eq (x := (P : ℚ) - Q + R) (n := 2 * b) (by push_cast [hP, hQ, hR]; ring),
    ratFactorial_of_eq (x := -(P : ℚ) + Q + R) (n := 2 * c) (by push_cast [hP, hQ, hR]; ring),
    ratFactorial_of_eq (x := (P : ℚ) + Q + R + 1) (n := 2 * N + 1)
      (by push_cast [hP, hQ, hR, hN]; ring),
    ratFactorial_of_eq (x := (P : ℚ) + 0) (n := P) (by ring),
    ratFactorial_of_eq (x := (P : ℚ) - 0) (n := P) (by ring),
    ratFactorial_of_eq (x := (Q : ℚ) + 0) (n := Q) (by ring),
    ratFactorial_of_eq (x := (Q : ℚ) - 0) (n := Q) (by ring),
    ratFactorial_of_eq (x := (R : ℚ) + 0) (n := R) (by ring),
    ratFactorial_of_eq (x := (R : ℚ) - 0) (n := R) (by ring),
    ratFactorial_of_eq (x := 2 * (N : ℚ) - 2 * P) (n := 2 * c) (by push_cast [hP, hN]; ring),
    ratFactorial_of_eq (x := 2 * (N : ℚ) - 2 * Q) (n := 2 * b) (by push_cast [hQ, hN]; ring),
    ratFactorial_of_eq (x := 2 * (N : ℚ) - 2 * R) (n := 2 * a) (by push_cast [hR, hN]; ring),
    ratFactorial_of_eq (x := 2 * (N : ℚ) + 1) (n := 2 * N + 1) (by push_cast; ring),
    ratFactorial_of_eq (x := (N : ℚ) - P) (n := c) (by push_cast [hP, hN]; ring),
    ratFactorial_of_eq (x := (N : ℚ) - Q) (n := b) (by push_cast [hQ, hN]; ring),
    ratFactorial_of_eq (x := (N : ℚ) - R) (n := a) (by push_cast [hR, hN]; ring)]
  have hX : (0 : ℝ) ≤ ((2 * a).factorial : ℝ) * (2 * b).factorial * (2 * c).factorial /
      (2 * N + 1).factorial := by positivity
  rw [show ((P.factorial : ℝ) * P.factorial * Q.factorial * Q.factorial * R.factorial *
      R.factorial) = ((P.factorial : ℝ) * Q.factorial * R.factorial) ^ 2 by ring,
    Real.sqrt_mul hX, Real.sqrt_sq (by positivity)]
  have hsgn : (-1 : ℝ) ^ ((b : ℤ) - c) * (-1) ^ a = (-1) ^ N := by
    rw [show ((b : ℤ) - c) = ((b + c : ℕ) : ℤ) - 2 * (c : ℤ) by push_cast; ring,
      zpow_sub₀ (by norm_num), zpow_natCast, zpow_mul, show ((-1 : ℝ) ^ (2 : ℤ)) = 1 by norm_num,
      one_zpow, div_one, ← pow_add, hN]
    ring_nf
  rw [← hsgn, show ((2 * c).factorial : ℝ) * (2 * b).factorial * (2 * a).factorial =
    (2 * a).factorial * (2 * b).factorial * (2 * c).factorial by ring]
  field_simp

/-! ### Single-term evaluations -/

/-- Finish `s * √A * B = s * √C` from `A * B² = C`. -/
macro "wigner_finish" : tactic => `(tactic|
  (simp only [mul_assoc]
   congr 1
   apply sqrt_mul_eq_sqrt_of_eq (by positivity) (by positivity)
   first | (field_simp; done) | (field_simp; ring1)))

/-- The symmetric Racah sum with `x₁ = y₁ = 0`. -/
private lemma symmetricRacahSum_x₁_y₁_zero (x₂ x₃ y₂ y₃ : ℚ) :
    symmetricRacahSum 0 x₂ x₃ 0 y₂ y₃ = ratInvFactorial x₂ * ratInvFactorial x₃ *
        (ratInvFactorial (-y₂) * ratInvFactorial (-y₃)) := by
  have := symmetricRacahSum_intCast_intCast 0 x₂ x₃ y₂ y₃
  simp only [Int.cast_zero, sub_zero, zero_sub, zpow_zero, one_mul] at this
  exact this

/-- The symmetric Racah sum with `x₂ = y₁ = 0`. -/
private lemma symmetricRacahSum_x₂_y₁_zero (x₁ x₃ y₂ y₃ : ℚ) :
    symmetricRacahSum x₁ 0 x₃ 0 y₂ y₃ = ratInvFactorial x₁ * ratInvFactorial x₃ *
        (ratInvFactorial (-y₂) * ratInvFactorial (-y₃)) := by
  rw [symmetricRacahSum_swap_x12, symmetricRacahSum_x₁_y₁_zero]

/-- The symmetric Racah sum with `x₃ = y₁ = 0`. -/
private lemma symmetricRacahSum_x₃_y₁_zero (x₁ x₂ y₂ y₃ : ℚ) :
    symmetricRacahSum x₁ x₂ 0 0 y₂ y₃ = ratInvFactorial x₁ * ratInvFactorial x₂ *
        (ratInvFactorial (-y₂) * ratInvFactorial (-y₃)) := by
  rw [← symmetricRacahSum_cycle_x, symmetricRacahSum_x₁_y₁_zero]

/-- DLMF 34.3.6: the stretched case `j₃ = j₁ + j₂`,
`(j₁ j₂ j₁+j₂; m₁ m₂ -m₁-m₂) = (-1)^{j₁-j₂+m₁+m₂}`
`× ((2j₁)!(2j₂)!(j₁+j₂+m₁+m₂)!(j₁+j₂-m₁-m₂)!`
`/ ((2j₁+2j₂+1)!(j₁+m₁)!(j₁-m₁)!(j₂+m₂)!(j₂-m₂)!))^{1/2}`.
-/
@[dlmf 34.3.E6]
theorem wigner3j_stretched {j₁ j₂ m₁ m₂ : ℚ} (h₁ : IsProjection j₁ m₁)
    (h₂ : IsProjection j₂ m₂) :
    wigner3j j₁ j₂ (j₁ + j₂) m₁ m₂ (-m₁ - m₂) =
      signPow (j₁ - j₂ + m₁ + m₂) * Real.sqrt (ratFactorial (2 * j₁) * ratFactorial (2 * j₂) *
        ratFactorial (j₁ + j₂ + m₁ + m₂) * ratFactorial (j₁ + j₂ - m₁ - m₂) /
        (ratFactorial (2 * j₁ + 2 * j₂ + 1) * ratFactorial (j₁ + m₁) * ratFactorial (j₁ - m₁) *
            ratFactorial (j₂ + m₂) *
          ratFactorial (j₂ - m₂))) := by
  obtain ⟨⟨p₁, hp₁⟩, ⟨q₁, hq₁⟩⟩ := h₁
  obtain ⟨⟨p₂, hp₂⟩, ⟨q₂, hq₂⟩⟩ := h₂
  obtain rfl : j₁ = ((p₁ : ℚ) + q₁) / 2 := by linarith
  obtain rfl : m₁ = ((q₁ : ℚ) - p₁) / 2 := by linarith
  obtain rfl : j₂ = ((p₂ : ℚ) + q₂) / 2 := by linarith
  obtain rfl : m₂ = ((q₂ : ℚ) - p₂) / 2 := by linarith
  have hadm : IsAdmissible3j (((p₁ : ℚ) + q₁) / 2) (((p₂ : ℚ) + q₂) / 2)
      (((p₁ : ℚ) + q₁) / 2 + ((p₂ : ℚ) + q₂) / 2) (((q₁ : ℚ) - p₁) / 2)
      (((q₂ : ℚ) - p₂) / 2) (-(((q₁ : ℚ) - p₁) / 2) - ((q₂ : ℚ) - p₂) / 2) :=
    ⟨⟨⟨0, by wigner_ring_cast⟩, ⟨p₁ + q₁, by wigner_ring_cast⟩, ⟨p₂ + q₂, by wigner_ring_cast⟩⟩,
      ⟨⟨p₁, by wigner_ring_cast⟩, ⟨q₁, by wigner_ring_cast⟩⟩,
      ⟨⟨p₂, by wigner_ring_cast⟩, ⟨q₂, by wigner_ring_cast⟩⟩,
      ⟨⟨q₁ + q₂, by wigner_ring_cast⟩, ⟨p₁ + p₂, by wigner_ring_cast⟩⟩, by ring⟩
  rw [wigner3j_eq_sqrt_mul_symmetricRacahSum hadm, sub_self, symmetricRacahSum_x₁_y₁_zero]
  ring_nf
  simp only [one_add_natCast_eq, ← Nat.cast_add, ratFactorial_natCast, ratInvFactorial_natCast,
    ratFactorial_zero, one_mul]
  wigner_finish

/-- DLMF 34.3.7: `(j₁ j₂ j₃; j₁ -j₁-m₃ m₃) = (-1)^{j₁-j₂-m₃}`
`× ((2j₁)!(-j₁+j₂+j₃)!(j₁+j₂+m₃)!(j₃-m₃)!`
`/ ((j₁+j₂+j₃+1)!(j₁-j₂+j₃)!(j₁+j₂-j₃)!(-j₁+j₂-m₃)!(j₃+m₃)!))^{1/2}`,
assuming the triangle conditions and that `m₃` and `-j₁-m₃` are projections of `j₃` and `j₂`.
-/
@[dlmf 34.3.E7]
theorem wigner3j_top {j₁ j₂ j₃ m₃ : ℚ} (h : IsTriad j₁ j₂ j₃) (h₂ : IsProjection j₂ (-j₁ - m₃))
    (h₃ : IsProjection j₃ m₃) :
    wigner3j j₁ j₂ j₃ j₁ (-j₁ - m₃) m₃ =
      signPow (j₁ - j₂ - m₃) * Real.sqrt (ratFactorial (2 * j₁) * ratFactorial (-j₁ + j₂ + j₃) *
        ratFactorial (j₁ + j₂ + m₃) * ratFactorial (j₃ - m₃) /
        (ratFactorial (j₁ + j₂ + j₃ + 1) * ratFactorial (j₁ - j₂ + j₃) *
            ratFactorial (j₁ + j₂ - j₃) *
          ratFactorial (-j₁ + j₂ - m₃) * ratFactorial (j₃ + m₃))) := by
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
    ⟨⟨⟨a₁, by wigner_ring_cast⟩, ⟨a₂, by wigner_ring_cast⟩, ⟨c + e, by wigner_ring_cast⟩⟩,
      ⟨⟨0, by wigner_ring_cast⟩, ⟨a₁ + a₂, by wigner_ring_cast⟩⟩,
      ⟨⟨a₁ + e, by wigner_ring_cast⟩, ⟨c, by wigner_ring_cast⟩⟩,
      ⟨⟨a₂ + c, by wigner_ring_cast⟩, ⟨e, by wigner_ring_cast⟩⟩, by ring⟩
  rw [wigner3j_eq_sqrt_mul_symmetricRacahSum hadm]
  ring_nf
  simp only [symmetricRacahSum_x₂_y₁_zero, neg_neg, one_add_natCast_eq,
      ← Nat.cast_add, ratFactorial_natCast,
    ratInvFactorial_natCast, ratFactorial_zero, mul_one]
  wigner_finish

/-! ## §34.3(ii) Symmetry -/

/-- DLMF 34.3.8, first equality: invariance under the cyclic permutation of the columns. -/
@[dlmf 34.3.E8]
theorem wigner3j_cycle (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ) :
    wigner3j j₁ j₂ j₃ m₁ m₂ m₃ = wigner3j j₂ j₃ j₁ m₂ m₃ m₁ := by
  by_cases hm : m₁ + m₂ + m₃ = 0
  swap
  · rw [wigner3j_eq_zero_of_add_add_ne_zero hm,
        wigner3j_eq_zero_of_add_add_ne_zero (fun h => hm (by linarith))]
  obtain rfl : m₃ = -m₁ - m₂ := by linarith
  have hiff : IsAdmissible3j j₁ j₂ j₃ m₁ m₂ (-m₁ - m₂) ↔
      IsAdmissible3j j₂ j₃ j₁ m₂ (-m₁ - m₂) m₁ := by
    unfold IsAdmissible3j IsTriad IsProjection
    constructor <;> rintro ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, ⟨h6, h7⟩, ⟨h8, h9⟩, -⟩ <;>
      exact ⟨⟨by wigner_pick9, by wigner_pick9, by wigner_pick9⟩,
          ⟨by wigner_pick9, by wigner_pick9⟩,
        ⟨by wigner_pick9, by wigner_pick9⟩, ⟨by wigner_pick9, by wigner_pick9⟩, by ring⟩
  by_cases h : IsAdmissible3j j₁ j₂ j₃ m₁ m₂ (-m₁ - m₂)
  · have h' := hiff.mp h
    rw [wigner3j_eq_sqrt_mul_symmetricRacahSum h, wigner3j_eq_sqrt_mul_symmetricRacahSum h']
    obtain ⟨-, ⟨⟨p₁, hp₁⟩, ⟨q₁, hq₁⟩⟩, ⟨⟨p₂, hp₂⟩, ⟨q₂, hq₂⟩⟩, ⟨⟨p₃, hp₃⟩, ⟨q₃, hq₃⟩⟩, -⟩ := h
    have hpq : q₁ + q₂ + q₃ = p₁ + p₂ + p₃ := by
      exact_mod_cast (by linarith : (q₁ : ℚ) + q₂ + q₃ = p₁ + p₂ + p₃)
    have e : symmetricRacahSum (j₂ + j₃ - j₁) (j₂ - m₂) (j₃ + (-m₁ - m₂)) 0 (j₃ - j₁ - m₂)
        (j₂ - j₁ + (-m₁ - m₂)) =
        symmetricRacahSum ((j₂ + m₂) + (j₃ - j₁ - m₂)) ((j₁ + j₂ - j₃) + (j₃ - j₁ - m₂))
          ((j₁ - m₁) + (j₃ - j₁ - m₂)) ((j₁ - j₃ + m₂) + (j₃ - j₁ - m₂))
          (0 + (j₃ - j₁ - m₂)) ((j₂ - j₃ - m₁) + (j₃ - j₁ - m₂)) := by
      congr 1 <;> ring
    rw [e, symmetricRacahSum_add_intCast _ _ _ _ _ _ _ ((q₃ : ℤ) - p₁) (by push_cast; linarith),
      ← symmetricRacahSum_cycle_x, ← symmetricRacahSum_cycle_y, ← symmetricRacahSum_cycle_x,
          ← symmetricRacahSum_cycle_y,
      signPow_of_eq (x := j₁ - j₂ - (-m₁ - m₂)) (n := (q₁ : ℤ) - p₂) (by push_cast; linarith),
      signPow_of_eq (x := j₂ - j₃ - m₁) (n := (q₂ : ℤ) - p₃) (by push_cast; linarith)]
    have hs : (-1 : ℝ) ^ ((q₂ : ℤ) - p₃) * (-1) ^ ((q₃ : ℤ) - p₁) = (-1) ^ ((q₁ : ℤ) - p₂) := by
      rw [← zpow_add₀ (by norm_num)]
      exact neg_one_zpow_eq_of_eq_add_two_mul ((p₂ : ℤ) - q₁) (by omega)
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
  · rw [wigner3j_eq_zero_of_add_add_ne_zero hm,
        wigner3j_eq_zero_of_add_add_ne_zero (fun h => hm (by linarith)), mul_zero]
  obtain rfl : m₃ = -m₁ - m₂ := by linarith
  have hiff : IsAdmissible3j j₁ j₂ j₃ m₁ m₂ (-m₁ - m₂) ↔
      IsAdmissible3j j₂ j₁ j₃ m₂ m₁ (-m₁ - m₂) := by
    unfold IsAdmissible3j IsTriad IsProjection
    constructor <;> rintro ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, ⟨h6, h7⟩, ⟨h8, h9⟩, -⟩ <;>
      exact ⟨⟨by wigner_pick9, by wigner_pick9, by wigner_pick9⟩,
          ⟨by wigner_pick9, by wigner_pick9⟩,
        ⟨by wigner_pick9, by wigner_pick9⟩, ⟨by wigner_pick9, by wigner_pick9⟩, by ring⟩
  by_cases h : IsAdmissible3j j₁ j₂ j₃ m₁ m₂ (-m₁ - m₂)
  · have h' := hiff.mp h
    rw [wigner3j_eq_sqrt_mul_symmetricRacahSum h, wigner3j_eq_sqrt_mul_symmetricRacahSum h']
    obtain ⟨⟨⟨a₁, ha₁⟩, -, -⟩, ⟨⟨p₁, hp₁⟩, ⟨q₁, hq₁⟩⟩, ⟨⟨p₂, hp₂⟩, ⟨q₂, hq₂⟩⟩,
      ⟨⟨p₃, hp₃⟩, ⟨q₃, hq₃⟩⟩, -⟩ := h
    have ha : 2 * a₁ + p₃ + q₃ = p₁ + q₁ + p₂ + q₂ := by
      exact_mod_cast (by linarith : 2 * (a₁ : ℚ) + p₃ + q₃ = p₁ + q₁ + p₂ + q₂)
    have e : symmetricRacahSum (j₂ + j₁ - j₃) (j₂ - m₂) (j₁ + m₁) 0 (j₁ - j₃ - m₂) (j₂ - j₃ + m₁) =
        symmetricRacahSum (-0 + (j₁ + j₂ - j₃)) (-(j₁ - j₃ + m₂) + (j₁ + j₂ - j₃))
          (-(j₂ - j₃ - m₁) + (j₁ + j₂ - j₃)) (-(j₁ + j₂ - j₃) + (j₁ + j₂ - j₃))
          (-(j₂ + m₂) + (j₁ + j₂ - j₃)) (-(j₁ - m₁) + (j₁ + j₂ - j₃)) := by
      congr 1 <;> ring
    rw [e, symmetricRacahSum_add_intCast _ _ _ _ _ _ _ (a₁ : ℤ) (by push_cast; linarith),
      ← symmetricRacahSum_swap_x23, ← symmetricRacahSum_swap_y23, ← symmetricRacahSum_neg,
      signPow_of_eq (x := j₁ - j₂ - (-m₁ - m₂)) (n := (q₁ : ℤ) - p₂) (by push_cast; linarith),
      signPow_of_eq (x := j₂ - j₁ - (-m₁ - m₂)) (n := (q₂ : ℤ) - p₁) (by push_cast; linarith),
      signPow_of_eq (x := j₁ + j₂ + j₃) (n := (a₁ : ℤ) + p₃ + q₃) (by push_cast; linarith)]
    have hs : (-1 : ℝ) ^ ((a₁ : ℤ) + p₃ + q₃) * ((-1) ^ ((q₂ : ℤ) - p₁) * (-1) ^ (a₁ : ℤ)) =
        (-1) ^ ((q₁ : ℤ) - p₂) := by
      rw [← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num)]
      exact neg_one_zpow_eq_of_eq_add_two_mul ((p₂ : ℤ) + q₂) (by omega)
    rw [← hs]
    ring_nf
  · rw [wigner3j_of_not h, wigner3j_of_not (mt hiff.mpr h), mul_zero]

/-- DLMF 34.3.10: reversing the signs of the projections gives the phase `(-1)^{j₁+j₂+j₃}`. -/
@[dlmf 34.3.E10]
theorem wigner3j_neg (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ) :
    wigner3j j₁ j₂ j₃ m₁ m₂ m₃ = signPow (j₁ + j₂ + j₃) * wigner3j j₁ j₂ j₃ (-m₁) (-m₂) (-m₃) := by
  by_cases hm : m₁ + m₂ + m₃ = 0
  swap
  · rw [wigner3j_eq_zero_of_add_add_ne_zero hm,
        wigner3j_eq_zero_of_add_add_ne_zero (fun h => hm (by linarith)), mul_zero]
  obtain rfl : m₃ = -m₁ - m₂ := by linarith
  have hiff : IsAdmissible3j j₁ j₂ j₃ m₁ m₂ (-m₁ - m₂) ↔
      IsAdmissible3j j₁ j₂ j₃ (-m₁) (-m₂) (-(-m₁ - m₂)) := by
    unfold IsAdmissible3j IsTriad IsProjection
    constructor <;> rintro ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, ⟨h6, h7⟩, ⟨h8, h9⟩, -⟩ <;>
      exact ⟨⟨by wigner_pick9, by wigner_pick9, by wigner_pick9⟩,
          ⟨by wigner_pick9, by wigner_pick9⟩,
        ⟨by wigner_pick9, by wigner_pick9⟩, ⟨by wigner_pick9, by wigner_pick9⟩, by ring⟩
  by_cases h : IsAdmissible3j j₁ j₂ j₃ m₁ m₂ (-m₁ - m₂)
  · have h' := hiff.mp h
    rw [wigner3j_eq_sqrt_mul_symmetricRacahSum h, wigner3j_eq_sqrt_mul_symmetricRacahSum h']
    obtain ⟨⟨⟨a₁, ha₁⟩, -, -⟩, ⟨⟨p₁, hp₁⟩, ⟨q₁, hq₁⟩⟩, ⟨⟨p₂, hp₂⟩, ⟨q₂, hq₂⟩⟩,
      ⟨⟨p₃, hp₃⟩, ⟨q₃, hq₃⟩⟩, -⟩ := h
    have ha : 2 * a₁ + p₃ + q₃ = p₁ + q₁ + p₂ + q₂ := by
      exact_mod_cast (by linarith : 2 * (a₁ : ℚ) + p₃ + q₃ = p₁ + q₁ + p₂ + q₂)
    have e : symmetricRacahSum (j₁ + j₂ - j₃) (j₁ - -m₁) (j₂ + -m₂) 0 (j₂ - j₃ - -m₁)
        (j₁ - j₃ + -m₂) =
        symmetricRacahSum (-0 + (j₁ + j₂ - j₃)) (-(j₂ - j₃ - m₁) + (j₁ + j₂ - j₃))
          (-(j₁ - j₃ + m₂) + (j₁ + j₂ - j₃)) (-(j₁ + j₂ - j₃) + (j₁ + j₂ - j₃))
          (-(j₁ - m₁) + (j₁ + j₂ - j₃)) (-(j₂ + m₂) + (j₁ + j₂ - j₃)) := by
      congr 1 <;> ring
    rw [e, symmetricRacahSum_add_intCast _ _ _ _ _ _ _ (a₁ : ℤ) (by push_cast; linarith),
        ← symmetricRacahSum_neg,
      signPow_of_eq (x := j₁ - j₂ - (-m₁ - m₂)) (n := (q₁ : ℤ) - p₂) (by push_cast; linarith),
      signPow_of_eq (x := j₁ - j₂ - -(-m₁ - m₂)) (n := (p₁ : ℤ) - q₂) (by push_cast; linarith),
      signPow_of_eq (x := j₁ + j₂ + j₃) (n := (a₁ : ℤ) + p₃ + q₃) (by push_cast; linarith)]
    have hs : (-1 : ℝ) ^ ((a₁ : ℤ) + p₃ + q₃) * ((-1) ^ ((p₁ : ℤ) - q₂) * (-1) ^ (a₁ : ℤ)) =
        (-1) ^ ((q₁ : ℤ) - p₂) := by
      rw [← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num)]
      exact neg_one_zpow_eq_of_eq_add_two_mul ((p₁ : ℤ) + p₂) (by omega)
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
  · rw [wigner3j_eq_zero_of_add_add_ne_zero hm,
        wigner3j_eq_zero_of_add_add_ne_zero (fun h => hm (by linarith))]
  obtain rfl : m₃ = -m₁ - m₂ := by linarith
  have hiff : IsAdmissible3j j₁ j₂ j₃ m₁ m₂ (-m₁ - m₂) ↔
      IsAdmissible3j j₁ ((j₂ + j₃ + m₁) / 2) ((j₂ + j₃ - m₁) / 2) (j₂ - j₃)
        ((j₃ - j₂ + m₁) / 2 + m₂) ((j₃ - j₂ + m₁) / 2 + (-m₁ - m₂)) := by
    unfold IsAdmissible3j IsTriad IsProjection
    constructor <;> rintro ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, ⟨h6, h7⟩, ⟨h8, h9⟩, -⟩ <;>
      exact ⟨⟨by wigner_pick9, by wigner_pick9, by wigner_pick9⟩,
          ⟨by wigner_pick9, by wigner_pick9⟩,
        ⟨by wigner_pick9, by wigner_pick9⟩, ⟨by wigner_pick9, by wigner_pick9⟩, by ring⟩
  by_cases h : IsAdmissible3j j₁ j₂ j₃ m₁ m₂ (-m₁ - m₂)
  · have h' := hiff.mp h
    rw [wigner3j_eq_sqrt_mul_symmetricRacahSum h, wigner3j_eq_sqrt_mul_symmetricRacahSum h']
    obtain ⟨-, ⟨⟨p₁, hp₁⟩, ⟨q₁, hq₁⟩⟩, ⟨⟨p₂, hp₂⟩, ⟨q₂, hq₂⟩⟩, ⟨⟨p₃, hp₃⟩, ⟨q₃, hq₃⟩⟩, -⟩ := h
    have hpq : q₁ + q₂ + q₃ = p₁ + p₂ + p₃ := by
      exact_mod_cast (by linarith : (q₁ : ℚ) + q₂ + q₃ = p₁ + p₂ + p₃)
    have e : symmetricRacahSum (j₁ + (j₂ + j₃ + m₁) / 2 - (j₂ + j₃ - m₁) / 2) (j₁ - (j₂ - j₃))
        ((j₂ + j₃ + m₁) / 2 + ((j₃ - j₂ + m₁) / 2 + m₂)) 0
        ((j₂ + j₃ + m₁) / 2 - (j₂ + j₃ - m₁) / 2 - (j₂ - j₃))
        (j₁ - (j₂ + j₃ - m₁) / 2 + ((j₃ - j₂ + m₁) / 2 + m₂)) =
        symmetricRacahSum ((j₁ + j₂ - j₃) + (j₃ - j₂ + m₁)) ((j₁ - m₁) + (j₃ - j₂ + m₁))
          ((j₂ + m₂) + (j₃ - j₂ + m₁)) ((j₂ - j₃ - m₁) + (j₃ - j₂ + m₁))
          (0 + (j₃ - j₂ + m₁)) ((j₁ - j₃ + m₂) + (j₃ - j₂ + m₁)) := by
      congr 1 <;> ring
    rw [e, symmetricRacahSum_add_intCast _ _ _ _ _ _ _ ((p₃ : ℤ) - q₂) (by push_cast; linarith),
        ← symmetricRacahSum_swap_y12,
      signPow_of_eq (x := j₁ - j₂ - (-m₁ - m₂)) (n := (q₁ : ℤ) - p₂) (by push_cast; linarith),
      signPow_of_eq (x := j₁ - (j₂ + j₃ + m₁) / 2 - ((j₃ - j₂ + m₁) / 2 + (-m₁ - m₂)))
        (n := (p₁ : ℤ) - q₃) (by push_cast; linarith)]
    have hs : (-1 : ℝ) ^ ((p₁ : ℤ) - q₃) * (-1) ^ ((p₃ : ℤ) - q₂) = (-1) ^ ((q₁ : ℤ) - p₂) := by
      rw [← zpow_add₀ (by norm_num)]
      exact neg_one_zpow_eq_of_eq_add_two_mul 0 (by omega)
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
  · rw [wigner3j_eq_zero_of_add_add_ne_zero hm,
        wigner3j_eq_zero_of_add_add_ne_zero (fun h => hm (by linarith))]
  obtain rfl : m₃ = -m₁ - m₂ := by linarith
  have hiff : IsAdmissible3j j₁ j₂ j₃ m₁ m₂ (-m₁ - m₂) ↔
      IsAdmissible3j ((j₁ + j₂ - (-m₁ - m₂)) / 2) ((j₂ + j₃ - m₁) / 2) ((j₁ + j₃ - m₂) / 2)
        (j₃ - (j₁ + j₂ + (-m₁ - m₂)) / 2) (j₁ - (j₂ + j₃ + m₁) / 2)
        (j₂ - (j₁ + j₃ + m₂) / 2) := by
    unfold IsAdmissible3j IsTriad IsProjection
    constructor <;> rintro ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, ⟨h6, h7⟩, ⟨h8, h9⟩, -⟩ <;>
      exact ⟨⟨by wigner_pick9, by wigner_pick9, by wigner_pick9⟩,
          ⟨by wigner_pick9, by wigner_pick9⟩,
        ⟨by wigner_pick9, by wigner_pick9⟩, ⟨by wigner_pick9, by wigner_pick9⟩, by ring⟩
  by_cases h : IsAdmissible3j j₁ j₂ j₃ m₁ m₂ (-m₁ - m₂)
  · have h' := hiff.mp h
    rw [wigner3j_eq_sqrt_mul_symmetricRacahSum h, wigner3j_eq_sqrt_mul_symmetricRacahSum h',
        symmetricRacahSum_cycle_x, symmetricRacahSum_cycle_x]
    ring_nf
  · rw [wigner3j_of_not h, wigner3j_of_not (mt hiff.mpr h)]

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
