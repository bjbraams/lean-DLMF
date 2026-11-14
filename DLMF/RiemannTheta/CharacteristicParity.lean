/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.RiemannTheta.Products
import Mathlib.Tactic

/-!
# Even and odd half-characteristics

For binary vectors `a,b`, the sign of the half-characteristic `[a/2;b/2]` is
`(-1)^(a·b)`. The signed sum over all characteristics is `2^g`; the even and odd
counts are `(4^g + 2^g)/2` and `(4^g - 2^g)/2`, respectively. The formulas include
genus zero. Odd theta constants vanish for every matrix, including totalized series.

References: Mumford, *Tata Lectures on Theta I*, Chapter II, §3, pp. 168–170;
Igusa, *Theta Functions*, Chapter V, §6, pp. 209–211;
Mumford, *Tata Lectures on Theta II*, Chapter IIIa, §6.
-/

public noncomputable section

open Complex Matrix Finset

namespace DLMF.RiemannTheta

variable {ι : Type*} [Fintype ι]

attribute [local instance] Classical.propDecidable

/-- The sign of the binary half-characteristic, in a form that factors by coordinate. -/
@[expose] def characteristicSign (a b : ι → Fin 2) : ℤ :=
  ∏ i, (-1 : ℤ) ^ ((a i : ℕ) * (b i : ℕ))

/-- The characteristic sign is the parity of the binary dot product. -/
theorem characteristicSign_eq_pow (a b : ι → Fin 2) :
    characteristicSign a b = (-1 : ℤ) ^ (∑ i, (a i : ℕ) * (b i : ℕ)) := by
  exact Finset.prod_pow_eq_pow_sum _ _ _

/-- Every half-characteristic has sign one or minus one. -/
theorem characteristicSign_eq_one_or_neg_one (a b : ι → Fin 2) :
    characteristicSign a b = 1 ∨ characteristicSign a b = -1 := by
  rw [characteristicSign_eq_pow]
  exact neg_one_pow_eq_or ℤ _

/-- The set of even binary half-characteristics. -/
@[expose] def evenHalfCharacteristics (ι : Type*) [Fintype ι] :
    Finset ((ι → Fin 2) × (ι → Fin 2)) := by
  classical
  exact univ.filter fun c => characteristicSign c.1 c.2 = 1

/-- The set of odd binary half-characteristics. -/
@[expose] def oddHalfCharacteristics (ι : Type*) [Fintype ι] :
    Finset ((ι → Fin 2) × (ι → Fin 2)) := by
  classical
  exact univ.filter fun c => characteristicSign c.1 c.2 = -1

/-- Membership in the even set is the positive sign condition. -/
@[simp] theorem mem_evenHalfCharacteristics (c : (ι → Fin 2) × (ι → Fin 2)) :
    c ∈ evenHalfCharacteristics ι ↔ characteristicSign c.1 c.2 = 1 := by
  classical
  simp [evenHalfCharacteristics]

/-- Membership in the odd set is the negative sign condition. -/
@[simp] theorem mem_oddHalfCharacteristics (c : (ι → Fin 2) × (ι → Fin 2)) :
    c ∈ oddHalfCharacteristics ι ↔ characteristicSign c.1 c.2 = -1 := by
  classical
  simp [oddHalfCharacteristics]

/-- The sum of the signs of the `4^g` half-characteristics is `2^g`. -/
theorem sum_characteristicSign :
    (∑ c : (ι → Fin 2) × (ι → Fin 2), characteristicSign c.1 c.2) =
      (2 : ℤ) ^ Fintype.card ι := by
  classical
  calc
    (∑ c : (ι → Fin 2) × (ι → Fin 2), characteristicSign c.1 c.2) =
        ∑ a : ι → Fin 2, ∑ b : ι → Fin 2,
          ∏ i, (-1 : ℤ) ^ ((a i : ℕ) * (b i : ℕ)) := by
      rw [Fintype.sum_prod_type]
      rfl
    _ = ∑ a : ι → Fin 2, ∏ i : ι, ∑ b : Fin 2, (-1 : ℤ) ^ ((a i).val * b.val) := by
      apply Finset.sum_congr rfl
      intro a _ha
      exact (Fintype.prod_sum (fun (i : ι) (b : Fin 2) =>
        (-1 : ℤ) ^ ((a i).val * b.val))).symm
    _ = ∏ i : ι, ∑ a : Fin 2, ∑ b : Fin 2, (-1 : ℤ) ^ (a.val * b.val) :=
      (Fintype.prod_sum (fun (_ : ι) (a : Fin 2) => ∑ b : Fin 2,
        (-1 : ℤ) ^ (a.val * b.val))).symm
    _ = _ := by norm_num [Fin.sum_univ_two]

/-- Even and odd half-characteristics partition all binary characteristics. -/
theorem card_evenHalfCharacteristics_add_card_oddHalfCharacteristics :
    (evenHalfCharacteristics ι).card + (oddHalfCharacteristics ι).card =
      4 ^ Fintype.card ι := by
  classical
  have hd : Disjoint (evenHalfCharacteristics ι) (oddHalfCharacteristics ι) := by
    rw [Finset.disjoint_left]
    intro c hc he
    have h₁ := mem_evenHalfCharacteristics c |>.mp hc
    have h₂ := mem_oddHalfCharacteristics c |>.mp he
    omega
  have hu : evenHalfCharacteristics ι ∪ oddHalfCharacteristics ι = univ := by
    ext c
    simp only [mem_union, mem_evenHalfCharacteristics, mem_oddHalfCharacteristics,
      mem_univ, iff_true]
    exact characteristicSign_eq_one_or_neg_one c.1 c.2
  rw [← Finset.card_union_of_disjoint hd, hu, Finset.card_univ]
  norm_num [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ← mul_pow]

/-- The difference between the even and odd counts is `2^g`. -/
theorem card_evenHalfCharacteristics_sub_card_oddHalfCharacteristics :
    ((evenHalfCharacteristics ι).card : ℤ) - (oddHalfCharacteristics ι).card =
      (2 : ℤ) ^ Fintype.card ι := by
  classical
  rw [← sum_characteristicSign (ι := ι)]
  symm
  calc
    (∑ c : (ι → Fin 2) × (ι → Fin 2), characteristicSign c.1 c.2) =
        ∑ c : (ι → Fin 2) × (ι → Fin 2),
          ((if characteristicSign c.1 c.2 = 1 then 1 else 0) -
            (if characteristicSign c.1 c.2 = -1 then 1 else 0) : ℤ) := by
      apply Finset.sum_congr rfl
      intro c _hc
      rcases characteristicSign_eq_one_or_neg_one c.1 c.2 with h | h <;> simp [h]
    _ = _ := by
      simp only [Finset.sum_sub_distrib, ← Finset.sum_filter, Finset.sum_const,
        nsmul_eq_mul, mul_one, evenHalfCharacteristics, oddHalfCharacteristics]

/-- There are `(4^g + 2^g)/2` even half-characteristics, including one in genus zero. -/
theorem card_evenHalfCharacteristics :
    (evenHalfCharacteristics ι).card = (4 ^ Fintype.card ι + 2 ^ Fintype.card ι) / 2 := by
  have ht := card_evenHalfCharacteristics_add_card_oddHalfCharacteristics (ι := ι)
  have hd := card_evenHalfCharacteristics_sub_card_oddHalfCharacteristics (ι := ι)
  have hp : ((2 ^ Fintype.card ι : ℕ) : ℤ) = (2 : ℤ) ^ Fintype.card ι := by norm_cast
  rw [← hp] at hd
  have hd' : (evenHalfCharacteristics ι).card =
      (oddHalfCharacteristics ι).card + 2 ^ Fintype.card ι := by omega
  omega

/-- There are `(4^g - 2^g)/2` odd half-characteristics, including none in genus zero. -/
theorem card_oddHalfCharacteristics :
    (oddHalfCharacteristics ι).card = (4 ^ Fintype.card ι - 2 ^ Fintype.card ι) / 2 := by
  have ht := card_evenHalfCharacteristics_add_card_oddHalfCharacteristics (ι := ι)
  have hd := card_evenHalfCharacteristics_sub_card_oddHalfCharacteristics (ι := ι)
  have hp : ((2 ^ Fintype.card ι : ℕ) : ℤ) = (2 : ℤ) ^ Fintype.card ι := by norm_cast
  rw [← hp] at hd
  have hd' : (evenHalfCharacteristics ι).card =
      (oddHalfCharacteristics ι).card + 2 ^ Fintype.card ι := by omega
  omega

/-- The sign counts the parity of the actual theta function with that half-characteristic. -/
theorem riemannThetaChar_neg_binary (a b : ι → Fin 2) (z : ι → ℂ) (Ω : Matrix ι ι ℂ) :
    riemannThetaChar (halfBinaryVector a) (halfBinaryVector b) (-z) Ω =
      (characteristicSign a b : ℂ) *
        riemannThetaChar (halfBinaryVector a) (halfBinaryVector b) z Ω := by
  have hc : ((fun i => (a i : ℤ)) ⬝ᵥ fun i => (b i : ℤ)) =
      ((∑ i, (a i : ℕ) * (b i : ℕ) : ℕ) : ℤ) := by simp [dotProduct]
  have h := riemannThetaChar_neg_half (fun i => (a i : ℤ)) (fun i => (b i : ℤ)) z Ω
  simpa only [hc, zpow_natCast, characteristicSign_eq_pow, Int.cast_pow,
    Int.cast_neg, Int.cast_one, halfBinaryVector, Int.cast_natCast] using h

/-- Every odd theta constant is zero. No convergence or nonsingularity is needed. -/
theorem riemannThetaChar_zero_of_odd (a b : ι → Fin 2) (Ω : Matrix ι ι ℂ)
    (hab : characteristicSign a b = -1) :
    riemannThetaChar (halfBinaryVector a) (halfBinaryVector b) 0 Ω = 0 := by
  have h := riemannThetaChar_neg_binary a b 0 Ω
  simp only [neg_zero, hab, Int.cast_neg, Int.cast_one, neg_one_mul] at h
  exact CharZero.eq_neg_self_iff.mp h

end DLMF.RiemannTheta
