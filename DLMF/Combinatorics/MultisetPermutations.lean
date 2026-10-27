/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.Permutations
public import DLMF.QSeries.QBinomial
public import Mathlib.GroupTheory.Perm.DomMulAct

/-!
# Multiset permutations (DLMF §26.16)

For `a : Fin m → ℕ`, the multiset `S = {1^{a_1}, …, m^{a_m}}` has the permutations
`𝔖_S` = words `w : Fin (a_1 + ⋯ + a_m) → Fin m` taking the value `j` exactly `a_j` times
(`multisetPermutations a`; values `0`-based). Inversion number and major index are the word
statistics `wordInversions`, `wordMajorIndex` of §26.14. The `q`-multinomial coefficient
(26.16.1) is `qMultinomial q a`, built from the project's Gaussian coefficients `qBinom`; the
product is taken over all `k`, the factor `k = m` being `[a_m, a_m]_q = 1`.

## References

* NIST DLMF §26.16.
-/

@[expose] public section

noncomputable section

open Finset Equiv

namespace DLMF.Combinatorics

/-- `𝔖_S` for `S = {1^{a_1}, …, m^{a_m}}`: the words of length `a_1 + ⋯ + a_m` with exactly
`a_j` letters `j` (DLMF §26.16). -/
@[dlmf 26.16]
def multisetPermutations {m : ℕ} (a : Fin m → ℕ) : Finset (Fin (∑ i, a i) → Fin m) :=
  univ.filter fun w => ∀ j, #{i | w i = j} = a j

/-- §26.16: `|𝔖_S|` is the multinomial coefficient `(a_1 + ⋯ + a_m; a_1, …, a_m)`. -/
@[dlmf 26.16]
theorem card_multisetPermutations {m : ℕ} (a : Fin m → ℕ) :
    #(multisetPermutations a) = Nat.multinomial univ a := by
  classical
  set N := ∑ i, a i
  -- a base word
  set s : Multiset (Fin m) := (univ : Finset (Fin m)).val.bind fun j => Multiset.replicate (a j) j
  have hs : Multiset.card s = N := by
    simp only [s, Multiset.card_bind, Function.comp_def, Multiset.card_replicate]
    rfl
  have hcs : ∀ j, Multiset.count j s = a j := by
    intro j
    rw [Multiset.count_bind]
    rw [show (univ : Finset (Fin m)).val.map
        (fun b => Multiset.count j (Multiset.replicate (a b) b)) =
        (univ : Finset (Fin m)).val.map (fun b => if b = j then a j else 0) by
      refine Multiset.map_congr rfl fun b _ => ?_
      rw [Multiset.count_replicate]
      split_ifs <;> simp_all]
    rw [← Finset.sum_eq_multiset_sum, Finset.sum_ite_eq' univ j]
    simp
  obtain ⟨w0, hw0⟩ := q26b_exists_map_eq (n := N) s hs
  have hw0c : ∀ j, #{i | w0 i = j} = a j := fun j => by rw [← q26b_count_map, hw0, hcs]
  have hmem : ∀ w : Fin N → Fin m, w ∈ multisetPermutations a ↔
      univ.val.map w0 = univ.val.map w := by
    intro w
    simp only [multisetPermutations, mem_filter, mem_univ, true_and]
    rw [Multiset.ext]
    simp only [q26b_count_map, hw0c]
    exact ⟨fun h j => (h j).symm, fun h j => (h j).symm⟩
  have hstab : Fintype.card {g : Perm (Fin N) // w0 ∘ g = w0} = ∏ j, (a j).factorial := by
    rw [DomMulAct.stabilizer_card]
    refine prod_congr rfl fun j _ => ?_
    rw [Fintype.card_subtype, hw0c]
  have hfib : ∀ w ∈ multisetPermutations a,
      #{σ : Perm (Fin N) | w0 ∘ σ = w} = ∏ j, (a j).factorial := by
    intro w hw
    obtain ⟨τ, rfl⟩ := (q26b_map_eq_iff w0 w).1 ((hmem w).1 hw)
    rw [← hstab, ← Fintype.card_subtype]
    refine Fintype.card_congr ((Equiv.mulRight τ⁻¹).subtypeEquiv fun σ => ?_)
    simp only [Equiv.coe_mulRight, Perm.coe_mul]
    constructor
    · intro h; rw [← Function.comp_assoc, h]; funext i; simp
    · intro h; funext i
      have := congrFun h (τ i)
      simpa using this
  have htot : N.factorial = #(multisetPermutations a) * ∏ j, (a j).factorial := by
    rw [← Fintype.card_fin N, ← Fintype.card_perm, ← card_univ,
      Finset.card_eq_sum_card_fiberwise (f := fun σ : Perm (Fin N) => w0 ∘ σ)
        (t := multisetPermutations a) ?_]
    · rw [Finset.sum_congr rfl hfib, sum_const, smul_eq_mul]
    · intro σ _
      rw [Finset.mem_coe, hmem]
      exact (q26b_map_eq_iff w0 (w0 ∘ σ)).2 ⟨σ, rfl⟩
  have hspec := Nat.multinomial_spec univ a
  have hpos : 0 < ∏ j, (a j).factorial := Finset.prod_pos fun j _ => Nat.factorial_pos _
  have : #(multisetPermutations a) * ∏ j, (a j).factorial =
      Nat.multinomial univ a * ∏ j, (a j).factorial := by
    rw [← htot, mul_comm, hspec]
  exact Nat.eq_of_mul_eq_mul_right hpos this

/-- §26.16, the example `351322453154 ∈ 𝔖_{1²,2²,3³,4²,5³}`: `inv = 24` and `maj = 34`. -/
@[dlmf 26.16]
theorem multisetPermutation_example :
    wordInversions (![3, 5, 1, 3, 2, 2, 4, 5, 3, 1, 5, 4] : Fin 12 → ℕ) = 24 ∧
      wordMajorIndex (![3, 5, 1, 3, 2, 2, 4, 5, 3, 1, 5, 4] : Fin 12 → ℕ) = 34 := by
  decide

/-- (26.16.1): the `q`-multinomial coefficient
`[a_1+⋯+a_m; a_1, …, a_m]_q = ∏_{k=1}^{m-1} [a_k + a_{k+1} + ⋯ + a_m, a_k]_q`. -/
@[dlmf 26.16.E1]
def qMultinomial (q : ℂ) {m : ℕ} (a : Fin m → ℕ) : ℂ :=
  ∏ k : Fin m, DLMF.QSeries.qBinom q (∑ i ∈ univ.filter (k ≤ ·), a i) (a k)

/-- (26.16.2): `∑_{σ ∈ 𝔖_S} q^{inv(σ)} = [a_1+⋯+a_m; a_1, …, a_m]_q` (every `q`). -/
@[dlmf 26.16.E2]
theorem sum_pow_wordInversions_multisetPermutations (q : ℂ) {m : ℕ} (a : Fin m → ℕ) :
    ∑ w ∈ multisetPermutations a, q ^ wordInversions (fun i => (w i : ℕ)) = qMultinomial q a := by
  sorry

/-- (26.16.3): `∑_{σ ∈ 𝔖_S} q^{maj(σ)} = [a_1+⋯+a_m; a_1, …, a_m]_q` (MacMahon; every `q`). -/
@[dlmf 26.16.E3]
theorem sum_pow_wordMajorIndex_multisetPermutations (q : ℂ) {m : ℕ} (a : Fin m → ℕ) :
    ∑ w ∈ multisetPermutations a, q ^ wordMajorIndex (fun i => (w i : ℕ)) = qMultinomial q a := by
  sorry

end DLMF.Combinatorics
