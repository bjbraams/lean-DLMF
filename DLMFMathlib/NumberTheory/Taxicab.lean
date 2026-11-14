/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Tactic.NormNum

/-!
# The first taxicab number

The exact arithmetic claim in Rao–Lakshminarayanan, *Generalized Hypergeometric
Functions* (2018), §9.6, p. 9-14, synopsis RL-9.10. Representations are positive
and unordered pairs are encoded in increasing order.
-/

@[expose] public section
namespace Nat

/-- Two distinct unordered positive cube representations,
Rao–Lakshminarayanan §9.6, synopsis RL-9.10. -/
def HasTwoCubeRepresentations (n : ℕ) : Prop :=
  ∃ a b c d : ℕ, 0 < a ∧ a ≤ b ∧ 0 < c ∧ c ≤ d ∧
    (a, b) ≠ (c, d) ∧ a ^ 3 + b ^ 3 = n ∧ c ^ 3 + d ^ 3 = n

/-- The explicit positive-pair condition defining the taxicab predicate, RL-9.10. -/
theorem hasTwoCubeRepresentations_iff (n : ℕ) : HasTwoCubeRepresentations n ↔
    ∃ a b c d : ℕ, 0 < a ∧ a ≤ b ∧ 0 < c ∧ c ≤ d ∧
      (a, b) ≠ (c, d) ∧ a ^ 3 + b ^ 3 = n ∧ c ^ 3 + d ^ 3 = n := Iff.rfl

/-- The two famous cube representations, Rao–Lakshminarayanan §9.6, RL-9.10. -/
theorem hasTwoCubeRepresentations_1729 : HasTwoCubeRepresentations 1729 := by
  refine ⟨1, 12, 9, 10, ?_⟩
  norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- Below 1729 the positive ordered cube pairs among bases at most twelve are distinct. -/
private theorem cube_pair_unique_small :
    ∀ a b c d : Fin 13,
      0 < a.val → a.val ≤ b.val → 0 < c.val → c.val ≤ d.val →
      a.val ^ 3 + b.val ^ 3 < 1729 →
      a.val ^ 3 + b.val ^ 3 = c.val ^ 3 + d.val ^ 3 →
      (a.val, b.val) = (c.val, d.val) := by
  decide

/-- Minimality of 1729 among integers with two positive unordered cube
representations, Rao–Lakshminarayanan §9.6, synopsis RL-9.10. -/
theorem le_of_hasTwoCubeRepresentations {n : ℕ} (hn : HasTwoCubeRepresentations n) :
    1729 ≤ n := by
  by_contra h
  have hnlt : n < 1729 := by omega
  rcases hn with ⟨a, b, c, d, ha, hab, hc, hcd, hne, heq, heq'⟩
  have hbound : ∀ x : ℕ, x ^ 3 ≤ n → x ≤ 12 := by
    intro x hx
    by_contra hxl
    have hpow := Nat.pow_le_pow_left (by omega : 13 ≤ x) 3
    norm_num at hpow
    omega
  have ha13 : a < 13 := by have := hbound a (by omega); omega
  have hb13 : b < 13 := by have := hbound b (by omega); omega
  have hc13 : c < 13 := by have := hbound c (by omega); omega
  have hd13 : d < 13 := by have := hbound d (by omega); omega
  exact hne (cube_pair_unique_small ⟨a, ha13⟩ ⟨b, hb13⟩ ⟨c, hc13⟩ ⟨d, hd13⟩
    ha hab hc hcd (heq.symm ▸ hnlt) (heq.trans heq'.symm))

end Nat
