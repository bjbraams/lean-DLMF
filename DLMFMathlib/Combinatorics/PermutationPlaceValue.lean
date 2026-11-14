/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.Lex
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Fin.VecNotation

/-!
# Lexicographic permutation values and their palindromic differences

Rao–Lakshminarayanan, *Generalized Hypergeometric Functions* (2018), §2.2,
(2.30)–(2.58), synopsis RL-2.03–RL-2.04. The palindrome theorem does not
require the numerical values to be increasing in a base smaller than `n`.
-/

@[expose] public noncomputable section
namespace List

/-- All permutations of `0,…,n-1` in lexicographic order,
Rao–Lakshminarayanan (2.30)–(2.43), synopsis RL-2.03. -/
def lexicographicPermutations (n : ℕ) : List (List (Fin n)) :=
  ((List.finRange n).permutations).mergeSort

/-- The lexicographically sorted list of permutations, RL-2.03. -/
theorem lexicographicPermutations_def (n : ℕ) : lexicographicPermutations n =
    ((List.finRange n).permutations).mergeSort := rfl

/-- The list has `n!` elements, including the single empty permutation at `n=0`,
Rao–Lakshminarayanan (2.30)–(2.43), synopsis RL-2.03. -/
theorem length_lexicographicPermutations (n : ℕ) :
    (lexicographicPermutations n).length = n.factorial := by
  sorry

/-- Complementation reverses lexicographic order on the full permutation list,
Rao–Lakshminarayanan (2.38)–(2.58), synopsis RL-2.03/04. -/
theorem map_rev_lexicographicPermutations (n : ℕ) {k : ℕ} (hk : k < n.factorial) :
    ((lexicographicPermutations n).getD k []).map Fin.rev =
      (lexicographicPermutations n).getD (n.factorial - 1 - k) [] := by
  sorry

end List
namespace Nat

/-- Place value of the `k`th lexicographic permutation with digits `1,…,n`,
Rao–Lakshminarayanan (2.30)–(2.43), synopsis RL-2.03. `k` is zero-based. -/
def permutationPlaceValue (B n k : ℕ) : ℕ :=
  ofDigits B (((List.lexicographicPermutations n).getD k []).reverse.map (fun i => i.val + 1))

/-- The digit formula defining place values of permutations, RL-2.03. -/
theorem permutationPlaceValue_def (B n k : ℕ) : permutationPlaceValue B n k =
    ofDigits B (((List.lexicographicPermutations n).getD k []).reverse.map
      (fun i => i.val + 1)) := rfl

/-- Lexicographic and numerical place-value order agree for `B≥n`,
Rao–Lakshminarayanan (2.30)–(2.43), synopsis RL-2.03. -/
theorem permutationPlaceValue_lt {B n k l : ℕ} (hB : 2 ≤ B) (hn : n ≤ B)
    (hkl : k < l) (hl : l < n.factorial) :
    permutationPlaceValue B n k < permutationPlaceValue B n l := by
  sorry

/-- Consecutive place-value differences form a palindrome, without a monotonicity
assumption on place values, Rao–Lakshminarayanan labelled Theorem, p. 2-11,
(2.38)–(2.58), synopsis RL-2.04. Signed differences retain the small-base cases. -/
theorem permutationPlaceValue_sub_palindrome (B n : ℕ) {k : ℕ}
    (hk : k + 1 < n.factorial) :
    (permutationPlaceValue B n (k + 1) : ℤ) - permutationPlaceValue B n k =
      (permutationPlaceValue B n (n.factorial - 1 - k) : ℤ) -
        permutationPlaceValue B n (n.factorial - 2 - k) := by
  sorry

end Nat
