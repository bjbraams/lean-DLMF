/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Basic
public import DLMF.GeneralizedHypergeometric.UnitArgument
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Finite permutation invariants of hypergeometric transformations

Rao–Lakshminarayanan, *Generalized Hypergeometric Functions* (2018), Chapters
3, 4 and 6. Polynomial scaling records the identities at singular parameters
without assigning arbitrary values to quotients of Gamma poles.
-/

@[expose] public noncomputable section
open Complex Finset
open scoped Nat
namespace DLMF.Hypergeometric

namespace TerminatingTransformations

/-- The denominator-cleared terminating `₃F₂`, Rao–Lakshminarayanan
(4.18)–(4.35), synopsis RL-4.03. Coordinates are `(a,b,t,d,e)`;
`t=1-N` is used in the transformation theorem. -/
def scaledThreeF2 (N : ℕ) (v : Fin 5 → ℂ) : ℂ :=
  ∑ k ∈ range (N + 1), pochhammer (-(N : ℂ)) k *
    pochhammer (v 0) k * pochhammer (v 1) k / k.factorial *
    pochhammer (v 3 + k) (N - k) * pochhammer (v 4 + k) (N - k)

/-- The Weber–Erdélyi parameter involution, Rao–Lakshminarayanan (4.57), RL-4.03. -/
def weberMap (v : Fin 5 → ℂ) : Fin 5 → ℂ :=
  ![v 0, v 4 - v 1, v 2, v 0 + v 2 - v 3, v 4]

/-- The defining finite polynomial for RL-4.03. -/
theorem scaledThreeF2_def (N : ℕ) (v : Fin 5 → ℂ) :
    scaledThreeF2 N v =
      ∑ k ∈ range (N + 1), pochhammer (-(N : ℂ)) k *
        pochhammer (v 0) k * pochhammer (v 1) k / k.factorial *
        pochhammer (v 3 + k) (N - k) * pochhammer (v 4 + k) (N - k) := rfl

/-- The defining parameter map for RL-4.03. -/
theorem weberMap_def (v : Fin 5 → ℂ) :
    weberMap v = ![v 0, v 4 - v 1, v 2, v 0 + v 2 - v 3, v 4] := rfl

/-- The first parameter generator is an involution, Rao–Lakshminarayanan
(4.57)–(4.69), synopsis RL-4.07. -/
theorem weberMap_involutive : Function.Involutive weberMap := by
  intro v
  funext i
  fin_cases i <;> norm_num [weberMap] <;> ring

/-- Polynomial Weber–Erdélyi transformation, Rao–Lakshminarayanan
(4.18)–(4.35), synopsis RL-4.03. -/
theorem scaledThreeF2_weber (N : ℕ) (v : Fin 5 → ℂ) (ht : v 2 = 1 - N) :
    scaledThreeF2 N v = (-1 : ℂ) ^ N * scaledThreeF2 N (weberMap v) := by
  sorry

/-- The polynomial scaling agrees with ordinary finite evaluation on its
regular locus, Rao–Lakshminarayanan (4.93), synopsis RL-4.10. -/
theorem scaledThreeF2_eq (N : ℕ) (v : Fin 5 → ℂ)
    (hreg : ∀ k ≤ N, pochhammer (v 3) k * pochhammer (v 4) k ≠ 0) :
    scaledThreeF2 N v = pochhammer (v 3) N * pochhammer (v 4) N *
      generalizedHypergeometricTruncated N {v 0, v 1, -(N : ℂ)} {v 3, v 4} 1 := by
  sorry

/-- Reversal of an arbitrary terminating `ₚ₊₁Fₚ(1)`, Rao–Lakshminarayanan
(4.28), (6.57)–(6.60), synopses RL-4.04 and RL-6.06. -/
theorem finite_reversal (N : ℕ) (A B : Multiset ℂ) (hcard : A.card = B.card)
    (hreg : ∀ k ≤ N, pochhammerProduct B k ≠ 0)
    (hreg' : ∀ k ≤ N, pochhammerProduct (A.map (fun a => 1 - a - N)) k ≠ 0) :
    generalizedHypergeometricTruncated N (-(N : ℂ) ::ₘ A) B 1 =
      (-1 : ℂ) ^ N * pochhammerProduct A N / pochhammerProduct B N *
        generalizedHypergeometricTruncated N
          (-(N : ℂ) ::ₘ B.map (fun b => 1 - b - N))
          (A.map (fun a => 1 - a - N)) 1 := by
  sorry

/-- The balanced denominator-cleared polynomial, Rao–Lakshminarayanan
(6.76)–(6.99), synopsis RL-6.10. -/
def balancedPolynomial (N : ℕ) (x : Fin 6 → ℂ) : ℂ :=
  ∑ k ∈ range (N + 1), pochhammer (-(N : ℂ)) k / k.factorial *
    pochhammer (x 0 + x 1) k * pochhammer (x 1 + x 2) k *
    pochhammer (x 0 + x 2) k *
    ∏ i : Fin 3, pochhammer (x 0 + x 1 + x 2 + x ⟨i.val + 3, by omega⟩ + k) (N - k)

/-- The finite formula defining the balanced polynomial of RL-6.10. -/
theorem balancedPolynomial_def (N : ℕ) (x : Fin 6 → ℂ) :
    balancedPolynomial N x =
      ∑ k ∈ range (N + 1), pochhammer (-(N : ℂ)) k / k.factorial *
        pochhammer (x 0 + x 1) k * pochhammer (x 1 + x 2) k *
        pochhammer (x 0 + x 2) k *
        ∏ i : Fin 3, pochhammer (x 0 + x 1 + x 2 + x ⟨i.val + 3, by omega⟩ + k) (N - k) := rfl

/-- Full `S₆` invariance including singular finite parameters,
Rao–Lakshminarayanan (6.76)–(6.99), synopsis RL-6.10. -/
theorem balancedPolynomial_perm (N : ℕ) (x : Fin 6 → ℂ)
    (hx : ∑ i, x i = 1 - N) (π : Equiv.Perm (Fin 6)) :
    balancedPolynomial N x = balancedPolynomial N (x ∘ π) := by
  sorry

end TerminatingTransformations

namespace ThomaeCoordinates

/-- The affine five-coordinate Gauss parameters of the `S₅` invariant,
Rao–Lakshminarayanan (4.107)–(4.122), synopsis RL-4.12. -/
def parameters (x : Fin 5 → ℂ) : Fin 5 → ℂ :=
  ![1 / 2 + x 0 + x 3 + x 4, 1 / 2 + x 1 + x 3 + x 4,
    1 / 2 + x 2 + x 3 + x 4, 1 + (∑ i, x i) + x 3, 1 + (∑ i, x i) + x 4]

/-- The defining five-coordinate map of RL-4.12. -/
theorem parameters_def (x : Fin 5 → ℂ) : parameters x =
    ![1 / 2 + x 0 + x 3 + x 4, 1 / 2 + x 1 + x 3 + x 4,
      1 / 2 + x 2 + x 3 + x 4, 1 + (∑ i, x i) + x 3, 1 + (∑ i, x i) + x 4] := rfl

/-- Full `S₅` invariance of the Gamma-normalized `₃F₂(1)`,
Rao–Lakshminarayanan (4.107)–(4.122), synopsis RL-4.12. Both ordinary
series converge on the stated common excess domain. -/
theorem normalized_threeF2_perm (x : Fin 5 → ℂ) (π : Equiv.Perm (Fin 5))
    (hreg : LowerParametersRegular {(parameters x) 3, (parameters x) 4})
    (hreg' : LowerParametersRegular {(parameters (x ∘ π)) 3, (parameters (x ∘ π)) 4})
    (hex : 0 < ((parameters x) 3 + (parameters x) 4 -
      (parameters x) 0 - (parameters x) 1 - (parameters x) 2).re)
    (hex' : 0 < ((parameters (x ∘ π)) 3 + (parameters (x ∘ π)) 4 -
      (parameters (x ∘ π)) 0 - (parameters (x ∘ π)) 1 - (parameters (x ∘ π)) 2).re) :
    generalizedHypergeometric {(parameters x) 0, (parameters x) 1, (parameters x) 2}
      {(parameters x) 3, (parameters x) 4} 1 /
      (Gamma ((parameters x) 3) * Gamma ((parameters x) 4) *
        Gamma ((parameters x) 3 + (parameters x) 4 -
          (parameters x) 0 - (parameters x) 1 - (parameters x) 2)) =
    generalizedHypergeometric {(parameters (x ∘ π)) 0, (parameters (x ∘ π)) 1,
        (parameters (x ∘ π)) 2} {(parameters (x ∘ π)) 3, (parameters (x ∘ π)) 4} 1 /
      (Gamma ((parameters (x ∘ π)) 3) * Gamma ((parameters (x ∘ π)) 4) *
        Gamma ((parameters (x ∘ π)) 3 + (parameters (x ∘ π)) 4 -
          (parameters (x ∘ π)) 0 - (parameters (x ∘ π)) 1 - (parameters (x ∘ π)) 2)) := by
  sorry

end ThomaeCoordinates
end DLMF.Hypergeometric
