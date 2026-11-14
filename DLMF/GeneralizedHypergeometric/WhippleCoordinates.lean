/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.TransformationGroups
public import DLMF.GeneralizedHypergeometric.FiniteTransformationGroups
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Whipple coordinates and the full terminating transformation action

Rao–Lakshminarayanan, *Generalized Hypergeometric Functions* (2018),
§§4.1–4.2, (4.6)–(4.95). The normalized functions use entire reciprocal
Gamma factors; statements distinguish convergence and exceptional parameters.
-/

@[expose] public noncomputable section
open Complex Finset
namespace DLMF.Hypergeometric.WhippleCoordinates

/-- The triangular Whipple coordinate, Rao–Lakshminarayanan (4.6), RL-4.05. -/
def alpha (r : Fin 6 → ℂ) (i j k : Fin 6) : ℂ := 1 / 2 + r i + r j + r k

/-- The pair Whipple coordinate, Rao–Lakshminarayanan (4.7), RL-4.05. -/
def beta (r : Fin 6 → ℂ) (i j : Fin 6) : ℂ := 1 + r i - r j

/-- The three upper parameters for a chosen arrangement `(l,i,j,k,m,n)`,
Rao–Lakshminarayanan (4.8)–(4.10), RL-4.05. -/
def upper (r : Fin 6 → ℂ) (p : Equiv.Perm (Fin 6)) : Multiset ℂ :=
  {alpha r (p 1) (p 4) (p 5), alpha r (p 2) (p 4) (p 5), alpha r (p 3) (p 4) (p 5)}

/-- The two lower parameters in the same arrangement, RL-4.05. -/
def lower (r : Fin 6 → ℂ) (p : Equiv.Perm (Fin 6)) : Multiset ℂ :=
  {beta r (p 4) (p 0), beta r (p 5) (p 0)}

/-- Whipple's normalized positive function for a chosen arrangement,
Rao–Lakshminarayanan (4.8), RL-4.05. -/
def positive (r : Fin 6 → ℂ) (p : Equiv.Perm (Fin 6)) : ℂ :=
  generalizedHypergeometric (upper r p) (lower r p) 1 /
    (Gamma (alpha r (p 1) (p 2) (p 3)) *
      Gamma (beta r (p 4) (p 0)) * Gamma (beta r (p 5) (p 0)))

/-- The negative Whipple function reverses the signs of the six coordinates,
Rao–Lakshminarayanan (4.9), RL-4.05. -/
def negative (r : Fin 6 → ℂ) (p : Equiv.Perm (Fin 6)) : ℂ := positive (-r) p

/-- The explicit triangular coordinate, RL-4.05. -/
theorem alpha_def (r : Fin 6 → ℂ) (i j k : Fin 6) :
    alpha r i j k = 1 / 2 + r i + r j + r k := rfl

/-- The explicit pair coordinate, RL-4.05. -/
theorem beta_def (r : Fin 6 → ℂ) (i j : Fin 6) : beta r i j = 1 + r i - r j := rfl

/-- The explicit upper parameter multiset, RL-4.05. -/
theorem upper_def (r : Fin 6 → ℂ) (p : Equiv.Perm (Fin 6)) : upper r p =
    {alpha r (p 1) (p 4) (p 5), alpha r (p 2) (p 4) (p 5), alpha r (p 3) (p 4) (p 5)} := rfl

/-- The explicit lower parameter multiset, RL-4.05. -/
theorem lower_def (r : Fin 6 → ℂ) (p : Equiv.Perm (Fin 6)) :
    lower r p = {beta r (p 4) (p 0), beta r (p 5) (p 0)} := rfl

/-- The Gamma normalization of the positive function, RL-4.05. -/
theorem positive_def (r : Fin 6 → ℂ) (p : Equiv.Perm (Fin 6)) :
    positive r p = generalizedHypergeometric (upper r p) (lower r p) 1 /
      (Gamma (alpha r (p 1) (p 2) (p 3)) *
        Gamma (beta r (p 4) (p 0)) * Gamma (beta r (p 5) (p 0))) := rfl

/-- The negative function is the coordinate sign reversal, RL-4.05. -/
theorem negative_def (r : Fin 6 → ℂ) (p : Equiv.Perm (Fin 6)) :
    negative r p = positive (-r) p := rfl

/-- The excess in a positive Whipple arrangement, Rao–Lakshminarayanan RL-4.05. -/
theorem parameterExcess_upper_lower (r : Fin 6 → ℂ) (hr : ∑ i, r i = 0)
    (p : Equiv.Perm (Fin 6)) :
    parameterExcess (upper r p) (lower r p) = alpha r (p 1) (p 2) (p 3) := by
  sorry

/-- For a fixed excluded index, the ten choices of the lower pair give the same
normalized Whipple function on their common convergence domain,
Rao–Lakshminarayanan (4.8)–(4.10), synopsis RL-4.05. -/
theorem positive_eq_of_same_first (r : Fin 6 → ℂ) (hr : ∑ i, r i = 0)
    (p q : Equiv.Perm (Fin 6)) (hpq : p 0 = q 0)
    (hp : LowerParametersRegular (lower r p)) (hq : LowerParametersRegular (lower r q))
    (hep : 0 < (alpha r (p 1) (p 2) (p 3)).re)
    (heq : 0 < (alpha r (q 1) (q 2) (q 3)).re) : positive r p = positive r q := by
  sorry

/-- Six fixed arrangements choosing the terminating upper parameter in the two blocks,
Rao–Lakshminarayanan (4.36)–(4.56), synopsis RL-4.06. -/
def arrangement : Fin 6 → Equiv.Perm (Fin 6) :=
  ![1, Equiv.swap 0 1, Equiv.swap 0 2,
    Equiv.swap 0 3 * Equiv.swap 1 4 * Equiv.swap 2 5,
    Equiv.swap 0 4 * Equiv.swap 1 3 * Equiv.swap 2 5,
    Equiv.swap 0 5 * Equiv.swap 1 3 * Equiv.swap 2 4]

/-- The three Gamma factors used in each terminating Whipple relation,
Rao–Lakshminarayanan (4.36)–(4.56), RL-4.06. -/
def terminatingFactor (r : Fin 6 → ℂ) (l : Fin 6) : ℂ :=
  if l.val < 3 then
    ∏ j ∈ Icc (3 : Fin 6) 5, Gamma (1 / 2 + (r 0 + r 1 + r 2 - r l) + r j)
  else ∏ k : Fin 3, Gamma (1 / 2 + (r 0 + r 1 + r 2 - r k.castSucc.castSucc.castSucc) + r l)

/-- The six fixed arrangements used in RL-4.06. -/
theorem arrangement_def : arrangement =
    ![1, Equiv.swap 0 1, Equiv.swap 0 2,
      Equiv.swap 0 3 * Equiv.swap 1 4 * Equiv.swap 2 5,
      Equiv.swap 0 4 * Equiv.swap 1 3 * Equiv.swap 2 5,
      Equiv.swap 0 5 * Equiv.swap 1 3 * Equiv.swap 2 4] := rfl

/-- The explicit Gamma products in the six terminating relations, RL-4.06. -/
theorem terminatingFactor_def (r : Fin 6 → ℂ) (l : Fin 6) :
    terminatingFactor r l = if l.val < 3 then
      ∏ j ∈ Icc (3 : Fin 6) 5, Gamma (1 / 2 + (r 0 + r 1 + r 2 - r l) + r j)
    else ∏ k : Fin 3,
      Gamma (1 / 2 + (r 0 + r 1 + r 2 - r k.castSucc.castSucc.castSucc) + r l) := rfl

/-- The six normalized terminating Whipple functions agree with the prescribed sign,
Rao–Lakshminarayanan (4.36)–(4.56), RL-4.06. This states the regular Gamma-factor
locus; its exceptional finite extension is the denominator-cleared polynomial invariant. -/
theorem terminating_relations (N : ℕ) (r : Fin 6 → ℂ) (hr : ∑ i, r i = 0)
    (hN : alpha r 3 4 5 = -(N : ℂ))
    (hreg : ∀ l : Fin 6, LowerParametersRegular
      (lower (if l.val < 3 then r else -r) (arrangement l)))
    (hfac : ∀ l, terminatingFactor r l ≠ 0) (l : Fin 6) :
    terminatingFactor r 0 * positive r (arrangement 0) =
      terminatingFactor r l *
        (if l.val < 3 then positive r (arrangement l)
          else (-1 : ℂ) ^ N * negative r (arrangement l)) := by
  sorry

open DLMF.Hypergeometric.TransformationGroups

/-- The sign character in the signed-permutation realization, RL-4.10. -/
def epsilon (g : terminatingGroup) : ℂ := if g.val.2 = 1 then 1 else -1

/-- The signed action on Whipple coordinates, Rao–Lakshminarayanan (4.57)–(4.69). -/
def action (g : terminatingGroup) (r : Fin 6 → ℂ) (i : Fin 6) : ℂ :=
  epsilon g * r (g.val.1⁻¹ i)

/-- The five terminating parameters extracted from the six Whipple coordinates,
Rao–Lakshminarayanan (4.6)–(4.11), synopsis RL-4.10. -/
def parameters (r : Fin 6 → ℂ) : Fin 5 → ℂ :=
  ![alpha r 1 4 5, alpha r 2 4 5, 1 + alpha r 3 4 5, beta r 4 0, beta r 5 0]

/-- The defining sign character, RL-4.10. -/
theorem epsilon_def (g : terminatingGroup) : epsilon g = if g.val.2 = 1 then 1 else -1 := rfl

/-- The defining signed coordinate action, RL-4.07. -/
theorem action_def (g : terminatingGroup) (r : Fin 6 → ℂ) (i : Fin 6) :
    action g r i = epsilon g * r (g.val.1⁻¹ i) := rfl

/-- The five original parameters from Whipple coordinates, RL-4.10. -/
theorem parameters_def (r : Fin 6 → ℂ) : parameters r =
    ![alpha r 1 4 5, alpha r 2 4 5, 1 + alpha r 3 4 5, beta r 4 0, beta r 5 0] := rfl

/-- The sign is multiplicative, Rao–Lakshminarayanan (4.93)–(4.95), RL-4.10. -/
theorem epsilon_mul (g h : terminatingGroup) : epsilon (g * h) = epsilon g * epsilon h := by
  sorry

/-- Polynomial invariance under every generated terminating transformation,
Rao–Lakshminarayanan (4.93)–(4.95), synopsis RL-4.10. -/
theorem scaledThreeF2_action (N : ℕ) (r : Fin 6 → ℂ) (hr : ∑ i, r i = 0)
    (hN : alpha r 3 4 5 = -(N : ℂ)) (g : terminatingGroup) :
    TerminatingTransformations.scaledThreeF2 N (parameters r) =
      epsilon g ^ N * TerminatingTransformations.scaledThreeF2 N (parameters (action g r)) := by
  sorry

/-- The signed coordinate action has the claimed faithful irreducible four-dimensional
summand and two one-dimensional summands, Rao–Lakshminarayanan (4.57)–(4.69), RL-4.07.
The four-dimensional summand consists of vectors whose sums on both triples vanish. -/
theorem exists_representation_decomposition :
    ∃ ρ : Representation ℂ terminatingGroup (Fin 6 → ℂ),
      (∀ g v i, ρ g v i = action g v i) ∧
      Function.Injective ρ ∧
      ∃ V : Submodule ℂ (Fin 6 → ℂ),
        (∀ v, v ∈ V ↔ v 0 + v 1 + v 2 = 0 ∧ v 3 + v 4 + v 5 = 0) ∧
        Module.finrank ℂ V = 4 ∧
        (∀ g v, v ∈ V → ρ g v ∈ V) ∧
        (∀ W : Submodule ℂ (Fin 6 → ℂ), W ≤ V →
          (∀ g v, v ∈ W → ρ g v ∈ W) → W = ⊥ ∨ W = V) ∧
        (∀ g, ρ g (fun _ => 1) = fun _ => epsilon g) ∧
        (∀ g, ρ g (fun i => if i.val < 3 then 1 else -1) =
          fun i => if i.val < 3 then 1 else -1) ∧
        ∀ v : Fin 6 → ℂ, ∃! p : ℂ × ℂ × V,
          v = fun i => p.1 + p.2.1 * (if i.val < 3 then 1 else -1) + p.2.2.val i := by
  sorry

end DLMF.Hypergeometric.WhippleCoordinates
