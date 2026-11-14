/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Basic.ParametersAndSeries

/-!
# Kampé de Fériet and general triple hypergeometric series

The coefficients use parameter multisets and the normalizations of Rao and
Lakshminarayanan, *Generalized Hypergeometric Functions* (2018), §§7.1 and 7.8,
equations (7.16)–(7.18) and (7.109). Values are totalized sums; analytic identities
involving them separately require absolute summability or finite support.
-/

@[expose] public noncomputable section
open scoped Nat

namespace DLMF.Hypergeometric

namespace KampeDeFeriet

/-- The two-index coefficient of the Kampé de Fériet series, Rao–Lakshminarayanan
§7.8, (7.109), synopsis RL-7.13. `A,C` couple both indices; the other lists
belong to the first and second indices respectively. -/
def coefficient (A B B' C D D' : Multiset ℂ) (mn : ℕ × ℕ) : ℂ :=
  pochhammerProduct A (mn.1 + mn.2) * pochhammerProduct B mn.1 *
    pochhammerProduct B' mn.2 /
    (pochhammerProduct C (mn.1 + mn.2) * pochhammerProduct D mn.1 *
      pochhammerProduct D' mn.2 * mn.1.factorial * mn.2.factorial)

/-- The explicitly indexed Kampé de Fériet term at `(x,y)`,
Rao–Lakshminarayanan §7.8, (7.109), synopsis RL-7.13. -/
def term (A B B' C D D' : Multiset ℂ) (x y : ℂ) (mn : ℕ × ℕ) : ℂ :=
  coefficient A B B' C D D' mn * x ^ mn.1 * y ^ mn.2

/-- The Kampé de Fériet series in Rao–Lakshminarayanan (7.109), synopsis RL-7.13.
This is a totalized sum, not a choice of analytic continuation at divergent arguments. -/
def value (A B B' C D D' : Multiset ℂ) (x y : ℂ) : ℂ :=
  ∑' mn : ℕ × ℕ, term A B B' C D D' x y mn

/-- The defining coefficient formula of RL-7.13. -/
theorem coefficient_def (A B B' C D D' : Multiset ℂ) (mn : ℕ × ℕ) :
    coefficient A B B' C D D' mn =
      pochhammerProduct A (mn.1 + mn.2) * pochhammerProduct B mn.1 *
        pochhammerProduct B' mn.2 /
        (pochhammerProduct C (mn.1 + mn.2) * pochhammerProduct D mn.1 *
          pochhammerProduct D' mn.2 * mn.1.factorial * mn.2.factorial) := rfl

/-- The defining summand formula of RL-7.13. -/
theorem term_def (A B B' C D D' : Multiset ℂ) (x y : ℂ) (mn : ℕ × ℕ) :
    term A B B' C D D' x y mn = coefficient A B B' C D D' mn * x ^ mn.1 * y ^ mn.2 :=
  rfl

/-- The defining sum of RL-7.13. -/
theorem value_def (A B B' C D D' : Multiset ℂ) (x y : ℂ) :
    value A B B' C D D' x y = ∑' mn : ℕ × ℕ, term A B B' C D D' x y mn := rfl

end KampeDeFeriet

namespace TripleHypergeometric

/-- The general three-index coefficient, Rao–Lakshminarayanan §7.1,
(7.16)–(7.18), synopsis RL-7.03. The three `B,F` lists correspond to
`m+n,n+r,r+m`, and the `C,G` lists to the three separate indices. -/
def coefficient (A E : Multiset ℂ) (B C F G : Fin 3 → Multiset ℂ)
    (m : Fin 3 → ℕ) : ℂ :=
  pochhammerProduct A (m 0 + m 1 + m 2) /
    pochhammerProduct E (m 0 + m 1 + m 2) *
    (∏ i : Fin 3, pochhammerProduct (B i) (m i + m (i + 1)) /
      pochhammerProduct (F i) (m i + m (i + 1))) *
    ∏ i : Fin 3, pochhammerProduct (C i) (m i) /
      (pochhammerProduct (G i) (m i) * (m i).factorial)

/-- The general triple series term, Rao–Lakshminarayanan (7.16)–(7.18),
synopsis RL-7.03. -/
def term (A E : Multiset ℂ) (B C F G : Fin 3 → Multiset ℂ)
    (z : Fin 3 → ℂ) (m : Fin 3 → ℕ) : ℂ :=
  coefficient A E B C F G m * ∏ i : Fin 3, z i ^ m i

/-- Rao–Lakshminarayanan's `F^(3)` series (7.16)–(7.18), synopsis RL-7.03,
with the natural totalized sum at divergent arguments. -/
def value (A E : Multiset ℂ) (B C F G : Fin 3 → Multiset ℂ)
    (z : Fin 3 → ℂ) : ℂ :=
  ∑' m : Fin 3 → ℕ, term A E B C F G z m

/-- The defining formula for the general triple coefficient of RL-7.03. -/
theorem coefficient_def (A E : Multiset ℂ) (B C F G : Fin 3 → Multiset ℂ)
    (m : Fin 3 → ℕ) :
    coefficient A E B C F G m =
      pochhammerProduct A (m 0 + m 1 + m 2) /
        pochhammerProduct E (m 0 + m 1 + m 2) *
        (∏ i : Fin 3, pochhammerProduct (B i) (m i + m (i + 1)) /
          pochhammerProduct (F i) (m i + m (i + 1))) *
        ∏ i : Fin 3, pochhammerProduct (C i) (m i) /
          (pochhammerProduct (G i) (m i) * (m i).factorial) := rfl

/-- The defining summand of RL-7.03. -/
theorem term_def (A E : Multiset ℂ) (B C F G : Fin 3 → Multiset ℂ)
    (z : Fin 3 → ℂ) (m : Fin 3 → ℕ) :
    term A E B C F G z m = coefficient A E B C F G m * ∏ i : Fin 3, z i ^ m i := rfl

/-- The defining totalized sum of RL-7.03. -/
theorem value_def (A E : Multiset ℂ) (B C F G : Fin 3 → Multiset ℂ)
    (z : Fin 3 → ℂ) : value A E B C F G z = ∑' m : Fin 3 → ℕ, term A E B C F G z m := rfl

end TripleHypergeometric
end DLMF.Hypergeometric
