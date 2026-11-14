/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.FieldTheory.Finite.Extension

/-!
# Finite-field polynomial products and resultant characters

Andrews, Askey and Roy, *Special Functions*, §§8.10–8.11, pp. 430–439.
The character coefficient vanishing is Lemma 8.11.1; its modulus is nonconstant,
and its factor multiplicities are primitive for the generating character.
-/

@[expose] public noncomputable section

open scoped Classical

open UniqueFactorizationMonoid

namespace Polynomial

variable {F : Type*} [Field F] [Fintype F]

/-- The product of all monic irreducibles whose degrees divide `m` is `X^(q^m)-X`.
Andrews–Askey–Roy, *Special Functions*, §8.10, pp. 430–432
(synopsis AAR-8.10.4–8.11.2). The positive extension degree is essential. -/
theorem exists_prod_monic_irreducibles_degree_dvd (m : ℕ) (hm : 0 < m) :
    ∃ S : Finset F[X],
      (∀ P : F[X], P ∈ S ↔ P.Monic ∧ Irreducible P ∧ P.natDegree ∣ m) ∧
      ∏ P ∈ S, P = X ^ (Fintype.card F ^ m) - X := by
  sorry

/-- The resultant-character generating series has degree smaller than the degree of the
squarefree radical of its modulus. Andrews–Askey–Roy, *Special Functions*,
Lemma 8.11.1, pp. 436–437 (synopsis AAR-8.10.4–8.11.2).
The coefficient is a finite sum over all monic polynomials of degree `m`.
Every irreducible multiplicity is required to be nonzero modulo `q-1`. -/
theorem sum_resultant_mulChar_eq_zero (χ : MulChar F ℂ)
    (hχ : orderOf χ = Fintype.card F - 1) (V : F[X]) (hV : V.Monic)
    (hdegree : 0 < V.natDegree)
    (hprimitive : ∀ (P : F[X]) (k : ℕ), P.Monic → Irreducible P → 0 < k →
      P ^ k ∣ V → ¬P ^ (k + 1) ∣ V → ¬(Fintype.card F - 1) ∣ k)
    (m : ℕ) (hm : (normalizedFactors V).toFinset.sum (fun P => P.natDegree) ≤ m) :
    ∑ v : Fin m → F,
      χ (V.resultant (X ^ m + ∑ i : Fin m, C (v i) * X ^ i.val)) = 0 := by
  sorry

end Polynomial
