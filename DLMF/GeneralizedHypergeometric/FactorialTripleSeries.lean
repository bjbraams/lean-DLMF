/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Basic.MultipleSeries
public import Mathlib.Data.Fintype.Pi

/-!
# Factorial triple sums as explicit multiple hypergeometric series

Rao–Lakshminarayanan, *Generalized Hypergeometric Functions* (2018),
§7.3, (7.55)–(7.59), synopsis RL-7.09. This is a purely algebraic
coefficient identification; it asserts no unverified nine-j phase formula.
The natural parameter arrays express the regular zero-index factorial case.
-/

@[expose] public noncomputable section
namespace DLMF.Hypergeometric.FactorialTripleSeries

/-- The exact nonnegative factorial domain for the regular triple-sum term,
Rao–Lakshminarayanan (7.44)–(7.59), synopsis RL-7.09. -/
def InSupport (X Y Z : Fin 5 → ℕ) (P : Fin 3 → ℕ) (m : Fin 3 → ℕ) : Prop :=
  m 0 ≤ X 0 ∧ m 0 ≤ X 3 ∧ m 0 ≤ X 4 ∧ m 1 ≤ Y 3 ∧ m 1 ≤ Y 4 ∧
    m 2 ≤ Z 0 ∧ m 2 ≤ Z 2 ∧ m 2 ≤ Z 3 ∧ m 2 ≤ Z 4 ∧ m 1 + m 2 ≤ P 0

/-- The support inequalities are precisely the factorial-domain conditions,
Rao–Lakshminarayanan (7.55)–(7.59), RL-7.09. -/
theorem inSupport_iff (X Y Z : Fin 5 → ℕ) (P : Fin 3 → ℕ) (m : Fin 3 → ℕ) :
    InSupport X Y Z P m ↔
      m 0 ≤ X 0 ∧ m 0 ≤ X 3 ∧ m 0 ≤ X 4 ∧ m 1 ≤ Y 3 ∧ m 1 ≤ Y 4 ∧
        m 2 ≤ Z 0 ∧ m 2 ≤ Z 2 ∧ m 2 ≤ Z 3 ∧ m 2 ≤ Z 4 ∧ m 1 + m 2 ≤ P 0 := Iff.rfl

/-- The finite factorial summand, with value zero outside the exact support,
Rao–Lakshminarayanan (7.44)–(7.59), synopsis RL-7.09. All subtractions
inside a factorial are performed only after the support guard. -/
def factorialTerm (X Y Z : Fin 5 → ℕ) (P : Fin 3 → ℕ) (m : Fin 3 → ℕ) : ℂ := by
  classical
  exact if InSupport X Y Z P m then
    (-1 : ℂ) ^ (m 0 + m 1 + m 2) /
      ((m 0).factorial * (m 1).factorial * (m 2).factorial) *
    (((X 0 - m 0).factorial : ℂ) * (X 1 + m 0).factorial * (X 2 + m 0).factorial /
      ((X 3 - m 0).factorial * (X 4 - m 0).factorial)) *
    (((Y 0 + m 1).factorial : ℂ) * (Y 1 + m 1).factorial /
      ((Y 2 + m 1).factorial * (Y 3 - m 1).factorial * (Y 4 - m 1).factorial)) *
    (((Z 0 - m 2).factorial : ℂ) * (Z 1 + m 2).factorial /
      ((Z 2 - m 2).factorial * (Z 3 - m 2).factorial * (Z 4 - m 2).factorial)) *
    ((P 0 - m 1 - m 2).factorial : ℂ) /
      ((P 1 + m 0 + m 1).factorial * (P 2 + m 0 + m 2).factorial)
  else 0

/-- The factorial formula on its genuine finite support,
Rao–Lakshminarayanan (7.55)–(7.59), synopsis RL-7.09. -/
theorem factorialTerm_of_inSupport (X Y Z : Fin 5 → ℕ) (P : Fin 3 → ℕ)
    (m : Fin 3 → ℕ) (hm : InSupport X Y Z P m) :
    factorialTerm X Y Z P m =
    (-1 : ℂ) ^ (m 0 + m 1 + m 2) /
      ((m 0).factorial * (m 1).factorial * (m 2).factorial) *
    (((X 0 - m 0).factorial : ℂ) * (X 1 + m 0).factorial * (X 2 + m 0).factorial /
      ((X 3 - m 0).factorial * (X 4 - m 0).factorial)) *
    (((Y 0 + m 1).factorial : ℂ) * (Y 1 + m 1).factorial /
      ((Y 2 + m 1).factorial * (Y 3 - m 1).factorial * (Y 4 - m 1).factorial)) *
    (((Z 0 - m 2).factorial : ℂ) * (Z 1 + m 2).factorial /
      ((Z 2 - m 2).factorial * (Z 3 - m 2).factorial * (Z 4 - m 2).factorial)) *
    ((P 0 - m 1 - m 2).factorial : ℂ) /
      ((P 1 + m 0 + m 1).factorial * (P 2 + m 0 + m 2).factorial) := by
  classical
  simp only [factorialTerm, hm, ↓reduceIte]

/-- The four individual-index upper parameters in each direction,
Rao–Lakshminarayanan (7.55)–(7.59), synopsis RL-7.09. -/
def upper (X Y Z : Fin 5 → ℕ) : Fin 3 → Multiset ℂ :=
  ![{1 + (X 1 : ℂ), 1 + (X 2 : ℂ), -(X 3 : ℂ), -(X 4 : ℂ)},
    {1 + (Y 0 : ℂ), 1 + (Y 1 : ℂ), -(Y 3 : ℂ), -(Y 4 : ℂ)},
    {1 + (Z 1 : ℂ), -(Z 2 : ℂ), -(Z 3 : ℂ), -(Z 4 : ℂ)}]

/-- The pairwise-index lower parameters, ordered as `x+y,y+z,z+x`,
Rao–Lakshminarayanan (7.55)–(7.59), synopsis RL-7.09. -/
def pairLower (P : Fin 3 → ℕ) : Fin 3 → Multiset ℂ :=
  ![{1 + (P 1 : ℂ)}, {-(P 0 : ℂ)}, {1 + (P 2 : ℂ)}]

/-- The individual-index lower parameters, Rao–Lakshminarayanan RL-7.09. -/
def lower (X Y Z : Fin 5 → ℕ) : Fin 3 → Multiset ℂ :=
  ![{-(X 0 : ℂ)}, {1 + (Y 2 : ℂ)}, {-(Z 0 : ℂ)}]

/-- The upper-list formula of RL-7.09. -/
theorem upper_def (X Y Z : Fin 5 → ℕ) : upper X Y Z =
    ![{1 + (X 1 : ℂ), 1 + (X 2 : ℂ), -(X 3 : ℂ), -(X 4 : ℂ)},
      {1 + (Y 0 : ℂ), 1 + (Y 1 : ℂ), -(Y 3 : ℂ), -(Y 4 : ℂ)},
      {1 + (Z 1 : ℂ), -(Z 2 : ℂ), -(Z 3 : ℂ), -(Z 4 : ℂ)}] := rfl

/-- The pairwise lower-list formula of RL-7.09. -/
theorem pairLower_def (P : Fin 3 → ℕ) : pairLower P =
    ![{1 + (P 1 : ℂ)}, {-(P 0 : ℂ)}, {1 + (P 2 : ℂ)}] := rfl

/-- The individual lower-list formula of RL-7.09. -/
theorem lower_def (X Y Z : Fin 5 → ℕ) : lower X Y Z =
    ![{-(X 0 : ℂ)}, {1 + (Y 2 : ℂ)}, {-(Z 0 : ℂ)}] := rfl

/-- The zero-index factorial is nonzero in the regular factorial domain,
Rao–Lakshminarayanan (7.55)–(7.59), synopsis RL-7.09. -/
theorem factorialTerm_zero_ne_zero (X Y Z : Fin 5 → ℕ) (P : Fin 3 → ℕ) :
    factorialTerm X Y Z P (fun _ => 0) ≠ 0 := by
  classical
  simp [factorialTerm, InSupport, Nat.factorial_ne_zero]

/-- A factorial term vanishes outside its precise finite support,
Rao–Lakshminarayanan (7.55)–(7.59), synopsis RL-7.09. -/
theorem factorialTerm_eq_zero_of_not_inSupport (X Y Z : Fin 5 → ℕ) (P : Fin 3 → ℕ)
    (m : Fin 3 → ℕ) (hm : ¬ InSupport X Y Z P m) : factorialTerm X Y Z P m = 0 := by
  classical
  simp [factorialTerm, hm]

/-- The factorial summand divided by its zero-index value is exactly the stated
multiple hypergeometric coefficient, Rao–Lakshminarayanan (7.55)–(7.59), RL-7.09. -/
theorem factorialTerm_eq_mul_coefficient (X Y Z : Fin 5 → ℕ) (P : Fin 3 → ℕ)
    (m : Fin 3 → ℕ) :
    factorialTerm X Y Z P m = factorialTerm X Y Z P (fun _ => 0) *
      TripleHypergeometric.coefficient ∅ ∅ (fun _ => ∅) (upper X Y Z)
        (pairLower P) (lower X Y Z) m := by
  sorry

/-- The triple factorial summation has finite support, Rao–Lakshminarayanan RL-7.09. -/
theorem finite_support_factorialTerm (X Y Z : Fin 5 → ℕ) (P : Fin 3 → ℕ) :
    (Function.support (factorialTerm X Y Z P)).Finite := by
  let b : Fin 3 → ℕ := ![X 3, Y 3, Z 3]
  have hbox : {m : Fin 3 → ℕ | ∀ i, m i ∈ Set.Iic (b i)}.Finite :=
    Set.Finite.pi' (fun i => Set.finite_Iic (b i))
  refine hbox.subset ?_
  intro m hm
  have hs : InSupport X Y Z P m := by
    by_contra h
    exact hm (factorialTerm_eq_zero_of_not_inSupport X Y Z P m h)
  intro i
  fin_cases i
  · exact hs.2.1
  · exact hs.2.2.2.1
  · exact hs.2.2.2.2.2.2.2.1

/-- The regular triple factorial sum is the explicitly parametrized finite `F^(3)` value,
Rao–Lakshminarayanan (7.55)–(7.59), synopsis RL-7.09. -/
theorem tsum_factorialTerm_eq_tripleHypergeometric (X Y Z : Fin 5 → ℕ) (P : Fin 3 → ℕ) :
    (∑' m : Fin 3 → ℕ, factorialTerm X Y Z P m) =
      factorialTerm X Y Z P (fun _ => 0) *
        TripleHypergeometric.value ∅ ∅ (fun _ => ∅) (upper X Y Z) (pairLower P)
          (lower X Y Z) (fun _ => 1) := by
  sorry

end DLMF.Hypergeometric.FactorialTripleSeries
