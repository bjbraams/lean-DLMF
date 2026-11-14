/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.Polynomial.PartialFractions
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Complex.Basic

/-!
# Analytic coefficients of rational partial fractions

A factored denominator supplies explicit polynomial cofactors. Taylor derivatives
of the cancelled rational function give every principal-part coefficient, with
polynomial division fixing the entire polynomial part. Source: Kristensson,
*Second Order Differential Equations*, Appendix C, pp. 201–202.
-/

@[expose] public noncomputable section

open Complex Filter
open scoped BigOperators Topology

namespace Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The denominator with the entire root factor at `i` removed, including the
leading constant. Kristensson, Appendix C, pp. 201–202. -/
def partialFractionCofactor (c : ℂ) (a : ι → ℂ) (m : ι → ℕ) (i : ι) : Polynomial ℂ :=
  C c * ∏ j ∈ Finset.univ.erase i, (X - C (a j)) ^ m j

/-- The defining finite product of the cofactor polynomial. -/
theorem partialFractionCofactor_def (c : ℂ) (a : ι → ℂ) (m : ι → ℕ) (i : ι) :
    partialFractionCofactor c a m i =
      C c * ∏ j ∈ Finset.univ.erase i, (X - C (a j)) ^ m j := rfl

/-- Evaluation of the polynomial cofactor as a finite root product. -/
theorem eval_partialFractionCofactor (c : ℂ) (a : ι → ℂ) (m : ι → ℕ) (i : ι) (z : ℂ) :
    (partialFractionCofactor c a m i).eval z =
      c * ∏ j ∈ Finset.univ.erase i, (z - a j) ^ m j := by
  simp [partialFractionCofactor, eval_prod]

/-- The coefficient of `(z-a_i)^(-j-1)` from the Taylor derivatives of the
cancelled rational function. The mathematical principal-part range is `j<m_i`.
Kristensson, Appendix C, p. 202. -/
def partialFractionCoefficient (p : Polynomial ℂ) (c : ℂ) (a : ι → ℂ) (m : ι → ℕ)
    (i : ι) (j : ℕ) : ℂ :=
  iteratedDeriv (m i - 1 - j)
    (fun z => p.eval z / (partialFractionCofactor c a m i).eval z) (a i) /
      (m i - 1 - j).factorial

/-- The defining derivative/factorial expression for a principal-part coefficient. -/
theorem partialFractionCoefficient_def (p : Polynomial ℂ) (c : ℂ)
    (a : ι → ℂ) (m : ι → ℕ) (i : ι) (j : ℕ) :
    partialFractionCoefficient p c a m i j = iteratedDeriv (m i - 1 - j)
      (fun z => p.eval z / (partialFractionCofactor c a m i).eval z) (a i) /
        (m i - 1 - j).factorial := rfl

/-- The highest-pole coefficient is the value of the cancelled rational function. -/
theorem partialFractionCoefficient_top (p : Polynomial ℂ) (c : ℂ)
    (a : ι → ℂ) (m : ι → ℕ) (i : ι) :
    partialFractionCoefficient p c a m i (m i - 1) =
      p.eval (a i) / (partialFractionCofactor c a m i).eval (a i) := by
  simp [partialFractionCoefficient]

/-- The cancelled rational function is analytic at the selected root because all
other root factors are nonzero there. Kristensson, Appendix C, p. 202. -/
theorem analyticAt_div_partialFractionCofactor (p : Polynomial ℂ) {c : ℂ} (hc : c ≠ 0)
    {a : ι → ℂ} (ha : Function.Injective a) (m : ι → ℕ) (i : ι) :
    AnalyticAt ℂ (fun z => p.eval z / (partialFractionCofactor c a m i).eval z) (a i) := by
  sorry

/-- Rational partial fractions with all coefficients given explicitly by Taylor
derivatives. The polynomial quotient fixes the polynomial part uniquely.
Kristensson, Appendix C, pp. 201–202. -/
theorem eval_div_eval_eq_quotient_add_partialFractions (p q : Polynomial ℂ)
    {c : ℂ} (hc : c ≠ 0) {a : ι → ℂ} (ha : Function.Injective a)
    (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hq : q = C c * ∏ i, (X - C (a i)) ^ m i) {z : ℂ} (hz : q.eval z ≠ 0) :
    p.eval z / q.eval z = (p / q).eval z +
      ∑ i, ∑ j ∈ Finset.range (m i),
        partialFractionCoefficient p c a m i j / (z - a i) ^ (j + 1) := by
  sorry

/-- Once the polynomial quotient is fixed, the principal-part coefficients are
unique at all the distinct poles. Kristensson, Appendix C, p. 201. -/
theorem existsUnique_partialFractionCoefficients (p q : Polynomial ℂ)
    {c : ℂ} (hc : c ≠ 0) {a : ι → ℂ} (ha : Function.Injective a)
    (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hq : q = C c * ∏ i, (X - C (a i)) ^ m i) :
    ∃! b : (i : ι) → Fin (m i) → ℂ, ∀ z : ℂ, q.eval z ≠ 0 →
      p.eval z / q.eval z = (p / q).eval z +
        ∑ i, ∑ j : Fin (m i), b i j / (z - a i) ^ (j.val + 1) := by
  sorry

/-- The proper rational remainder tends to zero at infinity in every complex
direction, including constant denominators. Kristensson, Appendix C, p. 201. -/
theorem tendsto_eval_mod_div_eval_cobounded (p : Polynomial ℂ) {q : Polynomial ℂ}
    (hq : q ≠ 0) :
    Tendsto (fun z : ℂ => (p % q).eval z / q.eval z) (Bornology.cobounded ℂ) (𝓝 0) := by
  sorry

end Polynomial
