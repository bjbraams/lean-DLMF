/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
import DLMF.Heun.Basic
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# A boundary check for the Stieltjes-polynomial counting formula

For one singular point at zero, residue one and degree one, the defining polynomial
identity has no monic solution. The unrestricted binomial expression equals one.
The script proves this incompatibility without invoking the admitted counting theorem.
-/
open Complex Polynomial Set
namespace Chapter2036StatementChecks
open DLMF.Heun
/-- There is no monic linear Stieltjes solution with one singular point and positive residue. -/
lemma no_linear_stieltjes_singleton {S V : ℂ[X]} (hm : S.Monic)
    (h : IsVanVleckStieltjes (fun _ : Fin 1 => (0 : ℂ)) (fun _ => (1 : ℂ)) 1 V S) :
    False := by
  obtain ⟨hV, hdeg, _, heq⟩ := h
  have hS := hm.eq_X_add_C hdeg
  have hVc : V = C (V.coeff 0) := eq_C_of_natDegree_le_zero hV
  rw [IsStieltjesEquation, fuchsianPi, fuchsianGammaPoly] at heq
  simp at heq
  rw [hS, hVc] at heq
  simp only [derivative_add, derivative_X, derivative_C, add_zero, derivative_one,
    mul_zero, zero_add] at heq
  have hc1 := congrArg (fun p : ℂ[X] => p.coeff 1) heq
  have hc0 := congrArg (fun p : ℂ[X] => p.coeff 0) heq
  simp only [coeff_add, coeff_one, coeff_C_mul, coeff_X, coeff_C, one_ne_zero,
    ↓reduceIte, mul_one, add_zero, coeff_zero] at hc1 hc0
  simp only [zero_add] at hc1 hc0
  rw [hc1] at hc0
  norm_num at hc0
/-- The corresponding set of monic degree-one Stieltjes polynomials is empty. -/
lemma singleton_stieltjes_set_empty :
    {S : ℂ[X] | S.Monic ∧ ∃ V,
      IsVanVleckStieltjes (fun _ : Fin 1 => (0 : ℂ)) (fun _ => (1 : ℂ)) 1 V S} = ∅ := by
  ext S
  simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
  rintro ⟨hmono, V, h⟩
  exact no_linear_stieltjes_singleton hmono h
/-- The singleton configuration contradicts the unrestricted binomial count at degree one. -/
lemma stieltjes_card_counterexample :
    {S : ℂ[X] | S.Monic ∧ ∃ V,
      IsVanVleckStieltjes (fun _ : Fin 1 => (0 : ℂ)) (fun _ => (1 : ℂ)) 1 V S}.encard ≠
        (((1 + 0 - 1).choose (0 - 1) : ℕ) : ℕ∞) := by
  rw [singleton_stieltjes_set_empty]
  norm_num
/-- The one-point real singular configuration is strictly monotone. -/
lemma strictMono_singleton_configuration : StrictMono (fun _ : Fin 1 => (0 : ℝ)) := by
  intro i j hij
  have heq : i = j := Subsingleton.elim i j
  simp only [heq, lt_self_iff_false] at hij
/-- The one-point residue is positive. -/
lemma pos_singleton_residue (j : Fin 1) : (0 : ℝ) < (fun _ : Fin 1 => (1 : ℝ)) j := by norm_num
#print axioms no_linear_stieltjes_singleton
#print axioms singleton_stieltjes_set_empty
#print axioms stieltjes_card_counterexample
#print axioms strictMono_singleton_configuration
#print axioms pos_singleton_residue
end Chapter2036StatementChecks
