/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Askey–Wilson and Nassrallah–Rahman beta integrals

The ordinary real-angle integrals of Andrews, Askey and Roy, *Special Functions*,
§10.8. The products are paired complex products and remain meaningful for complex bases.
-/

@[expose] public section

open Finset MeasureTheory
open scoped Real

noncomputable section

namespace DLMF.QHypergeometric

open DLMF.QSeries

/-- The paired infinite shifted factorial occurring in trigonometric beta integrals.
Andrews–Askey–Roy, *Special Functions*, §10.8 (synopsis AAR-10.8.1–10.8.2). -/
def pairedShiftedFactorial (a q : ℂ) (θ : ℝ) : ℂ :=
  qPochhammerInf (a * Complex.exp (Complex.I * θ)) q *
    qPochhammerInf (a * Complex.exp (-Complex.I * θ)) q

/-- The paired complex-product formula. -/
theorem pairedShiftedFactorial_def (a q : ℂ) (θ : ℝ) :
    pairedShiftedFactorial a q θ =
      qPochhammerInf (a * Complex.exp (Complex.I * θ)) q *
        qPochhammerInf (a * Complex.exp (-Complex.I * θ)) q := rfl

/-- The Askey–Wilson integral for a complex base in the unit disk.
Andrews–Askey–Roy, *Special Functions*, Theorem 10.8.1
(synopsis AAR-10.8.1–10.8.2). -/
theorem askey_wilson_integral {a b c d q : ℂ} (hq : ‖q‖ < 1)
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (hc : ‖c‖ < 1) (hd : ‖d‖ < 1) :
    IntegrableOn
      (fun θ : ℝ => pairedShiftedFactorial 1 q (2 * θ) /
        (pairedShiftedFactorial a q θ * pairedShiftedFactorial b q θ *
          pairedShiftedFactorial c q θ * pairedShiftedFactorial d q θ))
      (Set.Ioo 0 Real.pi) ∧
    (∫ θ in Set.Ioo 0 Real.pi, pairedShiftedFactorial 1 q (2 * θ) /
      (pairedShiftedFactorial a q θ * pairedShiftedFactorial b q θ *
        pairedShiftedFactorial c q θ * pairedShiftedFactorial d q θ)) =
      2 * Real.pi * qPochhammerInf (a * b * c * d) q /
        (qPochhammerInf q q * qPochhammerInf (a * b) q *
          qPochhammerInf (a * c) q * qPochhammerInf (a * d) q *
          qPochhammerInf (b * c) q * qPochhammerInf (b * d) q *
          qPochhammerInf (c * d) q) := by
  sorry

/-- The Nassrallah–Rahman extension, with products of the other four parameters at
zero parameters. Andrews–Askey–Roy, *Special Functions*, Theorem 10.8.2
(synopsis AAR-10.8.1–10.8.2). -/
theorem nassrallah_rahman_integral (a : Fin 5 → ℂ) {q : ℂ} (hq : ‖q‖ < 1)
    (ha : ∀ i, ‖a i‖ < 1) :
    IntegrableOn
      (fun θ : ℝ => pairedShiftedFactorial 1 q (2 * θ) *
        pairedShiftedFactorial (∏ i, a i) q θ /
        (∏ i, pairedShiftedFactorial (a i) q θ)) (Set.Ioo 0 Real.pi) ∧
    (∫ θ in Set.Ioo 0 Real.pi, pairedShiftedFactorial 1 q (2 * θ) *
      pairedShiftedFactorial (∏ i, a i) q θ /
      (∏ i, pairedShiftedFactorial (a i) q θ)) =
      2 * Real.pi * (∏ i : Fin 5, qPochhammerInf (∏ j ∈ univ.erase i, a j) q) /
        (qPochhammerInf q q *
          ∏ i : Fin 5, ∏ j ∈ univ.filter (i < ·), qPochhammerInf (a i * a j) q) := by
  sorry

end DLMF.QHypergeometric
