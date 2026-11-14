/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ParabolicCylinder.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The fixed-argument large-positive-parameter cylinder scale

Olver, *Asymptotics and Special Functions*, Chapter 9, §5,
pp. 334–336, synopsis O-9.06. The normalization is the canonical Weber
function U(a,z), not the differently indexed D function.
-/

@[expose] public noncomputable section
open Filter Asymptotics
open scoped Topology
namespace DLMF.Confluent

/-- The exact fixed-argument scale and its relative inverse-square-root error.
Olver, Chapter 9, §5, pp. 334–336. -/
theorem isBigO_parabolicCylinderU_nat_add_half_div_main_sub_one (a : ℝ) :
    (fun n : ℕ => parabolicCylinderU ((n : ℂ) + 1 / 2) a /
      ((Real.sqrt Real.pi * (n : ℝ) ^ ((n : ℝ) / 2) *
        Real.exp (-(n : ℝ) / 2 - a * Real.sqrt n) / Real.Gamma (n + 1) : ℝ) : ℂ) - 1)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-1 / 2 : ℝ)) := by
  sorry

end DLMF.Confluent
