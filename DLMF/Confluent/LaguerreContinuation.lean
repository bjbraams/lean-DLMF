/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.BasicProperties.Continuity
public import DLMF.OrthogonalPolynomials.Basic.Classical
public import Mathlib.Data.Nat.Choose.Cast

/-!
# Tricomi's Laguerre specialization at all parameters

Temme, *Special Functions* (1996), Chapter 7, pages 185–186, synopsis TEM-07-12.
The polynomial continuation `laguerreExtended` retains exceptional negative integral
parameters, where a totalized ordinary hypergeometric quotient need not agree.
-/

@[expose] public noncomputable section

open Complex DLMF.Hypergeometric DLMF.OrthogonalPolynomials

namespace DLMF.Confluent

/-- The negative-integral first-parameter Tricomi function is the complete Laguerre
polynomial, including every exceptional second parameter. Temme, Chapter 7, pages
185–186, synopsis TEM-07-12. -/
theorem kummerU_eq_laguerreExtended (n : ℕ) (α z : ℂ) :
    kummerU (-(n : ℂ)) (α + 1) z =
      (-1 : ℂ) ^ n * n.factorial * laguerreExtended α n z := by
  rw [kummerU_neg_nat_sum, laguerreExtended, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  rw [Nat.cast_choose ℂ hk]
  have harg : α + 1 + (k : ℂ) = α + k + 1 := by ring
  rw [harg]
  ring

end DLMF.Confluent
