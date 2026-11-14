/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic.CutPlane
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The finite algorithm for Kummer's twenty-four expressions

A permutation orders the three marked points `0,1,infinity`; two independent
binary choices select the exponents to remove at the first two points. The
resulting formulas use the canonical continued regularized Gauss function.
The number twenty-four counts symbolic expressions, not distinct solutions.
Source: Kristensson, *Second Order Differential Equations*, Chapter 5,
Theorem 5.2, pp. 73–76; DLMF §15.10(ii).
-/

@[expose] public noncomputable section

open Complex
open scoped Real

namespace DLMF.Hypergeometric.KummerPermutations

/-- The exponent pairs at `0,1,infinity`, indexed in that order.
Kristensson, Chapter 5, Theorem 5.2, pp. 73–76. -/
def exponents (a b c : ℂ) : Fin 3 → ℂ × ℂ := ![(0, 1 - c), (0, c - a - b), (a, b)]

/-- The defining three exponent pairs. -/
theorem exponents_def (a b c : ℂ) :
    exponents a b c = ![(0, 1 - c), (0, c - a - b), (a, b)] := rfl

/-- The unique one of the six standard Möbius maps taking the marked points
`σ 0,σ 1,σ 2` to `0,1,infinity`, respectively. The index `2` denotes infinity.
Kristensson, Chapter 5, Theorem 5.2, pp. 73–76. -/
def coordinate (σ : Equiv.Perm (Fin 3)) (z : ℂ) : ℂ :=
  if σ 0 = 0 then if σ 1 = 1 then z else z / (z - 1)
  else if σ 0 = 1 then if σ 1 = 0 then 1 - z else (z - 1) / z
  else if σ 1 = 0 then 1 / (1 - z) else 1 / z

/-- The six defining coordinate cases. -/
theorem coordinate_def (σ : Equiv.Perm (Fin 3)) (z : ℂ) : coordinate σ z =
    if σ 0 = 0 then if σ 1 = 1 then z else z / (z - 1)
    else if σ 0 = 1 then if σ 1 = 0 then 1 - z else (z - 1) / z
    else if σ 1 = 0 then 1 / (1 - z) else 1 / z := rfl

/-- The identity permutation gives the original coordinate. -/
@[simp] theorem coordinate_refl (z : ℂ) : coordinate (Equiv.refl (Fin 3)) z = z := by
  simp [coordinate]

/-- Select one exponent from a pair; false selects the first, true the second. -/
def selectedExponent (p : ℂ × ℂ) (second : Bool) : ℂ := if second then p.2 else p.1

/-- The defining binary exponent choice. -/
theorem selectedExponent_def (p : ℂ × ℂ) (second : Bool) :
    selectedExponent p second = if second then p.2 else p.1 := rfl

/-- The transformed upper and lower parameters `(A,B,C)` in the finite algorithm.
Kristensson, Chapter 5, Theorem 5.2, pp. 73–76. -/
def parameters (a b c : ℂ) (σ : Equiv.Perm (Fin 3)) (first second : Bool) : ℂ × ℂ × ℂ :=
  let p := exponents a b c
  let r := selectedExponent (p (σ 0)) first
  let r' := selectedExponent (p (σ 0)) (!first)
  let s := selectedExponent (p (σ 1)) second
  ((p (σ 2)).1 + r + s, (p (σ 2)).2 + r + s, 1 + r - r')

/-- The explicit transformed-parameter algorithm. -/
theorem parameters_def (a b c : ℂ) (σ : Equiv.Perm (Fin 3)) (first second : Bool) :
    parameters a b c σ first second =
      let p := exponents a b c
      let r := selectedExponent (p (σ 0)) first
      let r' := selectedExponent (p (σ 0)) (!first)
      let s := selectedExponent (p (σ 1)) second
      ((p (σ 2)).1 + r + s, (p (σ 2)).2 + r + s, 1 + r - r') := rfl

/-- The explicit gauge multiplying the transformed Gauss function. Principal
powers are used only on the stated common branch domain in the ODE theorem.
Kristensson, Chapter 5, Theorem 5.2, pp. 73–76. -/
def gauge (a b c : ℂ) (σ : Equiv.Perm (Fin 3)) (first second : Bool) (z : ℂ) : ℂ :=
  coordinate σ z ^ selectedExponent (exponents a b c (σ 0)) first *
    (1 - coordinate σ z) ^ selectedExponent (exponents a b c (σ 1)) second

/-- The defining two powers of the gauge. -/
theorem gauge_def (a b c : ℂ) (σ : Equiv.Perm (Fin 3)) (first second : Bool) (z : ℂ) :
    gauge a b c σ first second z =
      coordinate σ z ^ selectedExponent (exponents a b c (σ 0)) first *
        (1 - coordinate σ z) ^ selectedExponent (exponents a b c (σ 1)) second := rfl

/-- The continued regularized expression belonging to one of the twenty-four
indices. At admissible `C`, multiplication by `Gamma(C)` recovers the book's
ordinary normalization. Kristensson, Chapter 5, Theorem 5.2, pp. 73–76. -/
def solution (a b c : ℂ) (σ : Equiv.Perm (Fin 3)) (first second : Bool) (z : ℂ) : ℂ :=
  let p := parameters a b c σ first second
  gauge a b c σ first second z * regularizedGaussHypergeometric p.1 p.2.1 p.2.2 (coordinate σ z)

/-- The defining continued Gauss expression. -/
theorem solution_def (a b c : ℂ) (σ : Equiv.Perm (Fin 3)) (first second : Bool) (z : ℂ) :
    solution a b c σ first second z =
      let p := parameters a b c σ first second
      gauge a b c σ first second z *
        regularizedGaussHypergeometric p.1 p.2.1 p.2.2 (coordinate σ z) := rfl

/-- There are twenty-four symbolic indices: six permutations and four exponent
choices. The assertion does not count distinct functions. Kristensson,
Chapter 5, Theorem 5.2, pp. 73–76. -/
theorem card_indices : Fintype.card (Equiv.Perm (Fin 3) × Bool × Bool) = 24 := by
  decide

/-- Every expression in the finite algorithm solves the original Gauss equation
on its common analytic branch domain. The regularized equation also makes sense
at exceptional lower parameters, although a logarithmic basis may then be needed.
Kristensson, Chapter 5, Theorem 5.2, pp. 73–76. -/
theorem gaussOperator_solution (a b c : ℂ) (σ : Equiv.Perm (Fin 3))
    (first second : Bool) {z : ℂ} (hz₀ : z ≠ 0) (hz₁ : z ≠ 1)
    (hT : coordinate σ z ∈ slitPlane) (h₁T : 1 - coordinate σ z ∈ slitPlane) :
    gaussOperator a b c (solution a b c σ first second) z = 0 := by
  sorry

/-- Inside the transformed series disc and at an admissible lower parameter,
the regularized expression is exactly the ordinary expression divided by Gamma(C).
This bridge is not used to assign ordinary totalized series continuation outside
its disc. Kristensson, Chapter 5, Theorem 5.2, pp. 73–76. -/
theorem solution_eq_ordinary (a b c : ℂ) (σ : Equiv.Perm (Fin 3))
    (first second : Bool) {z : ℂ} (hz : ‖coordinate σ z‖ < 1)
    (hC : ∀ n : ℕ, (parameters a b c σ first second).2.2 ≠ -(n : ℂ)) :
    solution a b c σ first second z =
      let p := parameters a b c σ first second
      gauge a b c σ first second z *
        ordinaryHypergeometric p.1 p.2.1 p.2.2 (coordinate σ z) / Gamma p.2.2 := by
  sorry

end DLMF.Hypergeometric.KummerPermutations
