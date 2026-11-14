/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.ArgumentContinuation
public import Mathlib.Data.Fin.VecNotation

/-!
# The regularized twenty-four Kummer solutions

Duverney, *An Introduction to Hypergeometric Functions*, Chapter 4,
equations (4.26)–(4.37), specifies eight solutions on each real interval separated
by zero and one. The eight-function generator below spells out every prefactor and
parameter. Regularization retains all lower parameters, although some solutions may
vanish or become dependent at exceptional parameters.
-/

@[expose] public noncomputable section

open Complex Set

namespace DLMF.Hypergeometric.KummerSolutions

/-- The eight regularized Kummer expressions on `0<t<1`.
Duverney (4.26)–(4.37), synopsis DU-4.05. Complex powers use the principal branch;
all bases of the prefactors are positive on the stated real interval. -/
def eightSolutions (A B C : ℂ) (t : ℝ) : Fin 8 → ℂ :=
  ![regularizedGaussHypergeometric A B C t,
    (t : ℂ) ^ (1 - C) * regularizedGaussHypergeometric
      (A - C + 1) (B - C + 1) (2 - C) t,
    (1 - (t : ℂ)) ^ (C - A - B) * regularizedGaussHypergeometric (C - A) (C - B) C t,
    (t : ℂ) ^ (1 - C) * (1 - (t : ℂ)) ^ (C - A - B) *
      regularizedGaussHypergeometric (1 - A) (1 - B) (2 - C) t,
    regularizedGaussHypergeometric A B (A + B - C + 1) (1 - t),
    (1 - (t : ℂ)) ^ (C - A - B) * regularizedGaussHypergeometric
      (C - A) (C - B) (C - A - B + 1) (1 - t),
    (t : ℂ) ^ (1 - C) * regularizedGaussHypergeometric
      (A - C + 1) (B - C + 1) (A + B - C + 1) (1 - t),
    (t : ℂ) ^ (1 - C) * (1 - (t : ℂ)) ^ (C - A - B) *
      regularizedGaussHypergeometric (1 - A) (1 - B) (C - A - B + 1) (1 - t)]

/-- The explicit vector is the defining formula for the eight Kummer expressions.
Duverney (4.26)–(4.37), synopsis DU-4.05. -/
theorem eightSolutions_def (A B C : ℂ) (t : ℝ) :
    eightSolutions A B C t =
      ![regularizedGaussHypergeometric A B C t,
        (t : ℂ) ^ (1 - C) * regularizedGaussHypergeometric
          (A - C + 1) (B - C + 1) (2 - C) t,
        (1 - (t : ℂ)) ^ (C - A - B) * regularizedGaussHypergeometric (C - A) (C - B) C t,
        (t : ℂ) ^ (1 - C) * (1 - (t : ℂ)) ^ (C - A - B) *
          regularizedGaussHypergeometric (1 - A) (1 - B) (2 - C) t,
        regularizedGaussHypergeometric A B (A + B - C + 1) (1 - t),
        (1 - (t : ℂ)) ^ (C - A - B) * regularizedGaussHypergeometric
          (C - A) (C - B) (C - A - B + 1) (1 - t),
        (t : ℂ) ^ (1 - C) * regularizedGaussHypergeometric
          (A - C + 1) (B - C + 1) (A + B - C + 1) (1 - t),
        (t : ℂ) ^ (1 - C) * (1 - (t : ℂ)) ^ (C - A - B) *
          regularizedGaussHypergeometric (1 - A) (1 - B) (C - A - B + 1) (1 - t)] := rfl

/-- Every one of the eight expressions solves Gauss's equation on the unit interval.
Duverney (4.26)–(4.37), synopsis DU-4.05. -/
theorem eightSolutions_ode (a b c : ℂ) (i : Fin 8) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (x : ℂ) * (1 - x) * iteratedDeriv 2 (fun t => eightSolutions a b c t i) x +
      (c - (a + b + 1) * x) * deriv (fun t => eightSolutions a b c t i) x -
        a * b * eightSolutions a b c x i = 0 := by
  sorry

/-- The eight infinity expressions obtained by inversion solve Gauss's equation on `x>1`.
Duverney (4.26)–(4.37), synopsis DU-4.05. -/
theorem eightSolutions_inversion_ode (a b c : ℂ) (i : Fin 8) {x : ℝ} (hx : 1 < x) :
    let y : ℝ → ℂ := fun t => (t : ℂ) ^ (-a) *
      eightSolutions a (a - c + 1) (a - b + 1) t⁻¹ i
    (x : ℂ) * (1 - x) * iteratedDeriv 2 y x +
      (c - (a + b + 1) * x) * deriv y x - a * b * y x = 0 := by
  sorry

/-- The eight Pfaff-inversion expressions solve Gauss's equation on `x<0`.
Duverney (4.26)–(4.37), synopsis DU-4.05. -/
theorem eightSolutions_pfaff_inversion_ode (a b c : ℂ) (i : Fin 8) {x : ℝ} (hx : x < 0) :
    let y : ℝ → ℂ := fun t => (1 - (t : ℂ)) ^ (-a) *
      eightSolutions a (c - b) (a - b + 1) (1 - t)⁻¹ i
    (x : ℂ) * (1 - x) * iteratedDeriv 2 y x +
      (c - (a + b + 1) * x) * deriv y x - a * b * y x = 0 := by
  sorry

end DLMF.Hypergeometric.KummerSolutions
