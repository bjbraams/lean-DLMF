/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Fin.VecNotation

/-!
# Canonical position, momentum and orbital commutators

Rao–Lakshminarayanan, *Generalized Hypergeometric Functions* (2018), §2.3,
(2.75)–(2.95), and §5.1, (5.1)–(5.25), synopses RL-2.06 and RL-5.01.
Compositions act on a common smooth domain, rather than asserting algebraic
laws for totalized derivatives of arbitrary functions.
-/

@[expose] public noncomputable section
open Complex Finset
open scoped ContDiff
namespace Complex.CanonicalOperators

/-- Multiplication by the `j`th real coordinate, Rao–Lakshminarayanan (2.75)–(2.95). -/
def position {n : ℕ} (j : Fin n) (f : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) : ℂ :=
  (x j : ℂ) * f x

/-- The momentum `-i∂_j`, Rao–Lakshminarayanan (2.75)–(2.95), on its smooth domain. -/
def momentum {n : ℕ} (j : Fin n) (f : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) : ℂ :=
  -I * fderiv ℝ f x (Pi.single j 1)

/-- The defining position operator, Rao–Lakshminarayanan (2.75)–(2.95). -/
theorem position_def {n : ℕ} (j : Fin n) (f : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) :
    position j f x = (x j : ℂ) * f x := rfl

/-- The defining momentum operator, Rao–Lakshminarayanan (2.75)–(2.95). -/
theorem momentum_def {n : ℕ} (j : Fin n) (f : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) :
    momentum j f x = -I * fderiv ℝ f x (Pi.single j 1) := rfl

/-- The orientation tensor in three coordinates, Rao–Lakshminarayanan §5.1. -/
def orientation (i j k : Fin 3) : ℝ :=
  if (i, j, k) ∈ ({(0, 1, 2), (1, 2, 0), (2, 0, 1)} : Finset (Fin 3 × Fin 3 × Fin 3))
  then 1 else
    if (i, j, k) ∈ ({(0, 2, 1), (2, 1, 0), (1, 0, 2)} : Finset (Fin 3 × Fin 3 × Fin 3))
    then -1 else 0

/-- The defining orientation tensor, Rao–Lakshminarayanan §5.1. -/
theorem orientation_def (i j k : Fin 3) : orientation i j k =
    if (i, j, k) ∈ ({(0, 1, 2), (1, 2, 0), (2, 0, 1)} : Finset (Fin 3 × Fin 3 × Fin 3))
    then 1 else
      if (i, j, k) ∈ ({(0, 2, 1), (2, 1, 0), (1, 0, 2)} : Finset (Fin 3 × Fin 3 × Fin 3))
      then -1 else 0 := rfl

/-- Orbital angular momentum `L_j=Σ ε_jkl X_k p_l`, Rao–Lakshminarayanan
(2.75)–(2.95), (5.1)–(5.25), RL-2.06/5.01. -/
def angularMomentum (j : Fin 3) (f : (Fin 3 → ℝ) → ℂ) (x : Fin 3 → ℝ) : ℂ :=
  ∑ k : Fin 3, ∑ l : Fin 3, (orientation j k l : ℂ) * position k (momentum l f) x

/-- The orbital Casimir, Rao–Lakshminarayanan (5.1)–(5.25). -/
def casimir (f : (Fin 3 → ℝ) → ℂ) (x : Fin 3 → ℝ) : ℂ :=
  ∑ j : Fin 3, angularMomentum j (angularMomentum j f) x

/-- The defining orbital angular momentum, Rao–Lakshminarayanan §5.1. -/
theorem angularMomentum_def (j : Fin 3) (f : (Fin 3 → ℝ) → ℂ) (x : Fin 3 → ℝ) :
    angularMomentum j f x =
      ∑ k : Fin 3, ∑ l : Fin 3, (orientation j k l : ℂ) * position k (momentum l f) x := rfl

/-- The defining sum of squares of orbital angular momenta, Rao–Lakshminarayanan §5.1. -/
theorem casimir_def (f : (Fin 3 → ℝ) → ℂ) (x : Fin 3 → ℝ) :
    casimir f x = ∑ j : Fin 3, angularMomentum j (angularMomentum j f) x := rfl

/-- The canonical position–momentum commutator on smooth functions,
Rao–Lakshminarayanan (2.75)–(2.95), synopsis RL-2.06. -/
theorem position_momentum_sub_momentum_position {n : ℕ}
    (f : (Fin n → ℝ) → ℂ) (hf : ContDiff ℝ ∞ f) (j k : Fin n) (x : Fin n → ℝ) :
    position j (momentum k f) x - momentum k (position j f) x =
      if j = k then I * f x else 0 := by
  sorry

/-- Coordinate multiplications commute, Rao–Lakshminarayanan §2.3, RL-2.06. -/
theorem position_position_comm {n : ℕ} (f : (Fin n → ℝ) → ℂ)
    (j k : Fin n) (x : Fin n → ℝ) :
    position j (position k f) x = position k (position j f) x := by
  simp only [position]
  ring

/-- Smooth momentum derivatives commute, Rao–Lakshminarayanan §2.3, RL-2.06. -/
theorem momentum_momentum_comm {n : ℕ} (f : (Fin n → ℝ) → ℂ)
    (hf : ContDiff ℝ ∞ f) (j k : Fin n) (x : Fin n → ℝ) :
    momentum j (momentum k f) x = momentum k (momentum j f) x := by
  sorry

/-- The orbital angular-momentum Lie commutator,
Rao–Lakshminarayanan (2.75)–(2.95), (5.1)–(5.25), RL-2.06/5.01. -/
theorem angularMomentum_commutator (f : (Fin 3 → ℝ) → ℂ) (hf : ContDiff ℝ ∞ f)
    (j k : Fin 3) (x : Fin 3 → ℝ) :
    angularMomentum j (angularMomentum k f) x - angularMomentum k (angularMomentum j f) x =
      I * ∑ l : Fin 3, (orientation j k l : ℂ) * angularMomentum l f x := by
  sorry

/-- The orbital Casimir commutes with every component,
Rao–Lakshminarayanan (2.75)–(2.95), (5.1)–(5.25), RL-2.06/5.01. -/
theorem casimir_angularMomentum_comm (f : (Fin 3 → ℝ) → ℂ) (hf : ContDiff ℝ ∞ f)
    (j : Fin 3) (x : Fin 3 → ℝ) :
    casimir (angularMomentum j f) x = angularMomentum j (casimir f) x := by
  sorry

end Complex.CanonicalOperators
