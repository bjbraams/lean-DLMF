/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import Mathlib.Analysis.SpecialFunctions.Bessel

/-!
# DLMF Chapter 10 results already in Mathlib 4.35.0-rc2

The `dlmf_upstream` commands below are checked pointers to Mathlib declarations,
deliberately not duplicate local theorems. `J_ν` is Mathlib's `Complex.besselJ`, used
directly by the project; the project's `besselJ_eq_regularized` carries the `@[dlmf 10.2.E2]`
tag for the regularized `₀F₁` form.
-/

-- DLMF 10.2.2: Mathlib's definition of `J_ν`.
dlmf_upstream 10.2.E2 Complex.besselJ
  "exact: (z/2)^ν (principal power) times the regularized ₀F₁(;ν+1;-z²/4), for all ν; at \
  z = 0 Mathlib's value uses the totalized 0^ν"

-- DLMF 10.4.1, first equality.
dlmf_upstream 10.4.E1 Complex.besselJ_neg_int
  "partial: J_{-n}(z) = (-1)^n J_n(z), n ∈ ℤ; Mathlib has no Y_ν"

-- DLMF 10.11.1 at integer order.
dlmf_upstream 10.11.E1 Complex.besselJ_int_neg
  "special case: integer order ν = n and m = ±1, i.e. J_n(-z) = (-1)^n J_n(z)"
