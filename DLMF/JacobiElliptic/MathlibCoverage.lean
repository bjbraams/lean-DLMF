/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# DLMF Chapter 22 (§§22.2–22.9) and Mathlib

Mathlib (and the pinned TauCeti) have no Jacobian elliptic functions, no complete elliptic
integral of complex modulus and no Landen or cyclic identities (checked 2026-10-25). The only
upstream ingredient is the two-variable theta function, from which the project's `θ₁, …, θ₄`
and hence all twelve Jacobian functions of `DLMF.JacobiElliptic.Basic` are built. The limiting
forms of Tables 22.5.3–22.5.4 have Mathlib's elementary functions as their targets.
-/

-- DLMF 22.2.4–22.2.11: the theta quotients are built from Mathlib's `jacobiTheta₂`.
dlmf_upstream 22.2.E11 jacobiTheta₂
  "partial: ingredient only; jacobiTheta₂ z τ = θ₃(πz | τ), from which θ₁…θ₄ and the twelve \
  Jacobian functions are defined locally"

-- Tables 22.5.3–22.5.4: limiting values are Mathlib's trigonometric and hyperbolic functions.
dlmf_upstream 22.5.T3 Complex.sin "partial: target of sn, sd as k → 0"
dlmf_upstream 22.5.T4 Complex.tanh "partial: target of sn as k → 1"
