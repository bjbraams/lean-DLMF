/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Upstream
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# DLMF Chapter 21 coverage already available in Mathlib

Mathlib has no multidimensional theta function and no Siegel upper half-space; neither does
TauCeti. It does have the symplectic group with its determinant theorem, positive definite
matrices, and the genus-one theta function `jacobiTheta₂ z τ = ∑ₙ exp(2πinz + πin²τ)`, which
is exactly DLMF's `θ(z|τ)` (21.2.1) for `g = 1`. The pointers below record the genus-one
special cases and the linear-algebra input. Mathlib's symplectic form is
`Matrix.J = [[0, -I], [I, 0]] = -J_{2g}`; both define the same group
(`DLMF.RiemannTheta.isSymplectic_iff_mem_symplecticGroup`).
-/

dlmf_upstream 21.1 Matrix.PosDef
  "partial: positive definiteness of Im Ω in the definition of a Riemann matrix"

dlmf_upstream 21.1 Matrix.J "different convention: Mathlib's J is -J_{2g} of DLMF"

dlmf_upstream 21.2.E1 jacobiTheta₂
  "special case g = 1: jacobiTheta₂ z τ = θ(z|τ); see DLMF.RiemannTheta.rth21_riemannTheta_fin_one'"

dlmf_upstream 21.2.i hasSum_jacobiTheta₂_term "special case g = 1: convergence for 0 < Im τ"

dlmf_upstream 21.2.i differentiableAt_jacobiTheta₂_fst "special case g = 1: analytic in z"

dlmf_upstream 21.2.i differentiableAt_jacobiTheta₂_snd "special case g = 1: analytic in τ"

dlmf_upstream 21.3.E1 jacobiTheta₂_neg_left "special case g = 1"

dlmf_upstream 21.3.E2 jacobiTheta₂_add_left "special case g = 1, m₁ = 1"

dlmf_upstream 21.3.E3 jacobiTheta₂_add_left'
  "special case g = 1, m₁ = 0, m₂ = 1: θ(z+τ|τ) = exp(-πi(τ+2z)) θ(z|τ)"

dlmf_upstream 21.5.E2 Matrix.symplecticGroup
  "different convention: Mathlib's J is -J_{2g}; the same group of matrices"

dlmf_upstream 21.5.E3 SymplecticGroup.det_eq_one
  "exact after the bridge DLMF.RiemannTheta.isSymplectic_iff_mem_symplecticGroup"

dlmf_upstream 21.5.E6 jacobiTheta₂_add_right "special case g = 1, B = 2"

dlmf_upstream 21.5.E8 jacobiTheta₂_functional_equation
  "special case g = 1, principal square root; see DLMF.RiemannTheta.riemannTheta_inversion_fin_one"
