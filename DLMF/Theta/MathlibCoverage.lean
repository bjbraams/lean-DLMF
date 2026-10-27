/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# DLMF Chapter 20 results already in Mathlib

Checked pointers to Mathlib declarations for DLMF Chapter 20. Mathlib's
`jacobiTheta₂ z τ = ∑ₙ exp(2πinz + πin²τ)` is `θ₃(πz|τ)` and `jacobiTheta τ = θ₃(0|τ)`; the
argument is scaled by `π` relative to DLMF, the series is totalized to `0` for `Im τ ≤ 0`. The
project's `θ₁, …, θ₄` (`DLMF.Elliptic.jacobiThetaOneTau …`) are defined from `jacobiTheta₂`
and their DLMF statements are tagged at the local declarations in `DLMF.Elliptic.Theta` and
`DLMF.Theta.*`. The pointer for `jacobiTheta₂` itself (20.2.3) is in
`DLMF.Elliptic.MathlibCoverage`.
-/

dlmf_upstream 20.2.E3 jacobiTheta_eq_jacobiTheta₂
  "special case z = 0: jacobiTheta τ = jacobiTheta₂ 0 τ = θ₃(0|τ)"

dlmf_upstream 20.2.E3 hasSum_nat_jacobiTheta
  "special case z = 0: θ₃(0|τ) = 1 + 2 Σ_{n≥1} q^{n²}, Im τ > 0"

dlmf_upstream 20.2.E8 jacobiTheta₂_add_left
  "special case m = 1, n = 0 in Mathlib's argument z/π: period π of θ₃"

dlmf_upstream 20.2.E8 jacobiTheta₂_add_left'
  "special case m = 0, n = 1 in Mathlib's argument z/π: θ₃(z + πτ|τ) = q⁻¹ e^{-2iz} θ₃(z|τ)"

dlmf_upstream 20.2.ii jacobiTheta₂_neg_left "θ₃ is even in z"

dlmf_upstream 20.2.ii differentiableAt_jacobiTheta₂_fst
  "θ₃(·|τ) is entire in z for Im τ > 0"

dlmf_upstream 20.2.ii differentiableAt_jacobiTheta₂_snd
  "θ₃(z|·) is analytic in τ on Im τ > 0"

dlmf_upstream 20.2.ii differentiableAt_jacobiTheta
  "θ₃(0|·) is analytic in τ on Im τ > 0"

dlmf_upstream 20.7.E28 jacobiTheta₂_add_right
  "partial: only the period 2 in τ, i.e. 20.7.28 followed by 20.7.29"

dlmf_upstream 20.7.E28 jacobiTheta_two_add
  "partial: θ₃(0|τ + 2) = θ₃(0|τ), i.e. 20.7.28 followed by 20.7.29 at z = 0"

dlmf_upstream 20.7.E32 jacobiTheta₂_functional_equation
  "exact in Mathlib's argument z/π: θ₃(z|τ) = (-iτ)^{-1/2} exp(iτ'z²/π) θ₃(zτ'|τ'); \
  principal square root; the local form is DLMF.Theta.jacobiThetaThreeTau_neg_inv"

dlmf_upstream 20.7.E32 jacobiTheta_S_smul
  "special case z = 0, τ ∈ ℍ: θ₃(0|-1/τ) = (-iτ)^{1/2} θ₃(0|τ)"
