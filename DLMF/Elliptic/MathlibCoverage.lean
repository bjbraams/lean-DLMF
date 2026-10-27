/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import Mathlib.Analysis.SpecialFunctions.ArithmeticGeometricMean
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# DLMF Chapters 19–20 results already in Mathlib 4.35.0-rc2

The `dlmf_upstream` commands below are checked pointers to Mathlib declarations,
deliberately not duplicate local theorems. The project's `θ₁, …, θ₄` in DLMF normalization
are defined from `jacobiTheta₂` in `DLMF.Elliptic.Theta` and carry their own `@[dlmf]` tags.
-/

-- DLMF 19.8.1 and §19.8(i): Gauss's arithmetic-geometric mean.
dlmf_upstream 19.8.E1 NNReal.agmSequences
  "different convention: agmSequences x y n = (g_{n+1}, a_{n+1}) for a_0, g_0 = y, x ≥ 0 \
  (symmetric in x, y)"
dlmf_upstream 19.8.i NNReal.tendsto_agmSequences_snd_agm
  "special case: nonnegative real a_0, g_0; a_n → M(a_0, g_0) = NNReal.agm"
dlmf_upstream 19.8.i NNReal.tendsto_agmSequences_fst_agm
  "special case: nonnegative real a_0, g_0; g_n → M(a_0, g_0) = NNReal.agm"

-- DLMF 20.2.3: Mathlib's two-variable theta function is `θ₃` with argument scaled by `π`.
dlmf_upstream 20.2.E3 jacobiTheta₂
  "different convention: jacobiTheta₂ z τ = θ₃(πz | τ) = Σ_{n∈ℤ} q^{n²} e^{2πinz}, \
  q = e^{iπτ}, for Im τ > 0 (the tsum is totalized to 0 otherwise)"
