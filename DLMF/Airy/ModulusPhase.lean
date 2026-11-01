/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Airy.ModulusPhase.Representations
public import DLMF.Airy.ModulusPhase.Nicholson
public import DLMF.Airy.ModulusPhase.ReciprocalExpansions
public import DLMF.Airy.ModulusPhase.PhaseExpansions

/-!
# Airy modulus and phase (DLMF §9.8)

Modulus and phase of the Airy functions and their derivatives on the real line: definitions,
Bessel forms, differential equations, Nicholson integrals, monotonicity, and the asymptotic
expansions at `-∞` with signed error bounds.
-/
