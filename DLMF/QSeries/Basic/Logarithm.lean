/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-!
# The unscaled q-logarithm

Duverney, *An Introduction to Hypergeometric Functions*, Chapter 10, equation (10.30),
defines the unscaled q-logarithm by its convergent partial-fraction series.
-/

@[expose] public noncomputable section

namespace DLMF.QSeries

/-- Duverney's q-logarithm `L_q(z)=∑ q^k z/(1-q^k z)`, defined when `|q|<1`
and `z≠q⁻ᴺ`, and totalized by `tsum` elsewhere. Duverney (10.30), DU-10.08. -/
def qLogarithm (q z : ℂ) : ℂ := ∑' k : ℕ, q ^ k * z / (1 - q ^ k * z)

/-- Defining series for the unscaled q-logarithm. Duverney (10.30), DU-10.08. -/
theorem qLogarithm_def (q z : ℂ) :
    qLogarithm q z = ∑' k : ℕ, q ^ k * z / (1 - q ^ k * z) := rfl

end DLMF.QSeries
