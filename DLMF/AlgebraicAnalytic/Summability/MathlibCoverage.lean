/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import DLMF.AlgebraicAnalytic.Summability.Defs
public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# DLMF §1.15 results already in Mathlib

Checked pointers (`dlmf_upstream`) for DLMF §1.15. Mathlib's Abel limit theorem is stated for
`tsum` of a power series with convergent partial sums `∑_{i<n} a_i`, which is DLMF's
convergence of `∑ a_n`; the local `hasAbelSum_of_tendsto` (`Summability/Series.lean`) restates it
with `HasAbelSum`. Mathlib's Cesàro lemma is for averages of a convergent sequence. The project's
`MeasureTheory.tendsto_abel_of_tendsto_intervalIntegral` (`DLMFMathlib/Analysis/Integral/
Improper.lean`) is the one-sided analogue of §1.15(iv) for integrals over `(0, ∞)`.
-/

/- §1.15(ii): regularity of the Abel and Cesàro methods. -/
dlmf_upstream 1.15.E10 Complex.tendsto_tsum_powerSeries_nhdsWithin_lt
  "exact: Abel's theorem, ∑ a_n xⁿ → ∑ a_n as x → 1⁻ for a convergent series (complex terms)"
dlmf_upstream 1.15.E11 Real.tendsto_tsum_powerSeries_nhdsWithin_lt
  "special case: Abel's theorem for real terms"
dlmf_upstream 1.15.ii Filter.Tendsto.cesaro_smul
  "partial: averages of a convergent sequence converge to its limit ((C,1) regularity)"

/- §1.15(iii): Fourier coefficients. -/
dlmf_upstream 1.15.E19 fourierCoeffOn
  "different convention: Fourier coefficient on [a, b]; DLMF's F(n) is fourierCoeffOn on [0, 2π]"

/- §1.15(v): Poisson kernel of the half-plane. -/
dlmf_upstream 1.15.E34 integral_univ_inv_one_add_sq
  "special case: ∫ (1 + x²)⁻¹ dx = π, the case y = 1 of (1/2π) ∫ P(x, y) dx = 1"
