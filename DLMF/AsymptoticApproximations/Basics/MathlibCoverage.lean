/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import DLMF.AlgebraicAnalytic.Transforms.Defs
public import DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion
public import DLMFMathlib.Analysis.Asymptotics.AsymptoticInversion
public import DLMFMathlib.Analysis.Asymptotics.Watson
public import DLMFMathlib.Analysis.Asymptotics.WatsonSector
public import DLMFMathlib.Analysis.Asymptotics.WatsonRotated
public import ToMathlib.Analysis.Integral.Laplace
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.MellinInversion
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# DLMF §§2.1–2.5 results already upstream

Checked pointers (`dlmf_upstream`) from DLMF §§2.1–2.5 to Mathlib, lean-codes' `ToMathlib`, the
project's general library `DLMFMathlib`, and the Laplace transform of §1.14 in this project.

Conventions: Mathlib's `f ~[l] g` (`Asymptotics.IsEquivalent`) is `f - g = o(g)`, which agrees
with DLMF's `f/g → 1` (2.1.1) when `g` is eventually nonzero; `f =o[l] g` and `f =O[l] g` are
DLMF's `o` and `O` (2.1.2–2.1.3) without a division, so they also cover functions with zeros.
`HasAsymptoticExpansion l φ a f` (`DLMFMathlib`) is the generalized expansion of §2.1(v) with
coefficients `a` on a scale `φ`; the Poincaré expansions of §2.1(iii) are the scale `x^{-s}`
(`HasPoincareExpansion`, `Basics.Defs`).
-/

/- §2.1(i): order symbols. -/
dlmf_upstream 2.1.E1 Asymptotics.isEquivalent_iff_tendsto_one
  "different convention: f ~ g iff f/g → 1, when g is eventually nonzero"
dlmf_upstream 2.1.E2 Asymptotics.isLittleO_iff_tendsto'
  "different convention: f = o(g) iff f/g → 0, when g x = 0 → f x = 0 eventually"
dlmf_upstream 2.1.E3 Asymptotics.isBigO_iff_isBoundedUnder_le_div
  "different convention: f = O(g) iff |f/g| is bounded, when g is eventually nonzero"
dlmf_upstream 2.1.i Asymptotics.isBigO_top
  "exact: f = O(g) in a region (the filter ⊤): |f| ≤ C|g| everywhere"
dlmf_upstream 2.1.E10 Asymptotics.IsLittleO.isBigO
  "exact: o(φ) is O(φ)"
dlmf_upstream 2.1.E10 Asymptotics.IsBigO.add
  "exact: O(φ) + O(φ) = O(φ)"
dlmf_upstream 2.1.E10 Asymptotics.IsLittleO.add
  "exact: o(φ) + o(φ) = o(φ)"

/- §2.1(iii)–(v): asymptotic expansions. -/
dlmf_upstream 2.1.E8 HasFPowerSeriesAt.isBigO_sub_partialSum_pow
  "stronger: a convergent power series is an asymptotic expansion, f - partial sum = O(zⁿ)"
dlmf_upstream 2.1.iii Asymptotics.HasAsymptoticExpansion.unique
  "exact: uniqueness of the coefficients of an expansion on an asymptotic scale (DLMFMathlib)"
dlmf_upstream 2.1.iii Asymptotics.HasAsymptoticExpansion.add
  "exact: expansions can be added (DLMFMathlib)"
dlmf_upstream 2.1.E19 Asymptotics.IsAsymptoticScale
  "exact: φ_{s+1} = o(φ_s) (DLMFMathlib)"
dlmf_upstream 2.1.E20 Asymptotics.HasAsymptoticExpansion
  "special case: ∑ aₛ φₛ with constant aₛ (DLMFMathlib); see HasGeneralizedAsymptoticExpansion"

/- §2.2: reversion of asymptotic power series. -/
dlmf_upstream 2.2 Asymptotics.HasAsymptoticPowerSeries.inversion
  "stronger: reversion of an asymptotic power series w ∼ P(σ), P(0) = 0, P'(0) ≠ 0 (DLMFMathlib)"

/- §2.3–§2.4: Watson's lemma and Laplace's method. -/
dlmf_upstream 2.3.E1 DLMF.AlgebraicAnalytic.laplaceTransform
  "exact: the Laplace transform of §1.14 (DLMF 1.14.17)"
dlmf_upstream 2.3.E8 hasAsymptoticExpansion_integral_exp_smul
  "special case: Watson's lemma 2.3.8 with DLMF's μ = 1 (DLMFMathlib's μ is DLMF's λ)"
dlmf_upstream 2.3.E8 hasAsymptoticExpansion_integral_exp_smul_cpow
  "stronger: Watson's lemma with complex exponent μ, ℜμ > 0 (DLMFMathlib)"
dlmf_upstream 2.4.E1 hasAsymptoticExpansion_integral_cexp_smul_sector
  "exact: Watson's lemma in a sector |ph z| ≤ π/2 - δ (DLMFMathlib)"
dlmf_upstream 2.4.i hasAsymptoticExpansion_integral_cexp_smul_rotate
  "exact: Watson's lemma after rotation of the path of integration (DLMFMathlib)"
dlmf_upstream 2.3.iii Complex.isEquivalent_integral_laplace_Icc
  "special case: leading term of Laplace's method at an interior quadratic minimum (lean-codes)"

/- §2.5: Mellin transforms. -/
dlmf_upstream 2.5.E1 mellin
  "exact: 𝓜f(z) = ∫₀^∞ t^{z-1} f(t) dt"
dlmf_upstream 2.5.E2 mellinInv_mellin_eq
  "exact: Mellin inversion, (2πi)⁻¹ ∫_{(c)} t^{-z} 𝓜f(z) dz = f(t) at continuity points"
dlmf_upstream 2.5.i mellinConvergent_of_isBigO_rpow
  "exact: the strip of convergence a < ℜz < b from O-bounds at 0 and ∞"
dlmf_upstream 2.5.i mellin_differentiableAt_of_isBigO_rpow
  "exact: analyticity of 𝓜f in the strip of convergence"
dlmf_upstream 2.3.E6 eVariationOn
  "different convention: total variation as an extended real; 𝒱 of 2.3.6 is variationalOperator"
