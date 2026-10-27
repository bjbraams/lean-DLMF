/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

/-!
# DLMF Chapter 23 coverage already available in Mathlib

Mathlib's `PeriodPair` is parametrized by the full periods `ω₁, ω₂` (DLMF's `2ω₁, 2ω₃`), and
`℘[L]`, `℘'[L]` are defined by the lattice sums 23.2.4 and its derivative. Its `G n` is the
lattice sum `∑' l, l⁻ⁿ` over all lattice points (the term `l = 0` contributes `0⁻ⁿ = 0`), so
`g₂ = 60 G 4` and `g₃ = 140 G 6` are exactly 23.3.1–23.3.2. Dedekind's `η` is
`ModularForm.eta` (`q^{1/24}`-form with `q = e^{2πiτ}`, i.e. DLMF's `e^{iπτ/12}`), and the
modular discriminant `ModularForm.discriminant = η²⁴` is the normalized form of 23.19.4.
-/

dlmf_upstream 23.2.E4 PeriodPair.weierstrassP
  "exact: ℘(z) = 1/z² + Σ' ((z-w)⁻² - w⁻²), written as one lattice sum (the w = 0 term is 1/z²)"

dlmf_upstream 23.2.E4 PeriodPair.hasSum_weierstrassP "exact: the lattice series 23.2.4 converges"

dlmf_upstream 23.2.E9 PeriodPair.weierstrassP_add_coe
  "exact: ℘(z + 2ω_j) = ℘(z); stated for every lattice vector"

dlmf_upstream 23.2.iii PeriodPair.periodic_weierstrassP "exact: ℘ is 𝕃-periodic"

dlmf_upstream 23.2.iii PeriodPair.periodic_derivWeierstrassP "exact: ℘' is 𝕃-periodic"

dlmf_upstream 23.2.ii PeriodPair.weierstrassP_neg "exact: ℘ is even"

dlmf_upstream 23.2.ii PeriodPair.derivWeierstrassP_neg "exact: ℘' is odd"

dlmf_upstream 23.2.ii PeriodPair.meromorphic_weierstrassP "exact: ℘ is meromorphic on ℂ"

dlmf_upstream 23.2.ii PeriodPair.analyticOnNhd_weierstrassP "exact: ℘ is analytic off 𝕃"

dlmf_upstream 23.2.ii PeriodPair.order_weierstrassP
  "exact: ℘ has a double pole at each lattice point"

dlmf_upstream 23.3.E1 PeriodPair.g₂ "exact: g₂ = 60 Σ' w⁻⁴"

dlmf_upstream 23.3.E2 PeriodPair.g₃ "exact: g₃ = 140 Σ' w⁻⁶"

dlmf_upstream 23.3.E10 PeriodPair.derivWeierstrassP_sq
  "exact: ℘'² = 4℘³ - g₂℘ - g₃ off the lattice"

dlmf_upstream 23.15.E3 UpperHalfPlane.coe_specialLinearGroup_apply
  "exact: the SL(2,ℤ) action on ℍ is τ ↦ (aτ+b)/(cτ+d)"

dlmf_upstream 23.15.E4 Matrix.SpecialLinearGroup "exact: SL(2,ℤ), integer matrices with ad - bc = 1"

dlmf_upstream 23.15.E9 ModularForm.eta
  "definition: η(τ) = e^{2πiτ/24} ∏ (1 - e^{2πi(n+1)τ}); equals DLMF 23.17.8"

dlmf_upstream 23.17.E8 ModularForm.eta
  "exact: q^{1/12} ∏ (1 - q^{2n}) with q = e^{iπτ}, q^{1/12} = e^{iπτ/12}"

dlmf_upstream 23.17.E8 ModularForm.eta_ne_zero "related: η has no zeros in ℍ"

dlmf_upstream 23.19.E4 ModularForm.discriminant
  "normalized: Mathlib's Δ(τ) = η(τ)²⁴, i.e. DLMF's Δ/(2π)¹² for the lattice 1, τ"

dlmf_upstream 23.19.E4 ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq
  "related: η²⁴ = (E₄³ - E₆²)/1728, the Eisenstein-series form of g₂³ - 27g₃²"
