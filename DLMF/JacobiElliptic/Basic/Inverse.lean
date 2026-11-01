/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elliptic.Basic.Jacobi

/-!
# Inverse Jacobian elliptic functions: definitions (DLMF §22.15)

The inverse Jacobian elliptic functions for real variables and real parameter `m = k² < 1`
(`k'² = 1 - m`): definitions, the inverse relations for `cn`, `dn` and the principal ranges
(DLMF §22.15(i)).

## Main definitions

* `Real.jacobiArccnm`, `Real.jacobiArcdnm`: `arccn(x, k) = F(arccos x | m)` and
  `arcdn(x, k) = F(arcsin √((1 - x²)/m) | m)`, the solutions of DLMF 22.15.2–22.15.3 in the
  principal ranges 22.15.6–22.15.7.
* `Real.jacobiArccdm`, `Real.jacobiArcsdm`, `Real.jacobiArcndm`, `Real.jacobiArcdcm`,
  `Real.jacobiArcncm`, `Real.jacobiArcscm`, `Real.jacobiArcnsm`, `Real.jacobiArcdsm`,
  `Real.jacobiArccsm`: the other inverse functions, defined by DLMF's integral representations
  22.15.15–22.15.23.

## Main results

* `Real.jacobiCnm_jacobiArccnm`, `Real.jacobiDnm_jacobiArcdnm`: DLMF 22.15.2–22.15.4.
* `Real.jacobiArcsnm_mem_Icc`, `Real.jacobiArccnm_mem_Icc`, `Real.jacobiArcdnm_mem_Icc`: the
  principal ranges DLMF 22.15.5–22.15.7.

## Implementation notes

`arcsn(x, k)` is `DLMF.Elliptic.Real.jacobiArcsnm x m = F(arcsin x | m)`, with
`sn(arcsn x) = x` (`Real.jacobiSnm_jacobiArcsnm`). Outside DLMF's ranges of `x` the integral
definitions take Lean's totalized values.
-/

@[expose] public section

open Real DLMF.Elliptic
open scoped Topology

noncomputable section

namespace DLMF.JacobiElliptic

/-! ### Definitions -/

/-- `arccn(x, k) = F(arccos x | k²)`: the solution `η ∈ [0, 2K]` of `cn(η, k) = x`,
`-1 ≤ x ≤ 1` (DLMF 22.15.2, 22.15.4, 22.15.6). -/
@[dlmf 22.15.E4]
def Real.jacobiArccnm (x m : ℝ) : ℝ := Real.incEllIntFm (Real.arccos x) m

/-- `arcdn(x, k) = F(arcsin √((1 - x²)/k²) | k²)`: the solution `ζ ∈ [0, K]` of `dn(ζ, k) = x`,
`k' ≤ x ≤ 1` (DLMF 22.15.3, 22.15.4, 22.15.7); meaningful for `0 < m < 1`. -/
@[dlmf 22.15.E4]
def Real.jacobiArcdnm (x m : ℝ) : ℝ := Real.incEllIntFm (Real.arcsin (√((1 - x ^ 2) / m))) m

/-- `arccd(x, k) = ∫ₓ¹ dt/√((1 - t²)(1 - k²t²))`, `-1 ≤ x ≤ 1` (DLMF 22.15.15). -/
@[dlmf 22.15.E15]
def Real.jacobiArccdm (x m : ℝ) : ℝ := ∫ t in x..1, 1 / √((1 - t ^ 2) * (1 - m * t ^ 2))

/-- `arcsd(x, k) = ∫₀ˣ dt/√((1 - k'²t²)(1 + k²t²))`, `-1/k' ≤ x ≤ 1/k'` (DLMF 22.15.16). -/
@[dlmf 22.15.E16]
def Real.jacobiArcsdm (x m : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, 1 / √((1 - (1 - m) * t ^ 2) * (1 + m * t ^ 2))

/-- `arcnd(x, k) = ∫₁ˣ dt/√((t² - 1)(1 - k'²t²))`, `1 ≤ x ≤ 1/k'` (DLMF 22.15.17). -/
@[dlmf 22.15.E17]
def Real.jacobiArcndm (x m : ℝ) : ℝ :=
  ∫ t in (1 : ℝ)..x, 1 / √((t ^ 2 - 1) * (1 - (1 - m) * t ^ 2))

/-- `arcdc(x, k) = ∫₁ˣ dt/√((t² - 1)(t² - k²))`, `1 ≤ x < ∞` (DLMF 22.15.18). -/
@[dlmf 22.15.E18]
def Real.jacobiArcdcm (x m : ℝ) : ℝ := ∫ t in (1 : ℝ)..x, 1 / √((t ^ 2 - 1) * (t ^ 2 - m))

/-- `arcnc(x, k) = ∫₁ˣ dt/√((t² - 1)(k² + k'²t²))`, `1 ≤ x < ∞` (DLMF 22.15.19). -/
@[dlmf 22.15.E19]
def Real.jacobiArcncm (x m : ℝ) : ℝ :=
  ∫ t in (1 : ℝ)..x, 1 / √((t ^ 2 - 1) * (m + (1 - m) * t ^ 2))

/-- `arcsc(x, k) = ∫₀ˣ dt/√((1 + t²)(1 + k'²t²))`, `x ∈ ℝ` (DLMF 22.15.20). -/
@[dlmf 22.15.E20]
def Real.jacobiArcscm (x m : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, 1 / √((1 + t ^ 2) * (1 + (1 - m) * t ^ 2))

/-- `arcns(x, k) = ∫ₓ^∞ dt/√((t² - 1)(t² - k²))`, `1 ≤ x < ∞` (DLMF 22.15.21). -/
@[dlmf 22.15.E21]
def Real.jacobiArcnsm (x m : ℝ) : ℝ := ∫ t in Set.Ioi x, 1 / √((t ^ 2 - 1) * (t ^ 2 - m))

/-- `arcds(x, k) = ∫ₓ^∞ dt/√((t² + k²)(t² - k'²))`, `k' ≤ x < ∞` (DLMF 22.15.22). -/
@[dlmf 22.15.E22]
def Real.jacobiArcdsm (x m : ℝ) : ℝ := ∫ t in Set.Ioi x, 1 / √((t ^ 2 + m) * (t ^ 2 - (1 - m)))

/-- `arccs(x, k) = ∫ₓ^∞ dt/√((1 + t²)(t² + k'²))`, `x ∈ ℝ` (DLMF 22.15.23). -/
@[dlmf 22.15.E23]
def Real.jacobiArccsm (x m : ℝ) : ℝ := ∫ t in Set.Ioi x, 1 / √((1 + t ^ 2) * (t ^ 2 + (1 - m)))

/-! ### §22.15(i): the principal inverses of `sn, cn, dn` -/

section Principal

variable {m : ℝ}

/-- DLMF 22.15.2/22.15.4: `cn(arccn(x, k), k) = x` for `-1 ≤ x ≤ 1`. -/
@[dlmf 22.15.E2 "special case: real parameter m = k² < 1"]
theorem Real.jacobiCnm_jacobiArccnm (hm : m < 1) {x : ℝ} (hx0 : -1 ≤ x) (hx1 : x ≤ 1) :
    Real.jacobiCnm (Real.jacobiArccnm x m) m = x := by
  rw [Real.jacobiCnm, Real.jacobiArccnm, Real.jacobiAmm_incEllIntFm hm, Real.cos_arccos hx0 hx1]

/-- DLMF 22.15.3/22.15.4: `dn(arcdn(x, k), k) = x` for `k' ≤ x ≤ 1`, `0 < k² < 1`. -/
@[dlmf 22.15.E3 "special case: real parameter 0 < m = k² < 1"]
theorem Real.jacobiDnm_jacobiArcdnm (hm0 : 0 < m) (hm : m < 1) {x : ℝ} (hx0 : √(1 - m) ≤ x)
    (hx1 : x ≤ 1) : Real.jacobiDnm (Real.jacobiArcdnm x m) m = x := by
  have hx : 0 ≤ x := le_trans (Real.sqrt_nonneg _) hx0
  have h1 : 1 - m ≤ x ^ 2 := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 1 - m by linarith)
    nlinarith [Real.sqrt_nonneg (1 - m)]
  have hq0 : 0 ≤ (1 - x ^ 2) / m := div_nonneg (by nlinarith) hm0.le
  have hq1 : (1 - x ^ 2) / m ≤ 1 := by rw [div_le_one hm0]; linarith
  have hs0 : 0 ≤ √((1 - x ^ 2) / m) := Real.sqrt_nonneg _
  have hs1 : √((1 - x ^ 2) / m) ≤ 1 := Real.sqrt_le_one.mpr hq1
  rw [Real.jacobiDnm, Real.jacobiSnm, Real.jacobiArcdnm, Real.jacobiAmm_incEllIntFm hm,
    Real.sin_arcsin (by linarith) hs1, Real.sq_sqrt hq0,
    show 1 - m * ((1 - x ^ 2) / m) = x ^ 2 by field_simp; ring, ← Real.sqrt_eq_rpow,
    Real.sqrt_sq hx]

/-- DLMF 22.15.5: `-K ≤ arcsn(x, k) ≤ K` for `-1 ≤ x ≤ 1`. -/
@[dlmf 22.15.E5 "special case: real parameter m = k² < 1"]
theorem Real.jacobiArcsnm_mem_Icc (hm : m < 1) (x : ℝ) :
    Real.jacobiArcsnm x m ∈ Set.Icc (-Real.compEllIntKm m) (Real.compEllIntKm m) := by
  have hmono := (Real.strictMono_incEllIntFm hm).monotone
  refine ⟨?_, ?_⟩
  · have := hmono (Real.neg_pi_div_two_le_arcsin x)
    dsimp only at this
    rw [Real.incEllIntFm_neg, Real.incEllIntFm_pi_div_two] at this
    exact this
  · have := hmono (Real.arcsin_le_pi_div_two x)
    dsimp only at this
    rw [Real.incEllIntFm_pi_div_two] at this
    exact this

/-- DLMF 22.15.6: `0 ≤ arccn(x, k) ≤ 2K`. -/
@[dlmf 22.15.E6 "special case: real parameter m = k² < 1"]
theorem Real.jacobiArccnm_mem_Icc (hm : m < 1) (x : ℝ) :
    Real.jacobiArccnm x m ∈ Set.Icc 0 (2 * Real.compEllIntKm m) := by
  have hmono := (Real.strictMono_incEllIntFm hm).monotone
  refine ⟨?_, ?_⟩
  · have := hmono (Real.arccos_nonneg x)
    simpa [Real.incEllIntFm, Real.jacobiArccnm] using this
  · have h := Real.incEllIntFm_add_pi hm 0
    rw [zero_add, show Real.incEllIntFm 0 m = 0 by simp [Real.incEllIntFm], zero_add] at h
    have := hmono (Real.arccos_le_pi x)
    dsimp only at this
    rw [h] at this
    exact this

/-- DLMF 22.15.7: `0 ≤ arcdn(x, k) ≤ K`. -/
@[dlmf 22.15.E7 "special case: real parameter m = k² < 1"]
theorem Real.jacobiArcdnm_mem_Icc (hm : m < 1) (x : ℝ) :
    Real.jacobiArcdnm x m ∈ Set.Icc 0 (Real.compEllIntKm m) := by
  have hmono := (Real.strictMono_incEllIntFm hm).monotone
  refine ⟨?_, ?_⟩
  · have := hmono (Real.arcsin_nonneg.mpr (Real.sqrt_nonneg ((1 - x ^ 2) / m)))
    simpa [Real.incEllIntFm, Real.jacobiArcdnm] using this
  · have := hmono (Real.arcsin_le_pi_div_two (√((1 - x ^ 2) / m)))
    dsimp only at this
    rw [Real.incEllIntFm_pi_div_two] at this
    exact this

end Principal

end DLMF.JacobiElliptic
