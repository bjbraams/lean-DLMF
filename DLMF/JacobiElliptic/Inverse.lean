/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Related
public import DLMF.Elliptic.SpecialValues

/-!
# Inverse Jacobian elliptic functions (DLMF §22.15)

For real variables and real parameter `m = k² < 1` (`k'² = 1 - m`):

* `arcsn(x, k)` is the existing `DLMF.Elliptic.Real.jacobiArcsnm x m = F(arcsin x | m)`
  (`DLMF.Elliptic.SpecialValues`), with `sn(arcsn x) = x` (`Real.jacobiSnm_jacobiArcsnm`).
* `Real.jacobiArccnm x m = F(arccos x | m)` and
  `Real.jacobiArcdnm x m = F(arcsin √((1 - x²)/m) | m)` are the solutions of 22.15.2–22.15.3 in
  the principal ranges 22.15.6–22.15.7; their inverse properties and ranges are proved.
* The other nine inverse functions are *defined* by DLMF's integral representations
  22.15.15–22.15.23 (on DLMF's ranges of `x`; outside them the integrals are Lean's totalized
  values); that they invert `cd, sd, …, cs` is admitted.

The representations 22.15.12 (and so 22.15.11, proved for `-K ≤ x ≤ K`, stronger than DLMF's
`-1 ≤ x ≤ 1`) are proved; 22.15.13–22.15.14 and the general solutions 22.15.8–22.15.10 are
admitted.
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

/-- DLMF 22.15.8: the general real solution of `sn(ξ, k) = x`, `-1 ≤ x ≤ 1`, is
`ξ = (-1)ᵐ arcsn(x, k) + 2mK`, `m ∈ ℤ`. Admitted. -/
@[dlmf 22.15.E8 "special case: real parameter k² < 1"]
theorem Real.jacobiSnm_eq_iff (hm : m < 1) {x ξ : ℝ} (hx0 : -1 ≤ x) (hx1 : x ≤ 1) :
    Real.jacobiSnm ξ m = x ↔
      ∃ n : ℤ, ξ = (-1) ^ n * Real.jacobiArcsnm x m + 2 * n * Real.compEllIntKm m := by
  sorry

/-- DLMF 22.15.9: the general real solution of `cn(η, k) = x`, `-1 ≤ x ≤ 1`, is
`η = ± arccn(x, k) + 4mK`, `m ∈ ℤ`. Admitted. -/
@[dlmf 22.15.E9 "special case: real parameter k² < 1"]
theorem Real.jacobiCnm_eq_iff (hm : m < 1) {x η : ℝ} (hx0 : -1 ≤ x) (hx1 : x ≤ 1) :
    Real.jacobiCnm η m = x ↔ ∃ n : ℤ, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      η = σ * Real.jacobiArccnm x m + 4 * n * Real.compEllIntKm m := by
  sorry

/-- DLMF 22.15.10: the general real solution of `dn(ζ, k) = x`, `k' ≤ x ≤ 1`, is
`ζ = ± arcdn(x, k) + 2mK`, `m ∈ ℤ` (`0 < k² < 1`). Admitted. -/
@[dlmf 22.15.E10 "special case: real parameter 0 < k² < 1"]
theorem Real.jacobiDnm_eq_iff (hm0 : 0 < m) (hm : m < 1) {x ζ : ℝ} (hx0 : √(1 - m) ≤ x)
    (hx1 : x ≤ 1) :
    Real.jacobiDnm ζ m = x ↔ ∃ n : ℤ, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ζ = σ * Real.jacobiArcdnm x m + 2 * n * Real.compEllIntKm m := by
  sorry

end Principal

/-! ### §22.15(ii): integral representations -/

section Integrals

variable {m : ℝ}

/-- DLMF 22.15.12: `arcsn(x, k) = ∫₀ˣ dt/√((1 - t²)(1 - k²t²))` for `-1 ≤ x ≤ 1`. -/
@[dlmf 22.15.E12 "special case: real parameter m = k² < 1"]
theorem Real.jacobiArcsnm_eq_integral (hm : m < 1) {x : ℝ} (hx0 : -1 ≤ x) (hx1 : x ≤ 1) :
    Real.jacobiArcsnm x m = ∫ t in (0 : ℝ)..x, 1 / √((1 - t ^ 2) * (1 - m * t ^ 2)) := by
  rcases le_total 0 x with hx | hx
  · rw [Real.integral_recip_sqrt_eq_incEllIntFm hm hx hx1, Real.jacobiArcsnm]
  · have h := Real.integral_recip_sqrt_eq_incEllIntFm hm (neg_nonneg.mpr hx) (by linarith)
    rw [Real.arcsin_neg, Real.incEllIntFm_neg] at h
    have hneg : (∫ t in (0 : ℝ)..x, 1 / √((1 - t ^ 2) * (1 - m * t ^ 2))) =
        -∫ t in (0 : ℝ)..-x, 1 / √((1 - t ^ 2) * (1 - m * t ^ 2)) := by
      have hc := intervalIntegral.integral_comp_neg (a := 0) (b := -x)
        (fun t => 1 / √((1 - t ^ 2) * (1 - m * t ^ 2)))
      simp only [neg_sq, neg_neg, neg_zero] at hc
      rw [hc, intervalIntegral.integral_symm x 0]
    rw [hneg, h, neg_neg, Real.jacobiArcsnm]

/-- DLMF 22.15.11: `x = ∫₀^{sn(x,k)} dt/√((1 - t²)(1 - k²t²))`; proved for `-K ≤ x ≤ K`
(stronger than DLMF's `-1 ≤ x ≤ 1`, since `K ≥ π/2 > 1`). -/
@[dlmf 22.15.E11 "stronger than DLMF: -K ≤ x ≤ K; real parameter m = k² < 1"]
theorem Real.eq_integral_jacobiSnm (hm : m < 1) {x : ℝ} (hx : |x| ≤ Real.compEllIntKm m) :
    x = ∫ t in (0 : ℝ)..Real.jacobiSnm x m, 1 / √((1 - t ^ 2) * (1 - m * t ^ 2)) := by
  have hs := (je22b_abs_le_one (m := m) x).1
  rw [← Real.jacobiArcsnm_eq_integral hm (neg_le_of_abs_le hs) (le_of_abs_le hs),
    Real.jacobiArcsnm_jacobiSnm hm hx]

/-- DLMF 22.15.13: `arccn(x, k) = ∫ₓ¹ dt/√((1 - t²)(k'² + k²t²))` for `-1 ≤ x ≤ 1`. Admitted. -/
@[dlmf 22.15.E13 "special case: real parameter m = k² < 1"]
theorem Real.jacobiArccnm_eq_integral (hm : m < 1) {x : ℝ} (hx0 : -1 ≤ x) (hx1 : x ≤ 1) :
    Real.jacobiArccnm x m = ∫ t in x..1, 1 / √((1 - t ^ 2) * ((1 - m) + m * t ^ 2)) := by
  sorry

/-- DLMF 22.15.14: `arcdn(x, k) = ∫ₓ¹ dt/√((1 - t²)(t² - k'²))` for `k' ≤ x ≤ 1`. Admitted. -/
@[dlmf 22.15.E14 "special case: real parameter 0 < m = k² < 1"]
theorem Real.jacobiArcdnm_eq_integral (hm0 : 0 < m) (hm : m < 1) {x : ℝ} (hx0 : √(1 - m) ≤ x)
    (hx1 : x ≤ 1) :
    Real.jacobiArcdnm x m = ∫ t in x..1, 1 / √((1 - t ^ 2) * (t ^ 2 - (1 - m))) := by
  sorry

/-- DLMF 22.15.15: `arccd` inverts `cd`: `cd(arccd(x,k), k) = x` for `-1 ≤ x ≤ 1`. Admitted. -/
@[dlmf 22.15.E15 "special case: real parameter m = k² < 1"]
theorem Real.jacobiCdm_jacobiArccdm (hm : m < 1) {x : ℝ} (hx0 : -1 ≤ x) (hx1 : x ≤ 1) :
    Real.jacobiCnm (Real.jacobiArccdm x m) m / Real.jacobiDnm (Real.jacobiArccdm x m) m = x := by
  sorry

/-- DLMF 22.15.16: `arcsd` inverts `sd` for `-1/k' ≤ x ≤ 1/k'`. Admitted. -/
@[dlmf 22.15.E16 "special case: real parameter m = k² < 1"]
theorem Real.jacobiSdm_jacobiArcsdm (hm : m < 1) {x : ℝ} (hx : |x| ≤ 1 / √(1 - m)) :
    Real.jacobiSnm (Real.jacobiArcsdm x m) m / Real.jacobiDnm (Real.jacobiArcsdm x m) m = x := by
  sorry

/-- DLMF 22.15.17: `arcnd` inverts `nd` for `1 ≤ x ≤ 1/k'`. Admitted. -/
@[dlmf 22.15.E17 "special case: real parameter m = k² < 1"]
theorem Real.jacobiNdm_jacobiArcndm (hm : m < 1) {x : ℝ} (hx0 : 1 ≤ x) (hx1 : x ≤ 1 / √(1 - m)) :
    1 / Real.jacobiDnm (Real.jacobiArcndm x m) m = x := by
  sorry

/-- DLMF 22.15.18: `arcdc` inverts `dc` for `1 ≤ x < ∞`. Admitted. -/
@[dlmf 22.15.E18 "special case: real parameter 0 ≤ m = k² < 1"]
theorem Real.jacobiDcm_jacobiArcdcm (hm0 : 0 ≤ m) (hm : m < 1) {x : ℝ} (hx : 1 ≤ x) :
    Real.jacobiDnm (Real.jacobiArcdcm x m) m / Real.jacobiCnm (Real.jacobiArcdcm x m) m = x := by
  sorry

/-- DLMF 22.15.19: `arcnc` inverts `nc` for `1 ≤ x < ∞`. Admitted. -/
@[dlmf 22.15.E19 "special case: real parameter 0 ≤ m = k² < 1"]
theorem Real.jacobiNcm_jacobiArcncm (hm0 : 0 ≤ m) (hm : m < 1) {x : ℝ} (hx : 1 ≤ x) :
    1 / Real.jacobiCnm (Real.jacobiArcncm x m) m = x := by
  sorry

/-- DLMF 22.15.20: `arcsc` inverts `sc` on `ℝ`. Admitted. -/
@[dlmf 22.15.E20 "special case: real parameter 0 ≤ m = k² < 1"]
theorem Real.jacobiScm_jacobiArcscm (hm0 : 0 ≤ m) (hm : m < 1) (x : ℝ) :
    Real.jacobiSnm (Real.jacobiArcscm x m) m / Real.jacobiCnm (Real.jacobiArcscm x m) m = x := by
  sorry

/-- DLMF 22.15.21: `arcns` inverts `ns` for `1 ≤ x < ∞`. Admitted. -/
@[dlmf 22.15.E21 "special case: real parameter 0 ≤ m = k² < 1"]
theorem Real.jacobiNsm_jacobiArcnsm (hm0 : 0 ≤ m) (hm : m < 1) {x : ℝ} (hx : 1 ≤ x) :
    1 / Real.jacobiSnm (Real.jacobiArcnsm x m) m = x := by
  sorry

/-- DLMF 22.15.22: `arcds` inverts `ds` for `k' ≤ x < ∞` (`0 < m`). Admitted. -/
@[dlmf 22.15.E22 "special case: real parameter 0 < m = k² < 1"]
theorem Real.jacobiDsm_jacobiArcdsm (hm0 : 0 < m) (hm : m < 1) {x : ℝ} (hx : √(1 - m) ≤ x) :
    Real.jacobiDnm (Real.jacobiArcdsm x m) m / Real.jacobiSnm (Real.jacobiArcdsm x m) m = x := by
  sorry

/-- DLMF 22.15.23: `arccs` inverts `cs` on `ℝ`. Admitted. -/
@[dlmf 22.15.E23 "special case: real parameter 0 ≤ m = k² < 1"]
theorem Real.jacobiCsm_jacobiArccsm (hm0 : 0 ≤ m) (hm : m < 1) (x : ℝ) :
    Real.jacobiCnm (Real.jacobiArccsm x m) m / Real.jacobiSnm (Real.jacobiArccsm x m) m = x := by
  sorry

end Integrals

end DLMF.JacobiElliptic
