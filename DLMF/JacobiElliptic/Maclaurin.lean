/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Basic
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Maclaurin series of the Jacobian elliptic functions (DLMF §22.10)

* §22.10(i): the initial Maclaurin coefficients of `sn, cn, dn` in `z` (22.10.1–22.10.3), as
  `Asymptotics.IsBigO` statements at `z = 0`, for complex `k ∈ jacobiModulusDomain`; and the
  convergence of the full expansions in the disc `|z| < min(K, K')` (prose 22.10.i), stated for
  `0 < k < 1` as the existence of a power series on that ball.
* §22.10(ii): the expansions in `k` (22.10.4–22.10.6, `k → 0`) and in `k'`
  (22.10.7–22.10.9, `k → 1`), for fixed complex `z`, with `k` tending to its limit inside
  `jacobiModulusDomain`. In 22.10.7–22.10.9 `cosh z ≠ 0` is assumed (`sech z` appears).

All statements are admitted. The coefficients were checked numerically (mpmath, 2026-10-25),
also for complex `k`.
-/

@[expose] public section

open Complex Asymptotics Filter
open scoped Topology

noncomputable section

namespace DLMF.JacobiElliptic

variable {k : ℂ}

/-! ### §22.10(i): Maclaurin series in `z` -/

/-- DLMF 22.10.1: `sn(z,k) = z - (1 + k²) z³/3! + (1 + 14k² + k⁴) z⁵/5!
- (1 + 135k² + 135k⁴ + k⁶) z⁷/7! + O(z⁹)`. Admitted. -/
@[dlmf 22.10.E1 "domain: k ∈ jacobiModulusDomain"]
theorem jacobiSnk_isBigO_maclaurin (hk : k ∈ jacobiModulusDomain) :
    (fun z => jacobiSnk z k - (z - (1 + k ^ 2) * z ^ 3 / 6 + (1 + 14 * k ^ 2 + k ^ 4) * z ^ 5 /
        120 -
      (1 + 135 * k ^ 2 + 135 * k ^ 4 + k ^ 6) * z ^ 7 / 5040)) =O[𝓝 0] fun z => z ^ 9 := by
  sorry

/-- DLMF 22.10.2: `cn(z,k) = 1 - z²/2! + (1 + 4k²) z⁴/4! - (1 + 44k² + 16k⁴) z⁶/6! + O(z⁸)`.
Admitted. -/
@[dlmf 22.10.E2 "domain: k ∈ jacobiModulusDomain"]
theorem jacobiCnk_isBigO_maclaurin (hk : k ∈ jacobiModulusDomain) :
    (fun z => jacobiCnk z k - (1 - z ^ 2 / 2 + (1 + 4 * k ^ 2) * z ^ 4 / 24 -
      (1 + 44 * k ^ 2 + 16 * k ^ 4) * z ^ 6 / 720)) =O[𝓝 0] fun z => z ^ 8 := by
  sorry

/-- DLMF 22.10.3: `dn(z,k) = 1 - k² z²/2! + k²(4 + k²) z⁴/4! - k²(16 + 44k² + k⁴) z⁶/6! + O(z⁸)`.
Admitted. -/
@[dlmf 22.10.E3 "domain: k ∈ jacobiModulusDomain"]
theorem jacobiDnk_isBigO_maclaurin (hk : k ∈ jacobiModulusDomain) :
    (fun z => jacobiDnk z k - (1 - k ^ 2 * z ^ 2 / 2 + k ^ 2 * (4 + k ^ 2) * z ^ 4 / 24 -
      k ^ 2 * (16 + 44 * k ^ 2 + k ^ 4) * z ^ 6 / 720)) =O[𝓝 0] fun z => z ^ 8 := by
  sorry

/-- DLMF §22.10(i), prose: the full Maclaurin expansions of `sn, cn, dn` converge for
`|z| < min(K, K')`; stated for `0 < k < 1` as power series on the ball of that radius
(`K = K(k²)`, `K' = K(1 - k²)`). Admitted. -/
@[dlmf 22.10.i "special case: 0 < k < 1"]
theorem jacobi_hasFPowerSeriesOnBall {κ : ℝ} (hk0 : 0 < κ) (hk1 : κ < 1) :
    let r := ENNReal.ofReal (min (DLMF.Elliptic.Real.compEllIntKm (κ ^ 2))
      (DLMF.Elliptic.Real.compEllIntKm (1 - κ ^ 2)))
    (∃ p : FormalMultilinearSeries ℂ ℂ ℂ, HasFPowerSeriesOnBall (fun z => jacobiSnk z κ) p 0 r) ∧
      (∃ p : FormalMultilinearSeries ℂ ℂ ℂ,
        HasFPowerSeriesOnBall (fun z => jacobiCnk z κ) p 0 r) ∧
      ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, HasFPowerSeriesOnBall (fun z => jacobiDnk z κ) p 0 r :=
          by
  sorry

/-! ### §22.10(ii): Maclaurin series in `k` and `k'` -/

/-- DLMF 22.10.4: `sn(z,k) = sin z - k²(z - sin z cos z) cos z/4 + O(k⁴)` as `k → 0` in
`jacobiModulusDomain`, for fixed complex `z`. Admitted. -/
@[dlmf 22.10.E4 "domain: k → 0 within jacobiModulusDomain, fixed z"]
theorem jacobiSnk_isBigO_small_modulus (z : ℂ) :
    (fun k => jacobiSnk z k - (sin z - k ^ 2 / 4 * (z - sin z * cos z) * cos z))
      =O[𝓝[jacobiModulusDomain] 0] fun k => k ^ 4 := by
  sorry

/-- DLMF 22.10.5: `cn(z,k) = cos z + k²(z - sin z cos z) sin z/4 + O(k⁴)` as `k → 0`.
Admitted. -/
@[dlmf 22.10.E5 "domain: k → 0 within jacobiModulusDomain, fixed z"]
theorem jacobiCnk_isBigO_small_modulus (z : ℂ) :
    (fun k => jacobiCnk z k - (cos z + k ^ 2 / 4 * (z - sin z * cos z) * sin z))
      =O[𝓝[jacobiModulusDomain] 0] fun k => k ^ 4 := by
  sorry

/-- DLMF 22.10.6: `dn(z,k) = 1 - k² sin² z/2 + O(k⁴)` as `k → 0`. Admitted. -/
@[dlmf 22.10.E6 "domain: k → 0 within jacobiModulusDomain, fixed z"]
theorem jacobiDnk_isBigO_small_modulus (z : ℂ) :
    (fun k => jacobiDnk z k - (1 - k ^ 2 / 2 * sin z ^ 2))
      =O[𝓝[jacobiModulusDomain] 0] fun k => k ^ 4 := by
  sorry

/-- DLMF 22.10.7: `sn(z,k) = tanh z - k'²(z - sinh z cosh z) sech² z/4 + O(k'⁴)` as `k → 1`
in `jacobiModulusDomain`, for fixed `z` with `cosh z ≠ 0`. Admitted. -/
@[dlmf 22.10.E7 "domain: k → 1 within jacobiModulusDomain, fixed z with cosh z ≠ 0"]
theorem jacobiSnk_isBigO_small_comodulus {z : ℂ} (hz : cosh z ≠ 0) :
    (fun k => jacobiSnk z k - (tanh z - jacobiComodulusk k ^ 2 / 4 * (z - sinh z * cosh z) /
      cosh z ^ 2)) =O[𝓝[jacobiModulusDomain] 1] fun k => jacobiComodulusk k ^ 4 := by
  sorry

/-- DLMF 22.10.8: `cn(z,k) = sech z + k'²(z - sinh z cosh z) tanh z sech z/4 + O(k'⁴)` as
`k → 1`, `cosh z ≠ 0`. Admitted. -/
@[dlmf 22.10.E8 "domain: k → 1 within jacobiModulusDomain, fixed z with cosh z ≠ 0"]
theorem jacobiCnk_isBigO_small_comodulus {z : ℂ} (hz : cosh z ≠ 0) :
    (fun k => jacobiCnk z k - (1 / cosh z + jacobiComodulusk k ^ 2 / 4 *
      (z - sinh z * cosh z) * tanh z / cosh z))
      =O[𝓝[jacobiModulusDomain] 1] fun k => jacobiComodulusk k ^ 4 := by
  sorry

/-- DLMF 22.10.9: `dn(z,k) = sech z + k'²(z + sinh z cosh z) tanh z sech z/4 + O(k'⁴)` as
`k → 1`, `cosh z ≠ 0`. Admitted. -/
@[dlmf 22.10.E9 "domain: k → 1 within jacobiModulusDomain, fixed z with cosh z ≠ 0"]
theorem jacobiDnk_isBigO_small_comodulus {z : ℂ} (hz : cosh z ≠ 0) :
    (fun k => jacobiDnk z k - (1 / cosh z + jacobiComodulusk k ^ 2 / 4 *
      (z + sinh z * cosh z) * tanh z / cosh z))
      =O[𝓝[jacobiModulusDomain] 1] fun k => jacobiComodulusk k ^ 4 := by
  sorry

end DLMF.JacobiElliptic
