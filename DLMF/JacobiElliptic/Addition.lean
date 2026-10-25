/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.PeriodsPolesZeros
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Jacobian elliptic functions: addition theorems (DLMF §22.8)

The addition theorems 22.8.1–22.8.18 are stated pointwise for complex `u`, `v` where the
functions involved are finite (`jacobiRegulark`) and the printed denominator is nonzero; they
are admitted. The four-point identities 22.8.20–22.8.27 are admitted except 22.8.27, which follows
from Table 22.4.3.

**Correction.** DLMF 22.8.23 as printed (columns `sn cn, cn dn, cn, dn` with
`z₁ + z₂ + z₃ + z₄ = 2K`) fails numerically (e.g. `k = 0.6`, determinant `≈ -0.107 + 0.033i`).
Replacing the third column by `sn`, or the second by `sn dn`, gives true identities; both are
acquired (`jacobi_det_sum_two_K`, `jacobi_det_sum_two_K'`).
-/

@[expose] public section

open Complex DLMF.Elliptic
open scoped Real

noncomputable section

namespace DLMF.JacobiElliptic

/-- **Admitted.** DLMF 22.8.1: an addition theorem for `sn`, at points `u`, `v` where the functions
`·n` are finite (`jacobiRegulark .n`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E1]
theorem jacobiSnk_add {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .n u k) (hv : jacobiRegulark .n v k)
    (hden : (1 - k ^ 2 * jacobiSnk u k ^ 2 * jacobiSnk v k ^ 2) ≠ 0) :
    jacobiSnk (u + v) k =
      (jacobiSnk u k * jacobiCnk v k * jacobiDnk v k + jacobiSnk v k * jacobiCnk u k *
        jacobiDnk u k) / (1 - k ^ 2 * jacobiSnk u k ^ 2 * jacobiSnk v k ^ 2) := by
  sorry

/-- **Admitted.** DLMF 22.8.2: an addition theorem for `cn`, at points `u`, `v` where the functions
`·n` are finite (`jacobiRegulark .n`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E2]
theorem jacobiCnk_add {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .n u k) (hv : jacobiRegulark .n v k)
    (hden : (1 - k ^ 2 * jacobiSnk u k ^ 2 * jacobiSnk v k ^ 2) ≠ 0) :
    jacobiCnk (u + v) k =
      (jacobiCnk u k * jacobiCnk v k - jacobiSnk u k * jacobiDnk u k * jacobiSnk v k *
        jacobiDnk v k) / (1 - k ^ 2 * jacobiSnk u k ^ 2 * jacobiSnk v k ^ 2) := by
  sorry

/-- **Admitted.** DLMF 22.8.3: an addition theorem for `dn`, at points `u`, `v` where the functions
`·n` are finite (`jacobiRegulark .n`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E3]
theorem jacobiDnk_add {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .n u k) (hv : jacobiRegulark .n v k)
    (hden : (1 - k ^ 2 * jacobiSnk u k ^ 2 * jacobiSnk v k ^ 2) ≠ 0) :
    jacobiDnk (u + v) k =
      (jacobiDnk u k * jacobiDnk v k - k ^ 2 * jacobiSnk u k * jacobiCnk u k * jacobiSnk v k *
        jacobiCnk v k) / (1 - k ^ 2 * jacobiSnk u k ^ 2 * jacobiSnk v k ^ 2) := by
  sorry

/-- **Admitted.** DLMF 22.8.4: an addition theorem for `cd`, at points `u`, `v` where the functions
`·d` are finite (`jacobiRegulark .d`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E4]
theorem jacobiCdk_add {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .d u k) (hv : jacobiRegulark .d v k)
    (hden : (1 + k ^ 2 * jacobiComodulusk k ^ 2 * jacobiSdk u k ^ 2 * jacobiSdk v k ^ 2) ≠ 0) :
    jacobiCdk (u + v) k =
      (jacobiCdk u k * jacobiCdk v k - jacobiComodulusk k ^ 2 * jacobiSdk u k * jacobiNdk u k *
        jacobiSdk v k * jacobiNdk v k) / (1 + k ^ 2 * jacobiComodulusk k ^ 2 * jacobiSdk u k ^ 2 *
          jacobiSdk v k ^ 2) := by
  sorry

/-- **Admitted.** DLMF 22.8.5: an addition theorem for `sd`, at points `u`, `v` where the functions
`·d` are finite (`jacobiRegulark .d`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E5]
theorem jacobiSdk_add {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .d u k) (hv : jacobiRegulark .d v k)
    (hden : (1 + k ^ 2 * jacobiComodulusk k ^ 2 * jacobiSdk u k ^ 2 * jacobiSdk v k ^ 2) ≠ 0) :
    jacobiSdk (u + v) k =
      (jacobiSdk u k * jacobiCdk v k * jacobiNdk v k + jacobiSdk v k * jacobiCdk u k *
        jacobiNdk u k) / (1 + k ^ 2 * jacobiComodulusk k ^ 2 * jacobiSdk u k ^ 2 *
          jacobiSdk v k ^ 2) := by
  sorry

/-- **Admitted.** DLMF 22.8.6: an addition theorem for `nd`, at points `u`, `v` where the functions
`·d` are finite (`jacobiRegulark .d`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E6]
theorem jacobiNdk_add {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .d u k) (hv : jacobiRegulark .d v k)
    (hden : (1 + k ^ 2 * jacobiComodulusk k ^ 2 * jacobiSdk u k ^ 2 * jacobiSdk v k ^ 2) ≠ 0) :
    jacobiNdk (u + v) k =
      (jacobiNdk u k * jacobiNdk v k + k ^ 2 * jacobiSdk u k * jacobiCdk u k * jacobiSdk v k *
        jacobiCdk v k) / (1 + k ^ 2 * jacobiComodulusk k ^ 2 * jacobiSdk u k ^ 2 *
          jacobiSdk v k ^ 2) := by
  sorry

/-- **Admitted.** DLMF 22.8.7: an addition theorem for `dc`, at points `u`, `v` where the functions
`·c` are finite (`jacobiRegulark .c`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E7]
theorem jacobiDck_add {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .c u k) (hv : jacobiRegulark .c v k)
    (hden : (1 - jacobiComodulusk k ^ 2 * jacobiSck u k ^ 2 * jacobiSck v k ^ 2) ≠ 0) :
    jacobiDck (u + v) k =
      (jacobiDck u k * jacobiDck v k + jacobiComodulusk k ^ 2 * jacobiSck u k * jacobiNck u k *
        jacobiSck v k * jacobiNck v k) / (1 - jacobiComodulusk k ^ 2 * jacobiSck u k ^ 2 *
          jacobiSck v k ^ 2) := by
  sorry

/-- **Admitted.** DLMF 22.8.8: an addition theorem for `nc`, at points `u`, `v` where the functions
`·c` are finite (`jacobiRegulark .c`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E8]
theorem jacobiNck_add {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .c u k) (hv : jacobiRegulark .c v k)
    (hden : (1 - jacobiComodulusk k ^ 2 * jacobiSck u k ^ 2 * jacobiSck v k ^ 2) ≠ 0) :
    jacobiNck (u + v) k =
      (jacobiNck u k * jacobiNck v k + jacobiSck u k * jacobiDck u k * jacobiSck v k *
        jacobiDck v k) / (1 - jacobiComodulusk k ^ 2 * jacobiSck u k ^ 2 * jacobiSck v k ^ 2) := by
  sorry

/-- **Admitted.** DLMF 22.8.9: an addition theorem for `sc`, at points `u`, `v` where the functions
`·c` are finite (`jacobiRegulark .c`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E9]
theorem jacobiSck_add {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .c u k) (hv : jacobiRegulark .c v k)
    (hden : (1 - jacobiComodulusk k ^ 2 * jacobiSck u k ^ 2 * jacobiSck v k ^ 2) ≠ 0) :
    jacobiSck (u + v) k =
      (jacobiSck u k * jacobiDck v k * jacobiNck v k + jacobiSck v k * jacobiDck u k *
        jacobiNck u k) / (1 - jacobiComodulusk k ^ 2 * jacobiSck u k ^ 2 * jacobiSck v k ^ 2) := by
  sorry

/-- **Admitted.** DLMF 22.8.10: an addition theorem for `ns`, at points `u`, `v` where the functions
`·s` are finite (`jacobiRegulark .s`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E10]
theorem jacobiNsk_add {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .s u k) (hv : jacobiRegulark .s v k)
    (hden : (jacobiCsk v k ^ 2 - jacobiCsk u k ^ 2) ≠ 0) :
    jacobiNsk (u + v) k =
      (jacobiNsk u k * jacobiDsk v k * jacobiCsk v k - jacobiNsk v k * jacobiDsk u k *
        jacobiCsk u k) / (jacobiCsk v k ^ 2 - jacobiCsk u k ^ 2) := by
  sorry

/-- **Admitted.** DLMF 22.8.11: an addition theorem for `ds`, at points `u`, `v` where the functions
`·s` are finite (`jacobiRegulark .s`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E11]
theorem jacobiDsk_add {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .s u k) (hv : jacobiRegulark .s v k)
    (hden : (jacobiCsk v k ^ 2 - jacobiCsk u k ^ 2) ≠ 0) :
    jacobiDsk (u + v) k =
      (jacobiDsk u k * jacobiCsk v k * jacobiNsk v k - jacobiDsk v k * jacobiCsk u k *
        jacobiNsk u k) / (jacobiCsk v k ^ 2 - jacobiCsk u k ^ 2) := by
  sorry

/-- **Admitted.** DLMF 22.8.12: an addition theorem for `cs`, at points `u`, `v` where the functions
`·s` are finite (`jacobiRegulark .s`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E12]
theorem jacobiCsk_add {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .s u k) (hv : jacobiRegulark .s v k)
    (hden : (jacobiCsk v k ^ 2 - jacobiCsk u k ^ 2) ≠ 0) :
    jacobiCsk (u + v) k =
      (jacobiCsk u k * jacobiDsk v k * jacobiNsk v k - jacobiCsk v k * jacobiDsk u k *
        jacobiNsk u k) / (jacobiCsk v k ^ 2 - jacobiCsk u k ^ 2) := by
  sorry

/-- **Admitted.** DLMF 22.8.13: an addition theorem for `sn`, at points `u`, `v` where the functions
`·n` are finite (`jacobiRegulark .n`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E13]
theorem jacobiSnk_add_alt {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .n u k) (hv : jacobiRegulark .n v k)
    (hden : jacobiSnk u k * jacobiCnk v k * jacobiDnk v k -
      jacobiSnk v k * jacobiCnk u k * jacobiDnk u k ≠ 0) :
    jacobiSnk (u + v) k =
      (jacobiSnk u k ^ 2 - jacobiSnk v k ^ 2) / (jacobiSnk u k * jacobiCnk v k * jacobiDnk v k -
        jacobiSnk v k * jacobiCnk u k * jacobiDnk u k) := by
  sorry

/-- **Admitted.** DLMF 22.8.14: an addition theorem for `sn`, at points `u`, `v` where the functions
`·n` are finite (`jacobiRegulark .n`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E14]
theorem jacobiSnk_add_alt₂ {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .n u k) (hv : jacobiRegulark .n v k)
    (hden : jacobiCnk u k * jacobiCnk v k +
      jacobiSnk u k * jacobiDnk u k * jacobiSnk v k * jacobiDnk v k ≠ 0) :
    jacobiSnk (u + v) k =
      (jacobiSnk u k * jacobiCnk u k * jacobiDnk v k + jacobiSnk v k * jacobiCnk v k *
        jacobiDnk u k) / (jacobiCnk u k * jacobiCnk v k + jacobiSnk u k * jacobiDnk u k *
          jacobiSnk v k * jacobiDnk v k) := by
  sorry

/-- **Admitted.** DLMF 22.8.15: an addition theorem for `cn`, at points `u`, `v` where the functions
`·n` are finite (`jacobiRegulark .n`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E15]
theorem jacobiCnk_add_alt {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .n u k) (hv : jacobiRegulark .n v k)
    (hden : jacobiSnk u k * jacobiCnk v k * jacobiDnk v k -
      jacobiSnk v k * jacobiCnk u k * jacobiDnk u k ≠ 0) :
    jacobiCnk (u + v) k =
      (jacobiSnk u k * jacobiCnk u k * jacobiDnk v k - jacobiSnk v k * jacobiCnk v k *
        jacobiDnk u k) / (jacobiSnk u k * jacobiCnk v k * jacobiDnk v k - jacobiSnk v k *
          jacobiCnk u k * jacobiDnk u k) := by
  sorry

/-- **Admitted.** DLMF 22.8.16: an addition theorem for `cn`, at points `u`, `v` where the functions
`·n` are finite (`jacobiRegulark .n`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E16]
theorem jacobiCnk_add_alt₂ {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .n u k) (hv : jacobiRegulark .n v k)
    (hden : jacobiCnk u k * jacobiCnk v k +
      jacobiSnk u k * jacobiDnk u k * jacobiSnk v k * jacobiDnk v k ≠ 0) :
    jacobiCnk (u + v) k =
      (1 - jacobiSnk u k ^ 2 - jacobiSnk v k ^ 2 + k ^ 2 * jacobiSnk u k ^ 2 * jacobiSnk v k ^ 2) /
        (jacobiCnk u k * jacobiCnk v k + jacobiSnk u k * jacobiDnk u k * jacobiSnk v k *
          jacobiDnk v k) := by
  sorry

/-- **Admitted.** DLMF 22.8.17: an addition theorem for `dn`, at points `u`, `v` where the functions
`·n` are finite (`jacobiRegulark .n`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E17]
theorem jacobiDnk_add_alt {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .n u k) (hv : jacobiRegulark .n v k)
    (hden : jacobiSnk u k * jacobiCnk v k * jacobiDnk v k -
      jacobiSnk v k * jacobiCnk u k * jacobiDnk u k ≠ 0) :
    jacobiDnk (u + v) k =
      (jacobiSnk u k * jacobiCnk v k * jacobiDnk u k - jacobiSnk v k * jacobiCnk u k *
        jacobiDnk v k) / (jacobiSnk u k * jacobiCnk v k * jacobiDnk v k - jacobiSnk v k *
          jacobiCnk u k * jacobiDnk u k) := by
  sorry

/-- **Admitted.** DLMF 22.8.18: an addition theorem for `dn`, at points `u`, `v` where the functions
`·n` are finite (`jacobiRegulark .n`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E18]
theorem jacobiDnk_add_alt₂ {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .n u k) (hv : jacobiRegulark .n v k)
    (hden : jacobiCnk u k * jacobiCnk v k +
      jacobiSnk u k * jacobiDnk u k * jacobiSnk v k * jacobiDnk v k ≠ 0) :
    jacobiDnk (u + v) k =
      (jacobiCnk u k * jacobiDnk u k * jacobiCnk v k * jacobiDnk v k + jacobiComodulusk k ^ 2 *
        jacobiSnk u k * jacobiSnk v k) / (jacobiCnk u k * jacobiCnk v k + jacobiSnk u k *
          jacobiDnk u k * jacobiSnk v k * jacobiDnk v k) := by
  sorry


/-- **Admitted.** DLMF 22.8.19–22.8.20: if `z₁ + z₂ + z₃ + z₄ = 0` then
`det [sn zⱼ, cn zⱼ, dn zⱼ, 1] = 0` (at points where `sn, cn, dn` are finite). -/
@[dlmf 22.8.E19, dlmf 22.8.E20]
theorem jacobi_det_sum_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : Fin 4 → ℂ)
    (hz : z 0 + z 1 + z 2 + z 3 = 0) (hreg : ∀ j, jacobiRegulark .n (z j) k) :
    Matrix.det (Matrix.of fun i : Fin 4 =>
      ![jacobiSnk (z i) k, jacobiCnk (z i) k, jacobiDnk (z i) k, 1]) = 0 := by
  sorry

/-- **Admitted.** DLMF 22.8.21: if `z₁ + z₂ + z₃ + z₄ = 0` then
`k'² - k'²k² ∏ sn zⱼ + k² ∏ cn zⱼ - ∏ dn zⱼ = 0`. -/
@[dlmf 22.8.E19, dlmf 22.8.E21]
theorem jacobi_prod_sum_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : Fin 4 → ℂ)
    (hz : z 0 + z 1 + z 2 + z 3 = 0) (hreg : ∀ j, jacobiRegulark .n (z j) k) :
    jacobiComodulusk k ^ 2 - jacobiComodulusk k ^ 2 * k ^ 2 * ∏ j, jacobiSnk (z j) k +
      k ^ 2 * ∏ j, jacobiCnk (z j) k - ∏ j, jacobiDnk (z j) k = 0 := by
  sorry

/-- **Admitted, corrected.** DLMF 22.8.22–22.8.23 with the third column corrected to `sn`: if
`z₁ + z₂ + z₃ + z₄ = 2K` then `det [sn zⱼ cn zⱼ, cn zⱼ dn zⱼ, sn zⱼ, dn zⱼ] = 0`.
Corrected from the printed DLMF formula: with the printed third column `cn zⱼ` the determinant
is nonzero (≈ -0.107 + 0.033i at `k = 0.6`); with `sn zⱼ` it vanishes. -/
@[dlmf 22.8.E22,
  dlmf 22.8.E23 "corrected: printed third column cn z_j replaced by sn z_j"]
theorem jacobi_det_sum_two_K {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : Fin 4 → ℂ)
    (hz : z 0 + z 1 + z 2 + z 3 = 2 * compEllIntKk k) (hreg : ∀ j, jacobiRegulark .n (z j) k) :
    Matrix.det (Matrix.of fun i : Fin 4 =>
      ![jacobiSnk (z i) k * jacobiCnk (z i) k, jacobiCnk (z i) k * jacobiDnk (z i) k,
        jacobiSnk (z i) k, jacobiDnk (z i) k]) = 0 := by
  sorry

/-- **Admitted, corrected.** DLMF 22.8.22–22.8.23 with the second column corrected to
`sn zⱼ dn zⱼ`: if `z₁ + z₂ + z₃ + z₄ = 2K` then
`det [sn zⱼ cn zⱼ, sn zⱼ dn zⱼ, cn zⱼ, dn zⱼ] = 0`.
Corrected from the printed DLMF formula: the printed determinant (second column `cn zⱼ dn zⱼ`)
is nonzero numerically; with second column `sn zⱼ dn zⱼ` it vanishes (an alternative to
`jacobi_det_sum_two_K`). -/
@[dlmf 22.8.E22,
  dlmf 22.8.E23 "corrected: printed second column cn z_j dn z_j replaced by sn z_j dn z_j"]
theorem jacobi_det_sum_two_K' {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : Fin 4 → ℂ)
    (hz : z 0 + z 1 + z 2 + z 3 = 2 * compEllIntKk k) (hreg : ∀ j, jacobiRegulark .n (z j) k) :
    Matrix.det (Matrix.of fun i : Fin 4 =>
      ![jacobiSnk (z i) k * jacobiCnk (z i) k, jacobiSnk (z i) k * jacobiDnk (z i) k,
        jacobiCnk (z i) k, jacobiDnk (z i) k]) = 0 := by
  sorry

/-- The expression of DLMF 22.8.25 at `z₁`, with `z₂ = z₁ - 2K/3`, `z₃ = z₂ - 2K/3`. -/
def jacobiDnThreePointExpr (z k : ℂ) : ℂ :=
  let d₁ := jacobiDnk z k
  let d₂ := jacobiDnk (z - 2 * compEllIntKk k / 3) k
  let d₃ := jacobiDnk (z - 4 * compEllIntKk k / 3) k
  (d₂ + d₃) * (d₃ + d₁) * (d₁ + d₂) / (d₁ + d₂ + d₃)

/-- **Admitted.** DLMF 22.8.24–22.8.25: if `z₁ - z₂ = z₂ - z₃ = 2K/3` then
`(dn z₂ + dn z₃)(dn z₃ + dn z₁)(dn z₁ + dn z₂)/(dn z₁ + dn z₂ + dn z₃)` is independent of the
`zⱼ` (at points where the `dn zⱼ` are finite and the denominator is nonzero). -/
@[dlmf 22.8.E24, dlmf 22.8.E25]
theorem jacobiDnThreePointExpr_const {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    ∃ c : ℂ, ∀ z : ℂ, (∀ j : ℕ, jacobiRegulark .n (z - 2 * j * compEllIntKk k / 3) k) →
      jacobiDnk z k + jacobiDnk (z - 2 * compEllIntKk k / 3) k +
        jacobiDnk (z - 4 * compEllIntKk k / 3) k ≠ 0 →
      jacobiDnThreePointExpr z k = c := by
  sorry

/-- `dn(z + K) dn z = k'` where both are finite and `dn z ≠ 0` (from Table 22.4.3). -/
theorem jacobiDnk_add_K_mul {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : jacobiRegulark .n z k) (hd : jacobiRegulark .d z k) :
    jacobiDnk (z + compEllIntKk k) k * jacobiDnk z k = jacobiComodulusk k := by
  rw [(jacobiDnk_shift hk z).1, mul_assoc]
  have hdn : jacobiDnk z k ≠ 0 := by
    unfold jacobiDnk jacobiPQk jacobiGlaisher
    simp only [reduceCtorEq, ↓reduceIte]
    exact div_ne_zero hd hn
  rw [jacobiNdk, jacobiPQk_eq_one_div, ← jacobiDnk, one_div_mul_cancel hdn, mul_one]

/-- DLMF 22.8.26–22.8.27: if `z₁ - z₂ = z₂ - z₃ = z₃ - z₄ = K/2` then
`dn z₁ dn z₃ = dn z₂ dn z₄ = k'` (at points `z₃`, `z₄` where `dn` is finite and nonzero). -/
@[dlmf 22.8.E26, dlmf 22.8.E27]
theorem jacobiDn_four_point {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z₁ z₂ z₃ z₄ : ℂ}
    (h₁ : z₁ - z₂ = compEllIntKk k / 2) (h₂ : z₂ - z₃ = compEllIntKk k / 2)
    (h₃ : z₃ - z₄ = compEllIntKk k / 2)
    (hn₃ : jacobiRegulark .n z₃ k) (hd₃ : jacobiRegulark .d z₃ k)
    (hn₄ : jacobiRegulark .n z₄ k) (hd₄ : jacobiRegulark .d z₄ k) :
    jacobiDnk z₁ k * jacobiDnk z₃ k = jacobiComodulusk k ∧
      jacobiDnk z₂ k * jacobiDnk z₄ k = jacobiComodulusk k := by
  have e₁ : z₁ = z₃ + compEllIntKk k := by linear_combination h₁ + h₂
  have e₂ : z₂ = z₄ + compEllIntKk k := by linear_combination h₂ + h₃
  exact ⟨e₁ ▸ jacobiDnk_add_K_mul hk hn₃ hd₃, e₂ ▸ jacobiDnk_add_K_mul hk hn₄ hd₄⟩

end DLMF.JacobiElliptic
