/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Basic

/-!
# Moduli outside the interval `[0, 1]` (DLMF §22.17)

* 22.17.1 `pq(z, -k) = pq(z, k)` is proved for all twelve functions and all complex `z, k`:
  the definition `jacobiPQk` depends on `k` only through `k²`.
* The reciprocal-modulus transformation 22.17.2–22.17.4 and the imaginary-modulus
  transformation 22.17.6–22.17.8 are stated for complex moduli with both moduli involved in
  `jacobiModulusDomain` (DLMF §22.17(ii): the functions are meromorphic in `k²`, so the
  identities persist for complex `k`). The real moduli `1/k > 1` and `ik` lie on the cut
  `[1, ∞)` or on the imaginary axis, where the literal definition `jacobiPQk` uses principal
  branches of `K'(k)` that are not the analytic continuation, so they are not covered here.
  These six statements are admitted; they were checked numerically for complex `k`
  (mpmath, 2026-10-25).
* 22.17.5: `k₁ = k/√(1 + k²)`, `k₁k₁' = k/(1 + k²)`, proved for real `k`.
-/

@[expose] public section

open Complex

noncomputable section

namespace DLMF.JacobiElliptic

/-- DLMF 22.17.1: `pq(z, -k) = pq(z, k)` for all twelve Glaisher functions (all letters
`p, q`), all complex `z` and `k`. -/
@[dlmf 22.17.E1 "stronger than DLMF: all complex z and k"]
theorem jacobiPQk_neg_modulus (p q : JacobiLetter) (z k : ℂ) :
    jacobiPQk p q z (-k) = jacobiPQk p q z k := by
  simp only [jacobiPQk, jacobiZetak, jacobiTauk, compEllIntKk, compEllIntKpk, neg_sq]

/-- DLMF 22.17.2: `sn(z, 1/k) = k sn(z/k, k)`, for complex `k` with `k, 1/k ∈ jacobiModulusDomain`.
Admitted. -/
@[dlmf 22.17.E2 "special case: k and 1/k in jacobiModulusDomain (non-real k)"]
theorem jacobiSnk_inv {k : ℂ} (hk : k ∈ jacobiModulusDomain) (hk' : k⁻¹ ∈ jacobiModulusDomain)
    (z : ℂ) : jacobiSnk z k⁻¹ = k * jacobiSnk (z / k) k := by
  sorry

/-- DLMF 22.17.3: `cn(z, 1/k) = dn(z/k, k)`, for `k, 1/k ∈ jacobiModulusDomain`. Admitted. -/
@[dlmf 22.17.E3 "special case: k and 1/k in jacobiModulusDomain (non-real k)"]
theorem jacobiCnk_inv {k : ℂ} (hk : k ∈ jacobiModulusDomain) (hk' : k⁻¹ ∈ jacobiModulusDomain)
    (z : ℂ) : jacobiCnk z k⁻¹ = jacobiDnk (z / k) k := by
  sorry

/-- DLMF 22.17.4: `dn(z, 1/k) = cn(z/k, k)`, for `k, 1/k ∈ jacobiModulusDomain`. Admitted. -/
@[dlmf 22.17.E4 "special case: k and 1/k in jacobiModulusDomain (non-real k)"]
theorem jacobiDnk_inv {k : ℂ} (hk : k ∈ jacobiModulusDomain) (hk' : k⁻¹ ∈ jacobiModulusDomain)
    (z : ℂ) : jacobiDnk z k⁻¹ = jacobiCnk (z / k) k := by
  sorry

/-- DLMF 22.17.5: for real `k`, `k₁ = k/√(1 + k²)` satisfies `k₁ k₁' = k/(1 + k²)` with
`k₁' = √(1 - k₁²)`. -/
@[dlmf 22.17.E5 "special case: real k"]
theorem mul_sqrt_one_sub_sq_imagModulus (k : ℝ) :
    k / √(1 + k ^ 2) * √(1 - (k / √(1 + k ^ 2)) ^ 2) = k / (1 + k ^ 2) := by
  have hp : 0 < 1 + k ^ 2 := by positivity
  have hs : 0 < √(1 + k ^ 2) := Real.sqrt_pos.mpr hp
  have h1 : 1 - (k / √(1 + k ^ 2)) ^ 2 = (1 / √(1 + k ^ 2)) ^ 2 := by
    rw [div_pow, div_pow, Real.sq_sqrt hp.le]
    field_simp
    ring
  rw [h1, Real.sqrt_sq (by positivity)]
  field_simp
  rw [Real.sq_sqrt hp.le]

/-- The modulus `k₁ = k/√(1 + k²)` of DLMF 22.17.5 for complex `k` (principal square root;
DLMF 22.17(i): either value of the square root can be chosen). -/
@[dlmf 22.17.E5]
def jacobiImagModulusk (k : ℂ) : ℂ := k / (1 + k ^ 2) ^ (1 / 2 : ℂ)

/-- DLMF 22.17.6: `sn(z, ik) = k₁' sd(z/k₁', k₁)`, `k₁ = k/√(1 + k²)`, `k₁' = √(1 - k₁²)`, for
complex `k` with `ik, k₁ ∈ jacobiModulusDomain`. Admitted. -/
@[dlmf 22.17.E6 "special case: ik and k₁ in jacobiModulusDomain"]
theorem jacobiSnk_I_mul {k : ℂ} (hk : I * k ∈ jacobiModulusDomain)
    (hk₁ : jacobiImagModulusk k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiSnk z (I * k) = jacobiComodulusk (jacobiImagModulusk k) *
      jacobiSdk (z / jacobiComodulusk (jacobiImagModulusk k)) (jacobiImagModulusk k) := by
  sorry

/-- DLMF 22.17.7: `cn(z, ik) = cd(z/k₁', k₁)`, for `ik, k₁ ∈ jacobiModulusDomain`. Admitted. -/
@[dlmf 22.17.E7 "special case: ik and k₁ in jacobiModulusDomain"]
theorem jacobiCnk_I_mul {k : ℂ} (hk : I * k ∈ jacobiModulusDomain)
    (hk₁ : jacobiImagModulusk k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiCnk z (I * k) =
      jacobiCdk (z / jacobiComodulusk (jacobiImagModulusk k)) (jacobiImagModulusk k) := by
  sorry

/-- DLMF 22.17.8: `dn(z, ik) = nd(z/k₁', k₁)`, for `ik, k₁ ∈ jacobiModulusDomain`. Admitted. -/
@[dlmf 22.17.E8 "special case: ik and k₁ in jacobiModulusDomain"]
theorem jacobiDnk_I_mul {k : ℂ} (hk : I * k ∈ jacobiModulusDomain)
    (hk₁ : jacobiImagModulusk k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiDnk z (I * k) =
      jacobiNdk (z / jacobiComodulusk (jacobiImagModulusk k)) (jacobiImagModulusk k) := by
  sorry

end DLMF.JacobiElliptic
