/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.AnalyticProperties

/-!
# Jacobian elliptic functions: Landen transformations (DLMF §22.7)

The descending modulus `k₁ = (1 - k')/(1 + k')` and the ascending pair
`k₂ = 2√k/(1 + k)`, `k₂' = (1 - k)/(1 + k)` (principal square root) are defined as in
DLMF 22.7.1 and 22.7.5. DLMF *defines* `k₂'` by the quotient; it satisfies `k₂'² = 1 - k₂²`
(proved), and it is the principal `√(1 - k₂²)` for `0 < k < 1` but not for all complex `k`
(e.g. `k = 1.3 + 0.4i`). The transformation formulas 22.7.2–22.7.4 and 22.7.6–22.7.8 are
admitted; they were checked numerically for real and complex `k` with these definitions.
-/

@[expose] public section

open Complex DLMF.Elliptic
open scoped Real

noncomputable section

namespace DLMF.JacobiElliptic

/-- The descending Landen modulus `k₁ = (1 - k')/(1 + k')` (DLMF 22.7.1). -/
@[dlmf 22.7.E1]
def jacobiLandenDescModulus (k : ℂ) : ℂ := (1 - jacobiComodulusk k) / (1 + jacobiComodulusk k)

/-- The ascending Landen modulus `k₂ = 2√k/(1 + k)` (DLMF 22.7.5, principal square root). -/
@[dlmf 22.7.E5]
def jacobiLandenAscModulus (k : ℂ) : ℂ := 2 * k ^ (1 / 2 : ℂ) / (1 + k)

/-- The ascending complementary Landen modulus `k₂' = (1 - k)/(1 + k)` (DLMF 22.7.5). -/
@[dlmf 22.7.E5]
def jacobiLandenAscComodulus (k : ℂ) : ℂ := (1 - k) / (1 + k)

/-- `k₂'² = 1 - k₂²` for `k ≠ -1` (DLMF 22.7.5). -/
@[dlmf 22.7.E5]
theorem jacobiLandenAscComodulus_sq {k : ℂ} (hk : 1 + k ≠ 0) :
    jacobiLandenAscComodulus k ^ 2 = 1 - jacobiLandenAscModulus k ^ 2 := by
  have hs : (k ^ (1 / 2 : ℂ)) ^ 2 = k := by
    rw [one_div]; exact cpow_ofNat_inv_pow k 2
  rw [jacobiLandenAscComodulus, jacobiLandenAscModulus, div_pow, div_pow, mul_pow, hs]
  field_simp
  ring

/-- **Admitted.** DLMF 22.7.2–22.7.4 (descending Landen transformation): with
`k₁ = (1 - k')/(1 + k')` and `w = z/(1 + k₁)`,
`sn(z, k) = (1 + k₁) sn(w, k₁)/(1 + k₁ sn²(w, k₁))`,
`cn(z, k) = cn(w, k₁) dn(w, k₁)/(1 + k₁ sn²(w, k₁))`,
`dn(z, k) = (dn²(w, k₁) - (1 - k₁))/(1 + k₁ - dn²(w, k₁))`, where the functions are finite and
the denominators nonzero. -/
@[dlmf 22.7.E2, dlmf 22.7.E3, dlmf 22.7.E4]
theorem jacobi_landen_descending {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : JacobiRegulark .n z k)
    (hn₁ : JacobiRegulark .n (z / (1 + jacobiLandenDescModulus k)) (jacobiLandenDescModulus k))
    (h₁ : 1 + jacobiLandenDescModulus k *
      jacobiSnk (z / (1 + jacobiLandenDescModulus k)) (jacobiLandenDescModulus k) ^ 2 ≠ 0)
    (h₂ : 1 + jacobiLandenDescModulus k -
      jacobiDnk (z / (1 + jacobiLandenDescModulus k)) (jacobiLandenDescModulus k) ^ 2 ≠ 0) :
    let k₁ := jacobiLandenDescModulus k
    let w := z / (1 + k₁)
    jacobiSnk z k = (1 + k₁) * jacobiSnk w k₁ / (1 + k₁ * jacobiSnk w k₁ ^ 2) ∧
      jacobiCnk z k = jacobiCnk w k₁ * jacobiDnk w k₁ / (1 + k₁ * jacobiSnk w k₁ ^ 2) ∧
      jacobiDnk z k = (jacobiDnk w k₁ ^ 2 - (1 - k₁)) / (1 + k₁ - jacobiDnk w k₁ ^ 2) := by
  sorry

/-- **Admitted.** DLMF 22.7.6–22.7.8 (ascending Landen transformation): with
`k₂ = 2√k/(1 + k)`, `k₂' = (1 - k)/(1 + k)` and `w = z/(1 + k₂')`,
`sn(z, k) = (1 + k₂') sn(w, k₂) cn(w, k₂)/dn(w, k₂)`,
`cn(z, k) = (1 + k₂')(dn²(w, k₂) - k₂')/(k₂² dn(w, k₂))`,
`dn(z, k) = (1 - k₂')(dn²(w, k₂) + k₂')/(k₂² dn(w, k₂))`, where the functions are finite and
`dn(w, k₂) ≠ 0`. -/
@[dlmf 22.7.E6, dlmf 22.7.E7, dlmf 22.7.E8]
theorem jacobi_landen_ascending {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : JacobiRegulark .n z k)
    (hn₂ : JacobiRegulark .n (z / (1 + jacobiLandenAscComodulus k)) (jacobiLandenAscModulus k))
    (hd₂ : jacobiDnk (z / (1 + jacobiLandenAscComodulus k)) (jacobiLandenAscModulus k) ≠ 0) :
    let k₂ := jacobiLandenAscModulus k
    let k₂' := jacobiLandenAscComodulus k
    let w := z / (1 + k₂')
    jacobiSnk z k = (1 + k₂') * jacobiSnk w k₂ * jacobiCnk w k₂ / jacobiDnk w k₂ ∧
      jacobiCnk z k = (1 + k₂') * (jacobiDnk w k₂ ^ 2 - k₂') / (k₂ ^ 2 * jacobiDnk w k₂) ∧
      jacobiDnk z k = (1 - k₂') * (jacobiDnk w k₂ ^ 2 + k₂') / (k₂ ^ 2 * jacobiDnk w k₂) := by
  sorry

end DLMF.JacobiElliptic
