/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Addition

/-!
# Jacobian elliptic functions: elementary identities (DLMF §22.6)

The sums of squares 22.6.1 are admitted (they are the theta identities 20.7.1–20.7.2); the
other sums of squares 22.6.2–22.6.4 follow from them by Glaisher's relations. The double-argument
formulas 22.6.5–22.6.13 are the cases `u = v` of the admitted addition theorems 22.8.1–22.8.9
(the second forms of 22.6.6–22.6.7 also use 22.6.1). The remaining double-, half-argument
formulas and Jacobi's imaginary transformation (Table 22.6.1) are admitted. All identities are
pointwise, at points where the functions involved are finite (`jacobiRegulark`) and the printed
denominators are nonzero.
-/

@[expose] public section

open Complex DLMF.Elliptic
open scoped Real

noncomputable section

namespace DLMF.JacobiElliptic

/-- `k'² = 1 - k²` for the principal `k' = (1 - k²)^{1/2}`. -/
theorem jacobiComodulusk_sq (k : ℂ) : jacobiComodulusk k ^ 2 = 1 - k ^ 2 := by
  rw [jacobiComodulusk, one_div]
  exact cpow_ofNat_inv_pow (1 - k ^ 2) 2

/-- `pq(z, k) ≠ 0` where the letters `p ≠ q` are both regular at `z`. -/
theorem jacobiPQk_ne_zero {p q : JacobiLetter} (hpq : p ≠ q) {z k : ℂ}
    (hp : jacobiRegulark p z k) (hq : jacobiRegulark q z k) : jacobiPQk p q z k ≠ 0 := by
  unfold jacobiPQk jacobiGlaisher
  simp only [hpq, ↓reduceIte]
  exact div_ne_zero hp hq

/-- **Admitted.** DLMF 22.6.1: `sn² + cn² = 1` and `k² sn² + dn² = 1`, at points where `sn`, `cn`,
`dn` are finite. -/
@[dlmf 22.6.E1]
theorem jacobi_sq_sum {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : jacobiRegulark .n z k) :
    jacobiSnk z k ^ 2 + jacobiCnk z k ^ 2 = 1 ∧ k ^ 2 * jacobiSnk z k ^ 2 + jacobiDnk z k ^ 2 = 1 :=
        by
  sorry

/-- Glaisher's relations expressing the nine functions with a letter other than `n` through
`sn, cn, dn` (DLMF 22.2.10, `r = n`). -/
theorem je22a_glaisher_via_n {z k : ℂ} (hn : jacobiRegulark .n z k) :
    jacobiCsk z k = jacobiCnk z k / jacobiSnk z k ∧ jacobiDsk z k = jacobiDnk z k / jacobiSnk z k ∧
    jacobiNsk z k = 1 / jacobiSnk z k ∧ jacobiSck z k = jacobiSnk z k / jacobiCnk z k ∧
    jacobiDck z k = jacobiDnk z k / jacobiCnk z k ∧ jacobiNck z k = 1 / jacobiCnk z k ∧
    jacobiSdk z k = jacobiSnk z k / jacobiDnk z k ∧ jacobiCdk z k = jacobiCnk z k / jacobiDnk z k ∧
    jacobiNdk z k = 1 / jacobiDnk z k := by
  refine ⟨jacobiPQk_eq_div (by decide) (by decide) (by decide) hn,
    jacobiPQk_eq_div (by decide) (by decide) (by decide) hn, jacobiPQk_eq_one_div _ _ _ _,
    jacobiPQk_eq_div (by decide) (by decide) (by decide) hn,
    jacobiPQk_eq_div (by decide) (by decide) (by decide) hn, jacobiPQk_eq_one_div _ _ _ _,
    jacobiPQk_eq_div (by decide) (by decide) (by decide) hn,
    jacobiPQk_eq_div (by decide) (by decide) (by decide) hn, jacobiPQk_eq_one_div _ _ _ _⟩

set_option hygiene false in
/-- Close a polynomial consequence of `h1 : sn² + cn² = 1`, `h2 : k² sn² + dn² = 1`. -/
macro "je22a_lc" : tactic => `(tactic| first
  | linear_combination h1 - h2 | linear_combination h2 - h1 | linear_combination h2
  | linear_combination -h2 | linear_combination h1 | linear_combination -h1
  | linear_combination h2 - k ^ 2 * h1 | linear_combination k ^ 2 * h1 - h2
  | linear_combination k ^ 2 * (h2 - h1) | linear_combination k ^ 2 * (h1 - h2))

/-- DLMF 22.6.2: `1 + cs²= k² + ds² = ns²`, where `sn`, `cn`, `dn` are finite and `sn ≠ 0`.
Proved from 22.6.1. -/
@[dlmf 22.6.E2]
theorem jacobi_sq_sum_s {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : jacobiRegulark .n z k) (hs : jacobiRegulark .s z k) :
    1 + jacobiCsk z k ^ 2 = k ^ 2 + jacobiDsk z k ^ 2 ∧
      k ^ 2 + jacobiDsk z k ^ 2 = jacobiNsk z k ^ 2 := by
  obtain ⟨h1, h2⟩ := jacobi_sq_sum hk hn
  obtain ⟨e1, e2, e3, -⟩ := je22a_glaisher_via_n hn
  have hsn : jacobiSnk z k ≠ 0 := jacobiPQk_ne_zero (by decide) hs hn
  rw [e1, e2, e3]
  refine ⟨?_, ?_⟩ <;> field_simp <;> je22a_lc

/-- DLMF 22.6.3: `k'² sc² + 1 = dc² = k'² nc² + k²`, where `sn`, `cn`, `dn` are finite and
`cn ≠ 0`. Proved from 22.6.1. -/
@[dlmf 22.6.E3]
theorem jacobi_sq_sum_c {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : jacobiRegulark .n z k) (hc : jacobiRegulark .c z k) :
    jacobiComodulusk k ^ 2 * jacobiSck z k ^ 2 + 1 = jacobiDck z k ^ 2 ∧
      jacobiDck z k ^ 2 = jacobiComodulusk k ^ 2 * jacobiNck z k ^ 2 + k ^ 2 := by
  obtain ⟨h1, h2⟩ := jacobi_sq_sum hk hn
  obtain ⟨-, -, -, e4, e5, e6, -⟩ := je22a_glaisher_via_n hn
  have hcn : jacobiCnk z k ≠ 0 := jacobiPQk_ne_zero (by decide) hc hn
  rw [e4, e5, e6, jacobiComodulusk_sq]
  refine ⟨?_, ?_⟩ <;> field_simp <;> je22a_lc

/-- DLMF 22.6.4: `-k²k'² sd² = k²(cd² - 1) = k'²(1 - nd²)`, where `sn`, `cn`, `dn` are finite
and `dn ≠ 0`. Proved from 22.6.1. -/
@[dlmf 22.6.E4]
theorem jacobi_sq_sum_d {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : jacobiRegulark .n z k) (hd : jacobiRegulark .d z k) :
    -k ^ 2 * jacobiComodulusk k ^ 2 * jacobiSdk z k ^ 2 = k ^ 2 * (jacobiCdk z k ^ 2 - 1) ∧
      k ^ 2 * (jacobiCdk z k ^ 2 - 1) = jacobiComodulusk k ^ 2 * (1 - jacobiNdk z k ^ 2) := by
  obtain ⟨h1, h2⟩ := jacobi_sq_sum hk hn
  obtain ⟨-, -, -, -, -, -, e7, e8, e9⟩ := je22a_glaisher_via_n hn
  have hdn : jacobiDnk z k ≠ 0 := jacobiPQk_ne_zero (by decide) hd hn
  rw [e7, e8, e9, jacobiComodulusk_sq]
  refine ⟨?_, ?_⟩ <;> field_simp <;> je22a_lc

/-! ### Double argument (§22.6(ii)) -/

/-- DLMF 22.6.5: `sn 2z = 2 sn cn dn/(1 - k² sn⁴)` (from the addition theorem 22.8.1). -/
@[dlmf 22.6.E5]
theorem jacobiSnk_two_mul {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : jacobiRegulark .n z k) (hden : 1 - k ^ 2 * jacobiSnk z k ^ 4 ≠ 0) :
    jacobiSnk (2 * z) k =
      2 * jacobiSnk z k * jacobiCnk z k * jacobiDnk z k / (1 - k ^ 2 * jacobiSnk z k ^ 4) := by
  have hd : 1 - k ^ 2 * jacobiSnk z k ^ 2 * jacobiSnk z k ^ 2 ≠ 0 := by
    convert hden using 2; ring
  rw [two_mul, jacobiSnk_add hk hn hn hd]
  ring

/-- DLMF 22.6.6: `cn 2z = (cn² - sn² dn²)/(1 - k² sn⁴) = (cn⁴ - k'² sn⁴)/(1 - k² sn⁴)`
(from 22.8.2 and 22.6.1). -/
@[dlmf 22.6.E6]
theorem jacobiCnk_two_mul {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : jacobiRegulark .n z k) (hden : 1 - k ^ 2 * jacobiSnk z k ^ 4 ≠ 0) :
    jacobiCnk (2 * z) k = (jacobiCnk z k ^ 2 - jacobiSnk z k ^ 2 * jacobiDnk z k ^ 2) /
        (1 - k ^ 2 * jacobiSnk z k ^ 4) ∧
      (jacobiCnk z k ^ 2 - jacobiSnk z k ^ 2 * jacobiDnk z k ^ 2) /
          (1 - k ^ 2 * jacobiSnk z k ^ 4) =
        (jacobiCnk z k ^ 4 - jacobiComodulusk k ^ 2 * jacobiSnk z k ^ 4) /
          (1 - k ^ 2 * jacobiSnk z k ^ 4) := by
  have hd : 1 - k ^ 2 * jacobiSnk z k ^ 2 * jacobiSnk z k ^ 2 ≠ 0 := by
    convert hden using 2; ring
  obtain ⟨h1, h2⟩ := jacobi_sq_sum hk hn
  have hc2 : jacobiCnk z k ^ 2 = 1 - jacobiSnk z k ^ 2 := by linear_combination h1
  have hd2 : jacobiDnk z k ^ 2 = 1 - k ^ 2 * jacobiSnk z k ^ 2 := by linear_combination h2
  refine ⟨?_, ?_⟩
  · rw [two_mul, jacobiCnk_add hk hn hn hd]
    ring
  · rw [jacobiComodulusk_sq, show jacobiCnk z k ^ 4 = (jacobiCnk z k ^ 2) ^ 2 by ring, hc2, hd2]
    ring

/-- DLMF 22.6.7: `dn 2z = (dn² - k² sn² cn²)/(1 - k² sn⁴) = (dn⁴ + k²k'² sn⁴)/(1 - k² sn⁴)`
(from 22.8.3 and 22.6.1). -/
@[dlmf 22.6.E7]
theorem jacobiDnk_two_mul {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : jacobiRegulark .n z k) (hden : 1 - k ^ 2 * jacobiSnk z k ^ 4 ≠ 0) :
    jacobiDnk (2 * z) k = (jacobiDnk z k ^ 2 - k ^ 2 * jacobiSnk z k ^ 2 * jacobiCnk z k ^ 2) /
        (1 - k ^ 2 * jacobiSnk z k ^ 4) ∧
      (jacobiDnk z k ^ 2 - k ^ 2 * jacobiSnk z k ^ 2 * jacobiCnk z k ^ 2) /
          (1 - k ^ 2 * jacobiSnk z k ^ 4) =
        (jacobiDnk z k ^ 4 + k ^ 2 * jacobiComodulusk k ^ 2 * jacobiSnk z k ^ 4) /
          (1 - k ^ 2 * jacobiSnk z k ^ 4) := by
  have hd : 1 - k ^ 2 * jacobiSnk z k ^ 2 * jacobiSnk z k ^ 2 ≠ 0 := by
    convert hden using 2; ring
  obtain ⟨h1, h2⟩ := jacobi_sq_sum hk hn
  have hc2 : jacobiCnk z k ^ 2 = 1 - jacobiSnk z k ^ 2 := by linear_combination h1
  have hd2 : jacobiDnk z k ^ 2 = 1 - k ^ 2 * jacobiSnk z k ^ 2 := by linear_combination h2
  refine ⟨?_, ?_⟩
  · rw [two_mul, jacobiDnk_add hk hn hn hd]
    ring
  · rw [jacobiComodulusk_sq, show jacobiDnk z k ^ 4 = (jacobiDnk z k ^ 2) ^ 2 by ring, hc2, hd2]
    ring

/-- DLMF 22.6.8: `cd 2z = (cd² - k'² sd² nd²)/(1 + k²k'² sd⁴)` (from 22.8.4). -/
@[dlmf 22.6.E8]
theorem jacobiCdk_two_mul {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hd : jacobiRegulark .d z k)
    (hden : 1 + k ^ 2 * jacobiComodulusk k ^ 2 * jacobiSdk z k ^ 4 ≠ 0) :
    jacobiCdk (2 * z) k =
      (jacobiCdk z k ^ 2 - jacobiComodulusk k ^ 2 * jacobiSdk z k ^ 2 * jacobiNdk z k ^ 2) /
        (1 + k ^ 2 * jacobiComodulusk k ^ 2 * jacobiSdk z k ^ 4) := by
  have hd' : 1 + k ^ 2 * jacobiComodulusk k ^ 2 * jacobiSdk z k ^ 2 * jacobiSdk z k ^ 2 ≠ 0 := by
    convert hden using 2; ring
  rw [two_mul, jacobiCdk_add hk hd hd hd']
  ring

/-- DLMF 22.6.9: `sd 2z = 2 sd cd nd/(1 + k²k'² sd⁴)` (from 22.8.5). -/
@[dlmf 22.6.E9]
theorem jacobiSdk_two_mul {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hd : jacobiRegulark .d z k)
    (hden : 1 + k ^ 2 * jacobiComodulusk k ^ 2 * jacobiSdk z k ^ 4 ≠ 0) :
    jacobiSdk (2 * z) k = 2 * jacobiSdk z k * jacobiCdk z k * jacobiNdk z k /
      (1 + k ^ 2 * jacobiComodulusk k ^ 2 * jacobiSdk z k ^ 4) := by
  have hd' : 1 + k ^ 2 * jacobiComodulusk k ^ 2 * jacobiSdk z k ^ 2 * jacobiSdk z k ^ 2 ≠ 0 := by
    convert hden using 2; ring
  rw [two_mul, jacobiSdk_add hk hd hd hd']
  ring

/-- DLMF 22.6.10: `nd 2z = (nd² + k² sd² cd²)/(1 + k²k'² sd⁴)` (from 22.8.6). -/
@[dlmf 22.6.E10]
theorem jacobiNdk_two_mul {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hd : jacobiRegulark .d z k)
    (hden : 1 + k ^ 2 * jacobiComodulusk k ^ 2 * jacobiSdk z k ^ 4 ≠ 0) :
    jacobiNdk (2 * z) k = (jacobiNdk z k ^ 2 + k ^ 2 * jacobiSdk z k ^ 2 * jacobiCdk z k ^ 2) /
      (1 + k ^ 2 * jacobiComodulusk k ^ 2 * jacobiSdk z k ^ 4) := by
  have hd' : 1 + k ^ 2 * jacobiComodulusk k ^ 2 * jacobiSdk z k ^ 2 * jacobiSdk z k ^ 2 ≠ 0 := by
    convert hden using 2; ring
  rw [two_mul, jacobiNdk_add hk hd hd hd']
  ring

/-- DLMF 22.6.11: `dc 2z = (dc² + k'² sc² nc²)/(1 - k'² sc⁴)` (from 22.8.7). -/
@[dlmf 22.6.E11]
theorem jacobiDck_two_mul {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hc : jacobiRegulark .c z k) (hden : 1 - jacobiComodulusk k ^ 2 * jacobiSck z k ^ 4 ≠ 0) :
    jacobiDck (2 * z) k =
      (jacobiDck z k ^ 2 + jacobiComodulusk k ^ 2 * jacobiSck z k ^ 2 * jacobiNck z k ^ 2) /
        (1 - jacobiComodulusk k ^ 2 * jacobiSck z k ^ 4) := by
  have hd' : 1 - jacobiComodulusk k ^ 2 * jacobiSck z k ^ 2 * jacobiSck z k ^ 2 ≠ 0 := by
    convert hden using 2; ring
  rw [two_mul, jacobiDck_add hk hc hc hd']
  ring

/-- DLMF 22.6.12: `nc 2z = (nc² + sc² dc²)/(1 - k'² sc⁴)` (from 22.8.8). -/
@[dlmf 22.6.E12]
theorem jacobiNck_two_mul {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hc : jacobiRegulark .c z k) (hden : 1 - jacobiComodulusk k ^ 2 * jacobiSck z k ^ 4 ≠ 0) :
    jacobiNck (2 * z) k = (jacobiNck z k ^ 2 + jacobiSck z k ^ 2 * jacobiDck z k ^ 2) /
      (1 - jacobiComodulusk k ^ 2 * jacobiSck z k ^ 4) := by
  have hd' : 1 - jacobiComodulusk k ^ 2 * jacobiSck z k ^ 2 * jacobiSck z k ^ 2 ≠ 0 := by
    convert hden using 2; ring
  rw [two_mul, jacobiNck_add hk hc hc hd']
  ring

/-- DLMF 22.6.13: `sc 2z = 2 sc dc nc/(1 - k'² sc⁴)` (from 22.8.9). -/
@[dlmf 22.6.E13]
theorem jacobiSck_two_mul {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hc : jacobiRegulark .c z k) (hden : 1 - jacobiComodulusk k ^ 2 * jacobiSck z k ^ 4 ≠ 0) :
    jacobiSck (2 * z) k = 2 * jacobiSck z k * jacobiDck z k * jacobiNck z k /
      (1 - jacobiComodulusk k ^ 2 * jacobiSck z k ^ 4) := by
  have hd' : 1 - jacobiComodulusk k ^ 2 * jacobiSck z k ^ 2 * jacobiSck z k ^ 2 ≠ 0 := by
    convert hden using 2; ring
  rw [two_mul, jacobiSck_add hk hc hc hd']
  ring

/-- **Admitted.** DLMF 22.6.14–22.6.16: `ns 2z = (ns⁴ - k²)/(2 cs ds ns)`,
`ds 2z = (k²k'² + ds⁴)/(2 cs ds ns)`, `cs 2z = (cs⁴ - k'²)/(2 cs ds ns)`, where the `·s`
functions are finite and the denominator is nonzero. -/
@[dlmf 22.6.E14, dlmf 22.6.E15, dlmf 22.6.E16]
theorem jacobi_two_mul_s {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hs : jacobiRegulark .s z k)
    (hden : 2 * jacobiCsk z k * jacobiDsk z k * jacobiNsk z k ≠ 0) :
    jacobiNsk (2 * z) k = (jacobiNsk z k ^ 4 - k ^ 2) /
        (2 * jacobiCsk z k * jacobiDsk z k * jacobiNsk z k) ∧
      jacobiDsk (2 * z) k = (k ^ 2 * jacobiComodulusk k ^ 2 + jacobiDsk z k ^ 4) /
        (2 * jacobiCsk z k * jacobiDsk z k * jacobiNsk z k) ∧
      jacobiCsk (2 * z) k = (jacobiCsk z k ^ 4 - jacobiComodulusk k ^ 2) /
        (2 * jacobiCsk z k * jacobiDsk z k * jacobiNsk z k) := by
  sorry

/-- **Admitted.** DLMF 22.6.17–22.6.18:
`(1 - cn 2z)/(1 + cn 2z) = sn² dn²/cn²` and `(1 - dn 2z)/(1 + dn 2z) = k² sn² cn²/dn²`, where
`sn, cn, dn` are finite at `z` and `2z` and the denominators are nonzero. -/
@[dlmf 22.6.E17, dlmf 22.6.E18]
theorem jacobi_two_mul_ratio {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : jacobiRegulark .n z k) (hn2 : jacobiRegulark .n (2 * z) k)
    (hc : jacobiCnk z k ≠ 0) (hd : jacobiDnk z k ≠ 0)
    (hc2 : 1 + jacobiCnk (2 * z) k ≠ 0) (hd2 : 1 + jacobiDnk (2 * z) k ≠ 0) :
    (1 - jacobiCnk (2 * z) k) / (1 + jacobiCnk (2 * z) k) =
        jacobiSnk z k ^ 2 * jacobiDnk z k ^ 2 / jacobiCnk z k ^ 2 ∧
      (1 - jacobiDnk (2 * z) k) / (1 + jacobiDnk (2 * z) k) =
        k ^ 2 * jacobiSnk z k ^ 2 * jacobiCnk z k ^ 2 / jacobiDnk z k ^ 2 := by
  sorry

/-! ### Half argument (§22.6(iii)) -/

/-- **Admitted.** DLMF 22.6.19: `sn²(z/2) = (1 - cn z)/(1 + dn z) = (1 - dn z)/(k²(1 + cn z))
= (dn z - k² cn z - k'²)/(k²(dn z - cn z))`, where the functions are finite at `z/2`, `z` and
the denominators are nonzero. -/
@[dlmf 22.6.E19]
theorem jacobiSnk_half_sq {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : jacobiRegulark .n z k) (hn2 : jacobiRegulark .n (z / 2) k)
    (h1 : 1 + jacobiDnk z k ≠ 0) (h2 : 1 + jacobiCnk z k ≠ 0)
    (h3 : jacobiDnk z k - jacobiCnk z k ≠ 0) :
    jacobiSnk (z / 2) k ^ 2 = (1 - jacobiCnk z k) / (1 + jacobiDnk z k) ∧
      jacobiSnk (z / 2) k ^ 2 = (1 - jacobiDnk z k) / (k ^ 2 * (1 + jacobiCnk z k)) ∧
      jacobiSnk (z / 2) k ^ 2 = (jacobiDnk z k - k ^ 2 * jacobiCnk z k - jacobiComodulusk k ^ 2) /
        (k ^ 2 * (jacobiDnk z k - jacobiCnk z k)) := by
  sorry

/-- **Admitted.** DLMF 22.6.20: `cn²(z/2) = (-k'² + dn z + k² cn z)/(k²(1 + cn z))
= k'²(1 - dn z)/(k²(dn z - cn z)) = k'²(1 + cn z)/(k'² + dn z - k² cn z)`. -/
@[dlmf 22.6.E20]
theorem jacobiCnk_half_sq {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : jacobiRegulark .n z k) (hn2 : jacobiRegulark .n (z / 2) k)
    (h1 : 1 + jacobiCnk z k ≠ 0) (h2 : jacobiDnk z k - jacobiCnk z k ≠ 0)
    (h3 : jacobiComodulusk k ^ 2 + jacobiDnk z k - k ^ 2 * jacobiCnk z k ≠ 0) :
    jacobiCnk (z / 2) k ^ 2 = (-jacobiComodulusk k ^ 2 + jacobiDnk z k + k ^ 2 * jacobiCnk z k) /
        (k ^ 2 * (1 + jacobiCnk z k)) ∧
      jacobiCnk (z / 2) k ^ 2 = jacobiComodulusk k ^ 2 * (1 - jacobiDnk z k) /
        (k ^ 2 * (jacobiDnk z k - jacobiCnk z k)) ∧
      jacobiCnk (z / 2) k ^ 2 = jacobiComodulusk k ^ 2 * (1 + jacobiCnk z k) /
        (jacobiComodulusk k ^ 2 + jacobiDnk z k - k ^ 2 * jacobiCnk z k) := by
  sorry

/-- **Admitted.** DLMF 22.6.21: `dn²(z/2) = (k² cn z + dn z + k'²)/(1 + dn z)
= k'²(1 - cn z)/(dn z - cn z) = k'²(1 + dn z)/(k'² + dn z - k² cn z)`. -/
@[dlmf 22.6.E21]
theorem jacobiDnk_half_sq {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : jacobiRegulark .n z k) (hn2 : jacobiRegulark .n (z / 2) k)
    (h1 : 1 + jacobiDnk z k ≠ 0) (h2 : jacobiDnk z k - jacobiCnk z k ≠ 0)
    (h3 : jacobiComodulusk k ^ 2 + jacobiDnk z k - k ^ 2 * jacobiCnk z k ≠ 0) :
    jacobiDnk (z / 2) k ^ 2 = (k ^ 2 * jacobiCnk z k + jacobiDnk z k + jacobiComodulusk k ^ 2) /
        (1 + jacobiDnk z k) ∧
      jacobiDnk (z / 2) k ^ 2 = jacobiComodulusk k ^ 2 * (1 - jacobiCnk z k) /
        (jacobiDnk z k - jacobiCnk z k) ∧
      jacobiDnk (z / 2) k ^ 2 = jacobiComodulusk k ^ 2 * (1 + jacobiDnk z k) /
        (jacobiComodulusk k ^ 2 + jacobiDnk z k - k ^ 2 * jacobiCnk z k) := by
  sorry

/-- **Admitted.** DLMF 22.6.22: for a permutation `{p, q, r}` of `{c, d, n}`,
`pq²(z/2) = (ps + rs)/(qs + rs) = (pq + rq)/(1 + rq) = (pr + 1)/(qr + 1)`, where all twelve
functions are finite at `z/2` and `z` and the denominators are nonzero. -/
@[dlmf 22.6.E22]
theorem jacobiPQk_half_sq {k : ℂ} (hk : k ∈ jacobiModulusDomain) {p q r : JacobiLetter}
    (hp : p ≠ .s) (hq : q ≠ .s) (hr : r ≠ .s) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) {z : ℂ}
    (hz : ∀ l, jacobiRegulark l z k) (hz2 : ∀ l, jacobiRegulark l (z / 2) k)
    (h1 : jacobiPQk q .s z k + jacobiPQk r .s z k ≠ 0) (h2 : 1 + jacobiPQk r q z k ≠ 0)
    (h3 : jacobiPQk q r z k + 1 ≠ 0) :
    jacobiPQk p q (z / 2) k ^ 2 =
        (jacobiPQk p .s z k + jacobiPQk r .s z k) / (jacobiPQk q .s z k + jacobiPQk r .s z k) ∧
      jacobiPQk p q (z / 2) k ^ 2 =
        (jacobiPQk p q z k + jacobiPQk r q z k) / (1 + jacobiPQk r q z k) ∧
      jacobiPQk p q (z / 2) k ^ 2 = (jacobiPQk p r z k + 1) / (jacobiPQk q r z k + 1) := by
  sorry

/-! ### Jacobi's imaginary transformation (§22.6(iv), Table 22.6.1) -/

/-- **Admitted.** Table 22.6.1 (Jacobi's imaginary transformation), with the complementary
modulus `k' = √(1 - k²)` (which again lies in `jacobiModulusDomain`). Both sides have the same
poles, where both are Lean's `0`. -/
@[dlmf 22.6.T1]
theorem jacobi_imaginary_transformation {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    let k' := jacobiComodulusk k
    jacobiSnk (I * z) k = I * jacobiSck z k' ∧ jacobiCnk (I * z) k = jacobiNck z k' ∧
      jacobiDnk (I * z) k = jacobiDck z k' ∧ jacobiCdk (I * z) k = jacobiNdk z k' ∧
      jacobiSdk (I * z) k = I * jacobiSdk z k' ∧ jacobiNdk (I * z) k = jacobiCdk z k' ∧
      jacobiDck (I * z) k = jacobiDnk z k' ∧ jacobiNck (I * z) k = jacobiCnk z k' ∧
      jacobiSck (I * z) k = I * jacobiSnk z k' ∧ jacobiNsk (I * z) k = -I * jacobiCsk z k' ∧
      jacobiDsk (I * z) k = -I * jacobiDsk z k' ∧ jacobiCsk (I * z) k = -I * jacobiNsk z k' := by
  sorry

end DLMF.JacobiElliptic
