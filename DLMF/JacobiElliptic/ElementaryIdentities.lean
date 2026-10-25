/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Addition

/-!
# Jacobian elliptic functions: elementary identities (DLMF §22.6)

The sums of squares 22.6.1 are proved from the theta identities 20.7.2–20.7.3; the
other sums of squares 22.6.2–22.6.4 follow from them by Glaisher's relations. The double-argument
formulas 22.6.5–22.6.13 are the cases `u = v` of the addition theorems 22.8.1–22.8.9
(the second forms of 22.6.6–22.6.7 also use 22.6.1). The double-argument formulas
22.6.14–22.6.16 are proved from the theta duplication identities, 22.6.17–22.6.18 and the
half-argument formulas 22.6.19–22.6.21 from 22.6.6–22.6.7 and 22.6.1. Jacobi's imaginary
transformation (Table 22.6.1) is proved from `τ(k') = -1/τ(k)` and the theta transformations
under `τ ↦ -1/τ`. The half-argument formula 22.6.22 is admitted. All
identities are pointwise, at points where the functions involved are finite (`jacobiRegulark`)
and the printed denominators are nonzero.
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

/-- DLMF 22.6.1: `sn² + cn² = 1` and `k² sn² + dn² = 1`, at points where `sn`, `cn`,
`dn` are finite. From the theta identities 20.7.2–20.7.3 and `k = θ₂²/θ₃²` (22.2.2). -/
@[dlmf 22.6.E1]
theorem jacobi_sq_sum {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : jacobiRegulark .n z k) :
    jacobiSnk z k ^ 2 + jacobiCnk z k ^ 2 = 1 ∧ k ^ 2 * jacobiSnk z k ^ 2 + jacobiDnk z k ^ 2 = 1 :=
        by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hn' : jacobiThetaFourTau (jacobiZetak z k) (jacobiTauk k) ≠ 0 := by
    intro h; apply hn; simp [jacobiLetterTheta, h]
  simp only [jacobiSnk, jacobiCnk, jacobiDnk, jacobiPQk, jacobiGlaisher, jacobiLetterTheta,
    reduceCtorEq, ↓reduceIte]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = ζ at hn' ⊢
  generalize jacobiTauk k = τ at hτ hn' hmod ⊢
  subst hmod
  have h2 := je22a_thetaTwo_zero_ne_zero hτ
  have h3 := je22a_thetaThree_zero_ne_zero hτ
  have h4 := je22a_thetaFour_zero_ne_zero hτ
  have e3 := DLMF.Theta.jacobiTheta_sq_two_four ζ τ hτ
  have e2 := DLMF.Theta.jacobiTheta_sq_three_four ζ τ hτ
  simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
    DLMF.Theta.jacobiThetaFourNullTau] at e2 e3
  constructor
  · field_simp
    linear_combination -e3
  · field_simp
    linear_combination -e2

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

local notation "θ₁" => jacobiThetaOneTau
local notation "θ₂" => jacobiThetaTwoTau
local notation "θ₃" => jacobiThetaThreeTau
local notation "θ₄" => jacobiThetaFourTau

/-- `1 - k² sn⁴ z ≠ 0` where `sn` is finite at `z` and `2z` (helper). -/
lemma p22R1_den_two {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : jacobiRegulark .n z k) (hn2 : jacobiRegulark .n (2 * z) k) :
    1 - k ^ 2 * jacobiSnk z k ^ 4 ≠ 0 := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hu' : θ₄ (jacobiZetak z k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hn; simp [jacobiLetterTheta, h']
  have hu2 : θ₄ (jacobiZetak (2 * z) k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hn2; simp [jacobiLetterTheta, h']
  have h2z : jacobiZetak (2 * z) k = jacobiZetak z k + jacobiZetak z k := by
    simp only [jacobiZetak]; ring
  rw [h2z] at hu2
  simp only [jacobiSnk, jacobiPQk, jacobiGlaisher, jacobiLetterTheta, reduceCtorEq, ↓reduceIte]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hu' hu2 ⊢
  generalize jacobiTauk k = τ at hτ hu' hu2 hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have N4 := p22R1_four_add_mul_sub x x τ hτ
  rw [sub_self] at N4
  intro h0
  field_simp at h0
  apply hu2
  apply mul_left_cancel₀ (pow_ne_zero 3 h4)
  linear_combination N4 + h0

/-- DLMF 22.6.14–22.6.16: `ns 2z = (ns⁴ - k²)/(2 cs ds ns)`,
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
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hu' : θ₁ (jacobiZetak z k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hs; simp [jacobiLetterTheta, h']
  simp only [eq_div_iff hden]
  rw [← (jacobi_inversion_k hk).2.1]
  have h2z : jacobiZetak (2 * z) k = jacobiZetak z k + jacobiZetak z k := by
    simp only [jacobiZetak]; ring
  simp only [jacobiNsk, jacobiDsk, jacobiCsk, jacobiPQk, jacobiGlaisher, jacobiLetterTheta,
    jacobiComodulusTau, reduceCtorEq, ↓reduceIte, h2z] at hden ⊢
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hu' hden ⊢
  generalize jacobiTauk k = τ at hτ hu' hden hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hx2 : θ₂ x τ ≠ 0 := by intro h0; apply hden; simp [h0]
  have hx3 : θ₃ x τ ≠ 0 := by intro h0; apply hden; simp [h0]
  have hx4 : θ₄ x τ ≠ 0 := by intro h0; apply hden; simp [h0]
  have dup := p22R1_mixed14 x x τ hτ
  rw [sub_self] at dup
  have hD : θ₁ (x + x) τ ≠ 0 := by
    intro h0
    rw [h0] at dup
    have : θ₁ x τ * θ₄ x τ * (θ₂ x τ * θ₃ x τ) = 0 := by linear_combination -dup / 2
    simp [hu', hx2, hx3, hx4] at this
  have N4 := p22R1_four_add_mul_sub x x τ hτ
  have N3 := p22R1_S3 x x τ hτ
  have N2 := p22R1_S2 x x τ hτ
  rw [sub_self] at N4 N3 N2
  generalize x + x = X at hD dup N4 N3 N2 ⊢
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    linear_combination (-(θ₄ X τ * θ₄ 0 τ ^ 2)) * dup + (θ₂ 0 τ * θ₃ 0 τ * θ₁ X τ) * N4
  · field_simp
    linear_combination (-(θ₃ X τ * θ₃ 0 τ ^ 2)) * dup + (θ₂ 0 τ * θ₄ 0 τ * θ₁ X τ) * N3
  · field_simp
    linear_combination (-(θ₂ X τ * θ₂ 0 τ ^ 2)) * dup + (θ₃ 0 τ * θ₄ 0 τ * θ₁ X τ) * N2

/-- DLMF 22.6.17–22.6.18:
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
  have hD := p22R1_den_two hk hn hn2
  obtain ⟨h1, h2⟩ := jacobi_sq_sum hk hn
  rw [(jacobiCnk_two_mul hk hn hD).1] at hc2 ⊢
  rw [(jacobiDnk_two_mul hk hn hD).1] at hd2 ⊢
  have hD' : 1 - jacobiSnk z k ^ 4 * k ^ 2 ≠ 0 := by rwa [mul_comm] at hD
  constructor
  · rw [div_eq_div_iff hc2 (pow_ne_zero 2 hc)]
    field_simp
    linear_combination (-(jacobiCnk z k) ^ 2 - k ^ 2 * (jacobiSnk z k) ^ 4 +
        (jacobiSnk z k) ^ 2) * h1 +
      ((jacobiDnk z k) ^ 2 * (jacobiSnk z k) ^ 4 + (jacobiSnk z k) ^ 4 - (jacobiSnk z k) ^ 2) * h2
  · rw [div_eq_div_iff hd2 (pow_ne_zero 2 hd)]
    field_simp
    linear_combination ((jacobiCnk z k) ^ 2 * k ^ 4 * (jacobiSnk z k) ^ 4 +
        k ^ 4 * (jacobiSnk z k) ^ 4 -
      k ^ 2 * (jacobiSnk z k) ^ 2) * h1 +
      (-(jacobiDnk z k) ^ 2 - k ^ 2 * (jacobiSnk z k) ^ 4 + k ^ 2 * (jacobiSnk z k) ^ 2) * h2

/-! ### Half argument (§22.6(iii)) -/

/-- DLMF 22.6.19: `sn²(z/2) = (1 - cn z)/(1 + dn z) = (1 - dn z)/(k²(1 + cn z))
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
  have hk0 : k ≠ 0 := by
    rintro rfl; simp [jacobiModulusDomain] at hk
  obtain ⟨w, rfl⟩ : ∃ w, z = 2 * w := ⟨z / 2, by ring⟩
  have hw : 2 * w / 2 = w := by ring
  rw [hw] at hn2 ⊢
  have hD := p22R1_den_two hk hn2 hn
  have hD' : 1 - jacobiSnk w k ^ 4 * k ^ 2 ≠ 0 := by rwa [mul_comm] at hD
  obtain ⟨e1, e2⟩ := jacobi_sq_sum hk hn2
  have hK := jacobiComodulusk_sq k
  simp only [(jacobiCnk_two_mul hk hn2 hD).1, (jacobiDnk_two_mul hk hn2 hD).1] at h1 h2 h3 ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [eq_div_iff (by assumption)]
    field_simp
    linear_combination (-k ^ 2 * (jacobiSnk w k) ^ 4 + 1) * e1
  · rw [eq_div_iff (mul_ne_zero (pow_ne_zero 2 hk0) (by assumption))]
    field_simp
    linear_combination (-k ^ 2 * (jacobiSnk w k) ^ 4 + 1) * e2
  · rw [eq_div_iff (mul_ne_zero (pow_ne_zero 2 hk0) (by assumption))]
    field_simp
    linear_combination (-k ^ 4 * (jacobiSnk w k) ^ 4 + k ^ 2) * e1 +
      (k ^ 2 * (jacobiSnk w k) ^ 4 - 1) * e2 +
      (-k ^ 2 * (jacobiSnk w k) ^ 4 + 1) * hK

/-- DLMF 22.6.20: `cn²(z/2) = (-k'² + dn z + k² cn z)/(k²(1 + cn z))
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
  have hk0 : k ≠ 0 := by
    rintro rfl; simp [jacobiModulusDomain] at hk
  obtain ⟨w, rfl⟩ : ∃ w, z = 2 * w := ⟨z / 2, by ring⟩
  have hw : 2 * w / 2 = w := by ring
  rw [hw] at hn2 ⊢
  have hD := p22R1_den_two hk hn2 hn
  have hD' : 1 - jacobiSnk w k ^ 4 * k ^ 2 ≠ 0 := by rwa [mul_comm] at hD
  obtain ⟨e1, e2⟩ := jacobi_sq_sum hk hn2
  have hK := jacobiComodulusk_sq k
  simp only [(jacobiCnk_two_mul hk hn2 hD).1, (jacobiDnk_two_mul hk hn2 hD).1] at h1 h2 h3 ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [eq_div_iff (mul_ne_zero (pow_ne_zero 2 hk0) (by assumption))]
    field_simp
    linear_combination ((jacobiCnk w k) ^ 2 * k ^ 2 -
        (jacobiDnk w k) ^ 2 * k ^ 2 * (jacobiSnk w k) ^ 2 - k ^ 4 * (jacobiSnk w k) ^ 4 +
            k ^ 2) * e1 +
      (k ^ 2 * (jacobiSnk w k) ^ 4 - 1) * e2 +
      (-k ^ 2 * (jacobiSnk w k) ^ 4 + 1) * hK
  · rw [eq_div_iff (mul_ne_zero (pow_ne_zero 2 hk0) (by assumption))]
    field_simp
    linear_combination (-(jacobiCnk w k) ^ 2 * k ^ 4 * (jacobiSnk w k) ^ 2 -
        (jacobiCnk w k) ^ 2 * k ^ 2 + (jacobiDnk w k) ^ 2 * k ^ 2 * (jacobiSnk w k) ^ 2 +
            (jacobiDnk w k) ^ 2 * k ^ 2 +
                k ^ 4 * (jacobiSnk w k) ^ 4 - k ^ 4 * (jacobiSnk w k) ^ 2 -
                    k ^ 2 * (jacobiComodulusk k) ^ 2 * (jacobiSnk w k) ^ 2 +
                        k ^ 2 * (jacobiSnk w k) ^ 2 - k ^ 2) * e1 +
      (-k ^ 2 * (jacobiSnk w k) ^ 4 + k ^ 2 + (jacobiComodulusk k) ^ 2) * e2 +
      (2 * k ^ 2 * (jacobiSnk w k) ^ 4 - 2 * k ^ 2 * (jacobiSnk w k) ^ 2) * hK
  · rw [eq_div_iff (by assumption)]
    field_simp
    linear_combination (-(jacobiCnk w k) ^ 2 * k ^ 2 * (jacobiSnk w k) ^ 2 -
        (jacobiCnk w k) ^ 2 * k ^ 2 + (jacobiDnk w k) ^ 2 * k ^ 2 * (jacobiSnk w k) ^ 2 +
            (jacobiDnk w k) ^ 2 - k ^ 2 * (jacobiComodulusk k) ^ 2 * (jacobiSnk w k) ^ 4 +
                k ^ 2 * (jacobiSnk w k) ^ 4 - k ^ 2) * e1 +
      (-k ^ 2 * (jacobiSnk w k) ^ 4 + k ^ 2 * (jacobiSnk w k) ^ 2 +
          (jacobiComodulusk k) ^ 2 * (jacobiSnk w k) ^ 2 - (jacobiSnk w k) ^ 2 + 1) * e2 +
      (k ^ 2 * (jacobiSnk w k) ^ 6 - k ^ 2 * (jacobiSnk w k) ^ 4 + (jacobiSnk w k) ^ 2 - 1) * hK

/-- DLMF 22.6.21: `dn²(z/2) = (k² cn z + dn z + k'²)/(1 + dn z)
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
  have hk0 : k ≠ 0 := by
    rintro rfl; simp [jacobiModulusDomain] at hk
  obtain ⟨w, rfl⟩ : ∃ w, z = 2 * w := ⟨z / 2, by ring⟩
  have hw : 2 * w / 2 = w := by ring
  rw [hw] at hn2 ⊢
  have hD := p22R1_den_two hk hn2 hn
  have hD' : 1 - jacobiSnk w k ^ 4 * k ^ 2 ≠ 0 := by rwa [mul_comm] at hD
  obtain ⟨e1, e2⟩ := jacobi_sq_sum hk hn2
  have hK := jacobiComodulusk_sq k
  simp only [(jacobiCnk_two_mul hk hn2 hD).1, (jacobiDnk_two_mul hk hn2 hD).1] at h1 h2 h3 ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [eq_div_iff (by assumption)]
    field_simp
    linear_combination (-(jacobiDnk w k) ^ 2 * k ^ 2 * (jacobiSnk w k) ^ 2 +
        k ^ 2 * (jacobiSnk w k) ^ 2 - k ^ 2) * e1 +
      ((jacobiDnk w k) ^ 2 - k ^ 2 * (jacobiSnk w k) ^ 2 + 1) * e2 +
      (k ^ 2 * (jacobiSnk w k) ^ 4 - 1) * hK
  · rw [eq_div_iff (by assumption)]
    field_simp
    linear_combination (-(jacobiDnk w k) ^ 2 * k ^ 2 * (jacobiSnk w k) ^ 2 - (jacobiDnk w k) ^ 2 +
        (jacobiComodulusk k) ^ 2) * e1 +
      ((jacobiDnk w k) ^ 2 * (jacobiSnk w k) ^ 2 +
          (jacobiDnk w k) ^ 2 - 2 * k ^ 2 * (jacobiSnk w k) ^ 2 -
              (jacobiComodulusk k) ^ 2 * (jacobiSnk w k) ^ 2 + 2 * (jacobiSnk w k) ^ 2) * e2 +
      (2 * k ^ 2 * (jacobiSnk w k) ^ 4 - 2 * (jacobiSnk w k) ^ 2) * hK
  · rw [eq_div_iff (by assumption)]
    field_simp
    linear_combination (-(jacobiDnk w k) ^ 2 * k ^ 2 * (jacobiSnk w k) ^ 2 -
        (jacobiDnk w k) ^ 2 * k ^ 2 + k ^ 2 * (jacobiComodulusk k) ^ 2 * (jacobiSnk w k) ^ 2) * e1 +
      ((jacobiDnk w k) ^ 2 * k ^ 2 * (jacobiSnk w k) ^ 2 +
          (jacobiDnk w k) ^ 2 - k ^ 4 * (jacobiSnk w k) ^ 4 -
              k ^ 2 * (jacobiComodulusk k) ^ 2 * (jacobiSnk w k) ^ 4 +
                  k ^ 2 * (jacobiSnk w k) ^ 4 - k ^ 2 + 1) * e2 +
      (k ^ 4 * (jacobiSnk w k) ^ 6 - k ^ 2 * (jacobiSnk w k) ^ 4 +
          k ^ 2 * (jacobiSnk w k) ^ 2 - 1) * hK

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

/-- The principal square root of a slit-plane number has positive real part. -/
lemma p22R1_re_sqrt_pos {w : ℂ} (hw : w ∈ slitPlane) : 0 < (w ^ (1 / 2 : ℂ)).re := by
  rcases (p22R1_sqrt_parts w).1.eq_or_lt with h | h
  · exfalso
    have hsq := p22R1_sqrt_sq w
    set r := w ^ (1 / 2 : ℂ)
    have hr : r = (r.im : ℂ) * I := by
      apply Complex.ext <;> simp [h.symm]
    have : w = -((r.im : ℂ) ^ 2) := by
      rw [← hsq]; nth_rewrite 1 [hr]; rw [mul_pow, I_sq]; ring
    rw [this, mem_slitPlane_iff] at hw
    rcases hw with hw | hw
    · have : (-((r.im : ℂ) ^ 2)).re = -(r.im ^ 2) := by
        rw [← ofReal_pow, ← ofReal_neg, ofReal_re]
      rw [this] at hw; nlinarith [sq_nonneg r.im]
    · apply hw; rw [← ofReal_pow, ← ofReal_neg, ofReal_im]
  · exact h

/-- The complementary modulus of a modulus in `jacobiModulusDomain` is again in the domain. -/
lemma p22R1_comodulus_mem {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiComodulusk k ∈ jacobiModulusDomain := by
  have hsl : 1 - k ^ 2 ∈ slitPlane := by
    have := hk; rw [p22R1_domain_eq] at this; exact this.2
  refine ⟨p22R1_re_sqrt_pos hsl, fun him => ?_⟩
  have hsq := jacobiComodulusk_sq k
  set r := jacobiComodulusk k
  have hr : r = (r.re : ℂ) := by rw [← re_add_im r, him]; simp
  have hpos : 0 < r.re := p22R1_re_sqrt_pos hsl
  have hm := p22R1_sq_of_mem_domain hk
  have hk2 : k ^ 2 = ((1 - r.re ^ 2 : ℝ) : ℂ) := by
    have : k ^ 2 = 1 - r ^ 2 := by rw [hsq]; ring
    rw [this, hr]; push_cast; simp
  rw [hk2, ofReal_im, ofReal_re] at hm
  rcases hm with hm | ⟨-, hm1, -⟩
  · exact absurd rfl hm
  · nlinarith

lemma p22R1_K_comodulus (k : ℂ) : compEllIntKk (jacobiComodulusk k) = compEllIntKpk k := by
  rw [compEllIntKk, compEllIntKpk, jacobiComodulusk_sq]

lemma p22R1_Kp_comodulus (k : ℂ) : compEllIntKpk (jacobiComodulusk k) = compEllIntKk k := by
  rw [compEllIntKk, compEllIntKpk, jacobiComodulusk_sq]; ring_nf

lemma p22R1_tau_comodulus {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiTauk (jacobiComodulusk k) = -1 / jacobiTauk k := by
  have h1 := compEllIntKk_ne_zero hk
  have h2 : compEllIntKpk k ≠ 0 := by
    rw [← p22R1_K_comodulus]; exact compEllIntKk_ne_zero (p22R1_comodulus_mem hk)
  rw [jacobiTauk, jacobiTauk, p22R1_K_comodulus, p22R1_Kp_comodulus]
  field_simp
  simp [I_sq]

/-- Letter map of the modular transformation `τ ↦ -1/τ`: `s ↦ s`, `c ↦ n`, `d ↦ d`, `n ↦ c`. -/
def p22R1_sig : JacobiLetter → JacobiLetter
  | .s => .s
  | .c => .n
  | .d => .d
  | .n => .c

/-- The normalized thetas under `τ ↦ -1/τ`. -/
lemma p22R1_letter_neg_inv {τ : ℂ} (hτ : 0 < τ.im) (p : JacobiLetter) (ζ : ℂ) :
    jacobiLetterTheta p ζ τ = cexp (I * (-1 / τ) * ζ ^ 2 / π) * (if p = .s then -I else 1) *
      jacobiLetterTheta (p22R1_sig p) (ζ * (-1 / τ)) (-1 / τ) := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  have hA : (-I * τ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; push Not; intro h; exact absurd (by simpa using h) hτ0
  have t1 := DLMF.Theta.jacobiThetaOneTau_neg_inv hτ ζ
  have t2 := DLMF.Theta.jacobiThetaTwoTau_neg_inv hτ ζ
  have t3 := DLMF.Theta.jacobiThetaThreeTau_neg_inv hτ ζ
  have t4 := DLMF.Theta.jacobiThetaFourTau_neg_inv hτ ζ
  have t20 := DLMF.Theta.jacobiThetaTwoTau_neg_inv hτ 0
  have t30 := DLMF.Theta.jacobiThetaThreeTau_neg_inv hτ 0
  have t40 := DLMF.Theta.jacobiThetaFourTau_neg_inv hτ 0
  simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    zero_div, Complex.exp_zero, one_mul] at t20 t30 t40
  have n2 := je22a_thetaTwo_zero_ne_zero hτ
  have n3 := je22a_thetaThree_zero_ne_zero hτ
  have n4 := je22a_thetaFour_zero_ne_zero hτ
  set A := (-I * τ) ^ (1 / 2 : ℂ)
  set E := cexp (I * (-1 / τ) * ζ ^ 2 / π)
  cases p <;> simp only [jacobiLetterTheta, p22R1_sig, reduceCtorEq, ↓reduceIte]
  · rw [← t20, ← t30, ← t40]
    have : jacobiThetaOneTau ζ τ = -I * E * jacobiThetaOneTau (ζ * (-1 / τ)) (-1 / τ) / A := by
      rw [← t1]; field_simp
    rw [this]; field_simp
  · rw [← t20]
    have : jacobiThetaTwoTau ζ τ = E * jacobiThetaFourTau (ζ * (-1 / τ)) (-1 / τ) / A := by
      rw [← t2]; field_simp
    rw [this]; field_simp
  · rw [← t30]
    have : jacobiThetaThreeTau ζ τ = E * jacobiThetaThreeTau (ζ * (-1 / τ)) (-1 / τ) / A := by
      rw [← t3]; field_simp
    rw [this]; field_simp
  · rw [← t40]
    have : jacobiThetaFourTau ζ τ = E * jacobiThetaTwoTau (ζ * (-1 / τ)) (-1 / τ) / A := by
      rw [← t4]; field_simp
    rw [this]; field_simp

/-- General form of Jacobi's imaginary transformation. -/
lemma p22R1_imag_PQ {k : ℂ} (hk : k ∈ jacobiModulusDomain) (p q : JacobiLetter) (hpq : p ≠ q)
    (z : ℂ) : jacobiPQk p q (I * z) k =
      (if p = .s then -I else 1) / (if q = .s then -I else 1) *
        ((if p = .s then -1 else 1) * (if q = .s then -1 else 1)) *
        jacobiPQk (p22R1_sig p) (p22R1_sig q) z (jacobiComodulusk k) := by
  have hτ := jacobiTauk_im_pos hk
  have hσ : p22R1_sig p ≠ p22R1_sig q := by
    cases p <;> cases q <;> simp_all [p22R1_sig]
  have hw : jacobiZetak (I * z) k * (-1 / jacobiTauk k) = -jacobiZetak z (jacobiComodulusk k) := by
    have h1 := compEllIntKk_ne_zero hk
    have h2 : compEllIntKpk k ≠ 0 := by
      rw [← p22R1_K_comodulus]; exact compEllIntKk_ne_zero (p22R1_comodulus_mem hk)
    rw [jacobiZetak, jacobiZetak, jacobiTauk, p22R1_K_comodulus]
    field_simp
  unfold jacobiPQk jacobiGlaisher
  simp only [hpq, hσ, ↓reduceIte]
  rw [p22R1_letter_neg_inv hτ p, p22R1_letter_neg_inv hτ q, hw,
    ← p22R1_tau_comodulus hk, jacobiLetterTheta_neg, jacobiLetterTheta_neg]
  have hE : cexp (I * jacobiTauk (jacobiComodulusk k) * jacobiZetak (I * z) k ^ 2 / π) ≠ 0 :=
    exp_ne_zero _
  generalize cexp (I * jacobiTauk (jacobiComodulusk k) * jacobiZetak (I * z) k ^ 2 / π) = E
    at hE ⊢
  have hs : ∀ r : JacobiLetter, (p22R1_sig r = .s) = (r = .s) := by
    intro r; cases r <;> simp [p22R1_sig]
  simp only [hs]
  generalize jacobiLetterTheta (p22R1_sig p) (jacobiZetak z (jacobiComodulusk k))
    (jacobiTauk (jacobiComodulusk k)) = X
  generalize jacobiLetterTheta (p22R1_sig q) (jacobiZetak z (jacobiComodulusk k))
    (jacobiTauk (jacobiComodulusk k)) = Y
  by_cases hp : p = .s <;> by_cases hq : q = .s <;> simp only [hp, hq, ↓reduceIte]
  · exact absurd (hp.trans hq.symm) hpq
  all_goals rcases eq_or_ne Y 0 with rfl | hY
  all_goals first | (simp; done) | (field_simp; ring) | (simp; field_simp; done) |
    (simp; field_simp; ring_nf; simp [I_sq]; done) | (field_simp; ring_nf; simp [I_sq]; done)

/-- Table 22.6.1 (Jacobi's imaginary transformation), with the complementary
modulus `k' = √(1 - k²)` (which again lies in `jacobiModulusDomain`). Both sides have the same
poles, where both are Lean's `0`. Proof: `τ(k') = -1/τ(k)` and the theta transformations
20.7.30–20.7.33 (`θ₁ ↦ θ₁`, `θ₂ ↔ θ₄`, `θ₃ ↦ θ₃`). -/
@[dlmf 22.6.T1]
theorem jacobi_imaginary_transformation {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    let k' := jacobiComodulusk k
    jacobiSnk (I * z) k = I * jacobiSck z k' ∧ jacobiCnk (I * z) k = jacobiNck z k' ∧
      jacobiDnk (I * z) k = jacobiDck z k' ∧ jacobiCdk (I * z) k = jacobiNdk z k' ∧
      jacobiSdk (I * z) k = I * jacobiSdk z k' ∧ jacobiNdk (I * z) k = jacobiCdk z k' ∧
      jacobiDck (I * z) k = jacobiDnk z k' ∧ jacobiNck (I * z) k = jacobiCnk z k' ∧
      jacobiSck (I * z) k = I * jacobiSnk z k' ∧ jacobiNsk (I * z) k = -I * jacobiCsk z k' ∧
      jacobiDsk (I * z) k = -I * jacobiDsk z k' ∧ jacobiCsk (I * z) k = -I * jacobiNsk z k' := by
  intro k'
  simp only [jacobiSnk, jacobiCnk, jacobiDnk, jacobiCdk, jacobiSdk, jacobiNdk, jacobiDck,
    jacobiNck, jacobiSck, jacobiNsk, jacobiDsk, jacobiCsk]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [p22R1_imag_PQ hk _ _ (by decide)]; simp only [p22R1_sig, reduceCtorEq, ↓reduceIte, k'];
      try field_simp) <;> (try ring_nf) <;> (try simp [I_sq])

end DLMF.JacobiElliptic
