/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Addition
public import Carlson.Elliptic.Addition

/-!
# Jacobian elliptic functions: elementary identities (DLMF §22.6)

Sums of squares, double- and half-argument formulas and Jacobi's imaginary transformation for
the Jacobian elliptic functions in modulus form (DLMF §22.6). All identities are pointwise, at
points where the functions involved are finite (`IsJacobiRegular`) and the printed denominators
are nonzero.

## Main definitions

* `jacobiLetterModularSwap`: the letter map `s ↦ s`, `c ↦ n`, `d ↦ d`, `n ↦ c` of the modular
  transformation `τ ↦ -1/τ`.

## Main results

* `jacobi_sq_sum`: `sn² + cn² = 1` and `k² sn² + dn² = 1` (DLMF 22.6.1).
* `jacobi_sq_sum_s`, `jacobi_sq_sum_c`, `jacobi_sq_sum_d`: DLMF 22.6.2–22.6.4.
* `jacobiSn_two_mul`, `jacobiCn_two_mul`, `jacobiDn_two_mul`, `jacobiCd_two_mul`,
  `jacobiSd_two_mul`, `jacobiNd_two_mul`, `jacobiDc_two_mul`, `jacobiNc_two_mul`,
  `jacobiSc_two_mul`: the double-argument formulas DLMF 22.6.5–22.6.13.
* `jacobi_two_mul_s`, `jacobi_two_mul_ratio`: DLMF 22.6.14–22.6.16 and 22.6.17–22.6.18.
* `jacobiSn_half_sq`, `jacobiCn_half_sq`, `jacobiDn_half_sq`, `jacobiPQ_half_sq`: the
  half-argument formulas DLMF 22.6.19–22.6.22.
* `jacobiPQ_I_mul`, `jacobi_imaginary_transformation`: Jacobi's imaginary transformation,
  Table 22.6.1, with the complementary modulus `k' = √(1 - k²)`.

## Implementation notes

The sums of squares 22.6.1 are proved from the theta identities 20.7.2–20.7.3; the other sums
of squares 22.6.2–22.6.4 follow by Glaisher's relations. The double-argument formulas
22.6.5–22.6.13 are the cases `u = v` of the addition theorems 22.8.1–22.8.9 (the second forms
of 22.6.6–22.6.7 also use 22.6.1). The formulas 22.6.14–22.6.16 are proved from the theta
duplication identities; 22.6.17–22.6.18 and the half-argument formulas 22.6.19–22.6.21 follow
from 22.6.6–22.6.7 and 22.6.1, and 22.6.22 from the doubled pair sums and Glaisher quotients.
Jacobi's imaginary transformation is proved from `τ(k') = -1/τ(k)` and the theta
transformations under `τ ↦ -1/τ`.
-/

@[expose] public section

open Complex DLMF.Elliptic
open scoped Real

noncomputable section

namespace DLMF.JacobiElliptic

open DLMF.EllipticIntegrals (completeEllipticK completeEllipticKPrime)

/-- `k'² = 1 - k²` for the principal `k' = (1 - k²)^{1/2}`. -/
theorem jacobiComodulus_sq (k : ℂ) : jacobiComodulus k ^ 2 = 1 - k ^ 2 := by
  rw [jacobiComodulus, one_div]
  exact cpow_ofNat_inv_pow (1 - k ^ 2) 2

/-- `pq(z, k) ≠ 0` where the letters `p ≠ q` are both regular at `z`. -/
theorem jacobiPQ_ne_zero {p q : JacobiLetter} (hpq : p ≠ q) {z k : ℂ}
    (hp : IsJacobiRegular p z k) (hq : IsJacobiRegular q z k) : jacobiPQ p q z k ≠ 0 := by
  unfold jacobiPQ jacobiGlaisher
  simp only [hpq, ↓reduceIte]
  exact div_ne_zero hp hq

/-- DLMF 22.6.1: `sn² + cn² = 1` and `k² sn² + dn² = 1`, at points where `sn`, `cn`,
`dn` are finite. From the theta identities 20.7.2–20.7.3 and `k = θ₂²/θ₃²` (22.2.2). -/
@[dlmf 22.6.E1]
theorem jacobi_sq_sum {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : IsJacobiRegular .n z k) :
    jacobiSn z k ^ 2 + jacobiCn z k ^ 2 = 1 ∧ k ^ 2 * jacobiSn z k ^ 2 + jacobiDn z k ^ 2 = 1 :=
        by
  have hτ := jacobiTau_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hn' : jacobiThetaFourTau (jacobiThetaArgument z k) (jacobiTau k) ≠ 0 := by
    intro h; apply hn; simp [jacobiLetterTheta, h]
  simp only [jacobiSn, jacobiCn, jacobiDn, jacobiPQ, jacobiGlaisher, jacobiLetterTheta,
    reduceCtorEq, ↓reduceIte]
  rw [jacobiModulusOfTau] at hmod
  generalize jacobiThetaArgument z k = ζ at hn' ⊢
  generalize jacobiTau k = τ at hτ hn' hmod ⊢
  subst hmod
  have h2 := jacobiThetaTwoTau_zero_ne_zero hτ
  have h3 := jacobiThetaThreeTau_zero_ne_zero hτ
  have h4 := jacobiThetaFourTau_zero_ne_zero hτ
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
theorem jacobiPQ_eq_div_of_regular_n {z k : ℂ} (hn : IsJacobiRegular .n z k) :
    jacobiCs z k = jacobiCn z k / jacobiSn z k ∧ jacobiDs z k = jacobiDn z k / jacobiSn z k ∧
    jacobiNs z k = 1 / jacobiSn z k ∧ jacobiSc z k = jacobiSn z k / jacobiCn z k ∧
    jacobiDc z k = jacobiDn z k / jacobiCn z k ∧ jacobiNc z k = 1 / jacobiCn z k ∧
    jacobiSd z k = jacobiSn z k / jacobiDn z k ∧ jacobiCd z k = jacobiCn z k / jacobiDn z k ∧
    jacobiNd z k = 1 / jacobiDn z k := by
  refine ⟨jacobiPQ_eq_div (by decide) (by decide) (by decide) hn,
    jacobiPQ_eq_div (by decide) (by decide) (by decide) hn, jacobiPQ_eq_one_div _ _ _ _,
    jacobiPQ_eq_div (by decide) (by decide) (by decide) hn,
    jacobiPQ_eq_div (by decide) (by decide) (by decide) hn, jacobiPQ_eq_one_div _ _ _ _,
    jacobiPQ_eq_div (by decide) (by decide) (by decide) hn,
    jacobiPQ_eq_div (by decide) (by decide) (by decide) hn, jacobiPQ_eq_one_div _ _ _ _⟩

set_option hygiene false in
/-- Close a polynomial consequence of `h1 : sn² + cn² = 1`, `h2 : k² sn² + dn² = 1`. -/
macro "jacobi_lin_comb" : tactic => `(tactic| first
  | linear_combination h1 - h2 | linear_combination h2 - h1 | linear_combination h2
  | linear_combination -h2 | linear_combination h1 | linear_combination -h1
  | linear_combination h2 - k ^ 2 * h1 | linear_combination k ^ 2 * h1 - h2
  | linear_combination k ^ 2 * (h2 - h1) | linear_combination k ^ 2 * (h1 - h2))

/-- DLMF 22.6.2: `1 + cs²= k² + ds² = ns²`, where `sn`, `cn`, `dn` are finite and `sn ≠ 0`.
Proved from 22.6.1. -/
@[dlmf 22.6.E2]
theorem jacobi_sq_sum_s {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : IsJacobiRegular .n z k) (hs : IsJacobiRegular .s z k) :
    1 + jacobiCs z k ^ 2 = k ^ 2 + jacobiDs z k ^ 2 ∧
      k ^ 2 + jacobiDs z k ^ 2 = jacobiNs z k ^ 2 := by
  obtain ⟨h1, h2⟩ := jacobi_sq_sum hk hn
  obtain ⟨e1, e2, e3, -⟩ := jacobiPQ_eq_div_of_regular_n hn
  have hsn : jacobiSn z k ≠ 0 := jacobiPQ_ne_zero (by decide) hs hn
  rw [e1, e2, e3]
  refine ⟨?_, ?_⟩ <;> field_simp <;> jacobi_lin_comb

/-- DLMF 22.6.3: `k'² sc² + 1 = dc² = k'² nc² + k²`, where `sn`, `cn`, `dn` are finite and
`cn ≠ 0`. Proved from 22.6.1. -/
@[dlmf 22.6.E3]
theorem jacobi_sq_sum_c {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : IsJacobiRegular .n z k) (hc : IsJacobiRegular .c z k) :
    jacobiComodulus k ^ 2 * jacobiSc z k ^ 2 + 1 = jacobiDc z k ^ 2 ∧
      jacobiDc z k ^ 2 = jacobiComodulus k ^ 2 * jacobiNc z k ^ 2 + k ^ 2 := by
  obtain ⟨h1, h2⟩ := jacobi_sq_sum hk hn
  obtain ⟨-, -, -, e4, e5, e6, -⟩ := jacobiPQ_eq_div_of_regular_n hn
  have hcn : jacobiCn z k ≠ 0 := jacobiPQ_ne_zero (by decide) hc hn
  rw [e4, e5, e6, jacobiComodulus_sq]
  refine ⟨?_, ?_⟩ <;> field_simp <;> jacobi_lin_comb

/-- DLMF 22.6.4: `-k²k'² sd² = k²(cd² - 1) = k'²(1 - nd²)`, where `sn`, `cn`, `dn` are finite
and `dn ≠ 0`. Proved from 22.6.1. -/
@[dlmf 22.6.E4]
theorem jacobi_sq_sum_d {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : IsJacobiRegular .n z k) (hd : IsJacobiRegular .d z k) :
    -k ^ 2 * jacobiComodulus k ^ 2 * jacobiSd z k ^ 2 = k ^ 2 * (jacobiCd z k ^ 2 - 1) ∧
      k ^ 2 * (jacobiCd z k ^ 2 - 1) = jacobiComodulus k ^ 2 * (1 - jacobiNd z k ^ 2) := by
  obtain ⟨h1, h2⟩ := jacobi_sq_sum hk hn
  obtain ⟨-, -, -, -, -, -, e7, e8, e9⟩ := jacobiPQ_eq_div_of_regular_n hn
  have hdn : jacobiDn z k ≠ 0 := jacobiPQ_ne_zero (by decide) hd hn
  rw [e7, e8, e9, jacobiComodulus_sq]
  refine ⟨?_, ?_⟩ <;> field_simp <;> jacobi_lin_comb

/-! ### Double argument (§22.6(ii)) -/

/-- DLMF 22.6.5: `sn 2z = 2 sn cn dn/(1 - k² sn⁴)` (from the addition theorem 22.8.1). -/
@[dlmf 22.6.E5]
theorem jacobiSn_two_mul {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : IsJacobiRegular .n z k) (hden : 1 - k ^ 2 * jacobiSn z k ^ 4 ≠ 0) :
    jacobiSn (2 * z) k =
      2 * jacobiSn z k * jacobiCn z k * jacobiDn z k / (1 - k ^ 2 * jacobiSn z k ^ 4) := by
  have hd : 1 - k ^ 2 * jacobiSn z k ^ 2 * jacobiSn z k ^ 2 ≠ 0 := by
    convert hden using 2; ring
  rw [two_mul, jacobiSn_add hk hn hn hd]
  ring

/-- DLMF 22.6.6: `cn 2z = (cn² - sn² dn²)/(1 - k² sn⁴) = (cn⁴ - k'² sn⁴)/(1 - k² sn⁴)`
(from 22.8.2 and 22.6.1). -/
@[dlmf 22.6.E6]
theorem jacobiCn_two_mul {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : IsJacobiRegular .n z k) (hden : 1 - k ^ 2 * jacobiSn z k ^ 4 ≠ 0) :
    jacobiCn (2 * z) k = (jacobiCn z k ^ 2 - jacobiSn z k ^ 2 * jacobiDn z k ^ 2) /
        (1 - k ^ 2 * jacobiSn z k ^ 4) ∧
      (jacobiCn z k ^ 2 - jacobiSn z k ^ 2 * jacobiDn z k ^ 2) /
          (1 - k ^ 2 * jacobiSn z k ^ 4) =
        (jacobiCn z k ^ 4 - jacobiComodulus k ^ 2 * jacobiSn z k ^ 4) /
          (1 - k ^ 2 * jacobiSn z k ^ 4) := by
  have hd : 1 - k ^ 2 * jacobiSn z k ^ 2 * jacobiSn z k ^ 2 ≠ 0 := by
    convert hden using 2; ring
  obtain ⟨h1, h2⟩ := jacobi_sq_sum hk hn
  have hc2 : jacobiCn z k ^ 2 = 1 - jacobiSn z k ^ 2 := by linear_combination h1
  have hd2 : jacobiDn z k ^ 2 = 1 - k ^ 2 * jacobiSn z k ^ 2 := by linear_combination h2
  refine ⟨?_, ?_⟩
  · rw [two_mul, jacobiCn_add hk hn hn hd]
    ring
  · rw [jacobiComodulus_sq, show jacobiCn z k ^ 4 = (jacobiCn z k ^ 2) ^ 2 by ring, hc2, hd2]
    ring

/-- DLMF 22.6.7: `dn 2z = (dn² - k² sn² cn²)/(1 - k² sn⁴) = (dn⁴ + k²k'² sn⁴)/(1 - k² sn⁴)`
(from 22.8.3 and 22.6.1). -/
@[dlmf 22.6.E7]
theorem jacobiDn_two_mul {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : IsJacobiRegular .n z k) (hden : 1 - k ^ 2 * jacobiSn z k ^ 4 ≠ 0) :
    jacobiDn (2 * z) k = (jacobiDn z k ^ 2 - k ^ 2 * jacobiSn z k ^ 2 * jacobiCn z k ^ 2) /
        (1 - k ^ 2 * jacobiSn z k ^ 4) ∧
      (jacobiDn z k ^ 2 - k ^ 2 * jacobiSn z k ^ 2 * jacobiCn z k ^ 2) /
          (1 - k ^ 2 * jacobiSn z k ^ 4) =
        (jacobiDn z k ^ 4 + k ^ 2 * jacobiComodulus k ^ 2 * jacobiSn z k ^ 4) /
          (1 - k ^ 2 * jacobiSn z k ^ 4) := by
  have hd : 1 - k ^ 2 * jacobiSn z k ^ 2 * jacobiSn z k ^ 2 ≠ 0 := by
    convert hden using 2; ring
  obtain ⟨h1, h2⟩ := jacobi_sq_sum hk hn
  have hc2 : jacobiCn z k ^ 2 = 1 - jacobiSn z k ^ 2 := by linear_combination h1
  have hd2 : jacobiDn z k ^ 2 = 1 - k ^ 2 * jacobiSn z k ^ 2 := by linear_combination h2
  refine ⟨?_, ?_⟩
  · rw [two_mul, jacobiDn_add hk hn hn hd]
    ring
  · rw [jacobiComodulus_sq, show jacobiDn z k ^ 4 = (jacobiDn z k ^ 2) ^ 2 by ring, hc2, hd2]
    ring

/-- DLMF 22.6.8: `cd 2z = (cd² - k'² sd² nd²)/(1 + k²k'² sd⁴)` (from 22.8.4). -/
@[dlmf 22.6.E8]
theorem jacobiCd_two_mul {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hd : IsJacobiRegular .d z k)
    (hden : 1 + k ^ 2 * jacobiComodulus k ^ 2 * jacobiSd z k ^ 4 ≠ 0) :
    jacobiCd (2 * z) k =
      (jacobiCd z k ^ 2 - jacobiComodulus k ^ 2 * jacobiSd z k ^ 2 * jacobiNd z k ^ 2) /
        (1 + k ^ 2 * jacobiComodulus k ^ 2 * jacobiSd z k ^ 4) := by
  have hd' : 1 + k ^ 2 * jacobiComodulus k ^ 2 * jacobiSd z k ^ 2 * jacobiSd z k ^ 2 ≠ 0 := by
    convert hden using 2; ring
  rw [two_mul, jacobiCd_add hk hd hd hd']
  ring

/-- DLMF 22.6.9: `sd 2z = 2 sd cd nd/(1 + k²k'² sd⁴)` (from 22.8.5). -/
@[dlmf 22.6.E9]
theorem jacobiSd_two_mul {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hd : IsJacobiRegular .d z k)
    (hden : 1 + k ^ 2 * jacobiComodulus k ^ 2 * jacobiSd z k ^ 4 ≠ 0) :
    jacobiSd (2 * z) k = 2 * jacobiSd z k * jacobiCd z k * jacobiNd z k /
      (1 + k ^ 2 * jacobiComodulus k ^ 2 * jacobiSd z k ^ 4) := by
  have hd' : 1 + k ^ 2 * jacobiComodulus k ^ 2 * jacobiSd z k ^ 2 * jacobiSd z k ^ 2 ≠ 0 := by
    convert hden using 2; ring
  rw [two_mul, jacobiSd_add hk hd hd hd']
  ring

/-- DLMF 22.6.10: `nd 2z = (nd² + k² sd² cd²)/(1 + k²k'² sd⁴)` (from 22.8.6). -/
@[dlmf 22.6.E10]
theorem jacobiNd_two_mul {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hd : IsJacobiRegular .d z k)
    (hden : 1 + k ^ 2 * jacobiComodulus k ^ 2 * jacobiSd z k ^ 4 ≠ 0) :
    jacobiNd (2 * z) k = (jacobiNd z k ^ 2 + k ^ 2 * jacobiSd z k ^ 2 * jacobiCd z k ^ 2) /
      (1 + k ^ 2 * jacobiComodulus k ^ 2 * jacobiSd z k ^ 4) := by
  have hd' : 1 + k ^ 2 * jacobiComodulus k ^ 2 * jacobiSd z k ^ 2 * jacobiSd z k ^ 2 ≠ 0 := by
    convert hden using 2; ring
  rw [two_mul, jacobiNd_add hk hd hd hd']
  ring

/-- DLMF 22.6.11: `dc 2z = (dc² + k'² sc² nc²)/(1 - k'² sc⁴)` (from 22.8.7). -/
@[dlmf 22.6.E11]
theorem jacobiDc_two_mul {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hc : IsJacobiRegular .c z k) (hden : 1 - jacobiComodulus k ^ 2 * jacobiSc z k ^ 4 ≠ 0) :
    jacobiDc (2 * z) k =
      (jacobiDc z k ^ 2 + jacobiComodulus k ^ 2 * jacobiSc z k ^ 2 * jacobiNc z k ^ 2) /
        (1 - jacobiComodulus k ^ 2 * jacobiSc z k ^ 4) := by
  have hd' : 1 - jacobiComodulus k ^ 2 * jacobiSc z k ^ 2 * jacobiSc z k ^ 2 ≠ 0 := by
    convert hden using 2; ring
  rw [two_mul, jacobiDc_add hk hc hc hd']
  ring

/-- DLMF 22.6.12: `nc 2z = (nc² + sc² dc²)/(1 - k'² sc⁴)` (from 22.8.8). -/
@[dlmf 22.6.E12]
theorem jacobiNc_two_mul {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hc : IsJacobiRegular .c z k) (hden : 1 - jacobiComodulus k ^ 2 * jacobiSc z k ^ 4 ≠ 0) :
    jacobiNc (2 * z) k = (jacobiNc z k ^ 2 + jacobiSc z k ^ 2 * jacobiDc z k ^ 2) /
      (1 - jacobiComodulus k ^ 2 * jacobiSc z k ^ 4) := by
  have hd' : 1 - jacobiComodulus k ^ 2 * jacobiSc z k ^ 2 * jacobiSc z k ^ 2 ≠ 0 := by
    convert hden using 2; ring
  rw [two_mul, jacobiNc_add hk hc hc hd']
  ring

/-- DLMF 22.6.13: `sc 2z = 2 sc dc nc/(1 - k'² sc⁴)` (from 22.8.9). -/
@[dlmf 22.6.E13]
theorem jacobiSc_two_mul {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hc : IsJacobiRegular .c z k) (hden : 1 - jacobiComodulus k ^ 2 * jacobiSc z k ^ 4 ≠ 0) :
    jacobiSc (2 * z) k = 2 * jacobiSc z k * jacobiDc z k * jacobiNc z k /
      (1 - jacobiComodulus k ^ 2 * jacobiSc z k ^ 4) := by
  have hd' : 1 - jacobiComodulus k ^ 2 * jacobiSc z k ^ 2 * jacobiSc z k ^ 2 ≠ 0 := by
    convert hden using 2; ring
  rw [two_mul, jacobiSc_add hk hc hc hd']
  ring

local notation "θ₁" => jacobiThetaOneTau
local notation "θ₂" => jacobiThetaTwoTau
local notation "θ₃" => jacobiThetaThreeTau
local notation "θ₄" => jacobiThetaFourTau

/-- `1 - k² sn⁴ z ≠ 0` where `sn` is finite at `z` and `2z` (helper). -/
private lemma one_sub_sq_mul_jacobiSn_pow_four_ne_zero {k : ℂ}
    (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : IsJacobiRegular .n z k) (hn2 : IsJacobiRegular .n (2 * z) k) :
    1 - k ^ 2 * jacobiSn z k ^ 4 ≠ 0 := by
  have hτ := jacobiTau_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hu' : θ₄ (jacobiThetaArgument z k) (jacobiTau k) ≠ 0 := by
    intro h'; apply hn; simp [jacobiLetterTheta, h']
  have hu2 : θ₄ (jacobiThetaArgument (2 * z) k) (jacobiTau k) ≠ 0 := by
    intro h'; apply hn2; simp [jacobiLetterTheta, h']
  have h2z : jacobiThetaArgument (2 * z) k = jacobiThetaArgument z k + jacobiThetaArgument z k := by
    simp only [jacobiThetaArgument]; ring
  rw [h2z] at hu2
  simp only [jacobiSn, jacobiPQ, jacobiGlaisher, jacobiLetterTheta, reduceCtorEq, ↓reduceIte]
  rw [jacobiModulusOfTau] at hmod
  generalize jacobiThetaArgument z k = x at hu' hu2 ⊢
  generalize jacobiTau k = τ at hτ hu' hu2 hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  have N4 := jacobiThetaFourTau_add_mul_jacobiThetaFourTau_sub x x τ hτ
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
    (hs : IsJacobiRegular .s z k)
    (hden : 2 * jacobiCs z k * jacobiDs z k * jacobiNs z k ≠ 0) :
    jacobiNs (2 * z) k = (jacobiNs z k ^ 4 - k ^ 2) /
        (2 * jacobiCs z k * jacobiDs z k * jacobiNs z k) ∧
      jacobiDs (2 * z) k = (k ^ 2 * jacobiComodulus k ^ 2 + jacobiDs z k ^ 4) /
        (2 * jacobiCs z k * jacobiDs z k * jacobiNs z k) ∧
      jacobiCs (2 * z) k = (jacobiCs z k ^ 4 - jacobiComodulus k ^ 2) /
        (2 * jacobiCs z k * jacobiDs z k * jacobiNs z k) := by
  have hτ := jacobiTau_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hu' : θ₁ (jacobiThetaArgument z k) (jacobiTau k) ≠ 0 := by
    intro h'; apply hs; simp [jacobiLetterTheta, h']
  simp only [eq_div_iff hden]
  rw [← (jacobi_inversion_k hk).2.1]
  have h2z : jacobiThetaArgument (2 * z) k = jacobiThetaArgument z k + jacobiThetaArgument z k := by
    simp only [jacobiThetaArgument]; ring
  simp only [jacobiNs, jacobiDs, jacobiCs, jacobiPQ, jacobiGlaisher, jacobiLetterTheta,
    jacobiComodulusOfTau, reduceCtorEq, ↓reduceIte, h2z] at hden ⊢
  rw [jacobiModulusOfTau] at hmod
  generalize jacobiThetaArgument z k = x at hu' hden ⊢
  generalize jacobiTau k = τ at hτ hu' hden hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  have hx2 : θ₂ x τ ≠ 0 := by intro h0; apply hden; simp [h0]
  have hx3 : θ₃ x τ ≠ 0 := by intro h0; apply hden; simp [h0]
  have hx4 : θ₄ x τ ≠ 0 := by intro h0; apply hden; simp [h0]
  have dup := jacobiThetaOneTau_add_mul_jacobiThetaFourTau_sub x x τ hτ
  rw [sub_self] at dup
  have hD : θ₁ (x + x) τ ≠ 0 := by
    intro h0
    rw [h0] at dup
    have : θ₁ x τ * θ₄ x τ * (θ₂ x τ * θ₃ x τ) = 0 := by linear_combination -dup / 2
    simp [hu', hx2, hx3, hx4] at this
  have N4 := jacobiThetaFourTau_add_mul_jacobiThetaFourTau_sub x x τ hτ
  have N3 := jacobiThetaThreeTau_add_mul_jacobiThetaThreeTau_sub x x τ hτ
  have N2 := jacobiThetaTwoTau_add_mul_jacobiThetaTwoTau_sub x x τ hτ
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
    (hn : IsJacobiRegular .n z k) (hn2 : IsJacobiRegular .n (2 * z) k)
    (hc : jacobiCn z k ≠ 0) (hd : jacobiDn z k ≠ 0)
    (hc2 : 1 + jacobiCn (2 * z) k ≠ 0) (hd2 : 1 + jacobiDn (2 * z) k ≠ 0) :
    (1 - jacobiCn (2 * z) k) / (1 + jacobiCn (2 * z) k) =
        jacobiSn z k ^ 2 * jacobiDn z k ^ 2 / jacobiCn z k ^ 2 ∧
      (1 - jacobiDn (2 * z) k) / (1 + jacobiDn (2 * z) k) =
        k ^ 2 * jacobiSn z k ^ 2 * jacobiCn z k ^ 2 / jacobiDn z k ^ 2 := by
  have hD := one_sub_sq_mul_jacobiSn_pow_four_ne_zero hk hn hn2
  obtain ⟨h1, h2⟩ := jacobi_sq_sum hk hn
  rw [(jacobiCn_two_mul hk hn hD).1] at hc2 ⊢
  rw [(jacobiDn_two_mul hk hn hD).1] at hd2 ⊢
  have hD' : 1 - jacobiSn z k ^ 4 * k ^ 2 ≠ 0 := by rwa [mul_comm] at hD
  constructor
  · rw [div_eq_div_iff hc2 (pow_ne_zero 2 hc)]
    field_simp
    linear_combination (-(jacobiCn z k) ^ 2 - k ^ 2 * (jacobiSn z k) ^ 4 +
        (jacobiSn z k) ^ 2) * h1 +
      ((jacobiDn z k) ^ 2 * (jacobiSn z k) ^ 4 + (jacobiSn z k) ^ 4 - (jacobiSn z k) ^ 2) * h2
  · rw [div_eq_div_iff hd2 (pow_ne_zero 2 hd)]
    field_simp
    linear_combination ((jacobiCn z k) ^ 2 * k ^ 4 * (jacobiSn z k) ^ 4 +
        k ^ 4 * (jacobiSn z k) ^ 4 -
      k ^ 2 * (jacobiSn z k) ^ 2) * h1 +
      (-(jacobiDn z k) ^ 2 - k ^ 2 * (jacobiSn z k) ^ 4 + k ^ 2 * (jacobiSn z k) ^ 2) * h2

/-! ### Half argument (§22.6(iii)) -/

/-- DLMF 22.6.19: `sn²(z/2) = (1 - cn z)/(1 + dn z) = (1 - dn z)/(k²(1 + cn z))
= (dn z - k² cn z - k'²)/(k²(dn z - cn z))`, where the functions are finite at `z/2`, `z` and
the denominators are nonzero. -/
@[dlmf 22.6.E19]
theorem jacobiSn_half_sq {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : IsJacobiRegular .n z k) (hn2 : IsJacobiRegular .n (z / 2) k)
    (h1 : 1 + jacobiDn z k ≠ 0) (h2 : 1 + jacobiCn z k ≠ 0)
    (h3 : jacobiDn z k - jacobiCn z k ≠ 0) :
    jacobiSn (z / 2) k ^ 2 = (1 - jacobiCn z k) / (1 + jacobiDn z k) ∧
      jacobiSn (z / 2) k ^ 2 = (1 - jacobiDn z k) / (k ^ 2 * (1 + jacobiCn z k)) ∧
      jacobiSn (z / 2) k ^ 2 = (jacobiDn z k - k ^ 2 * jacobiCn z k - jacobiComodulus k ^ 2) /
        (k ^ 2 * (jacobiDn z k - jacobiCn z k)) := by
  have hk0 : k ≠ 0 := by
    rintro rfl; simp [jacobiModulusDomain] at hk
  obtain ⟨w, rfl⟩ : ∃ w, z = 2 * w := ⟨z / 2, by ring⟩
  have hw : 2 * w / 2 = w := by ring
  rw [hw] at hn2 ⊢
  have hD := one_sub_sq_mul_jacobiSn_pow_four_ne_zero hk hn2 hn
  have hD' : 1 - jacobiSn w k ^ 4 * k ^ 2 ≠ 0 := by rwa [mul_comm] at hD
  obtain ⟨e1, e2⟩ := jacobi_sq_sum hk hn2
  have hK := jacobiComodulus_sq k
  simp only [(jacobiCn_two_mul hk hn2 hD).1, (jacobiDn_two_mul hk hn2 hD).1] at h1 h2 h3 ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [eq_div_iff (by assumption)]
    field_simp
    linear_combination (-k ^ 2 * (jacobiSn w k) ^ 4 + 1) * e1
  · rw [eq_div_iff (mul_ne_zero (pow_ne_zero 2 hk0) (by assumption))]
    field_simp
    linear_combination (-k ^ 2 * (jacobiSn w k) ^ 4 + 1) * e2
  · rw [eq_div_iff (mul_ne_zero (pow_ne_zero 2 hk0) (by assumption))]
    field_simp
    linear_combination (-k ^ 4 * (jacobiSn w k) ^ 4 + k ^ 2) * e1 +
      (k ^ 2 * (jacobiSn w k) ^ 4 - 1) * e2 +
      (-k ^ 2 * (jacobiSn w k) ^ 4 + 1) * hK

/-- DLMF 22.6.20: `cn²(z/2) = (-k'² + dn z + k² cn z)/(k²(1 + cn z))
= k'²(1 - dn z)/(k²(dn z - cn z)) = k'²(1 + cn z)/(k'² + dn z - k² cn z)`. -/
@[dlmf 22.6.E20]
theorem jacobiCn_half_sq {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : IsJacobiRegular .n z k) (hn2 : IsJacobiRegular .n (z / 2) k)
    (h1 : 1 + jacobiCn z k ≠ 0) (h2 : jacobiDn z k - jacobiCn z k ≠ 0)
    (h3 : jacobiComodulus k ^ 2 + jacobiDn z k - k ^ 2 * jacobiCn z k ≠ 0) :
    jacobiCn (z / 2) k ^ 2 = (-jacobiComodulus k ^ 2 + jacobiDn z k + k ^ 2 * jacobiCn z k) /
        (k ^ 2 * (1 + jacobiCn z k)) ∧
      jacobiCn (z / 2) k ^ 2 = jacobiComodulus k ^ 2 * (1 - jacobiDn z k) /
        (k ^ 2 * (jacobiDn z k - jacobiCn z k)) ∧
      jacobiCn (z / 2) k ^ 2 = jacobiComodulus k ^ 2 * (1 + jacobiCn z k) /
        (jacobiComodulus k ^ 2 + jacobiDn z k - k ^ 2 * jacobiCn z k) := by
  have hk0 : k ≠ 0 := by
    rintro rfl; simp [jacobiModulusDomain] at hk
  obtain ⟨w, rfl⟩ : ∃ w, z = 2 * w := ⟨z / 2, by ring⟩
  have hw : 2 * w / 2 = w := by ring
  rw [hw] at hn2 ⊢
  have hD := one_sub_sq_mul_jacobiSn_pow_four_ne_zero hk hn2 hn
  have hD' : 1 - jacobiSn w k ^ 4 * k ^ 2 ≠ 0 := by rwa [mul_comm] at hD
  obtain ⟨e1, e2⟩ := jacobi_sq_sum hk hn2
  have hK := jacobiComodulus_sq k
  simp only [(jacobiCn_two_mul hk hn2 hD).1, (jacobiDn_two_mul hk hn2 hD).1] at h1 h2 h3 ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [eq_div_iff (mul_ne_zero (pow_ne_zero 2 hk0) (by assumption))]
    field_simp
    linear_combination ((jacobiCn w k) ^ 2 * k ^ 2 -
        (jacobiDn w k) ^ 2 * k ^ 2 * (jacobiSn w k) ^ 2 - k ^ 4 * (jacobiSn w k) ^ 4 +
            k ^ 2) * e1 +
      (k ^ 2 * (jacobiSn w k) ^ 4 - 1) * e2 +
      (-k ^ 2 * (jacobiSn w k) ^ 4 + 1) * hK
  · rw [eq_div_iff (mul_ne_zero (pow_ne_zero 2 hk0) (by assumption))]
    field_simp
    linear_combination (-(jacobiCn w k) ^ 2 * k ^ 4 * (jacobiSn w k) ^ 2 -
        (jacobiCn w k) ^ 2 * k ^ 2 + (jacobiDn w k) ^ 2 * k ^ 2 * (jacobiSn w k) ^ 2 +
            (jacobiDn w k) ^ 2 * k ^ 2 +
                k ^ 4 * (jacobiSn w k) ^ 4 - k ^ 4 * (jacobiSn w k) ^ 2 -
                    k ^ 2 * (jacobiComodulus k) ^ 2 * (jacobiSn w k) ^ 2 +
                        k ^ 2 * (jacobiSn w k) ^ 2 - k ^ 2) * e1 +
      (-k ^ 2 * (jacobiSn w k) ^ 4 + k ^ 2 + (jacobiComodulus k) ^ 2) * e2 +
      (2 * k ^ 2 * (jacobiSn w k) ^ 4 - 2 * k ^ 2 * (jacobiSn w k) ^ 2) * hK
  · rw [eq_div_iff (by assumption)]
    field_simp
    linear_combination (-(jacobiCn w k) ^ 2 * k ^ 2 * (jacobiSn w k) ^ 2 -
        (jacobiCn w k) ^ 2 * k ^ 2 + (jacobiDn w k) ^ 2 * k ^ 2 * (jacobiSn w k) ^ 2 +
            (jacobiDn w k) ^ 2 - k ^ 2 * (jacobiComodulus k) ^ 2 * (jacobiSn w k) ^ 4 +
                k ^ 2 * (jacobiSn w k) ^ 4 - k ^ 2) * e1 +
      (-k ^ 2 * (jacobiSn w k) ^ 4 + k ^ 2 * (jacobiSn w k) ^ 2 +
          (jacobiComodulus k) ^ 2 * (jacobiSn w k) ^ 2 - (jacobiSn w k) ^ 2 + 1) * e2 +
      (k ^ 2 * (jacobiSn w k) ^ 6 - k ^ 2 * (jacobiSn w k) ^ 4 + (jacobiSn w k) ^ 2 - 1) * hK

/-- DLMF 22.6.21: `dn²(z/2) = (k² cn z + dn z + k'²)/(1 + dn z)
= k'²(1 - cn z)/(dn z - cn z) = k'²(1 + dn z)/(k'² + dn z - k² cn z)`. -/
@[dlmf 22.6.E21]
theorem jacobiDn_half_sq {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : IsJacobiRegular .n z k) (hn2 : IsJacobiRegular .n (z / 2) k)
    (h1 : 1 + jacobiDn z k ≠ 0) (h2 : jacobiDn z k - jacobiCn z k ≠ 0)
    (h3 : jacobiComodulus k ^ 2 + jacobiDn z k - k ^ 2 * jacobiCn z k ≠ 0) :
    jacobiDn (z / 2) k ^ 2 = (k ^ 2 * jacobiCn z k + jacobiDn z k + jacobiComodulus k ^ 2) /
        (1 + jacobiDn z k) ∧
      jacobiDn (z / 2) k ^ 2 = jacobiComodulus k ^ 2 * (1 - jacobiCn z k) /
        (jacobiDn z k - jacobiCn z k) ∧
      jacobiDn (z / 2) k ^ 2 = jacobiComodulus k ^ 2 * (1 + jacobiDn z k) /
        (jacobiComodulus k ^ 2 + jacobiDn z k - k ^ 2 * jacobiCn z k) := by
  have hk0 : k ≠ 0 := by
    rintro rfl; simp [jacobiModulusDomain] at hk
  obtain ⟨w, rfl⟩ : ∃ w, z = 2 * w := ⟨z / 2, by ring⟩
  have hw : 2 * w / 2 = w := by ring
  rw [hw] at hn2 ⊢
  have hD := one_sub_sq_mul_jacobiSn_pow_four_ne_zero hk hn2 hn
  have hD' : 1 - jacobiSn w k ^ 4 * k ^ 2 ≠ 0 := by rwa [mul_comm] at hD
  obtain ⟨e1, e2⟩ := jacobi_sq_sum hk hn2
  have hK := jacobiComodulus_sq k
  simp only [(jacobiCn_two_mul hk hn2 hD).1, (jacobiDn_two_mul hk hn2 hD).1] at h1 h2 h3 ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [eq_div_iff (by assumption)]
    field_simp
    linear_combination (-(jacobiDn w k) ^ 2 * k ^ 2 * (jacobiSn w k) ^ 2 +
        k ^ 2 * (jacobiSn w k) ^ 2 - k ^ 2) * e1 +
      ((jacobiDn w k) ^ 2 - k ^ 2 * (jacobiSn w k) ^ 2 + 1) * e2 +
      (k ^ 2 * (jacobiSn w k) ^ 4 - 1) * hK
  · rw [eq_div_iff (by assumption)]
    field_simp
    linear_combination (-(jacobiDn w k) ^ 2 * k ^ 2 * (jacobiSn w k) ^ 2 - (jacobiDn w k) ^ 2 +
        (jacobiComodulus k) ^ 2) * e1 +
      ((jacobiDn w k) ^ 2 * (jacobiSn w k) ^ 2 +
          (jacobiDn w k) ^ 2 - 2 * k ^ 2 * (jacobiSn w k) ^ 2 -
              (jacobiComodulus k) ^ 2 * (jacobiSn w k) ^ 2 + 2 * (jacobiSn w k) ^ 2) * e2 +
      (2 * k ^ 2 * (jacobiSn w k) ^ 4 - 2 * (jacobiSn w k) ^ 2) * hK
  · rw [eq_div_iff (by assumption)]
    field_simp
    linear_combination (-(jacobiDn w k) ^ 2 * k ^ 2 * (jacobiSn w k) ^ 2 -
        (jacobiDn w k) ^ 2 * k ^ 2 + k ^ 2 * (jacobiComodulus k) ^ 2 * (jacobiSn w k) ^ 2) * e1 +
      ((jacobiDn w k) ^ 2 * k ^ 2 * (jacobiSn w k) ^ 2 +
          (jacobiDn w k) ^ 2 - k ^ 4 * (jacobiSn w k) ^ 4 -
              k ^ 2 * (jacobiComodulus k) ^ 2 * (jacobiSn w k) ^ 4 +
                  k ^ 2 * (jacobiSn w k) ^ 4 - k ^ 2 + 1) * e2 +
      (k ^ 4 * (jacobiSn w k) ^ 6 - k ^ 2 * (jacobiSn w k) ^ 4 +
          k ^ 2 * (jacobiSn w k) ^ 2 - 1) * hK

/-- Doubled Jacobi cosine and delta pair sums in terms of the half-argument values. -/
private lemma jacobiCn_jacobiDn_two_mul_pair_sums {k w : ℂ} (hk : k ∈ jacobiModulusDomain)
    (hn : IsJacobiRegular .n w k) (hn2 : IsJacobiRegular .n (2 * w) k) :
    let D := 1 - k ^ 2 * jacobiSn w k ^ 4
    D * (jacobiCn (2 * w) k + 1) = 2 * jacobiCn w k ^ 2 ∧
      D * (jacobiDn (2 * w) k + 1) = 2 * jacobiDn w k ^ 2 ∧
      D * (jacobiCn (2 * w) k + jacobiDn (2 * w) k) =
        2 * jacobiCn w k ^ 2 * jacobiDn w k ^ 2 := by
  have hD := one_sub_sq_mul_jacobiSn_pow_four_ne_zero hk hn hn2
  have e1 := (jacobi_sq_sum hk hn).1
  have e2 := (jacobi_sq_sum hk hn).2
  have ec := (jacobiCn_two_mul hk hn hD).1
  have ed := (jacobiDn_two_mul hk hn hD).1
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [ec]; field_simp
    linear_combination -e1 - jacobiSn w k ^ 2 * e2
  · rw [ed]; field_simp
    linear_combination -e2 - k ^ 2 * jacobiSn w k ^ 2 * e1
  · rw [ec, ed]; field_simp
    linear_combination (-2 * jacobiDn w k ^ 2 - jacobiSn w k ^ 2 * k ^ 2 + 1) * e1 +
      (jacobiSn w k ^ 2 - 1) * e2

/-- DLMF 22.6.22: for a permutation `{p, q, r}` of `{c, d, n}`,
`pq²(z/2) = (ps + rs)/(qs + rs) = (pq + rq)/(1 + rq) = (pr + 1)/(qr + 1)`, where all twelve
functions are finite at `z/2` and `z` and the denominators are nonzero. -/
@[dlmf 22.6.E22]
theorem jacobiPQ_half_sq {k : ℂ} (hk : k ∈ jacobiModulusDomain) {p q r : JacobiLetter}
    (hp : p ≠ .s) (hq : q ≠ .s) (hr : r ≠ .s) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) {z : ℂ}
    (hz : ∀ l, IsJacobiRegular l z k) (hz2 : ∀ l, IsJacobiRegular l (z / 2) k)
    (h1 : jacobiPQ q .s z k + jacobiPQ r .s z k ≠ 0) (h2 : 1 + jacobiPQ r q z k ≠ 0)
    (h3 : jacobiPQ q r z k + 1 ≠ 0) :
    jacobiPQ p q (z / 2) k ^ 2 =
        (jacobiPQ p .s z k + jacobiPQ r .s z k) / (jacobiPQ q .s z k + jacobiPQ r .s z k) ∧
      jacobiPQ p q (z / 2) k ^ 2 =
        (jacobiPQ p q z k + jacobiPQ r q z k) / (1 + jacobiPQ r q z k) ∧
      jacobiPQ p q (z / 2) k ^ 2 = (jacobiPQ p r z k + 1) / (jacobiPQ q r z k + 1) := by
  obtain ⟨w, rfl⟩ : ∃ w, z = 2 * w := ⟨z / 2, by ring⟩
  have hw : 2 * w / 2 = w := by ring
  simp only [hw] at hz2 ⊢
  have hn : IsJacobiRegular .n w k := hz2 .n
  have hn2 : IsJacobiRegular .n (2 * w) k := hz .n
  have hD := one_sub_sq_mul_jacobiSn_pow_four_ne_zero hk hn hn2
  let D : ℂ := 1 - k ^ 2 * jacobiSn w k ^ 4
  have hsum := jacobiCn_jacobiDn_two_mul_pair_sums hk hn hn2
  change D * (jacobiCn (2 * w) k + 1) = 2 * jacobiCn w k ^ 2 ∧
    D * (jacobiDn (2 * w) k + 1) = 2 * jacobiDn w k ^ 2 ∧
    D * (jacobiCn (2 * w) k + jacobiDn (2 * w) k) =
      2 * jacobiCn w k ^ 2 * jacobiDn w k ^ 2 at hsum
  obtain ⟨gcn, gdn, gcd⟩ := hsum
  have hc0 : jacobiCn w k ≠ 0 := jacobiPQ_ne_zero (by decide) (hz2 .c) hn
  have hd0 : jacobiDn w k ≠ 0 := jacobiPQ_ne_zero (by decide) (hz2 .d) hn
  have hS0 : jacobiSn (2 * w) k ≠ 0 := jacobiPQ_ne_zero (by decide) (hz .s) hn2
  have hC0 : jacobiCn (2 * w) k ≠ 0 := jacobiPQ_ne_zero (by decide) (hz .c) hn2
  have hD0 : jacobiDn (2 * w) k ≠ 0 := jacobiPQ_ne_zero (by decide) (hz .d) hn2
  have hdn : jacobiDn (2 * w) k + 1 ≠ 0 := by
    intro hz0; rw [hz0, mul_zero] at gdn
    exact (mul_ne_zero (by norm_num) (pow_ne_zero 2 hd0)) gdn.symm
  have hcn : jacobiCn (2 * w) k + 1 ≠ 0 := by
    intro hz0; rw [hz0, mul_zero] at gcn
    exact (mul_ne_zero (by norm_num) (pow_ne_zero 2 hc0)) gcn.symm
  have hcd : jacobiCn (2 * w) k + jacobiDn (2 * w) k ≠ 0 := by
    intro hz0; rw [hz0, mul_zero] at gcd
    exact (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hc0))
      (pow_ne_zero 2 hd0)) gcd.symm
  have hcross1 : jacobiCn w k ^ 2 * (jacobiDn (2 * w) k + 1) =
      jacobiDn w k ^ 2 * (jacobiCn (2 * w) k + 1) := by
    apply mul_left_cancel₀ hD
    dsimp only [D] at gcn gdn
    linear_combination jacobiCn w k ^ 2 * gdn - jacobiDn w k ^ 2 * gcn
  have hcross2 : jacobiCn w k ^ 2 * (jacobiDn (2 * w) k + 1) =
      jacobiCn (2 * w) k + jacobiDn (2 * w) k := by
    apply mul_left_cancel₀ hD
    dsimp only [D] at gdn gcd
    linear_combination jacobiCn w k ^ 2 * gdn - gcd
  have hcross3 : jacobiDn w k ^ 2 * (jacobiCn (2 * w) k + 1) =
      jacobiCn (2 * w) k + jacobiDn (2 * w) k := by
    apply mul_left_cancel₀ hD
    dsimp only [D] at gcn gcd
    linear_combination jacobiDn w k ^ 2 * gcn - gcd
  have Rcd : (jacobiCn w k / jacobiDn w k) ^ 2 =
      (jacobiCn (2 * w) k + 1) / (jacobiDn (2 * w) k + 1) := by
    rw [eq_div_iff hdn, div_pow]
    field_simp
    exact hcross1
  have Rcn : jacobiCn w k ^ 2 =
      (jacobiCn (2 * w) k + jacobiDn (2 * w) k) / (jacobiDn (2 * w) k + 1) :=
    (eq_div_iff hdn).2 hcross2
  have Rdc : (jacobiDn w k / jacobiCn w k) ^ 2 =
      (jacobiDn (2 * w) k + 1) / (jacobiCn (2 * w) k + 1) := by
    rw [eq_div_iff hcn, div_pow]
    field_simp
    exact hcross1.symm
  have Rdn : jacobiDn w k ^ 2 =
      (jacobiCn (2 * w) k + jacobiDn (2 * w) k) / (jacobiCn (2 * w) k + 1) :=
    (eq_div_iff hcn).2 hcross3
  have Rnc : (1 / jacobiCn w k) ^ 2 =
      (jacobiDn (2 * w) k + 1) / (jacobiCn (2 * w) k + jacobiDn (2 * w) k) := by
    rw [eq_div_iff hcd, div_pow]
    field_simp
    exact hcross2.symm
  have Rnd : (1 / jacobiDn w k) ^ 2 =
      (jacobiCn (2 * w) k + 1) / (jacobiCn (2 * w) k + jacobiDn (2 * w) k) := by
    rw [eq_div_iff hcd, div_pow]
    field_simp
    exact hcross3.symm
  have eG := jacobiPQ_eq_div_of_regular_n hn2
  have eGw := jacobiPQ_eq_div_of_regular_n hn
  cases p <;> cases q <;> cases r <;>
    try
      exfalso
      first
        | exact hp rfl | exact hq rfl | exact hr rfl
        | exact hpq rfl | exact hpr rfl | exact hqr rfl
  all_goals have hCsk (t : ℂ) : jacobiPQ .c .s t k = jacobiCs t k := rfl
  all_goals have hDsk (t : ℂ) : jacobiPQ .d .s t k = jacobiDs t k := rfl
  all_goals have hNsk (t : ℂ) : jacobiPQ .n .s t k = jacobiNs t k := rfl
  all_goals have hDck (t : ℂ) : jacobiPQ .d .c t k = jacobiDc t k := rfl
  all_goals have hNck (t : ℂ) : jacobiPQ .n .c t k = jacobiNc t k := rfl
  all_goals have hCdk (t : ℂ) : jacobiPQ .c .d t k = jacobiCd t k := rfl
  all_goals have hNdk (t : ℂ) : jacobiPQ .n .d t k = jacobiNd t k := rfl
  all_goals have hCnk (t : ℂ) : jacobiPQ .c .n t k = jacobiCn t k := rfl
  all_goals have hDnk (t : ℂ) : jacobiPQ .d .n t k = jacobiDn t k := rfl
  all_goals simp only [hCsk, hDsk, hNsk, hDck, hNck, hCdk, hNdk, hCnk, hDnk] at h1 h2 h3 ⊢
  all_goals obtain ⟨gcs, gds, gns, _, gdc, gnc, _, gcd, gnd⟩ := eG
  all_goals obtain ⟨_, _, _, _, wdc, wnc, _, wcd, wnd⟩ := eGw
  all_goals simp only [gcs, gds, gns, gdc, gnc, gcd, gnd, wdc, wnc, wcd, wnd] at h1 h2 h3 ⊢
  all_goals first | rw [Rcd] | rw [Rdc] | rw [Rnc] | rw [Rnd] | rw [Rcn] | rw [Rdn]
  all_goals refine ⟨?_, ?_, ?_⟩
  all_goals
    have hdc : jacobiDn (2 * w) k + jacobiCn (2 * w) k ≠ 0 := by
      simpa only [add_comm] using hcd
  all_goals field_simp [hcd, hdc, hcn, hdn, hS0, hC0, hD0, hc0, hd0, h1, h2, h3]
  all_goals ring

/-! ### Jacobi's imaginary transformation (§22.6(iv), Table 22.6.1) -/

/-- The complementary modulus of a modulus in `jacobiModulusDomain` is again in the domain. -/
theorem jacobiComodulus_mem_jacobiModulusDomain {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiComodulus k ∈ jacobiModulusDomain := by
  have hsl : 1 - k ^ 2 ∈ slitPlane := by
    have := hk; rw [jacobiModulusDomain_eq] at this; exact this.2
  refine ⟨Carlson.re_cpow_half_pos hsl, fun him => ?_⟩
  have hsq := jacobiComodulus_sq k
  set r := jacobiComodulus k
  have hr : r = (r.re : ℂ) := by rw [← re_add_im r, him]; simp
  have hpos : 0 < r.re := Carlson.re_cpow_half_pos hsl
  have hm := sq_im_ne_zero_or_mem_Ioo_of_mem_jacobiModulusDomain hk
  have hk2 : k ^ 2 = ((1 - r.re ^ 2 : ℝ) : ℂ) := by
    have : k ^ 2 = 1 - r ^ 2 := by rw [hsq]; ring
    rw [this, hr]; push_cast; simp
  rw [hk2, ofReal_im, ofReal_re] at hm
  rcases hm with hm | ⟨-, hm1, -⟩
  · exact absurd rfl hm
  · nlinarith

/-- Identity under the stated parameter and domain assumptions:
`completeEllipticK (jacobiComodulus k) = completeEllipticKPrime k`. -/
theorem completeEllipticK_jacobiComodulus_eq_completeEllipticKPrime (k : ℂ) : completeEllipticK
    (jacobiComodulus k) =
    completeEllipticKPrime k := by
  rw [completeEllipticK, completeEllipticKPrime, jacobiComodulus_sq]

/-- Identity under the stated parameter and domain assumptions:
`completeEllipticKPrime (jacobiComodulus k) = completeEllipticK k`. -/
private lemma completeEllipticKPrime_jacobiComodulus_eq_completeEllipticK (k : ℂ) :
    completeEllipticKPrime
    (jacobiComodulus k) = completeEllipticK k := by
  rw [completeEllipticK, completeEllipticKPrime, jacobiComodulus_sq]; ring_nf

/-- Identity under the stated parameter and domain assumptions: `jacobiTau (jacobiComodulus k) =
-1 / jacobiTau k`. -/
private lemma jacobiTau_jacobiComodulus {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiTau (jacobiComodulus k) = -1 / jacobiTau k := by
  have h1 := completeEllipticK_ne_zero hk
  have h2 : completeEllipticKPrime k ≠ 0 := by
    rw [← completeEllipticK_jacobiComodulus_eq_completeEllipticKPrime];
        exact completeEllipticK_ne_zero (jacobiComodulus_mem_jacobiModulusDomain hk)
  rw [jacobiTau, jacobiTau, completeEllipticK_jacobiComodulus_eq_completeEllipticKPrime,
      completeEllipticKPrime_jacobiComodulus_eq_completeEllipticK]
  field_simp
  simp [I_sq]

/-- Letter map of the modular transformation `τ ↦ -1/τ`: `s ↦ s`, `c ↦ n`, `d ↦ d`, `n ↦ c`. -/
def jacobiLetterModularSwap : JacobiLetter → JacobiLetter
  | .s => .s
  | .c => .n
  | .d => .d
  | .n => .c

/-- The normalized thetas under `τ ↦ -1/τ`. -/
private lemma jacobiLetterTheta_neg_inv {τ : ℂ} (hτ : 0 < τ.im) (p : JacobiLetter) (ζ : ℂ) :
    jacobiLetterTheta p ζ τ = cexp (I * (-1 / τ) * ζ ^ 2 / π) * (if p = .s then -I else 1) *
      jacobiLetterTheta (jacobiLetterModularSwap p) (ζ * (-1 / τ)) (-1 / τ) := by
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
  have n2 := jacobiThetaTwoTau_zero_ne_zero hτ
  have n3 := jacobiThetaThreeTau_zero_ne_zero hτ
  have n4 := jacobiThetaFourTau_zero_ne_zero hτ
  set A := (-I * τ) ^ (1 / 2 : ℂ)
  set E := cexp (I * (-1 / τ) * ζ ^ 2 / π)
  cases p <;> simp only [jacobiLetterTheta, jacobiLetterModularSwap, reduceCtorEq, ↓reduceIte]
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
theorem jacobiPQ_I_mul {k : ℂ} (hk : k ∈ jacobiModulusDomain) (p q : JacobiLetter) (hpq : p ≠ q)
    (z : ℂ) : jacobiPQ p q (I * z) k =
      (if p = .s then -I else 1) / (if q = .s then -I else 1) *
        ((if p = .s then -1 else 1) * (if q = .s then -1 else 1)) *
        jacobiPQ (jacobiLetterModularSwap p) (jacobiLetterModularSwap q) z
            (jacobiComodulus k) := by
  have hτ := jacobiTau_im_pos hk
  have hσ : jacobiLetterModularSwap p ≠ jacobiLetterModularSwap q := by
    cases p <;> cases q <;> simp_all [jacobiLetterModularSwap]
  have hw : jacobiThetaArgument (I * z) k * (-1 / jacobiTau k) =
      -jacobiThetaArgument z (jacobiComodulus k) := by
    have h1 := completeEllipticK_ne_zero hk
    have h2 : completeEllipticKPrime k ≠ 0 := by
      rw [← completeEllipticK_jacobiComodulus_eq_completeEllipticKPrime];
          exact completeEllipticK_ne_zero (jacobiComodulus_mem_jacobiModulusDomain hk)
    rw [jacobiThetaArgument, jacobiThetaArgument, jacobiTau,
        completeEllipticK_jacobiComodulus_eq_completeEllipticKPrime]
    field_simp
  unfold jacobiPQ jacobiGlaisher
  simp only [hpq, hσ, ↓reduceIte]
  rw [jacobiLetterTheta_neg_inv hτ p, jacobiLetterTheta_neg_inv hτ q, hw,
    ← jacobiTau_jacobiComodulus hk, jacobiLetterTheta_neg, jacobiLetterTheta_neg]
  have hE : cexp (I * jacobiTau (jacobiComodulus k) * jacobiThetaArgument (I * z) k ^ 2 / π) ≠ 0 :=
    exp_ne_zero _
  generalize cexp (I * jacobiTau (jacobiComodulus k) * jacobiThetaArgument (I * z) k ^ 2 / π) = E
    at hE ⊢
  have hs : ∀ r : JacobiLetter, (jacobiLetterModularSwap r = .s) = (r = .s) := by
    intro r; cases r <;> simp [jacobiLetterModularSwap]
  simp only [hs]
  generalize jacobiLetterTheta (jacobiLetterModularSwap p)
      (jacobiThetaArgument z (jacobiComodulus k))
    (jacobiTau (jacobiComodulus k)) = X
  generalize jacobiLetterTheta (jacobiLetterModularSwap q)
      (jacobiThetaArgument z (jacobiComodulus k))
    (jacobiTau (jacobiComodulus k)) = Y
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
    let k' := jacobiComodulus k
    jacobiSn (I * z) k = I * jacobiSc z k' ∧ jacobiCn (I * z) k = jacobiNc z k' ∧
      jacobiDn (I * z) k = jacobiDc z k' ∧ jacobiCd (I * z) k = jacobiNd z k' ∧
      jacobiSd (I * z) k = I * jacobiSd z k' ∧ jacobiNd (I * z) k = jacobiCd z k' ∧
      jacobiDc (I * z) k = jacobiDn z k' ∧ jacobiNc (I * z) k = jacobiCn z k' ∧
      jacobiSc (I * z) k = I * jacobiSn z k' ∧ jacobiNs (I * z) k = -I * jacobiCs z k' ∧
      jacobiDs (I * z) k = -I * jacobiDs z k' ∧ jacobiCs (I * z) k = -I * jacobiNs z k' := by
  intro k'
  simp only [jacobiSn, jacobiCn, jacobiDn, jacobiCd, jacobiSd, jacobiNd, jacobiDc,
    jacobiNc, jacobiSc, jacobiNs, jacobiDs, jacobiCs]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [jacobiPQ_I_mul hk _ _ (by decide)];
        simp only [jacobiLetterModularSwap, reduceCtorEq, ↓reduceIte, k'];
      try field_simp) <;> (try ring_nf) <;> (try simp [I_sq])

end DLMF.JacobiElliptic
