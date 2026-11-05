/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Symmetric
public import DLMF.EllipticIntegrals.Legendre
public import DLMF.EllipticIntegrals.SymmetricAddition
public import DLMF.EllipticIntegrals.LegendrePrincipalValue
public import DLMF.EllipticIntegrals.LegendreSymmetricForms
public import DLMF.EllipticIntegrals.SymmetricLegendreConnection
public import DLMF.EllipticIntegrals.LegendreIdentities
public import DLMF.EllipticIntegrals.Derivatives
public import DLMF.EllipticIntegrals.Connection.ParameterChanges
public import Carlson.TwoVariable.GaussHypergeometric
public import DLMF.JacobiElliptic.Inverse
public import DLMF.Weierstrass.EllipticFunctionsAndInvariants

/-!
# Relations of the symmetric integrals to other functions (DLMF §19.25)

Legendre's and Bulirsch's integrals as symmetric integrals and conversely (§19.25(i)–(iii)),
and the symmetric integrals in terms of Jacobian elliptic functions (§19.25(v)), Weierstrass
elliptic functions (§19.25(vi)) and the Gauss hypergeometric function (§19.25(vii)).
§19.25(iv) is a pointer to §20.9(i) (19.25.iv.p1) with no formula.

## Main definitions

* `jacobiLetterNumerator`: the Glaisher numerator `p(u, k)` for `p ∈ {s, c, d, n}`.
* `jacobiDeltam`: `Δ(p, q) = ps²(u, k) - qs²(u, k)` (DLMF 19.25.28).
* `weierstrassSigmaIdx`: the functions `σ_j(z)` (DLMF 19.25.41).

## Main results

* `completeEllipticK_eq_symmetricEllipticRF`, `completeEllipticK_eq_symmetricEllipticRF'`,
  `completeEllipticK_ofReal_eq_symmetricEllipticRF`, `completeEllipticE_eq_symmetricElliptic`: the
  complete integrals `K`, `E` (DLMF 19.25.1).
* `completeEllipticPi_sub_completeEllipticK`, `completeEllipticPi_eq_symmetricEllipticR`,
  `completeEllipticPi_pv_eq`: `Π(α², k)` (DLMF 19.25.2–19.25.4).
* `incompleteEllipticF_eq_symmetricEllipticRF`, `incompleteEllipticF_eq_symmetricEllipticRF'`:
  `F(φ, k) = R_F(c - 1, c - k², c)`, `c = csc² φ` (DLMF 19.25.5, 19.25.17, 19.25.18).
* `incompleteEllipticE_eq_symmetricEllipticRG`, `incompleteEllipticE_eq_symmetricEllipticR`,
  `incompleteEllipticE_eq_symmetricEllipticRF_sub_symmetricEllipticRD`,
  `incompleteEllipticE_eq_symmetricEllipticRD_second`,
  `incompleteEllipticE_eq_symmetricEllipticRD_third`: `E(φ, k)` (DLMF 19.25.7–19.25.11).
* `hasDerivAt_incompleteEllipticF_symmetricEllipticRD`,
  `hasDerivAt_incompleteEllipticE_symmetricEllipticRD`: DLMF 19.25.6, 19.25.12.
* `incompleteEllipticD_eq_symmetricEllipticRD`, `incompleteEllipticD_eq_symmetricEllipticRD'`,
  `incompleteEllipticPi_sub_incompleteEllipticF`, `incompleteEllipticPi_eq_symmetricEllipticR`,
  `incompleteEllipticPi_pv_eq`: DLMF 19.25.13–19.25.16.
* `bulirschCel_eq_symmetricElliptic`, `bulirschEl1_eq_symmetricEllipticRF`,
  `bulirschEl2_eq_symmetricElliptic`, `bulirschEl3_eq_symmetricElliptic`: Bulirsch's integrals (DLMF
  19.25.19–19.25.22).
* `sqrt_mul_symmetricEllipticRF_eq_incompleteEllipticF`,
  `sqrt_mul_symmetricEllipticRF_eq_incompleteEllipticF'`, `symmetricEllipticRD_eq_incEllInt`,
  `symmetricEllipticRJ_eq_incEllInt`, `symmetricEllipticRG_eq_incEllInt`: symmetric integrals as
  Legendre integrals (DLMF 19.25.23–19.25.27).
* `jacobiDeltam_swap`, `jacobiDeltam_values`, `jacobiAmOfParameter_eq_symmetricEllipticRC`,
  `jacobiAmOfParameter_eq_symmetricEllipticRC'`, `eq_symmetricEllipticRF_jacobi`: Jacobian elliptic
  functions (DLMF 19.25.28–19.25.31); the inverse functions (DLMF 19.25.32–19.25.34) are in
  `DLMF.EllipticIntegrals.SymmetricInverseJacobi`.
* `weierstrassP_symmetricEllipticRF`, `weierstrassZeta_symmetricEllipticRG`,
  `halfPeriod_eq_symmetricEllipticRF`, `eq_weierstrassSigma_mul_symmetricEllipticRF`: Weierstrass
  functions (DLMF 19.25.35–19.25.40).
* `ordinaryHypergeometric_eq_symmetricEllipticR`,
  `symmetricEllipticR_two_eq_ordinaryHypergeometric`: the Gauss hypergeometric function (DLMF
  19.25.42, 19.25.43).
* `symmetricEllipticRF_zero_one_two`, `integral_sq_div_sqrt_one_sub_pow_four`,
  `symmetricEllipticRF_mul_symmetricEllipticRD_lemniscate`: the lemniscate constants (DLMF 19.20.2,
  19.20.22) and their product (DLMF 19.21.1 at `z = 1`).

## Implementation notes

Legendre's integrals are the complex `DLMF.EllipticIntegrals.incompleteEllipticF` etc. of
`DLMF.EllipticIntegrals.Legendre` (segment path from `0` to `φ`, principal powers, a Cauchy
principal value for `Π`), and `K(k)` is `DLMF.EllipticIntegrals.completeEllipticK`. Jacobian
functions are the project's real `DLMF.Elliptic.Real.jacobiSnOfParameter` etc. (parameter `m = k²`)
and the inverse functions of `DLMF.JacobiElliptic.Inverse`; Weierstrass functions are those of
`DLMF.Weierstrass` on the lattice of `H : HalfPeriods`; `₂F₁` is Mathlib's
`ordinaryHypergeometric` (the Gauss series, `|z| < 1`). In §19.25(i) `c = csc² φ`; in
§19.25(ii) `r = 1/x²`.

**Domains and corrections** (numerical evidence with mpmath):
* §19.25(i) is stated for **real** `φ ∈ (0, π/2]` and complex `k` with `1 - k² sin² φ` off
  `(-∞, 0]`. DLMF allows `0 ≤ ℜ φ ≤ π/2`; with Legendre's integral along the segment `[0, φ]`
  and principal branches, (19.25.5) and (19.25.7) fail when both `φ` and `k` are nonreal
  (e.g. `φ = 0.771 + 0.492i`, `k = -1.32 + 0.604i`), although they hold for real `φ` and for
  real `k² < 1`.
* (19.25.30)–(19.25.31): DLMF's condition `cs²(u, k) ≥ 0` holds for all real `u` but the
  formulas fail for `K < u < 2K` (the right sides are symmetric under `u ↦ 2K - u`); they are
  stated for `0 < u ≤ K`.
* (19.25.32)–(19.25.34): DLMF's conditions on `x²` allow negative `x`, where the formulas fail
  for `arccs`, `arccd`, `arccn` (the right sides are even in `x`); they are stated for `x ≥ 0`.
* (19.25.25) divides by `k²`; we assume `y < z` (so `k ≠ 0`).
* (19.25.38)–(19.25.40) assume the arguments of `R_F`, `R_G` lie in `ℂ \ (-∞, 0]` (DLMF uses
  its conventions on the cut implicitly).

## References

* NIST DLMF §19.25.
* B. C. Carlson, *Special Functions of Applied Mathematics*, 1977, (9.2-11), (9.2-14), (9.3-2);
  formalized in `lean-codes` (`Carlson.Real.incEllIntFk_eq`, `Carlson.Real.compEllIntKk_eq`).
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Real Topology

open DLMF.Core

namespace DLMF.EllipticIntegrals

open DLMF.JacobiElliptic

/-! ### §19.25(i) Legendre's integrals as symmetric integrals -/

/-- DLMF 19.25.1 (first formula): `K(k) = R_F(0, k'², 1)`, `k'² = 1 - k²`, for complex `k` with
`k'² ∈ ℂ \ (-∞, 0]` (`k² ∉ [1, ∞)`, the principal domain of `K`). This is stronger than DLMF, which
assumes `1 - k² ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.25.E1]
theorem completeEllipticK_eq_symmetricEllipticRF' {k : ℂ} :
    completeEllipticK k = symmetricEllipticRF 0 (1 - k ^ 2) 1 := by
  rw [completeEllipticK_eq_incompleteEllipticF, show ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) by
      push_cast; ring,
    incompleteEllipticF_ofReal_eq_integral,
        ← symmetricEllipticRF_csc_sq_eq_integral (by positivity) le_rfl k,
    csc_sq_pi_div_two, sub_self]

/-- DLMF 19.25.1 (first formula): `K(k) = R_F(0, k'², 1)`, `k'² = 1 - k²`, for complex `k` with
`k'² ∈ ℂ \ (-∞, 0]` (`k² ∉ [1, ∞)`, the principal domain of `K`). -/
@[dlmf 19.25.E1]
theorem completeEllipticK_eq_symmetricEllipticRF {k : ℂ} (_hk : 1 - k ^ 2 ∈ slitPlane) :
    completeEllipticK k = symmetricEllipticRF 0 (1 - k ^ 2) 1 :=
  completeEllipticK_eq_symmetricEllipticRF'

/-- DLMF 19.25.1 (first formula) for real `k² < 1`. From `lean-codes`'
`Carlson.Real.compEllIntKk_eq` (Carlson (9.2-14)). -/
@[dlmf 19.25.E1]
theorem completeEllipticK_ofReal_eq_symmetricEllipticRF {k : ℝ} (hk : k ^ 2 < 1) :
    completeEllipticK k = symmetricEllipticRF 0 ((1 - k ^ 2 : ℝ) : ℂ) 1 := by
  rw [completeEllipticK_ofReal_carlson hk.le, Carlson.Real.compEllIntKk_eq hk,
    symmetricEllipticRF_zero_eq_pi_div_two_mul_carlsonRK (ofReal_mem_slitPlane.mpr (by linarith))
        one_mem_slitPlane]

/-- DLMF 19.25.1 (second to fifth formulas): with `k'² = 1 - k² ∈ ℂ \ (-∞, 0]`,
`E(k) = 2 R_G(0, k'², 1) = (1/3) k'² (R_D(0, k'², 1) + R_D(0, 1, k'²))`,
`K(k) - E(k) = k² D(k) = (1/3) k² R_D(0, k'², 1)` and
`E(k) - k'² K(k) = (1/3) k² k'² R_D(0, 1, k'²)`. -/
@[dlmf 19.25.E1]
theorem completeEllipticE_eq_symmetricElliptic {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) :
    completeEllipticE k = 2 * symmetricEllipticRG 0 (1 - k ^ 2) 1 ∧
      completeEllipticE k = (1 / 3) * (1 - k ^ 2) *
        (symmetricEllipticRD 0 (1 - k ^ 2) 1 + symmetricEllipticRD 0 1 (1 - k ^ 2)) ∧
      completeEllipticK k - completeEllipticE k = k ^ 2 * completeEllipticD k ∧
      k ^ 2 * completeEllipticD k = (1 / 3) * k ^ 2 * symmetricEllipticRD 0 (1 - k ^ 2) 1 ∧
      completeEllipticE k - (1 - k ^ 2) * completeEllipticK k =
        (1 / 3) * k ^ 2 * (1 - k ^ 2) * symmetricEllipticRD 0 1 (1 - k ^ 2) := by
  have e : ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) := by push_cast; ring
  have hk' : 1 - k ^ 2 * (Real.sin (π / 2) : ℂ) ^ 2 ∈ slitPlane := by
    simpa [Real.sin_pi_div_two] using hk
  have hp : (0 : ℝ) < π / 2 := by positivity
  have hE := incompleteEllipticE_eq_symmetricEllipticRF_sub_one_third_symmetricEllipticRD hp le_rfl
      hk'
  have hD := incompleteEllipticD_eq_one_third_symmetricEllipticRD hp le_rfl k
  have hsub := incompleteEllipticE_eq_incompleteEllipticF_sub hp.le le_rfl hk'
  rw [csc_sq_pi_div_two, sub_self] at hE hD
  have hK : completeEllipticK k = symmetricEllipticRF 0 (1 - k ^ 2) 1 :=
      completeEllipticK_eq_symmetricEllipticRF hk
  have hKF : completeEllipticK k = incompleteEllipticF ((π / 2 : ℝ) : ℂ) k := by
    rw [completeEllipticK_eq_incompleteEllipticF, e]
  have hEE : completeEllipticE k = incompleteEllipticE ((π / 2 : ℝ) : ℂ) k := by
      rw [completeEllipticE, e]
  have hDD : completeEllipticD k = incompleteEllipticD ((π / 2 : ℝ) : ℂ) k := by
      rw [completeEllipticD, e]
  have hG := two_mul_symmetricEllipticRG (x := 0) (Or.inr rfl) hk one_mem_slitPlane
  rw [zero_cpow (by norm_num)] at hG
  have hcyc := symmetricEllipticRD_cyclic_mul_sum_of_isCarlsonArgument (x := 0) (Or.inr rfl) hk
      one_mem_slitPlane
  rw [symmetricEllipticRD_comm 0 1] at hcyc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hEE, hE]; linear_combination -hG
  · rw [hEE, hE]; linear_combination -(1 / 3 : ℂ) * hcyc
  · rw [hKF, hEE, hDD, hsub]; ring
  · rw [hDD, hD]; ring
  · rw [hEE, hE, hK]; linear_combination -(k ^ 2 / 3) * hcyc

/-- DLMF 19.25.2: `Π(α², k) - K(k) = (1/3) α² R_J(0, k'², 1, 1 - α²)`, for `k'² = 1 - k²` and
`1 - α²` in `ℂ \ (-∞, 0]` (no principal value). -/
@[dlmf 19.25.E2]
theorem completeEllipticPi_sub_completeEllipticK {k α2 : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane)
    (hα : 1 - α2 ∈ slitPlane) :
    completeEllipticPi α2 k - completeEllipticK k = (1 / 3) * α2 *
        symmetricEllipticRJ 0 (1 - k ^ 2) 1 (1 - α2) := by
  have e : ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) := by push_cast; ring
  have hp : (0 : ℝ) < π / 2 := by positivity
  have hk' : 1 - k ^ 2 * (Real.sin (π / 2) : ℂ) ^ 2 ∈ slitPlane := by
    simpa [Real.sin_pi_div_two] using hk
  have hα' : 1 - α2 * (Real.sin (π / 2) : ℂ) ^ 2 ∈ slitPlane := by
    simpa [Real.sin_pi_div_two] using hα
  have h := incompleteEllipticPi_sub_incompleteEllipticF_eq_integral hp.le le_rfl hk' hα'
  have hJ := symmetricEllipticRJ_csc_sq_eq_integral hp le_rfl k α2
    (not_isNegReal_of_mem_slitPlane (csc_sq_sub_mem_slitPlane hp le_rfl hα'))
  rw [csc_sq_pi_div_two, sub_self] at hJ
  rw [completeEllipticPi, completeEllipticK_eq_incompleteEllipticF, e, h, hJ]
  ring

/-- DLMF 19.25.3: `Π(α², k) = (π/2) R_{-1/2}(1/2, -1/2, 1; k'², 1, 1 - α²)`, for `k'² = 1 - k²`
and `1 - α²` in `ℂ \ (-∞, 0]`. -/
@[dlmf 19.25.E3]
theorem completeEllipticPi_eq_symmetricEllipticR {k α2 : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane)
    (hα : 1 - α2 ∈ slitPlane) :
    completeEllipticPi α2 k =
      (π / 2) * symmetricEllipticR (1 / 2) ![1 / 2, -1 / 2, 1] ![1 - k ^ 2, 1, 1 - α2] := by
  exact completeEllipticPi_eq_pi_div_two_mul_symmetricEllipticR hk hα

/-- DLMF 19.25.4: the Cauchy principal value
`Π(α², k) = -(1/3)(k²/α²) R_J(0, 1 - k², 1, 1 - k²/α²)` for `-∞ < k² < 1 < α²` (real `k²`,
`α²`; written with real `k`). -/
@[dlmf 19.25.E4]
theorem completeEllipticPi_pv_eq {k α2 : ℝ} (hk : k ^ 2 < 1) (hα : 1 < α2) :
    completeEllipticPi α2 k = -(1 / 3) * ((k ^ 2 / α2 : ℝ) : ℂ) *
      symmetricEllipticRJ 0 ((1 - k ^ 2 : ℝ) : ℂ) 1 ((1 - k ^ 2 / α2 : ℝ) : ℂ) := by
  have hslit : 1 - (k : ℂ) ^ 2 ∈ slitPlane := by
    rw [← ofReal_pow, ← ofReal_one, ← ofReal_sub]
    exact ofReal_mem_slitPlane.mpr (by linarith)
  have hP := completeEllipticPi_eq_symmetricEllipticRF_add_RJ hslit
    (show α2 ≠ 1 by linarith)
  have H := symmetricEllipticRJ_complete_reciprocal_parameter hk hα
  push_cast at H ⊢
  rw [hP]
  push_cast
  linear_combination (1 / 3 : ℂ) * H

/-- DLMF 19.25.5 (and its rewriting (19.25.17)–(19.25.18)): `F(φ, k) = R_F(c - 1, c - k², c)`,
`c = csc² φ`, i.e. `F(φ, k) = R_F(x, y, z)` with `(x, y, z) = (c - 1, c - k², c)`. Stated for
real `φ ∈ (0, π/2]` and complex `k` with `1 - k² sin² φ ∈ ℂ \ (-∞, 0]` (see the module
docstring for DLMF's complex `φ`). This is stronger than DLMF, which assumes
`1 - k² sin² φ ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.25.E5, dlmf 19.25.E17, dlmf 19.25.E18]
theorem incompleteEllipticF_eq_symmetricEllipticRF' {φ : ℝ} {k : ℂ} (hφ : 0 < φ) (hφ' : φ ≤ π / 2) :
    let c : ℂ := ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)
    incompleteEllipticF φ k = symmetricEllipticRF (c - 1) (c - k ^ 2) c := by
  intro c
  exact (incompleteEllipticF_ofReal_eq_integral φ k).trans
      (symmetricEllipticRF_csc_sq_eq_integral hφ hφ' k).symm

/-- DLMF 19.25.5 (and its rewriting (19.25.17)–(19.25.18)): `F(φ, k) = R_F(c - 1, c - k², c)`,
`c = csc² φ`, i.e. `F(φ, k) = R_F(x, y, z)` with `(x, y, z) = (c - 1, c - k², c)`. Stated for
real `φ ∈ (0, π/2]` and complex `k` with `1 - k² sin² φ ∈ ℂ \ (-∞, 0]` (see the module
docstring for DLMF's complex `φ`). -/
@[dlmf 19.25.E5, dlmf 19.25.E17, dlmf 19.25.E18]
theorem incompleteEllipticF_eq_symmetricEllipticRF {φ : ℝ} {k : ℂ} (hφ : 0 < φ) (hφ' : φ ≤ π / 2)
    (_hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    let c : ℂ := ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)
    incompleteEllipticF φ k = symmetricEllipticRF (c - 1) (c - k ^ 2) c :=
  incompleteEllipticF_eq_symmetricEllipticRF' hφ hφ'

/-- Under the cosecant-square substitution, moving `c-k²` to the third argument
of `R_D` gives the sine integral with the inverse unitCube of the Legendre square root. -/
private lemma symmetricEllipticRD_csc_sq_swap_eq_integral {φ : ℝ} {k : ℂ} (hφ : 0 < φ)
    (hφ' : φ ≤ π / 2)
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    let c : ℂ := ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)
    symmetricEllipticRD (c - 1) c (c - k ^ 2) =
      3 * ∫ θ in (0 : ℝ)..φ, (Real.sin θ : ℂ) ^ 2 *
        (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(3 / 2 : ℂ)) := by
  dsimp only
  have hc := csc_sq_sub_mem_slitPlane hφ hφ' hk
  rw [symmetricEllipticRD_eq_integral (not_isNegReal_of_mem_slitPlane hc),
    integral_Ioi_eq_integral_Ioo_csc_sq_subst hφ hφ', intervalIntegral.integral_of_le hφ.le,
    integral_Ioc_eq_integral_Ioo, ← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  have hperm : ∀ x y z : ℂ, ∀ t : ℝ, carlsonRootProduct x y z t = carlsonRootProduct x z y t := by
    intros; simp only [carlsonRootProduct]; ring
  rw [hperm, carlsonRootProduct_csc_sq_subst hs hcos k]
  have hsC : Complex.sin (θ : ℂ) ≠ 0 := by
    rw [← ofReal_sin]; exact ofReal_ne_zero.mpr hs.ne'
  have hcC : Complex.cos (θ : ℂ) ≠ 0 := by
    rw [← ofReal_cos]; exact ofReal_ne_zero.mpr hcos.ne'
  have hden : ((1 / Real.sin θ ^ 2 - 1 / Real.sin φ ^ 2 : ℝ) : ℂ) +
      (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - k ^ 2) =
      (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) / (Real.sin θ : ℂ) ^ 2 := by
    push_cast; field_simp [hsC]; ring
  rw [hden]
  have hslit : 1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2 ∈ slitPlane := by
    have h := legendrePathInSlitPlane_ofReal_of_endpoint hφ hφ' hk (θ / φ)
        ⟨div_nonneg hθ.1.le hφ.le,
      (div_le_one hφ).mpr hθ.2.le⟩
    simpa only [div_mul_cancel₀ _ hφ.ne', ← ofReal_mul, ← ofReal_sin] using h
  have hw0 := slitPlane_ne_zero hslit
  rw [cpow_neg_three_halves_eq hw0, cpow_neg]
  have hV := cpow_half_mul_cpow_half (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2)
  have hs0 : (Real.sin θ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have hcos0 : (Real.cos θ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hcos.ne'
  have hV0 : (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := by
    intro hv; rw [hv, zero_mul] at hV; exact hw0 hV.symm
  generalize hB : (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) = B at hw0 hV hV0 ⊢
  generalize hVdef : B ^ (1 / 2 : ℂ) = V at hV hV0 ⊢
  push_cast
  field_simp [hsC, hcC, hV0, hw0]

/-- DLMF 19.25.6: `∂F(φ, k)/∂k = (1/3) k R_D(c - 1, c, c - k²)`, `c = csc² φ`, for real
`φ ∈ (0, π/2]` and `1 - k² sin² φ ∈ ℂ \ (-∞, 0]`, `k ≠ 0`... (the derivative is the complex
derivative in `k`). -/
@[dlmf 19.25.E6]
theorem hasDerivAt_incompleteEllipticF_symmetricEllipticRD {φ : ℝ} {k : ℂ} (hφ : 0 < φ)
    (hφ' : φ ≤ π / 2)
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    let c : ℂ := ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)
    HasDerivAt (fun κ : ℂ => incompleteEllipticF φ κ)
      ((1 / 3) * k * symmetricEllipticRD (c - 1) c (c - k ^ 2)) k := by
  dsimp only
  have hpath := legendrePathInSlitPlane_ofReal_of_endpoint hφ hφ' hk
  have h := hasDerivAt_integral_unit_mul_cpow
      (by fun_prop : Continuous fun t : ℝ => Complex.sin (t * φ) ^ 2)
    continuousOn_const (-(1 / 2) : ℂ) (w := fun _ => (φ : ℂ)) hpath
  have hfun : (fun κ : ℂ => incompleteEllipticF φ κ) = fun κ : ℂ => ∫ t in (0 : ℝ)..1,
      (φ : ℂ) * (1 - κ ^ 2 * Complex.sin (t * φ) ^ 2) ^ (-(1 / 2) : ℂ) := by
    funext κ; simp only [incompleteEllipticF, primitive_eq_integral]
  change HasDerivAt (fun κ : ℂ => ∫ t in (0 : ℝ)..1,
      (φ : ℂ) * (1 - κ ^ 2 * Complex.sin (t * φ) ^ 2) ^ (-(1 / 2) : ℂ)) _ k at h
  rw [← hfun] at h
  have hpt (t : ℝ) : (φ : ℂ) * ((-(1 / 2) : ℂ) *
      (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) ^ ((-(1 / 2) : ℂ) - 1) *
          (-(2 * k * Complex.sin (t * φ) ^ 2))) =
      k * ((φ : ℂ) * (Complex.sin (t * φ) ^ 2 * (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) ^
          (-(3 / 2 : ℂ)))) := by
    rw [show (-(1 / 2) : ℂ) - 1 = -(3 / 2) by norm_num]; ring
  simp only [hpt, intervalIntegral.integral_const_mul] at h
  rw [symmetricEllipticRD_csc_sq_swap_eq_integral hφ hφ' hk]
  have he : (φ : ℂ) * ∫ t in (0 : ℝ)..1, Complex.sin (t * φ) ^ 2 *
      (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) ^ (-(3 / 2 : ℂ)) =
      ∫ θ in (0 : ℝ)..φ, (Real.sin θ : ℂ) ^ 2 * (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^
          (-(3 / 2 : ℂ)) := by
    simp only [ofReal_sin]
    rw [← primitive_ofReal (fun z : ℂ => Complex.sin z ^ 2 *
      (1 - k ^ 2 * Complex.sin z ^ 2) ^ (-(3 / 2 : ℂ))) φ, primitive_eq_integral,
      intervalIntegral.integral_const_mul]
  rw [he] at h
  convert h using 1
  ring

/-- DLMF 19.25.7: `E(φ, k) = 2 R_G(c - 1, c - k², c) - (c - 1) R_F(c - 1, c - k², c)
- √(c - 1) √(c - k²)/√c`, for real `φ ∈ (0, π/2]` and `1 - k² sin² φ ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.25.E7]
theorem incompleteEllipticE_eq_symmetricEllipticRG {φ : ℝ} {k : ℂ} (hφ : 0 < φ) (hφ' : φ ≤ π / 2)
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    let c : ℂ := ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)
    incompleteEllipticE φ k = 2 * symmetricEllipticRG (c - 1) (c - k ^ 2) c - (c - 1) *
        symmetricEllipticRF (c - 1)
        (c - k ^ 2) c -
      (c - 1) ^ (1 / 2 : ℂ) * (c - k ^ 2) ^ (1 / 2 : ℂ) / c ^ (1 / 2 : ℂ) := by
  intro c
  have hc : c = ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) := rfl
  have hE := incompleteEllipticE_eq_symmetricEllipticRF_sub_one_third_symmetricEllipticRD hφ hφ' hk
  have hG := two_mul_symmetricEllipticRG (isCarlsonArgument_csc_sq_sub_one hφ hφ')
    (csc_sq_sub_mem_slitPlane hφ hφ' hk) (csc_sq_mem_slitPlane hφ hφ')
  rw [← inv_cpow_half_eq_cpow_neg_half] at hG
  rw [hc]
  linear_combination hE - hG

/-- DLMF 19.25.8: `E(φ, k) = R_{-1/2}(1/2, -1/2, 3/2; c - 1, c - k², c)`, for real
`φ ∈ (0, π/2)` and `1 - k² sin² φ ∈ ℂ \ (-∞, 0]` (at `φ = π/2` the node `c - 1` vanishes and
`symmetricEllipticR` is the boundary limit). -/
@[dlmf 19.25.E8]
theorem incompleteEllipticE_eq_symmetricEllipticR {φ : ℝ} {k : ℂ} (hφ : 0 < φ) (hφ' : φ < π / 2)
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    let c : ℂ := ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)
    incompleteEllipticE φ k =
        symmetricEllipticR (1 / 2) ![1 / 2, -1 / 2, 3 / 2] ![c - 1, c - k ^ 2, c] := by
  exact incompleteEllipticE_eq_symmetricEllipticR_csc_sq hφ hφ' hk

/-- DLMF 19.25.9: `E(φ, k) = R_F(c - 1, c - k², c) - (1/3) k² R_D(c - 1, c - k², c)`, for real
`φ ∈ (0, π/2]` and `1 - k² sin² φ ∈ ℂ \ (-∞, 0]`; all terms are nonnegative when `k² ≤ 0`
(19.25.i.p2). -/
@[dlmf 19.25.E9]
theorem incompleteEllipticE_eq_symmetricEllipticRF_sub_symmetricEllipticRD {φ : ℝ} {k : ℂ}
    (hφ : 0 < φ) (hφ' : φ ≤ π / 2)
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    let c : ℂ := ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)
    incompleteEllipticE φ k = symmetricEllipticRF (c - 1) (c - k ^ 2) c - (1 / 3) * k ^ 2 *
        symmetricEllipticRD (c - 1)
        (c - k ^ 2) c := by
  intro c
  have hc : c = ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) := rfl
  rw [hc]
  exact incompleteEllipticE_eq_symmetricEllipticRF_sub_one_third_symmetricEllipticRD hφ hφ' hk

/-- DLMF 19.25.10: `E(φ, k) = k'² R_F(c - 1, c - k², c) + (1/3) k² k'² R_D(c - 1, c, c - k²)
+ k² √(c - 1)/(√c √(c - k²))`, for `c > k²` (real `k`, `k² sin² φ < 1`), real `φ ∈ (0, π/2]`;
all terms are nonnegative when `0 ≤ k² ≤ 1` (19.25.i.p2). -/
@[dlmf 19.25.E10]
theorem incompleteEllipticE_eq_symmetricEllipticRD_second {φ k : ℝ} (hφ : 0 < φ) (hφ' : φ ≤ π / 2)
    (hk : k ^ 2 * Real.sin φ ^ 2 < 1) :
    let c : ℂ := ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)
    incompleteEllipticE φ k = (1 - (k : ℂ) ^ 2) * symmetricEllipticRF (c - 1) (c - k ^ 2) c +
      (1 / 3) * k ^ 2 * (1 - (k : ℂ) ^ 2) * symmetricEllipticRD (c - 1) c (c - k ^ 2) +
      k ^ 2 * (c - 1) ^ (1 / 2 : ℂ) / (c ^ (1 / 2 : ℂ) * (c - k ^ 2) ^ (1 / 2 : ℂ)) := by
  intro c
  have hc : c = ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) := rfl
  have hk' : 1 - (k : ℂ) ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane := by
    rw [show 1 - (k : ℂ) ^ 2 * (Real.sin φ : ℂ) ^ 2 = ((1 - k ^ 2 * Real.sin φ ^ 2 : ℝ) : ℂ) by
      push_cast; ring]
    exact ofReal_mem_slitPlane.mpr (by linarith)
  rw [hc]
  rcases eq_or_lt_of_le hφ' with h | h
  · subst h
    have hE := incompleteEllipticE_eq_symmetricEllipticRF_sub_one_third_symmetricEllipticRD hφ
        le_rfl hk'
    have hy := csc_sq_sub_mem_slitPlane hφ le_rfl hk'
    rw [csc_sq_pi_div_two] at hE hy ⊢
    rw [sub_self] at hE ⊢
    have hcyc := symmetricEllipticRD_cyclic_mul_sum_of_isCarlsonArgument (x := 0) (Or.inr rfl) hy
        one_mem_slitPlane
    rw [symmetricEllipticRD_comm 0 1] at hcyc
    rw [hE, zero_cpow (by norm_num)]
    linear_combination -((k : ℂ) ^ 2 / 3) * hcyc
  · have hE := incompleteEllipticE_eq_symmetricEllipticRF_sub_one_third_symmetricEllipticRD hφ hφ'
        hk'
    have hM := symmetricEllipticRD_two_term_relation (csc_sq_sub_mem_slitPlane hφ hφ' hk')
      (csc_sq_sub_one_mem_slitPlane hφ h) (csc_sq_mem_slitPlane hφ hφ')
    rw [symmetricEllipticRD_comm (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - 1),
        symmetricEllipticRF_comm_left,
      ← inv_cpow_half_eq_cpow_neg_half,
      ← inv_cpow_half_eq_cpow_neg_half] at hM
    linear_combination hE - ((k : ℂ) ^ 2 / 3) * hM

/-- DLMF 19.25.11: `E(φ, k) = -(1/3) k'² R_D(c - k², c, c - 1) + √(c - k²)/(√c √(c - 1))`, for
`φ ≠ π/2` (real `φ ∈ (0, π/2)`) and `1 - k² sin² φ ∈ ℂ \ (-∞, 0]`; all terms are nonnegative
when `1 ≤ k² ≤ c` (19.25.i.p2). -/
@[dlmf 19.25.E11]
theorem incompleteEllipticE_eq_symmetricEllipticRD_third {φ : ℝ} {k : ℂ} (hφ : 0 < φ)
    (hφ' : φ < π / 2)
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    let c : ℂ := ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)
    incompleteEllipticE φ k = -(1 / 3) * (1 - k ^ 2) * symmetricEllipticRD (c - k ^ 2) c (c - 1) +
      (c - k ^ 2) ^ (1 / 2 : ℂ) / (c ^ (1 / 2 : ℂ) * (c - 1) ^ (1 / 2 : ℂ)) := by
  intro c
  have hc : c = ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) := rfl
  have hE := incompleteEllipticE_eq_symmetricEllipticRF_sub_one_third_symmetricEllipticRD hφ hφ'.le
      hk
  have hM := symmetricEllipticRD_two_term_relation (csc_sq_sub_one_mem_slitPlane hφ hφ')
    (csc_sq_sub_mem_slitPlane hφ hφ'.le hk) (csc_sq_mem_slitPlane hφ hφ'.le)
  rw [← inv_cpow_half_eq_cpow_neg_half, ← inv_cpow_half_eq_cpow_neg_half] at hM
  rw [hc]
  linear_combination hE - (1 / 3 : ℂ) * hM

/-- DLMF 19.25.12: `∂E(φ, k)/∂k = -(1/3) k R_D(c - 1, c - k², c)` (complex derivative in `k`),
for real `φ ∈ (0, π/2]` and `1 - k² sin² φ ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.25.E12]
theorem hasDerivAt_incompleteEllipticE_symmetricEllipticRD {φ : ℝ} {k : ℂ} (hφ : 0 < φ)
    (hφ' : φ ≤ π / 2)
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    let c : ℂ := ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)
    HasDerivAt (fun κ : ℂ => incompleteEllipticE φ κ)
      (-(1 / 3) * k * symmetricEllipticRD (c - 1) (c - k ^ 2) c) k := by
  have hpath := legendrePathInSlitPlane_ofReal_of_endpoint hφ hφ' hk
  have h := hasDerivAt_integral_unit_mul_cpow
      (by fun_prop : Continuous fun t : ℝ => Complex.sin (t * φ) ^ 2)
    continuousOn_const (1 / 2 : ℂ) (w := fun _ => (φ : ℂ)) hpath
  have hfun : (fun κ : ℂ => incompleteEllipticE φ κ) = fun κ : ℂ => ∫ t in (0 : ℝ)..1,
      (φ : ℂ) * (1 - κ ^ 2 * Complex.sin (t * φ) ^ 2) ^ (1 / 2 : ℂ) := by
    funext κ; simp only [incompleteEllipticE, primitive_eq_integral]
  change HasDerivAt (fun κ : ℂ => ∫ t in (0 : ℝ)..1,
      (φ : ℂ) * (1 - κ ^ 2 * Complex.sin (t * φ) ^ 2) ^ (1 / 2 : ℂ)) _ k at h
  rw [← hfun] at h
  have hpt (t : ℝ) : (φ : ℂ) * ((1 / 2 : ℂ) *
      (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) ^ ((1 / 2 : ℂ) - 1) *
          (-(2 * k * Complex.sin (t * φ) ^ 2))) =
      (-k) * ((φ : ℂ) * (Complex.sin (t * φ) ^ 2 * (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) ^
          (-(1 / 2 : ℂ)))) := by
    rw [show (1 / 2 : ℂ) - 1 = -(1 / 2) by norm_num]; ring
  simp only [hpt, intervalIntegral.integral_const_mul] at h
  have he : incompleteEllipticD φ k = (φ : ℂ) * ∫ t in (0 : ℝ)..1, Complex.sin (t * φ) ^ 2 *
      (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) ^ (-(1 / 2 : ℂ)) := by
    rw [incompleteEllipticD, primitive_eq_integral, intervalIntegral.integral_const_mul]
  rw [← he] at h
  rw [incompleteEllipticD_eq_one_third_symmetricEllipticRD hφ hφ' k] at h
  convert h using 1
  ring

/-- DLMF 19.25.13: `D(φ, k) = (1/3) R_D(c - 1, c - k², c)`, for real `φ ∈ (0, π/2]` and
`1 - k² sin² φ ∈ ℂ \ (-∞, 0]`. This is stronger than DLMF, which assumes
`1 - k² sin² φ ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.25.E13]
theorem incompleteEllipticD_eq_symmetricEllipticRD' {φ : ℝ} {k : ℂ} (hφ : 0 < φ) (hφ' : φ ≤ π / 2) :
    let c : ℂ := ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)
    incompleteEllipticD φ k = (1 / 3) * symmetricEllipticRD (c - 1) (c - k ^ 2) c := by
  intro c
  have hc : c = ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) := rfl
  rw [hc]
  exact incompleteEllipticD_eq_one_third_symmetricEllipticRD hφ hφ' k

/-- DLMF 19.25.13: `D(φ, k) = (1/3) R_D(c - 1, c - k², c)`, for real `φ ∈ (0, π/2]` and
`1 - k² sin² φ ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.25.E13]
theorem incompleteEllipticD_eq_symmetricEllipticRD {φ : ℝ} {k : ℂ} (hφ : 0 < φ) (hφ' : φ ≤ π / 2)
    (_hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    let c : ℂ := ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)
    incompleteEllipticD φ k = (1 / 3) * symmetricEllipticRD (c - 1) (c - k ^ 2) c :=
  incompleteEllipticD_eq_symmetricEllipticRD' hφ hφ'

/-- DLMF 19.25.14: `Π(φ, α², k) - F(φ, k) = (1/3) α² R_J(c - 1, c - k², c, c - α²)`, for real
`φ ∈ (0, π/2]`, `1 - k² sin² φ` and `1 - α² sin² φ` in `ℂ \ (-∞, 0]` (no principal value). -/
@[dlmf 19.25.E14]
theorem incompleteEllipticPi_sub_incompleteEllipticF {φ : ℝ} {k α2 : ℂ} (hφ : 0 < φ)
    (hφ' : φ ≤ π / 2)
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane)
    (hα : 1 - α2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    let c : ℂ := ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)
    incompleteEllipticPi φ α2 k - incompleteEllipticF φ k = (1 / 3) * α2 *
        symmetricEllipticRJ (c - 1) (c - k ^ 2) c
        (c - α2) := by
  intro c
  have hc : c = ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) := rfl
  rw [hc, incompleteEllipticPi_sub_incompleteEllipticF_eq_integral hφ.le hφ' hk hα,
      symmetricEllipticRJ_csc_sq_eq_integral
      hφ hφ' k α2
    (not_isNegReal_of_mem_slitPlane (csc_sq_sub_mem_slitPlane hφ hφ' hα))]
  ring

/-- DLMF 19.25.15: `Π(φ, α², k) = R_{-1/2}(1/2, 1/2, -1/2, 1; c - 1, c - k², c, c - α²)`, for real
`φ ∈ (0, π/2)`, `1 - k² sin² φ` and `1 - α² sin² φ` in `ℂ \ (-∞, 0]`. -/
@[dlmf 19.25.E15]
theorem incompleteEllipticPi_eq_symmetricEllipticR {φ : ℝ} {k α2 : ℂ} (hφ : 0 < φ) (hφ' : φ < π / 2)
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane)
    (hα : 1 - α2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    let c : ℂ := ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)
    incompleteEllipticPi φ α2 k =
      symmetricEllipticR (1 / 2) ![1 / 2, 1 / 2, -1 / 2, 1] ![c - 1, c - k ^ 2, c, c - α2] := by
  exact incompleteEllipticPi_eq_symmetricEllipticR_csc_sq hφ hφ' hk hα

/-- DLMF 19.25.16: if `α² > c` the Cauchy principal value is
`Π(φ, α², k) = -(1/3) ω² R_J(c - 1, c - k², c, c - ω²)
+ √((c - 1)(c - k²)/((α² - 1)(1 - ω²))) R_C(c (α² - 1)(1 - ω²), (α² - c)(c - ω²))`,
`ω² = k²/α²`; real `φ ∈ (0, π/2)`, real `k` with `k² < 1`. -/
@[dlmf 19.25.E16]
theorem incompleteEllipticPi_pv_eq {φ k α2 : ℝ} (hφ : 0 < φ) (hφ' : φ < π / 2) (hk : k ^ 2 < 1)
    (hα : 1 / Real.sin φ ^ 2 < α2) :
    let c : ℝ := 1 / Real.sin φ ^ 2
    let ω2 : ℝ := k ^ 2 / α2
    incompleteEllipticPi φ α2 k = -(1 / 3) * (ω2 : ℂ) *
        symmetricEllipticRJ ((c - 1 : ℝ) : ℂ) ((c - k ^ 2 : ℝ) : ℂ) (c : ℂ) ((c - ω2 : ℝ) : ℂ) +
      ((√((c - 1) * (c - k ^ 2) / ((α2 - 1) * (1 - ω2))) : ℝ) : ℂ) *
        symmetricEllipticRC ((c * (α2 - 1) * (1 - ω2) : ℝ) : ℂ)
            (((α2 - c) * (c - ω2) : ℝ) : ℂ) := by
  intro c ω2
  have hc1 : 1 < c := one_lt_csc_sq hφ hφ'
  have hc : 0 < c := by linarith
  have hα1 : 1 < α2 := by linarith
  have hα0 : 0 < α2 := by linarith
  have hω : ω2 < 1 := (div_lt_one hα0).mpr (by linarith)
  have hαω : α2 * ω2 = k ^ 2 := by dsimp [ω2]; field_simp
  have hck : 0 < c - k ^ 2 := by linarith
  have hD : 0 < (α2 - 1) * (1 - ω2) := mul_pos (by linarith) (by linarith)
  have hX : 0 < (c - 1) * (c - k ^ 2) := mul_pos (by linarith) hck
  have hY : (c - α2) * (c - ω2) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) (by linarith)
  have hdiff : (c - 1) * (c - k ^ 2) - (c - α2) * (c - ω2) =
      c * (α2 - 1) * (1 - ω2) := by linear_combination (c - 1) * hαω
  have hks : 1 - (k : ℂ) ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane := by
    rw [← ofReal_pow, ← ofReal_pow, ← ofReal_mul, ← ofReal_one, ← ofReal_sub]
    exact ofReal_mem_slitPlane.mpr (by
      nlinarith [Real.sin_sq_le_one φ, sq_nonneg (Real.sin φ), sq_nonneg k])
  have hQ := incompleteEllipticPi_eq_symmetricEllipticRF_add_RJ hφ hφ'.le hks
    (show ω2 ≠ 1 / Real.sin φ ^ 2 by change ω2 ≠ c; linarith)
  change incompleteEllipticPi φ ω2 k =
    symmetricEllipticRF ((c : ℂ) - 1) ((c : ℂ) - k ^ 2) c + (ω2 : ℂ) / 3 *
      symmetricEllipticRJ ((c : ℂ) - 1) ((c : ℂ) - k ^ 2) c (c - ω2 : ℝ) at hQ
  have hF : incompleteEllipticF φ k =
      symmetricEllipticRF (c - 1 : ℝ) (c - k ^ 2 : ℝ) c := by
    rw [incompleteEllipticF_ofReal_eq_integral]
    push_cast
    simpa only [ofReal_sin] using
      (symmetricEllipticRF_csc_sq_eq_integral hφ hφ'.le (k : ℂ)).symm
  have H := incompleteEllipticPi_add_first' hφ hφ' hk hαω
    (show α2 ≠ 1 / Real.sin φ ^ 2 by linarith)
    (show ω2 ≠ 1 / Real.sin φ ^ 2 by change ω2 ≠ c; linarith)
  change incompleteEllipticPi φ α2 k + incompleteEllipticPi φ ω2 k =
    incompleteEllipticF φ k + Real.sqrt c *
      symmetricEllipticRC ((c - 1) * (c - k ^ 2) : ℝ) ((c - α2) * (c - ω2) : ℝ) at H
  have hRC := (symmetricEllipticRC_of_neg hY hX.le).1
  simp only [← ofReal_sub, ← ofReal_neg] at hRC
  rw [hdiff, show -((c - α2) * (c - ω2)) = (α2 - c) * (c - ω2) by ring] at hRC
  rw [hRC] at H
  have hs : Real.sqrt c *
      Real.sqrt ((c - 1) * (c - k ^ 2) / (c * (α2 - 1) * (1 - ω2))) =
      Real.sqrt ((c - 1) * (c - k ^ 2) / ((α2 - 1) * (1 - ω2))) := by
    rw [← Real.sqrt_mul hc.le]
    congr 1
    field_simp
  rw [← mul_assoc, ← ofReal_mul, hs, hF] at H
  push_cast at H hQ ⊢
  linear_combination H - hQ

/-! ### §19.25(ii) Bulirsch's integrals as symmetric integrals -/

/-- DLMF 19.25.19: `cel(k_c, p, a, b) = a R_F(0, k_c², 1) + (1/3)(b - p a) R_J(0, k_c², 1, p)`,
for real `p ≠ 0`, `a, b` and `k_c² ∈ ℂ \ (-∞, 0]` (principal values when `p < 0`). -/
@[dlmf 19.25.E19]
theorem bulirschCel_eq_symmetricElliptic {kc : ℂ} {p a b : ℝ}
    (hkc : kc ^ 2 ∈ slitPlane) (hp : p ≠ 0) :
    bulirschCel kc p a b =
      a * symmetricEllipticRF 0 (kc ^ 2) 1 + (1 / 3) * ((b - p * a : ℝ) : ℂ) *
        symmetricEllipticRJ 0 (kc ^ 2) 1 p := by
  let k : ℂ := jacobiComodulus kc
  have hksq : 1 - k ^ 2 = kc ^ 2 := by
    dsimp only [k]
    rw [jacobiComodulus_sq_eq_one_sub_sq, sub_sub_cancel]
  have hk : 1 - k ^ 2 ∈ slitPlane := by rw [hksq]; exact hkc
  have hpi : (0 : ℝ) < π / 2 := by positivity
  have hpiC : ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) := by push_cast; ring
  let R : ℝ → ℂ := fun θ => (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))
  have hi := LegendrePrincipalValue.integrableOn_completeEllipticKernel hk
  have hroot := continuousOn_one_sub_mul_sin_sq_cpow hpi.le le_rfl
    (show 1 - k ^ 2 * (Real.sin (π / 2) : ℂ) ^ 2 ∈ slitPlane by simpa using hk)
    (-(1 / 2 : ℂ))
  have hRI : IntervalIntegrable R volume 0 (π / 2) := hroot.intervalIntegrable
  have hSI : IntervalIntegrable (fun θ => (Real.sin θ : ℂ) ^ 2 * R θ) volume 0 (π / 2) :=
    ((by fun_prop : ContinuousOn (fun θ : ℝ => (Real.sin θ : ℂ) ^ 2) (uIcc 0 (π / 2))).mul
      hroot).intervalIntegrable
  rcases eq_or_ne p 1 with rfl | hp1
  · rw [bulirschCel_one_eq_primitive, hpiC, primitive_ofReal]
    have heq (θ : ℝ) :
        ((a : ℂ) * Complex.cos θ ^ 2 + b * Complex.sin θ ^ 2) *
          (Complex.cos θ ^ 2 + kc ^ 2 * Complex.sin θ ^ 2) ^ (-(1 / 2 : ℂ)) =
        (a : ℂ) * R θ + (b - a : ℝ) * ((Real.sin θ : ℂ) ^ 2 * R θ) := by
      have hcs := Complex.cos_sq_add_sin_sq (θ : ℂ)
      have harg : Complex.cos θ ^ 2 + kc ^ 2 * Complex.sin θ ^ 2 =
          1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2 := by
        rw [← hksq]
        push_cast
        linear_combination hcs
      rw [harg]
      dsimp only [R]
      push_cast at hcs ⊢
      linear_combination ((a : ℂ) *
        (1 - k ^ 2 * Complex.sin (θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) * hcs
    rw [intervalIntegral.integral_congr (fun θ _ => heq θ),
      intervalIntegral.integral_add (hRI.const_mul _) (hSI.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hD := incompleteEllipticD_eq_one_third_symmetricEllipticRD hpi le_rfl k
    rw [csc_sq_pi_div_two, sub_self, hksq] at hD
    rw [incompleteEllipticD_ofReal_eq_integral] at hD
    have hK : (∫ θ in (0 : ℝ)..(π / 2), R θ) = symmetricEllipticRF 0 (kc ^ 2) 1 := by
      have H := (symmetricEllipticRF_csc_sq_eq_integral hpi le_rfl k).symm
      simpa only [csc_sq_pi_div_two, sub_self, hksq] using H
    change (a : ℂ) * (∫ θ in (0 : ℝ)..(π / 2), R θ) +
      (b - a : ℝ) * (∫ θ in (0 : ℝ)..(π / 2), (Real.sin θ : ℂ) ^ 2 * R θ) = _
    rw [hK]
    change (a : ℂ) * symmetricEllipticRF 0 (kc ^ 2) 1 +
      (b - a : ℝ) * (∫ θ in (0 : ℝ)..(π / 2), (Real.sin θ : ℂ) ^ 2 * R θ) =
        (a : ℂ) * symmetricEllipticRF 0 (kc ^ 2) 1 +
          (1 / 3) * (b - 1 * a : ℝ) * symmetricEllipticRD 0 (kc ^ 2) 1
    dsimp only [R] at hD ⊢
    push_cast at hD ⊢
    linear_combination ((b : ℂ) - a) * hD
  · let A : ℝ := (b - p * a) / (1 - p)
    let B : ℝ := (a - b) / (1 - p)
    have hα : 1 - p ≠ 1 := by intro H; apply hp; linarith
    have hA : (1 - (p : ℂ)) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr (Ne.symm hp1)
    have hP := LegendrePrincipalValue.tendsto_integral_cutoff_completeEllipticPi hk hα
    have hK := LegendrePrincipalValue.tendsto_integral_cutoff_completeEllipticK hk (1 - p)
    have hEq : ∀ᶠ ε : ℝ in 𝓝[>] 0,
        (∫ θ in (0 : ℝ)..(π / 2), if ε ≤ |1 - (1 - p) * Real.sin θ ^ 2| then
          ((a : ℂ) + (b - a : ℝ) * (Real.sin θ : ℂ) ^ 2) /
            (1 - ((1 - p : ℝ) : ℂ) * (Real.sin θ : ℂ) ^ 2) * R θ else 0) =
        (A : ℂ) * (∫ θ in (0 : ℝ)..(π / 2), if ε ≤ |1 - (1 - p) * Real.sin θ ^ 2| then
          (1 - ((1 - p : ℝ) : ℂ) * (Real.sin θ : ℂ) ^ 2)⁻¹ * R θ else 0) +
        (B : ℂ) * (∫ θ in (0 : ℝ)..(π / 2), if ε ≤ |1 - (1 - p) * Real.sin θ ^ 2|
          then R θ else 0) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε0 : 0 < ε := hε
      have hM : MeasurableSet {θ | ε ≤ |1 - (1 - p) * Real.sin θ ^ 2|} := by
        measurability
      have hiP := integrable_indicator_abs_ge_inv_mul hi
        (show Measurable (fun θ : ℝ => 1 - (1 - p) * Real.sin θ ^ 2) by fun_prop) hε0
      simp only [ofReal_sub, ofReal_one, ofReal_mul, ofReal_pow] at hiP
      have hiK : IntegrableOn (fun θ => if ε ≤ |1 - (1 - p) * Real.sin θ ^ 2| then R θ else 0)
          (Ioc 0 (π / 2)) := by
        change Integrable (fun θ => if ε ≤ |1 - (1 - p) * Real.sin θ ^ 2| then R θ else 0)
          (volume.restrict (Ioc 0 (π / 2)))
        convert (show Integrable R (volume.restrict (Ioc 0 (π / 2))) from hi).indicator hM using 1
        funext θ
        simp only [Set.indicator_apply, mem_ofPred_eq]
      dsimp only [R] at hiK ⊢
      simp only [intervalIntegral.integral_of_le hpi.le, ofReal_sub, ofReal_one]
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hiP.const_mul (A : ℂ))
        (hiK.const_mul (B : ℂ))]
      refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
      change (if ε ≤ |1 - (1 - p) * Real.sin θ ^ 2| then
        ((a : ℂ) + ((b : ℂ) - a) * (Real.sin θ : ℂ) ^ 2) /
          (1 - (1 - (p : ℂ)) * (Real.sin θ : ℂ) ^ 2) * R θ else 0) =
        (A : ℂ) * (if ε ≤ |1 - (1 - p) * Real.sin θ ^ 2| then
          (1 - (1 - (p : ℂ)) * (Real.sin θ : ℂ) ^ 2)⁻¹ * R θ else 0) +
        (B : ℂ) * (if ε ≤ |1 - (1 - p) * Real.sin θ ^ 2| then R θ else 0)
      by_cases hcut : ε ≤ |1 - (1 - p) * Real.sin θ ^ 2|
      · simp only [ite_eq_left hcut]
        have hgne : 1 - (1 - p) * Real.sin θ ^ 2 ≠ 0 := by
          intro H; rw [H, abs_zero] at hcut; linarith
        have hgc : 1 - (1 - (p : ℂ)) * (Real.sin θ : ℂ) ^ 2 ≠ 0 := by
          exact_mod_cast hgne
        have hnum : (a : ℂ) + ((b : ℂ) - a) * (Real.sin θ : ℂ) ^ 2 =
            (A : ℂ) + (B : ℂ) * (1 - (1 - (p : ℂ)) * (Real.sin θ : ℂ) ^ 2) := by
          dsimp only [A, B]
          push_cast
          field_simp [hA]
          ring
        rw [hnum, add_div, mul_div_cancel_right₀ _ hgc]
        ring
      · simp only [ite_eq_right hcut, mul_zero, add_zero]
    have H := ((hP.const_mul (A : ℂ)).add (hK.const_mul (B : ℂ))).congr'
      (hEq.mono fun ε h => h.symm)
    rw [bulirschCel_eq_limUnder_cutoff]
    calc limUnder _ _ = (A : ℂ) * completeEllipticPi (1 - p : ℝ) k +
        (B : ℂ) * completeEllipticK k := H.limUnder_eq
      _ = _ := by
        rw [completeEllipticPi_eq_symmetricEllipticRF_add_RJ hk hα,
          completeEllipticK_eq_symmetricEllipticRF hk, hksq]
        simp only [show (1 - (1 - p) : ℝ) = p by ring]
        dsimp only [A, B]
        push_cast
        field_simp [hA]
        ring

/-- DLMF 19.25.20: `el1(x, k_c) = R_F(r, r + k_c², r + 1)`, `r = 1/x²`, for real `x > 0` and
`k_c² ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.25.E20]
theorem bulirschEl1_eq_symmetricEllipticRF {x : ℝ} {kc : ℂ} (hx : 0 < x)
    (_hkc : kc ^ 2 ∈ slitPlane) :
    let r : ℂ := ((1 / x ^ 2 : ℝ) : ℂ)
    bulirschEl1 x kc = symmetricEllipticRF r (r + kc ^ 2) (r + 1) :=
  bulirschEl1_eq_symmetricEllipticRF_of_pos hx kc

/-- DLMF 19.25.21: `el2(x, k_c, a, b) = a el1(x, k_c) + (1/3)(b - a) R_D(r, r + k_c², r + 1)`,
`r = 1/x²`, for real `x > 0`, `a, b` and `k_c² ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.25.E21]
theorem bulirschEl2_eq_symmetricElliptic {x : ℝ} {kc : ℂ} {a b : ℝ} (hx : 0 < x)
    (hkc : kc ^ 2 ∈ slitPlane) :
    let r : ℂ := ((1 / x ^ 2 : ℝ) : ℂ)
    bulirschEl2 x kc a b = a * bulirschEl1 x kc + (1 / 3) * ((b - a : ℝ) : ℂ) *
        symmetricEllipticRD r
        (r + kc ^ 2) (r + 1) := by
  exact bulirschEl2_eq_symmetricEllipticRD hx hkc a b

/-- DLMF 19.25.22: `el3(x, k_c, p) = el1(x, k_c) + (1/3)(1 - p) R_J(r, r + k_c², r + 1, r + p)`,
`r = 1/x²`, for real `x > 0`, real `p ≠ 0` with `x² ≠ -1/p` (19.2.16), and
`k_c² ∈ ℂ \ (-∞, 0]` (principal values when `r + p < 0`). -/
@[dlmf 19.25.E22]
theorem bulirschEl3_eq_symmetricElliptic {x : ℝ} {kc : ℂ} {p : ℝ} (hx : 0 < x)
    (hkc : kc ^ 2 ∈ slitPlane)
    (hp : p ≠ 0) (hxp : x ^ 2 ≠ -1 / p) :
    let r : ℂ := ((1 / x ^ 2 : ℝ) : ℂ)
    bulirschEl3 x kc p = bulirschEl1 x kc + (1 / 3) * ((1 - p : ℝ) : ℂ) *
        symmetricEllipticRJ r (r + kc ^ 2)
        (r + 1) (r + p) := by
  intro r
  obtain ⟨h0, h1, hc⟩ := arctan_mem_and_csc_sq hx
  have hpr : 1 / x ^ 2 + p ≠ 0 := by
    intro H
    have HH : 1 + p * x ^ 2 = 0 := by
      field_simp [hx.ne'] at H
      nlinarith
    apply hxp
    field_simp [hp]
    linarith
  have hα : 1 - p ≠ 1 / Real.sin (Real.arctan x) ^ 2 := by
    rw [hc]
    intro H
    apply hpr
    linarith
  have hk : 1 - jacobiComodulus kc ^ 2 ∈ slitPlane := by
    rw [jacobiComodulus_sq_eq_one_sub_sq, sub_sub_cancel]
    exact hkc
  have hks : 1 - jacobiComodulus kc ^ 2 * (Real.sin (Real.arctan x) : ℂ) ^ 2 ∈ slitPlane := by
    have H := one_sub_mul_ofReal_mem_slitPlane hk (sq_nonneg (Real.sin (Real.arctan x)))
      (Real.sin_sq_le_one (Real.arctan x))
    simpa only [ofReal_pow] using H
  have H := incompleteEllipticPi_eq_symmetricEllipticRF_add_RJ h0 h1.le hks hα
  have hdouble : jacobiComodulus (jacobiComodulus kc) ^ 2 = kc ^ 2 := by
    rw [jacobiComodulus_sq_eq_one_sub_sq, jacobiComodulus_sq_eq_one_sub_sq, sub_sub_cancel]
  have hPi := bulirschEl3_eq_incompleteEllipticPi (x : ℂ) (jacobiComodulus kc) p
  conv_lhs at hPi => rw [bulirschEl3, hdouble, ← bulirschEl3]
  rw [← ofReal_arctan] at hPi
  dsimp only at H
  rw [hc] at H
  have hr0 : (((1 / x ^ 2 : ℝ) : ℂ) + 1) - 1 = r := by dsimp [r]; ring
  have hrk : (((1 / x ^ 2 : ℝ) : ℂ) + 1) - jacobiComodulus kc ^ 2 = r + kc ^ 2 := by
    rw [jacobiComodulus_sq_eq_one_sub_sq]
    dsimp [r]
    ring
  have hrp : ((1 / x ^ 2 + 1 - (1 - p) : ℝ) : ℂ) = r + p := by
    dsimp [r]
    push_cast
    ring
  simp only [ofReal_add, ofReal_one] at H
  rw [hr0, hrk, hrp] at H
  rw [hPi, bulirschEl1_eq_symmetricEllipticRF_of_pos hx kc]
  dsimp only [r] at H ⊢
  push_cast at H ⊢
  linear_combination H

/-! ### §19.25(iii) Symmetric integrals as Legendre's integrals -/

/-- DLMF 19.25.24 with 19.25.23: for `0 ≤ x ≤ y ≤ z`, `x < z`, `(x, y) ≠ (0, 0)`, with
`φ = arccos √(x/z)` and `k = √((z - y)/(z - x))`, `(z - x)^{1/2} R_F(x, y, z) = F(φ, k)`. This is
stronger than DLMF, which assumes `x ≤ y` and `(x, y) ≠ (0, 0)`. -/
@[dlmf 19.25.E23, dlmf 19.25.E24]
theorem sqrt_mul_symmetricEllipticRF_eq_incompleteEllipticF' {x y z : ℝ} (hx : 0 ≤ x) (hyz : y ≤ z)
    (hxz : x < z) :
    let φ := Real.arccos √(x / z)
    let k := √((z - y) / (z - x))
    ((√(z - x) : ℝ) : ℂ) * symmetricEllipticRF x y z = incompleteEllipticF φ k := by
  intro φ k
  obtain ⟨hφ0, hφ1, ex, ey, ez, -, -, -⟩ := real_symmetric_legendre_parametrization hx hyz hxz
  have hl : 0 < z - x := by linarith
  rw [ex, ey, ez, symmetricEllipticRF_scale hl, ofReal_sqrt_eq_cpow_half hl.le,
    mul_inv_cancel_left₀ (ofReal_cpow_half_ne_zero hl),
        symmetricEllipticRF_csc_sq_eq_integral hφ0 hφ1,
    ← incompleteEllipticF_ofReal_eq_integral]

/-- DLMF 19.25.24 with 19.25.23: for `0 ≤ x ≤ y ≤ z`, `x < z`, `(x, y) ≠ (0, 0)`, with
`φ = arccos √(x/z)` and `k = √((z - y)/(z - x))`, `(z - x)^{1/2} R_F(x, y, z) = F(φ, k)`. -/
@[dlmf 19.25.E23, dlmf 19.25.E24]
theorem sqrt_mul_symmetricEllipticRF_eq_incompleteEllipticF {x y z : ℝ} (hx : 0 ≤ x) (_hxy : x ≤ y)
    (hyz : y ≤ z) (hxz : x < z) (_h0 : (x, y) ≠ (0, 0)) :
    let φ := Real.arccos √(x / z)
    let k := √((z - y) / (z - x))
    ((√(z - x) : ℝ) : ℂ) * symmetricEllipticRF x y z = incompleteEllipticF φ k :=
  sqrt_mul_symmetricEllipticRF_eq_incompleteEllipticF' hx hyz hxz

/-- DLMF 19.25.25 with 19.25.23: `(z - x)^{3/2} R_D(x, y, z) = (3/k²)(F(φ, k) - E(φ, k))`, under
the assumptions of (19.25.24) and `y < z` (so that `k ≠ 0`; DLMF divides by `k²`). -/
@[dlmf 19.25.E23, dlmf 19.25.E25]
theorem symmetricEllipticRD_eq_incEllInt {x y z : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hyz : y < z)
    (h0 : (x, y) ≠ (0, 0)) :
    let φ := Real.arccos √(x / z)
    let k := √((z - y) / (z - x))
    (((z - x) ^ (3 / 2 : ℝ) : ℝ) : ℂ) * symmetricEllipticRD x y z =
      3 / (k : ℂ) ^ 2 * (incompleteEllipticF φ k - incompleteEllipticE φ k) := by
  intro φ k
  have hxz : x < z := lt_of_le_of_lt hxy hyz
  obtain ⟨hφ0, hφ1, ex, ey, ez, -, hA, hk2⟩ := real_symmetric_legendre_parametrization hx hyz.le hxz
  have hl : 0 < z - x := by linarith
  have hz : 0 < z := by linarith
  have hy : 0 < y := by
    rcases eq_or_lt_of_le (le_trans hx hxy) with h | h
    · exact absurd (Prod.ext (le_antisymm (h ▸ hxy) hx) h.symm) h0
    · exact h
  have hk : 1 - (k : ℂ) ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane := by
    rw [hA]; exact ofReal_mem_slitPlane.mpr (div_pos hy hz)
  have hk0 : (k : ℂ) ^ 2 ≠ 0 := by
    rw [hk2]; exact ofReal_ne_zero.mpr (div_pos (by linarith) hl).ne'
  rw [ex, ey, ez, symmetricEllipticRD_scale hl _ _ _
      (not_isNegReal_of_mem_slitPlane (csc_sq_mem_slitPlane hφ0 hφ1)),
    ofReal_rpow_three_halves hl, mul_inv_cancel_left₀ (pow_ne_zero _ (ofReal_cpow_half_ne_zero hl)),
    incompleteEllipticE_eq_incompleteEllipticF_sub hφ0.le hφ1 hk,
        incompleteEllipticD_eq_one_third_symmetricEllipticRD hφ0 hφ1,
        sub_sub_cancel,
    ← mul_assoc, div_mul_cancel₀ _ hk0]
  ring

/-- DLMF 19.25.26 with 19.25.23: `(z - x)^{3/2} R_J(x, y, z, p) = (3/α²)(Π(φ, α², k) - F(φ, k))`,
`α² = (z - p)/(z - x) ≠ 0`, under the assumptions of (19.25.24) and `p > 0` (a Cauchy principal
value when `α² sin² φ > 1`, i.e. `p < x`). -/
@[dlmf 19.25.E23, dlmf 19.25.E26]
theorem symmetricEllipticRJ_eq_incEllInt {x y z p : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z)
    (hxz : x < z) (h0 : (x, y) ≠ (0, 0)) (hp : 0 < p) (hpz : p ≠ z) :
    let φ := Real.arccos √(x / z)
    let k := √((z - y) / (z - x))
    let α2 := (z - p) / (z - x)
    (((z - x) ^ (3 / 2 : ℝ) : ℝ) : ℂ) * symmetricEllipticRJ x y z p =
      3 / (α2 : ℂ) * (incompleteEllipticPi φ α2 k - incompleteEllipticF φ k) := by
  intro φ k α2
  obtain ⟨hφ0, hφ1, ex, ey, ez, hs2, hA, hk2⟩ := real_symmetric_legendre_parametrization hx hyz hxz
  have hl : 0 < z - x := by linarith
  have hz : 0 < z := by linarith
  have hy : 0 < y := by
    rcases eq_or_lt_of_le (le_trans hx hxy) with h | h
    · exact absurd (Prod.ext (le_antisymm (h ▸ hxy) hx) h.symm) h0
    · exact h
  have hk : 1 - (k : ℂ) ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane := by
    rw [hA]; exact ofReal_mem_slitPlane.mpr (div_pos hy hz)
  have hα : 1 - (α2 : ℂ) * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane := by
    rw [← ofReal_pow, hs2, show (1 : ℂ) - (α2 : ℂ) * (((z - x) / z : ℝ) : ℂ) = ((p / z : ℝ) : ℂ) by
      have : (z : ℂ) ≠ 0 := ofReal_ne_zero.mpr hz.ne'
      have : ((z : ℂ) - x) ≠ 0 := by exact_mod_cast hl.ne'
      simp only [α2]; push_cast; field_simp; ring]
    exact ofReal_mem_slitPlane.mpr (div_pos hp hz)
  have ep : (p : ℂ) = ((z - x : ℝ) : ℂ) * (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - (α2 : ℂ)) := by
    have hc : 1 / Real.sin φ ^ 2 = z / (z - x) := by rw [hs2, one_div_div]
    exact ofReal_eq_sub_mul_csc_sq_sub (w := p) hxz _ hc
  have hα0 : (α2 : ℂ) ≠ 0 := by
    simp only [α2]
    exact ofReal_ne_zero.mpr (div_ne_zero (sub_ne_zero.mpr (Ne.symm hpz)) hl.ne')
  rw [ex, ey, ez, ep, symmetricEllipticRJ_scale hl _ _ _ _
      (not_isNegReal_of_mem_slitPlane (csc_sq_sub_mem_slitPlane hφ0 hφ1 hα)),
    ofReal_rpow_three_halves hl, mul_inv_cancel_left₀ (pow_ne_zero _ (ofReal_cpow_half_ne_zero hl)),
    incompleteEllipticPi_sub_incompleteEllipticF_eq_integral hφ0.le hφ1 hk hα,
        symmetricEllipticRJ_csc_sq_eq_integral hφ0
        hφ1 _ _
      (not_isNegReal_of_mem_slitPlane (csc_sq_sub_mem_slitPlane hφ0 hφ1 hα)),
    ← mul_assoc, div_mul_cancel₀ _ hα0]

/-- DLMF 19.25.27 with 19.25.23: `2(z - x)^{-1/2} R_G(x, y, z) = E(φ, k) + cot² φ F(φ, k)
+ cot φ √(1 - k² sin² φ)`, under the assumptions of (19.25.24). -/
@[dlmf 19.25.E23, dlmf 19.25.E27]
theorem symmetricEllipticRG_eq_incEllInt {x y z : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z)
    (hxz : x < z) (h0 : (x, y) ≠ (0, 0)) :
    let φ := Real.arccos √(x / z)
    let k := √((z - y) / (z - x))
    2 * (((z - x) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) * symmetricEllipticRG x y z =
      incompleteEllipticE φ k + ((Real.cot φ ^ 2 : ℝ) : ℂ) * incompleteEllipticF φ k +
        ((Real.cot φ * √(1 - k ^ 2 * Real.sin φ ^ 2) : ℝ) : ℂ) := by
  intro φ k
  obtain ⟨hφ0, hφ1, ex, ey, ez, -, hA, -⟩ := real_symmetric_legendre_parametrization hx hyz hxz
  have hl : 0 < z - x := by linarith
  have hz : 0 < z := by linarith
  have hy : 0 < y := by
    rcases eq_or_lt_of_le (le_trans hx hxy) with h | h
    · exact absurd (Prod.ext (le_antisymm (h ▸ hxy) hx) h.symm) h0
    · exact h
  have hk : 1 - (k : ℂ) ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane := by
    rw [hA]; exact ofReal_mem_slitPlane.mpr (div_pos hy hz)
  have hAr : 1 - k ^ 2 * Real.sin φ ^ 2 = y / z := by exact_mod_cast hA
  have hG := two_mul_symmetricEllipticRG (isCarlsonArgument_csc_sq_sub_one hφ0 hφ1)
    (csc_sq_sub_mem_slitPlane hφ0 hφ1 hk) (csc_sq_mem_slitPlane hφ0 hφ1)
  have hE := incompleteEllipticE_eq_symmetricEllipticRF_sub_one_third_symmetricEllipticRD hφ0 hφ1 hk
  have hF : incompleteEllipticF φ k = symmetricEllipticRF (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - 1)
      (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - (k : ℂ) ^ 2) ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) :=
    (incompleteEllipticF_ofReal_eq_integral _ _).trans
        (symmetricEllipticRF_csc_sq_eq_integral hφ0 hφ1 _).symm
  have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ0 (by linarith [Real.pi_pos])
  have hcot2r : Real.cot φ ^ 2 = 1 / Real.sin φ ^ 2 - 1 := by
    rw [Real.cot_eq_cos_div_sin, div_pow]
    have := Real.sin_sq_add_cos_sq φ
    field_simp; linarith
  have hcot2 : ((Real.cot φ ^ 2 : ℝ) : ℂ) = ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - 1 := by
    rw [hcot2r]; push_cast; ring
  have hA0 : 0 ≤ 1 - k ^ 2 * Real.sin φ ^ 2 := by rw [hAr]; positivity
  have hc1 : 0 ≤ 1 / Real.sin φ ^ 2 - 1 := by rw [← hcot2r]; positivity
  have hck : 0 ≤ 1 / Real.sin φ ^ 2 - k ^ 2 := by
    have : 1 / Real.sin φ ^ 2 - k ^ 2 = (1 - k ^ 2 * Real.sin φ ^ 2) / Real.sin φ ^ 2 := by
      field_simp
    rw [this]; positivity
  have hsq : ((Real.cot φ * √(1 - k ^ 2 * Real.sin φ ^ 2) : ℝ) : ℂ) =
      (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - 1) ^ (1 / 2 : ℂ) *
        (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - (k : ℂ) ^ 2) ^ (1 / 2 : ℂ) *
          ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) ^ (-1 / 2 : ℂ) := by
    rw [cot_mul_sqrt_eq_sqrt_csc_sq hφ0 hφ1 hA0, ofReal_div, ofReal_mul,
      ofReal_sqrt_eq_cpow_half hc1, ofReal_sqrt_eq_cpow_half hck,
      ofReal_sqrt_eq_cpow_half (by positivity), ← inv_cpow_half_eq_cpow_neg_half]
    push_cast
    ring
  have hL0 := ofReal_cpow_half_ne_zero hl
  rw [ex, ey, ez, symmetricEllipticRG_scale hl, ofReal_rpow_neg_half hl, hcot2, hsq, hE, hF,
    mul_assoc, inv_mul_cancel_left₀ hL0]
  linear_combination hG

/-! ### §19.25(v) Jacobian elliptic functions -/

/-- The real Glaisher numerator `p(u, k)` for `p ∈ {s, c, d, n}`: `sn, cn, dn, 1` (parameter
`m = k²`), so that `pq = p/q` (DLMF 22.2.10). -/
def jacobiLetterNumerator : JacobiLetter → ℝ → ℝ → ℝ
  | .s, u, m => DLMF.Elliptic.Real.jacobiSnOfParameter u m
  | .c, u, m => DLMF.Elliptic.Real.jacobiCnOfParameter u m
  | .d, u, m => DLMF.Elliptic.Real.jacobiDnOfParameter u m
  | .n, _, _ => 1

/-- DLMF 19.25.28: `Δ(p, q) = ps²(u, k) - qs²(u, k)` for `p, q ∈ {c, d, n}` (real `u`,
parameter `m = k²`), with `Δ(p, q) = -Δ(q, p)`. -/
@[dlmf 19.25.E28]
def jacobiDeltam (p q : JacobiLetter) (u m : ℝ) : ℝ :=
  (jacobiLetterNumerator p u m / DLMF.Elliptic.Real.jacobiSnOfParameter u m) ^ 2 -
    (jacobiLetterNumerator q u m / DLMF.Elliptic.Real.jacobiSnOfParameter u m) ^ 2

/-- DLMF 19.25.28 (antisymmetry): `Δ(p, q) = -Δ(q, p)`. -/
@[dlmf 19.25.E28]
theorem jacobiDeltam_swap (p q : JacobiLetter) (u m : ℝ) :
    jacobiDeltam p q u m = -jacobiDeltam q p u m := by
  unfold jacobiDeltam; ring

/-- DLMF 19.25.29: `Δ(n, d) = k²`, `Δ(d, c) = k'²`, `Δ(n, c) = 1`, for `k² < 1` and
`sn(u, k) ≠ 0` (at the zeros of `sn` the squares `ps²` are poles); stronger than DLMF, which
also assumes `0 ≤ k²`. -/
@[dlmf 19.25.E29]
theorem jacobiDeltam_values {u m : ℝ} (hm : m < 1)
    (hs : DLMF.Elliptic.Real.jacobiSnOfParameter u m ≠ 0) :
    jacobiDeltam .n .d u m = m ∧ jacobiDeltam .d .c u m = 1 - m ∧ jacobiDeltam .n .c u m = 1 := by
  have hsc : DLMF.Elliptic.Real.jacobiSnOfParameter u m ^ 2 +
      DLMF.Elliptic.Real.jacobiCnOfParameter u m ^ 2 = 1 := by
    simp only [DLMF.Elliptic.Real.jacobiSnOfParameter, DLMF.Elliptic.Real.jacobiCnOfParameter,
        Real.sin_sq_add_cos_sq]
  have hd : DLMF.Elliptic.Real.jacobiDnOfParameter u m ^ 2 = 1 - m *
      DLMF.Elliptic.Real.jacobiSnOfParameter u m ^ 2 := by
    have h1 : 0 ≤ 1 - m * DLMF.Elliptic.Real.jacobiSnOfParameter u m ^ 2 := by
      have : DLMF.Elliptic.Real.jacobiSnOfParameter u m ^ 2 ≤ 1 := by
        nlinarith [sq_nonneg (DLMF.Elliptic.Real.jacobiCnOfParameter u m)]
      nlinarith
    rw [DLMF.Elliptic.Real.jacobiDnOfParameter, ← Real.sqrt_eq_rpow, Real.sq_sqrt h1]
  have hs2 : DLMF.Elliptic.Real.jacobiSnOfParameter u m ^ 2 ≠ 0 := pow_ne_zero 2 hs
  refine ⟨?_, ?_, ?_⟩
  · simp only [jacobiDeltam, jacobiLetterNumerator, div_pow]
    field_simp
    linear_combination (-1 : ℝ) * hd
  · simp only [jacobiDeltam, jacobiLetterNumerator, div_pow]
    field_simp
    linear_combination hd - hsc
  · simp only [jacobiDeltam, jacobiLetterNumerator, div_pow]
    field_simp
    linear_combination (-1 : ℝ) * hsc


/-- Round-1 helper: the real `F(φ|m)` as the complex Legendre integral with `k = √m`. -/
private lemma ofReal_incompleteEllipticFOfParameter_eq_integral {m : ℝ} (hm0 : 0 ≤ m)
    (hm : m < 1) (φ : ℝ) :
    ((DLMF.Elliptic.Real.incompleteEllipticFOfParameter φ m : ℝ) : ℂ) = ∫ θ in (0 : ℝ)..φ,
      (1 - ((√m : ℝ) : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) := by
  rw [DLMF.Elliptic.Real.incompleteEllipticFOfParameter, ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hb : 0 ≤ 1 - m * Real.sin θ ^ 2 := by nlinarith [Real.sin_sq_le_one θ]
  rw [ofReal_cpow hb, ofReal_sqrt_sq_of_nonneg hm0]
  push_cast
  ring_nf

/-- Round-1 helper: for `0 < u ≤ K(m)`, `0 < am(u|m) ≤ π/2`. -/
private lemma jacobiAmOfParameter_mem_Ioc {u m : ℝ} (hm : m < 1) (hu : 0 < u)
    (huK : u ≤ DLMF.Elliptic.Real.completeEllipticKOfParameter m) :
    0 < DLMF.Elliptic.Real.jacobiAmOfParameter u m ∧
        DLMF.Elliptic.Real.jacobiAmOfParameter u m ≤ π / 2 := by
  have hmono := DLMF.Elliptic.Real.strictMono_incompleteEllipticFOfParameter hm
  have hF := DLMF.Elliptic.Real.incompleteEllipticFOfParameter_jacobiAmOfParameter hm u
  have hF0 : DLMF.Elliptic.Real.incompleteEllipticFOfParameter 0 m = 0 := by
      simp [DLMF.Elliptic.Real.incompleteEllipticFOfParameter]
  constructor
  · have : DLMF.Elliptic.Real.incompleteEllipticFOfParameter 0 m <
        DLMF.Elliptic.Real.incompleteEllipticFOfParameter
            (DLMF.Elliptic.Real.jacobiAmOfParameter u m) m := by
      rw [hF, hF0]; exact hu
    exact hmono.lt_iff_lt.mp this
  · have : DLMF.Elliptic.Real.incompleteEllipticFOfParameter
        (DLMF.Elliptic.Real.jacobiAmOfParameter u m) m ≤
        DLMF.Elliptic.Real.incompleteEllipticFOfParameter (π / 2) m := by
      rw [hF, DLMF.Elliptic.Real.incompleteEllipticFOfParameter_pi_div_two]; exact huK
    exact hmono.le_iff_le.mp this

/-- DLMF 19.25.30, **corrected domain**: `am(u, k) = R_C(cs²(u, k), ns²(u, k))` for
`0 ≤ k² < 1` and `0 < u ≤ K(k)`. DLMF's condition `cs²(u, k) ≥ 0` does not suffice: it holds for
every real `u`, but for `K < u < 2K` the right side equals `π - am(u, k)`. This is stronger than
`jacobiAmOfParameter_eq_symmetricEllipticRC`, which also assumes `0 ≤ k²`. -/
@[dlmf 19.25.E30]
theorem jacobiAmOfParameter_eq_symmetricEllipticRC' {u m : ℝ} (hm : m < 1) (hu : 0 < u)
    (huK : u ≤ DLMF.Elliptic.Real.completeEllipticKOfParameter m) :
    (DLMF.Elliptic.Real.jacobiAmOfParameter u m : ℂ) =
      symmetricEllipticRC
        (((DLMF.Elliptic.Real.jacobiCnOfParameter u m /
            DLMF.Elliptic.Real.jacobiSnOfParameter u m) ^ 2 : ℝ) : ℂ)
        (((1 / DLMF.Elliptic.Real.jacobiSnOfParameter u m) ^ 2 : ℝ) : ℂ) := by
  obtain ⟨h0, h1⟩ := jacobiAmOfParameter_mem_Ioc hm hu huK
  set φ := DLMF.Elliptic.Real.jacobiAmOfParameter u m with hφ
  have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos φ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], h1⟩
  have hsc := Real.sin_sq_add_cos_sq φ
  have hsn : DLMF.Elliptic.Real.jacobiSnOfParameter u m = Real.sin φ := rfl
  have hcn : DLMF.Elliptic.Real.jacobiCnOfParameter u m = Real.cos φ := rfl
  rw [hsn, hcn]
  have hlt : (Real.cos φ / Real.sin φ) ^ 2 < (1 / Real.sin φ) ^ 2 := by
    rw [div_pow, div_pow]
    exact div_lt_div_of_pos_right (by nlinarith) (by positivity)
  rw [(symmetricEllipticRC_of_lt (sq_nonneg _) hlt).1]
  have e1 : (Real.cos φ / Real.sin φ) ^ 2 / (1 / Real.sin φ) ^ 2 = Real.cos φ ^ 2 := by
    field_simp
  have e2 : (1 / Real.sin φ) ^ 2 - (Real.cos φ / Real.sin φ) ^ 2 = 1 := by
    field_simp; linarith
  rw [e1, e2, Real.sqrt_sq hc, Real.sqrt_one, div_one, Real.arccos_cos h0.le
    (by linarith [Real.pi_pos])]

/-- DLMF 19.25.30, **corrected domain**: `am(u, k) = R_C(cs²(u, k), ns²(u, k))` for
`0 ≤ k² < 1` and `0 < u ≤ K(k)`. DLMF's condition `cs²(u, k) ≥ 0` does not suffice: it holds for
every real `u`, but for `K < u < 2K` the right side equals `π - am(u, k)`. -/
@[dlmf 19.25.E30]
theorem jacobiAmOfParameter_eq_symmetricEllipticRC {u m : ℝ} (_hm0 : 0 ≤ m)
    (hm : m < 1) (hu : 0 < u)
    (huK : u ≤ DLMF.Elliptic.Real.completeEllipticKOfParameter m) :
    (DLMF.Elliptic.Real.jacobiAmOfParameter u m : ℂ) =
      symmetricEllipticRC
        (((DLMF.Elliptic.Real.jacobiCnOfParameter u m /
            DLMF.Elliptic.Real.jacobiSnOfParameter u m) ^ 2 : ℝ) : ℂ)
        (((1 / DLMF.Elliptic.Real.jacobiSnOfParameter u m) ^ 2 : ℝ) : ℂ) :=
  jacobiAmOfParameter_eq_symmetricEllipticRC' hm hu huK

/-- DLMF 19.25.31, **corrected domain**: `u = R_F(ps²(u, k), qs²(u, k), rs²(u, k))` for
`p, q, r` any permutation of `c, d, n` (by the symmetry of `R_F` it suffices to take `c, d, n`),
`0 ≤ k² < 1` and `0 < u ≤ K(k)` (DLMF: `cs² ≥ 0`; the formula fails for `K < u < 2K`). -/
@[dlmf 19.25.E31]
theorem eq_symmetricEllipticRF_jacobi {u m : ℝ} (hm0 : 0 ≤ m) (hm : m < 1) (hu : 0 < u)
    (huK : u ≤ DLMF.Elliptic.Real.completeEllipticKOfParameter m) :
    (u : ℂ) = symmetricEllipticRF
      (((DLMF.Elliptic.Real.jacobiCnOfParameter u m /
          DLMF.Elliptic.Real.jacobiSnOfParameter u m) ^ 2 : ℝ) : ℂ)
      (((DLMF.Elliptic.Real.jacobiDnOfParameter u m /
          DLMF.Elliptic.Real.jacobiSnOfParameter u m) ^ 2 : ℝ) : ℂ)
      (((1 / DLMF.Elliptic.Real.jacobiSnOfParameter u m) ^ 2 : ℝ) : ℂ) := by
  obtain ⟨h0, h1⟩ := jacobiAmOfParameter_mem_Ioc hm hu huK
  have hs : 0 < Real.sin (DLMF.Elliptic.Real.jacobiAmOfParameter u m) :=
    Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hF := DLMF.Elliptic.Real.incompleteEllipticFOfParameter_jacobiAmOfParameter hm u
  have hb : 0 ≤ 1 - m * DLMF.Elliptic.Real.jacobiSnOfParameter u m ^ 2 := by
    unfold DLMF.Elliptic.Real.jacobiSnOfParameter; nlinarith
        [Real.sin_sq_le_one (DLMF.Elliptic.Real.jacobiAmOfParameter u m)]
  have e1 : (((DLMF.Elliptic.Real.jacobiCnOfParameter u m /
      DLMF.Elliptic.Real.jacobiSnOfParameter u m) ^ 2 : ℝ) : ℂ) =
      ((1 / Real.sin (DLMF.Elliptic.Real.jacobiAmOfParameter u m) ^ 2 : ℝ) : ℂ) - 1 := by
    have : (DLMF.Elliptic.Real.jacobiCnOfParameter u m /
        DLMF.Elliptic.Real.jacobiSnOfParameter u m) ^ 2 =
        1 / Real.sin (DLMF.Elliptic.Real.jacobiAmOfParameter u m) ^ 2 - 1 := by
      unfold DLMF.Elliptic.Real.jacobiCnOfParameter DLMF.Elliptic.Real.jacobiSnOfParameter
      have := Real.sin_sq_add_cos_sq (DLMF.Elliptic.Real.jacobiAmOfParameter u m)
      field_simp; linarith
    rw [this]; push_cast; ring
  have e2 : (((DLMF.Elliptic.Real.jacobiDnOfParameter u m /
      DLMF.Elliptic.Real.jacobiSnOfParameter u m) ^ 2 : ℝ) : ℂ) =
      ((1 / Real.sin (DLMF.Elliptic.Real.jacobiAmOfParameter u m) ^ 2 : ℝ) : ℂ) -
          ((√m : ℝ) : ℂ) ^ 2 := by
    have : (DLMF.Elliptic.Real.jacobiDnOfParameter u m /
        DLMF.Elliptic.Real.jacobiSnOfParameter u m) ^ 2 =
        1 / Real.sin (DLMF.Elliptic.Real.jacobiAmOfParameter u m) ^ 2 - m := by
      rw [div_pow, DLMF.Elliptic.Real.jacobiDnOfParameter, ← Real.sqrt_eq_rpow, Real.sq_sqrt hb]
      unfold DLMF.Elliptic.Real.jacobiSnOfParameter
      field_simp
    rw [this, ofReal_sqrt_sq_of_nonneg hm0]; push_cast; ring
  have e3 : (((1 / DLMF.Elliptic.Real.jacobiSnOfParameter u m) ^ 2 : ℝ) : ℂ) =
      ((1 / Real.sin (DLMF.Elliptic.Real.jacobiAmOfParameter u m) ^ 2 : ℝ) : ℂ) := by
    unfold DLMF.Elliptic.Real.jacobiSnOfParameter; push_cast; ring
  rw [e1, e2, e3, symmetricEllipticRF_csc_sq_eq_integral h0 h1,
      ← ofReal_incompleteEllipticFOfParameter_eq_integral hm0 hm, hF]

/-! ### §19.25(vi) Weierstrass elliptic functions -/

/-- DLMF 19.25.35 with 19.25.36: if `z ∉ 𝕃` and `℘(z) - e_j ∈ ℂ \ (-∞, 0]` for `j = 1, 2, 3`,
then `z + 2ω = ± R_F(℘(z) - e₁, ℘(z) - e₂, ℘(z) - e₃)` for some `2ω ∈ 𝕃` and some sign (the sign
changes across the curves where some `℘(z) - e_j < 0`). -/
@[dlmf 19.25.E35, dlmf 19.25.E36]
theorem weierstrassP_symmetricEllipticRF (H : DLMF.Weierstrass.HalfPeriods) {z : ℂ}
    (hz : z ∉ H.lattice)
    (hP : ∀ j ∈ ({1, 2, 3} : Finset ℕ), H.weierstrassP z - H.e j ∈ slitPlane) :
    ∃ w ∈ H.lattice, ∃ s : ℂ, (s = 1 ∨ s = -1) ∧
      z + w = s * symmetricEllipticRF (H.weierstrassP z - H.e 1) (H.weierstrassP z - H.e 2)
        (H.weierstrassP z - H.e 3) := by
  sorry

/-- DLMF 19.25.37 (with 19.25.35, the same sign and `ω`): under the hypotheses of (19.25.35),
`ζ(z + 2ω) + (z + 2ω) ℘(z) = ± 2 R_G(℘(z) - e₁, ℘(z) - e₂, ℘(z) - e₃)`. -/
@[dlmf 19.25.E35, dlmf 19.25.E37]
theorem weierstrassZeta_symmetricEllipticRG (H : DLMF.Weierstrass.HalfPeriods) {z : ℂ}
    (hz : z ∉ H.lattice)
    (hP : ∀ j ∈ ({1, 2, 3} : Finset ℕ), H.weierstrassP z - H.e j ∈ slitPlane) :
    ∃ w ∈ H.lattice, ∃ s : ℂ, (s = 1 ∨ s = -1) ∧
      z + w = s * symmetricEllipticRF (H.weierstrassP z - H.e 1) (H.weierstrassP z - H.e 2)
        (H.weierstrassP z - H.e 3) ∧
      H.weierstrassZeta (z + w) + (z + w) * H.weierstrassP z =
        s * (2 * symmetricEllipticRG (H.weierstrassP z - H.e 1) (H.weierstrassP z - H.e 2)
          (H.weierstrassP z - H.e 3)) := by
  sorry

/-- DLMF 19.25.38–19.25.39: for `j, k, ℓ` any permutation of `1, 2, 3` there is `ω_j` with
`2ω_j ∈ 𝕃` and `℘(ω_j) = e_j` such that `ω_j = R_F(0, e_j - e_k, e_j - e_ℓ)` and
`ζ(ω_j) + ω_j e_j = 2 R_G(0, e_j - e_k, e_j - e_ℓ)`; we assume `e_j - e_k, e_j - e_ℓ` lie in
`ℂ \ (-∞, 0]`. -/
@[dlmf 19.25.E38, dlmf 19.25.E39]
theorem halfPeriod_eq_symmetricEllipticRF (H : DLMF.Weierstrass.HalfPeriods)
    (σ : Equiv.Perm (Fin 3))
    (hk : H.e (σ 0 + 1) - H.e (σ 1 + 1) ∈ slitPlane)
    (hl : H.e (σ 0 + 1) - H.e (σ 2 + 1) ∈ slitPlane) :
    ∃ ω : ℂ, 2 * ω ∈ H.lattice ∧ H.weierstrassP ω = H.e (σ 0 + 1) ∧
      ω = symmetricEllipticRF 0 (H.e (σ 0 + 1) - H.e (σ 1 + 1)) (H.e (σ 0 + 1) - H.e (σ 2 + 1)) ∧
      H.weierstrassZeta ω + ω * H.e (σ 0 + 1) =
        2 * symmetricEllipticRG 0 (H.e (σ 0 + 1) - H.e (σ 1 + 1))
            (H.e (σ 0 + 1) - H.e (σ 2 + 1)) := by
  sorry

/-- DLMF 19.25.41: `σ_j(z) = exp(-η_j z) σ(z + ω_j)/σ(ω_j)`, `j = 1, 2, 3`, with
`η_j = ζ(ω_j)` (23.2.12) and `ω₂ = -ω₁ - ω₃`. -/
@[dlmf 19.25.E41]
def weierstrassSigmaIdx (H : DLMF.Weierstrass.HalfPeriods) (j : ℕ) (z : ℂ) : ℂ :=
  cexp (-(H.eta j * z)) * H.weierstrassSigma (z + H.halfPeriod j) /
    H.weierstrassSigma (H.halfPeriod j)

/-- DLMF 19.25.40: `z + 2ω = ± σ(z) R_F(σ₁²(z), σ₂²(z), σ₃²(z))` for some `2ω ∈ 𝕃` and some sign
(changing across curves where some `σ_j²(z) < 0`), for `z ∉ 𝕃` with `σ_j²(z) ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.25.E40]
theorem eq_weierstrassSigma_mul_symmetricEllipticRF (H : DLMF.Weierstrass.HalfPeriods) {z : ℂ}
    (hz : z ∉ H.lattice)
    (hσ : ∀ j ∈ ({1, 2, 3} : Finset ℕ), weierstrassSigmaIdx H j z ^ 2 ∈ slitPlane) :
    ∃ w ∈ H.lattice, ∃ s : ℂ, (s = 1 ∨ s = -1) ∧
      z + w = s * H.weierstrassSigma z * symmetricEllipticRF (weierstrassSigmaIdx H 1 z ^ 2)
        (weierstrassSigmaIdx H 2 z ^ 2) (weierstrassSigmaIdx H 3 z ^ 2) := by
  sorry

/-! ### §19.25(vii) Hypergeometric function -/

/-- DLMF 19.25.42: `₂F₁(a, b; c; z) = R_{-a}(b, c - b; 1 - z, 1)`, for `|z| < 1` (the Gauss
series) and `c ∉ {0, -1, -2, …}`; all complex `a, b` (Carlson's continuation of `R`). -/
@[dlmf 19.25.E42]
theorem ordinaryHypergeometric_eq_symmetricEllipticR (a b c : ℂ) (hc : ∀ n : ℕ, c ≠ -n) {z : ℂ}
    (hz : ‖z‖ < 1) :
    ordinaryHypergeometric a b c z = symmetricEllipticR a ![b, c - b] ![1 - z, 1] := by
  have hre : 0 < (1 - z).re := by
    have := (abs_re_le_norm z).trans_lt hz
    simp only [sub_re, one_re]
    linarith [le_abs_self z.re]
  have hw : (1 - z) ∈ slitPlane := Or.inl hre
  rw [symmetricEllipticR_of_mem _ _ (vec2_mem_carlsonRSlitDomain hw one_mem_slitPlane)]
  have h := Carlson.regCarlsonR_pair_one_sub_eq_regularizedGaussHGFun a b c hz
  unfold Carlson.carlsonR
  have e1 : (![b, c - b] : Fin 2 → ℂ) = Carlson.TwoVariable.pair b (c - b) := rfl
  have e2 : (![1 - z, 1] : Fin 2 → ℂ) = Carlson.TwoVariable.pair (1 - z) 1 := rfl
  rw [e1, e2, Carlson.TwoVariable.regCarlsonR_pair_swap _ _ _ one_mem_slitPlane hw, h,
    ← ordinaryHypergeometric_div_Gamma_eq hc]
  have hsum : ∑ i, Carlson.TwoVariable.pair b (c - b) i = c := by
    simp only [Fin.sum_univ_two, Carlson.TwoVariable.pair_zero, Carlson.TwoVariable.pair_one]
    ring
  rw [hsum, mul_div_cancel₀ _ (Complex.Gamma_ne_zero hc)]

/-- DLMF 19.25.43: `R_{-a}(b₁, b₂; z₁, z₂) = z₂^{-a} ₂F₁(a, b₁; b₁ + b₂; 1 - z₁/z₂)`, for
`z₁, z₂ ∈ ℂ \ (-∞, 0]` with `|1 - z₁/z₂| < 1` and `arg z₁ - arg z₂ ∈ (-π, π)` (so that
`z₂^{-a}` and the homogeneity of `R` match the principal branches), `b₁ + b₂ ∉ {0, -1, …}`. -/
@[dlmf 19.25.E43]
theorem symmetricEllipticR_two_eq_ordinaryHypergeometric (a b₁ b₂ : ℂ) (hb : ∀ n : ℕ, b₁ + b₂ ≠ -n)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ slitPlane) (hz₂ : z₂ ∈ slitPlane) (hz : ‖1 - z₁ / z₂‖ < 1)
    (harg : arg z₁ - arg z₂ ∈ Ioo (-π) π) :
    symmetricEllipticR a ![b₁, b₂] ![z₁, z₂] = z₂ ^ (-a) * ordinaryHypergeometric a b₁ (b₁ + b₂)
        (1 - z₁ / z₂) := by
  have h₂ : z₂ ≠ 0 := slitPlane_ne_zero hz₂
  have h₁ : z₁ ≠ 0 := slitPlane_ne_zero hz₁
  have hdivarg : arg (z₁ / z₂) = arg z₁ - arg z₂ := by
    rw [div_eq_mul_inv, arg_mul h₁ (inv_ne_zero h₂)]
    · rw [arg_inv, ite_eq_right (mem_slitPlane_iff_arg.mp hz₂).1]
      ring
    · rw [arg_inv, ite_eq_right (mem_slitPlane_iff_arg.mp hz₂).1]
      change -π < arg z₁ + -arg z₂ ∧ arg z₁ + -arg z₂ ≤ π
      simpa only [sub_eq_add_neg] using And.intro harg.1 harg.2.le
  have hdiv : z₁ / z₂ ∈ slitPlane := by
    apply mem_slitPlane_iff.mpr
    left
    have hr := (abs_re_le_norm (1 - z₁ / z₂)).trans_lt hz
    simp only [sub_re, one_re] at hr
    linarith [le_abs_self (1 - (z₁ / z₂).re)]
  rw [ordinaryHypergeometric_eq_symmetricEllipticR a b₁ (b₁ + b₂) hb hz]
  simp only [show b₁ + b₂ - b₁ = b₂ by ring, sub_sub_cancel]
  have hnodes : (![z₁, z₂] : Fin 2 → ℂ) = fun i => z₂ * ![z₁ / z₂, 1] i := by
    funext i
    fin_cases i
    · exact (mul_div_cancel₀ z₁ h₂).symm
    · simp
  rw [hnodes, symmetricEllipticR_mul a _ (vec2_mem_carlsonRSlitDomain hdiv one_mem_slitPlane) hz₂]
  intro i
  fin_cases i
  · change arg z₂ + arg (z₁ / z₂) ∈ Ioo (-π) π
    rw [hdivarg, show arg z₂ + (arg z₁ - arg z₂) = arg z₁ by ring]
    exact ⟨neg_pi_lt_arg z₁,
      lt_of_le_of_ne (arg_le_pi z₁) (mem_slitPlane_iff_arg.mp hz₁).1⟩
  · change arg z₂ + arg 1 ∈ Ioo (-π) π
    rw [arg_one, add_zero]
    exact ⟨neg_pi_lt_arg z₂,
      lt_of_le_of_ne (arg_le_pi z₂) (mem_slitPlane_iff_arg.mp hz₂).1⟩

/-! ### Round-1 helpers: the lemniscate constants -/

/-- Round-1 helper (DLMF 19.21.1 at `z = 1`): `R_F(0, 1, 2) · (1/3) R_D(0, 2, 1) = π/4`. -/
theorem symmetricEllipticRF_mul_symmetricEllipticRD_lemniscate :
    symmetricEllipticRF 0 1 2 * ((1 / 3) * symmetricEllipticRD 0 2 1) = π / 4 := by
  have hL := DLMF.Elliptic.legendre_relation (m := 1 / 2) (by norm_num) (by norm_num)
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hL
  set k : ℂ := ((√(1 / 2 : ℝ) : ℝ) : ℂ) with hk
  have hk2 : k ^ 2 = ((1 / 2 : ℝ) : ℂ) := ofReal_sqrt_sq_of_nonneg (by norm_num)
  have hK := completeEllipticK_eq_ofReal (k := k) (m := 1 / 2) hk2 (by norm_num)
  have hE := completeEllipticE_eq_ofReal (k := k) (m := 1 / 2) hk2 (by norm_num)
  have hk2' : k ^ 2 = 1 / 2 := by rw [hk2]; push_cast; ring
  have h12 : (1 / 2 : ℂ) ∈ slitPlane := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
    exact ofReal_mem_slitPlane.mpr (by norm_num)
  have hmem : 1 - k ^ 2 ∈ slitPlane := by
    rw [hk2', show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num]; exact h12
  obtain ⟨-, -, -, -, h5⟩ := completeEllipticE_eq_symmetricElliptic hmem
  have hKF := completeEllipticK_eq_symmetricEllipticRF hmem
  rw [hk2', show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num] at h5 hKF
  have hl : (0 : ℝ) < 2 := by norm_num
  have hA := symmetricEllipticRF_scale hl 0 (1 / 2) 1
  have hB := symmetricEllipticRD_scale hl 0 1 (1 / 2) (not_isNegReal_of_mem_slitPlane h12)
  simp only [mul_zero, mul_one, ofReal_ofNat] at hA hB
  rw [show (2 : ℂ) * (1 / 2) = 1 by norm_num] at hA hB
  rw [hA, hB, ← hKF]
  have hL2 := ofReal_cpow_half_sq (l := 2)
  have hL0 := ofReal_cpow_half_ne_zero hl
  simp only [ofReal_ofNat] at hL2 hL0
  have hLc : ((completeEllipticE k * EllipticIntegrals.completeEllipticK k + completeEllipticE k *
      EllipticIntegrals.completeEllipticK k -
      EllipticIntegrals.completeEllipticK k *
          EllipticIntegrals.completeEllipticK k : ℂ)) = π / 2 := by
    rw [hK, hE]; exact_mod_cast hL
  generalize (2 : ℂ) ^ (1 / 2 : ℂ) = L at hL2 hL0 ⊢
  have hL4 : L ^ 4 = 4 := by rw [show L ^ 4 = (L ^ 2) ^ 2 by ring, hL2]; norm_num
  rw [show L⁻¹ * EllipticIntegrals.completeEllipticK k *
      (1 / 3 * ((L ^ 3)⁻¹ * symmetricEllipticRD 0 1 (1 / 2)))
      =
      EllipticIntegrals.completeEllipticK k * symmetricEllipticRD 0 1 (1 / 2) * (L ^ 4)⁻¹ / 3 by
          field_simp, hL4]
  linear_combination (-EllipticIntegrals.completeEllipticK k) * h5 + (1 / 2 : ℂ) * hLc

/-- Round-1 helper: `R_F(0, 1, 2) = Γ(1/4)²/(4 √(2π))` (DLMF 19.20.2). -/
theorem symmetricEllipticRF_zero_one_two :
    symmetricEllipticRF 0 1 2 = ((Real.Gamma (1 / 4) ^ 2 / (4 * Real.sqrt (2 * π)) : ℝ) : ℂ) := by
  set k : ℂ := ((√(1 / 2 : ℝ) : ℝ) : ℂ) with hk
  have hk2 : k ^ 2 = ((1 / 2 : ℝ) : ℂ) := ofReal_sqrt_sq_of_nonneg (by norm_num)
  have hK := completeEllipticK_eq_ofReal (k := k) (m := 1 / 2) hk2 (by norm_num)
  have hk2' : k ^ 2 = 1 / 2 := by rw [hk2]; push_cast; ring
  have h12 : (1 / 2 : ℂ) ∈ slitPlane := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
    exact ofReal_mem_slitPlane.mpr (by norm_num)
  have hmem : 1 - k ^ 2 ∈ slitPlane := by
    rw [hk2', show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num]; exact h12
  have hKF := completeEllipticK_eq_symmetricEllipticRF hmem
  rw [hk2', show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num] at hKF
  have hl : (0 : ℝ) < 2 := by norm_num
  have hA := symmetricEllipticRF_scale hl 0 (1 / 2) 1
  simp only [mul_zero, mul_one, ofReal_ofNat] at hA
  rw [show (2 : ℂ) * (1 / 2) = 1 by norm_num] at hA
  have h2 : (2 : ℂ) ^ (1 / 2 : ℂ) = ((√2 : ℝ) : ℂ) := by
    rw [ofReal_sqrt_eq_cpow_half (by norm_num)]; push_cast; ring_nf
  rw [hA, ← hKF, hK, DLMF.Elliptic.Real.completeEllipticKOfParameter_one_half, h2,
      Real.sqrt_mul (by norm_num)]
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hsπ : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  push_cast
  field_simp

/-- Round-1 helper: `∫₀¹ t² dt/√(1 - t⁴) = ∫₀^{π/2} sin² θ dθ/√(1 + sin² θ)` (`t = sin θ`). -/
private lemma integral_sq_div_sqrt_eq_integral_sin :
    ∫ t in (0 : ℝ)..1, t ^ 2 / Real.sqrt (1 - t ^ 4) =
      ∫ θ in (0 : ℝ)..(π / 2), Real.sin θ ^ 2 / Real.sqrt (1 + Real.sin θ ^ 2) := by
  have hcv := MeasureTheory.integral_image_eq_integral_abs_deriv_smul (f := Real.sin)
    (f' := Real.cos) (measurableSet_Ioo (a := (0 : ℝ)) (b := π / 2))
    (fun θ _ => (Real.hasDerivAt_sin θ).hasDerivWithinAt)
    (Real.injOn_sin.mono fun θ (hθ : θ ∈ Ioo 0 (π / 2)) =>
      (⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩ : θ ∈ Icc (-(π / 2)) (π / 2)))
    (fun t => t ^ 2 / Real.sqrt (1 - t ^ 4))
  have himg := DLMF.Elliptic.sin_image_Ioo_arcsin (x := 1) zero_le_one le_rfl
  rw [Real.arcsin_one] at himg
  rw [himg] at hcv
  rw [intervalIntegral.integral_of_le zero_le_one, MeasureTheory.integral_Ioc_eq_integral_Ioo, hcv,
    intervalIntegral.integral_of_le (by positivity), MeasureTheory.integral_Ioc_eq_integral_Ioo]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have hc : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  simp only [smul_eq_mul]
  have e : 1 - Real.sin θ ^ 4 = Real.cos θ ^ 2 * (1 + Real.sin θ ^ 2) := by
    have := Real.sin_sq_add_cos_sq θ
    have : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by linarith
    rw [this]; ring
  rw [abs_of_pos hc, e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc.le]
  have : 0 < Real.sqrt (1 + Real.sin θ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  field_simp

/-- Round-1 helper: `∫₀¹ t² dt/√(1 - t⁴) = (1/3) R_D(0, 2, 1)` (DLMF 19.20.22). -/
theorem integral_sq_div_sqrt_one_sub_pow_four :
    ((∫ t in (0 : ℝ)..1, t ^ 2 / Real.sqrt (1 - t ^ 4) : ℝ) : ℂ) =
      (1 / 3) * symmetricEllipticRD 0 2 1 := by
  have hp : (0 : ℝ) < π / 2 := by positivity
  have hD := symmetricEllipticRD_csc_sq_eq_integral hp le_rfl I
  rw [csc_sq_pi_div_two, sub_self, I_sq, show (1 : ℂ) - -1 = 2 by norm_num] at hD
  rw [hD, integral_sq_div_sqrt_eq_integral_sin, ← intervalIntegral.integral_ofReal]
  rw [← mul_assoc, show (1 / 3 : ℂ) * 3 = 1 by norm_num, one_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [ofReal_div, ofReal_sqrt_eq_cpow_half (by positivity), cpow_neg]
  push_cast
  ring_nf

end DLMF.EllipticIntegrals
