/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Symmetric
public import DLMF.EllipticIntegrals.Legendre
public import DLMF.EllipticIntegrals.SymmetricAddition
public import DLMF.JacobiElliptic.Inverse
public import DLMF.Weierstrass.Basic
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Relations of the symmetric integrals to other functions (DLMF §19.25)

* §19.25(i): Legendre's integrals as symmetric integrals, (19.25.1)–(19.25.18), with
  `c = csc² φ`;
* §19.25(ii): Bulirsch's integrals as symmetric integrals, (19.25.19)–(19.25.22), `r = 1/x²`;
* §19.25(iii): symmetric integrals as Legendre's integrals, (19.25.23)–(19.25.27);
* §19.25(iv): theta functions — a pointer to §20.9(i) (19.25.iv.p1), no formula;
* §19.25(v): Jacobian elliptic functions, (19.25.28)–(19.25.34);
* §19.25(vi): Weierstrass elliptic functions, (19.25.35)–(19.25.41);
* §19.25(vii): the Gauss hypergeometric function, (19.25.42)–(19.25.43).

Legendre's integrals are the complex `DLMF.EllipticIntegrals.incEllIntFk` etc. of
`DLMF.EllipticIntegrals.Legendre` (segment path from `0` to `φ`, principal powers, a Cauchy
principal value for `Π`), `K(k)` is `DLMF.JacobiElliptic.compEllIntKk`. Jacobian functions are
the project's real `DLMF.Elliptic.Real.jacobiSnm` etc. (parameter `m = k²`) and the inverse
functions of `DLMF.JacobiElliptic.Inverse`; Weierstrass functions are those of
`DLMF.Weierstrass` on the lattice of `H : HalfPeriods`; `₂F₁` is Mathlib's
`ordinaryHypergeometric` (the Gauss series, `|z| < 1`).

**Domains and corrections** (numerical evidence with mpmath recorded in the ledger):
* §19.25(i) is stated for **real** `φ ∈ (0, π/2]` and complex `k` with `1 - k² sin² φ` off
  `(-∞, 0]`. DLMF allows `0 ≤ ℜ φ ≤ π/2`; with Legendre's integral along the segment `[0, φ]`
  and principal branches, (19.25.5) and (19.25.7) fail when both `φ` and `k` are nonreal
  (e.g. `φ = 0.771 + 0.492i`, `k = -1.32 + 0.604i`), although they hold for real `φ` and for
  real `k² < 1`.
* (19.25.30)–(19.25.31): DLMF's condition `cs²(u, k) ≥ 0` holds for all real `u` but the
  formulas fail for `K < u < 2K` (the right sides are symmetric under `u ↦ 2K - u`); acquired for
  `0 < u ≤ K`.
* (19.25.32)–(19.25.34): DLMF's conditions on `x²` allow negative `x`, where the formulas fail
  for `arccs`, `arccd`, `arccn` (the right sides are even in `x`); acquired for `x ≥ 0`.
* (19.25.25) divides by `k²`; we assume `y < z` (so `k ≠ 0`).
* (19.25.38)–(19.25.40) assume the arguments of `R_F`, `R_G` lie in `ℂ \ (-∞, 0]` (DLMF uses its
  conventions on the cut implicitly).

## References

* NIST DLMF §19.25.
* B. C. Carlson, *Special Functions of Applied Mathematics*, 1977, (9.2-11), (9.2-14), (9.3-2);
  formalized in `lean-codes` (`Carlson.Real.incEllIntFk_eq`, `Carlson.Real.compEllIntKk_eq`).
-/

@[expose] public noncomputable section

open Complex Set
open scoped Real

namespace DLMF.EllipticIntegrals

open DLMF.JacobiElliptic

/-! ### §19.25(i) Legendre's integrals as symmetric integrals -/

/-- DLMF 19.25.1 (first formula): `K(k) = R_F(0, k'², 1)`, `k'² = 1 - k²`, for complex `k` with
`k'² ∈ ℂ \ (-∞, 0]` (`k² ∉ [1, ∞)`, the principal domain of `K`). -/
@[dlmf 19.25.E1]
theorem compEllIntKk_eq_symEllIntRF {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) :
    compEllIntKk k = symEllIntRF 0 (1 - k ^ 2) 1 := by
  sorry

/-- DLMF 19.25.1 (first formula) for real `k² < 1`. From `lean-codes`'
`Carlson.Real.compEllIntKk_eq` (Carlson (9.2-14)). -/
@[dlmf 19.25.E1]
theorem compEllIntKk_ofReal_eq_symEllIntRF {k : ℝ} (hk : k ^ 2 < 1) :
    compEllIntKk k = symEllIntRF 0 ((1 - k ^ 2 : ℝ) : ℂ) 1 := by
  rw [compEllIntKk_ofReal_carlson hk.le, Carlson.Real.compEllIntKk_eq hk,
    ei19d_symEllIntRF_zero_eq_carlsonRK (ofReal_mem_slitPlane.mpr (by linarith)) one_mem_slitPlane]

/-- DLMF 19.25.1 (second to fifth formulas): with `k'² = 1 - k² ∈ ℂ \ (-∞, 0]`,
`E(k) = 2 R_G(0, k'², 1) = (1/3) k'² (R_D(0, k'², 1) + R_D(0, 1, k'²))`,
`K(k) - E(k) = k² D(k) = (1/3) k² R_D(0, k'², 1)` and
`E(k) - k'² K(k) = (1/3) k² k'² R_D(0, 1, k'²)`. -/
@[dlmf 19.25.E1]
theorem compEllIntEk_eq_symEllInt {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) :
    compEllIntEk k = 2 * symEllIntRG 0 (1 - k ^ 2) 1 ∧
      compEllIntEk k = (1 / 3) * (1 - k ^ 2) *
        (symEllIntRD 0 (1 - k ^ 2) 1 + symEllIntRD 0 1 (1 - k ^ 2)) ∧
      compEllIntKk k - compEllIntEk k = k ^ 2 * compEllIntDk k ∧
      k ^ 2 * compEllIntDk k = (1 / 3) * k ^ 2 * symEllIntRD 0 (1 - k ^ 2) 1 ∧
      compEllIntEk k - (1 - k ^ 2) * compEllIntKk k =
        (1 / 3) * k ^ 2 * (1 - k ^ 2) * symEllIntRD 0 1 (1 - k ^ 2) := by
  sorry

/-- DLMF 19.25.2: `Π(α², k) - K(k) = (1/3) α² R_J(0, k'², 1, 1 - α²)`, for `k'² = 1 - k²` and
`1 - α²` in `ℂ \ (-∞, 0]` (no principal value). -/
@[dlmf 19.25.E2]
theorem compEllIntPik_sub_compEllIntKk {k α2 : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane)
    (hα : 1 - α2 ∈ slitPlane) :
    compEllIntPik α2 k - compEllIntKk k = (1 / 3) * α2 * symEllIntRJ 0 (1 - k ^ 2) 1 (1 - α2) := by
  sorry

/-- DLMF 19.25.3: `Π(α², k) = (π/2) R_{-1/2}(1/2, -1/2, 1; k'², 1, 1 - α²)`, for `k'² = 1 - k²`
and `1 - α²` in `ℂ \ (-∞, 0]`. -/
@[dlmf 19.25.E3]
theorem compEllIntPik_eq_symEllIntR {k α2 : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane)
    (hα : 1 - α2 ∈ slitPlane) :
    compEllIntPik α2 k =
      (π / 2) * symEllIntR (1 / 2) ![1 / 2, -1 / 2, 1] ![1 - k ^ 2, 1, 1 - α2] := by
  sorry

/-- DLMF 19.25.4: the Cauchy principal value
`Π(α², k) = -(1/3)(k²/α²) R_J(0, 1 - k², 1, 1 - k²/α²)` for `-∞ < k² < 1 < α²` (real `k²`,
`α²`; written with real `k`). -/
@[dlmf 19.25.E4]
theorem compEllIntPik_pv_eq {k α2 : ℝ} (hk : k ^ 2 < 1) (hα : 1 < α2) :
    compEllIntPik α2 k = -(1 / 3) * ((k ^ 2 / α2 : ℝ) : ℂ) *
      symEllIntRJ 0 ((1 - k ^ 2 : ℝ) : ℂ) 1 ((1 - k ^ 2 / α2 : ℝ) : ℂ) := by
  sorry

/-- DLMF 19.25.5 (and its rewriting (19.25.17)–(19.25.18)): `F(φ, k) = R_F(c - 1, c - k², c)`,
`c = csc² φ`, i.e. `F(φ, k) = R_F(x, y, z)` with `(x, y, z) = (c - 1, c - k², c)`. Stated for
real `φ ∈ (0, π/2]` and complex `k` with `1 - k² sin² φ ∈ ℂ \ (-∞, 0]` (see the module
docstring for DLMF's complex `φ`). -/
@[dlmf 19.25.E5, dlmf 19.25.E17, dlmf 19.25.E18]
theorem incEllIntFk_eq_symEllIntRF {φ : ℝ} {k : ℂ} (hφ : 0 < φ) (hφ' : φ ≤ π / 2)
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    let c : ℂ := ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)
    incEllIntFk φ k = symEllIntRF (c - 1) (c - k ^ 2) c := by
  sorry

/-- DLMF 19.25.6: `∂F(φ, k)/∂k = (1/3) k R_D(c - 1, c, c - k²)`, `c = csc² φ`, for real
`φ ∈ (0, π/2]` and `1 - k² sin² φ ∈ ℂ \ (-∞, 0]`, `k ≠ 0`... (the derivative is the complex
derivative in `k`). -/
@[dlmf 19.25.E6]
theorem hasDerivAt_incEllIntFk_symEllIntRD {φ : ℝ} {k : ℂ} (hφ : 0 < φ) (hφ' : φ ≤ π / 2)
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    let c : ℂ := ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)
    HasDerivAt (fun κ : ℂ => incEllIntFk φ κ)
      ((1 / 3) * k * symEllIntRD (c - 1) c (c - k ^ 2)) k := by
  sorry

/-- DLMF 19.25.7: `E(φ, k) = 2 R_G(c - 1, c - k², c) - (c - 1) R_F(c - 1, c - k², c)
- √(c - 1) √(c - k²)/√c`, for real `φ ∈ (0, π/2]` and `1 - k² sin² φ ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.25.E7]
theorem incEllIntEk_eq_symEllIntRG {φ : ℝ} {k : ℂ} (hφ : 0 < φ) (hφ' : φ ≤ π / 2)
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    let c : ℂ := ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)
    incEllIntEk φ k = 2 * symEllIntRG (c - 1) (c - k ^ 2) c - (c - 1) * symEllIntRF (c - 1)
        (c - k ^ 2) c -
      (c - 1) ^ (1 / 2 : ℂ) * (c - k ^ 2) ^ (1 / 2 : ℂ) / c ^ (1 / 2 : ℂ) := by
  sorry

/-- DLMF 19.25.8: `E(φ, k) = R_{-1/2}(1/2, -1/2, 3/2; c - 1, c - k², c)`, for real
`φ ∈ (0, π/2)` and `1 - k² sin² φ ∈ ℂ \ (-∞, 0]` (at `φ = π/2` the node `c - 1` vanishes and
`symEllIntR` is the boundary limit). -/
@[dlmf 19.25.E8]
theorem incEllIntEk_eq_symEllIntR {φ : ℝ} {k : ℂ} (hφ : 0 < φ) (hφ' : φ < π / 2)
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    let c : ℂ := ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)
    incEllIntEk φ k = symEllIntR (1 / 2) ![1 / 2, -1 / 2, 3 / 2] ![c - 1, c - k ^ 2, c] := by
  sorry

/-- DLMF 19.25.9: `E(φ, k) = R_F(c - 1, c - k², c) - (1/3) k² R_D(c - 1, c - k², c)`, for real
`φ ∈ (0, π/2]` and `1 - k² sin² φ ∈ ℂ \ (-∞, 0]`; all terms are nonnegative when `k² ≤ 0`
(19.25.i.p2). -/
@[dlmf 19.25.E9]
theorem incEllIntEk_eq_symEllIntRF_sub_symEllIntRD {φ : ℝ} {k : ℂ} (hφ : 0 < φ) (hφ' : φ ≤ π / 2)
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    let c : ℂ := ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)
    incEllIntEk φ k = symEllIntRF (c - 1) (c - k ^ 2) c - (1 / 3) * k ^ 2 * symEllIntRD (c - 1)
        (c - k ^ 2) c := by
  sorry

/-- DLMF 19.25.10: `E(φ, k) = k'² R_F(c - 1, c - k², c) + (1/3) k² k'² R_D(c - 1, c, c - k²)
+ k² √(c - 1)/(√c √(c - k²))`, for `c > k²` (real `k`, `k² sin² φ < 1`), real `φ ∈ (0, π/2]`;
all terms are nonnegative when `0 ≤ k² ≤ 1` (19.25.i.p2). -/
@[dlmf 19.25.E10]
theorem incEllIntEk_eq_symEllIntRD_second {φ k : ℝ} (hφ : 0 < φ) (hφ' : φ ≤ π / 2)
    (hk : k ^ 2 * Real.sin φ ^ 2 < 1) :
    let c : ℂ := ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)
    incEllIntEk φ k = (1 - (k : ℂ) ^ 2) * symEllIntRF (c - 1) (c - k ^ 2) c +
      (1 / 3) * k ^ 2 * (1 - (k : ℂ) ^ 2) * symEllIntRD (c - 1) c (c - k ^ 2) +
      k ^ 2 * (c - 1) ^ (1 / 2 : ℂ) / (c ^ (1 / 2 : ℂ) * (c - k ^ 2) ^ (1 / 2 : ℂ)) := by
  sorry

/-- DLMF 19.25.11: `E(φ, k) = -(1/3) k'² R_D(c - k², c, c - 1) + √(c - k²)/(√c √(c - 1))`, for
`φ ≠ π/2` (real `φ ∈ (0, π/2)`) and `1 - k² sin² φ ∈ ℂ \ (-∞, 0]`; all terms are nonnegative
when `1 ≤ k² ≤ c` (19.25.i.p2). -/
@[dlmf 19.25.E11]
theorem incEllIntEk_eq_symEllIntRD_third {φ : ℝ} {k : ℂ} (hφ : 0 < φ) (hφ' : φ < π / 2)
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    let c : ℂ := ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)
    incEllIntEk φ k = -(1 / 3) * (1 - k ^ 2) * symEllIntRD (c - k ^ 2) c (c - 1) +
      (c - k ^ 2) ^ (1 / 2 : ℂ) / (c ^ (1 / 2 : ℂ) * (c - 1) ^ (1 / 2 : ℂ)) := by
  sorry

/-- DLMF 19.25.12: `∂E(φ, k)/∂k = -(1/3) k R_D(c - 1, c - k², c)` (complex derivative in `k`),
for real `φ ∈ (0, π/2]` and `1 - k² sin² φ ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.25.E12]
theorem hasDerivAt_incEllIntEk_symEllIntRD {φ : ℝ} {k : ℂ} (hφ : 0 < φ) (hφ' : φ ≤ π / 2)
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    let c : ℂ := ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)
    HasDerivAt (fun κ : ℂ => incEllIntEk φ κ)
      (-(1 / 3) * k * symEllIntRD (c - 1) (c - k ^ 2) c) k := by
  sorry

/-- DLMF 19.25.13: `D(φ, k) = (1/3) R_D(c - 1, c - k², c)`, for real `φ ∈ (0, π/2]` and
`1 - k² sin² φ ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.25.E13]
theorem incEllIntDk_eq_symEllIntRD {φ : ℝ} {k : ℂ} (hφ : 0 < φ) (hφ' : φ ≤ π / 2)
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    let c : ℂ := ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)
    incEllIntDk φ k = (1 / 3) * symEllIntRD (c - 1) (c - k ^ 2) c := by
  sorry

/-- DLMF 19.25.14: `Π(φ, α², k) - F(φ, k) = (1/3) α² R_J(c - 1, c - k², c, c - α²)`, for real
`φ ∈ (0, π/2]`, `1 - k² sin² φ` and `1 - α² sin² φ` in `ℂ \ (-∞, 0]` (no principal value). -/
@[dlmf 19.25.E14]
theorem incEllIntPik_sub_incEllIntFk {φ : ℝ} {k α2 : ℂ} (hφ : 0 < φ) (hφ' : φ ≤ π / 2)
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane)
    (hα : 1 - α2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    let c : ℂ := ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)
    incEllIntPik φ α2 k - incEllIntFk φ k = (1 / 3) * α2 * symEllIntRJ (c - 1) (c - k ^ 2) c
        (c - α2) := by
  sorry

/-- DLMF 19.25.15: `Π(φ, α², k) = R_{-1/2}(1/2, 1/2, -1/2, 1; c - 1, c - k², c, c - α²)`, for real
`φ ∈ (0, π/2)`, `1 - k² sin² φ` and `1 - α² sin² φ` in `ℂ \ (-∞, 0]`. -/
@[dlmf 19.25.E15]
theorem incEllIntPik_eq_symEllIntR {φ : ℝ} {k α2 : ℂ} (hφ : 0 < φ) (hφ' : φ < π / 2)
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane)
    (hα : 1 - α2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    let c : ℂ := ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)
    incEllIntPik φ α2 k =
      symEllIntR (1 / 2) ![1 / 2, 1 / 2, -1 / 2, 1] ![c - 1, c - k ^ 2, c, c - α2] := by
  sorry

/-- DLMF 19.25.16: if `α² > c` the Cauchy principal value is
`Π(φ, α², k) = -(1/3) ω² R_J(c - 1, c - k², c, c - ω²)
+ √((c - 1)(c - k²)/((α² - 1)(1 - ω²))) R_C(c (α² - 1)(1 - ω²), (α² - c)(c - ω²))`,
`ω² = k²/α²`; real `φ ∈ (0, π/2)`, real `k` with `k² < 1`. -/
@[dlmf 19.25.E16]
theorem incEllIntPik_pv_eq {φ k α2 : ℝ} (hφ : 0 < φ) (hφ' : φ < π / 2) (hk : k ^ 2 < 1)
    (hα : 1 / Real.sin φ ^ 2 < α2) :
    let c : ℝ := 1 / Real.sin φ ^ 2
    let ω2 : ℝ := k ^ 2 / α2
    incEllIntPik φ α2 k = -(1 / 3) * (ω2 : ℂ) *
        symEllIntRJ ((c - 1 : ℝ) : ℂ) ((c - k ^ 2 : ℝ) : ℂ) (c : ℂ) ((c - ω2 : ℝ) : ℂ) +
      ((√((c - 1) * (c - k ^ 2) / ((α2 - 1) * (1 - ω2))) : ℝ) : ℂ) *
        symEllIntRC ((c * (α2 - 1) * (1 - ω2) : ℝ) : ℂ) (((α2 - c) * (c - ω2) : ℝ) : ℂ) := by
  sorry

/-! ### §19.25(ii) Bulirsch's integrals as symmetric integrals -/

/-- DLMF 19.25.19: `cel(k_c, p, a, b) = a R_F(0, k_c², 1) + (1/3)(b - p a) R_J(0, k_c², 1, p)`,
for real `p ≠ 0`, `a, b` and `k_c² ∈ ℂ \ (-∞, 0]` (principal values when `p < 0`). -/
@[dlmf 19.25.E19]
theorem bulirschCel_eq_symEllInt {kc : ℂ} {p a b : ℝ} (hkc : kc ^ 2 ∈ slitPlane) (hp : p ≠ 0) :
    bulirschCel kc p a b =
      a * symEllIntRF 0 (kc ^ 2) 1 + (1 / 3) * ((b - p * a : ℝ) : ℂ) *
        symEllIntRJ 0 (kc ^ 2) 1 p := by
  sorry

/-- DLMF 19.25.20: `el1(x, k_c) = R_F(r, r + k_c², r + 1)`, `r = 1/x²`, for real `x > 0` and
`k_c² ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.25.E20]
theorem bulirschEl1_eq_symEllIntRF {x : ℝ} {kc : ℂ} (hx : 0 < x) (hkc : kc ^ 2 ∈ slitPlane) :
    let r : ℂ := ((1 / x ^ 2 : ℝ) : ℂ)
    bulirschEl1 x kc = symEllIntRF r (r + kc ^ 2) (r + 1) := by
  sorry

/-- DLMF 19.25.21: `el2(x, k_c, a, b) = a el1(x, k_c) + (1/3)(b - a) R_D(r, r + k_c², r + 1)`,
`r = 1/x²`, for real `x > 0`, `a, b` and `k_c² ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.25.E21]
theorem bulirschEl2_eq_symEllInt {x : ℝ} {kc : ℂ} {a b : ℝ} (hx : 0 < x)
    (hkc : kc ^ 2 ∈ slitPlane) :
    let r : ℂ := ((1 / x ^ 2 : ℝ) : ℂ)
    bulirschEl2 x kc a b = a * bulirschEl1 x kc + (1 / 3) * ((b - a : ℝ) : ℂ) * symEllIntRD r
        (r + kc ^ 2) (r + 1) := by
  sorry

/-- DLMF 19.25.22: `el3(x, k_c, p) = el1(x, k_c) + (1/3)(1 - p) R_J(r, r + k_c², r + 1, r + p)`,
`r = 1/x²`, for real `x > 0`, real `p ≠ 0` with `x² ≠ -1/p` (19.2.16), and
`k_c² ∈ ℂ \ (-∞, 0]` (principal values when `r + p < 0`). -/
@[dlmf 19.25.E22]
theorem bulirschEl3_eq_symEllInt {x : ℝ} {kc : ℂ} {p : ℝ} (hx : 0 < x) (hkc : kc ^ 2 ∈ slitPlane)
    (hp : p ≠ 0) (hxp : x ^ 2 ≠ -1 / p) :
    let r : ℂ := ((1 / x ^ 2 : ℝ) : ℂ)
    bulirschEl3 x kc p = bulirschEl1 x kc + (1 / 3) * ((1 - p : ℝ) : ℂ) * symEllIntRJ r (r + kc ^ 2)
        (r + 1) (r + p) := by
  sorry

/-! ### §19.25(iii) Symmetric integrals as Legendre's integrals -/

/-- DLMF 19.25.24 with 19.25.23: for `0 ≤ x ≤ y ≤ z`, `x < z`, `(x, y) ≠ (0, 0)`, with
`φ = arccos √(x/z)` and `k = √((z - y)/(z - x))`, `(z - x)^{1/2} R_F(x, y, z) = F(φ, k)`. -/
@[dlmf 19.25.E23, dlmf 19.25.E24]
theorem sqrt_mul_symEllIntRF_eq_incEllIntFk {x y z : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z)
    (hxz : x < z) (h0 : (x, y) ≠ (0, 0)) :
    let φ := Real.arccos √(x / z)
    let k := √((z - y) / (z - x))
    ((√(z - x) : ℝ) : ℂ) * symEllIntRF x y z = incEllIntFk φ k := by
  sorry

/-- DLMF 19.25.25 with 19.25.23: `(z - x)^{3/2} R_D(x, y, z) = (3/k²)(F(φ, k) - E(φ, k))`, under
the assumptions of (19.25.24) and `y < z` (so that `k ≠ 0`; DLMF divides by `k²`). -/
@[dlmf 19.25.E23, dlmf 19.25.E25]
theorem symEllIntRD_eq_incEllInt {x y z : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hyz : y < z)
    (h0 : (x, y) ≠ (0, 0)) :
    let φ := Real.arccos √(x / z)
    let k := √((z - y) / (z - x))
    (((z - x) ^ (3 / 2 : ℝ) : ℝ) : ℂ) * symEllIntRD x y z =
      3 / (k : ℂ) ^ 2 * (incEllIntFk φ k - incEllIntEk φ k) := by
  sorry

/-- DLMF 19.25.26 with 19.25.23: `(z - x)^{3/2} R_J(x, y, z, p) = (3/α²)(Π(φ, α², k) - F(φ, k))`,
`α² = (z - p)/(z - x) ≠ 0`, under the assumptions of (19.25.24) and `p > 0` (a Cauchy principal
value when `α² sin² φ > 1`, i.e. `p < x`). -/
@[dlmf 19.25.E23, dlmf 19.25.E26]
theorem symEllIntRJ_eq_incEllInt {x y z p : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z)
    (hxz : x < z) (h0 : (x, y) ≠ (0, 0)) (hp : 0 < p) (hpz : p ≠ z) :
    let φ := Real.arccos √(x / z)
    let k := √((z - y) / (z - x))
    let α2 := (z - p) / (z - x)
    (((z - x) ^ (3 / 2 : ℝ) : ℝ) : ℂ) * symEllIntRJ x y z p =
      3 / (α2 : ℂ) * (incEllIntPik φ α2 k - incEllIntFk φ k) := by
  sorry

/-- DLMF 19.25.27 with 19.25.23: `2(z - x)^{-1/2} R_G(x, y, z) = E(φ, k) + cot² φ F(φ, k)
+ cot φ √(1 - k² sin² φ)`, under the assumptions of (19.25.24). -/
@[dlmf 19.25.E23, dlmf 19.25.E27]
theorem symEllIntRG_eq_incEllInt {x y z : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z)
    (hxz : x < z) (h0 : (x, y) ≠ (0, 0)) :
    let φ := Real.arccos √(x / z)
    let k := √((z - y) / (z - x))
    2 * (((z - x) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) * symEllIntRG x y z =
      incEllIntEk φ k + ((Real.cot φ ^ 2 : ℝ) : ℂ) * incEllIntFk φ k +
        ((Real.cot φ * √(1 - k ^ 2 * Real.sin φ ^ 2) : ℝ) : ℂ) := by
  sorry

/-! ### §19.25(v) Jacobian elliptic functions -/

/-- The real Glaisher numerator `p(u, k)` for `p ∈ {s, c, d, n}`: `sn, cn, dn, 1` (parameter
`m = k²`), so that `pq = p/q` (DLMF 22.2.10). -/
def ei19d_jacobiLetterm : JacobiLetter → ℝ → ℝ → ℝ
  | .s, u, m => DLMF.Elliptic.Real.jacobiSnm u m
  | .c, u, m => DLMF.Elliptic.Real.jacobiCnm u m
  | .d, u, m => DLMF.Elliptic.Real.jacobiDnm u m
  | .n, _, _ => 1

/-- DLMF 19.25.28: `Δ(p, q) = ps²(u, k) - qs²(u, k)` for `p, q ∈ {c, d, n}` (real `u`,
parameter `m = k²`), with `Δ(p, q) = -Δ(q, p)`. -/
@[dlmf 19.25.E28]
def jacobiDeltam (p q : JacobiLetter) (u m : ℝ) : ℝ :=
  (ei19d_jacobiLetterm p u m / DLMF.Elliptic.Real.jacobiSnm u m) ^ 2 -
    (ei19d_jacobiLetterm q u m / DLMF.Elliptic.Real.jacobiSnm u m) ^ 2

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
    (hs : DLMF.Elliptic.Real.jacobiSnm u m ≠ 0) :
    jacobiDeltam .n .d u m = m ∧ jacobiDeltam .d .c u m = 1 - m ∧ jacobiDeltam .n .c u m = 1 := by
  have hsc : DLMF.Elliptic.Real.jacobiSnm u m ^ 2 + DLMF.Elliptic.Real.jacobiCnm u m ^ 2 = 1 := by
    simp only [DLMF.Elliptic.Real.jacobiSnm, DLMF.Elliptic.Real.jacobiCnm, Real.sin_sq_add_cos_sq]
  have hd : DLMF.Elliptic.Real.jacobiDnm u m ^ 2 = 1 - m *
      DLMF.Elliptic.Real.jacobiSnm u m ^ 2 := by
    have h1 : 0 ≤ 1 - m * DLMF.Elliptic.Real.jacobiSnm u m ^ 2 := by
      have : DLMF.Elliptic.Real.jacobiSnm u m ^ 2 ≤ 1 := by
        nlinarith [sq_nonneg (DLMF.Elliptic.Real.jacobiCnm u m)]
      nlinarith
    rw [DLMF.Elliptic.Real.jacobiDnm, ← Real.sqrt_eq_rpow, Real.sq_sqrt h1]
  have hs2 : DLMF.Elliptic.Real.jacobiSnm u m ^ 2 ≠ 0 := pow_ne_zero 2 hs
  refine ⟨?_, ?_, ?_⟩
  · simp only [jacobiDeltam, ei19d_jacobiLetterm, div_pow]
    field_simp
    linear_combination (-1 : ℝ) * hd
  · simp only [jacobiDeltam, ei19d_jacobiLetterm, div_pow]
    field_simp
    linear_combination hd - hsc
  · simp only [jacobiDeltam, ei19d_jacobiLetterm, div_pow]
    field_simp
    linear_combination (-1 : ℝ) * hsc

/-- DLMF 19.25.30, **corrected domain**: `am(u, k) = R_C(cs²(u, k), ns²(u, k))` for
`0 ≤ k² < 1` and `0 < u ≤ K(k)`. DLMF's condition `cs²(u, k) ≥ 0` does not suffice: it holds for
every real `u`, but for `K < u < 2K` the right side equals `π - am(u, k)`. -/
@[dlmf 19.25.E30]
theorem jacobiAmm_eq_symEllIntRC {u m : ℝ} (hm0 : 0 ≤ m) (hm : m < 1) (hu : 0 < u)
    (huK : u ≤ DLMF.Elliptic.Real.compEllIntKm m) :
    (DLMF.Elliptic.Real.jacobiAmm u m : ℂ) =
      symEllIntRC
        (((DLMF.Elliptic.Real.jacobiCnm u m / DLMF.Elliptic.Real.jacobiSnm u m) ^ 2 : ℝ) : ℂ)
        (((1 / DLMF.Elliptic.Real.jacobiSnm u m) ^ 2 : ℝ) : ℂ) := by
  sorry

/-- DLMF 19.25.31, **corrected domain**: `u = R_F(ps²(u, k), qs²(u, k), rs²(u, k))` for
`p, q, r` any permutation of `c, d, n` (by the symmetry of `R_F` it suffices to take `c, d, n`),
`0 ≤ k² < 1` and `0 < u ≤ K(k)` (DLMF: `cs² ≥ 0`; the formula fails for `K < u < 2K`). -/
@[dlmf 19.25.E31]
theorem eq_symEllIntRF_jacobi {u m : ℝ} (hm0 : 0 ≤ m) (hm : m < 1) (hu : 0 < u)
    (huK : u ≤ DLMF.Elliptic.Real.compEllIntKm m) :
    (u : ℂ) = symEllIntRF
      (((DLMF.Elliptic.Real.jacobiCnm u m / DLMF.Elliptic.Real.jacobiSnm u m) ^ 2 : ℝ) : ℂ)
      (((DLMF.Elliptic.Real.jacobiDnm u m / DLMF.Elliptic.Real.jacobiSnm u m) ^ 2 : ℝ) : ℂ)
      (((1 / DLMF.Elliptic.Real.jacobiSnm u m) ^ 2 : ℝ) : ℂ) := by
  sorry

/-- DLMF 19.25.32 for `ps = cs, ds, ns` (with `Δ(d, c) = k'²`, `Δ(n, c) = 1`, `Δ(n, d) = k²`,
19.25.29): `arcps(x, k) = R_F(x², x² + Δ(q, p), x² + Δ(r, p))`, i.e.
`arccs x = R_F(x², x² + k'², x² + 1)` for `x ≥ 0` (**corrected**: DLMF says `x` real; the left
side is not even in `x`), `arcds x = R_F(x², x² - k'², x² + k²)` for `x ≥ k'`, and
`arcns x = R_F(x², x² - 1, x² - k²)` for `x ≥ 1`; real parameter `0 ≤ m = k² < 1`. -/
@[dlmf 19.25.E32]
theorem jacobiArcps_eq_symEllIntRF {m x : ℝ} (hm0 : 0 ≤ m) (hm : m < 1) :
    (0 ≤ x → (Real.jacobiArccsm x m : ℂ) =
        symEllIntRF ((x ^ 2 : ℝ) : ℂ) ((x ^ 2 + (1 - m) : ℝ) : ℂ) ((x ^ 2 + 1 : ℝ) : ℂ)) ∧
      (√(1 - m) ≤ x → (Real.jacobiArcdsm x m : ℂ) =
        symEllIntRF ((x ^ 2 : ℝ) : ℂ) ((x ^ 2 - (1 - m) : ℝ) : ℂ) ((x ^ 2 + m : ℝ) : ℂ)) ∧
      (1 ≤ x → (Real.jacobiArcnsm x m : ℂ) =
        symEllIntRF ((x ^ 2 : ℝ) : ℂ) ((x ^ 2 - 1 : ℝ) : ℂ) ((x ^ 2 - m : ℝ) : ℂ)) := by
  sorry

/-- DLMF 19.25.33 for `sp = sc, sd, sn`: `arcsp(x, k) = x R_F(1, 1 + Δ(q, p) x², 1 + Δ(r, p) x²)`,
i.e. `arcsc x = x R_F(1, 1 + k'² x², 1 + x²)` for real `x`,
`arcsd x = x R_F(1, 1 - k'² x², 1 + k² x²)` for `0 ≤ x² ≤ 1/k'²`, and
`arcsn x = x R_F(1, 1 - x², 1 - k² x²)` for `0 ≤ x² ≤ 1`; real `0 ≤ m = k² < 1`. -/
@[dlmf 19.25.E33]
theorem jacobiArcsp_eq_symEllIntRF {m x : ℝ} (hm0 : 0 ≤ m) (hm : m < 1) :
    ((Real.jacobiArcscm x m : ℂ) =
        x * symEllIntRF 1 ((1 + (1 - m) * x ^ 2 : ℝ) : ℂ) ((1 + x ^ 2 : ℝ) : ℂ)) ∧
      ((1 - m) * x ^ 2 ≤ 1 → (Real.jacobiArcsdm x m : ℂ) =
        x * symEllIntRF 1 ((1 - (1 - m) * x ^ 2 : ℝ) : ℂ) ((1 + m * x ^ 2 : ℝ) : ℂ)) ∧
      (x ^ 2 ≤ 1 → (DLMF.Elliptic.Real.jacobiArcsnm x m : ℂ) =
        x * symEllIntRF 1 ((1 - x ^ 2 : ℝ) : ℂ) ((1 - m * x ^ 2 : ℝ) : ℂ)) := by
  sorry

/-- DLMF 19.25.34 for the six `pq` with `p, q ∈ {c, d, n}`:
`arcpq(x, k) = √w R_F(x², 1, 1 + Δ(r, q) w)`, `w = (1 - x²)/Δ(q, p)`, with `0 < m = k² < 1`:
`arccd` and `arccn` for `0 ≤ x ≤ 1` (**corrected**: DLMF allows `0 ≤ x² ≤ 1`, but the left sides
are not even in `x`), `arcdc` and `arcnc` for `x ≥ 1`, `arcdn` for `k' ≤ x ≤ 1`, `arcnd` for
`1 ≤ x ≤ 1/k'`. -/
@[dlmf 19.25.E34]
theorem jacobiArcpq_eq_symEllIntRF {m x : ℝ} (hm0 : 0 < m) (hm : m < 1) :
    -- `cd`: `p = c, q = d, r = n`, `w = (1 - x²)/k'²`, `Δ(n, d) = k²`
    (0 ≤ x → x ≤ 1 → (Real.jacobiArccdm x m : ℂ) =
        ((√((1 - x ^ 2) / (1 - m)) : ℝ) : ℂ) *
          symEllIntRF ((x ^ 2 : ℝ) : ℂ) 1 ((1 + m * ((1 - x ^ 2) / (1 - m)) : ℝ) : ℂ)) ∧
    -- `cn`: `p = c, q = n, r = d`, `w = 1 - x²`, `Δ(d, n) = -k²`
    (0 ≤ x → x ≤ 1 → (Real.jacobiArccnm x m : ℂ) =
        ((√(1 - x ^ 2) : ℝ) : ℂ) * symEllIntRF ((x ^ 2 : ℝ) : ℂ) 1 ((1 - m * (1 - x ^ 2) : ℝ) : ℂ))
          ∧
    -- `dc`: `p = d, q = c, r = n`, `w = (x² - 1)/k'²`, `Δ(n, c) = 1`
    (1 ≤ x → (Real.jacobiArcdcm x m : ℂ) =
        ((√((x ^ 2 - 1) / (1 - m)) : ℝ) : ℂ) *
          symEllIntRF ((x ^ 2 : ℝ) : ℂ) 1 ((1 + (x ^ 2 - 1) / (1 - m) : ℝ) : ℂ)) ∧
    -- `nc`: `p = n, q = c, r = d`, `w = x² - 1`, `Δ(d, c) = k'²`
    (1 ≤ x → (Real.jacobiArcncm x m : ℂ) =
        ((√(x ^ 2 - 1) : ℝ) : ℂ) * symEllIntRF ((x ^ 2 : ℝ) : ℂ) 1
          ((1 + (1 - m) * (x ^ 2 - 1) : ℝ) : ℂ)) ∧
    -- `dn`: `p = d, q = n, r = c`, `w = (1 - x²)/k²`, `Δ(c, n) = -1`
    (√(1 - m) ≤ x → x ≤ 1 → (Real.jacobiArcdnm x m : ℂ) =
        ((√((1 - x ^ 2) / m) : ℝ) : ℂ) * symEllIntRF ((x ^ 2 : ℝ) : ℂ) 1
          ((1 - (1 - x ^ 2) / m : ℝ) : ℂ)) ∧
    -- `nd`: `p = n, q = d, r = c`, `w = (x² - 1)/k²`, `Δ(c, d) = -k'²`
    (1 ≤ x → x * √(1 - m) ≤ 1 → (Real.jacobiArcndm x m : ℂ) =
        ((√((x ^ 2 - 1) / m) : ℝ) : ℂ) *
          symEllIntRF ((x ^ 2 : ℝ) : ℂ) 1 ((1 - (1 - m) * ((x ^ 2 - 1) / m) : ℝ) : ℂ)) := by
  sorry

/-! ### §19.25(vi) Weierstrass elliptic functions -/

/-- DLMF 19.25.35 with 19.25.36: if `z ∉ 𝕃` and `℘(z) - e_j ∈ ℂ \ (-∞, 0]` for `j = 1, 2, 3`,
then `z + 2ω = ± R_F(℘(z) - e₁, ℘(z) - e₂, ℘(z) - e₃)` for some `2ω ∈ 𝕃` and some sign (the sign
changes across the curves where some `℘(z) - e_j < 0`). -/
@[dlmf 19.25.E35, dlmf 19.25.E36]
theorem weierstrassP_symEllIntRF (H : DLMF.Weierstrass.HalfPeriods) {z : ℂ} (hz : z ∉ H.lattice)
    (hP : ∀ j ∈ ({1, 2, 3} : Finset ℕ), H.weierstrassP z - H.e j ∈ slitPlane) :
    ∃ w ∈ H.lattice, ∃ s : ℂ, (s = 1 ∨ s = -1) ∧
      z + w = s * symEllIntRF (H.weierstrassP z - H.e 1) (H.weierstrassP z - H.e 2)
        (H.weierstrassP z - H.e 3) := by
  sorry

/-- DLMF 19.25.37 (with 19.25.35, the same sign and `ω`): under the hypotheses of (19.25.35),
`ζ(z + 2ω) + (z + 2ω) ℘(z) = ± 2 R_G(℘(z) - e₁, ℘(z) - e₂, ℘(z) - e₃)`. -/
@[dlmf 19.25.E35, dlmf 19.25.E37]
theorem weierstrassZeta_symEllIntRG (H : DLMF.Weierstrass.HalfPeriods) {z : ℂ}
    (hz : z ∉ H.lattice)
    (hP : ∀ j ∈ ({1, 2, 3} : Finset ℕ), H.weierstrassP z - H.e j ∈ slitPlane) :
    ∃ w ∈ H.lattice, ∃ s : ℂ, (s = 1 ∨ s = -1) ∧
      z + w = s * symEllIntRF (H.weierstrassP z - H.e 1) (H.weierstrassP z - H.e 2)
        (H.weierstrassP z - H.e 3) ∧
      H.weierstrassZeta (z + w) + (z + w) * H.weierstrassP z =
        s * (2 * symEllIntRG (H.weierstrassP z - H.e 1) (H.weierstrassP z - H.e 2)
          (H.weierstrassP z - H.e 3)) := by
  sorry

/-- DLMF 19.25.38–19.25.39: for `j, k, ℓ` any permutation of `1, 2, 3` there is `ω_j` with
`2ω_j ∈ 𝕃` and `℘(ω_j) = e_j` such that `ω_j = R_F(0, e_j - e_k, e_j - e_ℓ)` and
`ζ(ω_j) + ω_j e_j = 2 R_G(0, e_j - e_k, e_j - e_ℓ)`; we assume `e_j - e_k, e_j - e_ℓ` lie in
`ℂ \ (-∞, 0]`. -/
@[dlmf 19.25.E38, dlmf 19.25.E39]
theorem halfPeriod_eq_symEllIntRF (H : DLMF.Weierstrass.HalfPeriods) (σ : Equiv.Perm (Fin 3))
    (hk : H.e (σ 0 + 1) - H.e (σ 1 + 1) ∈ slitPlane)
    (hl : H.e (σ 0 + 1) - H.e (σ 2 + 1) ∈ slitPlane) :
    ∃ ω : ℂ, 2 * ω ∈ H.lattice ∧ H.weierstrassP ω = H.e (σ 0 + 1) ∧
      ω = symEllIntRF 0 (H.e (σ 0 + 1) - H.e (σ 1 + 1)) (H.e (σ 0 + 1) - H.e (σ 2 + 1)) ∧
      H.weierstrassZeta ω + ω * H.e (σ 0 + 1) =
        2 * symEllIntRG 0 (H.e (σ 0 + 1) - H.e (σ 1 + 1)) (H.e (σ 0 + 1) - H.e (σ 2 + 1)) := by
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
theorem eq_weierstrassSigma_mul_symEllIntRF (H : DLMF.Weierstrass.HalfPeriods) {z : ℂ}
    (hz : z ∉ H.lattice)
    (hσ : ∀ j ∈ ({1, 2, 3} : Finset ℕ), weierstrassSigmaIdx H j z ^ 2 ∈ slitPlane) :
    ∃ w ∈ H.lattice, ∃ s : ℂ, (s = 1 ∨ s = -1) ∧
      z + w = s * H.weierstrassSigma z * symEllIntRF (weierstrassSigmaIdx H 1 z ^ 2)
        (weierstrassSigmaIdx H 2 z ^ 2) (weierstrassSigmaIdx H 3 z ^ 2) := by
  sorry

/-! ### §19.25(vii) Hypergeometric function -/

/-- DLMF 19.25.42: `₂F₁(a, b; c; z) = R_{-a}(b, c - b; 1 - z, 1)`, for `|z| < 1` (the Gauss
series) and `c ∉ {0, -1, -2, …}`; all complex `a, b` (Carlson's continuation of `R`). -/
@[dlmf 19.25.E42]
theorem ordinaryHypergeometric_eq_symEllIntR (a b c : ℂ) (hc : ∀ n : ℕ, c ≠ -n) {z : ℂ}
    (hz : ‖z‖ < 1) :
    ordinaryHypergeometric a b c z = symEllIntR a ![b, c - b] ![1 - z, 1] := by
  sorry

/-- DLMF 19.25.43: `R_{-a}(b₁, b₂; z₁, z₂) = z₂^{-a} ₂F₁(a, b₁; b₁ + b₂; 1 - z₁/z₂)`, for
`z₁, z₂ ∈ ℂ \ (-∞, 0]` with `|1 - z₁/z₂| < 1` and `arg z₁ - arg z₂ ∈ (-π, π)` (so that
`z₂^{-a}` and the homogeneity of `R` match the principal branches), `b₁ + b₂ ∉ {0, -1, …}`. -/
@[dlmf 19.25.E43]
theorem symEllIntR_two_eq_ordinaryHypergeometric (a b₁ b₂ : ℂ) (hb : ∀ n : ℕ, b₁ + b₂ ≠ -n)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ slitPlane) (hz₂ : z₂ ∈ slitPlane) (hz : ‖1 - z₁ / z₂‖ < 1)
    (harg : arg z₁ - arg z₂ ∈ Ioo (-π) π) :
    symEllIntR a ![b₁, b₂] ![z₁, z₂] = z₂ ^ (-a) * ordinaryHypergeometric a b₁ (b₁ + b₂)
        (1 - z₁ / z₂) := by
  sorry

end DLMF.EllipticIntegrals
