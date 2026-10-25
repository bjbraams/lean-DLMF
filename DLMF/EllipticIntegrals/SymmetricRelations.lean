/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Symmetric
public import DLMF.EllipticIntegrals.Legendre
public import DLMF.EllipticIntegrals.SymmetricAddition
public import DLMF.EllipticIntegrals.P19sR1Legendre
public import DLMF.EllipticIntegrals.P19sR1Connection
public import DLMF.EllipticIntegrals.LegendreIdentities
public import Carlson.TwoVariable.GaussHypergeometric
public import Carlson.TwoVariable.ParameterSymmetry
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
  have _ := hk
  rw [compEllIntKk_eq_incEllIntFk, show ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) by push_cast; ring,
    incEllIntFk_ofReal_eq_integral, ← p19sR1_symEllIntRF_legendre (by positivity) le_rfl k,
    p19sR1_csc_sq_pi_div_two, sub_self]

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
  have e : ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) := by push_cast; ring
  have hk' : 1 - k ^ 2 * (Real.sin (π / 2) : ℂ) ^ 2 ∈ slitPlane := by
    simpa [Real.sin_pi_div_two] using hk
  have hp : (0 : ℝ) < π / 2 := by positivity
  have hE := p19sR1_incEllIntEk_eq hp le_rfl hk'
  have hD := p19sR1_incEllIntDk_eq hp le_rfl k
  have hsub := p19sR1_incEllIntEk_eq_sub hp.le le_rfl hk'
  rw [p19sR1_csc_sq_pi_div_two, sub_self] at hE hD
  have hK : compEllIntKk k = symEllIntRF 0 (1 - k ^ 2) 1 := compEllIntKk_eq_symEllIntRF hk
  have hKF : compEllIntKk k = incEllIntFk ((π / 2 : ℝ) : ℂ) k := by
    rw [compEllIntKk_eq_incEllIntFk, e]
  have hEE : compEllIntEk k = incEllIntEk ((π / 2 : ℝ) : ℂ) k := by rw [compEllIntEk, e]
  have hDD : compEllIntDk k = incEllIntDk ((π / 2 : ℝ) : ℂ) k := by rw [compEllIntDk, e]
  have hG := p19sR1_two_mul_symEllIntRG (x := 0) (Or.inr rfl) hk one_mem_slitPlane
  rw [zero_cpow (by norm_num)] at hG
  have hcyc := p19sR1_symEllIntRD_cyclic_mul_sum (x := 0) (Or.inr rfl) hk one_mem_slitPlane
  rw [symEllIntRD_comm 0 1] at hcyc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hEE, hE]; linear_combination -hG
  · rw [hEE, hE]; linear_combination -(1 / 3 : ℂ) * hcyc
  · rw [hKF, hEE, hDD, hsub]; ring
  · rw [hDD, hD]; ring
  · rw [hEE, hE, hK]; linear_combination -(k ^ 2 / 3) * hcyc

/-- DLMF 19.25.2: `Π(α², k) - K(k) = (1/3) α² R_J(0, k'², 1, 1 - α²)`, for `k'² = 1 - k²` and
`1 - α²` in `ℂ \ (-∞, 0]` (no principal value). -/
@[dlmf 19.25.E2]
theorem compEllIntPik_sub_compEllIntKk {k α2 : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane)
    (hα : 1 - α2 ∈ slitPlane) :
    compEllIntPik α2 k - compEllIntKk k = (1 / 3) * α2 * symEllIntRJ 0 (1 - k ^ 2) 1 (1 - α2) := by
  have e : ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) := by push_cast; ring
  have hp : (0 : ℝ) < π / 2 := by positivity
  have hk' : 1 - k ^ 2 * (Real.sin (π / 2) : ℂ) ^ 2 ∈ slitPlane := by
    simpa [Real.sin_pi_div_two] using hk
  have hα' : 1 - α2 * (Real.sin (π / 2) : ℂ) ^ 2 ∈ slitPlane := by
    simpa [Real.sin_pi_div_two] using hα
  have h := p19sR1_incEllIntPik_sub hp.le le_rfl hk' hα'
  have hJ := p19sR1_symEllIntRJ_legendre hp le_rfl k α2
    (ei19c_not_isNegReal_of_mem_slitPlane (p19sR1_csc_sq_sub_mem hp le_rfl hα'))
  rw [p19sR1_csc_sq_pi_div_two, sub_self] at hJ
  rw [compEllIntPik, compEllIntKk_eq_incEllIntFk, e, h, hJ]
  ring

/-- DLMF 19.25.3: `Π(α², k) = (π/2) R_{-1/2}(1/2, -1/2, 1; k'², 1, 1 - α²)`, for `k'² = 1 - k²`
and `1 - α²` in `ℂ \ (-∞, 0]`. -/
@[dlmf 19.25.E3]
theorem compEllIntPik_eq_symEllIntR {k α2 : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane)
    (hα : 1 - α2 ∈ slitPlane) :
    compEllIntPik α2 k =
      (π / 2) * symEllIntR (1 / 2) ![1 / 2, -1 / 2, 1] ![1 - k ^ 2, 1, 1 - α2] := by
  exact p19sR1_compEllIntPik_eq_symEllIntR hk hα

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
  have _ := hk
  intro c
  exact (incEllIntFk_ofReal_eq_integral φ k).trans (p19sR1_symEllIntRF_legendre hφ hφ' k).symm

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
  intro c
  have hc : c = ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) := rfl
  have hE := p19sR1_incEllIntEk_eq hφ hφ' hk
  have hG := p19sR1_two_mul_symEllIntRG (p19sR1_csc_sq_sub_one_arg hφ hφ')
    (p19sR1_csc_sq_sub_mem hφ hφ' hk) (p19sR1_csc_sq_mem hφ hφ')
  rw [← ei19c_inv_cpow_half] at hG
  rw [hc]
  linear_combination hE - hG

/-- DLMF 19.25.8: `E(φ, k) = R_{-1/2}(1/2, -1/2, 3/2; c - 1, c - k², c)`, for real
`φ ∈ (0, π/2)` and `1 - k² sin² φ ∈ ℂ \ (-∞, 0]` (at `φ = π/2` the node `c - 1` vanishes and
`symEllIntR` is the boundary limit). -/
@[dlmf 19.25.E8]
theorem incEllIntEk_eq_symEllIntR {φ : ℝ} {k : ℂ} (hφ : 0 < φ) (hφ' : φ < π / 2)
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    let c : ℂ := ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)
    incEllIntEk φ k = symEllIntR (1 / 2) ![1 / 2, -1 / 2, 3 / 2] ![c - 1, c - k ^ 2, c] := by
  exact p19sR1_incEllIntEk_eq_symEllIntR hφ hφ' hk

/-- DLMF 19.25.9: `E(φ, k) = R_F(c - 1, c - k², c) - (1/3) k² R_D(c - 1, c - k², c)`, for real
`φ ∈ (0, π/2]` and `1 - k² sin² φ ∈ ℂ \ (-∞, 0]`; all terms are nonnegative when `k² ≤ 0`
(19.25.i.p2). -/
@[dlmf 19.25.E9]
theorem incEllIntEk_eq_symEllIntRF_sub_symEllIntRD {φ : ℝ} {k : ℂ} (hφ : 0 < φ) (hφ' : φ ≤ π / 2)
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    let c : ℂ := ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)
    incEllIntEk φ k = symEllIntRF (c - 1) (c - k ^ 2) c - (1 / 3) * k ^ 2 * symEllIntRD (c - 1)
        (c - k ^ 2) c := by
  intro c
  have hc : c = ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) := rfl
  rw [hc]
  exact p19sR1_incEllIntEk_eq hφ hφ' hk

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
  intro c
  have hc : c = ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) := rfl
  have hk' : 1 - (k : ℂ) ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane := by
    rw [show 1 - (k : ℂ) ^ 2 * (Real.sin φ : ℂ) ^ 2 = ((1 - k ^ 2 * Real.sin φ ^ 2 : ℝ) : ℂ) by
      push_cast; ring]
    exact ofReal_mem_slitPlane.mpr (by linarith)
  rw [hc]
  rcases eq_or_lt_of_le hφ' with h | h
  · subst h
    have hE := p19sR1_incEllIntEk_eq hφ le_rfl hk'
    have hy := p19sR1_csc_sq_sub_mem hφ le_rfl hk'
    rw [p19sR1_csc_sq_pi_div_two] at hE hy ⊢
    rw [sub_self] at hE ⊢
    have hcyc := p19sR1_symEllIntRD_cyclic_mul_sum (x := 0) (Or.inr rfl) hy one_mem_slitPlane
    rw [symEllIntRD_comm 0 1] at hcyc
    rw [hE, zero_cpow (by norm_num)]
    linear_combination -((k : ℂ) ^ 2 / 3) * hcyc
  · have hE := p19sR1_incEllIntEk_eq hφ hφ' hk'
    have hM := p19sR1_symEllIntRD_move (p19sR1_csc_sq_sub_mem hφ hφ' hk')
      (p19sR1_csc_sq_sub_one_mem hφ h) (p19sR1_csc_sq_mem hφ hφ')
    rw [symEllIntRD_comm (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - 1), symEllIntRF_comm_left,
      ← ei19c_inv_cpow_half,
      ← ei19c_inv_cpow_half] at hM
    linear_combination hE - ((k : ℂ) ^ 2 / 3) * hM

/-- DLMF 19.25.11: `E(φ, k) = -(1/3) k'² R_D(c - k², c, c - 1) + √(c - k²)/(√c √(c - 1))`, for
`φ ≠ π/2` (real `φ ∈ (0, π/2)`) and `1 - k² sin² φ ∈ ℂ \ (-∞, 0]`; all terms are nonnegative
when `1 ≤ k² ≤ c` (19.25.i.p2). -/
@[dlmf 19.25.E11]
theorem incEllIntEk_eq_symEllIntRD_third {φ : ℝ} {k : ℂ} (hφ : 0 < φ) (hφ' : φ < π / 2)
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    let c : ℂ := ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)
    incEllIntEk φ k = -(1 / 3) * (1 - k ^ 2) * symEllIntRD (c - k ^ 2) c (c - 1) +
      (c - k ^ 2) ^ (1 / 2 : ℂ) / (c ^ (1 / 2 : ℂ) * (c - 1) ^ (1 / 2 : ℂ)) := by
  intro c
  have hc : c = ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) := rfl
  have hE := p19sR1_incEllIntEk_eq hφ hφ'.le hk
  have hM := p19sR1_symEllIntRD_move (p19sR1_csc_sq_sub_one_mem hφ hφ')
    (p19sR1_csc_sq_sub_mem hφ hφ'.le hk) (p19sR1_csc_sq_mem hφ hφ'.le)
  rw [← ei19c_inv_cpow_half, ← ei19c_inv_cpow_half] at hM
  rw [hc]
  linear_combination hE - (1 / 3 : ℂ) * hM

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
  have _ := hk
  intro c
  have hc : c = ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) := rfl
  rw [hc]
  exact p19sR1_incEllIntDk_eq hφ hφ' k

/-- DLMF 19.25.14: `Π(φ, α², k) - F(φ, k) = (1/3) α² R_J(c - 1, c - k², c, c - α²)`, for real
`φ ∈ (0, π/2]`, `1 - k² sin² φ` and `1 - α² sin² φ` in `ℂ \ (-∞, 0]` (no principal value). -/
@[dlmf 19.25.E14]
theorem incEllIntPik_sub_incEllIntFk {φ : ℝ} {k α2 : ℂ} (hφ : 0 < φ) (hφ' : φ ≤ π / 2)
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane)
    (hα : 1 - α2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    let c : ℂ := ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)
    incEllIntPik φ α2 k - incEllIntFk φ k = (1 / 3) * α2 * symEllIntRJ (c - 1) (c - k ^ 2) c
        (c - α2) := by
  intro c
  have hc : c = ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) := rfl
  rw [hc, p19sR1_incEllIntPik_sub hφ.le hφ' hk hα, p19sR1_symEllIntRJ_legendre hφ hφ' k α2
    (ei19c_not_isNegReal_of_mem_slitPlane (p19sR1_csc_sq_sub_mem hφ hφ' hα))]
  ring

/-- DLMF 19.25.15: `Π(φ, α², k) = R_{-1/2}(1/2, 1/2, -1/2, 1; c - 1, c - k², c, c - α²)`, for real
`φ ∈ (0, π/2)`, `1 - k² sin² φ` and `1 - α² sin² φ` in `ℂ \ (-∞, 0]`. -/
@[dlmf 19.25.E15]
theorem incEllIntPik_eq_symEllIntR {φ : ℝ} {k α2 : ℂ} (hφ : 0 < φ) (hφ' : φ < π / 2)
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane)
    (hα : 1 - α2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    let c : ℂ := ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)
    incEllIntPik φ α2 k =
      symEllIntR (1 / 2) ![1 / 2, 1 / 2, -1 / 2, 1] ![c - 1, c - k ^ 2, c, c - α2] := by
  exact p19sR1_incEllIntPik_eq_symEllIntR hφ hφ' hk hα

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
  have _ := hkc
  exact p19sR1_bulirschEl1_eq hx kc

/-- DLMF 19.25.21: `el2(x, k_c, a, b) = a el1(x, k_c) + (1/3)(b - a) R_D(r, r + k_c², r + 1)`,
`r = 1/x²`, for real `x > 0`, `a, b` and `k_c² ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.25.E21]
theorem bulirschEl2_eq_symEllInt {x : ℝ} {kc : ℂ} {a b : ℝ} (hx : 0 < x)
    (hkc : kc ^ 2 ∈ slitPlane) :
    let r : ℂ := ((1 / x ^ 2 : ℝ) : ℂ)
    bulirschEl2 x kc a b = a * bulirschEl1 x kc + (1 / 3) * ((b - a : ℝ) : ℂ) * symEllIntRD r
        (r + kc ^ 2) (r + 1) := by
  exact p19sR1_bulirschEl2_eq hx hkc a b

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
  have _ := hxy
  have _ := h0
  intro φ k
  obtain ⟨hφ0, hφ1, ex, ey, ez, -, -, -⟩ := p19sR1_iii_setup hx hyz hxz
  have hl : 0 < z - x := by linarith
  rw [ex, ey, ez, p19sR1_symEllIntRF_scale hl, p19sR1_sqrt_cast_eq_cpow hl.le,
    mul_inv_cancel_left₀ (p19sR1_half_pow_ne hl), p19sR1_symEllIntRF_legendre hφ0 hφ1,
    ← incEllIntFk_ofReal_eq_integral]

/-- DLMF 19.25.25 with 19.25.23: `(z - x)^{3/2} R_D(x, y, z) = (3/k²)(F(φ, k) - E(φ, k))`, under
the assumptions of (19.25.24) and `y < z` (so that `k ≠ 0`; DLMF divides by `k²`). -/
@[dlmf 19.25.E23, dlmf 19.25.E25]
theorem symEllIntRD_eq_incEllInt {x y z : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hyz : y < z)
    (h0 : (x, y) ≠ (0, 0)) :
    let φ := Real.arccos √(x / z)
    let k := √((z - y) / (z - x))
    (((z - x) ^ (3 / 2 : ℝ) : ℝ) : ℂ) * symEllIntRD x y z =
      3 / (k : ℂ) ^ 2 * (incEllIntFk φ k - incEllIntEk φ k) := by
  intro φ k
  have hxz : x < z := lt_of_le_of_lt hxy hyz
  obtain ⟨hφ0, hφ1, ex, ey, ez, -, hA, hk2⟩ := p19sR1_iii_setup hx hyz.le hxz
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
  rw [ex, ey, ez, p19sR1_symEllIntRD_scale hl _ _ _
      (ei19c_not_isNegReal_of_mem_slitPlane (p19sR1_csc_sq_mem hφ0 hφ1)),
    p19sR1_rpow_three_halves hl, mul_inv_cancel_left₀ (pow_ne_zero _ (p19sR1_half_pow_ne hl)),
    p19sR1_incEllIntEk_eq_sub hφ0.le hφ1 hk, p19sR1_incEllIntDk_eq hφ0 hφ1, sub_sub_cancel,
    ← mul_assoc, div_mul_cancel₀ _ hk0]
  ring

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
  have _ := hxy
  intro φ k α2
  obtain ⟨hφ0, hφ1, ex, ey, ez, hs2, hA, hk2⟩ := p19sR1_iii_setup hx hyz hxz
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
    exact p19sR1_real_scale_eq (w := p) hxz _ hc
  have hα0 : (α2 : ℂ) ≠ 0 := by
    simp only [α2]
    exact ofReal_ne_zero.mpr (div_ne_zero (sub_ne_zero.mpr (Ne.symm hpz)) hl.ne')
  rw [ex, ey, ez, ep, p19sR1_symEllIntRJ_scale hl _ _ _ _
      (ei19c_not_isNegReal_of_mem_slitPlane (p19sR1_csc_sq_sub_mem hφ0 hφ1 hα)),
    p19sR1_rpow_three_halves hl, mul_inv_cancel_left₀ (pow_ne_zero _ (p19sR1_half_pow_ne hl)),
    p19sR1_incEllIntPik_sub hφ0.le hφ1 hk hα, p19sR1_symEllIntRJ_legendre hφ0 hφ1 _ _
      (ei19c_not_isNegReal_of_mem_slitPlane (p19sR1_csc_sq_sub_mem hφ0 hφ1 hα)),
    ← mul_assoc, div_mul_cancel₀ _ hα0]

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
  intro φ k
  obtain ⟨hφ0, hφ1, ex, ey, ez, -, hA, -⟩ := p19sR1_iii_setup hx hyz hxz
  have hl : 0 < z - x := by linarith
  have hz : 0 < z := by linarith
  have hy : 0 < y := by
    rcases eq_or_lt_of_le (le_trans hx hxy) with h | h
    · exact absurd (Prod.ext (le_antisymm (h ▸ hxy) hx) h.symm) h0
    · exact h
  have hk : 1 - (k : ℂ) ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane := by
    rw [hA]; exact ofReal_mem_slitPlane.mpr (div_pos hy hz)
  have hAr : 1 - k ^ 2 * Real.sin φ ^ 2 = y / z := by exact_mod_cast hA
  have hG := p19sR1_two_mul_symEllIntRG (p19sR1_csc_sq_sub_one_arg hφ0 hφ1)
    (p19sR1_csc_sq_sub_mem hφ0 hφ1 hk) (p19sR1_csc_sq_mem hφ0 hφ1)
  have hE := p19sR1_incEllIntEk_eq hφ0 hφ1 hk
  have hF : incEllIntFk φ k = symEllIntRF (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - 1)
      (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - (k : ℂ) ^ 2) ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) :=
    (incEllIntFk_ofReal_eq_integral _ _).trans (p19sR1_symEllIntRF_legendre hφ0 hφ1 _).symm
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
    rw [p19sR1_cot_sqrt_eq hφ0 hφ1 hA0, ofReal_div, ofReal_mul,
      p19sR1_sqrt_cast_eq_cpow hc1, p19sR1_sqrt_cast_eq_cpow hck,
      p19sR1_sqrt_cast_eq_cpow (by positivity), ← ei19c_inv_cpow_half]
    push_cast
    ring
  have hL0 := p19sR1_half_pow_ne hl
  rw [ex, ey, ez, p19sR1_symEllIntRG_scale hl, p19sR1_rpow_neg_half hl, hcot2, hsq, hE, hF,
    mul_assoc, inv_mul_cancel_left₀ hL0]
  linear_combination hG

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


/-- Round-1 helper: the real `F(φ|m)` as the complex Legendre integral with `k = √m`. -/
theorem p19sR1_incEllIntFm_ofReal {m : ℝ} (hm0 : 0 ≤ m) (hm : m < 1) (φ : ℝ) :
    ((DLMF.Elliptic.Real.incEllIntFm φ m : ℝ) : ℂ) = ∫ θ in (0 : ℝ)..φ,
      (1 - ((√m : ℝ) : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) := by
  rw [DLMF.Elliptic.Real.incEllIntFm, ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hb : 0 ≤ 1 - m * Real.sin θ ^ 2 := by nlinarith [Real.sin_sq_le_one θ]
  rw [ofReal_cpow hb, p19sR1_sqrt_sq_cast hm0]
  push_cast
  ring_nf

/-- Round-1 helper: for `0 < u ≤ K(m)`, `0 < am(u|m) ≤ π/2`. -/
theorem p19sR1_jacobiAmm_mem {u m : ℝ} (hm : m < 1) (hu : 0 < u)
    (huK : u ≤ DLMF.Elliptic.Real.compEllIntKm m) :
    0 < DLMF.Elliptic.Real.jacobiAmm u m ∧ DLMF.Elliptic.Real.jacobiAmm u m ≤ π / 2 := by
  have hmono := DLMF.Elliptic.Real.strictMono_incEllIntFm hm
  have hF := DLMF.Elliptic.Real.incEllIntFm_jacobiAmm hm u
  have hF0 : DLMF.Elliptic.Real.incEllIntFm 0 m = 0 := by simp [DLMF.Elliptic.Real.incEllIntFm]
  constructor
  · have : DLMF.Elliptic.Real.incEllIntFm 0 m <
        DLMF.Elliptic.Real.incEllIntFm (DLMF.Elliptic.Real.jacobiAmm u m) m := by
      rw [hF, hF0]; exact hu
    exact hmono.lt_iff_lt.mp this
  · have : DLMF.Elliptic.Real.incEllIntFm (DLMF.Elliptic.Real.jacobiAmm u m) m ≤
        DLMF.Elliptic.Real.incEllIntFm (π / 2) m := by
      rw [hF, DLMF.Elliptic.Real.incEllIntFm_pi_div_two]; exact huK
    exact hmono.le_iff_le.mp this

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
  have _ := hm0
  obtain ⟨h0, h1⟩ := p19sR1_jacobiAmm_mem hm hu huK
  set φ := DLMF.Elliptic.Real.jacobiAmm u m with hφ
  have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos φ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], h1⟩
  have hsc := Real.sin_sq_add_cos_sq φ
  have hsn : DLMF.Elliptic.Real.jacobiSnm u m = Real.sin φ := rfl
  have hcn : DLMF.Elliptic.Real.jacobiCnm u m = Real.cos φ := rfl
  rw [hsn, hcn]
  have hlt : (Real.cos φ / Real.sin φ) ^ 2 < (1 / Real.sin φ) ^ 2 := by
    rw [div_pow, div_pow]
    exact div_lt_div_of_pos_right (by nlinarith) (by positivity)
  rw [(symEllIntRC_of_lt (sq_nonneg _) hlt).1]
  have e1 : (Real.cos φ / Real.sin φ) ^ 2 / (1 / Real.sin φ) ^ 2 = Real.cos φ ^ 2 := by
    field_simp
  have e2 : (1 / Real.sin φ) ^ 2 - (Real.cos φ / Real.sin φ) ^ 2 = 1 := by
    field_simp; linarith
  rw [e1, e2, Real.sqrt_sq hc, Real.sqrt_one, div_one, Real.arccos_cos h0.le
    (by linarith [Real.pi_pos])]

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
  obtain ⟨h0, h1⟩ := p19sR1_jacobiAmm_mem hm hu huK
  have hs : 0 < Real.sin (DLMF.Elliptic.Real.jacobiAmm u m) :=
    Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hF := DLMF.Elliptic.Real.incEllIntFm_jacobiAmm hm u
  have hb : 0 ≤ 1 - m * DLMF.Elliptic.Real.jacobiSnm u m ^ 2 := by
    unfold DLMF.Elliptic.Real.jacobiSnm; nlinarith [Real.sin_sq_le_one (DLMF.Elliptic.Real.jacobiAmm u m)]
  have e1 : (((DLMF.Elliptic.Real.jacobiCnm u m / DLMF.Elliptic.Real.jacobiSnm u m) ^ 2 : ℝ) : ℂ) =
      ((1 / Real.sin (DLMF.Elliptic.Real.jacobiAmm u m) ^ 2 : ℝ) : ℂ) - 1 := by
    have : (DLMF.Elliptic.Real.jacobiCnm u m / DLMF.Elliptic.Real.jacobiSnm u m) ^ 2 =
        1 / Real.sin (DLMF.Elliptic.Real.jacobiAmm u m) ^ 2 - 1 := by
      unfold DLMF.Elliptic.Real.jacobiCnm DLMF.Elliptic.Real.jacobiSnm
      have := Real.sin_sq_add_cos_sq (DLMF.Elliptic.Real.jacobiAmm u m)
      field_simp; linarith
    rw [this]; push_cast; ring
  have e2 : (((DLMF.Elliptic.Real.jacobiDnm u m / DLMF.Elliptic.Real.jacobiSnm u m) ^ 2 : ℝ) : ℂ) =
      ((1 / Real.sin (DLMF.Elliptic.Real.jacobiAmm u m) ^ 2 : ℝ) : ℂ) - ((√m : ℝ) : ℂ) ^ 2 := by
    have : (DLMF.Elliptic.Real.jacobiDnm u m / DLMF.Elliptic.Real.jacobiSnm u m) ^ 2 =
        1 / Real.sin (DLMF.Elliptic.Real.jacobiAmm u m) ^ 2 - m := by
      rw [div_pow, DLMF.Elliptic.Real.jacobiDnm, ← Real.sqrt_eq_rpow, Real.sq_sqrt hb]
      unfold DLMF.Elliptic.Real.jacobiSnm
      field_simp
    rw [this, p19sR1_sqrt_sq_cast hm0]; push_cast; ring
  have e3 : (((1 / DLMF.Elliptic.Real.jacobiSnm u m) ^ 2 : ℝ) : ℂ) =
      ((1 / Real.sin (DLMF.Elliptic.Real.jacobiAmm u m) ^ 2 : ℝ) : ℂ) := by
    unfold DLMF.Elliptic.Real.jacobiSnm; push_cast; ring
  rw [e1, e2, e3, p19sR1_symEllIntRF_legendre h0 h1, ← p19sR1_incEllIntFm_ofReal hm0 hm, hF]

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
  have hre : 0 < (1 - z).re := by
    have := (abs_re_le_norm z).trans_lt hz
    simp only [sub_re, one_re]
    linarith [le_abs_self z.re]
  have hw : (1 - z) ∈ slitPlane := Or.inl hre
  rw [symEllIntR_of_mem _ _ (ei19c_slit2 hw one_mem_slitPlane)]
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
theorem symEllIntR_two_eq_ordinaryHypergeometric (a b₁ b₂ : ℂ) (hb : ∀ n : ℕ, b₁ + b₂ ≠ -n)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ slitPlane) (hz₂ : z₂ ∈ slitPlane) (hz : ‖1 - z₁ / z₂‖ < 1)
    (harg : arg z₁ - arg z₂ ∈ Ioo (-π) π) :
    symEllIntR a ![b₁, b₂] ![z₁, z₂] = z₂ ^ (-a) * ordinaryHypergeometric a b₁ (b₁ + b₂)
        (1 - z₁ / z₂) := by
  sorry

/-! ### Round-1 helpers: the lemniscate constants -/

/-- Round-1 helper (DLMF 19.21.1 at `z = 1`): `R_F(0, 1, 2) · (1/3) R_D(0, 2, 1) = π/4`. -/
theorem p19sR1_lemniscate_product :
    symEllIntRF 0 1 2 * ((1 / 3) * symEllIntRD 0 2 1) = π / 4 := by
  have hL := DLMF.Elliptic.legendre_relation (m := 1 / 2) (by norm_num) (by norm_num)
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hL
  set k : ℂ := ((√(1 / 2 : ℝ) : ℝ) : ℂ) with hk
  have hk2 : k ^ 2 = ((1 / 2 : ℝ) : ℂ) := p19sR1_sqrt_sq_cast (by norm_num)
  have hK := compEllIntKk_eq_ofReal (k := k) (m := 1 / 2) hk2 (by norm_num)
  have hE := compEllIntEk_eq_ofReal (k := k) (m := 1 / 2) hk2 (by norm_num)
  have hk2' : k ^ 2 = 1 / 2 := by rw [hk2]; push_cast; ring
  have h12 : (1 / 2 : ℂ) ∈ slitPlane := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
    exact ofReal_mem_slitPlane.mpr (by norm_num)
  have hmem : 1 - k ^ 2 ∈ slitPlane := by
    rw [hk2', show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num]; exact h12
  obtain ⟨-, -, -, -, h5⟩ := compEllIntEk_eq_symEllInt hmem
  have hKF := compEllIntKk_eq_symEllIntRF hmem
  rw [hk2', show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num] at h5 hKF
  have hl : (0 : ℝ) < 2 := by norm_num
  have hA := p19sR1_symEllIntRF_scale hl 0 (1 / 2) 1
  have hB := p19sR1_symEllIntRD_scale hl 0 1 (1 / 2) (ei19c_not_isNegReal_of_mem_slitPlane h12)
  simp only [mul_zero, mul_one, ofReal_ofNat] at hA hB
  rw [show (2 : ℂ) * (1 / 2) = 1 by norm_num] at hA hB
  rw [hA, hB, ← hKF]
  have hL2 := p19sR1_half_pow_sq hl
  have hL0 := p19sR1_half_pow_ne hl
  simp only [ofReal_ofNat] at hL2 hL0
  have hLc : ((compEllIntEk k * JacobiElliptic.compEllIntKk k + compEllIntEk k * JacobiElliptic.compEllIntKk k -
      JacobiElliptic.compEllIntKk k * JacobiElliptic.compEllIntKk k : ℂ)) = π / 2 := by
    rw [hK, hE]; exact_mod_cast hL
  generalize (2 : ℂ) ^ (1 / 2 : ℂ) = L at hL2 hL0 ⊢
  have hL4 : L ^ 4 = 4 := by rw [show L ^ 4 = (L ^ 2) ^ 2 by ring, hL2]; norm_num
  rw [show L⁻¹ * JacobiElliptic.compEllIntKk k * (1 / 3 * ((L ^ 3)⁻¹ * symEllIntRD 0 1 (1 / 2))) =
      JacobiElliptic.compEllIntKk k * symEllIntRD 0 1 (1 / 2) * (L ^ 4)⁻¹ / 3 by field_simp, hL4]
  linear_combination (-JacobiElliptic.compEllIntKk k) * h5 + (1 / 2 : ℂ) * hLc

/-- Round-1 helper: `R_F(0, 1, 2) = Γ(1/4)²/(4 √(2π))` (DLMF 19.20.2). -/
theorem p19sR1_symEllIntRF_zero_one_two :
    symEllIntRF 0 1 2 = ((Real.Gamma (1 / 4) ^ 2 / (4 * Real.sqrt (2 * π)) : ℝ) : ℂ) := by
  set k : ℂ := ((√(1 / 2 : ℝ) : ℝ) : ℂ) with hk
  have hk2 : k ^ 2 = ((1 / 2 : ℝ) : ℂ) := p19sR1_sqrt_sq_cast (by norm_num)
  have hK := compEllIntKk_eq_ofReal (k := k) (m := 1 / 2) hk2 (by norm_num)
  have hk2' : k ^ 2 = 1 / 2 := by rw [hk2]; push_cast; ring
  have h12 : (1 / 2 : ℂ) ∈ slitPlane := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
    exact ofReal_mem_slitPlane.mpr (by norm_num)
  have hmem : 1 - k ^ 2 ∈ slitPlane := by
    rw [hk2', show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num]; exact h12
  have hKF := compEllIntKk_eq_symEllIntRF hmem
  rw [hk2', show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num] at hKF
  have hl : (0 : ℝ) < 2 := by norm_num
  have hA := p19sR1_symEllIntRF_scale hl 0 (1 / 2) 1
  simp only [mul_zero, mul_one, ofReal_ofNat] at hA
  rw [show (2 : ℂ) * (1 / 2) = 1 by norm_num] at hA
  have h2 : (2 : ℂ) ^ (1 / 2 : ℂ) = ((√2 : ℝ) : ℂ) := by
    rw [p19sR1_sqrt_cast_eq_cpow (by norm_num)]; push_cast; ring_nf
  rw [hA, ← hKF, hK, DLMF.Elliptic.Real.compEllIntKm_one_half, h2, Real.sqrt_mul (by norm_num)]
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hsπ : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  push_cast
  field_simp

/-- Round-1 helper: `∫₀¹ t² dt/√(1 - t⁴) = ∫₀^{π/2} sin² θ dθ/√(1 + sin² θ)` (`t = sin θ`). -/
theorem p19sR1_integral_sq_div_sqrt :
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
theorem p19sR1_integral_sq_div_sqrt_eq :
    ((∫ t in (0 : ℝ)..1, t ^ 2 / Real.sqrt (1 - t ^ 4) : ℝ) : ℂ) =
      (1 / 3) * symEllIntRD 0 2 1 := by
  have hp : (0 : ℝ) < π / 2 := by positivity
  have hD := p19sR1_symEllIntRD_legendre hp le_rfl I
  rw [p19sR1_csc_sq_pi_div_two, sub_self, I_sq, show (1 : ℂ) - -1 = 2 by norm_num] at hD
  rw [hD, p19sR1_integral_sq_div_sqrt, ← intervalIntegral.integral_ofReal]
  rw [← mul_assoc, show (1 / 3 : ℂ) * 3 = 1 by norm_num, one_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [ofReal_div, p19sR1_sqrt_cast_eq_cpow (by positivity), cpow_neg]
  push_cast
  ring_nf

end DLMF.EllipticIntegrals
