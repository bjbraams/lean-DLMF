/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Basic.Legendre
public import DLMF.JacobiElliptic.AnalyticProperties
public import DLMF.Elliptic.ThirdKind
public import Carlson.Elliptic.Standard

/-!
# Legendre's elliptic integrals: bridges to `lean-codes`

For real amplitude and real modulus with `k² ≤ 1`, the complex Legendre integrals of
`DLMF.EllipticIntegrals.Basic.Legendre` (DLMF §19.2) agree with the real Legendre integrals of
the companion library `lean-codes` (Carlson).

## Main results

* `incEllIntFk_ofReal`, `incEllIntEk_ofReal`, `incEllIntPik_ofReal`,
  `compEllIntKk_ofReal_carlson`, `compEllIntEk_ofReal`: bridges to the real integrals of
  `lean-codes`.

## References

* NIST DLMF §§19.1, 19.2.
* B. C. Carlson, *Special Functions of Applied Mathematics*, 1977 (via `lean-codes`).
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory intervalIntegral
open scoped Real Topology

namespace DLMF.EllipticIntegrals

open DLMF.JacobiElliptic

/-- Bridge to `lean-codes`: for real `φ` and real `k` with `k² ≤ 1`,
`F(φ, k) = Carlson.Real.incEllIntFk φ k`. -/
theorem incEllIntFk_ofReal {φ k : ℝ} (hk : k ^ 2 ≤ 1) :
    incEllIntFk φ k = (Carlson.Real.incEllIntFk φ k : ℂ) := by
  rw [incEllIntFk_eq_ofReal (m := k ^ 2) (by push_cast; ring) hk, DLMF.Elliptic.Real.incEllIntFm,
    Carlson.Real.incEllIntFk]
  norm_num

/-- Bridge to `lean-codes`: for real `φ` and real `k` with `k² ≤ 1`,
`E(φ, k) = Carlson.Real.incEllIntEk φ k`. -/
theorem incEllIntEk_ofReal {φ k : ℝ} (hk : k ^ 2 ≤ 1) :
    incEllIntEk φ k = (Carlson.Real.incEllIntEk φ k : ℂ) := by
  rw [incEllIntEk_eq_ofReal (m := k ^ 2) (by push_cast; ring) hk, DLMF.Elliptic.Real.incEllIntEm,
    Carlson.Real.incEllIntEk]

/-- Bridge to `lean-codes`: `K(k) = Carlson.Real.compEllIntKk k` for real `k`, `k² ≤ 1`. -/
theorem compEllIntKk_ofReal_carlson {k : ℝ} (hk : k ^ 2 ≤ 1) :
    compEllIntKk k = (Carlson.Real.compEllIntKk k : ℂ) := by
  rw [compEllIntKk_eq_incEllIntFk, show ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) by push_cast; ring,
    incEllIntFk_ofReal hk, Carlson.Real.compEllIntKk]

/-- Bridge to `lean-codes`: `E(k) = Carlson.Real.compEllIntEk k` for real `k`, `k² ≤ 1`. -/
theorem compEllIntEk_ofReal {k : ℝ} (hk : k ^ 2 ≤ 1) :
    compEllIntEk k = (Carlson.Real.compEllIntEk k : ℂ) := by
  rw [compEllIntEk, show ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) by push_cast; ring,
    incEllIntEk_ofReal hk, Carlson.Real.compEllIntEk]

/-- Bridge to `lean-codes`: for real `φ`, real `α² < 1` and real `k` with `k² ≤ 1`,
`Π(φ, α², k) = Carlson.Real.incEllIntPik φ α² k`. -/
theorem incEllIntPik_ofReal {φ α2 k : ℝ} (hα : α2 < 1) (hk : k ^ 2 ≤ 1) :
    incEllIntPik φ α2 k = (Carlson.Real.incEllIntPik φ α2 k : ℂ) := by
  rw [incEllIntPik_eq_ofReal (m := k ^ 2) (by push_cast; ring) hk hα,
    DLMF.Elliptic.Real.incEllIntPim, Carlson.Real.incEllIntPik]
  simp only [DLMF.Elliptic.piIntegrand]
  norm_num

end DLMF.EllipticIntegrals
