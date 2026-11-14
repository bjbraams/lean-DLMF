/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import DLMF.QHypergeometric.Convergence
import DLMF.QSeries.RamanujanPsi
import Mathlib.Tactic.Ring
/-!
# Ramanujan’s bilateral one-psi-one sum

The annular sum of DLMF 17.8.2 reuses the denominator-cleared proof
`DLMF.QSeries.ramanujan_1psi1_of_regular`. The product quotient retains the normalization
used for analytic continuation of the bilateral series.
-/

public noncomputable section
open Complex DLMF.QSeries
namespace DLMF.QHypergeometric

/-- Ramanujan's product quotient, giving continuation of one-psi-one. -/
@[expose] def qRamanujanValue (a b q z : ℂ) : ℂ :=
  qPochhammerListInf [q,b/a,a*z,q/(a*z)] q/qPochhammerListInf [b,q/a,z,b/(a*z)] q

/-- Ramanujan's `1ψ1` summation, valid for `|b/a| < |z| < 1` (DLMF 17.8.E2). -/
@[dlmf 17.8.E2]
theorem ramanujan_one_psi_one {a b q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (ha : a≠0)
    (hab : QBilateralRegular [a] [b] q) (hz : ‖b/a‖<‖z‖ ∧ ‖z‖<1) :
    qPsi [a] [b] q z=qRamanujanValue a b q z := by
  have h := ramanujan_1psi1_of_regular hq0 hq ha (fun n => hab.2 a (by simp) n)
    (fun n => hab.1 b (by simp) n) hz
  unfold qPsi qRamanujanValue
  simp only [qPsiTerm, qPochhammerListInt, qPsiExponent, qPochhammerListInf, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one, List.length_singleton, sub_self,
    zpow_zero]
  rw [h]
  ring

end DLMF.QHypergeometric
