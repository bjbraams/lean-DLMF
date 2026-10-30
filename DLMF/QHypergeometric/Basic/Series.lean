/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.Basic
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.RCLike.Sqrt

/-!
# General basic hypergeometric series and parameter conditions
-/

@[expose] public noncomputable section

open Complex Filter Finset Set
open scoped Real Topology ENNReal NNReal

namespace DLMF.QHypergeometric

/-- A product of finite q-shifted factorials; parameter repetitions are retained. -/
@[dlmf 17.2.E5]
def qPochhammerList (a : List ℂ) (q : ℂ) (n : ℕ) : ℂ :=
  (a.map fun ai => DLMF.QSeries.qPochhammer ai q n).prod
/-- A product of integer-index q-shifted factorials, reusing the negative-index convention. -/
def qPochhammerListInt (a : List ℂ) (q : ℂ) (n : ℤ) : ℂ :=
  (a.map fun ai => DLMF.QSeries.qPochhammerInt ai q n).prod
/-- A product of infinite q-shifted factorials. -/
@[dlmf 17.2.E6]
def qPochhammerListInf (a : List ℂ) (q : ℂ) : ℂ :=
  (a.map fun ai => DLMF.QSeries.qPochhammerInf ai q).prod
/-- The DLMF phase exponent for a unilateral series, computed in the integers. -/
def qPhiExponent (a b : List ℂ) : ℤ := 1+(b.length:ℤ)-(a.length:ℤ)
/-- The DLMF phase exponent for a bilateral series, computed in the integers. -/
def qPsiExponent (a b : List ℂ) : ℤ := (b.length:ℤ)-(a.length:ℤ)
/-- General unilateral basic-hypergeometric term, including the integer phase exponent. -/
def qPhiTerm (a b : List ℂ) (q z : ℂ) (n : ℕ) : ℂ :=
  qPochhammerList a q n/(qPochhammerList b q n*DLMF.QSeries.qPochhammer q q n)*
    (((-1:ℂ)^n*q^DLMF.QSeries.TripleProduct.tri (n:ℤ))^qPhiExponent a b)*z^n
/-- General unilateral basic-hypergeometric series r-phi-s. -/
@[dlmf 17.4.E1]
def qPhi (a b : List ℂ) (q z : ℂ) : ℂ := ∑' n : ℕ, qPhiTerm a b q z n
/-- General bilateral basic-hypergeometric term, with integer index and phase exponent. -/
def qPsiTerm (a b : List ℂ) (q z : ℂ) (n : ℤ) : ℂ :=
  qPochhammerListInt a q n/qPochhammerListInt b q n*
    (((-1:ℂ)^n*q^DLMF.QSeries.TripleProduct.tri n)^qPsiExponent a b)*z^n
/-- General bilateral basic-hypergeometric series r-psi-s. -/
@[dlmf 17.4.E3]
def qPsi (a b : List ℂ) (q z : ℂ) : ℂ := ∑' n : ℤ, qPsiTerm a b q z n
/-- A finite unilateral sum, including its term of index N. -/
def qPhiPartial (a b : List ℂ) (q z : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ range (N+1), qPhiTerm a b q z n
/-- Denominator parameters avoid the nonpositive q-lattice. -/
def qDenominatorRegular (b : List ℂ) (q : ℂ) : Prop :=
  ∀ bi∈b, ∀ n : ℕ, bi*q^n≠1
/-- Bilateral parameters avoid the additional positive q-lattice in the numerator. -/
def qBilateralRegular (a b : List ℂ) (q : ℂ) : Prop :=
  qDenominatorRegular b q ∧ ∀ ai∈a, ∀ n : ℕ, ai≠q^(n+1)
/-- Termination by an upper parameter q^(-N); lower-parameter validity is independent. -/
def qTerminating (a : List ℂ) (q : ℂ) : Prop :=
  ∃ ai∈a, ∃ N : ℕ, ai=q^(-(N:ℤ))

/-- Rogers–Ramanujan G; the term n=0 supplies the initial1. -/
def rogersG (q : ℂ) : ℂ := ∑' n : ℕ, q^(n*n)/DLMF.QSeries.qPochhammer q q n
/-- Rogers–Ramanujan H; the term n=0 supplies the initial1. -/
def rogersH (q : ℂ) : ℂ := ∑' n : ℕ, q^(n*(n+1))/DLMF.QSeries.qPochhammer q q n
/-- Complex-order shifted factorial, on the principal branch of q^ν. -/
def qPochhammerOrder (a q ν : ℂ) : ℂ :=
  DLMF.QSeries.qPochhammerInf a q/DLMF.QSeries.qPochhammerInf (a*q^ν) q
/-- Lower parameters are regular only through the final retained index of a terminating sum. -/
def qDenominatorRegularThrough (b : List ℂ) (q : ℂ) (N : ℕ) : Prop :=
  qPochhammerList b q N≠0
/-- Balanced/Saalschuetzian unilateral series: termination, r=s+1, z=q, and the product balance. -/
@[dlmf 17.4.E9]
def qBalanced (a b : List ℂ) (q z : ℂ) : Prop :=
  qTerminating a q ∧ a.length=b.length+1 ∧ z=q ∧ q*a.prod=b.prod
/-- k-balanced series; k=1 gives the product condition in the balanced case. -/
@[dlmf 17.4.E10]
def qKBalanced (k : ℤ) (a b : List ℂ) (q : ℂ) : Prop :=
  a.length=b.length+1 ∧ q^k*a.prod=b.prod
/-- Well-poised parameters, with a0 singled out and paired remaining upper/lower lists. -/
@[dlmf 17.4.E11]
def qWellPoised (a0 : ℂ) (a b : List ℂ) (q : ℂ) : Prop :=
  List.Forall₂ (fun ai bi => a0*q=ai*bi) a b
/-- Very-well-poised parameters, preserving the first two principal square-root parameters. -/
@[dlmf 17.4.E12]
def qVeryWellPoised (a0 : ℂ) (a b : List ℂ) (q : ℂ) : Prop :=
  qWellPoised a0 a b q ∧ ∃ bb : List ℂ,
    b=Complex.sqrt a0 :: -Complex.sqrt a0 :: bb
/-- Nearly-poised parameters: the paired relations hold except possibly at the last pair. -/
@[dlmf 17.4.E13]
def qNearlyPoised (a0 : ℂ) (a b : List ℂ) (q : ℂ) : Prop :=
  a.length=b.length ∧ List.Forall₂ (fun ai bi => a0*q=ai*bi) a.dropLast b.dropLast
/-- The idem notation is the sum obtained by singling out every parameter except the first. -/
def qIdem (f : ℂ → List ℂ → ℂ) (a : List ℂ) : ℂ :=
  ∑ j ∈ range (a.length-1), f (a[j+1]!) (a.eraseIdx (j+1))

/-- The scalar coefficient of the general unilateral series. -/
def qPhiCoeff (a b : List ℂ) (q : ℂ) (n : ℕ) : ℂ := qPhiTerm a b q 1 n
/-- Mathlib's formal scalar power series associated with the general q-series. -/
def qPhiPowerSeries (a b : List ℂ) (q : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (qPhiCoeff a b q)

end DLMF.QHypergeometric
