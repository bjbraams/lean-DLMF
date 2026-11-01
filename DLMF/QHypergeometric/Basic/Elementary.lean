/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.Basic

/-!
# `q`-elementary functions (DLMF §17.3)

This file defines the scaled `q`-exponentials, `q`-sines and `q`-cosines of DLMF §17.3 by their
product forms and proves the Euler-type relations between them and their parity.

## Main definitions

* `qExp`, `qExpBig`: the scaled little and big `q`-exponentials (DLMF 17.3.1–17.3.2).
* `qSin`, `qSinBig`, `qCos`, `qCosBig`: the `q`-sines and `q`-cosines (DLMF 17.3.3–17.3.6).

## Main results

* `qCos_add_I_mul_qSin`, `qCosBig_add_I_mul_qSinBig`: `cos_q x + i sin_q x = e_q(i x)` and its
  big analogue.
* `qSin_neg`, `qCos_neg`, `qSinBig_neg`, `qCosBig_neg`: the `q`-sines are odd and the
  `q`-cosines are even.

## Implementation notes

DLMF scales the two `q`-exponentials by `1 - q`. The product definitions retain analytic
continuation; the series expansions, with their convergence domains, are in
`DLMF.QHypergeometric.Elementary`.
-/

@[expose] public noncomputable section
open Complex DLMF.QSeries
namespace DLMF.QHypergeometric

/-- The scaled little q-exponential, including its meromorphic product continuation. -/
@[dlmf 17.3.E1]
def qExp (q x : ℂ) : ℂ := (qPochhammerInf ((1-q)*x) q)⁻¹

/-- The scaled big q-exponential, an entire product in its argument when |q|<1. -/
@[dlmf 17.3.E2]
def qExpBig (q x : ℂ) : ℂ := qPochhammerInf (-(1-q)*x) q

/-- The little q-sine. -/
@[dlmf 17.3.E3]
def qSin (q x : ℂ) : ℂ := (qExp q (I*x)-qExp q (-I*x))/(2*I)

/-- The big q-sine. -/
@[dlmf 17.3.E4]
def qSinBig (q x : ℂ) : ℂ := (qExpBig q (I*x)-qExpBig q (-I*x))/(2*I)

/-- The little q-cosine. -/
@[dlmf 17.3.E5]
def qCos (q x : ℂ) : ℂ := (qExp q (I*x)+qExp q (-I*x))/2

/-- The big q-cosine. -/
@[dlmf 17.3.E6]
def qCosBig (q x : ℂ) : ℂ := (qExpBig q (I*x)+qExpBig q (-I*x))/2

/-- The little `q`-cosine and `q`-sine combine to the little `q`-exponential. -/
theorem qCos_add_I_mul_qSin (q x : ℂ) : qCos q x + I * qSin q x = qExp q (I * x) := by
  simp only [qCos, qSin]
  field_simp
  ring

/-- The big `q`-cosine and `q`-sine combine to the big `q`-exponential. -/
theorem qCosBig_add_I_mul_qSinBig (q x : ℂ) :
    qCosBig q x + I * qSinBig q x = qExpBig q (I * x) := by
  simp only [qCosBig, qSinBig]
  field_simp
  ring

/-- The little `q`-sine is odd. -/
@[simp]
theorem qSin_neg (q x : ℂ) : qSin q (-x) = -qSin q x := by
  simp only [qSin, mul_neg, neg_mul, neg_neg]
  ring

/-- The little `q`-cosine is even. -/
@[simp]
theorem qCos_neg (q x : ℂ) : qCos q (-x) = qCos q x := by
  simp only [qCos, mul_neg, neg_mul, neg_neg]
  ring

/-- The big `q`-sine is odd. -/
@[simp]
theorem qSinBig_neg (q x : ℂ) : qSinBig q (-x) = -qSinBig q x := by
  simp only [qSinBig, mul_neg, neg_mul, neg_neg]
  ring

/-- The big `q`-cosine is even. -/
@[simp]
theorem qCosBig_neg (q x : ℂ) : qCosBig q (-x) = qCosBig q x := by
  simp only [qCosBig, mul_neg, neg_mul, neg_neg]
  ring

end DLMF.QHypergeometric
