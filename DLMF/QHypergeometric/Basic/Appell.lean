/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Basic.Series

/-!
# `q`-Appell functions (DLMF §17.4(iii))

This file defines the four `q`-Appell functions by their double series.

## Main definitions

* `qAppell1`, `qAppell2`, `qAppell3`, `qAppell4`: the `q`-Appell functions
  (DLMF 17.4.5–17.4.8), with terms `qAppell1Term`, …, `qAppell4Term`.

## Implementation notes

All four functions use the actual double series, totalized outside their convergence sets.
Absolute convergence on a bidisc and the transformations of DLMF §17.11 are in
`DLMF.QHypergeometric.Appell`.
-/

@[expose] public noncomputable section
open DLMF.QSeries
namespace DLMF.QHypergeometric

/-- One double-series term of the first q-Appell function. -/
def qAppell1Term (a b bp c q x y : ℂ) (p : ℕ × ℕ) : ℂ :=
  qPochhammer a q (p.1+p.2) * qPochhammer b q p.1 * qPochhammer bp q p.2 *
    x^p.1 * y^p.2 /
    (qPochhammer q q p.1 * qPochhammer q q p.2 * qPochhammer c q (p.1+p.2))

/-- The first q-Appell function, totalized outside its double-series convergence set. -/
@[dlmf 17.4.E5]
def qAppell1 (a b bp c q x y : ℂ) : ℂ := ∑' p : ℕ × ℕ, qAppell1Term a b bp c q x y p

/-- One double-series term of the second q-Appell function. -/
def qAppell2Term (a b bp c cp q x y : ℂ) (p : ℕ × ℕ) : ℂ :=
  qPochhammer a q (p.1+p.2) * qPochhammer b q p.1 * qPochhammer bp q p.2 *
    x^p.1 * y^p.2 /
    (qPochhammerList [q,c] q p.1 * qPochhammerList [q,cp] q p.2)

/-- The second q-Appell function. -/
@[dlmf 17.4.E6]
def qAppell2 (a b bp c cp q x y : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ, qAppell2Term a b bp c cp q x y p

/-- One double-series term of the third q-Appell function. -/
def qAppell3Term (a ap b bp c q x y : ℂ) (p : ℕ × ℕ) : ℂ :=
  qPochhammerList [a,b] q p.1 * qPochhammerList [ap,bp] q p.2 * x^p.1 * y^p.2 /
    (qPochhammer q q p.1 * qPochhammer q q p.2 * qPochhammer c q (p.1+p.2))

/-- The third q-Appell function. -/
@[dlmf 17.4.E7]
def qAppell3 (a ap b bp c q x y : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ, qAppell3Term a ap b bp c q x y p

/-- One double-series term of the fourth q-Appell function. -/
def qAppell4Term (a b c cp q x y : ℂ) (p : ℕ × ℕ) : ℂ :=
  qPochhammerList [a,b] q (p.1+p.2) * x^p.1 * y^p.2 /
    (qPochhammerList [q,c] q p.1 * qPochhammerList [q,cp] q p.2)

/-- The fourth q-Appell function. -/
@[dlmf 17.4.E8]
def qAppell4 (a b c cp q x y : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ, qAppell4Term a b c cp q x y p

end DLMF.QHypergeometric
