/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Polylog.Basic.Dilog
public import DLMF.Polylog.Basic.Series

/-!
# The polylogarithm: foundations (Duverney Chapter 8; DLMF §25.12)

* `DLMF.Polylog.Basic.Series`: basic properties of the series `Li_n(z) = ∑_{k ≥ 1} z^k/k^n` of
  natural order (`DLMF.Zeta.polylogSeries` at `s = n`).
* `DLMF.Polylog.Basic.Dilog`: the real dilogarithm `Real.dilog` as an integral, its derivative
  and its agreement with the series `Li₂` on `[-1, 1]`.

The series `DLMF.Zeta.polylogSeries` and the polylogarithm `DLMF.Zeta.polylog` of complex order
are defined in `DLMF.Zeta.Basic.Polylog`.
-/
