/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Polylog.Basic
public import DLMF.Polylog.Dilog
public import DLMF.Polylog.Trilog

/-!
# Polylogarithms (Duverney Chapter 8; DLMF §25.12)

This area develops the polylogarithm series `Li_n(z) = ∑ z^k/k^n` of natural order on the unit
disk (`DLMF.Polylog.Basic.Series`), the real dilogarithm `Li₂(x) = -∫₀ˣ log(1-t)/t dt` for
`x ≤ 1` (`DLMF.Polylog.Basic.Dilog` and `DLMF.Polylog.Dilog`) and the real trilogarithm
(`DLMF.Polylog.Trilog`), with their special values and functional equations. The series and
the polylogarithm `Li_s(z)` of complex order, continued to `ℂ \ [1, ∞)`, are
`DLMF.Zeta.polylogSeries` and `DLMF.Zeta.polylog`. Mathlib has the values `ζ(2k)`, `expZeta` and
the series of `log` and `arctan`, but no polylogarithm.
-/
