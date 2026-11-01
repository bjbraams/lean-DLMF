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

This area defines the polylogarithm `Li_n(z) = ∑ z^k/k^n` on the unit disk
(`DLMF.Polylog.Basic`), the real dilogarithm `Li₂(x) = -∫₀ˣ log(1-t)/t dt` for `x ≤ 1`
(`DLMF.Polylog.Dilog`) and the real trilogarithm (`DLMF.Polylog.Trilog`), with their special
values and functional equations. Mathlib has the values `ζ(2k)`, `expZeta` and the series of
`log` and `arctan`, but no polylogarithm.
-/
