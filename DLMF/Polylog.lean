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

Mathlib has the values `ζ(2k)`, `expZeta` and the series of `log` and `arctan`, but no
polylogarithm. This area defines `Li_n(z) = ∑ z^k/k^n` on the unit disk (`DLMF.Polylog.Basic`) and
the real dilogarithm `Li₂(x) = -∫₀ˣ log(1-t)/t dt` for `x ≤ 1` (`DLMF.Polylog.Dilog`), with:
* `Li₁(z) = -log(1-z)`, `Li_{n+1}' = Li_n/z`, `Li_n(1) = ζ(n)`, `Li_n(-1) = -(1-2^{1-n})ζ(n)`,
  the duplication formula, and `Li_n(e^{2πia}) = expZeta a n`;
* `Li₂(±1)`, Euler's reflection formula, `Li₂(1/2)`, Landen's identity, the inversion formula
  and the golden-ratio values;
* the real trilogarithm (`DLMF.Polylog.Trilog`): `Li₃(±1)`, Landen's identity for `Li₃` and
  `Li₃(1/2) = (7/8)ζ(3) - (π²/12) ln 2 + (ln 2)³/6`.
-/
