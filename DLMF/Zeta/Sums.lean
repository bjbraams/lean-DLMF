/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Zeta.Sums.ShiftedSeries
public import DLMF.Zeta.Sums.PowerSeries
public import DLMF.Zeta.Sums.OddEven

/-!
# Sums involving the Riemann zeta function

Umbrella for DLMF §25.8: `Sums.ShiftedSeries` (25.8.1–25.8.3), `Sums.PowerSeries`
(25.8.4–25.8.8) and `Sums.OddEven` (25.8.9–25.8.10).

## Implementation notes

Logarithms are principal: for `|z| < 1` the values `Γ(1-z)` and `πz/sin(πz)` stay off the
negative real axis, so DLMF's `ln Γ(1-z)` (the branch continuous from `ln Γ(1) = 0`) and
`ln(πz/sin(πz))` agree with `Complex.log` there. 25.8.6 excludes `z = 0`, where `πz cot(πz)` is
a removable `0 · ∞` form (Lean's `cot 0 = 0`); 25.8.3 excludes `s = 0, -1, -2, …` besides DLMF's
`s ≠ 1`: there the term `(s)_{1-s} ζ(1)` of the printed series is a `0 · ∞` form, for which
Lean's totalized `riemannZeta 1` gives a wrong value.
-/
