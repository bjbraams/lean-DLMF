/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Constants.BBP
public import DLMF.Constants.Catalan
public import DLMF.Constants.Dirichlet

/-!
# Elementary constants and series (Duverney §§2.5, 8.4)

* `DLMF.Constants.Dirichlet`: `∑ (-1)^i/(i+1) = ln 2` (as a limit of partial sums), Dirichlet's
  `η(s) = (1 - 2^{1-s}) ζ(s)` and `λ(s) = (1 - 2^{-s}) ζ(s)` for `Re s > 1`, and `ζ(s) → 1`.
* `DLMF.Constants.Catalan`: Catalan's constant `G`, with `ψ'(1/4) = π² + 8G` and
  `ψ'(3/4) = π² - 8G`.
* `DLMF.Constants.BBP`: the Bailey–Borwein–Plouffe formula for `π`, BBP-type series for `ln 2`,
  `ln 3`, `ln 5`, and Gauss's Machin-like formula.

There are no admissions.
-/
