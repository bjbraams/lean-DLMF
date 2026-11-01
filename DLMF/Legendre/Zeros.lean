/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Legendre.Zeros.FerrersAndReal
public import DLMF.Legendre.Zeros.Exterior

/-!
# Real Legendre zero counts and interlacing

The real zeros of Ferrers and associated Legendre functions (DLMF §14.16): zero counts and
interlacing in `(-1, 1)` in `FerrersAndReal`, and exterior zeros on `(1, ∞)` in `Exterior`.
The zero counts rest on the Sturm comparison and separation tools of `DLMF.Legendre.ZeroTools`
and `DLMF.Legendre.ZeroCounts`.
-/
