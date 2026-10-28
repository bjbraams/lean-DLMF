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

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; since 2026-10-22 every statement in this
file is proved (the 14.16 zero counts via the Sturm separation tools of
`DLMF.Legendre.ZeroCounts`). See `DLMF111214Acquisition.md` for coverage and validation.
-/
