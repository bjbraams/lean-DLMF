/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Gamma.Integrals.BarnesAndRamanujan
public import DLMF.Gamma.Integrals.FourierAndTrigamma

/-!
# Mellin–Barnes and related integrals; sums (DLMF §§5.13, 5.16)

This umbrella collects Barnes's beta integral, the vertical integral of `|Γ(a + it)|²`,
Barnes's first lemma, Ramanujan's integrals (DLMF §5.13) and the sums of DLMF §5.16. Vertical
integrals are stated with a real parameter `t` along `s = σ + it` in place of DLMF's
`c ± i∞` contour, on the indicated real-part strips, so DLMF's factor `1/(2πi) ds` becomes
`1/(2π) dt`; the inversion contour 5.13.1 is restricted to positive real `z`.
-/
