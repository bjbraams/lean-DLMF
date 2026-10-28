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

Vertical-line integrals are acquired with a real parameter `t` in place of the
source's `c±i∞` contour, on the indicated real-part strips. The inversion
contour 5.13.1 is restricted to positive real `z`. Parametrizing `s = σ + it`
converts the factor `1/(2πi) ds` into `1/(2π) dt`.
The alternating trigamma sum 5.16.1 has closed-form partial sums, and its limit
uses the odd part of `ζ(2)`.
-/
