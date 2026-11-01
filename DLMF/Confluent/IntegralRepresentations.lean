/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Confluent.IntegralRepresentations.EulerAndBessel
public import DLMF.Confluent.IntegralRepresentations.BarnesAndConnections

/-!
# Integral representations of confluent hypergeometric functions

Euler, Laplace, Bessel-kernel and vertical Barnes integrals for Kummer's, Tricomi's and
Whittaker's functions (DLMF §§13.4, 13.16). The Gauss and Stieltjes representations 13.4.5,
13.4.6, 13.4.8, 13.16.6 and 13.16.9 are in `DLMF.Confluent.Integrals`; the Hankel-loop and
Pochhammer double-loop formulas 13.4.9–13.4.15 are not formalized.
-/
