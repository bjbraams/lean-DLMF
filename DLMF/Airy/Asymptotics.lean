/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Airy.Asymptotics.LaplaceSectors
public import DLMF.Airy.Asymptotics.OscillatoryForms
public import DLMF.Airy.Asymptotics.RotatedBi
public import DLMF.Airy.Asymptotics.RealRemainders
public import DLMF.Airy.Asymptotics.SectorRemainders
public import DLMF.Airy.Asymptotics.OscillatoryRemainders
public import DLMF.Airy.Asymptotics.DerivativeRemainders
public import DLMF.Airy.Asymptotics.DerivativeErrorBounds

/-!
# Airy asymptotic expansions and error bounds (DLMF §9.7)

Exponential and oscillatory Poincaré expansions of `Ai`, `Bi` and their derivatives, the
expansions on rotated rays, and the real and complex remainder bounds of DLMF §9.7(iii)–(v).
-/
