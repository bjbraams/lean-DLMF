/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Coulomb.RealOrder

public import DLMF.Coulomb.OrderMinimality
public import DLMF.Coulomb.Basic
public import DLMF.Coulomb.Basic.AuxiliaryData
public import DLMF.Coulomb.RhoEtaProperties
public import DLMF.Coulomb.RhoEtaLimits
public import DLMF.Coulomb.RhoEtaSeries
public import DLMF.Coulomb.RhoEtaRepresentations
public import DLMF.Coulomb.RhoEtaAsymptotics
public import DLMF.Coulomb.Energy.Basic
public import DLMF.Coulomb.Energy.RegularSolution
public import DLMF.Coulomb.Energy.Properties
public import DLMF.Coulomb.Energy.Connection
public import DLMF.Coulomb.Energy.Recurrence
public import DLMF.Coulomb.Energy.Series
public import DLMF.Coulomb.Energy.Asymptotics

/-!
# Coulomb functions

Coulomb functions of DLMF Chapter 33. The functions of the variables `ρ, η` (DLMF §§33.2–33.13)
are in `DLMF.Coulomb.Basic` and the `RhoEta` modules; the functions `f, h, s, c` of the
variables `r, ε` (DLMF §§33.14–33.21) are in the `Energy` modules.
-/
