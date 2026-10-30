/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Coulomb.Basic
public import DLMF.Coulomb.Basic.AuxiliaryData
public import DLMF.Coulomb.RhoEtaProperties
public import DLMF.Coulomb.RhoEtaLimits
public import DLMF.Coulomb.RhoEtaSeries
public import DLMF.Coulomb.RhoEtaRepresentations
public import DLMF.Coulomb.RhoEtaAsymptotics
public import DLMF.Coulomb.Energy.Basic
public import DLMF.Coulomb.Energy.Q2eRegular
public import DLMF.Coulomb.Energy.Properties
public import DLMF.Coulomb.Energy.Connection
public import DLMF.Coulomb.Energy.Recurrence
public import DLMF.Coulomb.Energy.Series
public import DLMF.Coulomb.Energy.Asymptotics

/-! # Coulomb functions: DLMF Chapter 33

Variables ρ, η (§§33.2–33.13): `Basic` holds the Coulomb functions moved down unchanged from the
Confluent area (namespace `DLMF.Confluent`: `coulombF`, `coulombG`, `coulombHPlus`, …), `Basic.AuxiliaryData` the
further definitions of Chapter 33 (namespace `DLMF.Coulomb`). Variables r, ε (§§33.14–33.21): the
`Energy` modules, with the functions f, h, s, c of §33.14. Ledger: `DLMF33Acquisition.md`.
-/
