/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Airy.Basic.Properties
public import DLMF.Airy.Basic.Connections
public import DLMF.Airy.Basic.Maclaurin
public import DLMF.Airy.Basic.ModulusPhase
public import DLMF.Airy.Basic.Scorer
public import DLMF.Bessel.SturmZeros

/-!
# Basic properties of Airy functions (DLMF §§9.2, 9.4, 9.8, 9.12)

This module collects the Basic layer of the Airy area together with the Bessel theorem modules
on which the later Airy files build.

## Implementation notes

The results themselves are in `DLMF.Airy.Basic.Properties` (Airy's equation, values at the
origin, the Wronskian, rotations and reality), `DLMF.Airy.Basic.Connections` (DLMF 9.2.2,
9.2.8–9.2.16), `DLMF.Airy.Basic.Maclaurin` (DLMF 9.4.1–9.4.4), `DLMF.Airy.Basic.ModulusPhase`
(the definitions and calculus of DLMF §9.8) and `DLMF.Airy.Basic.Scorer` (DLMF 9.12.1–9.12.7,
9.12.17).
-/
