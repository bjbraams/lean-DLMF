/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Painleve.BacklundDLMF.SecondAndThird
public import DLMF.Painleve.BacklundDLMF.FourthAndFifth
public import DLMF.Painleve.BacklundDLMF.Sixth

/-!
# Bäcklund transformations: DLMF §32.7

The transformations of `PII`–`PVI` in the DLMF normalization. The `PII` transformations come
from the Beals–Wong development (`DLMF.Painleve.Backlund`) through the bridge
`isPainleveIIOn_iff_isPIIOn`. All maps are stated on open sets where their denominators do
not vanish; square roots of parameters (`√(-2β)`, `√(2α)`, …) are replaced by arbitrary
numbers with the right square, so both branches are covered at once.
-/
