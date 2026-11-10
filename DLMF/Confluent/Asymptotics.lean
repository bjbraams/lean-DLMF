/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Confluent.Asymptotics.LargeArgument
public import DLMF.Confluent.Asymptotics.LargeParameter
public import DLMF.Confluent.Asymptotics.RightHalfPlane

/-!
# Asymptotic expansions of confluent hypergeometric functions (DLMF §§13.7, 13.8, 13.19)

Large-argument expansions of `M`, `U` and the Whittaker functions, and large-parameter
expansions of `M` and `U`, following Temme, *Special Functions*, §§7.1–7.2. The sector
expansion 13.7.2 and the limits 13.2.6, 13.2.23, 13.14.20–21 are in
`DLMF.Confluent.AsymptoticConsequences`.
-/
