/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Hypergeometric.Solutions.Equation
public import DLMF.Hypergeometric.Solutions.Logarithmic
public import DLMF.Hypergeometric.Solutions.Connections

/-!
# Local solutions and Wronskians (DLMF §15.10)

The ordinary solution and its ODE are already in `DiffEq`. The functions here
are local solutions, not globally continued functions. Swapping `a,b` supplies
the second solution at infinity. Wronskians plus the ODE give fundamental pairs
when the Wronskians are nonzero. The integral-parameter logarithmic pairs are
stated with explicit nonvanishing Wronskians, including empty finite sums.
The four zero/one connection formulas hold on the overlap of their series disks.
See `Kummer` for the other Kummer representations.
-/
