/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Hypergeometric.Solutions.InfinityWronskian

public import DLMF.Hypergeometric.Solutions.Equation
public import DLMF.Hypergeometric.Solutions.Logarithmic
public import DLMF.Hypergeometric.Solutions.Connections

/-!
# Local solutions and Wronskians (DLMF §15.10)

This umbrella imports the local solutions of the Gauss equation and their Wronskians
(`DLMF.Hypergeometric.Solutions.Equation`), the logarithmic solutions at integral parameters
(`DLMF.Hypergeometric.Solutions.Logarithmic`) and the connection formulas between `0` and `1`
(`DLMF.Hypergeometric.Solutions.Connections`).

The functions are local solutions, not globally continued functions. Swapping `a, b` supplies
the second solution at infinity. Wronskians together with the equation give fundamental pairs
when the Wronskians are nonzero. The integral-parameter logarithmic pairs are stated with
explicit nonvanishing Wronskians, including empty finite sums. The four connection formulas
between `0` and `1` hold on the overlap of their series disks. The other Kummer representations
are in `DLMF.Hypergeometric.Kummer`; the ordinary solution and its equation are in
`DLMF.Hypergeometric.DiffEq`.
-/
