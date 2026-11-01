/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Combinatorics.PlanePartitions.BoxFormula
public import DLMF.Combinatorics.PlanePartitions.GeneratingFunctions

/-!
# Plane partitions (DLMF §26.12)

Plane partitions as finite down-closed sets of lattice points: counts in boxes for the
symmetry classes of DLMF §26.12(i)–(ii), descending plane partitions, MacMahon's generating
functions, the recurrence and the asymptotic form of `pp(n)`.

## References

* NIST DLMF §26.12.
-/
