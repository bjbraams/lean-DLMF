/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Combinatorics.PartitionIdentities.RestrictedProducts
public import DLMF.Combinatorics.PartitionIdentities.GaussIdentity
public import DLMF.Combinatorics.PartitionIdentities.StaircaseAndPentagonal
public import DLMF.Combinatorics.PartitionIdentities.RogersRamanujan

/-!
# Integer partitions: other restrictions (DLMF §26.10)

Partitions into distinct parts, odd parts, parts with prescribed differences and parts from a
given set (DLMF §26.10): generating products, recurrences, the pentagonal identities, the
Rogers–Ramanujan identities, Schur's theorem and the Bessel series for `p(𝒟, n)`.

## References

* NIST DLMF §26.10.
-/
