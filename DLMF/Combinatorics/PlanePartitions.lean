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

A plane partition is, following DLMF §26.12(i), a finite set `π ⊆ ℕ × ℕ × ℕ` of points with
positive coordinates such that `(r, s, t) ∈ π` implies `B(r, s, t) ⊆ π` (`IsPlanePartition`),
where `B(r, s, t) = [1, r] × [1, s] × [1, t]` (`planeBox`, (26.12.3)); `|π|` is `π.card`. The
array description (weakly decreasing rows and columns) is the equivalent form of §26.12(i),
acquired as `planePartitionCount_eq_card_arrays`. `pp(n)` is `planePartitionCount n`.

Symmetry classes (all inside a box): symmetric (`(h, j, k) ∈ π → (j, h, k) ∈ π`), cyclically
symmetric (`(h, j, k) ∈ π → (j, k, h) ∈ π`), totally symmetric, the complement
`π^c = {(h, j, k) ∈ B | (r-h+1, s-j+1, t-k+1) ∉ π}` (`planeComplement`), self-complementary
(`π = π^c`) and transpose complement (`π^c` equals the transpose of `π`).

Strict shifted and descending plane partitions are lists of rows (`List (List ℕ)`), row `i`
indented by `i` places (`IsStrictShiftedPP`, `IsDescendingPP`). A descending plane partition
"in `B(r, r, r)`" is one with all parts at most `r`.

Counts in boxes are stated as rational numbers (`ℚ`), as DLMF's products are.

Corrections and clarifications (verified by brute force):

* §26.12(i), transpose complement: DLMF says "equal to the reflection through the `(x, y)`-plane
  of its complement". The count (26.12.12) is that of plane partitions whose complement is their
  transpose `(h, j, k) ↦ (j, h, k)` (reflection in the plane `x = y`); with the literal
  reflection `k ↦ t + 1 - k` the counts differ (`r = 1`, `t = 1`: none versus one). The
  transpose reading is acquired.
* (26.12.24): the product must run over `1 ≤ h ≤ j ≤ r`, not `1 ≤ h < j ≤ r`. As printed, for
  `r = 2` the right side is `(1 - q⁴)/(1 - q³)`, not a polynomial, whereas the descending plane
  partitions with parts at most 2 are `∅` and `(2)`, with generating function `1 + q²`; at
  `q = 1` the printed product does not reproduce (26.12.19). The corrected product matches for
  `r ≤ 5`.
* 26.12.27 (decimal values of `ζ(3)`, `ζ'(-1)`) and Table 26.12.1 are numerical and not acquired.

## References

* NIST DLMF §26.12.
-/
