/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Combinatorics.PartitionIdentities.RestrictedProducts
public import DLMF.Combinatorics.PartitionIdentities.StaircaseAndPentagonal
public import DLMF.Combinatorics.PartitionIdentities.RogersRamanujan

/-!
# Integer partitions: other restrictions (DLMF §26.10)

Restricted partition counts of DLMF §26.10(i), on Mathlib's `Nat.Partition`:

* `p(𝒟, n)` (`partitionCountDistinct`) is `#(Nat.Partition.distincts n)`; `p(𝒪, n)`
  (`partitionCountOdd`) is `#(Nat.Partition.odds n)`;
* `p_m(𝒟, n)` (`partitionCountAtMostDistinct`): at most `m` distinct parts;
  `p_m(≤ k, 𝒟, n)` (`partitionCountAtMostDistinctBoxed`): moreover every part at most `k`;
* `p(𝒟k, n)` (`partitionCountDiff`): any two parts differ by at least `k`
  (`PartsDifferAtLeast`; for `k = 0` all partitions, for `k = 1` distinct parts);
* `p(𝒟'3, n)` (`partitionCountSchur`): parts differ by at least 3 and multiples of 3 by at
  least 6;
* `p(∈ S, n)` (`partitionCountIn`): parts taken from `S`; `A_{j,k}` is `residueSetPM j k`
  and `T = {2, 3, …}` is `setGeTwo`. Combined restrictions are conjunctions.

Euler's identity (26.10.12) is Mathlib's `Nat.Partition.card_odds_eq_card_distincts` (pointer in
`MathlibCoverageB`).

Corrections (all verified by brute force in Python, `n < 40`):

* (26.10.9) as printed, `p_m(𝒟, n) = p_m(𝒟, n - m) + p_{m-1}(𝒟, n)`, is false for the stated
  definition (`m = n = 2`: `1 ≠ 2`). Removing one from each of `m` distinct parts leaves `m` or
  `m - 1` distinct parts, so the correct analogue of (26.9.8) is
  `p_m(𝒟, n) = p_{m-1}(𝒟, n) + p_m(𝒟, n - m) - p_{m-2}(𝒟, n - m)` (equivalently, for exactly
  `m` distinct parts, `q_m(n) = q_m(n - m) + q_{m-1}(n - m)`); this is acquired.
* §26.10(iv): `p(𝒟'3, n) < p(𝒟3, n)` holds for `n = 9` and `n ≥ 15`, not for all `n ≥ 9`:
  `p(𝒟'3, n) = p(𝒟3, n)` for `10 ≤ n ≤ 14` (for instance both are 4 at `n = 10`). The
  corrected range is acquired.
* (26.10.18): the sum over `1 < h ≤ k` would make `A_1(n) = 0` and the leading term of
  (26.10.17) vanish; with `1 ≤ h ≤ k` the series reproduces `p(𝒟, n)` (mpmath, `n ≤ 20`). The
  corrected range is acquired.
* (26.10.7), (26.10.8): the printed sums over `k ≥ 0` with both signs `±` (the `k = 0` term once)
  are sums over `k ∈ ℤ` of the pentagonal numbers `k(3k-1)/2` (Mathlib's `pentagonal`).

## References

* NIST DLMF §26.10.
-/
