# DLMF Chapter 26 acquisition: Combinatorial Analysis

This acquisition covers the definitions, numbered formulas and analytical assertions in prose
of [DLMF Chapter 26](https://dlmf.nist.gov/26), version 1.2.8, checked on 2026-10-25. It was
done in two parts: part A (ACQ26A) covers §§26.1–26.8 (notation, lattice paths, binomial,
multinomial, Catalan, Delannoy, Motzkin, Narayana and Schröder numbers, Bell and Stirling
numbers); part B (ACQ26B) covers §§26.9–26.22 (integer partitions, plane partitions,
compositions, permutations, the twelvefold way, counting techniques, and the excluded
applications and computation sections) in its own sections below. The modules are under
[DLMF/Combinatorics/](DLMF/Combinatorics). Part A's Mathlib pointers are in
[DLMF/Combinatorics/MathlibCoverage.lean](DLMF/Combinatorics/MathlibCoverage.lean); part B's
are in `DLMF/Combinatorics/MathlibCoverageB.lean`.

Most of the objects of §§26.1–26.8 are already Mathlib's: `Nat.choose`, `Nat.multinomial` and
`Multiset.multinomial`, `catalan`, `Nat.largeSchroder` (DLMF's r(n)), `Nat.bell`,
`Nat.stirlingSecond` (DLMF's S(n, k)) and the unsigned `Nat.stirlingFirst` (DLMF's |s(n, k)|).
The new definitions are the signed `DLMF.Combinatorics.signedStirlingFirst` (s(n, k) ∈ ℤ),
`delannoy`, `motzkin`, `narayana` and the lattice-path sets `latticePaths`/`latticePathsFin`.

Part A: §§26.1–26.8 have 95 numbered equations (26.1: 1, 26.3: 12, 26.4: 10, 26.5: 7,
26.6: 14, 26.7: 8, 26.8: 43) and 7 prose items tagged at subsection or section level (26.2,
26.3.i, 26.4.i, 26.5.i, 26.6.i, 26.7.i, 26.8.i), 102 IDs in all. All are covered: 94 by local
tags, and 8 (26.3.E1, E2, E5, E7, E9, 26.4.E1, E9, 26.7.E1) only by `dlmf_upstream` pointers.
Part A lives in `Basic`, `Stirling`, `Bell`, `Binomial`, `Catalan`, `Multinomial` and
`LatticePaths` under `DLMF/Combinatorics/`, with 117 tagged declarations: 7 definitions,
57 proved theorems (1 of them, `signedStirlingFirst_eq_card`, proved from an admission) and
**53 direct admissions** (`grep -c '\bsorry\b'`: Basic 0, Stirling 20, Bell 8, Binomial 2,
Catalan 3, Multinomial 5, LatticePaths 15). `MathlibCoverage` holds 63 `dlmf_upstream`
pointers for 40 IDs.

**Status after proof round 1 (2026-10-25).** The 295 declarations tagged with Chapter 26 IDs are 49 definitions, 150 proved theorems and 96 theorems that still depend on admissions; direct admissions in DLMF/Combinatorics fell from 157 to 95. The per-line statuses in this ledger are regenerated from the compiled dump; the counts below record the acquisition. See REVIEW.md, "Proof round 1 for Chapters 24–27 (2026-10-25)".

**Status after proof round 2 (2026-10-25).** The 295 declarations tagged with Chapter 26 IDs are 49 definitions, 183 proved theorems and 63 theorems that still depend on admissions; direct admissions in DLMF/Combinatorics fell from 95 to 62. See REVIEW.md, "Proof round 2 for Chapters 24–27 (2026-10-25)".

**Status after proof round 3 (2026-10-26).** The 295 declarations tagged with Chapter 26 IDs are 49 definitions, 209 proved theorems and 37 theorems that still depend on admissions; direct admissions in DLMF/Combinatorics fell from 62 to 37. No statement was changed. See REVIEW.md, "Proof round 3 for Chapters 24–27 (2026-10-26)".

## Domains, conventions and source corrections (part A)

- Every numbered formula of §§26.3–26.8 was checked by brute force (exact integer arithmetic,
  and mpmath for the generating functions and asymptotics) over ranges of the indices. The
  findings below are recorded here and in the docstrings; they are not yet in
  [DLMFErrata.md](DLMFErrata.md).
- **26.8.31 is false as printed.** For an entire f with a convergent series, the identity
  `f⁽ᵏ⁾(x)/k! = ∑_{n≥k} s(n, k) Δⁿf(x)/n!` can fail: f(z) = sin(πz), x = 0, k = 1 gives
  f'(0) = π while every Δⁿf(0) vanishes. The counterexample is proved
  (`not_forall_stirling_deriv_eq_fwdDiff_series`); the identity is acquired for polynomials f,
  where the series terminates (`hasSum_signedStirlingFirst_fwdDiff`, admitted).
- Implicit conditions, made explicit in the hypotheses:
  - 26.8.10: the form with k from 1 needs n ≥ 1 (at n = 0 the sum is empty and gives 0 ≠ 1);
    the k-from-0 form holds for all n and is also proved.
  - 26.8.29 needs n ≥ 1 (at n = 0 the printed sum is empty, 0 ≠ 0! = 1).
  - 26.7.3 needs n ≥ 1 (with m ≥ n): at n = 0, m = 2 it gives 1/2 instead of B(0) = 1.
  - 26.7.4: the first Dobiński form `e⁻¹ ∑_{k≥1} kⁿ/k!` fails at n = 0 (gives 1 − e⁻¹); it is
    stated for n ≥ 1, the sum from k = 0 for all n, and the floor form for all n.
  - 26.4.10 needs the total m ≥ 1 (the empty multinomial fails the recurrence).
  - 26.8.5, 26.8.27 and 26.8.33 need k ≤ n.
  - 26.5.1, third and fourth forms (differences of binomial coefficients), need n ≥ 1.
  - 26.3.8 at m = n uses C(−1, 0) = 1, so the inner coefficient is `Ring.choose` over ℤ.
- Natural-number division is never used to state a printed quotient: quotients are stated in
  ℚ or ℝ, or multiplied out in ℕ/ℤ (26.3.6, 26.4.6, 26.5.1, 26.5.4, 26.6.3).
- Generating functions are analytic `HasSum` statements with explicit discs (26.3.4 ‖x‖ < 1,
  26.5.2 0 < |x| < 1/4, 26.6.5 |x| + |y| + |xy| < 1, 26.6.6 |x| < 3 − 2√2, 26.6.7
  0 < |x| < 1/3, 26.6.8 an existential neighbourhood of 0, 26.8.11 |x| < 1/k, 26.8.8
  |x| < 1). Asymptotics use `Asymptotics.IsEquivalent`, `IsBigO` or `Tendsto` at `atTop`.
- Stirling numbers: s(n, k) = (−1)^{n−k}·|s(n, k)| with Mathlib's unsigned `Nat.stirlingFirst`.
  lean-codes' `ascPochhammer_eq_sum_stirlingFirst` and `sum_stirlingSecond_mul_ascPochhammer`
  are the rising-factorial forms of 26.8.7 and 26.8.10 (upstream pointers).
- Lattice paths (§26.2): a path is a list of steps from a finite set of integer step vectors,
  starting at (0, 0) and ending at (m, n) (`latticePaths steps m n`), so path counts are
  `Finset.card`s, decidable for fixed indices; the d-dimensional version is `latticePathsFin`.
  The path-counting characterizations in 26.3(i)–26.6(i) are admitted.

## Numbered formulas and prose items (part A)

## [§26.1 Special Notation](https://dlmf.nist.gov/26.1)

- [26.1.E1](https://dlmf.nist.gov/26.1.E1): [`DLMF.Combinatorics.ascPochhammer_eval_eq_prod_range`](DLMF/Combinatorics/Basic.lean#L46) (proved); [`DLMF.Combinatorics.descPochhammer_eval_eq_prod_range'`](DLMF/Combinatorics/Basic.lean#L54) (proved); [`ascPochhammer`](DLMF/Combinatorics/MathlibCoverage.lean#L42) (Mathlib, upstream pointer); [`descPochhammer_eval_eq_prod_range`](DLMF/Combinatorics/MathlibCoverage.lean#L44) (Mathlib, upstream pointer). Rising and falling factorials as `ascPochhammer`/`descPochhammer` evaluated at x (commutative semiring/ring).

## [§26.2 Basic Definitions](https://dlmf.nist.gov/26.2)

- [26.2](https://dlmf.nist.gov/26.2): [`DLMF.Combinatorics.latticePaths`](DLMF/Combinatorics/Basic.lean#L79) (definition); [`DLMF.Combinatorics.StaysWeaklyAboveDiagonal`](DLMF/Combinatorics/Basic.lean#L116) (definition); [`DLMF.Combinatorics.latticePathsFin`](DLMF/Combinatorics/Basic.lean#L129) (definition); [`Equiv.Perm`](DLMF/Combinatorics/MathlibCoverage.lean#L48) (Mathlib, upstream pointer); [`Equiv.Perm.cycleFactorsFinset`](DLMF/Combinatorics/MathlibCoverage.lean#L49) (Mathlib, upstream pointer); [`Equiv.Perm.partition`](DLMF/Combinatorics/MathlibCoverage.lean#L51) (Mathlib, upstream pointer); [`Finpartition`](DLMF/Combinatorics/MathlibCoverage.lean#L53) (Mathlib, upstream pointer); [`Nat.Partition`](DLMF/Combinatorics/MathlibCoverage.lean#L54) (Mathlib, upstream pointer). Lattice paths as lists of steps from a finite step set (`stepLists`), ending at (m, n); `StaysWeaklyAboveDiagonal` is decidable. Permutations, cycles, set partitions and integer partitions are Mathlib's (upstream pointers). p(n) is the existing `DLMF.Partitions.partitionFunction` (not tagged here; that file belongs to the partition acquisition).

## [§26.3 Lattice Paths: Binomial Coefficients](https://dlmf.nist.gov/26.3)

- [26.3.i](https://dlmf.nist.gov/26.3.i): [`DLMF.Combinatorics.card_latticePaths_unitSteps`](DLMF/Combinatorics/Binomial.lean#L40) (proved); [`DLMF.Combinatorics.card_latticePaths_unitSteps_above`](DLMF/Combinatorics/Binomial.lean#L79) (proved); [`Finset.card_powersetCard`](DLMF/Combinatorics/MathlibCoverage.lean#L57) (Mathlib, upstream pointer). Unit-step lattice paths to (m, n): C(m+n, n) of them, and C(m+n, m) − C(m+n, m−1) staying weakly above y = x for m ≤ n (both admitted; decidable for each fixed m, n). The subset-count characterization is Mathlib `Finset.card_powersetCard`.
- [26.3.E1](https://dlmf.nist.gov/26.3.E1): [`Nat.choose_symm`](DLMF/Combinatorics/MathlibCoverage.lean#L59) (Mathlib, upstream pointer); [`Nat.choose_eq_factorial_div_factorial`](DLMF/Combinatorics/MathlibCoverage.lean#L60) (Mathlib, upstream pointer). Upstream only.
- [26.3.E2](https://dlmf.nist.gov/26.3.E2): [`Nat.choose_eq_zero_of_lt`](DLMF/Combinatorics/MathlibCoverage.lean#L62) (Mathlib, upstream pointer). Upstream only.
- [26.3.E3](https://dlmf.nist.gov/26.3.E3): [`DLMF.Combinatorics.sum_choose_mul_pow`](DLMF/Combinatorics/Binomial.lean#L93) (proved); [`add_pow`](DLMF/Combinatorics/MathlibCoverage.lean#L63) (Mathlib, upstream pointer). Natural-number form of the binomial theorem (Mathlib `add_pow` for general rings).
- [26.3.E4](https://dlmf.nist.gov/26.3.E4): [`DLMF.Combinatorics.hasSum_choose_mul_pow`](DLMF/Combinatorics/Binomial.lean#L101) (proved); [`hasSum_choose_mul_geometric_of_norm_lt_one`](DLMF/Combinatorics/MathlibCoverage.lean#L64) (Mathlib, upstream pointer). Normed field, ‖x‖ < 1; proved from `hasSum_choose_mul_geometric_of_norm_lt_one`.
- [26.3.E5](https://dlmf.nist.gov/26.3.E5): [`Nat.choose_succ_succ'`](DLMF/Combinatorics/MathlibCoverage.lean#L66) (Mathlib, upstream pointer). Upstream only.
- [26.3.E6](https://dlmf.nist.gov/26.3.E6): [`DLMF.Combinatorics.choose_eq_div_mul`](DLMF/Combinatorics/Binomial.lean#L111) (proved); [`Nat.add_one_mul_choose_eq`](DLMF/Combinatorics/MathlibCoverage.lean#L68) (Mathlib, upstream pointer); [`Nat.choose_succ_right_eq`](DLMF/Combinatorics/MathlibCoverage.lean#L70) (Mathlib, upstream pointer). Stated in ℚ with the divisions as printed (n ≥ 1 where required); proved from Mathlib's multiplied forms.
- [26.3.E7](https://dlmf.nist.gov/26.3.E7): [`Nat.sum_Icc_choose`](DLMF/Combinatorics/MathlibCoverage.lean#L72) (Mathlib, upstream pointer). Upstream only.
- [26.3.E8](https://dlmf.nist.gov/26.3.E8): [`DLMF.Combinatorics.choose_eq_sum_ringChoose`](DLMF/Combinatorics/Binomial.lean#L143) (proved). At m = n DLMF uses C(-1, 0) = 1, so the inner coefficient is `Ring.choose` over ℤ; true for all m, n.
- [26.3.E9](https://dlmf.nist.gov/26.3.E9): [`Nat.choose_zero_right`](DLMF/Combinatorics/MathlibCoverage.lean#L73) (Mathlib, upstream pointer); [`Nat.choose_self`](DLMF/Combinatorics/MathlibCoverage.lean#L74) (Mathlib, upstream pointer). Upstream only.
- [26.3.E10](https://dlmf.nist.gov/26.3.E10): [`DLMF.Combinatorics.choose_eq_alternating_sum`](DLMF/Combinatorics/Binomial.lean#L163) (proved). Proved for all m, n (DLMF states it for n ≤ m).
- [26.3.E11](https://dlmf.nist.gov/26.3.E11): [`DLMF.Combinatorics.centralBinom_eq_doubleFactorial`](DLMF/Combinatorics/Binomial.lean#L180) (proved); [`Nat.doubleFactorial_two_mul`](DLMF/Combinatorics/MathlibCoverage.lean#L75) (Mathlib, upstream pointer). Proved via `Nat.doubleFactorial_two_mul` and the double factorial of odd numbers.
- [26.3.E12](https://dlmf.nist.gov/26.3.E12): [`DLMF.Combinatorics.centralBinom_isEquivalent`](DLMF/Combinatorics/Binomial.lean#L230) (proved). `IsEquivalent atTop`: C(2n, n) ~ 4ⁿ/√(πn); proved from Stirling's formula (`Stirling.tendsto_stirlingSeq_sqrt_pi`).

## [§26.4 Lattice Paths: Multinomial Coefficients and Set Partitions](https://dlmf.nist.gov/26.4)

- [26.4.i](https://dlmf.nist.gov/26.4.i): [`DLMF.Combinatorics.card_boxPlacements_eq_multinomial`](DLMF/Combinatorics/Multinomial.lean#L186) (proved); [`DLMF.Combinatorics.card_latticePathsFin_eq_multinomial`](DLMF/Combinatorics/Multinomial.lean#L193) (proved); [`Nat.multinomial_empty`](DLMF/Combinatorics/MathlibCoverage.lean#L79) (Mathlib, upstream pointer); [`Nat.multinomial_singleton`](DLMF/Combinatorics/MathlibCoverage.lean#L80) (Mathlib, upstream pointer). Placements of objects in boxes and lattice paths in k dimensions counted by `Nat.multinomial` (admitted). k = 0 and k = 1 values are upstream.
- [26.4.E1](https://dlmf.nist.gov/26.4.E1): [`Nat.binomial_eq_choose`](DLMF/Combinatorics/MathlibCoverage.lean#L81) (Mathlib, upstream pointer); [`Nat.multinomial_univ_two`](DLMF/Combinatorics/MathlibCoverage.lean#L82) (Mathlib, upstream pointer). Upstream only (k = 2 case of the multinomial).
- [26.4.E2](https://dlmf.nist.gov/26.4.E2): [`DLMF.Combinatorics.multinomial_eq_prod_choose`](DLMF/Combinatorics/Multinomial.lean#L202) (proved); [`Nat.multinomial`](DLMF/Combinatorics/MathlibCoverage.lean#L83) (Mathlib, upstream pointer); [`Nat.multinomial_spec`](DLMF/Combinatorics/MathlibCoverage.lean#L85) (Mathlib, upstream pointer); [`Nat.multinomial_insert`](DLMF/Combinatorics/MathlibCoverage.lean#L86) (Mathlib, upstream pointer). Product of binomial coefficients form admitted; the factorial form is Mathlib's definition (`Nat.multinomial_spec`).
- [26.4.E3](https://dlmf.nist.gov/26.4.E3): [`DLMF.Combinatorics.sum_mul_count_parts`](DLMF/Combinatorics/Multinomial.lean#L229) (proved). For a Mathlib `Nat.Partition`, ∑ j · (count of j) = n.
- [26.4.E4](https://dlmf.nist.gov/26.4.E4): [`DLMF.Combinatorics.sum_count_parts`](DLMF/Combinatorics/Multinomial.lean#L239) (proved). Number of parts as the sum of the counts.
- [26.4.E5](https://dlmf.nist.gov/26.4.E5): [`DLMF.Combinatorics.parts_eq_sum_replicate`](DLMF/Combinatorics/Multinomial.lean#L248) (proved). The partition as the sum of `replicate` blocks.
- [26.4.E6](https://dlmf.nist.gov/26.4.E6): [`DLMF.Combinatorics.multinomial_parts_eq`](DLMF/Combinatorics/Multinomial.lean#L269) (proved); [`Multiset.multinomial`](DLMF/Combinatorics/MathlibCoverage.lean#L88) (Mathlib, upstream pointer). M₁ = n!/∏ (j!)^{a_j} a_j! written in ℕ with multiplied factorials; proved via `Nat.multinomial_spec`.
- [26.4.E7](https://dlmf.nist.gov/26.4.E7): [`DLMF.Combinatorics.card_perm_partition_eq`](DLMF/Combinatorics/Multinomial.lean#L305) (proved); [`Equiv.Perm.card_of_cycleType`](DLMF/Combinatorics/MathlibCoverage.lean#L90) (Mathlib, upstream pointer). M₂: number of permutations of cycle type p (admitted; Mathlib `Equiv.Perm.card_of_cycleType` is the fixed-points-omitted version).
- [26.4.E8](https://dlmf.nist.gov/26.4.E8): [`DLMF.Combinatorics.card_finpartition_blocks_eq`](DLMF/Combinatorics/Multinomial.lean#L412) (proved); [`Multiset.bell_mul_eq`](DLMF/Combinatorics/MathlibCoverage.lean#L92) (Mathlib, upstream pointer). M₃: number of set partitions with block sizes given by p (admitted; Mathlib's counting statement is a TODO).
- [26.4.E9](https://dlmf.nist.gov/26.4.E9): [`Finset.sum_pow_eq_sum_piAntidiag`](DLMF/Combinatorics/MathlibCoverage.lean#L94) (Mathlib, upstream pointer); [`Finset.sum_pow`](DLMF/Combinatorics/MathlibCoverage.lean#L96) (Mathlib, upstream pointer). Upstream only (multinomial theorem).
- [26.4.E10](https://dlmf.nist.gov/26.4.E10): [`DLMF.Combinatorics.multinomial_eq_sum_update`](DLMF/Combinatorics/Multinomial.lean#L513) (proved). Recurrence for the multinomial coefficient; needs m = ∑ nⱼ ≥ 1 (the empty case fails).

## [§26.5 Lattice Paths: Catalan Numbers](https://dlmf.nist.gov/26.5)

- [26.5.i](https://dlmf.nist.gov/26.5.i): [`DLMF.Combinatorics.card_latticePaths_above_eq_catalan`](DLMF/Combinatorics/Catalan.lean#L38) (proved); [`DyckWord.card_dyckWord_semilength_eq_catalan`](DLMF/Combinatorics/MathlibCoverage.lean#L99) (Mathlib, upstream pointer); [`BinaryTree.treesOfNumNodesEq_card_eq_catalan`](DLMF/Combinatorics/MathlibCoverage.lean#L101) (Mathlib, upstream pointer). Catalan number counts lattice paths weakly above the diagonal (admitted for `latticePaths`; Mathlib's Dyck-word and binary-tree counts are upstream pointers).
- [26.5.E1](https://dlmf.nist.gov/26.5.E1): [`DLMF.Combinatorics.catalan_eq_choose_div`](DLMF/Combinatorics/Catalan.lean#L61) (proved); [`DLMF.Combinatorics.catalan_eq_choose_sub`](DLMF/Combinatorics/Catalan.lean#L84) (proved); [`succ_mul_catalan_eq_centralBinom`](DLMF/Combinatorics/MathlibCoverage.lean#L103) (Mathlib, upstream pointer); [`catalan_eq_centralBinom_div`](DLMF/Combinatorics/MathlibCoverage.lean#L104) (Mathlib, upstream pointer). C(n) = C(2n, n)/(n+1) in ℚ and C(2n, n) − C(2n, n−1) (n ≥ 1); the forms with C(2n+1, n) also included.
- [26.5.E2](https://dlmf.nist.gov/26.5.E2): [`DLMF.Combinatorics.hasSum_catalan_mul_pow`](DLMF/Combinatorics/Catalan.lean#L163) (proved); [`PowerSeries.catalanSeries_sq_mul_X_add_one`](DLMF/Combinatorics/MathlibCoverage.lean#L105) (Mathlib, upstream pointer). Analytic generating function for |x| < 1/4, x ≠ 0 (admitted); formal version is Mathlib `PowerSeries.catalanSeries_sq_mul_X_add_one`.
- [26.5.E3](https://dlmf.nist.gov/26.5.E3): [`DLMF.Combinatorics.catalan_succ_eq_sum`](DLMF/Combinatorics/Catalan.lean#L186) (proved); [`catalan_succ`](DLMF/Combinatorics/MathlibCoverage.lean#L107) (Mathlib, upstream pointer); [`catalan_succ'`](DLMF/Combinatorics/MathlibCoverage.lean#L108) (Mathlib, upstream pointer). Segner recurrence over the range; Mathlib's `catalan_succ` is the Fin form.
- [26.5.E4](https://dlmf.nist.gov/26.5.E4): [`DLMF.Combinatorics.catalan_succ_eq_mul`](DLMF/Combinatorics/Catalan.lean#L193) (proved); [`Nat.succ_mul_centralBinom_succ`](DLMF/Combinatorics/MathlibCoverage.lean#L109) (Mathlib, upstream pointer). C(n+1) = 2(2n+1)/(n+2) C(n), stated multiplied in ℕ.
- [26.5.E5](https://dlmf.nist.gov/26.5.E5): [`DLMF.Combinatorics.catalan_succ_eq_sum_touchard`](DLMF/Combinatorics/Catalan.lean#L214) (proved). Touchard's identity (admitted).
- [26.5.E6](https://dlmf.nist.gov/26.5.E6): [`DLMF.Combinatorics.catalan_isEquivalent`](DLMF/Combinatorics/Catalan.lean#L227) (proved). `IsEquivalent atTop`: C(n) ~ 4ⁿ/(√π n^{3/2}); proved from 26.3.E12.
- [26.5.E7](https://dlmf.nist.gov/26.5.E7): [`DLMF.Combinatorics.tendsto_catalan_succ_div`](DLMF/Combinatorics/Catalan.lean#L252) (proved). C(n+1)/C(n) → 4.

## [§26.6 Other Lattice Path Numbers](https://dlmf.nist.gov/26.6)

- [26.6.i](https://dlmf.nist.gov/26.6.i): [`DLMF.Combinatorics.delannoy`](DLMF/Combinatorics/LatticePaths.lean#L44) (definition); [`DLMF.Combinatorics.motzkin`](DLMF/Combinatorics/LatticePaths.lean#L63) (definition); [`DLMF.Combinatorics.narayana`](DLMF/Combinatorics/LatticePaths.lean#L90) (definition); [`DLMF.Combinatorics.card_latticePaths_eq_delannoy`](DLMF/Combinatorics/LatticePaths.lean#L134) (proved); [`DLMF.Combinatorics.card_latticePaths_above_eq_motzkin`](DLMF/Combinatorics/LatticePaths.lean#L167) (admitted); [`DLMF.Combinatorics.card_latticePaths_peaks_eq_narayana`](DLMF/Combinatorics/LatticePaths.lean#L177) (admitted); [`DLMF.Combinatorics.card_latticePaths_above_eq_largeSchroder`](DLMF/Combinatorics/LatticePaths.lean#L187) (admitted); [`Nat.largeSchroder`](DLMF/Combinatorics/MathlibCoverage.lean#L113) (Mathlib, upstream pointer). Delannoy D(m, n), Motzkin M(n) and Narayana N(n, k) are new definitions (recurrence, recurrence, closed form with N(n, 0) = 0); r(n) is Mathlib `Nat.largeSchroder`. The path-count characterizations are admitted.
- [26.6.E1](https://dlmf.nist.gov/26.6.E1): [`DLMF.Combinatorics.delannoy_eq_sum`](DLMF/Combinatorics/LatticePaths.lean#L503) (proved). Both closed forms of D(m, n) admitted.
- [26.6.E2](https://dlmf.nist.gov/26.6.E2): [`DLMF.Combinatorics.motzkin_eq_sum`](DLMF/Combinatorics/LatticePaths.lean#L510) (proved). Motzkin closed form (admitted).
- [26.6.E3](https://dlmf.nist.gov/26.6.E3): [`DLMF.Combinatorics.narayana_eq`](DLMF/Combinatorics/LatticePaths.lean#L122) (proved). Narayana closed form N(n, k) = C(n, k)C(n, k−1)/n, proved in ℕ (divisibility proved).
- [26.6.E4](https://dlmf.nist.gov/26.6.E4): [`DLMF.Combinatorics.largeSchroder_eq_delannoy_sub`](DLMF/Combinatorics/LatticePaths.lean#L528) (proved). r(n) = D(n, n) − D(n+1, n−1), n ≥ 1 (admitted).
- [26.6.E5](https://dlmf.nist.gov/26.6.E5): [`DLMF.Combinatorics.hasSum_delannoy`](DLMF/Combinatorics/LatticePaths.lean#L575) (proved). Bivariate Delannoy generating function, |x| + |y| + |xy| < 1 (admitted).
- [26.6.E6](https://dlmf.nist.gov/26.6.E6): [`DLMF.Combinatorics.hasSum_delannoy_diag`](DLMF/Combinatorics/LatticePaths.lean#L635) (proved). Diagonal Delannoy generating function 1/√(1 − 6x + x²), |x| < 3 − 2√2 (admitted).
- [26.6.E7](https://dlmf.nist.gov/26.6.E7): [`DLMF.Combinatorics.hasSum_motzkin`](DLMF/Combinatorics/LatticePaths.lean#L672) (proved). Motzkin generating function, 0 < |x| < 1/3 (admitted).
- [26.6.E8](https://dlmf.nist.gov/26.6.E8): [`DLMF.Combinatorics.hasSum_narayana`](DLMF/Combinatorics/LatticePaths.lean#L713) (admitted). Narayana generating function in a neighbourhood of 0 (stated with an existential radius; admitted).
- [26.6.E9](https://dlmf.nist.gov/26.6.E9): [`DLMF.Combinatorics.hasSum_largeSchroder`](DLMF/Combinatorics/LatticePaths.lean#L721) (proved). Large Schröder generating function (admitted).
- [26.6.E10](https://dlmf.nist.gov/26.6.E10): [`DLMF.Combinatorics.delannoy_succ_succ`](DLMF/Combinatorics/LatticePaths.lean#L56) (proved). D(m+1, n+1) = D(m, n+1) + D(m+1, n) + D(m, n): the defining recurrence.
- [26.6.E11](https://dlmf.nist.gov/26.6.E11): [`DLMF.Combinatorics.motzkin_eq`](DLMF/Combinatorics/LatticePaths.lean#L73) (proved). Motzkin recurrence, the defining equation.
- [26.6.E12](https://dlmf.nist.gov/26.6.E12): [`DLMF.Combinatorics.catalan_eq_sum_narayana`](DLMF/Combinatorics/LatticePaths.lean#L763) (proved). C(n) = ∑ₖ N(n, k) (admitted).
- [26.6.E13](https://dlmf.nist.gov/26.6.E13): [`DLMF.Combinatorics.motzkin_eq_sum_catalan`](DLMF/Combinatorics/LatticePaths.lean#L772) (proved). M(n) = ∑ C(n, 2k) C(k) (admitted).
- [26.6.E14](https://dlmf.nist.gov/26.6.E14): [`DLMF.Combinatorics.catalan_eq_sum_motzkin`](DLMF/Combinatorics/LatticePaths.lean#L778) (proved). C(n+1) = ∑ C(n, k) M(k) (admitted).

## [§26.7 Set Partitions: Bell Numbers](https://dlmf.nist.gov/26.7)

- [26.7.i](https://dlmf.nist.gov/26.7.i): [`DLMF.Combinatorics.card_finpartition_eq_bell`](DLMF/Combinatorics/Bell.lean#L68) (proved); [`Nat.bell`](DLMF/Combinatorics/MathlibCoverage.lean#L117) (Mathlib, upstream pointer); [`Nat.bell_eq_sum_partition`](DLMF/Combinatorics/MathlibCoverage.lean#L119) (Mathlib, upstream pointer). B(n) counts set partitions of an n-set (admitted; Mathlib's own statement is a TODO). B(n) is Mathlib `Nat.bell`.
- [26.7.E1](https://dlmf.nist.gov/26.7.E1): [`Nat.bell_zero`](DLMF/Combinatorics/MathlibCoverage.lean#L121) (Mathlib, upstream pointer). Upstream only (`Nat.bell_zero`).
- [26.7.E2](https://dlmf.nist.gov/26.7.E2): [`DLMF.Combinatorics.bell_eq_sum_stirlingSecond`](DLMF/Combinatorics/Bell.lean#L46) (proved). B(n) = ∑ S(n, k); proved from the recurrences by strong induction.
- [26.7.E3](https://dlmf.nist.gov/26.7.E3): [`DLMF.Combinatorics.bell_eq_sum_mul_sum`](DLMF/Combinatorics/Bell.lean#L134) (proved). Valid for n ≥ 1 and m ≥ n (fails at n = 0, m ≥ 2: gives 1/2 for m = 2); admitted.
- [26.7.E4](https://dlmf.nist.gov/26.7.E4): [`DLMF.Combinatorics.hasSum_pow_div_factorial`](DLMF/Combinatorics/Bell.lean#L145) (proved); [`DLMF.Combinatorics.bell_eq_exp_neg_one_mul_tsum`](DLMF/Combinatorics/Bell.lean#L162) (proved); [`DLMF.Combinatorics.bell_eq_one_add_floor`](DLMF/Combinatorics/Bell.lean#L196) (proved). Dobiński: the series form with k from 0 for all n, the e⁻¹ form for n ≥ 1 (fails at n = 0, gives 1 − e⁻¹), and the floor form for all n (admitted).
- [26.7.E5](https://dlmf.nist.gov/26.7.E5): [`DLMF.Combinatorics.hasSum_bell_div_factorial`](DLMF/Combinatorics/Bell.lean#L258) (proved). Exponential generating function exp(eˣ − 1), all complex x (admitted).
- [26.7.E6](https://dlmf.nist.gov/26.7.E6): [`DLMF.Combinatorics.bell_succ_eq_sum`](DLMF/Combinatorics/Bell.lean#L36) (proved); [`Nat.bell_succ`](DLMF/Combinatorics/MathlibCoverage.lean#L122) (Mathlib, upstream pointer); [`Nat.bell_succ'`](DLMF/Combinatorics/MathlibCoverage.lean#L123) (Mathlib, upstream pointer). B(n+1) = ∑ C(n, k) B(k); proved from Mathlib's `Nat.bell_succ`.
- [26.7.E7](https://dlmf.nist.gov/26.7.E7): [`DLMF.Combinatorics.bell_isBigO`](DLMF/Combinatorics/Bell.lean#L307) (admitted). The relative error is O((ln n)^{1/2} n^{−1/2}), with N(n) supplied by hypothesis as the solution of 26.7.8 (admitted).
- [26.7.E8](https://dlmf.nist.gov/26.7.E8): [`DLMF.Combinatorics.existsUnique_mul_log_eq`](DLMF/Combinatorics/Bell.lean#L274) (proved). For real x ≥ 0 there is a unique N ≥ 1 with N ln N = x (admitted; IVT plus monotonicity).

## [§26.8 Set Partitions: Stirling Numbers](https://dlmf.nist.gov/26.8)

- [26.8.i](https://dlmf.nist.gov/26.8.i): [`DLMF.Combinatorics.signedStirlingFirst`](DLMF/Combinatorics/Stirling.lean#L72) (definition); [`DLMF.Combinatorics.card_perm_numCycles`](DLMF/Combinatorics/Stirling.lean#L1883) (proved); [`DLMF.Combinatorics.signedStirlingFirst_eq_card`](DLMF/Combinatorics/Stirling.lean#L1892) (proved); [`DLMF.Combinatorics.card_finpartition_eq_stirlingSecond`](DLMF/Combinatorics/Stirling.lean#L1900) (proved); [`Nat.stirlingFirst`](DLMF/Combinatorics/MathlibCoverage.lean#L126) (Mathlib, upstream pointer); [`Nat.stirlingSecond`](DLMF/Combinatorics/MathlibCoverage.lean#L128) (Mathlib, upstream pointer). s(n, k) is the new `signedStirlingFirst` (ℤ-valued), S(n, k) is Mathlib `Nat.stirlingSecond`. Cycle and set-partition counts admitted; `signedStirlingFirst_eq_card` is proved from the admitted cycle count.
- [26.8.E1](https://dlmf.nist.gov/26.8.E1): [`DLMF.Combinatorics.signedStirlingFirst_self`](DLMF/Combinatorics/Stirling.lean#L119) (proved); [`Nat.stirlingFirst_self`](DLMF/Combinatorics/MathlibCoverage.lean#L129) (Mathlib, upstream pointer).
- [26.8.E2](https://dlmf.nist.gov/26.8.E2): [`DLMF.Combinatorics.signedStirlingFirst_one`](DLMF/Combinatorics/Stirling.lean#L124) (proved).
- [26.8.E3](https://dlmf.nist.gov/26.8.E3): [`DLMF.Combinatorics.neg_one_pow_mul_signedStirlingFirst_eq_esymm`](DLMF/Combinatorics/Stirling.lean#L189) (proved). Elementary symmetric form (admitted).
- [26.8.E4](https://dlmf.nist.gov/26.8.E4): [`DLMF.Combinatorics.stirlingSecond_self'`](DLMF/Combinatorics/Stirling.lean#L198) (proved); [`Nat.stirlingSecond_self`](DLMF/Combinatorics/MathlibCoverage.lean#L130) (Mathlib, upstream pointer).
- [26.8.E5](https://dlmf.nist.gov/26.8.E5): [`DLMF.Combinatorics.stirlingSecond_eq_sum_antidiagonalTuple`](DLMF/Combinatorics/Stirling.lean#L272) (proved). Sum over compositions (admitted); needs k ≤ n.
- [26.8.E6](https://dlmf.nist.gov/26.8.E6): [`DLMF.Combinatorics.stirlingSecond_eq_sum`](DLMF/Combinatorics/Stirling.lean#L326) (proved). Explicit alternating sum (admitted).
- [26.8.E7](https://dlmf.nist.gov/26.8.E7): [`DLMF.Combinatorics.sum_signedStirlingFirst_mul_pow`](DLMF/Combinatorics/Stirling.lean#L360) (proved); [`ascPochhammer_eq_sum_stirlingFirst`](DLMF/Combinatorics/MathlibCoverage.lean#L131) (Mathlib, upstream pointer). Falling factorial expansion; stated in ℤ[X] as `descPochhammer`.
- [26.8.E8](https://dlmf.nist.gov/26.8.E8): [`DLMF.Combinatorics.hasSum_signedStirlingFirst_div_factorial`](DLMF/Combinatorics/Stirling.lean#L603) (proved). EGF ((ln(1+x))^k/k!), |x| < 1 (admitted).
- [26.8.E9](https://dlmf.nist.gov/26.8.E9): [`DLMF.Combinatorics.hasSum_signedStirlingFirst_bivariate`](DLMF/Combinatorics/Stirling.lean#L610) (proved). Bivariate generating function (admitted).
- [26.8.E10](https://dlmf.nist.gov/26.8.E10): [`DLMF.Combinatorics.sum_range_stirlingSecond_mul_ascPochhammer`](DLMF/Combinatorics/Stirling.lean#L388) (proved); [`DLMF.Combinatorics.sum_Icc_stirlingSecond_mul_ascPochhammer`](DLMF/Combinatorics/Stirling.lean#L398) (proved); [`Nat.pow_eq_sum_stirlingSecond_mul_descFactorial`](DLMF/Combinatorics/MathlibCoverage.lean#L133) (Mathlib, upstream pointer); [`sum_stirlingSecond_mul_ascPochhammer`](DLMF/Combinatorics/MathlibCoverage.lean#L135) (Mathlib, upstream pointer). Printed with k from 1, the identity needs n ≥ 1 (at n = 0 the sum is empty: 0 ≠ 1); the k-from-0 form holds for all n. Any commutative ring.
- [26.8.E11](https://dlmf.nist.gov/26.8.E11): [`DLMF.Combinatorics.hasSum_stirlingSecond_mul_pow`](DLMF/Combinatorics/Stirling.lean#L636) (proved). Ordinary generating function, |x| < 1/k (admitted).
- [26.8.E12](https://dlmf.nist.gov/26.8.E12): [`DLMF.Combinatorics.hasSum_stirlingSecond_div_factorial`](DLMF/Combinatorics/Stirling.lean#L686) (proved). EGF (eˣ − 1)^k/k! (admitted).
- [26.8.E13](https://dlmf.nist.gov/26.8.E13): [`DLMF.Combinatorics.hasSum_stirlingSecond_bivariate`](DLMF/Combinatorics/Stirling.lean#L713) (proved). Bivariate EGF (admitted).
- [26.8.E14](https://dlmf.nist.gov/26.8.E14): [`DLMF.Combinatorics.signedStirlingFirst_zero_right`](DLMF/Combinatorics/Stirling.lean#L749) (proved); [`DLMF.Combinatorics.signedStirlingFirst_one_right`](DLMF/Combinatorics/Stirling.lean#L755) (proved); [`Nat.stirlingFirst_succ_zero`](DLMF/Combinatorics/MathlibCoverage.lean#L137) (Mathlib, upstream pointer); [`Nat.stirlingFirst_one_right`](DLMF/Combinatorics/MathlibCoverage.lean#L138) (Mathlib, upstream pointer).
- [26.8.E15](https://dlmf.nist.gov/26.8.E15): [`DLMF.Combinatorics.signedStirlingFirst_two_right`](DLMF/Combinatorics/Stirling.lean#L774) (proved). s(n, 2) = (−1)ⁿ (n−1)! H_{n−1}, n ≥ 1.
- [26.8.E16](https://dlmf.nist.gov/26.8.E16): [`DLMF.Combinatorics.neg_signedStirlingFirst_pred_self`](DLMF/Combinatorics/Stirling.lean#L787) (proved); [`Nat.stirlingFirst_succ_self_left`](DLMF/Combinatorics/MathlibCoverage.lean#L140) (Mathlib, upstream pointer); [`Nat.stirlingSecond_succ_self_left`](DLMF/Combinatorics/MathlibCoverage.lean#L142) (Mathlib, upstream pointer). Index form n ≥ 1.
- [26.8.E17](https://dlmf.nist.gov/26.8.E17): [`DLMF.Combinatorics.stirlingSecond_zero_one_right`](DLMF/Combinatorics/Stirling.lean#L797) (proved); [`DLMF.Combinatorics.stirlingSecond_two_right`](DLMF/Combinatorics/Stirling.lean#L804) (proved); [`Nat.stirlingSecond_succ_zero`](DLMF/Combinatorics/MathlibCoverage.lean#L143) (Mathlib, upstream pointer); [`Nat.stirlingSecond_one_right`](DLMF/Combinatorics/MathlibCoverage.lean#L144) (Mathlib, upstream pointer).
- [26.8.E18](https://dlmf.nist.gov/26.8.E18): [`DLMF.Combinatorics.signedStirlingFirst_succ_succ`](DLMF/Combinatorics/Stirling.lean#L95) (proved); [`DLMF.Combinatorics.signedStirlingFirst_succ_zero'`](DLMF/Combinatorics/Stirling.lean#L111) (proved); [`Nat.stirlingFirst_succ_succ`](DLMF/Combinatorics/MathlibCoverage.lean#L145) (Mathlib, upstream pointer).
- [26.8.E19](https://dlmf.nist.gov/26.8.E19): [`DLMF.Combinatorics.choose_mul_signedStirlingFirst`](DLMF/Combinatorics/Stirling.lean#L834) (proved). Binomial convolution (admitted).
- [26.8.E20](https://dlmf.nist.gov/26.8.E20): [`DLMF.Combinatorics.signedStirlingFirst_succ_succ_eq_sum`](DLMF/Combinatorics/Stirling.lean#L929) (proved).
- [26.8.E21](https://dlmf.nist.gov/26.8.E21): [`DLMF.Combinatorics.signedStirlingFirst_add_succ`](DLMF/Combinatorics/Stirling.lean#L943) (proved).
- [26.8.E22](https://dlmf.nist.gov/26.8.E22): [`DLMF.Combinatorics.stirlingSecond_succ_succ'`](DLMF/Combinatorics/Stirling.lean#L955) (proved); [`Nat.stirlingSecond_succ_succ`](DLMF/Combinatorics/MathlibCoverage.lean#L147) (Mathlib, upstream pointer).
- [26.8.E23](https://dlmf.nist.gov/26.8.E23): [`DLMF.Combinatorics.choose_mul_stirlingSecond`](DLMF/Combinatorics/Stirling.lean#L1045) (proved). Binomial convolution for S (admitted).
- [26.8.E24](https://dlmf.nist.gov/26.8.E24): [`DLMF.Combinatorics.stirlingSecond_eq_sum_pow`](DLMF/Combinatorics/Stirling.lean#L1076) (proved).
- [26.8.E25](https://dlmf.nist.gov/26.8.E25): [`DLMF.Combinatorics.stirlingSecond_succ_succ_eq_sum`](DLMF/Combinatorics/Stirling.lean#L1121) (proved).
- [26.8.E26](https://dlmf.nist.gov/26.8.E26): [`DLMF.Combinatorics.stirlingSecond_add_succ`](DLMF/Combinatorics/Stirling.lean#L1133) (proved).
- [26.8.E27](https://dlmf.nist.gov/26.8.E27): [`DLMF.Combinatorics.signedStirlingFirst_sub_eq_sum`](DLMF/Combinatorics/Stirling.lean#L1158) (admitted). Needs k ≤ n (admitted).
- [26.8.E28](https://dlmf.nist.gov/26.8.E28): [`DLMF.Combinatorics.sum_signedStirlingFirst`](DLMF/Combinatorics/Stirling.lean#L1167) (proved).
- [26.8.E29](https://dlmf.nist.gov/26.8.E29): [`DLMF.Combinatorics.sum_neg_one_pow_mul_signedStirlingFirst`](DLMF/Combinatorics/Stirling.lean#L1184) (proved). Needs n ≥ 1 (fails at n = 0).
- [26.8.E30](https://dlmf.nist.gov/26.8.E30): [`DLMF.Combinatorics.sum_signedStirlingFirst_succ_mul_pow`](DLMF/Combinatorics/Stirling.lean#L1201) (proved).
- [26.8.E31](https://dlmf.nist.gov/26.8.E31): [`DLMF.Combinatorics.not_forall_stirling_deriv_eq_fwdDiff_series`](DLMF/Combinatorics/Stirling.lean#L1221) (proved); [`DLMF.Combinatorics.hasSum_signedStirlingFirst_fwdDiff`](DLMF/Combinatorics/Stirling.lean#L1250) (proved). **False as printed** for general analytic f (counterexample f(z) = sin(πz), x = 0, k = 1 proved). Acquired for polynomials (admitted).
- [26.8.E32](https://dlmf.nist.gov/26.8.E32): [`DLMF.Combinatorics.fwdDiff_one_apply`](DLMF/Combinatorics/Stirling.lean#L1311) (proved); [`fwdDiff`](DLMF/Combinatorics/MathlibCoverage.lean#L148) (Mathlib, upstream pointer).
- [26.8.E33](https://dlmf.nist.gov/26.8.E33): [`DLMF.Combinatorics.stirlingSecond_sub_eq_sum`](DLMF/Combinatorics/Stirling.lean#L1316) (admitted). Needs k ≤ n (admitted).
- [26.8.E34](https://dlmf.nist.gov/26.8.E34): [`DLMF.Combinatorics.sum_pow_mul_X_pow_eq`](DLMF/Combinatorics/Stirling.lean#L1325) (proved); [`hasSum_pow_mul_geometric_of_norm_lt_one'`](DLMF/Combinatorics/MathlibCoverage.lean#L149) (Mathlib, upstream pointer). Polynomial identity in R[X], with (1 − x^{n+1})/(1 − x) read as 1 + x + ⋯ + xⁿ (its removable value n + 1 at x = 1).
- [26.8.E35](https://dlmf.nist.gov/26.8.E35): [`DLMF.Combinatorics.sum_range_pow_eq_sum_stirlingSecond`](DLMF/Combinatorics/Stirling.lean#L1346) (proved).
- [26.8.E36](https://dlmf.nist.gov/26.8.E36): [`DLMF.Combinatorics.sum_neg_one_pow_mul_factorial_mul_stirlingSecond`](DLMF/Combinatorics/Stirling.lean#L1363) (proved).
- [26.8.E37](https://dlmf.nist.gov/26.8.E37): [`DLMF.Combinatorics.hasSum_stirlingSecond_iteratedDeriv`](DLMF/Combinatorics/Stirling.lean#L1378) (proved). Entire f: admitted (route: Taylor expansion plus 26.8.6).
- [26.8.E38](https://dlmf.nist.gov/26.8.E38): [`DLMF.Combinatorics.stirlingMatrix_inv`](DLMF/Combinatorics/Stirling.lean#L1469) (proved). The Stirling matrices are mutually inverse.
- [26.8.E39](https://dlmf.nist.gov/26.8.E39): [`DLMF.Combinatorics.sum_signedStirlingFirst_mul_stirlingSecond`](DLMF/Combinatorics/Stirling.lean#L1409) (proved); [`DLMF.Combinatorics.sum_signedStirlingFirst_mul_stirlingSecond'`](DLMF/Combinatorics/Stirling.lean#L1449) (proved). Both orthogonality relations.
- [26.8.E40](https://dlmf.nist.gov/26.8.E40): [`DLMF.Combinatorics.tendsto_signedStirlingFirst_div`](DLMF/Combinatorics/Stirling.lean#L1508) (admitted). Admitted.
- [26.8.E41](https://dlmf.nist.gov/26.8.E41): [`DLMF.Combinatorics.signedStirlingFirst_add_isEquivalent`](DLMF/Combinatorics/Stirling.lean#L1637) (proved). Admitted.
- [26.8.E42](https://dlmf.nist.gov/26.8.E42): [`DLMF.Combinatorics.stirlingSecond_isEquivalent`](DLMF/Combinatorics/Stirling.lean#L1648) (proved). Admitted.
- [26.8.E43](https://dlmf.nist.gov/26.8.E43): [`DLMF.Combinatorics.tendsto_stirlingSecond_add_div`](DLMF/Combinatorics/Stirling.lean#L1684) (admitted). Admitted.

## Prose, informal and excluded items (part A)

- §26.1 (notation): the notation table (26.1.p3, its rows) and the remarks 26.1.Px1.p2–p3
  are notational; the rising and falling factorials are 26.1.E1. The empty-product and
  empty-set conventions are those of Lean's `Finset.prod`/`Finset.card`.
- §26.2 (basic definitions): permutations, cycles, set partitions, integer partitions and
  lattice paths are acquired under the section tag `26.2` and the Mathlib pointers.
  p(n) is the existing `DLMF.Partitions.partitionFunction`. Table 26.2.1 (values of p(n)):
  excluded: numerical.
- Tables 26.3.1–26.3.2, 26.4.1 (the coefficients M₁, M₂, M₃ are acquired as 26.4.6–26.4.8),
  26.5.1, 26.6.1–26.6.4, 26.7.1, 26.8.1–26.8.2: excluded: numerical.
- The prose paragraphs introducing each formula (26.3.i.p1–p3, 26.4.i.p1–p2, 26.5.i.p1–p2,
  26.6.Px1–Px4, 26.7.i.p1–p4, 26.8.i.p1–p3 and the others) are acquired with the formulas or
  under the subsection tags; the lattice-path and set-partition counts are admitted theorems.
- §26.8(vi) (relations to Bernoulli numbers) is a cross-reference to §24.15(iii) and has no
  statement of its own.
- 26.8.vii.p4–p6 are bibliographic pointers to further asymptotic results (excluded:
  reference only).

## Validation (part A)

- Strict check: `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false` on each of the
  eight files gives no errors; the only warnings are `declaration uses 'sorry'` on the
  admitted DLMF statements. `lake build` of the eight modules succeeds.
- No axioms, `native_decide` or `sorry` in definitions or helper lemmas. `#print axioms` on a
  sample of proved theorems (`centralBinom_isEquivalent`, `catalan_isEquivalent`,
  `sum_signedStirlingFirst_mul_stirlingSecond'`, `stirlingMatrix_inv`,
  `multinomial_eq_sum_update`, `bell_eq_sum_stirlingSecond`,
  `not_forall_stirling_deriv_eq_fwdDiff_series`) shows only `propext`, `Classical.choice` and
  `Quot.sound`.
- `#eval` checks of the lattice-path definitions agree with the DLMF values: 6 unit-step paths
  to (2, 2), 5 Catalan paths, 22 Schröder paths, 9 Motzkin paths, multinomial 12.
- Numerical brute-force verification of every numbered formula in §§26.3–26.8 (see the
  corrections above).

## Numbered formulas and prose items (part B: §§26.9–26.18)

Part B covers §§26.9–26.18 in the modules `DLMF/Combinatorics/RestrictedPartitions.lean`,
`PartitionIdentities.lean`, `Compositions.lean`, `PlanePartitions.lean`, `Permutations.lean`,
`MultisetPermutations.lean`, `TwelvefoldWay.lean`, `CountingTechniques.lean` and the upstream
pointers in `MathlibCoverageB.lean`. Excluded: §§26.19–26.20 (excluded: application) and
§§26.21–26.22 (excluded: computation).

Part B: §§26.9–26.18 have 106 numbered equations (26.9: 10, 26.10: 20, 26.11: 7, 26.12: 27,
26.13: 6, 26.14: 16, 26.15: 13, 26.16: 3, 26.18: 4) and five tables (26.9.T1, 26.10.T1,
26.12.T1, 26.14.T1, 26.17.T1). Of the equations, 100 carry local tags, 4 are covered only by
`dlmf_upstream` pointers (26.10.E12, 26.11.E5, 26.11.E7, 26.18.E1), 26.13.E1 is notation and
26.12.E27 is excluded: numerical. Tables 26.12.T1, 26.14.T1 (partially) and 26.17.T1 (all twelve
entries) are acquired. Prose is tagged at 11 subsection or section IDs. The 177 tagged
declarations are 42 definitions, 28 proved theorems, 4 proved from admissions and 103 admitted
theorems; `MathlibCoverageB` holds 19 `dlmf_upstream` pointers.

Conventions:

- Partitions are Mathlib's `Nat.Partition n`; `p(n)` is the existing
  `DLMF.Partitions.partitionFunction`; restricted counts (`p_k(n)`, `p(𝒟, n)`, `p(∈S, n)`, …) are
  cardinalities of filtered `Finset (Nat.Partition n)`.
- `q`-series are over `ℂ` with `|q| < 1` as `HasSum`/`HasProd`; Gaussian coefficients are the
  existing `DLMF.QSeries.qBinom`.
- Permutations are `Equiv.Perm (Fin n)` with `0`-based values; word statistics (`inv`, `des`,
  `maj`) are defined on words `Fin n → ℕ` and specialized to permutations.
- Rook and hit numbers are defined for boards `B ⊆ Fin n × Fin n`.
- Recurrences with DLMF's conventions `p(m) = 0` for `m < 0` are stated with the cases explicit
  or with natural subtraction guarded by hypotheses.

## [§26.9 Integer Partitions: Restricted Number and Part Size](https://dlmf.nist.gov/26.9)

- [26.9.E1](https://dlmf.nist.gov/26.9.E1): [`DLMF.Combinatorics.partitionCountAtMostParts_of_le`](DLMF/Combinatorics/RestrictedPartitions.lean#L69) (proved).
- [26.9.E2](https://dlmf.nist.gov/26.9.E2): [`DLMF.Combinatorics.partitionCountAtMostParts_zero`](DLMF/Combinatorics/RestrictedPartitions.lean#L76) (proved).
- [26.9.E3](https://dlmf.nist.gov/26.9.E3): [`DLMF.Combinatorics.partitionCountAtMostParts_one`](DLMF/Combinatorics/RestrictedPartitions.lean#L88) (proved); [`DLMF.Combinatorics.partitionCountAtMostParts_two`](DLMF/Combinatorics/RestrictedPartitions.lean#L211) (proved); [`DLMF.Combinatorics.partitionCountAtMostParts_three`](DLMF/Combinatorics/RestrictedPartitions.lean#L221) (proved). `p_1` proved; `p_2`, `p_3` admitted (natural-number floor division).
- [26.9.E4](https://dlmf.nist.gov/26.9.E4): [`DLMF.Combinatorics.qBinom_eq_prod`](DLMF/Combinatorics/RestrictedPartitions.lean#L537) (proved). Proved for `n ≤ m` and `q^j ≠ 1` (`1 ≤ j ≤ n`), from the polynomial identity `[m n]_q (q;q)_n = ∏_{i<n}(1 - q^{m-i})` (`c26b_qBinom_mul_qPochhammer`); `qBinom` is the existing Gaussian coefficient of DLMF/QSeries/QBinomial.lean.
- [26.9.E5](https://dlmf.nist.gov/26.9.E5): [`DLMF.Combinatorics.hasSum_partitionCountAtMostParts`](DLMF/Combinatorics/RestrictedPartitions.lean#L615) (proved); [`DLMF.Combinatorics.hasSum_qBinom_mul_pow`](DLMF/Combinatorics/RestrictedPartitions.lean#L708) (proved). `|q| < 1`; the second equality is the series with the `m = 0` term `1`.
- [26.9.E6](https://dlmf.nist.gov/26.9.E6): [`DLMF.Combinatorics.hasSum_partitionCountBoxed`](DLMF/Combinatorics/RestrictedPartitions.lean#L727) (proved). Finite sum; every `q ∈ ℂ` (stronger than DLMF).
- [26.9.E7](https://dlmf.nist.gov/26.9.E7): [`DLMF.Combinatorics.hasSum_partitionCountBoxed_two`](DLMF/Combinatorics/RestrictedPartitions.lean#L790) (proved); [`DLMF.Combinatorics.hasSum_qBinom_mul_pow_x`](DLMF/Combinatorics/RestrictedPartitions.lean#L833) (proved). **Corrected** (DLMF error): the printed sum over `m, n` is a sum over `k, n` (the summand and both right sides have a fixed `m`), and the printed condition `|xq| < 1` is insufficient (the `n = 0` terms give `∑_k x^k`): acquired for `|q| < 1`, `|x| < 1`. Checked numerically (`q = 0.3`, `x = 0.6`, `m = 2`).
- [26.9.E8](https://dlmf.nist.gov/26.9.E8): [`DLMF.Combinatorics.partitionCountAtMostParts_succ`](DLMF/Combinatorics/RestrictedPartitions.lean#L840) (proved). `k ≥ 1`; DLMF's convention `p_k(n - k) = 0` for `n < k` made explicit.
- [26.9.E9](https://dlmf.nist.gov/26.9.E9): [`DLMF.Combinatorics.partitionCountAtMostParts_recurrence`](DLMF/Combinatorics/RestrictedPartitions.lean#L1008) (proved). Stated multiplied by `n`.
- [26.9.E10](https://dlmf.nist.gov/26.9.E10): [`DLMF.Combinatorics.partitionCountAtMostParts_isEquivalent`](DLMF/Combinatorics/RestrictedPartitions.lean#L1017) (admitted). `k ≥ 1`, `IsEquivalent` along `atTop`.
- [26.9.T1](https://dlmf.nist.gov/26.9.T1): Not acquired: finite table of exact values (`decide` does not evaluate Mathlib's `Fintype (Nat.Partition n)`); the closed forms (26.9.2)–(26.9.3) cover its first rows.

Analytical prose (tagged with the subsection or section ID):

- [26.9.i](https://dlmf.nist.gov/26.9#i): [`DLMF.Combinatorics.partitionCountAtMostParts`](DLMF/Combinatorics/RestrictedPartitions.lean#L52) (definition); [`DLMF.Combinatorics.partitionCountBoxed`](DLMF/Combinatorics/RestrictedPartitions.lean#L57) (definition); [`DLMF.Combinatorics.partitionCountAtMostParts_eq_card_parts_le`](DLMF/Combinatorics/RestrictedPartitions.lean#L245) (proved); [`DLMF.Combinatorics.card_parts_conjugate`](DLMF/Combinatorics/RestrictedPartitions.lean#L252) (proved); [`DLMF.Combinatorics.partitionCountBoxed_eq_card_latticePaths`](DLMF/Combinatorics/RestrictedPartitions.lean#L501) (proved).
- [26.9.i](https://dlmf.nist.gov/26.9.i): [`DLMF.Combinatorics.card_parts_conjugate`](DLMF/Combinatorics/RestrictedPartitions.lean#L252) (proved); [`DLMF.Combinatorics.partitionCountAtMostParts`](DLMF/Combinatorics/RestrictedPartitions.lean#L52) (definition); [`DLMF.Combinatorics.partitionCountAtMostParts_eq_card_parts_le`](DLMF/Combinatorics/RestrictedPartitions.lean#L245) (proved); [`DLMF.Combinatorics.partitionCountBoxed`](DLMF/Combinatorics/RestrictedPartitions.lean#L57) (definition); [`DLMF.Combinatorics.partitionCountBoxed_eq_card_latticePaths`](DLMF/Combinatorics/RestrictedPartitions.lean#L501) (proved).

## [§26.10 Integer Partitions: Other Restrictions](https://dlmf.nist.gov/26.10)

- [26.10.E1](https://dlmf.nist.gov/26.10.E1): [`DLMF.Combinatorics.partitionCount_zero`](DLMF/Combinatorics/PartitionIdentities.lean#L149) (proved).
- [26.10.E2](https://dlmf.nist.gov/26.10.E2): [`DLMF.Combinatorics.hasSum_partitionCountDistinct`](DLMF/Combinatorics/PartitionIdentities.lean#L538) (proved); [`DLMF.Combinatorics.hasProd_one_sub_odd_pow_inv`](DLMF/Combinatorics/PartitionIdentities.lean#L507) (proved); [`DLMF.Combinatorics.hasSum_pow_triangle_div_qPochhammer`](DLMF/Combinatorics/PartitionIdentities.lean#L565) (proved); [`DLMF.Combinatorics.hasSum_pow_mul_prod_one_add`](DLMF/Combinatorics/PartitionIdentities.lean#L595) (proved); [`DLMF.Combinatorics.hasSum_distinct_largest`](DLMF/Combinatorics/PartitionIdentities.lean#L697) (proved). Four equalities as four `HasSum`/`HasProd` statements (`|q| < 1`); the series start at `m = 0` with term `1`. `hasSum_distinct_largest` is the prose remark after (26.10.2) (largest part `m`). Mathlib's formal power-series Glaisher product is a partial upstream pointer; Mathlib: [`Nat.Partition.hasProd_powerSeriesMk_card_countRestricted`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Enumerative/Partition/Glaisher.html#Nat.Partition.hasProd_powerSeriesMk_card_countRestricted).
- [26.10.E3](https://dlmf.nist.gov/26.10.E3): [`DLMF.Combinatorics.partitionCountAtMostDistinctBoxed`](DLMF/Combinatorics/PartitionIdentities.lean#L82) (definition); [`DLMF.Combinatorics.hasSum_partitionCountAtMostDistinctBoxed`](DLMF/Combinatorics/PartitionIdentities.lean#L784) (proved); [`DLMF.Combinatorics.sum_qBinom_triangle_eq_prod`](DLMF/Combinatorics/PartitionIdentities.lean#L824) (proved). `|x| < 1`, every `q` (finite `n`-sums; stronger than DLMF). The middle member (Cauchy's finite `q`-binomial theorem) is proved from the existing `qPochhammer_eq_sum_qBinom`.
- [26.10.E4](https://dlmf.nist.gov/26.10.E4): [`DLMF.Combinatorics.hasSum_partitionCountDiff`](DLMF/Combinatorics/PartitionIdentities.lean#L940) (proved). Exponent `(km² + (2-k)m)/2` written `k·C(m,2) + m`; all `k ≥ 0`.
- [26.10.E5](https://dlmf.nist.gov/26.10.E5): [`DLMF.Combinatorics.hasSum_partitionCountIn`](DLMF/Combinatorics/PartitionIdentities.lean#L955) (proved). Any `S ⊆ ℕ` (parts are positive, so `0 ∈ S` is irrelevant); infinite product as `HasProd`; Mathlib: [`Nat.Partition.hasProd_powerSeriesMk_card_restricted`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Enumerative/Partition/Glaisher.html#Nat.Partition.hasProd_powerSeriesMk_card_restricted).
- [26.10.E6](https://dlmf.nist.gov/26.10.E6): [`DLMF.Combinatorics.partitionCountDistinct_recurrence`](DLMF/Combinatorics/PartitionIdentities.lean#L1094) (proved).
- [26.10.E7](https://dlmf.nist.gov/26.10.E7): [`DLMF.Combinatorics.sum_neg_one_pow_partitionCountDistinct_pentagonal`](DLMF/Combinatorics/PartitionIdentities.lean#L1219) (proved). The printed sum over `k ≥ 0` with both signs `±` (the `k = 0` term once) is the sum over `k ∈ ℤ` of Mathlib's `pentagonal k = k(3k-1)/2`; right side `(-1)^r` if `n = r(3r - 1)`, `r ∈ ℤ`. Verified for `n < 40`.
- [26.10.E8](https://dlmf.nist.gov/26.10.E8): [`DLMF.Combinatorics.sum_neg_one_pow_partitionCountDistinct_two_pentagonal`](DLMF/Combinatorics/PartitionIdentities.lean#L1231) (admitted). Same reading; right side `1` iff `n` is triangular. Verified for `n < 40`.
- [26.10.E9](https://dlmf.nist.gov/26.10.E9): [`DLMF.Combinatorics.card_distinct_card_eq_recurrence`](DLMF/Combinatorics/PartitionIdentities.lean#L1394) (proved). **Corrected** (DLMF error): the printed `p_m(𝒟, n) = p_m(𝒟, n - m) + p_{m-1}(𝒟, n)` is false for "at most `m` distinct parts" (`m = n = 2`: `1 ≠ 2`; `m = n = 3`: `2 ≠ 3`). Removing `1` from each of `m` distinct parts leaves `m` or `m - 1` distinct parts. Acquired: `p_m(𝒟, n) = p_{m-1}(𝒟, n) + p_m(𝒟, n-m) - p_{m-2}(𝒟, n-m)` and, for exactly `m` distinct parts, `q_m(n) = q_m(n-m) + q_{m-1}(n-m)` (`1 ≤ m ≤ n`); verified for `m ≤ 6`, `n < 40`; [`DLMF.Combinatorics.partitionCountAtMostDistinct_recurrence`](DLMF/Combinatorics/PartitionIdentities.lean#L1407) (proved).
- [26.10.E10](https://dlmf.nist.gov/26.10.E10): [`DLMF.Combinatorics.partitionCountDiff_eq_sum`](DLMF/Combinatorics/PartitionIdentities.lean#L1433) (proved). The argument `n - km²/2 - m + km/2` is `n - (k·C(m,2) + m)`; verified for `k ≤ 4`, `n < 40`.
- [26.10.E11](https://dlmf.nist.gov/26.10.E11): [`DLMF.Combinatorics.partitionCountIn_recurrence`](DLMF/Combinatorics/PartitionIdentities.lean#L1442) (proved). Stated multiplied by `n`.
- [26.10.E12](https://dlmf.nist.gov/26.10.E12): Upstream: Mathlib `Nat.Partition.card_odds_eq_card_distincts` (pointer in MathlibCoverageB).
- [26.10.E13](https://dlmf.nist.gov/26.10.E13): [`DLMF.Combinatorics.partitionCountDiff_two_eq`](DLMF/Combinatorics/PartitionIdentities.lean#L1548) (proved). Combinatorial first Rogers–Ramanujan identity. The analytic identities are the existing `DLMF.Bailey.rogers_ramanujan_first`/`_second` (tagged 17.2.E49/E50).
- [26.10.E14](https://dlmf.nist.gov/26.10.E14): [`DLMF.Combinatorics.partitionCountDiffTwoNoOne_eq`](DLMF/Combinatorics/PartitionIdentities.lean#L1561) (proved).
- [26.10.E15](https://dlmf.nist.gov/26.10.E15): [`DLMF.Combinatorics.partitionCountSchur_eq`](DLMF/Combinatorics/PartitionIdentities.lean#L1586) (admitted). Schur's theorem; `𝒟'3` read as: parts differ by at least 3, and (consecutive) multiples of 3 by at least 6 (matches Table 26.10.1).
- [26.10.E16](https://dlmf.nist.gov/26.10.E16): [`DLMF.Combinatorics.partitionCountDistinct_isEquivalent`](DLMF/Combinatorics/PartitionIdentities.lean#L1724) (admitted). `IsEquivalent` along `atTop`.
- [26.10.E17](https://dlmf.nist.gov/26.10.E17): [`DLMF.Combinatorics.hasSum_partitionCountDistinct_bessel`](DLMF/Combinatorics/PartitionIdentities.lean#L1830) (admitted). With the corrected `A_k` (26.10.18); `I_1` is the project's `DLMF.Bessel.besselI 1`. The series reproduces `p(𝒟, n)` numerically (mpmath, `n ≤ 20`, 40 terms).
- [26.10.E18](https://dlmf.nist.gov/26.10.E18): [`DLMF.Combinatorics.distinctPartitionKloosterman`](DLMF/Combinatorics/PartitionIdentities.lean#L1740) (definition). **Corrected** (DLMF error): the printed range `1 < h ≤ k` gives `A_1(n) = 0`, killing the leading term of (26.10.17) (with it the series gives `0.08 + 0.07i` instead of `1` at `n = 1`); the range is `1 ≤ h ≤ k`.
- [26.10.E19](https://dlmf.nist.gov/26.10.E19): [`DLMF.Combinatorics.distinctPartitionDedekindSum`](DLMF/Combinatorics/PartitionIdentities.lean#L1735) (definition).
- [26.10.E20](https://dlmf.nist.gov/26.10.E20): [`DLMF.Combinatorics.sawtooth`](DLMF/Combinatorics/PartitionIdentities.lean#L1731) (definition).
- [26.10.T1](https://dlmf.nist.gov/26.10.T1): Not acquired: finite table of exact values (same reason); the identities (26.10.12)–(26.10.15) state the coincidences of its columns. The table was used to confirm the reading of `𝒟'3`.

Analytical prose (tagged with the subsection or section ID):

- [26.10.i](https://dlmf.nist.gov/26.10#i): [`DLMF.Combinatorics.partitionCountDistinct`](DLMF/Combinatorics/PartitionIdentities.lean#L69) (definition); [`DLMF.Combinatorics.partitionCountOdd`](DLMF/Combinatorics/PartitionIdentities.lean#L73) (definition); [`DLMF.Combinatorics.partitionCountAtMostDistinct`](DLMF/Combinatorics/PartitionIdentities.lean#L77) (definition); [`DLMF.Combinatorics.partitionCountDiff`](DLMF/Combinatorics/PartitionIdentities.lean#L95) (definition); [`DLMF.Combinatorics.partitionCountSchur`](DLMF/Combinatorics/PartitionIdentities.lean#L107) (definition); [`DLMF.Combinatorics.partitionCountIn`](DLMF/Combinatorics/PartitionIdentities.lean#L112) (definition); [`DLMF.Combinatorics.residueSetPM`](DLMF/Combinatorics/PartitionIdentities.lean#L117) (definition); [`DLMF.Combinatorics.setGeTwo`](DLMF/Combinatorics/PartitionIdentities.lean#L125) (definition); [`DLMF.Combinatorics.partitionCountDiffTwoNoOne`](DLMF/Combinatorics/PartitionIdentities.lean#L132) (definition).
- [26.10.iv](https://dlmf.nist.gov/26.10#iv): [`DLMF.Combinatorics.partitionCountSchur_le`](DLMF/Combinatorics/PartitionIdentities.lean#L1592) (proved); [`DLMF.Combinatorics.partitionCountSchur_lt_iff`](DLMF/Combinatorics/PartitionIdentities.lean#L1686) (proved); [`DLMF.Combinatorics.partitionCountIn_le_partitionCountDiff`](DLMF/Combinatorics/PartitionIdentities.lean#L1709) (admitted); [`DLMF.Combinatorics.eventually_partitionCountIn_lt_partitionCountDiff`](DLMF/Combinatorics/PartitionIdentities.lean#L1716) (admitted).
- [26.10.vi](https://dlmf.nist.gov/26.10#vi): [`DLMF.Combinatorics.distinctPartitionKloosterman_im`](DLMF/Combinatorics/PartitionIdentities.lean#L1825) (proved).
- [26.10.i](https://dlmf.nist.gov/26.10.i): [`DLMF.Combinatorics.partitionCountAtMostDistinct`](DLMF/Combinatorics/PartitionIdentities.lean#L77) (definition); [`DLMF.Combinatorics.partitionCountDiff`](DLMF/Combinatorics/PartitionIdentities.lean#L95) (definition); [`DLMF.Combinatorics.partitionCountDiffTwoNoOne`](DLMF/Combinatorics/PartitionIdentities.lean#L132) (definition); [`DLMF.Combinatorics.partitionCountDistinct`](DLMF/Combinatorics/PartitionIdentities.lean#L69) (definition); [`DLMF.Combinatorics.partitionCountIn`](DLMF/Combinatorics/PartitionIdentities.lean#L112) (definition); [`DLMF.Combinatorics.partitionCountOdd`](DLMF/Combinatorics/PartitionIdentities.lean#L73) (definition); [`DLMF.Combinatorics.partitionCountSchur`](DLMF/Combinatorics/PartitionIdentities.lean#L107) (definition); [`DLMF.Combinatorics.residueSetPM`](DLMF/Combinatorics/PartitionIdentities.lean#L117) (definition); [`DLMF.Combinatorics.setGeTwo`](DLMF/Combinatorics/PartitionIdentities.lean#L125) (definition).
- [26.10.iv](https://dlmf.nist.gov/26.10.iv): [`DLMF.Combinatorics.eventually_partitionCountIn_lt_partitionCountDiff`](DLMF/Combinatorics/PartitionIdentities.lean#L1716) (admitted); [`DLMF.Combinatorics.partitionCountIn_le_partitionCountDiff`](DLMF/Combinatorics/PartitionIdentities.lean#L1709) (admitted); [`DLMF.Combinatorics.partitionCountSchur_le`](DLMF/Combinatorics/PartitionIdentities.lean#L1592) (proved); [`DLMF.Combinatorics.partitionCountSchur_lt_iff`](DLMF/Combinatorics/PartitionIdentities.lean#L1686) (proved).
- [26.10.vi](https://dlmf.nist.gov/26.10.vi): [`DLMF.Combinatorics.distinctPartitionKloosterman_im`](DLMF/Combinatorics/PartitionIdentities.lean#L1825) (proved).

## [§26.11 Integer Partitions: Compositions](https://dlmf.nist.gov/26.11)

- [26.11.E1](https://dlmf.nist.gov/26.11.E1): [`DLMF.Combinatorics.compositionCount_zero`](DLMF/Combinatorics/Compositions.lean#L50) (proved).
- [26.11.E2](https://dlmf.nist.gov/26.11.E2): [`DLMF.Combinatorics.compositionCountLength_zero`](DLMF/Combinatorics/Compositions.lean#L64) (proved).
- [26.11.E3](https://dlmf.nist.gov/26.11.E3): [`DLMF.Combinatorics.compositionCountLength_eq_choose`](DLMF/Combinatorics/Compositions.lean#L125) (proved). `n ≥ 1`; DLMF's `C(n-1, -1) = 0` for `m = 0` made explicit.
- [26.11.E4](https://dlmf.nist.gov/26.11.E4): [`DLMF.Combinatorics.hasSum_compositionCountLength`](DLMF/Combinatorics/Compositions.lean#L148) (proved). `|q| < 1`.
- [26.11.E5](https://dlmf.nist.gov/26.11.E5): Upstream: `Nat.fib_zero`, `Nat.fib_one`, `Nat.fib_add_two` (pointers).
- [26.11.E6](https://dlmf.nist.gov/26.11.E6): [`DLMF.Combinatorics.compositionCountNoOne_eq_fib`](DLMF/Combinatorics/Compositions.lean#L303) (proved). `n ≥ 1`.
- [26.11.E7](https://dlmf.nist.gov/26.11.E7): Upstream: `Real.coe_fib_eq` (Binet, `φ = (1+√5)/2`, `ψ = (1-√5)/2`; pointer).

Analytical prose (tagged with the subsection or section ID):

- [26.11](https://dlmf.nist.gov/26.11): [`DLMF.Combinatorics.compositionCount`](DLMF/Combinatorics/Compositions.lean#L37) (definition); [`DLMF.Combinatorics.compositionCountLength`](DLMF/Combinatorics/Compositions.lean#L41) (definition); [`DLMF.Combinatorics.compositionCountNoOne`](DLMF/Combinatorics/Compositions.lean#L45) (definition).

## [§26.12 Plane Partitions](https://dlmf.nist.gov/26.12)

- [26.12.E1](https://dlmf.nist.gov/26.12.E1): [`DLMF.Combinatorics.planePartitionCount_three`](DLMF/Combinatorics/PlanePartitions.lean#L925) (proved). `pp(3) = 6` admitted (the box `B(3,3,3)` has `2^27` subsets, beyond `decide`).
- [26.12.E2](https://dlmf.nist.gov/26.12.E2): [`DLMF.Combinatorics.planePartitionExample_spec`](DLMF/Combinatorics/PlanePartitions.lean#L943) (proved). Proved by `decide +kernel`: the array (26.12.2) is a cyclically symmetric plane partition of 75 (Figure 26.12.1).
- [26.12.E3](https://dlmf.nist.gov/26.12.E3): [`DLMF.Combinatorics.planeBox`](DLMF/Combinatorics/PlanePartitions.lean#L64) (definition).
- [26.12.E4](https://dlmf.nist.gov/26.12.E4): [`DLMF.Combinatorics.card_planePartitionsIn`](DLMF/Combinatorics/PlanePartitions.lean#L951) (proved). Rational products; both forms.
- [26.12.E5](https://dlmf.nist.gov/26.12.E5): [`DLMF.Combinatorics.card_symmetric_planePartitionsIn`](DLMF/Combinatorics/PlanePartitions.lean#L1004) (admitted).
- [26.12.E6](https://dlmf.nist.gov/26.12.E6): [`DLMF.Combinatorics.card_cyclicallySymmetric_planePartitionsIn`](DLMF/Combinatorics/PlanePartitions.lean#L1013) (admitted).
- [26.12.E7](https://dlmf.nist.gov/26.12.E7): [`DLMF.Combinatorics.card_cyclicallySymmetric_planePartitionsIn'`](DLMF/Combinatorics/PlanePartitions.lean#L1022) (admitted).
- [26.12.E8](https://dlmf.nist.gov/26.12.E8): [`DLMF.Combinatorics.card_totallySymmetric_planePartitionsIn`](DLMF/Combinatorics/PlanePartitions.lean#L1030) (admitted).
- [26.12.E9](https://dlmf.nist.gov/26.12.E9): [`DLMF.Combinatorics.card_selfComplementary_even`](DLMF/Combinatorics/PlanePartitions.lean#L1042) (admitted).
- [26.12.E10](https://dlmf.nist.gov/26.12.E10): [`DLMF.Combinatorics.card_selfComplementary_odd_even`](DLMF/Combinatorics/PlanePartitions.lean#L1051) (admitted).
- [26.12.E11](https://dlmf.nist.gov/26.12.E11): [`DLMF.Combinatorics.card_selfComplementary_odd_odd`](DLMF/Combinatorics/PlanePartitions.lean#L1060) (admitted).
- [26.12.E12](https://dlmf.nist.gov/26.12.E12): [`DLMF.Combinatorics.card_transposeComplement`](DLMF/Combinatorics/PlanePartitions.lean#L1069) (admitted). **Clarified** (DLMF wording): "transpose complement" is acquired as complement = transpose `(h, j, k) ↦ (j, h, k)` (reflection in the plane `x = y`). With the literal "reflection through the `(x, y)`-plane" `k ↦ 2t + 1 - k` the counts differ (`r = 1`, `t = 1`: 0 versus 1; `r = 3`, `t = 1`: 0 versus 5), while the transpose reading reproduces (26.12.12) for `r ≤ 3`, `t ≤ 2`. `r ≥ 1`.
- [26.12.E13](https://dlmf.nist.gov/26.12.E13): [`DLMF.Combinatorics.card_symmetric_selfComplementary_even`](DLMF/Combinatorics/PlanePartitions.lean#L1080) (admitted).
- [26.12.E14](https://dlmf.nist.gov/26.12.E14): [`DLMF.Combinatorics.card_symmetric_selfComplementary_odd`](DLMF/Combinatorics/PlanePartitions.lean#L1089) (admitted).
- [26.12.E15](https://dlmf.nist.gov/26.12.E15): [`DLMF.Combinatorics.card_cyclicallySymmetric_transposeComplement`](DLMF/Combinatorics/PlanePartitions.lean#L1097) (admitted). Brute force agrees for `r ≤ 2`.
- [26.12.E16](https://dlmf.nist.gov/26.12.E16): [`DLMF.Combinatorics.card_cyclicallySymmetric_selfComplementary`](DLMF/Combinatorics/PlanePartitions.lean#L1110) (admitted).
- [26.12.E17](https://dlmf.nist.gov/26.12.E17): [`DLMF.Combinatorics.card_totallySymmetric_selfComplementary`](DLMF/Combinatorics/PlanePartitions.lean#L1118) (admitted).
- [26.12.E18](https://dlmf.nist.gov/26.12.E18): [`DLMF.Combinatorics.isDescendingPP_example`](DLMF/Combinatorics/PlanePartitions.lean#L1146) (proved).
- [26.12.E19](https://dlmf.nist.gov/26.12.E19): [`DLMF.Combinatorics.card_descendingPPIn`](DLMF/Combinatorics/PlanePartitions.lean#L1171) (admitted). "In `B(r, r, r)`" read as all parts at most `r`; brute force gives 1, 2, 7, 42, 429 for `r ≤ 5`.
- [26.12.E20](https://dlmf.nist.gov/26.12.E20): [`DLMF.Combinatorics.hasSum_planePartitionCount`](DLMF/Combinatorics/PlanePartitions.lean#L1692) (proved). `|q| < 1`; MacMahon's product as `HasProd`.
- [26.12.E21](https://dlmf.nist.gov/26.12.E21): [`DLMF.Combinatorics.sum_planePartitionsIn_pow`](DLMF/Combinatorics/PlanePartitions.lean#L1789) (proved). `q` not a root of unity (DLMF divides). (26.12.21)–(26.12.23) checked symbolically against brute force (`r, s ≤ 3`).
- [26.12.E22](https://dlmf.nist.gov/26.12.E22): [`DLMF.Combinatorics.sum_symmetric_planePartitionsIn_pow`](DLMF/Combinatorics/PlanePartitions.lean#L1817) (admitted).
- [26.12.E23](https://dlmf.nist.gov/26.12.E23): [`DLMF.Combinatorics.sum_cyclicallySymmetric_planePartitionsIn_pow`](DLMF/Combinatorics/PlanePartitions.lean#L1827) (admitted).
- [26.12.E24](https://dlmf.nist.gov/26.12.E24): [`DLMF.Combinatorics.sum_descendingPPIn_pow`](DLMF/Combinatorics/PlanePartitions.lean#L1843) (admitted). **Corrected** (DLMF error): the product runs over `1 ≤ h ≤ j ≤ r`, not `h < j`. As printed, `r = 2` gives `(1-q⁴)/(1-q³)` (not a polynomial), while the descending plane partitions with parts ≤ 2 are `∅`, `(2)` (`1 + q²`); at `q = 1` the printed product contradicts (26.12.19). The corrected product matches brute force for `r ≤ 5`.
- [26.12.E25](https://dlmf.nist.gov/26.12.E25): [`DLMF.Combinatorics.planePartitionCount_recurrence`](DLMF/Combinatorics/PlanePartitions.lean#L1852) (proved). Stated multiplied by `n`; `σ_2` is `ArithmeticFunction.sigma 2`.
- [26.12.E26](https://dlmf.nist.gov/26.12.E26): [`DLMF.Combinatorics.planePartitionCount_isEquivalent`](DLMF/Combinatorics/PlanePartitions.lean#L1860) (admitted). `ζ(3)` as `(riemannZeta 3).re`, `ζ'(-1)` as `(deriv riemannZeta (-1)).re`.
- [26.12.E27](https://dlmf.nist.gov/26.12.E27): excluded: numerical (decimal values of `ζ(3)` and `ζ'(-1)`).
- [26.12.T1](https://dlmf.nist.gov/26.12.T1): [`DLMF.Combinatorics.planePartitionCount_one_two`](DLMF/Combinatorics/PlanePartitions.lean#L833) (proved). A few exact entries (`pp(1) = 1`, `pp(2) = 3`, by `decide +kernel`; `pp(0) = 1` is 26.12.i); the rest of the table is not acquired (finite exact table).

Analytical prose (tagged with the subsection or section ID):

- [26.12.i](https://dlmf.nist.gov/26.12#i): [`DLMF.Combinatorics.IsPlanePartition`](DLMF/Combinatorics/PlanePartitions.lean#L68) (definition); [`DLMF.Combinatorics.planePartitionCount`](DLMF/Combinatorics/PlanePartitions.lean#L822) (definition); [`DLMF.Combinatorics.planePartitionCount_zero`](DLMF/Combinatorics/PlanePartitions.lean#L828) (proved); [`DLMF.Combinatorics.planePartitionCount_eq_card_arrays`](DLMF/Combinatorics/PlanePartitions.lean#L839) (proved); [`DLMF.Combinatorics.IsSymmetricPP`](DLMF/Combinatorics/PlanePartitions.lean#L974) (definition); [`DLMF.Combinatorics.IsCyclicallySymmetricPP`](DLMF/Combinatorics/PlanePartitions.lean#L978) (definition); [`DLMF.Combinatorics.IsTotallySymmetricPP`](DLMF/Combinatorics/PlanePartitions.lean#L982) (definition); [`DLMF.Combinatorics.planeComplement`](DLMF/Combinatorics/PlanePartitions.lean#L987) (definition); [`DLMF.Combinatorics.IsStrictShiftedPP`](DLMF/Combinatorics/PlanePartitions.lean#L1126) (definition); [`DLMF.Combinatorics.IsDescendingPP`](DLMF/Combinatorics/PlanePartitions.lean#L1137) (definition).
- [26.12.i](https://dlmf.nist.gov/26.12.i): [`DLMF.Combinatorics.IsCyclicallySymmetricPP`](DLMF/Combinatorics/PlanePartitions.lean#L978) (definition); [`DLMF.Combinatorics.IsDescendingPP`](DLMF/Combinatorics/PlanePartitions.lean#L1137) (definition); [`DLMF.Combinatorics.IsPlanePartition`](DLMF/Combinatorics/PlanePartitions.lean#L68) (definition); [`DLMF.Combinatorics.IsStrictShiftedPP`](DLMF/Combinatorics/PlanePartitions.lean#L1126) (definition); [`DLMF.Combinatorics.IsSymmetricPP`](DLMF/Combinatorics/PlanePartitions.lean#L974) (definition); [`DLMF.Combinatorics.IsTotallySymmetricPP`](DLMF/Combinatorics/PlanePartitions.lean#L982) (definition); [`DLMF.Combinatorics.planeComplement`](DLMF/Combinatorics/PlanePartitions.lean#L987) (definition); [`DLMF.Combinatorics.planePartitionCount`](DLMF/Combinatorics/PlanePartitions.lean#L822) (definition); [`DLMF.Combinatorics.planePartitionCount_eq_card_arrays`](DLMF/Combinatorics/PlanePartitions.lean#L839) (proved); [`DLMF.Combinatorics.planePartitionCount_zero`](DLMF/Combinatorics/PlanePartitions.lean#L828) (proved).

## [§26.13 Permutations: Cycle Notation](https://dlmf.nist.gov/26.13)

- [26.13.E1](https://dlmf.nist.gov/26.13.E1): Notation: `σ ∈ Equiv.Perm (Fin n)` with values `σ i` (0-based); no separate declaration.
- [26.13.E2](https://dlmf.nist.gov/26.13.E2): [`DLMF.Combinatorics.dlmfExamplePerm_eq_cycles`](DLMF/Combinatorics/Permutations.lean#L68) (proved). `0`-based: `c[0, 2, 1, 4, 6] * c[5, 7]`, proved by `decide`.
- [26.13.E3](https://dlmf.nist.gov/26.13.E3): [`DLMF.Combinatorics.card_numCycles_eq_abs_signedStirlingFirst`](DLMF/Combinatorics/Permutations.lean#L79) (proved). `[n k] = |s(n, k)|` with ACQ26A's signed `signedStirlingFirst`; the count itself is ACQ26A's admitted `card_perm_numCycles` (§26.8(i)), hence "proved from admissions".
- [26.13.E4](https://dlmf.nist.gov/26.13.E4): [`DLMF.Combinatorics.numDerangements_eq_factorial_mul_sum`](DLMF/Combinatorics/Permutations.lean#L91) (proved); [`DLMF.Combinatorics.numDerangements_eq_floor`](DLMF/Combinatorics/Permutations.lean#L110) (proved). First form proved from Mathlib's `numDerangements_sum`. **Domain correction**: the floor form `⌊(n! + e - 2)/e⌋` fails at `n = 0` (`d(0) = 1`, floor `0`); acquired for `n ≥ 1`; Mathlib: [`card_derangements_eq_numDerangements`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Derangements/Finite.html#card_derangements_eq_numDerangements).
- [26.13.E5](https://dlmf.nist.gov/26.13.E5): [`DLMF.Combinatorics.formPerm_eq_prod_swap`](DLMF/Combinatorics/Permutations.lean#L171) (proved). For any list (`List.formPerm`), proved.
- [26.13.E6](https://dlmf.nist.gov/26.13.E6): [`DLMF.Combinatorics.swap_eq_prod_adjacent`](DLMF/Combinatorics/Permutations.lean#L204) (proved). Stated in `Perm ℕ` for `j < k`, proved by induction (conjugation `swap_mul_swap_mul_swap`).

Analytical prose (tagged with the subsection or section ID):

- [26.13](https://dlmf.nist.gov/26.13): [`DLMF.Combinatorics.numCycles`](DLMF/Combinatorics/Permutations.lean#L74) (definition); [`DLMF.Combinatorics.exists_swap_factorization_numCycles`](DLMF/Combinatorics/Permutations.lean#L186) (proved); [`DLMF.Combinatorics.dlmfExamplePerm_eq_swaps`](DLMF/Combinatorics/Permutations.lean#L198) (proved); [`DLMF.Combinatorics.inversionNumber_eq_min_adjacent`](DLMF/Combinatorics/Permutations.lean#L426) (proved); Mathlib: [`Equiv.Perm.sign_prod_list_swap`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Perm/Sign.html#Equiv.Perm.sign_prod_list_swap); Mathlib: [`Equiv.Perm.swap_induction_on`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Perm/Sign.html#Equiv.Perm.swap_induction_on); Mathlib: [`List.formPerm_cons_cons`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Perm/List.html#List.formPerm_cons_cons).

## [§26.14 Permutations: Order Notation](https://dlmf.nist.gov/26.14)

- [26.14.E1](https://dlmf.nist.gov/26.14.E1): [`DLMF.Combinatorics.wordInversions`](DLMF/Combinatorics/Permutations.lean#L237) (definition); [`DLMF.Combinatorics.inversionNumber`](DLMF/Combinatorics/Permutations.lean#L252) (definition).
- [26.14.E2](https://dlmf.nist.gov/26.14.E2): [`DLMF.Combinatorics.wordMajorIndex`](DLMF/Combinatorics/Permutations.lean#L247) (definition); [`DLMF.Combinatorics.majorIndex`](DLMF/Combinatorics/Permutations.lean#L260) (definition).
- [26.14.E3](https://dlmf.nist.gov/26.14.E3): [`DLMF.Combinatorics.sum_pow_inversionNumber`](DLMF/Combinatorics/Permutations.lean#L1269) (proved). `q ≠ 1` (DLMF divides by `1 - q`).
- [26.14.E4](https://dlmf.nist.gov/26.14.E4): [`DLMF.Combinatorics.hasSum_eulerianNumber`](DLMF/Combinatorics/Permutations.lean#L1306) (admitted). Double series over `ℕ × ℕ`, `|x| < 1`, `|t| < 1` (absolute convergence holds there).
- [26.14.E5](https://dlmf.nist.gov/26.14.E5): [`DLMF.Combinatorics.worpitzky`](DLMF/Combinatorics/Permutations.lean#L1313) (proved). `n ≥ 1` (for `n = 0` the printed sum is empty), complex `x`, `C(y, n) = y^{\underline n}/n!`.
- [26.14.E6](https://dlmf.nist.gov/26.14.E6): [`DLMF.Combinatorics.eulerianNumber_eq_sum`](DLMF/Combinatorics/Permutations.lean#L1351) (proved).
- [26.14.E7](https://dlmf.nist.gov/26.14.E7): [`DLMF.Combinatorics.eulerianNumber_eq_sum_stirlingSecond`](DLMF/Combinatorics/Permutations.lean#L1358) (proved).
- [26.14.E8](https://dlmf.nist.gov/26.14.E8): [`DLMF.Combinatorics.eulerianNumber_recurrence`](DLMF/Combinatorics/Permutations.lean#L1401) (proved). `n ≥ 2`, `k ≥ 1` (for `k = 0` see 26.14.14), integer coefficient `n - k`.
- [26.14.E9](https://dlmf.nist.gov/26.14.E9): [`DLMF.Combinatorics.eulerianNumber_symm`](DLMF/Combinatorics/Permutations.lean#L1419) (proved). `k ≤ n - 1` (natural subtraction).
- [26.14.E10](https://dlmf.nist.gov/26.14.E10): [`DLMF.Combinatorics.sum_eulerianNumber`](DLMF/Combinatorics/Permutations.lean#L1438) (proved). Proved (descents of `σ ∈ 𝔖_n` are `≤ n - 1`).
- [26.14.E11](https://dlmf.nist.gov/26.14.E11): [`DLMF.Combinatorics.bernoulli_eq_sum_eulerianNumber`](DLMF/Combinatorics/Permutations.lean#L1514) (proved). `bernoulli` (Mathlib, `B_1 = -1/2`), `m ≥ 2`; checked for `m ≤ 8`.
- [26.14.E12](https://dlmf.nist.gov/26.14.E12): [`DLMF.Combinatorics.stirlingSecond_eq_sum_eulerianNumber`](DLMF/Combinatorics/Permutations.lean#L1524) (proved).
- [26.14.E13](https://dlmf.nist.gov/26.14.E13): [`DLMF.Combinatorics.eulerianNumber_zero_left`](DLMF/Combinatorics/Permutations.lean#L1538) (proved). Proved.
- [26.14.E14](https://dlmf.nist.gov/26.14.E14): [`DLMF.Combinatorics.eulerianNumber_zero_right`](DLMF/Combinatorics/Permutations.lean#L1551) (proved).
- [26.14.E15](https://dlmf.nist.gov/26.14.E15): [`DLMF.Combinatorics.eulerianNumber_one_right`](DLMF/Combinatorics/Permutations.lean#L1558) (proved).
- [26.14.E16](https://dlmf.nist.gov/26.14.E16): [`DLMF.Combinatorics.eulerianNumber_two_right`](DLMF/Combinatorics/Permutations.lean#L1572) (proved).
- [26.14.T1](https://dlmf.nist.gov/26.14.T1): [`DLMF.Combinatorics.eulerianNumber_table`](DLMF/Combinatorics/Permutations.lean#L1263) (proved). A few exact entries (`⟨3 1⟩ = 4`, `⟨4 1⟩ = 11`, `⟨5 2⟩ = 66`, by `decide +kernel`); the rest of the table is not acquired.

Analytical prose (tagged with the subsection or section ID):

- [26.14.i](https://dlmf.nist.gov/26.14#i): [`DLMF.Combinatorics.wordDescentSet`](DLMF/Combinatorics/Permutations.lean#L242) (definition); [`DLMF.Combinatorics.descentNumber`](DLMF/Combinatorics/Permutations.lean#L256) (definition); [`DLMF.Combinatorics.dlmfExamplePerm_stats`](DLMF/Combinatorics/Permutations.lean#L264) (proved); [`DLMF.Combinatorics.eulerianNumber`](DLMF/Combinatorics/Permutations.lean#L496) (definition); [`DLMF.Combinatorics.eulerianNumber_eq_card_excedance`](DLMF/Combinatorics/Permutations.lean#L1206) (proved); [`DLMF.Combinatorics.eulerianNumber_eq_card_weakExcedance`](DLMF/Combinatorics/Permutations.lean#L1221) (proved).
- [26.14.i](https://dlmf.nist.gov/26.14.i): [`DLMF.Combinatorics.descentNumber`](DLMF/Combinatorics/Permutations.lean#L256) (definition); [`DLMF.Combinatorics.dlmfExamplePerm_stats`](DLMF/Combinatorics/Permutations.lean#L264) (proved); [`DLMF.Combinatorics.eulerianNumber`](DLMF/Combinatorics/Permutations.lean#L496) (definition); [`DLMF.Combinatorics.eulerianNumber_eq_card_excedance`](DLMF/Combinatorics/Permutations.lean#L1206) (proved); [`DLMF.Combinatorics.eulerianNumber_eq_card_weakExcedance`](DLMF/Combinatorics/Permutations.lean#L1221) (proved); [`DLMF.Combinatorics.wordDescentSet`](DLMF/Combinatorics/Permutations.lean#L242) (definition).

## [§26.15 Permutations: Matrix Notation](https://dlmf.nist.gov/26.15)

- [26.15.E1](https://dlmf.nist.gov/26.15.E1): [`DLMF.Combinatorics.dlmfExamplePerm_permMatrix`](DLMF/Combinatorics/Permutations.lean#L1598) (proved). Mathlib's `Equiv.Perm.permMatrix` (entry 1 at `(j, σ j)`), proved by `decide +kernel`; sign = sign of the determinant is Mathlib `Matrix.det_permutation` (pointer, 26.15).
- [26.15.E2](https://dlmf.nist.gov/26.15.E2): [`DLMF.Combinatorics.inversionNumber_eq_sum_permMatrix`](DLMF/Combinatorics/Permutations.lean#L1607) (proved).
- [26.15.E3](https://dlmf.nist.gov/26.15.E3): [`DLMF.Combinatorics.rookPolynomial`](DLMF/Combinatorics/Permutations.lean#L1649) (definition).
- [26.15.E4](https://dlmf.nist.gov/26.15.E4): [`DLMF.Combinatorics.rookPolynomial_union`](DLMF/Combinatorics/Permutations.lean#L1735) (proved).
- [26.15.E5](https://dlmf.nist.gov/26.15.E5): [`DLMF.Combinatorics.rookPolynomial_delete`](DLMF/Combinatorics/Permutations.lean#L1804) (proved).
- [26.15.E6](https://dlmf.nist.gov/26.15.E6): [`DLMF.Combinatorics.hitPolynomial`](DLMF/Combinatorics/Permutations.lean#L1660) (definition).
- [26.15.E7](https://dlmf.nist.gov/26.15.E7): [`DLMF.Combinatorics.hitPolynomial_eq`](DLMF/Combinatorics/Permutations.lean#L1898) (proved).
- [26.15.E8](https://dlmf.nist.gov/26.15.E8): [`DLMF.Combinatorics.hitNumber_zero_eq`](DLMF/Combinatorics/Permutations.lean#L1986) (proved). Both equalities; the second from (26.15.7) at `x = 0` ("proved from admissions"). Also 26.18.E3.
- [26.15.E9](https://dlmf.nist.gov/26.15.E9): [`DLMF.Combinatorics.rookNumber_menageBoard`](DLMF/Combinatorics/Permutations.lean#L2379) (proved). Ménage board `{(j,j), (j,j+1)}` with indices mod `n`, `n ≥ 2` (for `n = 1` the board has one square and the formula fails), `k ≤ n`; checked for `n ≤ 7`.
- [26.15.E10](https://dlmf.nist.gov/26.15.E10): [`DLMF.Combinatorics.hitNumber_menageBoard_zero`](DLMF/Combinatorics/Permutations.lean#L2386) (proved). The counting identity for the permutations avoiding the ménage board; the seating interpretation (`2(n!)` placements of the wives) is not formalized.
- [26.15.E11](https://dlmf.nist.gov/26.15.E11): [`DLMF.Combinatorics.sum_rookNumber_ferrersBoard`](DLMF/Combinatorics/Permutations.lean#L2675) (proved). Monotone shape `b_j ≤ n`, polynomial identity in `ℤ[X]`, `(x-k+1)_k` = `descPochhammer ℤ k`; checked for all shapes with `n ≤ 5`.
- [26.15.E12](https://dlmf.nist.gov/26.15.E12): [`DLMF.Combinatorics.sum_rookNumber_staircase`](DLMF/Combinatorics/Permutations.lean#L2688) (proved). Derived from (26.15.11) ("proved from admissions").
- [26.15.E13](https://dlmf.nist.gov/26.15.E13): [`DLMF.Combinatorics.rookNumber_staircase`](DLMF/Combinatorics/Permutations.lean#L2697) (proved).

Analytical prose (tagged with the subsection or section ID):

- [26.15](https://dlmf.nist.gov/26.15): [`DLMF.Combinatorics.rookNumber`](DLMF/Combinatorics/Permutations.lean#L1643) (definition); [`DLMF.Combinatorics.hitNumber`](DLMF/Combinatorics/Permutations.lean#L1654) (definition); [`DLMF.Combinatorics.hitNumber_diagonalBoard_zero`](DLMF/Combinatorics/Permutations.lean#L1668) (proved); [`DLMF.Combinatorics.rookNumber_diagonalBoard`](DLMF/Combinatorics/Permutations.lean#L1693) (proved); Mathlib: [`Matrix.det_permutation`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Permutation.html#Matrix.det_permutation).

## [§26.16 Multiset Permutations](https://dlmf.nist.gov/26.16)

- [26.16.E1](https://dlmf.nist.gov/26.16.E1): [`DLMF.Combinatorics.qMultinomial`](DLMF/Combinatorics/MultisetPermutations.lean#L112) (definition). Product over all `k`; the factor `k = m` is `[a_m, a_m]_q = 1`.
- [26.16.E2](https://dlmf.nist.gov/26.16.E2): [`DLMF.Combinatorics.sum_pow_wordInversions_multisetPermutations`](DLMF/Combinatorics/MultisetPermutations.lean#L118) (admitted). Every `q`; checked symbolically for small multisets.
- [26.16.E3](https://dlmf.nist.gov/26.16.E3): [`DLMF.Combinatorics.sum_pow_wordMajorIndex_multisetPermutations`](DLMF/Combinatorics/MultisetPermutations.lean#L124) (admitted). Every `q`; checked symbolically for small multisets.

Analytical prose (tagged with the subsection or section ID):

- [26.16](https://dlmf.nist.gov/26.16): [`DLMF.Combinatorics.multisetPermutations`](DLMF/Combinatorics/MultisetPermutations.lean#L37) (definition); [`DLMF.Combinatorics.card_multisetPermutations`](DLMF/Combinatorics/MultisetPermutations.lean#L43) (proved); [`DLMF.Combinatorics.multisetPermutation_example`](DLMF/Combinatorics/MultisetPermutations.lean#L105) (proved).

## [§26.17 The Twelvefold Way](https://dlmf.nist.gov/26.17)

- [26.17.T1](https://dlmf.nist.gov/26.17.T1): [`DLMF.Combinatorics.twelvefoldCount_LL_unrestricted`](DLMF/Combinatorics/TwelvefoldWay.lean#L433) (proved); [`DLMF.Combinatorics.twelvefoldCount_LL_injective`](DLMF/Combinatorics/TwelvefoldWay.lean#L442) (proved); [`DLMF.Combinatorics.twelvefoldCount_LL_surjective`](DLMF/Combinatorics/TwelvefoldWay.lean#L456) (proved); [`DLMF.Combinatorics.twelvefoldCount_UL_unrestricted`](DLMF/Combinatorics/TwelvefoldWay.lean#L465) (proved); [`DLMF.Combinatorics.twelvefoldCount_UL_injective`](DLMF/Combinatorics/TwelvefoldWay.lean#L481) (proved); [`DLMF.Combinatorics.twelvefoldCount_UL_surjective`](DLMF/Combinatorics/TwelvefoldWay.lean#L503) (proved); [`DLMF.Combinatorics.twelvefoldCount_LU_unrestricted`](DLMF/Combinatorics/TwelvefoldWay.lean#L541) (proved); [`DLMF.Combinatorics.twelvefoldCount_LU_injective`](DLMF/Combinatorics/TwelvefoldWay.lean#L591) (proved); [`DLMF.Combinatorics.twelvefoldCount_LU_surjective`](DLMF/Combinatorics/TwelvefoldWay.lean#L599) (proved); [`DLMF.Combinatorics.twelvefoldCount_UU_unrestricted`](DLMF/Combinatorics/TwelvefoldWay.lean#L605) (proved); [`DLMF.Combinatorics.twelvefoldCount_UU_injective`](DLMF/Combinatorics/TwelvefoldWay.lean#L617) (proved); [`DLMF.Combinatorics.twelvefoldCount_UU_surjective`](DLMF/Combinatorics/TwelvefoldWay.lean#L625) (proved). All twelve entries as theorems about `twelvefoldCount` (quotients of `Fin n → Fin k` by the permutations of the unlabeled sides). Proved: labeled/labeled unrestricted (`kⁿ`) and one-to-one (`(k-n+1)_n`, as `ascPochhammer`). Qualifications: `C(n-1, n-k)` for `1 ≤ k ≤ n`; `S(n,1) + ⋯ + S(n,k)` for `n ≥ 1` (**domain correction**: for `n = 0` the count is 1 and the printed sum 0); `p_k(n) - p_{k-1}(n)` for `k ≥ 1`. Mathlib pointers: `Nat.card_fun`, `Fintype.card_embedding_eq`, `Sym.card_sym_eq_multichoose`, `Finset.card_powersetCard`.

Analytical prose (tagged with the subsection or section ID):

- [26.17](https://dlmf.nist.gov/26.17): [`DLMF.Combinatorics.twelvefoldCount`](DLMF/Combinatorics/TwelvefoldWay.lean#L76) (definition).

## [§26.18 Counting Techniques](https://dlmf.nist.gov/26.18)

- [26.18.E1](https://dlmf.nist.gov/26.18.E1): Upstream: Mathlib `Finset.inclusion_exclusion_card_inf_compl` and `Finset.inclusion_exclusion_card_biUnion` (pointers; the `t = ∅` term of Mathlib's sum is `|S|`).
- [26.18.E2](https://dlmf.nist.gov/26.18.E2): [`DLMF.Combinatorics.card_not_dvd_primes`](DLMF/Combinatorics/CountingTechniques.lean#L47) (proved). Distinct primes (`Function.Injective p`).
- [26.18.E3](https://dlmf.nist.gov/26.18.E3): [`DLMF.Combinatorics.hitNumber_zero_eq_inclusion_exclusion`](DLMF/Combinatorics/CountingTechniques.lean#L104) (proved). Proved from (26.15.8) and `r_0(B) = 1` ("proved from admissions").
- [26.18.E4](https://dlmf.nist.gov/26.18.E4): [`DLMF.Combinatorics.card_surjective_eq_sum`](DLMF/Combinatorics/CountingTechniques.lean#L121) (proved). **Corrected** (DLMF error): the upper limit is `t = k`, not `t = n`; as printed the formula fails whenever `n ≤ k - 2` (`n = 1`, `k = 3`: `-3`; `n = 2`, `k = 5`: `35`), and for `n = 0 < k`. Brute force for `n, k ≤ 5`.

## Corrections and qualifications (part B)

DLMF errors (each checked by brute force or numerically; scripts in the acquisition scratch):

1. (26.9.7): the sum runs over `k, n` (printed `m, n`) and needs `|x| < 1` (printed `|xq| < 1`).
2. (26.10.9): false as printed for at most `m` distinct parts (`m = n = 2`: `1 ≠ 2`); corrected
   recurrences acquired.
3. §26.10(iv): `p(𝒟'3, n) < p(𝒟3, n)` holds strictly only for `n = 9` and `n ≥ 15`; for
   `10 ≤ n ≤ 14` the two counts are equal (`n = 10`: `4 = 4`). Acquired as `≤`
   (`partitionCountSchur_le`, proved) and the exact strictness range
   (`partitionCountSchur_lt_iff`, admitted).
4. (26.10.18): the range is `1 ≤ h ≤ k` (printed `1 < h ≤ k`, which makes `A_1 = 0`).
5. (26.12.24): the product runs over `1 ≤ h ≤ j ≤ r` (printed `h < j`).
6. §26.12, (26.12.12): "transpose complement" is acquired with transpose `(h, j, k) ↦ (j, h, k)`;
   the literal reflection reading contradicts the count.
7. (26.13.4): the floor form fails at `n = 0`; acquired for `n ≥ 1`.
8. (26.18.4): the upper limit is `k` (printed `n`).

Qualifications: Table 26.17.1 (`C(n-1, n-k)` for `1 ≤ k ≤ n`; `S(n,1) + ⋯ + S(n,k)` for `n ≥ 1`;
`p_k(n) - p_{k-1}(n)` for `k ≥ 1`); (26.14.5) and §26.14(i) weak excedances for `n ≥ 1`;
(26.11.3) `m = 0` case explicit; (26.15.9) for `n ≥ 2`.

## Exclusions (part B)

- 26.9.T1, 26.10.T1: not acquired (finite tables of exact values; `decide` does not evaluate
  `Fintype (Nat.Partition n)`); 26.12.T1 and 26.14.T1 partially acquired.
- 26.12.E27: excluded: numerical.
- Figures 26.9.F1, 26.9.F2, 26.12.F1: excluded: graphical.
- §26.15 ménage seating interpretation (the factor `2(n!)`): application prose, not formalized.
- §§26.19–26.20: excluded: application. §§26.21–26.22: excluded: computation.

## Validation (part B)

- `lake build` of each part-B module succeeds; strict
  `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false` reports only
  `declaration uses sorry`.
- `#print axioms` of the proved declarations: `[propext, Classical.choice, Quot.sound]`.
- Sorry counts (`grep -c '\bsorry\b'`): RestrictedPartitions 13, PartitionIdentities 24,
  Compositions 3, PlanePartitions 24, Permutations 25, MultisetPermutations 3, TwelvefoldWay 10,
  CountingTechniques 2, MathlibCoverageB 0.
