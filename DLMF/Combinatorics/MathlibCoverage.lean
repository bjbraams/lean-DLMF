/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Combinatorics.Enumerative.Bell
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Combinatorics.Enumerative.Catalan.Tree
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Enumerative.Schroder
public import Mathlib.RingTheory.PowerSeries.Catalan
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.Perm.Cycle.Factors
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Algebra.Group.ForwardDiff
public import Pochhammer.PochhammerTransform

/-!
# DLMF Chapter 26, §§26.1–26.8: results already upstream

The `dlmf_upstream` commands below are checked pointers to Mathlib (and lean-codes)
declarations for DLMF §§26.1–26.8, deliberately not duplicate local theorems. Mathlib's
`@[dlmf]` attribute has no Chapter 26 tags. The DLMF objects themselves are Mathlib's:
`Nat.choose`, `Nat.multinomial`/`Multiset.multinomial`, `catalan`, `Nat.bell`,
`Nat.largeSchroder` (DLMF's `r(n)`), `Nat.stirlingSecond` (DLMF's `S(n, k)`) and the unsigned
`Nat.stirlingFirst` (DLMF's `|s(n, k)|`; the signed `s(n, k)` is
`DLMF.Combinatorics.signedStirlingFirst`). The pointers for §§26.9–26.22 are in
`DLMF/Combinatorics/MathlibCoverageB.lean`.
-/

/- §26.1: rising and falling factorials. -/
dlmf_upstream 26.1.E1 ascPochhammer
  "exact: x(x+1)⋯(x+n-1) is (ascPochhammer R n).eval x"
dlmf_upstream 26.1.E1 descPochhammer_eval_eq_prod_range
  "exact: x(x-1)⋯(x-n+1) = (descPochhammer R n).eval x, commutative ring"

/- §26.2: basic definitions. -/
dlmf_upstream 26.2 Equiv.Perm "exact: a permutation of a set is a bijection of it"
dlmf_upstream 26.2 Equiv.Perm.cycleFactorsFinset
  "different convention: the nontrivial cycles of a permutation (fixed points omitted)"
dlmf_upstream 26.2 Equiv.Perm.partition
  "exact: the cycle type with fixed points as 1-cycles"
dlmf_upstream 26.2 Finpartition "exact: a partition of a finite set into nonempty parts"
dlmf_upstream 26.2 Nat.Partition "exact: a partition of a nonnegative integer"

/- §26.3: binomial coefficients. -/
dlmf_upstream 26.3.i Finset.card_powersetCard
  "exact: C(m, n) is the number of n-element subsets of an m-element set"
dlmf_upstream 26.3.E1 Nat.choose_symm "exact: C(m, m-n) = C(m, n), n ≤ m"
dlmf_upstream 26.3.E1 Nat.choose_eq_factorial_div_factorial
  "exact: C(m, n) = m!/(n!(m-n)!), n ≤ m (natural division)"
dlmf_upstream 26.3.E2 Nat.choose_eq_zero_of_lt "exact"
dlmf_upstream 26.3.E3 add_pow "different form: binomial theorem for (x + y)ⁿ"
dlmf_upstream 26.3.E4 hasSum_choose_mul_geometric_of_norm_lt_one
  "exact up to C(m+n, n) = C(m+n, m); normed field, ‖x‖ < 1"
dlmf_upstream 26.3.E5 Nat.choose_succ_succ'
  "exact, written C(m+1, n+1) = C(m, n) + C(m, n+1)"
dlmf_upstream 26.3.E6 Nat.add_one_mul_choose_eq
  "different form: (m+1) C(m, n) = C(m+1, n+1)(n+1)"
dlmf_upstream 26.3.E6 Nat.choose_succ_right_eq
  "different form: C(m, n+1)(n+1) = C(m, n)(m-n)"
dlmf_upstream 26.3.E7 Nat.sum_Icc_choose "exact: ∑_{k=n}^{m} C(k, n) = C(m+1, n+1)"
dlmf_upstream 26.3.E9 Nat.choose_zero_right "exact: C(n, 0) = 1"
dlmf_upstream 26.3.E9 Nat.choose_self "exact: C(n, n) = 1"
dlmf_upstream 26.3.E11 Nat.doubleFactorial_two_mul
  "partial: (2n)‼ = 2ⁿ n!, the ingredient of 26.3.11"

/- §26.4: multinomial coefficients. -/
dlmf_upstream 26.4.i Nat.multinomial_empty "exact: k = 0 gives 1"
dlmf_upstream 26.4.i Nat.multinomial_singleton "exact: k = 1 gives 1"
dlmf_upstream 26.4.E1 Nat.binomial_eq_choose "exact: k = 2 gives C(n₁ + n₂, n₁)"
dlmf_upstream 26.4.E1 Nat.multinomial_univ_two "exact: k = 2 as (a+b)!/(a! b!)"
dlmf_upstream 26.4.E2 Nat.multinomial
  "exact: defined as (∑ nᵢ)! / ∏ nᵢ! (natural division)"
dlmf_upstream 26.4.E2 Nat.multinomial_spec "exact: (∏ nᵢ!) · multinomial = (∑ nᵢ)!"
dlmf_upstream 26.4.E2 Nat.multinomial_insert
  "partial: one step of the product formula, C(n_j + ⋯ + n_k, n_j) times the rest"
dlmf_upstream 26.4.E6 Multiset.multinomial
  "exact: the multinomial coefficient of a multiset of parts (M₁ of Table 26.4.1)"
dlmf_upstream 26.4.E7 Equiv.Perm.card_of_cycleType
  "partial: number of permutations of given cycle type (fixed points omitted), M₂"
dlmf_upstream 26.4.E8 Multiset.bell_mul_eq
  "partial: the formula M₃ for Multiset.bell (the counting statement is a Mathlib TODO)"
dlmf_upstream 26.4.E9 Finset.sum_pow_eq_sum_piAntidiag
  "exact: multinomial theorem, sum over functions with ∑ nᵢ = n, commutative semiring"
dlmf_upstream 26.4.E9 Finset.sum_pow "different form: sum over multisets s.sym n"

/- §26.5: Catalan numbers. -/
dlmf_upstream 26.5.i DyckWord.card_dyckWord_semilength_eq_catalan
  "different form: Dyck words of semilength n (lattice paths above the diagonal)"
dlmf_upstream 26.5.i BinaryTree.treesOfNumNodesEq_card_eq_catalan
  "different form: binary trees with n internal nodes"
dlmf_upstream 26.5.E1 succ_mul_catalan_eq_centralBinom "exact: (n+1) C(n) = C(2n, n)"
dlmf_upstream 26.5.E1 catalan_eq_centralBinom_div "exact: C(n) = C(2n, n)/(n+1), natural division"
dlmf_upstream 26.5.E2 PowerSeries.catalanSeries_sq_mul_X_add_one
  "partial: formal identity x C(x)² + 1 = C(x), equivalent to 26.5.2 as formal series"
dlmf_upstream 26.5.E3 catalan_succ "exact: sum over Fin (n+1)"
dlmf_upstream 26.5.E3 catalan_succ' "exact: sum over the antidiagonal"
dlmf_upstream 26.5.E4 Nat.succ_mul_centralBinom_succ
  "partial: (n+1) C(2n+2, n+1) = 2(2n+1) C(2n, n), the ingredient of 26.5.4"

/- §26.6: other lattice path numbers. -/
dlmf_upstream 26.6.i Nat.largeSchroder
  "exact: the large Schröder numbers 1, 2, 6, 22, … are DLMF's r(n), defined by recurrence"

/- §26.7: Bell numbers. -/
dlmf_upstream 26.7.i Nat.bell
  "exact: defined by the recurrence 26.7.6; the counting statement is a Mathlib TODO"
dlmf_upstream 26.7.i Nat.bell_eq_sum_partition
  "partial: B(n) = ∑ over integer partitions of n of Multiset.bell"
dlmf_upstream 26.7.E1 Nat.bell_zero "exact"
dlmf_upstream 26.7.E6 Nat.bell_succ "exact up to k ↦ n - k: B(n+1) = ∑ C(n, k) B(n-k)"
dlmf_upstream 26.7.E6 Nat.bell_succ' "exact up to k ↦ n - k, antidiagonal form"

/- §26.8: Stirling numbers. -/
dlmf_upstream 26.8.i Nat.stirlingFirst
  "different convention: unsigned |s(n, k)|, defined by recurrence"
dlmf_upstream 26.8.i Nat.stirlingSecond "exact: S(n, k), defined by recurrence"
dlmf_upstream 26.8.E1 Nat.stirlingFirst_self "different convention: unsigned"
dlmf_upstream 26.8.E4 Nat.stirlingSecond_self "exact"
dlmf_upstream 26.8.E7 ascPochhammer_eq_sum_stirlingFirst
  "different convention (lean-codes): rising factorial x(x+1)⋯(x+n-1) with unsigned |s(n, k)|"
dlmf_upstream 26.8.E10 Nat.pow_eq_sum_stirlingSecond_mul_descFactorial
  "special case: natural-number x, nᵏ = ∑ S(k, j) n(n-1)⋯(n-j+1)"
dlmf_upstream 26.8.E10 sum_stirlingSecond_mul_ascPochhammer
  "different convention (lean-codes): Xⁿ = ∑ (-1)^{n-k} S(n, k) X(X+1)⋯(X+k-1)"
dlmf_upstream 26.8.E14 Nat.stirlingFirst_succ_zero "different convention: unsigned, s(n, 0) = 0"
dlmf_upstream 26.8.E14 Nat.stirlingFirst_one_right
  "different convention: unsigned, |s(n+1, 1)| = n!"
dlmf_upstream 26.8.E16 Nat.stirlingFirst_succ_self_left
  "different convention: unsigned, |s(n+1, n)| = C(n+1, 2)"
dlmf_upstream 26.8.E16 Nat.stirlingSecond_succ_self_left "exact: S(n+1, n) = C(n+1, 2)"
dlmf_upstream 26.8.E17 Nat.stirlingSecond_succ_zero "exact: S(n+1, 0) = 0"
dlmf_upstream 26.8.E17 Nat.stirlingSecond_one_right "exact: S(n+1, 1) = 1"
dlmf_upstream 26.8.E18 Nat.stirlingFirst_succ_succ
  "different convention: unsigned |s(n+1, k+1)| = n |s(n, k+1)| + |s(n, k)|"
dlmf_upstream 26.8.E22 Nat.stirlingSecond_succ_succ "exact, written with n+1, k+1"
dlmf_upstream 26.8.E32 fwdDiff "exact: Δf(x) = f(x + 1) - f(x) is fwdDiff 1 f x"
dlmf_upstream 26.8.E34 hasSum_pow_mul_geometric_of_norm_lt_one'
  "different form: the n → ∞ limit ∑ jᵏ xʲ = ∑ S(k, j) j! xʲ (1-x)^{-j-1}, ‖x‖ < 1"
