# DLMF Chapter 1 acquisition: Algebraic and Analytic Methods

This acquisition covers the definitions, numbered formulas and analytical assertions in prose
of [DLMF Chapter 1](https://dlmf.nist.gov/1), version 1.2.8, checked on 2026-10-27, by six
agents working in parallel, one part each: g1a (§§1.1–1.3), g1b (§§1.4–1.7), g1c (§§1.8–1.10),
g1d (§§1.11–1.13), g1e (§§1.14–1.15) and g1f (§§1.16–1.18). Helper lemmas carry the agent's
prefix (`g1a_` …) or are private. The Lean code is in `DLMF/AlgebraicAnalytic/` (namespace
`DLMF.AlgebraicAnalytic`), with one subdirectory per part or section group, each with its own
`Defs` file and, where something is upstream, a `MathlibCoverage` file of `dlmf_upstream`
pointers. The umbrella is [DLMF/AlgebraicAnalytic.lean](DLMF/AlgebraicAnalytic.lean).

Chapter 1 is largely standard mathematics, so a large share of it is already in Mathlib or
Tau Ceti; those items are recorded as upstream pointers rather than reproved. The parts below
are the agents' ledgers, assembled unchanged apart from heading levels.

**Admissions at acquisition** (`grep -cE 'by sorry|:= sorry|^\s*(·\s*)?sorry\s*$|exact sorry'`):
304 in all. By subdirectory: Algebra 1, Calculus 37, Fourier 11, Complex 46, Polynomials 3,
ContinuedFractions 7, ODE 11, Transforms 94, Summability 35, Distributions 34, Spectral 25.

**Source corrections found in this acquisition** (details in the parts; the confirmed errata
are also in `reports/DLMFErrata.tex`): 1.2.51 (equality case of Cauchy–Schwarz when u = 0),
1.7.1–1.7.3 (equality cases when b = 0), 1.7.11 (strict inequality fails for constant f),
1.9.51 (convergence of both factors does not give convergence of the Cauchy product on the
boundary), 1.10.25 (missing zₙ ≠ 0 and |zₙ| → ∞), 1.14.45 (the constant is A_p^p for p-th
powers), Tables 1.14.2, 1.14.4 and 1.14.5 (branch and conditions), §1.15(v) after 1.15.40
(the limit is −ℋf under 1.14.41), 1.15.53 (missing hypothesis on f), 1.17.19–1.17.20
(continuity of φ is not enough), 1.18.54 (f ∈ C(X) is not enough). Convention notes: 1.10.24,
§1.10(ii) (connectedness of D₁ ∩ D₂), 1.13(viii) (periodic boundary conditions under the
Liouville transformation), 1.18.38 (the eigenvalue (2n)² of Case 3 is not printed).

## Part g1a: §§1.1–1.3

This part covers the definitions, numbered formulas and analytical assertions in prose of
[DLMF §1.1](https://dlmf.nist.gov/1.1) (special notation),
[§1.2](https://dlmf.nist.gov/1.2) (elementary algebra) and
[§1.3](https://dlmf.nist.gov/1.3) (determinants, linear operators and spectral expansions),
version 1.2.8, checked on 2026-10-27 by agent g1a (helper prefix `g1a_`). The Lean code is in
`DLMF/AlgebraicAnalytic/Algebra/` (namespace `DLMF.AlgebraicAnalytic`). Modules, in import
order:

- [Defs](DLMF/AlgebraicAnalytic/Algebra/Defs.lean) (all definitions of this part; Mathlib only);
- [Binomial](DLMF/AlgebraicAnalytic/Algebra/Binomial.lean) (§1.2(i)–(iii); Mathlib only);
- [Means](DLMF/AlgebraicAnalytic/Algebra/Means.lean) (§1.2(iv); imports `Defs`);
- [Matrices](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean) (§1.2(v)–(vi); imports `Means`);
- [Determinants](DLMF/AlgebraicAnalytic/Algebra/Determinants.lean) (§1.3(i)–(iii); imports `Defs`);
- [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean) (117 upstream pointers, 116
  to Mathlib and one to Tau Ceti; imports `DLMF.Core.Upstream`, Mathlib and
  `TauCeti.Analysis.Normed.Algebra.MatrixExponential`).

**Counts.** §1.1 is notation only. §1.2 has 77 numbered equations and §1.3 has 21. In scope:
98, all covered: 51 by project declarations (all of them by a proved theorem or a definition,
with one admitted companion theorem for 1.3.E19) and 47 by upstream pointers only (38 in §1.2,
9 in §1.3). In addition 6 prose IDs carry tags or pointers (1.2.iv, 1.2.v, 1.2.vi, 1.3.i,
1.3.iii, 1.3.iv). 52 DLMF IDs are tagged on 56 project declarations and 75 IDs have upstream
pointers. The six modules contain 8 definitions (all tagged, in `Defs`) and 61 theorems:
48 tagged proved theorems, 2 untagged API lemmas, 10 untagged `g1a_` helpers and 1 admission
(the convergence of Hill-type infinite determinants, 1.3.iii/1.3.E19). No proved theorem
depends on an admission.

Module admissions (`grep -cE 'by sorry|:= sorry|^\s*(·\s*)?sorry\s*$|exact sorry'`) and
declarations:

- [Defs](DLMF/AlgebraicAnalytic/Algebra/Defs.lean): 0 admissions; 8 definitions.
- [Binomial](DLMF/AlgebraicAnalytic/Algebra/Binomial.lean): 0 admissions; 9 theorems, all proved.
- [Means](DLMF/AlgebraicAnalytic/Algebra/Means.lean): 0 admissions; 11 theorems, all proved.
- [Matrices](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean): 0 admissions; 22 theorems, all proved.
- [Determinants](DLMF/AlgebraicAnalytic/Algebra/Determinants.lean): 1 admission; 19 theorems: 18
  proved, 1 admitted.
- [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean): no declarations; 117
  `dlmf_upstream` pointers.

### Conventions and design (part g1a)

- Binomial coefficients: `Nat.choose` for natural arguments and `Ring.choose z k` for complex `z`
  (1.2.6); Pochhammer symbols are Mathlib's `ascPochhammer`/`descPochhammer`.
- The partial-fraction formulas 1.2.12–1.2.16 are stated over any field (1.2.14–1.2.15 in
  characteristic zero) as identities of values off the poles, with the coefficients `A_j`, `B_j`
  explicit.
- Means (§1.2(iv)) are real-valued functions of a finite family `a : ι → ℝ`; the weighted power mean
  `weightedPowerMean p a r` takes the weights as an argument. DLMF leaves `M(0)` undefined and
  states its limit 1.2.26; the definition sets `M(0) = ∏ a_j^{p_j}`, and the exception of 1.2.22 (`r
  < 0` and some `a_j = 0`) is part of the definition. 1.2.26 is proved for arbitrary positive
  weights summing to `1` (stronger than DLMF) and in the equal-weight form with `G`.
- Scalar product (1.2.40): DLMF's `⟨u, v⟩ = ∑ u_j conj(v_j)` is linear in `u`; it is `u ⬝ᵥ star v`
  on `Fin n → ℂ` and Mathlib's `⟪v, u⟫_ℂ` on `EuclideanSpace` (the argument order is reversed).
- Matrices are `Matrix (Fin n) (Fin n) ℂ` (or a general field where DLMF's statement is algebraic).
  The characteristic polynomial in Mathlib is `det(XI - A)`, DLMF's is `det(A - λI)`; the tagged
  eigenvalue theorem uses DLMF's form. The adjugate is the transposed cofactor matrix in both.
- The matrix exponential 1.2.76 is `NormedSpace.exp`; 1.2.77 is Tau Ceti's `Matrix.det_exp`.
- DLMF's circulant (1.3.15) has entry `a_{k-j}` in row `j`, column `k`, the transpose of Mathlib's
  `Matrix.circulant`. Indices run over `Fin n` from `0`.
- Krattenthaler's formula 1.3.16–1.3.17 is stated over any commutative ring with indices shifted to
  `Fin n`.
- Infinite determinants (§1.3(iii)): `truncDet a n` is the `(2n+1) × (2n+1)` determinant `D_n` of
  1.3.18 over the indices `-n, …, n`; `HasInfiniteDet a L` is `D_n → L`; `IsHillType a` is the
  absolute summability 1.3.19 of `a_{j,k} - δ_{j,k}` over `ℤ × ℤ`.
- §1.3(iv) (linear operators on inner product spaces, self-adjointness, the spectral expansions
  1.3.20–1.3.21) is covered by Mathlib's inner-product-space and spectral-theorem API; only pointers
  are recorded.

### Suspected source imprecision (part g1a)

- [1.2.E51](https://dlmf.nist.gov/1.2.E51): DLMF states that equality holds in the Cauchy–Schwarz
  inequality "iff `v` is a scalar multiple of `u`". This fails for `u = 0`, `v ≠ 0` (equality `0 =
  0` holds but `v` is no multiple of `0`). The theorem `norm_inner_eq_norm_mul_iff` states the
  corrected form: equality iff `u = 0` or `v` is a scalar multiple of `u` (equivalently, `u` and `v`
  are linearly dependent).

### Numbered formulas and prose items (part g1a)

## [§1.1 Special Notation](https://dlmf.nist.gov/1.1)

- [1.1](https://dlmf.nist.gov/1.1): no statement (notation).

## [§1.2 Elementary Algebra](https://dlmf.nist.gov/1.2)

- [1.2.iv](https://dlmf.nist.gov/1.2.iv): upstream only: Mathlib:; Mathlib: [`Real.geom_mean_le_arith_mean_weighted`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/MeanInequalities.html#Real.geom_mean_le_arith_mean_weighted).
  `Real.geom_mean_le_arith_mean_weighted` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.v](https://dlmf.nist.gov/1.2.v): upstream only: Mathlib: `norm_smul_inv_norm` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.vi](https://dlmf.nist.gov/1.2.vi): upstream only: Mathlib: `Matrix.IsUpperTriangular`,
  Mathlib: `Matrix.IsLowerTriangular` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E1](https://dlmf.nist.gov/1.2.E1): upstream only: Mathlib: `Nat.cast_choose`, Mathlib:; Mathlib: [`Nat.choose_eq_factorial_div_factorial`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Choose/Basic.html#Nat.choose_eq_factorial_div_factorial); Mathlib: [`Nat.choose_symm`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Choose/Basic.html#Nat.choose_symm).
  `Nat.choose_eq_factorial_div_factorial`, Mathlib: `Nat.choose_symm` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). Natural-number binomial
  coefficients are `Nat.choose`.
- [1.2.E2](https://dlmf.nist.gov/1.2.E2): upstream only: Mathlib: `add_pow`, Mathlib:; Mathlib: [`Commute.add_pow`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Choose/Sum.html#Commute.add_pow).
  `Commute.add_pow` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). Valid also for `n = 0`
  (DLMF: `n` positive).
- [1.2.E3](https://dlmf.nist.gov/1.2.E3): upstream only: Mathlib: `Nat.sum_range_choose` (pointers
  in [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E4](https://dlmf.nist.gov/1.2.E4): upstream only: Mathlib:; Mathlib: [`Int.alternating_sum_range_choose_of_ne`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Choose/Sum.html#Int.alternating_sum_range_choose_of_ne).
  `Int.alternating_sum_range_choose_of_ne` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). `n ≠ 0` as in DLMF
  (erratum V1.0.5/V1.0.11 already applied).
- [1.2.E5](https://dlmf.nist.gov/1.2.E5):; [`DLMF.AlgebraicAnalytic.sum_choose_even`](DLMF/AlgebraicAnalytic/Algebra/Binomial.lean#L43) (proved).
  [`sum_choose_even`](DLMF/AlgebraicAnalytic/Algebra/Binomial.lean#L43) (proved). Sum over the even
  `k ≤ n`; `n ≠ 0`.
- [1.2.E6](https://dlmf.nist.gov/1.2.E6):; [`DLMF.AlgebraicAnalytic.ringChoose_eq_descPochhammer`](DLMF/AlgebraicAnalytic/Algebra/Binomial.lean#L67) (proved); Mathlib: [`Ring.descPochhammer_eq_factorial_smul_choose`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Binomial.html#Ring.descPochhammer_eq_factorial_smul_choose); Mathlib: [`Ring.choose_neg`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Binomial.html#Ring.choose_neg).
  [`ringChoose_eq_descPochhammer`](DLMF/AlgebraicAnalytic/Algebra/Binomial.lean#L67) (proved).
  Upstream: Mathlib: `Ring.descPochhammer_eq_factorial_smul_choose`, Mathlib: `Ring.choose_neg`
  (pointers in [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). `C(z,k)` for
  complex `z` is `Ring.choose z k`; the Pochhammer symbols are `descPochhammer`/`ascPochhammer`.
- [1.2.E7](https://dlmf.nist.gov/1.2.E7): upstream only: Mathlib: `Ring.choose_succ_succ`, Mathlib:; Mathlib: [`Nat.choose_succ_succ`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Choose/Basic.html#Nat.choose_succ_succ).
  `Nat.choose_succ_succ` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). Stated by Mathlib with `k
  + 1`; the case `k = 0` is DLMF's convention `C(z, -1) = 0`.
- [1.2.E8](https://dlmf.nist.gov/1.2.E8):; [`DLMF.AlgebraicAnalytic.sum_ringChoose_add`](DLMF/AlgebraicAnalytic/Algebra/Binomial.lean#L88) (proved).
  [`sum_ringChoose_add`](DLMF/AlgebraicAnalytic/Algebra/Binomial.lean#L88) (proved).
- [1.2.E9](https://dlmf.nist.gov/1.2.E9):; [`DLMF.AlgebraicAnalytic.alternating_sum_ringChoose`](DLMF/AlgebraicAnalytic/Algebra/Binomial.lean#L101) (proved).
  [`alternating_sum_ringChoose`](DLMF/AlgebraicAnalytic/Algebra/Binomial.lean#L101) (proved).
- [1.2.E10](https://dlmf.nist.gov/1.2.E10):; [`DLMF.AlgebraicAnalytic.sum_arithmetic_progression`](DLMF/AlgebraicAnalytic/Algebra/Binomial.lean#L116) (proved); Mathlib: [`Finset.sum_range_id_mul_two`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/BigOperators/Intervals.html#Finset.sum_range_id_mul_two).
  [`sum_arithmetic_progression`](DLMF/AlgebraicAnalytic/Algebra/Binomial.lean#L116) (proved).
  Upstream: Mathlib: `Finset.sum_range_id_mul_two` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). Any field of
  characteristic zero.
- [1.2.E11](https://dlmf.nist.gov/1.2.E11):; [`DLMF.AlgebraicAnalytic.sum_geometric_progression`](DLMF/AlgebraicAnalytic/Algebra/Binomial.lean#L129) (proved); Mathlib: [`geom_sum_eq`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Field/GeomSum.html#geom_sum_eq).
  [`sum_geometric_progression`](DLMF/AlgebraicAnalytic/Algebra/Binomial.lean#L129) (proved).
  Upstream: Mathlib: `geom_sum_eq` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). Any field; `x ≠ 1`.
- [1.2.E12](https://dlmf.nist.gov/1.2.E12):; [`DLMF.AlgebraicAnalytic.div_prod_sub_eq_sum`](DLMF/AlgebraicAnalytic/Algebra/Binomial.lean#L140) (proved); Mathlib: [`Lagrange.eval_interpolate_not_at_node`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Lagrange.html#Lagrange.eval_interpolate_not_at_node).
  [`div_prod_sub_eq_sum`](DLMF/AlgebraicAnalytic/Algebra/Binomial.lean#L140) (proved). Upstream:
  Mathlib: `Lagrange.eval_interpolate_not_at_node` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). Values at `x` off the
  poles, any field; `deg f < n`, distinct `α_j`. Proved from Lagrange interpolation.
- [1.2.E13](https://dlmf.nist.gov/1.2.E13):; [`DLMF.AlgebraicAnalytic.div_prod_sub_eq_sum`](DLMF/AlgebraicAnalytic/Algebra/Binomial.lean#L140) (proved).
  [`div_prod_sub_eq_sum`](DLMF/AlgebraicAnalytic/Algebra/Binomial.lean#L140) (proved). The
  coefficient `A_j` appears explicitly in `div_prod_sub_eq_sum`.
- [1.2.E14](https://dlmf.nist.gov/1.2.E14):; [`DLMF.AlgebraicAnalytic.div_pow_sub_eq_sum`](DLMF/AlgebraicAnalytic/Algebra/Binomial.lean#L160) (proved).
  [`div_pow_sub_eq_sum`](DLMF/AlgebraicAnalytic/Algebra/Binomial.lean#L160) (proved). Field of
  characteristic zero; `deg f < n`, `x ≠ α`. Proved from the Taylor expansion (`Polynomial.taylor`,
  Hasse derivatives).
- [1.2.E15](https://dlmf.nist.gov/1.2.E15):; [`DLMF.AlgebraicAnalytic.div_pow_sub_eq_sum`](DLMF/AlgebraicAnalytic/Algebra/Binomial.lean#L160) (proved).
  [`div_pow_sub_eq_sum`](DLMF/AlgebraicAnalytic/Algebra/Binomial.lean#L160) (proved). The
  coefficient `B_j` appears explicitly in `div_pow_sub_eq_sum`.
- [1.2.E16](https://dlmf.nist.gov/1.2.E16):; [`DLMF.AlgebraicAnalytic.exists_div_prod_pow_sub_eq_sum`](DLMF/AlgebraicAnalytic/Algebra/Binomial.lean#L191) (proved); Mathlib: [`Polynomial.eq_quo_mul_prod_add_sum_rem_mul_prod`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/PartialFractions.html#Polynomial.eq_quo_mul_prod_add_sum_rem_mul_prod); Mathlib: [`Polynomial.eq_quo_mul_prod_pow_add_sum_rem_mul_prod_pow`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/PartialFractions.html#Polynomial.eq_quo_mul_prod_pow_add_sum_rem_mul_prod_pow).
  [`exists_div_prod_pow_sub_eq_sum`](DLMF/AlgebraicAnalytic/Algebra/Binomial.lean#L191) (proved).
  Upstream: Mathlib: `Polynomial.eq_quo_mul_prod_add_sum_rem_mul_prod`, Mathlib:
  `Polynomial.eq_quo_mul_prod_pow_add_sum_rem_mul_prod_pow` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). Existence of the `f_j`;
  the positivity of the `m_j` is not needed. Proved from Mathlib's partial-fraction theorem, with
  the quotient shown to vanish by degrees.
- [1.2.E17](https://dlmf.nist.gov/1.2.E17):; [`DLMF.AlgebraicAnalytic.arithmeticMean`](DLMF/AlgebraicAnalytic/Algebra/Defs.lean#L40) (definition).
  [`arithmeticMean`](DLMF/AlgebraicAnalytic/Algebra/Defs.lean#L40) (definition). Real numbers; the
  mean of the empty family is `0`.
- [1.2.E18](https://dlmf.nist.gov/1.2.E18):; [`DLMF.AlgebraicAnalytic.geometricMean`](DLMF/AlgebraicAnalytic/Algebra/Defs.lean#L46) (definition).
  [`geometricMean`](DLMF/AlgebraicAnalytic/Algebra/Defs.lean#L46) (definition).
- [1.2.E19](https://dlmf.nist.gov/1.2.E19):; [`DLMF.AlgebraicAnalytic.harmonicMean`](DLMF/AlgebraicAnalytic/Algebra/Defs.lean#L52) (definition); [`DLMF.AlgebraicAnalytic.inv_harmonicMean`](DLMF/AlgebraicAnalytic/Algebra/Means.lean#L41) (proved).
  [`harmonicMean`](DLMF/AlgebraicAnalytic/Algebra/Defs.lean#L52) (definition);
  [`inv_harmonicMean`](DLMF/AlgebraicAnalytic/Algebra/Means.lean#L41) (proved).
- [1.2.E20](https://dlmf.nist.gov/1.2.E20):; [`DLMF.AlgebraicAnalytic.weightedPowerMean`](DLMF/AlgebraicAnalytic/Algebra/Defs.lean#L58) (definition).
  [`weightedPowerMean`](DLMF/AlgebraicAnalytic/Algebra/Defs.lean#L58) (definition). The weights are
  arguments of `weightedPowerMean`; positivity and 1.2.20 are hypotheses of the theorems.
- [1.2.E21](https://dlmf.nist.gov/1.2.E21):; [`DLMF.AlgebraicAnalytic.weightedPowerMean`](DLMF/AlgebraicAnalytic/Algebra/Defs.lean#L58) (definition).
  [`weightedPowerMean`](DLMF/AlgebraicAnalytic/Algebra/Defs.lean#L58) (definition). `M(0)` is
  defined as the weighted geometric mean (the limit 1.2.26), which DLMF leaves undefined.
- [1.2.E22](https://dlmf.nist.gov/1.2.E22):; [`DLMF.AlgebraicAnalytic.weightedPowerMean`](DLMF/AlgebraicAnalytic/Algebra/Defs.lean#L58) (definition).
  [`weightedPowerMean`](DLMF/AlgebraicAnalytic/Algebra/Defs.lean#L58) (definition). The exception is
  part of the definition.
- [1.2.E23](https://dlmf.nist.gov/1.2.E23):; [`DLMF.AlgebraicAnalytic.tendsto_weightedPowerMean_atTop`](DLMF/AlgebraicAnalytic/Algebra/Means.lean#L98) (proved).
  [`tendsto_weightedPowerMean_atTop`](DLMF/AlgebraicAnalytic/Algebra/Means.lean#L98) (proved).
  Positive weights, nonnegative `a_j`; the normalization 1.2.20 is not needed.
- [1.2.E24](https://dlmf.nist.gov/1.2.E24):; [`DLMF.AlgebraicAnalytic.tendsto_weightedPowerMean_atBot`](DLMF/AlgebraicAnalytic/Algebra/Means.lean#L112) (proved).
  [`tendsto_weightedPowerMean_atBot`](DLMF/AlgebraicAnalytic/Algebra/Means.lean#L112) (proved).
  Positive weights, nonnegative `a_j`; the normalization 1.2.20 is not needed.
- [1.2.E25](https://dlmf.nist.gov/1.2.E25):; [`DLMF.AlgebraicAnalytic.weightedPowerMean_neg_one`](DLMF/AlgebraicAnalytic/Algebra/Means.lean#L155) (proved); [`DLMF.AlgebraicAnalytic.weightedPowerMean_one`](DLMF/AlgebraicAnalytic/Algebra/Means.lean#L147) (proved).
  [`weightedPowerMean_one`](DLMF/AlgebraicAnalytic/Algebra/Means.lean#L147) (proved);
  [`weightedPowerMean_neg_one`](DLMF/AlgebraicAnalytic/Algebra/Means.lean#L155) (proved). `M(-1) =
  H` for positive `a_j` (DLMF: "the last two equations require `a_j > 0`").
- [1.2.E26](https://dlmf.nist.gov/1.2.E26):; [`DLMF.AlgebraicAnalytic.tendsto_weightedPowerMean_zero`](DLMF/AlgebraicAnalytic/Algebra/Means.lean#L165) (proved); [`DLMF.AlgebraicAnalytic.tendsto_weightedPowerMean_zero_geometricMean`](DLMF/AlgebraicAnalytic/Algebra/Means.lean#L200) (proved).
  [`tendsto_weightedPowerMean_zero`](DLMF/AlgebraicAnalytic/Algebra/Means.lean#L165) (proved);
  [`tendsto_weightedPowerMean_zero_geometricMean`](DLMF/AlgebraicAnalytic/Algebra/Means.lean#L202)
  (proved). Stronger than DLMF: for arbitrary positive weights with `∑ p_j = 1` the limit is `∏
  a_j^{p_j}`; the equal-weight form gives `G`. Limit along `r → 0`, `r ≠ 0`.
- [1.2.E27](https://dlmf.nist.gov/1.2.E27): upstream only: Mathlib: `Matrix` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E28](https://dlmf.nist.gov/1.2.E28): upstream only: Mathlib: `Matrix.transpose_apply`
  (pointers in [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E29](https://dlmf.nist.gov/1.2.E29): upstream only: Mathlib: `Matrix.map_apply` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E30](https://dlmf.nist.gov/1.2.E30): upstream only: Mathlib: `Matrix.conjTranspose_apply`
  (pointers in [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E31](https://dlmf.nist.gov/1.2.E31): upstream only: Mathlib: `Matrix.smul_apply`, Mathlib:; Mathlib: [`IsCentralScalar.op_smul_eq_smul`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Action/Defs.html#IsCentralScalar.op_smul_eq_smul).
  `op_smul_eq_smul` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E32](https://dlmf.nist.gov/1.2.E32): upstream only: Mathlib: `Matrix.add_apply`, Mathlib:; Mathlib: [`add_comm`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Semigroup.html#add_comm).
  `add_comm` (pointers in [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E33](https://dlmf.nist.gov/1.2.E33): upstream only: Mathlib: `add_assoc` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E34](https://dlmf.nist.gov/1.2.E34): upstream only: Mathlib: `Matrix.mul_apply` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E35](https://dlmf.nist.gov/1.2.E35): upstream only: Mathlib: `Matrix.mul_assoc` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E36](https://dlmf.nist.gov/1.2.E36): upstream only: Mathlib: `Matrix.mul_add` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E37](https://dlmf.nist.gov/1.2.E37): upstream only: Mathlib: `Matrix.transpose_mul` (pointers
  in [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E38](https://dlmf.nist.gov/1.2.E38): upstream only: Mathlib: `Matrix.replicateCol` (pointers
  in [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E39](https://dlmf.nist.gov/1.2.E39): upstream only: Mathlib: `Matrix.replicateRow`, Mathlib:; Mathlib: [`Matrix.transpose_replicateCol`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/RowCol.html#Matrix.transpose_replicateCol).
  `Matrix.transpose_replicateCol` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E40](https://dlmf.nist.gov/1.2.E40):; [`DLMF.AlgebraicAnalytic.dotProduct_star_eq_inner`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L61) (proved); [`DLMF.AlgebraicAnalytic.dotProduct_star_eq_sum`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L54) (proved); Mathlib: [`EuclideanSpace.inner_eq_star_dotProduct`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/PiL2.html#EuclideanSpace.inner_eq_star_dotProduct).
  [`dotProduct_star_eq_sum`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L54) (proved);
  [`dotProduct_star_eq_inner`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L61) (proved). Upstream:
  Mathlib: `EuclideanSpace.inner_eq_star_dotProduct` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). Convention: DLMF's `⟨u,
  v⟩` (linear in `u`) is `u ⬝ᵥ star v`, and Mathlib's `⟪v, u⟫_ℂ` on `EuclideanSpace`.
- [1.2.E41](https://dlmf.nist.gov/1.2.E41):; [`DLMF.AlgebraicAnalytic.dotProduct_star_conj_symm`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L69) (proved); Mathlib: [`inner_conj_symm`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Basic.html#inner_conj_symm).
  [`dotProduct_star_conj_symm`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L69) (proved).
  Upstream: Mathlib: `inner_conj_symm` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E42](https://dlmf.nist.gov/1.2.E42):; [`DLMF.AlgebraicAnalytic.smul_dotProduct_star_smul`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L76) (proved); Mathlib: [`inner_smul_left`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Basic.html#inner_smul_left); Mathlib: [`inner_smul_right`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Basic.html#inner_smul_right).
  [`smul_dotProduct_star_smul`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L76) (proved).
  Upstream: Mathlib: `inner_smul_left`, Mathlib: `inner_smul_right` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E43](https://dlmf.nist.gov/1.2.E43): upstream only: Mathlib: `dotProduct_self_star_eq_zero`,; Mathlib: [`inner_self_eq_zero`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Basic.html#inner_self_eq_zero).
  Mathlib: `inner_self_eq_zero` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E44](https://dlmf.nist.gov/1.2.E44): upstream only: Mathlib: `inner_eq_zero_symm` (pointers
  in [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). No separate
  definition: orthogonality is `⟪u, v⟫ = 0`.
- [1.2.E45](https://dlmf.nist.gov/1.2.E45): upstream only: Mathlib: `PiLp.norm_eq_sum` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). Mathlib's `PiLp p` norm,
  valid for `0 < p < ∞`.
- [1.2.E46](https://dlmf.nist.gov/1.2.E46): upstream only: Mathlib: `EuclideanSpace.norm_eq`,; Mathlib: [`norm_eq_sqrt_re_inner`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Basic.html#norm_eq_sqrt_re_inner).
  Mathlib: `norm_eq_sqrt_re_inner` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E47](https://dlmf.nist.gov/1.2.E47): upstream only: Mathlib: `PiLp.norm_eq_of_L1` (pointers
  in [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E48](https://dlmf.nist.gov/1.2.E48):; [`DLMF.AlgebraicAnalytic.tendsto_lpNorm_atTop`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L119) (proved); Mathlib: [`PiLp.norm_eq_ciSup`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Lp/PiLp.html#PiLp.norm_eq_ciSup).
  [`tendsto_lpNorm_atTop`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L119) (proved). Upstream:
  Mathlib: `PiLp.norm_eq_ciSup` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). The limit `‖v‖_p → ‖v‖_∞`
  as `p → ∞` is `tendsto_lpNorm_atTop`.
- [1.2.E49](https://dlmf.nist.gov/1.2.E49): upstream only: Mathlib: `Real.HolderConjugate` (pointers
  in [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). `Real.HolderConjugate
  p q`.
- [1.2.E50](https://dlmf.nist.gov/1.2.E50):; [`DLMF.AlgebraicAnalytic.norm_dotProduct_star_le_Lp_mul_Lq`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L84) (proved); Mathlib: [`Real.inner_le_Lp_mul_Lq`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/MeanInequalities.html#Real.inner_le_Lp_mul_Lq).
  [`norm_dotProduct_star_le_Lp_mul_Lq`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L84) (proved).
  Upstream: Mathlib: `Real.inner_le_Lp_mul_Lq` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). Complex vectors, derived
  from Mathlib's real Hölder inequality.
- [1.2.E51](https://dlmf.nist.gov/1.2.E51):; [`DLMF.AlgebraicAnalytic.norm_inner_eq_norm_mul_iff`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L96) (proved); Mathlib: [`norm_inner_le_norm`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Basic.html#norm_inner_le_norm); Mathlib: [`norm_inner_eq_norm_iff`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Basic.html#norm_inner_eq_norm_iff).
  [`norm_inner_eq_norm_mul_iff`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L96) (proved).
  Upstream: Mathlib: `norm_inner_le_norm`, Mathlib: `norm_inner_eq_norm_iff` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). Corrected equality case:
  DLMF's "iff `v` is a scalar multiple of `u`" fails for `u = 0 ≠ v`; the theorem has `u = 0 ∨ ∃ c,
  v = c • u`.
- [1.2.E52](https://dlmf.nist.gov/1.2.E52): upstream only: Mathlib: `norm_add_le` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E53](https://dlmf.nist.gov/1.2.E53): upstream only: Mathlib: `Matrix.one_apply` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E54](https://dlmf.nist.gov/1.2.E54): upstream only: Mathlib: `Matrix.IsDiag` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E55](https://dlmf.nist.gov/1.2.E55): upstream only: Mathlib: `Matrix.IsSymm` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). A real symmetric matrix
  is `IsSymm` for `Matrix n n ℝ`.
- [1.2.E56](https://dlmf.nist.gov/1.2.E56): upstream only: Mathlib: `Matrix.IsHermitian` (pointers
  in [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E57](https://dlmf.nist.gov/1.2.E57):; [`DLMF.AlgebraicAnalytic.IsTridiagonal`](DLMF/AlgebraicAnalytic/Algebra/Defs.lean#L72) (definition).
  [`IsTridiagonal`](DLMF/AlgebraicAnalytic/Algebra/Defs.lean#L72) (definition). Indices `Fin n`.
- [1.2.E58](https://dlmf.nist.gov/1.2.E58): upstream only: Mathlib: `Matrix.det` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E59](https://dlmf.nist.gov/1.2.E59):; [`DLMF.AlgebraicAnalytic.det_eq_sum_sign_mul_prod`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L135) (proved); Mathlib: [`Matrix.det_apply`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.html#Matrix.det_apply).
  [`det_eq_sum_sign_mul_prod`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L135) (proved).
  Upstream: Mathlib: `Matrix.det_apply` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). DLMF's factor order
  `a_{i,σ(i)}`; Mathlib's `det_apply` has `a_{σ(i),i}`.
- [1.2.E60](https://dlmf.nist.gov/1.2.E60):; [`DLMF.AlgebraicAnalytic.eq_of_mul_eq_mul_of_det_ne_zero`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L152) (proved); [`DLMF.AlgebraicAnalytic.exists_mul_eq_mul_ne_of_det_eq_zero`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L159) (proved); [`DLMF.AlgebraicAnalytic.mul_inv_eq_one_of_det_ne_zero`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L143) (proved); Mathlib: [`Matrix.mul_nonsing_inv`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.html#Matrix.mul_nonsing_inv); Mathlib: [`Matrix.nonsing_inv_mul`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.html#Matrix.nonsing_inv_mul); Mathlib: [`Matrix.inv_eq_left_inv`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.html#Matrix.inv_eq_left_inv).
  [`mul_inv_eq_one_of_det_ne_zero`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L143) (proved);
  [`eq_of_mul_eq_mul_of_det_ne_zero`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L152) (proved);
  [`exists_mul_eq_mul_ne_of_det_eq_zero`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L162)
  (proved). Upstream: Mathlib: `Matrix.mul_nonsing_inv`, Mathlib: `Matrix.nonsing_inv_mul`, Mathlib:
  `Matrix.inv_eq_left_inv` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). With the prose of
  §1.2(vi): cancellation for `det A ≠ 0`, and a counterexample for `det A = 0`.
- [1.2.E61](https://dlmf.nist.gov/1.2.E61):; [`DLMF.AlgebraicAnalytic.eq_inv_mulVec_of_mulVec_eq`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L184) (proved); [`DLMF.AlgebraicAnalytic.existsUnique_mulVec_eq`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L174) (proved); [`DLMF.AlgebraicAnalytic.mulVec_eq_iff_of_mulVec_eq`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L192) (proved); [`DLMF.AlgebraicAnalytic.not_exists_or_infinite_of_det_eq_zero`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L199) (proved); Mathlib: [`Matrix.exists_mulVec_eq_zero_iff`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/ToLinearEquiv.html#Matrix.exists_mulVec_eq_zero_iff).
  [`existsUnique_mulVec_eq`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L174) (proved);
  [`eq_inv_mulVec_of_mulVec_eq`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L184) (proved);
  [`mulVec_eq_iff_of_mulVec_eq`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L192) (proved);
  [`not_exists_or_infinite_of_det_eq_zero`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L202)
  (proved). Upstream: Mathlib: `Matrix.exists_mulVec_eq_zero_iff` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). With the prose: unique
  solution for `det A ≠ 0`; for `det A = 0` either none or infinitely many (infinite field), and the
  solution set is a particular solution plus the kernel.
- [1.2.E62](https://dlmf.nist.gov/1.2.E62): upstream only: Mathlib: `Matrix.trace` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E63](https://dlmf.nist.gov/1.2.E63): upstream only: Mathlib: `Matrix.trace_smul` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E64](https://dlmf.nist.gov/1.2.E64): upstream only: Mathlib: `Matrix.trace_add` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E65](https://dlmf.nist.gov/1.2.E65): upstream only: Mathlib: `Matrix.trace_mul_comm`
  (pointers in [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E66](https://dlmf.nist.gov/1.2.E66): upstream only: Mathlib: `Ring.lie_def`, Mathlib:; Mathlib: [`lie_skew`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Lie/Basic.html#lie_skew).
  `lie_skew` (pointers in [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E67](https://dlmf.nist.gov/1.2.E67):; [`DLMF.AlgebraicAnalytic.l2_opNorm_isGreatest`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L219) (proved); Mathlib: [`Matrix.l2_opNorm_def`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/CStarAlgebra/Matrix.html#Matrix.l2_opNorm_def); Mathlib: [`Matrix.l2_opNorm_mulVec`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/CStarAlgebra/Matrix.html#Matrix.l2_opNorm_mulVec).
  [`l2_opNorm_isGreatest`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L219) (proved). Upstream:
  Mathlib: `Matrix.l2_opNorm_def`, Mathlib: `Matrix.l2_opNorm_mulVec` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). The `l²` operator norm
  (scoped instance `Matrix.Norms.L2Operator`); `l2_opNorm_isGreatest` proves that the maximum over
  the unit sphere is attained.
- [1.2.E68](https://dlmf.nist.gov/1.2.E68): upstream only: Mathlib: `Matrix.l2_opNorm_mul` (pointers
  in [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E69](https://dlmf.nist.gov/1.2.E69): upstream only: Mathlib:; Mathlib: [`Matrix.instL2OpNormedAddCommGroup`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/CStarAlgebra/Matrix.html#Matrix.instL2OpNormedAddCommGroup).
  `Matrix.instL2OpNormedAddCommGroup` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). `norm_add_le` for the
  scoped `l²` operator norm.
- [1.2.E70](https://dlmf.nist.gov/1.2.E70):; [`DLMF.AlgebraicAnalytic.exists_eigenvector_iff_det_sub_eq_zero`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L236) (proved); Mathlib: [`Module.End.HasEigenvector`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Eigenspace/Basic.html#Module.End.HasEigenvector).
  [`exists_eigenvector_iff_det_sub_eq_zero`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L240)
  (proved). Upstream: Mathlib: `Module.End.HasEigenvector` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.2.E71](https://dlmf.nist.gov/1.2.E71):; [`DLMF.AlgebraicAnalytic.exists_eigenvector_iff_det_sub_eq_zero`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L236) (proved); Mathlib: [`Module.End.hasEigenvalue_iff_isRoot_charpoly`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Eigenspace/Charpoly.html#Module.End.hasEigenvalue_iff_isRoot_charpoly).
  [`exists_eigenvector_iff_det_sub_eq_zero`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L240)
  (proved). Upstream: Mathlib: `Module.End.hasEigenvalue_iff_isRoot_charpoly` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). Mathlib's characteristic
  polynomial is `det(XI - A)`; the tagged theorem uses DLMF's `det(A - λI)`.
- [1.2.E72](https://dlmf.nist.gov/1.2.E72):; [`DLMF.AlgebraicAnalytic.exists_eigenvector_iff_det_sub_eq_zero`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L236) (proved).
  [`exists_eigenvector_iff_det_sub_eq_zero`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L240)
  (proved).
- [1.2.E73](https://dlmf.nist.gov/1.2.E73):; [`DLMF.AlgebraicAnalytic.inv_mul_mul_eq_diagonal_iff`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L246) (proved); [`DLMF.AlgebraicAnalytic.nonDefective_iff_exists_diagonal`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L272) (proved); Mathlib: [`Matrix.linearIndependent_col_iff_isUnit`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.html#Matrix.linearIndependent_col_iff_isUnit).
  [`inv_mul_mul_eq_diagonal_iff`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L246) (proved);
  [`nonDefective_iff_exists_diagonal`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L272) (proved).
  Upstream: Mathlib: `Matrix.linearIndependent_col_iff_isUnit` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). Columns of `S` are
  eigenvectors iff `S⁻¹AS` is diagonal, and non-defective iff diagonalizable.
- [1.2.E74](https://dlmf.nist.gov/1.2.E74):; [`DLMF.AlgebraicAnalytic.det_eq_prod_of_inv_mul_mul_eq_diagonal`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L293) (proved); Mathlib: [`Matrix.det_eq_prod_roots_charpoly`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Charpoly/Eigs.html#Matrix.det_eq_prod_roots_charpoly); Mathlib: [`Matrix.det_conj'`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.html#Matrix.det_conj').
  [`det_eq_prod_of_inv_mul_mul_eq_diagonal`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L297)
  (proved). Upstream: Mathlib: `Matrix.det_eq_prod_roots_charpoly`, Mathlib: `Matrix.det_conj'`
  (pointers in [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). DLMF form
  for diagonalizable `A`; Mathlib has it for every matrix over an algebraically closed field.
- [1.2.E75](https://dlmf.nist.gov/1.2.E75):; [`DLMF.AlgebraicAnalytic.trace_eq_sum_of_inv_mul_mul_eq_diagonal`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L301) (proved); Mathlib: [`Matrix.trace_eq_sum_roots_charpoly`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Charpoly/Eigs.html#Matrix.trace_eq_sum_roots_charpoly); Mathlib: [`Matrix.trace_conj'`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.html#Matrix.trace_conj').
  [`trace_eq_sum_of_inv_mul_mul_eq_diagonal`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L304)
  (proved). Upstream: Mathlib: `Matrix.trace_eq_sum_roots_charpoly`, Mathlib: `Matrix.trace_conj'`
  (pointers in [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). DLMF form
  for diagonalizable `A`; Mathlib has it for every matrix over an algebraically closed field.
- [1.2.E76](https://dlmf.nist.gov/1.2.E76):; [`DLMF.AlgebraicAnalytic.hasSum_exp_matrix`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L308) (proved); Mathlib: [`NormedSpace.exp_eq_tsum`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Algebra/Exponential.html#NormedSpace.exp_eq_tsum); Mathlib: [`NormedSpace.exp_series_hasSum_exp'`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Algebra/Exponential.html#NormedSpace.exp_series_hasSum_exp').
  [`hasSum_exp_matrix`](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L308) (proved). Upstream:
  Mathlib: `NormedSpace.exp_eq_tsum`, Mathlib: `NormedSpace.exp_series_hasSum_exp'` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). Convergence in norm and
  entry by entry.
- [1.2.E77](https://dlmf.nist.gov/1.2.E77): upstream only: TauCeti: `Matrix.det_exp` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). TauCeti: every square
  matrix over `ℝ` or `ℂ`, as DLMF's final remark states (Hall 2015, Thm 2.12).

## [§1.3 Determinants, Linear Operators, and Spectral Expansions](https://dlmf.nist.gov/1.3)

- [1.3.i](https://dlmf.nist.gov/1.3.i): upstream only: Mathlib: `Matrix.det_permute`, Mathlib:; Mathlib: [`Matrix.det_permute'`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.html#Matrix.det_permute'); Mathlib: [`Matrix.det_zero_of_row_eq`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.html#Matrix.det_zero_of_row_eq); Mathlib: [`Matrix.det_zero_of_column_eq`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.html#Matrix.det_zero_of_column_eq); Mathlib: [`Matrix.det_updateRow_smul`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.html#Matrix.det_updateRow_smul); Mathlib: [`Matrix.det_updateCol_smul`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.html#Matrix.det_updateCol_smul); Mathlib: [`Matrix.det_updateRow_add_smul_self`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.html#Matrix.det_updateRow_add_smul_self); Mathlib: [`Matrix.det_updateCol_add_smul_self`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.html#Matrix.det_updateCol_add_smul_self); Mathlib: [`Matrix.det_of_isUpperTriangular`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Block.html#Matrix.det_of_isUpperTriangular); Mathlib: [`Matrix.det_of_isLowerTriangular`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Block.html#Matrix.det_of_isLowerTriangular); Mathlib: [`Matrix.det_diagonal`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.html#Matrix.det_diagonal).
  `Matrix.det_permute'`, Mathlib: `Matrix.det_zero_of_row_eq`, Mathlib:
  `Matrix.det_zero_of_column_eq`, Mathlib: `Matrix.det_updateRow_smul`, Mathlib:
  `Matrix.det_updateCol_smul`, Mathlib: `Matrix.det_updateRow_add_smul_self`, Mathlib:
  `Matrix.det_updateCol_add_smul_self`, Mathlib: `Matrix.det_of_isUpperTriangular`, Mathlib:
  `Matrix.det_of_isLowerTriangular`, Mathlib: `Matrix.det_diagonal` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.3.iii](https://dlmf.nist.gov/1.3.iii):; [`DLMF.AlgebraicAnalytic.HasInfiniteDet`](DLMF/AlgebraicAnalytic/Algebra/Defs.lean#L87) (definition); [`DLMF.AlgebraicAnalytic.IsHillType.exists_hasInfiniteDet`](DLMF/AlgebraicAnalytic/Algebra/Determinants.lean#L482) (admitted).
  [`HasInfiniteDet`](DLMF/AlgebraicAnalytic/Algebra/Defs.lean#L87) (definition);
  [`IsHillType.exists_hasInfiniteDet`](DLMF/AlgebraicAnalytic/Algebra/Determinants.lean#L484)
  (admitted). The convergence theorem for Hill type is admitted. Proof route: with `r_j = ∑_k
  |a_{j,k} - δ_{j,k}|`, expand by permutations to get `|D_m - D_n| ≤ ∏_{|j|≤m}(1 + r_j) -
  ∏_{|j|≤n}(1 + r_j)` for `m > n`, so `(D_n)` is Cauchy.
- [1.3.iv](https://dlmf.nist.gov/1.3.iv): upstream only: Mathlib: `Matrix.mulVecLin`, Mathlib:
  `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`, Mathlib:
  `Matrix.isSymmetric_toEuclideanLin_iff`, Mathlib: `LinearMap.IsSymmetric.conj_eigenvalue_eq_self`,
  Mathlib: `Matrix.IsHermitian.eigenvalues`, Mathlib: `Matrix.IsHermitian.eigenvectorBasis`,
  Mathlib: `Matrix.IsHermitian.mulVec_eigenvectorBasis`, Mathlib:
  `Matrix.IsHermitian.eigenvectorUnitary`, Mathlib: `Matrix.IsHermitian.spectral_theorem`, Mathlib:
  `LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.3.E1](https://dlmf.nist.gov/1.3.E1): upstream only: Mathlib: `Matrix.det_fin_two` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.3.E2](https://dlmf.nist.gov/1.3.E2): upstream only: Mathlib: `Matrix.det_fin_three`, Mathlib:; Mathlib: [`Matrix.det_succ_row_zero`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.html#Matrix.det_succ_row_zero).
  `Matrix.det_succ_row_zero` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.3.E3](https://dlmf.nist.gov/1.3.E3): upstream only: Mathlib:; Mathlib: [`Matrix.adjugate_fin_succ_eq_det_submatrix`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Adjugate.html#Matrix.adjugate_fin_succ_eq_det_submatrix).
  `Matrix.adjugate_fin_succ_eq_det_submatrix` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). Mathlib's `adjugate` is
  the transposed cofactor matrix, `adjugate A k j = A_{jk}`.
- [1.3.E4](https://dlmf.nist.gov/1.3.E4): upstream only: Mathlib: `Matrix.det_succ_row`, Mathlib:; Mathlib: [`Matrix.det_succ_column`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.html#Matrix.det_succ_column).
  `Matrix.det_succ_column` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.3.E5](https://dlmf.nist.gov/1.3.E5): upstream only: Mathlib: `Matrix.det_transpose` (pointers
  in [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.3.E6](https://dlmf.nist.gov/1.3.E6):; [`DLMF.AlgebraicAnalytic.det_inv_eq_one_div`](DLMF/AlgebraicAnalytic/Algebra/Determinants.lean#L51) (proved); Mathlib: [`Matrix.det_nonsing_inv`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.html#Matrix.det_nonsing_inv).
  [`det_inv_eq_one_div`](DLMF/AlgebraicAnalytic/Algebra/Determinants.lean#L51) (proved). Upstream:
  Mathlib: `Matrix.det_nonsing_inv` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). Over a field,
  unconditional with Lean's `0⁻¹ = 0` (stronger than DLMF).
- [1.3.E7](https://dlmf.nist.gov/1.3.E7): upstream only: Mathlib: `Matrix.det_mul` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.3.E8](https://dlmf.nist.gov/1.3.E8):; [`DLMF.AlgebraicAnalytic.det_fin_two_sq_le`](DLMF/AlgebraicAnalytic/Algebra/Determinants.lean#L60) (proved).
  [`det_fin_two_sq_le`](DLMF/AlgebraicAnalytic/Algebra/Determinants.lean#L60) (proved).
- [1.3.E9](https://dlmf.nist.gov/1.3.E9):; [`DLMF.AlgebraicAnalytic.det_sq_le_prod_sum_sq`](DLMF/AlgebraicAnalytic/Algebra/Determinants.lean#L120) (proved).
  [`det_sq_le_prod_sum_sq`](DLMF/AlgebraicAnalytic/Algebra/Determinants.lean#L120) (proved). Proved
  by Gram–Schmidt orthonormalization of the rows.
- [1.3.E10](https://dlmf.nist.gov/1.3.E10):; [`DLMF.AlgebraicAnalytic.det_sq_eq_prod_sum_sq_iff`](DLMF/AlgebraicAnalytic/Algebra/Determinants.lean#L135) (proved).
  [`det_sq_eq_prod_sum_sq_iff`](DLMF/AlgebraicAnalytic/Algebra/Determinants.lean#L135) (proved).
  Proved: equality iff the rows are pairwise orthogonal or one row vanishes.
- [1.3.E11](https://dlmf.nist.gov/1.3.E11):; [`DLMF.AlgebraicAnalytic.det_alternant_swap`](DLMF/AlgebraicAnalytic/Algebra/Determinants.lean#L194) (proved); Mathlib: [`Matrix.det_permute`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.html#Matrix.det_permute).
  [`det_alternant_swap`](DLMF/AlgebraicAnalytic/Algebra/Determinants.lean#L194) (proved). Upstream:
  Mathlib: `Matrix.det_permute` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). An interchange of two
  variables `x_i`, `x_{i'}`.
- [1.3.E12](https://dlmf.nist.gov/1.3.E12):; [`DLMF.AlgebraicAnalytic.det_alternant₂_swap`](DLMF/AlgebraicAnalytic/Algebra/Determinants.lean#L206) (proved).
  [`det_alternant₂_swap`](DLMF/AlgebraicAnalytic/Algebra/Determinants.lean#L206) (proved).
- [1.3.E13](https://dlmf.nist.gov/1.3.E13): upstream only: Mathlib: `Matrix.det_vandermonde`
  (pointers in [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).
- [1.3.E14](https://dlmf.nist.gov/1.3.E14):; [`DLMF.AlgebraicAnalytic.det_cauchy`](DLMF/AlgebraicAnalytic/Algebra/Determinants.lean#L242) (proved).
  [`det_cauchy`](DLMF/AlgebraicAnalytic/Algebra/Determinants.lean#L242) (proved). Any field, `a_j ≠
  b_k`. Proved by factoring the Cauchy matrix through two Vandermonde matrices.
- [1.3.E15](https://dlmf.nist.gov/1.3.E15):; [`DLMF.AlgebraicAnalytic.det_circulant`](DLMF/AlgebraicAnalytic/Algebra/Determinants.lean#L309) (proved).
  [`det_circulant`](DLMF/AlgebraicAnalytic/Algebra/Determinants.lean#L309) (proved). DLMF's
  circulant (entry `a_{k-j}`) is the transpose of Mathlib's `Matrix.circulant`; `ω_k = e^{2πik/n}`,
  indices from `0`. Proved by diagonalizing with the Fourier (Vandermonde) matrix.
- [1.3.E16](https://dlmf.nist.gov/1.3.E16):; [`DLMF.AlgebraicAnalytic.det_krattenthaler`](DLMF/AlgebraicAnalytic/Algebra/Determinants.lean#L400) (proved).
  [`det_krattenthaler`](DLMF/AlgebraicAnalytic/Algebra/Determinants.lean#L400) (proved). Indices
  shifted to `Fin n`; any commutative ring. Proof: each column is a polynomial of degree `< n` in
  `x_j`, so the determinant is the Vandermonde times a coefficient determinant; the coefficient
  determinant is computed for generic `a`, `b` (in `MvPolynomial`) by evaluating at `x_j = -a_j`,
  where the matrix is triangular, and cancelling the Vandermonde in `a`, then specialized.
- [1.3.E17](https://dlmf.nist.gov/1.3.E17):; [`DLMF.AlgebraicAnalytic.det_krattenthaler`](DLMF/AlgebraicAnalytic/Algebra/Determinants.lean#L400) (proved).
  [`det_krattenthaler`](DLMF/AlgebraicAnalytic/Algebra/Determinants.lean#L400) (proved). See
  1.3.E16.
- [1.3.E18](https://dlmf.nist.gov/1.3.E18):; [`DLMF.AlgebraicAnalytic.truncDet`](DLMF/AlgebraicAnalytic/Algebra/Defs.lean#L80) (definition).
  [`truncDet`](DLMF/AlgebraicAnalytic/Algebra/Defs.lean#L80) (definition). Row/column index `i : Fin
  (2n+1)` carries the DLMF index `i - n`.
- [1.3.E19](https://dlmf.nist.gov/1.3.E19):; [`DLMF.AlgebraicAnalytic.IsHillType`](DLMF/AlgebraicAnalytic/Algebra/Defs.lean#L94) (definition); [`DLMF.AlgebraicAnalytic.IsHillType.exists_hasInfiniteDet`](DLMF/AlgebraicAnalytic/Algebra/Determinants.lean#L482) (admitted).
  [`IsHillType`](DLMF/AlgebraicAnalytic/Algebra/Defs.lean#L94) (definition);
  [`IsHillType.exists_hasInfiniteDet`](DLMF/AlgebraicAnalytic/Algebra/Determinants.lean#L484)
  (admitted). Absolute summability of `a_{j,k} - δ_{j,k}` over `ℤ × ℤ`; the convergence theorem is
  admitted.
- [1.3.E20](https://dlmf.nist.gov/1.3.E20): upstream only: Mathlib: `OrthonormalBasis.sum_repr'`
  (pointers in [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)). DLMF's `c_i
  = ⟨u, a_i⟩` is Mathlib's `⟪a_i, u⟫`.
- [1.3.E21](https://dlmf.nist.gov/1.3.E21): upstream only: Mathlib:; Mathlib: [`OrthonormalBasis.sum_sq_norm_inner_right`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/PiL2.html#OrthonormalBasis.sum_sq_norm_inner_right).
  `OrthonormalBasis.sum_sq_norm_inner_right` (pointers in
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean)).

### Prose, informal and excluded items (part g1a)

- [1.2.i](https://dlmf.nist.gov/1.2.i), [1.2.ii](https://dlmf.nist.gov/1.2.ii) and
  [1.2.iii](https://dlmf.nist.gov/1.2.iii): covered by their numbered formulas 1.2.1–1.2.16; no
  separate prose tag.
- [1.2.vi](https://dlmf.nist.gov/1.2.vi): the remarks that the eigenvalues of a real matrix may be; Mathlib: [`Matrix.IsLowerTriangular`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Block.html#Matrix.IsLowerTriangular).
  complex and that the multiplicities of the eigenvalues add up to `n` are informal; the latter is
  Mathlib's `Matrix.charpoly_natDegree_eq_dim` (degree of the characteristic polynomial).
- [1.3.ii](https://dlmf.nist.gov/1.3.ii): covered by its numbered formulas 1.3.11–1.3.17; no
  separate prose tag.
- [1.3.iv](https://dlmf.nist.gov/1.3.iv): the introductory description of a matrix as a linear; Mathlib: [`Matrix.toEuclideanLin_conjTranspose_eq_adjoint`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Adjoint.html#Matrix.toEuclideanLin_conjTranspose_eq_adjoint); Mathlib: [`Matrix.isSymmetric_toEuclideanLin_iff`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Matrix/Hermitian.html#Matrix.isSymmetric_toEuclideanLin_iff); Mathlib: [`LinearMap.IsSymmetric.conj_eigenvalue_eq_self`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Spectrum.html#LinearMap.IsSymmetric.conj_eigenvalue_eq_self); Mathlib: [`Matrix.IsHermitian.eigenvalues`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Matrix/Spectrum.html#Matrix.IsHermitian.eigenvalues); Mathlib: [`Matrix.IsHermitian.eigenvectorBasis`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Matrix/Spectrum.html#Matrix.IsHermitian.eigenvectorBasis); Mathlib: [`Matrix.IsHermitian.mulVec_eigenvectorBasis`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Matrix/Spectrum.html#Matrix.IsHermitian.mulVec_eigenvectorBasis); Mathlib: [`Matrix.IsHermitian.eigenvectorUnitary`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Matrix/Spectrum.html#Matrix.IsHermitian.eigenvectorUnitary); Mathlib: [`Matrix.IsHermitian.spectral_theorem`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Matrix/Spectrum.html#Matrix.IsHermitian.spectral_theorem); Mathlib: [`LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/JointEigenspace.html#LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute).
  operator on `ℂⁿ` is notation; the statements are covered by the pointers listed above.
- No item of §§1.1–1.3 is excluded as numerical or graphical.

### Validation (part g1a)

- `lake build` of the six modules succeeds; the only warning is `declaration uses 'sorry'` for
  `IsHillType.exists_hasInfiniteDet`. Strict checks (`lake env lean -DautoImplicit=false
  -DrelaxedAutoImplicit=false`) of all six modules report nothing else. No line exceeds 100
  characters; `git diff --check` is clean.
- `#print axioms` on a sample of proved theorems (`det_krattenthaler`, `det_cauchy`,
  `det_circulant`, `det_sq_eq_prod_sum_sq_iff`, `exists_div_prod_pow_sub_eq_sum`,
  `tendsto_weightedPowerMean_zero`, `hasSum_exp_matrix`) shows only `propext`, `Classical.choice`
  and `Quot.sound`.
- All 117 `dlmf_upstream` pointers elaborate (the declaration names are checked by the command).
- Numerical checks (mpmath, `n ≤ 6`, random real data; scratch scripts `num.py`, `num2.py`) of the
  Cauchy determinant 1.3.14, the circulant 1.3.15 and Krattenthaler's formula 1.3.17 before
  acquisition, all to working precision.

## Part g1b: §§1.4–1.7

This part covers the definitions, numbered formulas and analytical assertions in prose of
[DLMF §§1.4–1.7](https://dlmf.nist.gov/1.4) (calculus of one and several variables, vectors
and vector-valued functions including the theorems of Green, Gauss and Stokes, and
inequalities), version 1.2.8, checked on 2026-10-27, by agent g1b (helper prefix `g1b_`). The
Lean code is in `DLMF/AlgebraicAnalytic/Calculus/` (namespace `DLMF.AlgebraicAnalytic`). The modules, in import order, are
[Defs](DLMF/AlgebraicAnalytic/Calculus/Defs.lean) (all definitions; imports Mathlib only),
[OneVariable](DLMF/AlgebraicAnalytic/Calculus/OneVariable.lean) (§1.4; imports `Defs`),
[SeveralVariables](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean) (§1.5; imports `Defs`),
[Vectors](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean) (§1.6(i)–(iii); imports `SeveralVariables`),
[VectorIntegrals](DLMF/AlgebraicAnalytic/Calculus/VectorIntegrals.lean) (§1.6(iv)–(v), Gauss and Green's identities;
imports `Vectors`),
[GreenStokes](DLMF/AlgebraicAnalytic/Calculus/GreenStokes.lean) (Green's area formulas and Stokes; imports
`VectorIntegrals` and `TauCeti.Analysis.Green.IndexOne`),
[Inequalities](DLMF/AlgebraicAnalytic/Calculus/Inequalities.lean) (§1.7; imports Mathlib only) and
[MathlibCoverage](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean) (`dlmf_upstream` pointers; imports
`DLMF.Core.Upstream`, Mathlib and TauCeti).

**Counts.** §§1.4–1.7 have 155 numbered equations (1.4: 41, namely 1.4.E1–1.4.E38 and
1.4.E23_1–1.4.E23_3; 1.5: 43; 1.6: 60; 1.7: 11). In scope: 155. Covered: 154, of which 94 by
project declarations only, 23 by project declarations and an upstream pointer, and 37 by upstream
pointers only; 1.6.E43 is notation (no statement). In addition 13 prose IDs (1.4.i, 1.4.ii,
1.4.iii, 1.4.iv, 1.4.v, 1.4.vii, 1.4.viii, 1.5.i, 1.6.i, 1.6.ii, 1.6.iv, 1.6.v,
1.7.i) carry tags or pointers. The 169 declarations of the seven Lean modules are
28 definitions (all in `Defs`) and 141 theorems: 104 proved (of which 22 untagged `g1b_`
helpers) and 37 direct admissions. There are 78 `dlmf_upstream` pointers.

Module admissions (`grep -cE 'by sorry|:= sorry|^\s*(·\s*)?sorry\s*$|exact sorry'`) and
declarations:

- [Defs](DLMF/AlgebraicAnalytic/Calculus/Defs.lean): 0 admissions; 28 definitions.
- [OneVariable](DLMF/AlgebraicAnalytic/Calculus/OneVariable.lean): 7 admissions; 22 theorems: 15 proved, 7 admitted.
- [SeveralVariables](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean): 12 admissions; 30 theorems: 18 proved,
  12 admitted.
- [Vectors](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean): 1 admission; 39 theorems: 38 proved, 1 admitted.
- [VectorIntegrals](DLMF/AlgebraicAnalytic/Calculus/VectorIntegrals.lean): 3 admissions; 26 theorems: 23 proved,
  3 admitted.
- [GreenStokes](DLMF/AlgebraicAnalytic/Calculus/GreenStokes.lean): 1 admission; 3 theorems: 2 proved, 1 admitted.
- [Inequalities](DLMF/AlgebraicAnalytic/Calculus/Inequalities.lean): 13 admissions; 21 theorems: 8 proved, 13 admitted.
- [MathlibCoverage](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean): 0 admissions; 78 `dlmf_upstream` pointers.

Proved theorems that depend on admissions: `integral_normalDomain_swap` (1.5.35, from the
admitted 1.5.31 and 1.5.34), `integral_green_first_identity` and
`integral_green_second_identity` (1.6.59–1.6.60, from the admitted Gauss theorem 1.6.58).

### Domains, conventions and source corrections (part g1b)

- Partial derivatives (1.5.3–1.5.4) are section derivatives `partialDeriv i f x`, the derivative
  of `t ↦ f (Function.update x i t)` at `x i`, on `Fin n → ℝ`; functions of two variables use
  `ℝ × ℝ` and the explicit sections. `partialDeriv_eq_fderiv` links them to `fderiv`.
- Vectors in §1.6 are `Fin 3 → ℝ` with Mathlib's `dotProduct` and `crossProduct`; the magnitude
  is `vecNorm a = √(a · a)` (Mathlib's norm on `Fin 3 → ℝ` is the sup norm); `vecNorm_eq_norm`
  links it to the Euclidean norm of `EuclideanSpace ℝ (Fin 3)`, used for angles (1.6.4, 1.6.9).
- Spherical coordinates 1.5.16 follow DLMF (physicists' `(ρ, θ, φ)`, `θ` the polar angle).
  Mathlib's `polarCoord` (pointer for 1.5.10) uses `φ ∈ (-π, π)`.
- Path, line and surface integrals are defined by their parametric formulas (1.6.36–1.6.38,
  1.6.48, 1.6.54–1.6.55). The line-integral reparametrization 1.6.39 is proved without
  monotonicity of `h` (stronger than DLMF).
- Green's theorem 1.6.44 is TauCeti's `green_ac_index_one` (stronger than DLMF: closed absolutely
  continuous curves, the region being the points of winding number 1; DLMF's simple closed
  curves reduce to this by the Jordan curve theorem, not in Mathlib). The area formulas below
  1.6.44 are proved from it. Stokes's theorem 1.6.57 is stated for a `C²` parametrization over
  such a TauCeti region.
- Gauss's theorem 1.6.58 is stated with the structure `HasPiecewiseSmoothBoundary` (compact `V`
  whose frontier is covered by finitely many injective `C¹` smooth patches with disjoint
  interiors and outward normals). Green's identities 1.6.59–1.6.60 are proved from it.
- The change of variables 1.5.42–1.5.43 is proved with an exceptional null set on which
  injectivity may fail (stronger than DLMF's boundary exception).
- Means in §1.7(iii) are written out explicitly (the §1.2(iv) definitions belong to part g1a).
- **1.7.11 (correction).** DLMF states `exp(∫₀¹ ln f) < ∫₀¹ f`, which is false for constant
  `f` (equality). Acquired as `≤` (proved, `exp_integral_log_le_integral`) and with strict
  inequality for `f` not a.e. constant (`exp_integral_log_lt_integral`, admitted).
- **1.7.1–1.7.3 equality conditions (correction).** DLMF's "equality iff `a_j = c b_j`"
  (resp. `a_j^p = c b_j^q`) misses `b = 0`, `a ≠ 0`, where equality holds. Acquired in the
  symmetric form "`A a_j = B b_j` with `A`, `B` not both zero", as DLMF itself writes the
  integral versions 1.7.4–1.7.6. Integral equality conditions are stated almost everywhere.

### Numbered formulas and prose items (part g1b)

## [§1.4 Calculus of One Variable](https://dlmf.nist.gov/1.4)

- [1.4.i](https://dlmf.nist.gov/1.4.i): upstream: [`MonotoneOn`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L56) (exact: nondecreasing on I (StrictMonoOn, AntitoneOn, StrictAntiOn for the other cases))
- [1.4.ii](https://dlmf.nist.gov/1.4.ii): [`DLMF.AlgebraicAnalytic.IsSimpleDiscontinuity`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L55) (definition); [`DLMF.AlgebraicAnalytic.IsPiecewiseContinuousOn`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L61) (definition); upstream: [`ContinuousOn`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L62) (exact: C(a, b) and C[a, b] are ContinuousOn f (Ioo a b) and ContinuousOn f (Icc a b))
- [1.4.E1](https://dlmf.nist.gov/1.4.E1): [`DLMF.AlgebraicAnalytic.continuousWithinAt_Ici_iff_eps_delta`](DLMF/AlgebraicAnalytic/Calculus/OneVariable.lean#L49) (proved); upstream: [`ContinuousWithinAt`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L58) (exact: right continuity at c is ContinuousWithinAt f (Ici c) c)
- [1.4.E2](https://dlmf.nist.gov/1.4.E2): [`DLMF.AlgebraicAnalytic.continuousWithinAt_Ici_iff_eps_delta`](DLMF/AlgebraicAnalytic/Calculus/OneVariable.lean#L49) (proved)
- [1.4.E3](https://dlmf.nist.gov/1.4.E3): upstream: [`continuousAt_iff_continuous_left_right`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L60) (exact: continuity at c iff continuity from the left (Iic c) and the right (Ici c))
- [1.4.iii](https://dlmf.nist.gov/1.4.iii): upstream: [`ContDiffOn`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L73) (exact: f ∈ Cⁿ(I) is ContDiffOn ℝ n f I, C^∞ is n = ∞); upstream: [`IsLocalMax.deriv_eq_zero`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L76) (exact: f'(c) = 0 at a local maximum (IsLocalMin.deriv_eq_zero for minima)); upstream: [`monotoneOn_of_deriv_nonneg`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L80) (exact: f' ≥ 0 on (a, b) implies f nondecreasing (see also antitoneOn_of_deriv_nonpos))
- [1.4.E4](https://dlmf.nist.gov/1.4.E4): upstream: [`hasDerivAt_iff_tendsto_slope_zero`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L66) (exact: f'(x) = lim_{h→0} (f(x + h) - f(x))/h)
- [1.4.E5](https://dlmf.nist.gov/1.4.E5): upstream: [`deriv_add`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L68) (exact: for f, g differentiable at x)
- [1.4.E6](https://dlmf.nist.gov/1.4.E6): upstream: [`deriv_mul`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L69) (exact: for f, g differentiable at x)
- [1.4.E7](https://dlmf.nist.gov/1.4.E7): upstream: [`deriv_div`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L70) (exact: for f, g differentiable at x, g(x) ≠ 0)
- [1.4.E8](https://dlmf.nist.gov/1.4.E8): upstream: [`iteratedDeriv_succ`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L71) (exact: f^(n) = d/dx f^(n-1) (with 1.4.E9))
- [1.4.E9](https://dlmf.nist.gov/1.4.E9): upstream: [`iteratedDeriv_succ`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L72) (exact: iteratedDeriv (n + 1) f = deriv (iteratedDeriv n f))
- [1.4.E10](https://dlmf.nist.gov/1.4.E10): upstream: [`deriv_comp`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L75) (exact: chain rule h'(x) = f'(g(x)) g'(x))
- [1.4.E11](https://dlmf.nist.gov/1.4.E11): upstream: [`exists_deriv_eq_slope`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L78) (exact: mean value theorem, f continuous on [a, b], differentiable on (a, b))
- [1.4.E12](https://dlmf.nist.gov/1.4.E12): upstream: [`iteratedDeriv_mul`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L82) (exact: Leibniz's formula, f and g n times differentiable (ContDiffAt) at x)
- [1.4.E13](https://dlmf.nist.gov/1.4.E13): [`DLMF.AlgebraicAnalytic.iteratedDeriv_comp_faaDiBruno`](DLMF/AlgebraicAnalytic/Calculus/OneVariable.lean#L72) (admitted)
- [1.4.E14](https://dlmf.nist.gov/1.4.E14): [`DLMF.AlgebraicAnalytic.lhopital_atTop_nhdsNE`](DLMF/AlgebraicAnalytic/Calculus/OneVariable.lean#L87) (admitted)
- [1.4.E15](https://dlmf.nist.gov/1.4.E15): [`DLMF.AlgebraicAnalytic.lhopital_atTop_nhdsNE`](DLMF/AlgebraicAnalytic/Calculus/OneVariable.lean#L87) (admitted); upstream: [`deriv.lhopital_zero_nhdsNE`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L84) (partial: the case 0/0 of L'Hôpital's rule; the case ∞/∞ is lhopital_atTop_nhdsNE)
- [1.4.iv](https://dlmf.nist.gov/1.4.iv): upstream: [`intervalIntegral.integral_eq_sub_of_hasDerivAt`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L88) (exact: F' = f gives ∫ f = F + C (also 1.4.26))
- [1.4.E16](https://dlmf.nist.gov/1.4.E16): upstream: [`intervalIntegral.integral_mul_deriv_eq_deriv_mul`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L90) (different convention: definite form of integration by parts, ∫ₐᵇ u v' = u v|ₐᵇ - ∫ₐᵇ u' v)
- [1.4.E17](https://dlmf.nist.gov/1.4.E17): [`DLMF.AlgebraicAnalytic.hasDerivAt_zpow_succ_div`](DLMF/AlgebraicAnalytic/Calculus/OneVariable.lean#L103) (proved); [`DLMF.AlgebraicAnalytic.hasDerivAt_pow_succ_div`](DLMF/AlgebraicAnalytic/Calculus/OneVariable.lean#L119) (proved); [`DLMF.AlgebraicAnalytic.hasDerivAt_log_abs`](DLMF/AlgebraicAnalytic/Calculus/OneVariable.lean#L129) (proved); upstream: [`integral_pow`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L92) (special case: definite integral ∫ₐᵇ xⁿ = (bⁿ⁺¹ - aⁿ⁺¹)/(n + 1))
- [1.4.v](https://dlmf.nist.gov/1.4.v): [`DLMF.AlgebraicAnalytic.tendsto_integral_of_tendsto_integral_abs`](DLMF/AlgebraicAnalytic/Calculus/OneVariable.lean#L159) (proved); upstream: [`BoxIntegral.integrable_of_continuousOn`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L95) (exact: continuous functions are Riemann integrable); upstream: [`BoxIntegral.integrable_of_bounded_and_ae_continuousWithinAt`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L97) (stronger: bounded and a.e. continuous (covers piecewise continuous) is Riemann integrable); upstream: [`MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_tendsto`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L104) (exact: absolute convergence of ∫ₐ^∞ gives integrability); upstream: [`LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L116) (exact: Jordan decomposition f = g - h, g, h nondecreasing); upstream: [`variationOnFromTo.monotoneOn`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L118) (exact: x ↦ 𝒱_{a,x}(f) is nondecreasing (variationOnFromTo.sub_self_monotoneOn for 𝒱 - f))
- [1.4.E18](https://dlmf.nist.gov/1.4.E18): upstream: [`BoxIntegral.HasIntegral`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L93) (different convention: Riemann integral via tagged box partitions with IntegrationParams.Riemann)
- [1.4.E19](https://dlmf.nist.gov/1.4.E19): [`DLMF.AlgebraicAnalytic.integral_const_mul_add_const_mul`](DLMF/AlgebraicAnalytic/Calculus/OneVariable.lean#L137) (proved)
- [1.4.E20](https://dlmf.nist.gov/1.4.E20): upstream: [`intervalIntegral.integral_symm`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L99) (exact: ∫ₐᵇ f = -∫ᵇₐ f)
- [1.4.E21](https://dlmf.nist.gov/1.4.E21): upstream: [`intervalIntegral.integral_add_adjacent_intervals`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L100) (exact: for f integrable on both intervals)
- [1.4.E22](https://dlmf.nist.gov/1.4.E22): upstream: [`MeasureTheory.intervalIntegral_tendsto_integral_Ioi`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L102) (stronger: for f integrable on (a, ∞), ∫ₐᵇ f → ∫_(a,∞) f as b → ∞)
- [1.4.E23](https://dlmf.nist.gov/1.4.E23): [`DLMF.AlgebraicAnalytic.tendsto_integral_nhdsLT_of_integrableOn`](DLMF/AlgebraicAnalytic/Calculus/OneVariable.lean#L145) (proved)
- [1.4.E23_1](https://dlmf.nist.gov/1.4.E23_1): [`DLMF.AlgebraicAnalytic.stieltjes_measure_eq_withDensity`](DLMF/AlgebraicAnalytic/Calculus/OneVariable.lean#L172) (proved)
- [1.4.E23_2](https://dlmf.nist.gov/1.4.E23_2): [`DLMF.AlgebraicAnalytic.setIntegral_stieltjes_eq_integral_mul`](DLMF/AlgebraicAnalytic/Calculus/OneVariable.lean#L185) (proved)
- [1.4.E23_3](https://dlmf.nist.gov/1.4.E23_3): [`DLMF.AlgebraicAnalytic.setIntegral_withDensity_add_dirac`](DLMF/AlgebraicAnalytic/Calculus/OneVariable.lean#L197) (admitted)
- [1.4.E24](https://dlmf.nist.gov/1.4.E24): [`DLMF.AlgebraicAnalytic.HasCauchyPrincipalValue`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L79) (definition); [`DLMF.AlgebraicAnalytic.hasCauchyPrincipalValue_of_intervalIntegrable`](DLMF/AlgebraicAnalytic/Calculus/OneVariable.lean#L209) (proved)
- [1.4.E25](https://dlmf.nist.gov/1.4.E25): [`DLMF.AlgebraicAnalytic.HasPrincipalValueAtInfinity`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L89) (definition); [`DLMF.AlgebraicAnalytic.hasPrincipalValueAtInfinity_of_integrable`](DLMF/AlgebraicAnalytic/Calculus/OneVariable.lean#L252) (proved)
- [1.4.E26](https://dlmf.nist.gov/1.4.E26): upstream: [`intervalIntegral.integral_eq_sub_of_hasDerivAt`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L106) (stronger: F' = f on [a, b] with f integrable (continuity not needed))
- [1.4.E27](https://dlmf.nist.gov/1.4.E27): upstream: [`intervalIntegral.integral_hasDerivAt_right`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L108) (exact: d/dx ∫ₐˣ f = f(x) at points of continuity)
- [1.4.E28](https://dlmf.nist.gov/1.4.E28): upstream: [`intervalIntegral.integral_comp_mul_deriv`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L110) (special case: φ' continuous on [a, b] and f continuous)
- [1.4.E29](https://dlmf.nist.gov/1.4.E29): [`DLMF.AlgebraicAnalytic.exists_integral_mul_eq_mul_integral`](DLMF/AlgebraicAnalytic/Calculus/OneVariable.lean#L260) (admitted)
- [1.4.E30](https://dlmf.nist.gov/1.4.E30): [`DLMF.AlgebraicAnalytic.exists_integral_mul_eq_secondMeanValue`](DLMF/AlgebraicAnalytic/Calculus/OneVariable.lean#L269) (admitted)
- [1.4.E31](https://dlmf.nist.gov/1.4.E31): [`DLMF.AlgebraicAnalytic.iterate_primitive_eq_integral`](DLMF/AlgebraicAnalytic/Calculus/OneVariable.lean#L280) (admitted)
- [1.4.E32](https://dlmf.nist.gov/1.4.E32): upstream: [`MeasureTheory.MemLp`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L112) (exact: square integrability is MemLp f 2, ‖f‖₂ is eLpNorm f 2)
- [1.4.E33](https://dlmf.nist.gov/1.4.E33): upstream: [`eVariationOn`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L114) (exact: total variation, the supremum over finite increasing families in the set)
- [1.4.E34](https://dlmf.nist.gov/1.4.E34): [`DLMF.AlgebraicAnalytic.eVariationOn_eq_integral_norm_deriv`](DLMF/AlgebraicAnalytic/Calculus/OneVariable.lean#L289) (admitted)
- [1.4.E35](https://dlmf.nist.gov/1.4.E35): upstream: [`taylorWithinEval`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L122) (exact: the Taylor polynomial ∑ f⁽ᵏ⁾(a)(x - a)ᵏ/k!)
- [1.4.E36](https://dlmf.nist.gov/1.4.E36): upstream: [`taylor_mean_remainder_lagrange`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L123) (exact: Lagrange remainder, f ∈ Cⁿ[a, x] with f⁽ⁿ⁾ differentiable on (a, x))
- [1.4.E37](https://dlmf.nist.gov/1.4.E37): upstream: [`taylor_integral_remainder`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L125) (exact: integral remainder, f ∈ Cⁿ⁺¹[a, x])
- [1.4.vii](https://dlmf.nist.gov/1.4.vii): [`DLMF.AlgebraicAnalytic.exists_isMaxOn_Icc_endpoint_or_isLocalMax`](DLMF/AlgebraicAnalytic/Calculus/OneVariable.lean#L302) (proved); [`DLMF.AlgebraicAnalytic.exists_isMinOn_Icc_endpoint_or_isLocalMin`](DLMF/AlgebraicAnalytic/Calculus/OneVariable.lean#L316) (proved); upstream: [`isLocalMax_of_deriv_deriv_neg`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L126) (exact: f'(x₀) = 0, f''(x₀) < 0 gives a local maximum (isLocalMin_of_deriv_deriv_pos))
- [1.4.viii](https://dlmf.nist.gov/1.4.viii): [`DLMF.AlgebraicAnalytic.convexOn_Ioo_iff_deriv2_nonneg`](DLMF/AlgebraicAnalytic/Calculus/OneVariable.lean#L332) (proved); [`DLMF.AlgebraicAnalytic.convexOn_Ioo_iff_tangent_le`](DLMF/AlgebraicAnalytic/Calculus/OneVariable.lean#L349) (proved); upstream: [`convexOn_of_deriv2_nonneg`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L129) (exact: f'' ≥ 0 implies convexity)
- [1.4.E38](https://dlmf.nist.gov/1.4.E38): upstream: [`ConvexOn`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L128) (exact: ConvexOn ℝ (Ioo a b) f)

## [§1.5 Calculus of Two or More Variables](https://dlmf.nist.gov/1.5)

- [1.5.i](https://dlmf.nist.gov/1.5.i): [`DLMF.AlgebraicAnalytic.IsPiecewiseContinuousOnProd`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L70) (definition); [`DLMF.AlgebraicAnalytic.exists_implicitFunction`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L227) (admitted); upstream: [`eventually_apply_eq_iff_implicitFunctionOfBivariate`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L137) (stronger: bivariate implicit function theorem in Banach spaces, zero set = graph of ψ); upstream: [`hasStrictFDerivAt_implicitFunctionOfBivariate`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L139) (partial: ψ'(a) = -F_y⁻¹ F_x at the base point only)
- [1.5.E1](https://dlmf.nist.gov/1.5.E1): [`DLMF.AlgebraicAnalytic.continuousAt_prod_iff_eps_delta`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L113) (proved); upstream: [`Metric.continuousAt_iff`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L132) (exact: with the sup norm on ℝ × ℝ this is the ε-δ form 1.5.2)
- [1.5.E2](https://dlmf.nist.gov/1.5.E2): [`DLMF.AlgebraicAnalytic.continuousAt_prod_iff_eps_delta`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L113) (proved)
- [1.5.E3](https://dlmf.nist.gov/1.5.E3): [`DLMF.AlgebraicAnalytic.partialDeriv`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L98) (definition); [`DLMF.AlgebraicAnalytic.hasDerivAt_partialDeriv`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L48) (proved); [`DLMF.AlgebraicAnalytic.partialDeriv_eq_fderiv`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L60) (proved); [`DLMF.AlgebraicAnalytic.hasDerivAt_section_fst`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L133) (proved)
- [1.5.E4](https://dlmf.nist.gov/1.5.E4): [`DLMF.AlgebraicAnalytic.partialDeriv`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L98) (definition); [`DLMF.AlgebraicAnalytic.hasDerivAt_section_snd`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L142) (proved)
- [1.5.E5](https://dlmf.nist.gov/1.5.E5): [`DLMF.AlgebraicAnalytic.deriv_section_comm`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L151) (proved)
- [1.5.E6](https://dlmf.nist.gov/1.5.E6): [`DLMF.AlgebraicAnalytic.partialDeriv_comm`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L101) (proved); [`DLMF.AlgebraicAnalytic.deriv_section_comm`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L151) (proved); upstream: [`ContDiffAt.isSymmSndFDerivAt`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L134) (stronger: symmetry of the second Fréchet derivative of a C² function)
- [1.5.E7](https://dlmf.nist.gov/1.5.E7): [`DLMF.AlgebraicAnalytic.hasDerivAt_comp_prod`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L180) (proved); upstream: [`HasFDerivAt.comp_hasDerivAt`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L136) (stronger: chain rule in Banach spaces)
- [1.5.E8](https://dlmf.nist.gov/1.5.E8): [`DLMF.AlgebraicAnalytic.deriv_comp_prod_section`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L198) (proved)
- [1.5.E9](https://dlmf.nist.gov/1.5.E9): [`DLMF.AlgebraicAnalytic.hasDerivAt_comp_pi`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L209) (proved)
- [1.5.E10](https://dlmf.nist.gov/1.5.E10): upstream: [`polarCoord`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L141) (different convention: polar coordinates with φ ∈ (-π, π) (DLMF 0 ≤ φ ≤ 2π))
- [1.5.E11](https://dlmf.nist.gov/1.5.E11): [`DLMF.AlgebraicAnalytic.partialDeriv_polar`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L242) (proved)
- [1.5.E12](https://dlmf.nist.gov/1.5.E12): [`DLMF.AlgebraicAnalytic.partialDeriv_polar`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L242) (proved)
- [1.5.E13](https://dlmf.nist.gov/1.5.E13): [`DLMF.AlgebraicAnalytic.laplacian_polar`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L288) (admitted)
- [1.5.E14](https://dlmf.nist.gov/1.5.E14): [`DLMF.AlgebraicAnalytic.cylindricalCoord`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L119) (definition)
- [1.5.E15](https://dlmf.nist.gov/1.5.E15): [`DLMF.AlgebraicAnalytic.laplacian_cylindrical`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L302) (admitted)
- [1.5.E16](https://dlmf.nist.gov/1.5.E16): [`DLMF.AlgebraicAnalytic.sphericalCoord`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L125) (definition)
- [1.5.E17](https://dlmf.nist.gov/1.5.E17): [`DLMF.AlgebraicAnalytic.laplacian_spherical`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L315) (admitted)
- [1.5.E18](https://dlmf.nist.gov/1.5.E18): [`DLMF.AlgebraicAnalytic.taylor_isLittleO_prod`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L331) (admitted)
- [1.5.E19](https://dlmf.nist.gov/1.5.E19): [`DLMF.AlgebraicAnalytic.isLocalMin_of_hessian_posDef`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L344) (admitted); [`DLMF.AlgebraicAnalytic.isLocalMax_of_hessian_negDef`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L357) (admitted)
- [1.5.E20](https://dlmf.nist.gov/1.5.E20): [`DLMF.AlgebraicAnalytic.isLocalMin_of_hessian_posDef`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L344) (admitted); [`DLMF.AlgebraicAnalytic.isLocalMax_of_hessian_negDef`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L357) (admitted)
- [1.5.E21](https://dlmf.nist.gov/1.5.E21): [`DLMF.AlgebraicAnalytic.isLocalMin_of_hessian_posDef`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L344) (admitted); [`DLMF.AlgebraicAnalytic.isLocalMax_of_hessian_negDef`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L357) (admitted)
- [1.5.E22](https://dlmf.nist.gov/1.5.E22): [`DLMF.AlgebraicAnalytic.hasDerivAt_integral_variable_limits`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L371) (admitted)
- [1.5.E23](https://dlmf.nist.gov/1.5.E23): [`DLMF.AlgebraicAnalytic.hasDerivAt_improper_integral_of_tendstoUniformlyOn`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L388) (admitted)
- [1.5.E24](https://dlmf.nist.gov/1.5.E24): [`DLMF.AlgebraicAnalytic.hasDerivAt_improper_integral_of_tendstoUniformlyOn`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L388) (admitted); upstream: [`hasDerivAt_integral_of_dominated_loc_of_deriv_le`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L143) (different convention: differentiation under the integral sign with a dominating function)
- [1.5.E25](https://dlmf.nist.gov/1.5.E25): upstream: [`BoxIntegral.TaggedPrepartition`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L145) (different convention: tagged partitions of a box (the grid partitions of 1.5.25–1.5.26))
- [1.5.E26](https://dlmf.nist.gov/1.5.E26): upstream: [`BoxIntegral.TaggedPrepartition`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L147) (different convention: tagged partitions of a box (the grid partitions of 1.5.25–1.5.26))
- [1.5.E27](https://dlmf.nist.gov/1.5.E27): upstream: [`BoxIntegral.HasIntegral`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L149) (different convention: Riemann double integral via tagged box partitions)
- [1.5.E28](https://dlmf.nist.gov/1.5.E28): upstream: [`Set.indicator`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L151) (exact: f* = D.indicator f, the extension by zero)
- [1.5.E29](https://dlmf.nist.gov/1.5.E29): upstream: [`MeasureTheory.integral_indicator`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L152) (exact: ∬_D f = ∬_R f* with f* the extension by zero)
- [1.5.E30](https://dlmf.nist.gov/1.5.E30): [`DLMF.AlgebraicAnalytic.setIntegral_normalDomain_fst`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L406) (admitted)
- [1.5.E31](https://dlmf.nist.gov/1.5.E31): [`DLMF.AlgebraicAnalytic.setIntegral_normalDomain_fst`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L406) (admitted)
- [1.5.E32](https://dlmf.nist.gov/1.5.E32): [`DLMF.AlgebraicAnalytic.setIntegral_normalDomain_fst`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L406) (admitted)
- [1.5.E33](https://dlmf.nist.gov/1.5.E33): [`DLMF.AlgebraicAnalytic.setIntegral_normalDomain_snd`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L417) (admitted)
- [1.5.E34](https://dlmf.nist.gov/1.5.E34): [`DLMF.AlgebraicAnalytic.setIntegral_normalDomain_snd`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L417) (admitted)
- [1.5.E35](https://dlmf.nist.gov/1.5.E35): [`DLMF.AlgebraicAnalytic.integral_normalDomain_swap`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L428) (proved from admissions)
- [1.5.E36](https://dlmf.nist.gov/1.5.E36): [`DLMF.AlgebraicAnalytic.integral_integral_swap_of_abs`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L445) (proved); upstream: [`MeasureTheory.integral_integral_swap`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L154) (stronger: Fubini's theorem for f integrable on the product)
- [1.5.E37](https://dlmf.nist.gov/1.5.E37): [`DLMF.AlgebraicAnalytic.setIntegral_normalDomain_three`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L463) (admitted)
- [1.5.E38](https://dlmf.nist.gov/1.5.E38): [`DLMF.AlgebraicAnalytic.jacobianDet2`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L105) (definition)
- [1.5.E39](https://dlmf.nist.gov/1.5.E39): [`DLMF.AlgebraicAnalytic.jacobianDet2_polar`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L482) (proved)
- [1.5.E40](https://dlmf.nist.gov/1.5.E40): [`DLMF.AlgebraicAnalytic.jacobianDet3`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L112) (definition)
- [1.5.E41](https://dlmf.nist.gov/1.5.E41): [`DLMF.AlgebraicAnalytic.jacobianDet3_spherical`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L489) (proved)
- [1.5.E42](https://dlmf.nist.gov/1.5.E42): [`DLMF.AlgebraicAnalytic.integral_image_eq_integral_abs_det_of_injOn_diff_null`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L500) (proved); upstream: [`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L156) (special case: Φ one-to-one on all of D* (no exceptional null set))
- [1.5.E43](https://dlmf.nist.gov/1.5.E43): [`DLMF.AlgebraicAnalytic.integral_image_eq_integral_abs_det_of_injOn_diff_null`](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L500) (proved)

## [§1.6 Vectors and Vector-Valued Functions](https://dlmf.nist.gov/1.6)

- [1.6.i](https://dlmf.nist.gov/1.6.i): [`DLMF.AlgebraicAnalytic.volume_parallelepiped_eq_abs_triple_product`](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean#L114) (proved); [`DLMF.AlgebraicAnalytic.hausdorffMeasure_parallelogram`](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean#L124) (admitted); upstream: [`triple_product_eq_det`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L172) (exact: a · (b × c) = det (a, b, c))
- [1.6.E1](https://dlmf.nist.gov/1.6.E1): upstream: [`Matrix.vecCons`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L160) (different convention: vectors of ℝ³ are Fin 3 → ℝ, written ![a₁, a₂, a₃])
- [1.6.E2](https://dlmf.nist.gov/1.6.E2): [`DLMF.AlgebraicAnalytic.dotProduct_fin_three`](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean#L42) (proved); upstream: [`dotProduct`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L162) (exact: a ⬝ᵥ b = ∑ aᵢ bᵢ)
- [1.6.E3](https://dlmf.nist.gov/1.6.E3): [`DLMF.AlgebraicAnalytic.vecNorm`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L135) (definition); [`DLMF.AlgebraicAnalytic.vecNorm_eq_norm`](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean#L48) (proved)
- [1.6.E4](https://dlmf.nist.gov/1.6.E4): [`DLMF.AlgebraicAnalytic.cos_angle_eq_dotProduct_div`](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean#L60) (proved); upstream: [`InnerProductGeometry.cos_angle`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L163) (exact: in EuclideanSpace ℝ (Fin 3))
- [1.6.E5](https://dlmf.nist.gov/1.6.E5): upstream: [`Pi.basisFun`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L164) (exact: the unit vectors i, j, k are Pi.single 0 1, …)
- [1.6.E6](https://dlmf.nist.gov/1.6.E6): upstream: [`pi_eq_sum_univ`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L165) (exact: a = ∑ aᵢ eᵢ (also 1.6.13))
- [1.6.E7](https://dlmf.nist.gov/1.6.E7): [`DLMF.AlgebraicAnalytic.cross_unit_vectors`](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean#L67) (proved)
- [1.6.E8](https://dlmf.nist.gov/1.6.E8): [`DLMF.AlgebraicAnalytic.cross_unit_vectors_neg`](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean#L75) (proved)
- [1.6.E9](https://dlmf.nist.gov/1.6.E9): [`DLMF.AlgebraicAnalytic.cross_eq_sum_unit_vectors`](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean#L83) (proved); [`DLMF.AlgebraicAnalytic.vecNorm_cross`](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean#L92) (proved); [`DLMF.AlgebraicAnalytic.cross_orthogonal_rightHanded`](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean#L102) (proved); upstream: [`cross_apply`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L167) (exact: components of a × b)
- [1.6.E10](https://dlmf.nist.gov/1.6.E10): upstream: [`cross_cross_eq_smul_sub_smul'`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L168) (exact: a × (b × c) = (a · c) b - (b · a) c)
- [1.6.E11](https://dlmf.nist.gov/1.6.E11): upstream: [`cross_cross_eq_smul_sub_smul`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L170) (exact: (a × b) × c = (a · c) b - (b · c) a)
- [1.6.ii](https://dlmf.nist.gov/1.6.ii): [`DLMF.AlgebraicAnalytic.triple_product_eq_sum_leviCivita`](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean#L180) (proved)
- [1.6.E12](https://dlmf.nist.gov/1.6.E12): [`DLMF.AlgebraicAnalytic.dotProduct_fin_three`](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean#L42) (proved); upstream: [`dotProduct`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L173) (exact: aⱼbⱼ = ∑ aⱼbⱼ)
- [1.6.E13](https://dlmf.nist.gov/1.6.E13): upstream: [`pi_eq_sum_univ`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L166) (exact: aⱼ eⱼ = a)
- [1.6.E14](https://dlmf.nist.gov/1.6.E14): [`DLMF.AlgebraicAnalytic.leviCivita`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L141) (definition); [`DLMF.AlgebraicAnalytic.leviCivita_perm`](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean#L136) (proved); [`DLMF.AlgebraicAnalytic.leviCivita_eq_zero_of_not_injective`](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean#L144) (proved)
- [1.6.E15](https://dlmf.nist.gov/1.6.E15): [`DLMF.AlgebraicAnalytic.leviCivita_values`](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean#L150) (proved)
- [1.6.E16](https://dlmf.nist.gov/1.6.E16): [`DLMF.AlgebraicAnalytic.sum_leviCivita_mul_leviCivita`](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean#L157) (proved)
- [1.6.E17](https://dlmf.nist.gov/1.6.E17): [`DLMF.AlgebraicAnalytic.single_cross_single`](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean#L166) (proved)
- [1.6.E18](https://dlmf.nist.gov/1.6.E18): [`DLMF.AlgebraicAnalytic.cross_apply_eq_sum_leviCivita`](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean#L174) (proved)
- [1.6.E19](https://dlmf.nist.gov/1.6.E19): [`DLMF.AlgebraicAnalytic.grad`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L150) (definition)
- [1.6.E20](https://dlmf.nist.gov/1.6.E20): [`DLMF.AlgebraicAnalytic.grad`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L150) (definition)
- [1.6.E21](https://dlmf.nist.gov/1.6.E21): [`DLMF.AlgebraicAnalytic.divergence`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L156) (definition)
- [1.6.E22](https://dlmf.nist.gov/1.6.E22): [`DLMF.AlgebraicAnalytic.curl`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L161) (definition)
- [1.6.E23](https://dlmf.nist.gov/1.6.E23): [`DLMF.AlgebraicAnalytic.grad_mul`](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean#L258) (proved)
- [1.6.E24](https://dlmf.nist.gov/1.6.E24): [`DLMF.AlgebraicAnalytic.grad_div`](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean#L267) (proved)
- [1.6.E25](https://dlmf.nist.gov/1.6.E25): [`DLMF.AlgebraicAnalytic.divergence_smul`](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean#L276) (proved)
- [1.6.E26](https://dlmf.nist.gov/1.6.E26): [`DLMF.AlgebraicAnalytic.divergence_cross`](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean#L289) (proved)
- [1.6.E27](https://dlmf.nist.gov/1.6.E27): [`DLMF.AlgebraicAnalytic.divergence_curl`](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean#L309) (proved)
- [1.6.E28](https://dlmf.nist.gov/1.6.E28): [`DLMF.AlgebraicAnalytic.curl_smul`](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean#L324) (proved)
- [1.6.E29](https://dlmf.nist.gov/1.6.E29): [`DLMF.AlgebraicAnalytic.curl_grad`](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean#L338) (proved)
- [1.6.E30](https://dlmf.nist.gov/1.6.E30): [`DLMF.AlgebraicAnalytic.laplacian`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L168) (definition); [`DLMF.AlgebraicAnalytic.laplacian_eq_divergence_grad`](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean#L349) (proved)
- [1.6.E31](https://dlmf.nist.gov/1.6.E31): [`DLMF.AlgebraicAnalytic.laplacian_mul`](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean#L355) (proved)
- [1.6.E32](https://dlmf.nist.gov/1.6.E32): [`DLMF.AlgebraicAnalytic.divergence_grad_cross_grad`](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean#L386) (proved)
- [1.6.E33](https://dlmf.nist.gov/1.6.E33): [`DLMF.AlgebraicAnalytic.divergence_smul_grad_sub`](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean#L407) (proved)
- [1.6.E34](https://dlmf.nist.gov/1.6.E34): [`DLMF.AlgebraicAnalytic.vectorLaplacian`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L174) (definition); [`DLMF.AlgebraicAnalytic.curl_curl`](DLMF/AlgebraicAnalytic/Calculus/Vectors.lean#L426) (proved)
- [1.6.iv](https://dlmf.nist.gov/1.6.iv): [`DLMF.AlgebraicAnalytic.IsSimpleClosedPath`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L197) (definition); [`DLMF.AlgebraicAnalytic.volume_real_eq_green_area`](DLMF/AlgebraicAnalytic/Calculus/GreenStokes.lean#L46) (proved)
- [1.6.E35](https://dlmf.nist.gov/1.6.E35): [`DLMF.AlgebraicAnalytic.pathLength`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L181) (definition)
- [1.6.E36](https://dlmf.nist.gov/1.6.E36): [`DLMF.AlgebraicAnalytic.pathLength`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L181) (definition)
- [1.6.E37](https://dlmf.nist.gov/1.6.E37): [`DLMF.AlgebraicAnalytic.pathIntegral`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L187) (definition)
- [1.6.E38](https://dlmf.nist.gov/1.6.E38): [`DLMF.AlgebraicAnalytic.lineIntegral`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L192) (definition)
- [1.6.E39](https://dlmf.nist.gov/1.6.E39): [`DLMF.AlgebraicAnalytic.lineIntegral_comp`](DLMF/AlgebraicAnalytic/Calculus/VectorIntegrals.lean#L63) (proved)
- [1.6.E40](https://dlmf.nist.gov/1.6.E40): [`DLMF.AlgebraicAnalytic.lineIntegral_comp_reverse`](DLMF/AlgebraicAnalytic/Calculus/VectorIntegrals.lean#L78) (proved)
- [1.6.E41](https://dlmf.nist.gov/1.6.E41): [`DLMF.AlgebraicAnalytic.pathIntegral_comp`](DLMF/AlgebraicAnalytic/Calculus/VectorIntegrals.lean#L88) (proved)
- [1.6.E42](https://dlmf.nist.gov/1.6.E42): [`DLMF.AlgebraicAnalytic.lineIntegral_grad`](DLMF/AlgebraicAnalytic/Calculus/VectorIntegrals.lean#L122) (proved)
- [1.6.E43](https://dlmf.nist.gov/1.6.E43): no statement (notation): the plane field `F = F₁ i + F₂ j`; Green's theorem 1.6.44 takes its components as the fields `P`, `Q` of TauCeti's `green_ac_index_one`.
- [1.6.E44](https://dlmf.nist.gov/1.6.E44): upstream: [`TauCeti.Green.green_ac_index_one`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L174) (stronger: closed absolutely continuous curve, winding number 1 on the enclosed region)
- [1.6.v](https://dlmf.nist.gov/1.6.v): [`DLMF.AlgebraicAnalytic.IsSmoothSurfaceAt`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L216) (definition); [`DLMF.AlgebraicAnalytic.HasPiecewiseSmoothBoundary`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L237) (definition); [`DLMF.AlgebraicAnalytic.tangent_dotProduct_cross`](DLMF/AlgebraicAnalytic/Calculus/VectorIntegrals.lean#L149) (proved); [`DLMF.AlgebraicAnalytic.surfaceArea_comp_diffeomorph`](DLMF/AlgebraicAnalytic/Calculus/VectorIntegrals.lean#L350) (admitted)
- [1.6.E45](https://dlmf.nist.gov/1.6.E45): [`DLMF.AlgebraicAnalytic.tangentU`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L205) (definition)
- [1.6.E46](https://dlmf.nist.gov/1.6.E46): [`DLMF.AlgebraicAnalytic.tangentU`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L205) (definition)
- [1.6.E47](https://dlmf.nist.gov/1.6.E47): [`DLMF.AlgebraicAnalytic.tangentV`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L211) (definition)
- [1.6.E48](https://dlmf.nist.gov/1.6.E48): [`DLMF.AlgebraicAnalytic.surfaceArea`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L221) (definition)
- [1.6.E49](https://dlmf.nist.gov/1.6.E49): [`DLMF.AlgebraicAnalytic.vecNorm_tangent_cross`](DLMF/AlgebraicAnalytic/Calculus/VectorIntegrals.lean#L167) (proved)
- [1.6.E50](https://dlmf.nist.gov/1.6.E50): [`DLMF.AlgebraicAnalytic.vecNorm_tangent_cross_sphere`](DLMF/AlgebraicAnalytic/Calculus/VectorIntegrals.lean#L192) (proved)
- [1.6.E51](https://dlmf.nist.gov/1.6.E51): [`DLMF.AlgebraicAnalytic.vecNorm_tangent_cross_graph`](DLMF/AlgebraicAnalytic/Calculus/VectorIntegrals.lean#L228) (proved); [`DLMF.AlgebraicAnalytic.surfaceArea_graph`](DLMF/AlgebraicAnalytic/Calculus/VectorIntegrals.lean#L250) (proved)
- [1.6.E52](https://dlmf.nist.gov/1.6.E52): [`DLMF.AlgebraicAnalytic.vecNorm_tangent_cross_revolution_x`](DLMF/AlgebraicAnalytic/Calculus/VectorIntegrals.lean#L271) (proved); [`DLMF.AlgebraicAnalytic.surfaceArea_revolution_x`](DLMF/AlgebraicAnalytic/Calculus/VectorIntegrals.lean#L296) (proved)
- [1.6.E53](https://dlmf.nist.gov/1.6.E53): [`DLMF.AlgebraicAnalytic.vecNorm_tangent_cross_revolution_y`](DLMF/AlgebraicAnalytic/Calculus/VectorIntegrals.lean#L310) (proved); [`DLMF.AlgebraicAnalytic.surfaceArea_revolution_y`](DLMF/AlgebraicAnalytic/Calculus/VectorIntegrals.lean#L336) (proved)
- [1.6.E54](https://dlmf.nist.gov/1.6.E54): [`DLMF.AlgebraicAnalytic.surfaceIntegral`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L226) (definition)
- [1.6.E55](https://dlmf.nist.gov/1.6.E55): [`DLMF.AlgebraicAnalytic.fluxIntegral`](DLMF/AlgebraicAnalytic/Calculus/Defs.lean#L231) (definition)
- [1.6.E56](https://dlmf.nist.gov/1.6.E56): [`DLMF.AlgebraicAnalytic.fluxIntegral_comp_diffeomorph`](DLMF/AlgebraicAnalytic/Calculus/VectorIntegrals.lean#L360) (admitted)
- [1.6.E57](https://dlmf.nist.gov/1.6.E57): [`DLMF.AlgebraicAnalytic.fluxIntegral_curl_eq_lineIntegral`](DLMF/AlgebraicAnalytic/Calculus/GreenStokes.lean#L84) (admitted); upstream: [`TauCeti.integralTopForm_mextDeriv`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L176) (different convention: Stokes for compactly supported C¹ forms on oriented manifolds)
- [1.6.E58](https://dlmf.nist.gov/1.6.E58): [`DLMF.AlgebraicAnalytic.integral_divergence_eq_sum_fluxIntegral`](DLMF/AlgebraicAnalytic/Calculus/VectorIntegrals.lean#L375) (admitted); upstream: [`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L178) (special case: divergence theorem on a rectangular box in ℝⁿ)
- [1.6.E59](https://dlmf.nist.gov/1.6.E59): [`DLMF.AlgebraicAnalytic.integral_green_first_identity`](DLMF/AlgebraicAnalytic/Calculus/VectorIntegrals.lean#L397) (proved from admissions)
- [1.6.E60](https://dlmf.nist.gov/1.6.E60): [`DLMF.AlgebraicAnalytic.integral_green_second_identity`](DLMF/AlgebraicAnalytic/Calculus/VectorIntegrals.lean#L420) (proved from admissions)

## [§1.7 Inequalities](https://dlmf.nist.gov/1.7)

- [1.7.i](https://dlmf.nist.gov/1.7.i): [`DLMF.AlgebraicAnalytic.sum_sq_le_of_forall_sq_sum_mul_le`](DLMF/AlgebraicAnalytic/Calculus/Inequalities.lean#L58) (proved); [`DLMF.AlgebraicAnalytic.sum_rpow_le_of_forall_inner_le`](DLMF/AlgebraicAnalytic/Calculus/Inequalities.lean#L97) (admitted)
- [1.7.E1](https://dlmf.nist.gov/1.7.E1): [`DLMF.AlgebraicAnalytic.sq_sum_mul_eq_iff`](DLMF/AlgebraicAnalytic/Calculus/Inequalities.lean#L50) (admitted); upstream: [`Finset.sum_mul_sq_le_sq_mul_sq`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L182) (exact: (∑ aⱼbⱼ)² ≤ (∑ aⱼ²)(∑ bⱼ²))
- [1.7.E2](https://dlmf.nist.gov/1.7.E2): [`DLMF.AlgebraicAnalytic.inner_eq_Lp_mul_Lq_iff`](DLMF/AlgebraicAnalytic/Calculus/Inequalities.lean#L87) (admitted); upstream: [`Real.inner_le_Lp_mul_Lq_of_nonneg`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L183) (exact: Hölder for aⱼ, bⱼ ≥ 0)
- [1.7.E3](https://dlmf.nist.gov/1.7.E3): [`DLMF.AlgebraicAnalytic.Lp_add_ge_of_lt_one`](DLMF/AlgebraicAnalytic/Calculus/Inequalities.lean#L108) (admitted); [`DLMF.AlgebraicAnalytic.Lp_add_eq_iff`](DLMF/AlgebraicAnalytic/Calculus/Inequalities.lean#L117) (admitted); upstream: [`Real.Lp_add_le_of_nonneg`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L184) (exact: Minkowski for p ≥ 1, aⱼ, bⱼ ≥ 0)
- [1.7.E4](https://dlmf.nist.gov/1.7.E4): [`DLMF.AlgebraicAnalytic.sq_integral_mul_le`](DLMF/AlgebraicAnalytic/Calculus/Inequalities.lean#L128) (proved); [`DLMF.AlgebraicAnalytic.sq_integral_mul_eq_iff`](DLMF/AlgebraicAnalytic/Calculus/Inequalities.lean#L155) (admitted)
- [1.7.E5](https://dlmf.nist.gov/1.7.E5): [`DLMF.AlgebraicAnalytic.integral_mul_eq_Lp_mul_Lq_iff`](DLMF/AlgebraicAnalytic/Calculus/Inequalities.lean#L164) (admitted); upstream: [`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L185) (exact: Hölder for integrals, f, g ≥ 0 in Lᵖ, L^q)
- [1.7.E6](https://dlmf.nist.gov/1.7.E6): [`DLMF.AlgebraicAnalytic.integral_add_rpow_le`](DLMF/AlgebraicAnalytic/Calculus/Inequalities.lean#L177) (admitted); [`DLMF.AlgebraicAnalytic.integral_add_rpow_ge_of_lt_one`](DLMF/AlgebraicAnalytic/Calculus/Inequalities.lean#L188) (admitted); [`DLMF.AlgebraicAnalytic.integral_add_rpow_eq_iff`](DLMF/AlgebraicAnalytic/Calculus/Inequalities.lean#L198) (admitted); upstream: [`MeasureTheory.eLpNorm_add_le`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L187) (different convention: Minkowski for eLpNorm, p ≥ 1)
- [1.7.E7](https://dlmf.nist.gov/1.7.E7): [`DLMF.AlgebraicAnalytic.harmMean_le_geomMean_le_arithMean`](DLMF/AlgebraicAnalytic/Calculus/Inequalities.lean#L211) (proved); [`DLMF.AlgebraicAnalytic.geomMean_eq_arithMean_iff`](DLMF/AlgebraicAnalytic/Calculus/Inequalities.lean#L258) (proved); upstream: [`Real.geom_mean_le_arith_mean_weighted`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L189) (exact: G ≤ A (weighted form)); upstream: [`Real.harm_mean_le_geom_mean`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L190) (exact: H ≤ G); upstream: [`Real.geom_mean_eq_arith_mean_weighted_iff_of_pos`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L191) (exact: G = A iff all aⱼ are equal (positive weights))
- [1.7.E8](https://dlmf.nist.gov/1.7.E8): [`DLMF.AlgebraicAnalytic.min_le_powerMean_le_max`](DLMF/AlgebraicAnalytic/Calculus/Inequalities.lean#L265) (admitted)
- [1.7.E9](https://dlmf.nist.gov/1.7.E9): [`DLMF.AlgebraicAnalytic.powerMean_le_powerMean`](DLMF/AlgebraicAnalytic/Calculus/Inequalities.lean#L279) (admitted); upstream: [`Real.rpow_arith_mean_le_arith_mean_rpow`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L193) (special case: M(1) ≤ M(p), p ≥ 1)
- [1.7.E10](https://dlmf.nist.gov/1.7.E10): [`DLMF.AlgebraicAnalytic.convexOn_Ioo_map_integral_le`](DLMF/AlgebraicAnalytic/Calculus/Inequalities.lean#L292) (proved); upstream: [`ConvexOn.map_integral_le`](DLMF/AlgebraicAnalytic/Calculus/MathlibCoverage.lean#L194) (partial: Jensen for a probability measure, φ convex and continuous on a closed convex set)
- [1.7.E11](https://dlmf.nist.gov/1.7.E11): [`DLMF.AlgebraicAnalytic.exp_integral_log_le_integral`](DLMF/AlgebraicAnalytic/Calculus/Inequalities.lean#L339) (proved); [`DLMF.AlgebraicAnalytic.exp_integral_log_lt_integral`](DLMF/AlgebraicAnalytic/Calculus/Inequalities.lean#L373) (admitted)
### Prose, informal and excluded items (part g1b)

- [1.4.iv](https://dlmf.nist.gov/1.4.iv): the pointers to §§4.10, 4.26, 4.40 and to tables of
  integrals are no statement (references only).
- [1.4.v](https://dlmf.nist.gov/1.4.v): the description of Stieltjes, Lebesgue and
  Lebesgue–Stieltjes integrals is acquired through 1.4.23_1–1.4.23_3 and Mathlib's
  `MeasureTheory` integral; the references to the literature are no statement.
- [1.4.viii](https://dlmf.nist.gov/1.4.viii): Figure 1.4.2 is excluded: graphics.
- [1.5.ii](https://dlmf.nist.gov/1.5.ii): the remark on physicists' notation is no statement
  (notation); the pointers to other coordinate systems (§§12.17, 14.19, …) are no statement
  (references only).
- [1.6.ii](https://dlmf.nist.gov/1.6.ii): the Einstein summation convention is notation; the
  sums are written out.
- [1.6.E43](https://dlmf.nist.gov/1.6.E43): no statement (notation).

### Validation (part g1b)

- The seven modules build with `lake build DLMF.AlgebraicAnalytic.Calculus.<Module>` and each
  of the eight files passes `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false`
  without errors or warnings other than `declaration uses 'sorry'`. There are no axioms, no
  `native_decide`, and no `sorry` in definitions or `g1b_` helpers. No line exceeds 100
  characters.
- `#print axioms` for a sample of proved theorems (`hasCauchyPrincipalValue_of_intervalIntegrable`,
  `convexOn_Ioo_iff_deriv2_nonneg`, `partialDeriv_comm`,
  `integral_image_eq_integral_abs_det_of_injOn_diff_null`, `jacobianDet3_spherical`,
  `curl_curl`, `volume_parallelepiped_eq_abs_triple_product`, `lineIntegral_comp`,
  `surfaceArea_revolution_x`, `volume_real_eq_green_area`, `convexOn_Ioo_map_integral_le`,
  `sq_integral_mul_le`, `geomMean_eq_arithMean_iff`) shows only `propext`, `Classical.choice`
  and `Quot.sound`; `integral_green_second_identity` also shows `sorryAx` through Gauss's
  theorem.
- Every `dlmf_upstream` name was checked by elaborating `MathlibCoverage`.

## Part g1c: §§1.8–1.10

This part covers the definitions, numbered formulas and analytical assertions in prose of
[DLMF §1.8](https://dlmf.nist.gov/1.8) (Fourier series),
[§1.9](https://dlmf.nist.gov/1.9) (calculus of a complex variable) and
[§1.10](https://dlmf.nist.gov/1.10) (functions of a complex variable), version 1.2.8, checked
on 2026-10-27 by agent g1c (helper prefix `g1c_`). The Lean code is in namespace
`DLMF.AlgebraicAnalytic`. Modules, in import order:

- [Fourier/Defs](DLMF/AlgebraicAnalytic/Fourier/Defs.lean) (definitions; Mathlib only),
  [Fourier/Series](DLMF/AlgebraicAnalytic/Fourier/Series.lean) (imports `Defs`),
  [Fourier/MathlibCoverage](DLMF/AlgebraicAnalytic/Fourier/MathlibCoverage.lean) (upstream
  pointers);
- [Complex/Defs](DLMF/AlgebraicAnalytic/Complex/Defs.lean) (definitions; Mathlib and Tau Ceti
  winding numbers, piecewise-`C¹` contours and filled hulls),
  [Complex/Calculus](DLMF/AlgebraicAnalytic/Complex/Calculus.lean) (§1.9; imports `Defs`),
  [Complex/Functions](DLMF/AlgebraicAnalytic/Complex/Functions.lean) (§1.10; imports `Defs`),
  [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean) (upstream
  pointers, Mathlib and Tau Ceti),
  [Complex/GeneratingFunctions](DLMF/AlgebraicAnalytic/Complex/GeneratingFunctions.lean)
  (1.10.28–1.10.29; a bridge file importing `DLMF.OrthogonalPolynomials.Series` and
  `DLMF.OrthogonalPolynomials.Differential`).

**Counts.** The three sections have 118 numbered equation IDs (§1.8: 18 including 1.8.E6_1 and
1.8.E6_2, §1.9: 71, §1.10: 29). 1.8.E13 has been moved by DLMF to 1.8.6_1 and carries no
statement. In scope: 117, all covered: 86 by project declarations (43 of them by a proved theorem
or a definition) and 31 by upstream pointers only. In addition 15 prose IDs carry tags or
pointers (1.8.i, 1.8.iii, 1.9.ii–vi, 1.10.i–vi, 1.10.viii, 1.10.ix); 97 DLMF IDs are tagged on
project declarations and 68 have upstream pointers. The eight modules contain 24 definitions
(all tagged) and 111 theorems: 48 tagged proved theorems, 57 tagged admissions and 6 private
helpers (all proved); 113 `dlmf_upstream` pointers. No proved theorem depends on an admission
(`#print axioms` on all 48 tagged proved theorems shows only `propext`, `Classical.choice`,
`Quot.sound`).

Module admissions (`grep -cE 'by sorry|:= sorry|^\s*(·\s*)?sorry\s*$|exact sorry'`):

- Fourier: Defs 0 (4 definitions), Series 11 (27 theorems, 4 of them private helpers),
  MathlibCoverage 0 (11 pointers).
- Complex: Defs 0 (20 definitions), Calculus 17 (47 theorems, 2 private helpers), Functions 29
  (35 theorems), GeneratingFunctions 0 (2 theorems), MathlibCoverage 0 (102 pointers).

### Conventions and design (part g1c)

- Fourier coefficients (1.8.2, 1.8.4) are defined on `ℝ → ℂ` over `[-π, π]` with DLMF's
  normalization (`a_n = π⁻¹∫ f cos nx`, `c_n = (2π)⁻¹∫ f e^{-inx}`);
  `fourierExpCoeff_eq_fourierCoeffOn` identifies `c_n` with Mathlib's `fourierCoeffOn`. The
  convergence results are transported from Mathlib's `AddCircle (2π)` API.
- Series that converge only conditionally (Fourier partial sums in 1.8.11, Cauchy products,
  1.9.68, 1.10.24) are stated with `Tendsto` of partial sums, since `HasSum` over `ℂ` is
  unconditional summation.
- The principal phase is Mathlib's `Complex.arg ∈ (-π, π]`, which agrees with DLMF's
  principal value off the negative real axis; on `(-∞, 0)` DLMF allows `±π` and Lean takes
  `π`. The multivalued phase `ph z` is the predicate `IsPhase z θ` (`z = |z| e^{iθ}`), and the
  general-phase identities 1.9.13, 1.9.18, 1.9.20 are stated for it, since the principal-value
  forms fail across the branch cut.
- Contours (§1.9(iii)) are Tau Ceti's piecewise-`C¹` curves `γ : ℝ → ℂ` on `[a, b]`;
  `contourIntegral` is `∫_a^b f(γ t) γ'(t) dt`. The interior of a simple closed contour is
  `filledHull (γ '' [a, b]) \ γ '' [a, b]` and the exterior the complement of the filled hull;
  "positively oriented" means winding number 1 at every interior point. The Jordan curve
  theorem (`IsSimpleClosedContour.jordan`) is admitted; Tau Ceti's Jordan curve and plane
  separation modules were not built at acquisition time and are not imported.
- The extended plane is `OnePoint ℂ`; `extAdd`, `extMul`, `extDiv` implement the conventions
  1.9.36–1.9.39, `AnalyticAtInfty f L` and `derivAtInfty f L` use `g(z) = f(1/z)` with `g(0) = L`.
- `laurentCoeff` (1.10.7) is a circle integral, `residueAt` the limit of the `-1` coefficient
  as the radius tends to `0`; `residueAt_eq_residue` relates it to Tau Ceti's residue.
- `recipCoeff`, `logCoeff`, `powCoeff` (1.9.56, 1.9.59, 1.9.62) are defined by the DLMF
  recurrences (well-founded recursion over `Fin n`).
- `ProdConvergesDLMF` (§1.10(ix)) encodes DLMF's definition of convergence of an infinite
  product (finitely many zero factors, nonzero limit of the remaining partial products).
- Stronger than DLMF: 1.8.12 (termwise integration for every `L¹` periodic function), 1.8.16
  (complex `x`), the Riemann–Lebesgue lemma of §1.8(i) (for every integrable `f`), 1.9.22
  (complex `θ`), 1.9.16 (no hypothesis `z₂ ≠ 0`, both sides being `0`).
- Restricted forms: 1.8.1 is stated with a summability hypothesis on the coefficients (DLMF
  states the series formally); 1.8.7 for `C^m` periodic `f`; 1.10.15–1.10.16 for integer `μ`.

### Suspected source imprecision (part g1c)

- [1.9.51](https://dlmf.nist.gov/1.9.E51): DLMF says that the Cauchy product of two power
  series equals the product of their sums "when both converge". This is false without
  convergence of the Cauchy product itself: for `aₙ = bₙ = (-1)ⁿ/√(n+1)` and `z = 1` both
  series converge but the Cauchy product terms do not tend to `0`. Acquired in corrected (Abel)
  form `tendsto_cauchyProduct`: if all three series converge, the product series sums to the
  product (equal for absolutely convergent series, Mathlib
  `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`).
- [1.10.24](https://dlmf.nist.gov/1.10.E24): `F(z) ≠ 0` is part of DLMF's notion of
  convergence of a product but does not follow from uniform convergence of the partial products
  (`aₙ = ½` gives the limit `0`); the hypothesis is added.
- [1.10.25](https://dlmf.nist.gov/1.10.E25) (Mittag-Leffler expansion): the hypotheses
  `zₙ ≠ 0` and `|zₙ| → ∞` are implicit in DLMF and added (otherwise the poles can accumulate,
  e.g. `zₙ = 1 + 1/n`, `aₙ = 2⁻ⁿ`).
- [§1.10(ii)](https://dlmf.nist.gov/1.10.ii): the identity theorem for continuation from `D₁`
  to `D₂` needs `D₁ ∩ D₂` connected; DLMF leaves this tacit (Mathlib's
  `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` requires a preconnected domain).

### Numbered formulas and prose items (part g1c)

## [§1.8 Fourier Series](https://dlmf.nist.gov/1.8)

- [1.8.E1](https://dlmf.nist.gov/1.8.E1): [`DLMF.AlgebraicAnalytic.hasSum_fourierSeries`](DLMF/AlgebraicAnalytic/Fourier/Series.lean#L187) (proved); with a summability hypothesis on the exponential coefficients (DLMF states 1.8.1 formally)
- [1.8.E2](https://dlmf.nist.gov/1.8.E2): [`DLMF.AlgebraicAnalytic.fourierCosCoeff`](DLMF/AlgebraicAnalytic/Fourier/Defs.lean#L37) (definition); [`DLMF.AlgebraicAnalytic.fourierSinCoeff`](DLMF/AlgebraicAnalytic/Fourier/Defs.lean#L43) (definition)
- [1.8.E3](https://dlmf.nist.gov/1.8.E3): [`DLMF.AlgebraicAnalytic.hasSum_fourierExpSeries`](DLMF/AlgebraicAnalytic/Fourier/Series.lean#L154) (proved); Mathlib: `has_pointwise_sum_fourier_series_of_summable` (pointer in [Fourier/MathlibCoverage](DLMF/AlgebraicAnalytic/Fourier/MathlibCoverage.lean))
- [1.8.E4](https://dlmf.nist.gov/1.8.E4): [`DLMF.AlgebraicAnalytic.fourierExpCoeff`](DLMF/AlgebraicAnalytic/Fourier/Defs.lean#L50) (definition); [`DLMF.AlgebraicAnalytic.fourierExpCoeff_eq_fourierCoeffOn`](DLMF/AlgebraicAnalytic/Fourier/Series.lean#L52) (proved); Mathlib: `fourierCoeffOn` (pointer in [Fourier/MathlibCoverage](DLMF/AlgebraicAnalytic/Fourier/MathlibCoverage.lean))
- [1.8.E5](https://dlmf.nist.gov/1.8.E5): [`DLMF.AlgebraicAnalytic.hasSum_norm_sq_fourierCosSinCoeff`](DLMF/AlgebraicAnalytic/Fourier/Series.lean#L246) (proved)
- [1.8.E6](https://dlmf.nist.gov/1.8.E6): [`DLMF.AlgebraicAnalytic.hasSum_norm_sq_fourierExpCoeff`](DLMF/AlgebraicAnalytic/Fourier/Series.lean#L224) (proved); Mathlib: `hasSum_sq_fourierCoeffOn` (pointer in [Fourier/MathlibCoverage](DLMF/AlgebraicAnalytic/Fourier/MathlibCoverage.lean)); Mathlib: `tsum_sq_fourierCoeff` (pointer in [Fourier/MathlibCoverage](DLMF/AlgebraicAnalytic/Fourier/MathlibCoverage.lean))
- [1.8.E6_1](https://dlmf.nist.gov/1.8.E6_1): [`DLMF.AlgebraicAnalytic.hasSum_fourierCosSinCoeff_mul_conj`](DLMF/AlgebraicAnalytic/Fourier/Series.lean#L277) (admitted)
- [1.8.E6_2](https://dlmf.nist.gov/1.8.E6_2): [`DLMF.AlgebraicAnalytic.hasSum_fourierExpCoeff_mul_conj`](DLMF/AlgebraicAnalytic/Fourier/Series.lean#L290) (admitted)
- [1.8.E7](https://dlmf.nist.gov/1.8.E7): [`DLMF.AlgebraicAnalytic.fourierCoeff_isLittleO`](DLMF/AlgebraicAnalytic/Fourier/Series.lean#L300) (admitted); Mathlib: `fourierCoeffOn_of_hasDerivAt` (pointer in [Fourier/MathlibCoverage](DLMF/AlgebraicAnalytic/Fourier/MathlibCoverage.lean)); special case of `C^m` periodic `f`
- [1.8.E8](https://dlmf.nist.gov/1.8.E8): [`DLMF.AlgebraicAnalytic.lebesgueConstant`](DLMF/AlgebraicAnalytic/Fourier/Defs.lean#L56) (definition)
- [1.8.E9](https://dlmf.nist.gov/1.8.E9): [`DLMF.AlgebraicAnalytic.lebesgueConstant_isEquivalent`](DLMF/AlgebraicAnalytic/Fourier/Series.lean#L320) (admitted)
- [1.8.E10](https://dlmf.nist.gov/1.8.E10): [`DLMF.AlgebraicAnalytic.tendsto_intervalIntegral_mul_exp_atTop`](DLMF/AlgebraicAnalytic/Fourier/Series.lean#L347) (proved); Mathlib: `Real.tendsto_integral_exp_smul_cocompact` (pointer in [Fourier/MathlibCoverage](DLMF/AlgebraicAnalytic/Fourier/MathlibCoverage.lean)); Mathlib: `tendsto_integral_exp_inner_smul_cocompact` (pointer in [Fourier/MathlibCoverage](DLMF/AlgebraicAnalytic/Fourier/MathlibCoverage.lean))
- [1.8.E11](https://dlmf.nist.gov/1.8.E11): [`DLMF.AlgebraicAnalytic.tendsto_fourierPartialSum_of_oneSidedDeriv`](DLMF/AlgebraicAnalytic/Fourier/Series.lean#L363) (admitted)
- [1.8.E12](https://dlmf.nist.gov/1.8.E12): [`DLMF.AlgebraicAnalytic.tendsto_integral_fourierSeries`](DLMF/AlgebraicAnalytic/Fourier/Series.lean#L383) (admitted); stronger than DLMF: termwise integration of the partial sums converges for every `L¹` periodic `f`
- [1.8.E13](https://dlmf.nist.gov/1.8.E13): no statement; DLMF has moved this equation to 1.8.6_1
- [1.8.E14](https://dlmf.nist.gov/1.8.E14): [`DLMF.AlgebraicAnalytic.poissonSummation`](DLMF/AlgebraicAnalytic/Fourier/Series.lean#L412) (admitted); Mathlib: `Real.tsum_eq_tsum_fourier_of_rpow_decay` (pointer in [Fourier/MathlibCoverage](DLMF/AlgebraicAnalytic/Fourier/MathlibCoverage.lean)); Mathlib: `Real.tsum_eq_tsum_fourier` (pointer in [Fourier/MathlibCoverage](DLMF/AlgebraicAnalytic/Fourier/MathlibCoverage.lean))
- [1.8.E15](https://dlmf.nist.gov/1.8.E15): [`DLMF.AlgebraicAnalytic.poissonSummation_cos`](DLMF/AlgebraicAnalytic/Fourier/Series.lean#L425) (admitted)
- [1.8.E16](https://dlmf.nist.gov/1.8.E16): [`DLMF.AlgebraicAnalytic.hasSum_exp_neg_sq_mul`](DLMF/AlgebraicAnalytic/Fourier/Series.lean#L438) (admitted); Mathlib: `Complex.tsum_exp_neg_quadratic` (pointer in [Fourier/MathlibCoverage](DLMF/AlgebraicAnalytic/Fourier/MathlibCoverage.lean)); stronger than DLMF: complex `x`
- [1.8.i](https://dlmf.nist.gov/1.8.i): [`DLMF.AlgebraicAnalytic.fourierExpCoeff_natCast`](DLMF/AlgebraicAnalytic/Fourier/Series.lean#L92) (proved); [`DLMF.AlgebraicAnalytic.fourierExpCoeff_neg_natCast`](DLMF/AlgebraicAnalytic/Fourier/Series.lean#L102) (proved); [`DLMF.AlgebraicAnalytic.fourierExpCoeff_zero`](DLMF/AlgebraicAnalytic/Fourier/Series.lean#L117) (proved); [`DLMF.AlgebraicAnalytic.fourierSinCoeff_eq_zero_of_even`](DLMF/AlgebraicAnalytic/Fourier/Series.lean#L134) (proved); [`DLMF.AlgebraicAnalytic.fourierCosCoeff_eq_zero_of_odd`](DLMF/AlgebraicAnalytic/Fourier/Series.lean#L145) (proved); [`DLMF.AlgebraicAnalytic.eq_of_fourierCoeff_eq`](DLMF/AlgebraicAnalytic/Fourier/Series.lean#L311) (admitted); [`DLMF.AlgebraicAnalytic.tendsto_integral_mul_exp_atTop`](DLMF/AlgebraicAnalytic/Fourier/Series.lean#L326) (proved); Mathlib: `hasSum_fourier_series_L2` (pointer in [Fourier/MathlibCoverage](DLMF/AlgebraicAnalytic/Fourier/MathlibCoverage.lean)); coefficient identities, even/odd vanishing, uniqueness, Riemann–Lebesgue lemma (no hypothesis beyond integrability)
- [1.8.iii](https://dlmf.nist.gov/1.8.iii): [`DLMF.AlgebraicAnalytic.tendsto_deriv_fourierSeries`](DLMF/AlgebraicAnalytic/Fourier/Series.lean#L399) (admitted); termwise differentiation

## [§1.9 Calculus of a Complex Variable](https://dlmf.nist.gov/1.9)

- [1.9.E1](https://dlmf.nist.gov/1.9.E1): Mathlib: `Complex.re_add_im` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E2](https://dlmf.nist.gov/1.9.E2): Mathlib: `Complex.re` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `Complex.im` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E3](https://dlmf.nist.gov/1.9.E3): Mathlib: `Complex.norm_mul_cos_arg` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `Complex.norm_mul_sin_arg` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E4](https://dlmf.nist.gov/1.9.E4): Mathlib: `Complex.norm_eq_sqrt_sq_add_sq` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E5](https://dlmf.nist.gov/1.9.E5): [`DLMF.AlgebraicAnalytic.arg_eq_arctan_of_re_pos_of_im_nonneg`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L67) (proved); [`DLMF.AlgebraicAnalytic.arg_eq_neg_arctan_of_re_pos_of_im_neg`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L73) (proved); [`DLMF.AlgebraicAnalytic.arg_eq_pi_sub_arctan_of_re_neg_of_im_nonneg`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L79) (proved); [`DLMF.AlgebraicAnalytic.arg_eq_neg_pi_add_arctan_of_re_neg_of_im_neg`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L94) (proved); the four quadrant formulas (1.9.5–1.9.6) as four theorems; Mathlib `Complex.arg ∈ (-π, π]` is the DLMF principal phase, single valued on the negative real axis (DLMF allows ±π there)
- [1.9.E6](https://dlmf.nist.gov/1.9.E6): [`DLMF.AlgebraicAnalytic.arg_eq_arctan_of_re_pos_of_im_nonneg`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L67) (proved); [`DLMF.AlgebraicAnalytic.arg_eq_neg_arctan_of_re_pos_of_im_neg`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L73) (proved); [`DLMF.AlgebraicAnalytic.arg_eq_pi_sub_arctan_of_re_neg_of_im_nonneg`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L79) (proved); [`DLMF.AlgebraicAnalytic.arg_eq_neg_pi_add_arctan_of_re_neg_of_im_neg`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L94) (proved); see 1.9.5
- [1.9.E7](https://dlmf.nist.gov/1.9.E7): [`DLMF.AlgebraicAnalytic.IsPhase`](DLMF/AlgebraicAnalytic/Complex/Defs.lean#L55) (definition); [`DLMF.AlgebraicAnalytic.isPhase_arg`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L105) (proved); [`DLMF.AlgebraicAnalytic.isPhase_iff`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L109) (proved); Mathlib: `Complex.arg_mem_Ioc` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); `IsPhase` is the multivalued phase `ph z = arg z + 2πk`
- [1.9.E8](https://dlmf.nist.gov/1.9.E8): Mathlib: `Complex.abs_re_le_norm` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `Complex.abs_im_le_norm` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E9](https://dlmf.nist.gov/1.9.E9): Mathlib: `Complex.norm_mul_exp_arg_mul_I` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E10](https://dlmf.nist.gov/1.9.E10): Mathlib: `Complex.exp_mul_I` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E11](https://dlmf.nist.gov/1.9.E11): Mathlib: `Complex.conj_re` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `Complex.conj_im` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E12](https://dlmf.nist.gov/1.9.E12): Mathlib: `Complex.norm_conj` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E13](https://dlmf.nist.gov/1.9.E13): [`DLMF.AlgebraicAnalytic.IsPhase.conj`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L132) (proved); Mathlib: `Complex.arg_conj` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E14](https://dlmf.nist.gov/1.9.E14): Mathlib: `Complex.add_re` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `Complex.add_im` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `Complex.sub_re` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `Complex.sub_im` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E15](https://dlmf.nist.gov/1.9.E15): Mathlib: `Complex.mul_re` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `Complex.mul_im` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E16](https://dlmf.nist.gov/1.9.E16): [`DLMF.AlgebraicAnalytic.div_eq_mul_conj_div`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L167) (proved); Mathlib: `Complex.div_re` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `Complex.div_im` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E17](https://dlmf.nist.gov/1.9.E17): Mathlib: `Complex.norm_mul` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E18](https://dlmf.nist.gov/1.9.E18): [`DLMF.AlgebraicAnalytic.IsPhase.mul`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L144) (proved); Mathlib: `Complex.arg_mul_coe_angle` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E19](https://dlmf.nist.gov/1.9.E19): Mathlib: `Complex.norm_div` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E20](https://dlmf.nist.gov/1.9.E20): [`DLMF.AlgebraicAnalytic.IsPhase.div`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L155) (proved); Mathlib: `Complex.arg_div_coe_angle` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E21](https://dlmf.nist.gov/1.9.E21): [`DLMF.AlgebraicAnalytic.pow_eq_sum_choose`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L184) (admitted); binomial expansion of `(x + iy)^n` in real and imaginary parts
- [1.9.E22](https://dlmf.nist.gov/1.9.E22): [`DLMF.AlgebraicAnalytic.cos_add_sin_mul_I_zpow`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L196) (proved); Mathlib: `Complex.cos_add_sin_mul_I_pow` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E23](https://dlmf.nist.gov/1.9.E23): [`DLMF.AlgebraicAnalytic.abs_norm_sub_norm_le_norm_add_le`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L203) (proved); Mathlib: `norm_add_le` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `abs_norm_sub_norm_le` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); both triangle inequalities in one statement
- [1.9.E24](https://dlmf.nist.gov/1.9.E24): Mathlib: `hasDerivAt_iff_tendsto_slope` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E25](https://dlmf.nist.gov/1.9.E25): [`DLMF.AlgebraicAnalytic.hasDerivAt_re_im_of_hasDerivAt`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L212) (proved)
- [1.9.E26](https://dlmf.nist.gov/1.9.E26): Mathlib: `AnalyticAt.harmonicAt_re` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `AnalyticAt.harmonicAt_im` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E27](https://dlmf.nist.gov/1.9.E27): [`DLMF.AlgebraicAnalytic.harmonic_polar`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L252) (admitted)
- [1.9.E28](https://dlmf.nist.gov/1.9.E28): [`DLMF.AlgebraicAnalytic.contourIntegral`](DLMF/AlgebraicAnalytic/Complex/Defs.lean#L159) (definition); parametrized contour integral `∫ f(γ t) γ'(t) dt`
- [1.9.E29](https://dlmf.nist.gov/1.9.E29): [`DLMF.AlgebraicAnalytic.IsSimpleClosedContour.contourIntegral_eq_zero`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L283) (admitted); Tau Ceti: `TauCeti.Contour.homologyCauchyTheorem` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Cauchy theorem for a simple closed contour
- [1.9.E30](https://dlmf.nist.gov/1.9.E30): [`DLMF.AlgebraicAnalytic.IsSimpleClosedContour.cauchyIntegralFormula`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L294) (admitted); Mathlib: `DiffContOnCl.circleIntegral_sub_inv_smul` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E31](https://dlmf.nist.gov/1.9.E31): [`DLMF.AlgebraicAnalytic.IsSimpleClosedContour.cauchyIntegralFormula_iteratedDeriv`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L305) (admitted); Mathlib: `DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E32](https://dlmf.nist.gov/1.9.E32): [`DLMF.AlgebraicAnalytic.windingNumber_eq_intCast`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L318) (admitted); Tau Ceti: `TauCeti.Contour.windingNumber` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E33](https://dlmf.nist.gov/1.9.E33): Mathlib: `InnerProductSpace.HarmonicOnNhd.circleAverage_eq` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E34](https://dlmf.nist.gov/1.9.E34): Mathlib: `InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E35](https://dlmf.nist.gov/1.9.E35): [`DLMF.AlgebraicAnalytic.hasBasis_nhds_infty`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L352) (admitted)
- [1.9.E36](https://dlmf.nist.gov/1.9.E36): [`DLMF.AlgebraicAnalytic.extAdd`](DLMF/AlgebraicAnalytic/Complex/Defs.lean#L65) (definition); [`DLMF.AlgebraicAnalytic.extAdd_infty`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L360) (proved)
- [1.9.E37](https://dlmf.nist.gov/1.9.E37): [`DLMF.AlgebraicAnalytic.extMul`](DLMF/AlgebraicAnalytic/Complex/Defs.lean#L72) (definition); [`DLMF.AlgebraicAnalytic.extMul_infty`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L364) (proved)
- [1.9.E38](https://dlmf.nist.gov/1.9.E38): [`DLMF.AlgebraicAnalytic.extDiv`](DLMF/AlgebraicAnalytic/Complex/Defs.lean#L80) (definition); [`DLMF.AlgebraicAnalytic.extDiv_infty`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L368) (proved)
- [1.9.E39](https://dlmf.nist.gov/1.9.E39): [`DLMF.AlgebraicAnalytic.extDiv_zero`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L372) (proved)
- [1.9.E40](https://dlmf.nist.gov/1.9.E40): [`DLMF.AlgebraicAnalytic.mobius`](DLMF/AlgebraicAnalytic/Complex/Defs.lean#L100) (definition)
- [1.9.E41](https://dlmf.nist.gov/1.9.E41): [`DLMF.AlgebraicAnalytic.mobiusExt`](DLMF/AlgebraicAnalytic/Complex/Defs.lean#L106) (definition); [`DLMF.AlgebraicAnalytic.mobiusExt_neg_div`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L388) (proved)
- [1.9.E42](https://dlmf.nist.gov/1.9.E42): [`DLMF.AlgebraicAnalytic.hasDerivAt_mobius`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L397) (proved)
- [1.9.E43](https://dlmf.nist.gov/1.9.E43): [`DLMF.AlgebraicAnalytic.derivAtInfty_mobius`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L425) (proved)
- [1.9.E44](https://dlmf.nist.gov/1.9.E44): [`DLMF.AlgebraicAnalytic.mobius_mobius_inv`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L449) (proved)
- [1.9.E45](https://dlmf.nist.gov/1.9.E45): [`DLMF.AlgebraicAnalytic.crossRatio`](DLMF/AlgebraicAnalytic/Complex/Defs.lean#L113) (definition); [`DLMF.AlgebraicAnalytic.crossRatio_mobius`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L469) (proved)
- [1.9.E46](https://dlmf.nist.gov/1.9.E46): Mathlib: `tendsto_pi_nhds` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E47](https://dlmf.nist.gov/1.9.E47): Mathlib: `Metric.tendstoUniformlyOn_iff` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E48](https://dlmf.nist.gov/1.9.E48): Mathlib: `HasFPowerSeriesOnBall.factorial_smul` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E49](https://dlmf.nist.gov/1.9.E49): Mathlib: `FormalMultilinearSeries.radius_eq_liminf` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E50](https://dlmf.nist.gov/1.9.E50): Mathlib: `HasSum.add` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `HasSum.sub` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E51](https://dlmf.nist.gov/1.9.E51): [`DLMF.AlgebraicAnalytic.tendsto_cauchyProduct`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L494) (admitted); Mathlib: `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); corrected: DLMF says the Cauchy product equals the product "when both converge", which is false without convergence of the product series (`aₙ = bₙ = (-1)ⁿ/√(n+1)`, `z = 1`); stated in Abel form: if the Cauchy product also converges, its sum is the product
- [1.9.E52](https://dlmf.nist.gov/1.9.E52): [`DLMF.AlgebraicAnalytic.tendsto_cauchyProduct`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L494) (admitted); see 1.9.51
- [1.9.E53](https://dlmf.nist.gov/1.9.E53): [`DLMF.AlgebraicAnalytic.hasSum_recipCoeff`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L509) (admitted)
- [1.9.E54](https://dlmf.nist.gov/1.9.E54): [`DLMF.AlgebraicAnalytic.hasSum_recipCoeff`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L509) (admitted)
- [1.9.E55](https://dlmf.nist.gov/1.9.E55): [`DLMF.AlgebraicAnalytic.recipCoeff_zero_one_two`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L517) (proved)
- [1.9.E56](https://dlmf.nist.gov/1.9.E56): [`DLMF.AlgebraicAnalytic.recipCoeff`](DLMF/AlgebraicAnalytic/Complex/Defs.lean#L121) (definition)
- [1.9.E57](https://dlmf.nist.gov/1.9.E57): [`DLMF.AlgebraicAnalytic.hasSum_logCoeff`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L531) (admitted)
- [1.9.E58](https://dlmf.nist.gov/1.9.E58): [`DLMF.AlgebraicAnalytic.logCoeff_one_two_three`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L540) (proved)
- [1.9.E59](https://dlmf.nist.gov/1.9.E59): [`DLMF.AlgebraicAnalytic.logCoeff`](DLMF/AlgebraicAnalytic/Complex/Defs.lean#L130) (definition)
- [1.9.E60](https://dlmf.nist.gov/1.9.E60): [`DLMF.AlgebraicAnalytic.hasSum_powCoeff`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L553) (admitted)
- [1.9.E61](https://dlmf.nist.gov/1.9.E61): [`DLMF.AlgebraicAnalytic.powCoeff_zero_one_two`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L562) (proved)
- [1.9.E62](https://dlmf.nist.gov/1.9.E62): [`DLMF.AlgebraicAnalytic.powCoeff`](DLMF/AlgebraicAnalytic/Complex/Defs.lean#L140) (definition)
- [1.9.E63](https://dlmf.nist.gov/1.9.E63): [`DLMF.AlgebraicAnalytic.hasSum_iteratedDeriv_powerSeries`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L574) (admitted)
- [1.9.E64](https://dlmf.nist.gov/1.9.E64): [`DLMF.AlgebraicAnalytic.tendsto_iterated_of_tendsto_prod`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L587) (proved)
- [1.9.E65](https://dlmf.nist.gov/1.9.E65): [`DLMF.AlgebraicAnalytic.tendsto_iterated_of_tendsto_prod`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L587) (proved)
- [1.9.E66](https://dlmf.nist.gov/1.9.E66): Mathlib: `Summable.tsum_prod` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E67](https://dlmf.nist.gov/1.9.E67): Mathlib: `Summable.tsum_prod` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `Summable.tsum_comm` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E68](https://dlmf.nist.gov/1.9.E68): [`DLMF.AlgebraicAnalytic.tendsto_contourIntegral_tsum`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L612) (admitted)
- [1.9.E69](https://dlmf.nist.gov/1.9.E69): Mathlib: `MeasureTheory.integral_tsum` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E70](https://dlmf.nist.gov/1.9.E70): Mathlib: `MeasureTheory.integral_tsum` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.E71](https://dlmf.nist.gov/1.9.E71): Mathlib: `MeasureTheory.integral_tsum` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.ii](https://dlmf.nist.gov/1.9.ii): [`DLMF.AlgebraicAnalytic.differentiableAt_of_cauchyRiemann`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L240) (admitted); Mathlib: `Metric.continuousAt_iff` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `Metric.isOpen_iff` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `accPt_iff_frequently` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `closure_eq_self_union_derivedSet` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `IsOpen.isConnected_iff_isPathConnected` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `HasDerivAt.continuousAt` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `Complex.analyticAt_iff_eventually_differentiableAt` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `AnalyticOnNhd.iterated_deriv` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `DifferentiableOn.analyticOnNhd` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.iii](https://dlmf.nist.gov/1.9.iii): [`DLMF.AlgebraicAnalytic.IsSimpleClosedContour`](DLMF/AlgebraicAnalytic/Complex/Defs.lean#L152) (definition); [`DLMF.AlgebraicAnalytic.contourInterior`](DLMF/AlgebraicAnalytic/Complex/Defs.lean#L166) (definition); [`DLMF.AlgebraicAnalytic.contourExterior`](DLMF/AlgebraicAnalytic/Complex/Defs.lean#L172) (definition); [`DLMF.AlgebraicAnalytic.IsPositivelyOriented`](DLMF/AlgebraicAnalytic/Complex/Defs.lean#L178) (definition); [`DLMF.AlgebraicAnalytic.IsSimpleClosedContour.jordan`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L265) (admitted); [`DLMF.AlgebraicAnalytic.IsSimpleClosedContour.windingNumber_eq_one_or_neg_one`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L328) (admitted); [`DLMF.AlgebraicAnalytic.windingNumber_eq_zero_of_mem_contourExterior`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L338) (proved); Tau Ceti: `TauCeti.Contour.IsPiecewiseC1On` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Tau Ceti: `TauCeti.Contour.IsPiecewiseC1On.windingNumber_eq_zero_of_unbounded_component` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `Differentiable.apply_eq_apply_of_bounded` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Jordan curve theorem stated for simple closed piecewise-`C¹` contours; interior via Tau Ceti `filledHull`
- [1.9.iv](https://dlmf.nist.gov/1.9.iv): [`DLMF.AlgebraicAnalytic.AnalyticAtInfty`](DLMF/AlgebraicAnalytic/Complex/Defs.lean#L88) (definition); [`DLMF.AlgebraicAnalytic.derivAtInfty`](DLMF/AlgebraicAnalytic/Complex/Defs.lean#L95) (definition); [`DLMF.AlgebraicAnalytic.linear_hasDerivAt_bijective`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L377) (proved); [`DLMF.AlgebraicAnalytic.mobiusExt_bijective`](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L461) (admitted); Mathlib: `OnePoint` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `DifferentiableAt.conformalAt` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `InnerProductGeometry.ConformalAt.preserves_angle` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.v](https://dlmf.nist.gov/1.9.v): Mathlib: `Complex.hasSum_iff` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `Summable.of_norm` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `summable_of_ratio_test_tendsto_lt_one` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `not_summable_of_ratio_test_tendsto_gt_one` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `tendstoUniformlyOn_tsum` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `summable_int_iff_summable_nat_and_neg` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.9.vi](https://dlmf.nist.gov/1.9.vi): Mathlib: `FormalMultilinearSeries.summable_norm_mul_pow` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `FormalMultilinearSeries.not_summable_norm_of_radius_lt_nnnorm` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `FormalMultilinearSeries.hasFPowerSeriesOnBall` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `HasFPowerSeriesOnBall.tendstoUniformlyOn` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))

## [§1.10 Functions of a Complex Variable](https://dlmf.nist.gov/1.10)

- [1.10.E1](https://dlmf.nist.gov/1.10.E1): Mathlib: `Complex.hasSum_taylorSeries_on_ball` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `DifferentiableOn.hasFPowerSeriesOnBall` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.10.E2](https://dlmf.nist.gov/1.10.E2): [`DLMF.AlgebraicAnalytic.hasSum_exp_series`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L56) (proved); Mathlib: `NormedSpace.exp_eq_tsum` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.10.E3](https://dlmf.nist.gov/1.10.E3): Mathlib: `Complex.hasSum_taylorSeries_log` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.10.E4](https://dlmf.nist.gov/1.10.E4): Mathlib: `Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.10.E5](https://dlmf.nist.gov/1.10.E5): Tau Ceti: `TauCeti.exists_differentiableOn_eqOn_conj_of_symmetric` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.10.E6](https://dlmf.nist.gov/1.10.E6): [`DLMF.AlgebraicAnalytic.hasSum_laurentSeries`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L66) (admitted); Laurent expansion on an annulus
- [1.10.E7](https://dlmf.nist.gov/1.10.E7): [`DLMF.AlgebraicAnalytic.laurentCoeff`](DLMF/AlgebraicAnalytic/Complex/Defs.lean#L189) (definition)
- [1.10.E8](https://dlmf.nist.gov/1.10.E8): [`DLMF.AlgebraicAnalytic.IsSimpleClosedContour.residueTheorem`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L120) (admitted); Tau Ceti: `TauCeti.Contour.classicalResidueTheorem_circle` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.10.E9](https://dlmf.nist.gov/1.10.E9): [`DLMF.AlgebraicAnalytic.IsSimpleClosedContour.argumentPrinciple`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L134) (admitted); Tau Ceti: `TauCeti.Contour.argumentPrinciple_nullHomologous` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.10.E10](https://dlmf.nist.gov/1.10.E10): [`DLMF.AlgebraicAnalytic.IsSimpleClosedContour.argumentPrinciple_mul_id`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L153) (admitted)
- [1.10.E11](https://dlmf.nist.gov/1.10.E11): [`DLMF.AlgebraicAnalytic.schwarz_lemma`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L200) (proved); [`DLMF.AlgebraicAnalytic.schwarz_lemma_eq_iff`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L215) (admitted); Mathlib: `Complex.dist_le_div_mul_dist_of_mapsTo_ball` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `Complex.norm_deriv_le_div_of_mapsTo_ball` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.10.E12](https://dlmf.nist.gov/1.10.E12): [`DLMF.AlgebraicAnalytic.lagrangeInversion`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L273) (admitted)
- [1.10.E13](https://dlmf.nist.gov/1.10.E13): [`DLMF.AlgebraicAnalytic.lagrangeInversion`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L273) (admitted)
- [1.10.E14](https://dlmf.nist.gov/1.10.E14): [`DLMF.AlgebraicAnalytic.lagrangeBurmann`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L286) (admitted)
- [1.10.E15](https://dlmf.nist.gov/1.10.E15): [`DLMF.AlgebraicAnalytic.extendedInversion`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L298) (admitted); integer exponent `μ` only (the branch for non-integer `μ` is not formalized)
- [1.10.E16](https://dlmf.nist.gov/1.10.E16): [`DLMF.AlgebraicAnalytic.extendedInversion`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L298) (admitted); see 1.10.15
- [1.10.E17](https://dlmf.nist.gov/1.10.E17): [`DLMF.AlgebraicAnalytic.extendedInversion_comp`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L315) (admitted)
- [1.10.E18](https://dlmf.nist.gov/1.10.E18): [`DLMF.AlgebraicAnalytic.differentiableOn_intervalIntegral_param`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L332) (admitted)
- [1.10.E19](https://dlmf.nist.gov/1.10.E19): [`DLMF.AlgebraicAnalytic.differentiableOn_improperIntegral_param`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L344) (admitted)
- [1.10.E20](https://dlmf.nist.gov/1.10.E20): [`DLMF.AlgebraicAnalytic.prod_mtest_log`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L400) (admitted)
- [1.10.E21](https://dlmf.nist.gov/1.10.E21): [`DLMF.AlgebraicAnalytic.prod_mtest`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L413) (admitted)
- [1.10.E22](https://dlmf.nist.gov/1.10.E22): [`DLMF.AlgebraicAnalytic.weierstrassProduct`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L424) (admitted)
- [1.10.E23](https://dlmf.nist.gov/1.10.E23): [`DLMF.AlgebraicAnalytic.differentiableOn_of_tendstoUniformlyOn_prod`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L437) (proved); Mathlib: `TendstoLocallyUniformlyOn.differentiableOn` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.10.E24](https://dlmf.nist.gov/1.10.E24): [`DLMF.AlgebraicAnalytic.tendsto_logDeriv_prod`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L451) (admitted); Mathlib: `logDeriv_tprod_eq_tsum` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); hypothesis `F ≠ 0` added: it is part of DLMF's convergence definition but not of uniform convergence in the Lean sense (`aₙ = ½` gives the limit 0)
- [1.10.E25](https://dlmf.nist.gov/1.10.E25): [`DLMF.AlgebraicAnalytic.mittagLeffler`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L464) (admitted); implicit hypotheses `zₙ ≠ 0` and `|zₙ| → ∞` added (without them the poles may accumulate, `zₙ = 1 + 1/n`, `aₙ = 2⁻ⁿ`)
- [1.10.E26](https://dlmf.nist.gov/1.10.E26): [`DLMF.AlgebraicAnalytic.coeff_eq_circleIntegral`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L481) (admitted)
- [1.10.E27](https://dlmf.nist.gov/1.10.E27): [`DLMF.AlgebraicAnalytic.coeff_eq_circleIntegral`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L481) (admitted)
- [1.10.E28](https://dlmf.nist.gov/1.10.E28): [`DLMF.AlgebraicAnalytic.ultrasph_generatingFunction`](DLMF/AlgebraicAnalytic/Complex/GeneratingFunctions.lean#L30) (proved); = DLMF 18.12.4 for the ultraspherical polynomials
- [1.10.E29](https://dlmf.nist.gov/1.10.E29): [`DLMF.AlgebraicAnalytic.ultrasph_generatingFunction_deriv`](DLMF/AlgebraicAnalytic/Complex/GeneratingFunctions.lean#L38) (proved); proved from 18.12.4 and 18.9.19
- [1.10.i](https://dlmf.nist.gov/1.10.i): Mathlib: `analyticOrderAt` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.10.ii](https://dlmf.nist.gov/1.10.ii): Mathlib: `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); identity theorem: upstream needs a preconnected domain; DLMF's statement for `D₁ ∩ D₂` tacitly requires it to be connected
- [1.10.iii](https://dlmf.nist.gov/1.10.iii): [`DLMF.AlgebraicAnalytic.residueAt`](DLMF/AlgebraicAnalytic/Complex/Defs.lean#L196) (definition); [`DLMF.AlgebraicAnalytic.removable_iff_laurentCoeff_neg_eq_zero`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L78) (admitted); [`DLMF.AlgebraicAnalytic.meromorphicOrderAt_eq_neg_iff_laurentCoeff`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L89) (admitted); [`DLMF.AlgebraicAnalytic.residueAt_eq_residue`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L100) (admitted); [`DLMF.AlgebraicAnalytic.picard_great`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L108) (admitted); Mathlib: `Complex.differentiableOn_update_limUnder_of_bddAbove` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `MeromorphicOn` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `meromorphicOrderAt` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Tau Ceti: `TauCeti.Contour.residue` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Tau Ceti: `TauCeti.Contour.residue_of_laurent_expansion` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); removable singularities, poles via order, residue, Picard's great theorem
- [1.10.iv](https://dlmf.nist.gov/1.10.iv): [`DLMF.AlgebraicAnalytic.IsSimpleClosedContour.rouche`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L166) (admitted); Tau Ceti: `TauCeti.rouche_add` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.10.v](https://dlmf.nist.gov/1.10.v): [`DLMF.AlgebraicAnalytic.harmonic_eqOn_of_isMaxOn`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L182) (admitted); [`DLMF.AlgebraicAnalytic.harmonic_exists_mem_frontier_isMaxOn`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L190) (admitted); Mathlib: `Complex.eqOn_of_isPreconnected_of_isMaxOn_norm` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `Complex.exists_mem_frontier_isMaxOn_norm` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
- [1.10.vi](https://dlmf.nist.gov/1.10.vi): [`DLMF.AlgebraicAnalytic.sqrt_branch_slitPlane`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L227) (proved); [`DLMF.AlgebraicAnalytic.sqrt_branch_compl_Ici`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L239) (proved); [`DLMF.AlgebraicAnalytic.not_exists_sqrt_branch_punctured`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L251) (admitted); [`DLMF.AlgebraicAnalytic.differentiableOn_one_sub_cpow_mul_one_add_cpow`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L258) (proved); square-root branches on slit planes; nonexistence on the punctured plane
- [1.10.viii](https://dlmf.nist.gov/1.10.viii): [`DLMF.AlgebraicAnalytic.differentiableOn_improperIntegral_param_of_lt`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L358) (admitted); [`DLMF.AlgebraicAnalytic.tendstoUniformlyOn_integral_of_norm_le`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L372) (admitted)
- [1.10.ix](https://dlmf.nist.gov/1.10.ix): [`DLMF.AlgebraicAnalytic.ProdConvergesDLMF`](DLMF/AlgebraicAnalytic/Complex/Defs.lean#L207) (definition); [`DLMF.AlgebraicAnalytic.prodConvergesDLMF_iff_log`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L385) (admitted); [`DLMF.AlgebraicAnalytic.prodConvergesDLMF_norm_iff`](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L393) (admitted); Mathlib: `multipliable_one_add_of_summable` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean)); Mathlib: `Complex.multipliable_of_summable_log` (pointer in [Complex/MathlibCoverage](DLMF/AlgebraicAnalytic/Complex/MathlibCoverage.lean))
### Prose, informal and excluded items (part g1c)

- [1.8.E13](https://dlmf.nist.gov/1.8.E13): no statement (DLMF has moved the equation to
  1.8.6_1, acquired as `hasSum_fourierCosSinCoeff_mul_conj`).
- [1.8.ii](https://dlmf.nist.gov/1.8.ii): the remark that convergence of 1.8.11 need not be
  uniform is excluded: informal.
- [1.8.iv](https://dlmf.nist.gov/1.8.iv): the remark that 1.8.14 can be written with
  `√(2π) 𝓕` is notation of §1.14; no statement (notation).
- [1.8.v](https://dlmf.nist.gov/1.8.v): no statement (references only).
- [1.9.i](https://dlmf.nist.gov/1.9.i): the definitions of complex numbers, modulus, phase and
  conjugate are Mathlib's (`Complex.re`, `Complex.im`, `‖z‖`, `Complex.arg`, `conj`); no
  separate statement (notation) beyond the pointers under 1.9.E1–1.9.E12.
- [1.10.vii](https://dlmf.nist.gov/1.10.vii) and [1.10.x](https://dlmf.nist.gov/1.10.x),
  [1.10.xi](https://dlmf.nist.gov/1.10.xi): covered by their numbered formulas (1.10.12–1.10.17,
  1.10.25, 1.10.26–1.10.29); no separate prose tag.

### Validation (part g1c)

- Strict checks (`lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false`) of all eight
  modules report only `declaration uses 'sorry'` warnings; `lake build` of the modules succeeds.
  No line exceeds 100 characters.
- `#print axioms` on all 48 tagged proved theorems shows only `propext`, `Classical.choice` and
  `Quot.sound`.
- Numerical checks (mpmath, scratch helper script `g1c_num.py`): the recurrences 1.9.56,
  1.9.59, 1.9.62 against the series of `1/f`, `ln f`, `f^ν` (including the closed forms of
  `q₂`, `q₃`, `p₂`); 1.8.16; 1.8.12 (the discrepancy of a 200-term truncation, about 0.07, is
  the expected tail of order `4π/200`); 1.9.43; the Poisson integral 1.9.34.

## Part g1d: §§1.11–1.13

This part covers the definitions, numbered formulas and analytical assertions in prose of
[DLMF §1.11](https://dlmf.nist.gov/1.11) (zeros of polynomials),
[§1.12](https://dlmf.nist.gov/1.12) (continued fractions) and
[§1.13](https://dlmf.nist.gov/1.13) (differential equations), version 1.2.8, checked on
2026-10-27 by agent g1d (helper prefix `g1d_`). The Lean code is in namespace
`DLMF.AlgebraicAnalytic`. Modules, in import order:

- [Polynomials/Defs](DLMF/AlgebraicAnalytic/Polynomials/Defs.lean) (definitions; Mathlib and TauCeti only),
  [Polynomials/Zeros](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean) (imports `Defs`),
  [Polynomials/MathlibCoverage](DLMF/AlgebraicAnalytic/Polynomials/MathlibCoverage.lean) (upstream pointers);
- [ContinuedFractions/Defs](DLMF/AlgebraicAnalytic/ContinuedFractions/Defs.lean) (imports
  `DLMFMathlib.Analysis.ContinuedFraction.Convergence`),
  [ContinuedFractions/Convergents](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergents.lean) (imports `Defs`),
  [ContinuedFractions/Convergence](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergence.lean) (imports
  `Convergents`), [ContinuedFractions/MathlibCoverage](DLMF/AlgebraicAnalytic/ContinuedFractions/MathlibCoverage.lean);
- [ODE/Defs](DLMF/AlgebraicAnalytic/ODE/Defs.lean) (definitions; Mathlib only),
  [ODE/SecondOrder](DLMF/AlgebraicAnalytic/ODE/SecondOrder.lean) (imports `Defs` and
  `DLMFMathlib.Analysis.ODE.P1oEntireLinear`), [ODE/Transformations](DLMF/AlgebraicAnalytic/ODE/Transformations.lean)
  (imports `SecondOrder`), [ODE/SturmLiouville](DLMF/AlgebraicAnalytic/ODE/SturmLiouville.lean) (imports `Defs`).

**Counts.** The three sections have 85 numbered equations (§1.11: 26, §1.12: 28, §1.13: 31).
1.11.E8 (the worked example of the Horner scheme) is excluded: numerical. In scope: 84, all
covered by project declarations or upstream pointers. In addition 11 prose IDs carry tags
(1.11.ii–v, 1.12.ii, 1.12.iv, 1.12.v, 1.13.i–iii, 1.13.viii); 95 DLMF IDs are tagged or
pointed to. The eleven modules contain 28 definitions (26 tagged; `coeffInt`, `contFracTail`
are untagged helpers) and 126 theorems: 66 tagged proved theorems, 21 tagged admissions and 39
untagged proved helper and API lemmas; 26 `dlmf_upstream` pointers. Four proved theorems depend
on admissions: `exists_isFundamentalPair` and `isFundamentalPair_tfae` (on
`exists_isLinODE2SolOn`), `schwarzian_inverse` (on `schwarzian_comp`) and `vanVleck_arg_limit`
(on `vanVleck_arg_convs`).

Module admissions (`grep -cE 'by sorry|:= sorry|^\s*(·\s*)?sorry\s*$|exact sorry'`):

- Polynomials: Defs 0 (7 definitions), Zeros 3 (34 theorems), MathlibCoverage 0 (19 pointers).
- ContinuedFractions: Defs 0 (11 definitions), Convergents 4 (41 theorems), Convergence 3
  (11 theorems), MathlibCoverage 0 (7 pointers).
- ODE: Defs 0 (10 definitions), SecondOrder 3 (23 theorems), Transformations 4 (12 theorems),
  SturmLiouville 4 (5 theorems).

### Conventions and design (part g1d)

- Roots and branches (§1.11(iii)): Cardano and Ferrari are stated branch-free: for any cube
  root `A` of `-q/2 + √(q²/4 + p³/27)` (any square root) with `A ≠ 0` and `B = -p/(3A)`, the
  zeros are `A + B`, `ρA + ρ²B`, `ρ²A + ρB`; for Ferrari, any square roots `s_j` of the
  negatives of the resolvent roots with `s₁s₂s₃ = -q`. Depressions of the cubic and quartic
  carry `[CharZero]`.
- Discriminant 1.11.9 is related to Mathlib's `Polynomial.discr` (Sylvester-matrix definition)
  by the admitted `discr_eq_prod_roots`.
- Hurwitz criterion (§1.11(v)): the determinant ranges are read as `D_k` for `2k ≤ n` and
  `2k + 1 ≤ n` as printed; validated on 20000 random real polynomials of degree 1–7.
- Continued fractions use DLMF's indexing (`contFrac a b`, `a 0` unused) on top of Mathlib's
  `GenContFract`; `C_n` are the ratios `A_n/B_n` (`convs`), and the nested form (`convs'`)
  agrees with them when the nested tails do not vanish (1.12.4). 1.12.22 is stated for finite
  values. Pringsheim's theorem is proved in any complete normed field without `a_n ≠ 0`
  (stronger than DLMF).
- Differential equations: `IsLinODE2SolOn f g r w D` requires genuine differentiability of `w`
  and `w'` at each point of `D`, so the totalized `deriv` cannot create spurious solutions.
  DLMF integrals `∫ f dz` are primitives given as hypotheses (`HasDerivAt F (f z) z` on `D`),
  which keeps 1.13.5, 1.13.10, 1.13.13 and 1.13.16 branch-free. The Liouville transformation
  1.13.18–1.13.19 is stated in the variable `z` (with `d/dζ = (1/ζ') d/dz` and a chosen root
  `σ² = ζ'`); 1.13.20 (first form) uses a branch `τ` of `ż^-0.5`.
- §1.13(viii): the Sturm–Liouville eigenvalue predicates require the equation on `[a, b]` with
  two-sided derivatives (functions on `ℝ`); the Liouville-normal-form eigenvalue statements
  assume `p, ρ` of class `C²` and positive on all of `ℝ`.

### Suspected source imprecision (part g1d)

- §1.13(viii), Px10.p2 (iii): the Liouville transformation carries unmixed boundary conditions
  to unmixed ones, but periodic conditions to periodic ones only if `(pρ)^0.25`, its derivative
  and `ρ/p` agree at `a` and `b` (since `w(0) = m(a)u(a)` and `w(c) = m(b)u(b)`). The
  formalization (`liouville_eigenvalues_periodic`) carries these hypotheses.

No other errata: every formula checked numerically or symbolically agrees with DLMF as printed.

### Numbered formulas and prose items (part g1d)

## [§1.11 Zeros of Polynomials](https://dlmf.nist.gov/1.11)

- [1.11.E8](https://dlmf.nist.gov/1.11.E8): excluded: numerical (worked example of Horner's scheme).
- [1.11.E1](https://dlmf.nist.gov/1.11.E1): [`Polynomial.as_sum_range`](DLMF/AlgebraicAnalytic/Polynomials/MathlibCoverage.lean#L32) (upstream)
- [1.11.E2](https://dlmf.nist.gov/1.11.E2): [`Polynomial.modByMonic_add_div`](DLMF/AlgebraicAnalytic/Polynomials/MathlibCoverage.lean#L34) (upstream); [`DLMF.AlgebraicAnalytic.eval_eq_horner`](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean#L85) (proved)
- [1.11.E3](https://dlmf.nist.gov/1.11.E3): [`DLMF.AlgebraicAnalytic.hornerB`](DLMF/AlgebraicAnalytic/Polynomials/Defs.lean#L40) (definition); [`DLMF.AlgebraicAnalytic.hornerB_rec`](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean#L98) (proved); [`DLMF.AlgebraicAnalytic.hornerB_natDegree`](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean#L128) (proved)
- [1.11.E4](https://dlmf.nist.gov/1.11.E4): [`Polynomial.modByMonic_X_sub_C_eq_C_eval`](DLMF/AlgebraicAnalytic/Polynomials/MathlibCoverage.lean#L36) (upstream); [`DLMF.AlgebraicAnalytic.hornerB_zero`](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean#L57) (proved)
- [1.11.E5](https://dlmf.nist.gov/1.11.E5): [`DLMF.AlgebraicAnalytic.hornerC`](DLMF/AlgebraicAnalytic/Polynomials/Defs.lean#L48) (definition); [`DLMF.AlgebraicAnalytic.hornerC_rec`](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean#L134) (proved); [`DLMF.AlgebraicAnalytic.hornerC_natDegree`](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean#L142) (proved)
- [1.11.E6](https://dlmf.nist.gov/1.11.E6): [`DLMF.AlgebraicAnalytic.hornerC_one`](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean#L151) (proved)
- [1.11.E7](https://dlmf.nist.gov/1.11.E7): [`EuclideanDomain.div_add_mod`](DLMF/AlgebraicAnalytic/Polynomials/MathlibCoverage.lean#L38) (upstream); [`Polynomial.degree_mod_lt`](DLMF/AlgebraicAnalytic/Polynomials/MathlibCoverage.lean#L40) (upstream)
- [1.11.E9](https://dlmf.nist.gov/1.11.E9): [`Polynomial.discr`](DLMF/AlgebraicAnalytic/Polynomials/MathlibCoverage.lean#L54) (upstream); [`Polynomial.discr_of_degree_eq_two`](DLMF/AlgebraicAnalytic/Polynomials/MathlibCoverage.lean#L57) (upstream); [`Cubic.discr_eq_prod_three_roots`](DLMF/AlgebraicAnalytic/Polynomials/MathlibCoverage.lean#L59) (upstream); [`DLMF.AlgebraicAnalytic.discr_eq_prod_roots`](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean#L252) (admitted). DLMF form D = a_n^{2n-2} ∏_{j<k}(z_j-z_k)^2 for split f, against Mathlib `Polynomial.discr`.
- [1.11.E10](https://dlmf.nist.gov/1.11.E10): [`Polynomial.coeff_eq_esymm_roots_of_splits`](DLMF/AlgebraicAnalytic/Polynomials/MathlibCoverage.lean#L61) (upstream); [`Polynomial.Splits.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff`](DLMF/AlgebraicAnalytic/Polynomials/MathlibCoverage.lean#L63) (upstream); [`Polynomial.Splits.coeff_zero_eq_leadingCoeff_mul_prod_roots`](DLMF/AlgebraicAnalytic/Polynomials/MathlibCoverage.lean#L65) (upstream)
- [1.11.E11](https://dlmf.nist.gov/1.11.E11): [`quadratic_eq_zero_iff`](DLMF/AlgebraicAnalytic/Polynomials/MathlibCoverage.lean#L69) (upstream); [`discrim`](DLMF/AlgebraicAnalytic/Polynomials/MathlibCoverage.lean#L71) (upstream); [`DLMF.AlgebraicAnalytic.quadratic_roots_sum_prod`](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean#L263) (proved)
- [1.11.E12](https://dlmf.nist.gov/1.11.E12): [`DLMF.AlgebraicAnalytic.discr_reduced_cubic`](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean#L294) (proved)
- [1.11.E13](https://dlmf.nist.gov/1.11.E13): [`DLMF.AlgebraicAnalytic.cardano`](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean#L312) (proved). branch-free: for any A with A³ = -q/2 + √(q²/4+p³/27) (any square root), A ≠ 0, B = -p/(3A).
- [1.11.E14](https://dlmf.nist.gov/1.11.E14): [`DLMF.AlgebraicAnalytic.cardano`](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean#L312) (proved)
- [1.11.E15](https://dlmf.nist.gov/1.11.E15): [`DLMF.AlgebraicAnalytic.cardano_rho`](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean#L339) (proved)
- [1.11.E16](https://dlmf.nist.gov/1.11.E16): [`DLMF.AlgebraicAnalytic.quartic_comp_X_sub_C`](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean#L362) (proved). `[CharZero]`; the reduction to the depressed quartic.
- [1.11.E17](https://dlmf.nist.gov/1.11.E17): [`DLMF.AlgebraicAnalytic.discr_reduced_quartic`](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean#L379) (proved)
- [1.11.E18](https://dlmf.nist.gov/1.11.E18): [`DLMF.AlgebraicAnalytic.dlmfResolventCubic`](DLMF/AlgebraicAnalytic/Polynomials/Defs.lean#L55) (definition); [`DLMF.AlgebraicAnalytic.ferrari`](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean#L394) (proved). the resolvent cubic is a local `Cubic`; roots θ_j = -(α₁+α_{j+1})².
- [1.11.E19](https://dlmf.nist.gov/1.11.E19): [`DLMF.AlgebraicAnalytic.ferrari`](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean#L394) (proved). branch-free: any square roots s_j of -θ_j with s₁s₂s₃ = -q.
- [1.11.E20](https://dlmf.nist.gov/1.11.E20): [`DLMF.AlgebraicAnalytic.ferrari`](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean#L394) (proved)
- [1.11.E21](https://dlmf.nist.gov/1.11.E21): [`geom_sum_mul`](DLMF/AlgebraicAnalytic/Polynomials/MathlibCoverage.lean#L75) (upstream); [`Complex.mem_rootsOfUnity`](DLMF/AlgebraicAnalytic/Polynomials/MathlibCoverage.lean#L77) (upstream)
- [1.11.E22](https://dlmf.nist.gov/1.11.E22): [`DLMF.AlgebraicAnalytic.pow_eq_iff`](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean#L449) (proved). n-th roots of any nonzero w; 1.11.23 as the companion statement.
- [1.11.E23](https://dlmf.nist.gov/1.11.E23): [`DLMF.AlgebraicAnalytic.pow_eq_iff`](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean#L449) (proved)
- [1.11.E24](https://dlmf.nist.gov/1.11.E24): [`DLMF.AlgebraicAnalytic.IsStablePolynomial`](DLMF/AlgebraicAnalytic/Polynomials/Defs.lean#L62) (definition)
- [1.11.E25](https://dlmf.nist.gov/1.11.E25): [`DLMF.AlgebraicAnalytic.hurwitzDet`](DLMF/AlgebraicAnalytic/Polynomials/Defs.lean#L81) (definition); [`DLMF.AlgebraicAnalytic.hurwitzDet_one`](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean#L498) (proved); [`DLMF.AlgebraicAnalytic.hurwitzDet_two`](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean#L503) (proved); [`DLMF.AlgebraicAnalytic.hurwitzDet_three`](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean#L509) (proved)
- [1.11.E26](https://dlmf.nist.gov/1.11.E26): [`DLMF.AlgebraicAnalytic.hurwitzMatrix`](DLMF/AlgebraicAnalytic/Polynomials/Defs.lean#L74) (definition); [`DLMF.AlgebraicAnalytic.hurwitzDet`](DLMF/AlgebraicAnalytic/Polynomials/Defs.lean#L81) (definition)
- [1.11.ii](https://dlmf.nist.gov/1.11.ii): [`IsAlgClosed.card_roots_eq_natDegree`](DLMF/AlgebraicAnalytic/Polynomials/MathlibCoverage.lean#L44) (upstream); [`Polynomial.roots_countP_pos_le_signVariations`](DLMF/AlgebraicAnalytic/Polynomials/MathlibCoverage.lean#L47) (upstream); [`Polynomial.roots_comp_neg_X`](DLMF/AlgebraicAnalytic/Polynomials/MathlibCoverage.lean#L50) (upstream); [`Polynomial.eval₂_reverse_eq_zero_iff`](DLMF/AlgebraicAnalytic/Polynomials/MathlibCoverage.lean#L52) (upstream); [`DLMF.AlgebraicAnalytic.exists_root_sign_of_odd`](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean#L181) (proved); [`DLMF.AlgebraicAnalytic.exists_pos_neg_root_of_even`](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean#L203) (proved); [`DLMF.AlgebraicAnalytic.signVariations_sub_countP_pos_even`](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean#L224) (admitted); [`DLMF.AlgebraicAnalytic.roots_countP_neg_le_signVariations`](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean#L233) (proved); [`DLMF.AlgebraicAnalytic.isRoot_reverse_inv_iff`](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean#L242) (proved). Descartes parity (local, admitted) and the inequality (upstream); zeros of f(-z) and z^n f(1/z).
- [1.11.iii](https://dlmf.nist.gov/1.11.iii): [`DLMF.AlgebraicAnalytic.cubic_comp_X_sub_C`](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean#L279) (proved)
- [1.11.iv](https://dlmf.nist.gov/1.11.iv): [`DLMF.AlgebraicAnalytic.pow_eq_neg_one_iff`](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean#L425) (proved)
- [1.11.v](https://dlmf.nist.gov/1.11.v): [`DLMF.AlgebraicAnalytic.isStablePolynomial_iff_hurwitz`](DLMF/AlgebraicAnalytic/Polynomials/Zeros.lean#L517) (admitted). Hurwitz criterion; DLMF ranges of the determinants read as 2k ≤ n, 2k+1 ≤ n (validated: 20000 random polynomials, degrees 1–7).

## [§1.12 Continued Fractions](https://dlmf.nist.gov/1.12)

- [1.12.E1](https://dlmf.nist.gov/1.12.E1): [`DLMF.AlgebraicAnalytic.contFrac`](DLMF/AlgebraicAnalytic/ContinuedFractions/Defs.lean#L40) (definition)
- [1.12.E2](https://dlmf.nist.gov/1.12.E2): [`DLMF.AlgebraicAnalytic.contFrac`](DLMF/AlgebraicAnalytic/ContinuedFractions/Defs.lean#L40) (definition)
- [1.12.E3](https://dlmf.nist.gov/1.12.E3): [`DLMF.AlgebraicAnalytic.contFrac`](DLMF/AlgebraicAnalytic/ContinuedFractions/Defs.lean#L40) (definition)
- [1.12.E4](https://dlmf.nist.gov/1.12.E4): [`DLMF.AlgebraicAnalytic.contFrac_convs'_eq_convs`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergents.lean#L136) (proved); [`GenContFract.convs_eq_convs'`](DLMF/AlgebraicAnalytic/ContinuedFractions/MathlibCoverage.lean#L24) (upstream). nested form equals A_n/B_n when the nested tails do not vanish (Lean x/0 = 0).
- [1.12.E5](https://dlmf.nist.gov/1.12.E5): [`DLMF.AlgebraicAnalytic.contFrac_contsAux_rec`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergents.lean#L76) (proved); [`GenContFract.conts_recurrence`](DLMF/AlgebraicAnalytic/ContinuedFractions/MathlibCoverage.lean#L27) (upstream)
- [1.12.E6](https://dlmf.nist.gov/1.12.E6): [`DLMF.AlgebraicAnalytic.contFrac_initial`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergents.lean#L92) (proved); [`GenContFract.zeroth_contAux_eq_one_zero`](DLMF/AlgebraicAnalytic/ContinuedFractions/MathlibCoverage.lean#L29) (upstream); [`GenContFract.first_contAux_eq_h_one`](DLMF/AlgebraicAnalytic/ContinuedFractions/MathlibCoverage.lean#L31) (upstream)
- [1.12.E7](https://dlmf.nist.gov/1.12.E7): [`DLMF.AlgebraicAnalytic.contFrac_det`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergents.lean#L170) (proved); [`GenContFract.determinant`](DLMF/AlgebraicAnalytic/ContinuedFractions/MathlibCoverage.lean#L33) (upstream)
- [1.12.E8](https://dlmf.nist.gov/1.12.E8): [`DLMF.AlgebraicAnalytic.contFrac_convs_sub`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergents.lean#L196) (proved)
- [1.12.E9](https://dlmf.nist.gov/1.12.E9): [`DLMF.AlgebraicAnalytic.contFrac_convs_eq_sum`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergents.lean#L207) (proved); [`GenContFract.convs_eq_sum_of_forall_le`](DLMF/AlgebraicAnalytic/ContinuedFractions/MathlibCoverage.lean#L36) (upstream)
- [1.12.E10](https://dlmf.nist.gov/1.12.E10): [`DLMF.AlgebraicAnalytic.contFrac_a_eq`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergents.lean#L229) (proved)
- [1.12.E11](https://dlmf.nist.gov/1.12.E11): [`DLMF.AlgebraicAnalytic.contFrac_a_eq_convs`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergents.lean#L259) (proved)
- [1.12.E12](https://dlmf.nist.gov/1.12.E12): [`DLMF.AlgebraicAnalytic.contFrac_b_eq`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergents.lean#L245) (proved)
- [1.12.E13](https://dlmf.nist.gov/1.12.E13): [`DLMF.AlgebraicAnalytic.contFrac_b_eq_convs`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergents.lean#L276) (proved)
- [1.12.E14](https://dlmf.nist.gov/1.12.E14): [`DLMF.AlgebraicAnalytic.contFrac_initial_elements`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergents.lean#L294) (proved)
- [1.12.E15](https://dlmf.nist.gov/1.12.E15): [`DLMF.AlgebraicAnalytic.contFracEquiv_of_scale`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergents.lean#L314) (proved)
- [1.12.E16](https://dlmf.nist.gov/1.12.E16): [`DLMF.AlgebraicAnalytic.contFracEquiv_of_scale`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergents.lean#L314) (proved)
- [1.12.E17](https://dlmf.nist.gov/1.12.E17): [`DLMF.AlgebraicAnalytic.contFracEquiv_unit_denominators`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergents.lean#L336) (proved); [`DLMF.AlgebraicAnalytic.contFracEquiv_unit_numerators`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergents.lean#L370) (proved); [`DLMF.AlgebraicAnalytic.contFracUnitFactor`](DLMF/AlgebraicAnalytic/ContinuedFractions/Defs.lean#L65) (definition)
- [1.12.E18](https://dlmf.nist.gov/1.12.E18): [`DLMF.AlgebraicAnalytic.contFrac_euler_series`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergents.lean#L386) (proved); [`GenContFract.convs_euler`](DLMF/AlgebraicAnalytic/ContinuedFractions/MathlibCoverage.lean#L40) (upstream). stronger than DLMF: no hypothesis p_k ≠ 0.
- [1.12.E19](https://dlmf.nist.gov/1.12.E19): [`DLMF.AlgebraicAnalytic.contFrac_power_series`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergents.lean#L415) (proved)
- [1.12.E20](https://dlmf.nist.gov/1.12.E20): [`DLMF.AlgebraicAnalytic.contFracApprox`](DLMF/AlgebraicAnalytic/ContinuedFractions/Defs.lean#L53) (definition)
- [1.12.E21](https://dlmf.nist.gov/1.12.E21): [`DLMF.AlgebraicAnalytic.contFracApprox_zero`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergents.lean#L456) (proved); [`DLMF.AlgebraicAnalytic.contFracApprox_eq`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergents.lean#L498) (proved); [`DLMF.AlgebraicAnalytic.contFracApprox_tendsto_infty`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergents.lean#L516) (proved). C_n(w) = (A_n + A_{n-1} w)/(B_n + B_{n-1} w) and C_n(w) → C_{n-1} as w → ∞.
- [1.12.E22](https://dlmf.nist.gov/1.12.E22): [`DLMF.AlgebraicAnalytic.exists_contFrac_convs_iff`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergents.lean#L545) (proved). finite-valued form: convergent sequences of fractions with a_n ≠ 0 are exactly the sequences with C_n ≠ C_{n-1}.
- [1.12.E23](https://dlmf.nist.gov/1.12.E23): [`DLMF.AlgebraicAnalytic.contFrac_evenPart_convs`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergents.lean#L594) (admitted); [`DLMF.AlgebraicAnalytic.evenPartA`](DLMF/AlgebraicAnalytic/ContinuedFractions/Defs.lean#L86) (definition); [`DLMF.AlgebraicAnalytic.evenPartB`](DLMF/AlgebraicAnalytic/ContinuedFractions/Defs.lean#L95) (definition)
- [1.12.E24](https://dlmf.nist.gov/1.12.E24): [`DLMF.AlgebraicAnalytic.contFrac_oddPart_convs`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergents.lean#L612) (admitted); [`DLMF.AlgebraicAnalytic.oddPartA`](DLMF/AlgebraicAnalytic/ContinuedFractions/Defs.lean#L104) (definition); [`DLMF.AlgebraicAnalytic.oddPartB`](DLMF/AlgebraicAnalytic/ContinuedFractions/Defs.lean#L112) (definition)
- [1.12.E25](https://dlmf.nist.gov/1.12.E25): [`DLMF.AlgebraicAnalytic.pringsheim_norm_convs_lt_one`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergence.lean#L97) (proved); [`DLMF.AlgebraicAnalytic.pringsheim`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergence.lean#L114) (proved); [`DLMF.AlgebraicAnalytic.contFracConverges_of_pringsheim`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergence.lean#L136) (proved). Pringsheim; stronger than DLMF (a_n ≠ 0 not assumed), any complete normed field.
- [1.12.E26](https://dlmf.nist.gov/1.12.E26): [`DLMF.AlgebraicAnalytic.vanVleck_arg_convs`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergence.lean#L148) (admitted)
- [1.12.E27](https://dlmf.nist.gov/1.12.E27): [`DLMF.AlgebraicAnalytic.vanVleck_arg_convs`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergence.lean#L148) (admitted)
- [1.12.E28](https://dlmf.nist.gov/1.12.E28): [`DLMF.AlgebraicAnalytic.vanVleck_converges_iff`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergence.lean#L167) (admitted)
- [1.12.ii](https://dlmf.nist.gov/1.12.ii): [`DLMF.AlgebraicAnalytic.ContFracEquiv`](DLMF/AlgebraicAnalytic/ContinuedFractions/Defs.lean#L59) (definition)
- [1.12.iv](https://dlmf.nist.gov/1.12.iv): [`DLMF.AlgebraicAnalytic.exists_evenPart_iff`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergents.lean#L602) (admitted); [`DLMF.AlgebraicAnalytic.exists_oddPart_iff`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergents.lean#L620) (admitted); [`DLMF.AlgebraicAnalytic.IsContraction`](DLMF/AlgebraicAnalytic/ContinuedFractions/Defs.lean#L73) (definition)
- [1.12.v](https://dlmf.nist.gov/1.12.v): [`DLMF.AlgebraicAnalytic.vanVleck_even_odd`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergence.lean#L158) (admitted); [`DLMF.AlgebraicAnalytic.vanVleck_arg_limit`](DLMF/AlgebraicAnalytic/ContinuedFractions/Convergence.lean#L175) (proved from admissions); [`DLMF.AlgebraicAnalytic.ContFracConverges`](DLMF/AlgebraicAnalytic/ContinuedFractions/Defs.lean#L80) (definition). `vanVleck_arg_limit` is proved from the admitted `vanVleck_arg_convs`.

## [§1.13 Differential Equations](https://dlmf.nist.gov/1.13)

- [1.13.E1](https://dlmf.nist.gov/1.13.E1): [`DLMF.AlgebraicAnalytic.IsLinODE2SolOn`](DLMF/AlgebraicAnalytic/ODE/Defs.lean#L36) (definition)
- [1.13.E2](https://dlmf.nist.gov/1.13.E2): [`DLMF.AlgebraicAnalytic.IsFundamentalPair`](DLMF/AlgebraicAnalytic/ODE/Defs.lean#L43) (definition); [`DLMF.AlgebraicAnalytic.isFundamentalPair_of_wronskian_ne_zero`](DLMF/AlgebraicAnalytic/ODE/SecondOrder.lean#L133) (proved)
- [1.13.E3](https://dlmf.nist.gov/1.13.E3): [`DLMF.AlgebraicAnalytic.isFundamentalPair_of_initial`](DLMF/AlgebraicAnalytic/ODE/SecondOrder.lean#L156) (proved); [`DLMF.AlgebraicAnalytic.exists_isFundamentalPair`](DLMF/AlgebraicAnalytic/ODE/SecondOrder.lean#L166) (proved from admissions). `exists_isFundamentalPair` is proved from the admitted existence theorem `exists_isLinODE2SolOn`.
- [1.13.E4](https://dlmf.nist.gov/1.13.E4): [`DLMF.AlgebraicAnalytic.wronskian`](DLMF/AlgebraicAnalytic/ODE/Defs.lean#L50) (definition); [`DLMF.AlgebraicAnalytic.wronskianN`](DLMF/AlgebraicAnalytic/ODE/Defs.lean#L55) (definition); [`DLMF.AlgebraicAnalytic.wronskianN_two`](DLMF/AlgebraicAnalytic/ODE/SecondOrder.lean#L127) (proved)
- [1.13.E5](https://dlmf.nist.gov/1.13.E5): [`DLMF.AlgebraicAnalytic.wronskian_eq_mul_exp`](DLMF/AlgebraicAnalytic/ODE/SecondOrder.lean#L187) (proved); [`DLMF.AlgebraicAnalytic.wronskian_const_of_f_eq_zero`](DLMF/AlgebraicAnalytic/ODE/SecondOrder.lean#L205) (proved). with `F` a primitive of `f` on a connected open set (e^{-∫f} = e^{-F}).
- [1.13.E6](https://dlmf.nist.gov/1.13.E6): [`DLMF.AlgebraicAnalytic.isFundamentalPair_tfae`](DLMF/AlgebraicAnalytic/ODE/SecondOrder.lean#L229) (proved from admissions). TFAE on a simply connected domain; proved from the admitted existence theorem.
- [1.13.E7](https://dlmf.nist.gov/1.13.E7): [`DLMF.AlgebraicAnalytic.isLinODE2SolOn_param_analytic`](DLMF/AlgebraicAnalytic/ODE/SecondOrder.lean#L292) (admitted)
- [1.13.E8](https://dlmf.nist.gov/1.13.E8): [`DLMF.AlgebraicAnalytic.IsLinODE2SolOn`](DLMF/AlgebraicAnalytic/ODE/Defs.lean#L36) (definition); [`DLMF.AlgebraicAnalytic.exists_isLinODE2SolOn_inhom`](DLMF/AlgebraicAnalytic/ODE/SecondOrder.lean#L313) (admitted)
- [1.13.E9](https://dlmf.nist.gov/1.13.E9): [`DLMF.AlgebraicAnalytic.isLinODE2SolOn_inhom_eq`](DLMF/AlgebraicAnalytic/ODE/SecondOrder.lean#L323) (proved)
- [1.13.E10](https://dlmf.nist.gov/1.13.E10): [`DLMF.AlgebraicAnalytic.isLinODE2SolOn_varParam`](DLMF/AlgebraicAnalytic/ODE/SecondOrder.lean#L344) (proved). with primitives P, Q of w₁r/𝒲, w₂r/𝒲.
- [1.13.E11](https://dlmf.nist.gov/1.13.E11): [`DLMF.AlgebraicAnalytic.isLinODE2SolOn_inv`](DLMF/AlgebraicAnalytic/ODE/Transformations.lean#L39) (proved)
- [1.13.E12](https://dlmf.nist.gov/1.13.E12): [`DLMF.AlgebraicAnalytic.isLinODE2SolOn_inv`](DLMF/AlgebraicAnalytic/ODE/Transformations.lean#L39) (proved)
- [1.13.E13](https://dlmf.nist.gov/1.13.E13): [`DLMF.AlgebraicAnalytic.isLinODE2SolOn_elim_first`](DLMF/AlgebraicAnalytic/ODE/Transformations.lean#L72) (proved)
- [1.13.E14](https://dlmf.nist.gov/1.13.E14): [`DLMF.AlgebraicAnalytic.isLinODE2SolOn_elim_first`](DLMF/AlgebraicAnalytic/ODE/Transformations.lean#L72) (proved)
- [1.13.E15](https://dlmf.nist.gov/1.13.E15): [`DLMF.AlgebraicAnalytic.isLinODE2SolOn_elim_first`](DLMF/AlgebraicAnalytic/ODE/Transformations.lean#L72) (proved)
- [1.13.E16](https://dlmf.nist.gov/1.13.E16): [`DLMF.AlgebraicAnalytic.hasDerivAt_deriv_comp_eta`](DLMF/AlgebraicAnalytic/ODE/Transformations.lean#L105) (proved)
- [1.13.E17](https://dlmf.nist.gov/1.13.E17): [`DLMF.AlgebraicAnalytic.hasDerivAt_deriv_comp_eta`](DLMF/AlgebraicAnalytic/ODE/Transformations.lean#L105) (proved); [`DLMF.AlgebraicAnalytic.isLinODE2SolOn_comp_eta_iff`](DLMF/AlgebraicAnalytic/ODE/Transformations.lean#L133) (proved)
- [1.13.E18](https://dlmf.nist.gov/1.13.E18): [`DLMF.AlgebraicAnalytic.liouville_transformation`](DLMF/AlgebraicAnalytic/ODE/Transformations.lean#L158) (admitted)
- [1.13.E19](https://dlmf.nist.gov/1.13.E19): [`DLMF.AlgebraicAnalytic.liouville_transformation`](DLMF/AlgebraicAnalytic/ODE/Transformations.lean#L158) (admitted). stated in the variable z with a chosen root σ² = ζ'; validated symbolically.
- [1.13.E20](https://dlmf.nist.gov/1.13.E20): [`DLMF.AlgebraicAnalytic.schwarzian`](DLMF/AlgebraicAnalytic/ODE/Defs.lean#L61) (definition); [`DLMF.AlgebraicAnalytic.schwarzian_eq_sqrt`](DLMF/AlgebraicAnalytic/ODE/Transformations.lean#L172) (admitted)
- [1.13.E21](https://dlmf.nist.gov/1.13.E21): [`DLMF.AlgebraicAnalytic.schwarzian_comp`](DLMF/AlgebraicAnalytic/ODE/Transformations.lean#L180) (admitted)
- [1.13.E22](https://dlmf.nist.gov/1.13.E22): [`DLMF.AlgebraicAnalytic.schwarzian_inverse`](DLMF/AlgebraicAnalytic/ODE/Transformations.lean#L199) (proved from admissions). proved from the admitted Cayley identity `schwarzian_comp`.
- [1.13.E23](https://dlmf.nist.gov/1.13.E23): [`DLMF.AlgebraicAnalytic.product_solution_ode3`](DLMF/AlgebraicAnalytic/ODE/Transformations.lean#L215) (proved)
- [1.13.E24](https://dlmf.nist.gov/1.13.E24): [`DLMF.AlgebraicAnalytic.product_solution_IJ`](DLMF/AlgebraicAnalytic/ODE/Transformations.lean#L259) (admitted)
- [1.13.E25](https://dlmf.nist.gov/1.13.E25): [`DLMF.AlgebraicAnalytic.product_solution_IJ`](DLMF/AlgebraicAnalytic/ODE/Transformations.lean#L259) (admitted)
- [1.13.E26](https://dlmf.nist.gov/1.13.E26): [`DLMF.AlgebraicAnalytic.IsSturmLiouvilleSolOn`](DLMF/AlgebraicAnalytic/ODE/Defs.lean#L67) (definition)
- [1.13.E27](https://dlmf.nist.gov/1.13.E27): [`DLMF.AlgebraicAnalytic.SLUnmixedBC`](DLMF/AlgebraicAnalytic/ODE/Defs.lean#L74) (definition)
- [1.13.E28](https://dlmf.nist.gov/1.13.E28): [`DLMF.AlgebraicAnalytic.SLPeriodicBC`](DLMF/AlgebraicAnalytic/ODE/Defs.lean#L81) (definition)
- [1.13.E29](https://dlmf.nist.gov/1.13.E29): [`DLMF.AlgebraicAnalytic.liouville_normal_form`](DLMF/AlgebraicAnalytic/ODE/SturmLiouville.lean#L54) (admitted)
- [1.13.E30](https://dlmf.nist.gov/1.13.E30): [`DLMF.AlgebraicAnalytic.liouville_normal_form`](DLMF/AlgebraicAnalytic/ODE/SturmLiouville.lean#L54) (admitted)
- [1.13.E31](https://dlmf.nist.gov/1.13.E31): [`DLMF.AlgebraicAnalytic.liouville_normal_form`](DLMF/AlgebraicAnalytic/ODE/SturmLiouville.lean#L54) (admitted)
- [1.13.i](https://dlmf.nist.gov/1.13.i): [`DLMF.AlgebraicAnalytic.exists_isLinODE2SolOn`](DLMF/AlgebraicAnalytic/ODE/SecondOrder.lean#L89) (admitted); [`DLMF.AlgebraicAnalytic.exists_isLinODE2SolOn_univ`](DLMF/AlgebraicAnalytic/ODE/SecondOrder.lean#L98) (proved); [`DLMF.AlgebraicAnalytic.isLinODE2SolOn_unique`](DLMF/AlgebraicAnalytic/ODE/SecondOrder.lean#L109) (proved). existence on simply connected D admitted; entire coefficients proved; uniqueness proved.
- [1.13.ii](https://dlmf.nist.gov/1.13.ii): [`DLMF.AlgebraicAnalytic.isLinODE2SolOn_param_analytic`](DLMF/AlgebraicAnalytic/ODE/SecondOrder.lean#L292) (admitted)
- [1.13.iii](https://dlmf.nist.gov/1.13.iii): [`DLMF.AlgebraicAnalytic.exists_isLinODE2SolOn_inhom`](DLMF/AlgebraicAnalytic/ODE/SecondOrder.lean#L313) (admitted)
- [1.13.viii](https://dlmf.nist.gov/1.13.viii): [`DLMF.AlgebraicAnalytic.IsRegularSLEigenvalue`](DLMF/AlgebraicAnalytic/ODE/Defs.lean#L86) (definition); [`DLMF.AlgebraicAnalytic.IsPeriodicSLEigenvalue`](DLMF/AlgebraicAnalytic/ODE/Defs.lean#L96) (definition); [`DLMF.AlgebraicAnalytic.regularSL_eigenvalues`](DLMF/AlgebraicAnalytic/ODE/SturmLiouville.lean#L40) (admitted); [`DLMF.AlgebraicAnalytic.liouville_nodes`](DLMF/AlgebraicAnalytic/ODE/SturmLiouville.lean#L74) (proved); [`DLMF.AlgebraicAnalytic.liouville_eigenvalues_unmixed`](DLMF/AlgebraicAnalytic/ODE/SturmLiouville.lean#L93) (admitted); [`DLMF.AlgebraicAnalytic.liouville_eigenvalues_periodic`](DLMF/AlgebraicAnalytic/ODE/SturmLiouville.lean#L119) (admitted). periodic case of the transformation carries extra endpoint hypotheses (see design notes).

### Prose, informal and excluded items (part g1d)

- [1.11.i](https://dlmf.nist.gov/1.11.i): the division algorithm; covered by the statements of
  1.11.E1–1.11.E7, no separate tag. The worked examples of §1.11 (1.11.E8 and the numerical
  examples following the Cardano and Ferrari formulas): excluded: numerical.
- [1.12.i](https://dlmf.nist.gov/1.12.i): no statement (notation); the notation is the
  definition `contFrac`, tagged 1.12.E1–1.12.E3.
- [1.12.vi](https://dlmf.nist.gov/1.12.vi): no statement (references only, §3.10).
- [1.13.iv](https://dlmf.nist.gov/1.13.iv), [1.13.v](https://dlmf.nist.gov/1.13.v): covered by
  their numbered equations.
- [1.13.vi](https://dlmf.nist.gov/1.13.vi): no statement (references only, §2.7).
- [1.13.vii](https://dlmf.nist.gov/1.13.vii): no statement (references only, Kamke).

### Validation (part g1d)

Scripts in the agent scratch directory (`g1d_check1.py`–`g1d_check7.py`, mpmath and sympy)
checked: the depressed cubic and quartic, the discriminants 1.11.12 and 1.11.17, Cardano
1.11.13–1.11.15, the resolvent cubic and Ferrari 1.11.18–1.11.20, the Hurwitz criterion
(random polynomials), the equivalence transformations 1.12.15–1.12.17, Euler's fraction
1.12.18, 1.12.21, the even and odd parts 1.12.23–1.12.24 (with the continuant scale factors
`∏ b_{2k}` and `∏ b_{2k+1}`), 1.13.12, 1.13.15, 1.13.17, 1.13.19 (also in the `z`-form used
here), 1.13.20–1.13.23, 1.13.25 and 1.13.31. All agree with DLMF as printed.

## Part g1e: §§1.14–1.15 (agent g1e, 2026-10-27)

This part covers the definitions, numbered formulas, table rows and analytical assertions in
prose of [DLMF §1.14 Integral Transforms](https://dlmf.nist.gov/1.14) and
[DLMF §1.15 Summability Methods](https://dlmf.nist.gov/1.15), version 1.2.8. The Lean code is in
`DLMF/AlgebraicAnalytic/Transforms/` and `DLMF/AlgebraicAnalytic/Summability/` (namespace
`DLMF.AlgebraicAnalytic`, helper prefix `g1e_`). The modules, in import order, are
[Transforms/Defs](DLMF/AlgebraicAnalytic/Transforms/Defs.lean) (all §1.14 definitions),
[Transforms/Fourier](DLMF/AlgebraicAnalytic/Transforms/Fourier.lean) (§1.14(i)–(ii)),
[Transforms/Laplace](DLMF/AlgebraicAnalytic/Transforms/Laplace.lean) (§1.14(iii)),
[Transforms/MellinHilbertStieltjes](DLMF/AlgebraicAnalytic/Transforms/MellinHilbertStieltjes.lean)
(§1.14(iv)–(vi)), [Transforms/Tables](DLMF/AlgebraicAnalytic/Transforms/Tables.lean)
(§1.14(vii); imports `Laplace`) and
[Transforms/MathlibCoverage](DLMF/AlgebraicAnalytic/Transforms/MathlibCoverage.lean), all
importing `Transforms/Defs`; then
[Summability/Defs](DLMF/AlgebraicAnalytic/Summability/Defs.lean) (all §1.15 definitions; imports
`Transforms/Defs`), [Summability/Series](DLMF/AlgebraicAnalytic/Summability/Series.lean)
(§1.15(i)–(ii), (viii)),
[Summability/FourierSeries](DLMF/AlgebraicAnalytic/Summability/FourierSeries.lean) (§1.15(iii)),
[Summability/Integrals](DLMF/AlgebraicAnalytic/Summability/Integrals.lean) (§1.15(iv)–(v)),
[Summability/Fractional](DLMF/AlgebraicAnalytic/Summability/Fractional.lean) (§1.15(vi)–(vii))
and [Summability/MathlibCoverage](DLMF/AlgebraicAnalytic/Summability/MathlibCoverage.lean), all
importing `Summability/Defs`.

**Counts.** §1.14 has 51 numbered equations (1.14.1–1.14.50 and 1.14.7_5) and 5 tables with
60 rows; §1.15 has 57 numbered equations. In scope: 108 numbered equations and 60 table rows,
all covered (1.14.32 and 1.14.35 by upstream pointers only: Mathlib's `mellin` and
`mellinInv` are DLMF's 1.14.32 and 1.14.35). In addition 10 prose IDs (1.14.i, iii, iv, vi;
1.15.ii–vii) carry tags.
121 DLMF IDs are tagged on 194 declarations, and 21 `dlmf_upstream` pointers record Mathlib
coverage. The 208 declarations of the twelve modules are 38 definitions (all in the two `Defs`
modules), 41 proved theorems (of which 6 private `g1e_` helpers and 5 proved from admissions:
1.14.8, 1.14.15, 1.14.16, 1.14.37 and Table 1.14.4 row 6) and 129 direct admissions.

Module admissions (`grep -cE 'by sorry|:= sorry|^\s*(·\s*)?sorry\s*$|exact sorry'`) and
declarations:

- [Transforms/Defs](DLMF/AlgebraicAnalytic/Transforms/Defs.lean): 0 admissions; 11 definitions, 1 proved bridge lemma (`fourierTransform_eq_fourier`).
- [Transforms/Fourier](DLMF/AlgebraicAnalytic/Transforms/Fourier.lean): 9 admissions; 23 theorems: 14 proved (3 from admissions, 2 private helpers), 9 admitted.
- [Transforms/Laplace](DLMF/AlgebraicAnalytic/Transforms/Laplace.lean): 13 admissions; 16 theorems: 3 proved, 13 admitted.
- [Transforms/MellinHilbertStieltjes](DLMF/AlgebraicAnalytic/Transforms/MellinHilbertStieltjes.lean): 17 admissions; 1 definition (`pichoridesConstant`), 20 theorems: 3 proved (1 from admissions), 17 admitted.
- [Transforms/Tables](DLMF/AlgebraicAnalytic/Transforms/Tables.lean): 55 admissions; 60 theorems (one per table row): 5 proved (1 from admissions), 55 admitted.
- [Transforms/MathlibCoverage](DLMF/AlgebraicAnalytic/Transforms/MathlibCoverage.lean): 0 admissions; 16 `dlmf_upstream` pointers.
- [Summability/Defs](DLMF/AlgebraicAnalytic/Summability/Defs.lean): 0 admissions; 26 definitions, 1 proved bridge lemma (`fourierCoeffOn_two_pi_eq`).
- [Summability/Series](DLMF/AlgebraicAnalytic/Summability/Series.lean): 4 admissions; 6 theorems: 2 proved, 4 admitted.
- [Summability/FourierSeries](DLMF/AlgebraicAnalytic/Summability/FourierSeries.lean): 13 admissions; 16 theorems: 3 proved (1 private helper), 13 admitted.
- [Summability/Integrals](DLMF/AlgebraicAnalytic/Summability/Integrals.lean): 12 admissions; 19 theorems: 7 proved (3 private helpers), 12 admitted.
- [Summability/Fractional](DLMF/AlgebraicAnalytic/Summability/Fractional.lean): 6 admissions; 8 theorems: 2 proved, 6 admitted.
- [Summability/MathlibCoverage](DLMF/AlgebraicAnalytic/Summability/MathlibCoverage.lean): 0 admissions; 5 `dlmf_upstream` pointers.

### Domains, conventions and source corrections (part g1e)

- Normalizations follow DLMF: `fourierTransform f x = (2π)^{-1/2} ∫ f(t) e^{ixt} dt` (1.14.1),
  linked to Mathlib's `𝓕` (kernel `e^{-2πivw}`) by `fourierTransform_eq_fourier`; the
  convolution 1.14.5 carries the factor `(2π)^{-1/2}`; the Laplace transform is
  `∫_{(0,∞)} e^{-st} f(t) dt`; Mathlib's `mellin` is used for 1.14.32. Integrals are Lebesgue
  integrals, so every theorem carries integrability hypotheses; conditionally convergent
  integrals (1.14.3, 1.14.20, 1.14.34, table rows) are stated as limits of truncated integrals,
  principal values as `lim_{ε→0+}`.
- `HasAbelSum` and `HasBorelSum` include the convergence of the power series for `0 < x < 1`
  (respectively of `∑ a_n tⁿ/n!` for `t ≥ 0`), which DLMF leaves implicit. `HasAbelIntegral`
  uses Lebesgue integrals of `e^{-ε|t|}f(t)`, which is stricter than DLMF's improper integrals.
  `fejerKernel n θ` is `0` at `θ ∈ 2πℤ` (null set). Fourier coefficients 1.15.19 are Mathlib's
  `fourierCoeffOn Real.two_pi_pos`.
- The fractional calculus formulas are for `x ≥ 0` (DLMF erratum of version 1.0.1); theorems
  with derivatives take `x > 0` and `f` continuous on `[0, ∞)`. `fractionalDerivative` fixes
  `n = ⌊ℜα⌋ + 1`.
- Source corrections, each numerically verified with mpmath (scripts `g1e_riesz3.py`,
  `g1e_hilbert.py`, `g1e_complex.py`, `g1e_tables.py` of the acquisition):
  1. 1.14.45: the printed `∫|ℋf|^p ≤ A_p ∫|f|^p` is false; the sharp M. Riesz–Pichorides
     inequality is `‖ℋf‖_p ≤ A_p ‖f‖_p`, i.e. the constant `A_p^p` for the `p`-th powers.
     Evidence: for `p = 4/3`, the boundary values of `G(z) = (-iz)^{-0.745}(1 - iz)^{-1/2}`
     give the ratio `∫|ℋf|^p / ∫|f|^p ≈ 3.19 > A_p = 2.414` (and `< A_p^p = 3.2387`).
  2. §1.15(v), after 1.15.40: `lim_{y→0+} ℑΦ(x + iy)` is `−ℋf(x)` with DLMF's normalization
     1.14.41, not `ℋf(x)`; for `f(t) = 1/(1 + t²)`, `x = 0.6`: `ℑΦ(x + 0.001i) = 0.4405`,
     `ℋf(x) = −0.4412`.
  3. Table 1.14.2 row 11: with the principal logarithm of the quotient the entry fails for
     complex `a`, `b` (`a = 1 + 10i`, `b = 1 − 10i`, `x = 0.7`: integral `−2.3288i`, table
     `2.3365i`); it holds for `ln(a² + t²) − ln(b² + t²)`.
  4. Table 1.14.4 row 15: the condition `ℜ(s + a) > 0` is insufficient (`a = 1`, `s = ½`
     diverges); correct `ℜs > |ℜa|`. Rows 16–17: `ℜs > 0` suffices only for real `a`; for
     complex `a`, `ℜs > |ℑa|`.
  5. Table 1.14.5 row 3: the condition `ℜs > 1` is over-restrictive; the entry holds for
     `ℜs > 0` (acquired so). Row 7 needs `s ≠ 0` in Lean.
  6. 1.15.53 (missing hypothesis): `D^α D^β = D^{α+β}` fails for general `f`: for
     `f = x^{β−1}`, `ℜβ > 0`, the power rule gives `I^{n−β} f = (Γ(β)/Γ(n)) x^{n−1}`, so
     `D^β f = 0`, while `D^{α+β} f = (Γ(β)/Γ(−α)) x^{−α−1} ≠ 0` (e.g. `α = 1/2`, `β = 1/3`).
     Acquired for powers `x^μ` with `ℜμ > −1`, `ℜ(μ − β) > −1`.

### Numbered formulas and prose items (part g1e)

## [§1.14 Integral Transforms](https://dlmf.nist.gov/1.14)

- [1.14.i](https://dlmf.nist.gov/1.14.i): [`DLMF.AlgebraicAnalytic.continuous_fourierTransform`](DLMF/AlgebraicAnalytic/Transforms/Fourier.lean#L80) (proved); [`DLMF.AlgebraicAnalytic.tendsto_fourierTransform_cocompact`](DLMF/AlgebraicAnalytic/Transforms/Fourier.lean#L92) (proved); [`DLMF.AlgebraicAnalytic.integrable_fourierConvolution`](DLMF/AlgebraicAnalytic/Transforms/Fourier.lean#L188) (proved); [`DLMF.AlgebraicAnalytic.fourierTransform_fourierConvolution`](DLMF/AlgebraicAnalytic/Transforms/Fourier.lean#L201) (proved); [`DLMF.AlgebraicAnalytic.eq_of_fourierTransform_eq`](DLMF/AlgebraicAnalytic/Transforms/Fourier.lean#L258) (proved); Mathlib: [`Real.zero_at_infty_fourier`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/RiemannLebesgueLemma.html#Real.zero_at_infty_fourier) (different convention: Riemann–Lebesgue lemma, 𝓕 f → 0 at infinity); Mathlib: [`VectorFourier.fourierIntegral_continuous`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/FourierTransform.html#VectorFourier.fourierIntegral_continuous) (different convention: the Fourier integral of an integrable function is continuous); Mathlib: [`Real.fourier_mul_convolution_eq`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/Convolution.html#Real.fourier_mul_convolution_eq) (different convention: 𝓕(f ⋆ g) = 𝓕 f · 𝓕 g for integrable f, g). Continuity and Riemann–Lebesgue lemma of `𝓕f` for integrable `f` (i.p2–i.p3), the convolution theorem `𝓕(f∗g) = 𝓕f 𝓕g` (Px2.p1), uniqueness (Px5.p1, proved from Mathlib inversion through the bridge `fourierTransform_eq_fourier`). The Poisson summation paragraph Px4.p1 only cites §1.8(iv): no statement (references only).
- [1.14.E1](https://dlmf.nist.gov/1.14.E1): [`DLMF.AlgebraicAnalytic.fourierTransform`](DLMF/AlgebraicAnalytic/Transforms/Defs.lean#L48) (definition); Mathlib: [`Real.fourier_real_eq_integral_exp_smul`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/FourierTransform.html#Real.fourier_real_eq_integral_exp_smul) (different convention: 𝓕 f w = ∫ e^{-2πivw} f(v) dv; DLMF's 𝓕(f)(x) = (2π)^{-1/2} 𝓕 f (-x/2π)). Bridge `fourierTransform_eq_fourier` (proved): `𝓕f(x) = (2π)^{-1/2} 𝓕_Mathlib f(-x/2π)`.
- [1.14.E2](https://dlmf.nist.gov/1.14.E2): [`DLMF.AlgebraicAnalytic.norm_fourierTransform_le`](DLMF/AlgebraicAnalytic/Transforms/Fourier.lean#L65) (proved); Mathlib: [`Real.norm_fourier_le_integral_norm`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/FourierTransform.html#Real.norm_fourier_le_integral_norm) (different convention: ‖𝓕 f w‖ ≤ ∫ ‖f‖ (no factor (2π)^{-1/2})).
- [1.14.E3](https://dlmf.nist.gov/1.14.E3): [`DLMF.AlgebraicAnalytic.tendsto_fourierTransform_inversion_pv`](DLMF/AlgebraicAnalytic/Transforms/Fourier.lean#L110) (admitted). Principal value inversion at points where `f` is piecewise smooth, as the limit of `∫_{-R}^{R}`; value `(f(t-)+f(t+))/2`.
- [1.14.E4](https://dlmf.nist.gov/1.14.E4): [`DLMF.AlgebraicAnalytic.tendsto_fourierTransform_inversion_of_contDiff`](DLMF/AlgebraicAnalytic/Transforms/Fourier.lean#L123) (admitted); [`DLMF.AlgebraicAnalytic.fourierTransform_inversion`](DLMF/AlgebraicAnalytic/Transforms/Fourier.lean#L134) (proved); Mathlib: [`Continuous.fourierInv_fourier_eq`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/Inversion.html#Continuous.fourierInv_fourier_eq) (different convention: 𝓕⁻(𝓕 f) = f for continuous integrable f with 𝓕 f integrable); Mathlib: [`MeasureTheory.Integrable.fourierInv_fourier_eq`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/Inversion.html#MeasureTheory.Integrable.fourierInv_fourier_eq) (different convention: pointwise inversion at points of continuity, 𝓕 f integrable). Pointwise inversion for continuous `f` with `𝓕f` integrable proved through Mathlib; the form for `C¹` `f` with a principal-value integral admitted.
- [1.14.E5](https://dlmf.nist.gov/1.14.E5): [`DLMF.AlgebraicAnalytic.fourierConvolution`](DLMF/AlgebraicAnalytic/Transforms/Defs.lean#L64) (definition).
- [1.14.E6](https://dlmf.nist.gov/1.14.E6): [`DLMF.AlgebraicAnalytic.fourierConvolution_eq_integral`](DLMF/AlgebraicAnalytic/Transforms/Fourier.lean#L221) (admitted).
- [1.14.E7](https://dlmf.nist.gov/1.14.E7): [`DLMF.AlgebraicAnalytic.integral_fourierTransform_mul`](DLMF/AlgebraicAnalytic/Transforms/Fourier.lean#L230) (admitted).
- [1.14.E7_5](https://dlmf.nist.gov/1.14.E7_5): [`DLMF.AlgebraicAnalytic.integral_fourierTransform_mul_conj`](DLMF/AlgebraicAnalytic/Transforms/Fourier.lean#L238) (admitted); Mathlib: [`MeasureTheory.Lp.inner_fourier_eq`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/LpSpace.html#MeasureTheory.Lp.inner_fourier_eq) (partial: Parseval ⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫ for the L² extension of the transform).
- [1.14.E8](https://dlmf.nist.gov/1.14.E8): [`DLMF.AlgebraicAnalytic.integral_norm_fourierTransform_sq`](DLMF/AlgebraicAnalytic/Transforms/Fourier.lean#L246) (proved from admissions); Mathlib: [`MeasureTheory.Lp.norm_fourier_eq`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/LpSpace.html#MeasureTheory.Lp.norm_fourier_eq) (partial: Plancherel ‖𝓕 f‖₂ = ‖f‖₂ for the L² extension of the transform). Plancherel for `f ∈ L¹ ∩ L²`, proved from the admitted Parseval identity 1.14.7_5.
- [1.14.ii](https://dlmf.nist.gov/1.14.ii): No separate prose statement: the definitions and theorems of §1.14(ii) are 1.14.9–1.14.16.
- [1.14.E9](https://dlmf.nist.gov/1.14.E9): [`DLMF.AlgebraicAnalytic.fourierCosTransform`](DLMF/AlgebraicAnalytic/Transforms/Defs.lean#L54) (definition).
- [1.14.E10](https://dlmf.nist.gov/1.14.E10): [`DLMF.AlgebraicAnalytic.fourierSinTransform`](DLMF/AlgebraicAnalytic/Transforms/Defs.lean#L59) (definition).
- [1.14.E11](https://dlmf.nist.gov/1.14.E11): [`DLMF.AlgebraicAnalytic.tendsto_fourierCosTransform_inversion`](DLMF/AlgebraicAnalytic/Transforms/Fourier.lean#L292) (admitted).
- [1.14.E12](https://dlmf.nist.gov/1.14.E12): [`DLMF.AlgebraicAnalytic.tendsto_fourierSinTransform_inversion`](DLMF/AlgebraicAnalytic/Transforms/Fourier.lean#L304) (admitted).
- [1.14.E13](https://dlmf.nist.gov/1.14.E13): [`DLMF.AlgebraicAnalytic.integral_fourierCosTransform_mul`](DLMF/AlgebraicAnalytic/Transforms/Fourier.lean#L315) (admitted).
- [1.14.E14](https://dlmf.nist.gov/1.14.E14): [`DLMF.AlgebraicAnalytic.integral_fourierSinTransform_mul`](DLMF/AlgebraicAnalytic/Transforms/Fourier.lean#L325) (admitted).
- [1.14.E15](https://dlmf.nist.gov/1.14.E15): [`DLMF.AlgebraicAnalytic.integral_fourierCosTransform_sq`](DLMF/AlgebraicAnalytic/Transforms/Fourier.lean#L335) (proved from admissions). Proved from the admitted 1.14.13.
- [1.14.E16](https://dlmf.nist.gov/1.14.E16): [`DLMF.AlgebraicAnalytic.integral_fourierSinTransform_sq`](DLMF/AlgebraicAnalytic/Transforms/Fourier.lean#L342) (proved from admissions). Proved from the admitted 1.14.14.
- [1.14.iii](https://dlmf.nist.gov/1.14.iii): [`DLMF.AlgebraicAnalytic.integrableOn_laplace_integrand`](DLMF/AlgebraicAnalytic/Transforms/Laplace.lean#L36) (proved); [`DLMF.AlgebraicAnalytic.differentiableOn_laplaceTransform`](DLMF/AlgebraicAnalytic/Transforms/Laplace.lean#L58) (admitted); [`DLMF.AlgebraicAnalytic.eqOn_of_laplaceTransform_eq`](DLMF/AlgebraicAnalytic/Transforms/Laplace.lean#L233) (admitted). Absolute convergence for `ℜs > α` under 1.14.18 (Px8.p2), analyticity, and uniqueness (Px9) of the Laplace transform.
- [1.14.E17](https://dlmf.nist.gov/1.14.E17): [`DLMF.AlgebraicAnalytic.laplaceTransform`](DLMF/AlgebraicAnalytic/Transforms/Defs.lean#L70) (definition).
- [1.14.E18](https://dlmf.nist.gov/1.14.E18): [`DLMF.AlgebraicAnalytic.IsOfExponentialGrowth`](DLMF/AlgebraicAnalytic/Transforms/Defs.lean#L75) (definition).
- [1.14.E19](https://dlmf.nist.gov/1.14.E19): [`DLMF.AlgebraicAnalytic.tendsto_laplaceTransform_re_atTop`](DLMF/AlgebraicAnalytic/Transforms/Laplace.lean#L65) (admitted).
- [1.14.E20](https://dlmf.nist.gov/1.14.E20): [`DLMF.AlgebraicAnalytic.tendsto_laplaceTransform_inversion`](DLMF/AlgebraicAnalytic/Transforms/Laplace.lean#L72) (admitted); [`DLMF.AlgebraicAnalytic.laplaceTransform_inversion_of_isBigO`](DLMF/AlgebraicAnalytic/Transforms/Laplace.lean#L86) (admitted). Inversion as the limit of `∫_{σ-iT}^{σ+iT}` with value `(f(t-)+f(t+))/2`; the absolutely convergent form under an `O(s^{-K})` bound.
- [1.14.E21](https://dlmf.nist.gov/1.14.E21): [`DLMF.AlgebraicAnalytic.laplaceTransform_sub`](DLMF/AlgebraicAnalytic/Transforms/Laplace.lean#L99) (proved).
- [1.14.E22](https://dlmf.nist.gov/1.14.E22): [`DLMF.AlgebraicAnalytic.laplaceTransform_heaviside_shift`](DLMF/AlgebraicAnalytic/Transforms/Laplace.lean#L111) (proved).
- [1.14.E23](https://dlmf.nist.gov/1.14.E23): [`DLMF.AlgebraicAnalytic.iteratedDeriv_laplaceTransform`](DLMF/AlgebraicAnalytic/Transforms/Laplace.lean#L145) (admitted).
- [1.14.E24](https://dlmf.nist.gov/1.14.E24): [`DLMF.AlgebraicAnalytic.integral_laplaceTransform_ray`](DLMF/AlgebraicAnalytic/Transforms/Laplace.lean#L153) (admitted).
- [1.14.E25](https://dlmf.nist.gov/1.14.E25): [`DLMF.AlgebraicAnalytic.laplaceTransform_of_periodic`](DLMF/AlgebraicAnalytic/Transforms/Laplace.lean#L163) (admitted).
- [1.14.E26](https://dlmf.nist.gov/1.14.E26): [`DLMF.AlgebraicAnalytic.laplaceTransform_of_antiperiodic`](DLMF/AlgebraicAnalytic/Transforms/Laplace.lean#L173) (admitted).
- [1.14.E27](https://dlmf.nist.gov/1.14.E27): [`DLMF.AlgebraicAnalytic.laplaceTransform_deriv`](DLMF/AlgebraicAnalytic/Transforms/Laplace.lean#L183) (admitted).
- [1.14.E28](https://dlmf.nist.gov/1.14.E28): [`DLMF.AlgebraicAnalytic.laplaceTransform_deriv_of_jumps`](DLMF/AlgebraicAnalytic/Transforms/Laplace.lean#L194) (admitted). Piecewise `C¹` `f` with jumps at `t_1 < ⋯ < t_n` (Px13.p2).
- [1.14.E29](https://dlmf.nist.gov/1.14.E29): [`DLMF.AlgebraicAnalytic.laplaceTransform_iteratedDeriv`](DLMF/AlgebraicAnalytic/Transforms/Laplace.lean#L209) (admitted).
- [1.14.E30](https://dlmf.nist.gov/1.14.E30): [`DLMF.AlgebraicAnalytic.laplaceConvolution`](DLMF/AlgebraicAnalytic/Transforms/Defs.lean#L81) (definition).
- [1.14.E31](https://dlmf.nist.gov/1.14.E31): [`DLMF.AlgebraicAnalytic.laplaceTransform_laplaceConvolution`](DLMF/AlgebraicAnalytic/Transforms/Laplace.lean#L223) (admitted).
- [1.14.iv](https://dlmf.nist.gov/1.14.iv): [`DLMF.AlgebraicAnalytic.differentiableOn_mellin`](DLMF/AlgebraicAnalytic/Transforms/MellinHilbertStieltjes.lean#L53) (admitted); [`DLMF.AlgebraicAnalytic.mellinConvergent_of_isBigO`](DLMF/AlgebraicAnalytic/Transforms/MellinHilbertStieltjes.lean#L75) (proved); Mathlib: [`mellin_differentiableAt_of_isBigO_rpow`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/MellinTransform.html#mellin_differentiableAt_of_isBigO_rpow) (partial: analyticity in the strip under O-bounds at 0 and ∞); Mathlib: [`mellinConvergent_of_isBigO_rpow`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/MellinTransform.html#mellinConvergent_of_isBigO_rpow) (exact: x^{σ-1} f integrable for σ between the O-exponents (the note of §1.14(iv))). Analyticity in the strip `a < ℜs < b` (iv.p2) and the integrability criterion of iv.p3 (proved).
- [1.14.E32](https://dlmf.nist.gov/1.14.E32): Mathlib: [`mellin`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/MellinTransform.html#mellin) (exact: 𝓜(f)(s) = ∫₀^∞ x^{s-1} f(x) dx). `DLMF.AlgebraicAnalytic` uses Mathlib's `mellin` directly.
- [1.14.E33](https://dlmf.nist.gov/1.14.E33): [`DLMF.AlgebraicAnalytic.tendsto_mellin_vertical`](DLMF/AlgebraicAnalytic/Transforms/MellinHilbertStieltjes.lean#L61) (proved); Mathlib: [`mellin_eq_fourier`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/MellinInversion.html#mellin_eq_fourier) (partial: the Mellin transform on a vertical line is a Fourier transform (gives 1.14.33)). Proved for every `f` with `x^{σ-1}f` integrable, from Mathlib's `mellin_eq_fourier` and the Riemann–Lebesgue lemma.
- [1.14.E34](https://dlmf.nist.gov/1.14.E34): [`DLMF.AlgebraicAnalytic.tendsto_mellin_inversion_pv`](DLMF/AlgebraicAnalytic/Transforms/MellinHilbertStieltjes.lean#L87) (admitted).
- [1.14.E35](https://dlmf.nist.gov/1.14.E35): Mathlib: [`mellinInv_mellin_eq`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/MellinInversion.html#mellinInv_mellin_eq) (exact: f(x) = (1/2πi) ∫ x^{-s} 𝓜(f)(s) ds, with convergence on ℜs = σ and continuity at x). Upstream only: Mathlib's `mellinInv` is DLMF's inversion integral.
- [1.14.E36](https://dlmf.nist.gov/1.14.E36): [`DLMF.AlgebraicAnalytic.integral_mul_comp_mul_eq_mellin`](DLMF/AlgebraicAnalytic/Transforms/MellinHilbertStieltjes.lean#L100) (admitted).
- [1.14.E37](https://dlmf.nist.gov/1.14.E37): [`DLMF.AlgebraicAnalytic.integral_mul_eq_mellin`](DLMF/AlgebraicAnalytic/Transforms/MellinHilbertStieltjes.lean#L112) (proved from admissions). Proved from the admitted 1.14.36.
- [1.14.E38](https://dlmf.nist.gov/1.14.E38): [`DLMF.AlgebraicAnalytic.integral_sq_eq_mellin`](DLMF/AlgebraicAnalytic/Transforms/MellinHilbertStieltjes.lean#L125) (admitted).
- [1.14.E39](https://dlmf.nist.gov/1.14.E39): [`DLMF.AlgebraicAnalytic.mellinConvolution`](DLMF/AlgebraicAnalytic/Transforms/Defs.lean#L86) (definition).
- [1.14.E40](https://dlmf.nist.gov/1.14.E40): [`DLMF.AlgebraicAnalytic.mellin_mellinConvolution`](DLMF/AlgebraicAnalytic/Transforms/MellinHilbertStieltjes.lean#L135) (admitted).
- [1.14.v](https://dlmf.nist.gov/1.14.v): No separate prose statement beyond 1.14.41–1.14.46 (v.p1 introduces the definition).
- [1.14.E41](https://dlmf.nist.gov/1.14.E41): [`DLMF.AlgebraicAnalytic.hilbertTransform`](DLMF/AlgebraicAnalytic/Transforms/Defs.lean#L96) (definition); [`DLMF.AlgebraicAnalytic.ae_tendsto_hilbertTruncated`](DLMF/AlgebraicAnalytic/Transforms/MellinHilbertStieltjes.lean#L147) (admitted). `hilbertTransform` is the principal value `lim_{ε→0+}` of the truncated integral `hilbertTruncated`; existence a.e. for `f ∈ L^p`, `1 ≤ p < ∞`, admitted.
- [1.14.E42](https://dlmf.nist.gov/1.14.E42): [`DLMF.AlgebraicAnalytic.ae_tendsto_conjugatePoisson_hilbertTransform`](DLMF/AlgebraicAnalytic/Transforms/MellinHilbertStieltjes.lean#L155) (admitted).
- [1.14.E43](https://dlmf.nist.gov/1.14.E43): [`DLMF.AlgebraicAnalytic.hilbertTruncated_eq_integral_Ioi`](DLMF/AlgebraicAnalytic/Transforms/MellinHilbertStieltjes.lean#L165) (admitted).
- [1.14.E44](https://dlmf.nist.gov/1.14.E44): [`DLMF.AlgebraicAnalytic.hilbertTransform_hilbertTransform`](DLMF/AlgebraicAnalytic/Transforms/MellinHilbertStieltjes.lean#L174) (admitted).
- [1.14.E45](https://dlmf.nist.gov/1.14.E45): [`DLMF.AlgebraicAnalytic.hilbertTransform_lp_bound`](DLMF/AlgebraicAnalytic/Transforms/MellinHilbertStieltjes.lean#L187) (admitted); [`DLMF.AlgebraicAnalytic.integral_norm_hilbertTransform_sq`](DLMF/AlgebraicAnalytic/Transforms/MellinHilbertStieltjes.lean#L198) (admitted). **Corrected:** the printed `∫|ℋf|^p ≤ A_p ∫|f|^p` is false; the sharp inequality (Pichorides) has `A_p^p`, i.e. `‖ℋf‖_p ≤ A_p‖f‖_p`, with `A_p = tan(π/2p)` for `1 < p ≤ 2` and `cot(π/2p)` for `p ≥ 2` (`pichoridesConstant`). The `p = 2` isometry is separate.
- [1.14.E46](https://dlmf.nist.gov/1.14.E46): [`DLMF.AlgebraicAnalytic.tendsto_fourier_hilbertTransform`](DLMF/AlgebraicAnalytic/Transforms/MellinHilbertStieltjes.lean#L204) (admitted).
- [1.14.vi](https://dlmf.nist.gov/1.14.vi): [`DLMF.AlgebraicAnalytic.integrableOn_stieltjes_integrand`](DLMF/AlgebraicAnalytic/Transforms/MellinHilbertStieltjes.lean#L217) (admitted); [`DLMF.AlgebraicAnalytic.differentiableOn_stieltjesTransform`](DLMF/AlgebraicAnalytic/Transforms/MellinHilbertStieltjes.lean#L225) (admitted). Convergence and analyticity of the Stieltjes transform in the cut plane (vi.p2); uniform convergence on compacta not stated separately.
- [1.14.E47](https://dlmf.nist.gov/1.14.E47): [`DLMF.AlgebraicAnalytic.stieltjesTransform`](DLMF/AlgebraicAnalytic/Transforms/Defs.lean#L103) (definition).
- [1.14.E48](https://dlmf.nist.gov/1.14.E48): [`DLMF.AlgebraicAnalytic.iteratedDeriv_stieltjesTransform`](DLMF/AlgebraicAnalytic/Transforms/MellinHilbertStieltjes.lean#L235) (admitted).
- [1.14.E49](https://dlmf.nist.gov/1.14.E49): [`DLMF.AlgebraicAnalytic.tendsto_stieltjesTransform_jump`](DLMF/AlgebraicAnalytic/Transforms/MellinHilbertStieltjes.lean#L245) (admitted).
- [1.14.E50](https://dlmf.nist.gov/1.14.E50): [`DLMF.AlgebraicAnalytic.stieltjesTransform_eq_laplace_laplace`](DLMF/AlgebraicAnalytic/Transforms/MellinHilbertStieltjes.lean#L257) (admitted).
- [1.14.vii](https://dlmf.nist.gov/1.14.vii): Tables 1.14.1–1.14.5 (one theorem per row below); the section paragraph only cites Wong (1989): references only.
- [1.14.T1](https://dlmf.nist.gov/1.14.T1): [`DLMF.AlgebraicAnalytic.fourierTransform_indicator`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L59) (admitted); [`DLMF.AlgebraicAnalytic.fourierTransform_exp_neg_abs`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L67) (admitted); [`DLMF.AlgebraicAnalytic.fourierTransform_mul_exp_neg_abs`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L74) (admitted); [`DLMF.AlgebraicAnalytic.fourierTransform_abs_mul_exp_neg_abs`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L81) (admitted); [`DLMF.AlgebraicAnalytic.fourierTransform_exp_neg_abs_div_sqrt`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L88) (admitted); [`DLMF.AlgebraicAnalytic.fourierTransform_sinh_div_sinh`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L96) (admitted); [`DLMF.AlgebraicAnalytic.fourierTransform_cosh_div_cosh`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L105) (admitted); [`DLMF.AlgebraicAnalytic.fourierTransform_gaussian`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L115) (proved); [`DLMF.AlgebraicAnalytic.tendsto_fourierTransform_sin_sq`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L147) (admitted); [`DLMF.AlgebraicAnalytic.tendsto_fourierTransform_cos_sq`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L156) (admitted); Mathlib: [`fourierIntegral_gaussian`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Gaussian/FourierTransform.html#fourierIntegral_gaussian) (different convention: ∫ e^{itx} e^{-bx²} dx = (π/b)^{1/2} e^{-t²/(4b)}, ℜb > 0 (row 9)). All 10 rows (r2–r11). Rows with conditionally convergent integrals (r10, r11) as limits of `∫_{-R}^{R}`.
- [1.14.T2](https://dlmf.nist.gov/1.14.T2): [`DLMF.AlgebraicAnalytic.fourierCosTransform_indicator`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L167) (admitted); [`DLMF.AlgebraicAnalytic.fourierCosTransform_inv_sq_add_sq`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L175) (admitted); [`DLMF.AlgebraicAnalytic.fourierCosTransform_inv_sq_add_sq_sq`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L182) (admitted); [`DLMF.AlgebraicAnalytic.fourierCosTransform_quartic`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L189) (admitted); [`DLMF.AlgebraicAnalytic.fourierCosTransform_exp_neg`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L196) (admitted); [`DLMF.AlgebraicAnalytic.fourierCosTransform_gaussian`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L203) (admitted); [`DLMF.AlgebraicAnalytic.tendsto_fourierCosTransform_sin_sq`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L210) (admitted); [`DLMF.AlgebraicAnalytic.tendsto_fourierCosTransform_cos_sq`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L219) (admitted); [`DLMF.AlgebraicAnalytic.fourierCosTransform_log_one_add`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L228) (admitted); [`DLMF.AlgebraicAnalytic.fourierCosTransform_log_sub_log`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L236) (admitted). All 10 rows. **Corrected (row 11):** for complex `a`, `b` the principal `ln((a²+t²)/(b²+t²))` must be read as `ln(a²+t²) − ln(b²+t²)` (counterexample `a = 1+10i`, `b = 1−10i`, `x = 0.7`: integral `−2.3288i`, table `2.3365i`); rows 8–9 as limits of `∫_0^R`.
- [1.14.T3](https://dlmf.nist.gov/1.14.T3): [`DLMF.AlgebraicAnalytic.tendsto_fourierSinTransform_inv`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L248) (admitted); [`DLMF.AlgebraicAnalytic.tendsto_fourierSinTransform_inv_sqrt`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L256) (admitted); [`DLMF.AlgebraicAnalytic.fourierSinTransform_rpow_neg_three_halves`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L264) (admitted); [`DLMF.AlgebraicAnalytic.tendsto_fourierSinTransform_div_sq_add_sq`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L270) (admitted); [`DLMF.AlgebraicAnalytic.fourierSinTransform_div_sq_add_sq_sq`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L280) (admitted); [`DLMF.AlgebraicAnalytic.fourierSinTransform_inv_mul_sq_add_sq`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L287) (admitted); [`DLMF.AlgebraicAnalytic.fourierSinTransform_exp_neg_div`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L294) (admitted); [`DLMF.AlgebraicAnalytic.fourierSinTransform_exp_neg`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L301) (admitted); [`DLMF.AlgebraicAnalytic.fourierSinTransform_mul_exp_neg`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L308) (admitted); [`DLMF.AlgebraicAnalytic.fourierSinTransform_mul_gaussian`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L315) (admitted); [`DLMF.AlgebraicAnalytic.tendsto_fourierSinTransform_sin_div`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L323) (admitted); [`DLMF.AlgebraicAnalytic.tendsto_fourierSinTransform_arctan_abel`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L333) (admitted); [`DLMF.AlgebraicAnalytic.tendsto_fourierSinTransform_log_abs`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L343) (admitted). All 13 rows; conditionally convergent rows as limits of `∫_0^R`; row 13 (`arctan`) as an Abel limit.
- [1.14.T4](https://dlmf.nist.gov/1.14.T4): [`DLMF.AlgebraicAnalytic.laplaceTransform_exp_neg`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L354) (proved); [`DLMF.AlgebraicAnalytic.laplaceTransform_one`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L370) (proved); [`DLMF.AlgebraicAnalytic.laplaceTransform_pow_div_factorial`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L377) (admitted); [`DLMF.AlgebraicAnalytic.laplaceTransform_inv_sqrt`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L383) (admitted); [`DLMF.AlgebraicAnalytic.laplaceTransform_pow_mul_exp_neg_div_factorial`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L389) (proved from admissions); [`DLMF.AlgebraicAnalytic.laplaceTransform_exp_neg_sub_exp_neg`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L402) (proved); [`DLMF.AlgebraicAnalytic.laplaceTransform_sin`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L434) (admitted); [`DLMF.AlgebraicAnalytic.laplaceTransform_cos`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L440) (admitted); [`DLMF.AlgebraicAnalytic.laplaceTransform_sinh`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L446) (admitted); [`DLMF.AlgebraicAnalytic.laplaceTransform_cosh`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L452) (admitted); [`DLMF.AlgebraicAnalytic.laplaceTransform_mul_sin`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L458) (admitted); [`DLMF.AlgebraicAnalytic.laplaceTransform_mul_cos`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L464) (admitted); [`DLMF.AlgebraicAnalytic.laplaceTransform_exp_neg_sub_exp_neg_div`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L471) (admitted); [`DLMF.AlgebraicAnalytic.laplaceTransform_one_sub_cosh_div`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L480) (admitted); [`DLMF.AlgebraicAnalytic.laplaceTransform_one_sub_cos_div`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L489) (admitted); [`DLMF.AlgebraicAnalytic.laplaceTransform_sin_div`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L497) (admitted); Mathlib: [`integral_exp_mul_complex_Ioi`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.html#integral_exp_mul_complex_Ioi) (special case: ∫_c^∞ e^{ax} dx = -e^{ac}/a, ℜa < 0 (rows 2 and 5)). All 16 rows; four proved (rows 2, 5, 6, 7; row 6 from the admitted row 3). **Corrected conditions:** row 15 needs `ℜs > |ℜa|` (printed `ℜ(s+a) > 0` is insufficient); rows 16–17 need `ℜs > |ℑa|` for complex `a` (printed `ℜs > 0` suffices only for real `a`).
- [1.14.T5](https://dlmf.nist.gov/1.14.T5): [`DLMF.AlgebraicAnalytic.mellin_indicator_lt`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L506) (admitted); [`DLMF.AlgebraicAnalytic.mellin_log_indicator_lt`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L512) (admitted); [`DLMF.AlgebraicAnalytic.tendsto_mellin_inv_one_sub_pv`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L520) (admitted); [`DLMF.AlgebraicAnalytic.mellin_inv_one_add`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L529) (admitted); [`DLMF.AlgebraicAnalytic.mellin_log_one_add_mul`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L535) (admitted); [`DLMF.AlgebraicAnalytic.mellin_log_abs_one_add_div_one_sub`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L543) (admitted); [`DLMF.AlgebraicAnalytic.mellin_log_one_add_div`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L551) (admitted); [`DLMF.AlgebraicAnalytic.mellin_arctan`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L558) (admitted); [`DLMF.AlgebraicAnalytic.mellin_arccot`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L565) (admitted); [`DLMF.AlgebraicAnalytic.mellin_poisson_cos`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L572) (admitted); [`DLMF.AlgebraicAnalytic.mellin_poisson_sin`](DLMF/AlgebraicAnalytic/Transforms/Tables.lean#L581) (admitted). All 11 rows; row 4 as a principal value. Row 3 holds for `ℜs > 0` (printed `ℜs > 1` is over-restrictive; acquired with the weaker hypothesis); row 7 needs `s ≠ 0` in Lean (`0/0` at `s = 0`).
- [1.14.viii](https://dlmf.nist.gov/1.14.viii): No statement (references only): list of compendia of transforms.

## [§1.15 Summability Methods](https://dlmf.nist.gov/1.15)

- [1.15.i](https://dlmf.nist.gov/1.15.i): Definitions only (1.15.1–1.15.9).
- [1.15.E1](https://dlmf.nist.gov/1.15.E1): [`DLMF.AlgebraicAnalytic.seriesPartialSum`](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L57) (definition).
- [1.15.E2](https://dlmf.nist.gov/1.15.E2): [`DLMF.AlgebraicAnalytic.HasAbelSum`](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L62) (definition). Includes the convergence of `∑ a_n xⁿ` for `0 < x < 1`, implicit in DLMF.
- [1.15.E3](https://dlmf.nist.gov/1.15.E3): [`DLMF.AlgebraicAnalytic.HasAbelSum`](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L62) (definition).
- [1.15.E4](https://dlmf.nist.gov/1.15.E4): [`DLMF.AlgebraicAnalytic.HasCesaroSum`](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L73) (definition).
- [1.15.E5](https://dlmf.nist.gov/1.15.E5): [`DLMF.AlgebraicAnalytic.HasCesaroSum`](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L73) (definition).
- [1.15.E6](https://dlmf.nist.gov/1.15.E6): [`DLMF.AlgebraicAnalytic.HasCesaroSumOfOrder`](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L83) (definition).
- [1.15.E7](https://dlmf.nist.gov/1.15.E7): [`DLMF.AlgebraicAnalytic.HasCesaroSumOfOrder`](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L83) (definition).
- [1.15.E8](https://dlmf.nist.gov/1.15.E8): [`DLMF.AlgebraicAnalytic.HasBorelSum`](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L89) (definition). Includes the convergence of `∑ a_n tⁿ/n!` for `t ≥ 0`.
- [1.15.E9](https://dlmf.nist.gov/1.15.E9): [`DLMF.AlgebraicAnalytic.HasBorelSum`](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L89) (definition).
- [1.15.ii](https://dlmf.nist.gov/1.15.ii): [`DLMF.AlgebraicAnalytic.hasCesaroSum_of_tendsto`](DLMF/AlgebraicAnalytic/Summability/Series.lean#L59) (proved); [`DLMF.AlgebraicAnalytic.hasCesaroSumOfOrder_of_tendsto`](DLMF/AlgebraicAnalytic/Summability/Series.lean#L72) (admitted); [`DLMF.AlgebraicAnalytic.hasBorelSum_of_tendsto`](DLMF/AlgebraicAnalytic/Summability/Series.lean#L79) (admitted); Mathlib: [`Filter.Tendsto.cesaro_smul`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Asymptotics/SpecificAsymptotics.html#Filter.Tendsto.cesaro_smul) (partial: averages of a convergent sequence converge to its limit ((C,1) regularity)). Regularity of the (C,1), (C,α) and Borel methods.
- [1.15.E10](https://dlmf.nist.gov/1.15.E10): [`DLMF.AlgebraicAnalytic.hasAbelSum_of_tendsto`](DLMF/AlgebraicAnalytic/Summability/Series.lean#L31) (proved); Mathlib: [`Complex.tendsto_tsum_powerSeries_nhdsWithin_lt`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/AbelLimit.html#Complex.tendsto_tsum_powerSeries_nhdsWithin_lt) (exact: Abel's theorem, ∑ a_n xⁿ → ∑ a_n as x → 1⁻ for a convergent series (complex terms)).
- [1.15.E11](https://dlmf.nist.gov/1.15.E11): [`DLMF.AlgebraicAnalytic.hasAbelSum_of_tendsto`](DLMF/AlgebraicAnalytic/Summability/Series.lean#L31) (proved); Mathlib: [`Real.tendsto_tsum_powerSeries_nhdsWithin_lt`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/AbelLimit.html#Real.tendsto_tsum_powerSeries_nhdsWithin_lt) (special case: Abel's theorem for real terms).
- [1.15.iii](https://dlmf.nist.gov/1.15.iii): [`DLMF.AlgebraicAnalytic.harmonicOnNhd_abelMean`](DLMF/AlgebraicAnalytic/Summability/FourierSeries.lean#L148) (admitted). The Abel mean is harmonic in the unit disk (Px8–Px9).
- [1.15.E12](https://dlmf.nist.gov/1.15.E12): [`DLMF.AlgebraicAnalytic.abelPoissonKernel`](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L99) (definition); [`DLMF.AlgebraicAnalytic.hasSum_abelPoissonKernel`](DLMF/AlgebraicAnalytic/Summability/FourierSeries.lean#L33) (admitted).
- [1.15.E13](https://dlmf.nist.gov/1.15.E13): [`DLMF.AlgebraicAnalytic.integral_abelPoissonKernel`](DLMF/AlgebraicAnalytic/Summability/FourierSeries.lean#L40) (admitted).
- [1.15.E14](https://dlmf.nist.gov/1.15.E14): [`DLMF.AlgebraicAnalytic.tendstoUniformlyOn_abelPoissonKernel`](DLMF/AlgebraicAnalytic/Summability/FourierSeries.lean#L59) (proved).
- [1.15.E15](https://dlmf.nist.gov/1.15.E15): [`DLMF.AlgebraicAnalytic.fejerKernel`](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L104) (definition). At `θ ∈ 2πℤ` Lean's quotient is `0` rather than `n+1` (null set).
- [1.15.E16](https://dlmf.nist.gov/1.15.E16): [`DLMF.AlgebraicAnalytic.integral_fejerKernel`](DLMF/AlgebraicAnalytic/Summability/FourierSeries.lean#L94) (admitted).
- [1.15.E17](https://dlmf.nist.gov/1.15.E17): [`DLMF.AlgebraicAnalytic.tendstoUniformlyOn_fejerKernel`](DLMF/AlgebraicAnalytic/Summability/FourierSeries.lean#L100) (proved).
- [1.15.E18](https://dlmf.nist.gov/1.15.E18): [`DLMF.AlgebraicAnalytic.abelMean`](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L129) (definition).
- [1.15.E19](https://dlmf.nist.gov/1.15.E19): [`DLMF.AlgebraicAnalytic.fourierCoeffOn_two_pi_eq`](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L110) (proved); Mathlib: [`fourierCoeffOn`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/AddCircle.html#fourierCoeffOn) (different convention: Fourier coefficient on [a, b]; DLMF's F(n) is fourierCoeffOn on [0, 2π]). Bridge `fourierCoeffOn_two_pi_eq` (proved): DLMF's `F(n)` is `fourierCoeffOn Real.two_pi_pos f n`.
- [1.15.E20](https://dlmf.nist.gov/1.15.E20): [`DLMF.AlgebraicAnalytic.abelMean_eq_integral`](DLMF/AlgebraicAnalytic/Summability/FourierSeries.lean#L139) (admitted).
- [1.15.E21](https://dlmf.nist.gov/1.15.E21): [`DLMF.AlgebraicAnalytic.fourierCesaroMean`](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L140) (definition).
- [1.15.E22](https://dlmf.nist.gov/1.15.E22): [`DLMF.AlgebraicAnalytic.fourierPartialSum`](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L135) (definition).
- [1.15.E23](https://dlmf.nist.gov/1.15.E23): [`DLMF.AlgebraicAnalytic.fourierCesaroMean_eq_integral`](DLMF/AlgebraicAnalytic/Summability/FourierSeries.lean#L155) (admitted).
- [1.15.E24](https://dlmf.nist.gov/1.15.E24): [`DLMF.AlgebraicAnalytic.tendsto_abelMean`](DLMF/AlgebraicAnalytic/Summability/FourierSeries.lean#L164) (admitted); [`DLMF.AlgebraicAnalytic.tendsto_fourierCesaroMean`](DLMF/AlgebraicAnalytic/Summability/FourierSeries.lean#L173) (admitted); [`DLMF.AlgebraicAnalytic.tendstoUniformly_abelMean`](DLMF/AlgebraicAnalytic/Summability/FourierSeries.lean#L182) (admitted); [`DLMF.AlgebraicAnalytic.tendstoUniformly_fourierCesaroMean`](DLMF/AlgebraicAnalytic/Summability/FourierSeries.lean#L190) (admitted).
- [1.15.E25](https://dlmf.nist.gov/1.15.E25): [`DLMF.AlgebraicAnalytic.differentiableOn_fourierAnalyticExtension`](DLMF/AlgebraicAnalytic/Summability/FourierSeries.lean#L198) (admitted).
- [1.15.E26](https://dlmf.nist.gov/1.15.E26): [`DLMF.AlgebraicAnalytic.differentiableOn_fourierAnalyticExtension`](DLMF/AlgebraicAnalytic/Summability/FourierSeries.lean#L198) (admitted).
- [1.15.E27](https://dlmf.nist.gov/1.15.E27): [`DLMF.AlgebraicAnalytic.fourierAnalyticExtension`](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L145) (definition); [`DLMF.AlgebraicAnalytic.differentiableOn_fourierAnalyticExtension`](DLMF/AlgebraicAnalytic/Summability/FourierSeries.lean#L198) (admitted); [`DLMF.AlgebraicAnalytic.re_fourierAnalyticExtension`](DLMF/AlgebraicAnalytic/Summability/FourierSeries.lean#L209) (admitted).
- [1.15.E28](https://dlmf.nist.gov/1.15.E28): [`DLMF.AlgebraicAnalytic.im_fourierAnalyticExtension`](DLMF/AlgebraicAnalytic/Summability/FourierSeries.lean#L219) (admitted).
- [1.15.iv](https://dlmf.nist.gov/1.15.iv): [`DLMF.AlgebraicAnalytic.hasAbelIntegral_of_integrable`](DLMF/AlgebraicAnalytic/Summability/Integrals.lean#L40) (proved); [`DLMF.AlgebraicAnalytic.hasCesaroIntegral_of_integrable`](DLMF/AlgebraicAnalytic/Summability/Integrals.lean#L68) (admitted); [`DLMF.AlgebraicAnalytic.hasCesaroIntegral_of_tendsto`](DLMF/AlgebraicAnalytic/Summability/Integrals.lean#L75) (admitted); [`DLMF.AlgebraicAnalytic.hasAbelIntegral_of_tendsto`](DLMF/AlgebraicAnalytic/Summability/Integrals.lean#L83) (admitted). Abel and (C,1) summability of absolutely integrable functions (Lebesgue `HasAbelIntegral`; stricter than DLMF's improper integrals) and regularity for improper integrals.
- [1.15.E29](https://dlmf.nist.gov/1.15.E29): [`DLMF.AlgebraicAnalytic.HasAbelIntegral`](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L154) (definition).
- [1.15.E30](https://dlmf.nist.gov/1.15.E30): [`DLMF.AlgebraicAnalytic.HasAbelIntegral`](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L154) (definition).
- [1.15.E31](https://dlmf.nist.gov/1.15.E31): [`DLMF.AlgebraicAnalytic.HasCesaroIntegral`](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L161) (definition).
- [1.15.E32](https://dlmf.nist.gov/1.15.E32): [`DLMF.AlgebraicAnalytic.HasCesaroIntegral`](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L161) (definition).
- [1.15.v](https://dlmf.nist.gov/1.15.v): [`DLMF.AlgebraicAnalytic.re_poissonCauchyIntegral`](DLMF/AlgebraicAnalytic/Summability/Integrals.lean#L181) (proved); [`DLMF.AlgebraicAnalytic.differentiableOn_poissonCauchyIntegral`](DLMF/AlgebraicAnalytic/Summability/Integrals.lean#L218) (admitted); [`DLMF.AlgebraicAnalytic.tendsto_im_poissonCauchyIntegral`](DLMF/AlgebraicAnalytic/Summability/Integrals.lean#L225) (admitted). `ℜΦ = h` (proved) and analyticity of `Φ` (admitted). **Corrected:** DLMF says `lim_{y→0+} ℑΦ(x+iy)` is the Hilbert transform; with DLMF's normalization 1.14.41 it is `−ℋf(x)` (`f = 1/(1+t²)`, `x = 0.6`: `ℑΦ(x+0.001i) = 0.4405`, `ℋf(x) = −0.4412`); acquired with the sign corrected.
- [1.15.E33](https://dlmf.nist.gov/1.15.E33): [`DLMF.AlgebraicAnalytic.halfPlanePoissonKernel`](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L168) (definition).
- [1.15.E34](https://dlmf.nist.gov/1.15.E34): [`DLMF.AlgebraicAnalytic.integral_halfPlanePoissonKernel`](DLMF/AlgebraicAnalytic/Summability/Integrals.lean#L95) (proved); Mathlib: [`integral_univ_inv_one_add_sq`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.html#integral_univ_inv_one_add_sq) (special case: ∫ (1 + x²)⁻¹ dx = π, the case y = 1 of (1/2π) ∫ P(x, y) dx = 1). Proved for all `y > 0` from Mathlib's `integral_univ_inv_one_add_sq`.
- [1.15.E35](https://dlmf.nist.gov/1.15.E35): [`DLMF.AlgebraicAnalytic.tendsto_integral_halfPlanePoissonKernel_tail`](DLMF/AlgebraicAnalytic/Summability/Integrals.lean#L112) (admitted).
- [1.15.E36](https://dlmf.nist.gov/1.15.E36): [`DLMF.AlgebraicAnalytic.fourierAbelMean`](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L173) (definition).
- [1.15.E37](https://dlmf.nist.gov/1.15.E37): [`DLMF.AlgebraicAnalytic.fourierAbelMean_eq_poisson`](DLMF/AlgebraicAnalytic/Summability/Integrals.lean#L118) (admitted).
- [1.15.E38](https://dlmf.nist.gov/1.15.E38): [`DLMF.AlgebraicAnalytic.tendsto_integral_norm_fourierAbelMean_sub`](DLMF/AlgebraicAnalytic/Summability/Integrals.lean#L127) (admitted).
- [1.15.E39](https://dlmf.nist.gov/1.15.E39): [`DLMF.AlgebraicAnalytic.poissonCauchyIntegral`](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L180) (definition).
- [1.15.E40](https://dlmf.nist.gov/1.15.E40): [`DLMF.AlgebraicAnalytic.im_poissonCauchyIntegral`](DLMF/AlgebraicAnalytic/Summability/Integrals.lean#L200) (proved).
- [1.15.E41](https://dlmf.nist.gov/1.15.E41): [`DLMF.AlgebraicAnalytic.fejerKernelLine`](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L185) (definition).
- [1.15.E42](https://dlmf.nist.gov/1.15.E42): [`DLMF.AlgebraicAnalytic.integral_fejerKernelLine`](DLMF/AlgebraicAnalytic/Summability/Integrals.lean#L236) (admitted).
- [1.15.E43](https://dlmf.nist.gov/1.15.E43): [`DLMF.AlgebraicAnalytic.tendsto_integral_fejerKernelLine_tail`](DLMF/AlgebraicAnalytic/Summability/Integrals.lean#L241) (admitted).
- [1.15.E44](https://dlmf.nist.gov/1.15.E44): [`DLMF.AlgebraicAnalytic.fourierCesaroMeanIntegral`](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L190) (definition).
- [1.15.E45](https://dlmf.nist.gov/1.15.E45): [`DLMF.AlgebraicAnalytic.fourierCesaroMeanIntegral_eq`](DLMF/AlgebraicAnalytic/Summability/Integrals.lean#L247) (admitted).
- [1.15.E46](https://dlmf.nist.gov/1.15.E46): [`DLMF.AlgebraicAnalytic.tendsto_integral_norm_fourierCesaroMeanIntegral_sub`](DLMF/AlgebraicAnalytic/Summability/Integrals.lean#L255) (admitted).
- [1.15.vi](https://dlmf.nist.gov/1.15.vi): [`DLMF.AlgebraicAnalytic.riemannLiouvilleIntegralFrom`](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L206) (definition); [`DLMF.AlgebraicAnalytic.riemannLiouvilleIntegralUpper`](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L212) (definition); [`DLMF.AlgebraicAnalytic.weylFractionalIntegral`](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L218) (definition); [`DLMF.AlgebraicAnalytic.fractionalIntegral_eq_riemannLiouvilleIntegralFrom`](DLMF/AlgebraicAnalytic/Summability/Fractional.lean#L40) (proved). Variants of 1.15.47 with lower limit `a`, with limits `x`, `a` and kernel `(t−x)^{α−1}`, and with `a = ∞` (vi.p3); `fractionalIntegral` is the case `a = 0` (proved). The references to 18.17.9, 18.17.11 and 18.17.13 are examples in Chapter 18.
- [1.15.E47](https://dlmf.nist.gov/1.15.E47): [`DLMF.AlgebraicAnalytic.fractionalIntegral`](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L199) (definition).
- [1.15.E48](https://dlmf.nist.gov/1.15.E48): [`DLMF.AlgebraicAnalytic.fractionalIntegral_fractionalIntegral`](DLMF/AlgebraicAnalytic/Summability/Fractional.lean#L45) (admitted).
- [1.15.E49](https://dlmf.nist.gov/1.15.E49): [`DLMF.AlgebraicAnalytic.hasSum_fractionalIntegral_of_hasSum`](DLMF/AlgebraicAnalytic/Summability/Fractional.lean#L99) (admitted).
- [1.15.E50](https://dlmf.nist.gov/1.15.E50): [`DLMF.AlgebraicAnalytic.fractionalIntegral_cpow`](DLMF/AlgebraicAnalytic/Summability/Fractional.lean#L53) (proved); [`DLMF.AlgebraicAnalytic.hasSum_fractionalIntegral_of_hasSum`](DLMF/AlgebraicAnalytic/Summability/Fractional.lean#L99) (admitted). The power rule `I^α t^μ = Γ(μ+1)/Γ(μ+α+1) x^{μ+α}` (complex `μ`, `ℜμ > −1`) proved from Mathlib's Beta integral; stronger than DLMF termwise.
- [1.15.vii](https://dlmf.nist.gov/1.15.vii): [`DLMF.AlgebraicAnalytic.fractionalDerivative_half_deriv_ne`](DLMF/AlgebraicAnalytic/Summability/Fractional.lean#L138) (admitted). `D^{1/2}D ≠ D^{3/2}` (for `f = 1` at `x = 1`) admitted. All formulas of §1.15(vii) for `x ≥ 0` (DLMF erratum 1.0.1); Lean uses `x > 0`.
- [1.15.E51](https://dlmf.nist.gov/1.15.E51): [`DLMF.AlgebraicAnalytic.fractionalDerivative`](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L229) (definition); [`DLMF.AlgebraicAnalytic.fractionalDerivative_eq_iteratedDeriv`](DLMF/AlgebraicAnalytic/Summability/Fractional.lean#L109) (admitted). `fractionalDerivative` uses `n = ⌊ℜα⌋ + 1`; independence of `n` admitted.
- [1.15.E52](https://dlmf.nist.gov/1.15.E52): [`DLMF.AlgebraicAnalytic.iteratedDeriv_fractionalIntegral`](DLMF/AlgebraicAnalytic/Summability/Fractional.lean#L118) (admitted).
- [1.15.E53](https://dlmf.nist.gov/1.15.E53): [`DLMF.AlgebraicAnalytic.fractionalDerivative_fractionalDerivative_cpow`](DLMF/AlgebraicAnalytic/Summability/Fractional.lean#L127) (admitted). **Missing hypothesis:** false for general `f`: for `f = x^{β−1}`, `D^β f = 0` while `D^{α+β} f = (Γ(β)/Γ(−α)) x^{−α−1} ≠ 0` (e.g. `α = 1/2`, `β = 1/3`). Acquired for powers `x^μ` with `ℜμ > −1`, `ℜ(μ−β) > −1`.
- [1.15.viii](https://dlmf.nist.gov/1.15.viii): Tauberian theorems 1.15.54–1.15.57 (Littlewood, Hardy–Littlewood); the section paragraph cites Widder (1941).
- [1.15.E54](https://dlmf.nist.gov/1.15.E54): [`DLMF.AlgebraicAnalytic.tendsto_of_hasAbelSum_of_lower_bound`](DLMF/AlgebraicAnalytic/Summability/Series.lean#L85) (admitted).
- [1.15.E55](https://dlmf.nist.gov/1.15.E55): [`DLMF.AlgebraicAnalytic.tendsto_of_hasAbelSum_of_lower_bound`](DLMF/AlgebraicAnalytic/Summability/Series.lean#L85) (admitted).
- [1.15.E56](https://dlmf.nist.gov/1.15.E56): [`DLMF.AlgebraicAnalytic.tendsto_cesaro_of_abel_mean`](DLMF/AlgebraicAnalytic/Summability/Series.lean#L93) (admitted).
- [1.15.E57](https://dlmf.nist.gov/1.15.E57): [`DLMF.AlgebraicAnalytic.tendsto_cesaro_of_abel_mean`](DLMF/AlgebraicAnalytic/Summability/Series.lean#L93) (admitted).

### Prose, informal and excluded items (part g1e)

- 1.14 notation table (info.t1): no statement (notation).
- 1.14.Px4 (Poisson summation): the paragraph only refers to §1.8(iv) and 1.8.14: no statement
  (references only).
- 1.14.vii (section paragraph citing Wong 1989) and 1.14.viii (compendia of tables): no
  statement (references only).
- Citations to Love (1972b), Widder (1941), Andrews et al. (1999) and the "see also" remarks of
  §1.15: no statement (references only).
- The Hankel transform is not part of §1.14 (DLMF §10.22(v)); not acquired here.
- No item of §§1.14–1.15 is excluded as numerical or informal.

### Validation (part g1e)

- All twelve modules build (`lake build` of each module, 2026-10-27) and pass
  `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false` with no warnings other than
  the 129 `declaration uses 'sorry'` warnings, one per admitted theorem. Definitions and helper
  lemmas contain no `sorry`; no axioms, `native_decide` or `opaque` declarations are added.
- `#print axioms` for a sample of proved theorems (`fourierTransform_inversion`,
  `eq_of_fourierTransform_eq`, `fourierTransform_gaussian`, `laplaceTransform_heaviside_shift`,
  `tendsto_mellin_vertical`, `hasAbelSum_of_tendsto`, `tendstoUniformlyOn_fejerKernel`,
  `integral_halfPlanePoissonKernel`, `re_poissonCauchyIntegral`, `im_poissonCauchyIntegral`,
  `fractionalIntegral_cpow`) reports only `propext`, `Classical.choice` and `Quot.sound`.
- Every row of Tables 1.14.1–1.14.5 and the corrected statements were checked numerically with
  mpmath before acquisition; the counterexamples are recorded above.
- Lines are at most 100 characters; `git diff --check` is clean.

## Part g1f: §§1.16–1.18

This part covers the definitions, numbered formulas and analytical prose of
[DLMF §1.16](https://dlmf.nist.gov/1.16) (distributions),
[§1.17](https://dlmf.nist.gov/1.17) (integral and series representations of the Dirac delta)
and [§1.18](https://dlmf.nist.gov/1.18) (linear second-order differential operators and
eigenfunction expansions), DLMF version 1.2.8, checked on 2026-10-27, by agent g1f (helper
prefix `g1f_`). The Lean code is in `DLMF/AlgebraicAnalytic/Distributions/` and
`DLMF/AlgebraicAnalytic/Spectral/` (namespace `DLMF.AlgebraicAnalytic`). Modules in import
order:

- [Distributions/Defs](DLMF/AlgebraicAnalytic/Distributions/Defs.lean) (imports Mathlib only)
- [Distributions/MathlibCoverage](DLMF/AlgebraicAnalytic/Distributions/MathlibCoverage.lean)
  (`dlmf_upstream` pointers; imports `DLMF.Core.Upstream` and Mathlib)
- [Distributions/Theory](DLMF/AlgebraicAnalytic/Distributions/Theory.lean) (§1.16; imports
  `Defs`)
- [Distributions/DiracDelta](DLMF/AlgebraicAnalytic/Distributions/DiracDelta.lean) (§1.17;
  imports `Defs` and the special-function modules `DLMF.Bessel.Basic`, `DLMF.Airy.Basic`,
  `DLMF.Coulomb.Energy.Defs`, `DLMF.OrthogonalPolynomials.Classical`,
  `DLMF.Legendre.Harmonics`, `DLMF.Core.Framework`)
- [Spectral/Defs](DLMF/AlgebraicAnalytic/Spectral/Defs.lean) (imports Mathlib only)
- [Spectral/MathlibCoverage](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean)
- [Spectral/Theory](DLMF/AlgebraicAnalytic/Spectral/Theory.lean) (§1.18; imports `Spectral/Defs`
  and `DLMF.Bessel.Basic`)

### Domains, conventions and source corrections (part g1f)

- Distributions are Mathlib's `Distribution` (continuous linear functionals on real test
  functions `TestFunction`), with values in ℂ; δ is Mathlib's `Distribution.delta`. Tempered
  distributions and Schwartz functions are Mathlib's `TemperedDistribution` and `SchwartzMap`.
- The DLMF Fourier transform (1.16.29) `(2π)^{-n/2} ∫ e^{i x·t} φ(t) dt` differs from Mathlib's
  `𝓕` (kernel `e^{-2πi⟪x,ξ⟫}`); `dlmfFourierSchwartz` defines it as `(2π)^{-n/2} 𝓕⁻ φ(x/2π)`,
  and `dlmfFourierTempered` (1.16.35) is its transpose.
- The δ-representations of §1.17 are stated as weak limits against test functions
  (`IsDeltaSequence`, 1.17.3–1.17.4), never as pointwise identities.
- 1.16.17–1.16.18: the piecewise-smooth hypothesis is formalized through smooth one-sided
  extensions `g`, `h` (slightly stronger than one-sided smoothness).
- 1.17.19–1.17.21: DLMF says continuity and 2π-periodicity of φ suffice; that is false (du
  Bois-Reymond: the Fourier series of a continuous function can diverge at a point). Stated
  for `C¹` periodic φ.
- 1.18.54 (Sokhotski–Plemelj): DLMF's `f ∈ C(X)` is insufficient; stated for `C¹` compactly
  supported `f` on ℝ.
- 1.18.38 (Case 3): DLMF does not print the eigenvalue; it is `(2n)²`, as proved in
  `expEigenfunction_spec`.
- 1.18.42: `hermiteFunction` is built from Mathlib's probabilists' `Polynomial.hermite`
  through `H_n(x) = 2^{n/2} He_n(√2 x)`, so that `Spectral/Defs` imports no theorem file.
- The DLMF inner product is linear in its first argument; DLMF `⟨u, v⟩` is Mathlib `⟪v, u⟫`.
- Continuous and mixed spectra (1.18.44–1.18.66) are formalized by `IsEigenfunctionTransform`:
  a unitary `U : L²(X) ≃ₗᵢ L²(ν)`, ν Lebesgue measure on σ_c plus unit point masses on the
  (simple) eigenvalues σ_p, with `U f (λ) = ∫ f φ(·, λ)` on compactly supported `f`.
- `schrodingerMaxDomainC2` is the `C²` part of the maximal domain `D(𝓛*)`; the Weyl
  limit-point/limit-circle statements of §1.18(ix) are stated on it.
- 1.16.48–1.16.51 (Fourier transforms of sign and `H`) were rechecked analytically and agree.
  The normalization of 1.17.15 (Coulomb functions) was not checked numerically.

### Numbered formulas and prose items (part g1f)

## [§1.16 Distributions](https://dlmf.nist.gov/1.16)

- [1.16.E1](https://dlmf.nist.gov/1.16.E1): upstream `Distribution` (exact: distributions are continuous linear maps 𝓓(Ω, ℝ) →L[ℝ] F; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Distributions/MathlibCoverage.lean#L29))
- [1.16.E2](https://dlmf.nist.gov/1.16.E2): upstream `Distribution` (exact: continuity on 𝓓(Ω, ℝ); the topology is the inductive limit topology; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Distributions/MathlibCoverage.lean#L31))
- [1.16.E3](https://dlmf.nist.gov/1.16.E3): upstream `Distribution.ofFun_apply` (exact: ⟨Λ_f, φ⟩ = ∫ φ x • f x for locally integrable f; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Distributions/MathlibCoverage.lean#L33))
- [1.16.E3_5](https://dlmf.nist.gov/1.16.E3_5): [`DLMF.AlgebraicAnalytic.stieltjesDistribution`](DLMF/AlgebraicAnalytic/Distributions/Defs.lean#L73) (definition)
- [1.16.E4](https://dlmf.nist.gov/1.16.E4): upstream `ContinuousLinearMap.add_apply` (exact: (Λ₁ + Λ₂) φ = Λ₁ φ + Λ₂ φ; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Distributions/MathlibCoverage.lean#L35))
- [1.16.E5](https://dlmf.nist.gov/1.16.E5): upstream `ContinuousLinearMap.map_smul` (exact: Λ (c φ) = c Λ φ (real c on real test functions); (c Λ) φ = c (Λ φ) by definition; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Distributions/MathlibCoverage.lean#L37))
- [1.16.E6](https://dlmf.nist.gov/1.16.E6): [`DLMF.AlgebraicAnalytic.smoothMul`](DLMF/AlgebraicAnalytic/Distributions/Defs.lean#L90) (definition); [`DLMF.AlgebraicAnalytic.smoothMul_apply`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L183) (proved)
- [1.16.E7](https://dlmf.nist.gov/1.16.E7): [`DLMF.AlgebraicAnalytic.distrib_tendsto_iff`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L190) (admitted)
- [1.16.E8](https://dlmf.nist.gov/1.16.E8): upstream `Distribution.lineDerivOp_apply_apply` (exact: ⟨∂_v Λ, φ⟩ = ⟨Λ, -∂_v φ⟩; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Distributions/MathlibCoverage.lean#L41))
- [1.16.E9](https://dlmf.nist.gov/1.16.E9): [`DLMF.AlgebraicAnalytic.distribIterDeriv`](DLMF/AlgebraicAnalytic/Distributions/Defs.lean#L82) (definition); [`DLMF.AlgebraicAnalytic.distribIterDeriv_apply`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L61) (proved)
- [1.16.E9_5](https://dlmf.nist.gov/1.16.E9_5): [`DLMF.AlgebraicAnalytic.stieltjes_eq_deriv`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L201) (admitted)
- [1.16.E10](https://dlmf.nist.gov/1.16.E10): upstream `Distribution.delta_apply` (exact: ⟨δ_x, φ⟩ = φ(x) (real valued); pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Distributions/MathlibCoverage.lean#L43))
- [1.16.E11](https://dlmf.nist.gov/1.16.E11): upstream `Distribution.delta_apply` (exact: ⟨δ_{x₀}, φ⟩ = φ(x₀); pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Distributions/MathlibCoverage.lean#L45))
- [1.16.E12](https://dlmf.nist.gov/1.16.E12): [`DLMF.AlgebraicAnalytic.distribIterDeriv_delta_apply`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L78) (proved)
- [1.16.E13](https://dlmf.nist.gov/1.16.E13): [`DLMF.AlgebraicAnalytic.heaviside`](DLMF/AlgebraicAnalytic/Distributions/Defs.lean#L57) (definition)
- [1.16.E14](https://dlmf.nist.gov/1.16.E14): [`DLMF.AlgebraicAnalytic.heaviside`](DLMF/AlgebraicAnalytic/Distributions/Defs.lean#L57) (definition)
- [1.16.E15](https://dlmf.nist.gov/1.16.E15): [`DLMF.AlgebraicAnalytic.deriv_heaviside`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L129) (proved)
- [1.16.E16](https://dlmf.nist.gov/1.16.E16): [`DLMF.AlgebraicAnalytic.deriv_heaviside_shift`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L118) (proved)
- [1.16.E17](https://dlmf.nist.gov/1.16.E17): [`DLMF.AlgebraicAnalytic.iterDeriv_piecewise`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L227) (admitted)
- [1.16.E18](https://dlmf.nist.gov/1.16.E18): [`DLMF.AlgebraicAnalytic.iterDeriv_piecewise`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L227) (admitted)
- [1.16.E19](https://dlmf.nist.gov/1.16.E19): [`DLMF.AlgebraicAnalytic.xPlusRpow`](DLMF/AlgebraicAnalytic/Distributions/Defs.lean#L62) (definition); [`DLMF.AlgebraicAnalytic.xPlusDistrib`](DLMF/AlgebraicAnalytic/Distributions/Defs.lean#L104) (definition)
- [1.16.E20](https://dlmf.nist.gov/1.16.E20): [`DLMF.AlgebraicAnalytic.deriv_xPlusRpow`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L243) (admitted)
- [1.16.E21](https://dlmf.nist.gov/1.16.E21): [`DLMF.AlgebraicAnalytic.xPlusDistrib`](DLMF/AlgebraicAnalytic/Distributions/Defs.lean#L104) (definition); [`DLMF.AlgebraicAnalytic.xPlusDistrib_eq_iterDeriv`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L249) (admitted)
- [1.16.E22](https://dlmf.nist.gov/1.16.E22): [`DLMF.AlgebraicAnalytic.logPlus`](DLMF/AlgebraicAnalytic/Distributions/Defs.lean#L67) (definition)
- [1.16.E23](https://dlmf.nist.gov/1.16.E23): [`DLMF.AlgebraicAnalytic.xPlusDistrib`](DLMF/AlgebraicAnalytic/Distributions/Defs.lean#L104) (definition); [`DLMF.AlgebraicAnalytic.factorial_smul_xPlusDistrib`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L258) (proved)
- [1.16.E24](https://dlmf.nist.gov/1.16.E24): upstream `schwartz_withSeminorms` (stronger: the topology of 𝓢 is given by the seminorms sup |x|^k |φ^{(n)}(x)|; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Distributions/MathlibCoverage.lean#L51))
- [1.16.E25](https://dlmf.nist.gov/1.16.E25): upstream `PointwiseConvergenceCLM.tendsto_iff_forall_tendsto` (exact: convergence in 𝓢' is pointwise convergence on 𝓢; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Distributions/MathlibCoverage.lean#L55))
- [1.16.E26](https://dlmf.nist.gov/1.16.E26): upstream `Distribution.ofFun_apply` (exact: ⟨Λ_f, φ⟩ = ∫_{ℝⁿ} φ x • f x; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Distributions/MathlibCoverage.lean#L61))
- [1.16.E27](https://dlmf.nist.gov/1.16.E27): [`DLMF.AlgebraicAnalytic.iteratedLineDerivOp_ofFun_apply`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L279) (admitted)
- [1.16.E28](https://dlmf.nist.gov/1.16.E28): upstream `SchwartzMap.decay` (exact: |x|^k ‖D^n φ(x)‖ ≤ C, the defining bounds of 𝓣ₙ; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Distributions/MathlibCoverage.lean#L63))
- [1.16.E29](https://dlmf.nist.gov/1.16.E29): [`DLMF.AlgebraicAnalytic.dlmfFourierSchwartz`](DLMF/AlgebraicAnalytic/Distributions/Defs.lean#L137) (definition); [`DLMF.AlgebraicAnalytic.dlmfFourierSchwartz_apply`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L299) (proved); upstream `SchwartzMap.fourier_coe` (different convention: Mathlib's 𝓕 on 𝓢 uses e^{-2πi⟪x, ξ⟫}; DLMF's is dlmfFourierSchwartz; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Distributions/MathlibCoverage.lean#L67))
- [1.16.E30](https://dlmf.nist.gov/1.16.E30): [`DLMF.AlgebraicAnalytic.dlmfD`](DLMF/AlgebraicAnalytic/Distributions/Defs.lean#L183) (definition)
- [1.16.E31](https://dlmf.nist.gov/1.16.E31): [`DLMF.AlgebraicAnalytic.polyEval`](DLMF/AlgebraicAnalytic/Distributions/Defs.lean#L196) (definition)
- [1.16.E32](https://dlmf.nist.gov/1.16.E32): [`DLMF.AlgebraicAnalytic.polyDiffOp`](DLMF/AlgebraicAnalytic/Distributions/Defs.lean#L190) (definition)
- [1.16.E33](https://dlmf.nist.gov/1.16.E33): [`DLMF.AlgebraicAnalytic.dlmfFourierSchwartz_polyDiffOp`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L322) (admitted)
- [1.16.E34](https://dlmf.nist.gov/1.16.E34): [`DLMF.AlgebraicAnalytic.dlmfFourierSchwartz_polyMul`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L329) (admitted)
- [1.16.E35](https://dlmf.nist.gov/1.16.E35): [`DLMF.AlgebraicAnalytic.dlmfFourierTempered`](DLMF/AlgebraicAnalytic/Distributions/Defs.lean#L149) (definition); upstream `TemperedDistribution.fourier_apply` (different convention: ⟨𝓕 u, φ⟩ = ⟨u, 𝓕 φ⟩ with Mathlib's 𝓕; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Distributions/MathlibCoverage.lean#L69))
- [1.16.E36](https://dlmf.nist.gov/1.16.E36): [`DLMF.AlgebraicAnalytic.dlmfFourierTempered_polyDiffOp`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L336) (admitted); upstream `TemperedDistribution.fourier_lineDerivOp_eq` (different convention: Fourier transform of a directional derivative, Mathlib's 𝓕; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Distributions/MathlibCoverage.lean#L71))
- [1.16.E37](https://dlmf.nist.gov/1.16.E37): [`DLMF.AlgebraicAnalytic.dlmfFourierTempered_polyMul`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L347) (admitted)
- [1.16.E38](https://dlmf.nist.gov/1.16.E38): [`DLMF.AlgebraicAnalytic.dlmfFourierTempered_delta`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L357) (proved)
- [1.16.E39](https://dlmf.nist.gov/1.16.E39): [`DLMF.AlgebraicAnalytic.dlmfFourierTempered_delta`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L357) (proved); upstream `TemperedDistribution.fourier_delta_zero` (different convention: 𝓕 δ = 1 in Mathlib's normalization (DLMF: 1/√(2π)); pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Distributions/MathlibCoverage.lean#L73))
- [1.16.E40](https://dlmf.nist.gov/1.16.E40): [`DLMF.AlgebraicAnalytic.dlmfFourierTempered_delta`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L357) (proved)
- [1.16.E41](https://dlmf.nist.gov/1.16.E41): [`DLMF.AlgebraicAnalytic.dlmfFourierTempered_one`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L368) (admitted)
- [1.16.E42](https://dlmf.nist.gov/1.16.E42): [`DLMF.AlgebraicAnalytic.dlmfFourierTempered_one`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L368) (admitted)
- [1.16.E43](https://dlmf.nist.gov/1.16.E43): [`DLMF.AlgebraicAnalytic.dlmfFourierTempered_one`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L368) (admitted)
- [1.16.E44](https://dlmf.nist.gov/1.16.E44): [`DLMF.AlgebraicAnalytic.sign_eq_two_mul_heaviside_sub_one`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L137) (proved)
- [1.16.E45](https://dlmf.nist.gov/1.16.E45): [`DLMF.AlgebraicAnalytic.deriv_sign`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L160) (proved); [`DLMF.AlgebraicAnalytic.deriv_signTempered`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L376) (admitted)
- [1.16.E46](https://dlmf.nist.gov/1.16.E46): [`DLMF.AlgebraicAnalytic.dlmfFourierTempered_deriv_sign`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L382) (proved from admissions)
- [1.16.E47](https://dlmf.nist.gov/1.16.E47): [`DLMF.AlgebraicAnalytic.dlmfFourierTempered_deriv_sign'`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L409) (proved from admissions)
- [1.16.E48](https://dlmf.nist.gov/1.16.E48): [`DLMF.AlgebraicAnalytic.dlmfFourierTempered_sign`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L417) (admitted)
- [1.16.E49](https://dlmf.nist.gov/1.16.E49): [`DLMF.AlgebraicAnalytic.dlmfFourierTempered_sign`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L417) (admitted)
- [1.16.E50](https://dlmf.nist.gov/1.16.E50): [`DLMF.AlgebraicAnalytic.dlmfFourierTempered_heaviside`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L426) (admitted)
- [1.16.E51](https://dlmf.nist.gov/1.16.E51): [`DLMF.AlgebraicAnalytic.dlmfFourierTempered_heaviside`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L426) (admitted)
- [1.16.i](https://dlmf.nist.gov/1.16.i) (prose): upstream `TestFunction` (exact: 𝓓(Ω, F), smooth compactly supported functions with the inductive-limit topology; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Distributions/MathlibCoverage.lean#L27))
- [1.16.ii](https://dlmf.nist.gov/1.16.ii) (prose): [`DLMF.AlgebraicAnalytic.deriv_stieltjes_of_density`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L209) (admitted)
- [1.16.iii](https://dlmf.nist.gov/1.16.iii) (prose): [`DLMF.AlgebraicAnalytic.delta_not_regular`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L218) (admitted)
- [1.16.v](https://dlmf.nist.gov/1.16.v) (prose): upstream `SchwartzMap` (exact: the Schwartz space 𝓣 = 𝓢(E, F) of rapidly decreasing smooth functions; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Distributions/MathlibCoverage.lean#L49)); upstream `TemperedDistribution` (exact: 𝓢'(E, F) = 𝓢(E, ℂ) →Lₚₜ[ℂ] F; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Distributions/MathlibCoverage.lean#L53)); upstream `TemperedDistribution.derivCLM_apply_apply` (exact: the derivative of a tempered distribution, ⟨u', φ⟩ = ⟨u, -φ'⟩; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Distributions/MathlibCoverage.lean#L57))
- [1.16.vi](https://dlmf.nist.gov/1.16.vi) (prose): upstream `Distribution` (exact: distributions on an open set of any finite-dimensional real normed space; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Distributions/MathlibCoverage.lean#L59))
- [1.16.vii](https://dlmf.nist.gov/1.16.vii) (prose): [`DLMF.AlgebraicAnalytic.dlmfFourierSchwartz`](DLMF/AlgebraicAnalytic/Distributions/Defs.lean#L137) (definition)
- [1.16.ii](https://dlmf.nist.gov/1.16.ii): [`DLMF.AlgebraicAnalytic.deriv_stieltjes_of_density`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L209) (admitted).
- [1.16.iii](https://dlmf.nist.gov/1.16.iii): [`DLMF.AlgebraicAnalytic.delta_not_regular`](DLMF/AlgebraicAnalytic/Distributions/Theory.lean#L218) (admitted).
- [1.16.vii](https://dlmf.nist.gov/1.16.vii): [`DLMF.AlgebraicAnalytic.dlmfFourierSchwartz`](DLMF/AlgebraicAnalytic/Distributions/Defs.lean#L137) (definition).

## [§1.17 Integral and Series Representations of the Dirac Delta](https://dlmf.nist.gov/1.17)

- [1.17.E1](https://dlmf.nist.gov/1.17.E1): [`DLMF.AlgebraicAnalytic.delta_apply_eq_zero_of_notMem_tsupport`](DLMF/AlgebraicAnalytic/Distributions/DiracDelta.lean#L49) (proved)
- [1.17.E2](https://dlmf.nist.gov/1.17.E2): upstream `Distribution.delta_apply` (exact: ⟨δ_a, φ⟩ = φ(a), the meaning of ∫ δ(x - a) φ(x) dx = φ(a); pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Distributions/MathlibCoverage.lean#L77)); upstream `TemperedDistribution.delta_apply` (exact: the tempered delta, δ_a φ = φ(a); pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Distributions/MathlibCoverage.lean#L79))
- [1.17.E3](https://dlmf.nist.gov/1.17.E3): [`DLMF.AlgebraicAnalytic.IsDeltaSequence`](DLMF/AlgebraicAnalytic/Distributions/Defs.lean#L232) (definition); [`DLMF.AlgebraicAnalytic.isDeltaSequence_gaussian`](DLMF/AlgebraicAnalytic/Distributions/DiracDelta.lean#L108) (proved)
- [1.17.E4](https://dlmf.nist.gov/1.17.E4): [`DLMF.AlgebraicAnalytic.IsDeltaSequence`](DLMF/AlgebraicAnalytic/Distributions/Defs.lean#L232) (definition)
- [1.17.E5](https://dlmf.nist.gov/1.17.E5): [`DLMF.AlgebraicAnalytic.gaussianDeltaSeq`](DLMF/AlgebraicAnalytic/Distributions/Defs.lean#L241) (definition); [`DLMF.AlgebraicAnalytic.tendsto_gaussian_integral`](DLMF/AlgebraicAnalytic/Distributions/DiracDelta.lean#L87) (proved); [`DLMF.AlgebraicAnalytic.isDeltaSequence_gaussian`](DLMF/AlgebraicAnalytic/Distributions/DiracDelta.lean#L108) (proved)
- [1.17.E6](https://dlmf.nist.gov/1.17.E6): [`DLMF.AlgebraicAnalytic.tendsto_gaussian_integral`](DLMF/AlgebraicAnalytic/Distributions/DiracDelta.lean#L87) (proved); [`DLMF.AlgebraicAnalytic.tendsto_gaussian_integral_of_growth`](DLMF/AlgebraicAnalytic/Distributions/DiracDelta.lean#L114) (admitted)
- [1.17.E7](https://dlmf.nist.gov/1.17.E7): [`DLMF.AlgebraicAnalytic.tendsto_gaussian_integral_jump`](DLMF/AlgebraicAnalytic/Distributions/DiracDelta.lean#L124) (admitted)
- [1.17.E8](https://dlmf.nist.gov/1.17.E8): [`DLMF.AlgebraicAnalytic.fourier_inversion_dlmf`](DLMF/AlgebraicAnalytic/Distributions/DiracDelta.lean#L138) (admitted); upstream `Continuous.fourierInv_fourier_eq` (different convention: Fourier inversion 𝓕⁻(𝓕 f) = f in Mathlib's normalization; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Distributions/MathlibCoverage.lean#L81))
- [1.17.E9](https://dlmf.nist.gov/1.17.E9): [`DLMF.AlgebraicAnalytic.tendsto_fourier_kernel`](DLMF/AlgebraicAnalytic/Distributions/DiracDelta.lean#L206) (admitted)
- [1.17.E10](https://dlmf.nist.gov/1.17.E10): [`DLMF.AlgebraicAnalytic.gaussian_fourier_eq`](DLMF/AlgebraicAnalytic/Distributions/DiracDelta.lean#L148) (proved)
- [1.17.E11](https://dlmf.nist.gov/1.17.E11): [`DLMF.AlgebraicAnalytic.isDeltaSequence_gaussian_fourier`](DLMF/AlgebraicAnalytic/Distributions/DiracDelta.lean#L188) (proved)
- [1.17.E12](https://dlmf.nist.gov/1.17.E12): [`DLMF.AlgebraicAnalytic.tendsto_fourier_kernel`](DLMF/AlgebraicAnalytic/Distributions/DiracDelta.lean#L206) (admitted)
- [1.17.E12_1](https://dlmf.nist.gov/1.17.E12_1): [`DLMF.AlgebraicAnalytic.tendsto_cos_kernel`](DLMF/AlgebraicAnalytic/Distributions/DiracDelta.lean#L214) (admitted)
- [1.17.E12_2](https://dlmf.nist.gov/1.17.E12_2): [`DLMF.AlgebraicAnalytic.tendsto_sin_kernel`](DLMF/AlgebraicAnalytic/Distributions/DiracDelta.lean#L222) (admitted)
- [1.17.E13](https://dlmf.nist.gov/1.17.E13): [`DLMF.AlgebraicAnalytic.tendsto_bessel_kernel`](DLMF/AlgebraicAnalytic/Distributions/DiracDelta.lean#L230) (admitted)
- [1.17.E14](https://dlmf.nist.gov/1.17.E14): [`DLMF.AlgebraicAnalytic.tendsto_sphericalBessel_kernel`](DLMF/AlgebraicAnalytic/Distributions/DiracDelta.lean#L240) (admitted)
- [1.17.E15](https://dlmf.nist.gov/1.17.E15): [`DLMF.AlgebraicAnalytic.tendsto_coulomb_kernel`](DLMF/AlgebraicAnalytic/Distributions/DiracDelta.lean#L250) (admitted)
- [1.17.E16](https://dlmf.nist.gov/1.17.E16): [`DLMF.AlgebraicAnalytic.tendsto_airy_kernel`](DLMF/AlgebraicAnalytic/Distributions/DiracDelta.lean#L261) (admitted)
- [1.17.E17](https://dlmf.nist.gov/1.17.E17): [`DLMF.AlgebraicAnalytic.tendsto_fourier_series`](DLMF/AlgebraicAnalytic/Distributions/DiracDelta.lean#L271) (admitted); upstream `hasSum_fourier_series_of_summable` (partial: a function on the circle with summable Fourier coefficients is the sum of its series; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Distributions/MathlibCoverage.lean#L83))
- [1.17.E18](https://dlmf.nist.gov/1.17.E18): [`DLMF.AlgebraicAnalytic.tendsto_dirichletKernel_integral`](DLMF/AlgebraicAnalytic/Distributions/DiracDelta.lean#L290) (admitted)
- [1.17.E19](https://dlmf.nist.gov/1.17.E19): [`DLMF.AlgebraicAnalytic.tendsto_dirichletKernel_integral`](DLMF/AlgebraicAnalytic/Distributions/DiracDelta.lean#L290) (admitted)
- [1.17.E20](https://dlmf.nist.gov/1.17.E20): [`DLMF.AlgebraicAnalytic.dirichletKernel`](DLMF/AlgebraicAnalytic/Distributions/Defs.lean#L253) (definition); [`DLMF.AlgebraicAnalytic.dirichletKernel_eq`](DLMF/AlgebraicAnalytic/Distributions/DiracDelta.lean#L282) (admitted)
- [1.17.E21](https://dlmf.nist.gov/1.17.E21): [`DLMF.AlgebraicAnalytic.tendsto_dirichletKernel_integral`](DLMF/AlgebraicAnalytic/Distributions/DiracDelta.lean#L290) (admitted)
- [1.17.E22](https://dlmf.nist.gov/1.17.E22): [`DLMF.AlgebraicAnalytic.tendsto_legendre_kernel`](DLMF/AlgebraicAnalytic/Distributions/DiracDelta.lean#L306) (admitted)
- [1.17.E23](https://dlmf.nist.gov/1.17.E23): [`DLMF.AlgebraicAnalytic.tendsto_laguerre_kernel`](DLMF/AlgebraicAnalytic/Distributions/DiracDelta.lean#L316) (admitted)
- [1.17.E24](https://dlmf.nist.gov/1.17.E24): [`DLMF.AlgebraicAnalytic.tendsto_hermite_kernel`](DLMF/AlgebraicAnalytic/Distributions/DiracDelta.lean#L326) (admitted)
- [1.17.E25](https://dlmf.nist.gov/1.17.E25): [`DLMF.AlgebraicAnalytic.tendsto_sphericalHarmonic_kernel`](DLMF/AlgebraicAnalytic/Distributions/DiracDelta.lean#L337) (admitted)

## [§1.18 Linear Second Order Differential Operators and Eigenfunction Expansions](https://dlmf.nist.gov/1.18)

- [1.18.E1](https://dlmf.nist.gov/1.18.E1): upstream `norm_eq_sqrt_re_inner` (exact: ‖v‖ = √⟨v, v⟩; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L28))
- [1.18.E2](https://dlmf.nist.gov/1.18.E2): upstream `Orthonormal.tsum_inner_products_le` (exact: Bessel's inequality Σ |⟨v, vₙ⟩|² ≤ ‖v‖²; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L30))
- [1.18.E3](https://dlmf.nist.gov/1.18.E3): upstream `HilbertBasis.repr_apply_apply` (exact: the coefficients b.repr v n = ⟪b n, v⟫ (DLMF's ⟨v, vₙ⟩); pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L32))
- [1.18.E4](https://dlmf.nist.gov/1.18.E4): upstream `HilbertBasis.tsum_inner_mul_inner` (exact: Parseval Σ ⟪v, bₙ⟫⟪bₙ, w⟫ = ⟪v, w⟫, with w = v; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L34))
- [1.18.E5](https://dlmf.nist.gov/1.18.E5): upstream `HilbertBasis.summable_inner_mul_inner` (exact: Σ |cₙ|² < ∞; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L38))
- [1.18.E6](https://dlmf.nist.gov/1.18.E6): upstream `HilbertBasis.hasSum_repr_symm` (exact: for c ∈ ℓ², Σ cₙ bₙ converges to the unique v with coefficients c; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L40))
- [1.18.E7](https://dlmf.nist.gov/1.18.E7): upstream `HilbertBasis.hasSum_repr_symm` (stronger: unconditional convergence in norm; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L42))
- [1.18.E8](https://dlmf.nist.gov/1.18.E8): upstream `lp.norm_rpow_eq_tsum` (exact: ‖v‖² = Σ |cₙ|² in ℓ²; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L44))
- [1.18.E9](https://dlmf.nist.gov/1.18.E9): upstream `lp.inner_eq_tsum` (exact: ⟨v, w⟩ = Σ cₙ conj(dₙ) (Mathlib: Σ ⟪cₙ, dₙ⟫); pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L46))
- [1.18.E10](https://dlmf.nist.gov/1.18.E10): upstream `HilbertBasis.repr` (exact: the isometric isomorphism E ≃ₗᵢ ℓ² given by a Hilbert basis; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L48))
- [1.18.E11](https://dlmf.nist.gov/1.18.E11): upstream `MeasureTheory.MemLp` (exact: MemLp f 2 μ, square integrability for a measure μ (Lebesgue–Stieltjes included); pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L52))
- [1.18.E12](https://dlmf.nist.gov/1.18.E12): upstream `MeasureTheory.L2.inner_def` (exact: ⟨f, g⟩ = ∫ conj(f) g dμ in Mathlib's convention; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L54))
- [1.18.E13](https://dlmf.nist.gov/1.18.E13): [`DLMF.AlgebraicAnalytic.tendsto_integral_sq_sub_partialSum`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L46) (admitted)
- [1.18.E14](https://dlmf.nist.gov/1.18.E14): upstream `HilbertBasis.tsum_inner_mul_inner` (exact: ∫ |f|² = Σ |cₙ|² (Parseval in L²(X)); pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L56))
- [1.18.E15](https://dlmf.nist.gov/1.18.E15): [`DLMF.AlgebraicAnalytic.tendsto_integral_sq_sub_partialSum`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L46) (admitted)
- [1.18.E16](https://dlmf.nist.gov/1.18.E16): [`DLMF.AlgebraicAnalytic.tendsto_integral_sq_sub_partialSum`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L46) (admitted)
- [1.18.E17](https://dlmf.nist.gov/1.18.E17): upstream `HilbertBasis.hasSum_repr` (exact: f = Σ ⟨f, φₙ⟩ φₙ in L²; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L58))
- [1.18.E18](https://dlmf.nist.gov/1.18.E18): upstream `HilbertBasis.tsum_inner_mul_inner` (partial: the kernel K(x, y) = Σ φₙ(x) conj(φₙ(y)) acts weakly as the identity; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L60))
- [1.18.E19](https://dlmf.nist.gov/1.18.E19): upstream `HilbertBasis.tsum_inner_mul_inner` (partial: completeness relation, weakly: Σ ⟨g, φₙ⟩⟨φₙ, f⟩ = ⟨g, f⟩; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L62))
- [1.18.E20](https://dlmf.nist.gov/1.18.E20): upstream `HilbertBasis.orthonormal` (exact: orthonormality of the basis; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L64))
- [1.18.E21](https://dlmf.nist.gov/1.18.E21): upstream `LinearMap` (exact: linear maps; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L68))
- [1.18.E22](https://dlmf.nist.gov/1.18.E22): upstream `ContinuousLinearMap.sSup_sphere_eq_norm` (exact: ‖T‖ = sup_{‖v‖ = 1} ‖Tv‖; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L70))
- [1.18.E23](https://dlmf.nist.gov/1.18.E23): upstream `ContinuousLinearMap.adjoint_inner_right` (exact: ⟨Tv, w⟩ = ⟨v, T* w⟩ for bounded T; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L74))
- [1.18.E24](https://dlmf.nist.gov/1.18.E24): [`DLMF.AlgebraicAnalytic.IsSymmetricOp.eigenvalue_real`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L64) (proved); [`DLMF.AlgebraicAnalytic.IsSymmetricOp.inner_eq_zero`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L74) (proved)
- [1.18.E25](https://dlmf.nist.gov/1.18.E25): [`DLMF.AlgebraicAnalytic.integral_deriv2_mul_eq`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L88) (proved)
- [1.18.E26](https://dlmf.nist.gov/1.18.E26): [`DLMF.AlgebraicAnalytic.integral_deriv2_mul_eq`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L88) (proved)
- [1.18.E27](https://dlmf.nist.gov/1.18.E27): [`DLMF.AlgebraicAnalytic.integral_deriv2_mul_eq_of_dirichlet`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L123) (proved)
- [1.18.E28](https://dlmf.nist.gov/1.18.E28): [`DLMF.AlgebraicAnalytic.schrodingerOp`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L57) (definition)
- [1.18.E29](https://dlmf.nist.gov/1.18.E29): [`DLMF.AlgebraicAnalytic.hasSum_eigen_expansion`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L147) (proved)
- [1.18.E30](https://dlmf.nist.gov/1.18.E30): [`DLMF.AlgebraicAnalytic.hasSum_eigen_expansion`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L147) (proved); upstream `HilbertBasis.tsum_inner_mul_inner` (partial: completeness relation of an eigenbasis, weakly; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L92))
- [1.18.E31](https://dlmf.nist.gov/1.18.E31): [`DLMF.AlgebraicAnalytic.hasSum_eigen_expansion`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L147) (proved); upstream `HilbertBasis.hasSum_repr` (exact: f = Σ f̂(λₙ) φ_{λₙ} in L²; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L94))
- [1.18.E32](https://dlmf.nist.gov/1.18.E32): [`DLMF.AlgebraicAnalytic.eigenCoeff`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L219) (definition)
- [1.18.E33](https://dlmf.nist.gov/1.18.E33): upstream `HilbertBasis.tsum_inner_mul_inner` (exact: Parseval ∫ |f|² = Σ |f̂(λₙ)|²; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L96))
- [1.18.E34](https://dlmf.nist.gov/1.18.E34): [`DLMF.AlgebraicAnalytic.hasSum_eigen_expansion`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L147) (proved)
- [1.18.E35](https://dlmf.nist.gov/1.18.E35): [`DLMF.AlgebraicAnalytic.hasSum_resolvent_expansion`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L165) (proved)
- [1.18.E36](https://dlmf.nist.gov/1.18.E36): [`DLMF.AlgebraicAnalytic.sinEigenfunction`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L77) (definition); [`DLMF.AlgebraicAnalytic.sinEigenfunction_spec`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L213) (proved); [`DLMF.AlgebraicAnalytic.sinEigenfunction_hilbertBasis`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L231) (admitted)
- [1.18.E37](https://dlmf.nist.gov/1.18.E37): [`DLMF.AlgebraicAnalytic.cosEigenfunction`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L81) (definition); [`DLMF.AlgebraicAnalytic.cosEigenfunction_spec`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L239) (proved); [`DLMF.AlgebraicAnalytic.cosEigenfunction_hilbertBasis`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L267) (admitted)
- [1.18.E38](https://dlmf.nist.gov/1.18.E38): [`DLMF.AlgebraicAnalytic.expEigenfunction`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L88) (definition); [`DLMF.AlgebraicAnalytic.expEigenfunction_spec`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L275) (proved); [`DLMF.AlgebraicAnalytic.expEigenfunction_hilbertBasis`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L304) (admitted)
- [1.18.E39](https://dlmf.nist.gov/1.18.E39): [`DLMF.AlgebraicAnalytic.expEigenfunction_hilbertBasis`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L304) (admitted)
- [1.18.E40](https://dlmf.nist.gov/1.18.E40): [`DLMF.AlgebraicAnalytic.expEigenfunction_hilbertBasis`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L304) (admitted); upstream `hasSum_fourier_series_L2` (different setting: Fourier series in L² of the circle ℝ/Tℤ with Haar measure; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L98))
- [1.18.E41](https://dlmf.nist.gov/1.18.E41): [`DLMF.AlgebraicAnalytic.hermiteOp`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L63) (definition); [`DLMF.AlgebraicAnalytic.hermiteFunction_eigen`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L317) (admitted)
- [1.18.E42](https://dlmf.nist.gov/1.18.E42): [`DLMF.AlgebraicAnalytic.hermiteFunction`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L92) (definition); [`DLMF.AlgebraicAnalytic.hermiteFunction_eigen`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L317) (admitted); [`DLMF.AlgebraicAnalytic.hermiteFunction_hilbertBasis`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L324) (admitted)
- [1.18.E43](https://dlmf.nist.gov/1.18.E43): [`DLMF.AlgebraicAnalytic.hermiteFunction_hilbertBasis`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L324) (admitted)
- [1.18.E44](https://dlmf.nist.gov/1.18.E44): [`DLMF.AlgebraicAnalytic.IsEigenfunctionTransform`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L225) (definition)
- [1.18.E45](https://dlmf.nist.gov/1.18.E45): [`DLMF.AlgebraicAnalytic.IsEigenfunctionTransform`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L225) (definition)
- [1.18.E46](https://dlmf.nist.gov/1.18.E46): [`DLMF.AlgebraicAnalytic.IsEigenfunctionTransform.ae_eq_integral`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L349) (admitted)
- [1.18.E47](https://dlmf.nist.gov/1.18.E47): [`DLMF.AlgebraicAnalytic.eigenCoeff`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L219) (definition)
- [1.18.E48](https://dlmf.nist.gov/1.18.E48): [`DLMF.AlgebraicAnalytic.IsEigenfunctionTransform.integral_norm_sq`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L339) (admitted)
- [1.18.E49](https://dlmf.nist.gov/1.18.E49): [`DLMF.AlgebraicAnalytic.IsDiagonalizedBy`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L241) (definition); [`DLMF.AlgebraicAnalytic.IsDiagonalizedBy.inner_apply`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L362) (admitted)
- [1.18.E50](https://dlmf.nist.gov/1.18.E50): [`DLMF.AlgebraicAnalytic.IsDiagonalizedBy`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L241) (definition)
- [1.18.E51](https://dlmf.nist.gov/1.18.E51): [`DLMF.AlgebraicAnalytic.IsDiagonalizedBy.inner_apply`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L362) (admitted)
- [1.18.E52](https://dlmf.nist.gov/1.18.E52): [`DLMF.AlgebraicAnalytic.IsDiagonalizedBy.inner_resolvent`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L373) (admitted)
- [1.18.E53](https://dlmf.nist.gov/1.18.E53): [`DLMF.AlgebraicAnalytic.tendsto_stieltjes_inversion`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L388) (admitted)
- [1.18.E54](https://dlmf.nist.gov/1.18.E54): [`DLMF.AlgebraicAnalytic.tendsto_sokhotski_plemelj`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L400) (admitted)
- [1.18.E55](https://dlmf.nist.gov/1.18.E55): [`DLMF.AlgebraicAnalytic.besselOp`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L67) (definition); [`DLMF.AlgebraicAnalytic.besselOp_sqrt_mul_besselJ`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L416) (admitted)
- [1.18.E56](https://dlmf.nist.gov/1.18.E56): [`DLMF.AlgebraicAnalytic.tendsto_hankel_kernel`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L424) (admitted)
- [1.18.E57](https://dlmf.nist.gov/1.18.E57): [`DLMF.AlgebraicAnalytic.tendsto_hankel_kernel`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L424) (admitted)
- [1.18.E58](https://dlmf.nist.gov/1.18.E58): [`DLMF.AlgebraicAnalytic.tendsto_hankel_kernel`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L424) (admitted)
- [1.18.E59](https://dlmf.nist.gov/1.18.E59): [`DLMF.AlgebraicAnalytic.tendsto_fourier_cos_sin`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L442) (admitted)
- [1.18.E60](https://dlmf.nist.gov/1.18.E60): [`DLMF.AlgebraicAnalytic.IsEigenfunctionTransform`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L225) (definition)
- [1.18.E61](https://dlmf.nist.gov/1.18.E61): [`DLMF.AlgebraicAnalytic.IsEigenfunctionTransform`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L225) (definition)
- [1.18.E62](https://dlmf.nist.gov/1.18.E62): [`DLMF.AlgebraicAnalytic.IsEigenfunctionTransform`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L225) (definition)
- [1.18.E63](https://dlmf.nist.gov/1.18.E63): [`DLMF.AlgebraicAnalytic.IsEigenfunctionTransform`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L225) (definition)
- [1.18.E64](https://dlmf.nist.gov/1.18.E64): [`DLMF.AlgebraicAnalytic.IsEigenfunctionTransform.ae_eq_integral`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L349) (admitted)
- [1.18.E65](https://dlmf.nist.gov/1.18.E65): [`DLMF.AlgebraicAnalytic.IsEigenfunctionTransform.integral_norm_sq`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L339) (admitted)
- [1.18.E66](https://dlmf.nist.gov/1.18.E66): [`DLMF.AlgebraicAnalytic.IsDiagonalizedBy.inner_resolvent`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L373) (admitted)
- [1.18.E67](https://dlmf.nist.gov/1.18.E67): [`DLMF.AlgebraicAnalytic.radialSchrodingerOp`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L71) (definition)
- [1.18.E68](https://dlmf.nist.gov/1.18.E68): upstream `LinearPMap.mem_adjoint_domain_iff` (exact: w ∈ 𝓓(T*) iff v ↦ ⟨Tv, w⟩ is continuous (equivalently bounded on the unit sphere); pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L78))
- [1.18.E69](https://dlmf.nist.gov/1.18.E69): upstream `LinearPMap.adjoint_isFormalAdjoint` (exact: ⟨Tv, w⟩ = ⟨v, T* w⟩, v ∈ 𝓓(T), w ∈ 𝓓(T*), for densely defined T; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L80))
- [1.18.E70](https://dlmf.nist.gov/1.18.E70): [`DLMF.AlgebraicAnalytic.IsSymmetricOp`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L108) (definition); upstream `LinearPMap.IsFormalAdjoint` (exact: T.IsFormalAdjoint T is ⟨Tv, w⟩ = ⟨v, Tw⟩ on 𝓓(T); pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L82))
- [1.18.E71](https://dlmf.nist.gov/1.18.E71): [`DLMF.AlgebraicAnalytic.boundaryValueLeft`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L200) (definition); [`DLMF.AlgebraicAnalytic.limitPoint_iff_wronskian_tendsto_zero`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L574) (admitted)
- [1.18.i](https://dlmf.nist.gov/1.18.i) (prose): upstream `InnerProductSpace` (exact: inner product spaces (Mathlib's inner product is linear in the second argument); pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L26)); upstream `exists_hilbertBasis` (stronger: every Hilbert space has a Hilbert basis (complete orthonormal set); pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L36))
- [1.18.iii](https://dlmf.nist.gov/1.18.iii) (prose): [`DLMF.AlgebraicAnalytic.integral_deriv2_mul_eq_of_dirichlet`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L123) (proved); upstream `ContinuousLinearMap.extend` (exact: a bounded densely defined operator extends uniquely to a bounded operator; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L72)); upstream `LinearPMap` (exact: unbounded operators T : 𝓓(T) → V with linear domain; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L76))
- [1.18.viii](https://dlmf.nist.gov/1.18.viii) (prose): [`DLMF.AlgebraicAnalytic.exists_bound_state_of_integral_nonpos`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L453) (admitted)
- [1.18.ix](https://dlmf.nist.gov/1.18.ix) (prose): [`DLMF.AlgebraicAnalytic.IsEssentiallySelfAdjoint`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L114) (definition); [`DLMF.AlgebraicAnalytic.opResolventSet`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L123) (definition); [`DLMF.AlgebraicAnalytic.opSpectrum`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L130) (definition); [`DLMF.AlgebraicAnalytic.opPointSpectrum`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L134) (definition); [`DLMF.AlgebraicAnalytic.opContinuousSpectrum`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L139) (definition); [`DLMF.AlgebraicAnalytic.opResidualSpectrum`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L146) (definition); [`DLMF.AlgebraicAnalytic.deficiencySubspace`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L151) (definition); [`DLMF.AlgebraicAnalytic.deficiencyIndices`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L156) (definition); [`DLMF.AlgebraicAnalytic.IsLimitCircleLeft`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L184) (definition); [`DLMF.AlgebraicAnalytic.IsLimitCircleRight`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L189) (definition); [`DLMF.AlgebraicAnalytic.opSpectrum_eq_union`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L469) (proved); [`DLMF.AlgebraicAnalytic.IsSelfAdjoint.opSpectrum_real`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L486) (admitted); [`DLMF.AlgebraicAnalytic.IsSelfAdjoint.inner_eigenvectors_eq_zero`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L493) (proved); [`DLMF.AlgebraicAnalytic.IsSymmetricOp.rank_deficiencySubspace`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L501) (admitted); [`DLMF.AlgebraicAnalytic.IsSymmetricOp.exists_selfAdjoint_extension_iff`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L510) (admitted); [`DLMF.AlgebraicAnalytic.IsSymmetricOp.adjoint_domain_eq`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L519) (admitted); [`DLMF.AlgebraicAnalytic.IsSymmetricOp.selfAdjoint_extension_iff`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L528) (admitted); [`DLMF.AlgebraicAnalytic.allSolutionsL2Left_of_exists`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L543) (admitted); [`DLMF.AlgebraicAnalytic.rank_l2SolutionSpace_left`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L553) (admitted); [`DLMF.AlgebraicAnalytic.rank_l2SolutionSpace_add_two`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L563) (admitted); [`DLMF.AlgebraicAnalytic.limitPoint_iff_wronskian_tendsto_zero`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L574) (admitted); upstream `LinearPMap.IsFormalAdjoint.le_adjoint` (exact: a symmetric operator satisfies T ⊂ T*; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L84)); upstream `LinearPMap.isSelfAdjoint_def` (exact: T is self-adjoint iff T* = T; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L86)); upstream `spectrum.isCompact` (exact: the spectrum of a bounded operator is compact; pointer in [MathlibCoverage.lean](DLMF/AlgebraicAnalytic/Spectral/MathlibCoverage.lean#L88))
- [1.18.iii](https://dlmf.nist.gov/1.18.iii): [`DLMF.AlgebraicAnalytic.integral_deriv2_mul_eq_of_dirichlet`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L123) (proved); Mathlib: [`ContinuousLinearMap.extend`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Extend.html#ContinuousLinearMap.extend); Mathlib: [`LinearPMap`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/LinearPMap.html#LinearPMap).
- [1.18.ix](https://dlmf.nist.gov/1.18.ix): [`DLMF.AlgebraicAnalytic.IsEssentiallySelfAdjoint`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L114) (definition); [`DLMF.AlgebraicAnalytic.IsLimitCircleLeft`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L184) (definition); [`DLMF.AlgebraicAnalytic.IsLimitCircleRight`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L189) (definition); [`DLMF.AlgebraicAnalytic.IsSelfAdjoint.inner_eigenvectors_eq_zero`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L493) (proved); [`DLMF.AlgebraicAnalytic.IsSelfAdjoint.opSpectrum_real`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L486) (admitted); [`DLMF.AlgebraicAnalytic.IsSymmetricOp.adjoint_domain_eq`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L519) (admitted); [`DLMF.AlgebraicAnalytic.IsSymmetricOp.exists_selfAdjoint_extension_iff`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L510) (admitted); [`DLMF.AlgebraicAnalytic.IsSymmetricOp.rank_deficiencySubspace`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L501) (admitted); [`DLMF.AlgebraicAnalytic.IsSymmetricOp.selfAdjoint_extension_iff`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L528) (admitted); [`DLMF.AlgebraicAnalytic.allSolutionsL2Left_of_exists`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L543) (admitted); [`DLMF.AlgebraicAnalytic.deficiencyIndices`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L156) (definition); [`DLMF.AlgebraicAnalytic.deficiencySubspace`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L151) (definition); [`DLMF.AlgebraicAnalytic.limitPoint_iff_wronskian_tendsto_zero`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L574) (admitted); [`DLMF.AlgebraicAnalytic.opContinuousSpectrum`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L139) (definition); [`DLMF.AlgebraicAnalytic.opPointSpectrum`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L134) (definition); [`DLMF.AlgebraicAnalytic.opResidualSpectrum`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L146) (definition); [`DLMF.AlgebraicAnalytic.opResolventSet`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L123) (definition); [`DLMF.AlgebraicAnalytic.opSpectrum`](DLMF/AlgebraicAnalytic/Spectral/Defs.lean#L130) (definition); [`DLMF.AlgebraicAnalytic.opSpectrum_eq_union`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L469) (proved); [`DLMF.AlgebraicAnalytic.rank_l2SolutionSpace_add_two`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L563) (admitted); [`DLMF.AlgebraicAnalytic.rank_l2SolutionSpace_left`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L553) (admitted); Mathlib: [`LinearPMap.IsFormalAdjoint.le_adjoint`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/LinearPMap.html#LinearPMap.IsFormalAdjoint.le_adjoint); Mathlib: [`LinearPMap.isSelfAdjoint_def`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/LinearPMap.html#LinearPMap.isSelfAdjoint_def); Mathlib: [`spectrum.isCompact`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Algebra/Spectrum.html#spectrum.isCompact).
- [1.18.viii](https://dlmf.nist.gov/1.18.viii): [`DLMF.AlgebraicAnalytic.exists_bound_state_of_integral_nonpos`](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L453) (admitted).

### Prose, informal and excluded items (part g1f)

- [§1.16(ix)](https://dlmf.nist.gov/1.16.ix), [§1.17(iv)](https://dlmf.nist.gov/1.17.iv),
  [§1.18(x)](https://dlmf.nist.gov/1.18.x) and the further-reading paragraph 1.18.Px16:
  excluded: no statement (references only).
- 1.17.ii.p2 and 1.17.Px4.p2 (physical interpretation of the δ-limits): excluded: informal.
- 1.18.p1 (introduction), 1.18.ii.p3, 1.18.iv.p2–p5, 1.18.Px6.p2 and 1.18.Px7.p1 (standing
  assumptions, absorbed into the hypotheses of the formalized statements): excluded:
  informal.
- [§1.18(vii)](https://dlmf.nist.gov/1.18.vii) (band spectra, Anderson localization) and
  1.18.viii.p2 (resonances): excluded: informal (descriptive, no precise statement).
- 1.18.Px11 (description of the radial Coulomb problem): excluded: informal.
- Not formalized: the §1.18(ix) remark that every self-adjoint extension of `𝓛` arises from
  boundary conditions (it needs the minimal operator on `L²` as a `LinearPMap`, which is not
  built here). The deficiency-index statements are stated for an abstract symmetric `T`.
- Excluded: numerical: none.

### Validation (part g1f)

- All 151 numbered IDs in scope (§1.16: 53, including 1.16.E3_5 and 1.16.E9_5; §1.17: 27,
  including 1.17.E12_1 and 1.17.E12_2; §1.18: 71) are covered: 32 with a proved theorem, 61
  by admitted theorems only, 22 by definitions only and 36 by upstream pointers only. There
  are 59 upstream pointers in the two `MathlibCoverage` files.
- The seven modules build with `lake build DLMF.AlgebraicAnalytic.<Area>.<Module>` and each
  passes `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false` without errors.
  Admissions: Distributions/Theory 17, Distributions/DiracDelta 17, Spectral/Theory 25; the
  Defs and MathlibCoverage files have none. There are no axioms, no `native_decide`, and no
  `sorry` in definitions or helper declarations (prefix `g1f_`). No Lean line exceeds 100
  characters.
- `#print axioms` for `deriv_sign`, `dlmfFourierTempered_delta`, `gaussian_fourier_eq`,
  `tendsto_gaussian_integral`, `hasSum_eigen_expansion`, `cosEigenfunction_spec` and
  `expEigenfunction_spec` shows only `propext`, `Classical.choice` and `Quot.sound`.
