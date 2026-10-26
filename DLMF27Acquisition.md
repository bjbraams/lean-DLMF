# DLMF Chapter 27 acquisition: Functions of Number Theory

This acquisition covers the definitions, numbered formulas and analytical assertions in prose
of [DLMF Chapter 27](https://dlmf.nist.gov/27), §§27.1–27.14, version 1.2.8, checked on
2026-10-25 (agent ACQ27). The applications §§27.15–27.17 and the computation sections
§§27.18–27.22 are excluded; their pure-mathematics content is pointed to Mathlib below. The
Lean code is in `DLMF/NumberTheory/` (namespace `DLMF.NumberTheory`, helper prefix `n27_`);
the modules, in import order, are
[Functions](DLMF/NumberTheory/Functions.lean) (§§27.1–27.3),
[DirichletSeries](DLMF/NumberTheory/DirichletSeries.lean) (§27.4),
[Inversion](DLMF/NumberTheory/Inversion.lean) (§27.5),
[DivisorSums](DLMF/NumberTheory/DivisorSums.lean) (§§27.6–27.7),
[Characters](DLMF/NumberTheory/Characters.lean) (§§27.8–27.10),
[Asymptotics](DLMF/NumberTheory/Asymptotics.lean) (§27.11),
[Primes](DLMF/NumberTheory/Primes.lean) (§27.12),
[Additive](DLMF/NumberTheory/Additive.lean) (§27.13),
[Partitions](DLMF/NumberTheory/Partitions.lean) (§27.14) and
[MathlibCoverage](DLMF/NumberTheory/MathlibCoverage.lean) (`dlmf_upstream` pointers). All of
them import `Functions`; `Partitions` also imports the AAR module
[DLMF/Partitions.lean](DLMF/Partitions.lean), `DLMF.QSeries.Pochhammer` and
`DLMF.Weierstrass.ModularFunctions`, and `Primes` imports `DLMF.ExpIntegrals.Basic` (for `li`)
and `DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion`. Nothing here depends on the
concurrent Chapter 25 work: `ζ` is Mathlib's `riemannZeta`.

**Counts.** §§27.2–27.14 have 134 numbered items (132 equations and the two tables 27.2.T1,
27.2.T2); §27.1 is notation only. In scope: 132 numbered equations (the tables are excluded:
numerical). Covered: all 132, of which 131 by project declarations and 27.4.E4 (the definition
of a Dirichlet series) by the upstream pointer to Mathlib's `LSeries`. In addition 14 prose IDs
(27.2.i, 27.3, 27.5, 27.8, 27.9, 27.10, 27.11, 27.12, 27.13.ii, 27.13.iii, 27.13.iv, 27.14.i,
27.14.v, 27.14.vi) carry tags. 145 DLMF IDs are tagged on 212 declarations: 30 definitions,
79 proved theorems, 3 theorems proved from admissions and 100 direct admissions. Of these,
208 declarations are in `DLMF/NumberTheory/` (97 admissions); the other four are the existing
AAR declarations `partitionFunction_zero` (proved) and `ramanujan_mod_five/seven/eleven`
(admitted) in DLMF/Partitions.lean, which received `@[dlmf]` tags only.

Module admissions (`grep -c '\bsorry\b'`) and tagged declarations:

- [Functions](DLMF/NumberTheory/Functions.lean): 0 admissions. 39 tagged: 6 definitions, 27 proved, 6 admitted.
- [DirichletSeries](DLMF/NumberTheory/DirichletSeries.lean): 0 admissions. 12 tagged: 7 proved, 5 admitted.
- [Inversion](DLMF/NumberTheory/Inversion.lean): 0 admissions. 12 tagged: 8 proved, 4 admitted.
- [DivisorSums](DLMF/NumberTheory/DivisorSums.lean): 0 admissions. 14 tagged: 1 definition, 3 proved, 1 proved from admissions, 9 admitted.
- [Characters](DLMF/NumberTheory/Characters.lean): 1 admissions. 42 tagged: 9 definitions, 17 proved, 16 admitted.
- [Asymptotics](DLMF/NumberTheory/Asymptotics.lean): 7 admissions. 18 tagged: 1 definition, 1 proved, 16 admitted.
- [Primes](DLMF/NumberTheory/Primes.lean): 8 admissions. 13 tagged: 2 proved, 1 proved from admissions, 10 admitted.
- [Additive](DLMF/NumberTheory/Additive.lean): 14 admissions. 28 tagged: 7 definitions, 3 proved, 1 proved from admissions, 17 admitted.
- [Partitions](DLMF/NumberTheory/Partitions.lean): 6 admissions. 30 tagged: 6 definitions, 10 proved, 14 admitted.
- [MathlibCoverage](DLMF/NumberTheory/MathlibCoverage.lean): 0 admissions; 49 `dlmf_upstream` pointers.

**Status after proof round 1 (2026-10-25).** The 212 declarations tagged with Chapter 27 IDs are 33 definitions, 117 proved theorems and 71 theorems that still depend on admissions; direct admissions in DLMF/NumberTheory fell from 97 to 65. The per-line statuses in this ledger are regenerated from the compiled dump; the counts below record the acquisition. See REVIEW.md, "Proof round 1 for Chapters 24–27 (2026-10-25)".

**Status after proof round 2 (2026-10-25).** The 212 declarations tagged with Chapter 27 IDs are 30 definitions, 128 proved theorems and 54 theorems that still depend on admissions; direct admissions in DLMF/NumberTheory fell from 65 to 49. Direct admissions in DLMF/Partitions.lean (Ramanujan congruences, 27.14(v)) remain 3. See REVIEW.md, "Proof round 2 for Chapters 24–27 (2026-10-25)".

**Status after proof round 3 (2026-10-26).** The 212 declarations tagged with Chapter 27 IDs are 30 definitions, 135 proved theorems and 47 theorems that still depend on admissions; direct admissions in DLMF/NumberTheory fell from 49 to 42. Direct admissions in DLMF/Partitions.lean (Ramanujan congruences, 27.14(v)) remain 3. No statement was changed. See REVIEW.md, "Proof round 3 for Chapters 24–27 (2026-10-26)".

**Status after the bridge round (2026-10-26).** τ multiplicativity (§27.14(vi)), 27.14.19 and the 691 congruence 27.14.20 are proved from TauCeti's discriminant eigenform results; 27.2.3, 27.2.4, 27.12.1 and the prime number theorem in arithmetic progressions (§27.11) from TauCeti's prime ideal and Chebotarev theorems. Direct admissions in DLMF/NumberTheory fell from 42 to 36. See REVIEW.md, "Ramanujan's τ and the prime number theorem (2026-10-26)".

## Domains, conventions and source corrections

- DLMF's arithmetic functions live on `n = 1, 2, …`. Mathlib's are `ArithmeticFunction R`
  (`f 0 = 0`); the new functions are total on `ℕ` and every statement carries `0 < n` where
  DLMF has `n ≥ 1`. Multiplicativity in DLMF's sense is `IsMultiplicativeFn` (27.3.1), proved
  equivalent to Mathlib's `ArithmeticFunction.IsMultiplicative`.
- Mathlib supplies `ν = ω` (`cardDistinctFactors`), `Ω`, `φ` (`Nat.totient`), `σ_k` for
  natural `k`, `μ`, `λ`, `Λ`, `π(n)` (`Nat.primeCounting`), Dirichlet characters, Legendre and
  Jacobi symbols, Gauss sums, `LSeries`, `riemannZeta`, `RiemannHypothesis`, the Euler function
  and pentagonal numbers, `ModularForm.eta` and `ModularForm.discriminant`. New definitions:
  `nthPrime n = Nat.nth Nat.Prime (n - 1)` (`p₁ = 2`), `primePi x = π(⌊x⌋)` for real `x`,
  `totientPowerSum` (`φ_k`), `IsPrimitiveRootMod`, `divisorCountK` (`d_k`), `sigmaC`
  (`σ_α`, complex `α`), `jordanTotient` (`J_k`), `lambertSeries`, `IsDirichletCharacterFn`,
  `IsPrimitiveDLMF`, `IsInducedModulus`, `IsPeriodicFn`, `finiteFourierCoeff`, `ramanujanSum`,
  `divisorConvolutionSum`, `gaussSumDLMF`, `GaussSumSeparable`, `HasPartialSumAsymptotic`,
  Waring's `waringSmallG`/`waringBigG`, `sumSquaresCount` (`r_k`), `jacobiThetaSeries` (`ϑ`),
  `partitionsAtMost` (`p_k`), `eulerReciprocal` (`f`), `rademacherA`, `discriminantDLMF`,
  `ramanujanTau`. The project's existing `DLMF.Partitions.partitionFunction`,
  `DLMF.QSeries.qPochhammerInf`, `DLMF.Weierstrass.dedekindSum` and
  `DLMF.Confluent.Real.logIntLi` (`li`) are reused, not redefined.
- Dirichlet series (§27.4) are stated as `LSeriesHasSum f s F` on `ℜs > σ_a`; Lambert series
  (§27.7) and the theta and partition generating functions as `HasSum` for `|x| < 1`;
  totalized `tsum`/`tprod` values are only used under such convergence statements.
- Asymptotic formulas (§§27.11–27.12) use `Asymptotics.IsBigO atTop` and `IsEquivalent`;
  constants that DLMF only asserts to exist are existentially quantified.
- Open conjectures are not stated as theorems: Goldbach (`GoldbachConjecture`), the
  Hardy–Littlewood conjectures on `G(k)` (`HardyLittlewoodWaringConjecture`) and Lehmer's
  `τ(n) ≠ 0` (`LehmerConjecture`) are `Prop` definitions (conjecture: not acquired); the
  Riemann hypothesis enters only through the equivalence 27.12.7.
- The prime number theorem 27.2.3 (and 27.2.4, 27.12.1, primes in progressions in §27.11) is
  proved since 2026-10-26 from TauCeti's prime ideal and Chebotarev theorems specialized to
  `K = ℚ`, through the bridge `DLMFMathlib/NumberTheory/T27aPrimeNumberTheorem.lean`.

Source corrections (each checked numerically; scripts in the agent's scratch directory):

- **§27.3, first sentence** (incorrect claim): DLMF says that all functions of §27.2 except `ν`,
  `Λ`, `p_n`, `π(x)` are multiplicative. The power sums `φ_k`, `k ≥ 1`, are not:
  `φ₁(2)φ₁(3) = 1 · 3 = 3 ≠ 6 = φ₁(6)` (`totientPowerSum_one_not_multiplicative`, proved).
- **27.3.6** (missing hypothesis): for complex `α` the condition `α ≠ 0` does not keep
  `p^α - 1` away from zero (`p^α = 1` for `α = 2πim/ln p`). Stated and proved under
  `p^α ≠ 1` for every prime `p ∣ n` (automatic for real `α ≠ 0`).
- **27.12.3** (erratum): Legendre's formula as printed,
  `π(x) = ⌊x⌋ - 1 - ∑_{p_j ≤ √x} ⌊x/p_j⌋ + ∑_{r≥2} (-1)^r ∑ ⌊x/(p_{j_1}⋯p_{j_r})⌋`, computes
  `π(x) - π(√x)`: at `x = 10` the right side is `10 - 1 - (5 + 3) + 1 = 2`, while `π(10) = 4`
  (the sieve counts the integers in `(1, x]` free of primes `≤ √x`). Acquired as
  `π(x) = π(√x) - 1 + ∑_{S ⊆ {p ≤ √x}} (-1)^{|S|} ⌊x/∏S⌋`, checked for
  `x = 1, 2, 3, 10, 30, 57.5, 100, 200`.
- **27.6.2** (stronger than DLMF): DLMF states it for `n > 1`; it holds for `n = 1` as well
  and is proved for all `n ≥ 1`.
- **27.14.17** (stronger than DLMF): proved for every `𝒜 ∈ SL(2, ℤ)`; DLMF assumes `c > 0`.
- 27.14.14: the multiplier `ε = exp(πi((a + d)/(12c) - s(d, c)))` agrees with DLMF 23.18.6's
  `exp(πi((a + d)/(12c) + s(-d, c)))` because `s(-d, c) = -s(d, c)` for `(c, d) = 1`; the
  transformation law was checked numerically for several matrices.
- Checked numerically and found correct: 27.3.4, 27.3.7, 27.3.8, all of §27.6, 27.10.5,
  27.10.7, 27.10.8, 27.10.10–27.10.12, the Jacobi-symbol properties of §27.9, 27.12.2, 27.13.7
  and Jacobi's `r₄` formula, 27.14.6, 27.14.7, 27.14.15, 27.14.19, 27.14.20 and the
  Rademacher series 27.14.9–27.14.10.

## Numbered formulas and prose items

## [§27.2 Functions](https://dlmf.nist.gov/27.2)

- [27.2.i](https://dlmf.nist.gov/27.2.i): [`DLMF.NumberTheory.infinite_setOf_prime'`](DLMF/NumberTheory/Functions.lean#L96) (proved); [`DLMF.NumberTheory.IsPrimitiveRootMod`](DLMF/NumberTheory/Functions.lean#L170) (definition); [`DLMF.NumberTheory.IsPrimitiveRootMod.reduced_residue_system`](DLMF/NumberTheory/Functions.lean#L177) (proved). Euclid's theorem (Mathlib `Nat.exists_infinite_primes`, pointer), the fundamental theorem of arithmetic (27.2.1) and primitive roots (`IsPrimitiveRootMod`: the powers of a primitive root form a reduced residue system); Mathlib: [`Nat.factorization_prod_pow_eq_self`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Factorization/Defs.html#Nat.factorization_prod_pow_eq_self).
- [27.2.E1](https://dlmf.nist.gov/27.2.E1): [`DLMF.NumberTheory.prod_primeFactors_pow_factorization`](DLMF/NumberTheory/Functions.lean#L78) (proved); [`DLMF.NumberTheory.eq_factorization_of_prod`](DLMF/NumberTheory/Functions.lean#L89) (proved). Existence via `Nat.factorization`; uniqueness as `eq_factorization_of_prod`. Mathlib: `Nat.factorization_prod_pow_eq_self` (pointer).
- [27.2.E2](https://dlmf.nist.gov/27.2.E2): [`DLMF.NumberTheory.primePi_eq_card`](DLMF/NumberTheory/Functions.lean#L100) (proved). `primePi x = Nat.primeCounting ⌊x⌋₊` for real `x`.
- [27.2.E3](https://dlmf.nist.gov/27.2.E3): [`DLMF.NumberTheory.primePi_isEquivalent`](DLMF/NumberTheory/Functions.lean#L109) (proved). The prime number theorem `π(x) ∼ x/ln x`; not in Mathlib. Proved from TauCeti's prime ideal theorem for `K = ℚ` (`Nat.t27a_primeCounting_isEquivalent`).
- [27.2.E4](https://dlmf.nist.gov/27.2.E4): [`DLMF.NumberTheory.nthPrime_isEquivalent`](DLMF/NumberTheory/Functions.lean#L117) (proved). `p_n ∼ n ln n` (`nthPrime n = Nat.nth Nat.Prime (n - 1)`, `p₁ = 2`).
- [27.2.E5](https://dlmf.nist.gov/27.2.E5): [`DLMF.NumberTheory.floor_one_div`](DLMF/NumberTheory/Functions.lean#L132) (proved).
- [27.2.E6](https://dlmf.nist.gov/27.2.E6): [`DLMF.NumberTheory.totientPowerSum`](DLMF/NumberTheory/Functions.lean#L146) (definition).
- [27.2.E7](https://dlmf.nist.gov/27.2.E7): [`DLMF.NumberTheory.totientPowerSum_zero`](DLMF/NumberTheory/Functions.lean#L152) (proved).
- [27.2.E8](https://dlmf.nist.gov/27.2.E8): [`DLMF.NumberTheory.pow_totient_modEq_one`](DLMF/NumberTheory/Functions.lean#L165) (proved). Mathlib: `Nat.ModEq.pow_totient` (pointer).
- [27.2.E9](https://dlmf.nist.gov/27.2.E9): [`DLMF.NumberTheory.divisorCountK`](DLMF/NumberTheory/Functions.lean#L206) (definition); [`DLMF.NumberTheory.sigma_zero_eq_card_divisors`](DLMF/NumberTheory/Functions.lean#L211) (proved); [`DLMF.NumberTheory.divisorCountK_two`](DLMF/NumberTheory/Functions.lean#L216) (proved). `d(n) = σ₀(n)` (Mathlib `ArithmeticFunction.sigma 0`); `d_k(n)` is `divisorCountK k n = #Nat.finMulAntidiag k n`; Mathlib: [`ArithmeticFunction.sigma_zero_apply`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ArithmeticFunction/Misc.html#ArithmeticFunction.sigma_zero_apply).
- [27.2.E10](https://dlmf.nist.gov/27.2.E10): [`DLMF.NumberTheory.sigmaC_apply`](DLMF/NumberTheory/Functions.lean#L244) (proved); [`DLMF.NumberTheory.sigmaC_zero`](DLMF/NumberTheory/Functions.lean#L261) (proved). `sigmaC α` is `σ_α` for complex `α` as an `ArithmeticFunction ℂ`; it agrees with Mathlib's `σ k` for natural `k` (`sigmaC_natCast`); Mathlib: [`ArithmeticFunction.sigma_apply`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ArithmeticFunction/Misc.html#ArithmeticFunction.sigma_apply).
- [27.2.E11](https://dlmf.nist.gov/27.2.E11): [`DLMF.NumberTheory.jordanTotient`](DLMF/NumberTheory/Functions.lean#L266) (definition); [`DLMF.NumberTheory.jordanTotient_one`](DLMF/NumberTheory/Functions.lean#L273) (proved). `J_k(n)` counted literally (k-tuples in `[1, n]` with gcd coprime to `n`); `J₁ = φ` proved; the product formula is 27.3.E4.
- [27.2.E12](https://dlmf.nist.gov/27.2.E12): [`DLMF.NumberTheory.moebius_eq_cases`](DLMF/NumberTheory/Functions.lean#L293) (proved).
- [27.2.E13](https://dlmf.nist.gov/27.2.E13): [`DLMF.NumberTheory.liouville_eq_cases`](DLMF/NumberTheory/Functions.lean#L321) (proved).
- [27.2.E14](https://dlmf.nist.gov/27.2.E14): [`DLMF.NumberTheory.vonMangoldt_eq_cases`](DLMF/NumberTheory/Functions.lean#L331) (proved); Mathlib: [`ArithmeticFunction.vonMangoldt_apply`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ArithmeticFunction/VonMangoldt.html#ArithmeticFunction.vonMangoldt_apply).

## [§27.3 Multiplicative Properties](https://dlmf.nist.gov/27.3)

- [27.3](https://dlmf.nist.gov/27.3): [`DLMF.NumberTheory.isMultiplicativeFn_basic`](DLMF/NumberTheory/Functions.lean#L385) (proved); [`DLMF.NumberTheory.isMultiplicativeFn_divisorCountK`](DLMF/NumberTheory/Functions.lean#L591) (proved); [`DLMF.NumberTheory.isMultiplicativeFn_jordanTotient`](DLMF/NumberTheory/Functions.lean#L602) (proved); [`DLMF.NumberTheory.totientPowerSum_one_not_multiplicative`](DLMF/NumberTheory/Functions.lean#L608) (proved). Multiplicativity of `⌊1/n⌋, φ, d, σ_α, μ, λ` (proved), `d_k` and `J_k` (admitted). Correction: `φ_k` (`k ≥ 1`) is not multiplicative (`totientPowerSum_one_not_multiplicative`, see source corrections).
- [27.3.E1](https://dlmf.nist.gov/27.3.E1): [`DLMF.NumberTheory.IsMultiplicativeFn`](DLMF/NumberTheory/Functions.lean#L342) (definition); [`DLMF.NumberTheory.isMultiplicative_iff_isMultiplicativeFn`](DLMF/NumberTheory/Functions.lean#L348) (proved). Equivalent to Mathlib's `ArithmeticFunction.IsMultiplicative` (`isMultiplicative_iff_isMultiplicativeFn`).
- [27.3.E2](https://dlmf.nist.gov/27.3.E2): [`DLMF.NumberTheory.IsMultiplicativeFn.eq_prod_primeFactors`](DLMF/NumberTheory/Functions.lean#L618) (proved). `IsMultiplicativeFn.eq_prod_primeFactors`, `n ≥ 1`.
- [27.3.E3](https://dlmf.nist.gov/27.3.E3): [`DLMF.NumberTheory.totient_eq_mul_prod`](DLMF/NumberTheory/Functions.lean#L632) (proved). Mathlib: `Nat.totient_eq_mul_prod_factors` (pointer).
- [27.3.E4](https://dlmf.nist.gov/27.3.E4): [`DLMF.NumberTheory.jordanTotient_eq_mul_prod`](DLMF/NumberTheory/Functions.lean#L638) (proved).
- [27.3.E5](https://dlmf.nist.gov/27.3.E5): [`DLMF.NumberTheory.sigma_zero_eq_prod`](DLMF/NumberTheory/Functions.lean#L663) (proved). Mathlib: `Nat.card_divisors` (pointer).
- [27.3.E6](https://dlmf.nist.gov/27.3.E6): [`DLMF.NumberTheory.sigmaC_eq_prod`](DLMF/NumberTheory/Functions.lean#L670) (proved). Corrected hypothesis `p^α ≠ 1` for all `p ∣ n` (DLMF: `α ≠ 0`).
- [27.3.E7](https://dlmf.nist.gov/27.3.E7): [`DLMF.NumberTheory.sigmaC_mul_sigmaC`](DLMF/NumberTheory/Functions.lean#L856) (proved).
- [27.3.E8](https://dlmf.nist.gov/27.3.E8): [`DLMF.NumberTheory.totient_mul_totient`](DLMF/NumberTheory/Functions.lean#L863) (proved). Mathlib: `Nat.totient_gcd_mul_totient_mul` (pointer).
- [27.3.E9](https://dlmf.nist.gov/27.3.E9): [`DLMF.NumberTheory.IsCompletelyMultiplicativeFn`](DLMF/NumberTheory/Functions.lean#L359) (definition); [`DLMF.NumberTheory.isCompletelyMultiplicativeFn_floor_one_div`](DLMF/NumberTheory/Functions.lean#L370) (proved); [`DLMF.NumberTheory.isCompletelyMultiplicativeFn_liouville`](DLMF/NumberTheory/Functions.lean#L379) (proved); Mathlib: [`ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ArithmeticFunction/Defs.html#ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers).
- [27.3.E10](https://dlmf.nist.gov/27.3.E10): [`DLMF.NumberTheory.IsCompletelyMultiplicativeFn.eq_prod_primeFactors`](DLMF/NumberTheory/Functions.lean#L872) (proved). The completely multiplicative case `IsCompletelyMultiplicativeFn.eq_prod_primeFactors`.

## [§27.4 Euler Products and Dirichlet Series](https://dlmf.nist.gov/27.4)

- [27.4.E1](https://dlmf.nist.gov/27.4.E1): [`DLMF.NumberTheory.eulerProduct_multiplicative`](DLMF/NumberTheory/DirichletSeries.lean#L35) (proved). Absolute convergence `∑|f(n)| n^{-σ} < ∞` as hypothesis (DLMF: 'absolutely convergent'). Mathlib: `EulerProduct.eulerProduct_hasProd` (pointer).
- [27.4.E2](https://dlmf.nist.gov/27.4.E2): [`DLMF.NumberTheory.eulerProduct_completelyMultiplicative`](DLMF/NumberTheory/DirichletSeries.lean#L48) (proved). Mathlib: `EulerProduct.eulerProduct_completely_multiplicative_hasProd` (pointer).
- [27.4.E3](https://dlmf.nist.gov/27.4.E3): [`DLMF.NumberTheory.riemannZeta_hasSum_hasProd`](DLMF/NumberTheory/DirichletSeries.lean#L55) (proved). Mathlib: `riemannZeta_eulerProduct_hasProd` (pointer).
- [27.4.E4](https://dlmf.nist.gov/27.4.E4): upstream only: Mathlib's `LSeries f s = ∑' n, f n / n ^ s` (pointer in [DLMF/NumberTheory/MathlibCoverage.lean](DLMF/NumberTheory/MathlibCoverage.lean); the `n = 0` term is dropped). All Dirichlet series of §27.4 are stated with `LSeriesHasSum`.
- [27.4.E5](https://dlmf.nist.gov/27.4.E5): [`DLMF.NumberTheory.LSeriesHasSum_moebius`](DLMF/NumberTheory/DirichletSeries.lean#L62) (proved). Mathlib: `ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius` (pointer).
- [27.4.E6](https://dlmf.nist.gov/27.4.E6): [`DLMF.NumberTheory.LSeriesHasSum_totient`](DLMF/NumberTheory/DirichletSeries.lean#L406) (proved).
- [27.4.E7](https://dlmf.nist.gov/27.4.E7): [`DLMF.NumberTheory.LSeriesHasSum_liouville`](DLMF/NumberTheory/DirichletSeries.lean#L412) (proved).
- [27.4.E8](https://dlmf.nist.gov/27.4.E8): [`DLMF.NumberTheory.LSeriesHasSum_abs_moebius`](DLMF/NumberTheory/DirichletSeries.lean#L418) (proved).
- [27.4.E9](https://dlmf.nist.gov/27.4.E9): [`DLMF.NumberTheory.LSeriesHasSum_two_pow_cardDistinctFactors`](DLMF/NumberTheory/DirichletSeries.lean#L424) (proved).
- [27.4.E10](https://dlmf.nist.gov/27.4.E10): [`DLMF.NumberTheory.LSeriesHasSum_divisorCountK`](DLMF/NumberTheory/DirichletSeries.lean#L431) (proved).
- [27.4.E11](https://dlmf.nist.gov/27.4.E11): [`DLMF.NumberTheory.LSeriesHasSum_sigmaC`](DLMF/NumberTheory/DirichletSeries.lean#L437) (proved).
- [27.4.E12](https://dlmf.nist.gov/27.4.E12): [`DLMF.NumberTheory.LSeriesHasSum_vonMangoldt`](DLMF/NumberTheory/DirichletSeries.lean#L445) (proved). Mathlib: `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div` (pointer).
- [27.4.E13](https://dlmf.nist.gov/27.4.E13): [`DLMF.NumberTheory.LSeriesHasSum_log`](DLMF/NumberTheory/DirichletSeries.lean#L453) (proved).

## [§27.5 Inversion Formulas](https://dlmf.nist.gov/27.5)

- [27.5](https://dlmf.nist.gov/27.5): [`DLMF.NumberTheory.isUnit_iff_apply_one_ne_zero`](DLMF/NumberTheory/Inversion.lean#L43) (proved); [`DLMF.NumberTheory.one_apply_eq_floor`](DLMF/NumberTheory/Inversion.lean#L51) (proved); [`DLMF.NumberTheory.isMultiplicative_mul_inv`](DLMF/NumberTheory/Inversion.lean#L115) (proved). Prose: Dirichlet-product units are the `f` with `f(1) ≠ 0`; the identity is `⌊1/n⌋`; the inverse of a multiplicative function is multiplicative (admitted).
- [27.5.E1](https://dlmf.nist.gov/27.5.E1): [`DLMF.NumberTheory.dirichletProduct_apply_hasSum`](DLMF/NumberTheory/Inversion.lean#L33) (proved); Mathlib: [`ArithmeticFunction.mul_apply`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ArithmeticFunction/Defs.html#ArithmeticFunction.mul_apply).
- [27.5.E2](https://dlmf.nist.gov/27.5.E2): [`DLMF.NumberTheory.sum_divisors_moebius`](DLMF/NumberTheory/Inversion.lean#L123) (proved); Mathlib: [`ArithmeticFunction.moebius_mul_coe_zeta`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ArithmeticFunction/Moebius.html#ArithmeticFunction.moebius_mul_coe_zeta).
- [27.5.E3](https://dlmf.nist.gov/27.5.E3): [`DLMF.NumberTheory.moebius_inversion`](DLMF/NumberTheory/Inversion.lean#L129) (proved). Mathlib: `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq` (pointer).
- [27.5.E4](https://dlmf.nist.gov/27.5.E4): [`DLMF.NumberTheory.sum_totient_and_inverse`](DLMF/NumberTheory/Inversion.lean#L146) (proved). Mathlib: `Nat.sum_totient` (pointer).
- [27.5.E5](https://dlmf.nist.gov/27.5.E5): [`DLMF.NumberTheory.sum_vonMangoldt_and_inverse`](DLMF/NumberTheory/Inversion.lean#L156) (proved). Mathlib: `ArithmeticFunction.vonMangoldt_sum` (pointer).
- [27.5.E6](https://dlmf.nist.gov/27.5.E6): [`DLMF.NumberTheory.moebius_inversion_floor`](DLMF/NumberTheory/Inversion.lean#L267) (proved). Generalized inversion `G(x) = ∑_{n≤x} F(x/n)`, `x ≥ 1` (admitted).
- [27.5.E7](https://dlmf.nist.gov/27.5.E7): [`DLMF.NumberTheory.moebius_inversion_series`](DLMF/NumberTheory/Inversion.lean#L451) (proved); [`DLMF.NumberTheory.moebius_inversion_series_symm`](DLMF/NumberTheory/Inversion.lean#L464) (proved). Both directions, with the absolute-convergence hypotheses that DLMF leaves implicit.
- [27.5.E8](https://dlmf.nist.gov/27.5.E8): [`DLMF.NumberTheory.moebius_inversion_prod`](DLMF/NumberTheory/Inversion.lean#L476) (proved). Mathlib: `ArithmeticFunction.prod_eq_iff_prod_pow_moebius_eq_of_nonzero` (pointer).

## [§27.6 Divisor Sums](https://dlmf.nist.gov/27.6)

- [27.6.E1](https://dlmf.nist.gov/27.6.E1): [`DLMF.NumberTheory.sum_divisors_liouville`](DLMF/NumberTheory/DivisorSums.lean#L32) (proved).
- [27.6.E2](https://dlmf.nist.gov/27.6.E2): [`DLMF.NumberTheory.sum_divisors_moebius_mul`](DLMF/NumberTheory/DivisorSums.lean#L92) (proved). Stronger than DLMF: holds for all `n ≥ 1` (DLMF: `n > 1`). Mathlib: `ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree` (partial, squarefree `n`).
- [27.6.E3](https://dlmf.nist.gov/27.6.E3): [`DLMF.NumberTheory.sum_divisors_abs_moebius`](DLMF/NumberTheory/DivisorSums.lean#L111) (proved).
- [27.6.E4](https://dlmf.nist.gov/27.6.E4): [`DLMF.NumberTheory.sum_sq_dvd_moebius`](DLMF/NumberTheory/DivisorSums.lean#L247) (proved).
- [27.6.E5](https://dlmf.nist.gov/27.6.E5): [`DLMF.NumberTheory.sum_divisors_abs_moebius_div_totient`](DLMF/NumberTheory/DivisorSums.lean#L253) (proved).
- [27.6.E6](https://dlmf.nist.gov/27.6.E6): [`DLMF.NumberTheory.sum_divisors_totientPowerSum`](DLMF/NumberTheory/DivisorSums.lean#L259) (proved).
- [27.6.E7](https://dlmf.nist.gov/27.6.E7): [`DLMF.NumberTheory.sum_divisors_moebius_pow`](DLMF/NumberTheory/DivisorSums.lean#L271) (proved). Proved from 27.6.E8 (admitted).
- [27.6.E8](https://dlmf.nist.gov/27.6.E8): [`DLMF.NumberTheory.sum_divisors_jordanTotient`](DLMF/NumberTheory/DivisorSums.lean#L265) (proved).

## [§27.7 Lambert Series as Generating Functions](https://dlmf.nist.gov/27.7)

- [27.7.E1](https://dlmf.nist.gov/27.7.E1): [`DLMF.NumberTheory.lambertSeries`](DLMF/NumberTheory/DivisorSums.lean#L285) (definition). `lambertSeries f x = ∑ f(n) xⁿ/(1 - xⁿ)` (index `n + 1`).
- [27.7.E2](https://dlmf.nist.gov/27.7.E2): [`DLMF.NumberTheory.lambertSeries_hasSum`](DLMF/NumberTheory/DivisorSums.lean#L493) (proved).
- [27.7.E3](https://dlmf.nist.gov/27.7.E3): [`DLMF.NumberTheory.lambert_moebius`](DLMF/NumberTheory/DivisorSums.lean#L502) (proved).
- [27.7.E4](https://dlmf.nist.gov/27.7.E4): [`DLMF.NumberTheory.lambert_totient`](DLMF/NumberTheory/DivisorSums.lean#L508) (proved).
- [27.7.E5](https://dlmf.nist.gov/27.7.E5): [`DLMF.NumberTheory.lambert_cpow`](DLMF/NumberTheory/DivisorSums.lean#L515) (proved). Complex `α`; Mathlib `tsum_pow_div_one_sub_eq_tsum_sigma` (partial, natural `α`, pointer).
- [27.7.E6](https://dlmf.nist.gov/27.7.E6): [`DLMF.NumberTheory.lambert_liouville`](DLMF/NumberTheory/DivisorSums.lean#L524) (proved).

## [§27.8 Dirichlet Characters](https://dlmf.nist.gov/27.8)

- [27.8](https://dlmf.nist.gov/27.8): [`DLMF.NumberTheory.IsDirichletCharacterFn.exists_dirichletCharacter`](DLMF/NumberTheory/Characters.lean#L81) (proved); [`DLMF.NumberTheory.DirichletCharacter.apply_ne_zero_iff`](DLMF/NumberTheory/Characters.lean#L124) (proved); [`DLMF.NumberTheory.card_dirichletCharacter`](DLMF/NumberTheory/Characters.lean#L135) (proved); [`DLMF.NumberTheory.DirichletCharacter.exists_conj`](DLMF/NumberTheory/Characters.lean#L148) (proved); [`DLMF.NumberTheory.IsPrimitiveDLMF`](DLMF/NumberTheory/Characters.lean#L185) (definition); [`DLMF.NumberTheory.isPrimitiveDLMF_iff`](DLMF/NumberTheory/Characters.lean#L239) (proved); [`DLMF.NumberTheory.isPrimitive_of_prime`](DLMF/NumberTheory/Characters.lean#L253) (proved); [`DLMF.NumberTheory.real_character_eq_jacobiSym`](DLMF/NumberTheory/Characters.lean#L285) (admitted). Prose: existence of `φ(k)` characters, `χ(n) ≠ 0 ⇔ (n, k) = 1`, conjugate characters, primitive characters (`IsPrimitiveDLMF`, equivalent to Mathlib's `DirichletCharacter.IsPrimitive`), nonprincipal characters to prime moduli are primitive, real characters as Jacobi symbols. Mathlib: `DirichletCharacter.conductor` (pointer).
- [27.8.E1](https://dlmf.nist.gov/27.8.E1): [`DLMF.NumberTheory.IsDirichletCharacterFn`](DLMF/NumberTheory/Characters.lean#L41) (definition); [`DirichletCharacter.isDirichletCharacterFn`](DLMF/NumberTheory/Characters.lean#L48) (proved). One definition `IsDirichletCharacterFn` bundles 27.8.1–27.8.4; Mathlib's `DirichletCharacter ℂ k` satisfies it.
- [27.8.E2](https://dlmf.nist.gov/27.8.E2): [`DLMF.NumberTheory.IsDirichletCharacterFn`](DLMF/NumberTheory/Characters.lean#L41) (definition); [`DirichletCharacter.isDirichletCharacterFn`](DLMF/NumberTheory/Characters.lean#L48) (proved).
- [27.8.E3](https://dlmf.nist.gov/27.8.E3): [`DLMF.NumberTheory.IsDirichletCharacterFn`](DLMF/NumberTheory/Characters.lean#L41) (definition); [`DirichletCharacter.isDirichletCharacterFn`](DLMF/NumberTheory/Characters.lean#L48) (proved).
- [27.8.E4](https://dlmf.nist.gov/27.8.E4): [`DLMF.NumberTheory.IsDirichletCharacterFn`](DLMF/NumberTheory/Characters.lean#L41) (definition); [`DirichletCharacter.isDirichletCharacterFn`](DLMF/NumberTheory/Characters.lean#L48) (proved).
- [27.8.E5](https://dlmf.nist.gov/27.8.E5): [`DLMF.NumberTheory.principalCharacter_apply`](DLMF/NumberTheory/Characters.lean#L115) (proved).
- [27.8.E6](https://dlmf.nist.gov/27.8.E6): [`DLMF.NumberTheory.sum_dirichletCharacter_mul_conj`](DLMF/NumberTheory/Characters.lean#L177) (proved). Mathlib: `DirichletCharacter.sum_char_inv_mul_char_eq` (pointer; exact up to `χ⁻¹ = conj χ`).
- [27.8.E7](https://dlmf.nist.gov/27.8.E7): [`DLMF.NumberTheory.IsInducedModulus`](DLMF/NumberTheory/Characters.lean#L259) (definition).
- [27.8.E8](https://dlmf.nist.gov/27.8.E8): [`DLMF.NumberTheory.DirichletCharacter.eq_mul_principal`](DLMF/NumberTheory/Characters.lean#L277) (proved). Every character mod `k` is induced from a primitive character mod its conductor (admitted).

## [§27.9 Quadratic Characters](https://dlmf.nist.gov/27.9)

- [27.9](https://dlmf.nist.gov/27.9): [`DLMF.NumberTheory.legendreSym_cases`](DLMF/NumberTheory/Characters.lean#L295) (proved); [`DLMF.NumberTheory.isDirichletCharacterFn_legendreSym`](DLMF/NumberTheory/Characters.lean#L305) (proved); [`DLMF.NumberTheory.jacobiSym_cases`](DLMF/NumberTheory/Characters.lean#L368) (proved); [`DLMF.NumberTheory.isDirichletCharacterFn_jacobiSym`](DLMF/NumberTheory/Characters.lean#L378) (proved). Legendre and Jacobi symbols as real Dirichlet characters (proved from Mathlib).
- [27.9.E1](https://dlmf.nist.gov/27.9.E1): [`DLMF.NumberTheory.legendreSym_neg_one`](DLMF/NumberTheory/Characters.lean#L324) (proved); [`DLMF.NumberTheory.jacobiSym_neg_one`](DLMF/NumberTheory/Characters.lean#L393) (proved). Mathlib: `legendreSym.at_neg_one` (pointer).
- [27.9.E2](https://dlmf.nist.gov/27.9.E2): [`DLMF.NumberTheory.legendreSym_two`](DLMF/NumberTheory/Characters.lean#L347) (proved); [`DLMF.NumberTheory.jacobiSym_two`](DLMF/NumberTheory/Characters.lean#L401) (proved). Mathlib: `legendreSym.at_two` (pointer).
- [27.9.E3](https://dlmf.nist.gov/27.9.E3): [`DLMF.NumberTheory.legendreSym_reciprocity`](DLMF/NumberTheory/Characters.lean#L354) (proved); [`DLMF.NumberTheory.jacobiSym_reciprocity`](DLMF/NumberTheory/Characters.lean#L406) (proved). Mathlib: `legendreSym.quadratic_reciprocity`, `jacobiSym.quadratic_reciprocity` (pointers).

## [§27.10 Periodic Number-Theoretic Functions](https://dlmf.nist.gov/27.10)

- [27.10](https://dlmf.nist.gov/27.10): [`DLMF.NumberTheory.isPrimitive_of_separable`](DLMF/NumberTheory/Characters.lean#L1089) (proved). Prose: separable Gauss sums for primitive characters (`isPrimitive_of_separable`, admitted).
- [27.10.E1](https://dlmf.nist.gov/27.10.E1): [`DLMF.NumberTheory.IsPeriodicFn`](DLMF/NumberTheory/Characters.lean#L422) (definition); [`DLMF.NumberTheory.isPeriodicFn_examples`](DLMF/NumberTheory/Characters.lean#L427) (proved).
- [27.10.E2](https://dlmf.nist.gov/27.10.E2): [`DLMF.NumberTheory.finiteFourier_expansion`](DLMF/NumberTheory/Characters.lean#L656) (proved).
- [27.10.E3](https://dlmf.nist.gov/27.10.E3): [`DLMF.NumberTheory.finiteFourierCoeff`](DLMF/NumberTheory/Characters.lean#L437) (definition); [`DLMF.NumberTheory.finiteFourier_expansion`](DLMF/NumberTheory/Characters.lean#L656) (proved).
- [27.10.E4](https://dlmf.nist.gov/27.10.E4): [`DLMF.NumberTheory.ramanujanSum`](DLMF/NumberTheory/Characters.lean#L664) (definition); [`DLMF.NumberTheory.ramanujanSum_eq_sum_primitiveRoots`](DLMF/NumberTheory/Characters.lean#L748) (proved).
- [27.10.E5](https://dlmf.nist.gov/27.10.E5): [`DLMF.NumberTheory.ramanujanSum_eq_sum_divisors`](DLMF/NumberTheory/Characters.lean#L755) (proved).
- [27.10.E6](https://dlmf.nist.gov/27.10.E6): [`DLMF.NumberTheory.divisorConvolutionSum`](DLMF/NumberTheory/Characters.lean#L761) (definition); [`DLMF.NumberTheory.isPeriodicFn_divisorConvolutionSum`](DLMF/NumberTheory/Characters.lean#L766) (proved).
- [27.10.E7](https://dlmf.nist.gov/27.10.E7): [`DLMF.NumberTheory.divisorConvolutionSum_fourier`](DLMF/NumberTheory/Characters.lean#L773) (proved).
- [27.10.E8](https://dlmf.nist.gov/27.10.E8): [`DLMF.NumberTheory.divisorConvolutionSum_fourier`](DLMF/NumberTheory/Characters.lean#L773) (proved).
- [27.10.E9](https://dlmf.nist.gov/27.10.E9): [`DLMF.NumberTheory.gaussSumDLMF`](DLMF/NumberTheory/Characters.lean#L855) (definition); [`DLMF.NumberTheory.gaussSumDLMF_one`](DLMF/NumberTheory/Characters.lean#L860) (proved); [`DLMF.NumberTheory.gaussSumDLMF_eq_gaussSum`](DLMF/NumberTheory/Characters.lean#L881) (proved). DLMF's `G(n, χ) = ∑_{m=1}^{k} χ(m) e^{2πimn/k}`; bridge `gaussSumDLMF_eq_gaussSum` to Mathlib's `gaussSum` (admitted). Mathlib: `gaussSum` (pointer).
- [27.10.E10](https://dlmf.nist.gov/27.10.E10): [`DLMF.NumberTheory.GaussSumSeparable`](DLMF/NumberTheory/Characters.lean#L888) (definition); [`DLMF.NumberTheory.gaussSumSeparable_iff`](DLMF/NumberTheory/Characters.lean#L912) (proved).
- [27.10.E11](https://dlmf.nist.gov/27.10.E11): [`DLMF.NumberTheory.gaussSumDLMF_primitive`](DLMF/NumberTheory/Characters.lean#L976) (proved). Mathlib: `gaussSum_mulShift_of_isPrimitive` (partial, pointer).
- [27.10.E12](https://dlmf.nist.gov/27.10.E12): [`DLMF.NumberTheory.dirichletCharacter_fourier`](DLMF/NumberTheory/Characters.lean#L1096) (proved).

## [§27.11 Asymptotic Formulas: Partial Sums](https://dlmf.nist.gov/27.11)

- [27.11](https://dlmf.nist.gov/27.11): [`DLMF.NumberTheory.sum_sigma_zero_huxley`](DLMF/NumberTheory/Asymptotics.lean#L1746) (admitted); [`DLMF.NumberTheory.infinite_primes_mod`](DLMF/NumberTheory/Asymptotics.lean#L1824) (proved); [`DLMF.NumberTheory.primeCounting_ap_isEquivalent`](DLMF/NumberTheory/Asymptotics.lean#L1858) (proved). Prose: Huxley's exponent `θ > 131/416` (admitted), Dirichlet's theorem (proved from Mathlib `Nat.infinite_setOfPred_prime_and_modEq`; pointer `Nat.infinite_setOf_prime_and_eq_mod`), the prime number theorem in arithmetic progressions (proved from TauCeti's natural-density Chebotarev theorem).
- [27.11.E1](https://dlmf.nist.gov/27.11.E1): [`DLMF.NumberTheory.HasPartialSumAsymptotic`](DLMF/NumberTheory/Asymptotics.lean#L39) (definition). `O(g(x))` as `Asymptotics.IsBigO atTop`; constants that DLMF only asserts to exist are existentially quantified (27.11.8, 27.11.9, 27.11.12).
- [27.11.E2](https://dlmf.nist.gov/27.11.E2): [`DLMF.NumberTheory.sum_sigma_zero_asymptotic`](DLMF/NumberTheory/Asymptotics.lean#L1738) (proved).
- [27.11.E3](https://dlmf.nist.gov/27.11.E3): [`DLMF.NumberTheory.sum_sigma_zero_div_asymptotic`](DLMF/NumberTheory/Asymptotics.lean#L1755) (proved).
- [27.11.E4](https://dlmf.nist.gov/27.11.E4): [`DLMF.NumberTheory.sum_sigma_one_asymptotic`](DLMF/NumberTheory/Asymptotics.lean#L1763) (proved).
- [27.11.E5](https://dlmf.nist.gov/27.11.E5): [`DLMF.NumberTheory.sum_sigmaC_asymptotic`](DLMF/NumberTheory/Asymptotics.lean#L1770) (proved).
- [27.11.E6](https://dlmf.nist.gov/27.11.E6): [`DLMF.NumberTheory.sum_totient_asymptotic`](DLMF/NumberTheory/Asymptotics.lean#L1779) (proved).
- [27.11.E7](https://dlmf.nist.gov/27.11.E7): [`DLMF.NumberTheory.sum_totient_div_asymptotic`](DLMF/NumberTheory/Asymptotics.lean#L1786) (proved).
- [27.11.E8](https://dlmf.nist.gov/27.11.E8): [`DLMF.NumberTheory.sum_prime_inv_asymptotic`](DLMF/NumberTheory/Asymptotics.lean#L1793) (proved).
- [27.11.E9](https://dlmf.nist.gov/27.11.E9): [`DLMF.NumberTheory.sum_prime_inv_ap_asymptotic`](DLMF/NumberTheory/Asymptotics.lean#L1801) (admitted).
- [27.11.E10](https://dlmf.nist.gov/27.11.E10): [`DLMF.NumberTheory.sum_log_prime_div_asymptotic`](DLMF/NumberTheory/Asymptotics.lean#L1809) (proved).
- [27.11.E11](https://dlmf.nist.gov/27.11.E11): [`DLMF.NumberTheory.sum_log_prime_div_ap_asymptotic`](DLMF/NumberTheory/Asymptotics.lean#L1816) (admitted).
- [27.11.E12](https://dlmf.nist.gov/27.11.E12): [`DLMF.NumberTheory.sum_moebius_isBigO`](DLMF/NumberTheory/Asymptotics.lean#L1831) (admitted).
- [27.11.E13](https://dlmf.nist.gov/27.11.E13): [`DLMF.NumberTheory.tendsto_sum_moebius_div`](DLMF/NumberTheory/Asymptotics.lean#L1838) (admitted).
- [27.11.E14](https://dlmf.nist.gov/27.11.E14): [`DLMF.NumberTheory.tendsto_sum_moebius_div_self`](DLMF/NumberTheory/Asymptotics.lean#L1845) (admitted).
- [27.11.E15](https://dlmf.nist.gov/27.11.E15): [`DLMF.NumberTheory.tendsto_sum_moebius_log_div`](DLMF/NumberTheory/Asymptotics.lean#L1851) (admitted).

## [§27.12 Asymptotic Formulas: Primes](https://dlmf.nist.gov/27.12)

- [27.12](https://dlmf.nist.gov/27.12): [`DLMF.NumberTheory.infinite_primes_mod`](DLMF/NumberTheory/Asymptotics.lean#L1824) (proved); [`DLMF.NumberTheory.primePi_sub_li_sign_changes`](DLMF/NumberTheory/Primes.lean#L184) (admitted); [`DLMF.NumberTheory.prime_of_mersenne_prime`](DLMF/NumberTheory/Primes.lean#L210) (proved); [`DLMF.NumberTheory.not_prime_of_two_pow_not_modEq`](DLMF/NumberTheory/Primes.lean#L216) (proved); [`DLMF.NumberTheory.isCarmichael_iff_dlmf`](DLMF/NumberTheory/Primes.lean#L267) (proved); [`DLMF.NumberTheory.infinite_setOf_isCarmichael`](DLMF/NumberTheory/Primes.lean#L274) (admitted). Prose: Dirichlet's theorem (shared with §27.11), Littlewood's sign changes of `π(x) - li(x)` (admitted), Mersenne primes (`Nat.Prime.of_mersenne`), the pseudoprime test (proved), Carmichael numbers (Mathlib `Nat.IsCarmichael`, pointer; Korselt bridge and Alford–Granville–Pomerance admitted). The largest known prime is excluded (numerical); Mathlib: [`Nat.bertrand`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Bertrand.html#Nat.bertrand).
- [27.12.E1](https://dlmf.nist.gov/27.12.E1): [`DLMF.NumberTheory.tendsto_nthPrime_div`](DLMF/NumberTheory/Primes.lean#L43) (proved). Proved from 27.2.E4.
- [27.12.E2](https://dlmf.nist.gov/27.12.E2): [`DLMF.NumberTheory.nthPrime_gt`](DLMF/NumberTheory/Primes.lean#L57) (admitted).
- [27.12.E3](https://dlmf.nist.gov/27.12.E3): [`DLMF.NumberTheory.primePi_legendre`](DLMF/NumberTheory/Primes.lean#L90) (proved). Corrected form `π(x) = π(√x) - 1 + ∑_{S} (-1)^{|S|} ⌊x/∏S⌋` (see source corrections).
- [27.12.E4](https://dlmf.nist.gov/27.12.E4): [`DLMF.NumberTheory.primePi_hasAsymptoticExpansion`](DLMF/NumberTheory/Primes.lean#L159) (admitted). `HasAsymptoticExpansion` of DLMFMathlib with scale `x/(ln x)^{k+1}` and coefficients `k!`.
- [27.12.E5](https://dlmf.nist.gov/27.12.E5): [`DLMF.NumberTheory.primePi_sub_li_isBigO`](DLMF/NumberTheory/Primes.lean#L167) (admitted).
- [27.12.E6](https://dlmf.nist.gov/27.12.E6): [`DLMF.NumberTheory.primePi_sub_li_isBigO_vinogradov`](DLMF/NumberTheory/Primes.lean#L175) (admitted).
- [27.12.E7](https://dlmf.nist.gov/27.12.E7): [`DLMF.NumberTheory.riemannHypothesis_iff_primePi`](DLMF/NumberTheory/Primes.lean#L191) (admitted). Equivalence with Mathlib's `RiemannHypothesis`; not a claim that RH holds.
- [27.12.E8](https://dlmf.nist.gov/27.12.E8): [`DLMF.NumberTheory.primeCounting_ap_siegelWalfisz`](DLMF/NumberTheory/Primes.lean#L199) (admitted).

## [§27.13 Functions](https://dlmf.nist.gov/27.13)

- [27.13.ii](https://dlmf.nist.gov/27.13.ii): [`DLMF.NumberTheory.GoldbachConjecture`](DLMF/NumberTheory/Additive.lean#L37) (definition); [`DLMF.NumberTheory.vinogradov_three_primes`](DLMF/NumberTheory/Additive.lean#L43) (admitted); [`DLMF.NumberTheory.chen_even`](DLMF/NumberTheory/Additive.lean#L51) (admitted). Goldbach's conjecture is open: `GoldbachConjecture` is a `Prop` definition only (conjecture: not acquired as a theorem). Vinogradov's and Chen's theorems admitted.
- [27.13.iii](https://dlmf.nist.gov/27.13.iii): [`DLMF.NumberTheory.isWaringNumber_two_four`](DLMF/NumberTheory/Additive.lean#L76) (proved); [`DLMF.NumberTheory.waringSmallG_two`](DLMF/NumberTheory/Additive.lean#L84) (proved); [`DLMF.NumberTheory.waring_hilbert`](DLMF/NumberTheory/Additive.lean#L111) (admitted); [`DLMF.NumberTheory.waringSmallG_values`](DLMF/NumberTheory/Additive.lean#L116) (admitted); [`DLMF.NumberTheory.waringBigG_le_waringSmallG`](DLMF/NumberTheory/Additive.lean#L148) (proved from admissions); [`DLMF.NumberTheory.waringBigG_values`](DLMF/NumberTheory/Additive.lean#L157) (admitted); [`DLMF.NumberTheory.waringBigG_bounds`](DLMF/NumberTheory/Additive.lean#L162) (admitted); [`DLMF.NumberTheory.HardyLittlewoodWaringConjecture`](DLMF/NumberTheory/Additive.lean#L169) (definition); [`DLMF.NumberTheory.waringBigG_lt`](DLMF/NumberTheory/Additive.lean#L176) (admitted). Lagrange (`isWaringNumber_two_four` proved from Mathlib `Nat.sum_four_squares`, pointer; `g(2) = 4` admitted), Hilbert, the exact values `g(3), …, g(8)`, `G(k) ≤ g(k)` (proved from Hilbert), `G(2) = 4`, `G(4) = 16`, the upper bounds for `G(3), G(5), …, G(8)` and `G(k) < ck ln k`. The Hardy–Littlewood conjectures are open: `HardyLittlewoodWaringConjecture` is a `Prop` definition only (conjecture: not acquired as a theorem).
- [27.13.E1](https://dlmf.nist.gov/27.13.E1): [`DLMF.NumberTheory.IsWaringNumber`](DLMF/NumberTheory/Additive.lean#L60) (definition); [`DLMF.NumberTheory.waringSmallG`](DLMF/NumberTheory/Additive.lean#L66) (definition); [`DLMF.NumberTheory.waringBigG`](DLMF/NumberTheory/Additive.lean#L70) (definition). `g(k)` and `G(k)` as `sInf` (junk value `0` if no admissible `m`; Hilbert's theorem shows the sets are nonempty).
- [27.13.E2](https://dlmf.nist.gov/27.13.E2): [`DLMF.NumberTheory.waringSmallG_ge`](DLMF/NumberTheory/Additive.lean#L123) (admitted); [`DLMF.NumberTheory.waringSmallG_eq_of_le`](DLMF/NumberTheory/Additive.lean#L128) (admitted); [`DLMF.NumberTheory.waringSmallG_eq_of_rem`](DLMF/NumberTheory/Additive.lean#L134) (admitted); [`DLMF.NumberTheory.waring_rem_condition_eventually`](DLMF/NumberTheory/Additive.lean#L141) (admitted). Also the two equality criteria and Mahler's finiteness result stated after 27.13.2.
- [27.13.iv](https://dlmf.nist.gov/27.13.iv): [`DLMF.NumberTheory.jacobiThetaSeries_pow`](DLMF/NumberTheory/Additive.lean#L422) (proved); [`DLMF.NumberTheory.sumSquaresCount_four`](DLMF/NumberTheory/Additive.lean#L451) (admitted). Prose: `ϑ(x)^k = ∑ r_k(n) xⁿ` and Jacobi's `r₄(n)` formula (admitted). The remark on exact formulas for `r_k`, `k = 3, 5, 7, …`, is informal and not acquired.
- [27.13.E3](https://dlmf.nist.gov/27.13.E3): [`DLMF.NumberTheory.sumSquaresCount`](DLMF/NumberTheory/Additive.lean#L183) (definition). `r_k(n)` as a `Finset` count over `x : Fin k → ℤ`, `|x_i| ≤ n`.
- [27.13.E4](https://dlmf.nist.gov/27.13.E4): [`DLMF.NumberTheory.jacobiThetaSeries`](DLMF/NumberTheory/Additive.lean#L190) (definition); [`DLMF.NumberTheory.jacobiTheta_eq_jacobiThetaSeries`](DLMF/NumberTheory/Additive.lean#L194) (proved). `ϑ(x) = 1 + 2∑ x^{m²}` (totalized); bridge to Mathlib's `jacobiTheta` (proved; Mathlib `jacobiTheta_eq_tsum_nat`, pointer).
- [27.13.E5](https://dlmf.nist.gov/27.13.E5): [`DLMF.NumberTheory.jacobiThetaSeries_sq`](DLMF/NumberTheory/Additive.lean#L410) (proved).
- [27.13.E6](https://dlmf.nist.gov/27.13.E6): [`DLMF.NumberTheory.jacobiThetaSeries_sq_divisors`](DLMF/NumberTheory/Additive.lean#L430) (admitted).
- [27.13.E7](https://dlmf.nist.gov/27.13.E7): [`DLMF.NumberTheory.sumSquaresCount_two`](DLMF/NumberTheory/Additive.lean#L439) (admitted); [`DLMF.NumberTheory.sumSquaresCount_two_five`](DLMF/NumberTheory/Additive.lean#L446) (proved). The example `r₂(5) = 8` is proved by `rfl`.

## [§27.14 Unrestricted Partitions](https://dlmf.nist.gov/27.14)

- [27.14.i](https://dlmf.nist.gov/27.14.i): [`DLMF.NumberTheory.partitionFunction_five`](DLMF/NumberTheory/Partitions.lean#L350) (proved); [`DLMF.NumberTheory.partitionsAtMost`](DLMF/NumberTheory/Partitions.lean#L362) (definition). `p(5) = 7` (admitted: the `Fintype` instance of `Nat.Partition` does not reduce by `decide`), `p_k(n)` as `partitionsAtMost`.
- [27.14.E1](https://dlmf.nist.gov/27.14.E1): [`DLMF.NumberTheory.partitionFunction_eq_card`](DLMF/NumberTheory/Partitions.lean#L344) (proved).
- [27.14.E2](https://dlmf.nist.gov/27.14.E2): [`DLMF.NumberTheory.eulerReciprocal`](DLMF/NumberTheory/Partitions.lean#L369) (definition); [`DLMF.NumberTheory.eulerReciprocal_eq_qPochhammerInf`](DLMF/NumberTheory/Partitions.lean#L374) (proved); [`DLMF.NumberTheory.hasProd_eulerReciprocal`](DLMF/NumberTheory/Partitions.lean#L380) (proved). `eulerReciprocal x = ∏' (1 - x^{m+1})`; equal to `(x; x)_∞` for all `x` and to Mathlib's `eulerFunction x` for `|x| < 1`. Mathlib: `hasProd_eulerFunction` (pointer).
- [27.14.E3](https://dlmf.nist.gov/27.14.E3): [`DLMF.NumberTheory.hasSum_partitionFunction`](DLMF/NumberTheory/Partitions.lean#L388) (proved); [`DLMF.Partitions.partitionFunction_zero`](DLMF/Partitions.lean#L34) (proved). `p(0) = 1` is `DLMF.Partitions.partitionFunction_zero` (tagged in DLMF/Partitions.lean).
- [27.14.E4](https://dlmf.nist.gov/27.14.E4): [`DLMF.NumberTheory.eulerReciprocal_pentagonal`](DLMF/NumberTheory/Partitions.lean#L410) (proved). Proved from Mathlib `hasSum_eulerFunction_pentagonal` (pointer); formal version `PowerSeries.WithPiTopology.hasProd_one_sub_X_pow` (pointer).
- [27.14.E5](https://dlmf.nist.gov/27.14.E5): [`DLMF.NumberTheory.pentagonal_pm`](DLMF/NumberTheory/Partitions.lean#L402) (proved). Mathlib's `pentagonal k = (k(3k - 1)/2).toNat`, `k ∈ ℤ` (pointer).
- [27.14.E6](https://dlmf.nist.gov/27.14.E6): [`DLMF.NumberTheory.partitionFunction_recursion`](DLMF/NumberTheory/Partitions.lean#L428) (proved). The sum is finite: terms with `k > n` vanish.
- [27.14.E7](https://dlmf.nist.gov/27.14.E7): [`DLMF.NumberTheory.partitionFunction_sigma_recursion`](DLMF/NumberTheory/Partitions.lean#L437) (proved).
- [27.14.E8](https://dlmf.nist.gov/27.14.E8): [`DLMF.NumberTheory.partitionFunction_isEquivalent`](DLMF/NumberTheory/Partitions.lean#L469) (admitted). The values `p(10)`, `p(100)`, `p(200)` in the prose are excluded (numerical).
- [27.14.E9](https://dlmf.nist.gov/27.14.E9): [`DLMF.NumberTheory.partitionFunction_rademacher`](DLMF/NumberTheory/Partitions.lean#L490) (admitted).
- [27.14.E10](https://dlmf.nist.gov/27.14.E10): [`DLMF.NumberTheory.rademacherA`](DLMF/NumberTheory/Partitions.lean#L484) (definition).
- [27.14.E11](https://dlmf.nist.gov/27.14.E11): [`DLMF.NumberTheory.dedekindSum_eq`](DLMF/NumberTheory/Partitions.lean#L476) (proved). `s(h, k)` is the project's `DLMF.Weierstrass.dedekindSum` (DLMF 23.18.7), reused by `rfl`.
- [27.14.E12](https://dlmf.nist.gov/27.14.E12): [`DLMF.NumberTheory.eta_eq_prod`](DLMF/NumberTheory/Partitions.lean#L502) (proved). Mathlib's `ModularForm.eta` (pointer).
- [27.14.E13](https://dlmf.nist.gov/27.14.E13): [`DLMF.NumberTheory.eta_eq_eulerReciprocal`](DLMF/NumberTheory/Partitions.lean#L513) (proved).
- [27.14.E14](https://dlmf.nist.gov/27.14.E14): [`DLMF.NumberTheory.eta_transform`](DLMF/NumberTheory/Partitions.lean#L523) (admitted). `ε = exp(πi((a + d)/(12c) - s(d, c)))`, principal square root; equivalent to DLMF 23.18.5 (`DLMF.Weierstrass.eta_smul`, admitted there) since `s(-d, c) = -s(d, c)` for `(c, d) = 1`. Checked numerically.
- [27.14.v](https://dlmf.nist.gov/27.14.v): [`DLMF.NumberTheory.exists_partition_congruence`](DLMF/NumberTheory/Partitions.lean#L543) (admitted); [`DLMF.NumberTheory.partitionFunction_mod_thirteen`](DLMF/NumberTheory/Partitions.lean#L550) (admitted); [`DLMF.Partitions.ramanujan_mod_five`](DLMF/Partitions.lean#L47) (admitted); [`DLMF.Partitions.ramanujan_mod_seven`](DLMF/Partitions.lean#L52) (admitted); [`DLMF.Partitions.ramanujan_mod_eleven`](DLMF/Partitions.lean#L57) (admitted). Ramanujan's congruences mod 5, 7, 11 are the AAR declarations `DLMF.Partitions.ramanujan_mod_five/seven/eleven` (admitted, tagged in DLMF/Partitions.lean); Ono's theorem and the example mod 13 admitted.
- [27.14.E15](https://dlmf.nist.gov/27.14.E15): [`DLMF.NumberTheory.hasSum_partitionFunction_five`](DLMF/NumberTheory/Partitions.lean#L536) (admitted).
- [27.14.vi](https://dlmf.nist.gov/27.14.vi): [`DLMF.NumberTheory.isMultiplicativeFn_ramanujanTau`](DLMF/NumberTheory/Partitions.lean#L706) (proved); [`DLMF.NumberTheory.LehmerConjecture`](DLMF/NumberTheory/Partitions.lean#L724) (definition). Multiplicativity admitted. Lehmer's conjecture is open: `LehmerConjecture` is a `Prop` definition only (conjecture: not acquired as a theorem); Lehmer's verification bound is excluded (numerical).
- [27.14.E16](https://dlmf.nist.gov/27.14.E16): [`DLMF.NumberTheory.discriminantDLMF`](DLMF/NumberTheory/Partitions.lean#L558) (definition); [`DLMF.NumberTheory.discriminantDLMF_eq`](DLMF/NumberTheory/Partitions.lean#L562) (proved). DLMF's `Δ = (2π)¹² η²⁴`; Mathlib's `ModularForm.discriminant` is `η²⁴` (partial, pointer).
- [27.14.E17](https://dlmf.nist.gov/27.14.E17): [`DLMF.NumberTheory.discriminantDLMF_transform`](DLMF/NumberTheory/Partitions.lean#L567) (proved). Stronger than DLMF: proved for every `𝒜 ∈ SL(2, ℤ)` (DLMF: `c > 0`) from Mathlib's `CuspForm.discriminant` (pointer).
- [27.14.E18](https://dlmf.nist.gov/27.14.E18): [`DLMF.NumberTheory.ramanujanTau`](DLMF/NumberTheory/Partitions.lean#L581) (definition); [`DLMF.NumberTheory.hasSum_ramanujanTau`](DLMF/NumberTheory/Partitions.lean#L586) (proved). `τ(n)` is the `n`th coefficient of `X · pentagonalSeries²⁴ ∈ ℤ⟦X⟧`; the analytic identity is admitted.
- [27.14.E19](https://dlmf.nist.gov/27.14.E19): [`DLMF.NumberTheory.ramanujanTau_mul`](DLMF/NumberTheory/Partitions.lean#L713) (proved).
- [27.14.E20](https://dlmf.nist.gov/27.14.E20): [`DLMF.NumberTheory.ramanujanTau_modEq`](DLMF/NumberTheory/Partitions.lean#L729) (proved). Congruence in `ℤ` modulo 691.
## Prose, informal and excluded items

- [§27.1](https://dlmf.nist.gov/27.1) Special Notation: notation only (no formulas); the
  conventions are recorded above.
- [27.2.ii](https://dlmf.nist.gov/27.2.ii) Tables 27.2.1 (the first 100 primes) and 27.2.2
  (`φ(n)`, `d(n)`, `σ(n)` for `n ≤ 52`): 27.2.T1, 27.2.T2 excluded: numerical.
- [27.13.i](https://dlmf.nist.gov/27.13.i) Introduction: informal description of additive
  number theory; not acquired.
- 27.13(iv): the remark that exact formulas for `r_k(n)` exist for `k = 3, 5, 7, …` is
  informal; not acquired.
- 27.14(iii): the values `p(10) = 42`, `p(100)`, `p(200)` excluded: numerical. 27.14(vi):
  Lehmer's verification bound for `τ(n) ≠ 0` excluded: numerical. 27.12: the record largest
  known (Mersenne) prime excluded: numerical.
- [§27.15](https://dlmf.nist.gov/27.15) Chinese Remainder Theorem: excluded: application. The
  theorem itself is in Mathlib: `Nat.chineseRemainder` and `ZMod.chineseRemainder` (pointers
  under ID 27.15 in MathlibCoverage).
- [§27.16](https://dlmf.nist.gov/27.16) Cryptography: excluded: application. The RSA scheme
  rests on the Euler–Fermat theorem 27.2.8 (Mathlib `Nat.ModEq.pow_totient`, pointer under ID
  27.16; the project's `pow_totient_modEq_one`).
- [§27.17](https://dlmf.nist.gov/27.17) Other Applications: excluded: application (the
  arithmetic Fourier transform uses the Möbius inversion 27.5.7, acquired).
- [§27.18](https://dlmf.nist.gov/27.18)–[§27.20](https://dlmf.nist.gov/27.20) Methods of
  Computation: excluded: computation. [§27.21](https://dlmf.nist.gov/27.21) Tables: excluded:
  numerical. [§27.22](https://dlmf.nist.gov/27.22) Software: excluded: software.
- Bibliographic paragraphs (references to Apostol, Hardy–Wright, Andrews, …) are not
  acquired.

## Validation

- All ten modules build with `lake build DLMF.NumberTheory.<Module>` and each passes
  `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false` with only `sorry` warnings
  (MathlibCoverage with none). There are no axioms, no `native_decide` and no `sorry` in
  definitions or helper declarations (prefix `n27_`); the finite checks
  `sumSquaresCount_two_five` use `rfl`.
- `#print axioms` over all 212 tagged declarations shows only `propext`, `Classical.choice`,
  `Quot.sound` and (for the 103 admitted or dependent theorems) `sorryAx`; for example
  `discriminantDLMF_transform`, `eulerReciprocal_pentagonal`, `legendreSym_reciprocity`,
  `sigmaC_eq_prod`, `sum_divisors_moebius_mul`, `jacobiTheta_eq_jacobiThetaSeries`,
  `LSeriesHasSum_vonMangoldt` and `moebius_inversion_prod` depend on
  `[propext, Classical.choice, Quot.sound]`.
- The three theorems proved from admissions are `tendsto_nthPrime_div` (27.12.1, from
  27.2.4), `sum_divisors_moebius_pow` (27.6.7, from 27.6.8) and `waringBigG_le_waringSmallG`
  (§27.13(iii), from Hilbert's theorem).
- DLMF/Partitions.lean received only the four attribute lines `@[dlmf 27.14.E3]` and
  `@[dlmf 27.14.v]`; DLMF.lean, the lakefile and the other ledgers are unchanged.
