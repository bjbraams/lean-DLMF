# TauCeti reuse review and implementation

Reviewed and implemented 2026-10-04 against the pinned source and compiled declarations.

## Setup and scope

TauCeti is an explicit Lake dependency at
`a780c7ad6beb23f60a17351a492d177878020ad5`. Lean remains `v4.35.0-rc3` and Mathlib
remains `5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`. The shared `.lake` symlink and
`.lake/build-DLMF` are unchanged. The policy in [AGENTS.md](AGENTS.md) is
**Mathlib → pinned TauCeti → local code**.

The review covered the 97 Lean files under `DLMF/`. All six selected recommendations
have now been implemented. Existing theorem statements and hypotheses are preserved.
Three admitted proofs are complete, reducing the source admissions from 385 to 382.
The remaining admissions have not received a new comprehensive correctness audit.

## 1. Probabilists’ Hermite orthogonality — implemented

[DLMF/OrthogonalPolynomials/Integrals.lean](DLMF/OrthogonalPolynomials/Integrals.lean)
now proves `hermite_orthogonality` using
`TauCeti.integral_hermite_mul_hermite_mul_gaussian`, imported from
`TauCeti.Analysis.SpecialFunctions.Hermite.Orthogonality`.
The short adapter changes only the presentation of the exponent and the order of
factors. The local physicists’ polynomial API and its integration helpers remain
available for their other uses.

## 2. Polynomial Gaussian integrability — implemented

The same file proves `integrable_eval_mul_exp_neg_sq` directly by
`TauCeti.integrable_eval_mul_exp_neg_sq`, from
`TauCeti.Probability.Distributions.Gaussian.PolynomialMemLp`.
The local name is retained for callers. The adjacent power-integrability theorem
continues to use Mathlib directly.

## 3. Real Euler beta integral — implemented

[DLMF/Gamma/BetaFunction.lean](DLMF/Gamma/BetaFunction.lean) now proves
`DLMF.Gamma.real_betaIntegral` using `TauCeti.integral_rpow_mul_one_sub_rpow`
and unfolds Mathlib's `ProbabilityTheory.beta` to obtain the gamma quotient.
The import is `TauCeti.Analysis.SpecialFunctions.Beta`. Complex beta integrals
and the local changes of variables retain their existing generality.

## 4. Real error-function interfaces — implemented

[DLMF/Confluent/Basic.lean](DLMF/Confluent/Basic.lean) imports
`TauCeti.Analysis.SpecialFunctions.Erf` and adds:

```lean
erf_ofReal (x : ℝ) : erf x = (TauCeti.Real.erf x : ℂ)
erfc_ofReal (x : ℝ) : erfc x = (TauCeti.Real.erfc x : ℂ)
```

These proved identities connect the local complex functions to TauCeti's real
bounds, monotonicity, derivative and limit API. The complex definitions remain
unchanged. Individual transfers of all those real properties have not been added;
callers can use the identities where needed.

The related real incomplete-gamma development remains a separate opportunity.
`TauCeti.Analysis.SpecialFunctions.IncompleteGamma` provides
`ofReal_lowerIncGamma_eq_partialGamma` for positive shape and nonnegative
argument. The project's `lowerIncompleteGamma` has complex parameters and is defined using
`kummerM`; TauCeti's real definition is zero for nonpositive shape or argument.
A bridge on the appropriate domain still needs a proof. There is no claim of
unrestricted equality of those definitions.

## 5. Hermite Fourier eigenfunctions — both admissions resolved

[Integrals.lean](DLMF/OrthogonalPolynomials/Integrals.lean) now proves
`hermitePolynomialH_fourier_eigenfunction` and `hermite_fourier_eigenfunction` using
`TauCeti.fourier_twoPiHermiteFunction` from
`TauCeti.Analysis.SpecialFunctions.Hermite.Function.Fourier.Basic`.

The helper `hermiteFunction_integral` converts Mathlib's negative `2π` Fourier
phase to the positive unit-frequency phase, using dilation and Hermite parity.
The helpers `hermitePolynomialH_envelope` and `hermite_envelope` identify the two local
unnormalized polynomial envelopes with TauCeti's normalized Hermite function.
The probabilists’ convention additionally requires dilation by `√2`.
Neither proof uses an admitted local identity. Both original statements,
normalizing constants and DLMF tags are preserved.

## 6. Compact-support Parseval — admission resolved

[DLMF/OrthogonalPolynomials/General.lean](DLMF/OrthogonalPolynomials/General.lean)
now proves `orthogonal_polynomials_parseval` using
`TauCeti.Analysis.InnerProductSpace.PolynomialCompleteness` and its imported
weighted-basis API, followed by Mathlib's `HilbertBasis.tsum_inner_mul_inner`.

The proof derives finiteness of the measure from integrability of the constant
polynomial. Compact support then makes the required exponential moment finite.
Exact degrees and the positive squared norms supply completeness and normalization.
With weight one, `TauCeti.hilbertBasisOfOrthogonalSystem` gives the basis in the
original `L²(μ)`, and its coefficient formula yields the stated raw integrals.
No probability-measure or exponential-moment assumption has been added to the
public theorem. The proof does not assume `a ≤ b` beyond what follows from the
existing orthogonality and support hypotheses.

## Coverage of the remaining areas

“No direct replacement found” below is the result of this source review, not a
claim that no useful supporting lemma exists anywhere in TauCeti.

| Area | Finding at the pinned revision |
| --- | --- |
| Gamma (23 submodules) | Real beta replacement above. Real incomplete gamma and Dirichlet integrals are useful adjacent theory. Complex Gamma, Barnes G, q-Gamma, digamma and asymptotic developments have no identified direct replacements. |
| Hypergeometric (20) | Keep the current Mathlib-backed series and local complex cut-plane continuation, transformations and exceptional-parameter theory. No matching TauCeti replacement identified. |
| Confluent (15) | Error-function bridge above; real incomplete-gamma bridge is further work. Retain complex Kummer, Tricomi and Whittaker definitions and continuation. |
| Bessel (5) | No matching TauCeti replacement for the local complex Bessel developments identified. Continue preferring existing Mathlib results. |
| OrthogonalPolynomials (18) | Strongest reuse area: items 1, 2, 5 and 6. TauCeti's Hermite and weighted `L²` work does not by itself replace all Jacobi, Laguerre, Wilson, Hahn, q-polynomial or parameter-limit results. |
| Selberg (2) | TauCeti's real Dirichlet and positive-definite-matrix multivariate Gamma integrals are related, but not the complex Selberg/Vandermonde statements here. |
| SphericalHarmonics (2) | General harmonic/PDE support is adjacent; no checked replacement for the local spherical-harmonic identities identified. |
| QSeries (2) | No direct replacement for the basic hypergeometric identities identified. |
| Partitions (single file) | Partition foundations exist upstream, but no replacement for the three admitted Ramanujan congruences was identified. |
| Bailey (single file) | No direct replacement for the Bailey-pair/chain statements identified. |

The complex simplex integrals in `Gamma/Multidimensional.lean` also require more
than TauCeti's real positive-parameter Dirichlet theory. A real specialization
would be useful but would not discharge the existing complex statements.

## Validation and remaining work

- `lake build`: passed, 3,983 jobs, with existing admission warnings.
- `lake env lean` for each of the four changed Lean modules: passed.
- An axiom audit importing the full `AAR` library checked all eleven new or
  changed public results, including the three formerly admitted theorems. Each
  depends only on `propext`, `Classical.choice` and `Quot.sound`; none uses `sorryAx`.
- `git diff --check`: passed.
- `rg -n '\bsorry\b' AAR -g '*.lean'`: 382 standalone admissions remain in 54 files,
  plus one documentation mention. No new admission or axiom was introduced.

No existing theorem statement or assumption changed, and no additional false
statement was identified. [REVIEW.md](REVIEW.md) contains an earlier mathematical
review and inventory; its 385-admission count predates these three completed proofs.
See [CREDITS.md](CREDITS.md) for attribution to the imported work.

## Proof pass of 2026-10-05

A second pass searched TauCeti per topic before attempting the admissions. TauCeti has
little further special-function material at the pinned revision. Hermite parity
(`Polynomial.hermite_aeval_neg`) and Gaussian integrability
(`integrable_aeval_mul_gaussian`) were adopted for the Hermite cosine and sine transforms.
TauCeti's complex binomial series and Hermite generating function were checked; the
project's existing `hasSum_pochhammer_div_factorial` already covers the former, and the latter
did not match a remaining admission. There is nothing for polygamma, Barnes G, q-series,
partition congruences, the Jacobi triple product, Hasse–Davenport or the
`SU(2) → SO(3)` cover.

35 admissions were proved, all depending only on `propext`, `Classical.choice` and
`Quot.sound`:

- Gamma: `polygamma_one`, `polygamma_one_div_two`, `polygamma_multiplication`,
  `digamma_half_diff`, `digamma_one_add_zeta`, `digamma_one_add_odd_zeta`,
  `sum_alternating_trigamma`, `digamma_add_euler`, `digamma_gauss`, `digamma_binet`.
- Orthogonal polynomials: `hermite_even_cosine_transform`, `hermite_odd_sine_transform`,
  `ultrasphericalPolynomial_cos_sum`, `ultrasphericalPolynomial_finite_sum`, the four quadratic transformations
  18.7.13–18.7.16, `ultrasphericalPolynomial_convolution`, `ultrasphericalPolynomial_geometric_convolution`,
  `legendre_convolution`, `ultrasphericalPolynomial_generating_function`,
  `ultrasphericalPolynomial_weighted_generating_function`, `legendre_generating_function`,
  `laguerrePolynomialL_addition`, `hermitePolynomialH_even_convolution`,
  `jacobi_regularized_generating_function`, `laguerrePolynomialL_bessel_generating_function`,
  `hermitePolynomialH_half_factorial_generating_function`, `ultrasphericalPolynomial_bound_at_one`,
  `meixnerPollaczek_generating_function`, `pollaczek_finite_sum`,
  `pollaczek_generating_function`, `charlier_limit_hermite`, `besselPolynomial_recurrence`.

New modules: `BinomialSeries.lean` (the formal series `(1 - uX)^{-a}(1 - X/u)^{-b}`, its
differential equation and three-term recurrence), `GegenbauerSeries.lean` and
`LaguerreSeries.lean`. The Gegenbauer sums 18.5.10–18.5.11 and the quadratic
transformations need the recurrences of `Differential.lean`, which imports
`Explicit.lean`. They were therefore moved from `Explicit.lean` to
`GegenbauerSeries.lean` with unchanged statements. `aeval_hermitePolynomialH_succ_succ` moved
from `Integrals.lean` to `Classical.lean` so that `Hahn.lean` can use it. No theorem
statement or hypothesis was changed, and no false statement was found.
