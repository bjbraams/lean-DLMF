# Duverney synopsis acquisition ledger

Source: Daniel Duverney, *An Introduction to Hypergeometric Functions*, Birkhäuser, 2024.
The specifications and book numbering are in [SYNOPSIS-Duverney.md](SYNOPSIS-Duverney.md).
This ledger maps all **197** stable entries, including all 53 labelled theorems, seven lemmas,
Corollary B.14, definitions and the additional substantial equations.

The lookup order is pinned Mathlib, pinned TauCeti, then DLMF. The pins are Mathlib
`1b1ccf4b088b32fa3f23f2de1127433254a81e1e`, TauCeti
`396c3bd971e9722aa8656231760e710fe641d8cf`, and Lean `v4.36.0-rc2`.
No pin or synopsis text was changed.

“Existing” records an exact declaration or an elementary derivation whose substitutions are
specified. It does not imply that the declaration is proved. “New target” is an actual Lean
statement, with concrete mathematical expressions and domain hypotheses. The declaration index
below distinguishes proved declarations, direct admissions and dependence on admissions using
Lean's transitive `#print axioms` output. Some straightforward derivations are recorded instead
of adding redundant public wrappers; three checked Lean examples are included at the end.
Definitions and their defining equations are proved; every newly admitted result remains in
the theorem layer. In particular, conditional alternating series use ordered finite partial sums,
not the unconditional `HasSum` predicate or a totalized `tsum` at the boundary.

## Chapter 1

### DU-1.01 — Gamma definition and smoothness (1.1–1.3, p. 1).

Existing: Mathlib `Real.GammaIntegral_convergent`, `Real.Gamma_eq_integral`,
`Real.Gamma_pos_of_pos`; smoothness follows from `DLMF.Gamma.analyticAt_Gamma` away from the
nonpositive integers. Every logarithmic moment and the nth derivative integral are
`DLMF.Gamma.integrableOn_log_pow_mul_Gamma` and `DLMF.Gamma.iteratedDeriv_Gamma` in
`Gamma/IntegralRepresentations/FrullaniAndMoments.lean`.

The named declarations have no `sorryAx` dependency.

### DU-1.02 — Recurrence and extension (1.4–1.8, p. 2).

Existing: Mathlib `Real.Gamma_one`, `Real.Gamma_add_one`, `Real.Gamma_nat_eq_factorial`,
`Complex.Gamma_add_nat_div_Gamma_eq` and `Complex.Gamma_ofReal`. The extension formula and
independence of N are algebraic rearrangements of the last identity; smoothness follows from
`DLMF.Gamma.analyticAt_Gamma`.

The named declarations have no `sorryAx` dependency.

### DU-1.03 — Generalized binomial coefficients (1.11–1.15, p. 3).

Existing: Mathlib `Ring.choose`, `ascPochhammer`, `descPochhammer`;
`Ring.choose_eq_descPochhammer_div` in `DLMFMathlib/RingTheory/Binomial.lean`,
`DLMF.Gamma.pochhammer_neg_eq`, `Complex.Gamma_add_nat_div_Gamma_eq`. These give both binomial
products and the Gamma quotient, with the precise regular-parameter assumption.

The named declarations have no `sorryAx` dependency.

### DU-1.04 — Beta definition and Theorem 1.5 (1.16–1.17, pp. 3–4).

Existing: Mathlib `Complex.betaIntegral`, `Complex.betaIntegral_convergent`,
`Complex.betaIntegral_symm`, `Complex.betaIntegral_eq_Gamma_mul_div`. Integer values follow by
`Real.Gamma_nat_eq_factorial` (or its complex counterpart); the real form is obtained by
inclusion, preserving positivity of both parameters.

The named declarations have no `sorryAx` dependency.

### DU-1.05 — Gaussian integral (1.9–1.10, 1.20, pp. 2, 5).

Existing: Mathlib's Gaussian integral API and `Real.Gamma_one_half_eq`; the positive-half-line
Gaussian integral is `integral_gaussian_Ioi` specialized to coefficient one. The Gamma value is
also obtained from duplication at one half.

The named declarations have no `sorryAx` dependency.

### DU-1.06 — Theorem 1.8: duplication (1.21, p. 5).

Existing: Mathlib `Real.Gamma_mul_Gamma_add_half` and `Complex.Gamma_mul_Gamma_add_half`.
Rearranging the factor `2^(2x-1)/sqrt π` gives the source normalization, including all real
parameters permitted by the source.

The named declarations have no `sorryAx` dependency.

### DU-1.07 — Theorem 1.9: Gauss limit (1.23, p. 5).

Existing: Mathlib `Real.GammaSeq_tendsto_Gamma` and `Complex.GammaSeq_tendsto_Gamma`, together
with the explicit `Complex.GammaSeq` product. Source N starts sufficiently far from zero; deletion
of finitely many initial indices does not alter the limit.

The named declarations have no `sorryAx` dependency.

### DU-1.08 — Gamma-ratio asymptotic (1.25–1.26, p. 6).

Existing: `DLMF.Gamma.Gamma_ratio_power` and `DLMF.Gamma.tendsto_Gamma_add_div_Gamma_mul_cpow` in
`Gamma/Asymptotics/Stirling.lean`, plus Mathlib's Gamma–Pochhammer quotient. Multiplication by the
fixed nonzero Gamma ratio gives the stated Pochhammer equivalent.

The named declarations have no `sorryAx` dependency.

### DU-1.09 — Euler constant and Weierstrass product (1.27–1.34, pp. 7–8).

Existing: Mathlib `Real.eulerMascheroniConstant` and its harmonic-minus-log limit API;
`DLMF.Gamma.Real.one_div_Gamma_eq_tprod`, `DLMF.Gamma.Real.tendsto_weierstrassGamma_prod` and
`DLMF.Gamma.multipliable_weierstrassGammaTerm` in `Gamma/Basic.lean`. The reciprocal is continuous
everywhere by Mathlib `Complex.differentiable_one_div_Gamma` and real restriction. The integral is
`DLMF.Gamma.eulerMascheroni_integrals` in `FrullaniAndMoments.lean`.

The named declarations have no `sorryAx` dependency.

### DU-1.10 — Theorem 1.13: reflection (1.35, p. 9).

Existing: Mathlib `Real.Gamma_mul_Gamma_one_sub` and `Complex.Gamma_mul_Gamma_one_sub`. They use
Lean's totalized Gamma and division; restricting away from integers gives exactly the source.

The named declarations have no `sorryAx` dependency.

### DU-1.11 — Sine product (1.36, p. 9).

Existing: Mathlib `HasProdLocallyUniformlyOn_euler_sin_prod` in
`Analysis/SpecialFunctions/Trigonometric/Cotangent.lean`, and its sine-product result. Real
restriction and rescaling z=x/π give the displayed product and local uniform convergence.

The named declarations have no `sorryAx` dependency.

### DU-1.12 — Lemma 1.15: integer sine polynomials (pp. 9–10).

New: `Polynomial.integerSinePolynomial` and its `Polynomial.integerSinePolynomial_def`,
`Polynomial.natDegree_integerSinePolynomial`, `Polynomial.integerSinePolynomial_eval_zero`,
`Polynomial.derivative_integerSinePolynomial_eval_zero`,
`Polynomial.integerSinePolynomial_eval_sin` in
`DLMFMathlib/Analysis/SpecialFunctions/Trigonometric/IntegerSinePolynomial.lean`. The explicit
integer coefficients are part of the definition; evaluation at zero is proved,
degree/derivative/trigonometric evaluation are admitted targets.

Admission status: `Polynomial.natDegree_integerSinePolynomial`,
`Polynomial.derivative_integerSinePolynomial_eval_zero`,
`Polynomial.integerSinePolynomial_eval_sin`.

### DU-1.13 — Reciprocal gamma at poles (1.47–1.50, p. 12).

Existing: Mathlib `Complex.differentiable_one_div_Gamma`;
`DLMF.Gamma.differentiable_recipGammaDeriv` and `DLMF.Gamma.recipGammaDeriv_one_neg_nat` in
`Gamma/RecipGammaDeriv.lean`. The reflection formula on x<1 follows by Mathlib Gamma reflection
and continuity at the nonpositive integers. Repeated differentiability gives the C∞ assertion.

The named declarations have no `sorryAx` dependency.

### DU-1.14 — Bohr–Mollerup characterization (Note 1.5, p. 12).

Existing: Mathlib `Real.eq_Gamma_of_log_convex` in
`Analysis/SpecialFunctions/Gamma/BohrMollerup.lean`. Its positivity, normalization, recurrence and
log-convexity hypotheses match the synopsis.

The named declarations have no `sorryAx` dependency.

### DU-1.15 — Beta substitutions and triplication (Exercises 1.14–1.17, pp. 13–14).

Existing: trigonometric beta substitutions in `DLMF.Gamma.beta_sin_cos`,
`DLMF.Gamma.integral_rpow_div_one_add` in `PrymAndOscillatory.lean`, and
`DLMF.Gamma.Real.Gamma_mul_nat` in `Gamma/Multiplication.lean` at m=3. The first source integral
follows by beta at parameters (α+1)/2 and 1/2, then duplication; the second is the explicit
half-line integral; the third is the multiplication theorem at three.

The named declarations have no `sorryAx` dependency.

### DU-1.16 — Oscillatory gamma integral (Exercise 1.18, (1.53–1.54), p. 14).

Existing: `DLMF.Gamma.Gamma_laplace_power`/`DLMF.Gamma.integral_cpow_mul_exp_neg_mul_Ioi` in
`HankelAndGaussian.lean` at Laplace parameter 1-ix. The conditional oscillatory limit combines
`DLMF.Gamma.tendsto_integral_rpow_mul_cos` and `DLMF.Gamma.tendsto_integral_rpow_mul_sin` in
`PrymAndOscillatory.lean`; these use ordered finite-integral limits, not absolute integrability.

The named declarations have no `sorryAx` dependency.

## Chapter 2

### DU-2.01 — Digamma definition and recurrence (2.1–2.2, p. 25).

Existing definition `DLMF.Gamma.Real.digamma` and Mathlib `Complex.digamma_apply_add_one`. New
proved foundational bridges in `Gamma/Basic/RealDigamma.lean`:
`DLMF.Gamma.digamma_ofReal_of_not_neg_nat`, `DLMF.Gamma.Real.hasDerivAt_log_abs_Gamma`,
`DLMF.Gamma.Real.digamma_add_one_of_not_neg_nat`. They cover every regular real parameter,
including negative intervals; the older x>0-only bridge is not counted as full coverage. These
three adapter proofs were checked with Lean and contain no sorryAx dependency.

The named declarations have no `sorryAx` dependency.

### DU-2.02 — Series and integer values (2.4–2.5, p. 26).

Existing: `DLMF.Gamma.Real.digamma_eq_tsum`, `DLMF.Gamma.Real.hasDerivAt_digamma` and
`DLMF.Gamma.Real.trigamma_eq_tsum` in `Gamma/Digamma.lean`; `DLMF.Gamma.polygamma_add_one` gives
the continued recurrences. Positivity of the trigamma series yields monotonicity on the positive
half-line.

The named declarations have no `sorryAx` dependency.

### DU-2.03 — Reflection and cotangent partial fractions (2.6–2.7, pp. 26–27).

Existing: `DLMF.Gamma.polygamma_reflection` at order zero and the local digamma reflection API;
Mathlib `cot_series_rep'` plus `Complex.hasSum_cotTerm` in
`DLMFMathlib/.../Trigonometric/PartialFractions.lean`. Rescale by π for the displayed cotangent
expansion.

The named declarations have no `sorryAx` dependency.

### DU-2.04 — Pochhammer and reciprocal-gamma derivatives (2.8–2.10, p. 27).

Existing: `DLMF.Hypergeometric.hasDerivAt_pochhammer` and
`DLMF.Hypergeometric.deriv_recip_Gamma_eq` in `Hypergeometric/ConnectionFormulas.lean`; at poles
`DLMF.Gamma.recipGammaDeriv_one_neg_nat` gives the separate value. The upper-parameter exclusion
is retained for the literal digamma expression.

The named declarations have no `sorryAx` dependency.

### DU-2.05 — Digamma integral representations (2.11–2.14, p. 28).

Existing: `DLMF.Gamma.digamma_gauss`, `DLMF.Gamma.digamma_frullani`,
`DLMF.Gamma.digamma_add_euler_Ioo`, `DLMF.Gamma.digamma_add_euler_Ioi`; special values Mathlib
`Complex.digamma_one`, `Complex.digamma_one_half` and `DLMF.Gamma.deriv_Gamma_one`.

The named declarations have no `sorryAx` dependency.

### DU-2.06 — Lemma 2.4: logarithm integral (2.15, p. 29).

Existing: `DLMF.Gamma.integrableOn_exp_neg_sub_exp_neg_div` and
`DLMF.Gamma.integral_exp_neg_sub_exp_neg_div` in
`Gamma/IntegralRepresentations/DigammaAndBinet.lean`. The integral is absolutely convergent for
x>0.

The named declarations have no `sorryAx` dependency.

### DU-2.07 — Theorem 2.5: Binet formula (2.16–2.17, p. 29).

Existing: `DLMF.Gamma.log_Gamma_binet_exp`, `DLMF.Gamma.log_Gamma_eq_add_binetIntegral`,
`DLMF.Gamma.digamma_eq_log_sub_binetBeta` in `Gamma/IntegralRepresentations/DigammaAndBinet.lean`,
with `DLMF.Gamma.binetBeta` and `DLMF.Gamma.binetIntegral` explicit. Algebraically rewrite the
kernel to match the synopsis.

The named declarations have no `sorryAx` dependency.

### DU-2.08 — Stirling formulas (2.24–2.26, p. 32).

Existing: `DLMF.Gamma.log_Gamma_stirling` and `DLMF.Gamma.hasAsymptoticExpansion_log_Gamma` in
`Gamma/Asymptotics/Stirling.lean`. Their first remainder gives the relative O(1/x) Gamma formula
by exponentiation; restrict x to n+1 and use Gamma factorial values for Stirling's factorial form.
The mere ratio-limit theorem is not counted as the requested quantitative remainder.

The named declarations have no `sorryAx` dependency.

### DU-2.09 — Theorem 2.7: polygamma (2.27–2.29, p. 33).

Existing: `DLMF.Gamma.polygamma_eq_tsum` and `DLMF.Gamma.polygamma_eq_integral` in
`Gamma/Polygamma.lean` and `Gamma/PolygammaHurwitz.lean`. The series applies on all regular
complex arguments; the integral has the source's positive-real assumption.

The named declarations have no `sorryAx` dependency.

### DU-2.10 — Rational series by residues (2.30–2.35, pp. 33–35).

New exact polynomial-residue target `DLMF.Gamma.hasSum_polynomial_div_of_distinct_real_roots` in
`Gamma/PolynomialSeries.lean`, with explicit factorization into all distinct real roots, no
natural-number roots, the degree gap, zero residue sum and the convergent digamma evaluation.
Existing `DLMF.Gamma.hasSum_sum_div_sub` supplies the balanced partial-fraction series step;
repeated poles use `DLMF.Gamma.polygamma_eq_tsum`.

Admission status: `DLMF.Gamma.hasSum_polynomial_div_of_distinct_real_roots`.

### DU-2.11 — Rational trigonometric sums (2.36–2.43, pp. 35–37).

Existing: `DLMF.Elementary.hasSum_csc_sq_partial_fraction` in
`Elementary/Trigonometric/DirectIdentities.lean` and `Complex.hasSum_csc_partial_fraction` in
`DLMFMathlib/.../Trigonometric/PartialFractions.lean`; reindex the absolutely convergent
positive/negative square terms and rescale by π. These supply the bilateral square sum and the
alternating csc expansion.

The named declarations have no `sorryAx` dependency.

### DU-2.12 — Positive Bernoulli numbers (2.45–2.54, pp. 37–39).

Existing: Mathlib `bernoulli_zero`, `bernoulli_one`, Bernoulli recurrence;
`DLMF.BernoulliEuler.bernoulli_two_mul_add_one_eq_zero_and_sign`,
`DLMF.BernoulliEuler.hasSum_bernoulliPolyB_mul_pow_div` at x=0, and
`Complex.hasSum_pi_mul_cot_bernoulli`. The positive b_n convention is the explicit sign (-1)^(n+1)
times the canonical B_(2n); no duplicate sequence is defined.

The named declarations have no `sorryAx` dependency.

### DU-2.13 — Positive Euler numbers (2.55–2.57, pp. 39–40).

Existing: signed canonical `eulerNumber`, `sum_choose_mul_eulerNumber`,
`eulerNumber_eq_zero_of_odd`, and the full-radius
`DLMF.BernoulliEuler.hasSum_eulerNumber_mul_pow_div'` in
`BernoulliEuler/GeneratingFunctions.lean`; positivity and integrality are
`DLMF.BernoulliEuler.eulerNumber_two_mul_add_one_eq_zero_and_sign` and
`DLMF.BernoulliEuler.eulerNumber_eq_two_pow_mul_and_integer`. The positive secant coefficients are
(-1)^n E_(2n), and the source recurrence is the canonical recurrence after deleting odd indices.
Odd integrality follows from `DLMF.BernoulliEuler.eulerNumber_two_mul_modEq_two_pow'` at indices
2n and 0, modulus 2, together with the integer-value theorem and E0=1; positivity then gives the
positive odd source convention. The odd-integrality step was checked by a Lean example using the
modulus-two congruence and Rat.num_intCast.

The named declarations have no `sorryAx` dependency.

### DU-2.14 — Laplace-transform domain (Definition 2.10, (2.58), p. 40).

New: `MeasureTheory.laplaceIntegral`, `MeasureTheory.IsLaplaceTransformable`,
`MeasureTheory.laplaceAbscissa` in `DLMFMathlib/Analysis/Integral/LaplaceDomain.lean`, with proved
defining lemmas, introduction and elimination lemmas.
`MeasureTheory.IsLaplaceTransformable.integrableOn_of_abscissa_lt` is the admitted domain theorem.
The extended-real infimum includes the value -∞ correctly.

Admission status: `MeasureTheory.IsLaplaceTransformable.integrableOn_of_abscissa_lt`.

### DU-2.15 — Basic Laplace transforms (Example 2.11, p. 40).

Existing power transform: Mathlib `Real.integral_rpow_mul_exp_neg_mul_Ioi` and
`DLMFMathlib/.../Asymptotics/Watson.lean`'s `integral_exp_neg_mul_mul_rpow_sub_one`; sine/cosine
transforms: `Complex.integral_cpow_mul_cexp_neg_mul_mul_sin_Ioi`, `...mul_cos_Ioi` in
`DLMFMathlib/Analysis/Integral/LaplaceSine.lean` at a=1; exponential transform: Mathlib
`integral_exp_mul_complex_Ioi`. The logarithm transform is existing
`integral_exp_neg_mul_rpow_sub_one_mul_log` in `DLMFMathlib/Analysis/Asymptotics/WatsonLog.lean`
at s=1, using Gamma(1)=1 and Gamma'(1)=-γ.

The named declarations have no `sorryAx` dependency.

### DU-2.16 — Lemma 2.12: Watson lemma (2.59–2.60, pp. 40–41).

Existing: `hasAsymptoticExpansion_integral_exp_smul` in
`DLMFMathlib/Analysis/Asymptotics/Watson.lean` at μ=1. The exponential growth and local Taylor
bounds imply the required Laplace integrability; its quantitative remainder gives exactly the
O(x^(-N-1)) bound, not merely an asymptotic equivalent.

The named declarations have no `sorryAx` dependency.

### DU-2.17 — Log-gamma expansion (2.66, p. 42).

Existing: `DLMF.Gamma.hasAsymptoticExpansion_log_Gamma` and `DLMF.Gamma.log_Gamma_stirling` in
`Gamma/Asymptotics/Stirling.lean`; specialize the truncation to retain terms through B_(2N). The
zero even-power coefficients improve the displayed remainder to the stated odd inverse power.

The named declarations have no `sorryAx` dependency.

### DU-2.18 — Zeta, eta and lambda (2.67–2.75, pp. 43–44).

Existing definitions and zeta relations: `DLMF.Constants.dirichletEta`,
`DLMF.Constants.dirichletLambda`, `DLMF.Constants.hasSum_zeta`, `DLMF.Constants.dirichletEta_eq`,
`DLMF.Constants.dirichletLambda_eq`, `DLMF.Constants.tendsto_dirichletEta_one`,
`DLMF.Constants.tendsto_riemannZeta_atTop`. New positive-order eta convergence, strict bounds,
value at one and limit: `DLMF.Zeta.Real.alternatingHurwitzZeta_one`,
`DLMF.Zeta.Real.tendsto_sum_alternatingHurwitzZeta`,
`DLMF.Zeta.Real.alternatingHurwitzZeta_one_bounds`,
`DLMF.Zeta.Real.alternatingHurwitzZeta_one_one`,
`DLMF.Zeta.Real.tendsto_alternatingHurwitzZeta_one` in `Zeta/AlternatingHurwitz.lean`. The
existing Constants.dirichletEta is an unconditional tsum and is used only for s>1; the
all-positive eta is the real Lerch value alternatingHurwitzZeta s 1, with actual ordered partial
sums.

Admission status: `DLMF.Zeta.Real.alternatingHurwitzZeta_one`,
`DLMF.Zeta.Real.tendsto_sum_alternatingHurwitzZeta`,
`DLMF.Zeta.Real.alternatingHurwitzZeta_one_bounds`,
`DLMF.Zeta.Real.alternatingHurwitzZeta_one_one`,
`DLMF.Zeta.Real.tendsto_alternatingHurwitzZeta_one`.

### DU-2.19 — Even zeta values and Bernoulli growth (2.76–2.79, pp. 44–45).

Existing: Mathlib even zeta values (Bernoulli formula), `DLMF.Gamma.polygamma_one`, and
`DLMF.BernoulliEuler.bernoulli_two_mul_isEquivalent`. The polygamma value follows by substitution
of the even zeta formula; divide the Bernoulli equivalent by (2k)! and switch to the positive b_k
convention for its growth.

The named declarations have no `sorryAx` dependency.

### DU-2.20 — Hurwitz and alternating Hurwitz functions (2.80–2.85, pp. 45–46).

Existing Hurwitz series and continuation: `DLMF.Zeta.hurwitzZetaComplex`,
`DLMF.Gamma.polygamma_eq_hurwitzZeta`, `DLMF.Gamma.hurwitzZeta_one_half_nat`; the half-shift
relation for arbitrary real s>1 follows by splitting even/odd terms. New
`DLMF.Zeta.Real.alternatingHurwitzZeta`, defining lemma and convergence theorem capture the
positive-order alternating function. Its defining Lerch value and
`DLMF.Zeta.Real.tendsto_sum_alternatingHurwitzZeta` avoid treating conditional convergence as
unconditional HasSum; the latter is separately stated only for s>1. The definition and its proved
defining identity live in `Zeta/Basic/AlternatingHurwitz.lean`; convergence and integrals remain
in the theorem layer.

Admission status: `DLMF.Zeta.Real.tendsto_sum_alternatingHurwitzZeta`.

### DU-2.21 — Dirichlet beta and Euler growth (2.86–2.88, p. 46).

New definition and beta/Hurwitz bridge: `DLMF.Zeta.Real.dirichletBeta`,
`DLMF.Zeta.Real.dirichletBeta_def`, `DLMF.Zeta.Real.hasSum_dirichletBeta`,
`DLMF.Zeta.Real.dirichletBeta_two`. Existing odd beta values:
`DLMF.BernoulliEuler.hasSum_alt_inv_odd_pow_eulerNumber`; existing Euler growth:
`DLMF.BernoulliEuler.eulerNumber_two_mul_isEquivalent`. The n=0 odd value is the Leibniz
arctangent series. Catalan's constant reuses `DLMF.Constants.catalanConstant`. The all-positive
series is `DLMF.Zeta.Real.tendsto_sum_dirichletBeta`; HasSum is restricted to s>1.

Admission status: `DLMF.Zeta.Real.hasSum_dirichletBeta`, `DLMF.Zeta.Real.dirichletBeta_two`,
`DLMF.Zeta.Real.tendsto_sum_dirichletBeta`.

### DU-2.22 — Mellin integral representations (2.89–2.90, p. 47).

Existing nonalternating Mellin integral: `DLMF.Gamma.Gamma_mul_hurwitzZeta_eq_integral`. New
alternating convergence and formula: `DLMF.Zeta.Real.integrableOn_alternatingHurwitzZeta_kernel`,
`DLMF.Zeta.Real.alternatingHurwitzZeta_eq_integral`. Both retain a>0 and the distinct order ranges
s>1 versus s>0.

Admission status: `DLMF.Zeta.Real.integrableOn_alternatingHurwitzZeta_kernel`,
`DLMF.Zeta.Real.alternatingHurwitzZeta_eq_integral`.

### DU-2.23 — Bernoulli polynomials (Exercise 2.13, (2.94), pp. 50–51).

Existing: Mathlib `Polynomial.bernoulli`, its coefficient/degree, derivative, reflection and
finite-difference API in `NumberTheory/BernoulliPolynomials.lean`;
`DLMF.BernoulliEuler.bernoulliPolyB_eq_sum`,
`DLMF.BernoulliEuler.hasSum_bernoulliPolyB_mul_pow_div`; the Mathlib power-sum formula is
Faulhaber. Canonical Bernoulli uses B1=-1/2, matching the synopsis.

The named declarations have no `sorryAx` dependency.

### DU-2.24 — Euler polynomials (Exercise 2.14, (2.95), p. 51).

Existing: `Polynomial.euler`, `Polynomial.derivative_euler_succ`,
`Polynomial.euler_comp_one_sub_X`, `Polynomial.euler_eval_add_one_add`, `eulerNumber` in
`DLMFMathlib/NumberTheory/EulerPolynomials.lean`; `DLMF.BernoulliEuler.eulerPolyE_eq_sum` and the
generating-function API. The centered formula follows by Taylor expansion at 1/2 with the defining
Euler-number relation; odd and even endpoint values use the parity/translation identities.

The named declarations have no `sorryAx` dependency.

### DU-2.25 — Euler–Maclaurin on a unit interval (Exercise 2.16, p. 51).

The exact local-regularity one-cell formula is newly acquired by the Temme audit as
`euler_summation_one_cell` in `DLMFMathlib/Analysis/Summation/PolynomialRemainders.lean`.
Instantiate its derivative jet by iterated derivatives within [0,1], and k=2N+1. Splitting off
j=1, vanishing of odd Bernoulli numbers above one, and solving for the integral give precisely the
synopsis remainder and sign. The older `integral_eq_sum_bernoulliFun_add` in
`DLMFMathlib/Analysis/EulerMaclaurin.lean` requires global ContDiff and is recorded only as
partial regularity coverage. No independent duplicate target is introduced.

Admission status: `euler_summation_one_cell`.

### DU-2.26 — Catalan special values (Exercise 2.12, p. 50).

Existing: `DLMF.Constants.trigamma_one_quarter` and `DLMF.Constants.trigamma_three_quarters` in
`Constants/Catalan.lean`. These use the canonical Catalan constant and give both signs directly.

The named declarations have no `sorryAx` dependency.

## Chapter 3

### DU-3.01 — Series and finite convention (3.1–3.6, pp. 69–70).

Existing canonical definitions: `DLMF.Hypergeometric.generalizedHypergeometricCoeff`,
`DLMF.Hypergeometric.generalizedHypergeometric`,
`DLMF.Hypergeometric.generalizedHypergeometricTruncated`,
`DLMF.Hypergeometric.LowerParametersRegular`, `DLMF.Hypergeometric.IsTerminating` in
`GeneralizedHypergeometric/Basic/ParametersAndSeries.lean` and `PrincipalContinuation.lean`. The
regularized principal continuation supplies the ordinary function for globally regular lower
parameters. For a later lower pole, use the explicitly truncated function, not Gamma(lower) times
a regularized value (which has a different totalization).

The named declarations have no `sorryAx` dependency.

### DU-3.02 — Convergence radii and endpoints (p. 70; Exercises 3.10–3.11, p. 88).

Existing: `DLMF.Hypergeometric.generalizedHypergeometric_entire`,
`DLMF.Hypergeometric.generalizedHypergeometric_radius_one`,
`DLMF.Hypergeometric.generalizedHypergeometric_radius_zero`,
`DLMF.Hypergeometric.generalizedHypergeometric_diverges_nonzero`,
`DLMF.Hypergeometric.generalizedHypergeometric_unit_absolute_iff`,
`DLMF.Hypergeometric.generalizedHypergeometric_unit_conditional`,
`DLMF.Hypergeometric.generalizedHypergeometric_unit_diverges`,
`DLMF.Hypergeometric.generalizedHypergeometric_one_converges_iff` in
`GeneralizedHypergeometric/AnalyticProperties.lean`. These distinguish termination, absolute
convergence, ordered conditional convergence and divergence; the negative-one iff combines the
conditional and divergence results.

The named declarations have no `sorryAx` dependency.

### DU-3.03 — Theorem 3.3: coefficient-ratio recognition (3.10–3.11, p. 71).

New admitted target `DLMF.Hypergeometric.eq_generalizedHypergeometric_of_coefficient_recurrence`
in `GeneralizedHypergeometric/BookSeries.lean`. It keeps the original radius R in the hypothesis
and conclusion, the nonzero scale A, and all denominator factors; no incorrect extra scaling of
the convergence interval is imposed.

Admission status: `DLMF.Hypergeometric.eq_generalizedHypergeometric_of_coefficient_recurrence`.

### DU-3.04 — Elementary cases (3.5, 3.7–3.19, pp. 70–73).

New canonical identities `DLMF.Hypergeometric.generalizedHypergeometric_empty_empty`,
`DLMF.Hypergeometric.generalizedHypergeometric_singleton_empty`,
`DLMF.Hypergeometric.mul_regularizedGaussHypergeometric_one_one_two` in
`GeneralizedHypergeometric/BookSeries.lean` cover exp, the full continued binomial formula and the
full continued logarithm formula. Existing `DLMF.Bessel.regularized0F1_half_eq_cos` and
`DLMF.Bessel.regularized0F1_three_halves_eq_sinc`, with Gamma half-integer values, cover cos and
sin. The raw Mathlib Gauss series identities only cover their convergence disk and were not
counted as continuation outside it.

Admission status: `DLMF.Hypergeometric.generalizedHypergeometric_empty_empty`,
`DLMF.Hypergeometric.generalizedHypergeometric_singleton_empty`,
`DLMF.Hypergeometric.mul_regularizedGaussHypergeometric_one_one_two`.

### DU-3.05 — Sine integral (3.18–3.20, Exercise 3.3, pp. 73–74, 87).

Existing definition and series: `DLMF.Confluent.Real.sinIntegral`,
`DLMF.Confluent.Real.hasSum_sinIntegral`; hypergeometric formula
`DLMF.Hypergeometric.Real.sinIntegral_eq_regularizedHGFun` in `Hypergeometric/SpecialCases.lean`.
Existing all-order auxiliary F/G expansions in `ExpIntegrals/Asymptotics.lean`, combined with the
defining Si auxiliary relation, give the displayed three-term remainder. The integrand uses the
sinc removable value at zero.

The named declarations have no `sorryAx` dependency.

### DU-3.06 — Regularized series (3.21–3.22, p. 74).

Existing: Mathlib `Complex.regularizedHGFun` and `Complex.regularizedHGFunCoeff`; project
`DLMF.Hypergeometric.regularizedGeneralizedHypergeometric`,
`DLMF.Hypergeometric.generalizedHypergeometricCoeff_eq_gamma_mul_regularized`,
`DLMF.Hypergeometric.gammaProduct_ne_zero`,
`DLMF.Hypergeometric.regularizedGeneralizedHypergeometric_eq_series` in
`GeneralizedHypergeometric/Basic/SeriesProperties.lean`. These retain zero reciprocal Gamma
factors at arbitrary lower parameters and the ordinary bridge only on regular lower parameters.

The named declarations have no `sorryAx` dependency.

### DU-3.07 — Theorem 3.5: differentiation (pp. 74–75).

Existing: `DLMF.Hypergeometric.deriv_regularizedHGFun`,
`DLMF.Hypergeometric.regularizedGeneralizedHypergeometric_iteratedDeriv`,
`DLMF.Hypergeometric.generalizedHypergeometric_iteratedDeriv`, together with the analytic APIs.
The n=1 instance gives the derivative, and analyticity implies C∞. The first applies on the series
interior, the latter two on the full canonical analytic domain.

The named declarations have no `sorryAx` dependency.

### DU-3.08 — Theorem 3.6: differential equation (3.23–3.25, p. 75).

Existing: `DLMF.Hypergeometric.regularizedHGFun_ode`,
`DLMF.Hypergeometric.regularizedHGFun_ode_of_card_le`,
`DLMF.Hypergeometric.regularizedHGFun_ode_of_card_eq_add_one`; continued ordinary equation
`DLMF.Hypergeometric.generalizedHypergeometric_theta_ode` and expanded equation in
`GeneralizedHypergeometric/DifferentialEquations.lean`. `DLMF.Hypergeometric.eulerTheta` and
`DLMF.Hypergeometric.thetaPoly` are explicit operators. The 0F1 and 1F1 equations are also their
existing Bessel/Kummer foundational equations.

The named declarations have no `sorryAx` dependency.

### DU-3.09 — Theorem 3.8: analytic uniqueness at zero (p. 77).

Existing coefficient uniqueness `DLMF.Hypergeometric.coeff_eq_of_generalized_ode` in
`Hypergeometric/Basic/GeneralizedCalculus.lean`; uniqueness of scalar power-series coefficients is
`DLMF.Hypergeometric.scalarSeries_unique_ball`. Together with Mathlib's real analytic identity
theorem on an interval, this gives the source global analytic uniqueness from the normalized germ.
No C² uniqueness is inferred from this analytic-only theorem.

The named declarations have no `sorryAx` dependency.

### DU-3.10 — Theorem 3.9: real analytic continuation (3.30, pp. 78–79).

Existing: `DLMF.Hypergeometric.PrincipalContinuation`,
`DLMF.Hypergeometric.principalContinuation_exists`,
`DLMF.Hypergeometric.nonempty_principalContinuation`,
`DLMF.Hypergeometric.principalContinuation_unique`,
`DLMF.Hypergeometric.analyticOnNhd_regularizedGeneralizedHypergeometric` in
`GeneralizedHypergeometric/Basic/`. The complex cut-plane continuation restricts to the real
interval (-∞,1); the real identity theorem gives uniqueness. Ordinary values multiply by the
nonzero lower Gamma product.

The named declarations have no `sorryAx` dependency.

### DU-3.11 — Theorems 3.10 and 3.11: continued equation and derivatives (3.33, p. 79).

Existing: `DLMF.Hypergeometric.generalizedHypergeometric_principal_analytic`,
`DLMF.Hypergeometric.generalizedHypergeometric_terminating_entire`,
`DLMF.Hypergeometric.regularizedGeneralizedHypergeometric_iteratedDeriv`,
`DLMF.Hypergeometric.generalizedHypergeometric_iteratedDeriv`,
`DLMF.Hypergeometric.generalizedHypergeometric_theta_ode`. The canonical polynomial/truncated
convention is used for termination; no theorem is restricted to a disk when the source allows all
real arguments.

The named declarations have no `sorryAx` dependency.

### DU-3.12 — Contiguity operators (3.34–3.43, pp. 80–82).

Existing generalized raising identities: `DLMF.Hypergeometric.regularizedHGFun_contiguous` and
`DLMF.Hypergeometric.generalizedHypergeometric_raising_iterate`,
`DLMF.Hypergeometric.generalizedHypergeometric_lower_weighted_iteratedDeriv`, plus
`DLMF.Hypergeometric.GenContiguous`. For two upper shifts, eliminate theta between two instances
of the raising identity; for an upper/lower shift, combine the upper raising and lower shift
identities. All appearing ordinary lower parameters remain regular.

The named declarations have no `sorryAx` dependency.

### DU-3.13 — Lower-parameter Gauss contiguity (3.46, p. 82).

Existing full cut-plane identity
`DLMF.Hypergeometric.regularizedGaussHypergeometric_contiguous_c_three` in
`Hypergeometric/ArgumentContinuation.lean`. Multiply by Gamma(c) and use Gamma recurrence for c±1;
the displayed ordinary formula follows. This is not merely the disk-only
`DLMF.Hypergeometric.contiguous_c_three` predecessor.

The named declarations have no `sorryAx` dependency.

### DU-3.14 — Theorem 3.16: confluence (3.47, pp. 82–83).

Existing: `DLMF.Hypergeometric.generalizedHypergeometric_upper_confluence` in
`GeneralizedHypergeometric/DifferentialEquations.lean`. It sends one upper parameter to infinity
with z/A scaling and retains the remaining lists and lower regularity; restrict the complex
statement to real parameters.

The named declarations have no `sorryAx` dependency.

### DU-3.15 — Theorem 3.18: Euler–Pochhammer reduction (3.51, p. 84).

Existing: `DLMF.Hypergeometric.generalizedHypergeometric_euler_integral'` and
`DLMF.Hypergeometric.generalizedHypergeometric_euler_integral` in
`GeneralizedHypergeometric/Integrals.lean`; they include interval integrability and the full p≤q+1
cut-plane/entire domain. The coefficient Gamma(c)/(Gamma(a)Gamma(c-a)) is reciprocal beta by
Mathlib's beta identity.

The named declarations have no `sorryAx` dependency.

### DU-3.16 — Parameter derivatives (Exercise 3.5, p. 87).

New explicit parameter derivative targets in `GeneralizedHypergeometric/BookSeries.lean`:
`DLMF.Hypergeometric.hasDerivAt_generalizedHypergeometric_upper_parameter`,
`DLMF.Hypergeometric.summable_generalizedHypergeometric_upper_parameter_derivative`,
`DLMF.Hypergeometric.hasDerivAt_generalizedHypergeometric_lower_parameter`,
`DLMF.Hypergeometric.summable_generalizedHypergeometric_lower_parameter_derivative`. Both digamma
differences and the actual convergence interiors are written out; upper termination elsewhere is
permitted.

Admission status: `DLMF.Hypergeometric.hasDerivAt_generalizedHypergeometric_upper_parameter`,
`DLMF.Hypergeometric.summable_generalizedHypergeometric_upper_parameter_derivative`,
`DLMF.Hypergeometric.hasDerivAt_generalizedHypergeometric_lower_parameter`,
`DLMF.Hypergeometric.summable_generalizedHypergeometric_lower_parameter_derivative`.

### DU-3.17 — Fresnel integrals (Exercise 3.14, p. 89).

Existing: `DLMF.Confluent.fresnelC`, `DLMF.Confluent.fresnelS`;
`DLMF.Confluent.fresnelC_hypergeometric`, `DLMF.Confluent.fresnelS_hypergeometric` in
`ErrorFunctions/Relations.lean`. Remainders follow from
`DLMF.Confluent.fresnelAuxiliaryFComplex_sector_asymptotic`,
`DLMF.Confluent.fresnelAuxiliaryGComplex_sector_asymptotic` in
`ErrorFunctions/BoundsAsymptotics/FresnelRemainders.lean` and the existing Fresnel auxiliary
identities. The synopsis' corrected signs agree with these identities.

The named declarations have no `sorryAx` dependency.

### DU-3.18 — Airy equation (Exercise 3.15, p. 89).

New exact real C² basis characterization
`DLMF.Airy.Real.airy_equation_iff_existsUnique_hypergeometric_coordinates` in
`Airy/HypergeometricBasis.lean`. It includes every real solution and unique real coefficients of
the precise ordinary 0F1 functions; no holomorphic-solution hypothesis is added.

Admission status: `DLMF.Airy.Real.airy_equation_iff_existsUnique_hypergeometric_coordinates`.

### DU-3.19 — Borel integral (3.63–3.64, Exercise 3.17, p. 90).

New general Borel–Laplace target `Complex.integral_exp_neg_mul_factorialSeries` in
`DLMFMathlib/Analysis/Integral/BorelPowerSeries.lean`, including absolute integrability. The
hypergeometric instance uses `DLMF.Hypergeometric.generalizedHypergeometric_hasSum_disk` or
`DLMF.Hypergeometric.generalizedHypergeometric_hasSum_entire`, whose coefficients acquire exactly
the extra lower parameter one after division by n!; also existing
`DLMF.Hypergeometric.generalizedHypergeometric_laplace_integral` gives the parameter-reduction
form.

Admission status: `Complex.integral_exp_neg_mul_factorialSeries`,
`DLMF.Hypergeometric.generalizedHypergeometric_laplace_integral`.

### DU-3.20 — Newton polynomial expansion (Exercise 3.18, (3.65), pp. 90–91).

Existing finite-difference operator `fwdDiff`, its iterates and `shift_eq_sum_fwdDiff_iter` in
Mathlib; generalized choose is `Ring.choose`. New arbitrary-scalar polynomial expansion
`Polynomial.eval_eq_sum_fwdDiff_mul_choose` in
`DLMFMathlib/Algebra/Polynomial/NewtonExpansion.lean`. The choose first-difference identity is the
generalized Pascal identity in Mathlib's binomial API.

Admission status: `Polynomial.eval_eq_sum_fwdDiff_mul_choose`.

## Chapter 4

### DU-4.01 — Exceptional lower parameters (4.8, p. 106).

Existing: `DLMF.Hypergeometric.regularizedGaussHypergeometric_neg_nat` in
`Hypergeometric/Basic/CutPlane.lean`; the source coefficient becomes (a)_(N+1)(b)_(N+1)/(N+1)!
after converting the regularized positive lower parameter to ordinary normalization. Valid on the
full cut plane, hence x<1.

The named declarations have no `sorryAx` dependency.

### DU-4.02 — Gauss equation and Euler integral (4.9–4.11, p. 107).

Existing: `DLMF.Hypergeometric.regularizedGaussHypergeometric_ode`,
`DLMF.Hypergeometric.regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricIntegral`,
`DLMF.Hypergeometric.intervalIntegrable_eulerKernel` in `Hypergeometric/Basic/CutPlane.lean`.
Multiply by Gamma(c) for ordinary F; this retains the full real interval x<1 and c>b>0.

The named declarations have no `sorryAx` dependency.

### DU-4.03 — Inverse functions and Legendre function (4.12–4.18, pp. 107–108).

Existing arcsine disk formula `DLMF.Hypergeometric.arcsin_eq_ordinaryHypergeometric`; new all-real
arctangent formula `DLMF.Hypergeometric.arctan_eq_regularizedGaussHypergeometric` in
`GeneralizedHypergeometric/BookSeries.lean`. Existing `DLMF.Legendre.legendreP` and
`DLMF.Legendre.legendreP_ode` in `Legendre/Basic/Functions.lean` and `Properties.lean` cover the
continued Legendre definition and equation for x>-1.

Admission status: `DLMF.Hypergeometric.arctan_eq_regularizedGaussHypergeometric`.

### DU-4.04 — Fifteen contiguity relations (4.19–4.23, pp. 108–109).

Existing cut-plane contiguity family in `Hypergeometric/ArgumentContinuation.lean`:
`DLMF.Hypergeometric.regularizedGaussHypergeometric_contiguous_ab`,
`DLMF.Hypergeometric.regularizedGaussHypergeometric_contiguous_a`,
`DLMF.Hypergeometric.regularizedGaussHypergeometric_contiguous_a_b_pred`,
`DLMF.Hypergeometric.regularizedGaussHypergeometric_contiguous_a_c_succ`,
`DLMF.Hypergeometric.regularizedGaussHypergeometric_contiguous_a_succ_c_pred`,
`DLMF.Hypergeometric.regularizedGaussHypergeometric_contiguous_a_pred_c_succ`,
`DLMF.Hypergeometric.regularizedGaussHypergeometric_contiguous_a_pred_c_pred`,
`DLMF.Hypergeometric.regularizedGaussHypergeometric_contiguous_c_three`,
`DLMF.Hypergeometric.regularizedGaussHypergeometric_contiguous_diagonal`. Symmetry exchanges a,b.
Conversion with Gamma recurrence gives the nine displayed ordinary forms and their fifteen
distinct symmetric forms, with regularity for every shifted lower parameter.

The named declarations have no `sorryAx` dependency.

### DU-4.05 — Explicit generator of all 24 Kummer solutions (4.26–4.37, pp. 109–115).

New `DLMF.Hypergeometric.KummerSolutions.eightSolutions`, its proved defining-vector identity, and
the three admitted ODE targets `DLMF.Hypergeometric.KummerSolutions.eightSolutions_ode`,
`DLMF.Hypergeometric.KummerSolutions.eightSolutions_inversion_ode`,
`DLMF.Hypergeometric.KummerSolutions.eightSolutions_pfaff_inversion_ode` in
`Hypergeometric/RegularizedKummerSolutions.lean`. Every prefactor and shifted regularized Gauss
parameter is explicit, with no lower-parameter restrictions. The three real intervals produce all
24 expressions. For the two basis assertions, use the existing specific Wronskians with c
noninteger or a-b noninteger and the new general
`ODE.existsUnique_linearCombination_of_wronskian_ne_zero`.

Admission status: `DLMF.Hypergeometric.KummerSolutions.eightSolutions_ode`,
`DLMF.Hypergeometric.KummerSolutions.eightSolutions_inversion_ode`,
`DLMF.Hypergeometric.KummerSolutions.eightSolutions_pfaff_inversion_ode`,
`ODE.existsUnique_linearCombination_of_wronskian_ne_zero`.

### DU-4.06 — Theorem 4.8: Pfaff/Euler transformation (4.38, p. 115).

Existing `DLMF.Hypergeometric.regularizedGaussHypergeometric_pfaff` in
`Hypergeometric/ArgumentContinuation.lean` has arbitrary a,b,c and the full cut-plane domain.
Ordinary F is obtained by multiplying by Gamma(c), with c regular. The raw series Pfaff lemma with
both arguments in the unit disk is not counted as full coverage.

The named declarations have no `sorryAx` dependency.

### DU-4.07 — Euler parameter transformation (4.39, p. 117).

Existing `DLMF.Hypergeometric.regularizedGaussHypergeometric_euler` in
`Hypergeometric/ArgumentContinuation.lean`, arbitrary lower parameter and full cut plane. Ordinary
conversion is multiplication by Gamma(c).

The named declarations have no `sorryAx` dependency.

### DU-4.08 — Clausen square (4.40, p. 117).

Existing `DLMF.Hypergeometric.generalizedHypergeometric_clausen_principal` in
`GeneralizedHypergeometric/Transformations.lean`, supplementing the disk
`DLMF.Hypergeometric.clausen_formula` in `Hypergeometric/Clausen.lean`. The source's 2a+2b
regularity also guarantees a+b+1/2 regularity; real x<1 lies in the canonical cut plane.

The named declarations have no `sorryAx` dependency.

### DU-4.09 — Arcsine-square series (4.45–4.46, p. 119).

Existing `DLMF.Hypergeometric.hasSum_arcsin_sq` in `Hypergeometric/Clausen.lean`. Its explicit
coefficients agree with `generalizedHypergeometricCoeff {1,1,1} {2,3/2}` by factorial/Pochhammer
identities, so the 3F2 form follows by the canonical series-sum theorem.

The named declarations have no `sorryAx` dependency.

### DU-4.10 — Gauss summation (4.49–4.50, p. 120).

Existing `DLMF.Hypergeometric.hasSum_regularizedGauss_one` in `Hypergeometric/Boundary.lean`, with
arbitrary c and Re(c-a-b)>0. Reciprocal denominator Gamma factors are already totalized correctly.
Ordinary values follow by multiplication by Gamma(c), only for regular c.

The named declarations have no `sorryAx` dependency.

### DU-4.11 — Chu–Vandermonde (4.51, p. 120).

New finite-only lower-regularity target `DLMF.Hypergeometric.sum_pochhammer_mul_neg_nat_div` in
`Hypergeometric/TerminatingSummations.lean`. It permits denominator poles after N and excludes
only the displayed finite denominators, unlike the older globally regular ordinary Gauss lemma.

Admission status: `DLMF.Hypergeometric.sum_pochhammer_mul_neg_nat_div`.

### DU-4.12 — Bailey half-argument summation (4.52, p. 121).

Existing `DLMF.Hypergeometric.bailey_summation` in
`Hypergeometric/Elementary/AlgebraicValues.lean`. The Gamma quotient uses totalized inverse Gamma,
so denominator poles give zero exactly as in the synopsis. The evaluation point 1/2 is strictly
within the Gauss series disk.

The named declarations have no `sorryAx` dependency.

### DU-4.13 — Kummer summation at minus one (4.57, p. 122).

Derivation from existing `DLMF.Hypergeometric.regularizedGaussHypergeometric_pfaff` at z=-1 and
`DLMF.Hypergeometric.gauss_second_summation` at z=1/2. Pfaff changes (a,b;c;-1) into
2^(-a)F(a,c-b;c;1/2), with c=1+a-b satisfying the second Gauss sum condition. This gives the
continued value even when the original series at -1 diverges; the older
`DLMF.Hypergeometric.kummer_theorem` is not used outside its series convergence hypotheses. This
Pfaff-at-minus-one and Gauss-second-summation derivation was checked by a Lean example, retaining
every regular lower parameter and the continued function at -1.

The named declarations have no `sorryAx` dependency.

### DU-4.14 — Gauss second summation (4.58, p. 122).

Existing `DLMF.Hypergeometric.gauss_second_summation` in
`Hypergeometric/Elementary/AlgebraicValues.lean`. The regular lower parameter and totalized
reciprocal denominator Gamma factors match the synopsis exactly.

The named declarations have no `sorryAx` dependency.

### DU-4.15 — Theorem 4.11: limits at one (4.59–4.61, pp. 122–123).

Positive excess: existing `DLMF.Hypergeometric.tendsto_regularizedGaussHypergeometric_left_one` in
`Hypergeometric/Boundary.lean`; negative excess: apply full-plane Euler transformation and that
positive-excess limit. Zero excess: new
`DLMF.Hypergeometric.tendsto_regularizedGaussHypergeometric_div_log_left_one` in
`Hypergeometric/EndpointLogarithm.lean`. Multiply by Gamma(c) for each ordinary limit/equivalent;
source a,b,c regular ensures the nonzero leading coefficients in the equivalents.

Admission status: `DLMF.Hypergeometric.tendsto_regularizedGaussHypergeometric_div_log_left_one`.

### DU-4.16 — Lemma 4.12: connection at one (4.63, p. 123).

Existing `DLMF.Hypergeometric.zero_first_connection_one_of_not_neg_nat` in
`Hypergeometric/Solutions/Connections.lean`, plus reciprocal-Gamma connection forms in
`Hypergeometric/LogConnectionsRecipGamma.lean`. The lens contains every real 0<x<1; noninteger
excess excludes singular shifted lower parameters.

The named declarations have no `sorryAx` dependency.

### DU-4.17 — Lemma 4.13: logarithmic connection (4.64, p. 123).

Existing `DLMF.Hypergeometric.logarithmic_connection_one_sub` in
`Hypergeometric/ConnectionFormulas.lean` at integer excess zero, and its reciprocal-Gamma
extension in `LogConnectionsRecipGamma.lean`. The explicit n=0 digamma terms require the
synopsis's upper-parameter regularity, so terminating cases are not substituted literally.

The named declarations have no `sorryAx` dependency.

### DU-4.18 — Cauchy trigonometric identities (4.68–4.69, p. 127).

Existing `DLMF.Hypergeometric.sin_sq_sin` and `DLMF.Hypergeometric.sin_sq_cos` in
`Hypergeometric/Elementary/AlgebraicValues.lean`. These hold on the source interval |x|<π/2 for
arbitrary complex a, hence include the real forms.

The named declarations have no `sorryAx` dependency.

### DU-4.19 — Saalschütz (4.70, p. 128).

New finite-only regularity target `DLMF.Hypergeometric.pfaff_saalschutz_of_finite_regular` in
`Hypergeometric/TerminatingSummations.lean`. Both lower Pochhammer sequences are required nonzero
only through N; no artificial later-pole exclusion is imposed.

Admission status: `DLMF.Hypergeometric.pfaff_saalschutz_of_finite_regular`.

### DU-4.20 — Quadratic transformations (4.71–4.72, pp. 128–129).

Existing quadratic transformations `DLMF.Hypergeometric.kummer_quadratic`,
`DLMF.Hypergeometric.gauss_quadratic`, `DLMF.Hypergeometric.quadratic_double_denominator` in
`Hypergeometric/FurtherTransformations/Quadratic.lean`, with principal-continuation identities
from the argument-continuation APIs. For the second source formula use t=(1-y)/(1+y) in (0,1), so
4t/(1+t)^2=x²; the positive square root y fixes the real branch.

The named declarations have no `sorryAx` dependency.

### DU-4.21 — Legendre second-kind function (4.74–4.75, pp. 129–130).

Existing definitions `DLMF.Legendre.legendreQ`, `DLMF.Legendre.legendreP`, their ODEs and
`DLMF.Legendre.associated_wronskian_11` at order zero; the canonical Q body is exactly the source
hypergeometric form. New all-real-degree integral and convergence target
`DLMF.Legendre.legendreQ_eq_finite_weighted_integral` in `Legendre/FiniteWeightedIntegral.lean`.
The new generic FundamentalPair theorem upgrades the Wronskian to unique real C² solution
coordinates.

Admission status: `DLMF.Legendre.legendreQ_eq_finite_weighted_integral`.

### DU-4.22 — Dixon summation (4.76, p. 130).

Existing `DLMF.Hypergeometric.dixon_sum` in `Hypergeometric/Identities/Dixon.lean` and the
generalized 3F2 unit-argument infrastructure. The source's real hypotheses imply positive excess.
Its finite numerator Gamma restrictions must be retained; denominator poles are allowed via
totalized inverse Gamma factors.

The named declarations have no `sorryAx` dependency.

## Chapter 5

### DU-5.01 — Complete and incomplete integrals (5.3–5.9, pp. 152–154).

Existing real parameter functions `DLMF.Elliptic.Real.completeEllipticKOfParameter`,
`DLMF.Elliptic.Real.completeEllipticEOfParameter`,
`DLMF.Elliptic.Real.incompleteEllipticFOfParameter`; source modulus k is represented by parameter
m=k². Existing `DLMF.Elliptic.Real.completeEllipticKOfParameter_eq_ordinaryHypergeometric` and
`DLMF.Elliptic.Real.completeEllipticEOfParameter_eq_ordinaryHypergeometric` in
`Elliptic/Complete.lean`; TauCeti also provides `TauCeti.Real.legendreK`,
`TauCeti.Real.legendreEc` in modulus convention with precise bridges in
`Elliptic/MathlibCoverage.lean`.

The named declarations have no `sorryAx` dependency.

### DU-5.02 — Curve lengths (5.3, 5.6, 5.13, pp. 152–155).

Existing `DLMF.Elliptic.ellipsePerimeter`, `DLMF.Elliptic.ellipsePerimeter_eq`,
`DLMF.Elliptic.ellipsePerimeter_eq_ordinaryHypergeometric` in `Elliptic/SpecialValues.lean`.
Lemniscate constant and Gamma evaluation are upstream `TauCeti.Real.lemniscateConstant_eq_Gamma`,
`TauCeti.Real.lemniscateConstant_eq_sqrt_two_mul_legendreK` in TauCeti
`Analysis/SpecialFunctions/EllipticIntegral/Lemniscate.lean`; scale the normalized arc length by
a.

The named declarations have no `sorryAx` dependency.

### DU-5.03 — Differential equations and derivatives (5.16–5.20, pp. 155–156).

Existing TauCeti `TauCeti.Real.legendreK_differential_equation`,
`TauCeti.Real.legendreEc_differential_equation`, `TauCeti.Real.deriv_legendreK`,
`TauCeti.Real.deriv_legendreEc` and their second-derivative formulas in
`Analysis/SpecialFunctions/EllipticIntegral/ModulusDerivative.lean` give all four source equations
directly in modulus convention. The older parameter-convention first derivatives are also in
`DLMF.Elliptic.Real.hasDerivAt_completeEllipticEOfParameter_sq` and
`DLMF.Elliptic.Real.hasDerivAt_completeEllipticKOfParameter_sq`.

The named declarations have no `sorryAx` dependency.

### DU-5.04 — Legendre relation (5.21–5.25, pp. 156–157).

Existing `DLMF.Elliptic.legendre_relation` in `Elliptic/Complete.lean`, and TauCeti's modulus
Legendre relation. The complementary parameter is 1-m; source k'=sqrt(1-k²) therefore maps
correctly.

The named declarations have no `sorryAx` dependency.

### DU-5.05 — Descending Landen transformation (5.26–5.27, p. 157).

Existing `DLMF.Elliptic.Real.completeEllipticKOfParameter_landen_descending`,
`DLMF.Elliptic.Real.completeEllipticEOfParameter_landen_descending` in `Elliptic/AGM.lean`;
TauCeti `TauCeti.Real.legendreK_eq_one_add_mul_legendreK` provides the modulus form. Both K and E
transformations, including E's subtraction term, are covered.

The named declarations have no `sorryAx` dependency.

### DU-5.06 — AGM definition and quadratic convergence (5.28–5.33, p. 158).

Existing Mathlib `NNReal.agmSequences`, `NNReal.agm` and convergence/monotonicity bounds; TauCeti
`NNReal.agmSequences_snd_sub_fst_le` and `Real.half_add_sub_sqrt_mul_le` in
`Analysis/SpecialFunctions/ArithmeticGeometricMean.lean` give the exact quadratic difference
bound. Positivity and equality of limits follow from the lower initial value u>0.

The named declarations have no `sorryAx` dependency.

### DU-5.07 — Theorem 5.2: elliptic integral and AGM (5.35–5.37, pp. 159–160).

Existing TauCeti `TauCeti.Real.legendreK_eq_pi_div_two_mul_agm`,
`TauCeti.Real.agmIntegral_eq_legendreK_div` in `EllipticIntegral/Gauss.lean`; local
`DLMF.Elliptic.agmIntegral_eq_pi_div_two_div_agm` and
`DLMF.Elliptic.Real.completeEllipticKOfParameter_eq_pi_div_agm` cover the scaled two-variable
integral and K formula.

The named declarations have no `sorryAx` dependency.

### DU-5.08 — Singular modulus (5.38, p. 160).

Existing TauCeti `TauCeti.Real.legendreK_one_div_sqrt_two`; local
`DLMF.Elliptic.Real.completeEllipticKOfParameter_one_half`,
`DLMF.Elliptic.Gamma_one_fourth_sq_mul_agm`. They give both the Gamma value and the equivalent AGM
identity.

The named declarations have no `sorryAx` dependency.

### DU-5.09 — Amplitude and Jacobi functions (5.39–5.46, pp. 160–161).

Existing `DLMF.Elliptic.Real.strictMono_incompleteEllipticFOfParameter`,
`DLMF.Elliptic.Real.surjective_incompleteEllipticFOfParameter`, the order isomorphism and inverse
amplitude definitions in `Elliptic/Basic/Amplitude.lean`. Parity, square identities and special
values are `DLMF.Elliptic.Real.jacobiAmOfParameter_neg`,
`DLMF.Elliptic.Real.jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq`,
`DLMF.Elliptic.Real.mul_jacobiSnOfParameter_sq_add_jacobiDnOfParameter_sq`,
`DLMF.Elliptic.jacobi_zero`, `DLMF.Elliptic.jacobi_neg`,
`DLMF.Elliptic.Real.jacobi_completeEllipticKOfParameter` in `Elliptic/Basic/Jacobi.lean`.

The named declarations have no `sorryAx` dependency.

### DU-5.10 — Theorem 5.4: periods (5.47, p. 162).

Existing `DLMF.Elliptic.Real.jacobi_add_two_completeEllipticKOfParameter` in
`Elliptic/Basic/Jacobi.lean`, whose three components are exactly the source antiperiods/period for
sn,cn,dn. No claim that 2K is the least period of sn or cn is made.

The named declarations have no `sorryAx` dependency.

### DU-5.11 — Theorem 5.5: derivatives (5.48, p. 162).

Existing `DLMF.Elliptic.Real.hasDerivAt_jacobiAmOfParameter`,
`DLMF.Elliptic.Real.hasDerivAt_jacobiSnOfParameter`,
`DLMF.Elliptic.Real.hasDerivAt_jacobiCnOfParameter`,
`DLMF.Elliptic.Real.hasDerivAt_jacobiDnOfParameter`. Their coupled analytic right sides bootstrap
the functions to C∞; TauCeti's JacobiElliptic foundational API also supplies this smoothness
directly.

The named declarations have no `sorryAx` dependency.

### DU-5.12 — Theorem 5.6: pendulum (5.49–5.55, pp. 162–163).

Existing `DLMF.Elliptic.pendulumAngle`, `DLMF.Elliptic.pendulumAngle_ode`,
`DLMF.Elliptic.pendulumAngle_periodic` in `Elliptic/JacobiIdentities.lean`. For turning-point
initial data and uniqueness use TauCeti `Real.pendulumAngle_zero`,
`Real.deriv_pendulumAngle_zero`, `Real.eq_pendulumAngle_of_hasDerivAt`,
`DLMF.Elliptic.pendulumAngle_periodic` in
`Analysis/SpecialFunctions/JacobiElliptic/Pendulum.lean`; the source phase K turns sn into the
turning-point form by the existing K-shift identity. No duplicate admitted pendulum theorem was
retained.

The named declarations have no `sorryAx` dependency.

### DU-5.13 — Theorem 5.9: inverse sn (5.56–5.58, p. 164).

Existing `DLMF.Elliptic.Real.jacobiArcsnOfParameter`,
`DLMF.Elliptic.Real.jacobiSnOfParameter_jacobiArcsnOfParameter`,
`DLMF.Elliptic.Real.jacobiArcsnOfParameter_jacobiSnOfParameter`,
`DLMF.Elliptic.Real.hasDerivAt_jacobiArcsnOfParameter` in `Elliptic/Basic/Jacobi.lean`. The
interval bijection follows from these inverse identities, and the algebraic integral is
`DLMF.Elliptic.Real.integral_recip_sqrt_eq_incompleteEllipticFOfParameter` and its endpoint
theorem in `Elliptic/SpecialValues.lean`.

The named declarations have no `sorryAx` dependency.

### DU-5.14 — Quartic integral reductions (5.60–5.66, pp. 165–166).

New explicit reductions in `DLMF/Elliptic/BookReductions.lean`:
`DLMF.Elliptic.integral_recip_sqrt_one_sub_pow_four_to`,
`DLMF.Elliptic.integral_recip_sqrt_one_add_pow_four`,
`DLMF.Elliptic.integral_recip_sqrt_sub_sq_mul_sub_sq`,
`DLMF.Elliptic.integral_Ioi_recip_sqrt_sq_sub_mul_sq_sub`. The exterior formula includes
integrability. Every modulus is converted to parameter m=k², including m=1/2 for the lemniscatic
formulas.

Admission status: `DLMF.Elliptic.integral_recip_sqrt_one_sub_pow_four_to`,
`DLMF.Elliptic.integral_recip_sqrt_one_add_pow_four`,
`DLMF.Elliptic.integral_recip_sqrt_sub_sq_mul_sub_sq`,
`DLMF.Elliptic.integral_Ioi_recip_sqrt_sq_sub_mul_sq_sub`.

### DU-5.15 — Cubic integral reduction (5.67–5.68, p. 166).

New target `DLMF.Elliptic.integral_recip_sqrt_cubic` in `Elliptic/BookReductions.lean`; explicit
ordered roots a<b<c, x∈[a,b], parameter (b-a)/(c-a), and the source factor 2/sqrt(c-a).

Admission status: `DLMF.Elliptic.integral_recip_sqrt_cubic`.

## Chapter 6

### DU-6.01 — Definition, confluence, equation and Euler integral (6.1–6.6, pp. 181–182).

Existing `DLMF.Confluent.kummerM`, `regularizedHGFun {a} {c}`, `DLMF.Confluent.hasSum_kummerM`,
`DLMF.Confluent.analyticOnNhd_kummerM`, `DLMF.Confluent.kummerM_ode`; the full regularized
equation is supplied by the generalized theta equation. Euler integral is
`DLMF.Confluent.regularized_euler_integral` in
`Confluent/IntegralRepresentations/EulerAndBessel.lean`; multiply by Gamma(c) and use beta.
Confluence is the existing generalized upper-confluence theorem at two upper/one lower parameters.

The named declarations have no `sorryAx` dependency.

### DU-6.02 — Exceptional lower parameters (6.7, p. 182).

Existing `DLMF.Confluent.regularizedHGFun_of_neg_nat` in
`Confluent/BasicProperties/Continuity.lean`. Conversion of its positive lower parameter N+2 to
ordinary M gives exactly the factorial factor and shifted numerator parameter.

The named declarations have no `sorryAx` dependency.

### DU-6.03 — Error function (6.8–6.10, pp. 182–183).

Existing complex `DLMF.Confluent.erf`, real bridge `DLMF.Confluent.erf_ofReal` to TauCeti
`TauCeti.Real.erf`, its integral definition, oddness and positive-infinity limit. Hypergeometric
identity `DLMF.Confluent.kummerM_erf` in `Confluent/Relations.lean` matches the source
normalization 2/sqrt π.

The named declarations have no `sorryAx` dependency.

### DU-6.04 — Incomplete gamma (6.11–6.14, p. 183).

Existing `DLMF.Confluent.lowerIncompleteGamma`, `DLMF.Confluent.lowerIncompleteGamma_eq_integral`,
`DLMF.Confluent.kummerM_lowerIncompleteGamma` and the limit to Gamma in the IncompleteGamma area;
error bridge `DLMF.Confluent.erf_lowerIncompleteGamma` in ErrorFunctions relations. The source
a,x>0 selects the positive-real branches of all powers.

The named declarations have no `sorryAx` dependency.

### DU-6.05 — Kummer transformation (6.15–6.16, p. 184).

Existing `DLMF.Confluent.kummerM_kummer_transform`,
`DLMF.Confluent.regularizedConfluent_kummer_transform`; combine
`DLMF.Confluent.kummerM_lowerIncompleteGamma` with Kummer transformation to obtain the
exponential-times-M(1,a+1,x) formula. Lower regularity is retained only in the ordinary identity;
the regularized theorem has arbitrary c.

The named declarations have no `sorryAx` dependency.

### DU-6.06 — Six contiguity relations (6.17, p. 184).

Existing complete Kummer contiguity family in `Confluent/Basic/KummerContiguous.lean`:
`DLMF.Confluent.kummerM_contiguous_a`, `DLMF.Confluent.kummerM_contiguous_b`,
`DLMF.Confluent.kummerM_contiguous_a_b`, `DLMF.Confluent.kummerM_contiguous_shift_a`,
`DLMF.Confluent.kummerM_contiguous_mixed`, `DLMF.Confluent.kummerM_contiguous_down`,
`DLMF.Confluent.kummerM_ode_contiguous`, `DLMF.Confluent.kummerM_contiguous_shift_b_succ`,
`DLMF.Confluent.kummerM_contiguous_mixed_b_pred`. Eliminate the derivative between the displayed
derivative-shift identities for any of the six source forms. The final mixed relation includes the
source's corrected factor x.

The named declarations have no `sorryAx` dependency.

### DU-6.07 — Theorem 6.3: solution basis (6.18–6.20, pp. 184–185).

Existing `DLMF.Confluent.kummerM_ode`, shifted-power equation and
`DLMF.Confluent.wronskian_kummerM_pair` in `Confluent/BasicProperties/Wronskians.lean`. New
`ODE.existsUnique_linearCombination_of_wronskian_ne_zero` in
`DLMFMathlib/Analysis/ODE/FundamentalPair.lean` supplies unique coordinates for real-variable C²
solutions, not only holomorphic solutions. Normalize Kummer's equation by dividing by x on (0,∞).

Admission status: `ODE.existsUnique_linearCombination_of_wronskian_ne_zero`.

### DU-6.08 — Zero-upper-parameter bridge (6.21–6.25, pp. 185–186).

Existing `DLMF.Bessel.kummerM_eq_exp_mul_regularized0F1` in `Bessel/RegularizedSeries.lean`, and
the Gamma conversion to ordinary 0F1. Substitute ν=c-1 and the doubled/scaled argument. The
positive and negative real z forms are specializations at 4sqrt z and 4i sqrt(-z), preserving the
entire complex M branch.

The named declarations have no `sorryAx` dependency.

### DU-6.09 — Tricomi solution (Exercise 6.8, (6.26), p. 187).

Existing `DLMF.Confluent.kummerU_laplace_integrable`, `DLMF.Confluent.kummerU_laplace`,
`DLMF.Confluent.hasDerivAt_kummerU` and `DLMF.Confluent.kummerU_ode_contiguous` (substitution of
the first two derivative-shift identities gives the differential equation),
large-positive-argument U asymptotics, and
`DLMF.Confluent.wronskian_regularizedHGFun_kummerU_all`. For a>0 the Wronskian coefficient
1/Gamma(a) is nonzero, including integer c. The new generic FundamentalPair theorem gives the
real-variable basis statement from this Wronskian and both ODEs. The differential-equation
substitution was checked by a Lean example: rewrite iteratedDeriv_kummerU at order two and
deriv_kummerU, expand the two-factor Pochhammer, and take a times kummerU_ode_contiguous.

The named declarations have no `sorryAx` dependency.

### DU-6.10 — Hermite equation (Exercise 6.9, (6.27), p. 188).

New exact `DLMF.Confluent.Real.hermite_equation_iff_existsUnique_kummer_coordinates` in
`Confluent/HermiteBasis.lean` characterizes all real C² solutions and unique real coefficients of
the stated even and odd M functions, for arbitrary real ν. Existing integer Hermite polynomial
identities alone do not cover this parameter range.

Admission status: `DLMF.Confluent.Real.hermite_equation_iff_existsUnique_kummer_coordinates`.

### DU-6.11 — Complementary error asymptotic (6.28–6.29, p. 188).

Existing `DLMF.Confluent.erfc`, erfc tail integral and erf bridge;
`DLMF.Confluent.erfc_sector_asymptotic` in
`ErrorFunctions/BoundsAsymptotics/GaussianRemainders.lean`. At three terms on the positive real
ray its coefficients are 1,-1/2,3/4 with remainder O(x^-6) inside the scaled bracket.

The named declarations have no `sorryAx` dependency.

### DU-6.12 — Repeated error integrals (6.30–6.33, p. 188).

Existing `DLMF.Confluent.iteratedErfc`, `DLMF.Confluent.iteratedErfc_tail`,
`DLMF.Confluent.iteratedErfc_normalization`, `DLMF.Confluent.iteratedDeriv_iteratedErfc_zero`,
`DLMF.Confluent.iteratedErfc_ode`, `DLMF.Confluent.iteratedErfc_general_solution`, and its nonzero
Wronskian in `ErrorFunctions/Repeated.lean`. The new generic real FundamentalPair theorem gives
the real C² basis from the same pair and Wronskian. Integer n and the source factorial/Gamma
normalization are retained.

The named declarations have no `sorryAx` dependency.

## Chapter 7

### DU-7.01 — First-kind definition (7.1–7.7, pp. 203–205).

Existing Mathlib `Complex.besselJ`, project `DLMF.Bessel.besselJ_eq_regularized`, its regularized
coefficient series and analyticity/ODE API in `Bessel/Basic/` and `Bessel/RegularizedSeries.lean`.
The positive-real ray fixes the source real power; reciprocal Gamma vanishes at the exceptional
indices.

The named declarations have no `sorryAx` dependency.

### DU-7.02 — Theorem 7.1: noninteger basis (p. 205).

Existing `DLMF.Bessel.wronskian_besselJ_neg` and Bessel equations. For real noninteger ν the sine
factor in that Wronskian is nonzero; the new generic
`ODE.existsUnique_linearCombination_of_wronskian_ne_zero` yields unique real C² coordinates in
J_ν,J_-ν on (0,∞). The existing complex `DLMF.Bessel.eq_besselJ_besselY_of_ode` alone was not
counted as the source's real C² statement.

Admission status: `ODE.existsUnique_linearCombination_of_wronskian_ne_zero`.

### DU-7.03 — Integer and half-integer cases (7.8–7.12, pp. 205–206).

Existing integer-order series and negative-order identity for Mathlib `Complex.besselJ`, parity on
the real axis, and `DLMF.Bessel.besselJ_half`, `DLMF.Bessel.besselJ_neg_half` in
`Bessel/RegularizedSeries.lean`. Real restrictions give the source sine/cosine formulas for x>0;
integer arguments at x=0 use their entire series, not the general slit-plane branch.

The named declarations have no `sorryAx` dependency.

### DU-7.04 — Recurrences and derivatives (7.16–7.18, p. 207).

Existing `Complex.two_mul_self_mul_besselJ`, `DLMF.Bessel.hasDerivAt_besselJ` and integer-order
derivative API in `Bessel/Basic/`. The ν=0 derivative follows from the recurrence and negative
integer order; at zero use the integer entire series derivative, so the source all-real J0'
identity is preserved.

The named declarations have no `sorryAx` dependency.

### DU-7.05 — Poisson integral (7.19–7.21, p. 207).

Existing `DLMF.Bessel.besselJ_eq_poisson_integral`, `DLMF.Bessel.besselJ_eq_poisson_cos` in
`Bessel/Theorems.lean` and `YIntegralRep.lean`. The integer zero-order integral for all real
arguments is `DLMF.Bessel.besselJ_zero_eq_integral_cos` in `Bessel/BesselIntegral.lean`.

The named declarations have no `sorryAx` dependency.

### DU-7.06 — Schläfli integral (7.22–7.23, p. 208).

Existing `DLMF.Bessel.besselJ_eq_schlafli` and `DLMF.Bessel.integrableOn_schlafli` in
`Bessel/Schlafli.lean`; the integer-order real-axis formula is
`DLMF.Bessel.besselJ_int_eq_integral_cos` in `Bessel/BesselIntegral.lean`. The order may be any
real number; x>0 controls the infinite hyperbolic-exponential tail.

The named declarations have no `sorryAx` dependency.

### DU-7.07 — Theorem 7.4: stationary phase (7.32, p. 210).

New general target `Asymptotics.isBigO_integral_exp_mul_phase_of_maximum` in
`DLMFMathlib/Analysis/Asymptotics/QuadraticStationaryPhase.lean`. It records both derivative
signs, the interior critical point and negative second derivative, arbitrary complex smooth
amplitude, the exact Gaussian phase factor and the O(x^-1) remainder.

Admission status: `Asymptotics.isBigO_integral_exp_mul_phase_of_maximum`.

### DU-7.08 — Theorem 7.6: large-argument asymptotic (7.33, p. 211).

Existing `DLMF.Bessel.besselJ_sub_cos_isBigO` in `Bessel/Asymptotics.lean`, a stronger
all-complex-order fixed-order asymptotic. Restriction to positive real arguments and weakening the
inverse-power remainder gives the source O(x^-1) statement.

The named declarations have no `sorryAx` dependency.

### DU-7.09 — Theorem 7.7: zeros (pp. 211–212).

Existing `DLMF.Bessel.besselJ_infinite_zeros_of_real` covers infinitude at all real orders, but
the older `DLMF.Bessel.besselJ_zeros_simple` assumes ν>-1. New full-domain targets
`DLMF.Bessel.deriv_re_besselJ_ne_zero_of_eq_zero`,
`DLMF.Bessel.exists_strictMono_besselJ_positive_zeros` in `Bessel/PositiveZeroSequence.lean` cover
arbitrary real order, simple roots, complete injective increasing enumeration and divergence of
the zero sequence. The same module also captures nontrivial analytic Bessel-solution and
derivative-zero simplicity for Temme's stronger scope.

Admission status: `DLMF.Bessel.deriv_re_besselJ_ne_zero_of_eq_zero`,
`DLMF.Bessel.exists_strictMono_besselJ_positive_zeros`.

### DU-7.10 — Lommel integrals and orthogonality (7.36–7.39, p. 213).

Existing `DLMF.Bessel.integral_mul_besselJ_mul_besselJ`,
`DLMF.Bessel.integral_besselJ_orthogonal`, `DLMF.Bessel.hasDerivAt_besselNormPrimitive`,
`DLMF.Bessel.tendsto_besselNormPrimitive`, `DLMF.Bessel.integral_mul_besselJ_sq` in
`Bessel/Lommel.lean`. Rescale [0,1] to [0,a]. The general equal-parameter formula is the primitive
evaluation, while the last existing theorem gives its root specialization. Negative integer orders
reduce to nonnegative integer orders using J_-n=(-1)^nJ_n; arbitrary noninteger orders below -1
are correctly excluded.

The named declarations have no `sorryAx` dependency.

### DU-7.11 — Second-kind definition and integer limits (Definitions 7.9–7.10, (7.40–7.45), pp. 214–215).

Existing canonical `DLMF.Bessel.besselY`, its noninteger connection and order limits in
`Bessel/Basic/SecondKind.lean`; `DLMF.Bessel.besselY_eq_schlafli` in `Bessel/YSchlafli.lean` is
the full real-order integral formula. Integer negative-order parity is in the canonical integer
parameter API.

The named declarations have no `sorryAx` dependency.

### DU-7.12 — Integer-order logarithmic series (7.49, p. 216).

Existing `DLMF.Bessel.besselY_nat_eq_series` in `Bessel/WeberSeries.lean`, with the finite
singular sum, logarithmic J_n term and the two digamma coefficients explicitly present. The
positive-real branch gives the source real formula.

The named declarations have no `sorryAx` dependency.

### DU-7.13 — Theorem 7.11: integer-order basis (7.50, p. 216).

Existing `DLMF.Bessel.wronskian_besselJ_besselY` for all complex orders on the slit plane and
`DLMF.Bessel.eq_besselJ_besselY_of_ode` for holomorphic solutions. The new generic real
FundamentalPair theorem supplies unique real C² coordinates on (0,∞), including every integer
order and every noninteger real order.

The named declarations have no `sorryAx` dependency.

### DU-7.14 — Generating function and Fourier expansions (7.52, Exercise 7.10, p. 218).

Existing `DLMF.Bessel.hasSum_besselJ_generating_function` in `Bessel/Generating.lean` gives the
bilateral generating series and absolute convergence for nonzero complex t.
`DLMF.Bessel.hasSum_besselJ_cos` and `DLMF.Bessel.hasSum_besselJ_sin` in `Bessel/WeberSeries.lean`
are exactly the two real Fourier expansions.

The named declarations have no `sorryAx` dependency.

### DU-7.15 — Airy integral and Bessel bridge (7.53–7.56, p. 219).

Existing `DLMF.Airy.airyAi`, `DLMF.Airy.airyAiDeriv`, their entire analyticity, Airy ODE and
initial values in `Airy/Basic/`; conditional real integral/derivative representations in
`Airy/IntegralRepresentations.lean` and its constituent files;
`DLMF.Airy.airyAi_neg_eq_besselJ_complex` in `Airy/Relations/BesselRepresentations.lean` gives the
source negative-axis bridge. Finite-integral limits are used for the oscillatory representation.

The named declarations have no `sorryAx` dependency.

### DU-7.16 — Struve function (7.57–7.59, p. 220).

Existing `DLMF.Struve.struveH`, coefficient series, regularized 1F2 bridge,
`DLMF.Struve.struveH_ode` in `Struve/SeriesAndEquations.lean`, and the Poisson sine integral in
`Struve/Representations/PoissonAndBarnesLoop.lean`. The forcing coefficient equals
4(x/2)^(ν+1)/(sqrtπ Gamma(ν+1/2)); the positive-real ray preserves the source real branch.

The named declarations have no `sorryAx` dependency.

## Chapter 8

### DU-8.01 — Real definition, series and hypergeometric form (8.1–8.5, pp. 239–240).

Existing principal `DLMF.Zeta.polylog`, `DLMF.Zeta.polylog_zero_order`,
`DLMF.Zeta.polylog_one_eq_neg_log`, `DLMF.Zeta.hasDerivAt_polylog`, `DLMF.Zeta.polylog_zero_arg`
and power-series sum. The recursive real integral follows by the fundamental theorem with the
removable derivative value at zero. New explicit arbitrary-natural-order hypergeometric bridge
`DLMF.Polylog.polylog_natCast_eq_hypergeometric` is in `Polylog/BookIdentities.lean`.

Admission status: `DLMF.Polylog.polylog_natCast_eq_hypergeometric`.

### DU-8.02 — Theorem 8.1: Bose–Einstein integral (8.6, p. 240).

Existing `DLMF.Zeta.polylog_eq_integral` in `Zeta/Polylog/Properties.lean`; at integer n>=1,
Gamma(n)=(n-1)! gives exactly Duverney's Bose–Einstein integral. Its hypotheses include every real
x<1, not only positive x or the disk.

The named declarations have no `sorryAx` dependency.

### DU-8.03 — Endpoint values and duplication (8.7–8.11, p. 241).

Existing `DLMF.Zeta.polylog_one`, `DLMF.Polylog.polylogSeries_neg_one`,
`DLMF.Polylog.polylogSeries_add_polylogSeries_neg`,
`DLMF.Polylog.polylogSeries_add_polylogSeries_neg_of_norm_le`, and
`DLMF.Zeta.polylog_one_eq_neg_log`. For n>=2 the boundary polylog equals its series; n=1 at -1
follows from the principal logarithm identity; n=0 duplication is the rational zero-order formula
and algebra.

The named declarations have no `sorryAx` dependency.

### DU-8.04 — Dilogarithm integrals and reflection (8.12–8.18, p. 242).

Existing `DLMF.Polylog.Real.dilog` with its logarithmic integral,
`DLMF.Polylog.Real.dilog_add_dilog_one_sub`, and complex/real bridge
`DLMF.Zeta.polylog_two_ofReal_eq_dilog`. New double integral target
`DLMF.Polylog.Real.dilog_eq_double_integral` in `Polylog/BookIdentities.lean` captures the
source's second representation on the full real interval x<1.

Admission status: `DLMF.Polylog.Real.dilog_eq_double_integral`.

### DU-8.05 — Dilogarithm Landen formula (8.19–8.20, p. 243).

Existing `DLMF.Polylog.Real.dilog_add_dilog_div_sub_one` and `DLMF.Polylog.Real.dilog_one_half` in
`Polylog/Dilog.lean`. They use the same real principal branch and cover all x<1 for Landen's
formula.

The named declarations have no `sorryAx` dependency.

### DU-8.06 — Golden-ratio dilogarithms (8.21–8.27, p. 243).

Existing `DLMF.Polylog.Real.dilog_goldenRatio` in `Polylog/Dilog.lean` is a conjunction of all
three source values, with the same positive golden ratio and squared real logarithm. No duplicate
three-special-value theorem was added.

The named declarations have no `sorryAx` dependency.

### DU-8.07 — Trilogarithm Landen formula (8.28–8.35, pp. 244–245).

Existing `DLMF.Polylog.Real.trilog_landen` and `DLMF.Polylog.Real.trilog_one_half` in
`Polylog/Trilog.lean`. Replacing x by 1-x in the existing Landen identity gives the synopsis's
x/(x-1) form. New `DLMF.Polylog.polylog_three_ofReal_eq_trilog` bridges the full real branch; new
`DLMF.Polylog.Real.trilog_goldenRatio_inv_sq` in `Polylog/BookIdentities.lean` gives the remaining
golden-ratio trilogarithm value.

Admission status: `DLMF.Polylog.polylog_three_ofReal_eq_trilog`,
`DLMF.Polylog.Real.trilog_goldenRatio_inv_sq`.

### DU-8.08 — Complex principal branch (8.36–8.38, p. 245).

Existing canonical `DLMF.Zeta.polylog`, `DLMF.Zeta.slitOne`, `DLMF.Zeta.polylog_eq_integral`,
`DLMF.Zeta.analyticOnNhd_polylog` and Lerch kernel absolute-integrability results. The
natural-order integral is the source complex principal branch. New
`DLMF.Polylog.polylog_natCast_conj` in `Polylog/BookIdentities.lean` records conjugation at every
natural order.

Admission status: `DLMF.Polylog.polylog_natCast_conj`.

### DU-8.09 — Theorem 8.5: closed-disk series (8.39, pp. 245–246).

Existing boundary series handles n>=2. New `DLMF.Polylog.tendsto_sum_polylog_natCast_closed_disk`
in `Polylog/BookIdentities.lean` includes n=1 and every |z|<=1,z!=1, preserving the ordered
conditional-convergence case.

Admission status: `DLMF.Polylog.tendsto_sum_polylog_natCast_closed_disk`.

### DU-8.10 — Unit-interval integral (8.41, p. 247).

New `DLMF.Polylog.polylog_natCast_eq_unit_integral` in `Polylog/BookIdentities.lean`; explicit
n>=1, slit-plane domain, logarithmic power, denominator 1-zt and factorial. The n=1 kernel is
included.

Admission status: `DLMF.Polylog.polylog_natCast_eq_unit_integral`.

### DU-8.11 — Complex Clausen convention (8.42–8.48, pp. 247–248).

The complex Clausen convention is represented directly as `DLMF.Zeta.polylog n (exp (θ*I))`, not
confused with a real or imaginary part. New `DLMF.Polylog.tendsto_sum_polylog_exp_mul_I`,
`DLMF.Polylog.polylog_natCast_I`, `DLMF.Polylog.polylog_one_I`, `DLMF.Polylog.polylog_two_I` in
`Polylog/BookIdentities.lean`; n=0 is the existing rational `DLMF.Zeta.polylog_zero_order`. All
eta and beta factors use canonical definitions and Catalan's existing constant. At order one, the
eta factor is alternatingHurwitzZeta 1 1 rather than the unrelated totalized unconditional eta
tsum.

Admission status: `DLMF.Polylog.tendsto_sum_polylog_exp_mul_I`, `DLMF.Polylog.polylog_natCast_I`,
`DLMF.Polylog.polylog_one_I`, `DLMF.Polylog.polylog_two_I`.

### DU-8.12 — Theorem 8.10: Clausen derivative (8.49, p. 248).

New `DLMF.Polylog.hasDerivAt_polylog_exp_mul_I` in `Polylog/BookIdentities.lean`, for every n>=0
and 0<θ<2π. Its derivative is exactly i Li_n(exp(iθ)), including the order-one derivative's
rational order-zero term.

Admission status: `DLMF.Polylog.hasDerivAt_polylog_exp_mul_I`.

### DU-8.13 — Inverse polytangent (8.50–8.57, pp. 248–249).

New `DLMF.Polylog.Real.inversePolytangent` and proved defining lemma;
`DLMF.Polylog.Real.inversePolytangent_zero`, `DLMF.Polylog.Real.inversePolytangent_neg`,
`DLMF.Polylog.Real.inversePolytangent_one`, `DLMF.Polylog.Real.inversePolytangent_succ`,
`DLMF.Polylog.Real.hasDerivAt_inversePolytangent_succ`,
`DLMF.Polylog.Real.inversePolytangent_one_arg`, `DLMF.Polylog.Real.hasSum_inversePolytangent`,
`DLMF.Polylog.Real.inversePolytangent_eq_hypergeometric`,
`DLMF.Polylog.Real.inversePolytangent_eq_polylog`,
`DLMF.Polylog.Real.inversePolytangent_eq_integral` in `Polylog/BookIdentities.lean`. These
separately capture the rational initial function, oddness, arctangent, integral
recursion/removable value, beta endpoint, series, hypergeometric function and full real-axis
integral/polylog identities.

Admission status: `DLMF.Polylog.Real.inversePolytangent_zero`,
`DLMF.Polylog.Real.inversePolytangent_neg`, `DLMF.Polylog.Real.inversePolytangent_one`,
`DLMF.Polylog.Real.inversePolytangent_succ`,
`DLMF.Polylog.Real.hasDerivAt_inversePolytangent_succ`,
`DLMF.Polylog.Real.inversePolytangent_one_arg`, `DLMF.Polylog.Real.hasSum_inversePolytangent`,
`DLMF.Polylog.Real.inversePolytangent_eq_hypergeometric`,
`DLMF.Polylog.Real.inversePolytangent_eq_polylog`,
`DLMF.Polylog.Real.inversePolytangent_eq_integral`.

### DU-8.14 — Theorem 8.11: principal logarithm (8.59–8.61, p. 250).

Existing Mathlib `Complex.log`, `Complex.log_eq_integral` in
`Analysis/SpecialFunctions/Complex/LogBounds.lean`, applied with argument z-1, is exactly the
principal segment integral. Existing `DLMF.Zeta.polylog_one_eq_neg_log` gives Log(z)=-Li_1(1-z).
Polar evaluation is Mathlib's log/exp/argument API, on r>0 and -π<θ<π. No new logarithm definition
or admitted copy is needed.

The named declarations have no `sorryAx` dependency.

### DU-8.15 — Polynomial-weighted cotangent integrals (8.64–8.70, pp. 251–253).

New `DLMF.Polylog.integral_pow_mul_cot`, `DLMF.Polylog.integral_mul_cot_pi_div_two`,
`DLMF.Polylog.integral_mul_cot_pi_div_four` in `Polylog/BookIdentities.lean`, with the complete
finite polylogarithm expression, zeta endpoint term and both special values. The right side's
imaginary part is zero by the equality to the real-valued integral.

Admission status: `DLMF.Polylog.integral_pow_mul_cot`, `DLMF.Polylog.integral_mul_cot_pi_div_two`,
`DLMF.Polylog.integral_mul_cot_pi_div_four`.

### DU-8.16 — Polynomial-weighted coth integrals (8.71–8.76, pp. 253–255).

New `DLMF.Polylog.integral_pow_mul_coth` in `Polylog/BookIdentities.lean`. Its p=2 specialization
and the substitution u=sinh t give the source inverse-hyperbolic-square formula. The polynomial
sum, factorials, powers of two and exp(-2x) arguments are explicit.

Admission status: `DLMF.Polylog.integral_pow_mul_coth`.

### DU-8.17 — Apéry series (8.77–8.78, pp. 255–256).

Existing Apéry central-binomial identity `DLMF.Zeta.hasSum_riemannZeta_three_central_binom` in
`Zeta/IntegerArguments.lean`. New `DLMF.Polylog.integral_arsinh_sq_div` in
`Polylog/BookIdentities.lean` gives the source integral at 1/2. Neither statement is presented as
irrationality of zeta(3).

Admission status: `DLMF.Polylog.integral_arsinh_sq_div`.

### DU-8.18 — BBP family and integral algorithm (8.79, 8.92–8.95, pp. 256, 258).

New `DLMF.Constants.bbpSeries`, `DLMF.Constants.bbpSeries_def`,
`DLMF.Constants.summable_bbpSeries`, `DLMF.Constants.bbpSeries_eq_integral` in
`Constants/BBPFamily.lean`. The definition fixes the grouped order, arithmetic progression h,
coefficients b_l, integer radix with |a|>=2, positive order and explicit polynomial numerator; no
unknown coefficient family is assumed.

Admission status: `DLMF.Constants.summable_bbpSeries`, `DLMF.Constants.bbpSeries_eq_integral`.

### DU-8.19 — Root-of-unity evaluation (8.98–8.99, p. 259).

New `DLMF.Constants.bbpSeries_eq_sum_polylog` in `Constants/BBPFamily.lean`. The formula uses
every chosen root ω with ω^h=a and explicitly constructs r_j=ω exp(2πij/h). Independence of the
chosen root follows because the same series equals the expression for each choice; the modulus
condition follows from |ω|^h=|a|>=2.

Admission status: `DLMF.Constants.bbpSeries_eq_sum_polylog`.

### DU-8.20 — Exact BBP and Machin examples (8.81–8.91, pp. 256–257).

Existing `DLMF.Constants.hasSum_log_three`, `DLMF.Constants.hasSum_log_two`,
`DLMF.Constants.hasSum_bbp_pi` in `Constants/BBP.lean`. The three stated Machin identities are
already Mathlib `Real.arctan_inv_2_add_arctan_inv_3`,
`Real.two_mul_arctan_inv_2_sub_arctan_inv_7`, `Real.four_mul_arctan_inv_5_sub_arctan_inv_239`;
their absolutely convergent arctangent expansions are Mathlib's power series. The different
existing local `DLMF.Constants.gauss_machin` formula is not substituted for these three.

The named declarations have no `sorryAx` dependency.

## Chapter 9

### DU-9.01 — Weighted polynomial inner product (Definition 9.1, (9.1–9.4), pp. 281–282).

Existing `DLMF.OrthogonalPolynomials.IsOrthogonalPolynomials`, its basis,
`DLMF.OrthogonalPolynomials.IsOrthogonalPolynomials.expansion`,
`DLMF.OrthogonalPolynomials.IsOrthogonalPolynomials.integral_eval_sq_pos`,
`DLMF.OrthogonalPolynomials.IsOrthogonalPolynomials.memLp_eval` in
`OrthogonalPolynomials/Basic/General.lean`. A source weight is the measure volume restricted to
its open interval with density ENNReal.ofReal(w); positive definiteness follows because a nonzero
real polynomial cannot vanish on an interval and w is positive there. The moment assumptions
guarantee integrability of every polynomial product. The finite expansion is the existing exact
basis expansion.

The named declarations have no `sorryAx` dependency.

### DU-9.02 — Theorem 9.4: three-term recurrence (9.10–9.12, p. 283).

New exact `DLMF.OrthogonalPolynomials.three_term_recurrence_explicit` in
`OrthogonalPolynomials/GeneralRecurrenceCoefficients.lean` states all three source coefficients
using actual leading and subleading coefficients and squared norms, without imposing monic
normalization. The existing existential recurrence
`DLMF.OrthogonalPolynomials.three_term_recurrence` alone did not capture these explicit formulas.

Admission status: `DLMF.OrthogonalPolynomials.three_term_recurrence_explicit`.

### DU-9.03 — Theorem 9.5: zeros (p. 285).

Existing `DLMF.OrthogonalPolynomials.orthogonal_polynomials_roots` in
`OrthogonalPolynomials/General.lean`. Apply it to the source weighted interval measure, whose
support meets every open subinterval because w>0. Exact degree n excludes additional real or
complex roots after the n distinct interval roots are obtained; each has multiplicity one.

The named declarations have no `sorryAx` dependency.

### DU-9.04 — Theorem 9.6: Rodrigues criterion (9.19–9.21, pp. 285–286).

New `DLMF.OrthogonalPolynomials.orthogonal_and_norm_of_rodrigues` in
`OrthogonalPolynomials/GeneralRodrigues.lean`. It explicitly represents extended-real endpoints,
real endpoint filters pulled back through ℝ→EReal, all polynomially weighted boundary derivative
limits, smooth positive weight, every moment's absolute integrability, the exact Rodrigues
expression and degree, and both orthogonality and the norm formula.

Admission status: `DLMF.OrthogonalPolynomials.orthogonal_and_norm_of_rodrigues`.

### DU-9.05 — Jacobi definition and Theorem 9.7 (9.23–9.24, p. 287).

Existing `DLMF.OrthogonalPolynomials.jacobiPolynomialP`,
`DLMF.OrthogonalPolynomials.jacobiPolyPR`, their evaluation bridge and degree API, plus
`DLMF.OrthogonalPolynomials.jacobi_rodrigues` in the Differential area. The hypergeometric lower
parameter α+1 is positive, so the terminating finite convention has no denominator issue for
α,β>-1.

The named declarations have no `sorryAx` dependency.

### DU-9.06 — Theorem 9.8: Jacobi equation (9.28, p. 289).

Existing `DLMF.OrthogonalPolynomials.jacobi_differential_equation` in
`OrthogonalPolynomials/Differential/ClassicalEquations.lean`, with the source α,β and
normalization. The polynomial nature makes the equation valid globally, including endpoints.

The named declarations have no `sorryAx` dependency.

### DU-9.07 — Jacobi symmetry, endpoints and derivatives (9.29–9.31, p. 289; Exercise 9.12, p. 305).

Existing `DLMF.OrthogonalPolynomials.jacobi_reflection`,
`DLMF.OrthogonalPolynomials.jacobiPolynomialP_one_eq` and derivative-shift identities in
`OrthogonalPolynomials/Differential/`. The value at -1 follows by reflection and the +1 value. The
derivative coefficient is (n+α+β+2)/2, retaining the source's n+1 degree index.

The named declarations have no `sorryAx` dependency.

### DU-9.08 — Theorem 9.9: Jacobi orthogonality, norm and recurrence (9.32–9.34, pp. 289–290).

Existing `DLMF.OrthogonalPolynomials.jacobiPolynomialP_orthogonal`, norm and recurrence APIs in
`Classical.lean`, `ClassicalInstances.lean` and `Differential/ClassicalEquations.lean`. Existing
`DLMF.OrthogonalPolynomials.jacobi_norm_all` in
`OrthogonalPolynomials/Integrals/AngularRepresentations.lean` handles n=0,α+β=-1; the synopsis's
beta expression is finite there. The quoted rational coefficients follow by rearranging
`DLMF.OrthogonalPolynomials.jacobi_recurrence` at degree n+1. No totalized 0/0 Gamma quotient is
used at the removable exception.

The named declarations have no `sorryAx` dependency.

### DU-9.09 — Gegenbauer normalization (9.41–9.48, pp. 292–293).

Existing `DLMF.OrthogonalPolynomials.ultrasphericalPolynomial` and its Jacobi relation;
`DLMF.OrthogonalPolynomials.ultrasphericalPolynomial_one_eq`,
`DLMF.OrthogonalPolynomials.ultrasphericalPolynomial_even_at_zero`, reflection/parity,
`DLMF.OrthogonalPolynomials.ultrasphericalPolynomial_recurrence`,
`DLMF.OrthogonalPolynomials.ultrasphericalPolynomial_differential_equation` in the Differential
area; orthogonality/norm in ClassicalInstances. The source excludes λ=0 and permits negative
λ>-1/2, so an API requiring λ>0 alone is insufficient; the full signed norm expression and its
removable factors must be retained. The exact full-range norm is newly acquired as
`DLMF.OrthogonalPolynomials.ultrasphericalPolynomial_norm_of_nonzero` in
`OrthogonalPolynomials/GegenbauerNorm.lean`; the older
`DLMF.OrthogonalPolynomials.ultrasphericalPolynomial_norm` requires positive λ. Existing
`DLMF.OrthogonalPolynomials.ultrasph_isOrthogonalPolynomials` in ClassicalInstances already has
the full orthogonality range.

Admission status: `DLMF.OrthogonalPolynomials.ultrasphericalPolynomial_norm_of_nonzero`.

### DU-9.10 — Theorem 9.11: Gegenbauer generating function (9.49, p. 293).

Existing `DLMF.OrthogonalPolynomials.ultrasphericalPolynomial_generating_function` in
`OrthogonalPolynomials/Series/ClassicalGenerating.lean` and full scalar-series refinements in
`GegenbauerSeries.lean`. Restricting their larger true domain to |x|<=1,|t|<1/3 gives exactly the
source's Theorem 9.11 range.

The named declarations have no `sorryAx` dependency.

### DU-9.11 — Legendre specialization (9.51–9.60, pp. 294–296).

Existing `DLMF.OrthogonalPolynomials.legendrePolynomialP`, Jacobi/Gegenbauer specialization,
Rodrigues formula, orthogonality/norm, `DLMF.OrthogonalPolynomials.legendre_differential_equation`
and recurrence, and `DLMF.OrthogonalPolynomials.legendre_generating_function`. The local
polynomial special-value API gives the integer values directly; Mathlib has no polynomial named
Polynomial.legendre at this pin. The potential series is the generating function at x=cosθ,t=a/r,
multiplied by 1/r, with |a/r|<1/3; the algebraic distance is sqrt(r²-2ar cosθ+a²).

The named declarations have no `sorryAx` dependency.

### DU-9.12 — Chebyshev first kind and Theorem 9.13 (9.61–9.69, pp. 296–298).

Existing Mathlib `Polynomial.Chebyshev.T`, its recurrence, `Polynomial.Chebyshev.T_real_cos`,
roots and differential equation; project `DLMF.OrthogonalPolynomials.chebyshevT_hypergeometric`,
`DLMF.OrthogonalPolynomials.chebyshevT_eq_jacobi` in
`OrthogonalPolynomials/Differential/ClassicalEquations.lean`, and exact continuous
orthogonality/norm in the General/Classical area. The n=0 norm π is distinct from the n>=1 norm
π/2. Precise upstream norm/orthogonality pointers are
`Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT_of_ne`,
`Polynomial.Chebyshev.integral_eval_T_real_mul_self_measureT_zero` and
`Polynomial.Chebyshev.integral_T_real_mul_self_measureT_of_ne_zero` in Mathlib
Chebyshev/Orthogonality.lean.

The named declarations have no `sorryAx` dependency.

### DU-9.13 — Chebyshev second kind (9.70–9.81, pp. 298–299).

Existing Mathlib `Polynomial.Chebyshev.U`, derivative relation with T, recurrence, cosine/sine
evaluation and `DLMF.OrthogonalPolynomials.integral_eval_U_mul_of_ne`,
`DLMF.OrthogonalPolynomials.integral_eval_U_mul_self` in `OrthogonalPolynomials/General.lean`;
Gegenbauer and hypergeometric bridges are in the Differential area. The relation T_n=U_n-xU_(n-1)
uses n>=1, avoiding a natural-subtraction ambiguity at zero.

The named declarations have no `sorryAx` dependency.

### DU-9.14 — Laguerre definition and equation (9.82–9.86, pp. 299–300).

Existing `DLMF.OrthogonalPolynomials.laguerrePolynomialL`, polynomial representative
`DLMF.OrthogonalPolynomials.laguerrePolyLR`, its degree, Rodrigues formula and
`DLMF.OrthogonalPolynomials.laguerrePolynomialL_differential_equation`. The source α>-1 ensures
the lower M parameter α+1 is regular and the polynomial has degree n.

The named declarations have no `sorryAx` dependency.

### DU-9.15 — Theorem 9.14: Laguerre orthogonality (9.87–9.89, pp. 300–301).

Existing `DLMF.OrthogonalPolynomials.laguerrePolynomialL_orthogonal`, the squared norm in
ClassicalInstances, `DLMF.OrthogonalPolynomials.laguerrePolynomialL_recurrence`,
`DLMF.OrthogonalPolynomials.laguerrePolynomialL_generating_function` and
`DLMF.OrthogonalPolynomials.hasSum_laguerreExtended_generating_function` in `Classical.lean`. The
generating function covers arbitrary real x and |t|<1; exp(xt/(t-1)) agrees with exp(-xt/(1-t)).

The named declarations have no `sorryAx` dependency.

### DU-9.16 — Hermite definition and differential API (9.90–9.96, pp. 301–302; Theorem 9.15).

Existing canonical physicists' `DLMF.OrthogonalPolynomials.hermitePolynomialH` and its polynomial
API; `DLMF.OrthogonalPolynomials.deriv_gaussian_eq_hermitePolynomialH`,
`DLMF.OrthogonalPolynomials.iteratedDeriv_cexp_neg_sq`,
`DLMF.OrthogonalPolynomials.hermitePolynomialH_generating_function` in `Classical.lean`;
derivative, parity, degree, recurrence and
`DLMF.OrthogonalPolynomials.hermitePolynomialH_differential_equation` in Basic/Differential. This
is not the probabilists' Hermite normalization.

The named declarations have no `sorryAx` dependency.

### DU-9.17 — Theorem 9.16: Hermite hypergeometric formulas (9.97–9.98, p. 303).

Existing `DLMF.Confluent.kummerM_hermite_even`, `DLMF.Confluent.kummerM_hermite_odd` in
`Confluent/Relations.lean`, and
`DLMF.OrthogonalPolynomials.hermitePolynomialH_even_eq_laguerrePolynomialL`,
`DLMF.OrthogonalPolynomials.hermitePolynomialH_odd_eq_laguerrePolynomialL` in
`OrthogonalPolynomials/Explicit.lean`. Both parity cases and both equivalent Laguerre forms are
present with the source factorial/power-of-two factors.

The named declarations have no `sorryAx` dependency.

### DU-9.18 — Theorem 9.17: Hermite orthogonality (pp. 303–304).

Existing exact `DLMF.OrthogonalPolynomials.hermitePolynomialH_orthogonality` and
`DLMF.OrthogonalPolynomials.hermite_orthogonality` in
`OrthogonalPolynomials/Integrals/AngularRepresentations.lean` already state the complete
diagonal/off-diagonal formula with physicists H_n and measure exp(-x²)dx. Integrability also
follows from `DLMF.OrthogonalPolynomials.hermite_isOrthogonalPolynomials` and the general product
integrability API.

The named declarations have no `sorryAx` dependency.

### DU-9.19 — Charlier convention (Exercise 9.14, pp. 305–306).

Existing canonical `DLMF.OrthogonalPolynomials.charlier` has the DLMF normalization, so it is not
identified literally with the source C_n. New explicit bridge
`DLMF.OrthogonalPolynomials.charlier_coefficient_eq_sum` and arbitrary-real-x generating function
`DLMF.OrthogonalPolynomials.hasSum_charlier_coefficient` in
`OrthogonalPolynomials/CharlierCoefficientNormalization.lean` use the factor (-μ)^n/n!. Existing
`DLMF.OrthogonalPolynomials.charlier_orthogonality` in `Hahn/Orthogonality.lean`, multiplied by
the two normalization factors, yields the source diagonal e^μ μ^n/n! and zero off-diagonal sum.

Admission status: `DLMF.OrthogonalPolynomials.charlier_coefficient_eq_sum`,
`DLMF.OrthogonalPolynomials.hasSum_charlier_coefficient`.

### DU-9.20 — Irrational Chebyshev zeros (Exercise 9.15, p. 306).

Existing Mathlib `Polynomial.Chebyshev.irrational_of_isRoot_T_real` in
`Analysis/SpecialFunctions/Trigonometric/Chebyshev/RootsExtrema.lean`; every root of even-degree
T_(2n) is nonzero by its value at zero. The particular cos(π/(4n)) is the first positive root of
T_(2n). Alternatively `irrational_cos_rat_mul_pi` (Niven) with denominator 4n gives the first
assertion directly.

The named declarations have no `sorryAx` dependency.

## Chapter 10

### DU-10.01 — Shifted factorial, limit and infinite product (10.1–10.3, 10.9, pp. 317–319).

Existing `DLMF.QSeries.qPochhammer`, `DLMF.QSeries.qPochhammerInf`,
`DLMF.QSeries.multipliable_one_sub_mul_pow`, `DLMF.QSeries.tendsto_qPochhammer`,
`DLMF.QSeries.qPochhammerInf_ne_zero`, and the zero-factor/shift API. Upstream TauCeti
`TauCeti.multipliable_one_sub_pow_mul`, `TauCeti.tprod_one_sub_pow_mul_ne_zero` supplies the same
infinite product. The finite classical limit is
`DLMF.QHypergeometric.tendsto_qPochhammer_normalized` in
`QHypergeometric/ClassicalLimits/ShiftedFactorials.lean`. Zero iff a=q^-N follows by the nonzero
theorem and an actual vanishing factor.

The named declarations have no `sorryAx` dependency.

### DU-10.02 — Gaussian binomial coefficients (10.4–10.8, p. 318).

Existing `DLMF.QSeries.qBinom`, `DLMF.QSeries.qBinom_succ_succ`, `DLMF.QSeries.qBinom_one`,
`DLMF.QSeries.continuous_qBinom`, `DLMF.QSeries.tendsto_qBinom`, `DLMF.QSeries.qBinom_eq` and
`DLMF.QSeries.qPochhammer_eq_sum_qBinom` in Basic/CalculusProperties, QExponential and QBinomial.
These supply the finite quotient, endpoint values, q-Pascal recurrence, q→1 limit and full finite
q-binomial expansion.

The named declarations have no `sorryAx` dependency.

### DU-10.03 — Jackson derivative and Leibniz rule (10.10–10.15, p. 319).

Existing `DLMF.QSeries.qDeriv`, `DLMF.QSeries.qDeriv_mul`, `DLMF.QHypergeometric.qDeriv_leibniz`,
`DLMF.QHypergeometric.qDerivIterate`, and the extended origin value. New real-power rule
`DLMF.QSeries.qDeriv_cpow_real` and real differentiability limit
`DLMF.QSeries.tendsto_qDeriv_of_hasDerivAt_real` in `QSeries/BookIdentities.lean`; the latter does
not require a holomorphic extension of a merely real-differentiable function.

Admission status: `DLMF.QSeries.qDeriv_cpow_real`,
`DLMF.QSeries.tendsto_qDeriv_of_hasDerivAt_real`.

### DU-10.04 — Theorem 10.2: constants (p. 320).

New `DLMF.QSeries.qDeriv_eq_zero_iff_eq_limit` in `QSeries/BookIdentities.lean`, retaining the
indispensable finite right limit at zero. New `DLMF.QSeries.qDeriv_sin_log_eq_zero` and
`DLMF.QSeries.exists_pos_sin_log_ne_zero` record both the zero Jackson derivative and nonconstancy
of the explicit logarithmically periodic counterexample when that limit assumption is removed.

Admission status: `DLMF.QSeries.qDeriv_eq_zero_iff_eq_limit`,
`DLMF.QSeries.qDeriv_sin_log_eq_zero`, `DLMF.QSeries.exists_pos_sin_log_ne_zero`.

### DU-10.05 — Theorem 10.4: Jackson integral (10.18–10.19, p. 320).

Existing `DLMF.QSeries.jacksonIntegral`, `DLMF.QSeries.qDeriv_jacksonIntegral`,
`DLMF.QSeries.jacksonIntegral_qDeriv`, and `DLMF.QHypergeometric.jackson_series_hasSum`. New
finite-right-limit scope and uniqueness: `DLMF.QSeries.summable_jackson_of_tendsto`,
`DLMF.QSeries.tendsto_jacksonIntegral_zero`, `DLMF.QSeries.eq_jacksonIntegral_of_qDeriv_eq` in
`QSeries/BookIdentities.lean`. They do not impose global continuity on the whole interval when the
source assumes only a limit at zero.

Admission status: `DLMF.QSeries.summable_jackson_of_tendsto`,
`DLMF.QSeries.tendsto_jacksonIntegral_zero`, `DLMF.QSeries.eq_jacksonIntegral_of_qDeriv_eq`.

### DU-10.06 — Series differentiation, integration and Lambert identity (10.21–10.25, pp. 321–322).

New `DLMF.QSeries.hasSum_qDeriv_powerSeries`, `DLMF.QSeries.hasSum_jacksonIntegral_powerSeries` in
`QSeries/BookIdentities.lean`, retaining a genuine convergent power-series representation on its
disk. The removable zero derivative value uses the existing
`DLMF.QHypergeometric.qDerivExtended_zero` and the ordinary derivative of a power series. The
Lambert identity is new `DLMF.QSeries.hasSum_qLogarithm` together with
`DLMF.QSeries.qLogarithm_def` in `QSeries/Logarithm.lean`.

Admission status: `DLMF.QSeries.hasSum_qDeriv_powerSeries`,
`DLMF.QSeries.hasSum_jacksonIntegral_powerSeries`, `DLMF.QSeries.hasSum_qLogarithm`.

### DU-10.07 — Two exponentials (10.26–10.35, pp. 322–324).

Existing unscaled products `(qPochhammerInf x q)^-1` and `qPochhammerInf (-x) q`, the series
`DLMF.QSeries.tsum_div_qPochhammer`, `DLMF.QSeries.tsum_qExp`, and `DLMF.QSeries.qExp_mul_qExp`;
scaled DLMF `DLMF.QHypergeometric.qExp`, `DLMF.QHypergeometric.qExpBig` in
QHypergeometric/Basic/Elementary use (1-q)x. New full product-domain Jackson equation
`DLMF.QSeries.qDeriv_inv_qPochhammerInf` in `QSeries/BookIdentities.lean`. The product inverse
identity outside poles is algebraic; the q→1 limit follows from
`DLMF.QHypergeometric.qPhi_classical_limit` for the empty lists and the empty hypergeometric
exponential identity (take inverses for the little exponential).

Admission status: `DLMF.QSeries.qDeriv_inv_qPochhammerInf`.

### DU-10.08 — q-logarithm (10.30–10.32, pp. 323–324).

New `DLMF.QSeries.qLogarithm`, proved `DLMF.QSeries.qLogarithm_def`, and admitted
`DLMF.QSeries.summable_qLogarithm`, `DLMF.QSeries.qLogarithm_eq_logarithmicDeriv`,
`DLMF.QSeries.qLogarithm_mul`, `DLMF.QSeries.hasSum_qLogarithm`, `DLMF.QSeries.tendsto_qLogarithm`
in `QSeries/Logarithm.lean`. The logarithmic derivative uses Duverney's unscaled exponential, not
the DLMF (1-q)-scaled function. The canonical definition and proved defining equation live in
`QSeries/Basic/Logarithm.lean`; admitted analytic identities remain in the theorem layer.

Admission status: `DLMF.QSeries.summable_qLogarithm`,
`DLMF.QSeries.qLogarithm_eq_logarithmicDeriv`, `DLMF.QSeries.qLogarithm_mul`,
`DLMF.QSeries.hasSum_qLogarithm`, `DLMF.QSeries.tendsto_qLogarithm`.

### DU-10.09 — Definition 10.7: basic hypergeometric series (p. 325).

Existing `DLMF.QHypergeometric.qPhiTerm`, `DLMF.QHypergeometric.qPhi`,
`DLMF.QHypergeometric.qPhiExponent`, `DLMF.QHypergeometric.QDenominatorRegular`,
`DLMF.QHypergeometric.QDenominatorRegularThrough`, `DLMF.QHypergeometric.QTerminating`,
`DLMF.QHypergeometric.qPhiPartial`; `DLMF.QHypergeometric.qPhi_hasSum`,
`DLMF.QHypergeometric.qPhi_analytic_disc`, `DLMF.QHypergeometric.qPhi_analytic_entire`,
`DLMF.QHypergeometric.qPhi_terminates` in Convergence. The phase exponent is an integer,
preserving the definition for all parameter counts. Exceptional lower parameters after termination
are represented by the finite partial sum.

The named declarations have no `sorryAx` dependency.

### DU-10.10 — Theorem 10.8: classical limit (10.36, pp. 325–326).

Existing `DLMF.QHypergeometric.qPhi_classical_limit` in `QHypergeometric/Convergence.lean`. Its
argument is exactly ((q:ℂ)-1)^(s+1-r)x, so the phase sign is correct; the synopsis's |x|<1 is
within its possibly larger convergence range.

The named declarations have no `sorryAx` dependency.

### DU-10.11 — q-binomial theorem (10.41–10.43, p. 327).

Existing `DLMF.QSeries.q_binomial_theorem`, `DLMF.QHypergeometric.one_phi_zero` and one-phi-zero
series identities in `QHypergeometric/BasicSummations/OnePhiZero.lean`. They supply both the
series and infinite-product quotient for every real a and |x|<1.

The named declarations have no `sorryAx` dependency.

### DU-10.12 — Heine transformation (10.46, p. 328).

Existing `DLMF.QSeries.heine_transformation`, `DLMF.QHypergeometric.heine_first` and corresponding
product/series identities in `QHypergeometric/BasicSummations/Heine.lean`. The source |b|,|x|<1
and all nonzero displayed denominators select the direct series identity without ambiguous
continuation.

The named declarations have no `sorryAx` dependency.

### DU-10.13 — q-Euler transformation (10.51–10.52, p. 329).

Existing `DLMF.QSeries.heine_transformation_three` and the q-Euler/Heine third transformation in
`QHypergeometric/BasicSummations/Heine.lean`. Both x and abx/c lie in the unit disk; nonzero a,b,c
and regular c are retained, as are all explicit infinite-product denominator conditions.

The named declarations have no `sorryAx` dependency.

### DU-10.14 — q-Gauss sum (10.53, p. 330).

Existing `DLMF.QSeries.q_gauss_summation` in `QHypergeometric/BasicSummations/QGauss.lean` is the
full-domain q-Gauss sum, supplementing the more restrictive legacy
`DLMF.QSeries.q_gauss_summation`. The larger Remark10.12 range |c/(ab)|<1 is covered without
requiring |b|<1.

The named declarations have no `sorryAx` dependency.

### DU-10.15 — q-Chu–Vandermonde (10.54, p. 330).

Existing `DLMF.QHypergeometric.q_chu_vandermonde_first` in
`QHypergeometric/BasicSummations/QGauss.lean` has the finite denominator condition
`DLMF.QHypergeometric.QDenominatorRegularThrough`; it covers the full source domain. The legacy
`DLMF.QSeries.q_chu_vandermonde` has extra disk/pole exclusions and is not counted as exact source
coverage.

The named declarations have no `sorryAx` dependency.

### DU-10.16 — q-Saalschütz/Jackson sum (10.55, pp. 330–331).

Existing `DLMF.QHypergeometric.QuadraticTransformation.q_pfaff_saalschutz_ratio` and
`DLMF.QHypergeometric.PfaffSaalschutz.sum_eq_quotient_of_ne_zero` in
`QHypergeometric/PfaffSaalschutz.lean` and HigherSummations. They use finite denominator
regularity and nonzero a,b,c,q, retaining later exceptional lower parameters.

The named declarations have no `sorryAx` dependency.

### DU-10.17 — Basic Jacobi definitions (Note 10.3, p. 332).

Existing `DLMF.OrthogonalPolynomials.littleQJacobi`, `DLMF.OrthogonalPolynomials.bigQJacobi` in
`OrthogonalPolynomials/Basic/QFamilies.lean`; these definitions use explicit terminating basic
hypergeometric polynomials and agree with the two displayed source normalizations. Their parameter
restrictions are finite denominator conditions, not unnecessary global lattice exclusions.

The named declarations have no `sorryAx` dependency.

### DU-10.18 — Divisor-series identity and Erdős–Borwein constant (Exercises 10.10, 10.13, p. 333).

New `DLMF.QSeries.tsum_pow_div_one_sub_pow_sq`, `DLMF.QSeries.Real.erdosBorweinConstant`, defining
lemma, `DLMF.QSeries.Real.summable_erdosBorweinConstant`,
`DLMF.QSeries.Real.hasSum_erdosBorweinConstant_accelerated`,
`DLMF.QSeries.Real.irrational_erdosBorweinConstant` in `QSeries/BookIdentities.lean`. The Lambert
identity, convergence, accelerated representation and irrationality are separate targets;
irrationality is not inferred from the identity alone.

Admission status: `DLMF.QSeries.tsum_pow_div_one_sub_pow_sq`,
`DLMF.QSeries.Real.summable_erdosBorweinConstant`,
`DLMF.QSeries.Real.hasSum_erdosBorweinConstant_accelerated`,
`DLMF.QSeries.Real.irrational_erdosBorweinConstant`.

## Appendix A

### DU-A.01 — Lerch function (A.1–A.2, pp. 345–346).

Existing `DLMF.Zeta.lerchPhi`, `DLMF.Zeta.hasSum_lerchPhi`, `DLMF.Zeta.lerchPhi_eq_integral`,
`DLMF.Zeta.analyticOnNhd_lerchPhi`, `DLMF.Zeta.tendsto_lerchPhi_exp_zero`,
`DLMF.Zeta.hurwitzZetaComplex_eq_lerchPhi`, `DLMF.Zeta.polylog_eq_mul_lerchPhi_of_mem_slitOne`.
The limit at -1 uses continuity in the slit plane and new
`DLMF.Zeta.Real.alternatingHurwitzZeta_eq_lerchPhi`; the source s,a>0 is retained for the
integral, and s>1 for the limit at one.

Admission status: `DLMF.Zeta.Real.alternatingHurwitzZeta_eq_lerchPhi`.

## Appendix B

### DU-B.01 — Definition B.1 and local coefficients (B.1–B.3, pp. 347–349).

Existing Mathlib `AnalyticAt`, `AnalyticOnNhd`, `HasFPowerSeriesOnBall`,
`FormalMultilinearSeries.ofScalars`, and
`HasFPowerSeriesOnBall.factorial_smul`/iterated-derivative coefficient API. Absolute summability
at radius ρ and bounding one summand by the tsum gives the finite coefficient bound M_ρρ^-n. Real
analytic functions and their actual convergent Taylor coefficients, not just formal power series,
are used.

The named declarations have no `sorryAx` dependency.

### DU-B.02 — Theorems B.5–B.7: analytic operations (p. 348).

Existing Mathlib analytic addition/multiplication/inversion/division APIs, analytic-to-ContDiff,
`DLMF.AsymptoticApproximations.HasPoincareExpansion.deriv` and iterated derivative series in
`Analysis/Analytic/`. Nonzero denominators are hypotheses for the quotient; smaller balls are
taken within the actual convergence radius.

The named declarations have no `sorryAx` dependency.

### DU-B.03 — Smooth nonanalytic function (Remark B.9, p. 349).

Existing Mathlib `expNegInvGlue.contDiff` covers the building block exp(-1/x) for positive x. New
`Real.contDiff_exp_neg_inv_sq` in `DLMFMathlib/Analysis/Analytic/DerivativeCriterion.lean` proves
smoothness of the exact squared reciprocal example by composition with x²;
`Real.iteratedDeriv_exp_neg_inv_sq_zero` and `Real.not_analyticAt_exp_neg_inv_sq_zero` are
explicit admitted targets for all derivatives and nonanalyticity at zero.

Admission status: `Real.iteratedDeriv_exp_neg_inv_sq_zero`,
`Real.not_analyticAt_exp_neg_inv_sq_zero`.

### DU-B.04 — Theorem B.10: derivative criterion (B.4, pp. 349–351).

New `Real.analyticOnNhd_iff_iteratedDeriv_bound` in
`DLMFMathlib/Analysis/Analytic/DerivativeCriterion.lean`. It has the precise quantifiers over
every compact subinterval, positive constants C,δ, every derivative order and every point, and the
C∞ assumption. Both implications are included in the iff.

Admission status: `Real.analyticOnNhd_iff_iteratedDeriv_bound`.

### DU-B.05 — Gamma analyticity (Example B.11, pp. 352–353).

Existing Mathlib complex Gamma differentiability off nonpositive integers, hence analyticity, and
`DLMF.Gamma.analyticAt_Gamma`; restriction through ℝ→ℂ and `Complex.Gamma_ofReal` gives real
analyticity on all regular real intervals, not only (0,∞).

The named declarations have no `sorryAx` dependency.

### DU-B.06 — Isolated zeros and Theorem B.12 (B.11, p. 353).

Existing Mathlib real analytic identity theorem and isolated-zero/analytic-order APIs in
`Analysis/Analytic/IsolatedZeros.lean` and `Analysis/Analytic/Order.lean`. Connectedness and
nontriviality are essential for isolated finite-order zeros; agreement on a nonempty open
subinterval gives equality on the connected interval. Exact pointers are
`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`,
`AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure`,
`AnalyticAt.exists_eventuallyEq_pow_smul_ne_zero_iff`, `AnalyticAt.analyticOrderAt_eq_natCast`,
and `AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected`.

The named declarations have no `sorryAx` dependency.

### DU-B.07 — Theorem B.13 and Corollary B.14 (B.12, B.16, pp. 354–355).

New `ODE.analyticOnNhd_of_hasDerivAt_matrix_mulVec` and
`ODE.analyticOnNhd_of_iteratedDeriv_eq_sum` in
`DLMFMathlib/Analysis/ODE/RealAnalyticRegularity.lean`. The matrix coefficient entries are
genuinely real analytic; the first statement needs an actual derivative solution, and the second
retains n>=1, C^n regularity and every scalar coefficient in the monic equation.

Admission status: `ODE.analyticOnNhd_of_hasDerivAt_matrix_mulVec`,
`ODE.analyticOnNhd_of_iteratedDeriv_eq_sum`.

## Appendix C

### DU-C.01 — Inverse hyperbolic functions (C.1–C.6, pp. 357–358).

Existing Mathlib `Real.arsinh`, `Real.sinh_arsinh`, `Real.arsinh_sinh`, `Real.hasDerivAt_arsinh`;
`Real.arcosh`, `Real.cosh_arcosh`, `Real.arcosh_cosh`, `Real.hasDerivAt_arcosh` in
`Analysis/SpecialFunctions/Arsinh.lean` and `Arcosh.lean`. The arcosh domain x>=1 and derivative
domain x>1 remain distinct.

The named declarations have no `sorryAx` dependency.

### DU-C.02 — Inverse-hyperbolic series (C.7–C.10, p. 358).

New `DLMF.Elementary.arsinh_eq_ordinaryHypergeometric`,
`DLMF.Elementary.arsinh_sq_eq_generalizedHypergeometric`, `DLMF.Elementary.hasSum_arsinh_sq` in
`Elementary/InverseHyperbolicSeries.lean`. The displayed 2F1/3F2 parameters and the alternating
reciprocal central-binomial coefficients are explicit, with |x|<1 and the real principal arsinh.

Admission status: `DLMF.Elementary.arsinh_eq_ordinaryHypergeometric`,
`DLMF.Elementary.arsinh_sq_eq_generalizedHypergeometric`, `DLMF.Elementary.hasSum_arsinh_sq`.

## Appendix D

### DU-D.01 — Lemma D.1: endpoint Fresnel asymptotic (D.1, p. 359).

New `Asymptotics.isBigO_integral_exp_neg_I_mul_sq` in
`DLMFMathlib/Analysis/Asymptotics/QuadraticStationaryPhase.lean`, fixed A>0, exact
exp(-iπ/4)sqrtπ/(2sqrt x) leading term and O(x^-1) remainder.

Admission status: `Asymptotics.isBigO_integral_exp_neg_I_mul_sq`.

### DU-D.02 — Lemma D.2: smooth amplitude (D.3, p. 360).

New `Asymptotics.isBigO_integral_mul_exp_neg_I_mul_sq` in the same module. It allows complex
smooth amplitudes, stronger than the source's real k; the endpoint coefficient is k(0), with the
same phase factor and O(x^-1) remainder. Its stationary-maximum consequence is the separately
explicit DU-7.07 target.

Admission status: `Asymptotics.isBigO_integral_mul_exp_neg_I_mul_sq`.

## Validation

All 197 entries are mapped. The transitive axiom audit checked **665** distinct
declarations; **115** depend on admissions. The **31**
new modules owned by this acquisition contain **143** public declarations, including
**112** directly admitted targets. The Catalan-value
adapter additionally depends on the new admitted beta convergence theorem. The three real
digamma bridges, the smooth flat-function composition, and all new defining equations are
free of admissions. The additional Euler–Maclaurin target is shared with the Temme audit.

The Lean axiom audit and declaration locations are retained in
[reports/BookAcquisition-Duverney.tsv](reports/BookAcquisition-Duverney.tsv).
Every new module has been compiled directly with `autoImplicit=false` and
`relaxedAutoImplicit=false`; the modules are registered in their area umbrellas. The import
survey finds no foundational import violation, forbidden Basic closure dependency, missing
module or file-import cycle. The final repository-wide build is coordinated separately from
these individual checks because the other book acquisitions are being integrated in parallel.

No additional suspected mathematical erratum was found beyond the corrections already recorded
in [ERRATA-Duverney.md](ERRATA-Duverney.md). No unresolved user approval is needed for this book.

## Checked declaration index

- [AnalyticAt](.lake/packages/mathlib/Mathlib/Analysis/Analytic/Basic.lean#L110) — definition, no admission.
- [AnalyticAt.analyticOrderAt_eq_natCast](.lake/packages/mathlib/Mathlib/Analysis/Analytic/Order.lean#L92) — proved, no admission.
- [AnalyticAt.exists_eventuallyEq_pow_smul_ne_zero_iff](.lake/packages/mathlib/Mathlib/Analysis/Analytic/IsolatedZeros.lean#L178) — proved, no admission.
- [AnalyticOnNhd](.lake/packages/mathlib/Mathlib/Analysis/Analytic/Basic.lean#L120) — definition, no admission.
- [AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected](.lake/packages/mathlib/Mathlib/Analysis/Analytic/Order.lean#L654) — proved, no admission.
- [AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq](.lake/packages/mathlib/Mathlib/Analysis/Analytic/IsolatedZeros.lean#L234) — proved, no admission.
- [AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure](.lake/packages/mathlib/Mathlib/Analysis/Analytic/IsolatedZeros.lean#L247) — proved, no admission.
- [Asymptotics.isBigO_integral_exp_mul_phase_of_maximum](DLMFMathlib/Analysis/Asymptotics/QuadraticStationaryPhase.lean#L48) — direct admission.
- [Asymptotics.isBigO_integral_exp_neg_I_mul_sq](DLMFMathlib/Analysis/Asymptotics/QuadraticStationaryPhase.lean#L30) — direct admission.
- [Asymptotics.isBigO_integral_mul_exp_neg_I_mul_sq](DLMFMathlib/Analysis/Asymptotics/QuadraticStationaryPhase.lean#L39) — direct admission.
- [Complex.GammaSeq](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L230) — definition, no admission.
- [Complex.GammaSeq_tendsto_Gamma](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L335) — proved, no admission.
- [Complex.Gamma_add_nat_div_Gamma_eq](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L481) — proved, no admission.
- [Complex.Gamma_mul_Gamma_add_half](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L580) — proved, no admission.
- [Complex.Gamma_mul_Gamma_one_sub](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L398) — proved, no admission.
- [Complex.Gamma_ofReal](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean#L419) — proved, no admission.
- [Complex.besselJ](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Bessel.lean#L55) — definition, no admission.
- [Complex.betaIntegral](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L60) — definition, no admission.
- [Complex.betaIntegral_convergent](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L78) — proved, no admission.
- [Complex.betaIntegral_eq_Gamma_mul_div](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L558) — proved, no admission.
- [Complex.betaIntegral_symm](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L90) — proved, no admission.
- [Complex.differentiable_one_div_Gamma](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L543) — proved, no admission.
- [Complex.digamma_apply_add_one](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Digamma.lean#L64) — proved, no admission.
- [Complex.digamma_one](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Digamma.lean#L56) — proved, no admission.
- [Complex.digamma_one_half](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Digamma.lean#L59) — proved, no admission.
- [Complex.hasSum_cotTerm](DLMFMathlib/Analysis/SpecialFunctions/Trigonometric/PartialFractions.lean#L43) — proved, no admission.
- [Complex.hasSum_csc_partial_fraction](DLMFMathlib/Analysis/SpecialFunctions/Trigonometric/PartialFractions.lean#L114) — proved, no admission.
- [Complex.hasSum_pi_mul_cot_bernoulli](DLMFMathlib/NumberTheory/BernoulliTaylor.lean#L138) — proved, no admission.
- [Complex.integral_cpow_mul_cexp_neg_mul_mul_sin_Ioi](DLMFMathlib/Analysis/Integral/LaplaceSine.lean#L28) — proved, no admission.
- [Complex.integral_exp_neg_mul_factorialSeries](DLMFMathlib/Analysis/Integral/BorelPowerSeries.lean#L29) — direct admission.
- [Complex.log](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/Log.lean#L30) — definition, no admission.
- [Complex.log_eq_integral](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/LogBounds.lean#L44) — proved, no admission.
- [Complex.regularizedHGFun](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/RegularizedHypergeometric.lean#L192) — definition, no admission.
- [Complex.regularizedHGFunCoeff](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/RegularizedHypergeometric.lean#L67) — definition, no admission.
- [Complex.two_mul_self_mul_besselJ](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Bessel.lean#L123) — proved, no admission.
- [DLMF.Airy.Real.airy_equation_iff_existsUnique_hypergeometric_coordinates](DLMF/Airy/HypergeometricBasis.lean#L26) — direct admission.
- [DLMF.Airy.airyAi](DLMF/Airy/Basic.lean#L53) — definition, no admission.
- [DLMF.Airy.airyAiDeriv](DLMF/Airy/Basic.lean#L58) — definition, no admission.
- [DLMF.Airy.airyAi_neg_eq_besselJ_complex](DLMF/Airy/Relations/BesselRepresentations.lean#L312) — proved, no admission.
- [DLMF.AsymptoticApproximations.HasPoincareExpansion.deriv](DLMF/AsymptoticApproximations/Basics/Calculus.lean#L39) — proved, no admission.
- [DLMF.BernoulliEuler.bernoulliPolyB_eq_sum](DLMF/BernoulliEuler/Basic/GeneratingFunctions.lean#L128) — proved, no admission.
- [DLMF.BernoulliEuler.bernoulli_two_mul_add_one_eq_zero_and_sign](DLMF/BernoulliEuler/Basic/GeneratingFunctions.lean#L106) — proved, no admission.
- [DLMF.BernoulliEuler.bernoulli_two_mul_isEquivalent](DLMF/BernoulliEuler/Asymptotics.lean#L65) — proved, no admission.
- [DLMF.BernoulliEuler.eulerNumber_eq_two_pow_mul_and_integer](DLMF/BernoulliEuler/Basic/GeneratingFunctions.lean#L238) — proved, no admission.
- [DLMF.BernoulliEuler.eulerNumber_two_mul_add_one_eq_zero_and_sign](DLMF/BernoulliEuler/Basic/GeneratingFunctions.lean#L209) — proved, no admission.
- [DLMF.BernoulliEuler.eulerNumber_two_mul_isEquivalent](DLMF/BernoulliEuler/Asymptotics.lean#L120) — proved, no admission.
- [DLMF.BernoulliEuler.eulerNumber_two_mul_modEq_two_pow'](DLMF/BernoulliEuler/Arithmetic.lean#L462) — proved, no admission.
- [DLMF.BernoulliEuler.eulerPolyE_eq_sum](DLMF/BernoulliEuler/Basic/GeneratingFunctions.lean#L227) — proved, no admission.
- [DLMF.BernoulliEuler.hasSum_alt_inv_odd_pow_eulerNumber](DLMF/BernoulliEuler/Basic/GeneratingFunctions.lean#L167) — proved, no admission.
- [DLMF.BernoulliEuler.hasSum_bernoulliPolyB_mul_pow_div](DLMF/BernoulliEuler/Basic/GeneratingFunctions.lean#L138) — proved, no admission.
- [DLMF.BernoulliEuler.hasSum_eulerNumber_mul_pow_div'](DLMF/BernoulliEuler/GeneratingFunctions.lean#L44) — proved, no admission.
- [DLMF.Bessel.besselJ_eq_poisson_cos](DLMF/Bessel/YIntegralRep.lean#L613) — proved, no admission.
- [DLMF.Bessel.besselJ_eq_poisson_integral](DLMF/Bessel/Theorems.lean#L37) — proved, no admission.
- [DLMF.Bessel.besselJ_eq_regularized](DLMF/Bessel/Basic/RegularizedSeries.lean#L52) — proved, no admission.
- [DLMF.Bessel.besselJ_eq_schlafli](DLMF/Bessel/Schlafli.lean#L591) — proved, no admission.
- [DLMF.Bessel.besselJ_half](DLMF/Bessel/RegularizedSeries.lean#L278) — proved, no admission.
- [DLMF.Bessel.besselJ_infinite_zeros_of_real](DLMF/Bessel/Asymptotics.lean#L532) — proved, no admission.
- [DLMF.Bessel.besselJ_int_eq_integral_cos](DLMF/Bessel/BesselIntegral.lean#L114) — proved, no admission.
- [DLMF.Bessel.besselJ_neg_half](DLMF/Bessel/RegularizedSeries.lean#L289) — proved, no admission.
- [DLMF.Bessel.besselJ_sub_cos_isBigO](DLMF/Bessel/Asymptotics.lean#L386) — proved, no admission.
- [DLMF.Bessel.besselJ_zero_eq_integral_cos](DLMF/Bessel/BesselIntegral.lean#L150) — proved, no admission.
- [DLMF.Bessel.besselJ_zeros_simple](DLMF/Bessel/Theorems.lean#L159) — proved, no admission.
- [DLMF.Bessel.besselY](DLMF/Bessel/Basic.lean#L41) — definition, no admission.
- [DLMF.Bessel.besselY_eq_schlafli](DLMF/Bessel/YSchlafli.lean#L58) — proved, no admission.
- [DLMF.Bessel.besselY_nat_eq_series](DLMF/Bessel/WeberSeries.lean#L174) — proved, no admission.
- [DLMF.Bessel.deriv_ne_zero_of_bessel_solution_eq_zero](DLMF/Bessel/PositiveZeroSequence.lean#L29) — direct admission.
- [DLMF.Bessel.deriv_re_besselJ_ne_zero_of_eq_zero](DLMF/Bessel/PositiveZeroSequence.lean#L51) — direct admission.
- [DLMF.Bessel.eq_besselJ_besselY_of_ode](DLMF/Bessel/WeberSeries.lean#L280) — proved, no admission.
- [DLMF.Bessel.exists_strictMono_besselJ_positive_zeros](DLMF/Bessel/PositiveZeroSequence.lean#L59) — direct admission.
- [DLMF.Bessel.hasDerivAt_besselJ](DLMF/Bessel/Basic/Equation.lean#L138) — proved, no admission.
- [DLMF.Bessel.hasDerivAt_besselNormPrimitive](DLMF/Bessel/Lommel.lean#L293) — proved, no admission.
- [DLMF.Bessel.hasSum_besselJ_cos](DLMF/Bessel/WeberSeries.lean#L424) — proved, no admission.
- [DLMF.Bessel.hasSum_besselJ_generating_function](DLMF/Bessel/Generating.lean#L59) — proved, no admission.
- [DLMF.Bessel.hasSum_besselJ_sin](DLMF/Bessel/WeberSeries.lean#L459) — proved, no admission.
- [DLMF.Bessel.integrableOn_schlafli](DLMF/Bessel/Schlafli.lean#L654) — proved, no admission.
- [DLMF.Bessel.integral_besselJ_orthogonal](DLMF/Bessel/Lommel.lean#L280) — proved, no admission.
- [DLMF.Bessel.integral_mul_besselJ_mul_besselJ](DLMF/Bessel/Lommel.lean#L245) — proved, no admission.
- [DLMF.Bessel.integral_mul_besselJ_sq](DLMF/Bessel/Lommel.lean#L375) — proved, no admission.
- [DLMF.Bessel.iteratedDeriv_two_ne_zero_of_bessel_solution_deriv_eq_zero](DLMF/Bessel/PositiveZeroSequence.lean#L40) — direct admission.
- [DLMF.Bessel.kummerM_eq_exp_mul_regularized0F1](DLMF/Bessel/RegularizedSeries.lean#L308) — proved, no admission.
- [DLMF.Bessel.regularized0F1_half_eq_cos](DLMF/Bessel/RegularizedSeries.lean#L248) — proved, no admission.
- [DLMF.Bessel.regularized0F1_three_halves_eq_sinc](DLMF/Bessel/RegularizedSeries.lean#L209) — proved, no admission.
- [DLMF.Bessel.tendsto_besselNormPrimitive](DLMF/Bessel/Lommel.lean#L311) — proved, no admission.
- [DLMF.Bessel.wronskian_besselJ_besselY](DLMF/Bessel/Basic/SecondKind.lean#L524) — proved, no admission.
- [DLMF.Bessel.wronskian_besselJ_neg](DLMF/Bessel/Basic/SecondKind.lean#L467) — proved, no admission.
- [DLMF.Confluent.Real.hasSum_sinIntegral](DLMF/Confluent/Basic/ExponentialIntegralSeries.lean#L115) — proved, no admission.
- [DLMF.Confluent.Real.hermite_equation_iff_existsUnique_kummer_coordinates](DLMF/Confluent/HermiteBasis.lean#L25) — direct admission.
- [DLMF.Confluent.Real.sinIntegral](DLMF/Confluent/Basic/ExponentialIntegrals.lean#L52) — definition, no admission.
- [DLMF.Confluent.analyticOnNhd_kummerM](DLMF/Confluent/Basic/KummerProperties.lean#L139) — proved, no admission.
- [DLMF.Confluent.erf](DLMF/Confluent/Basic/ErrorFunctions.lean#L50) — definition, no admission.
- [DLMF.Confluent.erf_lowerIncompleteGamma](DLMF/ErrorFunctions/Relations.lean#L529) — proved, no admission.
- [DLMF.Confluent.erf_ofReal](DLMF/ErrorFunctions/Basic/Properties.lean#L66) — proved, no admission.
- [DLMF.Confluent.erfc](DLMF/Confluent/Basic/ErrorFunctions.lean#L54) — definition, no admission.
- [DLMF.Confluent.erfc_sector_asymptotic](DLMF/ErrorFunctions/BoundsAsymptotics/GaussianRemainders.lean#L371) — proved, no admission.
- [DLMF.Confluent.fresnelAuxiliaryFComplex_sector_asymptotic](DLMF/ErrorFunctions/BoundsAsymptotics/FresnelRemainders.lean#L205) — proved, no admission.
- [DLMF.Confluent.fresnelAuxiliaryGComplex_sector_asymptotic](DLMF/ErrorFunctions/BoundsAsymptotics/FresnelRemainders.lean#L603) — proved, no admission.
- [DLMF.Confluent.fresnelC](DLMF/ErrorFunctions/Basic/Functions.lean#L61) — definition, no admission.
- [DLMF.Confluent.fresnelC_hypergeometric](DLMF/ErrorFunctions/Relations.lean#L635) — proved, no admission.
- [DLMF.Confluent.fresnelS](DLMF/ErrorFunctions/Basic/Functions.lean#L66) — definition, no admission.
- [DLMF.Confluent.fresnelS_hypergeometric](DLMF/ErrorFunctions/Relations.lean#L661) — proved, no admission.
- [DLMF.Confluent.hasDerivAt_kummerU](DLMF/Confluent/Recurrence/Derivatives.lean#L119) — proved, no admission.
- [DLMF.Confluent.hasSum_kummerM](DLMF/Confluent/Basic/KummerContiguous.lean#L50) — proved, no admission.
- [DLMF.Confluent.iteratedDeriv_iteratedErfc_zero](DLMF/ErrorFunctions/Repeated.lean#L524) — proved, no admission.
- [DLMF.Confluent.iteratedErfc](DLMF/ErrorFunctions/Basic/Functions.lean#L123) — definition, no admission.
- [DLMF.Confluent.iteratedErfc_general_solution](DLMF/ErrorFunctions/Repeated.lean#L474) — proved, no admission.
- [DLMF.Confluent.iteratedErfc_normalization](DLMF/ErrorFunctions/Repeated.lean#L125) — proved, no admission.
- [DLMF.Confluent.iteratedErfc_ode](DLMF/ErrorFunctions/Repeated.lean#L419) — proved, no admission.
- [DLMF.Confluent.iteratedErfc_tail](DLMF/ErrorFunctions/Repeated.lean#L289) — proved, no admission.
- [DLMF.Confluent.kummerM](DLMF/Confluent/Basic/KummerM.lean#L47) — definition, no admission.
- [DLMF.Confluent.kummerM_contiguous_a](DLMF/Confluent/Basic/KummerContiguous.lean#L254) — proved, no admission.
- [DLMF.Confluent.kummerM_contiguous_a_b](DLMF/Confluent/Basic/KummerContiguous.lean#L275) — proved, no admission.
- [DLMF.Confluent.kummerM_contiguous_b](DLMF/Confluent/Basic/KummerContiguous.lean#L264) — proved, no admission.
- [DLMF.Confluent.kummerM_contiguous_down](DLMF/Confluent/Basic/KummerContiguous.lean#L310) — proved, no admission.
- [DLMF.Confluent.kummerM_contiguous_mixed](DLMF/Confluent/Basic/KummerContiguous.lean#L300) — proved, no admission.
- [DLMF.Confluent.kummerM_contiguous_mixed_b_pred](DLMF/Confluent/Basic/KummerContiguous.lean#L374) — proved, no admission.
- [DLMF.Confluent.kummerM_contiguous_shift_a](DLMF/Confluent/Basic/KummerContiguous.lean#L286) — proved, no admission.
- [DLMF.Confluent.kummerM_contiguous_shift_b_succ](DLMF/Confluent/Basic/KummerContiguous.lean#L362) — proved, no admission.
- [DLMF.Confluent.kummerM_erf](DLMF/Confluent/Relations.lean#L166) — proved, no admission.
- [DLMF.Confluent.kummerM_hermite_even](DLMF/Confluent/Relations.lean#L769) — proved, no admission.
- [DLMF.Confluent.kummerM_hermite_odd](DLMF/Confluent/Relations.lean#L788) — proved, no admission.
- [DLMF.Confluent.kummerM_kummer_transform](DLMF/Confluent/Basic/KummerProperties.lean#L230) — proved, no admission.
- [DLMF.Confluent.kummerM_lowerIncompleteGamma](DLMF/Confluent/Relations.lean#L133) — proved, no admission.
- [DLMF.Confluent.kummerM_ode](DLMF/Confluent/Basic/KummerProperties.lean#L160) — proved, no admission.
- [DLMF.Confluent.kummerM_ode_contiguous](DLMF/Confluent/Basic/KummerContiguous.lean#L321) — proved, no admission.
- [DLMF.Confluent.kummerU_laplace](DLMF/Confluent/IntegralRepresentations/EulerAndBessel.lean#L694) — proved, no admission.
- [DLMF.Confluent.kummerU_laplace_integrable](DLMF/Confluent/IntegralRepresentations/EulerAndBessel.lean#L309) — proved, no admission.
- [DLMF.Confluent.kummerU_ode_contiguous](DLMF/Confluent/Recurrence/Contiguous.lean#L501) — proved, no admission.
- [DLMF.Confluent.lowerIncompleteGamma](DLMF/Confluent/Basic/IncompleteGamma.lean#L32) — definition, no admission.
- [DLMF.Confluent.lowerIncompleteGamma_eq_integral](DLMF/Confluent/IncompleteGamma.lean#L169) — proved, no admission.
- [DLMF.Confluent.regularizedConfluent_kummer_transform](DLMF/Confluent/Continuation.lean#L287) — proved, no admission.
- [DLMF.Confluent.regularizedHGFun_of_neg_nat](DLMF/Confluent/BasicProperties/Continuity.lean#L56) — proved, no admission.
- [DLMF.Confluent.regularized_euler_integral](DLMF/Confluent/IntegralRepresentations/EulerAndBessel.lean#L70) — proved, no admission.
- [DLMF.Confluent.wronskian_kummerM_pair](DLMF/Confluent/BasicProperties/Wronskians.lean#L323) — proved, no admission.
- [DLMF.Confluent.wronskian_regularizedHGFun_kummerU_all](DLMF/Confluent/BasicProperties/Wronskians.lean#L376) — proved, no admission.
- [DLMF.Constants.bbpSeries](DLMF/Constants/BBPFamily.lean#L30) — definition, no admission.
- [DLMF.Constants.bbpSeries_def](DLMF/Constants/BBPFamily.lean#L35) — proved, no admission.
- [DLMF.Constants.bbpSeries_eq_integral](DLMF/Constants/BBPFamily.lean#L49) — direct admission.
- [DLMF.Constants.bbpSeries_eq_sum_polylog](DLMF/Constants/BBPFamily.lean#L60) — direct admission.
- [DLMF.Constants.catalanConstant](DLMF/Constants/Basic.lean#L38) — definition, no admission.
- [DLMF.Constants.dirichletEta](DLMF/Constants/Dirichlet.lean#L78) — definition, no admission.
- [DLMF.Constants.dirichletEta_eq](DLMF/Constants/Dirichlet.lean#L146) — proved, no admission.
- [DLMF.Constants.dirichletLambda](DLMF/Constants/Dirichlet.lean#L81) — definition, no admission.
- [DLMF.Constants.dirichletLambda_eq](DLMF/Constants/Dirichlet.lean#L114) — proved, no admission.
- [DLMF.Constants.gauss_machin](DLMF/Constants/BBP.lean#L261) — proved, no admission.
- [DLMF.Constants.hasSum_bbp_pi](DLMF/Constants/BBP.lean#L87) — proved, no admission.
- [DLMF.Constants.hasSum_log_three](DLMF/Constants/BBP.lean#L136) — proved, no admission.
- [DLMF.Constants.hasSum_log_two](DLMF/Constants/BBP.lean#L157) — proved, no admission.
- [DLMF.Constants.hasSum_zeta](DLMF/Constants/Dirichlet.lean#L91) — proved, no admission.
- [DLMF.Constants.summable_bbpSeries](DLMF/Constants/BBPFamily.lean#L41) — direct admission.
- [DLMF.Constants.tendsto_dirichletEta_one](DLMF/Constants/Dirichlet.lean#L152) — proved, no admission.
- [DLMF.Constants.tendsto_riemannZeta_atTop](DLMF/Constants/Dirichlet.lean#L160) — proved, no admission.
- [DLMF.Constants.trigamma_one_quarter](DLMF/Constants/Catalan.lean#L92) — proved, no admission.
- [DLMF.Constants.trigamma_three_quarters](DLMF/Constants/Catalan.lean#L111) — proved, no admission.
- [DLMF.Elementary.arsinh_eq_ordinaryHypergeometric](DLMF/Elementary/InverseHyperbolicSeries.lean#L28) — direct admission.
- [DLMF.Elementary.arsinh_sq_eq_generalizedHypergeometric](DLMF/Elementary/InverseHyperbolicSeries.lean#L35) — direct admission.
- [DLMF.Elementary.hasSum_arsinh_sq](DLMF/Elementary/InverseHyperbolicSeries.lean#L43) — direct admission.
- [DLMF.Elementary.hasSum_csc_sq_partial_fraction](DLMF/Elementary/Trigonometric/DirectIdentities.lean#L1125) — proved, no admission.
- [DLMF.Elliptic.Gamma_one_fourth_sq_mul_agm](DLMF/Elliptic/SpecialValues.lean#L143) — proved, no admission.
- [DLMF.Elliptic.Real.completeEllipticEOfParameter](DLMF/Elliptic/Basic/Integrals.lean#L66) — definition, no admission.
- [DLMF.Elliptic.Real.completeEllipticEOfParameter_eq_ordinaryHypergeometric](DLMF/Elliptic/Complete.lean#L431) — proved, no admission.
- [DLMF.Elliptic.Real.completeEllipticEOfParameter_landen_descending](DLMF/Elliptic/AGM.lean#L388) — proved, no admission.
- [DLMF.Elliptic.Real.completeEllipticKOfParameter](DLMF/Elliptic/Basic/Integrals.lean#L60) — definition, no admission.
- [DLMF.Elliptic.Real.completeEllipticKOfParameter_eq_ordinaryHypergeometric](DLMF/Elliptic/Complete.lean#L422) — proved, no admission.
- [DLMF.Elliptic.Real.completeEllipticKOfParameter_eq_pi_div_agm](DLMF/Elliptic/AGM.lean#L320) — proved, no admission.
- [DLMF.Elliptic.Real.completeEllipticKOfParameter_landen_descending](DLMF/Elliptic/AGM.lean#L332) — proved, no admission.
- [DLMF.Elliptic.Real.completeEllipticKOfParameter_one_half](DLMF/Elliptic/SpecialValues.lean#L109) — proved, no admission.
- [DLMF.Elliptic.Real.hasDerivAt_completeEllipticEOfParameter_sq](DLMF/Elliptic/Complete.lean#L465) — proved, no admission.
- [DLMF.Elliptic.Real.hasDerivAt_completeEllipticKOfParameter_sq](DLMF/Elliptic/Complete.lean#L451) — proved, no admission.
- [DLMF.Elliptic.Real.hasDerivAt_jacobiAmOfParameter](DLMF/Elliptic/Basic/Jacobi.lean#L87) — proved, no admission.
- [DLMF.Elliptic.Real.hasDerivAt_jacobiArcsnOfParameter](DLMF/Elliptic/Basic/Jacobi.lean#L300) — proved, no admission.
- [DLMF.Elliptic.Real.hasDerivAt_jacobiCnOfParameter](DLMF/Elliptic/Basic/Jacobi.lean#L162) — proved, no admission.
- [DLMF.Elliptic.Real.hasDerivAt_jacobiDnOfParameter](DLMF/Elliptic/Basic/Jacobi.lean#L170) — proved, no admission.
- [DLMF.Elliptic.Real.hasDerivAt_jacobiSnOfParameter](DLMF/Elliptic/Basic/Jacobi.lean#L155) — proved, no admission.
- [DLMF.Elliptic.Real.incompleteEllipticFOfParameter](DLMF/Elliptic/Basic/Integrals.lean#L72) — definition, no admission.
- [DLMF.Elliptic.Real.integral_recip_sqrt_eq_incompleteEllipticFOfParameter](DLMF/Elliptic/SpecialValues.lean#L74) — proved, no admission.
- [DLMF.Elliptic.Real.jacobiAmOfParameter_neg](DLMF/Elliptic/Basic/Jacobi.lean#L119) — proved, no admission.
- [DLMF.Elliptic.Real.jacobiArcsnOfParameter](DLMF/Elliptic/Basic/Jacobi.lean#L272) — definition, no admission.
- [DLMF.Elliptic.Real.jacobiArcsnOfParameter_jacobiSnOfParameter](DLMF/Elliptic/Basic/Jacobi.lean#L283) — proved, no admission.
- [DLMF.Elliptic.Real.jacobiSnOfParameter_jacobiArcsnOfParameter](DLMF/Elliptic/Basic/Jacobi.lean#L276) — proved, no admission.
- [DLMF.Elliptic.Real.jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq](DLMF/Elliptic/Basic/Jacobi.lean#L133) — proved, no admission.
- [DLMF.Elliptic.Real.jacobi_add_two_completeEllipticKOfParameter](DLMF/Elliptic/Basic/Jacobi.lean#L209) — proved, no admission.
- [DLMF.Elliptic.Real.jacobi_completeEllipticKOfParameter](DLMF/Elliptic/Basic/Jacobi.lean#L238) — proved, no admission.
- [DLMF.Elliptic.Real.mul_jacobiSnOfParameter_sq_add_jacobiDnOfParameter_sq](DLMF/Elliptic/Basic/Jacobi.lean#L139) — proved, no admission.
- [DLMF.Elliptic.Real.strictMono_incompleteEllipticFOfParameter](DLMF/Elliptic/Basic/Amplitude.lean#L135) — proved, no admission.
- [DLMF.Elliptic.Real.surjective_incompleteEllipticFOfParameter](DLMF/Elliptic/Basic/Amplitude.lean#L142) — proved, no admission.
- [DLMF.Elliptic.agmIntegral_eq_pi_div_two_div_agm](DLMF/Elliptic/AGM.lean#L290) — proved, no admission.
- [DLMF.Elliptic.ellipsePerimeter](DLMF/Elliptic/SpecialValues.lean#L206) — definition, no admission.
- [DLMF.Elliptic.ellipsePerimeter_eq](DLMF/Elliptic/SpecialValues.lean#L211) — proved, no admission.
- [DLMF.Elliptic.ellipsePerimeter_eq_ordinaryHypergeometric](DLMF/Elliptic/SpecialValues.lean#L232) — proved, no admission.
- [DLMF.Elliptic.integral_Ioi_recip_sqrt_sq_sub_mul_sq_sub](DLMF/Elliptic/BookReductions.lean#L51) — direct admission.
- [DLMF.Elliptic.integral_recip_sqrt_cubic](DLMF/Elliptic/BookReductions.lean#L61) — direct admission.
- [DLMF.Elliptic.integral_recip_sqrt_one_add_pow_four](DLMF/Elliptic/BookReductions.lean#L36) — direct admission.
- [DLMF.Elliptic.integral_recip_sqrt_one_sub_pow_four_to](DLMF/Elliptic/BookReductions.lean#L28) — direct admission.
- [DLMF.Elliptic.integral_recip_sqrt_sub_sq_mul_sub_sq](DLMF/Elliptic/BookReductions.lean#L43) — direct admission.
- [DLMF.Elliptic.jacobi_neg](DLMF/Elliptic/Basic/Jacobi.lean#L255) — proved, no admission.
- [DLMF.Elliptic.jacobi_zero](DLMF/Elliptic/Basic/Jacobi.lean#L247) — proved, no admission.
- [DLMF.Elliptic.legendre_relation](DLMF/Elliptic/Complete.lean#L309) — proved, no admission.
- [DLMF.Elliptic.pendulumAngle](DLMF/Elliptic/JacobiIdentities.lean#L395) — definition, no admission.
- [DLMF.Elliptic.pendulumAngle_ode](DLMF/Elliptic/JacobiIdentities.lean#L400) — proved, no admission.
- [DLMF.Elliptic.pendulumAngle_periodic](DLMF/Elliptic/JacobiIdentities.lean#L462) — proved, no admission.
- [DLMF.Gamma.Gamma_laplace_power](DLMF/Gamma/IntegralRepresentations/HankelAndGaussian.lean#L73) — proved, no admission.
- [DLMF.Gamma.Gamma_mul_hurwitzZeta_eq_integral](DLMF/Gamma/PolygammaHurwitz.lean#L148) — proved, no admission.
- [DLMF.Gamma.Gamma_ratio_power](DLMF/Gamma/Asymptotics/Stirling.lean#L701) — proved, no admission.
- [DLMF.Gamma.Real.Gamma_mul_nat](DLMF/Gamma/Multiplication.lean#L696) — proved, no admission.
- [DLMF.Gamma.Real.digamma](DLMF/Gamma/Basic/Digamma.lean#L55) — definition, no admission.
- [DLMF.Gamma.Real.digamma_add_one_of_not_neg_nat](DLMF/Gamma/Basic/RealDigamma.lean#L50) — proved, no admission.
- [DLMF.Gamma.Real.digamma_eq_tsum](DLMF/Gamma/Digamma.lean#L268) — proved, no admission.
- [DLMF.Gamma.Real.hasDerivAt_digamma](DLMF/Gamma/Digamma.lean#L297) — proved, no admission.
- [DLMF.Gamma.Real.hasDerivAt_log_abs_Gamma](DLMF/Gamma/Basic/RealDigamma.lean#L42) — proved, no admission.
- [DLMF.Gamma.Real.one_div_Gamma_eq_tprod](DLMF/Gamma/Basic.lean#L317) — proved, no admission.
- [DLMF.Gamma.Real.tendsto_weierstrassGamma_prod](DLMF/Gamma/Basic.lean#L296) — proved, no admission.
- [DLMF.Gamma.Real.trigamma_eq_tsum](DLMF/Gamma/Digamma.lean#L345) — proved, no admission.
- [DLMF.Gamma.analyticAt_Gamma](DLMF/Gamma/Polygamma.lean#L95) — proved, no admission.
- [DLMF.Gamma.beta_sin_cos](DLMF/Gamma/BetaFunction/ParameterIntegrals.lean#L57) — proved, no admission.
- [DLMF.Gamma.binetBeta](DLMF/Gamma/IntegralRepresentations/DigammaAndBinet.lean#L434) — definition, no admission.
- [DLMF.Gamma.binetIntegral](DLMF/Gamma/IntegralRepresentations/DigammaAndBinet.lean#L537) — definition, no admission.
- [DLMF.Gamma.deriv_Gamma_one](DLMF/Gamma/SpecialValues.lean#L179) — proved, no admission.
- [DLMF.Gamma.differentiable_recipGammaDeriv](DLMF/Gamma/RecipGammaDeriv.lean#L75) — proved, no admission.
- [DLMF.Gamma.digamma_add_euler_Ioi](DLMF/Gamma/IntegralRepresentations/DigammaAndBinet.lean#L156) — proved, no admission.
- [DLMF.Gamma.digamma_add_euler_Ioo](DLMF/Gamma/IntegralRepresentations/DigammaAndBinet.lean#L93) — proved, no admission.
- [DLMF.Gamma.digamma_eq_log_sub_binetBeta](DLMF/Gamma/IntegralRepresentations/DigammaAndBinet.lean#L596) — proved, no admission.
- [DLMF.Gamma.digamma_frullani](DLMF/Gamma/IntegralRepresentations/FrullaniAndMoments.lean#L346) — proved, no admission.
- [DLMF.Gamma.digamma_gauss](DLMF/Gamma/IntegralRepresentations/FrullaniAndMoments.lean#L52) — proved, no admission.
- [DLMF.Gamma.digamma_ofReal_of_not_neg_nat](DLMF/Gamma/Basic/RealDigamma.lean#L24) — proved, no admission.
- [DLMF.Gamma.eulerMascheroni_integrals](DLMF/Gamma/IntegralRepresentations/FrullaniAndMoments.lean#L484) — proved, no admission.
- [DLMF.Gamma.hasAsymptoticExpansion_log_Gamma](DLMF/Gamma/Asymptotics/Stirling.lean#L510) — proved, no admission.
- [DLMF.Gamma.hasSum_polynomial_div_of_distinct_real_roots](DLMF/Gamma/PolynomialSeries.lean#L28) — direct admission.
- [DLMF.Gamma.hasSum_sum_div_sub](DLMF/Gamma/RationalSeries.lean#L55) — proved, no admission.
- [DLMF.Gamma.hurwitzZeta_one_half_nat](DLMF/Gamma/PolygammaHurwitz.lean#L61) — proved, no admission.
- [DLMF.Gamma.integrableOn_exp_neg_sub_exp_neg_div](DLMF/Gamma/IntegralRepresentations/DigammaAndBinet.lean#L259) — proved, no admission.
- [DLMF.Gamma.integrableOn_log_pow_mul_Gamma](DLMF/Gamma/IntegralRepresentations/FrullaniAndMoments.lean#L572) — proved, no admission.
- [DLMF.Gamma.integral_cpow_mul_exp_neg_mul_Ioi](DLMF/Gamma/IntegralRepresentations/HankelAndGaussian.lean#L64) — proved, no admission.
- [DLMF.Gamma.integral_exp_neg_sub_exp_neg_div](DLMF/Gamma/IntegralRepresentations/DigammaAndBinet.lean#L273) — proved, no admission.
- [DLMF.Gamma.integral_rpow_div_one_add](DLMF/Gamma/IntegralRepresentations/PrymAndOscillatory.lean#L450) — proved, no admission.
- [DLMF.Gamma.iteratedDeriv_Gamma](DLMF/Gamma/IntegralRepresentations/FrullaniAndMoments.lean#L643) — proved, no admission.
- [DLMF.Gamma.log_Gamma_binet_exp](DLMF/Gamma/IntegralRepresentations/DigammaAndBinet.lean#L633) — proved, no admission.
- [DLMF.Gamma.log_Gamma_eq_add_binetIntegral](DLMF/Gamma/IntegralRepresentations/DigammaAndBinet.lean#L761) — proved, no admission.
- [DLMF.Gamma.log_Gamma_stirling](DLMF/Gamma/Asymptotics/Stirling.lean#L318) — proved, no admission.
- [DLMF.Gamma.multipliable_weierstrassGammaTerm](DLMF/Gamma/Basic.lean#L135) — proved, no admission.
- [DLMF.Gamma.pochhammer_neg_eq](DLMF/Gamma/Pochhammer.lean#L35) — proved, no admission.
- [DLMF.Gamma.polygamma_add_one](DLMF/Gamma/Polygamma.lean#L409) — proved, no admission.
- [DLMF.Gamma.polygamma_eq_hurwitzZeta](DLMF/Gamma/PolygammaHurwitz.lean#L48) — proved, no admission.
- [DLMF.Gamma.polygamma_eq_integral](DLMF/Gamma/PolygammaHurwitz.lean#L157) — proved, no admission.
- [DLMF.Gamma.polygamma_eq_tsum](DLMF/Gamma/Polygamma.lean#L304) — proved, no admission.
- [DLMF.Gamma.polygamma_one](DLMF/Gamma/Polygamma.lean#L355) — proved, no admission.
- [DLMF.Gamma.polygamma_reflection](DLMF/Gamma/Polygamma.lean#L455) — proved, no admission.
- [DLMF.Gamma.recipGammaDeriv_one_neg_nat](DLMF/Gamma/RecipGammaDeriv.lean#L144) — proved, no admission.
- [DLMF.Gamma.tendsto_Gamma_add_div_Gamma_mul_cpow](DLMF/Gamma/Asymptotics/Stirling.lean#L660) — proved, no admission.
- [DLMF.Gamma.tendsto_integral_rpow_mul_cos](DLMF/Gamma/IntegralRepresentations/PrymAndOscillatory.lean#L709) — proved, no admission.
- [DLMF.Gamma.tendsto_integral_rpow_mul_sin](DLMF/Gamma/IntegralRepresentations/PrymAndOscillatory.lean#L748) — proved, no admission.
- [DLMF.Hypergeometric.GenContiguous](DLMF/GeneralizedHypergeometric/Derivatives.lean#L61) — definition, no admission.
- [DLMF.Hypergeometric.IsTerminating](DLMF/GeneralizedHypergeometric/Basic/ParametersAndSeries.lean#L58) — definition, no admission.
- [DLMF.Hypergeometric.KummerSolutions.eightSolutions](DLMF/Hypergeometric/RegularizedKummerSolutions.lean#L30) — definition, no admission.
- [DLMF.Hypergeometric.KummerSolutions.eightSolutions_def](DLMF/Hypergeometric/RegularizedKummerSolutions.lean#L47) — proved, no admission.
- [DLMF.Hypergeometric.KummerSolutions.eightSolutions_inversion_ode](DLMF/Hypergeometric/RegularizedKummerSolutions.lean#L73) — direct admission.
- [DLMF.Hypergeometric.KummerSolutions.eightSolutions_ode](DLMF/Hypergeometric/RegularizedKummerSolutions.lean#L65) — direct admission.
- [DLMF.Hypergeometric.KummerSolutions.eightSolutions_pfaff_inversion_ode](DLMF/Hypergeometric/RegularizedKummerSolutions.lean#L82) — direct admission.
- [DLMF.Hypergeometric.LowerParametersRegular](DLMF/GeneralizedHypergeometric/Basic/ParametersAndSeries.lean#L55) — definition, no admission.
- [DLMF.Hypergeometric.PrincipalContinuation](DLMF/GeneralizedHypergeometric/Basic/PrincipalContinuation.lean#L31) — definition, no admission.
- [DLMF.Hypergeometric.Real.sinIntegral_eq_regularizedHGFun](DLMF/Hypergeometric/SpecialCases.lean#L61) — proved, no admission.
- [DLMF.Hypergeometric.analyticOnNhd_regularizedGeneralizedHypergeometric](DLMF/GeneralizedHypergeometric/Basic/PrincipalContinuationExistence.lean#L766) — proved, no admission.
- [DLMF.Hypergeometric.arcsin_eq_ordinaryHypergeometric](DLMF/Hypergeometric/DiffEq.lean#L143) — proved, no admission.
- [DLMF.Hypergeometric.arctan_eq_regularizedGaussHypergeometric](DLMF/GeneralizedHypergeometric/BookSeries.lean#L49) — direct admission.
- [DLMF.Hypergeometric.bailey_summation](DLMF/Hypergeometric/Elementary/AlgebraicValues.lean#L827) — proved, no admission.
- [DLMF.Hypergeometric.clausen_formula](DLMF/Hypergeometric/Clausen.lean#L198) — proved, no admission.
- [DLMF.Hypergeometric.coeff_eq_of_generalized_ode](DLMF/Hypergeometric/Basic/GeneralizedCalculus.lean#L331) — proved, no admission.
- [DLMF.Hypergeometric.contiguous_c_three](DLMF/Hypergeometric/Derivatives.lean#L417) — proved, no admission.
- [DLMF.Hypergeometric.deriv_recip_Gamma_eq](DLMF/Hypergeometric/ConnectionFormulas.lean#L177) — proved, no admission.
- [DLMF.Hypergeometric.deriv_regularizedHGFun](DLMF/Hypergeometric/Basic/GeneralizedCalculus.lean#L77) — proved, no admission.
- [DLMF.Hypergeometric.dixon_sum](DLMF/Hypergeometric/Identities/Dixon.lean#L627) — proved, no admission.
- [DLMF.Hypergeometric.eq_generalizedHypergeometric_of_coefficient_recurrence](DLMF/GeneralizedHypergeometric/BookSeries.lean#L56) — direct admission.
- [DLMF.Hypergeometric.eulerTheta](DLMF/Hypergeometric/Basic/GeneralizedEquation.lean#L41) — definition, no admission.
- [DLMF.Hypergeometric.gammaProduct_ne_zero](DLMF/GeneralizedHypergeometric/Basic/SeriesProperties.lean#L92) — proved, no admission.
- [DLMF.Hypergeometric.gauss_quadratic](DLMF/Hypergeometric/FurtherTransformations/Quadratic.lean#L466) — proved, no admission.
- [DLMF.Hypergeometric.gauss_second_summation](DLMF/Hypergeometric/Elementary/AlgebraicValues.lean#L727) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric](DLMF/GeneralizedHypergeometric/Basic/PrincipalContinuation.lean#L56) — definition, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometricCoeff](DLMF/GeneralizedHypergeometric/Basic/ParametersAndSeries.lean#L51) — definition, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometricCoeff_eq_gamma_mul_regularized](DLMF/GeneralizedHypergeometric/Basic/SeriesProperties.lean#L132) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometricTruncated](DLMF/GeneralizedHypergeometric/Basic/ParametersAndSeries.lean#L65) — definition, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_clausen_principal](DLMF/GeneralizedHypergeometric/Transformations.lean#L528) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_diverges_nonzero](DLMF/GeneralizedHypergeometric/AnalyticProperties.lean#L1057) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_empty_empty](DLMF/GeneralizedHypergeometric/BookSeries.lean#L30) — direct admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_entire](DLMF/GeneralizedHypergeometric/AnalyticProperties.lean#L66) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_euler_integral](DLMF/GeneralizedHypergeometric/Integrals.lean#L186) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_euler_integral'](DLMF/GeneralizedHypergeometric/Integrals.lean#L153) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_hasSum_disk](DLMF/GeneralizedHypergeometric/Basic/SeriesProperties.lean#L146) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_hasSum_entire](DLMF/GeneralizedHypergeometric/AnalyticProperties.lean#L74) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_iteratedDeriv](DLMF/GeneralizedHypergeometric/Derivatives.lean#L217) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_laplace_integral](DLMF/GeneralizedHypergeometric/Integrals.lean#L199) — direct admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_lower_weighted_iteratedDeriv](DLMF/GeneralizedHypergeometric/Derivatives.lean#L739) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_one_converges_iff](DLMF/GeneralizedHypergeometric/AnalyticProperties.lean#L942) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_principal_analytic](DLMF/GeneralizedHypergeometric/AnalyticProperties.lean#L294) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_radius_one](DLMF/GeneralizedHypergeometric/AnalyticProperties.lean#L102) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_radius_zero](DLMF/GeneralizedHypergeometric/AnalyticProperties.lean#L1036) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_raising_iterate](DLMF/GeneralizedHypergeometric/Derivatives.lean#L729) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_singleton_empty](DLMF/GeneralizedHypergeometric/BookSeries.lean#L36) — direct admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_terminating_entire](DLMF/GeneralizedHypergeometric/AnalyticProperties.lean#L92) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_theta_ode](DLMF/GeneralizedHypergeometric/DifferentialEquations.lean#L407) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_unit_absolute_iff](DLMF/GeneralizedHypergeometric/AnalyticProperties.lean#L299) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_unit_conditional](DLMF/GeneralizedHypergeometric/AnalyticProperties.lean#L892) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_unit_diverges](DLMF/GeneralizedHypergeometric/AnalyticProperties.lean#L345) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_upper_confluence](DLMF/GeneralizedHypergeometric/DifferentialEquations.lean#L1147) — proved, no admission.
- [DLMF.Hypergeometric.hasDerivAt_generalizedHypergeometric_lower_parameter](DLMF/GeneralizedHypergeometric/BookSeries.lean#L89) — direct admission.
- [DLMF.Hypergeometric.hasDerivAt_generalizedHypergeometric_upper_parameter](DLMF/GeneralizedHypergeometric/BookSeries.lean#L68) — direct admission.
- [DLMF.Hypergeometric.hasDerivAt_pochhammer](DLMF/Hypergeometric/ConnectionFormulas.lean#L85) — proved, no admission.
- [DLMF.Hypergeometric.hasSum_arcsin_sq](DLMF/Hypergeometric/Clausen.lean#L264) — proved, no admission.
- [DLMF.Hypergeometric.hasSum_regularizedGauss_one](DLMF/Hypergeometric/Boundary.lean#L58) — proved, no admission.
- [DLMF.Hypergeometric.intervalIntegrable_eulerKernel](DLMF/Hypergeometric/Basic/CutPlane.lean#L201) — proved, no admission.
- [DLMF.Hypergeometric.kummer_quadratic](DLMF/Hypergeometric/FurtherTransformations/Quadratic.lean#L626) — proved, no admission.
- [DLMF.Hypergeometric.kummer_theorem](DLMF/Hypergeometric/Identities/CarlsonTools.lean#L45) — proved, no admission.
- [DLMF.Hypergeometric.logarithmic_connection_one_sub](DLMF/Hypergeometric/ConnectionFormulas.lean#L228) — proved, no admission.
- [DLMF.Hypergeometric.mul_regularizedGaussHypergeometric_one_one_two](DLMF/GeneralizedHypergeometric/BookSeries.lean#L42) — direct admission.
- [DLMF.Hypergeometric.nonempty_principalContinuation](DLMF/GeneralizedHypergeometric/Basic/PrincipalContinuationExistence.lean#L711) — proved, no admission.
- [DLMF.Hypergeometric.pfaff_saalschutz_of_finite_regular](DLMF/Hypergeometric/TerminatingSummations.lean#L35) — direct admission.
- [DLMF.Hypergeometric.principalContinuation_exists](DLMF/GeneralizedHypergeometric/Basic/PrincipalContinuationExistence.lean#L747) — proved, no admission.
- [DLMF.Hypergeometric.principalContinuation_unique](DLMF/GeneralizedHypergeometric/Basic/SeriesProperties.lean#L52) — proved, no admission.
- [DLMF.Hypergeometric.quadratic_double_denominator](DLMF/Hypergeometric/FurtherTransformations/Quadratic.lean#L636) — proved, no admission.
- [DLMF.Hypergeometric.regularizedGaussHypergeometric_contiguous_a](DLMF/Hypergeometric/ArgumentContinuation.lean#L73) — proved, no admission.
- [DLMF.Hypergeometric.regularizedGaussHypergeometric_contiguous_a_b_pred](DLMF/Hypergeometric/ArgumentContinuation.lean#L104) — proved, no admission.
- [DLMF.Hypergeometric.regularizedGaussHypergeometric_contiguous_a_c_succ](DLMF/Hypergeometric/ArgumentContinuation.lean#L134) — proved, no admission.
- [DLMF.Hypergeometric.regularizedGaussHypergeometric_contiguous_a_pred_c_pred](DLMF/Hypergeometric/ArgumentContinuation.lean#L181) — proved, no admission.
- [DLMF.Hypergeometric.regularizedGaussHypergeometric_contiguous_a_pred_c_succ](DLMF/Hypergeometric/ArgumentContinuation.lean#L165) — proved, no admission.
- [DLMF.Hypergeometric.regularizedGaussHypergeometric_contiguous_a_succ_c_pred](DLMF/Hypergeometric/ArgumentContinuation.lean#L149) — proved, no admission.
- [DLMF.Hypergeometric.regularizedGaussHypergeometric_contiguous_ab](DLMF/Hypergeometric/ArgumentContinuation.lean#L89) — proved, no admission.
- [DLMF.Hypergeometric.regularizedGaussHypergeometric_contiguous_c_three](DLMF/Hypergeometric/ArgumentContinuation.lean#L197) — proved, no admission.
- [DLMF.Hypergeometric.regularizedGaussHypergeometric_contiguous_diagonal](DLMF/Hypergeometric/ArgumentContinuation.lean#L214) — proved, no admission.
- [DLMF.Hypergeometric.regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricIntegral](DLMF/Hypergeometric/Basic/CutPlane.lean#L457) — proved, no admission.
- [DLMF.Hypergeometric.regularizedGaussHypergeometric_euler](DLMF/Hypergeometric/ArgumentContinuation.lean#L231) — proved, no admission.
- [DLMF.Hypergeometric.regularizedGaussHypergeometric_neg_nat](DLMF/Hypergeometric/Basic/CutPlane.lean#L567) — proved, no admission.
- [DLMF.Hypergeometric.regularizedGaussHypergeometric_ode](DLMF/Hypergeometric/Basic/CutPlane.lean#L536) — proved, no admission.
- [DLMF.Hypergeometric.regularizedGaussHypergeometric_pfaff](DLMF/Hypergeometric/ArgumentContinuation.lean#L266) — proved, no admission.
- [DLMF.Hypergeometric.regularizedGeneralizedHypergeometric](DLMF/GeneralizedHypergeometric/Basic/PrincipalContinuation.lean#L48) — definition, no admission.
- [DLMF.Hypergeometric.regularizedGeneralizedHypergeometric_eq_series](DLMF/GeneralizedHypergeometric/Basic/SeriesProperties.lean#L120) — proved, no admission.
- [DLMF.Hypergeometric.regularizedGeneralizedHypergeometric_iteratedDeriv](DLMF/GeneralizedHypergeometric/Derivatives.lean#L168) — proved, no admission.
- [DLMF.Hypergeometric.regularizedHGFun_contiguous](DLMF/Hypergeometric/Basic/GeneralizedCalculus.lean#L111) — proved, no admission.
- [DLMF.Hypergeometric.regularizedHGFun_ode](DLMF/Hypergeometric/Basic/GeneralizedEquation.lean#L145) — proved, no admission.
- [DLMF.Hypergeometric.regularizedHGFun_ode_of_card_eq_add_one](DLMF/Hypergeometric/Basic/GeneralizedEquation.lean#L182) — proved, no admission.
- [DLMF.Hypergeometric.regularizedHGFun_ode_of_card_le](DLMF/Hypergeometric/Basic/GeneralizedEquation.lean#L175) — proved, no admission.
- [DLMF.Hypergeometric.scalarSeries_unique_ball](DLMF/Hypergeometric/Basic/GeneralizedCalculus.lean#L302) — proved, no admission.
- [DLMF.Hypergeometric.sin_sq_cos](DLMF/Hypergeometric/Elementary/AlgebraicValues.lean#L492) — proved, no admission.
- [DLMF.Hypergeometric.sin_sq_sin](DLMF/Hypergeometric/Elementary/AlgebraicValues.lean#L639) — proved, no admission.
- [DLMF.Hypergeometric.sum_pochhammer_mul_neg_nat_div](DLMF/Hypergeometric/TerminatingSummations.lean#L27) — direct admission.
- [DLMF.Hypergeometric.summable_generalizedHypergeometric_lower_parameter_derivative](DLMF/GeneralizedHypergeometric/BookSeries.lean#L99) — direct admission.
- [DLMF.Hypergeometric.summable_generalizedHypergeometric_upper_parameter_derivative](DLMF/GeneralizedHypergeometric/BookSeries.lean#L79) — direct admission.
- [DLMF.Hypergeometric.tendsto_regularizedGaussHypergeometric_div_log_left_one](DLMF/Hypergeometric/EndpointLogarithm.lean#L29) — direct admission.
- [DLMF.Hypergeometric.tendsto_regularizedGaussHypergeometric_left_one](DLMF/Hypergeometric/Boundary.lean#L119) — proved, no admission.
- [DLMF.Hypergeometric.thetaPoly](DLMF/Hypergeometric/Basic/GeneralizedEquation.lean#L44) — definition, no admission.
- [DLMF.Hypergeometric.zero_first_connection_one_of_not_neg_nat](DLMF/Hypergeometric/Solutions/Connections.lean#L540) — proved, no admission.
- [DLMF.Legendre.associated_wronskian_11](DLMF/Legendre/AssociatedRecurrences.lean#L1082) — proved, no admission.
- [DLMF.Legendre.legendreP](DLMF/Legendre/Basic/Functions.lean#L35) — definition, no admission.
- [DLMF.Legendre.legendreP_ode](DLMF/Legendre/Basic/Properties.lean#L116) — proved, no admission.
- [DLMF.Legendre.legendreQ](DLMF/Legendre/Basic/Functions.lean#L48) — definition, no admission.
- [DLMF.Legendre.legendreQ_eq_finite_weighted_integral](DLMF/Legendre/FiniteWeightedIntegral.lean#L27) — direct admission.
- [DLMF.OrthogonalPolynomials.IsOrthogonalPolynomials](DLMF/OrthogonalPolynomials/Basic/General.lean#L53) — definition, no admission.
- [DLMF.OrthogonalPolynomials.IsOrthogonalPolynomials.expansion](DLMF/OrthogonalPolynomials/Basic/General.lean#L100) — proved, no admission.
- [DLMF.OrthogonalPolynomials.IsOrthogonalPolynomials.integral_eval_sq_pos](DLMF/OrthogonalPolynomials/Basic/General.lean#L226) — proved, no admission.
- [DLMF.OrthogonalPolynomials.IsOrthogonalPolynomials.memLp_eval](DLMF/OrthogonalPolynomials/Basic/General.lean#L117) — proved, no admission.
- [DLMF.OrthogonalPolynomials.bigQJacobi](DLMF/OrthogonalPolynomials/Basic/QFamilies.lean#L54) — definition, no admission.
- [DLMF.OrthogonalPolynomials.charlier](DLMF/OrthogonalPolynomials/Basic/AskeyScheme.lean#L88) — definition, no admission.
- [DLMF.OrthogonalPolynomials.charlier_coefficient_eq_sum](DLMF/OrthogonalPolynomials/CharlierCoefficientNormalization.lean#L27) — direct admission.
- [DLMF.OrthogonalPolynomials.charlier_orthogonality](DLMF/OrthogonalPolynomials/Hahn/Orthogonality.lean#L370) — proved, no admission.
- [DLMF.OrthogonalPolynomials.chebyshevT_eq_jacobi](DLMF/OrthogonalPolynomials/Differential/ClassicalEquations.lean#L1036) — proved, no admission.
- [DLMF.OrthogonalPolynomials.chebyshevT_hypergeometric](DLMF/OrthogonalPolynomials/Differential/ClassicalEquations.lean#L1017) — proved, no admission.
- [DLMF.OrthogonalPolynomials.deriv_gaussian_eq_hermitePolynomialH](DLMF/OrthogonalPolynomials/Classical.lean#L58) — proved, no admission.
- [DLMF.OrthogonalPolynomials.hasSum_charlier_coefficient](DLMF/OrthogonalPolynomials/CharlierCoefficientNormalization.lean#L35) — direct admission.
- [DLMF.OrthogonalPolynomials.hasSum_laguerreExtended_generating_function](DLMF/OrthogonalPolynomials/Classical.lean#L312) — proved, no admission.
- [DLMF.OrthogonalPolynomials.hermitePolynomialH](DLMF/OrthogonalPolynomials/Basic/Definitions.lean#L56) — definition, no admission.
- [DLMF.OrthogonalPolynomials.hermitePolynomialH_differential_equation](DLMF/OrthogonalPolynomials/Differential/ClassicalEquations.lean#L199) — proved, no admission.
- [DLMF.OrthogonalPolynomials.hermitePolynomialH_even_eq_laguerrePolynomialL](DLMF/OrthogonalPolynomials/Explicit.lean#L285) — proved, no admission.
- [DLMF.OrthogonalPolynomials.hermitePolynomialH_generating_function](DLMF/OrthogonalPolynomials/Classical.lean#L137) — proved, no admission.
- [DLMF.OrthogonalPolynomials.hermitePolynomialH_odd_eq_laguerrePolynomialL](DLMF/OrthogonalPolynomials/Explicit.lean#L305) — proved, no admission.
- [DLMF.OrthogonalPolynomials.hermitePolynomialH_orthogonality](DLMF/OrthogonalPolynomials/Integrals/AngularRepresentations.lean#L474) — proved, no admission.
- [DLMF.OrthogonalPolynomials.hermite_isOrthogonalPolynomials](DLMF/OrthogonalPolynomials/ClassicalInstances.lean#L240) — proved, no admission.
- [DLMF.OrthogonalPolynomials.hermite_orthogonality](DLMF/OrthogonalPolynomials/Integrals/AngularRepresentations.lean#L510) — proved, no admission.
- [DLMF.OrthogonalPolynomials.integral_eval_U_mul_of_ne](DLMF/OrthogonalPolynomials/General.lean#L516) — proved, no admission.
- [DLMF.OrthogonalPolynomials.integral_eval_U_mul_self](DLMF/OrthogonalPolynomials/General.lean#L568) — proved, no admission.
- [DLMF.OrthogonalPolynomials.iteratedDeriv_cexp_neg_sq](DLMF/OrthogonalPolynomials/Classical.lean#L82) — proved, no admission.
- [DLMF.OrthogonalPolynomials.jacobiPolyPR](DLMF/OrthogonalPolynomials/ClassicalInstances.lean#L515) — definition, no admission.
- [DLMF.OrthogonalPolynomials.jacobiPolynomialP](DLMF/OrthogonalPolynomials/Basic/Definitions.lean#L71) — definition, no admission.
- [DLMF.OrthogonalPolynomials.jacobiPolynomialP_one_eq](DLMF/OrthogonalPolynomials/Differential/ClassicalEquations.lean#L781) — proved, no admission.
- [DLMF.OrthogonalPolynomials.jacobiPolynomialP_orthogonal](DLMF/OrthogonalPolynomials/Classical.lean#L480) — proved, no admission.
- [DLMF.OrthogonalPolynomials.jacobi_differential_equation](DLMF/OrthogonalPolynomials/Differential/ClassicalEquations.lean#L128) — proved, no admission.
- [DLMF.OrthogonalPolynomials.jacobi_norm_all](DLMF/OrthogonalPolynomials/Integrals/AngularRepresentations.lean#L356) — proved, no admission.
- [DLMF.OrthogonalPolynomials.jacobi_recurrence](DLMF/OrthogonalPolynomials/Differential/ClassicalEquations.lean#L303) — proved, no admission.
- [DLMF.OrthogonalPolynomials.jacobi_reflection](DLMF/OrthogonalPolynomials/Differential/ClassicalEquations.lean#L821) — proved, no admission.
- [DLMF.OrthogonalPolynomials.jacobi_rodrigues](DLMF/OrthogonalPolynomials/Integrals/AngularRepresentations.lean#L791) — proved, no admission.
- [DLMF.OrthogonalPolynomials.laguerrePolyLR](DLMF/OrthogonalPolynomials/ClassicalInstances.lean#L389) — definition, no admission.
- [DLMF.OrthogonalPolynomials.laguerrePolynomialL](DLMF/OrthogonalPolynomials/Basic/Definitions.lean#L64) — definition, no admission.
- [DLMF.OrthogonalPolynomials.laguerrePolynomialL_differential_equation](DLMF/OrthogonalPolynomials/Differential/ClassicalEquations.lean#L179) — proved, no admission.
- [DLMF.OrthogonalPolynomials.laguerrePolynomialL_generating_function](DLMF/OrthogonalPolynomials/Classical.lean#L381) — proved, no admission.
- [DLMF.OrthogonalPolynomials.laguerrePolynomialL_orthogonal](DLMF/OrthogonalPolynomials/Classical.lean#L220) — proved, no admission.
- [DLMF.OrthogonalPolynomials.laguerrePolynomialL_recurrence](DLMF/OrthogonalPolynomials/Differential/ClassicalEquations.lean#L425) — proved, no admission.
- [DLMF.OrthogonalPolynomials.legendrePolynomialP](DLMF/OrthogonalPolynomials/Basic/Definitions.lean#L76) — definition, no admission.
- [DLMF.OrthogonalPolynomials.legendre_differential_equation](DLMF/OrthogonalPolynomials/Differential/ClassicalEquations.lean#L167) — proved, no admission.
- [DLMF.OrthogonalPolynomials.legendre_generating_function](DLMF/OrthogonalPolynomials/Series/ClassicalGenerating.lean#L670) — proved, no admission.
- [DLMF.OrthogonalPolynomials.littleQJacobi](DLMF/OrthogonalPolynomials/Basic/QFamilies.lean#L59) — definition, no admission.
- [DLMF.OrthogonalPolynomials.orthogonal_and_norm_of_rodrigues](DLMF/OrthogonalPolynomials/GeneralRodrigues.lean#L31) — direct admission.
- [DLMF.OrthogonalPolynomials.orthogonal_polynomials_roots](DLMF/OrthogonalPolynomials/General.lean#L351) — proved, no admission.
- [DLMF.OrthogonalPolynomials.three_term_recurrence](DLMF/OrthogonalPolynomials/Basic/General.lean#L245) — proved, no admission.
- [DLMF.OrthogonalPolynomials.three_term_recurrence_explicit](DLMF/OrthogonalPolynomials/GeneralRecurrenceCoefficients.lean#L26) — direct admission.
- [DLMF.OrthogonalPolynomials.ultrasph_isOrthogonalPolynomials](DLMF/OrthogonalPolynomials/ClassicalInstances.lean#L926) — proved, no admission.
- [DLMF.OrthogonalPolynomials.ultrasphericalPolynomial](DLMF/OrthogonalPolynomials/Basic/Definitions.lean#L83) — definition, no admission.
- [DLMF.OrthogonalPolynomials.ultrasphericalPolynomial_differential_equation](DLMF/OrthogonalPolynomials/Differential/ClassicalEquations.lean#L147) — proved, no admission.
- [DLMF.OrthogonalPolynomials.ultrasphericalPolynomial_even_at_zero](DLMF/OrthogonalPolynomials/Differential/ClassicalEquations.lean#L872) — proved, no admission.
- [DLMF.OrthogonalPolynomials.ultrasphericalPolynomial_generating_function](DLMF/OrthogonalPolynomials/Series/ClassicalGenerating.lean#L471) — proved, no admission.
- [DLMF.OrthogonalPolynomials.ultrasphericalPolynomial_norm](DLMF/OrthogonalPolynomials/Integrals/AngularRepresentations.lean#L616) — proved, no admission.
- [DLMF.OrthogonalPolynomials.ultrasphericalPolynomial_norm_of_nonzero](DLMF/OrthogonalPolynomials/GegenbauerNorm.lean#L27) — direct admission.
- [DLMF.OrthogonalPolynomials.ultrasphericalPolynomial_one_eq](DLMF/OrthogonalPolynomials/Differential/ClassicalEquations.lean#L795) — proved, no admission.
- [DLMF.OrthogonalPolynomials.ultrasphericalPolynomial_recurrence](DLMF/OrthogonalPolynomials/Differential/ClassicalEquations.lean#L368) — proved, no admission.
- [DLMF.Polylog.Real.dilog](DLMF/Polylog/Basic/Dilog.lean#L76) — definition, no admission.
- [DLMF.Polylog.Real.dilog_add_dilog_div_sub_one](DLMF/Polylog/Dilog.lean#L124) — proved, no admission.
- [DLMF.Polylog.Real.dilog_add_dilog_one_sub](DLMF/Polylog/Dilog.lean#L67) — proved, no admission.
- [DLMF.Polylog.Real.dilog_eq_double_integral](DLMF/Polylog/BookIdentities.lean#L181) — direct admission.
- [DLMF.Polylog.Real.dilog_goldenRatio](DLMF/Polylog/Dilog.lean#L206) — proved, no admission.
- [DLMF.Polylog.Real.dilog_one_half](DLMF/Polylog/Dilog.lean#L116) — proved, no admission.
- [DLMF.Polylog.Real.hasDerivAt_inversePolytangent_succ](DLMF/Polylog/BookIdentities.lean#L65) — direct admission.
- [DLMF.Polylog.Real.hasSum_inversePolytangent](DLMF/Polylog/BookIdentities.lean#L76) — direct admission.
- [DLMF.Polylog.Real.inversePolytangent](DLMF/Polylog/BookIdentities.lean#L34) — definition, no admission.
- [DLMF.Polylog.Real.inversePolytangent_def](DLMF/Polylog/BookIdentities.lean#L38) — proved, no admission.
- [DLMF.Polylog.Real.inversePolytangent_eq_hypergeometric](DLMF/Polylog/BookIdentities.lean#L83) — direct admission.
- [DLMF.Polylog.Real.inversePolytangent_eq_integral](DLMF/Polylog/BookIdentities.lean#L98) — direct admission.
- [DLMF.Polylog.Real.inversePolytangent_eq_polylog](DLMF/Polylog/BookIdentities.lean#L92) — direct admission.
- [DLMF.Polylog.Real.inversePolytangent_neg](DLMF/Polylog/BookIdentities.lean#L47) — direct admission.
- [DLMF.Polylog.Real.inversePolytangent_one](DLMF/Polylog/BookIdentities.lean#L52) — direct admission.
- [DLMF.Polylog.Real.inversePolytangent_one_arg](DLMF/Polylog/BookIdentities.lean#L71) — direct admission.
- [DLMF.Polylog.Real.inversePolytangent_succ](DLMF/Polylog/BookIdentities.lean#L58) — direct admission.
- [DLMF.Polylog.Real.inversePolytangent_zero](DLMF/Polylog/BookIdentities.lean#L42) — direct admission.
- [DLMF.Polylog.Real.trilog_goldenRatio_inv_sq](DLMF/Polylog/BookIdentities.lean#L111) — direct admission.
- [DLMF.Polylog.Real.trilog_landen](DLMF/Polylog/Trilog.lean#L189) — proved, no admission.
- [DLMF.Polylog.Real.trilog_one_half](DLMF/Polylog/Trilog.lean#L254) — proved, no admission.
- [DLMF.Polylog.hasDerivAt_polylog_exp_mul_I](DLMF/Polylog/BookIdentities.lean#L157) — direct admission.
- [DLMF.Polylog.integral_arsinh_sq_div](DLMF/Polylog/BookIdentities.lean#L219) — direct admission.
- [DLMF.Polylog.integral_mul_cot_pi_div_four](DLMF/Polylog/BookIdentities.lean#L202) — direct admission.
- [DLMF.Polylog.integral_mul_cot_pi_div_two](DLMF/Polylog/BookIdentities.lean#L197) — direct admission.
- [DLMF.Polylog.integral_pow_mul_cot](DLMF/Polylog/BookIdentities.lean#L187) — direct admission.
- [DLMF.Polylog.integral_pow_mul_coth](DLMF/Polylog/BookIdentities.lean#L209) — direct admission.
- [DLMF.Polylog.polylogSeries_add_polylogSeries_neg](DLMF/Polylog/Basic/Series.lean#L109) — proved, no admission.
- [DLMF.Polylog.polylogSeries_add_polylogSeries_neg_of_norm_le](DLMF/Polylog/Basic/Series.lean#L138) — proved, no admission.
- [DLMF.Polylog.polylogSeries_neg_one](DLMF/Polylog/Basic/Series.lean#L145) — proved, no admission.
- [DLMF.Polylog.polylog_natCast_I](DLMF/Polylog/BookIdentities.lean#L165) — direct admission.
- [DLMF.Polylog.polylog_natCast_conj](DLMF/Polylog/BookIdentities.lean#L142) — direct admission.
- [DLMF.Polylog.polylog_natCast_eq_hypergeometric](DLMF/Polylog/BookIdentities.lean#L126) — direct admission.
- [DLMF.Polylog.polylog_natCast_eq_unit_integral](DLMF/Polylog/BookIdentities.lean#L134) — direct admission.
- [DLMF.Polylog.polylog_one_I](DLMF/Polylog/BookIdentities.lean#L171) — direct admission.
- [DLMF.Polylog.polylog_three_ofReal_eq_trilog](DLMF/Polylog/BookIdentities.lean#L105) — direct admission.
- [DLMF.Polylog.polylog_two_I](DLMF/Polylog/BookIdentities.lean#L175) — direct admission.
- [DLMF.Polylog.tendsto_sum_polylog_exp_mul_I](DLMF/Polylog/BookIdentities.lean#L148) — direct admission.
- [DLMF.Polylog.tendsto_sum_polylog_natCast_closed_disk](DLMF/Polylog/BookIdentities.lean#L118) — direct admission.
- [DLMF.QHypergeometric.PfaffSaalschutz.sum_eq_quotient_of_ne_zero](DLMF/QHypergeometric/PfaffSaalschutz.lean#L77) — proved, no admission.
- [DLMF.QHypergeometric.QDenominatorRegular](DLMF/QHypergeometric/Basic/Series.lean#L86) — definition, no admission.
- [DLMF.QHypergeometric.QDenominatorRegularThrough](DLMF/QHypergeometric/Basic/Series.lean#L103) — definition, no admission.
- [DLMF.QHypergeometric.QTerminating](DLMF/QHypergeometric/Basic/Series.lean#L92) — definition, no admission.
- [DLMF.QHypergeometric.QuadraticTransformation.q_pfaff_saalschutz_ratio](DLMF/QHypergeometric/TerminatingQuadraticTransformation.lean#L139) — proved, no admission.
- [DLMF.QHypergeometric.heine_first](DLMF/QHypergeometric/BasicSummations/Heine.lean#L241) — proved, no admission.
- [DLMF.QHypergeometric.jackson_series_hasSum](DLMF/QHypergeometric/Calculus/JacksonIntegral.lean#L57) — proved, no admission.
- [DLMF.QHypergeometric.one_phi_zero](DLMF/QHypergeometric/BasicSummations/OnePhiZero.lean#L406) — proved, no admission.
- [DLMF.QHypergeometric.qDerivExtended_zero](DLMF/QHypergeometric/Basic/Calculus.lean#L57) — proved, no admission.
- [DLMF.QHypergeometric.qDerivIterate](DLMF/QHypergeometric/Basic/Calculus.lean#L49) — definition, no admission.
- [DLMF.QHypergeometric.qDeriv_leibniz](DLMF/QHypergeometric/Calculus/QDerivative.lean#L194) — proved, no admission.
- [DLMF.QHypergeometric.qExp](DLMF/QHypergeometric/Basic/Elementary.lean#L41) — definition, no admission.
- [DLMF.QHypergeometric.qExpBig](DLMF/QHypergeometric/Basic/Elementary.lean#L45) — definition, no admission.
- [DLMF.QHypergeometric.qPhi](DLMF/QHypergeometric/Basic/Series.lean#L74) — definition, no admission.
- [DLMF.QHypergeometric.qPhiExponent](DLMF/QHypergeometric/Basic/Series.lean#L65) — definition, no admission.
- [DLMF.QHypergeometric.qPhiPartial](DLMF/QHypergeometric/Basic/Series.lean#L83) — definition, no admission.
- [DLMF.QHypergeometric.qPhiTerm](DLMF/QHypergeometric/Basic/Series.lean#L69) — definition, no admission.
- [DLMF.QHypergeometric.qPhi_analytic_disc](DLMF/QHypergeometric/Convergence.lean#L713) — proved, no admission.
- [DLMF.QHypergeometric.qPhi_analytic_entire](DLMF/QHypergeometric/Convergence.lean#L725) — proved, no admission.
- [DLMF.QHypergeometric.qPhi_classical_limit](DLMF/QHypergeometric/Convergence.lean#L534) — proved, no admission.
- [DLMF.QHypergeometric.qPhi_hasSum](DLMF/QHypergeometric/Convergence.lean#L67) — proved, no admission.
- [DLMF.QHypergeometric.qPhi_terminates](DLMF/QHypergeometric/Convergence.lean#L393) — proved, no admission.
- [DLMF.QHypergeometric.q_chu_vandermonde_first](DLMF/QHypergeometric/BasicSummations/QGauss.lean#L36) — proved, no admission.
- [DLMF.QHypergeometric.tendsto_qPochhammer_normalized](DLMF/QHypergeometric/ClassicalLimits/ShiftedFactorials.lean#L50) — proved, no admission.
- [DLMF.QSeries.Real.erdosBorweinConstant](DLMF/QSeries/BookIdentities.lean#L130) — definition, no admission.
- [DLMF.QSeries.Real.erdosBorweinConstant_def](DLMF/QSeries/BookIdentities.lean#L133) — proved, no admission.
- [DLMF.QSeries.Real.hasSum_erdosBorweinConstant_accelerated](DLMF/QSeries/BookIdentities.lean#L144) — direct admission.
- [DLMF.QSeries.Real.irrational_erdosBorweinConstant](DLMF/QSeries/BookIdentities.lean#L152) — direct admission.
- [DLMF.QSeries.Real.summable_erdosBorweinConstant](DLMF/QSeries/BookIdentities.lean#L138) — direct admission.
- [DLMF.QSeries.continuous_qBinom](DLMF/QSeries/Basic/CalculusProperties.lean#L90) — proved, no admission.
- [DLMF.QSeries.eq_jacksonIntegral_of_qDeriv_eq](DLMF/QSeries/BookIdentities.lean#L83) — direct admission.
- [DLMF.QSeries.exists_pos_sin_log_ne_zero](DLMF/QSeries/BookIdentities.lean#L53) — direct admission.
- [DLMF.QSeries.hasSum_jacksonIntegral_powerSeries](DLMF/QSeries/BookIdentities.lean#L103) — direct admission.
- [DLMF.QSeries.hasSum_qDeriv_powerSeries](DLMF/QSeries/BookIdentities.lean#L93) — direct admission.
- [DLMF.QSeries.hasSum_qLogarithm](DLMF/QSeries/Logarithm.lean#L50) — direct admission.
- [DLMF.QSeries.heine_transformation](DLMF/QSeries/Identities.lean#L333) — proved, no admission.
- [DLMF.QSeries.heine_transformation_three](DLMF/QSeries/Heine.lean#L123) — proved, no admission.
- [DLMF.QSeries.jacksonIntegral](DLMF/QSeries/Basic/Pochhammer.lean#L44) — definition, no admission.
- [DLMF.QSeries.jacksonIntegral_qDeriv](DLMF/QSeries/QCalculus.lean#L52) — proved, no admission.
- [DLMF.QSeries.multipliable_one_sub_mul_pow](DLMF/QSeries/Basic/PochhammerProperties.lean#L197) — proved, no admission.
- [DLMF.QSeries.qBinom](DLMF/QSeries/Basic/Calculus.lean#L28) — definition, no admission.
- [DLMF.QSeries.qBinom_eq](DLMF/QSeries/QExponential.lean#L72) — proved, no admission.
- [DLMF.QSeries.qBinom_one](DLMF/QSeries/Basic/CalculusProperties.lean#L73) — proved, no admission.
- [DLMF.QSeries.qBinom_succ_succ](DLMF/QSeries/Basic/CalculusProperties.lean#L55) — proved, no admission.
- [DLMF.QSeries.qDeriv](DLMF/QSeries/Basic/Calculus.lean#L34) — definition, no admission.
- [DLMF.QSeries.qDeriv_cpow_real](DLMF/QSeries/BookIdentities.lean#L30) — direct admission.
- [DLMF.QSeries.qDeriv_eq_zero_iff_eq_limit](DLMF/QSeries/BookIdentities.lean#L59) — direct admission.
- [DLMF.QSeries.qDeriv_inv_qPochhammerInf](DLMF/QSeries/BookIdentities.lean#L114) — direct admission.
- [DLMF.QSeries.qDeriv_jacksonIntegral](DLMF/QSeries/QCalculus.lean#L36) — proved, no admission.
- [DLMF.QSeries.qDeriv_mul](DLMF/QSeries/Basic/CalculusProperties.lean#L115) — proved, no admission.
- [DLMF.QSeries.qDeriv_sin_log_eq_zero](DLMF/QSeries/BookIdentities.lean#L45) — direct admission.
- [DLMF.QSeries.qExp_mul_qExp](DLMF/QSeries/QExponential.lean#L146) — proved, no admission.
- [DLMF.QSeries.qLogarithm](DLMF/QSeries/Basic/Logarithm.lean#L24) — definition, no admission.
- [DLMF.QSeries.qLogarithm_def](DLMF/QSeries/Basic/Logarithm.lean#L27) — proved, no admission.
- [DLMF.QSeries.qLogarithm_eq_logarithmicDeriv](DLMF/QSeries/Logarithm.lean#L36) — direct admission.
- [DLMF.QSeries.qLogarithm_mul](DLMF/QSeries/Logarithm.lean#L43) — direct admission.
- [DLMF.QSeries.qPochhammer](DLMF/QSeries/Basic/Pochhammer.lean#L33) — definition, no admission.
- [DLMF.QSeries.qPochhammerInf](DLMF/QSeries/Basic/Pochhammer.lean#L39) — definition, no admission.
- [DLMF.QSeries.qPochhammerInf_ne_zero](DLMF/QSeries/Basic/PochhammerProperties.lean#L90) — proved, no admission.
- [DLMF.QSeries.qPochhammer_eq_sum_qBinom](DLMF/QSeries/QBinomial.lean#L38) — proved, no admission.
- [DLMF.QSeries.q_binomial_theorem](DLMF/QSeries/Pochhammer.lean#L190) — proved, no admission.
- [DLMF.QSeries.q_chu_vandermonde](DLMF/QSeries/Heine.lean#L145) — proved, no admission.
- [DLMF.QSeries.q_gauss_summation](DLMF/QSeries/Heine.lean#L87) — proved, no admission.
- [DLMF.QSeries.summable_jackson_of_tendsto](DLMF/QSeries/BookIdentities.lean#L68) — direct admission.
- [DLMF.QSeries.summable_qLogarithm](DLMF/QSeries/Logarithm.lean#L29) — direct admission.
- [DLMF.QSeries.tendsto_jacksonIntegral_zero](DLMF/QSeries/BookIdentities.lean#L76) — direct admission.
- [DLMF.QSeries.tendsto_qBinom](DLMF/QSeries/Basic/CalculusProperties.lean#L100) — proved, no admission.
- [DLMF.QSeries.tendsto_qDeriv_of_hasDerivAt_real](DLMF/QSeries/BookIdentities.lean#L38) — direct admission.
- [DLMF.QSeries.tendsto_qLogarithm](DLMF/QSeries/Logarithm.lean#L56) — direct admission.
- [DLMF.QSeries.tendsto_qPochhammer](DLMF/QSeries/Basic/PochhammerProperties.lean#L206) — proved, no admission.
- [DLMF.QSeries.tsum_div_qPochhammer](DLMF/QSeries/Heine.lean#L66) — proved, no admission.
- [DLMF.QSeries.tsum_pow_div_one_sub_pow_sq](DLMF/QSeries/BookIdentities.lean#L121) — direct admission.
- [DLMF.QSeries.tsum_qExp](DLMF/QSeries/QExponential.lean#L90) — proved, no admission.
- [DLMF.Struve.struveH](DLMF/Struve/Basic/Functions.lean#L56) — definition, no admission.
- [DLMF.Struve.struveH_ode](DLMF/Struve/SeriesAndEquations.lean#L522) — proved, no admission.
- [DLMF.Zeta.Real.alternatingHurwitzZeta](DLMF/Zeta/Basic/AlternatingHurwitz.lean#L25) — definition, no admission.
- [DLMF.Zeta.Real.alternatingHurwitzZeta_def](DLMF/Zeta/Basic/AlternatingHurwitz.lean#L29) — proved, no admission.
- [DLMF.Zeta.Real.alternatingHurwitzZeta_eq_integral](DLMF/Zeta/AlternatingHurwitz.lean#L77) — direct admission.
- [DLMF.Zeta.Real.alternatingHurwitzZeta_eq_lerchPhi](DLMF/Zeta/AlternatingHurwitz.lean#L63) — direct admission.
- [DLMF.Zeta.Real.alternatingHurwitzZeta_one](DLMF/Zeta/AlternatingHurwitz.lean#L57) — direct admission.
- [DLMF.Zeta.Real.alternatingHurwitzZeta_one_bounds](DLMF/Zeta/AlternatingHurwitz.lean#L83) — direct admission.
- [DLMF.Zeta.Real.alternatingHurwitzZeta_one_one](DLMF/Zeta/AlternatingHurwitz.lean#L89) — direct admission.
- [DLMF.Zeta.Real.dirichletBeta](DLMF/Zeta/Basic/AlternatingHurwitz.lean#L34) — definition, no admission.
- [DLMF.Zeta.Real.dirichletBeta_def](DLMF/Zeta/Basic/AlternatingHurwitz.lean#L38) — proved, no admission.
- [DLMF.Zeta.Real.dirichletBeta_two](DLMF/Zeta/AlternatingHurwitz.lean#L98) — depends on admission.
- [DLMF.Zeta.Real.hasSum_alternatingHurwitzZeta](DLMF/Zeta/AlternatingHurwitz.lean#L30) — direct admission.
- [DLMF.Zeta.Real.hasSum_dirichletBeta](DLMF/Zeta/AlternatingHurwitz.lean#L36) — direct admission.
- [DLMF.Zeta.Real.integrableOn_alternatingHurwitzZeta_kernel](DLMF/Zeta/AlternatingHurwitz.lean#L69) — direct admission.
- [DLMF.Zeta.Real.tendsto_alternatingHurwitzZeta_one](DLMF/Zeta/AlternatingHurwitz.lean#L93) — direct admission.
- [DLMF.Zeta.Real.tendsto_sum_alternatingHurwitzZeta](DLMF/Zeta/AlternatingHurwitz.lean#L43) — direct admission.
- [DLMF.Zeta.Real.tendsto_sum_dirichletBeta](DLMF/Zeta/AlternatingHurwitz.lean#L50) — direct admission.
- [DLMF.Zeta.analyticOnNhd_lerchPhi](DLMF/Zeta/Basic/LerchProperties.lean#L132) — proved, no admission.
- [DLMF.Zeta.analyticOnNhd_polylog](DLMF/Zeta/Basic/PolylogProperties.lean#L128) — proved, no admission.
- [DLMF.Zeta.hasDerivAt_polylog](DLMF/Zeta/Basic/PolylogProperties.lean#L158) — proved, no admission.
- [DLMF.Zeta.hasSum_lerchPhi](DLMF/Zeta/Basic/LerchProperties.lean#L101) — proved, no admission.
- [DLMF.Zeta.hasSum_riemannZeta_three_central_binom](DLMF/Zeta/IntegerArguments.lean#L618) — proved, no admission.
- [DLMF.Zeta.hurwitzZetaComplex](DLMF/Zeta/Basic/Hurwitz.lean#L477) — definition, no admission.
- [DLMF.Zeta.hurwitzZetaComplex_eq_lerchPhi](DLMF/Zeta/Lerch.lean#L82) — proved, no admission.
- [DLMF.Zeta.lerchPhi](DLMF/Zeta/Basic/Polylog.lean#L116) — definition, no admission.
- [DLMF.Zeta.lerchPhi_eq_integral](DLMF/Zeta/Lerch.lean#L174) — proved, no admission.
- [DLMF.Zeta.polylog](DLMF/Zeta/Basic/Polylog.lean#L81) — definition, no admission.
- [DLMF.Zeta.polylog_eq_integral](DLMF/Zeta/Polylog/Properties.lean#L588) — proved, no admission.
- [DLMF.Zeta.polylog_eq_mul_lerchPhi_of_mem_slitOne](DLMF/Zeta/Basic/LerchProperties.lean#L228) — proved, no admission.
- [DLMF.Zeta.polylog_one](DLMF/Zeta/Basic/PolylogProperties.lean#L231) — proved, no admission.
- [DLMF.Zeta.polylog_one_eq_neg_log](DLMF/Zeta/Basic/PolylogProperties.lean#L181) — proved, no admission.
- [DLMF.Zeta.polylog_two_ofReal_eq_dilog](DLMF/Zeta/Polylog/Properties.lean#L96) — proved, no admission.
- [DLMF.Zeta.polylog_zero_arg](DLMF/Zeta/Basic/Polylog.lean#L148) — proved, no admission.
- [DLMF.Zeta.polylog_zero_order](DLMF/Zeta/Basic/PolylogProperties.lean#L165) — proved, no admission.
- [DLMF.Zeta.slitOne](DLMF/Zeta/Basic/Polylog.lean#L61) — definition, no admission.
- [DLMF.Zeta.tendsto_lerchPhi_exp_zero](DLMF/Zeta/Basic/LerchProperties.lean#L262) — proved, no admission.
- [FormalMultilinearSeries.ofScalars](.lake/packages/mathlib/Mathlib/Analysis/Analytic/OfScalars.lean#L38) — definition, no admission.
- [HasFPowerSeriesOnBall](.lake/packages/mathlib/Mathlib/Analysis/Analytic/Basic.lean#L74) — definition, no admission.
- [HasFPowerSeriesOnBall.factorial_smul](.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean#L864) — proved, no admission.
- [HasProdLocallyUniformlyOn_euler_sin_prod](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Cotangent.lean#L136) — proved, no admission.
- [MeasureTheory.IsLaplaceTransformable](DLMFMathlib/Analysis/Integral/LaplaceDomain.lean#L39) — definition, no admission.
- [MeasureTheory.IsLaplaceTransformable.continuousOn](DLMFMathlib/Analysis/Integral/LaplaceDomain.lean#L55) — proved, no admission.
- [MeasureTheory.IsLaplaceTransformable.exists_integrableOn](DLMFMathlib/Analysis/Integral/LaplaceDomain.lean#L60) — proved, no admission.
- [MeasureTheory.IsLaplaceTransformable.integrableOn_of_abscissa_lt](DLMFMathlib/Analysis/Integral/LaplaceDomain.lean#L78) — direct admission.
- [MeasureTheory.IsLaplaceTransformable.mk](DLMFMathlib/Analysis/Integral/LaplaceDomain.lean#L49) — proved, no admission.
- [MeasureTheory.isLaplaceTransformable_iff](DLMFMathlib/Analysis/Integral/LaplaceDomain.lean#L44) — proved, no admission.
- [MeasureTheory.laplaceAbscissa](DLMFMathlib/Analysis/Integral/LaplaceDomain.lean#L66) — definition, no admission.
- [MeasureTheory.laplaceAbscissa_def](DLMFMathlib/Analysis/Integral/LaplaceDomain.lean#L72) — proved, no admission.
- [MeasureTheory.laplaceIntegral](DLMFMathlib/Analysis/Integral/LaplaceDomain.lean#L30) — definition, no admission.
- [MeasureTheory.laplaceIntegral_def](DLMFMathlib/Analysis/Integral/LaplaceDomain.lean#L34) — proved, no admission.
- [NNReal.agm](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ArithmeticGeometricMean.lean#L165) — definition, no admission.
- [NNReal.agmSequences](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ArithmeticGeometricMean.lean#L56) — definition, no admission.
- [NNReal.agmSequences_snd_sub_fst_le](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/ArithmeticGeometricMean.lean#L78) — proved, no admission.
- [ODE.analyticOnNhd_of_hasDerivAt_matrix_mulVec](DLMFMathlib/Analysis/ODE/RealAnalyticRegularity.lean#L29) — direct admission.
- [ODE.analyticOnNhd_of_iteratedDeriv_eq_sum](DLMFMathlib/Analysis/ODE/RealAnalyticRegularity.lean#L38) — direct admission.
- [ODE.existsUnique_linearCombination_of_wronskian_ne_zero](DLMFMathlib/Analysis/ODE/FundamentalPair.lean#L29) — direct admission.
- [Polynomial.Chebyshev.T](.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Chebyshev.lean#L67) — definition, no admission.
- [Polynomial.Chebyshev.T_real_cos](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Basic.lean#L149) — proved, no admission.
- [Polynomial.Chebyshev.U](.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Chebyshev.lean#L263) — definition, no admission.
- [Polynomial.Chebyshev.integral_T_real_mul_self_measureT_of_ne_zero](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Orthogonality.lean#L141) — proved, no admission.
- [Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT_of_ne](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Orthogonality.lean#L129) — proved, no admission.
- [Polynomial.Chebyshev.integral_eval_T_real_mul_self_measureT_zero](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Orthogonality.lean#L136) — proved, no admission.
- [Polynomial.Chebyshev.irrational_of_isRoot_T_real](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/RootsExtrema.lean#L314) — proved, no admission.
- [Polynomial.bernoulli](.lake/packages/mathlib/Mathlib/NumberTheory/BernoulliPolynomials.lean#L48) — definition, no admission.
- [Polynomial.derivative_euler_succ](DLMFMathlib/NumberTheory/EulerPolynomials.lean#L90) — proved, no admission.
- [Polynomial.derivative_integerSinePolynomial_eval_zero](DLMFMathlib/Analysis/SpecialFunctions/Trigonometric/IntegerSinePolynomial.lean#L52) — direct admission.
- [Polynomial.euler](DLMFMathlib/NumberTheory/EulerPolynomials.lean#L61) — definition, no admission.
- [Polynomial.euler_comp_one_sub_X](DLMFMathlib/NumberTheory/EulerPolynomials.lean#L259) — proved, no admission.
- [Polynomial.euler_eval_add_one_add](DLMFMathlib/NumberTheory/EulerPolynomials.lean#L215) — proved, no admission.
- [Polynomial.eval_eq_sum_fwdDiff_mul_choose](DLMFMathlib/Algebra/Polynomial/NewtonExpansion.lean#L28) — direct admission.
- [Polynomial.integerSinePolynomial](DLMFMathlib/Analysis/SpecialFunctions/Trigonometric/IntegerSinePolynomial.lean#L27) — definition, no admission.
- [Polynomial.integerSinePolynomial_def](DLMFMathlib/Analysis/SpecialFunctions/Trigonometric/IntegerSinePolynomial.lean#L33) — proved, no admission.
- [Polynomial.integerSinePolynomial_eval_sin](DLMFMathlib/Analysis/SpecialFunctions/Trigonometric/IntegerSinePolynomial.lean#L58) — direct admission.
- [Polynomial.integerSinePolynomial_eval_zero](DLMFMathlib/Analysis/SpecialFunctions/Trigonometric/IntegerSinePolynomial.lean#L46) — proved, no admission.
- [Polynomial.natDegree_integerSinePolynomial](DLMFMathlib/Analysis/SpecialFunctions/Trigonometric/IntegerSinePolynomial.lean#L40) — direct admission.
- [Real.GammaIntegral_convergent](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean#L66) — proved, no admission.
- [Real.GammaSeq_tendsto_Gamma](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L502) — proved, no admission.
- [Real.Gamma_add_one](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean#L410) — proved, no admission.
- [Real.Gamma_eq_integral](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean#L405) — proved, no admission.
- [Real.Gamma_mul_Gamma_add_half](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L618) — proved, no admission.
- [Real.Gamma_mul_Gamma_one_sub](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L512) — proved, no admission.
- [Real.Gamma_nat_eq_factorial](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean#L422) — proved, no admission.
- [Real.Gamma_one](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean#L416) — proved, no admission.
- [Real.Gamma_one_half_eq](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean#L306) — proved, no admission.
- [Real.Gamma_pos_of_pos](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean#L443) — proved, no admission.
- [Real.analyticOnNhd_iff_iteratedDeriv_bound](DLMFMathlib/Analysis/Analytic/DerivativeCriterion.lean#L30) — direct admission.
- [Real.arcosh](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Arcosh.lean#L61) — definition, no admission.
- [Real.arcosh_cosh](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Arcosh.lean#L93) — proved, no admission.
- [Real.arctan_inv_2_add_arctan_inv_3](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Arctan.lean#L329) — proved, no admission.
- [Real.arsinh](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Arsinh.lean#L54) — definition, no admission.
- [Real.arsinh_sinh](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Arsinh.lean#L96) — proved, no admission.
- [Real.contDiff_exp_neg_inv_sq](DLMFMathlib/Analysis/Analytic/DerivativeCriterion.lean#L39) — proved, no admission.
- [Real.cosh_arcosh](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Arcosh.lean#L77) — proved, no admission.
- [Real.deriv_pendulumAngle_zero](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/JacobiElliptic/Pendulum.lean#L163) — proved, no admission.
- [Real.eq_Gamma_of_log_convex](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/BohrMollerup.lean#L307) — proved, no admission.
- [Real.eq_pendulumAngle_of_hasDerivAt](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/JacobiElliptic/Pendulum.lean#L170) — proved, no admission.
- [Real.eulerMascheroniConstant](.lake/packages/mathlib/Mathlib/NumberTheory/Harmonic/EulerMascheroni.lean#L131) — definition, no admission.
- [Real.four_mul_arctan_inv_5_sub_arctan_inv_239](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Arctan.lean#L339) — proved, no admission.
- [Real.half_add_sub_sqrt_mul_le](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/ArithmeticGeometricMean.lean#L42) — proved, no admission.
- [Real.hasDerivAt_arcosh](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Arcosh.lean#L160) — proved, no admission.
- [Real.hasDerivAt_arsinh](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Arsinh.lean#L166) — proved, no admission.
- [Real.integral_rpow_mul_exp_neg_mul_Ioi](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean#L465) — proved, no admission.
- [Real.iteratedDeriv_exp_neg_inv_sq_zero](DLMFMathlib/Analysis/Analytic/DerivativeCriterion.lean#L49) — direct admission.
- [Real.not_analyticAt_exp_neg_inv_sq_zero](DLMFMathlib/Analysis/Analytic/DerivativeCriterion.lean#L55) — direct admission.
- [Real.pendulumAngle_zero](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/JacobiElliptic/Pendulum.lean#L154) — proved, no admission.
- [Real.sinh_arsinh](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Arsinh.lean#L75) — proved, no admission.
- [Real.two_mul_arctan_inv_2_sub_arctan_inv_7](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Arctan.lean#L332) — proved, no admission.
- [Ring.choose](.lake/packages/mathlib/Mathlib/RingTheory/Binomial.lean#L386) — definition, no admission.
- [Ring.choose_eq_descPochhammer_div](DLMFMathlib/RingTheory/Binomial.lean#L34) — proved, no admission.
- [TauCeti.Real.agmIntegral_eq_legendreK_div](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/Gauss.lean#L71) — proved, no admission.
- [TauCeti.Real.deriv_legendreEc](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/ModulusDerivative.lean#L253) — proved, no admission.
- [TauCeti.Real.deriv_legendreK](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/ModulusDerivative.lean#L248) — proved, no admission.
- [TauCeti.Real.erf](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/Erf.lean#L61) — definition, no admission.
- [TauCeti.Real.legendreEc](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/Legendre.lean#L100) — definition, no admission.
- [TauCeti.Real.legendreEc_differential_equation](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/ModulusDerivative.lean#L317) — proved, no admission.
- [TauCeti.Real.legendreK](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/Legendre.lean#L97) — definition, no admission.
- [TauCeti.Real.legendreK_differential_equation](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/ModulusDerivative.lean#L304) — proved, no admission.
- [TauCeti.Real.legendreK_eq_one_add_mul_legendreK](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/Gauss.lean#L107) — proved, no admission.
- [TauCeti.Real.legendreK_eq_pi_div_two_mul_agm](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/Gauss.lean#L63) — proved, no admission.
- [TauCeti.Real.legendreK_one_div_sqrt_two](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/Lemniscate.lean#L148) — proved, no admission.
- [TauCeti.Real.lemniscateConstant_eq_Gamma](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/Lemniscate.lean#L98) — proved, no admission.
- [TauCeti.Real.lemniscateConstant_eq_sqrt_two_mul_legendreK](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/Lemniscate.lean#L137) — proved, no admission.
- [TauCeti.multipliable_one_sub_pow_mul](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/QPochhammer.lean#L168) — proved, no admission.
- [TauCeti.tprod_one_sub_pow_mul_ne_zero](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/QPochhammer.lean#L222) — proved, no admission.
- [ascPochhammer](.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Pochhammer.lean#L51) — definition, no admission.
- [bernoulli_one](.lake/packages/mathlib/Mathlib/NumberTheory/Bernoulli.lean#L207) — proved, no admission.
- [bernoulli_zero](.lake/packages/mathlib/Mathlib/NumberTheory/Bernoulli.lean#L204) — proved, no admission.
- [cot_series_rep'](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Cotangent.lean#L226) — proved, no admission.
- [descPochhammer](.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Pochhammer.lean#L265) — definition, no admission.
- [eulerNumber](DLMFMathlib/NumberTheory/EulerPolynomials.lean#L312) — definition, no admission.
- [eulerNumber_eq_zero_of_odd](DLMFMathlib/NumberTheory/EulerPolynomials.lean#L320) — proved, no admission.
- [euler_summation_one_cell](DLMFMathlib/Analysis/Summation/PolynomialRemainders.lean#L63) — direct admission.
- [expNegInvGlue.contDiff](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean#L140) — proved, no admission.
- [fwdDiff](.lake/packages/mathlib/Mathlib/Algebra/Group/ForwardDiff.lean#L40) — definition, no admission.
- [hasAsymptoticExpansion_integral_exp_smul](DLMFMathlib/Analysis/Asymptotics/Watson.lean#L183) — proved, no admission.
- [integral_eq_sum_bernoulliFun_add](DLMFMathlib/Analysis/EulerMaclaurin.lean#L103) — proved, no admission.
- [integral_exp_mul_complex_Ioi](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean#L87) — proved, no admission.
- [integral_exp_neg_mul_mul_rpow_sub_one](DLMFMathlib/Analysis/Asymptotics/Watson.lean#L57) — proved, no admission.
- [integral_exp_neg_mul_rpow_sub_one_mul_log](DLMFMathlib/Analysis/Asymptotics/WatsonLog.lean#L59) — proved, no admission.
- [integral_gaussian_Ioi](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean#L289) — proved, no admission.
- [irrational_cos_rat_mul_pi](.lake/packages/mathlib/Mathlib/NumberTheory/Niven.lean#L164) — proved, no admission.
- [shift_eq_sum_fwdDiff_iter](.lake/packages/mathlib/Mathlib/Algebra/Group/ForwardDiff.lean#L165) — proved, no admission.
- [sum_choose_mul_eulerNumber](DLMFMathlib/NumberTheory/EulerPolynomials.lean#L327) — proved, no admission.

## Checked elementary derivations

The following examples check the Kummer U differential equation, continued Kummer summation
at minus one, and odd integrality of the even Euler numbers against the pinned imports.

```lean
import DLMF.Hypergeometric.Elementary.AlgebraicValues
import DLMF.Hypergeometric.Basic.Pochhammer
import DLMF.Confluent.Recurrence.Derivatives
import DLMF.Confluent.Recurrence.Contiguous
import DLMF.Hypergeometric.ArgumentContinuation
import DLMF.BernoulliEuler.Arithmetic

open Complex

example (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    z * iteratedDeriv 2 (DLMF.Confluent.kummerU a b) z +
      (b - z) * deriv (DLMF.Confluent.kummerU a b) z -
      a * DLMF.Confluent.kummerU a b z = 0 := by
  rw [DLMF.Confluent.iteratedDeriv_kummerU a b 2 hz,
    DLMF.Confluent.deriv_kummerU a b hz]
  norm_num [DLMF.Hypergeometric.pochhammer_succ, DLMF.Hypergeometric.pochhammer_zero]
  linear_combination a * DLMF.Confluent.kummerU_ode_contiguous a b z
    (slitPlane_ne_zero hz)

example (a b : ℂ) (hc : ∀ k : ℕ, 1 + a - b ≠ -(k : ℂ)) :
    Gamma (1 + a - b) *
      DLMF.Hypergeometric.regularizedGaussHypergeometric a b (1 + a - b) (-1) =
      (2 : ℂ) ^ (-a) * (Real.sqrt Real.pi : ℂ) * Gamma (1 + a - b) /
        (Gamma ((a + 1) / 2) * Gamma (1 + a / 2 - b)) := by
  have hC : (a + (1 + a - 2 * b) + 1) / 2 = 1 + a - b := by ring
  have hg := DLMF.Hypergeometric.gauss_second_summation (a := a)
    (b := 1 + a - 2 * b) (by simpa only [hC] using hc)
  rw [hC, DLMF.Hypergeometric.ordinaryHypergeometric_eq_Gamma_mul_regularizedGaussHypergeometric
    hc (by norm_num)] at hg
  have hv : (1 + a - 2 * b + 1) / 2 = 1 + a / 2 - b := by ring
  rw [hv] at hg
  have hp := DLMF.Hypergeometric.regularizedGaussHypergeometric_pfaff a b
    (1 + a - b) (z := -1) (by
      rw [DLMF.Hypergeometric.mem_cutPlane]
      norm_num [Complex.mem_slitPlane_iff])
  norm_num at hp
  have hab : 1 + a - b - b = 1 + a - 2 * b := by ring
  rw [hab] at hp
  rw [hp]
  calc
    _ = (2 : ℂ) ^ (-a) * (Gamma (1 + a - b) *
      DLMF.Hypergeometric.regularizedGaussHypergeometric a (1 + a - 2 * b)
        (1 + a - b) (1 / 2)) := by ring
    _ = _ := by rw [hg]; ring

example (n : ℕ) : ∃ z : ℤ, Odd z ∧ eulerNumber (2 * n) = z := by
  obtain ⟨z, hz⟩ :=
    (DLMF.BernoulliEuler.eulerNumber_eq_two_pow_mul_and_integer (2 * n)).2
  have hc := DLMF.BernoulliEuler.eulerNumber_two_mul_modEq_two_pow' (2 * n) 0 1
    (by simp [Nat.ModEq])
  dsimp only [DLMF.BernoulliEuler.RatModEq] at hc
  rw [hz] at hc
  norm_num at hc
  rw [← Int.cast_one, ← Int.cast_sub, Rat.num_intCast] at hc
  obtain ⟨k, hk⟩ := hc
  exact ⟨z, ⟨k, by omega⟩, hz⟩
```
