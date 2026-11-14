# Temme Chapter 1 acquisition audit

This companion covers every group TEM-01-01 through TEM-01-16 of
[SYNOPSIS-Temme.md](SYNOPSIS-Temme.md), including the individual subclaims.
The source is Temme, *Special Functions*, Chapter 1, pp. 1–27.
The synopsis is unchanged. Search order was pinned Mathlib, pinned TauCeti,
then DLMF. An admission is acquisition coverage, not a completed proof.

Local Bernoulli/Euler names below belong to `DLMF.BernoulliEuler`, unless
another namespace is supplied explicitly. New generic results are registered
through the DLMFMathlib umbrella by the integration agent.

## TEM-01-01: Bernoulli definitions and complex order

- Mathlib `bernoulli` and `Polynomial.bernoulli` are canonical. The local complex
  evaluation is `bernoulliPolyB`; `bernoulliPolyB_zero_arg` identifies the numbers.
  Existing `hasSum_bernoulliPolyB_mul_pow_div` in `Basic/GeneratingFunctions.lean`
  is the full complex generating series on the punctured `2π` disk. Its zero
  argument follows directly because all positive powers vanish and `B_0 = 1`.
- New shared canonical `ComplexOrder.bernoulliPolynomial` in
  `Basic/ComplexOrder.lean` is a finite formula using the existing Nörlund
  polynomials. Its defining equation is proved. Shared new admissions
  `ComplexOrder.bernoulliPolynomial_natCast` and `exists_bernoulli_generating_log`
  in `Generalizations/ComplexOrder.lean` give the natural-order bridge and the
  normalized analytic logarithm on the full disk.
- Newly admitted `ComplexOrder.monic_bernoulliPolynomial` and
  `exists_polynomial_coeff_bernoulliPolynomial` in
  `Generalizations/ComplexOrderProperties.lean` give exact degree, monicity and
  polynomial dependence on complex order. Coefficient `j` has order degree at
  most `n-j`, including its zero value for `j > n`.

## TEM-01-02: elementary identities

- Translation: `bernoulliPolyB_add` in `Basic/Polynomials.lean`.
  Reflection: `bernoulliPolyB_one_sub` in `Properties.lean`, also Mathlib
  `Polynomial.bernoulli_comp_one_sub_X`. The endpoint formula is
  `bernoulliPolyB_zero_one`, with the zero-argument bridge above.
- Derivatives: `hasDerivAt_bernoulliPolyB`; polynomial versions are Mathlib
  `Polynomial.derivative_bernoulli_add_one` and `derivative_bernoulli`.
- Unit differences: `bernoulliPolyB_add_one_sub`, also Mathlib
  `Polynomial.bernoulli_comp_one_add_X`.
- The integral is existing `integral_bernoulliFun_add_one` in `IntegralsSums.lean`:
  at `x=0`, its right side is zero for positive degree.
- Seeds are Mathlib `bernoulli_zero`, `bernoulli_one`; the binomial recurrence
  is `sum_choose_mul_bernoulli_eq_zero` in `Recurrences.lean` (replace its index
  by `n+1`), also Mathlib `sum_bernoulli`.
- Odd vanishing and even signs: `bernoulli_two_mul_add_one_eq_zero_and_sign`.
  The half argument is `bernoulliPolyB_half` in `Properties.lean`.

## TEM-01-03: tangent coefficients

- The canonical `tangentNumber` and its Bernoulli generating series are in
  `Basic/RelatedNumbers.lean`; the expansion radius is `π/2`.
- Shared new admitted `tangentNumber_succ` and
  `exists_pos_natCast_tangentNumber_odd` in `TangentCoefficients.lean` give
  the derivative convolution and positive-integer property. They include the
  initial coefficient and encode the recursion from `T' = 1+T²`.

## TEM-01-04: Fourier series, signs and strict bounds

- Existing real Fourier identities are `hasSum_one_div_nat_pow_mul_cos` and
  `hasSum_one_div_nat_pow_mul_sin`; the first includes both endpoints.
- Degree one uses ordered convergence `tendsto_sum_sin_div_eq_bernoulliFun_one`
  in `Series.lean`. At either endpoint each sine summand is zero; hence the
  series value is zero, the required midpoint value rather than `B_1(0)`.
- Mathlib `hasSum_zeta_nat` gives the exact even-zeta evaluation. The local
  `bernoulli_two_mul_add_one_eq_zero_and_sign` gives the signs.
- Newly admitted `bernoulli_two_mul_elementary_bounds` in `ElementaryBounds.lean`
  gives exactly both strict inequalities for every `n ≥ 1`. Existing
  `bernoulli_two_mul_zeta_bounds` is a sharper but differently expressed bound.

## TEM-01-05: corrected periodization

- Canonical `periodicBernoulli` is in `DLMFMathlib.Analysis.EulerMaclaurin`;
  `periodicBernoulliB_eq_periodizedBernoulli` identifies the area convention.
- Shared new admitted `contDiff_periodicBernoulli`,
  `hasDerivAt_periodicBernoulli`, `tendsto_periodicBernoulli_one_sides` in
  `DLMFMathlib/Analysis/Summation/PolynomialRemainders.lean` give precisely
  `C^(n-2)`, off-integer derivatives and the downward jump of size one.
  They do not reproduce the erroneous `C^(n-1)` source assertion.

## TEM-01-06: all antidifferences and Faulhaber

- Existing proved `Polynomial.exists_eval_add_one_sub_eval_eq` in
  `DLMFMathlib/Algebra/Polynomial/FiniteDifference.lean` constructs a normalized
  polynomial primitive, over every characteristic-zero field.
- Newly admitted `Polynomial.forall_eval_add_one_sub_eq_iff_exists_periodic`
  in `FiniteDifferenceClassification.lean` gives the full explicit Bernoulli
  sum plus an arbitrary unit-periodic function, with no continuity assumption.
- Mathlib `Polynomial.sum_range_pow_eq_bernoulli_sub` is Faulhaber, including
  exponent zero. It retains Lean's `0^0 = 1` convention in this polynomial identity.

## TEM-01-07: one-cell Euler summation

- Shared new admitted `euler_summation_one_cell` in
  `DLMFMathlib/Analysis/Summation/PolynomialRemainders.lean` uses a complete
  normed vector target and a supplied continuous derivative chain. This includes
  every complex `C^k` function, and retains the exact endpoint and remainder signs.

## TEM-01-08: finite and infinite Euler–Maclaurin

- Shared new admitted `sum_range_eulerMaclaurin_local` and
  `tendsto_sum_eulerMaclaurin_local` in the same generic module give the finite
  and infinite formulas using local endpoint jets and ordinary improper limits.
- The general older exact summation API is
  `sum_range_succ_eq_integral_add` in `DLMFMathlib.Analysis.EulerMaclaurin`.
  Translating the integer lower endpoint and choosing the odd derivative order
  gives the displayed source convention.

## TEM-01-09: strict enveloping remainder

- Shared new admitted `exists_eulerMaclaurin_remainder_factor` and
  `exists_eulerMaclaurin_tail_remainder_factor` in `PolynomialRemainders.lean`
  give the strict `0 < θ < 1` factor at finite and infinite endpoints.
- The hypotheses retain the monotonicity, decay and integral convergence of
  the supplied derivative chain. If the first omitted coefficient is zero,
  the factor formulation still correctly permits a zero remainder.

## TEM-01-10: Euler constant, harmonic and power tails

- Mathlib `Real.tendsto_harmonic_sub_log` gives existence and the canonical
  `Real.eulerMascheroniConstant`.
- Existing `DLMF.AsymptoticApproximations.harmonic_asymptotic` and
  `harmonic_remainder_bound` in `AsymptoticApproximations/Sums/EulerMaclaurin.lean`
  give the full harmonic expansion and signed first-omitted-term bound.
  Their function is `H_(n-1)` with coefficient `-1/(2n)`. The exact identity
  `H_n = H_(n-1)+1/n` for positive `n` gives the synopsis's `+1/(2n)` display.
- Existing `DLMF.Zeta.hasSum_hurwitzZetaComplex` identifies every real `s>1`
  power tail with `hurwitzZetaComplex s n`; `hurwitzZetaComplex_asymptotic`
  in `HurwitzAsymptotics.lean` gives every algebraic order, even on closed
  complex sectors. The derivative factors are exactly `(s)_r` in its formula.
  The exact scalar omitted-term formula, including its strict factor `0<θ<1`,
  is newly admitted `Real.exists_powerTail_remainder_factor` in
  `DLMFMathlib/Analysis/Asymptotics/PowerTailRemainder.lean`.
  It includes absolute summability and every positive real shift.

## TEM-01-11: Euler definitions and symmetries

- Canonical generic `Polynomial.euler`, `eulerNumber`, `eulerFun` live in
  `DLMFMathlib.NumberTheory.EulerPolynomials` and `EulerNumbers`. The complex
  local evaluation is `eulerPolyE`.
- `eulerNumber_eq_two_pow_mul_and_integer` gives the half-argument relation and
  integrality; `eulerNumber_two_mul_add_one_eq_zero_and_sign` includes odd
  vanishing. `hasDerivAt_eulerPolyE` gives derivatives, including degree zero.
- `eulerPolyE_one_sub`, `eulerPolyE_add_one_add`, `eulerPolyE_add` give reflection,
  unit shift and translation. Their generic polynomial counterparts are
  `Polynomial.euler_comp_one_sub_X`, `euler_comp_X_add_one_add` and
  `euler_comp_X_add_C`.
- Shared new canonical `ComplexOrder.eulerPolynomial`, admitted natural-order
  bridge and `exists_euler_generating_log` give the normalized complex-order
  series on the full `π` disk. New admitted `monic_eulerPolynomial` and
  `exists_polynomial_coeff_eulerPolynomial` give its parameter and degree API.

## TEM-01-12: Euler Fourier series, bound and antiperiodicity

- Existing `hasSum_cos_odd_eulerFun` and `hasSum_sin_odd_eulerFun` in
  `Series.lean` give the two corrected Fourier series on the closed interval.
- Newly admitted `abs_eulerFun_two_mul_le` in `ElementaryBounds.lean` gives the
  exact absolute bound on all of `[0,1]`, including `n=0`.
- Canonical `antiperiodicEuler` is in `DLMFMathlib.Analysis.BooleSummation`.
  Shared new proved `antiperiodic_antiperiodicEuler` and admitted
  `contDiff_antiperiodicEuler` in `PolynomialRemainders.lean` give the integer
  antiperiodicity and corrected `C^(n-1)` assertion. Applying antiperiodicity
  twice gives period two.

## TEM-01-13: corrected one-cell Boole

- Shared new admitted `boole_summation_one_cell` in `PolynomialRemainders.lean`
  carries the exact corrected `(-1)^(k+1)` remainder factor and includes complex
  functions via its complete normed vector target.

## TEM-01-14: infinite shifted Boole and explicit alternating tail

- Shared new admitted `tendsto_boole_summation_shifted` retains derivative decay,
  absolute integrability of the top derivative, ordered summation and the shifted
  antiperiodic kernel. No absolute convergence of the alternating series is asserted.
- Shared new admitted `exists_alternating_odd_harmonic_remainder` gives the exact
  Euler-number truncation and its absolute first-omitted-term bound for positive
  integer lower endpoint and truncation order.

## TEM-01-15: both Stirling conventions, positivity and inverses

- Use Mathlib `Nat.stirlingFirst` (unsigned) and `Nat.stirlingSecond`, and the
  canonical `DLMF.Combinatorics.signedStirlingFirst`. The latter's
  `neg_one_pow_mul_signedStirlingFirst` is the exact convention bridge.
- The polynomial expansions are `descPochhammer_eq_sum` and
  `X_pow_eq_sum_stirlingSecond_mul_descPochhammer` in
  `Combinatorics/Stirling/DefinitionsAndSeries.lean`.
- Signed recurrence and all seeds are in `Combinatorics/Basic/Stirling.lean`;
  Mathlib's `stirlingSecond_succ_succ`, `zero`, `zero_succ`, `succ_zero`,
  `eq_zero_of_lt` and `self` give the second-kind recurrence and all boundaries.
- Newly proved `Nat.stirlingFirst_pos` and `Nat.stirlingSecond_pos` in
  `DLMFMathlib/Combinatorics/StirlingPositivity.lean` give strict positivity
  for `1 ≤ k ≤ n`. The signed bridge gives the source's first-kind sign.
- Both inverse convolution orders are already proved by
  `DLMF.Combinatorics.sum_signedStirlingFirst_mul_stirlingSecond` and its primed
  counterpart in `Stirling/RecurrencesAndIdentities.lean`. Scalar commutativity
  turns the first into the source's second product order. `stirlingMatrix_inv`
  gives the corresponding finite rational matrix inverse; no second inverse
  axiom is needed. The finite transform-inversion assertions follow by exchanging
  finite sums and applying these Kronecker identities.

## TEM-01-16: complex Stirling generating functions

- Shared newly admitted `DLMF.Combinatorics.hasSum_signedStirlingFirst_complex`
  and `hasSum_stirlingSecond_complex` in `Stirling/ComplexGeneratingFunctions.lean`
  give the full principal logarithmic disk and the entire exponential identity.
  The zero degrees and zero coefficients are included in their natural-index sums.
- Existing proved `DLMF.Combinatorics.stirlingSecond_eq_sum_pow` is the finite
  alternating binomial formula with its factorial normalization.

## Validation

All newly added statements above have passed direct strict Lean source checks.
The targeted build of the four initial Chapter 1 modules passed (6735 jobs);
the additional scalar power-tail module passed its target build (5015 jobs).
A strict axiom audit of 29 reused declarations passed with no `sorryAx`.
The two strict Stirling positivity proofs have only `propext` and `Quot.sound`
as axioms; no `sorryAx` or choice is used. The signed convention corollary was
also checked in `/tmp/AAR-stirling-positivity-audit.lean`. The scalar power-tail
specialization is acquired explicitly above. The harmonic index conversion is
Mathlib's exact `harmonic_succ (n-1)`, using `n-1+1=n` for positive n and
casting its rational reciprocal to the reals; this adapter was accepted in
`/tmp/AAR-harmonic-shift.lean`. No source statement, canonical
definition body or synopsis was changed.
