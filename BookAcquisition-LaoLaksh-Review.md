# Rao–Lakshminarayanan Chapters 4–9 mathematical review

This review checks the new acquisition statements against their explicit definitions,
normalizations, convergence regions and finite supports. The synopsis is unchanged.
A mathematical consistency check is not a Lean proof of an admitted theorem.

## Angular momentum and factorial formulas

- `DLMF.WignerSymbols.SpinCoupling.coefficientMatrix` uses decreasing magnetic order in
  both factors and in each coupled block. Its canonical Clebsch–Gordan definition has
  the Condon–Shortley phase. `spinY` is `(raising-lowering)/(2i)`, consistent with that
  basis. The allowed doubled degrees `N₁+N₂-2k`, with `k≤min(N₁,N₂)`, include every
  nonnegative allowed total spin, including spin-zero blocks and `N₁=0` or `N₂=0`.
  The rectangular two-sided unitarity and intertwining statements have the correct
  product and block index types.
- `DLMF.WignerSymbols.ReggeArrays.spin` and `projection` reconstruct
  `(J-R₁ⱼ)/2` and `(R₃ⱼ-R₂ⱼ)/2`. Nonnegative common row/column sums imply all triangle,
  projection and half-integrality conditions. The row/column odd-permutation phases
  each equal `(-1)^J`; transposition has positive phase. The symmetric Racah sum uses
  reciprocal factorials, so its support excludes negative factorial arguments without
  applying natural subtraction to them. The ordinary `₃F₂` form separately requires
  both printed lower parameters to be positive integers; its finite factorial form
  remains available elsewhere.
- `DLMF.WignerSymbols.SixJCoordinates` uses the symbol `{a b e; d c f}` consistently
  with its four triangle factors. The inverse coordinate map and balance equation
  agree algebraically. Set I reverses the Racah index from a minimal quadrilateral
  sum; its lower parameter `-βₖ-1` has no zero through the retained degree
  `βₖ-α₀≤βₖ`. Set II starts at a maximal triangular sum, making all three lower
  parameters positive integers. Either chosen degree can exceed another upper
  termination; all excess terms then vanish. No additional global lower-parameter
  exclusion is needed for these finite sums. The full 144-coordinate action is
  compatible with the triangle/integrality conditions; inadmissibility is preserved
  under its inverse as well, consistent with the globally zero-extended symbol.
- `DLMF.Hypergeometric.FactorialTripleSeries.InSupport` guards every decreasing
  factorial argument. The three signs from negative individual and pairwise
  Pochhammer factors multiply to `(-1)^(m₀+m₁+m₂)`, as in the factorial definition.
  Beyond a negative lower parameter's finite support the totalized reciprocal
  Pochhammer factor vanishes, agreeing with the guarded factorial term. This
  identification does not establish the conjectural nine-j triple-sum phase.

The remaining eight linear identities of RL-7.09 are now proved in
[DLMF/WignerSymbols/NineJFactorialCoordinates.lean](DLMF/WignerSymbols/NineJFactorialCoordinates.lean).
Its `xParameters`, `yParameters`, `zParameters`, and `pairParameters` are the literal
rational linear combinations of the nine spins. `parameter_relations` verifies all
identities without admissibility or sign hypotheses. No conjectural nine-j equality
is used in this proof.

## Transformation groups and Whipple normalization

- `DLMF.Hypergeometric.ThomaeCoordinates.thomaeEquiv` has the displayed linear inverse.
  `thomaeEquiv_parameters` identifies it with a five-cycle on the actual affine
  invariant coordinates. The generated group is therefore the intended parameter
  action, rather than an unrelated abstract group of the same order.
- `DLMF.Hypergeometric.WhippleCoordinates` has the correct positive excess
  `αᵢⱼₖ`; replacing all coordinates by their negatives gives the complementary excess
  because the six coordinates sum to zero. Equality of the ten arrangements is
  asserted on the common positive-excess, regular-lower locus. The literal ordinary
  quotient definition alone does not assign analytic continuation values at lower
  poles. For terminating cases, `scaledThreeF2_eq` and `scaledThreeF2_action` provide
  the denominator-cleared polynomial extension instead.
- The six factors and the `(-1)^N` sign in `terminating_relations` agree with direct
  finite evaluation for all six arrangements at four regular sample coordinate
  sets, with `N=0,1,2,3`, to 40-digit arithmetic. This is only a normalization sanity
  check, not proof. The independent check is recorded in the temporary review script
  used during development; the Lean targets remain admitted.
- The signed terminating coordinate action preserves the constraint
  `α₃₄₅=-N`: its generators either permute within the two triples or exchange them
  while reversing all coordinate signs. The four-dimensional subspace with both
  triple sums zero is invariant. The constant vector carries the sign character,
  while the difference of the two triple indicators is invariant, matching the
  stated two one-dimensional summands.

## Kampé de Fériet and beta-generated identities

The convergence inequalities in `KampeDeFeriet.summable_term_one` control both
coordinate axes; away from the axes the common lower Pochhammer supplies the
additional binomial decay. In `euler_transformation`, the two transformed excesses
are `d-a` and `d+e-a-b-c+a+ΣG-ΣF`; the stated hypotheses make them positive.

The three one-direction-terminating identities initially required globally regular
lower parameters even in their finite direction. This excluded valid later lower
poles. The new untagged statements now retain finite nonvanishing conditions there:

- `terminating_to_coupled`: the unbounded direction retains global regularity of
  `d,e',d-b`; the finite direction needs only `e,1+a-e-N,1-b-N` through `N`.
- `coupled_reduction_complementary`: global regularity of `e,1+e-c`; finite
  nonvanishing for `c,d,1+a-d-N,c-e+a'+b'` through `N`.
- `coupled_reduction_shared_lower`: global regularity of `e,c'`; finite
  nonvanishing for `c,1+a-c-N,1+a'+b'-c'` through `N`.

The triangular identities have `m+n≤N`; their hypotheses already quantify all
retained lower factors. The rectangular Carlitz sums have `m≤n₀,n≤m₀`, and
nonvanishing of the last retained Pochhammer implies nonvanishing at every earlier
index. No nonterminating absolute-summability claim is needed for these finite sums.

The six generic `SeedTransformations` statements use genuine regular analytic germs
or convergent unit-argument series. For the connection beta transform, the first
series has excess `d+e-a-b-c`, while both transformed series have excess `1+c-d`;
both required inequalities appear explicitly. For the even–odd beta transform,
both `₄F₃(1)` excesses equal `e-d+(1-a-b)/2`, precisely its explicit hypothesis.
Gamma factors in denominators are interpreted through their reciprocal zeros;
no unnecessary exclusion of a denominator Gamma pole is imposed.

The missing coherent-germ adapter for RL-8.13 is now acquired in
[DLMF/Hypergeometric/QuadraticGerms.lean](DLMF/Hypergeometric/QuadraticGerms.lean).
`eventuallyEq_quadratic_inverse_sqrt` states the identity on a whole complex
neighborhood of zero, and
`generalizedHypergeometricTruncated_quadratic_inverse_sqrt` gives its finite form
for every `t≠1`, assuming nonzero lower factors only through degree `N`. These two
targets remain admitted. The finite form uses the polynomial power `(1-t)^(2N)`,
so it needs no coherent-root hypothesis.

Independently truncating exceptional lower parameters in a generic Euler/Pfaff or
quadratic identity need not preserve the whole analytic family's limit. The
counterexamples already recorded in the revision notes remain exceptions to the
synopsis's blanket finite-specialization rule; no false variant was acquired.

## Ramanujan and digamma families

`RamanujanDigamma` correctly distinguishes the natural-order alternating half-cubed
series from the absolutely convergent quarter-fourth and half-fifth series.
The repeated-parameter `₃F₂` has excess `N+2-x`, so its domain `Re x<N+2` is exact.
The Gamma/digamma quotient is stated only on its literal regular locus; the whole
family, rather than an isolated totalized digamma factor, has the removable value
at `a=0`.

For an excluded `x₀` inside that half-plane, the whole right-hand-side removable
limit follows directly from its regular-locus identity and
`DLMF.Hypergeometric.UnitParameterSeries.analyticOnNhd_generalizedHypergeometric_one`:
compose the latter with the affine map
`x↦![a,a,x,a+1,a+N+1]`, take its continuity limit, and replace the function on the
regular-locus filter using the displayed identity. The `N=0,a=1/2` specialization
likewise gives all removable values of the half-repeated family. This derivation
uses analyticity of the actual convergent unit series, not convergence of the
Gauss series outside `Re x<1`.

## Exact pointers closing earlier ledger questions

- RL-7.01: `DLMF.Hypergeometric.generalizedHypergeometric_theta_ode` in
  `DLMF/GeneralizedHypergeometric/DifferentialEquations.lean`; the finite-only case
  is `DLMF.Hypergeometric.generalizedHypergeometricTruncated_theta_ode` in
  `DLMF/GeneralizedHypergeometric/TerminatingDifferentialEquation.lean`.
- RL-7.02: the four canonical Appell families and their convergence theorems are in
  `Appell/Basic/Series.lean` and `Appell/SeriesAndDifferentialEquations.lean`.
  The exact last sum-to-Gauss claim is
  `DLMF.Hypergeometric.hasSum_double_pochhammer_eq_ordinaryHypergeometric_add`
  in `Appell/DiagonalReduction.lean`, with `‖x‖+‖y‖<1` and regular `c`.
- RL-7.11: `DLMF.Hypergeometric.generalizedHypergeometricTruncated_karlsson_minton`
  in `GeneralizedHypergeometric/KarlssonMinton.lean`, including empty lists;
  `DLMF.Hypergeometric.sum_pochhammer_mul_neg_nat_div` and
  `DLMF.Hypergeometric.pfaff_saalschutz_of_finite_regular` in
  `Hypergeometric/TerminatingSummations.lean`. All require only the retained
  finite lower factors, including lower poles beyond termination.
- RL-8.01: Mathlib `Complex.betaIntegral`, `Complex.betaIntegral_convergent`, and
  `Complex.Gamma_mul_Gamma_eq_betaIntegral` in
  `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean`. The positivity of the two
  real parts implies that `Gamma(u+v)` is nonzero, yielding the exact quotient.

RL-7.08, the phase-dependent parts of RL-7.10, and RL-7.12 inherit the explicitly
conjectural source-repair issue already recorded in the synopsis. They are not
new valid acquisition gaps, and no admission of a conjectural repair was added.
