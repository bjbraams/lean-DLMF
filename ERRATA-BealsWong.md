# Source checks for Beals–Wong's theta and elliptic formulas

These checks refer to the PDFs in `../lean-CKMA/References`. The page formulas were
checked against rendered PDF pages as well as extracted text. No existing tagged
DLMF theorem or mathematical definition is changed by these source observations.

## More Explorations in Complex Functions, §11.3

On printed p. 272 (PDF page 281), the convergence argument displays a bound whose
left side is `|⟨BN,N⟩|` and whose right side is negative for a nonzero integer vector,
when `Re B` is negative definite. With `B = -1` and `N = 1`, this would say `1 ≤ -1`.
The useful estimate is instead

`Re(⟨BN,N⟩) = ⟨(Re B)N,N⟩ ≤ -b|N|²`.

Consequently the modulus of a summand is bounded by
`exp(-b|N|²/2 + |N||z|)`. The new analyticity theorem uses the existing convergent
theta series in the standard normalization and the proved change of matrix domain;
it does not depend on the printed absolute-value inequality.

On printed p. 273 (PDF page 282), equation (11.3.6) has the integer-period vector
in the linear exponent and omits the factor `θ(z)`. For the shift `2πiN + BM`,
the correct multiplier uses `M` in both its quadratic and linear terms:

`θ(z + 2πiN + BM) = exp(-⟨BM,M⟩/2 - ⟨M,z⟩) θ(z)`.

Putting both integer vectors equal to zero in the printed formula would require
`θ(z) = 1`. Putting `M = 0` also contradicts the integer-period formula (11.3.3).
The displayed characteristic law (11.3.10) uses the expected period-matrix vector
in the linear term. The corrected law is proved as
`DLMF.RiemannTheta.riemannThetaBig_add_lattice`, using `m` for the integer-period
vector and `n` for the period-matrix vector.

## Explorations in Complex Functions, Theorem 14.3.3

On printed p. 213 (PDF page 222), the converse asserts exact elliptic order `k`
for every quotient of `k` shifted theta factors satisfying the stated balance.
Exact order requires the numerator and denominator divisor classes not to cancel
and the scalar to be nonzero. Taking identical numerator and denominator lists
with `k = 2` and scalar one satisfies the displayed balance but gives a constant
meromorphic germ of order zero. The printed statement also allows a zero scalar.

The new genus-one quotient results assert meromorphy and periodicity. They permit
cancellation and make no assertion of exact pole order. The forward representation
of an arbitrary elliptic function by its divisor is not claimed by these results.
