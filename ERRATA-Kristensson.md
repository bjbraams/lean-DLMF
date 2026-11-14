# Errata and mathematical qualifications: Kristensson

Source: Gerhard Kristensson, *Second Order Differential Equations: Special Functions
and Their Classification* (Springer, 2010), the PDF in `References/`.
These are findings from reading the supplied edition, not a publisher's official list.
Printed pages are the primary locator. The first two findings were checked against rendered
PDF pages, so they are print issues rather than text-extraction artifacts.

## K-E1: missing argument factor in Lemma 5.1

- Location: printed p. 69, PDF p. 80, Lemma 5.1 and the immediately preceding display.
- Issue: the coefficient of `F(a,b;c+1;z)` lacks a factor `z`.
- Corrected identity, with `c`, `c-1` and `c+1` admissible lower parameters, is

  $$
  (1-z)F(a,b;c-1;z)=
  \left(1+\frac{z(a+b-2c+1)}{c-1}\right)F(a,b;c;z)
  +\frac{z(a-c)(b-c)}{c(c-1)}F(a,b;c+1;z).
  $$

- Evidence: all three hypergeometric functions equal `1` at `z=0`. Taking
  `a=b=1`, `c=3` makes the printed equality `1=1+2/3`. The preceding unsimplified
  equation on the same page retains the outer factor `z`; dividing and rearranging it
  gives the correction. SYNOPSIS-Kristensson item K-5.04 records the corrected identity.

## K-E2: final exponent in the Vandermonde determinant

- Location: printed p. 35, PDF p. 47, footnote 4.
- Issue: the displayed determinant with `n` columns ends in the powers `a_j^n`.
  The Vandermonde determinant has rows of powers `0,1,...,n-1`, so the final row must
  instead be `a_1^{n-1},...,a_n^{n-1}`.
- Evidence: the matrix must be square, and
  `det (a_j^i)_{0≤i,j<n}=∏_{i>j}(a_i-a_j)`. For two columns, replacing the final
  row by squares gives `a_2²-a_1²`, not `a_2-a_1`.

## Qualifications to preserve during formalization

- Printed p. 23, the sentence preceding Theorem 2.4 says a logarithmic term appears
  in both resonant cases. For distinct exponents differing by an integer its coefficient
  can be zero: `u''=0` has exponents `1,0` and solutions `z,1` without logarithms.
  The theorem's displayed formula permits that zero coefficient. Read the prose as
  saying that a logarithmic term **may** appear; do not assert that it must be nonzero.
- A branch of every nonintegral power and logarithm must be fixed on a simply connected
  punctured domain before using the local Frobenius and contour formulas. This makes the
  book's analytic conventions explicit, rather than changing its mathematics.

## Extraction cautions

The embedded text layer separates fraction bars, superscripts and integral limits.
The glyph rendered as `6=` by extraction is the ordinary not-equal sign in the page image.
Such text-layer artifacts are not additional errata.

## K-E3: convergence versus the prescribed minimal solution in Theorem B.3

- Location: printed pp. 184–185, PDF pp. 193–194, Theorem B.3 (Pincherle).
- Issue: the continued fraction depends on the recurrence coefficients, while the
  assertion identifies its convergence with minimality of the solution initialized by
  an arbitrary `A₀`. Convergence alone does not impose the correct initial ratio.
- Explicit counterexample: take `A_n=3`, `B_n=-2` for every `n≥1`, `A₀=3`,
  `x₀=1`. Then `x_n=2^{n+1}-1`; the minimal solution is the constant sequence.
  Nevertheless the finite fractions `-2/(3-2/(3-...))` converge to `-1`, and the
  fraction with head `A₀` converges to `2`. The prescribed sequence is not minimal.
  For example its ratio to the dominant solution `2^n` tends to `2`, not `0`.
- Correct distinction: convergence of the tail fraction is equivalent to existence of a
  minimal solution with nonzero zeroth term; its limit is minus that solution's initial
  ratio. A **prescribed** solution is minimal precisely when that limit equals
  `-x₁/x₀=-A₀`, equivalently when the whole fraction converges to **zero**.
  SYNOPSIS-Kristensson K-B.06 separates these two assertions.
- The printed page was rendered and checked; the missing zero-value requirement is not
  caused by extraction. This affects the exact statement of the theorem, not just its proof.

## K-E4: regular versus regular singular in §7.2

- Location: printed p. 133, PDF p. 143, paragraph following equation (7.11).
- Issue: the origin of `z u''+c u'-u=0` is called a regular point.
- Correction: it is a **regular singular** point. After dividing by `z`, the coefficient
  of `u` is `-1/z`, which is singular at zero, while `z·(c/z)=c` and
  `z²·(-1/z)=-z` are analytic. The next paragraph already uses the correct terminology.
- Checked against the rendered page.

## K-E5: wrong dependent-function name after (7.11)

- Location: printed p. 133, PDF p. 143, equation obtained after setting
  `v(z)=z^{1-c} f(z)`.
- Issue: the final term is printed as `-u(z)`.
- Correction: it must be `-f(z)`, giving `z f''+(2-c)f'-f=0`.
- Evidence: direct substitution into `z v''+c v'-v=0` gives the corrected equation.
  This is also the differential equation of the next displayed solution
  `f(z)={}_0F_1(;2-c;z)`. Checked against the rendered page.

## K-E6: a gauge can remove a regular singularity

- Location: printed pp. 36–37, Theorem 3.3 and its introduction.
- Issue: the coefficient and exponent transformations are correct, but the unrestricted
  assertion that singular points keep their singular classification is too strong.
- Counterexample: `u''-2u'/z+2u/z²=0` has regular singularities at zero and infinity,
  with finite exponents `1,2`. Substituting `u=zv`, a permitted power displacement,
  gives `v''=0`. Zero becomes ordinary. It is the class “ordinary or regular singular”
  that is preserved; strict singularity preservation needs a nonremovability condition.
- The synopsis keeps the coefficient and exponent identities and states this qualification.

## K-E7: the normalized Heun accessory parameter does not cover a zero product

- Location: printed pp. 56–57, equation (4.10), and Chapter 8, equation (8.1).
- Issue: the claimed general numerator `ab(z-h)` restricts the constant accessory
  coefficient to zero whenever `ab=0`.
- General form: use `abz-q` with `q` independent. The substitution `h=q/(ab)` is
  available only when `ab≠0`. For example `a=0`, `b=1`, and `q=1` cannot be
  written in the book's parameterization for any finite `h`.
- This is a limitation of the parameterization, not a failure of the formulas for
  equations actually represented by it. SYNOPSIS-Kristensson preserves the book's
  `h` normalization in Chapter 8 and distinguishes it from the general form in K-4.10.

## K-E8: initial coefficient after product normalization

- Location: printed p. 189, PDF p. 198, Lemma B.4; repeated on p. 190 in its proof.
- Issue: after defining `a'_n=a_n∏_{k=1}^n(1+c₁/k+c₂/k²)`, the initial
  coefficient is printed as `A'₀=A₀`.
- Correction: `A'₀=A₀(1+c₁+c₂)`. Indeed `a'₁=a₁(1+c₁+c₂)` and
  `a'₀=a₀`, so the new initial equation must have that coefficient.
  The displayed general formula `A'_n=A_n(1+c₁/(n+1)+c₂/(n+1)²)` also gives
  the corrected value when extended to `n=0`.
- Checked against the rendered page. The large-index asymptotic coefficient calculation
  is unaffected, but a literal recurrence theorem must correct its initialization.

## K-E9: boundedness of Binet's remainder near the sector vertex

- Location: printed p. 166, PDF p. 175, paragraph following (A.6).
- Issue: `J(z)` is called bounded on the whole open sector
  `{z: |arg z|<π-δ}`. The vertex is excluded but can be approached.
- Counterexample: on positive reals `z→0`, `Γ(z)∼1/z`, and its defining equation gives
  `J(z)=-(1/2)log z-(1/2)log(2π)+o(1)→+∞`.
- Correction: retain analyticity on the sector and boundedness outside any disc about
  zero, together with the explicitly stated large-argument estimate `J(z)=O(1/z)`.
  The synopsis uses this large-argument formulation. Checked against the rendered page.

## Branch issue requiring an explicit domain convention

Theorem 6.2 and the second-kind discussion use `z∉[-1,1]` as though it were a
single-valued analytic domain for general complex degree. The infinity normalization
`Q_ν(z)∼C_ν z^{-ν-1}` has nontrivial monodromy for nonintegral `ν`; it cannot be a
globally single-valued analytic function on that entire exterior domain. Use a slit
such as `ℂ\(-∞,1]`, a chosen continuation path, or a covering-space formulation.
The contour identity can then retain its intended correlated powers. This qualification
concerns global branch interpretation; it does not claim the real `z>1` formula is wrong.

## Synopsis-only coefficient and parameter-limit qualifications

These corrections concern inferences in the synopsis, not newly established
printing errors in the book.

- K-3.02: printed Theorem 3.1 specifies the coefficient r_(n-2); it need not be
  the leading coefficient after further degree cancellation. The synopsis now
  states the coefficient at that fixed degree.
- K-6.02: the exterior leading equivalent requires a nonzero leading coefficient
  and a regular degree. At nu=-3/2 the reciprocal Gamma factor vanishes, so use
  the first nonzero term of the full expansion, pi*z^(-3/2)/(4*sqrt(2)).
- K-6.04: the removable integer-degree contour limit applies to nonnegative
  integers. Negative degrees require meromorphic continuation; at nu=-1 the
  Hobson Q has a simple degree pole with residue one.
