# AAR: errata and formalization clarifications

Source: Andrews, Askey and Roy, *Special Functions* (1999), the PDF in References.
Printed page \(p\) corresponds to PDF page \(p+16\). These observations concern the
copy actually inspected, not an unverified list of corrections for every printing.
Extraction artifacts are not counted as mathematical errata.

## Confirmed mathematical misprint: Theorem 1.10.7, equation (1.10.9), p. 39

The displayed formula is \(J(\varepsilon,\chi)=0\) for nontrivial \(\chi\).
The correction is
\[
 J(\varepsilon,\chi)=-1.
\]
The definition on p. 38 extends **every** multiplicative character by value \(0\)
at \(0\), including \(\varepsilon\). Thus
\[
 J(\varepsilon,\chi)=\sum_{x\ne0}\chi(1-x)
 =\sum_{y\ne1}\chi(y)=-\chi(1)=-1.
\]
For a concrete check take the nontrivial quadratic character of \(\mathbb F_3\):
the only nonzero contribution is \(x=2\), of value \(-1\).
The printed zero was visually verified on PDF page 55; it is not an OCR substitution.
The synopsis uses the corrected formula and marks the correction.

## Missing regularity in the standalone Corollary 1.10.2, p. 37

The preceding Theorem 1.10.1 assumes differentiability, whereas the printed
corollary only says that \(g:(0,\infty)\to\mathbb C^\times\) is a group
homomorphism and concludes \(g(x)=x^c\). A regularity hypothesis must be carried
into that corollary, for example continuity or differentiability.
Indeed, choose a discontinuous additive \(A:\mathbb R\to\mathbb R\)
using a Hamel basis and put \(g(x)=\exp(A(\log x))\). Then \(g(xy)=g(x)g(y)\),
but \(g\) is not \(x^c\): positivity would force \(c\) real, and injectivity of
the real exponential would force \(A(t)=ct\), contrary to the choice of \(A\).
The synopsis explicitly assumes continuity.

## Measure convention in Theorem 1.8.6, p. 34

The displayed integration element is \(dx_1\cdots dx_{n-1}\), with
\(x_n=1-\sum_{j<n}x_j\). Its formula is correct for this coordinate measure.
The following prose calls it a “surface integral”; if that is interpreted as
Euclidean hypersurface measure, the answer must be multiplied by \(\sqrt n\).
This is a convention clarification, not an error in the displayed formula.

## Confirmed mathematical misprint: Theorem 2.6.3, equation (2.6.14), p. 105

Let \(r=(\sqrt5-1)/2\). The displayed argument is
\(-(1+\sqrt5)/2=-1/r\), but its displayed value is
\(-\pi^2/10+\frac12\log^2((\sqrt5+1)/2)\). The correct value is
\[
 \mathrm{Li}_2(-1/r)=-\frac{\pi^2}{10}-\log^2r.
\]
This follows from the book's own Landen formula, Theorem 2.6.1, applied at
\(x=r\): since \(1-r=r^2\) and \(r/(r-1)=-1/r\), it gives
\(\mathrm{Li}_2(r)+\mathrm{Li}_2(-1/r)=-2\log^2r\).
Substitute the value \(\mathrm{Li}_2(r)=\pi^2/10-\log^2r\)
from (2.6.12). The incorrect plus sign and coefficient \(1/2\) were visually
verified on PDF page 121. This is independent of numerical approximation.

## Confirmed coefficient misprint: Theorem 6.2.1, equation (6.2.40), p. 292

The denominator \(\Gamma(k+\alpha+1)\) in the second, infinite sum must be
\(\Gamma(k+\lambda+1)\). This follows directly from the coefficient identity
printed in the proof immediately below (6.2.40), which has
\(\Gamma(k+\lambda+1)\); multiplying by the Laguerre-\(\beta\) reconstruction
factor cancels the \(n\)-dependent factors but does not change this denominator.

An exact finite counterexample avoids any convergence question. Take
\(N=0,\alpha=0,c=1,\beta=1,\lambda=2\), and
\(f(x)=L_1^2(x)=3-x\). Then \(a_0=1,b_1=6,b_k=0\) for \(k>1\).
The printed expression gives \(1+6L_1^1(x)=13-6x\), whereas the corrected
expression gives \(1+L_1^1(x)=3-x\). The printed inequalities
\(\alpha,\lambda>-1\), \(c>(\lambda-2\alpha-1)/2\) all hold.
Multiplying \(f\) by any positive scalar makes the data arbitrarily small,
so the informal “small enough” clause cannot cure the mismatch.
The discrepancy between the displayed theorem and its proof was visually
verified on PDF page 308.

## Incorrect unqualified bound: equation (7.7.4), p. 394

The proof writes \(\pi(n)<1.06n/\log n\), where \(\pi(n)\) counts primes
less than \(n\), without a lower threshold on \(n\), and attributes it to
Chebyshev. This cannot hold for every positive integer \(n>1\):
\(\pi(100)=25\), whereas \(106/\log100<25\).
For an exact comparison, \(\log3>
2(1/2+(1/2)^3/3)=13/12\), hence
\(\log100>\log81>13/3>106/25\).

The prime number theorem implies the displayed \(1.06\) bound for all
sufficiently large \(n\); that version, or an independent sufficiently-large
bound \(\mathrm{lcm}(1,\ldots,n)<3^n\), suffices for the irrationality argument.
No explicit threshold is asserted here. The coefficient 1.06 and absence
of a threshold were visually verified on PDF page 410. The irrationality
theorem itself is unaffected.

## Missing leading sine term: Theorem 7.3.6, p. 380

The displayed \(q(\theta)\) starts its sum at \(k=1\), but the stated
\(n-1\) interior zeros and the following bounds require
\[
 q(\theta)=\sum_{k=0}^{n-1}\lambda_k\sin((n-k)\theta).
\]
With the printed lower limit, the highest frequency is \(n-1\), not \(n\).
For example, take \(n=2,\lambda_0=3,\lambda_1=2,\lambda_2=1\), which
satisfies the hypotheses. The printed expression is \(2\sin\theta\), with
no zero in \((0,\pi)\), contradicting the asserted \(t_1\).
The corrected expression \(3\sin2\theta+2\sin\theta\) has one interior zero.
The lower index \(k=1\) was visually checked on PDF page 396; the synopsis
uses \(k=0\) and explicitly marks the correction.

## Missing factor: Theorem 8.3.3, p. 410

The left side contains \(x_1\cdots x_k\), but the displayed right side
omits \(\prod_{j=1}^k(\alpha+(n-j)\gamma)\).
For \(n=k=1,\alpha=2,\beta=1,\gamma=0\), the integral is
\(\int_0^1x^2dx=1/3\), whereas the printed right side is
\(\Gamma(1)\Gamma(2)/\Gamma(4)=1/6\).
The missing factor is then \(\alpha=2\).
The corrected formula follows by scaling the Laguerre–Selberg integral
and its elementary-symmetric moment formula. The absence of the factor
was visually verified on PDF page 426.

## Product normalization in Lemma 8.6.3, p. 421

The printed condition is \(s^n>p\) but the displayed product constraint is
\(\prod_i x_i=p^n\). These use inconsistent meanings of \(p\).
For instance \(n=2,s=2,p=3\) satisfies \(s^n>p\), but positive numbers
with sum \(4\) and product \(9\) do not exist.
Use either product \(p\) with condition \(s^n>p\), or product \(p^n\)
with condition \(s>p\). The synopsis uses \(P=\prod_i x_i\).
Both displayed occurrences were visually checked on PDF page 437.

## Missing distinct-root condition in standalone Theorem 8.6.5, p. 423

The printed statement permits an arbitrary monic integer polynomial with
all roots positive. For every \(n\), \((x-1)^n\) has trace \(n\), contradicting
the conclusion for any \(1<\lambda<\lambda_0\), where the specified
Siegel constant \(\lambda_0\) is greater than \(1\).
Its proof uses a nonzero discriminant, so squarefreeness must be retained
from the preceding setting; irreducibility also suffices.
The synopsis explicitly assumes a squarefree polynomial. For the intended
application to minimal polynomials of algebraic integers, this condition
holds automatically in characteristic zero. The printed hypotheses were
visually checked on PDF page 439.

## Haar measure convention: equation (9.11.3), p. 468

The displayed \(da\wedge d\bar a\wedge db\wedge d\bar b\) is an ambient
four-dimensional volume form on \(\mathbb C^2\), whereas
\(SU(2)\cong S^3\) is three-dimensional. Its pullback to \(SU(2)\) is zero;
taken literally it is not a nonzero Haar measure on that group.
To obtain Haar measure one must first disintegrate the ambient volume
radially, contract with the radial normal, or directly use induced
three-dimensional surface measure and normalize it.
The Euler-angle probability measure later given on p. 471,
\(\sin\theta\,d\theta\,d\phi\,d\psi/(16\pi^2)\), is correct.
The ambient-form display was visually checked on PDF page 484.

## Complex-parameter weight convention: Theorem 10.11.1, p. 527

The theorem allows \(|q|,|\beta|<1\), but the displayed weight is an
absolute-value square. That formula agrees with the paired product
\[
 \frac{(e^{2i\theta},e^{-2i\theta};q)_\infty}
 {(\beta e^{2i\theta},\beta e^{-2i\theta};q)_\infty}
\]
when \(q,\beta\) are real. For complex parameters it must be the paired
product if the claimed analytic continuation is intended; an absolute-value
square introduces conjugate parameters. The proof explicitly begins with
real parameters. The synopsis states the real positive-measure theorem
and the paired-product analytic continuation separately.
This is a necessary convention clarification for Lean, not a claim that
the real orthogonality theorem is false.

## Missing minus sign: Lemma 10.2.3, p. 491

The displayed denominator is \(1-e^{(k+1)t}\), but the claimed
\(f'(t)\le0\) requires \(1-e^{-(k+1)t}\).
The literal expression is false even for \(\lambda=0,\mu=1,k=2\),
which satisfies every printed parameter restriction. Writing \(q=e^{-t}\),
it becomes \(-q^4/(1+q+q^2)\), whose derivative at \(t=\log2\) is
\(6/49>0\).
The negative-exponent denominator gives the intended positive decreasing
function \(q/(1+q+q^2)\).
The positive exponent was visually verified on PDF page 507 and independently
checked by the integrating agent. The synopsis uses the corrected exponent.

## Missing endpoint compatibility: Corollary B.1.6, p. 602

The standalone corollary says every continuous function on \([0,2\pi]\)
can be uniformly approximated by trigonometric polynomials.
It must retain periodic endpoint compatibility \(f(0)=f(2\pi)\).
For \(f(x)=x\), every trigonometric polynomial \(T\) has \(T(0)=T(2\pi)\),
so its uniform error is at least \(\pi\). The preceding Fourier theorems
already assume periodicity, and under that hypothesis the conclusion is correct.
The absence of an endpoint condition was visually verified on PDF page 618.

## Wrong sign in the irregular first-order example, p. 639

For \(b(x)=(x-x_0)^2,\ c(x)=c_0\), the equation
\(b(x)y'+c(x)y=0\) has solution
\(y=A\exp(c_0/(x-x_0))\), not the displayed negative exponent.
Differentiating the printed expression gives residual \(2c_0y\),
nonzero when \(A,c_0\ne0\).
The sign was visually verified on PDF page 655.

## Wrong resonance exclusion in the Frobenius discussion, p. 640

After choosing an indicial root \(\mu\), the prose asserts that an analytic
factor exists provided \(2\mu+b_1/a_2\) is not a nonnegative integer.
The excluded set must instead be the **nonpositive** integers:
the recurrence denominator is \(n(n-1+2\mu+b_1/a_2)\), \(n\ge1\).
Equivalently require \(I(\mu+n)\ne0\) for all \(n\ge1\).

For a counterexample to the printed sufficient condition take
\(x^2y''-xy'+x^2y=0\), choose the indicial root \(\mu=0\), and require
analytic factor \(f(0)=1\). Here \(2\mu+b_1/a_2=-1\), which passes the
printed exclusion. But the coefficient of \(x^2\) in the differential
equation is \(f(0)\), forcing \(f(0)=0\), a contradiction.
The later paragraph correctly guarantees the larger-root solution;
the error is in this earlier sign restriction. Visually verified on PDF page 656.


## Missing boundary qualification: equation (7.3.29), §7.3

Under the permitted weak inequalities
\((2k-1)\lambda_{k-1}\ge2k\lambda_k>0\), the displayed strict upper
bound \(s_k<k\pi/(n+1/2)\) fails already at
\(n=1,\lambda_0=2,\lambda_1=1\): the zero of
\(2\cos\theta+1\) is exactly \(2\pi/3\).
The sharpened boundary formulation needs verification before replacing it by a
non-strict bound or imposing extra strictness hypotheses. The synopsis withholds
this sharpened claim while retaining the preceding valid zero theorems.

## Wrong denominator: Theorem 8.9.1(a), p. 429

Replace the last denominator factor \((\alpha)_{2k}\) by
\((\alpha+1)_{2k}\). At \(\alpha=\beta=1,k=1\), the finite sum is
\(1/3\), whereas the printed right side is \(1\); the corrected factor gives
\(1/3\). The proved Lean theorem `DLMF.Selberg.nearly_poised_3F2` already
has the corrected denominator. The synopsis now uses that formula.

## Synopsis transcription correction: Elliott's Theorem 3.2.8

The book's parameter shifts on p. 138 are correct. The synopsis's three products
were corrected to match them and recover \(EK'+KE'-KK'=\pi/2\) at
\(a=b=c=0\). This is not an additional erratum in the book.
