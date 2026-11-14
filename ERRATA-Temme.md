# Temme: errata encountered while preparing the synopsis

Edition checked: Nico M. Temme, *Special Functions*, Wiley, 1996,
ISBN 0-471-11313-1, in
[the local PDF](References/Temme1996SpecialFunctionsIntroductionClassicalFunctionsMathematicalPhysics-Wiley.pdf).
These are independently identified issues, not an author-approved errata list.
The cited displayed pages have been checked as page images where indicated;
the problems below are visible in print and are not corrections of OCR alone.
No Lean definition or tagged theorem is changed by this document.

## Confirmed mathematical issues

### TEM-E01 — Periodic Bernoulli regularity, p. 6, after (1.16), PDF p. 17

The period-one extension is said to have continuous derivatives through order
`n−1`. In general it has only `n−2` continuous derivatives for `n≥2`.
Already `B̄_1(x)={x}−1/2` is discontinuous at integers. The extension of
`B_2(x)=x²−x+1/6` is continuous, but its left and right first derivatives
at zero are `1` and `−1`. Thus the problem is not an endpoint convention.
Correct target: `B̄_n∈C^{n−2}(ℝ)` for `n≥2`, with the ordinary polynomial
derivative identities off the integers. The page image confirms the printed
`n−1`. Synopsis entry TEM-01-05 uses the corrected order.

### TEM-E02 — Euler extension: period one versus antiperiod one, p. 16, PDF p. 27

The extension of `E_n` from `[0,1)` is assigned period one, while its
figures, Fourier series and stated `C^{n−1}` regularity describe the
antiperiodic extension. For `E_1(x)=x−1/2`, the printed period-one rule
gives a jump of size `−1` at every integer, whereas Figure 1.3 is the
continuous triangular wave. The consistent convention is
`Ê_n(x+j)=(-1)^j E_n(x)` for integer `j` and `0≤x<1`.
It has period two and, for `n≥1`, is `C^{n−1}`.
The page image confirms that the minus sign is absent in the extension rule.
The antiperiodic convention is also needed in the remainder in (1.25).

### TEM-E03 — Sign of the odd Euler Fourier series, p. 16, PDF p. 27

The cosine expansion for `E_{2n−1}(x)` has prefactor
`4(-1)^{n+1}(2n−1)!`. It should have `4(-1)^n(2n−1)!`.
At `n=1,x=0`, the printed right side is
`4∑_{m≥0}1/((2m+1)π)²=1/2`, whereas `E_1(0)=−1/2`.
The series is absolutely convergent here, so no endpoint summation convention
changes the counterexample. The page image confirms the exponent `n+1`.
The sine expansion for `E_{2n}` has the correct sign.

### TEM-E04 — Absolute value in the Euler bound, p. 16, PDF p. 27

The displayed bound ends with `2^{−2n}𝔈_{2n}`, without an absolute value
on the Euler number. The numbers are signed: the preceding page gives
`𝔈_2=−1`, `𝔈_4=5`, `𝔈_6=−61`.
At `n=1,x=1/2`, the printed inequality would say `1/4≤−1/4`.
The correct bound on `[0,1]` is
`|E_{2n}(x)|≤|E_{2n}(1/2)|=2^{−2n}|𝔈_{2n}|`.
The missing absolute value is confirmed in the page image.

### TEM-E05 — Boole remainder sign, Theorem 1.4, p. 17, PDF p. 28

The printed remainder is
`∫₀¹ f^{(k)}(t)E_{k−1}(t)dt/(2(k−1)!)`.
It needs the factor `(-1)^{k+1}`. For `f(t)=t³`, `k=2`, the finite
boundary sum equals `5/4`, and the printed remainder equals `1/4`;
the asserted equality would therefore give `f(1)=3/2`.
With the missing sign restored it gives `5/4−1/4=1`.
Integration by parts also forces the sign to alternate with `k`.
Synopsis TEM-01-13 gives the corrected theorem; the formula was checked
against the page image.

### TEM-E06 — Insufficient convergence hypothesis, Theorem 1.5, pp. 17–18

The displayed hypotheses require `f` and its first `k` derivatives to tend
to zero. That does not ensure convergence of the alternating sampled series
or of the remainder integral. Take `m=0,h=0` and
`f(t)=cos(πt)/√(t+1)`, `t≥0`. It is smooth, and every derivative tends
to zero. Nevertheless
`∑_{j≥0}(-1)^j f(j)=∑_{j≥0}1/√(j+1)` diverges.
Thus this is a false statement under its printed hypotheses, rather than
just an omitted step of its proof. A sufficient correction is `k≥1` and
`∫₀∞|f^{(k)}(t)|dt<∞`, in addition to the printed decay assumptions.
The finite-interval Boole identity then passes to the limit, using the
antiperiodic Euler extension from TEM-E02. The corrected target is
TEM-01-14. Both theorem pages were inspected as images.

### TEM-E07 — Poisson summation: sample values and negative spacing,
Theorem 12.2, pp. 326–327, PDF pp. 330–331

There are two independent problems with the printed formula under only
bounded variation and absolute integrability of `f`.

- **Values at jumps.** Take `f(0)=1` and `f(t)=0` for `t≠0`.
  It has bounded variation, is absolutely integrable, and has identically
  zero Fourier transform. At `a=x=0,b=1` the sample sum is one and
  the Fourier sum is zero. The sample values must instead be normalized
  as `(f(t−)+f(t+))/2`, or an assumption of that normalization must be added.
- **Sign of the spacing.** The book permits any nonzero real `b` but has
  prefactor `1/b` rather than `1/|b|`. For `f(t)=exp(−πt²)`,
  `a=x=0,b=−1`, both series without the prefactor have positive terms
  and are finite. The displayed right side is negative and the left side
  positive. Replace the prefactor by `1/|b|`, or restrict `b>0`.

The Fourier sum should be specified as the limit of symmetric partial sums
unless absolute convergence is separately assumed. These repairs are
incorporated explicitly in synopsis TEM-12-08. The formula and parameter
range were confirmed on the page images.

### TEM-E08 — Sign in the von Mises substitution, p. 309, PDF p. 314

The substitution preceding (11.88) states `cos t=1+2sin²(t/2)=1+2x²`.
Both plus signs must be minus signs. At `t=π`, the printed identity would
give `−1=3`. The immediately following integral correctly has
`exp(−2κx²)`, so this is a local trigonometric sign error, not a different
definition of the distribution. The page image confirms both plus signs.
Synopsis TEM-11-20 uses the correct substitution.

### TEM-E09 — Invalid nome range in the numerical discussion, p. 328, PDF p. 332

The discussion says to use the theta transformations (12.31) when `|q|>1`.
The defining theta series do not converge in that range: already their
`q^{n²}` terms fail to tend to zero. Moreover `q=e^{iπτ}` has `|q|>1`
exactly when `Im τ<0`, and `Im(−1/τ)=Im τ/|τ|²` has the same negative
sign. Thus the transformation cannot move such a parameter into the
convergent upper half-plane. The valid computational use is, for example,
real `0<q<1` close to one, where `τ=it` with small `t>0` is transformed
to `i/t` and a rapidly convergent nome. The page image confirms that the
printed bound is `1`, not a lost OCR fraction. This correct use is stated
in TEM-12-14; no continuation across the unit circle is asserted.

### TEM-E10 — Missing exponential in the large-lower-parameter Tricomi estimate,
p. 342, §13.3 Example 8, PDF p. 345

The displayed estimate for `g_n=U(a,c+n,z)` omits `e^z`. For fixed
positive `a,z`, it should read
`U(a,c+n,z)~e^z z^{1−c−n}Γ(c+n−1)/Γ(a)`.
An exact special case detects the missing factor: at `a=z=1`, write
`N=c+n` and take positive integral `N≥2`. Then
`U(1,N,1)=e Γ(N−1,1)` by the incomplete-gamma connection. The ratio
`Γ(N−1,1)/Γ(N−1)` tends to one, because the complementary lower
integral is at most `1/(N−1)` while `Γ(N−1)=(N−2)!` grows.
Thus the ratio of the actual function to the printed leading term tends
to `e`, not one. The page image confirms the omission. Consecutive-ratio
and minimality conclusions on that page are unaffected by this constant
factor. Synopsis TEM-13-07 restores it.

### TEM-E11 — Second beta saddle moment, p. 297, PDF p. 302

The text gives `Φ_0=1`, `Φ_1=0`, `Φ_2=2q`, immediately followed by
`Φ_{n+1}=−n(Φ_n+qΦ_{n−1})`. Substituting `n=1` in that recurrence
gives `Φ_2=−q`, not `2q`. The independent finite coefficient formula
from the contour definition also gives
`Φ_2=q²−2q²+q(q−1)=−q`.
Thus it is the stated initial value, not the recurrence, that needs repair.
The printed page image confirms `2q`. Synopsis TEM-11-15 uses the correct
recursion and finite polynomial definition.

## Interpretation requiring care, not classified as a confirmed misprint

**Theorem 2.2, p. 30, PDF p. 40: absolute convergence of repeated integrals.**
Read the absolute-convergence condition as absolute integrability of the
two-variable function, not just of each already integrated outer function.
The distinction matters even for smooth functions. On `(0,∞)²`, put

\[
 f(x,y)=\frac{(x+1)^2-(y+1)^2}{((x+1)^2+(y+1)^2)^2}.
\]

Each inner integral is absolutely convergent. Integrating first in `y`
gives `−1/((x+1)²+1)`, whose integral is `−π/4`; reversing the order
gives `1/((y+1)²+1)`, whose integral is `π/4`. Both outer integrals
are absolutely convergent, but the integral of `|f|` over the product is
infinite. The synopsis therefore spells out product absolute integrability.
The phrase in the book can carry that stronger, usual interpretation, so
this is recorded as an interpretation warning rather than a definite error.

## Audit boundary

This is a list of issues encountered in preparing the mathematical synopsis,
not a certificate that every other formula or exercise is error-free.
OCR frequently drops fraction bars, subscripts and signs in this PDF;
an OCR discrepancy by itself has not been classified as a printed erratum.
