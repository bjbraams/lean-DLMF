# Book corrections and remaining mathematical questions

The owner approved the correction round following acquisition. The four affected
SYNOPSIS files and their ERRATA records now incorporate the agreed corrections.
The raw lifted Tricomi and Whittaker expressions have explicit ConnectionOnLog
names, with deprecated compatibility aliases and updated project callers.

Each disposition below records the current status. The evidence paragraphs are
retained from the acquisition audit: references there to an unchanged synopsis
or an awaiting-review state describe that earlier snapshot, not the current files.
No replacement strict zero bound or unproved 9-j phase identity is asserted.

The Jucys–Bandzaitis repairs in RL-7.08 and their dependent claims in RL-7.12
already have conjectural status in the synopsis; they are not acquired as source theorems.

## Olver O-9.10: repeated oscillatory Airy tails

**Disposition:** Agreed synopsis correction applied; ERRATA distinguishes printed defects from
synopsis-only transcription or interpretation corrections.


- Status: confirmed synopsis transcription error; rendered printed page 343 (PDF page 362) checked.
- The displayed bound is `A_n(v) = O(v^(-3n/2+3/4))`, where
  `A_1(v) = ∫_v^∞ Ai(-t) dt` and each subsequent `A_n` is an additional tail integral.
- The Airy phase has derivative `√v`, so successive integrations gain a factor
  `v^(-1/2)`. The expected leading order is `v^(-n/2-1/4)`.
  For `n=2` this gives a nonzero oscillatory amplitude of order `v^(-5/4)`,
  incompatible with the synopsis bound `O(v^(-9/4))`.
- The source equation (8.02) explicitly gives `A_s(v) = O(v^(-s/2-1/4))`.
  Its derivative assumption is `f^(s)(v) = O(v^((2s-3-δ_s)/4))` for `s ≥ 1`;
  the synopsis instead imposes the stronger `O(v^(-1/4-δ_s))` and loses part of the
  source domain. Both are proposed revisions.
- The correct source bound is acquired with its page and equation provenance;
  the false synopsis bound is not added as an admission. The synopsis itself is unchanged.

## AAR Theorem 3.2.8: Elliott's identity

**Disposition:** Agreed synopsis correction applied; ERRATA distinguishes printed defects from
synopsis-only transcription or interpretation corrections.


- Status: confirmed synopsis transcription error; the book is correct.
- Source: printed page 138, local Chapter 3 PDF page 15. The three products
  shift the upper parameters in different factors from those in the synopsis.
- With the source's abbreviations `A,C,U,V`, the correct left side is
  `F(A,C−1;U;x)F(1−A,c+1/2;V;1−x)`
  `+ F(A,C;U;x)F(−A,c+1/2;V;1−x)`
  `− F(A,C;U;x)F(1−A,c+1/2;V;1−x)`.
- At `a=b=c=0`, the correct formula reduces to Legendre's relation
  `EK′+KE′−KK′`; the synopsis instead yields `KK′+EE′−EK′`.
- The correct book statement is acquired with its provenance. The synopsis itself
  remains unchanged pending review.

## Rao–Lakshminarayanan RL-8.18: finite specialization at a lower pole

**Disposition:** Agreed synopsis correction applied; ERRATA distinguishes printed defects from
synopsis-only transcription or interpretation corrections.


- Status: counterexample to an unrestricted finite-sum reading of the synopsis.
- Set `a=-2`, with ordinary generic positive `b,c`. Both displayed left upper
  and right upper lists contain `1+a/2=0`, so their literal terminating series
  are both `1`. The right lower parameter `a/2=-1` first vanishes after that
  termination and is permitted by the synopsis's finite-denominator convention.
- The displayed identity then becomes `1+t = 1/(1-t)`, which is false for
  nonzero small `t`. Joint parameter continuation of the right side can retain
  terms that the finite truncation loses.
- The ordinary identity with globally regular lower parameters remains a valid
  acquisition target. The finite-specialization instruction needs qualification;
  it is not acquired for the counterexample. The synopsis itself is unchanged.

## Rao–Lakshminarayanan RL-8.08–RL-8.22: exceptional finite-sum convention

**Disposition:** Agreed synopsis correction applied; ERRATA distinguishes printed defects from
synopsis-only transcription or interpretation corrections.


- Status: further exact counterexamples to applying the finite instructions
  whenever lower factors are nonzero only through termination.
- RL-8.19 at `a=-1` reduces to `1-t/2 = 1-2t`: both upper lists contain zero,
  while the exceptional lower parameters vanish just after the sole retained term.
- RL-8.12 at `a=c=-1` reduces to `1+2t = (1-t)^(-2)`.
- RL-8.15 at `a=-1,b=-1/2,c=-1` reduces to
  `1-2t+2t² = (1-t)²`; `c=a+b+1/2` as required.
- Globally regular ordinary lower parameters, or specified joint parameter limits,
  are essential. Termination before the first zero lower factor alone does not
  transfer the generic identity to every singular coincident parameter.
- Valid ordinary germ identities are acquired on their regular domain. False
  exceptional readings are not asserted. The synopses remain unchanged.


## AAR §7.3: strict upper bound in (7.3.29)

**Disposition:** The false strict refinement is withheld in the synopsis and documented in
ERRATA-AAR; its precise boundary replacement remains open.


The source and synopsis allow `(2k−1)λ_{k−1} ≥ 2kλ_k > 0` while claiming
a strict zero bound `s_k < kπ/(n+1/2)`. At degree one, `λ₀=2, λ₁=1`
give `p(θ)=2cos θ+1`, whose zero `2π/3` equals the proposed upper bound.
The boundary case therefore needs a correction or an additional strictness
hypothesis. The synopsis is unchanged; the defective strict target is not admitted.

## AAR Theorem 8.9.1(a): nearly-poised finite summation

**Disposition:** Agreed synopsis correction applied; ERRATA distinguishes printed defects from
synopsis-only transcription or interpretation corrections.


The printed denominator `(α)_{2k}` is incorrect. At `α=β=1, k=1`,
the finite left side is `1/3` and the printed right side is `1`. The
correct denominator `(α+1)_{2k}` gives `1/3` and is already present in
the proved `DLMF.Selberg.nearly_poised_3F2`. The source location is
printed p. 429 (Chapter 8 PDF p. 29). The synopsis remains unchanged.

## Kristensson K-3.02: coefficient versus leading coefficient

**Disposition:** Agreed synopsis correction applied; ERRATA distinguishes printed defects from
synopsis-only transcription or interpretation corrections.


For the partial-fraction numerator, after the sum of residues vanishes the
coefficient of `z^(n−2)` is `Σ aᵢ fᵢ`. It need not be the leading coefficient
when the degree drops further. At `n=3`, `a=(0,1,2)`, `f=(1,−2,1)`, both
`Σ fᵢ` and `Σ aᵢ fᵢ` vanish, but the numerator is the constant polynomial `2`.
The new acquisition states the correct coefficient identity; the synopsis
is unchanged pending review.

## Existing lifted Tricomi and Whittaker functions at integer parameters

**Disposition:** Raw formulas renamed to explicit ConnectionOnLog helpers; all project callers
updated and old names retained as deprecated aliases. Continued functions keep whole-parameter
limits. The principal-strip bridges are now proved and axiom-audited; global limit and analyticity
targets remain proof obligations.


The existing `kummerUOnLog` uses the noninteger connection formula with
totalized Gamma factors. At lower parameter `b=1` that expression vanishes
identically, so it cannot represent Tricomi U on the whole parameter domain.
The corresponding existing `whittakerWOnLog` inherits that issue. Their
definition bodies are unchanged. The acquisition adds parameter-continuation
functions and domain-specific bridges; whether to adopt those bodies under
the older names is left for the owner's review.

## Rao: exceptional finite parameters in the Kummer generator list

**Disposition:** Agreed synopsis correction applied; ERRATA distinguishes printed defects from
synopsis-only transcription or interpretation corrections.


The global finite-denominator convention also needs a qualification for RL-3.03,
not only for the Chapter 8 generators. With `a=c=-1` and `b=1/2`, the finite
left seed is `1+z/2`, while its Euler-transformed finite seed is
`(1-z)^(-1/2)` because `c-a=0`. They are analytic near zero but differ in
coefficient `z²`. Global lower-parameter regularity, or coherent limits of the
whole normalized combination, gives the valid generic Kummer representations.
No exceptional finite version of this equality has been asserted. The synopsis
has been left unchanged for owner review.

## Kristensson: negative integral degrees in the Q-contour quotient

**Disposition:** Agreed synopsis correction applied; ERRATA distinguishes printed defects from
synopsis-only transcription or interpretation corrections.


K6.04 describes integer-degree values of its Q-contour quotient as removable
parameter limits. This needs the restriction to nonnegative integers. At degree
`ν=-1` and order `μ=0`, the normalized Olver function is identically `1`:
one upper Gauss parameter is zero and the factor `sqrt(π)` cancels `Γ(1/2)`.
Consequently `associatedQ ν 0 z = Γ(ν+1) olverQ ν 0 z` has a simple pole
at `ν=-1`, of residue `1`, rather than a removable parameter singularity.
The existing `LegendreQRegular` predicate already excludes negative integral degrees.
New removable contour-limit targets are restricted to nonnegative degrees;
negative degrees retain a meromorphic interpretation. The synopsis is unchanged.

## Kristensson: a zero leading coefficient is not an asymptotic equivalent

**Disposition:** Agreed synopsis correction applied; ERRATA distinguishes printed defects from
synopsis-only transcription or interpretation corrections.


K6.02 requires a qualification when `1/Γ(ν+3/2)=0`. At `ν=-3/2`,
the stated leading coefficient is zero; the actual function satisfies
`Q_{-3/2}=Q_{1/2}` and has the nonzero leading term
`π z^(-3/2)/(4 sqrt(2))`. It comes from the first nonzero regularized
Gauss-series coefficient, rather than index zero. The acquired all-order
asymptotic expansion permits initial zero coefficients. Its leading-equivalent
corollary requires `ν+3/2` outside the nonpositive integers, along with the
canonical regular-degree condition. Existing tagged assertions and the synopsis
were left unchanged.

## Rao: cancellation before the specified terminating degree

**Disposition:** Agreed synopsis correction applied; ERRATA distinguishes printed defects from
synopsis-only transcription or interpretation corrections.


RL-1.18 needs `b` regular, or at least `(b)_k≠0` through `k=n`, in
`F(-n,b;b;z)=(1-z)^n`. Under the synopsis's first-terminating-index
convention, `n=1,b=0` instead retains the constant finite series `1`,
whereas the right side is `1-z`. Cancelling a common exceptional parameter
first selects a different convention. The valid finite-denominator statement
is mapped; no false exceptional cancellation target was added.

## Olver O-1.14: the inverse-series sign convention

**Disposition:** Agreed synopsis correction applied; ERRATA distinguishes printed defects from
synopsis-only transcription or interpretation corrections.


This is a synopsis transcription issue. Olver's printed p. 21 uses a forward
series with positive correction coefficients and writes the inverse with negative
corrections. The synopsis reverses both signs while retaining the same displayed
coefficient formulas. With a₀=a₁=1 and all later a's zero, its forward relation is
`u=z-1-1/z`. Direct inversion gives `z=u+1+1/u-1/u²+O(u⁻³)`, so the coefficient
of `u⁻²` is −1, whereas the retained formula gives +1. The acquisition follows
the source's original convention; the synopsis is unchanged pending review.

## Olver O-8.13: the number of retained Darboux terms

**Disposition:** Agreed synopsis correction applied; ERRATA distinguishes printed defects from
synopsis-only transcription or interpretation corrections.


The synopsis calls g_m the sum of the first m local terms but assigns the
error O(n^(-m-3/2)). Olver's printed p. 312 defines g_m by the inclusive sum
s=0,...,m: there are m+1 retained terms. With m terms the corresponding error
is O(n^(-m-1/2)). In particular, the leading term alone has O(n^(-3/2))
error. The new explicit finite target follows the book's inclusive convention.
The original synopsis remains unchanged for review.

## Olver O-11.11: arbitrary short loops do not give uniform variation

**Disposition:** Synopsis now requires controlled inner traversal for the variation corollary. The
interpretation of the book’s admissible-path convention remains open.


The source's printed p. 419 corollary needs its admissible-path convention to
be resolved. A bound on the weighted length integral
`∫ |dz|/(1+|z|^(1+rho))` alone does not uniformly bound variation of
`sqrt(z)*B_0(z)` near zero. If psi=1 locally, B_0=1. Taking N small loops of
radius 1/N keeps their total length bounded while the variation of this
square-root factor grows proportionally to sqrt(N). The acquisition retains
the six coefficient estimates and a uniform-variation conclusion for suitably
modified admissible paths, using the fixed disc contained in the domain.
No assertion about every arbitrarily looping length-bounded path was added.
This is a qualification pending review of the source convention, not a
confirmed book erratum. The synopsis is unchanged.

## Olver O-8.04: the inverse-power signs in the hyperfactorial logarithm

**Disposition:** Agreed synopsis correction applied; ERRATA distinguishes printed defects from
synopsis-only transcription or interpretation corrections.


For `sum_{j=1}^n j log j`, the synopsis prints positive Bernoulli coefficients
`+B_(2k)/((2k)(2k-1)(2k-2)n^(2k-2))`. They should have a preceding minus sign.
Indeed `f'''(x)=-1/x²` for `f(x)=x log x`, so the first such Euler–Maclaurin
term is `-B_4/(24n²)=+1/(720n²)`. The printed synopsis gives its negative.
The existing `sumMulLogTerm` and `jLogJSum_eq` use the correct minus sign;
the acquisition reuses them and keeps the correct constant `1/12-zeta'(-1)`.
No existing Lean statement or synopsis text was changed for this issue.

## Olver O-12.16: logarithmic obstruction at an even higher pole

**Disposition:** Synopsis now states the higher-even-pole residue obstruction and uses a local
primitive, not an improper integral from a divergent endpoint. ERRATA-Olver retains the
counterexample.


The assertion of an analytic transformed coordinate for every integer pole order
m other than -2 needs an additional residue/nonresonance qualification. In the
source's printed p. 476, take m=-4 and F(z)=1+z, so
`f(z)=z^(-4)(1+z)`. Then `sqrt(f)=z^(-2)+(1/2)z^(-1)+...` has a primitive
containing `(1/2)log z`. The canonical relation gives
`zeta=z+(1/2)z²log z+...`, which is not analytic at zero. More directly, for
an analytic `zeta=z+a*z²+...`, the coefficient of `z^(-3)` in
`zeta'^2/zeta^4` is zero, whereas that coefficient of f is one.
The new targets retain the unrestricted zero/simple-pole cases and impose the
necessary obstruction conditions for higher poles. The synopsis remains unchanged;
this appears to be an overstatement in the source, subject to review of its conventions.

## Olver O-6.13: the finite uniqueness threshold needs the full error derivative

**Disposition:** The full finite phase-derivative threshold is explicit in the synopsis; the main
eigenvalue asymptotic is unchanged.


The normalized boundary sine error's parameter derivative includes both the
phase exponential derivative and the amplitude derivative. If A bounds the
function error and B the remaining parameter derivative, the sufficient finite
threshold is `(c*A+B)/sqrt(1-A²)<c`, with `A<1`. Merely retaining `B<c` omits
these terms and is not the stated quantitative conclusion. The new parameter
bounds retain the complete expression, consistent with the source's printed
pp. 216–217, (9.14)–(9.15). The synopsis is unchanged pending review.

## Olver O-13.06: spectral parameter versus large spectral index

**Disposition:** Synopsis now states the source’s O(1/u). The stronger O(1/n) rate remains
unproved here and is not labelled false.


The synopsis assigns additive O(1/n) error to the action for q(x)-u² under
the differentiated power-tail hypotheses. The source's printed p. 500, §9.4,
actually gives additive O(1/u). These orders cannot simply be identified for
a varying potential: the action and phase index need not be proportional to u.
The new confining-potential target follows the source's O(1/u) result and retains
all four differentiated tail hypotheses. The stronger synopsis rate remains
unacquired pending a separate argument or revision. No synopsis was edited.

## Olver's finite-order I Debye error quotient can have zero denominator

**Disposition:** Nonzero finite-normalizer warning added; the large-parameter asymptotic statement
is unchanged. Printed qualification retained in ERRATA-Olver.


The extra exact normalized error quotient in the source's printed p. 377,
(7.16), needs a nonzero origin/infinity normalizer. At N=2,
`U_1(1)=-1/12`; taking `nu=1/12` makes `1+U_1(1)/nu=0`. The selected
auxiliary recessive solution then vanishes identically and its infinity error
is -1, so division by `1+eta_N(nu,infinity)` is invalid at that parameter.
The new targets use the cleared identity for all positive nu and the quotient
only under nonvanishing. The large-nu asymptotic statement in O-10.07 is
unaffected. No existing tagged statement or synopsis was changed.

## Olver O-12.13: signed-order simple-pole coefficient arrays

**Disposition:** Agreed synopsis correction applied; ERRATA distinguishes printed defects from
synopsis-only transcription or interpretation corrections.


The source, printed pp. 465–466, normalizes its signed-order arrays by
`A_(s+1)^nu(0)=2*nu*B_s^nu(0)`. Thus the expansion of `P^{-m}` uses
`A^{-m}, B^{-m}` with `I_m, I_(m-1)`, and
`A_s^{-m}(0)=-2*m*B_(s-1)^{-m}(0)`. The zero constants in the synopsis
belong to the unrearranged array before the signed-order replacement. The
new targets use the source-normalized arrays and retain the finite-truncation
normalizer for exterior Q. The synopsis is unchanged pending review.
