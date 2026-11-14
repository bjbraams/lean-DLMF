# Rao–Lakshminarayanan: mathematical errata encountered

Source: K Srinivasa Rao and Vasudevan Lakshminarayanan, *Generalized Hypergeometric
Functions: Transformations and Group Theoretical Aspects*, IOP Publishing 2018,
version 20181001, DOI 10.1088/978-0-7503-1496-1. The requested filename retains
`LaoLaksh`; the first author is Rao. Locations below use printed chapter-page labels.
Each confirmed item was checked in a rendered image of the local PDF, not just in
extracted text. These are findings from assembling the synopsis, not a publisher's
errata list or an assertion of an exhaustive error search. Corrections are mathematical
statements, not certified Lean proofs.

## Confirmed printed defects

- **RL-E01 — Euler integral, (1.19), p. 1-5.** Replace upper endpoint $\infty$
  by $1$, and $(1-t)^{a-c}$ by $(1-t)^{c-b-1}$. For example, at $z=0$ the
  corrected integral is $B(b,c-b)$ and the prefactor makes the result $1$;
  the printed integral does not in general even converge.
- **RL-E02 — Associated Laguerre, Bell Theorem part 5, p. 1-17.** In the
  associated polynomial replace the lower parameter $1$ by $k+1$.
  For $n=1$, the printed result is $(k+1)(1-x)$; the associated Laguerre
  polynomial is $k+1-x$. Ordinary $k=0$ Laguerre is unaffected.
- **RL-E03 — Second-kind Chebyshev, Bell Theorem part 6, p. 1-17.** The
  displayed $n\sqrt{1-x^2}F(1-n,n+1;3/2;(1-x)/2)$ is $\sin(n\arccos x)$,
  not $U_n(x)$. The polynomial is
  $(n+1)F(-n,n+2;3/2;(1-x)/2)$, with $U_0=1$.
- **RL-E04 — Jacobi, Bell Theorem part 8, p. 1-18.** Replace
  $\Gamma(\alpha)$ in the prefactor by $\Gamma(\alpha+1)$, and the argument
  $(x-1)/2$ by $(1-x)/2$. The printed prefactor fails already for $n=0$;
  the argument sign gives the wrong degree-one polynomial.
- **RL-E05 — Confluence scale, (1.108), p. 1-20.** With $b\to\infty$ the
  argument must be $z/b$, not $z/a$. Indeed
  $F(a,b;a;z/b)=(1-z/b)^{-b}\to e^z$; the printed fixed argument has no
  such limit, for example at real $0<z/a<1$.
- **RL-E06 — Logarithm, (1.121), p. 1-23.** Replace $xF(1,1;2;x)$ by
  $xF(1,1;2;-x)$. The coefficient of $x^2$ is then $-1/2$, as required by
  $\log(1+x)$; the printed hypergeometric expression has $+1/2$.
- **RL-E07 — Legendre substitution and equation, (1.125–1.126),
  pp. 1-24–1-25.** The lower parameter is $c=1$, not $c=n$, and the
  differential equation's last term is $n(n+1)y$, not $n(n+1)$.
  In particular $P_2=(3x^2-1)/2$ solves the corrected equation.
- **RL-E08 — Gauss equation in Appendix A, p. 1-25.** Its coefficient of
  $y'$ must be $c-(a+b+1)z$, not $(c-a-b)z-1$. Substitute the series
  $1+(ab/c)z+O(z^2)$: the printed equation has constant residual
  $-ab/c-ab$ in general. The chapter's earlier Gauss equation is correct.
- **RL-E09 — Cube-coordinate map, (3.9), p. 3-5.** The lower parameter is
  $1+x_1-x_6$, not $1+x_1-x_2$. Under $g_1=(2\,4\,5\,3)$, indices $1,6$
  are fixed, as required by (3.10) and the Pfaff transformation. With the correction,
  the transformed second upper parameter is $c-a$ using $\sum x_i=0$.
- **RL-E10 — Riemann exponents, (3.15–3.17), p. 3-7.** The Fuchs relation is
  $\alpha+\alpha'+\beta+\beta'+\gamma+\gamma'=1$, not
  $\alpha+\alpha'+\beta\beta'+\gamma\gamma'=1$.
  For singular points $(0,1,\infty)$ the exponent pairs are
  $(0,1-c),(0,c-a-b),(a,b)$; (3.17) assigns the last two pairs in reverse order.
  These follow directly by the indicial equations of the Gauss differential equation.
- **RL-E11 — Whipple upper parameter, (4.8), p. 4-3.** Replace its first
  upper parameter $\alpha_{ijk}$ by $\alpha_{imn}$. The prose immediately
  below (4.8) gives the latter, consistent with (4.9) after $r\mapsto-r$.
  The former has the wrong parameter excess for the stated normalization.
- **RL-E12 — Ladder factor, (5.69), p. 5-11.** Replace $j\mp1$ in the
  factored square root by $j\mp m$:
  $j(j+1)-m(m\pm1)=(j\mp m)(j\pm m+1)$.
  Equation (5.72) on the same page has the correct expression.
- **RL-E13 — Spin-one-half matrices, (5.80), p. 5-12.** Remove the prefactor
  $1/2$ from $J_+$ and $J_-$; keep it on $J_z$. The preceding (5.78–5.79)
  have ladder entry $1$. The printed half-scaled matrices give
  $[J_+,J_-]=J_z/2$, contradicting $[J_+,J_-]=2J_z$.
- **RL-E14 — Spin-one matrices, (5.85–5.89), p. 5-13.** The two nonzero
  superdiagonal entries of $J_+$ and subdiagonal entries of $J_-$ are $\sqrt2$.
  In (5.87) the $(2,3)$ entry of $J_+$ is also accidentally omitted.
  The prefactors on the displayed $J_x,J_y$ arrays are $1/\sqrt2$, not $1/2$.
  These follow from (5.72); the printed matrices violate both the ladder formula
  and $J^2=2I$.
- **RL-E15 — Raised-state eigenvalue, (5.90), p. 5-14.** Its right side must
  be $(m\pm1)J_\pm|j,m\rangle$, not $(m\pm1)J_z|j,m\rangle$.
  This is exactly the commutator $[J_z,J_\pm]=\pm J_\pm$.
- **RL-E16 — Pauli product, (5.93), p. 5-14.** Replace the final $J_k$ by
  $\sigma_k$, and read the scalar Kronecker term as $\delta_{ij}I$:
  $\sigma_i\sigma_j=\delta_{ij}I+i\varepsilon_{ijk}\sigma_k$.
  For example $\sigma_x\sigma_y=i\sigma_z=2iJ_z$.
- **RL-E17 — Orthogonal-group coset representative, (5.110), p. 5-16.**
  The choice $P=-I$ works only for odd $n$. In even dimension it has determinant
  $+1$ and $PSO(n)=SO(n)$, missing the determinant-minus-one matrices.
  Any fixed orthogonal $P$ with determinant $-1$, such as
  $\mathrm{diag}(-1,1,\ldots,1)$, gives the stated decomposition in every positive dimension.
- **RL-E18 — Racah factorial sum, (6.9), p. 6-3.** The factorial product is
  a denominator, not a multiplier, and the prefactor $N$ from (6.10) is missing.
  The correct formula is $W=N\sum_P(-1)^P(P+1)!/
  [\prod_i(P-\alpha_i)!\prod_j(\beta_j-P)!]$.
  For $a=b=c=d=1,e=f=0$, the normalization is essential; the unnormalized
  printed sum cannot be a matrix coefficient of an orthogonal recoupling map.
- **RL-E19 — Factorial/Gamma bridge, (6.30), p. 6-7.** Replace
  $n!=\Gamma(n-1)$ by $n!=\Gamma(n+1)$. For $n=2$ the printed right side
  is $1$, whereas $2!=2$. The earlier (5.136) has the correct bridge.
- **RL-E20 — Bailey transformation, (6.75), p. 6-15.** Its left upper list
  has an extra $D$ and its first prefactor must be $(F-C)_n$, not $(F-G)_n$.
  The correct four upper parameters are $(A,B,C,-n)$ under the balancing
  condition $E+F+G=A+B+C-n+1$. The immediately following (6.76) supplies
  the correct list and prefactor.
- **RL-E21 — 9-j orthogonality normalization, (7.33–7.34), pp. 7-7–7-8.**
  The LS–jj overlap is $\sqrt{(2j_1+1)(2j_2+1)(2L+1)(2S+1)}$ times the
  9-j symbol. The labels $J,M$ in (7.33) must be $L,S$; $M$ is a magnetic
  label, not an intermediate representation dimension. Equation (7.34) must use
  the product of the two full overlap factors, including primed $L',S'$.
  RL-7.04–RL-7.05 state the unambiguous orthogonal-matrix identity.
- **RL-E22 — Kampé de Fériet definition, (7.109), p. 7-20.** The denominator
  factor $\prod_{j=1}^D(b_j)_k$ must be $\prod_{j=1}^D(d_j)_k$, matching
  the lower list in the notation. The printed version cancels the wrong upper
  parameters and ignores the displayed lower list.
- **RL-E23 — Arguments in the labelled Proposition, (7.112), p. 7-20.**
  Both arguments on the left must be $(1,1)$ rather than free $(x,y)$.
  The right side is independent of $x,y$ and the left is generally not;
  the preceding paragraph and the integral proof are explicitly for unit arguments.
- **RL-E24 — Beta factors in the proof, (7.114–7.117), p. 7-21.**
  In (7.114) omit the prefactor $\Gamma(x+y)/(\Gamma(x)\Gamma(y))$
  in front of the integral defining $B(x,y)$. In (7.115) the integral's powers
  must be $t^{x+k-1}(1-t)^{y+l-1}$, with that prefactor retained.
  In (7.117) Euler's prefactor is $(1-t)^{e-b-c}$, not $(-1)^{e-b-c}$.
  These corrections are forced already by $k=l=0$ and Euler's transformation.
- **RL-E25 — Lower prefactor in (7.132), p. 7-25.** Replace $(d)_n$ by
  $(c)_n$; $d$ does not occur elsewhere in the identity. With $a'=0$, it
  reduces to the terminating Vandermonde case and confirms this denominator.
- **RL-E26 — Malformed labelled Proposition, (7.134), p. 7-25.** Its second
  numerator prefactor is $(c'-a')_n$ and its last lower parameter is
  $1+a'-c'-n$, replacing the malformed $c'-a-$ and the printed
  $a+a'-c'-n$. Reversing the terminating series in (7.138) gives precisely
  these corrections. For $n=1,a=2,b=3,c=5,d=7,a'=4,c'=11$, both corrected
  sides equal $179/385$.
- **RL-E27 — Repeated Euler-integral error, (8.5), p. 8-2.** Its integrand
  must contain $(1-t)^{c-b-1}(1-zt)^{-a}$, not
  $(1-t)^{b-1}(1-zt)^{c-b-1}$; hypotheses require
  $\Re c>\Re b>0$ on the Euler-integral locus. This is the correction in RL-E01.
- **RL-E28 — Unbound parameter in extended integral, (8.9), p. 8-2.**
  Remove $(1-tz)^{-a'}$. The remaining formula contains no $a'$, and at
  $l=m$ the first Gauss factor is $1$, reducing to Bateman's (8.6) only
  without that factor. Setting $a'=0$ is another valid reading of the printed expression.
- **RL-E29 — Cubic lower parameter and repeated labels, item 13, p. 8-12.**
  In the first (8.40), the last lower parameter on the right is
  $3a-b+3/2$, not $a-b+3/2$; the following transformed identity (8.41)
  has the correct one. The two successive cubic pairs on this page both use
  labels (8.40–8.41); likewise distinct formulas on pp. 8-13 and 8-14 both
  use (8.44–8.45). Cite item and page as well as equation number.
- **RL-E30 — Odd coefficient, second (8.44), p. 8-14.** Replace its
  $\Gamma(-(1+a+b)/2)$ by $\Gamma(-1/2)\Gamma((1+a+b)/2)$.
  At $a=b=1$, the exact function is
  $F(1,1;3/2;(1-t)/2)$; differentiating at $t=0$ gives the corrected odd
  coefficient $-1$, whereas the printed coefficient is $4/(3\sqrt\pi)>0$.
- **RL-E31 — Variables in the labelled Theorem, (9.32), p. 9-10.**
  Both $n!$ must be $N!$ and the second Gamma denominator must be
  $\Gamma(a-x+1)$ instead of $\Gamma(a=x+1)$. The latter is not even
  an expression with a complex argument; the finite-sum parameter below it
  and the limiting derivation identify the intended minus sign.
- **RL-E32 — Rising-factorial split, first (9.39), p. 9-12.** Replace
  $(1+\varepsilon)_{k+N-1}$ by $(1+\varepsilon)_{k-N-1}$:
  $(\varepsilon-N)_k=(\varepsilon-N)_N\varepsilon
  (1+\varepsilon)_{k-N-1}$ for $k\ge N+1$.
  The degrees in $\varepsilon$ on the two sides otherwise differ by $2N$.
- **RL-E33 — Triple-sum sign inconsistency, (7.44), p. 7-10.** The printed
  phase $(-1)^{z_5}$ is inconsistent with the book's own 6-j definition and
  (7.37), not merely with a different convention. For the admissible array
  $(1,1,1;1,1,1;1,1,0)$, (7.37) has just $x=1$. Its three 6-j factors,
  evaluated by the Racah factorial sum, are $-1/3,1/6,-1/3$, giving $+1/18$.
  In (7.44), the $Q$-prefactor ratio is $1$, $z_5=1$, and the three permitted
  $(x,z)$ terms are $-1/9,-1/18,2/9$ (with $y=0$), giving $-1/18$ after
  the printed phase. The displayed array also prints $g$ where its middle-right
  entry should be $f$. The corrected general phase has not been derived here;
  see the separate candidate below. The synopsis retains the exact signed 9-j
  definition and records the squared variant only as a conjectural repair, not an established theorem.

## Candidate correction requiring further verification

- **RL-S01 — General phase for (7.44).** Replacing $(-1)^{z_5}$ by
  $(-1)^{c+f+i+2g+2h}$ agrees with the conventional 6-j expansion for
  116 exact nonzero integer and half-integer test arrays, including the internal
  counterexample RL-E33. This is evidence for a correction, not a general proof.
  An algebraic phase derivation from the six Clebsch–Gordan factors remains needed
  before adopting the unsquared formula as a Lean theorem. The squared formula
  in the synopsis also remains a conjectural repair: the exact tests support its
  magnitude but do not establish the general identity. The firm finite formula
  for formalization is the book's three-6-j sum or the explicit six-CG definition.

## Domain and interpretation cautions

- Associated Legendre in Bell's Theorem uses the derivative convention **without**
  the Condon–Shortley sign. That convention difference is not an error.
- Nonresonant Gauss bases require nonintegral exponent differences; excluding
  only one sign of integral difference does not make every displayed lower
  parameter regular. The synopsis states the symmetric nonintegrality conditions.
- Several terminating 3-j and 6-j representations have nonpositive lower
  parameters. The finite factorial sums remain meaningful, but a singular
  unnormalized hypergeometric series cannot be assigned an arbitrary totalized
  value and expected to preserve the identity.
- The informal $S_3\times S_3\times S_2$ notation for the 9-j array group means
  a semidirect product: transposition exchanges row and column permutations.
  The action is specified explicitly in the synopsis.
- In (9.30–9.32), products of a Gamma pole and a vanishing digamma bracket
  require a limit of the whole expression. For example $x=1$ is allowed on
  the convergent left side, but the separated right factors are singular.
  The $a=0$ extension in (9.32) also requires a limit; the hypergeometric value
  is $1$ and the literal $\psi(0)$ expression is undefined.
- Numerous extraction artifacts, notably lost square-root signs on $\sqrt\pi$
  in (9.14), (9.30) and (9.40), were checked against images. Those factors are
  printed correctly and are **not** recorded as book errors.


## Exceptional specialization: qualification of the synopsis convention

Nonvanishing lower factors through a first terminating index define an individual
finite sum. They do not imply that every generic transformation survives independent
finite evaluation at coincident singular parameters. These are qualifications of the
synopsis's blanket extension rule, not claims that the generic printed identities fail.

- RL-3.03: at \(a=c=-1,b=1/2\), the finite seed is \(1+z/2\), while its
  independently finite Euler transform is \((1-z)^{-1/2}\).
- RL-8.12: \(a=c=-1\) gives \(1+2t\) versus \((1-t)^{-2}\).
- RL-8.15: \(a=-1,b=-1/2,c=-1\) gives \(1-2t+2t^2\) versus \((1-t)^2\).
- RL-8.18: \(a=-2\), with generic positive b,c, gives \(1+t\) versus
  \(1/(1-t)\).
- RL-8.19: \(a=-1\) gives \(1-t/2\) versus \(1-2t\).

Use regular lower parameters, a separately justified finite identity, or a specified
coherent limit of the entire normalized expression. Likewise RL-1.18 requires
\((b)_k\ne0\) through k=n before cancelling b in F(-n,b;b;z); n=1,b=0 is a
counterexample to the unrestricted finite reading. The Jucys–Bandzaitis candidate
repairs and their dependent claims retain their conjectural status.
