# Duverney: errata and formalization cautions

Source: Daniel Duverney, *An Introduction to Hypergeometric Functions*, Birkhäuser,
2024, [local PDF](References/Duverney2024IntroductionHypergeometricFunctions-Birkhäuser.pdf).
Page numbers below are printed page numbers. The items marked **confirmed** were checked
against rendered PDF pages, rather than inferred solely from text extraction. Evidence
here is mathematical reasoning and exact substitutions, not Lean-checked counterexamples.
The proposed correct statements are used in [SYNOPSIS-Duverney.md](SYNOPSIS-Duverney.md).
This is a record of issues encountered during the synopsis, not a claim of an exhaustive
publisher errata search.

## Confirmed printed errors

- **DU-E01 — p. 12, sentence after (1.47).** The exclusion is printed
  $1-x\notin\mathbb Z_{\le1}$, followed by the assertion that $x<1$ suffices.
  Replace $\mathbb Z_{\le1}$ by $\mathbb Z_{\le0}$. For example $x=0<1$ gives
  $1-x=1$, contradicting the printed implication. Gamma at $1$ is well defined.
- **DU-E02 — p. 26, (2.5).** The integer range is printed $n\ge0$.
  It must be $n\ge1$ for the book's digamma, whose domain excludes zero.
  The finite sum is $H_{n-1}$ and $\psi$ has a pole at zero.
- **DU-E03 — p. 45, (2.77), the $k=3$ eta entry.** Replace
  $31\pi^4/30240$ by $31\pi^6/30240$.
  Equations (2.71) and (2.76) give
  $\eta(6)=(1-2^{-5})\zeta(6)=31\pi^6/30240$.
- **DU-E04 — p. 49, Exercise 2.7, first displayed sum.** The printed identity has
  $\sum_{n\ge1}(-1)^n/n^{2k}=b_k\pi^{2k}/(2k)!$.
  The correct right side is
  $-(2^{2k-1}-1)b_k\pi^{2k}/(2k)!$.
  For $k=1$ the left side is negative, while the printed right side is positive;
  the general correction follows from $-\eta(2k)$ and (2.71), (2.76).
- **DU-E05 — p. 50, Exercise 2.13(2).** The coefficient $b_k$ in the displayed
  expansion for $B_n(x)$ needs the factor $(-1)^{k+1}$, because $b_k$ denotes the
  positive Bernoulli convention in (2.46). At $n=4,x=0$ the printed expression gives
  $+1/30$, while the generating function (2.94) gives $B_4(0)=-1/30$.
- **DU-E06 — p. 51, Exercise 2.13(5).** The finite difference must read
  $B_{p+1}(x+1)-B_{p+1}(x)=(p+1)x^p$.
  At $p=1$, $B_2(x)=x^2-x+1/6$ gives a difference of $2x$, not $x$.
- **DU-E07 — p. 51, Faulhaber formula in Exercise 2.13(5).** For the printed range
  $p\ge0$, replace $B_{p+1}(0)$ by $B_{p+1}(1)$, or separately exclude $p=0$.
  The sum from $1$ through $n$ equals
  $[B_{p+1}(n+1)-B_{p+1}(1)]/(p+1)$.
  At $p=0$ the printed right side equals $n+1$, while the left side equals $n$.
- **DU-E08 — p. 51, Exercise 2.14(3).** Replace
  $E_{2n}(1/2)=e_n/2^{2n}$ by $E_{2n}(1/2)=(-1)^ne_n/2^{2n}$.
  The generating function (2.95) gives $E_2(x)=x^2-x$; hence $E_2(1/2)=-1/4$,
  whereas $e_1=1$.
- **DU-E09 — p. 70, first convergence bullet.** The divergence condition printed
  $r\ge s+1$ must be $r\ge s+2$ in the nonterminating case.
  The next bullet correctly states convergence for $r=s+1$, $|x|<1$.
  The geometric example ${}_1F_0(1;;1/2)=2$ is an explicit contradiction to the
  printed first bullet.
- **DU-E10 — p. 71, Theorem 3.3, (3.11).** If $R$ denotes the radius of the original
  series $\sum\lambda_kx^k$, the conclusion is valid for $|x|<R$, not in general
  $|x|<R/|A|$. Take $\lambda_k=2^{-k}$, $A=1/2$, $r=1$, $s=0$, $a_1=1$.
  Then $R=2$, but the printed conclusion includes $x=3$, where the original series
  diverges. The corrected statement is DU-3.03.
- **DU-E11 — p. 79, Theorem 3.10, (3.33).** The final upper-parameter subscript on
  the right side is printed $a_s$. It must be $a_r$:
  $\theta\prod_{j=1}^s(\theta+c_j-1)y=x\prod_{i=1}^r(\theta+a_i)y$.
  This agrees with (3.25) and the preceding continuation equation (3.30).
- **DU-E12 — p. 89, Exercise 3.14(3).** Both first oscillatory correction signs are
  reversed. The correct expansions are
  $C_F(x)=1/2+\sin(\pi x^2/2)/(\pi x)+O(x^{-3})$ and
  $S_F(x)=1/2-\cos(\pi x^2/2)/(\pi x)+O(x^{-3})$.
  Integrate the complex tail $\int_x^\infty e^{i\pi t^2/2}\,dt$ by parts to get
  $i e^{i\pi x^2/2}/(\pi x)+O(x^{-3})$, then subtract it from the limiting integral.
- **DU-E13 — p. 128, Exercise 4.13, (4.72).** The real-domain assertion needs
  $y>0$ (the intended $y=\sqrt{1-x^2}$). The printed conditions allow
  $x=\sqrt3/2,y=-1/2$, for which the right-hand hypergeometric argument is $9$,
  outside the real branch $(-\infty,1)$ defined in the book. This is a missing
  domain restriction, not a numerical counterexample on a different complex branch.
- **DU-E14 — p. 153, (5.6).** The perimeter's first expression must be $L=4aE(e)$,
  not $2\pi aE(e)$. The second expression $2\pi a\,{}_2F_1(-1/2,1/2;1;e^2)$ is
  correct by (5.5). In the circle limit $E(0)=\pi/2$, the printed first expression
  gives $\pi^2a$ instead of $2\pi a$.
- **DU-E15 — p. 184, last relation of (6.17).** Insert $x$ after $c-a$:
  $acF^{a+1}+(c-a)xF_{c+1}-c(a+x)F=0$.
  At $x=0$ every ordinary $M$ is one, and the printed left side is $c-a$.
  For example $a=1,c=2$ gives one instead of zero.
- **DU-E16 — p. 211, proof of Theorem 7.7.** The displayed test points have an
  extra $\pi/2$: use $u_k=\nu\pi/2+\pi/4+k\pi$ instead of
  $(\nu+1)\pi/2+\pi/4+k\pi$. The former makes the leading cosine in (7.33)
  equal $(-1)^k$; the printed choice makes it zero. The theorem itself is unaffected.
- **DU-E17 — pp. 212–213, (7.36–7.39).** The derivation silently discards a lower
  boundary term and requires integrability at zero. For noninteger orders the displayed
  formulas require $\nu>-1$; integer negative orders are also valid using
  $J_{-n}=(-1)^nJ_n$. For example $\nu=-3/2$ has
  $J_\nu(x)\sim(x/2)^\nu/\Gamma(\nu+1)$, so the squared-integral integrand behaves
  as a positive multiple of $x^{-2}$ and is not integrable at zero.
- **DU-E18 — p. 261, Exercise 8.5(2).** Replace
  $\log(\sin(\theta/2))$ by $\log(2\sin(\theta/2))$ in
  $\mathrm{Log}(1-e^{i\theta})$ for $0<\theta<2\pi$.
  At $\theta=\pi$, the principal logarithm on the left is $\log2$, while the printed
  right side is zero. The imaginary part $(\theta-\pi)/2$ is correct.
- **DU-E19 — p. 289, Theorem 9.9, (9.33).** The gamma quotient needs a removable-value
  convention at $n=0$, $\alpha+\beta=-1$, allowed by $\alpha,\beta>-1$.
  Its factor $(2n+\alpha+\beta+1)\Gamma(n+\alpha+\beta+1)$ is then $0\cdot\Gamma(0)$.
  The beta expression in DU-9.08 is valid without a convention; in particular at
  $\alpha=\beta=-1/2$ the norm is $\pi$, not a totalized zero quotient.
- **DU-E20 — p. 360, proof of Lemma D.2.** The factorization
  $k(u)=k(0)+k'(0)u h(u)$ is not valid for every smooth $k$.
  Take $k(u)=u^2$, so $k'(0)=0$ but $k$ is not constant.
  Replace it by $k(u)=k(0)+u h(u)$, where
  $h(u)=\int_0^1k'(su)\,ds$ is smooth; the proof then works with no $k'(0)$ factor.
  The lemma's statement is unchanged.

## Literal-domain cautions

- **p. 123, Lemma 4.13.** The only printed parameter hypothesis is
  $a+b\notin\mathbb Z_{\le0}$, but the formula contains $\Gamma(a)$, $\Gamma(b)$,
  $\psi(a+k)$ and $\psi(b+k)$. With $a=0,b=1$ it is not a literal real-valued
  expression, although the left side equals one. DU-4.17 gives the ordinary formula
  for $a,b,a+b\notin\mathbb Z_{\le0}$; terminating cases need analytic parameter
  limits. This is a notation/domain issue, rather than a claim that the limiting
  connection formula is false.
- Gamma quotient summations elsewhere are also read using reciprocal gamma factors
  or removable limits when individual denominator gamma functions have poles. A Lean
  division by a totalized zero gamma value is not automatically the same expression.

## Text extraction issues excluded from the errata

The extracted text of (10.17) and (10.23) misplaces superscripts and fraction numerators.
The rendered pages 320–321 correctly print $(1-q)x^{\alpha+1}/(1-q^{\alpha+1})$
and $(1-q)x^{k+1}/(1-q^{k+1})$. These two formulas are not errors in the book.
