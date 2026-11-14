# Errata audit — Olver, *Asymptotics and Special Functions*

Source audited: F. W. J. Olver, corrected 1997 edition, the local file
[Olver1997AsymptoticsSpecialFunctionsCorrectedEd-TaylorFrancis.pdf](References/Olver1997AsymptoticsSpecialFunctionsCorrectedEd-TaylorFrancis.pdf).
Printed page numbers are primary; PDF page numbers equal printed page plus 19.

The acquisition audit found two mathematical qualifications with explicit
counterexamples, recorded below. These concern the scope of printed assertions,
not OCR artifacts. The book's historical corrections of earlier work are separate.
The synopsis incorporates the agreed qualifications. The source evidence and
remaining interpretation questions are retained in
[BookAcquisition-RevisionNotes.md](BookAcquisition-RevisionNotes.md).

## Higher even-order poles and analytic comparison coordinates (p. 476)

For `f(z)=z^(-4)*(1+z)`, the proposed analytic coordinate at the pole cannot
satisfy `zeta'(z)^2/zeta(z)^4=f(z)`. Indeed,
`sqrt(f(z))=z^(-2)+(1/2)*z^(-1)+O(1)`, so integrating introduces a logarithm.
An analytic normalized coordinate `zeta=z+a*z²+O(z³)` instead has
`zeta'^2/zeta^4=z^(-4)+O(z^(-2))`, with zero coefficient at `z^(-3)`.
The displayed f has that coefficient equal to one. An additional residue
condition, or allowance for a logarithmic coordinate, is therefore necessary
for this higher-even-pole case. The new Lean targets retain the exact permitted
families and recurrence/divisibility constraints; they do not assert this
unqualified analytic coordinate claim.

## A finite Debye normalizer can vanish (p. 377, (7.16))

The exact error quotient divides by the finite normalization
`1+eta_N(nu,infinity)`. At N=2 this is `1+U_1(1)/nu`, and the printed
Debye polynomial gives `U_1(1)=-1/12`. It vanishes at the permitted positive
parameter `nu=1/12`. The corresponding cleared identity remains meaningful,
whereas the quotient requires a nonzero normalizer. The large-nu asymptotic
conclusion is unaffected. The acquired Lean statements distinguish the cleared
identity from its quotient form.

## Branch and theorem-scope qualifications

These are implementation qualifications, not confirmed printing errors.

- The parabolic-cylinder identity using `U(a/2+1/4,1/2,z²/2)` must start at
  positive `z` and continue with its correlated argument sheet. Replacing the
  squared argument by its principal value independently after a half-turn makes
  the right side even in `z` and does not give the entire parabolic-cylinder
  function. See O-7.17, pp. 258–260.
- The ordinary Whittaker `M` has the ordinary Kummer parameter restrictions;
  dividing by `Γ(2μ+1)` defines a separately normalized regularized function.
  At exceptional parameters, one must specify which of these is being used.
- Zero-localization statements in Chapters 11–12 require real normalized
  solutions when their conclusions describe zeros in real intervals. A complex
  perturbation in the preceding existence theorem does not automatically preserve
  such real zeros. Each comparison bracket must also lie in the domain under
  consideration.
- Integral interchange, Abel–Plana, inversion, and infinite-reference error bounds
  retain their convergence hypotheses. Formal substitution into a differential
  equation is not substituted for a uniform remainder theorem.
- The separated-scaling classification in Theorem 14.1 of Chapter 12 concerns a
  variable parameter family and a parameter-independent comparison function;
  it does not classify arbitrary solutions at a single fixed parameter value.

## OCR and scan artifacts excluded from the errata list

The searchable text frequently drops numerators in fractions, omits displayed
formulas, and misreads page headers. Formulas were checked from rendered pages
when those defects affected the mathematics. Examples include:

- `3π/2` being extracted as `3π` in rank-one asymptotic sectors.
- The positive `sin(πc)/π` Wronskian in Chapter 5, p. 163, being misread as
  negative; the printed formula has the correct positive sign.
- Missing square-root powers and the half-power factor in the Bell-number saddle
  coefficient on p. 331.
- The positive first inverse-map coefficient in Chapter 9, p. 348, being extracted
  without a readable sign.
- Numerous running page numbers, including 287, 291, 309, and 351, being confused
  with other digits. Source locators in the synopsis use the actual printed sequence.

These extraction problems must not be cited as mathematical errata in the book.

## Synopsis corrections and remaining interpretation questions

The corrections to O-1.14 (reversion signs), O-8.04 (hyperfactorial signs),
O-8.13 (inclusive Darboux truncation), O-9.10 (Airy tails and derivative growth),
and O-12.13 (signed-order arrays) correct the synopsis, not the printed book.
O-13.06 now follows the source's O(1/u) action error; the stronger O(1/n)
rate is not established by the acquisition and is not labelled a confirmed error.
O-6.13 states the full finite phase-derivative threshold explicitly.

For O-11.11, weighted path length alone cannot bound all looping-path variations.
The synopsis gives an explicit additional inner-path control and distinguishes
admissible modified paths from arbitrary original paths. Whether the book's path
convention already supplies this restriction remains an interpretation question,
not a confirmed printing error.
