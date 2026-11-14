# Temme Chapter 3 alternating-series supplement

This supplement addresses the two remaining ordinary-order series subclaims in
SYNOPSIS-Temme.md. It leaves the source synopsis, definitions and tagged statements unchanged.

## TEM-03-06 — The unpaired digamma series

New proved `DLMF.Gamma.tendsto_sum_alternating_reciprocal` in
[DLMF/Gamma/AlternatingDigamma.lean](DLMF/Gamma/AlternatingDigamma.lean) states, for every
complex `z` with `Re z>0`,

`lim_N sum_{n<N} (-1)^n/(n+z) = (digamma((z+1)/2)-digamma(z/2))/2`.

Provenance: Temme, *Special Functions* (1996), Chapter 3, equations (3.10)–(3.14),
pp. 53–56, synopsis TEM-03-06. This is the original natural order, not an unconditional
`HasSum` assertion for a conditionally convergent complex series. The proof derives
absolute summability of adjacent pairs from the existing digamma series, uses the proved
`DLMF.Gamma.digamma_half_diff`, and combines the even partial sums with the vanishing
last term of the odd partial sums. The module passes strict Lean checking with
`autoImplicit=false` and `relaxedAutoImplicit=false`; no admission is introduced. A direct transitive `#print axioms` check reports only
`propext`, `Classical.choice` and `Quot.sound` for the new theorem.

## TEM-03-07 — Eta and the Bose Mellin integral

Existing proved `DLMF.Zeta.tendsto_alternating_partial_sums` in
[DLMF/Zeta/Riemann.lean](DLMF/Zeta/Riemann.lean) gives the exact natural-order complex
alternating series for `Re s>0`, `s!=1`, with limit `(1-2^(1-s))*riemannZeta s`.
It includes nontrivial zeros of the prefactor; no division by that factor is used.
Existing proved `DLMF.Constants.tendsto_dirichletEta_one` in
[DLMF/Constants/Dirichlet.lean](DLMF/Constants/Dirichlet.lean) supplies the removable
value `log 2` at `s=1` by the same natural partial sums. The totalized unconditional
`DLMF.Constants.dirichletEta` definition is used only in its absolutely convergent domain.
These existing declarations cover the complete eta subclaim; no duplicate target is added.

Existing proved `DLMF.Zeta.riemannZeta_eq_integral_exp_sub_one` in
[DLMF/Zeta/IntegralReps/ElementaryKernels.lean](DLMF/Zeta/IntegralReps/ElementaryKernels.lean)
includes absolute integrability of `t^(s-1)/(exp(t)-1)` for `Re s>1` and its integral
as `Gamma(s)*riemannZeta(s)`. Multiplying the stated reciprocal-Gamma formula by the
nonzero Gamma factor gives the exact source normalization.
