# DLMF Chapter 5 acquisition inventory

Reviewed against the live [NIST DLMF Chapter 5](https://dlmf.nist.gov/5) on
2026-09-17 (Version 1.2.8, release 2026-09-15) and the project's local Mathlib
**v4.34.0** sources. The project has since moved to Mathlib v4.35.0-rc2; this inventory was not re-reviewed against it.

This inventory covers numbered equations in §§5.2 and 5.4–5.18. Notation §5.1,
graphics §5.3, applications §§5.19–5.20, and computation §§5.21–5.24 were not
acquired.

## What was added

New modules under `DLMF/Gamma/` record tagged statements for Pochhammer
identities, special values, inequalities, series, products, integral
representations, continued fractions, Stirling expansions, Beta integrals,
Mellin–Barnes integrals, polygamma, Barnes `G`, and remaining `q`-gamma facts.
Every acquired mathematical result carries Mathlib's `@[dlmf ...]`
cross-reference attribute. Existing project results were tagged instead of
copied. Statements already supplied by Mathlib are identified in
[MathlibCoverage.lean](MathlibCoverage.lean) and below, without duplicate
project declarations.

Newly acquired identities are admitted (`sorry`) unless they were already
proved in the original Gamma files. No AAR source statement was changed.
The odd case of 5.4.2 was aligned to the DLMF display
`n!! = π^{-1/2} 2^{n/2+1/2} Γ(n/2+1)` (an earlier draft used the even-case
exponent `2^{n+1/2}` with Lean's `n` in `(2n+1)!!`).

## Interpretation and domain restrictions

- Mathlib `Complex.Gamma` vanishes at nonpositive integers (`0⁻¹ = 0` in a
  field), so reciprocal-Gamma identities hold at those poles as well.
- Complex powers and `log Γ` use principal branches. Positive real arguments
  are used for Binet, Stirling, and continued-fraction statements.
- Vertical Barnes integrals replace `c±i∞` contours by a real line `σ + it`
  in the indicated strip. For 5.13.1 the factor `1/(2πi)\,ds` becomes
  `1/(2π)\,dt`.
- The bound 5.6.8 is stated for real `x > 1` with `0 ≤ (b-a).re`, as
  `x^{-Re(b-a)}`, in place of the sectorial form with `|z|^{b-a}`.
- q-gamma inequalities 5.18.8–5.18.9 compare real parts of Mathlib-style
  complex `qGamma`.
- The continued-fraction partial numerators `a_k` are transcribed for
  `k = 0,…,6` as in the source display; the infinite tail is not filled in.
- Stirling coefficients `g_k` and `G_k(a,b)` are recorded for the tabulated
  low orders.

“Deferred” means the equation was reviewed but no formal theorem was introduced
because the required contour, remainder-region, or decimal-constant API is
absent.

## Mathlib and existing project coverage

| Equation | Declaration |
| --- | --- |
| 5.2.E1 | Mathlib: `Gamma_eq_integral` |
| 5.2.E2 | Mathlib: `Complex.digamma`; project: `Real.digamma` |
| 5.2.E3 | Mathlib: `Real.eulerMascheroniConstant` |
| 5.2.E4 | Existing: [`pochhammer_zero`](../Hypergeometric/Basic.lean), [`pochhammer_succ`](../Hypergeometric/Basic.lean) |
| 5.2.E5 | Mathlib: `Gamma_add_nat_div_Gamma_eq` |
| 5.4.E1 | Mathlib: `Gamma_one`, `Gamma_nat_eq_factorial` |
| 5.4.E6 | Mathlib: `Gamma_one_half_eq` |
| 5.4.E12 | Mathlib: `Complex.digamma_one`; project: [`digamma_one`](Digamma.lean); trigamma: [`trigamma_one`](SpecialValues.lean) |
| 5.4.E13 | Project: [`digamma_one_div_two`](GaussDigamma.lean); Mathlib: `Complex.digamma_one_half`; trigamma: [`trigamma_one_div_two`](SpecialValues.lean) |
| 5.4.E14 | Project: [`digamma_nat_add_one`](Digamma.lean) |
| 5.5.E1 | Mathlib: `Gamma_add_one` |
| 5.5.E2 | Mathlib: `digamma_apply_add_one`; project: [`digamma_add_one`](Digamma.lean) |
| 5.5.E3 | Mathlib: `Gamma_mul_Gamma_one_sub` |
| 5.5.E4 | Mathlib: `digamma_one_sub` |
| 5.5.E5 | Mathlib: `Gamma_mul_Gamma_add_half` |
| 5.5.E6 | Project: [`Gamma_mul_nat`](Multiplication.lean) |
| 5.5.E7 | Project: [`prod_Gamma_div`](Multiplication.lean) |
| 5.5.E8 | Mathlib: `digamma_two_mul`; project: [`digamma_add_digamma_add_half`](GaussDigamma.lean) |
| 5.5.E9 | Project: [`digamma_sum_add_div`](GaussDigamma.lean) |
| 5.7.E6 | Project: [`digamma_eq_tsum`](Digamma.lean) |
| 5.8.E1 | Mathlib: `GammaSeq_tendsto_Gamma` |
| 5.8.E2 | Project: [`one_div_Gamma_eq_tprod`](Basic.lean) |
| 5.11.E3 | Project: [`Gamma_nat_succ_isEquivalent_stirlingGamma`](Stirling.lean) (positive-integer form) |
| 5.12.E1 | Mathlib: `betaIntegral`; project: [`selberg_integral_one`](../Selberg/Basic.lean) |
| 5.14.E4 | Project: [`selberg_integral`](../Selberg/Basic.lean), [`aomoto_integral`](../Selberg/Basic.lean) |
| 5.15.E1 | Project: [`trigamma_eq_tsum`](Digamma.lean) |
| 5.18.E1, E3 | Existing: `qPochhammer`, `qPochhammerInf` |
| 5.18.E4, E5, E7 | Existing: [`qGamma`](../QSeries/Pochhammer.lean), `qGamma_one`, `qGamma_add_one` |
| 5.18.E12 | Existing: [`q_beta_integral`](../QSeries/Identities.lean) |

## Deferred infrastructure

| Equations | Reason |
| --- | --- |
| 5.4.E7–E10 | Decimal expansions, not mathematical identities |
| 5.4.E20 | Local extrema of `Γ` on the negative axis, indexed zeros |
| 5.9.E2 | Hankel loop `∫_{-∞}^{(0+)}` |
| 5.9.E11, E11_1, E11_2, E17 | Mellin–Barnes with `ζ(-s)` / complex `Γ*` |
| 5.11.E10–E11 | Remainder `R_K` with `sec(ph z)` |
| 5.11.E5–E6 | `g_k` in terms of the 5.10 numerators; recurrence for those numerators |
| 5.11.E8, E14, E16–E18 | Bernoulli polynomials / full `H_k` table |
| 5.12.E9–E12 | Hankel, Pochhammer, and loop contours |
| 5.8.E4 | Balancing hypothesis only (paired with 5.8.5) |

## Section summary

| Section | Tagged / numbered | Notes |
| --- | ---: | --- |
| [5.2](https://dlmf.nist.gov/5.2) | 7 / 7 | E4 split across `pochhammer_zero`/`pochhammer_succ`; E6–E7 new |
| [5.4](https://dlmf.nist.gov/5.4) | 15 / 20 | Decimals and extrema deferred |
| [5.5](https://dlmf.nist.gov/5.5) | 9 / 9 | Mathlib or existing project |
| [5.6](https://dlmf.nist.gov/5.6) | 9 / 9 | New inequalities |
| [5.7](https://dlmf.nist.gov/5.7) | 8 / 8 | E6 existing; remainder new |
| [5.8](https://dlmf.nist.gov/5.8) | 4 / 5 | E4 is the balancing hypothesis |
| [5.9](https://dlmf.nist.gov/5.9) | 20 / 25 | Loops and Mellin–Barnes deferred |
| [5.10](https://dlmf.nist.gov/5.10) | 1 / 1 | `a_0`–`a_6` transcribed |
| [5.11](https://dlmf.nist.gov/5.11) | 10 / 19 | Remainders and full coefficient tables deferred |
| [5.12](https://dlmf.nist.gov/5.12) | 8 / 12 | Contours deferred |
| [5.13](https://dlmf.nist.gov/5.13) | 5 / 5 | Vertical-line forms |
| [5.14](https://dlmf.nist.gov/5.14) | 7 / 7 | Selberg existing; Dirichlet/Hermite/circular new |
| [5.15](https://dlmf.nist.gov/5.15) | 9 / 9 | E1 existing |
| [5.16](https://dlmf.nist.gov/5.16) | 2 / 2 | New |
| [5.17](https://dlmf.nist.gov/5.17) | 7 / 7 | Barnes `G` defined by 5.17.3 |
| [5.18](https://dlmf.nist.gov/5.18) | 12 / 12 | Core `q`-gamma existing; remainder new |

## Proof status (2026-10-17)

Proved on 2026-10-17: 5.4.19 (`digamma_rat`), 5.6.2, 5.6.3, 5.6.9, 5.7.2, 5.7.3,
5.9.2_5 (`recip_Gamma_binet`), 5.11.9, 5.11.13, 5.11.19, 5.12.5, 5.12.6, 5.13.2, 5.13.4,
5.14.5, 5.17.1, 5.17.2, 5.17.4, 5.17.5, 5.18.8, 5.18.9, 5.18.10. The Selberg integral
(`DLMF/Selberg/Basic.lean`) and Aomoto's integral were proved the same day.

5.12.8 was restated with `Γ(a+b)/((a+b-1)Γ(a)Γ(b))` in place of `1/((a+b-1) B(a,b))`
(Mathlib's `betaIntegral` vanishes for `Re a ≤ 0`) and proved, together with 5.14.6 and
5.14.7, later the same day.

Still admitted in `DLMF/Gamma` (2): 5.6.8 (`Gamma_ratio_norm_le`) and 5.13.5
(de Branges–Wilson).
