# DLMF Chapter 25 acquisition: Zeta and Related Functions

This acquisition covers the definitions, numbered formulas and analytical assertions in prose
of [DLMF Chapter 25](https://dlmf.nist.gov/25), version 1.2.8, checked on 2026-10-25. It was
done in two parts: part A (ACQ25A) covers the Riemann zeta function, §§25.1–25.10; part B
(ACQ25B) covers §§25.11–25.21 (Hurwitz zeta, polylogarithms, Lerch's transcendent, Dirichlet
L-functions, and the excluded applications and computation sections) in its own sections
below. The modules are under [DLMF/Zeta/](DLMF/Zeta); part A's Mathlib pointers are in
[DLMF/Zeta/MathlibCoverage.lean](DLMF/Zeta/MathlibCoverage.lean), part B's in
`DLMF/Zeta/MathlibCoverageB.lean`. Existing Chapter 25 pointers in
[DLMF/Core/UpstreamElementary.lean](DLMF/Core/UpstreamElementary.lean) (25.2.1, 25.2(i),
25.2.4, 25.2.11, 25.4.1, 25.4.3, 25.6.1–25.6.3, 25.11.1, 25.11.2) are kept and not repeated.

ζ(s) is Mathlib's `riemannZeta`, defined on all of ℂ by analytic continuation, with the junk
value `riemannZeta 1 = (γ - log 4π)/2` at the pole; Λ(s) = π^{-s/2}Γ(s/2)ζ(s) is
`completedRiemannZeta` and its entire completion Λ₀ is `completedRiemannZeta₀`.

Part A: §§25.2, 25.4–25.6, 25.8–25.10 have 76 numbered equations (25.2: 12, 25.4: 6, 25.5: 21,
25.6: 20, 25.8: 10, 25.9: 3, 25.10: 4), all in scope and all covered; §25.1 (notation), §25.3
(graphics) and §25.7 (a bibliographic pointer) have none. Part A lives in `Riemann`,
`Reflection`, `IntegralReps`, `IntegerArguments`, `Sums`, `Asymptotics` and `Zeros` under
`DLMF/Zeta/`, with 93 tagged declarations: 13 definitions, 28 proved theorems (7 of them proved
from admissions) and **52 direct admissions** (`grep -c '\bsorry\b'`: Riemann 6, Reflection 1,
IntegralReps 20, IntegerArguments 13, Sums 7, Asymptotics 1, Zeros 4), plus 10 new
`dlmf_upstream` pointers and two `@[dlmf]` tags added in place in
[DLMF/Constants/Dirichlet.lean](DLMF/Constants/Dirichlet.lean) (`dirichletLambda_eq` 25.2.E2,
`hasSum_dirichletEta` 25.2.E3).

**Status after proof round 1 (2026-10-25).** The 212 declarations tagged with Chapter 25 IDs are 22 definitions, 96 proved theorems and 94 theorems that still depend on admissions; direct admissions in DLMF/Zeta fell from 124 to 87. The per-line statuses in this ledger are regenerated from the compiled dump; the counts below record the acquisition. See REVIEW.md, "Proof round 1 for Chapters 24–27 (2026-10-25)".

**Status after proof round 2 (2026-10-25).** The 213 declarations tagged with Chapter 25 IDs are 22 definitions, 126 proved theorems and 65 theorems that still depend on admissions; direct admissions in DLMF/Zeta fell from 87 to 62. 25.11.10 received the hypothesis s ≠ 0, −1, −2, … after a proved counterexample (Lean's totalized ζ(1); the errata report (reports/DLMFErrata.tex) (c)). See REVIEW.md, "Proof round 2 for Chapters 24–27 (2026-10-25)".

**Status after proof round 3 (2026-10-26).** The 213 declarations tagged with Chapter 25 IDs are 22 definitions, 142 proved theorems and 49 theorems that still depend on admissions; direct admissions in DLMF/Zeta fell from 62 to 46. No statement was changed. See REVIEW.md, "Proof round 3 for Chapters 24–27 (2026-10-26)".

## Domains, conventions and source corrections (part A)

- No DLMF erratum was found in §§25.1–25.10. Every numbered formula was checked numerically with
  mpmath at real and complex sample points (scripts in the acquisition scratch area); all agree
  to working precision, the conditionally or slowly convergent ones (25.2.8, 25.5.5, 25.6.5,
  25.2.12 with 300 pairs of zeros) to the accuracy of the truncation.
- Totalization. Lean's `x/0 = 0`, `Γ = 0` at its poles, `cot 0 = 0` and the junk value of
  `ζ(1)` are never used to fake an identity. Where DLMF divides by `1 - 2^{1-s}` (25.2.3,
  25.5.3, 25.5.4, 25.5.10, 25.5.21), which vanishes at `s = 1 + 2πik/ln 2`, the multiplied form
  is stated; it is equivalent where the factor is nonzero and also true at its zeros (stronger
  than DLMF). Removable `0·∞` and `0/0` forms in printed formulas are excluded by explicit
  hypotheses: 25.4.2 (`s = 2, 3, …`), 25.4.5 (`s = -1, -2, …`), 25.5.13 (`s = 0`), 25.8.3
  (`s = 0, -1, …`), 25.8.6 (`z = 0`), 25.10.4 (`cos √(2πt) = 0`). `1/Γ` is kept as printed
  where Lean's value `0` at the poles is the value of the reciprocal Gamma function (25.2.12,
  25.5.6, 25.5.7).
- Riemann's ξ (25.4.4) is defined as the entire function `½ s(s-1) Λ₀(s) + ½`; the printed
  product is proved wherever its factors are defined, and ξ(s) = ξ(1-s) is proved.
- Series: absolutely convergent series use `HasSum`; 25.2.3 (conditionally convergent for
  Re s ≤ 1) uses natural-order partial sums; 25.5.5 (conditionally convergent at ∞) uses the
  limit of `∫₀^R`. Lebesgue integrals are stated together with integrability.
- The Stieltjes constants (25.2.5) are `stieltjesConstant n = limUnder atTop (stieltjesSeq n)`;
  the existence of the limit is a separate (admitted) theorem, proved for n = 0 (γ₀ = γ).
- B̃ₙ (§25.1) is ACQ24A's `DLMF.BernoulliEuler.periodicBernoulliB`; the generalized binomial
  coefficient of complex top is `z25a_gbinom z m = (descPochhammer ℂ m).eval z / m!`; ψ is
  `Complex.digamma`, ψ^{(m)} is `DLMF.Gamma.polygamma m`; γ is `Real.eulerMascheroniConstant`.
- The Hankel-type loops of 25.5.20–25.5.21 are represented by the keyhole contours
  `keyholeLoopIntegral` (edges of the cut `(-∞, -δ]` with boundary values `x^a e^{∓iπa}`, and the
  circle `|z| = δ`), for every admissible radius; independence of the loop is not formalized.
- Zeros with multiplicity: the Hadamard product 25.2.12 and the counting functions N(T),
  N₀(T) of §25.10(ii) use `analyticOrderNatAt riemannZeta ρ`.
- θ(t) (25.10.2) uses the principal phase `Complex.arg`, as DLMF prescribes; it differs from
  the continuous Riemann–Siegel theta function (mpmath's `siegeltheta`) by integer multiples of
  2π (e.g. by 23·2π at t = 100). Z(t) and every statement of the chapter depend only on e^{iθ}.
  `riemannSiegelZ` is proved equal to Mathlib's `hardyZ`, so Z is real.
- 25.9.1 is stated with explicit uniform constants (`∃ C T₀`, for all x, y ≥ 1 with 2πxy = t),
  for each fixed σ ∈ [0, 1], including the endpoints, as DLMF states; numerically the ratio of
  the error to `x^{-σ} + y^{σ-1}t^{½-σ}` stays below 0.51 for σ = 0, 0.3, 1 and t ≤ 3000.
- The Riemann hypothesis is not acquired (conjecture); Mathlib's `RiemannHypothesis` is
  recorded as the statement only.

## Numbered formulas and prose items (part A)

## [§25.2 Definition and Expansions](https://dlmf.nist.gov/25.2)

- [25.2.E1](https://dlmf.nist.gov/25.2.E1): Mathlib: [`zeta_eq_tsum_one_div_nat_cpow`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=zeta_eq_tsum_one_div_nat_cpow#doc). Re s > 1; pointer in DLMF/Core/UpstreamElementary.lean (the n = 0 term is 0^s = 0).
- [25.2.E2](https://dlmf.nist.gov/25.2.E2): [`DLMF.Zeta.riemannZeta_eq_odd_series`](DLMF/Zeta/Riemann.lean#L69) (proved); [`DLMF.Constants.dirichletLambda_eq`](DLMF/Constants/Dirichlet.lean#L99) (proved). Re s > 1, where 1 - 2^{-s} ≠ 0; printed form with summability, proved from the existing Dirichlet λ identity (tagged in place).
- [25.2.E3](https://dlmf.nist.gov/25.2.E3): [`DLMF.Zeta.tendsto_alternating_partial_sums`](DLMF/Zeta/Riemann.lean#L1235) (proved); [`DLMF.Zeta.riemannZeta_eq_alternating`](DLMF/Zeta/Riemann.lean#L1283) (proved); [`DLMF.Constants.hasSum_dirichletEta`](DLMF/Constants/Dirichlet.lean#L115) (proved). Multiplied form (1 - 2^{1-s}) ζ(s) = lim of natural partial sums for Re s > 0, s ≠ 1 (covers the zeros s = 1 + 2πik/ln 2 of the factor); printed form for 2^{1-s} ≠ 1. The existing absolutely convergent case Re s > 1 is tagged in place.
- [25.2.E4](https://dlmf.nist.gov/25.2.E4): [`DLMF.Zeta.hasSum_riemannZeta_laurent`](DLMF/Zeta/Riemann.lean#L580) (proved); Mathlib: [`tendsto_riemannZeta_sub_one_div`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=tendsto_riemannZeta_sub_one_div#doc). Laurent series stated as a HasSum for all s ≠ 1 (the regular part is entire); Mathlib has the constant term γ₀ = γ.
- [25.2.E5](https://dlmf.nist.gov/25.2.E5): [`DLMF.Zeta.stieltjesSeq`](DLMF/Zeta/Riemann.lean#L89) (definition); [`DLMF.Zeta.stieltjesConstant`](DLMF/Zeta/Riemann.lean#L95) (definition); [`DLMF.Zeta.tendsto_stieltjesSeq`](DLMF/Zeta/Riemann.lean#L155) (proved); [`DLMF.Zeta.stieltjesConstant_zero`](DLMF/Zeta/Riemann.lean#L218) (proved). stieltjesConstant n is the limUnder of stieltjesSeq n; existence of the limit admitted for general n, proved for n = 0 (γ₀ = γ, from Mathlib's harmonic-number limit).
- [25.2.E6](https://dlmf.nist.gov/25.2.E6): [`DLMF.Zeta.hasSum_deriv_riemannZeta`](DLMF/Zeta/Riemann.lean#L256) (proved). Re s > 1; sum over all n : ℕ (the n = 0, 1 terms vanish). From Mathlib's LSeries derivative.
- [25.2.E7](https://dlmf.nist.gov/25.2.E7): [`DLMF.Zeta.hasSum_iteratedDeriv_riemannZeta`](DLMF/Zeta/Riemann.lean#L231) (proved). Re s > 1, all k ≥ 0 (stronger than DLMF: also k = 0); from Mathlib's LSeries_iteratedDeriv.
- [25.2.E8](https://dlmf.nist.gov/25.2.E8): [`DLMF.Zeta.riemannZeta_eq_sum_add_integral_fract`](DLMF/Zeta/Riemann.lean#L1137) (proved). Re s > 0, s ≠ 1, N ≥ 1, with x - ⌊x⌋ = Int.fract x; absolute integrability on (N, ∞) included.
- [25.2.E9](https://dlmf.nist.gov/25.2.E9): [`DLMF.Zeta.riemannZeta_eq_eulerMaclaurin`](DLMF/Zeta/Riemann.lean#L1295) (proved). n, N ≥ 1, Re s > -2n, s ≠ 1; B̃ is the project's periodicBernoulliB (ACQ24A); generalized binomial via descPochhammer (z25a_gbinom).
- [25.2.E10](https://dlmf.nist.gov/25.2.E10): [`DLMF.Zeta.riemannZeta_eq_eulerMaclaurin_one`](DLMF/Zeta/Riemann.lean#L1317) (proved). Derived from 25.2.9 with N = 1.
- [25.2.E11](https://dlmf.nist.gov/25.2.E11): Mathlib: [`riemannZeta_eulerProduct_tprod`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=riemannZeta_eulerProduct_tprod#doc); Mathlib: [`riemannZeta_eulerProduct_hasProd`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=riemannZeta_eulerProduct_hasProd#doc). Re s > 1; tprod pointer in DLMF/Core/UpstreamElementary.lean, HasProd pointer in DLMF/Zeta/MathlibCoverage.lean.
- [25.2.E12](https://dlmf.nist.gov/25.2.E12): [`DLMF.Zeta.riemannZeta_hadamard_product`](DLMF/Zeta/Riemann.lean#L1337) (admitted). Hadamard product over the zeros with Re ρ > 0, repeated by multiplicity (analyticOrderNatAt) as an unconditional HasProd, for s ≠ 1; 1/Γ(s/2+1) written (Γ(s/2+1))⁻¹ (Lean value 0 at the poles matches the trivial zeros). Checked numerically with 300 conjugate pairs of zeros (error 1.3e-4, consistent with truncation).

## [§25.4 Reflection Formulas](https://dlmf.nist.gov/25.4)

- [25.4.E1](https://dlmf.nist.gov/25.4.E1): Mathlib: [`riemannZeta_one_sub`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=riemannZeta_one_sub#doc). s ∉ {1, 0, -1, -2, …}; pointer in DLMF/Core/UpstreamElementary.lean.
- [25.4.E2](https://dlmf.nist.gov/25.4.E2): [`DLMF.Zeta.riemannZeta_eq_reflection`](DLMF/Zeta/Reflection.lean#L45) (proved). s ≠ 0 and s ∉ {1, 2, 3, …} (DLMF: s ≠ 0, 1; at s = 2, 3, … the printed right side is a removable 0·∞ form); proved from riemannZeta_one_sub.
- [25.4.E3](https://dlmf.nist.gov/25.4.E3): [`DLMF.Zeta.riemannXi_one_sub`](DLMF/Zeta/Reflection.lean#L97) (proved); Mathlib: [`completedRiemannZeta_one_sub`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=completedRiemannZeta_one_sub#doc). ξ(s) = ξ(1-s) for all s, proved; Mathlib's completedRiemannZeta_one_sub is the same identity for Λ(s) = π^{-s/2}Γ(s/2)ζ(s) (different normalization).
- [25.4.E4](https://dlmf.nist.gov/25.4.E4): [`DLMF.Zeta.riemannXi`](DLMF/Zeta/Reflection.lean#L60) (definition); [`DLMF.Zeta.differentiable_riemannXi`](DLMF/Zeta/Reflection.lean#L68) (proved); [`DLMF.Zeta.riemannXi_eq`](DLMF/Zeta/Reflection.lean#L84) (proved). riemannXi is the entire function ½ s(s-1) Λ₀(s) + ½ built on Mathlib's completedRiemannZeta₀; the printed product is proved for s ≠ 1, s ∉ {0, -2, -4, …}.
- [25.4.E5](https://dlmf.nist.gov/25.4.E5): [`DLMF.Zeta.iteratedDeriv_riemannZeta_one_sub`](DLMF/Zeta/Reflection.lean#L157) (proved). All k ≥ 0; excludes, besides s ≠ 0, 1, the poles s = -1, -2, … of Γ (where the right side is a limit). Checked numerically for k = 1, 2, 3 at complex s.
- [25.4.E6](https://dlmf.nist.gov/25.4.E6): [`DLMF.Zeta.reflectionConst`](DLMF/Zeta/Reflection.lean#L103) (definition). The constant c = -ln(2π) - πi/2.

## [§25.5 Integral Representations](https://dlmf.nist.gov/25.5)

- [25.5.E1](https://dlmf.nist.gov/25.5.E1): [`DLMF.Zeta.riemannZeta_eq_integral_exp_sub_one`](DLMF/Zeta/IntegralReps.lean#L172) (proved). Re s > 1; integrability on (0, ∞) included.
- [25.5.E2](https://dlmf.nist.gov/25.5.E2): [`DLMF.Zeta.riemannZeta_eq_integral_exp_sub_one_sq`](DLMF/Zeta/IntegralReps.lean#L229) (proved). Re s > 1.
- [25.5.E3](https://dlmf.nist.gov/25.5.E3): [`DLMF.Zeta.riemannZeta_eq_integral_exp_add_one`](DLMF/Zeta/IntegralReps.lean#L349) (proved). Multiplied form (1 - 2^{1-s}) Γ(s) ζ(s) = ∫, Re s > 0, s ≠ 1 (stronger than DLMF: holds at the zeros of 1 - 2^{1-s}).
- [25.5.E4](https://dlmf.nist.gov/25.5.E4): [`DLMF.Zeta.riemannZeta_eq_integral_exp_add_one_sq`](DLMF/Zeta/IntegralReps.lean#L452) (proved). Multiplied form, Re s > 0, s ≠ 1.
- [25.5.E5](https://dlmf.nist.gov/25.5.E5): [`DLMF.Zeta.tendsto_integral_fract_sub_half`](DLMF/Zeta/IntegralReps.lean#L570) (proved). -1 < Re s < 0; the integral converges only conditionally at ∞, stated as the limit of ∫₀^R.
- [25.5.E6](https://dlmf.nist.gov/25.5.E6): [`DLMF.Zeta.riemannZeta_eq_half_add_integral`](DLMF/Zeta/IntegralReps.lean#L683) (proved). Re s > -1, s ≠ 1; 1/Γ(s) as printed (Lean's value 0 at s = 0 is the reciprocal-Gamma value).
- [25.5.E7](https://dlmf.nist.gov/25.5.E7): [`DLMF.Zeta.riemannZeta_eq_half_add_bernoulli_integral`](DLMF/Zeta/IntegralReps.lean#L833) (admitted). n ≥ 1, Re s > -(2n+1), s ≠ 1; Pochhammer (s)_k = (ascPochhammer ℂ k).eval s.
- [25.5.E8](https://dlmf.nist.gov/25.5.E8): [`DLMF.Zeta.riemannZeta_eq_integral_sinh`](DLMF/Zeta/IntegralReps.lean#L851) (proved). Re s > 1.
- [25.5.E9](https://dlmf.nist.gov/25.5.E9): [`DLMF.Zeta.riemannZeta_eq_integral_sinh_sq`](DLMF/Zeta/IntegralReps.lean#L908) (proved). Re s > 1.
- [25.5.E10](https://dlmf.nist.gov/25.5.E10): [`DLMF.Zeta.riemannZeta_eq_integral_arctan_cosh`](DLMF/Zeta/IntegralReps.lean#L955) (admitted). Multiplied form (1 - 2^{1-s}) ζ(s) = 2^{s-1} ∫, all s ≠ 1.
- [25.5.E11](https://dlmf.nist.gov/25.5.E11): [`DLMF.Zeta.riemannZeta_eq_integral_arctan_exp_sub_one`](DLMF/Zeta/IntegralReps.lean#L965) (admitted). All s ≠ 1.
- [25.5.E12](https://dlmf.nist.gov/25.5.E12): [`DLMF.Zeta.riemannZeta_eq_integral_arctan_exp_add_one`](DLMF/Zeta/IntegralReps.lean#L975) (admitted). All s ≠ 1.
- [25.5.E13](https://dlmf.nist.gov/25.5.E13): [`DLMF.Zeta.riemannZeta_eq_integral_zetaOmega`](DLMF/Zeta/IntegralReps.lean#L1115) (proved). s ≠ 0, 1 (s = 0 is a removable 1/(0·∞) form of the printed first term).
- [25.5.E14](https://dlmf.nist.gov/25.5.E14): [`DLMF.Zeta.zetaOmega`](DLMF/Zeta/IntegralReps.lean#L987) (definition); [`DLMF.Zeta.zetaOmega_eq_jacobiTheta`](DLMF/Zeta/IntegralReps.lean#L993) (proved). zetaOmega x = ∑_{n≥1} e^{-n²πx}; the theta form is proved with Mathlib's jacobiTheta (θ₃(0|τ)).
- [25.5.E15](https://dlmf.nist.gov/25.5.E15): [`DLMF.Zeta.riemannZeta_eq_integral_log_sub_digamma`](DLMF/Zeta/IntegralReps.lean#L1147) (admitted). 0 < Re s < 1; ψ = Complex.digamma.
- [25.5.E16](https://dlmf.nist.gov/25.5.E16): [`DLMF.Zeta.riemannZeta_eq_integral_inv_sub_trigamma`](DLMF/Zeta/IntegralReps.lean#L1157) (admitted). 0 < Re s < 2, s ≠ 1 (DLMF's wider range for this formula); ψ' = DLMF.Gamma.polygamma 1.
- [25.5.E17](https://dlmf.nist.gov/25.5.E17): [`DLMF.Zeta.riemannZeta_one_add_eq_integral_digamma`](DLMF/Zeta/IntegralReps.lean#L1377) (proved). 0 < Re s < 1.
- [25.5.E18](https://dlmf.nist.gov/25.5.E18): [`DLMF.Zeta.riemannZeta_one_add_eq_integral_trigamma`](DLMF/Zeta/IntegralReps.lean#L1520) (proved). 0 < Re s < 1.
- [25.5.E19](https://dlmf.nist.gov/25.5.E19): [`DLMF.Zeta.riemannZeta_nat_add_eq_integral_polygamma`](DLMF/Zeta/IntegralReps.lean#L1536) (proved). m ≥ 1, 0 < Re s < 1; ψ^{(m)} = DLMF.Gamma.polygamma m.
- [25.5.E20](https://dlmf.nist.gov/25.5.E20): [`DLMF.Zeta.riemannZeta_eq_loop_integral`](DLMF/Zeta/IntegralReps.lean#L1561) (admitted). s ∉ {1, 2, 3, …}; the loop is the keyhole of radius 0 < δ < 2π (keyholeLoopIntegral); independence of the loop not formalized.
- [25.5.E21](https://dlmf.nist.gov/25.5.E21): [`DLMF.Zeta.riemannZeta_eq_loop_integral_add`](DLMF/Zeta/IntegralReps.lean#L1572) (admitted). Multiplied form, s ∉ {1, 2, 3, …}; keyhole of radius 0 < δ < π.

## [§25.6 Integer Arguments](https://dlmf.nist.gov/25.6)

- [25.6.E1](https://dlmf.nist.gov/25.6.E1): [`DLMF.Zeta.riemannZeta_four`](DLMF/Zeta/IntegerArguments.lean#L39) (proved); [`DLMF.Zeta.riemannZeta_six`](DLMF/Zeta/IntegerArguments.lean#L47) (proved); Mathlib: [`riemannZeta_zero`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=riemannZeta_zero#doc); Mathlib: [`riemannZeta_two`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=riemannZeta_two#doc). ζ(0), ζ(2) in Mathlib (pointers in DLMF/Core/UpstreamElementary.lean); ζ(4), ζ(6) proved here from riemannZeta_two_mul_nat.
- [25.6.E2](https://dlmf.nist.gov/25.6.E2): Mathlib: [`riemannZeta_two_mul_nat`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=riemannZeta_two_mul_nat#doc). n ≥ 1, with (-1)^{n+1} B_{2n} in place of |B_{2n}|; pointer in DLMF/Core/UpstreamElementary.lean.
- [25.6.E3](https://dlmf.nist.gov/25.6.E3): Mathlib: [`riemannZeta_neg_nat_eq_bernoulli`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=riemannZeta_neg_nat_eq_bernoulli#doc). Stronger: also n = 0; pointer in DLMF/Core/UpstreamElementary.lean.
- [25.6.E4](https://dlmf.nist.gov/25.6.E4): Mathlib: [`riemannZeta_neg_two_mul_nat_add_one`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=riemannZeta_neg_two_mul_nat_add_one#doc). Exact, as ζ(-2(n+1)) = 0, n ≥ 0.
- [25.6.E5](https://dlmf.nist.gov/25.6.E5): [`DLMF.Zeta.hasSum_multiple_sum_riemannZeta`](DLMF/Zeta/IntegerArguments.lean#L55) (admitted). k ≥ 1; the k-fold sum (over Fin k → ℕ, n_i + 1) has sum k! ζ(k+1).
- [25.6.E6](https://dlmf.nist.gov/25.6.E6): [`DLMF.Zeta.riemannZeta_two_mul_add_one_eq_integral`](DLMF/Zeta/IntegerArguments.lean#L138) (proved). k ≥ 1; interval integrability of B_{2k+1}(t) cot(πt) included.
- [25.6.E7](https://dlmf.nist.gov/25.6.E7): [`DLMF.Zeta.riemannZeta_two_eq_double_integral`](DLMF/Zeta/IntegerArguments.lean#L269) (proved). Integrability on the unit square included; iterated interval integrals.
- [25.6.E8](https://dlmf.nist.gov/25.6.E8): [`DLMF.Zeta.hasSum_riemannZeta_two_central_binom`](DLMF/Zeta/IntegerArguments.lean#L308) (proved). Series from k = 1 written with k + 1, k : ℕ.
- [25.6.E9](https://dlmf.nist.gov/25.6.E9): [`DLMF.Zeta.hasSum_riemannZeta_three_central_binom`](DLMF/Zeta/IntegerArguments.lean#L327) (admitted). As 25.6.8.
- [25.6.E10](https://dlmf.nist.gov/25.6.E10): [`DLMF.Zeta.hasSum_riemannZeta_four_central_binom`](DLMF/Zeta/IntegerArguments.lean#L334) (admitted). As 25.6.8.
- [25.6.E11](https://dlmf.nist.gov/25.6.E11): Mathlib: [`deriv_riemannZeta_zero`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=deriv_riemannZeta_zero#doc). Exact.
- [25.6.E12](https://dlmf.nist.gov/25.6.E12): [`DLMF.Zeta.iteratedDeriv_two_riemannZeta_zero`](DLMF/Zeta/IntegerArguments.lean#L343) (admitted). γ₁ = stieltjesConstant 1.
- [25.6.E13](https://dlmf.nist.gov/25.6.E13): [`DLMF.Zeta.iteratedDeriv_riemannZeta_neg_two_mul`](DLMF/Zeta/IntegerArguments.lean#L355) (proved). n ≥ 1, all k ≥ 0; proved from 25.4.5 at s = 2n+1 (inherits that admission).
- [25.6.E14](https://dlmf.nist.gov/25.6.E14): [`DLMF.Zeta.iteratedDeriv_riemannZeta_one_sub_two_mul`](DLMF/Zeta/IntegerArguments.lean#L390) (proved). n ≥ 1, all k ≥ 0; proved from 25.4.5 at s = 2n.
- [25.6.E15](https://dlmf.nist.gov/25.6.E15): [`DLMF.Zeta.deriv_riemannZeta_two_mul`](DLMF/Zeta/IntegerArguments.lean#L425) (proved). n ≥ 1; ψ = Complex.digamma.
- [25.6.E16](https://dlmf.nist.gov/25.6.E16): [`DLMF.Zeta.riemannZeta_two_mul_recursion`](DLMF/Zeta/IntegerArguments.lean#L550) (proved). n ≥ 2.
- [25.6.E17](https://dlmf.nist.gov/25.6.E17): [`DLMF.Zeta.riemannZeta_four_mul_add_two_recursion`](DLMF/Zeta/IntegerArguments.lean#L599) (proved). n ≥ 1.
- [25.6.E18](https://dlmf.nist.gov/25.6.E18): [`DLMF.Zeta.riemannZeta_four_mul_recursion`](DLMF/Zeta/IntegerArguments.lean#L608) (proved). n ≥ 1.
- [25.6.E19](https://dlmf.nist.gov/25.6.E19): [`DLMF.Zeta.riemannZeta_two_mul_recursion_two`](DLMF/Zeta/IntegerArguments.lean#L629) (proved). m, n ≥ 0, m + n ≥ 1.
- [25.6.E20](https://dlmf.nist.gov/25.6.E20): [`DLMF.Zeta.riemannZeta_two_mul_recursion_pow_two`](DLMF/Zeta/IntegerArguments.lean#L704) (proved). n ≥ 2.

## [§25.8 Sums](https://dlmf.nist.gov/25.8)

- [25.8.E1](https://dlmf.nist.gov/25.8.E1): [`DLMF.Zeta.hasSum_riemannZeta_sub_one`](DLMF/Zeta/Sums.lean#L73) (proved). As HasSum over k + 2, k : ℕ.
- [25.8.E2](https://dlmf.nist.gov/25.8.E2): [`DLMF.Zeta.hasSum_Gamma_mul_riemannZeta_sub_one`](DLMF/Zeta/Sums.lean#L619) (proved). s ∉ {1, 0, -1, -2, …}.
- [25.8.E3](https://dlmf.nist.gov/25.8.E3): [`DLMF.Zeta.hasSum_pochhammer_mul_riemannZeta`](DLMF/Zeta/Sums.lean#L638) (proved). s ≠ 1; the Lean statement also excludes s = 0, -1, -2, … where the printed series contains the 0·∞ term (s)_{1-s} ζ(1) (Lean's totalized ζ(1) would give a wrong value; the printed formula holds there only as a limit).
- [25.8.E4](https://dlmf.nist.gov/25.8.E4): [`DLMF.Zeta.hasSum_neg_one_pow_riemannZeta_mul_sub_one`](DLMF/Zeta/Sums.lean#L872) (proved). n ≥ 2; principal logarithm of the positive real product.
- [25.8.E5](https://dlmf.nist.gov/25.8.E5): [`DLMF.Zeta.hasSum_riemannZeta_mul_pow`](DLMF/Zeta/Sums.lean#L918) (proved). |z| < 1; proved from the project's ψ(1+z) series (5.7.4).
- [25.8.E6](https://dlmf.nist.gov/25.8.E6): [`DLMF.Zeta.hasSum_riemannZeta_two_mul_mul_pow`](DLMF/Zeta/Sums.lean#L935) (proved). 0 < |z| < 1 (z = 0 is a removable 0·∞ form with Lean's cot 0 = 0); proved from the project's cotangent series.
- [25.8.E7](https://dlmf.nist.gov/25.8.E7): [`DLMF.Zeta.hasSum_riemannZeta_div_mul_pow`](DLMF/Zeta/Sums.lean#L950) (proved). |z| < 1, principal logarithm (equals DLMF's ln Γ on the disk); proved from the project's ln Γ(1+z) series (5.7.3) and Mathlib's -log(1-z) series.
- [25.8.E8](https://dlmf.nist.gov/25.8.E8): [`DLMF.Zeta.hasSum_riemannZeta_two_mul_div_mul_pow`](DLMF/Zeta/Sums.lean#L1175) (proved). |z| < 1, principal logarithm (|ph(πz/sin πz)| < 1.65 on the disk, checked numerically).
- [25.8.E9](https://dlmf.nist.gov/25.8.E9): [`DLMF.Zeta.hasSum_riemannZeta_two_mul_div_odd`](DLMF/Zeta/Sums.lean#L1291) (proved). Exact value.
- [25.8.E10](https://dlmf.nist.gov/25.8.E10): [`DLMF.Zeta.hasSum_riemannZeta_two_mul_div_odd_even`](DLMF/Zeta/Sums.lean#L1380) (admitted). Exact value.

## [§25.9 Asymptotic Approximations](https://dlmf.nist.gov/25.9)

- [25.9.E1](https://dlmf.nist.gov/25.9.E1): [`DLMF.Zeta.approximate_functional_equation`](DLMF/Zeta/Asymptotics.lean#L37) (admitted). Fixed 0 ≤ σ ≤ 1, O-terms uniform in x, y ≥ 1 with 2πxy = t, as an explicit bound C (x^{-σ} + y^{σ-1} t^{½-σ}) for t ≥ T₀. Checked numerically at σ = 0, 0.3, 1.
- [25.9.E2](https://dlmf.nist.gov/25.9.E2): [`DLMF.Zeta.riemannChi`](DLMF/Zeta/Asymptotics.lean#L32) (definition). χ(s) = π^{s-½} Γ(½-s/2)/Γ(s/2).
- [25.9.E3](https://dlmf.nist.gov/25.9.E3): [`DLMF.Zeta.riemannZeta_critical_line_approx`](DLMF/Zeta/Asymptotics.lean#L48) (proved from admissions). IsBigO at t → ∞; proved from 25.9.1 with σ = ½, x = y = √(t/2π).

## [§25.10 Zeros](https://dlmf.nist.gov/25.10)

- [25.10.E1](https://dlmf.nist.gov/25.10.E1): [`DLMF.Zeta.riemannSiegelZ`](DLMF/Zeta/Zeros.lean#L153) (definition); [`DLMF.Zeta.riemannSiegelZ_eq_hardyZ`](DLMF/Zeta/Zeros.lean#L195) (proved); [`DLMF.Zeta.riemannSiegelZ_im`](DLMF/Zeta/Zeros.lean#L207) (proved); Mathlib: [`hardyZ`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=hardyZ#doc). riemannSiegelZ t = e^{iθ(t)} ζ(½+it); equal to Mathlib's hardyZ (proved), hence real.
- [25.10.E2](https://dlmf.nist.gov/25.10.E2): [`DLMF.Zeta.riemannSiegelTheta`](DLMF/Zeta/Zeros.lean#L147) (definition). Principal phase (Complex.arg) as DLMF prescribes; differs from the continuous Riemann–Siegel θ by multiples of 2π (all chapter statements depend only on e^{iθ}).
- [25.10.E3](https://dlmf.nist.gov/25.10.E3): [`DLMF.Zeta.riemannSiegelRemainder`](DLMF/Zeta/Zeros.lean#L284) (definition); [`DLMF.Zeta.riemannSiegelRemainder_isBigO`](DLMF/Zeta/Zeros.lean#L291) (admitted). R(t) = O(t^{-1/4}), with R defined from the real part of Z.
- [25.10.E4](https://dlmf.nist.gov/25.10.E4): [`DLMF.Zeta.riemannSiegelRemainder_sub_leading_isBigO`](DLMF/Zeta/Zeros.lean#L297) (admitted). Along t → ∞ with cos √(2πt) ≠ 0 (elsewhere the printed quotient is a removable 0/0 form). Checked numerically at t = 10, 100, 1000 (the leading term is Ψ(p) = cos 2π(p²-p-1/16)/cos 2πp, p = frac √(t/2π)).

## Prose, informal and excluded items (part A)

- [25.1](https://dlmf.nist.gov/25.1) p1–p4 (notation; the table of symbols): conventions only.
  k, m, n, p, x, a, s, z, γ (`Real.eulerMascheroniConstant`), ψ (`Complex.digamma`),
  Bₙ and Bₙ(x) (Mathlib's `bernoulli`, `bernoulliFun`, `Polynomial.bernoulli`; B₁ = -1/2 as in
  DLMF), B̃ₙ(x) (`DLMF.BernoulliEuler.periodicBernoulliB`), m ∣ n and primes for derivatives.
  p3 (Riemann 1859) and p4 (related functions, treated in part B) are informal.
- [25.2.i](https://dlmf.nist.gov/25.2.i): ζ is meromorphic with a simple pole of residue 1 at; Mathlib: [`riemannZeta_residue_one`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/RiemannZeta.html#riemannZeta_residue_one); Mathlib: [`differentiableAt_riemannZeta`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/RiemannZeta.html#differentiableAt_riemannZeta).
  s = 1 as its only singularity; Mathlib `riemannZeta_residue_one`, `differentiableAt_riemannZeta`
  (pointers in DLMF/Core/UpstreamElementary.lean).
- [25.2.ii](https://dlmf.nist.gov/25.2.ii) p2: a cross-reference to §27.4 (Dirichlet series,
  1/ζ(s)); excluded: cross-reference.
- [25.2.iii](https://dlmf.nist.gov/25.2.iii), [25.2.iv](https://dlmf.nist.gov/25.2.iv): the
  pointers to §24.2 and §5.2 and the description of the product over zeros are encoded in
  25.2.E9–E12.
- [§25.3](https://dlmf.nist.gov/25.3) (graphics): excluded: graphics. Its caption remark that
  Z(t) and ζ(½+it) have the same zeros is `riemannSiegelZ_eq_zero_iff`.
- [25.4](https://dlmf.nist.gov/25.4) p1–p2: the conditions s ≠ 0, 1 and k ≥ 1 are encoded (with
  the Lean restrictions listed above).
- [25.5.i](https://dlmf.nist.gov/25.5.i), [25.5.ii](https://dlmf.nist.gov/25.5.ii): the
  conditions (s ≠ 1; 0 < Re s < 1 in 25.5.15–25.5.19; 0 < Re s < 2 for 25.5.16) are encoded.
  The pointer to Erdélyi et al. for other theta functions is bibliographic (excluded).
- [25.5.iii](https://dlmf.nist.gov/25.5.iii): [`DLMF.Zeta.keyholeLoopIntegral`](DLMF/Zeta/IntegralReps.lean#L1548) (definition). The loop description of 25.5.20–25.5.21.
- [25.6.iii](https://dlmf.nist.gov/25.6.iii) p2 (Basu and Apostol): excluded: bibliographic.
- [§25.7](https://dlmf.nist.gov/25.7) (Integrals): only a bibliographic pointer (Prudnikov et
  al.); excluded: bibliographic.
- [25.8](https://dlmf.nist.gov/25.8) p2: bibliographic pointers; excluded: bibliographic.
- [25.9](https://dlmf.nist.gov/25.9) p1–p2: the hypotheses of 25.9.1 and 25.9.3 are encoded;
  p3 (Berry–Keating, Paris–Cang, Paris–Kaminski) is bibliographic (excluded).
- [25.10.i](https://dlmf.nist.gov/25.10.i): [`DLMF.Zeta.riemannZeta_ne_zero_of_re_nonpos`](DLMF/Zeta/Zeros.lean#L52) (proved); [`DLMF.Zeta.riemannZeta_conj_eq_zero_iff`](DLMF/Zeta/Zeros.lean#L92) (proved); [`DLMF.Zeta.riemannZeta_one_sub_eq_zero_iff`](DLMF/Zeta/Zeros.lean#L98) (proved); [`DLMF.Zeta.criticalStripZeros`](DLMF/Zeta/Zeros.lean#L142) (definition); [`DLMF.Zeta.norm_riemannSiegelZ`](DLMF/Zeta/Zeros.lean#L212) (proved); [`DLMF.Zeta.riemannSiegelZ_eq_zero_iff`](DLMF/Zeta/Zeros.lean#L217) (proved); [`DLMF.Zeta.riemannSiegelZ_sign_changes`](DLMF/Zeta/Zeros.lean#L223) (admitted); [`DLMF.Zeta.exists_riemannZeta_critical_line_zero_gt`](DLMF/Zeta/Zeros.lean#L229) (proved from admissions); [`DLMF.Zeta.criticalStripZeros_infinite`](DLMF/Zeta/Zeros.lean#L243) (proved from admissions). Mathlib: `riemannZeta_ne_zero_of_one_le_re` (no zeros for Re s ≥ 1), `riemannZeta_neg_two_mul_nat_add_one` (trivial zeros), `hardyZ_eq_zero_iff`, `abs_hardyZ`, `continuous_hardyZ`; the Riemann hypothesis: conjecture: not acquired (Mathlib `RiemannHypothesis` recorded as the statement only). The nonvanishing for Re s ≤ 0 away from the trivial zeros, the two symmetries of the zeros in the critical strip, |Z| = |ζ| and the zero correspondence are proved; Hardy's theorem (Z changes sign infinitely often) is admitted, and from it the infinitude of zeros on the critical line and in the critical strip is proved.
- [25.10.ii](https://dlmf.nist.gov/25.10.ii): [`DLMF.Zeta.riemannZeroCount`](DLMF/Zeta/Zeros.lean#L272) (definition); [`DLMF.Zeta.criticalLineZeroCount`](DLMF/Zeta/Zeros.lean#L278) (definition); [`DLMF.Zeta.eventually_criticalLineZeroCount_gt`](DLMF/Zeta/Zeros.lean#L308) (admitted). N(T) and N₀(T) count zeros with multiplicity (finiteness proved: `finite_criticalStripZerosBelow`). p3: "the first ten billion zeros lie on the critical line" is a computational result, excluded: numerical; "more than 41% of the zeros lie on the critical line" (Bui, Conrey and Young 2011) is acquired as the eventual inequality N₀(T) > 0.41 N(T) (admitted). p2 ("Riemann also developed a technique for determining further terms") and p4 (Berry 1995) are informal/bibliographic (excluded).

## Validation (part A)

- `lake build` of `DLMF.Zeta.{Riemann, Reflection, IntegralReps, IntegerArguments, Sums,
  Asymptotics, Zeros, MathlibCoverage}` and `DLMF.Constants.Dirichlet` succeeds; the strict
  check `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false` of every changed file
  reports no errors and no warnings other than `declaration uses 'sorry'`.
- Admissions (`grep -c '\bsorry\b'`): Riemann 6, Reflection 1, IntegralReps 20,
  IntegerArguments 13, Sums 7, Asymptotics 1, Zeros 4 (52). No helper declaration (prefix
  `z25a_`) contains `sorry`; no axioms, no `native_decide`.
- `#print axioms` on all 28 proved tagged theorems and the helper lemmas: 21 depend only on
  `[propext, Classical.choice, Quot.sound]`; the seven marked "proved from admissions"
  (25.2.3 printed form, 25.2.10, 25.6.13, 25.6.14, 25.9.3, and the two infinitude results of
  §25.10(i)) add `sorryAx`.


# Part B: §§25.11–25.21 (ACQ25B)

Part B covers the Hurwitz zeta function (§25.11), polylogarithms (§25.12), the periodic zeta
function (§25.13), Lerch's transcendent (§25.14) and Dirichlet L-functions (§25.15). §§25.16–25.17
(applications) and §§25.18–25.21 (computation, tables, approximations, software) are excluded
(see below). The in-scope items are 85 numbered equations (25.11: 44, the number 25.11.36 being
retired; 25.12: 16; 25.13: 3; 25.14: 12 including 25.14.3_1–25.14.3_3; 25.15: 10) and 6 prose
items (25.11.i, 25.12.ii, 25.13, 25.14.i, 25.15.i, 25.15.ii); all 91 are covered by at least one
Lean declaration or Mathlib pointer. Modules, in import order:
[DLMF/Zeta/Hurwitz.lean](DLMF/Zeta/Hurwitz.lean) →
[DLMF/Zeta/HurwitzIntegrals.lean](DLMF/Zeta/HurwitzIntegrals.lean) (also imports part A's
`IntegralReps` for the keyhole loop); [DLMF/Zeta/Polylog.lean](DLMF/Zeta/Polylog.lean)
(imports `Hurwitz` and `DLMF.Polylog.Dilog`) → [DLMF/Zeta/Periodic.lean](DLMF/Zeta/Periodic.lean),
[DLMF/Zeta/Lerch.lean](DLMF/Zeta/Lerch.lean); [DLMF/Zeta/DirichletL.lean](DLMF/Zeta/DirichletL.lean)
(imports `Hurwitz`); [DLMF/Zeta/MathlibCoverageB.lean](DLMF/Zeta/MathlibCoverageB.lean) (20
`dlmf_upstream` pointers). Part B has 105 tagged declarations: 6 definitions, 13 proved
theorems, 14 proved from admissions and **72 direct admissions** (`grep -c '\bsorry\b'`: Hurwitz
24, HurwitzIntegrals 20, Polylog 13, Periodic 1, Lerch 10, DirichletL 4), plus 18 untagged
helpers (prefix `z25b_` and a few auxiliary lemmas, none containing `sorry`). Existing
declarations were tagged in place: `DLMF.Constants.catalanConstant` (25.11.E40),
`DLMF.Polylog.polylogSeries` (25.12.E10), `polylogSeries_one_eq_zeta` (25.12.ii),
`polylogSeries_exp_eq_expZeta` (25.13), `Real.dilog` and `polylogSeries_two_ofReal_eq_dilog`
(25.12.E2), `Real.dilog_add_dilog_div_sub_one` (25.12.E3), `Real.dilog_add_dilog_recip`
(25.12.E4); the tags 25.11.E11, E12, E25 in DLMF/Gamma/PolygammaHurwitz.lean and 25.12.E6 in
DLMF/Polylog/Dilog.lean already existed.

## Domains, conventions and source corrections (part B)

- **Hurwitz zeta.** Mathlib's `hurwitzZeta (a : UnitAddCircle) s` has its parameter in ℝ/ℤ, so it
  is DLMF's ζ(s, a) only for 0 < a ≤ 1. Statements whose DLMF range lies in (0, 1] use it; all
  others use the project's `DLMF.Confluent.hurwitzZetaComplex s a` (complex a ∉ {0, -1, -2, …},
  defined by an Euler–Maclaurin limit in DLMF/IncompleteGamma/ZerosIntegrals.lean). The
  existence of that limit, its holomorphy and residue, and the bridge to Mathlib for
  0 < a ≤ 1 are admitted; 25.11.2–25.11.4 and 25.11.12 are derived from them.
- **Polylogarithm and Lerch's transcendent.** `DLMF.Zeta.polylog s z` (complex order) and
  `DLMF.Zeta.lerchPhi z s a` are the analytic continuations of their series to z ∈ ℂ \ [1, ∞),
  chosen by classical choice from an admitted existence theorem (uniqueness on the connected
  slit domain makes the choice canonical); on the unit circle they are the series where it
  converges. For natural order the project's `DLMF.Polylog.polylogSeries` is identified with
  `polylog` (proved from admissions). The periodic zeta function F(x, s) is Mathlib's
  `HurwitzZeta.expZeta`, the L-functions Mathlib's `DirichletCharacter.LFunction`, the Gauss sum
  Mathlib's `gaussSum χ ZMod.stdAddChar`.
- Conditionally convergent series and improper integrals are stated as limits of partial sums
  or of ∫_0^X; integrals ∫_0^a with complex a are along the segment [0, a]; asymptotic
  expansions (25.11.43–25.11.45) are stated for each truncation order with an O-remainder in the
  sector |ph a| ≤ π - δ. The loop integral 25.11.30 uses part A's keyhole contour
  `keyholeLoopIntegral` of radius 0 < δ < 2π.
- Totalization and implicit conditions. Lean's junk values (Γ = 0 at its poles, ζ(1), x/0 = 0)
  are never used: 25.11.16 also excludes s = -1, -2, …; 25.11.17 and 25.11.41 exclude s = 0;
  25.11.31 and 25.11.35 exclude the removable singularity s = 1; 25.13.2 excludes integer s ≥ 2
  (stated for all other s, stronger than DLMF's Re s > 1); 25.15.3, 25.15.6 and 25.15.10 need
  k ≥ 2 (for k = 1 the printed sums do not match L(s, χ₁) = ζ(s)); 25.12.12 and 25.14.3_1 add
  z ≠ 0 and z ∉ [1, ∞), where the principal ln z is used.
- **Erratum 25.11.23** (corrected in Lean). The first term printed as
  -B_{2n} ln 3/(8n√3 (3^{2n-1} - 1)) … has denominator 8n√3·3^{2n-1}: with mpmath, for
  n = 1, …, 4, (printed - true)/t₁ = -1/3^{2n-1} where t₁ is the first term, and the corrected
  formula agrees to working precision; the corrected form is also what 25.11.21 gives at h = 1, k = 3.
- **Branch in 25.12.13** (corrected). With principal ln z the printed
  Li_s(z) + e^{πis} Li_s(1/z) = (2π)^s e^{πis/2}/Γ(s) ζ(1 - s, ln z/(2πi)) fails for Im z < 0
  (mpmath: s = 2.5 + 0.2i, z = 0.5 - 0.9i; s = 0.7 + 0.3i, z = -0.3 - 0.4i; s = 2, z = -2 - 0.5i);
  it holds with 0 < ph z < 2π, i.e. with the parameter 1/2 + ln(-z)/(2πi), which is how it is
  stated (z ∉ [0, ∞)).
- **25.11.37** with principal logarithms of complex Gamma values holds only modulo 2πi (n = 2,
  a = 4 - 9i); it is stated exactly for real a ≥ 1 and in exponentiated form for Re a ≥ 1.
- **25.14.7** is printed without conditions. It holds for 0 < Re a < 1, 0 < |z| < 1 and fails
  for a = 1.6 + 0.2i, a = -0.4 + 0.3i, a = 1, on |z| = 1 (z = 0.6 - 0.8i) and in mixed cases
  with |z| > 1; it is stated on the verified domain.
- Numerical checks (mpmath, scripts in the acquisition scratch area) of every §§25.11–25.15
  formula at real and complex points agree to working precision, except the items above; the
  Euler–Maclaurin forms 25.11.5, 25.11.6, 25.11.19, 25.11.20 and the sawtooth integral 25.11.26
  were checked by exact cell-by-cell integration to 1e-10–1e-17.

## Numbered formulas and prose items (part B)

## [§25.11 Hurwitz Zeta Function](https://dlmf.nist.gov/25.11)

- [25.11.E1](https://dlmf.nist.gov/25.11.E1): [`DLMF.Zeta.hasSum_hurwitzZetaComplex`](DLMF/Zeta/Hurwitz.lean#L159) (proved); Mathlib: [`HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re#doc). Re s > 1, complex a ∉ {0, -1, …}; Mathlib pointer (real 0 < a ≤ 1) in DLMF/Core/UpstreamElementary.lean.
- [25.11.E2](https://dlmf.nist.gov/25.11.E2): [`DLMF.Zeta.hurwitzZetaComplex_one`](DLMF/Zeta/Hurwitz.lean#L170) (proved); Mathlib: [`HurwitzZeta.hurwitzZeta_zero`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=HurwitzZeta.hurwitzZeta_zero#doc). ζ(s, 1) = ζ(s) for s ≠ 1; from the admitted bridge hurwitzZetaComplex_mathlib.
- [25.11.E3](https://dlmf.nist.gov/25.11.E3): [`DLMF.Zeta.hurwitzZetaComplex_eq_add_one`](DLMF/Zeta/Hurwitz.lean#L179) (proved). s ≠ 1, complex a ∉ {0, -1, …}; proved from the admitted limit (tendsto_hurwitzZetaComplex).
- [25.11.E4](https://dlmf.nist.gov/25.11.E4): [`DLMF.Zeta.hurwitzZetaComplex_eq_add_nat`](DLMF/Zeta/Hurwitz.lean#L189) (proved). s ≠ 1, all m ≥ 0 (also m = 0), by induction from 25.11.3.
- [25.11.E5](https://dlmf.nist.gov/25.11.E5): [`DLMF.Zeta.hurwitzZetaComplex_eulerMaclaurin_one`](DLMF/Zeta/Hurwitz.lean#L400) (proved). Re s > 0, s ≠ 1, real a > 0, N ≥ 0; x - ⌊x⌋ = Int.fract x; checked numerically (complex s, N = 0, 2) to 1e-17.
- [25.11.E6](https://dlmf.nist.gov/25.11.E6): [`DLMF.Zeta.hurwitzZetaComplex_eulerMaclaurin_two`](DLMF/Zeta/Hurwitz.lean#L583) (proved). Re s > -2, s ≠ 1, a > 0; B̃₂ is the project's periodic Bernoulli function; checked numerically to 1e-20.
- [25.11.E7](https://dlmf.nist.gov/25.11.E7): [`DLMF.Zeta.hurwitzZetaComplex_eulerMaclaurin`](DLMF/Zeta/Hurwitz.lean#L635) (proved). n ≥ 1, N ≥ 0, Re s > -2n, s ≠ 1; generalized binomial coefficient Ring.choose.
- [25.11.E8](https://dlmf.nist.gov/25.11.E8): [`DLMF.Zeta.hurwitzZeta_half_eq_add_alternating`](DLMF/Zeta/Hurwitz.lean#L698) (proved). Re s > 0, s ≠ 1, 0 < a ≤ 1 (Mathlib hurwitzZeta); the conditionally convergent alternating series as a limit of partial sums.
- [25.11.E9](https://dlmf.nist.gov/25.11.E9): [`DLMF.Zeta.hurwitzZeta_one_sub_fourier`](DLMF/Zeta/Hurwitz.lean#L770) (proved). 0 < a < 1 with Re s > 0, or a = 1 with Re s > 1; the cosine series as a limit of partial sums, with the Γ factor moved to the left (2Γ(s) ≠ 0 in that range).
- [25.11.E10](https://dlmf.nist.gov/25.11.E10): [`DLMF.Zeta.hasSum_hurwitzZetaComplex_taylor`](DLMF/Zeta/Hurwitz.lean#L829) (admitted). s ≠ 1, |a - 1| < 1.
- [25.11.E11](https://dlmf.nist.gov/25.11.E11): [`DLMF.Zeta.hurwitzZeta_one_half`](DLMF/Zeta/Hurwitz.lean#L911) (proved); [`DLMF.Gamma.hurwitzZeta_one_half_nat`](DLMF/Gamma/PolygammaHurwitz.lean#L45) (proved). All s ≠ 1; the existing case s = n + 1 ≥ 2 is proved in DLMF.Gamma.
- [25.11.E12](https://dlmf.nist.gov/25.11.E12): [`DLMF.Zeta.hurwitzZetaComplex_nat_eq_polygamma`](DLMF/Zeta/Hurwitz.lean#L919) (proved); [`DLMF.Gamma.polygamma_eq_hurwitzZeta`](DLMF/Gamma/PolygammaHurwitz.lean#L31) (proved). n ≥ 1, complex Re a > 0, proved from 25.11.1 (admitted); real 0 < a ≤ 1 fully proved in DLMF.Gamma.
- [25.11.E13](https://dlmf.nist.gov/25.11.E13): [`DLMF.Zeta.hurwitzZetaComplex_zero`](DLMF/Zeta/Hurwitz.lean#L1052) (proved). Re a > 0; [`DLMF.Zeta.r25b_hurwitzZeta_zero`](DLMF/Zeta/Hurwitz.lean#L1069) (proved).
- [25.11.E14](https://dlmf.nist.gov/25.11.E14): [`DLMF.Zeta.hurwitzZetaComplex_neg_nat`](DLMF/Zeta/Hurwitz.lean#L1094) (proved); Mathlib: [`HurwitzZeta.hurwitzZeta_neg_nat`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=HurwitzZeta.hurwitzZeta_neg_nat#doc). All n ≥ 0, Re a > 0; Mathlib has real 0 ≤ a ≤ 1.
- [25.11.E15](https://dlmf.nist.gov/25.11.E15): [`DLMF.Zeta.hurwitzZetaComplex_mul`](DLMF/Zeta/Hurwitz.lean#L1121) (proved). k ≥ 1, s ≠ 1, Re a > 0.
- [25.11.E16](https://dlmf.nist.gov/25.11.E16): [`DLMF.Zeta.hurwitzZeta_one_sub_rat`](DLMF/Zeta/Hurwitz.lean#L1177) (proved). 1 ≤ h ≤ k; besides DLMF's s ≠ 0, 1 also s ≠ -1, -2, … (implicit condition: Γ(s) has a pole there, the printed right side is a limit and Lean's Γ(-m) = 0 would make the literal identity false).
- [25.11.E17](https://dlmf.nist.gov/25.11.E17): [`DLMF.Zeta.hasDerivAt_hurwitzZetaComplex_param`](DLMF/Zeta/Hurwitz.lean#L1259) (proved). HasDerivAt in a, s ≠ 0, 1 (at s = 0 the right side involves Lean's junk ζ(1, a)), Re a > 0.
- [25.11.E18](https://dlmf.nist.gov/25.11.E18): [`DLMF.Zeta.deriv_hurwitzZetaComplex_zero`](DLMF/Zeta/Hurwitz.lean#L1472) (proved). Real a > 0, real ln Γ(a).
- [25.11.E19](https://dlmf.nist.gov/25.11.E19): [`DLMF.Zeta.deriv_hurwitzZetaComplex_eulerMaclaurin`](DLMF/Zeta/Hurwitz.lean#L1379) (proved). Re s > -1, s ≠ 1, a > 0; checked numerically to 1e-10.
- [25.11.E20](https://dlmf.nist.gov/25.11.E20): [`DLMF.Zeta.iteratedDeriv_hurwitzZetaComplex`](DLMF/Zeta/Hurwitz.lean#L1553) (admitted). k ≥ 1, Re s > -1, s ≠ 1, a > 0; checked numerically for k = 1, 2 to 1e-10.
- [25.11.E21](https://dlmf.nist.gov/25.11.E21): [`DLMF.Zeta.deriv_hurwitzZeta_one_sub_two_mul_rat`](DLMF/Zeta/Hurwitz.lean#L1571) (admitted). 1 ≤ h ≤ k, n ≥ 1; ψ = digamma.
- [25.11.E22](https://dlmf.nist.gov/25.11.E22): [`DLMF.Zeta.deriv_hurwitzZeta_one_sub_two_mul_half`](DLMF/Zeta/Hurwitz.lean#L1588) (proved). n ≥ 1.
- [25.11.E23](https://dlmf.nist.gov/25.11.E23): [`DLMF.Zeta.deriv_hurwitzZeta_one_sub_two_mul_third`](DLMF/Zeta/Hurwitz.lean#L1615) (admitted). **Corrected** (DLMF erratum): the first denominator is 8n√3·3^{2n-1}, not 8n√3(3^{2n-1} - 1); see the corrections section.
- [25.11.E24](https://dlmf.nist.gov/25.11.E24): [`DLMF.Zeta.sum_deriv_hurwitzZeta_rat`](DLMF/Zeta/Hurwitz.lean#L1631) (proved). s ≠ 1, k ≥ 1.
- [25.11.E25](https://dlmf.nist.gov/25.11.E25): [`DLMF.Zeta.hurwitzZetaComplex_eq_integral`](DLMF/Zeta/HurwitzIntegrals.lean#L49) (proved); [`DLMF.Gamma.Gamma_mul_hurwitzZeta_eq_integral`](DLMF/Gamma/PolygammaHurwitz.lean#L131) (proved). Re s > 1, complex Re a > 0; real 0 < a ≤ 1 proved in DLMF.Gamma.
- [25.11.E26](https://dlmf.nist.gov/25.11.E26): [`DLMF.Zeta.tendsto_hurwitzZeta_sawtooth_integral`](DLMF/Zeta/HurwitzIntegrals.lean#L65) (admitted). -1 < Re s < 0, 0 < a ≤ 1; conditionally convergent, as limit of ∫_{-a}^X; checked numerically to 1e-14.
- [25.11.E27](https://dlmf.nist.gov/25.11.E27): [`DLMF.Zeta.hurwitzZetaComplex_eq_integral_bernoulli`](DLMF/Zeta/HurwitzIntegrals.lean#L255) (proved). s ≠ 1, Re s > -1, Re a > 0; checked numerically to 1e-12.
- [25.11.E28](https://dlmf.nist.gov/25.11.E28): [`DLMF.Zeta.hurwitzZetaComplex_eq_integral_bernoulli_sub`](DLMF/Zeta/HurwitzIntegrals.lean#L298) (admitted). n ≥ 0, s ≠ 1, Re s > -(2n+1), Re a > 0; checked numerically to 1e-12.
- [25.11.E29](https://dlmf.nist.gov/25.11.E29): [`DLMF.Zeta.hurwitzZetaComplex_hermite`](DLMF/Zeta/HurwitzIntegrals.lean#L312) (admitted). Hermite's formula, s ≠ 1, Re a > 0; principal arctan and power.
- [25.11.E30](https://dlmf.nist.gov/25.11.E30): [`DLMF.Zeta.hurwitzZetaComplex_eq_loop_integral`](DLMF/Zeta/HurwitzIntegrals.lean#L323) (admitted). s ∉ {1, 2, …}, Re a > 0; loop = keyhole of radius 0 < δ < 2π (DLMF.Zeta.keyholeLoopIntegral, part A); independence of the loop not formalized.
- [25.11.E31](https://dlmf.nist.gov/25.11.E31): [`DLMF.Zeta.integral_cosh_eq_hurwitzZetaComplex_sub`](DLMF/Zeta/HurwitzIntegrals.lean#L442) (proved). Re s > 0, Re a > -1, and s ≠ 1 (removable singularity of the difference; Lean's junk value at the pole).
- [25.11.E32](https://dlmf.nist.gov/25.11.E32): [`DLMF.Zeta.integral_pow_mul_digamma`](DLMF/Zeta/HurwitzIntegrals.lean#L503) (admitted). n ≥ 1, Re a > 0, along the segment [0, a]; H_k = Mathlib harmonic.
- [25.11.E33](https://dlmf.nist.gov/25.11.E33): Mathlib: [`harmonic`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=harmonic#doc). Hₙ = Mathlib harmonic (exact, as a rational).
- [25.11.E34](https://dlmf.nist.gov/25.11.E34): [`DLMF.Zeta.integral_deriv_hurwitzZetaComplex`](DLMF/Zeta/HurwitzIntegrals.lean#L519) (admitted). n ≥ 1, Re a > 0, along [0, a].
- [25.11.E35](https://dlmf.nist.gov/25.11.E35): [`DLMF.Zeta.tendsto_alternating_hurwitz`](DLMF/Zeta/HurwitzIntegrals.lean#L531) (admitted); [`DLMF.Zeta.tendsto_integral_alternating_hurwitz`](DLMF/Zeta/HurwitzIntegrals.lean#L541) (admitted). Series and integral forms as limits; Re a > 0, Re s > 0, or Re a = 0, Im a ≠ 0, 0 < Re s < 1; s ≠ 1 added (removable singularity).
- [25.11.E36](https://dlmf.nist.gov/25.11.E36): excluded: removed from the DLMF (equation number no longer in use).
- [25.11.E37](https://dlmf.nist.gov/25.11.E37): [`DLMF.Zeta.hasSum_hurwitzZeta_log_gamma`](DLMF/Zeta/HurwitzIntegrals.lean#L554) (admitted); [`DLMF.Zeta.exp_tsum_hurwitzZeta_eq_prod_gamma`](DLMF/Zeta/HurwitzIntegrals.lean#L563) (admitted). Two forms: exact with principal logarithms for real a ≥ 1, and exponentiated form for complex Re a ≥ 1 (with principal logs the printed identity holds only mod 2πi, e.g. n = 2, a = 4 - 9i).
- [25.11.E38](https://dlmf.nist.gov/25.11.E38): [`DLMF.Zeta.hasSum_hurwitzZeta_polygamma_sub`](DLMF/Zeta/HurwitzIntegrals.lean#L589) (proved). n ≥ 1, Re a > 0, |z| < |a|.
- [25.11.E39](https://dlmf.nist.gov/25.11.E39): [`DLMF.Zeta.hasSum_hurwitzZeta_three_quarters`](DLMF/Zeta/HurwitzIntegrals.lean#L638) (proved). Exact value with G = catalanConstant.
- [25.11.E40](https://dlmf.nist.gov/25.11.E40): [`DLMF.Constants.catalanConstant`](DLMF/Constants/Catalan.lean#L30) (definition). Definition G = ∑ (-1)^k/(2k+1)² (tagged in place); the decimal value of G: excluded: numerical.
- [25.11.E41](https://dlmf.nist.gov/25.11.E41): [`DLMF.Zeta.hurwitzZetaComplex_add_one_isBigO`](DLMF/Zeta/HurwitzIntegrals.lean#L665) (proved). a → 0 complex, s ≠ 1; s ≠ 0 also assumed (implicit: at s = 0 the coefficient s ζ(s+1) is a limit; Lean's junk ζ(1) breaks the literal form).
- [25.11.E42](https://dlmf.nist.gov/25.11.E42): [`DLMF.Zeta.tendstoUniformlyOn_hurwitzZetaComplex_im`](DLMF/Zeta/HurwitzIntegrals.lean#L712) (admitted). Re s > 1, uniformly for α ∈ [0, A], as β → ±∞ (cocompact ℝ).
- [25.11.E43](https://dlmf.nist.gov/25.11.E43): [`DLMF.Zeta.hurwitzZetaComplex_asymptotic`](DLMF/Zeta/HurwitzIntegrals.lean#L723) (admitted). For each truncation order, remainder O of the next power as a → ∞ in |ph a| ≤ π - δ (z25b_sector), s ≠ 1.
- [25.11.E44](https://dlmf.nist.gov/25.11.E44): [`DLMF.Zeta.deriv_hurwitzZetaComplex_neg_one_asymptotic`](DLMF/Zeta/HurwitzIntegrals.lean#L735) (admitted). As 25.11.43.
- [25.11.E45](https://dlmf.nist.gov/25.11.E45): [`DLMF.Zeta.deriv_hurwitzZetaComplex_neg_two_asymptotic`](DLMF/Zeta/HurwitzIntegrals.lean#L746) (admitted). As 25.11.43.
- [25.11.i](https://dlmf.nist.gov/25.11.i): [`DLMF.Zeta.tendsto_hurwitzZetaComplex`](DLMF/Zeta/Hurwitz.lean#L124) (proved); [`DLMF.Zeta.differentiableAt_hurwitzZetaComplex`](DLMF/Zeta/Hurwitz.lean#L139) (proved); [`DLMF.Zeta.hurwitzZetaComplex_residue_one`](DLMF/Zeta/Hurwitz.lean#L146) (proved); [`DLMF.Zeta.differentiableOn_hurwitzZetaComplex_param`](DLMF/Zeta/Hurwitz.lean#L152) (proved); Mathlib: [`HurwitzZeta.differentiableAt_hurwitzZeta`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=HurwitzZeta.differentiableAt_hurwitzZeta#doc); Mathlib: [`HurwitzZeta.hurwitzZeta_residue_one`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=HurwitzZeta.hurwitzZeta_residue_one#doc). ζ(s, a) for complex a ∉ {0, -1, -2, …} is DLMF.Confluent.hurwitzZetaComplex (Euler–Maclaurin limit); existence of the limit, holomorphy in s ≠ 1, residue 1 at s = 1 and holomorphy in a admitted. Mathlib covers real 0 < a ≤ 1 (parameter in ℝ/ℤ).

## [§25.12 Polylogarithms](https://dlmf.nist.gov/25.12)

- [25.12.E1](https://dlmf.nist.gov/25.12.E1): [`DLMF.Zeta.hasSum_dilog`](DLMF/Zeta/Polylog.lean#L324) (proved). Proved from admissions, |z| ≤ 1.
- [25.12.E2](https://dlmf.nist.gov/25.12.E2): [`DLMF.Zeta.polylog_two_eq_integral`](DLMF/Zeta/Polylog.lean#L334) (proved); [`DLMF.Polylog.Real.dilog`](DLMF/Polylog/Dilog.lean#L57) (definition); [`DLMF.Polylog.polylogSeries_two_ofReal_eq_dilog`](DLMF/Polylog/Dilog.lean#L177) (proved). z ∈ ℂ \ (1, ∞); real x ≤ 1 integral form Real.dilog (tagged in place).
- [25.12.E3](https://dlmf.nist.gov/25.12.E3): [`DLMF.Zeta.polylog_two_add_polylog_two_div_sub_one`](DLMF/Zeta/Polylog.lean#L391) (proved); [`DLMF.Polylog.Real.dilog_add_dilog_div_sub_one`](DLMF/Polylog/Dilog.lean#L288) (proved). z ∈ ℂ \ [1, ∞); real x < 1 proved (tagged in place).
- [25.12.E4](https://dlmf.nist.gov/25.12.E4): [`DLMF.Zeta.polylog_two_add_polylog_two_inv`](DLMF/Zeta/Polylog.lean#L444) (proved); [`DLMF.Polylog.Real.dilog_add_dilog_recip`](DLMF/Polylog/Dilog.lean#L326) (proved). z ∈ ℂ \ [0, ∞); real x < 0 proved (tagged in place).
- [25.12.E5](https://dlmf.nist.gov/25.12.E5): [`DLMF.Zeta.polylog_two_pow`](DLMF/Zeta/Polylog.lean#L502) (proved). m ≥ 1, |z| < 1.
- [25.12.E6](https://dlmf.nist.gov/25.12.E6): [`DLMF.Zeta.polylog_two_add_polylog_two_one_sub`](DLMF/Zeta/Polylog.lean#L583) (proved); [`DLMF.Polylog.Real.dilog_add_dilog_one_sub`](DLMF/Polylog/Dilog.lean#L231) (proved). Complex z ∉ (-∞, 0] ∪ [1, ∞) admitted (stronger than the real case; checked numerically); real 0 < x < 1 proved (existing).
- [25.12.E7](https://dlmf.nist.gov/25.12.E7): [`DLMF.Zeta.polylog_two_exp_mul_I`](DLMF/Zeta/Polylog.lean#L635) (proved). All real θ; proved from admissions.
- [25.12.E8](https://dlmf.nist.gov/25.12.E8): [`DLMF.Zeta.hasSum_cos_div_sq`](DLMF/Zeta/Polylog.lean#L659) (proved). 0 ≤ θ ≤ 2π; fully proved from Mathlib's Bernoulli Fourier series.
- [25.12.E9](https://dlmf.nist.gov/25.12.E9): [`DLMF.Zeta.hasSum_sin_div_sq`](DLMF/Zeta/Polylog.lean#L725) (proved). 0 ≤ θ ≤ 2π.
- [25.12.E10](https://dlmf.nist.gov/25.12.E10): [`DLMF.Zeta.polylogSeriesC`](DLMF/Zeta/Polylog.lean#L63) (definition); [`DLMF.Zeta.hasSum_polylog`](DLMF/Zeta/Polylog.lean#L166) (proved); [`DLMF.Zeta.hasSum_polylog_of_norm_eq_one`](DLMF/Zeta/Polylog.lean#L272) (proved); [`DLMF.Polylog.polylogSeries`](DLMF/Polylog/Basic.lean#L31) (definition). polylogSeriesC s z = ∑ z^n/n^s (complex order); HasSum for |z| < 1 (proved from admissions) and |z| = 1, Re s > 1 (admitted); natural order in DLMF.Polylog.
- [25.12.E11](https://dlmf.nist.gov/25.12.E11): [`DLMF.Zeta.polylog_eq_integral`](DLMF/Zeta/Polylog.lean#L765) (proved). Re s > 0 for z ∈ ℂ \ [1, ∞), Re s > 1 for z = 1.
- [25.12.E12](https://dlmf.nist.gov/25.12.E12): [`DLMF.Zeta.hasSum_polylog_log`](DLMF/Zeta/Polylog.lean#L786) (admitted). Series in ln z, |ln z| < 2π, s ∉ {1, 2, …}; z ∈ ℂ \ [1, ∞), z ≠ 0 (the principal branch is undefined on the cut).
- [25.12.E13](https://dlmf.nist.gov/25.12.E13): [`DLMF.Zeta.polylog_add_exp_mul_polylog_inv`](DLMF/Zeta/Polylog.lean#L797) (admitted). **Branch corrected**: with principal ln z the printed formula fails for Im z < 0; stated with 0 < ph z < 2π, i.e. 1/2 + ln(-z)/(2πi); s ≠ 0.
- [25.12.E14](https://dlmf.nist.gov/25.12.E14): [`DLMF.Zeta.fermiDiracF`](DLMF/Zeta/Polylog.lean#L810) (definition). Fermi–Dirac integral F_s(x), real s > -1.
- [25.12.E15](https://dlmf.nist.gov/25.12.E15): [`DLMF.Zeta.boseEinsteinG`](DLMF/Zeta/Polylog.lean#L816) (definition). Bose–Einstein integral G_s(x), s > -1, x < 0 or s > 0, x ≤ 0.
- [25.12.E16](https://dlmf.nist.gov/25.12.E16): [`DLMF.Zeta.fermiDiracF_eq_polylog`](DLMF/Zeta/Polylog.lean#L822) (proved); [`DLMF.Zeta.boseEinsteinG_eq_polylog`](DLMF/Zeta/Polylog.lean#L847) (proved). Two statements (F_s and G_s).
- [25.12.ii](https://dlmf.nist.gov/25.12.ii): [`DLMF.Zeta.polylog`](DLMF/Zeta/Polylog.lean#L70) (definition); [`DLMF.Zeta.summable_polylogSeriesC_of_norm_le_one`](DLMF/Zeta/Polylog.lean#L102) (proved); [`DLMF.Zeta.exists_polylog_continuation`](DLMF/Zeta/Polylog.lean#L121) (proved); [`DLMF.Zeta.analyticOnNhd_polylog`](DLMF/Zeta/Polylog.lean#L175) (proved); [`DLMF.Zeta.polylog_one`](DLMF/Zeta/Polylog.lean#L287) (proved); [`DLMF.Polylog.polylogSeries_one_eq_zeta`](DLMF/Polylog/Basic.lean#L85) (proved). polylog s z: the analytic continuation of the series to ℂ \ [1, ∞), chosen classically (z25b_slitContinuation); its existence admitted. Convergence on |z| ≤ 1 for Re s > 1 and Li_s(1) = ζ(s) (Re s > 1) proved.

## [§25.13 Periodic Zeta Function](https://dlmf.nist.gov/25.13)

- [25.13.E1](https://dlmf.nist.gov/25.13.E1): [`DLMF.Zeta.tendsto_expZeta_partialSum`](DLMF/Zeta/Periodic.lean#L35) (proved); Mathlib: [`HurwitzZeta.hasSum_expZeta_of_one_lt_re`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=HurwitzZeta.hasSum_expZeta_of_one_lt_re#doc). Conditional range 0 < Re s, x ∉ ℤ as a limit of partial sums (admitted); Re s > 1 in Mathlib.
- [25.13.E2](https://dlmf.nist.gov/25.13.E2): [`DLMF.Zeta.expZeta_eq_hurwitzZeta`](DLMF/Zeta/Periodic.lean#L77) (proved); Mathlib: [`HurwitzZeta.expZeta_one_sub`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=HurwitzZeta.expZeta_one_sub#doc). Stronger than DLMF: every real x and every s ∉ ℕ (at s = 2, 3, … the printed formula is a limit); proved from Mathlib.
- [25.13.E3](https://dlmf.nist.gov/25.13.E3): [`DLMF.Zeta.hurwitzZeta_one_sub_eq_expZeta`](DLMF/Zeta/Periodic.lean#L97) (proved); Mathlib: [`HurwitzZeta.hurwitzZeta_one_sub`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=HurwitzZeta.hurwitzZeta_one_sub#doc). Re s > 0 for 0 < x < 1, Re s > 1 for x = 1; proved from Mathlib.
- [25.13](https://dlmf.nist.gov/25.13): [`DLMF.Zeta.polylog_exp_eq_expZeta`](DLMF/Zeta/Periodic.lean#L45) (proved); [`DLMF.Zeta.expZeta_add_one`](DLMF/Zeta/Periodic.lean#L62) (proved); [`DLMF.Zeta.expZeta_intCast`](DLMF/Zeta/Periodic.lean#L68) (proved); [`DLMF.Polylog.polylogSeries_exp_eq_expZeta`](DLMF/Polylog/Basic.lean#L180) (proved); Mathlib: [`HurwitzZeta.expZeta`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=HurwitzZeta.expZeta#doc); Mathlib: [`HurwitzZeta.expZeta_zero`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=HurwitzZeta.expZeta_zero#doc). F(x, s) is Mathlib's HurwitzZeta.expZeta; periodicity, integer x, and F(x, s) = Li_s(e^{2πix}) for Re s > 1 (proved from admissions; natural s ≥ 2 proved in DLMF.Polylog).

## [§25.14 Lerch's Transcendent](https://dlmf.nist.gov/25.14)

- [25.14.E1](https://dlmf.nist.gov/25.14.E1): [`DLMF.Zeta.lerchPhiSeries`](DLMF/Zeta/Lerch.lean#L44) (definition); [`DLMF.Zeta.hasSum_lerchPhi`](DLMF/Zeta/Lerch.lean#L111) (proved); [`DLMF.Zeta.hasSum_lerchPhi_of_norm_eq_one`](DLMF/Zeta/Lerch.lean#L119) (proved). lerchPhiSeries; HasSum for |z| < 1 (proved from admissions), |z| = 1 with Re s > 1 (admitted).
- [25.14.E2](https://dlmf.nist.gov/25.14.E2): [`DLMF.Zeta.hurwitzZetaComplex_eq_lerchPhi`](DLMF/Zeta/Lerch.lean#L150) (proved). Proved from admissions.
- [25.14.E3](https://dlmf.nist.gov/25.14.E3): [`DLMF.Zeta.polylog_eq_mul_lerchPhi`](DLMF/Zeta/Lerch.lean#L160) (proved). Proved from admissions.
- [25.14.E3_1](https://dlmf.nist.gov/25.14.E3_1): [`DLMF.Zeta.hasSum_lerchPhi_log`](DLMF/Zeta/Lerch.lean#L181) (admitted). z ∈ ℂ \ [1, ∞), z ≠ 0, |ln z| < 2π, s ∉ {1, 2, …}.
- [25.14.E3_2](https://dlmf.nist.gov/25.14.E3_2): [`DLMF.Zeta.hasSum_lerchPhi_log_nat`](DLMF/Zeta/Lerch.lean#L193) (admitted). m ≥ 2; the excluded term n = m - 1 written with an if.
- [25.14.E3_3](https://dlmf.nist.gov/25.14.E3_3): [`DLMF.Zeta.mul_lerchPhi_one_eq_hypergeometric`](DLMF/Zeta/Lerch.lean#L205) (proved). |z| < 1, a ∉ {0, -1, …}; F = ordinaryHypergeometric.
- [25.14.E4](https://dlmf.nist.gov/25.14.E4): [`DLMF.Zeta.lerchPhi_eq_add_nat`](DLMF/Zeta/Lerch.lean#L240) (proved). All m ≥ 0; proved from admissions.
- [25.14.E5](https://dlmf.nist.gov/25.14.E5): [`DLMF.Zeta.lerchPhi_eq_integral`](DLMF/Zeta/Lerch.lean#L257) (proved). Re a > 0 with Re s > 1 at z = 1, Re s > 0 for z ∈ ℂ \ [1, ∞).
- [25.14.E6](https://dlmf.nist.gov/25.14.E6): [`DLMF.Zeta.tendsto_lerchPhi_hermite`](DLMF/Zeta/Lerch.lean#L274) (admitted). Re a > 0 with 0 < |z| < 1, or |z| = 1 and Re s > 1; the improper ∫_0^∞ z^x/(a+x)^s dx as a limit of ∫_0^X.
- [25.14.E7](https://dlmf.nist.gov/25.14.E7): [`DLMF.Zeta.lerchPhi_transformation`](DLMF/Zeta/Lerch.lean#L287) (admitted). DLMF states no conditions; stated for 0 < Re a < 1, 0 < |z| < 1 (verified numerically; it fails e.g. for a = 1.6 + 0.2i, a = 1, |z| = 1 and mixed cases with |z| > 1).
- [25.14.E8](https://dlmf.nist.gov/25.14.E8): [`DLMF.Zeta.lerchPhi_neg_eq_mellinBarnes`](DLMF/Zeta/Lerch.lean#L301) (admitted). |ph z| < π, Re a > 0, max(-Re a, -1) < σ < 0; the vertical line integral as ∫ over ℝ.
- [25.14.E9](https://dlmf.nist.gov/25.14.E9): [`DLMF.Zeta.hasSum_lerchPhi_neg_large`](DLMF/Zeta/Lerch.lean#L312) (admitted). |z| > 1 (exact in that range; checked numerically).
- [25.14.i](https://dlmf.nist.gov/25.14.i): [`DLMF.Zeta.lerchPhi`](DLMF/Zeta/Lerch.lean#L49) (definition); [`DLMF.Zeta.exists_lerchPhi_continuation`](DLMF/Zeta/Lerch.lean#L68) (proved); [`DLMF.Zeta.analyticOnNhd_lerchPhi`](DLMF/Zeta/Lerch.lean#L136) (proved). lerchPhi z s a: the continuation of the series to z ∈ ℂ \ [1, ∞) (classical choice, existence admitted); conditions a ∉ {0, -1, …} (z25b_lerchParamOK).

## [§25.15 Dirichlet L-functions](https://dlmf.nist.gov/25.15)

- [25.15.E1](https://dlmf.nist.gov/25.15.E1): Mathlib: [`DirichletCharacter.LFunction_eq_LSeries`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=DirichletCharacter.LFunction_eq_LSeries#doc). Re s > 1; Mathlib LFunction agrees with the LSeries.
- [25.15.E2](https://dlmf.nist.gov/25.15.E2): Mathlib: [`DirichletCharacter.LSeries_eulerProduct_hasProd`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=DirichletCharacter.LSeries_eulerProduct_hasProd#doc); Mathlib: [`DirichletCharacter.LFunction_ne_zero_of_one_le_re`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=DirichletCharacter.LFunction_ne_zero_of_one_le_re#doc). Re s > 1 as a HasProd; nonvanishing for Re s ≥ 1 in Mathlib.
- [25.15.E3](https://dlmf.nist.gov/25.15.E3): [`DLMF.Zeta.LFunction_eq_sum_hurwitzZeta`](DLMF/Zeta/DirichletL.lean#L81) (proved). Proved for k ≥ 2 and all s (the term r = k vanishes since χ(k) = 0); fully proved.
- [25.15.E4](https://dlmf.nist.gov/25.15.E4): Mathlib: [`DirichletCharacter.LFunction_changeLevel`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=DirichletCharacter.LFunction_changeLevel#doc). Mathlib has the stronger form for any χ₀ mod d with d ∣ k.
- [25.15.E5](https://dlmf.nist.gov/25.15.E5): [`DLMF.Zeta.LFunction_one_sub_of_isPrimitive`](DLMF/Zeta/DirichletL.lean#L106) (proved); Mathlib: [`DirichletCharacter.IsPrimitive.completedLFunction_one_sub`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=DirichletCharacter.IsPrimitive.completedLFunction_one_sub#doc). Proved, printed form with Mathlib gaussSum and star χ, s ≠ -n, (N ≠ 1 ∨ s ≠ 1); Mathlib's completed-L form also pointed.
- [25.15.E6](https://dlmf.nist.gov/25.15.E6): [`DLMF.Zeta.gaussSum_stdAddChar_eq_sum`](DLMF/Zeta/DirichletL.lean#L93) (proved); Mathlib: [`gaussSum`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=gaussSum#doc). G(χ) = ∑_{r=1}^{k} χ(r) e^{2πir/k} equals Mathlib gaussSum χ stdAddChar for k ≥ 2 (proved).
- [25.15.E7](https://dlmf.nist.gov/25.15.E7): [`DLMF.Zeta.LFunction_neg_two_mul_nat_eq_zero`](DLMF/Zeta/DirichletL.lean#L145) (proved); Mathlib: [`DirichletCharacter.Even.LFunction_neg_two_mul_nat`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=DirichletCharacter.Even.LFunction_neg_two_mul_nat#doc). All n ≥ 0, every even χ (not only primitive), k ≥ 2; proved from Mathlib.
- [25.15.E8](https://dlmf.nist.gov/25.15.E8): Mathlib: [`DirichletCharacter.Odd.LFunction_neg_two_mul_nat_sub_one`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=DirichletCharacter.Odd.LFunction_neg_two_mul_nat_sub_one#doc). Every odd χ (Mathlib).
- [25.15.E9](https://dlmf.nist.gov/25.15.E9): Mathlib: [`DirichletCharacter.LFunction_apply_one_ne_zero`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=DirichletCharacter.LFunction_apply_one_ne_zero#doc). Mathlib, χ ≠ χ₁.
- [25.15.E10](https://dlmf.nist.gov/25.15.E10): [`DLMF.Zeta.LFunction_zero_of_ne_one`](DLMF/Zeta/DirichletL.lean#L317) (proved); [`DLMF.Zeta.LFunction_one_zero`](DLMF/Zeta/DirichletL.lean#L347) (proved). Nonprincipal χ: L(0, χ) = -(1/k)∑ r χ(r) admitted; principal χ₁ with k ≥ 2: L(0, χ₁) = 0 proved (implicit condition k ≥ 2 for the printed form).
- [25.15.i](https://dlmf.nist.gov/25.15.i): [`DLMF.Zeta.LFunction_one_residue`](DLMF/Zeta/DirichletL.lean#L64) (proved); Mathlib: [`DirichletCharacter.differentiable_LFunction`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=DirichletCharacter.differentiable_LFunction#doc); Mathlib: [`DirichletCharacter.differentiableAt_LFunction`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=DirichletCharacter.differentiableAt_LFunction#doc); Mathlib: [`DirichletCharacter.LFunctionTrivChar_residue_one`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=DirichletCharacter.LFunctionTrivChar_residue_one#doc). Residue φ(k)/k of L(s, χ₁) at s = 1 proved (LFunction_one_residue, Mathlib's ∏(1 - 1/p) form rewritten); entire for χ ≠ χ₁ in Mathlib.
- [25.15.ii](https://dlmf.nist.gov/25.15.ii): [`DLMF.Zeta.eq_trivial_zero_of_LFunction_eq_zero`](DLMF/Zeta/DirichletL.lean#L170) (proved); [`DLMF.Zeta.infinite_LFunction_zeros_criticalStrip`](DLMF/Zeta/DirichletL.lean#L271) (admitted); [`DLMF.Zeta.LFunction_one_sub_conj_eq_zero`](DLMF/Zeta/DirichletL.lean#L278) (proved). Primitive χ, k ≥ 2: zeros with Re s < 0 are the trivial ones; infinitely many zeros in the critical strip; symmetry ρ ↦ 1 - ρ̄ (all admitted). GRH: conjecture, not acquired.
## Prose, informal and excluded items (part B)

- [25.11.ii](https://dlmf.nist.gov/25.11.ii) and the figures of §25.12: excluded: graphics.
- [25.11.E36](https://dlmf.nist.gov/25.11.E36): no longer in the DLMF (number retired); nothing
  to acquire.
- [25.11.E40](https://dlmf.nist.gov/25.11.E40): the decimal value of Catalan's constant is
  excluded: numerical; the defining series is the tagged `catalanConstant`.
- Bibliographic pointers in §§25.11–25.15 (Apostol, Erdélyi et al., Lewin, Maximon, Prudnikov
  et al., …): excluded: bibliographic.
- 25.15.ii: the generalized Riemann hypothesis is a conjecture: not acquired.
- [§25.16 Mathematical Applications](https://dlmf.nist.gov/25.16): excluded: application. Its
  pure-mathematics content, recorded for later acquisition: Chebyshev's ψ(x) and 25.16.1–25.16.4
  (ψ(x) = x - ∑_ρ x^ρ/ρ - …, the prime number theorem ψ(x) ~ x as an equivalent of ζ(1 + it) ≠ 0,
  the explicit formula, and the Riemann-hypothesis-equivalent error bound, a conjecture); Euler
  sums H(s) = ∑ Hₙ/n^s, 25.16.5–25.16.15 (H(2) = 2ζ(3), H(3) = (5/4)ζ(4), the general formula
  25.16.9–25.16.10, the reciprocity law 25.16.12 and the double-index sums 25.16.13–25.16.15).
  Mathlib has Chebyshev's ψ (`Chebyshev.psi`) and ζ(1 + it) ≠ 0, not yet the prime number
  theorem.
- [§25.17 Physical Applications](https://dlmf.nist.gov/25.17): excluded: application.
- [§§25.18–25.21](https://dlmf.nist.gov/25.18) (methods of computation, tables, approximations,
  software): excluded: computation.

## Validation (part B)

- `lake build` of `DLMF.Zeta.{Hurwitz, HurwitzIntegrals, Polylog, Periodic, Lerch, DirichletL,
  MathlibCoverageB}`, `DLMF.Polylog.Dilog`, `DLMF.Constants.Catalan` and
  `DLMF.Gamma.PolygammaHurwitz` succeeds; the strict check `lake env lean
  -DautoImplicit=false -DrelaxedAutoImplicit=false` of every new or changed file reports no
  errors and no warnings other than `declaration uses 'sorry'`.
- Admissions (`grep -c '\bsorry\b'`): Hurwitz 24, HurwitzIntegrals 20, Polylog 13, Periodic 1,
  Lerch 10, DirichletL 4, MathlibCoverageB 0 (72). No helper or definition contains `sorry`; no
  axioms, no `native_decide`.
- `#print axioms` on all proved declarations: the 13 proved tagged theorems (among them
  `hasSum_cos_div_sq`, `polylog_one`, `expZeta_eq_hurwitzZeta`, `hurwitzZeta_one_sub_eq_expZeta`,
  `LFunction_eq_sum_hurwitzZeta`, `gaussSum_stdAddChar_eq_sum`, `LFunction_one_sub_of_isPrimitive`,
  `LFunction_one_residue`) depend only on `[propext, Classical.choice, Quot.sound]`; the 14
  marked "proved from admissions" and the helper lemmas `z25b_polylog_spec`,
  `z25b_lerchPhi_spec`, `z25b_hasSum_lerchPhi_of_cond` (which unpack the admitted existence
  theorems) add `sorryAx`.
