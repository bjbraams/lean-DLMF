# DLMF Chapter 22 acquisition: Jacobian Elliptic Functions

**Proof status (2026-11-13).** Chapter 22 has 8 direct source admissions. The [updated-dependency proof round](
REVIEW.md#proofs-with-the-updated-dependencies-2026-11-12) proves 5 original admissions in this chapter.
Per-entry statuses and source links below follow the compiled axiom audit; earlier
dated counts describe their original batches.

> Source paths and current layout notes were refreshed on 2026-10-30; generated per-entry
> statuses follow the compiled ledger refresh. Dated acquisition and proof counts
> describe their original batches.

**Current layout (2026-10-30).** `JacobiElliptic.Basic` exports only `Basic.Definitions`. Quarter-period,
modulus-inversion and analytic-property results are in `QuarterPeriods`, `ModulusInversion`
and `AnalyticProperties`; the `SpecialValues` theorem leaves are imported through their
own umbrella. The real amplitude foundation is `DLMF.Elliptic.Basic.Amplitude`.

This acquisition covers the definitions, numbered formulas, exact tables and analytical
assertions in prose of [DLMF Chapter 22](https://dlmf.nist.gov/22), version 1.2.8, checked
on 2026-10-25. It was done in two parts: ACQ22A covers the notation (§22.1), the definitions
(§22.2) and §§22.4–22.9; ACQ22B covers §§22.10–22.17 and records the exclusions of §22.3
(graphics) and §§22.18–22.22 (applications and computation) in its own sections below.

**Status after proof round 1 (2026-10-25).** The 410 declarations tagged with Chapter 22 IDs are 43 definitions, 305 proved theorems and 62 theorems that still depend on admissions (62 direct admissions in DLMF/JacobiElliptic and DLMF/Theta/Relations.lean; the counts below record the acquisition and earlier states). The per-line statuses in this ledger are regenerated from the compiled dump. See REVIEW.md, "Proof round 1 for Chapters 19–23 (2026-10-25)".

Part A: §§22.2 and 22.4–22.9 have 92 numbered equations and 8 exact tables (22.4.1–3,
22.5.1–4, 22.6.1), all in scope and all acquired; no equation of these sections is numerical.
The entry point is [DLMF/JacobiElliptic.lean](DLMF/JacobiElliptic.lean); part A lives in
`Basic`, `PeriodsPolesZeros`, `SpecialValues`, `ElementaryIdentities`, `Landen`, `Addition`,
`Cyclic` and `MathlibCoverage` under `DLMF/JacobiElliptic/`. These modules contain 191
tagged declarations: 30 definitions, 59 proved theorems and **102 direct admissions**. Of the
proved theorems, 8 are free of `sorryAx`; 51 are proved from the two admitted foundations
below (or other admissions). Nine existing real-variable results in `DLMF/Elliptic/Jacobi.lean`
and `JacobiIdentities.lean` received part-A tags in place (all proved, admission-free). The
untagged lattice forms `jacobiSnOfTau_shift` … `jacobiCsOfTau_shift` (all 72 entries of
Table 22.4.3 in the τ-parametrization) are proved without any admission.

## Domains, conventions and source corrections

- Mathlib and the pinned TauCeti have no Jacobian elliptic functions, no complex-modulus
  complete elliptic integral, and no Landen or cyclic identities. The functions are built on
  the project's `θ₁…θ₄` (`DLMF/Elliptic/Theta.lean`, DLMF normalization, q = e^{iπτ}), which
  rest on Mathlib's `jacobiTheta₂`.
- Two parametrizations. The lattice form `jacobiPQOfTau p q z τ` (Im τ > 0) defines
  k = θ₂²(0|τ)/θ₃²(0|τ), k' = θ₄²/θ₃², K = (π/2)θ₃², K' = -iτK and pq by 22.2.4–22.2.9; its
  identities are proved from theta identities (triple-product nonvanishing of the theta
  constants, half-period shifts). The modulus form `jacobiPQ p q z k` is literal DLMF: K(k)
  and K'(k) are the principal complex integrals 19.2.8–19.2.9 (`compEllIntKk`,
  `completeEllipticKPrime`), τ = iK'/K, q = e^{-πK'/K}, and pq is the theta quotient at that τ.
- Modulus domain `jacobiModulusDomain`: Re k > 0 and k ∉ [1, ∞). DLMF 22.1 takes 0 ≤ k ≤ 1
  outside §§22.3(iv), 22.17, 22.19; the complex domain is the natural one on which the
  principal K, K' give the theta parametrization (checked numerically at k = 0.6,
  0.5 + 0.3i, 1.3 + 0.4i). The endpoint cases k = 0 and k = 1 are represented by the limits of
  Tables 22.5.3–22.5.4, not by values. ACQ22B handles moduli outside this domain (§22.17).
- Admitted foundations: `jacobiTau_im_pos` (Im τ(k) > 0 on the domain) and
  `jacobi_inversion_k` (the lattice modulus, comodulus and K at τ(k) are k, the principal k'
  and K(k): the inversion problem 22.2.2 / 20.9.1). Every k-form result proved from
  theta identities depends on them. The real bridges `jacobiSn_ofReal` etc. to the project's
  `Real.jacobiSnOfParameter u (k²)` (0 < k < 1) are admitted. (All of these were proved in proof round 1
  on 2026-10-25; the real bridges now live in `SpecialValues.lean`.)
- Lean totalization: x/0 = 0, so at a pole a function takes a junk value. Statements
  dividing by a function or theta value carry hypotheses: `IsJacobiRegular r z k` (θ_r(ζ) ≠ 0,
  i.e. the letter r is regular at z) and explicit nonvanishing of printed denominators.
  Residues in Table 22.5.1 are limits of (z - z₀) f(z) on punctured neighbourhoods.
- Glaisher's notation: `JacobiLetter` = s, c, d, n; `jacobiGlaisher p q` is 1 for p = q,
  so pp = 1 as DLMF's convention 22.2.10 implies.
- Source corrections (numerical evidence in the entries below): Table 22.5.1 derivative of
  dc at K + iK' is -k (printed k); 22.8.23 as printed fails, two corrected forms acquired;
  22.9.23 repeats a summand, corrected to s₃,₃d₃,₃. In 22.7.5 DLMF defines k₂' by the
  quotient (1-k)/(1+k), which is not always the principal √(1-k₂²) for complex k; the
  quotient is kept.

## Numbered formulas and exact tables

## [§22.2 Definitions](https://dlmf.nist.gov/22.2)

- [22.2.E1](https://dlmf.nist.gov/22.2.E1): [`DLMF.JacobiElliptic.jacobiNome`](DLMF/JacobiElliptic/Basic/Definitions.lean#L153) (definition); [`DLMF.JacobiElliptic.jacobiNome_eq_exp_tau`](DLMF/JacobiElliptic/Basic/ThetaShifts.lean#L108) (proved); [`DLMF.JacobiElliptic.jacobiTau_im_pos`](DLMF/JacobiElliptic/QuarterPeriods.lean#L273) (proved). Nome as `jacobiNome k = exp(-πK'(k)/K(k))`; `jacobiNome_eq_exp_tau` gives q = e^{iπτ}. Admitted foundation `jacobiTau_im_pos`: Im τ > 0 on the domain.
- [22.2.E2](https://dlmf.nist.gov/22.2.E2): [`DLMF.JacobiElliptic.completeEllipticKOfTau`](DLMF/JacobiElliptic/Basic/Definitions.lean#L117) (definition); [`DLMF.JacobiElliptic.jacobiModulusOfTau`](DLMF/JacobiElliptic/Basic/Definitions.lean#L126) (definition); [`DLMF.JacobiElliptic.jacobiComodulusOfTau`](DLMF/JacobiElliptic/Basic/Definitions.lean#L130) (definition); [`DLMF.JacobiElliptic.jacobi_inversion_k`](DLMF/JacobiElliptic/ModulusInversion.lean#L690) (proved). Lattice form: k = θ₂²(0|τ)/θ₃²(0|τ), k' = θ₄²/θ₃², K = (π/2)θ₃² (definitions `jacobiModulusOfTau`, `jacobiComodulusOfTau`, `completeEllipticKOfTau`). Admitted foundation `jacobi_inversion_k`: at τ(k) these recover k, the principal k' and K(k) on the domain (numerically confirmed at real and complex k).
- [22.2.E3](https://dlmf.nist.gov/22.2.E3): [`DLMF.JacobiElliptic.jacobiThetaArgumentOfTau`](DLMF/JacobiElliptic/Basic/Definitions.lean#L134) (definition); [`DLMF.JacobiElliptic.jacobiThetaArgument`](DLMF/JacobiElliptic/Basic/Definitions.lean#L157) (definition). ζ = πz/(2K).
- [22.2.E4](https://dlmf.nist.gov/22.2.E4): [`DLMF.JacobiElliptic.jacobiSn`](DLMF/JacobiElliptic/Basic/Definitions.lean#L173) (definition); [`DLMF.JacobiElliptic.jacobiNs`](DLMF/JacobiElliptic/Basic/Definitions.lean#L191) (definition); [`DLMF.JacobiElliptic.jacobiSn_ofReal`](DLMF/JacobiElliptic/SpecialValues/RealAndHalfPeriods.lean#L139) (proved); [`DLMF.JacobiElliptic.jacobiPQ_eq_one_div`](DLMF/JacobiElliptic/Basic/Properties.lean#L36) (proved); [`DLMF.JacobiElliptic.jacobi_eq_theta_quotients`](DLMF/JacobiElliptic/AnalyticProperties.lean#L80) (proved from admitted foundations). Theta quotients in DLMF normalization; `jacobi_eq_theta_quotients` restates 22.2.4–22.2.9 for the k-form (proved from the inversion admission). Real bridges to the project's `Real.jacobiSnOfParameter` etc. (parameter m = k², 0 < k < 1) are admitted.
- [22.2.E5](https://dlmf.nist.gov/22.2.E5): [`DLMF.JacobiElliptic.jacobiCn`](DLMF/JacobiElliptic/Basic/Definitions.lean#L176) (definition); [`DLMF.JacobiElliptic.jacobiNc`](DLMF/JacobiElliptic/Basic/Definitions.lean#L194) (definition); [`DLMF.JacobiElliptic.jacobiCn_ofReal`](DLMF/JacobiElliptic/SpecialValues/RealAndHalfPeriods.lean#L146) (proved); [`DLMF.JacobiElliptic.jacobiPQ_eq_one_div`](DLMF/JacobiElliptic/Basic/Properties.lean#L36) (proved); [`DLMF.JacobiElliptic.jacobi_eq_theta_quotients`](DLMF/JacobiElliptic/AnalyticProperties.lean#L80) (proved from admitted foundations).
- [22.2.E6](https://dlmf.nist.gov/22.2.E6): [`DLMF.JacobiElliptic.jacobiDn`](DLMF/JacobiElliptic/Basic/Definitions.lean#L179) (definition); [`DLMF.JacobiElliptic.jacobiNd`](DLMF/JacobiElliptic/Basic/Definitions.lean#L197) (definition); [`DLMF.JacobiElliptic.jacobiDn_ofReal`](DLMF/JacobiElliptic/SpecialValues/RealAndHalfPeriods.lean#L153) (proved); [`DLMF.JacobiElliptic.jacobiPQ_eq_one_div`](DLMF/JacobiElliptic/Basic/Properties.lean#L36) (proved); [`DLMF.JacobiElliptic.jacobi_eq_theta_quotients`](DLMF/JacobiElliptic/AnalyticProperties.lean#L80) (proved from admitted foundations).
- [22.2.E7](https://dlmf.nist.gov/22.2.E7): [`DLMF.JacobiElliptic.jacobiSd`](DLMF/JacobiElliptic/Basic/Definitions.lean#L182) (definition); [`DLMF.JacobiElliptic.jacobiDs`](DLMF/JacobiElliptic/Basic/Definitions.lean#L200) (definition); [`DLMF.JacobiElliptic.jacobiPQ_eq_one_div`](DLMF/JacobiElliptic/Basic/Properties.lean#L36) (proved); [`DLMF.JacobiElliptic.jacobi_eq_theta_quotients`](DLMF/JacobiElliptic/AnalyticProperties.lean#L80) (proved from admitted foundations).
- [22.2.E8](https://dlmf.nist.gov/22.2.E8): [`DLMF.JacobiElliptic.jacobiCd`](DLMF/JacobiElliptic/Basic/Definitions.lean#L185) (definition); [`DLMF.JacobiElliptic.jacobiDc`](DLMF/JacobiElliptic/Basic/Definitions.lean#L203) (definition); [`DLMF.JacobiElliptic.jacobiPQ_eq_one_div`](DLMF/JacobiElliptic/Basic/Properties.lean#L36) (proved); [`DLMF.JacobiElliptic.jacobi_eq_theta_quotients`](DLMF/JacobiElliptic/AnalyticProperties.lean#L80) (proved from admitted foundations).
- [22.2.E9](https://dlmf.nist.gov/22.2.E9): [`DLMF.JacobiElliptic.jacobiSc`](DLMF/JacobiElliptic/Basic/Definitions.lean#L188) (definition); [`DLMF.JacobiElliptic.jacobiCs`](DLMF/JacobiElliptic/Basic/Definitions.lean#L206) (definition); [`DLMF.JacobiElliptic.jacobiPQ_eq_one_div`](DLMF/JacobiElliptic/Basic/Properties.lean#L36) (proved); [`DLMF.JacobiElliptic.jacobi_eq_theta_quotients`](DLMF/JacobiElliptic/AnalyticProperties.lean#L80) (proved from admitted foundations).
- [22.2.E10](https://dlmf.nist.gov/22.2.E10): [`DLMF.JacobiElliptic.jacobiPQ_eq_one_div`](DLMF/JacobiElliptic/Basic/Properties.lean#L36) (proved); [`DLMF.JacobiElliptic.jacobiPQ_eq_div`](DLMF/JacobiElliptic/Basic/Properties.lean#L47) (proved); [`DLMF.JacobiElliptic.jacobiPQ_self`](DLMF/JacobiElliptic/Basic/Properties.lean#L57) (proved). Glaisher relation pq = pr/qr: unconditional reciprocal form `jacobiPQ_eq_one_div` and the quotient form for a letter r regular at z (`IsJacobiRegular`).
- [22.2.E11](https://dlmf.nist.gov/22.2.E11): [`DLMF.JacobiElliptic.jacobiPQ_eq_neville`](DLMF/JacobiElliptic/AnalyticProperties.lean#L134) (proved). Neville theta form; `nevilleThetaOfTau` is defined locally from the theta functions (ACQ20 owns Neville's functions in Ch. 20); Mathlib: [`jacobiTheta₂`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.html#jacobiTheta₂).
- [22.2.E12](https://dlmf.nist.gov/22.2.E12): [`DLMF.JacobiElliptic.completeEllipticKPrimeOfTau`](DLMF/JacobiElliptic/Basic/Definitions.lean#L122) (definition); [`DLMF.JacobiElliptic.jacobiTau`](DLMF/JacobiElliptic/Basic/Definitions.lean#L149) (definition). τ = iK'/K; K'(τ) := -iτK(τ) in the lattice form.

## [§22.4 Periods, Poles, and Zeros](https://dlmf.nist.gov/22.4)

- [22.4.T1](https://dlmf.nist.gov/22.4.T1): [`DLMF.JacobiElliptic.jacobiPQ_zeros_poles`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L1029) (proved); [`DLMF.JacobiElliptic.jacobiSn_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L995) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiCd_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L1004) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiDc_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L1013) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiNs_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L1022) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiCn_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L1031) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiSd_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L1040) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiNc_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L1049) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiDs_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L1058) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiDn_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L1067) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiNd_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L1077) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiSc_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L1087) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiCs_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L1097) (proved from admitted foundations); [`DLMF.Elliptic.Real.jacobiSnOfParameter_add_four_completeEllipticKOfParameter`](DLMF/Elliptic/Basic/Jacobi.lean#L221) (proved). Periods proved for all twelve functions (`jacobiXxk_periodic`); pole positions and congruence classes in `jacobiPQ_zeros_poles` (admitted).
- [22.4.T2](https://dlmf.nist.gov/22.4.T2): [`DLMF.JacobiElliptic.jacobiPQ_zeros_poles`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L1029) (proved); [`DLMF.JacobiElliptic.jacobiSn_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L995) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiCd_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L1004) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiDc_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L1013) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiNs_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L1022) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiCn_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L1031) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiSd_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L1040) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiNc_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L1049) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiDs_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L1058) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiDn_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L1067) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiNd_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L1077) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiSc_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L1087) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiCs_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L1097) (proved from admitted foundations). As 22.4.T1 for zeros.
- [22.4.T3](https://dlmf.nist.gov/22.4.T3): [`DLMF.JacobiElliptic.jacobiSn_shift`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L500) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiCn_shift`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L519) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiDn_shift`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L538) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiCd_shift`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L557) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiSd_shift`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L576) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiNd_shift`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L595) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiDc_shift`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L614) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiNc_shift`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L633) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiSc_shift`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L652) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiNs_shift`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L671) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiDs_shift`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L690) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiCs_shift`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L709) (proved from admitted foundations); [`DLMF.Elliptic.Real.jacobi_add_two_completeEllipticKOfParameter`](DLMF/Elliptic/Basic/Jacobi.lean#L207) (proved); [`DLMF.Elliptic.Real.jacobi_add_completeEllipticKOfParameter`](DLMF/Elliptic/JacobiIdentities.lean#L271) (proved). All 12 rows × 6 columns (K, K+iK', iK', 2K, 2K+2iK', 2iK') proved: lattice τ-form `jacobiXxTau_shift` from half-period theta shifts, k-form `jacobiXxk_shift` via the inversion admission.

## [§22.5 Special Values](https://dlmf.nist.gov/22.5)

- [22.5.T1](https://dlmf.nist.gov/22.5.T1): [`DLMF.JacobiElliptic.jacobiSn_specialValues`](DLMF/JacobiElliptic/SpecialValues/ThetaValues.lean#L102) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiCn_specialValues`](DLMF/JacobiElliptic/SpecialValues/ThetaValues.lean#L135) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiDn_specialValues`](DLMF/JacobiElliptic/SpecialValues/ThetaValues.lean#L168) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiCd_specialValues`](DLMF/JacobiElliptic/SpecialValues/ThetaValues.lean#L201) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiSd_specialValues`](DLMF/JacobiElliptic/SpecialValues/ThetaValues.lean#L234) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiNd_specialValues`](DLMF/JacobiElliptic/SpecialValues/ThetaValues.lean#L267) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiDc_specialValues`](DLMF/JacobiElliptic/SpecialValues/ThetaValues.lean#L300) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiNc_specialValues`](DLMF/JacobiElliptic/SpecialValues/ThetaValues.lean#L333) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiSc_specialValues`](DLMF/JacobiElliptic/SpecialValues/ThetaValues.lean#L366) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiNs_specialValues`](DLMF/JacobiElliptic/SpecialValues/ThetaValues.lean#L399) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiDs_specialValues`](DLMF/JacobiElliptic/SpecialValues/ThetaValues.lean#L420) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiCs_specialValues`](DLMF/JacobiElliptic/SpecialValues/ThetaValues.lean#L441) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiSn_specialDerivs`](DLMF/JacobiElliptic/SpecialValues/DerivativesAndResidues.lean#L98) (proved); [`DLMF.JacobiElliptic.jacobiCn_specialDerivs`](DLMF/JacobiElliptic/SpecialValues/DerivativesAndResidues.lean#L183) (proved); [`DLMF.JacobiElliptic.jacobiDn_specialDerivs`](DLMF/JacobiElliptic/SpecialValues/DerivativesAndResidues.lean#L268) (proved); [`DLMF.JacobiElliptic.jacobiCd_specialDerivs`](DLMF/JacobiElliptic/SpecialValues/DerivativesAndResidues.lean#L353) (proved); [`DLMF.JacobiElliptic.jacobiSd_specialDerivs`](DLMF/JacobiElliptic/SpecialValues/DerivativesAndResidues.lean#L438) (proved); [`DLMF.JacobiElliptic.jacobiNd_specialDerivs`](DLMF/JacobiElliptic/SpecialValues/DerivativesAndResidues.lean#L524) (proved); [`DLMF.JacobiElliptic.jacobiDc_specialDerivs`](DLMF/JacobiElliptic/SpecialValues/DerivativesAndResidues.lean#L610) (proved); [`DLMF.JacobiElliptic.jacobiNc_specialDerivs`](DLMF/JacobiElliptic/SpecialValues/DerivativesAndResidues.lean#L695) (proved); [`DLMF.JacobiElliptic.jacobiSc_specialDerivs`](DLMF/JacobiElliptic/SpecialValues/DerivativesAndResidues.lean#L780) (proved); [`DLMF.JacobiElliptic.jacobiNs_specialDerivs`](DLMF/JacobiElliptic/SpecialValues/DerivativesAndResidues.lean#L865) (proved); [`DLMF.JacobiElliptic.jacobiDs_specialDerivs`](DLMF/JacobiElliptic/SpecialValues/DerivativesAndResidues.lean#L969) (proved); [`DLMF.JacobiElliptic.jacobiCs_specialDerivs`](DLMF/JacobiElliptic/SpecialValues/DerivativesAndResidues.lean#L1073) (proved); [`DLMF.Elliptic.Real.jacobi_completeEllipticKOfParameter`](DLMF/Elliptic/Basic/Jacobi.lean#L236) (proved); [`DLMF.Elliptic.jacobi_zero`](DLMF/Elliptic/Basic/Jacobi.lean#L245) (proved). Values proved for all 12 functions (Lean junk value 0 at the poles is not asserted; poles are excluded). Derivatives and residues admitted; residues stated as limits of (z - z₀)·f(z) on a punctured neighbourhood. **Corrected** (DLMF erratum): the derivative of dc at K + iK' is -k = k'² sc nc there, printed k.
- [22.5.T2](https://dlmf.nist.gov/22.5.T2): [`DLMF.JacobiElliptic.jacobi_specialValues_HalfK`](DLMF/JacobiElliptic/SpecialValues/RealAndHalfPeriods.lean#L304) (proved); [`DLMF.JacobiElliptic.jacobi_specialValues_HalfKKp`](DLMF/JacobiElliptic/SpecialValues/RealAndHalfPeriods.lean#L743) (proved); [`DLMF.JacobiElliptic.jacobi_specialValues_HalfKp`](DLMF/JacobiElliptic/SpecialValues/RealAndHalfPeriods.lean#L469) (proved); [`DLMF.JacobiElliptic.jacobi_specialValues_ThreeHalfK`](DLMF/JacobiElliptic/SpecialValues/RealAndHalfPeriods.lean#L401) (proved); [`DLMF.JacobiElliptic.jacobi_specialValues_ThreeHalfKKp`](DLMF/JacobiElliptic/SpecialValues/RealAndHalfPeriods.lean#L963) (proved); [`DLMF.JacobiElliptic.jacobi_specialValues_ThreeHalfKp`](DLMF/JacobiElliptic/SpecialValues/RealAndHalfPeriods.lean#L517) (proved); [`DLMF.Elliptic.Real.jacobi_half_completeEllipticKOfParameter`](DLMF/Elliptic/JacobiIdentities.lean#L293) (proved). Admitted; principal square roots as printed, on the stated domain.
- [22.5.T3](https://dlmf.nist.gov/22.5.T3): [`DLMF.JacobiElliptic.tendsto_jacobiSn_zero`](DLMF/JacobiElliptic/SpecialValues/ModulusLimits.lean#L320) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiCd_zero`](DLMF/JacobiElliptic/SpecialValues/ModulusLimits.lean#L329) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiDc_zero`](DLMF/JacobiElliptic/SpecialValues/ModulusLimits.lean#L338) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiNs_zero`](DLMF/JacobiElliptic/SpecialValues/ModulusLimits.lean#L348) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiCn_zero`](DLMF/JacobiElliptic/SpecialValues/ModulusLimits.lean#L358) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiSd_zero`](DLMF/JacobiElliptic/SpecialValues/ModulusLimits.lean#L367) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiNc_zero`](DLMF/JacobiElliptic/SpecialValues/ModulusLimits.lean#L376) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiDs_zero`](DLMF/JacobiElliptic/SpecialValues/ModulusLimits.lean#L386) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiDn_zero`](DLMF/JacobiElliptic/SpecialValues/ModulusLimits.lean#L396) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiNd_zero`](DLMF/JacobiElliptic/SpecialValues/ModulusLimits.lean#L405) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiSc_zero`](DLMF/JacobiElliptic/SpecialValues/ModulusLimits.lean#L414) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiCs_zero`](DLMF/JacobiElliptic/SpecialValues/ModulusLimits.lean#L424) (proved); [`DLMF.Elliptic.jacobi_zero_param`](DLMF/Elliptic/Basic/Jacobi.lean#L262) (proved). Limits as real k → 0+ (pointwise in z, away from the poles of the limit function); Mathlib: [`Complex.sin`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Trigonometric.html#Complex.sin).
- [22.5.T4](https://dlmf.nist.gov/22.5.T4): [`DLMF.JacobiElliptic.tendsto_jacobiSn_one`](DLMF/JacobiElliptic/SpecialValues/ModulusLimits.lean#L495) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiCd_one`](DLMF/JacobiElliptic/SpecialValues/ModulusLimits.lean#L513) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiDc_one`](DLMF/JacobiElliptic/SpecialValues/ModulusLimits.lean#L531) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiNs_one`](DLMF/JacobiElliptic/SpecialValues/ModulusLimits.lean#L549) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiCn_one`](DLMF/JacobiElliptic/SpecialValues/ModulusLimits.lean#L567) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiSd_one`](DLMF/JacobiElliptic/SpecialValues/ModulusLimits.lean#L585) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiNc_one`](DLMF/JacobiElliptic/SpecialValues/ModulusLimits.lean#L603) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiDs_one`](DLMF/JacobiElliptic/SpecialValues/ModulusLimits.lean#L621) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiDn_one`](DLMF/JacobiElliptic/SpecialValues/ModulusLimits.lean#L639) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiNd_one`](DLMF/JacobiElliptic/SpecialValues/ModulusLimits.lean#L657) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiSc_one`](DLMF/JacobiElliptic/SpecialValues/ModulusLimits.lean#L675) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiCs_one`](DLMF/JacobiElliptic/SpecialValues/ModulusLimits.lean#L693) (proved). Limits as real k → 1- (pointwise in z, away from the poles of the limit function); Mathlib: [`Complex.tanh`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Trigonometric.html#Complex.tanh).

## [§22.6 Elementary Identities](https://dlmf.nist.gov/22.6)

- [22.6.E1](https://dlmf.nist.gov/22.6.E1): [`DLMF.JacobiElliptic.jacobi_sq_sum`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L72) (proved); [`DLMF.Elliptic.Real.jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq`](DLMF/Elliptic/Basic/Jacobi.lean#L131) (proved); [`DLMF.Elliptic.Real.mul_jacobiSnOfParameter_sq_add_jacobiDnOfParameter_sq`](DLMF/Elliptic/Basic/Jacobi.lean#L137) (proved); [`DLMF.Elliptic.Real.jacobiDnOfParameter_sq_sub_mul_jacobiCnOfParameter_sq`](DLMF/Elliptic/JacobiIdentities.lean#L53) (proved). Complex k-form admitted; real forms already in the project (`Real.jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq`, `Real.mul_jacobiSnOfParameter_sq_add_jacobiDnOfParameter_sq`).
- [22.6.E2](https://dlmf.nist.gov/22.6.E2): [`DLMF.JacobiElliptic.jacobi_sq_sum_s`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L99) (proved from admitted foundations).
- [22.6.E3](https://dlmf.nist.gov/22.6.E3): [`DLMF.JacobiElliptic.jacobi_sq_sum_c`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L112) (proved from admitted foundations).
- [22.6.E4](https://dlmf.nist.gov/22.6.E4): [`DLMF.JacobiElliptic.jacobi_sq_sum_d`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L125) (proved from admitted foundations).
- [22.6.E5](https://dlmf.nist.gov/22.6.E5): [`DLMF.JacobiElliptic.jacobiSn_two_mul`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L140) (proved from admitted foundations).
- [22.6.E6](https://dlmf.nist.gov/22.6.E6): [`DLMF.JacobiElliptic.jacobiCn_two_mul`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L151) (proved from admitted foundations).
- [22.6.E7](https://dlmf.nist.gov/22.6.E7): [`DLMF.JacobiElliptic.jacobiDn_two_mul`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L173) (proved from admitted foundations).
- [22.6.E8](https://dlmf.nist.gov/22.6.E8): [`DLMF.JacobiElliptic.jacobiCd_two_mul`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L195) (proved from admitted foundations).
- [22.6.E9](https://dlmf.nist.gov/22.6.E9): [`DLMF.JacobiElliptic.jacobiSd_two_mul`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L208) (proved from admitted foundations).
- [22.6.E10](https://dlmf.nist.gov/22.6.E10): [`DLMF.JacobiElliptic.jacobiNd_two_mul`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L220) (proved from admitted foundations).
- [22.6.E11](https://dlmf.nist.gov/22.6.E11): [`DLMF.JacobiElliptic.jacobiDc_two_mul`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L232) (proved from admitted foundations).
- [22.6.E12](https://dlmf.nist.gov/22.6.E12): [`DLMF.JacobiElliptic.jacobiNc_two_mul`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L244) (proved from admitted foundations).
- [22.6.E13](https://dlmf.nist.gov/22.6.E13): [`DLMF.JacobiElliptic.jacobiSc_two_mul`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L255) (proved from admitted foundations).
- [22.6.E14](https://dlmf.nist.gov/22.6.E14): [`DLMF.JacobiElliptic.jacobi_two_mul_s`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L325) (proved).
- [22.6.E15](https://dlmf.nist.gov/22.6.E15): [`DLMF.JacobiElliptic.jacobi_two_mul_s`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L325) (proved).
- [22.6.E16](https://dlmf.nist.gov/22.6.E16): [`DLMF.JacobiElliptic.jacobi_two_mul_s`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L325) (proved).
- [22.6.E17](https://dlmf.nist.gov/22.6.E17): [`DLMF.JacobiElliptic.jacobi_two_mul_ratio`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L376) (proved).
- [22.6.E18](https://dlmf.nist.gov/22.6.E18): [`DLMF.JacobiElliptic.jacobi_two_mul_ratio`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L376) (proved).
- [22.6.E19](https://dlmf.nist.gov/22.6.E19): [`DLMF.JacobiElliptic.jacobiSn_half_sq`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L408) (proved).
- [22.6.E20](https://dlmf.nist.gov/22.6.E20): [`DLMF.JacobiElliptic.jacobiCn_half_sq`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L443) (proved).
- [22.6.E21](https://dlmf.nist.gov/22.6.E21): [`DLMF.JacobiElliptic.jacobiDn_half_sq`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L494) (proved).
- [22.6.E22](https://dlmf.nist.gov/22.6.E22): [`DLMF.JacobiElliptic.jacobiPQ_half_sq`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L566) (proved).
- [22.6.T1](https://dlmf.nist.gov/22.6.T1): [`DLMF.JacobiElliptic.jacobi_imaginary_transformation`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L814) (proved). Jacobi imaginary transformation, all 12 rows; k' is the principal comodulus.

## [§22.7 Landen Transformations](https://dlmf.nist.gov/22.7)

- [22.7.E1](https://dlmf.nist.gov/22.7.E1): [`DLMF.JacobiElliptic.jacobiLandenDescModulus`](DLMF/JacobiElliptic/Landen.lean#L45) (definition). k₁ = (1-k')/(1+k') with the principal k'.
- [22.7.E2](https://dlmf.nist.gov/22.7.E2): [`DLMF.JacobiElliptic.jacobi_landen_descending`](DLMF/JacobiElliptic/Landen.lean#L67) (admitted).
- [22.7.E3](https://dlmf.nist.gov/22.7.E3): [`DLMF.JacobiElliptic.jacobi_landen_descending`](DLMF/JacobiElliptic/Landen.lean#L67) (admitted).
- [22.7.E4](https://dlmf.nist.gov/22.7.E4): [`DLMF.JacobiElliptic.jacobi_landen_descending`](DLMF/JacobiElliptic/Landen.lean#L67) (admitted).
- [22.7.E5](https://dlmf.nist.gov/22.7.E5): [`DLMF.JacobiElliptic.jacobiLandenAscModulus`](DLMF/JacobiElliptic/Landen.lean#L49) (definition); [`DLMF.JacobiElliptic.jacobiLandenAscComodulus`](DLMF/JacobiElliptic/Landen.lean#L53) (definition); [`DLMF.JacobiElliptic.jacobiLandenAscComodulus_sq`](DLMF/JacobiElliptic/Landen.lean#L57) (proved). k₂ = 2√k/(1+k) (principal root), k₂' = (1-k)/(1+k) as DLMF defines it; k₂'² = 1 - k₂² proved. Note: k₂' is not the principal √(1-k₂²) for every complex k (e.g. k = 1.3 + 0.4i); the Landen formulas hold with DLMF's quotient.
- [22.7.E6](https://dlmf.nist.gov/22.7.E6): [`DLMF.JacobiElliptic.jacobi_landen_ascending`](DLMF/JacobiElliptic/Landen.lean#L88) (admitted).
- [22.7.E7](https://dlmf.nist.gov/22.7.E7): [`DLMF.JacobiElliptic.jacobi_landen_ascending`](DLMF/JacobiElliptic/Landen.lean#L88) (admitted).
- [22.7.E8](https://dlmf.nist.gov/22.7.E8): [`DLMF.JacobiElliptic.jacobi_landen_ascending`](DLMF/JacobiElliptic/Landen.lean#L88) (admitted).

## [§22.8 Addition Theorems](https://dlmf.nist.gov/22.8)

- [22.8.E1](https://dlmf.nist.gov/22.8.E1): [`DLMF.JacobiElliptic.jacobiSn_add`](DLMF/JacobiElliptic/Addition/ThetaAndQuotients.lean#L375) (proved); [`DLMF.Elliptic.Real.jacobiSnOfParameter_add`](DLMF/Elliptic/JacobiIdentities.lean#L131) (proved). Hypotheses: the letter n regular at u, v (θ₄ ≠ 0) and the printed denominator nonzero; similarly d, c, s for 22.8.4–6, 7–9, 10–12. Real forms for 22.8.1–3 already exist (`Real.jacobiSnOfParameter_add` etc.).
- [22.8.E2](https://dlmf.nist.gov/22.8.E2): [`DLMF.JacobiElliptic.jacobiCn_add`](DLMF/JacobiElliptic/Addition/ThetaAndQuotients.lean#L412) (proved); [`DLMF.Elliptic.Real.jacobiCnOfParameter_add`](DLMF/Elliptic/JacobiIdentities.lean#L176) (proved).
- [22.8.E3](https://dlmf.nist.gov/22.8.E3): [`DLMF.JacobiElliptic.jacobiDn_add`](DLMF/JacobiElliptic/Addition/ThetaAndQuotients.lean#L448) (proved); [`DLMF.Elliptic.Real.jacobiDnOfParameter_add`](DLMF/Elliptic/JacobiIdentities.lean#L219) (proved).
- [22.8.E4](https://dlmf.nist.gov/22.8.E4): [`DLMF.JacobiElliptic.jacobiCd_add`](DLMF/JacobiElliptic/Addition/ThetaAndQuotients.lean#L484) (proved).
- [22.8.E5](https://dlmf.nist.gov/22.8.E5): [`DLMF.JacobiElliptic.jacobiSd_add`](DLMF/JacobiElliptic/Addition/ThetaAndQuotients.lean#L522) (proved).
- [22.8.E6](https://dlmf.nist.gov/22.8.E6): [`DLMF.JacobiElliptic.jacobiNd_add`](DLMF/JacobiElliptic/Addition/ThetaAndQuotients.lean#L560) (proved).
- [22.8.E7](https://dlmf.nist.gov/22.8.E7): [`DLMF.JacobiElliptic.jacobiDc_add`](DLMF/JacobiElliptic/Addition/ThetaAndQuotients.lean#L598) (proved).
- [22.8.E8](https://dlmf.nist.gov/22.8.E8): [`DLMF.JacobiElliptic.jacobiNc_add`](DLMF/JacobiElliptic/Addition/ThetaAndQuotients.lean#L635) (proved).
- [22.8.E9](https://dlmf.nist.gov/22.8.E9): [`DLMF.JacobiElliptic.jacobiSc_add`](DLMF/JacobiElliptic/Addition/ThetaAndQuotients.lean#L671) (proved).
- [22.8.E10](https://dlmf.nist.gov/22.8.E10): [`DLMF.JacobiElliptic.jacobiNs_add`](DLMF/JacobiElliptic/Addition/ThetaAndQuotients.lean#L707) (proved).
- [22.8.E11](https://dlmf.nist.gov/22.8.E11): [`DLMF.JacobiElliptic.jacobiDs_add`](DLMF/JacobiElliptic/Addition/ThetaAndQuotients.lean#L743) (proved).
- [22.8.E12](https://dlmf.nist.gov/22.8.E12): [`DLMF.JacobiElliptic.jacobiCs_add`](DLMF/JacobiElliptic/Addition/ThetaAndQuotients.lean#L779) (proved).
- [22.8.E13](https://dlmf.nist.gov/22.8.E13): [`DLMF.JacobiElliptic.jacobiSn_add_alt`](DLMF/JacobiElliptic/Addition/SymmetricAndThreePoint.lean#L68) (proved).
- [22.8.E14](https://dlmf.nist.gov/22.8.E14): [`DLMF.JacobiElliptic.jacobiSn_add_alt₂`](DLMF/JacobiElliptic/Addition/SymmetricAndThreePoint.lean#L105) (proved).
- [22.8.E15](https://dlmf.nist.gov/22.8.E15): [`DLMF.JacobiElliptic.jacobiCn_add_alt`](DLMF/JacobiElliptic/Addition/SymmetricAndThreePoint.lean#L143) (proved).
- [22.8.E16](https://dlmf.nist.gov/22.8.E16): [`DLMF.JacobiElliptic.jacobiCn_add_alt₂`](DLMF/JacobiElliptic/Addition/SymmetricAndThreePoint.lean#L181) (proved).
- [22.8.E17](https://dlmf.nist.gov/22.8.E17): [`DLMF.JacobiElliptic.jacobiDn_add_alt`](DLMF/JacobiElliptic/Addition/SymmetricAndThreePoint.lean#L219) (proved).
- [22.8.E18](https://dlmf.nist.gov/22.8.E18): [`DLMF.JacobiElliptic.jacobiDn_add_alt₂`](DLMF/JacobiElliptic/Addition/SymmetricAndThreePoint.lean#L257) (proved).
- [22.8.E19](https://dlmf.nist.gov/22.8.E19): [`DLMF.JacobiElliptic.jacobi_det_sum_zero`](DLMF/JacobiElliptic/Addition/SymmetricAndThreePoint.lean#L515) (proved); [`DLMF.JacobiElliptic.jacobi_prod_sum_zero`](DLMF/JacobiElliptic/Addition/SymmetricAndThreePoint.lean#L524) (proved).
- [22.8.E20](https://dlmf.nist.gov/22.8.E20): [`DLMF.JacobiElliptic.jacobi_det_sum_zero`](DLMF/JacobiElliptic/Addition/SymmetricAndThreePoint.lean#L515) (proved).
- [22.8.E21](https://dlmf.nist.gov/22.8.E21): [`DLMF.JacobiElliptic.jacobi_prod_sum_zero`](DLMF/JacobiElliptic/Addition/SymmetricAndThreePoint.lean#L524) (proved).
- [22.8.E22](https://dlmf.nist.gov/22.8.E22): [`DLMF.JacobiElliptic.jacobi_det_sum_two_K`](DLMF/JacobiElliptic/Addition/SymmetricAndThreePoint.lean#L537) (proved); [`DLMF.JacobiElliptic.jacobi_det_sum_two_K'`](DLMF/JacobiElliptic/Addition/SymmetricAndThreePoint.lean#L551) (proved).
- [22.8.E23](https://dlmf.nist.gov/22.8.E23): [`DLMF.JacobiElliptic.jacobi_det_sum_two_K`](DLMF/JacobiElliptic/Addition/SymmetricAndThreePoint.lean#L537) (proved); [`DLMF.JacobiElliptic.jacobi_det_sum_two_K'`](DLMF/JacobiElliptic/Addition/SymmetricAndThreePoint.lean#L551) (proved). **Corrected** (DLMF erratum): as printed (columns sn cn, cn dn, cn, dn; Σz = 2K) the determinant is nonzero numerically (≈ -0.107 + 0.033i at k = 0.6). Two corrected forms acquired: third column sn (`jacobi_det_sum_two_K`) or second column sn dn (`jacobi_det_sum_two_K'`).
- [22.8.E24](https://dlmf.nist.gov/22.8.E24): [`DLMF.JacobiElliptic.jacobiDnThreePointExpr_const`](DLMF/JacobiElliptic/Addition/SymmetricAndThreePoint.lean#L574) (proved).
- [22.8.E25](https://dlmf.nist.gov/22.8.E25): [`DLMF.JacobiElliptic.jacobiDnThreePointExpr_const`](DLMF/JacobiElliptic/Addition/SymmetricAndThreePoint.lean#L574) (proved).
- [22.8.E26](https://dlmf.nist.gov/22.8.E26): [`DLMF.JacobiElliptic.jacobiDn_four_point`](DLMF/JacobiElliptic/Addition/SymmetricAndThreePoint.lean#L787) (proved from admitted foundations). 22.8.26–27 proved (from the shift table, via dn(z + 2K) = dn z and dn(z+K) = k'/dn z).
- [22.8.E27](https://dlmf.nist.gov/22.8.E27): [`DLMF.JacobiElliptic.jacobiDn_four_point`](DLMF/JacobiElliptic/Addition/SymmetricAndThreePoint.lean#L787) (proved from admitted foundations).

## [§22.9 Cyclic Identities](https://dlmf.nist.gov/22.9)

- [22.9.E1](https://dlmf.nist.gov/22.9.E1): [`DLMF.JacobiElliptic.jacobiCyclicArg`](DLMF/JacobiElliptic/Cyclic/QuarterPeriodAndThreePoint.lean#L44) (definition); [`DLMF.JacobiElliptic.jacobiCyclicS`](DLMF/JacobiElliptic/Cyclic/QuarterPeriodAndThreePoint.lean#L48) (definition). Cyclic quantities s, c, d of order 2 and 4 as functions of (m, p, z, k); `jacobiCyclicArg` encodes the shifted arguments.
- [22.9.E2](https://dlmf.nist.gov/22.9.E2): [`DLMF.JacobiElliptic.jacobiCyclicC`](DLMF/JacobiElliptic/Cyclic/QuarterPeriodAndThreePoint.lean#L52) (definition).
- [22.9.E3](https://dlmf.nist.gov/22.9.E3): [`DLMF.JacobiElliptic.jacobiCyclicD`](DLMF/JacobiElliptic/Cyclic/QuarterPeriodAndThreePoint.lean#L56) (definition).
- [22.9.E4](https://dlmf.nist.gov/22.9.E4): [`DLMF.JacobiElliptic.jacobiCyclicArg`](DLMF/JacobiElliptic/Cyclic/QuarterPeriodAndThreePoint.lean#L44) (definition); [`DLMF.JacobiElliptic.jacobiCyclicS`](DLMF/JacobiElliptic/Cyclic/QuarterPeriodAndThreePoint.lean#L48) (definition).
- [22.9.E5](https://dlmf.nist.gov/22.9.E5): [`DLMF.JacobiElliptic.jacobiCyclicC`](DLMF/JacobiElliptic/Cyclic/QuarterPeriodAndThreePoint.lean#L52) (definition).
- [22.9.E6](https://dlmf.nist.gov/22.9.E6): [`DLMF.JacobiElliptic.jacobiCyclicD`](DLMF/JacobiElliptic/Cyclic/QuarterPeriodAndThreePoint.lean#L56) (definition).
- [22.9.E7](https://dlmf.nist.gov/22.9.E7): [`DLMF.JacobiElliptic.jacobiCyclicKappa`](DLMF/JacobiElliptic/Cyclic/QuarterPeriodAndThreePoint.lean#L60) (definition); [`DLMF.JacobiElliptic.jacobi_cyclic_s4_pairs`](DLMF/JacobiElliptic/Cyclic/QuarterPeriodAndThreePoint.lean#L185) (proved); [`DLMF.JacobiElliptic.jacobi_cyclic_c4_pairs`](DLMF/JacobiElliptic/Cyclic/QuarterPeriodAndThreePoint.lean#L269) (proved); [`DLMF.JacobiElliptic.jacobi_cyclic_d_pairs`](DLMF/JacobiElliptic/Cyclic/QuarterPeriodAndThreePoint.lean#L433) (proved); [`DLMF.JacobiElliptic.jacobi_cyclic_s4_triple`](DLMF/JacobiElliptic/Cyclic/QuarterPeriodAndThreePoint.lean#L773) (proved); [`DLMF.JacobiElliptic.jacobi_cyclic_c4_triple`](DLMF/JacobiElliptic/Cyclic/TripleProducts.lean#L38) (proved); [`DLMF.JacobiElliptic.jacobi_cyclic_d2_triple`](DLMF/JacobiElliptic/Cyclic/TripleProducts.lean#L172) (proved); [`DLMF.JacobiElliptic.jacobi_cyclic_scc_triple`](DLMF/JacobiElliptic/Cyclic/TripleProducts.lean#L418) (proved); [`DLMF.JacobiElliptic.jacobi_cyclic_scdd_three`](DLMF/JacobiElliptic/Cyclic/MixedTripleProducts.lean#L41) (proved); [`DLMF.JacobiElliptic.jacobi_cyclic_sdcc_three`](DLMF/JacobiElliptic/Cyclic/MixedTripleProducts.lean#L569) (proved).
- [22.9.E8](https://dlmf.nist.gov/22.9.E8): [`DLMF.JacobiElliptic.jacobi_cyclic_s4_pairs`](DLMF/JacobiElliptic/Cyclic/QuarterPeriodAndThreePoint.lean#L185) (proved).
- [22.9.E9](https://dlmf.nist.gov/22.9.E9): [`DLMF.JacobiElliptic.jacobi_cyclic_c4_pairs`](DLMF/JacobiElliptic/Cyclic/QuarterPeriodAndThreePoint.lean#L269) (proved).
- [22.9.E10](https://dlmf.nist.gov/22.9.E10): [`DLMF.JacobiElliptic.jacobi_cyclic_d_pairs`](DLMF/JacobiElliptic/Cyclic/QuarterPeriodAndThreePoint.lean#L433) (proved).
- [22.9.E11](https://dlmf.nist.gov/22.9.E11): [`DLMF.JacobiElliptic.jacobi_cyclic_d2_two`](DLMF/JacobiElliptic/Cyclic/QuarterPeriodAndThreePoint.lean#L733) (proved).
- [22.9.E12](https://dlmf.nist.gov/22.9.E12): [`DLMF.JacobiElliptic.jacobi_cyclic_csd_two`](DLMF/JacobiElliptic/Cyclic/QuarterPeriodAndThreePoint.lean#L756) (proved).
- [22.9.E13](https://dlmf.nist.gov/22.9.E13): [`DLMF.JacobiElliptic.jacobi_cyclic_s4_triple`](DLMF/JacobiElliptic/Cyclic/QuarterPeriodAndThreePoint.lean#L773) (proved).
- [22.9.E14](https://dlmf.nist.gov/22.9.E14): [`DLMF.JacobiElliptic.jacobi_cyclic_c4_triple`](DLMF/JacobiElliptic/Cyclic/TripleProducts.lean#L38) (proved).
- [22.9.E15](https://dlmf.nist.gov/22.9.E15): [`DLMF.JacobiElliptic.jacobi_cyclic_d2_triple`](DLMF/JacobiElliptic/Cyclic/TripleProducts.lean#L172) (proved).
- [22.9.E16](https://dlmf.nist.gov/22.9.E16): [`DLMF.JacobiElliptic.jacobi_cyclic_scc_triple`](DLMF/JacobiElliptic/Cyclic/TripleProducts.lean#L418) (proved).
- [22.9.E17](https://dlmf.nist.gov/22.9.E17): [`DLMF.JacobiElliptic.jacobi_cyclic_d2_four`](DLMF/JacobiElliptic/Cyclic/TripleProducts.lean#L594) (proved).
- [22.9.E18](https://dlmf.nist.gov/22.9.E18): [`DLMF.JacobiElliptic.jacobi_cyclic_d2_four_sq`](DLMF/JacobiElliptic/Cyclic/TripleProducts.lean#L627) (proved).
- [22.9.E19](https://dlmf.nist.gov/22.9.E19): [`DLMF.JacobiElliptic.jacobi_cyclic_csd_four`](DLMF/JacobiElliptic/Cyclic/TripleProducts.lean#L658) (proved).
- [22.9.E20](https://dlmf.nist.gov/22.9.E20): [`DLMF.JacobiElliptic.jacobi_cyclic_d2_two_rank4`](DLMF/JacobiElliptic/Cyclic/TripleProducts.lean#L683) (proved).
- [22.9.E21](https://dlmf.nist.gov/22.9.E21): [`DLMF.JacobiElliptic.jacobi_cyclic_cscs_two`](DLMF/JacobiElliptic/Cyclic/TripleProducts.lean#L704) (proved).
- [22.9.E22](https://dlmf.nist.gov/22.9.E22): [`DLMF.JacobiElliptic.jacobi_cyclic_scdd_three`](DLMF/JacobiElliptic/Cyclic/MixedTripleProducts.lean#L41) (proved).
- [22.9.E23](https://dlmf.nist.gov/22.9.E23): [`DLMF.JacobiElliptic.jacobi_cyclic_sdcc_three`](DLMF/JacobiElliptic/Cyclic/MixedTripleProducts.lean#L569) (proved). **Corrected** (DLMF erratum): printed right side repeats s₂,₃d₂,₃; corrected last summand s₃,₃d₃,₃ (printed RHS ≈ 4.208 - 0.036i vs LHS ≈ 0.552 + 0.183i at k = 0.6, z = 0.37 + 0.21i).
## Analytical prose and exclusions (part A)

- [22.1.p1](https://dlmf.nist.gov/22.1#p1): notation pointer; no mathematical content.
- [22.1.p2](https://dlmf.nist.gov/22.1#p2): notation for x, y, z, k, k', K, K', q, τ; `jacobiComodulus` (principal (1-k²)^{1/2}) with `jacobiComodulus_sq` (proved), `compEllIntKk`, `completeEllipticKPrime`, `jacobiNome`, `jacobiTau`. The DLMF restriction 0 ≤ k ≤ 1 is widened to `jacobiModulusDomain` as explained above.
- [22.1.p3](https://dlmf.nist.gov/22.1#p3): typographical convention (derivatives as differentials).
- [22.1.p4](https://dlmf.nist.gov/22.1#p4): the twelve functions `jacobiSnk` … `jacobiCs` (and `jacobiSnOfTau` … `jacobiCsOfTau`), generic `jacobiPQ` with `JacobiLetter`.
- [22.1.p5](https://dlmf.nist.gov/22.1#p5): historical notation; excluded: bibliographic.
- [22.2.p1](https://dlmf.nist.gov/22.2#p1), [22.2.p2](https://dlmf.nist.gov/22.2#p2): carry 22.2.1–22.2.9, recorded above.
- [22.2.p3](https://dlmf.nist.gov/22.2#p3): double periodicity (`jacobiXxk_periodic`, proved from foundations), meromorphy in z (`jacobiPQ_meromorphicAt`, proved from foundations), meromorphy in k (`jacobiPQ_meromorphicOn_modulus`, admitted), reality for real z and k ∈ (0, 1) (`jacobiPQ_real`, admitted; existing real theory in `DLMF/Elliptic/Jacobi.lean`); simple poles and zeros in `jacobiPQ_zeros_poles` (admitted). Lean tag `22.2`.
- [22.2.Px1.p1](https://dlmf.nist.gov/22.2#Px1.p1): carries 22.2.10.
- [22.2.Px1.p2](https://dlmf.nist.gov/22.2#Px1.p2): parity: `jacobiPQ_neg` (proved, admission-free), `jacobiLetterTheta_neg`, `jacobiThetaArgument_neg`; real `DLMF.Elliptic.jacobi_neg`. Lean tag `22.2`.
- [22.2.Px1.p3](https://dlmf.nist.gov/22.2#Px1.p3): carries 22.2.11–22.2.12.
- [22.2](https://dlmf.nist.gov/22.2): [`DLMF.Elliptic.jacobi_neg`](DLMF/Elliptic/Basic/Jacobi.lean#L253) (proved); [`DLMF.JacobiElliptic.jacobiPQ_meromorphicAt`](DLMF/JacobiElliptic/AnalyticProperties.lean#L292) (proved); [`DLMF.JacobiElliptic.jacobiPQ_meromorphicOn_modulus`](DLMF/JacobiElliptic/AnalyticProperties.lean#L166) (proved); [`DLMF.JacobiElliptic.jacobiPQ_neg`](DLMF/JacobiElliptic/Basic/Properties.lean#L73) (proved); [`DLMF.JacobiElliptic.jacobiPQ_real`](DLMF/JacobiElliptic/AnalyticProperties.lean#L259) (proved).
- [22.4.i.p1](https://dlmf.nist.gov/22.4#i.p1), [22.4.i.p3](https://dlmf.nist.gov/22.4#i.p3): poles and zeros at the congruent points z₀ + 2mK + 2niK': `jacobiCongruentk`, `jacobiLetterPointk`, `jacobiPQ_zeros_poles` (admitted; tagged 22.4.T1, 22.4.T2, 22.4.ii).
- [22.4.i.p2](https://dlmf.nist.gov/22.4#i.p2): copolar/coperiodic terminology; content is in Tables 22.4.1–2.
- [22.4.i.p4](https://dlmf.nist.gov/22.4#i.p4): excluded: graphics (Figure 22.4.1).
- [22.4.i.p5](https://dlmf.nist.gov/22.4#i.p5): k-zeros, bibliographic pointer (Walker 2009); excluded: bibliographic.
- [22.4.ii.p1](https://dlmf.nist.gov/22.4#ii.p1), [22.4.ii.p2](https://dlmf.nist.gov/22.4#ii.p2): the lattice mK + niK' and the unit-cell mnemonic: pq has a simple zero at p and a simple pole at q, and the half-periods/periods follow; `jacobiPQ_zeros_poles` (admitted, tag 22.4.ii) with the periods from Table 22.4.3. Figure 22.4.2 itself excluded: graphics.
- [22.4.iii.p1](https://dlmf.nist.gov/22.4#iii.p1), [22.4.iii.p2](https://dlmf.nist.gov/22.4#iii.p2): Table 22.4.3, recorded above.
- [22.4.ii](https://dlmf.nist.gov/22.4.ii): [`DLMF.JacobiElliptic.jacobiPQ_zeros_poles`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L1029) (proved).
- [22.5.i.p1](https://dlmf.nist.gov/22.5#i.p1), [22.5.i.p2](https://dlmf.nist.gov/22.5#i.p2): Tables 22.5.1–22.5.2 (recorded above); "for the other nine functions ratios can be taken" is 22.2.10.
- [22.5.ii.p1](https://dlmf.nist.gov/22.5#ii.p1): K → π/2 as k → 0+ (`tendsto_completeEllipticK_zero`, proved), K' → π/2 as k → 1- (`tendsto_completeEllipticKPrime_one`, proved), |K'| → ∞ as k → 0+ and |K| → ∞ as k → 1- (`tendsto_norm_completeEllipticKPrime_zero`, `tendsto_norm_completeEllipticK_one`, admitted); degeneration in Tables 22.5.3–22.5.4. Lean tag `22.5.ii`.
- [22.5.ii.p2](https://dlmf.nist.gov/22.5#ii.p2): cross-reference to §§19.5, 19.12; excluded: cross-reference.
- [22.5.ii.p3](https://dlmf.nist.gov/22.5#ii.p3): lemniscatic and equianharmonic values of K, K', cross-reference to §23.5(iii), §23.5(v); excluded: cross-reference (Chapter 23 acquisition).
- [22.5.ii](https://dlmf.nist.gov/22.5.ii): [`DLMF.JacobiElliptic.tendsto_completeEllipticK_zero`](DLMF/JacobiElliptic/SpecialValues/RealAndHalfPeriods.lean#L985) (proved); [`DLMF.JacobiElliptic.tendsto_completeEllipticKPrime_one`](DLMF/JacobiElliptic/SpecialValues/RealAndHalfPeriods.lean#L1002) (proved); [`DLMF.JacobiElliptic.tendsto_norm_completeEllipticK_one`](DLMF/JacobiElliptic/SpecialValues/RealAndHalfPeriods.lean#L1093) (proved); [`DLMF.JacobiElliptic.tendsto_norm_completeEllipticKPrime_zero`](DLMF/JacobiElliptic/SpecialValues/RealAndHalfPeriods.lean#L1081) (proved).
- [22.6.i.p1](https://dlmf.nist.gov/22.6#i.p1), [22.6.ii.p1](https://dlmf.nist.gov/22.6#ii.p1), [22.6.ii.p2](https://dlmf.nist.gov/22.6#ii.p2), [22.6.ii.p4](https://dlmf.nist.gov/22.6#ii.p4), [22.6.iii.p1](https://dlmf.nist.gov/22.6#iii.p1), [22.6.iii.p2](https://dlmf.nist.gov/22.6#iii.p2): carry 22.6.1–22.6.22 (22.6.22 for every permutation p, q, r of c, d, n, as `jacobiPQ_half_sq`).
- [22.6.ii.p3](https://dlmf.nist.gov/22.6#ii.p3), [22.6.v.p1](https://dlmf.nist.gov/22.6#v.p1): pointers to Carlson (2004) and §22.17; excluded: bibliographic/cross-reference. 22.6(iv) is Table 22.6.1, recorded above.
- [22.7.i.p1](https://dlmf.nist.gov/22.7#i.p1), [22.7.ii.p1](https://dlmf.nist.gov/22.7#ii.p1): carry 22.7.1–22.7.8.
- [22.7.iii.p1](https://dlmf.nist.gov/22.7#iii.p1): pointer to Khare and Sukhatme (2004); excluded: bibliographic.
- [22.8.i.p1](https://dlmf.nist.gov/22.8#i.p1), [22.8.i.p2](https://dlmf.nist.gov/22.8#i.p2), [22.8.ii.p1](https://dlmf.nist.gov/22.8#ii.p1), [22.8.iii.p1](https://dlmf.nist.gov/22.8#iii.p1), [22.8.iii.p2](https://dlmf.nist.gov/22.8#iii.p2), [22.8.iii.p4](https://dlmf.nist.gov/22.8#iii.p4)–[22.8.iii.p6](https://dlmf.nist.gov/22.8#iii.p6): carry 22.8.1–22.8.27 for all u, v ∈ ℂ (with the regularity hypotheses above).
- [22.8.i.p3](https://dlmf.nist.gov/22.8#i.p3), [22.8.ii.p2](https://dlmf.nist.gov/22.8#ii.p2), [22.8.iii.p3](https://dlmf.nist.gov/22.8#iii.p3): pointers to Carlson (2004) and a geometric interpretation in Whittaker and Watson; excluded: bibliographic.
- [22.9.i.p1](https://dlmf.nist.gov/22.9#i.p1): attribution; excluded: bibliographic.
- [22.9.i.p2](https://dlmf.nist.gov/22.9#i.p2), [22.9.ii.p1](https://dlmf.nist.gov/22.9#ii.p1): index ranges 1 ≤ m, n ≤ p are hypotheses of the cyclic definitions and identities.
- [22.9.i.p3](https://dlmf.nist.gov/22.9#i.p3): rank terminology; "all cyclic identities are independent of z" is the content of the identities, stated for every z.
- [22.9.Px1.p1](https://dlmf.nist.gov/22.9#Px1.p1)–[22.9.Px6.p1](https://dlmf.nist.gov/22.9#Px6.p1): carry 22.9.7–22.9.23; Px1.p2 (cyclic-permutation remark) is terminology.
- [22.9.v.p1](https://dlmf.nist.gov/22.9#v.p1): pointer to extensions; excluded: bibliographic.

## Validation (part A)

- Numerical checks (mpmath `ellipfun`, `ellipk`, `jtheta`; scripts outside the project) of
  every formula in §§22.2, 22.4–22.9 at k = 0.6, 0.5 + 0.3i and 1.3 + 0.4i with generic
  complex arguments; failures only at the three corrected entries and the 22.7.5 branch note.
- `lake build DLMF.JacobiElliptic` passes. Strict checks with `autoImplicit=false` and
  `relaxedAutoImplicit=false` pass with no errors and no warnings besides `sorry` for every
  part-A module and for `DLMF/Elliptic/Jacobi.lean` and `DLMF/Elliptic/JacobiIdentities.lean`.
- The `#print axioms` audit of all tagged part-A declarations reports only `propext`,
  `Classical.choice`, `Quot.sound` and, for admissions and their dependents, `sorryAx`.
  No definition depends on `sorryAx`.
- The numbered source inventory of §§22.2, 22.4–22.9 has no unexplained gap.

## Part B summary

Part B covers [§22.10](https://dlmf.nist.gov/22.10)–[§22.17](https://dlmf.nist.gov/22.17)
of DLMF Chapter 22 (version 1.2.8, checked on 2026-10-25), plus the excluded §22.3 and
§§22.18–22.22. All 143 numbered equation slots of §§22.10–22.17 and Table 22.13.T1 are in
scope and covered. The new modules are `DLMF.JacobiElliptic.{Maclaurin, FourierSeries,
PartialFractions, Derivatives, Integrals, Inverse, Related, OutsideModuli}`. They build on the
complex Glaisher functions `jacobiPQ` of `DLMF.JacobiElliptic.Basic`, and their real-parameter
statements use the existing `DLMF.Elliptic.Real.jacobi*m` functions. Of the 192 tagged
declarations, 14 are definitions, 65 are proved and 113 are admitted. Mathlib and TauCeti
have no Jacobian elliptic functions, so there are no upstream pointers.

## Domains, conventions and source corrections (part B)

- Complex statements assume `k ∈ jacobiModulusDomain`. Derivative statements also assume
  that the theta denominator is nonzero. Real statements use `0 < k < 1` (`m = k²`) or `m < 1`.
- `Real.jacobiAmOfParameter` is totalized (`am(x, m) = x` for `m ≥ 1`). So 22.16.E5 (`am(x,1) = gd x`)
  is stated as the limit `k → 1⁻`.
- 22.14.E2 and E6 use the principal `arccos`, which is valid for `0 < x < 2K`. DLMF's
  `Arccos` is multivalued, and the principal form fails for `x < 0`. This is a domain
  restriction, not an erratum.
- 22.16.E13: the converse direction needs `0 ≤ x` and `0 ≤ φ`, because `cos` is even.
- 22.16.E14 is the corrected form (DLMF erratum of 2010-07-08, Karney).
- Stronger than DLMF: 22.15.E11 (`|x| ≤ K` instead of `-1 ≤ x ≤ 1`), 22.16.E31 (all real `x`)
  and 22.17.E1 (all complex `z, k`).
- 22.17.E2–E4 and E6–E8 are stated for complex moduli, with both moduli involved in
  `jacobiModulusDomain` (§22.17(ii): the functions are meromorphic in `k²`). For real
  `1/k > 1` and for imaginary `ik`, the literal definition uses principal branches of `K'`
  that are not the analytic continuation, so those moduli are not covered.
- Naming: Jacobi's Zeta function (22.16.E32) is `Real.jacobiZeta`. This avoids
  `jacobiThetaArgument`, which in Basic denotes the theta argument `ζ = πz/(2K)`. Jacobi's Epsilon
  function (22.16.E17) is `Real.jacobiEpsilon`.
- Tag corrections (done by the coordinator, 2026-10-25): in `DLMF/Elliptic/Jacobi.lean`,
  `Real.hasDerivAt_jacobiSnOfParameter/Cnm/Dnm` are retagged Table 22.13.T1 (they were tagged 22.13.E1–E3);
  `Real.jacobiSnOfParameter_deriv_sq/Cnm/Dnm` now carry 22.13.E1–E3 and `Real.iteratedDeriv_two_jacobiSnOfParameter/Cnm/Dnm`
  22.13.E13–E15, with their docstrings renumbered; `Real.jacobiSnOfParameter_jacobiArcsnOfParameter` and `Real.jacobiArcsnOfParameter`
  carry 22.15.E1 and E4; `Real.jacobiAmOfParameter_add_two_completeEllipticKOfParameter`, `Real.jacobiAmOfParameter_zero_param`,
  `Real.incompleteEllipticFOfParameter_jacobiAmOfParameter` and `Real.hasDerivAt_jacobiAmOfParameter` carry 22.16.E2, E4, E11 and 22.16.i.
- No DLMF errata were found.

## Numbered formulas (part B)

## [§22.10 Maclaurin Series](https://dlmf.nist.gov/22.10)

- [22.10.E1](https://dlmf.nist.gov/22.10.E1): [`DLMF.JacobiElliptic.jacobiSn_isBigO_maclaurin`](DLMF/JacobiElliptic/Maclaurin.lean#L249) (proved). Domain: k ∈ jacobiModulusDomain.
- [22.10.E2](https://dlmf.nist.gov/22.10.E2): [`DLMF.JacobiElliptic.jacobiCn_isBigO_maclaurin`](DLMF/JacobiElliptic/Maclaurin.lean#L258) (proved). Domain: k ∈ jacobiModulusDomain.
- [22.10.E3](https://dlmf.nist.gov/22.10.E3): [`DLMF.JacobiElliptic.jacobiDn_isBigO_maclaurin`](DLMF/JacobiElliptic/Maclaurin.lean#L266) (proved). Domain: k ∈ jacobiModulusDomain.
- [22.10.E4](https://dlmf.nist.gov/22.10.E4): [`DLMF.JacobiElliptic.jacobiSn_isBigO_small_modulus`](DLMF/JacobiElliptic/Maclaurin.lean#L309) (admitted). Domain: k → 0 within jacobiModulusDomain, fixed z.
- [22.10.E5](https://dlmf.nist.gov/22.10.E5): [`DLMF.JacobiElliptic.jacobiCn_isBigO_small_modulus`](DLMF/JacobiElliptic/Maclaurin.lean#L317) (admitted). Domain: k → 0 within jacobiModulusDomain, fixed z.
- [22.10.E6](https://dlmf.nist.gov/22.10.E6): [`DLMF.JacobiElliptic.jacobiDn_isBigO_small_modulus`](DLMF/JacobiElliptic/Maclaurin.lean#L325) (admitted). Domain: k → 0 within jacobiModulusDomain, fixed z.
- [22.10.E7](https://dlmf.nist.gov/22.10.E7): [`DLMF.JacobiElliptic.jacobiSn_isBigO_small_comodulus`](DLMF/JacobiElliptic/Maclaurin.lean#L332) (admitted). Domain: k → 1 within jacobiModulusDomain, fixed z with cosh z ≠ 0.
- [22.10.E8](https://dlmf.nist.gov/22.10.E8): [`DLMF.JacobiElliptic.jacobiCn_isBigO_small_comodulus`](DLMF/JacobiElliptic/Maclaurin.lean#L340) (admitted). Domain: k → 1 within jacobiModulusDomain, fixed z with cosh z ≠ 0.
- [22.10.E9](https://dlmf.nist.gov/22.10.E9): [`DLMF.JacobiElliptic.jacobiDn_isBigO_small_comodulus`](DLMF/JacobiElliptic/Maclaurin.lean#L349) (admitted). Domain: k → 1 within jacobiModulusDomain, fixed z with cosh z ≠ 0.
- [22.10.i](https://dlmf.nist.gov/22.10#i): [`DLMF.JacobiElliptic.jacobi_hasFPowerSeriesOnBall`](DLMF/JacobiElliptic/Maclaurin.lean#L274) (proved). Prose convergence statement (disc |z| < min(K,K')), real 0<k<1.

## [§22.11 Fourier and Hyperbolic Series](https://dlmf.nist.gov/22.11)

- [22.11.E1](https://dlmf.nist.gov/22.11.E1): [`DLMF.JacobiElliptic.jacobiSn_hasSum_fourier`](DLMF/JacobiElliptic/FourierSeries.lean#L94) (proved). Domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition.
- [22.11.E2](https://dlmf.nist.gov/22.11.E2): [`DLMF.JacobiElliptic.jacobiCn_hasSum_fourier`](DLMF/JacobiElliptic/FourierSeries.lean#L129) (proved). Domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition.
- [22.11.E3](https://dlmf.nist.gov/22.11.E3): [`DLMF.JacobiElliptic.jacobiDn_hasSum_fourier`](DLMF/JacobiElliptic/FourierSeries.lean#L169) (proved). Domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition.
- [22.11.E4](https://dlmf.nist.gov/22.11.E4): [`DLMF.JacobiElliptic.jacobiCd_hasSum_fourier`](DLMF/JacobiElliptic/FourierSeries.lean#L219) (proved). Domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition.
- [22.11.E5](https://dlmf.nist.gov/22.11.E5): [`DLMF.JacobiElliptic.jacobiSd_hasSum_fourier`](DLMF/JacobiElliptic/FourierSeries.lean#L238) (proved). Domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition.
- [22.11.E6](https://dlmf.nist.gov/22.11.E6): [`DLMF.JacobiElliptic.jacobiNd_hasSum_fourier`](DLMF/JacobiElliptic/FourierSeries.lean#L261) (proved). Domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition.
- [22.11.E7](https://dlmf.nist.gov/22.11.E7): [`DLMF.JacobiElliptic.jacobiNs_hasSum_fourier`](DLMF/JacobiElliptic/FourierSeries.lean#L286) (proved). Domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition.
- [22.11.E8](https://dlmf.nist.gov/22.11.E8): [`DLMF.JacobiElliptic.jacobiDs_hasSum_fourier`](DLMF/JacobiElliptic/FourierSeries.lean#L333) (proved). Domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition.
- [22.11.E9](https://dlmf.nist.gov/22.11.E9): [`DLMF.JacobiElliptic.jacobiCs_hasSum_fourier`](DLMF/JacobiElliptic/FourierSeries.lean#L385) (proved). Domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition.
- [22.11.E10](https://dlmf.nist.gov/22.11.E10): [`DLMF.JacobiElliptic.jacobiDc_hasSum_fourier`](DLMF/JacobiElliptic/FourierSeries.lean#L422) (proved). Domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition.
- [22.11.E11](https://dlmf.nist.gov/22.11.E11): [`DLMF.JacobiElliptic.jacobiNc_hasSum_fourier`](DLMF/JacobiElliptic/FourierSeries.lean#L442) (proved). Domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition.
- [22.11.E12](https://dlmf.nist.gov/22.11.E12): [`DLMF.JacobiElliptic.jacobiSc_hasSum_fourier`](DLMF/JacobiElliptic/FourierSeries.lean#L467) (proved). Domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition.
- [22.11.E13](https://dlmf.nist.gov/22.11.E13): [`DLMF.JacobiElliptic.jacobiSn_sq_hasSum_fourier`](DLMF/JacobiElliptic/FourierSeries/SquaredSn.lean#L32) (proved). Real 0<k<1 (complete E(k) has no complex counterpart in the library).
- [22.11.E14](https://dlmf.nist.gov/22.11.E14): [`DLMF.JacobiElliptic.jacobiSn_sq_hasSum_sech`](DLMF/JacobiElliptic/FourierSeries/HyperbolicSn.lean#L122) (proved). Real 0<k<1.

## [§22.12 Expansions in Other Trigonometric Series](https://dlmf.nist.gov/22.12)

- [22.12.E1](https://dlmf.nist.gov/22.12.E1): [`DLMF.JacobiElliptic.jacobiTau_eq`](DLMF/JacobiElliptic/PartialFractions.lean#L67) (proved). Definitional (rfl) against `jacobiTau`.
- [22.12.E2](https://dlmf.nist.gov/22.12.E2): [`DLMF.JacobiElliptic.jacobiSn_partialFractions`](DLMF/JacobiElliptic/PartialFractions.lean#L78) (proved). Domain: k ∈ jacobiModulusDomain, t not a pole.
- [22.12.E3](https://dlmf.nist.gov/22.12.E3): [`DLMF.JacobiElliptic.jacobiCn_partialFractions`](DLMF/JacobiElliptic/PartialFractions.lean#L104) (proved). Domain: k ∈ jacobiModulusDomain, t not a pole.
- [22.12.E4](https://dlmf.nist.gov/22.12.E4): [`DLMF.JacobiElliptic.jacobiDn_partialFractions`](DLMF/JacobiElliptic/PartialFractions.lean#L129) (proved). Domain: k ∈ jacobiModulusDomain, t not a pole.
- [22.12.E5](https://dlmf.nist.gov/22.12.E5): [`DLMF.JacobiElliptic.jacobiCd_partialFractions`](DLMF/JacobiElliptic/PartialFractions.lean#L158) (proved). Domain: k ∈ jacobiModulusDomain, t not a pole.
- [22.12.E6](https://dlmf.nist.gov/22.12.E6): [`DLMF.JacobiElliptic.jacobiSd_partialFractions`](DLMF/JacobiElliptic/PartialFractions.lean#L184) (proved). Domain: k ∈ jacobiModulusDomain, t not a pole.
- [22.12.E7](https://dlmf.nist.gov/22.12.E7): [`DLMF.JacobiElliptic.jacobiNd_partialFractions`](DLMF/JacobiElliptic/PartialFractions.lean#L211) (proved). Domain: k ∈ jacobiModulusDomain, t not a pole.
- [22.12.E8](https://dlmf.nist.gov/22.12.E8): [`DLMF.JacobiElliptic.jacobiDc_partialFractions`](DLMF/JacobiElliptic/PartialFractions.lean#L251) (proved). Domain: k ∈ jacobiModulusDomain, t not a pole.
- [22.12.E9](https://dlmf.nist.gov/22.12.E9): [`DLMF.JacobiElliptic.jacobiNc_partialFractions`](DLMF/JacobiElliptic/PartialFractions.lean#L271) (proved). Domain: k ∈ jacobiModulusDomain, t not a pole.
- [22.12.E10](https://dlmf.nist.gov/22.12.E10): [`DLMF.JacobiElliptic.jacobiSc_partialFractions`](DLMF/JacobiElliptic/PartialFractions.lean#L291) (proved). Domain: k ∈ jacobiModulusDomain, t not a pole.
- [22.12.E11](https://dlmf.nist.gov/22.12.E11): [`DLMF.JacobiElliptic.jacobiNs_partialFractions`](DLMF/JacobiElliptic/PartialFractions.lean#L320) (proved). Domain: k ∈ jacobiModulusDomain, t not a pole.
- [22.12.E12](https://dlmf.nist.gov/22.12.E12): [`DLMF.JacobiElliptic.jacobiDs_partialFractions`](DLMF/JacobiElliptic/PartialFractions.lean#L335) (proved). Domain: k ∈ jacobiModulusDomain, t not a pole.
- [22.12.E13](https://dlmf.nist.gov/22.12.E13): [`DLMF.JacobiElliptic.jacobiCs_partialFractions`](DLMF/JacobiElliptic/PartialFractions.lean#L350) (proved). Domain: k ∈ jacobiModulusDomain, t not a pole.

## [§22.13 Derivatives and Differential Equations](https://dlmf.nist.gov/22.13)

- [22.13.E1](https://dlmf.nist.gov/22.13.E1): [`DLMF.JacobiElliptic.deriv_jacobiSn_sq`](DLMF/JacobiElliptic/Derivatives/ComplexEquations.lean#L57) (proved); [`DLMF.Elliptic.Real.jacobiSnOfParameter_deriv_sq`](DLMF/Elliptic/JacobiIdentities.lean#L61) (proved). Complex new statement; real m<1 form pre-existing (tagged in source).
- [22.13.E2](https://dlmf.nist.gov/22.13.E2): [`DLMF.JacobiElliptic.deriv_jacobiCn_sq`](DLMF/JacobiElliptic/Derivatives/ComplexEquations.lean#L70) (proved); [`DLMF.Elliptic.Real.jacobiCnOfParameter_deriv_sq`](DLMF/Elliptic/JacobiIdentities.lean#L72) (proved). As E1.
- [22.13.E3](https://dlmf.nist.gov/22.13.E3): [`DLMF.JacobiElliptic.deriv_jacobiDn_sq`](DLMF/JacobiElliptic/Derivatives/ComplexEquations.lean#L84) (proved); [`DLMF.Elliptic.Real.jacobiDnOfParameter_deriv_sq`](DLMF/Elliptic/JacobiIdentities.lean#L84) (proved). As E1.
- [22.13.E4](https://dlmf.nist.gov/22.13.E4): [`DLMF.JacobiElliptic.deriv_jacobiCd_sq`](DLMF/JacobiElliptic/Derivatives/ComplexEquations.lean#L99) (proved); [`DLMF.JacobiElliptic.Real.deriv_jacobiCdm_sq`](DLMF/JacobiElliptic/Derivatives/RealEquations.lean#L183) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E5](https://dlmf.nist.gov/22.13.E5): [`DLMF.JacobiElliptic.deriv_jacobiSd_sq`](DLMF/JacobiElliptic/Derivatives/ComplexEquations.lean#L114) (proved); [`DLMF.JacobiElliptic.Real.deriv_jacobiSdm_sq`](DLMF/JacobiElliptic/Derivatives/RealEquations.lean#L200) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E6](https://dlmf.nist.gov/22.13.E6): [`DLMF.JacobiElliptic.deriv_jacobiNd_sq`](DLMF/JacobiElliptic/Derivatives/ComplexEquations.lean#L127) (proved); [`DLMF.JacobiElliptic.Real.deriv_jacobiNdm_sq`](DLMF/JacobiElliptic/Derivatives/RealEquations.lean#L217) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E7](https://dlmf.nist.gov/22.13.E7): [`DLMF.JacobiElliptic.deriv_jacobiDc_sq`](DLMF/JacobiElliptic/Derivatives/ComplexEquations.lean#L141) (proved); [`DLMF.JacobiElliptic.Real.deriv_jacobiDcm_sq`](DLMF/JacobiElliptic/Derivatives/RealEquations.lean#L232) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E8](https://dlmf.nist.gov/22.13.E8): [`DLMF.JacobiElliptic.deriv_jacobiNc_sq`](DLMF/JacobiElliptic/Derivatives/ComplexEquations.lean#L155) (proved); [`DLMF.JacobiElliptic.Real.deriv_jacobiNcm_sq`](DLMF/JacobiElliptic/Derivatives/RealEquations.lean#L248) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E9](https://dlmf.nist.gov/22.13.E9): [`DLMF.JacobiElliptic.deriv_jacobiSc_sq`](DLMF/JacobiElliptic/Derivatives/ComplexEquations.lean#L169) (proved); [`DLMF.JacobiElliptic.Real.deriv_jacobiScm_sq`](DLMF/JacobiElliptic/Derivatives/RealEquations.lean#L262) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E10](https://dlmf.nist.gov/22.13.E10): [`DLMF.JacobiElliptic.deriv_jacobiNs_sq`](DLMF/JacobiElliptic/Derivatives/ComplexEquations.lean#L181) (proved); [`DLMF.JacobiElliptic.Real.deriv_jacobiNsm_sq`](DLMF/JacobiElliptic/Derivatives/RealEquations.lean#L278) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E11](https://dlmf.nist.gov/22.13.E11): [`DLMF.JacobiElliptic.deriv_jacobiDs_sq`](DLMF/JacobiElliptic/Derivatives/ComplexEquations.lean#L194) (proved); [`DLMF.JacobiElliptic.Real.deriv_jacobiDsm_sq`](DLMF/JacobiElliptic/Derivatives/RealEquations.lean#L291) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E12](https://dlmf.nist.gov/22.13.E12): [`DLMF.JacobiElliptic.deriv_jacobiCs_sq`](DLMF/JacobiElliptic/Derivatives/ComplexEquations.lean#L207) (proved); [`DLMF.JacobiElliptic.Real.deriv_jacobiCsm_sq`](DLMF/JacobiElliptic/Derivatives/RealEquations.lean#L308) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E13](https://dlmf.nist.gov/22.13.E13): [`DLMF.JacobiElliptic.iteratedDeriv_two_jacobiSn`](DLMF/JacobiElliptic/Derivatives/ComplexEquations.lean#L221) (proved); [`DLMF.Elliptic.Real.iteratedDeriv_two_jacobiSnOfParameter`](DLMF/Elliptic/JacobiIdentities.lean#L343) (proved). Complex new statement; real m<1 form pre-existing (untagged).
- [22.13.E14](https://dlmf.nist.gov/22.13.E14): [`DLMF.JacobiElliptic.iteratedDeriv_two_jacobiCn`](DLMF/JacobiElliptic/Derivatives/ComplexEquations.lean#L239) (proved); [`DLMF.Elliptic.Real.iteratedDeriv_two_jacobiCnOfParameter`](DLMF/Elliptic/JacobiIdentities.lean#L359) (proved). As E13.
- [22.13.E15](https://dlmf.nist.gov/22.13.E15): [`DLMF.JacobiElliptic.iteratedDeriv_two_jacobiDn`](DLMF/JacobiElliptic/Derivatives/ComplexEquations.lean#L258) (proved); [`DLMF.Elliptic.Real.iteratedDeriv_two_jacobiDnOfParameter`](DLMF/Elliptic/JacobiIdentities.lean#L376) (proved). As E13.
- [22.13.E16](https://dlmf.nist.gov/22.13.E16): [`DLMF.JacobiElliptic.iteratedDeriv_two_jacobiCd`](DLMF/JacobiElliptic/Derivatives/ComplexEquations.lean#L278) (proved); [`DLMF.JacobiElliptic.Real.iteratedDeriv_two_jacobiCdm`](DLMF/JacobiElliptic/Derivatives/RealEquations.lean#L326) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E17](https://dlmf.nist.gov/22.13.E17): [`DLMF.JacobiElliptic.iteratedDeriv_two_jacobiSd`](DLMF/JacobiElliptic/Derivatives/ComplexEquations.lean#L297) (proved); [`DLMF.JacobiElliptic.Real.iteratedDeriv_two_jacobiSdm`](DLMF/JacobiElliptic/Derivatives/RealEquations.lean#L350) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E18](https://dlmf.nist.gov/22.13.E18): [`DLMF.JacobiElliptic.iteratedDeriv_two_jacobiNd`](DLMF/JacobiElliptic/Derivatives/ComplexEquations.lean#L316) (proved); [`DLMF.JacobiElliptic.Real.iteratedDeriv_two_jacobiNdm`](DLMF/JacobiElliptic/Derivatives/RealEquations.lean#L374) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E19](https://dlmf.nist.gov/22.13.E19): [`DLMF.JacobiElliptic.iteratedDeriv_two_jacobiDc`](DLMF/JacobiElliptic/Derivatives/ComplexEquations.lean#L336) (proved); [`DLMF.JacobiElliptic.Real.iteratedDeriv_two_jacobiDcm`](DLMF/JacobiElliptic/Derivatives/RealEquations.lean#L392) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E20](https://dlmf.nist.gov/22.13.E20): [`DLMF.JacobiElliptic.iteratedDeriv_two_jacobiNc`](DLMF/JacobiElliptic/Derivatives/ComplexEquations.lean#L355) (proved); [`DLMF.JacobiElliptic.Real.iteratedDeriv_two_jacobiNcm`](DLMF/JacobiElliptic/Derivatives/RealEquations.lean#L417) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E21](https://dlmf.nist.gov/22.13.E21): [`DLMF.JacobiElliptic.iteratedDeriv_two_jacobiSc`](DLMF/JacobiElliptic/Derivatives/ComplexEquations.lean#L374) (proved); [`DLMF.JacobiElliptic.Real.iteratedDeriv_two_jacobiScm`](DLMF/JacobiElliptic/Derivatives/RealEquations.lean#L440) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E22](https://dlmf.nist.gov/22.13.E22): [`DLMF.JacobiElliptic.iteratedDeriv_two_jacobiNs`](DLMF/JacobiElliptic/Derivatives/ComplexEquations.lean#L392) (proved); [`DLMF.JacobiElliptic.Real.iteratedDeriv_two_jacobiNsm`](DLMF/JacobiElliptic/Derivatives/RealEquations.lean#L465) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E23](https://dlmf.nist.gov/22.13.E23): [`DLMF.JacobiElliptic.iteratedDeriv_two_jacobiDs`](DLMF/JacobiElliptic/Derivatives/ComplexEquations.lean#L409) (proved); [`DLMF.JacobiElliptic.Real.iteratedDeriv_two_jacobiDsm`](DLMF/JacobiElliptic/Derivatives/RealEquations.lean#L486) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E24](https://dlmf.nist.gov/22.13.E24): [`DLMF.JacobiElliptic.iteratedDeriv_two_jacobiCs`](DLMF/JacobiElliptic/Derivatives/ComplexEquations.lean#L426) (proved); [`DLMF.JacobiElliptic.Real.iteratedDeriv_two_jacobiCsm`](DLMF/JacobiElliptic/Derivatives/RealEquations.lean#L511) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.T1](https://dlmf.nist.gov/22.13.T1): [`DLMF.JacobiElliptic.hasDerivAt_jacobiSn`](DLMF/JacobiElliptic/Derivatives/ThetaWronskians.lean#L506) (proved); [`DLMF.JacobiElliptic.hasDerivAt_jacobiCn`](DLMF/JacobiElliptic/Derivatives/ThetaWronskians.lean#L530) (proved); [`DLMF.JacobiElliptic.hasDerivAt_jacobiDn`](DLMF/JacobiElliptic/Derivatives/ThetaWronskians.lean#L553) (proved); [`DLMF.JacobiElliptic.hasDerivAt_jacobiCd`](DLMF/JacobiElliptic/Derivatives/ThetaWronskians.lean#L576) (proved); [`DLMF.JacobiElliptic.hasDerivAt_jacobiSd`](DLMF/JacobiElliptic/Derivatives/ThetaWronskians.lean#L602) (proved); [`DLMF.JacobiElliptic.hasDerivAt_jacobiNd`](DLMF/JacobiElliptic/Derivatives/ThetaWronskians.lean#L625) (proved); [`DLMF.JacobiElliptic.hasDerivAt_jacobiDc`](DLMF/JacobiElliptic/Derivatives/ThetaWronskians.lean#L648) (proved); [`DLMF.JacobiElliptic.hasDerivAt_jacobiNc`](DLMF/JacobiElliptic/Derivatives/ThetaWronskians.lean#L674) (proved); [`DLMF.JacobiElliptic.hasDerivAt_jacobiSc`](DLMF/JacobiElliptic/Derivatives/ThetaWronskians.lean#L697) (proved); [`DLMF.JacobiElliptic.hasDerivAt_jacobiNs`](DLMF/JacobiElliptic/Derivatives/ThetaWronskians.lean#L720) (proved); [`DLMF.JacobiElliptic.hasDerivAt_jacobiDs`](DLMF/JacobiElliptic/Derivatives/ThetaWronskians.lean#L744) (proved); [`DLMF.JacobiElliptic.hasDerivAt_jacobiCs`](DLMF/JacobiElliptic/Derivatives/ThetaWronskians.lean#L767) (proved); [`DLMF.JacobiElliptic.Real.hasDerivAt_jacobiSdm`](DLMF/JacobiElliptic/Derivatives/RealEquations.lean#L70) (proved); [`DLMF.JacobiElliptic.Real.hasDerivAt_jacobiCdm`](DLMF/JacobiElliptic/Derivatives/RealEquations.lean#L84) (proved); [`DLMF.JacobiElliptic.Real.hasDerivAt_jacobiNdm`](DLMF/JacobiElliptic/Derivatives/RealEquations.lean#L97) (proved); [`DLMF.JacobiElliptic.Real.hasDerivAt_jacobiDcm`](DLMF/JacobiElliptic/Derivatives/RealEquations.lean#L110) (proved); [`DLMF.JacobiElliptic.Real.hasDerivAt_jacobiNcm`](DLMF/JacobiElliptic/Derivatives/RealEquations.lean#L122) (proved); [`DLMF.JacobiElliptic.Real.hasDerivAt_jacobiScm`](DLMF/JacobiElliptic/Derivatives/RealEquations.lean#L133) (proved); [`DLMF.JacobiElliptic.Real.hasDerivAt_jacobiNsm`](DLMF/JacobiElliptic/Derivatives/RealEquations.lean#L145) (proved); [`DLMF.JacobiElliptic.Real.hasDerivAt_jacobiDsm`](DLMF/JacobiElliptic/Derivatives/RealEquations.lean#L157) (proved); [`DLMF.JacobiElliptic.Real.hasDerivAt_jacobiCsm`](DLMF/JacobiElliptic/Derivatives/RealEquations.lean#L169) (proved); [`DLMF.Elliptic.Real.hasDerivAt_jacobiSnOfParameter`](DLMF/Elliptic/Basic/Jacobi.lean#L153) (proved); [`DLMF.Elliptic.Real.hasDerivAt_jacobiCnOfParameter`](DLMF/Elliptic/Basic/Jacobi.lean#L160) (proved); [`DLMF.Elliptic.Real.hasDerivAt_jacobiDnOfParameter`](DLMF/Elliptic/Basic/Jacobi.lean#L168) (proved). Complex: k ∈ jacobiModulusDomain and theta denominator nonzero. Real m<1: nine quotients proved here; sn, cn, dn pre-existing (tagged there 22.13.E1–E3, which is a mis-tag for T1).

## [§22.14 Integrals](https://dlmf.nist.gov/22.14)

- [22.14.E1](https://dlmf.nist.gov/22.14.E1): [`DLMF.JacobiElliptic.Real.hasDerivAt_primitive_jacobiSn`](DLMF/JacobiElliptic/Integrals.lean#L116) (proved). Special case: real x, 0 < k < 1.
- [22.14.E2](https://dlmf.nist.gov/22.14.E2): [`DLMF.JacobiElliptic.Real.hasDerivAt_primitive_jacobiCn`](DLMF/JacobiElliptic/Integrals.lean#L136) (proved). Principal arccos form valid on 0<x<2K; DLMF Arccos is multivalued, not an erratum.
- [22.14.E3](https://dlmf.nist.gov/22.14.E3): [`DLMF.JacobiElliptic.Real.hasDerivAt_arcsin_jacobiSnOfParameter`](DLMF/JacobiElliptic/Integrals.lean#L162) (proved). For |x| < K.
- [22.14.E4](https://dlmf.nist.gov/22.14.E4): [`DLMF.JacobiElliptic.Real.hasDerivAt_primitive_jacobiCd`](DLMF/JacobiElliptic/Integrals.lean#L185) (proved). Special case: real x, 0 < k < 1.
- [22.14.E5](https://dlmf.nist.gov/22.14.E5): [`DLMF.JacobiElliptic.Real.hasDerivAt_primitive_jacobiSd`](DLMF/JacobiElliptic/Integrals.lean#L207) (proved). Special case: real x, 0 < k < 1, principal arcsin.
- [22.14.E6](https://dlmf.nist.gov/22.14.E6): [`DLMF.JacobiElliptic.Real.hasDerivAt_primitive_jacobiNd`](DLMF/JacobiElliptic/Integrals.lean#L248) (proved). As E2: principal branch on 0<x<2K.
- [22.14.E7](https://dlmf.nist.gov/22.14.E7): [`DLMF.JacobiElliptic.Real.hasDerivAt_primitive_jacobiDc`](DLMF/JacobiElliptic/Integrals.lean#L290) (proved). Special case: real x, 0 < k < 1.
- [22.14.E8](https://dlmf.nist.gov/22.14.E8): [`DLMF.JacobiElliptic.Real.hasDerivAt_primitive_jacobiNc`](DLMF/JacobiElliptic/Integrals.lean#L312) (proved). Special case: real x, 0 < k < 1.
- [22.14.E9](https://dlmf.nist.gov/22.14.E9): [`DLMF.JacobiElliptic.Real.hasDerivAt_primitive_jacobiSc`](DLMF/JacobiElliptic/Integrals.lean#L347) (proved). Special case: real x, 0 < k < 1.
- [22.14.E10](https://dlmf.nist.gov/22.14.E10): [`DLMF.JacobiElliptic.Real.hasDerivAt_primitive_jacobiNs`](DLMF/JacobiElliptic/Integrals.lean#L372) (proved). Special case: real x, 0 < k < 1.
- [22.14.E11](https://dlmf.nist.gov/22.14.E11): [`DLMF.JacobiElliptic.Real.hasDerivAt_primitive_jacobiDs`](DLMF/JacobiElliptic/Integrals.lean#L402) (proved). Special case: real x, 0 < k < 1.
- [22.14.E12](https://dlmf.nist.gov/22.14.E12): [`DLMF.JacobiElliptic.Real.hasDerivAt_primitive_jacobiCs`](DLMF/JacobiElliptic/Integrals.lean#L423) (proved). Special case: real x, 0 < k < 1.
- [22.14.E13](https://dlmf.nist.gov/22.14.E13): [`DLMF.JacobiElliptic.Real.hasDerivAt_primitive_inv_jacobiSn`](DLMF/JacobiElliptic/Integrals.lean#L455) (proved). Special case: real x, 0 < k < 1.
- [22.14.E14](https://dlmf.nist.gov/22.14.E14): [`DLMF.JacobiElliptic.Real.hasDerivAt_primitive_jacobiCn_div_jacobiSn`](DLMF/JacobiElliptic/Integrals.lean#L484) (proved). Special case: real x, 0 < k < 1.
- [22.14.E15](https://dlmf.nist.gov/22.14.E15): [`DLMF.JacobiElliptic.Real.hasDerivAt_primitive_jacobiCn_div_jacobiSn_sq`](DLMF/JacobiElliptic/Integrals.lean#L511) (proved). Special case: real x, 0 < k < 1.
- [22.14.E16](https://dlmf.nist.gov/22.14.E16): [`DLMF.JacobiElliptic.Real.integral_log_jacobiSnOfParameter`](DLMF/JacobiElliptic/Integrals.lean#L691) (proved). Definite log integral, real 0<k<1.
- [22.14.E17](https://dlmf.nist.gov/22.14.E17): [`DLMF.JacobiElliptic.Real.integral_log_jacobiCnOfParameter`](DLMF/JacobiElliptic/Integrals.lean#L703) (proved). As E16.
- [22.14.E18](https://dlmf.nist.gov/22.14.E18): [`DLMF.JacobiElliptic.Real.integral_log_jacobiDnOfParameter`](DLMF/JacobiElliptic/Integrals.lean#L534) (proved). As E16.

## [§22.15 Inverse Functions](https://dlmf.nist.gov/22.15)

- [22.15.E1](https://dlmf.nist.gov/22.15.E1): [`DLMF.Elliptic.Real.jacobiSnOfParameter_jacobiArcsnOfParameter`](DLMF/Elliptic/Basic/Jacobi.lean#L274) (proved). Pre-existing (untagged).
- [22.15.E2](https://dlmf.nist.gov/22.15.E2): [`DLMF.JacobiElliptic.Real.jacobiCnm_jacobiArccn`](DLMF/JacobiElliptic/Basic/Inverse.lean#L108) (proved). Special case: real parameter m = k² < 1.
- [22.15.E3](https://dlmf.nist.gov/22.15.E3): [`DLMF.JacobiElliptic.Real.jacobiDnm_jacobiArcdn`](DLMF/JacobiElliptic/Basic/Inverse.lean#L115) (proved). Special case: real parameter 0 < m = k² < 1.
- [22.15.E4](https://dlmf.nist.gov/22.15.E4): [`DLMF.JacobiElliptic.Real.jacobiArccn`](DLMF/JacobiElliptic/Basic/Inverse.lean#L51) (definition); [`DLMF.JacobiElliptic.Real.jacobiArcdn`](DLMF/JacobiElliptic/Basic/Inverse.lean#L56) (definition); [`DLMF.Elliptic.Real.jacobiArcsnOfParameter`](DLMF/Elliptic/Basic/Jacobi.lean#L270) (definition). arccn and arcdn defined here; arcsn pre-existing.
- [22.15.E5](https://dlmf.nist.gov/22.15.E5): [`DLMF.JacobiElliptic.Real.jacobiArcsnOfParameter_mem_Icc`](DLMF/JacobiElliptic/Basic/Inverse.lean#L133) (proved). Special case: real parameter m = k² < 1.
- [22.15.E6](https://dlmf.nist.gov/22.15.E6): [`DLMF.JacobiElliptic.Real.jacobiArccn_mem_Icc`](DLMF/JacobiElliptic/Basic/Inverse.lean#L150) (proved). Special case: real parameter m = k² < 1.
- [22.15.E7](https://dlmf.nist.gov/22.15.E7): [`DLMF.JacobiElliptic.Real.jacobiArcdn_mem_Icc`](DLMF/JacobiElliptic/Basic/Inverse.lean#L166) (proved). Special case: real parameter m = k² < 1.
- [22.15.E8](https://dlmf.nist.gov/22.15.E8): [`DLMF.JacobiElliptic.Real.jacobiSnOfParameter_eq_iff`](DLMF/JacobiElliptic/Inverse.lean#L108) (proved). Special case: real parameter k² < 1.
- [22.15.E9](https://dlmf.nist.gov/22.15.E9): [`DLMF.JacobiElliptic.Real.jacobiCnOfParameter_eq_iff`](DLMF/JacobiElliptic/Inverse.lean#L123) (proved). Special case: real parameter k² < 1.
- [22.15.E10](https://dlmf.nist.gov/22.15.E10): [`DLMF.JacobiElliptic.Real.jacobiDnOfParameter_eq_iff`](DLMF/JacobiElliptic/Inverse.lean#L157) (proved). Special case: real parameter 0 < k² < 1.
- [22.15.E11](https://dlmf.nist.gov/22.15.E11): [`DLMF.JacobiElliptic.Real.eq_integral_jacobiSnOfParameter`](DLMF/JacobiElliptic/Inverse.lean#L256) (proved). Stronger than DLMF: |x| ≤ K.
- [22.15.E12](https://dlmf.nist.gov/22.15.E12): [`DLMF.JacobiElliptic.Real.jacobiArcsnOfParameter_eq_integral`](DLMF/JacobiElliptic/Inverse.lean#L238) (proved). Special case: real parameter m = k² < 1.
- [22.15.E13](https://dlmf.nist.gov/22.15.E13): [`DLMF.JacobiElliptic.Real.jacobiArccn_eq_integral`](DLMF/JacobiElliptic/Inverse.lean#L283) (proved). Special case: real parameter m = k² < 1.
- [22.15.E14](https://dlmf.nist.gov/22.15.E14): [`DLMF.JacobiElliptic.Real.jacobiArcdn_eq_integral`](DLMF/JacobiElliptic/Inverse.lean#L306) (proved). Special case: real parameter 0 < m = k² < 1.
- [22.15.E15](https://dlmf.nist.gov/22.15.E15): [`DLMF.JacobiElliptic.Real.jacobiArccd`](DLMF/JacobiElliptic/Basic/Inverse.lean#L62) (definition); [`DLMF.JacobiElliptic.Real.jacobiCdm_jacobiArccd`](DLMF/JacobiElliptic/Inverse.lean#L391) (proved). Special case: real parameter m = k² < 1.
- [22.15.E16](https://dlmf.nist.gov/22.15.E16): [`DLMF.JacobiElliptic.Real.jacobiArcsd`](DLMF/JacobiElliptic/Basic/Inverse.lean#L66) (definition); [`DLMF.JacobiElliptic.Real.jacobiSdm_jacobiArcsd`](DLMF/JacobiElliptic/Inverse.lean#L430) (proved). Special case: real parameter m = k² < 1.
- [22.15.E17](https://dlmf.nist.gov/22.15.E17): [`DLMF.JacobiElliptic.Real.jacobiArcnd`](DLMF/JacobiElliptic/Basic/Inverse.lean#L71) (definition); [`DLMF.JacobiElliptic.Real.jacobiNdm_jacobiArcnd`](DLMF/JacobiElliptic/Inverse.lean#L517) (proved). Special case: real parameter m = k² < 1.
- [22.15.E18](https://dlmf.nist.gov/22.15.E18): [`DLMF.JacobiElliptic.Real.jacobiArcdc`](DLMF/JacobiElliptic/Basic/Inverse.lean#L76) (definition); [`DLMF.JacobiElliptic.Real.jacobiDcm_jacobiArcdc`](DLMF/JacobiElliptic/Inverse.lean#L559) (proved). Special case: real parameter 0 ≤ m = k² < 1.
- [22.15.E19](https://dlmf.nist.gov/22.15.E19): [`DLMF.JacobiElliptic.Real.jacobiArcnc`](DLMF/JacobiElliptic/Basic/Inverse.lean#L80) (definition); [`DLMF.JacobiElliptic.Real.jacobiNcm_jacobiArcnc`](DLMF/JacobiElliptic/Inverse.lean#L585) (proved). Special case: real parameter 0 ≤ m = k² < 1.
- [22.15.E20](https://dlmf.nist.gov/22.15.E20): [`DLMF.JacobiElliptic.Real.jacobiArcsc`](DLMF/JacobiElliptic/Basic/Inverse.lean#L85) (definition); [`DLMF.JacobiElliptic.Real.jacobiScm_jacobiArcsc`](DLMF/JacobiElliptic/Inverse.lean#L695) (proved). Special case: real parameter 0 ≤ m = k² < 1.
- [22.15.E21](https://dlmf.nist.gov/22.15.E21): [`DLMF.JacobiElliptic.Real.jacobiArcns`](DLMF/JacobiElliptic/Basic/Inverse.lean#L90) (definition); [`DLMF.JacobiElliptic.Real.jacobiNsm_jacobiArcns`](DLMF/JacobiElliptic/Inverse.lean#L639) (proved). Special case: real parameter 0 ≤ m = k² < 1.
- [22.15.E22](https://dlmf.nist.gov/22.15.E22): [`DLMF.JacobiElliptic.Real.jacobiArcds`](DLMF/JacobiElliptic/Basic/Inverse.lean#L94) (definition); [`DLMF.JacobiElliptic.Real.jacobiDsm_jacobiArcds`](DLMF/JacobiElliptic/Inverse.lean#L663) (proved). Special case: real parameter 0 < m = k² < 1.
- [22.15.E23](https://dlmf.nist.gov/22.15.E23): [`DLMF.JacobiElliptic.Real.jacobiArccs`](DLMF/JacobiElliptic/Basic/Inverse.lean#L98) (definition); [`DLMF.JacobiElliptic.Real.jacobiCsm_jacobiArccs`](DLMF/JacobiElliptic/Inverse.lean#L729) (proved). Special case: real parameter 0 ≤ m = k² < 1.

## [§22.16 Related Functions](https://dlmf.nist.gov/22.16)

- [22.16.E1](https://dlmf.nist.gov/22.16.E1): [`DLMF.JacobiElliptic.Real.jacobiAmOfParameter_eq_arcsin_jacobiSnOfParameter`](DLMF/JacobiElliptic/Related.lean#L97) (proved). Special case: real parameter m = k² < 1; principal branch on -K ≤ x ≤ K.
- [22.16.E2](https://dlmf.nist.gov/22.16.E2): [`DLMF.Elliptic.Real.jacobiAmOfParameter_add_two_completeEllipticKOfParameter`](DLMF/Elliptic/Basic/Jacobi.lean#L109) (proved). Pre-existing (untagged).
- [22.16.E3](https://dlmf.nist.gov/22.16.E3): [`DLMF.JacobiElliptic.Real.jacobiAmOfParameter_eq_integral_jacobiDnOfParameter`](DLMF/JacobiElliptic/Related.lean#L130) (proved). Special case: real parameter m = k² < 1.
- [22.16.E4](https://dlmf.nist.gov/22.16.E4): [`DLMF.Elliptic.Real.jacobiAmOfParameter_zero_param`](DLMF/Elliptic/Basic/Jacobi.lean#L125) (proved). Pre-existing (untagged).
- [22.16.E5](https://dlmf.nist.gov/22.16.E5): [`DLMF.JacobiElliptic.Real.tendsto_jacobiAmOfParameter_one`](DLMF/JacobiElliptic/Related.lean#L141) (proved). Stated as limit k→1⁻: `Real.jacobiAmOfParameter` is totalized (am=x) at m≥1.
- [22.16.E6](https://dlmf.nist.gov/22.16.E6): [`DLMF.JacobiElliptic.Real.jacobiAmOfParameter_isBigO_maclaurin`](DLMF/JacobiElliptic/Related.lean#L223) (proved). Special case: real x, real parameter m = k² < 1.
- [22.16.E7](https://dlmf.nist.gov/22.16.E7): [`DLMF.JacobiElliptic.Real.jacobiAmOfParameter_isBigO_small_modulus`](DLMF/JacobiElliptic/Related.lean#L254) (proved). Special case: real x, real k → 0.
- [22.16.E8](https://dlmf.nist.gov/22.16.E8): [`DLMF.JacobiElliptic.Real.jacobiAmOfParameter_isBigO_small_comodulus`](DLMF/JacobiElliptic/Related.lean#L270) (proved). Special case: real x, real k → 1⁻.
- [22.16.E9](https://dlmf.nist.gov/22.16.E9): [`DLMF.JacobiElliptic.Real.jacobiAmOfParameter_hasSum_fourier`](DLMF/JacobiElliptic/Related.lean#L327) (proved). Special case: real x, 0 < k < 1.
- [22.16.E10](https://dlmf.nist.gov/22.16.E10): [`DLMF.JacobiElliptic.Real.eq_incompleteEllipticFOfParameter_iff_jacobiAmOfParameter_eq`](DLMF/JacobiElliptic/Related.lean#L397) (proved). Stronger than DLMF: all real x and φ.
- [22.16.E11](https://dlmf.nist.gov/22.16.E11): [`DLMF.Elliptic.Real.jacobiAmOfParameter`](DLMF/Elliptic/Basic/Amplitude.lean#L184) (definition); [`DLMF.Elliptic.Real.incompleteEllipticFOfParameter_jacobiAmOfParameter`](DLMF/Elliptic/Basic/Jacobi.lean#L66) (proved). Pre-existing definition of am as inverse of F(·,m) (untagged).
- [22.16.E12](https://dlmf.nist.gov/22.16.E12): [`DLMF.JacobiElliptic.Real.jacobiAmOfParameter_eq_iff_jacobiSnOfParameter_eq_sin`](DLMF/JacobiElliptic/Related.lean#L406) (proved). Special case: -π/2 ≤ φ ≤ π/2 made explicit.
- [22.16.E13](https://dlmf.nist.gov/22.16.E13): [`DLMF.JacobiElliptic.Real.jacobiAmOfParameter_eq_iff_jacobiCnOfParameter_eq_cos`](DLMF/JacobiElliptic/Related.lean#L419) (proved). Converse direction needs 0≤x and 0≤φ (cos is even).
- [22.16.E14](https://dlmf.nist.gov/22.16.E14): [`DLMF.JacobiElliptic.Real.jacobiEpsilon_eq_integral_sn`](DLMF/JacobiElliptic/Related.lean#L470) (proved). Corrected form (DLMF 2010-07-08, Karney) used.
- [22.16.E15](https://dlmf.nist.gov/22.16.E15): [`DLMF.JacobiElliptic.Real.jacobiEpsilon_eq_integral_jacobiSnOfParameter_sq`](DLMF/JacobiElliptic/Related.lean#L510) (proved). Special case: real modulus with k² < 1.
- [22.16.E16](https://dlmf.nist.gov/22.16.E16): [`DLMF.JacobiElliptic.Real.jacobiEpsilon_eq_integral_jacobiCnOfParameter_sq`](DLMF/JacobiElliptic/Related.lean#L527) (proved). Special case: real modulus with k² < 1.
- [22.16.E17](https://dlmf.nist.gov/22.16.E17): [`DLMF.JacobiElliptic.Real.jacobiEpsilon`](DLMF/JacobiElliptic/Basic/Epsilon.lean#L39) (definition).
- [22.16.E18](https://dlmf.nist.gov/22.16.E18): [`DLMF.JacobiElliptic.Real.jacobiEpsilon_eq_integral_cd_sq`](DLMF/JacobiElliptic/Related.lean#L571) (proved). Special case: real modulus 0 < k < 1.
- [22.16.E19](https://dlmf.nist.gov/22.16.E19): [`DLMF.JacobiElliptic.Real.jacobiEpsilon_eq_integral_sd_sq`](DLMF/JacobiElliptic/Related.lean#L622) (proved). Special case: real modulus 0 < k < 1.
- [22.16.E20](https://dlmf.nist.gov/22.16.E20): [`DLMF.JacobiElliptic.Real.jacobiEpsilon_eq_integral_nd_sq`](DLMF/JacobiElliptic/Related.lean#L675) (proved). Special case: real modulus 0 < k < 1.
- [22.16.E21](https://dlmf.nist.gov/22.16.E21): [`DLMF.JacobiElliptic.Real.jacobiEpsilon_eq_integral_dc_sq`](DLMF/JacobiElliptic/Related.lean#L725) (proved). Special case: real modulus 0 < k < 1.
- [22.16.E22](https://dlmf.nist.gov/22.16.E22): [`DLMF.JacobiElliptic.Real.jacobiEpsilon_eq_integral_nc_sq`](DLMF/JacobiElliptic/Related.lean#L790) (proved). Special case: real modulus 0 < k < 1.
- [22.16.E23](https://dlmf.nist.gov/22.16.E23): [`DLMF.JacobiElliptic.Real.jacobiEpsilon_eq_integral_sc_sq`](DLMF/JacobiElliptic/Related.lean#L852) (proved). Special case: real modulus 0 < k < 1.
- [22.16.E24](https://dlmf.nist.gov/22.16.E24): [`DLMF.JacobiElliptic.Real.jacobiEpsilon_eq_integral_ns_sq`](DLMF/JacobiElliptic/Related.lean#L1137) (proved). Special case: real modulus 0 < k < 1, x ≠ 0.
- [22.16.E25](https://dlmf.nist.gov/22.16.E25): [`DLMF.JacobiElliptic.Real.jacobiEpsilon_eq_integral_ds_sq`](DLMF/JacobiElliptic/Related.lean#L1149) (proved). Special case: real modulus 0 < k < 1, x ≠ 0.
- [22.16.E26](https://dlmf.nist.gov/22.16.E26): [`DLMF.JacobiElliptic.Real.jacobiEpsilon_eq_integral_cs_sq`](DLMF/JacobiElliptic/Related.lean#L1169) (proved). Special case: real modulus 0 < k < 1, x ≠ 0.
- [22.16.E27](https://dlmf.nist.gov/22.16.E27): [`DLMF.JacobiElliptic.Real.jacobiEpsilon_add`](DLMF/JacobiElliptic/Related.lean#L1186) (proved). Special case: real modulus with k² < 1.
- [22.16.E28](https://dlmf.nist.gov/22.16.E28): [`DLMF.JacobiElliptic.Real.jacobiEpsilon_add_completeEllipticKOfParameter`](DLMF/JacobiElliptic/Related.lean#L1233) (proved). Special case: real modulus with k² < 1.
- [22.16.E29](https://dlmf.nist.gov/22.16.E29): [`DLMF.JacobiElliptic.Real.jacobiEpsilon_add_two_completeEllipticKOfParameter`](DLMF/JacobiElliptic/Basic/EpsilonProperties.lean#L49) (proved). Special case: real modulus with k² < 1.
- [22.16.E30](https://dlmf.nist.gov/22.16.E30): [`DLMF.JacobiElliptic.Real.jacobiEpsilon_eq_theta`](DLMF/JacobiElliptic/Related.lean#L1249) (proved). Special case: real x, 0 < k < 1.
- [22.16.E31](https://dlmf.nist.gov/22.16.E31): [`DLMF.JacobiElliptic.Real.incompleteEllipticEOfParameter_jacobiAmOfParameter`](DLMF/JacobiElliptic/Basic/EpsilonProperties.lean#L29) (proved). Stronger than DLMF: all real x.
- [22.16.E32](https://dlmf.nist.gov/22.16.E32): [`DLMF.JacobiElliptic.Real.jacobiZeta`](DLMF/JacobiElliptic/Basic/Epsilon.lean#L45) (definition). Named `jacobiZeta` to avoid confusion with the theta argument `jacobiThetaArgument`.
- [22.16.E33](https://dlmf.nist.gov/22.16.E33): [`DLMF.JacobiElliptic.Real.jacobiZeta_add_completeEllipticKOfParameter`](DLMF/JacobiElliptic/Related.lean#L1282) (proved). Proof depends on admitted 22.16.E28.
- [22.16.E34](https://dlmf.nist.gov/22.16.E34): [`DLMF.JacobiElliptic.Real.jacobiZeta_add_two_completeEllipticKOfParameter`](DLMF/JacobiElliptic/Related.lean#L1293) (proved). Special case: real modulus with k² < 1.
- [22.16.i](https://dlmf.nist.gov/22.16#i): [`DLMF.JacobiElliptic.Real.contDiff_jacobiAmOfParameter`](DLMF/JacobiElliptic/Related.lean#L108) (proved); [`DLMF.Elliptic.Real.continuous_jacobiAmOfParameter`](DLMF/Elliptic/Basic/Jacobi.lean#L80) (proved); [`DLMF.Elliptic.Real.hasDerivAt_jacobiAmOfParameter`](DLMF/Elliptic/Basic/Jacobi.lean#L85) (proved). Smoothness ContDiff ℝ ⊤ of am in x proved; existing continuity and derivative pre-existing (untagged).
- [22.16.iii](https://dlmf.nist.gov/22.16#iii): [`DLMF.JacobiElliptic.Real.jacobiZeta_add`](DLMF/JacobiElliptic/Related.lean#L1271) (proved). Quasi-addition for Z; proof depends on admitted 22.16.E27.

## [§22.17 Moduli Outside the Interval [0,1]](https://dlmf.nist.gov/22.17)

- [22.17.E1](https://dlmf.nist.gov/22.17.E1): [`DLMF.JacobiElliptic.jacobiPQ_neg_modulus`](DLMF/JacobiElliptic/OutsideModuli.lean#L56) (proved). Stronger than DLMF: all complex z and k.
- [22.17.E2](https://dlmf.nist.gov/22.17.E2): [`DLMF.JacobiElliptic.jacobiSn_inv`](DLMF/JacobiElliptic/OutsideModuli.lean#L102) (proved). k, 1/k ∈ jacobiModulusDomain; real 1/k>1 lies on the definition cut.
- [22.17.E3](https://dlmf.nist.gov/22.17.E3): [`DLMF.JacobiElliptic.jacobiCn_inv`](DLMF/JacobiElliptic/OutsideModuli.lean#L109) (proved). As E2.
- [22.17.E4](https://dlmf.nist.gov/22.17.E4): [`DLMF.JacobiElliptic.jacobiDn_inv`](DLMF/JacobiElliptic/OutsideModuli.lean#L115) (proved). As E2.
- [22.17.E5](https://dlmf.nist.gov/22.17.E5): [`DLMF.JacobiElliptic.mul_sqrt_one_sub_sq_imagModulus`](DLMF/JacobiElliptic/OutsideModuli.lean#L121) (proved); [`DLMF.JacobiElliptic.jacobiImagModulusk`](DLMF/JacobiElliptic/OutsideModuli.lean#L136) (definition). Real identity proved; complex k₁ defined with principal root.
- [22.17.E6](https://dlmf.nist.gov/22.17.E6): [`DLMF.JacobiElliptic.jacobiSn_I_mul`](DLMF/JacobiElliptic/OutsideModuli.lean#L204) (proved). ik, k₁ ∈ jacobiModulusDomain.
- [22.17.E7](https://dlmf.nist.gov/22.17.E7): [`DLMF.JacobiElliptic.jacobiCn_I_mul`](DLMF/JacobiElliptic/OutsideModuli.lean#L213) (proved). As E6.
- [22.17.E8](https://dlmf.nist.gov/22.17.E8): [`DLMF.JacobiElliptic.jacobiDn_I_mul`](DLMF/JacobiElliptic/OutsideModuli.lean#L221) (proved). As E6.

## Analytical prose and exclusions (part B)

- [22.3](https://dlmf.nist.gov/22.3): excluded: graphics (figures only, no equations).
- [22.10.i.p1](https://dlmf.nist.gov/22.10#i.p1): Maclaurin coefficients as polynomials in `k²`; covered by 22.10.E1–E3.
- [22.10.i.p2](https://dlmf.nist.gov/22.10#i.p2): convergence for `|z| < min(K, K')`; `DLMF.JacobiElliptic.jacobi_hasFPowerSeriesOnBall` (tag 22.10.i, admitted, real `0 < k < 1`).
- [22.10.ii.p1](https://dlmf.nist.gov/22.10#ii.p1): expansions in `k` and `k'`; covered by 22.10.E4–E9.
- [22.10.ii.p2](https://dlmf.nist.gov/22.10#ii.p2): radius of convergence in the `k`-plane. Qualitative remark, not formalized.
- [22.10.i](https://dlmf.nist.gov/22.10.i): [`DLMF.JacobiElliptic.jacobi_hasFPowerSeriesOnBall`](DLMF/JacobiElliptic/Maclaurin.lean#L274) (proved).
- [22.11.p1](https://dlmf.nist.gov/22.11#p1)–[p4](https://dlmf.nist.gov/22.11#p4), [p6](https://dlmf.nist.gov/22.11#p6): nome, strip condition and the `q^{n+1/2}` convention. These are built into the hypotheses of 22.11.E1–E14 (`‖q‖ e^{2|Im ζ|} < 1` or `e^{|Im ζ|}`). [p5](https://dlmf.nist.gov/22.11#p5): bibliographic.
- [22.12.p1](https://dlmf.nist.gov/22.12#p1), [p2](https://dlmf.nist.gov/22.12#p2): `τ`, and the order of summation (symmetric partial sums for the doubly infinite tan-type series). Built into 22.12.E2–E13.
- [22.13.i.p1](https://dlmf.nist.gov/22.13#i.p1): copolar remark on Table 22.13.T1. Covered by the T1 entries.
- 22.13.i.p2, ii.p3, iii.p3: Carlson references for derivatives with respect to the modulus. Bibliographic.
- [22.14.i](https://dlmf.nist.gov/22.14#i) p1–p6: ranges of `x` for the primitives. Built into the hypotheses of 22.14.E1–E15. [22.14.ii](https://dlmf.nist.gov/22.14#ii) p1–p2: integrals of powers. References and qualitative remarks only. [22.14.iii.p1](https://dlmf.nist.gov/22.14#iii.p1): definite log integrals E16–E18. [22.14.iv](https://dlmf.nist.gov/22.14#iv) p1–p2: subsidiary integrals by subtraction. Remark only.
- [22.15.i](https://dlmf.nist.gov/22.15#i) p1–p2: principal ranges of arcsn, arccn and arcdn. Covered by 22.15.E5–E7. [22.15.ii](https://dlmf.nist.gov/22.15#ii) p1–p4: normal-form remark and references. Covered by 22.15.E15–E23, otherwise bibliographic.
- [22.16.Px1.p1](https://dlmf.nist.gov/22.16#Px1.p1): smoothness of `am`. `DLMF.JacobiElliptic.Real.contDiff_jacobiAmOfParameter` (tag 22.16.i, proved). The other 22.16 prose paragraphs restate the definitions and domains used in 22.16.E1–E34. Quasi-addition for `Z` in [22.16.iii](https://dlmf.nist.gov/22.16#iii): `DLMF.JacobiElliptic.Real.jacobiZeta_add` (proved, depends on admitted 22.16.E27).
- [22.16.iv](https://dlmf.nist.gov/22.16#iv): excluded: graphics (figures).
- [22.16.i](https://dlmf.nist.gov/22.16.i): [`DLMF.Elliptic.Real.hasDerivAt_jacobiAmOfParameter`](DLMF/Elliptic/Basic/Jacobi.lean#L85) (proved); [`DLMF.JacobiElliptic.Real.contDiff_jacobiAmOfParameter`](DLMF/JacobiElliptic/Related.lean#L108) (proved).
- [22.16.iii](https://dlmf.nist.gov/22.16.iii): [`DLMF.JacobiElliptic.Real.jacobiZeta_add`](DLMF/JacobiElliptic/Related.lean#L1271) (proved).
- [22.17.i](https://dlmf.nist.gov/22.17#i) p1–p5: transformations to `[0, 1]`. p5 (polynomial identities, choice of square root sign) is reflected in `jacobiImagModulusk`, which uses the principal root. [22.17.ii.p1](https://dlmf.nist.gov/22.17#ii.p1): meromorphy in `k²` and validity for complex `k`. Used as the justification for the complex-domain statements of 22.17.E2–E8.
- [22.18](https://dlmf.nist.gov/22.18) E1–E8: excluded: application. Mathematical content, briefly: arc length of the ellipse `l(u) = a ℰ(u, k)` (22.18.3); lemniscate arc length (22.18.4–6); conformal map of a rectangle by `sn` (22.18(ii)); uniformization of `y² = (1 - x²)(1 - k²x²)` (22.18.7); Jacobi–Abel / Euler addition law (22.18.8, equivalent to 22.8.1).
- [22.19](https://dlmf.nist.gov/22.19) E1–E9: excluded: application. Mathematical content: pendulum solution `sin(θ/2) = sin(α/2) sn(t + K, sin(α/2))` (22.19.2–3), cf. existing `DLMF.Elliptic.pendulumAngle_ode` and `DLMF.Elliptic.pendulumAngle_periodic` in `DLMF/Elliptic/JacobiIdentities.lean`; cn/sn/dn solutions of the quartic (Duffing) oscillator (22.19.6–9).
- [22.20](https://dlmf.nist.gov/22.20) E1–E6: excluded: computation (AGM algorithm, Landen transformations, lattice calculations).
- [22.21](https://dlmf.nist.gov/22.21), [22.22](https://dlmf.nist.gov/22.22): excluded: tables and software (no equations).

## Validation (part B)

- Strict `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false` passes for all
  eight modules, with `sorry` warnings only. `lake build` of each module succeeds.
- Admissions per file (`grep -c '\bsorry\b'`): Maclaurin 10, FourierSeries 14,
  PartialFractions 12, Derivatives 36, Integrals 3, Inverse 14, Related 18, OutsideModuli 6
  (total 113). There is no `sorry` in any definition or `je22b_` helper lemma.
- `#print axioms` on 16 sampled proved theorems shows only `propext`, `Classical.choice`
  and `Quot.sound`. `Real.jacobiZeta_add_completeEllipticKOfParameter` and
  `Real.jacobiZeta_add` inherit `sorryAx` from the admitted 22.16.E28 and E27.
- Numerical validation (mpmath, 2026-10-25) covers every formula of §§22.10–22.17 at
  `k = 0.6`. Complex moduli `0.6+0.3i`, `1.4+0.2i`, `0.3−1.5i` and `2.5+10⁻⁴i` were also
  checked for 22.10–22.12 and 22.17. An apparent mismatch in 22.16.24–26 was traced to
  cancellation in the quadrature; the formulas are correct.
