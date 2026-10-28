# DLMF Chapter 22 acquisition: Jacobian Elliptic Functions

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
untagged lattice forms `jacobiSnTau_shift` … `jacobiCsTau_shift` (all 72 entries of
Table 22.4.3 in the τ-parametrization) are proved without any admission.

## Domains, conventions and source corrections

- Mathlib and the pinned TauCeti have no Jacobian elliptic functions, no complex-modulus
  complete elliptic integral, and no Landen or cyclic identities. The functions are built on
  the project's `θ₁…θ₄` (`DLMF/Elliptic/Theta.lean`, DLMF normalization, q = e^{iπτ}), which
  rest on Mathlib's `jacobiTheta₂`.
- Two parametrizations. The lattice form `jacobiPQTau p q z τ` (Im τ > 0) defines
  k = θ₂²(0|τ)/θ₃²(0|τ), k' = θ₄²/θ₃², K = (π/2)θ₃², K' = -iτK and pq by 22.2.4–22.2.9; its
  identities are proved from theta identities (triple-product nonvanishing of the theta
  constants, half-period shifts). The modulus form `jacobiPQk p q z k` is literal DLMF: K(k)
  and K'(k) are the principal complex integrals 19.2.8–19.2.9 (`compEllIntKk`,
  `compEllIntKpk`), τ = iK'/K, q = e^{-πK'/K}, and pq is the theta quotient at that τ.
- Modulus domain `jacobiModulusDomain`: Re k > 0 and k ∉ [1, ∞). DLMF 22.1 takes 0 ≤ k ≤ 1
  outside §§22.3(iv), 22.17, 22.19; the complex domain is the natural one on which the
  principal K, K' give the theta parametrization (checked numerically at k = 0.6,
  0.5 + 0.3i, 1.3 + 0.4i). The endpoint cases k = 0 and k = 1 are represented by the limits of
  Tables 22.5.3–22.5.4, not by values. ACQ22B handles moduli outside this domain (§22.17).
- Admitted foundations: `jacobiTauk_im_pos` (Im τ(k) > 0 on the domain) and
  `jacobi_inversion_k` (the lattice modulus, comodulus and K at τ(k) are k, the principal k'
  and K(k): the inversion problem 22.2.2 / 20.9.1). Every k-form result proved from
  theta identities depends on them. The real bridges `jacobiSnk_ofReal` etc. to the project's
  `Real.jacobiSnm u (k²)` (0 < k < 1) are admitted. (All of these were proved in proof round 1
  on 2026-10-25; the real bridges now live in `SpecialValues.lean`.)
- Lean totalization: x/0 = 0, so at a pole a function takes a junk value. Statements
  dividing by a function or theta value carry hypotheses: `jacobiRegulark r z k` (θ_r(ζ) ≠ 0,
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

- [22.2.E1](https://dlmf.nist.gov/22.2.E1): [`DLMF.JacobiElliptic.jacobiNomek`](DLMF/JacobiElliptic/Basic.lean#L142) (definition); [`DLMF.JacobiElliptic.jacobiNomek_eq_exp_tau`](DLMF/JacobiElliptic/Basic.lean#L397) (proved); [`DLMF.JacobiElliptic.jacobiTauk_im_pos`](DLMF/JacobiElliptic/Basic.lean#L539) (proved). Nome as `jacobiNomek k = exp(-πK'(k)/K(k))`; `jacobiNomek_eq_exp_tau` gives q = e^{iπτ}. Admitted foundation `jacobiTauk_im_pos`: Im τ > 0 on the domain.
- [22.2.E2](https://dlmf.nist.gov/22.2.E2): [`DLMF.JacobiElliptic.compEllIntKTau`](DLMF/JacobiElliptic/Basic.lean#L94) (definition); [`DLMF.JacobiElliptic.jacobiModulusTau`](DLMF/JacobiElliptic/Basic.lean#L103) (definition); [`DLMF.JacobiElliptic.jacobiComodulusTau`](DLMF/JacobiElliptic/Basic.lean#L107) (definition); [`DLMF.JacobiElliptic.jacobi_inversion_k`](DLMF/JacobiElliptic/Basic.lean#L1173) (proved). Lattice form: k = θ₂²(0|τ)/θ₃²(0|τ), k' = θ₄²/θ₃², K = (π/2)θ₃² (definitions `jacobiModulusTau`, `jacobiComodulusTau`, `compEllIntKTau`). Admitted foundation `jacobi_inversion_k`: at τ(k) these recover k, the principal k' and K(k) on the domain (numerically confirmed at real and complex k).
- [22.2.E3](https://dlmf.nist.gov/22.2.E3): [`DLMF.JacobiElliptic.jacobiZetaTau`](DLMF/JacobiElliptic/Basic.lean#L111) (definition); [`DLMF.JacobiElliptic.jacobiZetak`](DLMF/JacobiElliptic/Basic.lean#L146) (definition). ζ = πz/(2K).
- [22.2.E4](https://dlmf.nist.gov/22.2.E4): [`DLMF.JacobiElliptic.jacobiSnk`](DLMF/JacobiElliptic/Basic.lean#L162) (definition); [`DLMF.JacobiElliptic.jacobiNsk`](DLMF/JacobiElliptic/Basic.lean#L180) (definition); [`DLMF.JacobiElliptic.jacobiSnk_ofReal`](DLMF/JacobiElliptic/SpecialValues.lean#L1502) (proved); [`DLMF.JacobiElliptic.jacobiPQk_eq_one_div`](DLMF/JacobiElliptic/Basic.lean#L1225) (proved); [`DLMF.JacobiElliptic.jacobi_eq_theta_quotients`](DLMF/JacobiElliptic/Basic.lean#L535) (proved from admitted foundations). Theta quotients in DLMF normalization; `jacobi_eq_theta_quotients` restates 22.2.4–22.2.9 for the k-form (proved from the inversion admission). Real bridges to the project's `Real.jacobiSnm` etc. (parameter m = k², 0 < k < 1) are admitted.
- [22.2.E5](https://dlmf.nist.gov/22.2.E5): [`DLMF.JacobiElliptic.jacobiCnk`](DLMF/JacobiElliptic/Basic.lean#L165) (definition); [`DLMF.JacobiElliptic.jacobiNck`](DLMF/JacobiElliptic/Basic.lean#L183) (definition); [`DLMF.JacobiElliptic.jacobiCnk_ofReal`](DLMF/JacobiElliptic/SpecialValues.lean#L1509) (proved); [`DLMF.JacobiElliptic.jacobiPQk_eq_one_div`](DLMF/JacobiElliptic/Basic.lean#L1225) (proved); [`DLMF.JacobiElliptic.jacobi_eq_theta_quotients`](DLMF/JacobiElliptic/Basic.lean#L535) (proved from admitted foundations).
- [22.2.E6](https://dlmf.nist.gov/22.2.E6): [`DLMF.JacobiElliptic.jacobiDnk`](DLMF/JacobiElliptic/Basic.lean#L168) (definition); [`DLMF.JacobiElliptic.jacobiNdk`](DLMF/JacobiElliptic/Basic.lean#L186) (definition); [`DLMF.JacobiElliptic.jacobiDnk_ofReal`](DLMF/JacobiElliptic/SpecialValues.lean#L1516) (proved); [`DLMF.JacobiElliptic.jacobiPQk_eq_one_div`](DLMF/JacobiElliptic/Basic.lean#L1225) (proved); [`DLMF.JacobiElliptic.jacobi_eq_theta_quotients`](DLMF/JacobiElliptic/Basic.lean#L535) (proved from admitted foundations).
- [22.2.E7](https://dlmf.nist.gov/22.2.E7): [`DLMF.JacobiElliptic.jacobiSdk`](DLMF/JacobiElliptic/Basic.lean#L171) (definition); [`DLMF.JacobiElliptic.jacobiDsk`](DLMF/JacobiElliptic/Basic.lean#L189) (definition); [`DLMF.JacobiElliptic.jacobiPQk_eq_one_div`](DLMF/JacobiElliptic/Basic.lean#L1225) (proved); [`DLMF.JacobiElliptic.jacobi_eq_theta_quotients`](DLMF/JacobiElliptic/Basic.lean#L535) (proved from admitted foundations).
- [22.2.E8](https://dlmf.nist.gov/22.2.E8): [`DLMF.JacobiElliptic.jacobiCdk`](DLMF/JacobiElliptic/Basic.lean#L174) (definition); [`DLMF.JacobiElliptic.jacobiDck`](DLMF/JacobiElliptic/Basic.lean#L192) (definition); [`DLMF.JacobiElliptic.jacobiPQk_eq_one_div`](DLMF/JacobiElliptic/Basic.lean#L1225) (proved); [`DLMF.JacobiElliptic.jacobi_eq_theta_quotients`](DLMF/JacobiElliptic/Basic.lean#L535) (proved from admitted foundations).
- [22.2.E9](https://dlmf.nist.gov/22.2.E9): [`DLMF.JacobiElliptic.jacobiSck`](DLMF/JacobiElliptic/Basic.lean#L177) (definition); [`DLMF.JacobiElliptic.jacobiCsk`](DLMF/JacobiElliptic/Basic.lean#L195) (definition); [`DLMF.JacobiElliptic.jacobiPQk_eq_one_div`](DLMF/JacobiElliptic/Basic.lean#L1225) (proved); [`DLMF.JacobiElliptic.jacobi_eq_theta_quotients`](DLMF/JacobiElliptic/Basic.lean#L535) (proved from admitted foundations).
- [22.2.E10](https://dlmf.nist.gov/22.2.E10): [`DLMF.JacobiElliptic.jacobiPQk_eq_one_div`](DLMF/JacobiElliptic/Basic.lean#L1225) (proved); [`DLMF.JacobiElliptic.jacobiPQk_eq_div`](DLMF/JacobiElliptic/Basic.lean#L1236) (proved); [`DLMF.JacobiElliptic.jacobiPQk_self`](DLMF/JacobiElliptic/Basic.lean#L1246) (proved). Glaisher relation pq = pr/qr: unconditional reciprocal form `jacobiPQk_eq_one_div` and the quotient form for a letter r regular at z (`jacobiRegulark`).
- [22.2.E11](https://dlmf.nist.gov/22.2.E11): [`DLMF.JacobiElliptic.jacobiPQk_eq_neville`](DLMF/JacobiElliptic/Basic.lean#L1373) (proved). Neville theta form; `jacobiNevilleTau` is defined locally from the theta functions (ACQ20 owns Neville's functions in Ch. 20); Mathlib: [`jacobiTheta₂`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.html#jacobiTheta₂).
- [22.2.E12](https://dlmf.nist.gov/22.2.E12): [`DLMF.JacobiElliptic.compEllIntKpTau`](DLMF/JacobiElliptic/Basic.lean#L99) (definition); [`DLMF.JacobiElliptic.jacobiTauk`](DLMF/JacobiElliptic/Basic.lean#L138) (definition). τ = iK'/K; K'(τ) := -iτK(τ) in the lattice form.

## [§22.4 Periods, Poles, and Zeros](https://dlmf.nist.gov/22.4)

- [22.4.T1](https://dlmf.nist.gov/22.4.T1): [`DLMF.JacobiElliptic.jacobiPQk_zeros_poles`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L1060) (proved); [`DLMF.JacobiElliptic.jacobiSnk_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L880) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiCdk_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L889) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiDck_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L898) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiNsk_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L907) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiCnk_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L916) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiSdk_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L925) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiNck_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L934) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiDsk_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L943) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiDnk_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L952) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiNdk_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L962) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiSck_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L972) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiCsk_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L982) (proved from admitted foundations); [`DLMF.Elliptic.Real.jacobiSnm_add_four_compEllIntKm`](DLMF/Elliptic/Jacobi.lean#L287) (proved). Periods proved for all twelve functions (`jacobiXxk_periodic`); pole positions and congruence classes in `jacobiPQk_zeros_poles` (admitted).
- [22.4.T2](https://dlmf.nist.gov/22.4.T2): [`DLMF.JacobiElliptic.jacobiPQk_zeros_poles`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L1060) (proved); [`DLMF.JacobiElliptic.jacobiSnk_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L880) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiCdk_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L889) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiDck_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L898) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiNsk_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L907) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiCnk_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L916) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiSdk_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L925) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiNck_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L934) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiDsk_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L943) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiDnk_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L952) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiNdk_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L962) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiSck_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L972) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiCsk_periodic`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L982) (proved from admitted foundations). As 22.4.T1 for zeros.
- [22.4.T3](https://dlmf.nist.gov/22.4.T3): [`DLMF.JacobiElliptic.jacobiSnk_shift`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L620) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiCnk_shift`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L639) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiDnk_shift`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L658) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiCdk_shift`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L677) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiSdk_shift`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L696) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiNdk_shift`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L715) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiDck_shift`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L734) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiNck_shift`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L753) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiSck_shift`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L772) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiNsk_shift`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L791) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiDsk_shift`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L810) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiCsk_shift`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L829) (proved from admitted foundations); [`DLMF.Elliptic.Real.jacobi_add_two_compEllIntKm`](DLMF/Elliptic/Jacobi.lean#L277) (proved); [`DLMF.Elliptic.Real.jacobi_add_compEllIntKm`](DLMF/Elliptic/JacobiIdentities.lean#L235) (proved). All 12 rows × 6 columns (K, K+iK', iK', 2K, 2K+2iK', 2iK') proved: lattice τ-form `jacobiXxTau_shift` from half-period theta shifts, k-form `jacobiXxk_shift` via the inversion admission.

## [§22.5 Special Values](https://dlmf.nist.gov/22.5)

- [22.5.T1](https://dlmf.nist.gov/22.5.T1): [`DLMF.JacobiElliptic.jacobiSnk_specialValues`](DLMF/JacobiElliptic/SpecialValues.lean#L102) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiCnk_specialValues`](DLMF/JacobiElliptic/SpecialValues.lean#L135) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiDnk_specialValues`](DLMF/JacobiElliptic/SpecialValues.lean#L168) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiCdk_specialValues`](DLMF/JacobiElliptic/SpecialValues.lean#L201) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiSdk_specialValues`](DLMF/JacobiElliptic/SpecialValues.lean#L234) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiNdk_specialValues`](DLMF/JacobiElliptic/SpecialValues.lean#L267) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiDck_specialValues`](DLMF/JacobiElliptic/SpecialValues.lean#L300) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiNck_specialValues`](DLMF/JacobiElliptic/SpecialValues.lean#L333) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiSck_specialValues`](DLMF/JacobiElliptic/SpecialValues.lean#L366) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiNsk_specialValues`](DLMF/JacobiElliptic/SpecialValues.lean#L399) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiDsk_specialValues`](DLMF/JacobiElliptic/SpecialValues.lean#L420) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiCsk_specialValues`](DLMF/JacobiElliptic/SpecialValues.lean#L441) (proved from admitted foundations); [`DLMF.JacobiElliptic.jacobiSnk_specialDerivs`](DLMF/JacobiElliptic/SpecialValues.lean#L511) (proved); [`DLMF.JacobiElliptic.jacobiCnk_specialDerivs`](DLMF/JacobiElliptic/SpecialValues.lean#L582) (proved); [`DLMF.JacobiElliptic.jacobiDnk_specialDerivs`](DLMF/JacobiElliptic/SpecialValues.lean#L653) (proved); [`DLMF.JacobiElliptic.jacobiCdk_specialDerivs`](DLMF/JacobiElliptic/SpecialValues.lean#L724) (proved); [`DLMF.JacobiElliptic.jacobiSdk_specialDerivs`](DLMF/JacobiElliptic/SpecialValues.lean#L797) (proved); [`DLMF.JacobiElliptic.jacobiNdk_specialDerivs`](DLMF/JacobiElliptic/SpecialValues.lean#L870) (proved); [`DLMF.JacobiElliptic.jacobiDck_specialDerivs`](DLMF/JacobiElliptic/SpecialValues.lean#L943) (proved); [`DLMF.JacobiElliptic.jacobiNck_specialDerivs`](DLMF/JacobiElliptic/SpecialValues.lean#L1016) (proved); [`DLMF.JacobiElliptic.jacobiSck_specialDerivs`](DLMF/JacobiElliptic/SpecialValues.lean#L1089) (proved); [`DLMF.JacobiElliptic.jacobiNsk_specialDerivs`](DLMF/JacobiElliptic/SpecialValues.lean#L1162) (proved); [`DLMF.JacobiElliptic.jacobiDsk_specialDerivs`](DLMF/JacobiElliptic/SpecialValues.lean#L1251) (proved); [`DLMF.JacobiElliptic.jacobiCsk_specialDerivs`](DLMF/JacobiElliptic/SpecialValues.lean#L1340) (proved); [`DLMF.Elliptic.Real.jacobi_compEllIntKm`](DLMF/Elliptic/Jacobi.lean#L298) (proved); [`DLMF.Elliptic.jacobi_zero`](DLMF/Elliptic/Jacobi.lean#L305) (proved). Values proved for all 12 functions (Lean junk value 0 at the poles is not asserted; poles are excluded). Derivatives and residues admitted; residues stated as limits of (z - z₀)·f(z) on a punctured neighbourhood. **Corrected** (DLMF erratum): the derivative of dc at K + iK' is -k = k'² sc nc there, printed k.
- [22.5.T2](https://dlmf.nist.gov/22.5.T2): [`DLMF.JacobiElliptic.jacobi_specialValues_HalfK`](DLMF/JacobiElliptic/SpecialValues.lean#L1653) (proved); [`DLMF.JacobiElliptic.jacobi_specialValues_HalfKKp`](DLMF/JacobiElliptic/SpecialValues.lean#L2038) (proved); [`DLMF.JacobiElliptic.jacobi_specialValues_HalfKp`](DLMF/JacobiElliptic/SpecialValues.lean#L1802) (proved); [`DLMF.JacobiElliptic.jacobi_specialValues_ThreeHalfK`](DLMF/JacobiElliptic/SpecialValues.lean#L1742) (proved); [`DLMF.JacobiElliptic.jacobi_specialValues_ThreeHalfKKp`](DLMF/JacobiElliptic/SpecialValues.lean#L2247) (proved); [`DLMF.JacobiElliptic.jacobi_specialValues_ThreeHalfKp`](DLMF/JacobiElliptic/SpecialValues.lean#L1847) (proved); [`DLMF.Elliptic.Real.jacobi_half_compEllIntKm`](DLMF/Elliptic/JacobiIdentities.lean#L254) (proved). Admitted; principal square roots as printed, on the stated domain.
- [22.5.T3](https://dlmf.nist.gov/22.5.T3): [`DLMF.JacobiElliptic.tendsto_jacobiSnk_zero`](DLMF/JacobiElliptic/SpecialValues.lean#L2673) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiCdk_zero`](DLMF/JacobiElliptic/SpecialValues.lean#L2680) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiDck_zero`](DLMF/JacobiElliptic/SpecialValues.lean#L2687) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiNsk_zero`](DLMF/JacobiElliptic/SpecialValues.lean#L2695) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiCnk_zero`](DLMF/JacobiElliptic/SpecialValues.lean#L2703) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiSdk_zero`](DLMF/JacobiElliptic/SpecialValues.lean#L2710) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiNck_zero`](DLMF/JacobiElliptic/SpecialValues.lean#L2717) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiDsk_zero`](DLMF/JacobiElliptic/SpecialValues.lean#L2725) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiDnk_zero`](DLMF/JacobiElliptic/SpecialValues.lean#L2733) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiNdk_zero`](DLMF/JacobiElliptic/SpecialValues.lean#L2740) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiSck_zero`](DLMF/JacobiElliptic/SpecialValues.lean#L2747) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiCsk_zero`](DLMF/JacobiElliptic/SpecialValues.lean#L2755) (proved); [`DLMF.Elliptic.jacobi_zero_param`](DLMF/Elliptic/Jacobi.lean#L318) (proved). Limits as real k → 0+ (pointwise in z, away from the poles of the limit function); Mathlib: [`Complex.sin`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Trigonometric.html#Complex.sin).
- [22.5.T4](https://dlmf.nist.gov/22.5.T4): [`DLMF.JacobiElliptic.tendsto_jacobiSnk_one`](DLMF/JacobiElliptic/SpecialValues.lean#L2807) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiCdk_one`](DLMF/JacobiElliptic/SpecialValues.lean#L2823) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiDck_one`](DLMF/JacobiElliptic/SpecialValues.lean#L2838) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiNsk_one`](DLMF/JacobiElliptic/SpecialValues.lean#L2853) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiCnk_one`](DLMF/JacobiElliptic/SpecialValues.lean#L2869) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiSdk_one`](DLMF/JacobiElliptic/SpecialValues.lean#L2885) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiNck_one`](DLMF/JacobiElliptic/SpecialValues.lean#L2901) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiDsk_one`](DLMF/JacobiElliptic/SpecialValues.lean#L2917) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiDnk_one`](DLMF/JacobiElliptic/SpecialValues.lean#L2933) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiNdk_one`](DLMF/JacobiElliptic/SpecialValues.lean#L2949) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiSck_one`](DLMF/JacobiElliptic/SpecialValues.lean#L2965) (proved); [`DLMF.JacobiElliptic.tendsto_jacobiCsk_one`](DLMF/JacobiElliptic/SpecialValues.lean#L2981) (proved). Limits as real k → 1- (pointwise in z, away from the poles of the limit function); Mathlib: [`Complex.tanh`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Trigonometric.html#Complex.tanh).

## [§22.6 Elementary Identities](https://dlmf.nist.gov/22.6)

- [22.6.E1](https://dlmf.nist.gov/22.6.E1): [`DLMF.JacobiElliptic.jacobi_sq_sum`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L46) (proved); [`DLMF.Elliptic.Real.jacobiSnm_sq_add_jacobiCnm_sq`](DLMF/Elliptic/Jacobi.lean#L227) (proved); [`DLMF.Elliptic.Real.mul_jacobiSnm_sq_add_jacobiDnm_sq`](DLMF/Elliptic/Jacobi.lean#L233) (proved); [`DLMF.Elliptic.Real.jacobiDnm_sq_sub_mul_jacobiCnm_sq`](DLMF/Elliptic/JacobiIdentities.lean#L34) (proved). Complex k-form admitted; real forms already in the project (`Real.jacobiSnm_sq_add_jacobiCnm_sq`, `Real.mul_jacobiSnm_sq_add_jacobiDnm_sq`).
- [22.6.E2](https://dlmf.nist.gov/22.6.E2): [`DLMF.JacobiElliptic.jacobi_sq_sum_s`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L75) (proved from admitted foundations).
- [22.6.E3](https://dlmf.nist.gov/22.6.E3): [`DLMF.JacobiElliptic.jacobi_sq_sum_c`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L88) (proved from admitted foundations).
- [22.6.E4](https://dlmf.nist.gov/22.6.E4): [`DLMF.JacobiElliptic.jacobi_sq_sum_d`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L101) (proved from admitted foundations).
- [22.6.E5](https://dlmf.nist.gov/22.6.E5): [`DLMF.JacobiElliptic.jacobiSnk_two_mul`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L116) (proved from admitted foundations).
- [22.6.E6](https://dlmf.nist.gov/22.6.E6): [`DLMF.JacobiElliptic.jacobiCnk_two_mul`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L127) (proved from admitted foundations).
- [22.6.E7](https://dlmf.nist.gov/22.6.E7): [`DLMF.JacobiElliptic.jacobiDnk_two_mul`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L149) (proved from admitted foundations).
- [22.6.E8](https://dlmf.nist.gov/22.6.E8): [`DLMF.JacobiElliptic.jacobiCdk_two_mul`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L171) (proved from admitted foundations).
- [22.6.E9](https://dlmf.nist.gov/22.6.E9): [`DLMF.JacobiElliptic.jacobiSdk_two_mul`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L184) (proved from admitted foundations).
- [22.6.E10](https://dlmf.nist.gov/22.6.E10): [`DLMF.JacobiElliptic.jacobiNdk_two_mul`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L196) (proved from admitted foundations).
- [22.6.E11](https://dlmf.nist.gov/22.6.E11): [`DLMF.JacobiElliptic.jacobiDck_two_mul`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L208) (proved from admitted foundations).
- [22.6.E12](https://dlmf.nist.gov/22.6.E12): [`DLMF.JacobiElliptic.jacobiNck_two_mul`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L220) (proved from admitted foundations).
- [22.6.E13](https://dlmf.nist.gov/22.6.E13): [`DLMF.JacobiElliptic.jacobiSck_two_mul`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L231) (proved from admitted foundations).
- [22.6.E14](https://dlmf.nist.gov/22.6.E14): [`DLMF.JacobiElliptic.jacobi_two_mul_s`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L298) (proved).
- [22.6.E15](https://dlmf.nist.gov/22.6.E15): [`DLMF.JacobiElliptic.jacobi_two_mul_s`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L298) (proved).
- [22.6.E16](https://dlmf.nist.gov/22.6.E16): [`DLMF.JacobiElliptic.jacobi_two_mul_s`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L298) (proved).
- [22.6.E17](https://dlmf.nist.gov/22.6.E17): [`DLMF.JacobiElliptic.jacobi_two_mul_ratio`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L349) (proved).
- [22.6.E18](https://dlmf.nist.gov/22.6.E18): [`DLMF.JacobiElliptic.jacobi_two_mul_ratio`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L349) (proved).
- [22.6.E19](https://dlmf.nist.gov/22.6.E19): [`DLMF.JacobiElliptic.jacobiSnk_half_sq`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L381) (proved).
- [22.6.E20](https://dlmf.nist.gov/22.6.E20): [`DLMF.JacobiElliptic.jacobiCnk_half_sq`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L416) (proved).
- [22.6.E21](https://dlmf.nist.gov/22.6.E21): [`DLMF.JacobiElliptic.jacobiDnk_half_sq`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L467) (proved).
- [22.6.E22](https://dlmf.nist.gov/22.6.E22): [`DLMF.JacobiElliptic.jacobiPQk_half_sq`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L516) (admitted).
- [22.6.T1](https://dlmf.nist.gov/22.6.T1): [`DLMF.JacobiElliptic.jacobi_imaginary_transformation`](DLMF/JacobiElliptic/ElementaryIdentities.lean#L668) (proved). Jacobi imaginary transformation, all 12 rows; k' is the principal comodulus.

## [§22.7 Landen Transformations](https://dlmf.nist.gov/22.7)

- [22.7.E1](https://dlmf.nist.gov/22.7.E1): [`DLMF.JacobiElliptic.jacobiLandenDescModulus`](DLMF/JacobiElliptic/Landen.lean#L30) (definition). k₁ = (1-k')/(1+k') with the principal k'.
- [22.7.E2](https://dlmf.nist.gov/22.7.E2): [`DLMF.JacobiElliptic.jacobi_landen_descending`](DLMF/JacobiElliptic/Landen.lean#L52) (admitted).
- [22.7.E3](https://dlmf.nist.gov/22.7.E3): [`DLMF.JacobiElliptic.jacobi_landen_descending`](DLMF/JacobiElliptic/Landen.lean#L52) (admitted).
- [22.7.E4](https://dlmf.nist.gov/22.7.E4): [`DLMF.JacobiElliptic.jacobi_landen_descending`](DLMF/JacobiElliptic/Landen.lean#L52) (admitted).
- [22.7.E5](https://dlmf.nist.gov/22.7.E5): [`DLMF.JacobiElliptic.jacobiLandenAscModulus`](DLMF/JacobiElliptic/Landen.lean#L34) (definition); [`DLMF.JacobiElliptic.jacobiLandenAscComodulus`](DLMF/JacobiElliptic/Landen.lean#L38) (definition); [`DLMF.JacobiElliptic.jacobiLandenAscComodulus_sq`](DLMF/JacobiElliptic/Landen.lean#L42) (proved). k₂ = 2√k/(1+k) (principal root), k₂' = (1-k)/(1+k) as DLMF defines it; k₂'² = 1 - k₂² proved. Note: k₂' is not the principal √(1-k₂²) for every complex k (e.g. k = 1.3 + 0.4i); the Landen formulas hold with DLMF's quotient.
- [22.7.E6](https://dlmf.nist.gov/22.7.E6): [`DLMF.JacobiElliptic.jacobi_landen_ascending`](DLMF/JacobiElliptic/Landen.lean#L73) (admitted).
- [22.7.E7](https://dlmf.nist.gov/22.7.E7): [`DLMF.JacobiElliptic.jacobi_landen_ascending`](DLMF/JacobiElliptic/Landen.lean#L73) (admitted).
- [22.7.E8](https://dlmf.nist.gov/22.7.E8): [`DLMF.JacobiElliptic.jacobi_landen_ascending`](DLMF/JacobiElliptic/Landen.lean#L73) (admitted).

## [§22.8 Addition Theorems](https://dlmf.nist.gov/22.8)

- [22.8.E1](https://dlmf.nist.gov/22.8.E1): [`DLMF.JacobiElliptic.jacobiSnk_add`](DLMF/JacobiElliptic/Addition.lean#L306) (proved); [`DLMF.Elliptic.Real.jacobiSnm_add`](DLMF/Elliptic/JacobiIdentities.lean#L107) (proved). Hypotheses: the letter n regular at u, v (θ₄ ≠ 0) and the printed denominator nonzero; similarly d, c, s for 22.8.4–6, 7–9, 10–12. Real forms for 22.8.1–3 already exist (`Real.jacobiSnm_add` etc.).
- [22.8.E2](https://dlmf.nist.gov/22.8.E2): [`DLMF.JacobiElliptic.jacobiCnk_add`](DLMF/JacobiElliptic/Addition.lean#L343) (proved); [`DLMF.Elliptic.Real.jacobiCnm_add`](DLMF/Elliptic/JacobiIdentities.lean#L148) (proved).
- [22.8.E3](https://dlmf.nist.gov/22.8.E3): [`DLMF.JacobiElliptic.jacobiDnk_add`](DLMF/JacobiElliptic/Addition.lean#L379) (proved); [`DLMF.Elliptic.Real.jacobiDnm_add`](DLMF/Elliptic/JacobiIdentities.lean#L188) (proved).
- [22.8.E4](https://dlmf.nist.gov/22.8.E4): [`DLMF.JacobiElliptic.jacobiCdk_add`](DLMF/JacobiElliptic/Addition.lean#L415) (proved).
- [22.8.E5](https://dlmf.nist.gov/22.8.E5): [`DLMF.JacobiElliptic.jacobiSdk_add`](DLMF/JacobiElliptic/Addition.lean#L451) (proved).
- [22.8.E6](https://dlmf.nist.gov/22.8.E6): [`DLMF.JacobiElliptic.jacobiNdk_add`](DLMF/JacobiElliptic/Addition.lean#L487) (proved).
- [22.8.E7](https://dlmf.nist.gov/22.8.E7): [`DLMF.JacobiElliptic.jacobiDck_add`](DLMF/JacobiElliptic/Addition.lean#L523) (proved).
- [22.8.E8](https://dlmf.nist.gov/22.8.E8): [`DLMF.JacobiElliptic.jacobiNck_add`](DLMF/JacobiElliptic/Addition.lean#L559) (proved).
- [22.8.E9](https://dlmf.nist.gov/22.8.E9): [`DLMF.JacobiElliptic.jacobiSck_add`](DLMF/JacobiElliptic/Addition.lean#L594) (proved).
- [22.8.E10](https://dlmf.nist.gov/22.8.E10): [`DLMF.JacobiElliptic.jacobiNsk_add`](DLMF/JacobiElliptic/Addition.lean#L629) (proved).
- [22.8.E11](https://dlmf.nist.gov/22.8.E11): [`DLMF.JacobiElliptic.jacobiDsk_add`](DLMF/JacobiElliptic/Addition.lean#L663) (proved).
- [22.8.E12](https://dlmf.nist.gov/22.8.E12): [`DLMF.JacobiElliptic.jacobiCsk_add`](DLMF/JacobiElliptic/Addition.lean#L697) (proved).
- [22.8.E13](https://dlmf.nist.gov/22.8.E13): [`DLMF.JacobiElliptic.jacobiSnk_add_alt`](DLMF/JacobiElliptic/Addition.lean#L731) (proved).
- [22.8.E14](https://dlmf.nist.gov/22.8.E14): [`DLMF.JacobiElliptic.jacobiSnk_add_alt₂`](DLMF/JacobiElliptic/Addition.lean#L766) (proved).
- [22.8.E15](https://dlmf.nist.gov/22.8.E15): [`DLMF.JacobiElliptic.jacobiCnk_add_alt`](DLMF/JacobiElliptic/Addition.lean#L802) (proved).
- [22.8.E16](https://dlmf.nist.gov/22.8.E16): [`DLMF.JacobiElliptic.jacobiCnk_add_alt₂`](DLMF/JacobiElliptic/Addition.lean#L838) (proved).
- [22.8.E17](https://dlmf.nist.gov/22.8.E17): [`DLMF.JacobiElliptic.jacobiDnk_add_alt`](DLMF/JacobiElliptic/Addition.lean#L874) (proved).
- [22.8.E18](https://dlmf.nist.gov/22.8.E18): [`DLMF.JacobiElliptic.jacobiDnk_add_alt₂`](DLMF/JacobiElliptic/Addition.lean#L910) (proved).
- [22.8.E19](https://dlmf.nist.gov/22.8.E19): [`DLMF.JacobiElliptic.jacobi_det_sum_zero`](DLMF/JacobiElliptic/Addition.lean#L1165) (admitted); [`DLMF.JacobiElliptic.jacobi_prod_sum_zero`](DLMF/JacobiElliptic/Addition.lean#L1174) (admitted).
- [22.8.E20](https://dlmf.nist.gov/22.8.E20): [`DLMF.JacobiElliptic.jacobi_det_sum_zero`](DLMF/JacobiElliptic/Addition.lean#L1165) (admitted).
- [22.8.E21](https://dlmf.nist.gov/22.8.E21): [`DLMF.JacobiElliptic.jacobi_prod_sum_zero`](DLMF/JacobiElliptic/Addition.lean#L1174) (admitted).
- [22.8.E22](https://dlmf.nist.gov/22.8.E22): [`DLMF.JacobiElliptic.jacobi_det_sum_two_K`](DLMF/JacobiElliptic/Addition.lean#L1183) (admitted); [`DLMF.JacobiElliptic.jacobi_det_sum_two_K'`](DLMF/JacobiElliptic/Addition.lean#L1196) (admitted).
- [22.8.E23](https://dlmf.nist.gov/22.8.E23): [`DLMF.JacobiElliptic.jacobi_det_sum_two_K`](DLMF/JacobiElliptic/Addition.lean#L1183) (admitted); [`DLMF.JacobiElliptic.jacobi_det_sum_two_K'`](DLMF/JacobiElliptic/Addition.lean#L1196) (admitted). **Corrected** (DLMF erratum): as printed (columns sn cn, cn dn, cn, dn; Σz = 2K) the determinant is nonzero numerically (≈ -0.107 + 0.033i at k = 0.6). Two corrected forms acquired: third column sn (`jacobi_det_sum_two_K`) or second column sn dn (`jacobi_det_sum_two_K'`).
- [22.8.E24](https://dlmf.nist.gov/22.8.E24): [`DLMF.JacobiElliptic.jacobiDnThreePointExpr_const`](DLMF/JacobiElliptic/Addition.lean#L1218) (proved).
- [22.8.E25](https://dlmf.nist.gov/22.8.E25): [`DLMF.JacobiElliptic.jacobiDnThreePointExpr_const`](DLMF/JacobiElliptic/Addition.lean#L1218) (proved).
- [22.8.E26](https://dlmf.nist.gov/22.8.E26): [`DLMF.JacobiElliptic.jacobiDn_four_point`](DLMF/JacobiElliptic/Addition.lean#L323) (proved from admitted foundations). 22.8.26–27 proved (from the shift table, via dn(z + 2K) = dn z and dn(z+K) = k'/dn z).
- [22.8.E27](https://dlmf.nist.gov/22.8.E27): [`DLMF.JacobiElliptic.jacobiDn_four_point`](DLMF/JacobiElliptic/Addition.lean#L323) (proved from admitted foundations).

## [§22.9 Cyclic Identities](https://dlmf.nist.gov/22.9)

- [22.9.E1](https://dlmf.nist.gov/22.9.E1): [`DLMF.JacobiElliptic.jacobiCyclicArg`](DLMF/JacobiElliptic/Cyclic.lean#L36) (definition); [`DLMF.JacobiElliptic.jacobiCyclicS`](DLMF/JacobiElliptic/Cyclic.lean#L40) (definition). Cyclic quantities s, c, d of order 2 and 4 as functions of (m, p, z, k); `jacobiCyclicArg` encodes the shifted arguments.
- [22.9.E2](https://dlmf.nist.gov/22.9.E2): [`DLMF.JacobiElliptic.jacobiCyclicC`](DLMF/JacobiElliptic/Cyclic.lean#L44) (definition).
- [22.9.E3](https://dlmf.nist.gov/22.9.E3): [`DLMF.JacobiElliptic.jacobiCyclicD`](DLMF/JacobiElliptic/Cyclic.lean#L48) (definition).
- [22.9.E4](https://dlmf.nist.gov/22.9.E4): [`DLMF.JacobiElliptic.jacobiCyclicArg`](DLMF/JacobiElliptic/Cyclic.lean#L36) (definition); [`DLMF.JacobiElliptic.jacobiCyclicS`](DLMF/JacobiElliptic/Cyclic.lean#L40) (definition).
- [22.9.E5](https://dlmf.nist.gov/22.9.E5): [`DLMF.JacobiElliptic.jacobiCyclicC`](DLMF/JacobiElliptic/Cyclic.lean#L44) (definition).
- [22.9.E6](https://dlmf.nist.gov/22.9.E6): [`DLMF.JacobiElliptic.jacobiCyclicD`](DLMF/JacobiElliptic/Cyclic.lean#L48) (definition).
- [22.9.E7](https://dlmf.nist.gov/22.9.E7): [`DLMF.JacobiElliptic.jacobiCyclicKappa`](DLMF/JacobiElliptic/Cyclic.lean#L52) (definition); [`DLMF.JacobiElliptic.jacobi_cyclic_s4_pairs`](DLMF/JacobiElliptic/Cyclic.lean#L163) (proved); [`DLMF.JacobiElliptic.jacobi_cyclic_c4_pairs`](DLMF/JacobiElliptic/Cyclic.lean#L247) (proved); [`DLMF.JacobiElliptic.jacobi_cyclic_d_pairs`](DLMF/JacobiElliptic/Cyclic.lean#L398) (proved); [`DLMF.JacobiElliptic.jacobi_cyclic_s4_triple`](DLMF/JacobiElliptic/Cyclic.lean#L710) (proved); [`DLMF.JacobiElliptic.jacobi_cyclic_c4_triple`](DLMF/JacobiElliptic/Cyclic.lean#L800) (proved); [`DLMF.JacobiElliptic.jacobi_cyclic_d2_triple`](DLMF/JacobiElliptic/Cyclic.lean#L932) (proved); [`DLMF.JacobiElliptic.jacobi_cyclic_scc_triple`](DLMF/JacobiElliptic/Cyclic.lean#L1140) (proved); [`DLMF.JacobiElliptic.jacobi_cyclic_scdd_three`](DLMF/JacobiElliptic/Cyclic.lean#L1439) (proved); [`DLMF.JacobiElliptic.jacobi_cyclic_sdcc_three`](DLMF/JacobiElliptic/Cyclic.lean#L1721) (proved).
- [22.9.E8](https://dlmf.nist.gov/22.9.E8): [`DLMF.JacobiElliptic.jacobi_cyclic_s4_pairs`](DLMF/JacobiElliptic/Cyclic.lean#L163) (proved).
- [22.9.E9](https://dlmf.nist.gov/22.9.E9): [`DLMF.JacobiElliptic.jacobi_cyclic_c4_pairs`](DLMF/JacobiElliptic/Cyclic.lean#L247) (proved).
- [22.9.E10](https://dlmf.nist.gov/22.9.E10): [`DLMF.JacobiElliptic.jacobi_cyclic_d_pairs`](DLMF/JacobiElliptic/Cyclic.lean#L398) (proved).
- [22.9.E11](https://dlmf.nist.gov/22.9.E11): [`DLMF.JacobiElliptic.jacobi_cyclic_d2_two`](DLMF/JacobiElliptic/Cyclic.lean#L670) (proved).
- [22.9.E12](https://dlmf.nist.gov/22.9.E12): [`DLMF.JacobiElliptic.jacobi_cyclic_csd_two`](DLMF/JacobiElliptic/Cyclic.lean#L693) (proved).
- [22.9.E13](https://dlmf.nist.gov/22.9.E13): [`DLMF.JacobiElliptic.jacobi_cyclic_s4_triple`](DLMF/JacobiElliptic/Cyclic.lean#L710) (proved).
- [22.9.E14](https://dlmf.nist.gov/22.9.E14): [`DLMF.JacobiElliptic.jacobi_cyclic_c4_triple`](DLMF/JacobiElliptic/Cyclic.lean#L800) (proved).
- [22.9.E15](https://dlmf.nist.gov/22.9.E15): [`DLMF.JacobiElliptic.jacobi_cyclic_d2_triple`](DLMF/JacobiElliptic/Cyclic.lean#L932) (proved).
- [22.9.E16](https://dlmf.nist.gov/22.9.E16): [`DLMF.JacobiElliptic.jacobi_cyclic_scc_triple`](DLMF/JacobiElliptic/Cyclic.lean#L1140) (proved).
- [22.9.E17](https://dlmf.nist.gov/22.9.E17): [`DLMF.JacobiElliptic.jacobi_cyclic_d2_four`](DLMF/JacobiElliptic/Cyclic.lean#L1305) (proved).
- [22.9.E18](https://dlmf.nist.gov/22.9.E18): [`DLMF.JacobiElliptic.jacobi_cyclic_d2_four_sq`](DLMF/JacobiElliptic/Cyclic.lean#L1338) (proved).
- [22.9.E19](https://dlmf.nist.gov/22.9.E19): [`DLMF.JacobiElliptic.jacobi_cyclic_csd_four`](DLMF/JacobiElliptic/Cyclic.lean#L1369) (proved).
- [22.9.E20](https://dlmf.nist.gov/22.9.E20): [`DLMF.JacobiElliptic.jacobi_cyclic_d2_two_rank4`](DLMF/JacobiElliptic/Cyclic.lean#L1394) (proved).
- [22.9.E21](https://dlmf.nist.gov/22.9.E21): [`DLMF.JacobiElliptic.jacobi_cyclic_cscs_two`](DLMF/JacobiElliptic/Cyclic.lean#L1415) (proved).
- [22.9.E22](https://dlmf.nist.gov/22.9.E22): [`DLMF.JacobiElliptic.jacobi_cyclic_scdd_three`](DLMF/JacobiElliptic/Cyclic.lean#L1439) (proved).
- [22.9.E23](https://dlmf.nist.gov/22.9.E23): [`DLMF.JacobiElliptic.jacobi_cyclic_sdcc_three`](DLMF/JacobiElliptic/Cyclic.lean#L1721) (proved). **Corrected** (DLMF erratum): printed right side repeats s₂,₃d₂,₃; corrected last summand s₃,₃d₃,₃ (printed RHS ≈ 4.208 - 0.036i vs LHS ≈ 0.552 + 0.183i at k = 0.6, z = 0.37 + 0.21i).
## Analytical prose and exclusions (part A)

- [22.1.p1](https://dlmf.nist.gov/22.1#p1): notation pointer; no mathematical content.
- [22.1.p2](https://dlmf.nist.gov/22.1#p2): notation for x, y, z, k, k', K, K', q, τ; `jacobiComodulusk` (principal (1-k²)^{1/2}) with `jacobiComodulusk_sq` (proved), `compEllIntKk`, `compEllIntKpk`, `jacobiNomek`, `jacobiTauk`. The DLMF restriction 0 ≤ k ≤ 1 is widened to `jacobiModulusDomain` as explained above.
- [22.1.p3](https://dlmf.nist.gov/22.1#p3): typographical convention (derivatives as differentials).
- [22.1.p4](https://dlmf.nist.gov/22.1#p4): the twelve functions `jacobiSnk` … `jacobiCsk` (and `jacobiSnTau` … `jacobiCsTau`), generic `jacobiPQk` with `JacobiLetter`.
- [22.1.p5](https://dlmf.nist.gov/22.1#p5): historical notation; excluded: bibliographic.
- [22.2.p1](https://dlmf.nist.gov/22.2#p1), [22.2.p2](https://dlmf.nist.gov/22.2#p2): carry 22.2.1–22.2.9, recorded above.
- [22.2.p3](https://dlmf.nist.gov/22.2#p3): double periodicity (`jacobiXxk_periodic`, proved from foundations), meromorphy in z (`jacobiPQk_meromorphicAt`, proved from foundations), meromorphy in k (`jacobiPQk_meromorphicOn_modulus`, admitted), reality for real z and k ∈ (0, 1) (`jacobiPQk_real`, admitted; existing real theory in `DLMF/Elliptic/Jacobi.lean`); simple poles and zeros in `jacobiPQk_zeros_poles` (admitted). Lean tag `22.2`.
- [22.2.Px1.p1](https://dlmf.nist.gov/22.2#Px1.p1): carries 22.2.10.
- [22.2.Px1.p2](https://dlmf.nist.gov/22.2#Px1.p2): parity: `jacobiPQk_neg` (proved, admission-free), `jacobiLetterTheta_neg`, `jacobiZetak_neg`; real `DLMF.Elliptic.jacobi_neg`. Lean tag `22.2`.
- [22.2.Px1.p3](https://dlmf.nist.gov/22.2#Px1.p3): carries 22.2.11–22.2.12.
- [22.2](https://dlmf.nist.gov/22.2): [`DLMF.Elliptic.jacobi_neg`](DLMF/Elliptic/Jacobi.lean#L311) (proved); [`DLMF.JacobiElliptic.jacobiPQk_meromorphicAt`](DLMF/JacobiElliptic/Basic.lean#L1525) (proved); [`DLMF.JacobiElliptic.jacobiPQk_meromorphicOn_modulus`](DLMF/JacobiElliptic/Basic.lean#L1405) (proved); [`DLMF.JacobiElliptic.jacobiPQk_neg`](DLMF/JacobiElliptic/Basic.lean#L1261) (proved); [`DLMF.JacobiElliptic.jacobiPQk_real`](DLMF/JacobiElliptic/Basic.lean#L1493) (proved).
- [22.4.i.p1](https://dlmf.nist.gov/22.4#i.p1), [22.4.i.p3](https://dlmf.nist.gov/22.4#i.p3): poles and zeros at the congruent points z₀ + 2mK + 2niK': `jacobiCongruentk`, `jacobiLetterPointk`, `jacobiPQk_zeros_poles` (admitted; tagged 22.4.T1, 22.4.T2, 22.4.ii).
- [22.4.i.p2](https://dlmf.nist.gov/22.4#i.p2): copolar/coperiodic terminology; content is in Tables 22.4.1–2.
- [22.4.i.p4](https://dlmf.nist.gov/22.4#i.p4): excluded: graphics (Figure 22.4.1).
- [22.4.i.p5](https://dlmf.nist.gov/22.4#i.p5): k-zeros, bibliographic pointer (Walker 2009); excluded: bibliographic.
- [22.4.ii.p1](https://dlmf.nist.gov/22.4#ii.p1), [22.4.ii.p2](https://dlmf.nist.gov/22.4#ii.p2): the lattice mK + niK' and the unit-cell mnemonic: pq has a simple zero at p and a simple pole at q, and the half-periods/periods follow; `jacobiPQk_zeros_poles` (admitted, tag 22.4.ii) with the periods from Table 22.4.3. Figure 22.4.2 itself excluded: graphics.
- [22.4.iii.p1](https://dlmf.nist.gov/22.4#iii.p1), [22.4.iii.p2](https://dlmf.nist.gov/22.4#iii.p2): Table 22.4.3, recorded above.
- [22.4.ii](https://dlmf.nist.gov/22.4.ii): [`DLMF.JacobiElliptic.jacobiPQk_zeros_poles`](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L1060) (proved).
- [22.5.i.p1](https://dlmf.nist.gov/22.5#i.p1), [22.5.i.p2](https://dlmf.nist.gov/22.5#i.p2): Tables 22.5.1–22.5.2 (recorded above); "for the other nine functions ratios can be taken" is 22.2.10.
- [22.5.ii.p1](https://dlmf.nist.gov/22.5#ii.p1): K → π/2 as k → 0+ (`tendsto_compEllIntKk_zero`, proved), K' → π/2 as k → 1- (`tendsto_compEllIntKpk_one`, proved), |K'| → ∞ as k → 0+ and |K| → ∞ as k → 1- (`tendsto_norm_compEllIntKpk_zero`, `tendsto_norm_compEllIntKk_one`, admitted); degeneration in Tables 22.5.3–22.5.4. Lean tag `22.5.ii`.
- [22.5.ii.p2](https://dlmf.nist.gov/22.5#ii.p2): cross-reference to §§19.5, 19.12; excluded: cross-reference.
- [22.5.ii.p3](https://dlmf.nist.gov/22.5#ii.p3): lemniscatic and equianharmonic values of K, K', cross-reference to §23.5(iii), §23.5(v); excluded: cross-reference (Chapter 23 acquisition).
- [22.5.ii](https://dlmf.nist.gov/22.5.ii): [`DLMF.JacobiElliptic.tendsto_compEllIntKk_zero`](DLMF/JacobiElliptic/SpecialValues.lean#L2297) (proved); [`DLMF.JacobiElliptic.tendsto_compEllIntKpk_one`](DLMF/JacobiElliptic/SpecialValues.lean#L2313) (proved); [`DLMF.JacobiElliptic.tendsto_norm_compEllIntKk_one`](DLMF/JacobiElliptic/SpecialValues.lean#L2401) (proved); [`DLMF.JacobiElliptic.tendsto_norm_compEllIntKpk_zero`](DLMF/JacobiElliptic/SpecialValues.lean#L2391) (proved).
- [22.6.i.p1](https://dlmf.nist.gov/22.6#i.p1), [22.6.ii.p1](https://dlmf.nist.gov/22.6#ii.p1), [22.6.ii.p2](https://dlmf.nist.gov/22.6#ii.p2), [22.6.ii.p4](https://dlmf.nist.gov/22.6#ii.p4), [22.6.iii.p1](https://dlmf.nist.gov/22.6#iii.p1), [22.6.iii.p2](https://dlmf.nist.gov/22.6#iii.p2): carry 22.6.1–22.6.22 (22.6.22 for every permutation p, q, r of c, d, n, as `jacobiPQk_half_sq`).
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
complex Glaisher functions `jacobiPQk` of `DLMF.JacobiElliptic.Basic`, and their real-parameter
statements use the existing `DLMF.Elliptic.Real.jacobi*m` functions. Of the 192 tagged
declarations, 14 are definitions, 65 are proved and 113 are admitted. Mathlib and TauCeti
have no Jacobian elliptic functions, so there are no upstream pointers.

## Domains, conventions and source corrections (part B)

- Complex statements assume `k ∈ jacobiModulusDomain`. Derivative statements also assume
  that the theta denominator is nonzero. Real statements use `0 < k < 1` (`m = k²`) or `m < 1`.
- `Real.jacobiAmm` is totalized (`am(x, m) = x` for `m ≥ 1`). So 22.16.E5 (`am(x,1) = gd x`)
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
- Naming: Jacobi's Zeta function (22.16.E32) is `Real.jacobiZetaFunctionk`. This avoids
  `jacobiZetak`, which in Basic denotes the theta argument `ζ = πz/(2K)`. Jacobi's Epsilon
  function (22.16.E17) is `Real.jacobiEpsilonk`.
- Tag corrections (done by the coordinator, 2026-10-25): in `DLMF/Elliptic/Jacobi.lean`,
  `Real.hasDerivAt_jacobiSnm/Cnm/Dnm` are retagged Table 22.13.T1 (they were tagged 22.13.E1–E3);
  `Real.jacobiSnm_deriv_sq/Cnm/Dnm` now carry 22.13.E1–E3 and `Real.iteratedDeriv_two_jacobiSnm/Cnm/Dnm`
  22.13.E13–E15, with their docstrings renumbered; `Real.jacobiSnm_jacobiArcsnm` and `Real.jacobiArcsnm`
  carry 22.15.E1 and E4; `Real.jacobiAmm_add_two_compEllIntKm`, `Real.jacobiAmm_zero_param`,
  `Real.incEllIntFm_jacobiAmm` and `Real.hasDerivAt_jacobiAmm` carry 22.16.E2, E4, E11 and 22.16.i.
- No DLMF errata were found.

## Numbered formulas (part B)

## [§22.10 Maclaurin Series](https://dlmf.nist.gov/22.10)

- [22.10.E1](https://dlmf.nist.gov/22.10.E1): [`DLMF.JacobiElliptic.jacobiSnk_isBigO_maclaurin`](DLMF/JacobiElliptic/Maclaurin.lean#L229) (proved). Domain: k ∈ jacobiModulusDomain.
- [22.10.E2](https://dlmf.nist.gov/22.10.E2): [`DLMF.JacobiElliptic.jacobiCnk_isBigO_maclaurin`](DLMF/JacobiElliptic/Maclaurin.lean#L238) (proved). Domain: k ∈ jacobiModulusDomain.
- [22.10.E3](https://dlmf.nist.gov/22.10.E3): [`DLMF.JacobiElliptic.jacobiDnk_isBigO_maclaurin`](DLMF/JacobiElliptic/Maclaurin.lean#L246) (proved). Domain: k ∈ jacobiModulusDomain.
- [22.10.E4](https://dlmf.nist.gov/22.10.E4): [`DLMF.JacobiElliptic.jacobiSnk_isBigO_small_modulus`](DLMF/JacobiElliptic/Maclaurin.lean#L288) (admitted). Domain: k → 0 within jacobiModulusDomain, fixed z.
- [22.10.E5](https://dlmf.nist.gov/22.10.E5): [`DLMF.JacobiElliptic.jacobiCnk_isBigO_small_modulus`](DLMF/JacobiElliptic/Maclaurin.lean#L296) (admitted). Domain: k → 0 within jacobiModulusDomain, fixed z.
- [22.10.E6](https://dlmf.nist.gov/22.10.E6): [`DLMF.JacobiElliptic.jacobiDnk_isBigO_small_modulus`](DLMF/JacobiElliptic/Maclaurin.lean#L304) (admitted). Domain: k → 0 within jacobiModulusDomain, fixed z.
- [22.10.E7](https://dlmf.nist.gov/22.10.E7): [`DLMF.JacobiElliptic.jacobiSnk_isBigO_small_comodulus`](DLMF/JacobiElliptic/Maclaurin.lean#L311) (admitted). Domain: k → 1 within jacobiModulusDomain, fixed z with cosh z ≠ 0.
- [22.10.E8](https://dlmf.nist.gov/22.10.E8): [`DLMF.JacobiElliptic.jacobiCnk_isBigO_small_comodulus`](DLMF/JacobiElliptic/Maclaurin.lean#L319) (admitted). Domain: k → 1 within jacobiModulusDomain, fixed z with cosh z ≠ 0.
- [22.10.E9](https://dlmf.nist.gov/22.10.E9): [`DLMF.JacobiElliptic.jacobiDnk_isBigO_small_comodulus`](DLMF/JacobiElliptic/Maclaurin.lean#L328) (admitted). Domain: k → 1 within jacobiModulusDomain, fixed z with cosh z ≠ 0.
- [22.10.i](https://dlmf.nist.gov/22.10#i): [`DLMF.JacobiElliptic.jacobi_hasFPowerSeriesOnBall`](DLMF/JacobiElliptic/Maclaurin.lean#L254) (proved). Prose convergence statement (disc |z| < min(K,K')), real 0<k<1.

## [§22.11 Fourier and Hyperbolic Series](https://dlmf.nist.gov/22.11)

- [22.11.E1](https://dlmf.nist.gov/22.11.E1): [`DLMF.JacobiElliptic.jacobiSnk_hasSum_fourier`](DLMF/JacobiElliptic/FourierSeries.lean#L42) (proved). Domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition.
- [22.11.E2](https://dlmf.nist.gov/22.11.E2): [`DLMF.JacobiElliptic.jacobiCnk_hasSum_fourier`](DLMF/JacobiElliptic/FourierSeries.lean#L74) (proved). Domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition.
- [22.11.E3](https://dlmf.nist.gov/22.11.E3): [`DLMF.JacobiElliptic.jacobiDnk_hasSum_fourier`](DLMF/JacobiElliptic/FourierSeries.lean#L111) (admitted). Domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition.
- [22.11.E4](https://dlmf.nist.gov/22.11.E4): [`DLMF.JacobiElliptic.jacobiCdk_hasSum_fourier`](DLMF/JacobiElliptic/FourierSeries.lean#L122) (proved). Domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition.
- [22.11.E5](https://dlmf.nist.gov/22.11.E5): [`DLMF.JacobiElliptic.jacobiSdk_hasSum_fourier`](DLMF/JacobiElliptic/FourierSeries.lean#L138) (proved). Domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition.
- [22.11.E6](https://dlmf.nist.gov/22.11.E6): [`DLMF.JacobiElliptic.jacobiNdk_hasSum_fourier`](DLMF/JacobiElliptic/FourierSeries.lean#L157) (admitted). Domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition.
- [22.11.E7](https://dlmf.nist.gov/22.11.E7): [`DLMF.JacobiElliptic.jacobiNsk_hasSum_fourier`](DLMF/JacobiElliptic/FourierSeries.lean#L169) (proved). Domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition.
- [22.11.E8](https://dlmf.nist.gov/22.11.E8): [`DLMF.JacobiElliptic.jacobiDsk_hasSum_fourier`](DLMF/JacobiElliptic/FourierSeries.lean#L214) (proved). Domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition.
- [22.11.E9](https://dlmf.nist.gov/22.11.E9): [`DLMF.JacobiElliptic.jacobiCsk_hasSum_fourier`](DLMF/JacobiElliptic/FourierSeries.lean#L263) (admitted). Domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition.
- [22.11.E10](https://dlmf.nist.gov/22.11.E10): [`DLMF.JacobiElliptic.jacobiDck_hasSum_fourier`](DLMF/JacobiElliptic/FourierSeries.lean#L276) (proved). Domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition.
- [22.11.E11](https://dlmf.nist.gov/22.11.E11): [`DLMF.JacobiElliptic.jacobiNck_hasSum_fourier`](DLMF/JacobiElliptic/FourierSeries.lean#L293) (proved). Domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition.
- [22.11.E12](https://dlmf.nist.gov/22.11.E12): [`DLMF.JacobiElliptic.jacobiSck_hasSum_fourier`](DLMF/JacobiElliptic/FourierSeries.lean#L314) (admitted). Domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition.
- [22.11.E13](https://dlmf.nist.gov/22.11.E13): [`DLMF.JacobiElliptic.jacobiSnk_sq_hasSum_fourier`](DLMF/JacobiElliptic/FourierSeries.lean#L328) (admitted). Real 0<k<1 (complete E(k) has no complex counterpart in the library).
- [22.11.E14](https://dlmf.nist.gov/22.11.E14): [`DLMF.JacobiElliptic.jacobiSnk_sq_hasSum_sech`](DLMF/JacobiElliptic/FourierSeries.lean#L340) (admitted). Real 0<k<1.

## [§22.12 Expansions in Other Trigonometric Series](https://dlmf.nist.gov/22.12)

- [22.12.E1](https://dlmf.nist.gov/22.12.E1): [`DLMF.JacobiElliptic.jacobiTauk_eq`](DLMF/JacobiElliptic/PartialFractions.lean#L45) (proved). Definitional (rfl) against `jacobiTauk`.
- [22.12.E2](https://dlmf.nist.gov/22.12.E2): [`DLMF.JacobiElliptic.jacobiSnk_partialFractions`](DLMF/JacobiElliptic/PartialFractions.lean#L55) (proved). Domain: k ∈ jacobiModulusDomain, t not a pole.
- [22.12.E3](https://dlmf.nist.gov/22.12.E3): [`DLMF.JacobiElliptic.jacobiCnk_partialFractions`](DLMF/JacobiElliptic/PartialFractions.lean#L78) (proved). Domain: k ∈ jacobiModulusDomain, t not a pole.
- [22.12.E4](https://dlmf.nist.gov/22.12.E4): [`DLMF.JacobiElliptic.jacobiDnk_partialFractions`](DLMF/JacobiElliptic/PartialFractions.lean#L101) (admitted). Domain: k ∈ jacobiModulusDomain, t not a pole.
- [22.12.E5](https://dlmf.nist.gov/22.12.E5): [`DLMF.JacobiElliptic.jacobiCdk_partialFractions`](DLMF/JacobiElliptic/PartialFractions.lean#L115) (proved). Domain: k ∈ jacobiModulusDomain, t not a pole.
- [22.12.E6](https://dlmf.nist.gov/22.12.E6): [`DLMF.JacobiElliptic.jacobiSdk_partialFractions`](DLMF/JacobiElliptic/PartialFractions.lean#L138) (proved). Domain: k ∈ jacobiModulusDomain, t not a pole.
- [22.12.E7](https://dlmf.nist.gov/22.12.E7): [`DLMF.JacobiElliptic.jacobiNdk_partialFractions`](DLMF/JacobiElliptic/PartialFractions.lean#L161) (admitted). Domain: k ∈ jacobiModulusDomain, t not a pole.
- [22.12.E8](https://dlmf.nist.gov/22.12.E8): [`DLMF.JacobiElliptic.jacobiDck_partialFractions`](DLMF/JacobiElliptic/PartialFractions.lean#L175) (proved). Domain: k ∈ jacobiModulusDomain, t not a pole.
- [22.12.E9](https://dlmf.nist.gov/22.12.E9): [`DLMF.JacobiElliptic.jacobiNck_partialFractions`](DLMF/JacobiElliptic/PartialFractions.lean#L193) (proved). Domain: k ∈ jacobiModulusDomain, t not a pole.
- [22.12.E10](https://dlmf.nist.gov/22.12.E10): [`DLMF.JacobiElliptic.jacobiSck_partialFractions`](DLMF/JacobiElliptic/PartialFractions.lean#L211) (admitted). Domain: k ∈ jacobiModulusDomain, t not a pole.
- [22.12.E11](https://dlmf.nist.gov/22.12.E11): [`DLMF.JacobiElliptic.jacobiNsk_partialFractions`](DLMF/JacobiElliptic/PartialFractions.lean#L225) (proved). Domain: k ∈ jacobiModulusDomain, t not a pole.
- [22.12.E12](https://dlmf.nist.gov/22.12.E12): [`DLMF.JacobiElliptic.jacobiDsk_partialFractions`](DLMF/JacobiElliptic/PartialFractions.lean#L239) (proved). Domain: k ∈ jacobiModulusDomain, t not a pole.
- [22.12.E13](https://dlmf.nist.gov/22.12.E13): [`DLMF.JacobiElliptic.jacobiCsk_partialFractions`](DLMF/JacobiElliptic/PartialFractions.lean#L253) (admitted). Domain: k ∈ jacobiModulusDomain, t not a pole.

## [§22.13 Derivatives and Differential Equations](https://dlmf.nist.gov/22.13)

- [22.13.E1](https://dlmf.nist.gov/22.13.E1): [`DLMF.JacobiElliptic.deriv_jacobiSnk_sq`](DLMF/JacobiElliptic/Derivatives.lean#L693) (proved); [`DLMF.Elliptic.Real.jacobiSnm_deriv_sq`](DLMF/Elliptic/JacobiIdentities.lean#L42) (proved). Complex new statement; real m<1 form pre-existing (tagged in source).
- [22.13.E2](https://dlmf.nist.gov/22.13.E2): [`DLMF.JacobiElliptic.deriv_jacobiCnk_sq`](DLMF/JacobiElliptic/Derivatives.lean#L706) (proved); [`DLMF.Elliptic.Real.jacobiCnm_deriv_sq`](DLMF/Elliptic/JacobiIdentities.lean#L52) (proved). As E1.
- [22.13.E3](https://dlmf.nist.gov/22.13.E3): [`DLMF.JacobiElliptic.deriv_jacobiDnk_sq`](DLMF/JacobiElliptic/Derivatives.lean#L720) (proved); [`DLMF.Elliptic.Real.jacobiDnm_deriv_sq`](DLMF/Elliptic/JacobiIdentities.lean#L63) (proved). As E1.
- [22.13.E4](https://dlmf.nist.gov/22.13.E4): [`DLMF.JacobiElliptic.deriv_jacobiCdk_sq`](DLMF/JacobiElliptic/Derivatives.lean#L735) (proved); [`DLMF.JacobiElliptic.Real.deriv_jacobiCdm_sq`](DLMF/JacobiElliptic/Derivatives.lean#L1191) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E5](https://dlmf.nist.gov/22.13.E5): [`DLMF.JacobiElliptic.deriv_jacobiSdk_sq`](DLMF/JacobiElliptic/Derivatives.lean#L750) (proved); [`DLMF.JacobiElliptic.Real.deriv_jacobiSdm_sq`](DLMF/JacobiElliptic/Derivatives.lean#L1205) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E6](https://dlmf.nist.gov/22.13.E6): [`DLMF.JacobiElliptic.deriv_jacobiNdk_sq`](DLMF/JacobiElliptic/Derivatives.lean#L763) (proved); [`DLMF.JacobiElliptic.Real.deriv_jacobiNdm_sq`](DLMF/JacobiElliptic/Derivatives.lean#L1220) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E7](https://dlmf.nist.gov/22.13.E7): [`DLMF.JacobiElliptic.deriv_jacobiDck_sq`](DLMF/JacobiElliptic/Derivatives.lean#L777) (proved); [`DLMF.JacobiElliptic.Real.deriv_jacobiDcm_sq`](DLMF/JacobiElliptic/Derivatives.lean#L1233) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E8](https://dlmf.nist.gov/22.13.E8): [`DLMF.JacobiElliptic.deriv_jacobiNck_sq`](DLMF/JacobiElliptic/Derivatives.lean#L791) (proved); [`DLMF.JacobiElliptic.Real.deriv_jacobiNcm_sq`](DLMF/JacobiElliptic/Derivatives.lean#L1246) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E9](https://dlmf.nist.gov/22.13.E9): [`DLMF.JacobiElliptic.deriv_jacobiSck_sq`](DLMF/JacobiElliptic/Derivatives.lean#L805) (proved); [`DLMF.JacobiElliptic.Real.deriv_jacobiScm_sq`](DLMF/JacobiElliptic/Derivatives.lean#L1258) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E10](https://dlmf.nist.gov/22.13.E10): [`DLMF.JacobiElliptic.deriv_jacobiNsk_sq`](DLMF/JacobiElliptic/Derivatives.lean#L817) (proved); [`DLMF.JacobiElliptic.Real.deriv_jacobiNsm_sq`](DLMF/JacobiElliptic/Derivatives.lean#L1271) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E11](https://dlmf.nist.gov/22.13.E11): [`DLMF.JacobiElliptic.deriv_jacobiDsk_sq`](DLMF/JacobiElliptic/Derivatives.lean#L830) (proved); [`DLMF.JacobiElliptic.Real.deriv_jacobiDsm_sq`](DLMF/JacobiElliptic/Derivatives.lean#L1282) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E12](https://dlmf.nist.gov/22.13.E12): [`DLMF.JacobiElliptic.deriv_jacobiCsk_sq`](DLMF/JacobiElliptic/Derivatives.lean#L843) (proved); [`DLMF.JacobiElliptic.Real.deriv_jacobiCsm_sq`](DLMF/JacobiElliptic/Derivatives.lean#L1296) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E13](https://dlmf.nist.gov/22.13.E13): [`DLMF.JacobiElliptic.iteratedDeriv_two_jacobiSnk`](DLMF/JacobiElliptic/Derivatives.lean#L857) (proved); [`DLMF.Elliptic.Real.iteratedDeriv_two_jacobiSnm`](DLMF/Elliptic/JacobiIdentities.lean#L301) (proved). Complex new statement; real m<1 form pre-existing (untagged).
- [22.13.E14](https://dlmf.nist.gov/22.13.E14): [`DLMF.JacobiElliptic.iteratedDeriv_two_jacobiCnk`](DLMF/JacobiElliptic/Derivatives.lean#L875) (proved); [`DLMF.Elliptic.Real.iteratedDeriv_two_jacobiCnm`](DLMF/Elliptic/JacobiIdentities.lean#L316) (proved). As E13.
- [22.13.E15](https://dlmf.nist.gov/22.13.E15): [`DLMF.JacobiElliptic.iteratedDeriv_two_jacobiDnk`](DLMF/JacobiElliptic/Derivatives.lean#L894) (proved); [`DLMF.Elliptic.Real.iteratedDeriv_two_jacobiDnm`](DLMF/Elliptic/JacobiIdentities.lean#L331) (proved). As E13.
- [22.13.E16](https://dlmf.nist.gov/22.13.E16): [`DLMF.JacobiElliptic.iteratedDeriv_two_jacobiCdk`](DLMF/JacobiElliptic/Derivatives.lean#L914) (proved); [`DLMF.JacobiElliptic.Real.iteratedDeriv_two_jacobiCdm`](DLMF/JacobiElliptic/Derivatives.lean#L1311) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E17](https://dlmf.nist.gov/22.13.E17): [`DLMF.JacobiElliptic.iteratedDeriv_two_jacobiSdk`](DLMF/JacobiElliptic/Derivatives.lean#L933) (proved); [`DLMF.JacobiElliptic.Real.iteratedDeriv_two_jacobiSdm`](DLMF/JacobiElliptic/Derivatives.lean#L1331) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E18](https://dlmf.nist.gov/22.13.E18): [`DLMF.JacobiElliptic.iteratedDeriv_two_jacobiNdk`](DLMF/JacobiElliptic/Derivatives.lean#L952) (proved); [`DLMF.JacobiElliptic.Real.iteratedDeriv_two_jacobiNdm`](DLMF/JacobiElliptic/Derivatives.lean#L1351) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E19](https://dlmf.nist.gov/22.13.E19): [`DLMF.JacobiElliptic.iteratedDeriv_two_jacobiDck`](DLMF/JacobiElliptic/Derivatives.lean#L972) (proved); [`DLMF.JacobiElliptic.Real.iteratedDeriv_two_jacobiDcm`](DLMF/JacobiElliptic/Derivatives.lean#L1368) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E20](https://dlmf.nist.gov/22.13.E20): [`DLMF.JacobiElliptic.iteratedDeriv_two_jacobiNck`](DLMF/JacobiElliptic/Derivatives.lean#L991) (proved); [`DLMF.JacobiElliptic.Real.iteratedDeriv_two_jacobiNcm`](DLMF/JacobiElliptic/Derivatives.lean#L1389) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E21](https://dlmf.nist.gov/22.13.E21): [`DLMF.JacobiElliptic.iteratedDeriv_two_jacobiSck`](DLMF/JacobiElliptic/Derivatives.lean#L1010) (proved); [`DLMF.JacobiElliptic.Real.iteratedDeriv_two_jacobiScm`](DLMF/JacobiElliptic/Derivatives.lean#L1408) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E22](https://dlmf.nist.gov/22.13.E22): [`DLMF.JacobiElliptic.iteratedDeriv_two_jacobiNsk`](DLMF/JacobiElliptic/Derivatives.lean#L1028) (proved); [`DLMF.JacobiElliptic.Real.iteratedDeriv_two_jacobiNsm`](DLMF/JacobiElliptic/Derivatives.lean#L1430) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E23](https://dlmf.nist.gov/22.13.E23): [`DLMF.JacobiElliptic.iteratedDeriv_two_jacobiDsk`](DLMF/JacobiElliptic/Derivatives.lean#L1045) (proved); [`DLMF.JacobiElliptic.Real.iteratedDeriv_two_jacobiDsm`](DLMF/JacobiElliptic/Derivatives.lean#L1449) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.E24](https://dlmf.nist.gov/22.13.E24): [`DLMF.JacobiElliptic.iteratedDeriv_two_jacobiCsk`](DLMF/JacobiElliptic/Derivatives.lean#L1062) (proved); [`DLMF.JacobiElliptic.Real.iteratedDeriv_two_jacobiCsm`](DLMF/JacobiElliptic/Derivatives.lean#L1470) (proved). Domain: k ∈ jacobiModulusDomain, z not a pole.
- [22.13.T1](https://dlmf.nist.gov/22.13.T1): [`DLMF.JacobiElliptic.hasDerivAt_jacobiSnk`](DLMF/JacobiElliptic/Derivatives.lean#L419) (proved); [`DLMF.JacobiElliptic.hasDerivAt_jacobiCnk`](DLMF/JacobiElliptic/Derivatives.lean#L442) (proved); [`DLMF.JacobiElliptic.hasDerivAt_jacobiDnk`](DLMF/JacobiElliptic/Derivatives.lean#L464) (proved); [`DLMF.JacobiElliptic.hasDerivAt_jacobiCdk`](DLMF/JacobiElliptic/Derivatives.lean#L486) (proved); [`DLMF.JacobiElliptic.hasDerivAt_jacobiSdk`](DLMF/JacobiElliptic/Derivatives.lean#L511) (proved); [`DLMF.JacobiElliptic.hasDerivAt_jacobiNdk`](DLMF/JacobiElliptic/Derivatives.lean#L533) (proved); [`DLMF.JacobiElliptic.hasDerivAt_jacobiDck`](DLMF/JacobiElliptic/Derivatives.lean#L555) (proved); [`DLMF.JacobiElliptic.hasDerivAt_jacobiNck`](DLMF/JacobiElliptic/Derivatives.lean#L580) (proved); [`DLMF.JacobiElliptic.hasDerivAt_jacobiSck`](DLMF/JacobiElliptic/Derivatives.lean#L602) (proved); [`DLMF.JacobiElliptic.hasDerivAt_jacobiNsk`](DLMF/JacobiElliptic/Derivatives.lean#L624) (proved); [`DLMF.JacobiElliptic.hasDerivAt_jacobiDsk`](DLMF/JacobiElliptic/Derivatives.lean#L647) (proved); [`DLMF.JacobiElliptic.hasDerivAt_jacobiCsk`](DLMF/JacobiElliptic/Derivatives.lean#L669) (proved); [`DLMF.JacobiElliptic.Real.hasDerivAt_jacobiSdm`](DLMF/JacobiElliptic/Derivatives.lean#L1095) (proved); [`DLMF.JacobiElliptic.Real.hasDerivAt_jacobiCdm`](DLMF/JacobiElliptic/Derivatives.lean#L1107) (proved); [`DLMF.JacobiElliptic.Real.hasDerivAt_jacobiNdm`](DLMF/JacobiElliptic/Derivatives.lean#L1118) (proved); [`DLMF.JacobiElliptic.Real.hasDerivAt_jacobiDcm`](DLMF/JacobiElliptic/Derivatives.lean#L1129) (proved); [`DLMF.JacobiElliptic.Real.hasDerivAt_jacobiNcm`](DLMF/JacobiElliptic/Derivatives.lean#L1139) (proved); [`DLMF.JacobiElliptic.Real.hasDerivAt_jacobiScm`](DLMF/JacobiElliptic/Derivatives.lean#L1148) (proved); [`DLMF.JacobiElliptic.Real.hasDerivAt_jacobiNsm`](DLMF/JacobiElliptic/Derivatives.lean#L1158) (proved); [`DLMF.JacobiElliptic.Real.hasDerivAt_jacobiDsm`](DLMF/JacobiElliptic/Derivatives.lean#L1168) (proved); [`DLMF.JacobiElliptic.Real.hasDerivAt_jacobiCsm`](DLMF/JacobiElliptic/Derivatives.lean#L1178) (proved); [`DLMF.Elliptic.Real.hasDerivAt_jacobiSnm`](DLMF/Elliptic/Jacobi.lean#L246) (proved); [`DLMF.Elliptic.Real.hasDerivAt_jacobiCnm`](DLMF/Elliptic/Jacobi.lean#L252) (proved); [`DLMF.Elliptic.Real.hasDerivAt_jacobiDnm`](DLMF/Elliptic/Jacobi.lean#L259) (proved). Complex: k ∈ jacobiModulusDomain and theta denominator nonzero. Real m<1: nine quotients proved here; sn, cn, dn pre-existing (tagged there 22.13.E1–E3, which is a mis-tag for T1).

## [§22.14 Integrals](https://dlmf.nist.gov/22.14)

- [22.14.E1](https://dlmf.nist.gov/22.14.E1): [`DLMF.JacobiElliptic.Real.hasDerivAt_primitive_jacobiSn`](DLMF/JacobiElliptic/Integrals.lean#L86) (proved). Special case: real x, 0 < k < 1.
- [22.14.E2](https://dlmf.nist.gov/22.14.E2): [`DLMF.JacobiElliptic.Real.hasDerivAt_primitive_jacobiCn`](DLMF/JacobiElliptic/Integrals.lean#L103) (proved). Principal arccos form valid on 0<x<2K; DLMF Arccos is multivalued, not an erratum.
- [22.14.E3](https://dlmf.nist.gov/22.14.E3): [`DLMF.JacobiElliptic.Real.hasDerivAt_arcsin_jacobiSnm`](DLMF/JacobiElliptic/Integrals.lean#L126) (proved). For |x| < K.
- [22.14.E4](https://dlmf.nist.gov/22.14.E4): [`DLMF.JacobiElliptic.Real.hasDerivAt_primitive_jacobiCd`](DLMF/JacobiElliptic/Integrals.lean#L145) (proved). Special case: real x, 0 < k < 1.
- [22.14.E5](https://dlmf.nist.gov/22.14.E5): [`DLMF.JacobiElliptic.Real.hasDerivAt_primitive_jacobiSd`](DLMF/JacobiElliptic/Integrals.lean#L167) (proved). Special case: real x, 0 < k < 1, principal arcsin.
- [22.14.E6](https://dlmf.nist.gov/22.14.E6): [`DLMF.JacobiElliptic.Real.hasDerivAt_primitive_jacobiNd`](DLMF/JacobiElliptic/Integrals.lean#L202) (proved). As E2: principal branch on 0<x<2K.
- [22.14.E7](https://dlmf.nist.gov/22.14.E7): [`DLMF.JacobiElliptic.Real.hasDerivAt_primitive_jacobiDc`](DLMF/JacobiElliptic/Integrals.lean#L241) (proved). Special case: real x, 0 < k < 1.
- [22.14.E8](https://dlmf.nist.gov/22.14.E8): [`DLMF.JacobiElliptic.Real.hasDerivAt_primitive_jacobiNc`](DLMF/JacobiElliptic/Integrals.lean#L262) (proved). Special case: real x, 0 < k < 1.
- [22.14.E9](https://dlmf.nist.gov/22.14.E9): [`DLMF.JacobiElliptic.Real.hasDerivAt_primitive_jacobiSc`](DLMF/JacobiElliptic/Integrals.lean#L293) (proved). Special case: real x, 0 < k < 1.
- [22.14.E10](https://dlmf.nist.gov/22.14.E10): [`DLMF.JacobiElliptic.Real.hasDerivAt_primitive_jacobiNs`](DLMF/JacobiElliptic/Integrals.lean#L316) (proved). Special case: real x, 0 < k < 1.
- [22.14.E11](https://dlmf.nist.gov/22.14.E11): [`DLMF.JacobiElliptic.Real.hasDerivAt_primitive_jacobiDs`](DLMF/JacobiElliptic/Integrals.lean#L345) (proved). Special case: real x, 0 < k < 1.
- [22.14.E12](https://dlmf.nist.gov/22.14.E12): [`DLMF.JacobiElliptic.Real.hasDerivAt_primitive_jacobiCs`](DLMF/JacobiElliptic/Integrals.lean#L366) (proved). Special case: real x, 0 < k < 1.
- [22.14.E13](https://dlmf.nist.gov/22.14.E13): [`DLMF.JacobiElliptic.Real.hasDerivAt_primitive_inv_jacobiSn`](DLMF/JacobiElliptic/Integrals.lean#L398) (proved). Special case: real x, 0 < k < 1.
- [22.14.E14](https://dlmf.nist.gov/22.14.E14): [`DLMF.JacobiElliptic.Real.hasDerivAt_primitive_jacobiCn_div_jacobiSn`](DLMF/JacobiElliptic/Integrals.lean#L425) (proved). Special case: real x, 0 < k < 1.
- [22.14.E15](https://dlmf.nist.gov/22.14.E15): [`DLMF.JacobiElliptic.Real.hasDerivAt_primitive_jacobiCn_div_jacobiSn_sq`](DLMF/JacobiElliptic/Integrals.lean#L450) (proved). Special case: real x, 0 < k < 1.
- [22.14.E16](https://dlmf.nist.gov/22.14.E16): [`DLMF.JacobiElliptic.Real.integral_log_jacobiSnm`](DLMF/JacobiElliptic/Integrals.lean#L472) (admitted). Definite log integral, real 0<k<1.
- [22.14.E17](https://dlmf.nist.gov/22.14.E17): [`DLMF.JacobiElliptic.Real.integral_log_jacobiCnm`](DLMF/JacobiElliptic/Integrals.lean#L481) (admitted). As E16.
- [22.14.E18](https://dlmf.nist.gov/22.14.E18): [`DLMF.JacobiElliptic.Real.integral_log_jacobiDnm`](DLMF/JacobiElliptic/Integrals.lean#L490) (admitted). As E16.

## [§22.15 Inverse Functions](https://dlmf.nist.gov/22.15)

- [22.15.E1](https://dlmf.nist.gov/22.15.E1): [`DLMF.Elliptic.Real.jacobiSnm_jacobiArcsnm`](DLMF/Elliptic/SpecialValues.lean#L88) (proved). Pre-existing (untagged).
- [22.15.E2](https://dlmf.nist.gov/22.15.E2): [`DLMF.JacobiElliptic.Real.jacobiCnm_jacobiArccnm`](DLMF/JacobiElliptic/Inverse.lean#L98) (proved). Special case: real parameter m = k² < 1.
- [22.15.E3](https://dlmf.nist.gov/22.15.E3): [`DLMF.JacobiElliptic.Real.jacobiDnm_jacobiArcdnm`](DLMF/JacobiElliptic/Inverse.lean#L104) (proved). Special case: real parameter 0 < m = k² < 1.
- [22.15.E4](https://dlmf.nist.gov/22.15.E4): [`DLMF.JacobiElliptic.Real.jacobiArccnm`](DLMF/JacobiElliptic/Inverse.lean#L42) (definition); [`DLMF.JacobiElliptic.Real.jacobiArcdnm`](DLMF/JacobiElliptic/Inverse.lean#L47) (definition); [`DLMF.Elliptic.Real.jacobiArcsnm`](DLMF/Elliptic/SpecialValues.lean#L84) (definition). arccn and arcdn defined here; arcsn pre-existing.
- [22.15.E5](https://dlmf.nist.gov/22.15.E5): [`DLMF.JacobiElliptic.Real.jacobiArcsnm_mem_Icc`](DLMF/JacobiElliptic/Inverse.lean#L121) (proved). Special case: real parameter m = k² < 1.
- [22.15.E6](https://dlmf.nist.gov/22.15.E6): [`DLMF.JacobiElliptic.Real.jacobiArccnm_mem_Icc`](DLMF/JacobiElliptic/Inverse.lean#L136) (proved). Special case: real parameter m = k² < 1.
- [22.15.E7](https://dlmf.nist.gov/22.15.E7): [`DLMF.JacobiElliptic.Real.jacobiArcdnm_mem_Icc`](DLMF/JacobiElliptic/Inverse.lean#L151) (proved). Special case: real parameter m = k² < 1.
- [22.15.E8](https://dlmf.nist.gov/22.15.E8): [`DLMF.JacobiElliptic.Real.jacobiSnm_eq_iff`](DLMF/JacobiElliptic/Inverse.lean#L202) (proved). Special case: real parameter k² < 1.
- [22.15.E9](https://dlmf.nist.gov/22.15.E9): [`DLMF.JacobiElliptic.Real.jacobiCnm_eq_iff`](DLMF/JacobiElliptic/Inverse.lean#L214) (proved). Special case: real parameter k² < 1.
- [22.15.E10](https://dlmf.nist.gov/22.15.E10): [`DLMF.JacobiElliptic.Real.jacobiDnm_eq_iff`](DLMF/JacobiElliptic/Inverse.lean#L246) (proved). Special case: real parameter 0 < k² < 1.
- [22.15.E11](https://dlmf.nist.gov/22.15.E11): [`DLMF.JacobiElliptic.Real.eq_integral_jacobiSnm`](DLMF/JacobiElliptic/Inverse.lean#L336) (proved). Stronger than DLMF: |x| ≤ K.
- [22.15.E12](https://dlmf.nist.gov/22.15.E12): [`DLMF.JacobiElliptic.Real.jacobiArcsnm_eq_integral`](DLMF/JacobiElliptic/Inverse.lean#L320) (proved). Special case: real parameter m = k² < 1.
- [22.15.E13](https://dlmf.nist.gov/22.15.E13): [`DLMF.JacobiElliptic.Real.jacobiArccnm_eq_integral`](DLMF/JacobiElliptic/Inverse.lean#L361) (proved). Special case: real parameter m = k² < 1.
- [22.15.E14](https://dlmf.nist.gov/22.15.E14): [`DLMF.JacobiElliptic.Real.jacobiArcdnm_eq_integral`](DLMF/JacobiElliptic/Inverse.lean#L383) (proved). Special case: real parameter 0 < m = k² < 1.
- [22.15.E15](https://dlmf.nist.gov/22.15.E15): [`DLMF.JacobiElliptic.Real.jacobiArccdm`](DLMF/JacobiElliptic/Inverse.lean#L52) (definition); [`DLMF.JacobiElliptic.Real.jacobiCdm_jacobiArccdm`](DLMF/JacobiElliptic/Inverse.lean#L462) (proved). Special case: real parameter m = k² < 1.
- [22.15.E16](https://dlmf.nist.gov/22.15.E16): [`DLMF.JacobiElliptic.Real.jacobiArcsdm`](DLMF/JacobiElliptic/Inverse.lean#L56) (definition); [`DLMF.JacobiElliptic.Real.jacobiSdm_jacobiArcsdm`](DLMF/JacobiElliptic/Inverse.lean#L495) (proved). Special case: real parameter m = k² < 1.
- [22.15.E17](https://dlmf.nist.gov/22.15.E17): [`DLMF.JacobiElliptic.Real.jacobiArcndm`](DLMF/JacobiElliptic/Inverse.lean#L61) (definition); [`DLMF.JacobiElliptic.Real.jacobiNdm_jacobiArcndm`](DLMF/JacobiElliptic/Inverse.lean#L578) (proved). Special case: real parameter m = k² < 1.
- [22.15.E18](https://dlmf.nist.gov/22.15.E18): [`DLMF.JacobiElliptic.Real.jacobiArcdcm`](DLMF/JacobiElliptic/Inverse.lean#L66) (definition); [`DLMF.JacobiElliptic.Real.jacobiDcm_jacobiArcdcm`](DLMF/JacobiElliptic/Inverse.lean#L619) (proved). Special case: real parameter 0 ≤ m = k² < 1.
- [22.15.E19](https://dlmf.nist.gov/22.15.E19): [`DLMF.JacobiElliptic.Real.jacobiArcncm`](DLMF/JacobiElliptic/Inverse.lean#L70) (definition); [`DLMF.JacobiElliptic.Real.jacobiNcm_jacobiArcncm`](DLMF/JacobiElliptic/Inverse.lean#L644) (proved). Special case: real parameter 0 ≤ m = k² < 1.
- [22.15.E20](https://dlmf.nist.gov/22.15.E20): [`DLMF.JacobiElliptic.Real.jacobiArcscm`](DLMF/JacobiElliptic/Inverse.lean#L75) (definition); [`DLMF.JacobiElliptic.Real.jacobiScm_jacobiArcscm`](DLMF/JacobiElliptic/Inverse.lean#L755) (proved). Special case: real parameter 0 ≤ m = k² < 1.
- [22.15.E21](https://dlmf.nist.gov/22.15.E21): [`DLMF.JacobiElliptic.Real.jacobiArcnsm`](DLMF/JacobiElliptic/Inverse.lean#L80) (definition); [`DLMF.JacobiElliptic.Real.jacobiNsm_jacobiArcnsm`](DLMF/JacobiElliptic/Inverse.lean#L698) (proved). Special case: real parameter 0 ≤ m = k² < 1.
- [22.15.E22](https://dlmf.nist.gov/22.15.E22): [`DLMF.JacobiElliptic.Real.jacobiArcdsm`](DLMF/JacobiElliptic/Inverse.lean#L84) (definition); [`DLMF.JacobiElliptic.Real.jacobiDsm_jacobiArcdsm`](DLMF/JacobiElliptic/Inverse.lean#L721) (proved). Special case: real parameter 0 < m = k² < 1.
- [22.15.E23](https://dlmf.nist.gov/22.15.E23): [`DLMF.JacobiElliptic.Real.jacobiArccsm`](DLMF/JacobiElliptic/Inverse.lean#L88) (definition); [`DLMF.JacobiElliptic.Real.jacobiCsm_jacobiArccsm`](DLMF/JacobiElliptic/Inverse.lean#L787) (proved). Special case: real parameter 0 ≤ m = k² < 1.

## [§22.16 Related Functions](https://dlmf.nist.gov/22.16)

- [22.16.E1](https://dlmf.nist.gov/22.16.E1): [`DLMF.JacobiElliptic.Real.jacobiAmm_eq_arcsin_jacobiSnm`](DLMF/JacobiElliptic/Related.lean#L63) (proved). Special case: real parameter m = k² < 1; principal branch on -K ≤ x ≤ K.
- [22.16.E2](https://dlmf.nist.gov/22.16.E2): [`DLMF.Elliptic.Real.jacobiAmm_add_two_compEllIntKm`](DLMF/Elliptic/Jacobi.lean#L200) (proved). Pre-existing (untagged).
- [22.16.E3](https://dlmf.nist.gov/22.16.E3): [`DLMF.JacobiElliptic.Real.jacobiAmm_eq_integral_jacobiDnm`](DLMF/JacobiElliptic/Related.lean#L94) (proved). Special case: real parameter m = k² < 1.
- [22.16.E4](https://dlmf.nist.gov/22.16.E4): [`DLMF.Elliptic.Real.jacobiAmm_zero_param`](DLMF/Elliptic/Jacobi.lean#L213) (proved). Pre-existing (untagged).
- [22.16.E5](https://dlmf.nist.gov/22.16.E5): [`DLMF.JacobiElliptic.Real.tendsto_jacobiAmm_one`](DLMF/JacobiElliptic/Related.lean#L103) (admitted). Stated as limit k→1⁻: `Real.jacobiAmm` is totalized (am=x) at m≥1.
- [22.16.E6](https://dlmf.nist.gov/22.16.E6): [`DLMF.JacobiElliptic.Real.jacobiAmm_isBigO_maclaurin`](DLMF/JacobiElliptic/Related.lean#L111) (admitted). Special case: real x, real parameter m = k² < 1.
- [22.16.E7](https://dlmf.nist.gov/22.16.E7): [`DLMF.JacobiElliptic.Real.jacobiAmm_isBigO_small_modulus`](DLMF/JacobiElliptic/Related.lean#L119) (admitted). Special case: real x, real k → 0.
- [22.16.E8](https://dlmf.nist.gov/22.16.E8): [`DLMF.JacobiElliptic.Real.jacobiAmm_isBigO_small_comodulus`](DLMF/JacobiElliptic/Related.lean#L127) (admitted). Special case: real x, real k → 1⁻.
- [22.16.E9](https://dlmf.nist.gov/22.16.E9): [`DLMF.JacobiElliptic.Real.jacobiAmm_hasSum_fourier`](DLMF/JacobiElliptic/Related.lean#L136) (admitted). Special case: real x, 0 < k < 1.
- [22.16.E10](https://dlmf.nist.gov/22.16.E10): [`DLMF.JacobiElliptic.Real.eq_incEllIntFm_iff_jacobiAmm_eq`](DLMF/JacobiElliptic/Related.lean#L149) (proved). Stronger than DLMF: all real x and φ.
- [22.16.E11](https://dlmf.nist.gov/22.16.E11): [`DLMF.Elliptic.Real.jacobiAmm`](DLMF/Elliptic/Jacobi.lean#L159) (definition); [`DLMF.Elliptic.Real.incEllIntFm_jacobiAmm`](DLMF/Elliptic/Jacobi.lean#L161) (proved). Pre-existing definition of am as inverse of F(·,m) (untagged).
- [22.16.E12](https://dlmf.nist.gov/22.16.E12): [`DLMF.JacobiElliptic.Real.jacobiAmm_eq_iff_jacobiSnm_eq_sin`](DLMF/JacobiElliptic/Related.lean#L158) (proved). Special case: -π/2 ≤ φ ≤ π/2 made explicit.
- [22.16.E13](https://dlmf.nist.gov/22.16.E13): [`DLMF.JacobiElliptic.Real.jacobiAmm_eq_iff_jacobiCnm_eq_cos`](DLMF/JacobiElliptic/Related.lean#L170) (proved). Converse direction needs 0≤x and 0≤φ (cos is even).
- [22.16.E14](https://dlmf.nist.gov/22.16.E14): [`DLMF.JacobiElliptic.Real.jacobiEpsilonk_eq_integral_sn`](DLMF/JacobiElliptic/Related.lean#L247) (proved). Corrected form (DLMF 2010-07-08, Karney) used.
- [22.16.E15](https://dlmf.nist.gov/22.16.E15): [`DLMF.JacobiElliptic.Real.jacobiEpsilonk_eq_integral_jacobiSnm_sq`](DLMF/JacobiElliptic/Related.lean#L284) (proved). Special case: real modulus with k² < 1.
- [22.16.E16](https://dlmf.nist.gov/22.16.E16): [`DLMF.JacobiElliptic.Real.jacobiEpsilonk_eq_integral_jacobiCnm_sq`](DLMF/JacobiElliptic/Related.lean#L299) (proved). Special case: real modulus with k² < 1.
- [22.16.E17](https://dlmf.nist.gov/22.16.E17): [`DLMF.JacobiElliptic.Real.jacobiEpsilonk`](DLMF/JacobiElliptic/Related.lean#L189) (definition).
- [22.16.E18](https://dlmf.nist.gov/22.16.E18): [`DLMF.JacobiElliptic.Real.jacobiEpsilonk_eq_integral_cd_sq`](DLMF/JacobiElliptic/Related.lean#L354) (proved). Special case: real modulus 0 < k < 1.
- [22.16.E19](https://dlmf.nist.gov/22.16.E19): [`DLMF.JacobiElliptic.Real.jacobiEpsilonk_eq_integral_sd_sq`](DLMF/JacobiElliptic/Related.lean#L396) (proved). Special case: real modulus 0 < k < 1.
- [22.16.E20](https://dlmf.nist.gov/22.16.E20): [`DLMF.JacobiElliptic.Real.jacobiEpsilonk_eq_integral_nd_sq`](DLMF/JacobiElliptic/Related.lean#L440) (proved). Special case: real modulus 0 < k < 1.
- [22.16.E21](https://dlmf.nist.gov/22.16.E21): [`DLMF.JacobiElliptic.Real.jacobiEpsilonk_eq_integral_dc_sq`](DLMF/JacobiElliptic/Related.lean#L483) (proved). Special case: real modulus 0 < k < 1.
- [22.16.E22](https://dlmf.nist.gov/22.16.E22): [`DLMF.JacobiElliptic.Real.jacobiEpsilonk_eq_integral_nc_sq`](DLMF/JacobiElliptic/Related.lean#L535) (proved). Special case: real modulus 0 < k < 1.
- [22.16.E23](https://dlmf.nist.gov/22.16.E23): [`DLMF.JacobiElliptic.Real.jacobiEpsilonk_eq_integral_sc_sq`](DLMF/JacobiElliptic/Related.lean#L587) (proved). Special case: real modulus 0 < k < 1.
- [22.16.E24](https://dlmf.nist.gov/22.16.E24): [`DLMF.JacobiElliptic.Real.jacobiEpsilonk_eq_integral_ns_sq`](DLMF/JacobiElliptic/Related.lean#L640) (admitted). Special case: real modulus 0 < k < 1, x ≠ 0.
- [22.16.E25](https://dlmf.nist.gov/22.16.E25): [`DLMF.JacobiElliptic.Real.jacobiEpsilonk_eq_integral_ds_sq`](DLMF/JacobiElliptic/Related.lean#L650) (admitted). Special case: real modulus 0 < k < 1, x ≠ 0.
- [22.16.E26](https://dlmf.nist.gov/22.16.E26): [`DLMF.JacobiElliptic.Real.jacobiEpsilonk_eq_integral_cs_sq`](DLMF/JacobiElliptic/Related.lean#L662) (admitted). Special case: real modulus 0 < k < 1, x ≠ 0.
- [22.16.E27](https://dlmf.nist.gov/22.16.E27): [`DLMF.JacobiElliptic.Real.jacobiEpsilonk_add`](DLMF/JacobiElliptic/Related.lean#L673) (proved). Special case: real modulus with k² < 1.
- [22.16.E28](https://dlmf.nist.gov/22.16.E28): [`DLMF.JacobiElliptic.Real.jacobiEpsilonk_add_compEllIntKm`](DLMF/JacobiElliptic/Related.lean#L717) (proved). Special case: real modulus with k² < 1.
- [22.16.E29](https://dlmf.nist.gov/22.16.E29): [`DLMF.JacobiElliptic.Real.jacobiEpsilonk_add_two_compEllIntKm`](DLMF/JacobiElliptic/Related.lean#L315) (proved). Special case: real modulus with k² < 1.
- [22.16.E30](https://dlmf.nist.gov/22.16.E30): [`DLMF.JacobiElliptic.Real.jacobiEpsilonk_eq_theta`](DLMF/JacobiElliptic/Related.lean#L729) (admitted). Special case: real x, 0 < k < 1.
- [22.16.E31](https://dlmf.nist.gov/22.16.E31): [`DLMF.JacobiElliptic.Real.incEllIntEm_jacobiAmm`](DLMF/JacobiElliptic/Related.lean#L215) (proved). Stronger than DLMF: all real x.
- [22.16.E32](https://dlmf.nist.gov/22.16.E32): [`DLMF.JacobiElliptic.Real.jacobiZetaFunctionk`](DLMF/JacobiElliptic/Related.lean#L195) (definition). Named `jacobiZetaFunctionk` to avoid confusion with the theta argument `jacobiZetak`.
- [22.16.E33](https://dlmf.nist.gov/22.16.E33): [`DLMF.JacobiElliptic.Real.jacobiZetaFunctionk_add_compEllIntKm`](DLMF/JacobiElliptic/Related.lean#L761) (proved). Proof depends on admitted 22.16.E28.
- [22.16.E34](https://dlmf.nist.gov/22.16.E34): [`DLMF.JacobiElliptic.Real.jacobiZetaFunctionk_add_two_compEllIntKm`](DLMF/JacobiElliptic/Related.lean#L771) (proved). Special case: real modulus with k² < 1.
- [22.16.i](https://dlmf.nist.gov/22.16#i): [`DLMF.JacobiElliptic.Real.contDiff_jacobiAmm`](DLMF/JacobiElliptic/Related.lean#L72) (proved); [`DLMF.Elliptic.Real.continuous_jacobiAmm`](DLMF/Elliptic/Jacobi.lean#L175) (proved); [`DLMF.Elliptic.Real.hasDerivAt_jacobiAmm`](DLMF/Elliptic/Jacobi.lean#L179) (proved). Smoothness ContDiff ℝ ⊤ of am in x proved; existing continuity and derivative pre-existing (untagged).
- [22.16.iii](https://dlmf.nist.gov/22.16#iii): [`DLMF.JacobiElliptic.Real.jacobiZetaFunctionk_add`](DLMF/JacobiElliptic/Related.lean#L750) (proved). Quasi-addition for Z; proof depends on admitted 22.16.E27.

## [§22.17 Moduli Outside the Interval [0,1]](https://dlmf.nist.gov/22.17)

- [22.17.E1](https://dlmf.nist.gov/22.17.E1): [`DLMF.JacobiElliptic.jacobiPQk_neg_modulus`](DLMF/JacobiElliptic/OutsideModuli.lean#L37) (proved). Stronger than DLMF: all complex z and k.
- [22.17.E2](https://dlmf.nist.gov/22.17.E2): [`DLMF.JacobiElliptic.jacobiSnk_inv`](DLMF/JacobiElliptic/OutsideModuli.lean#L80) (proved). k, 1/k ∈ jacobiModulusDomain; real 1/k>1 lies on the definition cut.
- [22.17.E3](https://dlmf.nist.gov/22.17.E3): [`DLMF.JacobiElliptic.jacobiCnk_inv`](DLMF/JacobiElliptic/OutsideModuli.lean#L87) (proved). As E2.
- [22.17.E4](https://dlmf.nist.gov/22.17.E4): [`DLMF.JacobiElliptic.jacobiDnk_inv`](DLMF/JacobiElliptic/OutsideModuli.lean#L93) (proved). As E2.
- [22.17.E5](https://dlmf.nist.gov/22.17.E5): [`DLMF.JacobiElliptic.mul_sqrt_one_sub_sq_imagModulus`](DLMF/JacobiElliptic/OutsideModuli.lean#L99) (proved); [`DLMF.JacobiElliptic.jacobiImagModulusk`](DLMF/JacobiElliptic/OutsideModuli.lean#L114) (definition). Real identity proved; complex k₁ defined with principal root.
- [22.17.E6](https://dlmf.nist.gov/22.17.E6): [`DLMF.JacobiElliptic.jacobiSnk_I_mul`](DLMF/JacobiElliptic/OutsideModuli.lean#L181) (proved). ik, k₁ ∈ jacobiModulusDomain.
- [22.17.E7](https://dlmf.nist.gov/22.17.E7): [`DLMF.JacobiElliptic.jacobiCnk_I_mul`](DLMF/JacobiElliptic/OutsideModuli.lean#L190) (proved). As E6.
- [22.17.E8](https://dlmf.nist.gov/22.17.E8): [`DLMF.JacobiElliptic.jacobiDnk_I_mul`](DLMF/JacobiElliptic/OutsideModuli.lean#L198) (proved). As E6.

## Analytical prose and exclusions (part B)

- [22.3](https://dlmf.nist.gov/22.3): excluded: graphics (figures only, no equations).
- [22.10.i.p1](https://dlmf.nist.gov/22.10#i.p1): Maclaurin coefficients as polynomials in `k²`; covered by 22.10.E1–E3.
- [22.10.i.p2](https://dlmf.nist.gov/22.10#i.p2): convergence for `|z| < min(K, K')`; `DLMF.JacobiElliptic.jacobi_hasFPowerSeriesOnBall` (tag 22.10.i, admitted, real `0 < k < 1`).
- [22.10.ii.p1](https://dlmf.nist.gov/22.10#ii.p1): expansions in `k` and `k'`; covered by 22.10.E4–E9.
- [22.10.ii.p2](https://dlmf.nist.gov/22.10#ii.p2): radius of convergence in the `k`-plane. Qualitative remark, not formalized.
- [22.10.i](https://dlmf.nist.gov/22.10.i): [`DLMF.JacobiElliptic.jacobi_hasFPowerSeriesOnBall`](DLMF/JacobiElliptic/Maclaurin.lean#L254) (proved).
- [22.11.p1](https://dlmf.nist.gov/22.11#p1)–[p4](https://dlmf.nist.gov/22.11#p4), [p6](https://dlmf.nist.gov/22.11#p6): nome, strip condition and the `q^{n+1/2}` convention. These are built into the hypotheses of 22.11.E1–E14 (`‖q‖ e^{2|Im ζ|} < 1` or `e^{|Im ζ|}`). [p5](https://dlmf.nist.gov/22.11#p5): bibliographic.
- [22.12.p1](https://dlmf.nist.gov/22.12#p1), [p2](https://dlmf.nist.gov/22.12#p2): `τ`, and the order of summation (symmetric partial sums for the doubly infinite tan-type series). Built into 22.12.E2–E13.
- [22.13.i.p1](https://dlmf.nist.gov/22.13#i.p1): copolar remark on Table 22.13.T1. Covered by the T1 entries.
- 22.13.i.p2, ii.p3, iii.p3: Carlson references for derivatives with respect to the modulus. Bibliographic.
- [22.14.i](https://dlmf.nist.gov/22.14#i) p1–p6: ranges of `x` for the primitives. Built into the hypotheses of 22.14.E1–E15. [22.14.ii](https://dlmf.nist.gov/22.14#ii) p1–p2: integrals of powers. References and qualitative remarks only. [22.14.iii.p1](https://dlmf.nist.gov/22.14#iii.p1): definite log integrals E16–E18. [22.14.iv](https://dlmf.nist.gov/22.14#iv) p1–p2: subsidiary integrals by subtraction. Remark only.
- [22.15.i](https://dlmf.nist.gov/22.15#i) p1–p2: principal ranges of arcsn, arccn and arcdn. Covered by 22.15.E5–E7. [22.15.ii](https://dlmf.nist.gov/22.15#ii) p1–p4: normal-form remark and references. Covered by 22.15.E15–E23, otherwise bibliographic.
- [22.16.Px1.p1](https://dlmf.nist.gov/22.16#Px1.p1): smoothness of `am`. `DLMF.JacobiElliptic.Real.contDiff_jacobiAmm` (tag 22.16.i, proved). The other 22.16 prose paragraphs restate the definitions and domains used in 22.16.E1–E34. Quasi-addition for `Z` in [22.16.iii](https://dlmf.nist.gov/22.16#iii): `DLMF.JacobiElliptic.Real.jacobiZetaFunctionk_add` (proved, depends on admitted 22.16.E27).
- [22.16.iv](https://dlmf.nist.gov/22.16#iv): excluded: graphics (figures).
- [22.16.i](https://dlmf.nist.gov/22.16.i): [`DLMF.Elliptic.Real.hasDerivAt_jacobiAmm`](DLMF/Elliptic/Jacobi.lean#L179) (proved); [`DLMF.JacobiElliptic.Real.contDiff_jacobiAmm`](DLMF/JacobiElliptic/Related.lean#L72) (proved).
- [22.16.iii](https://dlmf.nist.gov/22.16.iii): [`DLMF.JacobiElliptic.Real.jacobiZetaFunctionk_add`](DLMF/JacobiElliptic/Related.lean#L750) (proved).
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
  and `Quot.sound`. `Real.jacobiZetaFunctionk_add_compEllIntKm` and
  `Real.jacobiZetaFunctionk_add` inherit `sorryAx` from the admitted 22.16.E28 and E27.
- Numerical validation (mpmath, 2026-10-25) covers every formula of §§22.10–22.17 at
  `k = 0.6`. Complex moduli `0.6+0.3i`, `1.4+0.2i`, `0.3−1.5i` and `2.5+10⁻⁴i` were also
  checked for 22.10–22.12 and 22.17. An apparent mismatch in 22.16.24–26 was traced to
  cancellation in the quadrature; the formulas are correct.
