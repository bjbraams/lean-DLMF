# DLMF Chapter 19 acquisition: Elliptic Integrals

This acquisition covers the definitions, numbered formulas and analytical assertions in prose
of [DLMF Chapter 19](https://dlmf.nist.gov/19), version 1.2.8, checked on 2026-10-25. It was
done in five parts: ACQ19A covers the Legendre-form definitions (whole chapter) and §§19.1,
19.2, 19.4–19.8; ACQ19B–19E cover §§19.9–19.14 and the symmetric integrals §§19.15–19.29 in
their own sections below. The entry point is
[DLMF/EllipticIntegrals.lean](DLMF/EllipticIntegrals.lean).

**Status after proof round 1 (2026-10-25).** The 530 declarations tagged with Chapter 19 IDs are 66 definitions, 269 proved theorems and 195 theorems that still depend on admissions (187 direct admissions in DLMF/EllipticIntegrals; the counts below record the acquisition and earlier states). The per-line statuses in this ledger are regenerated from the compiled dump. See REVIEW.md, "Proof round 1 for Chapters 19–23 (2026-10-25)".

Whole chapter (compiled tag dump and axiom audit, 2026-10-25, after integration): 426 DLMF
IDs (numbered equations, sub-equations and prose items) carry tags on 528 declarations: 66
definitions, 163 proved theorems, and 299 theorems that depend on admissions, of which 281 are
direct admissions in the 26 `DLMF/EllipticIntegrals` modules (the rest are proved from
admitted lemmas). Excluded: §19.3 and §19.17 (graphics), §§19.30–19.35 (applications),
§§19.36–19.39 (computation, tables, approximations, software) and 19.9.E10 (numerical). The
DLMF errata found here were checked by an independent numerical verifier and are collected in
[DLMFErrata.md](DLMFErrata.md), section "Chapter 19". lean-codes' proved Carlson library (a
Lake dependency since 2026-10-25) is reused through bridges, not copied.

Part A: §§19.1, 19.2 and 19.4–19.8 have 100 numbered equations and tagged prose items
(sub-equations such as 19.2.E8_1, 19.5.E4_1 counted separately), all in scope and all
acquired; none is numerical. Part A lives in `Legendre`, `LegendreIdentities`, `Derivatives`,
`Expansions`, `SpecialCases`, `Connection` and `Quadratic` under `DLMF/EllipticIntegrals/`.
These modules contain 130 tagged declarations: 19 definitions, 44 proved theorems (6 of them
proved from admissions) and **67 direct admissions** (`grep -c '\bsorry\b'`: Legendre 0,
LegendreIdentities 11, Derivatives 8, Expansions 12, SpecialCases 15, Connection 10,
Quadratic 11). Twenty-two existing real-variable declarations in `DLMF/Elliptic/*.lean`,
`DLMF/JacobiElliptic/Basic.lean` and `DLMF/Hypergeometric/Identities.lean` already carried
§19.2–19.8 tags (all proved or definitions); part A added the tags 19.8.E4
(`DLMF.Elliptic.agmIntegral_eq_pi_div_two_div_agm`) and 19.8.E12
(`DLMF.Elliptic.Real.compEllIntEm_landen_descending`) in `DLMF/Elliptic/AGM.lean`.

## Domains, conventions and source corrections

- Mathlib and the pinned TauCeti have no elliptic integrals. The only upstream counterpart in
  part A's scope is Gauss's AGM (`NNReal.agmSequences`, `NNReal.agm`), whose pointers for
  19.8.E1 and §19.8(i) are already in `DLMF/Elliptic/MathlibCoverage.lean`; no new
  `dlmf_upstream` file was needed. The proved `lean-codes` Carlson library
  (`Carlson.Elliptic.Standard`, `Carlson.Real.incEllIntFk` …) is reused through bridge
  theorems, not copied.
- Complex arguments. `incEllIntFk φ k`, `incEllIntEk`, `incEllIntDk`, `incEllIntPik φ α² k`
  integrate along the straight path `θ = tφ`, `t ∈ [0, 1]` (`ei19a_segmentIntegral`), with
  principal powers, as DLMF 19.2.4–19.2.7 for complex φ (all square roots principal, §19.1).
  The complete integrals are the values at φ = π/2; `K` is the existing
  `DLMF.JacobiElliptic.compEllIntKk` and `K'(k) = K(k')` the existing `compEllIntKpk` (literal
  principal `k' = (1 - k²)^{1/2}`, `jacobiComodulusk`). Bridges go to the project's real
  `DLMF.Elliptic.Real.incEllIntFm/Em/Pim`, `Real.compEllIntKm/Em` (real φ, `k² = m ≤ 1`, resp.
  `α² < 1`) and to `Carlson.Real.*`.
- Cauchy principal values (19.2.7 with `α² > 1`, Bulirsch's cel/el3 with `p < 0`, 19.2.17 with
  `y < 0`, 19.6.5, 19.8.9): `ei19a_pvSegmentIntegral g f w` is the `limUnder (𝓝[>] 0)` of the
  path integral with `{t : ‖g(tw)‖ < ε}` excised; it equals the ordinary integral whenever `g`
  stays away from 0 (`ei19a_pvSegmentIntegral_eq`). This is a totalized definition (junk value
  if the limit does not exist).
- DLMF 19.2.9 defines the complementary integrals `K'(k)`, `E'(k)` piecewise: `K(k')`,
  `E(k')` for `Re k > 0` (and on the upper imaginary axis), and the printed continuations for
  `Re k < 0`, `Im k ≷ 0`. `cCompEllIntKk`, `cCompEllIntEk` implement exactly these branches
  (proved as `cCompEllIntKk_of_re_pos`, `_of_re_neg_of_im_pos`, `_of_re_neg_of_im_neg`).
  Numerically (mpmath, k = −0.4 ± 0.7i, −1.3 + 0.5i), the definition is continuous across the
  imaginary axis and satisfies Legendre's relation 19.7.1 also for `Re k < 0`; it jumps across
  the negative real axis, as DLMF's cuts imply.
- **Correction (implicit condition), 19.7.2 b, d.** `K(-ik'/k) = kK(k')` and
  `E(-ik'/k) = E(k')/k` hold only for `Re k > 0`; for `Re k < 0` both change sign (mpmath at
  k = −0.4 + 0.7i, −1.3 + 0.5i, −0.3 − 2i, with DLMF's principal K, E, k'). They are acquired
  with the hypothesis `0 < Re k` (`compEllInt_imaginary_comodulus`). For real `0 < k < 1`
  (DLMF's primary case) the printed formulas are correct.
- 19.6.9 `E(φ, 1) = sin φ` holds for real `|φ| ≤ π/2` (in general `E(φ, 1) = ∫₀^φ |cos θ| dθ`);
  the real case is proved with that range, the complex case admitted with `|Re φ| < π/2`.
- Totalization: real-parameter statements carry the hypotheses (`α² ≠ 1`, `α² ≠ k²`,
  `legendrePathOK φ k`, integrability) under which DLMF's integrals are genuine; Lean's
  `x / 0 = 0` is never used to fake an identity.
- Import clash: `DLMF.GeneralizedHypergeometric.Appell` cannot be imported together with
  `lean-codes` (both TauCeti's `CauchyIntegralPolydisc` and `SeveralComplexVariables` declare
  `DifferentiableOn.analyticOnNhd_of_finiteDimensional`), so Appell's `F₁` in 19.5.4 is
  written out as the double `tsum` of `ei19a_appF1Term` (DLMF 16.13.1) instead of reusing
  `DLMF.Hypergeometric.appF1`.
  (Resolved 2026-10-25: lean-codes now uses TauCeti's theorem, so the two can be imported
  together; replacing the inline F₁ by `appF1` is a follow-up.)
- All 100 part-A items were checked numerically with mpmath (scripts in the acquisition
  scratch area): every formula of §§19.2, 19.4–19.8 as stated in Lean agrees to working
  precision at real and complex sample points, except the 19.7.2 sign issue above.

## Numbered formulas and prose items (part A)

## [§19.1 Special Notation](https://dlmf.nist.gov/19.1)

- [19.1.E1](https://dlmf.nist.gov/19.1.E1): [`DLMF.EllipticIntegrals.compEllIntEk`](DLMF/EllipticIntegrals/Legendre.lean#L182) (definition); [`DLMF.EllipticIntegrals.compEllIntPik`](DLMF/EllipticIntegrals/Legendre.lean#L192) (definition). K(k) is the existing `DLMF.JacobiElliptic.compEllIntKk` (tagged 19.2.E8 there; an imported declaration cannot receive a second tag here).
- [19.1.E2](https://dlmf.nist.gov/19.1.E2): [`DLMF.EllipticIntegrals.incEllIntFk`](DLMF/EllipticIntegrals/Legendre.lean#L149) (definition); [`DLMF.EllipticIntegrals.incEllIntEk`](DLMF/EllipticIntegrals/Legendre.lean#L156) (definition); [`DLMF.EllipticIntegrals.incEllIntPik`](DLMF/EllipticIntegrals/Legendre.lean#L170) (definition). D(φ, k) of the prose is `incEllIntDk` (19.2.E6).

## [§19.2 Definitions](https://dlmf.nist.gov/19.2)

- [19.2.E1](https://dlmf.nist.gov/19.2.E1): [`DLMF.EllipticIntegrals.ellipticIntegrand_elliptic_part`](DLMF/EllipticIntegrals/LegendreIdentities.lean#L62) (proved). Stated for a polynomial `s²` of degree 3 or 4 with simple zeros: the integrand splits into a rational part and the elliptic part (19.2.E1/E3 bundled).
- [19.2.E2](https://dlmf.nist.gov/19.2.E2): [`DLMF.EllipticIntegrals.ellipticIntegrand_eq`](DLMF/EllipticIntegrals/LegendreIdentities.lean#L42) (proved).
- [19.2.E3](https://dlmf.nist.gov/19.2.E3): [`DLMF.EllipticIntegrals.ellipticIntegrand_elliptic_part`](DLMF/EllipticIntegrals/LegendreIdentities.lean#L62) (proved).
- [19.2.ii](https://dlmf.nist.gov/19.2.ii): [`DLMF.EllipticIntegrals.compEllIntKk_neg`](DLMF/EllipticIntegrals/LegendreIdentities.lean#L120) (proved); [`DLMF.EllipticIntegrals.compEllIntEk_neg`](DLMF/EllipticIntegrals/LegendreIdentities.lean#L125) (proved); [`DLMF.EllipticIntegrals.differentiableOn_compEllIntKk_compEllIntEk`](DLMF/EllipticIntegrals/LegendreIdentities.lean#L168) (proved); [`DLMF.EllipticIntegrals.differentiableOn_cCompEllIntKk_cCompEllIntEk`](DLMF/EllipticIntegrals/LegendreIdentities.lean#L179) (admitted); [`DLMF.EllipticIntegrals.circular_hyperbolic_alternate`](DLMF/EllipticIntegrals/LegendreIdentities.lean#L244) (proved). 19.2(ii) prose: K, E analytic in the cut plane; K(−k) = K(k), E(−k) = E(k); the alternate circular/hyperbolic forms; analyticity is admitted.
- [19.2.E4](https://dlmf.nist.gov/19.2.E4): [`DLMF.EllipticIntegrals.incEllIntFk`](DLMF/EllipticIntegrals/Legendre.lean#L149) (definition); [`DLMF.Elliptic.Real.incEllIntFm`](DLMF/Elliptic/Jacobi.lean#L30) (definition); [`DLMF.Hypergeometric.compEllIntKkSeries_eq_integral`](DLMF/Hypergeometric/Identities.lean#L2298) (proved). Complex φ, k; straight path `t ↦ tφ`, principal powers. Bridges: `incEllIntFk_eq_ofReal` (real φ, real `k² ≤ 1`, to `Real.incEllIntFm`) and `incEllIntFk_ofReal` (to `Carlson.Real.incEllIntFk`).
- [19.2.E5](https://dlmf.nist.gov/19.2.E5): [`DLMF.EllipticIntegrals.incEllIntEk`](DLMF/EllipticIntegrals/Legendre.lean#L156) (definition); [`DLMF.Elliptic.Real.incEllIntEm`](DLMF/Elliptic/Jacobi.lean#L35) (definition).
- [19.2.E6](https://dlmf.nist.gov/19.2.E6): [`DLMF.EllipticIntegrals.incEllIntDk`](DLMF/EllipticIntegrals/Legendre.lean#L163) (definition); [`DLMF.EllipticIntegrals.incEllIntDk_eq`](DLMF/EllipticIntegrals/LegendreIdentities.lean#L80) (proved); [`DLMF.EllipticIntegrals.incEllIntDk_eq_of_real`](DLMF/EllipticIntegrals/LegendreIdentities.lean#L102) (proved). `incEllIntDk_eq` needs integrability of both integrands along the path (a hypothesis, since the totalized integral is 0 otherwise).
- [19.2.E7](https://dlmf.nist.gov/19.2.E7): [`DLMF.EllipticIntegrals.incEllIntPik`](DLMF/EllipticIntegrals/Legendre.lean#L170) (definition); [`DLMF.Elliptic.Real.incEllIntPim`](DLMF/Elliptic/ThirdKind.lean#L34) (definition). Cauchy principal value: `ei19a_pvSegmentIntegral`, the `limUnder (𝓝[>] 0)` of the integral with `{‖1 - α² sin²(tφ)‖ < ε}` excised; equals the ordinary integral when the integrand has no singularity (`ei19a_pvSegmentIntegral_eq`). Bridge `incEllIntPik_eq_ofReal` to `Real.incEllIntPim` for `α² < 1`.
- [19.2.E8](https://dlmf.nist.gov/19.2.E8): [`DLMF.EllipticIntegrals.compEllIntEk`](DLMF/EllipticIntegrals/Legendre.lean#L182) (definition); [`DLMF.EllipticIntegrals.compEllIntDk`](DLMF/EllipticIntegrals/Legendre.lean#L188) (definition); [`DLMF.EllipticIntegrals.compEllIntPik`](DLMF/EllipticIntegrals/Legendre.lean#L192) (definition); [`DLMF.EllipticIntegrals.compEllIntKk_eq_incEllIntFk`](DLMF/EllipticIntegrals/Legendre.lean#L281) (proved); [`DLMF.EllipticIntegrals.compEllIntDk_eq`](DLMF/EllipticIntegrals/LegendreIdentities.lean#L111) (proved); [`DLMF.Elliptic.Real.compEllIntKm`](DLMF/Elliptic/Complete.lean#L115) (definition); [`DLMF.Elliptic.Real.compEllIntEm`](DLMF/Elliptic/Complete.lean#L120) (definition); [`DLMF.Elliptic.Real.compEllIntKm_eq_integral_algebraic`](DLMF/Elliptic/SpecialValues.lean#L77) (proved); [`DLMF.JacobiElliptic.compEllIntKk`](DLMF/JacobiElliptic/Basic.lean#L129) (definition). `compEllIntKk` (JacobiElliptic) is the principal K; `compEllIntKk_eq_incEllIntFk` proves K = F(π/2, k).
- [19.2.E8_1](https://dlmf.nist.gov/19.2.E8_1): [`DLMF.EllipticIntegrals.cCompEllIntKk`](DLMF/EllipticIntegrals/Legendre.lean#L199) (definition); [`DLMF.EllipticIntegrals.cCompEllIntKk_eq_integral`](DLMF/EllipticIntegrals/LegendreIdentities.lean#L209) (proved). K'(k) is the existing `DLMF.JacobiElliptic.compEllIntKpk` = K(k') with literal principal k'; `cCompEllIntKk` is DLMF's 19.2.9 piecewise K' (see conventions).
- [19.2.E8_2](https://dlmf.nist.gov/19.2.E8_2): [`DLMF.EllipticIntegrals.cCompEllIntEk`](DLMF/EllipticIntegrals/Legendre.lean#L211) (definition); [`DLMF.EllipticIntegrals.cCompEllIntEk_eq_integral`](DLMF/EllipticIntegrals/LegendreIdentities.lean#L218) (proved).
- [19.2.E9](https://dlmf.nist.gov/19.2.E9): [`DLMF.EllipticIntegrals.cCompEllIntKk_of_re_pos`](DLMF/EllipticIntegrals/Legendre.lean#L435) (proved); [`DLMF.EllipticIntegrals.cCompEllIntKk_of_re_neg_of_im_pos`](DLMF/EllipticIntegrals/Legendre.lean#L443) (proved); [`DLMF.EllipticIntegrals.cCompEllIntKk_of_re_neg_of_im_neg`](DLMF/EllipticIntegrals/Legendre.lean#L453) (proved); [`DLMF.JacobiElliptic.compEllIntKpk`](DLMF/JacobiElliptic/Basic.lean#L136) (definition). The three branches of 19.2.9 are proved definitionally from the piecewise definition.
- [19.2.E10](https://dlmf.nist.gov/19.2.E10): [`DLMF.EllipticIntegrals.incEllInt_add_int_mul_pi`](DLMF/EllipticIntegrals/LegendreIdentities.lean#L316) (proved). Real φ and `1 - k² ∈ slitPlane` (so the integrand is π-periodic and smooth on ℝ).
- [19.2.E11](https://dlmf.nist.gov/19.2.E11): [`DLMF.EllipticIntegrals.bulirschCel`](DLMF/EllipticIntegrals/Legendre.lean#L224) (definition).
- [19.2.E11_5](https://dlmf.nist.gov/19.2.E11_5): [`DLMF.EllipticIntegrals.bulirschEl1`](DLMF/EllipticIntegrals/Legendre.lean#L234) (definition).
- [19.2.E12](https://dlmf.nist.gov/19.2.E12): [`DLMF.EllipticIntegrals.bulirschEl2`](DLMF/EllipticIntegrals/Legendre.lean#L242) (definition).
- [19.2.E13](https://dlmf.nist.gov/19.2.E13): [`DLMF.EllipticIntegrals.compEllInt_eq_bulirschCel`](DLMF/EllipticIntegrals/LegendreIdentities.lean#L371) (proved); [`DLMF.EllipticIntegrals.incEllIntFk_eq_bulirschEl1`](DLMF/EllipticIntegrals/LegendreIdentities.lean#L431) (proved). 19.2.E13 (k_c² = 1 − k²) is built into each Bulirsch bridge.
- [19.2.E14](https://dlmf.nist.gov/19.2.E14): [`DLMF.EllipticIntegrals.compEllInt_eq_bulirschCel`](DLMF/EllipticIntegrals/LegendreIdentities.lean#L371) (proved); [`DLMF.EllipticIntegrals.compEllIntEk_eq_bulirschCel`](DLMF/EllipticIntegrals/LegendreIdentities.lean#L394) (proved); [`DLMF.EllipticIntegrals.compEllIntEk_sub_eq_bulirschCel`](DLMF/EllipticIntegrals/LegendreIdentities.lean#L407) (proved). Real 0 < k_c, or all real k for E; D and Π in `compEllInt_eq_bulirschCel`.
- [19.2.E15](https://dlmf.nist.gov/19.2.E15): [`DLMF.EllipticIntegrals.incEllIntFk_eq_bulirschEl1`](DLMF/EllipticIntegrals/LegendreIdentities.lean#L431) (proved); [`DLMF.EllipticIntegrals.incEllInt_eq_bulirschEl2`](DLMF/EllipticIntegrals/LegendreIdentities.lean#L440) (admitted). The el1 bridge is proved for every complex k and real |φ| < π/2; the el2 bridges (F, E, D; real k² < 1) are admitted.
- [19.2.iii](https://dlmf.nist.gov/19.2.iii): [`DLMF.EllipticIntegrals.tendsto_bulirsch_atTop`](DLMF/EllipticIntegrals/LegendreIdentities.lean#L462) (admitted). Prose of 19.2(iii): el1, el2 as x → ∞ give cel (admitted). The remark that k_c may be pure imaginary is covered by the complex `kc` argument.
- [19.2.E16](https://dlmf.nist.gov/19.2.E16): [`DLMF.EllipticIntegrals.bulirschEl3`](DLMF/EllipticIntegrals/Legendre.lean#L251) (definition); [`DLMF.EllipticIntegrals.bulirschEl3_eq_incEllIntPik`](DLMF/EllipticIntegrals/LegendreIdentities.lean#L451) (proved).
- [19.2.E17](https://dlmf.nist.gov/19.2.E17): [`DLMF.EllipticIntegrals.symEllIntRC_eq_integral`](DLMF/EllipticIntegrals/LegendreIdentities.lean#L474) (proved); [`DLMF.EllipticIntegrals.symEllIntRC_eq_cauchyPV`](DLMF/EllipticIntegrals/LegendreIdentities.lean#L482) (proved). R_C is ACQ19C's `symEllIntRC` (Symmetric.lean); 19.2.17 proved for the ordinary integral and for the PV (y < 0) form.
- [19.2.E18](https://dlmf.nist.gov/19.2.E18): [`DLMF.EllipticIntegrals.symEllIntRC_of_lt`](DLMF/EllipticIntegrals/LegendreIdentities.lean#L538) (proved).
- [19.2.E19](https://dlmf.nist.gov/19.2.E19): [`DLMF.EllipticIntegrals.symEllIntRC_of_gt`](DLMF/EllipticIntegrals/LegendreIdentities.lean#L568) (proved).
- [19.2.E20](https://dlmf.nist.gov/19.2.E20): [`DLMF.EllipticIntegrals.symEllIntRC_of_neg`](DLMF/EllipticIntegrals/LegendreIdentities.lean#L584) (admitted).
- [19.2.E21](https://dlmf.nist.gov/19.2.E21): [`DLMF.EllipticIntegrals.symEllIntRC_eq_integral_segment`](DLMF/EllipticIntegrals/LegendreIdentities.lean#L597) (admitted).
- [19.2.E22](https://dlmf.nist.gov/19.2.E22): [`DLMF.EllipticIntegrals.symEllIntRC_eq_integral_RC`](DLMF/EllipticIntegrals/LegendreIdentities.lean#L605) (admitted).

## [§19.4 Derivatives and Differential Equations](https://dlmf.nist.gov/19.4)

- [19.4.E1](https://dlmf.nist.gov/19.4.E1): [`DLMF.EllipticIntegrals.hasDerivAt_compEllIntKk`](DLMF/EllipticIntegrals/Derivatives.lean#L141) (proved); [`DLMF.EllipticIntegrals.hasDerivAt_compEllIntEk_sub`](DLMF/EllipticIntegrals/Derivatives.lean#L199) (proved); [`DLMF.Elliptic.Real.hasDerivAt_compEllIntKm`](DLMF/Elliptic/Complete.lean#L207) (proved); [`DLMF.Elliptic.Real.hasDerivAt_compEllIntKm_sq`](DLMF/Elliptic/Complete.lean#L455) (proved). Complex k in `compEllIntDomain` (off the cuts, k ≠ 0); the real versions in `DLMF/Elliptic/Complete.lean` are proved.
- [19.4.E2](https://dlmf.nist.gov/19.4.E2): [`DLMF.EllipticIntegrals.hasDerivAt_compEllIntEk`](DLMF/EllipticIntegrals/Derivatives.lean#L177) (proved); [`DLMF.EllipticIntegrals.hasDerivAt_compEllIntEk_sub_compEllIntKk`](DLMF/EllipticIntegrals/Derivatives.lean#L211) (proved); [`DLMF.Elliptic.Real.hasDerivAt_compEllIntEm`](DLMF/Elliptic/Complete.lean#L182) (proved); [`DLMF.Elliptic.Real.hasDerivAt_compEllIntEm_sq`](DLMF/Elliptic/Complete.lean#L468) (proved).
- [19.4.E3](https://dlmf.nist.gov/19.4.E3): [`DLMF.EllipticIntegrals.deriv_deriv_compEllIntEk`](DLMF/EllipticIntegrals/Derivatives.lean#L223) (proved).
- [19.4.E4](https://dlmf.nist.gov/19.4.E4): [`DLMF.EllipticIntegrals.hasDerivAt_compEllIntPik`](DLMF/EllipticIntegrals/Derivatives.lean#L241) (proved).
- [19.4.E5](https://dlmf.nist.gov/19.4.E5): [`DLMF.EllipticIntegrals.hasDerivAt_incEllIntFk`](DLMF/EllipticIntegrals/Derivatives.lean#L451) (proved). Derivatives in k at fixed φ, with `legendrePathOK φ k` (the path stays off the branch cut).
- [19.4.E6](https://dlmf.nist.gov/19.4.E6): [`DLMF.EllipticIntegrals.hasDerivAt_incEllIntEk`](DLMF/EllipticIntegrals/Derivatives.lean#L498) (proved).
- [19.4.E7](https://dlmf.nist.gov/19.4.E7): [`DLMF.EllipticIntegrals.hasDerivAt_incEllIntPik`](DLMF/EllipticIntegrals/Derivatives.lean#L522) (proved).
- [19.4.E8](https://dlmf.nist.gov/19.4.E8): [`DLMF.EllipticIntegrals.incEllIntFk_ode`](DLMF/EllipticIntegrals/Derivatives.lean#L598) (proved).
- [19.4.E9](https://dlmf.nist.gov/19.4.E9): [`DLMF.EllipticIntegrals.incEllIntEk_ode`](DLMF/EllipticIntegrals/Derivatives.lean#L647) (proved).
- [19.4.ii](https://dlmf.nist.gov/19.4.ii): [`DLMF.EllipticIntegrals.compEllIntKk_compEllIntEk_ode`](DLMF/EllipticIntegrals/Derivatives.lean#L673) (proved). K and E satisfy the hypergeometric ODEs of 19.4(ii); proved from the admitted 19.4.E1–E2.

## [§19.5 Maclaurin and Related Expansions](https://dlmf.nist.gov/19.5)

- [19.5.E1](https://dlmf.nist.gov/19.5.E1): [`DLMF.EllipticIntegrals.compEllIntKk_hasSum`](DLMF/EllipticIntegrals/Expansions.lean#L93) (proved); [`DLMF.Elliptic.Real.compEllIntKm_eq_ordinaryHypergeometric`](DLMF/Elliptic/Complete.lean#L427) (proved); [`DLMF.Hypergeometric.compEllIntKkSeries`](DLMF/Hypergeometric/Identities.lean#L2245) (definition).
- [19.5.E2](https://dlmf.nist.gov/19.5.E2): [`DLMF.EllipticIntegrals.compEllIntEk_hasSum`](DLMF/EllipticIntegrals/Expansions.lean#L109) (proved); [`DLMF.Elliptic.Real.compEllIntEm_eq_ordinaryHypergeometric`](DLMF/Elliptic/Complete.lean#L436) (proved).
- [19.5.E3](https://dlmf.nist.gov/19.5.E3): [`DLMF.EllipticIntegrals.compEllIntDk_hasSum`](DLMF/EllipticIntegrals/Expansions.lean#L125) (proved).
- [19.5.E4](https://dlmf.nist.gov/19.5.E4): [`DLMF.EllipticIntegrals.compEllIntPik_hasSum`](DLMF/EllipticIntegrals/Expansions.lean#L165) (admitted). F₁ written as `∑' p : ℕ × ℕ, ei19a_appF1Term …` (the project's `appF1` cannot be imported, see conventions).
- [19.5.E4_1](https://dlmf.nist.gov/19.5.E4_1): [`DLMF.EllipticIntegrals.incEllIntFk_hasSum`](DLMF/EllipticIntegrals/Expansions.lean#L176) (admitted).
- [19.5.E4_2](https://dlmf.nist.gov/19.5.E4_2): [`DLMF.EllipticIntegrals.incEllIntEk_hasSum`](DLMF/EllipticIntegrals/Expansions.lean#L190) (admitted).
- [19.5.E4_3](https://dlmf.nist.gov/19.5.E4_3): [`DLMF.EllipticIntegrals.incEllIntPik_hasSum`](DLMF/EllipticIntegrals/Expansions.lean#L204) (admitted).
- [19.5.E5](https://dlmf.nist.gov/19.5.E5): [`DLMF.EllipticIntegrals.jacobiNomek_isBigO`](DLMF/EllipticIntegrals/Expansions.lean#L217) (admitted). The `+ ⋯` series are stated as `O(r⁵)` (`Asymptotics.IsBigO`) as real `k → 0+`; 19.5.E6–E7 likewise with `O(λ²¹)`.
- [19.5.E6](https://dlmf.nist.gov/19.5.E6): [`DLMF.EllipticIntegrals.jacobiNomek_isBigO_lambda`](DLMF/EllipticIntegrals/Expansions.lean#L226) (admitted).
- [19.5.E7](https://dlmf.nist.gov/19.5.E7): [`DLMF.EllipticIntegrals.jacobiNomek_isBigO_lambda`](DLMF/EllipticIntegrals/Expansions.lean#L226) (admitted).
- [19.5.E8](https://dlmf.nist.gov/19.5.E8): [`DLMF.EllipticIntegrals.compEllIntKk_eq_nome_series`](DLMF/EllipticIntegrals/Expansions.lean#L236) (admitted).
- [19.5.E9](https://dlmf.nist.gov/19.5.E9): [`DLMF.EllipticIntegrals.compEllIntEk_eq_nome_series`](DLMF/EllipticIntegrals/Expansions.lean#L243) (admitted).
- [19.5.E10](https://dlmf.nist.gov/19.5.E10): [`DLMF.EllipticIntegrals.compEllIntKk_eq_landen_prod`](DLMF/EllipticIntegrals/Expansions.lean#L286) (proved). Natural-order partial products ∏_{m=1}^{N}(1 + k_m) → 2K/π.
- [19.5.E11](https://dlmf.nist.gov/19.5.E11): [`DLMF.EllipticIntegrals.landenModulusSeq`](DLMF/EllipticIntegrals/Expansions.lean#L253) (definition).

## [§19.6 Special Cases](https://dlmf.nist.gov/19.6)

- [19.6.E1](https://dlmf.nist.gov/19.6.E1): [`DLMF.EllipticIntegrals.compEllInt_special_pi_div_two`](DLMF/EllipticIntegrals/SpecialCases.lean#L128) (proved); [`DLMF.EllipticIntegrals.compEllInt_special_one`](DLMF/EllipticIntegrals/SpecialCases.lean#L140) (proved); [`DLMF.EllipticIntegrals.tendsto_norm_compEllIntKk_one'`](DLMF/EllipticIntegrals/SpecialCases.lean#L149) (proved); [`DLMF.EllipticIntegrals.tendsto_norm_cCompEllIntKk_zero`](DLMF/EllipticIntegrals/SpecialCases.lean#L156) (proved); [`DLMF.Elliptic.Real.compEllIntEm_one`](DLMF/Elliptic/Complete.lean#L248) (proved). Values at k = 0, k = 1 and the limits K → ∞ as k → 1, K' → ∞ as k → 0 (the limits proved from admitted JacobiElliptic lemmas).
- [19.6.E2](https://dlmf.nist.gov/19.6.E2): [`DLMF.EllipticIntegrals.compEllIntPik_sq_self`](DLMF/EllipticIntegrals/SpecialCases.lean#L321) (proved); [`DLMF.EllipticIntegrals.compEllIntPik_neg_self`](DLMF/EllipticIntegrals/SpecialCases.lean#L356) (admitted).
- [19.6.E3](https://dlmf.nist.gov/19.6.E3): [`DLMF.EllipticIntegrals.compEllIntPik_special`](DLMF/EllipticIntegrals/SpecialCases.lean#L368) (proved).
- [19.6.E4](https://dlmf.nist.gov/19.6.E4): [`DLMF.EllipticIntegrals.tendsto_compEllIntPik`](DLMF/EllipticIntegrals/SpecialCases.lean#L379) (admitted).
- [19.6.E5](https://dlmf.nist.gov/19.6.E5): [`DLMF.EllipticIntegrals.compEllIntPik_of_one_lt`](DLMF/EllipticIntegrals/SpecialCases.lean#L387) (admitted). Real `1 < α²`; Cauchy principal value.
- [19.6.E6](https://dlmf.nist.gov/19.6.E6): [`DLMF.EllipticIntegrals.compEllIntPik_of_one_lt_special`](DLMF/EllipticIntegrals/SpecialCases.lean#L394) (admitted).
- [19.6.E7](https://dlmf.nist.gov/19.6.E7): [`DLMF.EllipticIntegrals.incEllIntFk_special`](DLMF/EllipticIntegrals/SpecialCases.lean#L407) (proved); [`DLMF.EllipticIntegrals.incEllIntFk_limits`](DLMF/EllipticIntegrals/SpecialCases.lean#L465) (proved).
- [19.6.E8](https://dlmf.nist.gov/19.6.E8): [`DLMF.EllipticIntegrals.incEllIntFk_one_eq_integral_sec`](DLMF/EllipticIntegrals/SpecialCases.lean#L414) (proved); [`DLMF.EllipticIntegrals.incEllIntFk_one`](DLMF/EllipticIntegrals/SpecialCases.lean#L433) (proved).
- [19.6.E9](https://dlmf.nist.gov/19.6.E9): [`DLMF.EllipticIntegrals.incEllIntEk_special`](DLMF/EllipticIntegrals/SpecialCases.lean#L489) (proved); [`DLMF.EllipticIntegrals.incEllIntEk_one`](DLMF/EllipticIntegrals/SpecialCases.lean#L495) (proved); [`DLMF.EllipticIntegrals.incEllIntEk_pi_div_two_one`](DLMF/EllipticIntegrals/SpecialCases.lean#L514) (proved); [`DLMF.EllipticIntegrals.incEllIntEk_one_complex`](DLMF/EllipticIntegrals/SpecialCases.lean#L521) (proved). E(φ, 1) = sin φ only for real |φ| ≤ π/2 (otherwise ∫₀^φ |cos θ| dθ); docstring records this. The complex form is admitted with |Re φ| < π/2.
- [19.6.E10](https://dlmf.nist.gov/19.6.E10): [`DLMF.EllipticIntegrals.tendsto_incEllIntEk_div`](DLMF/EllipticIntegrals/SpecialCases.lean#L550) (proved).
- [19.6.E11](https://dlmf.nist.gov/19.6.E11): [`DLMF.EllipticIntegrals.incEllIntPik_special`](DLMF/EllipticIntegrals/SpecialCases.lean#L559) (proved); [`DLMF.EllipticIntegrals.incEllIntPik_one_zero`](DLMF/EllipticIntegrals/SpecialCases.lean#L565) (proved).
- [19.6.E12](https://dlmf.nist.gov/19.6.E12): [`DLMF.EllipticIntegrals.incEllIntPik_special_RC`](DLMF/EllipticIntegrals/SpecialCases.lean#L612) (admitted).
- [19.6.E13](https://dlmf.nist.gov/19.6.E13): [`DLMF.EllipticIntegrals.incEllIntPik_zero`](DLMF/EllipticIntegrals/SpecialCases.lean#L362) (proved); [`DLMF.EllipticIntegrals.incEllIntPik_special_k`](DLMF/EllipticIntegrals/SpecialCases.lean#L629) (proved).
- [19.6.E14](https://dlmf.nist.gov/19.6.E14): [`DLMF.EllipticIntegrals.incEllIntPik_pi_div_two`](DLMF/EllipticIntegrals/SpecialCases.lean#L659) (proved); [`DLMF.EllipticIntegrals.tendsto_incEllIntPik_div`](DLMF/EllipticIntegrals/SpecialCases.lean#L663) (proved).
- [19.6.E15](https://dlmf.nist.gov/19.6.E15): [`DLMF.EllipticIntegrals.symEllIntRC_special`](DLMF/EllipticIntegrals/SpecialCases.lean#L694) (admitted); [`DLMF.EllipticIntegrals.tendsto_symEllIntRC_zero`](DLMF/EllipticIntegrals/SpecialCases.lean#L707) (admitted).

## [§19.7 Connection Formulas](https://dlmf.nist.gov/19.7)

- [19.7.E1](https://dlmf.nist.gov/19.7.E1): [`DLMF.EllipticIntegrals.legendre_relation_ofReal`](DLMF/EllipticIntegrals/Connection.lean#L43) (proved); [`DLMF.EllipticIntegrals.legendre_relation_complex`](DLMF/EllipticIntegrals/Connection.lean#L537) (proved); [`DLMF.Elliptic.legendre_relation`](DLMF/Elliptic/Complete.lean#L317) (proved).
- [19.7.E2](https://dlmf.nist.gov/19.7.E2): [`DLMF.EllipticIntegrals.compEllInt_imaginary_modulus`](DLMF/EllipticIntegrals/Connection.lean#L559) (proved); [`DLMF.EllipticIntegrals.compEllInt_imaginary_comodulus`](DLMF/EllipticIntegrals/Connection.lean#L567) (proved). **Correction (implicit condition).** The two formulas in k'/k (b, d) are acquired with `0 < Re k`; they fail with reversed sign for Re k < 0 (numerical evidence in conventions).
- [19.7.E3](https://dlmf.nist.gov/19.7.E3): [`DLMF.EllipticIntegrals.compEllInt_reciprocal_modulus`](DLMF/EllipticIntegrals/Connection.lean#L576) (admitted). Fettis's form, stated for `0 < Re k` and `Im k² ≠ 0`, with DLMF's upper/lower signs as `s = ±1` according to the sign of `Im k²`.
- [19.7.E4](https://dlmf.nist.gov/19.7.E4): [`DLMF.EllipticIntegrals.incEllInt_reciprocal_modulus`](DLMF/EllipticIntegrals/Connection.lean#L769) (proved).
- [19.7.E5](https://dlmf.nist.gov/19.7.E5): [`DLMF.EllipticIntegrals.incEllInt_imaginary_modulus`](DLMF/EllipticIntegrals/Connection.lean#L955) (proved).
- [19.7.E6](https://dlmf.nist.gov/19.7.E6): [`DLMF.EllipticIntegrals.incEllInt_imaginary_modulus`](DLMF/EllipticIntegrals/Connection.lean#L955) (proved).
- [19.7.E7](https://dlmf.nist.gov/19.7.E7): [`DLMF.EllipticIntegrals.incEllInt_imaginary_argument`](DLMF/EllipticIntegrals/Connection.lean#L1374) (proved).
- [19.7.E8](https://dlmf.nist.gov/19.7.E8): [`DLMF.EllipticIntegrals.incEllIntPik_add_first`](DLMF/EllipticIntegrals/Connection.lean#L1393) (admitted).
- [19.7.E9](https://dlmf.nist.gov/19.7.E9): [`DLMF.EllipticIntegrals.incEllIntPik_add_second`](DLMF/EllipticIntegrals/Connection.lean#L1406) (admitted).
- [19.7.E10](https://dlmf.nist.gov/19.7.E10): [`DLMF.EllipticIntegrals.incEllIntPik_add_third`](DLMF/EllipticIntegrals/Connection.lean#L1420) (admitted).
- [19.7.iii](https://dlmf.nist.gov/19.7.iii): [`DLMF.EllipticIntegrals.first_relation_omega_lt`](DLMF/EllipticIntegrals/Connection.lean#L1434) (proved). The prose ordering lemma for the three cases of 19.7(iii) (ω² < k² etc.) is proved.

## [§19.8 Quadratic Transformations](https://dlmf.nist.gov/19.8)

- [19.8.E1](https://dlmf.nist.gov/19.8.E1): [`DLMF.EllipticIntegrals.agmSeqA`](DLMF/EllipticIntegrals/Quadratic.lean#L44) (definition); [`DLMF.EllipticIntegrals.agmSeqG`](DLMF/EllipticIntegrals/Quadratic.lean#L50) (definition); [`DLMF.EllipticIntegrals.agmSeq_succ`](DLMF/EllipticIntegrals/Quadratic.lean#L61) (proved); [`DLMF.EllipticIntegrals.tendsto_agmSeq`](DLMF/EllipticIntegrals/Quadratic.lean#L72) (proved). Mathlib's `NNReal.agmSequences` lists `(g_{n+1}, a_{n+1})`; pointer already in `DLMF/Elliptic/MathlibCoverage.lean`. `agmSeqA/G` restore DLMF's indexing; recursion and convergence to `NNReal.agm` proved.
- [19.8.E2](https://dlmf.nist.gov/19.8.E2): [`DLMF.EllipticIntegrals.agmSeqC`](DLMF/EllipticIntegrals/Quadratic.lean#L56) (definition).
- [19.8.E3](https://dlmf.nist.gov/19.8.E3): [`DLMF.EllipticIntegrals.agmSeqC_succ`](DLMF/EllipticIntegrals/Quadratic.lean#L97) (proved).
- [19.8.E4](https://dlmf.nist.gov/19.8.E4): [`DLMF.EllipticIntegrals.inv_agm_eq_integral`](DLMF/EllipticIntegrals/Quadratic.lean#L122) (proved); [`DLMF.Elliptic.agmIntegral_eq_pi_div_two_div_agm`](DLMF/Elliptic/AGM.lean#L263) (proved). First form proved (`DLMF.Elliptic.agmIntegral_eq_pi_div_two_div_agm`, tag added); second (t-integral) form admitted.
- [19.8.E5](https://dlmf.nist.gov/19.8.E5): [`DLMF.EllipticIntegrals.compEllIntKk_eq_pi_div_agm`](DLMF/EllipticIntegrals/Quadratic.lean#L170) (proved); [`DLMF.Elliptic.Real.compEllIntKm_eq_pi_div_agm`](DLMF/Elliptic/AGM.lean#L294) (proved). Complex k with real k² = m < 1.
- [19.8.E6](https://dlmf.nist.gov/19.8.E6): [`DLMF.EllipticIntegrals.compEllIntEk_eq_agm`](DLMF/EllipticIntegrals/Quadratic.lean#L196) (proved). Both forms; a₀ = 1, g₀ = k' (numerically checked with the exact Lean recursion).
- [19.8.E7](https://dlmf.nist.gov/19.8.E7): [`DLMF.EllipticIntegrals.compEllIntPik_eq_agm`](DLMF/EllipticIntegrals/Quadratic.lean#L302) (admitted).
- [19.8.E8](https://dlmf.nist.gov/19.8.E8): [`DLMF.EllipticIntegrals.agmPiSeq`](DLMF/EllipticIntegrals/Quadratic.lean#L284) (definition); [`DLMF.EllipticIntegrals.agmPiEps`](DLMF/EllipticIntegrals/Quadratic.lean#L296) (definition).
- [19.8.E9](https://dlmf.nist.gov/19.8.E9): [`DLMF.EllipticIntegrals.compEllIntPik_eq_agm_of_one_lt`](DLMF/EllipticIntegrals/Quadratic.lean#L312) (admitted). Cauchy principal value for real α² > 1, numerically checked.
- [19.8.E10](https://dlmf.nist.gov/19.8.E10): [`DLMF.EllipticIntegrals.compEllIntPik_eq_agm_of_one_lt`](DLMF/EllipticIntegrals/Quadratic.lean#L312) (admitted).
- [19.8.E11](https://dlmf.nist.gov/19.8.E11): [`DLMF.EllipticIntegrals.landen_descending_amplitude`](DLMF/EllipticIntegrals/Quadratic.lean#L332) (proved). Real 0 < k < 1, 0 < φ < π/2: equality of the two expressions of φ₁ and k₁ < k (admitted).
- [19.8.E12](https://dlmf.nist.gov/19.8.E12): [`DLMF.EllipticIntegrals.compEllInt_landen_descending_ofReal`](DLMF/EllipticIntegrals/Quadratic.lean#L364) (proved); [`DLMF.EllipticIntegrals.compEllInt_landen_descending`](DLMF/EllipticIntegrals/Quadratic.lean#L428) (proved); [`DLMF.Elliptic.Real.compEllIntKm_landen_descending`](DLMF/Elliptic/AGM.lean#L304) (proved); [`DLMF.Elliptic.Real.compEllIntEm_landen_descending`](DLMF/Elliptic/AGM.lean#L356) (proved). Real k² < 1 proved from the existing real Landen theorems; complex principal-domain form admitted.
- [19.8.E13](https://dlmf.nist.gov/19.8.E13): [`DLMF.EllipticIntegrals.incEllInt_landen_descending`](DLMF/EllipticIntegrals/Quadratic.lean#L458) (admitted).
- [19.8.E14](https://dlmf.nist.gov/19.8.E14): [`DLMF.EllipticIntegrals.incEllIntPik_landen_descending`](DLMF/EllipticIntegrals/Quadratic.lean#L473) (admitted).
- [19.8.E15](https://dlmf.nist.gov/19.8.E15): [`DLMF.EllipticIntegrals.incEllIntPik_landen_descending`](DLMF/EllipticIntegrals/Quadratic.lean#L473) (admitted).
- [19.8.E16](https://dlmf.nist.gov/19.8.E16): [`DLMF.EllipticIntegrals.incEllInt_landen_ascending`](DLMF/EllipticIntegrals/Quadratic.lean#L492) (admitted).
- [19.8.E17](https://dlmf.nist.gov/19.8.E17): [`DLMF.EllipticIntegrals.incEllInt_landen_ascending`](DLMF/EllipticIntegrals/Quadratic.lean#L492) (admitted).
- [19.8.E18](https://dlmf.nist.gov/19.8.E18): [`DLMF.EllipticIntegrals.incEllInt_gauss`](DLMF/EllipticIntegrals/Quadratic.lean#L508) (admitted).
- [19.8.E19](https://dlmf.nist.gov/19.8.E19): [`DLMF.EllipticIntegrals.incEllInt_gauss`](DLMF/EllipticIntegrals/Quadratic.lean#L508) (admitted).
- [19.8.E20](https://dlmf.nist.gov/19.8.E20): [`DLMF.EllipticIntegrals.incEllIntPik_gauss`](DLMF/EllipticIntegrals/Quadratic.lean#L523) (admitted). ρ may be pure imaginary for 0 < α² < k²; stated with complex ρ, α₁².
- [19.8.E21](https://dlmf.nist.gov/19.8.E21): [`DLMF.EllipticIntegrals.incEllIntPik_gauss`](DLMF/EllipticIntegrals/Quadratic.lean#L523) (admitted).


## Prose, informal and excluded items (part A)

- §19.1 (notation): `k² + k'² = 1` is `ei19a_jacobiComodulusk_sq`; the principal-value convention
  for square roots is built into every definition. 19.1.p4–p7 (other authors' notations,
  Byrd–Friedman, Abramowitz–Stegun, Erdélyi) are bibliographic: excluded: bibliographic.
  19.1.E3–E4 (symmetric integrals) belong to part C.
- 19.2.i.p1 (general elliptic integral `∫ r(s, t) dt`): acquired through 19.2.E1–E3
  (`ellipticIntegrand_eq`, `ellipticIntegrand_elliptic_part`).
- 19.2.ii.p2–p5 (branches, analyticity, K(−k) = K(k), the alternate circular/hyperbolic forms):
  tagged 19.2.ii (above). 19.2.iii.p2 (k_c may be pure imaginary) is covered by the complex
  `kc` argument of the Bulirsch functions.
- 19.5.p4, 19.6.i.p4, 19.7.Px1.p2, 19.7.Px2.p2 and 19.7.Px4.p2 are pointers to other sections
  or references and informal remarks: excluded: bibliographic/informal.
- §19.3 (graphics): excluded: graphics. §§19.30–19.35 (applications) and 19.36–19.39
  (computation, tables, approximations, software) are excluded by the chapter scope; their
  purely mathematical results are listed by the parts that own the related formulas.
- No part-A item is purely numerical.

## Validation (part A)

- `lake build` of `DLMF.EllipticIntegrals.{Legendre, LegendreIdentities, Derivatives,
  Expansions, SpecialCases, Connection, Quadratic}` and `DLMF.Elliptic.AGM` succeeds
  (the lakefile sets `autoImplicit = false`, `relaxedAutoImplicit = false`); no warnings other
  than `declaration uses 'sorry'`.
- `#print axioms` (temporary, removed after the check) on all 44 proved theorems: 38 depend
  only on `propext`, `Classical.choice`, `Quot.sound`; the six marked "proved from admissions"
  add `sorryAx`.
- The strict per-file check `lake env lean -DautoImplicit=false …` cannot run on any module that
  imports `lean-codes`' Carlson library: `lake env lean` resolves `ToMathlib.*` to
  `../lean-codes/.lake/build-codes/lib/lean/ToMathlib/Analysis/Asymptotics/WatsonSector.olean`,
  which does not exist (both packages have a `ToMathlib` root); `lake build` is unaffected.

## Numbered formulas and prose items (part B: §§19.9–19.14)

Modules `DLMF.EllipticIntegrals.{Inequalities, Relations, Addition, Asymptotics, Reduction}`.
Conventions of part B:

- Real-variable statements (inequalities, addition theorems, reductions) are stated for the
  complex Legendre integrals of part A at real arguments, via `.re` or `ofReal` casts; bridges
  `incEllIntFk_eq_ofReal` etc. connect to `DLMF.Elliptic.Real.incEllIntFm`.
- 19.10.1: the ranges of `x` are implicit in DLMF; the arccos line holds only for `0 ≤ x ≤ y`
  (domain qualification, checked numerically; not an erratum).
- 19.11.1–19.11.4: `ψ` is fixed by both `sin ψ` and `cos ψ`. 19.11.5, 19.11.6_5, 19.11.16 use
  the principal `R_C` (Cauchy principal value for negative second argument); the formulas were
  verified numerically to hold exactly when `α² < 1` and `α²(1 - cos θ cos φ cos ψ) < 1`
  (19.11.16: `α²(1 - cos²θ cos ψ) < 1`), which are hypotheses ("care has to be taken with the
  multivalued functions"). 19.11.6_5 is stated for `k² < α²` (the case `δ = 0` is a limit).
- 19.12: asymptotic statements are recast as `HasSum`/`IsBigO` statements along explicit
  filters (`k → 1⁻`; `x/y → 0` and `y/x → 0` on `ℝ × ℝ`); 19.12.1 needs the principal `k'`,
  hypothesis `1 - k² ∈ slitPlane`.
- 19.13 consists of bibliographic pointers only.
- No DLMF errata were found in §§19.9–19.14 (all formulas checked with mpmath).

## [§19.9 Inequalities](https://dlmf.nist.gov/19.9)

- [19.9.E1](https://dlmf.nist.gov/19.9.E1): [`DLMF.EllipticIntegrals.log_four_le_compEllIntKk_add_log`](DLMF/EllipticIntegrals/Inequalities.lean#L116) (admitted); [`DLMF.EllipticIntegrals.one_le_compEllIntEk_le`](DLMF/EllipticIntegrals/Inequalities.lean#L407) (proved); [`DLMF.EllipticIntegrals.one_le_compEllIntPik_le`](DLMF/EllipticIntegrals/Inequalities.lean#L416) (proved).
- [19.9.E2](https://dlmf.nist.gov/19.9.E2): [`DLMF.EllipticIntegrals.compEllIntKk_div_log_bounds`](DLMF/EllipticIntegrals/Inequalities.lean#L123) (admitted).
- [19.9.E3](https://dlmf.nist.gov/19.9.E3): [`DLMF.EllipticIntegrals.eight_add_sq_mul_compEllIntKk_div_log_bounds`](DLMF/EllipticIntegrals/Inequalities.lean#L130) (admitted).
- [19.9.E4](https://dlmf.nist.gov/19.9.E4): [`DLMF.EllipticIntegrals.compEllIntEk_bounds`](DLMF/EllipticIntegrals/Inequalities.lean#L138) (admitted).
- [19.9.E5](https://dlmf.nist.gov/19.9.E5): [`DLMF.EllipticIntegrals.pi_mul_cCompEllIntKk_div_bounds`](DLMF/EllipticIntegrals/Inequalities.lean#L146) (admitted).
- [19.9.E6](https://dlmf.nist.gov/19.9.E6): [`DLMF.EllipticIntegrals.compEllIntKk_sub_compEllIntEk_bounds`](DLMF/EllipticIntegrals/Inequalities.lean#L156) (admitted).
- [19.9.E7](https://dlmf.nist.gov/19.9.E7): [`DLMF.EllipticIntegrals.compEllIntEk_sub_mul_compEllIntKk_bounds`](DLMF/EllipticIntegrals/Inequalities.lean#L165) (admitted).
- [19.9.E8](https://dlmf.nist.gov/19.9.E8): [`DLMF.EllipticIntegrals.compEllIntEk_div_compEllIntKk_bounds`](DLMF/EllipticIntegrals/Inequalities.lean#L175) (admitted).
- [19.9.E9](https://dlmf.nist.gov/19.9.E9): [`DLMF.EllipticIntegrals.ellipsePerimeter_eq`](DLMF/EllipticIntegrals/Inequalities.lean#L188) (proved).
- [19.9.E10](https://dlmf.nist.gov/19.9.E10): excluded: numerical (Ramanujan's approximation formula with its leading error term, an approximation without an exact statement; its accuracy figures are numerical). The analytical claim that Ramanujan's approximation is from below is acquired under 19.9.i.p3.
- [19.9.E11](https://dlmf.nist.gov/19.9.E11): [`DLMF.EllipticIntegrals.incEllIntFk_bounds`](DLMF/EllipticIntegrals/Inequalities.lean#L260) (proved).
- [19.9.E12](https://dlmf.nist.gov/19.9.E12): [`DLMF.EllipticIntegrals.incEllIntEk_bounds`](DLMF/EllipticIntegrals/Inequalities.lean#L307) (proved).
- [19.9.E13](https://dlmf.nist.gov/19.9.E13): [`DLMF.EllipticIntegrals.incEllIntPik_bounds`](DLMF/EllipticIntegrals/Inequalities.lean#L352) (proved).
- [19.9.E14](https://dlmf.nist.gov/19.9.E14): [`DLMF.EllipticIntegrals.incEllIntFk_div_sin_bounds`](DLMF/EllipticIntegrals/Inequalities.lean#L446) (admitted).
- [19.9.E15](https://dlmf.nist.gov/19.9.E15): [`DLMF.EllipticIntegrals.incEllIntFk_div_sin_mul_log_bounds`](DLMF/EllipticIntegrals/Inequalities.lean#L457) (admitted).
- [19.9.E16](https://dlmf.nist.gov/19.9.E16): [`DLMF.EllipticIntegrals.incEllIntFk_eq_log_sub_bounds`](DLMF/EllipticIntegrals/Inequalities.lean#L469) (admitted).
- [19.9.E17](https://dlmf.nist.gov/19.9.E17): [`DLMF.EllipticIntegrals.incEllIntFk_arctanh_bounds`](DLMF/EllipticIntegrals/Inequalities.lean#L593) (proved).
- [19.9.E18](https://dlmf.nist.gov/19.9.E18): [`DLMF.EllipticIntegrals.incEllIntFk_arctanh_bounds`](DLMF/EllipticIntegrals/Inequalities.lean#L593) (proved).

Analytical prose:

- [19.9.i.p1](https://dlmf.nist.gov/19.9#i.p1): Range convention `0 < k < 1` (except 19.9.4, `0 ≤ k ≤ 1`); used as hypotheses throughout `Inequalities.lean`.
- [19.9.i.p2](https://dlmf.nist.gov/19.9#i.p2): Introduces 19.9.6–19.9.8; the bibliographic pointers (Alzer–Qiu, Anderson et al., Qiu–Vamanamurthy) and the remark that the left inequalities of 19.9.2/19.9.3 are equivalent are commentary; the sharper-range remarks "when `0 < k² ≤ 0.922`", "`0 ≤ k² ≤ 0.9960`" are excluded: numerical.
- [19.9.i.p3](https://dlmf.nist.gov/19.9#i.p3): [`DLMF.EllipticIntegrals.ellipsePerimeter`](DLMF/EllipticIntegrals/Inequalities.lean#L182) (definition) The perimeter `L(a,b)` is defined as an arc-length integral; Ramanujan's approximation being from below (Barnard et al. 2000) is acquired as [`DLMF.EllipticIntegrals.pi_mul_ramanujan_le_ellipsePerimeter`](DLMF/EllipticIntegrals/Inequalities.lean#L250) (admitted). The list of thirteen approximations, the accuracy figure 0.023% and the approximation formula 19.9.10 are excluded: numerical.
- [19.9.ii.p1](https://dlmf.nist.gov/19.9#ii.p1): Range convention `0 < k < 1`, `0 ≤ φ ≤ π/2`, `Δ > 0`; endpoint qualifications (`φ < π/2` where a bound is infinite, `φ > 0` where `sin φ` divides) recorded in the docstrings.
- [19.9.ii.p2](https://dlmf.nist.gov/19.9#ii.p2): Introduces 19.9.11–19.9.13 ("follow directly from the defining integrals"); proved from the integrals.
- [19.9.ii.p3](https://dlmf.nist.gov/19.9#ii.p3): Introduces 19.9.14–19.9.16; the remark on when 19.9.15 is preferable is qualitative commentary.
- [19.9.ii.p4](https://dlmf.nist.gov/19.9#ii.p4): Introduces 19.9.17–19.9.18 (Carlson 1961b); bibliographic.
- [19.9.ii.p5](https://dlmf.nist.gov/19.9#ii.p5): Bibliographic pointer (inequalities for `R_F` via 19.25.5); no formula stated.
- [19.9.i](https://dlmf.nist.gov/19.9.i): [`DLMF.EllipticIntegrals.ellipsePerimeter`](DLMF/EllipticIntegrals/Inequalities.lean#L182) (definition); [`DLMF.EllipticIntegrals.pi_mul_ramanujan_le_ellipsePerimeter`](DLMF/EllipticIntegrals/Inequalities.lean#L250) (admitted).

## [§19.10 Relations to Other Functions](https://dlmf.nist.gov/19.10)

- [19.10.E1](https://dlmf.nist.gov/19.10.E1): [`DLMF.EllipticIntegrals.log_div_eq_mul_symEllIntRC`](DLMF/EllipticIntegrals/Relations.lean#L124) (proved); [`DLMF.EllipticIntegrals.arctan_div_eq_mul_symEllIntRC`](DLMF/EllipticIntegrals/Relations.lean#L139) (proved); [`DLMF.EllipticIntegrals.artanh_div_eq_mul_symEllIntRC`](DLMF/EllipticIntegrals/Relations.lean#L165) (proved); [`DLMF.EllipticIntegrals.arcsin_div_eq_mul_symEllIntRC`](DLMF/EllipticIntegrals/Relations.lean#L197) (proved); [`DLMF.EllipticIntegrals.arccos_div_eq_mul_symEllIntRC`](DLMF/EllipticIntegrals/Relations.lean#L230) (proved); [`DLMF.EllipticIntegrals.arsinh_div_eq_mul_symEllIntRC`](DLMF/EllipticIntegrals/Relations.lean#L258) (proved); [`DLMF.EllipticIntegrals.arcosh_div_eq_mul_symEllIntRC`](DLMF/EllipticIntegrals/Relations.lean#L271) (proved).
- [19.10.E2](https://dlmf.nist.gov/19.10.E2): [`DLMF.EllipticIntegrals.sinh_mul_symEllIntRC_eq_gudermannian`](DLMF/EllipticIntegrals/Relations.lean#L293) (proved).

Analytical prose:

- [19.10.i.p1](https://dlmf.nist.gov/19.10#i.p1): Cross-reference to §§20.9(i), 22.15(ii), 23.6(iv) (acquired in those chapters) and Erdélyi et al.; no formula stated here.
- [19.10.ii.p1](https://dlmf.nist.gov/19.10#ii.p1): Assumption `y > 0` and the remark on the asymptotic role of the factor multiplying `R_C` as the left side tends to 0 (qualitative). The ranges of `x` are implicit in DLMF; the natural ranges are stated (`x > 0`, all `x`, `|x| < y`, `|x| ≤ y`, `0 ≤ x ≤ y`, `x ≥ y`). The arccos line is false for `x < 0` (its right side is even in `x`; `arccos(-1/2) = 2π/3` vs `π/3`), a domain qualification, not an erratum.
- [19.10.ii.p2](https://dlmf.nist.gov/19.10#ii.p2): Cross-reference to 19.6.8 (acquired by 19A) and introduction of 19.10.2.

## [§19.11 Addition Theorems](https://dlmf.nist.gov/19.11)

- [19.11.E1](https://dlmf.nist.gov/19.11.E1): [`DLMF.EllipticIntegrals.incEllIntFk_add`](DLMF/EllipticIntegrals/Addition.lean#L157) (admitted).
- [19.11.E2](https://dlmf.nist.gov/19.11.E2): [`DLMF.EllipticIntegrals.incEllIntEk_add`](DLMF/EllipticIntegrals/Addition.lean#L166) (admitted).
- [19.11.E3](https://dlmf.nist.gov/19.11.E3): [`DLMF.EllipticIntegrals.addition_sin_sq_add_cos_sq`](DLMF/EllipticIntegrals/Addition.lean#L65) (proved); [`DLMF.EllipticIntegrals.incEllIntFk_add`](DLMF/EllipticIntegrals/Addition.lean#L157) (admitted); [`DLMF.EllipticIntegrals.incEllIntEk_add`](DLMF/EllipticIntegrals/Addition.lean#L166) (admitted).
- [19.11.E4](https://dlmf.nist.gov/19.11.E4): [`DLMF.EllipticIntegrals.addition_sin_sq_add_cos_sq`](DLMF/EllipticIntegrals/Addition.lean#L65) (proved); [`DLMF.EllipticIntegrals.addition_tan_half`](DLMF/EllipticIntegrals/Addition.lean#L97) (proved).
- [19.11.E5](https://dlmf.nist.gov/19.11.E5): [`DLMF.EllipticIntegrals.incEllIntPik_add`](DLMF/EllipticIntegrals/Addition.lean#L176) (admitted).
- [19.11.E6](https://dlmf.nist.gov/19.11.E6): [`DLMF.EllipticIntegrals.incEllIntPik_add`](DLMF/EllipticIntegrals/Addition.lean#L176) (admitted).
- [19.11.E6_5](https://dlmf.nist.gov/19.11.E6_5): [`DLMF.EllipticIntegrals.symEllIntRC_addition_eq_arctan`](DLMF/EllipticIntegrals/Addition.lean#L191) (admitted).
- [19.11.E7](https://dlmf.nist.gov/19.11.E7): [`DLMF.EllipticIntegrals.incEllIntFk_eq_compEllIntKk_sub`](DLMF/EllipticIntegrals/Addition.lean#L435) (proved).
- [19.11.E8](https://dlmf.nist.gov/19.11.E8): [`DLMF.EllipticIntegrals.incEllIntEk_eq_compEllIntEk_sub`](DLMF/EllipticIntegrals/Addition.lean#L453) (proved).
- [19.11.E9](https://dlmf.nist.gov/19.11.E9): [`DLMF.EllipticIntegrals.incEllIntFk_eq_compEllIntKk_sub`](DLMF/EllipticIntegrals/Addition.lean#L435) (proved); [`DLMF.EllipticIntegrals.incEllIntEk_eq_compEllIntEk_sub`](DLMF/EllipticIntegrals/Addition.lean#L453) (proved).
- [19.11.E10](https://dlmf.nist.gov/19.11.E10): [`DLMF.EllipticIntegrals.incEllIntPik_eq_compEllIntPik_sub`](DLMF/EllipticIntegrals/Addition.lean#L471) (admitted).
- [19.11.E11](https://dlmf.nist.gov/19.11.E11): [`DLMF.EllipticIntegrals.incEllIntPik_eq_compEllIntPik_sub`](DLMF/EllipticIntegrals/Addition.lean#L471) (admitted).
- [19.11.E12](https://dlmf.nist.gov/19.11.E12): [`DLMF.EllipticIntegrals.incEllIntFk_duplication`](DLMF/EllipticIntegrals/Addition.lean#L518) (proved from the admitted incEllIntFk_add (19.11.1)).
- [19.11.E13](https://dlmf.nist.gov/19.11.E13): [`DLMF.EllipticIntegrals.incEllIntEk_duplication`](DLMF/EllipticIntegrals/Addition.lean#L528) (proved from the admitted incEllIntEk_add (19.11.2)).
- [19.11.E14](https://dlmf.nist.gov/19.11.E14): [`DLMF.EllipticIntegrals.incEllIntFk_duplication`](DLMF/EllipticIntegrals/Addition.lean#L518) (proved from the admitted incEllIntFk_add (19.11.1)); [`DLMF.EllipticIntegrals.incEllIntEk_duplication`](DLMF/EllipticIntegrals/Addition.lean#L528) (proved from the admitted incEllIntEk_add (19.11.2)).
- [19.11.E15](https://dlmf.nist.gov/19.11.E15): [`DLMF.EllipticIntegrals.duplication_half_angle`](DLMF/EllipticIntegrals/Addition.lean#L554) (proved).
- [19.11.E16](https://dlmf.nist.gov/19.11.E16): [`DLMF.EllipticIntegrals.incEllIntPik_duplication`](DLMF/EllipticIntegrals/Addition.lean#L625) (admitted).
- [19.11.E17](https://dlmf.nist.gov/19.11.E17): [`DLMF.EllipticIntegrals.incEllIntPik_duplication`](DLMF/EllipticIntegrals/Addition.lean#L625) (admitted).

Analytical prose:

- [19.11.i.p1](https://dlmf.nist.gov/19.11#i.p1): The addition theorems 19.11.1–19.11.4; `ψ` is fixed by both `sin ψ` and `cos ψ` (`ψ ∈ [0, π]`), consistency proved in `addition_sin_sq_add_cos_sq`.
- [19.11.i.p2](https://dlmf.nist.gov/19.11#i.p2): 19.11.5–19.11.6.
- [19.11.i.p3](https://dlmf.nist.gov/19.11#i.p3): 19.11.6_5 and the warning "care has to be taken with the multivalued functions": the branch region `α² < 1`, `α²(1 - cos θ cos φ cos ψ) < 1` was determined numerically and is a hypothesis of 19.11.5 and 19.11.6_5 (19.11.16 analogously).
- [19.11.ii.p1](https://dlmf.nist.gov/19.11#ii.p1): The case `ψ = π/2`, 19.11.7–19.11.11.
- [19.11.iii.p1](https://dlmf.nist.gov/19.11#iii.p1): The duplication case `φ = θ`, 19.11.12–19.11.17; `ei19b_dupSin_eq`, `ei19b_dupCos_eq` identify (19.11.14), (19.11.15 first) with (19.11.3), (19.11.4) at `φ = θ`.

## [§19.12 Asymptotic Approximations](https://dlmf.nist.gov/19.12)

- [19.12.E1](https://dlmf.nist.gov/19.12.E1): [`DLMF.EllipticIntegrals.compEllIntKk_hasSum_log`](DLMF/EllipticIntegrals/Asymptotics.lean#L83) (admitted).
- [19.12.E2](https://dlmf.nist.gov/19.12.E2): [`DLMF.EllipticIntegrals.compEllIntEk_hasSum_log`](DLMF/EllipticIntegrals/Asymptotics.lean#L94) (admitted).
- [19.12.E3](https://dlmf.nist.gov/19.12.E3): [`DLMF.EllipticIntegrals.compEllIntLogCoeff`](DLMF/EllipticIntegrals/Asymptotics.lean#L43) (definition); [`DLMF.EllipticIntegrals.compEllIntLogCoeff_zero`](DLMF/EllipticIntegrals/Asymptotics.lean#L48) (proved); [`DLMF.EllipticIntegrals.compEllIntLogCoeff_succ`](DLMF/EllipticIntegrals/Asymptotics.lean#L55) (proved).
- [19.12.E4](https://dlmf.nist.gov/19.12.E4): [`DLMF.EllipticIntegrals.compEllIntPik_isBigO_log`](DLMF/EllipticIntegrals/Asymptotics.lean#L109) (admitted).
- [19.12.E5](https://dlmf.nist.gov/19.12.E5): [`DLMF.EllipticIntegrals.compEllIntPik_isBigO_log_of_one_lt`](DLMF/EllipticIntegrals/Asymptotics.lean#L119) (admitted).
- [19.12.E6](https://dlmf.nist.gov/19.12.E6): [`DLMF.EllipticIntegrals.symEllIntRC_isBigO_small`](DLMF/EllipticIntegrals/Asymptotics.lean#L213) (proved).
- [19.12.E7](https://dlmf.nist.gov/19.12.E7): [`DLMF.EllipticIntegrals.symEllIntRC_isBigO_large`](DLMF/EllipticIntegrals/Asymptotics.lean#L255) (admitted).

Analytical prose:

- [19.12.p1](https://dlmf.nist.gov/19.12#p1): Digamma notation and the convergent expansions 19.12.1–19.12.3.
- [19.12.p2](https://dlmf.nist.gov/19.12#p2): Bibliographic pointer (Kaplan, Van de Vel, Karp–Sitnik) for `F(φ,k)`, `E(φ,k)` as `φ → π/2-`, `k → 1-`; no formula stated.
- [19.12.p3](https://dlmf.nist.gov/19.12#p3): Introduces 19.12.4–19.12.5 (`k² → 1-`).
- [19.12.p4](https://dlmf.nist.gov/19.12#p4): Bibliographic pointer (Karp et al. 2007) for `Π(φ, α², k)`; qualitative remark; no formula stated.
- [19.12.p5](https://dlmf.nist.gov/19.12#p5): Hypotheses `x ≥ 0`, `y > 0` of 19.12.6–19.12.7; the two-variable limits are filters on `ℝ × ℝ`.

## [§19.13 Integrals of Elliptic Integrals](https://dlmf.nist.gov/19.13)

No numbered equations; see the prose entries below.

Analytical prose:

- [19.13.i.p1](https://dlmf.nist.gov/19.13#i.p1): Bibliographic pointer (integrals of complete integrals with respect to the modulus); no formula stated.
- [19.13.i.p2](https://dlmf.nist.gov/19.13#i.p2): Bibliographic pointer (integrals of incomplete integrals); no formula stated.
- [19.13.ii.p1](https://dlmf.nist.gov/19.13#ii.p1): Bibliographic pointer (integration with respect to the amplitude, fractional integrals); no formula stated.
- [19.13.iii.p1](https://dlmf.nist.gov/19.13#iii.p1): Bibliographic pointer (Laplace transforms of `K`, `E`, `D`); no formula stated.

## [§19.14 Reduction of General Elliptic Integrals](https://dlmf.nist.gov/19.14)

- [19.14.E1](https://dlmf.nist.gov/19.14.E1): [`DLMF.EllipticIntegrals.integral_inv_sqrt_cube_sub_one`](DLMF/EllipticIntegrals/Reduction.lean#L41) (admitted).
- [19.14.E2](https://dlmf.nist.gov/19.14.E2): [`DLMF.EllipticIntegrals.integral_inv_sqrt_one_sub_cube`](DLMF/EllipticIntegrals/Reduction.lean#L51) (admitted).
- [19.14.E3](https://dlmf.nist.gov/19.14.E3): [`DLMF.EllipticIntegrals.integral_inv_sqrt_one_add_pow_four`](DLMF/EllipticIntegrals/Reduction.lean#L98) (proved).
- [19.14.E4](https://dlmf.nist.gov/19.14.E4): [`DLMF.EllipticIntegrals.integral_inv_sqrt_two_quadratics`](DLMF/EllipticIntegrals/Reduction.lean#L152) (admitted).
- [19.14.E5](https://dlmf.nist.gov/19.14.E5): [`DLMF.EllipticIntegrals.integral_inv_sqrt_two_quadratics`](DLMF/EllipticIntegrals/Reduction.lean#L152) (admitted).
- [19.14.E6](https://dlmf.nist.gov/19.14.E6): [`DLMF.EllipticIntegrals.integral_inv_sqrt_two_quadratics`](DLMF/EllipticIntegrals/Reduction.lean#L152) (admitted).
- [19.14.E7](https://dlmf.nist.gov/19.14.E7): [`DLMF.EllipticIntegrals.integral_inv_sqrt_two_quadratics_zero`](DLMF/EllipticIntegrals/Reduction.lean#L186) (proved from the admitted integral_inv_sqrt_two_quadratics (19.14.4)).
- [19.14.E8](https://dlmf.nist.gov/19.14.E8): [`DLMF.EllipticIntegrals.integral_inv_sqrt_two_quadratics_infty`](DLMF/EllipticIntegrals/Reduction.lean#L206) (admitted).
- [19.14.E9](https://dlmf.nist.gov/19.14.E9): [`DLMF.EllipticIntegrals.integral_inv_sqrt_two_quadratics_left`](DLMF/EllipticIntegrals/Reduction.lean#L223) (proved from the admitted integral_inv_sqrt_two_quadratics (19.14.4)).
- [19.14.E10](https://dlmf.nist.gov/19.14.E10): [`DLMF.EllipticIntegrals.integral_inv_sqrt_two_quadratics_right`](DLMF/EllipticIntegrals/Reduction.lean#L249) (proved from the admitted integral_inv_sqrt_two_quadratics (19.14.4)).

Analytical prose:

- [19.14.i.p1](https://dlmf.nist.gov/19.14#i.p1): Nonnegativity of the integrand and of `cos φ` in 19.14.1–19.14.3, giving the stated ranges of `x` (19.14.3 is proved for all real `x`, stronger than DLMF, with `φ = arccos((1-x²)/(1+x²)) = 2 arctan |x|`); the extension to `cos φ < 0` via 19.2.10 is a pointer.
- [19.14.i.p2](https://dlmf.nist.gov/19.14#i.p2): Hypotheses of 19.14.4 (`0 ≤ y < x`, positivity on `(y, x)`, the ordered permutation `α ≤ β ≤ γ` of `0, a₁b₂, a₂b₁`, not all 0), packaged as `ei19b_RedHyp`; introduces the four special cases.
- [19.14.i.p3](https://dlmf.nist.gov/19.14#i.p3): The special cases 19.14.7–19.14.10; the remark that they include 12 integrals of Abramowitz–Stegun is bibliographic.
- [19.14.ii.p1](https://dlmf.nist.gov/19.14#ii.p1): Legendre's theorem that every elliptic integral reduces to `F`, `E`, `Π` and elementary functions, and the reduction algorithms (Hermite reduction, Labahn–Mutrie, Byrd–Friedman, the 21 transformations, the example `(t(3-t)(4-t))^{-3/2}` on `[1,2]`): descriptive/algorithmic, not formalized (the symmetric-integral reduction theory is §19.29).


## Validation (part B)

- All five modules build with `lake build` (`autoImplicit=false`); no axioms, no
  `native_decide`, no `sorry` in helper declarations (prefix `ei19b_`).
- Admissions (`grep -c '\bsorry\b'`): Inequalities 13, Relations 0, Addition 7,
  Asymptotics 5, Reduction 4.
- `#print axioms` for a sample of proved statements (`incEllIntFk_eq_compEllIntKk_sub`,
  `incEllIntEk_eq_compEllIntEk_sub`, `ellipsePerimeter_eq`, `incEllIntPik_bounds`,
  `symEllIntRC_isBigO_small`, `compEllIntLogCoeff_succ`, `log_div_eq_mul_symEllIntRC`,
  `sinh_mul_symEllIntRC_eq_gudermannian`, `integral_inv_sqrt_one_add_pow_four`):
  `[propext, Classical.choice, Quot.sound]`.
- Every numbered formula of §§19.9–19.14 was checked numerically with mpmath before being stated.

## Numbered formulas and prose items (part C: §§19.15, 19.16, 19.18–19.22)

This part was acquired by ACQ19C on 2026-10-25 (DLMF version 1.2.8). It covers the symmetric-integral definitions and their bridges to the lean-codes Carlson library (§19.16), the permutation symmetry asserted in §19.15, derivatives and differential equations (§19.18), series (§19.19), special cases (§19.20), connection formulas (§19.21) and quadratic transformations (§19.22). §19.17 (graphics) is excluded. The modules are `DLMF.EllipticIntegrals.Symmetric`, `SymmetricSeries`, `SymmetricSpecialCases`, `SymmetricDerivatives`, `SymmetricConnection`, `SymmetricQuadratic` and `SymmetricCoverage`.

Of 113 numbered equation slots, 112 are in scope; 19.16.E3 is excluded because DLMF moved it to (19.23.6_5). All 112 in-scope IDs are covered by 142 tagged declarations: 10 definitions, 58 proved, 4 proved modulo admitted lemmas and 70 admitted. 41 IDs carry no admission, 9 are partly proved and 62 are admitted. Proof statuses come from a `#print axioms` audit. The 4 declarations proved modulo admitted lemmas all inherit the admitted R_G bridge 19.16.E17. The one Mathlib pointer is for 19.19.E4: `Multiset.prod_X_add_C_eq_sum_esymm` and `MvPolynomial.prod_C_add_X_eq_sum_esymm`, both recorded in `SymmetricCoverage.lean`. TauCeti has no coverage here.

Domains and conventions:

- `symEllIntRF`, `symEllIntRJ`, `symEllIntRG`, `symEllIntRD` and `symEllIntRC` take complex arguments and follow DLMF 19.16.1–19.16.5 and 19.2.17. Off the stated domains the Bochner integrals are totalized. R_J and R_C take the Cauchy principal value (`cauchyPVIoi`) when p or y is a negative real.
- `symEllIntR a b z` is lean-codes `Carlson.carlsonR (-a) b z` on the product slit plane. When a node lies on the cut or is 0 (§19.16(iii)), it is the limit from the slit domain. On the slit plane, the bridges `symEllIntRF_eq_carlsonRF`, `symEllIntRJ_eq_carlsonR`, `symEllIntRC_eq_carlsonRC` and `symEllIntRG_eq_carlsonRG` relate these definitions to the lean-codes ones. The first three are proved; the last is proved modulo 19.16.E17.
- **Corrected** (domain), 19.20.E3 and 19.20.E23: the printed identities fail for some complex arguments in the 19.16(i) domain. The independent check (2026-10-25) showed that the discrepancy factor is not a constant −i (at x = −1 + i, y = −1 + 2i it is +i for E3 and −i for E23; at x = −2 + 2i, y = 1.5 − 1.5i it is 0.945 + 0.328i and −0.541 + 0.841i), and that both formulas hold for Re x, Re y > 0. They are acquired for real x, y > 0 and, as corrected complex forms, for Re x, Re y > 0 (`symEllIntRF_lemniscatic_complex`, `symEllIntRD_lemniscatic_complex`). See DLMFErrata.md.
- Branch conditions not printed in DLMF are made explicit. 19.16.E11 requires ph λ + ph zⱼ ∈ (−π, π). 19.21.E4 and 19.21.E5 use `SignType.sign z.im`.
- The decimal values in 19.20.2 and 19.20.22 are excluded as numerical results; the exact identities are acquired.

## [§19.15 Advantages of Symmetry](https://dlmf.nist.gov/19.15)

Prose:

- [19.15.p1](https://dlmf.nist.gov/19.15#p1)–[19.15.p5](https://dlmf.nist.gov/19.15#p5): Advantages of symmetry (commentary). The permutation symmetry it asserts is acquired under the section tag `19.15`: `symEllIntRF_comm_left`, `symEllIntRF_comm_right`, `symEllIntRJ_comm_left`, `symEllIntRJ_comm_right`, `symEllIntRG_comm_left`, `symEllIntRG_comm_right` (all proved, in [Symmetric.lean](DLMF/EllipticIntegrals/Symmetric.lean)); the remaining remarks (simpler transformations, unified tables, numerical algorithms) are commentary.
- [19.15](https://dlmf.nist.gov/19.15): [`DLMF.EllipticIntegrals.symEllIntRF_comm_left`](DLMF/EllipticIntegrals/Symmetric.lean#L435) (proved); [`DLMF.EllipticIntegrals.symEllIntRF_comm_right`](DLMF/EllipticIntegrals/Symmetric.lean#L440) (proved); [`DLMF.EllipticIntegrals.symEllIntRG_comm_left`](DLMF/EllipticIntegrals/Symmetric.lean#L459) (proved); [`DLMF.EllipticIntegrals.symEllIntRG_comm_right`](DLMF/EllipticIntegrals/Symmetric.lean#L465) (proved); [`DLMF.EllipticIntegrals.symEllIntRJ_comm_left`](DLMF/EllipticIntegrals/Symmetric.lean#L445) (proved); [`DLMF.EllipticIntegrals.symEllIntRJ_comm_right`](DLMF/EllipticIntegrals/Symmetric.lean#L450) (proved).

## [§19.16 Definitions](https://dlmf.nist.gov/19.16)

- [19.16.E1](https://dlmf.nist.gov/19.16.E1): [`DLMF.EllipticIntegrals.symEllIntRF`](DLMF/EllipticIntegrals/Symmetric.lean#L106) (definition). Complex arguments; off `symEllIntRFDomain` the Bochner integral is totalized. Bridge to lean-codes `Carlson.carlsonRF` on the slit plane: `symEllIntRF_eq_carlsonRF`.
- [19.16.E2](https://dlmf.nist.gov/19.16.E2): [`DLMF.EllipticIntegrals.symEllIntRJ`](DLMF/EllipticIntegrals/Symmetric.lean#L113) (definition). R_G (19.16.E2_5) has its own line below. R_J takes the Cauchy principal value (`cauchyPVIoi`) when p is a negative real. Bridge `symEllIntRJ_eq_carlsonR`.
- [19.16.E3](https://dlmf.nist.gov/19.16.E3): excluded: moved (DLMF: "Moved to (19.23.6_5)"; see §19.23).
- [19.16.E4](https://dlmf.nist.gov/19.16.E4): [`DLMF.EllipticIntegrals.symEllIntS`](DLMF/EllipticIntegrals/Symmetric.lean#L101) (definition). Principal square roots.
- [19.16.E5](https://dlmf.nist.gov/19.16.E5): [`DLMF.EllipticIntegrals.symEllIntRD`](DLMF/EllipticIntegrals/Symmetric.lean#L132) (definition); [`DLMF.EllipticIntegrals.symEllIntRD_eq_integral`](DLMF/EllipticIntegrals/Symmetric.lean#L408) (proved).
- [19.16.E6](https://dlmf.nist.gov/19.16.E6): [`DLMF.EllipticIntegrals.symEllIntRC_eq_symEllIntRF`](DLMF/EllipticIntegrals/Symmetric.lean#L415) (proved). Stronger than DLMF: for all x, y (both sides are the same integral or principal value).
- [19.16.E7](https://dlmf.nist.gov/19.16.E7): [`DLMF.EllipticIntegrals.symEllIntRJ_eq_hyperelliptic`](DLMF/EllipticIntegrals/Symmetric.lean#L423) (proved).
- [19.16.E8](https://dlmf.nist.gov/19.16.E8): [`DLMF.EllipticIntegrals.symEllIntR`](DLMF/EllipticIntegrals/Symmetric.lean#L145) (definition); [`DLMF.EllipticIntegrals.symEllIntR_comp_perm`](DLMF/EllipticIntegrals/Symmetric.lean#L471) (proved). Defined as lean-codes `Carlson.carlsonR (-a) b z` on the product slit plane, else the limit from the slit domain.
- [19.16.E9](https://dlmf.nist.gov/19.16.E9): [`DLMF.EllipticIntegrals.symEllIntR_eq_integral`](DLMF/EllipticIntegrals/Symmetric.lean#L202) (proved). Stronger than DLMF: complex a, b with Re a > 0, Re a' > 0.
- [19.16.E10](https://dlmf.nist.gov/19.16.E10): [`DLMF.EllipticIntegrals.symEllIntRConj`](DLMF/EllipticIntegrals/Symmetric.lean#L226) (definition).
- [19.16.E11](https://dlmf.nist.gov/19.16.E11): [`DLMF.EllipticIntegrals.symEllIntR_mul`](DLMF/EllipticIntegrals/Symmetric.lean#L484) (proved); [`DLMF.EllipticIntegrals.symEllIntR_const`](DLMF/EllipticIntegrals/Symmetric.lean#L504) (proved). Homogeneity with the branch condition made explicit (λ, zⱼ in the slit plane, ph λ + ph zⱼ ∈ (−π, π); DLMF states none, automatic for λ > 0) and R_{-a}(𝐛; x𝟏) = x^{-a}.
- [19.16.E12](https://dlmf.nist.gov/19.16.E12): [`DLMF.EllipticIntegrals.symEllIntR_four_eq_integral_sin`](DLMF/EllipticIntegrals/Symmetric.lean#L586) (admitted). Also covers 19.16.E13.
- [19.16.E13](https://dlmf.nist.gov/19.16.E13): [`DLMF.EllipticIntegrals.symEllIntR_four_eq_integral_sin`](DLMF/EllipticIntegrals/Symmetric.lean#L586) (admitted).
- [19.16.E14](https://dlmf.nist.gov/19.16.E14): [`DLMF.EllipticIntegrals.symEllIntRF_eq_symEllIntR`](DLMF/EllipticIntegrals/Symmetric.lean#L245) (proved). Slit-plane arguments.
- [19.16.E15](https://dlmf.nist.gov/19.16.E15): [`DLMF.EllipticIntegrals.symEllIntRD_eq_symEllIntR`](DLMF/EllipticIntegrals/Symmetric.lean#L305) (proved).
- [19.16.E16](https://dlmf.nist.gov/19.16.E16): [`DLMF.EllipticIntegrals.symEllIntRJ_eq_symEllIntR`](DLMF/EllipticIntegrals/Symmetric.lean#L279) (proved).
- [19.16.E17](https://dlmf.nist.gov/19.16.E17): [`DLMF.EllipticIntegrals.symEllIntRG_eq_symEllIntR`](DLMF/EllipticIntegrals/Symmetric.lean#L568) (proved).
- [19.16.E18](https://dlmf.nist.gov/19.16.E18): [`DLMF.EllipticIntegrals.symEllIntRC_eq_symEllIntR`](DLMF/EllipticIntegrals/Symmetric.lean#L324) (proved).
- [19.16.E19](https://dlmf.nist.gov/19.16.E19): [`DLMF.EllipticIntegrals.symEllIntR_cons_zero`](DLMF/EllipticIntegrals/Symmetric.lean#L604) (admitted).
- [19.16.E20](https://dlmf.nist.gov/19.16.E20): [`DLMF.EllipticIntegrals.symEllIntRF_zero_left`](DLMF/EllipticIntegrals/Symmetric.lean#L349) (proved).
- [19.16.E21](https://dlmf.nist.gov/19.16.E21): [`DLMF.EllipticIntegrals.symEllIntRD_zero_left`](DLMF/EllipticIntegrals/Symmetric.lean#L366) (proved).
- [19.16.E22](https://dlmf.nist.gov/19.16.E22): [`DLMF.EllipticIntegrals.symEllIntRJ_zero_left`](DLMF/EllipticIntegrals/Symmetric.lean#L385) (proved).
- [19.16.E23](https://dlmf.nist.gov/19.16.E23): [`DLMF.EllipticIntegrals.symEllIntRG_zero_left`](DLMF/EllipticIntegrals/Symmetric.lean#L635) (proved).
- [19.16.E24](https://dlmf.nist.gov/19.16.E24): [`DLMF.EllipticIntegrals.symEllIntR_eq_integral_complete`](DLMF/EllipticIntegrals/Symmetric.lean#L657) (admitted).
Prose:

- [19.16.i.p1](https://dlmf.nist.gov/19.16#i.p1): domain of the integrals: `symEllIntArg`, `symEllIntRFDomain` (definitions, tag `19.16.i`); principal value for p < 0 in `symEllIntRJ`; normalizations R_F(1,1,1) = R_J(1,1,1,1) = 1: `symEllIntRF_one_one_one`, `symEllIntRJ_one_one_one_one` (proved); R_G(1,1,1) = 1 is a consequence of 19.20.E4.
- [19.16.i.p2](https://dlmf.nist.gov/19.16#i.p2), [19.16.i.p3](https://dlmf.nist.gov/19.16#i.p3): introduce 19.16.E5–E7.
- [19.16.ii.p1](https://dlmf.nist.gov/19.16#ii.p1), [19.16.ii.p2](https://dlmf.nist.gov/19.16#ii.p2): the conditions on a, 𝐛, 𝐳 are recorded in the docstrings of `symEllIntR` and `symEllIntR_eq_integral`.
- [19.16.ii.p3](https://dlmf.nist.gov/19.16#ii.p3): bibliographic (earlier notation R(a; 𝐛; 𝐳)); recorded in the `symEllIntR` docstring.
- [19.16.iii.p1](https://dlmf.nist.gov/19.16#iii.p1): classification terminology (complete/incomplete, symmetric cases); not formalized.
- [19.16.iii.p2](https://dlmf.nist.gov/19.16#iii.p2), [19.16.iii.p3](https://dlmf.nist.gov/19.16#iii.p3): introduce 19.16.E14–E24; the zero-argument convention is the limit from the slit domain in `symEllIntR`.
- [19.16.E2_5](https://dlmf.nist.gov/19.16.E2_5): [`DLMF.EllipticIntegrals.symEllIntRG`](DLMF/EllipticIntegrals/Symmetric.lean#L124) (definition).
- [19.16.i](https://dlmf.nist.gov/19.16.i): [`DLMF.EllipticIntegrals.symEllIntArg`](DLMF/EllipticIntegrals/Symmetric.lean#L76) (definition); [`DLMF.EllipticIntegrals.symEllIntRFDomain`](DLMF/EllipticIntegrals/Symmetric.lean#L81) (definition); [`DLMF.EllipticIntegrals.symEllIntRF_one_one_one`](DLMF/EllipticIntegrals/Symmetric.lean#L515) (proved); [`DLMF.EllipticIntegrals.symEllIntRJ_one_one_one_one`](DLMF/EllipticIntegrals/Symmetric.lean#L521) (proved).

## [§19.18 Derivatives and Differential Equations](https://dlmf.nist.gov/19.18)

- [19.18.E1](https://dlmf.nist.gov/19.18.E1): [`DLMF.EllipticIntegrals.hasDerivAt_symEllIntRF_right`](DLMF/EllipticIntegrals/SymmetricDerivatives.lean#L218) (proved).
- [19.18.E2](https://dlmf.nist.gov/19.18.E2): [`DLMF.EllipticIntegrals.hasDerivAt_symEllIntRG_translate`](DLMF/EllipticIntegrals/SymmetricDerivatives.lean#L210) (proved modulo admitted lemmas).
- [19.18.E3](https://dlmf.nist.gov/19.18.E3): [`DLMF.EllipticIntegrals.hasDerivAt_symEllIntR_update`](DLMF/EllipticIntegrals/SymmetricDerivatives.lean#L59) (proved). With 19.18.E4 (∂/∂zⱼ form).
- [19.18.E4](https://dlmf.nist.gov/19.18.E4): [`DLMF.EllipticIntegrals.hasDerivAt_symEllIntR_update`](DLMF/EllipticIntegrals/SymmetricDerivatives.lean#L59) (proved).
- [19.18.E5](https://dlmf.nist.gov/19.18.E5): [`DLMF.EllipticIntegrals.mul_partialDeriv_add_symEllIntR`](DLMF/EllipticIntegrals/SymmetricDerivatives.lean#L111) (proved).
- [19.18.E6](https://dlmf.nist.gov/19.18.E6): [`DLMF.EllipticIntegrals.hasDerivAt_symEllIntRF_translate`](DLMF/EllipticIntegrals/SymmetricDerivatives.lean#L258) (proved).
- [19.18.E7](https://dlmf.nist.gov/19.18.E7): [`DLMF.EllipticIntegrals.hasDerivAt_symEllIntRG_translate_zero`](DLMF/EllipticIntegrals/SymmetricDerivatives.lean#L265) (proved modulo admitted lemmas).
- [19.18.E8](https://dlmf.nist.gov/19.18.E8): [`DLMF.EllipticIntegrals.hasDerivAt_symEllIntR_translate`](DLMF/EllipticIntegrals/SymmetricDerivatives.lean#L72) (proved).
- [19.18.E9](https://dlmf.nist.gov/19.18.E9): [`DLMF.EllipticIntegrals.sum_mul_partialDeriv_symEllIntRF`](DLMF/EllipticIntegrals/SymmetricDerivatives.lean#L304) (proved).
- [19.18.E10](https://dlmf.nist.gov/19.18.E10): [`DLMF.EllipticIntegrals.eulerPoisson_symEllIntRF`](DLMF/EllipticIntegrals/SymmetricDerivatives.lean#L316) (proved).
- [19.18.E11](https://dlmf.nist.gov/19.18.E11): [`DLMF.EllipticIntegrals.sum_mul_partialDeriv_symEllIntR`](DLMF/EllipticIntegrals/SymmetricDerivatives.lean#L96) (proved).
- [19.18.E12](https://dlmf.nist.gov/19.18.E12): [`DLMF.EllipticIntegrals.eulerPoisson_symEllIntR'`](DLMF/EllipticIntegrals/SymmetricDerivatives.lean#L183) (proved). Second form of the Euler–Poisson system; the first form 19.18.E13 is proved.
- [19.18.E13](https://dlmf.nist.gov/19.18.E13): [`DLMF.EllipticIntegrals.eulerPoisson_symEllIntR`](DLMF/EllipticIntegrals/SymmetricDerivatives.lean#L148) (proved).
- [19.18.E14](https://dlmf.nist.gov/19.18.E14): [`DLMF.EllipticIntegrals.eulerPoissonDarboux_symEllIntR`](DLMF/EllipticIntegrals/SymmetricDerivatives.lean#L385) (proved). PDE checked numerically with mpmath.
- [19.18.E15](https://dlmf.nist.gov/19.18.E15): [`DLMF.EllipticIntegrals.wave_symEllIntR`](DLMF/EllipticIntegrals/SymmetricDerivatives.lean#L436) (admitted). PDE checked numerically with mpmath.
- [19.18.E16](https://dlmf.nist.gov/19.18.E16): [`DLMF.EllipticIntegrals.axialPotential_symEllIntR`](DLMF/EllipticIntegrals/SymmetricDerivatives.lean#L448) (proved). PDE checked numerically with mpmath.
- [19.18.E17](https://dlmf.nist.gov/19.18.E17): [`DLMF.EllipticIntegrals.laplace_symEllIntR`](DLMF/EllipticIntegrals/SymmetricDerivatives.lean#L498) (admitted). PDE checked numerically with mpmath.
Prose:

- [19.18.i.p1](https://dlmf.nist.gov/19.18#i.p1), [19.18.ii.p1](https://dlmf.nist.gov/19.18#ii.p1)–[19.18.ii.p4](https://dlmf.nist.gov/19.18#ii.p4): introduce the formulas; the operator definitions are in `DLMF.EllipticIntegrals.symEllIntRFVec`, `symEllIntRGVec` and lean-codes `Dirichlet.carlsonEulerPoissonOperator`.

## [§19.19 Taylor and Related Series](https://dlmf.nist.gov/19.19)

- [19.19.E1](https://dlmf.nist.gov/19.19.E1): [`DLMF.EllipticIntegrals.symEllIntT`](DLMF/EllipticIntegrals/SymmetricSeries.lean#L42) (definition).
- [19.19.E2](https://dlmf.nist.gov/19.19.E2): [`DLMF.EllipticIntegrals.symEllIntR_hasSum_T`](DLMF/EllipticIntegrals/SymmetricSeries.lean#L64) (proved). HasSum form; 0 < Re c assumed so that (c)_N ≠ 0.
- [19.19.E3](https://dlmf.nist.gov/19.19.E3): [`DLMF.EllipticIntegrals.symEllIntR_hasSum_T_last`](DLMF/EllipticIntegrals/SymmetricSeries.lean#L188) (proved).
- [19.19.E4](https://dlmf.nist.gov/19.19.E4): [`DLMF.EllipticIntegrals.prod_one_add_mul_eq_sum_symEllIntE`](DLMF/EllipticIntegrals/SymmetricSeries.lean#L53) (proved); `Multiset.prod_X_add_C_eq_sum_esymm` (Mathlib, upstream pointer); `MvPolynomial.prod_C_add_X_eq_sum_esymm` (Mathlib, upstream pointer). Proved by grouping the powerset expansion by cardinality; the polynomial form is in Mathlib.
- [19.19.E5](https://dlmf.nist.gov/19.19.E5): [`DLMF.EllipticIntegrals.symEllIntT_half`](DLMF/EllipticIntegrals/SymmetricSeries.lean#L232) (admitted).
- [19.19.E6](https://dlmf.nist.gov/19.19.E6): [`DLMF.EllipticIntegrals.symEllIntRJ_eq_symEllIntR_five`](DLMF/EllipticIntegrals/SymmetricSeries.lean#L243) (proved).
- [19.19.E7](https://dlmf.nist.gov/19.19.E7): [`DLMF.EllipticIntegrals.symEllIntR_half_hasSum_mean`](DLMF/EllipticIntegrals/SymmetricSeries.lean#L266) (admitted).
- [19.19.E8](https://dlmf.nist.gov/19.19.E8): [`DLMF.EllipticIntegrals.symEllIntR_half_hasSum_mean`](DLMF/EllipticIntegrals/SymmetricSeries.lean#L266) (admitted); [`DLMF.EllipticIntegrals.symEllIntE_one_mean`](DLMF/EllipticIntegrals/SymmetricSeries.lean#L278) (proved).
Prose:

- [19.19.p1](https://dlmf.nist.gov/19.19#p1), [19.19.p2](https://dlmf.nist.gov/19.19#p2), [19.19.p4](https://dlmf.nist.gov/19.19#p4), [19.19.p6](https://dlmf.nist.gov/19.19#p6): introduce 19.19.E1–E8 (conditions in the docstrings).
- [19.19.p3](https://dlmf.nist.gov/19.19#p3): for n = 2, (19.19.3) is a Gauss series; commentary.
- [19.19.p5](https://dlmf.nist.gov/19.19#p5): remark on the number of terms of T_N(½, 𝐙); computational, not formalized.

## [§19.20 Special Cases](https://dlmf.nist.gov/19.20)

- [19.20.E1](https://dlmf.nist.gov/19.20.E1): [`DLMF.EllipticIntegrals.symEllIntRF_self`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L58) (proved); [`DLMF.EllipticIntegrals.symEllIntRF_smul`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L63) (proved); [`DLMF.EllipticIntegrals.symEllIntRF_self_right`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L75) (proved); [`DLMF.EllipticIntegrals.symEllIntRF_zero_self`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L82) (proved); [`DLMF.EllipticIntegrals.not_integrableOn_symEllIntRF_zero_zero`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L91) (proved). x = y = z, λ > 0 scaling, R_F(x,y,y) = R_C(x,y) and R_F(0,y,y) = π/(2√y) proved; R_F(0,0,z) = ∞ as non-integrability (admitted). The decimal value of the lemniscate constant in 19.20.2 is excluded: numerical.
- [19.20.E2](https://dlmf.nist.gov/19.20.E2): [`DLMF.EllipticIntegrals.lemniscate_first_symEllIntRF`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L97) (proved). Exact identity only; the decimal value is excluded: numerical.
- [19.20.E3](https://dlmf.nist.gov/19.20.E3): [`DLMF.EllipticIntegrals.symEllIntRF_lemniscatic`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L106) (admitted). **Corrected** (domain): stated for real x, y > 0, and for complex x, y with Re x, Re y > 0 by `symEllIntRF_lemniscatic_complex`; the printed identity fails elsewhere in the 19.16(i) domain (see corrections); [`DLMF.EllipticIntegrals.symEllIntRF_lemniscatic_complex`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L114) (admitted).
- [19.20.E4](https://dlmf.nist.gov/19.20.E4): [`DLMF.EllipticIntegrals.symEllIntRG_self`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L115) (proved modulo admitted lemmas); [`DLMF.EllipticIntegrals.symEllIntRG_smul`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L123) (proved modulo admitted lemmas); [`DLMF.EllipticIntegrals.symEllIntRG_zero_self`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L198) (proved). Proved modulo the admitted R_G bridge 19.16.E17.
- [19.20.E5](https://dlmf.nist.gov/19.20.E5): [`DLMF.EllipticIntegrals.two_mul_symEllIntRG_self_right`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L226) (proved).
- [19.20.E6](https://dlmf.nist.gov/19.20.E6): [`DLMF.EllipticIntegrals.symEllIntRJ_self`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L239) (proved); [`DLMF.EllipticIntegrals.symEllIntRJ_smul`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L250) (proved); [`DLMF.EllipticIntegrals.symEllIntRJ_self_right`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L265) (proved); [`DLMF.EllipticIntegrals.not_integrableOn_symEllIntRJ_zero_zero`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L269) (proved); [`DLMF.EllipticIntegrals.symEllIntRJ_self_self_self`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L276) (proved); [`DLMF.EllipticIntegrals.symEllIntRJ_self_self_self_eq`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L287) (proved). R_J(x,x,x,x), scaling and R_J(x,y,z,z) = R_D(x,y,z) proved; ∞ case as non-integrability (admitted).
- [19.20.E7](https://dlmf.nist.gov/19.20.E7): [`DLMF.EllipticIntegrals.tendsto_symEllIntRJ_zero`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L297) (admitted).
- [19.20.E8](https://dlmf.nist.gov/19.20.E8): [`DLMF.EllipticIntegrals.symEllIntRJ_self_right`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L265) (proved); [`DLMF.EllipticIntegrals.symEllIntRJ_zero_self_self`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L304) (proved); [`DLMF.EllipticIntegrals.symEllIntRJ_zero_self_self_neg`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L350) (admitted); [`DLMF.EllipticIntegrals.symEllIntRJ_self_right_eq`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L357) (proved); [`DLMF.EllipticIntegrals.symEllIntRJ_self_right_eq_of_neg`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L365) (admitted).
- [19.20.E9](https://dlmf.nist.gov/19.20.E9): [`DLMF.EllipticIntegrals.symEllIntRJ_zero_sqrt`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L371) (admitted).
- [19.20.E10](https://dlmf.nist.gov/19.20.E10): [`DLMF.EllipticIntegrals.tendsto_symEllIntRJ_zero_left`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L381) (admitted).
- [19.20.E11](https://dlmf.nist.gov/19.20.E11): [`DLMF.EllipticIntegrals.symEllIntRJ_zero_asymptotic`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L393) (admitted).
- [19.20.E12](https://dlmf.nist.gov/19.20.E12): [`DLMF.EllipticIntegrals.tendsto_mul_symEllIntRJ`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L401) (admitted).
- [19.20.E13](https://dlmf.nist.gov/19.20.E13): [`DLMF.EllipticIntegrals.symEllIntRJ_special_p`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L409) (admitted).
- [19.20.E14](https://dlmf.nist.gov/19.20.E14): [`DLMF.EllipticIntegrals.symEllIntRJ_principalValue`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L421) (admitted).
- [19.20.E15](https://dlmf.nist.gov/19.20.E15): [`DLMF.EllipticIntegrals.symEllIntRJ_principalValue`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L421) (admitted).
- [19.20.E16](https://dlmf.nist.gov/19.20.E16): [`DLMF.EllipticIntegrals.symEllIntRJ_principalValue_p`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L435) (proved).
- [19.20.E17](https://dlmf.nist.gov/19.20.E17): [`DLMF.EllipticIntegrals.symEllIntRJ_principalValue_complete`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L446) (admitted).
- [19.20.E18](https://dlmf.nist.gov/19.20.E18): [`DLMF.EllipticIntegrals.symEllIntRD_self`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L457) (proved); [`DLMF.EllipticIntegrals.symEllIntRD_smul`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L462) (proved); [`DLMF.EllipticIntegrals.symEllIntRD_zero_self`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L469) (proved); [`DLMF.EllipticIntegrals.not_integrableOn_symEllIntRD_zero_zero`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L478) (proved).
- [19.20.E19](https://dlmf.nist.gov/19.20.E19): [`DLMF.EllipticIntegrals.symEllIntRD_isEquivalent_zero`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L484) (admitted).
- [19.20.E20](https://dlmf.nist.gov/19.20.E20): [`DLMF.EllipticIntegrals.symEllIntRD_self_right`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L492) (proved).
- [19.20.E21](https://dlmf.nist.gov/19.20.E21): [`DLMF.EllipticIntegrals.symEllIntRD_self_left`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L508) (proved).
- [19.20.E22](https://dlmf.nist.gov/19.20.E22): [`DLMF.EllipticIntegrals.lemniscate_second_symEllIntRD`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L515) (proved). Exact identity only; the decimal value is excluded: numerical.
- [19.20.E23](https://dlmf.nist.gov/19.20.E23): [`DLMF.EllipticIntegrals.symEllIntRD_lemniscatic`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L549) (admitted). **Corrected** (domain): stated for real x, y > 0, and for Re x, Re y > 0 by `symEllIntRD_lemniscatic_complex`, as 19.20.E3; [`DLMF.EllipticIntegrals.symEllIntRD_lemniscatic_complex`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L557) (admitted).
- [19.20.E24](https://dlmf.nist.gov/19.20.E24): [`DLMF.EllipticIntegrals.symEllIntR_zero`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L569) (proved); [`DLMF.EllipticIntegrals.symEllIntR_neg_natCast`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L580) (admitted). R_0 = 1 proved; the R_{-n} polynomial form admitted.
- [19.20.E25](https://dlmf.nist.gov/19.20.E25): [`DLMF.EllipticIntegrals.symEllIntR_sum`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L589) (proved).
- [19.20.E26](https://dlmf.nist.gov/19.20.E26): [`DLMF.EllipticIntegrals.symEllIntR_euler`](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L602) (proved). Euler's integral, via lean-codes `Carlson.R.EulerTransform`.
Prose:

- [19.20.i.p1](https://dlmf.nist.gov/19.20#i.p1), [19.20.i.p2](https://dlmf.nist.gov/19.20#i.p2), [19.20.ii.p1](https://dlmf.nist.gov/19.20#ii.p1), [19.20.iii.p1](https://dlmf.nist.gov/19.20#iii.p1), [19.20.iii.p2](https://dlmf.nist.gov/19.20#iii.p2), [19.20.iv.p1](https://dlmf.nist.gov/19.20#iv.p1), [19.20.iv.p2](https://dlmf.nist.gov/19.20#iv.p2), [19.20.v.p1](https://dlmf.nist.gov/19.20#v.p1): introduce the special cases; their conditions are in the docstrings. Decimal values of the lemniscate constants (19.20.2, 19.20.22) are excluded: numerical.

## [§19.21 Connection Formulas](https://dlmf.nist.gov/19.21)

- [19.21.E1](https://dlmf.nist.gov/19.21.E1): [`DLMF.EllipticIntegrals.legendreRelation_symEllInt`](DLMF/EllipticIntegrals/SymmetricConnection.lean#L36) (admitted); [`DLMF.EllipticIntegrals.lemniscate_product`](DLMF/EllipticIntegrals/SymmetricConnection.lean#L44) (proved). With the lemniscate product form.
- [19.21.E2](https://dlmf.nist.gov/19.21.E2): [`DLMF.EllipticIntegrals.symEllIntRF_zero_eq_symEllIntRD`](DLMF/EllipticIntegrals/SymmetricConnection.lean#L50) (proved).
- [19.21.E3](https://dlmf.nist.gov/19.21.E3): [`DLMF.EllipticIntegrals.symEllIntRG_zero_eq`](DLMF/EllipticIntegrals/SymmetricConnection.lean#L58) (proved).
- [19.21.E4](https://dlmf.nist.gov/19.21.E4): [`DLMF.EllipticIntegrals.symEllIntRF_zero_connection`](DLMF/EllipticIntegrals/SymmetricConnection.lean#L72) (admitted). Uses `SignType.sign z.im` for the branch.
- [19.21.E5](https://dlmf.nist.gov/19.21.E5): [`DLMF.EllipticIntegrals.symEllIntRG_zero_connection`](DLMF/EllipticIntegrals/SymmetricConnection.lean#L80) (admitted). Uses `SignType.sign z.im` for the branch.
- [19.21.E6](https://dlmf.nist.gov/19.21.E6): [`DLMF.EllipticIntegrals.symEllIntRJ_zero_eq_RF_RD`](DLMF/EllipticIntegrals/SymmetricConnection.lean#L90) (admitted).
- [19.21.E7](https://dlmf.nist.gov/19.21.E7): [`DLMF.EllipticIntegrals.symEllIntRD_move`](DLMF/EllipticIntegrals/SymmetricConnection.lean#L104) (proved).
- [19.21.E8](https://dlmf.nist.gov/19.21.E8): [`DLMF.EllipticIntegrals.symEllIntRD_cyclic_sum`](DLMF/EllipticIntegrals/SymmetricConnection.lean#L113) (proved).
- [19.21.E9](https://dlmf.nist.gov/19.21.E9): [`DLMF.EllipticIntegrals.symEllIntRD_cyclic_mul_sum`](DLMF/EllipticIntegrals/SymmetricConnection.lean#L121) (proved); [`DLMF.EllipticIntegrals.p19sR1_symEllIntRD_cyclic_mul_sum`](DLMF/EllipticIntegrals/P19sR1Connection.lean#L190) (proved).
- [19.21.E10](https://dlmf.nist.gov/19.21.E10): [`DLMF.EllipticIntegrals.two_mul_symEllIntRG_eq`](DLMF/EllipticIntegrals/SymmetricConnection.lean#L129) (proved); [`DLMF.EllipticIntegrals.p19sR1_two_mul_symEllIntRG`](DLMF/EllipticIntegrals/Symmetric.lean#L533) (proved).
- [19.21.E11](https://dlmf.nist.gov/19.21.E11): [`DLMF.EllipticIntegrals.six_mul_symEllIntRG_eq`](DLMF/EllipticIntegrals/SymmetricConnection.lean#L138) (proved).
- [19.21.E12](https://dlmf.nist.gov/19.21.E12): [`DLMF.EllipticIntegrals.symEllIntRJ_change_parameter`](DLMF/EllipticIntegrals/SymmetricConnection.lean#L153) (admitted).
- [19.21.E13](https://dlmf.nist.gov/19.21.E13): [`DLMF.EllipticIntegrals.symEllIntRJ_change_parameter`](DLMF/EllipticIntegrals/SymmetricConnection.lean#L153) (admitted).
- [19.21.E14](https://dlmf.nist.gov/19.21.E14): [`DLMF.EllipticIntegrals.symEllIntRJ_change_parameter_identities`](DLMF/EllipticIntegrals/SymmetricConnection.lean#L165) (proved). Algebraic identities among the changed parameters (proved).
- [19.21.E15](https://dlmf.nist.gov/19.21.E15): [`DLMF.EllipticIntegrals.symEllIntRJ_change_parameter_zero`](DLMF/EllipticIntegrals/SymmetricConnection.lean#L182) (admitted).
Prose:

- [19.21.i.p1](https://dlmf.nist.gov/19.21#i.p1)–[19.21.i.p3](https://dlmf.nist.gov/19.21#i.p3), [19.21.ii.p1](https://dlmf.nist.gov/19.21#ii.p1), [19.21.iii.p1](https://dlmf.nist.gov/19.21#iii.p1), [19.21.iii.p2](https://dlmf.nist.gov/19.21#iii.p2): introduce 19.21.E1–E15 with their conditions (docstrings).
- [19.21.ii.p2](https://dlmf.nist.gov/19.21#ii.p2): bibliographic; not formalized.

## [§19.22 Quadratic Transformations](https://dlmf.nist.gov/19.22)

- [19.22.E1](https://dlmf.nist.gov/19.22.E1): [`DLMF.EllipticIntegrals.symEllIntRF_zero_sq`](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L74) (proved).
- [19.22.E2](https://dlmf.nist.gov/19.22.E2): [`DLMF.EllipticIntegrals.symEllIntRG_zero_sq`](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L109) (proved).
- [19.22.E3](https://dlmf.nist.gov/19.22.E3): [`DLMF.EllipticIntegrals.symEllIntRD_zero_sq`](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L125) (proved).
- [19.22.E4](https://dlmf.nist.gov/19.22.E4): [`DLMF.EllipticIntegrals.symEllIntRJ_zero_sq`](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L158) (admitted).
- [19.22.E5](https://dlmf.nist.gov/19.22.E5): [`DLMF.EllipticIntegrals.symEllIntRJ_zero_sq`](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L158) (admitted).
- [19.22.E6](https://dlmf.nist.gov/19.22.E6): [`DLMF.EllipticIntegrals.symEllIntPm_mul_add`](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L170) (proved); [`DLMF.EllipticIntegrals.symEllIntPm_sub_real`](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L183) (proved). Complex first two equations; the last two for real arguments.
- [19.22.E7](https://dlmf.nist.gov/19.22.E7): [`DLMF.EllipticIntegrals.symEllIntRJ_zero_sq_bartky`](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L214) (admitted).
- [19.22.E8](https://dlmf.nist.gov/19.22.E8): [`DLMF.EllipticIntegrals.symEllIntRF_zero_eq_inv_agm`](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L226) (proved). Via `NNReal.agm` (lean-codes Carlson AGM).
- [19.22.E9](https://dlmf.nist.gov/19.22.E9): [`DLMF.EllipticIntegrals.symEllIntRG_zero_agm`](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L281) (proved).
- [19.22.E10](https://dlmf.nist.gov/19.22.E10): [`DLMF.EllipticIntegrals.symEllIntRD_zero_agm`](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L442) (proved).
- [19.22.E11](https://dlmf.nist.gov/19.22.E11): [`DLMF.EllipticIntegrals.symEllIntRD_zero_agm`](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L442) (proved); [`DLMF.EllipticIntegrals.agmQ_sign`](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L520) (proved).
- [19.22.E12](https://dlmf.nist.gov/19.22.E12): [`DLMF.EllipticIntegrals.symEllIntRJ_zero_agm`](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L589) (admitted).
- [19.22.E13](https://dlmf.nist.gov/19.22.E13): [`DLMF.EllipticIntegrals.symEllIntRJ_zero_agm`](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L589) (admitted); [`DLMF.EllipticIntegrals.tendsto_agmP`](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L668) (proved).
- [19.22.E14](https://dlmf.nist.gov/19.22.E14): [`DLMF.EllipticIntegrals.symEllIntRJ_zero_agm_neg`](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L709) (admitted).
- [19.22.E15](https://dlmf.nist.gov/19.22.E15): [`DLMF.EllipticIntegrals.symEllIntRJ_zero_agm_neg`](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L709) (admitted).
- [19.22.E16](https://dlmf.nist.gov/19.22.E16): [`DLMF.EllipticIntegrals.symEllIntRF_sq_landen`](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L723) (admitted).
- [19.22.E17](https://dlmf.nist.gov/19.22.E17): [`DLMF.EllipticIntegrals.symEllIntPm_mul_add_z`](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L773) (proved).
- [19.22.E18](https://dlmf.nist.gov/19.22.E18): [`DLMF.EllipticIntegrals.symEllIntRF_sq_landen`](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L723) (admitted); [`DLMF.EllipticIntegrals.symEllIntRF_sq_landen_real`](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L731) (proved); [`DLMF.EllipticIntegrals.symEllIntRF_sq_landen_conj`](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L753) (proved). Real case proved (Landen); the complex and conjugate cases admitted.
- [19.22.E19](https://dlmf.nist.gov/19.22.E19): [`DLMF.EllipticIntegrals.symEllIntRD_sq_landen`](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L781) (admitted).
- [19.22.E20](https://dlmf.nist.gov/19.22.E20): [`DLMF.EllipticIntegrals.symEllIntRJ_sq_landen`](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L792) (admitted).
- [19.22.E21](https://dlmf.nist.gov/19.22.E21): [`DLMF.EllipticIntegrals.symEllIntRG_sq_landen`](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L805) (admitted).
- [19.22.E22](https://dlmf.nist.gov/19.22.E22): [`DLMF.EllipticIntegrals.symEllIntRC_sq`](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L814) (proved).
- [19.22.E23](https://dlmf.nist.gov/19.22.E23): [`DLMF.EllipticIntegrals.symEllIntPm_inverse`](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L824) (proved); [`DLMF.EllipticIntegrals.symEllIntPm_inverse_sub_real`](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L834) (admitted).
Prose:

- [19.22.i.p1](https://dlmf.nist.gov/19.22#i.p1), [19.22.ii.p1](https://dlmf.nist.gov/19.22#ii.p1), [19.22.iii.p1](https://dlmf.nist.gov/19.22#iii.p1): introduce the formulas (conditions in the docstrings).
- [19.22.iii.p2](https://dlmf.nist.gov/19.22#iii.p2)–[19.22.iii.p4](https://dlmf.nist.gov/19.22#iii.p4): commentary on Landen/Gauss transformations and their history; not formalized.

## Validation (part C)

- All seven modules build with `lake build` (`autoImplicit=false`; strict `lake env lean` has no
  warnings other than `sorry`). There are no axioms and no `native_decide`, and no helper
  declaration (prefix `ei19c_`) contains `sorry`. One helper, `ei19c_RGVec_eventuallyEq`,
  inherits the admitted 19.16.E17.
- Admissions (`grep -c '\bsorry\b'`): Symmetric 5, SymmetricSeries 4, SymmetricSpecialCases 26,
  SymmetricDerivatives 5, SymmetricConnection 14, SymmetricQuadratic 16, SymmetricCoverage 0.
- `#print axioms` was run on all 97 proved declarations. 91 depend only on
  `[propext, Classical.choice, Quot.sound]`. The other 6 also depend on `sorryAx` through
  19.16.E17: `symEllIntRG_eq_carlsonRG`, `symEllIntRG_self`, `symEllIntRG_smul`,
  `ei19c_RGVec_eventuallyEq`, `hasDerivAt_symEllIntRG_translate` and
  `hasDerivAt_symEllIntRG_translate_zero`.
- Every acquired formula was checked numerically with mpmath (`elliprf`, `elliprj`, `elliprd`,
  `elliprg`, `elliprc`, quadrature for R_{-a} and the PDEs of 19.18) before being stated.
  For p < 0, mpmath's `elliprj` is complex, and its real part is the principal value.

## Numbered formulas and prose items (part D: §§19.23–19.26)

This part was acquired by ACQ19D on 2026-10-25 (DLMF version 1.2.8). It covers [§19.23](https://dlmf.nist.gov/19.23)–[§19.26](https://dlmf.nist.gov/19.26) (integral representations, inequalities, relations to other functions and addition
theorems for the symmetric integrals). There are 95 active numbered slots (10 in §19.23, 15 in §19.24,
43 in §19.25, 27 in §19.26); the retired slot 19.23.E7 now lives at 19.16.E2_5. All 95 are
acquired in four new modules:
[SymmetricIntegrals.lean](DLMF/EllipticIntegrals/SymmetricIntegrals.lean),
[SymmetricInequalities.lean](DLMF/EllipticIntegrals/SymmetricInequalities.lean),
[SymmetricRelations.lean](DLMF/EllipticIntegrals/SymmetricRelations.lean) and
[SymmetricAddition.lean](DLMF/EllipticIntegrals/SymmetricAddition.lean).
These modules contain 94 tagged declarations: three definitions, 18 proved theorems and
73 admitted statements. No equation in these sections is numerical or an application.
Mathlib has no symmetric-integral API, so there are no upstream pointers. The proofs reuse
the lean-codes Carlson library through the 19C bridges `symEllIntRF_eq_carlsonRF`,
`symEllIntRC_eq_carlsonRC` and `symEllIntR_of_mem`. The reused results are
`Carlson.carlsonRF_add_carlsonRF`, `carlsonRF_add_carlsonRF_zero`,
`carlsonRF_duplication`, `dupLambda_comm_left/right`, `carlsonRK_duplication`,
`regCarlsonR_eq_unitIntervalIntegral`, `inv_dupMean_le_carlsonRF_sq` and
`Real.compEllIntKk_eq`.

Conventions and corrections of part D:

- `symEllIntRJ`, `symEllIntRC` and therefore `symEllIntRD` follow 19C: Cauchy principal
  values for negative real p (respectively y). The normalization R_J = R_{-3/2}(½,½,½,1; ·)
  was confirmed numerically.
- Every statement was checked numerically with mpmath before acquisition. The statements
  below differ from the printed DLMF conditions, each on numerical evidence.
- 19.25.E5 (with 19.25(i) generally) for complex φ: with the straight-segment principal
  integrals, about 15% of random cases with both φ and k nonreal fail, for example
  φ = 0.771 + 0.492i, k = −1.32 + 0.604i. All cases pass for real φ, real k² < 1 or imaginary k.
  The 19.25(i) formulas are therefore acquired for real φ ∈ (0, π/2] with
  1 − k² sin²φ in the slit plane.
- 19.25.E30/E31: the stated condition cs² ≥ 0 holds for every real u. At u = 1.3K
  (m = 0.64), R_C returns π − am u and R_F returns 2K − u. Both are acquired for 0 < u ≤ K.
- 19.25.E32–E34: the right sides are even in x, so the inverse-function formulas fail for
  x < 0. Differences at x = −0.5 are 1.4639 (arccs), 1.0785 (arccd) and 1.6328 (arccn).
  They are acquired for x ≥ 0, with x ≥ 1 or x ≥ k′ where the function needs it.
- 19.25.E38–E40: the R_F/R_G arguments are assumed in the slit plane. For a rectangular
  lattice, e_j − e_k is negative real when j = 2, 3.
- 19.25.E25: y < z is assumed (k ≠ 0).
- 19.26.E9: stated for p > 0; it fails for p < 0 with principal values.
- 19.26.E13: α = −2, β = 3, θ = 1.5 meet the printed conditions but the identity is off by
  0.708. Corrected by adding α, β > 0.
- 19.26.E14: x > 0 is assumed, since the formula divides by x.
- 19.26.E27: fails at x = −2, θ = −3 (off by −0.98966) and at x = −1 + 0.5i. Corrected to
  Re x > 0. The independent check found a second failure, x = 1, θ = 2 (θ > x²: the left side is a
  Cauchy principal value by 19.2.20, the right side is not; they differ by −πi/(2√θ)), so the
  hypothesis x² − θ ∈ ℂ \ (−∞, 0] was added on 2026-10-25; 3000 random complex cases pass.
- Stronger than DLMF: 19.23.E10 holds for complex a, a′ with positive real parts;
  19.26.E18 holds on the slit plane; 19.25.E29 does not need 0 ≤ k²;
  19.26.E1 is proved on DLMF's full domain, including the zero cases.

## [§19.23 Integral Representations](https://dlmf.nist.gov/19.23)

- [19.23.E1](https://dlmf.nist.gov/19.23.E1): [`DLMF.EllipticIntegrals.symEllIntRF_zero_eq_integral_trig`](DLMF/EllipticIntegrals/SymmetricIntegrals.lean#L58) (admitted).
- [19.23.E2](https://dlmf.nist.gov/19.23.E2): [`DLMF.EllipticIntegrals.symEllIntRG_zero_eq_integral_trig`](DLMF/EllipticIntegrals/SymmetricIntegrals.lean#L66) (admitted).
- [19.23.E3](https://dlmf.nist.gov/19.23.E3): [`DLMF.EllipticIntegrals.symEllIntRD_zero_eq_integral_trig`](DLMF/EllipticIntegrals/SymmetricIntegrals.lean#L74) (admitted).
- [19.23.E4](https://dlmf.nist.gov/19.23.E4): [`DLMF.EllipticIntegrals.symEllIntRF_zero_eq_integral_symEllIntRC`](DLMF/EllipticIntegrals/SymmetricIntegrals.lean#L85) (admitted).
- [19.23.E5](https://dlmf.nist.gov/19.23.E5): [`DLMF.EllipticIntegrals.symEllIntRF_eq_integral_symEllIntRC`](DLMF/EllipticIntegrals/SymmetricIntegrals.lean#L97) (admitted).
- [19.23.E6](https://dlmf.nist.gov/19.23.E6): [`DLMF.EllipticIntegrals.symEllIntRF_eq_sphere_integral`](DLMF/EllipticIntegrals/SymmetricIntegrals.lean#L114) (admitted).
- [19.23.E6_5](https://dlmf.nist.gov/19.23.E6_5): [`DLMF.EllipticIntegrals.symEllIntRG_eq_sphere_integral`](DLMF/EllipticIntegrals/SymmetricIntegrals.lean#L123) (admitted).
- 19.23.E7: retired in DLMF (moved to 19.16.E2_5); no acquisition.
- [19.23.E8](https://dlmf.nist.gov/19.23.E8): [`DLMF.EllipticIntegrals.symEllIntR_two_eq_integral_trig`](DLMF/EllipticIntegrals/SymmetricIntegrals.lean#L134) (admitted).
- [19.23.E9](https://dlmf.nist.gov/19.23.E9): [`DLMF.EllipticIntegrals.symEllIntR_three_eq_integral_sphere`](DLMF/EllipticIntegrals/SymmetricIntegrals.lean#L150) (admitted).
- [19.23.E10](https://dlmf.nist.gov/19.23.E10): [`DLMF.EllipticIntegrals.symEllIntR_eq_integral_unitInterval`](DLMF/EllipticIntegrals/SymmetricIntegrals.lean#L166) (proved). Stronger than DLMF: complex parameters a, a′ with positive real parts.

## [§19.24 Inequalities](https://dlmf.nist.gov/19.24)

- [19.24.E1](https://dlmf.nist.gov/19.24.E1): [`DLMF.EllipticIntegrals.symEllIntRF_zero_log_bounds`](DLMF/EllipticIntegrals/SymmetricInequalities.lean#L80) (admitted).
- [19.24.E2](https://dlmf.nist.gov/19.24.E2): [`DLMF.EllipticIntegrals.symEllIntRG_zero_bounds`](DLMF/EllipticIntegrals/SymmetricInequalities.lean#L88) (admitted).
- [19.24.E3](https://dlmf.nist.gov/19.24.E3): [`DLMF.EllipticIntegrals.symEllIntRG_zero_sq_bounds`](DLMF/EllipticIntegrals/SymmetricInequalities.lean#L94) (admitted).
- [19.24.E4](https://dlmf.nist.gov/19.24.E4): [`DLMF.EllipticIntegrals.symEllIntRJ_zero_bounds`](DLMF/EllipticIntegrals/SymmetricInequalities.lean#L103) (admitted).
- [19.24.E5](https://dlmf.nist.gov/19.24.E5): [`DLMF.EllipticIntegrals.symEllIntRF_zero_agm_bounds`](DLMF/EllipticIntegrals/SymmetricInequalities.lean#L112) (admitted).
- [19.24.E6](https://dlmf.nist.gov/19.24.E6): [`DLMF.EllipticIntegrals.symEllIntRF_zero_agm_bounds`](DLMF/EllipticIntegrals/SymmetricInequalities.lean#L112) (admitted).
- [19.24.E7](https://dlmf.nist.gov/19.24.E7): [`DLMF.EllipticIntegrals.ellipsePerimeter_eq_symEllIntRG`](DLMF/EllipticIntegrals/SymmetricInequalities.lean#L122) (admitted). Stated for the 19.9(i) perimeter `ellipsePerimeter` from Inequalities.lean.
- [19.24.E8](https://dlmf.nist.gov/19.24.E8): [`DLMF.EllipticIntegrals.symEllIntRF_symEllIntRG_complete_bounds`](DLMF/EllipticIntegrals/SymmetricInequalities.lean#L131) (admitted).
- [19.24.E9](https://dlmf.nist.gov/19.24.E9): [`DLMF.EllipticIntegrals.symEllIntRG_div_symEllIntRF_agm_bounds`](DLMF/EllipticIntegrals/SymmetricInequalities.lean#L140) (admitted).
- [19.24.E10](https://dlmf.nist.gov/19.24.E10): [`DLMF.EllipticIntegrals.symEllIntRF_ge`](DLMF/EllipticIntegrals/SymmetricInequalities.lean#L154) (proved); [`DLMF.EllipticIntegrals.symEllIntRF_le`](DLMF/EllipticIntegrals/SymmetricInequalities.lean#L167) (admitted). Lower bound proved for positive reals; upper bound admitted.
- [19.24.E11](https://dlmf.nist.gov/19.24.E11): [`DLMF.EllipticIntegrals.symEllIntRJ_bounds`](DLMF/EllipticIntegrals/SymmetricInequalities.lean#L173) (admitted).
- [19.24.E12](https://dlmf.nist.gov/19.24.E12): [`DLMF.EllipticIntegrals.symEllIntRG_bounds`](DLMF/EllipticIntegrals/SymmetricInequalities.lean#L181) (admitted).
- [19.24.E13](https://dlmf.nist.gov/19.24.E13): [`DLMF.EllipticIntegrals.symEllIntR_mul_neg_gt`](DLMF/EllipticIntegrals/SymmetricInequalities.lean#L190) (admitted).
- [19.24.E14](https://dlmf.nist.gov/19.24.E14): [`DLMF.EllipticIntegrals.symEllIntRF_symEllIntRG_gt`](DLMF/EllipticIntegrals/SymmetricInequalities.lean#L203) (admitted).
- [19.24.E15](https://dlmf.nist.gov/19.24.E15): [`DLMF.EllipticIntegrals.symEllIntRF_symEllIntRC_bounds`](DLMF/EllipticIntegrals/SymmetricInequalities.lean#L212) (admitted).

## [§19.25 Relations to Other Functions](https://dlmf.nist.gov/19.25)

- [19.25.E1](https://dlmf.nist.gov/19.25.E1): [`DLMF.EllipticIntegrals.compEllIntKk_eq_symEllIntRF`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L74) (proved); [`DLMF.EllipticIntegrals.compEllIntKk_ofReal_eq_symEllIntRF`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L84) (proved); [`DLMF.EllipticIntegrals.compEllIntEk_eq_symEllInt`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L92) (proved). The real k² < 1 form is proved via `Carlson.Real.compEllIntKk_eq`; the complex form is admitted.
- [19.25.E2](https://dlmf.nist.gov/19.25.E2): [`DLMF.EllipticIntegrals.compEllIntPik_sub_compEllIntKk`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L129) (proved).
- [19.25.E3](https://dlmf.nist.gov/19.25.E3): [`DLMF.EllipticIntegrals.compEllIntPik_eq_symEllIntR`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L148) (proved).
- [19.25.E4](https://dlmf.nist.gov/19.25.E4): [`DLMF.EllipticIntegrals.compEllIntPik_pv_eq`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L157) (admitted). Principal value; checked against the real part of the mpmath value.
- [19.25.E5](https://dlmf.nist.gov/19.25.E5): [`DLMF.EllipticIntegrals.incEllIntFk_eq_symEllIntRF`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L166) (proved). Restricted to real φ ∈ (0, π/2] with 1 − k² sin²φ in the slit plane; see corrections.
- [19.25.E6](https://dlmf.nist.gov/19.25.E6): [`DLMF.EllipticIntegrals.hasDerivAt_incEllIntFk_symEllIntRD`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L179) (admitted).
- [19.25.E7](https://dlmf.nist.gov/19.25.E7): [`DLMF.EllipticIntegrals.incEllIntEk_eq_symEllIntRG`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L190) (proved).
- [19.25.E8](https://dlmf.nist.gov/19.25.E8): [`DLMF.EllipticIntegrals.incEllIntEk_eq_symEllIntR`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L208) (proved).
- [19.25.E9](https://dlmf.nist.gov/19.25.E9): [`DLMF.EllipticIntegrals.incEllIntEk_eq_symEllIntRF_sub_symEllIntRD`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L218) (proved).
- [19.25.E10](https://dlmf.nist.gov/19.25.E10): [`DLMF.EllipticIntegrals.incEllIntEk_eq_symEllIntRD_second`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L232) (proved).
- [19.25.E11](https://dlmf.nist.gov/19.25.E11): [`DLMF.EllipticIntegrals.incEllIntEk_eq_symEllIntRD_third`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L267) (proved).
- [19.25.E12](https://dlmf.nist.gov/19.25.E12): [`DLMF.EllipticIntegrals.hasDerivAt_incEllIntEk_symEllIntRD`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L285) (admitted).
- [19.25.E13](https://dlmf.nist.gov/19.25.E13): [`DLMF.EllipticIntegrals.incEllIntDk_eq_symEllIntRD`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L295) (proved).
- [19.25.E14](https://dlmf.nist.gov/19.25.E14): [`DLMF.EllipticIntegrals.incEllIntPik_sub_incEllIntFk`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L308) (proved).
- [19.25.E15](https://dlmf.nist.gov/19.25.E15): [`DLMF.EllipticIntegrals.incEllIntPik_eq_symEllIntR`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L323) (proved).
- [19.25.E16](https://dlmf.nist.gov/19.25.E16): [`DLMF.EllipticIntegrals.incEllIntPik_pv_eq`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L334) (admitted).
- [19.25.E17](https://dlmf.nist.gov/19.25.E17): [`DLMF.EllipticIntegrals.incEllIntFk_eq_symEllIntRF`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L166) (proved).
- [19.25.E18](https://dlmf.nist.gov/19.25.E18): [`DLMF.EllipticIntegrals.incEllIntFk_eq_symEllIntRF`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L166) (proved).
- [19.25.E19](https://dlmf.nist.gov/19.25.E19): [`DLMF.EllipticIntegrals.bulirschCel_eq_symEllInt`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L351) (admitted). Holds for p < 0 with the R_J principal value; checked numerically.
- [19.25.E20](https://dlmf.nist.gov/19.25.E20): [`DLMF.EllipticIntegrals.bulirschEl1_eq_symEllIntRF`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L360) (proved).
- [19.25.E21](https://dlmf.nist.gov/19.25.E21): [`DLMF.EllipticIntegrals.bulirschEl2_eq_symEllInt`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L369) (proved).
- [19.25.E22](https://dlmf.nist.gov/19.25.E22): [`DLMF.EllipticIntegrals.bulirschEl3_eq_symEllInt`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L379) (admitted).
- [19.25.E23](https://dlmf.nist.gov/19.25.E23): [`DLMF.EllipticIntegrals.sqrt_mul_symEllIntRF_eq_incEllIntFk`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L392) (proved); [`DLMF.EllipticIntegrals.symEllIntRD_eq_incEllInt`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L409) (proved); [`DLMF.EllipticIntegrals.symEllIntRJ_eq_incEllInt`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L438) (proved); [`DLMF.EllipticIntegrals.symEllIntRG_eq_incEllInt`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L479) (proved).
- [19.25.E24](https://dlmf.nist.gov/19.25.E24): [`DLMF.EllipticIntegrals.sqrt_mul_symEllIntRF_eq_incEllIntFk`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L392) (proved).
- [19.25.E25](https://dlmf.nist.gov/19.25.E25): [`DLMF.EllipticIntegrals.symEllIntRD_eq_incEllInt`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L409) (proved). Assumes y < z so that k ≠ 0.
- [19.25.E26](https://dlmf.nist.gov/19.25.E26): [`DLMF.EllipticIntegrals.symEllIntRJ_eq_incEllInt`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L438) (proved).
- [19.25.E27](https://dlmf.nist.gov/19.25.E27): [`DLMF.EllipticIntegrals.symEllIntRG_eq_incEllInt`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L479) (proved).
- [19.25.E28](https://dlmf.nist.gov/19.25.E28): [`DLMF.EllipticIntegrals.jacobiDeltam`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L543) (definition); [`DLMF.EllipticIntegrals.jacobiDeltam_swap`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L550) (proved).
- [19.25.E29](https://dlmf.nist.gov/19.25.E29): [`DLMF.EllipticIntegrals.jacobiDeltam_values`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L556) (proved). Stronger than DLMF: 0 ≤ k² is not needed.
- [19.25.E30](https://dlmf.nist.gov/19.25.E30): [`DLMF.EllipticIntegrals.jacobiAmm_eq_symEllIntRC`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L613) (proved). Restricted to 0 < u ≤ K; see corrections.
- [19.25.E31](https://dlmf.nist.gov/19.25.E31): [`DLMF.EllipticIntegrals.eq_symEllIntRF_jacobi`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L643) (proved). Restricted to 0 < u ≤ K; see corrections.
- [19.25.E32](https://dlmf.nist.gov/19.25.E32): [`DLMF.EllipticIntegrals.jacobiArcps_eq_symEllIntRF`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L680) (admitted). Restricted to x ≥ 0; see corrections.
- [19.25.E33](https://dlmf.nist.gov/19.25.E33): [`DLMF.EllipticIntegrals.jacobiArcsp_eq_symEllIntRF`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L695) (admitted). Restricted to x ≥ 0; see corrections.
- [19.25.E34](https://dlmf.nist.gov/19.25.E34): [`DLMF.EllipticIntegrals.jacobiArcpq_eq_symEllIntRF`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L709) (admitted). Restricted to x ≥ 0, with x ≥ 1 or x ≥ k′ where the function needs it; see corrections.
- [19.25.E35](https://dlmf.nist.gov/19.25.E35): [`DLMF.EllipticIntegrals.weierstrassP_symEllIntRF`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L744) (admitted); [`DLMF.EllipticIntegrals.weierstrassZeta_symEllIntRG`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L755) (admitted).
- [19.25.E36](https://dlmf.nist.gov/19.25.E36): [`DLMF.EllipticIntegrals.weierstrassP_symEllIntRF`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L744) (admitted).
- [19.25.E37](https://dlmf.nist.gov/19.25.E37): [`DLMF.EllipticIntegrals.weierstrassZeta_symEllIntRG`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L755) (admitted).
- [19.25.E38](https://dlmf.nist.gov/19.25.E38): [`DLMF.EllipticIntegrals.halfPeriod_eq_symEllIntRF`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L769) (admitted). The R_F arguments are assumed in the slit plane; a rectangular lattice with j = 2, 3 does not meet this hypothesis.
- [19.25.E39](https://dlmf.nist.gov/19.25.E39): [`DLMF.EllipticIntegrals.halfPeriod_eq_symEllIntRF`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L769) (admitted).
- [19.25.E40](https://dlmf.nist.gov/19.25.E40): [`DLMF.EllipticIntegrals.eq_weierstrassSigma_mul_symEllIntRF`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L790) (admitted). The R_F arguments are assumed in the slit plane.
- [19.25.E41](https://dlmf.nist.gov/19.25.E41): [`DLMF.EllipticIntegrals.weierstrassSigmaIdx`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L783) (definition).
- [19.25.E42](https://dlmf.nist.gov/19.25.E42): [`DLMF.EllipticIntegrals.ordinaryHypergeometric_eq_symEllIntR`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L803) (proved).
- [19.25.E43](https://dlmf.nist.gov/19.25.E43): [`DLMF.EllipticIntegrals.symEllIntR_two_eq_ordinaryHypergeometric`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L826) (admitted).

## [§19.26 Addition Theorems](https://dlmf.nist.gov/19.26)

- [19.26.E1](https://dlmf.nist.gov/19.26.E1): [`DLMF.EllipticIntegrals.symEllIntRF_add_symEllIntRF`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L257) (proved). Proved on the full DLMF domain, including the zero cases.
- [19.26.E2](https://dlmf.nist.gov/19.26.E2): [`DLMF.EllipticIntegrals.symEllInt_addition_mu_perm`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L78) (proved); [`DLMF.EllipticIntegrals.symEllIntRF_add_symEllIntRF`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L257) (proved).
- [19.26.E3](https://dlmf.nist.gov/19.26.E3): [`DLMF.EllipticIntegrals.symEllInt_addition_sqrt_z`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L105) (admitted).
- [19.26.E4](https://dlmf.nist.gov/19.26.E4): [`DLMF.EllipticIntegrals.symEllInt_addition_sqrt_z`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L105) (admitted); [`DLMF.EllipticIntegrals.symEllInt_addition_note`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L117) (proved).
- [19.26.E5](https://dlmf.nist.gov/19.26.E5): [`DLMF.EllipticIntegrals.symEllInt_addition_mu_iff`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L166) (proved).
- [19.26.E6](https://dlmf.nist.gov/19.26.E6): [`DLMF.EllipticIntegrals.symEllInt_addition_quadratic`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L201) (proved).
- [19.26.E7](https://dlmf.nist.gov/19.26.E7): [`DLMF.EllipticIntegrals.symEllIntRD_add_symEllIntRD`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L293) (admitted).
- [19.26.E8](https://dlmf.nist.gov/19.26.E8): [`DLMF.EllipticIntegrals.symEllIntRG_add_symEllIntRG`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L305) (admitted).
- [19.26.E9](https://dlmf.nist.gov/19.26.E9): [`DLMF.EllipticIntegrals.symEllIntRJ_add_symEllIntRJ`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L319) (admitted). Stated for p > 0; the identity fails for p < 0 with principal values.
- [19.26.E10](https://dlmf.nist.gov/19.26.E10): [`DLMF.EllipticIntegrals.symEllIntRJ_add_symEllIntRJ`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L319) (admitted).
- [19.26.E11](https://dlmf.nist.gov/19.26.E11): [`DLMF.EllipticIntegrals.symEllIntRC_add_symEllIntRC`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L333) (proved).
- [19.26.E12](https://dlmf.nist.gov/19.26.E12): [`DLMF.EllipticIntegrals.symEllIntRC_add_symEllIntRC`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L333) (proved); [`DLMF.EllipticIntegrals.symEllIntRC_addition_mu`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L369) (proved).
- [19.26.E13](https://dlmf.nist.gov/19.26.E13): [`DLMF.EllipticIntegrals.symEllIntRC_addition_theta`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L384) (admitted). Corrected by adding α, β > 0; see corrections.
- [19.26.E14](https://dlmf.nist.gov/19.26.E14): [`DLMF.EllipticIntegrals.symEllIntRC_addition_pq`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L399) (admitted). Assumes x > 0, since DLMF divides by x.
- [19.26.E15](https://dlmf.nist.gov/19.26.E15): [`DLMF.EllipticIntegrals.symEllIntRC_addition_pq`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L399) (admitted); [`DLMF.EllipticIntegrals.symEllIntRC_addition_eta_sub_xi`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L412) (proved).
- [19.26.E16](https://dlmf.nist.gov/19.26.E16): [`DLMF.EllipticIntegrals.symEllIntRF_addition_zero`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L132) (proved).
- [19.26.E17](https://dlmf.nist.gov/19.26.E17): [`DLMF.EllipticIntegrals.symEllIntRC_addition_zero`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L423) (admitted).
- [19.26.E18](https://dlmf.nist.gov/19.26.E18): [`DLMF.EllipticIntegrals.symEllIntRF_duplication`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L444) (proved); [`DLMF.EllipticIntegrals.symEllIntRF_duplication_zero`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L459) (proved); [`DLMF.EllipticIntegrals.symEllIntRF_duplication_quarter`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L503) (proved). Proved on the slit plane (stronger than DLMF), with one-zero and quarter forms.
- [19.26.E19](https://dlmf.nist.gov/19.26.E19): [`DLMF.EllipticIntegrals.symEllIntDupLambda`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L433) (definition).
- [19.26.E20](https://dlmf.nist.gov/19.26.E20): [`DLMF.EllipticIntegrals.symEllIntRD_duplication`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L526) (admitted).
- [19.26.E21](https://dlmf.nist.gov/19.26.E21): [`DLMF.EllipticIntegrals.symEllIntRG_duplication`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L535) (admitted).
- [19.26.E22](https://dlmf.nist.gov/19.26.E22): [`DLMF.EllipticIntegrals.symEllIntRJ_duplication`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L544) (admitted).
- [19.26.E23](https://dlmf.nist.gov/19.26.E23): [`DLMF.EllipticIntegrals.symEllIntRJ_duplication`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L544) (admitted); [`DLMF.EllipticIntegrals.symEllIntRJ_duplication_alpha_beta`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L556) (proved).
- [19.26.E24](https://dlmf.nist.gov/19.26.E24): [`DLMF.EllipticIntegrals.symEllInt_duplication_inverse`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L582) (proved).
- [19.26.E25](https://dlmf.nist.gov/19.26.E25): [`DLMF.EllipticIntegrals.symEllIntRC_duplication`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L618) (admitted).
- [19.26.E26](https://dlmf.nist.gov/19.26.E26): [`DLMF.EllipticIntegrals.symEllIntRC_sq_eq`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L625) (admitted).
- [19.26.E27](https://dlmf.nist.gov/19.26.E27): [`DLMF.EllipticIntegrals.symEllIntRC_duplication_theta`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L631) (admitted). Corrected to Re x > 0 and x² − θ ∈ ℂ \ (−∞, 0]; see corrections.

## Analytical prose (part D)

- [19.23.p1–p5](https://dlmf.nist.gov/19.23): the conditions on the integral
  representations are encoded in the hypotheses of the 19.23 declarations. The relocation
  of 19.23.E7 to 19.16.E2_5 is recorded above. p6 is a bibliographic pointer
  (excluded: commentary).
- [19.24(i).p1–p5](https://dlmf.nist.gov/19.24.i), [19.24(ii).p1](https://dlmf.nist.gov/19.24.ii)
  and 19.24.Px1.p1–p3: the domains and conditions of the inequalities are stated with the
  corresponding 19.24 declarations.
- [19.25(i).p1–p4](https://dlmf.nist.gov/19.25.i): the domain conditions are encoded at
  19.25.E1–E18. The nonnegativity remark in p2 is included in the docstrings.
- [19.25(ii).p1](https://dlmf.nist.gov/19.25.ii), [19.25(iii).p1–p4](https://dlmf.nist.gov/19.25.iii):
  the conditions are encoded at 19.25.E19–E27. iii.p3/p4 are commentary
  (excluded: commentary).
- [19.25(iv).p1](https://dlmf.nist.gov/19.25.iv): a pointer to theta-function formulas
  in 20.9(i) (excluded: cross-reference).
- [19.25(v).p1–p4](https://dlmf.nist.gov/19.25.v): the definition of Δ(p, q) is
  `jacobiDeltam` (19.25.E28). The range conditions are encoded and corrected at
  19.25.E30–E34. p3/p4 are commentary (excluded: commentary).
- [19.25(vi).p1–p3](https://dlmf.nist.gov/19.25.vi): lattice and root conventions use
  `DLMF.Weierstrass.HalfPeriods`. The index convention for σ_j is `weierstrassSigmaIdx`
  (19.25.E41).
- [19.25(vii).p1](https://dlmf.nist.gov/19.25.vii): the hypergeometric conditions are
  encoded at 19.25.E42–E43.
- [19.26(i).p1](https://dlmf.nist.gov/19.26.i), [19.26(ii).p1](https://dlmf.nist.gov/19.26.ii),
  [19.26(iii).p1–p3](https://dlmf.nist.gov/19.26.iii): the positivity domains and the
  definitions of λ and μ are encoded (`symEllIntDupLambda`, 19.26.E19 and E2–E6).

## Validation (part D)

- All four modules build with `lake build`. The strict `lake env lean -DautoImplicit=false
  -DrelaxedAutoImplicit=false` check has no warnings other than `sorry`; it was run with a
  merged ToMathlib overlay ahead of LEAN_PATH, because plain `lake env lean` cannot resolve
  ToMathlib modules split between lean-codes and lean-DLMF. There are no axioms and no
  `native_decide`, and no helper declaration (prefix `ei19d_`) contains `sorry`.
- Admissions (`grep -c '\bsorry\b'`): SymmetricIntegrals 9, SymmetricInequalities 14,
  SymmetricRelations 36, SymmetricAddition 14.
- `#print axioms` was run on all 18 proved declarations; every one depends only on
  `[propext, Classical.choice, Quot.sound]`.
- Every numbered formula of §§19.23–19.26 was checked numerically with mpmath before being
  stated. The inequalities of §19.24 were tested on at least 300 random samples each.

## Numbered formulas and prose items (part E: §§19.27–19.29)

Modules `DLMF.EllipticIntegrals.{SymmetricAsymptotics, SymmetricIntegralsOfIntegrals, SymmetricReduction}`, checked on 2026-10-25. All 59 numbered formulas are acquired; exclusions for the rest of the chapter follow the part E validation.

## [§19.27 Asymptotic Approximations and Expansions](https://dlmf.nist.gov/19.27)

Module [DLMF/EllipticIntegrals/SymmetricAsymptotics.lean](DLMF/EllipticIntegrals/SymmetricAsymptotics.lean) (ACQ19E).
DLMF's `O`-terms as `a/z → 0` etc. are read with the large arguments fixed and positive and the
small arguments tending to `0` jointly through DLMF's domain (real, nonnegative, at most one of
`x, y, z` zero, `p > 0`), as Mathlib `IsBigO` along `𝓝[S] 0`; uniformity in the fixed arguments
is not asserted. All 16 formulas were checked numerically along random directions of approach.
Two printed formulas are false and are acquired in corrected form (see "Corrections" below).

- [19.27.E1](https://dlmf.nist.gov/19.27.E1): [`DLMF.EllipticIntegrals.ellAsymA`](DLMF/EllipticIntegrals/SymmetricAsymptotics.lean#L75) (definition); [`DLMF.EllipticIntegrals.ellAsymB`](DLMF/EllipticIntegrals/SymmetricAsymptotics.lean#L79) (definition); [`DLMF.EllipticIntegrals.ellAsymC`](DLMF/EllipticIntegrals/SymmetricAsymptotics.lean#L83) (definition); [`DLMF.EllipticIntegrals.ellAsymF`](DLMF/EllipticIntegrals/SymmetricAsymptotics.lean#L87) (definition); [`DLMF.EllipticIntegrals.ellAsymG`](DLMF/EllipticIntegrals/SymmetricAsymptotics.lean#L91) (definition); [`DLMF.EllipticIntegrals.ellAsymH`](DLMF/EllipticIntegrals/SymmetricAsymptotics.lean#L95) (definition).
- [19.27.E2](https://dlmf.nist.gov/19.27.E2): [`DLMF.EllipticIntegrals.symEllIntRF_asymp_large_z`](DLMF/EllipticIntegrals/SymmetricAsymptotics.lean#L109) (admitted); [`DLMF.EllipticIntegrals.symEllIntRF_isEquivalent_atTop`](DLMF/EllipticIntegrals/SymmetricAsymptotics.lean#L128) (proved); [`DLMF.EllipticIntegrals.symEllIntRF_zero_isEquivalent`](DLMF/EllipticIntegrals/SymmetricAsymptotics.lean#L163) (proved).
- [19.27.E3](https://dlmf.nist.gov/19.27.E3): [`DLMF.EllipticIntegrals.symEllIntRF_asymp_small_x`](DLMF/EllipticIntegrals/SymmetricAsymptotics.lean#L119) (admitted).
- [19.27.E4](https://dlmf.nist.gov/19.27.E4): [`DLMF.EllipticIntegrals.symEllIntRG_asymp_large_z`](DLMF/EllipticIntegrals/SymmetricAsymptotics.lean#L195) (admitted).
- [19.27.E5](https://dlmf.nist.gov/19.27.E5): [`DLMF.EllipticIntegrals.symEllIntRG_asymp_small_x`](DLMF/EllipticIntegrals/SymmetricAsymptotics.lean#L204) (admitted).
- [19.27.E6](https://dlmf.nist.gov/19.27.E6): [`DLMF.EllipticIntegrals.symEllIntRG_zero_asymp`](DLMF/EllipticIntegrals/SymmetricAsymptotics.lean#L212) (admitted).
- [19.27.E7](https://dlmf.nist.gov/19.27.E7): [`DLMF.EllipticIntegrals.symEllIntRD_asymp_large_z`](DLMF/EllipticIntegrals/SymmetricAsymptotics.lean#L223) (admitted).
- [19.27.E8](https://dlmf.nist.gov/19.27.E8): [`DLMF.EllipticIntegrals.symEllIntRD_asymp_small_z`](DLMF/EllipticIntegrals/SymmetricAsymptotics.lean#L234) (admitted).
- [19.27.E9](https://dlmf.nist.gov/19.27.E9): [`DLMF.EllipticIntegrals.symEllIntRD_asymp_large_x`](DLMF/EllipticIntegrals/SymmetricAsymptotics.lean#L244) (admitted).
- [19.27.E10](https://dlmf.nist.gov/19.27.E10): [`DLMF.EllipticIntegrals.symEllIntRD_asymp_small_x`](DLMF/EllipticIntegrals/SymmetricAsymptotics.lean#L254) (admitted).
- [19.27.E11](https://dlmf.nist.gov/19.27.E11): [`DLMF.EllipticIntegrals.symEllIntRJ_asymp_large_p`](DLMF/EllipticIntegrals/SymmetricAsymptotics.lean#L265) (admitted).
- [19.27.E12](https://dlmf.nist.gov/19.27.E12): [`DLMF.EllipticIntegrals.symEllIntRJ_small_p_bounds`](DLMF/EllipticIntegrals/SymmetricAsymptotics.lean#L277) (admitted).
- [19.27.E13](https://dlmf.nist.gov/19.27.E13): [`DLMF.EllipticIntegrals.symEllIntRJ_asymp_small_xy`](DLMF/EllipticIntegrals/SymmetricAsymptotics.lean#L292) (admitted).
- [19.27.E14](https://dlmf.nist.gov/19.27.E14): [`DLMF.EllipticIntegrals.symEllIntRJ_asymp_small_xp`](DLMF/EllipticIntegrals/SymmetricAsymptotics.lean#L305) (admitted).
- [19.27.E15](https://dlmf.nist.gov/19.27.E15): [`DLMF.EllipticIntegrals.symEllIntRJ_asymp_small_x`](DLMF/EllipticIntegrals/SymmetricAsymptotics.lean#L316) (admitted).
- [19.27.E16](https://dlmf.nist.gov/19.27.E16): [`DLMF.EllipticIntegrals.symEllIntRJ_asymp_large_x`](DLMF/EllipticIntegrals/SymmetricAsymptotics.lean#L326) (admitted).

## [§19.28 Integrals of Elliptic Integrals](https://dlmf.nist.gov/19.28)

Module [DLMF/EllipticIntegrals/SymmetricIntegralsOfIntegrals.lean](DLMF/EllipticIntegrals/SymmetricIntegralsOfIntegrals.lean) (ACQ19E).
`B` is Mathlib's `Complex.betaIntegral`; `R_{-a}(b₁, b₂; t, 1)` is `symEllIntR a`. All ten
formulas were checked numerically (complex `σ` included); 19.28.9 needs an extra hypothesis.

- [19.28.E1](https://dlmf.nist.gov/19.28.E1): [`DLMF.EllipticIntegrals.integral_cpow_mul_symEllIntRF_zero`](DLMF/EllipticIntegrals/SymmetricIntegralsOfIntegrals.lean#L49) (admitted).
- [19.28.E2](https://dlmf.nist.gov/19.28.E2): [`DLMF.EllipticIntegrals.integral_cpow_mul_symEllIntRG_zero`](DLMF/EllipticIntegrals/SymmetricIntegralsOfIntegrals.lean#L56) (admitted).
- [19.28.E3](https://dlmf.nist.gov/19.28.E3): [`DLMF.EllipticIntegrals.integral_cpow_mul_symEllIntRD_zero`](DLMF/EllipticIntegrals/SymmetricIntegralsOfIntegrals.lean#L63) (admitted).
- [19.28.E4](https://dlmf.nist.gov/19.28.E4): [`DLMF.EllipticIntegrals.integral_cpow_mul_symEllIntR_two`](DLMF/EllipticIntegrals/SymmetricIntegralsOfIntegrals.lean#L70) (admitted).
- [19.28.E5](https://dlmf.nist.gov/19.28.E5): [`DLMF.EllipticIntegrals.integral_Ioi_symEllIntRD`](DLMF/EllipticIntegrals/SymmetricIntegralsOfIntegrals.lean#L83) (admitted).
- [19.28.E6](https://dlmf.nist.gov/19.28.E6): [`DLMF.EllipticIntegrals.integral_symEllIntRD_interp`](DLMF/EllipticIntegrals/SymmetricIntegralsOfIntegrals.lean#L89) (admitted).
- [19.28.E7](https://dlmf.nist.gov/19.28.E7): [`DLMF.EllipticIntegrals.integral_symEllIntRJ_sq`](DLMF/EllipticIntegrals/SymmetricIntegralsOfIntegrals.lean#L98) (admitted).
- [19.28.E8](https://dlmf.nist.gov/19.28.E8): [`DLMF.EllipticIntegrals.integral_symEllIntRJ_scale`](DLMF/EllipticIntegrals/SymmetricIntegralsOfIntegrals.lean#L105) (admitted).
- [19.28.E9](https://dlmf.nist.gov/19.28.E9): [`DLMF.EllipticIntegrals.integral_symEllIntRF_sin_cos`](DLMF/EllipticIntegrals/SymmetricIntegralsOfIntegrals.lean#L114) (admitted).
- [19.28.E10](https://dlmf.nist.gov/19.28.E10): [`DLMF.EllipticIntegrals.integral_symEllIntRF_cosh`](DLMF/EllipticIntegrals/SymmetricIntegralsOfIntegrals.lean#L125) (admitted).

## [§19.29 Reduction of General Elliptic Integrals](https://dlmf.nist.gov/19.29)

Module [DLMF/EllipticIntegrals/SymmetricReduction.lean](DLMF/EllipticIntegrals/SymmetricReduction.lean) (ACQ19E).
Coefficients `a_α, b_α` are complex, indexed by `Fin 5` (DLMF `α = 1..5` is Lean `0..4`);
integrals over `(y, x)` are Lebesgue integrals over `Ioo y x`. The algebraic identities
(19.29.5), (19.29.9) are proved for arbitrary complex data; the real case of (19.29.4) and the
case `0 < y` of (19.29.19) are proved from `lean-codes` (Carlson's (9.8-12) and Exercise 9.8-3);
the recurrences (19.29.15), (19.29.16), (19.29.18) are proved; (19.29.26), (19.29.27) and
(19.29.32) are derived from the admitted (19.29.24) and (19.29.30). All 33 formulas were
checked numerically (19.29.4, 19.29.7 also with complex coefficients; 19.29.6 both infinite
cases; the degenerate case of 19.29.iii.p1).

- [19.29.E1](https://dlmf.nist.gov/19.29.E1): [`DLMF.EllipticIntegrals.ellRedRoot`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L65) (definition).
- [19.29.E2](https://dlmf.nist.gov/19.29.E2): [`DLMF.EllipticIntegrals.ellRedDet`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L70) (definition).
- [19.29.E3](https://dlmf.nist.gov/19.29.E3): [`DLMF.EllipticIntegrals.ellRedS`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L74) (definition).
- [19.29.E4](https://dlmf.nist.gov/19.29.E4): [`DLMF.EllipticIntegrals.ellRed_integral_inv_s`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L248) (admitted); [`DLMF.EllipticIntegrals.ellRed_integral_inv_s_of_pos`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L339) (proved).
- [19.29.E5](https://dlmf.nist.gov/19.29.E5): [`DLMF.EllipticIntegrals.ellRedU`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L80) (definition); [`DLMF.EllipticIntegrals.ellRedU_symm`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L141) (proved); [`DLMF.EllipticIntegrals.ellRedU_sq_sub_sq`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L151) (proved).
- [19.29.E6](https://dlmf.nist.gov/19.29.E6): [`DLMF.EllipticIntegrals.ellRedUInf`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L88) (definition); [`DLMF.EllipticIntegrals.ellRedUNegInf`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L95) (definition); [`DLMF.EllipticIntegrals.ellRed_integral_inv_s_Ioi`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L258) (admitted); [`DLMF.EllipticIntegrals.ellRed_integral_inv_s_Iio`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L271) (admitted).
- [19.29.E7](https://dlmf.nist.gov/19.29.E7): [`DLMF.EllipticIntegrals.ellRed_integral_ratio_s`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L284) (admitted).
- [19.29.E8](https://dlmf.nist.gov/19.29.E8): [`DLMF.EllipticIntegrals.ellRed_integral_ratio5_s`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L298) (admitted).
- [19.29.E9](https://dlmf.nist.gov/19.29.E9): [`DLMF.EllipticIntegrals.ellRedU5Sq`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L102) (definition); [`DLMF.EllipticIntegrals.ellRedS5`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L109) (definition); [`DLMF.EllipticIntegrals.ellRedQ5Sq`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L117) (definition); [`DLMF.EllipticIntegrals.ellRedU5Sq_eq`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L183) (proved); [`DLMF.EllipticIntegrals.ellRedS5_sq_sub_Q5Sq`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L226) (proved).
- [19.29.E10](https://dlmf.nist.gov/19.29.E10): [`DLMF.EllipticIntegrals.ellRed_example_GR3142`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L321) (admitted).
- [19.29.E11](https://dlmf.nist.gov/19.29.E11): [`DLMF.EllipticIntegrals.ellRedI`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L424) (definition).
- [19.29.E12](https://dlmf.nist.gov/19.29.E12): [`DLMF.EllipticIntegrals.ellRedE`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L430) (definition); [`DLMF.EllipticIntegrals.ellRedE_sum`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L434) (proved).
- [19.29.E13](https://dlmf.nist.gov/19.29.E13): [`DLMF.EllipticIntegrals.ellRedBasic`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L440) (definition).
- [19.29.E14](https://dlmf.nist.gov/19.29.E14): [`DLMF.EllipticIntegrals.ellRedBasic`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L440) (definition).
- [19.29.E15](https://dlmf.nist.gov/19.29.E15): [`DLMF.EllipticIntegrals.ellRedI_partial_fraction`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L479) (proved).
- [19.29.E16](https://dlmf.nist.gov/19.29.E16): [`DLMF.EllipticIntegrals.ellRedI_cubic_recurrence`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L542) (proved).
- [19.29.E17](https://dlmf.nist.gov/19.29.E17): [`DLMF.EllipticIntegrals.ellRedS3`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L537) (definition).
- [19.29.E18](https://dlmf.nist.gov/19.29.E18): [`DLMF.EllipticIntegrals.ellRedI_recurrence`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L511) (proved).
- [19.29.E19](https://dlmf.nist.gov/19.29.E19): [`DLMF.EllipticIntegrals.ellRed_quad_first`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L692) (admitted); [`DLMF.EllipticIntegrals.ellRed_quad_first_of_pos`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L715) (proved).
- [19.29.E20](https://dlmf.nist.gov/19.29.E20): [`DLMF.EllipticIntegrals.ellRed_quad_second`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L766) (admitted).
- [19.29.E21](https://dlmf.nist.gov/19.29.E21): [`DLMF.EllipticIntegrals.ellRed_quad_third`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L779) (admitted).
- [19.29.E22](https://dlmf.nist.gov/19.29.E22): [`DLMF.EllipticIntegrals.ellRedQuadU`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L685) (definition).
- [19.29.E23](https://dlmf.nist.gov/19.29.E23): [`DLMF.EllipticIntegrals.ellRed_quad_infinite`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L811) (admitted).
- [19.29.E24](https://dlmf.nist.gov/19.29.E24): [`DLMF.EllipticIntegrals.ellRedQuadRF`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L830) (definition); [`DLMF.EllipticIntegrals.ellRed_two_quadratics`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L840) (admitted).
- [19.29.E25](https://dlmf.nist.gov/19.29.E25): [`DLMF.EllipticIntegrals.ellRedQuadS`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L820) (definition); [`DLMF.EllipticIntegrals.ellRedQuadD`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L826) (definition); [`DLMF.EllipticIntegrals.ellRedQuadRF`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L830) (definition).
- [19.29.E26](https://dlmf.nist.gov/19.29.E26): [`DLMF.EllipticIntegrals.ellRedQuadS_linear_mul`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L863) (proved); [`DLMF.EllipticIntegrals.ellRed_linear_linear_quadratic`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L885) (proved from the admitted 19.29.E24).
- [19.29.E27](https://dlmf.nist.gov/19.29.E27): [`DLMF.EllipticIntegrals.ellRed_linear_quadratic`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L916) (proved from the admitted 19.29.E24).
- [19.29.E28](https://dlmf.nist.gov/19.29.E28): [`DLMF.EllipticIntegrals.ellRed_cube_difference`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L931) (admitted).
- [19.29.E29](https://dlmf.nist.gov/19.29.E29): [`DLMF.EllipticIntegrals.ellRed_cube_difference`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L931) (admitted).
- [19.29.E30](https://dlmf.nist.gov/19.29.E30): [`DLMF.EllipticIntegrals.ellRed_biquadratic`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L957) (admitted).
- [19.29.E31](https://dlmf.nist.gov/19.29.E31): [`DLMF.EllipticIntegrals.ellRedBiquadU`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L951) (definition).
- [19.29.E32](https://dlmf.nist.gov/19.29.E32): [`DLMF.EllipticIntegrals.ellRed_quartic_plus`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L977) (proved from the admitted 19.29.E30).
- [19.29.E33](https://dlmf.nist.gov/19.29.E33): [`DLMF.EllipticIntegrals.ellRed_quartic_plus`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L977) (proved from the admitted 19.29.E30).

### §19.27–19.29 prose

- [19.27.i.p1](https://dlmf.nist.gov/19.27#i.p1): notation (19.27.1), definitions `ellAsymA` … `ellAsymH`.
- [19.27.ii.p1](https://dlmf.nist.gov/19.27#ii.p1), [19.27.iii.p1](https://dlmf.nist.gov/19.27#iii.p1), [19.27.iv.p1](https://dlmf.nist.gov/19.27#iv.p1), [19.27.v.p1](https://dlmf.nist.gov/19.27#v.p1): standing assumptions of the subsections, carried as hypotheses and approach sets (`ellAsymPair`, `ellAsymTriple`).
- [19.27.vi.p1](https://dlmf.nist.gov/19.27#vi.p1), [19.27.vi.p2](https://dlmf.nist.gov/19.27#vi.p2): commentary and bibliographic pointers (Carlson–Gustafson bounds; convergent asymptotic series of Wong, Carlson–Gustafson, López; Carlson (1985) for `R_{-a}`); no explicit formula.
- [19.28.p1](https://dlmf.nist.gov/19.28#p1), [19.28.p2](https://dlmf.nist.gov/19.28#p2): standing assumptions `ℜσ > 0`, `x, y, z, p > 0`, carried as hypotheses.
- [19.28.p3](https://dlmf.nist.gov/19.28#p3): pointers to (19.16.24) and Carlson (1963, (7.9)); no formula.
- [19.29.i.p1](https://dlmf.nist.gov/19.29#i.p1): the hypotheses (`EllRedHyp`, `EllRedPerm`), the reduction theorems (19.29.4)–(19.29.9) and "cubic cases by setting one factor equal to 1" (the statements allow `a_4 = 1`, `b_4 = 0`); the principal-value convention for `U_{α5}²`, `Q_{α5}²` is built into `symEllIntRJ`, `symEllIntRC`.
- [19.29.i.p2](https://dlmf.nist.gov/19.29#i.p2): commentary on Gradshteyn–Ryzhik coverage; its example is (19.29.10).
- [19.29.ii.p1](https://dlmf.nist.gov/19.29#ii.p1): (19.29.11), (19.29.12) and the identification of (19.29.4), (19.29.7), (19.29.8) as `I(𝟎)`, `I(𝐞_α - 𝐞_δ)`, `I(𝐞_α - 𝐞_5)` (docstring of `ellRedBasic`).
- [19.29.ii.p2](https://dlmf.nist.gov/19.29#ii.p2): terminology (which `I(𝐦)` are of the first, second, third kind); classification by definition, no theorem.
- [19.29.ii.p3](https://dlmf.nist.gov/19.29#ii.p3): `DLMF.EllipticIntegrals.ellRedI_reduction` (admitted): every `I(𝐦)` is a combination of the basic integrals (19.29.13), (19.29.14) plus `[s_h(t)P(t)/Q(t)]_y^x`; stated with all `d_{jl} ≠ 0`, radicands in the slit plane and all factors nonzero on `[y, x]`. The remark that the basic integrals `I(-𝐞_j)`, `j ≤ h` (and `I(𝐞_j)`, `j ≤ 4`) are not linearly independent is not acquired separately (it follows from (19.29.15) and partial fractions).
- [19.29.ii.p4](https://dlmf.nist.gov/19.29#ii.p4), [19.29.ii.p5](https://dlmf.nist.gov/19.29#ii.p5), [19.29.ii.p6](https://dlmf.nist.gov/19.29#ii.p6): (19.29.15)–(19.29.18); "`I(𝐞_α)` by `a_5 = 1`, `b_5 = 0` in (19.29.8)" is an instance of `ellRed_integral_ratio5_s`; the counts of Gradshteyn–Ryzhik formulas are commentary.
- [19.29.ii.p7](https://dlmf.nist.gov/19.29#ii.p7), [19.29.ii.p8](https://dlmf.nist.gov/19.29#ii.p8): software and bibliographic pointers (FitzSimons; Gray (2002)); no formula.
- [19.29.iii.p1](https://dlmf.nist.gov/19.29#iii.p1): (19.29.19)–(19.29.23) and the degenerate case `U = 0`: `DLMF.EllipticIntegrals.ellRed_quad_degenerate` (admitted; checked numerically with `Q₁ = t² - 1`, `Q₂ = 4 - t²`).
- [19.29.iii.p2](https://dlmf.nist.gov/19.29#iii.p2), [19.29.iii.p3](https://dlmf.nist.gov/19.29#iii.p3), [19.29.iii.p4](https://dlmf.nist.gov/19.29#iii.p4): (19.29.24)–(19.29.33); the parenthetical remark on when the `R_F` variables are real and nonnegative is recorded in the docstring of `ellRedQuadRF` (complex `V` is allowed), not as a theorem.
- [19.29.ii](https://dlmf.nist.gov/19.29.ii): [`DLMF.EllipticIntegrals.ellRedI_reduction`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L448) (admitted).
- [19.29.iii](https://dlmf.nist.gov/19.29.iii): [`DLMF.EllipticIntegrals.ellRed_quad_degenerate`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L794) (admitted).

### Corrections and added hypotheses (§19.27–19.29)

- **19.27.8** (suspected erratum): DLMF prints `R_D(x,y,z) = 3/√(xyz) - (6/(xy)) R_G(x,y,0)(1 + O(z/g))`. The relative error of the bracket is of order `√(z/g)`: for `x = 2, y = 3` the normalized error divided by `√(z/g)` tends to `-1.2895` (`z = 10⁻⁴ … 10⁻¹⁰`), in agreement with Carlson–Gustafson (1994, (37)), whose correction term is `(6a√z/g³)(1 - (πθ/4)√(z/a))`. Acquired with `O(√(z/g))`.
- **19.27.12** (suspected erratum): DLMF prints `R_J(x,y,z,p) = (3/(2√(xyz)))(ln(4f/p) - 2)(1 + O(p/f))`. False unless `x = y = z`: for `(1, 2, 3)` the absolute difference tends to `-0.0381…` as `p → 0`, so the relative error is of order `1/ln(1/p)`. Carlson–Gustafson (1994, (42)) give `R_J = (3/(2√(xyz)))(ln(4f/p) - 2 + r)` with `-ln(f/H) < r < (3p/(2(f-p))) ln(f/p)`, `H` the harmonic mean. Acquired in that form (non-strict bounds; checked on 400 random triples with `0 < p < f`).
- **19.28.9** (missing hypothesis): DLMF assumes only `x, y > 0`. The identity holds for `x + y ≤ π/2` and fails beyond (at `x = 2, y = 1.3` the sides are `2.6343` and `6.3569`; at `x = y = 0.8` they differ by `0.0918`). Acquired with the added hypothesis `x + y ≤ π/2`.
- **19.29.8** (restriction): the fifth factor is assumed nonzero on `[y, x]`; DLMF's principal-value reading of the left side when `a_5 + b_5 t` vanishes inside `(y, x)` is not covered (the principal values on the right side are built into `symEllIntRJ`, `symEllIntRC`).
- **§19.29(iii)** (convergence): DLMF assumes only positivity on the open interval, which allows non-integrable endpoint behaviour (double zeros, e.g. `Q₁ = Q₂ = 1 - t²` on `(0, 1)`). The theorems for (19.29.19)–(19.29.21), the degenerate case, (19.29.24), (19.29.26), (19.29.27), (19.29.30) carry an explicit `IntegrableOn` hypothesis; (19.29.21) and (19.29.28) need `0 < y` (at `y = 0`, resp. `a = y = 0`, the integral diverges); (19.29.32) needs `a ≠ 0 ∨ 0 < y` and `y < x` (DLMF: `0 ≤ y ≤ x`, `U` undefined at `x = y`).
- **19.29.15, 19.29.18**: proved under explicit integrability hypotheses (convergence implicit in DLMF) and otherwise for arbitrary complex data; **19.29.16** proved with the three radicands in `ℂ \ (-∞, 0]` on `[y, x]` (DLMF's endpoint values `s(x)/(a_α + b_α x)` require `a_α + b_α x ≠ 0`).

### Upstream and `lean-codes` reuse (§19.27–19.29)

Mathlib has no Carlson symmetric integrals, so no `dlmf_upstream` pointers apply. Reused from
`lean-codes` (package `LeanCodes`, imported, not copied): `Carlson.integral_quartic_eq_carlsonRF`
(9.8-12) for 19.29.4; `Carlson.integral_quadratic_mul_quadratic` (Exercise 9.8-3) for 19.29.19;
`Carlson.isEquivalent_carlsonRF_atTop` (9.2-10) and `Carlson.isEquivalent_carlsonRK_zero`
(8.3-16) for the leading term of 19.27.2. Carlson's reduction Tables 9.3-1–9.3-4 concern the
contiguous relations of §19.20–19.21 rather than §19.29 and are left to those sections.

## Excluded sections (part E: §19.3, §19.17, §§19.30–19.39)

- [§19.3](https://dlmf.nist.gov/19.3) and [§19.17](https://dlmf.nist.gov/19.17) (Graphics): excluded: graphics. No numbered formulas.
- [§19.30](https://dlmf.nist.gov/19.30) Lengths of Plane Curves (19.30.E1–E13): excluded: application. The mathematical content consists of instances of acquired results: the ellipse arc length `s/a = E(φ, k) = R_F(c-1, c-k², c) - (k²/3) R_D(c-1, c-k², c)` with `c = csc²φ` (19.30.3; DLMF points to 19.25.10 of part D for a cancellation-free form), the perimeter `L(a, b) = 4aE(k) = 8R_G(0, a², b²)` (19.30.5, from 19.25.1; compare 19.9.9 of part B), 19.30.6 (from 19.4.6), the hyperbola arc length 19.30.9 (from 19.29.7, acquired here as `ellRed_integral_ratio_s`) and the lemniscate arc length and perimeter 19.30.11–19.30.13, including `P = 4√(2a²) R_F(0, 1, 2) = 4aK(1/√2)` (decimal values excluded: numerical).
- [§19.31](https://dlmf.nist.gov/19.31) Probability Distributions (19.31.E1–E2): excluded: application. 19.31.2 (the Gaussian expectation of a ratio of quadratic forms as an `R_{-a}` function) is a direct instance of the definition of `R_{-a}` as an average over the simplex.
- [§19.32](https://dlmf.nist.gov/19.32) Conformal Map onto a Rectangle (19.32.E1–E4): excluded: application. The map `z(p) = R_F(p - x₁, p - x₂, p - x₃)` and its corner values 19.32.4 are specializations of `symEllIntRF`.
- [§19.33](https://dlmf.nist.gov/19.33) Triaxial Ellipsoids (19.33.E1–E12): excluded: application. Mathematical content: the surface area `S = 3V R_G(a⁻², b⁻², c⁻²)` (19.33.1) and 19.33.2, the electrostatic capacity `1/C = R_F(a², b², c²)` (19.33.5), the depolarization factors `L_c = V R_D(a², b², c²)` with `L_a + L_b + L_c = 4π` (19.33.7, 19.33.8, the latter an instance of 19.21.8), and 19.33.11. These are physics identities built from acquired functions; not acquired.
- [§19.34](https://dlmf.nist.gov/19.34) Mutual Inductance of Coaxial Circles (19.34.E1–E7): excluded: application. 19.34.3–19.34.7 express the inductance through `R_{-3/2}(3/2, 3/2; r₊², r₋²)`, `R_F` and `R_D`; they are instances of 19.16 and 19.25 identities.
- [§19.35](https://dlmf.nist.gov/19.35) Other Applications: excluded: application (pointers only; no numbered formulas).
- [§19.36](https://dlmf.nist.gov/19.36) Methods of Computation (19.36.E1–E13): excluded: computation. 19.36.1, 19.36.2 are truncations of the series (19.19.7) used as approximations with error bounds; 19.36.3–19.36.5 are a worked numerical example (excluded: numerical); 19.36.6–19.36.13 are AGM and quadratic-transformation algorithms whose underlying identities are 19.8 and 19.22 (acquired in parts A and C).
- [§19.37](https://dlmf.nist.gov/19.37) Tables: excluded: numerical.
- [§19.38](https://dlmf.nist.gov/19.38) Approximations: excluded: numerical.
- [§19.39](https://dlmf.nist.gov/19.39) Software: excluded: software (pointers only).

## Validation (part E) and whole-chapter exclusion notes

- Modules `DLMF.EllipticIntegrals.SymmetricAsymptotics`, `DLMF.EllipticIntegrals.SymmetricIntegralsOfIntegrals`, `DLMF.EllipticIntegrals.SymmetricReduction` build with `lake build`, and each passes `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false` with only `sorry` warnings. There are no axioms, no `native_decide` and no `sorry` in helper declarations (prefix `ei19e_`).
- Admissions (`grep -c '\bsorry\b'`): SymmetricAsymptotics 15, SymmetricIntegralsOfIntegrals 10, SymmetricReduction 15.
- Counts: 59 numbered formulas in scope (19.27: 16, 19.28: 10, 19.29: 33), all covered; 80 tagged declarations (24 definitions, 16 proved theorems, 40 admitted). Three of the proved theorems (19.29.26, 19.29.27, 19.29.32/33) rest on admitted statements.
- `#print axioms` for `ellRedI_cubic_recurrence`, `ellRedI_recurrence`, `ellRed_integral_inv_s_of_pos`, `ellRedS5_sq_sub_Q5Sq`, `ellRed_quad_first_of_pos`, `symEllIntRF_zero_isEquivalent`, `symEllIntRF_isEquivalent_atTop`: `[propext, Classical.choice, Quot.sound]`.
- Every numbered formula of §§19.27–19.29 was checked numerically with mpmath before it was stated; corrections are listed above.
- Whole chapter: graphics (§19.3, §19.17), applications (§§19.30–19.35), computation, tables, approximations and software (§§19.36–19.39) are excluded as listed; the numbered formulas there (51: 19.30: 13, 19.31: 2, 19.32: 4, 19.33: 12, 19.34: 7, 19.36: 13) are not acquired.
