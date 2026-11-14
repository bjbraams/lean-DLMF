# Temme Chapter12 acquisition ledger

All **15** entries and their distinct subclaims are audited in lookup order Mathlib,
TauCeti, DLMF. Pins: Mathlib `1b1ccf4b088b32fa3f23f2de1127433254a81e1e`, TauCeti
`396c3bd971e9722aa8656231760e710fe641d8cf`, Lean `v4.36.0-rc2`. The source synopsis,
pins and existing definition bodies are unchanged. “Existing” does not imply proved;
the transitive Lean axiom audit below distinguishes proofs, admissions and dependence on
admissions. Newly admitted statements remain in the theorem layer; defining APIs are proved.

## TEM-12-01 — Complete integrals and special values (12.1)–(12.4), pp. 315–316.

Pinned TauCeti `TauCeti.Real.legendreK`, `TauCeti.Real.legendreEc` give the exact real modulus
integrals; the local parameter versions are `DLMF.Elliptic.Real.completeEllipticKOfParameter` and
`DLMF.Elliptic.Real.completeEllipticEOfParameter`, at m=k^2. Existing
`DLMF.Elliptic.Real.completeEllipticKOfParameter_eq_ordinaryHypergeometric`,
`DLMF.Elliptic.Real.completeEllipticEOfParameter_eq_ordinaryHypergeometric`,
`DLMF.Elliptic.Real.completeEllipticKOfParameter_zero`,
`DLMF.Elliptic.Real.completeEllipticEOfParameter_zero`, and
`DLMF.Elliptic.Real.completeEllipticEOfParameter_one` give both hypergeometric forms and all exact
endpoint values. TauCeti `TauCeti.Real.tendsto_legendreK_nhdsLT_one` gives actual divergence, not
a totalized value at one. The complement is substitution sqrt(1-k^2), not differentiation.
`TauCeti.Green.Examples.integral_norm_deriv_ellipse` covers the entire a>=b>0 perimeter domain,
including the circle; local `DLMF.Elliptic.ellipsePerimeter_eq` independently covers all positive
semiaxes. TauCeti `TauCeti.Real.legendreK_one_div_sqrt_two` and
`TauCeti.Real.legendreEc_one_div_sqrt_two` are the exact two lemniscatic Gamma values. No
numerical constants are acquired.

Checked named coverage: 14 declarations; 0 depend on admissions.

## TEM-12-02 — Pendulum period, §12.1.1, pp. 316–318.

Pinned TauCeti `Real.pendulumAngle`, `Real.pendulumPeriod`, `Real.pendulumAngle_periodic`,
`Real.isLeast_pendulumPeriod`, `Real.tendsto_pendulumPeriod_nhds_zero`, and
`Real.tendsto_pendulumPeriod_nhdsLT_pi` give the actual solution, least period, small-angle limit
and separatrix divergence. Substitute omega=sqrt(g/L); positive L,g justify 1/omega=sqrt(L/g). New
`DLMF.Elliptic.Real.intervalIntegrable_pendulum_energy_kernel` and
`DLMF.Elliptic.Real.integral_pendulum_energy_eq_completeEllipticK` record the full energy
substitution through its integrable turning point: the source integral equals
sqrt(2)K(sin(alpha/2)), and its physical quarter-period prefactor is sqrt(L/(2g)).

Checked named coverage: 8 declarations; 2 depend on admissions.

## TEM-12-03 — AGM convergence and invariance (12.5)–(12.8), p. 318.

Mathlib `NNReal.agmSequences`, `NNReal.agmSequences_succ'`, `NNReal.agmSequences_fst_monotone`,
`NNReal.agmSequences_snd_antitone`, `NNReal.agmSequences_fst_le_snd`,
`NNReal.tendsto_agmSequences_fst_agm`, `NNReal.tendsto_agmSequences_snd_agm`, `NNReal.agm_comm`,
`NNReal.agm_mul_distrib`, and `NNReal.agm_eq_agm_gm_am` give all order, convergence, symmetry,
homogeneity and invariance claims on positive inputs. The Mathlib sequence begins after the first
mean step; local `DLMF.EllipticIntegrals.agmSeq_succ` and `DLMF.EllipticIntegrals.tendsto_agmSeq`
retain the book's n=0 convention. New proved `Real.add_div_two_sub_sqrt_mul_eq` and
`Real.add_div_two_sub_sqrt_mul_le` give the exact quadratic one-step gap and the smaller-input
bound. Apply these at a_n,b_n; monotonicity b_n>=b_0 and positive denominator comparison give the
stated bound with 8b_0. Mathlib `NNReal.agm_pos` gives positivity of the common limit.

Checked named coverage: 15 declarations; 0 depend on admissions.

## TEM-12-04 — Gauss AGM integral, Theorem 12.1, (12.9)–(12.10), pp. 319–320.

Existing `DLMF.EllipticIntegrals.inv_agm_eq_integral` is exactly the homogeneous Gauss integral
for all positive inputs, using the canonical NNReal AGM and both source initial values. Existing
`DLMF.Elliptic.Real.completeEllipticKOfParameter_eq_pi_div_agm` and TauCeti
`TauCeti.Real.legendreK_eq_pi_div_two_mul_agm` give the K specialization. These are proved
statements; no separate acquisition of the printed a=1 theorem is needed.

Checked named coverage: 3 declarations; 0 depend on admissions.

## TEM-12-05 — Landen transformations and derivatives (12.11)–(12.14), p. 320 and Exercise 12.1.

Pinned TauCeti `TauCeti.Real.legendreK_eq_one_add_mul_legendreK`,
`TauCeti.Real.legendreK_two_mul_sqrt_div_one_add`,
`TauCeti.Real.legendreEc_eq_one_add_mul_legendreEc`, and
`TauCeti.Real.legendreEc_two_mul_sqrt_div_one_add` give all four transformations on the precise
real source domain. Local `DLMF.Elliptic.Real.completeEllipticKOfParameter_landen_descending`,
`DLMF.Elliptic.Real.completeEllipticKOfParameter_landen_ascending`,
`DLMF.Elliptic.Real.completeEllipticEOfParameter_landen_descending`, and
`DLMF.Elliptic.Real.completeEllipticEOfParameter_landen_ascending` give the same forms with m=k^2.
Existing `DLMF.Elliptic.Real.hasDerivAt_completeEllipticKOfParameter_sq` and
`DLMF.Elliptic.Real.hasDerivAt_completeEllipticEOfParameter_sq` give both modulus derivatives with
k!=0 and k^2<1. No zero-denominator substitution at endpoints is made.

Checked named coverage: 10 declarations; 0 depend on admissions.

## TEM-12-06 — Incomplete integrals (12.15)–(12.20), pp. 321–322.

Pinned TauCeti `TauCeti.Real.legendreF`, `TauCeti.Real.legendreE`, `TauCeti.Real.legendrePi` give
all three real-amplitude integral definitions, with characteristic n rather than a squared
characteristic silently changed. `TauCeti.Real.legendreF_eq_integral_algebraic`,
`TauCeti.Real.legendreE_eq_integral_algebraic`, and
`TauCeti.Real.legendrePi_eq_integral_algebraic` include the entire closed amplitude interval
|phi|<=pi/2. The local period-splitting APIs
`DLMF.Elliptic.Real.incompleteEllipticFOfParameter_add_pi`,
`DLMF.Elliptic.Real.incompleteEllipticEOfParameter_add_pi`, and
`DLMF.Elliptic.Real.incompleteEllipticPiOfParameter_add_pi` retain all complete-period
contributions for other amplitudes. `TauCeti.Real.legendreF_one_modulus` and
`TauCeti.Real.legendreE_one_modulus` give artanh(sin phi) and sin phi at modulus one on their
convergent domains. New `DLMF.Elliptic.Real.not_intervalIntegrable_ellipticF_one` records actual
failure of integrability whenever the interval reaches or crosses either first singular endpoint;
a totalized zero integral is never called infinite.

Checked named coverage: 12 declarations; 1 depend on admissions.

## TEM-12-07 — Jacobi inverse functions (12.21)–(12.25), pp. 322–323.

Existing `DLMF.Elliptic.Real.strictMono_incompleteEllipticFOfParameter`,
`DLMF.Elliptic.Real.surjective_incompleteEllipticFOfParameter`,
`DLMF.Elliptic.Real.jacobiAmOfParameter`, and
`DLMF.Elliptic.Real.incompleteEllipticFOfParameter_jacobiAmOfParameter` give the global inverse.
Existing `DLMF.Elliptic.Real.jacobiSnOfParameter`, `DLMF.Elliptic.Real.jacobiCnOfParameter`,
`DLMF.Elliptic.Real.jacobiDnOfParameter`, their three derivative lemmas,
`DLMF.Elliptic.Real.jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq`,
`DLMF.Elliptic.Real.mul_jacobiSnOfParameter_sq_add_jacobiDnOfParameter_sq`,
`DLMF.Elliptic.Real.jacobiSnOfParameter_deriv_sq`,
`DLMF.Elliptic.Real.jacobi_add_two_completeEllipticKOfParameter`, and
`DLMF.Elliptic.jacobi_zero_param` give every real algebraic, derivative, shift and k=0 claim, with
m=k^2. The complex continuation uses canonical theta-quotient `DLMF.JacobiElliptic.jacobiSn`,
`DLMF.JacobiElliptic.jacobiCn`, `DLMF.JacobiElliptic.jacobiDn`; their meromorphicity and
two-period APIs retain poles. Existing `DLMF.JacobiElliptic.jacobiSn_ofReal`,
`DLMF.JacobiElliptic.jacobiCn_ofReal`, `DLMF.JacobiElliptic.jacobiDn_ofReal` are the bridge, not a
copied definition. `DLMF.JacobiElliptic.tendsto_jacobiSn_one`,
`DLMF.JacobiElliptic.tendsto_jacobiCn_one`, `DLMF.JacobiElliptic.tendsto_jacobiDn_one` give the
actual hyperbolic endpoint continuation on the entire real line. This is a limit/extension
convention: neither the local m<1 inverse nor TauCeti's k^2<1 inverse assigns those values at its
totalized k=1 argument.

Checked named coverage: 21 declarations; 0 depend on admissions.

## TEM-12-08 — Poisson summation, Theorem 12.2, pp. 326–327, corrected target.

New `Real.tendsto_sum_Icc_twistedFourier_of_boundedVariationOn` in
DLMFMathlib/Analysis/Fourier/ShiftedPoisson states the whole corrected Theorem 12.2: only global
bounded variation and L1 are assumed, samples use both one-sided limits, spacing may have either
nonzero sign, and the Fourier limit is symmetric ordered. The sampling side is norm-summable; the
Fourier side is not asserted norm-summable. Existing AAR PoissonBoundedVariation adds an
integrable decreasing envelope and does not alone cover this hypothesis set. For the Gaussian,
existing `DLMF.Theta.jacobiThetaThreeTau_neg_inv` at z=0,tau=i*s, together with positive-real
principal square roots and the Gaussian theta series, gives exactly the displayed transformed
Gaussian sum for every s>0.

Checked named coverage: 2 declarations; 1 depend on admissions.

## TEM-12-09 — Elliptic-function structure, (12.26) and Exercises 12.4–12.5, pp. 323, 331.

Mathlib `PeriodPair` represents the nondegenerate lattice, with the source generators doubled.
Existing `DLMF.Weierstrass.exists_eq_const_of_periodic_of_order_nonneg` gives the entire
elliptic-function constant theorem. Shared root acquisition `PeriodPair.openPeriodCell`,
`PeriodPair.poleMultiplicity`, `PeriodPair.zeroMultiplicity`, `PeriodPair.poleCount`,
`PeriodPair.valueCount`, `PeriodPair.finite_poles_openPeriodCell`,
`PeriodPair.finsum_residue_openPeriodCell_eq_zero`, `PeriodPair.two_le_poleCount`, and
`PeriodPair.valueCount_eq_poleCount` give the full residue, multiplicity and every-value
assertions with the exact boundary exclusions. Take c=0 for equality of zero and pole
multiplicities. Nonconstancy is tested at regular points, so arbitrary assigned values at poles
cannot manufacture a nonconstant meromorphic function. Distinct-point cardinalities are not
substituted for multiplicities.

Checked named coverage: 11 declarations; 4 depend on admissions.

## TEM-12-10 — Weierstrass function (12.27)–(12.28), p. 324 and Exercise 12.6.

Mathlib `PeriodPair.weierstrassP`, `PeriodPair.hasSumLocallyUniformly_weierstrassP`,
`PeriodPair.weierstrassP_neg`, `PeriodPair.weierstrassP_add_coe`, and its derivative API provide
the actual lattice series, normal convergence, parity and periodicity. The Weierstrass
foundational layer records the double and triple pole orders and the defining invariant sums.
Existing `DLMF.Weierstrass.HalfPeriods.derivWeierstrassP_sq_eq_prod`,
`DLMF.Weierstrass.deriv_derivWeierstrassP`, `DLMF.Weierstrass.weierstrassP_laurent`,
`DLMF.Weierstrass.laurentCoeff_two`, and `DLMF.Weierstrass.laurentCoeff_three` give the cubic
equation, second derivative, convergent Laurent expansion and g2/20,g3/28 coefficients. The
product cubic expands by the existing invariant-root identities. The analytic remaining Laurent
tail starts at z^6 and hence is O(z^6). Shared root
`DLMF.Weierstrass.exists_polynomial_weierstrass_representation` gives precisely
(A(wp)+wp'B(wp))/C(wp) with C nonzero and a nonempty common regular locus; it is a genuine
meromorphic rational representation.

Checked named coverage: 10 declarations; 1 depend on admissions.

## TEM-12-11 — Theta definitions (12.29), pp. 324–325.

Existing canonical `DLMF.Elliptic.jacobiThetaOneTau`, `DLMF.Elliptic.jacobiThetaTwoTau`,
`DLMF.Elliptic.jacobiThetaThreeTau`, `DLMF.Elliptic.jacobiThetaFourTau`, and
`DLMF.Theta.jacobiThetaOneTau_hasSum_sin`, `DLMF.Theta.jacobiThetaTwoTau_hasSum_cos`,
`DLMF.Theta.hasSum_jacobiThetaThreeTau`, `DLMF.Elliptic.jacobiThetaFourTau_eq_tsum` give all four
exact source series with tau-defined powers. Existing `DLMF.Theta.differentiable_jacobiThetaTau`
gives entirety in the angular argument, and the four negation lemmas give all parities. New
`DLMF.Theta.tendstoLocallyUniformlyOn_jacobiThetaTau_series` gives joint locally uniform
convergence of all four actual finite partial sums on C times the upper half-plane. New
`DLMF.Theta.analyticOnNhd_jacobiThetaTau_joint` gives joint analyticity. New
`DLMF.Theta.deriv_jacobiThetaTau_tau` gives the exact angular heat equation, with coefficient
-i*pi/4. Separate fixed-parameter differentiability alone was not used as a substitute for joint
series convergence.

Checked named coverage: 12 declarations; 3 depend on admissions.

## TEM-12-12 — Theta shifts and zeros, pp. 325–326.

Existing `DLMF.Theta.jacobiThetaOneTau_add_lattice`, `DLMF.Theta.jacobiThetaTwoTau_add_lattice`,
`DLMF.Theta.jacobiThetaThreeTau_add_lattice`, `DLMF.Theta.jacobiThetaFourTau_add_lattice` at
(m,n)=(1,0),(0,1) give all full-period and quasiperiod multipliers. Existing
`DLMF.Theta.jacobiThetaOneTau_half_periods`, `DLMF.Theta.jacobiThetaTwoTau_half_periods`,
`DLMF.Theta.jacobiThetaThreeTau_half_periods`, `DLMF.Theta.jacobiThetaFourTau_half_periods` give
the four half-real shifts and the half-imaginary shifts needed for comparing zeros. Existing
`DLMF.Theta.jacobiThetaTau_eq_zero_iff` gives exactly the four complete zero lattices. Simplicity
is the elementary derivative consequence of `DLMF.Theta.jacobiThetaOneDerivNullTau_eq_mul` and
`DLMF.Theta.jacobiThetaNullTau_ne_zero` at zero, followed by differentiation of those nonvanishing
exponential shift multipliers. The term involving the multiplier derivative vanishes at a zero.
Thus every translated zero of every theta function has nonzero first derivative; no multiplicity
claim is inferred merely from the zero locations.

Checked named coverage: 11 declarations; 0 depend on admissions.

## TEM-12-13 — Jacobi–theta bridge (12.30), p. 326.

Existing canonical `DLMF.JacobiElliptic.jacobiLetterTheta`, `DLMF.JacobiElliptic.jacobiGlaisher`,
`DLMF.JacobiElliptic.jacobiPQ`, `DLMF.JacobiElliptic.jacobiThetaArgument`, and the sn,cn,dn
definitions unfold directly to the three source theta quotients, with tau=iK'/K and v=pi*u/(2K).
Existing `DLMF.JacobiElliptic.jacobi_inversion_k` gives the actual modulus and
complementary-modulus theta constants as well as the K constant, rather than only defining a new
modulus from theta constants. `DLMF.JacobiElliptic.jacobiPQ_eq_jacobiPQOfTau` and the real bridges
verify that the same canonical functions occur. Pointwise equality is interpreted away from
quotient poles, and the theta quotient gives its meromorphic continuation.

Checked named coverage: 6 declarations; 0 depend on admissions.

## TEM-12-14 — Imaginary modular transformation (12.31), pp. 327–328.

Existing `DLMF.Theta.jacobiThetaOneTau_neg_inv`, `DLMF.Theta.jacobiThetaTwoTau_neg_inv`,
`DLMF.Theta.jacobiThetaThreeTau_neg_inv`, and `DLMF.Theta.jacobiThetaFourTau_neg_inv` are all four
exact modular transformations on Im tau>0. They are written with z*(-1/tau): parity converts this
to the source z/tau. In particular, the odd theta-one transformation has -i before this sign
conversion and +i afterwards, precisely as in the synopsis. Divide by the nonzero principal
(-i*tau)^(1/2); its real part is positive on the upper half-plane and it is positive at purely
imaginary positive tau. No series at |q|>1 is asserted.

Checked named coverage: 4 declarations; 0 depend on admissions.

## TEM-12-15 — Carlson forms and duplication (12.32)–(12.34), p. 329.

Existing `DLMF.EllipticIntegrals.symmetricEllipticRF`,
`DLMF.EllipticIntegrals.symmetricEllipticRJ`, `DLMF.EllipticIntegrals.symmetricEllipticRD`,
`DLMF.EllipticIntegrals.CarlsonNonnegDomain`, their nonnegative real integral theorems,
`DLMF.EllipticIntegrals.symmetricEllipticRF_comm_left`,
`DLMF.EllipticIntegrals.symmetricEllipticRF_comm_right`,
`DLMF.EllipticIntegrals.symmetricEllipticRJ_comm_left`,
`DLMF.EllipticIntegrals.symmetricEllipticRJ_comm_right`, and the defining equation of
`DLMF.EllipticIntegrals.symmetricEllipticRD` give exactly the three forms, all symmetric
first-three-argument permutations, and the positive z restriction for RD. Existing
`DLMF.EllipticIntegrals.symmetricEllipticRF_scale`,
`DLMF.EllipticIntegrals.symmetricEllipticRJ_scale`,
`DLMF.EllipticIntegrals.symmetricEllipticRD_scale` give positive scaling with powers -1/2,-3/2.
Existing `DLMF.EllipticIntegrals.incompleteEllipticF_eq_symmetricEllipticRF`,
`DLMF.EllipticIntegrals.incompleteEllipticE_eq_symmetricEllipticRF_sub_one_third_symmetricEllipticRD`,
and `DLMF.EllipticIntegrals.incompleteEllipticPi_eq_symmetricEllipticR_csc_sq` give the full
source reductions after homogeneous rescaling from csc^2 phi to the unit third argument. The
endpoint phi=pi/2 is included by the csc form; phi=0 is the separate zero value and negative phi
follows by oddness of each amplitude integral and sin phi. Existing
`DLMF.EllipticIntegrals.symmetricEllipticRF_duplication`,
`DLMF.EllipticIntegrals.symmetricEllipticRF_duplication_zero`, and
`DLMF.EllipticIntegrals.symmetricEllipticRF_duplication_quarter` cover positive arguments and
every allowed single zero, including the scaled-by-four form. Existing
`DLMF.EllipticIntegrals.symmetricEllipticRF_self` gives the common-positive-argument reciprocal
square root. The generic Carlson integral APIs are imported directly from lean-codes, never copied
into this project.

Checked named coverage: 18 declarations; 0 depend on admissions.

## Validation

All 15 entries are mapped. The transitive `#print axioms` audit checked **156** distinct
declarations; **12** depend on admissions. The **4** new modules
owned by this supplement contain **9** public declarations, including
**7** directly admitted targets. Definitions and their
defining equations have no admissions. Every new module has passed a direct strict Lean check
with `autoImplicit=false` and `relaxedAutoImplicit=false`; modules are registered in their
area umbrellas. Repository-wide build and import integration are coordinated with the other
book acquisitions and reported separately.

The per-entry declaration locations and proof statuses are retained in
[reports/BookAcquisition-Temme-Chapter12.tsv](reports/BookAcquisition-Temme-Chapter12.tsv). No additional
source erratum or user approval question was identified in this supplement.

## Checked declaration index

- [DLMF.Elliptic.Real.completeEllipticEOfParameter](DLMF/Elliptic/Basic/Integrals.lean#L66) — definition, no admission.
- [DLMF.Elliptic.Real.completeEllipticEOfParameter_eq_ordinaryHypergeometric](DLMF/Elliptic/Complete.lean#L431) — proved, no admission.
- [DLMF.Elliptic.Real.completeEllipticEOfParameter_landen_ascending](DLMF/Elliptic/AGM.lean#L449) — proved, no admission.
- [DLMF.Elliptic.Real.completeEllipticEOfParameter_landen_descending](DLMF/Elliptic/AGM.lean#L388) — proved, no admission.
- [DLMF.Elliptic.Real.completeEllipticEOfParameter_one](DLMF/Elliptic/Complete.lean#L235) — proved, no admission.
- [DLMF.Elliptic.Real.completeEllipticEOfParameter_zero](DLMF/Elliptic/Complete.lean#L230) — proved, no admission.
- [DLMF.Elliptic.Real.completeEllipticKOfParameter](DLMF/Elliptic/Basic/Integrals.lean#L60) — definition, no admission.
- [DLMF.Elliptic.Real.completeEllipticKOfParameter_eq_ordinaryHypergeometric](DLMF/Elliptic/Complete.lean#L422) — proved, no admission.
- [DLMF.Elliptic.Real.completeEllipticKOfParameter_eq_pi_div_agm](DLMF/Elliptic/AGM.lean#L320) — proved, no admission.
- [DLMF.Elliptic.Real.completeEllipticKOfParameter_landen_ascending](DLMF/Elliptic/AGM.lean#L359) — proved, no admission.
- [DLMF.Elliptic.Real.completeEllipticKOfParameter_landen_descending](DLMF/Elliptic/AGM.lean#L332) — proved, no admission.
- [DLMF.Elliptic.Real.completeEllipticKOfParameter_zero](DLMF/Elliptic/Complete.lean#L226) — proved, no admission.
- [DLMF.Elliptic.Real.hasDerivAt_completeEllipticEOfParameter_sq](DLMF/Elliptic/Complete.lean#L465) — proved, no admission.
- [DLMF.Elliptic.Real.hasDerivAt_completeEllipticKOfParameter_sq](DLMF/Elliptic/Complete.lean#L451) — proved, no admission.
- [DLMF.Elliptic.Real.incompleteEllipticEOfParameter_add_pi](DLMF/Elliptic/Basic/Amplitude.lean#L87) — proved, no admission.
- [DLMF.Elliptic.Real.incompleteEllipticFOfParameter_add_pi](DLMF/Elliptic/Basic/Amplitude.lean#L80) — proved, no admission.
- [DLMF.Elliptic.Real.incompleteEllipticFOfParameter_jacobiAmOfParameter](DLMF/Elliptic/Basic/Jacobi.lean#L68) — proved, no admission.
- [DLMF.Elliptic.Real.incompleteEllipticPiOfParameter_add_pi](DLMF/Elliptic/ThirdKind.lean#L90) — proved, no admission.
- [DLMF.Elliptic.Real.integral_pendulum_energy_eq_completeEllipticK](DLMF/Elliptic/PendulumEnergy.lean#L36) — direct admission.
- [DLMF.Elliptic.Real.intervalIntegrable_pendulum_energy_kernel](DLMF/Elliptic/PendulumEnergy.lean#L28) — direct admission.
- [DLMF.Elliptic.Real.jacobiAmOfParameter](DLMF/Elliptic/Basic/Amplitude.lean#L184) — definition, no admission.
- [DLMF.Elliptic.Real.jacobiCnOfParameter](DLMF/Elliptic/Basic/Amplitude.lean#L191) — definition, no admission.
- [DLMF.Elliptic.Real.jacobiDnOfParameter](DLMF/Elliptic/Basic/Amplitude.lean#L194) — definition, no admission.
- [DLMF.Elliptic.Real.jacobiSnOfParameter](DLMF/Elliptic/Basic/Amplitude.lean#L188) — definition, no admission.
- [DLMF.Elliptic.Real.jacobiSnOfParameter_deriv_sq](DLMF/Elliptic/JacobiIdentities.lean#L63) — proved, no admission.
- [DLMF.Elliptic.Real.jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq](DLMF/Elliptic/Basic/Jacobi.lean#L133) — proved, no admission.
- [DLMF.Elliptic.Real.jacobi_add_two_completeEllipticKOfParameter](DLMF/Elliptic/Basic/Jacobi.lean#L209) — proved, no admission.
- [DLMF.Elliptic.Real.mul_jacobiSnOfParameter_sq_add_jacobiDnOfParameter_sq](DLMF/Elliptic/Basic/Jacobi.lean#L139) — proved, no admission.
- [DLMF.Elliptic.Real.not_intervalIntegrable_ellipticF_one](DLMF/Elliptic/PendulumEnergy.lean#L46) — direct admission.
- [DLMF.Elliptic.Real.strictMono_incompleteEllipticFOfParameter](DLMF/Elliptic/Basic/Amplitude.lean#L135) — proved, no admission.
- [DLMF.Elliptic.Real.surjective_incompleteEllipticFOfParameter](DLMF/Elliptic/Basic/Amplitude.lean#L142) — proved, no admission.
- [DLMF.Elliptic.ellipsePerimeter_eq](DLMF/Elliptic/SpecialValues.lean#L211) — proved, no admission.
- [DLMF.Elliptic.jacobiThetaFourTau](DLMF/Elliptic/Basic/Theta.lean#L42) — definition, no admission.
- [DLMF.Elliptic.jacobiThetaFourTau_eq_tsum](DLMF/Elliptic/Basic/ThetaPeriodicity.lean#L41) — proved, no admission.
- [DLMF.Elliptic.jacobiThetaOneTau](DLMF/Elliptic/Basic/Theta.lean#L51) — definition, no admission.
- [DLMF.Elliptic.jacobiThetaThreeTau](DLMF/Elliptic/Basic/Theta.lean#L38) — definition, no admission.
- [DLMF.Elliptic.jacobiThetaTwoTau](DLMF/Elliptic/Basic/Theta.lean#L46) — definition, no admission.
- [DLMF.Elliptic.jacobi_zero_param](DLMF/Elliptic/Basic/Jacobi.lean#L264) — proved, no admission.
- [DLMF.EllipticIntegrals.CarlsonNonnegDomain](DLMF/EllipticIntegrals/SymmetricAddition.lean#L97) — definition, no admission.
- [DLMF.EllipticIntegrals.agmSeq_succ](DLMF/EllipticIntegrals/Quadratic.lean#L96) — proved, no admission.
- [DLMF.EllipticIntegrals.incompleteEllipticE_eq_symmetricEllipticRF_sub_one_third_symmetricEllipticRD](DLMF/EllipticIntegrals/LegendreSymmetricForms.lean#L467) — proved, no admission.
- [DLMF.EllipticIntegrals.incompleteEllipticF_eq_symmetricEllipticRF](DLMF/EllipticIntegrals/SymmetricRelations.lean#L255) — proved, no admission.
- [DLMF.EllipticIntegrals.incompleteEllipticPi_eq_symmetricEllipticR_csc_sq](DLMF/EllipticIntegrals/LegendreSymmetricForms.lean#L525) — proved, no admission.
- [DLMF.EllipticIntegrals.inv_agm_eq_integral](DLMF/EllipticIntegrals/Quadratic.lean#L164) — proved, no admission.
- [DLMF.EllipticIntegrals.symmetricEllipticRD](DLMF/EllipticIntegrals/Basic/Symmetric.lean#L105) — definition, no admission.
- [DLMF.EllipticIntegrals.symmetricEllipticRD_scale](DLMF/EllipticIntegrals/LegendreSymmetricForms.lean#L707) — proved, no admission.
- [DLMF.EllipticIntegrals.symmetricEllipticRF](DLMF/EllipticIntegrals/Basic/Symmetric.lean#L81) — definition, no admission.
- [DLMF.EllipticIntegrals.symmetricEllipticRF_comm_left](DLMF/EllipticIntegrals/Basic/SymmetricProperties.lean#L106) — proved, no admission.
- [DLMF.EllipticIntegrals.symmetricEllipticRF_comm_right](DLMF/EllipticIntegrals/Basic/SymmetricProperties.lean#L112) — proved, no admission.
- [DLMF.EllipticIntegrals.symmetricEllipticRF_duplication](DLMF/EllipticIntegrals/SymmetricAddition.lean#L921) — proved, no admission.
- [DLMF.EllipticIntegrals.symmetricEllipticRF_duplication_quarter](DLMF/EllipticIntegrals/SymmetricAddition.lean#L983) — proved, no admission.
- [DLMF.EllipticIntegrals.symmetricEllipticRF_duplication_zero](DLMF/EllipticIntegrals/SymmetricAddition.lean#L937) — proved, no admission.
- [DLMF.EllipticIntegrals.symmetricEllipticRF_scale](DLMF/EllipticIntegrals/LegendreSymmetricForms.lean#L664) — proved, no admission.
- [DLMF.EllipticIntegrals.symmetricEllipticRF_self](DLMF/EllipticIntegrals/SymmetricSpecialCases.lean#L252) — proved, no admission.
- [DLMF.EllipticIntegrals.symmetricEllipticRJ](DLMF/EllipticIntegrals/Basic/Symmetric.lean#L88) — definition, no admission.
- [DLMF.EllipticIntegrals.symmetricEllipticRJ_comm_left](DLMF/EllipticIntegrals/Basic/SymmetricProperties.lean#L119) — proved, no admission.
- [DLMF.EllipticIntegrals.symmetricEllipticRJ_comm_right](DLMF/EllipticIntegrals/Basic/SymmetricProperties.lean#L125) — proved, no admission.
- [DLMF.EllipticIntegrals.symmetricEllipticRJ_scale](DLMF/EllipticIntegrals/LegendreSymmetricForms.lean#L679) — proved, no admission.
- [DLMF.EllipticIntegrals.tendsto_agmSeq](DLMF/EllipticIntegrals/Quadratic.lean#L108) — proved, no admission.
- [DLMF.JacobiElliptic.jacobiCn](DLMF/JacobiElliptic/Basic/Definitions.lean#L178) — definition, no admission.
- [DLMF.JacobiElliptic.jacobiCn_ofReal](DLMF/JacobiElliptic/SpecialValues/RealAndHalfPeriods.lean#L149) — proved, no admission.
- [DLMF.JacobiElliptic.jacobiDn](DLMF/JacobiElliptic/Basic/Definitions.lean#L181) — definition, no admission.
- [DLMF.JacobiElliptic.jacobiDn_ofReal](DLMF/JacobiElliptic/SpecialValues/RealAndHalfPeriods.lean#L156) — proved, no admission.
- [DLMF.JacobiElliptic.jacobiGlaisher](DLMF/JacobiElliptic/Basic/Definitions.lean#L112) — definition, no admission.
- [DLMF.JacobiElliptic.jacobiLetterTheta](DLMF/JacobiElliptic/Basic/Definitions.lean#L103) — definition, no admission.
- [DLMF.JacobiElliptic.jacobiPQ](DLMF/JacobiElliptic/Basic/Definitions.lean#L168) — definition, no admission.
- [DLMF.JacobiElliptic.jacobiPQ_eq_jacobiPQOfTau](DLMF/JacobiElliptic/ModulusInversion.lean#L828) — proved, no admission.
- [DLMF.JacobiElliptic.jacobiSn](DLMF/JacobiElliptic/Basic/Definitions.lean#L175) — definition, no admission.
- [DLMF.JacobiElliptic.jacobiSn_ofReal](DLMF/JacobiElliptic/SpecialValues/RealAndHalfPeriods.lean#L142) — proved, no admission.
- [DLMF.JacobiElliptic.jacobiThetaArgument](DLMF/JacobiElliptic/Basic/Definitions.lean#L159) — definition, no admission.
- [DLMF.JacobiElliptic.jacobi_inversion_k](DLMF/JacobiElliptic/ModulusInversion.lean#L788) — proved, no admission.
- [DLMF.JacobiElliptic.tendsto_jacobiCn_one](DLMF/JacobiElliptic/SpecialValues/ModulusLimits.lean#L570) — proved, no admission.
- [DLMF.JacobiElliptic.tendsto_jacobiDn_one](DLMF/JacobiElliptic/SpecialValues/ModulusLimits.lean#L642) — proved, no admission.
- [DLMF.JacobiElliptic.tendsto_jacobiSn_one](DLMF/JacobiElliptic/SpecialValues/ModulusLimits.lean#L498) — proved, no admission.
- [DLMF.Theta.analyticOnNhd_jacobiThetaTau_joint](DLMF/Theta/JointConvergence.lean#L50) — direct admission.
- [DLMF.Theta.deriv_jacobiThetaTau_tau](DLMF/Theta/JointConvergence.lean#L56) — direct admission.
- [DLMF.Theta.differentiable_jacobiThetaTau](DLMF/Theta/Basic/Analytic.lean#L51) — proved, no admission.
- [DLMF.Theta.hasSum_jacobiThetaThreeTau](DLMF/Theta/Basic/Series.lean#L127) — proved, no admission.
- [DLMF.Theta.jacobiThetaFourTau_add_lattice](DLMF/Theta/Basic/Periodicity.lean#L61) — proved, no admission.
- [DLMF.Theta.jacobiThetaFourTau_half_periods](DLMF/Theta/Basic/Periodicity.lean#L183) — proved, no admission.
- [DLMF.Theta.jacobiThetaFourTau_neg_inv](DLMF/Theta/Identities.lean#L1036) — proved, no admission.
- [DLMF.Theta.jacobiThetaNullTau_ne_zero](DLMF/Theta/SeriesAndZeros.lean#L235) — proved, no admission.
- [DLMF.Theta.jacobiThetaOneDerivNullTau_eq_mul](DLMF/Theta/Products/LogDerivativesAndDoubleProducts.lean#L865) — proved, no admission.
- [DLMF.Theta.jacobiThetaOneTau_add_lattice](DLMF/Theta/Basic/Periodicity.lean#L87) — proved, no admission.
- [DLMF.Theta.jacobiThetaOneTau_half_periods](DLMF/Theta/Basic/Periodicity.lean#L126) — proved, no admission.
- [DLMF.Theta.jacobiThetaOneTau_hasSum_sin](DLMF/Theta/Basic/Series.lean#L192) — proved, no admission.
- [DLMF.Theta.jacobiThetaOneTau_neg_inv](DLMF/Theta/Identities.lean#L1063) — proved, no admission.
- [DLMF.Theta.jacobiThetaTau_eq_zero_iff](DLMF/Theta/SeriesAndZeros.lean#L192) — proved, no admission.
- [DLMF.Theta.jacobiThetaThreeTau_add_lattice](DLMF/Theta/Basic/Periodicity.lean#L54) — proved, no admission.
- [DLMF.Theta.jacobiThetaThreeTau_half_periods](DLMF/Theta/Basic/Periodicity.lean#L162) — proved, no admission.
- [DLMF.Theta.jacobiThetaThreeTau_neg_inv](DLMF/Theta/Identities.lean#L1024) — proved, no admission.
- [DLMF.Theta.jacobiThetaTwoTau_add_lattice](DLMF/Theta/Basic/Periodicity.lean#L74) — proved, no admission.
- [DLMF.Theta.jacobiThetaTwoTau_half_periods](DLMF/Theta/Basic/Periodicity.lean#L146) — proved, no admission.
- [DLMF.Theta.jacobiThetaTwoTau_hasSum_cos](DLMF/Theta/Basic/Series.lean#L170) — proved, no admission.
- [DLMF.Theta.jacobiThetaTwoTau_neg_inv](DLMF/Theta/Identities.lean#L1049) — proved, no admission.
- [DLMF.Theta.tendstoLocallyUniformlyOn_jacobiThetaTau_series](DLMF/Theta/JointConvergence.lean#L29) — direct admission.
- [DLMF.Weierstrass.HalfPeriods.derivWeierstrassP_sq_eq_prod](DLMF/Weierstrass/DifferentialEquations.lean#L45) — proved, no admission.
- [DLMF.Weierstrass.deriv_derivWeierstrassP](DLMF/Weierstrass/DifferentialEquations.lean#L79) — proved, no admission.
- [DLMF.Weierstrass.exists_eq_const_of_periodic_of_order_nonneg](DLMF/Weierstrass/EllipticFunctionsAndInvariants.lean#L101) — proved, no admission.
- [DLMF.Weierstrass.exists_polynomial_weierstrass_representation](DLMF/Weierstrass/RationalRepresentation.lean#L27) — direct admission.
- [DLMF.Weierstrass.laurentCoeff_three](DLMF/Weierstrass/Series.lean#L516) — proved, no admission.
- [DLMF.Weierstrass.laurentCoeff_two](DLMF/Weierstrass/Series.lean#L511) — proved, no admission.
- [DLMF.Weierstrass.weierstrassP_laurent](DLMF/Weierstrass/Series.lean#L523) — proved, no admission.
- [NNReal.agmSequences](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ArithmeticGeometricMean.lean#L56) — definition, no admission.
- [NNReal.agmSequences_fst_le_snd](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ArithmeticGeometricMean.lean#L117) — proved, no admission.
- [NNReal.agmSequences_fst_monotone](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ArithmeticGeometricMean.lean#L111) — proved, no admission.
- [NNReal.agmSequences_snd_antitone](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ArithmeticGeometricMean.lean#L114) — proved, no admission.
- [NNReal.agmSequences_succ'](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ArithmeticGeometricMean.lean#L67) — proved, no admission.
- [NNReal.agm_comm](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ArithmeticGeometricMean.lean#L168) — proved, no admission.
- [NNReal.agm_eq_agm_gm_am](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ArithmeticGeometricMean.lean#L251) — proved, no admission.
- [NNReal.agm_mul_distrib](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ArithmeticGeometricMean.lean#L293) — proved, no admission.
- [NNReal.agm_pos](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ArithmeticGeometricMean.lean#L242) — proved, no admission.
- [NNReal.tendsto_agmSequences_fst_agm](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ArithmeticGeometricMean.lean#L204) — proved, no admission.
- [NNReal.tendsto_agmSequences_snd_agm](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ArithmeticGeometricMean.lean#L176) — proved, no admission.
- [PeriodPair](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean#L60) — definition, no admission.
- [PeriodPair.finite_poles_openPeriodCell](DLMFMathlib/Analysis/Complex/EllipticDivisors.lean#L75) — direct admission.
- [PeriodPair.finsum_residue_openPeriodCell_eq_zero](DLMFMathlib/Analysis/Complex/EllipticDivisors.lean#L82) — direct admission.
- [PeriodPair.hasSumLocallyUniformly_weierstrassP](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean#L293) — proved, no admission.
- [PeriodPair.openPeriodCell](DLMFMathlib/Analysis/Complex/EllipticDivisors.lean#L28) — definition, no admission.
- [PeriodPair.poleCount](DLMFMathlib/Analysis/Complex/EllipticDivisors.lean#L56) — definition, no admission.
- [PeriodPair.poleMultiplicity](DLMFMathlib/Analysis/Complex/EllipticDivisors.lean#L37) — definition, no admission.
- [PeriodPair.two_le_poleCount](DLMFMathlib/Analysis/Complex/EllipticDivisors.lean#L91) — direct admission.
- [PeriodPair.valueCount](DLMFMathlib/Analysis/Complex/EllipticDivisors.lean#L61) — definition, no admission.
- [PeriodPair.valueCount_eq_poleCount](DLMFMathlib/Analysis/Complex/EllipticDivisors.lean#L100) — direct admission.
- [PeriodPair.weierstrassP](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean#L268) — definition, no admission.
- [PeriodPair.weierstrassP_add_coe](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean#L484) — proved, no admission.
- [PeriodPair.weierstrassP_neg](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean#L310) — proved, no admission.
- [PeriodPair.zeroMultiplicity](DLMFMathlib/Analysis/Complex/EllipticDivisors.lean#L43) — definition, no admission.
- [Real.add_div_two_sub_sqrt_mul_eq](DLMFMathlib/Analysis/SpecialFunctions/ArithmeticGeometricMeanGap.lean#L24) — proved, no admission.
- [Real.add_div_two_sub_sqrt_mul_le](DLMFMathlib/Analysis/SpecialFunctions/ArithmeticGeometricMeanGap.lean#L38) — proved, no admission.
- [Real.isLeast_pendulumPeriod](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/JacobiElliptic/Pendulum.lean#L197) — proved, no admission.
- [Real.pendulumAngle](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/JacobiElliptic/Pendulum.lean#L55) — definition, no admission.
- [Real.pendulumAngle_periodic](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/JacobiElliptic/Pendulum.lean#L191) — proved, no admission.
- [Real.pendulumPeriod](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/JacobiElliptic/Pendulum.lean#L60) — definition, no admission.
- [Real.tendsto_pendulumPeriod_nhdsLT_pi](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/JacobiElliptic/Pendulum.lean#L230) — proved, no admission.
- [Real.tendsto_pendulumPeriod_nhds_zero](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/JacobiElliptic/Pendulum.lean#L216) — proved, no admission.
- [Real.tendsto_sum_Icc_twistedFourier_of_boundedVariationOn](DLMFMathlib/Analysis/Fourier/ShiftedPoisson.lean#L30) — direct admission.
- [TauCeti.Green.Examples.integral_norm_deriv_ellipse](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/Ellipse.lean#L59) — proved, no admission.
- [TauCeti.Real.legendreE](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/Legendre.lean#L87) — definition, no admission.
- [TauCeti.Real.legendreE_eq_integral_algebraic](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/Algebraic.lean#L91) — proved, no admission.
- [TauCeti.Real.legendreE_one_modulus](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/Elementary.lean#L123) — proved, no admission.
- [TauCeti.Real.legendreEc](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/Legendre.lean#L100) — definition, no admission.
- [TauCeti.Real.legendreEc_eq_one_add_mul_legendreEc](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/Landen.lean#L81) — proved, no admission.
- [TauCeti.Real.legendreEc_one_div_sqrt_two](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/Relation.lean#L123) — proved, no admission.
- [TauCeti.Real.legendreEc_two_mul_sqrt_div_one_add](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/Landen.lean#L44) — proved, no admission.
- [TauCeti.Real.legendreF](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/Legendre.lean#L81) — definition, no admission.
- [TauCeti.Real.legendreF_eq_integral_algebraic](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/Algebraic.lean#L78) — proved, no admission.
- [TauCeti.Real.legendreF_one_modulus](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/Elementary.lean#L62) — proved, no admission.
- [TauCeti.Real.legendreK](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/Legendre.lean#L97) — definition, no admission.
- [TauCeti.Real.legendreK_eq_one_add_mul_legendreK](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/Gauss.lean#L107) — proved, no admission.
- [TauCeti.Real.legendreK_eq_pi_div_two_mul_agm](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/Gauss.lean#L63) — proved, no admission.
- [TauCeti.Real.legendreK_one_div_sqrt_two](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/Lemniscate.lean#L148) — proved, no admission.
- [TauCeti.Real.legendreK_two_mul_sqrt_div_one_add](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/Gauss.lean#L86) — proved, no admission.
- [TauCeti.Real.legendrePi](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/Legendre.lean#L93) — definition, no admission.
- [TauCeti.Real.legendrePi_eq_integral_algebraic](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/Algebraic.lean#L100) — proved, no admission.
- [TauCeti.Real.tendsto_legendreK_nhdsLT_one](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/Elementary.lean#L171) — proved, no admission.
