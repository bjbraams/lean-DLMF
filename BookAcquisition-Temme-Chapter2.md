# Temme Chapter2 acquisition ledger

All **8** entries and their distinct subclaims are audited in lookup order Mathlib,
TauCeti, DLMF. Pins: Mathlib `1b1ccf4b088b32fa3f23f2de1127433254a81e1e`, TauCeti
`396c3bd971e9722aa8656231760e710fe641d8cf`, Lean `v4.36.0-rc2`. The source synopsis,
pins and existing definition bodies are unchanged. “Existing” does not imply proved;
the transitive Lean axiom audit below distinguishes proofs, admissions and dependence on
admissions. Newly admitted statements remain in the theorem layer; defining APIs are proved.

## TEM-02-01 — Integration of a series, Theorem 2.1, p. 30.

Mathlib `MeasureTheory.hasSum_integral_of_summable_integral_norm` and
`MeasureTheory.integral_tsum_of_summable_integral_norm`, applied to volume restricted to the open
interval, give absolute summability of the scalar integrals and their sum identity. Continuity
supplies measurability. The source's absolute-integral hypotheses mean actual L1 integrability of
each term; they are not interpreted as finiteness of a totalized Bochner integral of a
nonintegrable norm. Equivalence with the single finite extended integral of the norm sum is
`MeasureTheory.lintegral_tsum`. The locally uniform limit F is continuous and hence measurable;
Tonelli gives pointwise absolute convergence almost everywhere, where its ordered sum equals the
unconditional sum. Domination by the integrable norm sum via `MeasureTheory.Integrable.mono'` and
`norm_tsum_le_tsum_norm` gives integrability of F. Thus no unconditional tsum identity at an
exceptional conditionally convergent point is assumed. These are direct measure-theoretic
consequences; no new admission is needed.

Checked named coverage: 5 declarations; 0 depend on admissions.

## TEM-02-02 — Interchange of improper integrals, Theorem 2.2, p. 30.

Mathlib `MeasureTheory.integrable_prod_iff`, `MeasureTheory.integrable_prod_iff'`,
`MeasureTheory.integral_integral_swap`, `MeasureTheory.Integrable.integral_prod_left`, and
`MeasureTheory.Integrable.integral_prod_right` give the exact complex Fubini assertion on the two
restricted positive-half-line measures. `MeasureTheory.lintegral_lintegral` gives the equivalent
extended integral-of-norm conditions. The almost-everywhere qualification of inner integrability
is retained. If separately specified ordinary improper inner integrals exist at all points, their
values agree with the Lebesgue integrals wherever the latter are absolutely convergent, and
therefore their outer integrals agree. Absolute convergence merely after cancellation in an outer
integral is not substituted for product absolute integrability.

Checked named coverage: 6 declarations; 0 depend on admissions.

## TEM-02-03 — Holomorphic parameter integration, Theorem 2.3, pp. 30–31.

Shared root acquisition
`Complex.differentiableOn_and_tendstoLocallyUniformlyOn_integral_iteratedDeriv` states the full
locally uniform improper parameter theorem for arbitrary complex Banach target, every natural
derivative order and arbitrary cutoff filter with a nontrivial limit. Take the cutoff index as the
product of the two endpoint filters and J=(a,b). Its conclusion supplies both holomorphy and local
uniform convergence of the actual truncated derivative integrals to the derivative of F. No
Bochner absolute-integrability hypothesis is inserted at conditional improper endpoints.

Checked named coverage: 1 declarations; 1 depend on admissions.

## TEM-02-04 — Poincaré asymptotic series (2.1)–(2.3), p. 31.

Existing `Asymptotics.HasAsymptoticExpansion` is exactly the every-N first-omitted-order Big-O
definition. Mathlib `Asymptotics.IsBigO` expands to an eventual constant bound; along the
norm-at-infinity filter restricted to the source set this is the displayed C,R condition, with
positive constants obtained by enlargement. `Asymptotics.isAsymptoticScale_pow` at w(z)=1/z and
`Asymptotics.HasAsymptoticExpansion.unique` prove uniqueness on every nontrivial such filter:
powers of 1/z are eventually nonzero. The scale tends to zero along norm infinity, so the next
term is little-o of the preceding one. Source sets with points tending to infinity provide exactly
the required nontriviality. New model
`DLMF.Confluent.Real.not_tendsto_envelopingExpIntegral_terms` below gives an explicit
everywhere-divergent asymptotic series, so convergence is not silently built into this definition.

Checked named coverage: 5 declarations; 1 depend on admissions.

## TEM-02-05 — A model enveloping expansion (2.4), pp. 31–32.

New `DLMF.Confluent.Real.envelopingExpIntegral` is the canonical scaled existing E1, and
`DLMF.Confluent.Real.envelopingExpIntegralRemainder` is the source's actual tail integral with
signed factorial prefactor; their defining equations are proved.
`DLMF.Confluent.Real.envelopingExpIntegral_eq_integral`,
`DLMF.Confluent.Real.envelopingExpIntegral_eq_sum_add_remainder`,
`DLMF.Confluent.Real.envelopingExpIntegralRemainder_sign`,
`DLMF.Confluent.Real.abs_envelopingExpIntegralRemainder_le`, and
`DLMF.Confluent.Real.not_tendsto_envelopingExpIntegral_terms` retain the exact integral, all N>=0
finite identities, strict sign, first-omitted-term bound and failure of the terms to tend to zero
at each x>0. `DLMF.Confluent.Real.hasAsymptoticExpansion_envelopingExpIntegral` is proved from the
finite identity and bound, rather than independently admitted. Existing
`DLMF.Confluent.expIntegralE_exact_remainder` is the general complex recurrence identity
underlying this example; it alone had not stated the real sign, exact improper tail, convergence
failure or enveloping bound.

Checked named coverage: 9 declarations; 6 depend on admissions.

## TEM-02-06 — Watson lemma, Theorem 2.4, (2.5)–(2.7), pp. 32–33.

Shared Olver acquisition `MeasureTheory.IsImproperLaplacePrimitive`, with its actual continuous
normalized primitive and specified derivative off a finite exceptional set, records local ordinary
improper integrability including interior integrable singularities.
`Asymptotics.watson_lemma_sector_conditional` with mu=1, arbitrary complex lam of positive real
part and an ordinarily convergent Laplace half-plane gives exactly the source closed-sector Watson
expansion. Its powers are principal in the initial right half-plane, continuous from the positive
ray. The transform is a limit of the primitive, not a Bochner integral that could totalize to zero
for conditionally convergent tails. The source hypotheses are input properties of the kernel and
its existing ordinary Laplace integral, not the desired asymptotic conclusion.

Checked named coverage: 2 declarations; 1 depend on admissions.

## TEM-02-07 — Sectorial Watson lemma, Theorem 2.5, (2.8), pp. 33–34.

New `Asymptotics.LiftedWatson.IsKernel` packages precisely the source analytic logarithmic strip,
full uniform endpoint expansions on its closed substrips and at-most-exponential growth on those
substrips. `Asymptotics.LiftedWatson.rayAngle` explicitly takes the midpoint of the intersection
of the kernel's angle interval with the decaying Laplace half-plane.
`Asymptotics.LiftedWatson.transform` is the actual rotated-ray Bochner integral, including its
complex tangent and logarithmic-sheet kernel value. Both defining equations and
`Asymptotics.LiftedWatson.rayAngle_mem` are proved.
`Asymptotics.LiftedWatson.exists_analyticOnNhd_transform` gives actual absolute convergence and
analytic continuation sufficiently far out on every closed continued subsector.
`Asymptotics.LiftedWatson.exists_transform_ofReal` identifies the initial positive ray.
`Asymptotics.LiftedWatson.hasAsymptoticExpansion_transform` gives the entire lifted union
-alpha2-pi/2<arg z<-alpha1+pi/2 with the same Gamma coefficients and continued powers. This allows
asymmetric sectors, arbitrary widths on the logarithmic covering and exponential growth; the older
polynomial-growth single-principal-ray rotation theorem did not cover all those subclaims.

Checked named coverage: 7 declarations; 3 depend on admissions.

## TEM-02-08 — Steepest descent geometry, pp. 34–38.

New `Complex.tangent_level_im_eq_real_mul_conj_deriv` records a genuine regular level curve with
its derivative and constant imaginary part; its tangent is a real multiple of the conjugate
complex derivative, the real-part gradient. Existing `Complex.exists_isAnalyticSaddleMap`,
`Complex.analyticSaddleMap` and `Complex.analyticSaddleMap_spec` give the analytic Morse inverse
with G(u)=u^2/2, derivative normalization phi''(z0)d^2=1, and nonzero d; complex square-root
existence supplies d. Inverting its nonzero analytic derivative gives the source forward
coordinate. The amplitude is the actual product psi(z(u))z'(u), not arbitrary coefficients. New
`Complex.tendsto_integral_homotopy_of_joining_arcs_zero` supplies the required actual holomorphic
contour homotopy and both explicit vanishing joining-arc integrals, so a local saddle germ is
never treated as a deformation proof. New
`Asymptotics.hasAsymptoticExpansion_integral_gaussian_of_analyticAt` states the full real-line
Gaussian expansion with the precise even derivatives sqrt(2pi)g^(2n)(0)/(2^n n!), under analytic
local amplitude and a Gaussian-weighted integrable tail. Its outer pieces are exponentially
negligible. Multiplication by exp(-w*phi(z0)) via `Asymptotics.HasAsymptoticExpansion.mul_left`
gives the full saddle expansion with its stated prefactor. The parameterized finite integral
change of variables is the ordinary one-dimensional chain rule/substitution, applied to this
actual inverse coordinate and its tangent.

Checked named coverage: 7 declarations; 5 depend on admissions.

## Validation

All 8 entries are mapped. The transitive `#print axioms` audit checked **45** distinct
declarations; **16** depend on admissions. The **3** new modules
owned by this supplement contain **22** public declarations, including
**11** directly admitted targets. Definitions and their
defining equations have no admissions. Every new module has passed a direct strict Lean check
with `autoImplicit=false` and `relaxedAutoImplicit=false`; modules are registered in their
area umbrellas. Repository-wide build and import integration are coordinated with the other
book acquisitions and reported separately.

The per-entry declaration locations and proof statuses are retained in
[reports/BookAcquisition-Temme-Chapter2.tsv](reports/BookAcquisition-Temme-Chapter2.tsv). No additional
source erratum requiring user approval was identified in this supplement.

## Checked declaration index

- [Asymptotics.HasAsymptoticExpansion](DLMFMathlib/Analysis/Asymptotics/AsymptoticExpansion.lean#L61) — definition, no admission.
- [Asymptotics.HasAsymptoticExpansion.mul_left](DLMFMathlib/Analysis/Asymptotics/AsymptoticExpansion.lean#L101) — proved, no admission.
- [Asymptotics.HasAsymptoticExpansion.unique](DLMFMathlib/Analysis/Asymptotics/AsymptoticExpansion.lean#L157) — proved, no admission.
- [Asymptotics.IsBigO](.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean#L87) — definition, no admission.
- [Asymptotics.LiftedWatson.IsKernel](DLMFMathlib/Analysis/Asymptotics/LiftedWatson.lean#L32) — definition, no admission.
- [Asymptotics.LiftedWatson.exists_analyticOnNhd_transform](DLMFMathlib/Analysis/Asymptotics/LiftedWatson.lean#L102) — direct admission.
- [Asymptotics.LiftedWatson.exists_transform_ofReal](DLMFMathlib/Analysis/Asymptotics/LiftedWatson.lean#L118) — direct admission.
- [Asymptotics.LiftedWatson.hasAsymptoticExpansion_transform](DLMFMathlib/Analysis/Asymptotics/LiftedWatson.lean#L129) — direct admission.
- [Asymptotics.LiftedWatson.rayAngle](DLMFMathlib/Analysis/Asymptotics/LiftedWatson.lean#L46) — definition, no admission.
- [Asymptotics.LiftedWatson.rayAngle_def](DLMFMathlib/Analysis/Asymptotics/LiftedWatson.lean#L59) — proved, no admission.
- [Asymptotics.LiftedWatson.rayAngle_mem](DLMFMathlib/Analysis/Asymptotics/LiftedWatson.lean#L73) — proved, no admission.
- [Asymptotics.LiftedWatson.transform](DLMFMathlib/Analysis/Asymptotics/LiftedWatson.lean#L53) — definition, no admission.
- [Asymptotics.LiftedWatson.transform_def](DLMFMathlib/Analysis/Asymptotics/LiftedWatson.lean#L65) — proved, no admission.
- [Asymptotics.hasAsymptoticExpansion_integral_gaussian_of_analyticAt](DLMFMathlib/Analysis/Complex/SteepestDescent.lean#L62) — direct admission.
- [Asymptotics.isAsymptoticScale_pow](DLMFMathlib/Analysis/Asymptotics/AsymptoticExpansion.lean#L173) — proved, no admission.
- [Asymptotics.watson_lemma_sector_conditional](DLMFMathlib/Analysis/Asymptotics/WatsonConditional.lean#L48) — direct admission.
- [Complex.analyticSaddleMap](DLMFMathlib/Analysis/Analytic/QuadraticInverse.lean#L59) — definition, no admission.
- [Complex.analyticSaddleMap_spec](DLMFMathlib/Analysis/Analytic/QuadraticInverse.lean#L69) — depends on admission.
- [Complex.differentiableOn_and_tendstoLocallyUniformlyOn_integral_iteratedDeriv](DLMFMathlib/Analysis/Complex/ImproperParameterIntegral.lean#L31) — direct admission.
- [Complex.exists_isAnalyticSaddleMap](DLMFMathlib/Analysis/Analytic/QuadraticInverse.lean#L49) — direct admission.
- [Complex.tangent_level_im_eq_real_mul_conj_deriv](DLMFMathlib/Analysis/Complex/SteepestDescent.lean#L30) — direct admission.
- [Complex.tendsto_integral_homotopy_of_joining_arcs_zero](DLMFMathlib/Analysis/Complex/SteepestDescent.lean#L41) — direct admission.
- [DLMF.Confluent.Real.abs_envelopingExpIntegralRemainder_le](DLMF/ExpIntegrals/EnvelopingModel.lean#L70) — direct admission.
- [DLMF.Confluent.Real.envelopingExpIntegral](DLMF/ExpIntegrals/EnvelopingModel.lean#L28) — definition, no admission.
- [DLMF.Confluent.Real.envelopingExpIntegralRemainder](DLMF/ExpIntegrals/EnvelopingModel.lean#L33) — definition, no admission.
- [DLMF.Confluent.Real.envelopingExpIntegralRemainder_def](DLMF/ExpIntegrals/EnvelopingModel.lean#L42) — proved, no admission.
- [DLMF.Confluent.Real.envelopingExpIntegralRemainder_sign](DLMF/ExpIntegrals/EnvelopingModel.lean#L64) — direct admission.
- [DLMF.Confluent.Real.envelopingExpIntegral_def](DLMF/ExpIntegrals/EnvelopingModel.lean#L38) — proved, no admission.
- [DLMF.Confluent.Real.envelopingExpIntegral_eq_integral](DLMF/ExpIntegrals/EnvelopingModel.lean#L49) — direct admission.
- [DLMF.Confluent.Real.envelopingExpIntegral_eq_sum_add_remainder](DLMF/ExpIntegrals/EnvelopingModel.lean#L56) — direct admission.
- [DLMF.Confluent.Real.hasAsymptoticExpansion_envelopingExpIntegral](DLMF/ExpIntegrals/EnvelopingModel.lean#L76) — depends on admission.
- [DLMF.Confluent.Real.not_tendsto_envelopingExpIntegral_terms](DLMF/ExpIntegrals/EnvelopingModel.lean#L97) — direct admission.
- [DLMF.Confluent.expIntegralE_exact_remainder](DLMF/IncompleteGamma/ExpIntegralAsymptotics.lean#L53) — proved, no admission.
- [MeasureTheory.Integrable.integral_prod_left](.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean#L334) — proved, no admission.
- [MeasureTheory.Integrable.integral_prod_right](.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean#L341) — proved, no admission.
- [MeasureTheory.Integrable.mono'](.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean#L104) — proved, no admission.
- [MeasureTheory.IsImproperLaplacePrimitive](DLMFMathlib/Analysis/Integral/ConditionalLaplace.lean#L33) — definition, no admission.
- [MeasureTheory.hasSum_integral_of_summable_integral_norm](.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean#L97) — proved, no admission.
- [MeasureTheory.integrable_prod_iff](.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean#L230) — proved, no admission.
- [MeasureTheory.integrable_prod_iff'](.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean#L238) — proved, no admission.
- [MeasureTheory.integral_integral_swap](.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean#L481) — proved, no admission.
- [MeasureTheory.integral_tsum_of_summable_integral_norm](.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean#L112) — proved, no admission.
- [MeasureTheory.lintegral_lintegral](.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean#L1090) — proved, no admission.
- [MeasureTheory.lintegral_tsum](.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean#L362) — proved, no admission.
- [norm_tsum_le_tsum_norm](.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/InfiniteSum.lean#L149) — proved, no admission.
