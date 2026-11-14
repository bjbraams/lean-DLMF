# LaoLaksh Chapter3 acquisition ledger

All **4** entries and their distinct subclaims are audited in lookup order Mathlib,
TauCeti, DLMF. Pins: Mathlib `1b1ccf4b088b32fa3f23f2de1127433254a81e1e`, TauCeti
`396c3bd971e9722aa8656231760e710fe641d8cf`, Lean `v4.36.0-rc2`. The source synopsis,
pins and existing definition bodies are unchanged. “Existing” does not imply proved;
the transitive Lean axiom audit below distinguishes proofs, admissions and dependence on
admissions. Newly admitted statements remain in the theorem layer; defining APIs are proved.

## RL-3.01 — Cube group (3.6–3.7, p. 3-3).

Existing `DLMF.Hypergeometric.TransformationGroups.cubeGenerator` gives exactly the two printed
face cycles, converted from one-based book labels to Fin 6. Existing
`DLMF.Hypergeometric.TransformationGroups.cubeRotations`,
`DLMF.Hypergeometric.TransformationGroups.card_cubeRotations`, and
`DLMF.Hypergeometric.TransformationGroups.card_cubeSymmetries` give the generated rotation and
full reflection groups, of orders 24 and 48. The formerly available
`DLMF.Hypergeometric.TransformationGroups.nonempty_cubeRotations_mulEquiv_perm_four` asserted only
an abstract S4 isomorphism. New `DLMF.Hypergeometric.TransformationGroups.cubeOppositeFace` and
`DLMF.Hypergeometric.TransformationGroups.cubeBodyDiagonal` define the actual antipodal
incident-face vertex pairs. New
`DLMF.Hypergeometric.TransformationGroups.exists_cubeBodyDiagonal_mulEquiv` states that the S4
isomorphism is precisely their actual image action. Definitions and their defining equations are
proved; the geometric action theorem is admitted, not claimed as a proved finite computation.

Checked named coverage: 8 declarations; 4 depend on admissions.

## RL-3.02 — Six-coordinate parameter map (3.8–3.11, pp. 3-5–3-6).

Existing `DLMF.Hypergeometric.TransformationGroups.kummerCubeParameters`,
`DLMF.Hypergeometric.TransformationGroups.kummerCubeParameters_def`, and
`DLMF.Hypergeometric.TransformationGroups.kummerCubeParameters_mirror` give all four literal
coordinates and the exact upper-parameter mirror interchange. Existing
`DLMF.Hypergeometric.TransformationGroups.kummerCubeParameters_argument_mem` supplies the six
rational argument maps. New proved
`DLMF.Hypergeometric.TransformationGroups.kummerCubeParameters_exponent_differences` identifies
all three opposite-face differences with c-1,a+b-c,a-b. New
`DLMF.Hypergeometric.TransformationGroups.kummerCubeParameters_mem_kummer_orbit` acquires the full
transformed A,B,C triple together with its argument, up to upper-parameter symmetry, in the
concrete `DLMF.Hypergeometric.KummerPermutations.parameters` and
`DLMF.Hypergeometric.KummerPermutations.coordinate` algorithm. Both original and transformed
six-coordinate denominators are explicit; no assertion at an undefined source quotient is made.
The full orbit target remains admitted.

Checked named coverage: 8 declarations; 2 depend on admissions.

## RL-3.03 — Finite generator for all 24 Kummer forms (table 3.1, (3.4), (3.12–3.13), pp. 3-2–3-6).

New `DLMF.Hypergeometric.KummerSeedForms.parameters`,
`DLMF.Hypergeometric.KummerSeedForms.argument`, `DLMF.Hypergeometric.KummerSeedForms.prefactor`,
`DLMF.Hypergeometric.KummerSeedForms.fourForms`, `DLMF.Hypergeometric.KummerSeedForms.expression`,
and `DLMF.Hypergeometric.KummerSeedForms.domain` contain every literal six-by-four expression,
including the negative-axis (-z)^(-a) and (-z)^(-b) infinity normalization. All defining APIs are
proved. New proved `DLMF.Hypergeometric.KummerSeedForms.fourForms_eq_first` and
`DLMF.Hypergeometric.KummerSeedForms.expression_eq_first` derive equality of the four continued
forms from the existing full-principal-domain regularized Euler and Pfaff identities; the proof
does not substitute a totalized divergent ordinary series. New
`DLMF.Hypergeometric.KummerSeedForms.analyticOnNhd_and_gaussOperator_expression` acquires
analyticity and the actual original Gauss ODE on each seed's branch domain, with regular lower
parameter. New `DLMF.Hypergeometric.KummerSeedForms.expression_eq_const_mul_permutation_solution`
records the nonzero constant phase/Gamma bridge to
`DLMF.Hypergeometric.KummerPermutations.solution` on either whole half-plane. The generic finite
algorithm has its own proved `DLMF.Hypergeometric.KummerPermutations.card_indices`; the literal
generator has proved `DLMF.Hypergeometric.KummerSeedForms.card_indices`. These count indices, not
independent solutions. Equality of germs continues by the identity principle when the same
branches are continued; the existing proved
`DLMF.AlgebraicAnalytic.isFundamentalPair_of_wronskian_ne_zero` gives the two-dimensional
solution-space interpretation. Exceptional independently terminating finite sums are governed by
`DLMF.Hypergeometric.generalizedHypergeometricTruncated_theta_ode`, not blindly substituted into
Euler/Pfaff. In particular A=C=0,B=1 gives retained F(0,1;0,u)=1 but its independently retained
B-Pfaff expression is (1-u)^(-1), so a claim equating all such exceptional finite assignments
would be false. This is recorded as a domain/convention caution, with the synopsis unchanged.

Checked named coverage: 15 declarations; 3 depend on admissions.

## RL-3.04 — Riemann equation (3.14–3.18, pp. 3-6–3-7).

Existing `DLMF.Hypergeometric.riemannOperator` is exactly the printed Papperitz P and Q formula,
and `DLMF.Hypergeometric.riemannSolutions` supplies the corresponding solution space. Existing
`Complex.eq_papperitz_coefficients_of_regularSingular` is the generic sphere classification;
`DLMF.Hypergeometric.coefficients_eq_gauss_of_regularSingular` gives its normalized Gauss
specialization. The older `DLMF.Hypergeometric.riemann_hypergeometric_solution` is confined to the
transformed unit disk and principal prefactor logarithms. New
`DLMF.Hypergeometric.riemann_hypergeometric_solution_exp_log` acquires the full continued
principal Gauss domain with arbitrary fixed analytic local logarithms of both printed ratios, the
Fuchs relation, distinct singularities, and regular lower parameter. It states both analyticity
and the actual differential equation, not merely a named solution predicate. New
`DLMF.Hypergeometric.TransformationGroups.riemannFaceLabelEquiv` identifies opposite-face pairs
with the six exponent labels. New `DLMF.Hypergeometric.TransformationGroups.riemannLabelAction`,
`DLMF.Hypergeometric.TransformationGroups.riemannPointAction`,
`DLMF.Hypergeometric.TransformationGroups.injective_riemannLabelAction`, and
`DLMF.Hypergeometric.TransformationGroups.card_range_riemannLabelAction` give the actual faithful
action of order 48. New `DLMF.Hypergeometric.TransformationGroups.exists_riemannPointAction_perm`
states preservation of exponent pairs, and
`DLMF.Hypergeometric.TransformationGroups.riemannOperator_labelAction` gives exact
Papperitz-operator invariance under point permutation and within-pair swaps. The Gauss exponent
pairs are explicitly `DLMF.Hypergeometric.KummerPermutations.exponents`; existing proved
`DLMF.Hypergeometric.gauss_fuchs_relation` and `DLMF.Hypergeometric.riemannNormalOperator_gauss`
verify their Fuchs relation and differential equation. The upper-parameter mirror is the already
proved cube mirror map.

Checked named coverage: 16 declarations; 6 depend on admissions.

## Validation

All 4 entries are mapped. The transitive `#print axioms` audit checked **59** distinct
declarations; **15** depend on admissions. The **5** new modules
owned by this supplement contain **36** public declarations, including
**7** directly admitted targets. Definitions and their
defining equations have no admissions. Every new module has passed a direct strict Lean check
with `autoImplicit=false` and `relaxedAutoImplicit=false`; modules are registered in their
area umbrellas. Repository-wide build and import integration are coordinated with the other
book acquisitions and reported separately.

The per-entry declaration locations and proof statuses are retained in
[reports/BookAcquisition-LaoLaksh-Chapter3.tsv](reports/BookAcquisition-LaoLaksh-Chapter3.tsv). No additional
source erratum requiring user approval was identified in this supplement.

## Checked declaration index

- [Complex.eq_papperitz_coefficients_of_regularSingular](DLMFMathlib/Analysis/ODE/FuchsianClassification.lean#L191) — direct admission.
- [DLMF.AlgebraicAnalytic.isFundamentalPair_of_wronskian_ne_zero](DLMF/AlgebraicAnalytic/ODE/SecondOrder.lean#L244) — proved, no admission.
- [DLMF.Hypergeometric.KummerPermutations.card_indices](DLMF/Hypergeometric/KummerPermutations.lean#L111) — proved, no admission.
- [DLMF.Hypergeometric.KummerPermutations.coordinate](DLMF/Hypergeometric/KummerPermutations.lean#L41) — definition, no admission.
- [DLMF.Hypergeometric.KummerPermutations.exponents](DLMF/Hypergeometric/KummerPermutations.lean#L32) — definition, no admission.
- [DLMF.Hypergeometric.KummerPermutations.parameters](DLMF/Hypergeometric/KummerPermutations.lean#L65) — definition, no admission.
- [DLMF.Hypergeometric.KummerPermutations.solution](DLMF/Hypergeometric/KummerPermutations.lean#L97) — definition, no admission.
- [DLMF.Hypergeometric.KummerSeedForms.analyticOnNhd_and_gaussOperator_expression](DLMF/Hypergeometric/KummerSeedForms.lean#L133) — direct admission.
- [DLMF.Hypergeometric.KummerSeedForms.argument](DLMF/Hypergeometric/KummerSeedForms.lean#L37) — definition, no admission.
- [DLMF.Hypergeometric.KummerSeedForms.argument_def](DLMF/Hypergeometric/KummerSeedForms.lean#L74) — proved, no admission.
- [DLMF.Hypergeometric.KummerSeedForms.card_indices](DLMF/Hypergeometric/KummerSeedForms.lean#L126) — proved, no admission.
- [DLMF.Hypergeometric.KummerSeedForms.domain](DLMF/Hypergeometric/KummerSeedForms.lean#L62) — definition, no admission.
- [DLMF.Hypergeometric.KummerSeedForms.expression](DLMF/Hypergeometric/KummerSeedForms.lean#L55) — definition, no admission.
- [DLMF.Hypergeometric.KummerSeedForms.expression_def](DLMF/Hypergeometric/KummerSeedForms.lean#L89) — proved, no admission.
- [DLMF.Hypergeometric.KummerSeedForms.expression_eq_const_mul_permutation_solution](DLMF/Hypergeometric/KummerSeedForms.lean#L143) — direct admission.
- [DLMF.Hypergeometric.KummerSeedForms.expression_eq_first](DLMF/Hypergeometric/KummerSeedForms.lean#L118) — proved, no admission.
- [DLMF.Hypergeometric.KummerSeedForms.fourForms](DLMF/Hypergeometric/KummerSeedForms.lean#L47) — definition, no admission.
- [DLMF.Hypergeometric.KummerSeedForms.fourForms_def](DLMF/Hypergeometric/KummerSeedForms.lean#L82) — proved, no admission.
- [DLMF.Hypergeometric.KummerSeedForms.fourForms_eq_first](DLMF/Hypergeometric/KummerSeedForms.lean#L104) — proved, no admission.
- [DLMF.Hypergeometric.KummerSeedForms.mem_domain_iff](DLMF/Hypergeometric/KummerSeedForms.lean#L96) — proved, no admission.
- [DLMF.Hypergeometric.KummerSeedForms.parameters](DLMF/Hypergeometric/KummerSeedForms.lean#L30) — definition, no admission.
- [DLMF.Hypergeometric.KummerSeedForms.parameters_def](DLMF/Hypergeometric/KummerSeedForms.lean#L68) — proved, no admission.
- [DLMF.Hypergeometric.KummerSeedForms.prefactor](DLMF/Hypergeometric/KummerSeedForms.lean#L42) — definition, no admission.
- [DLMF.Hypergeometric.KummerSeedForms.prefactor_def](DLMF/Hypergeometric/KummerSeedForms.lean#L78) — proved, no admission.
- [DLMF.Hypergeometric.TransformationGroups.card_cubeRotations](DLMF/GeneralizedHypergeometric/FiniteTransformationGroups.lean#L57) — direct admission.
- [DLMF.Hypergeometric.TransformationGroups.card_cubeSymmetries](DLMF/GeneralizedHypergeometric/FiniteTransformationGroups.lean#L67) — direct admission.
- [DLMF.Hypergeometric.TransformationGroups.card_range_riemannLabelAction](DLMF/Hypergeometric/RiemannLabelAction.lean#L76) — depends on admission.
- [DLMF.Hypergeometric.TransformationGroups.cubeBodyDiagonal](DLMF/GeneralizedHypergeometric/CubeDiagonalAction.lean#L35) — definition, no admission.
- [DLMF.Hypergeometric.TransformationGroups.cubeBodyDiagonal_def](DLMF/GeneralizedHypergeometric/CubeDiagonalAction.lean#L45) — proved, no admission.
- [DLMF.Hypergeometric.TransformationGroups.cubeGenerator](DLMF/GeneralizedHypergeometric/FiniteTransformationGroups.lean#L32) — definition, no admission.
- [DLMF.Hypergeometric.TransformationGroups.cubeOppositeFace](DLMF/GeneralizedHypergeometric/CubeDiagonalAction.lean#L27) — definition, no admission.
- [DLMF.Hypergeometric.TransformationGroups.cubeOppositeFace_apply](DLMF/GeneralizedHypergeometric/CubeDiagonalAction.lean#L41) — proved, no admission.
- [DLMF.Hypergeometric.TransformationGroups.cubeRotations](DLMF/GeneralizedHypergeometric/FiniteTransformationGroups.lean#L37) — definition, no admission.
- [DLMF.Hypergeometric.TransformationGroups.exists_cubeBodyDiagonal_mulEquiv](DLMF/GeneralizedHypergeometric/CubeDiagonalAction.lean#L53) — direct admission.
- [DLMF.Hypergeometric.TransformationGroups.exists_riemannPointAction_perm](DLMF/Hypergeometric/RiemannLabelAction.lean#L84) — direct admission.
- [DLMF.Hypergeometric.TransformationGroups.injective_riemannLabelAction](DLMF/Hypergeometric/RiemannLabelAction.lean#L69) — proved, no admission.
- [DLMF.Hypergeometric.TransformationGroups.kummerCubeParameters](DLMF/GeneralizedHypergeometric/KummerCubeCoordinates.lean#L24) — definition, no admission.
- [DLMF.Hypergeometric.TransformationGroups.kummerCubeParameters_argument_mem](DLMF/GeneralizedHypergeometric/KummerCubeCoordinates.lean#L45) — direct admission.
- [DLMF.Hypergeometric.TransformationGroups.kummerCubeParameters_def](DLMF/GeneralizedHypergeometric/KummerCubeCoordinates.lean#L29) — proved, no admission.
- [DLMF.Hypergeometric.TransformationGroups.kummerCubeParameters_exponent_differences](DLMF/GeneralizedHypergeometric/KummerCubeAction.lean#L28) — proved, no admission.
- [DLMF.Hypergeometric.TransformationGroups.kummerCubeParameters_mem_kummer_orbit](DLMF/GeneralizedHypergeometric/KummerCubeAction.lean#L48) — direct admission.
- [DLMF.Hypergeometric.TransformationGroups.kummerCubeParameters_mirror](DLMF/GeneralizedHypergeometric/KummerCubeCoordinates.lean#L35) — proved, no admission.
- [DLMF.Hypergeometric.TransformationGroups.nonempty_cubeRotations_mulEquiv_perm_four](DLMF/GeneralizedHypergeometric/FiniteTransformationGroups.lean#L62) — direct admission.
- [DLMF.Hypergeometric.TransformationGroups.riemannFaceLabelEquiv](DLMF/Hypergeometric/RiemannLabelAction.lean#L29) — definition, no admission.
- [DLMF.Hypergeometric.TransformationGroups.riemannLabelAction](DLMF/Hypergeometric/RiemannLabelAction.lean#L38) — definition, no admission.
- [DLMF.Hypergeometric.TransformationGroups.riemannLabelAction_def](DLMF/Hypergeometric/RiemannLabelAction.lean#L47) — proved, no admission.
- [DLMF.Hypergeometric.TransformationGroups.riemannLabelAction_mul](DLMF/Hypergeometric/RiemannLabelAction.lean#L61) — proved, no admission.
- [DLMF.Hypergeometric.TransformationGroups.riemannLabelAction_one](DLMF/Hypergeometric/RiemannLabelAction.lean#L55) — proved, no admission.
- [DLMF.Hypergeometric.TransformationGroups.riemannOperator_labelAction](DLMF/Hypergeometric/RiemannLabelAction.lean#L91) — direct admission.
- [DLMF.Hypergeometric.TransformationGroups.riemannPointAction](DLMF/Hypergeometric/RiemannLabelAction.lean#L43) — definition, no admission.
- [DLMF.Hypergeometric.TransformationGroups.riemannPointAction_def](DLMF/Hypergeometric/RiemannLabelAction.lean#L51) — proved, no admission.
- [DLMF.Hypergeometric.coefficients_eq_gauss_of_regularSingular](DLMF/Hypergeometric/RiemannClassification.lean#L33) — direct admission.
- [DLMF.Hypergeometric.gauss_fuchs_relation](DLMF/Hypergeometric/Riemann.lean#L69) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometricTruncated_theta_ode](DLMF/GeneralizedHypergeometric/TerminatingDifferentialEquation.lean#L25) — direct admission.
- [DLMF.Hypergeometric.riemannNormalOperator_gauss](DLMF/Hypergeometric/Riemann.lean#L74) — proved, no admission.
- [DLMF.Hypergeometric.riemannOperator](DLMF/Hypergeometric/Riemann.lean#L50) — definition, no admission.
- [DLMF.Hypergeometric.riemannSolutions](DLMF/Hypergeometric/Riemann.lean#L59) — definition, no admission.
- [DLMF.Hypergeometric.riemann_hypergeometric_solution](DLMF/Hypergeometric/Riemann.lean#L95) — proved, no admission.
- [DLMF.Hypergeometric.riemann_hypergeometric_solution_exp_log](DLMF/Hypergeometric/RiemannLogarithmicSolutions.lean#L29) — direct admission.
