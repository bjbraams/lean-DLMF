# Olver Chapter 13 network acquisition ledger

The five network entries O-13.08–O-13.12 and the infinity-selected S subclaim of
O-13.03 are audited in lookup order Mathlib,
TauCeti, DLMF. Pins: Mathlib `1b1ccf4b088b32fa3f23f2de1127433254a81e1e`, TauCeti
`396c3bd971e9722aa8656231760e710fe641d8cf`, Lean `v4.36.0-rc2`. The source synopsis,
pins and existing definition bodies are unchanged. “Existing” does not imply proved;
the transitive Lean axiom audit below distinguishes proofs, admissions and dependence on
admissions. Newly admitted statements remain in the theorem layer; defining APIs are proved.

## O-13.03 — parameterized pole connections and Legendre example (§§5–6, pp. 487–491).

The infinity-selected S acquisition is new
`DLMF.AsymptoticApproximations.ComplexBesselComparison.exists_complex_simplePole_K_recessive`: an
actual lifted K-normalized solution, vanishing relative value and derivative errors at the
prescribed progressive infinity, and the explicit adaptive-envelope c*exp(c*V/abs(u))*V/abs(u)
bound on every path retaining that initial tail. The coefficient sequence, comparison K, envelope
and radius-ratio constant are actual existing expressions. Root acquisitions
`ODE.SimplePoleScaling.dilated_residual`,
`ODE.SimplePoleScaling.exists_local_principalCut_parameterization`,
`DLMF.AsymptoticApproximations.SimplePoleConnection.tendsto_parameterRecessive_frobenius`, and
`DLMF.AsymptoticApproximations.SimplePoleConnection.tendsto_physical_frobenius_normalizer` give
the scaled perturbation, intrinsic cut direction and exact Frobenius multiplier. The two-bank
quotient and Legendre Gamma normalization comparison are in the coordinated root Chapter13 audit;
no unsupported endpoint identification is inferred from substitution alone.

Checked named coverage: 5 declarations; 5 depend on admissions.

## O-13.08 — principal curves and canonical solutions (§11, pp. 503–506).

New `Complex.SimpleTurningPoint.principalRay` and
`Complex.SimpleTurningPoint.exists_three_principal_arcs` give the actual local analytic inverse
coordinate and all three outgoing quadratic-differential arcs, whose tangent directions differ by
2*pi/3. `Complex.SimpleTurningPoint.principal_trajectories_no_crossing` gives global absence of
self-crossings, equality of intersecting maximal trajectories and the lack of regular interior
endpoints. `Complex.SimpleTurningPoint.exists_three_principal_branch_domains` constructs the
actual three maximal cuts, simply connected branch domains, adjacent principal components,
canonical root/phase/control primitives and cyclic amplitude normalization from analytic f with
one simple zero. It allows extra principal components elsewhere, as p504 states. New
`Complex.ThreeReferenceLiouvilleGreen.Data` supplies only actual branch/reference/progressive-path
geometry, with normalized multipliers and common prescribed tails.
`Complex.ThreeReferenceLiouvilleGreen.Data.exists_canonical_network` derives actual global
analytic endpoint-selected solutions, full accessible-point bounds, pairwise endpoint limits,
their symmetry and the sharp half-exponential variation bound. The endpoint errors are
conclusions, not structure fields.

Checked named coverage: 6 declarations; 4 depend on admissions.

## O-13.09 — fundamental three-solution connection (§11, pp. 505–506).

New `Complex.ThreeReferenceLiouvilleGreen.Data.exists_canonical_network` gives the exact cyclic
connection with coefficients (1+delta23), exp(-2*pi*i/3)*(1+delta31), exp(2*pi*i/3)*(1+delta12).
`Complex.ThreeReferenceLiouvilleGreen.Data.relativeError` and
`Complex.ThreeReferenceLiouvilleGreen.Data.IsCanonicalFamily` are actual solution/normalization
predicates with proved defining APIs;
`Complex.ThreeReferenceLiouvilleGreen.Data.IsCanonicalFamily.connection_limits` derives the same
identity and delta limits for any such actual family. New
`Complex.ThreeReferenceLiouvilleGreen.Data.normalized_coefficient_endpoint_symmetry` gives the
actual limits of the original-variable higher coefficient recursion, normalized to vanish at each
reference.
`Complex.ThreeReferenceLiouvilleGreen.Data.exists_positive_parameter_connection_expansions` gives
fixed-geometry uniform O(1/u) connection errors and all higher endpoint coefficient expansions,
with pair symmetry and actual control variations divided by u. The elementary algebraic basis
`ODE.wronskian_cyclic_sum` is fully proved for arbitrary normed-commutative-ring-valued functions;
the analytic normalization and endpoint identification remain admitted targets.

Checked named coverage: 7 declarations; 4 depend on admissions.

## O-13.10 — vanishing endpoint errors (Theorem 13.1, pp. 508–510).

New `Complex.PowerSectorLiouvilleGreen.Data` retains analytic complex-power equivalents on an
actual annular sector, the canonical root/phase/control and the source positive exponents.
`Complex.PowerSectorLiouvilleGreen.Data.control_deriv_isBigO` derives the differentiated control
decay z^(-1-min(alpha,beta)) on every closed interior subsector.
`Complex.PowerSectorLiouvilleGreen.AdjacentRayDirections` is the explicit unwrapped
principal-domain inequality, whose boundaries are alpha*theta+arg(k)/2=pi/2+n*pi.
`Complex.PowerSectorLiouvilleGreen.Data.exists_escaping_progressive_joins` constructs actual
eventually progressive straight tails and joins escaping every compact set, with total control
variation tending to zero. `Complex.PowerSectorLiouvilleGreen.Data.tendsto_error_adjacent_zero`
concludes exact vanishing of the actual canonical relative error and normalized derivative at the
adjacent reference. Its hypotheses are the actual ODE, coefficient branch and first-end
normalization; neither a zero delta nor the desired endpoint bound is assumed. The Airy special
case follows by f=z, g=0 and its exact rotated Airy normalization.

Checked named coverage: 5 declarations; 3 depend on admissions.

## O-13.11 — complex proof of real connections (§14, pp. 510–513).

New `Complex.ThreeReferenceLiouvilleGreen.IsRealGeometry` records the actual Schwarz-symmetric
coefficient domain, conjugate reference paths and the positive/negative real-axis canonical branch
normalizations. `Complex.ThreeReferenceLiouvilleGreen.real_connection_of_canonical_family` takes
only the actual canonical ODE family and the source stated cross-reference/negative-infinity
vanishing conditions; it derives the real amplitude-two identity, actual endpoint constant with
its sharp variation bound, the negative-infinity connection asymptotic, and separate
constant/local amplitude-phase bounds.
`Complex.ThreeReferenceLiouvilleGreen.cosine_connection_of_canonical_family` fixes the source real
cosine solution as Re(exp(-pi*i/6)*W2), with its exact growing-side error, negative-side phase and
endpoint asymptotic. The amplitude/phase inequality itself reuses
`Complex.exists_amplitude_phase_error`, including abs(p)<=abs(epsilon) and
abs(q)<=arcsin(abs(epsilon))<=pi*abs(epsilon)/2. Source vanishing/path hypotheses are retained;
Schwarz symmetry is not used to invent a zero connection correction.

Checked named coverage: 4 declarations; 3 depend on admissions.

## O-13.12 — exact scattering coefficients and Weber tests (§15, pp. 513–516).

New `Complex.ThreeReferenceScattering.scattering_probabilities_of_canonical_family` derives the
actual unit-transmitted `ODE.TwoTurningPoints.IsScatteringState` from the canonical network,
actual coefficient comparison waves, global classical ODE, and the source required cross-reference
and real-infinity vanishing errors. `Complex.ThreeReferenceScattering.rightRelativeError` is the
actual upper-cut transmitted-wave relative error with the common scale and unit phase retained.
The theorem derives delta2/delta3 as actual endpoint limits, their strict variation bounds, the
nonzero incoming denominator, both exact quotients T=exp(-2*u*L)/abs(1+delta3)^2 and
R=abs(1+delta2)^2/abs(1+delta3)^2, and exact flux R+T=1. No probability or connection coefficient
is assumed as input. The two exact tests reuse root
`DLMF.Confluent.WeberScattering.transmission_and_reflection`,
`DLMF.Confluent.WeberScattering.outgoingRight_flux`,
`DLMF.Confluent.WeberScattering.outgoingRight_eq_incoming_add_reflected`, and
`DLMF.Confluent.WeberScattering.isBoundState_iff_odd_square`: their waves and Wronskian
coefficients are actual cylinder functions, not definitions equal to the desired logistic
formulas. Progressive geometry remains the actual Data joins and the supplied vanishing errors;
O-13.10 supplies sufficient exact-vanishing conditions.

Checked named coverage: 7 declarations; 5 depend on admissions.

## Validation

All five network entries and the indicated O-13.03 subclaim are mapped. The transitive `#print axioms` audit checked **50** distinct
declarations; **23** depend on admissions. The **6** new modules
owned by this supplement contain **39** public declarations, including
**14** directly admitted targets. Definitions and their
defining equations have no admissions. Every new module has passed a direct strict Lean check
with `autoImplicit=false` and `relaxedAutoImplicit=false`; modules are registered in their
area umbrellas. Repository-wide build and import integration are coordinated with the other
book acquisitions and reported separately.

The per-entry declaration locations and proof statuses are retained in
[reports/BookAcquisition-Olver-Chapter13-Network.tsv](reports/BookAcquisition-Olver-Chapter13-Network.tsv).
Source statement qualifications are recorded in
[BookAcquisition-RevisionNotes.md](BookAcquisition-RevisionNotes.md); the SYNOPSIS file is unchanged.

## Checked declaration index

- [Complex.PowerSectorLiouvilleGreen.AdjacentRayDirections](DLMFMathlib/Analysis/ODE/VanishingLiouvilleGreenError.lean#L41) — definition, no admission.
- [Complex.PowerSectorLiouvilleGreen.Data](DLMFMathlib/Analysis/ODE/VanishingLiouvilleGreenError.lean#L63) — definition, no admission.
- [Complex.PowerSectorLiouvilleGreen.Data.control_deriv_isBigO](DLMFMathlib/Analysis/ODE/VanishingLiouvilleGreenError.lean#L99) — direct admission.
- [Complex.PowerSectorLiouvilleGreen.Data.exists_escaping_progressive_joins](DLMFMathlib/Analysis/ODE/VanishingLiouvilleGreenError.lean#L110) — direct admission.
- [Complex.PowerSectorLiouvilleGreen.Data.tendsto_error_adjacent_zero](DLMFMathlib/Analysis/ODE/VanishingLiouvilleGreenError.lean#L131) — direct admission.
- [Complex.PowerSectorLiouvilleGreen.adjacentRayDirections_iff](DLMFMathlib/Analysis/ODE/VanishingLiouvilleGreenError.lean#L51) — proved, no admission.
- [Complex.PowerSectorLiouvilleGreen.mem_sector_iff](DLMFMathlib/Analysis/ODE/VanishingLiouvilleGreenError.lean#L35) — proved, no admission.
- [Complex.PowerSectorLiouvilleGreen.sector](DLMFMathlib/Analysis/ODE/VanishingLiouvilleGreenError.lean#L31) — definition, no admission.
- [Complex.SimpleTurningPoint.IsMaximalPrincipalTrajectoryImage](DLMFMathlib/Analysis/ODE/SimpleTurningTrajectories.lean#L59) — definition, no admission.
- [Complex.SimpleTurningPoint.IsPrincipalTrajectory](DLMFMathlib/Analysis/ODE/SimpleTurningTrajectories.lean#L38) — definition, no admission.
- [Complex.SimpleTurningPoint.IsPrincipalTrajectoryImage](DLMFMathlib/Analysis/ODE/SimpleTurningTrajectories.lean#L50) — definition, no admission.
- [Complex.SimpleTurningPoint.exists_three_principal_arcs](DLMFMathlib/Analysis/ODE/SimpleTurningTrajectories.lean#L72) — direct admission.
- [Complex.SimpleTurningPoint.exists_three_principal_branch_domains](DLMFMathlib/Analysis/ODE/SimpleTurningTrajectories.lean#L110) — direct admission.
- [Complex.SimpleTurningPoint.isMaximalPrincipalTrajectoryImage_iff](DLMFMathlib/Analysis/ODE/SimpleTurningTrajectories.lean#L64) — proved, no admission.
- [Complex.SimpleTurningPoint.isPrincipalTrajectoryImage_iff](DLMFMathlib/Analysis/ODE/SimpleTurningTrajectories.lean#L54) — proved, no admission.
- [Complex.SimpleTurningPoint.isPrincipalTrajectory_iff](DLMFMathlib/Analysis/ODE/SimpleTurningTrajectories.lean#L44) — proved, no admission.
- [Complex.SimpleTurningPoint.principalRay](DLMFMathlib/Analysis/ODE/SimpleTurningTrajectories.lean#L31) — definition, no admission.
- [Complex.SimpleTurningPoint.principalRay_def](DLMFMathlib/Analysis/ODE/SimpleTurningTrajectories.lean#L34) — proved, no admission.
- [Complex.SimpleTurningPoint.principal_trajectories_no_crossing](DLMFMathlib/Analysis/ODE/SimpleTurningTrajectories.lean#L94) — direct admission.
- [Complex.ThreeReferenceLiouvilleGreen.Data](DLMFMathlib/Analysis/ODE/ThreeReferenceLiouvilleGreen.lean#L32) — definition, no admission.
- [Complex.ThreeReferenceLiouvilleGreen.Data.IsCanonicalFamily](DLMFMathlib/Analysis/ODE/ThreeReferenceLiouvilleGreen.lean#L115) — definition, no admission.
- [Complex.ThreeReferenceLiouvilleGreen.Data.IsCanonicalFamily.connection_limits](DLMFMathlib/Analysis/ODE/ThreeReferenceLiouvilleGreen.lean#L219) — direct admission.
- [Complex.ThreeReferenceLiouvilleGreen.Data.exists_canonical_network](DLMFMathlib/Analysis/ODE/ThreeReferenceLiouvilleGreen.lean#L136) — direct admission.
- [Complex.ThreeReferenceLiouvilleGreen.Data.exists_positive_parameter_connection_expansions](DLMFMathlib/Analysis/ODE/ThreeReferenceLiouvilleGreen.lean#L187) — direct admission.
- [Complex.ThreeReferenceLiouvilleGreen.Data.isCanonicalFamily_iff](DLMFMathlib/Analysis/ODE/ThreeReferenceLiouvilleGreen.lean#L124) — proved, no admission.
- [Complex.ThreeReferenceLiouvilleGreen.Data.joinVariation](DLMFMathlib/Analysis/ODE/ThreeReferenceLiouvilleGreen.lean#L98) — definition, no admission.
- [Complex.ThreeReferenceLiouvilleGreen.Data.joinVariation_def](DLMFMathlib/Analysis/ODE/ThreeReferenceLiouvilleGreen.lean#L102) — proved, no admission.
- [Complex.ThreeReferenceLiouvilleGreen.Data.normalized_coefficient_endpoint_symmetry](DLMFMathlib/Analysis/ODE/ThreeReferenceLiouvilleGreen.lean#L171) — direct admission.
- [Complex.ThreeReferenceLiouvilleGreen.Data.relativeError](DLMFMathlib/Analysis/ODE/ThreeReferenceLiouvilleGreen.lean#L106) — definition, no admission.
- [Complex.ThreeReferenceLiouvilleGreen.Data.relativeError_def](DLMFMathlib/Analysis/ODE/ThreeReferenceLiouvilleGreen.lean#L110) — proved, no admission.
- [Complex.ThreeReferenceLiouvilleGreen.Data.sourceAmplitude](DLMFMathlib/Analysis/ODE/ThreeReferenceLiouvilleGreen.lean#L90) — definition, no admission.
- [Complex.ThreeReferenceLiouvilleGreen.Data.sourceAmplitude_def](DLMFMathlib/Analysis/ODE/ThreeReferenceLiouvilleGreen.lean#L94) — proved, no admission.
- [Complex.ThreeReferenceLiouvilleGreen.IsRealGeometry](DLMFMathlib/Analysis/ODE/ThreeReferenceRealConnections.lean#L32) — definition, no admission.
- [Complex.ThreeReferenceLiouvilleGreen.cosine_connection_of_canonical_family](DLMFMathlib/Analysis/ODE/ThreeReferenceRealConnections.lean#L98) — direct admission.
- [Complex.ThreeReferenceLiouvilleGreen.real_connection_of_canonical_family](DLMFMathlib/Analysis/ODE/ThreeReferenceRealConnections.lean#L62) — direct admission.
- [Complex.ThreeReferenceScattering.rightRelativeError](DLMFMathlib/Analysis/ODE/ThreeReferenceScattering.lean#L32) — definition, no admission.
- [Complex.ThreeReferenceScattering.rightRelativeError_def](DLMFMathlib/Analysis/ODE/ThreeReferenceScattering.lean#L39) — proved, no admission.
- [Complex.ThreeReferenceScattering.scattering_probabilities_of_canonical_family](DLMFMathlib/Analysis/ODE/ThreeReferenceScattering.lean#L51) — direct admission.
- [Complex.exists_amplitude_phase_error](DLMFMathlib/Analysis/Complex/AmplitudePhaseError.lean#L24) — direct admission.
- [DLMF.AsymptoticApproximations.ComplexBesselComparison.exists_complex_simplePole_K_recessive](DLMF/AsymptoticApproximations/ODE/ComplexBesselEndpoint.lean#L32) — direct admission.
- [DLMF.AsymptoticApproximations.SimplePoleConnection.tendsto_parameterRecessive_frobenius](DLMF/AsymptoticApproximations/Connections/SimplePoleParameter.lean#L38) — direct admission.
- [DLMF.AsymptoticApproximations.SimplePoleConnection.tendsto_physical_frobenius_normalizer](DLMF/AsymptoticApproximations/Connections/SimplePoleParameter.lean#L51) — direct admission.
- [DLMF.Confluent.WeberScattering.isBoundState_iff_odd_square](DLMF/ParabolicCylinder/ScatteringAndBoundStates.lean#L129) — direct admission.
- [DLMF.Confluent.WeberScattering.outgoingRight_eq_incoming_add_reflected](DLMF/ParabolicCylinder/ScatteringAndBoundStates.lean#L114) — direct admission.
- [DLMF.Confluent.WeberScattering.outgoingRight_flux](DLMF/ParabolicCylinder/ScatteringAndBoundStates.lean#L102) — direct admission.
- [DLMF.Confluent.WeberScattering.transmission_and_reflection](DLMF/ParabolicCylinder/ScatteringAndBoundStates.lean#L121) — direct admission.
- [ODE.SimplePoleScaling.dilated_residual](DLMFMathlib/Analysis/ODE/SimplePoleScaling.lean#L35) — direct admission.
- [ODE.SimplePoleScaling.exists_local_principalCut_parameterization](DLMFMathlib/Analysis/ODE/SimplePoleScaling.lean#L49) — direct admission.
- [ODE.TwoTurningPoints.IsScatteringState](DLMFMathlib/Analysis/ODE/TwoTurningPoints.lean#L78) — definition, no admission.
- [ODE.wronskian_cyclic_sum](DLMFMathlib/Analysis/ODE/SymmetricSquareGeneral.lean#L45) — proved, no admission.
