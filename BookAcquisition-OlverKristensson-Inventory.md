# Olver and Kristensson acquisition inventory

The exact claim mappings are in BookAcquisition-Olver.md and BookAcquisition-Kristensson.md.
Olver Chapters10–12 contain41 mapped IDs; Kristensson contains125 mapped IDs. The generic
and area theorem targets are mostly admitted, as authorized. Coverage is statement acquisition,
not a claim that their proofs have been completed. Definitions and their displayed defining
interfaces are proved. No standalone axioms were introduced.

This inventory records the44 advanced Olver modules most recently completed: 100 definitions
or structures, 297 theorem/lemma declarations, and 159 literal admissions. Counts are textual;
a theorem can contain multiple mathematical conclusions. Earlier Kristensson/Olver acquisitions
are referenced individually in the exact ledgers and are not recounted here.

## Validation

All Lake builds were queued under /tmp/DLMF-book-acquisition.lock. Individual source checks
use autoImplicit=false and relaxedAutoImplicit=false. The final full integration build belongs
to the parent task. Some last target builds are queued behind that shared full build. A completed source-local
audit elaborates all44 advanced modules plus Basic.WhittakerLogarithmic successfully and
checks102 definition/structure/API declarations: none has a sorryAx dependency. Exact
results are saved in BookAcquisition-OlverKristensson-DefinitionAxioms.json.

The import survey passes: foundational imports0, Basic-closure violations0, missing imports0,
file cycles0. Potential newly introduced two-way area pairs are Airy/AsymptoticApproximations,
AsymptoticApproximations/Confluent, and AlgebraicAnalytic/OrthogonalPolynomials; the parent
maintains the task-baseline comparison. git diff --check passes.

A source-local #print axioms audit confirms all six new positive-real Airy sign/monotonicity
proofs depend only on propext, Classical.choice and Quot.sound. Both pure Mathlib Lipschitz
proofs likewise depend only on propext, Classical.choice and Quot.sound; their audit is in
/tmp/olver-lipschitz-axioms.log. The new coefficient/error
properties with sorry remain explicit theorem-layer admissions.

Confirmed mathematical qualifications and source evidence are in BookAcquisition-RevisionNotes.md:
Olver9.10 coefficient order,11.11 controlled inner paths,12.16 higher-pole residue obstruction,
finite-order Debye I normalization, signed Legendre coefficient normalization; Kristensson
partial-fraction degree, exceptional Q leading coefficients and negative-integer degree poles.
SYNOPSIS files were left unchanged.

## Advanced module inventory

- `DLMFMathlib.Analysis.Calculus.WeightedRayPrimitive`: 105 lines, 1 definitions/structures, 8 theorems/lemmas, 7 literal admissions.
- `DLMFMathlib.Analysis.Asymptotics.LipschitzComposition`: 66 lines, 0 definitions/structures, 2 theorems/lemmas, 0 literal admissions.
- `DLMFMathlib.Analysis.ODE.ComplexLiouvilleGreen`: 170 lines, 1 definitions/structures, 5 theorems/lemmas, 4 literal admissions.
- `DLMFMathlib.Analysis.ODE.ComplexLiouvilleGreenExpansion`: 163 lines, 2 definitions/structures, 10 theorems/lemmas, 4 literal admissions.
- `DLMFMathlib.Analysis.ODE.ComplexLiouvilleGreenUniform`: 129 lines, 0 definitions/structures, 3 theorems/lemmas, 3 literal admissions.
- `DLMFMathlib.Analysis.ODE.ComplexLiouvilleGreenLogarithm`: 64 lines, 0 definitions/structures, 3 theorems/lemmas, 3 literal admissions.
- `DLMFMathlib.Analysis.ODE.ComplexLiouvilleTransformation`: 39 lines, 0 definitions/structures, 1 theorems/lemmas, 1 literal admissions.
- `DLMFMathlib.Analysis.ODE.LiouvilleGreenSingularCoefficients`: 161 lines, 1 definitions/structures, 8 theorems/lemmas, 5 literal admissions.
- `DLMFMathlib.Analysis.ODE.AffineLiouvilleGreen`: 236 lines, 3 definitions/structures, 11 theorems/lemmas, 5 literal admissions.
- `DLMFMathlib.Analysis.ODE.ComplexGreenEquation`: 104 lines, 0 definitions/structures, 2 theorems/lemmas, 2 literal admissions.
- `DLMFMathlib.Analysis.ODE.InhomogeneousExpansion`: 101 lines, 2 definitions/structures, 7 theorems/lemmas, 2 literal admissions.
- `DLMFMathlib.Analysis.ODE.InhomogeneousGreenBounds`: 87 lines, 1 definitions/structures, 3 theorems/lemmas, 2 literal admissions.
- `DLMFMathlib.Analysis.ODE.TurningPointCoordinates`: 252 lines, 5 definitions/structures, 19 theorems/lemmas, 13 literal admissions.
- `DLMFMathlib.Analysis.ODE.TurningPointCoefficients`: 156 lines, 2 definitions/structures, 10 theorems/lemmas, 5 literal admissions.
- `DLMFMathlib.Analysis.ODE.TurningPointCoefficientBounds`: 94 lines, 0 definitions/structures, 2 theorems/lemmas, 2 literal admissions.
- `DLMFMathlib.Analysis.ODE.ForcedTurningPoint`: 109 lines, 2 definitions/structures, 5 theorems/lemmas, 2 literal admissions.
- `DLMFMathlib.Analysis.ODE.ShiftedTurningPoint`: 111 lines, 3 definitions/structures, 5 theorems/lemmas, 2 literal admissions.
- `DLMFMathlib.Analysis.ODE.SimplePoleCoefficients`: 152 lines, 2 definitions/structures, 9 theorems/lemmas, 4 literal admissions.
- `DLMFMathlib.Analysis.ODE.SimplePoleCoefficientBounds`: 63 lines, 0 definitions/structures, 1 theorems/lemmas, 1 literal admissions.
- `DLMFMathlib.Analysis.ODE.SimplePoleRealUniform`: 91 lines, 2 definitions/structures, 4 theorems/lemmas, 2 literal admissions.
- `DLMFMathlib.Analysis.ODE.TransitionCoordinates`: 99 lines, 0 definitions/structures, 4 theorems/lemmas, 4 literal admissions.
- `DLMFMathlib.Analysis.ODE.PowerTransitionCoefficients`: 86 lines, 1 definitions/structures, 3 theorems/lemmas, 2 literal admissions.
- `DLMFMathlib.Analysis.ODE.SeparatedScaling`: 64 lines, 0 definitions/structures, 2 theorems/lemmas, 2 literal admissions.
- `DLMF.AsymptoticApproximations.ODE.AiryEnvelopes`: 187 lines, 8 definitions/structures, 20 theorems/lemmas, 10 literal admissions.
- `DLMF.AsymptoticApproximations.ODE.BesselEnvelopes`: 141 lines, 3 definitions/structures, 15 theorems/lemmas, 10 literal admissions.
- `DLMF.AsymptoticApproximations.ODE.RealAiryPerturbation`: 88 lines, 1 definitions/structures, 3 theorems/lemmas, 1 literal admissions.
- `DLMF.AsymptoticApproximations.ODE.RealAiryExpansion`: 93 lines, 0 definitions/structures, 2 theorems/lemmas, 2 literal admissions.
- `DLMF.AsymptoticApproximations.ODE.RealAiryZeros`: 75 lines, 0 definitions/structures, 1 theorems/lemmas, 1 literal admissions.
- `DLMF.AsymptoticApproximations.ODE.ComplexAiryExpansion`: 117 lines, 0 definitions/structures, 2 theorems/lemmas, 2 literal admissions.
- `DLMF.AsymptoticApproximations.ODE.RealBesselExpansion`: 246 lines, 8 definitions/structures, 11 theorems/lemmas, 3 literal admissions.
- `DLMF.AsymptoticApproximations.ODE.RealBesselZeros`: 83 lines, 0 definitions/structures, 2 theorems/lemmas, 2 literal admissions.
- `DLMF.AsymptoticApproximations.ODE.RealBesselUniform`: 83 lines, 0 definitions/structures, 2 theorems/lemmas, 2 literal admissions.
- `DLMF.AsymptoticApproximations.ODE.ComplexBesselEnvelopes`: 111 lines, 4 definitions/structures, 8 theorems/lemmas, 4 literal admissions.
- `DLMF.AsymptoticApproximations.ODE.ComplexBesselExpansion`: 284 lines, 8 definitions/structures, 13 theorems/lemmas, 5 literal admissions.
- `DLMF.AsymptoticApproximations.ODE.RadialScattering`: 128 lines, 4 definitions/structures, 7 theorems/lemmas, 3 literal admissions.
- `DLMF.Airy.ComplexEnvelopes`: 164 lines, 9 definitions/structures, 16 theorems/lemmas, 6 literal admissions.
- `DLMF.Airy.RealOrderProperties`: 108 lines, 0 definitions/structures, 8 theorems/lemmas, 2 literal admissions.
- `DLMF.Bessel.Debye`: 167 lines, 5 definitions/structures, 15 theorems/lemmas, 8 literal admissions.
- `DLMF.Bessel.DebyeContinuation`: 154 lines, 6 definitions/structures, 10 theorems/lemmas, 3 literal admissions.
- `DLMF.Bessel.ForcedLargeOrder`: 110 lines, 2 definitions/structures, 8 theorems/lemmas, 5 literal admissions.
- `DLMF.Bessel.TurningPointExpansion`: 174 lines, 8 definitions/structures, 11 theorems/lemmas, 3 literal admissions.
- `DLMF.Bessel.TurningPointZeros`: 69 lines, 0 definitions/structures, 2 theorems/lemmas, 2 literal admissions.
- `DLMF.Legendre.SimplePoleExpansion`: 192 lines, 4 definitions/structures, 9 theorems/lemmas, 5 literal admissions.
- `DLMF.Legendre.AnalyticNeumannExpansion`: 79 lines, 2 definitions/structures, 5 theorems/lemmas, 3 literal admissions.
