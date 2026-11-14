# Olver Chapters 1–4: acquired modules and validation

The exact entry and subclaim mappings are in [BookAcquisition-Olver.md](BookAcquisition-Olver.md).
This list records the modules added while closing the Chapter 1–4 gaps. Admissions are
specifications for later proof rounds; a successful build is not a claim that they are proved.

- `DLMF.Airy.MaclaurinRecurrence`
- `DLMF.AsymptoticApproximations.Integrals.SaddleCoefficients`
- `DLMF.Bessel.HankelAndNormalConvergence`
- `DLMF.Bessel.RealDebyeExpansion`
- `DLMF.Gamma.DigammaPoles`
- `DLMF.IncompleteGamma.LaplaceTailMajorant`
- `DLMF.IncompleteGamma.StieltjesExponentialIntegral`
- `DLMF.OrthogonalPolynomials.LeastSquaresProjection`
- `DLMF.OrthogonalPolynomials.LegendreComplexLaplace`
- `DLMF.OrthogonalPolynomials.LegendreDarbouxLeading`
- `DLMF.OrthogonalPolynomials.PrescribedLeadingCoefficients`
- `DLMFMathlib.Analysis.Asymptotics.CompatibleProductScale`
- `DLMFMathlib.Analysis.Asymptotics.ElementaryLaplaceRemainders`
- `DLMFMathlib.Analysis.Asymptotics.EndpointLaplaceSeries`
- `DLMFMathlib.Analysis.Asymptotics.FourierEndpointIntegrableDerivative`
- `DLMFMathlib.Analysis.Asymptotics.IntegralMajorants`
- `DLMFMathlib.Analysis.Asymptotics.LaplaceAbsoluteMajorants`
- `DLMFMathlib.Analysis.Asymptotics.LaplaceMinimum`
- `DLMFMathlib.Analysis.Asymptotics.McMahonCoefficients`
- `DLMFMathlib.Analysis.Asymptotics.MorseStationaryPhase`
- `DLMFMathlib.Analysis.Asymptotics.NonstationaryPhaseEndpoints`
- `DLMFMathlib.Analysis.Asymptotics.PowerGrowthCounterexamples`
- `DLMFMathlib.Analysis.Asymptotics.PrescribedSeries`
- `DLMFMathlib.Analysis.Asymptotics.PrimitiveExpansion`
- `DLMFMathlib.Analysis.Asymptotics.RealInverseError`
- `DLMFMathlib.Analysis.Asymptotics.SingularFourierRemainders`
- `DLMFMathlib.Analysis.Asymptotics.StationaryEndpointLeading`
- `DLMFMathlib.Analysis.Complex.CriticalPointNormalForm`
- `DLMFMathlib.Analysis.Complex.ExteriorLaurentAsymptotics`
- `DLMFMathlib.Analysis.Complex.HigherSectorDerivatives`
- `DLMFMathlib.Analysis.Complex.SectorInverse`
- `DLMFMathlib.Analysis.Complex.UniformPowerSeriesTail`
- `DLMFMathlib.Analysis.Fourier.ImproperRiemannLebesgue`
- `DLMFMathlib.Analysis.Integral.LaplaceFiniteRemainder`
- `DLMFMathlib.RingTheory.PowerSeries.LogarithmicRecurrence`
- `DLMFMathlib.Topology.Algebra.InfiniteSum.EvenInt`

The two complex-power growth comparisons, meromorphy of digamma, the unique positive-real
Gamma minimum, even-bilateral-series pairing, normalized saddle coefficient, and Bessel-square
pairing are proved adapters. All nine substantive adapter proofs pass transitive axiom
audit with only `propext`, `Classical.choice` and `Quot.sound`, and no `sorryAx`.
The authoritative combined target build passed (12,801 jobs) for all 36 listed modules;
all strict source checks also passed. The only newly confirmed Chapter 1–4 synopsis defect is the sign
convention in O-1.14; the source-correct inversion statement is acquired and the synopsis
has been left unchanged, with evidence in the shared revision notes.
