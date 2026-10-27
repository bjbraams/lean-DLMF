/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.LHopital
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.BoxIntegral.Basic
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.Order.LeftRight
public import TauCeti.Analysis.Green.IndexOne
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Stokes

/-!
# DLMF §§1.4–1.7 results already in Mathlib and TauCeti

The `dlmf_upstream` commands below are checked pointers to upstream declarations for
DLMF §§1.4–1.7 (calculus of one and several variables, vector calculus, inequalities),
deliberately not duplicate local theorems. Green's theorem in the plane (1.6.44) is TauCeti's
`TauCeti.Green.green_ac_index_one` (by the Tau Ceti contributors), and Stokes's theorem for
differential forms on manifolds with boundary is TauCeti's
`TauCeti.integralTopForm_mextDeriv`.
-/

/- §1.4(i)–(ii): monotonicity and continuity. -/
dlmf_upstream 1.4.i MonotoneOn
  "exact: nondecreasing on I (StrictMonoOn, AntitoneOn, StrictAntiOn for the other cases)"
dlmf_upstream 1.4.E1 ContinuousWithinAt
  "exact: right continuity at c is ContinuousWithinAt f (Ici c) c"
dlmf_upstream 1.4.E3 continuousAt_iff_continuous_left_right
  "exact: continuity at c iff continuity from the left (Iic c) and the right (Ici c)"
dlmf_upstream 1.4.ii ContinuousOn
  "exact: C(a, b) and C[a, b] are ContinuousOn f (Ioo a b) and ContinuousOn f (Icc a b)"

/- §1.4(iii): derivatives. -/
dlmf_upstream 1.4.E4 hasDerivAt_iff_tendsto_slope_zero
  "exact: f'(x) = lim_{h→0} (f(x + h) - f(x))/h"
dlmf_upstream 1.4.E5 deriv_add "exact: for f, g differentiable at x"
dlmf_upstream 1.4.E6 deriv_mul "exact: for f, g differentiable at x"
dlmf_upstream 1.4.E7 deriv_div "exact: for f, g differentiable at x, g(x) ≠ 0"
dlmf_upstream 1.4.E8 iteratedDeriv_succ "exact: f^(n) = d/dx f^(n-1) (with 1.4.E9)"
dlmf_upstream 1.4.E9 iteratedDeriv_succ "exact: iteratedDeriv (n + 1) f = deriv (iteratedDeriv n f)"
dlmf_upstream 1.4.iii ContDiffOn
  "exact: f ∈ Cⁿ(I) is ContDiffOn ℝ n f I, C^∞ is n = ∞"
dlmf_upstream 1.4.E10 deriv_comp "exact: chain rule h'(x) = f'(g(x)) g'(x)"
dlmf_upstream 1.4.iii IsLocalMax.deriv_eq_zero
  "exact: f'(c) = 0 at a local maximum (IsLocalMin.deriv_eq_zero for minima)"
dlmf_upstream 1.4.E11 exists_deriv_eq_slope
  "exact: mean value theorem, f continuous on [a, b], differentiable on (a, b)"
dlmf_upstream 1.4.iii monotoneOn_of_deriv_nonneg
  "exact: f' ≥ 0 on (a, b) implies f nondecreasing (see also antitoneOn_of_deriv_nonpos)"
dlmf_upstream 1.4.E12 iteratedDeriv_mul
  "exact: Leibniz's formula, f and g n times differentiable (ContDiffAt) at x"
dlmf_upstream 1.4.E15 deriv.lhopital_zero_nhdsNE
  "partial: the case 0/0 of L'Hôpital's rule; the case ∞/∞ is lhopital_atTop_nhdsNE"

/- §1.4(iv)–(v): integrals. -/
dlmf_upstream 1.4.iv intervalIntegral.integral_eq_sub_of_hasDerivAt
  "exact: F' = f gives ∫ f = F + C (also 1.4.26)"
dlmf_upstream 1.4.E16 intervalIntegral.integral_mul_deriv_eq_deriv_mul
  "different convention: definite form of integration by parts, ∫ₐᵇ u v' = u v|ₐᵇ - ∫ₐᵇ u' v"
dlmf_upstream 1.4.E17 integral_pow "special case: definite integral ∫ₐᵇ xⁿ = (bⁿ⁺¹ - aⁿ⁺¹)/(n + 1)"
dlmf_upstream 1.4.E18 BoxIntegral.HasIntegral
  "different convention: Riemann integral via tagged box partitions with IntegrationParams.Riemann"
dlmf_upstream 1.4.v BoxIntegral.integrable_of_continuousOn
  "exact: continuous functions are Riemann integrable"
dlmf_upstream 1.4.v BoxIntegral.integrable_of_bounded_and_ae_continuousWithinAt
  "stronger: bounded and a.e. continuous (covers piecewise continuous) is Riemann integrable"
dlmf_upstream 1.4.E20 intervalIntegral.integral_symm "exact: ∫ₐᵇ f = -∫ᵇₐ f"
dlmf_upstream 1.4.E21 intervalIntegral.integral_add_adjacent_intervals
  "exact: for f integrable on both intervals"
dlmf_upstream 1.4.E22 MeasureTheory.intervalIntegral_tendsto_integral_Ioi
  "stronger: for f integrable on (a, ∞), ∫ₐᵇ f → ∫_(a,∞) f as b → ∞"
dlmf_upstream 1.4.v MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_tendsto
  "exact: absolute convergence of ∫ₐ^∞ gives integrability"
dlmf_upstream 1.4.E26 intervalIntegral.integral_eq_sub_of_hasDerivAt
  "stronger: F' = f on [a, b] with f integrable (continuity not needed)"
dlmf_upstream 1.4.E27 intervalIntegral.integral_hasDerivAt_right
  "exact: d/dx ∫ₐˣ f = f(x) at points of continuity"
dlmf_upstream 1.4.E28 intervalIntegral.integral_comp_mul_deriv
  "special case: φ' continuous on [a, b] and f continuous"
dlmf_upstream 1.4.E32 MeasureTheory.MemLp
  "exact: square integrability is MemLp f 2, ‖f‖₂ is eLpNorm f 2"
dlmf_upstream 1.4.E33 eVariationOn
  "exact: total variation, the supremum over finite increasing families in the set"
dlmf_upstream 1.4.v LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  "exact: Jordan decomposition f = g - h, g, h nondecreasing"
dlmf_upstream 1.4.v variationOnFromTo.monotoneOn
  "exact: x ↦ 𝒱_{a,x}(f) is nondecreasing (variationOnFromTo.sub_self_monotoneOn for 𝒱 - f)"

/- §1.4(vi)–(viii): Taylor's theorem, extrema, convexity. -/
dlmf_upstream 1.4.E35 taylorWithinEval "exact: the Taylor polynomial ∑ f⁽ᵏ⁾(a)(x - a)ᵏ/k!"
dlmf_upstream 1.4.E36 taylor_mean_remainder_lagrange
  "exact: Lagrange remainder, f ∈ Cⁿ[a, x] with f⁽ⁿ⁾ differentiable on (a, x)"
dlmf_upstream 1.4.E37 taylor_integral_remainder "exact: integral remainder, f ∈ Cⁿ⁺¹[a, x]"
dlmf_upstream 1.4.vii isLocalMax_of_deriv_deriv_neg
  "exact: f'(x₀) = 0, f''(x₀) < 0 gives a local maximum (isLocalMin_of_deriv_deriv_pos)"
dlmf_upstream 1.4.E38 ConvexOn "exact: ConvexOn ℝ (Ioo a b) f"
dlmf_upstream 1.4.viii convexOn_of_deriv2_nonneg "exact: f'' ≥ 0 implies convexity"

/- §1.5: several variables. -/
dlmf_upstream 1.5.E1 Metric.continuousAt_iff
  "exact: with the sup norm on ℝ × ℝ this is the ε-δ form 1.5.2"
dlmf_upstream 1.5.E6 ContDiffAt.isSymmSndFDerivAt
  "stronger: symmetry of the second Fréchet derivative of a C² function"
dlmf_upstream 1.5.E7 HasFDerivAt.comp_hasDerivAt "stronger: chain rule in Banach spaces"
dlmf_upstream 1.5.i eventually_apply_eq_iff_implicitFunctionOfBivariate
  "stronger: bivariate implicit function theorem in Banach spaces, zero set = graph of ψ"
dlmf_upstream 1.5.i hasStrictFDerivAt_implicitFunctionOfBivariate
  "partial: ψ'(a) = -F_y⁻¹ F_x at the base point only"
dlmf_upstream 1.5.E10 polarCoord
  "different convention: polar coordinates with φ ∈ (-π, π) (DLMF 0 ≤ φ ≤ 2π)"
dlmf_upstream 1.5.E24 hasDerivAt_integral_of_dominated_loc_of_deriv_le
  "different convention: differentiation under the integral sign with a dominating function"
dlmf_upstream 1.5.E25 BoxIntegral.TaggedPrepartition
  "different convention: tagged partitions of a box (the grid partitions of 1.5.25–1.5.26)"
dlmf_upstream 1.5.E26 BoxIntegral.TaggedPrepartition
  "different convention: tagged partitions of a box (the grid partitions of 1.5.25–1.5.26)"
dlmf_upstream 1.5.E27 BoxIntegral.HasIntegral
  "different convention: Riemann double integral via tagged box partitions"
dlmf_upstream 1.5.E28 Set.indicator "exact: f* = D.indicator f, the extension by zero"
dlmf_upstream 1.5.E29 MeasureTheory.integral_indicator
  "exact: ∬_D f = ∬_R f* with f* the extension by zero"
dlmf_upstream 1.5.E36 MeasureTheory.integral_integral_swap
  "stronger: Fubini's theorem for f integrable on the product"
dlmf_upstream 1.5.E42 MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
  "special case: Φ one-to-one on all of D* (no exceptional null set)"

/- §1.6: vectors and vector calculus. -/
dlmf_upstream 1.6.E1 Matrix.vecCons
  "different convention: vectors of ℝ³ are Fin 3 → ℝ, written ![a₁, a₂, a₃]"
dlmf_upstream 1.6.E2 dotProduct "exact: a ⬝ᵥ b = ∑ aᵢ bᵢ"
dlmf_upstream 1.6.E4 InnerProductGeometry.cos_angle "exact: in EuclideanSpace ℝ (Fin 3)"
dlmf_upstream 1.6.E5 Pi.basisFun "exact: the unit vectors i, j, k are Pi.single 0 1, …"
dlmf_upstream 1.6.E6 pi_eq_sum_univ "exact: a = ∑ aᵢ eᵢ (also 1.6.13)"
dlmf_upstream 1.6.E13 pi_eq_sum_univ "exact: aⱼ eⱼ = a"
dlmf_upstream 1.6.E9 cross_apply "exact: components of a × b"
dlmf_upstream 1.6.E10 cross_cross_eq_smul_sub_smul'
  "exact: a × (b × c) = (a · c) b - (b · a) c"
dlmf_upstream 1.6.E11 cross_cross_eq_smul_sub_smul
  "exact: (a × b) × c = (a · c) b - (b · c) a"
dlmf_upstream 1.6.i triple_product_eq_det "exact: a · (b × c) = det (a, b, c)"
dlmf_upstream 1.6.E12 dotProduct "exact: aⱼbⱼ = ∑ aⱼbⱼ"
dlmf_upstream 1.6.E44 TauCeti.Green.green_ac_index_one
  "stronger: closed absolutely continuous curve, winding number 1 on the enclosed region"
dlmf_upstream 1.6.E57 TauCeti.integralTopForm_mextDeriv
  "different convention: Stokes for compactly supported C¹ forms on oriented manifolds"
dlmf_upstream 1.6.E58 MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable
  "special case: divergence theorem on a rectangular box in ℝⁿ"

/- §1.7: inequalities. -/
dlmf_upstream 1.7.E1 Finset.sum_mul_sq_le_sq_mul_sq "exact: (∑ aⱼbⱼ)² ≤ (∑ aⱼ²)(∑ bⱼ²)"
dlmf_upstream 1.7.E2 Real.inner_le_Lp_mul_Lq_of_nonneg "exact: Hölder for aⱼ, bⱼ ≥ 0"
dlmf_upstream 1.7.E3 Real.Lp_add_le_of_nonneg "exact: Minkowski for p ≥ 1, aⱼ, bⱼ ≥ 0"
dlmf_upstream 1.7.E5 MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
  "exact: Hölder for integrals, f, g ≥ 0 in Lᵖ, L^q"
dlmf_upstream 1.7.E6 MeasureTheory.eLpNorm_add_le
  "different convention: Minkowski for eLpNorm, p ≥ 1"
dlmf_upstream 1.7.E7 Real.geom_mean_le_arith_mean_weighted "exact: G ≤ A (weighted form)"
dlmf_upstream 1.7.E7 Real.harm_mean_le_geom_mean "exact: H ≤ G"
dlmf_upstream 1.7.E7 Real.geom_mean_eq_arith_mean_weighted_iff_of_pos
  "exact: G = A iff all aⱼ are equal (positive weights)"
dlmf_upstream 1.7.E9 Real.rpow_arith_mean_le_arith_mean_rpow "special case: M(1) ≤ M(p), p ≥ 1"
dlmf_upstream 1.7.E10 ConvexOn.map_integral_le
  "partial: Jensen for a probability measure, φ convex and continuous on a closed convex set"
