/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Harmonic.MeanValue
public import Mathlib.Analysis.Complex.Harmonic.Poisson
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.Analytic.RadiusLiminf
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Calculus.Conformal.NormedSpace
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Conformal
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.DerivedSet
public import TauCeti.Analysis.Contour.HomologyCauchy
public import TauCeti.Analysis.Contour.Residue.Basic
public import TauCeti.Analysis.Contour.Residue.Theorem
public import TauCeti.Analysis.Contour.Argument.Cycle
public import TauCeti.Analysis.Contour.Winding.UnboundedComponent
public import TauCeti.Analysis.Complex.Conformal.Rouche
public import TauCeti.Analysis.Complex.Conformal.Reflection.Principle

/-!
# DLMF §§1.9–1.10 results already in Mathlib or Tau Ceti

Checked pointers to Mathlib and Tau Ceti declarations for DLMF §§1.9–1.10 (calculus and
functions of a complex variable). Branch conventions: Mathlib's `Complex.arg` takes values in
`(-π, π]` (`Complex.arg_mem_Ioc`), DLMF's single-valued principal phase; DLMF's
`-π ≤ ph z ≤ π` is two-valued on `(-∞, 0)`, where Lean takes `π`. `Complex.log` and `cpow` are
the principal branches of DLMF §4.2. Mathlib's `HasSum` is unconditional (absolute convergence
over `ℂ`); DLMF's series converge as partial sums. Tau Ceti's Cauchy, residue and argument
theorems are in the homology form (holomorphy on an open set containing the curve and a
null-homologous curve, winding numbers as weights); the DLMF forms for simple closed contours are
admitted in `DLMF.AlgebraicAnalytic.Complex.Calculus` and `.Functions`.
-/

/- §1.9(i) Complex numbers. -/
dlmf_upstream 1.9.E1 Complex.re_add_im "exact: z = ℜz + iℑz"
dlmf_upstream 1.9.E2 Complex.re "definition: real part"
dlmf_upstream 1.9.E2 Complex.im "definition: imaginary part"
dlmf_upstream 1.9.E3 Complex.norm_mul_cos_arg "exact: x = r cos θ with θ = arg z"
dlmf_upstream 1.9.E3 Complex.norm_mul_sin_arg "exact: y = r sin θ with θ = arg z"
dlmf_upstream 1.9.E4 Complex.norm_eq_sqrt_sq_add_sq "exact: r = (x² + y²)^{1/2}"
dlmf_upstream 1.9.E7 Complex.arg_mem_Ioc "convention: principal phase in (-π, π]"
dlmf_upstream 1.9.E8 Complex.abs_re_le_norm "exact: |ℜz| ≤ |z|"
dlmf_upstream 1.9.E8 Complex.abs_im_le_norm "exact: |ℑz| ≤ |z|"
dlmf_upstream 1.9.E9 Complex.norm_mul_exp_arg_mul_I "exact: z = r e^{iθ}, θ = arg z"
dlmf_upstream 1.9.E10 Complex.exp_mul_I "exact: e^{iθ} = cos θ + i sin θ (complex θ)"
dlmf_upstream 1.9.E11 Complex.conj_re "exact: ℜ z̄ = x"
dlmf_upstream 1.9.E11 Complex.conj_im "exact: ℑ z̄ = -y"
dlmf_upstream 1.9.E12 Complex.norm_conj "exact: |z̄| = |z|"
dlmf_upstream 1.9.E13 Complex.arg_conj "principal values: arg z̄ = -arg z except on (-∞, 0)"
dlmf_upstream 1.9.E14 Complex.add_re "exact: real part of a sum"
dlmf_upstream 1.9.E14 Complex.add_im "exact: imaginary part of a sum"
dlmf_upstream 1.9.E14 Complex.sub_re "exact: real part of a difference"
dlmf_upstream 1.9.E14 Complex.sub_im "exact: imaginary part of a difference"
dlmf_upstream 1.9.E15 Complex.mul_re "exact: ℜ(z₁z₂) = x₁x₂ - y₁y₂"
dlmf_upstream 1.9.E15 Complex.mul_im "exact: ℑ(z₁z₂) = x₁y₂ + x₂y₁"
dlmf_upstream 1.9.E16 Complex.div_re "exact: real part of a quotient"
dlmf_upstream 1.9.E16 Complex.div_im "exact: imaginary part of a quotient"
dlmf_upstream 1.9.E17 Complex.norm_mul "exact: |z₁z₂| = |z₁||z₂|"
dlmf_upstream 1.9.E18 Complex.arg_mul_coe_angle "principal values: equality modulo 2π"
dlmf_upstream 1.9.E19 Complex.norm_div "exact: |z₁/z₂| = |z₁|/|z₂|"
dlmf_upstream 1.9.E20 Complex.arg_div_coe_angle "principal values: equality modulo 2π"
dlmf_upstream 1.9.E22 Complex.cos_add_sin_mul_I_pow "special case: n ∈ ℕ, complex θ"
dlmf_upstream 1.9.E23 norm_add_le "exact: |z₁ + z₂| ≤ |z₁| + |z₂|"
dlmf_upstream 1.9.E23 abs_norm_sub_norm_le "exact: ||z₁| - |z₂|| ≤ |z₁ - z₂|"

/- §1.9(ii) Continuity, point sets and differentiation. -/
dlmf_upstream 1.9.ii Metric.continuousAt_iff "definition: ε-δ continuity"
dlmf_upstream 1.9.ii Metric.isOpen_iff "definition: open sets"
dlmf_upstream 1.9.ii accPt_iff_frequently "definition: limit (accumulation) points"
dlmf_upstream 1.9.ii closure_eq_self_union_derivedSet "exact: closure = S ∪ limit points"
dlmf_upstream 1.9.ii IsOpen.isConnected_iff_isPathConnected
  "related: a domain is an open connected (path-connected) set"
dlmf_upstream 1.9.E24 hasDerivAt_iff_tendsto_slope "definition: f'(z) as a limit"
dlmf_upstream 1.9.ii HasDerivAt.continuousAt "exact: differentiability implies continuity"
dlmf_upstream 1.9.ii Complex.analyticAt_iff_eventually_differentiableAt
  "exact: analytic at z₀ iff complex differentiable near z₀"
dlmf_upstream 1.9.ii AnalyticOnNhd.iterated_deriv "exact: derivatives of analytic functions"
dlmf_upstream 1.9.ii DifferentiableOn.analyticOnNhd "exact: holomorphic on open D is analytic"
dlmf_upstream 1.9.E26 AnalyticAt.harmonicAt_re "different notation: ℜf harmonic (Laplacian)"
dlmf_upstream 1.9.E26 AnalyticAt.harmonicAt_im "different notation: ℑf harmonic (Laplacian)"

/- §1.9(iii) Integration. -/
dlmf_upstream 1.9.iii TauCeti.Contour.IsPiecewiseC1On "definition: contours (piecewise C¹)"
dlmf_upstream 1.9.iii TauCeti.Contour.IsPiecewiseC1On.windingNumber_eq_zero_of_unbounded_component
  "exact: winding number 0 in unbounded components of the complement"
dlmf_upstream 1.9.E29 TauCeti.Contour.homologyCauchyTheorem
  "different hypotheses: f holomorphic on open Ω ⊇ C, C null-homologous in Ω"
dlmf_upstream 1.9.E29 Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
  "special case: C a circle, f continuous on the closed disc"
dlmf_upstream 1.9.E30 DiffContOnCl.circleIntegral_sub_inv_smul
  "special case: C a circle, f continuous on the closed disc"
dlmf_upstream 1.9.E31 DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul
  "special case: C a circle, z₀ its centre"
dlmf_upstream 1.9.iii Differentiable.apply_eq_apply_of_bounded
  "exact: Liouville's theorem, bounded entire functions are constant"
dlmf_upstream 1.9.E32 TauCeti.Contour.windingNumber
  "definition: winding number (principal value of the index integral)"
dlmf_upstream 1.9.E33 InnerProductSpace.HarmonicOnNhd.circleAverage_eq
  "different notation: mean value as circleAverage, u harmonic on the closed disc"
dlmf_upstream 1.9.E34 InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul
  "related: Poisson representation of a harmonic function (Mathlib poissonKernel)"

/- §1.9(iv) Conformal mapping. -/
dlmf_upstream 1.9.iv OnePoint "definition: the extended plane ℂ ∪ {∞} is OnePoint ℂ"
dlmf_upstream 1.9.iv DifferentiableAt.conformalAt "exact: f'(z₀) ≠ 0 gives a conformal map"
dlmf_upstream 1.9.iv InnerProductGeometry.ConformalAt.preserves_angle
  "exact: conformal maps preserve angles"

/- §1.9(v) Infinite sequences and series. -/
dlmf_upstream 1.9.v Complex.hasSum_iff "exact: convergence iff real and imaginary parts converge"
dlmf_upstream 1.9.v Summable.of_norm "exact: absolutely convergent series converge"
dlmf_upstream 1.9.v summable_of_ratio_test_tendsto_lt_one "exact: ratio test, convergence"
dlmf_upstream 1.9.v not_summable_of_ratio_test_tendsto_gt_one "exact: ratio test, divergence"
dlmf_upstream 1.9.E46 tendsto_pi_nhds "definition: pointwise convergence (product topology)"
dlmf_upstream 1.9.E47 Metric.tendstoUniformlyOn_iff "definition: uniform convergence"
dlmf_upstream 1.9.v tendstoUniformlyOn_tsum "exact: Weierstrass M-test"
dlmf_upstream 1.9.v summable_int_iff_summable_nat_and_neg
  "exact: doubly infinite series (pointwise)"

/- §1.9(vi) Power series. -/
dlmf_upstream 1.9.vi FormalMultilinearSeries.summable_norm_mul_pow
  "exact: absolute convergence inside the circle of convergence"
dlmf_upstream 1.9.vi FormalMultilinearSeries.not_summable_norm_of_radius_lt_nnnorm
  "exact: no absolute convergence outside the circle of convergence"
dlmf_upstream 1.9.vi FormalMultilinearSeries.hasFPowerSeriesOnBall
  "exact: the sum is analytic inside the circle of convergence"
dlmf_upstream 1.9.vi HasFPowerSeriesOnBall.tendstoUniformlyOn
  "exact: uniform convergence on smaller discs"
dlmf_upstream 1.9.E48 HasFPowerSeriesOnBall.factorial_smul
  "different notation: n! aₙ = f⁽ⁿ⁾(z₀)"
dlmf_upstream 1.9.E49 FormalMultilinearSeries.radius_eq_liminf
  "exact: Cauchy–Hadamard formula"
dlmf_upstream 1.9.E50 HasSum.add "exact: sum of series"
dlmf_upstream 1.9.E50 HasSum.sub "exact: difference of series"
dlmf_upstream 1.9.E51 tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
  "special case: Cauchy product of absolutely convergent series"

/- §1.9(vii) Inversion of limits. -/
dlmf_upstream 1.9.E66 Summable.tsum_prod
  "different notation: absolutely convergent double series as sums over ℕ × ℕ"
dlmf_upstream 1.9.E67 Summable.tsum_prod "exact: absolutely convergent double series"
dlmf_upstream 1.9.E67 Summable.tsum_comm "exact: the two repeated sums agree"
dlmf_upstream 1.9.E69 MeasureTheory.integral_tsum "stronger: hypothesis ∑ ∫⁻ ‖fₙ‖ < ∞"
dlmf_upstream 1.9.E70 MeasureTheory.integral_tsum "stronger: hypothesis ∑ ∫⁻ ‖fₙ‖ < ∞"
dlmf_upstream 1.9.E71 MeasureTheory.integral_tsum
  "stronger: hypothesis 1.9.70 (or 1.9.69, equivalent by Tonelli), no continuity"

/- §1.10(i) Taylor's theorem. -/
dlmf_upstream 1.10.E1 Complex.hasSum_taylorSeries_on_ball
  "exact: Taylor series on the disc of holomorphy"
dlmf_upstream 1.10.E1 DifferentiableOn.hasFPowerSeriesOnBall
  "exact: the radius of convergence is at least R"
dlmf_upstream 1.10.E2 NormedSpace.exp_eq_tsum "exact: exponential series"
dlmf_upstream 1.10.E3 Complex.hasSum_taylorSeries_log "exact: ln(1 + z), |z| < 1, principal branch"
dlmf_upstream 1.10.E4 Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero
  "different notation: coefficients Ring.choose (α + n - 1) n = (α)ₙ/n!, principal branch"
dlmf_upstream 1.10.i analyticOrderAt "definition: order of a zero"

/- §1.10(ii) Analytic continuation. -/
dlmf_upstream 1.10.ii AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
  "exact (D preconnected): identity theorem; DLMF omits connectedness of D₁ ∩ D₂"
dlmf_upstream 1.10.E5 TauCeti.exists_differentiableOn_eqOn_conj_of_symmetric
  "stronger: reflection across ℝ for a conjugation-symmetric open set"

/- §1.10(iii) Laurent series. -/
dlmf_upstream 1.10.iii Complex.differentiableOn_update_limUnder_of_bddAbove
  "stronger: a bounded isolated singularity is removable"
dlmf_upstream 1.10.iii MeromorphicOn "definition: meromorphic functions"
dlmf_upstream 1.10.iii meromorphicOrderAt "definition: order of a pole (negative order)"
dlmf_upstream 1.10.iii TauCeti.Contour.residue "definition: residue at a pole"
dlmf_upstream 1.10.iii TauCeti.Contour.residue_of_laurent_expansion
  "exact: the residue is the coefficient a₋₁ of a Laurent expansion"

/- §1.10(iv) Residue theorem. -/
dlmf_upstream 1.10.E8 TauCeti.Contour.classicalResidueTheorem_circle
  "special case: a circle, meromorphic f"
dlmf_upstream 1.10.E9 TauCeti.Contour.argumentPrinciple_nullHomologous
  "different hypotheses: homology form, winding-number weights"
dlmf_upstream 1.10.iv TauCeti.rouche_add "special case: C a circle"

/- §1.10(v) Maximum-modulus principle. -/
dlmf_upstream 1.10.v Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
  "exact: an interior maximum of |f| forces f constant"
dlmf_upstream 1.10.v Complex.exists_mem_frontier_isMaxOn_norm
  "exact: |f| attains its maximum on the boundary of a bounded domain"
dlmf_upstream 1.10.E11 Complex.dist_le_div_mul_dist_of_mapsTo_ball
  "stronger: Schwarz's lemma without f(0) = 0"
dlmf_upstream 1.10.E11 Complex.norm_deriv_le_div_of_mapsTo_ball "stronger: Cauchy estimate"

/- §1.10(viii)–(x). -/
dlmf_upstream 1.10.ix multipliable_one_add_of_summable
  "related: ∑ |aₙ| < ∞ gives (unconditional) convergence of ∏ (1 + aₙ)"
dlmf_upstream 1.10.ix Complex.multipliable_of_summable_log
  "related: convergent ∑ ln aₙ gives convergence of ∏ aₙ"
dlmf_upstream 1.10.E23 TendstoLocallyUniformlyOn.differentiableOn
  "stronger: locally uniform limits of holomorphic functions"
dlmf_upstream 1.10.E24 logDeriv_tprod_eq_tsum
  "different hypotheses: locally uniformly multipliable family, nonzero product"
