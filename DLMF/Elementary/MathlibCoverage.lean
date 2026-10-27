/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ComplexDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Meromorphic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.ZetaValues
public import TauCeti.Analysis.SpecialFunctions.Artanh
public import TauCeti.Analysis.SpecialFunctions.Hyperbolic
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Orthogonality

/-!
# DLMF Chapter 4 coverage already available in Mathlib and TauCeti

Checked pointers replace duplicate local statements. Native upstream DLMF tags are
also harvested by `scripts/DumpDLMF.lean` and listed in `DLMF4Acquisition.md`.
Comments distinguish exact results, partial coverage, and differences of branch,
normalization or domain. The principal logarithm uses argument in `(-π,π]`;
closed cut values and conditional boundary series are acquired separately.
Reciprocal functions and division are totalized at poles in Lean.

The real orthogonality and hyperbolic/artanh pointers credit the Tau Ceti
contributors. This module imports upstream libraries and the pointer facility;
the new elementary-function statements are in the sibling theory modules.
-/

dlmf_upstream 4.2.E3 Complex.log "exact off the cut: real part log norm and imaginary part arg"

dlmf_upstream 4.2.E3 Complex.mem_slitPlane_iff_arg "exact branch domain: argument strictly between -pi and pi"

dlmf_upstream 4.2.E5 Complex.log
  "exact: ln z = ln|z| + i ph z with -π < ph z ≤ π, z ≠ 0; Mathlib's log 0 = 0 is totalized"

dlmf_upstream 4.2.E12 Real.log_exp "exact at x=1: log(exp 1)=1; exp 1 is the unique positive such number"

dlmf_upstream 4.2.E13 integral_one_div_of_pos "exact after a=1,b=exp 1 and Real.log_exp"

dlmf_upstream 4.2.E19 Complex.exp_eq_exp_ℂ
  "partial: Complex.exp is the exponential series NormedSpace.exp"

dlmf_upstream 4.2.E19 NormedSpace.expSeries_div_hasSum_exp
  "partial: Σ zⁿ/n! sums to NormedSpace.exp z, which is Complex.exp by Complex.exp_eq_exp_ℂ"

dlmf_upstream 4.2.E20 Complex.exp_periodic "exact: exp is 2πi-periodic"

dlmf_upstream 4.2.E21 Complex.exp_neg "exact"

dlmf_upstream 4.2.E22 Complex.norm_exp "exact"

dlmf_upstream 4.2.E23 Complex.arg_exp "exact phase modulo 2 pi; the general phase adds arbitrary integer periods"

dlmf_upstream 4.2.E24 Complex.exp_eq_exp_re_mul_sin_add_cos "exact: x = Re z, y = Im z"

dlmf_upstream 4.2.E27 Complex.cpow_intCast "exact integer-power bridge"

dlmf_upstream 4.2.E27 Complex.cpow_natCast "partial: nonnegative integer powers agree with repeated multiplication"

dlmf_upstream 4.2.E27 Complex.cpow_neg "exact reciprocal identity"

dlmf_upstream 4.2.E28 Complex.cpow_def
  "exact: z ≠ 0, principal branch; Mathlib sets 0^0 = 1 and 0^a = 0 for a ≠ 0"

dlmf_upstream 4.2.E29 Complex.norm_cpow_of_ne_zero "exact: norm^Re a divided by exp(arg z Im a)"

dlmf_upstream 4.2.E31 Complex.norm_cpow_real "exact magnitude; unreduced phase also follows from power_phase"

dlmf_upstream 4.2.E34 NormedSpace.expSeries_div_hasSum_exp "exact at 1, together with Real.exp_eq_exp_\u211d"

dlmf_upstream 4.2.E34 Real.exp_eq_exp_ℝ "exact bridge for the real exponential series at 1"

dlmf_upstream 4.2.E37 Complex.zero_cpow "partial: zero base and nonzero exponent gives the exact origin square-root value"

dlmf_upstream 4.4.E1 Complex.log_one "exact"

dlmf_upstream 4.4.E3 Complex.log_I "partial: positive imaginary unit"

dlmf_upstream 4.4.E3 Complex.log_neg_I "partial: negative imaginary unit"

dlmf_upstream 4.4.E4 Complex.exp_zero "exact"

dlmf_upstream 4.4.E5 Complex.exp_neg_pi_mul_I "partial: negative sign"

dlmf_upstream 4.4.E5 Complex.exp_pi_mul_I "partial: positive sign"

dlmf_upstream 4.4.E6 Complex.exp_neg_pi_div_two_mul_I "partial: negative sign"

dlmf_upstream 4.4.E6 Complex.exp_pi_div_two_mul_I "partial: positive sign"

dlmf_upstream 4.4.E7 Complex.exp_eq_one_iff "exact: integer multiples of 2 pi i"

dlmf_upstream 4.4.E17 Complex.tendsto_one_add_div_pow_exp "exact: complex parameter z, natural n tends to infinity"

dlmf_upstream 4.4.E18 Real.tendsto_one_add_div_pow_exp "exact at parameter 1"

dlmf_upstream 4.4.E19 Real.tendsto_harmonic_sub_log "exact limit defining Euler constant; decimal excluded: numerical"

dlmf_upstream 4.5.E1 Real.log_lt_sub_one_of_pos
  "partial: right inequality ln(1+x) < x, in the form ln y < y - 1 for y = 1 + x > 0, y ≠ 1"

dlmf_upstream 4.5.E4 Real.log_le_sub_one_of_pos "exact: x > 0"

dlmf_upstream 4.5.E8 Real.add_one_lt_exp "exact: x ≠ 0 (equality at x = 0)"

dlmf_upstream 4.6.E1 Complex.hasSum_taylorSeries_log "partial: open unit disk only; closed boundary acquired locally"

dlmf_upstream 4.6.E2 Complex.hasSum_taylorSeries_neg_log "partial: transformed open disk only; half-plane boundary acquired locally"

dlmf_upstream 4.7.E1 Complex.hasDerivAt_log "exact principal branch on the slit plane"

dlmf_upstream 4.7.E3 iteratedDeriv_succ_log "exact for every positive derivative order on the slit plane"

dlmf_upstream 4.7.E7 Complex.hasDerivAt_exp "exact"

dlmf_upstream 4.7.E9 Complex.hasStrictDerivAt_const_cpow "exact principal-power derivative for nonzero base"

dlmf_upstream 4.7.E10 Complex.hasStrictDerivAt_cpow_const "exact on the principal slit domain"

dlmf_upstream 4.8.E2 Complex.log_mul "special case: -pi < arg x+arg y <= pi; closed lower edge needs closedLogValues"

dlmf_upstream 4.8.E7 Complex.log_inv "special case: arg z != pi; closed cut identity exchanges sides"

dlmf_upstream 4.8.E9 Complex.log_exp
  "special case: -π < Im z ≤ π; the printed bound Im z = -π fails for the principal branch"

dlmf_upstream 4.8.E10 Complex.exp_log "partial: exp(ln z) = z for z ≠ 0"

dlmf_upstream 4.8.E13 Real.log_rpow "exact: a > 0, real x"

dlmf_upstream 4.8.E14 Complex.cpow_add "exact: a ≠ 0, principal powers"

dlmf_upstream 4.8.E16 Complex.exp_add "exact"

dlmf_upstream 4.10.E11 integral_gaussian_complex "exact: complex c with positive real part; principal square root"

dlmf_upstream 4.14.E3 Complex.cos_sub_sin_I "partial: lower sign; order of the product i z is immaterial"

dlmf_upstream 4.14.E3 Complex.exp_mul_I "partial: upper sign, cos z + i sin z = e^{iz}"

dlmf_upstream 4.14.E8 Complex.sin_add_int_mul_two_pi "exact: k ∈ ℤ"

dlmf_upstream 4.14.E9 Complex.cos_add_int_mul_two_pi "exact: k ∈ ℤ"

dlmf_upstream 4.14.E10 Complex.tan_add_int_mul_pi
  "exact: k ∈ ℤ; Mathlib's tan is 0 at the poles, where the identity also holds"

dlmf_upstream 4.14 Complex.cos_eq_zero_iff "prose: all complex zeros of cosine"

dlmf_upstream 4.14 Complex.differentiable_cos "prose: cosine is entire"

dlmf_upstream 4.14 Complex.differentiable_sin "prose: sine is entire"

dlmf_upstream 4.14 Complex.meromorphic_tan "prose: tangent is meromorphic, with totalized values at its poles"

dlmf_upstream 4.14 Complex.sin_eq_zero_iff "prose: all complex zeros of sine"

dlmf_upstream 4.14 Complex.tan_eq_zero_iff' "prose: tangent zeros away from its cosine poles"

dlmf_upstream 4.14 Complex.tendsto_norm_tan_of_cos_eq_zero "prose: tangent poles are cosine zeros"

dlmf_upstream 4.15.E1 Complex.sin_add_pi_div_two "stronger: every complex argument"

dlmf_upstream 4.16.T1 Real.cos_pos_of_mem_Ioo "partial: cosine sign on quadrants I and IV"

dlmf_upstream 4.16.T1 Real.sin_pos_of_pos_of_lt_pi "partial: sine sign on quadrants I and II"

dlmf_upstream 4.16.T2 Complex.cos_add_pi "partial: half-period cosine translation"

dlmf_upstream 4.16.T2 Complex.cos_add_pi_div_two "partial: quarter-period cosine translation"

dlmf_upstream 4.16.T2 Complex.sin_add_pi "partial: half-period sine translation"

dlmf_upstream 4.16.T2 Complex.sin_add_pi_div_two "partial: quarter-period sine translation"

dlmf_upstream 4.17.E1 Complex.tendsto_sin_div_nhdsNE_zero "exact"

dlmf_upstream 4.17.T1 Real.cos_pi "partial: exact table entry or exact limit at infinity; reciprocal rows acquired locally"

dlmf_upstream 4.17.T1 Real.cos_pi_div_four "partial: exact table entry or exact limit at infinity; reciprocal rows acquired locally"

dlmf_upstream 4.17.T1 Real.cos_pi_div_six "partial: exact table entry or exact limit at infinity; reciprocal rows acquired locally"

dlmf_upstream 4.17.T1 Real.cos_pi_div_three "partial: exact table entry or exact limit at infinity; reciprocal rows acquired locally"

dlmf_upstream 4.17.T1 Real.cos_pi_div_two "partial: exact table entry or exact limit at infinity; reciprocal rows acquired locally"

dlmf_upstream 4.17.T1 Real.cos_zero "partial: exact table entry or exact limit at infinity; reciprocal rows acquired locally"

dlmf_upstream 4.17.T1 Real.sin_pi "partial: exact table entry or exact limit at infinity; reciprocal rows acquired locally"

dlmf_upstream 4.17.T1 Real.sin_pi_div_four "partial: exact table entry or exact limit at infinity; reciprocal rows acquired locally"

dlmf_upstream 4.17.T1 Real.sin_pi_div_six "partial: exact table entry or exact limit at infinity; reciprocal rows acquired locally"

dlmf_upstream 4.17.T1 Real.sin_pi_div_three "partial: exact table entry or exact limit at infinity; reciprocal rows acquired locally"

dlmf_upstream 4.17.T1 Real.sin_pi_div_two "partial: exact table entry or exact limit at infinity; reciprocal rows acquired locally"

dlmf_upstream 4.17.T1 Real.sin_zero "partial: exact table entry or exact limit at infinity; reciprocal rows acquired locally"

dlmf_upstream 4.17.T1 Real.tan_pi_div_four "partial: exact table entry or exact limit at infinity; reciprocal rows acquired locally"

dlmf_upstream 4.17.T1 Real.tan_pi_div_six "partial: exact table entry or exact limit at infinity; reciprocal rows acquired locally"

dlmf_upstream 4.17.T1 Real.tan_pi_div_three "partial: exact table entry or exact limit at infinity; reciprocal rows acquired locally"

dlmf_upstream 4.17.E2 Complex.tendsto_tan_div_nhdsNE_zero "exact"

dlmf_upstream 4.17.E3 Complex.tendsto_one_sub_cos_div_nhdsNE_zero "exact"

dlmf_upstream 4.18.E1 Real.mul_le_sin "partial: lower Jordan bound"

dlmf_upstream 4.18.E1 Real.sin_le "partial: upper Jordan bound"

dlmf_upstream 4.18.E2 Real.le_tan "exact"

dlmf_upstream 4.19.E1 Complex.hasSum_sin "exact: full convergent sine series"

dlmf_upstream 4.19.E2 Complex.hasSum_cos "exact: full convergent cosine series"

dlmf_upstream 4.20.E1 Complex.hasDerivAt_sin "exact"

dlmf_upstream 4.20.E2 Complex.hasDerivAt_cos "exact"

dlmf_upstream 4.20.E3 Complex.hasDerivAt_tan "exact: 1/cos\u00b2 at nonpoles"

dlmf_upstream 4.20.E7 Complex.iteratedDeriv_even_sin "partial: even derivative orders"

dlmf_upstream 4.20.E7 Complex.iteratedDeriv_odd_sin "partial: odd derivative orders"

dlmf_upstream 4.20.E8 Complex.iteratedDeriv_even_cos "partial: even derivative orders"

dlmf_upstream 4.20.E8 Complex.iteratedDeriv_odd_cos "partial: odd derivative orders"

dlmf_upstream 4.21.E2 Complex.sin_add "partial: upper sign"

dlmf_upstream 4.21.E2 Complex.sin_sub "partial: lower sign"

dlmf_upstream 4.21.E3 Complex.cos_add "partial: upper sign"

dlmf_upstream 4.21.E3 Complex.cos_sub "partial: lower sign"

dlmf_upstream 4.21.E4 Complex.tan_add "partial: upper sign, with all necessary denominator hypotheses"

dlmf_upstream 4.21.E4 Complex.tan_sub "partial: lower sign, with all necessary denominator hypotheses"

dlmf_upstream 4.21.E6 Complex.sin_add_sin "exact"

dlmf_upstream 4.21.E7 Complex.sin_sub_sin "exact: commuted two factors"

dlmf_upstream 4.21.E8 Complex.cos_add_cos "exact"

dlmf_upstream 4.21.E9 Complex.cos_sub_cos "exact"

dlmf_upstream 4.21.E12 Complex.sin_sq_add_cos_sq "exact"

dlmf_upstream 4.21.E15 Real.two_mul_sin_mul_sin "special case: real arguments; complex identity acquired locally"

dlmf_upstream 4.21.E16 Real.two_mul_cos_mul_cos "special case: real arguments; complex identity acquired locally"

dlmf_upstream 4.21.E17 Real.two_mul_sin_mul_cos "special case: real arguments; complex identity acquired locally"

dlmf_upstream 4.21.E21 Real.sin_half_eq_sqrt "special case: nonnegative real half-angle branch"

dlmf_upstream 4.21.E22 Real.cos_half "special case: real arguments in [-pi,pi]"

dlmf_upstream 4.21.E24 Complex.sin_neg "exact"

dlmf_upstream 4.21.E25 Complex.cos_neg "exact"

dlmf_upstream 4.21.E26 Complex.tan_neg "exact"

dlmf_upstream 4.21.E27 Complex.sin_two_mul "partial: first equality sin 2z = 2 sin z cos z"

dlmf_upstream 4.21.E28 Complex.cos_two_mul "partial: first equality cos 2z = 2cos²z - 1"

dlmf_upstream 4.21.E28 Complex.cos_two_mul' "partial: third equality cos 2z = cos²z - sin²z"

dlmf_upstream 4.21.E28 Complex.cos_two_mul_eq_one_sub "partial: second equality"

dlmf_upstream 4.21.E29 Complex.tan_two_mul "partial: first tangent double-angle form"

dlmf_upstream 4.21.E30 Complex.sin_three_mul "exact"

dlmf_upstream 4.21.E31 Complex.cos_three_mul "exact"

dlmf_upstream 4.21.E34 Complex.cos_add_sin_mul_I_pow "special case: n ∈ ℕ (DLMF: n ∈ ℤ)"

dlmf_upstream 4.21.E37 Complex.sin_eq "exact: x = Re z, y = Im z"

dlmf_upstream 4.21.E38 Complex.cos_eq "exact: x = Re z, y = Im z"

dlmf_upstream 4.21.E39 Complex.tan_eq "exact: real and imaginary parts, away from cosine poles"

dlmf_upstream 4.22.E1 Complex.tendsto_euler_sin_prod "exact: argument rescaled by pi"

dlmf_upstream 4.22.E3 cot_series_rep "exact: argument rescaled by pi, away from sine zeros"

dlmf_upstream 4.23.T1 Real.arccos_neg_one "partial: exact table entry or exact limit at infinity; reciprocal rows acquired locally"

dlmf_upstream 4.23.T1 Real.arccos_one "partial: exact table entry or exact limit at infinity; reciprocal rows acquired locally"

dlmf_upstream 4.23.T1 Real.arccos_zero "partial: exact table entry or exact limit at infinity; reciprocal rows acquired locally"

dlmf_upstream 4.23.T1 Real.arcsin_neg_one "partial: exact table entry or exact limit at infinity; reciprocal rows acquired locally"

dlmf_upstream 4.23.T1 Real.arcsin_one "partial: exact table entry or exact limit at infinity; reciprocal rows acquired locally"

dlmf_upstream 4.23.T1 Real.arcsin_zero "partial: exact table entry or exact limit at infinity; reciprocal rows acquired locally"

dlmf_upstream 4.23.T1 Real.arctan_one "partial: exact table entry or exact limit at infinity; reciprocal rows acquired locally"

dlmf_upstream 4.23.T1 Real.arctan_zero "partial: exact table entry or exact limit at infinity; reciprocal rows acquired locally"

dlmf_upstream 4.23.T1 Real.tendsto_arctan_atBot "partial: exact table entry or exact limit at infinity; reciprocal rows acquired locally"

dlmf_upstream 4.23.T1 Real.tendsto_arctan_atTop "partial: exact table entry or exact limit at infinity; reciprocal rows acquired locally"

dlmf_upstream 4.23.E10 Real.arcsin_neg "special case: real principal arcsine"

dlmf_upstream 4.23.E11 Real.arccos_neg "special case: real principal arccosine"

dlmf_upstream 4.23.E12 Real.arctan_neg "special case: real principal arctangent"

dlmf_upstream 4.23.E16 Real.arccos "special case: real principal arccosine is pi/2-arcsine"

dlmf_upstream 4.23.E28 Real.sin_arcsin "special case: real arguments in [-1,1]"

dlmf_upstream 4.23.E29 Real.cos_arccos "special case: real arguments in [-1,1]"

dlmf_upstream 4.23.E30 Complex.tan_arctan "exact: z differs from \u00b1i"

dlmf_upstream 4.24.E3 Complex.hasSum_arctan "partial: open unit disc; boundary acquired locally"

dlmf_upstream 4.24.E7 Real.hasDerivAt_arcsin "special case: real derivative, excluding endpoints"

dlmf_upstream 4.24.E8 Real.hasDerivAt_arccos "special case: real derivative, excluding endpoints"

dlmf_upstream 4.24.E9 Real.hasDerivAt_arctan "special case: real derivative"

dlmf_upstream 4.26.E1 Real.hasDerivAt_cos "exact: negative cosine is an antiderivative of sine"

dlmf_upstream 4.26.E2 Real.hasDerivAt_sin "exact: sine is an antiderivative of cosine"

dlmf_upstream 4.26.E9 TauCeti.integral_sin_nat_mul_mul_sin_nat_mul "special case: natural frequencies; integer statement needs m != -n too"

dlmf_upstream 4.26.E11 integral_cos_sq "partial: cosine square, general finite interval"

dlmf_upstream 4.26.E11 integral_sin_sq "partial: sine square, general finite interval"

dlmf_upstream 4.28.E1 Complex.sinh "exact: complex exponential definition"

dlmf_upstream 4.28.E2 Complex.cosh "exact: complex exponential definition"

dlmf_upstream 4.28.E3 Complex.cosh_add_sinh "exact: upper sign"

dlmf_upstream 4.28.E3 Complex.cosh_sub_sinh "exact: lower sign"

dlmf_upstream 4.28.E4 Complex.tanh_eq_sinh_div_cosh "exact"

dlmf_upstream 4.28.E8 Complex.sin_mul_I "exact: commute i and z"

dlmf_upstream 4.28.E9 Complex.cos_mul_I "exact: commute i and z"

dlmf_upstream 4.28.E10 Complex.tan_mul_I "exact: commute i and z"

dlmf_upstream 4.31.E1 Complex.isEquivalent_sinh "equivalent: sinh z is asymptotic to z at zero"

dlmf_upstream 4.33.E1 Complex.hasSum_sinh "exact: globally convergent complex series"

dlmf_upstream 4.33.E2 Complex.hasSum_cosh "exact: globally convergent complex series"

dlmf_upstream 4.34.E1 Complex.hasDerivAt_sinh "exact"

dlmf_upstream 4.34.E2 Complex.hasDerivAt_cosh "exact"

dlmf_upstream 4.35.E1 Complex.sinh_add "partial: upper sign"

dlmf_upstream 4.35.E1 Complex.sinh_sub "partial: lower sign"

dlmf_upstream 4.35.E2 Complex.cosh_add "partial: upper sign"

dlmf_upstream 4.35.E2 Complex.cosh_sub "partial: lower sign"

dlmf_upstream 4.35.E3 Real.tanh_add "special case: real arguments; proved in pinned TauCeti.Analysis.SpecialFunctions.Hyperbolic"

dlmf_upstream 4.35.E11 Complex.cosh_sq_sub_sinh_sq "exact"

dlmf_upstream 4.35.E23 Complex.sinh_neg "exact"

dlmf_upstream 4.35.E24 Complex.cosh_neg "exact"

dlmf_upstream 4.35.E25 Complex.tanh_neg "exact"

dlmf_upstream 4.35.E26 Complex.sinh_two_mul "partial: first equality"

dlmf_upstream 4.35.E27 Complex.cosh_two_mul "partial: final equality"

dlmf_upstream 4.35.E29 Complex.sinh_three_mul "exact"

dlmf_upstream 4.35.E30 Complex.cosh_three_mul "exact"

dlmf_upstream 4.37.E10 Real.arsinh_neg "special case: real arguments"

dlmf_upstream 4.37.E12 Real.artanh_neg_eq_neg_artanh "special case: real arguments; pinned TauCeti.Analysis.SpecialFunctions.Artanh"

dlmf_upstream 4.37.E16 Real.arsinh "special case: real arguments; complex principal branches acquired locally"

dlmf_upstream 4.37.E19 Real.arcosh "special case: real arguments at least one"

dlmf_upstream 4.37.E24 Real.artanh_eq_half_log "special case: real arguments in [-1,1], endpoint totalizations distinguished"

dlmf_upstream 4.38.E9 Real.hasDerivAt_arsinh "special case: real arguments"

dlmf_upstream 4.38.E10 Real.hasDerivAt_arcosh "special case: real arguments greater than one"

dlmf_upstream 4.38.E11 Real.hasDerivAt_artanh "special case: real arguments in (-1,1); pinned TauCeti.Analysis.SpecialFunctions.Artanh"

dlmf_upstream 4.38.E17 Real.artanh_add "special case: real principal inverses in (-1,1); pinned TauCeti.Analysis.SpecialFunctions.Artanh"

dlmf_upstream 4.38.E17 Real.artanh_sub "special case: real principal inverses in (-1,1); pinned TauCeti.Analysis.SpecialFunctions.Artanh"

dlmf_upstream 4.40.E1 Real.hasDerivAt_cosh "exact: antiderivative interpretation"

dlmf_upstream 4.40.E2 Real.hasDerivAt_sinh "exact: antiderivative interpretation"

dlmf_upstream 4.45.E2 Real.log_rpow
  "exact after y=x^(2^(-m))-1, x>0: log of a positive real power, followed by multiplying by 2^m"

dlmf_upstream 4.45.E3 Real.log_mul
  "partial: log(10^m*xi)=log(10^m)+log xi for xi>0"

dlmf_upstream 4.45.E3 Real.log_zpow
  "partial: log(10^m)=m*log 10 for every integer m"

dlmf_upstream 4.45.E5 Complex.exp_add
  "partial: exponential of x=m*log 10+y splits as a product; specialize to real arguments"

dlmf_upstream 4.45.E5 Complex.exp_int_mul
  "partial: exp(m*log 10)=exp(log 10)^m=10^m, integer m"

dlmf_upstream 4.45.E7 Real.cos_sub_int_mul_pi
  "partial: cosine equality, rearranged by (-1)^m, with theta=x-m*pi"

dlmf_upstream 4.45.E7 Real.sin_sub_int_mul_pi
  "partial: sine equality, rearranged by (-1)^m, with theta=x-m*pi"

dlmf_upstream 4.45.E11 Real.arctan_inv_of_pos
  "partial: complementary-angle identity converting the reciprocal-argument series to arctan x, x>1"

dlmf_upstream 4.45.E11 Real.hasSum_arctan
  "partial: convergent alternating series at 1/x for x>1; its sum is pi/2-arctan x by arctan_inv_of_pos"

dlmf_upstream 4.45.E15 Complex.log
  "exact: log z=log|z|+i arg z; principal value -pi<arg z<=pi, log 0 totalized"

dlmf_upstream 4.45.E16 Complex.exp_eq_exp_re_mul_sin_add_cos
  "exact: exp z=exp(Re z)*(cos(Im z)+i*sin(Im z))"

dlmf_upstream 4.45.i Real.arcsin_eq_arctan
  "partial: inverse sine via arctangent, real -1<x<1, from the computation prose"
